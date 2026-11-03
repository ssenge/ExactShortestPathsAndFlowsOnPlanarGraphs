"""Drivers. Usage: python3 -I nd_drive.py LANE OUT.json MAXSEC [args]
Lanes:
  exh M SHARD NSHARDS [maxrun]   all loopless connected maps with M edges, all ordered (s,t), all faces and corners,
                                 several capacity vectors, every run of the recursion up to maxrun per corner choice
  rand8 SEED                     random maps with 7 or 8 edges (sample of the exhaustive list), random capacities
  planar SEED [fam]              random planar graphs up to about 60 vertices, worst-case policies for ties
  hard                           saved hard instances, printed instances
  mut SEED                       saved hard instances with mutated capacities
  geo SEED                       straight-line drawings: the true sides of gamma from coordinates
  C SEED                         reading-direction variants of the whole recursion
  ctl SEED                       negative controls with a broken rule that drives the recursion
"""
import os
import sys
import json
import time
import random
import itertools
import collections

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.dont_write_bytecode = True
sys.setrecursionlimit(10000)
import nd_core as X
import nd_fam as F

REPO = os.path.dirname(HERE)
MAPS = os.path.join(REPO, 'testSO', 'logs', 'maps8nl.json')
RLOG = os.path.join(REPO, 'testR', 'logs')
SOLOG = os.path.join(REPO, 'testSO', 'logs')


class Saver:
    def __init__(self, out, meta):
        self.out, self.meta = out, meta
        self.t0 = self.tl = time.time()

    def save(self, ctx, final=False, extra=None):
        now = time.time()
        if not final and now - self.tl < 45:
            return
        self.tl = now
        res = dict(meta=self.meta, secs=round(now - self.t0, 1), final=final, counts=dict(ctx.C), fails=ctx.fails,
                   examples=ctx.examples, levels_by_m={str(k): v for k, v in sorted(ctx.levels_by_m.items())},
                   max_range_mult=ctx.max_mult, max_piece_mult=ctx.max_piece_mult, max_face_annuli=ctx.max_face_annuli)
        if extra:
            res.update(extra)
        tmp = self.out + '.tmp'
        with open(tmp, 'w') as f:
            json.dump(res, f, default=str)
        os.replace(tmp, self.out)


def corners(I, v):
    res = collections.defaultdict(list)
    for k in range(len(I.rot[v])):
        res[I.corner_face(v, k)].append(k)
    return res


def all_choices(I):
    cs_ = corners(I, I.s)
    ct_ = corners(I, I.t)
    for f, css in sorted(cs_.items()):
        for g, cts in sorted(ct_.items()):
            for cs in css:
                for ct in cts:
                    yield f, g, cs, ct


def random_choice(I, rng):
    cs_ = corners(I, I.s)
    ct_ = corners(I, I.t)
    f = rng.choice(sorted(cs_))
    g = rng.choice(sorted(ct_))
    return f, g, rng.choice(cs_[f]), rng.choice(ct_[g])


def enum_run(I, ctx, f, g, cs, ct, maxrun, opts):
    """every run for one choice of faces and corners, up to maxrun. returns (#runs, complete)."""
    ch = X.EnumCh()
    n = 0
    while True:
        ch.start()
        R = X.Run(I, ctx, ch, f, g, cs, ct, opts)
        try:
            R.go()
        except X.Abort as ex:
            ctx.C['abort'] += 1
            ctx.C['abort:' + str(ex)[:30]] += 1
        n += 1
        if not ch.advance():
            return n, True
        if n >= maxrun:
            return n, False


def capvecs(m, seed):
    rng = random.Random(seed)
    out = []
    if os.environ.get('RICH') == '1' and m == 6:
        out += [('all01', list(v)) for v in itertools.product(range(2), repeat=m)]
        out += [('r012', [rng.randint(0, 2) for _ in range(m)]) for _ in range(8)]
    elif m <= 4:
        out += [('all012', list(v)) for v in itertools.product(range(3), repeat=m)]
    elif m == 5:
        out += [('all01', list(v)) for v in itertools.product(range(2), repeat=m)]
        out += [('r012', [rng.randint(0, 2) for _ in range(m)]) for _ in range(8)]
    else:
        out += [('one', [1] * m), ('zero', [0] * m)]
        out += [('r012', [rng.randint(0, 2) for _ in range(m)]) for _ in range(4)]
        out += [('r12', [rng.randint(1, 2) for _ in range(m)]) for _ in range(2)]
    out += [('gen', [rng.randint(1, 10 ** 6) for _ in range(m)])]
    return out


def lane_exh(out, maxsec, M, shard, nsh, maxrun=30):
    maps = json.load(open(MAPS))[str(M)]
    ctx = X.Ctx()
    sv = Saver(out, dict(lane='exh', M=M, shard=shard, nsh=nsh, maxrun=maxrun, nmaps=len(maps)))
    t0 = time.time()
    done = stop = 0
    C = ctx.C
    opts = dict(cap_b=8, cap_paths=64, c_stats=True)
    for mi, (n, ends, rot) in enumerate(maps):
        if mi % nsh != shard:
            continue
        if time.time() - t0 > maxsec:
            stop = 1
            break
        for cname, cap in capvecs(M, 1000 * mi + M):
            for s, t in itertools.permutations(range(n), 2):
                I = X.Inst(n, [tuple(e) for e in ends], rot, cap, s, t, tag='map%d:%d:%s' % (M, mi, cname))
                C['instances'] += 1
                for f, g, cs, ct in all_choices(I):
                    C['corner_choices'] += 1
                    nr, compl = enum_run(I, ctx, f, g, cs, ct, maxrun, opts)
                    C['enum_incomplete'] += not compl
                sv.save(ctx)
        done += 1
        C['maps_done'] += 1
    sv.save(ctx, final=True, extra=dict(stopped_early=bool(stop)))
    print(json.dumps(dict(lane='exh', M=M, shard=shard, runs=C['runs'], maps=done, inst=C['instances'], incomplete=C['enum_incomplete'], secs=round(time.time() - t0))))


POLS = ['rand', 'rand', 'first', 'last', 'maxP', 'alt', 'touch', 'untouch', 'far', 'near', 'maxold', 'minold']


def lane_rand8(out, maxsec, seed):
    allm = json.load(open(MAPS))
    maps = allm['7'] + allm['8']
    ctx = X.Ctx()
    C = ctx.C
    sv = Saver(out, dict(lane='rand8', seed=seed, nmaps=len(maps)))
    rng = random.Random(seed)
    t0 = time.time()
    while time.time() - t0 < maxsec:
        n, ends, rot = rng.choice(maps)
        m = len(ends)
        sc = rng.choice(['one', 'r012', 'r12', 'z01', 'gen', 'r123'])
        cap = {'one': [1] * m, 'r012': [rng.randint(0, 2) for _ in range(m)], 'r12': [rng.randint(1, 2) for _ in range(m)],
               'z01': [rng.randint(0, 1) for _ in range(m)], 'gen': [rng.randint(1, 10 ** 6) for _ in range(m)],
               'r123': [rng.randint(1, 3) for _ in range(m)]}[sc]
        s, t = rng.sample(range(n), 2)
        I = X.Inst(n, [tuple(e) for e in ends], rot, cap, s, t, tag='rand8:' + sc)
        C['instances'] += 1
        # all corner choices, all runs up to a cap
        for f, g, cs, ct in all_choices(I):
            nr, compl = enum_run(I, ctx, f, g, cs, ct, 20, dict(cap_b=8, cap_paths=64))
            C['enum_incomplete'] += not compl
        sv.save(ctx)
    sv.save(ctx, final=True)
    print(json.dumps(dict(lane='rand8', seed=seed, runs=C['runs'], inst=C['instances'], secs=round(time.time() - t0))))


def lane_planar(out, maxsec, seed, fam=None, maxn=60):
    ctx = X.Ctx()
    C = ctx.C
    sv = Saver(out, dict(lane='planar', seed=seed, fam=fam, maxn=maxn))
    t0 = time.time()
    k = 0
    while time.time() - t0 < maxsec:
        I, rng = F.make(seed * 1000003 + k, fam, maxn)
        k += 1
        C['instances'] += 1
        C['fam.' + I.tag.split(':')[0]] += 1
        C['cap.' + I.tag.split(':')[1]] += 1
        for r in range(6):
            f, g, cs, ct = random_choice(I, rng)
            pol = rng.choice(POLS)
            ch = X.PolicyCh(rng, pol)
            opts = dict(cap_b=3, cap_paths=24, sample=True, ghat=(r == 0))
            R = X.Run(I, ctx, ch, f, g, cs, ct, opts)
            try:
                R.go()
            except X.Abort as ex:
                C['abort'] += 1
                C['abort:' + str(ex)[:30]] += 1
            sv.save(ctx)
    sv.save(ctx, final=True)
    print(json.dumps(dict(lane='planar', seed=seed, runs=C['runs'], inst=C['instances'], secs=round(time.time() - t0))))


def load_hard():
    res = []
    seen = set()

    def add(name, n, ends, rot, cap, s, t):
        key = json.dumps([n, ends, rot, cap, s, t], default=str)
        if key in seen:
            return
        seen.add(key)
        res.append((name, n, [tuple(e) for e in ends], rot, list(cap), s, t))

    def walk(obj, name):
        if isinstance(obj, dict):
            if all(k in obj for k in ('n', 'ends', 'rot', 'cap', 's', 't')):
                try:
                    add(name, obj['n'], obj['ends'], obj['rot'], obj['cap'], obj['s'], obj['t'])
                except Exception:
                    pass
            for k, v in obj.items():
                walk(v, name)
        elif isinstance(obj, list):
            for v in obj:
                walk(v, name)
    for d, fs in ((RLOG, sorted(os.listdir(RLOG))), (SOLOG, sorted(os.listdir(SOLOG)))):
        for fn in fs:
            if fn.endswith('.json') and fn != 'maps8nl.json':
                try:
                    walk(json.load(open(os.path.join(d, fn))), fn)
                except Exception:
                    pass
            if fn.endswith('.jsonl'):
                try:
                    for line in open(os.path.join(d, fn)):
                        walk(json.loads(line), fn)
                except Exception:
                    pass
    # the printed network of Example ex:recursion and (D1)
    ends = [(0, 1), (0, 2), (2, 7), (1, 3), (7, 8), (8, 4), (4, 5), (8, 9), (7, 10), (4, 9), (5, 8), (6, 5), (7, 0), (9, 5), (5, 10), (1, 2), (8, 2), (1, 7), (8, 10), (0, 3), (2, 3), (9, 6)]
    cap = [1, 1, 1, 1, 1, 1, 3, 1, 13, 1, 50, 1, 13, 2, 50, 20, 1, 30, 47, 20, 30, 2]
    rot = [[0, 38, 2, 25], [1, 34, 30, 6], [3, 40, 31, 4, 33], [7, 41, 39], [11, 12, 18], [13, 28, 20, 27, 23], [22, 43], [24, 8, 16, 5, 35], [9, 32, 36, 10, 14, 21], [15, 19, 42, 26], [17, 29, 37]]
    add('example_recursion', 11, ends, rot, cap, 5, 3)
    ends2 = [(0, 3), (0, 1), (1, 2), (2, 3), (1, 3)]
    d = lambda e, v: 2 * e + (0 if ends2[e][0] == v else 1)
    e03, e01, e12, e23, e13 = 0, 1, 2, 3, 4
    rot2 = [[d(e03, 0), d(e01, 0)], [d(e12, 1), d(e13, 1), d(e01, 1)], [d(e12, 2), d(e23, 2)], [d(e23, 3), d(e03, 3), d(e13, 3)]]
    add('D1', 4, ends2, rot2, [1, 1, 1, 1, 5], 1, 2)
    return res


def lane_hard(out, maxsec, seed=1):
    H = load_hard()
    ctx = X.Ctx()
    C = ctx.C
    sv = Saver(out, dict(lane='hard', ninstances=len(H)))
    rng = random.Random(seed)
    t0 = time.time()
    C['hard_instances'] = len(H)
    rounds = 0
    while time.time() - t0 < maxsec:
        rounds += 1
        for name, n, ends, rot, cap, s, t in H:
            if time.time() - t0 > maxsec:
                break
            m = len(ends)
            if any(a == b for a, b in ends):
                C['skip_loops'] += 1
                continue
            med = sorted(cap)[len(cap) // 2]
            for cname, cc in (('given', cap), ('one', [1] * m), ('one_two', [1 if c <= med else 2 for c in cap])):
                try:
                    I = X.Inst(n, ends, rot, cc, s, t, tag='hard:' + name + ':' + cname)
                except AssertionError:
                    C['skip_bad_format'] += 1
                    continue
                if I.euler() != 2 or not I.connected():
                    C['skip_nonplanar'] += 1
                    continue
                C['instances'] += 1
                if rounds == 1:
                    lst = list(all_choices(I))
                    rng.shuffle(lst)
                    for f, g, cs, ct in lst[:12]:
                        enum_run(I, ctx, f, g, cs, ct, 40, dict(cap_b=6, cap_paths=32))
                else:
                    for r in range(4):
                        f, g, cs, ct = random_choice(I, rng)
                        ch = X.PolicyCh(rng, rng.choice(POLS))
                        R = X.Run(I, ctx, ch, f, g, cs, ct, dict(cap_b=3, cap_paths=24, sample=True, ghat=False))
                        try:
                            R.go()
                        except X.Abort as ex:
                            C['abort'] += 1
                sv.save(ctx)
    sv.save(ctx, final=True, extra=dict(rounds=rounds))
    print(json.dumps(dict(lane='hard', runs=C['runs'], inst=C['instances'], rounds=rounds, secs=round(time.time() - t0))))


def lane_mut(out, maxsec, seed):
    """Hard instances with mutated capacities (many ties), worst-case policies."""
    H = [h for h in load_hard() if not any(a == b for a, b in h[2])]
    ctx = X.Ctx()
    C = ctx.C
    sv = Saver(out, dict(lane='mut', seed=seed, ninstances=len(H)))
    rng = random.Random(seed)
    t0 = time.time()
    while time.time() - t0 < maxsec:
        name, n, ends, rot, cap, s, t = rng.choice(H)
        m = len(ends)
        sc = rng.choice(['r12', 'r123', 'z01', 'perturb', 'perturb'])
        if sc == 'r12':
            cc = [rng.randint(1, 2) for _ in range(m)]
        elif sc == 'r123':
            cc = [rng.randint(1, 3) for _ in range(m)]
        elif sc == 'z01':
            cc = [rng.randint(0, 1) for _ in range(m)]
        else:
            cc = [c if rng.random() < .8 else rng.choice(cap) for c in cap]
        try:
            I = X.Inst(n, ends, rot, cc, s, t, tag='mut:' + name + ':' + sc)
        except AssertionError:
            C['skip_bad_format'] += 1
            continue
        if I.euler() != 2 or not I.connected():
            C['skip_nonplanar'] += 1
            continue
        if rng.random() < .3:
            s2, t2 = rng.sample(range(n), 2)
            I = X.Inst(n, ends, rot, cc, s2, t2, tag=I.tag + ':st')
        C['instances'] += 1
        for r in range(4):
            f, g, cs, ct = random_choice(I, rng)
            ch = X.PolicyCh(rng, rng.choice(POLS))
            R = X.Run(I, ctx, ch, f, g, cs, ct, dict(cap_b=3, cap_paths=24, sample=True, ghat=False))
            try:
                R.go()
            except X.Abort:
                C['abort'] += 1
            sv.save(ctx)
    sv.save(ctx, final=True)
    print(json.dumps(dict(lane='mut', runs=C['runs'], inst=C['instances'], secs=round(time.time() - t0))))


def lane_geo(out, maxsec, seed):
    ctx = X.Ctx()
    C = ctx.C
    sv = Saver(out, dict(lane='geo', seed=seed))
    rng = random.Random(seed)
    t0 = time.time()
    while time.time() - t0 < maxsec:
        mp, S, T, kind, pts = F.fam_grid(rng, 36, straight=True)
        if S == T:
            continue
        m = len(mp.ends)
        sc, cap = F.caps_for(mp, rng, kind, S)
        if rng.random() < .8:
            # make the outer face expensive to enter, so that P and the incised parts stay in convex faces
            Fc = mp.faces()

            def area(f):
                vs = [mp.tail(d) for d in f]
                return sum(pts[vs[q]][0] * pts[vs[(q + 1) % len(vs)]][1] - pts[vs[(q + 1) % len(vs)]][0] * pts[vs[q]][1] for q in range(len(vs)))
            outer = max(Fc, key=area)
            bd = {d >> 1 for d in outer}
            cap = [10 ** 4 if e in bd else cap[e] for e in range(m)]
            boundary_v = {mp.tail(d) for d in outer}
            inner = [v for v in range(mp.n) if v not in boundary_v]
            if len(inner) >= 2:
                S, T = rng.sample(inner, 2)
            sc += '+outer'
        I = X.Inst(mp.n, mp.ends, mp.rot, cap, S, T, coords=pts, tag='geo:' + sc)
        C['instances'] += 1
        lst = list(all_choices(I))
        rng.shuffle(lst)
        for f, g, cs, ct in lst[:10]:
            ch = X.PolicyCh(rng, rng.choice(POLS))
            R = X.Run(I, ctx, ch, f, g, cs, ct, dict(cap_b=2, cap_paths=16, sample=True, ghat=False))
            try:
                R.go()
            except X.Abort:
                C['abort'] += 1
        sv.save(ctx)
    sv.save(ctx, final=True)
    print(json.dumps(dict(lane='geo', runs=C['runs'], faces=C['a1.geo.faces'], secs=round(time.time() - t0))))


VARIANTS = {
    'V0_root0': dict(pick='tree', root='0', read='0', c_stats=True),
    'V1_root1_reversed': dict(pick='tree', root='1', read='0'),
    'V1_rootrand': dict(pick='tree', root='rand', read='0'),
    'V2a_wrongread_rightdart': dict(pick='tree', root='1', read='wrong'),
    'V2b_wrongread_dart_by_read': dict(pick='tree', root='1', read='wrong', rule='readdir', tolerant=True),
    'Vd_dag_wrongread': dict(pick='dag', read='wrong'),
    'Vd_dag_randread': dict(pick='dag', read='rand'),
}


def small_or_planar(rng, maps):
    r = rng.random()
    if r < .55:
        n, ends, rot = rng.choice(maps)
        m = len(ends)
        sc = rng.choice(['one', 'one', 'r012', 'r12', 'z01', 'r123'])
        cap = {'one': [1] * m, 'r012': [rng.randint(0, 2) for _ in range(m)], 'r12': [rng.randint(1, 2) for _ in range(m)],
               'z01': [rng.randint(0, 1) for _ in range(m)], 'r123': [rng.randint(1, 3) for _ in range(m)]}[sc]
        s, t = rng.sample(range(n), 2)
        return X.Inst(n, [tuple(e) for e in ends], rot, cap, s, t, tag='small:' + sc), rng
    return F.make(rng.randrange(10 ** 9), None, 40)


def lane_C(out, maxsec, seed):
    allm = json.load(open(MAPS))
    maps = allm['6'] + allm['7'] + allm['8']
    ctxs = {k: X.Ctx() for k in VARIANTS}
    sv = {k: Saver(out + '.' + k + '.json', dict(lane='C', variant=k, opts=VARIANTS[k])) for k in VARIANTS}
    rng = random.Random(seed)
    t0 = time.time()
    k = 0
    while time.time() - t0 < maxsec:
        I, r2 = small_or_planar(rng, maps)
        k += 1
        lst = list(all_choices(I))
        rng.shuffle(lst)
        for f, g, cs, ct in lst[:3]:
            for idseed in (1, 2):
                for name, vopts in VARIANTS.items():
                    opts = dict(vopts)
                    opts.update(idseed=idseed, cap_b=3, cap_paths=24, sample=True, ghat=False)
                    ch = X.PolicyCh(random.Random(seed * 7919 + k + idseed), rng.choice(POLS))
                    if name.startswith('Vd') and idseed == 2:
                        continue
                    R = X.Run(I, ctxs[name], ch, f, g, cs, ct, opts)
                    try:
                        R.go()
                    except X.Abort as ex:
                        ctxs[name].C['abort'] += 1
                        ctxs[name].C['abort:' + str(ex)[:30]] += 1
                    except (KeyError, ValueError, IndexError) as ex:
                        ctxs[name].C['crash'] += 1
                        ctxs[name].C['crash:' + type(ex).__name__] += 1
        for name in VARIANTS:
            sv[name].save(ctxs[name])
    for name in VARIANTS:
        sv[name].save(ctxs[name], final=True)
    print(json.dumps({name: ctxs[name].C['runs'] for name in VARIANTS}))


CTLS = {
    'rule_flip': dict(rule='flip', tolerant=True),
    'name_flip': dict(name_flip=True, tolerant=True),
    'name_swap': dict(name_swap=1, tolerant=True),
}


def lane_ctl(out, maxsec, seed):
    allm = json.load(open(MAPS))
    maps = allm['6'] + allm['7'] + allm['8']
    ctxs = {k: X.Ctx() for k in CTLS}
    sv = {k: Saver(out + '.' + k + '.json', dict(lane='ctl', variant=k, opts=CTLS[k])) for k in CTLS}
    rng = random.Random(seed)
    t0 = time.time()
    while time.time() - t0 < maxsec:
        I, r2 = small_or_planar(rng, maps)
        lst = list(all_choices(I))
        rng.shuffle(lst)
        for f, g, cs, ct in lst[:3]:
            for name, vopts in CTLS.items():
                opts = dict(vopts)
                if name == 'name_swap':
                    opts['name_swap'] = rng.randrange(10 ** 6)
                opts.update(cap_b=3, cap_paths=24, sample=True, ghat=False)
                ch = X.PolicyCh(rng, 'rand')
                R = X.Run(I, ctxs[name], ch, f, g, cs, ct, opts)
                try:
                    R.go()
                except X.Abort as ex:
                    ctxs[name].C['abort'] += 1
                except (KeyError, ValueError, IndexError) as ex:
                    ctxs[name].C['crash'] += 1
                    ctxs[name].C['crash:' + type(ex).__name__] += 1
                ctxs[name].C['attempts'] += 1
        for name in CTLS:
            sv[name].save(ctxs[name])
    for name in CTLS:
        sv[name].save(ctxs[name], final=True)
    print(json.dumps({name: ctxs[name].C['attempts'] for name in CTLS}))


if __name__ == '__main__':
    lane, out, maxsec = sys.argv[1], sys.argv[2], float(sys.argv[3])
    a = sys.argv[4:]
    if lane == 'exh':
        lane_exh(out, maxsec, int(a[0]), int(a[1]), int(a[2]), int(a[3]) if len(a) > 3 else 30)
    elif lane == 'rand8':
        lane_rand8(out, maxsec, int(a[0]))
    elif lane == 'planar':
        lane_planar(out, maxsec, int(a[0]), a[1] if len(a) > 1 and a[1] != 'any' else None, int(a[2]) if len(a) > 2 else 60)
    elif lane == 'hard':
        lane_hard(out, maxsec)
    elif lane == 'geo':
        lane_geo(out, maxsec, int(a[0]))
    elif lane == 'mut':
        lane_mut(out, maxsec, int(a[0]))
    elif lane == 'C':
        lane_C(out, maxsec, int(a[0]))
    elif lane == 'ctl':
        lane_ctl(out, maxsec, int(a[0]))
    else:
        raise SystemExit('unknown lane')
