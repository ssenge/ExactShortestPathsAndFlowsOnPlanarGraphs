"""The decomposition of [3], own implementation: bullet checks, empirical quality, give-ups, and needed t on built and climbed instances.

  a4_ldd.py bullets <seed> <secs>      weak diameter, zero-weight arcs, cut rates per arc over planar families and c
  a4_ldd.py wheel <secs>               the hub-rim family: all heavy on level d, all rim vertices light on level d/2
  a4_ldd.py climb <seed> <secs> <c>    hill climbing on the needed t with R = 1
  a4_ldd.py sweep <secs>               final potential wrong, by (c, t, R), on the families
"""
import collections
import json
import math
import os
import random
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from core import *
import networkx as nx


def grid_net(a, b):
    E = []
    for i in range(a):
        for j in range(b):
            x = i * b + j
            if j + 1 < b:
                E.append((x, x + 1))
            if i + 1 < a:
                E.append((x, x + b))
    return a * b, E


def fam_general(rng):
    kind = rng.randrange(6)
    if kind == 0:   # directed cycle, unit or zero weights
        n = rng.randrange(4, 80)
        z = rng.choice([0, 0.5, 0.9])
        return n, [(i, (i + 1) % n, 0 if rng.random() < z else 1) for i in range(n)], 'cycle'
    if kind == 1:   # bidirected grid
        a, b = rng.randrange(2, 10), rng.randrange(2, 10)
        n, E = grid_net(a, b)
        W = rng.choice([1, 2, 8])
        z = rng.choice([0, 0.5, 0.9, 0.99])
        arcs = []
        for x, y in E:
            for u, v in ((x, y), (y, x)):
                arcs.append((u, v, 0 if rng.random() < z else rng.randrange(1, W + 1)))
        return n, arcs, 'grid'
    if kind == 2:   # bidirected path, weights 1
        n = rng.randrange(4, 80)
        arcs = []
        for i in range(n - 1):
            arcs += [(i, i + 1, 1), (i + 1, i, 1)]
        return n, arcs, 'path'
    if kind == 3:   # wheel, hub with zero spokes one way
        n = rng.randrange(5, 60)
        arcs = []
        for i in range(1, n):
            arcs.append((0, i, rng.choice([0, 1, 5])))
            arcs.append((i, 0, rng.choice([0, 1, 5])))
            arcs.append((i, i % (n - 1) + 1, rng.choice([0, 1])))
        return n, arcs, 'wheel'
    if kind == 4:   # star of directed cycles with zero weights (zero-weight SCCs)
        k = rng.randrange(2, 8)
        L = rng.randrange(2, 8)
        arcs = []
        n = 1
        for _ in range(k):
            vs = list(range(n, n + L))
            n += L
            for a, b in zip(vs, vs[1:] + vs[:1]):
                arcs.append((a, b, 0))
            arcs += [(0, vs[0], 1), (vs[0], 0, rng.choice([1, 3]))]
        return n, arcs, 'flower'
    n = rng.randrange(4, 50)
    arcs = [(i, i + 1, rng.choice([0, 1])) for i in range(n - 1)]
    return n, arcs, 'dipath'


def scc_diam_ok(n, arcs, kept, d, c, tag):
    comp = tarjan_order(n, kept)
    groups = collections.defaultdict(list)
    for v in range(n):
        groups[comp[v]].append(v)
    bad = 0
    for g in groups.values():
        if len(g) == 1:
            continue
        for s in g:
            ds = oracle(n, arcs, [0 if v == s else None for v in range(n)], Stats())
            if any(ds[x] > d for x in g):
                bad += 1
                break
    return bad, comp


def bullets(seed, secs):
    rng = random.Random(seed)
    res = collections.Counter()
    worstQ = collections.defaultdict(float)
    end = time.time() + secs
    while time.time() < end:
        n, arcs, name = fam_general(rng)
        lim = 12
        for cc in (1.0, 2.0, 4.0):
            for d in (1, 2, 3, 4, 8, 16, 64, 2 * n * n):
                rem_count = collections.Counter()
                cut_count = collections.Counter()
                T = 20
                for _ in range(T):
                    st = Stats()
                    er = ldd(n, arcs, d, rng, cc, st=st)
                    kept = [a for i, a in enumerate(arcs) if i not in er]
                    bad, comp = scc_diam_ok(n, arcs, kept, d, res, name)
                    res['runs'] += 1
                    res['FAIL.weak_diameter'] += bad
                    # control: weak diameter with d - 1 fires sometimes
                    if d > 1 and scc_diam_ok(n, arcs, kept, d // 2 - 1 if d > 3 else 0, res, name)[0]:
                        res['ctl.weak_diam_tighter_fires'] += 1
                    res['giveup', cc] += st['ldd_giveup']
                    res['maxdepth'] = max(res['maxdepth'], st['ldd_maxdepth'])
                    if not st['ldd_giveup']:
                        zero = sum(1 for i in er if arcs[i][2] == 0)
                        res['zero_in_rem_without_giveup'] += zero
                    for i in er:
                        rem_count[i] += 1
                    for i, (u, v, w) in enumerate(arcs):
                        if comp[u] > comp[v]:
                            cut_count[i] += 1
                            if i not in er:
                                res['FAIL.cut_not_in_rem'] += 1
                for i, x in cut_count.items():
                    w = arcs[i][2]
                    if w > 0:
                        q = (x / T) * d / (w * math.log2(max(n, 2)) ** 2)
                        if d >= 4:
                            worstQ[cc] = max(worstQ[cc], q)
        if time.time() > end:
            break
    out = {str(k): v for k, v in sorted(res.items(), key=str)}
    out['empirical max of Pr[cut] d/(w log2^2 n), d>=4, by c'] = dict(worstQ)
    print(json.dumps(out))


# ---------- needed t

def needed(n, arcs, R, c, rng, label='tarjan', net=None):
    """For every level > 1: max over (r, v) of least, over r', of the cut arcs on a shortest path. No alternation is run."""
    L = 1
    while 2 ** L < 2 * n * n:
        L += 1
    ge = [(u, v, max(w, 0)) for u, v, w in arcs]
    prev = []
    worst = 0
    prof = []
    maxhops = 0
    for l in range(1, L + 1):
        cur = []
        for r in range(1 if l == L else R):
            st = Stats()
            rem = set() if l == L else ldd(n, ge, 2 ** l, rng, c, net=net, st=st)
            kept = [a for i, a in enumerate(ge) if i not in rem]
            idx = tarjan_order(n, kept)
            cur.append(idx)
            inside = [a for a in arcs if idx[a[0]] == idx[a[1]]]
            dist = bf(n, inside)
            if prev:
                tight = [(u, v) for u, v, w in inside if dist[u] + w == dist[v]]
                need = [INF] * n
                for pi in prev:
                    x = [0 if dist[v] == 0 else INF for v in range(n)]
                    for _ in range(n + 1):
                        ch = False
                        for u, v in tight:
                            if x[u] < INF:
                                y = x[u] + (1 if pi[u] > pi[v] else 0)
                                if y < x[v]:
                                    x[v] = y
                                    ch = True
                        if not ch:
                            break
                    need = [min(a, b) for a, b in zip(need, x)]
                m = max(need)
                prof.append((l, m))
                worst = max(worst, m)
        prev = cur
    return worst, prof


def wheel_instance(rim, pat, spoke, hub_leaves):
    """Hub 0, hub leaves, rim path. Rim weights follow pat; spokes both ways with weight spoke. Planar: a wheel with a pendant star.

    Every cycle through the hub: spoke + w(segment) + spoke >= hops + 2 needs spoke large; arcs above n are not allowed."""
    n = 1 + hub_leaves + rim
    arcs = []
    for i in range(1, hub_leaves + 1):
        arcs += [(0, i, 1), (i, 0, 1)]
    r0 = 1 + hub_leaves
    for i in range(rim):
        arcs += [(0, r0 + i, spoke), (r0 + i, 0, spoke)]
        if i + 1 < rim:
            arcs.append((r0 + i, r0 + i + 1, pat[i % len(pat)]))
    net = sorted({(min(a, b), max(a, b)) for a, b, w in arcs})
    return n, arcs, net


def wheel(secs):
    rng = random.Random(3)
    out = {}
    end = time.time() + secs
    for rim, pat in ((64, [-1, -1, 1]), (128, [-1, -1, 1]), (256, [-1, -1, 1]), (128, [-1, 1]), (256, [-1, 1]), (128, [-1, -1, -1, 1, 1]), (128, [-1, -1, 2])):
        for hub_mult in (1.5, 3):
            leaves = int(rim * hub_mult)
            # the smallest spoke that keeps the graph restricted
            lo, hi = 1, 4 * rim
            while hi - lo > 1:
                mid = (lo + hi) // 2
                n, arcs, net = wheel_instance(rim, pat, mid, leaves)
                if is_restricted(n, arcs):
                    hi = mid
                else:
                    lo = mid
            n, arcs, net = wheel_instance(rim, pat, hi, leaves)
            assert nx.check_planarity(nx.Graph(net))[0]
            for c in (1.0, 2.0, 4.0):
                vals = []
                vals3 = []
                for _ in range(2):
                    if time.time() > end:
                        break
                    vals.append(needed(n, arcs, 1, c, rng)[0])
                    vals3.append(needed(n, arcs, 3, c, rng)[0])
                out[f'rim={rim},pat={pat},leaves={leaves},spoke={hi},n={n},c={c}'] = {'R1': vals, 'R3': vals3}
                print(f'rim={rim},pat={pat},leaves={leaves},spoke={hi},n={n},c={c}', vals, vals3, flush=True)


def plane_seed(rng, nmax=70):
    """Plane instance as potentials on a plane net; arcs both ways where the weight stays within -1..n."""
    k = rng.randrange(3)
    if k == 0:
        a, b = rng.randrange(3, 9), rng.randrange(3, 9)
        n, net = grid_net(a, b)
    elif k == 1:
        n = rng.randrange(8, nmax)
        net = [(0, i) for i in range(1, n)] + [(i, i + 1) for i in range(1, n - 1)]
    else:
        n = rng.randrange(8, nmax)
        net = [(i, i + 1) for i in range(n - 1)] + [(0, n - 1)]
    order = list(range(n))
    rng.shuffle(order)
    p = [0] * n
    cur = 0
    for v in order:
        p[v] = cur
        cur += rng.choice([2, 2, 2, 1, -1, -3])
    return dict(n=n, net=net, p=p, slack={})


def inst_arcs(I):
    n, net, p, slack = I['n'], I['net'], I['p'], I['slack']
    arcs = []
    for x, y in net:
        for u, v in ((x, y), (y, x)):
            s = slack.get((u, v), 0)
            d = p[u] - p[v]
            w = 1 + s + d
            if w < -1:
                w += -1 - w
            if w <= n:
                arcs.append((u, v, w))
    return n, arcs


def score(I, c, rng, runs=2):
    n, arcs = inst_arcs(I)
    if not arcs:
        return -1, None
    tot = 0
    for _ in range(runs):
        tot += needed(n, arcs, 1, c, rng)[0]
    return tot / runs, None


def climb(seed, secs, c):
    rng = random.Random(seed)
    best_overall = -1
    best_I = None
    end = time.time() + secs
    evals = 0
    while time.time() < end:
        I = plane_seed(rng)
        s, _ = score(I, c, rng)
        for step in range(60):
            if time.time() > end:
                break
            J = dict(I)
            J['p'] = list(I['p'])
            J['slack'] = dict(I['slack'])
            for _ in range(rng.randrange(1, 4)):
                v = rng.randrange(J['n'])
                r = rng.random()
                if r < 0.6:
                    J['p'][v] += rng.choice([-2, -1, 1, 2])
                elif r < 0.8:
                    # shift a suffix: more rise along a path
                    delta = rng.choice([-2, -1, 1, 2])
                    for u in range(v, J['n']):
                        J['p'][u] += delta
                else:
                    x, y = rng.choice(J['net'])
                    J['slack'][(x, y) if rng.random() < 0.5 else (y, x)] = rng.choice([0, 1, 3])
            s2, _ = score(J, c, rng)
            evals += 1
            if s2 >= s:
                I, s = J, s2
            if s > best_overall:
                best_overall, best_I = s, I
    n, arcs = inst_arcs(best_I)
    vals = [needed(n, arcs, 1, c, rng)[0] for _ in range(6)]
    vals3 = [needed(n, arcs, 3, c, rng)[0] for _ in range(3)]
    print(json.dumps(dict(evals=evals, best=best_overall, n=n, m=len(arcs), confirm_R1=vals, confirm_R3=vals3, restricted=is_restricted(n, arcs))))
    with open(f'climb_{seed}_{c}.json', 'w') as f:
        json.dump(dict(n=n, arcs=arcs), f)


def sweep(secs):
    """Wrong final potentials on the rim family, by c, t and R. Shows what t = 8, R = 3, c = 1 does and does not test."""
    rng = random.Random(9)
    res = collections.Counter()
    end = time.time() + secs
    cases = [(1.0, 8, 3), (1.0, 2, 2), (2.0, 8, 3), (4.0, 8, 3), (8.0, 8, 3), (16.0, 8, 3), (4.0, 32, 3), (16.0, 64, 3)]
    fams = [(40, [-1, -1, 1], 60), (40, [-1, 1], 60), (24, [-1, -1, 1], 36), (60, [-1, -1, 1], 90)]
    while time.time() < end:
        for rim, pat, leaves in fams:
            lo, hi = 1, 4 * rim
            while hi - lo > 1:
                mid = (lo + hi) // 2
                n, arcs, net = wheel_instance(rim, pat, mid, leaves)
                if is_restricted(n, arcs):
                    hi = mid
                else:
                    lo = mid
            n, arcs, net = wheel_instance(rim, pat, hi, leaves)
            for cc, t, R in cases:
                if time.time() > end:
                    break
                phi = restricted(n, arcs, R=R, t=t, c=cc, rng=rng, st=Stats())
                res[f'c={cc},t={t},R={R}', 'runs'] += 1
                if any(w + phi[u] - phi[v] < 0 for u, v, w in arcs):
                    res[f'c={cc},t={t},R={R}', 'wrong'] += 1
    print(json.dumps({str(k): v for k, v in sorted(res.items(), key=str)}, indent=0))


if __name__ == '__main__':
    p = sys.argv[1]
    if p == 'bullets':
        bullets(int(sys.argv[2]), float(sys.argv[3]))
    elif p == 'wheel':
        wheel(float(sys.argv[2]))
    elif p == 'climb':
        climb(int(sys.argv[2]), float(sys.argv[3]), float(sys.argv[4]))
    elif p == 'sweep':
        sweep(float(sys.argv[2]))
