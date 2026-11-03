"""Hill-climbing toward stress conditions of Lemma O / Lemma S2.

State: an instance (rotation system, capacities, s, t). Score: over R runs with worst-case
policies (adv.Chooser 'policy'), a weighted count of rare conditions per incision (both bounds,
both bounds with overlap, overlap on both sides, linear nodes split in three, old end edges at
both ends, U or V crossing gamma, i1/i2 outside the range, deep levels, an overlap side made of
several subgraphs) plus 10^6 for any failed check or wrong final value. Mutations: capacity,
edge added inside a face, edge removed (keep connected), subdivision, parallel edge, s or t moved
to a neighbour, s/t swapped. Restart from a fresh instance every RESTART steps. GEO=1 adds the
topological curve-model checks (geo.py) to every run.

Usage: python3 -I hill.py SEED OUT.json [maxsec] [R]
"""
import sys
import os
import json
import time
import random
import collections

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import adv
import gens

T = adv.T
GEO = os.environ.get('GEO') == '1'
W = {'both_bounds': 2, 'both_bounds_and_overlap': 4, 'overlap_both': 6, 'lin_split3': 6, 'old_end_both': 1,
     'U_or_V_crosses': 3, 'i12_outside': 1, 'level>=6': 3, 'Q_linear_nodes>=3': 2, 'x_eq_y': 0.2,
     't_strict_between_xy_in_range': 1, 'child_both_bounds': 1}
WS = {'O2_overlap_side_split': 6, 'O_c23_chk_below_j': 0.05, 'R_full_only_overlap': 2, 'O_node_iv_split3': 3,
      'R_full_neq': 3, 'R_full_z_fail_need': 40, 'R_full_loses_side_min': 200}


def evaluate(I, R, prng, cnt_all, fails):
    sc = 0.0
    for r in range(R):
        cnt = collections.Counter()
        opts = adv.base_opts(pfar=prng.choice([0.0, 0.5, 1.0]), pcommon=0.0)
        ch = adv.Chooser(mode='policy', pols=[prng.choice(list(adv.POLICIES))], cap=300, prng=prng, cnt=cnt)
        chk, info, bad = adv.run(I, opts, random.Random(prng.random()), ch, cnt, geo=GEO)
        cnt['runs'] += 1
        cnt['levels_max'] = info.get('levels', 0)
        for k, w in W.items():
            sc += w * cnt[k]
        for k, w in WS.items():
            v = info.get(k, 0)
            if isinstance(v, int):
                sc += w * v
                cnt['ostat_' + k] += v
        for k, v in cnt.items():
            if k == 'levels_max':
                cnt_all[k] = max(cnt_all[k], v)
            else:
                cnt_all[k] += v
        for k in chk.flags:
            cnt_all['flag_' + k] += 1
        if bad:
            fails.append(dict(I=I, flags=dict(chk.flags), notes=[str(x)[:400] for x in chk.notes[:6]]))
            print('FAIL', dict(chk.flags), flush=True)
            sc += 1e6
    return sc / R


def mutate(I, rng):
    B = T.Builder(I['n'], [tuple(e) for e in I['ends']], I['rot'])
    cap = list(I['cap'])
    s, t = I['s'], I['t']
    op = rng.choice(['cap', 'cap', 'cap', 'add', 'add', 'rem', 'sub', 'par', 'mvs', 'mvt', 'swap'])
    try:
        if op == 'cap':
            for _ in range(rng.randint(1, 3)):
                cap[rng.randrange(len(cap))] = rng.choice([0, 1, 1, 2, 3, 5])
        elif op == 'add':
            F = [f for f in B.faces() if len(f) >= 4]
            if not F:
                return None
            f = rng.choice(F)
            a, b = rng.sample(range(len(f)), 2)
            if B.head(f[a]) == B.head(f[b]):
                return None
            B.add_edge_in_face(f[a], f[b])
            cap.append(rng.choice([0, 1, 1, 2]))
        elif op == 'rem':
            e = rng.randrange(len(B.ends))
            B2, keep = B.remove_edges({e})
            if not B2.connected() or B2.n < 3:
                return None
            B = B2
            cap = [cap[k] for k in keep]
        elif op == 'sub':
            if B.n >= 70:
                return None
            e = rng.randrange(len(B.ends))
            B.subdivide(e)
            cap.append(cap[e] if rng.random() < 0.7 else rng.choice([0, 1, 2]))
        elif op == 'par':
            e = rng.randrange(len(B.ends))
            B.add_parallel(e)
            cap.append(rng.choice([0, 1, cap[e]]))
        elif op in ('mvs', 'mvt'):
            v = s if op == 'mvs' else t
            w = rng.choice([B.head(d) for d in B.rot[v]])
            if w == (t if op == 'mvs' else s):
                return None
            if op == 'mvs':
                s = w
            else:
                t = w
        else:
            s, t = t, s
    except (AssertionError, ValueError, IndexError):
        return None
    if not (B.connected() and B.euler_ok()) or len(B.ends) > 220:
        return None
    J = dict(I)
    J.update(n=B.n, ends=list(B.ends), rot=[list(r) for r in B.rot], cap=cap, s=s, t=t, op=op)
    return J


def main():
    seed, out = int(sys.argv[1]), sys.argv[2]
    maxsec = float(sys.argv[3]) if len(sys.argv) > 3 else 3300
    R = int(sys.argv[4]) if len(sys.argv) > 4 else 4
    RESTART = 150
    rng = random.Random(seed)
    cnt = collections.Counter()
    fails = []
    t0 = time.time()
    best = (0, None)
    steps = restarts = 0
    while time.time() - t0 < maxsec and not fails:
        I = gens.make(rng.randrange(10 ** 9))
        if I['n'] > 70:
            continue
        restarts += 1
        cur = evaluate(I, R, rng, cnt, fails)
        for k in range(RESTART):
            if time.time() - t0 > maxsec or fails:
                break
            J = mutate(I, rng)
            if J is None:
                continue
            steps += 1
            sc = evaluate(J, R, rng, cnt, fails)
            if sc >= cur or rng.random() < 0.05:
                I, cur = J, sc
            if cur > best[0]:
                best = (cur, I)
    res = dict(seed=seed, geo=GEO, variant=os.environ.get('THMD_VARIANT', 'R'), steps=steps, restarts=restarts, counts=dict(cnt), best_score=best[0],
               best=best[1], nfail=len(fails), fails=fails[:5], secs=round(time.time() - t0, 1))
    json.dump(res, open(out, 'w'), indent=1, default=str)
    print(json.dumps(dict(seed=seed, steps=steps, restarts=restarts, runs=cnt['runs'], inc=cnt['inc'],
                          nfail=len(fails), best=best[0], secs=res['secs'])))


if __name__ == '__main__':
    main()
