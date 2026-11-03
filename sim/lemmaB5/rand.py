"""Random and structured combinatorial plane graphs. For each graph and spanning tree, run the
algorithm from every root and every start corner (or a sample), compare with b5.py, and check
the proof internals.
usage: python3 -I rand.py START END NMIN NMAX [fams] [deep_every] [maxroots]"""
import sys, os, time, random, collections
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fams import FAMS
from gen import random_spanning_tree, parents
from mine import Fail, mkidx, fan_all, random_virtual_marks, tpath, is_planar_rot
import harness as H

a, b, nmin, nmax = map(int, sys.argv[1:5])
fams = sys.argv[5].split(',') if len(sys.argv) > 5 and sys.argv[5] != 'all' else list(FAMS)
deep_every = int(sys.argv[6]) if len(sys.argv) > 6 else 10
maxroots = int(sys.argv[7]) if len(sys.argv) > 7 else 10 ** 9
t0 = time.time(); fails = 0; cnt = 0
famst = collections.Counter(); step3 = collections.Counter()
for s in range(a, b):
    fam = fams[s % len(fams)]
    rng = random.Random(1000003 * s + 17)
    n = rng.randint(nmin, nmax)
    V, rot = FAMS[fam](n, rng)
    n = len(V)
    if n < 4:
        continue
    if not is_planar_rot(rot, mkidx(rot)):
        H.TOT['skip_nonplanar_' + fam] += 1; continue
    mode = rng.choice(['bfs', 'bfs', 'dfs', 'rand'])
    r0, par0 = random_spanning_tree(V, rot, rng, mode)
    if len(par0) != len(V):
        H.TOT["skip_disconnected"] += 1; continue
    S = [(v, par0[v]) for v in V if par0[v] is not None]
    idx = mkidx(rot)
    roots = V[:] if len(V) <= maxroots else rng.sample(V, maxroots)
    for r in roots:
        par = parents(V, S, r)
        for k in range(len(rot[r])):
            cnt += 1
            try:
                res = H.check(V, rot, par, r, k, deep=(cnt % deep_every == 0))
                famst[fam] += 1
                if res['kind'] == 'virt':
                    step3[fam] += 1
                    if res['st'].get('chord_steps'):
                        H.TOT['virt_with_chord_steps'] += 1
                    if res['st'].get('e0_steps'):
                        H.TOT['virt_with_e0_step'] += 1
                    if 'e0' in res:
                        H.TOT['virt_with_heavy'] += 1
                    H.upd('max_j', res['j']); H.upd('max_m', res['m'])
                if cnt % (deep_every * 7) == 0:
                    H.TOT['rand_virt_marks'] += random_virtual_marks(V, rot, idx, par, r, k, rng, 6)
                if cnt % (deep_every * 13) == 0 and n <= 40:
                    H.TOT['fan_all_steps'] += fan_all(V, rot, idx, par, r, k, indep=(n <= 20))
            except Exception as ex:
                fails += 1; H.TOT['FAIL'] += 1
                if fails <= 20:
                    print('FAIL', fam, s, repr(ex), 'rot=', rot, 'par=', par, 'r=', r, 'k=', k, flush=True)
print('seeds', a, b, 'n', nmin, nmax, 'time', round(time.time() - t0, 1))
print('per family', dict(famst)); print('step3 per family', dict(step3))
H.report()
