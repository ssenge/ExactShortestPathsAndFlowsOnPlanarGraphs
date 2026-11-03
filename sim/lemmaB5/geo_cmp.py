"""my implementation vs b5.py on b5.py's own geometric instances (its instance() generator),
the instance's (root, corner) plus extra random (root, corner) pairs.
usage: geo_cmp.py START END EXTRA"""
import sys, os, time, random
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import harness as H
from gen import parents
from mine import Fail
REF = H.REF
a, b, extra = map(int, sys.argv[1:4])
fams = list(REF.FAMS) + list(REF.FAMS9)
t0 = time.time(); fails = 0
for s in range(a, b):
    fam = fams[s % len(fams)]
    inst = REF.instance(fam, s)
    if inst is None:
        H.TOT['bad_drawing'] += 1; continue
    V, rot, idx, par, depth, children, root, k, RG, mode, keep = inst
    n = len(V)
    if n < 4:
        continue
    S = [(v, par[v]) for v in V if par[v] is not None]
    rng = random.Random(s)
    pairs = [(root, k)] + [(r, rng.randrange(len(rot[r]))) for r in rng.sample(V, min(extra, n))]
    for r, kk in pairs:
        p = par if r == root else parents(V, S, r)
        try:
            H.check(V, rot, p, r, kk, deep=(n <= 150))
            H.upd('n_max', n)
        except Exception as ex:
            fails += 1; H.TOT['FAIL'] += 1
            if fails <= 10: print('FAIL', fam, s, mode, r, kk, repr(ex)[:300], flush=True)
print('geo seeds', a, b, 'time', round(time.time() - t0, 1))
H.report()
