"""Run the ORIGINAL sim/s9/engine_r.py (unmodified, imported read-only) and compare its holes() with the
exact count (Euler/Alexander) at every bag; check B4 on the original engine's bags."""
import sys, os, random, collections
REPO = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')
sys.path.insert(0, os.path.join(REPO, 'attack3')); sys.path.insert(0, os.path.join(REPO, 's9'))
import numpy as np
from sweep import CONF, params
from geo import FAMS, virtual_candidates, drawing_ok
from core import PG, Fail
import engine_r
import rsweep  # registers advb0/pxb/chb into CONF
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from engine_r9 import Engine as E9
conf = sys.argv[1]; a, b = map(int, sys.argv[2].split(':'))
fams = ['dl', 'grid', 'k2m', 'fan', 'nested', 'pend', 'flower']
C = collections.Counter(); M = collections.defaultdict(int)
for s in range(a, b):
    r = random.Random(s * 31 + 7); fam = fams[s % 7]; args = params(fam, r)
    pos, E = FAMS[fam](s, args)
    g = PG(pos, E, seed=s)
    cfg = dict(CONF[conf]); cfg['leaf'] = r.choice([6, 8, 10, 14])
    eng = engine_r.Engine(g, virtual_candidates(pos, E), random.Random(s * 7919 + 1), cfg)
    try:
        eng.run()
    except Fail as ex:
        C['FAIL'] += 1; continue
    ex = E9(g, set(), random.Random(0), dict(light=True))
    hx = {}
    for bb, B in eng.bags.items():
        he = ex.holes_euler(B['E']); ho = eng.holes(B['E']); hx[bb] = he
        C['bags'] += 1; C['under'] += ho < he; C['over'] += ho > he
        M['under_by'] = max(M['under_by'], he - ho); M['h_minus_depth'] = max(M['h_minus_depth'], he - B['depth'])
        M['h_max'] = max(M['h_max'], he)
    for bb, B in eng.bags.items():
        if B['parent'] is not None:
            C['B4_checks'] += 1
            if hx[bb] > hx[B['parent']] + 1:
                C['B4_VIOL'] += 1; print('B4 VIOL', conf, fam, s, bb, hx[B['parent']], hx[bb])
print(conf, dict(C), dict(M))
