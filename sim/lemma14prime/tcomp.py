"""Which knob drives comp(T[X]) growth?  python3 -I tcomp.py ZALL SWAP TXMODE START:END"""
import sys, os, random, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from sweep import params, MODES_ALL
from run import one
zall, swap, tx = float(sys.argv[1]), float(sys.argv[2]), sys.argv[3]
a, b = map(int, sys.argv[4].split(':'))
fams = ['dl', 'grid', 'k2m', 'nested', 'pend', 'flower', 'fan']
mx = collections.defaultdict(float); fails = 0; worst = None
for s in range(a, b):
    r = random.Random(s * 31 + 7); fam = fams[s % len(fams)]; args = params(fam, r)
    cfg = dict(modes=MODES_ALL, zall=zall, swap=swap, degenerate=False, txmode=tx, tries=120, leaf=r.choice([6, 8, 10, 14]), post=False)
    try: eng = one(fam, s, args, cfg)
    except AssertionError: continue
    fails += bool(eng.fails)
    v = eng.mx['T[X]comp_minus_depth']
    if v > mx['comp_minus_depth']: worst = (fam, s, args, v, eng.mx['TX_comp_of_T[X]_max'])
    for k in ('T[X]comp_minus_depth', 'TX_comp_of_T[X]_max'): mx[k] = max(mx[k], eng.mx[k])
    mx['comp_minus_depth'] = max(mx['comp_minus_depth'], v)
print('zall', zall, 'swap', swap, 'tx', tx, dict(mx), 'fails', fails, 'worst', worst)
