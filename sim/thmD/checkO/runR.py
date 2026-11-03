"""Run the Lemma O checks of thmD_O.py on generated instances.

Usage: python3 -I runO.py START COUNT OUT.json [tiebreak] [size] [grid] [pcommon] [pfar]
"""
import sys
import os
import json
import time
import collections

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import thmD_R as T

start, count, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
tieb = sys.argv[4] if len(sys.argv) > 4 else 'random'
if len(sys.argv) > 5:
    T.SIZE_MAX = int(sys.argv[5])
if len(sys.argv) > 6:
    T.GRID_MAX = int(sys.argv[6])
pcommon = float(sys.argv[7]) if len(sys.argv) > 7 else 0.5
pfar = float(sys.argv[8]) if len(sys.argv) > 8 else 0.3
opts = dict(mode='claimed', variant='fixed', tiebreak=tieb, pairs=1, pcommon=pcommon, pfar=pfar,
            e0rule=os.environ.get('E0RULE', 'formal'), ends=1, lemO=1)
tot = collections.Counter()
stat = collections.Counter()
fails = []
t0 = time.time()
for sd in range(start, start + count):
    I = T.make_instance(sd, None)
    chk, info = T.run_one(I, opts, sd * 1000 + 7)
    tot['runs'] += 1
    for k, v in info.items():
        if isinstance(k, str) and k.startswith(('O', 'R_')) and isinstance(v, int):
            stat[k] += v
            stat['inst_' + k] += 1
    bad = {k: v for k, v in chk.flags.items() if not k.startswith(('dev_', 'xa_', 'xb_'))}
    for k in chk.flags:
        tot[k] += 1
    if bad:
        fails.append(dict(seed=sd, flags=dict(chk.flags), notes=[str(x)[:300] for x in chk.notes[:8]]))
res = dict(opts=opts, start=start, count=count, size=T.SIZE_MAX, grid=T.GRID_MAX, flags=dict(tot),
           stats=dict(stat), nfail=len(fails), fails=fails[:100], secs=time.time() - t0)
with open(out, 'w') as fh:
    json.dump(res, fh, indent=1, default=str)
print(json.dumps(dict(flags=dict(tot), nfail=len(fails), secs=round(time.time() - t0, 1))))
