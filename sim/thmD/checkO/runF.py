"""Full-path reading of the overlap test (the bounding path = the whole P_i of the incising annulus).
Lemma O checks are off; we look only at the final value (iv_value) and the lengths.
Usage: python3 -I runF.py START COUNT OUT.json [tiebreak] [size] [grid] [pcommon] [pfar]"""
import sys, os, json, time, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import thmD_F as T
start, count, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
tieb = sys.argv[4] if len(sys.argv) > 4 else 'random'
if len(sys.argv) > 5:
    T.SIZE_MAX = int(sys.argv[5])
if len(sys.argv) > 6:
    T.GRID_MAX = int(sys.argv[6])
pcommon = float(sys.argv[7]) if len(sys.argv) > 7 else 0.5
pfar = float(sys.argv[8]) if len(sys.argv) > 8 else 0.3
opts = dict(mode='claimed', variant='fixed', tiebreak=tieb, pairs=1, pcommon=pcommon, pfar=pfar,
            e0rule='formal', ends=1, lemO=0)
tot = collections.Counter()
wrong = []
t0 = time.time()
for sd in range(start, start + count):
    I = T.make_instance(sd, None)
    chk, info = T.run_one(I, opts, sd * 1000 + 7)
    tot['runs'] += 1
    for k in chk.flags:
        tot[k] += 1
    if 'iv_value' in chk.flags:
        wrong.append(dict(seed=sd, n=I['n'], m=len(I['ends']), val=str(chk.flags.get('iv_value'))[:200]))
res = dict(opts=opts, flags=dict(tot), wrong=wrong[:200], nwrong=len(wrong), secs=time.time() - t0)
json.dump(res, open(out, 'w'), indent=1, default=str)
print(json.dumps(dict(flags=dict(tot), nwrong=len(wrong), secs=round(time.time() - t0, 1))))
