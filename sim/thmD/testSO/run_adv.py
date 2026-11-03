"""Worst-case tie-breaking on larger instances (gens.py: long strips, rings with a hub,
triangulations, the driver's families with tie-heavy capacities). Every instance is run R times;
each run picks, at every P_i, a shortest path by a policy drawn from POLS (adv.POLICIES:
maximise overlap with the bounds, run Q along a bound, many copies of P, small or large
i2 - i1, x = y, drop as many argmin indices of lambda as possible, push i1, i2 outside the
range, ...), P uniformly among all shortest paths, and f, g, corners (anycorner) and the overlap
source z at random. All Lemma O / extra checks, the final value, and with GEO=1 the
topological curve-model checks (geo.py). THMD_VARIANT=F: whole-path overlap reading.

Usage: python3 -I run_adv.py START COUNT OUT.json [R] [fam|any] [pols|all] [maxsec]
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

start, count, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
R = int(sys.argv[4]) if len(sys.argv) > 4 else 4
fam = sys.argv[5] if len(sys.argv) > 5 and sys.argv[5] != 'any' else None
pols = sys.argv[6].split(',') if len(sys.argv) > 6 and sys.argv[6] != 'all' else list(adv.POLICIES)
maxsec = float(sys.argv[7]) if len(sys.argv) > 7 else 3300
GEO = os.environ.get('GEO') == '1'

cnt = collections.Counter()
ostat = collections.Counter()
fails = []
t0 = time.time()
ninst = 0
for sd in range(start, start + count):
    if time.time() - t0 > maxsec:
        break
    I = gens.make(sd, fam)
    ninst += 1
    cnt['fam_' + I['family']] += 1
    for r in range(R):
        prng = random.Random(sd * 7919 + r)
        opts = adv.base_opts(pfar=prng.choice([0.0, 0.5, 1.0]), pcommon=prng.choice([0.0, 0.2]))
        polset = [prng.choice(pols)] if prng.random() < 0.5 else pols
        ch = adv.Chooser(mode='policy', pols=polset, cap=400, prng=prng, cnt=cnt)
        chk, info, bad = adv.run(I, opts, random.Random(sd * 104729 + r), ch, cnt, geo=GEO)
        cnt['runs'] += 1
        lv = info.get('levels', 0)
        cnt['levels_max'] = max(cnt['levels_max'], lv)
        cnt['levels=%d' % lv] += 1
        for k, v in info.items():
            if isinstance(k, str) and k.startswith(('O', 'R_')) and isinstance(v, int):
                ostat[k] += v
        for k in chk.flags:
            cnt['flag_' + k] += 1
        if bad:
            fails.append(dict(seed=sd, r=r, fam=I['family'], pols=polset, flags=dict(chk.flags),
                              notes=[str(x)[:400] for x in chk.notes[:6]], I=I))
            print('FAIL', sd, r, I['family'], dict(chk.flags), flush=True)
res = dict(variant=os.environ.get('THMD_VARIANT', 'R'), geo=GEO, start=start, count=count, done=ninst, R=R, fam=fam,
           pols=pols, counts=dict(cnt), ostats=dict(ostat), nfail=len(fails), fails=fails[:30],
           secs=round(time.time() - t0, 1))
json.dump(res, open(out, 'w'), indent=1, default=str)
print(json.dumps(dict(start=start, done=ninst, runs=cnt['runs'], inc=cnt['inc'], both=cnt['both_bounds'],
                      nfail=len(fails), secs=res['secs'])))
