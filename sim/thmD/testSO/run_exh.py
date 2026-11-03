"""Exhaustive small cases: every plane map with m edges (enum_maps.py), every ordered (s, t),
several capacity vectors, and EVERY run of the recursion (all f, g, all legal corners and modes
(anycorner), every w-shortest P, every w-shortest P_i at every annulus, every overlap source z),
up to a cap of runs per instance. All Lemma O / extra checks of thmD_R.py, the final value,
and (GEO=1) the topological curve-model checks of geo.py.

STPAIRS=k samples k ordered (s, t) pairs per map and capacity vector. MAPLO=i skips the maps with index < i
(to finish a shard that stopped early).
Usage: python3 -I run_exh.py MAPS.json M SHARD NSHARDS OUT.json [caps=one,zero,r012,r012b,gen] [maxruns] [maxsec]
"""
import sys
import os
import json
import time
import random
import itertools
import collections

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import adv

mapsf, M, shard, nsh, out = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
capsch = (sys.argv[6] if len(sys.argv) > 6 else 'one,zero,r012,r012b,gen').split(',')
maxruns = int(sys.argv[7]) if len(sys.argv) > 7 else 300
maxsec = float(sys.argv[8]) if len(sys.argv) > 8 else 3300
GEO = os.environ.get('GEO') == '1'
STPAIRS = int(os.environ.get('STPAIRS', '0'))
MAPLO = int(os.environ.get('MAPLO', '0'))
maps = json.load(open(mapsf))[str(M)]


def capvecs(m, seed):
    rng = random.Random(seed)
    out = []
    for sc in capsch:
        if sc == 'one':
            out.append(('one', [1] * m))
        elif sc == 'zero':
            out.append(('zero', [0] * m))
        elif sc in ('r012', 'r012b'):
            out.append((sc, [rng.randint(0, 2) for _ in range(m)]))
        elif sc == 'r12':
            out.append(('r12', [rng.randint(1, 2) for _ in range(m)]))
        elif sc == 'gen':
            out.append(('gen', [rng.randint(1, 10 ** 6) for _ in range(m)]))
        elif sc == 'all012':
            out += [('all012', list(v)) for v in itertools.product(range(3), repeat=m)]
        elif sc == 'all01':
            out += [('all01', list(v)) for v in itertools.product(range(2), repeat=m)]
    return out


cnt = collections.Counter()
fails = []
t0 = time.time()
opts = adv.base_opts()
ninst = nincomplete = done_maps = 0
stopped = False
for mi, (n, ends, rot) in enumerate(maps):
    if mi % nsh != shard or mi < MAPLO:
        continue
    if time.time() - t0 > maxsec:
        stopped = True
        break
    done_maps += 1
    for cname, cap in capvecs(len(ends), 1000 * mi + M):
        pairs = [(s, t) for s in range(n) for t in range(n) if s != t]
        if STPAIRS and len(pairs) > STPAIRS:
            pairs = random.Random(mi * 31 + len(cap)).sample(pairs, STPAIRS)
        for s, t in pairs:
            if True:
                I = dict(n=n, ends=[tuple(e) for e in ends], rot=rot, cap=cap, s=s, t=t)
                ninst += 1
                nr, complete, fl = adv.explore(I, opts, max_runs=maxruns, cnt=cnt, stop_on_fail=True, geo=GEO)
                if not complete and not fl:
                    nincomplete += 1
                if fl:
                    fails.append(dict(map=mi, caps=cname, I=I, fail=fl[0]))
                    print('FAIL', mi, cname, s, t, fl[0]['flags'], flush=True)
res = dict(maps=mapsf, M=M, shard=shard, nshards=nsh, caps=capsch, maxruns=maxruns, geo=GEO, done_maps=done_maps,
           total_maps=len(maps), stopped_early=stopped, instances=ninst, incomplete=nincomplete, counts=dict(cnt),
           nfail=len(fails), fails=fails[:50], secs=round(time.time() - t0, 1))
json.dump(res, open(out, 'w'), indent=1, default=str)
print(json.dumps(dict(M=M, shard=shard, maps=done_maps, inst=ninst, runs=cnt['runs'], incomplete=nincomplete,
                      inc=cnt['inc'], nfail=len(fails), secs=res['secs'])))
