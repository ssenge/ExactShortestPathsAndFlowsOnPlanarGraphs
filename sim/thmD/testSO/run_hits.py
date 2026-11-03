"""The saved instances on which the unrepaired recursion of [18] misses the minimum
(testR/logs/search_simple.json, search_e2e_n4_12.json): explore EVERY run of the repaired
recursion on each (all f, g, corners and modes, every w-shortest P and P_i, every overlap source
z) up to a cap (a depth-first walk over the choice sequence), then RAND runs with random
worst-case policies and random choices, with the given capacities and with capacities collapsed to {1, 2} (many ties), plus the
topological curve-model checks (GEO=1).

Usage: python3 -I run_hits.py OUT.json [maxruns] [RAND]
ENDS=k selects the variant of the repair (patchSO.py); ENDS=0 (no repair) is the negative control.
"""
import sys
import os
import json
import time
import collections
import random

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import adv

HERE = os.path.dirname(os.path.abspath(__file__))
LOGS = os.path.join(HERE, '..', 'testR', 'logs')
if not os.path.isdir(LOGS):
    LOGS = os.path.join(HERE, '..', '..', 'ExactShortestPathsAndFlowsOnPlanarGraphs', 'sim', 'thmD', 'testR', 'logs')
out = sys.argv[1]
maxruns = int(sys.argv[2]) if len(sys.argv) > 2 else 1000
RAND = int(sys.argv[3]) if len(sys.argv) > 3 else 1000
GEO = os.environ.get('GEO') == '1'
hits = [h for f in ('search_simple.json', 'search_e2e_n4_12.json') for h in json.load(open(os.path.join(LOGS, f)))['hits']]
cnt = collections.Counter()
fails = []
t0 = time.time()
per = []
for h in hits:
    for cname in ('given', 'one_two', 'one'):
        if cname == 'given':
            cap = h['cap']
        elif cname == 'one':
            cap = [1] * len(h['cap'])
        else:
            med = sorted(h['cap'])[len(h['cap']) // 2]
            cap = [1 if c <= med else 2 for c in h['cap']]
        I = dict(n=h['n'], ends=[tuple(e) for e in h['ends']], rot=h['rot'], cap=cap, s=h['s'], t=h['t'])
        nr, complete, fl = adv.explore(I, adv.base_opts(), max_runs=maxruns, cnt=cnt, stop_on_fail=True, geo=GEO)
        nbad = 0
        for r in range(RAND if not fl else 0):
            prng = random.Random(h['seed'] * 7919 + r)
            opts = adv.base_opts(pfar=prng.choice([0.0, 0.5, 1.0]), pcommon=prng.choice([0.0, 0.2]))
            pols = [prng.choice(list(adv.POLICIES))] if prng.random() < 0.5 else list(adv.POLICIES)
            ch = adv.Chooser(mode='policy', pols=pols, cap=400, prng=prng, cnt=cnt)
            chk, info, bad = adv.run(I, opts, random.Random(h['seed'] * 104729 + r), ch, cnt, geo=GEO)
            cnt['runs'] += 1
            cnt['rand_runs'] += 1
            if bad:
                nbad += 1
                if not fl:
                    fl = [dict(flags=dict(chk.flags), notes=[str(x)[:400] for x in chk.notes[:6]], r=r, pols=pols)]
        cnt['rand_bad'] += nbad
        per.append((h['seed'], cname, nr, complete, nbad))
        cnt['instances'] += 1
        cnt['complete'] += complete
        if fl:
            fails.append(dict(seed=h['seed'], caps=cname, I=I, fail=fl[0]))
            print('FAIL', h['seed'], cname, fl[0]['flags'], flush=True)
res = dict(geo=GEO, ends=adv.base_opts()['ends'], maxruns=maxruns, rand=RAND, nhits=len(hits), counts=dict(cnt), per=per, nfail=len(fails), fails=fails[:10],
           secs=round(time.time() - t0, 1))
json.dump(res, open(out, 'w'), indent=1, default=str)
print(json.dumps(dict(inst=cnt['instances'], complete=cnt['complete'], runs=cnt['runs'], inc=cnt['inc'],
                      rand_bad=cnt['rand_bad'], nfail=len(fails), secs=res['secs'])))
