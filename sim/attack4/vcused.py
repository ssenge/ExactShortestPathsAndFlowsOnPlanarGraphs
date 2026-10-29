"""Does the ORIGINAL engine_r ever close a separator with a virtual segment that crosses a G-edge?"""
import sys, os, random, collections
REPO = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')
sys.path.insert(0, os.path.join(REPO, 'attack3')); sys.path.insert(0, os.path.join(REPO, 's9'))
import numpy as np
from sweep import CONF, params
from geo import FAMS, virtual_candidates
from core import PG, Fail, seg_cross
import engine_r, rsweep
C = collections.Counter()
for conf in sys.argv[3].split(','):
    for s in range(int(sys.argv[1]), int(sys.argv[2])):
        if s % 7 != 5: continue          # pend only
        r = random.Random(s * 31 + 7); fam = 'pend'; args = params(fam, r)
        pos, E = FAMS[fam](s, args); pos = np.asarray(pos, float)
        vc = virtual_candidates(pos, E)
        A = pos[[a for a, b in E]]; B = pos[[b for a, b in E]]
        bad = {(a, b) for a, b in vc if seg_cross(pos[a], pos[b], A, B, eps=0.0)}
        if not bad: continue
        g = PG(pos, E, seed=s)
        cfg = dict(CONF[conf]); cfg['leaf'] = r.choice([6, 8, 10, 14])
        eng = engine_r.Engine(g, vc, random.Random(s * 7919 + 1), cfg)
        try:
            eng.run()
        except Fail as ex:
            C[(conf, 'FAIL', ex.args[0])] += 1
        C[(conf, 'inst_with_bad_cand')] += 1
        for b_, B_ in eng.bags.items():
            if 'q' in B_ and not B_['real']:
                pr = (min(B_['q'][0], B_['q'][-1]), max(B_['q'][0], B_['q'][-1]))
                C[(conf, 'virtual_closings')] += 1
                if pr in bad:
                    C[(conf, 'BAD_CLOSING_USED')] += 1; print('used', conf, s, args, b_, pr, B_['depth'])
for k in sorted(C, key=str): print(k, C[k])
