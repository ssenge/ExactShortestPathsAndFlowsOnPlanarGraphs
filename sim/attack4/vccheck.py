"""How many virtual_candidates (geo.py) properly cross a G-edge under an eps-free orientation test?"""
import sys, os, random, collections
REPO = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')
sys.path.insert(0, os.path.join(REPO, 'attack3'))
import numpy as np
from sweep import params
from geo import FAMS, virtual_candidates
from core import seg_cross
C = collections.Counter(); ex = {}
fams = ['dl', 'grid', 'k2m', 'fan', 'nested', 'pend', 'flower']
for s in range(int(sys.argv[1]), int(sys.argv[2])):
    r = random.Random(s * 31 + 7); fam = fams[s % 7]; args = params(fam, r)
    pos, E = FAMS[fam](s, args); pos = np.asarray(pos, float)
    vc = virtual_candidates(pos, E)
    A = pos[[a for a, b in E]]; B = pos[[b for a, b in E]]
    bad = [(a, b) for a, b in vc if seg_cross(pos[a], pos[b], A, B, eps=0.0)]
    C[(fam, 'inst')] += 1; C[(fam, 'vc')] += len(vc); C[(fam, 'bad')] += len(bad); C[(fam, 'inst_with_bad')] += bool(bad)
    if bad and fam not in ex:
        ex[fam] = (s, args, bad[:3])
for k in sorted(C): print(k, C[k])
print(ex)
