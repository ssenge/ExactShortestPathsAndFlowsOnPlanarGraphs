"""Negative controls for my checker: mutated algorithms must be caught.
 noheavy: ignore step 2 (fan in the face of o); anycorner: x may have several corners;
 skip1: skip step 1 (always fan). Also a bug: the chord-step bound W' < n/3 uses that step 1
 found no balanced chord."""
import sys, os, random, collections
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fams import FAMS
from gen import random_spanning_tree, parents
from mine import Fail, mkidx, run

neg = sys.argv[1]; a, b = int(sys.argv[2]), int(sys.argv[3])
fams = list(FAMS)
c = collections.Counter()
for s in range(a, b):
    fam = fams[s % len(fams)]
    rng = random.Random(77 * s + 5)
    n = rng.randint(10, 40)
    V, rot = FAMS[fam](n, rng)
    mode = rng.choice(['bfs', 'dfs', 'rand'])
    r, par = random_spanning_tree(V, rot, rng, mode)
    if len(par) != len(V):
        continue
    k = rng.randrange(len(rot[r]))
    try:
        res = run(V, rot, mkidx(rot), par, r, k, deep=True, neg=neg)
        c['pass'] += 1
    except Fail as ex:
        c['caught'] += 1; c[str(ex).split(':')[0][:40]] += 1
print(neg, dict(c))
