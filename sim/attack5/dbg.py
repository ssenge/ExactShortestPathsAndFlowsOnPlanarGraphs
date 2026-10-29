import sys, os, random
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fams import FAMS
from gen import random_spanning_tree
fams=list(FAMS)
for s in range(0,4000):
    fam = fams[s % len(fams)]
    rng = random.Random(1000003 * s + 17)
    n = rng.randint(10, 40)
    V, rot = FAMS[fam](n, rng)
    mode = rng.choice(['bfs', 'bfs', 'dfs', 'rand'])
    r0, par0 = random_spanning_tree(V, rot, rng, mode)
    if len(par0)!=len(V):
        print(s, fam, mode, len(V), len(par0), sorted(set(V)-set(par0))[:5], {v:rot[v] for v in sorted(set(V)-set(par0))[:3]}); break
