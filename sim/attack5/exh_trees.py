"""all plane trees on n vertices (nonisomorphic trees x all rotation systems, capped and sampled),
all roots, all start corners. usage: exh_trees.py n cap deep_every"""
import sys, os, time, itertools, random
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import networkx as nx
from gen import cyc_orders, parents
import harness as H
from mine import Fail
n, cap, deep_every = map(int, sys.argv[1:4])
rng = random.Random(n)
t0 = time.time(); cnt = 0; fails = 0; ntrees = 0; nemb = 0
for T in nx.nonisomorphic_trees(n):
    ntrees += 1
    V = sorted(T.nodes()); S = list(T.edges())
    per = [list(cyc_orders(sorted(T[v]))) for v in V]
    tot = 1
    for p in per: tot *= len(p)
    if tot <= cap:
        rots = itertools.product(*per)
    else:
        rots = (tuple(rng.choice(p) for p in per) for _ in range(cap))
    for combo in rots:
        nemb += 1
        rot = {v: combo[i] for i, v in enumerate(V)}
        for r in V:
            par = parents(V, S, r)
            for k in range(len(rot[r])):
                cnt += 1
                try:
                    H.check(V, rot, par, r, k, deep=(cnt % deep_every == 0))
                except Exception as ex:
                    fails += 1; H.TOT['FAIL'] += 1
                    if fails <= 10: print('FAIL', repr(ex), rot, par, r, k, flush=True)
print('trees n', n, 'trees', ntrees, 'embeddings', nemb, 'instances', cnt, 'time', round(time.time() - t0, 1))
H.report()
