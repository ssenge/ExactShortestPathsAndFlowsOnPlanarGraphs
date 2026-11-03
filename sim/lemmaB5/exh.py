"""Exhaustive: all connected planar graphs on n vertices (graph atlas), all planar rotation
systems, all spanning trees, all roots, all start corners.
usage: python3 -I exh.py n part nparts deep_every"""
import sys, os, time
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import networkx as nx
from gen import embeddings, spanning_trees, parents
import harness as H
from mine import Fail

n, part, nparts, deep_every = map(int, sys.argv[1:5])
gs = [g for g in nx.graph_atlas_g() if g.number_of_nodes() == n and nx.is_connected(g) and nx.check_planarity(g)[0]]
t0 = time.time(); fails = 0; cnt = 0
for gi, g in enumerate(gs):
    if gi % nparts != part:
        continue
    V = sorted(g.nodes()); E = sorted(tuple(sorted(e)) for e in g.edges())
    STs = list(spanning_trees(V, E))
    for rot in embeddings(V, E):
        for S in STs:
            for r in V:
                par = parents(V, S, r)
                for k in range(len(rot[r])):
                    cnt += 1
                    try:
                        H.check(V, rot, par, r, k, deep=(cnt % deep_every == 0))
                    except (Fail, Exception) as ex:
                        fails += 1
                        if fails <= 30:
                            print('FAIL', repr(ex), 'E=', E, 'rot=', rot, 'par=', par, 'r=', r, 'k=', k, flush=True)
                        H.TOT['FAIL'] += 1
print('n', n, 'part', part, 'graphs', len(gs), 'time', round(time.time() - t0, 1))
H.report()
