"""exhaustive generalised fan check (fan_all) on all embeddings/trees/roots/corners, n given."""
import sys, os, time
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import networkx as nx
from gen import embeddings, spanning_trees, parents
from mine import Fail, fan_all, mkidx
n, part, nparts, every = map(int, sys.argv[1:5])
gs = [g for g in nx.graph_atlas_g() if g.number_of_nodes() == n and nx.is_connected(g) and nx.check_planarity(g)[0]]
t0 = time.time(); fails = 0; cnt = 0; steps = 0; inst = 0
for gi, g in enumerate(gs):
    if gi % nparts != part:
        continue
    V = sorted(g.nodes()); E = sorted(tuple(sorted(e)) for e in g.edges())
    STs = list(spanning_trees(V, E))
    for rot in embeddings(V, E):
        idx = mkidx(rot)
        for S in STs:
            for r in V:
                par = parents(V, S, r)
                for k in range(len(rot[r])):
                    cnt += 1
                    if cnt % every:
                        continue
                    try:
                        steps += fan_all(V, rot, idx, par, r, k); inst += 1
                    except Exception as ex:
                        fails += 1
                        if fails <= 20:
                            print('FAIL', repr(ex), E, rot, par, r, k, flush=True)
print('n', n, 'part', part, 'inst', inst, 'steps', steps, 'fails', fails, 'time', round(time.time() - t0, 1))
