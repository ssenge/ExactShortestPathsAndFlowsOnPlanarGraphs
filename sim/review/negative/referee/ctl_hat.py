import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import networkx as nx
from plane import *
cnt = 0; tot = 0
for g in all_connected_planar(2, 6):
    P = Plane(g); nid, ES, ER, EC = P.hat()
    h = nx.Graph(); h.add_nodes_from(range(len(nid)))
    for a,b in ES+ER:
        if a!=b: h.add_edge(a,b)
    for d in P.darts:
        if P.pos[d[0]]<P.pos[d[1]]:
            x = nid[('k',P.prv[d])]; y = nid[('k',P.prv[(d[1],d[0])])]
            if x!=y: h.add_edge(x,y)
            x2 = nid[('k',(d[1],d[0]))]; y2 = nid[('k',d)]
            if x2!=y2: h.add_edge(x2,y2)
    tot += 1
    cnt += not nx.check_planarity(h)[0]
print('control both diagonals of each edge: nonplanar on', cnt, 'of', tot)
print('control K5 planar?', nx.check_planarity(nx.complete_graph(5))[0], 'K33', nx.check_planarity(nx.complete_bipartite_graph(3,3))[0])
