import sys, os, time
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import networkx as nx
from gen import *
t=time.time()
for n in range(4,8):
    gs=[g for g in nx.graph_atlas_g() if g.number_of_nodes()==n and nx.is_connected(g) and nx.check_planarity(g)[0]]
    ne=0; tot=0; maxemb=0
    for g in gs:
        V=sorted(g.nodes()); E=sorted(tuple(sorted(e)) for e in g.edges())
        k=sum(1 for _ in embeddings(V,E)); ne+=k; maxemb=max(maxemb,k)
        st=sum(1 for _ in spanning_trees(V,E))
        tot+=k*st*2*len(E)
    print(n,len(gs),'emb',ne,'maxemb',maxemb,'instances',tot, round(time.time()-t,1),flush=True)
