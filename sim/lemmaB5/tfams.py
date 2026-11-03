import sys, os, random
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fams import FAMS
from mine import is_planar_rot, mkidx
import networkx as nx
for name, f in [(k_, FAMS[k_]) for k_ in sys.argv[1:]] or FAMS.items():
    for s in range(30):
        rng = random.Random(s)
        n = rng.randint(4, 40)
        V, rot = f(n, rng)
        assert is_planar_rot(rot, mkidx(rot)), (name, s)
        G = nx.Graph([(a, b) for a in rot for b in rot[a]]); G.add_nodes_from(V)
        assert nx.is_connected(G), name
        for v in V: assert len(set(rot[v])) == len(rot[v]) and v not in rot[v], name
    print(name, 'ok', len(V), G.number_of_edges())
