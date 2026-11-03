"""(G1') + 7(a) consistency: graphs with k pendant leaves in every corner.
With one child per outside component (G1'), count per non-leaf bag A:
|S_A|, #children, max #outside components at a separator vertex, |L_A|, and |L_A|/|S_A|.
usage: python3 pendant.py k nseeds"""
import sys, os, random, collections
import networkx as nx
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from walk_check import add_pendants, TL, Plane

k = int(sys.argv[1]); ns = int(sys.argv[2])
for seed in range(ns):
    pos, E = TL.random_plane(40, 0.3, seed)
    pos, E = add_pendants(pos, E, k, seed)
    G = nx.Graph(E)
    P = Plane.from_coords(pos, E)
    bags = TL.build_bdd(G, pos, 14, random.Random(seed))
    B = bags[0]; S = B['S']
    kids = B['kids']
    kout = {v: sum(1 for kb in kids[1:] if v in bags[kb]['X']) for v in S}
    # L at the root: label of e after one step
    kid_of = {}
    for kb in kids:
        for x in bags[kb]['X'] - S:
            kid_of[x] = kb
    def lab(e):
        a, c = P.edges[e]
        return kid_of[a] if a not in S else (kid_of[c] if c not in S else kids[0])
    L = 0
    for v in S:
        r = P.rot[v]
        L += sum(1 for j in range(len(r)) if lab(r[j - 1]) != lab(r[j]))
    print('seed %d: n=%d |S_root|=%d children=%d max outside comps at an S vertex=%d |L_root|=%d (=%.1f |S|)'
          % (seed, G.number_of_nodes(), len(S), len(kids), max(kout.values()), L, L / len(S)))
