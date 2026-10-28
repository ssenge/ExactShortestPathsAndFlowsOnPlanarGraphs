"""Attack (a)/(G2): a hub path of Def. 6 whose two endpoints already lie on the same face
of G[X] (holes merged through a face of G that was split by VIRTUAL separator edges).
Cutting it (as O_X prescribes) disconnects O_X, so Lemma R4 and (G2) fail.

Grid W x H (x right, y up), straight-line embedding; outer face of G below row 0.
Root separator S1 = q1 + virtual (a,b): q1 = (0,0)->(0,R)->(W-1,R)->(W-1,0); the virtual
edge a=(0,0), b=(W-1,0) runs in the outer face just below row 0.  Interior child Y = rows 0..R.
Y's separator S2 = q2 + virtual (c,d): q2 = (c,0)->(c,R-1)->(d,R-1)->(d,0); virtual (c,d)
runs below row 0 between the bottom row and the virtual edge (a,b).
X = exterior child of S2 inside Y = Y minus strict interior of S2.
BFS tree rooted at m=(mid,R) contains q1, q2 and the edge p=(mid,R)-(mid,R-1).
Def. 6 for X: P_Y = {} ; (P_Y u dS*_Y) n S_Y = q1 n q2 = {}  -> step 3 adds p.  P_X = {p}."""
import sys
sys.path.insert(0, '.')
from rot import Plane
import networkx as nx

def build(W=13, H=8, R=5, c=3, d=9):
    pos = {(x, y): (x, y) for x in range(W) for y in range(H)}
    E = [((x, y), (x + 1, y)) for x in range(W - 1) for y in range(H)] + \
        [((x, y), (x, y + 1)) for x in range(W) for y in range(H - 1)]
    G = Plane.from_coords(pos, E)
    mid = (c + d) // 2
    q1 = [(0, y) for y in range(0, R + 1)] + [(x, R) for x in range(1, W)] + [(W - 1, y) for y in range(R - 1, -1, -1)]
    q2 = [(c, y) for y in range(0, R)] + [(x, R - 1) for x in range(c + 1, d + 1)] + [(d, y) for y in range(R - 2, -1, -1)]
    # BFS tree check: q1, q2 are tree paths of a BFS tree from m (distances strictly monotone away from m)
    m = (mid, R)
    dist = {v: abs(v[0] - m[0]) + abs(v[1] - m[1]) for v in pos}
    def monotone_from_root(path, apex):
        i = path.index(apex)
        return all(dist[path[j]] > dist[path[j + 1]] for j in range(i)) and \
               all(dist[path[j]] < dist[path[j + 1]] for j in range(i, len(path) - 1))
    apex2 = (mid, R - 1)
    assert monotone_from_root(q1, m) and monotone_from_root(q2, apex2)
    Y = [v for v in pos if v[1] <= R]
    inside2 = [(x, y) for x in range(c + 1, d) for y in range(0, R - 1)]
    X = [v for v in Y if v not in inside2]
    return G, Y, X, q1, q2, m, apex2, inside2

G, Y, X, q1, q2, m, apex2, inside2 = build()
V, E, F = G.euler(); print('G: V-E+F =', V - E + F, '(2 = plane)')
GX = G.induced(X)
print('|G|=%d |Y|=%d |X|=%d, strict interior of S2: %d vertices, |S1 n S2| = %d'
      % (len(G.rot), len(Y), len(X), len(inside2), len(set(q1) & set(q2))))
print('G[X] connected:', GX.components() == 1)
faces, df = GX.faces()
fv = [set(v for v, _ in f) for f in faces]
J = (set(q1) | set(q2)) & set(X)
onefaces = [i for i, s in enumerate(fv) if J <= s]
print('faces of G[X] containing ALL of dS*_X before any cut:', onefaces)
fid = onefaces[0]
print('p endpoints', m, apex2, 'both on that face:', m in fv[fid], apex2 in fv[fid])
cm = GX.corners_on_face(df, m, fid); ca = GX.corners_on_face(df, apex2, fid)
for i in cm:
    for j in ca:
        O, cp = GX.cut_path([m, apex2], i, j, tag='p')
        print('cut p at corners', (i, j), '-> components of O_X:', O.components())
# distances in O_X between left and right terminals, with W2 (both directions, weight 1)
O, cp = GX.cut_path([m, apex2], cm[0], ca[0], tag='p')
D = O.digraph(default=1)
a, b = (0, 0), (len(set(x for x, _ in G.rot)) - 1, 0)
print('dist_{G[X]}(a,b) =', nx.shortest_path_length(GX.digraph(default=1), a, b),
      '; dist_{O_X}(a,b) reachable:', nx.has_path(D, a, b))
