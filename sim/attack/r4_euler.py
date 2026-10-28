"""Attack (a): Lemma R4's Euler argument.
Random connected plane graphs (pruned Delaunay); repeatedly cut a random simple path whose
endpoints are split at corners of two faces f1, f2 of the CURRENT graph.
Claim checked: f1 != f2  => #components unchanged, F drops by 1.
Control:       f1 == f2  => #components rises by 1 (so R4 needs the distinct-face premise)."""
import random, sys, collections
import numpy as np
from scipy.spatial import Delaunay
import networkx as nx
sys.path.insert(0, '.')
from rot import Plane

def rand_plane(n, keep, rng):
    pts = rng.random((n, 2))
    tri = Delaunay(pts)
    E = set()
    for s in tri.simplices:
        for i in range(3):
            a, b = sorted((int(s[i]), int(s[(i + 1) % 3])))
            E.add((a, b))
    E = list(E)
    G = nx.Graph(); G.add_nodes_from(range(n)); G.add_edges_from(E)
    T = nx.minimum_spanning_tree(nx.Graph([(a, b, {'weight': rng.random()}) for a, b in E]))
    tree = set(tuple(sorted(e)) for e in T.edges())
    El = [e for e in E if e in tree or rng.random() < keep]
    pos = {i: tuple(pts[i]) for i in range(n)}
    return Plane.from_coords(pos, El)

def simple_path(P, u, w, rng):
    G = nx.Graph()
    for e, (a, b) in P.edges.items():
        G.add_edge(a, b, weight=rng.random())
    try:
        return nx.shortest_path(G, u, w, weight='weight')
    except nx.NetworkXNoPath:
        return None

def trial(rng, same):
    P = rand_plane(rng.integers(12, 40), rng.random() * 0.7, rng)
    stats = []
    for step in range(rng.integers(1, 5)):
        faces, df = P.faces()
        fv = [sorted(set(v for v, _ in f), key=str) for f in faces]
        c0 = P.components()
        for _ in range(50):
            f1 = rng.integers(len(faces))
            f2 = f1 if same else rng.integers(len(faces))
            if (not same) and f2 == f1:
                continue
            u = fv[f1][rng.integers(len(fv[f1]))]
            w = fv[f2][rng.integers(len(fv[f2]))]
            if u == w:
                continue
            path = simple_path(P, u, w, rng)
            if path is None:
                continue
            cu = P.corners_on_face(df, u, f1); cw = P.corners_on_face(df, w, f2)
            if not cu or not cw:
                continue
            Q, _ = P.cut_path(path, cu[rng.integers(len(cu))], cw[rng.integers(len(cw))], tag=step)
            V0, E0, F0 = P.euler(); V1, E1, F1 = Q.euler()
            c1 = Q.components()
            # sanity: genus 0 bookkeeping V-E+F = 2c for rotation faces
            ok_genus = (V1 - E1 + F1 == 2 * c1) and (V0 - E0 + F0 == 2 * c0)
            stats.append((c1 - c0, F1 - F0, len(path) - 1, ok_genus))
            P = Q
            break
    return stats

rng = np.random.default_rng(1)
for same in (False, True):
    agg = collections.Counter(); bad_genus = 0; n = 0
    for t in range(400):
        for dc, dF, k, okg in trial(rng, same):
            agg[(dc, dF)] += 1; n += 1; bad_genus += (not okg)
    print('endpoints on SAME face' if same else 'endpoints on DISTINCT faces',
          '| cuts:', n, '| (dComponents, dFaces) counts:', dict(agg), '| genus bookkeeping failures:', bad_genus)
