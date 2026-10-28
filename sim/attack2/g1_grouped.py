"""Re-run g1_inconsistency.py with [8]'s grouping: at the root no separator vertex is split,
so all outside components form ONE child (S n N(outside)) u outside. Report min largest child with 7(a)."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import networkx as nx, bdd
from g1_inconsistency import star, windmill, k2m, simple_paths

def best(P):
    X = frozenset(P.rot); PX = P.induced(X); faces, df = PX.faces()
    fv = [set(v for v, _ in f) for f in faces]
    G = nx.Graph([P.edges[e] for e in P.edges]); eid = {frozenset(P.edges[e]): e for e in P.edges}
    b = None
    for q in simple_paths(G):
        y, z = q[0], q[-1]; cl = []
        if len(q) >= 3 and G.has_edge(y, z): cl.append(('real', eid[frozenset((y, z))]))
        for fi in range(len(faces)):
            if y in fv[fi] and z in fv[fi]:
                cl += [('virtual', a, c) for a in PX.corners_on_face(df, y, fi) for c in PX.corners_on_face(df, z, fi)]
        S = set(q)
        for c in cl:
            res = bdd.analyse(PX, X, q, c)
            if res is None: continue
            comps, cside, _ = res
            for ins in 'LR':
                outs = [x for i, x in enumerate(comps) if cside[i] != ins]
                if not outs: continue
                inn = set(S).union(*[x for i, x in enumerate(comps) if cside[i] == ins])
                o = set().union(*outs); out = o | {s for s in S if any(G.has_edge(s, x) for x in o)}
                kids = [inn, out]
                assert max(sum(s in k for k in kids) for s in S) <= 3
                big = max(map(len, kids)); b = big if b is None else min(b, big)
    return b

for name, mk, ms in (('star', star, (8, 16, 32)), ('windmill', windmill, (4, 8, 12)), ('K2m', k2m, (6, 10, 16))):
    for m in ms:
        P = mk(m); n = len(P.rot); print(name, 'm=%d n=%d  min largest child, grouped, 7(a) holds: %d' % (m, n, best(P)), flush=True)
