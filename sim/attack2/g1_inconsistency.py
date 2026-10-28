"""Is the black box (G1') + 7(a) satisfiable together with Property 1 (height O(log n))?
For small graphs with D = 2 (star K_{1,m}, windmill/friendship graph F_m, 2-connected K_{2,m}) enumerate EVERY
(G1')-shaped separator of the root bag: q = any simple path with >= 1 edge (per-bag trees can contain any simple
path), closing edge real (endpoints adjacent, |E(q)| >= 2) or virtual at every pair of corners on every common face
of G[X], both choices of inside. Children minimal (X_C = C u (S n N(C)); extras only add memberships).
Prints the smallest possible largest child, with and without 7(a). If it is |X| - O(1) with 7(a), every
(G1')+7(a) BDD has height Omega(n), against Property 1 (O(log n)) and Property 5 (leaves O(D log n)).
Note: "minimal children" means one child per outside component, the reading used before the referee's fix.
LEMMA15.md (G1') groups outside components as in [8]; g1_grouped.py repeats the search with that grouping.
usage: python3 g1_inconsistency.py"""
import sys, os, math, itertools
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import networkx as nx
import gens, bdd
from rot import Plane


def star(m):
    pos = {'h': (0.0, 0.0)}
    pos.update({i: (math.cos(2 * math.pi * i / m), math.sin(2 * math.pi * i / m)) for i in range(m)})
    return Plane.from_coords(pos, [('h', i) for i in range(m)])


def windmill(m):
    pos = {'h': (0.0, 0.0)}; E = []
    for i in range(m):
        a, b = 2 * math.pi * (i + 0.15) / m, 2 * math.pi * (i + 0.85) / m
        pos['a%d' % i] = (math.cos(a), math.sin(a)); pos['b%d' % i] = (math.cos(b), math.sin(b))
        E += [('h', 'a%d' % i), ('h', 'b%d' % i), ('a%d' % i, 'b%d' % i)]
    return Plane.from_coords(pos, E)


def k2m(m):
    pos = {'h1': (0.0, 1.0), 'h2': (0.0, -1.0)}
    pos.update({i: (i - (m - 1) / 2.0, 0.0) for i in range(m)})
    return Plane.from_coords(pos, [('h1', i) for i in range(m)] + [('h2', i) for i in range(m)])


def simple_paths(G, maxlen=6):
    for s in G.nodes():
        stack = [[s]]
        while stack:
            p = stack.pop()
            if len(p) >= 2:
                yield p
            if len(p) > maxlen:
                continue
            for y in G.neighbors(p[-1]):
                if y not in p:
                    stack.append(p + [y])


def best_split(P):
    X = frozenset(P.rot)
    PX = P.induced(X); faces, df = PX.faces()
    fv = [set(v for v, _ in f) for f in faces]
    G = nx.Graph([P.edges[e] for e in P.edges])
    eid = {frozenset(P.edges[e]): e for e in P.edges}
    best7a = best_any = None; nsep = 0
    for q in simple_paths(G):
        y, z = q[0], q[-1]
        if q.index(y) > q.index(z) and len(q) > 2:
            pass
        closings = []
        if len(q) >= 3 and G.has_edge(y, z):
            closings.append(('real', eid[frozenset((y, z))]))
        for fi in range(len(faces)):
            if y in fv[fi] and z in fv[fi]:
                for jy in PX.corners_on_face(df, y, fi):
                    for jz in PX.corners_on_face(df, z, fi):
                        closings.append(('virtual', jy, jz))
        S = set(q)
        for cl in closings:
            res = bdd.analyse(PX, X, q, cl)
            if res is None:
                continue
            comps, cside, _ = res
            for ins in 'LR':
                outs = [c for i, c in enumerate(comps) if cside[i] != ins]
                if not outs:
                    continue
                nsep += 1
                inn = set(S)
                for i, c in enumerate(comps):
                    if cside[i] == ins:
                        inn |= c
                kids = [inn] + [set(c) | {s for s in S if any(G.has_edge(s, x) for x in c)} for c in outs]
                big = max(len(k) for k in kids)
                mem = max(sum(1 for k in kids if s in k) for s in S)
                if mem <= 3:
                    best7a = big if best7a is None else min(best7a, big)
                best_any = big if best_any is None else min(best_any, big)
    return nsep, best7a, best_any


def main():
    for name, mk, ms in (('star K_{1,m}', star, (8, 16, 32)), ('windmill F_m', windmill, (4, 8, 12)),
                         ('K_{2,m}', k2m, (6, 10, 16))):
        for m in ms:
            P = mk(m)
            n = len(P.rot)
            G = nx.Graph([P.edges[e] for e in P.edges])
            nsep, b7, ba = best_split(P)
            print('%-13s m=%2d n=%2d D=%d  separators=%5d  min largest child: with 7(a) %3s (= n-%d),  without 7(a) %3s' % (
                name, m, n, nx.diameter(G), nsep, b7, n - b7, ba), flush=True)


if __name__ == '__main__':
    main()
