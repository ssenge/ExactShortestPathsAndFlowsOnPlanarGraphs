"""Referee checks for LEMMA15.md section 3 (independent of tiles.py's own asserts).

Re-implements the level loop *as written in the document* (P_X = shortest path in T[X], used only if
d>=1, all q-edges labelled X and V(q) misses V(Gamma_d)), then checks at every level:
  W  section 3.5 walk: from collected port records only (opening/closing Gamma-corner, rank, face id),
     rebuild the cyclic port order of every tile of every bag and compare with the true boundary walk;
  I  Claim 7 injection: the opening corner of every port of X was added by a proper ancestor of X;
  C  Claim 3 step 3: every edge of p_X is labelled X; Gamma_{d+1} connected; tiles single-labelled;
  T  section 3.5 'child tiles to tiles of X' = classes of adjacency across N_X \\ Gamma_d;
  L  per separator vertex: (#outside components adjacent, #label-change corners).
usage: python3 walk_check.py nseeds [virtual] [pendants]
"""
import sys, os, random, collections, itertools, math
import numpy as np, networkx as nx
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'tiles'))
sys.path.insert(0, os.path.join(HERE, '..', 'attack'))
import tiles as TL
from rot import Plane


def add_pendants(pos, E, k, seed):
    """k pendant leaves in every corner of every vertex (straight-line, tiny, along the bisector)."""
    P = Plane.from_coords(pos, E)
    pos = dict(pos); E = list(E); nxt = max(pos) + 1
    for v, r in P.rot.items():
        x, y = pos[v]
        angs = []
        for e in r:
            u = P.other(e, v); ux, uy = pos[u]
            angs.append(math.atan2(uy - y, ux - x))
        n = len(angs)
        for j in range(n):
            a0 = angs[j - 1]; a1 = angs[j]
            span = (a1 - a0) % (2 * math.pi)
            if n == 1:
                span = 2 * math.pi
            for t in range(k):
                a = a0 + span * (t + 1) / (k + 1)
                pos[nxt] = (x + 1e-3 * math.cos(a), y + 1e-3 * math.sin(a))
                E.append((v, nxt)); nxt += 1
    return pos, E


def run(seed, virtual=False, pendants=0, n=160, drop=0.3, leaf=14):
    rng = random.Random(seed)
    pos, E = TL.random_plane(n, drop, seed)
    Gfull = None
    if virtual:
        _, Ef = TL.random_plane(n, 0.0, seed); Gfull = nx.Graph(Ef)
    if pendants:
        pos, E = add_pendants(pos, E, pendants, seed)
        if Gfull is not None:
            Gfull.add_edges_from(e for e in E)
    Gnx = nx.Graph(E)
    P = Plane.from_coords(pos, E)
    assert P.euler()[0] - P.euler()[1] + P.euler()[2] == 2
    R, cid, corner_of = TL.radial(P)
    tl = TL.Tiler(P, R, cid, corner_of)
    _, dart_face = P.faces()
    root = min(P.rot)
    rank = TL.euler_ranks(P, nx.bfs_tree(Gnx, root).to_undirected(), root)
    face = {(v, j): dart_face[(v, r[(j - 1) % len(r)])] for v, r in P.rot.items() for j in range(len(r))}
    bags = TL.build_bdd(Gnx, pos, leaf, rng, Gfull)
    st = collections.Counter(); hist = collections.Counter()
    maxdepth = max(b['depth'] for b in bags.values())
    def anc(b):
        out = []; p = bags[b]['parent']
        while p is not None:
            out.append(p); p = bags[p]['parent']
        return out
    label = {e: 0 for e in P.edges}
    gamma = set(); adder = {}            # corner R-edge id -> bag that added it
    Nsize = collections.Counter()
    for d in range(maxdepth + 1):
        level = [b for b, B in bags.items() if B['depth'] == d and 'kids' in B]
        if not level:
            break
        gverts = set(corner_of[c][0] for c in gamma)
        newlabel = dict(label); newc = {}
        for b in level:
            B = bags[b]; X, S, q = B['X'], B['S'], B['q']
            kid_of = {}
            for kb in B['kids']:
                for x in bags[kb]['X'] - S:
                    kid_of[x] = kb
            inkid = B['kids'][0]
            for e, (a, c) in P.edges.items():
                if label[e] != b:
                    continue
                newlabel[e] = kid_of[a] if a not in S else (kid_of[c] if c not in S else inkid)
            N = set()
            for v in S:
                r = P.rot[v]
                k = sum(1 for kb in B['kids'][1:] if v in bags[kb]['X'])
                ch = 0
                for j in range(len(r)):
                    e1, e2 = r[j - 1], r[j]
                    if label[e1] == b and label[e2] == b and newlabel[e1] != newlabel[e2]:
                        N.add(cid[(v, j)]); ch += 1
                hist[(k, ch)] += 1
                if k <= 2:
                    assert ch <= 4, ('more than 4 label changes with <=2 outside comps', ch)
            def rails(path):
                for u, v in zip(path, path[1:]):
                    e = tl.eid_of[frozenset((u, v))]
                    if label[e] != b:
                        continue
                    ju = P.rot[u].index(e); jv = P.rot[v].index(e)
                    N.add(cid[(u, (ju + 1) % len(P.rot[u]))]); N.add(cid[(v, jv)])
            rails(q)
            qedges = [tl.eid_of[frozenset((u, v))] for u, v in zip(q, q[1:])]
            if d >= 1 and all(label[e] == b for e in qedges) and not (set(q) & gverts):
                T = B['T']                           # T[X] (BFS tree of G[X], as in the prototype)
                targets = [x for x in X if x in gverts]
                assert targets
                dist, paths = nx.multi_source_dijkstra(T, set(q))
                t = min(targets, key=lambda x: dist[x])
                p = paths[t]
                for u, v in zip(p, p[1:]):
                    assert label[tl.eid_of[frozenset((u, v))]] == b, 'Claim 3: p_X edge not labelled X'
                rails(p); st['P_used'] += 1
            Nsize[b] = len(N)
            for c in N:
                if c not in gamma:
                    assert c not in newc, '(2b) violated: corner added by two bags'
                    newc[c] = b
                    v, j = corner_of[c]; r = P.rot[v]
                    assert label[r[j - 1]] == b and label[r[j]] == b, '(2b) violated'
        old_gamma, old_label = set(gamma), label
        gamma |= set(newc); adder.update(newc); label = newlabel
        # C: connectivity, single labels
        gg = nx.Graph([R.edges[c] for c in gamma])
        assert nx.is_connected(gg), 'Gamma disconnected'
        T_ = tl.tiles(gamma)
        for t in T_:
            assert len({label[e] for e in t}) == 1
        tile_id = {e: i for i, t in enumerate(T_) for e in t}
        # true boundary orders; occurrences are (v, opening corner index)
        orders = tl.boundary_orders(gamma)
        true_seq = {}
        for occ in orders:
            v, j = occ[0]
            true_seq[tile_id[P.rot[v][j]]] = [(v, jj) for (v, jj) in occ]
        # W: section 3.5 walk from records only
        def sector_corners(v, j_open):
            r = P.rot[v]; n = len(r)
            for t in range(1, n + 1):
                if cid[(v, (j_open + t) % n)] in gamma:
                    return (v, (j_open + t) % n)
        ports_by_bag = collections.defaultdict(list)
        for ti, seq in true_seq.items():
            Y = label[next(iter(T_[ti]))]
            ports_by_bag[Y].extend(seq)
        for Y, ports in ports_by_bag.items():
            rec = {}                                           # port -> (opening, closing)
            for (v, jo) in ports:
                rec[(v, jo)] = ((v, jo), sector_corners(v, jo))
            opened_by = {o: p_ for p_, (o, c) in rec.items()}
            byface = collections.defaultdict(set)
            for o, c in rec.values():
                byface[face[o]].add(o); byface[face[c]].add(c)
            byface = {f: sorted(cs, key=lambda c: rank[c]) for f, cs in byface.items()}
            res = {}
            for direction in (+1, -1):
                ok = True
                for ti in {tile_id[P.rot[v][j]] for (v, j) in ports}:
                    seq = true_seq[ti]
                    start = seq[0]; walk = [start]; cur = start
                    for _ in range(len(ports) + 1):
                        cc = rec[cur][1]; lst = byface[face[cc]]
                        nxt_c = lst[(lst.index(cc) + direction) % len(lst)]
                        if nxt_c not in opened_by:
                            ok = False; break
                        cur = opened_by[nxt_c]
                        if cur == start:
                            break
                        walk.append(cur)
                    if not ok:
                        break
                    # compare cyclic sequences, either orientation
                    k = len(seq)
                    if len(walk) != k:
                        ok = False; break
                    if not any(walk == seq[i:] + seq[:i] for i in range(k)) and \
                       not any(walk == (seq[::-1][i:] + seq[::-1][:i]) for i in range(k)):
                        ok = False; break
                res[direction] = ok
            assert res[+1] or res[-1], ('walk failed for bag', Y, res)
            st['walk_dir_%+d' % (+1 if res[+1] else -1)] += 1
            st['walk_bags'] += 1
        # I: injection into ancestors
        for (v, jo) in [p_ for ps in ports_by_bag.values() for p_ in ps]:
            Y = label[P.rot[v][jo]]
            A = adder[cid[(v, jo)]]
            assert A in anc(Y), ('opening corner not from an ancestor', A, Y)
            st['ports_checked'] += 1
        for Y, ps in ports_by_bag.items():
            bound = sum(Nsize[A] for A in anc(Y))
            assert len(ps) <= bound
            st['max_ports_over_bound_x100'] = max(st['max_ports_over_bound_x100'], int(100 * len(ps) / max(1, bound)))
        # T: child tiles to tiles of X
        if d >= 1:
            pT = tl.tiles(old_gamma); ptile = {e: i for i, t in enumerate(pT) for e in t}
            uf = list(range(len(T_)))
            def find(x):
                while uf[x] != x:
                    uf[x] = uf[uf[x]]; x = uf[x]
                return x
            for c in newc:
                v, j = corner_of[c]; r = P.rot[v]
                a, b2 = find(tile_id[r[j - 1]]), find(tile_id[r[j]])
                uf[a] = b2
            for b in level:
                kids = [i for i, t in enumerate(T_) if old_label[next(iter(t))] == b]
                cls = collections.defaultdict(set)
                for i in kids:
                    cls[find(i)].add(ptile[next(iter(T_[i]))])
                assert all(len(s) == 1 for s in cls.values()), 'class spans two parent tiles'
                assert len(cls) == len({ptile[next(iter(T_[i]))] for i in kids}), 'parent tile split into classes'
                st['T_checks'] += 1
        st['levels'] += 1
    # L-statistics at the root only (pendant demo)
    return st, hist, bags


if __name__ == '__main__':
    ns = int(sys.argv[1]) if len(sys.argv) > 1 else 2
    virtual = 'virtual' in sys.argv; pend = 2 if 'pendants' in sys.argv else 0
    tot = collections.Counter(); H = collections.Counter()
    for s in range(ns):
        st, hist, bags = run(s, virtual=virtual, pendants=pend, n=(60 if pend else 160))
        tot.update(st); H.update(hist)
        print(s, dict(st), flush=True)
    print('TOTAL', dict(tot))
    print('(outside comps k, label changes) histogram:', sorted(H.items()))
