"""Prototype of the tile construction for Lemma 14' (LEMMA15.md).

Gamma = set of corners (v, j) of G (radial-graph edges). Tiles at depth d = faces of Gamma_d.
Per non-leaf bag X: label edges of X's tiles by child; add (L) label-change corners at S_X,
(Q) radial path along in-tile edges of the separator tree path q, (P) radial path along a
connecting path if q misses Gamma_d. Checks: Gamma connected, tiles single-labelled, corners
between different labels already in Gamma, glue(sub-tiles) == tile, Monge (M) on every
sub-tile component in boundary order, planarity of the wheel model of every gluing, port counts.
"""
import sys, os, itertools, collections, random
import numpy as np, networkx as nx
from scipy.spatial import Delaunay
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', 'attack'))
from rot import Plane

# ---------------- input graphs ----------------
def random_plane(n, drop, seed):
    rng = np.random.default_rng(seed)
    pts = rng.random((n, 2))
    tri = Delaunay(pts)
    E = set()
    for s in tri.simplices:
        for a, b in itertools.combinations(sorted(s), 2):
            E.add((int(a), int(b)))
    E = sorted(E)
    G = nx.Graph(E)
    for e in rng.permutation(len(E)):
        a, b = E[e]
        if rng.random() < drop:
            G.remove_edge(a, b)
            if not nx.is_connected(G):
                G.add_edge(a, b)
    pos = {i: tuple(pts[i]) for i in range(n)}
    return pos, sorted(G.edges())

# ---------------- radial graph ----------------
def radial(P):
    faces, dart_face = P.faces()
    cid = {}
    R = Plane()
    for v, r in P.rot.items():
        for j in range(len(r)):
            e = R.new_eid(); cid[(v, j)] = e
            f = dart_face[(v, r[(j - 1) % len(r)])]
            R.edges[e] = (('v', v), ('f', f))
    for v, r in P.rot.items():
        R.rot[('v', v)] = [cid[(v, j)] for j in range(len(r))]
    for fid, cyc in enumerate(faces):
        lst = []
        for (x, ex) in cyc:
            i = P.rot[x].index(ex)
            lst.append(cid[(x, (i + 1) % len(P.rot[x]))])
        R.rot[('f', fid)] = lst
    V, E, F = R.euler()
    if V - E + F != 2:                       # wrong orientation at face vertices
        for fid in range(len(faces)):
            R.rot[('f', fid)] = R.rot[('f', fid)][::-1]
        V, E, F = R.euler()
    assert V - E + F == 2, 'radial graph not planar'
    corner_of = {e: c for c, e in cid.items()}
    return R, cid, corner_of

def sub_plane(R, keep):
    S = Plane(); S._next = R._next
    for e in keep:
        S.edges[e] = R.edges[e]
    vs = set(x for e in keep for x in R.edges[e])
    for x in vs:
        S.rot[x] = [e for e in R.rot[x] if e in keep]
    return S

# ---------------- BDD (Li-Parter-shaped children) ----------------
def inside_poly(pt, poly):
    x, y = pt; c = False
    for i in range(len(poly)):
        x1, y1 = poly[i]; x2, y2 = poly[(i + 1) % len(poly)]
        if (y1 > y) != (y2 > y) and x < (x2 - x1) * (y - y1) / (y2 - y1) + x1:
            c = not c
    return c

def separator(GX, pos, X, rng, Gfull=None):
    root = min(X)
    T = nx.bfs_tree(GX, root).to_undirected()
    best = None
    src = Gfull.subgraph(X) if Gfull is not None else GX
    nontree = [e for e in src.edges() if not T.has_edge(*e)]
    rng.shuffle(nontree)
    for (y, z) in nontree[:60]:
        q = nx.shortest_path(T, y, z)
        if len(q) < 3:
            continue
        poly = [pos[v] for v in q]
        Sset = set(q)
        ins = {v for v in X if v not in Sset and inside_poly(pos[v], poly)}
        rest = GX.subgraph([v for v in X if v not in Sset and v not in ins])
        comps = list(nx.connected_components(rest))
        big = max([len(ins)] + [len(c) for c in comps])
        if best is None or big < best[0]:
            best = (big, q, ins, comps, T)
    return best

def build_bdd(Gnx, pos, leaf_size, rng, Gfull=None):
    bags = {0: dict(X=set(Gnx.nodes()), parent=None, depth=0)}
    order = [0]; k = 0
    while k < len(order):
        b = order[k]; k += 1
        X = bags[b]['X']
        if len(X) <= leaf_size:
            continue
        GX = Gnx.subgraph(X)
        res = separator(GX, pos, X, rng, Gfull)
        if res is None:
            continue
        big, q, ins, comps, T = res
        if big >= len(X) - 1:
            continue
        S = set(q)
        if len(ins | S) >= len(X) or any(len(set(c) | S) >= len(X) for c in comps):
            continue
        kids = [('in', ins | S)] + [('out', set(c) | {s for s in S if any(Gnx.has_edge(s, x) for x in c)})
                                     for c in comps]
        bags[b].update(S=S, q=q, T=T, kids=[])
        for kind, Y in kids:
            nb = len(bags)
            bags[nb] = dict(X=Y, parent=b, depth=bags[b]['depth'] + 1, kind=kind)
            bags[b]['kids'].append(nb)
            order.append(nb)
    return bags

# ---------------- tiles ----------------
class Tiler:
    def __init__(self, P, R, cid, corner_of):
        self.P, self.R, self.cid, self.corner_of = P, R, cid, corner_of
        self.eid_of = {}
        for e, (a, b) in P.edges.items():
            self.eid_of[frozenset((a, b))] = e

    def tiles(self, gamma):
        P = self.P
        uf = {e: e for e in P.edges}
        def find(x):
            while uf[x] != x:
                uf[x] = uf[uf[x]]; x = uf[x]
            return x
        for v, r in P.rot.items():
            for j in range(len(r)):
                if self.cid[(v, j)] not in gamma:
                    a, b = find(r[j - 1]), find(r[j])
                    if a != b:
                        uf[a] = b
        comp = collections.defaultdict(set)
        for e in P.edges:
            comp[find(e)].add(e)
        return list(comp.values())

    def sector(self, gamma, v, i):
        """index of the Gamma-corner opening the sector of v that contains edge rot[v][i]; None if v not in Gamma."""
        r = self.P.rot[v]; n = len(r)
        for t in range(n):
            j = (i - t) % n
            if self.cid[(v, j)] in gamma:
                return j
        return None

    def boundary_orders(self, gamma):
        """For each Gamma-face: list of port occurrences (v, sector) in walk order, plus the edge set side."""
        Gm = sub_plane(self.R, gamma)
        faces, _ = Gm.faces()
        out = []
        for cyc in faces:
            occ = []
            for (x, ex) in cyc:
                if x[0] != 'v':
                    continue
                v = x[1]
                r = Gm.rot[x]
                # leaving via ex; the walk entered via the corner following ex (ccw) in Gamma's rotation
                j_out = self.corner_of[ex][1]
                occ.append((v, j_out))
            out.append(occ)
        return out

def euler_ranks(P, tree, root):
    """Contour ranks of all corners of G around the spanning tree `tree` (same turning rule as P.faces)."""
    rank = {}
    y, j = root, 0
    while (y, j) not in rank:
        rank[(y, j)] = len(rank)
        r = P.rot[y]; e = r[(j - 1) % len(r)]
        a, b = P.edges[e]
        if tree.has_edge(a, b):
            z = b if a == y else a
            y, j = z, P.rot[z].index(e)
        else:
            j = (j - 1) % len(r)
    assert len(rank) == sum(len(r) for r in P.rot.values()), 'contour missed corners'
    return rank

def check_face_ranks(P, R, cid, stats):
    root = min(P.rot)
    G_ = nx.Graph([P.edges[e] for e in P.edges])
    rank = euler_ranks(P, nx.bfs_tree(G_, root).to_undirected(), root)
    corner_of = {e: c for c, e in cid.items()}
    dirs = set()
    for x, lst in R.rot.items():
        if x[0] != 'f' or len(lst) < 3:
            continue
        rk = [rank[corner_of[e]] for e in lst]
        desc = sum(rk[(i + 1) % len(rk)] < rk[i] for i in range(len(rk)))
        asc = len(rk) - desc
        assert desc == 1 or asc == 1, 'face corners not in contour order'
        dirs.add('inc' if desc == 1 else 'dec')
        stats['face_rank_checks'] += 1
    assert len(dirs) <= 1, 'contour orientation differs between faces'

def run(n=140, drop=0.25, seed=1, leaf_size=14, verbose=False, virtual=False, neg=False):
    rng = random.Random(seed)
    pos, E = random_plane(n, drop, seed)
    Gnx = nx.Graph(E)
    Gfull = None
    if virtual:
        posf, Ef = random_plane(n, 0.0, seed)
        Gfull = nx.Graph(Ef)
        assert posf == pos
    P = Plane.from_coords(pos, E)
    nrng = np.random.default_rng(seed)
    for e in P.edges:
        P.w[(e, 0)] = int(nrng.integers(1, 20)); P.w[(e, 1)] = int(nrng.integers(1, 20))
    R, cid, corner_of = radial(P)
    tl = Tiler(P, R, cid, corner_of)
    check_face_ranks(P, R, cid, stats := collections.Counter())
    bags = build_bdd(Gnx, pos, leaf_size, rng, Gfull)
    stats['virtual_closings'] = sum(1 for B in bags.values() if 'q' in B and not Gnx.has_edge(B['q'][0], B['q'][-1]))
    maxdepth = max(b['depth'] for b in bags.values())
    def dSstar(b):
        X = bags[b]['X']; out = set(); p = bags[b]['parent']
        while p is not None:
            out |= bags[p]['S'] & X; p = bags[p]['parent']
        return out
    label = {e: 0 for e in P.edges}           # edge -> bag owning its tile at the current depth
    gamma = set()
    worst_ports = 0
    for d in range(maxdepth + 1):
        level = [b for b, B in bags.items() if B['depth'] == d and 'kids' in B]
        if not level:
            break
        gvert = {cid_v for cid_v in ()}
        gverts = set(corner_of[c][0] for c in gamma)
        new = set()
        newlabel = dict(label)
        for b in level:
            B = bags[b]; X, S, q = B['X'], B['S'], B['q']
            kid_of = {}
            for kb in B['kids']:
                for x in bags[kb]['X'] - S:
                    assert x not in kid_of
                    kid_of[x] = kb
            inkid = B['kids'][0]
            for e, (a, c) in P.edges.items():
                if label[e] != b:
                    continue
                assert a in X and c in X, 'tile content outside bag'
                if a not in S:
                    newlabel[e] = kid_of[a]
                elif c not in S:
                    newlabel[e] = kid_of[c]
                else:
                    newlabel[e] = inkid
                assert a in bags[newlabel[e]]['X'] and c in bags[newlabel[e]]['X'], '(7c) fails'
            # (L) label-change corners at S
            for v in S:
                r = P.rot[v]
                k = sum(1 for kb in B['kids'][1:] if v in bags[kb]['X'])
                ch = sum(1 for j in range(len(r)) if label[r[j - 1]] == b and label[r[j]] == b
                         and newlabel[r[j - 1]] != newlabel[r[j]])
                assert ch <= 2 * k, ('label changes', ch, k)
                stats['max_out_kids_at_S'] = max(stats['max_out_kids_at_S'], k)
                stats['L_vertex_checks'] += 1
                for j in range(len(r)):
                    e1, e2 = r[j - 1], r[j]
                    if label[e1] == b and label[e2] == b and newlabel[e1] != newlabel[e2]:
                        new.add(cid[(v, j)])
                    if (label[e1] == b) != (label[e2] == b):
                        assert cid[(v, j)] in gamma or d == 0, 'boundary corner missing from Gamma'
            # (Q) radial path along in-tile q-edges
            def add_edge_path(path):
                for u, v in zip(path, path[1:]):
                    e = tl.eid_of[frozenset((u, v))]
                    if label[e] != b:
                        continue
                    ju = P.rot[u].index(e); jv = P.rot[v].index(e)
                    new.add(cid[(u, (ju + 1) % len(P.rot[u]))]); new.add(cid[(v, jv)])
            add_edge_path(q)
            # (P) connect q to Gamma_d if needed
            if d > 0 and not (set(q) & gverts):
                Xin = [x for x in X]
                H = nx.Graph()
                for e, (a, c) in P.edges.items():
                    if label[e] == b:
                        H.add_edge(a, c)
                targets = [x for x in X if x in gverts]
                assert targets, 'no Gamma vertex in bag'
                dist, paths = nx.multi_source_dijkstra(H, set(q))
                t = min(targets, key=lambda x: dist.get(x, 1e18))
                assert t in dist, 'q not connected to Gamma inside tiles'
                add_edge_path(paths[t])
                stats['P_used'] += 1
        old_gamma = set(gamma); old_label = label
        gamma |= new
        label = newlabel
        # ---- checks at depth d+1 ----
        Gm = sub_plane(R, gamma)
        gg = nx.Graph([R.edges[e] for e in gamma])
        assert nx.is_connected(gg), 'Gamma disconnected'
        V, Ec, F = Gm.euler()
        T_ = tl.tiles(gamma)
        assert F == len(T_), ('face count', F, len(T_))
        for t in T_:
            labs = {label[e] for e in t}
            assert len(labs) == 1, 'tile with two labels'
        stats['levels'] += 1
        # per-tile structures
        orders = tl.boundary_orders(gamma)
        tile_of_occ = {}
        for oi, occ in enumerate(orders):
            for (v, j) in occ:
                e = P.rot[v][j]
                tile_of_occ[(v, j)] = oi
        # map each Gamma-face to its edge set via one occurrence
        face_edges = []
        for occ in orders:
            v, j = occ[0]
            e0 = P.rot[v][j]
            face_edges.append(next(t for t in T_ if e0 in t))
        # ports per bag at depth d+1
        per_bag = collections.Counter()
        for fi, occ in enumerate(orders):
            per_bag[label[next(iter(face_edges[fi]))]] += len(occ)
        for kb, cnt in per_bag.items():
            worst_ports = max(worst_ports, cnt / max(1, len(bags[bags[kb]['parent']]['S']) if bags[kb]['parent'] is not None else 1))
        # Monge on every tile component, boundary order
        for fi, occ in enumerate(orders):
            edges = face_edges[fi]
            def copy(v, e):
                s = tl.sector(gamma, v, P.rot[v].index(e))
                return (v, s)
            D = nx.MultiDiGraph()
            for e in edges:
                a, c = P.edges[e]
                ca, cc = copy(a, e), copy(c, e)
                D.add_edge(ca, cc, weight=P.w[(e, 0)]); D.add_edge(cc, ca, weight=P.w[(e, 1)])
            ports = [(v, j) for (v, j) in occ]
            assert len(set(ports)) == len(ports), 'port occurs twice on a tile boundary'
            for pt in ports:
                assert pt in D, 'port without edges'
            for comp in nx.weakly_connected_components(D):
                cp = [p for p in ports if p in comp]
                if len(cp) < 4:
                    continue
                sub = D.subgraph(comp)
                sp = dict(nx.all_pairs_dijkstra_path_length(sub))
                idx = {p: i for i, p in enumerate(cp)}
                cnt = 0
                for (a, b_, c, dd) in itertools.combinations(cp, 4):
                    for (u, v) in ((a, c), (c, a)):
                        for (w, z) in ((b_, dd), (dd, b_)):
                            cnt += 1
                            if sp[u][z] + sp[w][v] > sp[u][v] + sp[w][z] + 1e-9:
                                raise AssertionError('Monge violated in tile')
                stats['monge_checks'] += cnt
                if neg and len(cp) >= 5:
                    sh = cp[:]; random.Random(len(cp)).shuffle(sh)
                    bad = any(sp[u][z] + sp[w][v] > sp[u][v] + sp[w][z] + 1e-9
                              for (a, b_, c, dd) in itertools.combinations(sh, 4)
                              for (u, v) in ((a, c), (c, a)) for (w, z) in ((b_, dd), (dd, b_)))
                    stats['neg_monge_detected' if bad else 'neg_monge_missed'] += 1
            stats['tiles'] += 1
        # ---- wheel model of the gluing (T4c) ----
        par_orders = tl.boundary_orders(old_gamma) if d > 0 else []
        par_T = tl.tiles(old_gamma) if d > 0 else [set(P.edges)]
        par_of_edge = {}
        for pi, t in enumerate(par_T):
            for e in t:
                par_of_edge[e] = pi
        par_occ = collections.defaultdict(list)          # parent tile -> its port occurrences in order
        for occ in par_orders:
            v, j = occ[0]
            par_occ[par_of_edge[P.rot[v][j]]] = occ
        def tau_copy(v, j):
            s_ = tl.sector(old_gamma, v, j) if d > 0 else None
            return (v, s_)
        sub_by_par = collections.defaultdict(list)
        for fi, occ in enumerate(orders):
            v, j = occ[0]
            sub_by_par[par_of_edge[P.rot[v][j]]].append(fi)
        for b in level:
            Hg = nx.Graph()
            for pi, subs in sub_by_par.items():
                if old_label[next(iter(par_T[pi]))] != b:
                    continue
                W = nx.Graph()
                for fi in subs:
                    occ = orders[fi]
                    nodes = [tau_copy(v, j) for (v, j) in occ]
                    if neg and len(nodes) >= 4 and fi == subs[0]:
                        nodes = nodes[:]; random.Random(fi).shuffle(nodes)
                    hub = ('hub', fi)
                    for k_, x in enumerate(nodes):
                        W.add_edge(hub, x); W.add_edge(x, nodes[(k_ + 1) % len(nodes)]) if len(nodes) > 1 else None
                        Hg.add_edge(('hub', fi), x[0])
                        Hg.add_edge(x[0], nodes[(k_ + 1) % len(nodes)][0]) if len(nodes) > 1 and x[0] != nodes[(k_ + 1) % len(nodes)][0] else None
                if d > 0:
                    occ = par_occ[pi]
                    nodes = [(v, j) for (v, j) in occ]
                    for k_, x in enumerate(nodes):
                        W.add_edge(('outer', pi), x)
                        if len(nodes) > 1:
                            W.add_edge(x, nodes[(k_ + 1) % len(nodes)])
                ok, _ = nx.check_planarity(W)
                if neg:
                    stats['neg_wheel_nonplanar' if not ok else 'neg_wheel_planar'] += 1
                else:
                    assert ok, 'wheel gluing inside a tile is not planar'
                stats['wheel_checks'] += 1
            X = bags[b]['X']; dss = dSstar(b)
            gv_new = set(corner_of[c_][0] for c_ in gamma)
            for v in dss | bags[b]['S']:
                if any(old_label[e] == b for e in P.rot[v]):
                    assert v in gv_new, 'hub with X-edges not in Gamma_{d+1}'
                    stats['hub_checks'] += 1
            for e, (a, c) in P.edges.items():
                if a in X and c in X and old_label[e] != b:
                    Hg.add_edge(a, c); stats['outside_edges'] += 1
                    assert a in dss and c in dss, 'outside edge leaves dS*_X'
            ok, _ = nx.check_planarity(Hg)
            assert ok or neg, 'H_X wheel model not planar'
            stats['H_checks'] += 1
    return stats, worst_ports, maxdepth

if __name__ == '__main__':
    tot = collections.Counter(); wp = 0
    mode = sys.argv[2] if len(sys.argv) > 2 else ''
    for seed in range(int(sys.argv[1]) if len(sys.argv) > 1 else 5):
        st, w, md = run(n=160, drop=0.3, seed=seed, virtual='virtual' in mode, neg='neg' in mode)
        tot.update(st); wp = max(wp, w)
        print(seed, dict(st), 'maxdepth', md, 'ports/|S_parent| max %.2f' % w)
    print('TOTAL', dict(tot))
