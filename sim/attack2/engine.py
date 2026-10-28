"""attack2 engine: the tile construction of LEMMA15.md §3.2 on an arbitrary plane graph P (rotation
system, weights P.w) and an arbitrary (G1')-shaped BDD (bdd.py), with independent checks of
Claims 1-7, (T3), (T4a/b/c), (T5) and an end-to-end perturbed gluing test of Lemma 15'.

Corners are (v, j): the angle between rot[v][j-1] and rot[v][j]. Gamma is a set of corners.
Ports are ('p', v, j) with j the index of the Gamma-corner opening the sector; non-Gamma vertices
are ('i', v).
"""
import sys, os, itertools, collections, random, bisect, math
import numpy as np, networkx as nx
from scipy.sparse import csr_matrix
from scipy.sparse.csgraph import dijkstra as sp_dijkstra
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'attack'))
sys.path.insert(0, os.path.join(HERE, '..', 'tiles'))
from rot import Plane, monge_lp
from tiles import radial, sub_plane


class CheckFail(Exception):
    pass


_COMB = {}
def comb3(m):
    if m not in _COMB:
        _COMB[m] = np.array(list(itertools.combinations(range(m), 3)), dtype=np.int32).reshape(-1, 3)
    return _COMB[m]


def monge_viol(M, tol=1e-7):
    """max violation of (M) over all 4-subsets in the cyclic order of M's index, all 4 orientations."""
    k = M.shape[0]
    worst = 0.0; cnt = 0; arg = None
    if k < 4:
        return worst, cnt, arg
    for a in range(k - 3):
        c3 = comb3(k - a - 1) + (a + 1)
        b, c, d = c3[:, 0], c3[:, 1], c3[:, 2]
        v = np.stack([M[a, d] + M[b, c] - M[a, c] - M[b, d],
                      M[a, b] + M[d, c] - M[a, c] - M[d, b],
                      M[c, d] + M[b, a] - M[c, a] - M[b, d],
                      M[c, b] + M[d, a] - M[c, a] - M[d, b]])
        cnt += v.size
        mx = v.max()
        if mx > worst:
            worst = float(mx)
            i = np.unravel_index(v.argmax(), v.shape)
            arg = (i[0], a, int(b[i[1]]), int(c[i[1]]), int(d[i[1]]))
    return worst, cnt, arg


def apsp(nodes, arcs, sources):
    """arcs: dict (u,v)->w on node list; returns matrix dist[sources x nodes]."""
    idx = {x: i for i, x in enumerate(nodes)}
    if arcs:
        r = [idx[u] for (u, v) in arcs]; c = [idx[v] for (u, v) in arcs]; w = [max(x, 1e-12) for x in arcs.values()]
        A = csr_matrix((w, (r, c)), shape=(len(nodes), len(nodes)))
    else:
        A = csr_matrix((len(nodes), len(nodes)))
    return sp_dijkstra(A, directed=True, indices=[idx[s] for s in sources])


def add_arc(arcs, u, v, w):
    if u == v:
        return
    if (u, v) not in arcs or arcs[(u, v)] > w:
        arcs[(u, v)] = w


class Level:
    pass


class Engine:
    def __init__(self, P, bags, rng, opts=None):
        self.P, self.bags, self.rng = P, bags, rng
        self.o = dict(lp_max_ports=8, lp_samples=40, e2e=True, neg=False, rank_trees=2, stop=True,
                      monge_cap=10 ** 9, e2e_lp=0.3)
        self.o.update(opts or {})
        self.st = collections.Counter()
        self.mx = collections.defaultdict(float)
        self.fails = []
        self.lpc = collections.Counter()
        self.R, self.cid, self.corner_of = radial(P)
        faces, dart_face = P.faces()
        self.nfacesG = len(faces)
        self.gface = {}
        for v, r in P.rot.items():
            for j in range(len(r)):
                self.gface[(v, j)] = dart_face[(v, r[(j - 1) % len(r)])]
        self.pos = {v: {e: i for i, e in enumerate(r)} for v, r in P.rot.items()}
        self.eid = {frozenset(ab): e for e, ab in P.edges.items()}
        self.root = 0
        self.anc = {}
        for b in bags:
            out = []; p = bags[b]['parent']
            while p is not None:
                out.append(p); p = bags[p]['parent']
            self.anc[b] = out
        self.dss = {}
        for b, B in bags.items():
            s = set()
            for a in self.anc[b]:
                s |= bags[a]['S'] & B['X']
            self.dss[b] = s
        self.Gnx = nx.Graph([P.edges[e] for e in P.edges])
        self.Ninfo = {}

    # ------------------------------------------------------------------ helpers
    def fail(self, kind, info):
        self.st['FAIL ' + kind] += 1
        self.fails.append((kind, info))
        if self.o['stop']:
            raise CheckFail(kind, info)

    def mk_level(self, gamma, label):
        P = self.P
        L = Level()
        L.gamma = set(gamma); L.label = dict(label)
        L.gidx = collections.defaultdict(list)
        for (v, j) in gamma:
            L.gidx[v].append(j)
        for v in L.gidx:
            L.gidx[v].sort()
        L.gverts = set(L.gidx)
        # tiles by union-find
        uf = {e: e for e in P.edges}
        def find(x):
            while uf[x] != x:
                uf[x] = uf[uf[x]]; x = uf[x]
            return x
        for v, r in P.rot.items():
            for j in range(len(r)):
                if (v, j) not in gamma:
                    a, b = find(r[j - 1]), find(r[j])
                    if a != b:
                        uf[a] = b
        groups = collections.defaultdict(list)
        for e in P.edges:
            groups[find(e)].append(e)
        L.tiles = [set(g) for g in groups.values()]
        L.tile_of = {}
        for i, t in enumerate(L.tiles):
            for e in t:
                L.tile_of[e] = i
        L.owner = []
        for t in L.tiles:
            labs = {label[e] for e in t}
            if len(labs) != 1:
                self.fail('Claim2 tile with two labels', sorted(map(str, labs)))
            L.owner.append(next(iter(labs)))
        L.orders = None
        return L

    def sector(self, L, v, i):
        g = L.gidx.get(v)
        if not g:
            return None
        k = bisect.bisect_right(g, i) - 1
        return g[k]                # k = -1 wraps to the last corner

    def closing_corner(self, L, v, j):
        g = L.gidx[v]
        k = bisect.bisect_right(g, j)
        return g[k % len(g)]

    def node(self, L, v, e):
        s = self.sector(L, v, self.pos[v][e])
        return ('i', v) if s is None else ('p', v, s)

    def boundary_orders(self, L):
        """faces of Gamma (as R-subgraph) -> port sequences; maps to tiles (Fact 1 check)."""
        if L.orders is not None:
            return
        rids = set(self.cid[c] for c in L.gamma)
        Gm = sub_plane(self.R, rids)
        faces, _ = Gm.faces()
        L.orders = [None] * len(L.tiles)
        for cyc in faces:
            occ = []
            for (x, ex) in cyc:
                if x[0] != 'v':
                    continue
                v = x[1]
                j = self.corner_of[ex][1]
                occ.append(('p', v, j))
            tl = {L.tile_of[self.P.rot[v][j]] for (_, v, j) in occ}
            if len(tl) != 1:
                self.fail('Fact1 face meets several tiles', (len(tl),))
            ti = tl.pop()
            if L.orders[ti] is not None:
                self.fail('Fact1 tile with two faces', ti)
            if len(set(occ)) != len(occ):
                self.fail('T3 port visited twice', ti)
            L.orders[ti] = occ
        if any(o is None for o in L.orders):
            self.fail('Fact1 tile without face', None)

    def piece(self, L, ti):
        """exact piece P_tau: arcs dict, nodes, components (as lists of ports in sigma order)."""
        P = self.P
        arcs = {}; nodes = set(); und = nx.Graph()
        for e in L.tiles[ti]:
            a, c = P.edges[e]
            na, nc = self.node(L, a, e), self.node(L, c, e)
            add_arc(arcs, na, nc, P.w[(e, 0)]); add_arc(arcs, nc, na, P.w[(e, 1)])
            und.add_edge(na, nc); nodes |= {na, nc}
        order = L.orders[ti]
        for p in order:
            if p not in nodes:
                self.fail('T3 port without edge', p)
        for x in nodes:
            if x[0] == 'p' and x not in set(order):
                self.fail('T3 port missing from boundary walk', x)
        comps = []
        cid = {}
        for k, cc in enumerate(nx.connected_components(und)):
            for x in cc:
                cid[x] = k
            comps.append([p for p in order if p in cc])
        for c in comps:
            if not c:
                self.fail('Lemma15 component without port', None)
        return arcs, sorted(nodes, key=str), comps, cid

    # ------------------------------------------------------------------ construction
    def run(self):
        P, bags = self.P, self.bags
        maxd = max(B['depth'] for B in bags.values())
        label = {e: self.root for e in P.edges}
        self.levels = [self.mk_level(set(), label)]
        self.check_ranks()
        for d in range(maxd + 1):
            cur = self.levels[d]
            nonleaf = [b for b, B in bags.items() if B['depth'] == d and B.get('kids')]
            if not nonleaf:
                break
            newlabel = dict(cur.label)
            N = {}; Nnew = {}
            for b in nonleaf:
                N[b] = self.new_corners(d, b, cur, newlabel)
                Nnew[b] = N[b] - cur.gamma
            # (2b) disjointness
            seen = {}
            for b in nonleaf:
                for c in Nnew[b]:
                    if c in seen:
                        self.fail('Claim2b N_X\\Gamma_d overlap', (b, seen[c], c))
                    seen[c] = b
            for b in nonleaf:
                self.Ninfo[b] = (len(N[b]), len(Nnew[b]))
            gamma = cur.gamma | set().union(*N.values())
            nxt = self.mk_level(gamma, newlabel)
            self.levels.append(nxt)
            self.check_level(d, cur, nxt, nonleaf, Nnew)
        self.maxlevel = len(self.levels) - 1
        if self.o['e2e']:
            self.e2e()
        return self.st

    def new_corners(self, d, b, cur, newlabel):
        P, B = self.P, self.bags[b]
        X, S, q = B['X'], B['S'], B['q']
        label = cur.label
        kid_of = {}
        for kb in B['kids']:
            for x in self.bags[kb]['X'] - S:
                if x in kid_of:
                    self.fail('7a non-separator vertex in two children', x)
                kid_of[x] = kb
        for x in X - S:
            if x not in kid_of:
                self.fail('7a vertex in no child', x)
        inkid = B['kids'][0]
        myedges = [e for e in P.edges if label[e] == b]
        for e in myedges:
            a, c = P.edges[e]
            if a not in X or c not in X:
                self.fail('Claim1 label outside bag', e)
            if a not in S:
                newlabel[e] = kid_of[a]
            elif c not in S:
                newlabel[e] = kid_of[c]
            else:
                newlabel[e] = inkid
            Y = self.bags[newlabel[e]]['X']
            if a not in Y or c not in Y:
                self.fail('(7c)/(7c\') edge not in its new bag', e)
        new = set()
        # L_X
        Lcount = {}
        for v in S:
            r = P.rot[v]; cnt = 0
            for j in range(len(r)):
                e1, e2 = r[j - 1], r[j]
                if label[e1] == b and label[e2] == b and newlabel[e1] != newlabel[e2]:
                    new.add((v, j)); cnt += 1
            Lcount[v] = cnt
        self.check_claim7(b, Lcount, newlabel)
        # Q_X
        def rails(path):
            out = set()
            for u, w in zip(path, path[1:]):
                e = self.eid[frozenset((u, w))]
                if label[e] != b:
                    continue
                ju = self.pos[u][e]; jw = self.pos[w][e]
                out.add((u, (ju + 1) % len(P.rot[u]))); out.add((w, jw))
            return out
        new |= rails(q)
        qe = [self.eid[frozenset((q[i], q[i + 1]))] for i in range(len(q) - 1)]
        allX = all(label[e] == b for e in qe)
        self.st['q_edges_total'] += len(qe)
        self.st['q_edges_outside'] += sum(label[e] != b for e in qe)
        if not any(label[e] == b for e in qe):
            self.st['q_all_outside'] += 1
        if not myedges:
            self.st['bag_no_own_edges'] += 1
        # P_X
        if d >= 1 and allX and not (set(q) & cur.gverts):
            T = B['T']
            targets = cur.gverts & X
            if not targets:
                self.fail('Claim3 no Gamma vertex in bag', b)
            # BFS in T from V(q)
            par = {v: None for v in q}
            dq = collections.deque(q); hit = None
            while dq:
                x = dq.popleft()
                if x in targets:
                    hit = x; break
                for y in T.neighbors(x):
                    if y not in par:
                        par[y] = x; dq.append(y)
            if hit is None:
                self.fail('Claim3 p_X does not exist', b)
            path = [hit]
            while par[path[-1]] is not None:
                path.append(par[path[-1]])
            path = path[::-1]
            for x in path[1:-1]:
                if x in cur.gverts:
                    self.fail('Claim3 p_X interior on Gamma', b)
            for u, w in zip(path, path[1:]):
                if label[self.eid[frozenset((u, w))]] != b:
                    self.fail('Claim3 p_X edge not labelled X', (b, u, w))
            new |= rails(path)
            self.st['P_used'] += 1
            self.mx['p_len'] = max(self.mx['p_len'], len(path) - 1)
        return new

    def check_claim7(self, b, Lcount, newlabel):
        B = self.bags[b]
        self.mx['L_A_over_S_A'] = max(self.mx['L_A_over_S_A'], sum(Lcount.values()) / len(B['S']))
        for v, cnt in Lcount.items():
            kadj = B['nout_adj'].get(v, 0)
            self.st['claim7_vertex_checks'] += 1
            self.mx['L_per_vertex'] = max(self.mx['L_per_vertex'], cnt)
            if B['sat7a']:
                if cnt > 4 and self.o.get('region'):
                    self.st['region: >4 label changes at a vertex (expected)'] += 1
                    self.mx['region_L_per_vertex'] = max(self.mx['region_L_per_vertex'], cnt)
                elif cnt > 4:
                    self.fail('Claim7 more than 4 label changes at a separator vertex (7a holds)', (b, v, cnt))
            else:
                self.st['claim7_vertex_checks_7a_violated'] += 1
                self.mx['L_per_vertex_7a_violated'] = max(self.mx['L_per_vertex_7a_violated'], cnt)
                self.mx['kadj_7a_violated'] = max(self.mx['kadj_7a_violated'], kadj)
            if cnt > 2 * kadj:
                self.fail('Claim7 more than 2k label changes', (b, v, cnt, kadj))

    # ------------------------------------------------------------------ per level checks
    def check_level(self, d, cur, nxt, nonleaf, Nnew):
        P, bags = self.P, self.bags
        st = self.st
        # Claim 1
        for e in P.edges:
            a, c = P.edges[e]
            l0, l1 = cur.label[e], nxt.label[e]
            if l1 != l0 and bags[l1]['parent'] != l0:
                self.fail('Claim1 label jumped', e)
            if a not in bags[l1]['X'] or c not in bags[l1]['X']:
                self.fail('Claim1 edge not in its bag', e)
            if bags[l1].get('kids') and bags[l1]['depth'] != d + 1:
                self.fail('Claim1 non-leaf label at wrong depth', e)
        # Claim 2a
        for v, r in P.rot.items():
            if len({nxt.label[e] for e in r}) > 1 and v not in nxt.gverts:
                self.fail('Claim2a mixed labels at vertex off Gamma', v)
        # Claim 3: Gamma connected
        uf = {}
        def find(x):
            uf.setdefault(x, x)
            while uf[x] != x:
                uf[x] = uf[uf[x]]; x = uf[x]
            return x
        for (v, j) in nxt.gamma:
            a, b = find(('v', v)), find(('f', self.gface[(v, j)]))
            if a != b:
                uf[a] = b
        roots = {find(x) for x in list(uf)}
        if len(roots) != 1:
            self.fail('Claim3 Gamma disconnected', (d + 1, len(roots)))
        st['levels'] += 1
        # Fact 1 + T3 + Monge on every tile
        self.boundary_orders(nxt)
        nxt.pieces = {}
        for ti in range(len(nxt.tiles)):
            arcs, nodes, comps, cidm = self.piece(nxt, ti)
            nxt.pieces[ti] = (arcs, nodes, comps, cidm)
            st['tiles'] += 1
            ports = nxt.orders[ti]
            if len(ports) >= 4:
                D = apsp(nodes, arcs, ports)
                idx = {x: i for i, x in enumerate(nodes)}
                for cp in comps:
                    if len(cp) < 4:
                        continue
                    rows = [ports.index(p) for p in cp]
                    M = D[np.ix_(rows, [idx[p] for p in cp])]
                    if not np.all(np.isfinite(M)):
                        self.fail('W2 infinite distance inside a component', ti)
                    w, cnt, arg = monge_viol(M)
                    st['monge_checks'] += cnt
                    self.mx['ports_per_comp'] = max(self.mx['ports_per_comp'], len(cp))
                    if w > 1e-7:
                        self.fail('Monge (M) violated on exact tile component', (d + 1, ti, w, arg))
                    if self.o['neg'] and len(cp) >= 5:
                        perm = list(range(len(cp))); self.rng.shuffle(perm)
                        w2, _, _ = monge_viol(M[np.ix_(perm, perm)])
                        st['neg_monge_detected' if w2 > 1e-7 else 'neg_monge_missed'] += 1
                    if 4 <= len(cp) <= self.o['lp_max_ports'] and self.lpc[d + 1] < self.o['lp_samples']:
                        self.lpc[d + 1] += 1
                        delta = {(a, b): float(M[i, j]) for i, a in enumerate(cp) for j, b in enumerate(cp) if a != b}
                        status, _, _ = monge_lp(delta, cp, fix_alpha=1.0)
                        st['lp_checks'] += 1
                        if status != 0:
                            self.fail('LP(delta, sigma, 1) infeasible', (d + 1, ti, len(cp)))
        # Claim 4 for every non-leaf at depth d
        for b in nonleaf:
            for v in bags[b]['S']:
                if any(cur.label[e] == b for e in P.rot[v]):
                    st['claim4_checks'] += 1
                    if v not in nxt.gverts:
                        self.fail('Claim4 hub with X-edge not on Gamma_{d+1}', (b, v))
        # Claim 4 consequence and Claim 5 for every bag at depth d+1
        for b, B in bags.items():
            if B['depth'] != d + 1:
                continue
            X = B['X']; dss = self.dss[b]
            for v in dss:
                if any(nxt.label[e] == b for e in P.rot[v]):
                    st['claim4b_checks'] += 1
                    if v not in nxt.gverts:
                        self.fail('Claim4 hub of dS* with X-edge not on Gamma_d', (b, v))
            nout = 0
            for e, (a, c) in P.edges.items():
                if a in X and c in X and nxt.label[e] != b:
                    nout += 1
                    st['claim5_checks'] += 1
                    if a not in dss or c not in dss:
                        self.fail('Claim5 outside edge leaves dS*_X', (b, a, c))
            if nout > 3 * max(1, len(dss)):
                self.fail('Claim5 too many outside edges', (b, nout, len(dss)))
            self.mx['out_edges_per_dss'] = max(self.mx['out_edges_per_dss'], nout / max(1, len(dss)))
        # Claim 7 port counts
        ports_of = collections.Counter()
        for ti, o in enumerate(nxt.orders):
            ports_of[nxt.owner[ti]] += len(o)
        Dg = self.diam
        for b, B in bags.items():
            if B['depth'] != d + 1:
                continue
            J = ports_of.get(b, 0)
            bound = sum(self.Ninfo[a][1] for a in self.anc[b])
            st['claim7_J_checks'] += 1
            if J > bound:
                self.fail('Claim7 |J_X| exceeds sum of |N_A|', (b, J, bound))
            dep = B['depth']
            self.mx['J_max'] = max(self.mx['J_max'], J)
            self.mx['J_over_D_depth'] = max(self.mx['J_over_D_depth'], J / (Dg * dep))
            self.mx['J_over_sumS'] = max(self.mx['J_over_sumS'], J / max(1, sum(len(bags[a]['S']) for a in self.anc[b])))
        for b in nonleaf:
            tot = sum(ports_of.get(k, 0) for k in bags[b]['kids'])
            bound = sum(self.Ninfo[a][1] for a in self.anc[b] + [b])
            if tot > bound:
                self.fail('Claim7 sum over children of |J| exceeds bound', (b, tot, bound))
            self.mx['childJ_over_D_depth1'] = max(self.mx['childJ_over_D_depth1'], tot / (Dg * (bags[b]['depth'] + 1)))
            self.mx['nchildren'] = max(self.mx['nchildren'], len(bags[b]['kids']))
        # T4 + T5
        for b in nonleaf:
            self.check_T4(d, cur, nxt, b, Nnew[b])
        self.check_T5(nxt)

    # ------------------------------------------------------------------ T4
    def check_T4(self, d, cur, nxt, b, Nnew_b):
        P, bags, st = self.P, self.bags, self.st
        kids = set(bags[b]['kids'])
        X = bags[b]['X']
        par_tiles = [ti for ti in range(len(cur.tiles)) if cur.owner[ti] == b]
        child_tiles = [ti for ti in range(len(nxt.tiles)) if nxt.owner[ti] in kids]
        inside = collections.defaultdict(list)
        for ct in child_tiles:
            pts = {cur.tile_of[e] for e in nxt.tiles[ct]}
            if len(pts) != 1 or cur.owner[next(iter(pts))] != b:
                self.fail('T4 child tile not inside one tile of X', (b, ct))
            inside[next(iter(pts))].append(ct)
        for pt in par_tiles:
            for e in cur.tiles[pt]:
                if nxt.owner[nxt.tile_of[e]] not in kids:
                    self.fail('T4 edge of tile of X not in a child tile', (b, e))
        # (b) glue == P_tau, ports are terminal images; wheel planarity inside tau
        if d >= 1:
            self.boundary_orders(cur)
            for pt in par_tiles:
                glued = {}
                images = set()
                W = nx.Graph()
                for ct in inside[pt]:
                    for e in nxt.tiles[ct]:
                        a, c = P.edges[e]
                        ends = []
                        for v in (a, c):
                            x = self.node(nxt, v, e)
                            img = self.tau_image(cur, x)
                            if x[0] == 'p':
                                images.add(img)
                            ends.append(img)
                        glued[e] = tuple(ends)
                    for cp in nxt.pieces[ct][2]:
                        self.add_wheel(W, ('c', ct, tuple(cp[:1])), [self.tau_image(cur, x) for x in cp])
                for e in cur.tiles[pt]:
                    a, c = P.edges[e]
                    want = (self.node(cur, a, e), self.node(cur, c, e))
                    if glued.get(e) != want:
                        self.fail('T4b glue != P_tau', (b, pt, e, glued.get(e), want))
                st['T4b_glue_checks'] += 1
                for p in cur.orders[pt]:
                    if p not in images:
                        self.fail('T4b port of tau is not a terminal image', (b, pt, p))
                self.add_wheel(W, ('outer', pt), list(cur.orders[pt]))
                ok, _ = nx.check_planarity(W)
                st['wheel_tau_checks'] += 1
                if not ok:
                    self.fail('T4c wheel gluing inside tau not planar', (b, pt))
        # (a) glue of child tiles + outside edges == G[X]; dS+_X terminal images; H_X wheel planar
        out_edges = [e for e, (a, c) in P.edges.items() if a in X and c in X and cur.label[e] != b]
        child_edges = set().union(*[nxt.tiles[ct] for ct in child_tiles]) if child_tiles else set()
        GX_edges = {e for e, (a, c) in P.edges.items() if a in X and c in X}
        if child_edges & set(out_edges) or (child_edges | set(out_edges)) != GX_edges:
            self.fail('T4a glue != G[X]', b)
        term = set()
        for ct in child_tiles:
            for p in nxt.orders[ct]:
                term.add(p[1])
        endp = set()
        for e in out_edges:
            endp |= set(P.edges[e])
        term |= endp
        nonterm_single = set()
        for ct in child_tiles:
            for x in nxt.pieces[ct][1]:
                if x[0] == 'i':
                    nonterm_single.add(x[1])
        if nonterm_single & endp:
            self.fail('T4a non-terminal vertex is an outside-edge end', (b, sorted(nonterm_single & endp)[:3]))
        dsplus = self.dss[b] | bags[b]['S']
        for v in dsplus:
            st['T4a_terminal_checks'] += 1
            if v not in term:
                self.fail('T4a hub not a terminal image', (b, v))
        for v in X:
            if v not in term and v not in nonterm_single:
                self.fail('T4a vertex of X missing from glue', (b, v))
        H = nx.Graph()
        for ct in child_tiles:
            for cp in nxt.pieces[ct][2]:
                self.add_wheel(H, ('c', ct, tuple(cp[:1])), [('g', x[1]) for x in cp])
        for e in out_edges:
            a, c = P.edges[e]
            H.add_edge(('g', a), ('g', c))
        ok, _ = nx.check_planarity(H)
        st['H_wheel_checks'] += 1
        if not ok:
            self.fail('T4c H_X wheel model not planar', b)
        # T5: child tiles -> tiles of X via corners of N_X \ Gamma_d
        uf = {ct: ct for ct in child_tiles}
        def find(x):
            while uf[x] != x:
                uf[x] = uf[uf[x]]; x = uf[x]
            return x
        for (v, j) in Nnew_b:
            # sector closed by (v,j) and sector opened by (v,j), w.r.t. Gamma_{d+1}
            r = P.rot[v]
            t1 = nxt.tile_of[r[(j - 1) % len(r)]]; t2 = nxt.tile_of[r[j]]
            if t1 not in uf or t2 not in uf:
                self.fail('T5 new corner not between child tiles of X', (b, v, j))
            a_, b_ = find(t1), find(t2)
            if a_ != b_:
                uf[a_] = b_
        cls = collections.defaultdict(set)
        for ct in child_tiles:
            cls[find(ct)].add(ct)
        truth = sorted(sorted(v) for v in inside.values())
        got = sorted(sorted(v) for v in cls.values())
        st['T5_class_checks'] += 1
        if truth != got:
            self.fail('T5 child-tile classes != tiles of X', b)

    def tau_image(self, cur, x):
        if x[0] == 'i':
            return x
        _, v, j = x
        r = self.P.rot[v]
        s = self.sector(cur, v, j)
        return ('i', v) if s is None else ('p', v, s)

    def add_wheel(self, W, hub, imgs):
        if self.o['neg'] and len(imgs) >= 4 and self.rng.random() < 0.3:
            imgs = imgs[:]; self.rng.shuffle(imgs)
            self.st['neg_wheel_shuffled'] += 1
        k = len(imgs)
        pn = [('pn', hub, i) for i in range(k)]
        for i in range(k):
            W.add_edge(('hub', hub), pn[i])
            W.add_edge(pn[i], imgs[i])
            if k >= 2:
                W.add_edge(pn[i], pn[(i + 1) % k])

    # ------------------------------------------------------------------ T5 (orders from ranks) + rank lemma
    def check_ranks(self):
        P = self.P
        self.diam = max(1, nx.diameter(self.Gnx)) if len(self.Gnx) < 400 else max(1, nx.approximation.diameter(self.Gnx))
        self.ranks = []
        for t in range(self.o['rank_trees']):
            mode = ['bfs', 'dfs', 'rand'][t % 3]
            if mode == 'bfs':
                T = nx.bfs_tree(self.Gnx, self.rng.choice(list(P.rot))).to_undirected()
            elif mode == 'dfs':
                T = nx.dfs_tree(self.Gnx, self.rng.choice(list(P.rot))).to_undirected()
            else:
                H = nx.Graph(); [H.add_edge(a, b, weight=self.rng.random()) for a, b in self.Gnx.edges()]
                T = nx.minimum_spanning_tree(H)
            root = self.rng.choice(list(P.rot))
            rank = {}
            y, j = root, 0
            while (y, j) not in rank:
                rank[(y, j)] = len(rank)
                r = P.rot[y]; e = r[(j - 1) % len(r)]
                a, b = P.edges[e]
                if T.has_edge(a, b):
                    z = b if a == y else a
                    y, j = z, self.pos[z][e]
                else:
                    j = (j - 1) % len(r)
            if len(rank) != sum(len(r) for r in P.rot.values()):
                self.fail('rank contour missed corners', mode)
            # rank lemma on every face of G
            dirs = set()
            byface = collections.defaultdict(list)
            for c, f in self.gface.items():
                byface[f].append(c)
            for x, lst in self.R.rot.items():
                if x[0] != 'f':
                    continue
                rk = [rank[self.corner_of[e]] for e in lst]
                if len(rk) < 3:
                    continue
                desc = sum(rk[(i + 1) % len(rk)] < rk[i] for i in range(len(rk)))
                asc = len(rk) - desc
                self.st['rank_face_checks'] += 1
                if not (desc == 1 or asc == 1):
                    self.fail('rank lemma: face corners not in contour order', (mode, x))
                dirs.add('inc' if desc == 1 else 'dec')
            if len(dirs) > 1:
                self.fail('rank lemma: orientation differs between faces', mode)
            self.ranks.append(rank)

    def check_T5(self, L):
        """c_Y rebuilds sigma_tau for all tiles of Y from port records (corners, ranks, face IDs)."""
        P = self.P
        byowner = collections.defaultdict(list)
        for ti, o in enumerate(L.orders):
            byowner[L.owner[ti]].append(ti)
        for rank in self.ranks:
            okdir = {(+1, 'fwd'): 0, (-1, 'fwd'): 0, (+1, 'rev'): 0, (-1, 'rev'): 0}; ntiles = 0
            for Y, tis in byowner.items():
                rec_open = {}; corners_at_face = collections.defaultdict(set)
                for ti in tis:
                    for (_, v, j) in L.orders[ti]:
                        jc = self.closing_corner(L, v, j)
                        rec_open[(v, j)] = ti
                        for c in ((v, j), (v, jc)):
                            corners_at_face[self.gface[c]].add(c)
                srt = {f: sorted(cs, key=lambda c: rank[c]) for f, cs in corners_at_face.items()}
                pos_in = {f: {c: i for i, c in enumerate(lst)} for f, lst in srt.items()}
                for ti in tis:
                    order = [(v, j) for (_, v, j) in L.orders[ti]]
                    ntiles += 1
                    for dr in (+1, -1):
                        seq = [order[0]]; ok = True
                        while True:
                            v, j = seq[-1]
                            c = (v, self.closing_corner(L, v, j))
                            f = self.gface[c]; lst = srt[f]
                            nc = lst[(pos_in[f][c] + dr) % len(lst)]
                            if nc not in rec_open:
                                ok = False; break
                            if nc == seq[0]:
                                break
                            seq.append(nc)
                            if len(seq) > len(order):
                                ok = False; break
                        rev = [order[0]] + order[1:][::-1]
                        if ok and seq == order:
                            okdir[(dr, 'fwd')] += 1
                        if ok and seq == rev:
                            okdir[(dr, 'rev')] += 1
            self.st['T5_order_checks'] += ntiles
            if max(okdir.values()) != ntiles:
                self.fail('T5 sigma_tau not recovered from ranks', dict(okdir=okdir, ntiles=ntiles))
            self.st['T5_dir%+d_%s' % max((k for k in okdir if okdir[k] == ntiles), key=str)] += 1

    # ------------------------------------------------------------------ end-to-end (Lemma 15') with perturbed metrics
    def perturb(self, M):
        rng = self.rng
        k = M.shape[0]
        if k <= 1:
            return M.copy()
        out = M.copy()
        finite = M[np.isfinite(M) & (M > 0)]
        scale = float(finite.mean()) if finite.size else 1.0
        perm = list(range(k))
        bad = self.o.get('neg_e2e') and k >= 4 and rng.random() < 0.3
        if bad:                      # negative control: cuts along a WRONG cyclic order
            rng.shuffle(perm); self.st['neg_e2e_injected'] += 1
        for _ in range(rng.randint(1, 2 * k)):
            i = rng.randrange(k); Ln = rng.randrange(1, k)
            inI = np.zeros(k, bool)
            inI[[perm[(i + t) % k] for t in range(Ln)]] = True
            out += rng.uniform(0, (4.0 if bad else 0.4) * scale) * np.outer(inI, ~inI)
        if bad:
            return out
        if 4 <= k <= 7 and rng.random() < self.o['e2e_lp']:
            delta = {(a, b): float(out[a, b]) for a in range(k) for b in range(k) if a != b}
            obj = {p: rng.uniform(-1, 1) for p in delta}
            status, _, dd = monge_lp(delta, list(range(k)), fix_alpha=1.5, objective=obj)
            self.st['e2e_lp_calls'] += 1
            if status == 0:
                out = np.zeros((k, k))
                for (a, b), x in dd.items():
                    out[a, b] = x
                self.st['e2e_lp_points'] += 1
        w, _, _ = monge_viol(out, tol=1e-6)
        if w > 1e-7 * max(1.0, float(np.abs(out).max())) and not self.o.get('neg_e2e'):
            raise RuntimeError('perturbation broke Monge (harness bug) %g' % w)
        return out

    def e2e(self):
        """bottom-up: child component metrics (perturbed, Monge in their own order) glued via ~_tau
        must give, on every component of P_tau, a metric that is Monge in sigma_tau (G3 + R3 + T4c)."""
        bags, st, P = self.bags, self.st, self.P
        metric = {}     # (level, tile, comp index) -> (ports, matrix)
        lev_of = {b: B['depth'] for b, B in bags.items()}
        for ell in range(self.maxlevel, 0, -1):
            L = self.levels[ell]
            for ti in range(len(L.tiles)):
                Y = L.owner[ti]
                if lev_of[Y] != ell:
                    continue
                arcs, nodes, comps, cidm = L.pieces[ti]
                ports = L.orders[ti]
                if not bags[Y].get('kids'):
                    D = apsp(nodes, arcs, ports)
                    idx = {x: i for i, x in enumerate(nodes)}
                    for k_, cp in enumerate(comps):
                        rows = [ports.index(p) for p in cp]
                        M = D[np.ix_(rows, [idx[p] for p in cp])]
                        metric[(ell, ti, k_)] = (cp, self.perturb(M))
                    continue
                # non-leaf: glue children inside tile ti
                Ln = self.levels[ell + 1]
                kids = set(bags[Y]['kids'])
                garcs = {}; gnodes = set(ports)
                for ct in range(len(Ln.tiles)):
                    if Ln.owner[ct] not in kids:
                        continue
                    if L.tile_of[next(iter(Ln.tiles[ct]))] != ti:
                        continue
                    for k_, cp in enumerate(Ln.pieces[ct][2]):
                        cpp, m = metric[(ell + 1, ct, k_)]
                        imgs = [self.tau_image(L, x) for x in cpp]
                        gnodes |= set(imgs)
                        for i in range(len(cpp)):
                            for j in range(len(cpp)):
                                if i != j:
                                    add_arc(garcs, imgs[i], imgs[j], m[i, j])
                gl = sorted(gnodes, key=str)
                D = apsp(gl, garcs, ports)
                Dex = apsp(nodes, arcs, ports)
                gidx = {x: i for i, x in enumerate(gl)}; eidx = {x: i for i, x in enumerate(nodes)}
                pidx = {p: i for i, p in enumerate(ports)}
                # finiteness pattern must match components of P_tau
                for a in ports:
                    for b_ in ports:
                        fin_g = np.isfinite(D[pidx[a], gidx[b_]]); fin_e = np.isfinite(Dex[pidx[a], eidx[b_]])
                        if fin_g != fin_e:
                            self.fail('E2E finiteness pattern differs from P_tau components', (Y, ti))
                for k_, cp in enumerate(comps):
                    rows = [pidx[p] for p in cp]
                    M = D[np.ix_(rows, [gidx[p] for p in cp])]
                    Mex = Dex[np.ix_(rows, [eidx[p] for p in cp])]
                    if np.any(M < Mex - 1e-6):
                        self.fail('E2E glued distance below exact (R1 lower bound)', (Y, ti))
                    if len(cp) >= 4:
                        w, cnt, arg = monge_viol(M, tol=1e-6)
                        st['e2e_monge_checks'] += cnt
                        st['e2e_components'] += 1
                        self.mx['e2e_ports'] = max(self.mx['e2e_ports'], len(cp))
                        if w > 1e-6 * max(1.0, float(np.nanmax(M[np.isfinite(M)]))):
                            self.fail('E2E glued metric not Monge in sigma_tau', (Y, ti, w, arg, len(cp)))
                        if self.o['neg'] and len(cp) >= 5:
                            perm = list(range(len(cp))); self.rng.shuffle(perm)
                            w2, _, _ = monge_viol(M[np.ix_(perm, perm)], tol=1e-6)
                            st['neg_e2e_detected' if w2 > 1e-6 else 'neg_e2e_missed'] += 1
                    metric[(ell, ti, k_)] = (cp, self.perturb(M))
        # H_X for every non-leaf X: glue + outside edges; R1 sanity on dS+_X
        for b, B in bags.items():
            if not B.get('kids'):
                continue
            ell = B['depth']
            if ell + 1 > self.maxlevel:
                continue
            Ln = self.levels[ell + 1]; L = self.levels[ell]
            kids = set(B['kids']); X = B['X']
            garcs = {}; gn = set(('g', v) for v in X)
            for ct in range(len(Ln.tiles)):
                if Ln.owner[ct] not in kids:
                    continue
                for k_, cp in enumerate(Ln.pieces[ct][2]):
                    cpp, m = metric[(ell + 1, ct, k_)]
                    imgs = [('g', x[1]) for x in cpp]
                    for i in range(len(cpp)):
                        for j in range(len(cpp)):
                            if i != j:
                                add_arc(garcs, imgs[i], imgs[j], m[i, j])
            for e, (a, c) in P.edges.items():
                if a in X and c in X and L.label[e] != b:
                    add_arc(garcs, ('g', a), ('g', c), P.w[(e, 0)]); add_arc(garcs, ('g', c), ('g', a), P.w[(e, 1)])
            hubs = sorted(self.dss[b] | B['S'], key=str)
            gl = sorted(gn, key=str)
            DH = apsp(gl, garcs, [('g', h) for h in hubs])
            ex_arcs = {}
            for e, (a, c) in P.edges.items():
                if a in X and c in X:
                    add_arc(ex_arcs, ('g', a), ('g', c), P.w[(e, 0)]); add_arc(ex_arcs, ('g', c), ('g', a), P.w[(e, 1)])
            DG = apsp(gl, ex_arcs, [('g', h) for h in hubs])
            gi = {x: i for i, x in enumerate(gl)}
            cols = [gi[('g', h)] for h in hubs]
            A, Bm = DH[:, cols], DG[:, cols]
            if np.any(~np.isfinite(A)) or np.any(A < Bm - 1e-6):
                self.fail('E2E H_X distance on dS+_X below G[X] or infinite', b)
            st['e2e_H_checks'] += 1
            with np.errstate(divide='ignore', invalid='ignore'):
                ratio = np.where(Bm > 0, A / Bm, 1.0)
            self.mx['e2e_H_ratio'] = max(self.mx['e2e_H_ratio'], float(np.nanmax(ratio)))
