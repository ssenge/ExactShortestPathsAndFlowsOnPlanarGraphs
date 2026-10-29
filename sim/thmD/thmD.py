#!/usr/bin/env python3
"""Computational attack on "Theorem D" (exact min st-cut via Reif + exact SSSP on G^_l).

Single file (run with python3 -I).  Components:
  * Builder / Emb       : planar rotation systems with multi-edges, faces, corners.
  * explicit annuli     : node-parts as ranges of labelled darts, incision per [18] Def 2.2,
                          Remark 2.5, Remark 3.3 endpoint corners; built recursively.
  * build_ghat          : G^_l per [18] Sec 3.1 (+ Remark 3.3), 'literal' or 'fixed' variant.
  * sssp oracle         : virtual source, weights 0 / K c + 1 / M, parent = tight E_C edge.
  * run_reif            : [18] Algorithm 3 driven by the oracle, with all checks.

Labelled dart (d, lab): lab 0 = unincised, 1 = tail copy (attached at tail corner),
2 = head copy (attached at head corner).  Dual edge copy = {ld, partner(ld)}.
"""
import sys, os, random, heapq, math, json, time, collections, argparse, traceback
import networkx as nx

INF = float('inf')
SIZE_MAX = 30
GRID_MAX = 7

# =============================================================== embedding
class Builder:
    def __init__(self, n=0, ends=None, rot=None):
        self.n = n
        self.ends = list(ends) if ends else []
        self.rot = [list(r) for r in rot] if rot is not None else [[] for _ in range(n)]

    def copy(self):
        return Builder(self.n, self.ends, self.rot)

    @staticmethod
    def from_nx(G):
        ok, emb = nx.check_planarity(G)
        assert ok
        nodes = list(G.nodes())
        idx = {v: i for i, v in enumerate(nodes)}
        B = Builder(len(nodes))
        dart = {}
        for a, b in G.edges():
            e = len(B.ends)
            B.ends.append((idx[a], idx[b]))
            dart[(idx[a], idx[b])] = 2 * e
            dart[(idx[b], idx[a])] = 2 * e + 1
        for v in nodes:
            B.rot[idx[v]] = [dart[(idx[v], idx[w])] for w in emb.neighbors_cw_order(v)]
        return B

    def tail(self, d):
        u, v = self.ends[d >> 1]
        return u if d % 2 == 0 else v

    def head(self, d):
        return self.tail(d ^ 1)

    def fnext(self, d):
        h = self.head(d)
        r = self.rot[h]
        return r[(r.index(d ^ 1) + 1) % len(r)]

    def faces(self):
        seen = set()
        F = []
        for d0 in range(2 * len(self.ends)):
            if d0 in seen:
                continue
            cyc = []
            d = d0
            while d not in seen:
                seen.add(d)
                cyc.append(d)
                d = self.fnext(d)
            F.append(cyc)
        return F

    def connected(self):
        par = list(range(self.n))

        def f(x):
            while par[x] != x:
                par[x] = par[par[x]]
                x = par[x]
            return x
        for u, v in self.ends:
            par[f(u)] = f(v)
        return len({f(x) for x in range(self.n)}) == 1

    def euler_ok(self):
        return self.n - len(self.ends) + len(self.faces()) == 2

    # ---- operations (all keep planarity)
    def subdivide(self, e):
        u, v = self.ends[e]
        w = self.n
        self.n += 1
        self.rot.append([])
        e2 = len(self.ends)
        self.ends[e] = (u, w)
        self.ends.append((w, v))
        r = self.rot[v]
        r[r.index(2 * e + 1)] = 2 * e2 + 1
        self.rot[w] = [2 * e + 1, 2 * e2]
        return w

    def add_parallel(self, e):
        u, v = self.ends[e]
        e2 = len(self.ends)
        self.ends.append((u, v))
        ru = self.rot[u]
        ru.insert(ru.index(2 * e) + 1, 2 * e2)
        rv = self.rot[v]
        rv.insert(rv.index(2 * e + 1), 2 * e2 + 1)
        return e2

    def add_pendant(self, v, rng):
        w = self.n
        self.n += 1
        e2 = len(self.ends)
        self.ends.append((v, w))
        r = self.rot[v]
        r.insert(rng.randrange(len(r) + 1), 2 * e2)
        self.rot.append([2 * e2 + 1])
        return w

    def add_edge_in_face(self, da, db):
        """new edge between corner after da and corner after db (same face)."""
        u = self.head(da)
        v = self.head(db)
        assert u != v
        e2 = len(self.ends)
        self.ends.append((u, v))
        ru = self.rot[u]
        ru.insert(ru.index(da ^ 1) + 1, 2 * e2)
        rv = self.rot[v]
        rv.insert(rv.index(db ^ 1) + 1, 2 * e2 + 1)
        return e2

    def remove_edges(self, rem):
        rem = set(rem)
        keep = [e for e in range(len(self.ends)) if e not in rem]
        newid = {e: i for i, e in enumerate(keep)}
        ends = [self.ends[e] for e in keep]
        rot = [[2 * newid[d >> 1] + (d & 1) for d in r if (d >> 1) not in rem] for r in self.rot]
        return Builder(self.n, ends, rot), keep

    def delete_vertex(self, x):
        """remove vertex x and its edges; renumber vertices."""
        inc = {d >> 1 for d in self.rot[x]}
        B, keep = self.remove_edges(inc)
        ren = {v: (v if v < x else v - 1) for v in range(B.n) if v != x}
        ends = [(ren[u], ren[v]) for u, v in B.ends]
        rot = [B.rot[v] for v in range(B.n) if v != x]
        return Builder(B.n - 1, ends, rot), keep, ren

    def contract(self, e):
        """contract edge e=(u,v) into u; loops removed. returns builder, kept edges map, vertex ren."""
        u, v = self.ends[e]
        if u == v:
            return None
        ru = self.rot[u]
        rv = self.rot[v]
        iu = ru.index(2 * e)
        iv = rv.index(2 * e + 1)
        new_ru = ru[iu + 1:] + ru[:iu] + rv[iv + 1:] + rv[:iv]
        B = self.copy()
        B.rot[u] = new_ru
        B.rot[v] = []
        B.ends = [((u if a == v else a), (u if b == v else b)) for (a, b) in B.ends]
        loops = {i for i, (a, b) in enumerate(B.ends) if a == b}
        loops.add(e)
        # careful: e is now a loop (u,u); remove it and all loops
        B.ends[e] = (u, u)
        B2, keep = B.remove_edges(loops)
        ren = {w: (w if w < v else w - 1) for w in range(B2.n) if w != v}
        ends = [(ren[a], ren[b]) for a, b in B2.ends]
        rot = [B2.rot[w] for w in range(B2.n) if w != v]
        return Builder(B2.n - 1, ends, rot), keep, ren


class Emb:
    def __init__(self, B, cap):
        self.n = B.n
        self.ends = list(B.ends)
        self.m = len(self.ends)
        self.rot = [list(r) for r in B.rot]
        self.cap = list(cap)
        assert len(self.cap) == self.m
        self.tl = [0] * (2 * self.m)
        for e, (u, v) in enumerate(self.ends):
            self.tl[2 * e] = u
            self.tl[2 * e + 1] = v
        self.pos = [0] * (2 * self.m)
        for v in range(self.n):
            for i, d in enumerate(self.rot[v]):
                self.pos[d] = i
        self.face_of = [-1] * (2 * self.m)
        self.faces = []
        for d0 in range(2 * self.m):
            if self.face_of[d0] >= 0:
                continue
            f = len(self.faces)
            cyc = []
            d = d0
            while self.face_of[d] < 0:
                self.face_of[d] = f
                cyc.append(d)
                d = self.fnext(d)
            assert d == d0
            self.faces.append(cyc)
        assert self.n - self.m + len(self.faces) == 2, "not a connected planar embedding"

    def head(self, d):
        return self.tl[d ^ 1]

    def deg(self, v):
        return len(self.rot[v])

    def fnext(self, d):
        h = self.tl[d ^ 1]
        r = self.rot[h]
        return r[(self.pos[d ^ 1] + 1) % len(r)]

    def corner_face(self, v, i):
        return self.face_of[self.rot[v][i] ^ 1]

    def builder(self):
        return Builder(self.n, self.ends, self.rot)


# =============================================================== generic dijkstra
def dijkstra(adj, sources):
    """adj: dict/list node -> list of (nbr, w). sources: dict node->d0."""
    dist = {}
    pq = [(d0, s) for s, d0 in sources.items()]
    heapq.heapify(pq)
    best = dict(sources)
    while pq:
        d, x = heapq.heappop(pq)
        if x in dist:
            continue
        dist[x] = d
        for y, w in adj[x]:
            nd = d + w
            if y not in dist and nd < best.get(y, INF):
                best[y] = nd
                heapq.heappush(pq, (nd, y))
    return dist


# =============================================================== node-parts / annuli
def partner(ld):
    d, l = ld
    return (d ^ 1, (0, 2, 1)[l])


class NP:
    __slots__ = ('id', 'face', 'seq', 'cyc', 'anc', 'lowfirst')

    def __init__(self, id, face, seq, cyc, anc, lowfirst):
        self.id = id
        self.face = face
        self.seq = seq
        self.cyc = cyc
        self.anc = anc
        self.lowfirst = lowfirst

    def __repr__(self):
        return f"NP{self.id}(f{self.face},{self.anc},{'cyc' if self.cyc else 'lin'},{self.seq})"


def split_seq(seq, cut_darts, corner_after, cyclic):
    """seq: list of labelled darts. cut_darts: dict dart->tag (unlabelled darts to be cut).
    corner_after: dict dart->tag (corner cut right after that dart).
    Returns list of (segment, start_tag, end_tag)."""
    toks = []
    for (d, lab) in seq:
        if d in cut_darts:
            assert lab == 0, ("cut of labelled dart", d, lab)
            toks.append((d, 1))
            toks.append(('CUT', cut_darts[d]))
            toks.append((d, 2))
        else:
            toks.append((d, lab))
        if d in corner_after:
            toks.append(('CUT', corner_after[d]))
    cuts = [i for i, tk in enumerate(toks) if tk[0] == 'CUT']
    if not cuts:
        return [(list(seq), None, None)]
    if cyclic:
        k = cuts[0]
        start_tag = toks[k][1]
        toks = toks[k + 1:] + toks[:k] + [toks[k]]
        cur_start = start_tag
    else:
        cur_start = None
    segs = []
    cur = []
    for tk in toks:
        if tk[0] == 'CUT':
            segs.append((cur, cur_start, tk[1]))
            cur = []
            cur_start = tk[1]
        else:
            cur.append(tk)
    if not cyclic:
        segs.append((cur, cur_start, None))
    for s, a, b in segs:
        assert len(s) > 0, ("empty segment", seq, cut_darts, corner_after)
    return segs


class Ann:
    _ctr = 0

    def __init__(self, nodes, j, k, left, right, level):
        Ann._ctr += 1
        self.aid = Ann._ctr
        self.nodes = nodes
        self.ldmap = {}
        for X in nodes.values():
            for ld in X.seq:
                assert ld not in self.ldmap
                self.ldmap[ld] = X.id
        self.j, self.k = j, k
        self.left, self.right = left, right
        self.level = level
        self.piece = {}
        for X in nodes.values():
            if X.anc[0] == 'p':
                key = (X.anc[1], X.anc[2])
                assert key not in self.piece, ("two pieces of", key, "in one annulus")
                self.piece[key] = X.id

    def closed(self):
        return all(partner(ld) in self.ldmap for ld in self.ldmap)

    def adj(self, emb, K):
        """weights K*c+1 (K=None -> c)."""
        A = {x: [] for x in self.nodes}
        for X in self.nodes.values():
            for ld in X.seq:
                y = self.ldmap[partner(ld)]
                c = emb.cap[ld[0] >> 1]
                A[X.id].append((y, (K * c + 1) if K is not None else c))
        return A

    def edges_between(self, x, y):
        out = []
        for ld in self.nodes[x].seq:
            if self.ldmap[partner(ld)] == y:
                out.append(ld)
        return out


class Ctx:
    def __init__(self, emb):
        self.emb = emb
        self.ctr = 0
        self.store = {}

    def new_np(self, face, seq, cyc, anc, lowfirst):
        self.ctr += 1
        X = NP(self.ctr, face, seq, cyc, anc, lowfirst)
        self.store[self.ctr] = X
        return X


def level0_ann(ctx):
    emb = ctx.emb
    nodes = {}
    for f, cyc in enumerate(emb.faces):
        X = ctx.new_np(f, [(d, 0) for d in cyc], True, ('f', f), None)
        nodes[X.id] = X
    return Ann(nodes, None, None, None, None, 0)


def level1_ann(ctx, pf, pdart, scorner, tcorner):
    """pf: list of faces p_0..p_m; pdart[t] (t=1..m): dict face->dart of P-edge t in that face.
    scorner=(s,ci), tcorner=(t,ci). Returns Ann and lowfirst bookkeeping."""
    emb = ctx.emb
    m = len(pf) - 1
    s, cs = scorner
    tt, ct = tcorner
    da_s = emb.rot[s][cs] ^ 1
    da_t = emb.rot[tt][ct] ^ 1
    assert emb.face_of[da_s] == pf[0] and emb.face_of[da_t] == pf[m]
    onP = {f: t for t, f in enumerate(pf)}
    nodes = {}
    segs_of = {}
    for f, cyc in enumerate(emb.faces):
        if f not in onP:
            X = ctx.new_np(f, [(d, 0) for d in cyc], True, ('f', f), None)
            nodes[X.id] = X
            continue
        t = onP[f]
        cut = {}
        if t >= 1:
            cut[pdart[t][f]] = ('P', t)
        if t < m:
            cut[pdart[t + 1][f]] = ('P', t + 1)
        corner = {}
        if t == 0:
            corner[da_s] = ('S',)
        if t == m:
            assert da_t not in corner
            corner[da_t] = ('T',)
        segs = split_seq([(d, 0) for d in cyc], cut, corner, True)
        assert len(segs) == 2, segs
        segs_of[t] = segs
    # assign sides
    side = {}  # t -> {b: seg}
    s0 = [sg for sg in segs_of[0] if sg[2] == ('S',)]
    s1 = [sg for sg in segs_of[0] if sg[1] == ('S',)]
    assert len(s0) == 1 and len(s1) == 1
    side[0] = {0: s0[0], 1: s1[0]}
    for t in range(1, m + 1):
        side[t] = {}
        for b in (0, 1):
            prev = side[t - 1][b][0]
            dprev = pdart[t][pf[t - 1]]
            lds = [ld for ld in prev if ld[0] == dprev]
            assert len(lds) == 1
            pl = partner(lds[0])
            cand = [sg for sg in segs_of[t] if pl in sg[0]]
            assert len(cand) == 1
            side[t][b] = cand[0]
        assert side[t][0] is not side[t][1]
    # consistency at t-corner
    assert side[m][1][2] == ('T',), ("t-corner side inconsistent", side[m])
    assert side[m][0][1] == ('T',)
    for t in range(m + 1):
        for b in (0, 1):
            seg, st, en = side[t][b]
            if t == 0:
                lowfirst = (b == 1)
            else:
                dlow = pdart[t][pf[t]]
                if seg[0][0] == dlow:
                    lowfirst = True
                else:
                    assert seg[-1][0] == dlow
                    lowfirst = False
            X = ctx.new_np(pf[t], seg, False, ('p', t, b), lowfirst)
            nodes[X.id] = X
    A = Ann(nodes, 0, m, None, None, 1)
    assert A.closed()
    return A


def components(nodes):
    ldmap = {}
    for X in nodes.values():
        for ld in X.seq:
            ldmap[ld] = X.id
    comp = {}
    cid = 0
    for x in nodes:
        if x in comp:
            continue
        cid += 1
        comp[x] = cid
        st = [x]
        while st:
            y = st.pop()
            for ld in nodes[y].seq:
                z = ldmap.get(partner(ld))
                assert z is not None, ("not closed", ld)
                if z not in comp:
                    comp[z] = cid
                    st.append(z)
    return comp


# =============================================================== G^_l
class GHat:
    pass


def build_ghat(emb, incised, epts, variant='literal'):
    """epts: list of dict(v=, ci=, mode='L'|'R', e0=)."""
    G = GHat()
    V = {}
    keys = []

    def vid(key):
        if key not in V:
            V[key] = len(keys)
            keys.append(key)
        return V[key]
    E = []  # (a, b, typ, info, eid)
    n = emb.n
    for v in range(n):
        vid(('S', v))
        for i in range(emb.deg(v)):
            vid(('D', v, i))
            E.append((V[('S', v)], V[('D', v, i)], 'S', None, None))
    Lset, Rset = set(), set()
    for v in range(n):
        dv = emb.deg(v)
        for i in range(dv):
            if (emb.rot[v][i] >> 1) in incised:
                Lset.add((v, i))
            if (emb.rot[v][(i + 1) % dv] >> 1) in incised:
                Rset.add((v, i))
    # endpoint-case modifications
    modL = {}   # dart -> special head attachment key  (L mode, unincised)
    modR = {}   # dart -> special tail attachment key  (R mode, unincised)
    fixH = {}   # fixed variant, incised e0, L mode: head copy attaches to X
    fixT = {}   # fixed variant, incised e0, R mode: tail copy attaches to X
    ep_edges = collections.Counter()
    for ep in epts:
        v, ci, mode, e0 = ep['v'], ep['ci'], ep['mode'], ep['e0']
        dv = emb.deg(v)
        if mode == 'L':
            dd = emb.rot[v][ci] ^ 1
            assert dd >> 1 == e0
            if e0 not in incised:
                Lset.add((v, ci))
                modL[dd] = ('L', v, ci)
                ep_edges[e0] += 1
            elif variant == 'fixed':
                fixH[dd] = ('X', v, ci)
        else:
            dd = emb.rot[v][(ci + 1) % dv]
            assert dd >> 1 == e0
            if e0 not in incised:
                Rset.add((v, ci))
                modR[dd] = ('R', v, ci)
                ep_edges[e0] += 1
            elif variant == 'fixed':
                fixT[dd] = ('X', v, ci)
    for (v, i) in sorted(Lset):
        E.append((V[('D', v, i)], vid(('L', v, i)), 'S', None, None))
    for (v, i) in sorted(Rset):
        E.append((V[('D', v, i)], vid(('R', v, i)), 'S', None, None))
    for key in list(fixH.values()) + list(fixT.values()):
        _, v, i = key
        E.append((V[('D', v, i)], vid(key), 'S', None, None))
    # E_R per dart
    attach = {}  # ld -> (key at tail vertex, key at head vertex)
    for d in range(2 * emb.m):
        u = emb.tl[d]
        v = emb.head(d)
        cT = (emb.pos[d] - 1) % emb.deg(u)
        cH = emb.pos[d ^ 1]
        e = d >> 1
        if e not in incised:
            a = ('D', u, cT)
            b = ('D', v, cH)
            if d in modL:
                b = modL[d]
            if d in modR:
                a = modR[d]
            attach[(d, 0)] = (a, b)
        else:
            a1, b1 = ('D', u, cT), ('L', v, cH)
            a2, b2 = ('R', u, cT), ('D', v, cH)
            if d in fixH:
                b2 = fixH[d]
            if d in fixT:
                a1 = fixT[d]
            attach[(d, 1)] = (a1, b1)
            attach[(d, 2)] = (a2, b2)
    for ld, (a, b) in attach.items():
        E.append((vid(a), vid(b), 'R', ld, None))
    # E_C
    for e in range(emb.m):
        u, v = emb.ends[e]
        d = 2 * e                       # u -> v
        j = emb.pos[d]
        jm1 = (j - 1) % emb.deg(u)
        i = emb.pos[d ^ 1]
        im1 = (i - 1) % emb.deg(v)
        if e in incised:
            # u-side copy: lds (d,1),(d^1,2); v-side copy: (d,2),(d^1,1)
            if variant == 'literal':
                E.append((vid(('D', u, j)), vid(('D', u, jm1)), 'C', ((d, 1), (d ^ 1, 2)), (e, 1)))
                E.append((vid(('D', v, im1)), vid(('D', v, i)), 'C', ((d, 2), (d ^ 1, 1)), (e, 2)))
            else:
                for (l1, l2), w, tag in ((((d, 1), (d ^ 1, 2)), u, 1), (((d, 2), (d ^ 1, 1)), v, 2)):
                    a = [k for k in attach[l1] if k[1] == w][0]
                    b = [k for k in attach[l2] if k[1] == w][0]
                    E.append((vid(a), vid(b), 'C', (l1, l2), (e, tag)))
            continue
        lds = ((d, 0), (d ^ 1, 0))
        if ep_edges[e]:
            # endpoint-case edge(s): one E_C per endpoint record, at the other endpoint
            for kk, ep in enumerate([ep for ep in epts if ep['e0'] == e]):
                w = v if ep['v'] == u else u
                if variant == 'literal':
                    if w == u:
                        a, b = ('D', u, jm1), ('D', u, j)
                    else:
                        a, b = ('D', v, i), ('D', v, im1)
                else:
                    a = [k for k in attach[lds[0]] if k[1] == w][0]
                    b = [k for k in attach[lds[1]] if k[1] == w][0]
                E.append((vid(a), vid(b), 'C', lds, (e, 3 + kk)))
                if variant != 'literal':
                    break
            continue
        w = u if u < v else v
        if variant == 'literal':
            if w == u:
                a, b = ('D', u, jm1), ('D', u, j)
            else:
                a, b = ('D', v, i), ('D', v, im1)
        else:
            a = [k for k in attach[lds[0]] if k[1] == w][0]
            b = [k for k in attach[lds[1]] if k[1] == w][0]
        E.append((vid(a), vid(b), 'C', lds, (e, 0)))
    G.V, G.keys, G.E = V, keys, E
    # E_R components = p^ paths
    par = list(range(len(keys)))

    def fnd(x):
        while par[x] != x:
            par[x] = par[par[x]]
            x = par[x]
        return x
    for a, b, typ, info, _ in E:
        if typ == 'R':
            par[fnd(a)] = fnd(b)
    G.comp = [fnd(x) for x in range(len(keys))]
    G.phat_of_ld = {}
    G.lds_of_phat = collections.defaultdict(set)
    G.verts_of_phat = collections.defaultdict(list)
    for a, b, typ, info, _ in E:
        if typ == 'R':
            G.phat_of_ld[info] = G.comp[a]
            G.lds_of_phat[G.comp[a]].add(info)
    for x in range(len(keys)):
        G.verts_of_phat[G.comp[x]].append(x)
    G.nV = len(keys)
    return G


# =============================================================== oracle
class Fail(Exception):
    pass


class Checker:
    def __init__(self):
        self.flags = collections.Counter()
        self.notes = []

    def flag(self, name, note=None):
        self.flags[name] += 1
        if note is not None and len(self.notes) < 40:
            self.notes.append((name, note))


def ghat_weights(emb, G, mode, rng):
    K = G.nV + 1
    M = K * (sum(emb.cap) + 1) + 1
    if mode == 'Msmall':
        M = 1
    arcs = [[] for _ in range(G.nV)]
    cinfo = []  # (a, b, w_ab, w_ba, lds, eid)
    for a, b, typ, info, eid in G.E:
        if typ == 'R':
            wab = wba = 0
        elif typ == 'S':
            wab = wba = M
        else:
            c = emb.cap[eid[0]]
            if mode == 'cw':
                wab = wba = c
            else:
                wab = wba = K * c + 1
            if mode == 'noise':
                if rng.random() < 0.3:
                    wab += 1
                if rng.random() < 0.3:
                    wba += 1
            cinfo.append((a, b, wab, wba, info, eid))
        arcs[a].append((b, wab))
        arcs[b].append((a, wba))
    return K, M, arcs, cinfo


def map_ann_to_ghat(A, G, chk, where):
    """node-part -> p^ component; structural comparison."""
    np2ph = {}
    ph2np = collections.defaultdict(list)
    ok = True
    for X in A.nodes.values():
        comps = {G.phat_of_ld.get(ld) for ld in X.seq}
        if None in comps or len(comps) != 1:
            chk.flag('struct_split', (where, X.id, X.anc))
            ok = False
        ph = G.phat_of_ld.get(X.seq[0])
        np2ph[X.id] = ph
        ph2np[ph].append(X.id)
        if ph is not None and G.lds_of_phat[ph] != set(X.seq):
            chk.flag('struct_merge', (where, X.id, X.anc, sorted(G.lds_of_phat[ph] - set(X.seq))))
            ok = False
    return np2ph, ph2np, ok


def sssp_batch(ctx, G, reqs, mode, tiebreak, rng, chk, where, extra_pairs=0):
    """reqs: list of (Ann, src np id). Returns list of (dist_c, parent, tree_ok)."""
    emb = ctx.emb
    K, M, arcs, cinfo = ghat_weights(emb, G, mode, rng)
    sigma = G.nV
    arcs2 = arcs + [[]]
    maps = []
    for A, src in reqs:
        np2ph, ph2np, sok = map_ann_to_ghat(A, G, chk, where)
        maps.append((np2ph, ph2np))
        rep = min(G.verts_of_phat[np2ph[src]])
        arcs2[sigma].append((rep, 0))
    dist = dijkstra(arcs2, {sigma: 0})
    # E_C incidence by p^ component
    inc = collections.defaultdict(list)
    for (a, b, wab, wba, lds, eid) in cinfo:
        inc[G.comp[b]].append((a, b, wab, lds, eid))
        inc[G.comp[a]].append((b, a, wba, lds, eid))
    out = []
    for (A, src), (np2ph, ph2np) in zip(reqs, maps):
        # explicit annulus distances
        adjK = A.adj(emb, K if mode != 'cw' else None)
        dA = dijkstra(adjK, {src: 0})
        adjC = A.adj(emb, None)
        dC = dijkstra(adjC, {src: 0})
        assert len(dA) == len(A.nodes), "annulus not connected"
        dG = {}
        for x in A.nodes:
            ph = np2ph[x]
            vs = G.verts_of_phat[ph]
            ds = {dist.get(v, INF) for v in vs}
            if len(ds) != 1:
                chk.flag('i_phat_nonconst', (where, x))
            dG[x] = min(ds)
            if dG[x] != dA[x]:
                chk.flag('i_dist', (where, A.aid, x, A.nodes[x].anc, dG[x], dA[x]))
            if mode != 'cw':
                if dG[x] < INF and dG[x] // K != dC[x]:
                    chk.flag('i_floor', (where, x, dG[x] // K, dC[x]))
        # purity / (ii): components of E_R u E_C reachable from p^(src) w/o E_S
        # parents
        dist_c = {}
        parent = {}
        for x in A.nodes:
            if dG[x] == INF:
                chk.flag('ii_unreached', (where, x))
                continue
            dist_c[x] = dG[x] // K if mode != 'cw' else dG[x]
            if x == src:
                continue
            ph = np2ph[x]
            cands = []
            for (a, b, w, lds, eid) in inc[ph]:
                if dist.get(a, INF) + w == dist.get(b, INF) and dist.get(b, INF) == dG[x]:
                    cands.append((eid, a, b, lds))
            if not cands:
                if np2ph[x] == np2ph[src]:
                    # x and the source share one p^ path (merged node-parts): the claimed
                    # procedure sees distance 0 and an empty tree path.
                    chk.flag('struct_merged_with_source', (where, x, A.nodes[x].anc))
                    parent[x] = (src, 'MERGED', 'MERGED')
                    continue
                chk.flag('iii_noparent', (where, x))
                continue
            if tiebreak == 'minid':
                cands.sort(key=lambda z: z[0])
                eid, a, b, lds = cands[0]
            else:
                eid, a, b, lds = rng.choice(cands)
            pph = G.comp[a]
            pnps = [y for y in ph2np.get(pph, [])]
            if len(pnps) != 1:
                chk.flag('ii_parent_outside', (where, x, len(pnps)))
                continue
            y = pnps[0]
            # which ld is at x
            l1, l2 = lds
            if l1 in A.nodes[x].seq and l2 in A.nodes[y].seq:
                ldx, ldy = l1, l2
            elif l2 in A.nodes[x].seq and l1 in A.nodes[y].seq:
                ldx, ldy = l2, l1
            else:
                chk.flag('struct_ec_wiring', (where, x, y, lds))
                ldx, ldy = None, None
            parent[x] = (y, ldx, ldy)
        # tree check (iii)
        tree_ok = True
        for x in A.nodes:
            seen = set()
            z = x
            while z != src:
                if z in seen or z not in parent:
                    tree_ok = False
                    break
                seen.add(z)
                z = parent[z][0]
            if not tree_ok:
                break
        if not tree_ok:
            chk.flag('iii_not_tree', (where, A.aid))
        else:
            for x, (y, ldx, ldy) in parent.items():
                if ldx == 'MERGED':
                    continue
                if ldx is None:
                    tree_ok = False
                    continue
                c = emb.cap[ldx[0] >> 1]
                w = (K * c + 1) if mode != 'cw' else c
                if dA[y] + w != dA[x]:
                    chk.flag('iii_not_shortest', (where, x, y))
                    tree_ok = False
        out.append((dist_c, parent, tree_ok, dC))
    # (i) general pairs, sampled
    for _ in range(extra_pairs):
        if not reqs:
            break
        qi = rng.randrange(len(reqs))
        A = reqs[qi][0]
        np2ph = maps[qi][0]
        x = rng.choice(list(A.nodes))
        vs = G.verts_of_phat[np2ph[x]]
        v0 = rng.choice(vs)
        d1 = dijkstra(arcs, {v0: 0})
        dA = dijkstra(A.adj(emb, K if mode != 'cw' else None), {x: 0})
        for y in A.nodes:
            for v in G.verts_of_phat[np2ph[y]]:
                if d1.get(v, INF) != dA[y]:
                    chk.flag('i_pair', (where, x, y, d1.get(v, INF), dA[y]))
                    break
    return out


def tree_path(parent, src, tgt):
    """nodes from src to tgt, edges as (ld at earlier, ld at later)."""
    nodes = [tgt]
    edges = []
    z = tgt
    guard = 0
    while z != src:
        y, ldz, ldy = parent[z]
        if ldz is None:
            raise Fail('path edge unmapped')
        if ldz == 'MERGED':
            edges.append(('MERGED', 'MERGED'))
            nodes.append(y)
            z = y
            continue
        edges.append((ldy, ldz))
        nodes.append(y)
        z = y
        guard += 1
        if guard > 100000:
            raise Fail('parent loop')
    nodes.reverse()
    edges.reverse()
    return nodes, edges


def path_between(parent, root, a, b):
    """tree path a -> b in tree rooted at root (via LCA)."""
    na, ea = tree_path(parent, root, a)
    nb, eb = tree_path(parent, root, b)
    k = 0
    while k < min(len(na), len(nb)) and na[k] == nb[k]:
        k += 1
    k -= 1  # LCA index
    # a -> lca: reverse of na[k:], then lca -> b: nb[k:]
    nodes = list(reversed(na[k:])) + nb[k + 1:]
    edges = [(y, x) for (x, y) in reversed(ea[k:])] + eb[k:]
    return nodes, edges


# =============================================================== crossing in A1
class A1Map:
    def __init__(self, A1, Pedges):
        self.A1 = A1
        self.pos = {}
        self.byanc = {}
        for X in A1.nodes.values():
            self.byanc[X.anc] = X.id
            for i, ld in enumerate(X.seq):
                self.pos[ld] = (X.id, i, len(X.seq))
        self.Pedges = Pedges

    def ld1(self, ld):
        d, l = ld
        if (d >> 1) in self.Pedges:
            return ld
        return (d, 0)

    def lift(self, ctx, nodes, edges):
        N = [self.byanc[ctx.store[x].anc] for x in nodes]
        Ed = [(self.ld1(a), self.ld1(b)) for a, b in edges]
        for k, (a, b) in enumerate(Ed):
            assert self.pos[a][0] == N[k] and self.pos[b][0] == N[k + 1], "lift mismatch"
        return N, Ed


def side_of(pos, a, b, q):
    """at a node: is q strictly within forward cyclic interval (a, b)?"""
    xa, ia, L = pos[a]
    xb, ib, _ = pos[b]
    xq, iq, _ = pos[q]
    assert xa == xb == xq
    da = (ib - ia) % L
    dq = (iq - ia) % L
    return 0 < dq < da


def crosses(pos, P, Q):
    """P,Q = (nodes, edges) in A1 (simple in nodes). True if they cross."""
    PN, PE = P
    QN, QE = Q
    qidx = {x: i for i, x in enumerate(QN)}
    if len(set(QN)) != len(QN) or len(set(PN)) != len(PN):
        return None  # non-simple in A1
    i = 0
    res = []
    while i < len(PN):
        if PN[i] not in qidx:
            i += 1
            continue
        # extend run
        q0 = qidx[PN[i]]
        r = 0
        dirn = 0
        while i + r + 1 < len(PN) and PN[i + r + 1] in qidx:
            qn = qidx[PN[i + r + 1]]
            qc = qidx[PN[i + r]]
            st = qn - qc
            if abs(st) != 1 or (dirn and st != dirn):
                break
            pe = PE[i + r]
            qe = QE[min(qc, qn)]
            if st == 1:
                same = (qe == pe)
            else:
                same = (qe == (pe[1], pe[0]))
            if not same:
                break
            dirn = st
            r += 1
        a, b = i, i + r
        qa, qb = qidx[PN[a]], qidx[PN[b]]
        proper = a > 0 and b < len(PN) - 1 and min(qa, qb) > 0 and max(qa, qb) < len(QN) - 1
        if proper:
            p_in = PE[a - 1][1]
            if r == 0:
                p_out = PE[a][0]
                qx = [QE[qa - 1][1], QE[qa][0]]
                s1 = side_of(pos, p_in, p_out, qx[0])
                s2 = side_of(pos, p_in, p_out, qx[1])
                if s1 != s2:
                    res.append((a, b))
            else:
                # Q's non-run edge at PN[a] and at PN[b]
                if dirn == 1:
                    q_at_a = QE[qa - 1][1]
                    q_at_b = QE[qb][0]
                else:
                    q_at_a = QE[qa][0]
                    q_at_b = QE[qb - 1][1]
                s1 = side_of(pos, p_in, PE[a][0], q_at_a)
                s2 = side_of(pos, PE[b - 1][1], PE[b][0], q_at_b)
                if s1 != s2:
                    res.append((a, b))
        i = b + 1
    return res


# =============================================================== Reif driver
def mincut_nx(emb, s, t):
    G = nx.Graph()
    G.add_nodes_from(range(emb.n))
    for e, (u, v) in enumerate(emb.ends):
        if G.has_edge(u, v):
            G[u][v]['capacity'] += emb.cap[e]
        else:
            G.add_edge(u, v, capacity=emb.cap[e])
    return nx.minimum_cut_value(G, s, t)


def separates(emb, cutset, s, t):
    adj = [[] for _ in range(emb.n)]
    for e, (u, v) in enumerate(emb.ends):
        if e in cutset:
            continue
        adj[u].append(v)
        adj[v].append(u)
    seen = {s}
    st = [s]
    while st:
        x = st.pop()
        for y in adj[x]:
            if y not in seen:
                seen.add(y)
                st.append(y)
    return t not in seen


def chord_of(A_nodes_store, nodes, edges):
    return dict(nodes=list(nodes), edges=list(edges), prim={a[0] >> 1 for a, b in edges})


def incise(ctx, A, Qn, Qe):
    cuts = collections.defaultdict(dict)
    for k, (la, lb) in enumerate(Qe):
        if la[1] == 0:
            assert lb[1] == 0
            cuts[Qn[k]][la[0]] = ('Q',)
            cuts[Qn[k + 1]][lb[0]] = ('Q',)
    newnodes = dict(A.nodes)
    pieces = {}
    for x, cd in cuts.items():
        X = A.nodes[x]
        segs = split_seq(X.seq, cd, {}, X.cyc)
        del newnodes[x]
        ps = []
        for seg, _, _ in segs:
            Y = ctx.new_np(X.face, seg, False, X.anc, X.lowfirst)
            newnodes[Y.id] = Y
            ps.append(Y.id)
        pieces[x] = ps
    return newnodes, pieces


def run_reif(emb, s, t, opts, rng, chk, info):
    """opts: oracle mode, tiebreak, variant. Returns dict."""
    ctx = Ctx(emb)
    mode = opts.get('mode', 'claimed')
    tieb = opts.get('tiebreak', 'minid')
    variant = opts.get('variant', 'literal')
    xp = opts.get('pairs', 1)
    mc = mincut_nx(emb, s, t)
    info['mincut'] = mc
    # ---- level 0: P
    A0 = level0_ann(ctx)
    sfaces = sorted({emb.corner_face(s, i) for i in range(emb.deg(s))})
    tfaces = sorted({emb.corner_face(t, i) for i in range(emb.deg(t))})
    common = sorted(set(sfaces) & set(tfaces))
    if common and rng.random() < opts.get('pcommon', 0.5):
        f = g = rng.choice(common)
    elif rng.random() < opts.get('pfar', 0.5):
        # choose the pair (f,g) of faces at s,t with largest dual hop distance ([18]: any f in s*, g in t*)
        dadj = collections.defaultdict(set)
        for e in range(emb.m):
            a, b = emb.face_of[2 * e], emb.face_of[2 * e + 1]
            dadj[a].add(b)
            dadj[b].add(a)
        best = (-1, None)
        for f0 in sfaces:
            dist = {f0: 0}
            q = collections.deque([f0])
            while q:
                x = q.popleft()
                for y in dadj[x]:
                    if y not in dist:
                        dist[y] = dist[x] + 1
                        q.append(y)
            for g0 in tfaces:
                if dist[g0] > best[0]:
                    best = (dist[g0], (f0, g0))
        f, g = best[1]
    else:
        f = rng.choice(sfaces)
        g = rng.choice(tfaces)
    face2np = {X.face: X.id for X in A0.nodes.values()}
    G0 = build_ghat(emb, set(), [], variant)
    res0 = sssp_batch(ctx, G0, [(A0, face2np[f])], mode, tieb, rng, chk, ('L0',), xp)
    dist0, par0, ok0, _ = res0[0]
    if not ok0:
        raise Fail('level0 tree broken')
    Pn, Pe = tree_path(par0, face2np[f], face2np[g])
    pf = [ctx.store[x].face for x in Pn]
    if len(set(pf)) != len(pf):
        raise Fail('P not simple')
    m = len(pf) - 1
    Pedges = set()
    pdart = {}
    for k, (la, lb) in enumerate(Pe):
        e = la[0] >> 1
        Pedges.add(e)
        pdart[k + 1] = {pf[k]: la[0], pf[k + 1]: lb[0]}
    info['P_len'] = m + 1

    # ---- endpoint corners (Remark 3.3)
    def pick_corner(v, face):
        cs = [i for i in range(emb.deg(v)) if emb.corner_face(v, i) == face]
        assert cs
        if opts.get('e0rule') == 'free':
            # [18, Sec 5]: v picks any incident edge e0 of p(p0) whose dual is not on P; Remark 3.3's
            # formula is then applied with e0 = e_i (copy v_i^L), whether or not corner i lies in p0.
            dv = emb.deg(v)
            fr = []
            for i in range(dv):
                if (emb.rot[v][i] >> 1) in Pedges:
                    continue
                if emb.corner_face(v, i) == face:
                    fr.append((i, i))
                elif emb.corner_face(v, (i - 1) % dv) == face:
                    fr.append((i, (i - 1) % dv))
            if fr:
                i, xi = rng.choice(fr)
                if xi != i:
                    chk.flag('dev_free_wrongface')
                return dict(v=v, ci=i, mode='L', e0=emb.rot[v][i] >> 1, xci=xi)
        formal = [i for i in cs if (emb.rot[v][i] >> 1) not in Pedges]
        if formal:
            i = rng.choice(formal)
            return dict(v=v, ci=i, mode='L', e0=emb.rot[v][i] >> 1)
        mir = [i for i in cs if (emb.rot[v][(i + 1) % emb.deg(v)] >> 1) not in Pedges]
        assert mir
        i = rng.choice(mir)
        chk.flag('dev_mirrored_endpoint')
        return dict(v=v, ci=i, mode='R', e0=emb.rot[v][(i + 1) % emb.deg(v)] >> 1)
    eps = pick_corner(s, pf[0])
    ept = pick_corner(t, pf[m])
    epts = [eps, ept]
    info['e0_same'] = eps['e0'] == ept['e0']
    info['eps'] = eps
    info['ept'] = ept
    info['Pedges'] = sorted(Pedges)
    info['pf'] = pf
    info['incised_per_level'] = {}
    A1 = level1_ann(ctx, pf, pdart, (s, eps.get('xci', eps['ci'])), (t, ept.get('xci', ept['ci'])))
    amap = A1Map(A1, Pedges)
    # sanity: min_t dist_A1(p_t^0, p_t^1) == mincut
    adjC1 = A1.adj(emb, None)
    best_true = INF
    true_t = {}
    for tt in range(m + 1):
        dd = dijkstra(adjC1, {A1.piece[(tt, 0)]: 0})
        true_t[tt] = dd[A1.piece[(tt, 1)]]
        best_true = min(best_true, true_t[tt])
    if best_true != mc:
        chk.flag('sanity_reif_A1', (best_true, mc))

    results = []   # dicts: t, length, nodes, edges, kind, level
    computed_paths = []  # for crossing: (kind, nodes, edges)
    active = [A1]
    level = 1
    stats = collections.Counter()
    while active:
        incised = set(Pedges)
        for A in active:
            for ch in (A.left, A.right):
                if ch is not None:
                    incised |= ch['prim']
        G = build_ghat(emb, incised, epts, variant)
        info['incised_per_level'][level] = sorted(incised)
        where = ('L', level)
        # batch 1 and 2
        b1, b2 = [], []
        meta1, meta2 = [], []
        for A in active:
            leaf = A.k <= A.j + 1
            i = A.j if leaf else (A.j + A.k) // 2
            for key in ((i, 0), (i, 1), (A.k, 0), (A.k, 1)):
                if key[0] <= A.k and key not in A.piece:
                    chk.flag('impl_missing_piece', (A.aid, key, A.j, A.k))
            if (i, 0) not in A.piece or (i, 1) not in A.piece:
                continue
            b = rng.randrange(2)
            b1.append((A, A.piece[(i, b)]))
            meta1.append((A, i, b, leaf))
            if leaf and A.k == A.j + 1 and (A.k, 0) in A.piece and (A.k, 1) in A.piece:
                bb = rng.randrange(2)
                b2.append((A, A.piece[(A.k, bb)]))
                meta2.append((A, A.k, bb, True))
        out1 = sssp_batch(ctx, G, b1, mode, tieb, rng, chk, where + ('b1',), xp) if b1 else []
        out2 = sssp_batch(ctx, G, b2, mode, tieb, rng, chk, where + ('b2',), 0) if b2 else []
        Pi_of = {}
        for (A, i, b, leaf), (dc, par, ok, dC) in list(zip(meta1, out1)) + list(zip(meta2, out2)):
            src = A.piece[(i, b)]
            tgt = A.piece[(i, 1 - b)]
            if not ok and tgt not in par:
                raise Fail('tree broken')
            nodes, edges = tree_path(par, src, tgt)
            if b == 1:
                nodes = nodes[::-1]
                edges = [(y, x) for (x, y) in reversed(edges)]
            L = dc[tgt]
            if L != dC[tgt]:
                chk.flag('i_len', (where, i, L, dC[tgt]))
            if L > true_t[i]:
                stats['len_gt_trueA1'] += 1
            if L < true_t[i]:
                chk.flag('len_lt_trueA1', (where, i, L, true_t[i]))
            results.append(dict(t=i, length=L, nodes=nodes, edges=edges, kind='leaf' if leaf else 'Pi',
                                 level=level, aid=A.aid))
            cpe = dict(kind='leaf' if leaf else 'Pi', nodes=nodes, edges=edges, t=i, aid=A.aid, level=level, inc=None)
            computed_paths.append(cpe)
            if not leaf:
                Pi_of[A.aid] = (i, nodes, edges, cpe)
        # drop-end repair (opts['ends']): [18, Claim 2.4] drops i1 < t < i2, but i1 or i2 can lie outside
        # [A.j, A.k] and be dropped elsewhere. Compute P_a, P_b in A for a = max(i1, A.j), b = min(i2, A.k).
        if opts.get('ends'):
            bE, metaE = [[], []], [[], []]
            for A in active:
                if A.aid not in Pi_of:
                    continue
                i, Pn_, _, _ = Pi_of[A.aid]
                tidx = [ctx.store[x].anc[1] for x in Pn_ if ctx.store[x].anc[0] == 'p']
                for q, tt in enumerate((max(min(tidx), A.j), min(max(tidx), A.k))):
                    if tt == i:
                        continue
                    if (tt, 0) not in A.piece or (tt, 1) not in A.piece:
                        chk.flag('impl_end_missing_piece', (A.aid, tt))
                        continue
                    bb = rng.randrange(2)
                    bE[q].append((A, A.piece[(tt, bb)]))
                    metaE[q].append((A, tt, bb))
            for q in range(2):
                outE = sssp_batch(ctx, G, bE[q], mode, tieb, rng, chk, where + ('end%d' % q,), 0) if bE[q] else []
                for (A, tt, bb), (dc, par, ok, dC) in zip(metaE[q], outE):
                    tgt = A.piece[(tt, 1 - bb)]
                    if not ok and tgt not in par:
                        raise Fail('tree broken')
                    nodes, edges = tree_path(par, A.piece[(tt, bb)], tgt)
                    if bb == 1:
                        nodes = nodes[::-1]
                        edges = [(y, x) for (x, y) in reversed(edges)]
                    L = dc[tgt]
                    stats['end_computed'] += 1
                    if L > true_t[tt]:
                        stats['end_gt_trueA1'] += 1
                    if L < true_t[tt]:
                        chk.flag('len_lt_trueA1', (where, tt, L, true_t[tt]))
                    results.append(dict(t=tt, length=L, nodes=nodes, edges=edges, kind='end',
                                        level=level, aid=A.aid))
        # overlaps (Alg 3 lines 9-14)
        b3, meta3 = [], []
        ov = {}
        for A in active:
            if A.aid not in Pi_of:
                continue
            i, Pn_, Pe_, _ = Pi_of[A.aid]
            Pset = set(Pn_)
            for sidename, ch, a_, b_ in (('l', A.left, A.j, i), ('r', A.right, i, A.k)):
                if ch is None:
                    ov[(A.aid, sidename)] = False
                    continue
                inter = sorted(Pset & set(ch['nodes']))
                ov[(A.aid, sidename)] = bool(inter)
                if inter:
                    stats['overlap'] += 1
                    x = rng.choice(inter)
                    b3.append((A, x))
                    meta3.append((A, x, a_, b_))
        out3 = []
        # run each overlap as its own batch only if two per annulus; group: first-per-annulus, second
        groups = [[], []]
        seen_a = set()
        for q, mt in zip(b3, meta3):
            gi = 1 if q[0].aid in seen_a else 0
            seen_a.add(q[0].aid)
            groups[gi].append((q, mt))
        for grp in groups:
            if not grp:
                continue
            outs = sssp_batch(ctx, G, [q for q, _ in grp], mode, tieb, rng, chk, where + ('ov',), 0)
            for (q, (A, x, a_, b_)), (dc, par, ok, dC) in zip(grp, outs):
                for tt in range(a_, b_ + 1):
                    if (tt, 0) not in A.piece or (tt, 1) not in A.piece:
                        chk.flag('impl_ov_missing_piece', (A.aid, tt))
                        continue
                    p0, p1 = A.piece[(tt, 0)], A.piece[(tt, 1)]
                    L = dc[p0] + dc[p1]
                    nodes, edges = path_between(par, x, p0, p1)
                    if L > true_t[tt]:
                        stats['len_gt_trueA1'] += 1
                    if L < true_t[tt]:
                        chk.flag('len_lt_trueA1', (where, tt, L, true_t[tt]))
                    results.append(dict(t=tt, length=L, nodes=nodes, edges=edges, kind='ov',
                                        level=level, aid=A.aid))
                    computed_paths.append(dict(kind='ov', nodes=nodes, edges=edges, t=tt, aid=A.aid, level=level, inc=None))
        # incise, children
        nxt = []
        for A in active:
            if A.aid not in Pi_of:
                continue
            i, Pn_, Pe_, cpe = Pi_of[A.aid]
            if any(la == 'MERGED' for la, lb in Pe_):
                chk.flag('fail_merged_chord')
                continue
            ancs = [ctx.store[x].anc for x in Pn_]
            tidx = [a[1] for a in ancs if a[0] == 'p']
            i1, i2 = min(tidx), max(tidx)
            if i1 < A.j or i2 > A.k:
                stats['i12_outside'] += 1
            if opts.get('ends'):
                # interval form of [18, Claim 2.4]: every dropped t is dominated on [i1, t] or on [t, i2]
                for tt in range(max(i1 + 1, A.j), min(i2 - 1, A.k) + 1):
                    stats['c24_checked'] += 1
                    if not (all(true_t[q] <= true_t[tt] for q in range(i1, tt + 1)) or
                            all(true_t[q] <= true_t[tt] for q in range(tt, i2 + 1))):
                        chk.flag('c24_interval', (A.aid, i1, i2, tt, A.j, A.k))
            last0 = max(k for k, a in enumerate(ancs) if a[0] == 'p' and a[2] == 0)
            first1 = min(k for k, a in enumerate(ancs) if k > last0 and a[0] == 'p' and a[2] == 1)
            Qn = Pn_[last0:first1 + 1]
            Qe = Pe_[last0:first1]
            cpe['inc'] = (last0, first1)
            for x in Qn[1:-1]:
                assert ctx.store[x].anc[0] == 'f', "P_i' internal node on copy of P"
            newnodes, pieces = incise(ctx, A, Qn, Qe)
            comp = components(newnodes)
            X0, Y1 = Qn[0], Qn[-1]

            def lowhigh(x):
                if x not in pieces:
                    return None, None
                ps = pieces[x]
                assert len(ps) == 2
                Xn = ctx.store[x]
                return (ps[0], ps[1]) if Xn.lowfirst else (ps[1], ps[0])
            lx, hx = lowhigh(X0)
            ly, hy = lowhigh(Y1)
            xt, yt = ctx.store[X0].anc[1], ctx.store[Y1].anc[1]
            if opts.get('ends'):
                # (S): for x < t < y (or y < t < x) in range, incising Q leaves p_t^0 and p_t^1 apart;
                # and [i1, i2] is the hull of {i, x, y}
                if (i1, i2) != (min(i, xt, yt), max(i, xt, yt)):
                    chk.flag('hull_i12', (A.aid, i, xt, yt, i1, i2))
                for tt in range(max(min(xt, yt) + 1, A.j), min(max(xt, yt) - 1, A.k) + 1):
                    z0, z1 = A.piece.get((tt, 0)), A.piece.get((tt, 1))
                    stats['sep_checked'] += 1
                    if z0 in newnodes and z1 in newnodes and comp[z0] == comp[z1]:
                        chk.flag('sep_fail', (A.aid, tt, xt, yt))
                    elif z0 not in newnodes or z1 not in newnodes:
                        chk.flag('sep_piece_moved', (A.aid, tt))
            chain_l, chain_r = [], []
            for z in newnodes:
                an = newnodes[z].anc
                if an[0] != 'p' or z in (X0, Y1):
                    continue
                ref = xt if an[2] == 0 else yt
                if an[1] < ref:
                    chain_l.append(z)
                elif an[1] > ref:
                    chain_r.append(z)
            # Claim 5.8 bad edges: non-P_i edges of a boundary chord incident to a node in P_i cap chord
            PiE = {frozenset(e) for e in Pe_}
            bad = set()
            for ch in (A.left, A.right):
                if ch is None:
                    continue
                inter = set(Pn_) & set(ch['nodes'])
                for (la, lb) in ch['edges']:
                    if frozenset((la, lb)) in PiE:
                        continue
                    if A.ldmap[la] in inter or A.ldmap[lb] in inter:
                        bad.add(la)
                        bad.add(lb)
            for sidename, rng_ok, seeds, jj, kk, outer in (
                    ('l', A.j <= i1, [lx, ly] + chain_l, A.j, i1, A.left),
                    ('r', i2 <= A.k, [hx, hy] + chain_r, i2, A.k, A.right)):
                if ov.get((A.aid, sidename)):
                    continue
                if not rng_ok:
                    stats['child_range_empty'] += 1
                    continue
                seeds = [z for z in seeds if z is not None]
                if not seeds:
                    chk.flag('impl_no_seed', (A.aid, sidename))
                    continue
                cs = {comp[z] for z in seeds}
                if len(cs) != 1:
                    chk.flag('impl_seed_comps', (A.aid, sidename))
                    continue
                cid = cs.pop()
                cnodes = {x: newnodes[x] for x in newnodes if comp[x] == cid}
                if any(ld in bad for z in cnodes.values() for ld in z.seq):
                    chk.flag('child_has_bad_edge_discarded', (A.aid, sidename, jj, kk))
                    continue
                # chord copy
                cn, ce = [], []
                okc = True
                for x in Qn:
                    cand = [z for z in (pieces.get(x, [x])) if z in cnodes]
                    if len(cand) != 1:
                        okc = False
                        break
                    cn.append(cand[0])
                if okc:
                    for (la, lb) in Qe:
                        if la[1] == 0:
                            c1 = (la[0], 1)
                            c2 = (la[0], 2)
                            lda = c1 if any(c1 in cnodes[z].seq for z in cn) else c2
                            ce.append((lda, partner(lda)))
                        else:
                            ce.append((la, lb))
                if not okc:
                    chk.flag('impl_chord_copy', (A.aid, sidename))
                    continue
                chord = chord_of(None, cn, ce)
                if sidename == 'l':
                    C = Ann(cnodes, jj, kk, outer, chord, level + 1)
                else:
                    C = Ann(cnodes, jj, kk, chord, outer, level + 1)
                if not C.closed():
                    chk.flag('impl_child_not_closed', (A.aid, sidename))
                    continue
                nxt.append(C)
            # disjointness of children
        ids = [set(C.nodes) for C in nxt]
        tot = sum(len(z) for z in ids)
        if len(set().union(*ids)) != tot if ids else False:
            chk.flag('impl_children_overlap')
        active = nxt
        level += 1
        if level > 60:
            raise Fail('too many levels')
    info['levels'] = level - 1
    info['n_results'] = len(results)
    info.update({k: v for k, v in stats.items()})
    # ---- (iv)
    best = min(results, key=lambda r: (r['length'], r['t']))
    info['reported'] = best['length']
    if best['length'] != mc:
        chk.flag('iv_value', (best['length'], mc, best['t'], best['kind']))
    # cut extraction (Sec 5.2)
    nodes, edges = best['nodes'], best['edges']
    if any(la == 'MERGED' for la, lb in edges):
        chk.flag('iv_path_through_merge')
        realE = {la[0] >> 1 for la, lb in edges if la != 'MERGED'}
        val = sum(emb.cap[e] for e in realE)
        info['cut_value'] = val
        if val != mc:
            chk.flag('iv_cut_value', (val, mc))
        if not separates(emb, realE, s, t):
            chk.flag('iv_cut_not_separating', sorted(realE))
        return info
    ancs = [ctx.store[x].anc for x in nodes]
    last0 = max(k for k, a in enumerate(ancs) if a[0] == 'p' and a[2] == 0)
    first1 = min(k for k, a in enumerate(ancs) if k > last0 and a[0] == 'p' and a[2] == 1)
    seg_e = [la[0] >> 1 for la, lb in edges[last0:first1]]
    seg_f = [ctx.store[x].face for x in nodes[last0:first1 + 1]]
    inner = seg_f[1:-1]
    if (len(set(inner)) != len(inner) or set(inner) & {seg_f[0], seg_f[-1]}
            or len(set(seg_e)) != len(seg_e)):
        chk.flag('iv_Pm_prime_nonsimple', (seg_f, seg_e))
    x_, y_ = ancs[last0][1], ancs[first1][1]
    lo, hi = min(x_, y_), max(x_, y_)
    psub = [la[0] >> 1 for la, lb in Pe[lo:hi]]
    cutset = set(seg_e) | set(psub)
    val = sum(emb.cap[e] for e in cutset)
    info['cut_value'] = val
    if val != mc:
        chk.flag('iv_cut_value', (val, mc))
    if not separates(emb, cutset, s, t):
        chk.flag('iv_cut_not_separating', sorted(cutset))
    # ---- crossing in A1
    lifted = []
    for cp in computed_paths:
        if any(la == 'MERGED' for la, lb in cp['edges']):
            continue
        try:
            lifted.append((cp, amap.lift(ctx, cp['nodes'], cp['edges'])))
        except AssertionError:
            chk.flag('impl_lift')
    ncross = 0
    for a in range(len(lifted)):
        for b in range(a + 1, len(lifted)):
            ca, Pa = lifted[a]
            cb, Pb = lifted[b]
            # orient: X = path that was incised (if any) and computed earlier
            if cb['inc'] is not None and (ca['inc'] is None or cb['level'] < ca['level']):
                ca, Pa, cb, Pb = cb, Pb, ca, Pa
            runs = crosses(amap.pos, Pa, Pb)
            if runs is None:
                chk.flag('cross_nonsimple_in_A1')
                continue
            if not runs:
                continue
            ncross += 1
            if ca['aid'] == cb['aid']:
                chk.flag('xa_cross_same_annulus', (ca['kind'], ca['t'], cb['kind'], cb['t']))
            elif ca['inc'] is not None and ca['level'] < cb['level'] and crosses(
                    amap.pos, (Pa[0][ca['inc'][0]:ca['inc'][1] + 1], Pa[1][ca['inc'][0]:ca['inc'][1]]), Pb):
                chk.flag('xc_cross_incised_part', (ca['kind'], ca['t'], ca['inc'], cb['kind'], cb['t'], runs))
            else:
                chk.flag('xb_cross_nonincised_part', (ca['kind'], ca['t'], ca['inc'], cb['kind'], cb['t'], runs))
    info['ncross'] = ncross
    return info


# =============================================================== instance generators
def gen_delaunay(rng, n):
    import numpy as np
    from scipy.spatial import Delaunay
    pts = np.array([[rng.random(), rng.random()] for _ in range(n)])
    tri = Delaunay(pts)
    G = nx.Graph()
    G.add_nodes_from(range(n))
    for simp in tri.simplices:
        a, b, c = map(int, simp)
        G.add_edges_from([(a, b), (b, c), (a, c)])
    B = Builder.from_nx(G)
    return remove_some(B, rng, rng.uniform(0.15, 0.45))


def remove_some(B, rng, frac):
    k = int(frac * len(B.ends))
    order = list(range(len(B.ends)))
    rng.shuffle(order)
    removed = set()
    for e in order:
        if len(removed) >= k:
            break
        B2, _ = B.remove_edges(removed | {e})
        if B2.connected():
            removed.add(e)
    B2, _ = B.remove_edges(removed)
    return B2


def gen_grid(rng):
    a, b = rng.randint(2, GRID_MAX), rng.randint(2, GRID_MAX)
    B = Builder.from_nx(nx.grid_2d_graph(a, b))
    # diagonals in some faces
    for _ in range(rng.randint(0, 4)):
        F = [f for f in B.faces() if len(f) == 4]
        if not F:
            break
        f = rng.choice(F)
        k = rng.randrange(4)
        B.add_edge_in_face(f[k], f[(k + 2) % 4])
    if rng.random() < 0.6:
        B = remove_some(B, rng, rng.uniform(0.05, 0.3))
    return B


def gen_wheel(rng):
    n = rng.randint(4, 2 * GRID_MAX + 4)
    B = Builder.from_nx(nx.wheel_graph(n))
    if rng.random() < 0.5:
        B = remove_some(B, rng, rng.uniform(0.05, 0.3))
    return B


def gen_cycle_chords(rng):
    n = rng.randint(4, SIZE_MAX)
    B = Builder.from_nx(nx.cycle_graph(n))
    for _ in range(rng.randint(1, n // 2 + 1)):
        F = [f for f in B.faces() if len(f) >= 4]
        if not F:
            break
        f = rng.choice(F)
        a, b = rng.sample(range(len(f)), 2)
        u, v = B.head(f[a]), B.head(f[b])
        if u == v or any(set(B.ends[e]) == {u, v} for e in range(len(B.ends))):
            continue
        B.add_edge_in_face(f[a], f[b])
    return B


def gen_tree_plus(rng):
    n = rng.randint(3, SIZE_MAX)
    seq = [rng.randrange(n) for _ in range(n - 2)]
    T = nx.from_prufer_sequence(seq)
    B = Builder.from_nx(T)
    for _ in range(rng.randint(0, 4)):
        F = B.faces()
        f = rng.choice(F)
        if len(f) < 3:
            continue
        a, b = rng.sample(range(len(f)), 2)
        if B.head(f[a]) == B.head(f[b]):
            continue
        B.add_edge_in_face(f[a], f[b])
    return B


def gen_nested(rng):
    k = rng.randint(2, GRID_MAX // 2 + 2)
    L = rng.randint(3, GRID_MAX)
    G = nx.Graph()
    for r in range(k):
        for i in range(L):
            G.add_edge((r, i), (r, (i + 1) % L))
    for r in range(k - 1):
        sp = rng.sample(range(L), rng.randint(1, L))
        for i in sp:
            G.add_edge((r, i), (r + 1, i))
    B = Builder.from_nx(G)
    if rng.random() < 0.4:
        B = remove_some(B, rng, rng.uniform(0.05, 0.2))
    return B


def gen_rings(rng):
    k = rng.randint(3, GRID_MAX)
    L = rng.randint(3, 8)
    G = nx.Graph()
    for r in range(k):
        for i in range(L):
            G.add_edge((r, i), (r, (i + 1) % L))
    for r in range(k - 1):
        for i in range(L):
            if rng.random() < 0.7 or i == 0:
                G.add_edge((r, i), (r + 1, (i + rng.randint(0, 1)) % L))
    G.add_node('c')
    for i in range(L):
        if rng.random() < 0.6 or i == 0:
            G.add_edge('c', (0, i))
    B = Builder.from_nx(G)
    if rng.random() < 0.4:
        B = remove_some(B, rng, rng.uniform(0.03, 0.15))
    if rng.random() < 0.3:
        for _ in range(rng.randint(1, 3)):
            B.add_parallel(rng.randrange(len(B.ends)))
        for _ in range(rng.randint(0, 3)):
            B.subdivide(rng.randrange(len(B.ends)))
        for _ in range(rng.randint(0, 2)):
            B.add_pendant(rng.randrange(B.n), rng)
    return B


def gen_messy(rng):
    base = rng.choice(['delaunay', 'grid', 'wheel', 'cyc', 'tree'])
    if base == 'delaunay':
        B = gen_delaunay(rng, rng.randint(5, 14))
    elif base == 'grid':
        B = gen_grid(rng)
    elif base == 'wheel':
        B = gen_wheel(rng)
    elif base == 'cyc':
        B = gen_cycle_chords(rng)
    else:
        B = gen_tree_plus(rng)
    for _ in range(rng.randint(0, 4)):
        B.subdivide(rng.randrange(len(B.ends)))
    for _ in range(rng.randint(0, 4)):
        B.add_parallel(rng.randrange(len(B.ends)))
    for _ in range(rng.randint(0, 4)):
        B.add_pendant(rng.randrange(B.n), rng)
    if rng.random() < 0.3:
        # make a bridge: subdivide then remove nothing; or attach a small tree
        v = rng.randrange(B.n)
        w = B.add_pendant(v, rng)
        if rng.random() < 0.5:
            B.add_pendant(w, rng)
            B.add_pendant(w, rng)
    return B


FAMILIES = {
    'delaunay': lambda rng: gen_delaunay(rng, rng.randint(5, SIZE_MAX)),
    'grid': gen_grid,
    'wheel': gen_wheel,
    'cycle_chords': gen_cycle_chords,
    'tree_plus': gen_tree_plus,
    'nested': gen_nested,
    'messy': gen_messy,
    'rings': gen_rings,
}


def gen_caps(rng, m, scheme):
    if scheme == 'zeros':
        return [0 if rng.random() < 0.55 else rng.randint(1, 3) for _ in range(m)]
    if scheme == 'equal':
        c = rng.choice([1, 1, 1, 2, 5, 0])
        return [c] * m
    if scheme == 'huge':
        caps = [rng.randint(1, 5) for _ in range(m)]
        for _ in range(rng.randint(1, max(1, m // 4))):
            caps[rng.randrange(m)] = 10 ** 6
        return caps
    if scheme == 'small':
        return [rng.randint(0, 3) for _ in range(m)]
    raise ValueError(scheme)


SCHEMES = ['zeros', 'equal', 'huge', 'small']
STMODES = ['face', 'adj', 'far', 'deep', 'deep', 'bridge', 'random']


def pick_st(B, rng, mode):
    n = B.n
    if mode == 'face':
        F = B.faces()
        f = rng.choice(F)
        vs = sorted({B.tail(d) for d in f})
        if len(vs) >= 2:
            s, t = rng.sample(vs, 2)
            return s, t
    if mode == 'adj':
        u, v = B.ends[rng.randrange(len(B.ends))]
        if u != v:
            return (u, v) if rng.random() < 0.5 else (v, u)
    if mode == 'far':
        G = nx.Graph()
        G.add_edges_from(B.ends)
        s = rng.randrange(n)
        d = nx.single_source_shortest_path_length(G, s)
        mx = max(d.values())
        t = rng.choice([x for x in d if d[x] == mx])
        if t != s:
            return s, t
    if mode == 'bridge':
        G = nx.MultiGraph()
        G.add_nodes_from(range(n))
        G.add_edges_from(B.ends)
        Gs = nx.Graph(G)
        br = []
        for u, v in nx.bridges(Gs):
            if G.number_of_edges(u, v) == 1:
                br.append((u, v))
        deg1 = [v for v in range(n) if len(B.rot[v]) == 1]
        if br or deg1:
            if br and (not deg1 or rng.random() < 0.5):
                u, v = rng.choice(br)
                s = rng.choice([u, v])
            else:
                s = rng.choice(deg1)
            t = rng.choice([x for x in range(n) if x != s])
            return (s, t) if rng.random() < 0.5 else (t, s)
    if mode == 'deep':
        # maximise dual hop distance between faces at s and faces at t
        F = B.faces()
        fo = {}
        for fi, cyc in enumerate(F):
            for d in cyc:
                fo[d] = fi
        dadj = collections.defaultdict(set)
        for e in range(len(B.ends)):
            dadj[fo[2 * e]].add(fo[2 * e + 1])
            dadj[fo[2 * e + 1]].add(fo[2 * e])
        vf = collections.defaultdict(set)
        for d, fi in fo.items():
            vf[B.head(d)].add(fi)
        best = (-1, None)
        cand = rng.sample(range(n), min(n, 25))
        for s in cand:
            dist = {f: 0 for f in vf[s]}
            q = collections.deque(vf[s])
            while q:
                x = q.popleft()
                for y in dadj[x]:
                    if y not in dist:
                        dist[y] = dist[x] + 1
                        q.append(y)
            for t in range(n):
                if t == s:
                    continue
                dd = min(dist[f] for f in vf[t])
                if dd > best[0] or (dd == best[0] and rng.random() < 0.3):
                    best = (dd, (s, t))
        if best[1]:
            return best[1]
    s, t = rng.sample(range(n), 2)
    return s, t


def make_instance(seed, family=None, scheme=None, stmode=None):
    rng = random.Random(seed)
    family = family or rng.choice(list(FAMILIES))
    scheme = scheme or rng.choice(SCHEMES)
    stmode = stmode or rng.choice(STMODES)
    B = FAMILIES[family](rng)
    assert B.connected() and B.euler_ok()
    caps = gen_caps(rng, len(B.ends), scheme)
    s, t = pick_st(B, rng, stmode)
    return dict(seed=seed, family=family, scheme=scheme, stmode=stmode,
                n=B.n, ends=B.ends, rot=B.rot, cap=caps, s=s, t=t)


def inst_emb(I):
    return Emb(Builder(I['n'], I['ends'], I['rot']), I['cap'])


def run_one(I, opts, run_seed):
    emb = inst_emb(I)
    chk = Checker()
    info = {}
    rng = random.Random(run_seed)
    try:
        run_reif(emb, I['s'], I['t'], opts, rng, chk, info)
    except Fail as ex:
        chk.flag('fail_exception', str(ex))
    except AssertionError as ex:
        chk.flag('impl_assert', traceback.format_exc()[-600:])
    except KeyError as ex:
        chk.flag('fail_keyerror', traceback.format_exc()[-600:])
    return chk, info


CLAIM_FLAGS = ('i_dist', 'i_phat_nonconst', 'i_floor', 'i_pair', 'i_len', 'ii_unreached', 'ii_parent_outside',
               'iii_noparent', 'iii_not_tree', 'iii_not_shortest', 'cross_main', 'cross_ov',
               'iv_value', 'iv_cut_value', 'iv_cut_not_separating', 'len_lt_trueA1', 'fail_exception',
               'fail_keyerror', 'struct_split', 'struct_merge', 'struct_ec_wiring')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--start', type=int, default=0)
    ap.add_argument('--count', type=int, default=100)
    ap.add_argument('--mode', default='claimed')
    ap.add_argument('--variant', default='literal')
    ap.add_argument('--tiebreak', default='minid')
    ap.add_argument('--family', default=None)
    ap.add_argument('--runs', type=int, default=1)
    ap.add_argument('--out', default=None)
    ap.add_argument('--size', type=int, default=30)
    ap.add_argument('--grid', type=int, default=7)
    ap.add_argument('--pcommon', type=float, default=0.5)
    ap.add_argument('--pfar', type=float, default=0.5)
    ap.add_argument('--e0rule', default='formal')
    ap.add_argument('--ends', type=int, default=0)
    a = ap.parse_args()
    global SIZE_MAX, GRID_MAX
    SIZE_MAX, GRID_MAX = a.size, a.grid
    opts = dict(mode=a.mode, variant=a.variant, tiebreak=a.tiebreak, pairs=1, pcommon=a.pcommon, pfar=a.pfar, e0rule=a.e0rule,
                ends=a.ends)
    tot = collections.Counter()
    fam = collections.Counter()
    famfail = collections.Counter()
    fails = []
    t0 = time.time()
    for sd in range(a.start, a.start + a.count):
        I = make_instance(sd, a.family)
        for r in range(a.runs):
            chk, info = run_one(I, opts, sd * 1000 + r)
            fam[I['family']] += 1
            tot['levels=%s' % info.get('levels')] += 1
            for kk in ('overlap', 'i12_outside', 'child_range_empty', 'len_gt_trueA1', 'end_computed',
                       'end_gt_trueA1', 'c24_checked', 'sep_checked'):
                if info.get(kk):
                    tot['stat_' + kk] += 1
            if info.get('P_len', 0) >= 8:
                tot['stat_Plen>=8'] += 1
            if info.get('e0_same'):
                tot['stat_e0_same'] += 1
            bad = {k: v for k, v in chk.flags.items() if not k.startswith(('dev_', 'xa_', 'xb_'))}
            for k in chk.flags:
                tot[k] += 1
            if bad:
                if 'dev_free_wrongface' in chk.flags:
                    tot['rc_D3_free_e0_wrong_face'] += 1
                elif info.get('e0_same'):
                    tot['rc_D2_e0_eq_elast'] += 1
                elif 'struct_merge' in chk.flags or 'struct_merged_with_source' in chk.flags:
                    tot['rc_D1_incised_endpoint_edge'] += 1
                else:
                    tot['rc_other'] += 1
                if 'iv_value' in chk.flags or 'iv_cut_value' in chk.flags or 'iv_cut_not_separating' in chk.flags \
                        or 'fail_exception' in chk.flags:
                    tot['rc_wrong_or_no_answer'] += 1
                famfail[I['family']] += 1
                fails.append(dict(seed=sd, run=r, family=I['family'], scheme=I['scheme'], stmode=I['stmode'],
                                  n=I['n'], m=len(I['ends']), flags=dict(chk.flags), notes=[str(x) for x in chk.notes[:6]],
                                  info=info))
    res = dict(opts=opts, start=a.start, count=a.count, runs=a.runs, families=dict(fam),
               family_fail=dict(famfail), flag_instances=dict(tot), nfail=len(fails),
               secs=time.time() - t0, fails=fails[:200])
    s = json.dumps(res, indent=1, default=str)
    if a.out:
        with open(a.out, 'w') as fh:
            fh.write(s)
    print(json.dumps({k: res[k] for k in ('opts', 'families', 'family_fail', 'flag_instances', 'nfail', 'secs')},
                     default=str))


if __name__ == '__main__':
    main()
