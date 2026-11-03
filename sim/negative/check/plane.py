"""Plane graphs, faces, the face-disjoint graph of [1], and the flow algorithm of the note, written from [1] and the note.
Rotation system from networkx's planarity test. Everything is checked against an own Dinic and against enumeration."""
import itertools, os, random, sys
from collections import Counter, deque, defaultdict
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import networkx as nx
from core_check import *


class Plane:
    def __init__(self, g, emb=None):
        ok, E = nx.check_planarity(g) if emb is None else (True, emb)
        assert ok, 'not planar'
        self.g = g
        self.V = sorted(g.nodes())
        self.pos = {v: i for i, v in enumerate(self.V)}
        self.rot = {v: list(E.neighbors_cw_order(v)) for v in self.V}
        self.darts = [(u, v) for u in self.V for v in self.rot[u]]
        # next dart on the face to the left of d
        self.nxt = {}
        for (u, v) in self.darts:
            r = self.rot[v]
            i = r.index(u)
            self.nxt[(u, v)] = (v, r[(i + 1) % len(r)])
        self.prv = {b: a for a, b in self.nxt.items()}
        self.lft = {}
        self.nf = 0
        self.face_darts = []
        for d in self.darts:
            if d in self.lft:
                continue
            walk = []
            x = d
            while x not in self.lft:
                self.lft[x] = self.nf
                walk.append(x)
                x = self.nxt[x]
            self.face_darts.append(walk)
            self.nf += 1
        self.rgt = {(u, v): self.lft[(v, u)] for (u, v) in self.darts}
        assert len(self.V) - g.number_of_edges() + self.nf == 2, 'Euler'

    def hat(self):
        """Ĝ of [1]: star centres, corner nodes, E_S, E_R, E_C. Corner at head of d in lft(d) is keyed by d."""
        nid = {}
        for v in self.V:
            nid[('c', v)] = len(nid)
        for d in self.darts:
            nid[('k', d)] = len(nid)      # corner at the head of d, between rev d and next d, in lft(d)
        self.nid = nid
        ES = [(nid[('c', d[1])], nid[('k', d)]) for d in self.darts]
        ER = []
        for d in self.darts:
            ER.append((nid[('k', self.prv[d])], nid[('k', d)]))
        # the E_C edge of an edge e = {a, b} with a < b: at the end a, between the corners of a on the two sides of e.
        # corner of a in lft(a -> b) is the head corner of prv(a -> b); corner of a in lft(b -> a) is the head corner of (b -> a).
        EC = {}
        for d in self.darts:
            a, b = d
            if self.pos[a] < self.pos[b]:
                x = nid[('k', self.prv[(a, b)])]     # in lft(a->b)
                y = nid[('k', (b, a))]              # in lft(b->a) = rgt(a->b)
                EC[(a, b)] = (y, x)                 # arc for dart d: from the corner in rgt(d) to the corner in lft(d)
                EC[(b, a)] = (x, y)                 # arc for rev d: from the corner in rgt(rev d) = lft(d) to lft(rev d) = rgt(d)
        return nid, ES, ER, EC

    def corner_of(self, d):
        """The nodes of the two corners at the tail of d, in lft(d) and in rgt(d)."""
        u, v = d
        return self.nid[('k', self.prv[d])], self.nid[('k', (v, u))] if False else None


def hat_arcs(P, mu):
    """Weights of the Dual Distance Lemma for dual dart lengths mu(d). Returns N, arcs, or None when a negative loop exists."""
    nid, ES, ER, EC = P.hat()
    N = len(nid)
    Lam = max((abs(x) for x in mu.values()), default=0)
    M = N * Lam + 1
    best = {}

    def add(a, b, w):
        if a == b:
            return w >= 0
        if (a, b) not in best or w < best[(a, b)]:
            best[(a, b)] = w
        return True
    for a, b in ES:
        add(a, b, M)
        add(b, a, M)
    for a, b in ER:
        add(a, b, 0)
        add(b, a, 0)
    for d, (a, b) in EC.items():
        if not add(a, b, mu[d]):
            return N, None
    return N, [(a, b, w) for (a, b), w in best.items()]


def hat_simple_graph(P):
    nid, ES, ER, EC = P.hat()
    h = nx.Graph()
    h.add_nodes_from(range(len(nid)))
    for a, b in ES + ER + list(EC.values()):
        if a != b:
            h.add_edge(a, b)
    return h


def dinic(nodes, caps, s, t):
    """caps: {(u, v): c >= 0}. Own Edmonds-Karp, returns value and flow on arcs."""
    res = defaultdict(int)
    adj = defaultdict(set)
    for (u, v), c in caps.items():
        res[(u, v)] += c
        adj[u].add(v)
        adj[v].add(u)
    val = 0
    while True:
        par = {s: None}
        q = deque([s])
        while q and t not in par:
            x = q.popleft()
            for y in adj[x]:
                if y not in par and res[(x, y)] > 0:
                    par[y] = x
                    q.append(y)
        if t not in par:
            break
        b = INF
        y = t
        while par[y] is not None:
            b = min(b, res[(par[y], y)])
            y = par[y]
        y = t
        while par[y] is not None:
            res[(par[y], y)] -= b
            res[(y, par[y])] += b
            y = par[y]
        val += b
    return val


def bfs_path(g, s, t):
    par = {s: None}
    q = deque([s])
    while q:
        x = q.popleft()
        for y in sorted(g[x]):
            if y not in par:
                par[y] = x
                q.append(y)
    p = []
    y = t
    while par[y] is not None:
        p.append((par[y], y))
        y = par[y]
    return p[::-1]


def dual_test(P, mu, solver, mode='hat'):
    """Corollary 3. Returns None for 'negative cycle', or psi on corners as {face: value}, checking the corners agree."""
    if mode == 'hat':
        N, arcs = hat_arcs(P, mu)
        if arcs is None:
            return None
        if solver is None:
            d = bf_all(N, arcs)
            if d is None:
                return None
            s = P.nid[('k', P.darts[0])]
            ds = bf_from(N, arcs, s)
        else:
            phi = scale_potential(N, arcs, solver)
            if phi is None:
                return None
            s = P.nid[('k', P.darts[0])]
            ds, par, dx = distances_from_potential(N, arcs, phi, s)
        # every corner node of a face must hold the same distance
        psi = {}
        for d in P.darts:
            f = P.lft[d]
            x = ds[P.nid[('k', d)]]
            if f in psi and psi[f] != x:
                raise AssertionError(('corners of a face disagree', f, psi[f], x))
            psi[f] = x
        return psi
    raise ValueError


def flow_from_psi(P, psi, beta, path):
    pth = set(path)
    rv = {(b, a) for a, b in path}
    f = {}
    for d in P.darts:
        f[d] = psi[P.lft[d]] - psi[P.rgt[d]] + (beta if d in pth else 0) - (beta if d in rv else 0)
    return f


def check_flow(P, cap, f, s, t, val):
    for d in P.darts:
        if f[d] != -f[(d[1], d[0])]:
            return 'antisym'
        if f[d] > cap.get(d, 0):
            return 'capacity'
    net = Counter()
    for d, x in f.items():
        net[d[0]] += x
    for v in P.V:
        want = val if v == s else (-val if v == t else 0)
        if net[v] != want:
            return 'conservation'
    return None


def theorem2(P, cap, s, t, solver, upper=None, fail=None, runs=5):
    """The algorithm of Section 6, with the rerun. fail(beta) forces a wrong 'negative cycle' answer (fault injection)."""
    path = bfs_path(P.g, s, t)
    pth = set(path)
    rv = {(b, a) for a, b in path}
    if upper is None:
        upper = sum(cap.values())

    def mu(beta):
        return {d: cap.get(d, 0) - (beta if d in pth else 0) + (beta if d in rv else 0) for d in P.darts}
    for attempt in range(runs):
        lo, hi = 0, upper + 1      # lo feasible, hi infeasible
        while hi - lo > 1:
            m = (lo + hi) // 2
            bad = fail is not None and fail(attempt, m)
            psi = None if bad else dual_test(P, mu(m), solver)
            if psi is None:
                hi = m
            else:
                lo = m
        psi = dual_test(P, mu(lo), solver)
        assert psi is not None
        f = flow_from_psi(P, psi, lo, path)
        err = check_flow(P, cap, f, s, t, lo)
        if err:
            raise AssertionError(err)
        # residual reachability, one oracle call: weight 0 on residual arcs, 1 otherwise
        idx = P.pos
        arcs = [(idx[d[0]], idx[d[1]], 0 if f[d] < cap.get(d, 0) else 1) for d in P.darts]
        off = [INF] * len(P.V)
        off[idx[s]] = 0
        dd = oracle(len(P.V), arcs, off)
        S = {v for v in P.V if dd[idx[v]] == 0}
        if t not in S:
            cutcap = sum(cap.get((a, b), 0) for a in S for b in P.g[a] if b not in S)
            assert cutcap == lo, ('cut value', cutcap, lo)
            return lo, f, S, attempt
    return lo, f, None, runs


def all_connected_planar(nmin, nmax):
    """All connected graphs on nmin..nmax vertices (up to isomorphism) from the atlas, planar only."""
    out = []
    for g in nx.graph_atlas_g():
        n = g.number_of_nodes()
        if n < nmin or n > nmax:
            continue
        if g.number_of_edges() == 0 or not nx.is_connected(g):
            continue
        if nx.check_planarity(g)[0]:
            out.append(g)
    return out
