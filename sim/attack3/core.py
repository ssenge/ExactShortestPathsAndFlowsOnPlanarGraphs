"""attack3: independent implementation of LEMMA15.md §3 (tiles) with [8]-shaped children.

Straight-line plane graph G (coordinates).  Virtual closing edges are straight segments between
vertices that cross no edge of G (so they lie inside a face of G, hence of G[X]).
Corner (v,j) = angle between rot[v][j-1] and rot[v][j] (ccw).  Face walk: arrive at v from
rot[v][k], leave towards rot[v][k-1]; the corner passed is (v,k).
"""
import math, random, collections, itertools, sys
import numpy as np, networkx as nx
from scipy.sparse import coo_matrix
from scipy.sparse.csgraph import dijkstra, connected_components

TAU = 2 * math.pi


class Fail(Exception):
    pass


def between(a, x, b):
    """x strictly inside the ccw arc from a to b."""
    return 1e-10 < (x - a) % TAU < (b - a) % TAU - 1e-10


def pip(pts, poly):
    x = pts[:, 0][:, None]; y = pts[:, 1][:, None]
    x1 = poly[:, 0][None, :]; y1 = poly[:, 1][None, :]
    x2 = np.roll(poly[:, 0], -1)[None, :]; y2 = np.roll(poly[:, 1], -1)[None, :]
    cond = (y1 > y) != (y2 > y)
    dy = np.where(y2 - y1 == 0, 1.0, y2 - y1)
    xint = (x2 - x1) * (y - y1) / dy + x1
    return ((cond & (x < xint)).sum(1) % 2) == 1


def seg_cross(p1, p2, A, B, eps=1e-12):
    """does open segment p1p2 properly cross any segment A[i]B[i] (shared endpoints ignored)?"""
    def orient(a, b, c):
        return (b[..., 0] - a[..., 0]) * (c[..., 1] - a[..., 1]) - (b[..., 1] - a[..., 1]) * (c[..., 0] - a[..., 0])
    p1 = np.asarray(p1)[None, :]; p2 = np.asarray(p2)[None, :]
    o1 = orient(p1, p2, A); o2 = orient(p1, p2, B); o3 = orient(A, B, p1); o4 = orient(A, B, p2)
    return bool(np.any((o1 * o2 < -eps) & (o3 * o4 < -eps)))


class PG:
    def __init__(self, pos, edges, w=None, seed=0):
        self.pos = np.asarray(pos, float)
        n = self.n = len(self.pos)
        adj = [[] for _ in range(n)]
        self.eid = {}
        self.ends = []
        for a, b in edges:
            assert a != b
            k = (a, b) if a < b else (b, a)
            assert k not in self.eid, ('multi-edge', k)
            self.eid[k] = len(self.ends); self.ends.append(k)
            adj[a].append(b); adj[b].append(a)
        self.m = len(self.ends)
        P = self.pos
        self.rot = []
        for v in range(n):
            x, y = P[v]
            self.rot.append(sorted(adj[v], key=lambda u: math.atan2(P[u][1] - y, P[u][0] - x)))
        self.idx = [{u: i for i, u in enumerate(r)} for r in self.rot]
        self.deg = np.array([len(r) for r in self.rot])
        assert (self.deg > 0).all(), 'isolated vertex'
        self.cbase = np.concatenate([[0], np.cumsum(self.deg)])
        self.nc = int(self.cbase[-1])
        self.cv = np.repeat(np.arange(n), self.deg)
        self.cj = np.concatenate([np.arange(d) for d in self.deg])
        self.eprev = np.empty(self.nc, int); self.enext = np.empty(self.nc, int)
        for v in range(n):
            r = self.rot[v]; d = len(r)
            for j in range(d):
                c = self.cbase[v] + j
                self.eprev[c] = self.e(v, r[j - 1]); self.enext[c] = self.e(v, r[j])
        # faces
        self.cface = np.full(self.nc, -1)
        self.fcorners = []
        for c0 in range(self.nc):
            if self.cface[c0] >= 0:
                continue
            f = len(self.fcorners); lst = []
            x, k = int(self.cv[c0]), int(self.cj[c0])
            while True:
                cc = self.cbase[x] + k
                if self.cface[cc] >= 0:
                    break
                self.cface[cc] = f; lst.append(cc)
                y = self.rot[x][(k - 1) % self.deg[x]]
                k = self.idx[y][x]; x = y
            self.fcorners.append(lst)
        self.nf = len(self.fcorners)
        G = nx.Graph(); G.add_nodes_from(range(n)); G.add_edges_from(self.ends)
        self.G = G
        assert nx.is_connected(G), 'G disconnected'
        assert n - self.m + self.nf == 2, ('Euler fails: not a plane straight-line drawing?', n, self.m, self.nf)
        # radial rotation at faces: orientation check by counting faces of R
        self.frot = [list(l) for l in self.fcorners]
        allg = np.ones(self.nc, bool)
        faces = self.gamma_faces(allg, check_only_count=True)
        if faces != self.m:
            self.frot = [l[::-1] for l in self.fcorners]
            faces = self.gamma_faces(allg, check_only_count=True)
        assert faces == self.m, ('radial graph faces', faces, self.m)
        self.fpos = {}
        rng = np.random.default_rng(seed)
        self.w = {}
        for (a, b) in self.ends:
            self.w[(a, b)] = int(rng.integers(1, 20)); self.w[(b, a)] = int(rng.integers(1, 20))
        if w:
            self.w.update(w)
        self.ang = {}
        for v in range(n):
            for u in self.rot[v]:
                self.ang[(v, u)] = math.atan2(P[u][1] - P[v][1], P[u][0] - P[v][0])

    def e(self, a, b):
        return self.eid[(a, b) if a < b else (b, a)]

    def angle(self, a, b):
        P = self.pos
        return math.atan2(P[b][1] - P[a][1], P[b][0] - P[a][0])

    # ---------------- faces of a corner set Gamma (R-subgraph) ----------------
    def gamma_faces(self, gmask, check_only_count=False):
        n = self.n
        rv = {}; pv = {}
        gl = np.nonzero(gmask)[0]
        for c in gl:
            v = int(self.cv[c])
            rv.setdefault(v, []).append(int(c))
        for v in rv:
            rv[v].sort()
            for p, c in enumerate(rv[v]):
                pv[c] = p
        rf = {}; pf = {}
        for f, lst in enumerate(self.frot):
            l2 = [c for c in lst if gmask[c]]
            if l2:
                rf[f] = l2
                for p, c in enumerate(l2):
                    pf[c] = p
        seen = set(); faces = []
        for c0 in gl:
            for d0 in (0, 1):
                if (int(c0), d0) in seen:
                    continue
                walk = []
                c, d = int(c0), d0
                while (c, d) not in seen:
                    seen.add((c, d))
                    if d == 0:     # G-vertex -> face: arrive at face f
                        f = int(self.cface[c]); L = rf[f]; c2 = L[pf[c] - 1]; d2 = 1
                    else:          # face -> G-vertex v
                        v = int(self.cv[c]); L = rv[v]; c2 = L[pv[c] - 1]; d2 = 0
                        walk.append((v, c2))     # visit of v: leave via c2 = opening corner
                    c, d = c2, d2
                faces.append(walk)
        if check_only_count:
            return len(faces)
        return faces, rv


# ---------------------------------------------------------------- helpers
def bfs_far(adj, s):
    dist = {s: 0}; dq = collections.deque([s])
    while dq:
        x = dq.popleft()
        for y in adj[x]:
            if y not in dist:
                dist[y] = dist[x] + 1; dq.append(y)
    far = max(dist, key=dist.get)
    return far, dist[far], dist


def tree_diam(adj):
    s = next(iter(adj))
    a, _, _ = bfs_far(adj, s)
    _, d, _ = bfs_far(adj, a)
    return d


def monge_check(M, tol=1e-9):
    """max violation of (M), all 4 orientations, over 4-subsets in index (cyclic) order."""
    k = M.shape[0]
    worst = 0.0; cnt = 0
    if k < 4:
        return 0.0, 0
    for a in range(k - 3):
        c3 = np.array(list(itertools.combinations(range(a + 1, k), 3)), dtype=np.int64)
        b, c, d = c3[:, 0], c3[:, 1], c3[:, 2]
        # (u,v) in {(a,c),(c,a)}, (w,z) in {(b,d),(d,b)}: d(u,z)+d(w,v) <= d(u,v)+d(w,z)
        v1 = M[a, d] + M[b, c] - M[a, c] - M[b, d]
        v2 = M[a, b] + M[d, c] - M[a, c] - M[d, b]
        v3 = M[c, d] + M[b, a] - M[c, a] - M[b, d]
        v4 = M[c, b] + M[d, a] - M[c, a] - M[d, b]
        mx = max(v1.max(), v2.max(), v3.max(), v4.max())
        worst = max(worst, float(mx)); cnt += 4 * len(b)
    return worst, cnt


def sp_matrix(nodes, arcs, sources):
    idx = {x: i for i, x in enumerate(nodes)}
    if arcs:
        r = [idx[u] for (u, v) in arcs]; c = [idx[v] for (u, v) in arcs]
        w = [max(x, 1e-15) for x in arcs.values()]
        A = coo_matrix((w, (r, c)), shape=(len(nodes), len(nodes))).tocsr()
    else:
        A = coo_matrix((len(nodes), len(nodes))).tocsr()
    return dijkstra(A, directed=True, indices=[idx[s] for s in sources])


def add_arc(arcs, u, v, w):
    if u == v:
        return
    if (u, v) not in arcs or arcs[(u, v)] > w:
        arcs[(u, v)] = w
