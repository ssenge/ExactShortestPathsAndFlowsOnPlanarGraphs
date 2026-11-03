"""Minimal rotation-system toolkit for plane multigraphs.

rot[v]  : list of edge ids in counter-clockwise order around v
edges[e]: (a, b) endpoints (no self loops)
Face traversal: entering v via edge e, leave via the edge preceding e in ccw order.
Corner (v, j): gap between rot[v][j-1] and rot[v][j]; it lies on the face of the
outgoing dart (v, rot[v][j-1]).
"""
import math, itertools, collections


class Plane:
    def __init__(self):
        self.rot = {}
        self.edges = {}
        self.w = {}          # (eid, 0) weight of edges[e][0]->edges[e][1]; (eid,1) reverse
        self._next = 0

    def copy(self):
        P = Plane()
        P.rot = {v: list(r) for v, r in self.rot.items()}
        P.edges = dict(self.edges)
        P.w = dict(self.w)
        P._next = self._next
        return P

    def new_eid(self):
        self._next += 1
        return self._next

    def other(self, e, v):
        a, b = self.edges[e]
        return b if a == v else a

    # ---------- construction from straight-line coordinates ----------
    @staticmethod
    def from_coords(pos, edge_list):
        P = Plane()
        inc = collections.defaultdict(list)
        for (a, b) in edge_list:
            e = P.new_eid()
            P.edges[e] = (a, b)
            inc[a].append(e)
            inc[b].append(e)
        for v in pos:
            x, y = pos[v]
            def ang(e, v=v, x=x, y=y):
                u = P.other(e, v)
                ux, uy = pos[u]
                return math.atan2(uy - y, ux - x)
            P.rot[v] = sorted(inc[v], key=ang)
        return P

    def induced(self, keep):
        keep = set(keep)
        P = Plane()
        P._next = self._next
        for e, (a, b) in self.edges.items():
            if a in keep and b in keep:
                P.edges[e] = (a, b)
        for v in keep:
            P.rot[v] = [e for e in self.rot[v] if e in P.edges]
        P.w = {k: x for k, x in self.w.items() if k[0] in P.edges}
        return P

    # ---------- faces ----------
    def faces(self):
        seen = {}
        faces = []
        for v, r in self.rot.items():
            for e in r:
                if (v, e) in seen:
                    continue
                fid = len(faces)
                cyc = []
                d = (v, e)
                while d not in seen:
                    seen[d] = fid
                    cyc.append(d)
                    x, ex = d
                    y = self.other(ex, x)
                    j = self.rot[y].index(ex)
                    d = (y, self.rot[y][(j - 1) % len(self.rot[y])])
                faces.append(cyc)
        return faces, seen

    def face_vertices(self):
        faces, _ = self.faces()
        return [set(v for v, _ in f) for f in faces]

    def corner_face(self, dart_face, v, j):
        r = self.rot[v]
        return dart_face[(v, r[(j - 1) % len(r)])]

    def corners_on_face(self, dart_face, v, fid):
        r = self.rot[v]
        return [j for j in range(len(r)) if dart_face[(v, r[(j - 1) % len(r)])] == fid]

    def components(self):
        adj = collections.defaultdict(set)
        for e, (a, b) in self.edges.items():
            adj[a].add(b); adj[b].add(a)
        seen, c = set(), 0
        for v in self.rot:
            if v in seen:
                continue
            c += 1
            st = [v]; seen.add(v)
            while st:
                x = st.pop()
                for y in adj[x]:
                    if y not in seen:
                        seen.add(y); st.append(y)
        return c

    def euler(self):
        F = len(self.faces()[0]) + sum(1 for v, r in self.rot.items() if not r)
        V, E = len(self.rot), len(self.edges)
        return V, E, F

    # ---------- cut open a simple path ----------
    def cut_path(self, path, c0, ck, tag):
        """Cut along path=[v0..vk] (k>=1). c0 / ck are corner gap indices at v0 / vk
        (None = endpoint not split). Returns new Plane and map v -> (L copy, R copy)."""
        P = self.copy()
        k = len(path) - 1
        pe = []
        for i in range(k):
            a, b = path[i], path[i + 1]
            cand = [e for e in P.rot[a] if P.other(e, a) == b]
            assert len(cand) >= 1, (a, b)
            pe.append(cand[0])
        copies = {}
        newrot = {}
        newedge_L = {e: P.new_eid() for e in pe}
        newedge_R = {e: P.new_eid() for e in pe}
        reassign = {}  # (eid, oldvertex) -> new vertex
        for i, v in enumerate(path):
            r = P.rot[v]
            n = len(r)
            L, R = (v, tag, 'L'), (v, tag, 'R')
            if 0 < i < k:
                a = r.index(pe[i - 1]); b = r.index(pe[i])
                left = [r[(b + t) % n] for t in range(1, (a - b) % n)]
                right = [r[(a + t) % n] for t in range(1, (b - a) % n)]
                newrot[L] = [newedge_L[pe[i]]] + left + [newedge_L[pe[i - 1]]]
                newrot[R] = [newedge_R[pe[i - 1]]] + right + [newedge_R[pe[i]]]
            elif i == 0:
                b = r.index(pe[0])
                if c0 is None:
                    newrot[L] = [newedge_L[pe[0]]] + [r[(b + t) % n] for t in range(1, n)] + [newedge_R[pe[0]]]
                    R = L
                else:
                    # left = ccw from b up to corner (positions b+1 .. c0-1); right = c0 .. b-1
                    left = []
                    t = (b + 1) % n
                    while t != c0 % n:
                        left.append(r[t]); t = (t + 1) % n
                    right = []
                    t = c0 % n
                    while t != b:
                        right.append(r[t]); t = (t + 1) % n
                    newrot[L] = [newedge_L[pe[0]]] + left
                    newrot[R] = right + [newedge_R[pe[0]]]
            else:
                a = r.index(pe[k - 1])
                if ck is None:
                    newrot[L] = [newedge_R[pe[k - 1]]] + [r[(a + t) % n] for t in range(1, n)] + [newedge_L[pe[k - 1]]]
                    R = L
                else:
                    left = []
                    t = ck % n
                    while t != a:
                        left.append(r[t]); t = (t + 1) % n
                    right = []
                    t = (a + 1) % n
                    while t != ck % n:
                        right.append(r[t]); t = (t + 1) % n
                    newrot[L] = left + [newedge_L[pe[k - 1]]]
                    newrot[R] = [newedge_R[pe[k - 1]]] + right
            copies[v] = (L, R)
            for e in newrot[L]:
                if e in P.edges:
                    reassign[(e, v)] = L
            if R != L:
                for e in newrot[R]:
                    if e in P.edges:
                        reassign[(e, v)] = R
        # rebuild
        for (e, v), nv in reassign.items():
            a, b = P.edges[e]
            P.edges[e] = (nv if a == v else a, nv if b == v else b)
        for i, e in enumerate(pe):
            a, b = path[i], path[i + 1]
            P.edges[newedge_L[e]] = (copies[a][0], copies[b][0])
            P.edges[newedge_R[e]] = (copies[a][1], copies[b][1])
            fwd = 0 if self.edges[e][0] == a else 1   # direction index of a->b in old edge
            for ne in (newedge_L[e], newedge_R[e]):
                if (e, fwd) in self.w:
                    P.w[(ne, 0)] = self.w[(e, fwd)]
                if (e, 1 - fwd) in self.w:
                    P.w[(ne, 1)] = self.w[(e, 1 - fwd)]
                P.w.pop((e, 0), None); P.w.pop((e, 1), None)
            del P.edges[e]
        for v in path:
            del P.rot[v]
        P.rot.update(newrot)
        return P, copies

    # ---------- distances ----------
    def digraph(self, default=None):
        import networkx as nx
        D = nx.MultiDiGraph()
        D.add_nodes_from(self.rot)
        for e, (a, b) in self.edges.items():
            for di, (t, h) in enumerate(((a, b), (b, a))):
                wt = self.w.get((e, di), default)
                if wt is not None:
                    D.add_edge(t, h, weight=wt)
        return D


def monge_lp(delta, order, fix_alpha=None, objective=None):
    """LP of Lemma R5 with variable alpha (minimised) unless fix_alpha given.
    delta: dict (a,b)->value for a!=b. order: list of terminals (cyclic).
    Returns (status, alpha, d)."""
    import numpy as np
    from scipy.optimize import linprog
    T = list(order)
    pairs = [(a, b) for a in T for b in T if a != b]
    idx = {p: i for i, p in enumerate(pairs)}
    nv = len(pairs) + 1
    A, bvec = [], []
    def row():
        return np.zeros(nv)
    n = len(T)
    # Monge (13) for all cyclic 4-subsequences <ti,tj,tk,tl>: d(ti,tk)+d(tj,tl) >= d(ti,tl)+d(tj,tk)
    for comb in itertools.combinations(range(n), 4):
        for rotn in range(4):
            i, j, k, l = [T[comb[(rotn + s) % 4]] for s in range(4)]
            r = row()
            r[idx[(i, l)]] += 1; r[idx[(j, k)]] += 1
            r[idx[(i, k)]] -= 1; r[idx[(j, l)]] -= 1
            A.append(r); bvec.append(0)
    # triangle
    for a in T:
        for b in T:
            for c in T:
                if len({a, b, c}) == 3:
                    r = row(); r[idx[(a, c)]] = 1; r[idx[(a, b)]] -= 1; r[idx[(b, c)]] -= 1
                    A.append(r); bvec.append(0)
    # bounds delta <= d <= alpha*delta
    for p in pairs:
        r = row(); r[idx[p]] = -1; A.append(r); bvec.append(-delta[p])
        r = row(); r[idx[p]] = 1
        if fix_alpha is None:
            r[-1] = -delta[p]; A.append(r); bvec.append(0)
        else:
            A.append(r); bvec.append(fix_alpha * delta[p])
    c = np.zeros(nv)
    if objective is None:
        c[-1] = 1
    else:
        for p, coef in objective.items():
            c[idx[p]] = coef
    bounds = [(0, None)] * len(pairs) + [((1, None) if fix_alpha is None else (0, 0))]
    res = linprog(c, A_ub=np.array(A), b_ub=np.array(bvec), bounds=bounds, method='highs')
    if res.status != 0:
        return res.status, None, None
    d = {p: res.x[idx[p]] for p in pairs}
    return 0, (res.x[-1] if fix_alpha is None else fix_alpha), d


def all_cyclic_orders(T):
    T = list(T)
    first = T[0]
    for perm in itertools.permutations(T[1:]):
        yield [first] + list(perm)
