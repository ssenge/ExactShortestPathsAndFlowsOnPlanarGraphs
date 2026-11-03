"""Exact maximum flow by scaling over the portals of one BFS path: logic of notes/MAXFLOW.md, centrally.

An oracle for portal distances is modelled by true distances plus worst-case noise in [d, (1+eps)d].
No rounds, no labels, no hierarchy here. Run: python -I mf.py <seed> <seconds>, or ctl <seed> <seconds>.
Needs networkx for embeddings and the planarity check.
"""
import collections, heapq, json, os, random, sys, time
import networkx as nx

EPS_NUM, EPS_DEN = 1, 12      # eps = 1/12
K = 9                         # K >= (1+eps)(1+3eps)/(2 eps) = 8.125


def embed(V, E):
    g = nx.Graph()
    g.add_nodes_from(V)
    g.add_edges_from(E)
    ok, emb = nx.check_planarity(g)
    assert ok
    face, nf = {}, 0
    for u, v in emb.edges():
        if (u, v) not in face:
            for a, b in walk_face(emb, u, v):
                face[a, b] = nf
            nf += 1
    return g, face, nf, emb


def walk_face(emb, u, v):
    out, a, b = [], u, v
    while True:
        out.append((a, b))
        a, b = emb.next_face_half_edge(a, b)
        if (a, b) == (u, v):
            return out


class Inst:
    """rgt(d) is the face of the half-edge d, lft(d) = rgt(rev d)."""

    def __init__(self, V, E, cap, s, t):
        self.g, self.rgt, self.nf, self.emb = embed(V, E)
        self.cap, self.s, self.t, self.V = cap, s, t, V
        self.darts = list(self.rgt)
        self.R = bfs_path(self.g, s, t)
        self.Rset = set(self.R)
        self.Rrev = {(b, a) for a, b in self.R}
        self.portals = sorted({self.rgt[d] for d in self.R} | {self.rgt[b, a] for a, b in self.R})

    def lft(self, d):
        return self.rgt[d[1], d[0]]

    def on_R(self, d):
        return d in self.Rset or d in self.Rrev

    def sign(self, d):
        return 1 if d in self.Rset else (-1 if d in self.Rrev else 0)


def bfs_path(g, s, t):
    par, q = {s: None}, collections.deque([s])
    while q:
        x = q.popleft()
        for y in sorted(g[x]):
            if y not in par:
                par[y] = x
                q.append(y)
    p, x = [], t
    while par[x] is not None:
        p.append((par[x], x))
        x = par[x]
    return p[::-1]


def dijkstra(nf, adj, offs):
    dist, pq = dict(offs), [(d, f) for f, d in offs.items()]
    heapq.heapify(pq)
    while pq:
        d, x = heapq.heappop(pq)
        if d > dist[x]:
            continue
        for y, l in adj[x]:
            assert l >= 0
            if y not in dist or d + l < dist[y]:
                dist[y] = d + l
                heapq.heappush(pq, (d + l, y))
    return dist


def gamma_adj(I, length):
    """The dual without the darts of R; dart d gives an arc rgt(d) -> lft(d)."""
    adj = collections.defaultdict(list)
    for d in I.darts:
        if not I.on_R(d):
            adj[I.rgt[d]].append((I.lft(d), length(d)))
    return adj


def noise(rng, d, mode):
    hi = d + d * EPS_NUM // EPS_DEN
    if mode == 'lo':
        return d
    if mode == 'hi':
        return hi
    if mode == 'two':
        return rng.choice([d, hi])
    return rng.randint(d, hi)


def portal_bounds(I, C, rng, mode, st, wrong=None):
    """b(u,v) = floor(d~(u,v) / ((1+eps) 2N)): the bound (B) of the note."""
    N = I.nf + 1
    adj = gamma_adj(I, lambda d: 2 * N * K * C[d] + 1)
    adjC = gamma_adj(I, lambda d: C[d])
    b = {}
    for u in I.portals:
        dl = dijkstra(I.nf, adj, {u: 0})
        dc = dijkstra(I.nf, adjC, {u: 0})
        for v in I.portals:
            assert v in dl, 'Gamma not strongly connected'
            dt = noise(rng, dl[v], mode)
            if wrong == 'no_division':
                b[u, v] = dt // (2 * N)
            else:
                b[u, v] = dt * EPS_DEN // ((EPS_DEN + EPS_NUM) * 2 * N)
            st['chk.B_upper'] += 1
            if b[u, v] > K * dc[v]:
                st['FAIL.B_upper'] += 1
            st['chk.B_lower'] += 1
            if b[u, v] * (EPS_DEN + 3 * EPS_NUM) < K * dc[v] * EPS_DEN:
                st['FAIL.B_lower'] += 1
    return b


def solve_system(I, C, b, J):
    """Bellman-Ford on portals: psi(v) - psi(u) <= bound. Returns psi, or None."""
    arcs = [(u, v, w) for (u, v), w in b.items() if u != v]
    for d in I.R + [(y, x) for x, y in I.R]:
        arcs.append((I.rgt[d], I.lft(d), K * C[d] - I.sign(d) * J))
    psi = {p: 0 for p in I.portals}
    for it in range(len(psi) + 1):
        ch = False
        for u, v, w in arcs:
            if u == v:
                if w < 0:
                    return None
            elif psi[u] + w < psi[v]:
                psi[v] = psi[u] + w
                ch = True
        if not ch:
            return psi
    return None


def largest_J(I, C, b, st):
    lo, hi = 0, K * sum(C[d] for d in I.darts) + 1
    assert solve_system(I, C, b, 0) is not None
    while hi - lo > 1:
        m = (lo + hi) // 2
        if solve_system(I, C, b, m) is not None:
            lo = m
        else:
            hi = m
    return lo, solve_system(I, C, b, lo)


def step(I, C, rng, mode, st, wrong=None):
    """One approximation step on integer capacities C: returns J and face potentials, units 1/K."""
    b = portal_bounds(I, C, rng, mode, st, wrong)
    J, psi = largest_J(I, C, b, st)
    base = -min(psi.values())
    offs = {p: x + base for p, x in psi.items()}
    if wrong == 'one_source':
        offs = dict([min(offs.items())])
    phi = dijkstra(I.nf, gamma_adj(I, lambda d: K * C[d]), offs)
    for p, x in psi.items():
        st['chk.fill_keeps_portals'] += 1
        if phi[p] != x + base:
            st['FAIL.fill_keeps_portals'] += 1
    return J, phi


def run(I, rng, mode, st, wrong=None, iters=None, exact=True):
    n, N = len(I.V), I.nf + 1
    U = max(I.cap.values()) or 1
    C = dict(I.cap)
    if not I.R:
        return 0, {d: 0 for d in I.darts}
    T = iters if iters is not None else rounds_needed(N, n * U)
    scale, beta, Phi = 1, 0, collections.defaultdict(int)
    for it in range(T):
        lam = maxflow(I, C)
        J, phi = step(I, C, rng, mode, st, wrong)
        st['chk.J_bound'] += 1
        if J * (EPS_DEN + 3 * EPS_NUM) < (K * lam * EPS_DEN) - (EPS_DEN + 3 * EPS_NUM):
            st['FAIL.J_bound'] += 1
        st['chk.J_le_lambda'] += 1
        if J > K * lam:
            st['FAIL.J_le_lambda'] += 1
        new = {}
        for d in I.darts:
            g = phi[I.lft(d)] - phi[I.rgt[d]] + I.sign(d) * J
            new[d] = K * C[d] - g
            st['chk.residual_nonneg'] += 1
            if new[d] < 0:
                st['FAIL.residual_nonneg'] += 1
                if wrong:
                    return J, None
        C = new
        scale *= K
        beta = beta * K + J
        for f in range(I.nf):
            Phi[f] = Phi[f] * K + phi[f]
        st['iters'] += 1
    # exact: beta/scale is within 1/N of the integer lambda
    lam = -((-beta) // scale)
    p = lam * scale - beta
    if p:
        st['runs_p_positive'] += 1
    st['chk.gap'] += 1
    if p * N >= scale:
        st['FAIL.gap'] += 1
        if not exact:
            return beta, None
    st['max_log_scale'] = max(st['max_log_scale'], bitlen(scale))
    adj = collections.defaultdict(list)
    for d in I.darts:
        r = scale * (I.cap[d] - I.sign(d) * lam) + Phi[I.rgt[d]] - Phi[I.lft(d)] + (0 if wrong == 'no_p' else p)
        st['chk.reduced_nonneg'] += 1
        if r < 0:
            st['FAIL.reduced_nonneg'] += 1
            if wrong:
                return lam, None
            r = 0
        adj[I.rgt[d]].append((I.lft(d), r))
    dr = dijkstra(I.nf, adj, {0: 0})
    psi = {g: (dr[g] - Phi[0] + Phi[g]) // scale for g in range(I.nf)}
    f = {}
    for d in I.darts:
        f[d] = psi[I.lft(d)] - psi[I.rgt[d]] + I.sign(d) * lam
    return lam, f


def bitlen(x):
    return max(1, int(x).bit_length())


def rounds_needed(N, lam_max):
    """Least T with 5^T >= N (lam_max + 1): then p N < scale, by the bound on p in the note."""
    T = 0
    while 5 ** T < N * (lam_max + 1):
        T += 1
    return T


def maxflow(I, C):
    """Independent Dinic on the primal, from the capacities of the darts."""
    res = collections.defaultdict(int)
    adj = collections.defaultdict(set)
    big = sum(C.values()) + 1
    for (u, v), c in C.items():
        res[u, v] += c
        adj[u].add(v)
        adj[v].add(u)
    total = 0
    while True:
        lev, q = {I.s: 0}, collections.deque([I.s])
        while q:
            x = q.popleft()
            for y in adj[x]:
                if y not in lev and res[x, y] > 0:
                    lev[y] = lev[x] + 1
                    q.append(y)
        if I.t not in lev:
            return total
        it = {x: iter(sorted(adj[x])) for x in adj}

        def dfs(x, push):
            if x == I.t:
                return push
            for y in it[x]:
                if res[x, y] > 0 and lev.get(y) == lev[x] + 1:
                    g = dfs(y, min(push, res[x, y]))
                    if g:
                        res[x, y] -= g
                        res[y, x] += g
                        return g
            return 0

        while True:
            g = dfs(I.s, big)
            if not g:
                break
            total += g


def check_flow(I, f, val, st):
    st['chk.feasible'] += 1
    if any(f[d] > I.cap[d] for d in I.darts):
        st['FAIL.feasible'] += 1
    st['chk.antisym'] += 1
    if any(f[a, b] != -f[b, a] for a, b in I.darts):
        st['FAIL.antisym'] += 1
    net = collections.Counter()
    for (a, b) in I.darts:
        net[a] += f[a, b]
    st['chk.conservation'] += 1
    for v in I.V:
        want = val if v == I.s else (-val if v == I.t else 0)
        if net[v] != want:
            st['FAIL.conservation'] += 1
            break


# ------------------------------------------------------------------ instances
def largest(V, E):
    g = nx.Graph()
    g.add_nodes_from(V)
    g.add_edges_from(E)
    c = max(nx.connected_components(g), key=len)
    idx = {v: i for i, v in enumerate(sorted(c))}
    return set(idx.values()), sorted({(min(idx[a], idx[b]), max(idx[a], idx[b])) for a, b in E if a in c and b in c})


def graph(rng, big):
    k = rng.randrange(7)
    m = 12 if big else 7
    if k == 0:
        a, b, drop = rng.randrange(2, m), rng.randrange(2, m), rng.choice([0, 0.1, 0.3])
        E = []
        for i in range(a):
            for j in range(b):
                x = i * b + j
                if j + 1 < b and rng.random() >= drop:
                    E.append((x, x + 1))
                if i + 1 < a and rng.random() >= drop:
                    E.append((x, x + b))
        return largest(set(range(a * b)), E)
    if k == 1:
        a, b = rng.randrange(2, m), rng.randrange(3, m)   # cylinder: long separating cycles
        E = []
        for i in range(a):
            for j in range(b):
                x = i * b + j
                E.append((x, i * b + (j + 1) % b))
                if i + 1 < a:
                    E.append((x, x + b))
                    E.append((x, (i + 1) * b + (j + 1) % b))
        return largest(set(range(a * b)), E)
    if k == 2:
        n = rng.randrange(4, 8 * m)
        faces, E = [(0, 1, 2), (0, 1, 2)], {(0, 1), (0, 2), (1, 2)}
        for v in range(3, n):
            i = rng.randrange(len(faces))
            x, y, z = faces[i]
            faces[i] = (x, y, v)
            faces += [(y, z, v), (x, z, v)]
            E |= {(x, v), (y, v), (z, v)}
        drop = rng.choice([0, 0.2, 0.5])
        return largest(set(range(n)), [e for e in sorted(E) if rng.random() >= drop])
    if k == 3:
        n = rng.randrange(2, 6 * m)
        return set(range(n)), [(rng.randrange(max(0, v - 3), v), v) for v in range(1, n)]
    if k == 4:
        n = rng.randrange(4, 5 * m)
        return set(range(n)), [(0, v) for v in range(1, n)] + [(v, v + 1) for v in range(1, n - 1)] + [(1, n - 1)]
    if k == 5:
        n = rng.randrange(3, 5 * m)
        return set(range(n)), [(v, v + 1) for v in range(n - 1)] + [(0, n - 1)]
    a = rng.randrange(2, m)
    E = []
    for i in range(a):          # concentric rings with spokes: s in the middle, t outside
        for j in range(6):
            x = 1 + i * 6 + j
            E.append((x, 1 + i * 6 + (j + 1) % 6))
            if i + 1 < a and rng.random() < 0.7:
                E.append((x, x + 6))
            if i == 0:
                E.append((0, x))
    return largest(set(range(1 + a * 6)), E)


def capacities(V, E, rng):
    mode = rng.choice(['sym', 'sym', 'dir', 'oneway', 'zero', 'huge', 'unit'])
    U = rng.choice([1, 2, 5, 30, 1000])
    cap = {}
    for u, v in E:
        if mode == 'sym':
            cap[u, v] = cap[v, u] = rng.randrange(1, U + 1)
        elif mode == 'dir':
            cap[u, v], cap[v, u] = rng.randrange(0, U + 1), rng.randrange(0, U + 1)
        elif mode == 'oneway':
            a, b = (u, v) if rng.random() < 0.5 else (v, u)
            cap[a, b], cap[b, a] = rng.randrange(1, U + 1), 0
        elif mode == 'zero':
            cap[u, v] = cap[v, u] = rng.choice([0, 0, rng.randrange(0, U + 1)])
        elif mode == 'huge':
            cap[u, v] = cap[v, u] = rng.randrange(10 ** 5, 10 ** 6)
        else:
            cap[u, v] = cap[v, u] = 1
    return mode, cap


def far(V, E, rng):
    g = nx.Graph(E)
    g.add_nodes_from(V)
    s = rng.choice(sorted(V))
    d = nx.single_source_shortest_path_length(g, s)
    t = max(d, key=lambda x: (d[x], rng.random())) if rng.random() < 0.7 else rng.choice(sorted(V))
    return s, t


def lane(seed, secs, big):
    rng = random.Random(seed)
    st = collections.Counter()
    t0 = time.time()
    while time.time() - t0 < secs:
        V, E = graph(rng, big)
        if len(V) < 2 or not E:
            continue
        s, t = far(V, E, rng)
        if s == t:
            continue
        mode, cap = capacities(V, E, rng)
        I = Inst(V, E, cap, s, t)
        nm = rng.choice(['rand', 'two', 'hi', 'lo'])
        lam, f = run(I, rng, nm, st)
        st['runs'] += 1
        st['runs|' + mode] += 1
        st['chk.value'] += 1
        if lam != maxflow(I, cap):
            st['FAIL.value'] += 1
        check_flow(I, f, lam, st)
        st['max_portals'] = max(st['max_portals'], len(I.portals))
        st['max_R'] = max(st['max_R'], len(I.R))
        st['max_lambda'] = max(st['max_lambda'], lam)
    return st


def controls(seed, secs):
    out = {}
    for name, kw in [('no_division', dict(wrong='no_division')), ('one_source', dict(wrong='one_source')),
                     ('no_p', dict(wrong='no_p')), ('too_few_iters', dict(iters=1, exact=False))]:
        rng = random.Random(seed)
        st = collections.Counter()
        t0 = time.time()
        while time.time() - t0 < secs:
            V, E = graph(rng, False)
            if len(V) < 2 or not E:
                continue
            s, t = far(V, E, rng)
            if s == t:
                continue
            mode, cap = capacities(V, E, rng)
            I = Inst(V, E, cap, s, t)
            nm = 'hi' if name == 'no_division' else rng.choice(['rand', 'two', 'lo'])
            lam, f = run(I, rng, nm, st, **kw)
            st['runs'] += 1
            if f is not None:
                if lam != maxflow(I, cap):
                    st['FAIL.value'] += 1
                check_flow(I, f, lam, st)
        out[name] = {k: v for k, v in st.items() if k.startswith('FAIL') or k.startswith('runs')}
    return out


if __name__ == '__main__':
    sys.setrecursionlimit(100000)
    if sys.argv[1] == 'ctl':
        print(json.dumps(controls(int(sys.argv[2]), float(sys.argv[3]))))
    else:
        print(json.dumps(dict(lane(int(sys.argv[1]), float(sys.argv[2]), len(sys.argv) > 3)), sort_keys=True))
