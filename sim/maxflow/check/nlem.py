"""Independent implementation of Lemma N and the Section 6 pipeline of MAXFLOW.md.
Written from the note only. Rotation = ccw neighbour lists. Half-edge rotation of N is derived by hand.
"""
import collections, heapq, itertools, math, random, sys
from fractions import Fraction as Fr
import networkx as nx

K = 9
EPS = Fr(1, 12)


class G0:
    """plane graph from ccw rotation rot[v] = list of neighbours"""

    def __init__(self, rot):
        self.rot = rot
        self.pos = {v: {x: i for i, x in enumerate(r)} for v, r in rot.items()}
        self.darts = [(v, x) for v, r in rot.items() for x in r]
        self.rgt = {}
        nf = 0
        for d in self.darts:
            if d in self.rgt:
                continue
            a = d
            while a not in self.rgt:
                self.rgt[a] = nf
                a = self.nxt(a)
            nf += 1
        self.nf = nf
        self.m = len(self.darts) // 2
        self.n = len(rot)

    def ccw(self, v, x):
        r = self.rot[v]
        return r[(self.pos[v][x] + 1) % len(r)]

    def cw(self, v, x):
        r = self.rot[v]
        return r[(self.pos[v][x] - 1) % len(r)]

    def nxt(self, d):
        """next dart on the boundary walk of rgt(d): at the head w, the ccw successor of (w, tail)"""
        u, w = d
        return (w, self.ccw(w, u))

    def lft(self, d):
        return self.rgt[(d[1], d[0])]

    def genus0(self):
        return self.n - self.m + self.nf == 2


class NetN:
    """N: corner nodes ('c',d), star nodes ('s',v,bank). edges have ids, parallel kept, loops dropped."""

    def __init__(self, g, R, ec_end='larger', rng=None):
        self.g = g
        self.R = R                          # list of darts from s to t
        Rv = [R[0][0]] + [b for a, b in R]
        self.Rv = Rv
        self.Rd = set(R) | {(b, a) for a, b in R}
        self.sigma = {}
        for d in g.darts:
            self.sigma[d] = 1 if d in set(R) else (-1 if (d[1], d[0]) in set(R) else 0)
        inter = {}
        for i in range(1, len(Rv) - 1):
            inter[Rv[i]] = (Rv[i - 1], Rv[i + 1])
        self.bank_of = {}
        self.stars = {}
        for v in g.rot:
            if v in inter:
                p, n = inter[v]
                # right bank: ccw from p to n; corner (v,x) = angle (cw x, x)
                right, x = [], p
                while x != n:
                    x = g.ccw(v, x)
                    right.append(('c', (v, x)))
                left, x = [], n
                while x != p:
                    x = g.ccw(v, x)
                    left.append(('c', (v, x)))
                for bank, cs in (('R', right), ('L', left)):
                    for c in cs:
                        self.bank_of[c] = (v, bank)
                    if len(cs) >= 2:
                        self.stars['s', v, bank] = cs
            else:
                cs, x = [], g.rot[v][0]
                for _ in g.rot[v]:
                    x = g.ccw(v, x)
                    cs.append(('c', (v, x)))
                for c in cs:
                    self.bank_of[c] = (v, '')
                if len(cs) >= 2:
                    self.stars['s', v, ''] = cs
        self.nodes = [('c', d) for d in g.darts] + list(self.stars)
        self.E = []                         # (u,v,kind,data)
        self.he = collections.defaultdict(dict)  # node -> slot -> edge id
        self.ec_at = {}
        done = set()
        for d in g.darts:
            e = frozenset(d)
            if e in done:
                continue
            done.add(e)
            if d in self.Rd:
                continue
            a, b = d
            if ec_end == 'larger':
                at = max(a, b, key=repr)
            elif ec_end == 'smaller':
                at = min(a, b, key=repr)
            else:
                at = rng.choice([a, b])
            self.ec_at[e] = at
        self._rot()

    def _rot(self):
        g = self.g
        eid = {}

        def add(u, v, kind, data):
            i = len(self.E)
            self.E.append((u, v, kind, data))
            return i

        rot = {}
        # E_R edges: dart d joins corner(d) and corner(next d)
        er = {}
        for d in g.darts:
            er[d] = add(('c', d), ('c', g.nxt(d)), 'R', d)
        # E_C edges
        ec = {}
        for e, at in self.ec_at.items():
            x = next(iter(e - {at}))
            d = (at, x)                          # corner(d) in rgt(d), the other corner in lft(d)
            c1 = ('c', d)
            c2 = ('c', g.nxt((x, at)))
            if c1 == c2:
                continue                          # loop: dropped
            ec[d] = add(c1, c2, 'C', d)           # arc c1->c2 is dart d, c2->c1 is dart rev d
        # spokes
        sp = {}
        for s_, cs in self.stars.items():
            for c in cs:
                sp[c] = add(s_, c, 'S', None)
        # rotation at corner (v,x), a = cw(x): spoke, EC(va at v), ER along a, ER along x, EC(vx at v)
        for d in g.darts:
            v, x = d
            a = g.cw(v, x)
            c = ('c', d)
            lst = []
            if c in sp:
                lst.append(sp[c])
            # EC of edge v-a at v, seen from corner c: its dart (v,a) has corner(v,a)=c' and other corner next(a,v)=(v,ccw a)=(v,x)=c
            if (v, a) in ec:
                lst.append(ec[v, a])
            lst.append(er[(a, v)])                # next(a,v) = (v,x): ER of dart (a,v) ends at c
            lst.append(er[d])
            if (v, x) in ec and not (a == x):
                lst.append(ec[v, x])
            rot[c] = lst
        for s_, cs in self.stars.items():
            rot[s_] = [sp[c] for c in cs]
        self.rot = rot
        self.other = lambda i, u: self.E[i][1] if self.E[i][0] == u else self.E[i][0]

    def faces(self):
        """boundary walks with the same rule as G: arrive over edge i at w, leave by the ccw successor of i at w"""
        seen = set()
        out = []
        for u, lst in self.rot.items():
            for i in lst:
                if (u, i) in seen:
                    continue
                walk = []
                a, j = u, i
                while (a, j) not in seen:
                    seen.add((a, j))
                    walk.append((a, j))
                    w = self.other(j, a)
                    r = self.rot[w]
                    k = r.index(j)
                    nj = r[(k + 1) % len(r)]
                    a, j = w, nj
                out.append(walk)
        return out

    def euler_ok(self):
        V = len(self.nodes)
        E = len(self.E)
        F = len(self.faces())
        # connected?
        return V - E + F == 2, (V, E, F)

    def nxg(self):
        H = nx.MultiGraph()
        H.add_nodes_from(self.nodes)
        for u, v, k, dd in self.E:
            H.add_edge(u, v)
        return H

    def slit(self):
        """the cycle S as in Lemma N(3)"""
        g = self.g
        q = []

        def push(x):
            if not q or q[-1] != x:
                q.append(x)

        def link(a, b):
            if a == b:
                push(a)
                return
            va, ba = self.bank_of[a]
            vb, bb = self.bank_of[b]
            assert (va, ba) == (vb, bb), (a, b)
            push(a)
            push(('s', va, ba))
            push(b)

        R = self.R
        for i, d in enumerate(R):
            push(('c', d))
            n = ('c', g.nxt(d))
            if i + 1 < len(R):
                link(n, ('c', R[i + 1]))
            else:
                push(n)
        rev = [(b, a) for a, b in reversed(R)]
        link(q[-1], ('c', rev[0]))
        for i, d in enumerate(rev):
            push(('c', d))
            n = ('c', g.nxt(d))
            if i + 1 < len(rev):
                link(n, ('c', rev[i + 1]))
            else:
                push(n)
        # close at s
        if q[-1] == q[0]:
            q.pop()
        else:
            a, b = q[-1], q[0]
            va, ba = self.bank_of[a]
            assert self.bank_of[b] == (va, ba)
            q.append(('s', va, ba))
        return q

    def lengths(self, C, M):
        """arc lengths ell_C on N, as dict u -> list of (v, l); parallel edges kept"""
        adj = collections.defaultdict(list)
        for u, v, k, dd in self.E:
            if k == 'R':
                adj[u].append((v, 0))
                adj[v].append((u, 0))
            elif k == 'S':
                adj[u].append((v, M))
                adj[v].append((u, M))
            else:
                d = dd
                adj[u].append((v, C[d]))                # corner in rgt(d) -> corner in lft(d)
                adj[v].append((u, C[(d[1], d[0])]))
        return adj


def dijkstra(adj, offs, f=None):
    dist = dict(offs)
    pq = [(x, u) for u, x in offs.items()]
    heapq.heapify(pq)
    while pq:
        x, u = heapq.heappop(pq)
        if x > dist[u]:
            continue
        for v, l in adj[u]:
            nl = l if f is None else f(l)
            if v not in dist or x + nl < dist[v]:
                dist[v] = x + nl
                heapq.heappush(pq, (x + nl, v))
    return dist


def gamma_adj(g, N, C):
    adj = collections.defaultdict(list)
    for d in g.darts:
        if N.sigma[d] == 0:
            adj[g.rgt[d]].append((g.lft(d), C[d]))
    return adj


def maxflow_val(g, c, s, t):
    H = nx.DiGraph()
    H.add_nodes_from(g.rot)
    for d, x in c.items():
        H.add_edge(d[0], d[1], capacity=x)
    return nx.maximum_flow_value(H, s, t)


def check_structure(g, R, st, ec_end='larger', rng=None, fail=None):
    N = NetN(g, R, ec_end, rng)
    ok, tup = N.euler_ok()
    st['euler'] += 1
    Hm = nx.Graph()
    Hm.add_nodes_from(N.nodes)
    Hm.add_edges_from((u, v) for u, v, _, _ in N.E)
    if not nx.is_connected(Hm):
        st['FAIL.N_disconnected'] += 1
        fail('disconnected', g, R)
        return None
    if not ok:
        st['FAIL.euler'] += 1
        fail('euler %s' % (tup,), g, R)
        return None
    q = N.slit()
    st['slit'] += 1
    if len(set(q)) != len(q):
        st['FAIL.slit_not_simple'] += 1
        fail('slit not simple', g, R)
        return None
    for a, b in zip(q, q[1:] + q[:1]):
        if not Hm.has_edge(a, b):
            st['FAIL.slit_edge_missing'] += 1
            fail('slit edge missing %s %s' % (a, b), g, R)
            return None
    # a face of the rotation with exactly these nodes, each once
    Sset = set(q)
    fac = [w for w in N.faces() if {a for a, _ in w} == Sset and len(w) == len(q)]
    st['facial'] += 1
    if not fac:
        st['FAIL.slit_not_face'] += 1
        fail('slit not a face', g, R)
        return None
    # all corners of R darts on S
    for d in g.darts:
        if N.sigma[d] != 0 and ('c', d) not in Sset:
            st['FAIL.corner_missing'] += 1
            fail('corner missing', g, R)
            return None
    # sizes
    k = len(R)
    D = nx.diameter(nx.Graph([(a, b) for a, b in g.darts]))
    st['max|S|-6k'] = max(st['max|S|-6k'], len(q) - 6 * k)
    if len(q) > 6 * D + 2:
        st['FAIL.S_size'] += 1
        fail('S size', g, R)
    dN = nx.diameter(Hm)
    st['max.dN-6D'] = max(st['max.dN-6D'], dN - 6 * D)
    if dN > 6 * D + 2:
        st['FAIL.hop'] += 1
        fail('hop diam %d vs D %d' % (dN, D), g, R)
    # T
    T = nx.Graph()
    T.add_nodes_from(N.nodes)
    T.add_edges_from(zip(q, q[1:]))
    seen = set(q)
    dq = collections.deque(q)
    depth = {x: 0 for x in q}
    while dq:
        x = dq.popleft()
        for y in Hm[x]:
            if y not in seen:
                seen.add(y)
                T.add_edge(x, y)
                depth[y] = depth[x] + 1
                dq.append(y)
    if not nx.is_tree(T):
        st['FAIL.T_not_tree'] += 1
        fail('T not tree', g, R)
    st['max.Tdepth-3D'] = max(st['max.Tdepth-3D'], max(depth.values()) - 3 * D)
    return N, q, D, dN


def lam_exact(C, g, N, nn, P_all, pairs, st, fail, tag):
    """check Lemma N(5) and (6) on S corners, exact arithmetic"""
    maxC = max(C.values()) if C else 0
    M = nn * maxC + 1
    adj = N.lengths(C, M)
    ga = gamma_adj(g, N, C)
    for a in P_all:
        da = dijkstra(adj, {a: 0})
        dg = dijkstra(ga, {g.rgt[a[1]]: 0})
        for b in P_all:
            st['metric'] += 1
            if da[b] != dg[g.rgt[b[1]]]:
                st['FAIL.metric'] += 1
                fail('metric %s %s %s %s %s' % (a, b, da[b], dg[g.rgt[b[1]]], tag), g, N.R)


def portal_b(C, g, N, nn, P, mode, rng):
    """b from delta in [dist_L, (1+eps)dist_L] on N, Lemma N(6)"""
    maxC = max(C.values()) if C else 0
    M = nn * maxC + 1
    adj = N.lengths(C, M)
    sc = 2 * nn * K
    b = {}
    for a in P:
        dist = dijkstra(adj, {a: 0}, f=lambda l: sc * l + 1)
        for c in P:
            dl = dist[c]
            if mode == 'lo':
                de = Fr(dl)
            elif mode == 'hi':
                de = Fr(dl) * (1 + EPS)
            elif mode == 'two':
                de = Fr(dl) * rng.choice([1, 1 + EPS])
            else:
                de = Fr(dl) * (1 + EPS * Fr(rng.randrange(0, 1001), 1000))
            b[a, c] = math.floor(de / ((1 + EPS) * 2 * nn))
    return b


def direct_b(C, g, N, P, mode, rng):
    """b chosen directly anywhere in the range (B), including the bottom of the range"""
    ga = gamma_adj(g, N, C)
    b = {}
    for a in P:
        dg = dijkstra(ga, {g.rgt[a[1]]: 0})
        for c in P:
            d = dg[g.rgt[c[1]]]
            lo = math.ceil(Fr(36 * d, 5))
            hi = K * d
            if mode == 'blo':
                b[a, c] = lo
            elif mode == 'bhi':
                b[a, c] = hi
            elif mode == 'btwo':
                b[a, c] = rng.choice([lo, hi])
            else:
                b[a, c] = rng.randint(lo, hi)
    return b


def solve(g, N, P, b, C, J):
    arcs = [(u, v, w) for (u, v), w in b.items() if u != v]
    for d in g.darts:
        if N.sigma[d] != 0:
            # ψ(lft d) − ψ(rgt d) ≤ K C(d) − σ J; nodes: corner(d) carries rgt(d), corner(rev d) carries lft(d)
            arcs.append((('c', d), ('c', (d[1], d[0])), K * C[d] - N.sigma[d] * J))
    psi = {p: 0 for p in P}
    for it in range(len(P) + 1):
        ch = False
        for u, v, w in arcs:
            if psi[u] + w < psi[v]:
                psi[v] = psi[u] + w
                ch = True
        if not ch:
            return psi
    return None


def largest_J(g, N, P, b, C):
    if solve(g, N, P, b, C, 0) is None:
        return None, None
    lo, hi = 0, 1
    while solve(g, N, P, b, C, hi) is not None:
        lo, hi = hi, hi * 2
        if hi > 10 ** 40:
            raise AssertionError('unbounded')
    while hi - lo > 1:
        m = (lo + hi) // 2
        if solve(g, N, P, b, C, m) is not None:
            lo = m
        else:
            hi = m
    return lo, solve(g, N, P, b, C, lo)


def pipeline(g, N, q, c, s, t, st, fail, mode, rng):
    """Sections 2, 3, 6 on the real N: b from N or from (B) directly, phi from a virtual source on N."""
    nn = len(N.nodes)
    P = [x for x in q if x[0] == 'c']
    F = g.nf + 1
    n = g.n
    U = max(max(c.values()), 1)
    T = 0
    while 5 ** T < F * (n * U + 1):
        T += 1
    C = dict(c)
    lam = maxflow_val(g, c, s, t)
    beta, Phi, scale = 0, collections.defaultdict(int), 1
    for it in range(T):
        lam_i = maxflow_val(g, C, s, t)
        if mode.startswith('b'):
            b = direct_b(C, g, N, P, mode, rng)
        else:
            b = portal_b(C, g, N, nn, P, mode, rng)
            # (B) check
            ga = gamma_adj(g, N, C)
            for a in P:
                dg = dijkstra(ga, {g.rgt[a[1]]: 0})
                for x in P:
                    st['B'] += 1
                    d = dg[g.rgt[x[1]]]
                    if not (5 * b[a, x] >= 36 * d and b[a, x] <= K * d):
                        st['FAIL.B'] += 1
                        fail('(B) a=%s x=%s b=%s d=%s' % (a, x, b[a, x], d), g, N.R)
        J, psi = largest_J(g, N, P, b, C)
        if J is None:
            st['FAIL.J0_unsolvable'] += 1
            fail('System(0) unsolvable', g, N.R)
            return
        st['steps'] += 1
        if not (5 * J >= 36 * lam_i - 4 and J <= K * lam_i):
            st['FAIL.Jbound'] += 1
            fail('J bound J=%s lam=%s' % (J, lam_i), g, N.R)
        # same face same psi
        base = -min(psi.values())
        KC = {d: K * C[d] for d in C}
        M2 = nn * max(max(KC.values()), 1) + 1
        adj = N.lengths(KC, M2)
        off = {p: psi[p] + base for p in P}
        dist = dijkstra(adj, off)
        phi = {}
        for d in g.darts:
            f = g.rgt[d]
            v = dist[('c', d)] - base
            if f in phi and phi[f] != v:
                st['FAIL.corners_disagree'] += 1
                fail('corners of a face disagree', g, N.R)
            phi[f] = v
        for p in P:
            if phi[g.rgt[p[1]]] != psi[p]:
                st['FAIL.fill'] += 1
                fail('phi != psi on P', g, N.R)
        # star never minimal: phi equals Gamma distances
        ga = gamma_adj(g, N, KC)
        o2 = {}
        for p in P:
            f = g.rgt[p[1]]
            o2[f] = min(o2.get(f, 10 ** 60), psi[p] + base)
        dgam = dijkstra(ga, o2)
        for f in range(g.nf):
            st['fillcheck'] += 1
            if dgam[f] - base != phi[f]:
                st['FAIL.fill_gamma'] += 1
                fail('N fill differs from Gamma fill', g, N.R)
        new = {}
        for d in g.darts:
            gg = phi[g.lft(d)] - phi[g.rgt[d]] + N.sigma[d] * J
            new[d] = K * C[d] - gg
            st['residual'] += 1
            if new[d] < 0:
                st['FAIL.residual'] += 1
                fail('negative residual', g, N.R)
                return
        # value of the residual
        C = new
        scale *= K
        beta = beta * K + J
        for f in range(g.nf):
            Phi[f] = Phi[f] * K + phi[f]
    lam2 = -((-beta) // scale)
    st['final'] += 1
    if lam2 != lam:
        st['FAIL.value'] += 1
        fail('value %s %s' % (lam2, lam), g, N.R)
        return
    p = lam * scale - beta
    if p * F >= scale:
        st['FAIL.gap'] += 1
    adj = collections.defaultdict(list)
    for d in g.darts:
        r = scale * (c[d] - N.sigma[d] * lam) + Phi[g.rgt[d]] - Phi[g.lft(d)] + p
        if r < 0:
            st['FAIL.r_neg'] += 1
            fail('r negative', g, N.R)
            return
        adj[g.rgt[d]].append((g.lft(d), r))
    f0 = g.rgt[g.darts[0]]
    dr = dijkstra(adj, {f0: 0})
    psi = {x: (dr[x] - Phi[f0] + Phi[x]) // scale for x in range(g.nf)}
    net = collections.Counter()
    for d in g.darts:
        fl = psi[g.lft(d)] - psi[g.rgt[d]] + N.sigma[d] * lam
        if fl > c[d]:
            st['FAIL.infeasible'] += 1
            fail('infeasible', g, N.R)
            return
        net[d[0]] += fl
    for v in g.rot:
        want = lam if v == s else (-lam if v == t else 0)
        if net[v] != want:
            st['FAIL.conservation'] += 1
            fail('conservation', g, N.R)
            return
    st['exact_ok'] += 1


def caps(g, rng):
    mode = rng.choice(['sym', 'dir', 'oneway', 'zero', 'unit', 'huge'])
    U = rng.choice([1, 2, 3, 7, 50])
    c = {}
    for d in g.darts:
        if d in c:
            continue
        rv = (d[1], d[0])
        if mode == 'sym':
            c[d] = c[rv] = rng.randint(1, U)
        elif mode == 'dir':
            c[d], c[rv] = rng.randint(0, U), rng.randint(0, U)
        elif mode == 'oneway':
            c[d], c[rv] = rng.randint(1, U), 0
            if rng.random() < .5:
                c[d], c[rv] = c[rv], c[d]
        elif mode == 'zero':
            c[d] = c[rv] = rng.choice([0, 0, rng.randint(0, U)])
        elif mode == 'huge':
            c[d] = c[rv] = rng.randint(1000, 100000)
        else:
            c[d] = c[rv] = 1
    return c


def planar_rotations(H, rng, cap):
    """yield ccw rotations of H (all when few, sampled otherwise) with genus 0"""
    vs = list(H.nodes())
    nbr = {v: list(H[v]) for v in vs}
    tot = 1
    for v in vs:
        tot *= math.factorial(max(len(nbr[v]) - 1, 0))
    if tot <= cap:
        pr = [list(itertools.permutations(nbr[v][1:])) if nbr[v] else [()] for v in vs]
        for ch in itertools.product(*pr):
            rot = {v: [nbr[v][0]] + list(ch[i]) if nbr[v] else [] for i, v in enumerate(vs)}
            g = G0(rot)
            if g.genus0():
                yield g
    else:
        ok, em = nx.check_planarity(H)
        if ok:
            rot = {v: list(em.neighbors_cw_order(v))[::-1] for v in vs}
            yield G0(rot)
            for _ in range(cap // 200):
                # flip around: random perm trials
                rot = {v: rng.sample(nbr[v], len(nbr[v])) for v in vs}
                g = G0(rot)
                if g.genus0():
                    yield g


def shortest_paths(H, s, t, cap=6):
    out = []
    for p in nx.all_shortest_paths(H, s, t):
        out.append([(a, b) for a, b in zip(p, p[1:])])
        if len(out) >= cap:
            break
    return out
