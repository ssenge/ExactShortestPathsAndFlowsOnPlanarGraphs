"""Own implementation of the machinery of notes/NEGATIVE.md, exact integers, nothing taken from neg.py.

Arcs are tuples (u, v, w). Vertices 0..n-1. The oracle is heapq Dijkstra and asserts its preconditions.
"""
import collections
import heapq
import math
import random

INF = 10 ** 200


class Stats(collections.Counter):
    pass


GLOBAL = Stats()


def oracle(n, arcs, off, st=GLOBAL):
    """min over sources of off[u] + dist(u, v); off[u] None means not a source; asserts weights and offsets >= 0."""
    st['oracle'] += 1
    adj = [[] for _ in range(n)]
    for u, v, w in arcs:
        assert w >= 0, ('negative weight fed to oracle', u, v, w)
        st['max_w'] = max(st['max_w'], w)
        adj[u].append((v, w))
    d = [INF] * n
    h = []
    for v in range(n):
        if off[v] is not None:
            assert off[v] >= 0, ('negative offset fed to oracle', v, off[v])
            st['max_off'] = max(st['max_off'], off[v])
            d[v] = off[v]
            h.append((off[v], v))
    heapq.heapify(h)
    while h:
        x, v = heapq.heappop(h)
        if x > d[v]:
            continue
        for y, w in adj[v]:
            if x + w < d[y]:
                d[y] = x + w
                heapq.heappush(h, (x + w, y))
    return d


def rev(arcs):
    return [(v, u, w) for u, v, w in arcs]


def bf(n, arcs, init=None):
    """Exact distances from a virtual source with offsets init (default 0); None on a negative cycle reachable."""
    d = [0] * n if init is None else list(init)
    for it in range(n + 2):
        ch = False
        for u, v, w in arcs:
            if d[u] < INF and d[u] + w < d[v]:
                d[v] = d[u] + w
                ch = True
        if not ch:
            return d
    return None


def has_neg_cycle(n, arcs):
    return bf(n, arcs) is None


# ---------- Lemma 1

def lemma1(n, arcs, phi, t, st=GLOBAL):
    pos, neg = [], []
    for u, v, w in arcs:
        y = w + phi[u] - phi[v]
        (pos if y >= 0 else neg).append((u, v, y))
    sh = max(phi) if n else 0
    a = oracle(n, pos, [sh - phi[v] for v in range(n)], st)
    a = [x - sh for x in a]
    for i in range(t):
        b = list(a)
        for u, v, y in neg:
            if a[u] + y < b[v]:
                b[v] = a[u] + y
        if b == a:
            break
        st['rounds_lemma1'] += 1
        s2 = min(b)
        a = oracle(n, pos, [x - s2 for x in b], st)
        a = [x + s2 for x in a]
    return [a[v] + phi[v] for v in range(n)]


# ---------- strong components: direct, and Algorithm 3 of [3] with the reading of Cor. 33

def tarjan_order(n, arcs):
    """Strong components and an index that increases along every arc between components. Iterative."""
    adj = [[] for _ in range(n)]
    for u, v, w in arcs:
        adj[u].append(v)
    idx = [None] * n
    low = [0] * n
    on = [False] * n
    comp = [None] * n
    stack, cnt, ncomp = [], 0, 0
    for s in range(n):
        if idx[s] is not None:
            continue
        work = [(s, 0)]
        while work:
            v, i = work.pop()
            if i == 0:
                idx[v] = low[v] = cnt
                cnt += 1
                stack.append(v)
                on[v] = True
            rec = False
            while i < len(adj[v]):
                y = adj[v][i]
                i += 1
                if idx[y] is None:
                    work.append((v, i))
                    work.append((y, 0))
                    rec = True
                    break
                if on[y]:
                    low[v] = min(low[v], idx[y])
            if rec:
                continue
            if low[v] == idx[v]:
                while True:
                    x = stack.pop()
                    on[x] = False
                    comp[x] = ncomp
                    if x == v:
                        break
                ncomp += 1
            if work:
                p = work[-1][0]
                low[p] = min(low[p], low[v])
    # Tarjan numbers components in reverse topological order
    return [ncomp - 1 - c for c in comp]


def reach(n, arcs, srcs, inside):
    """Vertices of inside reachable from srcs along arcs inside."""
    adj = collections.defaultdict(list)
    for u, v, w in arcs:
        if u in inside and v in inside:
            adj[u].append(v)
    seen = set(srcs)
    q = list(srcs)
    while q:
        x = q.pop()
        for y in adj[x]:
            if y not in seen:
                seen.add(y)
                q.append(y)
    return seen


def components(V, edges):
    """Connected components of the undirected graph on V with the pairs in edges that lie in V."""
    p = {v: v for v in V}

    def f(x):
        while p[x] != x:
            p[x] = p[p[x]]
            x = p[x]
        return x
    for a, b in edges:
        if a in p and b in p:
            p[f(a)] = f(b)
    out = collections.defaultdict(set)
    for v in V:
        out[f(v)].add(v)
    return list(out.values())


def alg3(n, arcs, rng, cc=None, net=None, size_of='own', stats=None, big=2):
    """Algorithm 3 of [3], SCC+Topsort, labels r_v.

    cc=None: sequential as in Prop. 32. cc='input': recurse into components of the input digraph, as Cor. 33 says.
    cc='net': recurse into components of the network edges net.
    size_of: in the base case the interval is [l N^big, (l + m - 1) N^big]; m is the component ('own') or the set R_j ('parent').
    """
    N = max(n, 1)
    r = [None] * n
    und = [(u, v) for u, v, w in arcs] if cc == 'input' else (net if cc == 'net' else None)

    def recurse(V, l, m_parent, depth):
        if stats is not None:
            stats['alg3_maxdepth'] = max(stats['alg3_maxdepth'], depth)
        V = set(V)
        k = len(V)
        if k == 0:
            return
        E = [(u, v, w) for u, v, w in arcs if u in V and v in V]
        order = list(V)
        rng.shuffle(order)
        target = (k + len(E)) / 2
        # smallest p with |S_p| + |E_p| >= target; binary search would give the same since it is monotone
        S = set()
        p = None
        prevS = set()
        for i, v in enumerate(order):
            prevS = set(S)
            S = reach(n, E, set(S) | {v}, V)
            ep = sum(1 for a, b, w in E if a in S and b in S)
            if len(S) + ep >= target:
                p = i
                break
        A = prevS
        vp = order[p]
        B = reach(n, E, {vp}, V)
        Bin = reach(n, rev(E), {vp}, V)
        C = B & Bin
        if len(C) == k:
            m = k if size_of == 'own' else m_parent
            lo, hi = l * N ** big, (l + m - 1) * N ** big
            x = rng.randint(lo, hi)
            for v in V:
                r[v] = x
            return
        R1 = V - (A | B)
        R2 = A - B
        R3 = C
        R4 = B - (A | C)
        R5 = (A & B) - C
        ls = [l + len(R2) + len(R3) + len(R4) + len(R5), l + len(R3) + len(R4) + len(R5),
              l + len(R4) + len(R5), l + len(R5), l]
        for R, lj in zip((R1, R2, R3, R4, R5), ls):
            if not R:
                continue
            if cc is None:
                recurse(R, lj, len(R), depth + 1)
            else:
                for comp in components(R, und):
                    recurse(comp, lj, len(R), depth + 1)
    if cc is None:
        recurse(set(range(n)), 0, n, 0)
    else:
        for comp in components(set(range(n)), und):
            recurse(comp, 0, n, 0)
    return r


# ---------- the decomposition, Algorithms 1 and 2 of [3], with the recursion on components of Cor. 27

def trunc_geom(p, cap, rng):
    k = 0
    while k < cap and rng.random() >= p:
        k += 1
    return k


def sub(arcs, X):
    return [(u, v, w) for u, v, w in arcs if u in X and v in X]


def balls(n, arcs, X, srcs, reversed_=False, st=GLOBAL):
    """srcs: dict vertex -> radius. The set of vertices of X within radius of a source, in the graph arcs restricted to X."""
    if not srcs:
        return set()
    cap = max(srcs.values())
    off = [None] * n
    for v, r in srcs.items():
        off[v] = cap - r
    d = oracle(n, rev(sub(arcs, X)) if reversed_ else sub(arcs, X), off, st)
    return {v for v in X if d[v] <= cap}


def find_balanced(n, arcs, X, Vp, d, kind, rng, c, st):
    size = len(X)
    Vp = list(Vp)
    rng.shuffle(Vp)
    if not Vp:
        return set()
    p = min(c * math.log2(max(n, 2)) / d, 1.0)
    cap = d // 4
    ds = [trunc_geom(p, cap, rng) for _ in Vp]
    rv = (kind == 'in')

    def U(i):
        st['fb_calls'] += 1
        return balls(n, arcs, X, dict(zip(Vp[:i], ds[:i])), rv, st)
    full = U(len(Vp))
    if len(full) <= 0.1 * size:
        return full
    lo, hi = 1, len(Vp)
    while lo < hi:
        mid = (lo + hi) // 2
        if len(U(mid)) > 0.1 * size:
            hi = mid
        else:
            lo = mid + 1
    return U(lo)


def ldd(n, arcs, d, rng, c=1.0, net=None, st=GLOBAL, sample_with_replacement=False):
    """E_rem as a set of arc positions. net: network pairs for the component splitting (default the arcs themselves)."""
    und = net if net is not None else [(u, v) for u, v, w in arcs]
    erem = set()
    layer = components(set(range(n)), und)
    depth = 0
    k0 = max(1, math.ceil(c * math.log2(max(n, 2))))
    while layer:
        depth += 1
        st['ldd_depth_total'] += 1
        nxt = []
        for X in layer:
            if len(X) <= 1:
                continue
            A = sub(arcs, X)
            Xl = sorted(X)
            samples = rng.choices(Xl, k=k0) if sample_with_replacement else rng.sample(Xl, min(k0, len(Xl)))
            k = len(samples)
            cin = collections.Counter()
            cout = collections.Counter()
            for s in samples:
                dout = balls(n, arcs, X, {s: d // 4}, False, st)
                din = balls(n, arcs, X, {s: d // 4}, True, st)
                for v in dout:      # s reaches v: s in the in-ball of v
                    cin[v] += 1
                for v in din:       # v reaches s: s in the out-ball of v
                    cout[v] += 1
            Vin = {v for v in X if cin[v] <= 0.6 * k}
            Vout = {v for v in X if v not in Vin and cout[v] <= 0.6 * k}
            Ain = find_balanced(n, arcs, X, Vin, d, 'in', rng, c, st)
            Aout = find_balanced(n, arcs, X, Vout, d, 'out', rng, c, st)
            sz = len(X)
            pos = [i for i, (u, v, w) in enumerate(arcs) if u in X and v in X]
            if 0.1 * sz <= len(Ain) <= 0.9 * sz:
                erem.update(i for i in pos if arcs[i][0] not in Ain and arcs[i][1] in Ain)
                nxt += components(Ain, und) + components(X - Ain, und)
            elif 0.1 * sz <= len(Aout) <= 0.9 * sz:
                erem.update(i for i in pos if arcs[i][0] in Aout and arcs[i][1] not in Aout)
                nxt += components(Aout, und) + components(X - Aout, und)
            else:
                rest = X - Ain - Aout
                ok = len(Ain | Aout) < 0.5 * sz
                if rest:
                    u = min(rest)
                    bo = balls(n, arcs, X, {u: d // 2}, False, st)
                    bi = balls(n, arcs, X, {u: d // 2}, True, st)
                    ok = ok and rest <= (bo & bi)
                if not ok:
                    st['ldd_giveup'] += 1
                    erem.update(pos)
                    continue
                erem.update(i for i in pos if arcs[i][0] not in Ain and arcs[i][1] in Ain)
                erem.update(i for i in pos if arcs[i][0] in Aout and arcs[i][1] not in Aout)
                nxt += components(Ain, und) + components(Aout - Ain, und)
        layer = nxt
    st['ldd_runs'] += 1
    st['ldd_maxdepth'] = max(st['ldd_maxdepth'], depth)
    return erem


# ---------- Proposition 4

def restricted(n, arcs, R=3, t=8, c=1.0, rng=None, label='tarjan', net=None, st=GLOBAL, hook=None, decomp=None):
    """Algorithm of Section 4 of the note. Returns a potential; never reads the truth. hook(l, r, idx, best) for inspection.

    decomp(l, r, d) may replace the random decomposition: it returns idx (a list).
    label: 'tarjan', 'seq', 'cor33input', 'cor33net', 'cor33input_parent', 'cor33net_parent'.
    """
    rng = rng or random.Random(0)
    L = 1
    while 2 ** L < 2 * n * n:
        L += 1
    ge = [(u, v, max(w, 0)) for u, v, w in arcs]
    Phi = [[0] * n]
    for l in range(1, L + 1):
        new = []
        for r in range(1 if l == L else R):
            kept = ge
            if decomp is not None:
                idx = decomp(l, r, 2 ** l)
            else:
                if l == L:
                    rem = set()
                else:
                    rem = ldd(n, ge, 2 ** l, rng, c, net=net, st=st)
                kept = [a for i, a in enumerate(ge) if i not in rem]
                idx = indices(n, kept, rng, label, net, st)
            inside = [a for a in arcs if idx[a[0]] == idx[a[1]]]
            ds = [lemma1(n, inside, phi, t, st) for phi in Phi]
            best = [min(x[v] for x in ds) for v in range(n)]
            pot = [best[v] - idx[v] * n for v in range(n)]
            st['max_pot'] = max(st['max_pot'], max(abs(x) for x in pot) if pot else 0)
            if hook is not None:
                hook(l, r, idx, best, pot, inside, kept)
            new.append(pot)
        Phi = new
    return Phi[0]


def indices(n, kept, rng, label, net, st=GLOBAL):
    if label == 'tarjan':
        return tarjan_order(n, kept)
    if label == 'seq':
        r = alg3(n, kept, rng, cc=None, stats=st)
    elif label == 'cor33input':
        r = alg3(n, kept, rng, cc='input', stats=st)
    elif label == 'cor33net':
        r = alg3(n, kept, rng, cc='net', net=net, stats=st)
    elif label == 'cor33input_parent':
        r = alg3(n, kept, rng, cc='input', size_of='parent', stats=st)
    elif label == 'cor33net_parent':
        r = alg3(n, kept, rng, cc='net', net=net, size_of='parent', stats=st)
    else:
        raise ValueError(label)
    top = max(r) if r else 0
    return [top - x for x in r]


# ---------- Lemma 5

def params(B):
    if B >= 5:
        return (B + 2) // 3, 2
    if B >= 3:
        return 2, 1
    if B == 2:
        return 1, 1
    return 1, 0


def scale_x(arcs, n):
    return [(u, v, 2 * ((n + 1) * w + 1)) for u, v, w in arcs]


def scaling(n, arcs, solver, st=GLOBAL, maxphases=10 ** 6):
    """A potential phi with x_phi >= 0, or None when a check fails (reported as a negative cycle)."""
    xa = scale_x(arcs, n)
    phi = [0] * n
    while True:
        xp = [(u, v, w + phi[u] - phi[v]) for u, v, w in xa]
        B = max([0] + [-w for u, v, w in xp])
        if B == 0:
            return phi
        st['phases'] += 1
        rho, alpha = params(B)
        ra = [(u, v, w // rho + alpha) for u, v, w in xp]
        assert all(w >= -1 for u, v, w in ra), 'r below -1'
        kept = [a for a in ra if a[2] <= n]
        psi = solver(n, kept)
        if psi is None:
            return None
        rp = [(u, v, w + psi[u] - psi[v]) for u, v, w in kept]
        if any(w < 0 for u, v, w in rp):
            return None
        sh = max(psi) if n else 0
        dd = oracle(n, rp, [sh - psi[v] for v in range(n)], st)
        dd = [dd[v] - sh + psi[v] for v in range(n)]
        if any(w + dd[u] - dd[v] < 0 for u, v, w in ra):
            return None
        phi = [phi[v] + rho * dd[v] for v in range(n)]
        st['max_phi'] = max(st['max_phi'], max(abs(p) for p in phi))
        xn = [w + phi[u] - phi[v] for u, v, w in xa]
        assert min(xn) >= -rho * alpha, 'Lemma 5 lower bound'
        st['max_B'] = max(st['max_B'], B)


def bf_solver(n, kept):
    return bf(n, kept)


def dist_from_phi(n, arcs, s, phi, st=GLOBAL):
    """dist(s, v) in w by one call of the oracle and floor division, as Section 5 says."""
    xa = scale_x(arcs, n)
    xp = [(u, v, w + phi[u] - phi[v]) for u, v, w in xa]
    off = [None] * n
    off[s] = 0
    d = oracle(n, xp, off, st)
    out = []
    for v in range(n):
        if d[v] >= INF:
            out.append(INF)
        else:
            dx = d[v] - phi[s] + phi[v]
            out.append(dx // (2 * (n + 1)))
    return out


def is_restricted(n, arcs):
    if any(w < -1 or w > n for u, v, w in arcs):
        return False
    return not has_neg_cycle(n, [(u, v, w - 1) for u, v, w in arcs])


# ---------- plane multigraphs by rotation system, dual, face-disjoint graph

class Map:
    """Connected plane multigraph. Dart 2e is a->b, 2e+1 is b->a for edge e = (a, b). rot[v] is the cyclic list of darts leaving v."""

    def __init__(self, n, edges, rot):
        self.n, self.edges, self.rot = n, edges, rot
        self.pos = {}
        for v in range(n):
            for i, d in enumerate(rot[v]):
                assert self.tail(d) == v
                self.pos[d] = i
        self.lft = {}
        self.nf = 0
        for d0 in range(2 * len(edges)):
            if d0 in self.lft:
                continue
            d = d0
            while d not in self.lft:
                self.lft[d] = self.nf
                d = self.next_left(d)
            self.nf += 1

    def tail(self, d):
        a, b = self.edges[d // 2]
        return a if d % 2 == 0 else b

    def head(self, d):
        a, b = self.edges[d // 2]
        return b if d % 2 == 0 else a

    def sigma(self, d):
        v = self.tail(d)
        return self.rot[v][(self.pos[d] + 1) % len(self.rot[v])]

    def sigma_inv(self, d):
        v = self.tail(d)
        return self.rot[v][(self.pos[d] - 1) % len(self.rot[v])]

    def next_left(self, d):
        return self.sigma_inv(d ^ 1)

    def rgt(self, d):
        return self.lft[d ^ 1]

    def genus_zero(self):
        return self.n - len(self.edges) + self.nf == 2

    def dual_arcs(self, length):
        """dual dart of d: rgt(d) -> lft(d)."""
        return [(self.rgt(d), self.lft[d], length[d]) for d in range(2 * len(self.edges))]

    def ghat(self, length, M=None, end='tail'):
        """The face-disjoint graph: nodes 0..n-1 star centres, n+d the corner left of dart d at its tail.
        Returns nn, arcs, undirected pairs. E_C of edge e sits at the end 'tail' of its dart 2e, or at the end of larger degree."""
        n, m = self.n, len(self.edges)
        nn = n + 2 * m
        lam = max([abs(x) for x in length] + [0])
        if M is None:
            M = nn * lam + 1
        arcs = []
        pairs = []
        for d in range(2 * m):
            c = n + d
            v = self.tail(d)
            arcs += [(v, c, M), (c, v, M)]
            pairs.append((v, c))
            c2 = n + self.next_left(d)
            arcs += [(c, c2, 0), (c2, c, 0)]
            pairs.append((c, c2))
        for e in range(m):
            d = 2 * e
            if end == 'deg' and len(self.rot[self.tail(d)]) < len(self.rot[self.head(d)]):
                d = d + 1
            a = n + self.sigma_inv(d)      # corner on the right of d, in rgt(d)
            b = n + d                      # corner on the left of d, in lft(d)
            arcs.append((a, b, length[d]))
            arcs.append((b, a, length[d ^ 1]))
            pairs.append((a, b))
        return nn, arcs, pairs


def bfs_tree_from(m_, root=0):
    """Parent dart of every vertex in a BFS tree: dart from child to parent."""
    par = {root: None}
    order = [root]
    for x in order:
        for d in m_.rot[x]:
            y = m_.head(d)
            if y not in par:
                par[y] = d ^ 1
                order.append(y)
    return par, order


def route_tree(m_, b):
    """f0 on darts with net outflow b, sum b = 0."""
    par, order = bfs_tree_from(m_)
    sub_ = dict(enumerate(b))
    f0 = [0] * (2 * len(m_.edges))
    for x in reversed(order[1:]):
        d = par[x]
        f0[d] += sub_[x]
        f0[d ^ 1] -= sub_[x]
        sub_[m_.head(d)] += sub_[x]
    return f0


def net_out(m_, f):
    out = [0] * m_.n
    for d in range(2 * len(m_.edges)):
        out[m_.tail(d)] += f[d]
    return out
