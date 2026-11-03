"""Independent implementation of the logic of NEGATIVE.md. Written from the note and from [2], [3], not from neg.py.
Pure Python integers, so no float rounding. An oracle call asserts what Algorithm Exact of [1] requires:
integer weights >= 0, integer offsets >= 0."""
import heapq, math, random
from collections import Counter, deque

INF = 10 ** 40
STAT = Counter()


def oracle(n, arcs, off):
    """min_u (off(u) + dist(u, v)). arcs: (u, v, w). off: list with INF for 'not in S'."""
    STAT['oracle'] += 1
    adj = [[] for _ in range(n)]
    for u, v, w in arcs:
        assert isinstance(w, int) and w >= 0, ('negative weight fed to the oracle', u, v, w)
        adj[u].append((v, w))
        if w > STAT['max_w']:
            STAT['max_w'] = w
    d = list(off)
    h = []
    for v in range(n):
        if off[v] < INF:
            assert isinstance(off[v], int) and off[v] >= 0, ('negative offset', v, off[v])
            if off[v] > STAT['max_off']:
                STAT['max_off'] = off[v]
            h.append((off[v], v))
    heapq.heapify(h)
    while h:
        x, u = heapq.heappop(h)
        if x > d[u]:
            continue
        for v, w in adj[u]:
            if x + w < d[v]:
                d[v] = x + w
                heapq.heappush(h, (x + w, v))
    return d


def oracle_shift(n, arcs, val):
    """Offsets of any sign, by a common shift, as the note says. val: list with INF for none."""
    fin = [x for x in val if x < INF]
    if not fin:
        return [INF] * n
    c = -min(fin)
    d = oracle(n, arcs, [x + c if x < INF else INF for x in val])
    return [x - c if x < INF else INF for x in d]


def bf_all(n, arcs):
    """dist(V, v), empty walk included, or None if a negative cycle exists anywhere."""
    d = [0] * n
    for it in range(n + 1):
        ch = False
        for u, v, w in arcs:
            if d[u] + w < d[v]:
                d[v] = d[u] + w
                ch = True
        if not ch:
            return d
    return None


def bf_from(n, arcs, s):
    d = [INF] * n
    d[s] = 0
    for it in range(n + 1):
        ch = False
        for u, v, w in arcs:
            if d[u] < INF and d[u] + w < d[v]:
                d[v] = d[u] + w
                ch = True
        if not ch:
            return d
    return None


def alternate(n, arcs, phi, t, mode=''):
    """Lemma 1. Returns d, with d(v) = A_t(v) + phi(v)."""
    pos, neg = [], []
    for u, v, w in arcs:
        wp = w + phi[u] - phi[v]
        (pos if wp >= 0 else neg).append((u, v, wp))
    A = oracle_shift(n, pos, [-phi[x] for x in range(n)])
    tt = {'t_minus': max(t - 1, 0), 't0': 0}.get(mode, t)
    for i in range(tt):
        B = list(A)
        for u, v, wp in neg:
            if A[u] + wp < B[v]:
                B[v] = A[u] + wp
        if B == A:
            break
        A = oracle_shift(n, pos, B)
    return [A[v] + phi[v] for v in range(n)]


def tarjan(n, arcs):
    adj = [[] for _ in range(n)]
    for a in arcs:
        adj[a[0]].append(a[1])
    index = [None] * n
    low = [0] * n
    on = [False] * n
    st = []
    comp = [-1] * n
    ctr = [0, 0]
    for r in range(n):
        if index[r] is not None:
            continue
        work = [(r, 0)]
        while work:
            v, i = work.pop()
            if i == 0:
                index[v] = low[v] = ctr[0]
                ctr[0] += 1
                st.append(v)
                on[v] = True
            rec = False
            for j in range(i, len(adj[v])):
                w = adj[v][j]
                if index[w] is None:
                    work.append((v, j + 1))
                    work.append((w, 0))
                    rec = True
                    break
                if on[w]:
                    low[v] = min(low[v], index[w])
            if rec:
                continue
            if low[v] == index[v]:
                while True:
                    w = st.pop()
                    on[w] = False
                    comp[w] = ctr[1]
                    if w == v:
                        break
                ctr[1] += 1
            if work:
                u = work[-1][0]
                low[u] = min(low[u], low[v])
    # Tarjan numbers components in reverse topological order
    k = ctr[1]
    return [k - 1 - c for c in comp]


def trunc_geom(p, cap, rng):
    """Definition 21 of [3]: P[x = k] = (1 - p)^k p / (1 - (1 - p)^(cap + 1)), k = 0..cap."""
    if p >= 1 or cap == 0:
        return 0
    u = rng.random() * (1 - (1 - p) ** (cap + 1))
    k = int(math.floor(math.log(1 - u) / math.log(1 - p)))
    return min(k, cap)


def balls(n, arcs, X, sources, rev):
    """{v: dist from the offsets} inside X. sources: {v: offset}."""
    Xs = set(X)
    a = [(v, u, w) if rev else (u, v, w) for u, v, w in arcs if u in Xs and v in Xs]
    off = [INF] * n
    for v, x in sources.items():
        off[v] = x
    return oracle(n, a, off)


def find_balanced(n, arcs, X, Vs, d, in_kind, rng, c, nglob):
    """Algorithm 2 of [3]. A = union of balls around a prefix of Vs."""
    Vs = list(Vs)
    rng.shuffle(Vs)
    if not Vs:
        return set()
    cap = d // 4
    p = min(c * math.log2(max(nglob, 2)) / d, 1.0)
    ds = [trunc_geom(p, cap, rng) for _ in Vs]

    def union(i):
        src = {Vs[j]: cap - ds[j] for j in range(i)}
        x = balls(n, arcs, X, src, rev=in_kind)
        return {v for v in X if x[v] <= cap}
    tenth = 0.1 * len(X)
    full = union(len(Vs))
    if len(full) <= tenth:
        return full
    lo, hi = 1, len(Vs)
    while lo < hi:
        mid = (lo + hi) // 2
        if len(union(mid)) > tenth:
            hi = mid
        else:
            lo = mid + 1
    return union(lo)


def ldd(n, arcs, d, rng, c=1.0):
    """Algorithm 1 of [3]: indices of the removed arcs."""
    removed = set()
    stack = [list(range(n))]
    nglob = n
    k = max(1, math.ceil(c * math.log2(max(nglob, 2))))
    while stack:
        X = stack.pop()
        if len(X) <= 1:
            continue
        Xs = set(X)
        inner = [i for i, a in enumerate(arcs) if a[0] in Xs and a[1] in Xs]
        sub = [arcs[i] for i in inner]
        samp = [X[rng.randrange(len(X))] for _ in range(k)]
        cin = Counter()
        cout = Counter()
        for s in samp:
            out = balls(n, sub, X, {s: 0}, rev=False)   # dist(s, v) <= d/4: s is in the in-ball of v
            inn = balls(n, sub, X, {s: 0}, rev=True)    # dist(v, s) <= d/4: s is in the out-ball of v
            for v in X:
                if 4 * out[v] <= d:
                    cin[v] += 1
                if 4 * inn[v] <= d:
                    cout[v] += 1
        Vin = [v for v in X if cin[v] <= 0.6 * k]
        Vout = [v for v in X if v not in set(Vin) and cout[v] <= 0.6 * k]
        Ain = find_balanced(n, sub, X, Vin, d, True, rng, c, nglob)
        Aout = find_balanced(n, sub, X, Vout, d, False, rng, c, nglob)
        sz = len(X)
        d_in = {i for i in inner if arcs[i][0] not in Ain and arcs[i][1] in Ain}
        d_out = {i for i in inner if arcs[i][0] in Aout and arcs[i][1] not in Aout}
        if 0.1 * sz <= len(Ain) <= 0.9 * sz:
            removed |= d_in
            stack += [sorted(Ain), sorted(Xs - Ain)]
            continue
        if 0.1 * sz <= len(Aout) <= 0.9 * sz:
            removed |= d_out
            stack += [sorted(Aout), sorted(Xs - Aout)]
            continue
        rest = Xs - Ain - Aout
        bad = len(Ain | Aout) >= 0.5 * sz
        if not bad and rest:
            u = min(rest)
            f = balls(n, sub, X, {u: 0}, rev=False)
            g = balls(n, sub, X, {u: 0}, rev=True)
            bad = not all(2 * f[v] <= d and 2 * g[v] <= d for v in rest)
        if bad:
            STAT['ldd_return_E'] += 1
            removed |= set(inner)
            continue
        removed |= d_in | d_out
        stack += [sorted(Ain), sorted(Aout - Ain)]
    return removed


def decompose_ldd(n, arcs, d, rng, c=1.0):
    """Lemma 2: idx with equal index = cluster, cut = larger index to smaller."""
    wpos = [(u, v, max(w, 0)) for u, v, w in arcs]
    rem = ldd(n, wpos, d, rng, c)
    kept = [a for i, a in enumerate(wpos) if i not in rem]
    return tarjan(n, kept)


def decompose_scc(n, arcs):
    return tarjan(n, arcs)


def restricted(n, arcs, rng, R, t, c=1.0, decomp=None, hook=None, mode=''):
    """Algorithm 1 of [2] in the form of the note. decomp(l, r) may replace Lemma 2. hook sees each step."""
    L = 1
    while 2 ** L < 2 * n * n:
        L += 1
    Phi = [[0] * n]
    for l in range(1, L + 1):
        new = []
        reps = 1 if l == L else R
        for r in range(reps):
            if l == L:
                idx = decompose_scc(n, arcs)
            elif decomp is not None:
                idx = decomp(l, r)
            else:
                idx = decompose_ldd(n, arcs, 2 ** l, rng, c)
            inside = [a for a in arcs if idx[a[0]] == idx[a[1]]]
            best = None
            pool = Phi if mode != 'noprev' else [[0] * n]
            for phi in pool:
                dd = alternate(n, inside, phi, t, mode)
                best = dd if best is None else [min(x, y) for x, y in zip(best, dd)]
            sgn = {'nooffset': 0, 'wrongdir': 1}.get(mode, -1)
            pot = [best[v] + sgn * idx[v] * n for v in range(n)]
            new.append(pot)
            if hook:
                hook(l, r, L, idx, best, pot, Phi)
        Phi = new
    return Phi[0]


def phase_params(B):
    if B >= 5:
        return (B + 2) // 3, 2
    if B >= 3:
        return 2, 1
    if B == 2:
        return 1, 1
    return 1, 0


def scale_potential(n, arcs, solver, stats=None):
    """Lemma 5 and its surroundings. Returns a potential for x, or None for 'negative cycle'."""
    xarcs = [(u, v, 2 * ((n + 1) * w + 1)) for u, v, w in arcs]
    phi = [0] * n
    while True:
        low = min((w + phi[u] - phi[v] for u, v, w in xarcs), default=0)
        if low >= 0:
            return phi
        B = -low
        rho, alpha = phase_params(B)
        r = [(u, v, (w + phi[u] - phi[v]) // rho + alpha) for u, v, w in xarcs]
        assert min(a[2] for a in r) >= -1
        if stats is not None:
            stats['phases'] += 1
            stats['max_B'] = max(stats['max_B'], B)
        kept = [a for a in r if a[2] <= n]
        psi0 = solver(n, kept)
        if psi0 is None:
            return None
        red = [(u, v, w + psi0[u] - psi0[v]) for u, v, w in kept]
        if any(a[2] < 0 for a in red):
            return None
        d0 = oracle_shift(n, red, [-psi0[v] for v in range(n)])
        psi = [d0[v] + psi0[v] for v in range(n)]
        if any(w + psi[u] - psi[v] < 0 for u, v, w in r):
            return None
        new = [phi[v] + rho * psi[v] for v in range(n)]
        lown = min(w + new[u] - new[v] for u, v, w in xarcs)
        assert lown >= -rho * alpha, 'Lemma 5, second claim'
        assert rho * alpha < B
        phi = new


def bf_solver(n, arcs):
    """A restricted solver with no randomness: Bellman-Ford."""
    return bf_all(n, arcs)


def stack_solver(rng, R=2, t=4, c=1.0):
    return lambda n, arcs: restricted(n, arcs, rng, R, t, c)


def distances_from_potential(n, arcs, phi, s):
    """Section 5, Distances. Returns dist, parent."""
    xarcs = [(u, v, 2 * ((n + 1) * w + 1)) for u, v, w in arcs]
    red = [(u, v, w + phi[u] - phi[v]) for u, v, w in xarcs]
    off = [INF] * n
    off[s] = 0
    dr = oracle(n, red, off)
    dx = [dr[v] - phi[s] + phi[v] if dr[v] < INF else INF for v in range(n)]
    dist = [dx[v] // (2 * (n + 1)) if dx[v] < INF else INF for v in range(n)]
    par = [None] * n
    for u, v, w in xarcs:
        if dx[u] < INF and dx[v] < INF and dx[u] + w == dx[v] and v != s:
            par[v] = u
    return dist, par, dx


def johnson_from_potential(n, arcs, phi):
    """Section 5: dist(V, .) for w from a potential for x. The offsets are -phi in the reduced weights, not 0."""
    xarcs = [(u, v, 2 * ((n + 1) * w + 1)) for u, v, w in arcs]
    red = [(u, v, w + phi[u] - phi[v]) for u, v, w in xarcs]
    dr = oracle_shift(n, red, [-phi[v] for v in range(n)])
    return [(dr[v] + phi[v]) // (2 * (n + 1)) for v in range(n)]


def theorem1(n, arcs, s, solver, stats=None):
    """Returns ('dist', dist, parent, psi) or ('neg',)."""
    phi = scale_potential(n, arcs, solver, stats)
    if phi is None:
        return ('neg',)
    dist, par, dx = distances_from_potential(n, arcs, phi, s)
    psi = johnson_from_potential(n, arcs, phi)
    return ('dist', dist, par, psi)
