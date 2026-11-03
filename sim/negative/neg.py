"""Negative weights by polylogarithmically many nonnegative SSSP calls: logic of notes/NEGATIVE.md, centrally.

The oracle is Dijkstra. No rounds, no labels. The truth is Bellman-Ford and networkx, and every instance is checked for planarity.
Run with python -I:
  neg.py <seed> <seconds> [big]    restricted instances, full bottom-up algorithm with the LDD of [3]
  neg.py scale <seed> <seconds>    Scaling Lemma, general weights, with and without negative cycles
  neg.py full <seed> <seconds>     whole stack with the restricted algorithm inside the Scaling Lemma
  neg.py flow <seed> <seconds>     maximum flow and perfect matching in the dual on the whole stack
  neg.py ctl <seed> <seconds> [t]  negative controls, t = 2 by default
  neg.py event <seed> <seconds> <t> <R>  output wrong only if the success event failed
"""
import collections, heapq, json, math, os, random, sys, time
import networkx as nx
import numpy as np
from scipy.sparse import csr_matrix
from scipy.sparse.csgraph import connected_components, dijkstra as sp_dijkstra

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "maxflow"))
import mf

INF = 1 << 60
CAP = 1 << 52        # floats inside scipy stay exact below this
ST = collections.Counter()


# ---------- oracle and truth

def oracle(n, U, V, W, off):
    """dist from a virtual source with offsets off (INF = no arc). One call of the oracle of [3, Def. 24]."""
    ST['n.oracle'] += 1
    assert len(W) == 0 or W.min() >= 0
    src = np.flatnonzero(off < INF)
    assert len(src) == 0 or off[src].min() >= 0
    u = np.concatenate([U + 1, np.zeros(len(src), dtype=np.int64)])
    v = np.concatenate([V + 1, src + 1])
    w = np.concatenate([W, off[src]]).astype(np.float64)
    assert len(w) == 0 or w.max() < CAP
    d = sp_dijkstra(csr_matrix((w, (u, v)), shape=(n + 1, n + 1)), directed=True, indices=0)[1:]
    out = np.full(n, INF, dtype=np.int64)
    fin = np.isfinite(d)
    out[fin] = np.rint(d[fin]).astype(np.int64)
    return out


def bellman_ford(n, U, V, W, x0=None):
    """Exact distances from a virtual source with offsets x0, or None if a negative cycle is reachable."""
    x = np.zeros(n, dtype=np.int64) if x0 is None else x0.copy()
    for it in range(n + 2):
        y = x.copy()
        np.minimum.at(y, V, np.where(x[U] < INF, x[U] + W, INF))
        if (y == x).all():
            return x
        x = y
    return None


# ---------- low diameter decomposition, Algorithm 1 and 2 of [3], centrally; merged oracle calls are counted per depth

def sub_oracle(n, U, V, W, X, off, rev=False):
    inX = np.zeros(n, dtype=bool)
    inX[X] = True
    keep = inX[U] & inX[V]
    return oracle(n, V[keep], U[keep], W[keep], off) if rev else oracle(n, U[keep], V[keep], W[keep], off)


def find_balanced(n, U, V, W, X, Vs, d, kind, rng, c, calls):
    """FindBalancedSet. kind 'in': the union of in-balls, so reversed graph."""
    size = len(X)
    Vs = list(Vs)
    rng.shuffle(Vs)
    p = min(c * math.log2(max(n, 2)) / d, 1.0)
    cap = d // 4
    ds = {}
    for v in Vs:
        k = 0
        while k < cap and rng.random() >= p:
            k += 1
        ds[v] = k

    def union(i):
        off = np.full(n, INF, dtype=np.int64)
        for v in Vs[:i]:
            off[v] = cap - ds[v]
        calls[0] += 1
        x = sub_oracle(n, U, V, W, X, off, rev=(kind == 'in'))
        return x <= cap

    lo, hi = 1, len(Vs)
    if not Vs:
        return np.zeros(n, dtype=bool)
    if union(hi).sum() <= 0.1 * size:
        return union(hi)
    while lo < hi:
        mid = (lo + hi) // 2
        if union(mid).sum() > 0.1 * size:
            hi = mid
        else:
            lo = mid + 1
    return union(lo)


def ldd(n, U, V, W, d, rng, c=1.0):
    """E_rem as a boolean array over the arcs, and the merged number of oracle calls."""
    rem = np.zeros(len(U), dtype=bool)
    level = [np.arange(n)]
    merged = 0
    while level:
        nxt, most = [], 0
        for X in level:
            if len(X) <= 1:
                continue
            calls = [0]
            inX = np.zeros(n, dtype=bool)
            inX[X] = True
            k = max(1, math.ceil(c * math.log2(max(n, 2))))
            cnt_in, cnt_out = np.zeros(n, dtype=np.int64), np.zeros(n, dtype=np.int64)
            for s in rng.choices(list(X), k=k):
                off = np.full(n, INF, dtype=np.int64)
                off[s] = 0
                cnt_in += sub_oracle(n, U, V, W, X, off) <= d // 4
                cnt_out += sub_oracle(n, U, V, W, X, off, rev=True) <= d // 4
                calls[0] += 2
            light_in = inX & (cnt_in <= 0.6 * k)
            light_out = inX & ~light_in & (cnt_out <= 0.6 * k)
            Ain = find_balanced(n, U, V, W, X, np.flatnonzero(light_in).tolist(), d, 'in', rng, c, calls)
            Aout = find_balanced(n, U, V, W, X, np.flatnonzero(light_out).tolist(), d, 'out', rng, c, calls)
            arcs_in = inX[U] & inX[V]
            del_in = arcs_in & ~Ain[U] & Ain[V]
            del_out = arcs_in & Aout[U] & ~Aout[V]
            sz = len(X)
            if 0.1 * sz <= Ain.sum() <= 0.9 * sz:
                rem |= del_in
                nxt += [np.flatnonzero(Ain), np.flatnonzero(inX & ~Ain)]
            elif 0.1 * sz <= Aout.sum() <= 0.9 * sz:
                rem |= del_out
                nxt += [np.flatnonzero(Aout), np.flatnonzero(inX & ~Aout)]
            else:
                rest = inX & ~Ain & ~Aout
                ok = (Ain | Aout).sum() < 0.5 * sz
                if rest.any():
                    u = int(np.flatnonzero(rest)[0])
                    off = np.full(n, INF, dtype=np.int64)
                    off[u] = 0
                    a = sub_oracle(n, U, V, W, X, off) <= d // 2
                    b = sub_oracle(n, U, V, W, X, off, rev=True) <= d // 2
                    calls[0] += 2
                    ok = ok and (a[rest].all() and b[rest].all())
                if not ok:
                    ST['n.ldd_giveup'] += 1
                    rem |= arcs_in
                    continue
                rem |= del_in | del_out
                nxt += [np.flatnonzero(Ain), np.flatnonzero(inX & Aout & ~Ain)]
            most = max(most, calls[0])
        merged += most
        level = [X for X in nxt if len(X) > 1]
    ST['n.ldd_calls'] += merged
    ST['max.ldd_calls'] = max(ST['max.ldd_calls'], merged)
    return rem


def scc_order(n, U, V, keep):
    """Component of each vertex and an index, increasing along every kept arc between components."""
    g = csr_matrix((np.ones(int(keep.sum()), dtype=np.int8), (U[keep], V[keep])), shape=(n, n))
    k, lab = connected_components(g, directed=True, connection='strong')
    adj = [set() for _ in range(k)]
    indeg = [0] * k
    for a, b in zip(lab[U[keep]].tolist(), lab[V[keep]].tolist()):
        if a != b and b not in adj[a]:
            adj[a].add(b)
            indeg[b] += 1
    q = collections.deque(i for i in range(k) if indeg[i] == 0)
    rank = [0] * k
    r = 0
    while q:
        x = q.popleft()
        rank[x] = r
        r += 1
        for y in adj[x]:
            indeg[y] -= 1
            if indeg[y] == 0:
                q.append(y)
    assert r == k
    return lab, np.array(rank, dtype=np.int64)[lab]


# ---------- few negative edges, by alternation

def few_neg(n, U, V, W, phi, t, mode=''):
    """Lemma 1 of the note on the arcs given: d(v) <= w(P) for every path P to v with at most t negative arcs in w_phi."""
    wp = W + phi[U] - phi[V]
    pos = wp >= 0
    Up, Vp, Wp = U[pos], V[pos], wp[pos]
    Un, Vn, Wn = U[~pos], V[~pos], wp[~pos]
    shift = (-phi).min()
    A = oracle(n, Up, Vp, Wp, -phi - shift) + shift
    if mode == 't0':
        return A + phi
    for it in range(t):
        B = A.copy()
        np.minimum.at(B, Vn, A[Un] + Wn)
        if (B == A).all():
            break
        ST['n.alternations'] += 1
        ST['max.alternations'] = max(ST['max.alternations'], it + 1)
        sh = B.min()
        A = oracle(n, Up, Vp, Wp, B - sh) + sh
    return A + phi


# ---------- the restricted problem

def restricted(n, U, V, W, rng, R=3, t=8, c=1.0, mode='', truth=False):
    """Algorithm 1 of [2]; returns a potential. mode names a negative control. truth turns on the checks by Bellman-Ford."""
    L = math.ceil(math.log2(2 * n * n)) if n > 1 else 1
    Wp = np.maximum(W, 0)
    Phi = [np.zeros(n, dtype=np.int64)]
    prev_idx = []
    for l in range(1, L + 1):
        new, idxs = [], []
        reps = 1 if l == L else R
        if mode == 'oneR':
            reps = 1
        for r in range(reps):
            if l == L and mode != 'ldd_top':
                rem = np.zeros(len(U), dtype=bool)
            else:
                rem = ldd(n, U, V, Wp, 2 ** l, rng, c)
            ST['n.ldd'] += 1
            lab, idx = scc_order(n, U, V, ~rem)
            same = lab[U] == lab[V]
            Us, Vs, Ws = U[same], V[same], W[same]
            best = None
            for phi in ([np.zeros(n, dtype=np.int64)] if mode == 'noprev' else Phi):
                d = few_neg(n, Us, Vs, Ws, phi, t, mode)
                best = d if best is None else np.minimum(best, d)
            if mode == 'nomin':
                best = few_neg(n, Us, Vs, Ws, Phi[0], t, mode)
            if truth:
                dist = bellman_ford(n, Us, Vs, Ws)
                ST['chk.A'] += n
                if dist is None:
                    ST['FAIL.restricted_cycle'] += 1
                else:
                    miss = int((best != dist).sum())
                    assert (best >= dist).all()
                    ST['miss.A'] += miss
                    if miss == 0:
                        ST['n.A_exact'] += 1
                    else:
                        ST['n.A_inexact'] += 1
                    # the success event: cuts of a shortest path on the previous level
                    if prev_idx:
                        need = needed_t(n, Us, Vs, Ws, dist, prev_idx)
                        ST['max.need_t'] = max(ST['max.need_t'], need)
                    ST['max.hops'] = max(ST['max.hops'], hops(n, Us, Vs, Ws, dist))
            if mode == 'nooffset':
                phi_new = best
            elif mode == 'wrongdir':
                phi_new = best + idx * n
            else:
                phi_new = best - idx * n
            new.append(phi_new)
            idxs.append(idx)
            if truth:
                wn = W + phi_new[U] - phi_new[V]
                back = idx[U] > idx[V]
                ST['chk.B'] += int((~back).sum())
                ST['miss.B'] += int(((wn < 0) & ~back).sum())
                ST['max.cut_frac_x1000'] = max(ST['max.cut_frac_x1000'], int(1000 * back.sum() / max(len(U), 1)))
        Phi = new
        prev_idx = idxs
    return Phi[0]


def hops(n, U, V, W, dist):
    """Largest number of arcs on a shortest path from the set, over the vertices, with ties to fewer arcs."""
    tight = dist[U] + W == dist[V]
    Ut, Vt = U[tight], V[tight]
    x = np.where(dist == 0, 0, INF)
    for _ in range(n + 1):
        y = x.copy()
        np.minimum.at(y, Vt, np.where(x[Ut] < INF, x[Ut] + 1, INF))
        if (y == x).all():
            break
        x = y
    return int(x[x < INF].max()) if (x < INF).any() else 0


def needed_t(n, U, V, W, dist, prev_idx):
    """max over v of the least, over the previous level's repetitions, of the back arcs on a shortest path to v."""
    worst = 0
    tight = dist[U] + W == dist[V]
    Ut, Vt = U[tight], V[tight]
    best = np.full(n, INF, dtype=np.int64)
    for idx in prev_idx:
        back = (idx[Ut] > idx[Vt]).astype(np.int64)
        # fewest back arcs over tight paths from a vertex with dist 0: at most n passes, usually few
        x = np.where(dist == 0, 0, INF)
        for _ in range(n + 1):
            y = x.copy()
            np.minimum.at(y, Vt, np.where(x[Ut] < INF, x[Ut] + back, INF))
            if (y == x).all():
                break
            x = y
        best = np.minimum(best, x)
    finite = best[best < INF]
    return int(finite.max()) if len(finite) else 0


def is_restricted(n, U, V, W):
    return bool((W >= -1).all()) and bellman_ford(n, U, V, W - 1) is not None


# ---------- scaling lemma

def scale_up(W, n):
    return 2 * ((n + 1) * W + 1)


def scaling(n, U, V, W, solver, st=None):
    """Scaling Lemma: a potential for x = 2((n + 1)w + 1), or None if the restricted solver fails to give one.

    solver(n, U, V, r) returns a potential for a restricted r or for one of its subgraphs. Arcs above n are dropped and restored as in the note."""
    x = scale_up(W, n)
    phi = np.zeros(n, dtype=np.int64)
    while True:
        xp = x + phi[U] - phi[V]
        B = int(-xp.min()) if len(xp) else 0
        if B <= 0:
            return phi
        if B <= 1:
            rho, alpha = 1, 0
        elif B <= 2:
            rho, alpha = 1, 1
        elif B <= 4:
            rho, alpha = 2, 1
        else:
            rho, alpha = (B + 2) // 3, 2
        r = np.floor_divide(xp, rho) + alpha
        if st is not None:
            st['n.phases'] += 1
            st['chk.r_low'] += 1
            if r.min() < -1:
                st['FAIL.r_low'] += 1
        keep = r <= n
        psi = solver(n, U[keep], V[keep], r[keep])
        if psi is None:
            return None
        # one more nonnegative call: distances from the set in the graph without the heavy arcs
        rp = r[keep] + psi[U[keep]] - psi[V[keep]]
        if len(rp) and rp.min() < 0:
            return None
        sh = (-psi).min()
        dd = oracle(n, U[keep], V[keep], rp, -psi - sh) + sh + psi
        if (r + dd[U] - dd[V]).min() < 0:
            return None
        phi = phi + rho * dd
        xn = x + phi[U] - phi[V]
        if st is not None:
            st['chk.scale_low'] += 1
            if xn.min() < -rho * alpha:
                st['FAIL.scale_low'] += 1
            st['max.phases_B'] = max(st['max.phases_B'], B)


def distances(n, U, V, W, s, phi):
    """Distances from s in w from a potential for x = 2((n + 1)w + 1), by one oracle call."""
    x = scale_up(W, n)
    xp = x + phi[U] - phi[V]
    off = np.full(n, INF, dtype=np.int64)
    off[s] = 0
    d = oracle(n, U, V, xp, off)
    out = np.full(n, INF, dtype=np.int64)
    r = d < INF
    out[r] = np.floor_divide(d[r] - phi[s] + phi[r], 2 * (n + 1))
    return out


# ---------- instances

def plane_digraph(rng, big):
    Vs, E = mf.graph(rng, big)
    n = len(Vs)
    if n < 2:
        return plane_digraph(rng, big)
    idx = {v: i for i, v in enumerate(sorted(Vs))}
    E = [(idx[a], idx[b]) for a, b in E]
    g = nx.Graph(E)
    assert nx.check_planarity(g)[0]
    ST['chk.planar'] += 1
    arcs = set()
    mode = rng.choice(['both', 'both', 'one', 'mix'])
    for a, b in E:
        if a == b:
            continue
        if mode == 'both' or (mode == 'mix' and rng.random() < 0.5):
            arcs |= {(a, b), (b, a)}
        elif rng.random() < 0.5:
            arcs.add((a, b))
        else:
            arcs.add((b, a))
    arcs = sorted(arcs)
    return n, np.array([a for a, b in arcs], dtype=np.int64), np.array([b for a, b in arcs], dtype=np.int64)


def snake_instance(rng, big):
    """Grid with a snake: k arcs of weight -1, then one of weight k - 1, so shortest paths are long and carry weight in G>=0."""
    m = 26 if big else 11
    a, b = rng.randrange(3, m), rng.randrange(3, m)
    n = a * b
    order = [i * b + (j if i % 2 == 0 else b - 1 - j) for i in range(a) for j in range(b)]
    k = rng.choice([2, 3, 5, 9, 17])
    p = np.zeros(n, dtype=np.int64)
    cur = 0
    for i, v in enumerate(order):
        p[v] = cur
        cur += 2 if (i + 1) % (k + 1) else 2 - k
    snake = {(u, v) for u, v in zip(order, order[1:])}
    q = rng.choice([0, 0, 0.05, 0.3])
    arcs = []
    for i in range(a):
        for j in range(b):
            x = i * b + j
            for y in ([x + 1] if j + 1 < b else []) + ([x + b] if i + 1 < a else []):
                on = (x, y) in snake or (y, x) in snake
                if on or rng.random() < q:
                    arcs += [(x, y), (y, x)]
    arcs = sorted(arcs)
    assert nx.check_planarity(nx.Graph(arcs))[0]
    ST['chk.planar'] += 1
    U = np.array([x for x, y in arcs], dtype=np.int64)
    V = np.array([y for x, y in arcs], dtype=np.int64)
    diff = p[U] - p[V]
    W = 1 + np.maximum(0, -2 - diff) + diff
    off = np.array([(x, y) not in snake and (y, x) not in snake for x, y in arcs])
    W[off] += np.array([rng.randrange(0, 4) for _ in range(int(off.sum()))], dtype=np.int64)
    keep = W <= n
    return n, U[keep], V[keep], W[keep], 'snake'


def restricted_instance(rng, big):
    """Weights 1 + c(e) + p(u) - p(v) >= -1, so every cycle has mean at least 1."""
    if rng.random() < 0.5:
        return snake_instance(rng, big)
    n, U, V = plane_digraph(rng, big)
    mode = rng.choice(['walk', 'deep', 'layers', 'rand', 'saw', 'saw', 'saw', 'saw'])
    if mode in ('walk', 'saw'):
        # along a long path: rises of 2 give arcs of weight -1, drops of s give arcs of weight 1 + s, so shortest paths mix both
        order = dfs_order(n, U, V, rng)
        rise, big_step = rng.choice([0.6, 0.8, 0.9]), rng.choice([2, 4, 8, 16])
        p = np.zeros(n, dtype=np.int64)
        cur = 0
        for v in order:
            if mode == 'walk':
                cur += rng.choice([-2, -1, 0, 1, 2])
            elif rng.random() < rise:
                cur += 2
            else:
                cur -= rng.randrange(1, big_step + 1)
            p[v] = cur
    elif mode == 'deep':   # steep along a BFS order: long chains of arcs of weight -1
        order = bfs_order(n, U, V, rng)
        p = np.zeros(n, dtype=np.int64)
        for i, v in enumerate(order):
            p[v] = 2 * i
    elif mode == 'layers':
        order = bfs_order(n, U, V, rng)
        p = np.zeros(n, dtype=np.int64)
        w = rng.choice([2, 3, 5, 9])
        for i, v in enumerate(order):
            p[v] = 2 * (i // w)
    else:
        p = np.array([rng.randrange(0, 2 * n) for _ in range(n)], dtype=np.int64)
    slack = rng.choice([0, 0, 1, 3])
    diff = p[U] - p[V]
    c = np.maximum(0, -2 - diff) + np.array([rng.randrange(0, slack + 1) for _ in range(len(U))], dtype=np.int64)
    W = 1 + c + diff
    keep = W <= n        # the graph G' of the note: arcs above n are dropped
    return n, U[keep], V[keep], W[keep], mode


def dfs_order(n, U, V, rng):
    adj = [[] for _ in range(n)]
    for a, b in zip(U.tolist(), V.tolist()):
        adj[a].append(b)
        adj[b].append(a)
    s = rng.randrange(n)
    seen, out, stack = set(), [], [s]
    while stack:
        x = stack.pop()
        if x in seen:
            continue
        seen.add(x)
        out.append(x)
        nb = adj[x][:]
        rng.shuffle(nb)
        stack += nb
    return out + [v for v in range(n) if v not in seen]


def bfs_order(n, U, V, rng):
    adj = [[] for _ in range(n)]
    for a, b in zip(U.tolist(), V.tolist()):
        adj[a].append(b)
        adj[b].append(a)
    s = rng.randrange(n)
    seen, q, out = {s}, collections.deque([s]), []
    while q:
        x = q.popleft()
        out.append(x)
        nb = adj[x][:]
        rng.shuffle(nb)
        for y in nb:
            if y not in seen:
                seen.add(y)
                q.append(y)
    return out + [v for v in range(n) if v not in seen]


def general_instance(rng, big):
    """Weights c(e) + p(u) - p(v) with many tight arcs, so zero cycles, optionally lowered into a negative cycle."""
    n, U, V = plane_digraph(rng, big)
    W0 = rng.choice([3, 30, 1000, 10 ** 5])
    p = np.array([rng.randrange(-W0, W0 + 1) for _ in range(n)], dtype=np.int64)
    zero = rng.choice([0.2, 0.6, 0.95])
    c = np.array([0 if rng.random() < zero else rng.randrange(0, W0 + 1) for _ in range(len(U))], dtype=np.int64)
    W = c + p[U] - p[V]
    neg = rng.random() < 0.3
    if neg:
        # lower one arc on a cycle, if there is one, by more than the slack of its cheapest closing path
        i = rng.randrange(len(U))
        W = W.copy()
        W[i] -= rng.randrange(1, 2 * W0 + 2)
    return n, U, V, W


def sample_solver(R, t, c, rng, truth, mode=''):
    return lambda n, U, V, r: restricted(n, U, V, r, rng, R=R, t=t, c=c, mode=mode, truth=truth)


def exact_solver(n, U, V, r):
    """Restricted problem solved by Bellman-Ford, for the tests of the Scaling Lemma alone."""
    x = bellman_ford(n, U, V, r)
    return x


# ---------- lanes

def lane(seed, secs, big):
    rng = random.Random(seed)
    ST.clear()
    end = time.time() + secs
    while time.time() < end:
        n, U, V, W, kind = restricted_instance(rng, big)
        if not is_restricted(n, U, V, W):
            ST['n.not_restricted'] += 1
            continue
        ST['runs'] += 1
        ST['fam.' + kind] += 1
        ST['max.n'] = max(ST['max.n'], n)
        before = ST['n.oracle']
        phi = restricted(n, U, V, W, rng, R=3, t=8, c=1.0, truth=True)
        ST['max.calls'] = max(ST['max.calls'], ST['n.oracle'] - before)
        wn = W + phi[U] - phi[V]
        if len(wn) and wn.min() < 0:
            ST['FAIL.final'] += 1
    print(json.dumps(dict(sorted(ST.items()))))


def lane_scale(seed, secs):
    rng = random.Random(seed)
    ST.clear()
    end = time.time() + secs
    while time.time() < end:
        n, U, V, W = general_instance(rng, False)
        truth = bellman_ford(n, U, V, W)
        ST['runs'] += 1
        phi = scaling(n, U, V, W, exact_solver, ST)
        if truth is None:
            ST['n.neg_cycle'] += 1
            if phi is not None and (scale_up(W, n) + phi[U] - phi[V]).min() >= 0:
                ST['FAIL.neg_missed'] += 1
            continue
        if phi is None or (scale_up(W, n) + phi[U] - phi[V]).min() < 0:
            ST['FAIL.no_potential'] += 1
            continue
        s = rng.randrange(n)
        off = np.full(n, INF, dtype=np.int64)
        off[s] = 0
        bf = bellman_ford(n, U, V, W, off)
        d = distances(n, U, V, W, s, phi)
        ST['chk.dist'] += n
        if not (d == bf).all():
            ST['FAIL.dist'] += 1
    print(json.dumps(dict(sorted(ST.items()))))


def lane_full(seed, secs):
    rng = random.Random(seed)
    ST.clear()
    end = time.time() + secs
    while time.time() < end:
        n, U, V, W = general_instance(rng, False)
        truth = bellman_ford(n, U, V, W)
        ST['runs'] += 1
        ST['max.n'] = max(ST['max.n'], n)
        before = ST['n.oracle']
        phi = scaling(n, U, V, W, sample_solver(3, 8, 1.0, rng, False), ST)
        ST['max.calls'] = max(ST['max.calls'], ST['n.oracle'] - before)
        if truth is None:
            ST['n.neg_cycle'] += 1
            if phi is not None and (scale_up(W, n) + phi[U] - phi[V]).min() >= 0:
                ST['FAIL.neg_missed'] += 1
            continue
        if phi is None or (scale_up(W, n) + phi[U] - phi[V]).min() < 0:
            ST['FAIL.no_potential'] += 1
            continue
        s = rng.randrange(n)
        off = np.full(n, INF, dtype=np.int64)
        off[s] = 0
        bf = bellman_ford(n, U, V, W, off)
        d = distances(n, U, V, W, s, phi)
        ST['chk.dist'] += n
        if not (d == bf).all():
            ST['FAIL.dist'] += 1
    print(json.dumps(dict(sorted(ST.items()))))


# ---------- flow and perfect matching on the whole stack

def dual_arcs(darts, rgt, length):
    """Dual dart of d: from rgt(d) to lft(d). Keeps the lightest arc per ordered pair; a negative loop is reported as None."""
    best = {}
    for d in darts:
        a, b = rgt[d], rgt[d[1], d[0]]
        if a == b:
            if length[d] < 0:
                return None
            continue
        if (a, b) not in best or best[a, b] > length[d]:
            best[a, b] = length[d]
    return best


def feasible(nf, best, solver, exact):
    """Face potentials psi with psi(lft) - psi(rgt) <= length, or None if the dual has a negative cycle."""
    if best is None:
        return None
    if not best:
        return np.zeros(nf, dtype=np.int64)
    U = np.array([a for a, b in best], dtype=np.int64)
    V = np.array([b for a, b in best], dtype=np.int64)
    W = np.array(list(best.values()), dtype=np.int64)
    if exact:
        return bellman_ford(nf, U, V, W)
    phi = scaling(nf, U, V, W, solver)
    if phi is None or (scale_up(W, nf) + phi[U] - phi[V]).min() < 0:
        return None
    # Johnson distances in w from all faces, from the potential of x
    xp = scale_up(W, nf) + phi[U] - phi[V]
    sh = (-phi).min()
    d = oracle(nf, U, V, xp, -phi - sh) + sh + phi
    return np.floor_divide(d, 2 * (nf + 1))


def solve_flow(I, solver, exact):
    """Largest beta with a feasible dual, then the flow, as in the Maximum Flow Theorem of [1]."""
    darts = list(I.darts)
    U = max(I.cap.values(), default=0)
    lo, hi = 0, len(I.V) * U + 1
    path = set(I.R)
    rev = {(b, a) for a, b in I.R}
    def lengths(beta):
        return {d: I.cap.get(d, 0) - (beta if d in path else 0) + (beta if d in rev else 0) for d in darts}
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if feasible(I.nf, dual_arcs(darts, I.rgt, lengths(mid)), solver, exact) is not None:
            lo = mid
        else:
            hi = mid
    psi = feasible(I.nf, dual_arcs(darts, I.rgt, lengths(lo)), solver, exact)
    assert psi is not None
    # psi from a virtual source over all faces, so lft - rgt <= length on the dual dart from rgt to lft
    f = {d: int(psi[I.rgt[d[1], d[0]]] - psi[I.rgt[d]]) + (lo if d in path else 0) - (lo if d in rev else 0) for d in darts}
    return lo, f


def check_flow(I, f, val):
    for d in I.darts:
        if f[d] != -f[d[1], d[0]] or f[d] > I.cap.get(d, 0):
            return False
    net = collections.Counter()
    for (a, b), x in f.items():
        net[a] += x
    return all(net[v] == (val if v == I.s else -val if v == I.t else 0) for v in I.V) or I.s == I.t


def nx_maxflow(I):
    g = nx.DiGraph()
    g.add_nodes_from(I.V)
    for (a, b), c in I.cap.items():
        if c > 0:
            g.add_edge(a, b, capacity=c)
    return nx.maximum_flow_value(g, I.s, I.t) if I.s != I.t else 0


def bipartite_instance(rng):
    """Planar bipartite graph, half of the time with a perfect matching planted."""
    a, b = rng.randrange(2, 9), rng.randrange(2, 9)
    E = set()
    for i in range(a):
        for j in range(b):
            x = i * b + j
            if j + 1 < b:
                E.add((x, x + 1))
            if i + 1 < a:
                E.add((x, x + b))
    n = a * b
    keep = rng.choice([1.0, 0.8, 0.6])
    E2 = {e for e in E if rng.random() < keep}
    V, E3 = mf.largest(set(range(n)), sorted(E2))
    return V, E3


def perfect_matching(V, E, solver, exact):
    """Miller-Naor with demands +1 and -1 on the two sides; returns the matching, or None if the dual has a negative cycle, or 'odd'."""
    g = nx.Graph(E)
    g.add_nodes_from(V)
    side = nx.bipartite.color(g)
    b = {v: (1 if side[v] == 0 else -1) for v in V}
    if sum(b.values()) != 0:
        return 'odd'
    # f0 on a spanning tree with net outflow b
    s = min(V)
    par, order = {s: None}, [s]
    for x in order:
        for y in sorted(g[x]):
            if y not in par:
                par[y] = x
                order.append(y)
    sub = dict(b)
    f0 = collections.Counter()
    for x in reversed(order[1:]):
        p = par[x]
        f0[x, p] += sub[x]
        f0[p, x] -= sub[x]
        sub[p] += sub[x]
    _, rgt, nf, _ = mf.embed(V, E)
    darts = list(rgt)
    # capacities: from side 0 to side 1 at most 1, and the reverse at most 0
    cap = {d: (1 if side[d[0]] == 0 else 0) for d in darts}
    length = {d: cap[d] - f0[d] for d in darts}
    psi = feasible(nf, dual_arcs(darts, rgt, length), solver, exact)
    if psi is None:
        return None
    f = {d: int(psi[rgt[d[1], d[0]]] - psi[rgt[d]]) + f0[d] for d in darts}
    M = [d for d in darts if f[d] == 1 and side[d[0]] == 0]
    for d in darts:
        assert f[d] <= cap[d]
    return M


def lane_flow(seed, secs):
    rng = random.Random(seed)
    ST.clear()
    end = time.time() + secs
    while time.time() < end:
        solver = sample_solver(2, 8, 1.0, rng, False)
        exact = rng.random() < 0.7        # most runs use the exact test for the outer logic; the rest the whole stack
        if rng.random() < 0.5:
            Vs, E = mf.graph(rng, False)
            if len(Vs) < 3 or len(Vs) > (60 if exact else 25):
                continue
            E = sorted({(min(a, b), max(a, b)) for a, b in E if a != b})
            _, cap = mf.capacities(Vs, E, rng)
            cap = {d: (c if c < 1000 else c % 40) for d, c in cap.items()}
            s, t = mf.far(Vs, E, rng)
            if s == t:
                continue
            I = mf.Inst(Vs, E, cap, s, t)
            assert nx.check_planarity(nx.Graph(E))[0]
            ST['chk.planar'] += 1
            val, f = solve_flow(I, solver, exact)
            ST['runs.flow'] += 1
            ST['runs.flow_stack'] += 0 if exact else 1
            if val != nx_maxflow(I):
                ST['FAIL.flow_value'] += 1
            if not check_flow(I, f, val):
                ST['FAIL.flow_check'] += 1
        else:
            V, E = bipartite_instance(rng)
            if len(V) < 2 or len(V) > (64 if exact else 25):
                continue
            assert nx.check_planarity(nx.Graph(E))[0]
            ST['chk.planar'] += 1
            g = nx.Graph(E)
            g.add_nodes_from(V)
            if not nx.is_connected(g):
                continue
            side = nx.bipartite.color(g)
            if sum(1 if side[v] == 0 else -1 for v in V) != 0:
                ST['n.odd'] += 1
                continue
            top = {v for v in V if side[v] == 0}
            size = len(nx.bipartite.hopcroft_karp_matching(g, top_nodes=top)) // 2
            has = size * 2 == len(V)
            M = perfect_matching(V, E, solver, exact)
            ST['runs.match'] += 1
            ST['runs.match_stack'] += 0 if exact else 1
            ST['n.has_pm'] += has
            if has:
                if M is None or len(M) * 2 != len(V) or len({x for d in M for x in d}) != len(V):
                    ST['FAIL.match'] += 1
            elif M is not None:
                ST['FAIL.match_false'] += 1
    print(json.dumps(dict(sorted(ST.items()))))


CTL = ['t0', 'oneR', 'noprev', 'nomin', 'nooffset', 'wrongdir']


def controls(seed, secs, t=2):
    out = {}
    for m in CTL:
        rng = random.Random(seed)
        ST.clear()
        end = time.time() + secs
        res = collections.Counter()
        while time.time() < end:
            n, U, V, W, kind = restricted_instance(rng, True)
            if not is_restricted(n, U, V, W):
                continue
            res['runs'] += 1
            phi = restricted(n, U, V, W, rng, R=2, t=t, c=1.0, mode=m)
            if len(U) and (W + phi[U] - phi[V]).min() < 0:
                res['FAIL.final'] += 1
        out[m] = dict(res)
    rng = random.Random(seed)
    end = time.time() + secs
    res = collections.Counter()
    while time.time() < end:
        n, U, V, W, kind = restricted_instance(rng, True)
        if not is_restricted(n, U, V, W):
            continue
        res['runs'] += 1
        phi = restricted(n, U, V, W, rng, R=2, t=t, c=1.0)
        if len(U) and (W + phi[U] - phi[V]).min() < 0:
            res['FAIL.final'] += 1
    out['clean'] = dict(res)
    print(json.dumps(out))


def lane_event(seed, secs, t=2, R=2):
    """The deterministic part of Proposition 4: with small t and R the success event often fails, and only then may the output fail."""
    rng = random.Random(seed)
    res = collections.Counter()
    end = time.time() + secs
    while time.time() < end:
        n, U, V, W, kind = restricted_instance(rng, True)
        if not len(U) or not is_restricted(n, U, V, W):
            continue
        ST.clear()
        phi = restricted(n, U, V, W, rng, R=R, t=t, c=1.0, truth=True)
        bad = (W + phi[U] - phi[V]).min() < 0
        event = ST['max.need_t'] <= t
        res['runs'] += 1
        res['event' if event else 'no_event'] += 1
        res['max.n'] = max(res['max.n'], n)
        res['max.need_t'] = max(res['max.need_t'], ST['max.need_t'])
        if bad:
            res['wrong_output'] += 1
        if ST['miss.A'] or ST['miss.B']:
            res['inexact_step'] += 1
        if event and (bad or ST['miss.A'] or ST['miss.B']):
            res['FAIL.event_but_wrong'] += 1
    print(json.dumps(dict(sorted(res.items()))))


def self_check():
    """The oracle against a plain Dijkstra, zero arcs included."""
    rng = random.Random(1)
    for _ in range(200):
        n = rng.randrange(2, 30)
        arcs = sorted({(rng.randrange(n), rng.randrange(n)) for _ in range(3 * n)} - {(i, i) for i in range(n)})
        U = np.array([a for a, b in arcs], dtype=np.int64)
        V = np.array([b for a, b in arcs], dtype=np.int64)
        W = np.array([rng.choice([0, 0, 1, 5]) for _ in arcs], dtype=np.int64)
        off = np.array([rng.choice([INF, 0, 3, 7]) for _ in range(n)], dtype=np.int64)
        d = {v: int(off[v]) for v in range(n)}
        h = [(x, v) for v, x in d.items() if x < INF]
        heapq.heapify(h)
        adj = collections.defaultdict(list)
        for a, b, w in zip(U.tolist(), V.tolist(), W.tolist()):
            adj[a].append((b, w))
        while h:
            x, v = heapq.heappop(h)
            if x > d[v]:
                continue
            for y, w in adj[v]:
                if x + w < d[y]:
                    d[y] = x + w
                    heapq.heappush(h, (x + w, y))
        assert oracle(n, U, V, W, off).tolist() == [d[v] for v in range(n)]


if __name__ == '__main__':
    self_check()
    a = sys.argv[1:]
    if a[0] == 'scale':
        lane_scale(int(a[1]), float(a[2]))
    elif a[0] == 'full':
        lane_full(int(a[1]), float(a[2]))
    elif a[0] == 'flow':
        lane_flow(int(a[1]), float(a[2]))
    elif a[0] == 'event':
        lane_event(int(a[1]), float(a[2]), int(a[3]), int(a[4]))
    elif a[0] == 'ctl':
        controls(int(a[1]), float(a[2]), int(a[3]) if len(a) > 3 else 2)
    else:
        lane(int(a[0]), float(a[1]), len(a) > 2)
