"""Minimum-weight arborescence by O(log n) calls of a nonnegative SSSP oracle: logic of notes/DMST.md, centrally.

The oracle is Dijkstra on the physical graph, with weights as the note gives them. No rounds, no labels.
The truth is networkx and a separate Chu-Liu/Edmonds that computes the weight. Every instance is checked for planarity.
Run with python -I:
  dmst.py <seed> <seconds> [big]   main lane
  dmst.py branch <seed> <seconds>  maximum-weight branching, by a virtual root
  dmst.py ctl <seed> <seconds>     negative controls
  dmst.py scale                    long nested instances, iterations against log n
"""
import collections, heapq, json, math, os, random, sys, time
import networkx as nx
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'maxflow'))
import mf

INF = float('inf')


def chu_liu(n, arcs, r):
    """Weight of a minimum arborescence by plain contraction, separate from the code under test and from networkx."""
    arcs, total = list(arcs), 0
    while True:
        best = {}
        for u, v, w in arcs:
            if u != v and v != r and (v not in best or w < best[v][1]):
                best[v] = (u, w)
        nodes = {r} | {u for u, _, _ in arcs} | {v for _, v, _ in arcs}
        if any(v != r and v not in best for v in nodes):
            return None
        total += sum(w for _, w in best.values())
        mark, cyc = {}, {}
        for v in nodes:
            x, seen = v, []
            while x != r and x not in mark and x not in seen:
                seen.append(x)
                x = best[x][0]
            if x != r and x in seen:
                c = seen[seen.index(x):]
                for y in c:
                    cyc[y] = c[0]
            for y in seen:
                mark[y] = 1
        if not cyc:
            return total
        f = lambda x: cyc.get(x, x)
        arcs = [(f(u), f(v), w - best[v][1] if v in best else w) for u, v, w in arcs if f(u) != f(v)]
        r = f(r)


class Run:
    """Arcs are (u, v) on physical vertices. `edges` are the network edges, so a soft contraction can use them both ways."""

    def __init__(self, V, W, r, st, mode='ok', rng=None):
        self.V, self.w, self.r, self.st, self.mode, self.rng = list(V), dict(W), r, st, mode, rng
        self.nbr = collections.defaultdict(set)
        self.ins = collections.defaultdict(list)
        for u, v in W:
            self.nbr[u].add(v)
            self.nbr[v].add(u)
            self.ins[v].append(u)
        self.sid = {v: v for v in V}
        self.inarc = {}
        self.total = 0
        self.levels = []

    def members(self):
        m = collections.defaultdict(set)
        for v in self.V:
            m[self.sid[v]].add(v)
        return m

    def init(self):
        ins = collections.defaultdict(list)
        for (u, v) in self.w:
            if v != self.r:
                ins[v].append((u, v))
        for v in self.V:
            if v == self.r:
                continue
            e = min(ins[v], key=lambda a: (self.w[a], a))
            m = self.w[e]
            self.total += m
            for a in ins[v]:
                self.w[a] -= m
            self.inarc[v] = e

    def components(self):
        """Weak components of H. The spanning forest leaves out one meta-arc per active component, and its head is on the cycle."""
        parent = {s: s for s in set(self.sid.values())}

        def find(x):
            while parent[x] != x:
                parent[x] = parent[parent[x]]
                x = parent[x]
            return x
        heads = {}
        order = sorted(self.inarc)
        if self.rng:
            self.rng.shuffle(order)
        for s in order:
            t = self.sid[self.inarc[s][0]]
            a, b = find(s), find(t)
            if a == b:
                heads[a] = s
            else:
                parent[a] = b
        comp = collections.defaultdict(set)
        for s in parent:
            comp[find(s)].add(s)
        out = []
        rootc = find(self.sid[self.r])
        for c, ss in comp.items():
            if c == rootc:
                if c in heads:
                    self.st['FAIL.root_has_cycle'] += 1
                continue
            h = heads.get(c)
            if h is None:
                self.st['FAIL.no_cycle'] += 1
                continue
            # the head lies on the cycle of H: check against the definition
            if h not in self.cycle_of(h):
                self.st['FAIL.head_off_cycle'] += 1
            out.append((h, ss))
        return out

    def cycle_of(self, s):
        seen = []
        x = s
        while x not in seen:
            seen.append(x)
            x = self.sid[self.inarc[x][0]]
        return seen[seen.index(x):]

    def rev_oracle(self, comps):
        """One oracle call for all active components: reversed distances to the head, inside the component.
        Inside a super-vertex both directions of a network edge have weight 1. A meta-arc costs K(Kw + 1) with K = n + 1, so a
        tree path visits a super-vertex in one stretch, and all weights are positive, so tight arcs form a forest.
        dist is recovered by floor division."""
        n = len(self.V)
        K = n + 1
        scomp = {}
        for i, (h, ss) in enumerate(comps):
            for s in ss:
                scomp[s] = i
        into = collections.defaultdict(list)
        for x in self.V:
            for y in self.nbr[x]:
                if self.sid[x] == self.sid[y] and x != y:
                    into[y].append((x, 1))
        for (x, y), w in self.w.items():
            sx, sy = self.sid[x], self.sid[y]
            if sx != sy and scomp.get(sx, -1) == scomp.get(sy, -2):
                into[y].append((x, K * (K * max(w, 0) + 1)))   # only a control can make w negative, and it is counted there
        d, nxt = {}, {}
        pq = []
        heads = {h for h, _ in comps}
        for x in self.V:
            if self.sid[x] in heads:
                d[x] = 0
                nxt[x] = None
                pq.append((0, x))
        heapq.heapify(pq)
        self.st['n.oracle'] += 1
        while pq:
            dx, x = heapq.heappop(pq)
            if dx > d[x]:
                continue
            for y, w in into[x]:
                if y not in d or dx + w < d[y]:
                    d[y] = dx + w
                    nxt[y] = x
                    heapq.heappush(pq, (d[y], y))
        return {x: d[x] // K // K for x in d}, nxt

    def step(self, comps):
        mode = self.mode
        dist, nxt = self.rev_oracle(comps)
        scomp = {}
        for i, (h, ss) in enumerate(comps):
            for s in ss:
                scomp[s] = i
        vcomp = {x: scomp[self.sid[x]] for x in self.V if self.sid[x] in scomp}
        best = {}
        for (x, y), w in self.w.items():
            i = vcomp.get(y)
            if i is not None and vcomp.get(x) != i and y != self.r:
                b = w + (0 if mode == 'nodist' else dist.get(y, INF))
                if b < INF and (i not in best or (b, x, y) < best[i]):
                    best[i] = (b, x, y)
        snap = dict(self.sid), dict(self.inarc)
        mem = self.members()
        rec = []
        new_w = dict(self.w)
        new_sid = dict(self.sid)
        new_inarc = dict(self.inarc)
        for i, (h, ss) in enumerate(comps):
            if i not in best:
                self.st['FAIL.no_entering_arc'] += 1
                continue
            beta, u, v = best[i]
            if mode == 'cycleonly':
                A = set(self.cycle_of(h))
            elif mode == 'wholecomp':
                A = set(ss)
            else:
                A = {s for s in ss if dist_of(self, mem[s], dist) <= beta}
            if h not in A:
                self.st['FAIL.head_not_in_A'] += 1
            phys = set().union(*(mem[s] for s in A))
            self.total += beta
            for y in phys:
                for x in self.ins[y]:
                    if x not in phys:
                        nw = self.w[x, y] + (0 if mode == 'nodist' else dist[y]) - (0 if mode == 'nobeta' else beta)
                        if nw < 0:
                            self.st['FAIL.negative_weight'] += 1
                        if nw > self.w[x, y]:
                            self.st['FAIL.weight_grew'] += 1
                        new_w[x, y] = nw
                    else:
                        new_w[x, y] = 0
            sA = h
            for x in phys:
                new_sid[x] = sA
            for s in A:
                del new_inarc[s]
            new_inarc[sA] = (u, v)
            rec.append((sA, A, phys))
        self.w, self.sid, self.inarc = new_w, new_sid, new_inarc
        self.levels.append((rec, snap, nxt))
        self.st['n.contracted'] += sum(len(A) for _, A, _ in rec)

    def solve(self):
        self.init()
        it = 0
        while True:
            comps = self.components()
            if not comps:
                break
            it += 1
            if it > 2 * len(self.V) + 5:
                self.st['FAIL.no_end'] += 1
                return None
            if it > 1 and 2 * len(comps) > self.last_active:
                self.st['FAIL.no_halving'] += 1
            self.last_active = len(comps)
            self.st['n.active'] += len(comps)
            self.st['max.active'] = max(self.st['max.active'], len(comps))
            self.step(comps)
        self.iters = it
        return self.unpack()

    def unpack(self):
        """The levels in reverse. T holds the in-arc of each current super-vertex."""
        T = dict(self.inarc)
        for rec, (osid, oinarc), nxt in reversed(self.levels):
            for sA, A, phys in rec:
                u, x = T.pop(sA)
                for s in A:
                    if self.mode != 'nohold':
                        T[s] = oinarc[s]
                    elif s in oinarc:
                        T[s] = oinarc[s]
                if self.mode == 'nopath':
                    T[osid[x]] = (u, x)
                    continue
                # the path of the reversed tree from x to the head, as the vertices marked by (T2) see it
                T[osid[x]] = (u, x)
                a, seen = x, {osid[x]}
                while nxt[a] is not None:
                    b = nxt[a]
                    if osid[a] != osid[b]:
                        if osid[b] in seen:
                            self.st['FAIL.reentry'] += 1
                        seen.add(osid[b])
                        T[osid[b]] = (a, b)
                    a = b
                self.st['chk.path'] += 1
        return T


def dist_of(run, phys, dist):
    """All physical vertices of a super-vertex have the same distance."""
    vals = {dist.get(x, INF) for x in phys}
    if len(vals) != 1:
        run.st['FAIL.super_dist'] += 1
    return min(vals)


def check_tree(V, W, r, T, st):
    """T maps a vertex to its in-arc. Returns the weight, or None if T is no arborescence."""
    if set(T) != set(V) - {r}:
        st['bad.tree_cover'] += 1
        return None
    for v, (u, y) in T.items():
        if y != v or (u, y) not in W:
            st['bad.tree_arc'] += 1
            return None
    for v in V:
        x, c = v, 0
        while x != r:
            x = T[x][0]
            c += 1
            if c > len(V):
                st['bad.tree_cycle'] += 1
                return None
    return sum(W[a] for a in T.values())


def instance(rng, big):
    """A plane digraph with positive and zero weights, restricted to what the root reaches."""
    while True:
        Vs, E = mf.graph(rng, big)
        if len(Vs) < 2:
            continue
        idx = {v: i for i, v in enumerate(sorted(Vs))}
        E = sorted({tuple(sorted((idx[a], idx[b]))) for a, b in E if a != b})
        if not E:
            continue
        kind = rng.choice(['both', 'both', 'one', 'mix'])
        top = rng.choice([1, 2, 3, 10, 100, 10 ** 6])
        W = {}
        for a, b in E:
            how = kind if kind != 'mix' else rng.choice(['both', 'one'])
            if how == 'both':
                W[a, b] = rng.randint(0, top)
                W[b, a] = rng.randint(0, top)
            elif rng.random() < .5:
                W[a, b] = rng.randint(0, top)
            else:
                W[b, a] = rng.randint(0, top)
        G = nx.DiGraph(list(W))
        r = rng.choice(sorted(G.nodes))
        R = set(nx.descendants(G, r)) | {r}
        W = {a: w for a, w in W.items() if a[0] in R and a[1] in R}
        if len(R) < 2:
            continue
        assert nx.check_planarity(nx.Graph(list(W)))[0]
        return sorted(R), W, r


def ring_of_rings(rng, k):
    """Cycles of cycles, so that components merge in pairs and contractions nest, with cheap arcs inside and dear arcs out."""
    W = {}
    size = 3
    base = list(range(size ** k))
    for lev in range(k):
        step = size ** lev
        for i in range(0, len(base), step * size):
            for j in range(size):
                a = base[i + j * step]
                b = base[i + ((j + 1) % size) * step]
                W[a, b] = rng.randint(0, 2) + 2 ** lev
                W[b, a] = rng.randint(0, 2) + 2 ** (lev + 1)
    assert nx.check_planarity(nx.Graph(list(W)))[0]
    return base, W, 0


def nested(rng, n):
    """A path with arcs back, in the style of Figure 1 of Fischer and Oshman: Edmonds contracts two vertices at a time."""
    W = {}
    for i in range(n - 1):
        W[i, i + 1] = rng.randint(n, 2 * n)
        W[i + 1, i] = 1 + i + rng.randint(0, 1)
    assert nx.check_planarity(nx.Graph(list(W)))[0]
    return list(range(n)), W, 0


def one(V, W, r, st, mode, rng, fail=True):
    run = Run(V, W, r, st, mode, rng)
    try:
        T = run.solve()
    except KeyError:
        assert mode != 'ok'
        st['FAIL.crash'] += 1
        return None
    if T is None:
        return None
    arcs = [(u, v, w) for (u, v), w in W.items()]
    # ponytail: nx.minimum_spanning_arborescence refuses about 8% of these, its offset looks too small; a maximum branching with a large offset is spanning
    M = len(V) * (max(W.values()) + 1) + 1
    G = nx.DiGraph()
    G.add_nodes_from(V)
    G.add_weighted_edges_from([(u, v, M - w) for (u, v), w in W.items() if v != r])
    B = nx.maximum_branching(G)
    true = sum(W[e] for e in B.edges)
    st['chk.nx'] += 1
    if B.number_of_edges() != len(V) - 1:
        st['FAIL.truth_not_spanning'] += 1
    if chu_liu(len(V), arcs, r) != true:
        st['FAIL.truth_differs'] += 1
    got = check_tree(V, W, r, T, st)
    st['runs'] += 1
    if got is None:
        st['FAIL.tree'] += 1
    elif got != true:
        st['FAIL.weight'] += 1
    if run.total != true:
        st['FAIL.total'] += 1
    st['max.iters'] = max(st['max.iters'], run.iters)
    st['max.n'] = max(st['max.n'], len(V))
    st['n.iters'] += run.iters
    bound = math.floor(math.log2(max(len(V) - 1, 1)))
    st['chk.iters'] += 1
    if run.iters > bound:
        st['FAIL.iters'] += 1
    return run


def lane(seed, secs, big):
    rng = random.Random(seed)
    st = collections.Counter()
    end = time.time() + secs
    while time.time() < end:
        c = rng.random()
        if c < .8:
            V, W, r = instance(rng, big)
        elif c < .87:
            V, W, r = nested(rng, rng.randrange(3, 120 if big else 40))
        elif c < .94:
            V, W, r = pairs(rng, rng.randrange(1, 8 if big else 6))
        else:
            V, W, r = ring_of_rings(rng, rng.randrange(1, 5 if big else 4))
        one(V, W, r, st, 'ok', rng)
    print(json.dumps(dict(sorted((k, int(v)) for k, v in st.items()))))


def branching_lane(seed, secs):
    """Corollary 2. A virtual root has an arc of weight M to each vertex. It is never in an oracle call, since it stays in the root component."""
    rng = random.Random(seed)
    st = collections.Counter()
    end = time.time() + secs
    while time.time() < end:
        V, W, _ = instance(rng, False)
        M = max(W.values())
        star = max(V) + 1
        W2 = {a: M - w for a, w in W.items()}
        for v in V:
            W2[star, v] = M
        run = Run(V + [star], W2, star, st, 'ok', rng)
        T = run.solve()
        got = check_tree(V + [star], W2, star, T, st)
        G = nx.DiGraph()
        G.add_nodes_from(V)
        G.add_weighted_edges_from([(u, v, w) for (u, v), w in W.items()])
        true = sum(W[e] for e in nx.maximum_branching(G).edges)
        st['runs'] += 1
        if got is None or len(V) * M - got != true:
            st['FAIL.branching'] += 1
    print(json.dumps(dict(sorted((k, int(v)) for k, v in st.items()))))


def pairs(rng, k, grid=False):
    """2^k vertices on a path. At each level two blocks are joined by a two-way bridge dearer than all inside, so that the active components merge in pairs and the bound log2 n is met."""
    n = 2 ** k
    W = {}
    for lev in range(k):
        step = 2 ** lev
        for i in range(step - 1, n - 1, 2 * step):
            W[i, i + 1] = 4 ** lev + rng.randint(0, 1)
            W[i + 1, i] = 4 ** lev + rng.randint(0, 1)
    r = n - 1
    assert nx.check_planarity(nx.Graph(list(W)))[0]
    return list(range(n)), W, r


CTL = ['nodist', 'nobeta', 'cycleonly', 'wholecomp', 'nopath']


def controls(seed, secs):
    out = {}
    for m in CTL:
        rng = random.Random(seed)
        st = collections.Counter()
        end = time.time() + secs
        while time.time() < end:
            V, W, r = instance(rng, False)
            one(V, W, r, st, m, rng)
        out[m] = {k: int(st[k]) for k in sorted(st) if k.startswith('FAIL') or k == 'runs'}
    print(json.dumps(out))


def scale():
    rng = random.Random(1)
    for name, make in (('pairs', lambda s: pairs(rng, s)), ('rings', lambda s: ring_of_rings(rng, s)), ('nested', lambda s: nested(rng, s))):
        for s in {'pairs': (6, 8, 10, 12), 'rings': (2, 4, 6, 7), 'nested': (100, 400, 1600)}[name]:
            V, W, r = make(s)
            st = collections.Counter()
            t0 = time.time()
            run = one(V, W, r, st, 'ok', rng)
            print(json.dumps({'fam': name, 'n': len(V), 'iters': run.iters, 'log2n': round(math.log2(len(V)), 1), 'oracle': int(st['n.oracle']), 'secs': round(time.time() - t0, 1), 'fails': {k: int(v) for k, v in st.items() if k.startswith('FAIL')}}), flush=True)


if __name__ == '__main__':
    a = sys.argv[1:]
    if a[0] == 'ctl':
        controls(int(a[1]), float(a[2]))
    elif a[0] == 'branch':
        branching_lane(int(a[1]), float(a[2]))
    elif a[0] == 'scale':
        scale()
    else:
        lane(int(a[0]), float(a[1]), len(a) > 2)
