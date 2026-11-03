"""Corollary 3, Theorem 2 and Corollaries 4, 5, 6 on all small connected planar graphs, through the real Ĝ, against own truths.
Lanes: hat ddl thm2 cor4 cor5 cor6 stack. 'stack' uses the restricted algorithm with the LDD of [3] inside the scaling loop."""
import itertools, os, random, sys, time
from collections import Counter
from fractions import Fraction
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import networkx as nx
from core_check import *
from plane import *

ST = Counter()
EX = {}


def lane_hat(nmax):
    """Lemma statements about Ĝ on all connected planar graphs with one embedding: nodes, planarity, hop diameter, E_C count."""
    for g in all_connected_planar(2, nmax):
        P = Plane(g)
        n = g.number_of_nodes()
        D = nx.diameter(g)
        nid, ES, ER, EC = P.hat()
        h = hat_simple_graph(P)
        ST['hat.graphs'] += 1
        if len(nid) > 7 * n:
            ST['hat.FAIL_size'] += 1
        if not nx.check_planarity(h)[0]:
            ST['hat.FAIL_planar'] += 1
        if not nx.is_connected(h):
            ST['hat.FAIL_conn'] += 1
        elif nx.diameter(h) > 3 * D + 2:
            ST['hat.FAIL_hop'] += 1
        ST['hat.max_hop_excess'] = max(ST['hat.max_hop_excess'], nx.diameter(h) - 3 * D)
        # faces are vertex-disjoint E_R cycles: control of the construction
        # negative control: an E_C edge between corners at DIFFERENT ends of the edge may break planarity
        h2 = nx.Graph()
        h2.add_nodes_from(h.nodes())
        for a, b in ES + ER:
            if a != b:
                h2.add_edge(a, b)
        for d in P.darts:
            if P.pos[d[0]] < P.pos[d[1]]:
                x = nid[('k', P.prv[d])]            # at the tail, in lft(d)
                y = nid[('k', P.prv[(d[1], d[0])])]  # at the head, in rgt(d)
                if x != y:
                    h2.add_edge(x, y)
        if not nx.check_planarity(h2)[0]:
            ST['hat.ctl_wrong_ends_nonplanar'] += 1


def gstar_arcs(P, mu):
    return [(P.rgt[d], P.lft[d], mu[d]) for d in P.darts]


def lane_ddl(nmax, seed, secs):
    """Dual Distance Lemma on the real Ĝ: negative cycle iff G* has one, distances equal, on all corners."""
    rng = random.Random(seed)
    gs = all_connected_planar(2, nmax)
    # exhaustive on graphs with at most 3 edges, lengths -1, 0, 1
    for g in gs:
        P = Plane(g)
        ds = P.darts
        if len(ds) <= 6:
            for vals in itertools.product([-1, 0, 1], repeat=len(ds)):
                check_ddl(P, dict(zip(ds, vals)))
                ST['ddl.exh'] += 1
    end = time.time() + secs
    while time.time() < end:
        g = rng.choice(gs)
        P = Plane(g)
        k = rng.choice([1, 2, 5, 20])
        # half: potential-like lengths, so that few negative cycles appear but dual distances are negative
        if rng.random() < 0.5:
            mu = {d: rng.randrange(-k, k + 1) for d in P.darts}
        else:
            pf = [rng.randrange(-k, k + 1) for _ in range(P.nf)]
            mu = {d: rng.randrange(0, k + 1) + pf[P.rgt[d]] - pf[P.lft[d]] for d in P.darts}
        check_ddl(P, mu)
        ST['ddl.rand'] += 1


def check_ddl(P, mu):
    N, arcs = hat_arcs(P, mu)
    star = gstar_arcs(P, mu)
    t = bf_all(P.nf, star)
    if arcs is None:
        ST['ddl.neg_loop'] += 1
        if t is not None:
            ST['ddl.FAIL_loop'] += 1
        return
    h = bf_all(N, arcs)
    if (h is None) != (t is None):
        ST['ddl.FAIL_neg'] += 1
        return
    if t is None:
        ST['ddl.neg'] += 1
        return
    ST['ddl.noneg'] += 1
    s = P.darts[0]
    sf = P.lft[s]
    a = bf_from(N, arcs, P.nid[('k', s)])
    b = bf_from(P.nf, star, sf)
    for d in P.darts:
        if a[P.nid[('k', d)]] != b[P.lft[d]]:
            ST['ddl.FAIL_dist'] += 1
    # negative control: without the E_R arcs of one face distances do not all agree. Skipped in the count of failures.


def caps_sets(P, rng, k):
    ds = P.darts
    if len(ds) <= 6:
        return [dict(zip(ds, v)) for v in itertools.product([0, 1, 2], repeat=len(ds))]
    out = []
    for _ in range(k):
        U = rng.choice([1, 2, 3, 7, 50])
        kind = rng.choice(['both', 'one', 'sparse'])
        c = {}
        for d in ds:
            if kind == 'both':
                c[d] = rng.randrange(0, U + 1)
            elif kind == 'one':
                c[d] = rng.randrange(0, U + 1) if P.pos[d[0]] < P.pos[d[1]] else 0
            else:
                c[d] = rng.randrange(0, U + 1) if rng.random() < 0.5 else 0
        out.append(c)
    return out


def lane_thm2(nmin, nmax, seed, k, solver=None):
    rng = random.Random(seed)
    for g in all_connected_planar(nmin, nmax):
        P = Plane(g)
        ST['thm2.graphs'] += 1
        pairs = list(itertools.permutations(P.V, 2))
        for cap in caps_sets(P, rng, k):
            if len(pairs) > 8:
                ps = rng.sample(pairs, 8)
            else:
                ps = pairs
            for s, t in ps:
                truth = dinic(P.V, {d: c for d, c in cap.items() if c > 0}, s, t)
                val, f, S, att = theorem2(P, cap, s, t, solver)
                ST['thm2.runs'] += 1
                if val != truth:
                    ST['thm2.FAIL_value'] += 1
                    EX.setdefault('thm2', (list(g.edges()), cap, s, t, val, truth))
                if S is None:
                    ST['thm2.FAIL_nocut'] += 1
                ST['thm2.value_pos'] += val > 0
                # control: lft and rgt swapped in the flow formula must break capacity on some instances
                path = bfs_path(P.g, s, t)
                pth = set(path)
                rv = {(b, a) for a, b in path}
                mu = {d: cap.get(d, 0) - (val if d in pth else 0) + (val if d in rv else 0) for d in P.darts}
                psi = dual_test(P, mu, solver)
                ff = {d: psi[P.rgt[d]] - psi[P.lft[d]] + (val if d in pth else 0) - (val if d in rv else 0) for d in P.darts}
                if check_flow(P, cap, ff, s, t, val):
                    ST['thm2.ctl_swap_fires'] += 1
                # control: with beta = value + 1 a negative cycle must exist
                mu2 = {d: cap.get(d, 0) - (val + 1 if d in pth else 0) + (val + 1 if d in rv else 0) for d in P.darts}
                if dual_test(P, mu2, solver) is not None:
                    ST['thm2.FAIL_beta_plus'] += 1
                # fault injection: one wrong 'negative cycle' on the first attempt is detected, the second attempt is right
                if ST['thm2.runs'] % 7 == 0:
                    v2, f2, S2, att2 = theorem2(P, cap, s, t, solver, fail=lambda attempt, m: attempt == 0 and m > 0)
                    ST['thm2.fault_runs'] += 1
                    ST['thm2.fault_detected'] += att2 == 1 if truth > 0 else 0
                    if v2 != truth:
                        ST['thm2.FAIL_fault_value'] += 1


def tree_flow(P, b):
    """f0 on a BFS tree: net outflow b."""
    root = P.V[0]
    par = {root: None}
    order = [root]
    for x in order:
        for y in sorted(P.g[x]):
            if y not in par:
                par[y] = x
                order.append(y)
    sub = dict(b)
    f0 = Counter()
    for x in reversed(order[1:]):
        p = par[x]
        f0[(x, p)] += sub[x]
        f0[(p, x)] -= sub[x]
        sub[p] += sub[x]
    return f0


def cor4(P, c, b, solver):
    f0 = tree_flow(P, b)
    mu = {d: c[d] - f0[d] for d in P.darts}
    psi = dual_test(P, mu, solver)
    if psi is None:
        return None
    return {d: psi[P.lft[d]] - psi[P.rgt[d]] + f0[d] for d in P.darts}


def cor4_truth_brute(P, c, b):
    """Enumerate integer flows on the edges, for tiny graphs."""
    edges = [d for d in P.darts if P.pos[d[0]] < P.pos[d[1]]]
    ranges = []
    for d in edges:
        lo = -c[(d[1], d[0])]
        hi = c[d]
        if lo > hi:
            return False
        ranges.append(range(lo, hi + 1))
    for vals in itertools.product(*ranges):
        net = Counter()
        for d, x in zip(edges, vals):
            net[d[0]] += x
            net[d[1]] -= x
        if all(net[v] == b[v] for v in P.V):
            return True
    return False


def cor4_truth_flow(P, c, b):
    """Lower bounds -c(rev d) <= f(d) <= c(d); standard reduction to one max flow with a super source."""
    edges = [d for d in P.darts if P.pos[d[0]] < P.pos[d[1]]]
    caps = {}
    ex = Counter()
    for d in edges:
        lo = -c[(d[1], d[0])]
        hi = c[d]
        if lo > hi:
            return False
        if hi > lo:
            caps[d] = caps.get(d, 0) + hi - lo
        ex[d[0]] -= lo
        ex[d[1]] += lo
    # f = lo + y; y must have net outflow b + ex at each vertex
    need = {v: b[v] + ex[v] for v in P.V}
    tot = sum(x for x in need.values() if x > 0)
    for v, x in need.items():
        if x > 0:
            caps[('S', v)] = x
        elif x < 0:
            caps[(v, 'T')] = -x
    return dinic(P.V + ['S', 'T'], caps, 'S', 'T') == tot


def lane_cor4(nmax, seed, secs, solver=None):
    rng = random.Random(seed)
    gs = all_connected_planar(2, nmax)
    end = time.time() + secs
    while time.time() < end:
        g = rng.choice(gs)
        P = Plane(g)
        C = rng.choice([1, 2, 3])
        neg = rng.random() < 0.2
        c = {d: rng.randrange(-1 if neg else 0, C + 1) for d in P.darts}
        vs = P.V
        B = rng.choice([1, 2, 4])
        vals = [rng.randrange(-B, B + 1) for _ in vs]
        vals[-1] -= sum(vals)
        b = dict(zip(vs, vals))
        tr = cor4_truth_flow(P, c, b)
        m = g.number_of_edges()
        if m <= 6 and C <= 2:
            br = cor4_truth_brute(P, c, b)
            ST['cor4.brute'] += 1
            if br != tr:
                ST['cor4.FAIL_truths_differ'] += 1
        f = cor4(P, c, b, solver)
        ST['cor4.runs'] += 1
        ST['cor4.feasible'] += tr
        if (f is not None) != tr:
            ST['cor4.FAIL_decision'] += 1
            EX.setdefault('cor4', (list(g.edges()), c, b))
        if f is not None:
            for d in P.darts:
                if f[d] != -f[(d[1], d[0])] or f[d] > c[d]:
                    ST['cor4.FAIL_cap'] += 1
            net = Counter()
            for d, x in f.items():
                net[d[0]] += x
            if any(net[v] != b[v] for v in vs):
                ST['cor4.FAIL_net'] += 1


def bip_side(g):
    return nx.bipartite.color(g)


def brute_degree_subgraph(P, deg):
    es = [d for d in P.darts if P.pos[d[0]] < P.pos[d[1]]]
    for mask in range(1 << len(es)):
        cnt = Counter()
        for i, d in enumerate(es):
            if mask >> i & 1:
                cnt[d[0]] += 1
                cnt[d[1]] += 1
        if all(cnt[v] == deg[v] for v in P.V):
            return True
    return False


def cor5_degrees(P, side, g, solver):
    b = {v: (g[v] if side[v] == 0 else -g[v]) for v in P.V}
    if sum(b.values()) != 0:
        return 'none'
    c = {d: (1 if side[d[0]] == 0 else 0) for d in P.darts}
    f = cor4(P, c, b, solver)
    if f is None:
        return 'none'
    return {d for d in P.darts if f[d] == 1 and side[d[0]] == 0}


def cor5_orient(P, a, solver):
    O0 = {d for d in P.darts if P.pos[d[0]] < P.pos[d[1]]}
    outd = Counter(d[0] for d in O0)
    b = {v: outd[v] - a[v] for v in P.V}
    if sum(b.values()) != 0:
        return 'none'
    c = {d: (1 if d in O0 else 0) for d in P.darts}
    f = cor4(P, c, b, solver)
    if f is None:
        return 'none'
    return {(d if f[d] == 0 else (d[1], d[0])) for d in O0}


def lane_cor5(nmax, seed, per, solver=None):
    rng = random.Random(seed)
    gs = [g for g in all_connected_planar(2, nmax)]
    for g in gs:
        P = Plane(g)
        m = g.number_of_edges()
        n = g.number_of_nodes()
        if nx.is_bipartite(g) and m <= 14:
            side = bip_side(g)
            ST['cor5.bip_graphs'] += 1
            # perfect matching
            r = cor5_degrees(P, side, {v: 1 for v in P.V}, solver)
            tr = brute_degree_subgraph(P, {v: 1 for v in P.V})
            ST['cor5.pm_has'] += tr
            ST['cor5.pm_runs'] += 1
            if (r != 'none') != tr:
                ST['cor5.FAIL_pm'] += 1
            if r != 'none':
                cnt = Counter()
                for d in r:
                    cnt[d[0]] += 1
                    cnt[d[1]] += 1
                if any(cnt[v] != 1 for v in P.V):
                    ST['cor5.FAIL_pm_check'] += 1
            # prescribed degrees: all of them on tiny graphs, sampled otherwise
            choices = []
            rngs = [range(0, g.degree(v) + 1) for v in P.V]
            tot = 1
            for x in rngs:
                tot *= len(x)
            if tot <= 300:
                choices = list(itertools.product(*rngs))
            else:
                # half realizable by construction
                es = [d for d in P.darts if P.pos[d[0]] < P.pos[d[1]]]
                for _ in range(per):
                    if rng.random() < 0.5:
                        cnt = Counter()
                        for d in es:
                            if rng.random() < 0.5:
                                cnt[d[0]] += 1
                                cnt[d[1]] += 1
                        choices.append(tuple(cnt[v] for v in P.V))
                    else:
                        choices.append(tuple(rng.choice(r) for r in rngs))
            for ch in choices:
                gg = dict(zip(P.V, ch))
                r = cor5_degrees(P, side, gg, solver)
                tr = brute_degree_subgraph(P, gg)
                ST['cor5.deg_runs'] += 1
                ST['cor5.deg_has'] += tr
                if (r != 'none') != tr:
                    ST['cor5.FAIL_deg'] += 1
                    EX.setdefault('cor5deg', (list(g.edges()), gg))
                elif r != 'none':
                    cnt = Counter()
                    for d in r:
                        cnt[d[0]] += 1
                        cnt[d[1]] += 1
                    if any(cnt[v] != gg[v] for v in P.V):
                        ST['cor5.FAIL_deg_check'] += 1
        # orientations, all planar graphs with few edges
        if m <= 11:
            es = [d for d in P.darts if P.pos[d[0]] < P.pos[d[1]]]
            feasible = set()
            for mask in range(1 << m):
                cnt = Counter()
                for i, d in enumerate(es):
                    cnt[d[0] if mask >> i & 1 else d[1]] += 1
                feasible.add(tuple(cnt[v] for v in P.V))
            ST['cor5.orient_graphs'] += 1
            feas = sorted(feasible)
            tests = []
            for _ in range(per):
                tests.append(rng.choice(feas))
                v = [rng.randrange(0, g.degree(x) + 1) for x in P.V]
                tests.append(tuple(v))
            for ch in tests:
                a = dict(zip(P.V, ch))
                r = cor5_orient(P, a, solver)
                ST['cor5.orient_runs'] += 1
                tr = ch in feasible
                ST['cor5.orient_has'] += tr
                if (r != 'none') != tr:
                    ST['cor5.FAIL_orient'] += 1
                    EX.setdefault('cor5or', (list(g.edges()), a))
                elif r != 'none':
                    cnt = Counter(d[0] for d in r)
                    if any(cnt[v] != a[v] for v in P.V) or len(r) != m:
                        ST['cor5.FAIL_orient_check'] += 1


def min_mean_truth(n, arcs):
    g = nx.DiGraph()
    g.add_nodes_from(range(n))
    wt = {}
    for u, v, w in arcs:
        g.add_edge(u, v)
        wt[(u, v)] = w
    best = None
    for cyc in nx.simple_cycles(g):
        tot = sum(wt[(cyc[i], cyc[(i + 1) % len(cyc)])] for i in range(len(cyc)))
        x = Fraction(tot, len(cyc))
        if best is None or x < best:
            best = x
    return best


def cor6(n, arcs, W, solver):
    """Bisection with Theorem 1 as the test. Returns the fraction, or None if there is no cycle."""
    def neg(p, q):
        return scale_potential(n, [(u, v, q * w - p) for u, v, w in arcs], solver) is None
    if not arcs:
        return None, 0
    tests = 0
    # no cycle at all: no negative cycle at p/q = W + 1
    tests += 1
    if not neg(W + 1, 1):
        return None, tests
    lo = Fraction(-W)     # min mean >= lo
    hi = Fraction(W + 1)  # min mean < hi
    while hi - lo >= Fraction(1, n * n):
        mid = (lo + hi) / 2
        tests += 1
        if neg(mid.numerator, mid.denominator):
            hi = mid
        else:
            lo = mid
    # the one fraction with denominator <= n in [lo, hi)
    cand = [Fraction(a, k) for k in range(1, n + 1) for a in range(int(lo * k) - 1, int(hi * k) + 2) if lo <= Fraction(a, k) < hi]
    cand = set(cand)
    assert len(cand) == 1, ('unique fraction', lo, hi, cand)
    return cand.pop(), tests


def lane_cor6(nmax, seed, per, solver=None):
    solver = solver or bf_solver
    rng = random.Random(seed)
    for g in all_connected_planar(2, nmax):
        n = g.number_of_nodes()
        ST['cor6.graphs'] += 1
        for _ in range(per):
            W = rng.choice([1, 3, 10])
            arcs = []
            kind = rng.choice(['both', 'one', 'mix'])
            for a, b in g.edges():
                if kind == 'both' or (kind == 'mix' and rng.random() < 0.5):
                    arcs += [(a, b, rng.randrange(-W, W + 1)), (b, a, rng.randrange(-W, W + 1))]
                elif rng.random() < 0.5:
                    arcs.append((a, b, rng.randrange(-W, W + 1)))
                else:
                    arcs.append((b, a, rng.randrange(-W, W + 1)))
            tr = min_mean_truth(n, arcs)
            got, tests = cor6(n, arcs, W, solver)
            ST['cor6.runs'] += 1
            ST['cor6.tests'] += tests
            ST['cor6.no_cycle'] += tr is None
            if got != tr:
                ST['cor6.FAIL'] += 1
                EX.setdefault('cor6', (n, arcs, got, tr))


if __name__ == '__main__':
    import signal
    def _alarm(*_):  # the alarm survives exec: print what was counted, then stop
        print('ALARM partial', sys.argv[1:], {k: ST[k] for k in sorted(ST)}, flush=True)
        os._exit(0)
    signal.signal(signal.SIGALRM, _alarm)
    a = sys.argv[1:]
    L = a[0]
    if L == 'hat':
        lane_hat(int(a[1]))
    elif L == 'ddl':
        lane_ddl(int(a[1]), int(a[2]), float(a[3]))
    elif L == 'thm2':
        lane_thm2(int(a[1]), int(a[2]), int(a[3]), int(a[4]))
    elif L == 'thm2stack':
        rng = random.Random(int(a[3]))
        lane_thm2(int(a[1]), int(a[2]), int(a[3]), int(a[4]), solver=stack_solver(rng, R=2, t=4))
    elif L == 'cor4':
        lane_cor4(int(a[1]), int(a[2]), float(a[3]))
    elif L == 'cor5':
        lane_cor5(int(a[1]), int(a[2]), int(a[3]))
    elif L == 'cor6':
        lane_cor6(int(a[1]), int(a[2]), int(a[3]))
    print(' '.join(a), {k: ST[k] for k in sorted(ST)})
    print({k: STAT[k] for k in sorted(STAT)})
    if EX:
        print('EX', EX)
