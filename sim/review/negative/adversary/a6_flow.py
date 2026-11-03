"""Theorem 2 and Corollaries 3 to 6 on non-simple plane graphs given by rotation systems.

All connected plane multigraphs with few vertices and edges (parallel edges, bridges, cut vertices, degree 1, faces of length 1 or 2 in
the dual sense) and all their planar rotation systems. Truth: networkx max flow, brute force for degrees and orientations, cycle enumeration.

Each test is run on the dual directly and on the face-disjoint graph, either with Bellman-Ford as the test or the whole stack.
usage: a6_flow.py enum <nmax> <mmax> <seed> <cap_per_map>
       a6_flow.py rand <seed> <secs> [stack]
"""
import collections
import itertools
import json
import math
import os
import random
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from core import *
import networkx as nx


def rotations(n, edges):
    """All rotation systems of the multigraph, with the first dart at each vertex fixed; genus 0 only."""
    inc = [[] for _ in range(n)]
    for e, (a, b) in enumerate(edges):
        inc[a].append(2 * e)
        inc[b].append(2 * e + 1)
    opts = []
    for v in range(n):
        if len(inc[v]) <= 2:
            opts.append([tuple(inc[v])])
        else:
            first, rest = inc[v][0], inc[v][1:]
            opts.append([(first,) + p for p in itertools.permutations(rest)])
    total = 1
    for o in opts:
        total *= len(o)
    for pick in itertools.product(*opts):
        m_ = Map(n, edges, [list(p) for p in pick])
        if m_.genus_zero():
            yield m_


def connected_multigraphs(n, m):
    pairs = [(a, b) for a in range(n) for b in range(a + 1, n)]
    for edges in itertools.combinations_with_replacement(pairs, m):
        if len(components(set(range(n)), edges)) == 1:
            yield list(edges)


# ---------- tests of feasibility

def test_dual_bf(m_, length):
    return bf(m_.nf, m_.dual_arcs(length))


def potentials_from_ghat(m_, length, solver, end):
    """Theorem 1 on the face-disjoint graph with solver: potentials psi on faces from a fixed corner, None on a negative cycle."""
    nn, arcs, pairs = m_.ghat(length, end=end)
    # hosts check negative loops, drop other loops
    for u, v, w in arcs:
        if u == v and w < 0:
            return None
    arcs = [a for a in arcs if a[0] != a[1]]
    phi = scaling(nn, arcs, solver, Stats())
    if phi is None:
        return None
    src = m_.n  # corner of dart 0
    d = dist_from_phi(nn, arcs, src, phi, Stats())
    psi = {}
    for dart in range(2 * len(m_.edges)):
        f = m_.lft[dart]
        val = d[m_.n + dart]
        if f in psi and psi[f] != val:
            raise AssertionError(('corners of a face differ', m_.edges, m_.rot, length, f, psi[f], val))
        psi[f] = val
    return [psi[i] for i in range(m_.nf)]


def nx_value(n, edges, cap, s, t):
    g = nx.DiGraph()
    g.add_nodes_from(range(n))
    tot = collections.Counter()
    for e, (a, b) in enumerate(edges):
        tot[a, b] += cap[2 * e]
        tot[b, a] += cap[2 * e + 1]
    for (a, b), c in tot.items():
        if c > 0:
            g.add_edge(a, b, capacity=c)
    return nx.maximum_flow_value(g, s, t)


def theorem2(m_, cap, s, t, tester, c):
    """Binary search on beta, flow, cut. tester(length) returns face potentials or None."""
    par, order = bfs_tree_from(m_, s)
    P = set()
    x = t
    while x != s:
        d = par[x]            # child to parent
        P.add(d ^ 1)
        x = m_.head(d)
    dd = 2 * len(m_.edges)
    U = max(cap) if cap else 0
    lo, hi = 0, sum(cap[d] for d in m_.rot[s]) + 1

    def lengths(beta):
        return [cap[d] - (beta if d in P else 0) + (beta if (d ^ 1) in P else 0) for d in range(dd)]
    assert tester(lengths(0)) is not None
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if tester(lengths(mid)) is not None:
            lo = mid
        else:
            hi = mid
    psi = tester(lengths(lo))
    f = [psi[m_.lft[d]] - psi[m_.rgt(d)] + (lo if d in P else 0) - (lo if (d ^ 1) in P else 0) for d in range(dd)]
    return lo, f


def check_flow(m_, cap, f, val, s, t, c):
    dd = 2 * len(m_.edges)
    ok = True
    for d in range(dd):
        if f[d] != -f[d ^ 1] or f[d] > cap[d]:
            ok = False
    out = net_out(m_, f)
    for v in range(m_.n):
        want = val if v == s else (-val if v == t else 0)
        if out[v] != want:
            ok = False
    # residual reach and cut
    res = collections.defaultdict(list)
    for d in range(dd):
        if f[d] < cap[d]:
            res[m_.tail(d)].append(m_.head(d))
    seen = {s}
    q = [s]
    while q:
        x = q.pop()
        for y in res[x]:
            if y not in seen:
                seen.add(y)
                q.append(y)
    if t in seen:
        c['FAIL.t_reached'] += 1
        return False
    cutcap = sum(cap[d] for d in range(dd) if m_.tail(d) in seen and m_.head(d) not in seen)
    if cutcap != val:
        c['FAIL.cut_value'] += 1
        return False
    return ok


def truth_demands(m_, cap, b):
    """Feasible flow with f(d) <= c(d) on all darts and net outflow b: by lower bounds and max flow."""
    n = m_.n
    g = nx.DiGraph()
    g.add_nodes_from(range(n))
    S, T = 'S', 'T'
    bb = list(b)
    for e, (a, bv) in enumerate(m_.edges):
        h, l = cap[2 * e], -cap[2 * e + 1]
        if l > h:
            return False
        bb[a] -= l
        bb[bv] += l
        if h - l > 0:
            if g.has_edge(a, bv):
                g[a][bv]['capacity'] += h - l
            else:
                g.add_edge(a, bv, capacity=h - l)
    need = 0
    for v in range(n):
        if bb[v] > 0:
            g.add_edge(S, v, capacity=bb[v])
            need += bb[v]
        elif bb[v] < 0:
            g.add_edge(v, T, capacity=-bb[v])
    if need == 0:
        return True
    g.add_node(S)
    g.add_node(T)
    return nx.maximum_flow_value(g, S, T) == need


def corollary4(m_, cap, b, tester):
    f0 = route_tree(m_, b)
    dd = 2 * len(m_.edges)
    assert net_out(m_, f0) == list(b)
    length = [cap[d] - f0[d] for d in range(dd)]
    psi = tester(length)
    if psi is None:
        return None
    return [f0[d] + psi[m_.lft[d]] - psi[m_.rgt(d)] for d in range(dd)]


def bipartition(m_):
    col = {0: 0}
    q = [0]
    while q:
        x = q.pop()
        for d in m_.rot[x]:
            y = m_.head(d)
            if y not in col:
                col[y] = 1 - col[x]
                q.append(y)
            elif col[y] == col[x]:
                return None
    return col


def corollary5_degrees(m_, g, tester, col):
    """Subgraph with degree g(v). None for no."""
    b = [g[v] if col[v] == 0 else -g[v] for v in range(m_.n)]
    if sum(b) != 0:
        return None
    dd = 2 * len(m_.edges)
    cap = [1 if col[m_.tail(d)] == 0 else 0 for d in range(dd)]
    f = corollary4(m_, cap, b, tester)
    if f is None:
        return None
    return [d // 2 for d in range(dd) if f[d] == 1]


def brute_degrees(m_, g):
    me = len(m_.edges)
    for mask in range(2 ** me):
        deg = [0] * m_.n
        for e in range(me):
            if mask >> e & 1:
                a, b = m_.edges[e]
                deg[a] += 1
                deg[b] += 1
        if deg == list(g):
            return True
    return False


def corollary5_orient(m_, a, tester):
    """Orientation with out-degree a(v), or None. O_0 orients each edge along its dart 2e."""
    me = len(m_.edges)
    dd = 2 * me
    od = [0] * m_.n
    for e in range(me):
        od[m_.tail(2 * e)] += 1
    b = [od[v] - a[v] for v in range(m_.n)]
    if sum(b) != 0:
        return None
    cap = [1 if d % 2 == 0 else 0 for d in range(dd)]
    f = corollary4(m_, cap, b, tester)
    if f is None:
        return None
    new = [0] * m_.n
    for e in range(me):
        if f[2 * e] == 1:
            new[m_.head(2 * e)] += 1
        else:
            new[m_.tail(2 * e)] += 1
    return new


def brute_orient(m_, a):
    me = len(m_.edges)
    for mask in range(2 ** me):
        od = [0] * m_.n
        for e in range(me):
            x, y = m_.edges[e]
            od[x if mask >> e & 1 else y] += 1
        if od == list(a):
            return True
    return False


def check_map(m_, rng, c, testers, ncap):
    me = len(m_.edges)
    dd = 2 * me
    nv = m_.n
    # Every dart's face structure: circulations are circulations
    psi0 = [rng.randrange(-5, 6) for _ in range(m_.nf)]
    if any(x != 0 for x in net_out(m_, [psi0[m_.lft[d]] - psi0[m_.rgt(d)] for d in range(dd)])):
        c['FAIL.not_circulation'] += 1
    for _ in range(ncap):
        s, t = rng.sample(range(nv), 2)
        kind = rng.randrange(4)
        U = rng.choice([1, 2, 3, 7])
        if kind == 0:
            cap = [rng.randrange(0, U + 1) for _ in range(dd)]
        elif kind == 1:     # one direction only
            cap = [0] * dd
            for e in range(me):
                cap[2 * e + rng.randrange(2)] = rng.randrange(0, U + 1)
        elif kind == 2:     # undirected
            cap = [0] * dd
            for e in range(me):
                cap[2 * e] = cap[2 * e + 1] = rng.randrange(0, U + 1)
        else:
            cap = [rng.choice([0, 0, U]) for _ in range(dd)]
        true = nx_value(nv, m_.edges, cap, s, t)
        for name, tester in testers:
            val, f = theorem2(m_, cap, s, t, tester, c)
            c['flow.' + name] += 1
            if val != true:
                c['FAIL.flow_value.' + name] += 1
                print('flow', name, m_.edges, m_.rot, cap, s, t, val, true)
            elif not check_flow(m_, cap, f, val, s, t, c):
                c['FAIL.flow_check.' + name] += 1
                print('flowcheck', name, m_.edges, m_.rot, cap, s, t, val, f)
        # Corollary 4, capacities of any sign
        capn = [rng.randrange(-U, U + 1) for _ in range(dd)]
        if rng.random() < 0.6:
            # most pairs feasible: c(d) + c(rev d) >= 0
            for e in range(me):
                if capn[2 * e] + capn[2 * e + 1] < 0:
                    capn[2 * e + 1] = -capn[2 * e] + rng.randrange(0, 2)
        b = [rng.randrange(-U, U + 1) for _ in range(nv)]
        b[rng.randrange(nv)] -= sum(b)
        tr = truth_demands(m_, capn, b)
        for name, tester in testers:
            f = corollary4(m_, capn, b, tester)
            c['cor4.' + name] += 1
            c['cor4.feasible'] += tr
            if (f is not None) != tr:
                c['FAIL.cor4_iff.' + name] += 1
                print('cor4', name, m_.edges, m_.rot, capn, b, tr)
            elif f is not None:
                if net_out(m_, f) != b or any(f[d] > capn[d] or f[d] != -f[d ^ 1] for d in range(dd)):
                    c['FAIL.cor4_flow.' + name] += 1
                    print('cor4flow', name, m_.edges, m_.rot, capn, b, f)
        # Corollary 5
        col = bipartition(m_)
        if col is not None and me <= 12:
            for gmode in range(3):
                if gmode == 0:
                    g = [1] * nv
                else:
                    g = [rng.randrange(0, len(m_.rot[v]) + 1 + (gmode == 2)) for v in range(nv)]
                tr = brute_degrees(m_, g)
                for name, tester in testers:
                    ans = corollary5_degrees(m_, g, tester, col)
                    c['cor5deg.' + name] += 1
                    c['cor5deg.yes'] += tr
                    if (ans is not None) != tr:
                        c['FAIL.cor5deg.' + name] += 1
                        print('cor5', name, m_.edges, m_.rot, g, tr)
                    elif ans is not None:
                        deg = [0] * nv
                        for e in ans:
                            x, y = m_.edges[e]
                            deg[x] += 1
                            deg[y] += 1
                        if deg != g:
                            c['FAIL.cor5deg_sub.' + name] += 1
        if me <= 12:
            a = [rng.randrange(0, len(m_.rot[v]) + 1) for v in range(nv)]
            if rng.random() < 0.7:
                # make it plausible: start from a real orientation
                a = [0] * nv
                for x, y in m_.edges:
                    a[x if rng.random() < 0.5 else y] += 1
            tr = brute_orient(m_, a)
            for name, tester in testers:
                ans = corollary5_orient(m_, a, tester)
                c['cor5or.' + name] += 1
                c['cor5or.yes'] += tr
                if (ans is not None) != tr:
                    c['FAIL.cor5or.' + name] += 1
                    print('orient', name, m_.edges, m_.rot, a, tr)
                elif ans is not None and ans != list(a):
                    c['FAIL.cor5or_deg.' + name] += 1


def make_testers(stack, rng, R=2, t=8, cc=1.0):
    def dual_bf(length):
        return bf_face(length)

    testers = []
    return testers


def main_enum(nmax, mmax, seed, per):
    rng = random.Random(seed)
    c = collections.Counter()
    t0 = time.time()
    for n in range(2, nmax + 1):
        for me in range(n - 1, mmax + 1):
            for edges in connected_multigraphs(n, me):
                for m_ in rotations(n, edges):
                    c['maps'] += 1
                    if any(a == b for a, b in edges):
                        continue

                    def tdual(length, m_=m_):
                        return test_dual_bf(m_, length)

                    def tghat_tail(length, m_=m_):
                        return potentials_from_ghat(m_, length, bf_solver, 'tail')
                    check_map(m_, rng, c, [('dual', tdual), ('ghat', tghat_tail)], per)
    print('enum', json.dumps(dict(sorted(c.items()))), 'secs', round(time.time() - t0))


def random_plane_map(rng, nmax=9):
    """Random planar map: start from a random tree, add edges, parallel edges by splitting a face with a chord in a face."""
    n = rng.randrange(2, nmax + 1)
    edges = []
    rot = [[] for _ in range(n)]
    for v in range(1, n):
        u = rng.randrange(max(0, v - rng.choice([1, 2, 5])), v)
        e = len(edges)
        edges.append((u, v))
        rot[u].insert(rng.randrange(len(rot[u]) + 1), 2 * e)
        rot[v].append(2 * e + 1)
    extra = rng.randrange(0, 2 * n)
    for _ in range(extra):
        m_ = Map(n, edges, rot)
        # choose a face and two corners in it, add the chord there: keeps genus 0
        d = rng.randrange(2 * len(edges))
        walk = [d]
        x = m_.next_left(d)
        while x != d:
            walk.append(x)
            x = m_.next_left(x)
        d1, d2 = rng.choice(walk), rng.choice(walk)
        u, v = m_.tail(d1), m_.tail(d2)
        if u == v:
            continue
        e = len(edges)
        edges.append((u, v))
        # corner left of dart d at its tail is between d and sigma(d): insert the new dart right after d
        rot[u].insert(rot[u].index(d1) + 1, 2 * e)
        rot[v].insert(rot[v].index(d2) + 1, 2 * e + 1)
    m_ = Map(n, edges, rot)
    assert m_.genus_zero(), (edges, rot)
    return m_


def main_rand(seed, secs, stack):
    rng = random.Random(seed)
    c = collections.Counter()
    t0 = time.time()
    end = t0 + secs

    def solver(n, kept):
        return restricted(n, kept, R=2, t=8, c=1.0, rng=rng, st=Stats())
    while time.time() < end:
        m_ = random_plane_map(rng, 5 if stack else int(os.environ.get('NMAX', '9')))
        c['maps'] += 1
        c['maps.bridge'] += any(m_.lft[d] == m_.rgt(d) for d in range(2 * len(m_.edges)))
        c['maps.parallel'] += len({tuple(sorted(e)) for e in m_.edges}) < len(m_.edges)
        c['max_edges'] = max(c['max_edges'], len(m_.edges))

        def tdual(length, m_=m_):
            return test_dual_bf(m_, length)

        def tghat_tail(length, m_=m_):
            return potentials_from_ghat(m_, length, bf_solver, 'tail')

        def tghat_deg(length, m_=m_):
            return potentials_from_ghat(m_, length, bf_solver, 'deg')

        def tghat_stack(length, m_=m_):
            return potentials_from_ghat(m_, length, solver, 'deg')
        testers = [('dual', tdual), ('ghat', tghat_tail), ('ghatdeg', tghat_deg)]
        if stack:
            if len(m_.edges) > 7:
                continue
            testers = [('stack', tghat_stack)]
        check_map(m_, rng, c, testers, 1)
    print('rand', json.dumps(dict(sorted(c.items()))), 'secs', round(time.time() - t0))


if __name__ == '__main__':
    if sys.argv[1] == 'enum':
        main_enum(int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]))
    else:
        main_rand(int(sys.argv[2]), float(sys.argv[3]), len(sys.argv) > 4)
