"""LEMMA15's construction with a prescribed root cycle (hypothesis (L3) of notes/MAXFLOW.md).

Mode 'net': the network N of a flow instance, with the slit cycle as root cycle.
Mode 'gen': generic plane graphs of sim/s9, with a face or a fundamental cycle of any balance as root cycle.
Run: python -I forced.py <seed> <seconds> [net|gen], or neg <seed> <seconds> for negative controls.
"""
import collections, json, os, random, sys, time
HERE = os.path.dirname(os.path.abspath(__file__))
for d in ('s9', 'lemma14prime'):
    sys.path.insert(0, os.path.join(HERE, '..', d))
sys.path.insert(0, HERE)
import numpy as np
import networkx as nx
from core import PG, Fail, sp_matrix, add_arc
from engine_r import Engine
from geo import FAMS, virtual_candidates, drawing_ok
from sweep import params
import post_r
import rsweep
import mf


class Forced(Engine):
    def __init__(self, g, rng, cfg, q, swap, keep_T=False):
        cfg = dict(cfg, forced=True)
        super().__init__(g, virtual_candidates(g.pos, g.ends), rng, cfg)
        self.q, self.swap_root = q, swap
        if not keep_T:
            T = nx.Graph()
            T.add_nodes_from(range(g.n))
            T.add_edges_from(zip(q, q[1:]))
            seen, dq = set(q), collections.deque(q)
            while dq:
                x = dq.popleft()
                for y in g.G[x]:
                    if y not in seen:
                        seen.add(y)
                        T.add_edge(x, y)
                        dq.append(y)
            self.T, self.Tadj = T, {v: set(T[v]) for v in range(g.n)}

    def choose_and_split(self, b, cur):
        if b:
            return super().choose_and_split(b, cur)
        B = self.bags[0]
        adj, ncomp, added = self.make_TX(B['X'], cur['gverts'], B['E'])
        assert ncomp == 1
        res = self.children(0, self.q, True, self.swap_root, self.cfg['zall'])
        if res is None:
            return None
        res.update(q=self.q, real=True, TX=adj, swap=self.swap_root, mode='forced', feat={}, ncompT=ncomp, Tbased=added >= 0)
        self.st['forced_roots'] += 1
        return res


def side(g, q):
    rest = [v for v in range(g.n) if v not in set(q)]
    if not rest:
        return None, None
    from core import pip
    ins = pip(g.pos[rest], g.pos[q])
    return int(ins.sum()), len(rest)


def root_glue(eng, st, rng, gam=0.25, wrong=False):
    """(T4a) and Lemma R1 at the root: perturb every child tile piece, glue, compare on the root cycle."""
    g = eng.g
    if len(eng.levels) < 2:
        return
    lv = eng.levels[1]
    arcs = {}
    for t, es in lv['tile_edges'].items():
        carcs, _ = eng.piece(lv, t, es)
        if wrong and rng.random() < 0.15:
            continue
        for (a, b), w in carcs.items():
            add_arc(arcs, a[1], b[1], w * rng.uniform(1, 1 + gam))
    nodes = list(range(g.n))
    exact = {}
    for (a, c) in g.ends:
        exact[a, c] = g.w[a, c]
        exact[c, a] = g.w[c, a]
    src = sorted(eng.bags[0]['S'])
    D, E = sp_matrix(nodes, exact, src), sp_matrix(nodes, arcs, src)
    D, E = D[:, src], E[:, src]
    st['chk.root_pairs'] += D.size
    tol = eng.cfg.get('tol', 1e-7)
    if (E < D - tol).any() or (E > (1 + gam) * D + tol).any():
        st['FAIL.root_glue'] += 1


def run_engine(eng, st, s, rng):
    eng.run()
    post_r.lemma16(eng)
    post_r.e2e(eng)
    root_glue(eng, st, rng)
    bad = rsweep.lv_check(eng, random.Random(s))
    st['chk.lv'] += eng.g.n
    st['FAIL.lv'] += bad
    st['max_depth'] = max(st['max_depth'], eng.maxd)
    for k, v in eng.st.items():
        if k.startswith('FAIL'):
            st[k] += v
        elif k in ('tiles_checked', 'G1_checks', 'hub_checks', 'L16_checks', 'e2e_gluings', 'R1_pairs', 'HX_planar_checks',
                   'B2_checks', 'B34_checks', 'aY_checks', 'forced_roots', 'forced_leaf'):
            st[k] += v
    for k in ('aY_max', 'Tcomp', 'lp47_comp_growth'):
        st['max.' + k] = max(st['max.' + k], eng.mx.get(k, 0))


# ------------------------------------------------------------ the network N of a flow instance
def build_N(I, Lam):
    """N = hat G of G, without the E_C edges of R, with the star centres of interior R vertices split, and no slit corners.
    Nodes: ('c', d) corner before dart d, ('s', v, side) star centre. Returns rotation dict, arcs with length (kind, value),
    and the root cycle q. Lengths: E_R 0, E_C capacities, E_S big."""
    g = I.g
    emb = I.emb
    nxt = lambda d: emb.next_face_half_edge(*d)
    on = {}                                        # v -> (prev on R, next on R)
    Rv = [I.R[0][0]] + [b for a, b in I.R]
    for i, v in enumerate(Rv):
        on[v] = (Rv[i - 1] if i else None, Rv[i + 1] if i + 1 < len(Rv) else None)
    star = {}                                      # corner -> star node, None if the group has one corner only
    groups = collections.defaultdict(list)
    cw = {v: list(emb.neighbors_cw_order(v)) for v in g}
    for v in g:
        p, n = on.get(v, (None, None))
        order = cw[v]
        if p is not None and n is not None:        # corner of w lies between w and its cw successor
            i = order.index(n)
            order = order[i:] + order[:i]
            j = order.index(p)
            groups['s', v, 'A'] = [('c', (v, w)) for w in order[:j]]
            groups['s', v, 'B'] = [('c', (v, w)) for w in order[j:]]
        else:
            groups['s', v, ''] = [('c', (v, w)) for w in order]
    arcs = collections.defaultdict(list)           # undirected edge list with lengths per direction
    M = Lam

    def edge(u, v, kind, luv, lvu):
        if u != v:
            arcs[frozenset((u, v))].append((u, v, kind, luv, lvu))

    for s, cs in groups.items():
        if len(cs) >= 2:
            for c in cs:
                edge(s, c, 'S', None, None)
        elif not cs:
            raise AssertionError('empty star')
    done = set()
    for d in I.darts:
        edge(('c', d), ('c', nxt(d)), 'R', 0, 0)
    for (a, b) in I.darts:
        if frozenset((a, b)) in done:
            continue
        done.add(frozenset((a, b)))
        d = (a, b)
        if I.on_R(d):
            continue
        edge(('c', d), ('c', nxt((b, a))), 'C', d, (b, a))        # at the tail a: d runs rgt -> lft
    return groups, arcs


def slit_cycle(I, groups):
    """The closed curve: right side from s to t, then left side back."""
    nxt = lambda d: I.emb.next_face_half_edge(*d)
    cen = {}
    for s, cs in groups.items():
        for c in cs:
            cen[c] = s
    q = []

    def push(x):
        if not q or q[-1] != x:
            q.append(x)

    def link(a, b):                      # from corner a to corner b at one vertex
        if a == b:
            push(a)
            return
        assert cen[a] == cen[b], (a, b)
        push(a)
        push(cen[a])
        push(b)

    seq = list(I.R)
    for i, d in enumerate(seq):
        push(('c', d))
        n = ('c', nxt(d))
        if i + 1 < len(seq):
            link(n, ('c', seq[i + 1]))
        else:
            push(n)
    last = ('c', (seq[-1][1], seq[-1][0]))
    link(q[-1], last)
    for i in range(len(seq) - 1, -1, -1):
        rd = (seq[i][1], seq[i][0])
        push(('c', rd))
        n = ('c', nxt(rd))
        if i:
            link(n, ('c', (seq[i - 1][1], seq[i - 1][0])))
        else:
            push(n)
    first = q[0]
    if q[-1] != first:
        a, b = q[-1], first
        assert cen[a] == cen[b]
        q.append(cen[a])
    else:
        q.pop()
    assert len(set(q)) == len(q), 'slit cycle not simple'
    return q


def embedding_N(I, groups, arcs):
    """Rotation of N from the rotation of G, as in the drawing described in the note."""
    emb = I.emb
    nxt = lambda d: emb.next_face_half_edge(*d)
    prv = {nxt(d): d for d in I.darts}
    has = lambda u, v: frozenset((u, v)) in arcs
    E = nx.PlanarEmbedding()
    data = {}
    for s, cs in groups.items():
        if len(cs) >= 2:
            data[s] = list(cs)
    for d in I.darts:
        c = ('c', d)
        v, w = d
        rot = []
        cen = [s for s, cs in groups.items() if c in cs and len(cs) >= 2]
        rot += cen
        wp = list(emb.neighbors_cw_order(v))
        w2 = wp[(wp.index(w) + 1) % len(wp)]    # the edge on the other side of the corner

        def kept(x, u):                         # parallel E_C edges merge into the first: is it the edge of vu?
            if x == c or not has(c, x):
                return False
            return frozenset(arcs[frozenset((c, x))][0][3]) == frozenset((v, u))

        nb, nb2 = ('c', nxt((w, v))), ('c', (v, w2))   # across the edge of d, across the edge of the other side
        if kept(nb, w):
            rot.append(nb)
        for x in (('c', nxt(d)), ('c', prv[d])):
            if x not in rot and x != c:
                rot.append(x)
        if kept(nb2, w2) and nb2 not in rot:
            rot.append(nb2)
        data[c] = rot
    return data


def flow_instance(rng, big):
    while True:
        V, E = mf.graph(rng, big)
        if len(V) < 3 or not E:
            continue
        s, t = mf.far(V, E, rng)
        if s == t:
            continue
        _, cap = mf.capacities(V, E, rng)
        return mf.Inst(V, E, cap, s, t)


def net_case(rng, st, s, big):
    I = flow_instance(rng, big)
    groups, arcs = build_N(I, 1)
    q = slit_cycle(I, groups)
    Hg = nx.Graph()
    for pair in arcs:
        Hg.add_edge(*tuple(pair))
    st['chk.N_planar'] += 1
    ok, _ = nx.check_planarity(Hg)
    if not ok:
        st['FAIL.N_planar'] += 1
        return
    # every portal face has a corner on the cycle
    on = {x[1] for x in q if x[0] == 'c'}
    st['chk.portals_on_cycle'] += 1
    faces_on = {I.rgt[d] for d in on}
    if not set(I.portals) <= faces_on:
        st['FAIL.portals_on_cycle'] += 1
    # the cycle bounds a face of N: adding a vertex joined to all of it keeps planarity
    Hp = Hg.copy()
    for x in q:
        Hp.add_edge('apex', x)
    st['chk.cycle_is_facial'] += 1
    if not nx.check_planarity(Hp)[0]:
        st['FAIL.cycle_is_facial'] += 1
        return
    # the rotation that every host derives locally: planar, and the cycle is a face of it
    data = embedding_N(I, groups, arcs)
    st['chk.designed_rotation'] += 1
    Er = nx.PlanarEmbedding()
    Er.set_data(data)
    try:
        Er.check_structure()
    except nx.NetworkXException:
        st['FAIL.designed_rotation'] += 1
        return
    st['chk.designed_cycle_facial'] += 1
    if not any(set(Er.traverse_face(u, v)) == set(q) for u, v in ((q[0], q[1]), (q[1], q[0]))):
        st['FAIL.designed_cycle_facial'] += 1
    # hop bound
    D = nx.diameter(I.g)
    dN = nx.diameter(Hg)
    st['max_hop_ratio_x100'] = max(st['max_hop_ratio_x100'], 100 * dN // max(1, D))
    st['chk.N_hops'] += 1
    if dN > 6 * D + 2:
        st['FAIL.N_hops'] += 1
    # straight-line drawing of N in which the apex is drawn in the slit face
    em = nx.check_planarity(Hp)[1]
    pos = nx.combinatorial_embedding_to_pos(em)
    idx = {x: i for i, x in enumerate(sorted(Hg.nodes(), key=str))}
    P = np.array([pos[x] for x in sorted(Hg.nodes(), key=str)], float)
    Es = [(idx[a], idx[b]) for a, b in Hg.edges()]
    if not drawing_ok(P, Es):
        st['skip_bad_drawing'] += 1
        return
    # lengths: dual arcs with capacities, zero on E_R, big on E_S, scaled so that every arc is at least 1
    ndN = len(idx)
    Lam = max(I.cap.values()) + 1
    Mbig = ndN * Lam + 1
    w = {}
    for pair, lst in arcs.items():
        best = {}
        for u, v, k, luv, lvu in lst:
            if k == 'R':
                a, b = 0, 0
            elif k == 'S':
                a, b = Mbig, Mbig
            else:
                a, b = I.cap[luv], I.cap[lvu]
            for x, y, z in ((u, v, a), (v, u, b)):
                z2 = 2 * ndN * z + 1
                if (x, y) not in best or best[x, y] > z2:
                    best[x, y] = z2
        for (x, y), z in best.items():
            w[idx[x], idx[y]] = z
    g = PG(P, Es, w=w, seed=s)
    qi = [idx[x] for x in q]
    from core import pip
    if len(qi) >= 3:
        inn, tot = side(g, qi)
        if inn is None:
            st['skip_all_on_cycle'] += 1
            return
        swap = inn > 0
        st['chk.inside_empty'] += 1
        if inn not in (0, tot):
            st['FAIL.inside_empty'] += 1
    else:
        st['skip_short_cycle'] += 1
        return
    tol = 1e-13 * max(w.values()) * ndN   # lengths reach 1e10, the checks run on floats
    eng = Forced(g, random.Random(s + 1), dict(leaf=rng.choice([6, 8, 14]), tries=40, modes={'bal': 1.0}, zall=0.0, swap=0.0,
                                               degenerate=False, txmode='bfs', stop=True, tol=tol), qi, swap)
    run_engine(eng, st, s, rng)
    # the metric of N on portal corners is that of Gamma
    st['max_portals'] = max(st['max_portals'], len(I.portals))
    nodes = list(range(g.n))
    corners = [x for x in q if x[0] == 'c']
    src = [idx[x] for x in corners]
    Dn = sp_matrix(nodes, w, src)
    adj = mf.gamma_adj(I, lambda d: I.cap[d])
    for i, a in enumerate(corners):
        da = mf.dijkstra(I.nf, adj, {I.rgt[a[1]]: 0})
        for b in corners:
            st['chk.metric'] += 1
            val = Dn[i, idx[b]]
            ex = da[I.rgt[b[1]]]
            if not 2 * ndN * ex <= val + 1e-6 or not val < 2 * ndN * ex + ndN:
                st['FAIL.metric'] += 1
    st['runs_net'] += 1


def gen_case(rng, st, s):
    fams = ['dl', 'grid', 'k2m', 'fan', 'nested', 'pend', 'flower']
    fam = fams[s % len(fams)]
    r = random.Random(s * 31 + 7)
    args = params(fam, r)
    pos, E = FAMS[fam](s, args)
    if not drawing_ok(pos, E):
        return
    g = PG(pos, E, seed=s)
    kind = rng.choice(['face', 'fund'])
    if kind == 'face':
        fs = [[int(g.cv[c]) for c in lst] for lst in g.fcorners]
        fs = [f for f in fs if len(f) >= 3 and len(set(f)) == len(f)]
        if not fs:
            return
        q = max(fs, key=len) if rng.random() < 0.5 else rng.choice(fs)
        inn, tot = side(g, q)
        if inn is None:
            return
        keep = False
        swap = inn > 0
    else:
        root = rng.randrange(g.n)
        T = nx.bfs_tree(g.G, root).to_undirected()
        non = [e for e in g.ends if not T.has_edge(*e)]
        if not non:
            return
        y, z = rng.choice(non)
        q = nx.shortest_path(T, y, z)
        if len(q) < 3:
            return
        inn, tot = side(g, q)
        if inn is None:
            return
        keep = False
        swap = rng.random() < 0.5
    eng = Forced(g, random.Random(s + 1), dict(leaf=rng.choice([6, 8, 14]), tries=40, modes={'bal': 1.0}, zall=0.0, swap=0.0,
                                               degenerate=False, txmode='bfs', stop=True), q, swap, keep)
    run_engine(eng, st, s, rng)
    st['runs_gen|' + kind] += 1


def lane(seed, secs, what):
    rng = random.Random(seed)
    st = collections.Counter()
    t0 = time.time()
    s = seed * 1000
    while time.time() - t0 < secs:
        s += 1
        try:
            if what == 'net':
                net_case(rng, st, s, rng.random() < 0.2)
            else:
                gen_case(rng, st, s)
        except Fail as ex:
            st['FAIL.engine ' + str(ex.args[0])[:60]] += 1
            print('case', s, ex.args, file=sys.stderr)
    return st


def neg(seed, secs):
    """Control: a wrong gluing must be caught."""
    rng = random.Random(seed)
    st = collections.Counter()
    t0 = time.time()
    s = seed * 1000
    while time.time() - t0 < secs:
        s += 1
        fam = 'dl'
        args = params(fam, random.Random(s))
        pos, E = FAMS[fam](s, args)
        if not drawing_ok(pos, E):
            continue
        g = PG(pos, E, seed=s)
        fs = [[int(g.cv[c]) for c in lst] for lst in g.fcorners]
        fs = [f for f in fs if len(f) >= 3 and len(set(f)) == len(f)]
        if not fs:
            continue
        q = rng.choice(fs)
        inn, tot = side(g, q)
        if inn is None:
            continue
        eng = Forced(g, random.Random(s + 1), dict(leaf=8, tries=40, modes={'bal': 1.0}, zall=0.0, swap=0.0, degenerate=False,
                                                   txmode='bfs', stop=True), q, inn > 0)
        try:
            eng.run()
        except Fail:
            continue
        st['runs'] += 1
        root_glue(eng, st, rng, wrong=True)
    return st


if __name__ == '__main__':
    if sys.argv[1] == 'neg':
        print(json.dumps(dict(neg(int(sys.argv[2]), float(sys.argv[3]))), sort_keys=True))
    else:
        w = sys.argv[3] if len(sys.argv) > 3 else 'net'
        print(json.dumps(dict(lane(int(sys.argv[1]), float(sys.argv[2]), w)), sort_keys=True))
