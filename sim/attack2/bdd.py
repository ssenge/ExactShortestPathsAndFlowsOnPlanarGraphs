"""(G1')-shaped BDDs on arbitrary rotation systems, with adversarial separator choices.

Per bag X: a spanning tree T_X of G[X] (per-bag; see REPORT on Property 4), q_X = T_X-path y..z with
>= 1 edge, closing edge real (edge yz of G[X], only if q has >= 2 edges) or virtual (inserted at a
corner of y and a corner of z on a common face of G[X]; for |E(q)| = 1 this is a digon).
Sides are computed from the rotation of G[X] + closing edge.  Children: X_in = S u (vertices on the
chosen inside side); X_C = C u (S n N(C)) u extras (extras subset of S, keeping G[X_C] connected).
7(a) (every S-vertex in <= 3 children) is enforced unless cfg['allow7a'].
"""
import random, collections
import networkx as nx

VIRT = 'VIRT'

DEFAULT = dict(leaf_size=6, p_leaf=0.0, max_depth=40, tries=80,
               strats=('rand', 'face', 'hole', 'anc', 'pinch', 'far', 'hub', 'single', 'chordy'),
               tree_modes=('bfs', 'dfs', 'rand'), inside=('rand', 'small', 'big', 'empty'),
               p_real=0.5, p_extra=(0.0, 0.0, 0.3, 1.0), allow7a=False)


def spanning_tree(GX, rng, mode, prefer=()):
    nodes = list(GX.nodes())
    if mode == 'bfs':
        return nx.bfs_tree(GX, rng.choice(nodes)).to_undirected()
    if mode == 'dfs':
        return nx.dfs_tree(GX, rng.choice(nodes)).to_undirected()
    H = nx.Graph()
    pref = set(frozenset(e) for e in prefer)
    for a, b in GX.edges():
        w = rng.random() + (0 if (mode == 'anc' and frozenset((a, b)) in pref) else 1)
        H.add_edge(a, b, weight=w)
    return nx.minimum_spanning_tree(H)


def proper_ancestors(bags, b):
    out = []; p = bags[b]['parent']
    while p is not None:
        out.append(p); p = bags[p]['parent']
    return out


def dSstar(bags, b):
    X = bags[b]['X']; s = set()
    for a in proper_ancestors(bags, b):
        s |= bags[a]['S'] & X
    return s


def analyse(PX, X, q, closing):
    """returns (comps, side_of_comp) or None if inconsistent. closing: ('real', eid) or ('virtual', jy, jz)."""
    y, z = q[0], q[-1]
    rot = {v: list(PX.rot[v]) for v in q}
    eid = {}
    for e, (a, b) in PX.edges.items():
        eid[frozenset((a, b))] = e
    qe = [eid[frozenset((q[i], q[i + 1]))] for i in range(len(q) - 1)]
    if closing[0] == 'virtual':
        _, jy, jz = closing
        rot[y].insert(jy, VIRT)
        rot[z].insert(jz, VIRT)
        ce = VIRT
    else:
        ce = closing[1]
    k = len(q) - 1
    side = {}
    for i, s in enumerate(q):
        ein = ce if i == 0 else qe[i - 1]
        eout = ce if i == k else qe[i]
        r = rot[s]; n = len(r)
        a = r.index(eout); bpos = r.index(ein)
        left = set(r[(a + t) % n] for t in range(1, (bpos - a) % n))
        for e in r:
            if e in (ein, eout) or e == VIRT:
                continue
            side[(s, e)] = 'L' if e in left else 'R'
    S = set(q)
    GXn = nx.Graph()
    GXn.add_nodes_from(v for v in X if v not in S)
    for e, (a, b) in PX.edges.items():
        if a not in S and b not in S:
            GXn.add_edge(a, b)
    comps = [frozenset(c) for c in nx.connected_components(GXn)]
    comp_of = {v: i for i, c in enumerate(comps) for v in c}
    cside = {}
    for (s, e), sd in side.items():
        a, b = PX.edges[e]
        o = b if a == s else a
        if o in S:
            continue
        ci = comp_of[o]
        if cside.setdefault(ci, sd) != sd:
            return None            # Jordan violated: closing edge not drawable as given
    assert len(cside) == len(comps), 'component not adjacent to S'
    return comps, cside, side


def build(P, rng, cfg=None):
    cfg = dict(DEFAULT, **(cfg or {}))
    G = nx.Graph()
    G.add_nodes_from(P.rot)
    for e, (a, b) in P.edges.items():
        G.add_edge(a, b, eid=e)
    bags = {0: dict(X=frozenset(P.rot), parent=None, depth=0)}
    if cfg.get('global_tree'):
        cfg['T0'] = nx.bfs_tree(G, rng.choice(sorted(P.rot))).to_undirected()
    order = [0]; k = 0
    while k < len(order):
        b = order[k]; k += 1
        B = bags[b]
        if len(B['X']) <= cfg['leaf_size'] or B['depth'] >= cfg['max_depth'] or (B['depth'] > 0 and rng.random() < cfg['p_leaf']):
            continue
        sep = find_separator(P, G, bags, b, rng, cfg)
        if sep is None:
            continue
        kids = sep.pop('children')
        B.update(sep)
        B['kids'] = []
        for kind, Y in kids:
            nb = len(bags)
            bags[nb] = dict(X=frozenset(Y), parent=b, depth=B['depth'] + 1, kind=kind)
            B['kids'].append(nb)
            order.append(nb)
    return bags


def find_separator(P, G, bags, b, rng, cfg):
    B = bags[b]; X = B['X']
    GX = G.subgraph(X)
    PX = P.induced(X)
    facesX, dfX = PX.faces()
    fverts = [set(v for v, _ in f) for f in facesX]
    anc = proper_ancestors(bags, b)
    dss = dSstar(bags, b)
    anc_q_edges = []
    for a in anc:
        q = bags[a]['q']
        for i in range(len(q) - 1):
            if q[i] in X and q[i + 1] in X:
                anc_q_edges.append((q[i], q[i + 1]))
    Xl = sorted(X)
    deg = {v: GX.degree(v) for v in X}
    for attempt in range(cfg['tries']):
        strat = rng.choice(cfg['strats'])
        if cfg.get('global_tree'):
            tmode = 'global'
            T = cfg['T0'].subgraph(X).copy()
            if not nx.is_connected(T):
                return None            # Property 4 fails for this bag (cannot happen for accepted children)
        else:
            tmode = 'anc' if strat == 'anc' else rng.choice(cfg['tree_modes'])
            T = spanning_tree(GX, rng, tmode, anc_q_edges)
        y = z = None; want_virtual_face = None
        if strat == 'rand':
            y, z = rng.sample(Xl, 2)
        elif strat in ('face', 'hole'):
            if strat == 'face':
                wts = [len(f) ** 2 for f in facesX]
                fi = rng.choices(range(len(facesX)), weights=wts)[0]
            else:
                fi = max(range(len(facesX)), key=lambda i: (len(fverts[i] & dss), len(facesX[i]), rng.random()))
            cand = sorted(fverts[fi])
            if len(cand) < 2:
                continue
            pool = sorted(fverts[fi] & dss) if strat == 'hole' and len(fverts[fi] & dss) >= 2 and rng.random() < 0.6 else cand
            y, z = rng.sample(pool, 2)
            want_virtual_face = fi
        elif strat == 'anc':
            if len(dss) < 2:
                y, z = rng.sample(Xl, 2)
            else:
                y, z = rng.sample(sorted(dss), 2)
        elif strat == 'pinch':
            if not dss:
                continue
            y = rng.choice(sorted(dss))
            others = [v for v in Xl if v not in dss]
            if not others:
                continue
            z = rng.choice(others)
        elif strat == 'far':
            if dss:
                dist = nx.multi_source_dijkstra_path_length(GX, dss)
                far = sorted(X, key=lambda v: -dist.get(v, 0))[:max(2, len(X) // 3)]
            else:
                far = Xl
            if len(far) < 2:
                continue
            y, z = rng.sample(far, 2)
        elif strat == 'hub':
            h = max(Xl, key=lambda v: (deg[v], rng.random()))
            y = h; z = rng.choice([v for v in Xl if v != h])
            if rng.random() < 0.5:
                # put the hub in the middle of q
                nb = [v for v in GX.neighbors(h)]
                if len(nb) >= 2:
                    y, z = rng.sample(nb, 2)
        elif strat == 'single':
            ed = list(T.edges())
            y, z = rng.choice(ed)
        elif strat == 'chordy':
            # q through a dense region: start at a vertex with many triangles
            tri = nx.triangles(GX)
            y = max(Xl, key=lambda v: (tri[v], rng.random()))
            z = rng.choice([v for v in Xl if v != y])
        if y is None or y == z:
            continue
        q = nx.shortest_path(T, y, z)
        if strat == 'pinch' and len(set(q) & dss) != 1:
            continue
        # closing edge
        closing = None
        if len(q) >= 3 and GX.has_edge(y, z) and rng.random() < cfg['p_real']:
            closing = ('real', GX[y][z]['eid'])
        else:
            faces_yz = [i for i in range(len(facesX)) if y in fverts[i] and z in fverts[i]]
            if want_virtual_face is not None and want_virtual_face in faces_yz and rng.random() < 0.8:
                fi = want_virtual_face
            elif faces_yz:
                fi = rng.choice(faces_yz)
            else:
                continue
            jy = rng.choice(PX.corners_on_face(dfX, y, fi))
            jz = rng.choice(PX.corners_on_face(dfX, z, fi))
            closing = ('virtual', jy, jz)
        res = analyse(PX, X, q, closing)
        if res is None:
            continue
        comps, cside, eside = res
        S = set(q)
        mode = rng.choice(cfg['inside'])
        sideL = [i for i in range(len(comps)) if cside[i] == 'L']
        sideR = [i for i in range(len(comps)) if cside[i] == 'R']
        szL = sum(len(comps[i]) for i in sideL); szR = sum(len(comps[i]) for i in sideR)
        if mode == 'rand':
            ins = rng.choice('LR')
        elif mode == 'small':
            ins = 'L' if szL <= szR else 'R'
        elif mode == 'big':
            ins = 'L' if szL >= szR else 'R'
        else:  # empty interior if possible
            ins = 'L' if not sideL else ('R' if not sideR else rng.choice('LR'))
        inside = [i for i in range(len(comps)) if cside[i] == ins]
        outside = [i for i in range(len(comps)) if cside[i] != ins]
        if not outside:
            continue                       # X_in = X: no progress
        Xin = set(S)
        for i in inside:
            Xin |= comps[i]
        pex = rng.choice(cfg['p_extra'])
        kids = [('in', Xin)]
        if cfg.get('region'):
            # literal reading of [1, Sec. 5.1.1]: one child per region of S_X (NOT (G1')): X_out = S u outside
            Xout = set(S)
            for i in outside:
                Xout |= comps[i]
            kids.append(('out', Xout))
            outside_loop = []
        else:
            outside_loop = outside
        for i in outside_loop:
            C = comps[i]
            Y = set(C) | {s for s in S if any(GX.has_edge(s, x) for x in C)}
            if pex > 0:
                changed = True
                while changed:
                    changed = False
                    for s in sorted(S - Y):
                        if rng.random() < pex and any(GX.has_edge(s, x) for x in Y):
                            Y.add(s); changed = True
            kids.append(('out', Y))
        if any(len(Y) >= len(X) or len(Y) < 2 for _, Y in kids):
            continue
        member = collections.Counter()
        for _, Y in kids:
            for s in S & Y:
                member[s] += 1
        maxmem = max(member.values())
        nout_adj = collections.Counter()
        for i in outside:
            for s in S:
                if any(GX.has_edge(s, x) for x in comps[i]):
                    nout_adj[s] += 1
        if maxmem > 3 and not cfg['allow7a']:
            continue
        if cfg.get('global_tree') and any(not nx.is_connected(cfg['T0'].subgraph(Y)) for _, Y in kids):
            continue                       # Property 4: T[child] must be connected
        for _, Y in kids:
            assert nx.is_connected(GX.subgraph(Y)), 'child not connected'
        return dict(S=S, q=q, closing=closing, T=T, strat=strat, tmode=tmode, inside_mode=mode,
                    sat7a=(maxmem <= 3), maxmem=maxmem, nout_adj=dict(nout_adj), children=kids,
                    n_inside_comps=len(inside), n_out=len(outside), pex=pex)
    return None
