"""Post-run checks on an Engine: Lemma 16' recursion, Lemma 15' gluing with substitute disk graphs,
Property 6 / T_X congestion counts, §3.5 walk reconstruction from port records."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'attack3'))
import math, random, collections, itertools
import numpy as np, networkx as nx
from core import sp_matrix, add_arc, monge_check


def height(eng):
    h = {}
    for b in sorted(eng.bags, key=lambda b: -eng.bags[b]['depth']):
        k = eng.bags[b]['kids'] or []
        h[b] = 0 if not k else 1 + max(h[c] for c in k)
    return h


def dists_in(eng, X, sources, rev=False, E=None):
    g = eng.g
    nodes = sorted(X)
    arcs = {}
    for (a, c) in (g.ends if E is None else [g.ends[e] for e in E]):
        if a in X and c in X:
            if rev:
                arcs[(c, a)] = g.w[(a, c)]; arcs[(a, c)] = g.w[(c, a)]
            else:
                arcs[(a, c)] = g.w[(a, c)]; arcs[(c, a)] = g.w[(c, a)]
    D = sp_matrix(nodes, arcs, list(sources))
    ix = {v: i for i, v in enumerate(nodes)}
    return D, ix


def lemma16(eng, eps=0.05, neg=None):
    """d~_X per Lemma 16' with adversarial hub oracles; checks dist <= d~ <= (1+eps)^(3h+1) dist."""
    rng = eng.rng; bags = eng.bags
    h = height(eng)
    hubs = {b: eng.dss(b) | (bags[b].get('S', set()) if bags[b]['kids'] else set()) for b in bags}
    dt_f = {}; dt_b = {}       # b -> {(v,h): value}   forward v->h, backward h->v
    for b in sorted(bags, key=lambda b: -bags[b]['depth']):
        B = bags[b]; X = B['X']; H = sorted(hubs[b])
        lam = (1 + eps) ** (3 * h[b] + 1)
        if not H:
            dt_f[b] = {}; dt_b[b] = {}; continue
        Df, ix = dists_in(eng, X, H, E=B['E'])            # rows: hub -> all
        Db, _ = dists_in(eng, X, H, rev=True, E=B['E'])   # rows: all -> hub (reverse graph)
        f = {}; bk = {}
        if not B['kids']:
            for i, hh in enumerate(H):
                for v in X:
                    f[(v, hh)] = Db[i, ix[v]]; bk[(v, hh)] = Df[i, ix[v]]
        else:
            S = B['S']
            mode = rng.random()
            def oracle(d):
                if mode < 0.3: return d * lam
                if mode < 0.4: return d
                return d * rng.uniform(1, lam)
            dH = {}
            for i, a in enumerate(H):
                for j, c in enumerate(H):
                    dH[(a, c)] = oracle(Df[i, ix[c]]) if a != c else 0.0
            kid_of = {}
            for k in B['kids']:
                for x in bags[k]['X'] - S:
                    kid_of[x] = k
            hubset = set(H)
            for v in X:
                if v in hubset:
                    for hh in H:
                        f[(v, hh)] = dH[(v, hh)]; bk[(v, hh)] = dH[(hh, v)]
                    continue
                k = kid_of[v]; Y = bags[k]['X']
                ts = [t for t in S if t in Y]
                if neg == 'l16' and ts:
                    ts = ts[1:]
                for hh in H:
                    c1 = dt_f[k][(v, hh)] if hh in Y else math.inf
                    c2 = min((dt_f[k][(v, t)] + dH[(t, hh)] for t in ts), default=math.inf)
                    f[(v, hh)] = min(c1, c2)
                    c1 = dt_b[k][(v, hh)] if hh in Y else math.inf
                    c2 = min((dH[(hh, t)] + dt_b[k][(v, t)] for t in ts), default=math.inf)
                    bk[(v, hh)] = min(c1, c2)
        for i, hh in enumerate(H):
            for v in X:
                df = Db[i, ix[v]]; db = Df[i, ix[v]]
                for val, ex in ((f[(v, hh)], df), (bk[(v, hh)], db)):
                    eng.st['L16_checks'] += 1
                    if val < ex - 1e-9 or val > lam * ex + 1e-6:
                        if neg == 'l16':
                            eng.st['neg_L16_detected'] += 1
                        else:
                            eng.fail("Lemma16': bound violated", (b, v, hh, val, ex, lam))
        dt_f[b] = f; dt_b[b] = bk


def e2e(eng, neg=None):
    """Lemma 15' step 5: replace every child component C by a random disk graph (wheel on its
    ports in sigma order) or by C with perturbed weights; glue with ~_tau; check (M) in sigma_tau,
    component structure, and R1 bounds."""
    g = eng.g; rng = eng.rng
    for d in range(1, len(eng.levels) - 1):
        cur = eng.levels[d]; nxt = eng.levels[d + 1]
        par_of = {}
        for t, es in nxt['tile_edges'].items():
            par_of[t] = cur['tile'][es[0]]
        by_par = collections.defaultdict(list)
        for t, p in par_of.items():
            by_par[p].append(t)
        for p, subs in by_par.items():
            owner = cur['owner'][p]
            if not eng.bags[owner]['kids']:
                continue
            pports = [('p', v, j) for (v, j) in cur['order'][p]]
            if len(pports) < 2:
                continue
            for variant in ('wheel', 'perturb'):
                arcs = {}; shuffled = False
                gam = 0.3
                for t in subs:
                    carcs, cund = eng.piece(nxt, t, nxt['tile_edges'][t])
                    ports = [('p', v, j) for (v, j) in nxt['order'][t]]
                    def img(x):
                        if x[0] == 'p':
                            v, j = x[1], x[2]
                            return eng.node(cur, v, g.rot[v][j])
                        return x
                    for ci, cc in enumerate(nx.connected_components(cund)):
                        cp = [x for x in ports if x in cc]
                        if variant == 'wheel':
                            if neg == 'e2e' and len(cp) >= 4 and not shuffled:
                                cp = cp[:]; rng.shuffle(cp); shuffled = True
                            hub = ('hub', d, t, ci)
                            for i, x in enumerate(cp):
                                add_arc(arcs, hub, img(x), rng.randint(1, 40)); add_arc(arcs, img(x), hub, rng.randint(1, 40))
                                if len(cp) > 1:
                                    y = cp[(i + 1) % len(cp)]
                                    add_arc(arcs, img(x), img(y), rng.randint(1, 40))
                        else:
                            for (a, b), w in carcs.items():
                                if a in cc:
                                    add_arc(arcs, img(a), img(b), w * rng.uniform(1, 1 + gam))
                nodes = sorted({x for k in arcs for x in k} | set(pports), key=str)
                U = nx.Graph(); U.add_nodes_from(nodes); U.add_edges_from(arcs)
                # components of the exact piece P_tau
                parcs, pund = eng.piece(cur, p, cur['tile_edges'][p])
                pc = {x: i for i, cc in enumerate(nx.connected_components(pund)) for x in cc}
                qc = {x: i for i, cc in enumerate(nx.connected_components(U)) for x in cc}
                for a in pports:
                    for b in pports:
                        if (pc[a] == pc[b]) != (qc[a] == qc[b]):
                            eng.fail("Lemma15': glued components differ from P_tau components")
                D = sp_matrix(nodes, arcs, pports)
                ix = [nodes.index(x) for x in pports]
                M = D[:, ix]
                if variant == 'perturb':
                    pn = sorted(pund.nodes(), key=str)
                    Dp = sp_matrix(pn, parcs, pports)
                    Mp = Dp[:, [pn.index(x) for x in pports]]
                    fin = np.isfinite(Mp)
                    if (M[fin] < Mp[fin] - 1e-9).any() or (M[fin] > (1 + gam) * Mp[fin] + 1e-9).any():
                        eng.fail("Lemma R1 bound violated on glued tile")
                    eng.st['R1_pairs'] += int(fin.sum())
                for comp in set(pc[x] for x in pports):
                    sel = [i for i, x in enumerate(pports) if pc[x] == comp]
                    if len(sel) < 4:
                        continue
                    sel = sel[:eng.cfg['monge_cap']]
                    worst, cnt = monge_check(M[np.ix_(sel, sel)])
                    eng.st['e2e_monge_ineqs'] += cnt
                    if worst > 1e-7:
                        if neg == 'e2e' and shuffled:
                            eng.st['neg_e2e_detected'] += 1
                        else:
                            eng.fail("Lemma15' e2e: glued metric not Monge in sigma_tau", worst)
                    elif neg == 'e2e' and shuffled:
                        eng.st['neg_e2e_missed'] += 1
                eng.st['e2e_gluings'] += 1
    # H_X with wheels for every non-leaf X: planarity of the actual glued graph
    for d in range(0, len(eng.levels) - 1):
        cur = eng.levels[d]; nxt = eng.levels[d + 1]
        for b, B in eng.bags.items():
            if B['depth'] != d or not B['kids']:
                continue
            X = B['X']; kids = set(B['kids'])
            Hg = nx.Graph()
            for t, o in nxt['owner'].items():
                if o not in kids:
                    continue
                carcs, cund = eng.piece(nxt, t, nxt['tile_edges'][t])
                ports = [('p', v, j) for (v, j) in nxt['order'][t]]
                for ci, cc in enumerate(nx.connected_components(cund)):
                    cp = [x for x in ports if x in cc]
                    hub = ('hub', t, ci)
                    for i, x in enumerate(cp):
                        Hg.add_edge(hub, x[1])
                        y = cp[(i + 1) % len(cp)]
                        if len(cp) > 1 and y[1] != x[1]:
                            Hg.add_edge(x[1], y[1])
            for (a, c) in g.ends:
                if g.e(a, c) in eng.bags[b]['E'] and cur['label'][g.e(a, c)] != b:
                    Hg.add_edge(a, c)
            if not nx.check_planarity(Hg)[0]:
                eng.fail("Lemma15': H_X with wheel realizations not planar", b)
            eng.st['HX_planar_checks'] += 1


def prop6(eng):
    """max number of bags at one depth whose induced subgraph contains an edge; same for T_X."""
    g = eng.g
    bydepth = collections.defaultdict(list)
    for b, B in eng.bags.items():
        bydepth[B['depth']].append(b)
    worst = 0; worstT = 0; arg = None
    for d, bs in bydepth.items():
        cnt = collections.Counter(); cntT = collections.Counter()
        for b in bs:
            X = eng.bags[b]['X']
            for (a, c) in g.ends:
                if a in X and c in X:
                    cnt[(a, c)] += 1
            TX = eng.bags[b].get('TX')
            if TX:
                for a in TX:
                    for c in TX[a]:
                        if a < c:
                            cntT[(a, c)] += 1
        if cnt:
            e, k = cnt.most_common(1)[0]
            if k > worst:
                worst, arg = k, (d, e)
        if cntT:
            worstT = max(worstT, cntT.most_common(1)[0][1])
    eng.mx['prop6_max_bags_per_edge_per_depth'] = max(eng.mx['prop6_max_bags_per_edge_per_depth'], worst)
    eng.mx['TX_max_trees_per_edge_per_depth'] = max(eng.mx['TX_max_trees_per_edge_per_depth'], worstT)
    if worst > 2:
        eng.st['instances_violating_prop6'] += 1
    eng.prop6_arg = arg


def walk(eng):
    """§3.5: contour ranks around the global tree; rebuild every sigma_tau from port records."""
    g = eng.g; T = eng.T
    r = 0
    rank = {}
    y, j = r, 0
    while (y, j) not in rank:
        rank[(y, j)] = len(rank)
        e_to = g.rot[y][(j - 1) % g.deg[y]]
        if T.has_edge(y, e_to):
            y, j = e_to, g.idx[e_to][y]
        else:
            j = (j - 1) % g.deg[y]
    if len(rank) != g.nc:
        eng.fail('rank: contour missed corners'); return
    rk = np.array([rank[(int(g.cv[c]), int(g.cj[c]))] for c in range(g.nc)])
    dirs = set()
    for f, lst in enumerate(g.fcorners):
        if len(lst) < 3:
            continue
        rr = rk[lst]
        desc = sum(rr[(i + 1) % len(rr)] < rr[i] for i in range(len(rr)))
        asc = len(rr) - desc
        if not (desc == 1 or asc == 1):
            eng.fail('rank lemma: face corners not in rank order')
        dirs.add('inc' if desc == 1 else 'dec')
        eng.st['rank_checks'] += 1
    if len(dirs) > 1:
        eng.fail('rank lemma: orientation differs')
    # rebuild sigma for every tile of every level from records (opening/closing corner, rank, face)
    for d, lv in enumerate(eng.levels):
        if d == 0:
            continue
        gm = lv['gmask']
        byface = collections.defaultdict(list)
        for c in np.nonzero(gm)[0]:
            byface[int(g.cface[c])].append(int(c))
        for f in byface:
            byface[f].sort(key=lambda c: rk[c])
        pos_in = {c: (f, i) for f, L in byface.items() for i, c in enumerate(L)}
        okdir = {+1: True, -1: True}
        for t, ports in lv['order'].items():
            corners = [int(g.cbase[v] + j) for (v, j) in ports]
            for dr in (+1, -1):
                if not okdir[dr]:
                    continue
                # from the opening corner of a port, step to the neighbouring Gamma-corner of the same
                # face in rank order (direction dr): that must be the closing corner of the next port
                good = True
                for i, (v, j) in enumerate(ports):
                    c = corners[i]; f, k = pos_in[c]; L = byface[f]
                    c2 = L[(k + dr) % len(L)]
                    v2, j2 = ports[(i + 1) % len(ports)]
                    Lv = lv['gidx'][v2]; kk = Lv.index(j2)
                    close = int(g.cbase[v2] + Lv[(kk + 1) % len(Lv)])
                    if c2 != close:
                        good = False; break
                okdir[dr] = good
            eng.st['walk_rebuilds'] += 1
        if not (okdir[+1] or okdir[-1]):
            eng.fail('walk: sigma_tau not reconstructed from records', d)
