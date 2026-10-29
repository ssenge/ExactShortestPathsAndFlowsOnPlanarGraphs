"""Region-form BDD (engine_r): run the §3 checks and measure Property 6 / (5) / (6) / (6') for region
graphs. python3 rsweep.py CONF START:END [families] [gadget]"""
import sys, os, random, collections, json, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'attack3'))
import networkx as nx
from sweep import CONF, params, MODES_ALL
# T_X built from T (as in [8]) but otherwise adversarial: separator modes, z directions, swaps
CONF['advb'] = dict(modes=MODES_ALL, zall=1.0, swap=0.5, degenerate=True, txmode='bfs', tries=120)
CONF['pxb'] = dict(modes={"avoid": 6, "bal": 1}, zall=0.0, swap=0.3, degenerate=False, txmode='bfs', tries=400, bal=0.97)
CONF['chb'] = dict(modes={"chord": 4, "bnd": 1, "bal": 1}, zall=0.0, swap=0.3, degenerate=True, txmode='bfs', tries=200)
CONF['advb0'] = dict(modes=MODES_ALL, zall=0.0, swap=0.5, degenerate=True, txmode='bfs', tries=120)
from geo import FAMS, virtual_candidates, drawing_ok
from core import PG, Fail
from engine_r import Engine
from gadget import expand
import post_r, math


def lv_check(eng, rng):
    """Lemma V in region form with exact labels: d~(v) = min over leaves L with v in V(E_L) of the
    leaf term, and over bags X with v in V(E_X) and hubs h of A_X(h) + d_X(h,v); must equal d(sigma,v)."""
    g = eng.g
    phi = {u: rng.randint(0, 30) for u in range(g.n)}
    G = nx.DiGraph()
    for (a, c) in g.ends:
        G.add_edge(a, c, w=g.w[(a, c)]); G.add_edge(c, a, w=g.w[(c, a)])
    G.add_node('sig')
    for u in range(g.n):
        G.add_edge('sig', u, w=phi[u])
    true = nx.single_source_dijkstra_path_length(G, 'sig', weight='w')
    best = {v: math.inf for v in range(g.n)}
    for b, B in eng.bags.items():
        H = nx.DiGraph()
        for e in B['E']:
            a, c = g.ends[e]
            H.add_edge(a, c, w=g.w[(a, c)]); H.add_edge(c, a, w=g.w[(c, a)])
        V = set(H.nodes())
        if not B['kids']:
            H.add_node('sig')
            for u in V:
                H.add_edge('sig', u, w=phi[u])
            loc = nx.single_source_dijkstra_path_length(H, 'sig', weight='w')
            for v in V:
                best[v] = min(best[v], loc[v])
            continue
        hubs = (eng.dss(b) | B['S']) & V
        R = H.reverse()
        for h in hubs:
            to_h = nx.single_source_dijkstra_path_length(R, h, weight='w')
            A = min(phi[u] + du for u, du in to_h.items())
            fr = nx.single_source_dijkstra_path_length(H, h, weight='w')
            for v, dv in fr.items():
                best[v] = min(best[v], A + dv)
    bad = sum(1 for v in range(g.n) if abs(best[v] - true[v]) > 1e-6)
    return bad


def ecc_diam(H):
    if H.number_of_nodes() <= 1:
        return 0
    return max(max(nx.single_source_shortest_path_length(H, s).values()) for s in H)


def metrics(eng, D):
    g = eng.g; out = collections.Counter(); mx = collections.defaultdict(float)
    byd = collections.defaultdict(list)
    for b, B in eng.bags.items():
        byd[B['depth']].append(b)
    for d, bs in byd.items():
        mr = collections.Counter(); mi = collections.Counter()
        for b in bs:
            B = eng.bags[b]; X = B['X']
            for e in B['E']:
                mr[e] += 1
            for (a, c) in g.ends:
                if a in X and c in X:
                    mi[(a, c)] += 1
            H = nx.Graph(); H.add_nodes_from(X); H.add_edges_from(g.ends[e] for e in B['E'])
            out['bags'] += 1
            if not nx.is_connected(H):
                out['REGION_DISCONNECTED'] += 1; continue
            iso = [v for v in X if H.degree(v) == 0]
            out['isolated'] += len(iso)
            cT = eng.comps_T(X, B['E'])
            mx['Tcomp_minus_depth'] = max(mx['Tcomp_minus_depth'], cT - (d + 1))
            mx['Tcomp'] = max(mx['Tcomp'], cT)
            if len(X) <= 400:
                dr = ecc_diam(H); di = ecc_diam(g.G.subgraph(X))
                mx['regiondiam_over_D'] = max(mx['regiondiam_over_D'], dr / D)
                mx['regiondiam_over_induced'] = max(mx['regiondiam_over_induced'], dr / max(1, di))
            if B.get('TX'):
                from core import tree_diam
                mx['TXdiam_over_D'] = max(mx['TXdiam_over_D'], tree_diam(B['TX']) / D)
        if mr:
            mx['mult_region'] = max(mx['mult_region'], max(mr.values()))
        if mi:
            mx['mult_induced'] = max(mx['mult_induced'], max(mi.values()))
    return out, mx


if __name__ == '__main__':
    conf = sys.argv[1]; a, b = map(int, sys.argv[2].split(':'))
    fams = sys.argv[3].split(',') if len(sys.argv) > 3 and sys.argv[3] != '-' else ['dl', 'grid', 'k2m', 'fan', 'nested', 'pend', 'flower']
    gad = len(sys.argv) > 4 and sys.argv[4] == 'gadget'
    tot = collections.defaultdict(collections.Counter); mx = collections.defaultdict(lambda: collections.defaultdict(float))
    fails = []; t0 = time.time()
    for s in range(a, b):
        r = random.Random(s * 31 + 7); fam = fams[s % len(fams)]; args = params(fam, r)
        pos, E = FAMS[fam](s, args)
        if gad:
            pos, E, _ = expand(pos, E)
        if not drawing_ok(pos, E):
            tot[fam]['bad_instance'] += 1; continue
        g = PG(pos, E, seed=s)
        cfg = dict(CONF[conf]); cfg['leaf'] = r.choice([6, 8, 10, 14])
        eng = Engine(g, virtual_candidates(pos, E), random.Random(s * 7919 + 1), cfg)
        try:
            eng.run()
        except Fail as ex:
            tot[fam]['FAILED'] += 1; fails.append((fam, s, args, ex.args)); print('FAIL', fam, s, args, ex.args, flush=True)
            continue
        if os.environ.get('FAST'):
            D = nx.diameter(g.G); o, m = metrics(eng, D)
            tot[fam].update(eng.st); tot[fam].update(o); tot[fam]['instances'] += 1
            for k, v in list(eng.mx.items()) + list(m.items()):
                mx[fam][k] = max(mx[fam][k], v)
            continue
        try:
            post_r.lemma16(eng); post_r.e2e(eng)
        except Fail as ex:
            tot[fam]['FAILED'] += 1; fails.append((fam, s, args, ex.args)); print('FAIL post', fam, s, args, ex.args, flush=True)
            continue
        badv = lv_check(eng, random.Random(s))
        tot[fam]['LV_checked'] += g.n; tot[fam]['LV_BAD'] += badv
        if badv:
            print('LV BAD', fam, s, args, badv, flush=True)
        D = nx.diameter(g.G)
        o, m = metrics(eng, D)
        tot[fam].update(eng.st); tot[fam].update(o); tot[fam]['instances'] += 1
        for k, v in list(eng.mx.items()) + list(m.items()):
            mx[fam][k] = max(mx[fam][k], v)
    keys = ('instances', 'FAILED', 'bags', 'REGION_DISCONNECTED', 'isolated', 'R_side_lost', 'rule3_to_outside_child',
            'rule3_no_holder', 'S_vertices_without_inside_edge', 'inside_parts', 'allS_child_with_edges_kept',
            'tiles_checked', 'monge_ineqs', 'G1_checks', 'hub_checks', 'L16_checks', 'e2e_gluings', 'R1_pairs', 'HX_planar_checks', 'LV_checked', 'LV_BAD', 'aY_checks', 'B2_checks', 'aY_gt_max1_holes', 'aY_gt_max1_holes_REALCLOSING', 'aY_gt_bound', 'B34_checks', 'closing_crosses_nonregion_edge', 'split_suppressed')
    mk = ('mult_region', 'mult_induced', 'Tcomp', 'Tcomp_minus_depth', 'regiondiam_over_D', 'regiondiam_over_induced',
          'TXdiam_over_D', 'inside_parts_max', 'L_per_vertex_max', 'lp47_comp_growth', 'depth_max', 'aY_max', 'aY_minus_holesX', 'holesX_minus_depth', 'holesY_minus_holesX')
    for fam in tot:
        print('FAM', fam, {k: tot[fam][k] for k in keys if tot[fam][k]})
        print('   ', {k: round(mx[fam][k], 2) for k in mk if k in mx[fam]})
    print('NFAILS', len(fails), 'secs', round(time.time() - t0))
