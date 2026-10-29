"""S9 probe: owned edges (lambda_d), phantoms, and the communication graph Comm_Y = G[Y minus phantoms].
python3 comm.py CONF START:END [families]"""
import sys, os, json, random, collections
A3 = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'attack3')
sys.path.insert(0, A3)
import networkx as nx
from sweep import CONF, params
from run import one


def hopdiam(G):
    if G.number_of_nodes() <= 1:
        return 0
    return max(max(nx.single_source_shortest_path_length(G, s).values()) for s in G)


def probe(eng):
    g = eng.g; out = collections.Counter(); mx = collections.defaultdict(float)
    D = nx.diameter(g.G)
    bydepth = collections.defaultdict(list)
    for b, B in eng.bags.items():
        bydepth[B['depth']].append(b)
    for d, bs in bydepth.items():
        if d >= len(eng.levels):
            continue
        lab = eng.levels[d]['label']
        own = collections.defaultdict(list)
        for e, Y in enumerate(lab):
            own[int(Y)].append(e)
        mult_ind = collections.Counter(); mult_comm = collections.Counter()
        for b in bs:
            X = eng.bags[b]['X']
            hubs = eng.dss(b)
            Vo = set()
            for e in own[b]:
                Vo.update(g.ends[e])
            ph = X - Vo
            out['bags'] += 1; out['phantoms'] += len(ph); out['bags_with_phantom'] += bool(ph)
            if ph - hubs:
                out['CORE_PHANTOM'] += 1          # should never happen
            GX = g.G.subgraph(X)
            C = g.G.subgraph(Vo)
            O = nx.Graph(); O.add_edges_from(g.ends[e] for e in own[b])
            for (a, c) in GX.edges():
                mult_ind[(min(a, c), max(a, c))] += 1
            for (a, c) in C.edges():
                mult_comm[(min(a, c), max(a, c))] += 1
            if len(X) < 2:
                continue
            kc = nx.number_connected_components(C) if C.number_of_nodes() else 0
            ko = nx.number_connected_components(O) if O.number_of_nodes() else 0
            out['comm_disconnected'] += kc > 1; out['owned_disconnected'] += ko > 1
            dX = hopdiam(GX)
            dC = max(hopdiam(C.subgraph(cc)) for cc in nx.connected_components(C)) if kc else 0
            dO = max(hopdiam(O.subgraph(cc)) for cc in nx.connected_components(O)) if ko else 0
            mx['commdiam_over_GXdiam'] = max(mx['commdiam_over_GXdiam'], dC / max(dX, 1))
            mx['owneddiam_over_GXdiam'] = max(mx['owneddiam_over_GXdiam'], dO / max(dX, 1))
            mx['commdiam_over_D'] = max(mx['commdiam_over_D'], dC / D)
            mx['owneddiam_over_D'] = max(mx['owneddiam_over_D'], dO / D)
            mx['GXdiam_over_D'] = max(mx['GXdiam_over_D'], dX / D)
        if mult_ind:
            mx['mult_induced'] = max(mx['mult_induced'], max(mult_ind.values()))
        if mult_comm:
            mx['mult_comm'] = max(mx['mult_comm'], max(mult_comm.values()))
    mx['maxdeg'] = max(mx['maxdeg'], int(g.deg.max()))
    return out, mx


if __name__ == '__main__':
    conf = sys.argv[1]; a, b = map(int, sys.argv[2].split(':'))
    fams = sys.argv[3].split(',') if len(sys.argv) > 3 else ['dl', 'grid', 'k2m', 'fan', 'nested', 'pend', 'flower']
    tot = collections.defaultdict(collections.Counter); mx = collections.defaultdict(lambda: collections.defaultdict(float))
    for s in range(a, b):
        r = random.Random(s * 31 + 7); fam = fams[s % len(fams)]; args = params(fam, r)
        cfg = dict(CONF[conf]); cfg['leaf'] = r.choice([6, 8, 10, 14]); cfg['post'] = False
        try:
            eng = one(fam, s, args, cfg)
        except AssertionError:
            continue
        if eng.fails:
            tot[fam]['engine_fail'] += 1; continue
        o, m = probe(eng)
        tot[fam].update(o)
        for k, v in m.items():
            mx[fam][k] = max(mx[fam][k], v)
    for fam in tot:
        print(fam, dict(tot[fam]))
        print('   ', {k: round(v, 2) for k, v in mx[fam].items()})
