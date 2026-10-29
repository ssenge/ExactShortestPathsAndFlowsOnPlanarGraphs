# Wrap build_ghat: record whether each built G^_l is planar (multi-edges, self-loops dropped).
import sys, collections, networkx as nx
import thmD
cnt = collections.Counter()
orig = thmD.build_ghat
def wrapped(emb, incised, epts, variant='literal'):
    G = orig(emb, incised, epts, variant)
    H = nx.Graph()
    H.add_nodes_from(range(G.nV))
    H.add_edges_from((a, b) for a, b, *_ in G.E if a != b)
    ok, _ = nx.check_planarity(H)
    cnt['planar' if ok else 'NONPLANAR'] += 1
    B = nx.Graph(); B.add_edges_from((u, v) for u, v in emb.ends if u != v)
    if nx.is_connected(H) and nx.is_connected(B):
        D, Dh = nx.diameter(B), nx.diameter(H)
        cnt['max_excess_over_4D+4'] = max(cnt['max_excess_over_4D+4'], Dh - (4*D + 4))
    return G
thmD.build_ghat = wrapped
variant, start, count = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
opts = dict(mode='claimed', variant=variant, tiebreak='minid', pairs=1, pcommon=0.5, pfar=0.5, e0rule='formal')
for sd in range(start, start + count):
    I = thmD.make_instance(sd, None)
    try:
        thmD.run_one(I, opts, sd * 1000)
    except Exception as ex:
        cnt['exc'] += 1
print(variant, dict(cnt))
