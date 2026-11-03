"""Property 6 of Lemma 9 (every edge lies in <= 2 induced subgraphs of bags of one depth) on generated (G1')-BDDs:
with minimal children (no extras) vs with extras, and for region-based children. BDD only, no tile engine.
usage: python3 prop6.py <nseeds>"""
import sys, os, random, collections
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import gens, bdd

def worst(P, bags):
    by = collections.defaultdict(list)
    for B in bags.values():
        by[B['depth']].append(B['X'])
    w = 0; arg = None
    for d, Xs in by.items():
        cnt = collections.Counter()
        for X in Xs:
            for e, (a, c) in P.edges.items():
                if a in X and c in X:
                    cnt[e] += 1
        if cnt and max(cnt.values()) > w:
            w = max(cnt.values()); arg = d
    return w, arg

N = int(sys.argv[1])
for label, cfg in (('G1prime minimal children', dict(p_extra=(0.0,))), ('G1prime with extras', {}),
                   ('G1prime minimal, global BFS tree', dict(p_extra=(0.0,), global_tree=True, tries=200)),
                   ('region-based children', dict(region=True))):
    viol = 0; mx = 0; hist = collections.Counter()
    for s in range(N):
        rng = random.Random(77 + s)
        fam = rng.choice(['treeplus_sparse', 'treeplus_mid', 'treeplus_dense', 'delaunay', 'grid', 'nested', 'outerplanar', 'cactus'])
        P = gens.FAMILIES[fam](rng)
        c = dict(cfg); c['leaf_size'] = rng.choice([2, 4, 8])
        bags = bdd.build(P, rng, c)
        w, d = worst(P, bags)
        hist[min(w, 6)] += 1
        viol += w > 2; mx = max(mx, w)
    print('%-34s instances=%d  Property 6 violated in %d  max bags per edge at one depth = %d  hist(capped 6) %s' % (
        label, N, viol, mx, dict(sorted(hist.items()))), flush=True)
