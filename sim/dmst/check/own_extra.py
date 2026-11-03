"""Questions about the note's own lanes. This one does import dmst.py, unlike check_dmst.cpp and lemmas.py.
 (1) steps by generator: where does the 'largest number of steps 6' come from?
 (2) does the generator ever give negative weights, a vertex not reached, or an arc tie the code breaks at random?
 (3) the claim that nx.minimum_spanning_arborescence refuses about 8%.
"""
import collections, importlib.util, json, os, random, sys, time
import networkx as nx
D = __import__('os').path.join(__import__('os').path.dirname(__import__('os').path.abspath(__file__)), '..', 'dmst.py')
sys.dont_write_bytecode = True
spec = importlib.util.spec_from_file_location('dmst', D)
dmst = importlib.util.module_from_spec(spec)
spec.loader.exec_module(dmst)


def main(seed, secs):
    rng = random.Random(seed)
    hist = collections.Counter()
    negative = 0
    refused = ok = other = 0
    wrong_root = 0
    end = time.time() + secs
    k = 0
    while time.time() < end:
        big = k % 2 == 1
        k += 1
        V, W, r = dmst.instance(rng, big)
        if min(W.values()) < 0:
            negative += 1
        st = collections.Counter()
        run = dmst.Run(V, W, r, st, 'ok', rng)
        run.solve()
        hist[('big' if big else 'main'), run.iters] += 1
        G = nx.DiGraph()
        G.add_nodes_from(V)
        G.add_weighted_edges_from([(u, v, w) for (u, v), w in W.items()])
        try:
            A = nx.minimum_spanning_arborescence(G)
            ok += 1
        except nx.NetworkXException:
            refused += 1
        except Exception:
            other += 1
    print(json.dumps({'instances': k, 'negative_weight_instances': negative,
                      'steps': {f'{a}:{b}': c for (a, b), c in sorted(hist.items())},
                      'nx_msa_ok': ok, 'nx_msa_refused': refused, 'nx_msa_other_error': other}))


main(int(sys.argv[1]), float(sys.argv[2]))
