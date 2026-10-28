"""Region-based children (literal reading of [1]: X_out = S u all outside vertices; satisfies 7(a)) on a 'chord fan':
q = v, s_1, ..., s_k on a line, virtual closing s_k - v drawn below (in the outer face), inside = below.
Above the line: chords v - s_i (i = 2..k) drawn OUTSIDE S, and a pocket vertex w_i in each triangle v, s_i, s_{i+1}.
At v the outside wedge alternates X_out (w_i) and X_in (chords): Theta(k) label-change corners at ONE vertex,
although 7(a) holds. Claim 7's per-vertex bound (<= 4) fails; the total |L_A|/|S_A| stays bounded.
Same graph under (G1') per-component children: v meets k-1 outside components, 7(a) fails.
usage: python3 region_fan.py"""
import sys, os, random, collections
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import networkx as nx
import gens, bdd, handbdd
from engine import Engine
from rot import Plane


def fan(k):
    pos = {'v': (0.0, 10.0), 'u': (k / 2.0, -1.0)}
    for i in range(1, k + 1):
        pos['s%d' % i] = (float(i), 0.0)
    E = [('v', 's1')] + [('s%d' % i, 's%d' % (i + 1)) for i in range(1, k)]
    E += [('v', 's%d' % i) for i in range(2, k + 1)]
    for i in range(1, k):
        pos['w%d' % i] = ((0 + i + i + 1) / 3.0, 10.0 / 3.0)
        E += [('w%d' % i, 'v'), ('w%d' % i, 's%d' % i), ('w%d' % i, 's%d' % (i + 1))]
    E += [('u', 's%d' % i) for i in range(1, k + 1)]
    return Plane.from_coords(pos, E)


def main():
    for k in (4, 8, 16, 32, 64):
        P = fan(k)
        assert gens.euler_ok(P)
        gens.set_weights(P, random.Random(k))
        q = ['v'] + ['s%d' % i for i in range(1, k + 1)]
        for mode in ('region', 'G1prime'):
            bags = {0: dict(X=frozenset(P.rot), parent=None, depth=0)}
            # virtual closing s_k - v in the outer face (the face containing u's outer side and v)
            X = bags[0]['X']; PX = P.induced(X); faces, df = PX.faces()
            fi = max(range(len(faces)), key=lambda i: len(faces[i]))      # outer face
            kids = handbdd.split(P, bags, 0, q, ('virtual', fi), inside_vertex='u', rng=random.Random(0))
            if mode == 'region':
                outs = kids[1:]
                Xout = frozenset().union(*[bags[kb]['X'] for kb in outs]) | frozenset(q)
                for kb in outs:
                    del bags[kb]
                nb = max(bags) + 1
                bags[nb] = dict(X=Xout, parent=0, depth=1, kind='out')
                bags[0]['kids'] = [kids[0], nb]
                bags[0]['sat7a'] = True
            handbdd.complete(P, bags, random.Random(k), dict(leaf_size=3, region=(mode == 'region')))
            E = Engine(P, bags, random.Random(1), dict(stop=False))
            E.run()
            fails = collections.Counter(kk for kk, _ in E.fails)
            print('k=%2d %-8s 7(a) at root: %-5s  L-corners at v: %3d  max |L_A|/|S_A| = %.2f  max |J_X| = %d  D = %d  fails = %s' % (
                k, mode, bags[0]['sat7a'], E.mx['L_per_vertex'], E.mx['L_A_over_S_A'], E.mx['J_max'], E.diam, dict(fails)))


if __name__ == '__main__':
    main()
