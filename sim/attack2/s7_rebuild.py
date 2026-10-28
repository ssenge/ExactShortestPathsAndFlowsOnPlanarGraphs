"""The three (S7) configurations that broke [1, Lemma 14], rebuilt as (G1')-shaped BDDs and fed to the tile
construction with all engine checks (Claims 1-7, T3, T4, T5, Monge, LP, end-to-end perturbed gluing).
  chord_out : g2_chord.py exactly (hexagon S, chord s0-s3 drawn OUTSIDE, inside child contains it)
  chord_in  : chord s0-s3 drawn INSIDE S; outside children {w_top}+s0..s3, {w_bot}+s3..s0 contain it
  virtual   : g2_virtual.py exactly (13x8 grid, nested separators closing by virtual edges in one face)
  pinch     : g2_pinch.py graph inside an outer ring; X has two ancestor holes touching at o0
Each: W weightings x random completions of the BDD below the hand-built levels.
usage: python3 s7_rebuild.py [W]"""
import sys, os, random, collections, math
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import networkx as nx, numpy as np
import gens, handbdd
from engine import Engine, CheckFail, apsp, monge_viol
from rot import Plane, monge_lp


def chord_out():
    P = Plane()
    def E(a, b):
        e = P.new_eid(); P.edges[e] = (a, b); return e
    s = ['s%d' % i for i in range(6)]
    cyc = [E(s[i], s[(i + 1) % 6]) for i in range(6)]
    spk = [E('z', s[i]) for i in range(6)]
    ch = E('s0', 's3')
    w1a, w1b = E('w1', 's1'), E('w1', 's2')
    w2a, w2b = E('w2', 's4'), E('w2', 's5')
    P.rot['z'] = spk[:]
    P.rot['s0'] = [ch, cyc[0], spk[0], cyc[5]]
    P.rot['s1'] = [w1a, cyc[1], spk[1], cyc[0]]
    P.rot['s2'] = [cyc[1], w1b, cyc[2], spk[2]]
    P.rot['s3'] = [spk[3], cyc[2], ch, cyc[3]]
    P.rot['s4'] = [cyc[4], spk[4], cyc[3], w2a]
    P.rot['s5'] = [cyc[5], spk[5], cyc[4], w2b]
    P.rot['w1'] = [w1b, w1a]
    P.rot['w2'] = [w2a, w2b]
    assert gens.euler_ok(P)
    def bdds(rng):
        out = []
        for extra in (None, 'w1', 'w2'):
            bags = {0: dict(X=frozenset(P.rot), parent=None, depth=0)}
            kids = handbdd.split(P, bags, 0, s, 'real', inside_vertex='z', extras=None, rng=rng)
            if extra:      # put s0, s3 into an outside child so that the chord is one of its outside edges
                for kb in kids[1:]:
                    X = set(bags[kb]['X'])
                    if extra in X:
                        X |= {'s0', 's3'}
                        bags[kb]['X'] = frozenset(X)
            out.append(handbdd.complete(P, bags, rng, dict(leaf_size=2)))
        return out
    return P, bdds


def chord_in():
    R = 2.0
    pos = {'s%d' % i: (R * math.cos(math.pi * i / 3), R * math.sin(math.pi * i / 3)) for i in range(6)}
    pos.update(z1=(0, 1), z2=(0, -1), wt=(0, 6), wb=(0, -6))
    s = ['s%d' % i for i in range(6)]
    E = [(s[i], s[(i + 1) % 6]) for i in range(6)] + [('s0', 's3'), ('z1', 's1'), ('z1', 's2'), ('z1', 's0'), ('z1', 's3'),
         ('z2', 's4'), ('z2', 's5'), ('z2', 's0'), ('z2', 's3'), ('wt', 's0'), ('wt', 's1'), ('wt', 's2'), ('wt', 's3'),
         ('wb', 's3'), ('wb', 's4'), ('wb', 's5'), ('wb', 's0')]
    P = Plane.from_coords(pos, E)
    assert gens.euler_ok(P)
    def bdds(rng):
        out = []
        for q in (s, ['s1', 's2', 's3', 's4', 's5', 's0']):
            bags = {0: dict(X=frozenset(P.rot), parent=None, depth=0)}
            handbdd.split(P, bags, 0, q, 'real', inside_vertex='z1', rng=rng)
            out.append(handbdd.complete(P, bags, rng, dict(leaf_size=2)))
        return out
    return P, bdds


def virtual(W=13, H=8, Rr=5, c=3, d=9):
    pos = {(x, y): (x, y) for x in range(W) for y in range(H)}
    E = [((x, y), (x + 1, y)) for x in range(W - 1) for y in range(H)] + \
        [((x, y), (x, y + 1)) for x in range(W) for y in range(H - 1)]
    P = Plane.from_coords(pos, E)
    q1 = [(0, y) for y in range(0, Rr + 1)] + [(x, Rr) for x in range(1, W)] + [(W - 1, y) for y in range(Rr - 1, -1, -1)]
    q2 = [(c, y) for y in range(0, Rr)] + [(x, Rr - 1) for x in range(c + 1, d + 1)] + [(d, y) for y in range(Rr - 2, -1, -1)]
    def bdds(rng):
        out = []
        for leaf in (2, 4, 8, 1000):
            bags = {0: dict(X=frozenset(P.rot), parent=None, depth=0)}
            kids = handbdd.split(P, bags, 0, q1, 'virtual', inside_vertex=(6, 2), rng=rng)
            Y = kids[0]
            k2 = handbdd.split(P, bags, Y, q2, 'virtual', inside_vertex=(6, 1), rng=rng)
            out.append(handbdd.complete(P, bags, rng, dict(leaf_size=leaf)))
        return out
    return P, bdds


def pinch():
    pos = {'o0': (2, 0), 'o1': (0, 2), 'o2': (-2, 0), 'o3': (0, -2), 'a': (1, 0.4), 'b': (1, -0.4),
           'm': (-0.5, 0), 'n1': (0.3, 1), 'n2': (0.3, -1), 't': (1.3, 0),
           'r0': (4, 0), 'r1': (0, 4), 'r2': (-4, 0), 'r3': (0, -4)}
    E = [('o0', 'o1'), ('o1', 'o2'), ('o2', 'o3'), ('o3', 'o0'), ('o0', 'a'), ('a', 'b'), ('b', 'o0'),
         ('a', 'n1'), ('n1', 'o1'), ('b', 'n2'), ('n2', 'o3'), ('m', 'o2'), ('m', 'a'), ('m', 'b'),
         ('m', 'n1'), ('m', 'n2'), ('n1', 'o0'), ('n2', 'o0'), ('t', 'o0'), ('t', 'a'), ('t', 'b'),
         ('r0', 'o0'), ('r1', 'o1'), ('r2', 'o2'), ('r3', 'o3'), ('r0', 'r1'), ('r1', 'r2'), ('r2', 'r3'), ('r3', 'r0')]
    P = Plane.from_coords(pos, E)
    assert gens.euler_ok(P)
    def bdds(rng):
        out = []
        for leaf in (2, 3, 1000):
            bags = {0: dict(X=frozenset(P.rot), parent=None, depth=0)}
            kids = handbdd.split(P, bags, 0, ['o0', 'o1', 'o2', 'o3'], 'real', inside_vertex='m', rng=rng)
            Xin = kids[0]
            k2 = handbdd.split(P, bags, Xin, ['o0', 'a', 'b'], 'real', inside_vertex='t', rng=rng)
            X = k2[1]
            assert bags[X]['X'] == frozenset({'o0', 'o1', 'o2', 'o3', 'a', 'b', 'm', 'n1', 'n2'}), bags[X]['X']
            out.append(handbdd.complete(P, bags, rng, dict(leaf_size=leaf)))
        return out
    return P, bdds


def alpha_star_of_tiles(E):
    """for every tile component with 4..8 ports: alpha* of the LP with variable alpha in sigma_tau (must be 1)."""
    worst = 1.0; n = 0
    for L in E.levels[1:]:
        for ti, (arcs, nodes, comps, _) in L.pieces.items():
            ports = L.orders[ti]
            D = apsp(nodes, arcs, ports); idx = {x: i for i, x in enumerate(nodes)}
            for cp in comps:
                if 4 <= len(cp) <= 8:
                    rows = [ports.index(p) for p in cp]
                    M = D[np.ix_(rows, [idx[p] for p in cp])]
                    delta = {(a, b): float(M[i, j]) for i, a in enumerate(cp) for j, b in enumerate(cp) if a != b}
                    st, al, _ = monge_lp(delta, cp)
                    worst = max(worst, al); n += 1
    return worst, n


def main():
    W = int(sys.argv[1]) if len(sys.argv) > 1 else 60
    for name, mk in (('chord_out', chord_out), ('chord_in', chord_in), ('virtual', virtual), ('pinch', pinch)):
        P, bdds = mk()
        tot = collections.Counter(); fails = 0; inst = 0; worst_alpha = 1.0; nalpha = 0
        for w in range(W):
            rng = random.Random(1000 * w + 7)
            gens.set_weights(P, rng, ['small', 'heavy', 'asym', 'binary'][w % 4])
            for bags in bdds(rng):
                E = Engine(P, bags, rng, dict(lp_samples=200))
                try:
                    E.run()
                except CheckFail as ex:
                    fails += 1
                    print('FAIL', name, w, ex.args[0], str(ex.args[1])[:200])
                tot.update(E.st); inst += 1
                if w < 10:
                    a, n = alpha_star_of_tiles(E)
                    worst_alpha = max(worst_alpha, a); nalpha += n
        keys = ['levels', 'tiles', 'monge_checks', 'lp_checks', 'e2e_components', 'e2e_monge_checks', 'T4b_glue_checks',
                'wheel_tau_checks', 'H_wheel_checks', 'T5_order_checks', 'claim4_checks', 'claim5_checks', 'P_used']
        print('%-10s instances=%d fails=%d  alpha*(sigma_tau) max=%.6f over %d LPs  %s' % (
            name, inst, fails, worst_alpha, nalpha, {k: tot[k] for k in keys}), flush=True)


if __name__ == '__main__':
    main()
