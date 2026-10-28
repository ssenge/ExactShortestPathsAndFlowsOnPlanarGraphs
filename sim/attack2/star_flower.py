"""Assumption-side attacks on (G1') + 7(a) and Claim 7.
A. Star K_{1,m}: enumerate EVERY (G1')-shaped separator (q = h-l_i digon or l_i-h-l_j, virtual closing at every
   corner choice, both inside sides). Report the smallest possible largest child among separators obeying 7(a).
   If it is >= |X|-2, a (G1')+7(a) BDD of a star has height >= (m - leafsize)/2, against Property 1 (O(log n))
   and Property 5 (leaf size O(D log n), D = 2).
B. Star, balanced (G1') BDD that VIOLATES 7(a) (half the leaves outside each time): ports per bag and summed over
   the children of one bag, against D = 2.
C. Flower: hub v on S, outside a path C1 = c_1..c_k (all adjacent to v) with a pendant p_i between consecutive
   spokes. One bag X_{C1} gets >= k ports at v, while D <= 4. (7(a) violated: v meets k+1 outside components.)
usage: python3 star_flower.py"""
import sys, os, math, random, collections
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import networkx as nx
import gens, bdd, handbdd
from engine import Engine, CheckFail
from rot import Plane


def star(m):
    pos = {'h': (0.0, 0.0)}
    for i in range(m):
        pos[i] = (math.cos(2 * math.pi * i / m), math.sin(2 * math.pi * i / m))
    return Plane.from_coords(pos, [('h', i) for i in range(m)])


def part_A():
    print('A. star K_{1,m}: all (G1\') separators of the root bag')
    for m in (6, 10, 16, 30):
        P = star(m)
        X = frozenset(P.rot); PX = P.induced(X); faces, df = PX.faces()
        best7a = None; best_any = None; nsep = 0
        qs = [['h', i] for i in range(m)] + [[i, 'h', j] for i in range(m) for j in range(m) if i != j]
        for q in qs:
            y, z = q[0], q[-1]
            for jy in PX.corners_on_face(df, y, 0):
                for jz in PX.corners_on_face(df, z, 0):
                    res = bdd.analyse(PX, X, q, ('virtual', jy, jz))
                    if res is None:
                        continue
                    comps, cside, _ = res
                    for ins in 'LR':
                        outs = [c for i, c in enumerate(comps) if cside[i] != ins]
                        if not outs:
                            continue
                        nsep += 1
                        inn = set(q) | set().union(*[c for i, c in enumerate(comps) if cside[i] == ins]) if any(cside[i] == ins for i in range(len(comps))) else set(q)
                        kids = [inn] + [set(c) | {'h'} for c in outs]
                        big = max(len(k) for k in kids)
                        member_h = len(kids)          # h is in every child
                        if member_h <= 3:
                            best7a = big if best7a is None else min(best7a, big)
                        best_any = big if best_any is None else min(best_any, big)
        print('  m=%2d |X|=%2d  separators=%d  min largest child: with 7(a) %s, without 7(a) %s' % (
            m, m + 1, nsep, best7a, best_any))


def run_engine(P, bags, label):
    E = Engine(P, bags, random.Random(1), dict(stop=False))
    E.run()
    ports = collections.Counter()
    for ell, L in enumerate(E.levels[1:], 1):
        for ti, o in enumerate(L.orders):
            b = L.owner[ti]
            if bags[b]['depth'] == ell:
                ports[b] += len(o)
    D = nx.diameter(E.Gnx)
    worstJ = max(ports.values())
    worst_children = max((sum(ports[k] for k in B['kids']), b) for b, B in bags.items() if B.get('kids'))
    fails = collections.Counter(k for k, _ in E.fails)
    print('  %s: n=%d D=%d depth=%d  max |J_X|=%d  max sum_i |J_{X_i}|=%d  max L-corners at one vertex=%d  fails=%s' % (
        label, len(P.rot), D, max(B['depth'] for B in bags.values()), worstJ, worst_children[0],
        E.mx['L_per_vertex'], dict(fails)))
    return E


def part_B():
    print('B. star, balanced (G1\') BDD violating 7(a): half of the leaves outside at every split')
    for m in (16, 64, 256):
        P = star(m)
        gens.set_weights(P, random.Random(m))
        bags = {0: dict(X=frozenset(P.rot), parent=None, depth=0)}
        order = [0]
        while order:
            b = order.pop()
            X = bags[b]['X']
            leaves = sorted(v for v in X if v != 'h')
            if len(leaves) <= 3:
                continue
            # q = l_a - h - l_b with l_a, l_b at the ends of the first half (in rotation order)
            half = leaves[: len(leaves) // 2]
            q = [half[0], 'h', half[-1]]
            PX = P.induced(X); faces, df = PX.faces()
            kids = handbdd.split(P, bags, b, q, ('virtual', 0), inside_side='L', rng=random.Random(b))
            # choose inside = side with the larger number of leaves? keep 'L'; check sizes shrink
            if max(len(bags[k]['X']) for k in kids) >= len(X):
                kids2 = None
                for k in kids:
                    del bags[k]
                del bags[b]['kids']
                handbdd.split(P, bags, b, q, ('virtual', 0), inside_side='R', rng=random.Random(b))
                kids = bags[b]['kids']
            order += [k for k in kids if bags[k]['kind'] == 'in']
        run_engine(P, bags, 'star m=%d' % m)


def flower(k):
    pos = {'v': (0.0, 0.0), 'x': (-1.0, 0.0), 'y': (1.0, 0.0), 'z': (0.0, -1.0), 'u': (0.0, -0.4)}
    E = [('x', 'v'), ('v', 'y'), ('y', 'z'), ('z', 'x'), ('u', 'v'), ('u', 'z')]
    th = [math.pi * (i + 1) / (k + 1) for i in range(k)]
    for i in range(k):
        pos['c%d' % i] = (math.cos(th[i]) * 1.0, math.sin(th[i]) * 1.0 + 0.0)
        E.append(('v', 'c%d' % i))
        if i + 1 < k:
            E.append(('c%d' % i, 'c%d' % (i + 1)))
            mid = (th[i] + th[i + 1]) / 2
            pos['p%d' % i] = (0.5 * math.cos(mid), 0.5 * math.sin(mid))
            E.append(('v', 'p%d' % i))
    E += [('c0', 'y'), ('c%d' % (k - 1), 'x')]
    return Plane.from_coords(pos, E)


def part_C():
    print('C. flower: one outside component C1 wrapping k-1 pendant components at the hub v (7(a) violated)')
    for k in (4, 16, 64):
        P = flower(k)
        assert gens.euler_ok(P)
        gens.set_weights(P, random.Random(k))
        bags = {0: dict(X=frozenset(P.rot), parent=None, depth=0)}
        kids = handbdd.split(P, bags, 0, ['x', 'v', 'y', 'z'], 'real', inside_vertex='u', rng=random.Random(0))
        E = run_engine(P, bags, 'flower k=%d' % k)
        # ports of X_{C1}
        c1 = next(kb for kb in kids if 'c0' in bags[kb]['X'])
        L1 = E.levels[1]
        J = sum(len(o) for ti, o in enumerate(L1.orders) if L1.owner[ti] == c1)
        Jv = sum(1 for ti, o in enumerate(L1.orders) if L1.owner[ti] == c1 for p in o if p[1] == 'v')
        print('     |J_{X_C1}| = %d, of which %d ports at the hub v' % (J, Jv))


if __name__ == '__main__':
    part_A(); part_B(); part_C()
