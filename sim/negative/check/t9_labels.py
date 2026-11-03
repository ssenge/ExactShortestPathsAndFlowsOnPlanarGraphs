"""What the label collisions of [3, Section 5.2] do to Proposition 4, and whether the repairs work.
effect: the restricted algorithm with idx from Algorithm 3 on the kept arcs, in several readings, against idx from Tarjan, on the same instances.
repair: exact expected number of colliding pairs for the half-open interval. leader needs no table: its labels are distinct by construction, and 't4_ldd.py top' checks that."""
import os, random, signal, sys, time
from collections import Counter
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from core_check import *
from t2_prop4 import planar_random, restricted_weights, is_restricted
from t4_ldd import Topsort
from t8_collide import grid, expected_collisions

ST = Counter()
READ = [('tarjan', None, None), ('arcs_parent', 'parent', 'arcs'), ('arcs_own', 'own', 'arcs'), ('net_parent', 'parent', 'network'), ('arcs_leader', 'leader', 'arcs')]


def make_decomp(n, arcs, E, rng, cc, conn, name):
    wpos = [(u, v, max(w, 0)) for u, v, w in arcs]

    def decomp(l, r):
        rem = ldd(n, wpos, 2 ** l, rng, 1.0)
        kept = [(a[0], a[1]) for i, a in enumerate(wpos) if i not in rem]
        if cc is None:
            return tarjan(n, kept)
        T = Topsort(n, kept, dil=2, cc_n=cc, net=list(E) if conn == 'network' else kept)
        lab = T.run(rng)
        comp = tarjan(n, kept)
        ST[name + '.decomps'] += 1
        byl = {}
        for v in range(n):
            byl.setdefault(lab[v], set()).add(comp[v])
        if any(len(s) > 1 for s in byl.values()):
            ST[name + '.decomps_with_collision'] += 1
            if any(lab[u] == lab[v] and comp[u] != comp[v] for u, v, _ in wpos):
                ST[name + '.decomps_with_arc_inside'] += 1
        M = max(lab)
        return [M - x for x in lab]
    return decomp


def effect(seed, secs, nmax, R, t):
    rng = random.Random(seed)
    end = time.time() + secs
    while time.time() < end:
        n, E = planar_random(rng, nmax)
        arcs = restricted_weights(n, E, rng)
        if not arcs or not is_restricted(n, arcs):
            continue
        ST['instances'] += 1
        ST['max_n'] = max(ST['max_n'], n)
        for name, cc, conn in READ:
            r2 = random.Random(rng.random())
            pot = restricted(n, arcs, r2, R, t, 1.0, decomp=make_decomp(n, arcs, E, r2, cc, conn, name))
            ST[name + '.runs'] += 1
            if any(w + pot[u] - pot[v] < 0 for u, v, w in arcs):
                ST[name + '.final_wrong'] += 1


def repair(runs):
    rng = random.Random(4)
    for dil in (2, 4):
        for keep_p in (0.0, 0.3):
            row = []
            for a in (4, 6, 8, 12):
                n, E = grid(a)
                s = 0.0
                for _ in range(runs):
                    arcs = [((x, y) if rng.random() < 0.5 else (y, x)) for x, y in E if rng.random() < keep_p]
                    T = Topsort(n, arcs, dil=dil, cc_n='halfopen', net=arcs)
                    T.run(rng)
                    s += expected_collisions(T.bases)
                row.append((n, round(s / runs, 9)))
            print('halfopen arcs dil', dil, 'keep', keep_p, '(n, E colliding pairs):', row, flush=True)


if __name__ == '__main__':
    def _alarm(*_):
        print('ALARM partial', sys.argv[1:], {k: ST[k] for k in sorted(ST)}, flush=True)
        os._exit(0)
    signal.signal(signal.SIGALRM, _alarm)
    if sys.argv[1] == 'effect':
        effect(int(sys.argv[2]), float(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]), int(sys.argv[6]))
    else:
        repair(int(sys.argv[2]))
    print(sys.argv[1:], {k: ST[k] for k in sorted(ST)})
