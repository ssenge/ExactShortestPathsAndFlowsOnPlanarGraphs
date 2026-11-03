"""Theorem 1 on the whole stack: scaling, restricted algorithm with my LDD, Lemma 1. Against Bellman-Ford. Planarity asserted.
Exhaustive on n = 3 for small weights. 'fault' shows what the potential check does and does not certify, with a faulty oracle.
'size' records how large the numbers fed to the oracle get, in powers of n."""
import itertools, math, os, random, sys, time
from collections import Counter
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import networkx as nx
import core_check
from core_check import *
from t2_prop4 import planar_random

ST = Counter()
EX = {}


def check_answer(n, arcs, s, ans):
    truth = bf_all(n, arcs)
    ST['runs'] += 1
    if truth is None:
        ST['neg_instances'] += 1
        if ans[0] != 'neg':
            ST['FAIL.neg_missed'] += 1
        return
    if ans[0] == 'neg':
        ST['false_reports'] += 1
        return
    dist, par, psi = ans[1], ans[2], ans[3]
    if dist != bf_from(n, arcs, s):
        ST['FAIL.dist'] += 1
        EX.setdefault('dist', (n, arcs, s, dist))
    ST['dist_checked'] += n
    if any(w + psi[u] - psi[v] < 0 for u, v, w in arcs):
        ST['FAIL.pot'] += 1
    # the parent tree: path weights equal the distances
    wt = {}
    for u, v, w in arcs:
        wt[(u, v)] = min(w, wt.get((u, v), INF))
    for v in range(n):
        if dist[v] >= INF or v == s:
            continue
        x, tot, steps = v, 0, 0
        while x != s:
            p = par[x]
            if p is None or steps > n:
                ST['FAIL.tree'] += 1
                break
            tot += wt[(p, x)]
            x = p
            steps += 1
        else:
            if tot != dist[v]:
                ST['FAIL.tree_weight'] += 1


def exh3(R, t, c, seed):
    n = 3
    rng = random.Random(seed)
    allarcs = list(itertools.permutations(range(n), 2))
    solver = stack_solver(rng, R, t, c)
    for ws in itertools.product([None, -2, -1, 0, 1], repeat=len(allarcs)):
        arcs = [(a[0], a[1], w) for a, w in zip(allarcs, ws) if w is not None]
        if not arcs:
            continue
        ans = theorem1(n, arcs, 0, solver)
        check_answer(n, arcs, 0, ans)


def general_weights(n, E, rng):
    W0 = rng.choice([2, 5, 50, 10 ** 4])
    p = [rng.randrange(-W0, W0 + 1) for _ in range(n)]
    arcs = []
    mode = rng.choice(['both', 'one', 'mix'])
    zero = rng.choice([0.3, 0.8])
    for a, b in E:
        pairs = []
        if mode == 'both' or (mode == 'mix' and rng.random() < 0.5):
            pairs = [(a, b), (b, a)]
        else:
            pairs = [(a, b)] if rng.random() < 0.5 else [(b, a)]
        for u, v in pairs:
            c = 0 if rng.random() < zero else rng.randrange(0, W0 + 1)
            arcs.append((u, v, c + p[u] - p[v]))
    if rng.random() < 0.3 and arcs:
        i = rng.randrange(len(arcs))
        u, v, w = arcs[i]
        arcs[i] = (u, v, w - rng.randrange(1, 2 * W0 + 2))
    return arcs


def lane(seed, secs, nmax, R, t, c):
    rng = random.Random(seed)
    end = time.time() + secs
    solver = stack_solver(rng, R, t, c)
    st = Counter()
    while time.time() < end:
        n, E = planar_random(rng, nmax)
        arcs = general_weights(n, E, rng)
        if not arcs:
            continue
        s = rng.randrange(n)
        ans = theorem1(n, arcs, s, solver, st)
        check_answer(n, arcs, s, ans)
        ST['max_n'] = max(ST['max_n'], n)
    ST['phases'] = st['phases']
    ST['max_B'] = st['max_B']


def fault(seed, runs):
    """A correct potential, then one faulty oracle answer in the last call. The potential check still passes. Only the extra local check sees it."""
    rng = random.Random(seed)
    for _ in range(runs):
        n, E = planar_random(rng, 9)
        arcs = general_weights(n, E, rng)
        if not arcs or bf_all(n, arcs) is None:
            continue
        s = rng.randrange(n)
        phi = scale_potential(n, arcs, bf_solver)
        dist, par, dx = distances_from_potential(n, arcs, phi, s)
        fin = [v for v in range(n) if dx[v] < INF and v != s]
        if not fin:
            continue
        x = rng.choice(fin)
        bad = list(dx)
        bad[x] += 2 * (n + 1)        # one vertex holds a distance that is wrong by one
        xarcs = [(u, v, 2 * ((n + 1) * w + 1)) for u, v, w in arcs]
        pot_ok = all(w + phi[u] - phi[v] >= 0 for u, v, w in xarcs)
        ST['fault.runs'] += 1
        ST['fault.potential_check_passes'] += pot_ok
        # the local certificate: d(s) = 0, d(v) <= d(u) + x(u, v) on all arcs, every finite v != s has a tight in-arc, infinite v has no finite in-neighbour
        ok = bad[s] == 0
        for u, v, w in xarcs:
            if bad[u] < INF and bad[v] > bad[u] + w:
                ok = False
        for v in fin:
            if not any(b == v and bad[a] < INF and bad[a] + w == bad[v] for a, b, w in xarcs):
                ok = False
        ST['fault.local_certificate_fires'] += not ok
        # and it accepts the right answer
        ok2 = dx[s] == 0
        for u, v, w in xarcs:
            if dx[u] < INF and dx[v] > dx[u] + w:
                ok2 = False
        for v in fin:
            if not any(b == v and dx[a] < INF and dx[a] + w == dx[v] for a, b, w in xarcs):
                ok2 = False
        ST['fault.certificate_accepts_truth'] += ok2


def sizes(seed, nlist, W):
    """Largest weight and offset fed to the oracle, as a power of n, with idx up to n (my topological index). [3] has labels up to n^3, so add 2 to the exponents involving idx."""
    rng = random.Random(seed)
    out = []
    for nmax in nlist:
        # a grid with about nmax vertices
        a = int(math.isqrt(nmax))
        n = a * a
        E = []
        for i in range(a):
            for j in range(a):
                x = i * a + j
                if j + 1 < a:
                    E.append((x, x + 1))
                if i + 1 < a:
                    E.append((x, x + a))
        g = nx.Graph(E)
        assert nx.check_planarity(g)[0]
        p = [rng.randrange(-W, W + 1) for _ in range(n)]
        arcs = []
        for x, y in E:
            arcs.append((x, y, p[x] - p[y] + rng.randrange(0, 3)))
            arcs.append((y, x, p[y] - p[x] + rng.randrange(0, 3)))
        STAT.clear()
        solver = stack_solver(rng, 2, 4, 1.0)
        ans = theorem1(n, arcs, 0, solver)
        out.append(dict(n=n, W=W, ans=ans[0], oracle_calls=STAT['oracle'], max_w=STAT['max_w'], max_off=STAT['max_off'],
                        log_n_w=round(math.log(max(STAT['max_w'], 1), n), 2), log_n_off=round(math.log(max(STAT['max_off'], 1), n), 2)))
    return out


if __name__ == '__main__':
    import signal
    def _alarm(*_):  # the alarm survives exec: print what was counted, then stop
        print('ALARM partial', sys.argv[1:], {k: ST[k] for k in sorted(ST)}, flush=True)
        os._exit(0)
    signal.signal(signal.SIGALRM, _alarm)
    a = sys.argv[1:]
    if a[0] == 'exh3':
        exh3(int(a[1]), int(a[2]), float(a[3]), 5)
    elif a[0] == 'lane':
        lane(int(a[1]), float(a[2]), int(a[3]), int(a[4]), int(a[5]), float(a[6]))
    elif a[0] == 'fault':
        fault(int(a[1]), int(a[2]))
    elif a[0] == 'size':
        print(sizes(int(a[1]), [16, 36, 64], int(a[2])))
    print(' '.join(a), {k: ST[k] for k in sorted(ST)})
    if EX:
        print('EX', EX)
