"""Lemma 2 as a black box, tested from the text of [3]: Algorithm 1 and 2 with Definition 21 read literally, Algorithm 3 with the connected
components of Section 5.2. Empirical: cut probability against w/d, weak diameter, zero arcs, cut arcs on paths.
Also the distribution used in neg.py (all the tail mass of the geometric piled on the cap), which differs from Definition 21."""
import math, os, random, sys, time
from collections import Counter, defaultdict
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import networkx as nx
import core_check
from core_check import *
from t2_prop4 import planar_random, restricted_weights, is_restricted, wpos_all

ST = Counter()


def pile_geom(p, cap, rng):
    if p >= 1:
        return 0
    k = 0
    while k < cap and rng.random() >= p:
        k += 1
    return k


def dist_table_compare():
    """Mass at the cap, literal Definition 21 against the piled form, for parameters of the note's runs."""
    out = []
    for n, d in [(100, 64), (100, 512), (625, 4096), (625, 262144)]:
        p = min(math.log2(n) / d, 1.0)
        cap = d // 4
        lit = (1 - p) ** cap * p / (1 - (1 - p) ** (cap + 1))
        pile = (1 - p) ** cap
        out.append(dict(n=n, d=d, p=round(p, 5), cap=cap, mass_at_cap_def21=round(lit, 5), mass_at_cap_piled=round(pile, 4)))
    return out


def cut_stats(n, arcs, d, runs, rng, c):
    wpos = [(u, v, max(w, 0)) for u, v, w in arcs]
    D = [oracle(n, wpos, [0 if x == s else INF for x in range(n)]) for s in range(n)]
    cnt = Counter()
    for _ in range(runs):
        idx = decompose_ldd(n, arcs, d, rng, c)
        ST['ldd.runs'] += 1
        cl = defaultdict(list)
        for v, i in enumerate(idx):
            cl[i].append(v)
        for vs in cl.values():
            for a in vs:
                for b in vs:
                    if D[a][b] > d:
                        ST['FAIL.weak_diameter'] += 1
        for i, (u, v, w) in enumerate(wpos):
            if idx[u] > idx[v]:
                cnt[i] += 1
    worst = 0.0
    zero = 0
    zeros = 0
    for i, (u, v, w) in enumerate(wpos):
        if w == 0:
            zeros += 1
            zero += cnt[i]
        else:
            worst = max(worst, cnt[i] / runs * d / w)
    return worst, zero, zeros


def lane_cut(seed, secs, nmax, c):
    rng = random.Random(seed)
    end = time.time() + secs
    Qmax = 0
    while time.time() < end:
        n, E = planar_random(rng, nmax)
        arcs = restricted_weights(n, E, rng)
        if not arcs:
            continue
        d = 2 ** rng.randrange(1, 11)
        worst, zero, zeros = cut_stats(n, arcs, d, 30, rng, c)
        ST['inst'] += 1
        ST['zero_arc_cuts'] += zero
        ST['zero_arcs_runs'] += zeros * 30
        q = worst / max(math.log2(n) ** 2, 1)
        if q > Qmax:
            Qmax = q
    ST['Qhat_over_log2sq_x1000'] = int(Qmax * 1000)


# ---- Algorithm 3 with connected components

class Topsort:
    def __init__(self, n, arcs, N=None, dil=2, cc_n='own', conn='arcs', net=None):
        self.n = n
        self.arcs = arcs
        self.N = N or n
        self.dil = dil
        self.cc_n = cc_n
        self.conn = conn
        self.net = net or [(a[0], a[1]) for a in arcs]
        self.r = [None] * n
        self.depth = 0
        self.rng = None
        self.bases = []

    def reach(self, X, sources, rev):
        Xs = set(X)
        a = [(v, u, 0) if rev else (u, v, 0) for u, v, *_ in self.arcs if u in Xs and v in Xs]
        off = [INF] * self.n
        for s in sources:
            off[s] = 0
        d = oracle(self.n, a, off)
        return {v for v in X if d[v] == 0}

    def comps(self, R):
        g = nx.Graph()
        g.add_nodes_from(R)
        Rs = set(R)
        for u, v in self.net:
            if u in Rs and v in Rs:
                g.add_edge(u, v)
        return [sorted(c) for c in nx.connected_components(g)]

    def run(self, rng):
        self.rng = rng
        work = [(c, 0, self.n, 0) for c in self.comps(list(range(self.n)))]  # top level: the parent is G itself, as in Section 5.2 of [3]
        Nd = self.N ** self.dil
        while work:
            X, l, size_for_range, dep = work.pop()
            self.depth = max(self.depth, dep)
            n = len(X)
            Xs = set(X)
            m = sum(1 for u, v, *_ in self.arcs if u in Xs and v in Xs)
            order = list(X)
            rng.shuffle(order)

            def S_of(i):
                return self.reach(X, order[:i], False)
            # smallest p with |S_p| + |E_p| >= (n + m) / 2, by binary search
            lo, hi = 1, n

            def big(i):
                S = S_of(i)
                e = sum(1 for u, v, *_ in self.arcs if u in S and v in S)
                return 2 * (len(S) + e) >= n + m
            while lo < hi:
                mid = (lo + hi) // 2
                if big(mid):
                    hi = mid
                else:
                    lo = mid + 1
            p = lo
            A = S_of(p - 1) if p > 1 else set()
            vp = order[p - 1]
            B = self.reach(X, [vp], False)
            Cin = self.reach(X, [vp], True)
            C = B & Cin
            if len(C) == n:
                # line 5. n is the size of this instance ('own') or of the R_j it came from ('parent')
                nn = n if self.cc_n == 'own' else size_for_range
                if self.cc_n == 'leader':       # repair: ell, then the id of a leader; deterministic
                    val = l * (self.N + 1) + min(X)
                    self.bases.append((val, val))
                elif self.cc_n == 'halfopen':   # repair: an interval of at least N^dil values
                    val = rng.randint(l * Nd, (l + n) * Nd - 1)
                    self.bases.append((l * Nd, (l + n) * Nd - 1))
                else:
                    val = rng.randint(l * Nd, (l + nn - 1) * Nd)
                    self.bases.append((l * Nd, (l + nn - 1) * Nd))
                for v in X:
                    self.r[v] = val
                continue
            R1 = Xs - (A | B)
            R2 = A - B
            R3 = C
            R4 = B - (A | C)
            R5 = (A & B) - C
            sizes = [len(R1), len(R2), len(R3), len(R4), len(R5)]
            ls = [l + sum(sizes[j + 1:]) for j in range(5)]
            for R, ll, sz in zip([R1, R2, R3, R4, R5], ls, sizes):
                if not R:
                    continue
                for c in self.comps(sorted(R)):
                    work.append((c, ll, sz, dep + 1))
        return self.r


def lane_topsort(seed, secs, nmax, dil, cc_n, conn):
    rng = random.Random(seed)
    end = time.time() + secs
    while time.time() < end:
        n, E = planar_random(rng, nmax)
        arcs = []
        for a, b in E:
            if rng.random() < 0.7:
                arcs.append((a, b))
            if rng.random() < 0.7:
                arcs.append((b, a))
        # a removed set: the graph handed to Algorithm 3 is the rest. The network stays E.
        kept = [a for a in arcs if rng.random() < 0.8]
        net = list(E) if conn == 'network' else kept
        T = Topsort(n, kept, dil=dil, cc_n=cc_n, net=net)
        r = T.run(rng)
        comp = tarjan(n, kept)
        ST['runs'] += 1
        ST['max_depth'] = max(ST['max_depth'], T.depth)
        for u, v in kept:
            if comp[u] != comp[v] and not r[u] > r[v]:
                ST['FAIL.order'] += 1
        for u in range(n):
            for v in range(u + 1, n):
                if comp[u] == comp[v] and r[u] != r[v]:
                    ST['FAIL.same_scc_diff_label'] += 1
        # collisions of different SCCs
        byl = defaultdict(set)
        for v in range(n):
            byl[r[v]].add(comp[v])
        coll = [s for s in byl.values() if len(s) > 1]
        if coll:
            ST['runs_with_collision'] += 1
            # do the colliding SCCs have an arc of the full input (kept or removed) between them, so inside the 'cluster'?
            for lab, s in byl.items():
                if len(s) > 1:
                    vs = {v for v in range(n) if r[v] == lab}
                    if any(a in vs and b in vs and comp[a] != comp[b] for a, b in arcs):
                        ST['collision_with_arc_inside'] += 1


if __name__ == '__main__':
    import signal
    def _alarm(*_):  # the alarm survives exec: print what was counted, then stop
        print('ALARM partial', sys.argv[1:], {k: ST[k] for k in sorted(ST)}, flush=True)
        os._exit(0)
    signal.signal(signal.SIGALRM, _alarm)
    a = sys.argv[1:]
    if a[0] == 'cut':
        print('table', dist_table_compare())
        lane_cut(int(a[1]), float(a[2]), int(a[3]), float(a[4]))
    elif a[0] == 'cutpile':
        core_check.trunc_geom = pile_geom
        lane_cut(int(a[1]), float(a[2]), int(a[3]), float(a[4]))
    elif a[0] == 'top':
        lane_topsort(int(a[1]), float(a[2]), int(a[3]), int(a[4]), a[5], a[6])
    print(' '.join(a), {k: ST[k] for k in sorted(ST)})
