"""Instrumented token-graph simulator for the claims of 'Naming and sides', 'The cut', the reading
direction and the level / range claims of the proof of the Minimum Cut Theorem.

Inst and token_graph are copied from sim/thmD/checkD/sim.py (the rest of the recursion is that
file's logic, rewritten so that every step can be observed, and with the explicit paths that sim.py
does not keep).

THE ORACLE FOR SIDES. It does not use the rule under test, nor any naming. By Claim Ocurve,
J = C_Q u gamma[q0,q1] is a simple closed curve that crosses exactly the edges of Q and the edges of P
between p_x and p_y, once each, and misses every vertex disc. So the two sides of J are read off from
the components of G - E(C) with E(C) = E(Q) u E(P[x,y]), the low side Lo(J) (which by Claim Osides holds
the part of gamma before q0, q1) is the side of s, and a token is on the side of the vertex at its half
strip: (d,1) at the tail of d, (d,2) at the head of d, (d,0) on the whole strip, which J does not meet.

Rotation convention of sim.py: corner k of v lies between rot[v][k] and rot[v][k+1]; the corner (v,j)
of the paper is corner k = j-1 here. Dart 2e leaves ends[e][0], dart 2e+1 leaves ends[e][1].
"""
import heapq
import collections
import math
import random

INF = float('inf')


class Abort(Exception):
    pass


class Inst:
    def __init__(s, n, ends, rot, cap, S, T, coords=None, tag=''):
        s.n, s.ends, s.rot, s.cap, s.s, s.t = n, [tuple(e) for e in ends], rot, list(cap), S, T
        s.m = len(s.ends)
        s.coords = coords
        s.tag = tag
        s.pos = {d: (v, k) for v, r in enumerate(rot) for k, d in enumerate(r)}
        for d, (v, k) in s.pos.items():
            assert s.ends[d >> 1][d & 1] == v, 'dart 2e leaves first end'
        s.faces, s.face_of = [], {}
        for d0 in range(2 * s.m):
            if d0 in s.face_of:
                continue
            f, d = [], d0
            while d not in s.face_of:
                s.face_of[d] = len(s.faces)
                f.append(d)
                d = s.fnext(d)
            s.faces.append(f)
        s.adj = [[] for _ in range(n)]
        for e, (u, v) in enumerate(s.ends):
            s.adj[u].append((v, e))
            s.adj[v].append((u, e))
        s.prepared = False

    def fnext(s, d):
        v, k = s.pos[d ^ 1]
        r = s.rot[v]
        return r[(k + 1) % len(r)]

    def euler(s):
        return s.n - s.m + len(s.faces)

    def corner_face(s, v, k):
        r = s.rot[v]
        return s.face_of[r[(k + 1) % len(r)]]

    def corner_darts(s, v, k):
        r = s.rot[v]
        return r[k] ^ 1, r[(k + 1) % len(r)]   # in-dart, out-dart of the corner in the walk

    def tail(s, d):
        return s.ends[d >> 1][d & 1]

    def head(s, d):
        return s.ends[d >> 1][(d & 1) ^ 1]

    def connected(s):
        seen = {0}
        st = [0]
        while st:
            u = st.pop()
            for v, _ in s.adj[u]:
                if v not in seen:
                    seen.add(v)
                    st.append(v)
        return len(seen) == s.n

    def dump(s):
        return dict(n=s.n, ends=s.ends, rot=s.rot, cap=s.cap, s=s.s, t=s.t, tag=s.tag)


def mincut(n, ends, caps, S, T):
    """Dinic on an undirected network; independent of the planar machinery."""
    g = [[] for _ in range(n)]
    to, c = [], []
    for (u, v), w in zip(ends, caps):
        g[u].append(len(to))
        to.append(v)
        c.append(w)
        g[v].append(len(to))
        to.append(u)
        c.append(w)
    flow = 0
    while True:
        lev = [-1] * n
        lev[S] = 0
        q = [S]
        for u in q:
            for a in g[u]:
                if c[a] > 0 and lev[to[a]] < 0:
                    lev[to[a]] = lev[u] + 1
                    q.append(to[a])
        if lev[T] < 0:
            return flow
        it = [0] * n

        def dfs(u, f):
            if u == T:
                return f
            while it[u] < len(g[u]):
                a = g[u][it[u]]
                v = to[a]
                if c[a] > 0 and lev[v] == lev[u] + 1:
                    d = dfs(v, min(f, c[a]))
                    if d > 0:
                        c[a] -= d
                        c[a ^ 1] += d
                        return d
                it[u] += 1
            return 0
        while True:
            f = dfs(S, 10 ** 30)
            if not f:
                break
            flow += f


def prepare(I):
    if I.prepared:
        return
    simple = len({frozenset(e) for e in I.ends}) == I.m
    I.simple = simple
    I.N = I.n if simple else max(I.n, I.m + 1)
    I.K = 19 * I.n + 1 if simple else max(19 * I.n + 1, 4 * I.m + 8)
    I.cp = [I.N * I.N * c + 1 for c in I.cap]
    I.W = [I.K * x + 1 for x in I.cp]
    I.mc = mincut(I.n, I.ends, I.cap, I.s, I.t)
    I.mcp = mincut(I.n, I.ends, I.cp, I.s, I.t)
    I.prepared = True


def token_graph(I, inc, cornercuts):
    """Copied from sim.py. returns piece_of[token], pieces[pid]=[tokens], cyclic[pid], partner[token]."""
    cut_after = set(cornercuts)  # (in dart, out dart)
    piece_of, pieces, cyclic = {}, [], []
    for f in I.faces:
        toks = []
        for d in f:
            toks += [(d, 1), (d, 2)] if d >> 1 in inc else [(d, 0)]
        L = len(toks)

        def cut(a, b):
            if a[0] == b[0] and a[1] == 1 and b[1] == 2:
                return True
            return a[0] != b[0] and (a[0], b[0]) in cut_after or (a[0] == b[0] and L == 1 and (a[0], b[0]) in cut_after)
        cuts = [q for q in range(L) if cut(toks[q], toks[(q + 1) % L])]
        if not cuts:
            pid = len(pieces)
            pieces.append(list(toks))
            cyclic.append(True)
            for x in toks:
                piece_of[x] = pid
            continue
        st = (cuts[0] + 1) % L
        rot_t = toks[st:] + toks[:st]
        cur = []
        for q, x in enumerate(rot_t):
            cur.append(x)
            if cut(x, rot_t[(q + 1) % L]):
                pid = len(pieces)
                pieces.append(cur)
                cyclic.append(False)
                for y in cur:
                    piece_of[y] = pid
                cur = []
        assert not cur
    partner = {}
    for e in range(I.m):
        d, r = 2 * e, 2 * e + 1
        if e in inc:
            partner[(d, 1)] = (r, 2)
            partner[(r, 2)] = (d, 1)
            partner[(d, 2)] = (r, 1)
            partner[(r, 1)] = (d, 2)
        else:
            partner[(d, 0)] = (r, 0)
            partner[(r, 0)] = (d, 0)
    return piece_of, pieces, cyclic, partner


def dists(pieces, partner, piece_of, src, W):
    dist = {src: 0}
    pq = [(0, src)]
    done = set()
    while pq:
        dd, u = heapq.heappop(pq)
        if u in done:
            continue
        done.add(u)
        for x in pieces[u]:
            v = piece_of[partner[x]]
            nd = dd + W[x[0] >> 1]
            if nd < dist.get(v, INF):
                dist[v] = nd
                heapq.heappush(pq, (nd, v))
    return dist


class Dag:
    """All shortest src -> tgt paths. An arc is (u, v, x, y): x in u, y in v, a pair."""

    def __init__(s, pieces, partner, piece_of, src, tgt, W):
        dS = dists(pieces, partner, piece_of, src, W)
        dT = dists(pieces, partner, piece_of, tgt, W)
        s.D = dS[tgt]
        s.src, s.tgt = src, tgt
        s.out = collections.defaultdict(list)
        nodes = [u for u in dS if u in dT and dS[u] + dT[u] == s.D]
        for u in nodes:
            for x in pieces[u]:
                y = partner[x]
                v = piece_of[y]
                if v in dT and dS[u] + W[x[0] >> 1] + dT[v] == s.D:
                    s.out[u].append((v, x, y))
        cnt = {tgt: 1}
        for u in sorted(nodes, key=lambda z: -dS[z]):
            if u != tgt:
                cnt[u] = sum(cnt.get(v, 0) for v, _, _ in s.out[u])
        s.count = cnt.get(src, 0)
        s.cnt = cnt

    def enum(s, cap):
        res = []
        nodes, edges = [s.src], []

        def rec(u):
            if len(res) >= cap:
                return
            if u == s.tgt:
                res.append((list(nodes), list(edges)))
                return
            for v, x, y in s.out[u]:
                nodes.append(v)
                edges.append((x, y))
                rec(v)
                nodes.pop()
                edges.pop()
        rec(s.src)
        return res

    def sample(s, rng):
        u = s.src
        nodes, edges = [u], []
        while u != s.tgt:
            r = rng.randrange(s.cnt[u])
            for v, x, y in s.out[u]:
                c = s.cnt.get(v, 0)
                if r < c:
                    nodes.append(v)
                    edges.append((x, y))
                    u = v
                    break
                r -= c
        return nodes, edges


def tree_path(pieces, partner, piece_of, root, tgt, W, seed):
    """The tree of the Exact Trees Lemma: every node picks as parent the arc on a shortest path of
    smallest identifier; identifiers are a seeded hash of the arc, the same for both roots."""
    dist = dists(pieces, partner, piece_of, root, W)
    nodes, edges = [tgt], []
    v = tgt
    while v != root:
        best = None
        for y in pieces[v]:
            x = partner[y]
            u = piece_of[x]
            if dist.get(u, INF) + W[x[0] >> 1] == dist[v]:
                # the identifier of an arc does not depend on the root: hash the unordered pair
                a, b = (x, y) if x < y else (y, x)
                key = (hash((seed, a, b)), x, y, u)
                if best is None or key < best:
                    best = key
        _, x, y, u = best
        nodes.insert(0, u)
        edges.insert(0, (x, y))
        v = u
    return nodes, edges


def rev_path(nodes, edges):
    return nodes[::-1], [(y, x) for x, y in reversed(edges)]


# ---------------------------------------------------------------------- choosers
class FirstCh:
    def pick(self, paths, score=None):
        return 0


class EnumCh:
    """Every sequence of choices, by replay."""

    def __init__(self):
        self.seq, self.lim, self.pos = [], [], 0

    def start(self):
        self.pos = 0

    def pick(self, paths, score=None):
        n = len(paths)
        if n <= 1:
            return 0
        if self.pos < len(self.seq):
            i = self.seq[self.pos]
            self.lim[self.pos] = n
        else:
            i = 0
            self.seq.append(0)
            self.lim.append(n)
        self.pos += 1
        return i

    def advance(self):
        self.seq, self.lim = self.seq[:self.pos], self.lim[:self.pos]
        while self.seq:
            if self.seq[-1] + 1 < self.lim[-1]:
                self.seq[-1] += 1
                return True
            self.seq.pop()
            self.lim.pop()
        return False


class PolicyCh:
    """Worst-case choice among (a sample of) the shortest paths. score(path) gives a dict."""

    def __init__(self, rng, pol):
        self.rng, self.pol = rng, pol

    def pick(self, paths, score=None):
        if len(paths) <= 1:
            return 0
        pol = self.pol
        if pol == 'rand' or score is None:
            return self.rng.randrange(len(paths))
        if pol == 'first':
            return 0
        if pol == 'last':
            return len(paths) - 1
        vals = [score(p)[pol] for p in paths]
        b = max(vals)
        return self.rng.choice([i for i, v in enumerate(vals) if v == b])


class Ctx:
    """Accumulated counters and smallest failing instances."""

    def __init__(self):
        self.C = collections.Counter()
        self.fails = {}
        self.levels_by_m = {}
        self.max_mult = 0
        self.max_piece_mult = 0
        self.max_face_annuli = 0
        self.examples = {}

    def fail(self, name, run, detail=None):
        self.C['FAIL ' + name] += 1
        rec = self.fails.get(name)
        I = run.I
        size = (I.m, I.n)
        if rec is None or size < rec['size']:
            self.fails[name] = dict(size=size, inst=I.dump(), f=run.f, g=run.g, cs=run.cs, ct=run.ct,
                                    seq=list(getattr(run.ch, 'seq', [])), level=run.level, detail=str(detail)[:600],
                                    opts={k: v for k, v in run.opts.items() if isinstance(v, (int, str, bool, float))})

    def example(self, name, run, detail=None):
        rec = self.examples.get(name)
        I = run.I
        size = (I.m, I.n)
        if rec is None or size < rec['size']:
            self.examples[name] = dict(size=size, inst=I.dump(), f=run.f, g=run.g, cs=run.cs, ct=run.ct,
                                       seq=list(getattr(run.ch, 'seq', [])), level=run.level, detail=str(detail)[:600],
                                       opts={k: v for k, v in run.opts.items() if isinstance(v, (int, str, bool, float))})


def sgn_rel(x, y):
    return 'x=y' if x == y else ('x<y' if x < y else 'x>y')


class Run:
    def __init__(self, I, ctx, ch, f, g, cs, ct, opts=None):
        prepare(I)
        self.I, self.ctx, self.ch = I, ctx, ch
        self.C = ctx.C
        self.f, self.g, self.cs, self.ct = f, g, cs, ct
        self.opts = opts or {}
        self.level = 0
        self.walks = []
        self.label = {}
        self.bond_cache = {}
        self.pk = self.opts.get('pick', 'dag')
        self.cap_paths = self.opts.get('cap_paths', 64)
        self.cap_b = self.opts.get('cap_b', 8)

    def fail(self, name, detail=None):
        self.ctx.fail(name, self, detail)

    def chk(self, name, ok, detail=None):
        self.C[name + ' #chk'] += 1
        if not ok:
            self.fail(name, detail)

    # ---------------------------------------------------------------- oracle
    def bond(self, Cset):
        """sides of the closed curve with edge set Cset: (Lo vertex set or None, ok)."""
        key = frozenset(Cset)
        r = self.bond_cache.get(key)
        if r is not None:
            return r
        I = self.I
        seen = {I.s}
        st = [I.s]
        while st:
            u = st.pop()
            for v, e in I.adj[u]:
                if e not in key and v not in seen:
                    seen.add(v)
                    st.append(v)
        lo = seen
        sep = I.t not in lo
        seen = {I.t}
        st = [I.t]
        while st:
            u = st.pop()
            for v, e in I.adj[u]:
                if e not in key and v not in seen:
                    seen.add(v)
                    st.append(v)
        hi = seen
        cover = sep and len(lo) + len(hi) == I.n
        crossing = cover and all((I.ends[e][0] in lo) != (I.ends[e][1] in lo) for e in key)
        r = (lo, sep, cover, crossing)
        self.bond_cache[key] = r
        return r

    def side_token(self, lo, tk):
        d, nu = tk
        v = self.I.head(d) if nu == 2 else self.I.tail(d)
        return 'L' if v in lo else 'H'

    # ---------------------------------------------------------------- pick a path
    def pick(self, pcs, pt, pof, src, tgt, what, score=None):
        I = self.I
        if self.pk == 'tree':
            seed = self.opts.get('idseed', 1)
            r = self.opts.get('root', '0')
            if r == 'rand':
                r = '0' if self.ch.rng.random() < .5 else '1'
            if r == '1':
                n, e = tree_path(pcs, pt, pof, tgt, src, I.W, seed)
                return rev_path(n, e)
            return tree_path(pcs, pt, pof, src, tgt, I.W, seed)
        dag = Dag(pcs, pt, pof, src, tgt, I.W)
        self.C['ties.' + what] += dag.count > 1
        self.C['paths.' + what] += 1
        if self.opts.get('sample') and dag.count > self.cap_paths:
            paths = [dag.sample(self.ch.rng) for _ in range(self.cap_paths)]
            self.C['cap_paths_reached.' + what] += 1
        else:
            paths = dag.enum(self.cap_paths)
            self.C['cap_paths_reached.' + what] += dag.count > self.cap_paths
        i = self.ch.pick(paths, score)
        return paths[i]

    # ---------------------------------------------------------------- level 1 naming (claim A1)
    def naming(self):
        I, C = self.I, self.C
        Pf, Pd, cc, Pe = self.Pf, self.Pd, self.cc, self.Pe
        pof, pcs = self.pof, self.pcs
        m = self.m
        anc_tok = {}
        name = {}
        for t, h in enumerate(Pf):
            ps = sorted({pof[x] for d in I.faces[h] for x in ([(d, 1), (d, 2)] if d >> 1 in self.PeS else [(d, 0)])})
            self.chk('a1.two_pieces', len(ps) == 2, (t, ps))
            if len(ps) != 2:
                raise Abort('a1.two_pieces')
            zero = []
            for p in ps:
                first = pcs[p][0]
                if t > 0:
                    ok = first == (Pd[t - 1] ^ 1, 2)
                else:
                    ok = first[0] == cc[0][1] and first[1] != 2
                if ok:
                    zero.append(p)
            self.chk('a1.exactly_one_0_piece', len(zero) == 1, (t, zero, [pcs[p] for p in ps]))
            if len(zero) != 1:
                raise Abort('a1.zero')
            z = zero[0]
            o = ps[0] if ps[1] == z else ps[1]
            if self.opts.get('name_swap') is not None and t == self.opts['name_swap'] % (m + 1):
                z, o = o, z      # negative control: wrong name at one index
            elif self.opts.get('name_flip'):
                z, o = o, z      # negative control: wrong name at every index
            name[t] = (z, o)
            for x in pcs[z]:
                anc_tok[x] = (t, 0)
            for x in pcs[o]:
                anc_tok[x] = (t, 1)
        # the pair of e_k, with delta in p_{k-1}, joins two such pieces
        for k in range(1, m + 1):
            dl = Pd[k - 1]
            self.chk('a1.pair_joins_0', pof[(dl, 1)] == name[k - 1][0] and pof[(dl ^ 1, 2)] == name[k][0], k)
            self.chk('a1.pair_joins_1', pof[(dl, 2)] == name[k - 1][1] and pof[(dl ^ 1, 1)] == name[k][1], k)
            self.chk('a1.delta_is_last_of_0piece', pcs[name[k - 1][0]][-1] == (dl, 1), k)
            self.chk('a1.revdelta_is_first_of_0piece', pcs[name[k][0]][0] == (dl ^ 1, 2), k)
            # negative control: the convention with delta in p_k instead
            C['ctlA1.delta_in_p_k #chk'] += 1
            dd = dl ^ 1
            if not (pof[(dd, 1)] == name[k][0] and pof[(dd ^ 1, 2)] == name[k - 1][0]):
                C['ctlA1.delta_in_p_k #caught'] += 1
        # ends of the 0-piece of p_0, of p_m
        self.chk('a1.c_star_s_starts_0piece', pcs[name[0][0]][0][0] == cc[0][1], None)
        self.chk('a1.c_star_t_ends_0piece', pcs[name[m][0]][-1][0] == cc[1][0], None)
        self.chk('a1.c_star_t_starts_1piece', pcs[name[m][1]][0][0] == cc[1][1], None)
        self.chk('a1.c_star_s_ends_1piece', pcs[name[0][1]][-1][0] == cc[0][0], None)
        # second naming, by pair propagation from p_0 alone (the sides of gamma, without the local rule)
        pr = {0: name[0]}
        for k in range(1, m + 1):
            dl = Pd[k - 1]
            a = pof[(dl ^ 1, 2)] if pof[(dl, 1)] == pr[k - 1][0] else pof[(dl ^ 1, 1)]
            b = [p for p in {pof[x] for d in I.faces[Pf[k]] for x in ([(d, 1), (d, 2)] if d >> 1 in self.PeS else [(d, 0)])} if p != a][0]
            pr[k] = (a, b)
        self.chk('a1.rule_equals_pair_propagation', all(pr[t] == name[t] for t in range(m + 1)), None)
        self.name = name
        self.anc_tok = anc_tok
        C['a1.P_faces'] += m + 1
        C['a1.m=0'] += m == 0
        if I.coords is not None:
            self.geo_check()

    def geo_check(self):
        """True sides of gamma in a straight-line drawing: for every face of P that is a strictly convex
        bounded polygon, gamma_t is the straight segment from its entry to its exit, and the signed area of
        (arc of a piece) + (gamma_t reversed) tells on which side of gamma_t the piece lies."""
        I, C = self.I, self.C
        xy = I.coords
        res = []
        for t, h in enumerate(self.Pf):
            vs = [I.tail(d) for d in I.faces[h]]
            if len(set(vs)) != len(vs) or len(vs) < 3:
                C['a1.geo.skip_face'] += 1
                return
            area = 0.0
            sg = set()
            L = len(vs)
            for q in range(L):
                ax, ay = xy[vs[q]]
                bx, by = xy[vs[(q + 1) % L]]
                cx, cy = xy[vs[(q + 2) % L]]
                area += ax * by - bx * ay
                cr = (bx - ax) * (cy - by) - (by - ay) * (cx - bx)
                sg.add(cr > 1e-9)
                if abs(cr) <= 1e-9:
                    sg.add('flat')
            if 'flat' in sg or len(sg) != 1 or area >= 0:   # bounded faces are walked clockwise
                C['a1.geo.skip_face'] += 1
                return
            cen = (sum(xy[v][0] for v in vs) / L, sum(xy[v][1] for v in vs) / L)

            def mid(d):
                a, b = xy[I.tail(d)], xy[I.head(d)]
                return ((a[0] + b[0]) / 2, (a[1] + b[1]) / 2)

            def near(v):
                a = xy[v]
                return (a[0] + .1 * (cen[0] - a[0]), a[1] + .1 * (cen[1] - a[1]))
            E = near(I.s) if t == 0 else mid(self.Pd[t - 1] ^ 1)
            X = near(I.t) if t == self.m else mid(self.Pd[t])
            sides = []
            for sigma, p in enumerate(self.name[t]):
                pts = [E if sigma == 0 else X]
                for d, nu in self.pcs[p]:
                    a, b = xy[I.tail(d)], xy[I.head(d)]
                    if nu == 0:
                        pts += [a, b]
                    elif nu == 1:
                        pts += [a, mid(d)]
                    else:
                        pts += [mid(d), b]
                pts.append(X if sigma == 0 else E)
                A = 0.0
                for q in range(len(pts)):
                    (ax, ay), (bx, by) = pts[q], pts[(q + 1) % len(pts)]
                    A += ax * by - bx * ay
                if abs(A) < 1e-12:
                    C['a1.geo.skip_face'] += 1
                    return
                # sigma 0: closing edge runs from X to E; region left of X->E is right of E->X
                if sigma == 0:
                    sides.append('R' if A > 0 else 'L')
                else:
                    sides.append('L' if A > 0 else 'R')
            res.append(tuple(sides))
        C['a1.geo.runs'] += 1
        for sides in res:
            C['a1.geo.faces'] += 1
            self.chk('a1.geo.pieces_on_different_sides', sides[0] != sides[1], res)
            self.chk('a1.geo.0piece_left_of_gamma', sides[0] == 'L', res)
        self.chk('a1.geo.same_side_along_P', len(set(res)) == 1, res)

    def face_convex(self, h):
        I = self.I
        cache = getattr(I, '_conv', None)
        if cache is None:
            cache = I._conv = {}
        if h in cache:
            return cache[h]
        xy = I.coords
        vs = [I.tail(d) for d in I.faces[h]]
        ok = len(set(vs)) == len(vs) and len(vs) >= 3
        if ok:
            area, sg, L = 0.0, set(), len(vs)
            for q in range(L):
                ax, ay = xy[vs[q]]
                bx, by = xy[vs[(q + 1) % L]]
                cx, cy = xy[vs[(q + 2) % L]]
                area += ax * by - bx * ay
                cr = (bx - ax) * (cy - by) - (by - ay) * (cx - bx)
                sg.add('flat' if abs(cr) <= 1e-9 else cr > 0)
            ok = 'flat' not in sg and len(sg) == 1 and area < 0
        cache[h] = ok
        return ok

    def geo_J(self, Qn, Qe, x, y, lov, pcs):
        """J drawn as an honest polygon: straight chords in strictly convex bounded faces, through the midpoints
        of the edges it crosses; the two sides of all vertices by winding number. This checks the
        vertex-bipartition oracle itself, and the rule, without the graph G - E(C)."""
        I, C = self.I, self.C
        faces = [self.Pf[z] for z in range(min(x, y), max(x, y) + 1)] + [I.face_of[pcs[u][0][0]] for u in Qn[1:-1]]
        if not all(self.face_convex(h) for h in faces):
            C['a2.geo.skip_incision'] += 1
            return
        xy = I.coords

        def mid(e):
            a, b = xy[I.ends[e][0]], xy[I.ends[e][1]]
            return ((a[0] + b[0]) / 2, (a[1] + b[1]) / 2)

        def centroid(h):
            vs = [I.tail(d) for d in I.faces[h]]
            return (sum(xy[v][0] for v in vs) / len(vs), sum(xy[v][1] for v in vs) / len(vs))

        def near(v, h):
            a, c = xy[v], centroid(h)
            return (a[0] + .1 * (c[0] - a[0]), a[1] + .1 * (c[1] - a[1]))

        def gamma_ends(t):
            h = self.Pf[t]
            E = near(I.s, h) if t == 0 else mid(self.Pe[t - 1])
            X = near(I.t, h) if t == self.m else mid(self.Pe[t])
            return E, X

        def lerp(a, b, u):
            return (a[0] + u * (b[0] - a[0]), a[1] + u * (b[1] - a[1]))
        Ex, Xx = gamma_ends(x)
        Ey, Xy = gamma_ends(y)
        q0 = lerp(Ex, Xx, 0.37)
        q1 = lerp(Ey, Xy, 0.61)
        poly = [q0] + [mid(a[0] >> 1) for a, b in Qe] + [q1]
        if y > x:
            poly += [mid(self.Pe[z - 1]) for z in range(y, x, -1)]
        elif y < x:
            poly += [mid(self.Pe[z]) for z in range(y, x)]

        def wind(p):
            tot = 0.0
            for q in range(len(poly)):
                ax, ay = poly[q][0] - p[0], poly[q][1] - p[1]
                bx, by = poly[(q + 1) % len(poly)][0] - p[0], poly[(q + 1) % len(poly)][1] - p[1]
                tot += math.atan2(ax * by - ay * bx, ax * bx + ay * by)
            return abs(tot) > 3.0
        ins = [wind(xy[v]) for v in range(I.n)]
        C['a2.geo.incisions'] += 1
        # Claim Oorient, proof: Lo(J) lies on the right of C_Q in the paper's hand; left there is the hand of the face in
        # walk order, which is the geometric right here (bounded faces are walked clockwise), so Lo is geometrically left.
        for q in range(len(Qe) + 1):
            (ax, ay), (bx, by) = poly[q], poly[q + 1]
            eps = 1e-4
            pm = ((ax + bx) / 2 - eps * (by - ay), (ay + by) / 2 + eps * (bx - ax))
            self.chk('new.geo.Lo_on_paper_right_of_C_Q', wind(pm) == ins[I.s], (x, y, q))
        self.chk('a2.geo.s_t_on_different_sides', ins[I.s] != ins[I.t], (x, y))
        self.chk('a2.geo.polygon_equals_bipartition', all((ins[v] == ins[I.s]) == (v in lov) for v in range(I.n)), (x, y))
        for a, b in Qe:
            if a[1] == 0:
                C['a2.geo.new_edges'] += 1
                C['a2.geo.new_edges|' + sgn_rel(x, y)] += 1
                self.chk('a2.geo.rule', ins[I.tail(a[0])] == ins[I.s] and ins[I.head(a[0])] == ins[I.t], (a, x, y))

    # ---------------------------------------------------------------- the part (mode) check
    def er_partition(self, Inc, mus, mut, pof, pcs):
        """Components of G^_l[E_R] for the endpoint modes (Appendix A), against the pieces."""
        I = self.I
        par = {}

        def find(a):
            r = a
            while par.setdefault(r, r) != r:
                r = par[r]
            while par[a] != r:
                par[a], a = r, par[a]
            return r

        def tau(d):
            v, k = I.pos[d]
            return (v, (k - 1) % len(I.rot[v]))

        def eta(d):
            v, k = I.pos[d ^ 1]
            return (v, k)
        cs_c, ct_c = (I.s, self.cs), (I.t, self.ct)
        moved = {}
        for (c, mu) in ((cs_c, mus), (ct_c, mut)):
            din, dout = I.corner_darts(*c)
            if mu == 'L':
                moved[(din, 0 if din >> 1 not in Inc else 2, 'b')] = ('X', c)
            else:
                moved[(dout, 0 if dout >> 1 not in Inc else 1, 'a')] = ('X', c)
        tokc = {}
        deg = collections.Counter()
        for d in range(2 * I.m):
            for nu in ((1, 2) if d >> 1 in Inc else (0,)):
                if nu == 0:
                    a, b = ('D', tau(d)), ('D', eta(d))
                elif nu == 1:
                    a, b = ('D', tau(d)), ('L', eta(d))
                else:
                    a, b = ('R', tau(d)), ('D', eta(d))
                a = moved.get((d, nu, 'a'), a)
                b = moved.get((d, nu, 'b'), b)
                deg[a] += 1
                deg[b] += 1
                ra, rb = find(a), find(b)
                par[ra] = rb
                tokc[(d, nu)] = a
        partition = collections.defaultdict(set)
        for tk, a in tokc.items():
            partition[find(a)].add(tk)
        got = {frozenset(v) for v in partition.values()}
        want = {frozenset(p) for p in pcs}
        self.chk('mode.E_R_components_are_pieces', got == want, (mus, mut, len(got), len(want)))
        self.chk('mode.E_R_max_degree_2', max(deg.values()) <= 2, (mus, mut))

    # ---------------------------------------------------------------- one computed walk (claim B)
    def anc(self, x):
        d = x[0]
        if d >> 1 in self.PeS:
            return self.anc_tok.get(x)
        return self.anc_tok.get((d, 0))

    def check_walk(self, nodes, es, t, tag, level, pcs, overlap=False):
        I, C = self.I, self.C
        cp = I.cp
        lab = [self.anc(pcs[u][0]) for u in nodes]
        w = sum(I.W[x[0] >> 1] for x, y in es)
        cW = sum(cp[x[0] >> 1] for x, y in es)
        self.chk('b.W_simple', len(set(nodes)) == len(nodes), (t, tag, overlap))
        self.chk('b.W_length_is_lambda_t', w == self.lam[t], (t, tag, w, self.lam[t]))
        self.chk('b.W_ends', lab[0] == (t, 0) and lab[-1] == (t, 1), (t, lab[0], lab[-1]))
        q0s = [q for q, a in enumerate(lab) if a and a[1] == 0]
        q1s = [q for q, a in enumerate(lab) if a and a[1] == 1 and q > q0s[-1]] if q0s else []
        if not q0s or not q1s:
            self.fail('b.xy_undefined', (t, lab))
            return
        q0, q1 = q0s[-1], q1s[0]
        x, y = lab[q0][0], lab[q1][0]
        U, Qp, V = es[:q0], es[q0:q1], es[q1:]
        cU = sum(cp[a[0] >> 1] for a, b in U)
        cV = sum(cp[a[0] >> 1] for a, b in V)
        dP = lambda a, b: abs(self.Pcp[a] - self.Pcp[b])
        self.chk('b.cU_ge_P', cU >= dP(t, x), (t, x, cU, dP(t, x)))
        self.chk('b.cV_ge_P', cV >= dP(t, y), (t, y, cV, dP(t, y)))
        # the part Q'
        inner = nodes[q0 + 1:q1]
        inner_f = [I.face_of[pcs[u][0][0]] for u in inner]
        self.chk('b.inner_off_P', all(lab[q] is None for q in range(q0 + 1, q1)), (t, lab))
        self.chk('b.inner_distinct_faces', len(set(inner_f)) == len(inner_f) and not (set(inner_f) & self.PfS), (t, inner_f))
        Qedges = [a[0] >> 1 for a, b in Qp]
        self.chk('b.no_edge_copy_of_P', not (set(Qedges) & self.PeS), (t, Qedges))
        Pmid = self.Pe[min(x, y):max(x, y)]
        Cedges = Qedges + Pmid
        self.chk('b.C_edges_distinct', len(set(Cedges)) == len(Cedges), (t, Cedges))
        # the closed walk in G*: faces p_x f_1 .. f_r p_y p_(y-+1) .. back to p_x
        cyc_faces = [self.Pf[x]] + inner_f + ([self.Pf[y]] if x != y else [])
        if x != y:
            mid = range(y - 1, x, -1) if y > x else range(y + 1, x)
            cyc_faces += [self.Pf[z] for z in mid]
        is_loop = x == y and len(Qp) == 1
        self.chk('b.C_simple_cycle_or_loop', len(set(cyc_faces)) == len(cyc_faces), (t, cyc_faces))
        if is_loop:
            d = Qp[0][0][0]
            self.chk('b.loop_is_dual_loop', I.face_of[d] == I.face_of[d ^ 1] == self.Pf[x], (t, d))
        else:
            # consecutive faces of the closed walk are joined by the edges of C
            seq = [I.face_of[a[0]] for a, b in Qp] + [I.face_of[Qp[-1][1][0]]]
            self.chk('b.Q_image_is_walk', seq[0] == self.Pf[x] and seq[-1] == self.Pf[y], (t, seq))
        lo, sep, cover, crossing = self.bond(Cedges)
        self.chk('b.bond_separates_s_t', sep, (t, Cedges))
        self.chk('b.bond_exactly_two_components', cover, (t, Cedges))
        self.chk('b.bond_every_edge_crosses', crossing, (t, Cedges))
        cC = sum(cp[e] for e in Cedges)
        self.chk('b.C_no_longer_than_W', cC <= cW, (t, cC, cW))
        self.chk('b.C_at_least_mincut', cC >= I.mcp, (t, cC, I.mcp))
        cut_c = sum(I.cap[e] for e, (a, b) in enumerate(I.ends) if (a in lo) != (b in lo))
        rel = sgn_rel(x, y)
        C['b.stat.walks'] += 1
        C['b.stat.' + rel] += 1
        C['b.stat.overlap'] += overlap
        C['b.stat.loop'] += is_loop
        C['b.stat.Q1edge'] += len(Qp) == 1
        C['b.stat.U_longer_than_P'] += cU > dP(t, x)
        C['b.stat.strict_shortcut'] += cC < cW
        self.walks.append(dict(w=w, cp=cW, t=t, seq=len(self.walks), overlap=overlap, loop=is_loop, x=x, y=y, cC=cC,
                               ok=sep and cover and crossing, cut_c=cut_c, tag=tag, level=level, Qlen=len(Qp)))
        # negative controls for B: wrong rules that must be caught
        if x != y:
            r = self.bond(Qedges)
            C['ctlB.no_closure #chk'] += 1
            C['ctlB.no_closure #caught'] += not (r[1] and r[2] and r[3])
        if q0 != 0:
            q1b = min(q for q, a in enumerate(lab) if a and a[1] == 1)
            Qb = es[0:q1b]
            yb = lab[q1b][0]
            Eb = [a[0] >> 1 for a, b in Qb] + self.Pe[min(t, yb):max(t, yb)]
            r = self.bond(Eb)
            C['ctlB.first_0_piece #chk'] += 1
            bad = len(set(Eb)) != len(Eb) or bool(set(a[0] >> 1 for a, b in Qb) & self.PeS) or not (r[1] and r[2] and r[3])
            C['ctlB.first_0_piece #caught'] += bad
        Ewh = [a[0] >> 1 for a, b in es]
        r = self.bond(Ewh)
        C['ctlB.whole_W #chk'] += 1
        C['ctlB.whole_W #caught'] += bool(set(Ewh) & self.PeS) or not (r[1] and r[2] and r[3]) or len(set(Ewh)) != len(Ewh)
        # wrong capacity bound: c'(U) >= c'(P[0,x]) instead of c'(P[t,x])
        C['ctlB.U_ge_P0x #chk'] += 1
        C['ctlB.U_ge_P0x #caught'] += cU < self.Pcp[x]

    # ---------------------------------------------------------------- derived data of a path
    def derive(self, nodes, es, pcs, wrong=False):
        lab = [self.anc(pcs[u][0]) for u in nodes]
        ps = [a for a in lab if a]
        i1, i2 = min(a[0] for a in ps), max(a[0] for a in ps)
        if wrong:
            q1 = min(q for q, a in enumerate(lab) if a and a[1] == 1)
            q0 = max(q for q, a in enumerate(lab) if q < q1 and a and a[1] == 0)
        else:
            q0 = max(q for q, a in enumerate(lab) if a and a[1] == 0)
            q1 = min(q for q, a in enumerate(lab) if q > q0 and a and a[1] == 1)
        sg = [a[1] for a in ps]
        alt = sum(sg[q] != sg[q + 1] for q in range(len(sg) - 1))
        return dict(x=lab[q0][0], y=lab[q1][0], i1=i1, i2=i2, q0=q0, q1=q1, alt=alt,
                    Q=tuple(a[0] >> 1 for a, b in es[q0:q1]))

    # ---------------------------------------------------------------- the recursion
    def go(self):
        I, C = self.I, self.C
        W = I.W
        f, g = self.f, self.g
        # level 0: P
        pof0, pc0, _, pt0 = token_graph(I, set(), [])
        src, tgt = pof0[(I.faces[f][0], 0)], pof0[(I.faces[g][0], 0)]
        if src == tgt:
            nodes, es = [src], []
        else:
            nodes, es = self.pick(pc0, pt0, pof0, src, tgt, 'P')
        self.Pf = [I.face_of[pc0[x][0][0]] for x in nodes]
        self.PfS = set(self.Pf)
        self.Pe = [x[0] >> 1 for x, y in es]
        self.PeS = set(self.Pe)
        self.Pd = [x[0] for x, y in es]     # Pd[k] = dart of e_{k+1} in p_k
        self.m = m = len(self.Pf) - 1
        self.Pcp = [0]
        for e in self.Pe:
            self.Pcp.append(self.Pcp[-1] + I.cp[e])
        assert I.corner_face(I.s, self.cs) == f and I.corner_face(I.t, self.ct) == g
        self.cc = cc = [I.corner_darts(I.s, self.cs), I.corner_darts(I.t, self.ct)]
        Inc = set(self.Pe)
        self.pof, self.pcs, _, self.pt = pof, pcs, cyc, pt = token_graph(I, Inc, cc)
        self.level = 1
        # P is shortest for c' too
        dc = dists(pc0, pt0, pof0, src, I.cp)
        self.chk('b.P_shortest_for_cprime', dc[tgt] == self.Pcp[-1] if src != tgt else True, (dc.get(tgt), self.Pcp[-1]))
        # corners, modes
        mode_s, mode_t = [], []
        for (c, lst) in (((I.s, self.cs), mode_s), ((I.t, self.ct), mode_t)):
            din, dout = I.corner_darts(*c)
            if din >> 1 not in self.PeS:
                lst.append('L')
            if dout >> 1 not in self.PeS:
                lst.append('R')
            self.chk('mode.exists_flank_off_P', bool(lst), c)
        self.modes = mode_s, mode_t
        C['mode.s=' + ''.join(mode_s)] += 1
        C['mode.t=' + ''.join(mode_t)] += 1
        # A_1 connected
        s0 = {0}
        st = [0]
        while st:
            u = st.pop()
            for x in pcs[u]:
                v = pof[pt[x]]
                if v not in s0:
                    s0.add(v)
                    st.append(v)
        self.chk('inv.A1_connected', len(s0) == len(pcs), None)
        self.naming()
        anc = self.anc
        self.lam = lam = {}
        name = self.name
        for t in range(m + 1):
            lam[t] = dists(pcs, pt, pof, name[t][0], W)[name[t][1]]
        live = [dict(root=pcs[0][0], j=0, k=m, Pa=[], Pb=[], parent_len=None)]
        level = 1
        maxlev = 0
        self.nincisions = 0
        while live:
            self.level = level
            maxlev = level
            pof, pcs, cyc, pt = token_graph(I, Inc, cc)
            self.pof, self.pcs, self.pt = pof, pcs, pt
            # modes: components of G^[E_R] are the pieces, in all allowed modes
            if self.opts.get('ghat', True):
                for mus in mode_s:
                    for mut in mode_t:
                        self.er_partition(Inc, mus, mut, pof, pcs)
            self.level_ranges(live)
            newinc = set()
            allseen = set()
            piece_face_count = collections.Counter()
            face_annuli = collections.defaultdict(set)
            for A in live:
                seen = {pof[A['root']]}
                st = [pof[A['root']]]
                while st:
                    u = st.pop()
                    for x in pcs[u]:
                        v = pof[pt[x]]
                        if v not in seen:
                            seen.add(v)
                            st.append(v)
                self.chk('d.annuli_disjoint', not (seen & allseen), level)
                allseen |= seen
                A['seen'] = seen
                G = {}
                for u in seen:
                    labs = {anc(x) for x in pcs[u]}
                    self.chk('inv.piece_refines_one_name', len(labs) == 1, (u, labs))
                    a = anc(pcs[u][0])
                    if a is not None:
                        self.chk('inv.pieces_unique', a not in G, a)
                        G[a] = u
                        piece_face_count[a] += 1
                        face_annuli[a[0]].add(id(A))
                ff = [I.face_of[pcs[u][0][0]] for u in seen if anc(pcs[u][0]) is None]
                self.chk('inv.offP_pieces_unique', len(ff) == len(set(ff)), None)
                # text changed during the run: (Old) and the reason given in "The cut"
                Pes = set(self.Pe)
                cnt_e = collections.Counter(tk[0] >> 1 for u in seen for tk in pcs[u])
                for e, ce in cnt_e.items():
                    if e not in Pes:
                        self.chk('new.old_at_most_one_pair_of_edge_off_P', ce <= 2, (e, ce))
                for u in seen:
                    for tk in pcs[u]:
                        if tk[0] >> 1 in Pes:
                            a1_, a2_ = anc(tk), anc(pt[tk])
                            self.chk('new.copy_of_P_edge_joins_pieces_on_one_side', a1_ is not None and a2_ is not None and a1_[1] == a2_[1], (tk, a1_, a2_))
                for a_ in G:
                    C['d.pieces_named'] += 1
                    C['d.piece_outside_range'] += not (A['j'] <= a_[0] <= A['k'])
                A['G'] = G
                self.check_labels(A, seen, pcs, pt, level)
                j, k = A['j'], A['k']
                if k <= j + 1:
                    self.compute(A, j, 'leaf', level, G, pcs, pt, pof)
                    if k != j:
                        self.compute(A, k, 'leaf', level, G, pcs, pt, pof)
                    C['d.leaves'] += 1
                    continue
                self.nincisions += 1
                i = (j + k) // 2
                self.chk('inv.Pi_ends_exist', (i, 0) in G and (i, 1) in G, (i, sorted(G)))
                src, tgt = G[(i, 0)], G[(i, 1)]
                bset = {u for pr_ in A['Pa'] for tk in pr_ for u in (pof[tk],)}
                bset |= {u for pr_ in A['Pb'] for tk in pr_ for u in (pof[tk],)}

                def score(p, pcs=pcs, bset=bset):
                    nodes, es = p
                    lab = [anc(pcs[u][0]) for u in nodes]
                    ps = [a for a in lab if a]
                    sg = [a[1] for a in ps]
                    return dict(maxP=len(ps), alt=sum(sg[q] != sg[q + 1] for q in range(len(sg) - 1)),
                                touch=sum(u in bset for u in nodes),
                                untouch=-sum(u in bset for u in nodes),
                                far=max(a[0] for a in ps) - min(a[0] for a in ps),
                                near=min(a[0] for a in ps) - max(a[0] for a in ps),
                                maxold=sum(1 for x, y in es if x[1]),
                                minold=-sum(1 for x, y in es if x[1]))
                nodes, es = self.pick(pcs, pt, pof, src, tgt, 'Pi', score)
                wl = sum(W[x[0] >> 1] for x, y in es)
                self.chk('inv.Pi_dist', wl == lam[i], (i, wl, lam[i]))
                self.check_all_walks(A, i, 'Pi', level, G, pcs, pt, pof, (nodes, es))
                if self.opts.get('c_stats'):
                    self.c_stats(src, tgt, nodes, es, pcs, pt, pof)
                read = self.opts.get('read', '0')
                if read == 'rand':
                    read = '0' if self.ch.rng.random() < .5 else 'wrong'
                D = self.derive(nodes, es, pcs, wrong=(read == 'wrong'))
                D0 = D if read == '0' else self.derive(nodes, es, pcs)
                q0, q1, x, y, i1, i2 = D['q0'], D['q1'], D['x'], D['y'], D['i1'], D['i2']
                C['c.alternations>1'] += D['alt'] > 1
                C['c.Pi_seen'] += 1
                if read != '0':
                    C['c.wrong_Q_differs'] += D['Q'] != D0['Q']
                Qn, Qe = nodes[q0:q1 + 1], es[q0:q1]
                self.chk('q.inner_off_P', all(anc(pcs[u][0]) is None for u in Qn[1:-1]), None)
                self.chk('q.hull', (i1, i2) == (min(i, x, y), max(i, x, y)), (i1, i2, i, x, y))
                for t in sorted({max(i1, j), min(i2, k)} - {i}):
                    self.compute(A, t, 'end', level, G, pcs, pt, pof)
                pa_nodes = {pof[tk] for pr_ in A['Pa'] for tk in pr_}
                pb_nodes = {pof[tk] for pr_ in A['Pb'] for tk in pr_}
                common_a = sorted(pa_nodes & set(nodes))
                common_b = sorted(pb_nodes & set(nodes))
                ova, ovb = bool(common_a), bool(common_b)
                if ova:
                    self.overlap(A, common_a, range(j, i + 1), level, G, pcs, pt, pof, 'a')
                if ovb:
                    self.overlap(A, common_b, range(i, k + 1), level, G, pcs, pt, pof, 'b')
                hi, lo = [], []
                newq = []
                for a, b in Qe:
                    e = a[0] >> 1
                    if a[1] == 0:
                        dd = a[0]
                        if self.opts.get('rule') == 'readdir' and read == 'wrong' or self.opts.get('rule') == 'flip':
                            H, Lw = frozenset([(dd, 1), (dd ^ 1, 2)]), frozenset([(dd, 2), (dd ^ 1, 1)])
                        else:
                            H, Lw = frozenset([(dd, 2), (dd ^ 1, 1)]), frozenset([(dd, 1), (dd ^ 1, 2)])
                        hi.append(H)
                        lo.append(Lw)
                        self.label[H] = 'H'
                        self.label[Lw] = 'L'
                        newinc.add(e)
                        newq.append(e)
                    else:
                        hi.append(frozenset([a, b]))
                        lo.append(frozenset([a, b]))
                A['_q'] = dict(hi=hi, lo=lo, i=i, i1=i1, i2=i2, x=x, y=y, ova=ova, ovb=ovb, Qn=Qn, Qe=Qe, nodes=nodes, es=es,
                               newq=newq, pa_nodes=pa_nodes, pb_nodes=pb_nodes, read=read)
            mpm = max(piece_face_count.values(), default=0)
            mfa = max((len(v) for v in face_annuli.values()), default=0)
            self.ctx.max_piece_mult = max(self.ctx.max_piece_mult, mpm)
            self.ctx.max_face_annuli = max(self.ctx.max_face_annuli, mfa)
            C['d.annuli_holding_piece_of_one_p_t^sigma>2'] += mpm > 2
            C['d.annuli_holding_piece_of_one_face>2'] += mfa > 2
            if mpm > 2:
                self.ctx.example('d.piece_mult>2', self, (mpm, sorted((A['j'], A['k']) for A in live)))
            C['d.level_checked'] += 1
            # next level
            Inc2 = Inc | newinc
            pof2, pcs2, cyc2, pt2 = token_graph(I, Inc2, cc)
            nxt = []
            for A in live:
                if '_q' not in A:
                    continue
                self.check_incision(A, Inc, Inc2, newinc, pcs, pof, pt, pcs2, pof2, pt2, nxt)
            for c in nxt:
                c['parent_len'] = c['parent_len']
            Inc = Inc2
            live = nxt
            level += 1
        self.final(maxlev)
        return maxlev

    def level_ranges(self, live):
        C = self.C
        R = sorted((A['j'], A['k']) for A in live)
        C['d.levels_with_ranges'] += 1
        C['d.live_annuli'] += len(R)
        for a in range(len(R)):
            for b in range(a + 1, len(R)):
                j1, k1 = R[a]
                j2, k2 = R[b]
                ov = min(k1, k2) - max(j1, j2) + 1
                C['d.range_pairs'] += 1
                if ov > 0:
                    C['d.range_pairs_sharing'] += 1
                    s = max(j1, j2)
                    self.chk('d.share_at_most_one_index', ov == 1, (R[a], R[b]))
                    if ov == 1:
                        self.chk('d.shared_index_is_end_of_both', s in (j1, k1) and s in (j2, k2), (R[a], R[b]))
        mult = collections.Counter()
        for j, k in R:
            for t in range(j, k + 1):
                mult[t] += 1
        mx = max(mult.values(), default=0)
        self.ctx.max_mult = max(self.ctx.max_mult, mx)
        C['d.index_mult>2'] += mx > 2
        if mx > 2:
            self.ctx.example('d.index_mult>2', self, R)
        for A in live:
            if A.get('parent_len') is not None:
                self.chk('d.range_halves', (A['k'] - A['j']) <= (A['parent_len'] + 1) // 2, (A['j'], A['k'], A['parent_len']))

    def check_all_walks(self, A, t, tag, level, G, pcs, pt, pof, chosen):
        I = self.I
        if self.opts.get('b_all', True):
            dag = Dag(pcs, pt, pof, G[(t, 0)], G[(t, 1)], I.W)
            paths = dag.enum(self.cap_b)
            if chosen not in paths:
                paths.append(chosen)
            self.C['b.stat.tied_W'] += len(paths) > 1
        else:
            paths = [chosen]
        for n, e in paths:
            self.check_walk(n, e, t, tag, level, pcs)

    def compute(self, A, t, tag, level, G, pcs, pt, pof):
        I = self.I
        if (t, 0) not in G or (t, 1) not in G:
            self.fail('inv.compute_piece_missing', (t, tag, sorted(G)))
            raise Abort('missing')
        src, tgt = G[(t, 0)], G[(t, 1)]
        if self.pk == 'tree':
            nodes, es = self.pick(pcs, pt, pof, src, tgt, 'W')
        else:
            dag = Dag(pcs, pt, pof, src, tgt, I.W)
            nodes, es = dag.enum(1)[0]
        wl = sum(I.W[x[0] >> 1] for x, y in es)
        self.chk('inv.compute_dist', wl == self.lam[t], (t, tag, wl, self.lam[t]))
        self.check_all_walks(A, t, tag, level, G, pcs, pt, pof, (nodes, es))

    def overlap(self, A, common, rng_t, level, G, pcs, pt, pof, which):
        I, C = self.I, self.C
        C['overlap.' + which] += 1
        zs = common
        idx = self.ch.pick(zs) if self.pk != 'tree' else 0
        z = zs[idx]
        dz = dists(pcs, pt, pof, z, I.W)
        for t in rng_t:
            v = dz[G[(t, 0)]] + dz[G[(t, 1)]]
            self.chk('c23.sum_is_lambda', v == self.lam[t], (t, v, self.lam[t], which))
            for sd in ((1, 2) if self.opts.get('b_all', True) else (1,)):
                a = tree_path(pcs, pt, pof, z, G[(t, 0)], I.W, sd)
                b = tree_path(pcs, pt, pof, z, G[(t, 1)], I.W, sd)
                rn, re = rev_path(*a)
                nodes = rn + b[0][1:]
                es = re + b[1]
                self.check_walk(nodes, es, t, 'ov', level, pcs, overlap=True)
        for z2 in zs:
            if z2 == z:
                continue
            dz2 = dists(pcs, pt, pof, z2, I.W)
            for t in rng_t:
                self.chk('c23.every_common_node', dz2[G[(t, 0)]] + dz2[G[(t, 1)]] == self.lam[t], (t, z2, which))

    # ---------------------------------------------------------------- A4: labels decide the bound
    def check_labels(self, A, seen, pcs, pt, level):
        C = self.C
        PaS, PbS = set(A['Pa']), set(A['Pb'])
        self.chk('a4.bounds_have_no_common_pair', not (PaS & PbS), None)
        pof = self.pof
        pa_nodes = {pof[tk] for pr_ in PaS for tk in pr_}
        pb_nodes = {pof[tk] for pr_ in PbS for tk in pr_}
        self.chk('a4.no_node_on_both_bounds', not (pa_nodes & pb_nodes), (level, pa_nodes & pb_nodes))
        C['a4.bound_nodes'] += len(pa_nodes) + len(pb_nodes)
        for u in seen:
            labs = set()
            anyold = False
            for tk in pcs[u]:
                if tk[1] and (tk[0] >> 1) not in self.PeS:
                    anyold = True
                    pr = frozenset((tk, pt[tk]))
                    L = self.label.get(pr)
                    self.chk('a4.old_pair_off_P_has_label', L is not None, pr)
                    labs.add(L)
                    self.chk('a4.pair_on_a_bound', pr in PaS or pr in PbS, (pr, L))
                    self.chk('a4.high_label_iff_Pa', (L == 'H') == (pr in PaS), (pr, L))
                    self.chk('a4.low_label_iff_Pb', (L == 'L') == (pr in PbS), (pr, L))
                    C['ctlA4.swapped_labels #chk'] += 1
                    C['ctlA4.swapped_labels #caught'] += (L == 'L') != (pr in PaS) or (L == 'H') != (pr in PbS)
            if anyold:
                self.chk('a4.node_one_label', len(labs) == 1, (u, labs))
                C['a4.nodes_with_old_token'] += 1
            self.chk('a4.node_on_Pa_iff_high', ('H' in labs) == (u in pa_nodes), (u, labs))
            self.chk('a4.node_on_Pb_iff_low', ('L' in labs) == (u in pb_nodes), (u, labs))
            self.chk('a4.bound_nodes_are_old_token_nodes', anyold == (u in pa_nodes or u in pb_nodes), u)
        # P_a, P_b are paths from a 0-piece to a 1-piece (Bound), ends at low / high ends
        C['a4.bounds'] += bool(A['Pa']) + bool(A['Pb'])
        C['a4.both_bounds'] += bool(A['Pa']) and bool(A['Pb'])

    # ---------------------------------------------------------------- A2, A3: one incision
    def check_incision(self, A, Inc, Inc2, newinc, pcs, pof, pt, pcs2, pof2, pt2, nxt):
        I, C = self.I, self.C
        q = A['_q']
        Qe, Qn, x, y, i1, i2 = q['Qe'], q['Qn'], q['x'], q['y'], q['i1'], q['i2']
        j, k, i = A['j'], A['k'], q['i']
        ova, ovb = q['ova'], q['ovb']
        lo_list, hi_list = q['lo'], q['hi']
        newq = q['newq']
        rel = sgn_rel(x, y)
        lenq = 'len1' if len(Qe) == 1 else 'lenN'
        hasold = any(a[1] for a, b in Qe)
        Cedges = [a[0] >> 1 for a, b in Qe] + self.Pe[min(x, y):max(x, y)]
        self.chk('j.edges_distinct', len(set(Cedges)) == len(Cedges), Cedges)
        lov, sep, cover, crossing = self.bond(Cedges)
        self.chk('j.separates_s_t', sep, Cedges)
        self.chk('j.two_components', cover, Cedges)
        self.chk('j.every_edge_crosses', crossing, Cedges)
        if not (sep and cover and crossing):
            if self.opts.get('tolerant'):
                pass
            else:
                raise Abort('J')
        side_tok = lambda tk: self.side_token(lov, tk)
        if I.coords is not None:
            self.geo_J(Qn, Qe, x, y, lov, pcs)
        modes_key = '/'.join(''.join(z) for z in self.modes)
        # A2: new edges, the rule against the oracle
        isnew = [a[1] == 0 for a, b in Qe]
        for pos, (a, b) in enumerate(Qe):
            if a[1] != 0:
                continue
            lft = pos
            while lft > 0 and isnew[lft - 1]:
                lft -= 1
            rgt = pos
            while rgt < len(Qe) - 1 and isnew[rgt + 1]:
                rgt += 1
            touches = lft == 0 or rgt == len(Qe) - 1
            C['a2.chk|new_run_reaches_end=%d' % touches] += 1
            if not touches:
                self.ctx.example('a2.new_run_isolated_from_ends', self, (rel, [(z[0][0], z[0][1]) for z in Qe], pos))
            dl = a[0]
            e = dl >> 1
            tl, hd = I.tail(dl), I.head(dl)
            rule_ok = (tl in lov) and (hd not in lov)
            where = 'only' if len(Qe) == 1 else ('first' if pos == 0 else ('last' if pos == len(Qe) - 1 else 'mid'))
            C['a2.chk'] += 1
            C['a2.chk|' + rel] += 1
            C['a2.chk|' + lenq] += 1
            C['a2.chk|' + rel + '|' + lenq] += 1
            C['a2.chk|pos=' + where] += 1
            C['a2.chk|level=%d' % min(self.level, 6)] += 1
            C['a2.chk|modes=' + modes_key] += 1
            C['a2.chk|ova=%d,ovb=%d' % (ova, ovb)] += 1
            C['a2.chk|Qhasold=%d' % hasold] += 1
            if not rule_ok:
                self.fail('a2.rule', (rel, lenq, where, e, dl))
            # the rule as stored (labels), read on tokens with the oracle (should agree with rule_ok)
            Lw = lo_list[pos]
            H = hi_list[pos]
            self.chk('a2.stored_low_pair_on_low', all(side_tok(tk) == 'L' for tk in Lw), (Lw, rel))
            self.chk('a2.stored_high_pair_on_high', all(side_tok(tk) == 'H' for tk in H), (H, rel))
            # negative controls: rules that must fail
            C['ctlA2.rev_dart #chk'] += 1
            C['ctlA2.rev_dart #caught'] += not ((hd in lov) and (tl not in lov))
            even = dl & ~1
            C['ctlA2.even_dart #chk'] += 1
            C['ctlA2.even_dart #caught'] += not ((I.tail(even) in lov) and (I.head(even) not in lov))
            C['ctlA2.mirror_at_x>y #chk'] += x > y
            C['ctlA2.mirror_at_x>y #caught'] += x > y and rule_ok
        # the proof's two sentences: at g_x the low part ends with (d,1); parity at internal nodes
        tok_new = lambda dd: dd >> 1 in newq
        if Qe and Qe[0][0][1] == 0:
            dl = Qe[0][0][0]
            p = pof2[(dl, 1)]
            self.chk('a2.gx_low_part_ends_with_delta1', pcs2[p][-1] == (dl, 1) and side_tok((dl, 1)) == 'L', (dl,))
        if Qe and Qe[-1][1][1] == 0:
            rd = Qe[-1][1][0]
            p = pof2[(rd, 2)]
            self.chk('a2.gy_low_part_starts_with_rev2', pcs2[p][0] == (rd, 2) and side_tok((rd, 2)) == 'L', (rd,))
        for pos in range(1, len(Qe)):
            inb, outb = Qe[pos - 1][1], Qe[pos][0]  # tokens of the node at level l
            if inb[1] == 0 and outb[1] == 0:
                t1, t2 = (inb[0], 2), (outb[0], 1)
                same = pof2[t1] == pof2[t2]
                C['a2.parity_literal #chk'] += 1
                if not same:
                    C['a2.parity_literal #notsamepiece'] += 1
                    self.ctx.example('a2.parity_literal_not_same_piece', self, (t1, t2, pcs2[pof2[t1]], pcs2[pof2[t2]], rel))
                self.chk('a2.parity_same_side', side_tok(t1) == side_tok(t2), (t1, t2))
            elif inb[1] == 0 or outb[1] == 0:
                C['a2.parity_mixed_new_old'] += 1
                # one new, one old: the old pair lies on one side; the rule still reads the new one
        # Incision Lemma (a), P-pieces, against the oracle
        G = A['G']
        for (t, sg), u in G.items():
            pivot = x if sg == 0 else y
            if t != pivot:
                want = 'L' if t < pivot else 'H'
                # g unchanged unless it holds a new token of Q; it is not a node of Q
                sides = {side_tok(tk2) for tk in pcs[u] for tk2 in ([(tk[0], 1), (tk[0], 2)] if tk[1] == 0 and tk[0] >> 1 in newinc else [tk])}
                self.chk('o.a_P_pieces', sides == {want}, ((t, sg), sides, want, x, y))
        # A^Q
        tokA = [tk for u in A['seen'] for tk in pcs[u]]
        kids = []
        other_new = newinc - set(newq)
        for tk in tokA:
            if tk[1] == 0 and tk[0] >> 1 in newinc:
                self.chk('o.other_annulus_cuts_only_its_own', tk[0] >> 1 in newq, tk)
                kids += [(tk[0], 1), (tk[0], 2)]
            else:
                kids.append(tk)
        pieces2 = {pof2[tk] for tk in kids}
        comp = {}
        comps = []
        for u0 in pieces2:
            if u0 in comp:
                continue
            cid = len(comps)
            comps.append([u0])
            comp[u0] = cid
            st = [u0]
            while st:
                u = st.pop()
                for tk in pcs2[u]:
                    v = pof2[pt2[tk]]
                    self.chk('o.AQ_closed_under_pairs', v in pieces2, tk)
                    if v not in comp:
                        comp[v] = cid
                        comps[cid].append(v)
                        st.append(v)
        # sides of the components by the oracle
        cside = []
        for cid, ps in enumerate(comps):
            ss = {side_tok(tk) for u in ps for tk in pcs2[u]}
            self.chk('a3.component_on_one_side', len(ss) == 1, (cid, ss))
            cside.append(next(iter(ss)))
        for ps in comps:
            for u in ps:
                ss = {side_tok(tk) for tk in pcs2[u]}
                if len(ss) != 1:
                    self.fail('a3.piece_on_one_side', (u, pcs2[u]))
        call = {'L': (not ova) and j <= i1, 'H': (not ovb) and i2 <= k}
        on_side = {'L': [c for c in range(len(comps)) if cside[c] == 'L'], 'H': [c for c in range(len(comps)) if cside[c] == 'H']}
        C['a3.incisions'] += 1
        C['a3.components'] += len(comps)
        C['a3.components=%d' % min(len(comps), 5)] += 1
        C['a3.low_comps>1'] += len(on_side['L']) > 1
        C['a3.high_comps>1'] += len(on_side['H']) > 1
        # copies of new edges by component
        holds = [{'L': 0, 'H': 0} for _ in comps]
        for pos, (a, b) in enumerate(Qe):
            if a[1] != 0:
                continue
            for lab, pr in (('L', lo_list[pos]), ('H', hi_list[pos])):
                tks = list(pr)
                c0, c1 = comp[pof2[tks[0]]], comp[pof2[tks[1]]]
                self.chk('a3.copy_in_one_component', c0 == c1, pr)
                holds[c0][lab] += 1
        for c in range(len(comps)):
            self.chk('a3.no_component_holds_copies_of_both_sides', not (holds[c]['L'] and holds[c]['H']), holds[c])
            if not holds[c]['L'] and not holds[c]['H']:
                C['a3.components_without_new_copy'] += 1
                C['a3.components_without_new_copy|%s' % cside[c]] += 1
                C['a3.components_without_new_copy|side_called=%d' % call[cside[c]]] += 1
                if newq:
                    C['a3.no_copy_though_Q_has_new'] += 1
                    # by the rule it is not a child; it must not lie on a called side
                    self.chk('a3.no_new_copy_means_not_on_called_side', not call[cside[c]], (cside[c], call))
                    C['a3.no_copy_on_uncalled_side'] += not call[cside[c]]
        child = {}
        for sd in ('L', 'H'):
            if call[sd]:
                ok = len(on_side[sd]) == 1
                self.chk('a3.called_side_is_one_subgraph', ok, (sd, on_side[sd], rel, lenq))
                if ok:
                    child[sd] = on_side[sd][0]
                    ch_tok = [tk for u in comps[on_side[sd][0]] for tk in pcs2[u]]
                    cnt = collections.Counter(tk[0] >> 1 for tk in ch_tok)
                    for a, b in Qe:
                        e = a[0] >> 1
                        self.chk('a3.called_side_holds_one_copy_of_each_edge_of_Q', cnt[e] == 2, (sd, e, cnt[e]))
                    # bad edges
                    self.bad_edges(A, q, sd, comps[on_side[sd][0]], pcs2, pof2, pof, pt)
        # the rule: a component is the called child of a side iff it holds a copy of a new edge of Q of that side
        if newq:
            for c in range(len(comps)):
                for sd in ('L', 'H'):
                    truth = call[sd] and child.get(sd) == c
                    pred = call[sd] and holds[c][sd] > 0
                    C['a3.rule #chk'] += 1
                    C['a3.rule #chk|truth=%d' % truth] += 1
                    if truth != pred:
                        self.fail('a3.rule', (c, sd, truth, pred, holds[c], call, cside[c]))
                    # control: the sides of the stored copies swapped
                    predsw = call[sd] and holds[c]['H' if sd == 'L' else 'L'] > 0
                    C['ctlA3.swapped_sides #chk'] += call[sd]
                    C['ctlA3.swapped_sides #caught'] += call[sd] and truth != predsw
            C['a3.with_new_edge'] += 1
        else:
            # Q has no new edge: nothing is cut, one component, on the side given by part (a)
            C['a3.no_new_edge'] += 1
            self.chk('a3.no_new_edge_one_component', len(comps) == 1, len(comps))
            self.chk('a3.no_new_edge_same_tokens', set(kids) == set(tokA), None)
            f_pr, l_pr = frozenset(Qe[0]), frozenset(Qe[-1])
            PaS, PbS = set(A['Pa']), set(A['Pb'])
            self.chk('o.old_end_on_a_bound', (f_pr in PaS or f_pr in PbS) and (l_pr in PaS or l_pr in PbS), None)
            given_f = 'H' if f_pr in PaS else 'L'
            given_l = 'H' if l_pr in PaS else 'L'
            self.chk('a3.no_new_edge_ends_agree', given_f == given_l, (given_f, given_l))
            Qset = {frozenset(z) for z in Qe}
            self.chk('a3.no_new_edge_Q_is_a_whole_bound', Qset == PaS or Qset == PbS, None)
            C['a3.no_new_edge_given=' + given_f] += 1
            if len(comps) == 1:
                self.chk('a3.no_new_edge_side_is_part_a', cside[0] == given_f, (cside[0], given_f, x, y, rel))
                other = 'L' if given_f == 'H' else 'H'
                self.chk('a3.no_new_edge_other_side_not_called', not call[other], (other, call))
                C['a3.no_new_edge_called=%d' % call[given_f]] += 1
                for sd in ('L', 'H'):
                    truth = call[sd] and child.get(sd) == 0
                    pred = call[sd] and sd == given_f
                    C['a3.rule_no_new #chk'] += 1
                    if truth != pred:
                        self.fail('a3.rule_no_new', (sd, truth, pred))
        # ends of Q against part (a) and Claim Oends
        if Qe[0][0][1] != 0:
            pr = frozenset(Qe[0])
            sd = 'H' if pr in set(A['Pa']) else 'L'
            sides = {side_tok(tk) for tk in pcs[Qn[0]]}
            self.chk('o.old_end_x_side', sides == {sd}, (sd, sides))
            C['o.old_end_x'] += 1
        if Qe[-1][1][1] != 0:
            pr = frozenset(Qe[-1])
            sd = 'H' if pr in set(A['Pa']) else 'L'
            sides = {side_tok(tk) for tk in pcs[Qn[-1]]}
            self.chk('o.old_end_y_side', sides == {sd}, (sd, sides))
            C['o.old_end_y'] += 1
        # the children, by the paper's rule (the copies stored with the first edge)
        if call['L']:
            pl = len(lo_list)
            r = sorted(lo_list[0])[0]
            cch = dict(root=r, j=j, k=i1, Pa=A['Pa'], Pb=lo_list, parent_len=k - j)
            if 'L' in child:
                self.chk('a3.rule_root_in_truth_child', comp[pof2[r]] == child['L'], None)
            nxt.append(cch)
        if call['H']:
            r = sorted(hi_list[0])[0]
            cch = dict(root=r, j=i2, k=k, Pa=hi_list, Pb=A['Pb'], parent_len=k - j)
            if 'H' in child:
                self.chk('a3.rule_root_in_truth_child', comp[pof2[r]] == child['H'], None)
            nxt.append(cch)
        # statistics
        inner_linear = sum(1 for u in Qn[1:-1] if any(tk[1] for tk in pcs[u]))
        C['q.inner_linear_nodes'] += inner_linear
        C['q.with_inner_linear'] += inner_linear > 0
        for u in Qn[1:-1]:
            nparts = len({pof2[tk2] for tk in pcs[u] for tk2 in ([(tk[0], 1), (tk[0], 2)] if tk[1] == 0 and tk[0] >> 1 in newinc else [tk])})
            C['q.inner_node_parts=%d' % nparts] += 1
        C['q.rel.' + rel] += 1
        C['q.' + lenq] += 1
        C['q.hasold'] += hasold
        C['q.ov_a'] += ova
        C['q.ov_b'] += ovb
        C['q.call_L'] += call['L']
        C['q.call_H'] += call['H']
        C['q.empty_range_L'] += (not ova) and j > i1
        C['q.empty_range_H'] += (not ovb) and i2 > k

    def bad_edges(self, A, q, sd, comp_pieces, pcs2, pof2, pof, pt):
        """Part (b): a called side has no bad edge: an edge of P_a or P_b not on P_i with an end on
        P_i n P_a or P_i n P_b."""
        nodes = set(q['nodes'])
        es = {frozenset(z) for z in q['es']}
        comp_tok = {tk for u in comp_pieces for tk in pcs2[u]}
        for nm, B in (('a', A['Pa']), ('b', A['Pb'])):
            bset = {pof[tk] for pr in B for tk in pr}
            meet = nodes & bset
            if not meet:
                continue
            for pr in B:
                if pr in es:
                    continue
                if {pof[tk] for tk in pr} & meet:
                    # bad edge; the called side must not hold it
                    self.chk('o.called_side_has_no_bad_edge', not (set(pr) <= comp_tok), (nm, pr))

    # ---------------------------------------------------------------- C
    def c_stats(self, src, tgt, nodes, es, pcs, pt, pof):
        I, C = self.I, self.C
        C['c.tree.pi'] += 1
        base = self.derive(nodes, es, pcs)
        for seed in (1, 2, 3):
            p0 = tree_path(pcs, pt, pof, src, tgt, I.W, seed)
            p1 = rev_path(*tree_path(pcs, pt, pof, tgt, src, I.W, seed))
            C['c.tree.pairs'] += 1
            d0, d1 = self.derive(*p0, pcs), self.derive(*p1, pcs)
            if p0 != p1:
                C['c.tree.path_differs'] += 1
                self.ctx.example('c.tree.path_differs', self, (p0[1], p1[1]))
            if (d0['x'], d0['y'], d0['i1'], d0['i2']) != (d1['x'], d1['y'], d1['i1'], d1['i2']):
                C['c.tree.xyi_differs'] += 1
                self.ctx.example('c.tree.xyi_differs', self, (d0, d1))
            if d0['Q'] != d1['Q']:
                C['c.tree.Q_differs'] += 1
                self.ctx.example('c.tree.Q_differs', self, (d0, d1))
        # the literal definition of x and y applied to the path read from g^1: last 0-piece is the last node
        rn, re_ = rev_path(nodes, es)
        rl = [self.anc(pcs[u][0]) for u in rn]
        C['c.literal_on_reversed.chk'] += 1
        C['c.literal_on_reversed.y_undefined'] += max(q for q, a in enumerate(rl) if a and a[1] == 0) == len(rl) - 1
        dag = Dag(pcs, pt, pof, src, tgt, I.W)
        paths = dag.enum(64)
        C['c.dag.pi'] += 1
        C['c.dag.tied'] += dag.count > 1
        vals = {(d['x'], d['y'], d['i1'], d['i2']) for d in (self.derive(*p, pcs) for p in paths)}
        Qs = {self.derive(*p, pcs)['Q'] for p in paths}
        C['c.dag.distinct_xyi>1'] += len(vals) > 1
        C['c.dag.distinct_Q>1'] += len(Qs) > 1
        for p in paths:
            r = self.derive(*p, pcs)
            w = self.derive(*p, pcs, wrong=True)
            C['c.path.chk'] += 1
            C['c.path.alt>1'] += r['alt'] > 1
            if r['Q'] != w['Q'] or (r['x'], r['y']) != (w['x'], w['y']):
                C['c.path.wrong_reading_differs'] += 1
                self.ctx.example('c.path.wrong_reading_differs', self, (r, w))

    # ---------------------------------------------------------------- final value (claim B)
    def final(self, maxlev):
        I, C = self.I, self.C
        ctx = self.ctx
        C['runs'] += 1
        C['runs|m=%d' % min(self.m, 40)] += 1
        C['d.levels|%d' % maxlev] += 1
        if self.m >= 1:
            bound = 1 + math.ceil(math.log2(self.m))
        else:
            bound = 1
        self.chk('d.levels_le_1_plus_ceil_log2_m', maxlev <= bound, (maxlev, self.m))
        cur = ctx.levels_by_m.get(self.m, 0)
        ctx.levels_by_m[self.m] = max(cur, maxlev)
        C['d.levels_gt_log2(m+1)+1'] += maxlev > math.log2(self.m + 1) + 1
        ws = self.walks
        self.chk('b.some_walk', bool(ws), None)
        if not ws:
            return
        Lam = min(w['w'] for w in ws)
        lam_true = min(self.lam.values())
        self.chk('b.least_w_is_Lambda', Lam == lam_true, (Lam, lam_true))
        self.chk('b.floor_Lambda_K_is_mincut_cprime', Lam // I.K == I.mcp, (Lam // I.K, I.mcp))
        self.chk('b.least_cprime_is_mincut_cprime', min(w['cp'] for w in ws) == I.mcp, None)
        self.chk('b.value_c', I.mcp // (I.N * I.N) == I.mc, (I.mcp, I.N, I.mc))
        # winners: all walks of least w
        winners = [w for w in ws if w['w'] == Lam]
        C['b.winner.runs'] += 1
        C['b.winner.walks'] += len(winners)
        for w in winners:
            self.chk('b.winner_bond', w['ok'], w)
            self.chk('b.winner_C_is_mincut', w['cC'] == I.mcp, (w['cC'], I.mcp))
            self.chk('b.winner_cut_value_c', w['cut_c'] == I.mc, (w['cut_c'], I.mc))
            C['b.winner.' + sgn_rel(w['x'], w['y'])] += 1
            C['b.winner.overlap'] += w['overlap']
            C['b.winner.loop'] += w['loop']
        for w in ws:
            if w['cp'] == I.mcp:
                C['b.min_cp_walks'] += 1
                self.chk('b.min_cp_walk_is_mincut', w['ok'] and w['cC'] == I.mcp and w['cut_c'] == I.mc, w)
        # the rule of the paper: least t, first computed
        w0 = min(winners, key=lambda w: (w['t'], w['seq']))
        C['b.rule_winner.' + sgn_rel(w0['x'], w0['y'])] += 1
        C['b.rule_winner.overlap'] += w0['overlap']
        C['b.rule_winner.loop'] += w0['loop']
        C['b.rule_winner.tag=' + w0['tag']] += 1
        self.C['b.rule_winner #chk'] += 1
        # repair needed?
        if all(w['tag'] == 'end' for w in winners):
            C['stat.only_repair_paths_reach_Lambda'] += 1
