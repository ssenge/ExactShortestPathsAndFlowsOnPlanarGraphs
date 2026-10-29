"""Planar rotation systems (loopless multigraphs) written for the Lemma R attack.

Conventions follow GHAT_REPAIR.md, Conventions (re-derived here, nothing imported):
  dart 2e = ends[e][0] -> ends[e][1], dart 2e+1 the reverse; rev d = d ^ 1.
  r_v(i) = rot[v][i]; corner (v,i) lies between r_v(i) and r_v(i+1).
  in((v,i)) = rev r_v(i), out((v,i)) = r_v(i+1).
  tau(d) = (tail d, pos(d)-1), eta(d) = (head d, pos(rev d)).
  face walk: d is followed by out(eta(d)).
"""
import itertools, random


class Emb:
    __slots__ = ('n', 'ends', 'm', 'rot', 'tl', 'pos', 'face_of', 'faces', 'fidx', 'cap')

    def __init__(self, n, ends, rot, cap=None):
        self.n = n
        self.ends = [tuple(e) for e in ends]
        self.m = len(self.ends)
        self.rot = [list(r) for r in rot]
        self.tl = [0] * (2 * self.m)
        for e, (u, v) in enumerate(self.ends):
            assert u != v, "loop"
            self.tl[2 * e] = u
            self.tl[2 * e + 1] = v
        self.pos = [None] * (2 * self.m)
        for v in range(n):
            for i, d in enumerate(self.rot[v]):
                assert self.tl[d] == v
                assert self.pos[d] is None
                self.pos[d] = i
        assert all(p is not None for p in self.pos)
        self.face_of = [-1] * (2 * self.m)
        self.fidx = [-1] * (2 * self.m)
        self.faces = []
        for d0 in range(2 * self.m):
            if self.face_of[d0] >= 0:
                continue
            f = len(self.faces)
            cyc = []
            d = d0
            while self.face_of[d] < 0:
                self.face_of[d] = f
                self.fidx[d] = len(cyc)
                cyc.append(d)
                d = self.fnext(d)
            assert d == d0
            self.faces.append(cyc)
        self.cap = list(cap) if cap is not None else [1] * self.m

    # basic
    def head(self, d):
        return self.tl[d ^ 1]

    def deg(self, v):
        return len(self.rot[v])

    def r(self, v, i):
        return self.rot[v][i % len(self.rot[v])]

    def din(self, c):
        v, i = c
        return self.r(v, i) ^ 1

    def dout(self, c):
        v, i = c
        return self.r(v, i + 1)

    def tau(self, d):
        u = self.tl[d]
        return (u, (self.pos[d] - 1) % len(self.rot[u]))

    def eta(self, d):
        v = self.tl[d ^ 1]
        return (v, self.pos[d ^ 1])

    def fnext(self, d):
        return self.dout(self.eta(d))

    def corner_face(self, c):
        return self.face_of[self.din(c)]

    def corners(self, v):
        return [(v, i) for i in range(len(self.rot[v]))]

    def genus_ok(self):
        return self.n - self.m + len(self.faces) == 2

    def connected(self):
        par = list(range(self.n))

        def f(x):
            while par[x] != x:
                par[x] = par[par[x]]
                x = par[x]
            return x
        for u, v in self.ends:
            par[f(u)] = f(v)
        return len({f(x) for x in range(self.n)}) == 1

    def with_cap(self, cap):
        return Emb(self.n, self.ends, self.rot, cap)


# ---------------------------------------------------------------- canonical form of a map
def canon(n, ends, rot):
    """orientation-preserving canonical code of a connected map."""
    m = len(ends)
    if m == 0:
        return (n,)
    pos = {}
    for v in range(n):
        for i, d in enumerate(rot[v]):
            pos[d] = (v, i)

    def sig(d):
        v, i = pos[d]
        r = rot[v]
        return r[(i + 1) % len(r)]
    best = None
    for root in range(2 * m):
        lab = {root: 0}
        order = [root]
        k = 0
        code = []
        while k < len(order):
            d = order[k]
            k += 1
            for x in (sig(d), d ^ 1):
                if x not in lab:
                    lab[x] = len(order)
                    order.append(x)
            code.append((lab[sig(d)], lab[d ^ 1]))
        code = tuple(code)
        if best is None or code < best:
            best = code
    return best


def relabel_from_code(code):
    """rebuild (n, ends, rot) from a canonical code (darts = labels)."""
    D = len(code)
    sig = [c[0] for c in code]
    alp = [c[1] for c in code]
    # vertices = cycles of sig
    vert = [-1] * D
    rot = []
    for d in range(D):
        if vert[d] >= 0:
            continue
        v = len(rot)
        cyc = []
        x = d
        while vert[x] < 0:
            vert[x] = v
            cyc.append(x)
            x = sig[x]
        rot.append(cyc)
    # edges: pair darts d < alp[d]
    eid = {}
    ends = []
    for d in range(D):
        a = alp[d]
        if d < a:
            eid[d] = 2 * len(ends)
            eid[a] = 2 * len(ends) + 1
            ends.append((vert[d], vert[a]))
    rot2 = [[eid[d] for d in cyc] for cyc in rot]
    return len(rot), ends, rot2


def extensions(n, ends, rot, nmax):
    """all one-edge extensions: pendant at a corner, or chord between two corners of one face."""
    E = Emb(n, ends, rot)
    out = []
    if n < nmax:
        for v in range(n):
            for i in range(len(rot[v]) if rot[v] else 1):
                e = len(ends)
                ends2 = list(ends) + [(v, n)]
                rot2 = [list(r) for r in rot] + [[2 * e + 1]]
                rot2[v].insert(i + 1 if rot[v] else 0, 2 * e)
                out.append((n + 1, ends2, rot2))
    # chords
    for f, cyc in enumerate(E.faces):
        cs = [E.eta(d) for d in cyc]   # corners of the face, in walk order
        for a in range(len(cs)):
            for b in range(a + 1, len(cs)):
                (u, i), (v, j) = cs[a], cs[b]
                if u == v:
                    continue
                e = len(ends)
                ends2 = list(ends) + [(u, v)]
                rot2 = [list(r) for r in rot]
                rot2[u].insert(i + 1, 2 * e)
                # index j at v unaffected unless u == v (excluded)
                rot2[v].insert(j + 1, 2 * e + 1)
                out.append((n, ends2, rot2))
    return out


def enumerate_maps(nmax, mmax, verbose=False):
    """all connected loopless planar maps with 2 <= n <= nmax, 1 <= m <= mmax, up to
    orientation-preserving isomorphism. Returns dict m -> list of (n, ends, rot)."""
    start = (2, [(0, 1)], [[0], [1]])
    seen = {canon(*start)}
    levels = {1: [start]}
    for m in range(2, mmax + 1):
        cur = []
        for M in levels[m - 1]:
            for X in extensions(*M, nmax):
                c = canon(*X)
                if c in seen:
                    continue
                seen.add(c)
                Y = relabel_from_code(c)
                Em = Emb(*Y)
                assert Em.genus_ok()
                cur.append(Y)
        levels[m] = cur
        if verbose:
            print('m', m, len(cur), flush=True)
    return levels


# ---------------------------------------------------------------- random planar maps (bigger instances)
def random_map(rng, n_target, extra_frac=0.6, par_prob=0.1, nmax=None):
    """random connected loopless planar multigraph: random tree + chords in faces, with
    occasional parallel edges and pendants."""
    n = 2
    ends = [(0, 1)]
    rot = [[0], [1]]
    while n < n_target:
        v = rng.randrange(n)
        i = rng.randrange(len(rot[v]))
        e = len(ends)
        ends.append((v, n))
        rot[v].insert(i + 1, 2 * e)
        rot.append([2 * e + 1])
        n += 1
    nchord = int(extra_frac * 2 * n)
    for _ in range(nchord):
        E = Emb(n, ends, rot)
        if rng.random() < par_prob:
            e0 = rng.randrange(len(ends))
            u, v = ends[e0]
            e = len(ends)
            ends.append((u, v))
            # parallel: insert next to dart 2e0 at u and before 2e0+1 at v (2-gon face)
            rot[u].insert(rot[u].index(2 * e0) + 1, 2 * e)
            rot[v].insert(rot[v].index(2 * e0 + 1), 2 * e + 1)
            continue
        f = rng.randrange(len(E.faces))
        cyc = E.faces[f]
        cs = [E.eta(d) for d in cyc]
        pairs = [(a, b) for a in range(len(cs)) for b in range(a + 1, len(cs)) if cs[a][0] != cs[b][0]]
        if not pairs:
            continue
        a, b = rng.choice(pairs)
        (u, i), (v, j) = cs[a], cs[b]
        e = len(ends)
        ends.append((u, v))
        rot[u].insert(i + 1, 2 * e)
        rot[v].insert(j + 1, 2 * e + 1)
    E = Emb(n, ends, rot)
    assert E.genus_ok()
    return E


def grid_map(rng, w, h, drop=0.2):
    n = w * h
    ends = []
    idx = lambda x, y: y * w + x
    adj = {v: {} for v in range(n)}  # v -> {direction: dart}
    for y in range(h):
        for x in range(w):
            if x + 1 < w:
                e = len(ends)
                ends.append((idx(x, y), idx(x + 1, y)))
                adj[idx(x, y)][0] = 2 * e
                adj[idx(x + 1, y)][2] = 2 * e + 1
            if y + 1 < h:
                e = len(ends)
                ends.append((idx(x, y), idx(x, y + 1)))
                adj[idx(x, y)][1] = 2 * e
                adj[idx(x, y + 1)][3] = 2 * e + 1
    rot = [[adj[v][k] for k in sorted(adj[v])] for v in range(n)]
    E = Emb(n, ends, rot)
    # drop some edges keeping connectivity
    order = list(range(len(ends)))
    rng.shuffle(order)
    keep = set(range(len(ends)))
    for e in order[:int(drop * len(ends))]:
        k2 = keep - {e}
        ends2 = [ends[x] for x in sorted(k2)]
        par = list(range(n))

        def f(x):
            while par[x] != x:
                par[x] = par[par[x]]
                x = par[x]
            return x
        for u, v in ends2:
            par[f(u)] = f(v)
        if len({f(x) for x in range(n)}) == 1:
            keep = k2
    kl = sorted(keep)
    nid = {e: i for i, e in enumerate(kl)}
    ends2 = [ends[e] for e in kl]
    rot2 = [[2 * nid[d >> 1] + (d & 1) for d in r if (d >> 1) in keep] for r in rot]
    E2 = Emb(n, ends2, rot2)
    assert E2.genus_ok()
    return E2


if __name__ == '__main__':
    import sys, time
    t0 = time.time()
    L = enumerate_maps(int(sys.argv[1]), int(sys.argv[2]), verbose=True)
    print({m: len(v) for m, v in L.items()}, round(time.time() - t0, 1))
