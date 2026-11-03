"""Checks of notes/DIAMETER.md on the region bags of notes/LEMMA15.md, Section 9.
python3 -I diam.py SEED SECS [big]   main lane
python3 -I diam.py ctl SEED SECS     negative controls
python3 -I diam.py scale             tokens against D^2 on grids
python3 -I diam.py sum SEED SECS     sums of distances, with controls
python3 -I diam.py second            an instance that needs the second token
"""
import collections, json, os, random, sys, time
HERE = os.path.dirname(os.path.abspath(__file__))
for d in ('lemma14prime', 's9'):
    sys.path.insert(0, os.path.join(HERE, '..', d))
import numpy as np
from scipy.sparse import coo_matrix
from scipy.sparse.csgraph import connected_components, shortest_path
from core import PG, Fail
from engine_r import Engine, TAU
from geo import FAMS, virtual_candidates, drawing_ok
from sweep import params


class Bags(Engine):
    """Engine.run without the emulator construction: only the bag tree of Lemma B1."""
    def run(self):
        g = self.g
        cur = dict(gverts=frozenset(), label=np.full(g.m, -1))
        level = [0]; d = 0
        while level and d < self.cfg['maxdepth']:
            nxt = []
            for b in level:
                B = self.bags[b]
                if len(B['X']) <= self.cfg['leaf']:
                    B['kids'] = []; continue
                res = self.choose_and_split(b, cur)
                if res is None:
                    B['kids'] = []; self.st['forced_leaf'] += 1; continue
                B.update(S=res['S'], q=res['q'], real=res['real'], TX=res['TX'], W=res['W'])
                B['kids'] = []
                for i, Y in enumerate(res['kids']):
                    zc = {w: B['z'][w] for w in Y if w in B['z'] and w not in res['S']}
                    for s in res['S'] & Y:
                        os_, oe = res['W'][s]
                        zc[s] = os_ + ((oe - os_) % TAU) / 2 if res['kinds'][i] == 'in' else oe + ((os_ - oe) % TAU) / 2
                    nb = len(self.bags)
                    self.bags[nb] = dict(X=Y, parent=b, depth=d + 1, z=zc, kids=None, kind=res['kinds'][i], E=res['kidsE'][i])
                    B['kids'].append(nb); nxt.append(nb)
            level = nxt; d += 1
        return self.st


class Table:
    """P_X, its faces, W_Phi and t'' for one bag."""
    def __init__(self, eng, b, par, st, noanc=False, nolink=False):
        g = eng.g; B = eng.bags[b]; self.b = b; self.X = X = B['X']
        chain = [b] if noanc else [b] + eng.anc(b)
        Pe = set()
        for a in chain:
            q = eng.bags[a]['q']
            for u, w in zip(q, q[1:]):
                Pe.add((u, w) if u < w else (w, u))
            if not nolink:
                x = q[0]
                while par[x] is not None:
                    y = par[x]; Pe.add((x, y) if x < y else (y, x)); x = y
        self.Pe = Pe
        Padj = collections.defaultdict(set)
        for u, w in Pe:
            Padj[u].add(w); Padj[w].add(u)
        self.VP = VP = set(Padj)
        Prot = {x: [u for u in g.rot[x] if u in Padj[x]] for x in VP}
        # darts (a,b) stand for the corner at b right after a in the rotation
        occ = {}; self.walks = []; self.xo = []; self.fo = []
        for x in VP:
            for a in Prot[x]:
                if (a, x) in occ:
                    continue
                walk = []; a0, b0 = a, x; u, v = a, x
                while True:
                    occ[(u, v)] = len(self.xo); walk.append(len(self.xo)); self.xo.append(v); self.fo.append(len(self.walks))
                    r = Prot[v]; w = r[(r.index(u) + 1) % len(r)]
                    u, v = v, w
                    if (u, v) == (a0, b0):
                        break
                self.walks.append(walk)
        self.xo = np.array(self.xo); self.fo = np.array(self.fo); self.occ = occ
        if not nolink:
            assert len(VP) - len(Pe) + len(self.walks) == 2, 'Euler'
            st['chk.euler'] += 1
        corner = {}
        for x in VP:
            r = g.rot[x]; j0 = next(i for i, u in enumerate(r) if u in Padj[x])
            cur = r[j0]
            for i in range(1, len(r) + 1):
                u = r[(j0 + i) % len(r)]
                if u in Padj[x]:
                    cur = u
                else:
                    corner[(x, u)] = occ[(cur, x)]
        no = len(self.xo)
        self.vid = {}
        for v in X:
            if v not in VP:
                self.vid[v] = no + len(self.vid)
        N = no + len(self.vid)
        def node(a, c):
            return corner[(a, c)] if a in VP else self.vid[a]
        ring = []; inner = []
        for walk in self.walks:
            for i, o in enumerate(walk):
                ring.append((o, walk[(i + 1) % len(walk)]))
        for e in B['E']:
            a, c = g.ends[e]
            if (a, c) in Pe:
                continue
            inner.append((node(a, c), node(c, a)))
        self.N = N; self.no = no; self.ring = ring; self.inner = inner
        self.mat = mk(ring + inner, N)
        nc, lab = connected_components(self.mat, directed=False)
        # planarity: a component holds the occurrences of one face only
        seen = {}
        for o in range(no):
            f = seen.setdefault(lab[o], self.fo[o])
            if f != self.fo[o]:
                st['FAIL.corners_in_two_faces'] += 1
        st['chk.corners_in_one_face'] += 1
        self.t = shortest_path(self.mat, unweighted=True, indices=np.arange(no)) if no else np.zeros((0, N))
        self.face = {}
        for v, i in self.vid.items():
            if lab[i] in seen:
                self.face[v] = seen[lab[i]]
            else:
                st['FAIL.no_hub_reached'] += 1
        self.inX = np.array([x in X for x in self.xo], bool)
        self.child = {}
        for k in B['kids']:
            for v in eng.bags[k]['X']:
                if v in self.vid:
                    if v in self.child:
                        st['FAIL.two_children'] += 1
                    self.child[v] = k

    def vec(self, v):
        return self.t[self.walks[self.face[v]], self.vid[v]]


def mk(edges, N):
    if not edges:
        return coo_matrix((N, N)).tocsr()
    a = np.array(edges)
    return coo_matrix((np.ones(2 * len(a)), (np.r_[a[:, 0], a[:, 1]], np.r_[a[:, 1], a[:, 0]])), shape=(N, N)).tocsr()


def doubled(vec):
    n = len(vec); out = []
    for i in range(n):
        a, c = vec[i], vec[(i + 1) % n]
        m = 2 * min(a, c) + 1
        out += [m - 2 * a, 2 * c - m]
    return out


def changes(A, B):
    s = [1 if x > y else -1 for x, y in zip(A, B) if x != y]
    return sum(s[i] != s[i - 1] for i in range(len(s))) if s else 0


def segments(l, r):
    """nodes of the segment tree on positions l..r"""
    yield (l, r)
    if r - l >= 2:
        m = (l + r) // 2
        yield from segments(l, m)
        yield from segments(m, r)


def check_bag(eng, b, par, dG, st, rng, tokens):
    """Sections 2, 3, 4 at one bag. tokens[b] = (Table, per face: pattern -> list of (offset, child))."""
    B = eng.bags[b]; T = Table(eng, b, par, st); X = B['X']
    D = int(dG.max()); g = eng.g
    st['bags'] += 1
    K = [len(w) for w in T.walks]; E = len(T.Pe)
    assert sum(K) == 2 * E
    st['max.E_over_D_x100'] = max(st['max.E_over_D_x100'], int(100 * E / max(D, 1)))
    # sandwich and first hit
    pats = [collections.defaultdict(list) for _ in T.walks]
    us = [v for v in T.vid if v in T.face]
    for v in us:
        f = T.face[v]; vec = T.vec(v); xs = T.xo[T.walks[f]]
        st['chk.sandwich'] += 1
        if (vec < dG[v, xs]).any():
            st['FAIL.sandwich'] += 1
        mask = T.inX[T.walks[f]]
        if not mask.any() or vec[mask].min() > D:
            st['FAIL.near_hub'] += 1
        off = int(vec[0]); pat = tuple((vec - off).astype(int))
        pats[f][pat].append((off, T.child.get(v, -1), v))
    words = 0; ntok = 0
    for f, walk in enumerate(T.walks):
        k = K[f]
        if k >= 2:
            st['chk.theorem1'] += 1
            if len(pats[f]) > 2 * k * k - 2 * k + 2:
                st['FAIL.theorem1'] += 1
            if k >= 8:
                st['max.pat_over_K2_x100'] = max(st['max.pat_over_K2_x100'], int(100 * len(pats[f]) / (k * k)))
        table = {}
        for pat, lst in pats[f].items():
            lst.sort(key=lambda z: -z[0]); top = []
            for z in lst:
                if not top or z[1] != top[0][1]:
                    top.append(z)
                    if len(top) == 2:
                        break
            table[pat] = top; ntok += len(top)
        pats[f] = table
        # interval lemma and dictionary
        P = np.array(list(table), int) if table else np.zeros((0, k), int)
        if k >= 2 and len(P):
            for l, r in segments(0, k - 1):
                cnt = len({tuple(row) for row in (P[:, l + 1:r + 1] - P[:, l:r])}) if r > l else 1
                words += cnt
                st['chk.interval'] += 1
                if cnt > (2 * (r - l)) ** 2 + 1:
                    st['FAIL.interval'] += 1
            # forbidden configuration, on a sample of pairs
            idx = list(range(len(P)))
            for _ in range(min(40, len(P) * len(P))):
                i, j = rng.choice(idx), rng.choice(idx)
                if i != j:
                    st['chk.alternation'] += 1
                    if changes(doubled(list(P[i])), doubled(list(P[j]))) > 2:
                        st['FAIL.alternation'] += 1
    st['chk.tokens'] += 1
    bound = (2 * E) ** 2
    st['max.tokens_over_4E2_x100'] = max(st['max.tokens_over_4E2_x100'], int(100 * ntok / max(bound, 1)))
    st['max.dict_over_4E2_x100'] = max(st['max.dict_over_4E2_x100'], int(100 * words / max(bound, 1)))
    # first-hit form: what the vertices compute
    if T.no and T.no <= 200 and rng.random() < 0.3:
        first_hit(T, us, D, st, rng)
    # recursive table of Section 4
    if B['parent'] is not None:
        tab_check(eng, b, T, dG, st, rng)
    tokens[b] = (T, pats)


def first_hit(T, us, D, st, rng):
    """Step 3: depth limited search in W' (no cycle edges), then the metric on the occurrences."""
    no = T.no
    ft = shortest_path(mk(T.inner, T.N), unweighted=True, indices=np.arange(no))
    hub = np.full((no, no), np.inf); np.fill_diagonal(hub, 0)
    Kmax = max(len(w) for w in T.walks)
    depth = D + Kmax
    ft[ft > depth] = np.inf
    for a, c in T.ring:
        hub[a, c] = hub[c, a] = 1
    hub = np.minimum(hub, ft[:, :no])
    for k in range(no):
        hub = np.minimum(hub, hub[:, k:k + 1] + hub[k:k + 1, :])
    for v in rng.sample(us, min(20, len(us))):
        i = T.vid[v]; w = T.walks[T.face[v]]
        val = (ft[:, i][:, None] + hub).min(0)
        st['chk.first_hit'] += 1
        if not (val[w] == T.t[w, i]).all():
            st['FAIL.first_hit'] += 1


def tab_check(eng, b, T, dG, st, rng):
    """d_G on P_X within X from the parent's labels and a BFS in R_X of depth D."""
    g = eng.g; B = eng.bags[b]; A = eng.bags[B['parent']]; X = B['X']
    PA = [p for p in eng.tb[B['parent']].VP if p in A['X']]
    new = sorted(T.VP & X)
    Xl = sorted(X); ix = {v: i for i, v in enumerate(Xl)}
    M = mk([(ix[g.ends[e][0]], ix[g.ends[e][1]]) for e in B['E']], len(Xl))
    dX = shortest_path(M, unweighted=True, indices=[ix[q] for q in new]) if new else None
    D = dG.max()
    for j in rng.sample(range(len(new)), min(25, len(new))):
        q = new[j]
        for v in rng.sample(Xl, min(25, len(Xl))):
            st['chk.table'] += 1
            ins = dX[j, ix[v]] if dX[j, ix[v]] <= D else np.inf
            val = min(ins, (dG[v, PA] + dG[PA, q]).min()) if PA else ins
            if val != dG[v, q]:
                st['FAIL.table'] += 1


def ecc_all(eng, dG, tokens, st, mode, rng):
    """Section 5: eccentricities from labels, hub maxima and tokens only."""
    g = eng.g; n = g.n
    truth = dG.max(1)
    E = np.zeros(n)
    for v in range(n):
        b = 0
        while True:
            B = eng.bags[b]
            if not B['kids']:
                E[v] = max(E[v], dG[v, sorted(B['X'])].max()); break
            T, pats = tokens[b]
            hubs = sorted(T.VP & B['X'])
            E[v] = max(E[v], dG[v, hubs].max())
            if v in T.VP:
                E[v] = max(E[v], dG[v, sorted(B['X'])].max())   # A_X(v) by convergecast
            else:
                f = T.face.get(v)
                if f is not None:
                    all_ = np.flatnonzero(T.inX)
                    arr = np.full(T.no, np.inf)
                    arr[all_] = dG[v, T.xo[all_]]
                    cv = T.child.get(v, -2)
                    for f2, walk in enumerate(T.walks):
                        wk = np.array(walk)
                        for pat, top in pats[f2].items():
                            if mode == 'nochild':
                                cand = top[:1]
                            elif f2 != f:
                                cand = top[:1]
                            elif mode == 'top1':
                                cand = [z for z in top[:1] if z[1] != cv]
                            else:
                                cand = [z for z in top if z[1] != cv][:1]
                            for off, _, vv in cand:
                                if mode == 'bottom':
                                    off = 0
                                val = (arr[wk] + off + np.array(pat)).min()
                                st['chk.token_eval'] += 1
                                E[v] = max(E[v], val)
                                if mode == 'ok' and val != dG[v, vv]:
                                    st['FAIL.token_exact'] += 1
            if v in B['q']:
                break
            nxt = T.child.get(v)
            if nxt is None:
                nxt = next(k for k in B['kids'] if v in eng.bags[k]['X'])
            b = nxt
    bad = int((E != truth).sum())
    return bad, int((E > truth).sum()), int((E < truth).sum())


def sum_all(eng, dG, tokens, mode='ok'):
    """Section 5, Sum Corollary: S(u) from labels, hub sums and (count, offset sum) per pattern only."""
    g = eng.g; n = g.n
    chains = []; on = collections.defaultdict(set)
    for v in range(n):
        b = 0; c = []
        while True:
            c.append(b); on[b].add(v); B = eng.bags[b]
            if not B['kids'] or v in B['q']:
                break
            b = next(k for k in B['kids'] if v in eng.bags[k]['X'])
        chains.append(c)
    S = np.zeros(n)
    for b, B in eng.bags.items():
        Xo = sorted(on[b])
        if not B['kids']:
            for u in Xo:
                S[u] += dG[u, Xo].sum()
            continue
        T, _ = tokens[b]; SX = set(B['q'])
        kid = {v: next(k for k in B['kids'] if v in eng.bags[k]['X']) for v in Xo if v not in SX}
        rest = [v for v in Xo if v not in SX]
        hubs = [p for p in T.VP & B['X'] if p in on[b]]
        if mode == 'xo':
            hubs = sorted(T.VP & B['X'])
        total = collections.defaultdict(lambda: [0, 0]); inkid = collections.defaultdict(lambda: collections.defaultdict(lambda: [0, 0]))
        for v in rest:
            if v in T.vid:
                vec = T.vec(v); off = int(vec[0]); key = (T.face[v], tuple((vec - off).astype(int)))
                for rec in (total[key], inkid[kid[v]][key]):
                    rec[0] += 1; rec[1] += off
        for u in Xo:
            if u in SX:
                S[u] += dG[u, Xo].sum(); continue
            S[u] += sum(dG[u, h] for h in hubs if h in SX)
            Y = kid[u]
            if u in T.VP:
                S[u] += dG[u, rest].sum() - dG[u, sorted(on[Y])].sum(); continue
            S[u] += sum(dG[u, h] for h in hubs if h not in SX and kid.get(h) != Y)
            all_ = np.flatnonzero(T.inX)
            arr = np.full(T.no, np.inf)
            arr[all_] = dG[u, T.xo[all_]]
            memo = {}
            def value(key, rec):
                if key not in memo:
                    memo[key] = (arr[T.walks[key[0]]] + np.array(key[1])).min()
                return (1 if mode == 'cnt1' else rec[0]) * memo[key] + (0 if mode == 'nooff' else rec[1])
            S[u] += sum(value(k, r) for k, r in total.items())
            if mode != 'nosub':
                S[u] -= sum(value(k, r) for k, r in inkid[Y].items())
    return S


def sum_lane(seed, secs):
    """Main lane for S(u), then each mutation must make some S(u) wrong."""
    rng = random.Random(seed); st = collections.Counter(); t0 = time.time(); s = seed * 1000
    while time.time() - t0 < secs:
        s += 1
        r = instance(s, False, rng)
        if r is None:
            continue
        g, fam = r
        try:
            out = run_one(g, s, rng, collections.Counter())
        except Fail:
            continue
        if not out:
            continue
        eng, dG, tokens, par = out
        truth = dG.sum(1)
        st['runs'] += 1; st['chk.sum'] += g.n; st['FAIL.sum'] += int((sum_all(eng, dG, tokens) != truth).sum())
        st['max.n'] = max(st['max.n'], g.n)
        for mode in ('nosub', 'nooff', 'cnt1', 'xo'):
            st['ctl.' + mode] += bool((sum_all(eng, dG, tokens, mode) != truth).any())
    return st


def instance(s, big, rng):
    fams =['dl', 'grid', 'k2m', 'fan', 'nested', 'pend', 'flower']
    fam = fams[s % len(fams)]
    args = params(fam, random.Random(s * 31 + 7))
    if big and fam == 'dl':
        args['n'] = 300
    if big and fam == 'grid':
        args['k'] = 18
    pos, E = FAMS[fam](s, args)
    if not drawing_ok(pos, E):
        return None
    return PG(pos, E, seed=s), fam


def run_one(g, s, rng, st, mode='ok', leaf=None):
    import networkx as nx
    if not nx.is_connected(g.G):
        return False
    root = rng.randrange(g.n)
    eng = Bags(g, virtual_candidates(g.pos, g.ends), random.Random(s + 1),
               dict(leaf=leaf or rng.choice([6, 8, 14]), tries=30, modes={'bal': 1.0}, zall=0.0, swap=0.3,
                    degenerate=False, txmode='bfs', stop=True, root=root))
    eng.run()
    par = {root: None}; stack = [root]
    while stack:
        x = stack.pop()
        for y in eng.Tadj[x]:
            if y not in par:
                par[y] = x; stack.append(y)
    M = mk(list(g.ends), g.n)
    dG = shortest_path(M, unweighted=True)
    tokens = {}; eng.tb = {}
    order = sorted(eng.bags, key=lambda b: eng.bags[b]['depth'])
    for b in order:
        if eng.bags[b]['kids']:
            check_bag(eng, b, par, dG, st, rng, tokens)
            eng.tb[b] = tokens[b][0]
    return eng, dG, tokens, par


def lane(seed, secs, big):
    rng = random.Random(seed); st = collections.Counter(); t0 = time.time(); s = seed * 1000
    while time.time() - t0 < secs:
        s += 1
        r = instance(s, big, rng)
        if r is None:
            continue
        g, fam = r
        try:
            out = run_one(g, s, rng, st)
        except Fail:
            st['engine_fail'] += 1; continue
        if not out:
            continue
        eng, dG, tokens, par = out
        bad, hi, lo = ecc_all(eng, dG, tokens, st, 'ok', rng)
        st['chk.ecc'] += g.n; st['FAIL.ecc'] += bad; st['runs'] += 1; st['runs|' + fam] += 1
        st['max.n'] = max(st['max.n'], g.n); st['max.D'] = max(st['max.D'], int(dG.max()))
        st['max.bags'] = max(st['max.bags'], len(eng.bags))
    return st


def controls(seed, secs):
    """Each mutation must make some eccentricity wrong."""
    out = {}
    for mode in ('nochild', 'top1', 'bottom', 'noanc'):
        rng = random.Random(seed); st = collections.Counter(); t0 = time.time(); s = seed * 1000; c = collections.Counter()
        while time.time() - t0 < secs:
            s += 1
            r = instance(s, False, rng)
            if r is None:
                continue
            g, fam = r
            try:
                res = run_one(g, s, rng, st)
            except Fail:
                continue
            if not res:
                continue
            eng, dG, tokens, par = res
            if mode == 'noanc':
                t2 = {}
                for b in tokens:
                    T = Table(eng, b, par, collections.Counter(), noanc=True, nolink=True)
                    pats = [collections.defaultdict(list) for _ in T.walks]
                    for v in T.face:
                        vec = T.vec(v); off = int(vec[0]) if np.isfinite(vec[0]) else 0
                        pat = tuple(vec - off)
                        pats[T.face[v]][pat].append((off, T.child.get(v, -1), v))
                    tb = []
                    for d in pats:
                        tab = {}
                        for pat, lst in d.items():
                            lst.sort(key=lambda z: -z[0]); top = []
                            for z in lst:
                                if not top or z[1] != top[0][1]:
                                    top.append(z)
                                    if len(top) == 2:
                                        break
                            tab[pat] = top
                        tb.append(tab)
                    t2[b] = (T, tb)
                tokens = t2
            bad, hi, lo = ecc_all(eng, dG, tokens, c, 'nochild' if mode == 'nochild' else mode if mode != 'noanc' else 'ctl', rng)
            c['runs'] += 1; c['runs_wrong'] += bad > 0; c['too_high'] += hi; c['too_low'] += lo
        out[mode] = dict(c)
    return out


def second_instance(b, c, tooth):
    """A forced root: q ends at a, and the closing edge separates two combs at a, in one corner of P."""
    sys.path.insert(0, os.path.join(HERE, '..', 'maxflow'))
    from forced import Forced

    class FB(Forced, Bags):
        pass
    pos = [(0.0, 0.0)]; E = []

    def add(p, prev):
        pos.append(p); E.append((prev, len(pos) - 1)); return len(pos) - 1
    for sgn, m in ((1, b), (-1, c)):
        prev = 0
        for x in range(1, m + 1):
            prev = add((sgn * float(x), 0.0), prev); t = prev
            for i in range(1, tooth + 1):
                t = add((sgn * (x + 0.2), (0.8 if x % 2 else -0.8) * i / tooth), t)
    prev = 0; q = [0]
    for p in [(0.0, 1.0)] + [(float(x), 1.0) for x in range(1, b + 2)] + [(b + 1.0, 0.0)] + [(float(x), -1.0) for x in range(b + 1, -1, -1)]:
        prev = add(p, prev); q.append(prev)
    E.append((prev, 0))
    assert drawing_ok(pos, E)
    g = PG(pos, E, seed=1)
    eng = FB(g, random.Random(1), dict(leaf=8, tries=30, modes={'bal': 1.0}, zall=0.0, swap=0.3, degenerate=False, txmode='bfs', stop=True, root=0), q, False)
    eng.run()
    par = {0: None}; stack = [0]
    while stack:
        x = stack.pop()
        for y in eng.Tadj[x]:
            if y not in par:
                par[y] = x; stack.append(y)
    return eng, g, shortest_path(mk(list(g.ends), g.n), unweighted=True), par


def second_token():
    """Without the second token the eccentricity of the far end of the longer comb is wrong."""
    out = []
    for b, c, tooth in ((4, 5, 6), (6, 8, 9), (3, 3, 5)):
        eng, g, dG, par = second_instance(b, c, tooth)
        st = collections.Counter(); tokens = {}; eng.tb = {}
        for bb in sorted(eng.bags, key=lambda z: eng.bags[z]['depth']):
            if eng.bags[bb]['kids']:
                check_bag(eng, bb, par, dG, st, random.Random(1), tokens); eng.tb[bb] = tokens[bb][0]
        ok = ecc_all(eng, dG, tokens, st, 'ok', random.Random(1)); top1 = ecc_all(eng, dG, tokens, st, 'top1', random.Random(1))
        out.append(dict(n=g.n, ok_wrong=ok[0], top1_wrong=top1[0], fails=sum(v for a, v in st.items() if a.startswith('FAIL'))))
    return out


def scale():
    """Tokens and dictionary against D^2 on full square grids."""
    res = []
    for k in (6, 10, 14, 18, 24, 30, 40):
        st = collections.Counter(); rng = random.Random(k)
        pos, E = FAMS['grid'](k, dict(k=k, drop=0.0))
        g = PG(pos, E, seed=k)
        run_one(g, k, rng, st, leaf=8)
        res.append(dict(k=k, n=g.n, D=2 * (k - 1), tokens_4E2=st['max.tokens_over_4E2_x100'], dict_4E2=st['max.dict_over_4E2_x100'], E_D=st['max.E_over_D_x100'], pat_K2=st['max.pat_over_K2_x100'],
                        fails=sum(v for a, v in st.items() if a.startswith('FAIL'))))
    return res


if __name__ == '__main__':
    if sys.argv[1] == 'ctl':
        print(json.dumps(controls(int(sys.argv[2]), float(sys.argv[3]))))
    elif sys.argv[1] == 'scale':
        print(json.dumps(scale()))
    elif sys.argv[1] == 'second':
        print(json.dumps(second_token()))
    elif sys.argv[1] == 'sum':
        print(json.dumps(dict(sum_lane(int(sys.argv[2]), float(sys.argv[3]))), sort_keys=True))
    else:
        print(json.dumps(dict(lane(int(sys.argv[1]), float(sys.argv[2]), len(sys.argv) > 3)), sort_keys=True))
