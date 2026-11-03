"""Checks of notes/APPROX_DIAMETER.md on the region bags of notes/LEMMA15.md, Section 9.
python3 -I approx.py SEED SECS [big]   main lane
python3 -I approx.py ctl SEED SECS     negative controls
python3 -I approx.py scale             tokens against rho on grids
python3 -I approx.py second            an instance that needs the second token
"""
import collections, json, os, random, sys, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from diam import Bags, Table, mk, instance, segments, second_instance, FAMS, PG, Fail, virtual_candidates, np, shortest_path


def greedy_net(L, dist, rho):
    """first-fit maximal subset of L with pairwise distance above rho"""
    net = []
    for x in L:
        if all(dist(x, c) > rho for c in net):
            net.append(x)
    return net


def tree_metric(eng, B):
    """hop metric of a BFS tree of R_X, for a leaf"""
    g = eng.g; X = sorted(B['X']); ix = {v: i for i, v in enumerate(X)}
    adj = collections.defaultdict(list)
    for e in B['E']:
        a, c = g.ends[e]; adj[a].append(c); adj[c].append(a)
    seen = {X[0]}; st = [X[0]]; E = []
    while st:
        x = st.pop(0)
        for y in adj[x]:
            if y not in seen:
                seen.add(y); st.append(y); E.append((ix[x], ix[y]))
    return ix, shortest_path(mk(E, len(X)), unweighted=True), len(seen) == len(X)


def relax(A):
    """A: walk positions x vertices. Closure under +1 along the cycle."""
    k = A.shape[0]
    for _ in range(2):
        for j in range(1, k + 1):
            A[j % k] = np.minimum(A[j % k], A[j - 1] + 1)
        for j in range(k - 1, -1, -1):
            A[j] = np.minimum(A[j], A[(j + 1) % k] + 1)
    return A


def portals(T, walk, rho):
    """Scan the occurrences in V(X) along the walk; a new portal once more than rho steps from the last."""
    out = []
    for i, o in enumerate(walk):
        if T.inX[o] and (not out or i - out[-1] > rho):
            out.append(i)
    return out


def alternates(a):
    """strict sign sequence of a has + - + or - + -"""
    s = [x for x in np.sign(a) if x != 0]
    return sum(s[i] != s[i - 1] for i in range(1, len(s))) >= 2


def build(eng, dG, rho, st, rng, mode='ok'):
    """Top down: nets, the estimates e, h, tokens and hub maxima of each bag."""
    g = eng.g; n = g.n; D = dG.max(); lev = {}
    par = eng.par
    netrho = 3 * rho if mode == 'netwide' else rho
    on = collections.defaultdict(set)
    for v in range(n):
        b = 0
        while True:
            on[b].add(v); B = eng.bags[b]
            if not B['kids'] or v in B['q']:
                break
            b = next(k for k in B['kids'] if v in eng.bags[k]['X'])
    for b in sorted(eng.bags, key=lambda z: eng.bags[z]['depth']):
        B = eng.bags[b]; X = sorted(B['X']); L = {}
        if B['kids']:
            T = Table(eng, b, par, st)
            VP = sorted(T.VP); ix = {v: i for i, v in enumerate(VP)}
            ell = shortest_path(mk([(ix[a], ix[c]) for a, c in T.Pe], len(VP)), unweighted=True)
            hubs = sorted(T.VP & B['X'])
            E = len(T.Pe)
        else:
            T = None
            ix, ell, conn = tree_metric(eng, B)
            st['chk.leaf_connected'] += 1; st['FAIL.leaf_connected'] += int(not conn)
            hubs = X; E = len(X) - 1
        net = greedy_net(hubs, lambda x, c: ell[ix[x], ix[c]], netrho)
        st['chk.net_size'] += 1
        if len(net) > 1 + 3 * E / netrho:
            st['FAIL.net_size'] += 1
        st['max.net'] = max(st['max.net'], len(net))
        e = np.full((n, len(net)), np.inf)
        d = B['depth']
        if B['parent'] is None:
            e[:, :] = dG[:, net]
        else:
            xi = {v: i for i, v in enumerate(X)}
            M = mk([(xi[g.ends[q][0]], xi[g.ends[q][1]]) for q in B['E']], len(X))
            bv = shortest_path(M, unweighted=True, indices=[xi[c] for c in net])
            bv[bv > D] = np.inf
            la = lev[B['parent']]
            for j, c in enumerate(net):
                val = bv[j]
                if mode != 'norow':
                    val = np.minimum(val, (la['h'][X] + la['e'][c]).min(1))
                e[X, j] = val
        sub = dG[X][:, net]; got = e[X]
        st['chk.invariant'] += got.size
        st['FAIL.invariant_low'] += int((got < sub).sum())
        st['FAIL.invariant_high'] += int((got > sub + 2 * rho * d).sum())
        st['max.inv_err_over_rho_x100'] = max(st['max.inv_err_over_rho_x100'], int(100 * (got - sub).max() / rho) if np.isfinite(got).all() else 10 ** 9)
        L.update(net=net, e=e, ix=ix, ell=ell, T=T, near={x: next(c for c in net if ell[ix[x], ix[c]] <= netrho) for x in hubs}, pos={c: j for j, c in enumerate(net)})
        L['A'] = np.array([e[sorted(on[b]), j].max() if on[b] else -np.inf for j in range(len(net))])
        if T is not None:
            ft = shortest_path(mk(T.inner, T.N), unweighted=True, indices=np.arange(T.no))
            ft[ft > D + max(len(w) for w in T.walks)] = np.inf
            h = np.full((n, len(net)), np.inf)
            nidx = [ix[c] for c in net]
            for v in X:
                if v in T.VP:
                    h[v] = ell[ix[v], nidx]
            face_v = collections.defaultdict(list)
            for v, f in T.face.items():
                face_v[f].append(v)
            L['tok'] = {}; L['Pi'] = {}
            ntok = 0; ndict = 0
            for f, walk in enumerate(T.walks):
                vs = face_v[f]
                if not vs:
                    continue
                w = np.array(walk); ids = [T.vid[v] for v in vs]
                raw = ft[w][:, ids]
                xs = [ix[x] for x in T.xo[w]]
                h[vs] = (raw[:, :, None] + ell[xs][:, nidx][:, None, :]).min(0)
                tau = relax(raw.copy())
                if not np.isfinite(tau).all():
                    st['FAIL.tau_inf'] += 1
                pi = portals(T, walk, rho)
                L['Pi'][f] = (pi, [L['near'][T.xo[w[i]]] for i in pi])
                vals = tau[pi]
                if mode == 'noise':
                    vals = vals + np.array([[rng.choice((-1, 0, 1)) for _ in vs] for _ in pi])
                off = vals[0].astype(int); G = (vals - vals[0]).astype(int)
                for _ in range(min(60, len(vs) * len(vs))):
                    a, c = rng.randrange(len(vs)), rng.randrange(len(vs))
                    if a != c:
                        st['chk.single_crossing'] += 1
                        st['FAIL.single_crossing'] += int(alternates(G[:, a] - G[:, c]))
                    # on all positions, not only portals
                    if a != c and rng.random() < 0.2:
                        all_ = tau - tau[0]
                        st['chk.single_crossing_all'] += 1
                        st['FAIL.single_crossing_all'] += int(alternates(all_[:, a] - all_[:, c]))
                R = np.floor(G / rho).astype(int)
                table = collections.defaultdict(list)
                for j, v in enumerate(vs):
                    table[tuple(R[:, j])].append((int(off[j]), T.child.get(v, -1), v))
                m = len(pi); Y = R.max() - R.min() + 1 if R.size else 1
                N = m * Y
                st['chk.sauer'] += 1
                if len(table) > 1 + N + N * (N - 1) // 2:
                    st['FAIL.sauer'] += 1
                K = len(walk); Yb = K // rho + 2
                if Y > Yb:
                    st['FAIL.levels'] += 1
                top_ = {}
                for pat, lst in table.items():
                    lst.sort(key=lambda z: z[0] if mode == 'bottom' else -z[0]); top = []
                    for z in lst:
                        if not top or z[1] != top[0][1]:
                            top.append(z)
                            if len(top) == 2:
                                break
                    top_[pat] = top; ntok += len(top)
                L['tok'][f] = top_
                # dictionary on the segment tree over portal positions
                if m >= 2:
                    P = np.array(list(top_), int)
                    for l, r in segments(0, m - 1):
                        cnt = len({tuple(row) for row in P[:, l:r + 1]})
                        ndict += cnt
                        N2 = (r - l + 1) * Y
                        st['chk.interval'] += 1
                        if cnt > 1 + N2 + N2 * (N2 - 1) // 2:
                            st['FAIL.interval'] += 1
                else:
                    ndict += 1
                st['max.pat_face'] = max(st['max.pat_face'], len(top_))
            L['h'] = h
            kp = sum(len(p[0]) for p in L['Pi'].values())
            st['max.portals'] = max(st['max.portals'], kp)
            st['max.tokens'] = max(st['max.tokens'], ntok); st['max.dict'] = max(st['max.dict'], ndict)
            st['max.E_over_rho'] = max(st['max.E_over_rho'], int(2 * E / rho))
            st['max.nfaces'] = max(st['max.nfaces'], len(T.walks))
        lev[b] = L
    return lev


def ecc_est(eng, dG, lev, rho, st, mode='ok'):
    """Section 5: the estimate of every eccentricity from e, h, tokens and hub maxima."""
    n = eng.g.n; Est = np.zeros(n)
    for u in range(n):
        b = 0
        while True:
            B = eng.bags[b]; L = lev[b]; T = L['T']
            Est[u] = max(Est[u], L['e'][u].max())
            if T is None:
                break
            pos = L['pos']
            if u in T.VP:
                if u in L['near']:
                    Est[u] = max(Est[u], L['A'][pos[L['near'][u]]])
            else:
                f0 = T.face[u]; cu = T.child.get(u, -2)
                au = L['e'][u]
                for f, tab in L['tok'].items():
                    pi, cs = L['Pi'][f]
                    ac = au[[pos[c] for c in cs]]
                    for pat, top in tab.items():
                        if f != f0 or mode == 'nochild':
                            cand = top[:1]
                        elif mode == 'top1':
                            cand = [z for z in top[:1] if z[1] != cu]
                        else:
                            cand = [z for z in top if z[1] != cu][:1]
                        for off, _, z in cand:
                            val = (ac + off + rho * np.array(pat)).min()
                            Est[u] = max(Est[u], val)
                            st['chk.token'] += 1
                            st['FAIL.token_low'] += int(val < dG[u, z] - 2 * rho)
                            st['FAIL.token_high'] += int(val > dG[u, z] + (3 + 2 * B['depth']) * rho)
            if u in B['q']:
                break
            b = next(k for k in B['kids'] if u in eng.bags[k]['X'])
    return Est


def run(g, s, rng, rho, st, mode='ok', leaf=None):
    import networkx as nx
    if not nx.is_connected(g.G):
        return None
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
    eng.par = par
    dG = shortest_path(mk(list(g.ends), g.n), unweighted=True)
    lev = build(eng, dG, rho, st, rng, mode)
    Est = ecc_est(eng, dG, lev, rho, st, mode)
    H = max(B['depth'] for B in eng.bags.values())
    return Est, dG.max(1), H


def lane(seed, secs, big):
    rng = random.Random(seed); st = collections.Counter(); t0 = time.time(); s = seed * 1000
    while time.time() - t0 < secs:
        s += 1
        r = instance(s, big, rng)
        if r is None:
            continue
        g, fam = r
        rho = rng.choice([1, 2, 3, 4, 6, 8, 12])
        try:
            res = run(g, s, rng, rho, st)
        except Fail:
            st['engine_fail'] += 1; continue
        if res is None:
            continue
        Est, ecc, H = res
        st['runs'] += 1; st['runs|' + fam] += 1; st['chk.ecc'] += g.n
        st['FAIL.low'] += int((Est < ecc - 2 * rho).sum())
        st['FAIL.high'] += int((Est > ecc + (3 + 2 * H) * rho).sum())
        st['max.under_over_rho_x100'] = max(st['max.under_over_rho_x100'], int(100 * (ecc - Est).max() / rho))
        st['max.over_over_rho_x100'] = max(st['max.over_over_rho_x100'], int(100 * (Est - ecc).max() / rho))
        st['max.n'] = max(st['max.n'], g.n); st['max.ecc'] = max(st['max.ecc'], int(ecc.max())); st['max.H'] = max(st['max.H'], H)
    return st


def controls(seed, secs):
    """Each mutation should make a check fail; top1 fires only on the forced instance of second()."""
    out = {}
    for mode in ('nochild', 'top1', 'bottom', 'norow', 'netwide', 'noise'):
        rng = random.Random(seed); t0 = time.time(); s = seed * 1000; c = collections.Counter()
        while time.time() - t0 < secs:
            s += 1
            r = instance(s, False, rng)
            if r is None:
                continue
            g, fam = r
            rho = rng.choice([1, 2, 3])
            st = collections.Counter()
            try:
                res = run(g, s, rng, rho, st, mode)
            except (Fail, OverflowError, ValueError):
                c['crash'] += 1; continue
            if res is None:
                continue
            Est, ecc, H = res
            c['runs'] += 1
            c['low'] += int((Est < ecc - 2 * rho).sum()); c['high'] += int((Est > ecc + (3 + 2 * H) * rho).sum())
            c['under_rho'] += int((Est < ecc - rho).sum()); c['over_3rho'] += int((Est > ecc + 3 * rho).sum())
            for k, v in st.items():
                if k.startswith('FAIL') and v:
                    c[k] += int(v)
        out[mode] = dict(c)
    return out


def second():
    """The forced instance of diam.py: without the second token some value is too low."""
    out = []
    for b, c, tooth in ((4, 5, 6), (6, 8, 9), (3, 3, 5), (6, 8, 16)):
        eng, g, dG, par = second_instance(b, c, tooth)
        eng.par = par; rng = random.Random(1)
        for rho in (1, 2):
            st = collections.Counter()
            lev = build(eng, dG, rho, st, rng)
            ok = ecc_est(eng, dG, lev, rho, st); top1 = ecc_est(eng, dG, lev, rho, collections.Counter(), 'top1')
            ecc = dG.max(1)
            out.append(dict(n=g.n, rho=rho, ok_low=int((ok < ecc - 2 * rho).sum()), top1_low=int((top1 < ecc - 2 * rho).sum()), fails=sum(v for a, v in st.items() if a.startswith('FAIL'))))
    return out


def scale():
    """Tokens and net size against rho on full grids."""
    res = []
    for k in (20, 30, 40):
        for rho in (1, 2, 4, 8, 16):
            st = collections.Counter(); rng = random.Random(k)
            pos, E = FAMS['grid'](k, dict(k=k, drop=0.0))
            g = PG(pos, E, seed=k)
            Est, ecc, H = run(g, k, rng, rho, st, leaf=8)
            res.append(dict(k=k, n=g.n, D=int(ecc.max()), rho=rho, H=H, net=st['max.net'], portals=st['max.portals'], tokens=st['max.tokens'], dict=st['max.dict'],
                            E_rho=st['max.E_over_rho'], faces=st['max.nfaces'], over=float((Est - ecc).max()), under=float((ecc - Est).max()),
                            fails=sum(v for a, v in st.items() if a.startswith('FAIL'))))
    return res


if __name__ == '__main__':
    if sys.argv[1] == 'ctl':
        print(json.dumps(controls(int(sys.argv[2]), float(sys.argv[3]))))
    elif sys.argv[1] == 'scale':
        print(json.dumps(scale()))
    elif sys.argv[1] == 'second':
        print(json.dumps(second()))
    else:
        print(json.dumps({k: int(v) for k, v in lane(int(sys.argv[1]), float(sys.argv[2]), len(sys.argv) > 3).items()}, sort_keys=True))
