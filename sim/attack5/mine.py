"""Independent implementation of Lemma B5 (LEMMA15.md 9.6) written from the text, plus an
independent side counter (faces of the plane graph with the closing edge inserted, classes of
faces across non-cycle edges) and checks of every claim inside the proof.

Conventions: rot[v] is the cyclic order of neighbours; corner (v, j) lies between rot[v][j-1]
and rot[v][j]. The face walk goes from corner (v, j) along the edge to u = rot[v][j] and arrives
at corner (u, idx[u][v] + 1)."""
import sys, collections

sys.dont_write_bytecode = True
sys.setrecursionlimit(100000)


class Fail(Exception):
    pass


def mkidx(rot):
    return {v: {u: j for j, u in enumerate(rot[v])} for v in rot}


def corner_faces(rot, idx):
    """face id of every corner, and faces as corner sequences in walk order"""
    fid = {}; faces = []
    for v in rot:
        for j in range(len(rot[v])):
            if (v, j) in fid:
                continue
            f = len(faces); seq = []
            c = (v, j)
            while c not in fid:
                fid[c] = f; seq.append(c)
                a, i = c; u = rot[a][i]
                c = (u, (idx[u][a] + 1) % len(rot[u]))
            if c != (v, j):
                raise Fail('face orbit not closed')
            faces.append(seq)
    return fid, faces


def is_planar_rot(rot, idx):
    n = len(rot); E = sum(len(rot[v]) for v in rot) // 2
    _, faces = corner_faces(rot, idx)
    return n - E + len(faces) == 2


def tour(rot, idx, par, r, k):
    """iterative: from the start of corner (r, k), follow the boundary of a thin neighbourhood of
    T. Items: ('c', v, j) corner, ('m', w) a side of the parent edge of w, ('a', v, u) end at v
    of the non-tree edge vu."""
    items = []
    v, j = r, k
    while True:
        items.append(('c', v, j))
        u = rot[v][j]
        if par.get(u) == v:
            items.append(('m', u)); v, j = u, (idx[u][v] + 1) % len(rot[u])
        elif par.get(v) == u:
            items.append(('m', v)); v, j = u, (idx[u][v] + 1) % len(rot[u])
        else:
            items.append(('a', v, u)); j = (j + 1) % len(rot[v])
        if (v, j) == (r, k):
            break
    return items


def anc(par, v):
    out = [v]
    while par[v] is not None:
        v = par[v]; out.append(v)
    return out


def tpath(par, x, z):
    ax = anc(par, x); az = anc(par, z); sz = set(az)
    i = 0
    while ax[i] not in sz:
        i += 1
    l = ax[i]
    return ax[:i + 1] + az[:az.index(l)][::-1]


def sides_indep(V, rot, cyc, virt, seed):
    """cyc: list of vertices of the tree path x..z. virt: None (real closing edge zx, which must
    be an edge of rot) or (jx, jz): insert a virtual edge at corner jx of x and corner jz of z
    (indices in the original rotations). seed: a corner (v, i) of the augmented rotation that lies
    on the side we call 'in'. Returns (in, out) from face classes; checks Euler and Jordan."""
    x, z = cyc[0], cyc[-1]
    R2 = {v: [(u, 0) for u in rot[v]] for v in V}
    if virt is not None:
        if x == z:
            raise Fail('virtual loop')
        R2[x].insert(virt[0], (z, 1)); R2[z].insert(virt[1], (x, 1))
    ix = {v: {t: i for i, t in enumerate(R2[v])} for v in V}
    fid = {}; nf = 0
    for v in V:
        for j in range(len(R2[v])):
            if (v, j) in fid:
                continue
            c = (v, j)
            while c not in fid:
                fid[c] = nf
                a, i = c; u, tg = R2[a][i]
                c = (u, (ix[u][(a, tg)] + 1) % len(R2[u]))
            nf += 1
    E2 = sum(len(R2[v]) for v in V) // 2
    if len(V) - E2 + nf != 2:
        raise Fail('closing edge breaks planarity (corners not in one face)')
    Ce = set()
    for a, b in zip(cyc, cyc[1:]):
        Ce.add((frozenset((a, b)), 0))
    Ce.add((frozenset((x, z)), 1 if virt is not None else 0))
    if virt is None and len(cyc) < 3:
        raise Fail('real closing edge is a tree edge')
    p = list(range(nf))
    def find(a):
        while p[a] != a:
            p[a] = p[p[a]]; a = p[a]
        return a
    for v in V:
        d = len(R2[v])
        for i in range(d):
            u, tg = R2[v][i]
            if (frozenset((v, u)), tg) in Ce:
                continue
            a, b = find(fid[(v, i)]), find(fid[(v, (i + 1) % d)])
            if a != b:
                p[a] = b
    cls = {find(f) for f in range(nf)}
    if len(cls) != 2:
        raise Fail('cycle does not split faces in two classes: %d' % len(cls))
    sc = find(fid[seed])
    S = set(cyc); cin = cout = 0
    for v in V:
        if v in S:
            continue
        cs = {find(fid[(v, i)]) for i in range(len(R2[v]))}
        if len(cs) != 1:
            raise Fail('vertex %r on both sides' % (v,))
        if sc in cs:
            cin += 1
        else:
            cout += 1
    return cin, cout


def run(V, rot, idx, par, r, k, deep=True, neg=None):
    """Lemma B5 from the text. Returns result dict and records the proof quantities. With deep,
    every count is also checked against sides_indep and all internal claims are asserted."""
    n = len(V)
    depth = {v: len(anc(par, v)) - 1 for v in V}
    h = max(depth.values())
    it = tour(rot, idx, par, r, k)
    L = len(it)
    E = sum(len(rot[v]) for v in V) // 2
    if L != 4 * E:
        raise Fail('tour length')
    pref = [0] * (L + 1)
    for q, t in enumerate(it):
        pref[q + 1] = pref[q] + (t[0] == 'm')
    TOT = pref[L]
    if TOT != 2 * (n - 1):
        raise Fail('marks')
    pos = {}
    ends = collections.defaultdict(list)
    for q, t in enumerate(it):
        if t[0] == 'c':
            if (t[1], t[2]) in pos:
                raise Fail('corner twice')
            pos[(t[1], t[2])] = q
        elif t[0] == 'a':
            ends[frozenset((t[1], t[2]))].append((q, t[1], t[2]))
    if len(pos) != 2 * E:
        raise Fail('corners missed')
    fid, faces = corner_faces(rot, idx)
    plen = lambda a, b: len(tpath(par, a, b))

    def count(m, P):
        tw = m - P + 1
        if tw < 0 or tw % 2:
            raise Fail('marks lemma parity/neg m=%d P=%d' % (m, P))
        i = tw // 2; o = n - P - i
        if o < 0:
            raise Fail('negative out')
        return i, o

    def arcmarks(p, q):  # marks on the arc from position p forward to position q
        return pref[q] - pref[p] if q >= p else TOT - (pref[p] - pref[q])

    st = collections.Counter(); mx = {}
    def upd(key, val, f=max):
        mx[key] = val if key not in mx else f(mx[key], val)

    chords = []
    for e, es in ends.items():
        if len(es) != 2:
            raise Fail('chord ends')
        (p1, u, v), (p2, _, _) = sorted(es)
        P = plen(u, v)
        i, o = count(pref[p2] - pref[p1], P)
        ch = dict(p1=p1, p2=p2, u=u, v=v, P=P, ins=i, out=o)
        if deep:
            # marks lemma on both arcs of the real chord, against the independent count
            cyc = tpath(par, u, v)
            seed_far = (u, (idx[u][v] + 1) % len(rot[u]))
            ci, co = sides_indep(V, rot, cyc, None, seed_far)
            if (ci, co) != (i, o):
                raise Fail('marks lemma far arc: indep %s vs %s' % ((ci, co), (i, o)))
            i2, o2 = count(TOT - (pref[p2] - pref[p1]), P)
            if (i2, o2) != (o, i):
                raise Fail('marks lemma near arc')
            st['chord_marks_checks'] += 2
        chords.append(ch)
    bal = lambda i, o: 3 * i <= 2 * n and 3 * o <= 2 * n
    res = dict(n=n, h=h)
    good = [c for c in chords if bal(c['ins'], c['out'])]
    if good and neg != 'skip1':
        c = min(good, key=lambda c: (min(c['u'], c['v']), max(c['u'], c['v'])))
        res.update(kind='real', x=c['u'], z=c['v'], ins=c['ins'], out=c['out'], cyc=tpath(par, c['u'], c['v']), virt=None,
                   seed=(c['u'], (idx[c['u']][c['v']] + 1) % len(rot[c['u']])))
    else:
        heavy = [c for c in chords if 3 * c['ins'] > 2 * n]
        # heavy chords nested (a chain), by containment of far arcs
        for a in heavy:
            for b in heavy:
                if a is b:
                    continue
                ina = a['p1'] < b['p1'] < a['p2']
                inb = b['p1'] < a['p1'] < b['p2']
                if not (ina or inb):
                    raise Fail('heavy chords not nested')
        if heavy and neg != 'noheavy':
            e0 = min(heavy, key=lambda c: c['p2'] - c['p1'])
            for c in heavy:
                if not (c['p1'] <= e0['p1'] and e0['p2'] <= c['p2']):
                    raise Fail('innermost not unique')
            t = it[e0['p1'] + 1]
            if t[0] != 'c':
                raise Fail('item after chord end not a corner')
            F = fid[(t[1], t[2])]
            # the face just inside e0 also holds the corner just before its far end
            t2 = it[e0['p2'] - 1]
            if t2[0] != 'c' or fid[(t2[1], t2[2])] != F:
                raise Fail('face just inside e0 ambiguous')
            res['e0'] = (e0['u'], e0['v'])
        else:
            F = fid[(r, k)]; e0 = None
        Fc = faces[F]
        cnt = collections.Counter(v for v, _ in Fc)
        one = sorted(v for v in cnt if cnt[v] == 1)
        if deep:
            # x exists; every vertex with >= 2 corners in F is a cut vertex of B
            Bedges = set()
            for (a, j) in Fc:
                Bedges.add(frozenset((a, rot[a][j])))
            adj = collections.defaultdict(set)
            for e in Bedges:
                a, b = tuple(e); adj[a].add(b); adj[b].add(a)
            def ncomp(skip):
                seen = set(); comps = 0
                for s in adj:
                    if s == skip or s in seen:
                        continue
                    comps += 1; q = [s]; seen.add(s)
                    while q:
                        y = q.pop()
                        for w in adj[y]:
                            if w != skip and w not in seen:
                                seen.add(w); q.append(w)
                return comps
            if ncomp(None) != 1:
                raise Fail('B not connected')
            for v in cnt:
                if cnt[v] >= 2 and ncomp(v) < 2:
                    raise Fail('vertex with 2 corners in F is not a cut vertex of B')
        if neg == 'anycorner':
            one = sorted(cnt)
        if not one:
            raise Fail('no vertex with exactly one corner in F')
        x = one[0]
        c0 = min((c for c in Fc if c[0] == x), key=lambda c: pos[c])
        # walk around F from c0
        s = Fc.index(c0)
        walk = Fc[s:] + Fc[:s]
        m = len(walk) - 1
        if m < 1:
            raise Fail('face with one corner')
        # order along the walk = order along gamma
        keys = [(pos[c] - pos[c0]) % L for c in walk]
        if keys != sorted(keys):
            raise Fail('face walk not in gamma order')
        p0 = pos[c0]
        ins_ = [0]; outs = [n - 1]; Ps = [1]
        chosen = None
        for j in range(1, m + 1):
            cj = walk[j]; w = cj[0]
            if w == x and neg != 'anycorner':
                raise Fail('x has two corners in F')
            P = plen(x, w) if w != x else 1
            mm = arcmarks(p0, pos[cj])
            i, o = count(mm, P)
            ins_.append(i); outs.append(o); Ps.append(P)
            if deep and w != x:
                cyc = tpath(par, x, w)
                ci, co = sides_indep(V, rot, cyc, (c0[1], cj[1]), (x, c0[1] + 1))
                if (ci, co) != (i, o):
                    raise Fail('marks lemma virtual: indep %s vs %s (j=%d)' % ((ci, co), (i, o), j))
                st['virt_marks_checks'] += 1
            # step c_{j-1} -> c_j
            pa, pb = pos[walk[j - 1]], pos[cj]
            seg = [it[(pa + t) % L] for t in range(1, (pb - pa) % L)]
            Wm1 = ins_[j - 1] + Ps[j - 1]
            if len(seg) == 1 and seg[0][0] == 'm':
                st['tree_steps'] += 1
                if not (i <= ins_[j - 1] + 1 <= Wm1):
                    raise Fail('tree step bound j=%d' % j)
                if j == 1 and i != 0:
                    raise Fail('in_1 != 0 after tree step')
                upd('tree_step_ratio', i / Wm1)
            else:
                if seg[0][0] != 'a' or seg[-1][0] != 'a' or frozenset(seg[0][1:]) != frozenset(seg[-1][1:]):
                    raise Fail('step is neither a tree side nor a chord')
                a_, b_ = seg[0][1], seg[0][2]
                if (a_, b_) != (walk[j - 1][0], w):
                    raise Fail('chord step endpoints')
                ce = frozenset((a_, b_))
                ch = [c for c in chords if frozenset((c['u'], c['v'])) == ce][0]
                Te = ch['P']
                inside = (pa < ch['p1'] < pb) if pb > pa else not (pb < ch['p1'] < pa)
                # skipped arc: from the chord end after c_{j-1} to the end before c_j
                ms = arcmarks((pa + 1) % L, (pb - 1) % L)
                k_e, _ = count(ms, Te)
                Wp = k_e + Te
                if deep:
                    cyc = tpath(par, a_, b_)
                    sd = (a_, (idx[a_][b_] + 1) % len(rot[a_]))
                    ci, co = sides_indep(V, rot, cyc, None, sd)
                    if ci != k_e:
                        raise Fail('skipped side count')
                if 3 * Wp >= n:
                    raise Fail("W' >= n/3 at chord step j=%d (W'=%d n=%d)" % (j, Wp, n))
                if e0 is not None and ce == frozenset((e0['u'], e0['v'])):
                    st['e0_steps'] += 1
                    if Wp != n - e0['ins']:
                        raise Fail("W' of e0")
                else:
                    c_is_light = 3 * ch['out'] > 2 * n
                    if not c_is_light:
                        raise Fail('chord on F boundary is not light')
                    if Wp != ch['ins'] + Te:
                        raise Fail("W' of light chord != W(e)")
                d1, d2, d3 = Ps[j - 1] - 1, Te - 1, P - 1
                if d1 + d2 - d3 > 2 * min(d1, d2):
                    raise Fail('triangle')
                if 2 * i != 2 * ins_[j - 1] + d1 + 2 * (Wp - Te) + d2 - d3:
                    raise Fail('step identity')
                if not (i <= ins_[j - 1] + Wp + min(d1, d2) - d2 - 1):
                    raise Fail('chord step fine bound')
                if not (i < Wm1 + Wp):
                    raise Fail('chord step bound j=%d' % j)
                if j == 1 and i != Wp - Te:
                    raise Fail('in_1 != W\'-|T[e]|')
                st['chord_steps'] += 1
                upd('chord_step_ratio', i / (Wm1 + Wp))
                upd('chord_step_min_slack', Wm1 + Wp - i, min)
                upd('fine_bound_min_slack', ins_[j - 1] + Wp + min(d1, d2) - d2 - 1 - i, min)
                if j > 1:
                    upd('gain_over_Wp_j>1', (i - ins_[j - 1]) / Wp)
                    upd('Wp_over_n', Wp / n)
            if j == 1:
                if 3 * i >= n:
                    raise Fail('in_1 >= n/3')
                upd('in1_over_n', i / n)
            if chosen is None and 3 * o <= 2 * n:
                chosen = j
            if chosen is None and j > 1 and 3 * o <= 2 * n:
                pass
        # last corner: out_m < n/3
        if 3 * outs[m] >= n:
            raise Fail('out_m >= n/3')
        upd('outm_over_n', outs[m] / n)
        if chosen is None:
            raise Fail('no j qualifies')
        j = chosen; cj = walk[j]
        if j > 1:
            if not (3 * outs[j - 1] > 2 * n):
                raise Fail('first j not first')
            Wm1 = ins_[j - 1] + Ps[j - 1]
            if 3 * Wm1 >= n:
                raise Fail('W_{j-1} >= n/3')
            upd('virt_in_over_n_j>1', ins_[j] / n)
            upd('Wjm1_over_n', Wm1 / n)
        upd('virt_side_over_n', max(ins_[j], outs[j]) / n)
        res.update(kind='virt', x=x, z=cj[0], cx=c0, cz=cj, ins=ins_[j], out=outs[j], virt=(c0[1], cj[1]),
                   cyc=tpath(par, x, cj[0]), seed=(x, c0[1] + 1), j=j, m=m, Fsize=len(Fc))
        if fid[c0] != fid[cj]:
            raise Fail('corners in different faces')
    res['st'] = st; res['mx'] = mx
    if res['x'] == res['z']:
        raise Fail('x == z')
    if 3 * max(res['ins'], res['out']) > 2 * n:
        raise Fail('unbalanced by marks: %d %d of %d' % (res['ins'], res['out'], n))
    # independent count of the final separator
    ci, co = sides_indep(V, rot, res['cyc'], res['virt'], res['seed'])
    if (ci, co) != (res['ins'], res['out']):
        raise Fail('final sides indep %s vs marks %s' % ((ci, co), (res['ins'], res['out'])))
    if 3 * max(ci, co) > 2 * n:
        raise Fail('UNBALANCED %d %d of %d' % (ci, co, n))
    if len(res['cyc']) > 2 * h + 1:
        raise Fail('|S| > 2h+1')
    if len(set(res['cyc'])) != len(res['cyc']):
        raise Fail('path not simple')
    if res['kind'] == 'real' and frozenset((res['x'], res['z'])) not in ends:
        raise Fail('real closing edge not a chord')
    return res


def random_virtual_marks(V, rot, idx, par, r, k, rng, tries=10):
    """marks lemma on random virtual chords between two corners of one face (distinct
    vertices), both arcs, against sides_indep. Returns the number of checks."""
    n = len(V)
    it = tour(rot, idx, par, r, k); L = len(it)
    pref = [0] * (L + 1)
    for q, t in enumerate(it):
        pref[q + 1] = pref[q] + (t[0] == 'm')
    TOT = pref[L]
    pos = {(t[1], t[2]): q for q, t in enumerate(it) if t[0] == 'c'}
    fid, faces = corner_faces(rot, idx)
    cand = [f for f in faces if len({v for v, _ in f}) >= 2]
    done = 0
    for _ in range(tries):
        f = rng.choice(cand)
        a = rng.choice(f); b = rng.choice(f)
        if a[0] == b[0]:
            continue
        x, z = a[0], b[0]
        P = len(tpath(par, x, z))
        pa, pb = pos[a], pos[b]
        m1 = pref[pb] - pref[pa] if pb >= pa else TOT - (pref[pa] - pref[pb])
        m2 = TOT - m1
        for mm, (ci_exp) in ((m1, 'a'), (m2, 'b')):
            tw = mm - P + 1
            if tw < 0 or tw % 2:
                raise Fail('virtual marks parity')
        i1 = (m1 - P + 1) // 2; i2 = (m2 - P + 1) // 2
        if i1 + i2 + P != n:
            raise Fail('virtual marks sum')
        ci, co = sides_indep(V, rot, tpath(par, x, z), (a[1], b[1]), (x, a[1] + 1))
        if (ci, co) != (i1, i2):
            raise Fail('random virtual marks lemma %s vs %s' % ((ci, co), (i1, i2)))
        done += 2
    return done


def fan_all(V, rot, idx, par, r, k, indep=True):
    """generalised check, independent of the thresholds: for EVERY face F and EVERY vertex x with
    exactly one corner in F, walk around F and check the marks lemma for each kappa_j (against
    sides_indep), the step identity, and the step bounds in_j <= in_{j-1}+1 (tree side) and
    in_j <= in_{j-1} + W' - 1 (chord, W' = closed region of the skipped side). Also checks that
    every face has a vertex with one corner. Returns number of steps checked."""
    n = len(V)
    it = tour(rot, idx, par, r, k); L = len(it)
    pref = [0] * (L + 1)
    for q, t in enumerate(it):
        pref[q + 1] = pref[q] + (t[0] == 'm')
    TOT = pref[L]
    pos = {(t[1], t[2]): q for q, t in enumerate(it) if t[0] == 'c'}
    fid, faces = corner_faces(rot, idx)
    def am(p, q):
        return pref[q] - pref[p] if q >= p else TOT - (pref[p] - pref[q])
    steps = 0
    for Fc in faces:
        cnt = collections.Counter(v for v, _ in Fc)
        ones = [v for v in cnt if cnt[v] == 1]
        if not ones:
            raise Fail('fan_all: face without a one-corner vertex')
        for x in ones:
            c0 = [c for c in Fc if c[0] == x][0]
            s = Fc.index(c0); walk = Fc[s:] + Fc[:s]
            keys = [(pos[c] - pos[c0]) % L for c in walk]
            if keys != sorted(keys):
                raise Fail('fan_all: walk not in gamma order')
            p0 = pos[c0]; pin = 0; pP = 1
            for j in range(1, len(walk)):
                cj = walk[j]; w = cj[0]
                P = len(tpath(par, x, w)); mm = am(p0, pos[cj])
                tw = mm - P + 1
                if tw < 0 or tw % 2:
                    raise Fail('fan_all parity')
                i = tw // 2
                if indep:
                    ci, co = sides_indep(V, rot, tpath(par, x, w), (c0[1], cj[1]), (x, c0[1] + 1))
                    if ci != i or co != n - P - i:
                        raise Fail('fan_all marks lemma')
                pa, pb = pos[walk[j - 1]], pos[cj]
                seg = [it[(pa + t) % L] for t in range(1, (pb - pa) % L)]
                if len(seg) == 1 and seg[0][0] == 'm':
                    if not (i <= pin + 1 <= pin + pP):
                        raise Fail('fan_all tree step')
                else:
                    a_, b_ = seg[0][1], seg[0][2]
                    if seg[0][0] != 'a' or seg[-1][0] != 'a' or (seg[-1][1], seg[-1][2]) != (b_, a_):
                        raise Fail('fan_all step type')
                    Te = len(tpath(par, a_, b_))
                    ms = am((pa + 1) % L, (pb - 1) % L)
                    te = ms - Te + 1
                    if te < 0 or te % 2:
                        raise Fail('fan_all parity chord')
                    Wp = te // 2 + Te
                    d1, d2, d3 = pP - 1, Te - 1, P - 1
                    if 2 * i != 2 * pin + d1 + 2 * (Wp - Te) + d2 - d3:
                        raise Fail('fan_all identity')
                    if not (i <= pin + Wp + min(d1, d2) - d2 - 1):
                        raise Fail('fan_all chord bound')
                    if j == 1 and i != Wp - Te:
                        raise Fail('fan_all in_1')
                pin, pP = i, P
                steps += 1
            # last step back to c0: out of kappa_m is the skipped side of the last step
    return steps
