"""Repaired G^_l built from the formal definition in notes/GHAT_REPAIR.md (Def R), written
independently of thmD.build_ghat, plus an explicit rotation system (Lemma R (3)).

Notation (all indices mod deg v):
  corner c=(v,i) lies between darts r_v(i) and r_v(i+1);
  in(c)  = rev r_v(i)   (dart entering v just before c in its face walk)
  out(c) = r_v(i+1)     (dart leaving v just after c)
  tau(d) = corner with out(c)=d (tail corner), eta(d) = corner with in(c)=d (head corner).
Tokens: (d,0) for d of an edge not in I; (d,1),(d,2) for d of an edge in I.
  alpha/beta = attachment at tail/head:
  (d,0): D(tau d), D(eta d);  (d,1): D(tau d), L(eta d);  (d,2): R(tau d), D(eta d).
Repair (a): at each cut corner c* (mode L/R), the e0-side token attached to D(c*) is
  re-attached to the fresh copy X(c*).
Repair (b): the E_C edge of a token pair hosted at h joins att_h(x), att_h(y).
"""
import collections, os
NEG = os.environ.get("NEG", "")


def tau(emb, d):
    u = emb.tl[d]
    return (u, (emb.pos[d] - 1) % emb.deg(u))


def eta(emb, d):
    v = emb.tl[d ^ 1]
    return (v, emb.pos[d ^ 1])


def din(emb, c):
    v, i = c
    return emb.rot[v][i] ^ 1


def dout(emb, c):
    v, i = c
    return emb.rot[v][(i + 1) % emb.deg(v)]


def partner(x):
    d, l = x
    return (d ^ 1, (0, 2, 1)[l])


class FG:
    pass


def build_formal(emb, I, cuts):
    """cuts: list of dict(v=, ci=, mode='L'|'R') in the order [s-record, t-record]."""
    I = set(I)
    m = emb.m
    toks = []
    for d in range(2 * m):
        if (d >> 1) in I:
            toks += [(d, 1), (d, 2)]
        else:
            toks.append((d, 0))
    alpha, beta = {}, {}
    for (d, l) in toks:
        tc, hc = tau(emb, d), eta(emb, d)
        if l == 0:
            alpha[(d, l)], beta[(d, l)] = ('D',) + tc, ('D',) + hc
        elif l == 1:
            alpha[(d, l)], beta[(d, l)] = ('D',) + tc, ('L',) + hc
        else:
            alpha[(d, l)], beta[(d, l)] = ('R',) + tc, ('D',) + hc
    # repair (a)
    moved = {}   # corner -> (token, 'beta'|'alpha')
    for cu in cuts:
        c = (cu['v'], cu['ci'])
        if cu['mode'] == 'L':
            a = din(emb, c)
            x = (a, 2) if (a >> 1) in I else (a, 0)
            assert beta[x] == ('D',) + c
            beta[x] = ('X',) + c
            moved[c] = (x, 'beta')
        else:
            b = dout(emb, c)
            x = (b, 1) if (b >> 1) in I else (b, 0)
            assert alpha[x] == ('D',) + c
            alpha[x] = ('X',) + c
            moved[c] = (x, 'alpha')
    # vertices
    verts = set()
    for v in range(emb.n):
        verts.add(('S', v))
        for i in range(emb.deg(v)):
            c = (v, i)
            verts.add(('D',) + c)
            if (din(emb, c) >> 1) in I:
                verts.add(('L',) + c)
            if (dout(emb, c) >> 1) in I:
                verts.add(('R',) + c)
    for c in moved:
        verts.add(('X',) + c)
    # edges: (a, b, typ, info, endtok) ; endtok = (token at a-end, token at b-end) for E_C
    E = []
    ES_spoke, ES_leaf, ER_of = {}, {}, {}
    for v in range(emb.n):
        for i in range(emb.deg(v)):
            ES_spoke[(v, i)] = len(E)
            E.append((('S', v), ('D', v, i), 'S', None, None))
    for key in sorted(k for k in verts if k[0] in 'LRX'):
        c = key[1:]
        ES_leaf[key] = len(E)
        E.append((('D',) + c, key, 'S', None, None))
    for x in toks:
        ER_of[x] = len(E)
        E.append((alpha[x], beta[x], 'R', x, None))
    # E_C: host rule of [18] / thmD 'fixed'
    def att(x, h):
        d = x[0]
        if emb.tl[d] == h:
            return alpha[x]
        assert emb.tl[d ^ 1] == h
        return beta[x]
    ep_first = {}
    for cu in cuts:
        e0 = cu['e0']
        if e0 not in I and e0 not in ep_first:
            ep_first[e0] = cu['v']
    EC_of = {}   # (host, token) -> (edge id, end 0/1)
    pairs = []
    for e in range(m):
        u, v = emb.ends[e]
        d = 2 * e
        if e in I:
            pairs.append((((d, 1), (d ^ 1, 2)), u))
            pairs.append((((d, 2), (d ^ 1, 1)), v))
        else:
            if e in ep_first:
                h = v if ep_first[e] == u else u
            else:
                h = u if u < v else v
            pairs.append((((d, 0), (d ^ 1, 0)), h))
    for (x, y), h in pairs:
        k = len(E)
        E.append((att(x, h), att(y, h), 'C', (x, y), h))
        EC_of[(h, x)] = (k, 0)
        EC_of[(h, y)] = (k, 1)
    G = FG()
    G.verts, G.E, G.toks, G.alpha, G.beta, G.moved, G.pairs = verts, E, toks, alpha, beta, moved, pairs
    G.I, G.cuts = I, cuts
    G.ES_spoke, G.ES_leaf, G.ER_of, G.EC_of = ES_spoke, ES_leaf, ER_of, EC_of
    G.rot = rotation(emb, G)
    return G


def rotation(emb, G):
    """explicit rotation: vertex -> list of darts (2k leaves E[k][0], 2k+1 leaves E[k][1])."""
    I, moved = G.I, G.moved
    E = G.E
    # lens option per incised dart: 'ii' iff dart = out(c*) of an R-mode cut corner
    opt2 = set()
    for cu in G.cuts:
        if cu['mode'] == 'R':
            b = dout(emb, (cu['v'], cu['ci']))
            if (b >> 1) in I and NEG != 'noflip':
                opt2.add(b)
    if NEG == 'flipall':
        opt2 = {d for d in range(2 * emb.m) if (d >> 1) in I}
    rot = {}
    for v in range(emb.n):
        rot[('S', v)] = [2 * G.ES_spoke[(v, i)] for i in range(emb.deg(v))]
    for v in range(emb.n):
        for i in range(emb.deg(v)):
            c = (v, i)
            a, b = din(emb, c), dout(emb, c)
            mv = moved.get(c)
            # in-token at D(c) (head end of a)
            za = (a, 2) if (a >> 1) in I else (a, 0)
            zb = (b, 1) if (b >> 1) in I else (b, 0)
            if mv and mv[1] == 'beta':
                assert mv[0] == za
                za_item = 2 * G.ES_leaf[('X',) + c]
                ca = None
            else:
                za_item = 2 * G.ER_of[za] + 1
                ca = G.EC_of.get((v, za))
            if mv and mv[1] == 'alpha':
                assert mv[0] == zb
                zb_item = 2 * G.ES_leaf[('X',) + c]
                cb = None
            else:
                zb_item = 2 * G.ER_of[zb]
                cb = G.EC_of.get((v, zb))
            A = [za_item]
            if (a >> 1) in I:
                li = 2 * G.ES_leaf[('L',) + c]
                A = [za_item, li] if a not in opt2 else [li, za_item]
            B = [zb_item]
            if (b >> 1) in I:
                ri = 2 * G.ES_leaf[('R',) + c]
                # order listed is B2, B1 (B1 adjacent to chord C_B)
                B = [zb_item, ri] if b not in opt2 else [ri, zb_item]
            r = [2 * G.ES_spoke[c] + 1]
            if ca is not None:
                r.append(2 * ca[0] + ca[1])
            r += A + B
            if cb is not None:
                r.append(2 * cb[0] + cb[1])
            rot[('D',) + c] = r
            if ('L',) + c in G.verts:
                rot[('L',) + c] = [2 * G.ES_leaf[('L',) + c] + 1, 2 * G.ER_of[(a, 1)] + 1]
            if ('R',) + c in G.verts:
                rot[('R',) + c] = [2 * G.ES_leaf[('R',) + c] + 1, 2 * G.ER_of[(b, 2)]]
    for c, (x, side) in moved.items():
        v = c[0]
        es = 2 * G.ES_leaf[('X',) + c] + 1
        er = 2 * G.ER_of[x] + (1 if side == 'beta' else 0)
        ch = G.EC_of.get((v, x))
        chl = [] if ch is None else [2 * ch[0] + ch[1]]
        if NEG == 'xswap':
            side_r = 'alpha' if side == 'beta' else 'beta'
        else:
            side_r = side
        if side_r == 'beta':      # L mode
            rot[('X',) + c] = [es] + chl + [er]
        else:                   # R mode
            rot[('X',) + c] = [es, er] + chl
    return rot


def check_rotation(G):
    """returns (ok_perm, V, E, F, connected)."""
    E = G.E
    vid = {}
    for k in G.verts:
        vid[k] = len(vid)
    tailv = []
    for (a, b, *_rest) in E:
        tailv += [a, b]
    seen = collections.Counter()
    for v, r in G.rot.items():
        for d in r:
            if tailv[d] != v:
                return (False, 'dart %d not at %s' % (d, v))
            seen[d] += 1
    if set(seen) != set(range(2 * len(E))) or any(c != 1 for c in seen.values()):
        return (False, 'rotation not a permutation of darts')
    if set(G.rot) != set(G.verts):
        return (False, 'vertex set mismatch')
    pos = {}
    for v, r in G.rot.items():
        for i, d in enumerate(r):
            pos[d] = (v, i)
    seen = set()
    F = 0
    for d0 in range(2 * len(E)):
        if d0 in seen:
            continue
        F += 1
        d = d0
        while d not in seen:
            seen.add(d)
            v, i = pos[d ^ 1]
            r = G.rot[v]
            d = r[(i + 1) % len(r)]
    # connectivity
    par = {k: k for k in G.verts}

    def f(x):
        while par[x] != x:
            par[x] = par[par[x]]
            x = par[x]
        return x
    for (a, b, *_r) in E:
        par[f(a)] = f(b)
    conn = len({f(k) for k in G.verts}) == 1
    V = len(G.verts)
    return (True, V, len(E), F, conn)


def code_key(G, key):
    """map formal vertex names to thmD.build_ghat keys."""
    if key[0] != 'X':
        return key
    c = key[1:]
    x, side = G.moved[c]
    if (x[0] >> 1) in G.I:
        return key
    return ('L',) + c if side == 'beta' else ('R',) + c


def edge_multiset(G):
    out = collections.Counter()
    for (a, b, typ, info, _h) in G.E:
        ka, kb = code_key(G, a), code_key(G, b)
        if typ == 'C':
            info = frozenset(info)
        out[(frozenset([ka, kb]) if ka != kb else frozenset([ka]), typ, info)] += 1
    return out


def code_multiset(Gc):
    out = collections.Counter()
    for (a, b, typ, info, eid) in Gc.E:
        ka, kb = Gc.keys[a], Gc.keys[b]
        if typ == 'C':
            info = frozenset(info)
        out[(frozenset([ka, kb]) if ka != kb else frozenset([ka]), typ, info)] += 1
    return out


def pieces(emb, G):
    """pieces of the level cut structure, as lists of tokens, computed from faces directly."""
    cutc = {(cu['v'], cu['ci']) for cu in G.cuts}
    res = []
    for f, cyc in enumerate(emb.faces):
        seq = []   # tokens and 'CUT'
        for d in cyc:
            if (d >> 1) in G.I:
                seq += [(d, 1), 'CUT', (d, 2)]
            else:
                seq.append((d, 0))
            if eta(emb, d) in cutc:
                seq.append('CUT')
        if 'CUT' not in seq:
            res.append((f, True, seq))
            continue
        k = seq.index('CUT')
        seq = seq[k + 1:] + seq[:k + 1]
        cur = []
        for z in seq:
            if z == 'CUT':
                assert cur, 'empty piece'
                res.append((f, False, cur))
                cur = []
            else:
                cur.append(z)
        assert not cur
    return res
