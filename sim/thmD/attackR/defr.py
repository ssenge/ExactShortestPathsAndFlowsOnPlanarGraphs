"""Definition R (repaired G^_l) and Table R, built from the text of GHAT_REPAIR.md only.

cuts: list of dicts dict(z=vertex, i=corner index, mode='L'|'R', role='s'|'t').
The endpoint edge of a cut is the flank named by its mode: edge of r_z(i) (L) or r_z(i+1) (R).
I: set of incised edge ids (I_l).  cuts=[] and I=set() gives G^_0.

variant flags (negative controls), all default off:
  no_opt2   : never use option (ii)
  all_opt2  : option (ii) on every incised dart
  xswap     : swap the two orders at X(c*)
  host_head : host incised pair {(d,1),(rev d,2)} at head(d) instead of tail(d)
  no_reroute: keep the E_C end of x*'s pair at D(c*) (no repair (b) at c*), rotation unchanged
"""
import collections

PARTNER = (0, 2, 1)


def partner(x):
    d, l = x
    return (d ^ 1, PARTNER[l])


class GH:
    pass


def G_ep_incised(emb, c, mu, I):
    d = emb.din(c) if mu == 'L' else emb.dout(c)
    return (d >> 1) in I


def build(emb, I, cuts, var=frozenset()):
    I = set(I)
    G = GH()
    G.emb, G.I, G.cuts, G.var = emb, I, cuts, var
    inc = lambda d: (d >> 1) in I
    # ---- R1 tokens and pairs
    toks = []
    for d in range(2 * emb.m):
        if inc(d):
            toks += [(d, 1), (d, 2)]
        else:
            toks.append((d, 0))
    G.toks = toks
    pairs = []
    for e in range(emb.m):
        d = 2 * e
        if e in I and 'swap_pairs' in var:
            pairs.append(((d, 1), (d ^ 1, 1)))
            pairs.append(((d, 2), (d ^ 1, 2)))
        elif e in I:
            pairs.append(((d, 1), (d ^ 1, 2)))
            pairs.append(((d, 2), (d ^ 1, 1)))
        else:
            pairs.append(((d, 0), (d ^ 1, 0)))
    G.pairs = pairs
    # ---- cut corners and endpoint edges
    cutc = {}
    ep = {}
    for cu in cuts:
        c = (cu['z'], cu['i'] % emb.deg(cu['z']))
        assert c not in cutc
        cutc[c] = cu['mode']
        epd = emb.r(c[0], c[1]) if cu['mode'] == 'L' else emb.r(c[0], c[1] + 1)
        ep[cu['role']] = epd >> 1
        cu['_c'] = c
        cu['_e'] = epd >> 1
    G.cutc = cutc
    G.e0 = ep.get('s')
    G.elast = ep.get('t')
    # ---- R2 pieces
    pieces = []      # list of dict(face, toks, cyclic)
    piece_of = {}
    for f, cyc in enumerate(emb.faces):
        seq = []
        for d in cyc:
            if inc(d):
                seq += [(d, 1), 'CUT', (d, 2)]
            else:
                seq.append((d, 0))
            if emb.eta(d) in cutc:
                seq.append('CUT')
        cutpos = [k for k, x in enumerate(seq) if x == 'CUT']
        if not cutpos:
            pieces.append(dict(face=f, toks=list(seq), cyclic=True))
            continue
        k0 = cutpos[0]
        rot_ = seq[k0 + 1:] + seq[:k0 + 1]   # starts right after a cut, ends with a cut
        cur = []
        for x in rot_:
            if x == 'CUT':
                assert cur, "empty piece"
                pieces.append(dict(face=f, toks=cur, cyclic=False))
                cur = []
            else:
                cur.append(x)
        assert not cur
    for pi, P in enumerate(pieces):
        for x in P['toks']:
            piece_of[x] = pi
    G.pieces, G.piece_of = pieces, piece_of
    # ---- R3 vertices
    V = {}
    owner = {}

    def addv(key, v):
        V[key] = len(V)
        owner[key] = v
    for v in range(emb.n):
        addv(('S', v), v)
    for v in range(emb.n):
        for i in range(emb.deg(v)):
            c = (v, i)
            addv(('D', v, i), v)
            if inc(emb.din(c)):
                addv(('L', v, i), v)
            if inc(emb.dout(c)):
                addv(('R', v, i), v)
    for c in cutc:
        addv(('X',) + c, c[0])
    G.V, G.owner = V, owner
    # ---- R4 E_R
    alpha, beta = {}, {}
    for (d, l) in toks:
        tc, hc = emb.tau(d), emb.eta(d)
        if l == 0:
            alpha[(d, l)], beta[(d, l)] = ('D',) + tc, ('D',) + hc
        elif l == 1:
            alpha[(d, l)], beta[(d, l)] = ('D',) + tc, ('L',) + hc
        else:
            alpha[(d, l)], beta[(d, l)] = ('R',) + tc, ('D',) + hc
    moved = {}  # cut corner -> (token, 'a'|'b')
    for c, mu in list(cutc.items()):
        if 'literal_D1' in var and G_ep_incised(emb, c, mu, I):
            continue
        if mu == 'L':
            a = emb.din(c)
            x = (a, 2) if inc(a) else (a, 0)
            assert beta[x] == ('D',) + c
            beta[x] = ('X',) + c
            moved[c] = (x, 'b')
        else:
            b = emb.dout(c)
            x = (b, 1) if inc(b) else (b, 0)
            assert alpha[x] == ('D',) + c
            alpha[x] = ('X',) + c
            moved[c] = (x, 'a')
    G.alpha, G.beta, G.moved = alpha, beta, moved
    G.moved_tok = {x for (x, _) in moved.values()}
    # ---- edges: list of (end0 key, end1 key, typ, info)
    E = []
    ER = {}
    for x in toks:
        ER[x] = len(E)
        E.append((alpha[x], beta[x], 'R', x))
    ES = {}
    for v in range(emb.n):
        for i in range(emb.deg(v)):
            ES[('sd', v, i)] = len(E)
            E.append((('S', v), ('D', v, i), 'S', None))
            if ('L', v, i) in V:
                ES[('dl', v, i)] = len(E)
                E.append((('D', v, i), ('L', v, i), 'S', None))
            if ('R', v, i) in V:
                ES[('dr', v, i)] = len(E)
                E.append((('D', v, i), ('R', v, i), 'S', None))
    for c in cutc:
        ES[('dx',) + c] = len(E)
        E.append((('D',) + c, ('X',) + c, 'S', None))

    # ---- R6 E_C
    def tail(x):
        return emb.tl[x[0]]

    def att(h, x):
        return alpha[x] if tail(x) == h else beta[x]

    host = {}
    ECof = {}   # token -> (edge id, end)
    for (x, y) in pairs:
        e = x[0] >> 1
        if x[1] != 0:
            # incised: pair {(d,1),(rev d,2)} hosted at tail(d)
            d1 = x[0] if x[1] == 1 else y[0]
            if 'swap_pairs' in var:
                d1 = x[0]
            h = emb.tl[d1] if 'host_head' not in var else emb.tl[d1 ^ 1]
        else:
            u, w = emb.ends[e]
            sv = cuts[0]['z'] if cuts and cuts[0]['role'] == 's' else None
            tv = None
            for cu in cuts:
                if cu['role'] == 's':
                    sv = cu['z']
                else:
                    tv = cu['z']
            if G.e0 is not None and e == G.e0:
                h = w if u == sv else u
            elif G.elast is not None and e == G.elast:
                h = w if u == tv else u
            else:
                h = min(u, w)
        a0, a1 = att(h, x), att(h, y)
        if 'no_reroute' in var:
            # literal [18]: E_C at the rim, ignoring moved tokens
            a0 = ('D',) + (emb.tau(x[0]) if tail(x) == h else emb.eta(x[0]))
            a1 = ('D',) + (emb.tau(y[0]) if tail(y) == h else emb.eta(y[0]))
        eid = len(E)
        E.append((a0, a1, 'C', (x, y)))
        host[(x, y)] = h
        ECof[x] = (eid, 0)
        ECof[y] = (eid, 1)
    G.E, G.host, G.ECof, G.ER, G.ES = E, host, ECof, ER, ES
    return G


# ------------------------------------------------------------------ Table R
def option(G, d):
    """'i' or 'ii' for an incised dart d."""
    var = G.var
    if 'all_opt2' in var:
        return 'ii'
    if 'no_opt2' in var:
        return 'i'
    emb = G.emb
    c = emb.tau(d)
    if G.cutc.get(c) == 'R' and emb.dout(c) == d and (d >> 1) in G.I:
        return 'ii'
    return 'i'


def table_r(G):
    """rotation: key -> list of (edge id, end)."""
    emb, I, E = G.emb, G.I, G.E
    inc = lambda d: (d >> 1) in I
    rot = {}
    for v in range(emb.n):
        rot[('S', v)] = [(G.ES[('sd', v, i)], 0) for i in range(emb.deg(v))]
    pair_of = {}
    for (x, y) in G.pairs:
        pair_of[x] = (x, y)
        pair_of[y] = (x, y)
    for v in range(emb.n):
        for i in range(emb.deg(v)):
            c = (v, i)
            a, b = emb.din(c), emb.dout(c)
            ta = (a, 2) if inc(a) else (a, 0)     # token of a ending at D(c)
            tb = (b, 1) if inc(b) else (b, 0)     # token of b starting at D(c)
            ent = [(G.ES[('sd', v, i)], 1)]
            # C_A
            CA = None
            if G.host[pair_of[ta]] == v:
                eid, end = G.ECof[ta]
                if G.E[eid][end] == ('D',) + c:
                    CA = (eid, end)
            CB = None
            if G.host[pair_of[tb]] == v:
                eid, end = G.ECof[tb]
                if G.E[eid][end] == ('D',) + c:
                    CB = (eid, end)

            def tokent(x, endname):
                """entry of token x at D(c); moved token -> E_S edge to X."""
                if x in G.moved_tok and G.moved.get(c, (None,))[0] == x:
                    return (G.ES[('dx',) + c], 0)
                return (G.ER[x], 1 if endname == 'b' else 0)
            if not inc(a):
                A = [tokent(ta, 'b')]
            else:
                if option(G, a) == 'i':
                    A = [tokent(ta, 'b'), (G.ES[('dl', v, i)], 0)]
                else:
                    A = [(G.ES[('dl', v, i)], 0), tokent(ta, 'b')]
            if not inc(b):
                B1, B2 = tokent(tb, 'a'), None
            else:
                if option(G, b) == 'i':
                    B1, B2 = (G.ES[('dr', v, i)], 0), tokent(tb, 'a')
                else:
                    B1, B2 = tokent(tb, 'a'), (G.ES[('dr', v, i)], 0)
            lst = ent
            if CA is not None:
                lst.append(CA)
            lst += A
            if B2 is not None:
                lst.append(B2)
            lst.append(B1)
            if CB is not None:
                lst.append(CB)
            rot[('D', v, i)] = lst
            if ('L', v, i) in G.V:
                rot[('L', v, i)] = [(G.ES[('dl', v, i)], 1), (G.ER[(a, 1)], 1)]
            if ('R', v, i) in G.V:
                rot[('R', v, i)] = [(G.ES[('dr', v, i)], 1), (G.ER[(b, 2)], 0)]
    for c, mu in G.cutc.items():
        x, which = G.moved[c]
        xe = (G.ER[x], 1 if which == 'b' else 0)
        C = None
        eid, end = G.ECof[x]
        if G.E[eid][end] == ('X',) + c:
            C = (eid, end)
        lst = [(G.ES[('dx',) + c], 1)]
        if mu == 'L':
            order = [C, xe] if 'xswap' not in G.var else [xe, C]
        else:
            order = [xe, C] if 'xswap' not in G.var else [C, xe]
        lst += [z for z in order if z is not None]
        rot[('X',) + c] = lst
    return rot


def rot_consistent(G, rot):
    """every edge end listed exactly once, at its own vertex."""
    seen = collections.Counter()
    for key, lst in rot.items():
        for (eid, end) in lst:
            if G.E[eid][end] != key:
                return False, ('wrong_vertex', key, eid, end, G.E[eid])
            seen[(eid, end)] += 1
    for eid in range(len(G.E)):
        for end in (0, 1):
            if seen[(eid, end)] != 1:
                return False, ('count', eid, end, seen[(eid, end)], G.E[eid])
    if set(rot) != set(G.V):
        return False, ('vertex_set', set(G.V) ^ set(rot))
    return True, None


def euler(G, rot):
    """V - E + F for the rotation system and number of components."""
    nxt = {}
    for key, lst in rot.items():
        k = len(lst)
        for j, h in enumerate(lst):
            nxt[h] = lst[(j + 1) % k]
    seen = set()
    F = 0
    for h in nxt:
        if h in seen:
            continue
        F += 1
        x = h
        while x not in seen:
            seen.add(x)
            eid, end = x
            x = nxt[(eid, 1 - end)]
    # components
    par = {k: k for k in G.V}

    def fd(a):
        while par[a] != a:
            par[a] = par[par[a]]
            a = par[a]
        return a
    for (a, b, t, info) in G.E:
        par[fd(a)] = fd(b)
    ncomp = len({fd(k) for k in G.V})
    return len(G.V) - len(G.E) + F, ncomp


# ------------------------------------------------------------------ property checks
def check_props(G, bad, full=True):
    """properties (1), (2), (4) and Claim 1. bad(name, info) records failures."""
    emb = G.emb
    # Claim 1: E_R degrees
    erdeg = collections.Counter()
    for (a, b, t, info) in G.E:
        if t == 'R':
            erdeg[a] += 1
            erdeg[b] += 1
    for key in G.V:
        k = key[0]
        want = {'S': 0, 'L': 1, 'R': 1, 'X': 1}.get(k)
        if k == 'D':
            want = 1 if (key[1], key[2]) in G.cutc else 2
        if erdeg[key] != want:
            bad('claim1_ER_degree', (key, erdeg[key], want))
    # (1): pieces -> paths/cycles
    vpiece = {}
    for pi, P in enumerate(G.pieces):
        T = P['toks']
        k = len(T)
        for j in range(k - 1):
            if G.beta[T[j]] != G.alpha[T[j + 1]]:
                bad('P1_link', (pi, T[j], T[j + 1]))
        if P['cyclic']:
            if G.beta[T[-1]] != G.alpha[T[0]]:
                bad('P1_cycle_close', pi)
            verts = [G.alpha[x] for x in T]
            if len(set(verts)) != k:
                bad('P1_cycle_repeat', pi)
        else:
            verts = [G.alpha[T[0]]] + [G.beta[x] for x in T]
            if len(set(verts)) != k + 1:
                bad('P1_path_repeat', (pi, T))
        for w in verts:
            if w in vpiece and vpiece[w] != pi:
                bad('P1_shared_copy', (w, vpiece[w], pi))
            vpiece[w] = pi
        # every vertex of p(f) has a copy on p^(f)
        pv = {emb.tl[x[0]] for x in T} | {emb.head(x[0]) for x in T}
        cv = {G.owner[w] for w in verts}
        if pv != cv:
            bad('P1_vertex_copy', (pi, pv, cv))
    for key in G.V:
        if key[0] != 'S' and key not in vpiece:
            bad('P1_copy_off_paths', key)
    G.vpiece = vpiece
    # (2): E_C
    ncpairs = 0
    for eid, (a0, a1, t, info) in enumerate(G.E):
        if t != 'C':
            continue
        ncpairs += 1
        x, y = info
        h = G.host[info]
        if G.owner[a0] != h or G.owner[a1] != h:
            bad('P2_not_host_copies', (info, a0, a1, h))
        if vpiece.get(a0) != G.piece_of[x] or vpiece.get(a1) != G.piece_of[y]:
            bad('P2_wrong_paths', (info, a0, a1))
        if a0 == a1:
            moved_here = any(c[0] == h and z in (x, y) for c, (z, _) in G.moved.items())
            if emb.deg(h) != 1 or moved_here:
                bad('P2_selfloop_condition', (info, h))
            if G.piece_of[x] != G.piece_of[y]:
                bad('P2_selfloop_not_dual_loop', info)
    if ncpairs != len(G.pairs):
        bad('P2_count', (ncpairs, len(G.pairs)))
    if not full:
        return
    # (4): copies, distances
    cnt = collections.Counter(G.owner[k] for k in G.V)
    term = {cu['z'] for cu in G.cuts}
    for v in range(emb.n):
        lim = 3 * emb.deg(v) + 1 + (1 if v in term else 0)
        if cnt[v] > lim:
            bad('P4_copies', (v, cnt[v], lim))
    if len(G.V) > 6 * emb.m + emb.n + 2:
        bad('P4_total', len(G.V))
    adj = collections.defaultdict(list)
    adjRS = collections.defaultdict(list)
    for (a, b, t, info) in G.E:
        adj[a].append(b)
        adj[b].append(a)
        if t != 'C':
            adjRS[a].append(b)
            adjRS[b].append(a)

    def bfs(src, A, lim):
        dist = {src: 0}
        q = [src]
        for x in q:
            if dist[x] >= lim:
                continue
            for y in A[x]:
                if y not in dist:
                    dist[y] = dist[x] + 1
                    q.append(y)
        return dist
    for v in range(emb.n):
        dS = bfs(('S', v), adjRS, 4)
        for key in G.V:
            if G.owner[key] == v and key[0] != 'S':
                if key not in dS or dS[key] > 2:
                    bad('P4_copy_far', key)
        nb = {emb.head(d) for d in emb.rot[v]}
        for w in nb:
            if ('S', w) not in dS:
                bad('P4_edge_hops_RS', (v, w))


def check_planar(G, bad, use_nx=False):
    rot = table_r(G)
    ok, why = rot_consistent(G, rot)
    if not ok:
        bad('P3_rot_inconsistent', why)
        return False
    chi, nc = euler(G, rot)
    if nc != 1:
        bad('P3_disconnected', nc)
    if chi != 2 * nc:
        bad('P3_euler', chi)
        res = False
    else:
        res = True
    if use_nx:
        import networkx as nx
        H = nx.Graph()
        for (a, b, t, info) in G.E:
            if a != b:
                H.add_edge(a, b)
        if not nx.check_planarity(H)[0]:
            bad('P3_nx_nonplanar', None)
    return res


# ------------------------------------------------------------------ token graph
def token_components(G):
    """components of G*_l: piece index -> component id."""
    par = list(range(len(G.pieces)))

    def fd(a):
        while par[a] != a:
            par[a] = par[par[a]]
            a = par[a]
        return a
    for (x, y) in G.pairs:
        par[fd(G.piece_of[x])] = fd(G.piece_of[y])
    return [fd(i) for i in range(len(G.pieces))]
