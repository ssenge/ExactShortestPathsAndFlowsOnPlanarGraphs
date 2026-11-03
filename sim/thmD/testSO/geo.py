"""Topological test of the curve model of LEMMA_O.md (Claims 3 to 9), at every incision.

J = J_Q = C_Q u gamma[q_0, q_1] meets the closed disc of a face h in at most one cross-cut
(Claim 3c): in a face off P, the chord ch(g) of the internal node g of Q from c(u) to c(w); in p_t
with min(x,y) < t < max(x,y), gamma_t from its entry to its exit; in p_x (x != y),
ch(g_x) u gamma_x[q_0, exit] (y > x) or ch(g_x) u gamma_x[entry, q_0] (y < x); in p_y the
same with c(eps_1); in p_x = p_y, ch(g_x) u gamma_x[q_0,q_1] u ch(g_y), from c(eps_0) to
c(eps_1). By T2 the disc minus the cross-cut has two components, fixed by the two boundary
arcs between its ends, wherever the cross-cut runs inside the disc. J meets a strip S_e only in
cl(e), for e on Q or e = e_k with min(x,y) < k <= max(x,y), and no vertex disc. So the
components of S^2 minus J are computed exactly from face regions, strips (split into two halves
at cl(e) when cl(e) lies in J) and vertex discs, glued along token segments, half segments and
corner arcs. Checks (flags):
  G_two_sides      S^2 minus J has exactly two components (J is a simple closed curve)
  G_s_t_apart      B_s and B_t lie on different sides (Lo(J) holds the start of gamma at c*_s)
  G_piece_split    every piece of A^Q lies on one side (all its token segments)   [Claim 5]
  G_comp_mixed     every component of A^Q lies on one side                         [Claim 5]
  G_P_side         P-pieces off the ends: t < x (t < y) on Lo, t > x (t > y) on Hi  [Claim 6a]
  G_end_new        a split end: part below the cut on Lo, above it on Hi            [Claim 6b]
  G_end_old        an unsplit end: on Hi if its old token is on P_a, Lo if on P_b [Claim 6b,c]
  G_bound_offQ     tokens of P_a (P_b) off Q on Lo (Hi)                            [Claim 8b]
  G_bound_onQ      tokens of P_a (P_b) on Q on Hi (Lo)                             [Claim 8c]
  G_newedge        the two pairs of a new edge of Q on different sides             [Claim 7a]
  G_child_side     the driver's low child on Lo(J), its high child on Hi(J)        [names, §4]
"""
import collections


class Geo:
    def __init__(self, emb, s, t, cnt, flag):
        self.emb = emb
        self.s, self.t = s, t
        self.cnt = cnt
        self.flag = flag
        self.idx = {}
        for h, cyc in enumerate(emb.faces):
            for k, d in enumerate(cyc):
                self.idx[d] = k
        self.pf = None
        self.side_of = {}

    def set_P(self, ctx, Pn, Pe):
        self.pf = [ctx.store[x].face for x in Pn]
        self.pdart = {}
        for k, (la, lb) in enumerate(Pe):
            self.pdart[k + 1] = {self.pf[k]: la[0], self.pf[k + 1]: lb[0]}

    def pos_tok(self, ld):
        d, lab = ld
        return self.idx[d] + (0.5, 0.25, 0.75)[lab]

    def pos_cut(self, d):
        return self.idx[d] + 0.5

    def __call__(self, A, i, Pn_, Pe_, Qn, Qe, xt, yt, i1, i2, ov, pieces, newnodes, comp, stats, level):
        emb = self.emb
        if self.pf is None:
            self.flag('G_no_P')
            return
        m = len(self.pf) - 1
        cnt = self.cnt
        cnt['G_inc'] += 1

        def entry(t):
            return self.pos_cut(self.pdart[t][self.pf[t]]) if t >= 1 else None

        def exit_(t):
            return self.pos_cut(self.pdart[t + 1][self.pf[t]]) if t < m else None
        cc = {}
        lo, hi = min(xt, yt), max(xt, yt)
        for t in range(lo + 1, hi):
            cc[self.pf[t]] = (entry(t), exit_(t))
        e0 = self.pos_cut(Qe[0][0][0])
        e1 = self.pos_cut(Qe[-1][1][0])
        fx, fy = self.pf[xt], self.pf[yt]
        if xt == yt:
            cc[fx] = (e0, e1)
        else:
            cc[fx] = (e0, exit_(xt) if yt > xt else entry(xt))
            cc[fy] = (e1, entry(yt) if xt < yt else exit_(yt))
        for k in range(1, len(Qn) - 1):
            g = A.nodes[Qn[k]]
            if g.face in cc:
                self.flag('G_face_twice', (A.aid, g.face))
            cc[g.face] = (self.pos_cut(Qe[k - 1][1][0]), self.pos_cut(Qe[k][0][0]))
        for h, (a, b) in cc.items():
            if a is None or b is None or a == b:
                self.flag('G_bad_crosscut', (A.aid, h, a, b))
                return
        Jedges = {la[0] >> 1 for la, lb in Qe}
        for k in range(lo + 1, hi + 1):
            Jedges.add(next(iter(self.pdart[k].values())) >> 1)
        par = {}

        def f(x):
            par.setdefault(x, x)
            while par[x] != x:
                par[x] = par[par[x]]
                x = par[x]
            return x

        def u_(x, y):
            par[f(x)] = f(y)

        def region(h, p):
            if h not in cc:
                return ('F', h, 0)
            a, b = cc[h]
            L = len(emb.faces[h])
            return ('F', h, 1 if (p - a) % L < (b - a) % L else 2)
        for h, cyc in enumerate(emb.faces):
            for d in cyc:
                e = d >> 1
                k = self.idx[d]
                u_(region(h, k + 0.95), ('V', emb.head(d)))       # corner after d, at head(d)
                if e in Jedges:
                    t0 = 0 if d % 2 == 0 else 1                   # half of S_e at tail(d)
                    u_(region(h, k + 0.25), ('S', e, t0))
                    u_(region(h, k + 0.75), ('S', e, 1 - t0))
                else:
                    u_(region(h, k + 0.5), ('S', e))
        for e, (a, b) in enumerate(emb.ends):
            if e in Jedges:
                u_(('S', e, 0), ('V', a))
                u_(('S', e, 1), ('V', b))
            else:
                u_(('S', e), ('V', a))
                u_(('S', e), ('V', b))
        roots = {f(x) for x in list(par)}
        if len(roots) != 2:
            self.flag('G_two_sides', (A.aid, len(roots)))
            return
        LO = f(('V', self.s))
        if f(('V', self.t)) == LO:
            self.flag('G_s_t_apart', A.aid)
            return
        cnt['G_ok_two_sides'] += 1
        side = {}
        for z, Z in newnodes.items():
            ss = {'L' if f(region(Z.face, self.pos_tok(ld))) == LO else 'H' for ld in Z.seq}
            if len(ss) != 1:
                self.flag('G_piece_split', (A.aid, z))
                continue
            side[z] = ss.pop()
        self.side_of[A.aid] = side
        bycomp = collections.defaultdict(set)
        for z, sd in side.items():
            bycomp[comp[z]].add(sd)
        if any(len(v) > 1 for v in bycomp.values()):
            self.flag('G_comp_mixed', A.aid)
        X0, Y1 = Qn[0], Qn[-1]
        Xp, Yp = set(pieces.get(X0, [X0])), set(pieces.get(Y1, [Y1]))
        for z, Z in newnodes.items():
            if Z.anc[0] != 'p' or z in Xp or z in Yp:
                continue
            ref = xt if Z.anc[2] == 0 else yt
            want = 'L' if Z.anc[1] < ref else 'H'
            cnt['G_P_checked'] += 1
            if side.get(z) != want:
                self.flag('G_P_side', (A.aid, Z.anc, xt, yt, side.get(z)))
        PaL = set() if A.left is None else {ld for e in A.left['edges'] for ld in e}
        PbL = set() if A.right is None else {ld for e in A.right['edges'] for ld in e}
        for Xid, tok in ((X0, Qe[0][0]), (Y1, Qe[-1][1])):
            X = A.nodes[Xid]
            if Xid in pieces:
                ps = pieces[Xid]
                lowp, highp = (ps[0], ps[1]) if X.lowfirst else (ps[1], ps[0])
                cnt['G_end_new'] += 1
                if side.get(lowp) != 'L' or side.get(highp) != 'H':
                    self.flag('G_end_new', (A.aid, X.anc))
            else:
                want = 'H' if tok in PaL else ('L' if tok in PbL else None)
                cnt['G_end_old'] += 1
                if want is None or side.get(Xid) != want:
                    self.flag('G_end_old', (A.aid, X.anc, want, side.get(Xid)))
        ldpiece = {}
        for z, Z in newnodes.items():
            for ld in Z.seq:
                ldpiece[ld] = z
        Qlds = {ld for e in Qe for ld in e}
        for L_, want_off, want_on, nm in ((PaL, 'L', 'H', 'a'), (PbL, 'H', 'L', 'b')):
            for ld in L_:
                z = ldpiece.get(ld)
                if z is None:
                    continue
                want = want_on if ld in Qlds else want_off
                cnt['G_bound_checked'] += 1
                if side.get(z) != want:
                    self.flag('G_bound_' + ('onQ' if ld in Qlds else 'offQ'), (A.aid, nm, ld, side.get(z)))
        for la, lb in Qe:
            if la[1] == 0:
                cnt['G_newedge_checked'] += 1
                if side.get(ldpiece.get((la[0], 1))) == side.get(ldpiece.get((la[0], 2))):
                    self.flag('G_newedge', A.aid)

    def child(self, A, C, sidename, jj, kk, i, i1, i2, xt, yt, stats):
        side = self.side_of.get(A.aid)
        if side is None:
            return
        want = 'L' if sidename == 'l' else 'H'
        self.cnt['G_child_checked'] += 1
        if any(side.get(z) != want for z in C.nodes):
            self.flag('G_child_side', (A.aid, sidename))
