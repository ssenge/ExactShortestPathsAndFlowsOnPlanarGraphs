"""Global test of the curve model of LEMMA_O.md: the invariant (I1) for K_l, at every level.

geo.py tests one incision curve J_Q at a time. This builds K_l itself, the union of gamma and of
the curves C_Q of all incisions of levels below l, with the construction of Claim 3:
  - gamma_t splits the disc of p_t into two halves (gamma starts at the corner cut c*_s and ends
    at c*_t, points of the corner arcs, so it does not separate);
  - an internal node g of Q (a face off P) gets the chord ch(g) from c(u) to c(w);
  - g_x gets the chord ch(g_x) from c(eps_0) to a point q_0 inside its gamma-part, in the 0-half
    of p_x, and g_y the chord ch(g_y) from c(eps_1) to q_1 inside its gamma-part, in the 1-half;
  - the strip of an edge of Q (and of every edge of P) is cut along cl(e).
Each disc (an off-P face, or a half of a face of P, whose boundary circle is the arc of the face
followed by gamma_t backwards) is cut by non-crossing chords, so two boundary points lie in one
region iff no chord separates them. The components of S^2 \\ K_l are glued from these regions,
the strips (two halves when cut) and the vertex discs, exactly as in geo.py.

Checks, for every live annulus A of level l (A_1 and every called child, leaves included):
  K_cross        a new chord crosses an earlier one (Claim 3a: ch(g) runs inside the slot of g)
  K_piece_split  the tokens of a piece lie in two regions of K_l (slots are well defined)
  K_half         a piece of p_t^sigma has a token outside the sigma-half of p_t     (I1b)
  K_gamma_part   the slot of a piece of p_t^sigma has not exactly one gamma-part  (I1b)
  K_cyclic_cut   a cyclic piece off P lies in a face that K_l cuts                 (I1a)
  K_slot_shared  two pieces of live annuli of level l have the same slot
  K_omega_split  the slots of the pieces of A lie in two components of S^2 \\ K_l   (I1c)
  K_omega_shared two live annuli of level l lie in one component of S^2 \\ K_l      (I1c)
  K_end_half     c(eps_0) is not on the 0-half of p_x, or c(eps_1) not on the 1-half of p_y
"""
import os
import random
import collections

NEG = os.environ.get('GEOK_NEG', '')   # negative controls: nocut, nochord, wrongq, flipq


class GeoK:
    def __init__(self, emb, cnt, flag):
        self.emb = emb
        self.cnt = cnt
        self.flag = flag
        self.idx = {}
        self.L = {}
        for h, cyc in enumerate(emb.faces):
            self.L[h] = len(cyc)
            for k, d in enumerate(cyc):
                self.idx[d] = k
        self.ch = collections.defaultdict(list)   # (h, sigma|None) -> [(a, b, level)]
        self.cut = {}                               # incised edge -> level (P: 0)
        self.anns = collections.defaultdict(list)   # level -> [Ann]
        self.rng = random.Random(1)
        self.ok = False

    # ------------------------------------------------------------ setup (from level1_ann)
    def set_level1(self, pf, pdart, da_s, da_t, A1):
        self.pf = pf
        self.onP = {f: t for t, f in enumerate(pf)}
        m = len(pf) - 1
        self.ent, self.ext = {}, {}
        for t in range(m + 1):
            self.ent[t] = self.idx[da_s] + 0.95 if t == 0 else self.idx[pdart[t][pf[t]]] + 0.5
            self.ext[t] = self.idx[da_t] + 0.95 if t == m else self.idx[pdart[t + 1][pf[t]]] + 0.5
        for t in range(1, m + 1):
            self.cut[pdart[t][pf[t]] >> 1] = 0
        self.sideF = {}
        for t in range(m + 1):
            X = A1.nodes[A1.piece[(t, 0)]]
            d, lab = X.seq[0]
            fw = self._fwd(t, self.idx[d] + (0.5, 0.25, 0.75)[lab])
            self.sideF[t] = 0 if fw else 1
        self.anns[1].append(A1)
        self.ok = True

    def _fwd(self, t, p):
        L = self.L[self.pf[t]]
        a, b = self.ent[t], self.ext[t]
        return 0 < (p - a) % L < (b - a) % L

    def coord(self, h, p):
        """(disc key, coordinate on its boundary circle, circle length) of face position p."""
        if h not in self.onP:
            return (h, None), p, self.L[h]
        t = self.onP[h]
        L = self.L[h]
        a, b = self.ent[t], self.ext[t]
        if self._fwd(t, p):
            return (h, self.sideF[t]), ((p - a) % L) / ((b - a) % L), 2.0
        return (h, 1 - self.sideF[t]), ((a - p) % L) / ((a - b) % L), 2.0

    @staticmethod
    def inside(z, a, b, C):
        return 0 < (z - a) % C < (b - a) % C

    def label(self, key, z, C, lev):
        if z in [c for ch in self.ch[key] if ch[2] < lev for c in ch[:2]]:
            self.flag('K_sample_on_chord_end', (key, z))
        return (key, tuple(self.inside(z, a, b, C) for a, b, lv in self.ch[key] if lv < lev))

    def lab_pos(self, h, p, lev):
        key, z, C = self.coord(h, p)
        return self.label(key, z, C, lev)

    def tok_pos(self, ld):
        d, lab = ld
        return self.idx[d] + (0.5, 0.25, 0.75)[lab]

    def slot(self, X, lev):
        labs = {self.lab_pos(X.face, self.tok_pos(ld), lev) for ld in X.seq}
        if len(labs) != 1:
            self.flag('K_piece_split', (X.id, X.anc, lev))
            return None
        return labs.pop()

    def gamma_parts(self, key, lev, S):
        rs = sorted({2.0 - b for a, b, lv in self.ch[key] if lv < lev})
        pts = [0.0] + rs + [1.0]
        return [(r0, r1) for r0, r1 in zip(pts, pts[1:]) if self.label(key, 2.0 - (r0 + r1) / 2, 2.0, lev) == S]

    def add_chord(self, key, a, b, C, lev):
        for c, d, lv in self.ch[key]:
            if len({a, b, c, d}) == 4 and self.inside(c, a, b, C) != self.inside(d, a, b, C):
                self.flag('K_cross', (key, (a, b), (c, d), lev))
        self.ch[key].append((a, b, lev))
        self.cnt['K_chords'] += 1

    # ------------------------------------------------------------ hooks
    def inc(self, A, i, Pn_, Pe_, Qn, Qe, xt, yt, i1, i2, ov, pieces, newnodes, comp, stats, level):
        if not self.ok:
            return
        new = []
        for k in range(1, len(Qn) - 1):
            g = A.nodes[Qn[k]]
            key, a, C = self.coord(g.face, self.idx[Qe[k - 1][1][0]] + 0.5)
            key2, b, _ = self.coord(g.face, self.idx[Qe[k][0][0]] + 0.5)
            if key != key2 or key[1] is not None:
                self.flag('K_internal_on_P', (A.aid, g.anc))
                continue
            if NEG != 'nochord':
                new.append((key, a, b, C))
        for X, tok, sg in ((A.nodes[Qn[0]], Qe[0][0], 0), (A.nodes[Qn[-1]], Qe[-1][1], 1)):
            key, u, _ = self.coord(X.face, self.idx[tok[0]] + 0.5)
            if key[1] != sg or X.anc[:1] != ('p',) or X.anc[2] != sg:
                self.flag('K_end_half', (A.aid, X.anc, key))
                continue
            S = self.slot(X, level)
            if S is None:
                continue
            parts = self.gamma_parts(key, level, S)
            self.cnt['K_gamma_checked'] += 1
            if len(parts) != 1:
                self.flag('K_gamma_part', (A.aid, X.anc, len(parts), level))
                continue
            r0, r1 = parts[0]
            if NEG == 'wrongq':
                rs = sorted({2.0 - b for a, b, lv in self.ch[key]})
                pts = [0.0] + rs + [1.0]
                r0, r1 = self.rng.choice(list(zip(pts, pts[1:])))
            if NEG == 'flipq':
                key = (key[0], 1 - key[1])
            r = r0 + (r1 - r0) * self.rng.uniform(0.25, 0.75)
            new.append((key, u, 2.0 - r, 2.0))
        for key, a, b, C in new:
            self.add_chord(key, a, b, C, level)
        for la, lb in Qe:
            if NEG != 'nocut':
                self.cut.setdefault(la[0] >> 1, level)

    def child(self, A, C, sidename, jj, kk, i, i1, i2, xt, yt, stats):
        if self.ok:
            self.anns[C.level].append(C)

    # ------------------------------------------------------------ the check of (I1) at every level
    def finalize(self):
        if not self.ok:
            return
        emb = self.emb
        for lev, anns in sorted(self.anns.items()):
            par = {}

            def f(x):
                par.setdefault(x, x)
                while par[x] != x:
                    par[x] = par[par[x]]
                    x = par[x]
                return x

            def u_(x, y):
                par[f(x)] = f(y)
            for h, cyc in enumerate(emb.faces):
                for d in cyc:
                    e = d >> 1
                    k = self.idx[d]
                    for c in (0.9, 0.99):
                        u_(self.lab_pos(h, k + c, lev), ('V', emb.head(d)))
                    if self.cut.get(e, 10 ** 9) < lev:
                        t0 = 0 if d % 2 == 0 else 1
                        u_(self.lab_pos(h, k + 0.25, lev), ('S', e, t0))
                        u_(self.lab_pos(h, k + 0.75, lev), ('S', e, 1 - t0))
                    else:
                        u_(self.lab_pos(h, k + 0.5, lev), ('S', e))
            for e, (a, b) in enumerate(emb.ends):
                if self.cut.get(e, 10 ** 9) < lev:
                    u_(('S', e, 0), ('V', a))
                    u_(('S', e, 1), ('V', b))
                else:
                    u_(('S', e), ('V', a))
                    u_(('S', e), ('V', b))
            owner = {}
            omega = {}
            for A in anns:
                comps = set()
                for X in A.nodes.values():
                    S = self.slot(X, lev)
                    self.cnt['K_piece_checked'] += 1
                    if S is None:
                        continue
                    if S in owner and owner[S] != (A.aid, X.id):
                        self.flag('K_slot_shared', (lev, A.aid, X.anc, owner[S]))
                    owner[S] = (A.aid, X.id)
                    if X.anc[0] == 'p':
                        if S[0][1] != X.anc[2]:
                            self.flag('K_half', (lev, A.aid, X.anc))
                        elif len(self.gamma_parts(S[0], lev, S)) != 1:
                            self.flag('K_gamma_part', (lev, A.aid, X.anc, 'fin'))
                    elif X.cyc and any(lv < lev for _, _, lv in self.ch[(X.face, None)]):
                        self.flag('K_cyclic_cut', (lev, A.aid, X.anc))
                    comps.add(f(S))
                if len(comps) != 1:
                    self.flag('K_omega_split', (lev, A.aid, len(comps)))
                    continue
                c = comps.pop()
                if c in omega:
                    self.flag('K_omega_shared', (lev, A.aid, omega[c]))
                omega[c] = A.aid
                self.cnt['K_ann_checked'] += 1
        self.cnt['K_runs'] += 1
