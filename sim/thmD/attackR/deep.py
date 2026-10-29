"""Reif recursion of [18, Alg. 3] in the abstract incision model (abstract18.Model), checked at
every level against Definition R built from the monotone I_l (defr.py).

Per level l and live annulus A (abstract):
  N1  every node-part of A has at most one seam and its token sequence is a piece of R2
  N2  every dual edge copy of A is an R1 pair; A's pieces form exactly one component of G*_l
  N3  refinement: every piece of G*_l refines one piece of G*_{l-1}; Rule M (Claim 3) for all
      pieces; if f is in a live annulus A' then its parent piece is in parent(A')
  LV  liveness: a residual component of G*_l descending from a non-leaf live annulus contains a
      bad edge (Claim 5.8 criterion), i.e. the distributed test does not mark it live
  F1  internal nodes of P_i' are not node-parts of P-faces
  F2  an internal node of P_i' with a seam lies on a bounding chord of A
  F3  overlap on a side <=> a component on that side has a bad edge
  R   Def R properties (1),(2),(4), Claim 1, Table R + Euler; option conflict never occurs
  E2E min over computed P_t = lambda
usage: python3 -I deep.py START COUNT WORKERS [policy] [variant]
"""
import sys, os, collections, random, heapq, json, time, traceback, itertools
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from emb import Emb, random_map, grid_map
import defr
from abstract18 import Model
from level1 import mincut_brute, dual_adj, dijkstra as ddijk, legal

INF = float('inf')
LAB = {'all': 0, 'tail': 1, 'head': 2}


class Ann:
    ctr = 0

    def __init__(self, nodes, j, k, left, right, level, parent):
        Ann.ctr += 1
        self.aid = Ann.ctr
        self.nodes = set(nodes)
        self.j, self.k = j, k
        self.left, self.right = left, right
        self.level = level
        self.parent = parent


def mincut(emb, s, t):
    if emb.n <= 14:
        return mincut_brute(emb, s, t)
    import networkx as nx
    H = nx.Graph()
    for e, (u, v) in enumerate(emb.ends):
        if H.has_edge(u, v):
            H[u][v]['capacity'] += emb.cap[e]
        else:
            H.add_edge(u, v, capacity=emb.cap[e])
    return nx.minimum_cut_value(H, s, t)


def tok(M, h):
    H = M.he[h]
    return (H.dart, LAB[H.kind])


class Run:
    def __init__(self, emb, s, t, rng, policy, var, C, notes, ident):
        self.emb, self.s, self.t, self.rng, self.policy, self.var = emb, s, t, rng, policy, var
        self.C, self.notes, self.ident = C, notes, ident
        self.nonunique = 0

    def bad(self, k, v=None):
        self.C['BAD_' + k] += 1
        if len(self.notes) < 60:
            self.notes.append((k, str(v)[:700], self.ident))

    # ------------------------------------------------------------ shortest paths in the model
    def sssp(self, nodes, src, wfun):
        M = self.M
        A = M.adj(nodes, wfun)
        dist = {src: 0}
        pq = [(0, src)]
        done = set()
        while pq:
            d, x = heapq.heappop(pq)
            if x in done:
                continue
            done.add(x)
            for y, w, h in A[x]:
                if d + w < dist.get(y, INF):
                    dist[y] = d + w
                    heapq.heappush(pq, (d + w, y))
        return dist, A

    def pick_path(self, nodes, src, tgt, wfun, prefer):
        """a shortest src-tgt path (node list, half-edge list) with policy tie-breaking.
        prefer: set of nodes to steer towards (touch policy) or away from (avoid)."""
        dist, A = self.sssp(nodes, src, wfun)
        if tgt not in dist:
            return None, None, INF
        # predecessor candidates: x with dist[x] + w = dist[y]
        rev = collections.defaultdict(list)
        for x in A:
            if x not in dist:
                continue
            for y, w, h in A[x]:
                if y in dist and dist[x] + w == dist[y]:
                    rev[y].append((x, h))
        if self.policy not in ('c', 'touch_c', 'kiss_c'):
            # number of shortest src-tgt paths (tight DAG; all weights >= 1)
            order = sorted((x for x in dist), key=lambda x: dist[x])
            cnt = {src: 1}
            for y in order:
                if y != src:
                    cnt[y] = sum(cnt.get(x, 0) for (x, h) in rev[y])
            if cnt.get(tgt, 0) > 1:
                self.nonunique += 1
        for attempt in range(50):
            pn = [tgt]
            ph = []
            vis = {tgt}
            cur = tgt
            ok = True
            while cur != src:
                cand = [(x, h) for (x, h) in rev[cur] if x not in vis]
                if not cand:
                    ok = False
                    break
                if self.policy in ('touch', 'touch_c') and prefer:
                    good = [c for c in cand if c[0] in prefer]
                    if good and self.rng.random() < 0.85:
                        cand = good
                elif self.policy in ('kiss', 'kiss_c') and prefer:
                    # touch a chord node, then leave it by a non-chord predecessor
                    if cur in prefer:
                        good = [c for c in cand if c[0] not in prefer]
                    else:
                        good = [c for c in cand if c[0] in prefer]
                    if good and self.rng.random() < 0.9:
                        cand = good
                elif self.policy == 'avoid' and prefer:
                    good = [c for c in cand if c[0] not in prefer]
                    if good:
                        cand = good
                x, h = self.rng.choice(cand)
                pn.append(x)
                ph.append(h)
                vis.add(x)
                cur = x
            if ok:
                pn.reverse()
                ph.reverse()
                return pn, ph, dist[tgt]
        # fallback: BFS on tight edges (gives a simple path)
        par = {src: None}
        q = [src]
        for x in q:
            for y, w, h in A[x]:
                if y in dist and dist[x] + w == dist[y] and y not in par:
                    par[y] = (x, h)
                    q.append(y)
        if tgt not in par:
            return None, None, INF
        self.C['pick_fallback_bfs'] += 1
        pn, ph = [tgt], []
        cur = tgt
        while par[cur] is not None:
            x, h = par[cur]
            pn.append(x)
            ph.append(h)
            cur = x
        pn.reverse()
        ph.reverse()
        return pn, ph, dist[tgt]

    # ------------------------------------------------------------ main
    def run(self):
        emb, rng, C = self.emb, self.rng, self.C
        s, t = self.s, self.t
        lam = mincut(emb, s, t)
        self.lam = lam
        K = 6 * emb.m + emb.n + 3
        self.K = K
        if self.policy in ('c', 'touch_c', 'kiss_c'):
            wfun = lambda e: emb.cap[e]
        else:
            wfun = lambda e: K * emb.cap[e] + 1
        self.wfun = wfun
        # ---- P: shortest f-g dual path
        A = dual_adj(emb)
        sf = sorted({emb.corner_face((s, i)) for i in range(emb.deg(s))})
        tf = sorted({emb.corner_face((t, i)) for i in range(emb.deg(t))})
        if rng.random() < 0.75:
            best = None
            for f in sf:
                dd = ddijk(A, f, lambda e: 1)
                for g in tf:
                    if best is None or dd.get(g, -1) > best[0]:
                        best = (dd.get(g, -1), f, g)
            f, g = best[1], best[2]
        else:
            f, g = rng.choice(sf), rng.choice(tf)
        if getattr(self, 'force_fg', None):
            f, g = self.force_fg
        self.fg = (f, g)
        M = Model(emb)
        self.M = M
        node_of_face = {X.face: nid for nid, X in M.np.items()}
        pn, ph, _ = self.pick_path(set(M.np), node_of_face[f], node_of_face[g], wfun, set())
        pf = [M.np[x].face for x in pn]
        pe = [M.he[h].dart >> 1 for h in ph]
        m = len(pf) - 1
        self.pf, self.pe = pf, pe
        C['instances'] += 1
        C['P_len_%d' % min(m, 9)] += 1
        Pedges = set(pe)
        cs_, ls = legal(emb, s, pf[0], Pedges)
        ct_, lt = legal(emb, t, pf[m], Pedges)
        if not ls or not lt:
            self.bad('P5_no_legal', (pf, pe))
            return
        if 'formal' in self.var:
            lsL = [x for x in ls if x[1] == 'L']
            ls = lsL or ls
            ltL = [x for x in lt if x[1] == 'L']
            lt = ltL or lt
        cs, ms = rng.choice(ls)
        ct, mt = rng.choice(lt)
        if getattr(self, 'force_cuts', None):
            (cs, ms), (ct, mt) = self.force_cuts
            if (cs, ms) not in ls or (ct, mt) not in lt:
                raise ValueError('forced cut not legal')
        self.legal = (ls, lt)
        self.cuts = [dict(z=s, i=cs, mode=ms, role='s'), dict(z=t, i=ct, mode=mt, role='t')]
        side = M.incise_gamma(pf, {k + 1: pe[k] for k in range(m)}, (s, cs), (t, ct))
        if M.flags:
            for k in M.flags:
                self.bad('abs_' + k, M.notes[:2])
        A1 = Ann(set(M.np), 0, m, None, None, 1, None)
        self.results = []
        I = set(pe)
        self.Ihist = {0: set(), 1: set(I)}
        prevG = defr.build(emb, set(), [], frozenset())
        defr.check_props(prevG, lambda k, v: self.bad('G0_' + k, v), full=False)
        active = [A1]
        level = 1
        prev_active = None
        self.orphans = []
        while active:
            orph = self.orphans
            self.orphans = []
            Ib = I
            if 'nonmono' in self.var:
                Ib = set(pe)
                for A in active:
                    for ch in (A.left, A.right):
                        if ch:
                            Ib |= {M.he[h].dart >> 1 for (h, _) in ch['edges']}
                self.Ihist[level] = set(Ib)
            G = defr.build(emb, Ib, self.cuts, frozenset(self.var) & {'no_opt2', 'all_opt2', 'xswap', 'host_head', 'no_reroute', 'swap_pairs', 'literal_D1'})
            self.orph_now = orph
            self.check_level(G, prevG, active, level, Ib)
            C['levels'] += 1
            nxt = []
            for A in active:
                nxt += self.step(A, level)
            # monotone I
            I = set(I) | set(M.incised)
            self.Ihist[level + 1] = set(I)
            prevG = G
            active = nxt
            level += 1
            if level > 40:
                self.bad('too_many_levels')
                break
        C['max_level_%d' % min(level - 1, 9)] += 1
        best = min((r[1] for r in self.results), default=INF)
        C['e2e_checked'] += 1
        if best != (lam if self.policy not in ('c', 'touch_c') else lam):
            # with K c + 1 weights the path length is K c + hops: compare floor
            pass
        got = min((r[2] for r in self.results), default=INF)
        if self.nonunique == 0 and self.policy not in ('c', 'touch_c', 'kiss_c'):
            C['e2e_all_paths_unique'] += 1
        if got != lam:
            self.bad('e2e_value', (got, lam, 'nonunique_picks=%d' % self.nonunique))
            if self.nonunique == 0 and self.policy not in ('c', 'touch_c', 'kiss_c'):
                self.bad('e2e_value_unique_paths', (got, lam))

    # ------------------------------------------------------------ one ShortestCycle call
    def plen(self, nodes, edges_h):
        return sum(self.emb.cap[self.M.he[h].dart >> 1] for h in edges_h)

    def find_piece(self, A, key):
        xs = [x for x in A.nodes if self.M.np[x].anc == ('p',) + key]
        if len(xs) > 1:
            self.bad('two_parts_of_P_node_in_annulus', (A.aid, key))
        return xs[0] if xs else None

    def step(self, A, level):
        M, rng, C = self.M, self.rng, self.C
        j, k = A.j, A.k
        if k <= j + 1:
            C['leaf'] += 1
            for tt in sorted({j, k}):
                a, b = self.find_piece(A, (tt, 0)), self.find_piece(A, (tt, 1))
                if a is None or b is None:
                    if A.j > A.k or 'lit_chord' in self.var or 'lit_full' in self.var or 'clamp' in self.var:
                        C['leaf_missing_piece_degenerate'] += 1
                    else:
                        self.bad('leaf_missing_piece', (A.aid, tt))
                    continue
                pn, ph, L = self.pick_path(A.nodes, a, b, self.wfun, set())
                if pn is None:
                    self.bad('leaf_unreachable', (A.aid, tt))
                    continue
                self.results.append((tt, L, self.plen(pn, ph)))
            return []
        i = (j + k) // 2
        a, b = self.find_piece(A, (i, 0)), self.find_piece(A, (i, 1))
        if a is None or b is None:
            if 'lit_chord' in self.var or 'lit_full' in self.var:
                C['missing_piece_lit'] += 1
            else:
                self.bad('missing_piece', (A.aid, i))
            return []
        prefer = set()
        for ch in (A.left, A.right):
            if ch:
                prefer |= set(ch['nodes'])
        prefer |= {x for x in A.nodes if M.np[x].anc[0] == 'p'}
        pn, ph, L = self.pick_path(A.nodes, a, b, self.wfun, prefer)
        if pn is None:
            self.bad('Pi_unreachable', (A.aid, i))
            return []
        self.results.append((i, L, self.plen(pn, ph)))
        C['Pi_computed'] += 1
        Pset = set(pn)
        Pedge = set()
        for h in ph:
            Pedge.add(h)
            Pedge.add(M.he[h].partner)
        # ---- overlaps (lines 9-14)
        ov = {}
        for sname, ch, lo, hi in (('l', A.left, j, i), ('r', A.right, i, k)):
            inter = Pset & set(ch['nodes']) if ch else set()
            ov[sname] = bool(inter)
            if inter:
                C['overlap'] += 1
                x = rng.choice(sorted(inter))
                dist, _ = self.sssp(A.nodes, x, self.wfun)
                distc, _ = self.sssp(A.nodes, x, lambda e: self.emb.cap[e])
                for tt in range(lo, hi + 1):
                    p0, p1 = self.find_piece(A, (tt, 0)), self.find_piece(A, (tt, 1))
                    if p0 is None or p1 is None:
                        continue
                    self.results.append((tt, dist.get(p0, INF) + dist.get(p1, INF),
                                         distc.get(p0, INF) + distc.get(p1, INF)))
        # ---- i1, i2, P_i'
        ancs = [M.np[x].anc for x in pn]
        tid = [an[1] for an in ancs if an[0] == 'p']
        i1, i2 = min(tid), max(tid)
        if i1 < j or i2 > k:
            C['i12_outside_range'] += 1
        if 'clamp' in self.var:
            # attempted repair: clamp the discarded range to [j, k]
            i1, i2 = max(i1, j), min(i2, k)
        last0 = max(q for q, an in enumerate(ancs) if an[0] == 'p' and an[2] == 0)
        first1 = min(q for q, an in enumerate(ancs) if q > last0 and an[0] == 'p' and an[2] == 1)
        Qn = pn[last0:first1 + 1]
        Qh = ph[last0:first1]
        x_idx, y_idx = ancs[last0][1], ancs[first1][1]
        # F1
        for q in Qn[1:-1]:
            if M.np[q].anc[0] == 'p':
                self.bad('F1_internal_P_node', (A.aid, q))
        # F2 and case (iv) coverage
        chord_nodes = set()
        for ch in (A.left, A.right):
            if ch:
                chord_nodes |= set(ch['nodes'])
        for q_, q in enumerate(Qn):
            nseam = sum(1 for it in M.np[q].items if it[0] == 'S')
            if 0 < q_ < len(Qn) - 1:
                if nseam:
                    C['case_iv_nodes'] += 1
                    if q not in chord_nodes:
                        self.bad('F2_linear_internal_not_on_chord', (A.aid, q, M.np[q].items))
                    ua = M.he[Qh[q_ - 1]].partner
                    wd = Qh[q_]
                    key = ('old' if M.he[ua].kind != 'all' else 'new') + '_' + ('old' if M.he[wd].kind != 'all' else 'new')
                    C['case_iv_' + key] += 1
                else:
                    C['case_ii_nodes'] += 1
        newe = [M.he[h].kind == 'all' for h in Qh]
        C['Qedges_new'] += sum(newe)
        C['Qedges_old'] += len(newe) - sum(newe)
        for h in Qh:
            e = M.he[h].dart >> 1
            if M.he[h].kind == 'all':
                if self.cuts and e in (self.cuts[0]['_e'], self.cuts[1]['_e']):
                    C['cov_endpoint_edge_incised_anew'] += 1
        # ---- bad edges (Claim 5.8), before incision, under two readings of P_a:
        #      'c' = the incised part P_a' (chord), 'f' = the whole path P_a restricted to A
        badh = {('c', 'l'): set(), ('c', 'r'): set(), ('f', 'l'): set(), ('f', 'r'): set()}
        ovr = {}
        for rd, keyn in (('c', ('left', 'right')), ('f', ('leftF', 'rightF'))):
            for sname, attr in zip('lr', keyn):
                ch = getattr(A, attr, None)
                if not ch:
                    ovr[(rd, sname)] = False
                    continue
                inter = Pset & set(ch['nodes'])
                ovr[(rd, sname)] = bool(inter)
                for (h1, h2) in ch['edges']:
                    if h1 in Pedge:
                        continue
                    n1, n2 = M.he[h1].node, M.he[h2].node
                    if n1 in inter or n2 in inter:
                        badh[(rd, sname)] |= {h1, h2}
        if ovr[('c', 'l')] != ov['l'] or ovr[('c', 'r')] != ov['r']:
            self.bad('impl_ov_mismatch')
        for sname in 'lr':
            if ovr[('f', sname)] and not ovr[('c', sname)]:
                C['overlap_full_only'] += 1
        # ---- incise
        before = set(A.nodes)
        oldkind = {h: M.he[h].kind for h in ph}
        res = M.incise_path(Qn, Qh, ('Q', A.aid), None, None)
        newcopy = M.last_newcopy
        if M.flags:
            for kk in list(M.flags):
                self.bad('abs_' + kk, M.notes[-2:])
            M.flags.clear()
        newnodes = (before - set(res)) | {x for pr in res.values() for x in pr if x is not None}
        comp = M.components(newnodes)
        if M.flags:
            for kk in list(M.flags):
                self.bad('abs_' + kk, M.notes[-2:])
            M.flags.clear()
        # sides
        splitparts = {p for pr in res.values() for p in pr if p is not None}
        low_seed, high_seed = set(), set()
        for z in newnodes:
            an = M.np[z].anc
            if an[0] != 'p' or z in splitparts:
                continue
            ref = x_idx if an[2] == 0 else y_idx
            if an[1] < ref:
                low_seed.add(z)
            elif an[1] > ref:
                high_seed.add(z)
        lowc = {comp[z] for z in low_seed}
        highc = {comp[z] for z in high_seed}
        # plus/minus parts of Q decide the side of the remaining components
        sidepm = {}
        for g, (pl, mi) in res.items():
            if pl is not None:
                sidepm.setdefault(comp[pl], set()).add('plus')
            if mi is not None:
                sidepm.setdefault(comp[mi], set()).add('minus')
        pm_low = {lab for c in lowc for lab in sidepm.get(c, ())}
        pm_high = {lab for c in highc for lab in sidepm.get(c, ())}
        if len(pm_low) > 1 or len(pm_high) > 1 or (pm_low & pm_high):
            self.bad('side_pm_inconsistent', (A.aid, pm_low, pm_high))
        lowlab = next(iter(pm_low)) if pm_low else ({'plus', 'minus'} - pm_high).pop() if len(pm_high) == 1 else None
        side_of = {}
        for c in set(comp.values()):
            if c in lowc:
                side_of[c] = 'l'
            elif c in highc:
                side_of[c] = 'r'
            elif lowlab is not None and sidepm.get(c) == {lowlab}:
                side_of[c] = 'l'
            elif lowlab is not None and sidepm.get(c) and lowlab not in sidepm.get(c):
                side_of[c] = 'r'
            else:
                side_of[c] = '?'
                C['component_side_unknown'] += 1
        if lowc & highc:
            self.bad('sides_merge', A.aid)
        badnodes = {key: {M.he[h].node for h in hs} for key, hs in badh.items()}
        hasbad = {}
        for c in set(comp.values()):
            for rd in 'cf':
                hasbad[(rd, c)] = any(comp.get(z) == c for sn in 'lr' for z in badnodes[(rd, sn)])
        # F3 under both readings: overlap on a side <=> some component on that side has a bad edge
        for rd in 'cf':
            for sname in 'lr':
                cs = [c for c in side_of if side_of[c] == sname]
                if not cs:
                    continue
                hb = any(c for c in cs if any(comp.get(z) == c for z in badnodes[(rd, sname)]))
                if ovr[(rd, sname)] != hb:
                    C['F3_mismatch_%s_ov%d' % (rd, ovr[(rd, sname)])] += 1
                    if rd == 'f' or 'strictF3c' in self.var:
                        self.bad('F3_%s_overlap_vs_bad' % rd, (A.aid, sname, ovr[(rd, sname)], hb))
                    else:
                        if len(self.notes) < 60:
                            self.notes.append(('info_F3_c_mismatch', str((A.aid, sname, ovr[(rd, sname)], hb)), self.ident))
        mode = 'lit_chord' if 'lit_chord' in self.var else 'lit_full' if 'lit_full' in self.var else 'driver'
        children = []
        live_comps = []
        if mode == 'driver':
            for sname, jj, kk, rng_ok in (('l', j, i1, j <= i1), ('r', i2, k, i2 <= k)):
                cs = [c for c in side_of if side_of[c] == sname]
                if ov[sname] and 'F3off' not in self.var:
                    C['child_discarded_overlap'] += 1
                    for c in cs:
                        if not hasbad[('c', c)]:
                            self.orphans.append(self.mk_orphan(newnodes, comp, c, jj, kk, A, 'ov'))
                    continue
                if not rng_ok:
                    C['child_range_empty'] += 1
                    for c in cs:
                        if not hasbad[('c', c)]:
                            self.orphans.append(self.mk_orphan(newnodes, comp, c, jj, kk, A, 'range'))
                    continue
                if 'F3off' in self.var and cs:
                    live_comps.append((set(cs), sname, jj, kk))
                    C['F3off_child'] += 1
                    if len(cs) > 1 or any(hasbad[('c', c)] for c in cs):
                        C['F3off_child_would_be_discarded'] += 1
                    continue
                if len(cs) != 1:
                    self.bad('child_not_one_component', (A.aid, sname, len(cs)))
                    continue
                if hasbad[('c', cs[0])]:
                    self.bad('child_live_side_has_bad', (A.aid, sname))
                    continue
                live_comps.append(({cs[0]}, sname, jj, kk))
        else:
            rd = 'c' if mode == 'lit_chord' else 'f'
            for c, sname in side_of.items():
                if hasbad[(rd, c)]:
                    C['lit_discarded'] += 1
                    continue
                if sname == '?':
                    self.bad('lit_live_component_side_unknown', A.aid)
                    continue
                jj, kk = (j, i1) if sname == 'l' else (i2, k)
                if (sname == 'l' and ov['l']) or (sname == 'r' and ov['r']):
                    C['lit_live_despite_overlap'] += 1
                if jj > kk:
                    C['lit_live_range_empty'] += 1
                live_comps.append(({c}, sname, jj, kk))
        for cset, sname, jj, kk in live_comps:
            cnodes = {z for z in newnodes if comp[z] in cset}
            Qc = self.restrict_path(Qn, Qh, res, newcopy, oldkind, cnodes)
            Fc = self.restrict_path(pn, ph, res, newcopy, oldkind, cnodes)
            if Qc is None or len(Qc['nodes']) != len(Qn):
                if mode == 'driver' and 'F3off' not in self.var:
                    self.bad('chord_copy_incomplete', (A.aid, sname))
                    continue
                C['chord_copy_partial'] += 1
                if Qc is None:
                    Qc = dict(nodes=[], edges=[])
            outerc = A.left if sname == 'l' else A.right
            outerf = getattr(A, 'leftF' if sname == 'l' else 'rightF', None)
            oc = self.restrict_chord(outerc, res, cnodes)
            of = self.restrict_chord(outerf, res, cnodes)
            if sname == 'l':
                ch = Ann(cnodes, jj, kk, oc, Qc, A.level + 1, A)
                ch.leftF, ch.rightF = of, Fc
            else:
                ch = Ann(cnodes, jj, kk, Qc, oc, A.level + 1, A)
                ch.leftF, ch.rightF = Fc, of
            children.append(ch)
            C['children'] += 1
        A.post = dict(newnodes=newnodes, comp=comp,
                      badtok={tok(M, h) for sn in 'lr' for h in badh[('c', sn)]},
                      badtok_f={tok(M, h) for sn in 'lr' for h in badh[('f', sn)]},
                      live={c.aid for c in children}, children=children)
        return children

    def mk_orphan(self, newnodes, comp, c, jj, kk, A, why):
        onodes = {z for z in newnodes if comp[z] == c}
        self.C['orphan_' + why] += 1
        O = Ann(onodes, jj, kk, None, None, A.level + 1, A)
        has_pair = any(self.find_piece(O, (tt, 0)) is not None and self.find_piece(O, (tt, 1)) is not None
                       for tt in range(min(jj, kk), max(jj, kk) + 1))
        if has_pair:
            self.C['orphan_%s_with_Pt_pair' % why] += 1
        return O

    def restrict_chord(self, ch, res, cnodes):
        if not ch:
            return ch
        M = self.M
        nodes = []
        for g in ch['nodes']:
            if g in res:
                nodes += [p for p in res[g] if p is not None and p in cnodes]
            elif g in cnodes:
                nodes.append(g)
        edges = [(h1, h2) for (h1, h2) in ch['edges']
                 if h1 in M.he and M.he[h1].node in cnodes and M.he[h2].node in cnodes]
        return dict(nodes=nodes, edges=edges)

    def restrict_path(self, pn, ph, res, newcopy, oldkind, cnodes):
        M = self.M
        nodes = []
        for g in pn:
            if g in res:
                nodes += [p for p in res[g] if p is not None and p in cnodes]
            elif g in cnodes:
                nodes.append(g)
        edges = []
        for h in ph:
            if oldkind[h] == 'all' and h in newcopy:
                for sd in ('plus', 'minus'):
                    hh = newcopy[h].get(sd)
                    if hh is not None and M.he[hh].node in cnodes:
                        edges.append((hh, M.he[hh].partner))
            else:
                if M.he[h].node in cnodes and M.he[M.he[h].partner].node in cnodes:
                    edges.append((h, M.he[h].partner))
        return dict(nodes=nodes, edges=edges)

    # ------------------------------------------------------------ comparisons at one level
    def check_level(self, G, prevG, active, level, I):
        M, C, emb = self.M, self.C, self.emb
        bad = self.bad
        defr.check_props(G, bad, full=(emb.n <= 40))
        defr.check_planar(G, bad)
        C['defR_levels'] += 1
        # option conflict
        outR = {emb.dout(c) for c, mu in G.cutc.items() if mu == 'R'}
        inL = {emb.din(c) for c, mu in G.cutc.items() if mu == 'L'}
        if any((d >> 1) in I for d in outR & inL):
            bad('option_conflict_reached', level)
        # coverage
        e0, el = G.e0, G.elast
        for cu in self.cuts:
            if cu['_e'] in I:
                C['cov_endpoint_edge_in_I_mode' + cu['mode']] += 1
                C['cov_endpoint_edge_in_I_deg%d' % min(emb.deg(cu['z']), 3)] += 1
        if e0 == el and e0 in I:
            C['cov_e0_eq_elast_incised_' + self.cuts[0]['mode'] + self.cuts[1]['mode']] += 1
        for c in G.cutc:
            x, _ = G.moved[c]
            eid, end = G.ECof[x]
            if G.E[eid][end] == ('X',) + c:
                C['cov_X_deg3'] += 1
        # pieces lookup
        piece_key = {}
        for pi, P in enumerate(G.pieces):
            T = tuple(P['toks'])
            if P['cyclic']:
                kk = min(range(len(T)), key=lambda q: T[q:] + T[:q])
                T = T[kk:] + T[:kk]
            piece_key[(P['face'], T, P['cyclic'])] = pi
        comp = defr.token_components(G)
        pairset = {frozenset(p) for p in G.pairs}
        ann_of_piece = {}
        orph_comps = set()
        for A in list(active) + list(getattr(self, 'orph_now', [])):
            is_orph = A not in active
            ps = set()
            for nid in A.nodes:
                T, ns = M.tokens_of(nid)
                if ns > 1:
                    bad('N1_multi_seam_node_in_live_annulus', (level, A.aid, M.np[nid].items))
                T = tuple(T)
                cyc = ns == 0
                if cyc:
                    kk = min(range(len(T)), key=lambda q: T[q:] + T[:q])
                    T = T[kk:] + T[:kk]
                pi = piece_key.get((M.np[nid].face, T, cyc))
                if pi is None:
                    bad('N1_node_not_piece', (level, A.aid, M.np[nid].face, T, cyc))
                    continue
                ps.add(pi)
                if not is_orph:
                    ann_of_piece[pi] = A
                for it in M.np[nid].items:
                    if it[0] == 'H':
                        pr = frozenset([tok(M, it[1]), tok(M, M.he[it[1]].partner)])
                        if pr not in pairset:
                            bad('N2_edge_not_pair', (level, A.aid, sorted(pr)))
            C['N_annuli_checked' if not is_orph else 'N_orphans_checked'] += 1
            C['N_nodeparts_checked'] += len(A.nodes)
            cs = {comp[p] for p in ps}
            if is_orph:
                orph_comps |= cs
            if len(cs) != 1:
                bad('N2_annulus_spans_components', (level, A.aid, len(cs)))
                continue
            c0 = cs.pop()
            whole = {p for p in range(len(G.pieces)) if comp[p] == c0}
            if whole != ps:
                bad('N2_annulus_not_whole_component', (level, A.aid, len(whole), len(ps)))
        if level == 1 and len(set(comp)) != 1:
            bad('N_level1_disconnected', None)
        # refinement and Rule M
        Iprev = self.Ihist[level - 1]
        prev_ann_pieces = getattr(self, 'prev_ann_pieces', {})
        for pi, P in enumerate(G.pieces):
            par = set()
            for x in P['toks']:
                d, l = x
                xb = x if (d >> 1) in Iprev else (d, 0)
                if xb not in prevG.piece_of:
                    bad('N3_parent_token_missing', (level, x))
                    continue
                g = prevG.piece_of[xb]
                par.add(g)
                if (d >> 1) in I and (d >> 1) not in Iprev:
                    C['RuleM_tokens_incised_anew'] += 1
                    if any((d >> 1) == cu['_e'] for cu in self.cuts):
                        C['RuleM_endpoint_edge_incised_anew'] += 1
                if any(G.alpha[x] == ('X',) + c or G.beta[x] == ('X',) + c for c in G.cutc):
                    C['RuleM_X_tokens'] += 1
                for v in (emb.tl[d], emb.tl[d ^ 1]):
                    att0 = G.alpha[x] if emb.tl[d] == v else G.beta[x]
                    att1 = prevG.alpha[xb] if emb.tl[d] == v else prevG.beta[xb]
                    if G.vpiece.get(att0) != pi:
                        bad('RuleM_att_not_on_piece', (level, x, v))
                    if prevG.vpiece.get(att1) != g:
                        bad('RuleM_parent_att_not_on_parent_piece', (level, x, v))
            if len(par) != 1:
                bad('N3_piece_refines_several', (level, pi, par))
                continue
            C['N3_pieces_refined'] += 1
            A = ann_of_piece.get(pi)
            if A is not None and A.parent is not None:
                g = next(iter(par))
                if prev_ann_pieces.get(g) is not A.parent:
                    bad('N3_parent_piece_not_in_parent_annulus', (level, pi))
        # liveness test on token components (for children of the previous level)
        if level >= 2:
            live_comps = {comp[p] for p in ann_of_piece}
            for A in getattr(self, 'prev_active', []):
                if not hasattr(A, 'post'):
                    continue
                # pieces of G*_l descending from A
                Apieces = {p for p, B in prev_ann_pieces.items() if B is A}
                desc = set()
                for pi, P in enumerate(G.pieces):
                    x = P['toks'][0]
                    d, l = x
                    xb = x if (d >> 1) in Iprev else (d, 0)
                    if prevG.piece_of.get(xb) in Apieces:
                        desc.add(pi)
                dcomps = {comp[p] for p in desc}
                for c in dcomps:
                    members = [p for p in desc if comp[p] == c]
                    if c in live_comps:
                        continue
                    if c in orph_comps:
                        C['LV_orphan_component'] += 1
                        continue
                    toks = {x for p in members for x in G.pieces[p]['toks']}
                    C['LV_residual_components'] += 1
                    if toks & A.post['badtok']:
                        C['LV_residual_with_bad'] += 1
                        continue
                    if toks & A.post['badtok_f']:
                        C['LV_residual_with_full_bad_only'] += 1
                        continue
                    # no bad edge: would the distributed test mark it live?
                    anc = sorted({(M_anc) for M_anc in self.anc_of_pieces(G, members)})
                    has_range = any(a[0] == 'p' and A.j <= a[1] <= A.k for a in anc)
                    self.bad('LV_residual_without_bad_edge',
                             (level, A.aid, A.j, A.k, len(members), anc[:6], has_range))
        self.prev_active = list(active)
        self.prev_ann_pieces = ann_of_piece

    def anc_of_pieces(self, G, members):
        """P-ancestry of pieces via the abstract model (by token match)."""
        M = self.M
        tk = {}
        for nid, X in M.np.items():
            T, ns = M.tokens_of(nid)
            for x in T:
                tk[x] = X.anc
        out = []
        for p in members:
            x = G.pieces[p]['toks'][0]
            out.append(tk.get(x, ('?',)))
        return out


# ------------------------------------------------------------------ instances
FORCE = {}


def make_instance(seed):
    rng = random.Random(seed)
    fam = rng.choice(['rand', 'rand', 'rand', 'grid', 'sparse', 'dense'])
    if 'fam' in FORCE:
        fam = rng.choice(FORCE['fam'])
    if fam == 'big':
        emb = random_map(rng, rng.randint(30, 70), extra_frac=rng.choice([0.3, 0.6, 0.9]), par_prob=0.08)
    elif fam == 'biggrid':
        emb = grid_map(rng, rng.randint(5, 9), rng.randint(5, 9), drop=rng.choice([0, 0.1, 0.25]))
    elif fam == 'grid':
        emb = grid_map(rng, rng.randint(3, 6), rng.randint(3, 6), drop=rng.choice([0, 0.15, 0.3]))
    elif fam == 'sparse':
        emb = random_map(rng, rng.randint(6, 26), extra_frac=0.25, par_prob=0.15)
    elif fam == 'dense':
        emb = random_map(rng, rng.randint(6, 20), extra_frac=1.0, par_prob=0.1)
    else:
        emb = random_map(rng, rng.randint(5, 30), extra_frac=rng.choice([0.4, 0.6, 0.8]), par_prob=0.1)
    scheme = rng.choice(['unit', 'small', 'zeros', 'wide'])
    if 'scheme' in FORCE:
        scheme = rng.choice(FORCE['scheme'])
    if scheme == 'unit':
        cap = [1] * emb.m
    elif scheme == 'small':
        cap = [rng.randint(1, 3) for _ in range(emb.m)]
    elif scheme == 'zeros':
        cap = [rng.choice([0, 0, 1, 2]) for _ in range(emb.m)]
    elif scheme == 'generic':
        cap = [rng.randint(1, 10 ** 6) for _ in range(emb.m)]
    elif scheme == 'generic0':
        cap = [rng.choice([0, rng.randint(1, 10 ** 6)]) for _ in range(emb.m)]
    else:
        cap = [rng.choice([1, 2, 5, 20, 100]) for _ in range(emb.m)]
    emb = emb.with_cap(cap)
    stm = rng.choice(['rand', 'deg1', 'adj', 'face', 'far', 'far', 'far', 'far1'])
    V = list(range(emb.n))
    s, t = rng.sample(V, 2)
    if stm == 'deg1':
        d1 = [v for v in V if emb.deg(v) <= 2]
        if len(d1) >= 2:
            s, t = rng.sample(d1, 2)
        elif d1:
            s = d1[0]
            t = rng.choice([v for v in V if v != s])
    elif stm == 'adj':
        e = rng.randrange(emb.m)
        s, t = emb.ends[e]
        if rng.random() < 0.5:
            s, t = t, s
    elif stm == 'face':
        f = rng.choice(emb.faces)
        vs = sorted({emb.tl[d] for d in f})
        if len(vs) >= 2:
            s, t = rng.sample(vs, 2)
    if stm == 'far1':
        d1 = [v for v in V if emb.deg(v) <= 2] or V
        s = rng.choice(d1)
        stm2 = 'far'
    else:
        stm2 = stm
    if stm2 == 'far':
        import collections as _c
        adj = _c.defaultdict(list)
        for (u, v) in emb.ends:
            adj[u].append(v)
            adj[v].append(u)
        dist = {s: 0}
        q = [s]
        for x in q:
            for y in adj[x]:
                if y not in dist:
                    dist[y] = dist[x] + 1
                    q.append(y)
        t = max(V, key=lambda v: (dist[v], v != s, emb.deg(v) <= 2 and stm == 'far1'))
        if t == s:
            t = (s + 1) % emb.n
    return emb, s, t, dict(fam=fam, scheme=scheme, stm=stm)


def work(args):
    start, count, policy, var, force = args
    FORCE.update(force)
    C = collections.Counter()
    notes = []
    for sd in range(start, start + count):
        emb, s, t, meta = make_instance(sd)
        rng = random.Random(sd * 7919 + 13)
        pol = policy if policy != 'mix' else rng.choice(['random', 'touch', 'avoid', 'c', 'touch_c', 'kiss', 'kiss_c'])
        C['policy_' + pol] += 1
        R = Run(emb, s, t, rng, pol, var, C, notes, dict(seed=sd, pol=pol, **meta))
        nb0 = sum(v for k, v in C.items() if k.startswith('BAD_'))
        try:
            R.run()
        except Exception:
            C['BAD_exception'] += 1
            if len(notes) < 60:
                notes.append(('exception', traceback.format_exc()[-900:], dict(seed=sd, pol=pol)))
        if sum(v for k, v in C.items() if k.startswith('BAD_')) > nb0:
            C['inst_with_BAD'] += 1
    return C, notes


def main():
    start, count, workers = map(int, sys.argv[1:4])
    policy = sys.argv[4] if len(sys.argv) > 4 else 'mix'
    var = frozenset(sys.argv[5].split(',')) if len(sys.argv) > 5 and sys.argv[5] else frozenset()
    if len(sys.argv) > 6 and sys.argv[6]:
        FORCE['fam'] = sys.argv[6].split(',')
    if len(sys.argv) > 7 and sys.argv[7]:
        FORCE['scheme'] = sys.argv[7].split(',')
    t0 = time.time()
    per = max(1, count // (workers * 8))
    jobs = [(st, min(per, start + count - st), policy, var, dict(FORCE)) for st in range(start, start + count, per)]
    import multiprocessing as mp
    C = collections.Counter()
    notes = []
    with mp.Pool(workers) as pool:
        for c, nt in pool.imap_unordered(work, jobs):
            C.update(c)
            notes += nt
    print(json.dumps(dict(args=sys.argv[1:], secs=round(time.time() - t0), counts=dict(sorted(C.items())),
                          notes=notes[:60]), indent=1, default=str))


if __name__ == '__main__':
    main()
