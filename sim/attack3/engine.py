"""Level-by-level: build [8]-shaped children for every non-leaf bag at depth d (separators may be
chosen against Gamma_d), then run the construction of LEMMA15.md §3.2 and check §3 claims."""
import math, random, collections, itertools
import numpy as np, networkx as nx
from scipy.sparse import coo_matrix
from scipy.sparse.csgraph import connected_components
from core import PG, Fail, between, pip, TAU, tree_diam, monge_check, sp_matrix, add_arc


class Engine:
    def __init__(self, g, vcand, rng, cfg):
        self.g = g; self.rng = rng
        self.cfg = dict(leaf=8, tries=60, modes={'bal': 1.0}, zall=0.0, swap=0.3, degenerate=False,
                        txmode='bfs', maxdepth=60, monge_cap=70, stop=True, neg=None, root=None,
                        bal=0.92, prefer_virtual=0.0)
        self.cfg.update(cfg)
        self.vc = vcand                         # set of (a,b) a<b virtual candidates
        self.vadj = collections.defaultdict(set)
        for a, b in vcand:
            self.vadj[a].add(b); self.vadj[b].add(a)
        self.st = collections.Counter(); self.mx = collections.defaultdict(float)
        self.fails = []
        n = g.n
        r = self.cfg['root'] if self.cfg['root'] is not None else rng.randrange(n)
        if r == 'center':
            c = g.pos.mean(0); r = int(np.argmin(((g.pos - c) ** 2).sum(1)))
        self.T = nx.bfs_tree(g.G, r).to_undirected()
        self.Tadj = {v: set(self.T[v]) for v in range(n)}
        self.bags = {0: dict(X=set(range(n)), parent=None, depth=0, z={}, kids=None)}
        self.adder = {}                          # corner -> bag that added it

    def fail(self, kind, info=None):
        self.st['FAIL ' + kind] += 1
        self.fails.append((kind, info))
        if self.cfg['stop']:
            raise Fail(kind, info)

    # ------------------------------------------------------------ BDD part
    def anc(self, b):
        out = []; p = self.bags[b]['parent']
        while p is not None:
            out.append(p); p = self.bags[p]['parent']
        return out

    def dss(self, b):
        X = self.bags[b]['X']; s = set()
        for a in self.anc(b):
            s |= self.bags[a]['S'] & X
        return s

    def make_TX(self, X, gverts=frozenset()):
        g, rng = self.g, self.rng
        tx0 = self.cfg['txmode'] if not isinstance(self.cfg['txmode'], list) else None
        if tx0 == 'bfsfar' or (tx0 is None and 'bfsfar' in self.cfg['txmode'] and rng.random() < 0.5):
            GX = g.G.subgraph(X)
            src = [v for v in X if v in gverts]
            if src:
                dist = nx.multi_source_dijkstra_path_length(GX, src, weight=None)
                far = max(X, key=lambda v: (dist.get(v, 0), rng.random()))
            else:
                far = rng.choice(sorted(X))
            Tt = nx.bfs_tree(GX, far).to_undirected()
            return {v: set(Tt[v]) for v in X}, -1, -1
        adj = {v: set(u for u in self.Tadj[v] if u in X) for v in X}
        # union-find components of T[X]
        par = {v: v for v in X}
        def find(x):
            while par[x] != x:
                par[x] = par[par[x]]; x = par[x]
            return x
        for v in X:
            for u in adj[v]:
                a, b = find(u), find(v)
                if a != b:
                    par[a] = b
        ncomp = len({find(v) for v in X})
        tx = self.cfg['txmode'] if not isinstance(self.cfg['txmode'], list) else rng.choice(self.cfg['txmode'])
        if tx in ('dfs', 'rand'):
            GX = g.G.subgraph(X)
            if tx == 'dfs':
                Tt = nx.dfs_tree(GX, rng.choice(sorted(X))).to_undirected()
            else:
                H = nx.Graph()
                for a_, b_ in GX.edges():
                    H.add_edge(a_, b_, weight=rng.random())
                Tt = nx.minimum_spanning_tree(H)
            adj = {v: set(Tt[v]) for v in X}
            return adj, ncomp, -1
        cand = [(a, b) for (a, b) in g.ends if a in X and b in X and b not in adj[a]]
        rng.shuffle(cand)
        added = 0
        for a, b in cand:
            x, y = find(a), find(b)
            if x != y:
                par[x] = y; adj[a].add(b); adj[b].add(a); added += 1
        return adj, ncomp, added

    def tree_path(self, adj, root_par, depth, y, z):
        a, b = y, z; pa, pb = [a], [b]
        while depth[a] > depth[b]:
            a = root_par[a]; pa.append(a)
        while depth[b] > depth[a]:
            b = root_par[b]; pb.append(b)
        while a != b:
            a = root_par[a]; pa.append(a); b = root_par[b]; pb.append(b)
        return pa + pb[-2::-1]

    def analyse(self, X, Xl, q, swap):
        """sides of the cycle q (+closing edge q[-1]q[0])."""
        g = self.g
        S = set(q)
        rest = [v for v in Xl if v not in S]
        if not rest:
            return None
        if self.cfg.get('strict'):
            others = [v for v in range(g.n) if v not in X]
            if others and pip(g.pos[others], g.pos[q]).any():
                return None
        inside = pip(g.pos[rest], g.pos[q])
        ins = {v for v, f in zip(rest, inside) if f}
        if swap:
            ins = set(rest) - ins
        out = set(rest) - ins
        return S, ins, out

    def wedges(self, q, swap):
        """per s in S: (os, oe) = ccw arc of the out-wedge (X_in on the other side)."""
        g = self.g; P = g.pos
        poly = P[q]; L = len(q)
        W = {}
        for i, s in enumerate(q):
            p, nx_ = q[i - 1], q[(i + 1) % L]
            a1, a2 = g.angle(s, p), g.angle(s, nx_)
            mid = a1 + ((a2 - a1) % TAU) / 2
            pt = np.array([[P[s][0] + 1e-6 * math.cos(mid), P[s][1] + 1e-6 * math.sin(mid)]])
            inn = bool(pip(pt, poly)[0])
            if swap:
                inn = not inn
            W[s] = (a2, a1) if inn else (a1, a2)     # (os, oe) ccw = out-wedge
        return W

    def children(self, b, q, closing_real, swap, zmode):
        """[8]-shaped children: X_in, then components of the auxiliary graph (split at z),
        then split by G[Y]-components (virtual edge)."""
        g = self.g; B = self.bags[b]; X = B['X']; Xl = sorted(X)
        r = self.analyse(X, Xl, q, swap)
        if r is None:
            return None
        S, ins, out = r
        if not ins or not out:
            return None
        Xin = S | ins
        W = self.wedges(q, swap)
        L = len(q)
        cyc = {}
        for i, s in enumerate(q):
            cyc[s] = {q[i - 1], q[(i + 1) % L]}
        zold = B['z']
        z = {}
        for s in q:
            os_, oe = W[s]
            if s in zold and between(os_, zold[s], oe):
                z[s] = zold[s]
            elif s in zold:
                self.st['z_inherited_in_inside_wedge'] += 1
            elif zmode and self.rng.random() < zmode:
                z[s] = os_ + ((oe - os_) % TAU) * self.rng.uniform(0.05, 0.95)
        def node(s, th):
            if s in z:
                os_ = W[s][0]
                return ('s', s, 0 if ((th - os_) % TAU) <= ((z[s] - os_) % TAU) else 1)
            return ('s', s, 0)
        aux = nx.Graph()
        aux.add_nodes_from(('v', x) for x in out)
        chords = collections.Counter()
        for x in Xl:
            for t in g.rot[x]:
                if t not in X or t < x:
                    continue
                a, c = x, t
                if a in out and c in out:
                    aux.add_edge(('v', a), ('v', c))
                elif a in S and c in out:
                    aux.add_edge(node(a, g.ang[(a, c)]), ('v', c))
                elif c in S and a in out:
                    aux.add_edge(node(c, g.ang[(c, a)]), ('v', a))
                elif a in S and c in S:
                    is_s = c in cyc[a] and (closing_real or {a, c} != {q[0], q[-1]})
                    if is_s:
                        aux.add_edge(node(a, g.ang[(a, c)]), node(c, g.ang[(c, a)]))
                    else:
                        os_, oe = W[a]
                        if between(os_, g.ang[(a, c)], oe):
                            aux.add_edge(node(a, g.ang[(a, c)]), node(c, g.ang[(c, a)]))
                            chords[a] += 1; chords[c] += 1
        if not closing_real:
            y, zz = q[0], q[-1]
            aux.add_edge(node(y, g.angle(y, zz)), node(zz, g.angle(zz, y)))
        kids = [Xin]; ndeg = 0
        for comp in nx.connected_components(aux):
            Y = {nd[1] for nd in comp}
            hasv = any(nd[0] == 'v' for nd in comp)
            if not hasv and not self.cfg['degenerate']:
                continue
            for part in nx.connected_components(g.G.subgraph(Y)):
                if any(x in out for x in part) or self.cfg['degenerate']:
                    kids.append(set(part))
                    if not any(x in out for x in part):
                        ndeg += 1
        if any(len(Y) >= len(X) for Y in kids):
            return None
        return dict(S=S, ins=ins, out=out, W=W, z=z, kids=kids, chords=chords, ndeg=ndeg, cyc=cyc)

    def choose_and_split(self, b, cur):
        g, rng, cfg = self.g, self.rng, self.cfg
        B = self.bags[b]; X = B['X']
        adj, ncomp, added = self.make_TX(X, cur['gverts'])
        self.mx['TX_comp_of_T[X]_max'] = max(self.mx['TX_comp_of_T[X]_max'], ncomp)
        self.mx['T[X]comp_minus_depth'] = max(self.mx['T[X]comp_minus_depth'], ncomp - (B['depth'] + 1))
        root = min(X) if ncomp != -1 else next(v for v in X if True)
        rp = {root: None}; dep = {root: 0}; dq = collections.deque([root])
        while dq:
            x = dq.popleft()
            for y in adj[x]:
                if y not in rp:
                    rp[y] = x; dep[y] = dep[x] + 1; dq.append(y)
        assert len(rp) == len(X)
        real = [(a, c) for (a, c) in g.ends if a in X and c in X and c not in adj[a]]
        virt = [(a, c) for (a, c) in self.vc if a in X and c in X and c not in adj[a]]
        cands = [(e, True) for e in real] + [(e, False) for e in virt]
        rng.shuffle(cands)
        cands = cands[:cfg['tries'] * 3]
        modes = cfg['modes']
        mode = rng.choices(list(modes), weights=list(modes.values()))[0]
        gverts = cur['gverts']; label = cur['label']
        dS = self.dss(b)
        scored = []
        for (y, zz), realc in cands:
            q = self.tree_path(adj, rp, dep, y, zz)
            if len(q) < 3:
                continue
            swap = rng.random() < cfg['swap']
            r = self.analyse(X, sorted(X), q, swap)
            if r is None:
                continue
            S, ins, out = r
            if not ins or not out:
                continue
            big = max(len(ins), len(out)) + len(S)
            bal = big / len(X)
            qs = set(q)
            qe = [g.e(q[i], q[i + 1]) for i in range(len(q) - 1)]
            allX = all(label[e] == b for e in qe)
            nch = sum(1 for s_ in q for t_ in g.rot[s_] if t_ in qs) // 2 - len(q)
            feat = dict(bnd=len(qs & dS), avoid=(allX and not (qs & gverts)), ch=nch,
                        virt=not realc, onG=len(qs & gverts), long=len(q))
            scored.append((bal, feat, q, realc, swap))
            if len(scored) >= cfg['tries']:
                break
        if not scored:
            return None
        ok = [s for s in scored if s[0] <= cfg['bal']] or sorted(scored, key=lambda s: s[0])[:3]
        if mode == 'bal':
            pick = sorted(ok, key=lambda s: s[0])
        elif mode == 'bnd':
            pick = sorted(ok, key=lambda s: (-s[1]['bnd'], s[0]))
        elif mode == 'avoid':
            av = [s for s in scored if s[1]['avoid']]
            self.st['avoid_candidates_bags'] += bool(av)
            pick = sorted(av, key=lambda s: s[0]) + sorted(ok, key=lambda s: s[0])
        elif mode == 'virt':
            pick = sorted(ok, key=lambda s: (not s[1]['virt'], s[0]))
        elif mode == 'onG':
            pick = sorted(ok, key=lambda s: (-s[1]['onG'], s[0]))
        elif mode == 'chord':
            pick = sorted(ok, key=lambda s: (-s[1]['ch'], s[0]))
        elif mode == 'long':
            pick = sorted(ok, key=lambda s: (-s[1]['long'], s[0]))
        else:
            pick = list(ok); rng.shuffle(pick)
        for bal, feat, q, realc, swap in pick[:12]:
            res = self.children(b, q, realc, swap, cfg['zall'])
            if res is None:
                continue
            res.update(q=q, real=realc, TX=adj, swap=swap, mode=mode, feat=feat, ncompT=ncomp)
            return res
        return None

    def verify_G1(self, b, res):
        """independent check of (G1'), 7(a), 7(b), (7c), (7c'), Property 3 for the children."""
        g = self.g; X = self.bags[b]['X']; S = res['S']; ins = res['ins']; out = res['out']
        kids = res['kids']; W = res['W']
        Xin = kids[0]
        if Xin != S | ins:
            self.fail('G1 X_in != S + inside')
        for x in ins:
            for t in g.rot[x]:
                if t in out:
                    self.fail('Jordan: inside-outside edge', (x, t))
        owner = {}
        for i, Y in enumerate(kids[1:], 1):
            for x in Y - S:
                if x in owner or x not in out:
                    self.fail('G1 outside vertex not in exactly one child', x)
                owner[x] = i
        if set(owner) != out:
            self.fail('G1 outside vertex in no child')
        GXo = g.G.subgraph(out)
        for C in nx.connected_components(GXo):
            ids = {owner[x] for x in C}
            if len(ids) != 1:
                self.fail('G1 component split across children')
            i = ids.pop()
            for x in C:
                for t in g.rot[x]:
                    if t in S and t not in kids[i]:
                        self.fail("G1 child misses S-neighbour of its component")
        # contiguity: in the out-wedge of s (from os ccw to oe), the child ids of edges to outside
        # vertices change at most once
        for s in S:
            os_, oe = W[s]
            seq = []
            for t in g.rot[s]:
                if t in out:
                    th = g.ang[(s, t)]
                    if not between(os_, th, oe):
                        self.fail('outside edge not in out-wedge', (s, t))
                    seq.append(((th - os_) % TAU, owner[t]))
                elif t in ins:
                    if between(os_, g.ang[(s, t)], oe):
                        self.fail('inside edge in out-wedge', (s, t))
            seq.sort()
            ch = sum(1 for i in range(1, len(seq)) if seq[i][1] != seq[i - 1][1])
            if ch > 1:
                self.fail('G1 contiguity', (s, ch))
            k = sum(1 for Y in kids[1:] if s in Y)
            self.mx['outkids_per_s'] = max(self.mx['outkids_per_s'], k)
            if k > 2:
                self.fail('7(a): s in more than two outside children', (s, k))
        # 7(b) and (7c'), (7c), Property 3
        allk = kids
        kid_of = {}
        for i, Y in enumerate(allk):
            for x in Y - S:
                kid_of[x] = i
        for (a, c) in g.ends:
            if a in X and c in X:
                if a not in S and c not in S and kid_of[a] != kid_of[c]:
                    self.fail('7(b)')
                for x, t in ((a, c), (c, a)):
                    if x not in S and t not in allk[kid_of[x]]:
                        self.fail("(7c')")
                if not any(a in Y and c in Y for Y in allk):
                    self.fail('(7c)')
        for Y in allk:
            if not nx.is_connected(g.G.subgraph(Y)):
                self.fail('Property 3: child not connected')
        self.st['G1_checks'] += 1

    def comps_T(self, Y):
        par = {v: v for v in Y}
        def find(x):
            while par[x] != x:
                par[x] = par[par[x]]; x = par[x]
            return x
        for v in Y:
            for u in self.Tadj[v]:
                if u in Y:
                    a, b = find(u), find(v)
                    if a != b: par[a] = b
        return len({find(v) for v in Y})

    def lp46(self, b, res):
        """[8] Claim 4.6: S[X_i^-] is one segment and (T' u S)[X_i^-] is connected; [8] Lemma 4.7:
        T[X'] has at most one more component than T[X].  Report only."""
        q = res['q']; L = len(q); TX = res['TX']; X = self.bags[b]['X']
        cX = self.comps_T(X)
        for i, Y in enumerate(res['kids']):
            inY = [v in Y for v in q]
            if all(inY):
                arcs = 1
            else:
                arcs = sum(1 for k in range(L) if inY[k] and not inY[k - 1])
            H = nx.Graph(); H.add_nodes_from(Y)
            for v in Y:
                for u in TX[v]:
                    if u in Y: H.add_edge(u, v)
            for k in range(L):
                a_, c_ = q[k], q[(k + 1) % L]
                if a_ in Y and c_ in Y: H.add_edge(a_, c_)
            conn = nx.is_connected(H)
            cY = self.comps_T(Y)
            self.st['lp46_children'] += 1
            if i > 0 and arcs >= 2:
                self.st['lp46_multi_arc_children'] += 1
            self.mx['lp46_max_arcs'] = max(self.mx['lp46_max_arcs'], arcs if i > 0 else 0)
            if not conn:
                self.st['lp46_TuS_disconnected'] += 1
                if self.cfg['txmode'] == 'bfs': self.st['lp46_TuS_disconnected_bfs'] += 1
            self.mx['lp47_comp_growth'] = max(self.mx['lp47_comp_growth'], cY - cX)

    # ------------------------------------------------------------ tiles part
    def tiles(self, gmask):
        g = self.g
        keep = ~gmask
        A = coo_matrix((np.ones(int(keep.sum())), (g.eprev[keep], g.enext[keep])), shape=(g.m, g.m))
        k, lab = connected_components(A, directed=False)
        return k, lab

    def sector_open(self, gidx, v, i):
        """opening Gamma-corner index of the sector of v containing edge index i; None if v not in Gamma."""
        L = gidx.get(v)
        if not L:
            return None
        k = np.searchsorted(L, i, side='right') - 1
        return L[k]

    def mk_level(self, gmask, label):
        g = self.g
        lv = dict(gmask=gmask, label=label)
        gl = np.nonzero(gmask)[0]
        gidx = collections.defaultdict(list)
        for c in gl:
            gidx[int(g.cv[c])].append(int(g.cj[c]))
        for v in gidx:
            gidx[v].sort()
        lv['gidx'] = dict(gidx); lv['gverts'] = set(gidx)
        k, tl = self.tiles(gmask)
        lv['ntiles'] = k; lv['tile'] = tl
        owner = {}
        for e in range(g.m):
            t = tl[e]
            if t in owner and owner[t] != label[e]:
                self.fail('Claim2: tile with two labels', (t, owner[t], label[e]))
            owner[t] = label[e]
        lv['owner'] = owner
        if len(gl):
            faces, rv = g.gamma_faces(gmask)
            if len(faces) != k:
                self.fail('Fact1: #faces of Gamma != #tiles', (len(faces), k))
            order = {}
            for walk in faces:
                ports = [(v, int(g.cj[c])) for (v, c) in walk]
                tset = {tl[g.e(v, g.rot[v][j])] for (v, j) in ports}
                if len(tset) != 1:
                    self.fail('Fact1: face meets several tiles')
                t = tset.pop()
                if t in order:
                    self.fail('Fact1: tile has two faces')
                if len(set(ports)) != len(ports):
                    self.fail('T3: port visited twice')
                order[t] = ports
            lv['order'] = order
        else:
            lv['order'] = {0: []}
        return lv

    def node(self, lv, v, e_other):
        j = self.g.idx[v][e_other]
        s = self.sector_open(lv['gidx'], v, j)
        return ('i', v) if s is None else ('p', v, s)

    def piece(self, lv, t, edges):
        g = self.g
        arcs = {}; und = nx.Graph()
        for e in edges:
            a, c = g.ends[e]
            na, nc = self.node(lv, a, c), self.node(lv, c, a)
            add_arc(arcs, na, nc, g.w[(a, c)]); add_arc(arcs, nc, na, g.w[(c, a)])
            und.add_edge(na, nc)
        return arcs, und

    def run(self):
        g, cfg = self.g, self.cfg
        label = np.zeros(g.m, int)
        gmask = np.zeros(g.nc, bool)
        self.levels = [self.mk_level(gmask, label)]
        self.levels[0]['tiles_of'] = {0: [0]}
        d = 0
        level_bags = [0]
        while level_bags and d < cfg['maxdepth']:
            cur = self.levels[d]
            nonleaf = []
            for b in level_bags:
                B = self.bags[b]
                if len(B['X']) <= cfg['leaf']:
                    B['kids'] = []; continue
                res = self.choose_and_split(b, cur)
                if res is None:
                    B['kids'] = []; self.st['forced_leaf'] += 1; continue
                self.verify_G1(b, res)
                self.lp46(b, res)
                others = [v for v in range(g.n) if v not in B['X']]
                if others and pip(g.pos[others], g.pos[res['q']]).any():
                    self.st['separator_encloses_foreign_vertex'] += 1
                self.st['separators'] += 1
                B.update(S=res['S'], q=res['q'], real=res['real'], TX=res['TX'], W=res['W'],
                         chords=res['chords'], ins=res['ins'], out=res['out'], mode=res['mode'])
                self.st['virtual_closings'] += (not res['real'])
                self.st['degenerate_kids'] += res['ndeg']
                self.mx['T[X]_components'] = max(self.mx['T[X]_components'], res['ncompT'])
                B['kids'] = []
                for i, Y in enumerate(res['kids']):
                    zc = {w: B['z'][w] for w in Y if w in B['z'] and w not in res['S']}
                    for s in res['S'] & Y:
                        os_, oe = res['W'][s]
                        if i == 0:
                            zc[s] = os_ + ((oe - os_) % TAU) / 2
                        else:
                            zc[s] = oe + ((os_ - oe) % TAU) / 2
                    nb = len(self.bags)
                    self.bags[nb] = dict(X=Y, parent=b, depth=d + 1, z=zc, kids=None, kind='in' if i == 0 else 'out')
                    B['kids'].append(nb)
                nonleaf.append(b)
            if not nonleaf:
                break
            nxt = self.step(d, cur, nonleaf)
            self.levels.append(nxt)
            level_bags = [k for b in nonleaf for k in self.bags[b]['kids']]
            d += 1
        self.maxd = d
        return self.st

    # ------------------------------------------------------------ one level of the construction
    def rails(self, path, label, b):
        g = self.g; out = set()
        for u, w in zip(path, path[1:]):
            e = g.e(u, w)
            if label[e] != b:
                continue
            iu = g.idx[u][w]; iw = g.idx[w][u]
            out.add(int(g.cbase[u] + (iu + 1) % g.deg[u])); out.add(int(g.cbase[w] + iw))
        return out

    def step(self, d, cur, nonleaf):
        g, cfg = self.g, self.cfg
        label = cur['label']; gmask = cur['gmask']; gverts = cur['gverts']
        newlabel = label.copy()
        N = {}; Nnew = {}
        for b in nonleaf:
            B = self.bags[b]; X, S, q = B['X'], B['S'], B['q']
            kid_of = {}
            for kb in B['kids']:
                for x in self.bags[kb]['X'] - S:
                    kid_of[x] = kb
            inkid = B['kids'][0]
            mine = np.nonzero(label == b)[0]
            for e in mine:
                a, c = g.ends[e]
                if a not in X or c not in X:
                    self.fail('Claim1: label outside bag', (e, b))
                if a not in S:
                    newlabel[e] = kid_of[a]
                elif c not in S:
                    newlabel[e] = kid_of[c]
                else:
                    newlabel[e] = inkid
                Y = self.bags[newlabel[e]]['X']
                if a not in Y or c not in Y:
                    self.fail('Claim1: new label misses an end', e)
            new = set()
            # L_X with Claim 7 count
            Ltot = 0
            for s in S:
                r = g.rot[s]; cnt = 0
                for j in range(len(r)):
                    e1, e2 = g.e(s, r[j - 1]), g.e(s, r[j])
                    if label[e1] == b and label[e2] == b and newlabel[e1] != newlabel[e2]:
                        new.add(int(g.cbase[s] + j)); cnt += 1
                cs = B['chords'][s]
                Ltot += cnt
                self.st['claim7_vertex_checks'] += 1
                self.mx['L_minus_2cs_max'] = max(self.mx['L_minus_2cs_max'], cnt - 2 * cs)
                self.mx['L_per_vertex_max'] = max(self.mx['L_per_vertex_max'], cnt)
                if cnt > 4 + 2 * cs:
                    self.fail('Claim7: > 4+2c_s label changes', (b, s, cnt, cs))
            nch = sum(B['chords'].values()) // 2
            if nch > len(S) - 2:
                self.fail('Claim7: more than |S|-2 outside chords', (nch, len(S)))
            if Ltot > 8 * len(S):
                self.fail('Claim7: |L_A| > 8|S_A|', (Ltot, len(S)))
            self.mx['L_over_S_max'] = max(self.mx['L_over_S_max'], Ltot / len(S))
            Lset = set(new)
            # Q_X
            Qset = self.rails(q, label, b)
            new |= Qset
            qe = [g.e(q[i], q[i + 1]) for i in range(len(q) - 1)]
            allX = all(label[e] == b for e in qe)
            Pset = set(); plen = 0
            if d >= 1 and allX and not (set(q) & gverts):
                TX = B['TX']
                targets = gverts & X
                if not targets:
                    self.fail('Claim3: no Gamma vertex in bag')
                par = {v: None for v in q}; dq = collections.deque(q); hit = None
                while dq:
                    x = dq.popleft()
                    if x in targets:
                        hit = x; break
                    for y in TX[x]:
                        if y not in par:
                            par[y] = x; dq.append(y)
                if hit is None:
                    self.fail('Claim3: p_X does not exist')
                path = [hit]
                while par[path[-1]] is not None:
                    path.append(par[path[-1]])
                path = path[::-1]
                for x in path[1:-1]:
                    if x in gverts:
                        self.fail('Claim3: p_X interior on Gamma_d')
                for u, w in zip(path, path[1:]):
                    if label[g.e(u, w)] != b:
                        self.fail('Claim3: p_X edge not labelled X', (b, u, w))
                Pset = self.rails(path, label, b)
                if self.cfg['neg'] == 'noP':
                    Pset = set()
                new |= Pset
                plen = len(path) - 1
                self.st['P_used'] += 1
                self.mx['p_len_max'] = max(self.mx['p_len_max'], plen)
                diam = tree_diam(TX)
                self.mx['p_len_over_diamTX'] = max(self.mx['p_len_over_diamTX'], plen / max(1, diam))
                B['plen'] = plen
            if self.cfg['neg'] == 'dropL' and Lset and self.rng.random() < 0.5:
                c = next(iter(Lset))
                if not gmask[c]:
                    new.discard(c); self.st['neg_dropped_L'] += 1
            N[b] = new
            Nnew[b] = {c for c in new if not gmask[c]}
            B['N'] = len(new); B['Nnew'] = len(Nnew[b]); B['L'] = len(Lset); B['Q'] = len(Qset); B['P'] = len(Pset)
            diam = tree_diam(B['TX'])
            B['diamTX'] = diam
            bound = 8 * len(S) + 2 * (len(q) - 1) + 2 * plen
            if len(new) > bound:
                self.fail('Claim7: |N_A| over 8|S|+2|q|+2|p|', (len(new), bound))
            self.mx['N_over_S_plus_diam'] = max(self.mx['N_over_S_plus_diam'], len(new) / (len(S) + diam))
            for c in Nnew[b]:
                v = int(g.cv[c]); j = int(g.cj[c]); r = g.rot[v]
                if label[g.e(v, r[j - 1])] != b or label[g.e(v, r[j])] != b:
                    self.fail('Claim2b: new corner not inside a tile of X', (b, v, j))
        seen = {}
        for b in nonleaf:
            for c in Nnew[b]:
                if c in seen:
                    self.fail('Claim2b: N_X overlap', (b, seen[c]))
                seen[c] = b
                self.adder[c] = b
        gm2 = gmask.copy()
        for b in nonleaf:
            for c in N[b]:
                gm2[c] = True
        # Claim 1: labels move down
        for e in range(g.m):
            l0, l1 = label[e], newlabel[e]
            if l1 != l0 and self.bags[l1]['parent'] != l0:
                self.fail('Claim1: label jumped')
        # Gamma connected (R-subgraph)
        gl = np.nonzero(gm2)[0]
        A = coo_matrix((np.ones(len(gl)), (g.cv[gl], g.n + g.cface[gl])), shape=(g.n + g.nf, g.n + g.nf))
        used = np.unique(np.concatenate([g.cv[gl], g.n + g.cface[gl]]))
        k, lab = connected_components(A, directed=False)
        if len(set(lab[used])) != 1:
            self.fail('Claim3: Gamma disconnected', (d + 1, len(set(lab[used]))))
        nxt = self.mk_level(gm2, newlabel)
        self.st['levels'] += 1
        self.check_level(d, cur, nxt, nonleaf)
        return nxt

    # ------------------------------------------------------------ checks per level
    def check_level(self, d, cur, nxt, nonleaf):
        g = self.g
        label = cur['label']; nl = nxt['label']
        # Claim 4 (+consequence) for every bag at depth d (non-leaf) and depth d+1 (all)
        for b in nonleaf:
            B = self.bags[b]; X = B['X']; dS = self.dss(b)
            for v in dS | B['S']:
                if any(label[g.e(v, u)] == b for u in g.rot[v]):
                    if v not in nxt['gverts']:
                        self.fail('Claim4: hub with X-edge not on Gamma_{d+1}', (b, v))
                    if v in dS and d >= 1 and v not in cur['gverts']:
                        self.fail('Claim4: dS* hub with X-edge not on Gamma_d', (b, v))
                    self.st['hub_checks'] += 1
        kids = [k for b in nonleaf for k in self.bags[b]['kids']]
        tiles_of = collections.defaultdict(list)
        for t, o in nxt['owner'].items():
            tiles_of[o].append(t)
        nxt['tiles_of'] = tiles_of
        tile_edges = collections.defaultdict(list)
        for e in range(g.m):
            tile_edges[nxt['tile'][e]].append(e)
        nxt['tile_edges'] = tile_edges
        for y in kids:
            Y = self.bags[y]; X = Y['X']; dS = self.dss(y)
            # Claim 5
            nout = 0
            for (a, c) in g.ends:
                if a in X and c in X and nl[g.e(a, c)] != y:
                    nout += 1
                    if a not in dS or c not in dS:
                        self.fail('Claim5: outside edge leaves dS*', (y, a, c))
            k_ = len(dS); bnd = 3 * k_ - 6 if k_ >= 3 else k_ * (k_ - 1) // 2
            if nout > bnd:
                self.fail('Claim5: too many outside edges', (nout, len(dS)))
            # Claim 4 consequence for leaves too (hubs on Gamma_{d+1})
            for v in dS:
                if any(nl[g.e(v, u)] == y for u in g.rot[v]) and v not in nxt['gverts']:
                    self.fail('Claim4: dS* hub of child not on Gamma', (y, v))
            # T2: ports
            J = sum(len(nxt['order'][t]) for t in tiles_of.get(y, []))
            Y['J'] = J
            ancN = sum(self.bags[a]['Nnew'] for a in self.anc(y))
            if J > ancN:
                self.fail('T2: |J_X| > sum anc |N_A|', (y, J, ancN))
            # opening corners: injective, added by an ancestor
            anc = set(self.anc(y))
            for t in tiles_of.get(y, []):
                for (v, j) in nxt['order'][t]:
                    c = int(g.cbase[v] + j)
                    if self.adder.get(c) not in anc:
                        self.fail('T2: opening corner not added by an ancestor', (y, v, j, self.adder.get(c)))
            self.st['T2_checks'] += 1
            self.mx['J_over_sumN'] = max(self.mx['J_over_sumN'], J / max(1, ancN))
            self.mx['J_max'] = max(self.mx['J_max'], J)
        for b in nonleaf:
            B = self.bags[b]
            sJ = sum(self.bags[k].get('J', 0) for k in B['kids'])
            bound = sum(self.bags[a]['Nnew'] for a in self.anc(b) + [b])
            if sJ > bound:
                self.fail('T2: sum_i |J_Xi| > bound', (b, sJ, bound))
            self.mx['sumJkids_over_Sparent'] = max(self.mx['sumJkids_over_Sparent'], sJ / len(B['S']))
        # T3: pieces of every tile at d+1, Monge in sigma order + disk planarity
        for t, edges in tile_edges.items():
            arcs, und = self.piece(nxt, t, edges)
            ports = [('p', v, j) for (v, j) in nxt['order'][t]]
            for p in ports:
                if p not in und:
                    self.fail('T3: port without edge')
            for x in und.nodes():
                if x[0] == 'p' and x not in set(ports):
                    self.fail('T3: Gamma-copy missing from boundary walk')
            comps = list(nx.connected_components(und))
            for cc in comps:
                cp = [p for p in ports if p in cc]
                if not cp:
                    self.fail('Lemma15: component without port')
                if len(cp) >= 4:
                    cp2 = cp
                    if len(cp) > self.cfg['monge_cap']:
                        cp2 = cp[:self.cfg['monge_cap']]
                    nodes = sorted(cc, key=str)
                    sub = {k: v for k, v in arcs.items() if k[0] in cc}
                    D = sp_matrix(nodes, sub, cp2)
                    ix = [nodes.index(p) for p in cp2]
                    M = D[:, ix]
                    if self.cfg['neg'] == 'shuffle':
                        perm = list(range(len(cp2))); self.rng.shuffle(perm); M = M[np.ix_(perm, perm)]
                    if not np.isfinite(M).all():
                        self.fail('W2: infinite distance in a piece component')
                    worst, cnt = monge_check(M)
                    self.st['monge_ineqs'] += cnt
                    if worst > 1e-7:
                        if self.cfg['neg'] == 'shuffle':
                            self.st['neg_monge_detected'] += 1
                        else:
                            self.fail('T3: Monge violated in sigma order', worst)
                    elif self.cfg['neg'] == 'shuffle':
                        self.st['neg_monge_missed'] += 1
            # disk check: piece + outer vertex joined to ports + rim
            H = nx.Graph(und)
            for i, p in enumerate(ports):
                H.add_edge('OMEGA', p)
                if len(ports) > 2:
                    H.add_edge(p, ports[(i + 1) % len(ports)])
            if not nx.check_planarity(H)[0]:
                self.fail('T3: piece not disk-drawn in sigma order')
            self.st['tiles_checked'] += 1
        # T4 (a), (b), (c)
        for b in nonleaf:
            self.check_T4(d, cur, nxt, b)

    def check_T4(self, d, cur, nxt, b):
        g = self.g; B = self.bags[b]; X = B['X']
        label = cur['label']; nl = nxt['label']
        kids = set(B['kids'])
        child_tiles = [t for t, o in nxt['owner'].items() if o in kids]
        par_of = {}
        for t in child_tiles:
            es = nxt['tile_edges'][t]
            pt = {cur['tile'][e] for e in es}
            if len(pt) != 1:
                self.fail('T4: child tile spans two tiles of X')
            p = pt.pop()
            if cur['owner'][p] != b:
                self.fail('T4: child tile inside a tile not of X')
            par_of[t] = p
        # every edge of a tile of X lies in a child tile
        for e in np.nonzero(label == b)[0]:
            if nl[e] not in kids:
                self.fail('T4: edge of X tile not in child tile')
        # (b) glue map well defined; images of child ports cover parent ports; wheel planarity
        by_par = collections.defaultdict(list)
        for t, p in par_of.items():
            by_par[p].append(t)
        for p, subs in by_par.items():
            img_ports = set()
            Wg = nx.Graph()
            for t in subs:
                ports = nxt['order'][t]
                imgs = []
                for (v, j) in ports:
                    e_other = g.rot[v][j]       # first edge of the sector
                    im = self.node(cur, v, e_other) if d >= 1 else ('i', v)
                    # well-definedness: every edge of the child sector maps to the same Gamma_d sector
                    L = nxt['gidx'][v]; k = L.index(j); jn = L[(k + 1) % len(L)]
                    i = j
                    while True:
                        im2 = self.node(cur, v, g.rot[v][i % g.deg[v]]) if d >= 1 else ('i', v)
                        if im2 != im:
                            self.fail('T4b: child sector not inside one Gamma_d sector')
                        i += 1
                        if i % g.deg[v] == jn:
                            break
                    imgs.append(im); img_ports.add(im)
                if self.cfg['neg'] == 'wheel' and len(imgs) >= 4 and t == subs[0]:
                    imgs = imgs[:]; self.rng.shuffle(imgs)
                hub = ('hub', t)
                for i, x in enumerate(imgs):
                    Wg.add_edge(hub, x)
                    y = imgs[(i + 1) % len(imgs)]
                    if len(imgs) > 1 and x != y:
                        Wg.add_edge(x, y)
            if d >= 1:
                pports = [('p', v, j) for (v, j) in cur['order'][p]]
                for x in pports:
                    if x not in img_ports:
                        self.fail('T4b: port of tau is not a terminal image')
                for i, x in enumerate(pports):
                    Wg.add_edge('OUTER', x)
                    y = pports[(i + 1) % len(pports)]
                    if len(pports) > 1 and x != y:
                        Wg.add_edge(x, y)
            ok = nx.check_planarity(Wg)[0]
            if self.cfg['neg'] == 'wheel':
                self.st['neg_wheel_nonplanar' if not ok else 'neg_wheel_planar'] += 1
            elif not ok:
                self.fail('T4c: wheel gluing inside a tile of X not planar')
            self.st['T4b_gluings'] += 1
        # (a): H_X wheel model (hubs to vertex images) + outside edges
        dS = self.dss(b)
        Hg = nx.Graph()
        for t in child_tiles:
            ports = nxt['order'][t]
            vs = [v for (v, j) in ports]
            for i, v in enumerate(vs):
                Hg.add_edge(('hub', t), v)
                u = vs[(i + 1) % len(vs)]
                if len(vs) > 1 and u != v:
                    Hg.add_edge(v, u)
        nout = 0
        for (a, c) in g.ends:
            if a in X and c in X and label[g.e(a, c)] != b:
                Hg.add_edge(a, c); nout += 1
        if not nx.check_planarity(Hg)[0] and self.cfg['neg'] != 'wheel':
            self.fail('T4c: H_X wheel model not planar')
        # every vertex of dS+ is a terminal image
        timg = set(v for t in child_tiles for (v, j) in nxt['order'][t])
        for (a, c) in g.ends:
            if a in X and c in X and label[g.e(a, c)] != b:
                timg |= {a, c}
        for v in dS | B['S']:
            if v not in timg:
                self.fail('T4a: hub not a terminal image', (b, v))
        self.st['H_checks'] += 1
