"""An incision model of [18] written without the token labels of Definition R.

A node-part is a disc. Its boundary is a cyclic list of items:
   ('H', hid)  a dual half-edge copy (one side of one dart, or half of it), and
   ('S', tags) a seam: a stretch of boundary created by cutting along an incised path.
Adjacent seams are merged. A node-part without seams is a whole face.

A dual edge copy is a pair of half-edges (partner links). Cutting a node-part along a chord
between two boundary points gives two discs. The copies of a newly incised dual edge are
assigned by side: the copy that lies on the left of the path at one end is the copy on the left
at the other end. Left is the side reached from the arrival point going forward in the dual
rotation (face walk order), which is the same geometric side at every node because every dual
rotation is read in the same sense. Nothing here uses the rule {(d,1),(rev d,2)} of R1; the
comparison with Definition R is done afterwards.

Half-edge kinds: 'all' (whole dart side), 'tail' (the half of the dart side before the
crossing point in walk order), 'head' (the half after it).

Boundary points:
   ('mid', hid)   middle of a whole half-edge (new incision of its dual edge),
   ('old', hid)   an already split half-edge, crossed next to its adjacent seam,
   ('gap', hid)   the corner gap right after half-edge hid (corner cut of gamma at s or t),
   ('seam', k)    inside the seam item at index k (endpoint of an incised path).
"""
import collections, itertools


class HE:
    __slots__ = ('hid', 'dart', 'kind', 'partner', 'node')

    def __init__(self, hid, dart, kind):
        self.hid, self.dart, self.kind = hid, dart, kind
        self.partner = None
        self.node = None


class NPart:
    __slots__ = ('nid', 'face', 'items', 'anc', 'parent')

    def __init__(self, nid, face, items, anc, parent):
        self.nid, self.face, self.items, self.anc, self.parent = nid, face, items, anc, parent


class Model:
    def __init__(self, emb):
        self.emb = emb
        self.he = {}
        self.np = {}
        self.hctr = 0
        self.nctr = 0
        self.incised = set()   # primal edges incised so far
        self.flags = collections.Counter()
        self.notes = []
        # level 0: one node-part per face, one half-edge per dart
        hof = {}
        for d in range(2 * emb.m):
            hof[d] = self.new_he(d, 'all')
        for d in range(2 * emb.m):
            self.he[hof[d]].partner = hof[d ^ 1]
        for f, cyc in enumerate(emb.faces):
            items = [('H', hof[d]) for d in cyc]
            self.new_np(f, items, ('f', f), None)

    def flag(self, k, note=None):
        self.flags[k] += 1
        if note is not None and len(self.notes) < 30:
            self.notes.append((k, str(note)[:400]))

    def new_he(self, d, kind):
        self.hctr += 1
        self.he[self.hctr] = HE(self.hctr, d, kind)
        return self.hctr

    def new_np(self, face, items, anc, parent):
        self.nctr += 1
        X = NPart(self.nctr, face, items, anc, parent)
        self.np[self.nctr] = X
        for it in items:
            if it[0] == 'H':
                self.he[it[1]].node = self.nctr
        return self.nctr

    # ------------------------------------------------------------ splitting
    @staticmethod
    def merge_seams(items):
        """merge cyclically adjacent seams."""
        if not items:
            return items
        out = []
        for it in items:
            if it[0] == 'S' and out and out[-1][0] == 'S':
                out[-1] = ('S', out[-1][1] | it[1])
            else:
                out.append(it)
        if len(out) > 1 and out[0][0] == 'S' and out[-1][0] == 'S':
            out[0] = ('S', out[0][1] | out[-1][1])
            out.pop()
        return out

    def split(self, nid, p1, p2, tag, newcopy):
        """cut node-part nid along a chord from p1 to p2. Returns (plus, minus) node ids
        (None if that side has no half-edge). plus = from p1 forward to p2 (left of a path
        arriving at p1 and leaving at p2). newcopy: dict hid -> {'plus':h, 'minus':h} filled
        for 'mid' points."""
        X = self.np[nid]
        items = X.items
        k = len(items)
        idx = {it[1]: j for j, it in enumerate(items) if it[0] == 'H'}

        # Represent the boundary as a cyclic list of 'slots'; a point is a slot boundary.
        # Expand: each item becomes one or two atoms; points are between atoms.
        atoms = []   # (kind, payload)
        for j, it in enumerate(items):
            if it[0] == 'S':
                atoms.append(('S1', j))
                atoms.append(('S2', j))
            else:
                atoms.append(('H', it[1]))

        def where(p):
            """index in atoms such that the point lies just before atoms[index] (cyclic);
            for 'mid' the half-edge atom is split: returns ('mid', index of its atom)."""
            kind, val = p
            if kind == 'seam':
                return ('cut', [a for a, at in enumerate(atoms) if at == ('S2', val)][0])
            hid = val
            a = [a for a, at in enumerate(atoms) if at == ('H', hid)]
            if not a:
                raise KeyError(('point_not_in_node', p, nid))
            a = a[0]
            if kind == 'gap':
                return ('cut', (a + 1) % len(atoms))
            if kind == 'mid':
                return ('mid', a)
            if kind == 'old':
                # crossed next to the adjacent seam: on the seam side of the half-edge
                h = self.he[hid]
                nxt = atoms[(a + 1) % len(atoms)]
                prv = atoms[(a - 1) % len(atoms)]
                sn = nxt[0] in ('S1', 'S2')
                sp = prv[0] in ('S1', 'S2')
                if h.kind == 'tail':
                    if not sn:
                        self.flag('old_tail_not_before_seam', (nid, hid))
                    return ('cut', (a + 1) % len(atoms))
                if h.kind == 'head':
                    if not sp:
                        self.flag('old_head_not_after_seam', (nid, hid))
                    return ('cut', a)
                self.flag('old_on_whole_halfedge', (nid, hid))
                return ('mid', a)
            raise ValueError(p)
        w1, w2 = where(p1), where(p2)
        n = len(atoms)
        # build linear walk starting at p1
        seq = []
        if w1[0] == 'mid':
            start = w1[1]
            h = atoms[start][1]
            seq.append(('HH', h))        # head half of h starts plus side
            j = (start + 1) % n
        else:
            j = w1[1]
        # walk until p2
        plus = []
        plus += seq
        minus_tail = None
        steps = 0
        while True:
            if w2[0] == 'cut' and j == w2[1] and (steps > 0 or w1 != w2):
                break
            if w2[0] == 'mid' and j == w2[1]:
                h = atoms[j][1]
                plus.append(('HT', h))    # tail half ends plus side
                minus_start = ('HH', h)
                j = (j + 1) % n
                break
            plus.append(atoms[j])
            j = (j + 1) % n
            steps += 1
            if steps > n + 2:
                raise RuntimeError('split walk')
        minus = []
        if w2[0] == 'mid':
            minus.append(minus_start)
        # continue to p1
        steps = 0
        while True:
            if w1[0] == 'cut' and j == w1[1]:
                break
            if w1[0] == 'mid' and j == w1[1]:
                h = atoms[j][1]
                minus.append(('HT', h))
                break
            minus.append(atoms[j])
            j = (j + 1) % n
            steps += 1
            if steps > n + 2:
                raise RuntimeError('split walk 2')

        def realize(lst, side):
            out = []
            for at in lst:
                if at[0] == 'H':
                    out.append(('H', at[1]))
                elif at[0] in ('HH', 'HT'):
                    h0 = self.he[at[1]]
                    if h0.kind != 'all':
                        self.flag('mid_on_split_halfedge', at[1])
                    kind = 'head' if at[0] == 'HH' else 'tail'
                    nh = self.new_he(h0.dart, kind)
                    newcopy.setdefault(at[1], {})[side] = nh
                    out.append(('H', nh))
                elif at[0] == 'S1':
                    out.append(('S', items[at[1]][1]))
                elif at[0] == 'S2':
                    out.append(('S', items[at[1]][1]))
            out.append(('S', frozenset([tag])))
            return self.merge_seams(out)
        pi = realize(plus, 'plus')
        mi = realize(minus, 'minus')
        del self.np[nid]
        res = []
        for lst in (pi, mi):
            if any(it[0] == 'H' for it in lst):
                res.append(self.new_np(X.face, lst, X.anc, nid))
            else:
                res.append(None)
        return res

    # ------------------------------------------------------------ incision along a path
    def incise_path(self, nodes, hes, tag, start_pt, end_pt):
        """nodes g_0..g_r, hes[k] = half-edge at g_k leading to g_{k+1} (its partner is at
        g_{k+1}). start_pt / end_pt: boundary points at g_0 / g_r where the cut meets the
        boundary (None: the seam of the node; must be unique).
        Returns dict old node -> (plus, minus)."""
        r = len(nodes) - 1
        newedge = []
        for k in range(r):
            h = self.he[hes[k]]
            newedge.append(h.kind == 'all')
            if h.kind == 'all':
                self.incised.add(h.dart >> 1)
        newcopy = {}
        res = {}
        for k, g in enumerate(nodes):
            pts = []
            # arrival
            if k == 0:
                p1 = start_pt
            else:
                a = self.he[hes[k - 1]].partner
                p1 = ('mid', a) if newedge[k - 1] else ('old', a)
            if k == r:
                p2 = end_pt
            else:
                b = hes[k]
                p2 = ('mid', b) if newedge[k] else ('old', b)
            if p1 is None or p2 is None:
                X = self.np[g]
                sk = [j for j, it in enumerate(X.items) if it[0] == 'S']
                if len(sk) != 1:
                    self.flag('endpoint_seam_count_%d' % len(sk), (g, X.items))
                    if not sk:
                        raise RuntimeError('endpoint without seam')
                if p1 is None:
                    p1 = ('seam', sk[0])
                else:
                    p2 = ('seam', sk[0])
            res[g] = self.split(g, p1, p2, tag, newcopy)
        self.last_newcopy = newcopy
        # partners of new copies: plus with plus, minus with minus
        for k in range(r):
            if not newedge[k]:
                continue
            b = hes[k]
            a = self.he[b].partner
            for side in ('plus', 'minus'):
                hb = newcopy[b][side]
                ha = newcopy[a][side]
                self.he[hb].partner = ha
                self.he[ha].partner = hb
        return res

    # ------------------------------------------------------------ level 1 (gamma)
    def incise_gamma(self, pf, pe, cs, ct):
        """pf: faces p_0..p_m, pe[k] (k=1..m): primal edge e_k. cs, ct: cut corners.
        Returns dict (k, side) -> node id, side 0 = plus (left of gamma)."""
        emb = self.emb
        m = len(pf) - 1
        node_of_face = {X.face: nid for nid, X in self.np.items()}
        hes_by_dart = {self.he[h].dart: h for h in self.he}
        nodes = [node_of_face[f] for f in pf]
        hes = []
        for k in range(1, m + 1):
            e = pe[k]
            d = 2 * e if emb.face_of[2 * e] == pf[k - 1] else 2 * e + 1
            assert emb.face_of[d] == pf[k - 1] and emb.face_of[d ^ 1] == pf[k]
            hes.append(hes_by_dart[d])
        sp = ('gap', hes_by_dart[emb.din(cs)])
        tp = ('gap', hes_by_dart[emb.din(ct)])
        if m == 0:
            # one chord in p_0 from c*_s to c*_t
            g = nodes[0]
            pl, mi = self.split(g, sp, tp, 'P', {})
            res = {g: (pl, mi)}
        else:
            res = self.incise_path(nodes, hes, 'P', sp, tp)
        out = {}
        for k, g in enumerate(nodes):
            pl, mi = res[g]
            out[(k, 0)] = pl
            out[(k, 1)] = mi
            for side, x in ((0, pl), (1, mi)):
                if x is None:
                    self.flag('gamma_empty_side', (k, side))
                else:
                    self.np[x].anc = ('p', k, side)
        return out

    # ------------------------------------------------------------ graph helpers
    def tokens_of(self, nid):
        """token sequence (dart, label) of a node-part, starting after its seam."""
        X = self.np[nid]
        items = X.items
        sk = [j for j, it in enumerate(items) if it[0] == 'S']
        if sk:
            j0 = sk[0]
            items = items[j0 + 1:] + items[:j0]
        lab = {'all': 0, 'tail': 1, 'head': 2}
        return [(self.he[it[1]].dart, lab[self.he[it[1]].kind]) for it in items if it[0] == 'H'], len(sk)

    def components(self, nids):
        nids = set(nids)
        comp = {}
        c = 0
        for x in nids:
            if x in comp:
                continue
            c += 1
            comp[x] = c
            st = [x]
            while st:
                y = st.pop()
                for it in self.np[y].items:
                    if it[0] != 'H':
                        continue
                    z = self.he[self.he[it[1]].partner].node
                    if z not in nids:
                        self.flag('component_leaves_set', (y, z))
                        continue
                    if z not in comp:
                        comp[z] = c
                        st.append(z)
        return comp

    def adj(self, nids, w):
        """adjacency over node-parts in nids: list of (nbr, weight, out-halfedge)."""
        A = {x: [] for x in nids}
        for x in nids:
            for it in self.np[x].items:
                if it[0] != 'H':
                    continue
                h = self.he[it[1]]
                y = self.he[h.partner].node
                if y in A:
                    A[x].append((y, w(h.dart >> 1), it[1]))
        return A
