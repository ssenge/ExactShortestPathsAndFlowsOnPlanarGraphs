"""Chooser library for Lemma S / Lemma O (RECURSION.md, LEMMA_O.md).

Runs the driver with all Lemma O and extra checks (thmD_SO.py = checkO/thmD_R.py + hooks,
written by patchSO.py) and replaces every exact shortest path the recursion takes (the level-0
path P and every P_i) by one chosen by an chooser among ALL w-shortest paths of the annulus.

  * SPDag: all w-shortest src->tgt paths in an annulus (w = K c + 1, K = 10^9, i.e. the
    lexicographic order (c, hops) that the driver's K = |V(G^)| + 1 also gives; checked: the
    driver's own path is always one of them);
  * ChoiceRng: choice() is a branching point; explore() runs the recursion once for every
    sequence of choices (f, g, corners and modes (anycorner), P, every P_i, the overlap source z),
    i.e. it enumerates all runs of the recursion on an instance (up to a cap);
  * Chooser policies for the worst-case (non-exhaustive) mode;
  * stress counters per incision (INC_HOOK) and per child (CHILD_HOOK);
  * optional topological test of the curve model (geo.py).
THMD_VARIANT=F uses the whole-path overlap reading (checkO/thmD_F.py).
"""
import os
import sys
import random
import heapq
import collections

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
REPO_REF = os.path.join(HERE, '..', '..', 'ExactShortestPathsAndFlowsOnPlanarGraphs', 'sim', 'thmD', 'checkO')
_VAR = os.environ.get('THMD_VARIANT', 'R')
_SRC, _DST = (('thmD_F.py', 'thmD_SOF.py') if _VAR == 'F' else ('thmD_R.py', 'thmD_SO.py'))
SO = os.path.join(HERE, _DST)
if not os.path.exists(SO):
    import subprocess
    srcp = os.path.join(HERE, '..', 'checkO', _SRC)
    if not os.path.exists(srcp):
        srcp = os.path.join(REPO_REF, _SRC)
    subprocess.check_call([sys.executable, '-I', os.path.join(HERE, 'patchSO.py'), srcp, SO])
if _VAR == 'F':
    import thmD_SOF as T
else:
    import thmD_SO as T

KB = 10 ** 9
IGNORE = ('dev_', 'xa_', 'xb_', 'deg_')


# ---------------------------------------------------------------- shortest-path DAG of an annulus
def ann_adj(A, emb):
    adj = {x: [] for x in A.nodes}
    for X in A.nodes.values():
        for ld in X.seq:
            pl = T.partner(ld)
            y = A.ldmap[pl]
            adj[X.id].append((y, KB * emb.cap[ld[0] >> 1] + 1, ld, pl))
    return adj


def dijk(adj, s):
    dist = {s: 0}
    pq = [(0, s)]
    done = set()
    while pq:
        d, x = heapq.heappop(pq)
        if x in done:
            continue
        done.add(x)
        for y, w, _, _ in adj[x]:
            nd = d + w
            if nd < dist.get(y, float('inf')):
                dist[y] = nd
                heapq.heappush(pq, (nd, y))
    return dist


class SPDag:
    def __init__(self, A, emb, src, tgt):
        adj = ann_adj(A, emb)
        dS = dijk(adj, src)
        dT = dijk(adj, tgt)
        D = dS[tgt]
        self.D = D
        self.src, self.tgt = src, tgt
        self.out = collections.defaultdict(list)
        for x, lst in adj.items():
            if x not in dS:
                continue
            for y, w, ld, pl in lst:
                if y in dT and dS[x] + w + dT[y] == D:
                    self.out[x].append((y, ld, pl))
        order = sorted((x for x in dS if x in dT and dS[x] + dT[x] == D), key=lambda z: -dS[z])
        cnt = {}
        for x in order:
            cnt[x] = 1 if x == tgt else sum(cnt.get(y, 0) for y, _, _ in self.out[x])
        self.cnt = cnt
        self.count = cnt.get(src, 0)

    def enum(self, cap):
        res = []

        def rec(x, nodes, edges):
            if len(res) >= cap:
                return
            if x == self.tgt:
                res.append((list(nodes), list(edges)))
                return
            for y, ld, pl in self.out[x]:
                nodes.append(y)
                edges.append((ld, pl))
                rec(y, nodes, edges)
                nodes.pop()
                edges.pop()
        rec(self.src, [self.src], [])
        return res

    def sample(self, rng):
        x = self.src
        nodes, edges = [x], []
        while x != self.tgt:
            opts = [(y, ld, pl) for y, ld, pl in self.out[x] if self.cnt.get(y, 0) > 0]
            r = rng.randrange(sum(self.cnt[y] for y, _, _ in opts))
            for y, ld, pl in opts:
                if r < self.cnt[y]:
                    break
                r -= self.cnt[y]
            nodes.append(y)
            edges.append((ld, pl))
            x = y
        return nodes, edges

    def paths(self, cap, rng):
        """all tight paths if at most cap, else up to cap uniform samples (deduplicated)."""
        if self.count <= cap:
            return self.enum(cap), False
        seen = {}
        for _ in range(3 * cap):
            p = self.sample(rng)
            seen[tuple(p[1])] = p
            if len(seen) >= cap:
                break
        return list(seen.values()), True


# ---------------------------------------------------------------- rng that branches
class ChoiceRng:
    """choice() is a branching point (driven by a prefix; default index 0); randrange()/random()
    come from an ordinary Random (they only pick the side b of a tree root or thresholds)."""

    def __init__(self, prefix, seed):
        self.prefix = prefix
        self.trace = []
        self.r = random.Random(seed)

    def choice(self, seq):
        seq = list(seq)
        n = len(seq)
        if n == 0:
            raise IndexError('choice from empty sequence')
        if n == 1:
            return seq[0]
        k = len(self.trace)
        idx = self.prefix[k] if k < len(self.prefix) else 0
        self.trace.append((idx, n))
        return seq[idx]

    def randrange(self, *a):
        return self.r.randrange(*a)

    def random(self):
        return self.r.random()

    def randint(self, a, b):
        return self.r.randint(a, b)

    def shuffle(self, x):
        return self.r.shuffle(x)

    def sample(self, *a):
        return self.r.sample(*a)


# ---------------------------------------------------------------- path features and policies
def path_feats(ctx, A, nodes, edges):
    bn = set()
    for ch in (A.left, A.right):
        if ch is not None:
            bn |= set(ch['nodes'])
    anc = [ctx.store[x].anc for x in nodes]
    tidx = [a[1] for a in anc if a[0] == 'p']
    nP = len(tidx)
    span = (max(tidx) - min(tidx)) if tidx else 0
    ov = sum(1 for x in nodes if x in bn)
    old = sum(1 for la, lb in edges if la != 'MERGED' and la[1] != 0)
    xeqy = lin = qold = wig = 0
    try:
        last0 = max(k for k, a in enumerate(anc) if a[0] == 'p' and a[2] == 0)
        first1 = min(k for k, a in enumerate(anc) if k > last0 and a[0] == 'p' and a[2] == 1)
        xeqy = int(anc[last0][1] == anc[first1][1])
        lin = sum(1 for x in nodes[last0 + 1:first1] if not ctx.store[x].cyc)
        qold = sum(1 for la, lb in edges[last0:first1] if la[1] != 0)
        wig = sum(1 for k in range(last0) if anc[k][0] == 'p' and anc[k][2] == 1)
        wig += sum(1 for k in range(first1 + 1, len(anc)) if anc[k][0] == 'p' and anc[k][2] == 0)
    except ValueError:
        pass
    return dict(ov=ov, old=old, nP=nP, span=span, xeqy=xeqy, lin=lin, qold=qold, wig=wig, hops=len(edges))


POLICIES = {
    'rand': None,
    'maxbound': lambda f: (f['ov'] + f['old'], f['lin']),
    'minbound': lambda f: (-f['ov'] - f['old'],),
    'alongQ': lambda f: (f['qold'] + f['lin'], f['ov']),
    'maxP': lambda f: (f['nP'], f['wig']),
    'minP': lambda f: (-f['nP'],),
    'minspan': lambda f: (-f['span'],),
    'maxspan': lambda f: (f['span'],),
    'xeqy': lambda f: (f['xeqy'], f['ov']),
    'xneqy': lambda f: (-f['xeqy'], f['span']),
    'wiggle': lambda f: (f['wig'], f['nP']),
    'dropmin': None,   # needs lambda: maximise argmin indices of lambda strictly inside (i1, i2) and the range
    'outside': None,   # maximise how far i1, i2 lie outside [j_A, k_A]
}


class Chooser:
    """PATH_HOOK. mode 'branch': every tight path is a branch of the ChoiceRng (exhaustive);
    mode 'policy': pick by a policy (per decision, a random one from self.pols)."""

    def __init__(self, mode='policy', pols=('rand',), cap=64, branch_leaf=False, prng=None, cnt=None):
        self.mode = mode
        self.pols = list(pols)
        self.cap = cap
        self.branch_leaf = branch_leaf
        self.prng = prng or random.Random(0)
        self.cnt = cnt if cnt is not None else collections.Counter()
        self.lam = None
        self.on_P = None

    def __call__(self, role, ctx, A, src, tgt, nodes, edges, emb, rng, i):
        dag = SPDag(A, emb, src, tgt)
        self.cnt['paths_' + role] += 1
        if dag.count > 1:
            self.cnt['ties_' + role] += 1
        if dag.count == 0:
            self.cnt['dag_empty'] += 1
            return nodes, edges
        okd = nodes and nodes[0] == src and nodes[-1] == tgt and all(
            any(y == nodes[k + 1] and (ld, pl) == tuple(edges[k]) for y, ld, pl in dag.out[nodes[k]])
            for k in range(len(edges)))
        if not okd:
            self.cnt['driver_path_not_tight_' + role] += 1
        if role == 'Pi' and A.level == 1:
            adj = ann_adj(A, emb)
            mm = max(t for (t, b) in A.piece)
            self.lam = {t: dijk(adj, A.piece[(t, 0)])[A.piece[(t, 1)]] for t in range(mm + 1)}
        res = self._pick(role, ctx, A, src, tgt, nodes, edges, emb, rng, i, dag)
        if [tuple(e) for e in res[1]] != [tuple(e) for e in edges]:
            self.cnt['changed_' + role] += 1
        if role == 'P' and self.on_P is not None:
            self.on_P(ctx, res[0], res[1])
        return res

    def _pick(self, role, ctx, A, src, tgt, nodes, edges, emb, rng, i, dag):
        if self.mode == 'branch' and (role != 'leaf' or self.branch_leaf):
            ps, trunc = dag.paths(self.cap, self.prng)
            if trunc:
                self.cnt['branch_trunc'] += 1
            ps.sort(key=lambda p: [tuple(e) for e in p[1]])
            return rng.choice(ps)
        if role in ('leaf', 'P'):
            return dag.sample(self.prng)
        pol = self.prng.choice(self.pols)
        if pol == 'rand':
            return dag.sample(self.prng)
        ps, trunc = dag.paths(self.cap, self.prng)
        if pol in ('dropmin', 'outside'):
            lam = self.lam or {}
            Lmin = min(lam.values()) if lam else None

            def key(n_):
                tid = [ctx.store[x].anc[1] for x in n_ if ctx.store[x].anc[0] == 'p']
                i1, i2 = min(tid), max(tid)
                out = max(0, A.j - i1) + max(0, i2 - A.k)
                if pol == 'dropmin':
                    return (sum(1 for t in range(max(i1 + 1, A.j), min(i2 - 1, A.k) + 1) if lam.get(t) == Lmin), out)
                return (out, i2 - i1)
            scored = [(key(n_), self.prng.random(), k) for k, (n_, e_) in enumerate(ps)]
        else:
            kf = POLICIES[pol]
            scored = [(kf(path_feats(ctx, A, n_, e_)), self.prng.random(), k) for k, (n_, e_) in enumerate(ps)]
        scored.sort(reverse=True)
        return ps[scored[0][2]]


# ---------------------------------------------------------------- stress conditions
def inc_hook_factory(S):
    def inc_hook(A, i, Pn_, Pe_, Qn, Qe, xt, yt, i1, i2, ov, pieces, newnodes, comp, stats, level):
        S['inc'] += 1
        both = A.left is not None and A.right is not None
        if both:
            S['both_bounds'] += 1
        if xt == yt:
            S['x_eq_y'] += 1
        lin = [x for x in Qn[1:-1] if not A.nodes[x].cyc]
        if lin:
            S['Q_linear_nodes>=1'] += 1
        if len(lin) >= 3:
            S['Q_linear_nodes>=3'] += 1
        if any(len(pieces.get(x, [])) == 3 for x in lin):
            S['lin_split3'] += 1
        if any(x not in pieces for x in lin):
            S['lin_unchanged'] += 1
        oldx, oldy = Qe[0][0][1] != 0, Qe[-1][1][1] != 0
        S['old_end_x'] += oldx
        S['old_end_y'] += oldy
        S['old_end_both'] += oldx and oldy
        qold = sum(1 for la, lb in Qe if la[1] != 0)
        if qold and qold == len(Qe):
            S['Q_all_old'] += 1
        if qold >= 3:
            S['Q_old_edges>=3'] += 1
        ovl, ovr = ov.get((A.aid, 'l')), ov.get((A.aid, 'r'))
        if ovl and ovr:
            S['overlap_both'] += 1
        elif ovl or ovr:
            S['overlap_one'] += 1
        if both and (ovl or ovr):
            S['both_bounds_and_overlap'] += 1
        if level >= 4:
            S['level>=4'] += 1
        if level >= 6:
            S['level>=6'] += 1
        if (i2 in (xt, yt) and i2 > i) or (i1 in (xt, yt) and i1 < i):
            S['junction_child_end_at_x_or_y'] += 1
        if i1 < A.j or i2 > A.k:
            S['i12_outside'] += 1
        if any(A.j <= t <= A.k for t in range(min(xt, yt) + 1, max(xt, yt))):
            S['t_strict_between_xy_in_range'] += 1
        anc = [A.nodes[x].anc for x in Pn_]
        k0 = Pn_.index(Qn[0])
        k1 = k0 + len(Qn) - 1
        if any(a[0] == 'p' and a[2] == 1 for a in anc[:k0]) or any(a[0] == 'p' and a[2] == 0 for a in anc[k1 + 1:]):
            S['U_or_V_crosses'] += 1
        if Qn[0] in pieces and Qn[-1] in pieces:
            S['both_ends_split'] += 1
    return inc_hook


def child_hook_factory(S):
    def child_hook(A, C, side, jj, kk, i, i1, i2, xt, yt, stats):
        S['child'] += 1
        if C.left is not None and C.right is not None:
            S['child_both_bounds'] += 1
        if side == 'r' and jj in (xt, yt):
            S['child_range_starts_at_x_or_y'] += 1
        if side == 'l' and kk in (xt, yt):
            S['child_range_ends_at_x_or_y'] += 1
        if jj == kk:
            S['child_single_index'] += 1
    return child_hook


# ---------------------------------------------------------------- one run
def base_opts(**kw):
    o = dict(mode='claimed', variant='fixed', tiebreak='minid', pairs=0, pcommon=0.0, pfar=0.0,
             e0rule='anycorner', ends=int(os.environ.get('ENDS', '1')), lemO=1)
    o.update(kw)
    return o


def run(I, opts, rng, chooser, cnt, geo=False):
    emb = T.inst_emb(I)
    chk = T.Checker()
    info = {}
    ih, chh = inc_hook_factory(cnt), child_hook_factory(cnt)
    incs, chs = [ih], [chh]
    G = None
    if geo:
        import geo as GEO
        G = GEO.Geo(emb, I['s'], I['t'], cnt, chk.flag)
        chooser.on_P = G.set_P
        incs.append(G)
        chs.append(G.child)
    else:
        chooser.on_P = None
    KG = None
    l1orig = T.level1_ann
    if os.environ.get('GEOK') == '1':
        import geoK
        KG = geoK.GeoK(emb, cnt, chk.flag)
        incs.append(KG.inc)
        chs.append(KG.child)

        def l1(ctx, pf, pdart, scorner, tcorner):
            A1 = l1orig(ctx, pf, pdart, scorner, tcorner)
            (s_, cs), (t_, ct) = scorner, tcorner
            KG.set_level1(pf, pdart, emb.rot[s_][cs] ^ 1, emb.rot[t_][ct] ^ 1, A1)
            return A1
        T.level1_ann = l1

    def inc_all(*a):
        for h in incs:
            h(*a)

    def ch_all(*a):
        for h in chs:
            h(*a)
    T.INC_HOOK, T.CHILD_HOOK = inc_all, ch_all
    T.PATH_HOOK = chooser
    try:
        T.run_reif(emb, I['s'], I['t'], opts, rng, chk, info)
        if KG is not None:
            KG.finalize()
    except T.Fail as ex:
        chk.flag('fail_exception', str(ex))
    except AssertionError:
        import traceback
        chk.flag('impl_assert', traceback.format_exc()[-800:])
    except KeyError:
        import traceback
        chk.flag('fail_keyerror', traceback.format_exc()[-800:])
    except IndexError:
        import traceback
        tb = traceback.format_exc()
        if 'pick_corner' in tb and 'choice(legal)' in tb:
            # f or g is the inner face of a loop at s or t whose loop is on P: no legal corner (R0)
            chk.flag('deg_no_legal_corner')
        else:
            chk.flag('impl_indexerror', tb[-800:])
    finally:
        T.PATH_HOOK = T.INC_HOOK = T.CHILD_HOOK = None
        T.level1_ann = l1orig
    bad = {k: v for k, v in chk.flags.items() if not k.startswith(IGNORE)}
    return chk, info, bad


def explore(I, opts, max_runs=2000, cap=24, branch_leaf=False, seed=0, cnt=None, stop_on_fail=True, geo=False):
    """run every sequence of choices (DFS over ChoiceRng traces). Returns (nruns, complete, fails)."""
    cnt = cnt if cnt is not None else collections.Counter()
    prefix = []
    nruns = 0
    fails = []
    while True:
        rng = ChoiceRng(prefix, seed)
        ch = Chooser(mode='branch', cap=cap, branch_leaf=branch_leaf, prng=random.Random(seed), cnt=cnt)
        chk, info, bad = run(I, opts, rng, ch, cnt, geo=geo)
        nruns += 1
        cnt['runs'] += 1
        cnt['levels_max'] = max(cnt['levels_max'], info.get('levels', 0))
        for k in chk.flags:
            cnt['flag_' + k] += 1
        if bad:
            fails.append(dict(prefix=[t[0] for t in rng.trace], flags=dict(chk.flags),
                              notes=[str(x)[:400] for x in chk.notes[:6]]))
            if stop_on_fail:
                return nruns, False, fails
        tr = rng.trace
        k = len(tr) - 1
        while k >= 0 and tr[k][0] + 1 >= tr[k][1]:
            k -= 1
        if k < 0:
            return nruns, True, fails
        if nruns >= max_runs:
            return nruns, False, fails
        prefix = [t[0] for t in tr[:k]] + [tr[k][0] + 1]


def replay(I, opts, prefix, seed=0, cap=24, branch_leaf=False, geo=False):
    cnt = collections.Counter()
    rng = ChoiceRng(prefix, seed)
    ch = Chooser(mode='branch', cap=cap, branch_leaf=branch_leaf, prng=random.Random(seed), cnt=cnt)
    return run(I, opts, rng, ch, cnt, geo=geo)
