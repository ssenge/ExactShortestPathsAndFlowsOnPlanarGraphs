"""Lemma B5 (LEMMA15.md §9.6): a balanced fundamental-cycle separator from Euler-tour prefix sums
over a spanning tree. Runs the algorithm as written on connected plane graphs (subgraphs of the
sweep families) with BFS, DFS and random spanning trees, and checks every answer against an
independent count of the two sides of the cycle.
usage: python3 -I b5.py START END [fam1,fam2,...]"""
import sys, os, math, random, collections
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'attack3')); sys.path.insert(0, os.path.join(HERE, '..', 'attack4'))
import networkx as nx
from geo import FAMS, drawing_ok
from sweep import params
from fams9 import FAMS9, params9
sys.setrecursionlimit(100000)
NEG = os.environ.get('NEG')         # negative controls: 'anycorner' (fan apex with several corners), 'noheavy' (always fan in F_o)


class Bad(Exception):
    pass


def rotation(pos, E, V):
    nb = {v: [] for v in V}
    for a, b in E:
        nb[a].append(b); nb[b].append(a)
    return {v: sorted(nb[v], key=lambda u: math.atan2(pos[u][1] - pos[v][1], pos[u][0] - pos[v][0])) for v in V}


def face_ids(rot, idx):
    """corner (v, j) lies between rot[v][j-1] and rot[v][j]; it shares its face with corner
    (b, idx[b][v] + 1) of b = rot[v][j], across the edge vb."""
    par = {}
    def find(x):
        while par[x] != x:
            par[x] = par[par[x]]; x = par[x]
        return x
    for v in rot:
        for j in range(len(rot[v])):
            par[(v, j)] = (v, j)
    for v in rot:
        d = len(rot[v])
        for j in range(d):
            b = rot[v][j]; c = (b, (idx[b][v] + 1) % len(rot[b]))
            x, y = find((v, j)), find(c)
            if x != y:
                par[x] = y
    return {c: find(c) for c in par}


def tour(rot, idx, children, r, k):
    """Euler tour around T from the start of corner (r, k): items ('c', v, j) corners, ('m', w)
    the two sides of the parent edge of w, ('a', v, u) the end at v of the non-tree edge vu."""
    out = []
    def visit(v, start, skip):
        d = len(rot[v])
        for t in range(d):
            j = (start + t) % d
            out.append(('c', v, j))
            u = rot[v][j]
            if j == skip:
                continue
            if u in children[v]:
                out.append(('m', u)); visit(u, (idx[u][v] + 1) % len(rot[u]), idx[u][v]); out.append(('m', u))
            else:
                out.append(('a', v, u))
    visit(r, k, None)
    return out


def b5(V, rot, idx, par, depth, children, r, k):
    n = len(V)
    it = tour(rot, idx, children, r, k)
    L = len(it); Mb = [0] * (L + 1)
    for p, x in enumerate(it):
        Mb[p + 1] = Mb[p] + (x[0] == 'm')
    TOT = Mb[L]
    if TOT != 2 * (n - 1):
        raise Bad('mark count')
    def plen(x, z):
        a, b = x, z
        while depth[a] > depth[b]: a = par[a]
        while depth[b] > depth[a]: b = par[b]
        while a != b: a = par[a]; b = par[b]
        return depth[x] + depth[z] - 2 * depth[a] + 1
    def sides(marks, P):
        tw = marks - P + 1
        if tw % 2 or tw < 0:
            raise Bad('parity')
        i = tw // 2; o = n - P - i
        if o < 0:
            raise Bad('negative side')
        return i, o
    pc = {}; pa = collections.defaultdict(list); mp = collections.defaultdict(list)
    for p, x in enumerate(it):
        if x[0] == 'c':
            pc[(x[1], x[2])] = p
        elif x[0] == 'a':
            pa[frozenset((x[1], x[2]))].append((p, x[1]))
        else:
            mp[x[1]].append(p)
    base = dict(it=it, mp=mp, L=L, plen=plen)
    chords = []
    for e, ends in pa.items():
        (p1, u), (p2, v) = sorted(ends)
        P = plen(u, v); i, o = sides(Mb[p2] - Mb[p1], P)
        chords.append((p1, p2, u, v, P, i, o))
    bal = lambda i, o: 3 * i <= 2 * n and 3 * o <= 2 * n
    real = [c for c in chords if bal(c[5], c[6])]
    if real:
        c = min(real, key=lambda c: (min(c[2], c[3]), max(c[2], c[3])))
        return dict(base, kind='real', x=c[2], z=c[3], ins=c[5], out=c[6], P=c[4], chords=chords, arc=(c[0], c[1]))
    heavy = sorted([c for c in chords if 3 * c[5] > 2 * n], key=lambda c: c[0])
    for a, b in zip(heavy, heavy[1:]):
        if not (a[0] < b[0] and b[1] < a[1]):
            raise Bad('heavy chords not a chain')
    starts = sorted(c[0] for c in chords); ends_ = sorted(c[1] for c in chords)
    import bisect
    def ND(p):
        return bisect.bisect_left(starts, p) - bisect.bisect_left(ends_, p)
    if heavy and NEG != 'noheavy':
        e0 = heavy[-1]; nd0 = ND(e0[0]) + 1; lo, hi = e0[0], e0[1]
    else:
        e0 = None; nd0 = 0; lo, hi = -1, L
    Fs = [c for c, p in pc.items() if lo < p < hi and ND(p) == nd0]
    cnt = collections.Counter(v for v, _ in Fs)
    one = [v for v in cnt if cnt[v] == 1 or NEG == 'anycorner']
    if not one:
        raise Bad('no vertex with one corner in F*')
    x0 = min(one); c0 = min((c for c in Fs if c[0] == x0), key=lambda c: pc[c]); p0 = pc[c0]
    best = None
    for c in Fs:
        w = c[0]
        if (w == x0 and NEG != 'anycorner') or c == c0:
            continue
        p = pc[c]
        marks = Mb[p] - Mb[p0] if p > p0 else TOT - (Mb[p0] - Mb[p])
        P = plen(x0, w); i, o = sides(marks, P)
        key = (p - p0) % L
        if 3 * o <= 2 * n and (best is None or key < best[0]):
            best = (key, c, i, o, P)
    if best is None:
        raise Bad('fan found nothing')
    _, c, i, o, P = best
    if 3 * i > 2 * n:
        raise Bad('fan chord unbalanced')
    # the proof step by step: walk order, the step bounds, j = 1, the last corner
    walk = sorted(Fs, key=lambda c: (pc[c] - p0) % L)
    ins = [0]; outs = [None]; Ps = [1]; slack = 0.0
    for j in range(1, len(walk)):
        q = pc[walk[j]]; w = walk[j][0]
        marks = Mb[q] - Mb[p0] if q > p0 else TOT - (Mb[p0] - Mb[q])
        Pj = plen(x0, w); ij, oj = sides(marks, Pj)
        a_, b_ = pc[walk[j - 1]], q
        mid = [it[t % L] for t in range(a_ + 1, b_ if b_ > a_ else b_ + L)]
        if len(mid) == 1 and mid[0][0] == 'm':
            if (j == 1 and ij != 0) or ij > ins[-1] + 1:
                raise Bad('tree step bound')
        else:
            if mid[0][0] != 'a' or mid[-1][0] != 'a' or {mid[0][1], mid[0][2]} != {mid[-1][1], mid[-1][2]}:
                raise Bad('step is neither a tree side nor one chord')
            Te = plen(mid[0][1], mid[0][2]); ke, _ = sides(sum(1 for x in mid if x[0] == 'm'), Te)
            Wp = ke + Te
            if 3 * Wp >= n:
                raise Bad('skipped side not below n/3')
            if (j == 1 and ij != Wp - Te) or (j > 1 and ij > ins[-1] + Wp - 1):
                raise Bad('chord step bound')
            if j > 1:
                slack = max(slack, (ij - ins[-1]) / Wp)
        ins.append(ij); outs.append(oj); Ps.append(Pj)
    if 3 * outs[-1] >= n:
        raise Bad('last corner: out not below n/3')
    return dict(base, kind='virt', x=x0, z=c[0], cx=c0, cz=c, ins=i, out=o, P=P, Fs=Fs, e0=e0, chords=chords,
                walk=walk, arc=(p0, pc[c]), slack=slack)


def path(par, depth, x, z):
    a, b = x, z; pa_, pb_ = [a], [b]
    while depth[a] > depth[b]: a = par[a]; pa_.append(a)
    while depth[b] > depth[a]: b = par[b]; pb_.append(b)
    while a != b:
        a = par[a]; pa_.append(a); b = par[b]; pb_.append(b)
    return pa_ + pb_[-2::-1]


def count_sides(V, rot, cyc, ins_x, ins_z):
    """independent count: cyc = tree path x..z; the closing edge zx is real (ins_* None) or a
    virtual edge inserted into the rotations at the corners ins_x, ins_z (indices j)."""
    rr = {v: list(rot[v]) for v in cyc}
    x, z = cyc[0], cyc[-1]
    if ins_x is not None:
        rr[x].insert(ins_x, 'V'); rr[z].insert(ins_z, 'V')
        cx, cz = 'V', 'V'
    else:
        cx, cz = z, x
    S = set(cyc); side = {}
    k = len(cyc)
    for i, s in enumerate(cyc):
        prev = cyc[i - 1] if i > 0 else cx
        nxt = cyc[i + 1] if i < k - 1 else cz
        R = rr[s]; d = len(R); a, b = R.index(nxt), R.index(prev)
        t = (a + 1) % d; left = True
        while t != a:
            if t == b:
                left = False
            elif R[t] != 'V' and R[t] not in S:
                side.setdefault(R[t], set()).add(left)
            t = (t + 1) % d
    seen = {}; A = set(); B = set()
    for v0 in side:
        if v0 in seen:
            continue
        comp = [v0]; seen[v0] = 1; q = [v0]; att = set()
        while q:
            v = q.pop()
            att |= side.get(v, set())
            for u in rot[v]:
                if u not in S and u not in seen:
                    seen[u] = 1; comp.append(u); q.append(u)
        if len(att) != 1:
            raise Bad('component on both sides')
        (A if True in att else B).update(comp)
    if len(A) + len(B) + len(S) != len(V):
        raise Bad('vertices missed: %d + %d + %d != %d' % (len(A), len(B), len(S), len(V)))
    return A, B


def instance(fam, s):
    r = random.Random(s * 131 + 7)
    if fam in FAMS:
        pos, E = FAMS[fam](s, params(fam, r))
    else:
        pos, E = FAMS9[fam](s, params9(fam, r, r.choice([0.5, 1.0, 2.0])))
    if not drawing_ok(pos, E):
        return None
    G = nx.Graph(); G.add_edges_from(E)
    G = G.subgraph(max(nx.connected_components(G), key=len)).copy()
    # a connected spanning subgraph: a random spanning tree plus a random share of the rest
    H = nx.Graph()
    for a, b in G.edges():
        H.add_edge(a, b, weight=r.random())
    keep = r.choice([0.0, 0.1, 0.3, 0.6, 1.0])
    ST = nx.minimum_spanning_tree(H)
    RE = list(ST.edges()) + [e for e in G.edges() if not ST.has_edge(*e) and r.random() < keep]
    V = sorted(G.nodes())
    rot = rotation(pos, RE, V); idx = {v: {u: j for j, u in enumerate(rot[v])} for v in V}
    RG = nx.Graph(); RG.add_nodes_from(V); RG.add_edges_from(RE)
    root = r.choice(V); mode = r.choice(['bfs', 'bfs', 'dfs', 'rand'])
    if mode == 'bfs':
        T = nx.bfs_tree(RG, root)
    elif mode == 'dfs':
        T = nx.dfs_tree(RG, root)
    else:
        W = nx.Graph()
        for a, b in RE:
            W.add_edge(a, b, weight=r.random())
        T = nx.bfs_tree(nx.minimum_spanning_tree(W), root)
    par = {root: None}; depth = {root: 0}; children = {v: set() for v in V}
    for a, b in nx.bfs_edges(T, root):
        par[b] = a; depth[b] = depth[a] + 1; children[a].add(b)
    k = r.randrange(len(rot[root]))
    return V, rot, idx, par, depth, children, root, k, RG, mode, keep


if __name__ == '__main__':
    a, b = int(sys.argv[1]), int(sys.argv[2])
    fams = sys.argv[3].split(',') if len(sys.argv) > 3 else list(FAMS) + list(FAMS9)
    st = collections.Counter(); mx = collections.defaultdict(float)
    for s in range(a, b):
        fam = fams[s % len(fams)]
        inst = instance(fam, s)
        if inst is None:
            st['bad_drawing'] += 1; continue
        V, rot, idx, par, depth, children, root, k, RG, mode, keep = inst
        n = len(V)
        if n < 4:
            continue
        try:
            res = b5(V, rot, idx, par, depth, children, root, k)
            fid = face_ids(rot, idx)
            # every real chord: marks formula against the independent count
            rr = random.Random(s)
            sample = res['chords'] if len(res['chords']) <= 40 else rr.sample(res['chords'], 40)
            def marked(cyc, a_, b_):
                """vertices strictly on the side of the cyclic arc (a_, b_) by their marks; r by o"""
                Sx = set(cyc); L_ = res['L']
                inarc = lambda t: (a_ < t < b_) if a_ < b_ else (t > a_ or t < b_)
                out = {w for w, ps in res['mp'].items() if w not in Sx and all(inarc(t) for t in ps)}
                if root not in Sx and a_ > b_:
                    out.add(root)
                return out
            for c in sample:
                cyc = path(par, depth, c[2], c[3])
                A, B = count_sides(V, rot, cyc, None, None)
                M = marked(cyc, c[0], c[1])
                if M not in (A, B) or len(M) != c[5] or root in M:
                    raise Bad('real chord: marked side is not a side, or wrong count')
                st['chord_checks'] += 1
            if res['kind'] == 'virt':
                Fs = res['Fs']
                if len({fid[c] for c in Fs}) != 1:
                    raise Bad('F* corners in several faces')
                f = fid[Fs[0]]
                if sorted(c for c in fid if fid[c] == f) != sorted(Fs):
                    raise Bad('F* is not a whole face')
                if res['x'] == res['z']:
                    raise Bad('loop')
                c0 = res['cx']; seq = [c0]
                while True:
                    v_, j_ = seq[-1]; b_ = rot[v_][j_]; nxt = (b_, (idx[b_][v_] + 1) % len(rot[b_]))
                    if nxt == c0: break
                    seq.append(nxt)
                if seq != res['walk']:
                    raise Bad('walk around F is not the order along the tour')
                st['walk_checks'] += 1
                mx['step_slack'] = max(mx['step_slack'], res['slack'])
                cyc = path(par, depth, res['x'], res['z'])
                A, B = count_sides(V, rot, cyc, res['cx'][1], res['cz'][1])
            else:
                cyc = path(par, depth, res['x'], res['z'])
                A, B = count_sides(V, rot, cyc, None, None)
            M = marked(cyc, *res['arc'])
            if M not in (A, B) or len(M) != res['ins'] or len(V) - len(cyc) - len(M) != res['out']:
                raise Bad('separator: marked side is not a side, or wrong count')
            cA, cB = len(A), len(B)
            if 3 * max(cA, cB) > 2 * n:
                raise Bad('unbalanced: %d %d of %d' % (cA, cB, n))
            h = max(depth.values())
            if len(cyc) > 2 * h + 1:
                raise Bad('separator longer than 2h+1')
        except Bad as ex:
            st['FAIL'] += 1; print('FAIL', fam, s, mode, keep, ex, flush=True); continue
        st['instances'] += 1; st['kind_' + res['kind']] += 1; st['mode_' + mode] += 1
        st['vertices'] += n
        mx['n'] = max(mx['n'], n); mx['side_over_n'] = max(mx['side_over_n'], max(cA, cB) / n)
        mx['S_over_2h1'] = max(mx['S_over_2h1'], len(cyc) / (2 * max(depth.values()) + 1))
    print(dict(st)); print({k: round(v, 3) for k, v in mx.items()})
