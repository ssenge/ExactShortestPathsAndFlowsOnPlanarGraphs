"""deep.py plus the Theorem D SSSP check at every level (multi-source, all live annuli at once).

Weights on G^_l: 0 on E_R, M on E_S, K c + 1 on an E_C edge whose pair lies in a live annulus,
M on every other E_C edge. One source copy per live annulus (on p^ of its node-part (i,0) or
any node-part), offset 0. Check: every copy on p^(g), g in live annulus A, has distance
d_K(f_A, g) computed in the abstract annulus A with weights K c + 1; copies outside live
annuli have distance >= M.
usage: python3 -I deep2.py START COUNT WORKERS [policy] [variant] [fams] [schemes]
"""
import sys, os, collections, heapq, random
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import deep
from deep import Run, INF

orig_check = Run.check_level


def check_level(self, G, prevG, active, level, I):
    orig_check(self, G, prevG, active, level, I)
    try:
        sssp_check(self, G, active, level)
    except Exception as ex:
        import traceback
        self.bad('sssp_exception', traceback.format_exc()[-500:])


def sssp_check(self, G, active, level):
    M, emb, C = self.M, self.emb, self.C
    K = len(G.V) + 1
    Mw = K * (2 * sum(emb.cap) + 1) + 1
    if os.environ.get('SSSP_CTL') == 'M1':
        Mw = 1  # negative control: M too small
    # pieces of live annuli
    piece_key = {}
    for pi, P in enumerate(G.pieces):
        T = tuple(P['toks'])
        if P['cyclic']:
            kk = min(range(len(T)), key=lambda q: T[q:] + T[:q])
            T = T[kk:] + T[:kk]
        piece_key[(P['face'], T, P['cyclic'])] = pi
    ann_of_piece = {}
    node_of_piece = {}
    for A in active:
        for nid in A.nodes:
            T, ns = M.tokens_of(nid)
            T = tuple(T)
            cyc = ns == 0
            if cyc:
                kk = min(range(len(T)), key=lambda q: T[q:] + T[:q])
                T = T[kk:] + T[:kk]
            pi = piece_key.get((M.np[nid].face, T, cyc))
            if pi is None:
                return
            ann_of_piece[pi] = A
            node_of_piece[pi] = nid
    adj = collections.defaultdict(list)
    for (a, b, t, info) in G.E:
        if t == 'R':
            w = 0
        elif t == 'S':
            w = Mw
        else:
            x, y = info
            pa, pb = G.piece_of[x], G.piece_of[y]
            A1, A2 = ann_of_piece.get(pa), ann_of_piece.get(pb)
            if A1 is not None and A1 is A2:
                w = K * emb.cap[x[0] >> 1] + 1
            else:
                w = Mw
                if (A1 is None) != (A2 is None) or (A1 is not None and A1 is not A2):
                    self.bad('sssp_EC_between_live_and_other', (level, info))
        adj[a].append((b, w))
        adj[b].append((a, w))
    # sources: one node-part per annulus
    src_of = {}
    srcs = {}
    for A in active:
        cand = [pi for pi, B in ann_of_piece.items() if B is A]
        f = self.rng.choice(sorted(cand))
        src_of[A.aid] = f
        copies = sorted(k for k, p in G.vpiece.items() if p == f)
        srcs[self.rng.choice(copies)] = 0
    dist = {}
    pq = [(0, k) for k in srcs]
    best = dict(srcs)
    while pq:
        d, x = heapq.heappop(pq)
        if x in dist:
            continue
        dist[x] = d
        for y, w in adj[x]:
            if y not in dist and d + w < best.get(y, INF):
                best[y] = d + w
                heapq.heappush(pq, (d + w, y))
    # expected: d_K in the abstract annulus
    for A in active:
        f = src_of[A.aid]
        dK, _ = self.sssp(A.nodes, node_of_piece[f], lambda e: K * emb.cap[e] + 1)
        for pi, B in ann_of_piece.items():
            if B is not A:
                continue
            want = dK.get(node_of_piece[pi], INF)
            got = {dist.get(k, INF) for k, p in G.vpiece.items() if p == pi}
            if got != {want}:
                self.bad('sssp_distance', (level, A.aid, pi, sorted(got)[:3], want))
            C['sssp_nodeparts_checked'] += 1
    for k, p in G.vpiece.items():
        if p not in ann_of_piece and dist.get(k, INF) < Mw:
            self.bad('sssp_residual_below_M', (level, k, dist.get(k)))
    C['sssp_levels'] += 1


Run.check_level = check_level

if __name__ == '__main__':
    deep.main()
