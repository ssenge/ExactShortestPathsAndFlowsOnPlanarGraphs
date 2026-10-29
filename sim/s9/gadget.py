"""Bounded-degree expansion G° of a straight-line plane graph: every vertex of degree >= 4 becomes a
radial binary tree whose leaves carry its edges in rotation order. Max degree 3, planar, hop diameter
grows by a factor O(log maxdeg)."""
import math
import numpy as np


def expand(pos, E, r=None):
    pos = np.asarray(pos, float); n = len(pos)
    adj = [[] for _ in range(n)]
    for a, b in E:
        adj[a].append(b); adj[b].append(a)
    if r is None:
        dmin = min(np.linalg.norm(pos[a] - pos[b]) for a, b in E)
        r = 0.3 * dmin
    P = []; EE = []; port = {}        # port[(v,u)] = vertex of v's gadget carrying edge vu
    owner = []                         # owner[new vertex] = original vertex
    for v in range(n):
        nb = sorted(adj[v], key=lambda u: math.atan2(pos[u][1] - pos[v][1], pos[u][0] - pos[v][0]))
        k = len(nb)
        if k <= 3:
            i = len(P); P.append(tuple(pos[v])); owner.append(v)
            for u in nb:
                port[(v, u)] = i
            continue
        ang = [math.atan2(pos[u][1] - pos[v][1], pos[u][0] - pos[v][0]) for u in nb]
        H = math.ceil(math.log2(k))

        def build(lo, hi, t):
            th = sum(ang[lo:hi]) / (hi - lo)
            rad = r if hi - lo == 1 else r * t / (H + 1)
            i = len(P); P.append((pos[v][0] + rad * math.cos(th), pos[v][1] + rad * math.sin(th))); owner.append(v)
            if hi - lo == 1:
                port[(v, nb[lo])] = i
            else:
                mid = (lo + hi) // 2
                for a, b in ((lo, mid), (mid, hi)):
                    EE.append((i, build(a, b, t + 1)))
            return i
        build(0, k, 0)
    for a, b in E:
        EE.append((port[(a, b)], port[(b, a)]))
    EE = [(min(a, b), max(a, b)) for a, b in EE]
    return np.array(P), EE, owner
