"""Rounded patterns on the k x k grid against m^4, with m^2/K held near 0.4. Quoted in notes/APPROX_DIAMETER.md.
P is the boundary cycle, Phi its inner face, tau by Dijkstra per portal.
python3 -I grid_patterns.py"""
import json, sys
import numpy as np
from scipy.sparse import coo_matrix
from scipy.sparse.csgraph import dijkstra


def grid_disc(k):
    vid = lambda i, j: i * k + j
    bd = [vid(0, j) for j in range(k)] + [vid(i, k - 1) for i in range(1, k)] + [vid(k - 1, j) for j in range(k - 2, -1, -1)] + [vid(i, 0) for i in range(k - 2, 0, -1)]
    K = len(bd)
    ren = {v: i for i, v in enumerate(bd)}
    nxt = K
    for v in range(k * k):
        if v not in ren:
            ren[v] = nxt
            nxt += 1
    E = set()
    for i in range(k):
        for j in range(k):
            if i + 1 < k:
                E.add((ren[vid(i, j)], ren[vid(i + 1, j)]))
            if j + 1 < k:
                E.add((ren[vid(i, j)], ren[vid(i, j + 1)]))
    E = {(min(a, c), max(a, c)) for a, c in E}
    ring = {(min(i, (i + 1) % K), max(i, (i + 1) % K)) for i in range(K)}
    return k * k, K, sorted(E - ring)


def patterns(N, K, E, m):
    rho = max(1, K // m - 1)
    portal = list(range(0, K, rho + 1))
    a = np.array(E)
    rows, cols = np.r_[a[:, 0], a[:, 1]], np.r_[a[:, 1], a[:, 0]]
    tau = np.zeros((len(portal), N - K), dtype=np.int32)
    for i, p in enumerate(portal):
        wd = np.minimum((np.arange(K) - p) % K, (p - np.arange(K)) % K)
        R, C, W = np.r_[rows, np.full(K, N)], np.r_[cols, np.arange(K)], np.r_[np.ones(len(rows)), wd + 1.0]
        d = dijkstra(coo_matrix((W, (R, C)), shape=(N + 1, N + 1)).tocsr(), indices=N, directed=True)
        tau[i] = (d[K:N] - 1).astype(np.int32)
    uniq = np.unique(np.floor_divide(tau - tau[0], rho).T, axis=0)
    return dict(n=N, K=K, rho=rho, m=len(portal), patterns=len(uniq), over_m4=round(len(uniq) / len(portal) ** 4, 3))


if __name__ == '__main__':
    for k, m in ((26, 6), (53, 9), (100, 12), (186, 17), (350, 23), (700, 33), (1000, 39)):
        N, K, E = grid_disc(k)
        print(json.dumps(dict(k=k, **patterns(N, K, E, m))), flush=True)
        sys.stdout.flush()
