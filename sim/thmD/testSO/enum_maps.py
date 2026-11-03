"""All connected plane multigraphs (parallel edges allowed; loops optional) with at most M edges
and at least 2 vertices, up to orientation-preserving map isomorphism.

Every connected plane map with m >= 2 edges and n >= 2 vertices arises from one with m - 1 edges
by adding a pendant edge at a corner (delete a leaf edge of a tree) or an edge inside a face
between two corners, possibly of one vertex (delete a non-bridge edge). So the closure from the
one-edge map is complete. Check: with loops the counts are 1, 3, 12, 54, 306, 2057, 14996 for
m = 1..7, i.e. the sensed planar maps (OEIS A006384) minus the one-vertex maps (plane trees).
Rotation convention of sim/thmD/thmD.py: corner (v, i) lies between rot[v][i] and rot[v][i+1].

Usage: python3 -I enum_maps.py M OUT.json [noloops]
"""
import sys
import json


def faces(n, ends, rot):
    m = len(ends)
    tl = [0] * (2 * m)
    for e, (u, v) in enumerate(ends):
        tl[2 * e], tl[2 * e + 1] = u, v
    pos = {}
    for v in range(n):
        for i, d in enumerate(rot[v]):
            pos[d] = i
    seen = set()
    F = []
    for d0 in range(2 * m):
        if d0 in seen:
            continue
        cyc = []
        d = d0
        while d not in seen:
            seen.add(d)
            cyc.append(d)
            r = rot[tl[d ^ 1]]
            d = r[(pos[d ^ 1] + 1) % len(r)]
        F.append(cyc)
    return F, tl, pos


def canon(n, ends, rot):
    m = len(ends)
    F, tl, pos = faces(n, ends, rot)
    if n - m + len(F) != 2:
        return None

    def sigma(d):
        r = rot[tl[d]]
        return r[(pos[d] + 1) % len(r)]
    best = None
    for root in range(2 * m):
        lab = {root: 0}
        order = [root]
        code = []
        k = 0
        while k < len(order):
            d = order[k]
            for nd in (sigma(d), d ^ 1):
                if nd not in lab:
                    lab[nd] = len(order)
                    order.append(nd)
                code.append(lab[nd])
            k += 1
        code = tuple(code)
        if best is None or code < best:
            best = code
    return best


def extend(n, ends, rot):
    m = len(ends)
    out = []
    for v in range(n):
        for i in range(len(rot[v])):
            r = [list(x) for x in rot]
            r[v].insert(i + 1, 2 * m)
            r.append([2 * m + 1])
            out.append((n + 1, ends + [(v, n)], r))
    F, tl, pos = faces(n, ends, rot)
    for cyc in F:
        cs = [(tl[d ^ 1], pos[d ^ 1]) for d in cyc]
        L = len(cs)
        for a in range(L):
            for b in range(a, L):
                (u, i), (v, j) = cs[a], cs[b]
                for orient in (((0, 1), (1, 0)) if a == b else ((0, 1),)):
                    r = [list(x) for x in rot]
                    if u != v:
                        r[u].insert(i + 1, 2 * m)
                        r[v].insert(j + 1, 2 * m + 1)
                    elif a == b:
                        r[u].insert(i + 1, 2 * m + orient[1])
                        r[u].insert(i + 1, 2 * m + orient[0])
                    elif i > j:
                        r[u].insert(i + 1, 2 * m)
                        r[u].insert(j + 1, 2 * m + 1)
                    elif j > i:
                        r[u].insert(j + 1, 2 * m + 1)
                        r[u].insert(i + 1, 2 * m)
                    else:
                        continue
                    out.append((n, ends + [(u, v)], r))
    return out


def all_maps(M, loops=True):
    level = {canon(2, [(0, 1)], [[0], [1]]): (2, [(0, 1)], [[0], [1]])}
    res = {1: list(level.values())}
    for m in range(2, M + 1):
        nxt = {}
        for (n, ends, rot) in level.values():
            for (n2, e2, r2) in extend(n, ends, rot):
                if not loops and any(a == b for a, b in e2):
                    continue
                c = canon(n2, e2, r2)
                if c is None or c in nxt:
                    continue
                nxt[c] = (n2, e2, r2)
        level = nxt
        res[m] = list(level.values())
    return res


if __name__ == '__main__':
    M = int(sys.argv[1])
    loops = not (len(sys.argv) > 3 and sys.argv[3] == 'noloops')
    res = all_maps(M, loops)
    for m in sorted(res):
        print(m, len(res[m]))
    json.dump({str(m): v for m, v in res.items()}, open(sys.argv[2], 'w'))
