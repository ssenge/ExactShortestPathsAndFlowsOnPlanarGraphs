"""Hand-specified separators (for rebuilding the (S7) configurations) + random completion below."""
import collections, random
import networkx as nx
import bdd


def gx(P, X):
    G = nx.Graph()
    G.add_nodes_from(X)
    for e, (a, b) in P.edges.items():
        if a in X and b in X:
            G.add_edge(a, b, eid=e)
    return G


def split(P, bags, b, q, closing, inside_vertex=None, inside_side=None, extras=None, rng=None):
    """closing: 'real' or 'virtual' (virtual: first face of G[X] containing both ends, or a given face index
    via ('virtual', fi), with first corners); the inside side is the side of `inside_vertex` (or 'L'/'R')."""
    B = bags[b]; X = B['X']
    PX = P.induced(X)
    GX = gx(P, X)
    facesX, dfX = PX.faces()
    y, z = q[0], q[-1]
    if closing == 'real':
        cl = ('real', GX[y][z]['eid'])
    else:
        fis = [i for i, f in enumerate(facesX) if y in {v for v, _ in f} and z in {v for v, _ in f}]
        fi = closing[1] if isinstance(closing, tuple) else fis[0]
        cl = ('virtual', PX.corners_on_face(dfX, y, fi)[0], PX.corners_on_face(dfX, z, fi)[0])
    comps, cside, eside = bdd.analyse(PX, X, q, cl)
    S = set(q)
    if inside_vertex is not None:
        ci = next(i for i, c in enumerate(comps) if inside_vertex in c)
        ins = cside[ci]
    else:
        ins = inside_side
    inside = [i for i in range(len(comps)) if cside[i] == ins]
    outside = [i for i in range(len(comps)) if cside[i] != ins]
    Xin = set(S)
    for i in inside:
        Xin |= comps[i]
    kids = [('in', Xin)]
    nout_adj = collections.Counter()
    for i in outside:
        C = comps[i]
        Y = set(C) | {s for s in S if any(GX.has_edge(s, x) for x in C)}
        for s in (extras or {}).get(i, ()):
            Y.add(s)
        for s in S:
            if any(GX.has_edge(s, x) for x in C):
                nout_adj[s] += 1
        kids.append(('out', Y))
    member = collections.Counter()
    for _, Y in kids:
        for s in S & Y:
            member[s] += 1
    # tree of G[X] containing q
    H = nx.Graph()
    qe = set(frozenset((q[i], q[i + 1])) for i in range(len(q) - 1))
    rr = rng or random.Random(0)
    for a, c in GX.edges():
        H.add_edge(a, c, weight=(0 if frozenset((a, c)) in qe else 1) + rr.random() * 0.5)
    T = nx.minimum_spanning_tree(H)
    B.update(S=S, q=list(q), closing=cl, T=T, strat='hand', tmode='hand', inside_mode='hand',
             sat7a=max(member.values()) <= 3, maxmem=max(member.values()), nout_adj=dict(nout_adj),
             n_inside_comps=len(inside), n_out=len(outside), pex=0)
    B['kids'] = []
    for kind, Y in kids:
        nb = len(bags)
        bags[nb] = dict(X=frozenset(Y), parent=b, depth=B['depth'] + 1, kind=kind)
        B['kids'].append(nb)
    return B['kids']


def complete(P, bags, rng, cfg=None, frozen=()):
    """randomly split every unsplit bag not in `frozen` (as bdd.build does)."""
    cfg = dict(bdd.DEFAULT, **(cfg or {}))
    G = nx.Graph()
    G.add_nodes_from(P.rot)
    for e, (a, b) in P.edges.items():
        G.add_edge(a, b, eid=e)
    order = [b for b in bags if 'kids' not in bags[b] and b not in frozen]
    k = 0
    while k < len(order):
        b = order[k]; k += 1
        B = bags[b]
        if len(B['X']) <= cfg['leaf_size']:
            continue
        sep = bdd.find_separator(P, G, bags, b, rng, cfg)
        if sep is None:
            continue
        kids = sep.pop('children')
        B.update(sep)
        B['kids'] = []
        for kind, Y in kids:
            nb = len(bags)
            bags[nb] = dict(X=frozenset(Y), parent=b, depth=B['depth'] + 1, kind=kind)
            B['kids'].append(nb)
            order.append(nb)
    return bags
