"""Section 3 of notes/DMST.md on the level of a state, for EVERY arborescence, not only the optimum.

A random state: super-vertices 0..k-1, root 0, a random functional graph of zero-weight chosen arcs, more random arcs.
For each active component and each arborescence T of R: Lemma 3 by its own construction of T'.
For each arborescence T' after the contraction and each shortest path pi: Lemma 2 by its own construction of T.
Also the literal reading of "Several components", and how often the phrase of the proof of Lemma 2 fails.
No import of dmst.py. Standard library only.
"""
import itertools
import json
import random
import sys
import time
from collections import Counter

INF = float('inf')


def arbs(k, r, arcs):
    """All arborescences: a dict head -> arc index."""
    ins = {v: [] for v in range(k) if v != r}
    for i, (u, v, w) in enumerate(arcs):
        if v != r and u != v:
            ins[v].append(i)
    keys = sorted(ins)
    if any(not ins[v] for v in keys):
        return
    for pick in itertools.product(*[ins[v] for v in keys]):
        par = {v: arcs[e][0] for v, e in zip(keys, pick)}
        good = True
        for v in keys:
            x, c = v, 0
            while x != r:
                x = par[x]
                c += 1
                if c > k:
                    good = False
                    break
            if not good:
                break
        if good:
            yield dict(zip(keys, pick))


def cost(T, arcs):
    return sum(arcs[e][2] for e in T.values())


def state(rng):
    k = rng.randrange(3, 8)
    r = 0
    chosen = {}
    arcs = []
    for v in range(1, k):
        u = rng.choice([x for x in range(k) if x != v])
        chosen[v] = len(arcs)
        arcs.append((u, v, 0))
    top = rng.choice([1, 2, 3, 6, 20])
    for _ in range(rng.randrange(1, 2 * k + 6)):
        u = rng.randrange(k)
        v = rng.randrange(k)
        if u != v:
            arcs.append((u, v, rng.randint(0, top)))
    # every vertex reached from r: add arcs from the reached set if needed
    while True:
        seen = {r}
        grew = True
        while grew:
            grew = False
            for u, v, _ in arcs:
                if u in seen and v not in seen:
                    seen.add(v)
                    grew = True
        rest = [v for v in range(k) if v not in seen]
        if not rest:
            break
        arcs.append((rng.choice(sorted(seen)), rng.choice(rest), rng.randint(0, top + 3)))
    return k, r, chosen, arcs


def components(k, r, chosen, arcs):
    p = list(range(k))

    def f(x):
        while p[x] != x:
            p[x] = p[p[x]]
            x = p[x]
        return x
    for v, e in chosen.items():
        p[f(arcs[e][0])] = f(v)
    comp = {}
    for v in range(k):
        comp.setdefault(f(v), set()).add(v)
    return [c for c in comp.values() if r not in c]


def cycle_of(K, chosen, arcs):
    x = next(iter(K))
    seen = []
    while x not in seen:
        seen.append(x)
        x = arcs[chosen[x]][0]
    return seen[seen.index(x):]


def dist_to(K, c, arcs):
    d = {s: INF for s in K}
    d[c] = 0
    for _ in range(len(K) + 1):
        for u, v, w in arcs:
            if u in K and v in K and d[v] + w < d[u]:
                d[u] = d[v] + w
    return d


def shortest_paths(K, S, c, d, arcs, rng, tries=3):
    """Arc lists of shortest paths from S to c in R[K], random among tight arcs; simple by removal of zero loops."""
    out = []
    for _ in range(tries):
        x, path, seen = S, [], {S}
        ok = True
        while x != c:
            cand = [i for i, (u, v, w) in enumerate(arcs) if u == x and v in K and d[x] == w + d[v]]
            rng.shuffle(cand)
            step = None
            for i in cand:
                if arcs[i][1] not in seen:
                    step = i
                    break
            if step is None:
                ok = False
                break
            path.append(step)
            x = arcs[step][1]
            seen.add(x)
        if ok:
            out.append(path)
    return out


def contract(k, r, K, d, beta, arcs):
    """Returns the arcs after the contraction, as (u', v', w') with the index of the old arc, and the map of vertices."""
    A = {s for s in K if d[s] <= beta}
    name = min(A)
    mp = {v: (name if v in A else v) for v in range(k)}
    new = []
    for i, (u, v, w) in enumerate(arcs):
        if v in A and u in A:
            continue
        nw = w + d[v] - beta if v in A else w
        new.append((mp[u], mp[v], nw, i))
    return A, name, mp, new


def run(seed, secs):
    rng = random.Random(seed)
    st = Counter()
    end = time.time() + secs
    while time.time() < end:
        k, r, chosen, arcs = state(rng)
        comps = components(k, r, chosen, arcs)
        if not comps:
            continue
        st['states'] += 1
        allT = list(arbs(k, r, arcs))
        if len(allT) > 4000:
            st['skipped_big'] += 1
            continue
        opt = min(cost(T, arcs) for T in allT)
        for K in comps:
            cyc = cycle_of(K, chosen, arcs)
            c = rng.choice(cyc)
            d = dist_to(K, c, arcs)
            if any(d[s] != 0 for s in cyc):
                st['FAIL.cycle_not_zero'] += 1
            cand = [(w + d[v], i) for i, (u, v, w) in enumerate(arcs) if u not in K and v in K]
            beta = min(cand)[0] if cand else INF
            if beta == INF:
                st['FAIL.beta_inf'] += 1
                continue
            A, name, mp, new = contract(k, r, K, d, beta, arcs)
            st['contractions'] += 1
            st['A_between' if len(cyc) < len(A) < len(K) else ('A_K' if len(A) == len(K) else 'A_cycle')] += 1
            # Lemma 1
            for (u, v, w, i) in new:
                if w < 0:
                    st['FAIL.neg'] += 1
                if w > arcs[i][2]:
                    st['FAIL.grew'] += 1
            for s in A:
                if arcs[chosen[s]][0] not in A:
                    st['FAIL.chosen_tail'] += 1
            # relabel for arbs
            names = sorted({mp[v] for v in range(k)})
            idx = {x: j for j, x in enumerate(names)}
            arcs2 = [(idx[u], idx[v], w) for u, v, w, _ in new]
            old = [i for _, _, _, i in new]
            # Lemma 3, every T
            allT2 = list(arbs(len(names), idx[mp[r]], arcs2))
            if not allT2:
                st['FAIL.no_arb_after'] += 1
                continue
            opt2 = min(cost(T, arcs2) for T in allT2)
            if opt - opt2 != beta:
                st['FAIL.opt_drop'] += 1
            back = {i: j for j, i in enumerate(old)}
            for T in allT:
                st['L3.T'] += 1
                # path of T from r to c
                par = {v: e for v, e in T.items()}
                Q = []
                x = c
                while x != r:
                    Q.append(par[x])
                    x = arcs[par[x]][0]
                Q.reverse()
                first = next(e for e in Q if arcs[e][1] in A and arcs[e][0] not in A)
                T2 = {}
                for v, e in T.items():
                    if v in A:
                        continue
                    T2[idx[mp[v]]] = back[e]
                T2[idx[name]] = back[first]
                # T' an arborescence
                g = {v: arcs2[e][0] for v, e in T2.items()}
                good = set(g) == set(range(len(names))) - {idx[mp[r]]}
                for v in g:
                    y, cc = v, 0
                    while y != idx[mp[r]]:
                        y = g[y]
                        cc += 1
                        if cc > len(names):
                            good = False
                            break
                if not good:
                    st['FAIL.L3_not_arb'] += 1
                    continue
                if cost(T2, arcs2) > cost(T, arcs) - beta:
                    st['FAIL.L3_bound'] += 1
            # Lemma 2, every T', several paths
            for T2 in allT2:
                e2 = T2[idx[name]]
                ei = old[e2]
                x, y = arcs[ei][0], arcs[ei][1]
                for pi in shortest_paths(K, y, c, d, arcs, rng):
                    st['L2.T'] += 1
                    T = {}
                    for v2, e in T2.items():
                        if v2 != idx[name]:
                            oi = old[e]
                            T[arcs[oi][1]] = oi
                    for s in A:
                        T[s] = chosen[s]
                    for a in pi:
                        h = arcs[a][1]
                        if h not in A:
                            st['FAIL.L2_path_leaves_A'] += 1
                        if chosen[h] == a:
                            st['L2.arc_of_pi_is_chosen'] += 1
                        if h == c and chosen[c] == a:
                            st['L2.in_arc_of_c_IS_the_chosen_one'] += 1
                        T[h] = a
                    T[y] = ei
                    gg = {v: arcs[e][0] for v, e in T.items()}
                    good = set(gg) == set(range(k)) - {r}
                    for v in gg:
                        z, cc = v, 0
                        while z != r:
                            z = gg[z]
                            cc += 1
                            if cc > k:
                                good = False
                                break
                    if not good:
                        st['FAIL.L2_not_arb'] += 1
                    elif cost(T, arcs) != cost(T2, arcs2) + beta:
                        st['FAIL.L2_weight'] += 1
    print(json.dumps(dict(sorted(st.items()))))


def explicit():
    """Two explicit instances quoted in the report."""
    # 1. the phrase in the proof of Lemma 2
    print('Instance A (Lemma 2 phrase): super-vertices r=0, a=1, b=2; arcs a->b 0 (chosen of b), b->a 0 (chosen of a), r->b 3.')
    print('  c = a. beta = 3 + d(b) = 3 + 0 = 3. T\' enters at y = b. pi = b->a, the chosen arc of a, so the in-arc of c IS the chosen one. T = r->b, b->a: an arborescence.')
    # 2. the literal reading of "Several components"
    r, a1, a2, b1, b2 = range(5)
    arcs = [(a1, a2, 0), (a2, a1, 0), (b1, b2, 0), (b2, b1, 0), (b1, a1, 1), (a1, b1, 1), (r, a1, 5), (r, b1, 7)]
    allT = list(arbs(5, r, arcs))
    opt = min(cost(T, arcs) for T in allT)
    print('Instance B (several components): arcs', arcs, 'optimum', opt)
    Ka, Kb = {a1, a2}, {b1, b2}
    da = dist_to(Ka, a1, arcs)
    db = dist_to(Kb, b1, arcs)
    ba = min(w + da[v] for u, v, w in arcs if u not in Ka and v in Ka)
    bb = min(w + db[v] for u, v, w in arcs if u not in Kb and v in Kb)
    print('  in parallel: beta(K_a) =', ba, ', beta(K_b) =', bb)
    # after K_a alone: new chosen arc b1 -> A_a. Weak component of b1 is now K_b together with A_a.
    A_a = 'A'
    w_after = {(b1, a1): 1 + 0 - ba, (r, a1): 5 + 0 - ba}
    print('  after K_a alone: w(b1->A) =', w_after[b1, a1], ' w(r->A) =', w_after[r, a1], '; chosen arc of A is b1->A, so the weak component of b1 is {b1, b2, A}')
    # definition of Section 3 applied to this new weak component, c = b1: arcs into it from outside are r->A and r->b1
    dA = 1  # A->b1 has weight 1, unchanged since its head b1 is not in A
    lit = min(w_after[r, a1] + dA, 7 + 0)
    print('  Section 3 applied literally to that component: d(A) =', dA, ', beta =', lit, 'instead of', bb)


if __name__ == '__main__':
    if sys.argv[1] == 'explicit':
        explicit()
    else:
        run(int(sys.argv[1]), float(sys.argv[2]))
