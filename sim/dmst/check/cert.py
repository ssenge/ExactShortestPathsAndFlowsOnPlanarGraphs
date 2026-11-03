"""A remark for line 75 of notes/DMST.md: the sum of beta is a dual certificate, even for wrong d.

Claim. Let d' be any function on K with d'(c) = 0 and d'(x) <= w(x, y) + d'(y) on arcs inside K, and let
beta' = min over entering arcs of w + d'(head). Then every arborescence T has w(T) >= beta' + w''(T), where w''(x, y) is w minus the number of
integers t in [0, beta') for which (x, y) enters U_t = {S in K : d'(S) <= t}, and w'' >= 0. So local checks and w(tree) = total certify optimality
whatever the oracle returned.
Test: d' = min(d, cap) with a random cap, which satisfies the hypothesis and is not the true distance. Every arborescence is tried.
"""
import random
import sys
import time
from collections import Counter

sys.dont_write_bytecode = True
sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))
import lemmas as L   # our own file, not dmst.py


def run(seed, secs):
    rng = random.Random(seed)
    st = Counter()
    end = time.time() + secs
    while time.time() < end:
        k, r, chosen, arcs = L.state(rng)
        comps = L.components(k, r, chosen, arcs)
        if not comps:
            continue
        allT = list(L.arbs(k, r, arcs))
        if len(allT) > 3000:
            continue
        for K in comps:
            c = rng.choice(L.cycle_of(K, chosen, arcs))
            d = L.dist_to(K, c, arcs)
            finite = [x for x in d.values() if x != L.INF]
            cap = rng.choice(finite + [rng.randint(0, 5), L.INF])
            dp = {s: min(d[s], cap) for s in K}
            if any(u in K and v in K and dp[u] > w + dp[v] for u, v, w in arcs):
                st['skip_hypothesis_fails'] += 1      # d = inf with a finite cap: tail capped, head not relevant
                continue
            cand = [w + dp[v] for u, v, w in arcs if u not in K and v in K]
            if not cand:
                continue
            bp = min(cand)
            if bp == L.INF:
                continue
            st['cases'] += 1
            st['cap_changed_d'] += dp != d

            def enters(u, v, t):
                return v in K and dp[v] <= t and (u not in K or dp[u] > t)
            wpp = []
            for u, v, w in arcs:
                n = sum(1 for t in range(int(bp)) if enters(u, v, t))
                wpp.append(w - n)
                if w - n < 0:
                    st['FAIL.reduced_negative'] += 1
            for T in allT:
                st['T'] += 1
                a = sum(arcs[e][2] for e in T.values())
                b = bp + sum(wpp[e] for e in T.values())
                if a < b:
                    st['FAIL.weak_duality'] += 1
    print(dict(sorted(st.items())))


run(int(sys.argv[1]), float(sys.argv[2]))
