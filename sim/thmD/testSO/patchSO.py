"""Write thmD_SO.py: checkO/thmD_R.py (the driver with all Lemma O and extra checks) plus hooks
for an chooser. Applied to checkO/thmD_F.py it gives thmD_SOF.py (whole-path overlap reading).

Hooks (module globals, None = driver behaviour):
  PATH_HOOK(role, ctx, A, src, tgt, nodes, edges, emb, rng, i) -> (nodes, edges)
      called for the level-0 path P (role 'P', A = level-0 annulus, src = f, tgt = g) and for
      every path of batch 1/2 (role 'Pi' or 'leaf', src = A's piece of p_i^0, tgt = of p_i^1),
      after the driver has read its own tree path. The hook may return any other w-shortest
      path between the same two nodes of A (the lemmas assume an arbitrary exact shortest path).
  INC_HOOK(A, i, Pn_, Pe_, Qn, Qe, xt, yt, i1, i2, ov, pieces, newnodes, comp, stats, level)
      called at every incision, after the Lemma O checks.
  CHILD_HOOK(A, C, side, jj, kk, i, i1, i2, xt, yt, stats)
      called for every called child.
opts['ends'] = 2 or 3 selects the alternatives of RECURSION.md (P_{j_A}, P_{k_A}; or P_{i-}/P_{i+}
only when i1 < j_A / i2 > k_A); 1 (default) is unchanged.
Usage: python3 -I patchSO.py ../checkO/thmD_R.py thmD_SO.py
"""
import sys

src = open(sys.argv[1]).read()

a0 = "INF = float('inf')\n"
assert src.count(a0) == 1
src = src.replace(a0, a0 + "PATH_HOOK = None\nINC_HOOK = None\nCHILD_HOOK = None\n", 1)

a1 = "    Pn, Pe = tree_path(par0, face2np[f], face2np[g])\n"
assert src.count(a1) == 1
src = src.replace(a1, a1 + """    if PATH_HOOK is not None:
        Pn, Pe = PATH_HOOK('P', ctx, A0, face2np[f], face2np[g], Pn, Pe, emb, rng, None)
""", 1)

a2 = ("                edges = [(y, x) for (x, y) in reversed(edges)]\n"
      "            L = dc[tgt]\n"
      "            if L != dC[tgt]:\n")
assert src.count(a2) == 1
src = src.replace(a2, """                edges = [(y, x) for (x, y) in reversed(edges)]
            if PATH_HOOK is not None:
                nodes, edges = PATH_HOOK('leaf' if leaf else 'Pi', ctx, A, A.piece[(i, 0)], A.piece[(i, 1)],
                                         nodes, edges, emb, rng, i)
            L = dc[tgt]
            if L != dC[tgt]:
""", 1)

a3 = "            chain_l, chain_r = [], []\n"
assert src.count(a3) == 1
src = src.replace(a3, """            if INC_HOOK is not None:
                INC_HOOK(A, i, Pn_, Pe_, Qn, Qe, xt, yt, i1, i2, ov, pieces, newnodes, comp, stats, level)
""" + a3, 1)

a4 = "                nxt.append(C)\n"
assert src.count(a4) == 1
src = src.replace(a4, """                if CHILD_HOOK is not None:
                    CHILD_HOOK(A, C, sidename, jj, kk, i, i1, i2, xt, yt, stats)
""" + a4, 1)

# ENDS variants (opts['ends']): 1 = the repair of Lemma S2 (P_{i-}, P_{i+}); 2 = the alternative
# of RECURSION.md (P_{j_A}, P_{k_A}); 3 = the remark there (P_{i-} only if i1 < j_A, P_{i+} only if i2 > k_A)
a5 = "                for q, tt in enumerate((max(min(tidx), A.j), min(max(tidx), A.k))):\n"
assert src.count(a5) == 1
src = src.replace(a5, """                _e = opts.get('ends')
                if _e == 2:
                    _ends = (A.j, A.k)
                elif _e == 3:
                    _ends = (A.j if min(tidx) < A.j else i, A.k if max(tidx) > A.k else i)
                else:
                    _ends = (max(min(tidx), A.j), min(max(tidx), A.k))
                for q, tt in enumerate(_ends):
""", 1)

open(sys.argv[2], 'w').write(src)
print('ok')
