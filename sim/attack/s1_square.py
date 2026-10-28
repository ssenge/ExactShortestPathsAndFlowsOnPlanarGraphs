"""Attack (d): is the squaring in (S1) real?  O = star (centre c, terminals t0..t3, arcs both
ways weight 1): all distances 2, every Monge inequality tight.  Input delta = oracle-style
overestimate of O: delta = dist_O * (1+g)^{b}, b in {0,1}.  [1, Thm 2] returns SOME optimal
point of the LP at the minimum alpha*.  We maximise the worst ratio d/dist_O over that optimal
face and compare with (1+g) (what [1] claims) and (1+g)^2 (the witness-O bound)."""
import sys, itertools, numpy as np
sys.path.insert(0, '.')
from rot import monge_lp
g = 0.1
T = ['t0', 't1', 't2', 't3']
pairs = [(a, b) for a in T for b in T if a != b]
best = (0, None)
for bits in itertools.product((0, 1), repeat=len(pairs)):
    delta = {p: 2 * (1 + g) ** b for p, b in zip(pairs, bits)}
    st, a, _ = monge_lp(delta, T)
    for p in pairs:
        st2, _, d = monge_lp(delta, T, fix_alpha=a + 1e-12, objective={p: -1})
        if st2 == 0 and d[p] / 2 > best[0]:
            best = (d[p] / 2, (bits, a, p))
print('max over inputs/optimal LP points of d/dist_O = %.6f ; 1+g = %.4f ; (1+g)^2 = %.4f' % (best[0], 1 + g, (1 + g) ** 2))
print('alpha* for that input = %.6f' % best[1][1])
