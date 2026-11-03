"""The smallest instance for the label collision in [3, Section 5.2], and for the repair. Kept arcs a->b, c->d; a removed arc a->c.
Vertices: a=0, b=1, c=2, d=3. Self-check: fails if the literal labels stop colliding or the leader repair starts colliding."""
import os, random, sys
from collections import Counter
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from t4_ldd import Topsort

kept = [(0, 1), (2, 3)]
rng = random.Random(1)
for cc, dil in (('parent', 2), ('parent', 8), ('own', 2), ('leader', 2)):
    seen = Counter()
    for _ in range(2000):
        r = Topsort(4, kept, dil=dil, cc_n=cc, net=kept).run(rng)
        seen[tuple(r)] += 1
    print(cc, 'dil', dil, 'labels (a,b,c,d):', seen.most_common(3), 'a==c in', sum(c for x, c in seen.items() if x[0] == x[2]), 'of 2000')
    if cc in ('parent', 'own'):
        assert all(x[0] == x[2] for x in seen)
    if cc == 'leader':
        assert all(len(set(x)) == 4 and x[0] > x[1] and x[2] > x[3] for x in seen)
print('self-check passed')
