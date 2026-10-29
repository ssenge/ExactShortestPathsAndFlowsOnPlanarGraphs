import sys, math
sys.path.insert(0, sys.argv[1])
from emb import enumerate_maps, canon
L = enumerate_maps(20, 7)
for m, maps in sorted(L.items()):
    tot = 0
    for (n, ends, rot) in maps:
        # automorphisms = number of roots achieving the canonical code
        pos = {}
        for v in range(n):
            for i, d in enumerate(rot[v]):
                pos[d] = (v, i)
        def sig(d):
            v, i = pos[d]; r = rot[v]; return r[(i + 1) % len(r)]
        codes = []
        for root in range(2 * m):
            lab = {root: 0}; order = [root]; k = 0; code = []
            while k < len(order):
                d = order[k]; k += 1
                for x in (sig(d), d ^ 1):
                    if x not in lab:
                        lab[x] = len(order); order.append(x)
                code.append((lab[sig(d)], lab[d ^ 1]))
            codes.append(tuple(code))
        b = min(codes)
        aut = codes.count(b)
        tot += 2 * m // aut
    f = 2 * math.factorial(4 * m + 1) // (math.factorial(m + 1) * math.factorial(3 * m + 2))
    print(m, len(maps), 'rooted', tot, 'formula', f)
