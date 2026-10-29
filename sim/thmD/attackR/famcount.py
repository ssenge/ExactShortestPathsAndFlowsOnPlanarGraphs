"""Per-family instance counts of the deep runs, replaying only the family draw of each seed."""
import random, json, collections, os
HERE = os.path.dirname(os.path.abspath(__file__))
FAMS = ['rand', 'rand', 'rand', 'grid', 'sparse', 'dense']
RUNS = [  # name, start, count, forced families or None
    ('deep_A_mix_default', 100000, 60000, None), ('deep_B_big_default', 200000, 30000, ['big', 'biggrid']),
    ('deep_C_litchord', 300000, 40000, None), ('deep_D_litfull', 400000, 40000, None),
    ('deep_E_kissc', 500000, 40000, ['grid', 'sparse', 'rand', 'biggrid']),
    ('deep_F_kissc_lit', 600000, 30000, ['grid', 'sparse', 'rand', 'biggrid']),
    ('e2e_gen (x4 policies)', 1000000, 150000, None), ('e2e_tie_kiss', 2000000, 150000, None),
    ('sssp_mix', 3000000, 30000, None)]
tot = collections.Counter()
for name, st, cnt, force in RUNS:
    c = collections.Counter()
    for sd in range(st, st + cnt):
        rng = random.Random(sd)
        f = rng.choice(FAMS)
        if force:
            f = rng.choice(force)
        c[f] += 1
    mult = 4 if name.startswith('e2e_gen') else 1
    for k, v in c.items():
        tot[k] += v * mult
    print(name, dict(c))
c = collections.Counter()
for sd in range(0, 1500000):
    rng = random.Random(sd)
    rng.randint(4, 22)
    c['grid (simple)' if rng.random() < 0.2 else 'simple_map'] += 1
print('search_simple', dict(c))
tot.update(c)
tot['random_map (multigraph search, n 4..12)'] += 1000000
print('TOTAL', dict(tot))
