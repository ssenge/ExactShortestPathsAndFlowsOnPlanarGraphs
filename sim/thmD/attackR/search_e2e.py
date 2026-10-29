"""search small instances where the simulated [18] recursion misses lambda although every
shortest path it picks is unique (generic capacities).
usage: python3 -I search_e2e.py START COUNT WORKERS NMIN NMAX"""
import sys, os, collections, random, json, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from emb import random_map, Emb, grid_map


def simple_map(rng, n_target, extra_frac):
    """random simple connected plane graph: random tree plus chords inside faces between
    non-adjacent vertices."""
    n = 2
    ends = [(0, 1)]
    rot = [[0], [1]]
    adjs = {frozenset((0, 1))}
    while n < n_target:
        v = rng.randrange(n)
        i = rng.randrange(len(rot[v]))
        e = len(ends)
        ends.append((v, n))
        adjs.add(frozenset((v, n)))
        rot[v].insert(i + 1, 2 * e)
        rot.append([2 * e + 1])
        n += 1
    for _ in range(int(extra_frac * 2 * n)):
        E = Emb(n, ends, rot)
        cyc = E.faces[rng.randrange(len(E.faces))]
        cs = [E.eta(d) for d in cyc]
        pairs = [(a, b) for a in range(len(cs)) for b in range(a + 1, len(cs))
                 if cs[a][0] != cs[b][0] and frozenset((cs[a][0], cs[b][0])) not in adjs]
        if not pairs:
            continue
        a, b = rng.choice(pairs)
        (u, i), (v, j) = cs[a], cs[b]
        e = len(ends)
        ends.append((u, v))
        adjs.add(frozenset((u, v)))
        rot[u].insert(i + 1, 2 * e)
        rot[v].insert(j + 1, 2 * e + 1)
    E = Emb(n, ends, rot)
    assert E.genus_ok()
    return E
from deep import Run
SIMPLE = os.environ.get("SIMPLE") == "1"


def work(args):
    start, count, nmin, nmax = args
    C = collections.Counter()
    hits = []
    for sd in range(start, start + count):
        rng = random.Random(sd)
        n = rng.randint(nmin, nmax)
        if SIMPLE:
            if rng.random() < 0.2:
                emb = grid_map(rng, rng.randint(2, 5), rng.randint(2, 5), drop=rng.choice([0, 0.15, 0.3]))
            else:
                emb = simple_map(rng, n, rng.choice([0.5, 0.8, 1.0, 1.4]))
        else:
            emb = random_map(rng, n, extra_frac=rng.choice([0.5, 0.8, 1.0, 1.4]), par_prob=rng.choice([0, 0.1]))
        if SIMPLE and len({tuple(sorted(e)) for e in emb.ends}) < emb.m:
            C["skip_multi"] += 1
            continue
        emb = emb.with_cap([rng.randint(1, 10 ** 6) for _ in range(emb.m)])
        s, t = rng.sample(range(emb.n), 2)
        notes = []
        R = Run(emb, s, t, random.Random(sd + 1), 'random', frozenset(), C, notes, dict(seed=sd))
        try:
            R.run()
        except Exception as ex:
            C['exception'] += 1
            continue
        C['inst'] += 1
        if R.nonunique == 0:
            C['unique'] += 1
        if any(k == 'e2e_value' for k, _, _ in notes):
            C['fail'] += 1
            if R.nonunique == 0:
                C['fail_unique'] += 1
                hits.append(dict(seed=sd, n=emb.n, m=emb.m, s=s, t=t, Plen=len(R.pe), lam=R.lam,
                                 got=min(r[2] for r in R.results), ends=emb.ends, rot=emb.rot, cap=emb.cap))
    return C, hits


def main():
    start, count, workers, nmin, nmax = map(int, sys.argv[1:6])
    per = 2000
    jobs = [(st, min(per, start + count - st), nmin, nmax) for st in range(start, start + count, per)]
    import multiprocessing as mp
    C = collections.Counter()
    hits = []
    t0 = time.time()
    with mp.Pool(workers) as pool:
        for c, h in pool.imap_unordered(work, jobs):
            C.update(c)
            hits += h
    hits.sort(key=lambda h: (h['m'], h['n']))
    print(json.dumps(dict(args=sys.argv[1:], secs=round(time.time() - t0), counts=dict(C), hits=hits[:20]), default=str))


if __name__ == '__main__':
    main()
