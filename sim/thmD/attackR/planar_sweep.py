"""Table R / Definition R for arbitrary incised sets.

The proof of Lemma R (3) uses no property of I_l except the option conflict (an incised dart
that is out(c*) of an R-mode corner and in(c*') of an L-mode corner). So for every map, every
s != t, every corner at s and at t (any face), every mode pair and every I subset of E
(all subsets if m <= FULLM, else NSAMP random ones), build Definition R and check
(1), (2), Claim 1, (4), Table R consistency and Euler. Option-conflict configurations are
counted separately (the lemma says Reif never produces them).
usage: python3 -I planar_sweep.py NMAX MMAX FULLM NSAMP WORKERS [variant]
"""
import sys, os, collections, itertools, random, json, time, traceback
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from emb import Emb, enumerate_maps
import defr


def conflict(emb, I, cuts):
    cut = {(cu['z'], cu['i'] % emb.deg(cu['z'])): cu['mode'] for cu in cuts}
    outR = {emb.dout(c) for c, mu in cut.items() if mu == 'R'}
    inL = {emb.din(c) for c, mu in cut.items() if mu == 'L'}
    return any((d >> 1) in I for d in outR & inL)


def work(args):
    maps, fullm, nsamp, seed, var = args
    rng = random.Random(seed)
    C = collections.Counter()
    notes = []
    for (n, ends, rot) in maps:
        emb = Emb(n, ends, rot)
        m = emb.m
        if m <= fullm:
            Is = [set(e for e in range(m) if k >> e & 1) for k in range(1 << m)]
        else:
            Is = [set(e for e in range(m) if rng.random() < 0.5) for _ in range(nsamp)]
        for s in range(n):
            for t in range(n):
                if s == t:
                    continue
                for cs in range(emb.deg(s)):
                    for ct in range(emb.deg(t)):
                        for ms in 'LR':
                            for mt in 'LR':
                                cuts = [dict(z=s, i=cs, mode=ms, role='s'), dict(z=t, i=ct, mode=mt, role='t')]
                                for I in Is:
                                    cf = conflict(emb, I, cuts)
                                    key = 'conf' if cf else 'ok'
                                    fl = []

                                    def bad(k, v, fl=fl):
                                        fl.append((k, str(v)[:300]))
                                    try:
                                        G = defr.build(emb, I, cuts, var)
                                        defr.check_props(G, bad, full=(m <= 6))
                                        defr.check_planar(G, bad)
                                    except Exception:
                                        fl.append(('exception', traceback.format_exc()[-400:]))
                                    C[key + '_built'] += 1
                                    if G.e0 in I:
                                        C[key + '_e0_incised'] += 1
                                    if G.e0 in I and G.e0 == G.elast:
                                        C[key + '_e0_eq_elast_incised'] += 1
                                    if fl:
                                        C[key + '_FAIL'] += 1
                                        for k, _ in fl:
                                            C[key + '_BAD_' + k] += 1
                                        if len(notes) < 30 and (key == 'ok' or len(notes) < 10):
                                            notes.append(dict(cls=key, fl=fl[:3], n=n, ends=ends, rot=rot, s=s, t=t,
                                                              cuts=[(c['i'], c['mode']) for c in cuts], I=sorted(I)))
        C['maps'] += 1
    return C, notes


def main():
    nmax, mmax, fullm, nsamp, workers = map(int, sys.argv[1:6])
    var = frozenset(sys.argv[6].split(',')) if len(sys.argv) > 6 and sys.argv[6] else frozenset()
    t0 = time.time()
    L = enumerate_maps(nmax, mmax)
    allmaps = [M for m in sorted(L) for M in L[m]]
    chunks = [allmaps[i::workers * 4] for i in range(workers * 4)]
    import multiprocessing as mp
    C = collections.Counter()
    notes = []
    with mp.Pool(workers) as pool:
        for c, nt in pool.imap_unordered(work, [(ch, fullm, nsamp, 7 + j, var) for j, ch in enumerate(chunks)]):
            C.update(c)
            notes += nt
    print(json.dumps(dict(args=sys.argv[1:], secs=round(time.time() - t0), maps=len(allmaps),
                          counts=dict(sorted(C.items())), notes=notes[:40]), indent=1, default=str))


if __name__ == '__main__':
    main()
