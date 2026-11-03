"""Reads what neg.py's controls compare. Imports neg.py read-only from the repository; writes nothing there (-B).
1. Are the instances of the controls 'the same', as Section 9 says? Logs the sequence of instances per mode.
2. Does the code compute any st-cut? Static check on its source.
Controls are rerun separately with neg.py itself."""
import hashlib, importlib.util, os, random, re, sys
REPO = __import__('os').path.join(__import__('os').path.dirname(__import__('os').path.abspath(__file__)), '..', 'neg.py')
spec = importlib.util.spec_from_file_location('neg', REPO)
neg = importlib.util.module_from_spec(spec)
spec.loader.exec_module(neg)


def seq(mode, seed, count):
    rng = random.Random(seed)
    out = []
    while len(out) < count:
        n, U, V, W, kind = neg.restricted_instance(rng, True)
        if not neg.is_restricted(n, U, V, W):
            continue
        out.append(hashlib.md5(repr((n, U.tolist(), V.tolist(), W.tolist())).encode()).hexdigest()[:6])
        neg.restricted(n, U, V, W, rng, R=2, t=2, c=1.0, mode=mode)
    return out


if __name__ == '__main__':
    base = seq('', 7, 8)
    print('clean   ', base)
    for m in ['t0', 'oneR', 'noprev', 'nomin', 'nooffset', 'wrongdir']:
        s = seq(m, 7, 8)
        print(m.ljust(8), s, 'same as clean at positions', [i for i in range(8) if s[i] == base[i]])
    src = open(REPO).read()
    print('occurrences of "cut" in neg.py:', [l.strip()[:90] for l in src.splitlines() if 'cut' in l.lower()])
    print('minimum_cut' in src, 'residual' in src)
