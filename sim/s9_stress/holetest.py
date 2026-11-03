import sys, os, random
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import adv
from adv import *
import numpy as np
# 4x4 grid of vertices -> 3x3 inner faces
k = 4; pos = np.array([(i + 0.01 * j, j + 0.013 * i) for i in range(k) for j in range(k)], float)
vid = lambda i, j: i * k + j
E = []
for i in range(k):
    for j in range(k):
        if i + 1 < k: E.append((vid(i, j), vid(i + 1, j)))
        if j + 1 < k: E.append((vid(i, j), vid(i, j + 1)))
g = PG(pos, E)
eng = Engine(g, set(), random.Random(0), dict(light=True))
# dart sets per face
fd = {}
for f, cs in enumerate(g.fcorners):
    fd[f] = set(int(eng.cd1[c]) for c in cs) | set(int(eng.cd2[c]) for c in cs)
outer = max(fd, key=lambda f: len(fd[f]))
inner = [f for f in fd if f != outer]
def faceset(f):  # centre of face
    vs = sorted({int(g.cv[c]) for c in g.fcorners[f]}); return vs
def Ewithout(darts):
    E = {}
    for e in range(g.m):
        s = frozenset(t for t in (0, 1) if 2 * e + t not in darts)
        if s: E[e] = s
    return E
def report(name, darts, expect):
    Ed = Ewithout(darts)
    print(name, 'euler', eng.holes_euler(Ed), 'tri', eng.holes_tri(Ed), 'engine', eng.holes(Ed), 'expect', expect)
cent = {f: tuple(np.mean([g.pos[v] for v in faceset(f)], 0).round()) for f in inner}
byc = {c: f for f, c in cent.items()}
print(sorted(byc))
f00 = byc[(0.0, 0.0)] if (0.0, 0.0) in byc else inner[0]
fs = sorted(inner, key=lambda f: cent[f])
report('one inner face removed', fd[fs[0]], 1)
report('outer face removed', fd[outer], 1)
report('outer + one inner', fd[outer] | fd[fs[4]], 2)
report('two diagonal faces (touch at a vertex)', fd[fs[0]] | fd[fs[4]], 2)
# half a face: only two of its four darts missing, non-adjacent -> two separate triangles = 2 holes
d = sorted(fd[fs[4]])
# pick darts of opposite edges in face fs[4]
cs = g.fcorners[fs[4]]
dl = [int(eng.cd1[c]) for c in cs]
report('two opposite triangles of one face', {dl[0], dl[2]}, 2)
report('two adjacent triangles of one face', {dl[0], dl[1]}, 1)
