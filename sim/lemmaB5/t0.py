import sys, os
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from harness import *
# cycle 0..5, path tree 0-1-2-3-4-5, chord 5-0
n=6
V=list(range(n))
rot={v:[(v-1)%n,(v+1)%n] for v in V}
par={0:None}
for v in range(1,n): par[v]=v-1
for r_ in [0]:
  for k in range(2):
    res=check(V,rot,par,0,k)
    print(res['kind'],res['x'],res['z'],res['ins'],res['out'])
# wheel
n=7; V=list(range(n)); hub=6
rot={v:[(v-1)%6,hub,(v+1)%6] for v in range(6)}; rot[hub]=list(range(6))[::-1]
idx=mkidx(rot); print(is_planar_rot(rot,idx))
rot[hub]=list(range(6))[::-1]; print(is_planar_rot(rot,mkidx(rot)))
par={hub:None}
for v in range(6): par[v]=hub
for k in range(6):
    res=check(V,rot,par,hub,k); print(res['kind'],res['x'],res['z'],res['ins'],res['out'])
report()
