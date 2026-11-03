import os
import sys, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sim
ends=[(0,1),(0,2),(2,7),(1,3),(7,8),(8,4),(4,5),(8,9),(7,10),(4,9),(5,8),(6,5),(7,0),(9,5),(5,10),(1,2),(8,2),(1,7),(8,10),(0,3),(2,3),(9,6)]
cap=[1,1,1,1,1,1,3,1,13,1,50,1,13,2,50,20,1,30,47,20,30,2]
rot=[[0,38,2,25],[1,34,30,6],[3,40,31,4,33],[7,41,39],[11,12,18],[13,28,20,27,23],[22,43],[24,8,16,5,35],[9,32,36,10,14,21],[15,19,42,26],[17,29,37]]
I=sim.Inst(11,ends,rot,cap,5,3)
orig=sim.dijk
K=19*11+1
for name,ln in (('capacity',lambda e:cap[e]),('w=Kc\'+1',lambda e:K*(121*cap[e]+1)+1)):
    rec=[]
    log=[]
    st=collections.Counter()
    # wrap Fail-free run, instrumenting compute via results + a recompute of counts
    R=sim.run(I,12,1,3,2,length=ln,log=log,stats=st)
    print(name,'reported',min(r[1] for r in R['results']),'nonunique',st['nonunique'],'of computed non-overlap paths; P nonunique',st['P_nonunique'],'overlap',st['overlap_a'],st['overlap_b'])
    for l in log: print('  ',l)
# level-3 leaf [0,1] enumerate the tie by hand: two walks of capacity 105 from p0^0 to p0^1
print('walk via f7 f11  ',sum(cap[e] for e in [11,9,5,14,10,13]))
print('walk via copies  ',sum(cap[e] for e in [11,9,5,14,4,16,18,5,9,11]))
