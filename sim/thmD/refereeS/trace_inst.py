import sys, os, json, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import thmD_refS as T
ends=[(0,1),(0,2),(2,7),(1,3),(7,8),(8,4),(4,5),(8,9),(7,10),(4,9),(5,8),(6,5),(7,0),(9,5),(5,10),(1,2),(8,2),(1,7),(8,10),(0,3),(2,3),(9,6)]
c=[1,1,1,1,1,1,3,1,13,1,50,1,13,2,50,20,1,30,47,20,30,2]
rot=[[0,38,2,25],[1,34,30,6],[3,40,31,4,33],[7,41,39],[11,12,18],[13,28,20,27,23],[22,43],[24,8,16,5,35],[9,32,36,10,14,21],[15,19,42,26],[17,29,37]]
I=dict(n=11, ends=ends, rot=rot, cap=c, s=5, t=3)
for e in (0,1):
    C=collections.Counter(); rep=collections.Counter()
    for r in range(80):
        opts=dict(mode='claimed', variant='fixed', tiebreak='minid', pairs=1, pcommon=0.0, pfar=(r%2)*1.0, e0rule='formal', ends=e, refS=1)
        chk, info = T.run_one(I, opts, 7919*r+(r%2))
        rep[info.get('reported')]+=1
        for k in chk.flags: C[k]+=1
    print('ends',e,'reported',dict(rep),'flags',dict(C))
