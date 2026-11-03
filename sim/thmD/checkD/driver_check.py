import os
"""Run the repo driver (read-only import) on the printed example and on (D1)."""
import sys, collections, json
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import thmD
ends=[(0,1),(0,2),(2,7),(1,3),(7,8),(8,4),(4,5),(8,9),(7,10),(4,9),(5,8),(6,5),(7,0),(9,5),(5,10),(1,2),(8,2),(1,7),(8,10),(0,3),(2,3),(9,6)]
cap=[1,1,1,1,1,1,3,1,13,1,50,1,13,2,50,20,1,30,47,20,30,2]
rot=[[0,38,2,25],[1,34,30,6],[3,40,31,4,33],[7,41,39],[11,12,18],[13,28,20,27,23],[22,43],[24,8,16,5,35],[9,32,36,10,14,21],[15,19,42,26],[17,29,37]]
I=dict(n=11,ends=ends,rot=rot,cap=cap,s=5,t=3)
for en in (0,1):
    C=collections.Counter(); ex=[]; faces=collections.Counter()
    for r in range(40):
        for pfar in (1.0,0.0):
            opts=dict(mode='claimed',variant='fixed',tiebreak='minid',pairs=1,pcommon=0.0,pfar=pfar,e0rule='formal',ends=en)
            chk,info=thmD.run_one(I,opts,7919*r+int(pfar))
            C['runs']+=1
            for k in chk.flags: C[k]+=1
            faces[(info.get('pf',[None])[0],info.get('pf',[None])[-1])]+=1
            if 'iv_value' in chk.flags: ex.append((r,pfar,info.get('reported'),info.get('mincut'),info.get('pf'),info.get('eps'),info.get('ept')))
    print('ends',en,dict(C)); print(' face pairs',dict(faces)); print(' fails',ex[:4])
e03,e01,e12,e23,e13=0,1,2,3,4
ends2=[(0,3),(0,1),(1,2),(2,3),(1,3)]
d=lambda e,v:2*e+(0 if ends2[e][0]==v else 1)
rot2=[[d(e03,0),d(e01,0)],[d(e12,1),d(e13,1),d(e01,1)],[d(e12,2),d(e23,2)],[d(e23,3),d(e03,3),d(e13,3)]]
J=dict(n=4,ends=ends2,rot=rot2,cap=[1,1,1,1,5],s=1,t=2)
for var in ('literal','fixed'):
    C=collections.Counter(); rep=collections.Counter()
    for r in range(200):
        opts=dict(mode='claimed',variant=var,tiebreak='minid',pairs=1,pcommon=0.0,pfar=1.0,e0rule='formal',ends=1)
        chk,info=thmD.run_one(J,opts,r)
        C['runs']+=1
        for k in chk.flags: C[k]+=1
        rep[(info.get('reported'),info.get('mincut'),tuple(info.get('pf',[])),str(info.get('eps',{}).get('e0')),str(info.get('ept',{}).get('e0')))]+=1
    print('D1',var,dict(C)); print('  ',dict(rep))
# single edge st (D2)
K=dict(n=2,ends=[(0,1)],rot=[[0],[1]],cap=[3],s=0,t=1)
for var in ('literal','fixed'):
    C=collections.Counter()
    for r in range(20):
        opts=dict(mode='claimed',variant=var,tiebreak='minid',pairs=1,pcommon=0.5,pfar=1.0,e0rule='formal',ends=1)
        chk,info=thmD.run_one(K,opts,r)
        C['runs']+=1
        for k in chk.flags: C[k]+=1
    print('D2 single edge',var,dict(C))
