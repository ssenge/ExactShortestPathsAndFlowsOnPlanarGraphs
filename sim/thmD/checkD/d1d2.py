import os
import sys, collections
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
import thmD
ends2=[(0,3),(0,1),(1,2),(2,3),(1,3)]
d=lambda e,v:2*e+(0 if ends2[e][0]==v else 1)
rot2=[[d(0,0),d(1,0)],[d(2,1),d(4,1),d(1,1)],[d(2,2),d(3,2)],[d(3,3),d(0,3),d(4,3)]]
J=dict(n=4,ends=ends2,rot=rot2,cap=[1,1,1,1,5],s=1,t=2)
for var in ('literal','fixed'):
    rep=collections.Counter(); fl=collections.Counter()
    for r in range(400):
        opts=dict(mode='claimed',variant=var,tiebreak='minid',pairs=1,pcommon=0.0,pfar=0.0,e0rule='formal',ends=0)
        chk,info=thmD.run_one(J,opts,r)
        key=(tuple(info.get('pf',[])),info.get('reported'),info.get('eps',{}).get('e0'),info.get('ept',{}).get('e0'),info.get('eps',{}).get('mode'),info.get('ept',{}).get('mode'),tuple(sorted(chk.flags)))
        rep[key]+=1
    print('D1',var)
    for k,v in rep.items(): print('   ',k,v)
# (D2) second clause: pendant u at s, u != t.  triangle s,a,t plus pendant u at s
ends3=[(0,1),(1,2),(2,0),(0,3)]  # s=0,a=1,t=2,u=3
rot3=[[0,5,6],[1,2],[3,4],[7]]
# check all rotations of s by brute force
import itertools
for rs in ([0,5,6],[0,6,5]):
    I=dict(n=4,ends=ends3,rot=[rs,[1,2],[3,4],[7]],cap=[2,3,4,1],s=0,t=2)
    for var in ('literal','fixed'):
        rep=collections.Counter()
        for r in range(300):
            opts=dict(mode='claimed',variant=var,tiebreak='minid',pairs=1,pcommon=0.3,pfar=0.3,e0rule='formal',ends=1)
            chk,info=thmD.run_one(I,opts,r)
            rep[(info.get('eps',{}).get('e0'),info.get('eps',{}).get('mode'),tuple(info.get('pf',[])),tuple(sorted(chk.flags)))]+=1
        print('pendant at s rot',rs,var)
        for k,v in sorted(rep.items(),key=str): print('   e0,mode,pf,flags',k,v)
