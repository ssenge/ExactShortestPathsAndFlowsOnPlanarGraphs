import os
"""Recompute Example ex:recursion and (D1) from the data AS PRINTED in the paper."""
import sys, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sim, networkx as nx
ends=[(0,1),(0,2),(2,7),(1,3),(7,8),(8,4),(4,5),(8,9),(7,10),(4,9),(5,8),(6,5),(7,0),(9,5),(5,10),(1,2),(8,2),(1,7),(8,10),(0,3),(2,3),(9,6)]
cap=[1,1,1,1,1,1,3,1,13,1,50,1,13,2,50,20,1,30,47,20,30,2]
rot=[[0,38,2,25],[1,34,30,6],[3,40,31,4,33],[7,41,39],[11,12,18],[13,28,20,27,23],[22,43],[24,8,16,5,35],[9,32,36,10,14,21],[15,19,42,26],[17,29,37]]
I=sim.Inst(11,ends,rot,cap,5,3)
print('Euler', I.euler(), 'faces', len(I.faces), 'edges', I.m)
print('faces', {k:[d>>1 for d in f] for k,f in enumerate(I.faces)})
G=nx.Graph()
for e,(u,v) in enumerate(ends):
    assert not G.has_edge(u,v); G.add_edge(u,v,capacity=cap[e])
print('simple planar', nx.check_planarity(G)[0], 'mincut', nx.minimum_cut(G,5,3)[0])
v,(S,T)=nx.minimum_cut(G,5,3); print(' cut edges', [e for e,(a,b) in enumerate(ends) if (a in S)!=(b in S)])
sf=sorted({I.corner_face(5,k) for k in range(5)}); tf=sorted({I.corner_face(3,k) for k in range(3)})
print('faces at s',sf,'faces at t',tf)
tally=collections.Counter()
for f in sf:
  for g in tf:
    for cs in [k for k in range(5) if I.corner_face(5,k)==f]:
      for ct in [k for k in range(3) if I.corner_face(3,k)==g]:
        for flip in (False,True):
          log=[];st=collections.Counter()
          try:
            R=sim.run(I,f,g,cs,ct,log=log,stats=st,flip=flip)
            val=min(r[1] for r in R['results'])
            R2=sim.run(I,f,g,cs,ct,repair=True,flip=flip)
            val2=min(r[1] for r in R2['results'])
          except sim.Fail as ex:
            print('FAIL',f,g,cs,ct,flip,ex); continue
          tally[(val,val2)]+=1
          if val!=15 or (f,g)==(12,1):
            print('f,g',f,g,'corners',cs,ct,'flip',flip,'reported',val,'with repair',val2,'P faces',R['Pf'],'P edges',R['Pe'],'lam',R['lam'],'nonunique',st['nonunique'],st['P_nonunique'],'ov',st['overlap_a'],st['overlap_b'])
            print('   results',sorted(set(R['results'])))
            print('   repair ',sorted(set(R2['results'])))
            for l in log: print('   ',l)
print('tally (noRepair,repair)',tally)
# (D1) instance
e03,e01,e12,e23,e13=0,1,2,3,4
ends2=[(0,3),(0,1),(1,2),(2,3),(1,3)]
cap2=[1,1,1,1,5]
d=lambda e,v:2*e+(0 if ends2[e][0]==v else 1)
rot2=[[d(e03,0),d(e01,0)],[d(e12,1),d(e13,1),d(e01,1)],[d(e12,2),d(e23,2)],[d(e23,3),d(e03,3),d(e13,3)]]
J=sim.Inst(4,ends2,rot2,cap2,1,2)
print('D1 Euler',J.euler(),'faces',[[ends2[x>>1] for x in f] for f in J.faces])
G2=nx.Graph()
for e,(u,v) in enumerate(ends2): G2.add_edge(u,v,capacity=cap2[e])
print('D1 mincut',nx.minimum_cut(G2,1,2)[0])
for f in sorted({J.corner_face(1,k) for k in range(3)}):
  for g in sorted({J.corner_face(2,k) for k in range(2)}):
    for cs in [k for k in range(3) if J.corner_face(1,k)==f]:
      for ct in [k for k in range(2) if J.corner_face(2,k)==g]:
        log=[]
        try:
          R=sim.run(J,f,g,cs,ct,log=log)
          print(' D1 f,g',f,g,cs,ct,'P edges',[ends2[e] for e in R['Pe']],'val',min(r[1] for r in R['results']),log)
        except sim.Fail as ex: print(' D1 FAIL',f,g,ex)
