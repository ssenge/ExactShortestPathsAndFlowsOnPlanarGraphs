import networkx as nx, itertools
ends=[(0,1),(0,2),(2,7),(1,3),(7,8),(8,4),(4,5),(8,9),(7,10),(4,9),(5,8),(6,5),(7,0),(9,5),(5,10),(1,2),(8,2),(1,7),(8,10),(0,3),(2,3),(9,6)]
c=[1,1,1,1,1,1,3,1,13,1,50,1,13,2,50,20,1,30,47,20,30,2]
rot=[[0,38,2,25],[1,34,30,6],[3,40,31,4,33],[7,41,39],[11,12,18],[13,28,20,27,23],[22,43],[24,8,16,5,35],[9,32,36,10,14,21],[15,19,42,26],[17,29,37]]
s,t=5,3
G=nx.Graph()
for e,(u,v) in enumerate(ends):
    assert not G.has_edge(u,v); G.add_edge(u,v,capacity=c[e])
print('simple', G.number_of_nodes(), G.number_of_edges())
val,(S,T)=nx.minimum_cut(G,s,t)
print('mincut', val, sorted(S))
print('cut edges', [e for e,(u,v) in enumerate(ends) if (u in S)!=(v in S)])
# planarity of the given rotation: darts 2e, 2e+1 (assume dart 2e at ends[e][0])
E=len(ends); nxt={}
for v,r in enumerate(rot):
    for k,d in enumerate(r):
        assert (ends[d>>1][d&1])==v, (v,d)
        nxt[d]=r[(k+1)%len(r)]
seen=set(); F=0
for d in range(2*E):
    if d in seen: continue
    F+=1; x=d
    while x not in seen:
        seen.add(x); x=nxt[x^1]
print('V-E+F', len(rot)-E+F)
print('ok planar' if nx.check_planarity(G)[0] else 'nonplanar')
