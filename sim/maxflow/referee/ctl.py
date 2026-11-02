import sys, os, random, collections, math
sys.dont_write_bytecode=True
sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
import networkx as nx, nlem
from fractions import Fraction as Fr
rng=random.Random(5)
def inst():
    while True:
        a,b=rng.randrange(3,6),rng.randrange(3,6)
        H=nx.convert_node_labels_to_integers(nx.grid_2d_graph(a,b))
        ok,em=nx.check_planarity(H)
        g=nlem.G0({v:list(em.neighbors_cw_order(v))[::-1] for v in H})
        s,t=rng.sample(list(H),2)
        R=nlem.shortest_paths(H,s,t,1)[0]
        return H,g,R,s,t
def fail(msg,g,R): pass
# C1: keep the E_C edges of R
st=collections.Counter()
Orig=nlem.NetN
class KeepEC(nlem.NetN):
    def __init__(self,g,R,e='larger',rng=None):
        self._keep=True
        super().__init__(g,R,e,rng)
    def _rot(self):
        g=self.g
        for d in g.darts:
            e=frozenset(d)
            if e not in self.ec_at: self.ec_at[e]=max(d)
        super()._rot()
nlem.NetN=KeepEC
for _ in range(100):
    H,g,R,s,t=inst()
    res=nlem.check_structure(g,R,st,'larger',rng,fail)
print('keep E_C of R:',{k:v for k,v in st.items() if 'FAIL' in k or k=='euler'})
nlem.NetN=Orig
# C2: M far too small: star shortcut
st=collections.Counter()
ol=nlem.lam_exact
def bad_lam(C,g,N,nn,P,pairs,st,fail,tag):
    adj=N.lengths(C,0)
    ga=nlem.gamma_adj(g,N,C)
    for a in P:
        da=nlem.dijkstra(adj,{a:0}); dg=nlem.dijkstra(ga,{g.rgt[a[1]]:0})
        for b in P:
            st['metric']+=1
            if da[b]!=dg[g.rgt[b[1]]]: st['FAIL.metric']+=1
for _ in range(100):
    H,g,R,s,t=inst()
    N=nlem.NetN(g,R); q=N.slit()
    c=nlem.caps(g,rng); bad_lam(c,g,N,len(N.nodes),[x for x in q if x[0]=='c'],None,st,fail,'')
print('M=0:',dict(st))
# C3: no scaling by 2|V| in L (hop term not absorbed)
st=collections.Counter()
of=nlem.portal_b
def bad_b(C,g,N,nn,P,mode,rng):
    maxC=max(C.values()) if C else 0
    M=nn*maxC+1; adj=N.lengths(C,M); b={}
    for a in P:
        dist=nlem.dijkstra(adj,{a:0},f=lambda l:nlem.K*l+1)
        for c in P:
            b[a,c]=math.floor(Fr(dist[c])/(1+nlem.EPS))
    return b
nlem.portal_b=bad_b
for _ in range(100):
    H,g,R,s,t=inst()
    N=nlem.NetN(g,R); q=N.slit(); c=nlem.caps(g,rng)
    nlem.pipeline(g,N,q,c,s,t,st,fail,'rand',rng)
print('L without factor 2|V|:',{k:v for k,v in st.items() if 'FAIL' in k or k in('final','exact_ok','steps')})
nlem.portal_b=of
