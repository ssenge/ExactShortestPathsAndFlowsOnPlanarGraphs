import sys,os,collections,random
sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
sys.dont_write_bytecode=True
import nd_core as X, nd_drive as D, nd_fam as F
ends=[(0,1),(0,2),(2,7),(1,3),(7,8),(8,4),(4,5),(8,9),(7,10),(4,9),(5,8),(6,5),(7,0),(9,5),(5,10),(1,2),(8,2),(1,7),(8,10),(0,3),(2,3),(9,6)]
cap=[1,1,1,1,1,1,3,1,13,1,50,1,13,2,50,20,1,30,47,20,30,2]
rot=[[0,38,2,25],[1,34,30,6],[3,40,31,4,33],[7,41,39],[11,12,18],[13,28,20,27,23],[22,43],[24,8,16,5,35],[9,32,36,10,14,21],[15,19,42,26],[17,29,37]]
I=X.Inst(11,ends,rot,cap,5,3)
print('faces',len(I.faces),'euler',I.euler())
ctx=X.Ctx()
R=X.Run(I,ctx,X.FirstCh(),12,1,3,2,dict(cap_b=4,cap_paths=8))
R.go()
print('P faces',R.Pf,'m',R.m,'mc',I.mc,'lam',min(R.lam.values())//I.K//(I.N**2))
fails={k:v for k,v in ctx.C.items() if k.startswith('FAIL')}
print('fails',fails)
for k in sorted(ctx.C):
    if not k.startswith(('a2.chk|','FAIL')): print(k,ctx.C[k])
for k,v in ctx.fails.items(): print(k,v['detail'],v['level'])
