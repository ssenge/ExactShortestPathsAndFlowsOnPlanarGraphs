import sys,os,random,collections
sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
sys.dont_write_bytecode=True
import nd_core as X, nd_drive as D, nd_fam as F
ctx=X.Ctx(); rng=random.Random(5)
for k in range(150):
    mp,S,T,kind,pts=F.fam_grid(rng,36,straight=True)
    if S==T: continue
    sc,cap=F.caps_for(mp,rng,kind,S)
    I=X.Inst(mp.n,mp.ends,mp.rot,cap,S,T,coords=pts,tag='geo:'+sc)
    lst=list(D.all_choices(I)); rng.shuffle(lst)
    for f,g,cs,ct in lst[:4]:
        R=X.Run(I,ctx,X.PolicyCh(rng,'rand'),f,g,cs,ct,dict(cap_b=1,cap_paths=8,sample=True,ghat=False))
        R.go()
C=ctx.C
print({k:v for k,v in C.items() if k.startswith(('a2.geo','FAIL','a1.geo'))}, C['runs'])
