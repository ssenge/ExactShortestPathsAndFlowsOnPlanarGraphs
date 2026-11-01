"""Hand check of the oracle: print smallest incisions so that the rule can be followed by hand."""
import sys,os,json
sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
sys.dont_write_bytecode=True
import nd_core as X, nd_drive as D
maps=json.load(open(D.MAPS))
shown=0
for m in ('3','4'):
  for mi,(n,ends,rot) in enumerate(maps[m]):
    for s in range(n):
      for t in range(n):
        if s==t: continue
        I=X.Inst(n,[tuple(e) for e in ends],rot,[1]*len(ends),s,t)
        for f,g,cs,ct in D.all_choices(I):
            ctx=X.Ctx()
            R=X.Run(I,ctx,X.FirstCh(),f,g,cs,ct,dict(cap_b=1))
            # wrap check_incision to print
            orig=R.check_incision
            def wrap(A,Inc,Inc2,newinc,pcs,pof,pt,pcs2,pof2,pt2,nxt,orig=orig,R=R):
                global shown
                q=A['_q']
                if shown<4 and (q['x']>q['y'] if shown%2 else q['x']<q['y']):
                    shown+=1
                    print('--- map',m,mi,'ends',I.ends,'rot',I.rot,'s',s,'t',t,'f',f,'g',g,'cs',cs,'ct',ct)
                    print(' faces',{k:v for k,v in enumerate(I.faces)})
                    print(' P faces',R.Pf,'edges',R.Pe,'Pd',R.Pd)
                    print(' level1 pieces', [ (p,R.anc(pcs[p][0]),pcs[p]) for p in range(len(pcs))])
                    print(' range',A['j'],A['k'],'i',q['i'],'x',q['x'],'y',q['y'],'Qe',q['Qe'])
                    Ce=[a[0]>>1 for a,b in q['Qe']]+R.Pe[min(q['x'],q['y']):max(q['x'],q['y'])]
                    print(' C edges',Ce,'Lo vertices',sorted(R.bond(Ce)[0]))
                    for a,b in q['Qe']:
                        d=a[0]; print('  new edge dart delta',d,'tail',I.tail(d),'head',I.head(d))
                    print(' lo pairs',q['lo'],'hi pairs',q['hi'])
                    print(' next level pieces',[(p,pcs2[p]) for p in range(len(pcs2))])
                orig(A,Inc,Inc2,newinc,pcs,pof,pt,pcs2,pof2,pt2,nxt)
            R.check_incision=wrap
            R.go()
            if shown>=4: raise SystemExit
