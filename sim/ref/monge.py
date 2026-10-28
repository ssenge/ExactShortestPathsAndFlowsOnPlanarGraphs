# Do (13) [d(i,k)+d(j,l) >= d(i,l)+d(j,k) for i<j<k<l] plus triangle imply
# (1) [d(x1,y2)+d(x2,y1) <= d(x1,y1)+d(x2,y2) for <x1,y2,y1,x2> = i<j<k<l] for LINEAR subsequences?
import itertools
try:
    from scipy.optimize import linprog
except ImportError:
    print("no scipy"); raise SystemExit
for n in (4,5):
    P=[(a,b) for a in range(n) for b in range(n) if a!=b]
    idx={p:i for i,p in enumerate(P)}
    A=[];b=[]
    def row(pos,neg,rhs=0.0):
        r=[0.0]*len(P)
        for p in pos: r[idx[p]]+=1
        for p in neg: r[idx[p]]-=1
        A.append(r); b.append(rhs)
    for a,c in P:
        for m in range(n):
            if m not in (a,c): row([(a,c)],[(a,m),(m,c)])  # d(a,c)-d(a,m)-d(m,c)<=0
    for i,j,k,l in itertools.combinations(range(n),4):
        row([(i,l),(j,k)],[(i,k),(j,l)])  # (13): d(i,l)+d(j,k)-d(i,k)-d(j,l)<=0
    for p in P: row([],[p],-1.0)  # d>=1
    for p in P: row([p],[],100.0)
    worst=0
    for i,j,k,l in itertools.combinations(range(n),4):
        # (1) with x1=i,y2=j,y1=k,x2=l: d(i,j)+d(l,k) - d(i,k) - d(l,j) <= 0 ; maximise LHS
        c=[0.0]*len(P)
        for p in [(i,j),(l,k)]: c[idx[p]]-=1
        for p in [(i,k),(l,j)]: c[idx[p]]+=1
        r=linprog(c,A_ub=A,b_ub=b,bounds=[(0,None)]*len(P),method="highs")
        worst=max(worst,-r.fun)
    print(n,"max violation of (1) under (13)+triangle:",worst)
