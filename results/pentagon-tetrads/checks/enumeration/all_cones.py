"""For every one of the 116 closure cases, rederive from the case's map,
placement and labels: the angle equalities have rank 3, the stored angle
formulas solve them, and the stored length-cone rays generate exactly the
projected length cone (computed with the verifier's rational cone routine).
For case 8, the class closed by an identity, check that its angles, reflex
pattern and ray are the ones the identity uses."""
import json, sys, time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/"checks/enumeration"))
sys.path.insert(0,str(ROOT/"checks/verifier"))
from lengths import MapData,build_problem
from lcone import length_matrix
from verifier import cone_rays,incone
import sympy as S
A=S.symbols("a0:5")
t=time.monotonic()
ms=[MapData(json.loads(x)) for x in (ROOT/"data/maps-h0.jsonl").read_text().splitlines()]
ss=[json.loads(x) for x in (ROOT/"data/angle-survivors-n5.jsonl").read_text().splitlines()]
ident=lambda r:(r["map"],r["placement"],json.dumps(r["labs"]),json.dumps(r["pattern"]))
surv={ident(r):r for r in ss}
cs=json.loads((ROOT/"data/closure-cases-n5.json").read_text())
for i,c in enumerate(cs):
 r=surv[ident(c)]
 _,_,_,segs,lrows,arows=build_problem(ms[r["map"]],r,5)
 eq=[sum(A)-540]+[sum(a*b for a,b in zip(A,coef))+const-360 for kind,coef,const in arows if kind=="E"]
 M,b=S.linear_eq_to_matrix(eq,A)
 assert M.rank()==M.row_join(b).rank()==3,(i,"angle dimension")
 syms={str(a):a for a in A}
 vals={a:(a if str(a) in c["free"] else S.sympify(c["sol"][str(a)],locals=syms)) for a in A}
 assert all(S.expand(e.subs(vals,simultaneous=True))==0 for e in eq),(i,"angle formula")
 if i==8:
  p,q=A[3],A[4]
  assert c["free"]==["a3","a4"] and c["pattern"]==[False,True,False,False,False]
  assert [vals[a] for a in A]==[180-p-q,180+q,180-q,p,q]
  assert c["rays"]==[[1,2,1,2,1]]
  print("PASS case 8 identity bridge: actual angle equations, free variables, pattern and ray",flush=True)
 rr,k,full=cone_rays(length_matrix(5,len(segs),lrows))
 assert all(incone(v,c["rays"]) for v in rr), (i,"missing ray")
 assert all(incone(v,rr) for v in c["rays"]), (i,"extra ray")
 print("PASS case",i,"nullity",k,"projected rays",len(rr),flush=True)
print("PASS exact angle families and cones for all",len(cs),"cases; seconds",time.monotonic()-t)
