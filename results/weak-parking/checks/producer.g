# GAP computation, invoked by replay.py; no precomputed character answers.
if not IsBound(N) then N:=6; fi;
if not IsBound(OUT) then OUT:="result.json"; fi;
T0:=Runtime();;
A:=2*IdentityMat(N);;
edges:=[[1,3],[3,4],[2,4]];;
Append(edges,List([4..N-1],i->[i,i+1]));;
for e in edges do A[e[1]][e[2]]:=-1; A[e[2]][e[1]]:=-1; od;
I:=IdentityMat(N);;
sm:=[];;
for i in [1..N] do
 m:=StructuralCopy(I);
 for j in [1..N] do m[j][i]:=m[j][i]-A[j][i]; od;
 Add(sm,m);
od;
roots:=ShallowCopy(I);; at:=1;;
while at<=Length(roots) do
 r:=roots[at];
 for m in sm do s:=r*m; if not s in roots then Add(roots,s); fi; od;
 at:=at+1;
od;
Sort(roots);;
sp:=List(I,v->Position(roots,v));;
ToPerm:=m->PermList(List(roots,r->PositionSorted(roots,r*m)));;
sg:=List(sm,ToPerm);; W:=Group(sg);; c:=Product(sg);; h:=Order(c);;
Mat:=g->List(sp,i->roots[i^g]);;
pos:=Filtered(roots,r->First(r,x->x<>0)>0);;
ref:=[];;
for r in pos do
 m:=List([1..N],j->I[j]-(A[j]*r)*r);
 Add(ref,ToPerm(m));
od;
Below:=function(g)
 local fixed;
 fixed:=NullspaceMat(Mat(g)-I);
 return Filtered([1..Length(ref)],j->ForAll(fixed,v->(pos[j]*A)*v=0));
end;;
# Each downward edge g -> g*t has absolute rank one smaller.
nc:=[c];; parents:=[[0,0]];; seen:=NewDictionary(c,true);; AddDictionary(seen,c,true);; at:=1;;
while at<=Length(nc) do
 u:=nc[at];
 for j in Below(u) do
  v:=u*ref[j];
  if LookupDictionary(seen,v)=fail then
   AddDictionary(seen,v,true); Add(nc,v); Add(parents,[at,j]);
  fi;
 od;
 at:=at+1;
od;
ncms:=Runtime()-T0;;
Print("NC ",N," ",Length(nc)," ms ",ncms,"\n");
cl:=ConjugacyClasses(W);; reps:=List(cl,Representative);; sizes:=List(cl,Size);;
if Sum(sizes)<>Size(W) then Error("incomplete W classes"); fi;
cent:=List(sizes,s->Size(W)/s);;
sigs:=List(reps,CycleStructurePerm);;
cache:=NewDictionary((),true);;
for j in [1..Length(reps)] do AddDictionary(cache,reps[j],[j,()]); od;
fusioncalls:=0;; ambiguous:=0;;
Fuse:=function(g)
 local a, cand, k, witness;
 a:=LookupDictionary(cache,g);
 if a<>fail then return a; fi;
 cand:=Filtered([1..Length(cl)],k->CycleStructurePerm(g)=sigs[k]);
 if Length(cand)>1 then ambiguous:=ambiguous+1; fi;
 for k in cand do
  fusioncalls:=fusioncalls+1;
  witness:=RepresentativeAction(W,g,reps[k]);
  if witness<>fail then
   if g^witness<>reps[k] then Error("invalid fusion witness"); fi;
   AddDictionary(cache,g,[k,witness]); return [k,witness];
  fi;
 od;
 Error("unresolved class fusion");
end;;
chi:=List([1..Length(cl)],j->List([1..h],d->0));;
used:=NewDictionary(c,true);; orbits:=[];; units:=[];; orbitdata:=[];; certunits:=[];;
for u in nc do
 if LookupDictionary(used,u)=fail then
  l:=1; v:=u^c; AddDictionary(used,u,true);
  while v<>u do AddDictionary(used,v,true); l:=l+1; v:=v^c; od;
  Add(orbits,[u,l]);
  Add(orbitdata,[Position(nc,u),l]);
 fi;
od;
Print("ORBITS ",Length(orbits)," WCLASSES ",Length(cl),"\n");
for oi in [1..Length(orbits)] do
 u:=orbits[oi][1]; l:=orbits[oi][2]; start:=Runtime();
 pgens:=List(Below(u),j->ref[j]); P:=Group(Concatenation([()],pgens));
 if not ForAll(pgens,g->g^(c^l) in P) then Error("normalizer failure"); fi;
 K:=Group(Concatenation(pgens,[c^l]));
 kc:=ConjugacyClasses(K);
 if Sum(List(kc,Size))<>Size(K) then Error("incomplete K classes"); fi;
 certclasses:=[];
 for b in kc do
  v:=Representative(b); fusion:=Fuse(v); k:=fusion[1];
  Add(certclasses,[List(sp,i->i^v),Size(b),k,List(sp,i->i^fusion[2])]);
  for d in [0..h-1] do
   if d mod l=0 and v*c^(-d) in P then
    chi[k][d+1]:=chi[k][d+1]+l*cent[k]*Size(b)/Size(P);
   fi;
  od;
 od;
 Add(units,[oi,l,Size(P),Size(K),Length(kc),Runtime()-start]);
 Add(certunits,certclasses);
 if oi mod 10=0 then Print("UNIT ",oi,"/",Length(orbits)," ms ",Runtime()-T0,"\n"); fi;
od;
actualms:=Runtime()-T0;;
expected:=List(reps,g->List([0..h-1],d->(h+1)^(N-RankMat(Mat(g)-E(h)^d*I))));;
mismatches:=[];;
for j in [1..Length(cl)] do for d in [1..h] do
 if chi[j][d]<>expected[j][d] then Add(mismatches,[j,d-1,chi[j][d],expected[j][d]]); fi;
od; od;
if not ForAll(Concatenation(chi),x->IsInt(x) and x>=0) then Error("nonintegral character"); fi;
stream:=OutputTextFile(OUT,false);; SetPrintFormattingStatus(stream,false);;
PrintTo(stream,"{\"rank\":",N,",\"h\":",h,",\"group_order\":",Size(W),
 ",\"roots\":",Length(roots),",\"nc_count\":",Length(nc),",\"orbits\":",Length(orbits),
 ",\"w_classes\":",Length(cl),",\"nc_cpu_ms\":",ncms,",\"mechanism_cpu_ms\":",actualms,
 ",\"total_cpu_ms\":",Runtime()-T0,",\"fusion_calls\":",fusioncalls,",\"ambiguous_fusions\":",ambiguous,
 ",\"units\":",units,",\"class_sizes\":",sizes,",\"class_orders\":",List(reps,Order),
 ",\"class_matrices\":",List(reps,Mat),",\"character\":",chi,",\"expected\":",expected,
 ",\"mismatches\":",mismatches,"}\n");
CloseStream(stream);;
stream:=OutputTextFile(Concatenation(OUT,".certificate.json"),false);;
SetPrintFormattingStatus(stream,false);;
PrintTo(stream,"{\"rank\":",N,",\"parents\":",parents,",\"orbits\":",orbitdata,
 ",\"subgroup_classes\":",certunits,"}\n");
CloseStream(stream);;
Print("RESULT rank ",N," comparisons ",Length(cl)*h," mismatches ",Length(mismatches)," cpu_ms ",Runtime()-T0,"\n");
QUIT;
