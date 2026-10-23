# Independent checker. Input records D and C; this file imports no search code.
# It never calls ConjugacyClasses: certified class lists are checked by exact
# centralizer sizes, disjointness, and a sum to the known/generated group order.
T0:=Runtime();; n:=D.rank;; a:=2*IdentityMat(n);; eye:=IdentityMat(n);;
for e in Concatenation([[1,3],[3,4],[2,4]],List([4..n-1],i->[i,i+1])) do
 a[e[1]][e[2]]:=-1; a[e[2]][e[1]]:=-1;
od;
simples:=[];;
for i in [1..n] do
 m:=List([1..n],j->eye[j]-a[j][i]*eye[i]); Add(simples,m);
od;
rr:=Set(Concatenation(eye,-eye));;
repeat
 old:=Length(rr);
 for m in simples do UniteSet(rr,Set(List(rr,v->v*m))); od;
until old=Length(rr);
PofM:=m->PermList(List(rr,v->Position(rr,v*m)));;
gens:=List(simples,PofM);; group:=Group(gens);; cox:=Product(gens);; h:=Order(cox);;
sp:=List(eye,r->Position(rr,r));;
MofP:=g->List(sp,j->rr[j^g]);;
Decode:=function(v)
 if Length(v)<>n or not ForAll(v,i->IsInt(i) and i in [1..Length(rr)]) then
  Error("invalid simple-root image certificate");
 fi;
 return PofM(List(v,i->rr[i]));
end;;
if Size(group)<>D.group_order or Length(rr)<>D.roots or h<>D.h then Error("group model"); fi;
constants:=[[51840,72,12],[2903040,126,18],[696729600,240,30]][n-5];;
if [Size(group),Length(rr),h]<>constants then Error("external E constants"); fi;
wreps:=List(D.class_matrices,PofM);;
if not ForAll(wreps,g->g in group) then Error("W representative membership"); fi;
if Sum(D.class_sizes)<>Size(group) then Error("W class size sum"); fi;
for j in [1..Length(wreps)] do
 if D.class_sizes[j]<>Size(group)/Size(Centralizer(group,wreps[j])) then Error("W class size"); fi;
 for k in [1..j-1] do
  if CycleStructurePerm(wreps[j])=CycleStructurePerm(wreps[k]) and
     IsConjugate(group,wreps[j],wreps[k]) then Error("duplicate W class"); fi;
 od;
od;
positive:=Filtered(rr,r->First(r,x->x<>0)>0);;
tt:=List(positive,r->PofM(List([1..n],j->eye[j]-(a[j]*r)*r)));;
if C.parents[1]<>[0,0] then Error("cover top"); fi;
nc:=[cox];; present:=NewDictionary(cox,true);; AddDictionary(present,cox,true);;
for i in [2..Length(C.parents)] do
 edge:=C.parents[i];
 if not edge[1] in [1..i-1] or not edge[2] in [1..Length(tt)] then Error("cover edge"); fi;
 g:=nc[edge[1]]*tt[edge[2]];
 if LookupDictionary(present,g)<>fail then Error("duplicate cover element"); fi;
 Add(nc,g); AddDictionary(present,g,true);
od;
if Length(nc)<>D.nc_count then Error("cover count"); fi;
closure_tests:=0;;
for g in nc do
 rank:=RankMat(MofP(g)-eye);
 if rank+RankMat(MofP(g^-1*cox)-eye)<>n then Error("element outside NC"); fi;
 # Exhaustive cover check, distinct from the search's fixed-space predicate.
 for t in tt do
  v:=g*t; closure_tests:=closure_tests+1;
  if RankMat(MofP(v)-eye)=rank-1 and LookupDictionary(present,v)=fail then
   Error("missing downward cover");
  fi;
 od;
od;
spacekeys:=List(nc,g->RREF(NullspaceMat(MofP(g)-eye)));;
if Length(Set(spacekeys))<>Length(nc) then Error("NC fixed-space injection"); fi;
covered:=NewDictionary(cox,true);; actual:=List(wreps,g->List([1..h],d->0));;
fixed:=[];; l:=1;; par:=Group(());;
if Length(C.orbits)<>Length(C.subgroup_classes) then Error("orbit units"); fi;
if Sum(List(C.orbits,o->o[2]))<>Length(nc) then Error("orbit length sum"); fi;
for oi in [1..Length(C.orbits)] do
 if not C.orbits[oi][1] in [1..Length(nc)] or
    not C.orbits[oi][2] in DivisorsInt(h) then Error("orbit metadata"); fi;
 u:=nc[C.orbits[oi][1]]; l:=C.orbits[oi][2]; v:=u;
 for i in [1..l] do
  if LookupDictionary(present,v)=fail then Error("orbit outside NC"); fi;
  if LookupDictionary(covered,v)<>fail then Error("orbit overlap/length"); fi;
  AddDictionary(covered,v,true); v:=v^cox;
 od;
 if v<>u then Error("orbit not closed"); fi;
 fixed:=NullspaceMat(MofP(u)-eye);
 pgens:=Filtered(tt,t->ForAll(fixed,v->v*MofP(t)=v));
 par:=Group(Concatenation([()],pgens)); big:=Group(Concatenation(pgens,[cox^l]));
 if not u in par then Error("NC element not in pointwise stabilizer"); fi;
 # Check the common row fixed space, including the empty generating set.
 equations:=Concatenation(List(pgens,t->TransposedMat(MofP(t)-eye)));
 if Length(equations)=0 then common:=eye;
 else common:=NullspaceMat(TransposedMat(equations)); fi;
 if RREF(common)<>RREF(fixed) then Error("parabolic fixed space convention"); fi;
 if not ForAll(pgens,t->t^(cox^l) in par) then Error("not normal"); fi;
 kr:=[]; ks:=[]; kf:=[];
 for row in C.subgroup_classes[oi] do
  v:=Decode(row[1]); sz:=row[2]; f:=row[3];
  if not v in big or not f in [1..Length(wreps)] then Error("K representative"); fi;
  if sz<>Size(big)/Size(Centralizer(big,v)) then Error("K class size"); fi;
  if Length(row)<>4 then Error("missing fusion witness"); fi;
  witness:=Decode(row[4]);
  if not witness in group or v^witness<>wreps[f] then Error("K to W fusion witness"); fi;
  for j in [1..Length(kr)] do
   if ks[j]=sz and kf[j]=f and IsConjugate(big,kr[j],v) then Error("duplicate K class"); fi;
  od;
  Add(kr,v); Add(ks,sz); Add(kf,f);
  for d in [0..h-1] do
   if d mod l=0 and v*cox^(-d) in par then
    actual[f][d+1]:=actual[f][d+1]+l*(Size(group)/D.class_sizes[f])*sz/Size(par);
   fi;
  od;
 od;
 if Sum(ks)<>Size(big) then Error("K class cover"); fi;
od;
if not ForAll(nc,g->LookupDictionary(covered,g)<>fail) then Error("uncovered C orbit"); fi;
if actual<>D.character then Error("certificate character mismatch"); fi;
 if not ForAll(Concatenation(actual),x->IsInt(x) and x>=0) then Error("character integrality"); fi;
for j in [1..Length(wreps)] do for d in [0..h-1] do
 value:=(h+1)^(n-RankMat(D.class_matrices[j]-E(h)^d*eye));
 if actual[j][d+1]<>value then Error("eigenvalue mismatch"); fi;
od; od;
Print("CERTIFICATE PASS E",n," comparisons ",h*Length(wreps)," cover_tests ",closure_tests," fixed_spaces ",Length(Set(spacekeys))," fusion_witnesses ",Sum(List(C.subgroup_classes,Length))," orbit_subset_and_sum PASS cpu_ms ",Runtime()-T0,"\n");
QUIT;
