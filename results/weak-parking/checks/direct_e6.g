# Independent E6 control: no rotation-orbit decomposition and no twisted-group
# class aggregation. Enumerate W, select NC by rank, and enumerate P cosets.
N:=6;; A:=2*IdentityMat(N);;
for e in [[1,3],[3,4],[2,4],[4,5],[5,6]] do
 A[e[1]][e[2]]:=-1; A[e[2]][e[1]]:=-1;
od;
I:=IdentityMat(N);; S:=[];;
for i in [1..N] do
 m:=StructuralCopy(I);
 for j in [1..N] do m[j][i]:=m[j][i]-A[j][i]; od;
 Add(S,m);
od;
roots:=Set(Concatenation(I,-I));;
repeat
 old:=Length(roots);
 for m in S do UniteSet(roots,Set(List(roots,v->v*m))); od;
until Length(roots)=old;
sg:=List(S,m->PermList(List(roots,v->Position(roots,v*m))));;
W:=Group(sg);; c:=Product(sg);; h:=Order(c);;
sp:=List(I,v->Position(roots,v));;
Mat:=g->List(sp,i->roots[i^g]);;
T0:=Runtime();; all:=Elements(W);; cl:=ConjugacyClasses(W);;
fixed:=[];;
reps:=List(cl,Representative);; cent:=List(cl,b->Size(W)/Size(b));;
classmap:=NewDictionary((),true);;
for k in [1..Length(cl)] do
 for v in Elements(cl[k]) do AddDictionary(classmap,v,k); od;
od;
# Independent definition-based cover; no descent algorithm.
nc:=Filtered(all,u->RankMat(Mat(u)-I)+RankMat(Mat(u^-1*c)-I)=N);;
if Length(nc)<>833 then Error("independent NC count"); fi;
chi:=List(cl,x->List([1..h],d->0));; cells:=0;;
for u in nc do
 fixed:=NullspaceMat(Mat(u)-I);
 # Enumerate the pointwise stabilizer directly from W, instead of generating
 # it by reflections below u. This is intentionally a hard neighboring unit.
 pe:=Filtered(all,g->ForAll(fixed,v->v*Mat(g)=v));
 for d in [0..h-1] do
  if u^(c^d)=u then
   for p in pe do
    k:=LookupDictionary(classmap,p*c^d);
    if k=fail then Error("independent class coverage"); fi;
    chi[k][d+1]:=chi[k][d+1]+cent[k]/Length(pe);
    cells:=cells+1;
   od;
  fi;
 od;
od;
expected:=List(reps,g->List([0..h-1],d->(h+1)^(N-RankMat(Mat(g)-E(h)^d*I))));;
if chi<>expected then Error("independent character mismatch"); fi;
stream:=OutputTextFile(OUT,false);; SetPrintFormattingStatus(stream,false);;
PrintTo(stream,"{\"rank\":6,\"method\":\"all-W rank filter and direct pointwise stabilizers\",",
 "\"nc_count\":",Length(nc),",\"w_classes\":",Length(cl),",\"explicit_coset_elements\":",cells,
 ",\"cpu_ms\":",Runtime()-T0,",\"class_matrices\":",List(reps,Mat),",\"character\":",chi,"}\n");
CloseStream(stream);;
Print("INDEPENDENT E6 PASS comparisons 300 cpu_ms ",Runtime()-T0,"\n");
QUIT;
