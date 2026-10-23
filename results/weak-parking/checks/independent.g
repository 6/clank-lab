# Independently written from the mathematical reduction and certificate data.
# No search, producer, or primary-checker source is imported.
IndependentCheck := function()
local ensure,n,h,A,I,edges,e,simpleMatrices,i,j,k,r,roots,oldLength,m,s,
      rootIndex,simplePositions,decode,mat,permutation,W,c,positive,reflections,
      reflectionMatrices,t,wm,wp,ws,wcentral,a,b,NC,ncrank,ncmat,sortedNC,
      spaces,fixed,flatKeys,key,rank,child,idx,parents,orb,seen,l,rep,cur,
      P,K,pgens,ks,rows,row,kp,krep,ksizes,signatures,sig,witness,f,central,
      total,table,d,count,contribution,normal,offset,power,omega,eigen,
      closureTests,orbitIndex,classTests,space,trace,signature,allWsignature,canonical,startCpu;
ensure := function(ok,msg)
  if not ok then Print("INDEPENDENT FAIL: ",msg,"\n"); QUIT_GAP(1); fi;
end;
startCpu:=Runtime();
n:=D_rank; h:=D_h; I:=IdentityMat(n);
canonical:=function(rows)
  if Length(rows)=0 then return []; fi;
  return TriangulizedMat(BaseMat(rows));
end;
A:=2*I;
edges:=[[1,3],[3,4],[2,4]];
for i in [4..n-1] do Add(edges,[i,i+1]); od;
for e in edges do A[e[1]][e[2]]:=-1; A[e[2]][e[1]]:=-1; od;
simpleMatrices:=[];
for i in [1..n] do
  m:=StructuralCopy(I);
  for j in [1..n] do m[j][i]:=m[j][i]-A[j][i]; od;
  Add(simpleMatrices,m);
od;
roots:=Set(I);
repeat
  oldLength:=Length(roots);
  roots:=Union(roots,Concatenation(List(simpleMatrices,s->List(roots,r->r*s))));
until Length(roots)=oldLength;
ensure(Length(roots)=D_roots,"root count");
ensure(ForAll(roots,r->r*A*r=2),"root norm");
simplePositions:=List(I,r->Position(roots,r));
permutation:=function(matrix)
  local images;
  ensure(matrix*A*TransposedMat(matrix)=A,"matrix isometry");
  images:=List(roots,v->Position(roots,v*matrix));
  ensure(not fail in images and Length(Set(images))=Length(roots),"root permutation");
  return PermList(images);
end;
mat:=g->List(simplePositions,j->roots[j^g]);
decode:=images->permutation(List(images,j->roots[j]));
W:=Group(List(simpleMatrices,permutation));
ensure(Size(W)=D_group_order,"W order");
c:=Product(GeneratorsOfGroup(W));
ensure(Order(c)=h,"Coxeter order");
positive:=Filtered(roots,r->First(r,x->x<>0)>0);
reflectionMatrices:=List(positive,r->I-TransposedMat([A*r])*[r]);
reflections:=List(reflectionMatrices,permutation);
ensure(ForAll(reflections,t->t in W and Order(t)=2 and RankMat(I-mat(t))=1),"reflections");
Print("INDEPENDENT model E",n," GAP ",GAPInfo.Version,"\n");

# Use exact permutation cycle structure as a filter only; every potential
# collision is decided by the kernel's conjugacy test in the actual group.
signature:=g->Collected(CycleLengths(g,[1..Length(roots)]));
wm:=D_class_matrices; wp:=List(wm,permutation); ws:=D_class_sizes;
wcentral:=[]; allWsignature:=List(wp,signature);
for a in [1..Length(wp)] do
  ensure(wp[a] in W,"W representative membership");
  central:=Size(Centralizer(W,wp[a])); Add(wcentral,central);
  ensure(ws[a]*central=Size(W),"W class size");
  for b in [1..a-1] do
    if allWsignature[a]=allWsignature[b] then
      ensure(not IsConjugate(W,wp[a],wp[b]),"duplicate W conjugacy class");
    fi;
  od;
od;
ensure(Sum(ws)=Size(W),"W class cover");
Print("INDEPENDENT W class partition ",Length(wp),"\n");

NC:=[c]; parents:=C_parents;
for i in [2..Length(parents)] do
  ensure(1<=parents[i][1] and parents[i][1]<i and 1<=parents[i][2]
         and parents[i][2]<=Length(reflections),"parent reference");
  Add(NC,NC[parents[i][1]]*reflections[parents[i][2]]);
od;
sortedNC:=Set(NC);
ensure(Length(sortedNC)=Length(NC),"distinct NC elements");
ncmat:=List(NC,mat); ncrank:=List(ncmat,m->RankMat(I-m));
spaces:=[]; flatKeys:=[];
for i in [1..Length(NC)] do
  ensure(ncrank[i]+RankMat(I-mat(NC[i]^-1*c))=n,"NC membership");
  if i>1 then ensure(ncrank[i]=ncrank[parents[i][1]]-1,"descending parent"); fi;
  fixed:=NullspaceMat(I-ncmat[i]);
  ensure(Length(fixed)=n-ncrank[i] and ForAll(fixed,v->v*ncmat[i]=v),"fixed-space identity");
  key:=canonical(fixed); Add(spaces,fixed); Add(flatKeys,key);
od;
ensure(Length(Set(flatKeys))=Length(NC),"distinct fixed spaces");
closureTests:=0;
for i in [1..Length(NC)] do
  for j in [1..Length(reflections)] do
    rank:=RankMat(I-ncmat[i]*reflectionMatrices[j]);
    closureTests:=closureTests+1;
    if rank=ncrank[i]-1 then
      ensure(NC[i]*reflections[j] in sortedNC,"descending NC cover gap");
    fi;
  od;
od;
Print("INDEPENDENT NC closure ",Length(NC)," elements ",closureTests," tests\n");

seen:=[]; table:=List(wp,x->List([1..h],y->0)); classTests:=0;
for orbitIndex in [1..Length(C_orbits)] do
  orb:=C_orbits[orbitIndex]; rep:=orb[1]; l:=orb[2];
  ensure(1<=rep and rep<=Length(NC) and l>0 and h mod l=0,"orbit schema");
  cur:=NC[rep];
  for i in [1..l] do
    idx:=Position(sortedNC,cur);
    ensure(idx<>fail and not idx in seen,"orbit overlap or early period");
    Add(seen,idx); cur:=cur^c;
  od;
  ensure(cur=NC[rep],"orbit does not close");
  fixed:=spaces[rep];
  pgens:=Filtered(reflections,t->ForAll(fixed,v->v*mat(t)=v));
  P:=Group(Concatenation([One(W)],pgens));
  ensure(NC[rep] in P,"NC representative belongs to parabolic");
  ensure(ForAll(GeneratorsOfGroup(P),g->ForAll(fixed,v->v*mat(g)=v)),"P pointwise fixes X");
  # Reconstruct the common fixed space of P and compare to X itself.
  normal:=Concatenation(List(GeneratorsOfGroup(P),g->TransposedMat(I-mat(g))));
  space:=NullspaceMat(TransposedMat(normal));
  ensure(canonical(space)=canonical(fixed),"parabolic common fixed-space identity");
  power:=c^l;
  ensure(canonical(List(fixed,v->v*mat(power)))=canonical(fixed),"C power preserves flat");
  K:=Group(Concatenation(GeneratorsOfGroup(P),[power]));
  ensure(IsNormal(K,P),"P normal in K");
  rows:=C_subgroup_classes[orbitIndex]; kp:=[]; ksizes:=[]; signatures:=[];
  for row in rows do
    krep:=decode(row[1]); witness:=decode(row[4]); f:=row[3];
    ensure(krep in K and witness in W,"K representative or witness membership");
    ensure(krep^witness=wp[f],"fusion witness");
    central:=Size(Centralizer(K,krep));
    ensure(row[2]*central=Size(K),"K class size");
    sig:=signature(krep);
    for j in [1..Length(kp)] do
      if signatures[j]=sig then ensure(not IsConjugate(K,krep,kp[j]),"duplicate K class"); fi;
    od;
    Add(kp,krep); Add(ksizes,row[2]); Add(signatures,sig); classTests:=classTests+1;
    for d in [0..h-1] do
      if d mod l=0 and krep*c^-d in P then
        contribution:=l*wcentral[f]*row[2]/Size(P);
        table[f][d+1]:=table[f][d+1]+contribution;
      fi;
    od;
  od;
  ensure(Sum(ksizes)=Size(K),"K class partition cover");
  if orbitIndex mod 100=0 then Print("INDEPENDENT orbit progress ",orbitIndex,"/",Length(C_orbits),"\n"); fi;
od;
ensure(Length(seen)=Length(NC),"NC orbit cover");
ensure(table=D_character,"full combinatorial character table");
omega:=E(h);
for a in [1..Length(wp)] do
  for d in [0..h-1] do
    eigen:=n-RankMat(wm[a]-omega^d*I);
    ensure(table[a][d+1]=(h+1)^eigen,"cyclotomic eigenspace character");
  od;
od;
Print("INDEPENDENT class rows ",classTests," character entries ",Length(wp)*h,"\n");
Print("INDEPENDENT GAP CPU milliseconds ",Runtime()-startCpu,"\n");
Print("INDEPENDENT GAP E",n," PASS\n");
end;
IndependentCheck();
QUIT_GAP(0);
