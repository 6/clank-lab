# Exact models reconstructed from the mathematical root data. They do not read
# any selection program. Permutations act on sorted roots; a label records
# the images of a spanning ordered basis, hence determines an element exactly.
RootAction:=function(roots,a)
 local images;
 images:=List(roots,x->Position(roots,x*a));
 if fail in images or Length(Set(images))<>Length(roots) then Error("not a root permutation");fi;
 return PermList(images);
end;;

RealModel:=function(kind)
 local n,gram,links,e,generators,i,column,roots,previous,acts,W,basis,
      matrix,reflections,r,a,c,degree,expected;
 if kind="H4" then
  n:=4;degree:=30;expected:=14400;gram:=2*IdentityMat(n);
  gram[1][2]:=-1-E(5)-E(5)^4;gram[2][1]:=gram[1][2];links:=[[2,3],[3,4]];
 else
  n:=Int(kind{[2..Length(kind)]});
  if not n in [6,7,8] then Error("unknown real type");fi;
  degree:=[12,18,30][n-5];expected:=[51840,2903040,696729600][n-5];
  gram:=2*IdentityMat(n);links:=[[1,3],[2,4],[3,4]];
  Append(links,List([4..n-1],i->[i,i+1]));
 fi;
 for e in links do gram[e[1]][e[2]]:=-1;gram[e[2]][e[1]]:=-1;od;
 generators:=[];
 for i in [1..n] do
  column:=List([1..n],j->[gram[j][i]]);
  Add(generators,IdentityMat(n)-column*[IdentityMat(n)[i]]);
 od;
 roots:=Set(IdentityMat(n));
 repeat
  previous:=Length(roots);
  roots:=Union(roots,Concatenation(List(generators,a->List(roots,r->r*a))));
 until Length(roots)=previous;
 if not ForAll(roots,r->r*gram*r=2) then Error("real root norms");fi;
 acts:=List(generators,a->RootAction(roots,a));W:=Group(acts);
 if Size(W)<>expected then Error("real group identification order");fi;
 basis:=List(IdentityMat(n),r->Position(roots,r));
 matrix:=g->List(basis,i->roots[i^g]);
 reflections:=Set(List(roots,r->RootAction(roots,IdentityMat(n)-List(gram*r,x->[x])*[r])));
 c:=Product(acts);
 return rec(W:=W,c:=c,h:=degree,rank:=n,roots:=roots,sp:=basis,mat:=matrix,
   ref:=reflections,refmat:=List(reflections,matrix),gens:=acts,coxeter_word:=[1..n]);
end;;

ComplexModel:=function(kind)
 local z,theta,roots,pair,a,b,s,v,tuple,phases,projective,lines,
      reflection,allrefs,normal,named,generators,W,basisVectors,basis,
      inverseBasis,matrix,refs,c,word,eigen,n,h,expected;
 z:=E(3);theta:=1+2*z;roots:=[];
 # Oura--Sekiguchi: 270 vectors supported on two coordinates, and 486
 # vectors of six cube-root coordinates whose exponent sum is zero mod 3.
 for pair in Combinations([1..6],2) do
  for a in [0..2] do for b in [0..2] do for s in [-1,1] do
   v:=List([1..6],i->0);v[pair[1]]:=s*theta*z^a;v[pair[2]]:=-s*theta*z^b;Add(roots,v);
  od;od;od;
 od;
 for tuple in Tuples([0..2],6) do
  if Sum(tuple) mod 3=0 then
   v:=List(tuple,a->z^a);Add(roots,v);Add(roots,-v);
  fi;
 od;
 roots:=Set(roots);if Length(roots)<>756 then Error("complex root count");fi;
 phases:=[1,z,z^2,-1,-z,-z^2];
 projective:=v->Minimum(List(phases,s->s*v));lines:=Set(List(roots,projective));
 if Length(lines)<>126 then Error("complex line count");fi;
 reflection:=v->IdentityMat(6)-List(ComplexConjugate(v),x->[x])*[v]/3;
 allrefs:=List(lines,v->RootAction(roots,reflection(v)));
 normal:=function(i,j,a)
  local x;x:=List([1..6],k->0);x[i]:=theta;x[j]:=-theta*z^a;return projective(x);
 end;
 # These are exactly P1,P2,P3,Q1,R1,R2 of the source, in that order.
 named:=[normal(2,3,0),normal(3,4,0),normal(4,5,0),normal(1,2,0),normal(1,2,2),projective([1,1,1,1,1,1])];
 generators:=List(named,v->allrefs[Position(lines,v)]);
 if kind=33 then generators:=generators{[1,2,4,5,6]};n:=5;h:=18;expected:=51840;
 elif kind=34 then n:=6;h:=42;expected:=39191040;else Error("complex type");fi;
 W:=Group(generators);if Size(W)<>expected then Error("complex group order");fi;
 basisVectors:=List([1..5],i->theta*(IdentityMat(6)[i]-IdentityMat(6)[6]));
 Add(basisVectors,[1,1,1,1,1,1]);basis:=List(basisVectors,v->Position(roots,v));
 inverseBasis:=basisVectors^-1;matrix:=g->inverseBasis*List(basis,i->roots[i^g]);
 refs:=Filtered(allrefs,t->t in W);c:=fail;
 for word in PermutationsList([1..n]) do
  v:=Product(generators{word});
  if Order(v)=h and RankMat(matrix(v)-IdentityMat(6))=n then
   eigen:=NullspaceMat(matrix(v)-E(h)*IdentityMat(6));
   if ForAny(eigen,x->ForAll(refs,t->x*matrix(t)<>x)) then c:=v;break;fi;
  fi;
 od;
 if c=fail then Error("regular Coxeter element absent");fi;
 return rec(W:=W,c:=c,h:=h,rank:=n,roots:=roots,sp:=basis,mat:=matrix,
   ref:=refs,refmat:=List(refs,matrix),gens:=generators,coxeter_word:=word);
end;;
Model:=function(kind)
 if kind="G33" then return ComplexModel(33);elif kind="G34" then return ComplexModel(34);else return RealModel(kind);fi;
end;;
