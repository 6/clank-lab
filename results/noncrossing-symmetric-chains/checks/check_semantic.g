# Independent semantic checker. Reads data only. Traversal-free: reconstructs
# each element from its exact basis images, checks the whole reflection set by
# conjugacy classes, and exhausts all downward pairs with independent row rank.
Require:=function(ok,msg) if not ok then Print("REJECT ",msg,"\n");QUIT_GAP(1);fi;end;;
ExactRank:=function(a)
 local b,h,j,k,p,z;
 b:=List(a,ShallowCopy);h:=0;
 for j in [1..Length(b[1])] do
  p:=First([h+1..Length(b)],k->b[k][j]<>0);
  if p<>fail then
   h:=h+1;z:=b[h];b[h]:=b[p];b[p]:=z;b[h]:=b[h]/b[h][j];
   for k in [h+1..Length(b)] do b[k]:=b[k]-b[k][j]*b[h];od;
  fi;
  if h=Length(b) then break;fi;
 od;
 return h;
end;;
Check:=function(kind,out)
 local start,m,I,B,invB,decode,elts,mats,ranks,dict,k,j,v,q,idx,
      classes,reflectionClasses,total,cl,t,ev,x,edges,down,up,order,s,
      missingVertex,missingEdge,regular,genmats,ccms,tests;
 start:=Runtime();m:=Model(kind);I:=IdentityMat(Length(m.sp));
 Require(CERT_HEIGHT=m.rank and CERT_GROUP=kind,"declared group/rank");
 B:=m.roots{m.sp};invB:=B^-1;
 Require(RankMat(B)=Length(m.sp),"faithful spanning root basis");
 genmats:=List(m.gens,m.mat);
 Require(ExactRank(Concatenation(List(genmats,a->TransposedMat(a-I))))=m.rank,
         "essential rank from the common fixed space");
 Require(ForAll([1..Length(m.gens)],k->ForAll([1..Length(m.roots)],j->
     m.roots[j]*genmats[k]=m.roots[j^m.gens[k]])),"generator matrix action");
 Require(Length(Set(m.ref))=Length(m.ref),"reflection uniqueness");
 Require(ForAll(m.ref,t->t in m.W and Order(t)=2 and ExactRank(m.mat(t)-I)=1),"reflections");
 # Every group element is conjugate to one of these representatives, and
 # rank(I-g) is conjugacy invariant. This does not infer completeness from
 # one orbit, a model's roots, or a published reflection count.
 classes:=ConjugacyClasses(m.W);
 Require(Sum(classes,Size)=Size(m.W),"class census size");
 reflectionClasses:=Filtered(classes,cl->ExactRank(m.mat(Representative(cl))-I)=1);
 total:=0;
 for cl in reflectionClasses do
  Require(Number(m.ref,t->t in cl)=Size(cl),"entire reflection class present");
  total:=total+Size(cl);
 od;
 Require(total=Length(m.ref),"all and only reflection classes");ccms:=Runtime()-start;
 Require(Length(m.coxeter_word)=m.rank and ForAll(m.gens,t->t in m.ref),"Coxeter reflection word");
 Require(Product(m.gens{m.coxeter_word})=m.c and ExactRank(m.mat(m.c)-I)=m.rank,"Coxeter length witness");
 Require(Order(m.c)=m.h,"Coxeter order");
 ev:=NullspaceMat(m.mat(m.c)-E(m.h)*I);
 regular:=First(ev,x->ForAll(m.ref,t->x*m.mat(t)<>x));
 Require(regular<>fail,"primitive regular eigenvector");
 decode:=function(label)
  local a,images;
  Require(Length(label)=Length(m.sp) and ForAll(label,i->IsInt(i) and i>=1 and i<=Length(m.roots)),"label bounds");
  a:=invB*m.roots{label};images:=List(m.roots,r->PositionSorted(m.roots,r*a));
  Require(ForAll([1..Length(images)],j->images[j]<=Length(m.roots) and m.roots[images[j]]=m.roots[j]*a),"root action closure");
  return PermList(images);
 end;
 elts:=List(CERT_LABELS,decode);mats:=List(elts,m.mat);
 ranks:=List(mats,a->ExactRank(a-I));
 Require(ranks=CERT_RANKS,"ranks");
 Require(Length(Set(elts))=Length(elts),"distinct elements");
 Require(ForAll(elts,x->x in m.W),"element membership");
 Require(m.c in elts and One(m.W) in elts,"interval endpoints");
 dict:=NewDictionary(m.c,true);for k in [1..Length(elts)] do AddDictionary(dict,elts[k],k);od;
 edges:=[];tests:=0;
 for k in [1..Length(elts)] do
  for j in [1..Length(m.ref)] do
   tests:=tests+1;q:=ExactRank(mats[k]*m.refmat[j]-I);
   if q=ranks[k]-1 then
    idx:=LookupDictionary(dict,elts[k]*m.ref[j]);
    Require(idx<>fail,"descending closure gap");Add(edges,[idx,k]);
   fi;
  od;
 od;
 Require(Length(Set(CERT_EDGES))=Length(CERT_EDGES) and Set(edges)=Set(CERT_EDGES),"exact complete cover graph");
 # Paths in both directions, not just codimension equality, prove membership
 # in [1,c]. Strict ranks make these dynamic checks non-circular.
 down:=List(elts,x->false);up:=List(elts,x->false);
 down[Position(elts,One(m.W))]:=true;up[Position(elts,m.c)]:=true;
 for q in [1..m.rank] do for v in edges do if ranks[v[2]]=q and down[v[1]] then down[v[2]]:=true;fi;od;od;
 for q in Reversed([0..m.rank-1]) do for v in edges do if ranks[v[1]]=q and up[v[2]] then up[v[1]]:=true;fi;od;od;
 Require(ForAll(down,x->x) and ForAll(up,x->x),"two-sided length-n paths");
 s:=OutputTextFile(out,false);SetPrintFormattingStatus(s,false);
 PrintTo(s,"{\"accepted\":true,\"group\":\"",kind,"\",\"vertices\":",Length(elts),
  ",\"edges\":",Length(edges),",\"classes\":",Length(classes),
  ",\"reflection_classes\":",Length(reflectionClasses),",\"reflections\":",Length(m.ref),
  ",\"closure_tests\":",tests,",\"class_model_cpu_ms\":",ccms,
  ",\"cpu_ms\":",Runtime()-start,"}\n");CloseStream(s);
 Print("SEMANTIC ACCEPT ",kind," cpu_ms=",Runtime()-start,"\n");
end;;
Check(SCD_TYPE,SCD_OUT);;QUIT_GAP(0);
