# New rank-descent enumeration. No selection traversal, parent table or cover
# graph is read. Every decision is an exact rank of a reflection product.
Generate:=function(kind,out)
 local m,I,vertices,ranks,edges,dict,at,u,j,v,q,k,s,start;
 start:=Runtime();m:=Model(kind); I:=IdentityMat(Length(m.sp));
 vertices:=[m.c];ranks:=[m.rank];edges:=[];
 dict:=NewDictionary(m.c,true);AddDictionary(dict,m.c,1);at:=1;
 while at<=Length(vertices) do
  u:=vertices[at];
  for j in [1..Length(m.ref)] do
   v:=u*m.ref[j]; q:=RankMat(m.mat(v)-I);
   if q=ranks[at]-1 then
    k:=LookupDictionary(dict,v);
    if k=fail then Add(vertices,v);Add(ranks,q);k:=Length(vertices);AddDictionary(dict,v,k);fi;
    Add(edges,[k,at]);
   fi;
  od;
  at:=at+1;
 od;
 s:=OutputTextFile(out,false);SetPrintFormattingStatus(s,false);
 PrintTo(s,"{\"group\":\"",kind,"\",\"rank\":",m.rank,
  ",\"labels\":",List(vertices,g->List(m.sp,i->i^g)),
  ",\"ranks\":",ranks,",\"edges\":",edges,
  ",\"generation_cpu_ms\":",Runtime()-start,"}\n");CloseStream(s);
 Print("GENERATED ",kind," vertices=",Length(vertices)," edges=",Length(edges)," cpu_ms=",Runtime()-start,"\n");
end;;
Generate(SCD_TYPE,SCD_OUT);;
QUIT_GAP(0);
