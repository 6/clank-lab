// Standalone b1 semantic checker: all 720 injections, exact GMP arithmetic.
// No generator, multiplication table, optimizer, or search imports.
#include <algorithm>
#include <array>
#include <cassert>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <map>
#include <numeric>
#include <set>
#include <string>
#include <vector>
#include <gmpxx.h>
#include <omp.h>
using namespace std;
using Z=mpz_class;
vector<array<int,3>> triples[7];int ti[6][6][6];vector<array<int,6>> perms;
struct Basis {int n,k,type,d;vector<int> flags,ix;vector<Z> Q;};
int encoded(int e,int c,const vector<int>& p){
  int n=p.size(),v=0;for(int j=0;j<n;j++)v|=((c>>p[j])&1)<<j;
  for(int j=0;j<(int)triples[n].size();j++){auto t=triples[n][j];v|=((e>>ti[p[t[0]]][p[t[1]]][p[t[2]]])&1)<<(n+j);}return v;
}
int flag(int e,int c,vector<int> root,vector<int> free){
  sort(free.begin(),free.end());int best=INT32_MAX;
  do{auto p=root;p.insert(p.end(),free.begin(),free.end());best=min(best,encoded(e,c,p));}while(next_permutation(free.begin(),free.end()));return best;
}
Basis read(istream& in,bool matrix){
  Basis b;in>>b.n>>b.k>>b.type>>b.d;assert(in&&b.d>0&&b.d<1000);
  b.ix.assign(1<<(b.n+triples[b.n].size()),-1);b.flags.resize(b.d);
  for(int i=0;i<b.d;i++){in>>b.flags[i];assert(b.flags[i]>=0&&b.flags[i]<(int)b.ix.size()&&b.ix[b.flags[i]]<0);b.ix[b.flags[i]]=i;}
  if(matrix){b.Q.resize(b.d*b.d);for(auto& q:b.Q)in>>q;}
  assert(in);return b;
}
int main(int argc,char**argv){
  assert(argc==2||(argc==3&&string(argv[2])=="--plant-cover-gap"));auto start=chrono::steady_clock::now();
  for(int n=0;n<=6;n++)for(int a=0;a<n;a++)for(int b=a+1;b<n;b++)for(int c=b+1;c<n;c++)triples[n].push_back({a,b,c});
  for(int j=0;j<20;j++){auto t=triples[6][j];do{ti[t[0]][t[1]][t[2]]=j;}while(next_permutation(t.begin(),t.end()));}
  array<int,6> p{0,1,2,3,4,5};do{perms.push_back(p);}while(next_permutation(p.begin(),p.end()));
  ifstream in(argv[1]);Z S;long D,bn,bd;int cn,cd,nb,nh,has_slacks;in>>S>>D>>cn>>cd>>nb>>nh>>bn>>bd>>has_slacks;assert(has_slacks==0||has_slacks==1);
  const long U=720000000000L;assert(S>0&&D>0&&U%D==0&&nb==38&&nh==40547);
  assert((cn==1&&cd==1)||(cn==3999&&cd==4000));assert(D%(20L*cd)==0&&bn>=0&&bd>0&&U%bd==0);
  vector<Basis> blocks;map<pair<int,int>,int> bid;
  for(int j=0;j<nb;j++){blocks.push_back(read(in,true));auto& b=blocks.back();assert((b.n==4&&b.k==2)||(b.n==5&&b.k==4));
    assert(bid.emplace(make_pair(b.k,b.type),j).second);for(auto& q:b.Q)q*=U/720;}
  vector<Basis> local;local.push_back(read(in,false));local.push_back(read(in,false));Basis global=read(in,false);
  assert(local[0].n==4&&local[0].k==1&&local[0].type==0&&local[1].n==4&&local[1].k==1&&local[1].type==1);
  assert(global.n==3&&global.k==0&&global.d==8);
  int nl=local[0].d+local[1].d;assert(nl==80);vector<Z> y(12847),eq(120);
  for(auto& v:y){in>>v;assert(v>=0);}for(auto& v:eq)in>>v;
  vector<Z> yl(80),yc(8),yd(9);for(int j=0;j<80;j++)yl[j]=y[j]*(U/720);
  for(int j=0;j<8;j++)yc[j]=y[80+j]*(U/(720*5));for(int j=0;j<9;j++)yd[j]=y[88+j];for(auto& v:eq)v*=U/720;
  // Direct predicate-superset sums; no zeta transform or stored CL table.
  vector<Z> cl(2*8*4*256);
  auto clindex=[](int tau,int rc,int used,int mask){return (((tau*8+rc)*4+used)*256+mask);};
  for(int tau=0;tau<2;tau++)for(int rc=0;rc<8;rc++)for(int used=1;used<4;used++)for(int mask=1;mask<256;mask++){
    Z v=0;for(int pi=1;pi<256;pi++)if((pi&mask)==mask){v+=y[97+tau*255+pi-1];
      for(int C=1;C<4;C++)if((C&used)==used)v+=y[97+510+((tau*8+rc)*3+C-1)*255+pi-1];}
    cl[clindex(tau,rc,used,mask)]=v*(U/720);
  }
  vector<int> es(nh),cs(nh);vector<Z> targets(nh),slacks(nh);
  for(int h=0;h<nh;h++){in>>es[h]>>cs[h]>>targets[h];if(has_slacks)in>>slacks[h];assert(es[h]>=0&&es[h]<(1<<20)&&cs[h]>=0&&cs[h]<64);}
  assert(in);int failures=0;
  #pragma omp parallel for reduction(+:failures) schedule(dynamic,16)
  for(int h=0;h<nh;h++){
    int e=es[h],c=cs[h],bad=0,missing=0;Z total=0;
    auto edge=[&](int a,int b,int d){return (e>>ti[a][b][d])&1;};
    for(auto t:triples[6]){int count=((c>>t[0])&1)+((c>>t[1])&1)+((c>>t[2])&1);int present=edge(t[0],t[1],t[2]);
      bad+=present&&(count==0||count==2);missing+=!present&&count==1;}
    long target=long(bad*cd-missing*cn)*(D/(20L*cd));
    if(targets[h]!=target||slacks[h]<0){failures++;continue;}
    for(auto p:perms){
      for(int k:{2,4}){vector<int> root(p.begin(),p.begin()+k);auto it=bid.find({k,encoded(e,c,root)});if(it==bid.end())continue;
        const auto& b=blocks[it->second];int f,g;
        if(k==2){f=flag(e,c,root,{p[2],p[3]});g=flag(e,c,root,{p[4],p[5]});}
        else{auto a=root;a.push_back(p[4]);f=encoded(e,c,a);a.back()=p[5];g=encoded(e,c,a);}
        int i=b.ix[f],j=b.ix[g];assert(i>=0&&j>=0);total+=b.Q[i*b.d+j];
      }
      int x=p[0],u=p[1],v=p[2],colour=(c>>x)&1,cnt=((c>>u)&1)+((c>>v)&1);
      int sign=edge(x,u,v)*((cnt==1)-(cnt==0))*(colour?-1:1);
      int j=local[colour].ix[flag(e,c,{x},{p[3],p[4],p[5]})];assert(j>=0);
      if(sign)total+=sign*yl[(colour?local[0].d:0)+j];
      int typ=encoded(e,c,{x,u}),off=0;
      for(int bi=0;bi<3;bi++){const auto& b=blocks[bi];assert(b.k==2&&b.n==4);
        if(typ==b.type){int q=b.ix[flag(e,c,{x,u},{p[4],p[5]})];assert(q>=0);
          int diff=edge(x,p[2],p[3])-edge(u,p[2],p[3]);if(diff)total+=diff*eq[off+q];}off+=b.d;}
      assert(off==120);
      int fj=global.ix[flag(e,c,{}, {p[3],p[4],p[5]})];assert(fj>=0);
      int good=edge(x,u,v)*((((c>>x)&1)+((c>>u)&1)+((c>>v)&1))==1);
      total+=(5*good-2)*yc[fj];total+=(1000000000L*edge(x,u,v)-464101615L)*(yd[fj]+yd[8]);
      int a=p[3],b=p[4],d=p[5],ab=edge(x,a,b),ad=edge(x,a,d),bd=edge(x,b,d);
      int val=ab*ad*(1-bd)-ab*ad*bd*edge(a,b,d);
      if(val){int mask=0,used=0;for(int z:{a,b,d}){mask|=1<<(4*edge(x,u,z)+2*edge(x,v,z)+edge(u,v,z));used|=1<<((c>>z)&1);}
        int rc=((c>>x)&1)+2*((c>>u)&1)+4*((c>>v)&1);total+=val*cl[clindex(edge(x,u,v),rc,used,mask)];}
    }
    Z gap=S*(U/bd)*bn-S*target*(U/D)-total;
    if((has_slacks&&gap!=slacks[h]*(U/D))||(!has_slacks&&gap<0)){
      #pragma omp critical
      if(failures<4)cerr<<"REJECT: class identity "<<h<<endl;
      failures++;
    }
  }
  if(failures){cerr<<"REJECT: coefficient, sign, or identity failures="<<failures<<endl;return 1;}
  vector<uint8_t> seen(1<<26);long labelled=0;
  for(int h=0;h<nh;h++){if(argc==3&&es[h]==0&&cs[h]==0)continue;assert(!seen[(es[h]<<6)|cs[h]]);for(auto p:perms){vector<int> order(p.begin(),p.end());int key=encoded(es[h],cs[h],order);if(!seen[key]){seen[key]=1;labelled++;}}}
  set<int> forbidden;for(auto p:perms){int f=0;for(int j=0;j<5;j++)f|=1<<ti[p[j]][p[(j+1)%5]][p[(j+2)%5]];forbidden.insert(f);}
  for(int e=0;e<(1<<20);e++){bool allowed=true;for(int f:forbidden)if((e&f)==f){allowed=false;break;}for(int c=0;c<64;c++)assert(bool(seen[(e<<6)|c])==allowed);}
  assert(labelled==23758656);
  cout<<"{\"status\":\"EXACT_B1_IDENTITIES_AND_COVER\",\"classes\":"<<nh<<",\"labelled\":"<<labelled
      <<",\"coefficient\":["<<cn<<","<<cd<<"],\"bound\":["<<bn<<","<<bd<<"],\"wall_seconds\":"<<chrono::duration<double>(chrono::steady_clock::now()-start).count()<<"}"<<endl;
}
