// Build twice: -DFAST_KERNEL or -DDIRECT_KERNEL. No search/checker imports.
// Both builds share the wrapper, cases, cell order, option tables and ID map.
// Their difference-counting and search kernels are separate implementations.
#include <algorithm>
#include <array>
#include <chrono>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>
#include <omp.h>
using namespace std;
using Clock = chrono::steady_clock;
using U64 = uint64_t;
void require(bool b, const char* s) { if (!b) throw runtime_error(s); }
struct Task {
 U64 id=0,nodes=0,sols=0;
 bool initialized=false,done=false,valid=false;
 string path,next;
 vector<int> witness;
};
string token(const string& s) { return s.empty()?"-":s; }
string untoken(const string& s) { return s=="-"?"":s; }
vector<int> prefix(U64 id,int depth) {
 U64 width=1;for(int i=0;i<depth;i++)width*=3;
 id%=width;vector<int> p(depth);
 for(int i=depth-1;i>=0;i--){p[i]=id%3;id/=3;}
 return p;
}

#ifdef TEST_ONLY
// Compiled out of production binaries. These controls never write range receipts.
array<int,8> test_bounds;
array<string,8> test_leaves;
int bound_for(int ci){return test_bounds.at(ci);}
bool forced_option(int ci,int d,int a){return test_leaves[ci].empty()||test_leaves[ci][d]==char('0'+a);}
template<class Choices> void dump_choices(const Choices& cases,const char* path){
 ofstream f(path);require(bool(f),"choice dump open");f<<'[';
 for(size_t ci=0;ci<cases.size();ci++){if(ci)f<<',';f<<'[';
  for(size_t d=0;d<cases[ci].size();d++){if(d)f<<',';f<<'[';
   for(int a=0;a<3;a++){if(a)f<<',';f<<'[';bool first=true;
    for(int j:cases[ci][d][a]){if(!first)f<<',';first=false;f<<j;}f<<']';
   }f<<']';
  }f<<']';
 }f<<"]\n";f.flush();require(bool(f),"choice dump write");
}
#else
constexpr int bound_for(int){return 60;}
constexpr bool forced_option(int,int,int){return true;}
#endif

#if defined(FAST_KERNEL) == defined(DIRECT_KERNEL)
#error Define exactly one kernel
#endif

#ifdef FAST_KERNEL
namespace fast {
struct Pair { int d,n; };
struct Model {
 int C;vector<vector<int>> orbit;vector<int> sz,rep,cls;
 vector<vector<Pair>> internal;vector<vector<vector<Pair>>> cross;
 vector<vector<array<vector<int>,3>>> cases;
 int sub(int a,int b) const {
  return ((a/81-b/81+3)%3)*81+((a/9%9-b/9%9+9)%9)*9+(a%9-b%9+9)%9;
 }
 Model(const char* file,const char* images) {
  ifstream f(file);int r,a,b,c,k,lam,N;
  require(bool(f>>r>>a>>b>>c>>k>>lam>>N),"input header");
  require(r==3&&a==3&&b==9&&c==9&&k==121&&lam==60&&N==99,"frozen input header");
  orbit.resize(N);sz.resize(N);vector<int> seen(243);
  for(int j=0;j<N;j++){
   require(bool(f>>sz[j])&&(sz[j]==1||sz[j]==3),"orbit size");
   orbit[j].resize(sz[j]);for(int& x:orbit[j]){
    require(bool(f>>x)&&x>=0&&x<243&&!seen[x]++,"orbit partition");
   }
  }
  for(int x:seen)require(x==1,"incomplete partition");
  string extra;
  require(!(f>>extra),"trailing input");
  cls.assign(243,-1);cls[0]=-2;
  for(auto o:orbit)for(int x:o)if(x&&cls[x]<0){
   int id=rep.size();rep.push_back(x);
   for(int y:o){cls[y]=id;cls[sub(0,y)]=id;}
  }
  C=rep.size();require(C==49,"compressed classes");
  auto compress=[&](const vector<int>& d){
   vector<Pair> out;for(int x=1;x<243;x++)require(cls[x]>=0&&d[x]==d[rep[cls[x]]],"nonconstant class");
   for(int j=0;j<C;j++)if(d[rep[j]])out.push_back({j,d[rep[j]]});
   return out;
  };
  internal.resize(N);cross.resize(N,vector<vector<Pair>>(N));
  for(int i=0;i<N;i++){
   vector<int>d(243);for(int x:orbit[i])for(int y:orbit[i])if(x!=y)d[sub(x,y)]++;
   internal[i]=compress(d);
   for(int j=0;j<i;j++){
    fill(d.begin(),d.end(),0);for(int x:orbit[i])for(int y:orbit[j]){d[sub(x,y)]++;d[sub(y,x)]++;}
    cross[i][j]=cross[j][i]=compress(d);
   }
  }
  ifstream g(images);int weight;vector<int> weights;
  while(g>>weight){
   weights.push_back(weight);array<int,27> q;
   for(int& x:q)require(bool(g>>x),"case image");
   vector<vector<int>> bucket(27);
   for(int j=0;j<N;j++)if(sz[j]==3){int x=orbit[j][0];bucket[x/81*9+(x/9%3)*3+x%3].push_back(j);}
   vector<array<vector<int>,3>> opts;
   for(int n:{6,3})for(int j=0;j<27;j++)if(!bucket[j].empty()){
    require(q[j]==3||q[j]==6,"coset amount");if(q[j]!=n)continue;
    require(bucket[j].size()==3,"coset bucket");array<vector<int>,3> row;
    for(int a=0;a<3;a++)for(int b=0;b<3;b++)if((n==3)==(a==b))row[a].push_back(bucket[j][b]);
    opts.push_back(row);
   }
   require(opts.size()==24,"choice count");cases.push_back(opts);
  }
  require(g.eof()&&weights==vector<int>({27,27,9,9,27,27,9,9}),"eight cases");
 }
};
struct State {
 const Model& m;const int bound;vector<int> cnt,chosen;vector<int> marks;
 State(const Model& M,int ci):m(M),bound(bound_for(ci)),cnt(M.C){}
 bool add(int i){
  array<int,49> d{};for(auto p:m.internal[i])d[p.d]+=p.n;
  for(int j:chosen)for(auto p:m.cross[i][j])d[p.d]+=p.n;
  for(int j=0;j<m.C;j++)if(cnt[j]+d[j]>bound)return false;
  for(int j=0;j<m.C;j++)cnt[j]+=d[j];
  chosen.push_back(i);return true;
 }
 void undo(int n){while(int(chosen.size())>n){int i=chosen.back();chosen.pop_back();
  for(auto p:m.internal[i])cnt[p.d]-=p.n;
  for(int j:chosen)for(auto p:m.cross[i][j])cnt[p.d]-=p.n;
 }}
 bool choice(int ci,int d,int a){int n=chosen.size();for(int i:m.cases[ci][d][a])if(!add(i)){undo(n);return false;}marks.push_back(n);return true;}
 void pop(){int n=marks.back();marks.pop_back();undo(n);}
 void fixed(){for(int j=0;j<int(m.orbit.size());j++)if(m.sz[j]==1){
  int x=m.orbit[j][0],a=x/81*9+(x/27%3)*3+x/3%3;
  if(24909666u>>a&1)require(add(j),"fixed S rejected");
 }}
 vector<int> points()const{vector<int> p;for(int j:chosen)for(int x:m.orbit[j])p.push_back(x);sort(p.begin(),p.end());return p;}
};
void solve(const Model& m,Task& t,int depth,U64 width,Clock::time_point deadline){
 if(t.done)return;
 int ci=t.id/width;State s(m,ci);s.fixed();bool valid=true;
 auto p=prefix(t.id,depth);for(int d=0;d<depth&&valid;d++)valid=s.choice(ci,d,p[d]);
 if(!t.initialized){t.initialized=true;t.valid=valid;if(!valid){t.done=true;return;}t.nodes=1;t.next="0";}
 require(t.valid==valid,"resume prefix validity");if(!valid){require(t.done,"invalid continuation");return;}
 require(t.next.size()==t.path.size()+1,"continuation stack");
 for(int d=0;d<int(t.path.size());d++)require(s.choice(ci,depth+d,t.path[d]-'0'),"resume path rejected");
 U64 ticks=0;
 while(true){
  if((++ticks&4095)==0&&Clock::now()>=deadline)return;
  int d=depth+t.path.size();
  if(d==24){
   require(s.points().size()==121,"leaf cardinality");
#ifndef TEST_ONLY
   for(int count:s.cnt)require(count==60,"fast full leaf differences");
#endif
   t.sols++;
   if(t.witness.empty())t.witness=s.points();
  }else if(t.next.back()<'3'){
   int a=t.next.back()++-'0';
   if(!forced_option(ci,d,a))continue;
   if(s.choice(ci,d,a)){t.path+=char('0'+a);t.next+='0';t.nodes++;}
   continue;
  }
  if(t.path.empty()){t.done=true;t.next.clear();return;}
  s.pop();t.path.pop_back();t.next.pop_back();
 }
}
}
#else
namespace direct {
// Element-level implementation. No compressed class or contribution table.
struct Input {
 vector<vector<int>> orbits;array<array<int,243>,243> difference;
 vector<array<array<vector<int>,3>,24>> images;
 Input(const char* file,const char* cases){
  ifstream f(file);int rank,g0,g1,g2,k,l,n;
  require(bool(f>>rank>>g0>>g1>>g2>>k>>l>>n),"direct header");
  require(rank==3&&g0==3&&g1==9&&g2==9&&k==121&&l==60&&n==99,"direct frozen header");
  vector<int> seen(243);for(int j=0;j<n;j++){
   int size;require(bool(f>>size)&&(size==1||size==3),"direct orbit size");vector<int> o(size);
   for(int& x:o){require(bool(f>>x)&&x>=0&&x<243&&!seen[x]++,"direct partition");}orbits.push_back(o);
  }
  for(int count:seen)require(count==1,"direct incomplete partition");
  string junk;require(!(f>>junk),"direct trailing input");
  for(int a=0;a<243;a++)for(int b=0;b<243;b++){
   int x=(a/81+3-b/81)%3,y=(a/9%9+9-b/9%9)%9,z=(a%9+9-b%9)%9;
   difference[a][b]=81*x+9*y+z;
  }
  ifstream g(cases);int weight;vector<int> weights;
  while(g>>weight){
   weights.push_back(weight);array<int,27> q;for(int& x:q)require(bool(g>>x),"direct case image");
   array<array<vector<int>,3>,24> image;int pos=0;
   for(int amount:{6,3})for(int cell=0;cell<27;cell++)if(cell%9&&q[cell]==amount){
    vector<int> bucket;
    for(int j=0;j<n;j++)if(orbits[j].size()==3){int x=orbits[j][0];if(9*(x/81)+3*(x/9%3)+x%3==cell)bucket.push_back(j);}
    require(bucket.size()==3&&pos<24,"direct bucket");
    for(int opt=0;opt<3;opt++)for(int b=0;b<3;b++)if((amount==3)==(opt==b))image[pos][opt].push_back(bucket[b]);
    pos++;
   }
   require(pos==24,"direct options");images.push_back(image);
  }
  require(g.eof()&&weights==vector<int>({27,27,9,9,27,27,9,9}),"direct eight cases");
 }
};
struct Replay {
 const Input& in;const int bound;vector<int> points;array<int,243> counts{};
 Replay(const Input& x,int ci):in(x),bound(bound_for(ci)){}
 void restore(int n){while(int(points.size())>n){int x=points.back();points.pop_back();for(int y:points){--counts[in.difference[x][y]];--counts[in.difference[y][x]];}}}
 bool orbit(int j){int before=points.size();for(int x:in.orbits[j]){
  bool ok=true;for(int y:points){if(++counts[in.difference[x][y]]>bound)ok=false;if(++counts[in.difference[y][x]]>bound)ok=false;}
  points.push_back(x);if(!ok){restore(before);return false;}
 }return true;}
 bool option(int image,int layer,int digit){int n=points.size();for(int j:in.images[image][layer][digit])if(!orbit(j)){restore(n);return false;}return true;}
 void singletons(){for(int j=0;j<int(in.orbits.size());j++)if(in.orbits[j].size()==1){
  int x=in.orbits[j][0];unsigned bit=9*(x/81)+3*(x/27%3)+(x/3%3);
  if((24909666u>>bit)&1u)require(orbit(j),"direct singleton rejected");
 }}
};
void replay(const Input& in,Task& task,int depth,U64 width,Clock::time_point deadline){
 if(task.done)return;
 int ci=task.id/width;Replay r(in,ci);r.singletons();
 U64 value=task.id%width,place=width;bool accepts=true;
 for(int layer=0;layer<depth;layer++){place/=3;int digit=value/place;value%=place;if(accepts)accepts=r.option(ci,layer,digit);}
 if(!task.initialized){task.initialized=true;task.valid=accepts;if(!accepts){task.done=true;return;}task.nodes=1;task.next="0";}
 require(accepts==task.valid,"direct resumed prefix");
 require(accepts&&task.next.size()==task.path.size()+1,"direct continuation");
 vector<int> sizes;
 for(int i=0;i<int(task.path.size());i++){sizes.push_back(r.points.size());require(r.option(ci,depth+i,task.path[i]-'0'),"direct resumed branch");}
 unsigned iterations=0;
 for(;;){
  if((++iterations%4096)==0&&Clock::now()>=deadline)break;
  size_t level=task.path.size();
  if(depth+level<24&&task.next[level]!='3'){
   char digit=task.next[level]++;int old=r.points.size();
   if(!forced_option(ci,depth+level,digit-'0'))continue;
   if(r.option(ci,depth+level,digit-'0')){sizes.push_back(old);task.path.push_back(digit);task.next.push_back('0');++task.nodes;}
  }else{
   if(depth+level==24){
    require(r.points.size()==121,"direct leaf size");
#ifndef TEST_ONLY
    for(int d=1;d<243;d++)require(r.counts[d]==60,"direct leaf differences");
#endif
    ++task.sols;if(task.witness.empty()){task.witness=r.points;sort(task.witness.begin(),task.witness.end());}
   }
   if(level==0){task.done=true;task.next.clear();break;}
   r.restore(sizes.back());sizes.pop_back();task.next.pop_back();task.path.pop_back();
  }
 }
}
}
#endif

int main(int argc,char** argv)try{
 if(argc==2&&string(argv[1])=="--help"){
  cout<<"campaign INPUT CASES DEPTH QUANTUM_SECONDS THREADS TASKS OUTPUT";
#ifdef TEST_ONLY
  cout<<" --test-config CONFIG\nTEST ONLY; also --dump-choices INPUT CASES OUTPUT [--drop-option]\n";
#else
  cout<<"\nProduction bound is fixed at 60.\n";
#endif
  return 0;
 }
#ifdef TEST_ONLY
 if((argc==5||argc==6)&&string(argv[1])=="--dump-choices"){
  bool drop=argc==6;require(!drop||string(argv[5])=="--drop-option","dump arguments");
#ifdef FAST_KERNEL
  fast::Model model(argv[2],argv[3]);if(drop)model.cases[0][0][2].clear();
  dump_choices(model.cases,argv[4]);
#else
  direct::Input model(argv[2],argv[3]);if(drop)model.images[0][0][2].clear();
  dump_choices(model.images,argv[4]);
#endif
  return 0;
 }
 require(argc==10&&string(argv[8])=="--test-config","TEST ONLY: require explicit test config");
 ifstream config(argv[9]);
 for(int ci=0;ci<8;ci++){
  string leaf;require(bool(config>>test_bounds[ci]>>leaf),"test config row");
  require(test_bounds[ci]>=0&&test_bounds[ci]<=242,"test bound");
  if(leaf!="-"){require(leaf.size()==24,"forced leaf length");for(char c:leaf)require(c>='0'&&c<='2',"forced leaf digit");test_leaves[ci]=leaf;}
 }
 string junk;require(!(config>>junk),"trailing test config");
#else
 require(argc==8,"expected INPUT CASES DEPTH QUANTUM_SECONDS THREADS TASKS OUTPUT");
#endif
 int depth=stoi(argv[3]),threads=stoi(argv[5]);double seconds=stod(argv[4]);
 require(depth>=1&&depth<=24&&seconds>0&&seconds<=300&&threads>0,"execution bounds");
 U64 width=1;for(int i=0;i<depth;i++)width*=3;
 ifstream f(argv[6]);require(bool(f),"tasks file missing");vector<Task> tasks;Task t;int init,done,valid;string path,next;size_t nw;
 while(f>>t.id>>init>>done>>valid>>t.nodes>>t.sols>>path>>next>>nw){
  require(t.id<8*width&&(init==0||init==1)&&(done==0||done==1)&&(valid==0||valid==1)&&nw<=121,"task fields");
  t.initialized=init;t.done=done;t.valid=valid;t.path=untoken(path);t.next=untoken(next);t.witness.resize(nw);
  for(int& x:t.witness)require(bool(f>>x)&&x>=0&&x<243,"witness field");
  require(depth+t.path.size()<=24,"path length");
  for(char c:t.path)require(c>='0'&&c<='2',"path digit");
  for(char c:t.next)require(c>='0'&&c<='3',"stack digit");
  tasks.push_back(t);
 }
 require(f.eof()&&!tasks.empty()&&tasks.size()<=65536,"task input malformed or oversized");
 omp_set_dynamic(0);omp_set_num_threads(threads);
#ifdef FAST_KERNEL
 fast::Model model(argv[1],argv[2]);
#else
 direct::Input model(argv[1],argv[2]);
#endif
 Clock::time_point deadline;
 int failed=0;
 #pragma omp parallel
 {
 #pragma omp single
 deadline=Clock::now()+chrono::duration_cast<Clock::duration>(chrono::duration<double>(seconds));
 #pragma omp for schedule(dynamic,1)
 for(size_t i=0;i<tasks.size();i++){
  try{
   if(Clock::now()<deadline){
#ifdef FAST_KERNEL
    fast::solve(model,tasks[i],depth,width,deadline);
#else
    direct::replay(model,tasks[i],depth,width,deadline);
#endif
   }
  }catch(const exception& e){
   #pragma omp critical
   {cerr<<"task "<<tasks[i].id<<": "<<e.what()<<'\n';failed=1;}
  }
 }
 }
 require(!failed,"kernel failed");ofstream out(argv[7]);require(bool(out),"output open");
 for(const Task& a:tasks){out<<a.id<<' '<<a.initialized<<' '<<a.done<<' '<<a.valid<<' '<<a.nodes<<' '<<a.sols<<' '<<token(a.path)<<' '<<token(a.next)<<' '<<a.witness.size();for(int x:a.witness)out<<' '<<x;out<<'\n';}
 out.flush();require(bool(out),"output write");return 0;
}catch(const exception& e){cerr<<e.what()<<'\n';return 2;}
