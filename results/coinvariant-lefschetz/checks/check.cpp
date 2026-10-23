// Independent certificate verifier. No Groebner-basis search is performed.
// Membership: FLINT exact finite-field sparse polynomial convolution.
// Buchberger: own sparse polynomial arithmetic, division, product/chain DAG.
#include <flint/nmod_mpoly.h>
#include <omp.h>
#include <algorithm>
#include <atomic>
#include <chrono>
#include <cstdlib>
#include <fstream>
#include <filesystem>
#include <iostream>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>
#include <unordered_map>
#include <queue>
using namespace std;
using U=uint64_t;
int NV,P,NI,NG;vector<int> pure_bounds;int max_input_degree=0,max_pair_lcm_degree=0;vector<int> W;vector<string> names;vector<const char*> cnames;
struct Term{U m;int c;};using Poly=vector<Term>;
int expo(U a,int i){return (a>>(8*i))&255;}
int deg(U a){int d=0;for(int i=0;i<NV;i++)d+=expo(a,i)*W[i];return d;}
bool mondiv(U a,U b){for(int i=0;i<NV;i++)if(expo(a,i)>expo(b,i))return false;return true;}
U lcm_m(U a,U b){U c=0;for(int i=0;i<NV;i++)c|=U(max(expo(a,i),expo(b,i)))<<(8*i);return c;}
bool coprime(U a,U b){for(int i=0;i<NV;i++)if(expo(a,i)&&expo(b,i))return false;return true;}
int mod(long long a){int v=a%P;return v<0?v+P:v;}
int inv(int a){int r=1;for(int b=P-2;b;b>>=1,a=mod(a*a))if(b&1)r=mod(r*a);return r;}
Poly parse(const string&s){
 Poly f;size_t k=0;
 while(k<s.size()){
  int sign=1;if(s[k]=='+'||s[k]=='-'){if(s[k++]=='-')sign=-1;}
  long long c=1;if(k<s.size()&&isdigit(s[k])){c=0;while(k<s.size()&&isdigit(s[k]))c=c*10+s[k++]-'0';}
  U m=0;
  while(k<s.size()&&s[k]!='+'&&s[k]!='-'){
   if(s[k]=='*'){k++;continue;}
   int v=-1;for(int i=0;i<NV;i++)if(s.compare(k,names[i].size(),names[i])==0){v=i;k+=names[i].size();break;}
   if(v<0)throw runtime_error("bad polynomial token at "+s.substr(k,30));
   int e=1;if(k<s.size()&&s[k]=='^'){k++;e=0;while(k<s.size()&&isdigit(s[k]))e=e*10+s[k++]-'0';}
   if(e<0||e>200||expo(m,v)+e>200)throw runtime_error("exponent range");m+=U(e)<<(8*v);
  }
  int a=mod(sign*c);if(a)f.push_back({m,a});
 }
 sort(f.begin(),f.end(),[](Term a,Term b){return a.m<b.m;});
 for(int i=1;i<(int)f.size();i++)if(f[i-1].m==f[i].m)throw runtime_error("duplicate monomial");
 return f;
}
void homogeneous(const Poly&f){if(f.empty())throw runtime_error("zero input/basis polynomial");int d=deg(f[0].m);for(auto t:f)if(deg(t.m)!=d)throw runtime_error("inhomogeneous basis/input");}
struct Entry{int i,j;streamoff offset;};
struct Data{vector<string> Is,Gs;vector<Poly>I,G;vector<vector<Entry>>T;long long Tterms=0;};
// Trusted package location comes from verify.py, never from the certificate.
// Compare canonical coefficient/exponent data, independently of Python/Singular.
void bind_frozen_inputs(const vector<Poly>&inputs){
 if(P!=1009)return; // The separate neighbour validator covers G33.
 const char* root=getenv("CFG_INPUT_DIR");
 if(!root||!*root)throw runtime_error("CFG_INPUT_DIR required for frozen G34 input binding");
 const int degrees[]={6,12,18,24,30,42};
 for(int i=0;i<6;i++){
  ifstream f(filesystem::path(root)/("input-"+to_string(degrees[i])+".txt"));
  if(!f)throw runtime_error("cannot open frozen G34 input");
  Poly anchor;string line;
  while(getline(f,line)){
   if(line.empty())continue;
   for(char&ch:line)if(ch=='{'||ch=='}'||ch==','||ch==':')ch=' ';
   istringstream ss(line);U m=0;int e;long long c;string extra;
   for(int v=0;v<NV;v++){
    if(!(ss>>e)||e<0||e>200)throw runtime_error("bad frozen input exponent");
    m|=U(e)<<(8*v);
   }
   if(!(ss>>c)||(ss>>extra))throw runtime_error("bad frozen input coefficient");
   if(mod(c))anchor.push_back({m,mod(c)});
  }
  sort(anchor.begin(),anchor.end(),[](Term a,Term b){return a.m<b.m;});
  for(size_t j=1;j<anchor.size();j++)if(anchor[j-1].m==anchor[j].m)throw runtime_error("duplicate frozen input monomial");
  bool same=anchor.size()==inputs[i].size();
  if(same)for(size_t j=0;j<anchor.size();j++)if(anchor[j].m!=inputs[i][j].m||anchor[j].c!=inputs[i][j].c){same=false;break;}
  if(!same)throw runtime_error("frozen input mismatch at I "+to_string(i+1));
 }
}
Data load(const string&path){
 ifstream f(path);string s;getline(f,s);if(s!="CFG_POLY_V1")throw runtime_error("bad header");getline(f,s);istringstream(s)>>P>>NV>>NI>>NG;
 if(!((P==1009&&NV==6&&NI==6)||(P==73&&NV==5&&NI==5))||NG<=0)throw runtime_error("bad frozen field/variable/input count");
 W=NV==6?vector<int>{3,4,6,9,1,1}:vector<int>(5,1);
 names=NV==6?vector<string>{"a","b","c","d","y","z"}:vector<string>{"x1","x2","x3","x4","x5"};for(auto &n:names)cnames.push_back(n.c_str());
 {
 ifstream order(filesystem::path(path).parent_path()/"unit-order.txt");string magic,ord,v;int p0,n0,w0;
 if(!(order>>magic>>p0>>n0>>ord)||magic!="CFG_ORDER_V1"||p0!=P||n0!=NV||ord!="weighted_degree_reverse_lex")throw runtime_error("bad declared order");
 for(int i=0;i<NV;i++)if(!(order>>v)||v!=names[i])throw runtime_error("declared variable order mismatch");
 for(int i=0;i<NV;i++)if(!(order>>w0)||w0<=0||w0!=W[i])throw runtime_error("nonpositive or incorrect declared weight");
 if(order>>v)throw runtime_error("extra order data");
 }
 Data d;d.Is.resize(NI);d.Gs.resize(NG);d.T.resize(NG);
 vector<vector<bool>>seen(NI,vector<bool>(NG));
 while(f){streamoff off=f.tellg();if(!getline(f,s))break;istringstream ss(s);char kind;int i,j;ss>>kind>>i;if(kind=='T')ss>>j;string expr;ss>>expr;
  if(!ss||!ss.eof()||i<1||(kind=='I'&&i>NI)||(kind=='G'&&i>NG)||(kind=='T'&&(i>NI||j<1||j>NG)))throw runtime_error("bad record");
  if(kind=='I'){if(!d.Is[i-1].empty())throw runtime_error("duplicate I");d.Is[i-1]=expr;}
  else if(kind=='G'){if(!d.Gs[i-1].empty())throw runtime_error("duplicate G");d.Gs[i-1]=expr;}
  else if(kind=='T'){if(seen[i-1][j-1])throw runtime_error("duplicate T");seen[i-1][j-1]=true;d.T[j-1].push_back({i-1,j-1,off});}
  else throw runtime_error("unknown record");
 }
 for(auto&s:d.Is){d.I.push_back(parse(s));homogeneous(d.I.back());}
 bind_frozen_inputs(d.I);
 for(auto&s:d.Gs){d.G.push_back(parse(s));homogeneous(d.G.back());}
 {
 ifstream leads(filesystem::path(path).parent_path()/"unit-initial.txt");string line;int row=0;
 while(getline(leads,line)){
 if(line.empty())continue;for(char&c:line)if(c==','||c=='{'||c=='}'||c=='('||c==')'||c=='['||c==']')c=' ';
 istringstream ss(line);U m=0;int e;for(int i=0;i<NV;i++){if(!(ss>>e)||e<0||e>200)throw runtime_error("bad declared LT exponent");m|=U(e)<<(8*i);}
 string extra;if(ss>>extra)throw runtime_error("extra LT exponent");
 if(row>=NG||m!=d.G[row][0].m)throw runtime_error("declared LT differs from recomputed weighted revlex LT");row++;
 }
 if(row!=NG)throw runtime_error("declared LT cover gap");
 pure_bounds.assign(NV,0);
 for(auto&g:d.G){U m=g[0].m;int count=0,var=-1;for(int i=0;i<NV;i++)if(expo(m,i)){count++;var=i;}
 if(count==1){int e=expo(m,var);if(!pure_bounds[var]||e<pure_bounds[var])pure_bounds[var]=e;}}
 for(int e:pure_bounds)if(e<=0)throw runtime_error("missing pure power: nonfinite leading-ideal cover");
 // Homogeneous reduction preserves weighted degree. Positive integer weights
 // and a degree <256 imply every exponent stays <256, so packed-byte
 // monomial addition/subtraction cannot carry or borrow between variables.
 for(auto&f:d.I)max_input_degree=max(max_input_degree,deg(f[0].m));
 for(int j=0;j<NG;j++)for(int i=0;i<j;i++)max_pair_lcm_degree=max(max_pair_lcm_degree,deg(lcm_m(d.G[i][0].m,d.G[j][0].m)));
 if(max_input_degree>=256||max_pair_lcm_degree>=256)throw runtime_error("packed exponent no-carry precondition violated");
 }
 return d;
}
struct RStats{long long steps=0,updates=0;};
// All inputs and reductions are homogeneous, so ascending packed exponent
// tuples (last variable is most significant) give the required reverse lex.
bool reduce_sparse(const vector<Poly>&G, const vector<int>&inverses, const Poly&A,U shiftA,int scaleA,const Poly*B,U shiftB,int scaleB,RStats&st){
 unordered_map<U,int> c;c.reserve(8192);priority_queue<U,vector<U>,greater<U>> heap;
 auto add=[&](U m,int a){if(!a)return;auto it=c.find(m);if(it==c.end()){c.emplace(m,a);heap.push(m);}else {it->second=mod(it->second+a);if(!it->second)c.erase(it);}};
 for(auto t:A)add(t.m+shiftA,mod(t.c*scaleA));if(B)for(auto t:*B)add(t.m+shiftB,mod(t.c*scaleB));
 while(!c.empty()){
  if(heap.empty())throw runtime_error("internal heap error");U m=heap.top();heap.pop();auto it=c.find(m);if(it==c.end())continue;int a=it->second;int k=-1;
  for(int j=0;j<(int)G.size();j++)if(mondiv(G[j][0].m,m)){k=j;break;}
  if(k<0)return false;
  U shift=m-G[k][0].m;int scale=mod(a*inverses[k]);c.erase(it);st.steps++;
  for(size_t v=1;v<G[k].size();v++){auto t=G[k][v];add(t.m+shift,mod(-scale*t.c));st.updates++;}
 }
 return true;
}
struct Pair{U l;int i,j,d;};
int main(int argc,char**argv){try{
 if(argc<4)throw runtime_error("usage: check certificate threads output-prefix [membership-only]");
 string path=argv[1],out=argv[3];int threads=stoi(argv[2]);omp_set_num_threads(threads);
 auto start=chrono::steady_clock::now();auto elapsed=[&](){return chrono::duration<double>(chrono::steady_clock::now()-start).count();};
 Data d=load(path);double readtime=elapsed();cerr<<"read "<<NG<<" basis, "<<readtime<<" seconds; declared LT recomputed, positive weights, pure-power bounds:";for(int e:pure_bounds)cerr<<" "<<e;cerr<<"; max_input_degree="<<max_input_degree<<" max_pair_lcm_degree="<<max_pair_lcm_degree<<" (<256, no carry)\n";
 nmod_mpoly_ctx_t ctx;nmod_mpoly_ctx_init(ctx,NV,ORD_DEGREVLEX,P);
 vector<nmod_mpoly_struct> I(NI),G(NG);
 for(int i=0;i<NI;i++){nmod_mpoly_init(&I[i],ctx);if(nmod_mpoly_set_str_pretty(&I[i],d.Is[i].c_str(),cnames.data(),ctx))throw runtime_error("FLINT parse I");}
 for(int j=0;j<NG;j++){nmod_mpoly_init(&G[j],ctx);if(nmod_mpoly_set_str_pretty(&G[j],d.Gs[j].c_str(),cnames.data(),ctx))throw runtime_error("FLINT parse G");}
 atomic<int>errors{0},finished{0};atomic<long long>tterms{0};
 #pragma omp parallel
 {
 ifstream cert(path);nmod_mpoly_t a,b,c;nmod_mpoly_init(a,ctx);nmod_mpoly_init(b,ctx);nmod_mpoly_init(c,ctx);
 #pragma omp for schedule(dynamic)
 for(int j=0;j<NG;j++){
  nmod_mpoly_zero(a,ctx);
  for(auto e:d.T[j]){cert.clear();cert.seekg(e.offset);string line;getline(cert,line);istringstream ss(line);string tag,expr;int i0,j0;ss>>tag>>i0>>j0>>expr;
   if(nmod_mpoly_set_str_pretty(b,expr.c_str(),cnames.data(),ctx)){errors++;continue;}
   tterms+=nmod_mpoly_length(b,ctx);nmod_mpoly_mul(c,&I[e.i],b,ctx);nmod_mpoly_add(a,a,c,ctx);
  }
  if(!nmod_mpoly_equal(a,&G[j],ctx)){cerr<<"MEMBERSHIP_FAIL "<<j+1<<"\n";errors++;}
  int n=++finished;if(n%100==0)cerr<<"membership "<<n<<"/"<<NG<<" time="<<elapsed()<<"\n";
 }
 nmod_mpoly_clear(a,ctx);nmod_mpoly_clear(b,ctx);nmod_mpoly_clear(c,ctx);
 }
 double membership=elapsed()-readtime;cerr<<"membership errors="<<errors<<" seconds="<<membership<<" Tterms="<<tterms<<"\n";
 if(errors)throw runtime_error("coefficientwise I*T=G rejected");
 ofstream rec(out+".json");
 if(argc>4){rec<<"{\"accepted\":true,\"frozen_inputs_bound\":"<<(P==1009?6:0)<<",\"membership_columns\":"<<NG<<",\"T_terms\":"<<tterms<<",\"read_seconds\":"<<readtime<<",\"membership_seconds\":"<<membership<<",\"wall_seconds\":"<<elapsed()<<"}\n";return 0;}
 vector<int> inverses;for(auto&g:d.G)inverses.push_back(inv(g[0].c));
 long long inputsteps=0,inputupdates=0;
 #pragma omp parallel for reduction(+:inputsteps,inputupdates) schedule(dynamic)
 for(int i=0;i<NI;i++){RStats st;if(!reduce_sparse(d.G,inverses,d.I[i],0,1,nullptr,0,0,st)){errors++;cerr<<"INPUT_REDUCTION_FAIL "<<i+1<<"\n";}inputsteps+=st.steps;inputupdates+=st.updates;}
 if(errors)throw runtime_error("input inclusion rejected");double inputtime=elapsed()-readtime-membership;
 vector<Pair>pairs;pairs.reserve(NG*(NG-1)/2);long long products=0,chains=0;
 for(int j=0;j<NG;j++)for(int i=0;i<j;i++){U l=lcm_m(d.G[i][0].m,d.G[j][0].m);pairs.push_back({l,i,j,deg(l)});}
 sort(pairs.begin(),pairs.end(),[](Pair a,Pair b){if(a.d!=b.d)return a.d<b.d;if(a.l!=b.l)return a.l<b.l;return a.j!=b.j?a.j<b.j:a.i<b.i;});
 vector<unsigned char>status(NG*NG);auto idx=[&](int i,int j){if(i>j)swap(i,j);return j*NG+i;};vector<Pair>direct;
 ofstream plan(out+".pairs");plan<<"CFG_PAIRS_V1 "<<NG<<"\n";
 for(auto p:pairs){int why=-1;char flag='D';
  if(coprime(d.G[p.i][0].m,d.G[p.j][0].m)){flag='P';products++;}
  else for(int k=0;k<NG;k++)if(k!=p.i&&k!=p.j&&mondiv(d.G[k][0].m,p.l)&&status[idx(p.i,k)]&&status[idx(p.j,k)]){why=k;flag='C';chains++;break;}
  status[idx(p.i,p.j)]=1;
  plan<<p.i+1<<" "<<p.j+1<<" "<<flag;if(why>=0)plan<<" "<<why+1;plan<<"\n";
  if(flag=='D')direct.push_back(p);
 }
 plan.close();double planning=elapsed()-readtime-membership-inputtime;cerr<<"plan total="<<pairs.size()<<" product="<<products<<" chain="<<chains<<" direct="<<direct.size()<<" time="<<elapsed()<<"\n";
 long long steps=0,updates=0;finished=0;
 vector<RStats>stats(direct.size());
 #pragma omp parallel for reduction(+:steps,updates) schedule(dynamic)
 for(size_t a=0;a<direct.size();a++){
  auto p=direct[a];RStats st;
  if(!reduce_sparse(d.G,inverses,d.G[p.i],p.l-d.G[p.i][0].m,inverses[p.i],&d.G[p.j],p.l-d.G[p.j][0].m,mod(-inverses[p.j]),st)){errors++;cerr<<"SPAIR_FAIL "<<p.i+1<<" "<<p.j+1<<"\n";}
  stats[a]=st;steps+=st.steps;updates+=st.updates;int n=++finished;if(n%100==0)cerr<<"spairs "<<n<<"/"<<direct.size()<<" time="<<elapsed()<<"\n";
 }
 ofstream reductions(out+".reductions");for(size_t i=0;i<direct.size();i++)reductions<<direct[i].i+1<<" "<<direct[i].j+1<<" "<<stats[i].steps<<" "<<stats[i].updates<<"\n";
 double alltime=elapsed();rec<<"{\"accepted\":"<<(errors?"false":"true")<<",\"unresolved\":0,\"prime\":"<<P<<",\"frozen_inputs_bound\":"<<(P==1009?6:0)<<",\"max_input_weighted_degree\":"<<max_input_degree<<",\"max_pair_lcm_weighted_degree\":"<<max_pair_lcm_degree<<",\"packed_no_carry_checked\":true,\"basis_size\":"<<NG<<",\"membership_columns\":"<<NG<<",\"T_terms\":"<<tterms<<",\"inputs_reduced\":"<<NI<<",\"pairs_total\":"<<pairs.size()<<",\"pairs_product\":"<<products<<",\"pairs_chain\":"<<chains<<",\"pairs_direct\":"<<direct.size()<<",\"reduction_steps\":"<<steps<<",\"coefficient_updates\":"<<updates<<",\"read_seconds\":"<<readtime<<",\"membership_seconds\":"<<membership<<",\"input_reduction_seconds\":"<<inputtime<<",\"pair_plan_seconds\":"<<planning<<",\"spair_seconds\":"<<alltime-readtime-membership-inputtime-planning<<",\"wall_seconds\":"<<alltime<<"}\n";
 if(errors)throw runtime_error("S-pair rejected");cerr<<"ACCEPTED seconds="<<alltime<<"\n";
 for(auto &a:I)nmod_mpoly_clear(&a,ctx);for(auto&a:G)nmod_mpoly_clear(&a,ctx);nmod_mpoly_ctx_clear(ctx);return 0;
 }catch(exception&e){cerr<<"REJECTED: "<<e.what()<<"\n";return 1;}}
