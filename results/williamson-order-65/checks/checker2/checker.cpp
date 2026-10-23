#include <algorithm>
#include <array>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <ctime>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <map>
#include <numeric>
#include <set>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>
#include <fcntl.h>
#include <sys/mman.h>
#include <unistd.h>
#include <openssl/sha.h>
#include <omp.h>
#include "coefficients.h"
using namespace std;
struct Timer { double w=omp_get_wtime(); clock_t c=clock(); void line(string label,bool ok,string detail) {cout<<(ok?"PASS ":"FAIL ")<<label<<" "<<detail<<" cpu="<<double(clock()-c)/CLOCKS_PER_SEC<<" wall="<<omp_get_wtime()-w<<endl;} };
struct Cl {int id,key,r; array<int,13>x{}; uint64_t n,off; string hash; array<int,7> ac{};};
vector<Cl> cls;
int code(const array<int,13>&x){int c=0,p=1;for(int j=0;j<7;j++){c+=((5-x[j])/2)*p;p*=6;}return c;}
void load(string path){ifstream f(path);string l;uint64_t off=0;set<int>keys,codes;while(getline(f,l)){Cl c;string xs;istringstream s(l);if(!(s>>c.id>>c.key>>c.r>>xs>>c.n>>c.off>>c.hash))throw runtime_error("class syntax");replace(xs.begin(),xs.end(),',',' ');istringstream v(xs);for(int j=0;j<7;j++){if(!(v>>c.x[j]))throw runtime_error("class X");if(j)c.x[13-j]=c.x[j];}if(c.id!=(int)cls.size()||c.off!=off||!keys.insert(c.key).second||!codes.insert(code(c.x)).second||accumulate(c.x.begin(),c.x.end(),0)!=c.r)throw runtime_error("class metadata");for(int k=0;k<7;k++)for(int j=0;j<13;j++)c.ac[k]+=c.x[j]*c.x[(j+k)%13];off+=c.n;cls.push_back(c);}if(cls.size()!=15251||off!=396050997)throw runtime_error("class total");}
uint32_t image_mask(uint32_t m,int u){uint32_t out=0;for(int i=1;i<=32;i++){int j=i*u%65;j=min(j,65-j);if(m&(1u<<(j-1)))out|=1u<<(i-1);}return out;}
uint32_t perm[3][4][256];
bool minimal(uint32_t m){for(int k=0;k<3;k++){uint32_t v=0;for(int j=0;j<4;j++)v|=perm[k][j][(m>>(8*j))&255];if(v<m)return false;}return true;}
void rows(string dir){Timer t;int nt=omp_get_max_threads();vector<int> index(279936,-1);for(auto&c:cls)index[code(c.x)]=c.id;
 vector<array<int64_t,32>> lo(65536),hi(65536); vector<int> lc(65536),hc(65536);vector<unsigned char> pc(65536);
 int powers[7]={1,6,36,216,1296,7776,46656};
 for(int m=1;m<65536;m++){int b=__builtin_ctz((unsigned)m),prev=m&(m-1);pc[m]=pc[prev]+1;for(int k=1;k<=32;k++){lo[m][k-1]=lo[prev][k-1]+COEFF[((b+1)*k)%65];hi[m][k-1]=hi[prev][k-1]+COEFF[((b+17)*k)%65];}int j=(b+1)%13;lc[m]=lc[prev]+(j?powers[min(j,13-j)]:2);j=(b+17)%13;hc[m]=hc[prev]+(j?powers[min(j,13-j)]:2);}
 vector<vector<vector<uint32_t>>> bins(nt,vector<vector<uint32_t>>(cls.size()));uint64_t missing=0,near=0;
 #pragma omp parallel reduction(+:missing,near)
 {int tid=omp_get_thread_num();
 #pragma omp for schedule(static)
 for(int h=0;h<65536;h++)for(int l=0;l<65536;l++){int pop=pc[h]+pc[l];if(pop<13||pop>20)continue;bool ok=true;for(int k=0;k<32;k++){int64_t a=hi[h][k]+lo[l][k];if(a>LIMIT||a< -LIMIT){ok=false;break;}if(llabs(a)>LIMIT-66)near++;}if(!ok)continue;int id=index[hc[h]+lc[l]];if(id<0){missing++;continue;}bins[tid][id].push_back((uint32_t(h)<<16)|l);}}
 uint64_t total=0;for(auto&b:bins)for(auto&v:b)total+=v.size();t.line("rows_regeneration",total==396050997&&missing==0,"masks_examined=4294967296 retained="+to_string(total)+" classes="+to_string(cls.size())+" unlisted="+to_string(missing)+" boundary_tests="+to_string(near)+" threads="+to_string(nt));
 Timer ht;string path=dir+"/rows.bin";int fd=open(path.c_str(),O_CREAT|O_TRUNC|O_RDWR,0644);if(fd<0||ftruncate(fd,total*4))throw runtime_error("rows file");auto out=(uint32_t*)mmap(nullptr,total*4,PROT_READ|PROT_WRITE,MAP_SHARED,fd,0);if(out==MAP_FAILED)throw runtime_error("mmap");vector<uint64_t> counts(cls.size()),mins(cls.size());vector<string> hashes(cls.size());int failures=0;
 for(int u=0;u<3;u++)for(int j=0;j<4;j++)for(int m=0;m<256;m++)perm[u][j][m]=image_mask(uint32_t(m)<<(j*8),array<int,3>{14,27,53}[u]);
 #pragma omp parallel for reduction(+:failures) schedule(dynamic)
 for(int id=0;id<(int)cls.size();id++){auto&c=cls[id];uint64_t pos=c.off;for(auto&b:bins){auto&v=b[id];counts[id]+=v.size();if(pos+v.size()<=total)copy(v.begin(),v.end(),out+pos);pos+=v.size();}if(counts[id]!=c.n){failures++;continue;}uint32_t prev=0;for(uint64_t j=0;j<c.n;j++){uint32_t m=out[c.off+j];if(j&&m<=prev)failures++;prev=m;mins[id]+=minimal(m);}unsigned char digest[32];SHA256((unsigned char*)(out+c.off),c.n*4,digest);ostringstream ss;for(auto b:digest)ss<<hex<<setw(2)<<setfill('0')<<(int)b;hashes[id]=ss.str();if(hashes[id]!=c.hash)failures++;}
 munmap(out,total*4);close(fd);ofstream stats(dir+"/class-counts.tsv");for(int id=0;id<(int)cls.size();id++)stats<<id<<'\t'<<counts[id]<<'\t'<<mins[id]<<'\t'<<hashes[id]<<'\n';ht.line("class_sha256",failures==0,"classes="+to_string(cls.size())+" mismatches="+to_string(failures));if(total!=396050997||missing||failures)throw runtime_error("rows verification failed");}
using Sig=array<int,7>;using Tup=array<int,4>;
struct Pair {Sig s;int a,b;bool operator<(const Pair&o)const{return s<o.s;}};
void cover(string units,string dir){Timer t;vector<array<int,4>> patterns={{1,-3,5,-15},{1,-3,9,13},{-3,-3,-11,-11},{-3,-7,9,-11},{-7,-7,9,9}};map<int,vector<int>> groups;for(auto&c:cls)groups[c.r].push_back(c.id);vector<Tup> tuples;
 // Derive the rowsum patterns independently rather than trust this illustrative list.
 patterns.clear();vector<int> rs={1,-3,5,-7,9,-11,13,-15};for(int a=0;a<8;a++)for(int b=a;b<8;b++)for(int c=b;c<8;c++)for(int d=c;d<8;d++)if(rs[a]*rs[a]+rs[b]*rs[b]+rs[c]*rs[c]+rs[d]*rs[d]==260)patterns.push_back({rs[a],rs[b],rs[c],rs[d]});
 for(auto pat:patterns){vector<Pair> right;for(int c:groups[pat[2]])for(int d:groups[pat[3]])if(pat[2]!=pat[3]||c<=d){Pair p;p.a=c;p.b=d;for(int k=0;k<7;k++)p.s[k]=cls[c].ac[k]+cls[d].ac[k];right.push_back(p);}sort(right.begin(),right.end());int nt=omp_get_max_threads();vector<vector<Tup>> found(nt);auto&left=groups[pat[0]];
 #pragma omp parallel for schedule(dynamic)
 for(int ix=0;ix<(int)left.size();ix++){int a=left[ix];auto&v=found[omp_get_thread_num()];for(int b:groups[pat[1]]){if(pat[0]==pat[1]&&a>b)continue;Pair q;for(int k=0;k<7;k++)q.s[k]=(k?0:260)-cls[a].ac[k]-cls[b].ac[k];auto it=lower_bound(right.begin(),right.end(),q);for(;it!=right.end()&&it->s==q.s;++it)v.push_back({a,b,it->a,it->b});}}
 for(auto&v:found)tuples.insert(tuples.end(),v.begin(),v.end());}
 sort(tuples.begin(),tuples.end());map<array<int,13>,int> xmap;for(auto&c:cls)xmap[c.x]=c.id;vector<array<int,6>> action(cls.size());for(auto&c:cls)for(int u=1;u<=6;u++){array<int,13>x;for(int j=0;j<13;j++)x[j]=c.x[j*u%13];auto it=xmap.find(x);if(it==xmap.end())throw runtime_error("class action not closed");action[c.id][u-1]=it->second;}
 map<Tup,int> minima;for(auto q:tuples){set<Tup> orbit;for(int u=0;u<6;u++){Tup z;for(int p=0;p<4;p++)z[p]=action[q[p]][u];for(int a=0;a<4;){int b=a+1;while(b<4&&cls[z[b]].r==cls[z[a]].r)b++;sort(z.begin()+a,z.begin()+b);a=b;}orbit.insert(z);if(!binary_search(tuples.begin(),tuples.end(),z))throw runtime_error("tuple action not closed");}minima[*orbit.begin()]=orbit.size();}
 ifstream f(units);string line;vector<pair<Tup,int>> given;while(getline(f,line)){istringstream s(line);int id,sz;Tup q;string extra;if(!(s>>id>>q[0]>>q[1]>>q[2]>>q[3]>>sz)||s>>extra||id!=(int)given.size())throw runtime_error("units syntax/id");given.push_back({q,sz});}set<Tup> seen;bool ok=given.size()==minima.size();for(auto [q,sz]:given){auto it=minima.find(q);if(it==minima.end()||it->second!=sz||!seen.insert(q).second)ok=false;}
 ofstream out(dir+"/cover-minima.tsv");for(auto [q,sz]:minima)out<<q[0]<<'\t'<<q[1]<<'\t'<<q[2]<<'\t'<<q[3]<<'\t'<<sz<<'\n';ok=ok&&tuples.size()==423527&&minima.size()==70699;t.line("cover",ok,"tuples="+to_string(tuples.size())+" orbits="+to_string(minima.size())+" manifest_units="+to_string(given.size()));if(!ok)throw runtime_error("cover differs");}
int main(int argc,char**argv){try{if(argc!=5)throw runtime_error("usage: checker rows|cover classes65.tsv units.tsv output-dir");load(argv[2]);if(string(argv[1])=="rows")rows(argv[4]);else if(string(argv[1])=="cover")cover(argv[3],argv[4]);else throw runtime_error("mode");return 0;}catch(exception&e){cerr<<"FAIL checker "<<e.what()<<endl;return 1;}}
