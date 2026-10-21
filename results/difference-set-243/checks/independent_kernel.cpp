// Separate complete lifting kernel, with its own option construction and recursive DFS.
// usage: independent_kernel P243 CASES CONV FIRST STOP  -> rows "id valid nodes solutions"
// CONV 0: six-cell digit j = omit orbit j ; CONV 1: digit j = j-th lexicographic pair (01,02,12)
#include <cstdio>
#include <cstdlib>
#include <vector>
#include <array>
#include <string>
#include <fstream>
#include <sstream>
using namespace std;
static int SUBT[243][243];
struct Case{vector<int> base; vector<array<vector<int>,3>> opts;};
static int enc(int x,int y,int z){return 81*x+9*y+z;}
int main(int argc,char**argv){
  if(argc<6){fprintf(stderr,"usage\n");return 2;}
  int conv=atoi(argv[3]); long long first=atoll(argv[4]),stop=atoll(argv[5]);
  for(int a=0;a<243;a++)for(int b=0;b<243;b++){int x=(a/81-b/81+3)%3,y=(a/9%9-b/9%9+9)%9,z=(a%9-b%9+9)%9;SUBT[a][b]=enc(x,y,z);}
  // orbits from p243 (only used for orbit membership/order); verify they are 61-orbits
  ifstream f(argv[1]); string line; vector<vector<int>> orbs; int ln=0;
  while(getline(f,line)){ln++; if(ln<=2)continue; istringstream s(line); int n; if(!(s>>n))continue; vector<int> o(n); for(auto&e:o)s>>e; orbs.push_back(o);}
  auto mul61=[](int a){int x=a/81,y=a/9%9,z=a%9;return enc(x*61%3,y*61%9,z*61%9);};
  for(auto&o:orbs){ for(int e:o){int m=mul61(e); bool in=false; for(int e2:o) if(e2==m) in=true; if(!in){fprintf(stderr,"bad orbit\n");return 3;}}}
  if(orbs.size()!=99){fprintf(stderr,"orbit count %zu\n",orbs.size());return 3;}
  const int MASK=24909666; vector<int> S;
  for(int b=0;b<27;b++) if(MASK>>b&1){int x=b/9,u=b/3%3,w=b%3; S.push_back(enc(x,3*u,3*w));}
  // cell of an element
  auto cell=[](int a){return 9*(a/81)+3*(a/9%9%3)+(a%9%3);};
  vector<vector<int>> cellorbs(27); for(int i=0;i<99;i++) if(orbs[i].size()==3) cellorbs[cell(orbs[i][0])].push_back(i);
  for(int c=0;c<27;c++){ int exp=(c==0||c==9||c==18)?0:3; if((int)cellorbs[c].size()!=exp){fprintf(stderr,"cell %d has %zu orbits\n",c,cellorbs[c].size());return 3;} }
  ifstream cf(argv[2]); vector<Case> cases;
  while(getline(cf,line)){ istringstream s(line); int w; if(!(s>>w))continue; int r[27]; for(int i=0;i<27;i++)s>>r[i];
    if(r[0]!=4||r[9]!=3||r[18]!=6){fprintf(stderr,"special\n");return 3;}
    Case C; C.base=S; vector<int> six,three; for(int i=0;i<27;i++){ if(i==0||i==9||i==18)continue; if(r[i]==6)six.push_back(i); else if(r[i]==3)three.push_back(i); else {fprintf(stderr,"coef\n");return 3;} }
    auto addcell=[&](int c,bool isSix){ array<vector<int>,3> op; auto&co=cellorbs[c];
      for(int j=0;j<3;j++){ vector<int> pts; if(!isSix){ for(int e:orbs[co[j]])pts.push_back(e);} else {
          int keep[2]; if(conv==0){int k=0; for(int t=0;t<3;t++) if(t!=j) keep[k++]=t;} else {static const int P[3][2]={{0,1},{0,2},{1,2}}; keep[0]=P[j][0];keep[1]=P[j][1];}
          for(int t=0;t<2;t++) for(int e:orbs[co[keep[t]]]) pts.push_back(e);} op[j]=pts; }
      C.opts.push_back(op);};
    for(int c:six)addcell(c,true); for(int c:three)addcell(c,false);
    if(C.opts.size()!=24){fprintf(stderr,"opts\n");return 3;}
    cases.push_back(C);}
  if(cases.size()!=8){fprintf(stderr,"cases\n");return 3;}
  long long P12=531441; long long n=stop-first; vector<array<long long,3>> out(n);
  #pragma omp parallel for schedule(dynamic,16)
  for(long long k=0;k<n;k++){ long long id=first+k; int ci=id/P12; long long pre=id%P12; const Case&C=cases[ci];
    int digit[24]; long long t=pre; for(int d=11;d>=0;d--){digit[d]=t%3;t/=3;}
    vector<int> cnt(243,0); vector<int> set=C.base; bool ok=true;
    for(size_t i=0;i<set.size();i++)for(size_t j=0;j<set.size();j++) if(i!=j) cnt[SUBT[set[i]][set[j]]]++;
    auto addpts=[&](const vector<int>&np)->bool{ bool good=true; size_t m=set.size();
      for(int a:np){ for(size_t j=0;j<set.size();j++){ int d1=SUBT[a][set[j]],d2=SUBT[set[j]][a]; if(++cnt[d1]>60)good=false; if(++cnt[d2]>60)good=false;} set.push_back(a);} (void)m; return good;};
    auto rempts=[&](const vector<int>&np){ for(size_t q=0;q<np.size();q++){ int a=set.back(); set.pop_back(); for(size_t j=0;j<set.size();j++){cnt[SUBT[a][set[j]]]--;cnt[SUBT[set[j]][a]]--;} } };
    for(int d=0;d<12&&ok;d++){ if(!addpts(C.opts[d][digit[d]])) ok=false; }
    if(!ok){out[k]={0,0,0};continue;}
    long long nodes=0,sols=0;
    // recursive DFS
    struct R{static void go(int d,const Case&C,vector<int>&set,vector<int>&cnt,long long&nodes,long long&sols,
        decltype(addpts)&add,decltype(rempts)&rem){ nodes++;
        if(d==24){ if(set.size()!=121){fprintf(stderr,"size\n");exit(4);} bool all=true; for(int g=1;g<243;g++) if(cnt[g]!=60) all=false; if(all){sols++; fprintf(stderr,"SOLUTION\n");} return; }
        for(int j=0;j<3;j++){ bool g=add(C.opts[d][j]); if(g) go(d+1,C,set,cnt,nodes,sols,add,rem); rem(C.opts[d][j]); } } };
    R::go(12,C,set,cnt,nodes,sols,addpts,rempts);
    out[k]={1,nodes,sols};
  }
  for(long long k=0;k<n;k++) printf("%lld %lld %lld %lld\n",first+k,out[k][0],out[k][1],out[k][2]);
}
