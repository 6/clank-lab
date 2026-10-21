// Independent re-implementation of
// the lifting search for chosen prefix IDs. Written from the problem and the
// documented ID rule only; shares no code with campaign.cpp. Orbits, cells,
// singleton set and option lists are derived here, not read from p243.txt.
// Input: cases.txt path, then IDs on stdin. Output per ID: "id valid nodes sols".
// ID rule: id = case*3^12 + big-endian ternary digits of the first 12 cells.
// Cell order: cells with coefficient 6 ascending, then coefficient 3 ascending
// (Q-cell 9x+3(y%3)+(z%3)); within a cell the three orbits ascend by least
// element; digit a takes orbit a (coefficient 3) or all orbits but a (6).
#include <cstdio>
#include <cstdlib>
#include <vector>
#include <array>
#include <algorithm>
#include <functional>
using namespace std;
static int enc(int x,int y,int z){return 81*(((x%3)+3)%3)+9*(((y%9)+9)%9)+(((z%9)+9)%9);}
static int sub(int a,int b){return enc(a/81-b/81,a/9%9-b/9%9,a%9-b%9);}
int main(int argc,char**argv){
 const unsigned MASK=24909666u;
 vector<vector<int>> cellorb(27);vector<int> S;vector<int> seen(243);
 for(int e=0;e<243;e++){if(seen[e])continue;int x=e/81,y=e/9%9,z=e%9;
  vector<int> o;for(int t:{1,61,61*61%243}){int f=enc(x*t,y*t,z*t);if(find(o.begin(),o.end(),f)==o.end())o.push_back(f);}
  for(int f:o)seen[f]=1;
  if(o.size()==1){ if(y%3==0&&z%3==0&&(MASK>>(9*x+3*(y/3)+z/3)&1))S.push_back(e);}
  else{sort(o.begin(),o.end());cellorb[9*x+3*(y%3)+z%3].push_back(o[0]);}
 }
 // orbit members keyed by least element
 auto members=[&](int m){int x=m/81,y=m/9%9,z=m%9;vector<int> o;for(int t:{1,61,61*61%243}){int f=enc(x*t,y*t,z*t);if(find(o.begin(),o.end(),f)==o.end())o.push_back(f);}return o;};
 if(S.size()!=13){fprintf(stderr,"S size\n");return 2;}
 FILE*f=fopen(argv[1],"r");vector<array<int,27>> img;int w;
 while(fscanf(f,"%d",&w)==1){array<int,27> q;for(int&v:q)if(fscanf(f,"%d",&v)!=1)return 2;img.push_back(q);}
 if(img.size()!=8)return 2;
 // options[case][pos][digit] = list of points
 vector<vector<array<vector<int>,3>>> opt(8);
 for(int c=0;c<8;c++){for(int amt:{6,3})for(int cl=0;cl<27;cl++){if(cl%9==0||img[c][cl]!=amt)continue;
   auto&b=cellorb[cl];if(b.size()!=3)return 3;sort(b.begin(),b.end());array<vector<int>,3> r;
   for(int a=0;a<3;a++)for(int j=0;j<3;j++)if((amt==3)==(a==j))for(int p:members(b[j]))r[a].push_back(p);
   opt[c].push_back(r);}
  if(opt[c].size()!=24)return 4;}
 const long W=531441;long id;
 while(scanf("%ld",&id)==1){
  int c=id/W;long v=id%W;int dig[12];for(int i=11;i>=0;i--){dig[i]=v%3;v/=3;}
  vector<int> pts;array<int,243> cnt{};
  auto addp=[&](int p)->bool{bool ok=true;for(int q:pts){if(++cnt[sub(p,q)]>60)ok=false;if(++cnt[sub(q,p)]>60)ok=false;}pts.push_back(p);return ok;};
  auto undo=[&](size_t n){while(pts.size()>n){int p=pts.back();pts.pop_back();for(int q:pts){--cnt[sub(p,q)];--cnt[sub(q,p)];}}};
  auto addset=[&](const vector<int>&s)->bool{bool ok=true;for(int p:s)ok&=addp(p);return ok;};
  addset(S);bool valid=true;
  for(int d=0;d<12&&valid;d++)valid=addset(opt[c][d][dig[d]]);
  long nodes=0,sols=0;
  if(valid){nodes=1;
   // recursive DFS over positions 12..23
   vector<size_t> mark(25);
   function<void(int)> dfs=[&](int d){
    if(d==24){if(pts.size()!=121){fprintf(stderr,"size\n");exit(5);}
     for(int g=1;g<243;g++)if(cnt[g]!=60){fprintf(stderr,"leaf\n");exit(6);}sols++;return;}
    for(int a=0;a<3;a++){size_t n=pts.size();if(addset(opt[c][d][a])){nodes++;dfs(d+1);}undo(n);}
   };
   dfs(12);
  }
  printf("%ld %d %ld %ld\n",id,valid?1:0,nodes,sols);
 }
}
