// Positive discovery control: all x3-invariant (121,40,13)
// difference sets in Z121 (unions of 8 of the 24 nonzero x3-orbits); prints them.
#include <cstdio>
#include <vector>
using namespace std;
int main(){vector<vector<int>> orb;vector<int> seen(121);
 for(int e=1;e<121;e++)if(!seen[e]){vector<int> o;int x=e;do{o.push_back(x);seen[x]=1;x=x*3%121;}while(x!=e);orb.push_back(o);}
 int n=orb.size();long cnt=0;
 for(unsigned m=0;m<(1u<<n);m++){if(__builtin_popcount(m)!=8)continue;vector<int> s;for(int j=0;j<n;j++)if(m>>j&1)for(int x:orb[j])s.push_back(x);
  int c[121]={0};bool ok=true;for(int a:s)for(int b:s)if(a!=b)c[(a-b+121)%121]++;
  for(int g=1;g<121;g++)if(c[g]!=13){ok=false;break;}
  if(ok){cnt++;for(int x:s)printf("%d ",x);printf("\n");}}
 fprintf(stderr,"orbits=%d fixed_DS=%ld\n",n,cnt);}
