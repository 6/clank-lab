// Independent pruning-certificate checker. Input (stdin): 16 ints B (row-major), M, then M records of 20 ints (simplex pts) + 4 ints (apex).
#include <bits/stdc++.h>
using namespace std;
typedef long long ll; typedef __int128 LL;
typedef array<int,4> P4;
static ll det3(ll a[3][3]){return a[0][0]*(a[1][1]*a[2][2]-a[1][2]*a[2][1])-a[0][1]*(a[1][0]*a[2][2]-a[1][2]*a[2][0])+a[0][2]*(a[1][0]*a[2][1]-a[1][1]*a[2][0]);}
static ll det4(ll m[4][4]){ll r=0;for(int c=0;c<4;c++){ll s[3][3];for(int i=1;i<4;i++){int cc=0;for(int j=0;j<4;j++)if(j!=c)s[i-1][cc++]=m[i][j];}r+=((c&1)?-1:1)*m[0][c]*det3(s);}return r;}
ll B[4][4],adjB[4][4],D;
vector<P4> pts;
ll detPts(const array<int,5>&s){ll m[4][4];for(int i=0;i<4;i++)for(int j=0;j<4;j++)m[i][j]=pts[s[i+1]][j]-pts[s[0]][j];return det4(m);}
ll detFW(const array<int,4>&f,int w){ll m[4][4];for(int i=0;i<3;i++)for(int j=0;j<4;j++)m[i][j]=pts[f[i+1]][j]-pts[f[0]][j];for(int j=0;j<4;j++)m[3][j]=pts[w][j]-pts[f[0]][j];return det4(m);}
int main(){
  for(int i=0;i<4;i++)for(int j=0;j<4;j++)scanf("%lld",&B[i][j]);
  D=det4(B); if(D==0){puts("REJECT singular");return 1;}
  // adjugate: adj*B = D*I (cofactors)
  for(int i=0;i<4;i++)for(int j=0;j<4;j++){ll s[3][3];int r=0;for(int a=0;a<4;a++){if(a==j)continue;int c=0;for(int b=0;b<4;b++){if(b==i)continue;s[r][c++]=B[a][b];}r++;}adjB[i][j]=(((i+j)&1)?-1:1)*det3(s);}
  ll d=D; if(d<0){d=-d;for(auto&r:adjB)for(auto&x:r)x=-x;}
  // sanity adj*B = d I
  for(int i=0;i<4;i++)for(int j=0;j<4;j++){ll s=0;for(int k=0;k<4;k++)s+=adjB[i][k]*B[k][j];if(s!=(i==j?d:0)){puts("adj bug");return 2;}}
  int lo[4]={0,0,0,0},hi[4]={0,0,0,0};
  for(int m=0;m<16;m++)for(int i=0;i<4;i++){int s=0;for(int j=0;j<4;j++)if(m>>j&1)s+=B[i][j];lo[i]=min(lo[i],s);hi[i]=max(hi[i],s);}
  auto Y=[&](const P4&x,ll*y){for(int i=0;i<4;i++){y[i]=0;for(int k=0;k<4;k++)y[i]+=adjB[i][k]*x[k];}};
  for(int a=lo[0];a<=hi[0];a++)for(int b=lo[1];b<=hi[1];b++)for(int c=lo[2];c<=hi[2];c++)for(int e=lo[3];e<=hi[3];e++){P4 x={a,b,c,e};ll y[4];Y(x,y);bool ok=1;for(int i=0;i<4;i++)if(y[i]<0||y[i]>d)ok=0;if(ok)pts.push_back(x);}
  int N=pts.size(); map<P4,int> idx; for(int i=0;i<N;i++)idx[pts[i]]=i;
  vector<array<ll,4>> Yv(N); for(int i=0;i<N;i++)Y(pts[i],Yv[i].data());
  // enumerate unimodular simplices
  map<array<int,5>,int> sid; ll cnt=0;
  for(int a=0;a<N;a++)for(int b=a+1;b<N;b++)for(int c=b+1;c<N;c++)for(int e=c+1;e<N;e++)for(int f=e+1;f<N;f++){array<int,5> s={a,b,c,e,f};ll dt=detPts(s);if(dt==1||dt==-1){sid[s]=cnt++;}}
  printf("det=%lld points=%d unimodular_simplices=%lld\n",d,N,cnt);
  int M; scanf("%d",&M);
  vector<array<int,5>> S(M); vector<int> ap(M); vector<char> seen(cnt,0); vector<int> pos(cnt,-1);
  int bad=0;
  for(int m=0;m<M;m++){
    array<int,5> s; bool ok=1;
    for(int i=0;i<5;i++){P4 x;for(int j=0;j<4;j++)scanf("%d",&x[j]);auto it=idx.find(x);if(it==idx.end()){ok=0;s[i]=0;}else s[i]=it->second;}
    P4 a;for(int j=0;j<4;j++)scanf("%d",&a[j]);
    auto ia=idx.find(a); ap[m]=ia==idx.end()?-1:ia->second;
    if(!ok){printf("REJECT entry %d: point not in P(B)\n",m);return 1;}
    sort(s.begin(),s.end()); S[m]=s;
    auto it=sid.find(s); if(it==sid.end()){printf("REJECT entry %d: not a unimodular simplex of P(B) (or repeated vertex)\n",m);return 1;}
    if(find(s.begin(),s.end(),ap[m])==s.end()){printf("REJECT entry %d: apex not a vertex\n",m);return 1;}
    if(seen[it->second]){printf("REJECT entry %d: duplicate\n",m);return 1;}
    seen[it->second]=1; pos[it->second]=m;
  }
  if((ll)M!=cnt){printf("REJECT: %d deletions but %lld simplices\n",M,cnt);return 1;}
  // (1) holds: M distinct valid simplices = cnt
  for(int m=0;m<M&&!bad;m++){
    array<int,4> F;int k=0;for(int v:S[m])if(v!=ap[m])F[k++]=v;
    for(int i=0;i<4;i++){bool z=1,o=1;for(int v:F){if(Yv[v][i]!=0)z=0;if(Yv[v][i]!=d)o=0;}if(z||o){printf("REJECT entry %d: facet lies in boundary facet of P(B)\n",m);return 1;}}
    ll sa=detFW(F,ap[m]); int sga=sa>0?1:-1;
    for(int w=0;w<N;w++){
      if(find(F.begin(),F.end(),w)!=F.end()||w==ap[m])continue;
      ll dw=detFW(F,w); if(dw==0)continue; int sgw=dw>0?1:-1; if(sgw==sga)continue;
      if(dw!=1&&dw!=-1)continue; // F+w not unimodular
      array<int,5> t={F[0],F[1],F[2],F[3],w}; sort(t.begin(),t.end());
      auto it=sid.find(t); if(it==sid.end()){puts("internal inconsistency");return 2;}
      if(pos[it->second]>=m){printf("REJECT entry %d: opposite simplex at position %d not earlier\n",m,pos[it->second]);return 1;}
    }
  }
  puts("ACCEPT"); return 0;
}
