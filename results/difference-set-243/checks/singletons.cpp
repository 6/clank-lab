// Independent singleton enumeration: all 13-subsets S of H=C3^3 (bit 9x+3u+w)
// with layer counts satisfying the moment congruences and |S∩(S+h)|≡0 mod 3,
// then orbit of mask 24909666 under x->a x+t0, (u,w)->B(u,w)+(d,g)x+(t1,t2).
#include <cstdio>
#include <vector>
#include <set>
#include <cstdint>
#include <algorithm>
using namespace std;
int addp(int p,int q){int x=(p/9+q/9)%3,u=(p/3%3+q/3%3)%3,w=(p%3+q%3)%3;return 9*x+3*u+w;}
int main(){
  int add[27][27]; for(int p=0;p<27;p++)for(int q=0;q<27;q++)add[p][q]=addp(p,q);
  vector<uint32_t> pass; long long tested=0, layerok=0;
  for(uint32_t m=0;m<(1u<<27);m++){ if(__builtin_popcount(m)!=13)continue; tested++;
    int L[3]={__builtin_popcount(m&0x1FF),__builtin_popcount((m>>9)&0x1FF),__builtin_popcount((m>>18)&0x1FF)};
    if((L[0]*L[0]+L[1]*L[1]+L[2]*L[2])%9!=7)continue;
    int r[3]={L[0]%3,L[1]%3,L[2]%3}; int ones=0,zeros=0; for(int i=0;i<3;i++){if(r[i]==1)ones++; if(r[i]==0)zeros++;}
    if(!(ones==1&&zeros==2))continue; layerok++;
    bool ok=true;
    for(int h=1;h<27&&ok;h++){int c=0; for(int p=0;p<27;p++) if((m>>p&1)&&(m>>add[p][h]&1))c++; if(c%3)ok=false;}
    if(ok)pass.push_back(m);
  }
  printf("tested13=%lld layer_ok=%lld pass=%zu\n",tested,layerok,pass.size());
  // layer-count multiset of passing
  set<vector<int>> lc; for(auto m:pass){vector<int>v={__builtin_popcount(m&0x1FF),__builtin_popcount((m>>9)&0x1FF),__builtin_popcount((m>>18)&0x1FF)};lc.insert(v);} 
  for(auto&v:lc)printf("layers %d %d %d\n",v[0],v[1],v[2]);
  // group maps
  set<uint32_t> orb; uint32_t M0=24909666; long long nmaps=0, stab=0;
  for(int a=1;a<3;a++)for(int t0=0;t0<3;t0++)for(int B=0;B<81;B++){int b00=B%3,b01=B/3%3,b10=B/9%3,b11=B/27; if(((b00*b11-b01*b10)%3+3)%3==0)continue;
   for(int d=0;d<3;d++)for(int g=0;g<3;g++)for(int t1=0;t1<3;t1++)for(int t2=0;t2<3;t2++){nmaps++;
     uint32_t im=0; for(int p=0;p<27;p++) if(M0>>p&1){int x=p/9,u=p/3%3,w=p%3; int X=(a*x+t0)%3, U=(b00*u+b01*w+d*x+t1)%3, W=(b10*u+b11*w+g*x+t2)%3; im|=1u<<(9*X+3*U+W);} 
     orb.insert(im); if(im==M0){stab++; printf("stab a=%d t0=%d B=%d%d%d%d d=%d g=%d t=%d%d\n",a,t0,b00,b01,b10,b11,d,g,t1,t2);} }}
  set<uint32_t> ps(pass.begin(),pass.end());
  printf("maps=%lld orbit=%zu stab=%lld orbit==pass:%d mask_in_pass:%d\n",nmaps,orb.size(),stab,(int)(orb==ps),(int)ps.count(M0));
}
