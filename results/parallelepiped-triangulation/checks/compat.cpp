// Pairwise "proper intersection" test for lattice simplices via circuits.
// Two full-dim simplices A,B (vertex sets of a point set) intersect properly iff no circuit (Z+,Z-) of A∪B has Z+⊆A and Z-⊆B (or reverse).
#include <bits/stdc++.h>
using namespace std;
typedef long long ll;
int NP; vector<array<int,4>> P; vector<array<int,5>> S;
static ll detn(vector<vector<ll>> M){ // Bareiss, exact
  int n=M.size(); if(!n) return 1; ll sign=1, prev=1;
  for(int i=0;i<n-1;i++){
    if(M[i][i]==0){int r=-1;for(int k=i+1;k<n;k++)if(M[k][i]!=0){r=k;break;} if(r<0)return 0; swap(M[i],M[r]); sign=-sign;}
    for(int j=i+1;j<n;j++)for(int k=i+1;k<n;k++) M[j][k]=(M[j][k]*M[i][i]-M[j][i]*M[i][k])/prev;
    prev=M[i][i];
  }
  return sign*M[n-1][n-1];
}
// returns true if the subset (point indices) is a circuit; fills v (kernel vector, nonzero everywhere)
static bool circuit(const vector<int>& s, vector<ll>& v){
  int k=s.size(); // matrix 5 x k : rows coord0..3, ones
  auto ent=[&](int r,int c)->ll{ return r<4? P[s[c]][r] : 1; };
  int m=k-1; // choose m rows out of 5
  for(int mask=0;mask<32;mask++){ if(__builtin_popcount(mask)!=m) continue;
    vector<int> rows; for(int r=0;r<5;r++) if(mask>>r&1) rows.push_back(r);
    vector<ll> w(k); bool nz=false;
    for(int j=0;j<k;j++){
      vector<vector<ll>> M(m,vector<ll>(m));
      for(int a=0;a<m;a++){int cc=0;for(int c=0;c<k;c++){if(c==j)continue;M[a][cc++]=ent(rows[a],c);}}
      w[j]=((j&1)?-1:1)*detn(M); if(w[j]) nz=true;
    }
    if(!nz) continue;
    // check in kernel of all rows
    for(int r=0;r<5;r++){ ll t=0; for(int c=0;c<k;c++) t+=ent(r,c)*w[c]; if(t) return false; }
    for(int j=0;j<k;j++) if(!w[j]) return false;
    v=w; return true;
  }
  return false;
}
static bool incompatible(int a,int b){
  auto &A=S[a]; auto &B=S[b];
  auto inA=[&](int p){for(int x:A)if(x==p)return true;return false;};
  auto inB=[&](int p){for(int x:B)if(x==p)return true;return false;};
  vector<int> U(A.begin(),A.end()); for(int x:B) if(!inA(x)) U.push_back(x);
  int m=U.size();
  for(int mask=1;mask<(1<<m);mask++){
    int k=__builtin_popcount(mask); if(k<3||k>6) continue;
    vector<int> s; for(int i=0;i<m;i++) if(mask>>i&1) s.push_back(U[i]);
    vector<ll> v; if(!circuit(s,v)) continue;
    for(int sg=-1;sg<=1;sg+=2){ bool ok=true;
      for(int i=0;i<k&&ok;i++){ ll c=v[i]*sg; if(c>0 && !inA(s[i])) ok=false; if(c<0 && !inB(s[i])) ok=false; }
      if(ok) return true; }
  }
  return false;
}
int main(int argc,char**argv){
  scanf("%d",&NP); P.resize(NP); for(auto&p:P) for(int i=0;i<4;i++) scanf("%d",&p[i]);
  int ns; scanf("%d",&ns); S.resize(ns); for(auto&s:S) for(int i=0;i<5;i++) scanf("%d",&s[i]);
  vector<vector<pair<int,int>>> out(ns);
  #pragma omp parallel for schedule(dynamic,8)
  for(int a=0;a<ns;a++) for(int b=a+1;b<ns;b++) if(incompatible(a,b)) out[a].push_back({a,b});
  size_t tot=0; for(auto&o:out){ for(auto&pr:o) printf("%d %d\n",pr.first,pr.second); tot+=o.size(); }
  fprintf(stderr,"simplices %d incompatible pairs %zu\n",ns,tot);
}
