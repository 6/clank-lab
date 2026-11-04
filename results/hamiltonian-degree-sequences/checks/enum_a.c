/* Exhaustive enumerator A: every labelled digraph on n vertices (no loops; each unordered pair in one
   of 4 states: none, i->j, j->i, both). Sorted-degree-sequence form of the hypotheses, Held-Karp
   Hamiltonicity, reachability closure for strong connectivity.
   Prints: n, digraphs, NW-hypothesis count, NW counterexamples (strong, (i),(ii), not Hamiltonian),
   KOT-Conjecture-6 counterexamples ((i),(ii),(iii) for even n, not Hamiltonian). Usage: enum_a n */
#include <stdio.h>
#include <stdlib.h>
static int n, out[8];
static int cmp(const void *a, const void *b){ return *(const int*)a - *(const int*)b; }
static void seqs(int *dp, int *dm){
  for(int v=0;v<n;v++){ dp[v]=__builtin_popcount(out[v]); dm[v]=0; }
  for(int u=0;u<n;u++) for(int v=0;v<n;v++) if(out[u]>>v&1) dm[v]++;
  qsort(dp,n,sizeof(int),cmp); qsort(dm,n,sizeof(int),cmp);
}
static int nw(const int *dp, const int *dm){ /* d_i is dp[i-1] */
  for(int i=1;2*i<n;i++){
    if(!(dp[i-1]>=i+1 || dm[n-i-1]>=n-i)) return 0;
    if(!(dm[i-1]>=i+1 || dp[n-i-1]>=n-i)) return 0;
  }
  return 1;
}
static int cond3(const int *dp, const int *dm){ return n%2 ? 1 : (dp[n/2-1]>=n/2 || dm[n/2-1]>=n/2); }
static int strong(void){
  int in[8]={0}; for(int u=0;u<n;u++) for(int v=0;v<n;v++) if(out[u]>>v&1) in[v]|=1<<u;
  int R=1,F=1;
  for(int it=0;it<n;it++){ int r=R,f=F; for(int u=0;u<n;u++){ if(R>>u&1) r|=out[u]; if(F>>u&1) f|=in[u]; } R=r; F=f; }
  return R==(1<<n)-1 && F==(1<<n)-1;
}
static int ham(void){
  static int dp[1<<8];
  for(int S=0;S<(1<<n);S++) dp[S]=0;
  dp[1]=1;
  for(int S=1;S<(1<<n);S+=2) if(dp[S]) for(int v=0;v<n;v++) if(dp[S]>>v&1){
    int T=out[v]&~S; while(T){ int w=__builtin_ctz(T); T&=T-1; dp[S|1<<w]|=1<<w; } }
  for(int v=0;v<n;v++) if((dp[(1<<n)-1]>>v&1) && (out[v]&1)) return 1;
  return 0;
}
int main(int argc, char **argv){
  n=atoi(argv[1]); if(n<3||n>7) return 2;
  int P=n*(n-1)/2, pu[32], pv[32], k=0;
  for(int i=0;i<n;i++) for(int j=i+1;j<n;j++){ pu[k]=i; pv[k]=j; k++; }
  long total=0, hyp=0, nwce=0, kotce=0;
  for(long code=0; code < (1L<<(2*P)); code++){
    for(int v=0;v<n;v++) out[v]=0;
    long c=code;
    for(int p=0;p<P;p++){ int s=c&3; c>>=2; if(s&1) out[pu[p]]|=1<<pv[p]; if(s&2) out[pv[p]]|=1<<pu[p]; }
    total++;
    int dp[8], dm[8]; seqs(dp,dm);
    if(!nw(dp,dm)) continue;
    hyp++;
    int h=-1;
    if(strong()){ h=ham(); if(!h) nwce++; }
    if(cond3(dp,dm)){ if(h<0) h=ham(); if(!h) kotce++; }
  }
  printf("n=%d digraphs=%ld nw_hypothesis=%ld nw_counterexamples=%ld kot6_counterexamples=%ld\n",n,total,hyp,nwce,kotce);
  return 0;
}
