/* Exhaustive enumerator B (independent of A): every labelled digraph on n vertices as an n(n-1)-bit
   adjacency word over ordered pairs (u,v), u != v. Counting form of the hypotheses
   (d_i >= i+1 iff #{v: d(v) <= i} <= i-1; d_{n-i} >= n-i iff #{v: d(v) >= n-i} >= i+1),
   Warshall closure for strong connectivity, depth-first backtracking for Hamiltonicity.
   Same output fields as enumerator A. Usage: enum_b n */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static int n, A[8][8];
static int le(const int *d,int x){ int c=0; for(int v=0;v<n;v++) c += d[v]<=x; return c; }
static int ge(const int *d,int x){ int c=0; for(int v=0;v<n;v++) c += d[v]>=x; return c; }
static int used[8];
static int dfs(int v,int depth){
  if(depth==n) return A[v][0];
  for(int w=1;w<n;w++) if(A[v][w] && !used[w]){ used[w]=1; if(dfs(w,depth+1)) return 1; used[w]=0; }
  return 0;
}
static int hamiltonian(void){ memset(used,0,sizeof used); used[0]=1; return dfs(0,1); }
static int strong(void){
  int R[8][8];
  for(int u=0;u<n;u++) for(int v=0;v<n;v++) R[u][v] = (u==v) || A[u][v];
  for(int k=0;k<n;k++) for(int u=0;u<n;u++) if(R[u][k]) for(int v=0;v<n;v++) if(R[k][v]) R[u][v]=1;
  for(int u=0;u<n;u++) for(int v=0;v<n;v++) if(!R[u][v]) return 0;
  return 1;
}
int main(int argc,char **argv){
  n=atoi(argv[1]); if(n<3||n>7) return 2;
  int pu[64], pv[64], m=0;
  for(int u=0;u<n;u++) for(int v=0;v<n;v++) if(u!=v){ pu[m]=u; pv[m]=v; m++; }
  long total=0, hyp=0, nwce=0, kotce=0;
  for(unsigned long w=0; w < (1UL<<m); w++){
    memset(A,0,sizeof A);
    for(int b=0;b<m;b++) if(w>>b&1) A[pu[b]][pv[b]]=1;
    total++;
    int dout[8]={0}, din[8]={0};
    for(int u=0;u<n;u++) for(int v=0;v<n;v++) if(A[u][v]){ dout[u]++; din[v]++; }
    int ok=1;
    for(int i=1;2*i<n && ok;i++){
      if(!(le(dout,i)<=i-1 || ge(din,n-i)>=i+1)) ok=0;
      if(!(le(din,i)<=i-1 || ge(dout,n-i)>=i+1)) ok=0;
    }
    if(!ok) continue;
    hyp++;
    int c3 = (n%2) ? 1 : (le(dout,n/2-1)<=n/2-1 || le(din,n/2-1)<=n/2-1); /* d_{n/2} >= n/2 */
    int h = hamiltonian();
    if(!h && strong()) nwce++;
    if(!h && c3) kotce++;
  }
  printf("n=%d digraphs=%ld nw_hypothesis=%ld nw_counterexamples=%ld kot6_counterexamples=%ld\n",n,total,hyp,nwce,kotce);
  return 0;
}
