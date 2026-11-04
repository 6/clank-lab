/* Checker B: independent re-implementation (C). Reads witness files ("v: out-neighbours" lines,
   '#' comments) and/or builds the family F(n-4,4) for a range of n, then checks
   - the Nash-Williams hypothesis in its counting form: for 1 <= i < n/2,
       (i)  #{v : d+(v) <= i} <= i-1   or   #{v : d-(v) >= n-i} >= i+1,
       (ii) #{v : d-(v) <= i} <= i-1   or   #{v : d+(v) >= n-i} >= i+1,
     which is equivalent to the sorted-sequence form (d_i >= i+1 iff fewer than i entries are <= i;
     d_{n-i} >= n-i iff at least i+1 entries are >= n-i);
   - strong connectivity by Warshall transitive closure;
   - non-Hamiltonicity by depth-first backtracking over simple paths from vertex 0.
   Usage: check_b [files...] [-f NMIN NMAX]. Exit 0 iff every input is a counterexample. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define MAXN 40
static int n, A[MAXN][MAXN];
static int count_le(int *deg, int x){int c=0; for(int v=0;v<n;v++) if(deg[v]<=x) c++; return c;}
static int count_ge(int *deg, int x){int c=0; for(int v=0;v<n;v++) if(deg[v]>=x) c++; return c;}
static int hypothesis(void){
  int dout[MAXN]={0}, din[MAXN]={0};
  for(int u=0;u<n;u++) for(int v=0;v<n;v++) if(A[u][v]){dout[u]++; din[v]++;}
  for(int i=1;2*i<n;i++){
    if(!(count_le(dout,i)<=i-1 || count_ge(din,n-i)>=i+1)) return 0;
    if(!(count_le(din,i)<=i-1 || count_ge(dout,n-i)>=i+1)) return 0;
  }
  return 1;
}
static int strong(void){
  static int R[MAXN][MAXN];
  for(int u=0;u<n;u++) for(int v=0;v<n;v++) R[u][v]=(u==v)||A[u][v];
  for(int k=0;k<n;k++) for(int u=0;u<n;u++) if(R[u][k]) for(int v=0;v<n;v++) if(R[k][v]) R[u][v]=1;
  for(int u=0;u<n;u++) for(int v=0;v<n;v++) if(!R[u][v]) return 0;
  return 1;
}
static int used[MAXN];
static int dfs(int v,int depth){
  if(depth==n) return A[v][0];
  for(int w=0;w<n;w++) if(A[v][w] && !used[w]){ used[w]=1; if(dfs(w,depth+1)) return 1; used[w]=0; }
  return 0;
}
static int hamiltonian(void){ memset(used,0,sizeof used); used[0]=1; return dfs(0,1); }
static int load(const char *path){
  FILE *f=fopen(path,"r"); if(!f){perror(path); return 0;}
  char line[1024]; int maxv=-1; memset(A,0,sizeof A); int seen[MAXN]={0};
  while(fgets(line,sizeof line,f)){
    char *h=strchr(line,'#'); if(h) *h=0;
    char *c=strchr(line,':'); if(!c) continue;
    *c=0; int v=atoi(line); if(v<0||v>=MAXN||seen[v]){fclose(f); return 0;} seen[v]=1; if(v>maxv) maxv=v;
    char *p=c+1; char *tok;
    while((tok=strtok(p," \t\r\n"))){ p=NULL; int w=atoi(tok); if(w<0||w>=MAXN||w==v||A[v][w]){fclose(f); return 0;} A[v][w]=1; if(w>maxv) maxv=w; }
  }
  fclose(f); n=maxv+1; for(int v=0;v<n;v++) if(!seen[v]) return 0; return 1;
}
static void build_family(int u){ /* F(u,4): U={0..u-1}, w=0, s=u, t=u+1, R={u+2,u+3} */
  n=u+4; memset(A,0,sizeof A);
  for(int x=0;x<u;x++) for(int y=0;y<n;y++) if(x!=y) A[x][y]=1;
  int L[3]={u+1,u+2,u+3};
  for(int a=0;a<3;a++) for(int b=0;b<3;b++) if(a!=b) A[L[a]][L[b]]=1;
  A[u][u+1]=1; A[u][0]=1; A[u+1][0]=1;
}
static int judge(const char *name){
  int h=hypothesis(), s=strong(), ham=hamiltonian();
  int ok = n>=3 && h && s && !ham;
  printf("%s n=%d NW=%d strong=%d hamiltonian=%d -> %s\n",name,n,h,s,ham,ok?"COUNTEREXAMPLE":"FAIL");
  return ok;
}
int main(int argc,char **argv){
  int good=1;
  for(int i=1;i<argc;i++){
    if(!strcmp(argv[i],"-f") && i+2<argc){ int a=atoi(argv[i+1]), b=atoi(argv[i+2]); i+=2;
      for(int m=a;m<=b;m++){ char nm[32]; build_family(m-4); sprintf(nm,"F(%d,4)",m-4); good&=judge(nm);} }
    else { if(!load(argv[i])){ printf("%s malformed -> FAIL\n",argv[i]); good=0; continue;} good&=judge(argv[i]); }
  }
  puts(good?"PASS":"REJECT"); return good?0:1;
}
