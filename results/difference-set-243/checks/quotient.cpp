// Second, independent quotient enumeration: assign r in {0,3,6,9} to the 24 nonspecial cells of Q=C3^3
// (special cells fixed 4,3,6) and keep r iff for each of the 13 index-3 subgroups the coset counts are
// a permutation of (36,40,45); then filter autocorrelation (601 at 0, 540 elsewhere). No line-sum identity used.
#include <cstdio>
#include <vector>
#include <algorithm>
using namespace std;
int F[13][3]; int nf=0; int cosetOf[13][27]; int r[27]; vector<int> order; long long found=0,ac_ok=0; FILE* out;
int sums[13][3]; int remcap[13][3];
bool feasible(){ for(int f=0;f<nf;f++){ for(int j=0;j<3;j++){ if(sums[f][j]>45) return false; if(sums[f][j]+remcap[f][j]<36) return false; } } return true; }
void go(int k){
  if(k==(int)order.size()){
    for(int f=0;f<nf;f++){int a[3]={sums[f][0],sums[f][1],sums[f][2]}; sort(a,a+3); if(!(a[0]==36&&a[1]==40&&a[2]==45))return;}
    found++;
    // autocorrelation
    bool ok=true;
    for(int d=0;d<27&&ok;d++){int s=0; for(int p=0;p<27;p++){int q=9*((p/9+d/9)%3)+3*((p/3%3+d/3%3)%3)+((p%3+d%3)%3); s+=r[p]*r[q];} if(s!=(d==0?601:540)) ok=false;}
    if(ok){ac_ok++; for(int i=0;i<27;i++)fprintf(out,"%d%c",r[i],i==26?'\n':' ');}
    return; }
  int c=order[k];
  for(int f=0;f<nf;f++) remcap[f][cosetOf[f][c]]-=9;
  for(int v=0;v<=9;v+=3){ r[c]=v; for(int f=0;f<nf;f++) sums[f][cosetOf[f][c]]+=v;
    if(feasible()) go(k+1);
    for(int f=0;f<nf;f++) sums[f][cosetOf[f][c]]-=v; }
  for(int f=0;f<nf;f++) remcap[f][cosetOf[f][c]]+=9;
  r[c]=0;
}
int main(){
  out=fopen("qdfs_images.txt","w");
  for(int a=0;a<3;a++)for(int b=0;b<3;b++)for(int c=0;c<3;c++){ if(a==0&&b==0&&c==0)continue; int first=a?a:(b?b:c); if(first!=1)continue; F[nf][0]=a;F[nf][1]=b;F[nf][2]=c; nf++; }
  for(int f=0;f<nf;f++)for(int p=0;p<27;p++) cosetOf[f][p]=(F[f][0]*(p/9)+F[f][1]*(p/3%3)+F[f][2]*(p%3))%3;
  r[0]=4;r[9]=3;r[18]=6;
  for(int f=0;f<nf;f++)for(int j=0;j<3;j++){sums[f][j]=0;remcap[f][j]=0;}
  for(int p=0;p<27;p++){ if(p==0||p==9||p==18){ for(int f=0;f<nf;f++) sums[f][cosetOf[f][p]]+=r[p]; } else { order.push_back(p); for(int f=0;f<nf;f++) remcap[f][cosetOf[f][p]]+=9; } }
  go(0);
  printf("forms=%d line-count solutions=%lld autocorrelation-passing=%lld\n",nf,found,ac_ok); fclose(out);
}
