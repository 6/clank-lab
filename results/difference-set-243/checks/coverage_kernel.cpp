#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <fstream>
#include <filesystem>
#include <iostream>
#include <vector>
#include <omp.h>
using namespace std;
int main(int argc,char**argv){
 vector<string> args;int requested=2;
 for(int k=0;k<argc;k++){
  if(string(argv[k])=="--threads"){
   if(k+1>=argc)return 2;
   requested=stoi(argv[++k]);
  }else args.push_back(argv[k]);
 }
 if(args.size()<3 || requested<1)return 2;
 int count=args.size();string mode=args[1];
 omp_set_dynamic(0);omp_set_num_threads(requested);
 if(mode=="singleton"){
  bool smoke=count>3; vector<array<int,3>> layers;
  for(int a=0;a<=9;a++)for(int b=0;b<=9;b++)for(int c=0;c<=9;c++)
   if(a+b+c==13 && (a*a+b*b+c*c)%9==7){
    vector<int> residues={a%3,b%3,c%3};sort(residues.begin(),residues.end());
    if(residues==vector<int>{0,0,1})layers.push_back({a,b,c});
   }
  vector<int> masks[10];for(int m=0;m<512;m++)masks[popcount((unsigned)m)].push_back(m);
  int shifts[9][512];for(int h=0;h<9;h++)for(int m=0;m<512;m++){
   int r=0;for(int p=0;p<9;p++)if(m>>p&1)r|=1<<(((p/3+h/3)%3)*3+(p%3+h%3)%3);shifts[h][m]=r;
  }
  vector<array<int,3>> jobs;
  for(auto abc:layers)for(int a:masks[abc[0]])jobs.push_back({a,abc[1],abc[2]});
  vector<vector<uint32_t>> passes(requested);uint64_t tested=0;int threads=0;
  #pragma omp parallel reduction(+:tested)
  {
   int tid=omp_get_thread_num();
   #pragma omp single
   threads=omp_get_num_threads();
   #pragma omp for schedule(dynamic,1)
   for(size_t l=0;l<jobs.size();l++){
    auto job=jobs[l];int a=job[0],local=0;
    for(int b:masks[job[1]])for(int c:masks[job[2]]){
     if(smoke && local++>=10)continue;
     tested++;int v[3]={a,b,c};bool ok=true;
     for(int hx=0;hx<3 && ok;hx++)for(int h=0;h<9 && ok;h++)if(hx||h){
      int n=0;for(int x=0;x<3;x++)n+=popcount((unsigned)(v[x]&shifts[h][v[(x+3-hx)%3]]));
      if(n%3)ok=false;
     }
     if(ok)passes[tid].push_back(a|(b<<9)|(c<<18));
    }
   }
  }
  vector<uint32_t> all;for(auto&v:passes)all.insert(all.end(),v.begin(),v.end());sort(all.begin(),all.end());
  if(threads!=requested)return 1;
  ofstream out(args[2]);for(auto m:all)out<<m<<'\n';
  cout<<"{\"mode\":\"singleton\",\"smoke\":"<<(smoke?"true":"false")<<",\"threads\":"<<threads<<",\"layer_triples\":"<<layers.size()<<",\"tested\":"<<tested<<",\"passing\":"<<all.size()<<"}\n";
 }else if(mode=="prefix"){
  if(count<5)return 2;
  int cases=stoi(args[4]),base=1;for(int k=0;k<12;k++)base*=3;
  int total=cases*base,limit=count>5?stoi(args[5]):total;
  if(cases<1 || cases>256 || limit<1 || limit>total)return 2;
  vector<string> errors(requested);int actual_threads=0;
  string paths[2],outputs[2];
  for(int j=0;j<2;j++){
   string mode_name=j?"direct":"fast";
   paths[j]=args[2]+"/"+mode_name+"-prefixes.bin";
   outputs[j]=args[3]+"/derived-"+mode_name+"-prefixes.bin";
   if(limit==total && filesystem::file_size(paths[j])!=uint64_t(total)*17){cerr<<"wrong actual prefix byte length "<<mode_name<<"\n";return 1;}
   ofstream out(outputs[j],ios::binary);out.seekp(uint64_t(limit)*17-1);out.put(0);
   if(!out)return 1;
  }
  #pragma omp parallel
  {
   int tid=omp_get_thread_num(),nt=omp_get_num_threads();
   #pragma omp single
   actual_threads=nt;
   int begin=int(uint64_t(limit)*tid/nt),end=int(uint64_t(limit)*(tid+1)/nt);
   ifstream in[2];fstream derived[2];
   for(int j=0;j<2;j++){
    in[j].open(paths[j],ios::binary);in[j].seekg(uint64_t(begin)*17);
    derived[j].open(outputs[j],ios::binary|ios::in|ios::out);derived[j].seekp(uint64_t(begin)*17);
   }
   uint64_t previous=uint64_t(begin%base)*base;
   for(int id=begin;id<end;id++){
    array<unsigned char,17> want{};for(int k=0;k<4;k++)want[k]=(uint32_t(id)>>(8*k))&255;
    int cs=id/base,n=id%base;want[4]=cs;for(int k=16;k>=5;k--){want[k]=n%3;n/=3;}
    uint64_t rank=0;for(int k=5;k<17;k++)rank=rank*3+want[k];
    if(id%base==0)previous=0;
    uint64_t lo=rank*base,hi=(rank+1)*base;
    if(lo!=previous || (id%base==base-1 && hi!=uint64_t(base)*base)){errors[tid]="cylinder gap";break;}
    previous=hi;
    if(uint64_t(cs)*base+rank!=unsigned(id)){errors[tid]="rank inverse";break;}
    for(int j=0;j<2;j++){
     array<unsigned char,17> got{};
     derived[j].write((char*)want.data(),17);in[j].read((char*)got.data(),17);
     if(!derived[j] || in[j].gcount()!=17 || got!=want){errors[tid]="missing/mismatched decoder witness ID="+to_string(id)+" mode="+(j?"direct":"fast");break;}
    }
    if(!errors[tid].empty())break;
   }
  }
  if(actual_threads!=requested){cerr<<"requested thread count unavailable\n";return 1;}
  for(auto error:errors)if(!error.empty()){cerr<<error<<"\n";return 1;}
  for(int j=0;j<2;j++)cout<<(j?"direct":"fast")<<" records="<<limit<<" result=MATCH\n";
  cout<<"threads="<<actual_threads<<"\n";
 }else return 2;
}
