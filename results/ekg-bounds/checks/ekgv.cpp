#include <algorithm>
#include <array>
#include <cassert>
#include <chrono>
#include <csignal>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <filesystem>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <limits>
#include <list>
#include <map>
#include <numeric>
#include <sstream>
#include <stdexcept>
#include <string>
#include <sys/resource.h>
#include <sys/file.h>
#include <fcntl.h>
#include <unistd.h>
#include <vector>
#include <unordered_map>
using U=uint64_t; namespace fs=std::filesystem;
static constexpr U OFF=14695981039346656037ULL, FP=1099511628211ULL;
#ifndef EKGV_PAGE_SHIFT
#define EKGV_PAGE_SHIFT 24
#endif
#ifndef EKGV_SEG_SHIFT
#define EKGV_SEG_SHIFT 20
#endif
#ifndef EKGV_CUT_SHIFT
#define EKGV_CUT_SHIFT 20
#endif
#ifndef EKGV_CURSOR_SHIFT
#define EKGV_CURSOR_SHIFT 18
#endif
static constexpr U PAGE=1ULL<<EKGV_PAGE_SHIFT, WORDS=PAGE/64, CUT=1ULL<<EKGV_CUT_SHIFT, SEG=1ULL<<EKGV_SEG_SHIFT;
static constexpr U CSIZE=1ULL<<EKGV_CURSOR_SHIFT;
static volatile sig_atomic_t stop_requested=0;
static void sigstop(int){stop_requested=1;}
static void require(bool b,const std::string&s){if(!b)throw std::runtime_error(s);}
static U add(U a,U b){require(a<=UINT64_MAX-b,"uint64 addition overflow");return a+b;}
static U mul(U a,U b){require(!b||a<=UINT64_MAX/b,"uint64 multiplication overflow");return a*b;}
static U number(const std::string&s){size_t p;U x=std::stoull(s,&p);require(p==s.size()&&!s.empty()&&s[0]!='-',"invalid unsigned integer");return x;}
static void syncpath(const fs::path&p,bool dir=false){int fd=open(p.c_str(),dir?O_RDONLY|O_DIRECTORY:O_RDONLY);require(fd>=0,"open for fsync: "+p.string());int e=fsync(fd);close(fd);require(e==0,"fsync failed");}
static std::string hex(U x){std::ostringstream s;s<<std::hex<<std::setfill('0')<<std::setw(16)<<x;return s.str();}
static void hash_value(U&h,U x,int bytes){for(int i=0;i<bytes;i++){h^=uint8_t(x);h*=FP;x>>=8;}}
// Immutable checkpoint directories and a replaceable live overlay keep page
// metadata on disk. No in-memory directory grows with the number of pages.
struct PageStore {
 fs::path dir;U base=0;
 explicit PageStore(fs::path d):dir(d){fs::create_directories(dir/"live");fs::create_directories(dir/"snap");}
 fs::path snapshot(U gen){return dir/"snap"/std::to_string(gen);}
 fs::path readpath(U id){auto name=std::to_string(id);auto live=dir/"live"/name;if(fs::exists(live))return live;if(base){auto p=snapshot(base)/name;if(fs::exists(p))return p;}return {};}
 void write(U id,const std::vector<U>&v,bool sparse){auto target=dir/"live"/std::to_string(id);auto tmp=dir/"live"/"write.tmp";std::ofstream f(tmp,std::ios::binary);require(bool(f),"create live page");if(sparse){for(uint32_t i=0;i<v.size();i++)if(v[i]){f.write((char*)&i,4);f.write((char*)&v[i],8);}}else f.write((char*)v.data(),v.size()*8);f.close();require(bool(f),"write live page");fs::rename(tmp,target);}
 void prepare(U gen,U discard_below=0){auto dest=snapshot(gen);require(!fs::exists(dest),"checkpoint generation exists");fs::create_directory(dest);if(base)for(auto&p:fs::directory_iterator(snapshot(base))){auto name=p.path().filename().string();U id=number(name);if(id<discard_below||fs::exists(dir/"live"/name))continue;fs::create_hard_link(p.path(),dest/name);}for(auto&p:fs::directory_iterator(dir/"live")){auto name=p.path().filename().string();if(name=="write.tmp")continue;U id=number(name);if(id>=discard_below)fs::create_hard_link(p.path(),dest/name);}for(auto&p:fs::directory_iterator(dest))syncpath(p.path());syncpath(dest,true);syncpath(dir/"snap",true);}
 void cleanup(){for(auto&p:fs::directory_iterator(dir/"snap"))if(!base||p.path().filename()!=std::to_string(base))fs::remove_all(p.path());for(auto&p:fs::directory_iterator(dir/"live"))fs::remove(p.path());}
 bool empty(){return fs::is_empty(dir/"live")&&fs::is_empty(dir/"snap");}
};
struct Bitmap {
 struct Entry {U tick=0;bool dirty=false;std::vector<U> v;};
 PageStore store;std::unordered_map<U,Entry> cache;U clock=0,low=1;size_t cap;
 Bitmap(fs::path d,size_t c):store(d),cap(c){require(cap>0,"cache capacity must be positive");}
 void persist(U id,Entry&e){if(e.dirty){store.write(id,e.v,false);e.dirty=false;}}
 Entry& page(U id){auto it=cache.find(id);if(it!=cache.end()){it->second.tick=++clock;return it->second;}if(cache.size()>=cap){auto old=std::min_element(cache.begin(),cache.end(),[](auto&a,auto&b){return a.second.tick<b.second.tick;});persist(old->first,old->second);cache.erase(old);}Entry e;e.tick=++clock;e.v.resize(WORDS);auto p=store.readpath(id);if(!p.empty()){std::ifstream in(p,std::ios::binary);in.read((char*)e.v.data(),PAGE/8);require(bool(in),"read bitmap page");}return cache.emplace(id,std::move(e)).first->second;}
 bool get(U x){if(x<low)return true;auto&e=page(x/PAGE);return (e.v[(x%PAGE)/64]>>(x%64))&1;}
 void set(U x){require(x>=low,"attempt to reuse verified prefix");auto&e=page(x/PAGE);U &w=e.v[(x%PAGE)/64],mask=1ULL<<(x%64);require(!(w&mask),"duplicate sequence value");w|=mask;e.dirty=true;}
 void advance(){while(get(low))low=add(low,1);}
 void prepare(U gen){for(auto&[id,e]:cache)if(id>=low/PAGE)persist(id,e);for(auto it=cache.begin();it!=cache.end();)if(it->first<low/PAGE)it=cache.erase(it);else ++it;store.prepare(gen,low/PAGE);}
};
struct Cursors {
 struct Entry{U tick=0;bool dirty=false;std::vector<U> v;};
 PageStore store;std::unordered_map<U,Entry> cache;U clock=0;size_t cap=8192;
 explicit Cursors(fs::path d):store(d){}
 void persist(U id,Entry&e){if(e.dirty){store.write(id,e.v,true);e.dirty=false;}}
 Entry& page(U id){auto it=cache.find(id);if(it!=cache.end()){it->second.tick=++clock;return it->second;}if(cache.size()>=cap){auto old=std::min_element(cache.begin(),cache.end(),[](auto&a,auto&b){return a.second.tick<b.second.tick;});persist(old->first,old->second);cache.erase(old);}Entry e;e.tick=++clock;e.v.resize(CSIZE);auto p=store.readpath(id);if(!p.empty()){std::ifstream in(p,std::ios::binary);require(bool(in),"open cursor page");uint32_t i;U v;for(;;){in.read((char*)&i,4);if(in.gcount()==0){require(in.eof(),"read cursor page");break;}require(in.gcount()==4,"truncated cursor slot");in.read((char*)&v,8);require(bool(in)&&i<CSIZE,"invalid cursor page");e.v[i]=v;}}return cache.emplace(id,std::move(e)).first->second;}
 U get(U p){U x=page(p/CSIZE).v[p%CSIZE];return x?x:p;}
 void set(U p,U v){auto&e=page(p/CSIZE);e.v[p%CSIZE]=v;e.dirty=true;}
 void prepare(U gen){for(auto&[id,e]:cache)persist(id,e);store.prepare(gen);}
};
struct PrimeFactors {
 std::array<U,64> data;size_t count=0;
 void push_back(U x){require(count<data.size(),"too many distinct factors");data[count++]=x;}
 U* begin(){return data.data();}U* end(){return data.data()+count;}
};
struct Factor {
 struct Entry{U tick;bool persisted=false;std::vector<uint32_t> sp;};std::unordered_map<U,Entry> cache;fs::path disk;U generated=0,loaded=0,hits=0;U clock=0;std::vector<uint32_t> primes;U prime_limit=1;size_t cap;
 explicit Factor(size_t c,fs::path d):disk(d),cap(c){require(c>0,"factor cache capacity must be positive");fs::create_directories(disk);}
 void persist(U id,Entry&e){if(e.persisted)return;auto tmp=disk/"write.tmp",dest=disk/std::to_string(id);std::ofstream f(tmp,std::ios::binary);f.write((char*)e.sp.data(),e.sp.size()*4);f.close();require(bool(f),"write factor page");syncpath(tmp);fs::rename(tmp,dest);e.persisted=true;}

 void primebase(U limit){if(limit<=prime_limit)return;U upto=std::max<U>(limit,prime_limit*2);require(upto<=100000000,"factor base exceeds supported resource limit (no result claimed)");std::vector<bool> composite(upto+1);primes.clear();for(U p=2;p<=upto;p++){if(composite[p])continue;primes.push_back(p);if(p<=upto/p)for(U x=p*p;x<=upto;x+=p)composite[x]=true;}prime_limit=upto;}
 Entry& segment(U id){auto it=cache.find(id);if(it!=cache.end()){it->second.tick=++clock;hits++;return it->second;}if(cache.size()>=cap){auto old=std::min_element(cache.begin(),cache.end(),[](auto&a,auto&b){return a.second.tick<b.second.tick;});persist(old->first,old->second);cache.erase(old);}auto saved=disk/std::to_string(id);if(fs::exists(saved)){Entry e;e.tick=++clock;e.persisted=true;e.sp.resize(SEG/2);std::ifstream f(saved,std::ios::binary);f.read((char*)e.sp.data(),e.sp.size()*4);require(bool(f)&&f.peek()==EOF,"invalid factor page");loaded++;return cache.emplace(id,std::move(e)).first->second;}generated++;U lo=mul(id,SEG),hi=add(lo,SEG-1),root=0; // integer square root, never floating-point
 U a=0,b=std::min<U>(hi,UINT32_MAX)+1;while(a+1<b){U m=a+(b-a)/2;if(m<=hi/m)a=m;else b=m;}root=a;primebase(root);
 Entry e;e.tick=++clock;e.sp.resize(SEG/2);for(U p:primes){if(p==2)continue;if(p>hi/p)break;U start=mul(lo/p+(lo%p!=0),p);start=std::max(start,p*p);if(!(start&1))start=add(start,p);for(U x=start;x<=hi;){auto&v=e.sp[(x-lo)/2];if(!v)v=p;if(hi-x<2*p)break;x+=2*p;}}
 return cache.emplace(id,std::move(e)).first->second;}
 PrimeFactors factors(U x,U known){PrimeFactors v;if(known){require(known>1&&x%known==0,"bad known factor");v.push_back(known);do{x/=known;}while(x%known==0);}if(!(x&1)&&x>1){v.push_back(2);do{x/=2;}while(!(x&1));}while(x>1){auto&e=segment(x/SEG);U p=e.sp[(x%SEG)/2];if(!p)p=x;v.push_back(p);do{x/=p;}while(x%p==0);}std::sort(v.begin(),v.end());v.count=std::unique(v.begin(),v.end())-v.begin();return v;}
};
struct Threshold{U x,first=0,below=0;};
struct State{U n=0,last=0,known=0,E=2,evens=0,K=0,maxK=0,h8=OFF,h4=OFF,violations=0,equalities=0;};
struct Run {
 U N,interval=100000000,checkpoint_terms=0;double seconds=3600;fs::path dir,outpath;Bitmap bits;Cursors large;Factor fact;State s;std::vector<U> cursor;std::vector<Threshold> ts;FILE*out=nullptr;bool mirror=true;U committed_offset=0;double wall_prior=0;std::chrono::steady_clock::time_point start,last_save;
 Run(U n,fs::path d,fs::path o,size_t pages,size_t segments):N(n),dir(d),outpath(o),bits(d/"pages",pages),large(d/"cursors"),fact(segments,d/"factors"),cursor(CUT+1){start=last_save=std::chrono::steady_clock::now();}
 double elapsed(){return wall_prior+std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();}
 void line(const std::string&v){require(out,"output unopened");require(fprintf(out,"%s\n",v.c_str())>=0,"output write");fflush(out);if(mirror){std::cout<<v<<'\n';std::cout.flush();}}
 void ckpt(){std::cerr<<"progress n "<<s.n<<" wall_seconds "<<elapsed()<<" factor_generated "<<fact.generated<<" factor_disk_reads "<<fact.loaded<<" factor_hits "<<fact.hits<<'\n';line("ckpt "+std::to_string(s.n)+" "+std::to_string(s.last)+" "+std::to_string(s.E)+" "+std::to_string(s.K)+" "+std::to_string(s.maxK)+" "+hex(s.h8));}
 void save(){U gen=add(bits.store.base,1);bits.prepare(gen);large.prepare(gen);require(fflush(out)==0&&fsync(fileno(out))==0,"sync output");committed_offset=ftello(out);auto tmp=dir/"state.tmp";std::ofstream f(tmp,std::ios::binary);f<<"EKGV6\n"<<PAGE<<' '<<CUT<<' '<<SEG<<' '<<CSIZE<<'\n'<<N<<' '<<interval<<' '<<committed_offset<<' '<<std::setprecision(17)<<elapsed()<<'\n';f<<s.n<<' '<<s.last<<' '<<s.known<<' '<<s.E<<' '<<s.evens<<' '<<s.K<<' '<<s.maxK<<' '<<s.h8<<' '<<s.h4<<' '<<s.violations<<' '<<s.equalities<<'\n';f<<bits.low<<' '<<gen<<' '<<ts.size()<<'\n';for(auto&t:ts)f<<t.x<<' '<<t.first<<' '<<t.below<<'\n';f.write((char*)cursor.data(),cursor.size()*sizeof(U));f.close();require(bool(f),"write state");syncpath(tmp);fs::rename(tmp,dir/"state");syncpath(dir,true);bits.store.base=large.store.base=gen;bits.store.cleanup();large.store.cleanup();last_save=std::chrono::steady_clock::now();}
 void openout(bool resume){if(resume){std::ifstream f(dir/"state",std::ios::binary);std::string magic;std::getline(f,magic);require(magic=="EKGV6","invalid checkpoint");U page,cut,seg,csize;f>>page>>cut>>seg>>csize;require(page==PAGE&&cut==CUT&&seg==SEG&&csize==CSIZE,"checkpoint build geometry differs");U n,inter,nt;f>>n>>inter>>committed_offset>>wall_prior;require(n==N&&inter==interval,"checkpoint target or interval differs");f>>s.n>>s.last>>s.known>>s.E>>s.evens>>s.K>>s.maxK>>s.h8>>s.h4>>s.violations>>s.equalities;f>>bits.low>>bits.store.base>>nt;large.store.base=bits.store.base;require(fs::is_directory(bits.store.snapshot(bits.store.base))&&fs::is_directory(large.store.snapshot(large.store.base)),"missing checkpoint snapshot");require(nt==ts.size(),"checkpoint thresholds differ");for(auto&t:ts){U x;f>>x>>t.first>>t.below;require(x==t.x,"checkpoint thresholds differ");}f.get();f.read((char*)cursor.data(),cursor.size()*sizeof(U));require(bool(f),"truncated checkpoint");require(fs::file_size(outpath)>=committed_offset,"output shorter than committed checkpoint");fs::resize_file(outpath,committed_offset);out=fopen(outpath.c_str(),"a");bits.store.cleanup();large.store.cleanup();}else{require(!fs::exists(dir/"state")&&bits.store.empty()&&large.store.empty(),"existing state: use --resume or a new directory");out=fopen(outpath.c_str(),"w");}require(out,"cannot open output");start=last_save=std::chrono::steady_clock::now();}
 U candidate(U p){U x;if(p<=CUT){x=cursor[p];if(!x)x=p;}else x=large.get(p);if(x<bits.low)x=mul(bits.low/p+(bits.low%p!=0),p);while(bits.get(x))x=add(x,p);if(p<=CUT)cursor[p]=x;else large.set(p,x);return x;}
 std::pair<U,U> next(){U best=UINT64_MAX,known=0;auto ps=fact.factors(s.last,s.known);for(U p:ps){U x=candidate(p);if(x<best){best=x;known=p;}}require(known,"no next term");return {best,known};}
 void accept(U x,U known){U oldmax=s.maxK;bits.set(x);s.n++;s.last=x;s.known=known;if(!(x&1))s.evens++;while(bits.get(s.E))s.E=add(s.E,2);s.K=s.evens-(s.E/2-1);for(auto&t:ts)if(!t.first&&s.E>=t.x){t.first=s.n;t.below=oldmax;}s.maxK=std::max(s.maxK,s.K);bits.advance();hash_value(s.h8,x,8);hash_value(s.h4,x,4);
 using W=__uint128_t;bool low=W(28)*x<W(13)*s.n,high=W(7)*x>W(12)*s.n;bool eql=W(28)*x==W(13)*s.n,eqh=W(7)*x==W(12)*s.n;if(low||high){s.violations++;line("violation "+std::to_string(s.n)+" "+std::to_string(x)+" "+(low?"lower":"upper"));}if(eql||eqh){s.equalities++;line("equality "+std::to_string(s.n)+" "+std::to_string(x)+" "+(eql?"lower":"upper"));}if(s.n%interval==0)ckpt();}
 int run(){if(s.n==0){accept(1,0);if(N>=2)accept(2,2);save();}while(s.n<N){auto [x,p]=next();accept(x,p);if((s.n&65535)==0){double dt=std::chrono::duration<double>(std::chrono::steady_clock::now()-last_save).count();if(dt>=seconds||(checkpoint_terms&&s.n%checkpoint_terms<65536)||stop_requested){save();if(stop_requested)return 75;}}}save();if(s.n%interval)ckpt();for(auto&t:ts)line("threshold "+std::to_string(t.x)+" first_n "+(t.first?std::to_string(t.first):"not_reached")+" maxK_below "+std::to_string(t.first?t.below:s.maxK));line("hash64 "+hex(s.h8));line("hash32 "+hex(s.h4));line("counts violations "+std::to_string(s.violations)+" equalities "+std::to_string(s.equalities));return 0;}
};
// This deliberately scans positive integers from 1 and uses gcd directly.
static void naive_test(U N,size_t pages,size_t segs,fs::path dir){Bitmap bits(dir/"naive-pages",pages);Factor f(segs,dir/"factors");std::vector<U> curs(CUT+1),a={0,1,2};std::vector<uint8_t> used(3);used[1]=used[2]=1;bits.set(1);bits.set(2);bits.advance();U last=2,known=2,h=OFF;hash_value(h,1,8);hash_value(h,2,8);for(U n=3;n<=N;n++){U expected=1;for(;;expected++){if(expected>=used.size())used.resize(expected+1);if(!used[expected]&&std::gcd(expected,a.back())>1)break;}U best=UINT64_MAX,d=0;for(U p:f.factors(last,known)){U x=p<=CUT?curs[p]:p;if(!x)x=p;if(x<bits.low)x=mul(bits.low/p+(bits.low%p!=0),p);while(bits.get(x))x=add(x,p);if(p<=CUT)curs[p]=x;if(x<best){best=x;d=p;}}require(best==expected,"naive mismatch n="+std::to_string(n));used[expected]=1;a.push_back(expected);bits.set(best);bits.advance();last=best;known=d;hash_value(h,best,8);}std::cout<<"naive_compare terms "<<N<<" PASS hash64 "<<hex(h)<<'\n';}
int main(int argc,char**argv){try{require(argc>=2,"usage: ekgv N [X ...] [--state DIR] [--output FILE] [--resume] [--naive-check] [--interval N] [--checkpoint-seconds S] [--checkpoint-terms N] [--cache-pages N] [--factor-segments N] [--cursor-pages N] [--quiet]");U N=number(argv[1]);require(N>=1,"N must be >= 1");const char*env=getenv("EKGV_STATE_ROOT");fs::path dir=fs::path(env?env:".")/"ekgv"/("state-"+std::to_string(N)),out;std::vector<U> xs;bool resume=false,naive=false,quiet=false;U interval=100000000,ct=0;double sec=3600;size_t pages=128,segs=16384,cursorpages=8192;for(int i=2;i<argc;i++){std::string v=argv[i];auto arg=[&](){require(i+1<argc,"missing option argument");return std::string(argv[++i]);};if(v=="--state")dir=arg();else if(v=="--output")out=arg();else if(v=="--resume")resume=true;else if(v=="--naive-check")naive=true;else if(v=="--quiet")quiet=true;else if(v=="--interval")interval=number(arg());else if(v=="--checkpoint-terms")ct=number(arg());else if(v=="--checkpoint-seconds")sec=std::stod(arg());else if(v=="--cache-pages")pages=number(arg());else if(v=="--factor-segments")segs=number(arg());else if(v=="--cursor-pages")cursorpages=number(arg());else if(v.starts_with("--"))throw std::runtime_error("unknown option "+v);else xs.push_back(number(v));}require(interval&&sec>0&&cursorpages,"invalid interval or cursor cache");fs::create_directories(dir);int lockfd=open((dir/"lock").c_str(),O_CREAT|O_RDWR,0600);require(lockfd>=0&&flock(lockfd,LOCK_EX|LOCK_NB)==0,"state directory already in use");if(out.empty())out=dir/"output.txt";if(naive){require(N>=2,"naive check needs N >= 2");naive_test(N,pages,segs,dir);return 0;}Run r(N,dir,out,pages,segs);r.large.cap=cursorpages;r.interval=interval;r.seconds=sec;r.checkpoint_terms=ct;r.mirror=!quiet;for(U x:xs)r.ts.push_back({x});r.openout(resume);signal(SIGTERM,sigstop);signal(SIGINT,sigstop);int rc=r.run();rusage ru;getrusage(RUSAGE_SELF,&ru);std::cerr<<"resources wall_seconds "<<std::fixed<<std::setprecision(3)<<r.elapsed()<<" peak_rss_kib "<<ru.ru_maxrss<<" n "<<r.s.n<<'\n';return rc;}catch(const std::exception&e){std::cerr<<"error: "<<e.what()<<'\n';return 1;}}
