// An observation adapter, NOT the independent cover checker. This includes the
// unchanged production source to export its actual choices. Generated snippets
// contain the production prefix code with only its state object substituted by
// a tracer: no pruning, difference computation or tail DFS is executed.
#ifdef TEST_ONLY
#error Coverage observation must use the production build mode
#endif
#define main ds243_production_main
#include "campaign.cpp"
#undef main

struct CoverTrace {
 std::array<unsigned char,12> digits{};
 int image=-1, calls=0;
 CoverTrace()=default;
 CoverTrace(int,int) {}
 void fixed() {}
 void singletons() {}
 bool record(int ci,int layer,int digit) {
  require(layer==calls && layer<12 && digit>=0 && digit<3,"trace prefix");
  require(image<0 || image==ci,"trace image");
  image=ci;digits[calls++]=digit;return true;
 }
 bool choice(int ci,int layer,int digit){return record(ci,layer,digit);}
 bool option(int ci,int layer,int digit){return record(ci,layer,digit);}
};

CoverTrace observe_prefix(U64 id) {
 const int depth=12;const U64 width=531441;
#ifdef FAST_KERNEL
 Task t;t.id=id;int m=0;
#include "coverage-fast-prefix.inc"
 require(s.calls==12,"fast trace count");return s;
#else
 Task task;task.id=id;
#include "coverage-direct-prefix.inc"
 require(r.calls==12,"direct trace count");return r;
#endif
}

template<class V> void json_points(std::ostream& f,V points) {
 std::sort(points.begin(),points.end());f<<'[';
 for(size_t j=0;j<points.size();++j){if(j)f<<',';f<<points[j];}f<<']';
}

int main(int argc,char** argv)try {
 require(argc==6,"coverage_export INPUT CASES OPTIONS_JSON PREFIX_BIN THREADS");
 int threads=std::stoi(argv[5]);require(threads>0,"threads");
 omp_set_dynamic(0);omp_set_num_threads(threads);
#ifdef FAST_KERNEL
 fast::Model model(argv[1],argv[2]);fast::State state(model,0);state.fixed();
 const auto& choices=model.cases;const auto& orbits=model.orbit;
 auto initial=state.points();const char* mode="fast";
#else
 direct::Input model(argv[1],argv[2]);direct::Replay state(model,0);state.singletons();
 const auto& choices=model.images;const auto& orbits=model.orbits;
 auto initial=state.points;const char* mode="direct";
#endif
 std::ofstream out(argv[3]);require(bool(out),"options output");
 out<<"{\"schema\":\"ds243-production-cover-export-v1\",\"mode\":\""<<mode
    <<"\",\"initial_points\":";json_points(out,initial);out<<",\"options\":[";
 for(size_t ci=0;ci<choices.size();++ci){if(ci)out<<',';out<<'[';
  for(size_t d=0;d<choices[ci].size();++d){if(d)out<<',';out<<'[';
   for(int a=0;a<3;++a){if(a)out<<',';std::vector<int> points;
    for(int j:choices[ci][d][a])points.insert(points.end(),orbits[j].begin(),orbits[j].end());
    json_points(out,points);
   }out<<']';
  }out<<']';
 }out<<"]}\n";out.close();require(bool(out),"options write");
 // Each 17-byte record is LE uint32 ID, uint8 case, twelve uint8 digits.
 std::ofstream binary(argv[4],std::ios::binary);require(bool(binary),"prefix output");
 constexpr U64 total=4251528,chunk=65536;std::vector<unsigned char> buffer(17*chunk);
 for(U64 first=0;first<total;first+=chunk){U64 size=std::min(chunk,total-first);
  int failed=0;
  #pragma omp parallel for schedule(static) reduction(|:failed)
  for(U64 j=0;j<size;++j){try {
   U64 id=first+j;auto trace=observe_prefix(id);auto p=buffer.data()+17*j;
   require(trace.image>=0&&trace.image<8,"trace case");
   for(int k=0;k<4;++k)p[k]=(id>>(8*k))&255;
   p[4]=trace.image;
   for(int k=0;k<12;++k)p[5+k]=trace.digits[k];
  }catch(...){failed=1;}}
  require(!failed,"prefix trace failed");
  binary.write(reinterpret_cast<const char*>(buffer.data()),17*size);
 }binary.close();require(bool(binary),"prefix write");
 std::cout<<"OBSERVATION ONLY mode="<<mode<<" prefixes="<<total<<"; no tail search or cover verdict\n";
 return 0;
}catch(const std::exception& error){std::cerr<<error.what()<<'\n';return 2;}
