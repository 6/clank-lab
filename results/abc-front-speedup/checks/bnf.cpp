// Rigorous (CAPD interval) check of the hypotheses of Moser's twist theorem
// for the return map P from {z = 0} to {z = 2 pi} of a volume-preserving flow:
// an interval-Newton proof of a fixed point of P in a box X, the 3-jet of P
// over X, |trace DP| < 2, and the third-order Birkhoff normal form
// (CAPD's computePlanarEllipticNormalForm, which checks lambda^k != 1, k <= 4).
// usage: bnf check CERT     (the claim; exit 0 only if every check passes)
//        bnf control        (the integrable control x'=cos y, y'=sin x, z'=13/10
//                            at (0, pi/2): expected a0 = 2 pi - 20 pi/13, a1 = -(20 pi/13)/4)
#include <iostream>
#include <cstring>
#include <fstream>
#include <map>
#include <cmath>
#include <ctime>
#include <sys/resource.h>
#include "capd/capdlib.h"
#include "capd/normalForms/normalForms.h"
using namespace capd;
using namespace std;

int main(int argc, char** argv){
  cout.precision(17);
  if(argc<2){ cerr<<"usage: bnf check CERT | bnf control\n"; return 2; }
  string mode=argv[1];
  string sys = mode=="check" ? "abc" : "control";
  std::map<string,string> cert;
  if(mode=="check"){
    if(argc<3){ cerr<<"usage: bnf check CERT\n"; return 2; }
    ifstream in(argv[2]); string line;
    while(getline(in,line)){ if(line.empty()||line[0]=='#') continue; istringstream ss(line); string k,v; ss>>k>>v; cert[k]=v; }
    for(const char* k: {"centre_num_x","centre_num_y","radius_log2","time_lo","time_hi","trace_lo","trace_hi"})
      if(!cert.count(k)){ cerr<<"FAIL: certificate lacks "<<k<<"\n"; return 1; }
  }
  const int degree=3;
  string field = sys=="abc" ? "var:x,y,z;fun:sin(z)+cos(y),sin(x)+cos(z),sin(y)+cos(x);"
               : "var:x,y,z;fun:cos(y),sin(x),13/10;";
  IMap f(field,degree);
  ICnOdeSolver solver(f,20);
  solver.setMaxStep(0.1);
  interval twoPi = 2*interval::pi();
  IVector origin(3); origin[2]=twoPi;
  IVector normal(3); normal[2]=1;
  IAffineSection section(origin,normal);
  ICnPoincareMap pm(solver,section,poincare::MinusPlus);

  double cx, cy; interval r;
  if(mode=="check"){
    cx = ldexp((double)stoll(cert["centre_num_x"]),-40);   // exact: numerators < 2^53
    cy = ldexp((double)stoll(cert["centre_num_y"]),-40);
    r = interval(ldexp(1.0,stoi(cert["radius_log2"])));
  } else { cx = 0; cy = 1.5707963267948966; r = interval(ldexp(1.0,-20)); }
  IVector c(3); c[0]=cx; c[1]=cy; c[2]=0;
  IVector X(c); X[0]+=interval(-1,1)*r; X[1]+=interval(-1,1)*r;

  // P at the centre
  IVector Pc;
  { C0Rect2Set s(c); Pc = pm(s); }
  // DP over the box (C^1 part of a C^n computation with degree 1 is enough; use the jet)
  IJet J(3,degree);
  interval T;
  { CnRect2Set s(X,degree); IVector PX = pm(s,J,T); J = pm.computeDP(J);
    cout<<"P(X) = "<<PX<<"\nreturn time over X = "<<T<<"\n"; }
  if(mode=="check"){
    interval tl(cert["time_lo"],cert["time_lo"]), th(cert["time_hi"],cert["time_hi"]);
    bool ok = T.leftBound() > tl.rightBound() && T.rightBound() < th.leftBound();
    cout<<"return time inside claimed ["<<cert["time_lo"]<<", "<<cert["time_hi"]<<"]: "<<(ok?"yes":"FAIL")<<"\n";
    if(!ok) return 1;
  }
  IMatrix DPX = (IMatrix)J;
  // interval Newton for F(u) = P(u) - u on the (x,y) plane
  interval a=DPX[0][0]-1, b=DPX[0][1], cc=DPX[1][0], d=DPX[1][1]-1;
  interval det=a*d-b*cc;
  if(det.contains(0.)){ cout<<"FAIL: singular Newton matrix\n"; return 1; }
  interval F0=Pc[0]-c[0], F1=Pc[1]-c[1];
  interval N0 = c[0] - ( d*F0 - b*F1)/det;
  interval N1 = c[1] - (-cc*F0 + a*F1)/det;
  bool newtonOK = subsetInterior(N0,X[0]) && subsetInterior(N1,X[1]);
  cout<<"P(c) - c = ("<<F0<<", "<<F1<<")\n";
  cout<<"Newton image N = ("<<N0<<", "<<N1<<")\n";
  cout<<"interval Newton: "<<(newtonOK?"N inside interior of X: unique fixed point of P in X":"FAIL")<<"\n";
  if(!newtonOK) return 1;
  // z' = sin y + cos x > 0 along the whole orbit segment from {z = 0} to the return,
  // for every start in X (so the segment meets each plane z = c, 0 <= c <= 2 pi, once).
  if(sys=="abc"){
    IOdeSolver s0(f,20); s0.setMaxStep(0.1);
    ITimeMap tm(s0); tm.stopAfterStep(true);
    C0Rect2Set set(X);
    double Tend = T.rightBound();
    double vzmin = 1e300;
    do{
      tm(Tend,set);
      const IOdeSolver::SolutionCurve& curve = s0.getCurve();
      IVector v = curve(interval(0,1)*s0.getStep());
      interval vz = sin(v[1])+cos(v[0]);
      if(!(vz.leftBound()>0)){ cout<<"FAIL: z' not positive on "<<v<<"\n"; return 1; }
      vzmin = std::min(vzmin, (double)vz.leftBound());
    }while(!tm.completed());
    cout<<"z' > 0 along the orbit segment over [0, T+] for all starts in X: yes (min lower bound "<<vzmin<<")\n";
  }
  cout<<"z-displacement of P(X) - X: "<<(IVector)(J())-X<<"\n";

  // 2D jet in (x,y) over X: Taylor coefficients of P_i in variables x,y (z-variation 0)
  capd::diffAlgebra::Jet<IMatrix,0> J2(2,degree);
  for(int i=0;i<2;++i){
    J2(i) = J(i) - (i==0? interval(0.):interval(0.)); // value (not used by the normal form)
    for(int k=1;k<=degree;++k){
      Multipointer mp = J2.first(k);
      do{ J2(i,mp) = J(i,mp); }while(J2.hasNext(mp));
    }
  }
  J2(0) = interval(0.); J2(1)=interval(0.);
  interval tr = DPX[0][0]+DPX[1][1];
  interval dt = DPX[0][0]*DPX[1][1]-DPX[0][1]*DPX[1][0];
  cout<<"trace DP over X = "<<tr<<"\ndet DP over X = "<<dt<<"\n";
  bool elliptic = (tr > interval(-2)) && (tr < interval(2));
  cout<<"elliptic (|trace|<2 on X): "<<(elliptic?"yes":"FAIL")<<"\n";
  if(!elliptic) return 1;
  if(mode=="check"){
    interval tl(cert["trace_lo"],cert["trace_lo"]), th(cert["trace_hi"],cert["trace_hi"]);
    bool ok = tr.leftBound() > tl.rightBound() && tr.rightBound() < th.leftBound()
              && th.rightBound() < -1.0 && tl.leftBound() > -2.0;
    cout<<"trace inside claimed ["<<cert["trace_lo"]<<", "<<cert["trace_hi"]<<"] within (-2,-1): "<<(ok?"yes":"FAIL")<<"\n";
    if(!ok) return 1;
  }
  try{
    auto res = capd::normalForms::computePlanarEllipticNormalForm(J2);
    cout<<"normal form: w = a0 + a1 (x^2+y^2), a0 = "<<res[0]<<"\n a1 = "<<res[1]<<"\n";
    bool twist = !(res[1].real().contains(0.));
    cout<<"rotation a0/(2 pi) = "<<res[0].real()/twoPi<<"\n";
    cout<<"twist Re a1 excludes 0: "<<(twist?"yes":"FAIL")<<"\n";
    if(!twist) return 1;
  }catch(exception& e){ cout<<"FAIL normal form: "<<e.what()<<"\n"; return 1; }
  struct rusage ru; getrusage(RUSAGE_SELF,&ru);
  cout<<"cpu_s "<<ru.ru_utime.tv_sec+ru.ru_utime.tv_usec*1e-6<<" peak_rss_kb "<<ru.ru_maxrss<<"\n";
  cout<<"ALL CHECKS PASSED\n";
  return 0;
}
