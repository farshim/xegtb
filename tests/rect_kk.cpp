// rect_kk.cpp -- K + K vs K under capture rules on a RECTANGULAR board.
//
// Why this exists.  The square tables say the hunt stops working between
// 14 x 14 and 15 x 15, and every explanation phrased in terms of board *size*
// also predicts a failure between 13 x 13 and 14 x 14, where none happens.
// Rectangles separate the two variables.  They show that area is irrelevant and
// the shorter side decides: every board with a shorter side of at most 14 is
// won from every placement (24 x 14 is won in up to 299 plies), and every board
// with a shorter side of 15 collapses to the same frozen 73.
//
// Deliberately shares no code with src/kings.cpp -- no symmetry reduction, no
// combinatorial index, no bucketed induction, just value iteration by depth over
// a dense array.  It reproduces that solver's census, deepest depth and deepest
// position on every square board from 5 x 5 to 14 x 14, which is what makes it
// worth trusting about the rectangles.
//
//   c++ -std=c++20 -O2 -o rect_kk tests/rect_kk.cpp
//   ./rect_kk -f 24 -r 14
//
// Values are relative to the side to move: +d = mover wins in d plies, -d = the
// mover loses in d, 0 = draw.  Wins land on odd depths and losses on even ones,
// so an empty round is normal and the loop needs three before it stops.
#include <cstdio>
#include <cstdlib>
#include <string>
#include <vector>
static const short UNK = 32767, ILL = -32766;
static int NF, NR, M;
static inline int FI(int s){ return s % NF; }
static inline int RK(int s){ return s / NF; }
static inline bool adj(int a,int b){ int df=FI(a)-FI(b), dr=RK(a)-RK(b);
    if(df<0)df=-df; if(dr<0)dr=-dr; return (df|dr)!=0 && df<=1 && dr<=1; }
int main(int argc,char**argv){
    NF=15; NR=15;
    for(int i=1;i<argc;++i){ std::string a=argv[i];
        if(a=="-f") NF=atoi(argv[++i]); else if(a=="-r") NR=atoi(argv[++i]); }
    M=NF*NR;
    std::vector<std::vector<int>> nbr(M);
    for(int s=0;s<M;++s) for(int df=-1;df<=1;++df) for(int dr=-1;dr<=1;++dr){
        if(!df&&!dr) continue; int f=FI(s)+df,r=RK(s)+dr;
        if(f<0||r<0||f>=NF||r>=NR) continue; nbr[s].push_back(r*NF+f); }
    long long NP=(long long)M*(M-1)/2, N=NP*M;
    std::vector<int> pa(NP), pb(NP);
    for(int b=0;b<M;++b) for(int a=0;a<b;++a){ long long i=(long long)b*(b-1)/2+a; pa[i]=a; pb[i]=b; }
    auto PR=[&](int a,int b){ if(a>b){int t=a;a=b;b=t;} return (long long)b*(b-1)/2+a; };
    std::vector<short> v0(N,UNK), v1(N,UNK);
    for(long long p=0;p<NP;++p){ v0[p*M+pa[p]]=v1[p*M+pa[p]]=ILL; v0[p*M+pb[p]]=v1[p*M+pb[p]]=ILL; }
    auto kvk=[&](int w,int b){ return adj(w,b)?1:0; };   // K vs K, mover-relative
    // Strict depth-by-depth induction: a position is only committed as a win at
    // depth d when a successor is a loss at exactly d-1, so the first depth it
    // gets is the shortest one.  (Committing on any losing successor, which is
    // what plain value iteration does, gets the win/draw split right and the
    // depths wrong.)
    int pass=0, quiet=0;
    for(int d=1; d<6000; ++d){ long long changed=0; ++pass;
      for(long long p=0;p<NP;++p){ int w1=pa[p],w2=pb[p];
        for(int bk=0;bk<M;++bk){ if(bk==w1||bk==w2) continue; long long s=p*M+bk;
          for(int stm=0;stm<2;++stm){ short& cell = stm? v1[s] : v0[s];
            if(cell!=UNK) continue;
            bool win=false;
            if(stm==0){
              for(int k=0;k<2&&!win;++k){ int from=k?w2:w1, other=k?w1:w2;
                for(int to:nbr[from]){ if(to==other) continue;
                  if(to==bk){ if(d==1) win=true; continue; }
                  if(d>=2 && v1[PR(to,other)*M+bk]==-(short)(d-1)){ win=true; break; } } }
            } else if(d>=2){
              for(int to:nbr[bk]){
                if(to==w1||to==w2) continue;              // capture never loses for White
                if(v0[p*M+to]==-(short)(d-1)){ win=true; break; } } }
            if(win){ cell=(short)d; ++changed; } } } }
      // losses at depth d+1: every successor known, every one a win, deepest == d
      for(long long p=0;p<NP;++p){ int w1=pa[p],w2=pb[p];
        for(int bk=0;bk<M;++bk){ if(bk==w1||bk==w2) continue; long long s=p*M+bk;
          for(int stm=0;stm<2;++stm){ short& cell = stm? v1[s] : v0[s];
            if(cell!=UNK) continue;
            int worst=0,moves=0; bool bad=false;
            if(stm==0){
              for(int k=0;k<2&&!bad;++k){ int from=k?w2:w1, other=k?w1:w2;
                for(int to:nbr[from]){ if(to==other) continue;
                  ++moves;
                  if(to==bk){ bad=true; break; }           // an immediate win: not a loss
                  short x=v1[PR(to,other)*M+bk];
                  if(x==UNK||x<=0){ bad=true; break; }
                  if(x>worst) worst=x; } }
            } else {
              for(int to:nbr[bk]){ ++moves;
                short x;
                if(to==w1||to==w2){ int rem=(to==w1)?w2:w1; x=(short)kvk(rem,to); }
                else x=v0[p*M+to];
                if(x==UNK||x<=0){ bad=true; break; }
                if(x>worst) worst=x; } }
            if(!bad && moves && worst==d){ cell=(short)-(d+1); ++changed; } } } }
      quiet = changed ? 0 : quiet+1;
      if(quiet>=3) break; }
    long long won=0,drawn=0,legal=0; int deep=0; long long bestS=-1;
    for(long long p=0;p<NP;++p) for(int bk=0;bk<M;++bk){ if(bk==pa[p]||bk==pb[p]) continue;
        short x=v0[p*M+bk]; ++legal;
        if(x==UNK||x==0) ++drawn; else if(x>0){ ++won; if(x>deep){deep=x;bestS=p*M+bk;} } }
    std::printf("%2d x %-2d  minside %2d  maxedge %d  legal %9lld  won %9lld (%6.2f%%)  deepest %3d",
        NF,NR,NF<NR?NF:NR,((NF<NR?NF:NR)-1)/2,legal,won,100.0*won/legal,deep);
    if(bestS>=0){ long long p=bestS/M; int bk=(int)(bestS%M);
        auto nm=[&](int s){ static char o[8]; snprintf(o,sizeof o,"%c%d",'a'+FI(s),RK(s)+1); return std::string(o); };
        std::printf("   K%s K%s vs k%s", nm(pa[p]).c_str(), nm(pb[p]).c_str(), nm(bk).c_str()); }
    std::printf("   (%d passes)\n", pass);
    return 0;
}
