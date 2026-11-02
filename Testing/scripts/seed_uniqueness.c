// Variable-length seed measurement on hg38 (local, no downloads). gcc -O3 -march=native -pthread seedmeasure.c -o seedmeasure
// usage: seedmeasure genome.fa NPAIRS mason_R1 mason_R2 nova_R1 nova_R2 hg002_R1 hg002_R2
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <pthread.h>
#include <time.h>
typedef uint64_t u64; typedef uint32_t u32; typedef uint8_t u8;
static u8 *g; static u64 L;
static char chrname[1024][64]; static u64 chrstart[1024]; static int nchr;
#define EMPTY 0xFFFFFFFFFFFFFFFFULL
static double now(void){struct timespec t;clock_gettime(CLOCK_MONOTONIC,&t);return t.tv_sec+t.tv_nsec*1e-9;}
static void load_fasta(const char*p){
  FILE*f=fopen(p,"rb"); if(!f){perror("fasta");exit(1);} fseek(f,0,SEEK_END); long sz=ftell(f); fseek(f,0,SEEK_SET);
  g=malloc(sz+64); char*line=malloc(1<<20); L=0; nchr=0;
  while(fgets(line,1<<20,f)){
    if(line[0]=='>'){ char*e=line+1; while(*e&&*e!=' '&&*e!='\n'&&*e!='\t')e++; *e=0; strncpy(chrname[nchr],line+1,63); chrstart[nchr]=L; nchr++; continue; }
    for(char*c=line;*c&&*c!='\n';c++){ char x=*c|32; g[L++]= x=='a'?0:x=='c'?1:x=='g'?2:x=='t'?3:4; }
  }
  fclose(f); free(line);
}
typedef struct { int k; u32 nbits; u64*key; u32*cnt; u64*posf; u64*bloom; u32 bbits; } Tab;
static inline u64 hq(u64 c){return c*0x9E3779B97F4A7C15ULL;}
static inline u64 hb(u64 c){return (c^(c>>29))*0xBF58476D1CE4E5B9ULL;}
static Tab*mk(int k,u64 nitems,u32 bbits){
  Tab*t=calloc(1,sizeof(Tab)); t->k=k; u32 nb=10; while((1ULL<<nb)<2*nitems)nb++; t->nbits=nb;
  u64 n=1ULL<<nb; t->key=malloc(n*8); memset(t->key,0xFF,n*8); t->cnt=calloc(n,4); t->posf=calloc(n,8);
  t->bbits=bbits; t->bloom=calloc((1ULL<<bbits)/64+1,8); return t; }
static inline void tab_insert(Tab*t,u64 c){
  u64 m=(1ULL<<t->nbits)-1; u64 s=hq(c)>>(64-t->nbits);
  while(t->key[s]!=EMPTY&&t->key[s]!=c)s=(s+1)&m;
  if(t->key[s]==EMPTY)t->key[s]=c;
  u64 b=hb(c)>>(64-t->bbits); t->bloom[b>>6]|=1ULL<<(b&63); }
static inline long tab_find(Tab*t,u64 c){
  u64 m=(1ULL<<t->nbits)-1; u64 s=hq(c)>>(64-t->nbits);
  while(t->key[s]!=EMPTY){ if(t->key[s]==c)return (long)s; s=(s+1)&m; } return -1; }
static Tab*tabs[64]; static int ntabs;
typedef struct { u64 a,b; } Rng;
static void*worker(void*arg){
  Rng*r=arg; u64 a=r->a,b=r->b; u64 start=a>=31?a-31:0; u64 fwd=0,rc=0; int run=0;
  for(u64 i=start;i<b;i++){
    u8 x=g[i]; if(x>3){run=0;fwd=0;rc=0;continue;}
    fwd=(fwd<<2)|x; rc=(rc>>2)|((u64)(3-x)<<62); run++;
    if(i<a)continue;
    for(int ti=0;ti<ntabs;ti++){ Tab*t=tabs[ti]; int k=t->k; if(run<k)continue;
      u64 f= k==32?fwd:(fwd&((1ULL<<(2*k))-1)); u64 rr=rc>>(64-2*k); u64 c=f<rr?f:rr; u64 fl=f<=rr?0:1;
      u64 bb=hb(c)>>(64-t->bbits); if(!((t->bloom[bb>>6]>>(bb&63))&1))continue;
      long s=tab_find(t,c); if(s<0)continue;
      u32 old=__atomic_fetch_add(&t->cnt[s],1,__ATOMIC_RELAXED);
      if(old==0) t->posf[s]=((i-k+1)<<1)|fl; }
  }
  return 0; }
// reads
typedef struct { char*seq; int n; char name[200]; } Mate;
typedef struct { const char*label; Mate*m; int nm; } Set;
static Set sets[3];
static void load_reads(Set*S,const char*p1,const char*p2,int np){
  S->m=calloc(2*np,sizeof(Mate)); S->nm=0; const char*ps[2]={p1,p2};
  for(int which=0;which<2;which++){ FILE*f=fopen(ps[which],"r"); if(!f){perror("reads");exit(1);} char*l=malloc(1<<16);
    for(int i=0;i<np;i++){ if(!fgets(l,1<<16,f))break; Mate*m=&S->m[2*i+which]; strncpy(m->name,l+1,199); m->name[strcspn(m->name,"\n")]=0;
      if(!fgets(l,1<<16,f))break; l[strcspn(l,"\n")]=0; m->seq=strdup(l); m->n=strlen(l); fgets(l,1<<16,f); fgets(l,1<<16,f);} 
    free(l); fclose(f);} S->nm=2*np; }
static int code(char c){switch(c|32){case 'a':return 0;case 'c':return 1;case 'g':return 2;case 't':return 3;}return 4;}
// canonical k-mer of read window; returns 0 if N inside
static int rwin(const char*s,int i,int k,u64*c,u64*fl){ u64 f=0,r=0; for(int j=0;j<k;j++){int x=code(s[i+j]); if(x>3)return 0; f=(f<<2)|x; r|=(u64)(3-x)<<(2*j);} *c=f<r?f:r; *fl=f<=r?0:1; return 1; }
static const int K2[]={16,20,24,28,32}; // read-seed lengths
static const int K1[]={12,14,16,18,20,22,24,26,28,30,32}; // genome-position lengths
int main(int argc,char**argv){
  if(argc<9){fprintf(stderr,"usage\n");return 1;}
  double t0=now(); load_fasta(argv[1]); fprintf(stderr,"genome %llu bases, %d chroms, %.1fs\n",(unsigned long long)L,nchr,now()-t0);
  int np=atoi(argv[2]); const char*lab[3]={"mason","novaseq","hiseq(hg002)"};
  for(int s=0;s<3;s++){ sets[s].label=lab[s]; load_reads(&sets[s],argv[3+2*s],argv[4+2*s],np); }
  // part 1: random genome positions
  int S1=200000; u64*pos1=malloc(S1*8); srand48(12345); int got=0;
  while(got<S1){ u64 p=((u64)(drand48()*(double)(L-64))); int ok=1; for(int j=0;j<32;j++)if(g[p+j]>3){ok=0;break;} if(ok)pos1[got++]=p; }
  Tab*t1[11]; for(int ki=0;ki<11;ki++){ int k=K1[ki]; t1[ki]=mk(k,S1,23);
    for(int q=0;q<S1;q++){ u64 f=0,r=0; for(int j=0;j<k;j++){int x=g[pos1[q]+j]; f=(f<<2)|x; r|=(u64)(3-x)<<(2*j);} tab_insert(t1[ki],f<r?f:r);} tabs[ntabs++]=t1[ki]; }
  // part 2: read windows
  Tab*t2[5]; for(int ki=0;ki<5;ki++){ int k=K2[ki]; u64 nw=0; for(int s=0;s<3;s++)for(int m=0;m<sets[s].nm;m++)if(sets[s].m[m].n>=k)nw+=sets[s].m[m].n-k+1;
    t2[ki]=mk(k,nw,27);
    for(int s=0;s<3;s++)for(int m=0;m<sets[s].nm;m++){ Mate*M=&sets[s].m[m]; for(int i=0;i+k<=M->n;i++){u64 c,fl; if(rwin(M->seq,i,k,&c,&fl))tab_insert(t2[ki],c);} }
    tabs[ntabs++]=t2[ki]; }
  fprintf(stderr,"tables built %.1fs, %d tables\n",now()-t0,ntabs);
  // genome pass, 4 threads
  int NT=4; pthread_t th[4]; Rng rg[4]; for(int i=0;i<NT;i++){rg[i].a=L/NT*i; rg[i].b=(i==NT-1)?L:L/NT*(i+1); pthread_create(&th[i],0,worker,&rg[i]);}
  for(int i=0;i<NT;i++)pthread_join(th[i],0);
  fprintf(stderr,"genome pass done %.1fs\n",now()-t0);
  // ---- report part 1
  printf("PART 1: %d random hg38 positions (error-free genome windows), count of the k-mer at the position (both strands)\n",S1);
  int cnt_unique[11]={0}; for(int q=0;q<S1;q++){ for(int ki=0;ki<11;ki++){ int k=K1[ki]; u64 f=0,r=0; for(int j=0;j<k;j++){int x=g[pos1[q]+j]; f=(f<<2)|x; r|=(u64)(3-x)<<(2*j);} u64 c=f<r?f:r; long s=tab_find(t1[ki],c); if(t1[ki]->cnt[s]==1)cnt_unique[ki]++; } }
  printf("k  : fraction of positions whose k-mer occurs exactly once\n"); for(int ki=0;ki<11;ki++)printf("%2d : %6.2f %%\n",K1[ki],100.0*cnt_unique[ki]/S1);
  // minimal unique length histogram (over tested k), overall and in 'repeat' strata
  // strata by multiplicity of the 20-mer (idx 4) and 32-mer (idx 10)
  const char*sn[4]={"all positions","20-mer occurs >=2 times (repeat-ish)","32-mer occurs >=2 times (true repeat >=32 bp)","20-mer occurs >=2 but 32-mer unique"};
  int hist[4][13]; memset(hist,0,sizeof hist); int tot[4]={0};
  for(int q=0;q<S1;q++){ int minu=12; // index into K1 or 11 = none (>32)
    int cu[11]; for(int ki=0;ki<11;ki++){ int k=K1[ki]; u64 f=0,r=0; for(int j=0;j<k;j++){int x=g[pos1[q]+j]; f=(f<<2)|x; r|=(u64)(3-x)<<(2*j);} u64 c=f<r?f:r; long s=tab_find(t1[ki],c); cu[ki]=t1[ki]->cnt[s]; }
    int mu=11; for(int ki=0;ki<11;ki++)if(cu[ki]==1){mu=ki;break;} (void)minu;
    int in[4]={1,cu[4]>=2,cu[10]>=2,cu[4]>=2&&cu[10]==1};
    for(int sidx=0;sidx<4;sidx++)if(in[sidx]){hist[sidx][mu]++;tot[sidx]++;} }
  for(int sidx=0;sidx<4;sidx++){ printf("\nminimal unique length (smallest tested k with count 1), %s: n=%d\n",sn[sidx],tot[sidx]); int cum=0; for(int ki=0;ki<12;ki++){ cum+=hist[sidx][ki]; if(ki<11)printf("  <=%2d : %6.2f %% (bin %6.2f %%)\n",K1[ki],100.0*cum/tot[sidx],100.0*hist[sidx][ki]/tot[sidx]); else printf("  >32  : %6.2f %%\n",100.0*hist[sidx][ki]/tot[sidx]); } }
  // ---- part 2
  for(int s=0;s<3;s++){ Set*S=&sets[s]; printf("\nPART 2: %s, %d mates (first %d pairs)\n",S->label,S->nm,np);
    int upto[5]={0}; int rhist[6]={0}; long rtot=0; int ismason=(s==0);
    long nuw[5]={0},ngw[5]={0},mates_has[5]={0},mates_allgood[5]={0},mates_firstgood[5]={0};
    long pinA[5]={0},pinA_ok[5]={0},pinB[5]={0},pinB_ok[5]={0};
    for(int m=0;m<S->nm;m++){ Mate*M=&S->m[m]; int n=M->n; int has[5]={0},allgood[5],firstgood[5]; for(int a=0;a<5;a++){allgood[a]=1;firstgood[a]=-1;}
      char tchr[64]=""; long ta=0,tb=0; char tst='+';
      if(ismason){ char*p=M->name; char*c1=strchr(p,':'); if(c1){ c1++; char*c2=strchr(c1,':'); if(c2){ int ln=c2-c1; memcpy(tchr,c1,ln); tchr[ln]=0; char*iv=c2+1;
            if(m%2==1){ char*c3=strchr(iv,':'); if(c3)iv=c3+1; }
            ta=strtol(iv,&iv,10); iv++; tb=strtol(iv,&iv,10); tst=*iv; } } }
      u64 tstart=0; int found=0; if(ismason){ for(int c=0;c<nchr;c++)if(!strcmp(chrname[c],tchr)){tstart=chrstart[c];found=1;} if(!found){fprintf(stderr,"chr not found %s\n",tchr);} }
      int minu_pos[1024]; for(int i=0;i<n&&i<1024;i++)minu_pos[i]=5;
      for(int ki=0;ki<5;ki++){ int k=K2[ki]; for(int i=0;i+k<=n;i++){ u64 c,fl; if(!rwin(M->seq,i,k,&c,&fl))continue; long sl=tab_find(t2[ki],c); if(sl<0||t2[ki]->cnt[sl]!=1)continue;
          has[ki]=1; nuw[ki]++; if(i<1024&&minu_pos[i]==5)minu_pos[i]=ki;
          if(ismason){ u64 gp=t2[ki]->posf[sl]>>1; u64 gf=t2[ki]->posf[sl]&1; int plus=(gf==fl); long expct= tst=='+'? (long)tstart+ta+i : (long)tstart+tb-i-k; int good=(plus==(tst=='+')) && labs((long)gp-expct)<=25;
            if(good)ngw[ki]++; else allgood[ki]=0; if(firstgood[ki]<0)firstgood[ki]=good; } } }
      for(int i=0;i<n&&i<1024;i++){rhist[minu_pos[i]]++;rtot++;}
      int cum=0; for(int ki=0;ki<5;ki++){ cum|=has[ki]; if(cum)upto[ki]++; if(has[ki]){mates_has[ki]++; if(ismason){ if(allgood[ki])mates_allgood[ki]++; if(firstgood[ki]==1)mates_firstgood[ki]++; }} }
      if(ismason){ for(int cap=0;cap<5;cap++){ int sk=-1; for(int ki=0;ki<=cap;ki++)if(has[ki]){sk=ki;break;} if(sk>=0){pinA[cap]++; if(firstgood[sk]==1)pinA_ok[cap]++;} if(has[cap]){pinB[cap]++; if(firstgood[cap]==1)pinB_ok[cap]++;} } }
    }
    printf("  mates with >=1 exact UNIQUE seed (count==1 in hg38) of length <= K (any tested length up to K):\n"); for(int ki=0;ki<5;ki++)printf("   K=%2d : %6.2f %%\n",K2[ki],100.0*upto[ki]/S->nm);
    printf("  per seed length k (all windows of that length): mates with a unique k-window; unique windows per mate\n"); for(int ki=0;ki<5;ki++)printf("   k=%2d : %6.2f %% of mates, %.1f unique windows per mate\n",K2[ki],100.0*mates_has[ki]/S->nm,(double)nuw[ki]/S->nm);
    if(ismason){ printf("  mason truth (seed locus vs simulated locus: strand and +-25 bp):\n");
      for(int ki=0;ki<5;ki++)printf("   k=%2d: window precision %6.2f %% (%ld/%ld); of %ld mates with a unique k-window: all at truth %6.2f %%, leftmost at truth %6.2f %%\n",K2[ki],100.0*ngw[ki]/(nuw[ki]?nuw[ki]:1),ngw[ki],nuw[ki],mates_has[ki],100.0*mates_allgood[ki]/(mates_has[ki]?mates_has[ki]:1),100.0*mates_firstgood[ki]/(mates_has[ki]?mates_has[ki]:1));
      for(int cap=0;cap<5;cap++)printf("   cap K=%2d: policy 'shortest unique then leftmost': pinned %6.2f %%, correct %6.2f %% of pinned | policy 'length K only, leftmost': pinned %6.2f %%, correct %6.2f %% of pinned\n",K2[cap],100.0*pinA[cap]/S->nm,100.0*pinA_ok[cap]/(pinA[cap]?pinA[cap]:1),100.0*pinB[cap]/S->nm,100.0*pinB_ok[cap]/(pinB[cap]?pinB[cap]:1)); }
    printf("  per read position: shortest exact unique window starting there (tested lengths 16,20,24,28,32):\n   "); for(int a=0;a<5;a++)printf("%d: %.2f %%  ",K2[a],100.0*rhist[a]/rtot); printf("none<=32: %.2f %%\n",100.0*rhist[5]/rtot); }
  return 0; }
