// Count distinct canonical 25-mers (both strands) in a FASTA by #occurrences. Uppercase ACGT only;
// windows never cross a chromosome boundary or a non-ACGT byte. gcc -O3 -march=native -pthread heavy_count.c -o heavy_count
// usage: heavy_count genome.fa P THREADS
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <assert.h>
#include <pthread.h>
#include <time.h>
typedef uint64_t u64;
#define K 25
static unsigned char *g; static u64 L; static int P, T;
static const u64 MASK = (1ULL << (2*K)) - 1;
static double now(void){struct timespec t;clock_gettime(CLOCK_MONOTONIC,&t);return t.tv_sec+t.tv_nsec*1e-9;}
static inline u64 hsh(u64 c){ return (c*0x9E3779B97F4A7C15ULL) >> 40; }
static const int TH[] = {100, 200, 500, 1000, 10000};
#define NTH 5
static u64 res[64][NTH], resw[64][NTH], resmax[64], nwin[64];
static int cmp(const void*a,const void*b){u64 x=*(u64*)a,y=*(u64*)b;return x<y?-1:x>y;}
static void*run(void*arg){
  int p=(int)(intptr_t)arg; u64 cap=L/P*5/4+(1<<20), n=0; u64*buf=malloc(cap*8); assert(buf);
  u64 f=0,r=0; int len=0;
  for(u64 i=0;i<L;i++){
    int b; switch(g[i]){case 'A':b=0;break;case 'C':b=1;break;case 'G':b=2;break;case 'T':b=3;break;default:b=-1;}
    if(b<0){len=0;f=r=0;continue;}
    f=((f<<2)|b)&MASK; r=(r>>2)|((u64)(3-b)<<(2*K-2)); len++;
    if(len>=K){ u64 c=f<r?f:r; assert(f!=r); if(hsh(c)%P==(u64)p){ assert(n<cap); buf[n++]=c; } }
  }
  qsort(buf,n,8,cmp); nwin[p]=n;
  for(u64 i=0;i<n;){ u64 j=i; while(j<n&&buf[j]==buf[i])j++; u64 c=j-i;
    if(c>resmax[p])resmax[p]=c;
    for(int t=0;t<NTH;t++) if(c>=(u64)TH[t]){res[p][t]++;resw[p][t]+=c;} i=j; }
  free(buf); return 0;
}
int main(int argc,char**argv){
  assert(argc==4); P=atoi(argv[2]); T=atoi(argv[3]); assert(P<=64);
  double t0=now(); FILE*fp=fopen(argv[1],"rb"); assert(fp); fseek(fp,0,SEEK_END); long sz=ftell(fp); fseek(fp,0,SEEK_SET);
  g=malloc(sz+1); char*line=malloc(1<<20); L=0; int nchr=0;
  while(fgets(line,1<<20,fp)){ if(line[0]=='>'){ g[L++]='N'; nchr++; continue; }  // separator: no window crosses
    for(char*c=line;*c&&*c!='\n';c++) g[L++]=*c; }
  fclose(fp); fprintf(stderr,"loaded %lu bytes, %d chroms, %.1fs\n",(unsigned long)L,nchr,now()-t0);
  for(int p0=0;p0<P;p0+=T){ pthread_t th[64]; int m=0;
    for(int p=p0;p<P&&p<p0+T;p++,m++) pthread_create(&th[m],0,run,(void*)(intptr_t)p);
    for(int i=0;i<m;i++) pthread_join(th[i],0); fprintf(stderr,"partitions %d..%d done %.1fs\n",p0,p0+m-1,now()-t0); }
  u64 W=0,mx=0; for(int p=0;p<P;p++){W+=nwin[p]; if(resmax[p]>mx)mx=resmax[p];}
  printf("ACGT windows %lu, max copies %lu, time %.1fs\n",(unsigned long)W,(unsigned long)mx,now()-t0);
  for(int t=0;t<NTH;t++){ u64 a=0,w=0; for(int p=0;p<P;p++){a+=res[p][t];w+=resw[p][t];}
    printf(">= %5d copies: %10lu distinct canonical 25-mers (%.1f MB at 8 B), covering %lu windows (%.1f%%)\n",
      TH[t],(unsigned long)a,a*8/1e6,(unsigned long)w,100.0*w/W); }
  return 0;
}
