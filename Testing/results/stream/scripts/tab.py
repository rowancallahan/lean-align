import json,sys,statistics as st
pre=sys.argv[1]; hs=[]
print("tool rep | wall_s | load_s | aligner_cpu_s | cores | pipeline_cpu_s | cores | rssGB | Gbp/hr | Gbp/core-h(aligner) | pairs R1/R2 | Gbp")
R={}
for t in ('ours','minibwa'):
    for i in (1,2,3):
        r=json.load(open(f'{pre}10000000_{t}_rep{i}/result.json')); w=r['wall_s']; a=r['aligner_user_s']+r['aligner_sys_s']; p=r['all_children_user_s']+r['all_children_sys_s']; g=(r['bases_R1']+r['bases_R2'])/1e9
        row=(w,r['index_load_s'],a,a/w,p,p/w,r['peak_rss_GB'],g/w*3600,g/a*3600)
        R.setdefault(t,[]).append(row)
        print(f"{t} {i} | {w:.1f} | {row[1]:.2f} | {a:.1f} | {a/w:.2f} | {p:.1f} | {p/w:.2f} | {r['peak_rss_GB']:.2f} | {row[7]:.1f} | {row[8]:.2f} | {r['pairs_R1']:.0f}/{r['pairs_R2']:.0f} | {g:.3f}  (R1 bases {r['bases_R1']:.0f}, R2 {r['bases_R2']:.0f})")
for t,v in R.items():
    print(t,'mean/min/max wall',f"{st.mean(x[0] for x in v):.1f}/{min(x[0] for x in v):.1f}/{max(x[0] for x in v):.1f}",'Gbp/hr',f"{st.mean(x[7] for x in v):.1f}",'Gbp/core-h',f"{st.mean(x[8] for x in v):.2f}")
