#!/usr/bin/env python3
"""python3 make_figs.py  -> figs/*.svg and figs/*.png. Reads only data/*.tsv; rows with NA are skipped (drawn as 'not measured')."""
import csv, collections, statistics as st, os
import matplotlib; matplotlib.use('Agg')
import matplotlib.pyplot as plt
D = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'data'); O = os.path.join(os.path.dirname(D), 'figs'); os.makedirs(O, exist_ok=True)
def tsv(n): return list(csv.DictReader((l for l in open(f'{D}/{n}.tsv') if not l.startswith('#')), delimiter='\t'))
def num(x):
    try: return float(x)
    except (TypeError, ValueError): return None          # NA, '' -> None
# one colour per tool in every figure (Okabe-Ito)
C = {'lean-align': '#0072B2', 'lean-align-before': '#56B4E9', 'minibwa': '#E69F00', 'other': '#999999'}
LAB = {'lean-align': 'lean-align (f465a57)', 'lean-align-before': 'lean-align before (64ae73f / e96862d)', 'minibwa': 'minibwa (c07de5c)'}
plt.rcParams.update({'font.size': 9, 'axes.spines.top': False, 'axes.spines.right': False, 'axes.grid': True, 'axes.axisbelow': True, 'grid.alpha': .25, 'axes.grid.axis': 'y'})
def save(fig, name): fig.tight_layout(); [fig.savefig(f'{O}/{name}.{e}', dpi=150) for e in ('svg', 'png')]; plt.close(fig)
def bars(ax, groups, series, val, fmt='{:.1f}', colors=None, width=.8, miss='not measured'):
    """val(group, series) -> number or None; None draws an empty hatched slot with a note."""
    w = width / len(series); top = max([val(g, s) or 0 for g in groups for s in series] + [1e-9])
    for j, s in enumerate(series):
        for i, g in enumerate(groups):
            x = i + (j - (len(series) - 1) / 2) * w; v = val(g, s); c = (colors or C).get(s, C['other'])
            if v is None:
                ax.bar(x, top * .9, w * .92, fill=False, edgecolor=c, lw=1, ls='--'); ax.text(x, top * .45, miss, rotation=90, ha='center', va='center', fontsize=7.5, color='#444')   # dashed empty slot: no value implied
            else:
                ax.bar(x, v, w * .92, color=c); ax.text(x, v, fmt.format(v), ha='center', va='bottom', fontsize=7.5)
    ax.set_xticks(range(len(groups))); ax.set_xticklabels(groups)
def legend(ax, series, **k): ax.legend(handles=[plt.Rectangle((0, 0), 1, 1, color=C.get(s, C['other'])) for s in series], labels=[LAB.get(s, s) for s in series], fontsize=7.5, frameon=False, **k)
R = tsv('runs')
def pick(**kw):                                        # median of a column over the rows that match
    return lambda col: (lambda v: st.median(v) if v else None)([num(r[col]) for r in R if all(r[k] == str(x) for k, x in kw.items()) and num(r[col]) is not None])
DS = {'hiseq_2x250': 'HiSeq 2x250', 'novaseq_2x151': 'NovaSeq 2x151'}
T3 = ['lean-align-before', 'lean-align', 'minibwa']
# (a) speed at 4 threads, 5M pairs, gz
fig, ax = plt.subplots(1, 2, figsize=(9, 3.6))
for a, col, yl in zip(ax, ('Gbp_hr', 'Gbp_core_hr'), ('speed (Gbp/hour, 4 threads)', 'Gbp per core-hour')):
    bars(a, list(DS), T3, lambda g, s: pick(experiment='gz5m', data=g, tool=s)(col), fmt='{:.1f}'); a.set_ylabel(yl); a.set_xticklabels(list(DS.values()))
fig.legend(handles=[plt.Rectangle((0, 0), 1, 1, color=C[t]) for t in T3], labels=[LAB[t] for t in T3], loc='lower center', ncol=3, frameon=False, fontsize=8); fig.suptitle('5M pairs from gz files, 4 cores', fontsize=9, y=.99); fig.tight_layout(rect=(0, .07, 1, 1)); [fig.savefig(f'{O}/a_speed_4threads.{e}', dpi=150) for e in ('svg', 'png')]; plt.close(fig)
# (b) peak memory (rows that have it)
G = [('stream', 'novaseq_2x151', 20000000, 'NovaSeq 20M'), ('lane', 'hiseq_2x250', 33900000, 'HiSeq 34M'), ('lane', 'novaseq_2x151', 40000000, 'NovaSeq 40M')]
fig, ax = plt.subplots(figsize=(6.5, 3.6))
bars(ax, [g[3] for g in G], T3, lambda lab, s: (lambda g: pick(experiment=g[0], data=g[1], pairs=g[2], tool=s)('peak_GB'))([g for g in G if g[3] == lab][0]), fmt='{:.1f}')
ax.set_ylabel('peak memory (GB)'); legend(ax, T3, loc='upper left'); ax.set_ylim(0, 11.5); save(fig, 'b_memory')
# (c) throughput vs run size (streamed from the network, NovaSeq)
fig, ax = plt.subplots(1, 2, figsize=(9, 3.6))
for a, col, yl in zip(ax, ('Gbp_hr', 'Gbp_core_hr'), ('Gbp/hour (4 cores)', 'Gbp per core-hour')):
    for s in T3:
        pts = sorted((num(r['pairs']) / 1e6, num(r[col])) for r in R if r['experiment'] == 'stream' and r['tool'] == s and num(r[col]) is not None)
        if pts: a.plot(*zip(*pts), 'o-', color=C[s], label=LAB[s]); [a.annotate(f'{y:.1f}', (x, y), textcoords='offset points', xytext=(0, 5), ha='center', fontsize=7.5) for x, y in pts]
    a.set_xlabel('pairs streamed (millions, NovaSeq)'); a.set_ylabel(yl); a.set_xticks([10, 20, 40]); a.set_ylim(bottom=0)
ax[0].legend(fontsize=7.5, frameon=False, loc='lower right'); save(fig, 'c_throughput_vs_size')
# (d) slow jobs
J = tsv('slow_jobs'); G = [f'{r["data"]}' for r in J if r['build'] == 'before']
fig, ax = plt.subplots(1, 2, figsize=(8, 3.4))
for a, col, yl in zip(ax, ('jobs_over_5s', 'pct_wall_under_4_jobs'), ('jobs longer than 5 s', '% of wall time with fewer than 4 jobs running')):
    bars(a, G, ['lean-align-before', 'lean-align'], lambda g, s: num(next(r[col] for r in J if r['data'] == g and r['build'] == ('before' if s.endswith('before') else 'after'))), fmt='{:.0f}' if col == 'jobs_over_5s' else '{:.1f}'); a.set_ylabel(yl)
legend(ax[1], ['lean-align-before', 'lean-align'], loc='upper right'); save(fig, 'd_slow_jobs')
# (e) slow pairs: mapped alone, 1 core (log axis)
P = tsv('slow_pairs'); cols = [('before_64ae73f', 'lean-align-before', '64ae73f'), ('fix1_351301d', 'other', '351301d (first fix)'), ('merged_f465a57', 'lean-align', 'f465a57')]
fig, ax = plt.subplots(figsize=(8, 3.6)); w = .8 / 3
for j, (c, k, lab) in enumerate(cols):
    for i, r in enumerate(P):
        v = num(r[c])
        if v: ax.bar(i + (j - 1) * w, v, w * .92, color=C[k], label=lab if i == 0 else None); ax.text(i + (j - 1) * w, v, f'{v:.2f}' if v < 10 else f'{v:.0f}', ha='center', va='bottom', fontsize=7.5)
ax.set_yscale('log'); ax.set_xticks(range(len(P))); ax.set_xticklabels([r['pair'].replace('_', ' ') for r in P]); ax.set_ylabel('time to map the pair(s) alone (s, log axis)'); ax.set_ylim(.1, 400); ax.legend(fontsize=7.5, frameon=False); save(fig, 'e_slow_pairs')
# (e2) the same pairs inside the HiSeq lane run: before vs after, one point per pair
S = tsv('slow_pairs_stream'); fig, ax = plt.subplots(figsize=(4.8, 4.2))
ax.scatter([num(r['before_ms']) / 1e3 for r in S], [num(r['after_ms']) / 1e3 for r in S], s=18, color=C['lean-align'])
ax.plot([.01, 100], [.01, 100], color='#888', lw=.8, ls=':'); ax.set_xscale('log'); ax.set_yscale('log'); ax.set_xlim(.8, 100); ax.set_ylim(.01, 100)
ax.set_xlabel('before: 64ae73f (s)'); ax.set_ylabel('after: f465a57 (s)'); ax.grid(axis='both', alpha=.25)
ax.text(.9, 70, f'{len(S)} pairs that took 1 s or more before\nHiSeq lane run, same pair indexes', fontsize=7.5, va='top'); save(fig, 'e2_slow_pairs_in_lane')
# (f) accuracy / uniqueness vs minibwa
A = tsv('accuracy'); v = lambda **kw: next((num(r['value']) for r in A if all(r[k] == x for k, x in kw.items())), None)
fig, ax = plt.subplots(1, 3, figsize=(14, 4), gridspec_kw={'width_ratios': [1, 1, 2.2]}); two = ['lean-align', 'minibwa']
for a, met, yl in ((ax[0], 'pct_proper_pair', 'proper pairs (% of all pairs)'), (ax[1], 'pct_unique', 'unique pairs (% of all pairs)')):
    bars(a, ['novaseq_200k', 'hiseq_200k'], two, lambda g, s: v(block='real', dataset=g, metric=met, tool=s), fmt='{:.1f}'); a.set_ylabel(yl); a.set_ylim(0, 112); a.set_xticklabels(['NovaSeq 200k', 'HiSeq 200k'])
cl = ['unique', 'unknown', 'not proper']; G = [f'{m} / {c}' for m in ('mason', 'low', 'high') for c in cl]
bars(ax[2], G, two, lambda g, s: v(block='sim', dataset=g.split(' / ')[0], **{'class': g.split(' / ')[1]}, metric='pct_pair_correct', tool=s), fmt='{:.0f}')
ax[2].set_ylabel('pairs placed correctly (%), by our class'); ax[2].set_ylim(0, 112); ax[2].tick_params(axis='x', rotation=60); [t.set_fontsize(6.5) for t in ax[2].texts]; fig.legend(handles=[plt.Rectangle((0, 0), 1, 1, color=C[t]) for t in two], labels=['lean-align (027ef1e; output identical to f465a57)', LAB['minibwa']], loc='upper center', ncol=2, frameon=False, fontsize=8); fig.subplots_adjust(top=.9)
fig.tight_layout(rect=(0, 0, 1, .92)); [fig.savefig(f'{O}/f_accuracy.{e}', dpi=150) for e in ('svg', 'png')]; plt.close(fig)
# (g) ROC on simulated reads
Rc = tsv('roc'); fig, ax = plt.subplots(1, 3, figsize=(12, 3.6))
for a, m in zip(ax, ('mason', 'low', 'high')):
    for tool, mk, ms in (('minibwa', 'o-', 3.5), ('lean-align', 's', 8)):
        pts = [(num(r['mapped_frac']), num(r['correct_frac_of_mapped'])) for r in Rc if r['set'] == m and r['tool'] == ('ours' if tool == 'lean-align' else tool)]
        if pts: a.plot(*zip(*pts), mk, ms=ms, color=C[tool], label=tool + (' (MAPQ 60 and MAPQ >= 0)' if tool == 'lean-align' else ' (one point per MAPQ threshold)'))
    a.set_xlabel('fraction of reads mapped'); a.set_ylabel('fraction of mapped reads correct'); a.set_title(f'simulated: {m}', fontsize=9); a.grid(axis='both', alpha=.25)
ax[0].legend(fontsize=7, frameon=False, loc='lower left'); save(fig, 'g_roc')
# (h) the paper's Fig. 3 WGS bars + an empty slot for lean-align at 32 threads
W = [r for r in tsv('paper_perf') if r['dataset'] == 'WGS']; W.sort(key=lambda r: -num(r['Gbp_hr'])); names = [r['tool'] for r in W] + ['lean-align (32 thr.)']
fig, ax = plt.subplots(2, 1, figsize=(8, 6), sharex=True)
for a, col, yl in zip(ax, ('Gbp_hr', 'peak_GB'), ('speed (Gbp/hour, 32 threads)', 'peak memory (GB)')):
    bars(a, names, ['t'], lambda g, s: next((num(r[col]) for r in W if r['tool'] == g), None), fmt='{:.1f}', colors={'t': C['other']}, width=.7, miss='not measured yet'); a.set_ylabel(yl)
    for p, n in zip(a.patches, names):
        if n == 'minibwa': p.set_color(C['minibwa'])
        if n.startswith('lean-align'): p.set_edgecolor(C['lean-align'])
ax[1].tick_params(axis='x', rotation=30); fig.suptitle("minibwa paper Fig. 3, HG002 NovaSeq 30x WGS, 2 x Xeon Gold 6130, as published", fontsize=9, y=.995); save(fig, 'h_paper_fig3_wgs')
print('wrote', sorted(os.listdir(O)))
