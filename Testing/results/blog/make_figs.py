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
# vs_minibwa: ONLY current lean-align vs minibwa, every single run from reps.tsv. bar = median, whisker = min to max (none for n = 1), dots = single runs.
RP = tsv('reps'); SC = ['lean-align', 'minibwa']; DSN = ['novaseq_2x151', 'hiseq_2x250']
def src(exp, ds):   # streamed column: same-method repetition rows ('stream') where a data set has them, else the older single runs ('stream_single')
    return 'stream_single' if exp == 'stream' and not any(r['experiment'] == 'stream' and r['data'] == ds for r in RP) else exp
def runs_of(exp, ds, tool, col): return sorted(x for x in (num(r[col]) for r in RP if r['experiment'] == src(exp, ds) and r['data'] == ds and r['tool'] == tool) if x is not None)
def rep_panel(ax, exp, col, top, fmt='{:.1f}'):
    w = .36
    for i, d in enumerate(DSN):
        for j, t in enumerate(SC):
            x = i + (j - .5) * w * 1.15; v = runs_of(exp, d, t, col); n = len(v)
            if n:
                m = st.median(v); ax.bar(x, m, w, color=C[t], alpha=.9, zorder=2)
                if n > 1: ax.errorbar(x, m, yerr=[[m - v[0]], [v[-1] - m]], color='#222', capsize=4, lw=1.2, zorder=3)
                ax.scatter([x + (k - (n - 1) / 2) * .035 for k in range(n)], v, s=9, color='#111', zorder=4)
                ax.text(x, v[-1] + top * .02, fmt.format(m), ha='center', va='bottom', fontsize=8, zorder=5)
            else: ax.bar(x, top * .9, w, fill=False, edgecolor=C[t], lw=1, ls='--'); ax.text(x, top * .45, 'no runs', rotation=90, ha='center', va='center', fontsize=7.5)
            ax.text(x, -.035, f'n={n}', transform=ax.get_xaxis_transform(), ha='center', va='top', fontsize=7.5, color='#444')
    ax.set_xticks(range(len(DSN))); ax.set_xticklabels([DS[d] for d in DSN]); ax.tick_params(axis='x', pad=14); ax.set_ylim(0, top * 1.14); ax.set_xlim(-.6, len(DSN) - .4)
def sizes(ds): return sorted({int(r['pairs']) for r in RP if r['experiment'] == src('stream', ds) and r['data'] == ds})
def nruns(ds): return [len(runs_of('stream', ds, t, 'wall_s')) for t in SC]
def srs(d): return ' [container restart between runs: the spread is mostly the restart]' if any('container restarted' in r['source'] for r in RP if r['experiment'] == src('stream', d) and r['data'] == d) else ''
def sdesc(d):
    n = nruns(d); per = (f"{n[0]} run{'s' if n[0] != 1 else ''} per tool") if n[0] == n[1] else f'{n[0]} and {n[1]} runs'
    return f"{DS[d].split()[0]} " + (f"first {', '.join(f'{p / 1e6:.3g}M' for p in sizes(d))} pairs, {per}" if src('stream', d) == 'stream' else f"{', '.join(f'{p / 1e6:.3g}M' for p in sizes(d))} pairs (older single runs), {per}") + srs(d)
foot = lambda: 'bar = median, whisker = min to max, dots = single runs, 4 threads, n = runs.\nstreamed: ' + '\nstreamed: '.join(sdesc(d) for d in DSN if sizes(d))
def commits(tool, exp):   # build(s) of a tool among the rows plotted in one column
    seen = []
    for d in DSN:
        for r in RP:
            if r['tool'] == tool and r['experiment'] == src(exp, d) and r['data'] == d and r['commit'] not in seen: seen.append(r['commit'])
    return seen
def tool_label(tool):    # the legend names the build(s) actually plotted
    g, t = commits(tool, 'gz5m'), commits(tool, 'stream')
    return f"{tool} ({'/'.join(g)})" if g == t or not t else f"{tool} (gz {'/'.join(g)}, streamed {'/'.join(t)})"
def vs_fig(rows, name, h):
    fig, ax = plt.subplots(len(rows), 2, figsize=(9, h), sharey='row', squeeze=False)
    for r, (col, yl) in enumerate(rows):
        top = max([max(runs_of(e, d, t, col) or [0]) for e in ('gz5m', 'stream') for d in DSN for t in SC] + [1e-9])
        for c, exp in enumerate(('gz5m', 'stream')): rep_panel(ax[r][c], exp, col, top)
        ax[r][0].set_ylabel(yl)
    ax[0][0].set_title('gzipped files, 5M pairs', fontsize=9); ax[0][1].set_title('streamed from the network', fontsize=9)
    fig.legend(handles=[plt.Rectangle((0, 0), 1, 1, color=C[t]) for t in SC], labels=[tool_label('lean-align'), tool_label('minibwa')], loc='lower center', ncol=2, frameon=False, fontsize=8.5, bbox_to_anchor=(.5, .075))
    fig.text(.5, .008, foot(), ha='center', va='bottom', fontsize=7, color='#444'); fig.tight_layout(rect=(0, .14, 1, 1)); [fig.savefig(f'{O}/{name}.{e}', dpi=150) for e in ('svg', 'png')]; plt.close(fig)
vs_fig([('Gbp_hr', 'speed (Gbp/hour)'), ('Gbp_core_hr', 'Gbp per core-hour')], 'vs_minibwa', 7.4)
vs_fig([('peak_GB', 'peak memory (GB)')], 'vs_minibwa_memory', 4.2)
# this round: lean-align new build against the previous build, same session (wall and CPU from reps.tsv, instructions from this_round.tsv)
TR = tsv('this_round')
def med(exp, ds, col): return (lambda v: st.median(v) if v else None)(runs_of(exp, ds, 'lean-align', col))
def prevnew(ds):
    out = []
    for lab, col in (('wall time', 'wall_s'), ('CPU (incl. gzips)', 'cpu_s')):
        a, b = med('gz5m_prev_build', ds, col), med('gz5m', ds, col)
        if a and b: out.append((lab, 100 * (b / a - 1)))
    t = [num(r['change_pct']) for r in TR if r['data'] == ds and r['metric'] == 'instructions']
    if t: out.append(('instructions', t[0]))
    return out
PN = [(d, prevnew(d)) for d in DSN if prevnew(d)]
if PN:
    labs = ['wall time', 'CPU (incl. gzips)', 'instructions']; newb = '/'.join(sorted({r['commit'] for r in RP if r['experiment'] == 'gz5m' and r['tool'] == 'lean-align'})); prevb = '/'.join(sorted({r['commit'] for r in RP if r['experiment'] == 'gz5m_prev_build'}))
    fig, ax = plt.subplots(figsize=(6.2, 3.6)); w = .8 / len(PN); done = set()
    for j, (d, vals) in enumerate(PN):
        for i, lab in enumerate(labs):
            v = dict(vals).get(lab)
            if v is None: continue
            x = i + (j - (len(PN) - 1) / 2) * w
            ax.bar(x, v, w * .92, color=C['lean-align'] if j == 0 else C['lean-align-before'], label=DS[d] if d not in done else None); done.add(d)
            ax.text(x, v - 0.5, f'{v:.1f}%', ha='center', va='top', fontsize=8)
    ax.set_xticks(range(len(labs))); ax.set_xticklabels(labs); ax.axhline(0, color='#222', lw=.8); ax.set_ylabel(f'change, {newb} vs {prevb} (%)')
    ax.set_ylim(min(v for _, vals in PN for _, v in vals) - 4, 2); ax.legend(frameon=False, fontsize=8, loc='lower right')
    fig.text(.5, .01, 'wall, CPU: medians of 3 alternating runs, same session, 5M gz pairs, 4 threads;  instructions: callgrind, 50k pairs, 1 thread', ha='center', fontsize=6.5, color='#444')
    fig.tight_layout(rect=(0, .04, 1, 1)); [fig.savefig(f'{O}/this_round.{e}', dpi=150) for e in ('svg', 'png')]; plt.close(fig)
# (a) speed at 4 threads, 5M pairs, gz. Two methods, two columns: A = before/after on the same method (gz5m: map time, index load excluded);
#     B = ours vs minibwa with the same script for both tools (gz5m_script: wall incl. index load, CPU incl. both gzips).
SC = ['lean-align', 'minibwa']
fig, ax = plt.subplots(2, 2, figsize=(10, 6.2))
for r, (col, yl) in enumerate((('Gbp_hr', 'Gbp/hour'), ('Gbp_core_hr', 'Gbp per core-hour'))):
    bars(ax[r][0], list(DS), T3[:2], lambda g, s: pick(experiment='gz5m', data=g, tool=s)(col), fmt='{:.1f}'); ax[r][0].set_ylabel(yl)
    bars(ax[r][1], list(DS), SC, lambda g, s: pick(experiment='gz5m_script', data=g, tool=s)(col), fmt='{:.1f}')
    [a.set_xticklabels(list(DS.values())) for a in ax[r]]
ax[0][0].set_title('A: before / after, same method\n(map time, index load excluded; 3-run median)', fontsize=8.5)
ax[0][1].set_title('B: lean-align vs minibwa, same script (Testing/ec2/run.sh)\n(wall incl. index load, CPU incl. both gzips; 3-run median)', fontsize=8.5)
fig.legend(handles=[plt.Rectangle((0, 0), 1, 1, color=C[t]) for t in T3], labels=[LAB[t] for t in T3], loc='lower center', ncol=3, frameon=False, fontsize=8)
fig.suptitle('5M pairs from gz files, 4 cores', fontsize=9, y=.995); fig.tight_layout(rect=(0, .05, 1, 1)); [fig.savefig(f'{O}/a_speed_4threads.{e}', dpi=150) for e in ('svg', 'png')]; plt.close(fig)
# (b) peak memory. Left: 5M gz, same script for both tools. Right: streamed runs and whole lanes (lane rows first, then stream rows).
def peak(data, pairs, tool):
    for e in ('lane', 'stream'):
        v = pick(experiment=e, data=data, pairs=pairs, tool=tool)('peak_GB')
        if v is not None: return v
G = [('NovaSeq 20M', 'novaseq_2x151', 20000000), ('HiSeq 34M lane', 'hiseq_2x250', 33916091), ('NovaSeq 40M', 'novaseq_2x151', 40000000)]
fig, ax = plt.subplots(1, 2, figsize=(10, 3.8), gridspec_kw={'width_ratios': [1, 1.5]})
bars(ax[0], list(DS), SC, lambda g, s: pick(experiment='gz5m_script', data=g, tool=s)('peak_GB'), fmt='{:.1f}'); ax[0].set_xticklabels(list(DS.values())); ax[0].set_title('5M pairs from gz, same script for both tools', fontsize=8.5)
bars(ax[1], [g[0] for g in G], T3, lambda lab, s: (lambda g: peak(g[1], g[2], s))([g for g in G if g[0] == lab][0]), fmt='{:.1f}'); ax[1].set_title('streamed runs and whole lanes', fontsize=8.5)
for a in ax: a.set_ylabel('peak memory (GB)'); a.set_ylim(0, 11.5)
legend(ax[1], T3, loc='upper left'); save(fig, 'b_memory')
# (c) throughput vs run size (streamed NovaSeq), and whole lanes: before / after / minibwa
def rate(data, pairs, tool, col):
    for e in ('lane', 'stream'):
        v = pick(experiment=e, data=data, pairs=pairs, tool=tool)(col)
        if v is not None: return v
fig, ax = plt.subplots(1, 3, figsize=(13.5, 3.8), gridspec_kw={'width_ratios': [1, 1, 1.15]})
for a, col, yl in zip(ax[:2], ('Gbp_hr', 'Gbp_core_hr'), ('Gbp/hour (4 cores)', 'Gbp per core-hour')):
    for s in T3:
        pts = sorted((num(r['pairs']) / 1e6, num(r[col]), 'cold index load' in r['source']) for r in R if r['experiment'] == 'stream' and r['tool'] == s and num(r[col]) is not None)
        if pts: a.plot([p[0] for p in pts], [p[1] for p in pts], 'o-', color=C[s], label=LAB[s]); [a.annotate(f'{y:.1f}' + ('*' if cold else ''), (x, y), textcoords='offset points', xytext=(0, 5), ha='center', fontsize=7.5) for x, y, cold in pts]
    a.set_xlabel('pairs streamed (millions, NovaSeq)'); a.set_ylabel(yl); a.set_xticks([10, 20, 40]); a.set_ylim(bottom=0)
ax[0].legend(fontsize=7.5, frameon=False, loc='lower right'); ax[1].text(.98, .02, '* wall includes a cold index load (see runs.tsv)', transform=ax[1].transAxes, ha='right', fontsize=7, color='#444')
LG = [('HiSeq lane\n33.9M pairs', 'hiseq_2x250', 33916091), ('NovaSeq\n40M pairs', 'novaseq_2x151', 40000000)]
bars(ax[2], [g[0] for g in LG], T3, lambda lab, s: (lambda g: rate(g[1], g[2], s, 'Gbp_hr'))([g for g in LG if g[0] == lab][0]), fmt='{:.1f}'); ax[2].set_ylabel('Gbp/hour (4 cores)'); ax[2].set_title('whole lanes', fontsize=8.5)
save(fig, 'c_throughput_vs_size')
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
# (f) accuracy / uniqueness vs minibwa. Real reads: 1M pairs each, f465a57 (Testing/ec2/compare.py); simulated: 100k pairs, f465a57.
E = tsv('ec2_compare'); ev = lambda **kw: next((num(r['value']) for r in E if all(r[k] == x for k, x in kw.items())), None)
A = tsv('accuracy'); v = lambda **kw: next((num(r['value']) for r in A if all(r[k] == x for k, x in kw.items())), None)
fig, ax = plt.subplots(1, 3, figsize=(14, 4), gridspec_kw={'width_ratios': [1, 1, 2.2]}); two = ['lean-align', 'minibwa']
for a, met, yl in ((ax[0], 'pct_mapped', 'mapped pairs (% of 1M pairs)'), (ax[1], 'pct_unique', 'unique pairs (% of 1M pairs)')):
    bars(a, list(DS), two, lambda g, s: ev(dataset=g, metric=met, tool=s), fmt='{:.1f}'); a.set_ylabel(yl); a.set_ylim(0, 112); a.set_xticklabels(list(DS.values()))
    a.set_title('real reads', fontsize=8.5)
cl = ['unique', 'unknown', 'not proper']; G = [f'{m} / {c}' for m in ('mason', 'low', 'high') for c in cl]
bars(ax[2], G, two, lambda g, s: v(block='sim', dataset=g.split(' / ')[0], **{'class': g.split(' / ')[1]}, metric='pct_pair_correct', tool=s), fmt='{:.0f}')
ax[2].set_ylabel('pairs placed correctly (%), by our class'); ax[2].set_ylim(0, 112); ax[2].tick_params(axis='x', rotation=60); [t.set_fontsize(6.5) for t in ax[2].texts]
ax[2].set_title('simulated reads, 100k pairs each', fontsize=8.5)
fig.legend(handles=[plt.Rectangle((0, 0), 1, 1, color=C[t]) for t in two], labels=['lean-align (f465a57)', LAB['minibwa']], loc='upper center', ncol=2, frameon=False, fontsize=8)
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
