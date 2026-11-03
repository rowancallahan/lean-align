#!/usr/bin/env python3
"""Malformed-output check of lean-align's SAM against its own inputs. Zero violations tolerated (exit 1 otherwise).
   python3 -I sam_fuzz_check.py [--xfail=no-aligned-base] [--xfail=short-mate] OURS.sam R1.fq R2.fq CHROMOSOMES [CALMD.sam]
Per record: FLAG bits, '*'/0 fields of unmapped records, CIGAR syntax (M I D only, no zero length, no adjacent equal
ops), CIGAR query length == len(SEQ), len(QUAL) == len(SEQ), alphabet and quality range, position inside the chromosome.
Per pair: order and QNAME against the FASTQ, mate flags (0x20 vs mate strand, 0x8 vs mate unmapped, 0x40/0x80), RNEXT/PNEXT
against the mate, TLEN (= -mate's, magnitude = span of both alignments, positive on the leftmost), proper-pair = opposite
strands, same tags and MAPQ rule (60 iff XU unique, else 0), '*' SEQ/QUAL only on a mate marked XT:Z:trimmedAway1/2.
Provenance: the printed SEQ/QUAL (reverse-complemented/reversed on the reverse strand) is a contiguous window of the FASTQ
read with the matching qualities, A/C/G/T only (the trimmer's proved property).
CALMD.sam (optional, `samtools calmd` output of the same records): mapped records with only M ops and no N: AS == -4*NM
(counts reported as information, not as violations)."""
import re, sys, collections
# --xfail=KEY: a rule known to fail until a fix lands. Its hits are reported as XFAIL and do not fail the run; when it has no hits the run
# prints XPASS (the fix landed: delete the flag). KEYs: no-aligned-base (a mapped CIGAR with no aligned base, the 150I placeholders),
# short-mate (a mapped mate trimmed below 20 letters from an input of 20 or more, e.g. the all-'#' read cut to 1 letter).
XFAIL_RULES = {'no-aligned-base': 'mapped record whose CIGAR has no aligned base (no M)',
               'short-mate': 'mapped mate trimmed to fewer than 20 letters (input had 20 or more)'}
xfail = [a[8:] for a in sys.argv[1:] if a.startswith('--xfail=')]
assert all(k in XFAIL_RULES for k in xfail), f'unknown --xfail key; known: {sorted(XFAIL_RULES)}'
args = [a for a in sys.argv[1:] if not a.startswith('--')]
sam, f1, f2, chrfile = args[:4]
calmd = args[4] if len(args) > 4 else None
chroms = {l.split('\t')[0]: int(l.split('\t')[1]) for l in open(chrfile).read().split('\n') if l}
def fastq(p):
    L = open(p).read().split('\n'); assert len(L) % 4 == 1 and L[-1] == '', p
    return [(L[i][1:], L[i + 1], L[i + 3]) for i in range(0, len(L) - 1, 4)]
R = {1: fastq(f1), 2: fastq(f2)}
assert len(R[1]) == len(R[2])
def mate_name(n):
    b = n.split(' ')[0]
    return b[:-2] if b.endswith('/1') or b.endswith('/2') else b
RC = str.maketrans('ACGTN', 'TGCAN')
viol, ex = collections.Counter(), collections.defaultdict(list)
def bad(rule, qn, detail=''):
    viol[rule] += 1
    if len(ex[rule]) < 3: ex[rule].append(f'{qn} {detail}'.strip())
OPS = re.compile(r'(\d+)([MIDNSHP=X])')
def cig(c):
    if c == '*': return None
    ops = OPS.findall(c)
    if ''.join(n + o for n, o in ops) != c: return 'syntax'
    return [(int(n), o) for n, o in ops]
info = collections.Counter()
warn = collections.Counter(); wex = []; wex2 = []
nm = {}
if calmd:
    for l in open(calmd):
        if l[0] == '@': continue
        r = l.rstrip('\n').split('\t'); t = {x[:2]: x[5:] for x in r[11:]}
        if 'NM' in t: nm[(r[0], int(r[1]) & 192)] = (int(t['NM']), t.get('MD'))
n_pairs = 0
recs = []
for l in open(sam):
    if l[0] != '@': recs.append(l.rstrip('\n').split('\t'))
if len(recs) != 2 * len(R[1]): bad('record count != 2 x FASTQ pairs', '', f'{len(recs)} vs {2 * len(R[1])}')
def parse(r, mate, i):
    qn, flag, rname, pos, mapq, cigar, rnext, pnext, tlen, seq, qual = r[:11]
    d = dict(qn=qn, flag=int(flag), rname=rname, pos=int(pos), mapq=int(mapq), cigar=cigar, rnext=rnext, pnext=int(pnext),
             tlen=int(tlen), seq=seq, qual=qual, tags={t[:2]: t[5:] for t in r[11:]}, tagorder=[t[:2] for t in r[11:]])
    d['mapped'] = not d['flag'] & 4; d['rev'] = bool(d['flag'] & 16)
    return d
pairs = 0
for i in range(min(len(R[1]), len(recs) // 2)):
    a, b = parse(recs[2 * i], 1, i), parse(recs[2 * i + 1], 2, i)
    qn = R[1][i][0]
    if mate_name(R[1][i][0]) != mate_name(R[2][i][0]): bad('FASTQ mates differ in name', qn)
    pairs += 1
    for mate, d in ((1, a), (2, b)):
        o_name, o_seq, o_qual = R[mate][i]
        if d['qn'] != mate_name(o_name): bad('QNAME != FASTQ name (order or content)', d['qn'], mate_name(o_name))
        f = d['flag']
        if not f & 1: bad('0x1 not set', qn)
        if (f & 64 != 0) != (mate == 1) or (f & 128 != 0) != (mate == 2): bad('0x40/0x80 wrong for the mate', qn, str(f))
        if f & (256 | 512 | 1024 | 2048 | ~0xFFF): bad('secondary/QC/dup/supplementary flag set', qn, str(f))
        if d['seq'] == '*':
            if d['qual'] != '*': bad('SEQ * but QUAL not *', qn)
            if d['mapped']: bad('mapped record with SEQ *', qn)
        else:
            if len(d['qual']) != len(d['seq']): bad('len(QUAL) != len(SEQ)', qn, f"{len(d['qual'])} {len(d['seq'])}")
            if not re.fullmatch('[ACGTN]+', d['seq']): bad('SEQ outside ACGTN', qn)
            if len(d['seq']) < 20: warn['mate shortened to fewer than 20 letters by trimming (still aligned/printed)'] += 1; wex2.append(f"{qn} len {len(d['seq'])} {d['cigar']}") if len(wex2) < 3 else None
            if d['mapped'] and len(d['seq']) < 20 <= len(o_seq): bad(XFAIL_RULES['short-mate'], qn, f"len {len(d['seq'])} of {len(o_seq)} {d['cigar']}")
            if not all(33 <= ord(c) <= 126 for c in d['qual']): bad('QUAL outside 33..126', qn)
        # provenance and trimming
        if d['seq'] == '*':
            if not any(k.startswith('trimmedAway') for k in [d['tags'].get('XT', '')]): bad('SEQ * without XT:Z:trimmedAway', qn)
            if len(o_seq) == 0: pass
        else:
            w = d['seq'].translate(RC)[::-1] if d['rev'] and d['mapped'] else d['seq']
            wq = d['qual'][::-1] if d['rev'] and d['mapped'] else d['qual']
            if 'N' in w: bad('trimmed window contains N (proved A/C/G/T only)', qn)
            ok, p = False, o_seq.find(w)
            while p >= 0 and not ok:
                ok = o_qual[p:p + len(w)] == wq; p = o_seq.find(w, p + 1)
            if not ok: bad('SEQ/QUAL are not a window of the FASTQ read (strand-corrected)', qn)
        if d['mapped']:
            c = cig(d['cigar'])
            if c is None: bad('mapped record with CIGAR *', qn)
            elif c == 'syntax': bad('CIGAR syntax', qn, d['cigar'])
            else:
                if any(n == 0 for n, _ in c): bad('zero-length CIGAR op', qn, d['cigar'])
                if any(o not in 'MID' for _, o in c): bad('CIGAR op outside M/I/D', qn, d['cigar'])
                if any(c[k][1] == c[k + 1][1] for k in range(len(c) - 1)): bad('adjacent equal CIGAR ops', qn, d['cigar'])
                if not any(o in 'M=X' for _, o in c): bad(XFAIL_RULES['no-aligned-base'], qn, f"{d['rname']}:{d['pos']} {d['cigar']} MAPQ {d['mapq']} {d['tags'].get('XT')}")
                elif c[0][1] != 'M' or c[-1][1] != 'M':
                    warn['CIGAR starts or ends with I/D (legal SAM, validators dislike it)'] += 1
                    if len(wex) < 3: wex.append(f"{qn} {d['cigar']}")
                q = sum(n for n, o in c if o in 'MIS=X'); d['reflen'] = sum(n for n, o in c if o in 'MDN=X')
                if d['seq'] != '*' and q != len(d['seq']): bad('CIGAR query length != len(SEQ)', qn, f"{d['cigar']} {len(d['seq'])}")
                if d['rname'] not in chroms: bad('RNAME not in the genome', qn, d['rname'])
                elif d['pos'] < 1 or d['pos'] - 1 + d['reflen'] > chroms[d['rname']]: bad('alignment outside the chromosome', qn, f"{d['rname']}:{d['pos']} {d['cigar']}")
            if not 0 <= d['mapq'] <= 255: bad('MAPQ range', qn)
        else:
            if (d['rname'], d['pos'], d['mapq'], d['cigar'], d['rnext'], d['pnext'], d['tlen']) != ('*', 0, 0, '*', '*', 0, 0):
                bad('unmapped record with non-default RNAME/POS/MAPQ/CIGAR/RNEXT/PNEXT/TLEN', qn)
    # pair level
    if a['mapped'] != b['mapped']: info['half-mapped pair'] += 1
    for x, y in ((a, b), (b, a)):
        if bool(x['flag'] & 8) != (not y['mapped']): bad('0x8 != mate unmapped', qn)
        if x['mapped'] and y['mapped']:
            if bool(x['flag'] & 32) != y['rev']: bad('0x20 != mate strand', qn)
            if x['rnext'] != ('=' if x['rname'] == y['rname'] else y['rname']): bad('RNEXT != mate RNAME', qn)
            if x['pnext'] != y['pos']: bad('PNEXT != mate POS', qn)
            if not x['flag'] & 2: bad('both mapped but 0x2 not set', qn)
    if a['mapped'] and b['mapped']:
        if a['rname'] == b['rname'] and 'reflen' in a and 'reflen' in b:
            left = min(a['pos'], b['pos']); right = max(a['pos'] + a['reflen'], b['pos'] + b['reflen'])
            span = right - left
            if abs(a['tlen']) != span or abs(b['tlen']) != span: bad('|TLEN| != span of the two alignments', qn, f"{a['tlen']} {b['tlen']} span {span}")
            if a['tlen'] != -b['tlen']: bad('TLEN of the mates not opposite', qn)
            a_left = a['pos'] <= b['pos']
            if (a['tlen'] > 0) != a_left or (b['tlen'] > 0) == a_left: bad('TLEN sign: positive must be the leftmost mate (mate 1 on ties)', qn)
        if a['rev'] == b['rev']: bad('proper pair with both mates on one strand', qn)
        if a['tags'].get('XU') is None: bad('mapped without XU', qn)
    else:
        for d in (a, b):
            if d['flag'] & 2: bad('0x2 set on a pair that is not mapped', qn)
    # tags
    for d in (a, b):
        t = d['tags']
        if d['mapped']:
            if d['tagorder'] != ['AS', 'XB', 'XU', 'XT']: bad('mapped record tags != AS XB XU XT', qn, str(d['tagorder']))
            elif not re.fullmatch(r'-?\d+', t['AS']) or int(t['AS']) > 0: bad('AS not a non-positive integer', qn, t['AS'])
        else:
            if t.get('XT', '').startswith('trimmedAway'):
                if d['tagorder'] != ['XT']: bad('trimmedAway record has other tags', qn, str(d['tagorder']))
                if d['flag'] not in (77, 141): bad('trimmedAway record flag != 77/141', qn, str(d['flag']))
            elif d['tagorder'] != ['XB', 'XU', 'XT']: bad('unmapped record tags != XB XU XT (or XT trimmedAway)', qn, str(d['tagorder']))
            elif d['flag'] not in (77, 141): bad('unmapped record flag != 77/141', qn, str(d['flag']))
        if 'XB' in t and not (re.fullmatch(r'-?\d+', t['XB']) and int(t['XB']) <= 0): bad('XB not a non-positive integer', qn, t['XB'])
        if 'XU' in t and t['XU'] not in ('unique', 'multimapper', 'unknown'): bad('XU value', qn, t['XU'])
        if d['mapped'] and d['mapq'] != (60 if t.get('XU') == 'unique' else 0): bad('MAPQ != 60 iff XU unique', qn, f"{d['mapq']} {t.get('XU')}")
        if not d['mapped'] and 'XU' in t and t['XU'] == 'unique': bad('XU unique on an unmapped record', qn)
    if a['mapped'] and b['mapped'] and (a['tags'].get('XU'), a['tags'].get('XB'), a['tags'].get('XT')) != (b['tags'].get('XU'), b['tags'].get('XB'), b['tags'].get('XT')):
        bad('mates carry different XU/XB/XT', qn)
    # trimmedAway tag vs the mate it names
    for d in (a, b):
        xt = d['tags'].get('XT', '')
        if xt.startswith('trimmedAway'):
            m = int(xt[-1])
            named = a if m == 1 else b
            if named['seq'] != '*': bad('XT trimmedAway names a mate that still has SEQ', qn, xt)
            if m == 2 and a['seq'] == '*' : bad('trimmedAway2 but mate 1 is also gone (should say trimmedAway1)', qn)
    # calmd cross-check
    if calmd:
        for d, mate in ((a, 1), (b, 2)):
            if d['mapped'] and (d['qn'], d['flag'] & 192) in nm and re.fullmatch(r'\d+M', d['cigar']):
                n_m, md = nm[(d['qn'], d['flag'] & 192)]
                w = d['seq']
                if 'N' in w: info['calmd: M-only with N in read (not compared)'] += 1
                elif int(d['tags']['AS']) == -4 * n_m: info['calmd: M-only, AS == -4*NM'] += 1
                else: info['calmd: M-only, AS != -4*NM'] += 1; ex['info AS != -4*NM'].append(f"{d['qn']} AS {d['tags']['AS']} NM {n_m}") if len(ex['info AS != -4*NM']) < 3 else None
print(f'{pairs} pairs, {len(recs)} records checked against {f1.split("/")[-1]} / {f2.split("/")[-1]}')
expected = {r: viol.pop(r) for r in list(viol) if r in [XFAIL_RULES[k] for k in xfail]}
if viol:
    print('VIOLATIONS (must be zero):')
    for r, n in viol.most_common(): print(f'  {n:8d}  {r}   e.g. {ex[r][0] if ex[r] else ""}')
else:
    print('VIOLATIONS: none')
for k in xfail:
    r = XFAIL_RULES[k]
    if r in expected: print(f'  XFAIL (expected until the fix lands, --xfail={k}): {expected[r]} x "{r}"   e.g. {ex[r][0]}')
    else: print(f'  XPASS (--xfail={k}): "{r}" has no hits any more: the fix landed, delete the flag so this rule is enforced')
for k, v in sorted(warn.items()): print(f'  WARNING: {k}: {v}   e.g. {wex2 if "fewer" in k else wex}')
for k, v in sorted(info.items()): print(f'  info: {k}: {v}')
for k in ex:
    if k.startswith('info'): print(f'  e.g. {k}: {ex[k]}')
sys.exit(1 if viol else 0)
