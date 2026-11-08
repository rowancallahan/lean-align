#!/usr/bin/env python3
"""Edge-case paired FASTQ for the SAM/BAM fuzz run (valid FASTQ: A/C/G/T/N, Phred+33, equal SEQ/QUAL lengths).
   python3 -I fuzz_reads.py GENOME.upper.fa OUT_PREFIX [PAIRS_PER_CATEGORY=150] [SEED=1]  ->  OUT_PREFIX_R1.fq / _R2.fq
Categories (the read names say which): normal pairs with errors and indels; bad-quality tails/heads and noisy qualities (trimmed);
adapter-like tails; one mate or both trimmed away; all-N and N-rich reads; reads of 1..101 letters; long reads (400..1000, the spec's limit);
mates of different lengths; same-strand mates; mates far apart; mates on different chromosomes; random non-genomic reads;
identical mates; mate 2 left of mate 1; duplicated pairs; reads next to N runs and at chromosome ends; names with comments."""
import mmap, random, sys
fa, pre = sys.argv[1:3]
per = int(sys.argv[3]) if len(sys.argv) > 3 else 150
random.seed(int(sys.argv[4]) if len(sys.argv) > 4 else 1)
genome_file = open(fa, 'rb')
G = mmap.mmap(genome_file.fileno(), 0, access=mmap.ACCESS_READ)
chrom, i = [], 0    # [name, first sequence byte, line width, length]
while i < len(G):
    j = G.find(b'\n', i); k = G.find(b'\n', j + 1); e = G.find(b'\n>', j); e = len(G) if e < 0 else e + 1
    chrom.append([G[i + 1:j].split()[0].decode(), j + 1, k - j - 1, (e - j - 1) - G[j + 1:e].count(b'\n')]); i = e
main = [c for c in chrom if c[0] in {f'chr{x}' for x in list(range(1, 23)) + ['X']}]
def sub(c, pos, n):   # letters [pos, pos+n) of chromosome c
    _, s, w, _ = c
    return G[s + pos + pos // w:s + pos + n + (pos + n) // w + 1].replace(b'\n', b'')[:n].decode()
def window(n):        # an N-free window of n letters at a random place: (chromosome, position, letters)
    while True:
        c = random.choices(main, [m[3] for m in main])[0]; p = random.randrange(0, c[3] - n); s = sub(c, p, n)
        if 'N' not in s: return c, p, s
RC = str.maketrans('ACGTN', 'TGCAN')
rc = lambda s: s.translate(RC)[::-1]
def mutate(s, sub_rate=0.01, indel_rate=0.002):
    out = []
    for ch in s:
        r = random.random()
        if r < sub_rate: out.append(random.choice('ACGT'))
        elif r < sub_rate + indel_rate / 2: pass
        elif r < sub_rate + indel_rate: out += [ch, random.choice('ACGT')]
        else: out.append(ch)
    return ''.join(out) or 'A'
def qual(n, kind='good'):
    if kind == 'good': return ''.join(chr(33 + random.choice([40, 40, 40, 39, 38, 37, 34, 30])) for _ in range(n))
    if kind == 'bad': return '#' * n
    if kind == 'mixed': return ''.join(chr(33 + random.randint(2, 41)) for _ in range(n))
    k = random.randint(1, max(1, n // 2)); low = ''.join(chr(33 + random.randint(2, 10)) for _ in range(k))
    return qual(n - k) + low if kind == 'tail' else low + qual(n - k)    # 'tail' or 'head'
pairs, cnt = [], {}
def add(cat, s1, q1, s2, q2, comment=''):
    assert s1 and s2 and len(s1) == len(q1) and len(s2) == len(q2)
    cnt[cat] = cnt.get(cat, 0) + 1
    pairs.append((f'{cat}_{cnt[cat]}' + (' ' + comment if comment else ''), s1, q1, s2, q2))
def frag(n1, n2, flen):     # an FR pair from one fragment: (mate 1, mate 2)
    s = window(flen)[2]; return s[:n1], rc(s[-n2:])
def good(cat, a, b, qa='good', qb='good', **kw): add(cat, a, qual(len(a), qa), b, qual(len(b), qb), **kw)
for _ in range(per):
    n = random.choice([75, 100, 125, 150, 151, 250]); a, b = frag(n, n, random.randint(n + 100, n + 350)); good('normal', mutate(a), mutate(b))
for kind in ('tail', 'head', 'mixed'):
    for _ in range(per):
        n = random.choice([100, 150, 250]); a, b = frag(n, n, 400); good('trim_' + kind, mutate(a), mutate(b), kind, kind)
for _ in range(per):
    a, b = frag(150, 150, 400); ad = 'AGATCGGAAGAGCACACGTCTGAACTCCAGTCA'; k = random.randint(10, 60)
    good('adapter_tail', (a[:150 - k] + ad)[:150], (b[:150 - k] + ad)[:150], 'tail', 'tail')
for _ in range(per):
    a, b = frag(150, 150, 400); good('mate2_trimmed_away', a, b, 'good', 'bad'); good('mate1_trimmed_away', a, b, 'bad', 'good')
for _ in range(per):
    n = random.choice([50, 150, 250]); good('both_trimmed_away', ''.join(random.choices('ACGT', k=n)), ''.join(random.choices('ACGT', k=n)), 'bad', 'bad')
for n in (1, 10, 150):
    for _ in range(per // 3): good(f'all_N_{n}', 'N' * n, 'N' * n)
for _ in range(per):
    a, b = frag(150, 150, 400); good('N_rich', ''.join('N' if random.random() < 0.15 else x for x in a), ''.join('N' if random.random() < 0.05 else x for x in b))
for n in (1, 2, 3, 5, 10, 17, 20, 24, 25, 26, 30, 31, 49, 50, 51, 74, 75, 76, 99, 100, 101):
    for _ in range(max(2, per // 20)):
        a, b = frag(n, n, n + 150); good(f'short{n}', a, b)
for n in (400, 500, 700, 1000):
    for _ in range(max(3, per // 30)):
        a, b = frag(n, n, n + 150); good(f'long{n}', mutate(a)[:1000], b)   # FQ.Record.valid: at most 1000 bases
for _ in range(per):
    n1, n2 = random.choice([(50, 150), (150, 90), (30, 250), (100, 101)]); a, b = frag(n1, n2, 350); good('lengths_differ', a, b)
for _ in range(per):
    s = window(450)[2]; good('same_strand', s[:150], s[200:350])
for _ in range(per):
    s = window(2500)[2]; good('far_apart', s[:150], rc(s[-150:]))
for _ in range(per): good('diff_chrom', window(150)[2], rc(window(150)[2]))
for _ in range(per):
    n = random.choice([30, 100, 150, 250]); good('random_seq', ''.join(random.choices('ACGT', k=n)), ''.join(random.choices('ACGT', k=n)))
for _ in range(per // 2):
    s = window(150)[2]; good('identical_mates', s, s); good('mates_reverse_complements', s, rc(s))
for _ in range(per // 2):
    a, b = frag(150, 150, 400); good('mate2_left_of_mate1', rc(b), rc(a))
for _ in range(per // 2):
    a, b = frag(100, 100, 300); qa, qb = qual(100), qual(100)
    for _ in range(3): add('duplicate', a, qa, b, qb)
for c in main[:12]:   # chromosome ends (N runs of the genome replaced by A)
    s, e = sub(c, 0, 400).replace('N', 'A'), sub(c, c[3] - 400, 400).replace('N', 'A')
    good('chrom_start', s[:150], rc(s[150:300])); good('chrom_end', e[-300:-150], rc(e[-150:]))
for _ in range(per // 2):   # reads that overlap the genome's N runs
    c = random.choice(main); s = sub(c, 0, 20000); p = s.find('N') if 'N' in s else 0
    w = sub(c, max(0, p - 75), 150); good('near_genome_N', w, rc(w))
for _ in range(per // 2):
    a, b = frag(150, 150, 400); good('named_with_comment', a, b, comment='1:N:0:ACGT extra comment')
random.shuffle(pairs)
with open(pre + '_R1.fq', 'w') as o1, open(pre + '_R2.fq', 'w') as o2:
    for i, (name, s1, q1, s2, q2) in enumerate(pairs):
        o1.write(f'@{i}_{name}\n{s1}\n+\n{q1}\n'); o2.write(f'@{i}_{name}\n{s2}\n+\n{q2}\n')
print(len(pairs), 'pairs;', ', '.join(f'{k}:{v}' for k, v in sorted(cnt.items())))
