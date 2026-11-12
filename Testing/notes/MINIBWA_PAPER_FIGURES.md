# minibwa paper (lh3/minibwa @ c07de5c, tex/): figures, tables, evaluation method

Source: `tex/minibwa.tex`, `perf.tsv`, `plot-perf.gp`, `Makefile`, `minibwa.bib`, `oup-authoring-template.cls`.
The repo has NO figure files (fig-prefetch.pdf, fig-roc.pdf, fig-perf are referenced but not committed) and no ROC data:
the only data behind a figure is `perf.tsv`. So there are no numbers for Fig. 2 (accuracy) in the repo.

## Figures and tables (captions verbatim)

**Table 1 (tab:relation)** "Relationship with BWA-MEM, ropebwt3 and minimap2"
Component | Source | Modification: FM-index BWA-MEM near identical; SMEM ropebwt3 reimplemented and batched; SA query ropebwt3 batched differently; Seeding BWA-MEM different algorithm; Chaining minimap2 adapted for variable-length seeds; Alignment minimap2 more frequent ungapped fast path; Pairing BWA-MEM ungapped fast path. No data file.

**Fig. 1 (fig:prefetch)** "Example of memory prefetch. (a) Standard backward search for three 5bp query strings. (r,i) denotes query r at its position i. Black arrows follow the computation order on a CPU. Red arrows indicate data access in RAM. (b) Batched backward search with prefetch." A schematic (fig-prefetch.pdf, not in repo). No data.

**Fig. 2 (fig:roc)** "Mapping accuracy measured on simulated reads. Short and long reads are simulated from GRCh38, T2T-CHM13 or the HG002 diploid genomes and are mapped to the corresponding source genomes with various read aligners. Suppose a read is originated from genomic interval G_s in simulation and is mapped to interval G_a by an aligner. It is considered mapped correctly if |G_s ∩ G_a|/|G_s ∪ G_a| ≥ 10%. Each point in the figures gives the fraction of mapped reads and the fraction of correctly mapped at a mapping quality threshold. (a) 2×150 bp paired-end reads simulated from GRCh38. (b) 2×150 bp paired-end reads simulated from T2T-CHM13. (c) Same reads in (b) but excluding reads from centromeres or acrocentric short arms. (d) Same reads in (a) but mapped in the methylation mode. (e) HiFi and Nanopore reads simulated from T2T-CHM13. (f) HiFi reads simulated from the diploid HG002 genome consisting of two haplotypes."
Plotted: ROC-style curve per aligner, x = fraction of reads mapped, y = fraction correctly mapped, one point per MAPQ threshold. Short-read panels: a, b, c (WGS), d (BS-seq aligners). Data file: none in the repo.

**Fig. 3 (fig:perf)** "Speed and peak memory on real data. Reads are aligned to GRCh38. 32 CPU threads are specified for all mappers except for Winnowmap2 which automatically uses all available CPUs. Dragmap crashed for Roche's SBX data. Alignment output is redirected to /dev/null except for Bismark which has to generate BAM files. The exact memory usage of Bismark could not be captured."
Plotted (plot-perf.gp, 2x3 multiplot, histograms): top row speed in Gbp/hr over 32 threads (y 0-160), bottom row peak memory in GB (y 0-140). Columns: short reads (WGS, SBX, Hi-C), long reads (HiFi, ONT), BS-seq. Data: `perf.tsv`, columns = dataset, tool, Gbp/hr, peak GB.
Short-read rows (WGS = HG002 NovaSeq 30x), Gbp/hr, GB:
| tool | speed | mem |
|---|---|---|
| bowtie2 | 34.37 | 4.06 |
| bwa-mem | 30.37 | 9.77 |
| bwa-mem2 | 50.79 | 26.02 |
| bwa-mem3 | 97.05 | 17.39 |
| bwa-meme | 74.57 | 131.26 |
| dragmap | 30.51 | 38.66 |
| minibwa | 135.82 | 8.28 |
| minimap2 | 60.89 | 12.93 |
| strobealign | 149.96 | 63.53 |
Hi-C: minibwa 101.22/8.60, bwa-mem 25.42/11.76, bwa-mem2 51.31/27.64, bwa-mem3 99.64/19.78, strobealign 75.08/44.96, minimap2 73.38/13.71, bowtie2 41.89/3.99, dragmap 24.86/39.72, bwa-meme 70.74/134.11.
SBX: minibwa 102.38/8.52, bwa-mem 27.73/8.42, bwa-mem2 39.51/25.47, bwa-mem3 90.31/17.00, strobealign 114.71/89.75, minimap2 82.27/13.36, bowtie2 28.27/5.24, bwa-meme 65.54/131.58, dragmap 0/0 (crashed).
Long/BS rows: HiFi minibwa 117.57/14.87, minimap2 77.04/24.97, rammap 84.78/17.62, winnowmap2 7.76/23.87; ONT minibwa 103.03/16.22, minimap2 83.76/25.78, rammap 88.67/17.00, winnowmap2 7.95/30.52; BS-seq bismark 3.50/0 (memory not captured), biscuit 12.89/24.64, bwa-meth 19.09/56.60, minibwa 50.17/15.35.
Text claims: minibwa about 4x BWA-MEM and >2x BWA-MEM2 on WGS; strobealign fastest (10% faster than minibwa); advantage narrows on Hi-C/SBX where mate rescue is disabled; minibwa <20 GB peak on all six datasets.

**Table 2 (tab:var)** "Short-read variant calling accuracy with DeepVariant" (note: FN false negative, FP false positive; bold = best per metric)
| aligner | SNP FN | SNP FP | Indel FN | Indel FP |
|---|---|---|---|---|
| minibwa | 48,579 | **6,811** | **36,459** | 5,288 |
| BWA-MEM | **46,895** | 7,585 | 37,425 | **5,218** |
| DRAGMAP | 47,539 | 6,949 | 37,415 | 5,304 |
| strobealign | 57,545 | 8,108 | 37,828 | 5,655 |
Method: HG002 short reads aligned to GRCh38, small variants called with DeepVariant v1.10.0, compared to GIAB Q100 truth v1.1 with RTG vcfeval v3.13.

Also Algorithm boxes: algo:backfor "Backward and forward extension", algo:sa "Retrieve chromosomal positions", algo:smem "Find (ℓ,c)-SMEMs in string set P".

## How accuracy was evaluated (short reads), verbatim
- "We simulated short reads using mason v2.0.9 with `--illumina-read-length 150 --illumina-prob-mismatch-scale 2.5`."
- Truth criterion: "It is considered mapped correctly if |G_s ∩ G_a|/|G_s ∪ G_a| ≥ 10%." (interval overlap of simulated vs mapped interval; no distance threshold)
- "We measured mapping errors by comparing the simulated position to the mapping position of each read (Fig. 2), stratified by mapping quality. A mapper of higher accuracy tends to yield a curve closer to the upper left corner."
- MAPQ: swept as a threshold (a point per threshold); no fixed MAPQ 60 / 30 cutoff is given. No "error rate" is defined; the y-axis is the fraction of mapped reads that are correct, x the fraction of reads mapped. The tex does not say whether the y denominator is all reads or mapped reads only.
- "Minibwa achieves comparable accuracy to BWA-MEM and Dragmap for WGS short-read alignment (Fig. 2a-c). We still believe BWA-MEM is more accurate than minibwa due to more efforts in highly repetitive regions; minibwa has a similar curve perhaps because its mapping quality estimate is more calibrated."
- Caveat quoted: "on real data, most false read alignment at high mapping quality is caused by large structural variants between individuals ... The theoretical accuracy ... may not reflect accuracy in downstream data processing."
- Tool versions: BWA-MEM v0.7.19, BWA-MEM2 v2.2.1, BWA-MEM3 v0.11.0 (`--compat=bwa-mem2`), Bowtie2 v2.5.5, minimap2 v2.30, Dragmap v1.3.0, strobealign v0.17.0. Machine: two Xeon Gold 6130 at 2.10 GHz. "We used the recommended setting of each tool."
- Command lines in the tex: only the mason option above and the Badread options (long reads). No minibwa command line is given. Mate rescue: prefilter q=7, SW only if max_t M_t >= 10; disabling it slows alignment 7% on real data.
- Data: HG002 NovaSeq (bit.ly/hg002-baid-sr-30x), HiFi, ONT R10, Hi-C, SBX, NA12878 BS-seq SRR4235788.
