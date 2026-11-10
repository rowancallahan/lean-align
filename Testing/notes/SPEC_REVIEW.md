# Independent review of the locked spec (S-R, Fable 5.1, commit 1c58833; read-only)

Decisions for Rowan (spec changes). Nothing here is changed yet.

HIGH
1. Trim ties (Spec/Draft/Trim.lean trim_correct): Phred 25 scores 0, so windows tie; e.g. 20×Q40 + 10×Q25: [0,20) and [0,30) both score 300 -> dropped vs kept 30. All-Q25 read: any window is "best". Fix: tie rule (longest, then leftmost) as two more ∀ clauses.
2. Best-then-drop: 24×Q40 (360), N, 100×Q28 (300) -> best is the 24-base window -> read dropped although a 100-base clean window exists. Fix if unintended: maximise over windows ≥ minLength.
3. Chromosome names (Spec/Fasta.lean readFasta keeps the whole header line): ">1 dna:chromosome ..." gives SN/RNAME with spaces (invalid SAM); a tab breaks .chromosomes (silently LN:0); duplicates / empty chromosomes not rejected. Fix: name up to first whitespace, check SAM RNAME pattern, unique, length ≥ 1; fail the build otherwise.
4. Streaming is not forced by process_correct: a mapStep that buffers both whole files and emits at `none` satisfies it. Also needs `alignPairs (xs ++ ys) = alignPairs xs ++ alignPairs ys` stated in the Spec. Fix: add the append law as a Spec theorem; a per-step (bounded memory) theorem if streaming is to be a claim.

MEDIUM
5. `toNat!` (Main.lean, Fasta.lean) panics and continues with 0: "map idx r1 r2 out abc 500" runs with minFragment = 0, exit 0. Not fail-fast. Fix: toNat? + exit 1.
6. chrs and index are independent inputs: a stale .chromosomes gives wrong or "*" RNAMEs with a mapped flag, exit 0. Fix: derive the list from the index; chrName out of range -> none.
7. body's List.zip truncates if alignPairs returned fewer results (only excluded via alignPairs_correct, i.e. index = buildIndex). Fix: none on length mismatch, or prove the length unconditionally.
8. 10 ≤ name length (with '@') rejects short real names ("@read1"). Suggest 2.
9. No end theorem joins parse_correct + trim_correct + alignPairs_correct for mapFiles' output line i. StateM -> IO step is informal (list it as trusted).

LOW
10. Failure message has no reason (Option). Use Except String (already on the checklist).
11. IO exception leaves OUT.tmp; existing OUT.tmp clobbered; no fsync before rename. OUT is never wrong.
12. /1 /2 stripped without checking which file: swapped R1/R2 inputs pass with flags 64/128 swapped.
13. Both mates trimmed away: tag names only one mate (trimmedAway1 or 2).
14. SEQ/QUAL are the trimmed read with no clipping record.
15. SO:unsorted fine (GO:query more accurate); comment: XB is a pair score, AS a mate score.
16. Very different record sizes in the two files: mapStep buffers the surplus of one file (memory only).

Checked fine: Main vs process_correct (short reads, one file ending first, temp-file rename, fuel bound), process_correct pins the output given mapReads, parse unique, prepPairs counts, trim_correct satisfiable and non-vacuous, cut = TruSeq common prefix (random hit rates ~1e-4 / ~3e-4 per read), every SAM field per SAMv1 §1.4.
