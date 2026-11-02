# deepCaps, part 2: why the shim pays more than the bench (box O2, 2026-11-02)

Box: 4 vCPU, 15 GB, release `bench-release`; tree festive-fermi 2b496d6. Bench index made from shim.idx (same
bytes: `.sl`/`.pgw` hardlinks, `.offs`/`.runs`/`.meta`/`.pgx`/`.pgc` written from `Spec.loadIndex`'s result;
converter in the session scratchpad, not committed). Bench: `WG_NOCHECK=1 WG_MODES=RTX WG_XH=0`, deepCaps on =
`WG_PASS2=1 WG_P2BUDGET=3000 WG_T2=250:28,150:20` (the shim's `tierCfg` with `deepCaps := true`, field by field).

## Cause: the shim maps untrimmed reads
The bench reads every mate through the proved quality trimmer (`ReadTrim.trimReadQ`, `readMates`). The shim does
not trim (`Spec/Shim.lean` / `Main.lean`: "Stand-ins for now: no trimming"). HiSeq 2×250 tails are low quality:
untrimmed mates miss cap 16 (`XB:i:-17`), stay `boundsOnly`, and all of them go to pass 2, where the genome-wide
stage B runs a banded DP on nearly every anchor diagonal.

| 2000 HiSeq pairs, callgrind Ir inside `tierPair` | off | on |
|---|---|---|
| shim (untrimmed) | 1.13 G | 3.74 G |
| bench (trimmed) | 4.29 G | 5.10 G |
Stage-B banded DPs in pass 2: shim 306k, bench 92k. Pass 1: bench keeps 1,655 of 2,000 as unique, shim 1,436; of
the difference, 197 pairs are unique in the bench and `boundsOnly` in the shim.

## Shim on the bench's trimmed mates (`WG_TRIMOUT`, quality 'I'), 4 cores, CPU s, 2 warm runs
| set | reads | off | on | pass-2 cost | unique pairs off → on |
|---|---|---|---|---|---|
| HiSeq 200k | untrimmed | 23.6 / 25.5 | 58.2 / 59.2 | +135% | 140,974 → 150,342 |
| HiSeq 200k | trimmed | 27.9 (cold run 42.8 dropped) | 40.4 / 38.4 | ~+40% | 163,634 → 165,485 |
| NovaSeq 200k | untrimmed | 34.0 / 35.0 | 39.9 / 39.2 | +14% | 162,941 → 164,535 |
| NovaSeq 200k | trimmed | 27.2 / 30.6 | 32.9 / 32.0 | +12% | 163,865 → 164,698 |
(unique pairs = `XT:Z:eachMateUnique` lines / 2; the bench keeps 164,485 HiSeq / 165,205 NovaSeq pairs at deepCaps off.)

## Proposed change (Rowan's file; text only, not applied)
`Spec/Shim.lean` (and `Main.lean`, which mirrors it), `chunkPairs`: trim each mate with the proved trimmer; a mate
trimmed away is `none` (the spec already allows `none` = trimmed away):
```lean
def Spec.chunkPairs (chunk : Array (Spec.FastqRecord × Spec.FastqRecord)) :
    List (Option ByteArray × Option ByteArray) :=
  let trim (r : Spec.FastqRecord) : Option ByteArray :=
    (ReadTrim.trimRead r.letters r.quality.toUTF8).map fun (b, e) => r.letters.extract b e
  chunk.toList.map fun (record1, record2) => (trim record1, trim record2)
```
(needs `import ReadTrim` in the shim; SAM output then reports the trimmed window, so SAM changes: a decision.)
Effect: +22.7k unique HiSeq pairs per 200k at deepCaps off; deepCaps' HiSeq cost +135% → ~+40%.

## Knobs in `tierCfg` alone (untrimmed reads; not a fix)
2000 HiSeq pairs, Ir in `tierPair`: today's deepCaps 3.74 G; gate2 budget 1000: 3.28 G; 250 bp cap 24: 3.65 G;
both: 2.86 G — each loses 1.1k–4.4k of the 18.7k extra unique mate lines per 200k. `alignPairs` sees no qualities,
so the trimming cannot be done on our side.

## Side findings
- After O1's thread fix the bench is no longer a proxy for the shim: it uses ~2× the shim's CPU (no per-task index
  copy, contended counts) and 3.8× its Ir in pass 1 (per-chromosome routing; the shim routes on one sequence).
- Remaining gap with trimmed reads (HiSeq +40% vs bench +16%): not traced yet.
