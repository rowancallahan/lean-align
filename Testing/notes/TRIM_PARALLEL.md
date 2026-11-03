# Parallel trimming (patch only: Testing/notes/trim_parallel.patch, not applied)

What it does: `readChunk` reads untrimmed pairs. `trimChunk raw 16` trims them in 16 dedicated tasks, inside the
same reader task. `trimChunk_eq` (Proofs/TrimRecord.lean, standard axioms) shows it equals mapping `trimRecord`.

Verification, each in a scratch copy (worktrees off speed/join 0221a57):
- Patch alone: `FUZZ=1 CI_check.sh` passes everything except the frozen checksum of Spec/Shim.lean, as
  expected, since the patch does not regenerate FROZEN. 456 theorems, standard axioms; all mirrors match; fuzz
  violations: none.
- shim_speed.patch alone: CI with FUZZ=1 fully green (454 theorems).
- shim_speed + this patch: same as the patch alone (only the Shim checksum fails), 455 theorems.
- SAM: byte-identical to the unpatched binary for all three variants on the full NovaSeq and HiSeq (hg002) 200k
  sets, on every run.

Wall time, 200k pairs, 4 cores, heavy.idx, minimum of runs 2–4 (run 1 discarded), seconds wall / user:
| binary | NovaSeq | HiSeq |
|---|---|---|
| base (speed/join) | 9.36 / 21.4 | 10.18 / 22.1 |
| + trim_parallel | 8.11 / 19.9 | 9.39 / 23.2 |
| + shim_speed | 7.99 / 18.8 | 8.59 / 20.1 |
| + shim_speed + trim_parallel | 7.91 / 18.7 | 8.73 / 20.7 |
- The box is noisy. In an earlier series the base had min 8.6 s (NovaSeq) and 9.7 s (HiSeq), and trim_parallel
  was no faster. Index load alone is 2.2 s.
- Reading: on 4 cores, trim_parallel alone may save up to ~1 s, but that is within noise. On top of shim_speed
  it gains nothing measurable: the trimming tasks compete for the same 4 cores the aligner uses. It may help more
  on machines with more cores; not measured.
