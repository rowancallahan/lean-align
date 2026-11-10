# Proof of `process_correct` (Spec/MapFiles.lean), assuming `job_eq`

`Spec.Total.process_correct'` (Proofs/MapCorrect.lean) has the Spec's statement with one hypothesis,
`job_eq : (MapFast.job settings index chrs s1 s2).map bytes = mapReads settings index chrs (bytes s1) (bytes s2)` (S-G proves it).
Standard axioms only. Layers (all in Proofs/, built by lake):

| file | content |
|---|---|
| FastqSlices | `cutLines`, `slices_parse`, `cutLines_valid`, `parse_append` |
| MapStream | list-level machine `fast_correct` for arbitrary record-aligned streaming (not used by the final proof, kept as a check) |
| MapProcess | `process_fold`: Spec's `process` on `StateM` with `fuel > chunks.length` = start, one `step` per pair of chunks, end |
| MapJobs | `R_append`, `mapReads_cut`: cutting both files after `4 n` newlines (n reads each), `mapReads` of the whole = the first job's lines ++ `mapReads` of the rest (none if either is) |
| MapScan | `MapFast.advance` = `cutLines` on the buffer's bytes |
| MapSlices | `cutSlices_spec`: the slices cut are `IsSlice` (exactly `4 · jobPairs` newlines, ending in one); the carry keeps `ScanOk` |
| MapPending | `spawnPaired_vals`, `collect_vals`: the pending tasks by value (`(Task.spawn f).get = f ()`), `collect` takes the oldest `len - keep` results, none if one is none |
| MapRun | invariant `FInv`/`InvG` (bytes read so far = spawned slices ++ queued slices ++ carry; the written lines ++ the pending results = the jobs' outputs), `spawn_inv`, `collect_inv`, `failing_job`, `step_some_inv`, `step_some_fail`, `pair_inv`, `end_correct`, `fold_correct` |
| MapCorrect | `process_fold'` for the Spec's own `process`, and `process_correct'` |

Not in the proof: `job_eq`; the placement of `process_correct` itself (Proofs/MapFiles.lean defines `mapReads`/`process`, and the proof
modules import it, so the theorem cannot be proved inside that file: split its definitions into a module the proofs import).
A step that returns none after collecting a failing job is shown to mean `mapReads` of the *whole* files is none for every
continuation (`failing_job` via `chain`); output held back across steps is handled by the invariant (K jobs written, the rest pending).
