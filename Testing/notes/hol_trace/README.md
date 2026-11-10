# hol-trace: NEVER MERGE
64ae73f with trace logging in Proofs/MapFast.lean (`implemented_by` + `unsafeBaseIO`) and `process_correct` stubbed
with `sorry` in Proofs/MapFiles.lean. For measurement only; it fails CI by design.

Logs to stderr: `J spawn start end tid sliceBytes` per job (monotonic ns), `C waitStart waitEnd alreadyFinished` per
`collect` get (the k-th C is job k in spawn order). SAM output is unchanged.

Run (S-T's method, stderr to a file), then summarize:

    lake build lean-align && T=Testing/notes/gz_probe I=IDX R=$PWD bash Testing/notes/gz_probe/v.sh "h5m trace" \
      $PWD/.lake/build/bin/lean-align R1.fq.gz R2.fq.gz 0 cat tl 2> trace.log; python3 Testing/notes/hol_trace/ana.py trace.log

(gz_probe is on exp/gz-probe: `git checkout origin/exp/gz-probe -- Testing/notes/gz_probe`.) Without the probe, any
run works: `lean-align map IDX A B OUT 100 1000 2> trace.log`.

Also logs every pair slower than 20 ms: `P tid ms index-in-job seq1 seq2` (the trimmed mates; `alignPairsP` runs
through `implemented_by`, `alignPairsP_eq` stubbed). `grep '^P' trace.log | sort -k3 -n -r | head` lists the slowest.

And every pipeline stage over 5 ms of a pair: `S tid stage ms`, stage one of router / walk / join / short / gaveup /
look (`Proofs/Aligner.lean` `timeIt`). Stage lines of a pair come before its `P` line, on the same tid.
`grep '^S' trace.log | awk '{n[$3]++; t[$3]+=$4} END{for(k in n) print k, n[k], t[k]" ms"}'` sums them.

`pmp.sh N OUT CMD...`: gdb stack samples of every thread every 0.5 s (no perf needed), then the most common Lean
frames (innermost and inclusive). On the slow 2-job run it shows whether the time is in aligner code or in the
runtime (allocator, `lean_*`, memset/page faults: raw frames are in OUT).
