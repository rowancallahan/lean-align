# Index load time (`speed/index-load`, prototype + measurements; no Spec/Shim change)

Index: `Testing/data/prebuilt/shim.idx`, 5,326,114,456 bytes = 2-bit genome 775 MB (14.5%) + 856M slots × 5 B
= 4.28 GB (80.4%) + 2^26 + 1 bucket offsets × 4 B = 268 MB (5.0%) + small fields (k 22, w 4, T 8, B 26).
`loadIndex` copies nothing big (views into the bytes), so load = `IO.FS.readBinFile` = one `Handle.read` of
the whole file into a freshly allocated 5.3 GB `ByteArray`. Bench: `index_load` (Testing/benches/IndexLoad.lean).

## Why the load swings 2–30 s on these boxes: memory, not disk
The box is a Firecracker VM with `virtio_balloon` and **free page reporting** (dmesg: "Free page reporting
enabled"). Memory a process frees goes back to the host after ~1–3 s; the next big allocation is then backed
by the host page by page. The page cache is not freed, so the index file stays in guest RAM.

`index_load whole` (readBinFile, file in page cache), one run right after another with a gap:
| gap after the previous 5.3 GB run exits | 0 s | 1 s | 3 s | 10 s | 30 s |
|---|---|---|---|---|---|
| read time | 1.75 s | 6.35 s | 18.4 s | 26.4 s | 30.9 s |

Same picture from a C probe (diagnostic only): `malloc` + touch 5.3 GB takes 0.8–18.6 s; `read()` of the
cached file into an already touched buffer takes 1.1–1.2 s every time. Shim with empty FASTQ (load only), back to
back, alternating plain / huge pages: plain 16.6 (first), 1.6, 1.7 s; huge pages 10.2, 10.3, 7.7 s. Free page
reporting works on 2 MB blocks (page_reporting_order 9).
Disk: first-ever read of the file 18.9 s (`cat`); after `drop_caches` 1.5–4 s, because the host caches the
disk too (the guest cannot drop that), so a truly cold load is not reproducible here.

## (a) mmap
Not possible: Lean 4.35 core has no mmap, seek, pread, or fadvise (the `Handle` primitives are mk, lock,
flush, rewind, truncate, read, write, getLine, putStr). It needs one `@[extern]` (C) function, which our rules
forbid. It would be the real fix here: the index would be the page cache's pages, so no fresh 5.3 GB
allocation at all (minibwa does this).

## (b) chunked / parallel reads
Measured (`chunks 64`, `chunks 512`, `parts 4` = 4 part files read by 4 tasks then appended): never faster than
`whole`, typically 5–20 s, because each adds a second copy of the data and more fresh memory (`parts` peaks at
10.6 GB, which also pushes the index out of the page cache). `readBinFile` (one read into one buffer) is the
best that core Lean offers. Huge pages (`GLIBC_TUNABLES=glibc.malloc.hugetlb=1`, no code change) take effect
(5.2 GB AnonHugePages) but do not remove the host-side cost: back-to-back pairs gave 1.7–1.8 s for whichever
run came second in one test, and 7.7–10.3 s for the huge-page runs in the shim test; no consistent gain.

## (c) what mapping touches; a smaller index
Estimate for 200k pairs: ~50 minimizer lookups per 150-bp mate (w 4) ≈ 20M bucket lookups. The bucket offsets
(65k pages of 4 KB) and the slots (1.05M pages) are then touched essentially completely (expected untouched
share e^(−20M/1.05M) ≈ 0); the genome (190k pages) gets ≥ 2 windows per pair, ≥ 87% of pages. So loading only
the touched parts (mmap or lazy reads) saves almost nothing for runs of this size; it only helps small runs.
A compressed on-disk form does not help either: the cost is the in-memory size, and decoding would add CPU.
Shrinking the in-memory index means a different layout from the proved builder (`buildIndex` + checker):
5 → 4-byte slots (no tag bits: every bucket entry checked against the genome) −856 MB (−16%); B 26 → 24 −200 MB
(−4%, longer buckets); larger w → fewer slots, less sensitive. Each costs mapping speed or proof work; none
removes the VM effect, only scales it.

## Proposals (Rowan's files; nothing changed)
1. Several read sets per index load (`map INDEX` then many `R1 R2 OUT` triples): one load per run of files.
   Spec/Shim + Main change.
2. One trusted mmap `extern` in Main.lean (would need an exception to the no-extern rule): load ≈ 0, pages come
   from the page cache as mapping touches them.
3. Benchmarks on these boxes: time the load separately, or start the timed run within ~0.5 s of a previous
   5 GB run; otherwise the load measures the VM's memory backing (6–31 s), not our code (1.7 s).
On a normal server (no free page reporting) the load should be ≈ fresh-memory faults + one copy from page cache,
≈ 1.5–3 s for 5.3 GB (not measured here).
