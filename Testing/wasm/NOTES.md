# WebAssembly spike (exp/wasm-spike)

Question: can `lean-align build` / `map` be compiled to wasm with byte-identical output?
Status: **not answered**. Blocked at step 1: installing Emscripten (emsdk) was refused by this
session's permission policy (twice: `emsdk install 3.1.44`). Network was not the blocker:
`storage.googleapis.com` (emsdk binaries) and `git clone github.com/emscripten-core/emsdk` both work.

## 1. Toolchain (findings)
- No official wasm build of Lean v4.35.0. `lean-4.35.0-linux_wasm32.tar.zst` is 404 on the release.
  In `lean4@v4.35.0/.github/workflows/ci.yml` the "Web Assembly" job is commented out.
- The source still supports it: `src/CMakeLists.txt` has an Emscripten branch
  (`-s ALLOW_MEMORY_GROWTH=1 -fwasm-exceptions -pthread -flto`, `-DLEAN_EMSCRIPTEN`,
  libuv built from git with a patch, no OpenSSL, `USE_GMP=OFF`).
  `build-template.yml` pins emsdk **3.1.44** for that job.
- lean-align imports only Init/Std (no `Lean`, no packages), so wasm needs:
  leanrt (C++ runtime + libuv) + C of Init/Std + the 203 files in `.lake/build/ir/*.c`.
- Plan (not run): emsdk 3.1.44; build `leanrt` with `emcmake cmake` on `lean4/src`
  (options from the commented CI job: `-DUSE_GMP=OFF -DMMAP=OFF -DLEAN_INSTALL_SUFFIX=-linux_wasm32`);
  generate Init/Std C with the native `lean -c` from the release's `src/lean`
  (the release ships no `.c` for them; `stage0/stdlib` is a different Lean version, do not use);
  `emcc -O3` over all C + `libleanrt.a` + `libuv.a`, `-sALLOW_MEMORY_GROWTH -sMAXIMUM_MEMORY=4GB -sNODERAWFS`
  for Node, `-sFORCE_FILESYSTEM` + MEMFS for the browser.
- Local clang 18 has the wasm32 backend and `wasm-ld`, but no libc/libc++ sysroot; not a replacement.

## 2.-5. Not reached (no wasm module).

## Native baseline (Lean 4.35.0 release toolchain, 4 cores, tiny set: 4 Mb genome, 199,710 pairs, uncompressed FASTQ)
`python3 Testing/wasm/run_timed.py CMD` (wall, peak RSS via wait4):
| step | wall | peak RSS | output |
|---|---|---|---|
| `build genome.fa idx` | 4.45 s, 4.80 s | 1064 MB | idx 275,231,420 B (+66 B `.chromosomes`) |
| `map idx r1.fq r2.fq out.sam 100 1000`, `LEAN_NUM_THREADS=1` | 2.72 s, 3.16 s | 622-629 MB | 158,973,745 B |
Both deterministic (`cmp` of two runs equal).

## 32-bit audit of the generated C (static, not a test)
- Proofs about USize use `USize.size = 2 ^ System.Platform.numBits` abstractly (e.g. `usz_toNat`, `usz_lit` needs `n < 2^32`);
  no `numBits = 64` found. So the proved fast-path = slow-path equalities should also hold on wasm32.
- Only one USize literal ≥ 2^31 in the C: `(size_t)4294967278ULL` in `MapSpec.Fast.flagsOkU` (MapperK250.lean:778);
  < 2^32, so not truncated. Callers guard `17*stop < 4294967278`.
- Fast paths guarded by a bound test will take the slow path more often on 32-bit only for arrays near 4 GB; not reached on small genomes.
- Memory: index = ~68 B per genome base (275 MB for 4 Mb), build peaks at 1.06 GB natively. wasm32 cap is 4 GB;
  Chrome's per-tab practical limit is often lower. Mycoplasma (~1 Mb) should be ~70 MB index.
- Threads: `build` and `map` use `Task.spawn` (17 call sites in the C). A pthread wasm build needs
  SharedArrayBuffer, i.e. COOP/COEP cross-origin isolation in the browser; a `MULTI_THREAD=OFF` runtime runs tasks inline.

## Files
- `Testing/wasm/run_timed.py`  wall + peak RSS of one command, asserts exit 0.
