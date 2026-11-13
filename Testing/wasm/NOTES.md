# WebAssembly spike (exp/wasm-spike)

Question: can `lean-align build` / `map` (Main.lean, unchanged) run as wasm with byte-identical output?
**Answer: yes for both, in Node and in headless Chromium. In a browser Web Worker, `map` fails with a stack
overflow** in `Spec.MapFast.advance` (Proofs/MapFast.lean:57), a non-tail recursion 16,000 frames deep (one per
FASTQ line of a 4000-pair job). Native has an 8 MB stack; V8's default limit is ~1 MB and browsers do not let a
page raise it for workers. Fixing it means a tail-recursive `advance` with an equality proof. That is a Proofs/ change
and the owner's decision; it was not made here.

Data: `Testing/bench/tiny_data.py make` → 4 Mb genome, 199,710 pairs; FASTQ uncompressed. Machine: 4 cores.
Native = Lean 4.35.0 release toolchain, `lake build lean-align`.

## How it is built
1. `setup.sh W`: native Lean 4.35.0. There is no official wasm build for 4.35.0: `lean-4.35.0-linux_wasm32.tar.zst`
   is 404, and the "Web Assembly" CI job is commented out upstream. Then the Lean source at v4.35.0, emsdk **3.1.44**
   (pinned by that disabled job), and the Lean runtime (`leanrt`) + libuv built with `emcmake` on `lean4/src`.
   Init/Std C comes from the release's `lean -c` over its own `src/lean` (`core_c.py`; 787 modules, 3 min).
   lean-align imports only Init and Std.
2. `lake build lean-align` (native): its C (203 files in `.lake/build/ir`) is the same C the wasm build compiles.
3. `build.sh W st`: `emcc -O3` over the 990 C files, then a link with leanrt.a + libuv.a, giving two outputs:
   `out-st/lean-align.js` (Node, `NODERAWFS`) and `out-st/web/` (browser, MEMFS, `MODULARIZE`, `callMain`).

Patches to the Lean source (not to this repo):
- `runtime/uv/system.cpp:636`: the Emscripten stub of `lean_uv_os_get_group` is missing its `uint64_t gid` argument
  upstream, so it does not compile (the code rotted while the job was off).
- Single-threaded variant only: `-pthread` removed from the Emscripten flags in `src/CMakeLists.txt`; `-DMULTI_THREAD=OFF`.
- `USE_MIMALLOC=OFF` in both variants (Lean's mimalloc comes from its top-level CMake).
Link warnings: `lean_io_create_tempdir/tempfile` signature mismatch between the Init C and the runtime's Emscripten
code. lean-align does not call them; a call would trap.

## Results
| | native | wasm st, Node 22 | wasm st, Chromium |
|---|---|---|---|
| `build`: index bytes | 275,231,420 B | identical (`cmp`) | identical (SHA-256) |
| `build`: time / memory | 4.45-4.80 s, 1,064 MB RSS | 14.2 s, 2,861 MB RSS | 13.2-13.5 s, 2,861 MB wasm heap |
| `map`: SAM bytes | 158,973,745 B | identical (`cmp`), also on the wasm-built index | identical (SHA-256), **page thread with `--js-flags=--stack-size=2000` only** |
| `map`: time / memory | 3.3 s 1 thread (`LEAN_NUM_THREADS=1`), 1.18 s 4 threads; 0.61 GB | 9.0-9.3 s, 1.14 GB (needs `node --stack-size=2000`) | 8.3 s, 1,247 MB heap |
| `map` in a Web Worker | | | **fails: RangeError: Maximum call stack size exceeded** (with or without the flag) |

- `.wasm` size: 3,382,462 B (3.3 MB), plus JS glue of 82-93 KB.
- Single-threaded wasm needs no SharedArrayBuffer: `crossOriginIsolated` was false and everything ran.
- Threads (`mt`, upstream flags `-pthread`): Lean tasks do run on pthreads. `map` gave an identical SAM in Node but
  took 162 s. A CPU profile shows the time in `emscripten_futex_wait/wake` on the single dlmalloc lock;
  emsdk 3.1.44 has no `-sMALLOC=mimalloc`. With `MAXIMUM_MEMORY=4GB`, `build` died with "Invalid atomic access index"
  (the 3.1.44 JS glue breaks above 2 GB with threads). With 2 GB it hung once the heap reached 2.2 GB.
  mt also needs COOP/COEP headers in a browser. Not pursued: single-threaded is simpler and faster here.

## 32-bit
- The byte comparisons above are the test: fast paths with a bound test and their slow copies agree on wasm32
  for this data.
- The USize proofs use `2 ^ System.Platform.numBits` abstractly; I found no `numBits = 64` assumption. The only
  `size_t` literal ≥ 2^31 in the C (4294967278, MapperK250.lean:778) is < 2^32.
- Memory is the real limit. Index build peaks at 2.86 GB of wasm heap for a 4 Mb genome (native 1.06 GB; no
  mimalloc, and the heap never shrinks). The cap is 4 GB. A ~1 Mb mycoplasma genome should fit; anything much
  above 4 Mb will not. Shipping a prebuilt index avoids this: `map` alone used 1.25 GB.

## Open risks
- `advance` stack depth (above): this blocks `map` in a Worker.
- Running on the page thread freezes the UI and still needs a V8 flag; this is not a deployment option.
- emsdk 3.1.44 is old (2023). A newer emsdk might allow mimalloc for mt and 4 GB with threads. Untested.
- The Init/Std C comes from the 64-bit `lean -c`. Upstream's old wasm job compiled from a 32-bit stage0. The byte
  comparison found no difference, but only this data was tested.
- Not tested: gzip input, other read lengths, genomes other than the tiny one, Firefox/Safari.

## Files
- `setup.sh`: toolchain (native Lean, Lean source + 2 patches, emsdk, wasm leanrt/libuv, Init/Std C).
- `core_c.py`: C for the import closure of the given Lean core modules.
- `build.sh W st|mt`: compile + link (Node and browser builds).
- `run_timed.py`: wall, CPU and peak RSS of one command; asserts exit 0.
- `web/worker.js`, `web/index.html`: Web Worker runner (MEMFS in, SHA-256 out). `browser_test.js URL worker|page [flags]`:
  Playwright driver. Serve `index.html worker.js lean-align.{js,wasm}` and `data/` with any static server
  (I used `python3 -m http.server`).
