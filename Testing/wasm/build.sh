#!/bin/bash
# Build lean-align (Main.lean, unchanged) as WebAssembly with Emscripten 3.1.44.
#   bash Testing/wasm/build.sh W st|mt
#     W   work dir holding emsdk-src/, corec/ (Init/Std C from core_c.py), rt-st/ or rt/ (leanrt + libuv), see NOTES.md
#     st  single-threaded: runtime built with MULTI_THREAD=OFF and no -pthread; Task.spawn runs inline
#     mt  threaded: upstream settings (-pthread); needs SharedArrayBuffer
# Needs the native `lake build lean-align` first (C in .lake/build/ir).
# Output: W/out-VARIANT/lean-align.{js,wasm} for Node (real file system), W/out-VARIANT/web/ for the browser (MEMFS).
set -euo pipefail
W=$(cd "$1" && pwd)
V=$2
cd "$(dirname "$0")/../.."
source "$W/emsdk-src/emsdk_env.sh" > /dev/null 2>&1
emcc --version | head -1 | grep -q 3.1.44
case "$V" in
  st) RT=$W/rt-st; T="";;
  mt) RT=$W/rt;    T="-pthread -sPROXY_TO_PTHREAD=1 -sPTHREAD_POOL_SIZE=8 -sDEFAULT_PTHREAD_STACK_SIZE=8MB";;
esac
O=$W/obj-$V
mkdir -p "$O" "$W/out-$V/web"
# -ffp-contract=off as upstream uses for Lean C; same exception model as the runtime
CFLAGS="-O3 -DNDEBUG ${T%% *} -fwasm-exceptions -ffp-contract=off -Wno-unused-command-line-argument -I$RT/include"
# object name = path with / replaced by _ (Proofs/Fastq.c and Spec/Fastq.c must not collide)
{ cd "$W/corec" && ls *.c | sed 's|^|core/|'; cd - > /dev/null; find .lake/build/ir -name '*.c' | sed 's|^.lake/build/ir/|ir/|'; } |
  xargs -P "$(nproc)" -I{} sh -c 'case "$1" in core/*) c="$0/corec/${1#core/}";; ir/*) c=".lake/build/ir/${1#ir/}";; esac
    o="$2/$(echo "$1" | tr / _).o"; [ "$o" -nt "$c" ] || emcc '"$CFLAGS"' -c "$c" -o "$o"' "$W" {} "$O"
test "$(ls "$O" | wc -l)" = "$(( $(ls "$W"/corec/*.c | wc -l) + $(find .lake/build/ir -name '*.c' | wc -l) ))"
LIBS="$RT/lib/lean/libleanrt.a $RT/libuv/src/libuv/libuv.a"
LFLAGS="-O3 $T -fwasm-exceptions -sALLOW_MEMORY_GROWTH=1 -sMAXIMUM_MEMORY=4GB -sSTACK_SIZE=8MB -sEXIT_RUNTIME=1"
emcc $LFLAGS -sNODERAWFS=1 "$O"/*.o $LIBS -o "$W/out-$V/lean-align.js"
emcc $LFLAGS -sENVIRONMENT=web,worker -sFORCE_FILESYSTEM=1 -sINVOKE_RUN=0 -sMODULARIZE=1 -sEXPORT_NAME=LeanAlign \
  -sEXPORTED_RUNTIME_METHODS=FS,callMain "$O"/*.o $LIBS -o "$W/out-$V/web/lean-align.js"
ls -l "$W/out-$V" "$W/out-$V/web"
