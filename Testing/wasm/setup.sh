#!/bin/bash
# Toolchain for the wasm spike, in work dir W (outside the repo). Each command here was run by hand and worked;
# the script as a whole has not been run end to end.
#   bash Testing/wasm/setup.sh W        then: lake build lean-align (native, PATH=W/leanbin/lean-4.35.0-linux/bin:$PATH)
#                                       then: bash Testing/wasm/build.sh W st
# Hosts: github.com (release asset, git clone of lean4, emsdk, libuv), storage.googleapis.com (emsdk binaries), pypi (zstandard).
set -euo pipefail
mkdir -p "$1"; W=$(cd "$1" && pwd)
R=$(cd "$(dirname "$0")/../.." && pwd)
V=4.35.0
grep -q "v$V" "$R/lean-toolchain"
# 1. native Lean (the release; no linux_wasm32 asset exists for this version)
pip install -q zstandard
curl -sSfL -o "$W/lean.tar.zst" "https://github.com/leanprover/lean4/releases/download/v$V/lean-$V-linux.tar.zst"
mkdir -p "$W/leanbin"
python3 -I -c "import sys,zstandard,tarfile; tarfile.open(fileobj=zstandard.ZstdDecompressor().stream_reader(open(sys.argv[1],'rb')),mode='r|').extractall(sys.argv[2],filter='data')" "$W/lean.tar.zst" "$W/leanbin"
rm "$W/lean.tar.zst"
L=$W/leanbin/lean-$V-linux
# 2. Lean source at the same tag, for the runtime. Patch 1: the Emscripten stub of lean_uv_os_get_group lost its
#    argument upstream (does not compile). Patch 2 (single-threaded copy only): drop -pthread from the Emscripten flags.
git clone -q --depth 1 --branch "v$V" https://github.com/leanprover/lean4 "$W/lean4src"
sed -i '636s/lean_uv_os_get_group()/lean_uv_os_get_group(uint64_t gid)/' "$W/lean4src/src/runtime/uv/system.cpp"
grep -q 'lean_uv_os_get_group(uint64_t gid) {' "$W/lean4src/src/runtime/uv/system.cpp"
cp -r "$W/lean4src" "$W/lean4src-st"
sed -i 's/ALLOW_MEMORY_GROWTH=1 -fwasm-exceptions -pthread -flto/ALLOW_MEMORY_GROWTH=1 -fwasm-exceptions -flto/; s/  string(APPEND LEANC_EXTRA_CC_FLAGS " -pthread")/  # no -pthread/' "$W/lean4src-st/src/CMakeLists.txt"
test "$(git -C "$W/lean4src-st" diff --stat | tail -1)" = " 2 files changed, 3 insertions(+), 3 deletions(-)"
# 3. emsdk 3.1.44 (the version upstream's disabled wasm CI job pins)
git clone -q --depth 1 https://github.com/emscripten-core/emsdk "$W/emsdk-src"
python3 "$W/emsdk-src/emsdk.py" install 3.1.44
python3 "$W/emsdk-src/emsdk.py" activate 3.1.44
source "$W/emsdk-src/emsdk_env.sh" > /dev/null 2>&1
# 4. leanrt + libuv for wasm (CMake clones libuv v1.48.0 itself). mimalloc off: it comes from Lean's top-level CMake.
for v in st mt; do
  if [ $v = st ]; then S=$W/lean4src-st; B=$W/rt-st; MT=OFF; else S=$W/lean4src; B=$W/rt; MT=ON; fi
  mkdir -p "$B"
  (cd "$B" && emcmake cmake "$S/src" -DCMAKE_BUILD_TYPE=Release -DSTAGE=1 -DUSE_GMP=OFF -DMMAP=OFF -DUSE_MIMALLOC=OFF \
     -DMULTI_THREAD=$MT -DCMAKE_C_COMPILER_WORKS=1 -DLEAN_INSTALL_SUFFIX=-linux_wasm32 > cfg.log && make -j"$(nproc)" leanrt > rt.log)
done
# 5. C for Init and Std (the release ships only native objects for them), from the release's own sources
python3 "$R/Testing/wasm/core_c.py" "$L" "$W/corec" Init Std.Data.HashMap
