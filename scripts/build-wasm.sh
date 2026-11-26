#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."
project_root=$PWD
build_root=${1:-.lake/wasm}
mkdir -p "$build_root"
build_root=$(cd "$build_root" && pwd)
lean_source="$build_root/lean4"
lean_build="$build_root/lean-runtime"
output="$build_root/output"

toolchain=$(<lean-toolchain)
tag=${toolchain#leanprover/lean4:}
lean_prefix=$(lean --print-prefix)
if [[ ! -d "$lean_source/.git" ]]; then
  git -c advice.detachedHead=false clone --depth 1 --branch "$tag" \
    https://github.com/leanprover/lean4.git "$lean_source"
fi
if [[ $(git -C "$lean_source" rev-parse HEAD) != "$(lean --githash)" ]]; then
  printf 'Lean source does not match %s. Use an empty WASM build directory.\n' "$toolchain" >&2
  exit 1
fi

# Correct the runtime signatures that 4.36.0's native ABI tolerates but WASM checks.
if [[ $tag == v4.36.0 ]]; then
  patch="$project_root/scripts/patches/lean-4.36.0-emscripten.patch"
  if ! git -C "$lean_source" apply --reverse --check "$patch" 2>/dev/null; then
    git -C "$lean_source" apply "$patch"
  fi
fi

emcmake cmake -S "$lean_source/src" -B "$lean_build" -G 'Unix Makefiles' \
  -DSTAGE=1 -DPREV_STAGE="$lean_prefix" -DCMAKE_BUILD_TYPE=Release \
  -DUSE_GMP=OFF -DUSE_MIMALLOC=OFF -DMMAP=OFF -DMULTI_THREAD=OFF -DCCACHE=OFF
cmake --build "$lean_build" --target leanrt --parallel "${LEAN_NUM_THREADS:-4}"

archive_path=$PATH
if [[ $(uname -s) == Darwin ]]; then
  # Bootstrap Lake uses the host libtool on macOS even when LEAN_AR is set.
  mkdir -p "$build_root/wasm-tools"
  cat > "$build_root/wasm-tools/libtool" <<'SH'
#!/usr/bin/env bash
set -euo pipefail

if [[ $# != 5 || $1 != -static || $2 != -o || $4 != -filelist ]]; then
  exec /usr/bin/libtool "$@"
fi
args_file=$(mktemp)
trap 'rm -f "$args_file"' EXIT
sed -e 's/\\/\\\\/g' -e 's/"/\\"/g' -e 's/.*/"&"/' "$5" > "$args_file"
rm -f "$3"
emar rcs "$3" "@$args_file"
SH
  chmod +x "$build_root/wasm-tools/libtool"
  archive_path="$build_root/wasm-tools:$PATH"
fi
PATH="$archive_path" LEAN_CC="$(command -v emcc)" LEAN_AR="$(command -v emar)" \
  lake -f "$lean_build/lakefile.toml" build Init:static Std:static --no-cache --fail-fast

lake build Fab FabCards FabDriver +FabWasm:c --wfail
ir=.lake/build/ir
sources=("$ir/Fab.c" "$ir/FabCards.c" "$ir/FabDriver.c" "$ir/FabWasm.c")
while IFS= read -r -d '' source; do
  sources+=("$ir/${source%.lean}.c")
done < <(find Fab FabCards FabDriver -name '*.lean' -print0)

mkdir -p "$output"
emcc -O2 -pthread -fwasm-exceptions -ffunction-sections -fdata-sections \
  -I"$lean_build/include" "${sources[@]}" \
  "$lean_build/lib/lean/libStd.a" "$lean_build/lib/lean/libInit.a" \
  "$lean_build/lib/lean/libleanrt.a" "$lean_build/libuv/src/libuv/libuv.a" \
  -Wl,--fatal-warnings -s ALLOW_MEMORY_GROWTH=1 -s STACK_SIZE=8388608 -s EXIT_RUNTIME=1 \
  -o "$output/fab.js"
