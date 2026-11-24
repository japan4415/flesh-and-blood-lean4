#!/usr/bin/env bash
# 全体の検証。main へマージする前に通す（docs/lean-guidelines.md §7）。
# 1 つでも失敗したら、そこで止まる。
set -euo pipefail

cd "$(dirname "$0")/.."
export PATH="$HOME/.elan/bin:$PATH"

step() { printf '\n==> %s\n' "$*"; }

step "1/4 build (--wfail)"
lake build Fab FabCards FabDriver FabTest --wfail

step "2/4 test"
lake test

step "3/4 axiom audit (lake check)"
# サンドボックスは Linux でしか動かない。自分のコードを自分のマシンで検査するので外す。
# 対象は defaultTargets（検証コア Fab だけ）。
lake check --inadvisably-no-sandbox

step "4/4 rule citations"
python3 scripts/cr_citations.py

printf '\nverify: OK\n'
