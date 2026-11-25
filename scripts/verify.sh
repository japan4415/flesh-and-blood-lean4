#!/usr/bin/env bash
# 全体の検証。main へマージする前に通す（docs/lean-guidelines.md §7）。
# 1 つでも失敗したら、そこで止まる。
set -euo pipefail

cd "$(dirname "$0")/.."
export PATH="$HOME/.elan/bin:$PATH"

step() { printf '\n==> %s\n' "$*"; }

step "1/5 build (--wfail)"
lake build Fab FabCards FabDriver FabTest --wfail

step "2/5 test"
lake test

step "3/5 axiom audit (lake check)"
# サンドボックスは Linux でしか動かない。自分のコードを自分のマシンで検査するので外す。
# 対象は defaultTargets（検証コア Fab だけ）。
lake check --inadvisably-no-sandbox

step "4/5 generated cards check"
python3 scripts/gen_lean.py --check
uv run --no-project scripts/gen_lean.py --check \
  --in data/normalized/arc_cards.json --out FabCards/ARC/Meta.lean

step "5/5 rule citations"
python3 scripts/cr_citations.py

printf '\nverify: OK\n'
