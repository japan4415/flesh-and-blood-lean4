#!/usr/bin/env python3
"""Generate docs/coverage.md from normalized card data and FabCards/<Set>.lean."""

from __future__ import annotations

import argparse
import json
import pathlib
import re
from collections import Counter


def scan_statuses(wtr_lean_path: pathlib.Path, card_ids: list[str]) -> tuple[dict[str, str], int]:
    """Scan FabCards/WTR.lean to determine each card's ImplStatus and custom IR count."""
    statuses = {cid: "todo" for cid in card_ids}
    if not wtr_lean_path.exists():
        return statuses, 0

    text = wtr_lean_path.read_text(encoding="utf-8")
    custom_uses = len(re.findall(r"\.custom\b", text))

    # Any card defined as `def WTR_xxx : CardDef := ...` in FabCards/WTR.lean is an override;
    # default to `drafted` unless explicitly marked `.full`, `.«partial»`, or `.todo`.
    for m in re.finditer(
        r"def\s+(WTR_\d+(?:_[RYB])?)\s*:\s*CardDef\s*:=(.*?)(?=\n(?:/--|def |private |end ))",
        text,
        re.S,
    ):
        cid = m.group(1)
        body = m.group(2)
        if cid not in statuses:
            continue
        if ".full" in body:
            statuses[cid] = "full"
        elif ".«partial»" in body or ".partial" in body:
            statuses[cid] = "partial"
        elif ".todo" in body:
            statuses[cid] = "todo"
        else:
            statuses[cid] = "drafted"

    return statuses, custom_uses


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--data", default="data/normalized/wtr_cards.json")
    parser.add_argument("--lean", default="FabCards/WTR.lean")
    parser.add_argument("--out", default="docs/coverage.md")
    args = parser.parse_args()

    payload = json.loads(pathlib.Path(args.data).read_text(encoding="utf-8"))
    cards = payload["cards"]
    card_ids = [c["card_id"] for c in cards]
    statuses, custom_uses = scan_statuses(pathlib.Path(args.lean), card_ids)

    counts = Counter(statuses.values())
    total = len(cards)
    unique_names = len({c["name"] for c in cards})
    drafted_or_better = counts["drafted"] + counts["partial"] + counts["full"]

    # Breakdown by supertype/class
    by_class: dict[str, Counter] = {}
    for c in cards:
        supers = c["supertypes"]
        if not supers:
            cls = "None"
        elif supers[0]["kind"] == "generic":
            cls = "Generic"
        else:
            cls = supers[0]["val"].capitalize()
        by_class.setdefault(cls, Counter())[statuses[c["card_id"]]] += 1

    lines = [
        "# カード実装カバレッジ（自動生成）",
        "",
        "`scripts/coverage.py` によって自動生成されています。",
        "",
        f"- **データ源**: `{payload.get('source_repo')}@{(payload.get('source_commit') or '')[:12]}`",
        f"- **対象セット**: Welcome to Rathe (`{payload.get('set_code')}`)",
        "",
        "## セット別サマリ",
        "",
        "| セット | 論理カード数 | ユニーク名数 | `full` | `partial` | `drafted` | `todo` | IR 転記率 | `custom` 数 |",
        "|---|---:|---:|---:|---:|---:|---:|---:|---:|",
        f"| WTR | {total} | {unique_names} | {counts['full']} | {counts['partial']} | {counts['drafted']} | {counts['todo']} | {drafted_or_better}/{total} ({100.0 * drafted_or_better / total:.1f}%) | {custom_uses} |",
        "",
        "## WTR クラス別内訳",
        "",
        "| クラス | 合計 | `full` | `partial` | `drafted` | `todo` |",
        "|---|---:|---:|---:|---:|---:|",
    ]

    for cls in sorted(by_class):
        cc = by_class[cls]
        ctot = sum(cc.values())
        lines.append(
            f"| {cls} | {ctot} | {cc['full']} | {cc['partial']} | {cc['drafted']} | {cc['todo']} |"
        )

    lines.append("")
    out_path = pathlib.Path(args.out)
    out_path.write_text("\n".join(lines), encoding="utf-8")
    print(f"Wrote {out_path}: {drafted_or_better}/{total} drafted+, {counts['full']} full, {custom_uses} custom")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
