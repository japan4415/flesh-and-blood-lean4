#!/usr/bin/env python3
"""Generate docs/coverage.md from normalized card data and FabCards/<Set>.lean."""

from __future__ import annotations

import argparse
import json
import pathlib
import re
from collections import Counter


def scan_statuses(lean_path: pathlib.Path, card_ids: list[str]) -> tuple[dict[str, str], int]:
    """Read explicit card overrides and their implementation status."""
    statuses = {cid: "todo" for cid in card_ids}
    if not lean_path.exists():
        return statuses, 0

    text = lean_path.read_text(encoding="utf-8")
    custom_uses = len(re.findall(r"\.custom\b", text))

    # Explicit card definitions in a set module override generated metadata.
    # default to `drafted` unless explicitly marked `.full`, `.«partial»`, or `.todo`.
    for m in re.finditer(
        r"def\s+([A-Z0-9]+_\d+(?:_[RYB])?)\s*:\s*CardDef\s*:=(.*?)(?=\n(?:/--|def |private |end ))",
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


def report(sources: list[tuple[pathlib.Path, pathlib.Path]]) -> tuple[str, list[str]]:
    datasets = [(json.loads(data.read_text(encoding="utf-8")), lean) for data, lean in sources]
    source_refs = dict.fromkeys(
        f"{payload.get('source_repo')}@{(payload.get('source_commit') or '')[:12]}"
        for payload, _ in datasets
    )
    reference = ", ".join(f"`{ref}`" for ref in source_refs)
    lines = [
        "# カード実装カバレッジ（自動生成）",
        "",
        "`scripts/coverage.py` によって自動生成されています。",
        "",
        f"データ源は {reference} です。",
        "",
        "## セット別サマリ",
        "",
        "| セット | 新規論理カード | ユニーク名 | 再録 | `full` | `partial` | "
        "`drafted` | `todo` | IR 転記率 | `custom` |",
        "|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|",
    ]
    seen: set[str] = set()
    classes: list[str] = []
    summaries: list[str] = []
    for payload, lean in datasets:
        code = payload["set_code"]
        cards = []
        for card in payload["cards"]:
            identity = card.get("unique_id") or card["card_id"]
            if identity not in seen:
                cards.append(card)
                seen.add(identity)
        statuses, custom = scan_statuses(lean, [card["card_id"] for card in cards])
        counts = Counter(statuses.values())
        total = len(cards)
        reprints = len(payload["cards"]) - total
        names = len({card["name"] for card in cards})
        implemented = total - counts["todo"]
        percent = 100.0 * implemented / total if total else 0.0
        lines.append(
            f"| {code} | {total} | {names} | {reprints} | {counts['full']} | {counts['partial']} | "
            f"{counts['drafted']} | {counts['todo']} | {implemented}/{total} ({percent:.1f}%) | {custom} |"
        )
        summaries.append(f"{code} {counts['full']}/{total} full")
        by_class: dict[str, Counter[str]] = {}
        for card in cards:
            supers = card["supertypes"]
            cls = "None" if not supers else (
                "Generic" if supers[0]["kind"] == "generic" else supers[0]["val"].capitalize()
            )
            by_class.setdefault(cls, Counter())[statuses[card["card_id"]]] += 1
        classes.extend([
            "",
            f"## {code} クラス別内訳",
            "",
            "| クラス | 合計 | `full` | `partial` | `drafted` | `todo` |",
            "|---|---:|---:|---:|---:|---:|",
        ])
        for cls, cc in sorted(by_class.items()):
            classes.append(
                f"| {cls} | {sum(cc.values())} | {cc['full']} | {cc['partial']} | {cc['drafted']} | {cc['todo']} |"
            )
    return "\n".join([*lines, *classes, ""]), summaries


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--data", type=pathlib.Path)
    parser.add_argument("--lean", type=pathlib.Path)
    parser.add_argument("--out", type=pathlib.Path, default=pathlib.Path("docs/coverage.md"))
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    sources = [
        (pathlib.Path(f"data/normalized/{code.lower()}_cards.json"), pathlib.Path(f"FabCards/{code}.lean"))
        for code in ("WTR", "ARC")
    ]
    if args.data is not None or args.lean is not None:
        wtr_data, wtr_lean = sources[0]
        sources = [(args.data or wtr_data, args.lean or wtr_lean)]

    content, summaries = report(sources)
    if args.check:
        if not args.out.is_file() or args.out.read_text(encoding="utf-8") != content:
            print(f"coverage --check: {args.out} is out of date")
            return 1
        print(f"coverage --check: OK ({', '.join(summaries)})")
    else:
        args.out.write_text(content, encoding="utf-8")
        print(f"Wrote {args.out}: {', '.join(summaries)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
