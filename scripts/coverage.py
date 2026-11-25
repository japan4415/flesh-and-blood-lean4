#!/usr/bin/env python3
"""Generate docs/coverage.md from normalized card data and FabCards/<Set>.lean."""

from __future__ import annotations

import argparse
import json
import pathlib
import re
from collections import Counter

SETS = [
    ("WTR", "Welcome to Rathe", "data/normalized/wtr_cards.json", "FabCards/WTR.lean"),
    ("MON", "Monarch", "data/normalized/mon_cards.json", "FabCards/MON.lean"),
]


def scan_statuses(set_code: str, lean_path: pathlib.Path, card_ids: list[str]) -> tuple[dict[str, str], int]:
    """Scan FabCards/<Set>.lean to determine each card's ImplStatus and custom IR count."""
    statuses = {cid: "todo" for cid in card_ids}
    if not lean_path.exists():
        return statuses, 0

    text = lean_path.read_text(encoding="utf-8")
    custom_uses = len(re.findall(r"\.custom\b", text))

    pattern = rf"^def\s+({re.escape(set_code)}_\d+(?:_[RYB])?)\s*:\s*CardDef\s*:=(.*?)(?=\n(?:/--|def |private |end |\n/-!)|\Z)"
    for m in re.finditer(pattern, text, re.M | re.S):
        cid = m.group(1)
        body = m.group(2)
        if cid not in statuses:
            continue
        status = re.search(r"\bstatus\s*:=\s*\.(full|«partial»|partial|todo|drafted)(?![\w»])", body)
        if status:
            statuses[cid] = status[1].strip("«»")
        else:
            statuses[cid] = "full" if re.match(r"\s*verifiedCard\b", body) else "drafted"

    return statuses, custom_uses


def supertype_label(card: dict) -> str:
    supers = card["supertypes"]
    if not supers:
        return "None"
    parts = []
    for s in supers:
        if s["kind"] == "generic":
            parts.append("Generic")
        else:
            parts.append(s["val"].capitalize())
    return " ".join(parts)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--data", help="Report on one normalized set")
    parser.add_argument("--lean", help="Override the handwritten card module for one set")
    parser.add_argument("--out", default="docs/coverage.md")
    parser.add_argument("--check", action="store_true", help="Check the report without writing it")
    args = parser.parse_args()

    summary_rows: list[str] = []
    detail_sections: list[str] = []
    source_meta: dict[str, None] = {}
    set_labels: list[str] = []
    total_all = 0
    done_all = 0

    sets = SETS
    if args.data or args.lean:
        data = args.data or SETS[0][2]
        code = json.loads(pathlib.Path(data).read_text(encoding="utf-8"))["set_code"]
        title = next((name for key, name, _, _ in SETS if key == code), code)
        sets = [(code, title, data, args.lean or f"FabCards/{code}.lean")]

    for code, title, data_rel, lean_rel in sets:
        data_path = pathlib.Path(data_rel)
        payload = json.loads(data_path.read_text(encoding="utf-8"))
        source_meta[f"`{payload.get('source_repo')}@{(payload.get('source_commit') or '')[:12]}`"] = None
        set_labels.append(f"{title} (`{code}`)")
        cards = payload["cards"]
        card_ids = [c["card_id"] for c in cards]
        statuses, custom_uses = scan_statuses(code, pathlib.Path(lean_rel), card_ids)

        counts = Counter(statuses.values())
        total = len(cards)
        unique_names = len({c["name"] for c in cards})
        transcribed = counts["drafted"] + counts["partial"] + counts["full"]
        total_all += total
        done_all += transcribed

        summary_rows.append(
            f"| {code} ({title}) | {total} | {unique_names} | {counts['full']} | {counts['partial']} | "
            f"{counts['drafted']} | {counts['todo']} | {transcribed}/{total} ({100.0 * transcribed / total:.1f}%) | {custom_uses} |"
        )

        by_class: dict[str, Counter] = {}
        for c in cards:
            lbl = supertype_label(c)
            by_class.setdefault(lbl, Counter())[statuses[c["card_id"]]] += 1

        detail_sections.extend([
            f"## {code}（{title}）クラス別内訳",
            "",
            "| クラス / タレント | 合計 | `full` | `partial` | `drafted` | `todo` |",
            "|---|---:|---:|---:|---:|---:|",
        ])
        for cls in sorted(by_class):
            cc = by_class[cls]
            ctot = sum(cc.values())
            detail_sections.append(
                f"| {cls} | {ctot} | {cc['full']} | {cc['partial']} | {cc['drafted']} | {cc['todo']} |"
            )
        detail_sections.append("")

    lines = [
        "# カード実装カバレッジ（自動生成）",
        "",
        "`scripts/coverage.py` によって自動生成されています。",
        "",
        f"- **データ源**: {', '.join(source_meta)}",
        f"- **対象セット**: {', '.join(set_labels)}",
        "",
        "## セット別サマリ",
        "",
        "| セット | 論理カード数 | ユニーク名数 | `full` | `partial` | `drafted` | `todo` | IR 転記率 | `custom` 数 |",
        "|---|---:|---:|---:|---:|---:|---:|---:|---:|",
        *summary_rows,
        "",
        *detail_sections,
    ]

    out_path = pathlib.Path(args.out)
    report = "\n".join(lines)
    if args.check:
        if not out_path.is_file() or out_path.read_text(encoding="utf-8") != report:
            parser.exit(1, f"Coverage report is stale: {out_path}\n")
        print(f"coverage --check: OK ({out_path})")
        return 0
    out_path.write_text(report, encoding="utf-8")
    print(f"Wrote {out_path}: {done_all}/{total_all} total cards transcribed across sets")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
