#!/usr/bin/env python3
"""Fetch Welcome to Rathe (WTR) card snapshot from the-fab-cube/flesh-and-blood-cards.

Strips art URLs, artist credits, marketplace fields, and flavor text to stay
strictly within rule-relevant card characteristics (docs/card-data.md §10).
"""

from __future__ import annotations

import argparse
import datetime as dt
import json
import pathlib
import sys
import urllib.request

REPO = "the-fab-cube/flesh-and-blood-cards"
DEFAULT_BRANCH = "develop"
CARD_JSON_URL = (
    "https://raw.githubusercontent.com/{repo}/{ref}/json/english/card.json"
)
COMMIT_API_URL = "https://api.github.com/repos/{repo}/commits/{ref}"

ALLOWED_CARD_FIELDS = (
    "unique_id",
    "name",
    "pitch",
    "cost",
    "power",
    "defense",
    "health",
    "intelligence",
    "arcane",
    "types",
    "card_keywords",
    "abilities_and_effects",
    "ability_and_effect_keywords",
    "granted_keywords",
    "removed_keywords",
    "interacts_with_keywords",
    "functional_text_plain",
    "type_text",
    "blitz_legal",
    "cc_legal",
    "commoner_legal",
    "ll_legal",
)


def fetch_json(url: str) -> object:
    req = urllib.request.Request(
        url,
        headers={"User-Agent": "flesh-and-blood-lean4-fetch/0.1"},
    )
    with urllib.request.urlopen(req, timeout=60) as resp:
        return json.loads(resp.read().decode("utf-8"))


def get_commit_sha(ref: str) -> str:
    try:
        data = fetch_json(COMMIT_API_URL.format(repo=REPO, ref=ref))
        if isinstance(data, dict) and isinstance(data.get("sha"), str):
            return data["sha"]
    except Exception:
        pass
    return ref


def filter_set_cards(cards: list[dict], set_code: str) -> list[dict]:
    selected: list[dict] = []
    for card in cards:
        printings = card.get("printings") or []
        set_printings = [
            p for p in printings if (p.get("set_id") or "").upper() == set_code
        ]
        if not set_printings:
            continue

        # Collect distinct set codes and primary collector number in target set.
        all_sets = sorted(
            {
                (p.get("set_id") or "").upper()
                for p in printings
                if p.get("set_id")
            }
        )
        set_numbers = sorted(
            {
                p.get("id")
                for p in set_printings
                if isinstance(p.get("id"), str) and p.get("id")
            }
        )
        rarities = sorted(
            {
                p.get("rarity")
                for p in set_printings
                if isinstance(p.get("rarity"), str) and p.get("rarity")
            }
        )
        double_sided = any(
            bool(p.get("double_sided_card_info")) for p in set_printings
        )

        entry = {k: card.get(k) for k in ALLOWED_CARD_FIELDS if k in card}
        entry["set_ids"] = all_sets
        entry["target_set"] = set_code
        entry["target_print_ids"] = set_numbers
        entry["primary_print_id"] = set_numbers[0] if set_numbers else card.get("unique_id", "")
        entry["rarities"] = rarities
        entry["double_sided"] = double_sided
        selected.append(entry)

    selected.sort(
        key=lambda c: (
            c.get("primary_print_id") or "",
            str(c.get("pitch") or ""),
            c.get("name") or "",
        )
    )
    return selected


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--set", dest="set_code", default="WTR", help="Target set code (default: WTR)")
    parser.add_argument("--ref", default=DEFAULT_BRANCH, help="Git ref in the-fab-cube repo")
    parser.add_argument(
        "--out",
        default="data/raw/wtr_cards.json",
        help="Output snapshot path",
    )
    args = parser.parse_args()

    set_code = args.set_code.upper()
    sha = get_commit_sha(args.ref)
    url = CARD_JSON_URL.format(repo=REPO, ref=sha)
    print(f"Fetching {url} ...", file=sys.stderr)
    raw = fetch_json(url)
    if not isinstance(raw, list):
        print("Expected top-level JSON array from card.json", file=sys.stderr)
        return 1

    cards = filter_set_cards(raw, set_code)
    out_path = pathlib.Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    payload = {
        "source_repo": REPO,
        "source_ref": args.ref,
        "source_commit": sha,
        "fetched_at": dt.datetime.now(dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "set_code": set_code,
        "card_count": len(cards),
        "cards": cards,
    }
    out_path.write_text(
        json.dumps(payload, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    print(f"Wrote {len(cards)} {set_code} logical cards to {out_path} (commit {sha[:12]})")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
