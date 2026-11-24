#!/usr/bin/env python3
"""Normalize raw the-fab-cube snapshot JSON into canonical Lean-ready card data.

Classifies types into Supertypes / CardTypes / Subtypes, assigns stable CardIds
with color suffixes for pitched cards, extracts true printed ability keywords
(distinguishing conditional mentions like 'this gets go again' from standalone
printed keywords), and validates that no unknown tokens are silently dropped.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import pathlib
import re
import sys

CLASS_MAP = {
    "Adjudicator": "adjudicator",
    "Assassin": "assassin",
    "Bard": "bard",
    "Brute": "brute",
    "Guardian": "guardian",
    "Illusionist": "illusionist",
    "Mechanologist": "mechanologist",
    "Merchant": "merchant",
    "Necromancer": "necromancer",
    "Ninja": "ninja",
    "Pirate": "pirate",
    "Ranger": "ranger",
    "Runeblade": "runeblade",
    "Shapeshifter": "shapeshifter",
    "Thief": "thief",
    "Warrior": "warrior",
    "Wizard": "wizard",
}

TALENT_MAP = {
    "Chaos": "chaos",
    "Draconic": "draconic",
    "Earth": "earth",
    "Elemental": "elemental",
    "Ice": "ice",
    "Light": "light",
    "Lightning": "lightning",
    "Mystic": "mystic",
    "Revered": "revered",
    "Reviled": "reviled",
    "Royal": "royal",
    "Shadow": "shadow",
}

CARD_TYPE_MAP = {
    "Action": "action",
    "Attack Reaction": "attackReaction",
    "Block": "block",
    "Companion": "companion",
    "Defense Reaction": "defenseReaction",
    "Demi-Hero": "demiHero",
    "Equipment": "equipment",
    "Hero": "hero",
    "Instant": "instant",
    "Macro": "macro",
    "Mentor": "mentor",
    "Resource": "resource",
    "Token": "token",
    "Weapon": "weapon",
}

SUBTYPE_MAP = {
    "Affliction": "affliction",
    "Ally": "ally",
    "Arms": "arms",
    "Arrow": "arrow",
    "Ash": "ash",
    "Attack": "attack",
    "Aura": "aura",
    "Base": "base",
    "Bow": "bow",
    "Chest": "chest",
    "Claw": "claw",
    "Club": "club",
    "Construct": "construct",
    "Dagger": "dagger",
    "Evo": "evo",
    "Figment": "figment",
    "Flail": "flail",
    "Gem": "gem",
    "Gun": "gun",
    "Hammer": "hammer",
    "Head": "head",
    "Invocation": "invocation",
    "Item": "item",
    "Landmark": "landmark",
    "Legs": "legs",
    "Off-Hand": "offHand",
    "1H": "oneHanded",
    "Orb": "orb",
    "Pistol": "pistol",
    "Pit-Fighter": "pitFighter",
    "Polearm": "polearm",
    "Scepter": "scepter",
    "Scythe": "scythe",
    "Staff": "staff",
    "Sword": "sword",
    "2H": "twoHanded",
    "Wrench": "wrench",
    "Young": "young",
}

PITCH_SUFFIX = {1: ("R", "red"), 2: ("Y", "yellow"), 3: ("B", "blue")}

# Effect keywords (CR 8.5) that the-fab-cube puts in card_keywords but belong in IR Prim.
EFFECT_ONLY_KEYWORDS = {"Intimidate", "Opt", "Charge", "Transform"}


def parse_opt_int(val: object) -> int | None:
    if val is None:
        return None
    s = str(val).strip()
    if s == "":
        return None
    return int(s)


def make_card_id(primary_print_id: str, pitch: int | None) -> str:
    m = re.match(r"^([A-Z]+)(\d+)$", primary_print_id)
    if m:
        base = f"{m.group(1)}_{m.group(2)}"
    else:
        base = re.sub(r"[^A-Za-z0-9_]", "_", primary_print_id)
    if pitch in PITCH_SUFFIX:
        return f"{base}_{PITCH_SUFFIX[pitch][0]}"
    return base


def extract_keywords(card: dict) -> list[dict]:
    """Extract printed KeywordInsts, avoiding conditional text false positives."""
    text = card.get("functional_text_plain") or ""
    lines = [ln.strip() for ln in text.splitlines() if ln.strip()]
    raw_kws = card.get("card_keywords") or []
    result: list[dict] = []

    for kw in raw_kws:
        if kw in EFFECT_ONLY_KEYWORDS:
            continue
        if kw == "Go again":
            # Only treat as printed static keyword if 'Go again' stands on its own line.
            if any(ln == "Go again" for ln in lines):
                result.append({"kind": "goAgain"})
        elif kw == "Dominate":
            if any(ln == "Dominate" for ln in lines):
                result.append({"kind": "dominate"})
        elif kw == "Overpower":
            if any(ln == "Overpower" for ln in lines):
                result.append({"kind": "overpower"})
        elif kw == "Battleworn":
            result.append({"kind": "battleworn"})
        elif kw == "Blade Break":
            result.append({"kind": "bladeBreak"})
        elif kw == "Temper":
            result.append({"kind": "temper"})
        elif kw == "Guardwell":
            result.append({"kind": "guardwell"})
        elif kw == "Combo":
            result.append({"kind": "combo"})
        elif kw == "Crush":
            result.append({"kind": "crush"})
        elif kw == "Reprise":
            result.append({"kind": "reprise"})
        elif kw == "Legendary":
            result.append({"kind": "legendary"})
        elif kw == "Unlimited":
            result.append({"kind": "unlimited"})
        elif kw == "Universal":
            result.append({"kind": "universal"})
        elif kw.endswith(" Specialization"):
            hero = kw[: -len(" Specialization")].strip()
            result.append({"kind": "specialization", "arg": hero})
        else:
            raise ValueError(f"Unknown keyword {kw!r} on card {card.get('name')!r}")

    return result


def normalize_card(card: dict) -> dict:
    supertypes: list[dict] = []
    card_types: list[str] = []
    subtypes: list[str] = []

    for t in card.get("types") or []:
        if t == "Generic":
            supertypes.append({"kind": "generic"})
        elif t in CLASS_MAP:
            supertypes.append({"kind": "class_", "val": CLASS_MAP[t]})
        elif t in TALENT_MAP:
            supertypes.append({"kind": "talent", "val": TALENT_MAP[t]})
        elif t in CARD_TYPE_MAP:
            card_types.append(CARD_TYPE_MAP[t])
        elif t in SUBTYPE_MAP:
            subtypes.append(SUBTYPE_MAP[t])
        else:
            raise ValueError(f"Unknown type token {t!r} on card {card.get('name')!r}")

    pitch = parse_opt_int(card.get("pitch"))
    color = PITCH_SUFFIX[pitch][1] if pitch in PITCH_SUFFIX else None
    cost_res = parse_opt_int(card.get("cost"))
    is_action_card = "action" in card_types and "token" not in card_types
    cost = (
        {"actionPoints": 1 if is_action_card else 0, "resources": cost_res}
        if cost_res is not None
        else None
    )

    text = (card.get("functional_text_plain") or "").strip()
    text_hash = hashlib.sha256(text.encode("utf-8")).hexdigest()[:12]

    card_id = make_card_id(card["primary_print_id"], pitch)

    return {
        "card_id": card_id,
        "unique_id": card.get("unique_id", ""),
        "primary_print_id": card["primary_print_id"],
        "name": card["name"],
        "supertypes": supertypes,
        "types": card_types,
        "subtypes": subtypes,
        "color": color,
        "pitch": pitch,
        "cost": cost,
        "power": parse_opt_int(card.get("power")),
        "defense": parse_opt_int(card.get("defense")),
        "intellect": parse_opt_int(card.get("intelligence")),
        "life": parse_opt_int(card.get("health")),
        "keywords": extract_keywords(card),
        "sets": [card.get("target_set", "WTR")],
        "all_print_sets": card.get("set_ids") or [],
        "type_text": card.get("type_text") or "",
        "functional_text": text,
        "text_hash": text_hash,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--in", dest="in_path", default="data/raw/wtr_cards.json")
    parser.add_argument("--out", dest="out_path", default="data/normalized/wtr_cards.json")
    args = parser.parse_args()

    raw = json.loads(pathlib.Path(args.in_path).read_text(encoding="utf-8"))
    norm_cards = [normalize_card(c) for c in raw["cards"]]

    # Verify uniqueness of (card_id) and (name, pitch)
    ids = [c["card_id"] for c in norm_cards]
    if len(ids) != len(set(ids)):
        raise ValueError("Duplicate normalized card_id detected")
    keys = [(c["name"], c["pitch"]) for c in norm_cards]
    if len(keys) != len(set(keys)):
        raise ValueError("Duplicate (name, pitch) detected")

    out_payload = {
        "source_repo": raw.get("source_repo"),
        "source_commit": raw.get("source_commit"),
        "set_code": raw.get("set_code"),
        "card_count": len(norm_cards),
        "cards": norm_cards,
    }
    out_path = pathlib.Path(args.out_path)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(
        json.dumps(out_payload, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    print(f"Normalized {len(norm_cards)} cards -> {out_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
