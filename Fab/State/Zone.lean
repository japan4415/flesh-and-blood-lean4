module

public import Fab.Core.Ids

/-!
# Zones

The zones of Flesh and Blood (CR 3.0-3.16), split into Arena zones and Non-Arena zones.
Every zone stores a `List ObjId` as the source of truth; for ordered zones (`deck`, `stack`,
`graveyard`) the head of the list is the top.
-/

@[expose] public section

namespace Fab

/-- Per-player zone kinds (CR 3.0-3.16). Eight are Arena zones and seven are Non-Arena zones. -/
inductive ZoneKind where
  /-- Hero zone, Arena (CR 3.9). -/
  | hero
  /-- Soul sub-zone under the hero, Arena (CR 3.9). -/
  | soul
  /-- Head equipment zone, Arena; head of list is topmost Evo/equipment (CR 3.8). -/
  | head
  /-- Chest equipment zone, Arena (CR 3.4). -/
  | chest
  /-- Arms equipment zone, Arena (CR 3.1). -/
  | arms
  /-- Legs equipment zone, Arena (CR 3.11). -/
  | legs
  /-- Weapon zones, Arena (CR 3.16). -/
  | weapon
  /-- Permanent zone for auras, items, allies, landmarks, and tokens, Arena (CR 3.13). -/
  | permanent
  /-- Main deck, Non-Arena, ordered with head as top (CR 3.7). -/
  | deck
  /-- Hand, Non-Arena, private (CR 3.10). -/
  | hand
  /-- Arsenal, Non-Arena, face-down private or face-up public (CR 3.2). -/
  | arsenal
  /-- Pitch zone, Non-Arena, returned to deck bottom in End Phase (CR 3.14, 4.4.3c). -/
  | pitch
  /-- Graveyard, Non-Arena, public (CR 3.0). -/
  | graveyard
  /-- Banished zone, Non-Arena, face-up public or face-down private (CR 3.3). -/
  | banished
  /-- Inventory zone for unused registered card-pool cards, Non-Arena (CR 4.1.4). -/
  | inventory
deriving DecidableEq, Repr, Hashable

/-- List of every per-player `ZoneKind`. -/
def ZoneKind.all : List ZoneKind :=
  [ .hero, .soul, .head, .chest, .arms, .legs, .weapon, .permanent,
    .deck, .hand, .arsenal, .pitch, .graveyard, .banished, .inventory ]

/-- Distinct ordinal below 15 for each `ZoneKind`. -/
def ZoneKind.idx : ZoneKind → Nat
  | .hero => 0
  | .soul => 1
  | .head => 2
  | .chest => 3
  | .arms => 4
  | .legs => 5
  | .weapon => 6
  | .permanent => 7
  | .deck => 8
  | .hand => 9
  | .arsenal => 10
  | .pitch => 11
  | .graveyard => 12
  | .banished => 13
  | .inventory => 14

/-- Every `ZoneKind` index is below 15. -/
theorem ZoneKind.idx_lt (k : ZoneKind) : k.idx < 15 := by
  cases k <;> decide

/-- Distinct `ZoneKind`s have distinct indices. -/
theorem ZoneKind.idx_inj {a b : ZoneKind} (h : a.idx = b.idx) : a = b := by
  cases a <;> cases b <;> simp_all [ZoneKind.idx]

/-- Whether a per-player zone kind belongs to the Arena (CR 3.0.5). -/
def ZoneKind.isArena : ZoneKind → Bool
  | .hero | .soul | .head | .chest | .arms | .legs | .weapon | .permanent => true
  | .deck | .hand | .arsenal | .pitch | .graveyard | .banished | .inventory => false

/-- Every `ZoneKind` is listed in `ZoneKind.all`. -/
theorem ZoneKind.mem_all (k : ZoneKind) : k ∈ ZoneKind.all := by
  cases k <;> decide

/-- `ZoneKind.all` has no duplicates. -/
theorem ZoneKind.all_nodup : ZoneKind.all.Nodup := by decide

/-- A zone of a Flesh and Blood game (CR 3.0). -/
inductive Zone where
  /-- A zone belonging to player `p`. -/
  | player (p : PlayerId) (k : ZoneKind)
  /-- The shared Combat Chain zone, Arena (CR 3.5). -/
  | combatChain
  /-- The shared Stack zone, Non-Arena, ordered LIFO with head as top (CR 3.15). -/
  | stack
deriving DecidableEq, Repr, Hashable

namespace Zone

/-- Whether a zone belongs to the Arena (CR 3.0.5). Moving between two Arena zones preserves
object identity and counters (CR 3.0.9). -/
def isArena : Zone → Bool
  | .player _ k => k.isArena
  | .combatChain => true
  | .stack => false

/-- Moving between `src` and `dst` crosses the Arena boundary or moves between Non-Arena zones,
minting a new object with a fresh `ObjId` (CR 3.0.9). -/
def crosses (src dst : Zone) : Bool :=
  !(src.isArena && dst.isArena)

/-- Non-Arena player zones always belong to the moving object's owner. -/
def normalize (owner : PlayerId) : Zone → Zone
  | .player q k => if k.isArena then .player q k else .player owner k
  | z => z

/-- Numeric key encoding each zone uniquely: `0` and `1` for shared zones, then 15 per seat. -/
def key : Zone → Nat
  | .combatChain => 0
  | .stack => 1
  | .player p k => 2 + p.n * 15 + k.idx

/-- Different zones have different numeric keys. -/
theorem key_inj {a b : Zone} (h : a.key = b.key) : a = b := by
  cases a with
  | combatChain => cases b <;> simp only [key] at h <;> first | rfl | omega
  | stack => cases b <;> simp only [key] at h <;> first | rfl | omega
  | player p k =>
    cases b with
    | combatChain => simp only [key] at h; omega
    | stack => simp only [key] at h; omega
    | player q l =>
      have hk := k.idx_lt
      have hl := l.idx_lt
      simp only [key] at h
      have h1 : p.n = q.n := by omega
      have h2 : k.idx = l.idx := by omega
      obtain ⟨pn⟩ := p
      obtain ⟨qn⟩ := q
      simp only at h1
      subst h1
      rw [ZoneKind.idx_inj h2]

end Zone

end Fab

end
