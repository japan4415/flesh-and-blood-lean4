module

/-!
# Core identifiers

Identifiers for players, physical cards, game objects, logical cards, combat chain links,
timestamps, and expansion sets (CR 1.2, 1.3, 2.6, 2.8, 3.5, 6.3.3).
-/

@[expose] public section

namespace Fab

/-- Seat index identifying a player in turn order (CR 1.1). -/
structure PlayerId where
  /-- Zero-based seat index. -/
  n : Nat
deriving DecidableEq, Repr, Hashable, Ord

/-- Physical card instance from a player's registered card-pool.
Tokens, layers, and attack-proxies do not have a `PhysId` (CR 1.3). -/
structure PhysId where
  /-- Monotonic physical card identifier. -/
  n : Nat
deriving DecidableEq, Repr, Hashable, Ord

/-- Game object instance. Crossing the arena boundary or moving between non-arena zones mints a
fresh `ObjId` (CR 3.0.9). -/
structure ObjId where
  /-- Monotonic game object identifier. -/
  n : Nat
deriving DecidableEq, Repr, Hashable, Ord

/-- Logical card identifier corresponding to a unique `(name, pitch)` card entry (CR 2.6, 2.8). -/
structure CardId where
  /-- Stable identifier string (for example, `"WTR_001"` or `"WTR_215_R"`). -/
  val : String
deriving DecidableEq, Repr, Hashable, Ord

/-- One-based combat chain link index within an open combat chain (CR 3.5.4). -/
structure LinkId where
  /-- Chain link ordinal. -/
  n : Nat
deriving DecidableEq, Repr, Hashable, Ord

/-- Logical timestamp assigned when an object or continuous effect is created (CR 6.3.3). -/
structure Timestamp where
  /-- Monotonic timestamp counter. -/
  n : Nat
deriving DecidableEq, Repr, Hashable, Ord

/-- Expansion set code identifying where a card was printed (for example, `"WTR"`). -/
structure SetCode where
  /-- Official three-letter set code. -/
  val : String
deriving DecidableEq, Repr, Hashable, Ord

/-- `Welcome to Rathe` set code (1st set). -/
def SetCode.wtr : SetCode := ⟨"WTR"⟩

/-- `Arcane Rising` set code (2nd set). -/
def SetCode.arc : SetCode := ⟨"ARC"⟩

/-- `Crucible of War` set code (3rd set). -/
def SetCode.cru : SetCode := ⟨"CRU"⟩

/-- `Monarch` set code (4th set). -/
def SetCode.mon : SetCode := ⟨"MON"⟩

end Fab

end
