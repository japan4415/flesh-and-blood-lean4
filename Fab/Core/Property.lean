module

/-!
# Object properties (color strip, damage kind, numeric floor)

Basic property types and clamping helpers for numeric object properties (CR 2.0-2.8).
-/

@[expose] public section

namespace Fab

/-- Color strip printed across the top of a card, conventionally corresponding to pitch value
1 (red), 2 (yellow), or 3 (blue) (CR 2.0, 2.8). -/
inductive ColorStrip where
  /-- Red color strip (typically pitch 1). -/
  | red
  /-- Yellow color strip (typically pitch 2). -/
  | yellow
  /-- Blue color strip (typically pitch 3). -/
  | blue
deriving DecidableEq, Repr, Hashable

/-- Damage type distinguishing blockable physical damage from arcane damage (CR 7.5, 8.3). -/
inductive DamageKind where
  /-- Standard physical damage dealt by combat attacks and effects. -/
  | physical
  /-- Arcane damage, which cannot be defended by defense values and requires prevention. -/
  | arcane
deriving DecidableEq, Repr, Hashable

/-- Clamp a possibly-negative signed numeric property to a non-negative `Nat` when evaluated for
damage or defense totals (CR 2.0.3). -/
def clampNonNeg (n : Int) : Nat :=
  n.toNat

/-- Clamping a non-negative integer preserves its value. -/
theorem clampNonNeg_of_nonneg (n : Int) (h : 0 ≤ n) :
    ((clampNonNeg n : Nat) : Int) = n := by
  unfold clampNonNeg
  omega

/-- Clamping a non-positive integer yields zero. -/
theorem clampNonNeg_of_nonpos (n : Int) (h : n ≤ 0) :
    clampNonNeg n = 0 := by
  unfold clampNonNeg
  omega

/-- Clamping is monotonic. -/
theorem clampNonNeg_mono {a b : Int} (h : a ≤ b) :
    clampNonNeg a ≤ clampNonNeg b := by
  unfold clampNonNeg
  omega

end Fab

end
