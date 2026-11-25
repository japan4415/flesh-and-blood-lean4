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

/-- Generic, physical, and arcane damage are distinct (CR 8.5.3b). -/
inductive DamageKind where
  /-- Physical damage dealt using attack power during the Damage Step (CR 7.5.2). -/
  | physical
  /-- Arcane damage, which cannot be defended by defense values and requires prevention. -/
  | arcane
  /-- Damage dealt by an effect that specifies no damage type (CR 8.5.3b). -/
  | generic
deriving DecidableEq, Repr, Hashable

/-- The four replacement-effect application stages in strict precedence order (CR 6.4.10, 6.5.1). -/
inductive ReplacementStage where
  /-- Stage A: Self-replacement and identity-replacement effects (CR 6.4.10a, 6.4.10b). -/
  | selfOrIdentity
  /-- Stage B: Standard replacement effects (CR 6.4.10c). -/
  | standard
  /-- Stage C: Prevention effects, including Ward, Arcane Barrier, Spellvoid, Quell (CR 6.4.10d). -/
  | prevention
  /-- Stage D: Outcome-replacement effects applied after the event concludes (CR 6.4.10e). -/
  | outcome
deriving DecidableEq, Repr, Hashable

/-- Precedence order of replacement stages (CR 6.5.1). -/
def ReplacementStage.order : List ReplacementStage :=
  [.selfOrIdentity, .standard, .prevention, .outcome]

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
