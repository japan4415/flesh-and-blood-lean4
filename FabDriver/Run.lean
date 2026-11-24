module

public import Fab

/-!
# FabDriver: deterministic seeded driver for Start-of-Game setup

Supplies reproducible pseudo-random answers to `Actor.chance` frames (`chanceFirstPlayer`,
`chanceShuffle`) and automated default loadout decisions for testing and simulation.
Not subject to the kernel axiom audit (design.md §4).
-/

@[expose] public section

namespace FabDriver

open Fab

/-- Simple deterministic 64-bit LCG state for reproducible test runs. -/
structure Rng where
  /-- Current PRNG seed value. -/
  seed : UInt64
deriving DecidableEq, Repr

/-- Advance the PRNG and return a random `Nat` below `bound` (or 0 if `bound = 0`). -/
def Rng.nextNat (r : Rng) (bound : Nat) : Nat × Rng :=
  let s' : UInt64 := r.seed * 6364136223846793005 + 1442695040888963407
  if bound = 0 then (0, ⟨s'⟩)
  else ((s' >>> 16).toNat % bound, ⟨s'⟩)

/-- Remove the element at index `i` from a list, returning it and the remaining list. -/
def takeAt {α : Type} : List α → Nat → Option (α × List α)
  | [], _ => none
  | x :: xs, 0 => some (x, xs)
  | x :: xs, n + 1 =>
    match takeAt xs n with
    | none => none
    | some (y, rest) => some (y, x :: rest)

/-- Deterministically shuffle a list into a permutation using `Rng`. -/
def shuffleAux {α : Type} : Nat → Rng → List α → List α × Rng
  | 0, r, xs => (xs, r)
  | _ + 1, r, [] => ([], r)
  | k + 1, r, xs =>
    let (idx, r1) := r.nextNat xs.length
    match takeAt xs idx with
    | none => (xs, r1)
    | some (picked, rest) =>
      let (tail, r2) := shuffleAux k r1 rest
      (picked :: tail, r2)

/-- Shuffle a list using `Rng`. -/
def Rng.shuffle {α : Type} (r : Rng) (xs : List α) : List α × Rng :=
  shuffleAux xs.length r xs

/-- Pick the next action automatically for Start-of-Game frames:
- `chanceFirstPlayer`: random player
- `chooseFirstPlayer chooser`: picks `chooser` to go first
- `chooseLoadout p`: equips every equippable armor/weapon, adds every deck-card to deck, then
  finishes loadout
- `chanceShuffle z`: shuffles `s.zone z` -/
def nextSetupAction (r : Rng) (s : GameState) : Option (Action × Rng) :=
  match s.pending with
  | .chanceFirstPlayer :: _ =>
    let (i, r1) := r.nextNat s.playerCount
    some (⟨.chance, .chanceFirstChooser ⟨i⟩⟩, r1)
  | .chooseFirstPlayer chooser :: _ =>
    some (⟨.player chooser, .pickFirstPlayer chooser⟩, r)
  | .chooseLoadout p :: _ =>
    let inv := s.zone (.player p .inventory)
    match inv.find? (fun id => (loadoutEquipDest? s p id).isSome) with
    | some id => some (⟨.player p, .loadoutEquip id⟩, r)
    | none =>
      match inv.find? (fun id => loadoutCanAddDeck s p id) with
      | some id => some (⟨.player p, .loadoutToDeck id⟩, r)
      | none =>
        if loadoutCanFinish s p then some (⟨.player p, .loadoutDone⟩, r)
        else none
  | .chanceShuffle z :: _ =>
    let (perm, r1) := r.shuffle (s.zone z)
    some (⟨.chance, .shuffleOrder perm⟩, r1)
  | _ => none

/-- Run `step` repeatedly using `nextSetupAction` until `pending` is empty or `steps` budget
expires. -/
def runSetupLoop (fuel : Nat) : Nat → Rng → GameState → Except RuleError GameState
  | 0, _, s => .ok s
  | n + 1, r, s =>
    if s.pending.isEmpty then .ok s
    else
      match nextSetupAction r s with
      | none => .ok s
      | some (a, r1) =>
        match step fuel s a with
        | .error e => .error e
        | .ok (s', _) => runSetupLoop fuel n r1 s'

end FabDriver

end
