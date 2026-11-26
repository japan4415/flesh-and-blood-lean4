module

public import Fab.Core.Ids

/-!
# Booster opening

An opening resolves one supplied choice per slot against its eligible logical cards.
-/

public section

namespace Fab.BoosterPack

/-- Eligible logical cards for each slot, in the model's slot order. -/
abbrev Layout := List (List CardId)

/-- The cards fill the slots in order, each drawn from the corresponding candidates. -/
inductive Fits : List CardId → Layout → Prop where
  /-- There are no cards and no slots left. -/
  | nil : Fits [] []
  /-- This card fits the first slot and the remaining cards fill the remaining slots. -/
  | cons {card : CardId} {cards choices : List CardId} {slots : Layout} :
      card ∈ choices → Fits cards slots → Fits (card :: cards) (choices :: slots)

/-- A pack that fits has exactly one card per slot. -/
theorem Fits.length_eq {cards : List CardId} {slots : Layout} (h : Fits cards slots) :
    cards.length = slots.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

/-- Open a pack from zero-based slot choices. Reject an out-of-range index or a wrong count. -/
def openSlots : Layout → List Nat → Option (List CardId)
  | [], [] => some []
  | choices :: slots, index :: indices => do
    let card ← choices[index]?
    let cards ← openSlots slots indices
    return card :: cards
  | _, _ => none

/-- Every successful opening fills exactly the specified slots with eligible cards. -/
theorem openSlots_fits {slots : Layout} {indices : List Nat} {cards : List CardId}
    (h : openSlots slots indices = some cards) : Fits cards slots := by
  induction slots generalizing indices cards with
  | nil =>
    cases indices <;> simp [openSlots] at h
    subst cards
    exact .nil
  | cons choices slots ih =>
    cases indices with
    | nil => simp [openSlots] at h
    | cons index indices =>
      cases head : choices[index]? with
      | none => simp [openSlots, head] at h
      | some card =>
        cases tail : openSlots slots indices with
        | none => simp [openSlots, head, tail] at h
        | some rest =>
          simp [openSlots, head, tail] at h
          subst cards
          exact .cons (List.mem_of_getElem? head) (ih tail)

end Fab.BoosterPack

end
