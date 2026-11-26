module

public import Fab.Tournament.Draft
import FabCards.Booster
import FabDriver.BrowserDuel

public section

open Fab Fab.BoosterDraft

private def openWtrBooster (args : List String) : Option Booster :=
  (args.mapM String.toNat?).bind FabCards.openWtrBooster

private def openWtr (args : List String) : Option (List Fab.CardId) :=
  (openWtrBooster args).map (List.filterMap id)

/-- Space-separated candidate counts for the WTR slots, used by the browser sampler. -/
@[export fab_wtr_bounds]
def wtrBounds (_ : Unit) : String :=
  String.intercalate " " (FabCards.wtrBoosterLayout.map fun slot => toString slot.length)

/-- Open a WTR pack from space-separated indices for the browser, or return an empty result. -/
@[export fab_wtr_open]
def wtrOpen (input : String) : String :=
  match openWtr (input.splitOn " ") with
  | none => ""
  | some cards => String.intercalate " " (cards.map (·.val))

private def groupBoosters : List Booster → Option (List Boosters)
  | [] => some []
  | first :: second :: third :: rest =>
    (groupBoosters rest).map (⟨first, second, third⟩ :: ·)
  | _ => none

/-- Start an eight-seat optional-registration WTR draft from 24 lines of booster slot indices.
The three boosters for each seat are consecutive. -/
@[export fab_draft_start]
def startDraft (input : String) : Option State := do
  let packs := input.splitOn "\n"
  if packs.length != 24 then none else do
    let boosters ← packs.mapM (fun pack => openWtrBooster (pack.splitOn " "))
    let seats ← groupBoosters boosters
    (State.start FabCards.wtrDB FabCards.wtrDraft .optional seats).toOption

/-- Submit a logical card ID for the given zero-based seat. -/
@[export fab_draft_pick]
def draftPick (state : State) (seat : UInt32) (card : String) : Option State :=
  (state.pick ⟨seat.toNat⟩ ⟨card⟩).toOption

/-- Open the next booster while the draft is in review. -/
@[export fab_draft_next]
def draftNext (state : State) : Option State :=
  state.openNext.toOption

private def viewCards : Option (List CardId) → String
  | none => "-"
  | some cards => String.intercalate " " (cards.map (·.val))

/-- Encode only the requesting seat's Lean view. The four lines are phase, one-based booster
number (zero after completion), current pack, and visible drafted cards. A dash means hidden. -/
@[export fab_draft_view]
def draftView (state : State) (seat : UInt32) : String :=
  match state.view ⟨seat.toNat⟩ with
  | none => ""
  | some view =>
    let (phase, booster) := match view.phase with
      | .picking index => ("picking", index + 1)
      | .review index => ("review", index + 1)
      | .complete => ("complete", 0)
    String.intercalate "\n" [phase, toString booster, viewCards view.pack, viewCards view.drafted]

/-- Open a WTR booster from sixteen slot indices and print its logical card IDs in slot order. -/
def main (args : List String) : IO UInt32 := do
  let some cards := openWtr args
    | IO.eprintln "Expected sixteen valid WTR booster slot indices."
      return 1
  for card in cards do
    IO.println card.val
  return 0

end
