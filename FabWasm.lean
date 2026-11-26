module

import FabCards.Booster

public section

private def openWtr (args : List String) : Option (List Fab.CardId) :=
  ((args.mapM String.toNat?).bind FabCards.openWtrBooster).map (List.filterMap id)

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

/-- Open a WTR booster from sixteen slot indices and print its logical card IDs in slot order. -/
def main (args : List String) : IO UInt32 := do
  let some cards := openWtr args
    | IO.eprintln "Expected sixteen valid WTR booster slot indices."
      return 1
  for card in cards do
    IO.println card.val
  return 0

end
