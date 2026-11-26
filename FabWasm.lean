module

import FabCards.Booster

public section

/-- Open a WTR booster from sixteen slot indices and print its logical card IDs in slot order. -/
def main (args : List String) : IO UInt32 := do
  let some booster := (args.mapM String.toNat?).bind FabCards.openWtrBooster
    | IO.eprintln "Expected sixteen valid WTR booster slot indices."
      return 1
  for card in booster.filterMap id do
    IO.println card.val
  return 0

end
