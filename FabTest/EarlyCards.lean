module

import FabCards
meta import FabCards

open Fab FabCards

-- The authorized test prints resolve to the same four implemented equipment cards.
#guard (["OXO001-P", "OXO002-P", "OXO003-P", "OXO004-P"].map fun number =>
    (earlyPrintingCardId? number).bind wtrDB.find? |>.map (·.front.name)) ==
  [some "Ironrot Helm", some "Ironrot Plate", some "Ironrot Gauntlet", some "Ironrot Legs"]

#guard earlyPrintingCardId? "OXO005" == none
