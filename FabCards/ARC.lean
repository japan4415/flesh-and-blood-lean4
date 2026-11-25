module

public import FabCards.ARC.Meta

@[expose] public section

namespace FabCards.ARC

open Fab

/-- Eye of Ophidia (ARC000). -/
def ARC_000_B : CardDef :=
  { Meta.ARC_000_B_meta with
    front := {
      Meta.ARC_000_B_meta.front with
      abilities := [.triggered .onPitch false none none { body := .prim (.opt .controller 2) }] }
    status := .full }

/-- The item Dash may start with (CR 4.1.5b). -/
def dashSetupAbility : Ability :=
  .setupPermanent { supertypes := [.class_ .mechanologist], subtypes := [.item], maxCost := some 2 }

/-- Dash, Inventor Extraordinaire (ARC001). -/
def ARC_001 : CardDef :=
  { Meta.ARC_001_meta with
    front := { Meta.ARC_001_meta.front with abilities := [dashSetupAbility] }
    status := .full }

/-- Verified logical cards first printed in the Arcane Rising booster. -/
def arcCards : List CardDef := [ARC_000_B, ARC_001]

end FabCards.ARC

end
