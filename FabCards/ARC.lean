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

/-- Dash (ARC002). -/
def ARC_002 : CardDef :=
  { Meta.ARC_002_meta with
    front := { Meta.ARC_002_meta.front with abilities := [dashSetupAbility] }
    status := .full }

/-- Teklo Plasma Pistol (ARC003). -/
def ARC_003 : CardDef :=
  { Meta.ARC_003_meta with
    front := { Meta.ARC_003_meta.front with
      abilities :=
        [ .activated .action false { actionPoints := 1 } [{ cost := .removeCounters .steam 1 }] none false
            { body := .prim .weaponAttack }
        , .activated .action false { actionPoints := 1, resources := 1 } [] none true
            { body := .ifThen (.sourceCounterLt .steam 1)
                (.prim (.addCounter .self_ .steam (.const 1))) .nop } ] }
    status := .full }

/-- Teklo Foundry Heart (ARC004). -/
def ARC_004 : CardDef :=
  { Meta.ARC_004_meta with
    front := { Meta.ARC_004_meta.front with
      abilities :=
        [ .activated .action true { actionPoints := 1, resources := 1 } [] (some (.boostedThisTurn 1)) true
            { body := .bindBanishTopCount .controller 2 { supertypes := [.class_ .mechanologist] } ⟨0⟩
                (.prim (.gainResource .controller (.varVal ⟨0⟩))) } ] }
    status := .full }

/-- Verified logical cards first printed in the Arcane Rising booster. -/
def arcCards : List CardDef := [ARC_000_B, ARC_001, ARC_002, ARC_003, ARC_004]

end FabCards.ARC

end
