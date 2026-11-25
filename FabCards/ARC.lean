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

/-- Achilles Accelerator (ARC005). -/
def ARC_005 : CardDef :=
  { Meta.ARC_005_meta with
    front := { Meta.ARC_005_meta.front with
      abilities :=
        [ .activated .instant false {} [{ cost := .destroySelf }] (some (.boostedThisTurn 1)) false
            { body := .prim (.gainAP .controller (.const 1)) } ] }
    status := .full }

/-- High Octane (ARC006). -/
def ARC_006_R : CardDef :=
  { Meta.ARC_006_R_meta with
    front := { Meta.ARC_006_R_meta.front with
      playEffect := some {
        body := .seqL
          [ .onBoostThisTurn (.prim (.gainAP .controller (.const 1)))
          , .prim (.draw .controller (.const 1)) ] } }
    status := .full }

/-- Teklo Core (ARC007). -/
def ARC_007_B : CardDef :=
  { Meta.ARC_007_B_meta with
    front := { Meta.ARC_007_B_meta.front with
      entryCounters := [(.steam, 2)]
      abilities :=
        [ .triggered (.onCountersEmptied .steam) false none none
            { body := .prim (.destroy .self_) }
        , .triggered .onStartOfActionPhase false none none
            { body := .seqL
                [ .prim (.removeCounter .self_ .steam (.const 1))
                , .prim (.gainResource .controller (.const 2)) ] } ] }
    status := .full }

/-- Maximum Velocity (ARC008). -/
def ARC_008_R : CardDef :=
  { Meta.ARC_008_R_meta with
    front := { Meta.ARC_008_R_meta.front with playRequirement := some (.boostedAtLeast 3) }
    status := .full }

/-- Spark of Genius (ARC009). -/
def ARC_009_Y : CardDef :=
  { Meta.ARC_009_Y_meta with
    front := { Meta.ARC_009_Y_meta.front with
      playEffect := some {
        body := .seqL
          [ .prim (.searchDeck .controller { supertypes := [.class_ .mechanologist], subtypes := [.item] }
                (some 1) .arena true none true (some .xValue))
          , .ifThen (.boostedThisTurn 1) (.prim (.draw .controller (.const 1))) .nop ] } }
    status := .full }

/-- Induction Chamber (ARC010). -/
def ARC_010_R : CardDef :=
  { Meta.ARC_010_R_meta with
    front := { Meta.ARC_010_R_meta.front with
      abilities :=
        [ .activated .action false { actionPoints := 1, resources := 1 } [] none true
            { body := .ifThen (.sourceCounterLt .steam 1)
                (.prim (.addCounter .self_ .steam (.const 1))) .nop }
        , .activated .attackReaction true {} [{ cost := .removeCounters .steam 1 }] none false
            { targets :=
                [{ kind := .weaponAttack
                   filter := { supertypes := [.class_ .mechanologist], subtypes := [.pistol] } }]
              body := .grant (.obj (.slot 0)) (.grantKeyword .goAgain) .thisChainLink } ] }
    status := .full }

/-- A hit sets a modifier for the controller's next attack this turn. -/
def pedalToTheMetal (base : CardDef) : CardDef :=
  { base with
    front := { base.front with
      abilities := [.triggered .onHit false none none
        { body := .grant (.nextAttack {}) (.grantKeyword .dominate) .thisTurn }] } }

/-- Pedal to the Metal (ARC011). -/
def ARC_011_R : CardDef := { pedalToTheMetal Meta.ARC_011_R_meta with status := .full }

/-- Pedal to the Metal (ARC012). -/
def ARC_012_Y : CardDef := { pedalToTheMetal Meta.ARC_012_Y_meta with status := .full }

/-- Pedal to the Metal (ARC013). -/
def ARC_013_B : CardDef := { pedalToTheMetal Meta.ARC_013_B_meta with status := .full }

/-- Verified logical cards first printed in the Arcane Rising booster. -/
def arcCards : List CardDef :=
  [ARC_000_B, ARC_001, ARC_002, ARC_003, ARC_004, ARC_005, ARC_006_R, ARC_007_B,
   ARC_008_R, ARC_009_Y, ARC_010_R, ARC_011_R, ARC_012_Y, ARC_013_B]

end FabCards.ARC

end
