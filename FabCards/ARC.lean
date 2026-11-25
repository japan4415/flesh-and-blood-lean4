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

/-- An action that loads a steam counter only when its source is empty. -/
def loadSteamAbility : Ability :=
  .activated .action false { actionPoints := 1, resources := 1 } [] none true
    { body := .ifThen (.sourceCounterLt .steam 1)
        (.prim (.addCounter .self_ .steam (.const 1))) .nop }

/-- Teklo Plasma Pistol (ARC003). -/
def ARC_003 : CardDef :=
  { Meta.ARC_003_meta with
    front := { Meta.ARC_003_meta.front with
      abilities :=
        [ .activated .action false { actionPoints := 1 } [{ cost := .removeCounters .steam 1 }] none false
            { body := .prim .weaponAttack }
        , loadSteamAbility ] }
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
        [ loadSteamAbility
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

/-- Formalize optional item placement and the additional entry counter after a boost. -/
def pourTheMold (base : CardDef) (maxCost : Nat) : CardDef :=
  let place (counter : Option CounterKind) :=
    Effect.prim (.putHandPermanent .controller
      { supertypes := [.class_ .mechanologist], subtypes := [.item], maxCost := some maxCost } counter)
  { base with front := { base.front with
      playEffect := some { body := .ifThen (.boostedThisTurn 1) (place (some .steam)) (place none) } } }

/-- Pour the Mold (ARC014). -/
def ARC_014_R : CardDef := { pourTheMold Meta.ARC_014_R_meta 0 with status := .full }

/-- Pour the Mold (ARC015). -/
def ARC_015_Y : CardDef := { pourTheMold Meta.ARC_015_Y_meta 1 with status := .full }

/-- Pour the Mold (ARC016). -/
def ARC_016_B : CardDef := { pourTheMold Meta.ARC_016_B_meta 2 with status := .full }

/-- Aether Sink (ARC017). -/
def ARC_017_Y : CardDef :=
  { Meta.ARC_017_Y_meta with
    front := { Meta.ARC_017_Y_meta.front with
      entryCounters := [(.steam, 1)]
      abilities :=
        [ loadSteamAbility
        , .activated .instant false {} [{ cost := .removeCounters .steam 1 }] none false
            { body := .grant .self_ (.grantKeyword (.arcaneBarrier 2)) .thisTurn } ] }
    status := .full }

/-- Cognition Nodes (ARC018). -/
def ARC_018_B : CardDef :=
  { Meta.ARC_018_B_meta with
    front := { Meta.ARC_018_B_meta.front with
      abilities :=
        [ loadSteamAbility
        , .activated .attackReaction true {} [{ cost := .removeCounters .steam 1 }] none false
            { targets := [{ kind := .attackAction }]
              body := .grant (.obj (.slot 0))
                (.grantTrigger .onHit none (.prim (.moveCard .self_ .deck .bottom true)))
                .thisCombatChain } ] }
    status := .full }

/-- Convection Amplifier (ARC019). -/
def ARC_019_R : CardDef :=
  { Meta.ARC_019_R_meta with
    front := { Meta.ARC_019_R_meta.front with
      entryCounters := [(.steam, 2)]
      abilities :=
        [ .triggered (.onCountersEmptied .steam) false none none
            { body := .prim (.destroy .self_) }
        , .activated .action false { actionPoints := 1 } [{ cost := .removeCounters .steam 1 }] none true
            { body := .grant (.nextAttack { types := [.action], subtypes := [.attack] })
                (.grantKeyword .dominate) .thisTurn } ] }
    status := .full }

/-- Formalize an attack that returns to its owner's deck if it hits. -/
def overLoop (base : CardDef) : CardDef :=
  { base with front := { base.front with
    abilities := [.triggered .onHit false none none
      { body := .prim (.moveCard .self_ .deck .bottom true) }] } }

/-- Over Loop (ARC020). -/
def ARC_020_R : CardDef := { overLoop Meta.ARC_020_R_meta with status := .full }

/-- Over Loop (ARC021). -/
def ARC_021_Y : CardDef := { overLoop Meta.ARC_021_Y_meta with status := .full }

/-- Over Loop (ARC022). -/
def ARC_022_B : CardDef := { overLoop Meta.ARC_022_B_meta with status := .full }

/-- Throttle (ARC023). -/
def ARC_023_R : CardDef := { Meta.ARC_023_R_meta with status := .full }

/-- Throttle (ARC024). -/
def ARC_024_Y : CardDef := { Meta.ARC_024_Y_meta with status := .full }

/-- Throttle (ARC025). -/
def ARC_025_B : CardDef := { Meta.ARC_025_B_meta with status := .full }

/-- Zero to Sixty (ARC026). -/
def ARC_026_R : CardDef := { Meta.ARC_026_R_meta with status := .full }

/-- Verified logical cards first printed in the Arcane Rising booster. -/
def arcCards : List CardDef :=
  [ARC_000_B, ARC_001, ARC_002, ARC_003, ARC_004, ARC_005, ARC_006_R, ARC_007_B,
   ARC_008_R, ARC_009_Y, ARC_010_R, ARC_011_R, ARC_012_Y, ARC_013_B, ARC_014_R, ARC_015_Y,
   ARC_016_B, ARC_017_Y, ARC_018_B, ARC_019_R, ARC_020_R, ARC_021_Y, ARC_022_B,
   ARC_023_R, ARC_024_Y, ARC_025_B,
   ARC_026_R]

end FabCards.ARC

end
