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

/-- Zero to Sixty (ARC027). -/
def ARC_027_Y : CardDef := { Meta.ARC_027_Y_meta with status := .full }

/-- Zero to Sixty (ARC028). -/
def ARC_028_B : CardDef := { Meta.ARC_028_B_meta with status := .full }

/-- Zipper Hit (ARC029). -/
def ARC_029_R : CardDef := { Meta.ARC_029_R_meta with status := .full }

/-- Zipper Hit (ARC030). -/
def ARC_030_Y : CardDef := { Meta.ARC_030_Y_meta with status := .full }

/-- Zipper Hit (ARC031). -/
def ARC_031_B : CardDef := { Meta.ARC_031_B_meta with status := .full }

/-- Formalize the next attack's power modifier and conditional opt. -/
def lockedAndLoaded (base : CardDef) (bonus : Int) : CardDef :=
  let attacks : CardFilter :=
    { supertypes := [.class_ .mechanologist]
      types := [.action]
      subtypes := [.attack] }
  { base with front := { base.front with
    playEffect := some {
      body := .seqL
        [ .grant (.nextAttack attacks) (.addPower (.const bonus)) .thisTurn
        , .ifThen (.boostedThisTurn 1) (.prim (.opt .controller 1)) .nop ] } } }

/-- Locked and Loaded (ARC032). -/
def ARC_032_R : CardDef := { lockedAndLoaded Meta.ARC_032_R_meta 3 with status := .full }

/-- Locked and Loaded (ARC033). -/
def ARC_033_Y : CardDef := { lockedAndLoaded Meta.ARC_033_Y_meta 2 with status := .full }

/-- Locked and Loaded (ARC034). -/
def ARC_034_B : CardDef := { lockedAndLoaded Meta.ARC_034_B_meta 1 with status := .full }

/-- Dissipation Shield (ARC035). -/
def ARC_035_Y : CardDef :=
  let destroy := Effect.prim (.destroy .self_)
  let spend := Effect.prim (.removeCounter .self_ .steam (.const 1))
  { Meta.ARC_035_Y_meta with
    front := { Meta.ARC_035_Y_meta.front with
      entryCounters := [(.steam, 4)]
      abilities :=
        [ .triggered .onStartOfActionPhase false none none
            { body := .ifThen (.sourceCounterLt .steam 1) destroy (.chooseOneL [spend, destroy]) }
        , .activated .instant false {} [{ cost := .destroySelf }] none false
            { body := .prim (.preventDamageOnce .controller (.sourceCounterCount .steam)) } ] }
    status := .full }

/-- Hyper Driver (ARC036). -/
def ARC_036_R : CardDef :=
  { Meta.ARC_036_R_meta with
    front := { Meta.ARC_036_R_meta.front with
      entryCounters := [(.steam, 3)]
      abilities :=
        [ .triggered (.onCountersEmptied .steam) false none none
            { body := .prim (.destroy .self_) }
        , .triggered .onBoost true none none
            { body := .seqL
                [ .prim (.removeCounter .self_ .steam (.const 1))
                , .prim (.gainResource .controller (.const 1)) ] } ] }
    status := .full }

/-- Optekal Monocle (ARC037). -/
def ARC_037_B : CardDef :=
  { Meta.ARC_037_B_meta with
    front := { Meta.ARC_037_B_meta.front with
      entryCounters := [(.steam, 5)]
      abilities :=
        [ .triggered (.onCountersEmptied .steam) false none none
            { body := .prim (.destroy .self_) }
        , .activated .action false { actionPoints := 1 } [{ cost := .removeCounters .steam 1 }] none true
            { body := .prim (.opt .controller 1) } ] }
    status := .full }

/-- The arsenal activation shared by the adult and young Azalea heroes. -/
def azaleaArsenalAbility : Ability :=
  .activated .action true { actionPoints := 1 } [] none true
    { body := .prim (.cycleArsenal .controller .arrow .dominate) }

/-- Azalea, Ace in the Hole (ARC038). -/
def ARC_038 : CardDef :=
  { Meta.ARC_038_meta with
    front := { Meta.ARC_038_meta.front with abilities := [azaleaArsenalAbility] }
    status := .full }

/-- Azalea (ARC039). -/
def ARC_039 : CardDef :=
  { Meta.ARC_039_meta with
    front := { Meta.ARC_039_meta.front with abilities := [azaleaArsenalAbility] }
    status := .full }

/-- Death Dealer (ARC040). -/
def ARC_040 : CardDef :=
  { Meta.ARC_040_meta with
    front := { Meta.ARC_040_meta.front with
      abilities := [ .activated .action true { actionPoints := 1, resources := 1 } [] none true
        { body := .prim (.putHandArsenal .controller { subtypes := [.arrow] } true) } ] }
    status := .full }

/-- Skullbone Crosswrap (ARC041). -/
def ARC_041 : CardDef :=
  { Meta.ARC_041_meta with
    front := { Meta.ARC_041_meta.front with
      abilities := [ .activated .action true { actionPoints := 1 } [{ cost := .turnArsenalFaceUp }] none true
        { body := .prim (.opt .controller 1) } ] }
    status := .full }

/-- Bull's Eye Bracers (ARC042). -/
def ARC_042 : CardDef :=
  { Meta.ARC_042_meta with
    front := { Meta.ARC_042_meta.front with
      abilities := [ .activated .action false { actionPoints := 1 } [{ cost := .destroySelf }] none true
        { body := .prim (.putHandArsenal .controller { subtypes := [.arrow] } false (some 1)) } ] }
    status := .full }

/-- Red in the Ledger (ARC043). -/
def ARC_043_R : CardDef :=
  { Meta.ARC_043_R_meta with
    front := { Meta.ARC_043_R_meta.front with
      abilities := [ .triggered .onHitHero false none none
        { body := .grant (.playerActionsAndAttacks .defendingHero) (.limitActions 1) .nextActionPhase } ] }
    status := .full }

/-- Three of a Kind (ARC044). -/
def ARC_044_R : CardDef :=
  let body := Effect.seqL
    [ .prim (.draw .controller (.const 3))
    , .grant (.player .controller) .onlyPlayFromArsenal .thisTurn ]
  { Meta.ARC_044_R_meta with
    front := { Meta.ARC_044_R_meta.front with playEffect := some { body } }
    status := .full }

/-- Endless Arrow (ARC045). -/
def ARC_045_R : CardDef :=
  { Meta.ARC_045_R_meta with
    front := { Meta.ARC_045_R_meta.front with
      abilities := [ .triggered .onHit false none none
        { body := .prim (.moveCard .self_ .hand .top false) } ] }
    status := .full }

/-- Nock the Deathwhistle (ARC046). -/
def ARC_046_B : CardDef :=
  let body := Effect.seqL
    [ .prim (.searchDeckToTop .controller { subtypes := [.arrow] })
    , .prim (.reload .controller) ]
  { Meta.ARC_046_B_meta with
    front := { Meta.ARC_046_B_meta.front with playEffect := some { body } }
    status := .full }

/-- Rapid Fire (ARC047). -/
def ARC_047_Y : CardDef :=
  let body := Effect.seqL
    [ .grant (.allMatching .controller { subtypes := [.arrow] }) (.grantKeyword .goAgain) .thisTurn
    , .prim (.reload .controller) ]
  { Meta.ARC_047_Y_meta with
    front := { Meta.ARC_047_Y_meta.front with keywords := [.goAgain], playEffect := some { body } }
    status := .full }

/-- A Take Cover defense reaction reloads during resolution. -/
def takeCover (card : CardDef) : CardDef :=
  { card with
    front := { card.front with playEffect := some { body := .prim (.reload .controller) } } }

/-- Take Cover (ARC048). -/
def ARC_048_R : CardDef := { takeCover Meta.ARC_048_R_meta with status := .full }

/-- Take Cover (ARC049). -/
def ARC_049_Y : CardDef := { takeCover Meta.ARC_049_Y_meta with status := .full }

/-- Take Cover (ARC050). -/
def ARC_050_B : CardDef := { takeCover Meta.ARC_050_B_meta with status := .full }

/-- Silver the Tip looks at its pitch-specific number of cards before loading an arrow. -/
def silverTheTip (card : CardDef) (count : Nat) : CardDef :=
  let body := Effect.prim (.lookDeckToArsenal .controller count { subtypes := [.arrow] })
  { card with
    front := { card.front with playEffect := some { body } } }

/-- Silver the Tip (ARC051). -/
def ARC_051_R : CardDef := { silverTheTip Meta.ARC_051_R_meta 4 with status := .full }

/-- Silver the Tip (ARC052). -/
def ARC_052_Y : CardDef := { silverTheTip Meta.ARC_052_Y_meta 3 with status := .full }

/-- Silver the Tip (ARC053). -/
def ARC_053_B : CardDef := { silverTheTip Meta.ARC_053_B_meta 2 with status := .full }

/-- Take Aim modifies the next Ranger attack action that is played and then reloads. -/
def takeAim (card : CardDef) (power : Int) : CardDef :=
  let filter := { CardFilter.attackAction with supertypes := [.class_ .ranger] }
  let body := Effect.seqL
    [ .grant (.nextCardPlayed filter) (.addPower (.const power)) .thisTurn
    , .prim (.reload .controller) ]
  { card with
    front := { card.front with playEffect := some { body } } }

/-- Take Aim (ARC054). -/
def ARC_054_R : CardDef := { takeAim Meta.ARC_054_R_meta 3 with status := .full }

/-- Take Aim (ARC055). -/
def ARC_055_Y : CardDef := { takeAim Meta.ARC_055_Y_meta 2 with status := .full }

/-- Take Aim (ARC056). -/
def ARC_056_B : CardDef := { takeAim Meta.ARC_056_B_meta 1 with status := .full }

/-- Head Shot gets a turn-scoped power bonus when it enters arsenal face up. -/
def headShot (card : CardDef) : CardDef :=
  let ability := Ability.triggered .onArsenalFaceUp false none none
    { body := .grant .self_ (.addPower (.const 2)) .thisTurn }
  { card with
    front := { card.front with abilities := [ability] } }

/-- Head Shot (ARC057). -/
def ARC_057_R : CardDef := { headShot Meta.ARC_057_R_meta with status := .full }

/-- Head Shot (ARC058). -/
def ARC_058_Y : CardDef := { headShot Meta.ARC_058_Y_meta with status := .full }

/-- Head Shot (ARC059). -/
def ARC_059_B : CardDef := { headShot Meta.ARC_059_B_meta with status := .full }

/-- Hamstring Shot makes the defending hero’s first attack next turn cost an extra resource. -/
def hamstringShot (card : CardDef) : CardDef :=
  let ability := Ability.triggered .onHitHero false none none
    { body := .grant (.firstAttackNextTurn .defendingHero) (.modifyCost 1) .untilEndOfNextTurn }
  { card with
    front := { card.front with abilities := [ability] } }

/-- Hamstring Shot (ARC060). -/
def ARC_060_R : CardDef := { hamstringShot Meta.ARC_060_R_meta with status := .full }

/-- Hamstring Shot (ARC061). -/
def ARC_061_Y : CardDef := { hamstringShot Meta.ARC_061_Y_meta with status := .full }

/-- Hamstring Shot (ARC062). -/
def ARC_062_B : CardDef := { hamstringShot Meta.ARC_062_B_meta with status := .full }

/-- Ridge Rider Shot opts when it enters arsenal face up. -/
def ridgeRiderShot (card : CardDef) : CardDef :=
  let ability := Ability.triggered .onArsenalFaceUp false none none
    { body := .prim (.opt .controller 1) }
  { card with
    front := { card.front with abilities := [ability] } }

/-- Ridge Rider Shot (ARC063). -/
def ARC_063_R : CardDef := { ridgeRiderShot Meta.ARC_063_R_meta with status := .full }

/-- Ridge Rider Shot (ARC064). -/
def ARC_064_Y : CardDef := { ridgeRiderShot Meta.ARC_064_Y_meta with status := .full }

/-- Ridge Rider Shot (ARC065). -/
def ARC_065_B : CardDef := { ridgeRiderShot Meta.ARC_065_B_meta with status := .full }

/-- Salvage Shot (ARC066). -/
def ARC_066_R : CardDef := { overLoop Meta.ARC_066_R_meta with status := .full }

/-- Salvage Shot (ARC067). -/
def ARC_067_Y : CardDef := { overLoop Meta.ARC_067_Y_meta with status := .full }

/-- Verified logical cards first printed in the Arcane Rising booster. -/
def arcCards : List CardDef :=
  [ARC_000_B, ARC_001, ARC_002, ARC_003, ARC_004, ARC_005, ARC_006_R, ARC_007_B,
   ARC_008_R, ARC_009_Y, ARC_010_R, ARC_011_R, ARC_012_Y, ARC_013_B, ARC_014_R, ARC_015_Y,
   ARC_016_B, ARC_017_Y, ARC_018_B, ARC_019_R, ARC_020_R, ARC_021_Y, ARC_022_B,
   ARC_023_R, ARC_024_Y, ARC_025_B,
   ARC_026_R, ARC_027_Y, ARC_028_B,
   ARC_029_R, ARC_030_Y, ARC_031_B,
   ARC_032_R, ARC_033_Y, ARC_034_B, ARC_035_Y, ARC_036_R, ARC_037_B, ARC_038, ARC_039, ARC_040, ARC_041, ARC_042, ARC_043_R, ARC_044_R, ARC_045_R, ARC_046_B, ARC_047_Y, ARC_048_R, ARC_049_Y, ARC_050_B, ARC_051_R, ARC_052_Y, ARC_053_B, ARC_054_R, ARC_055_Y, ARC_056_B, ARC_057_R, ARC_058_Y, ARC_059_B, ARC_060_R, ARC_061_Y, ARC_062_B, ARC_063_R, ARC_064_Y, ARC_065_B, ARC_066_R, ARC_067_Y]

end FabCards.ARC

end
