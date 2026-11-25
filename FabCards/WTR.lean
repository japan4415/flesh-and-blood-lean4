module

public import FabCards.WTR.Meta

/-!
# Welcome to Rathe (WTR) card definitions and IR transcriptions

Handwritten effect IR transcriptions (`status := .drafted`) overlaid on top of the
auto-generated metadata in `FabCards.WTR.Meta` (docs/card-data.md §4.1-4.2).
All 226 logical cards of WTR are included in `wtrCards`; cards not yet transcribed
retain their generated `.todo` metadata.
-/

@[expose] public section

namespace FabCards.WTR

open Fab
open FabCards.WTR.Meta

/-- Attach abilities and an optional play effect to a generated card, marking it `.drafted`. -/
def draftCard (base : CardDef) (abilities : List Ability := [])
    (playEffect : Option EffectDef := none) : CardDef :=
  { base with
    front := { base.front with abilities := abilities, playEffect := playEffect }
    status := .drafted }

/-- Mark a vanilla or keyword-only card (no additional text abilities) as `.drafted`. -/
def draftVanilla (base : CardDef) : CardDef :=
  { base with status := .drafted }

/-- Helper: standard weapon attack activated ability (`Once per Turn Action - {r}: Attack`). -/
def weaponAttackAbility (resCost : Nat) : Ability :=
  .activated .action true { actionPoints := 1, resources := resCost } [] none false
    { body := .prim .weaponAttack }

/-- Helper: filter for cards with power `≥ 6` (Brute threshold). -/
def power6Filter : CardFilter := { minPower := some 6 }

/-- Helper: filter for cards with cost `≥ 3` (Guardian threshold). -/
def cost3Filter : CardFilter := { minCost := some 3 }

/-- Helper: filter for Brute attacks (attack actions or weapon attacks). -/
def bruteAttackFilter : CardFilter := { supertypes := [.class_ .brute], subtypes := [.attack] }

/-- Helper: filter for Guardian attack action cards. -/
def guardianAttackAction : CardFilter :=
  { supertypes := [.class_ .guardian], types := [.action], subtypes := [.attack] }

/-- Helper: filter for Ninja attack action cards. -/
def ninjaAttackAction : CardFilter :=
  { supertypes := [.class_ .ninja], types := [.action], subtypes := [.attack] }

/-- Helper: filter for cards with `Combo`. -/
def comboFilter : CardFilter := { keywords := [.combo] }

/-- Helper: target spec for 1 weapon attack on the combat chain. -/
def targetWeaponAttack : TargetSpec := { kind := .weaponAttack }

/-! ## Generic Gem (WTR000) -/

/-- Heart of Fyendal (drafted IR). -/
def WTR_000_B : CardDef :=
  draftCard WTR_000_B_meta
    [ .triggered .onPitch false none (some .lessLifeThanOpponent)
        { body := .prim (.gainLife .controller (.const 1)) } ]

/-! ## Brute (WTR001-WTR037) -/

/-- Shared Rhinar triggered ability: discard ≥6{p} during action phase → intimidate. -/
def rhinarAbility : List Ability :=
  [ .triggered (.onDiscard power6Filter true) false none none
      { body := .prim (.intimidate .opposingHero) } ]

/-- Rhinar, Reckless Rampage (drafted IR). -/
def WTR_001 : CardDef := draftCard WTR_001_meta rhinarAbility

/-- Rhinar (Young, drafted IR). -/
def WTR_002 : CardDef := draftCard WTR_002_meta rhinarAbility

/-- Romping Club (drafted IR). -/
def WTR_003 : CardDef :=
  draftCard WTR_003_meta
    [ weaponAttackAbility 2
    , .triggered (.onDiscard power6Filter false) true none none
        { body := .grant .self_ (.addPower (.const 1)) .thisTurn } ]

/-- Scabskin Leathers (drafted IR). -/
def WTR_004 : CardDef :=
  draftCard WTR_004_meta
    [ .activated .action true { actionPoints := 1, resources := 0 } [] none false
        { body := .rollDie6 ⟨0⟩ .nil (.prim (.gainAP .controller (.halfRoundDown ⟨0⟩))) } ]

/-- Barkbone Strapping (drafted IR). -/
def WTR_005 : CardDef :=
  draftCard WTR_005_meta
    [ .activated .instant false {} [{ cost := .destroySelf }] none false
        { body := .rollDie6 ⟨0⟩ .nil (.prim (.gainResource .controller (.halfRoundDown ⟨0⟩))) } ]

/-- Alpha Rampage (drafted IR). -/
def WTR_006_R : CardDef :=
  draftCard WTR_006_R_meta
    [ .triggered .onAttack false none none { body := .prim (.intimidate .opposingHero) } ]
    (some { extraCosts := [{ cost := .discardRandom 1 }] })

/-- Bloodrush Bellow (drafted IR). -/
def WTR_007_Y : CardDef :=
  draftCard WTR_007_Y_meta []
    (some
      { extraCosts := [{ cost := .discardRandom 1 }]
        body := .seqL
          [ .grant (.allMatching .controller bruteAttackFilter) (.addPower (.const 2)) .thisTurn
          , .ifThen (.lastDiscardedMatches power6Filter)
              (.seqL
                [ .prim (.draw .controller (.const 2))
                , .grant .self_ (.grantKeyword .goAgain) .thisTurn ])
              .nop ] })

/-- Reckless Swing (drafted IR). -/
def WTR_008_B : CardDef :=
  draftCard WTR_008_B_meta []
    (some
      { extraCosts := [{ cost := .discardRandom 1 }]
        body := .ifThen (.lastDiscardedMatches power6Filter)
          (.prim (.dealDamage .physical .attackingHero (.const 2)))
          .nop })

/-- Bone Head Barrier (drafted IR). -/
def WTR_010_Y : CardDef :=
  draftCard WTR_010_Y_meta []
    (some
      { body := .rollDie6 ⟨0⟩ .nil
          (.prim (.preventNextDamage .controller (.varVal ⟨0⟩) .thisTurn)) })

/-- Shared 3-color helper for Breakneck Battery. -/
def breakneckBattery (base : CardDef) : CardDef :=
  draftCard base []
    (some
      { extraCosts := [{ cost := .discardRandom 1 }]
        body := .ifThen (.lastDiscardedMatches power6Filter)
          (.grant .self_ (.grantKeyword .goAgain) .thisChainLink)
          .nop })

/-- Breakneck Battery Red (drafted IR). -/
def WTR_011_R : CardDef := breakneckBattery WTR_011_R_meta
/-- Breakneck Battery Yellow (drafted IR). -/
def WTR_012_Y : CardDef := breakneckBattery WTR_012_Y_meta
/-- Breakneck Battery Blue (drafted IR). -/
def WTR_013_B : CardDef := breakneckBattery WTR_013_B_meta

/-- Shared 3-color helper for Barraging Beatdown (+4/+3/+2 if <2 non-equip defenders). -/
def barragingBeatdown (base : CardDef) (bonus : Int) : CardDef :=
  draftCard base []
    (some
      { body := .seqL
          [ .grant (.nextAttack bruteAttackFilter)
              (.conditionalPower (.defendedByFewerNonEquip 2) bonus)
              .thisTurn
          , .prim (.intimidate .opposingHero) ] })

/-- Barraging Beatdown Red (drafted IR). -/
def WTR_017_R : CardDef := barragingBeatdown WTR_017_R_meta 4
/-- Barraging Beatdown Yellow (drafted IR). -/
def WTR_018_Y : CardDef := barragingBeatdown WTR_018_Y_meta 3
/-- Barraging Beatdown Blue (drafted IR). -/
def WTR_019_B : CardDef := barragingBeatdown WTR_019_B_meta 2

/-- Shared 3-color helper for Pack Hunt (onAttack intimidate). -/
def packHunt (base : CardDef) : CardDef :=
  draftCard base
    [ .triggered .onAttack false none none { body := .prim (.intimidate .opposingHero) } ]

/-- Pack Hunt Red (drafted IR). -/
def WTR_023_R : CardDef := packHunt WTR_023_R_meta
/-- Pack Hunt Yellow (drafted IR). -/
def WTR_024_Y : CardDef := packHunt WTR_024_Y_meta
/-- Pack Hunt Blue (drafted IR). -/
def WTR_025_B : CardDef := packHunt WTR_025_B_meta

/-- Shared 3-color helper for Awakening Bellow (intimidate + next Brute attack +3/+2/+1). -/
def awakeningBellow (base : CardDef) (bonus : Int) : CardDef :=
  draftCard base []
    (some
      { body := .seqL
          [ .prim (.intimidate .opposingHero)
          , .grant (.nextCardPlayed { supertypes := [.class_ .brute], types := [.action], subtypes := [.attack] })
              (.addPower (.const bonus))
              .thisTurn ] })

/-- Awakening Bellow Red (drafted IR). -/
def WTR_032_R : CardDef := awakeningBellow WTR_032_R_meta 3
/-- Awakening Bellow Yellow (drafted IR). -/
def WTR_033_Y : CardDef := awakeningBellow WTR_033_Y_meta 2
/-- Awakening Bellow Blue (drafted IR). -/
def WTR_034_B : CardDef := awakeningBellow WTR_034_B_meta 1

/-! ## Guardian (WTR038-WTR075) -/

/-- Shared Bravo activated ability: Action {r}{r}: cost ≥3 attack actions get dominate. Go again. -/
def bravoAbility : List Ability :=
  [ .activated .action false { actionPoints := 1, resources := 2 } [] none true
      { body := .grant
          (.allMatching .controller { types := [.action], subtypes := [.attack], minCost := some 3 })
          (.grantKeyword .dominate)
          .thisTurn } ]

/-- Bravo, Showstopper (drafted IR). -/
def WTR_038 : CardDef := draftCard WTR_038_meta bravoAbility

/-- Bravo (Young, drafted IR). -/
def WTR_039 : CardDef := draftCard WTR_039_meta bravoAbility

/-- Anothos (drafted IR). -/
def WTR_040 : CardDef :=
  draftCard WTR_040_meta
    [ weaponAttackAbility 3
    , .static_ (some (.zoneCountGe .controller .pitch cost3Filter 2)) .self_ (.addPower (.const 2)) ]

/-- Tectonic Plating (drafted IR). -/
def WTR_041 : CardDef :=
  draftCard WTR_041_meta
    [ .activated .action true { actionPoints := 1, resources := 1 } [] none true
        { body := .prim (.createToken .controller ⟨"WTR_075"⟩ 1) } ]

/-- Helm of Isen's Peak (drafted IR). -/
def WTR_042 : CardDef :=
  draftCard WTR_042_meta
    [ .activated .action false { actionPoints := 1, resources := 1 } [{ cost := .destroySelf }] none false
        { body := .grant (.hero .controller) (.addIntellect 1) .thisTurn } ]

/-- Crippling Crush (drafted IR). -/
def WTR_043_R : CardDef :=
  draftCard WTR_043_R_meta
    [ .triggered (.onDealDamage 4 true) false none none
        { body := .prim (.discardRandom .defendingHero (.const 2)) } ]

/-- Spinal Crush (drafted IR). -/
def WTR_044_R : CardDef :=
  draftCard WTR_044_R_meta
    [ .triggered (.onDealDamage 4 true) false none none
        { body := .grant (.playerActionsAndAttacks .defendingHero) .cantGainGoAgain .nextActionPhase } ]

/-- Cranial Crush (drafted IR). -/
def WTR_045_B : CardDef :=
  draftCard WTR_045_B_meta
    [ .triggered (.onDealDamage 4 true) false none none
        { body := .grant (.hero .defendingHero) .cantDrawCards .nextActionPhase } ]

/-- Shared 3-color helper for Disable (Crush → defending hero's arsenal to deck bottom). -/
def disableCard (base : CardDef) : CardDef :=
  draftCard base
    [ .triggered (.onDealDamage 4 true) false none none
        { body := .prim (.putArsenalOnDeckBottom .defendingHero) } ]

/-- Disable Red (drafted IR). -/
def WTR_048_R : CardDef := disableCard WTR_048_R_meta
/-- Disable Yellow (drafted IR). -/
def WTR_049_Y : CardDef := disableCard WTR_049_Y_meta
/-- Disable Blue (drafted IR). -/
def WTR_050_B : CardDef := disableCard WTR_050_B_meta

/-- Shared 3-color helper for Staunch Response (optional pay 4 → +3{d}). -/
def staunchResponse (base : CardDef) : CardDef :=
  draftCard base []
    (some
      { extraCosts := [{ cost := .payResources 4, optional := true }]
        body := .ifThen .additionalCostPaid
          (.grant .self_ (.addDefense (.const 3)) .thisChainLink)
          .nop })

/-- Staunch Response Red (drafted IR). -/
def WTR_051_R : CardDef := staunchResponse WTR_051_R_meta
/-- Staunch Response Yellow (drafted IR). -/
def WTR_052_Y : CardDef := staunchResponse WTR_052_Y_meta
/-- Staunch Response Blue (drafted IR). -/
def WTR_053_B : CardDef := staunchResponse WTR_053_B_meta

/-- Shared 3-color helper for Blessing of Deliverance (reveal top 3/2/1, gain life for cost ≥3). -/
def blessingOfDeliverance (base : CardDef) (revealCount : Nat) : CardDef :=
  draftCard base
    [ .triggered .onEnterArena false none (some (.zoneCountGe .controller .pitch cost3Filter 1))
        { body := .prim (.draw .controller (.const 1)) }
    , .triggered .onStartOfActionPhase false none none
        { body := .seqL
            [ .prim (.destroy .self_)
            , .bindRevealTopCount .controller revealCount cost3Filter ⟨0⟩
                (.prim (.gainLife .controller (.varVal ⟨0⟩))) ] } ]

/-- Blessing of Deliverance Red (drafted IR). -/
def WTR_054_R : CardDef := blessingOfDeliverance WTR_054_R_meta 3
/-- Blessing of Deliverance Yellow (drafted IR). -/
def WTR_055_Y : CardDef := blessingOfDeliverance WTR_055_Y_meta 2
/-- Blessing of Deliverance Blue (drafted IR). -/
def WTR_056_B : CardDef := blessingOfDeliverance WTR_056_B_meta 1

/-- Shared 3-color helper for Buckling Blow (Crush → `-1{d}` counter on target equipment). -/
def bucklingBlow (base : CardDef) : CardDef :=
  draftCard base
    [ .triggered (.onDealDamage 4 true) false none none
        { targets := [{ kind := .equipment .defendingHero }]
          body := .prim (.addCounter (.slot 0) .minusOneDefense (.const 1)) } ]

/-- Buckling Blow Red (drafted IR). -/
def WTR_057_R : CardDef := bucklingBlow WTR_057_R_meta
/-- Buckling Blow Yellow (drafted IR). -/
def WTR_058_Y : CardDef := bucklingBlow WTR_058_Y_meta
/-- Buckling Blow Blue (drafted IR). -/
def WTR_059_B : CardDef := bucklingBlow WTR_059_B_meta

/-- Seismic Surge Token (drafted IR). -/
def WTR_075 : CardDef :=
  draftCard WTR_075_meta
    [ .triggered .onStartOfActionPhase false none none
        { body := .seqL
            [ .prim (.destroy .self_)
            , .grant (.nextCardPlayed guardianAttackAction) (.modifyCost (-1)) .thisTurn ] } ]

/-! ## Ninja (WTR076-WTR112) -/

/-- Shared Katsu hero ability: first attack action hit each turn → may discard cost 0 to tutor Combo. -/
def katsuAbility : List Ability :=
  [ .triggered .onAttackActionHit false (some 1) none
      { body := .may
          (.prim (.discardChoice .controller { maxCost := some 0 } (.const 1)))
          (.prim (.searchDeck .controller comboFilter (some 1) .banished false (some .thisTurn))) } ]

/-- Katsu, the Wanderer (drafted IR). -/
def WTR_076 : CardDef := draftCard WTR_076_meta katsuAbility

/-- Katsu (Young, drafted IR). -/
def WTR_077 : CardDef := draftCard WTR_077_meta katsuAbility

/-- Harmonized Kodachi (drafted IR). -/
def WTR_078 : CardDef :=
  draftCard WTR_078_meta
    [ weaponAttackAbility 1
    , .static_ (some (.zoneCountGe .controller .pitch { maxCost := some 0 } 1)) .self_
        (.grantKeyword .goAgain) ]

/-- Mask of Momentum (drafted IR). -/
def WTR_079 : CardDef :=
  draftCard WTR_079_meta
    [ .triggered (.onConsecutiveHitLink 3) true none none
        { body := .prim (.draw .controller (.const 1)) } ]

/-- Breaking Scales (drafted IR). -/
def WTR_080 : CardDef :=
  draftCard WTR_080_meta
    [ .activated .attackReaction false {} [{ cost := .destroySelf }] none false
        { targets := [{ kind := .attackAction, filter := comboFilter }]
          body := .grant (.obj (.slot 0)) (.addPower (.const 1)) .thisChainLink } ]

/-- Lord of Wind (drafted IR — exercises Combo-gated optional `{x}` cost and `NumExpr.xValue`). -/
def WTR_081_B : CardDef :=
  draftCard WTR_081_B_meta []
    (some
      { extraCosts :=
          [ { cost := .payX
              optional := true
              cond := some (.prevChainLinkNamed "Mugenshi: RELEASE") } ]
        body := .ifThen .additionalCostPaid
          (.seqL
            [ .prim (.shuffleZoneIntoDeck .controller .graveyard
                { nameIn := ["Surging Strike", "Whelming Gustwave", "Mugenshi: RELEASE"] }
                none false)
            , .grant .self_ (.addPower .xValue) .thisChainLink ])
          .nop })

/-- Ancestral Empowerment (drafted IR). -/
def WTR_082_R : CardDef :=
  draftCard WTR_082_R_meta []
    (some
      { targets := [{ kind := .attackAction, filter := ninjaAttackAction }]
        body := .seqL
          [ .grant (.obj (.slot 0)) (.addPower (.const 1)) .thisChainLink
          , .prim (.draw .controller (.const 1)) ] })

/-- Hurricane Technique (drafted IR). -/
def WTR_084_Y : CardDef :=
  draftCard WTR_084_Y_meta []
    (some
      { body := .ifThen (.prevChainLinkNamed "Rising Knee Thrust")
          (.seqL
            [ .grant .self_ (.addPower (.const 1)) .thisChainLink
            , .grant .self_ (.grantKeyword .goAgain) .thisChainLink
            , .grant .self_
                (.grantTrigger .onHit none (.prim (.moveCard .self_ .hand .top false)))
                .thisChainLink ])
          .nop })

/-- Pounding Gale (drafted IR). -/
def WTR_085_R : CardDef :=
  draftCard WTR_085_R_meta []
    (some
      { body := .ifThen (.prevChainLinkNamed "Open the Center")
          (.grant .self_ .doubleDamageToHero .thisChainLink)
          .nop })

/-- Shared 3-color helper for Fluster Fist (Combo: +1{p} per hit this combat chain). -/
def flusterFist (base : CardDef) : CardDef :=
  draftCard base []
    (some
      { body := .ifThen (.prevChainLinkNamed "Open the Center")
          (.grant .self_ (.addPower .chainHits) .thisChainLink)
          .nop })

/-- Fluster Fist Red (drafted IR). -/
def WTR_086_R : CardDef := flusterFist WTR_086_R_meta
/-- Fluster Fist Yellow (drafted IR). -/
def WTR_087_Y : CardDef := flusterFist WTR_087_Y_meta
/-- Fluster Fist Blue (drafted IR). -/
def WTR_088_B : CardDef := flusterFist WTR_088_B_meta

/-- Head Jab Red (vanilla Go Again, drafted IR). -/
def WTR_098_R : CardDef := draftVanilla WTR_098_R_meta
/-- Head Jab Yellow (vanilla Go Again, drafted IR). -/
def WTR_099_Y : CardDef := draftVanilla WTR_099_Y_meta
/-- Head Jab Blue (vanilla Go Again, drafted IR). -/
def WTR_100_B : CardDef := draftVanilla WTR_100_B_meta

/-- Leg Tap Red, whose printed Go Again is handled by combat resolution. -/
def WTR_101_R : CardDef := { WTR_101_R_meta with status := .full }

/-- Leg Tap Yellow, whose printed Go Again is handled by combat resolution. -/
def WTR_102_Y : CardDef := { WTR_102_Y_meta with status := .full }

/-- Leg Tap Blue, whose printed Go Again is handled by combat resolution. -/
def WTR_103_B : CardDef := { WTR_103_B_meta with status := .full }

/-- Surging Strike Red (vanilla Go Again, drafted IR). -/
def WTR_107_R : CardDef := draftVanilla WTR_107_R_meta
/-- Surging Strike Yellow (vanilla Go Again, drafted IR). -/
def WTR_108_Y : CardDef := draftVanilla WTR_108_Y_meta
/-- Surging Strike Blue (vanilla Go Again, drafted IR). -/
def WTR_109_B : CardDef := draftVanilla WTR_109_B_meta

/-- Shared 3-color helper for Whelming Gustwave (Combo: +1{p}, go again, onHit draw 1). -/
def whelmingGustwave (base : CardDef) : CardDef :=
  draftCard base []
    (some
      { body := .ifThen (.prevChainLinkNamed "Surging Strike")
          (.seqL
            [ .grant .self_ (.addPower (.const 1)) .thisChainLink
            , .grant .self_ (.grantKeyword .goAgain) .thisChainLink
            , .grant .self_
                (.grantTrigger .onHit none (.prim (.draw .controller (.const 1))))
                .thisChainLink ])
          .nop })

/-- Whelming Gustwave Red (drafted IR). -/
def WTR_110_R : CardDef := whelmingGustwave WTR_110_R_meta
/-- Whelming Gustwave Yellow (drafted IR). -/
def WTR_111_Y : CardDef := whelmingGustwave WTR_111_Y_meta
/-- Whelming Gustwave Blue (drafted IR). -/
def WTR_112_B : CardDef := whelmingGustwave WTR_112_B_meta

/-! ## Warrior (WTR113-WTR149) -/

/-- Shared Dorinthea hero ability: first weapon attack hit each turn → additional weapon attack. -/
def dorintheaAbility : List Ability :=
  [ .triggered .onWeaponAttackHit false (some 1) none
      { body := .grant (.obj .currentAttack) .additionalWeaponAttack .thisTurn } ]

/-- Dorinthea Ironsong (drafted IR). -/
def WTR_113 : CardDef := draftCard WTR_113_meta dorintheaAbility

/-- Dorinthea (Young, drafted IR). -/
def WTR_114 : CardDef := draftCard WTR_114_meta dorintheaAbility

/-- Dawnblade (drafted IR). -/
def WTR_115 : CardDef :=
  draftCard WTR_115_meta
    [ weaponAttackAbility 1
    , .triggered .onHit false (some 2) none
        { body := .prim (.addCounter .self_ .plusOnePower (.const 1)) }
    , .triggered .onStartOfEndPhase false none (some .sourceNotHitThisTurn)
        { body := .prim (.removeAllCounters .self_ .plusOnePower) } ]

/-- Braveforge Bracers (drafted IR). -/
def WTR_116 : CardDef :=
  draftCard WTR_116_meta
    [ .activated .action true { actionPoints := 1, resources := 1 } [] (some .weaponHitThisTurn) true
        { body := .grant (.nextAttack CardFilter.weaponAttack) (.addPower (.const 1)) .thisTurn } ]

/-- Refraction Bolters (drafted IR). -/
def WTR_117 : CardDef :=
  draftCard WTR_117_meta
    [ .triggered .onWeaponAttackHit false none none
        { body := .may (.prim (.destroy .self_))
            (.grant (.obj .currentAttack) (.grantKeyword .goAgain) .thisChainLink) } ]

/-- Glint the Quicksilver (drafted IR). -/
def WTR_118_B : CardDef :=
  draftCard WTR_118_B_meta []
    (some
      { targets := [targetWeaponAttack]
        body := .seqL
          [ .grant (.obj (.slot 0)) (.grantKeyword .goAgain) .thisChainLink
          , .ifThen .defendedFromHandThisLink (.prim (.draw .controller (.const 1))) .nop ] })

/-- Steelblade Supremacy (drafted IR). -/
def WTR_119_R : CardDef :=
  draftCard WTR_119_R_meta []
    (some
      { targets := [{ kind := .weapon .controller }]
        body := .seqL
          [ .grant (.obj (.slot 0)) (.addPower (.const 2)) .thisTurn
          , .grant (.obj (.slot 0))
              (.grantTrigger .onHit none (.prim (.draw .controller (.const 1))))
              .thisTurn ] })

/-- Rout (drafted IR). -/
def WTR_120_R : CardDef :=
  draftCard WTR_120_R_meta []
    (some
      { targets := [targetWeaponAttack]
        body := .seqL
          [ .grant (.obj (.slot 0)) (.addPower (.const 3)) .thisChainLink
          , .ifThen .defendedFromHandThisLink
              (.may (.prim (.returnDefendingCardToHand CardFilter.nonEquipment)) .nop)
              .nop ] })

/-- Shared 3-color helper for Overpower (weapon attack +base, or +repriseBonus if Reprise). -/
def overpowerCard (base : CardDef) (baseBonus repriseBonus : Int) : CardDef :=
  draftCard base []
    (some
      { targets := [targetWeaponAttack]
        body := .ifThen .defendedFromHandThisLink
          (.grant (.obj (.slot 0)) (.addPower (.const repriseBonus)) .thisChainLink)
          (.grant (.obj (.slot 0)) (.addPower (.const baseBonus)) .thisChainLink) })

/-- Overpower Red (drafted IR). -/
def WTR_123_R : CardDef := overpowerCard WTR_123_R_meta 4 6
/-- Overpower Yellow (drafted IR). -/
def WTR_124_Y : CardDef := overpowerCard WTR_124_Y_meta 3 5
/-- Overpower Blue (drafted IR). -/
def WTR_125_B : CardDef := overpowerCard WTR_125_B_meta 2 4

/-- Shared 3-color helper for Sharpen Steel (next weapon attack +3/+2/+1). -/
def sharpenSteel (base : CardDef) (bonus : Int) : CardDef :=
  draftCard base []
    (some
      { body := .grant (.nextAttack CardFilter.weaponAttack) (.addPower (.const bonus)) .thisTurn })

/-- Sharpen Steel Red (drafted IR). -/
def WTR_141_R : CardDef := sharpenSteel WTR_141_R_meta 3
/-- Sharpen Steel Yellow (drafted IR). -/
def WTR_142_Y : CardDef := sharpenSteel WTR_142_Y_meta 2
/-- Sharpen Steel Blue (drafted IR). -/
def WTR_143_B : CardDef := sharpenSteel WTR_143_B_meta 1

/-! ## Generic Equipment, Attacks, Reactions, Instants, Items, Tokens (WTR150-WTR225) -/

/-- Fyendal's Spring Tunic (drafted IR). -/
def WTR_150 : CardDef :=
  draftCard WTR_150_meta
    [ .triggered .onStartOfTurn false none (some (.sourceCounterLt .energy 3))
        { body := .may (.prim (.addCounter .self_ .energy (.const 1))) .nop }
    , .activated .instant false {} [{ cost := .removeCounters .energy 3 }] none false
        { body := .prim (.gainResource .controller (.const 1)) } ]

/-- Hope Merchant's Hood (drafted IR). -/
def WTR_151 : CardDef :=
  draftCard WTR_151_meta
    [ .activated .instant false {} [{ cost := .destroySelf }] none false
        { body := .prim (.shuffleZoneIntoDeck .controller .hand CardFilter.any none true) } ]

/-- Snapdragon Scalers (drafted IR). -/
def WTR_154 : CardDef :=
  draftCard WTR_154_meta
    [ .activated .attackReaction false {} [{ cost := .destroySelf }] none false
        { targets := [{ kind := .attackAction, filter := { maxCost := some 1 } }]
          body := .grant (.obj (.slot 0)) (.grantKeyword .goAgain) .thisChainLink } ]

/-- Ironrot Helm (keyword-only Blade Break, drafted IR). -/
def WTR_155 : CardDef := draftVanilla WTR_155_meta
/-- Ironrot Plate (keyword-only Blade Break, drafted IR). -/
def WTR_156 : CardDef := draftVanilla WTR_156_meta
/-- Ironrot Gauntlet (keyword-only Blade Break, drafted IR). -/
def WTR_157 : CardDef := draftVanilla WTR_157_meta
/-- Ironrot Legs (keyword-only Blade Break, drafted IR). -/
def WTR_158 : CardDef := draftVanilla WTR_158_meta

/-- Enlightened Strike (drafted IR — modal choice + deck-bottom extra cost). -/
def WTR_159_R : CardDef :=
  draftCard WTR_159_R_meta []
    (some
      { extraCosts := [{ cost := .putHandCardOnDeckBottom }]
        body := .chooseOneL
          [ .grant .self_ (.grantTrigger .onAttack none (.prim (.draw .controller (.const 1)))) .thisChainLink
          , .grant .self_ (.addPower (.const 2)) .thisChainLink
          , .grant .self_ (.grantKeyword .goAgain) .thisChainLink ] })

/-- Tome of Fyendal (drafted IR). -/
def WTR_160_Y : CardDef :=
  draftCard WTR_160_Y_meta []
    (some
      { body := .seqL
          [ .prim (.draw .controller (.const 2))
          , .ifThen .playedFromArsenal
              (.prim (.gainLife .controller (.handCount .controller)))
              .nop ] })

/-- Crazy Brew (drafted IR — 6-sided die branches 1-2 / 3-4 / 5-6). -/
def WTR_162_B : CardDef :=
  draftCard WTR_162_B_meta
    [ .activated .action false { actionPoints := 1 } [{ cost := .destroySelf }] none false
        { body := .rollDie6 ⟨0⟩
            (.cons 1 2 (.seqL [.prim (.loseLife .controller (.const 2)), .prim (.gainAP .controller (.const 1))])
            (.cons 3 4 (.seqL [.prim (.gainLife .controller (.const 2)), .prim (.gainAP .controller (.const 1))])
            (.cons 5 6 (.seqL
              [ .prim (.gainResource .controller (.const 2))
              , .prim (.gainAP .controller (.const 2))
              , .grant (.nextAttack CardFilter.any) (.addPower (.const 2)) .thisTurn ])
            .nil)))
            .nop } ]

/-- Remembrance (drafted IR). -/
def WTR_163_Y : CardDef :=
  draftCard WTR_163_Y_meta []
    (some
      { body := .seqL
          [ .prim (.shuffleZoneIntoDeck .controller .graveyard { types := [.action] } (some 3) false)
          , .prim (.banish .self_ false) ] })

/-- Shared 3-color helper for Drone of Brutality (replacement: graveyard → deck bottom). -/
def droneOfBrutality (base : CardDef) : CardDef :=
  draftCard base
    [ .replacement .standard (.selfWouldGoToGraveyard .any)
        { body := .prim (.moveCard .self_ .deck .bottom false) } ]

/-- Drone of Brutality Red (drafted IR). -/
def WTR_164_R : CardDef := droneOfBrutality WTR_164_R_meta
/-- Drone of Brutality Yellow (drafted IR). -/
def WTR_165_Y : CardDef := droneOfBrutality WTR_165_Y_meta
/-- Drone of Brutality Blue (drafted IR). -/
def WTR_166_B : CardDef := droneOfBrutality WTR_166_B_meta

/-- Shared 3-color helper for Snatch (onHit draw 1). -/
def snatchCard (base : CardDef) : CardDef :=
  draftCard base
    [ .triggered .onHit false none none { body := .prim (.draw .controller (.const 1)) } ]

/-- Snatch Red. -/
def WTR_167_R : CardDef := { snatchCard WTR_167_R_meta with status := .full }
/-- Snatch Yellow. -/
def WTR_168_Y : CardDef := { snatchCard WTR_168_Y_meta with status := .full }
/-- Snatch Blue (drafted IR). -/
def WTR_169_B : CardDef := snatchCard WTR_169_B_meta

/-- Shared 3-color helper for Sigil of Solace (Instant gain 3/2/1 life). -/
def sigilOfSolace (base : CardDef) (amount : Int) : CardDef :=
  draftCard base []
    (some { body := .prim (.gainLife .controller (.const amount)) })

/-- Sigil of Solace Red (drafted IR). -/
def WTR_173_R : CardDef := sigilOfSolace WTR_173_R_meta 3
/-- Sigil of Solace Yellow (drafted IR). -/
def WTR_174_Y : CardDef := sigilOfSolace WTR_174_Y_meta 2
/-- Sigil of Solace Blue (drafted IR). -/
def WTR_175_B : CardDef := sigilOfSolace WTR_175_B_meta 1

/-- Raging Onslaught Red (vanilla, drafted IR). -/
def WTR_188_R : CardDef := draftVanilla WTR_188_R_meta
/-- Raging Onslaught Yellow (vanilla, drafted IR). -/
def WTR_189_Y : CardDef := draftVanilla WTR_189_Y_meta
/-- Raging Onslaught Blue (vanilla, drafted IR). -/
def WTR_190_B : CardDef := draftVanilla WTR_190_B_meta

/-- Shared 3-color helper for Scar for a Scar (onPlay lessLife → goAgain). -/
def scarForAScar (base : CardDef) : CardDef :=
  draftCard base
    [ .triggered .onPlay false none (some .lessLifeThanOpponent)
        { body := .grant .self_ (.grantKeyword .goAgain) .thisChainLink } ]

/-- Scar for a Scar Red (drafted IR). -/
def WTR_191_R : CardDef := scarForAScar WTR_191_R_meta
/-- Scar for a Scar Yellow (drafted IR). -/
def WTR_192_Y : CardDef := scarForAScar WTR_192_Y_meta
/-- Scar for a Scar Blue (drafted IR). -/
def WTR_193_B : CardDef := scarForAScar WTR_193_B_meta

/-- Wounding Blow Red (vanilla, drafted IR). -/
def WTR_203_R : CardDef := draftVanilla WTR_203_R_meta
/-- Wounding Blow Yellow (vanilla, drafted IR). -/
def WTR_204_Y : CardDef := draftVanilla WTR_204_Y_meta
/-- Wounding Blow Blue (vanilla, drafted IR). -/
def WTR_205_B : CardDef := draftVanilla WTR_205_B_meta

/-- Shared 3-color helper for Pummel (per-mode `ModeSpec` targets: club/hammer vs cost ≥2 attack). -/
def pummelCard (base : CardDef) (bonus : Int) : CardDef :=
  draftCard base []
    (some
      { modes :=
          [ { targets := [{ kind := .weaponAttack, filter := { anySubtypes := [.club, .hammer] } }]
              body := .grant (.obj (.slot 0)) (.addPower (.const bonus)) .thisChainLink }
          , { targets := [{ kind := .attackAction, filter := { minCost := some 2 } }]
              body := .seqL
                [ .grant (.obj (.slot 0)) (.addPower (.const bonus)) .thisChainLink
                , .grant (.obj (.slot 0))
                    (.grantTrigger .onHitHero none
                      (.prim (.discardChoice .defendingHero CardFilter.any (.const 1))))
                    .thisChainLink ] } ] })

/-- Pummel Red (drafted IR). -/
def WTR_206_R : CardDef := pummelCard WTR_206_R_meta 4
/-- Pummel Yellow (drafted IR). -/
def WTR_207_Y : CardDef := pummelCard WTR_207_Y_meta 3
/-- Pummel Blue (drafted IR). -/
def WTR_208_B : CardDef := pummelCard WTR_208_B_meta 2

/-- Shared 3-color helper for Razor Reflex (per-mode `ModeSpec` targets: dagger/sword vs cost ≤1 attack). -/
def razorReflex (base : CardDef) (bonus : Int) : CardDef :=
  draftCard base []
    (some
      { modes :=
          [ { targets := [{ kind := .weaponAttack, filter := { anySubtypes := [.dagger, .sword] } }]
              body := .grant (.obj (.slot 0)) (.addPower (.const bonus)) .thisChainLink }
          , { targets := [{ kind := .attackAction, filter := { maxCost := some 1 } }]
              body := .seqL
                [ .grant (.obj (.slot 0)) (.addPower (.const bonus)) .thisChainLink
                , .grant (.obj (.slot 0))
                    (.grantTrigger .onHit none
                      (.grant .self_ (.grantKeyword .goAgain) .thisChainLink))
                    .thisChainLink ] } ] })

/-- Razor Reflex Red (drafted IR). -/
def WTR_209_R : CardDef := razorReflex WTR_209_R_meta 3
/-- Razor Reflex Yellow (drafted IR). -/
def WTR_210_Y : CardDef := razorReflex WTR_210_Y_meta 2
/-- Razor Reflex Blue (drafted IR). -/
def WTR_211_B : CardDef := razorReflex WTR_211_B_meta 1

/-- Shared 3-color helper for Sink Below (may put hand card on deck bottom; if done, draw 1). -/
def sinkBelow (base : CardDef) : CardDef :=
  draftCard base []
    (some
      { body := .may
          (.prim (.putHandOnDeck .controller .bottom))
          (.prim (.draw .controller (.const 1))) })

/-- Sink Below Red (drafted IR). -/
def WTR_215_R : CardDef := sinkBelow WTR_215_R_meta
/-- Sink Below Yellow (drafted IR). -/
def WTR_216_Y : CardDef := sinkBelow WTR_216_Y_meta
/-- Sink Below Blue (drafted IR). -/
def WTR_217_B : CardDef := sinkBelow WTR_217_B_meta

/-- Quicken Token (drafted IR). -/
def WTR_225 : CardDef :=
  draftCard WTR_225_meta
    [ .triggered .onPlayAttackOrWeapon false none none
        { body := .seqL
            [ .prim (.destroy .self_)
            , .grant (.obj .currentAttack) (.grantKeyword .goAgain) .thisChainLink ] } ]

/-! ## Merged WTR card list (all 226 logical cards) -/

/-- All WTR cards with handwritten overrides. -/
def draftedCards : List CardDef :=
  [ WTR_000_B
  , WTR_001, WTR_002, WTR_003, WTR_004, WTR_005, WTR_006_R, WTR_007_Y, WTR_008_B, WTR_010_Y
  , WTR_011_R, WTR_012_Y, WTR_013_B, WTR_017_R, WTR_018_Y, WTR_019_B
  , WTR_023_R, WTR_024_Y, WTR_025_B, WTR_032_R, WTR_033_Y, WTR_034_B
  , WTR_038, WTR_039, WTR_040, WTR_041, WTR_042, WTR_043_R, WTR_044_R, WTR_045_B
  , WTR_048_R, WTR_049_Y, WTR_050_B, WTR_051_R, WTR_052_Y, WTR_053_B
  , WTR_054_R, WTR_055_Y, WTR_056_B, WTR_057_R, WTR_058_Y, WTR_059_B, WTR_075
  , WTR_076, WTR_077, WTR_078, WTR_079, WTR_080, WTR_081_B, WTR_082_R, WTR_084_Y, WTR_085_R
  , WTR_086_R, WTR_087_Y, WTR_088_B, WTR_098_R, WTR_099_Y, WTR_100_B, WTR_101_R, WTR_102_Y
  , WTR_103_B
  , WTR_107_R, WTR_108_Y, WTR_109_B, WTR_110_R, WTR_111_Y, WTR_112_B
  , WTR_113, WTR_114, WTR_115, WTR_116, WTR_117, WTR_118_B, WTR_119_R, WTR_120_R
  , WTR_123_R, WTR_124_Y, WTR_125_B, WTR_141_R, WTR_142_Y, WTR_143_B
  , WTR_150, WTR_151, WTR_154, WTR_155, WTR_156, WTR_157, WTR_158
  , WTR_159_R, WTR_160_Y, WTR_162_B, WTR_163_Y
  , WTR_164_R, WTR_165_Y, WTR_166_B, WTR_167_R, WTR_168_Y, WTR_169_B
  , WTR_173_R, WTR_174_Y, WTR_175_B, WTR_188_R, WTR_189_Y, WTR_190_B
  , WTR_191_R, WTR_192_Y, WTR_193_B, WTR_203_R, WTR_204_Y, WTR_205_B
  , WTR_206_R, WTR_207_Y, WTR_208_B, WTR_209_R, WTR_210_Y, WTR_211_B
  , WTR_215_R, WTR_216_Y, WTR_217_B, WTR_225 ]

/-- Complete list of all 226 WTR logical cards with drafted IR overrides applied. -/
def wtrCards : List CardDef :=
  allMeta.map fun base =>
    match draftedCards.find? (fun c => c.id == base.id) with
    | some drafted => drafted
    | none => base

end FabCards.WTR

end
