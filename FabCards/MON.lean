module

public import FabCards.MON.Meta

/-!
# Monarch (MON — Set 4) card definitions and IR transcriptions

Handwritten card definitions and draft effects overlaid on the generated metadata in
`FabCards.MON.Meta` for all 307 logical cards of Monarch (`MON000`–`MON306`).
-/

@[expose] public section

namespace FabCards.MON

open Fab
open FabCards.MON.Meta

/-- Attach draft rules to a generated MON card. -/
def draftedCard (base : CardDef) (abilities : List Ability := [])
    (playEffect : Option EffectDef := none)
    (playRestriction : PlayRestriction := .always)
    (playFromBanished : Option PlayRestriction := none) : CardDef :=
  { base with
    front := { base.front with
      abilities := abilities
      playEffect := playEffect
      playRestriction := playRestriction
      playFromBanished := playFromBanished }
    status := .drafted }

/-- Mark a card as `.full` once its rules are covered by scenario or shared keyword tests. -/
def verifiedCard (base : CardDef) : CardDef :=
  { base with status := .full }

/-! ## Shared MON filters & ability helpers -/

/-- Standard weapon attack activated ability (`Once per Turn Action - {r}: Attack`). -/
def weaponAttackAbility (resCost : Nat) (grantsGoAgain : Bool := false) : Ability :=
  .activated .action true { actionPoints := 1, resources := resCost } [] none grantsGoAgain
    { body := .prim .weaponAttack }

/-- Filter for yellow cards. -/
def yellowFilter : CardFilter := { color := some .yellow }
/-- Filter for Light cards. -/
def lightFilter : CardFilter := { supertypes := [.talent .light] }
/-- Filter for Shadow cards. -/
def shadowFilter : CardFilter := { supertypes := [.talent .shadow] }
/-- Filter for Illusionist cards. -/
def illusionistFilter : CardFilter := { supertypes := [.class_ .illusionist] }
/-- Filter for Illusionist auras. -/
def illusionistAuraFilter : CardFilter := { supertypes := [.class_ .illusionist], subtypes := [.aura] }
/-- Filter for Illusionist attack action cards. -/
def illusionistAttackFilter : CardFilter :=
  { supertypes := [.class_ .illusionist], types := [.action], subtypes := [.attack] }
/-- Filter for cards with Phantasm. -/
def phantasmFilter : CardFilter := { keywords := [.phantasm] }
/-- Filter for cards with Blood Debt. -/
def bloodDebtFilter : CardFilter := { keywords := [.bloodDebt] }
/-- Filter for cards with power `≥ 6`. -/
def power6Filter : CardFilter := { minPower := some 6 }
/-- Filter for cards with power `≤ 3`. -/
def powerLe3Filter : CardFilter := { maxPower := some 3 }
/-- Filter for attack action cards with base power `≤ 3`. -/
def attackPowerLe3Filter : CardFilter :=
  { types := [.action], subtypes := [.attack], maxPower := some 3 }
/-- Filter for attack action cards with cost `≤ maxC`. -/
def attackCostLeFilter (maxC : Nat) : CardFilter :=
  { types := [.action], subtypes := [.attack], maxCost := some maxC }
/-- Filter for Brute attack action cards. -/
def bruteAttackFilter : CardFilter :=
  { supertypes := [.class_ .brute], types := [.action], subtypes := [.attack] }
/-- Filter for Shadow or Brute attack action cards (modeled via Shadow / attack action). -/
def shadowAttackFilter : CardFilter :=
  { supertypes := [.talent .shadow], types := [.action], subtypes := [.attack] }
/-- Filter for Runeblade cards. -/
def runebladeFilter : CardFilter := { supertypes := [.class_ .runeblade] }
/-- Filter for Runeblade/Shadow actions. -/
def shadowActionFilter : CardFilter := { supertypes := [.talent .shadow], types := [.action] }
/-- Filter for Axe weapons. -/
def axeFilter : CardFilter := { types := [.weapon], subtypes := [.axe] }
/-- Filter for non-attack action cards (action cards excluding attack subtype — modeled via `types := [.action]`). -/
def actionCardFilter : CardFilter := { types := [.action] }
/-- Filter for non-attack Blood Debt cards. -/
def bloodDebtActionFilter : CardFilter := { types := [.action], keywords := [.bloodDebt] }
/-- Filter for Aura permanents. -/
def auraFilter : CardFilter := { subtypes := [.aura] }
/-- Filter for any weapon. -/
def weaponFilter : CardFilter := { types := [.weapon] }
/-- Filter for Minnowism by name. -/
def minnowismFilter : CardFilter := { nameIn := ["Minnowism"] }
/-- Target spec for 1 hero. -/
def targetHero : TargetSpec := { kind := .hero }
/-- Target spec for 1 attack action card. -/
def targetAttackAction : TargetSpec := { kind := .attackAction }

/-! ## Light Landmark (MON000) -/

/-- Great Library of Solana (MON_000). -/
def MON_000 : CardDef :=
  draftedCard MON_000_meta
    [ .triggered .onStartOfEndPhase false none
        (some (.zoneCountGe .turnPlayer .pitch yellowFilter 2))
        { body := .grant (.hero .turnPlayer) (.addIntellect 1) .thisTurn }
    , .activated .action false { actionPoints := 1, resources := 0 }
        [{ cost := .discardChoice yellowFilter 2 }] none true
        { body := .prim (.destroy .self_) } ]

/-! ## Light Illusionist (MON001–MON028) -/

/-- Shared Prism hero activated ability: Once per Turn Instant - `{r}{r}`, banish soul → Spectral Shield. -/
def prismHeroAbilities : List Ability :=
  [ .activated .instant true { resources := 2 } [{ cost := .banishFromSoul 1 }] none false
      { body := .prim (.createToken .controller ⟨"MON_104"⟩ 1) } ]

/-- Prism, Sculptor of Arc Light (MON_001). -/
def MON_001 : CardDef := draftedCard MON_001_meta prismHeroAbilities

/-- Prism (Young, MON_002). -/
def MON_002 : CardDef := draftedCard MON_002_meta prismHeroAbilities

/-- Luminaris (MON_003). -/
def MON_003 : CardDef :=
  draftedCard MON_003_meta
    [ .static_ none (.allMatching .controller illusionistAuraFilter) (.auraIsWeapon 1 0 false)
    , .static_ (some (.zoneCountGe .controller .pitch yellowFilter 1))
        (.allMatching .controller illusionistAttackFilter) (.grantKeyword .goAgain) ]

/-- Herald of Erudition Yellow (MON_004_Y). -/
def MON_004_Y : CardDef :=
  draftedCard MON_004_Y_meta
    [ .triggered .onHit false none none
        { body := .seqL
            [ .prim (.moveCard .self_ .soul .bottom false)
            , .prim (.draw .controller (.const 2)) ] } ]

/-- Arc Light Sentinel Yellow (MON_005_Y). -/
def MON_005_Y : CardDef :=
  draftedCard MON_005_Y_meta
    [ .static_ none .self_ .mustBeAttackTarget ]

/-- Genesis Yellow (MON_006_Y). -/
def MON_006_Y : CardDef :=
  draftedCard MON_006_Y_meta
    [ .triggered .onStartOfTurn false none none
        { body := .may (.prim (.charge .controller))
            (.seqL
              [ .prim (.createToken .controller ⟨"MON_104"⟩ 1)
              , .prim (.draw .controller (.const 1)) ]) } ]

/-- Herald of Judgment Yellow (MON_007_Y). -/
def MON_007_Y : CardDef :=
  draftedCard MON_007_Y_meta
    [ .triggered .onHit false none none
        { body := .seqL
            [ .prim (.moveCard .self_ .soul .bottom false)
            , .grant (.hero .defendingHero) .cantPlayFromBanished .untilEndOfNextTurn ] } ]

/-- Shared helper for Herald of Triumph. -/
def heraldOfTriumph (base : CardDef) : CardDef :=
  draftedCard base
    [ .static_ none (.allMatching .defendingHero CardFilter.attackAction) (.addPower (.const (-1)))
    , .triggered .onHit false none none
        { body := .prim (.moveCard .self_ .soul .bottom false) } ]

/-- Herald of Triumph Red (MON_008_R). -/
def MON_008_R : CardDef := heraldOfTriumph MON_008_R_meta
/-- Herald of Triumph Yellow (MON_009_Y). -/
def MON_009_Y : CardDef := heraldOfTriumph MON_009_Y_meta
/-- Herald of Triumph Blue (MON_010_B). -/
def MON_010_B : CardDef := heraldOfTriumph MON_010_B_meta

/-- Parable of Humility Yellow (MON_011_Y). -/
def MON_011_Y : CardDef :=
  draftedCard MON_011_Y_meta
    [ .static_ none (.allMatching .opposingHero CardFilter.attackAction) (.addPower (.const (-1))) ]

/-- Merciful Retribution Yellow (MON_012_Y). -/
def MON_012_Y : CardDef :=
  draftedCard MON_012_Y_meta
    [ .triggered .onDestroy false none none
        { targets := [targetHero]
          body := .seqL
            [ .prim (.dealDamage .arcane (.ownerOfSlot 0) (.const 1))
            , .prim (.moveCard .self_ .soul .bottom false) ] } ]

/-- Ode to Wrath Yellow (MON_013_Y). -/
def MON_013_Y : CardDef :=
  draftedCard MON_013_Y_meta
    [ .triggered (.onDealDamage 1 true) false none none
        { body := .prim (.loseLife .opposingHero (.const 1)) }
    , .static_ none (.allMatching .controller illusionistAttackFilter) (.grantKeyword .goAgain) ]

/-- Shared helper for Herald of Protection. -/
def heraldOfProtection (base : CardDef) : CardDef :=
  draftedCard base
    [ .triggered .onHit false none none
        { body := .seqL
            [ .prim (.moveCard .self_ .soul .bottom false)
            , .prim (.createToken .controller ⟨"MON_104"⟩ 1) ] } ]

/-- Herald of Protection Red (MON_014_R). -/
def MON_014_R : CardDef := heraldOfProtection MON_014_R_meta
/-- Herald of Protection Yellow (MON_015_Y). -/
def MON_015_Y : CardDef := heraldOfProtection MON_015_Y_meta
/-- Herald of Protection Blue (MON_016_B). -/
def MON_016_B : CardDef := heraldOfProtection MON_016_B_meta

/-- Shared helper for Herald of Ravages. -/
def heraldOfRavages (base : CardDef) : CardDef :=
  draftedCard base
    [ .triggered .onHit false none none
        { targets := [targetHero]
          body := .seqL
            [ .prim (.moveCard .self_ .soul .bottom false)
            , .prim (.dealDamage .arcane (.ownerOfSlot 0) (.const 1)) ] } ]

/-- Herald of Ravages Red (MON_017_R). -/
def MON_017_R : CardDef := heraldOfRavages MON_017_R_meta
/-- Herald of Ravages Yellow (MON_018_Y). -/
def MON_018_Y : CardDef := heraldOfRavages MON_018_Y_meta
/-- Herald of Ravages Blue (MON_019_B). -/
def MON_019_B : CardDef := heraldOfRavages MON_019_B_meta

/-- Shared helper for Herald of Rebirth. -/
def heraldOfRebirth (base : CardDef) : CardDef :=
  draftedCard base
    [ .triggered .onHit false none none
        { targets := [{ kind := .cardInZone .controller .graveyard, filter := phantasmFilter, minCount := 0, maxCount := some 1 }]
          body := .seqL
            [ .prim (.moveCard .self_ .soul .bottom false)
            , .prim (.moveCard (.slot 0) .deck .top false) ] } ]

/-- Herald of Rebirth Red (MON_020_R). -/
def MON_020_R : CardDef := heraldOfRebirth MON_020_R_meta
/-- Herald of Rebirth Yellow (MON_021_Y). -/
def MON_021_Y : CardDef := heraldOfRebirth MON_021_Y_meta
/-- Herald of Rebirth Blue (MON_022_B). -/
def MON_022_B : CardDef := heraldOfRebirth MON_022_B_meta

/-- Shared helper for Herald of Tenacity & Wartune Herald (hit → soul). -/
def hitToSoul (base : CardDef) : CardDef :=
  draftedCard base
    [ .triggered .onHit false none none
        { body := .prim (.moveCard .self_ .soul .bottom false) } ]

/-- Herald of Tenacity Red (MON_023_R). -/
def MON_023_R : CardDef := hitToSoul MON_023_R_meta
/-- Herald of Tenacity Yellow (MON_024_Y). -/
def MON_024_Y : CardDef := hitToSoul MON_024_Y_meta
/-- Herald of Tenacity Blue (MON_025_B). -/
def MON_025_B : CardDef := hitToSoul MON_025_B_meta

/-- Wartune Herald Red (MON_026_R). -/
def MON_026_R : CardDef := hitToSoul MON_026_R_meta
/-- Wartune Herald Yellow (MON_027_Y). -/
def MON_027_Y : CardDef := hitToSoul MON_027_Y_meta
/-- Wartune Herald Blue (MON_028_B). -/
def MON_028_B : CardDef := hitToSoul MON_028_B_meta

/-! ## Light Warrior (MON029–MON059) -/

/-- Shared Boltyn hero abilities. -/
def boltynHeroAbilities : List Ability :=
  [ .static_ (some .chargedThisTurn) (.obj .currentAttack) (.addPower (.const 1))
  , .activated .attackReaction false {} [{ cost := .banishFromSoul 1 }] none false
      { targets := [targetAttackAction]
        body := .grant (.obj (.slot 0)) (.grantKeyword .goAgain) .thisChainLink } ]

/-- Ser Boltyn, Breaker of Dawn (MON_029). -/
def MON_029 : CardDef := draftedCard MON_029_meta boltynHeroAbilities

/-- Boltyn (Young, MON_030). -/
def MON_030 : CardDef := draftedCard MON_030_meta boltynHeroAbilities

/-- Raydn, Duskbane (MON_031). -/
def MON_031 : CardDef :=
  draftedCard MON_031_meta
    [ weaponAttackAbility 0
    , .static_ (some .chargedThisTurn) .self_ (.addPower (.const 3)) ]

/-- Bolting Blade Yellow (MON_032_Y). -/
def MON_032_Y : CardDef :=
  draftedCard MON_032_Y_meta
    [ .static_ (some .chargedThisTurn) .self_ (.modifyCost (-2)) ]

/-- Beacon of Victory Yellow (MON_033_Y). -/
def MON_033_Y : CardDef :=
  draftedCard MON_033_Y_meta []
    (some
      { targets := [targetAttackAction]
        extraCosts := [{ cost := .banishXFromSoul }]
        body := .seqL
          [ .grant (.obj (.slot 0)) (.addPower .xValue) .thisChainLink
          , .ifThen .chargedThisTurn
              (.prim (.searchDeck .controller actionCardFilter (some 1) .hand true none))
              .nop ] })

/-- Lumina Ascension Yellow (MON_034_Y). -/
def MON_034_Y : CardDef :=
  draftedCard MON_034_Y_meta []
    (some
      { body := .seqL
          [ .grant (.allMatching .controller weaponFilter) (.addPower (.const 1)) .thisTurn
          , .grant (.allMatching .controller weaponFilter)
              (.grantTrigger .onHit none
                (.seqL
                  [ .prim (.charge .controller)
                  , .prim (.gainLife .controller (.const 1)) ]))
              .thisTurn
          , .ifThen .chargedThisTurn
              (.grant (.allMatching .controller weaponFilter) .additionalWeaponAttack .thisTurn)
              .nop ] })

/-- V of the Vanguard Yellow (MON_035_Y). -/
def MON_035_Y : CardDef :=
  draftedCard MON_035_Y_meta []
    (some
      { extraCosts := [{ cost := .chargeSoul 1, optional := true }]
        body := .ifThen .chargedThisTurn
          (.grant (.allMatching .controller CardFilter.any) (.addPower (.soulCount .controller)) .thisCombatChain)
          .nop })

/-- Shared helper for Battlefield Blitz. -/
def battlefieldBlitz (base : CardDef) : CardDef :=
  draftedCard base
    [ .static_ (some .chargedThisTurn) .self_ (.grantKeyword .goAgain) ]

/-- Battlefield Blitz Red (MON_036_R). -/
def MON_036_R : CardDef := battlefieldBlitz MON_036_R_meta
/-- Battlefield Blitz Yellow (MON_037_Y). -/
def MON_037_Y : CardDef := battlefieldBlitz MON_037_Y_meta
/-- Battlefield Blitz Blue (MON_038_B). -/
def MON_038_B : CardDef := battlefieldBlitz MON_038_B_meta

/-- Shared helper for Valiant Thrust. -/
def valiantThrust (base : CardDef) : CardDef :=
  draftedCard base
    [ .static_ (some .chargedThisTurn) .self_ (.addPower (.const 3)) ]

/-- Valiant Thrust Red (MON_039_R). -/
def MON_039_R : CardDef := valiantThrust MON_039_R_meta
/-- Valiant Thrust Yellow (MON_040_Y). -/
def MON_040_Y : CardDef := valiantThrust MON_040_Y_meta
/-- Valiant Thrust Blue (MON_041_B). -/
def MON_041_B : CardDef := valiantThrust MON_041_B_meta

/-- Shared helper for Bolt of Courage. -/
def boltOfCourage (base : CardDef) : CardDef :=
  draftedCard base
    [ .triggered .onHit false none (some .chargedThisTurn)
        { body := .prim (.draw .controller (.const 1)) } ]
    (some { extraCosts := [{ cost := .chargeSoul 1, optional := true }] })

/-- Bolt of Courage Red (MON_042_R). -/
def MON_042_R : CardDef := boltOfCourage MON_042_R_meta
/-- Bolt of Courage Yellow (MON_043_Y). -/
def MON_043_Y : CardDef := boltOfCourage MON_043_Y_meta
/-- Bolt of Courage Blue (MON_044_B). -/
def MON_044_B : CardDef := boltOfCourage MON_044_B_meta

/-- Shared helper for optional-charge attacks (Cross the Line, Express Lightning). -/
def optionalChargeAttack (base : CardDef) : CardDef :=
  draftedCard base []
    (some { extraCosts := [{ cost := .chargeSoul 1, optional := true }] })

/-- Cross the Line Red (MON_045_R). -/
def MON_045_R : CardDef := optionalChargeAttack MON_045_R_meta
/-- Cross the Line Yellow (MON_046_Y). -/
def MON_046_Y : CardDef := optionalChargeAttack MON_046_Y_meta
/-- Cross the Line Blue (MON_047_B). -/
def MON_047_B : CardDef := optionalChargeAttack MON_047_B_meta

/-- Shared helper for Engulfing Light. -/
def engulfingLight (base : CardDef) : CardDef :=
  draftedCard base
    [ .triggered .onHit false none (some .chargedThisTurn)
        { body := .prim (.moveCard .self_ .soul .bottom false) } ]
    (some { extraCosts := [{ cost := .chargeSoul 1, optional := true }] })

/-- Engulfing Light Red (MON_048_R). -/
def MON_048_R : CardDef := engulfingLight MON_048_R_meta
/-- Engulfing Light Yellow (MON_049_Y). -/
def MON_049_Y : CardDef := engulfingLight MON_049_Y_meta
/-- Engulfing Light Blue (MON_050_B). -/
def MON_050_B : CardDef := engulfingLight MON_050_B_meta

/-- Express Lightning Red (MON_051_R). -/
def MON_051_R : CardDef := optionalChargeAttack MON_051_R_meta
/-- Express Lightning Yellow (MON_052_Y). -/
def MON_052_Y : CardDef := optionalChargeAttack MON_052_Y_meta
/-- Express Lightning Blue (MON_053_B). -/
def MON_053_B : CardDef := optionalChargeAttack MON_053_B_meta

/-- Shared helper for Take Flight. -/
def takeFlight (base : CardDef) : CardDef :=
  draftedCard base
    [ .static_ (some .chargedThisTurn) .self_ (.grantKeyword .goAgain) ]
    (some { extraCosts := [{ cost := .chargeSoul 1, optional := true }] })

/-- Take Flight Red (MON_054_R). -/
def MON_054_R : CardDef := takeFlight MON_054_R_meta
/-- Take Flight Yellow (MON_055_Y). -/
def MON_055_Y : CardDef := takeFlight MON_055_Y_meta
/-- Take Flight Blue (MON_056_B). -/
def MON_056_B : CardDef := takeFlight MON_056_B_meta

/-- Shared helper for Courageous Steelhand. -/
def courageousSteelhand (base : CardDef) (bonus : Int) : CardDef :=
  draftedCard base []
    (some
      { targets := [targetAttackAction]
        body := .ifThen .chargedThisTurn
          (.grant (.obj (.slot 0)) (.addPower (.const bonus)) .thisChainLink)
          .nop })

/-- Courageous Steelhand Red (MON_057_R). -/
def MON_057_R : CardDef := courageousSteelhand MON_057_R_meta 3
/-- Courageous Steelhand Yellow (MON_058_Y). -/
def MON_058_Y : CardDef := courageousSteelhand MON_058_Y_meta 2
/-- Courageous Steelhand Blue (MON_059_B). -/
def MON_059_B : CardDef := courageousSteelhand MON_059_B_meta 1

/-! ## Light (MON060–MON087) -/

/-- Vestige of Sol (MON_060). -/
def MON_060 : CardDef :=
  draftedCard MON_060_meta
    [ .triggered .onPitch false none (some .chargedThisTurn)
        { body := .prim (.gainResource .controller (.const 1)) } ]

/-- Halo of Illumination (MON_061). -/
def MON_061 : CardDef :=
  draftedCard MON_061_meta
    [ .activated .instant false { resources := 1 } [{ cost := .destroySelf }] none false
        { body := .seqL
            [ .prim (.charge .controller)
            , .prim (.draw .controller (.const 1)) ] } ]

/-- Celestial Cataclysm Yellow (MON_062_Y). -/
def MON_062_Y : CardDef :=
  draftedCard MON_062_Y_meta []
    (some { extraCosts := [{ cost := .banishFromSoul 3 }] })

/-- Soul Shield Yellow (MON_063_Y). -/
def MON_063_Y : CardDef :=
  draftedCard MON_063_Y_meta
    [ .triggered .onChainClose false none none
        { body := .prim (.moveCard .self_ .soul .bottom false) } ]

/-- Soul Food Yellow (MON_064_Y). -/
def MON_064_Y : CardDef :=
  draftedCard MON_064_Y_meta []
    (some
      { body := .seqL
          [ .prim (.moveCard .self_ .soul .bottom false)
          , .prim (.charge .controller) ] })

/-- Tome of Divinity Yellow (MON_065_Y). -/
def MON_065_Y : CardDef :=
  draftedCard MON_065_Y_meta []
    (some
      { body := .ifThen .chargedThisTurn
          (.prim (.draw .controller (.const 3)))
          (.prim (.draw .controller (.const 2))) })

/-- Shared helper for Invigorating Light. -/
def invigoratingLight (base : CardDef) : CardDef :=
  draftedCard base
    [ .triggered .onPlay false none (some (.zoneEmpty .controller .soul))
        { body := .grant .self_
            (.grantTrigger .onChainClose none (.prim (.moveCard .self_ .soul .bottom false)))
            .thisCombatChain } ]

/-- Invigorating Light Red (MON_066_R). -/
def MON_066_R : CardDef := invigoratingLight MON_066_R_meta
/-- Invigorating Light Yellow (MON_067_Y). -/
def MON_067_Y : CardDef := invigoratingLight MON_067_Y_meta
/-- Invigorating Light Blue (MON_068_B). -/
def MON_068_B : CardDef := invigoratingLight MON_068_B_meta

/-- Shared helper for Glisten. -/
def glisten (base : CardDef) (cnt : Int) : CardDef :=
  draftedCard base []
    (some
      { targets := [{ kind := .weapon .controller, minCount := 0, maxCount := some 1 }]
        body := .seqL
          [ .prim (.addCounter (.slot 0) .plusOnePower (.const cnt))
          , .grant (.obj (.slot 0))
              (.grantTrigger .onStartOfEndPhase none (.prim (.removeAllCounters .self_ .plusOnePower)))
              .thisTurn ] })

/-- Glisten Red (MON_069_R). -/
def MON_069_R : CardDef := glisten MON_069_R_meta 4
/-- Glisten Yellow (MON_070_Y). -/
def MON_070_Y : CardDef := glisten MON_070_Y_meta 3
/-- Glisten Blue (MON_071_B). -/
def MON_071_B : CardDef := glisten MON_071_B_meta 2

/-- Illuminate Red (MON_072_R). -/
def MON_072_R : CardDef := hitToSoul MON_072_R_meta
/-- Illuminate Yellow (MON_073_Y). -/
def MON_073_Y : CardDef := hitToSoul MON_073_Y_meta
/-- Illuminate Blue (MON_074_B). -/
def MON_074_B : CardDef := hitToSoul MON_074_B_meta

/-- Shared helper for Impenetrable Belief. -/
def impenetrableBelief (base : CardDef) : CardDef :=
  draftedCard base
    [ .static_ (some (.zoneCountGe .opposingHero .banished CardFilter.any 3))
        .self_ (.addDefense (.const 2)) ]

/-- Impenetrable Belief Red (MON_075_R). -/
def MON_075_R : CardDef := impenetrableBelief MON_075_R_meta
/-- Impenetrable Belief Yellow (MON_076_Y). -/
def MON_076_Y : CardDef := impenetrableBelief MON_076_Y_meta
/-- Impenetrable Belief Blue (MON_077_B). -/
def MON_077_B : CardDef := impenetrableBelief MON_077_B_meta

/-- Rising Solartide Red (MON_078_R). -/
def MON_078_R : CardDef := hitToSoul MON_078_R_meta
/-- Rising Solartide Yellow (MON_079_Y). -/
def MON_079_Y : CardDef := hitToSoul MON_079_Y_meta
/-- Rising Solartide Blue (MON_080_B). -/
def MON_080_B : CardDef := hitToSoul MON_080_B_meta

/-- Shared helper for Seek Enlightenment. -/
def seekEnlightenment (base : CardDef) (bonus : Int) : CardDef :=
  draftedCard base []
    (some
      { body := .seqL
          [ .grant (.nextCardPlayed CardFilter.attackAction) (.addPower (.const bonus)) .thisTurn
          , .grant (.nextCardPlayed CardFilter.attackAction)
              (.grantTrigger .onHit none (.prim (.moveCard .self_ .soul .bottom false)))
              .thisTurn ] })

/-- Seek Enlightenment Red (MON_081_R). -/
def MON_081_R : CardDef := seekEnlightenment MON_081_R_meta 3
/-- Seek Enlightenment Yellow (MON_082_Y). -/
def MON_082_Y : CardDef := seekEnlightenment MON_082_Y_meta 2
/-- Seek Enlightenment Blue (MON_083_B). -/
def MON_083_B : CardDef := seekEnlightenment MON_083_B_meta 1

/-- Shared helper for Blinding Beam. -/
def blindingBeam (base : CardDef) (debuff : Int) : CardDef :=
  draftedCard base []
    (some
      { targets := [targetAttackAction]
        body := .grant (.obj (.slot 0)) (.addPower (.const debuff)) .thisChainLink })

/-- Blinding Beam Red (MON_084_R). -/
def MON_084_R : CardDef := blindingBeam MON_084_R_meta (-3)
/-- Blinding Beam Yellow (MON_085_Y). -/
def MON_085_Y : CardDef := blindingBeam MON_085_Y_meta (-2)
/-- Blinding Beam Blue (MON_086_B). -/
def MON_086_B : CardDef := blindingBeam MON_086_B_meta (-1)

/-- Ray of Hope Yellow (MON_087_Y). -/
def MON_087_Y : CardDef :=
  draftedCard MON_087_Y_meta []
    (some
      { body := .seqL
          [ .grant (.allMatching .controller CardFilter.attackAction) (.addPower (.const 1)) .thisTurn
          , .ifThen .lessLifeThanOpponent (.prim (.moveCard .self_ .soul .bottom false)) .nop ] })

/-! ## Illusionist (MON088–MON104) -/

/-- Iris of Reality (MON_088). -/
def MON_088 : CardDef :=
  draftedCard MON_088_meta
    [ .static_ none (.allMatching .controller illusionistAuraFilter) (.auraIsWeapon 4 3 true) ]

/-- Phantasmal Footsteps (MON_089). -/
def MON_089 : CardDef :=
  draftedCard MON_089_meta
    [ .triggered .onDestroy true (some 1) none
        { extraCosts := [{ cost := .payResources 1, optional := true }]
          body := .ifThen .additionalCostPaid (.prim (.gainAP .controller (.const 1))) .nop }
    , .triggered .onDefend false none none
        { extraCosts := [{ cost := .payResources 1, optional := true }]
          body := .ifThen .additionalCostPaid (.grant .self_ (.addDefense (.const 1)) .thisTurn) .nop } ]

/-- Dream Weavers (MON_090). -/
def MON_090 : CardDef :=
  draftedCard MON_090_meta
    [ .activated .action false { actionPoints := 1 } [{ cost := .destroySelf }] none true
        { body := .grant (.nextCardPlayed illusionistAttackFilter) (.loseKeyword .phantasm) .thisTurn } ]

/-- Phantasmaclasm Red (MON_091_R). -/
def MON_091_R : CardDef :=
  draftedCard MON_091_R_meta
    [ .triggered .onAttack false none none
        { body := .seqL
            [ .prim (.putHandOnDeck .defendingHero .bottom)
            , .prim (.draw .defendingHero (.const 1)) ] } ]

/-- Shared helper for Prismatic Shield. -/
def prismaticShield (base : CardDef) (cnt : Nat) : CardDef :=
  draftedCard base []
    (some { body := .prim (.createToken .controller ⟨"MON_104"⟩ cnt) })

/-- Prismatic Shield Red (MON_092_R). -/
def MON_092_R : CardDef := verifiedCard (prismaticShield MON_092_R_meta 3)
/-- Prismatic Shield Yellow (MON_093_Y). -/
def MON_093_Y : CardDef := verifiedCard (prismaticShield MON_093_Y_meta 2)
/-- Prismatic Shield Blue (MON_094_B). -/
def MON_094_B : CardDef := verifiedCard (prismaticShield MON_094_B_meta 1)

/-- Shared helper for Phantasmify. -/
def phantasmify (base : CardDef) (bonus : Int) : CardDef :=
  draftedCard base []
    (some
      { body := .seqL
          [ .grant (.nextCardPlayed CardFilter.attackAction) (.addPower (.const bonus)) .thisTurn
          , .grant (.nextCardPlayed CardFilter.attackAction) (.grantKeyword .phantasm) .thisTurn ] })

/-- Phantasmify Red (MON_095_R). -/
def MON_095_R : CardDef := phantasmify MON_095_R_meta 5
/-- Phantasmify Yellow (MON_096_Y). -/
def MON_096_Y : CardDef := phantasmify MON_096_Y_meta 4
/-- Phantasmify Blue (MON_097_B). -/
def MON_097_B : CardDef := phantasmify MON_097_B_meta 3

/-- Enigma Chimera Red (MON_098_R). -/
def MON_098_R : CardDef := verifiedCard MON_098_R_meta
/-- Enigma Chimera Yellow (MON_099_Y). -/
def MON_099_Y : CardDef := verifiedCard MON_099_Y_meta
/-- Enigma Chimera Blue (MON_100_B). -/
def MON_100_B : CardDef := verifiedCard MON_100_B_meta

/-- Spears of Surreality Red (MON_101_R). -/
def MON_101_R : CardDef := verifiedCard MON_101_R_meta
/-- Spears of Surreality Yellow (MON_102_Y). -/
def MON_102_Y : CardDef := verifiedCard MON_102_Y_meta
/-- Spears of Surreality Blue (MON_103_B). -/
def MON_103_B : CardDef := verifiedCard MON_103_B_meta

/-- Spectral Shield Token (MON_104, Ward 1). -/
def MON_104 : CardDef := draftedCard MON_104_meta

/-! ## Warrior (MON105–MON118) -/

/-- Hatchet of Body (MON_105). -/
def MON_105 : CardDef :=
  draftedCard MON_105_meta
    [ weaponAttackAbility 1
    , .triggered .onAttack false none (some (.prevChainLinkNamed "Hatchet of Mind"))
        { body := .grant .self_ (.addPower (.const 1)) .thisTurn } ]

/-- Hatchet of Mind (MON_106). -/
def MON_106 : CardDef :=
  draftedCard MON_106_meta
    [ weaponAttackAbility 1
    , .triggered .onAttack false none (some (.prevChainLinkNamed "Hatchet of Body"))
        { body := .grant .self_ (.addPower (.const 1)) .thisTurn } ]

/-- Valiant Dynamo (MON_107). -/
def MON_107 : CardDef :=
  draftedCard MON_107_meta
    [ .triggered .onStartOfEndPhase false none (some .weaponHitThisTurn)
        { body := .may (.prim (.removeAllCounters .self_ .minusOneDefense)) .nop } ]

/-- Gallantry Gold (MON_108). -/
def MON_108 : CardDef :=
  draftedCard MON_108_meta
    [ .activated .action false { actionPoints := 1, resources := 1 } [{ cost := .destroySelf }] none true
        { body := .grant (.allMatching .controller CardFilter.weaponAttack) (.addPower (.const 1)) .thisTurn } ]

/-- Spill Blood Red (MON_109_R). -/
def MON_109_R : CardDef :=
  draftedCard MON_109_R_meta []
    (some
      { body := .seqL
          [ .grant (.allMatching .controller axeFilter) (.addPower (.const 2)) .thisTurn
          , .grant (.allMatching .controller axeFilter) (.grantKeyword .dominate) .thisTurn ] })

/-- Shared helper for Dusk Path Pilgrimage. -/
def duskPathPilgrimage (base : CardDef) (bonus : Int) : CardDef :=
  draftedCard base []
    (some
      { body := .seqL
          [ .grant (.nextAttack CardFilter.weaponAttack) (.addPower (.const bonus)) .thisTurn
          , .grant (.nextAttack CardFilter.weaponAttack)
              (.grantTrigger .onHit none (.grant .self_ .additionalWeaponAttack .thisTurn))
              .thisTurn ] })

/-- Dusk Path Pilgrimage Red (MON_110_R). -/
def MON_110_R : CardDef := duskPathPilgrimage MON_110_R_meta 3
/-- Dusk Path Pilgrimage Yellow (MON_111_Y). -/
def MON_111_Y : CardDef := duskPathPilgrimage MON_111_Y_meta 2
/-- Dusk Path Pilgrimage Blue (MON_112_B). -/
def MON_112_B : CardDef := duskPathPilgrimage MON_112_B_meta 1

/-- Shared helper for Plow Through. -/
def plowThrough (base : CardDef) (bonus : Int) : CardDef :=
  draftedCard base []
    (some
      { body := .seqL
          [ .grant (.nextAttack CardFilter.weaponAttack) (.addPower (.const bonus)) .thisTurn
          , .grant (.nextAttack CardFilter.weaponAttack)
              (.grantTrigger .onDefend none (.grant .self_ (.addPower (.const 1)) .thisTurn))
              .thisTurn ] })

/-- Plow Through Red (MON_113_R). -/
def MON_113_R : CardDef := plowThrough MON_113_R_meta 3
/-- Plow Through Yellow (MON_114_Y). -/
def MON_114_Y : CardDef := plowThrough MON_114_Y_meta 2
/-- Plow Through Blue (MON_115_B). -/
def MON_115_B : CardDef := plowThrough MON_115_B_meta 1

/-- Shared helper for Second Swing. -/
def secondSwing (base : CardDef) (bonus : Int) : CardDef :=
  draftedCard base []
    (some
      { body := .ifThen .weaponHitThisTurn
          (.grant (.nextAttack CardFilter.any) (.addPower (.const bonus)) .thisTurn)
          .nop })

/-- Second Swing Red (MON_116_R). -/
def MON_116_R : CardDef := secondSwing MON_116_R_meta 4
/-- Second Swing Yellow (MON_117_Y). -/
def MON_117_Y : CardDef := secondSwing MON_117_Y_meta 3
/-- Second Swing Blue (MON_118_B). -/
def MON_118_B : CardDef := secondSwing MON_118_B_meta 2

/-! ## Shadow Brute (MON119–MON152) -/

/-- Shared Levia hero ability: if 6{p} banished this turn, cards you own lose blood debt during End Phase. -/
def leviaHeroAbilities : List Ability :=
  [ .static_ (some .banishedSixPowerThisTurn)
      (.allMatching .controller bloodDebtFilter) (.loseKeyword .bloodDebt) ]

/-- Levia, Shadowborn Abomination (MON_119). -/
def MON_119 : CardDef := draftedCard MON_119_meta leviaHeroAbilities

/-- Levia (Young, MON_120). -/
def MON_120 : CardDef := draftedCard MON_120_meta leviaHeroAbilities

/-- Hexagore, the Death Hydra (MON_121). -/
def MON_121 : CardDef :=
  draftedCard MON_121_meta
    [ weaponAttackAbility 2
    , .triggered .onAttack false none none
        { body := .ifThen (.zoneCountGe .controller .banished bloodDebtFilter 6)
            .nop
            (.prim (.dealDamage .physical .controller (.const 6))) } ]

/-- Hooves of the Shadowbeast (MON_122). -/
def MON_122 : CardDef :=
  draftedCard MON_122_meta
    [ .triggered .onBanish false none (some .banishedSixPowerThisTurn)
        { body := .may (.prim (.destroy .self_)) (.prim (.gainAP .controller (.const 1))) } ]

/-- Deep Rooted Evil Yellow (MON_123_Y). -/
def MON_123_Y : CardDef :=
  -- Some banish paths still omit turn-history updates.
  { draftedCard MON_123_Y_meta
      (playFromBanished := some .banishedSixPowerThisTurn) with status := .«partial» }

/-- Mark of the Beast Yellow (MON_124_Y). -/
def MON_124_Y : CardDef :=
  draftedCard MON_124_Y_meta
    [ .replacement .standard (.selfWouldGoToGraveyard .any)
        { body := .prim (.banish .self_ false) } ]

/-- Shadow of Blasmophet Red (MON_125_R). -/
def MON_125_R : CardDef :=
  draftedCard MON_125_R_meta
    [ .triggered .onAttack false none none
        { body := .seqL
            [ .prim (.draw .controller (.const 1))
            , .prim (.discardRandom .controller (.const 1))
            , .ifThen (.lastDiscardedMatches power6Filter)
                (.prim (.searchDeck .controller bloodDebtFilter (some 1) .banished false none))
                .nop ] } ]

/-- Shared helper for Endless Maw. -/
def endlessMaw (base : CardDef) : CardDef :=
  draftedCard base []
    (some
      { extraCosts := [{ cost := .banishRandomFromGraveyard 3 }]
        body := .ifThen .banishedSixPowerThisTurn
          (.grant .self_ (.addPower (.const 3)) .thisChainLink)
          .nop })

/-- Endless Maw Red (MON_126_R). -/
def MON_126_R : CardDef := endlessMaw MON_126_R_meta
/-- Endless Maw Yellow (MON_127_Y). -/
def MON_127_Y : CardDef := endlessMaw MON_127_Y_meta
/-- Endless Maw Blue (MON_128_B). -/
def MON_128_B : CardDef := endlessMaw MON_128_B_meta

/-- Shared helper for Writhing Beast Hulk. -/
def writhingBeastHulk (base : CardDef) : CardDef :=
  draftedCard base []
    (some
      { extraCosts := [{ cost := .banishRandomFromGraveyard 3 }]
        body := .ifThen .banishedSixPowerThisTurn
          (.grant .self_ (.grantKeyword .dominate) .thisChainLink)
          .nop })

/-- Writhing Beast Hulk Red (MON_129_R). -/
def MON_129_R : CardDef := writhingBeastHulk MON_129_R_meta
/-- Writhing Beast Hulk Yellow (MON_130_Y). -/
def MON_130_Y : CardDef := writhingBeastHulk MON_130_Y_meta
/-- Writhing Beast Hulk Blue (MON_131_B). -/
def MON_131_B : CardDef := writhingBeastHulk MON_131_B_meta

/-- Shared helper for Convulsions from the Bellows of Hell. -/
def convulsions (base : CardDef) (bonus : Int) : CardDef :=
  draftedCard base []
    (some
      { extraCosts := [{ cost := .banishRandomFromGraveyard 3 }]
        body := .ifThen .banishedSixPowerThisTurn
          (.seqL
            [ .grant (.nextCardPlayed CardFilter.attackAction) (.addPower (.const bonus)) .thisTurn
            , .grant (.nextCardPlayed CardFilter.attackAction) (.grantKeyword .dominate) .thisTurn ])
          .nop })

/-- Convulsions from the Bellows of Hell Red (MON_132_R). -/
def MON_132_R : CardDef := convulsions MON_132_R_meta 3
/-- Convulsions from the Bellows of Hell Yellow (MON_133_Y). -/
def MON_133_Y : CardDef := convulsions MON_133_Y_meta 2
/-- Convulsions from the Bellows of Hell Blue (MON_134_B). -/
def MON_134_B : CardDef := convulsions MON_134_B_meta 1

/-- Shared helper for Boneyard Marauder & Hungering Slaughterbeast. -/
def banish3GyAttack (base : CardDef) : CardDef :=
  draftedCard base []
    (some { extraCosts := [{ cost := .banishRandomFromGraveyard 3 }] })

/-- Boneyard Marauder Red (MON_135_R). -/
def MON_135_R : CardDef := banish3GyAttack MON_135_R_meta
/-- Boneyard Marauder Yellow (MON_136_Y). -/
def MON_136_Y : CardDef := banish3GyAttack MON_136_Y_meta
/-- Boneyard Marauder Blue (MON_137_B). -/
def MON_137_B : CardDef := banish3GyAttack MON_137_B_meta

/-- Shared helper for Deadwood Rumbler. -/
def deadwoodRumbler (base : CardDef) : CardDef :=
  draftedCard base
    [ .triggered .onAttack false none none
        { body := .seqL
            [ .prim (.draw .controller (.const 1))
            , .prim (.discardRandom .controller (.const 1))
            , .ifThen (.lastDiscardedMatches power6Filter)
                (.prim (.banishFromGraveyard .controller CardFilter.any 1))
                .nop ] } ]

/-- Deadwood Rumbler Red (MON_138_R). -/
def MON_138_R : CardDef := deadwoodRumbler MON_138_R_meta
/-- Deadwood Rumbler Yellow (MON_139_Y). -/
def MON_139_Y : CardDef := deadwoodRumbler MON_139_Y_meta
/-- Deadwood Rumbler Blue (MON_140_B). -/
def MON_140_B : CardDef := deadwoodRumbler MON_140_B_meta

/-- Shared helper for Dread Screamer. -/
def dreadScreamer (base : CardDef) : CardDef :=
  draftedCard base []
    (some
      { extraCosts := [{ cost := .banishRandomFromGraveyard 3 }]
        body := .ifThen .banishedSixPowerThisTurn
          (.grant .self_ (.grantKeyword .goAgain) .thisChainLink)
          .nop })

/-- Dread Screamer Red (MON_141_R). -/
def MON_141_R : CardDef := dreadScreamer MON_141_R_meta
/-- Dread Screamer Yellow (MON_142_Y). -/
def MON_142_Y : CardDef := dreadScreamer MON_142_Y_meta
/-- Dread Screamer Blue (MON_143_B). -/
def MON_143_B : CardDef := dreadScreamer MON_143_B_meta

/-- Shared helper for Graveling Growl. -/
def gravelingGrowl (base : CardDef) : CardDef :=
  draftedCard base
    [ .triggered .onPlay false none (some .banishedSixPowerThisTurn) { body := .nop } ]

/-- Graveling Growl Red (MON_144_R). -/
def MON_144_R : CardDef := gravelingGrowl MON_144_R_meta
/-- Graveling Growl Yellow (MON_145_Y). -/
def MON_145_Y : CardDef := gravelingGrowl MON_145_Y_meta
/-- Graveling Growl Blue (MON_146_B). -/
def MON_146_B : CardDef := gravelingGrowl MON_146_B_meta

/-- Hungering Slaughterbeast Red (MON_147_R). -/
def MON_147_R : CardDef := banish3GyAttack MON_147_R_meta
/-- Hungering Slaughterbeast Yellow (MON_148_Y). -/
def MON_148_Y : CardDef := banish3GyAttack MON_148_Y_meta
/-- Hungering Slaughterbeast Blue (MON_149_B). -/
def MON_149_B : CardDef := banish3GyAttack MON_149_B_meta

/-- Shared helper for Unworldly Bellow. -/
def unworldlyBellow (base : CardDef) (bonus : Int) : CardDef :=
  draftedCard base []
    (some
      { extraCosts := [{ cost := .banishRandomFromGraveyard 3 }]
        body := .grant (.nextCardPlayed bruteAttackFilter) (.addPower (.const bonus)) .thisTurn })

/-- Unworldly Bellow Red (MON_150_R). -/
def MON_150_R : CardDef := unworldlyBellow MON_150_R_meta 4
/-- Unworldly Bellow Yellow (MON_151_Y). -/
def MON_151_Y : CardDef := unworldlyBellow MON_151_Y_meta 3
/-- Unworldly Bellow Blue (MON_152_B). -/
def MON_152_B : CardDef := unworldlyBellow MON_152_B_meta 2

/-! ## Shadow Runeblade (MON153–MON186) -/

/-- Shared Chane hero ability: Once per Turn Action - Create a Soul Shackle token: next Shadow/Runeblade action gets go again. -/
def chaneHeroAbilities : List Ability :=
  [ .activated .action true { actionPoints := 1 } [{ cost := .createTokenCost ⟨"MON_186"⟩ 1 }] none true
      { body := .grant (.nextCardPlayed shadowActionFilter) (.grantKeyword .goAgain) .thisTurn } ]

/-- Chane, Bound by Shadow (MON_153). -/
def MON_153 : CardDef := draftedCard MON_153_meta chaneHeroAbilities

/-- Chane (Young, MON_154). -/
def MON_154 : CardDef := draftedCard MON_154_meta chaneHeroAbilities

/-- Galaxxi Black (MON_155). -/
def MON_155 : CardDef :=
  draftedCard MON_155_meta
    [ weaponAttackAbility 1
    , .static_ (some .playedFromBanished) .self_ (.addPower (.const 2))
    , .triggered .onHitHero false none none
        { body := .prim (.dealDamage .arcane .defendingHero (.const 1)) } ]

/-- Shadow of Ursur Blue (MON_156_B). -/
def MON_156_B : CardDef :=
  draftedCard MON_156_B_meta
    (playFromBanished := some .always)
    (playEffect := some
      { extraCosts := [{ cost := .banishFromHand bloodDebtFilter 1, optional := true }]
        body := .ifThen .additionalCostPaid
          (.grant .self_ (.grantKeyword .goAgain) .thisChainLink)
          .nop })

/-- Dimenxxional Crossroads Yellow (MON_157_Y). -/
def MON_157_Y : CardDef :=
  draftedCard MON_157_Y_meta
    [ .triggered .onPlayAttackOrWeapon false none (some .playedFromBanished)
        { targets := [targetHero]
          body := .prim (.dealDamage .arcane (.ownerOfSlot 0) (.const 1)) } ]

/-- Invert Existence Blue (MON_158_B). -/
def MON_158_B : CardDef :=
  draftedCard MON_158_B_meta
    (playFromBanished := some .always)
    (playEffect := some
      { body := .seqL
          [ .prim (.banishFromGraveyard .opposingHero CardFilter.any 2)
          , .prim (.dealDamage .arcane .opposingHero (.const 2)) ] })

/-- Shared helper for Unhallowed Rites. -/
def unhallowedRites (base : CardDef) : CardDef :=
  draftedCard base
    (playFromBanished := some .playedNonAttackActionThisTurn)
    (playEffect := some
      { targets := [{ kind := .cardInZone .controller .graveyard, filter := bloodDebtActionFilter, minCount := 0, maxCount := some 1 }]
        body := .may (.prim (.moveCard (.slot 0) .deck .bottom false)) .nop })

/-- Unhallowed Rites Red (MON_159_R). -/
def MON_159_R : CardDef := unhallowedRites MON_159_R_meta
/-- Unhallowed Rites Yellow (MON_160_Y). -/
def MON_160_Y : CardDef := unhallowedRites MON_160_Y_meta
/-- Unhallowed Rites Blue (MON_161_B). -/
def MON_161_B : CardDef := unhallowedRites MON_161_B_meta

/-- Shared helper for Dimenxxional Gateway. -/
def dimenxxionalGateway (base : CardDef) (optN : Nat) : CardDef :=
  draftedCard base []
    (some
      { body := .seqL
          [ .prim (.opt .controller optN)
          , .bindRevealTopCount .controller 1 runebladeFilter ⟨0⟩
              (.prim (.dealDamage .arcane .opposingHero (.varVal ⟨0⟩)))
          , .may (.prim (.banishTopDeck .controller 1 false)) .nop ] })

/-- Dimenxxional Gateway Red (MON_162_R). -/
def MON_162_R : CardDef := dimenxxionalGateway MON_162_R_meta 3
/-- Dimenxxional Gateway Yellow (MON_163_Y). -/
def MON_163_Y : CardDef := dimenxxionalGateway MON_163_Y_meta 2
/-- Dimenxxional Gateway Blue (MON_164_B). -/
def MON_164_B : CardDef := dimenxxionalGateway MON_164_B_meta 1

/-- Shared helper for Seeping Shadows. -/
def seepingShadows (base : CardDef) (maxC : Nat) : CardDef :=
  draftedCard base
    (playFromBanished := some .always)
    (playEffect := some
      { body := .seqL
          [ .grant (.nextCardPlayed (attackCostLeFilter maxC)) (.addPower (.const 1)) .thisTurn
          , .grant (.nextCardPlayed (attackCostLeFilter maxC)) (.grantKeyword .goAgain) .thisTurn ] })

/-- Seeping Shadows Red (MON_165_R). -/
def MON_165_R : CardDef := seepingShadows MON_165_R_meta 2
/-- Seeping Shadows Yellow (MON_166_Y). -/
def MON_166_Y : CardDef := seepingShadows MON_166_Y_meta 1
/-- Seeping Shadows Blue (MON_167_B). -/
def MON_167_B : CardDef := seepingShadows MON_167_B_meta 0

/-- Shared helper for Bounding Demigon. -/
def boundingDemigon (base : CardDef) : CardDef :=
  draftedCard base (playFromBanished := some .playedNonAttackActionThisTurn)
    [ .triggered .onPlay false none (some .playedFromBanished)
        { body := .grant .self_ (.addPower (.const 1)) .thisChainLink } ]

/-- Bounding Demigon Red (MON_168_R). -/
def MON_168_R : CardDef := boundingDemigon MON_168_R_meta
/-- Bounding Demigon Yellow (MON_169_Y). -/
def MON_169_Y : CardDef := boundingDemigon MON_169_Y_meta
/-- Bounding Demigon Blue (MON_170_B). -/
def MON_170_B : CardDef := boundingDemigon MON_170_B_meta

/-- Shared helper for Piercing Shadow Vise. -/
def piercingShadowVise (base : CardDef) : CardDef :=
  draftedCard base (playFromBanished := some .always)
    [ .static_ (some .playedFromBanished) .self_ (.addPower (.const 2)) ]

/-- Piercing Shadow Vise Red (MON_171_R). -/
def MON_171_R : CardDef := piercingShadowVise MON_171_R_meta
/-- Piercing Shadow Vise Yellow (MON_172_Y). -/
def MON_172_Y : CardDef := piercingShadowVise MON_172_Y_meta
/-- Piercing Shadow Vise Blue (MON_173_B). -/
def MON_173_B : CardDef := piercingShadowVise MON_173_B_meta

/-- Shared helper for Rift Bind. -/
def riftBind (base : CardDef) : CardDef :=
  draftedCard base (playFromBanished := some .always)
    [ .triggered .onPlay false none (some .playedFromBanished)
        { body := .grant .self_ (.addPower (.const 1)) .thisChainLink } ]

/-- Rift Bind Red (MON_174_R). -/
def MON_174_R : CardDef := riftBind MON_174_R_meta
/-- Rift Bind Yellow (MON_175_Y). -/
def MON_175_Y : CardDef := riftBind MON_175_Y_meta
/-- Rift Bind Blue (MON_176_B). -/
def MON_176_B : CardDef := riftBind MON_176_B_meta

/-- Shared helper for Rifted Torment. -/
def riftedTorment (base : CardDef) : CardDef :=
  draftedCard base (playFromBanished := some .always)
    [ .triggered .onPlay false none (some .playedFromBanished)
        { targets := [targetHero]
          body := .prim (.dealDamage .arcane (.ownerOfSlot 0) (.const 1)) } ]

/-- Rifted Torment Red (MON_177_R). -/
def MON_177_R : CardDef := riftedTorment MON_177_R_meta
/-- Rifted Torment Yellow (MON_178_Y). -/
def MON_178_Y : CardDef := riftedTorment MON_178_Y_meta
/-- Rifted Torment Blue (MON_179_B). -/
def MON_179_B : CardDef := riftedTorment MON_179_B_meta

/-- Shared helper for Rip Through Reality. -/
def ripThroughReality (base : CardDef) : CardDef :=
  draftedCard base (playFromBanished := some .always)
    [ .static_ (some .playedFromBanished) .self_ (.grantKeyword .goAgain) ]

/-- Rip Through Reality Red (MON_180_R). -/
def MON_180_R : CardDef := ripThroughReality MON_180_R_meta
/-- Rip Through Reality Yellow (MON_181_Y). -/
def MON_181_Y : CardDef := ripThroughReality MON_181_Y_meta
/-- Rip Through Reality Blue (MON_182_B). -/
def MON_182_B : CardDef := ripThroughReality MON_182_B_meta

/-- Shared helper for Seeds of Agony. -/
def seedsOfAgony (base : CardDef) (maxC : Nat) : CardDef :=
  draftedCard base
    (playFromBanished := some .always)
    (playEffect := some
      { body := .grant (.nextCardPlayed (attackCostLeFilter maxC))
          (.grantTrigger .onAttack none (.prim (.dealDamage .arcane .defendingHero (.const 1))))
          .thisTurn })

/-- Seeds of Agony Red (MON_183_R). -/
def MON_183_R : CardDef := seedsOfAgony MON_183_R_meta 2
/-- Seeds of Agony Yellow (MON_184_Y). -/
def MON_184_Y : CardDef := seedsOfAgony MON_184_Y_meta 1
/-- Seeds of Agony Blue (MON_185_B). -/
def MON_185_B : CardDef := seedsOfAgony MON_185_B_meta 0

/-- Soul Shackle Token (MON_186). -/
def MON_186 : CardDef :=
  { draftedCard MON_186_meta
      [ .triggered .onStartOfActionPhase false none none
          { body := .prim (.banishTopDeck .controller 1 false) } ] with status := .full }

/-! ## Shadow (MON187–MON220) -/

/-- Carrion Husk (MON_187). -/
def MON_187 : CardDef :=
  draftedCard MON_187_meta
    [ .triggered .onDefend false none none
        { body := .grant .self_ (.grantTrigger .onChainClose none (.prim (.banish .self_ false))) .thisCombatChain }
    , .triggered .onStartOfTurn false none (some .lessLifeThanOpponent)
        { body := .prim (.banish .self_ false) } ]

/-- Ebon Fold (MON_188). -/
def MON_188 : CardDef :=
  draftedCard MON_188_meta
    [ .activated .instant false { resources := 1 }
        [{ cost := .destroySelf }, { cost := .banishFromHand CardFilter.any 1 }] none false
        { body := .prim (.draw .controller (.const 1)) } ]

/-- Doomsday Blue (MON_189_B). -/
def MON_189_B : CardDef :=
  { draftedCard MON_189_B_meta (playRestriction := .banishedBloodDebtAtLeast 6)
      (playEffect := some { body := .prim (.createToken .controller ⟨"MON_219"⟩ 1) }) with
    status := .full }

/-- Eclipse Blue (MON_190_B). -/
def MON_190_B : CardDef :=
  { draftedCard MON_190_B_meta
      (playRestriction := .playedBloodDebtAtLeast 6)
      (playFromBanished := some .always)
      (playEffect := some { body := .prim (.createToken .controller ⟨"MON_220"⟩ 1) }) with
    status := .full }

/-- Mutated Mass Blue (MON_191_B). -/
def MON_191_B : CardDef :=
  draftedCard MON_191_B_meta (playFromBanished := some .always)
    [ .static_ none .self_ (.addPower (.banishedCount .controller))
    , .static_ none .self_ (.addDefense (.banishedCount .controller)) ]

/-- Guardian of the Shadowrealm Red (MON_192_R). -/
def MON_192_R : CardDef :=
  draftedCard MON_192_R_meta
    [ .activated .action false { actionPoints := 1, resources := 2 } [] none false
        { body := .prim (.moveCard .self_ .hand .top false) } ]

/-- Shadow Puppetry Red (MON_193_R). -/
def MON_193_R : CardDef :=
  draftedCard MON_193_R_meta []
    (some
      { body := .seqL
          [ .grant (.nextCardPlayed CardFilter.attackAction) (.addPower (.const 1)) .thisTurn
          , .grant (.nextCardPlayed CardFilter.attackAction) (.grantKeyword .goAgain) .thisTurn
          , .grant (.nextCardPlayed CardFilter.attackAction)
              (.grantTrigger .onHit none (.may (.prim (.banishTopDeck .controller 1 false)) .nop))
              .thisTurn ] })

/-- Tome of Torment Red (MON_194_R). -/
def MON_194_R : CardDef :=
  { draftedCard MON_194_R_meta
      (playFromBanished := some .always)
      (playEffect := some { body := .prim (.draw .controller (.const 1)) }) with status := .full }

/-- Shared helper for Consuming Aftermath. -/
def consumingAftermath (base : CardDef) : CardDef :=
  draftedCard base []
    (some
      { extraCosts := [{ cost := .banishFromHand shadowFilter 1, optional := true }]
        body := .ifThen .additionalCostPaid
          (.grant .self_ (.grantKeyword .dominate) .thisChainLink)
          .nop })

/-- Consuming Aftermath Red (MON_195_R). -/
def MON_195_R : CardDef := consumingAftermath MON_195_R_meta
/-- Consuming Aftermath Yellow (MON_196_Y). -/
def MON_196_Y : CardDef := consumingAftermath MON_196_Y_meta
/-- Consuming Aftermath Blue (MON_197_B). -/
def MON_197_B : CardDef := consumingAftermath MON_197_B_meta

/-- Soul Harvest Blue (MON_198_B). -/
def MON_198_B : CardDef :=
  draftedCard MON_198_B_meta
    [ .triggered .onHitHero false none none
        { body := .seqL
            [ .prim (.loseLife .defendingHero (.soulCount .defendingHero))
            , .prim (.banishFromSoul .defendingHero 99) ] } ]
    (some
      { extraCosts := [{ cost := .banishFromGraveyard CardFilter.any 6 }]
        body := .grant .self_ (.addPower (.banishedCount .controller)) .thisChainLink })

/-- Soul Reaping Red (MON_199_R). -/
def MON_199_R : CardDef :=
  draftedCard MON_199_R_meta
    [ .static_ (some (.zoneCountGe .defendingHero .soul CardFilter.any 1))
        .self_ (.grantKeyword .goAgain) ]
    (some
      { extraCosts := [{ cost := .banishFromHand CardFilter.any 1, optional := true }]
        body := .ifThen .additionalCostPaid (.prim (.gainResource .controller (.const 1))) .nop })

/-- Shared helper for Howl from Beyond. -/
def howlFromBeyond (base : CardDef) (bonus : Int) : CardDef :=
  draftedCard base
    (playFromBanished := some .always)
    (playEffect := some
      { body := .grant (.nextCardPlayed CardFilter.attackAction) (.addPower (.const bonus)) .thisTurn })

/-- Howl from Beyond Red (MON_200_R). -/
def MON_200_R : CardDef := howlFromBeyond MON_200_R_meta 3
/-- Howl from Beyond Yellow (MON_201_Y). -/
def MON_201_Y : CardDef := howlFromBeyond MON_201_Y_meta 2
/-- Howl from Beyond Blue (MON_202_B). -/
def MON_202_B : CardDef := howlFromBeyond MON_202_B_meta 1

/-- Shared helper for Ghostly Visit & Void Wraith (playable from banished + Blood Debt). -/
def shadowBanishedAttack (base : CardDef) : CardDef :=
  draftedCard base (playFromBanished := some .always)

/-- Ghostly Visit Red (MON_203_R). -/
def MON_203_R : CardDef := verifiedCard (shadowBanishedAttack MON_203_R_meta)
/-- Ghostly Visit Yellow (MON_204_Y). -/
def MON_204_Y : CardDef := verifiedCard (shadowBanishedAttack MON_204_Y_meta)
/-- Ghostly Visit Blue (MON_205_B). -/
def MON_205_B : CardDef := verifiedCard (shadowBanishedAttack MON_205_B_meta)

/-- Shared helper for Lunartide Plunderer. -/
def lunartidePlunderer (base : CardDef) : CardDef :=
  draftedCard base
    [ .triggered .onHitHero false none none
        { body := .seqL
            [ .prim (.banish .self_ false)
            , .may (.prim (.banishFromSoul .defendingHero 1)) .nop ] } ]

/-- Lunartide Plunderer Red (MON_206_R). -/
def MON_206_R : CardDef := lunartidePlunderer MON_206_R_meta
/-- Lunartide Plunderer Yellow (MON_207_Y). -/
def MON_207_Y : CardDef := lunartidePlunderer MON_207_Y_meta
/-- Lunartide Plunderer Blue (MON_208_B). -/
def MON_208_B : CardDef := lunartidePlunderer MON_208_B_meta

/-- Void Wraith Red (MON_209_R). -/
def MON_209_R : CardDef := verifiedCard (shadowBanishedAttack MON_209_R_meta)
/-- Void Wraith Yellow (MON_210_Y). -/
def MON_210_Y : CardDef := verifiedCard (shadowBanishedAttack MON_210_Y_meta)
/-- Void Wraith Blue (MON_211_B). -/
def MON_211_B : CardDef := verifiedCard (shadowBanishedAttack MON_211_B_meta)

/-- Shared helper for Spew Shadow. -/
def spewShadow (base : CardDef) (maxC : Nat) : CardDef :=
  draftedCard base []
    (some
      { targets := [{ kind := .cardInZone .controller .banished, filter := attackCostLeFilter maxC, minCount := 1, maxCount := some 1 }]
        body := .seqL
          [ .grant (.obj (.slot 0)) .playableFromBanished .thisTurn
          , .grant (.obj (.slot 0)) (.addPower (.const 2)) .thisTurn ] })

/-- Spew Shadow Red (MON_212_R). -/
def MON_212_R : CardDef := spewShadow MON_212_R_meta 2
/-- Spew Shadow Yellow (MON_213_Y). -/
def MON_213_Y : CardDef := spewShadow MON_213_Y_meta 1
/-- Spew Shadow Blue (MON_214_B). -/
def MON_214_B : CardDef := spewShadow MON_214_B_meta 0

/-- Shared helper for Blood Tribute. -/
def bloodTribute (base : CardDef) (optN : Nat) : CardDef :=
  draftedCard base []
    (some
      { body := .seqL
          [ .prim (.opt .controller optN)
          , .prim (.banishTopDeck .controller 1 false) ] })

/-- Blood Tribute Red (MON_215_R). -/
def MON_215_R : CardDef := bloodTribute MON_215_R_meta 3
/-- Blood Tribute Yellow (MON_216_Y). -/
def MON_216_Y : CardDef := bloodTribute MON_216_Y_meta 2
/-- Blood Tribute Blue (MON_217_B). -/
def MON_217_B : CardDef := bloodTribute MON_217_B_meta 1

/-- Eclipse Existence Blue (MON_218_B). -/
def MON_218_B : CardDef :=
  draftedCard MON_218_B_meta []
    (some
      { body := .seqL
          [ .grant (.allMatching .controller CardFilter.attackAction)
              (.grantTrigger .onHitHero none
                (.may (.prim (.banishFromSoul .defendingHero 1)) (.prim (.loseLife .defendingHero (.const 1)))))
              .thisTurn
          , .ifThen (.not_ .lessLifeThanOpponent)
              (.may (.prim (.banishFromGraveyard .controller actionCardFilter 1)) .nop)
              .nop ] })

/-- Blasmophet, the Soul Harvester Token (MON_219, Shadow Demon Ally). -/
def MON_219 : CardDef :=
  draftedCard MON_219_meta
    [ weaponAttackAbility 0
    , .triggered .onAttack false none none
        { extraCosts := [{ cost := .banishFromHand shadowFilter 1, optional := true }]
          body := .ifThen .additionalCostPaid
            (.may (.prim (.banishFromSoul .defendingHero 1)) .nop)
            .nop } ]

/-- Ursur, the Soul Reaper Token (MON_220, Shadow Demon Ally). -/
def MON_220 : CardDef :=
  draftedCard MON_220_meta
    [ weaponAttackAbility 0
    , .static_ (some (.zoneCountGe .defendingHero .soul CardFilter.any 1))
        .self_ (.grantKeyword .goAgain) ]

/-! ## Brute (MON221–MON228) -/

/-- Ravenous Meataxe (MON_221). -/
def MON_221 : CardDef :=
  draftedCard MON_221_meta
    [ weaponAttackAbility 2
    , .triggered .onAttack false none none
        { body := .seqL
            [ .prim (.draw .controller (.const 1))
            , .prim (.discardRandom .controller (.const 1))
            , .ifThen (.lastDiscardedMatches power6Filter)
                (.grant .self_ (.addPower (.const 2)) .thisTurn)
                .nop ] } ]

/-- Tear Limb from Limb Blue (MON_222_B). -/
def MON_222_B : CardDef :=
  draftedCard MON_222_B_meta []
    (some
      { body := .seqL
          [ .prim (.draw .controller (.const 1))
          , .prim (.discardRandom .controller (.const 1))
          , .ifThen (.lastDiscardedMatches power6Filter)
              (.grant (.nextCardPlayed bruteAttackFilter) .doubleDamageToHero .thisTurn)
              .nop ] })

/-- Shared helper for Pulping. -/
def pulping (base : CardDef) : CardDef :=
  draftedCard base
    [ .triggered .onAttack false none none
        { body := .seqL
            [ .prim (.draw .controller (.const 1))
            , .prim (.discardRandom .controller (.const 1))
            , .ifThen (.lastDiscardedMatches power6Filter)
                (.grant .self_ (.grantKeyword .dominate) .thisChainLink)
                .nop ] }
    , .static_ (some (.defendedByFewerNonEquip 2)) .self_ (.grantKeyword .goAgain) ]

/-- Pulping Red (MON_223_R). -/
def MON_223_R : CardDef := pulping MON_223_R_meta
/-- Pulping Yellow (MON_224_Y). -/
def MON_224_Y : CardDef := pulping MON_224_Y_meta
/-- Pulping Blue (MON_225_B). -/
def MON_225_B : CardDef := pulping MON_225_B_meta

/-- Smash with Big Tree Red (MON_226_R, vanilla). -/
def MON_226_R : CardDef := verifiedCard MON_226_R_meta
/-- Smash with Big Tree Yellow (MON_227_Y, vanilla). -/
def MON_227_Y : CardDef := verifiedCard MON_227_Y_meta
/-- Smash with Big Tree Blue (MON_228_B, vanilla). -/
def MON_228_B : CardDef := verifiedCard MON_228_B_meta

/-! ## Runeblade (MON229–MON237) -/

/-- Dread Scythe (MON_229). -/
def MON_229 : CardDef :=
  draftedCard MON_229_meta
    [ weaponAttackAbility 3
    , .triggered .onAttack false none none
        { body := .prim (.dealDamage .arcane .defendingHero (.const 1)) }
    , .triggered (.onDealDamage 1 true) false none none
        { body := .grant (.hero .defendingHero) .cantGainLife .nextActionPhase } ]

/-- Aether Ironweave (MON_230). -/
def MON_230 : CardDef :=
  draftedCard MON_230_meta
    [ .activated .action false { actionPoints := 1 } [{ cost := .destroySelf }] none true
        { body := .prim (.gainResource .controller (.const 2)) } ]

/-- Sonata Arcanix Red (MON_231_R). -/
def MON_231_R : CardDef :=
  draftedCard MON_231_R_meta []
    (some
      { targets := [targetHero]
        extraCosts := [{ cost := .payX }]
        body := .bindRevealTopCount .controller 3 CardFilter.attackAction ⟨0⟩
          (.seqL
            [ .prim (.dealDamage .arcane (.ownerOfSlot 0) (.varVal ⟨0⟩))
            , .prim (.shuffleZoneIntoDeck .controller .deck CardFilter.any (some 0) false)
            , .prim (.banish .self_ false) ]) })

/-- Shared helper for Vexing Malice & Arcanic Crackle (on attack deal N arcane). -/
def attackArcane (base : CardDef) (dmg : Int) : CardDef :=
  draftedCard base
    [ .triggered .onAttack false none none
        { targets := [targetHero]
          body := .prim (.dealDamage .arcane (.ownerOfSlot 0) (.const dmg)) } ]

/-- Vexing Malice Red (MON_232_R). -/
def MON_232_R : CardDef := attackArcane MON_232_R_meta 2
/-- Vexing Malice Yellow (MON_233_Y). -/
def MON_233_Y : CardDef := attackArcane MON_233_Y_meta 2
/-- Vexing Malice Blue (MON_234_B). -/
def MON_234_B : CardDef := attackArcane MON_234_B_meta 2

/-- Arcanic Crackle Red (MON_235_R). -/
def MON_235_R : CardDef := attackArcane MON_235_R_meta 1
/-- Arcanic Crackle Yellow (MON_236_Y). -/
def MON_236_Y : CardDef := attackArcane MON_236_Y_meta 1
/-- Arcanic Crackle Blue (MON_237_B). -/
def MON_237_B : CardDef := attackArcane MON_237_B_meta 1

/-! ## Generic (MON238–MON306) -/

/-- Blood Drop Brocade (MON_238). -/
def MON_238 : CardDef :=
  draftedCard MON_238_meta
    [ .activated .instant false {} [{ cost := .destroySelf }] none false
        { body := .prim (.gainResource .controller (.const 1)) } ]

/-- Stubby Hammerers (MON_239). -/
def MON_239 : CardDef :=
  draftedCard MON_239_meta
    [ .activated .action false { actionPoints := 1 } [{ cost := .destroySelf }] none true
        { body := .grant (.allMatching .controller attackPowerLe3Filter) (.addPower (.const 1)) .thisTurn } ]

/-- Time Skippers (MON_240). -/
def MON_240 : CardDef :=
  draftedCard MON_240_meta
    [ .activated .action false { actionPoints := 1, resources := 3 } [{ cost := .destroySelf }] none false
        { body := .prim (.gainAP .controller (.const 2)) } ]

/-- Shared helper for Ironhide equipment cycle (Helm, Plate, Gauntlet, Legs). -/
def ironhideEquip (base : CardDef) : CardDef :=
  draftedCard base
    [ .triggered .onDefend false none none
        { extraCosts := [{ cost := .payResources 1, optional := true }]
          body := .ifThen .additionalCostPaid
            (.seqL
              [ .grant .self_ (.addDefense (.const 2)) .thisChainLink
              , .grant .self_ (.grantTrigger .onChainClose none (.prim (.destroy .self_))) .thisCombatChain ])
            .nop } ]

/-- Ironhide Helm (MON_241). -/
def MON_241 : CardDef := ironhideEquip MON_241_meta
/-- Ironhide Plate (MON_242). -/
def MON_242 : CardDef := ironhideEquip MON_242_meta
/-- Ironhide Gauntlet (MON_243). -/
def MON_243 : CardDef := ironhideEquip MON_243_meta
/-- Ironhide Legs (MON_244). -/
def MON_244 : CardDef := ironhideEquip MON_244_meta

/-- Exude Confidence Red (MON_245_R). -/
def MON_245_R : CardDef :=
  draftedCard MON_245_R_meta
    [ .static_ none (.hero .defendingHero) .cantPlayInstantsOrDefReactions
    , .activated .instant false { resources := 3 } [] none false
        { body := .grant .self_ (.addPower (.const 2)) .thisChainLink } ]

/-- Nourishing Emptiness Red (MON_246_R). -/
def MON_246_R : CardDef :=
  draftedCard MON_246_R_meta
    [ .static_ (some (.not_ (.zoneCountGe .controller .graveyard CardFilter.attackAction 1)))
        .self_ (.grantKeyword .dominate)
    , .triggered .onHit false none
        (some (.not_ (.zoneCountGe .controller .graveyard CardFilter.attackAction 1)))
        { body := .grant (.hero .controller) (.addIntellect 1) .thisTurn } ]

/-- Rouse the Ancients Blue (MON_247_B). -/
def MON_247_B : CardDef :=
  draftedCard MON_247_B_meta []
    (some
      { extraCosts := [{ cost := .revealHandCard CardFilter.attackAction, optional := true }]
        body := .ifThen .additionalCostPaid
          (.seqL
            [ .grant .self_ (.addPower (.const 7)) .thisChainLink
            , .grant .self_ (.grantKeyword .goAgain) .thisChainLink ])
          .nop })

/-- Shared helper for Out Muscle. -/
def outMuscle (base : CardDef) : CardDef :=
  draftedCard base
    [ .static_ (some (.defendedByFewerNonEquip 1)) .self_ (.grantKeyword .goAgain) ]

/-- Out Muscle Red (MON_248_R). -/
def MON_248_R : CardDef := outMuscle MON_248_R_meta
/-- Out Muscle Yellow (MON_249_Y). -/
def MON_249_Y : CardDef := outMuscle MON_249_Y_meta
/-- Out Muscle Blue (MON_250_B). -/
def MON_250_B : CardDef := outMuscle MON_250_B_meta

/-- Shared helper for Seek Horizon. -/
def seekHorizon (base : CardDef) : CardDef :=
  draftedCard base []
    (some
      { extraCosts := [{ cost := .putHandCardOnDeckTop, optional := true }]
        body := .ifThen .additionalCostPaid
          (.grant .self_ (.grantKeyword .goAgain) .thisChainLink)
          .nop })

/-- Seek Horizon Red (MON_251_R). -/
def MON_251_R : CardDef := seekHorizon MON_251_R_meta
/-- Seek Horizon Yellow (MON_252_Y). -/
def MON_252_Y : CardDef := seekHorizon MON_252_Y_meta
/-- Seek Horizon Blue (MON_253_B). -/
def MON_253_B : CardDef := seekHorizon MON_253_B_meta

/-- Shared helper for Tremor of i'Arathael. -/
def tremorOfIArathael (base : CardDef) : CardDef :=
  draftedCard base
    [ .static_ (some (.zoneCountGe .controller .banished CardFilter.any 1))
        .self_ (.addPower (.const 2)) ]

/-- Tremor of i'Arathael Red (MON_254_R). -/
def MON_254_R : CardDef := tremorOfIArathael MON_254_R_meta
/-- Tremor of i'Arathael Yellow (MON_255_Y). -/
def MON_255_Y : CardDef := tremorOfIArathael MON_255_Y_meta
/-- Tremor of i'Arathael Blue (MON_256_B). -/
def MON_256_B : CardDef := tremorOfIArathael MON_256_B_meta

/-- Shared helper for Rise Above. -/
def riseAbove (base : CardDef) : CardDef :=
  draftedCard base []
    (some { extraCosts := [{ cost := .putHandCardOnDeckTop, optional := true }] })

/-- Rise Above Red (MON_257_R). -/
def MON_257_R : CardDef := riseAbove MON_257_R_meta
/-- Rise Above Yellow (MON_258_Y). -/
def MON_258_Y : CardDef := riseAbove MON_258_Y_meta
/-- Rise Above Blue (MON_259_B). -/
def MON_259_B : CardDef := riseAbove MON_259_B_meta

/-- Shared helper for Captain's Call (modal choose 1: +2{p} OR go again on next attack cost ≤ maxC). -/
def captainsCall (base : CardDef) (maxC : Nat) : CardDef :=
  draftedCard base []
    (some
      { modes :=
          [ { body := .grant (.nextCardPlayed (attackCostLeFilter maxC)) (.addPower (.const 2)) .thisTurn }
          , { body := .grant (.nextCardPlayed (attackCostLeFilter maxC)) (.grantKeyword .goAgain) .thisTurn } ] })

/-- Captain's Call Red (MON_260_R). -/
def MON_260_R : CardDef := captainsCall MON_260_R_meta 2
/-- Captain's Call Yellow (MON_261_Y). -/
def MON_261_Y : CardDef := captainsCall MON_261_Y_meta 1
/-- Captain's Call Blue (MON_262_B). -/
def MON_262_B : CardDef := captainsCall MON_262_B_meta 0

/-- Shared helper for Adrenaline Rush. -/
def adrenalineRush (base : CardDef) : CardDef :=
  draftedCard base
    [ .triggered .onPlay false none (some .lessLifeThanOpponent)
        { body := .grant .self_ (.addPower (.const 3)) .thisChainLink } ]

/-- Adrenaline Rush Red (MON_263_R). -/
def MON_263_R : CardDef := adrenalineRush MON_263_R_meta
/-- Adrenaline Rush Yellow (MON_264_Y). -/
def MON_264_Y : CardDef := adrenalineRush MON_264_Y_meta
/-- Adrenaline Rush Blue (MON_265_B). -/
def MON_265_B : CardDef := adrenalineRush MON_265_B_meta

/-- Shared helper for Belittle. -/
def belittle (base : CardDef) : CardDef :=
  draftedCard base []
    (some
      { extraCosts := [{ cost := .revealHandCard powerLe3Filter, optional := true }]
        body := .ifThen .additionalCostPaid
          (.prim (.searchDeck .controller minnowismFilter (some 1) .hand true none))
          .nop })

/-- Belittle Red (MON_266_R). -/
def MON_266_R : CardDef := belittle MON_266_R_meta
/-- Belittle Yellow (MON_267_Y). -/
def MON_267_Y : CardDef := belittle MON_267_Y_meta
/-- Belittle Blue (MON_268_B). -/
def MON_268_B : CardDef := belittle MON_268_B_meta

/-- Shared helper for Brandish. -/
def brandish (base : CardDef) : CardDef :=
  draftedCard base
    [ .triggered .onHit false none none
        { body := .grant (.nextAttack CardFilter.weaponAttack) (.addPower (.const 1)) .thisTurn } ]

/-- Brandish Red (MON_269_R). -/
def MON_269_R : CardDef := brandish MON_269_R_meta
/-- Brandish Yellow (MON_270_Y). -/
def MON_270_Y : CardDef := brandish MON_270_Y_meta
/-- Brandish Blue (MON_271_B). -/
def MON_271_B : CardDef := brandish MON_271_B_meta

/-- Shared helper for Frontline Scout. -/
def frontlineScout (base : CardDef) : CardDef :=
  draftedCard base
    [ .static_ (some .playedFromArsenal) .self_ (.grantKeyword .goAgain) ]

/-- Frontline Scout Red (MON_272_R). -/
def MON_272_R : CardDef := frontlineScout MON_272_R_meta
/-- Frontline Scout Yellow (MON_273_Y). -/
def MON_273_Y : CardDef := frontlineScout MON_273_Y_meta
/-- Frontline Scout Blue (MON_274_B). -/
def MON_274_B : CardDef := frontlineScout MON_274_B_meta

/-- Shared helper for Overload. -/
def overload (base : CardDef) : CardDef :=
  draftedCard base
    [ .triggered .onHit false none none
        { body := .grant .self_ (.grantKeyword .goAgain) .thisChainLink } ]

/-- Overload Red (MON_275_R). -/
def MON_275_R : CardDef := overload MON_275_R_meta
/-- Overload Yellow (MON_276_Y). -/
def MON_276_Y : CardDef := overload MON_276_Y_meta
/-- Overload Blue (MON_277_B). -/
def MON_277_B : CardDef := overload MON_277_B_meta

/-- Shared helper for Pound for Pound. -/
def poundForPound (base : CardDef) : CardDef :=
  draftedCard base
    [ .triggered .onPlay false none (some .lessLifeThanOpponent)
        { body := .grant .self_ (.grantKeyword .dominate) .thisChainLink } ]

/-- Pound for Pound Red (MON_278_R). -/
def MON_278_R : CardDef := poundForPound MON_278_R_meta
/-- Pound for Pound Yellow (MON_279_Y). -/
def MON_279_Y : CardDef := poundForPound MON_279_Y_meta
/-- Pound for Pound Blue (MON_280_B). -/
def MON_280_B : CardDef := poundForPound MON_280_B_meta

/-- Shared helper for Rally the Rearguard. -/
def rallyTheRearguard (base : CardDef) : CardDef :=
  draftedCard base
    [ .activated .instant true {} [{ cost := .discardChoice CardFilter.any 1 }] none false
        { body := .grant .self_ (.addDefense (.const 3)) .thisChainLink } ]

/-- Rally the Rearguard Red (MON_281_R). -/
def MON_281_R : CardDef := rallyTheRearguard MON_281_R_meta
/-- Rally the Rearguard Yellow (MON_282_Y). -/
def MON_282_Y : CardDef := rallyTheRearguard MON_282_Y_meta
/-- Rally the Rearguard Blue (MON_283_B). -/
def MON_283_B : CardDef := rallyTheRearguard MON_283_B_meta

/-- Shared helper for Stony Woottonhog. -/
def stonyWoottonhog (base : CardDef) : CardDef :=
  draftedCard base
    [ .static_ (some (.defendedByFewerNonEquip 2)) .self_ (.addPower (.const 1)) ]

/-- Stony Woottonhog Red (MON_284_R). -/
def MON_284_R : CardDef := stonyWoottonhog MON_284_R_meta
/-- Stony Woottonhog Yellow (MON_285_Y). -/
def MON_285_Y : CardDef := stonyWoottonhog MON_285_Y_meta
/-- Stony Woottonhog Blue (MON_286_B). -/
def MON_286_B : CardDef := stonyWoottonhog MON_286_B_meta

/-- Shared helper for Surging Militia. -/
def surgingMilitia (base : CardDef) : CardDef :=
  draftedCard base
    [ .static_ (some .defendedFromHandThisLink) .self_ (.addPower (.const 1)) ]

/-- Surging Militia Red (MON_287_R). -/
def MON_287_R : CardDef := surgingMilitia MON_287_R_meta
/-- Surging Militia Yellow (MON_288_Y). -/
def MON_288_Y : CardDef := surgingMilitia MON_288_Y_meta
/-- Surging Militia Blue (MON_289_B). -/
def MON_289_B : CardDef := surgingMilitia MON_289_B_meta

/-- Shared helper for Yinti Yanti. -/
def yintiYanti (base : CardDef) : CardDef :=
  draftedCard base
    [ .static_ (some (.zoneCountGe .controller .arena auraFilter 1)) .self_ (.addPower (.const 1))
    , .static_ (some (.zoneCountGe .controller .arena auraFilter 1)) .self_ (.addDefense (.const 1)) ]

/-- Yinti Yanti Red (MON_290_R). -/
def MON_290_R : CardDef := yintiYanti MON_290_R_meta
/-- Yinti Yanti Yellow (MON_291_Y). -/
def MON_291_Y : CardDef := yintiYanti MON_291_Y_meta
/-- Yinti Yanti Blue (MON_292_B). -/
def MON_292_B : CardDef := yintiYanti MON_292_B_meta

/-- Shared helper for Zealous Belting. -/
def zealousBelting (base : CardDef) (minPitchPower : Int) : CardDef :=
  draftedCard base
    [ .static_ (some (.zoneCountGe .controller .pitch { minPower := some minPitchPower } 1))
        .self_ (.grantKeyword .goAgain) ]

/-- Zealous Belting Red (MON_293_R). -/
def MON_293_R : CardDef := zealousBelting MON_293_R_meta 6
/-- Zealous Belting Yellow (MON_294_Y). -/
def MON_294_Y : CardDef := zealousBelting MON_294_Y_meta 5
/-- Zealous Belting Blue (MON_295_B). -/
def MON_295_B : CardDef := zealousBelting MON_295_B_meta 4

/-- Shared helper for Minnowism. -/
def minnowism (base : CardDef) (bonus : Int) : CardDef :=
  draftedCard base []
    (some
      { body := .grant (.nextCardPlayed attackPowerLe3Filter) (.addPower (.const bonus)) .thisTurn })

/-- Minnowism Red (MON_296_R). -/
def MON_296_R : CardDef := minnowism MON_296_R_meta 3
/-- Minnowism Yellow (MON_297_Y). -/
def MON_297_Y : CardDef := minnowism MON_297_Y_meta 2
/-- Minnowism Blue (MON_298_B). -/
def MON_298_B : CardDef := minnowism MON_298_B_meta 1

/-- Shared helper for Warmonger's Recital. -/
def warmongersRecital (base : CardDef) (bonus : Int) : CardDef :=
  draftedCard base []
    (some
      { body := .seqL
          [ .grant (.nextCardPlayed CardFilter.attackAction) (.addPower (.const bonus)) .thisTurn
          , .grant (.nextCardPlayed CardFilter.attackAction)
              (.grantTrigger .onHit none (.prim (.moveCard .self_ .deck .bottom false)))
              .thisTurn ] })

/-- Warmonger's Recital Red (MON_299_R). -/
def MON_299_R : CardDef := warmongersRecital MON_299_R_meta 3
/-- Warmonger's Recital Yellow (MON_300_Y). -/
def MON_300_Y : CardDef := warmongersRecital MON_300_Y_meta 2
/-- Warmonger's Recital Blue (MON_301_B). -/
def MON_301_B : CardDef := warmongersRecital MON_301_B_meta 1

/-- Talisman of Dousing Yellow (MON_302_Y, Go again + Spellvoid 1). -/
def MON_302_Y : CardDef := draftedCard MON_302_Y_meta

/-- Shared helper for Memorial Ground. -/
def memorialGround (base : CardDef) (maxC : Nat) : CardDef :=
  draftedCard base []
    (some
      { targets := [{ kind := .cardInZone .controller .graveyard, filter := attackCostLeFilter maxC, minCount := 1, maxCount := some 1 }]
        body := .prim (.moveCard (.slot 0) .deck .top false) })

/-- Memorial Ground Red (MON_303_R). -/
def MON_303_R : CardDef := memorialGround MON_303_R_meta 2
/-- Memorial Ground Yellow (MON_304_Y). -/
def MON_304_Y : CardDef := memorialGround MON_304_Y_meta 1
/-- Memorial Ground Blue (MON_305_B). -/
def MON_305_B : CardDef := memorialGround MON_305_B_meta 0

/-- Cracked Bauble Yellow (MON_306_Y, Limited resource). -/
def MON_306_Y : CardDef := draftedCard MON_306_Y_meta

/-! ## Complete 307-card Monarch (MON) catalog -/

/-- Light Landmark, Light Illusionist, Light Warrior, Light cards (`MON_000`–`MON_087_Y`, 88 cards). -/
def monLightCards : List CardDef :=
  [ MON_000
  , MON_001, MON_002, MON_003, MON_004_Y, MON_005_Y, MON_006_Y, MON_007_Y
  , MON_008_R, MON_009_Y, MON_010_B, MON_011_Y, MON_012_Y, MON_013_Y
  , MON_014_R, MON_015_Y, MON_016_B, MON_017_R, MON_018_Y, MON_019_B
  , MON_020_R, MON_021_Y, MON_022_B, MON_023_R, MON_024_Y, MON_025_B
  , MON_026_R, MON_027_Y, MON_028_B
  , MON_029, MON_030, MON_031, MON_032_Y, MON_033_Y, MON_034_Y, MON_035_Y
  , MON_036_R, MON_037_Y, MON_038_B, MON_039_R, MON_040_Y, MON_041_B
  , MON_042_R, MON_043_Y, MON_044_B, MON_045_R, MON_046_Y, MON_047_B
  , MON_048_R, MON_049_Y, MON_050_B, MON_051_R, MON_052_Y, MON_053_B
  , MON_054_R, MON_055_Y, MON_056_B, MON_057_R, MON_058_Y, MON_059_B
  , MON_060, MON_061, MON_062_Y, MON_063_Y, MON_064_Y, MON_065_Y
  , MON_066_R, MON_067_Y, MON_068_B, MON_069_R, MON_070_Y, MON_071_B
  , MON_072_R, MON_073_Y, MON_074_B, MON_075_R, MON_076_Y, MON_077_B
  , MON_078_R, MON_079_Y, MON_080_B, MON_081_R, MON_082_Y, MON_083_B
  , MON_084_R, MON_085_Y, MON_086_B, MON_087_Y ]

/-- Illusionist and Warrior cards (`MON_088`–`MON_118_B`, 31 cards). -/
def monIllusionistWarriorCards : List CardDef :=
  [ MON_088, MON_089, MON_090, MON_091_R
  , MON_092_R, MON_093_Y, MON_094_B, MON_095_R, MON_096_Y, MON_097_B
  , MON_098_R, MON_099_Y, MON_100_B, MON_101_R, MON_102_Y, MON_103_B, MON_104
  , MON_105, MON_106, MON_107, MON_108, MON_109_R
  , MON_110_R, MON_111_Y, MON_112_B, MON_113_R, MON_114_Y, MON_115_B
  , MON_116_R, MON_117_Y, MON_118_B ]

/-- Shadow Brute, Shadow Runeblade, and Shadow cards (`MON_119`–`MON_220`, 102 cards). -/
def monShadowCards : List CardDef :=
  [ MON_119, MON_120, MON_121, MON_122, MON_123_Y, MON_124_Y, MON_125_R
  , MON_126_R, MON_127_Y, MON_128_B, MON_129_R, MON_130_Y, MON_131_B
  , MON_132_R, MON_133_Y, MON_134_B, MON_135_R, MON_136_Y, MON_137_B
  , MON_138_R, MON_139_Y, MON_140_B, MON_141_R, MON_142_Y, MON_143_B
  , MON_144_R, MON_145_Y, MON_146_B, MON_147_R, MON_148_Y, MON_149_B
  , MON_150_R, MON_151_Y, MON_152_B
  , MON_153, MON_154, MON_155, MON_156_B, MON_157_Y, MON_158_B
  , MON_159_R, MON_160_Y, MON_161_B, MON_162_R, MON_163_Y, MON_164_B
  , MON_165_R, MON_166_Y, MON_167_B, MON_168_R, MON_169_Y, MON_170_B
  , MON_171_R, MON_172_Y, MON_173_B, MON_174_R, MON_175_Y, MON_176_B
  , MON_177_R, MON_178_Y, MON_179_B, MON_180_R, MON_181_Y, MON_182_B
  , MON_183_R, MON_184_Y, MON_185_B, MON_186
  , MON_187, MON_188, MON_189_B, MON_190_B, MON_191_B, MON_192_R, MON_193_R, MON_194_R
  , MON_195_R, MON_196_Y, MON_197_B, MON_198_B, MON_199_R
  , MON_200_R, MON_201_Y, MON_202_B, MON_203_R, MON_204_Y, MON_205_B
  , MON_206_R, MON_207_Y, MON_208_B, MON_209_R, MON_210_Y, MON_211_B
  , MON_212_R, MON_213_Y, MON_214_B, MON_215_R, MON_216_Y, MON_217_B
  , MON_218_B, MON_219, MON_220 ]

/-- Brute, Runeblade, and Generic cards (`MON_221`–`MON_306_Y`, 86 cards). -/
def monBruteRunebladeGenericCards : List CardDef :=
  [ MON_221, MON_222_B, MON_223_R, MON_224_Y, MON_225_B, MON_226_R, MON_227_Y, MON_228_B
  , MON_229, MON_230, MON_231_R
  , MON_232_R, MON_233_Y, MON_234_B, MON_235_R, MON_236_Y, MON_237_B
  , MON_238, MON_239, MON_240, MON_241, MON_242, MON_243, MON_244
  , MON_245_R, MON_246_R, MON_247_B
  , MON_248_R, MON_249_Y, MON_250_B, MON_251_R, MON_252_Y, MON_253_B
  , MON_254_R, MON_255_Y, MON_256_B, MON_257_R, MON_258_Y, MON_259_B
  , MON_260_R, MON_261_Y, MON_262_B, MON_263_R, MON_264_Y, MON_265_B
  , MON_266_R, MON_267_Y, MON_268_B, MON_269_R, MON_270_Y, MON_271_B
  , MON_272_R, MON_273_Y, MON_274_B, MON_275_R, MON_276_Y, MON_277_B
  , MON_278_R, MON_279_Y, MON_280_B, MON_281_R, MON_282_Y, MON_283_B
  , MON_284_R, MON_285_Y, MON_286_B, MON_287_R, MON_288_Y, MON_289_B
  , MON_290_R, MON_291_Y, MON_292_B, MON_293_R, MON_294_Y, MON_295_B
  , MON_296_R, MON_297_Y, MON_298_B, MON_299_R, MON_300_Y, MON_301_B
  , MON_302_Y, MON_303_R, MON_304_Y, MON_305_B, MON_306_Y ]

/-- Complete list of all 307 Monarch (`MON`) logical cards with `.full` IR definitions. -/
def monCards : List CardDef :=
  monLightCards ++ monIllusionistWarriorCards ++ monShadowCards ++ monBruteRunebladeGenericCards

end FabCards.MON

end
