module

import FabCards
import Fab.Engine.Step
import Fab.Invariant.Info
import Fab.Rules.Setup
meta import FabCards
meta import Fab.Engine.Step
meta import Fab.Invariant.Info
meta import Fab.Rules.Setup

open Fab FabCards

-- The authorized test prints resolve to the same four implemented equipment cards.
#guard (["OXO001-P", "OXO002-P", "OXO003-P", "OXO004-P"].map fun number =>
    (earlyPrintingCardId? number).bind wtrDB.find? |>.map (·.front.name)) ==
  [some "Ironrot Helm", some "Ironrot Plate", some "Ironrot Gauntlet", some "Ironrot Legs"]

#guard earlyPrintingCardId? "OXO005" == none

meta def earlyAttacker : PlayerId := ⟨0⟩
meta def earlyDefender : PlayerId := ⟨1⟩

meta def earlyBase : GameState :=
  let s : GameState :=
    { config := GameConfig.ccDuel, cards := throughWtrDB, turn := 2
      active := some earlyAttacker, turnOrder := [earlyAttacker, earlyDefender]
      phase := .actionPhase, pending := [.priority earlyAttacker 0] }
  ((s.setLife earlyAttacker 20).setLife earlyDefender 40).setPool earlyAttacker
    { actionPoints := 4, resources := 8 }

meta def earlyPlace (s : GameState) (p : PlayerId) (zone : Zone) (name : String) :
    Option (GameState × ObjId) :=
  addObject s zone
    { kind := .card ⟨s.nextId⟩ ⟨name⟩, owner := p, controller := p, timestamp := ⟨0⟩ } .top

meta def earlySteps (s : GameState) (actions : List Action) : Option GameState :=
  actions.foldlM (fun st action => ((step 64 st action).toOption).map Prod.fst) s

meta def earlyPass : List Action :=
  [⟨.player earlyAttacker, .pass⟩, ⟨.player earlyDefender, .pass⟩]

meta def earlyAttack (s : GameState) (action : ActionKind) : Option GameState :=
  earlySteps s (⟨.player earlyAttacker, action⟩ :: earlyPass ++ earlyPass)

meta def earlyDamage (s : GameState) : Option GameState :=
  earlySteps s (⟨.player earlyDefender, .defendDone⟩ :: earlyPass ++ earlyPass)

meta def iraAttackOrdinalScenario : Option Bool := do
  let p := earlyAttacker
  let (heroState, hero) ← earlyPlace earlyBase p (.player p .hero) "IRA_001"
  let (weaponState, weapon) ← earlyPlace heroState p (.player p .weapon) "WTR_078"
  let (handState, jab) ← earlyPlace weaponState p (.player p .hand) "WTR_100_B"
  let (ready, another) ← earlyPlace handState p (.player p .hand) "WTR_100_B"
  let first ← earlyAttack ready (.attackWeapon weapon)
  let hit ← earlyDamage first
  let closed ← earlySteps hit (earlyPass ++ earlyPass)
  let second ← earlyAttack closed (.playCard jab)
  let secondHit ← earlyDamage second
  let third ← (earlySteps secondHit earlyPass).bind (earlyAttack · (.playCard another))
  let firstLink ← first.combat.bind CombatChain.activeLink?
  let secondLink ← second.combat.bind CombatChain.activeLink?
  let thirdLink ← third.combat.bind CombatChain.activeLink?
  let silence : ContinuousEffect :=
    { id := second.nextTimestamp, source := hero, controller := earlyDefender, target := .obj hero
      op := .loseAllAbilities, duration := .thisTurn, timestamp := ⟨second.nextTimestamp⟩ }
  pure (closed.combat.isNone && firstLink.turnAttackOrdinal == 1 && linkAttackPower first firstLink == 1 &&
    secondLink.linkId.n == 1 && secondLink.turnAttackOrdinal == 2 && linkAttackPower second secondLink == 2 &&
    linkAttackPower { second with activeEffects := [silence] } secondLink == 1 &&
    thirdLink.turnAttackOrdinal == 3 && linkAttackPower third thirdLink == 1)

#guard iraAttackOrdinalScenario == some true

meta def edgeOfAutumnScenario : Option Bool := do
  let p := earlyAttacker
  let (ready, sword) ← earlyPlace earlyBase p (.player p .weapon) "IRA_002"
  let defending ← earlyAttack ready (.attackWeapon sword)
  let hit ← earlyDamage defending
  let finished ← earlySteps hit earlyPass
  let link ← hit.combat.bind CombatChain.activeLink?
  pure (linkAttackPower hit link == 1 && linkHasKeyword hit link .goAgain &&
    (finished.poolOf p).actionPoints == 4 && (finished.poolOf p).resources == 7 &&
    !(canAttackWithWeapon finished p sword))
#guard edgeOfAutumnScenario == some true

meta def blossomScenario : Option Bool := do
  let p := earlyAttacker
  let deck := Zone.player p .deck
  let handZone := Zone.player p .hand
  let (one, _) ← earlyPlace earlyBase p deck "WTR_100_B"
  let (two, _) ← earlyPlace one p deck "WTR_100_B"
  let (hand, jab) ← earlyPlace two p handZone "WTR_100_B"
  let (ready, blossom) ← earlyPlace hand p (.player p .hand) "IRA_003_Y"
  let opening ← earlyAttack ready (.playCard blossom)
  let openingHit ← earlyDamage opening
  let prior ← (earlyAttack ready (.playCard jab)).bind earlyDamage
  let next ← (earlySteps prior earlyPass).bind (earlyAttack · (.playCard blossom))
  let hit ← earlyDamage next
  let trigger ← hit.pendingTriggers.head?
  let resolved ← earlySteps hit
    ([⟨.player p, .pickTriggerStart p⟩, ⟨.player p, .pickTrigger trigger.id⟩] ++ earlyPass)
  pure (openingHit.pendingTriggers.isEmpty && hit.pendingTriggers.length == 1 &&
    (resolved.zone deck).isEmpty && (resolved.zone handZone).length == 2)
#guard blossomScenario == some true

meta def saltScenario : Option Bool := do
  let p := earlyAttacker
  let (hand, jab) ← earlyPlace earlyBase p (.player p .hand) "WTR_100_B"
  let (ready, salt) ← earlyPlace hand p (.player p .hand) "IRA_004_Y"
  let opening ← earlyAttack ready (.playCard salt)
  let prior ← (earlyAttack ready (.playCard jab)).bind earlyDamage
  let follow ← (earlySteps prior earlyPass).bind (earlyAttack · (.playCard salt))
  let baseLink ← opening.combat.bind CombatChain.activeLink?
  let linked ← follow.combat.bind CombatChain.activeLink?
  let saltHit ← earlyDamage follow
  let afterHit ← saltHit.combat.bind CombatChain.activeLink?
  pure (linkAttackPower opening baseLink == 2 && linkAttackPower follow linked == 3 &&
    linkAttackPower saltHit afterHit == 4 && saltHit.lifeOf earlyDefender == 36)
#guard saltScenario == some true

meta def thornsScenario : Option Bool := do
  let p := earlyAttacker
  let (hand, thorns) ← earlyPlace earlyBase p (.player p .hand) "IRA_005_Y"
  let (ready, jab) ← earlyPlace hand p (.player p .hand) "WTR_100_B"
  let hit ← (earlyAttack ready (.playCard thorns)).bind earlyDamage
  let trigger ← hit.pendingTriggers.head?
  let resolved ← earlySteps hit
    ([⟨.player p, .pickTriggerStart p⟩, ⟨.player p, .pickTrigger trigger.id⟩] ++ earlyPass)
  let follow ← (earlySteps resolved earlyPass).bind (earlyAttack · (.playCard jab))
  let link ← follow.combat.bind CombatChain.activeLink?
  pure (linkAttackPower follow link == 2)
#guard thornsScenario == some true

meta def tempoScenario : Option Bool := do
  let p := earlyAttacker
  let (ready, tempo) ← earlyPlace earlyBase p (.player p .hand) "IRA_006_R"
  let hit ← (earlyAttack ready (.playCard tempo)).bind earlyDamage
  let trigger ← hit.pendingTriggers.head?
  let before ← hit.combat.bind CombatChain.activeLink?
  let resolved ← earlySteps hit
    ([⟨.player p, .pickTriggerStart p⟩, ⟨.player p, .pickTrigger trigger.id⟩] ++ earlyPass)
  let after ← resolved.combat.bind CombatChain.activeLink?
  pure (!linkHasKeyword hit before .goAgain && linkHasKeyword resolved after .goAgain)
#guard tempoScenario == some true

meta def kickScenario : Option Bool := do
  let p := earlyAttacker
  let (firstHand, jab1) ← earlyPlace earlyBase p (.player p .hand) "WTR_100_B"
  let (secondHand, jab2) ← earlyPlace firstHand p (.player p .hand) "WTR_100_B"
  let (ready, kick) ← earlyPlace secondHand p (.player p .hand) "IRA_007_R"
  let first ← earlyAttack ready (.playCard kick)
  let hit1 ← (earlyAttack ready (.playCard jab1)).bind earlyDamage
  let second ← (earlySteps hit1 earlyPass).bind (earlyAttack · (.playCard kick))
  let hit2 ← (earlySteps hit1 earlyPass).bind (earlyAttack · (.playCard jab2)) >>= earlyDamage
  let third ← (earlySteps hit2 earlyPass).bind (earlyAttack · (.playCard kick))
  let power (s : GameState) := (s.combat.bind CombatChain.activeLink?).map (linkAttackPower s)
  pure (power first == some 5 && power second == some 5 && power third == some 7)
#guard kickScenario == some true

#guard ((earlyPrintingCardId? "IRA008-P").bind throughWtrDB.find?).any
  (fun c => c.id == ⟨"WTR_100_B"⟩ && c.status == .full)

#guard ((earlyPrintingCardId? "IRA009-P").bind throughWtrDB.find?).any
  (fun c => c.id == ⟨"WTR_191_R"⟩ && c.status == .full)

meta def assaultScenario : Option Bool := do
  let p := earlyAttacker
  let (ready, assault) ← earlyPlace earlyBase p (.player p .hand) "IRA_010_B"
  let hit ← (earlyAttack ready (.playCard assault)).bind earlyDamage
  pure (hit.lifeOf earlyDefender == 36 && (hit.poolOf p).resources == 6)
#guard assaultScenario == some true

meta def pressScenario : Option Bool := do
  let p := earlyAttacker
  let (hand, jab) ← earlyPlace earlyBase p (.player p .hand) "WTR_100_B"
  let (ready, press) ← earlyPlace hand p (.player p .hand) "IRA_011_B"
  let defending ← earlyAttack ready (.playCard jab)
  let reaction ← earlySteps defending (⟨.player earlyDefender, .defendDone⟩ :: earlyPass)
  let resolved ← earlySteps reaction (⟨.player p, .playCard press⟩ :: earlyPass)
  let link ← resolved.combat.bind CombatChain.activeLink?
  pure (linkAttackPower resolved link == 2 && (resolved.poolOf p).resources == 8)
#guard pressScenario == some true

meta def springboardScenario : Option Bool := do
  let p := earlyAttacker
  let q := earlyDefender
  let (ready, jab) ← earlyPlace earlyBase p (.player p .hand) "WTR_100_B"
  let defendWith (zone : Zone) := do
    let (s, reaction) ← earlyPlace ready q zone "IRA_012_Y"
    let attacking ← earlyAttack s (.playCard jab)
    let offered ← earlySteps attacking (⟨.player q, .defendDone⟩ :: earlyPass)
    let resolved ← earlySteps offered
      [⟨.player p, .pass⟩, ⟨.player q, .playCard reaction⟩,
       ⟨.player q, .pass⟩, ⟨.player p, .pass⟩]
    let link ← resolved.combat.bind CombatChain.activeLink?
    pure (linkTotalDefense resolved link)
  let hand ← defendWith (.player q .hand)
  let arsenal ← defendWith (.player q .arsenal)
  pure (hand == 2 && arsenal == 4)
#guard springboardScenario == some true

-- The original Ira deck has twelve printings, two of which share WTR card IDs.
#guard
  ["IRA001-P", "IRA002-P", "IRA003-P", "IRA004-P", "IRA005-P", "IRA006-P",
   "IRA007-P", "IRA008-P", "IRA009-P", "IRA010-P", "IRA011-P", "IRA012-P"].map
    earlyPrintingCardId? ==
  (["IRA_001", "IRA_002", "IRA_003_Y", "IRA_004_Y", "IRA_005_Y", "IRA_006_R",
    "IRA_007_R", "WTR_100_B", "WTR_191_R", "IRA_010_B", "IRA_011_B", "IRA_012_Y"].map
      fun id => some (CardId.mk id))

#guard
  ["LGS001-P", "LGS002-P", "LGS003-P", "LGS004-P", "LGS005-P", "LGS006-P",
   "LGS007-P", "LGS008-P"].map earlyPrintingCardId? ==
  (["WTR_003", "WTR_040", "WTR_078", "WTR_115", "WTR_031_B", "WTR_054_R", "WTR_110_R",
    "WTR_132_R"].map fun id => some (CardId.mk id))

#guard wtrDB.cards.length == 226
#guard IRA.iraCards.length == 10
#guard throughWtrDB.cards.length == 236 && throughWtrDB.cards.all (·.status == .full)

#guard ([ ("BVO", 29), ("TEA", 30), ("KSU", 30), ("RNR", 31) ] : List (String × Nat)).all
  (fun (setCode, count) => (List.range count).all fun index =>
    let number := String.ofList ((toString (index + 1)).toList.leftpad 3 '0')
    ((earlyPrintingCardId? (setCode ++ number)).bind throughWtrDB.find?).any (·.status == .full))

#guard ["BVO015", "KSU021", "RNR022", "TEA019"].all
  (fun number => earlyPrintingCardId? number == some ⟨"IRA_012_Y"⟩)
#guard earlyPrintingCardId? "KSU028" == some ⟨"IRA_011_B"⟩
#guard earlyPrintingCardId? "KSU003" == earlyPrintingCardId? "KSU004"
#guard earlyPrintingCardId? "KSU031" == none

meta def goBananasScenario : Option Bool := do
  let player := earlyAttacker
  let opponent := earlyDefender
  let hand := Zone.player player .hand
  let cards : CardDB := ⟨LSS.LSS_002_Y :: throughWtrDB.cards⟩
  let setup := { earlyBase with cards, phase := .setup }
  let first ← supplyBooster setup player [⟨"WTR_203_R"⟩]
  let other ← supplyBooster first opponent [⟨"WTR_098_R"⟩]
  let stocked ← supplyBooster other player [⟨"WTR_098_R"⟩, ⟨"WTR_100_B"⟩, ⟨"WTR_203_R"⟩]
  let (ready, promo) ← earlyPlace { stocked with phase := .actionPhase } player hand "LSS_002_Y"
  let choose ← earlySteps ready (⟨.player player, .playCard promo⟩ :: earlyPass)
  let .chooseModal _ _ _ _ choices :: _ := choose.pending | none
  let headJab ← choices.findIdx? (· == .prim (.openBoosters (some "Head Jab")))
  let (miss, firstEvents) ← (step 64 choose ⟨.player player, .pickMode headJab⟩).toOption
  let declined ← earlySteps miss [⟨.player player, .pickMay false⟩]
  let (hit, nextEvents) ← (step 64 miss ⟨.player player, .pickMay true⟩).toOption
  let received := (hit.zone hand).filterMap fun id => (hit.obj? id).bind (·.kind.cardId?)
  pure ((declined.zone hand).isEmpty && received.length == 2 &&
    received.contains ⟨"WTR_098_R"⟩ && received.contains ⟨"WTR_100_B"⟩ &&
    firstEvents.contains (.boosterOpened player [⟨"WTR_203_R"⟩]) &&
    nextEvents.contains (.boosterOpened player [⟨"WTR_098_R"⟩, ⟨"WTR_100_B"⟩, ⟨"WTR_203_R"⟩]) &&
    hit.unopenedBoosters.length == 1 && hit.physIds.length == ready.physIds.length)

#guard goBananasScenario == some true

#guard
  (["FAB001-P", "HER005-P", "HER006-P", "HER007-P", "HER008-P"].map fun number =>
    ((earlyPrintingCardId? number).bind throughWtrDB.find?).map (·.front.name)) ==
  ["Fyendal's Spring Tunic", "Rhinar", "Bravo", "Katsu", "Dorinthea"].map some

#guard ARC.Meta.allMeta.length == 219
#guard ARC.Meta.allMeta.all (fun card => card.sets == [.arc] && card.status == .todo)
#guard ((earlyPrintingCardId? "ARC218").bind throughWtrDB.find?).any
  (fun card => card.front.name == "Cracked Bauble" && card.status == .full)

meta def eyeOfOphidiaScenario : Option Bool := do
  let player := earlyAttacker
  let deck := Zone.player player .deck
  let hand := Zone.player player .hand
  let setup := { earlyBase.setPool player { actionPoints := 1 } with cards := throughArcDB }
  let (base, untouched) ← earlyPlace setup player deck "WTR_203_R"
  let (one, second) ← earlyPlace base player deck "WTR_098_R"
  let (two, first) ← earlyPlace one player deck "WTR_100_B"
  let (three, eye) ← earlyPlace two player hand "ARC_000_B"
  let (ready, tome) ← earlyPlace three player hand "WTR_160_Y"
  let pitched ← earlySteps ready [⟨.player player, .playCard tome⟩, ⟨.player player, .pitchCard eye⟩]
  let trigger ← pitched.pendingTriggers.head?
  let viewed ← earlySteps pitched
    ([⟨.player player, .pickTriggerStart player⟩, ⟨.player player, .pickTrigger trigger.id⟩] ++ earlyPass)
  let reorder ← earlySteps viewed [⟨.player player, .optPick true (some second)⟩]
  let (swapped, events) ← (step 64 reorder ⟨.player player, .optPick true⟩).toOption
  let bottom ← earlySteps viewed
    [⟨.player player, .optPick false (some second)⟩, ⟨.player player, .optPick false⟩]
  pure ((view player viewed).selectionChoices.map Prod.fst == [first, second] &&
    (view earlyDefender viewed).selectionChoices.isEmpty &&
    (earlySteps viewed [⟨.player player, .optPick true (some untouched)⟩]).isNone &&
    swapped.zone deck == [second, first, untouched] && events.contains (.opted player 2 0) &&
    bottom.zone deck == [untouched, second, first] &&
    (swapped.poolOf player).resources == 2 && (swapped.zone .stack).length == 1)

#guard eyeOfOphidiaScenario == some true

meta def dashSetupScenario (hero : String) (format : Format) (deckSize : Nat)
    (itemId : String := "Dash-test-item") (startingSteam : Nat := 0) : Option Bool := do
  let player := earlyAttacker
  let opponent := earlyDefender
  let permanent := Zone.player player .permanent
  let deck := Zone.player player .deck
  let inventory := Zone.player player .inventory
  let item : CardDef :=
    { id := ⟨"Dash-test-item"⟩
      front := { name := "Setup item", supertypes := [.class_ .mechanologist],
                 types := [.action], subtypes := [.item], cost := some { actionPoints := 1, resources := 2 } } }
  let expensive :=
    { item with
      id := ⟨"Dash-test-expensive"⟩
      front := { item.front with name := "Costlier item", cost := some { actionPoints := 1, resources := 3 } } }
  let cards : CardDB := ⟨item :: expensive :: throughArcDB.cards⟩
  let setup :=
    { earlyBase with
      cards
      phase := .setup
      config := { earlyBase.config with format }
      pending := [.chooseLoadout player, .revealLoadouts] }
  let (withHero, _) ← earlyPlace setup player (.player player .hero) hero
  let loaded ← (List.range (deckSize - 1)).foldlM
    (fun s _ => (earlyPlace s player deck "WTR_203_R").map Prod.fst) withHero
  let (withExpensive, wrong) ← earlyPlace loaded player inventory "Dash-test-expensive"
  let (ready, allowed) ← earlyPlace withExpensive player inventory itemId
  let selected ← earlySteps ready [⟨.player player, .loadoutEquip allowed⟩]
  let id ← (selected.zone permanent).head?
  let revealed ← earlySteps selected [⟨.player player, .loadoutDone⟩]
  pure (!loadoutCanFinish ready player && loadoutCanFinish selected player &&
    loadoutEquipDest? ready player wrong == none && (selected.obj? id).any (·.faceDown) &&
    viewZone opponent selected permanent == .countOnly 0 &&
    viewZone opponent selected deck == .countOnly deckSize &&
    (revealed.obj? id).any (fun obj => !obj.faceDown && obj.counterCount .steam == startingSteam) &&
    (revealed.zone deck).length == deckSize - 1)

#guard dashSetupScenario "ARC_001" .classicConstructed 60 == some true
#guard dashSetupScenario "ARC_002" .blitz 40 == some true
#guard dashSetupScenario "ARC_001" .classicConstructed 60 "ARC_007_B" 2 == some true
#guard dashSetupScenario "ARC_002" .blitz 40 "ARC_007_B" 2 == some true

#guard (["ARC003", "LGS009-P"].map fun number =>
  (earlyPrintingCardId? number).bind throughArcDB.find? |>.map (·.front.name)) ==
  [some "Teklo Plasma Pistol", some "Teklo Plasma Pistol"]

meta def tekloPlasmaPistolScenario : Option Bool := do
  let p := earlyAttacker
  let (ready, pistol) ← earlyPlace { earlyBase with cards := throughArcDB } p
    (.player p .weapon) "ARC_003"
  let fire : Action := ⟨.player p, .attackWeapon pistol⟩
  let load : Action := ⟨.player p, .activateAbility pistol 1 none⟩
  let steam (s : GameState) := (s.obj? pistol).map (fun obj => obj.counterCount .steam)
  let loaded ← earlySteps ready (load :: earlyPass)
  let surcharge : ContinuousEffect :=
    { id := loaded.nextTimestamp, source := pistol, controller := p, target := .nextActionBy p
      op := .addCostRes 1, duration := .thisTurn, timestamp := ⟨loaded.nextTimestamp⟩ }
  let (taxed, pitch) ← earlyPlace
    { loaded.setPool p { actionPoints := 4 } with activeEffects := [surcharge] }
    p (.player p .hand) "WTR_100_B"
  let paying ← earlySteps taxed [fire]
  let cancelled ← earlySteps paying [⟨.player p, .cancelPlay⟩]
  let paidByPitch ← earlySteps paying [⟨.player p, .pitchCard pitch⟩]
  let loadedAgain ← earlySteps loaded (load :: earlyPass)
  let paid ← earlySteps loadedAgain [fire]
  let defending ← earlySteps paid (earlyPass ++ earlyPass)
  let link ← defending.combat.bind CombatChain.activeLink?
  let hit ← earlyDamage defending
  let closed ← earlySteps hit (earlyPass ++ earlyPass)
  let reloaded ← earlySteps closed (load :: earlyPass)
  let second ← earlyAttack reloaded (.attackWeapon pistol)
  let secondLink ← second.combat.bind CombatChain.activeLink?
  pure ((earlySteps ready [fire]).isNone && steam ready == some 0 &&
    steam loaded == some 1 && (loaded.poolOf p).actionPoints == 4 && (loaded.poolOf p).resources == 7 &&
    steam paying == some 1 && steam cancelled == some 1 &&
    cancelled.zone .stack == [] && cancelled.zone (.player p .hand) == [pitch] &&
    (cancelled.poolOf p).actionPoints == 4 && cancelled.activeEffects == [surcharge] &&
    steam paidByPitch == some 0 && (paidByPitch.poolOf p).resources == 2 &&
    paidByPitch.activeEffects.isEmpty &&
    steam loadedAgain == some 1 && (loadedAgain.poolOf p).actionPoints == 4 &&
    (loadedAgain.poolOf p).resources == 6 &&
    steam paid == some 0 && (paid.poolOf p).actionPoints == 3 && (paid.poolOf p).resources == 6 &&
    link.attackSource == some pistol && linkAttackPower defending link == 2 &&
    (earlySteps closed [fire]).isNone &&
    secondLink.attackSource == some pistol && secondLink.turnAttackOrdinal == 2 &&
    linkAttackPower second secondLink == 2 && steam second == some 0)

#guard tekloPlasmaPistolScenario == some true

#guard ((earlyPrintingCardId? "ARC004").bind throughArcDB.find?).any
  (fun card => card.front.name == "Teklo Foundry Heart" && card.status == .full)

meta def foundryHeartScenario (deckCards : List String) (matchCount : Nat) (mechBoost : Bool) :
    Option Bool := do
  let p := earlyAttacker
  let deck := Zone.player p .deck
  let banished := Zone.player p .banished
  let fixture : CardDef :=
    { id := ⟨"Boost fixture"⟩
      front :=
        { name := "Boost fixture"
          supertypes := [.class_ .mechanologist]
          types := [.action]
          subtypes := [.attack]
          cost := some { actionPoints := 1 }
          power := some 3
          keywords := [.boost] } }
  let cards : CardDB := ⟨fixture :: throughArcDB.cards⟩
  let (equipped, heart) ← earlyPlace { earlyBase with cards } p (.player p .chest) "ARC_004"
  let deckReady ← deckCards.reverse.foldlM
    (fun s name => (earlyPlace s p deck name).map Prod.fst) equipped
  let (ready, attack) ← earlyPlace deckReady p (.player p .hand) fixture.id.val
  let use : Action := ⟨.player p, .activateAbility heart 0 none⟩
  let declare : Action := ⟨.player p, .playCard attack⟩
  let (withoutDeck, anotherAttack) ← earlyPlace equipped p (.player p .hand) fixture.id.val
  let paidWithoutBoost ← earlySteps withoutDeck [⟨.player p, .playCard anotherAttack⟩]
  let choose ← earlySteps ready [declare]
  let cancelled ← earlySteps choose [⟨.player p, .cancelPlay⟩]
  let declined ← earlySteps choose [⟨.player p, .pickMay false⟩]
  let (paid, events) ← (step 64 choose ⟨.player p, .pickMay true⟩).toOption
  let defended ← earlySteps paid (earlyPass ++ earlyPass)
  let link ← defended.combat.bind CombatChain.activeLink?
  let hit ← earlyDamage defended
  let closed ← earlySteps hit (earlyPass ++ earlyPass)
  let result ← earlySteps closed (use :: earlyPass)
  pure ((earlySteps ready [use]).isNone &&
    (earlySteps paidWithoutBoost [⟨.player p, .pickMay true⟩]).isNone &&
    paidWithoutBoost.zone banished == [] && paidWithoutBoost.boostsThisTurn == [] &&
    cancelled.zone deck == ready.zone deck && !cancelled.boostsThisTurn.contains p &&
    declined.zone deck == ready.zone deck && !declined.boostsThisTurn.contains p &&
    paid.boostsThisTurn == [p] && events.contains (.boosted p) &&
    (paid.zone deck).length == deckCards.length - 1 &&
    (paid.zone banished).length == 1 &&
    linkHasKeyword defended link .goAgain == mechBoost &&
    (earlySteps hit [use]).isNone && (earlySteps result [use]).isNone &&
    result.zone deck == [] && (result.zone banished).length == deckCards.length &&
    (result.poolOf p).resources == 7 + matchCount &&
    (result.poolOf p).actionPoints == (closed.poolOf p).actionPoints)

#guard foundryHeartScenario ["WTR_191_R", "ARC_007_B", "WTR_203_R"] 1 false == some true
#guard foundryHeartScenario ["ARC_007_B", "ARC_007_B", "ARC_007_B"] 2 true == some true
#guard foundryHeartScenario ["WTR_191_R"] 0 false == some true

#guard ((earlyPrintingCardId? "ARC005").bind throughArcDB.find?).any
  (fun card => card.front.name == "Achilles Accelerator" && card.status == .full &&
    card.front.keywords.contains (.arcaneBarrier 1))

meta def achillesAcceleratorScenario : Option Bool := do
  let p := earlyAttacker
  let base := { earlyBase.setPool p {} with cards := throughArcDB }
  let (ready, accelerator) ← earlyPlace base p (.player p .legs) "ARC_005"
  let use : Action := ⟨.player p, .activateAbility accelerator 0 none⟩
  let (announced, events) ← (step 64 { ready with boostsThisTurn := [p] } use).toOption
  let resolved ← earlySteps announced earlyPass
  let spent ← (announced.zone (.player p .graveyard)).head?
  pure ((earlySteps ready [use]).isNone &&
    events.contains (.moved accelerator spent (.player p .legs) (.player p .graveyard)) &&
    announced.zone (.player p .legs) == [] && (announced.poolOf p).actionPoints == 0 &&
    (resolved.cardDefOf? spent).any (fun card => card.id == ⟨"ARC_005"⟩) &&
    (resolved.poolOf p).actionPoints == 1 && (resolved.poolOf p).resources == 0)

#guard achillesAcceleratorScenario == some true

meta def acceleratorDamageBoard (kind : DamageKind) (resources : Nat) :
    Option (GameState × ObjId × ObjId) := do
  let p := earlyDefender
  let testDamage : CardDef :=
    { id := ⟨"Arcane Barrier damage fixture"⟩
      front :=
        { name := "Damage fixture"
          types := [.action]
          cost := some { actionPoints := 1 }
          playEffect := some { body := .prim (.dealDamage kind .opposingHero (.const 2)) } } }
  let cards : CardDB := ⟨testDamage :: throughArcDB.cards⟩
  let base := { earlyBase.setPool p { resources } with cards }
  let (equipped, accelerator) ← earlyPlace base p (.player p .legs) "ARC_005"
  let (ready, damage) ← earlyPlace equipped earlyAttacker (.player earlyAttacker .hand) testDamage.id.val
  return (ready, accelerator, damage)

meta def acceleratorBarrierScenario : Option Bool := do
  let p := earlyDefender
  let select (id : Option Nat) : Action := ⟨.player p, .pickReplacement id⟩
  let (ready, accelerator, damage) ← acceleratorDamageBoard .arcane 1
  let play (id : ObjId) := ⟨Actor.player earlyAttacker, ActionKind.playCard id⟩ :: earlyPass
  let prompt ← earlySteps ready (play damage)
  let .chooseReplacement _ .prevention [barrier] true :: _ := prompt.pending | none
  let prevented ← earlySteps prompt [select (some barrier)]
  let declined ← earlySteps prompt [select none]
  let lethal ← earlySteps (prompt.setLife p 1) [select (some barrier)]
  let (physical, _, physicalDamage) ← acceleratorDamageBoard .physical 1
  let physicalHit ← earlySteps physical (play physicalDamage)
  let (withoutResources, _, pitchDamage) ← acceleratorDamageBoard .arcane 0
  let noPayment ← earlySteps withoutResources (play pitchDamage)
  let (withCard, pitchCard) ← earlyPlace withoutResources p (.player p .hand) "WTR_100_B"
  let pitchOffer ← earlySteps withCard (play pitchDamage)
  let .chooseReplacement _ .prevention [pitchBarrier] true :: _ := pitchOffer.pending | none
  let paying ← earlySteps pitchOffer [select (some pitchBarrier)]
  let paid ← earlySteps paying [⟨.player p, .pitchCard pitchCard⟩]
  pure (prompt.lifeOf p == 40 &&
    (view earlyAttacker pitchOffer).pending.head? == (view earlyAttacker noPayment).pending.head? &&
    (legalActionsFor p noPayment).contains (select none) &&
    !(legalActionsFor p noPayment).contains (select (some barrier)) &&
    !(legalActionsFor earlyAttacker pitchOffer).contains (select (some pitchBarrier)) &&
    prevented.lifeOf p == 39 && (prevented.poolOf p).resources == 0 &&
    prevented.zone (.player p .legs) == [accelerator] &&
    declined.lifeOf p == 38 && (declined.poolOf p).resources == 1 &&
    lethal.result == some (.won [earlyAttacker]) && lethal.pending.isEmpty &&
    physicalHit.lifeOf p == 38 && (physicalHit.poolOf p).resources == 1 &&
    paying.lifeOf p == 40 && (legalActionsFor p paying).contains ⟨.player p, .pitchCard pitchCard⟩ &&
    !(legalActionsFor p paying).contains ⟨.player p, .cancelPlay⟩ &&
    paid.lifeOf p == 39 && (paid.poolOf p).resources == 2 && (paid.poolOf p).actionPoints == 0 &&
    (paid.zone (.player p .pitch)).length == 1)

#guard acceleratorBarrierScenario == some true

meta def acceleratorShieldOrderScenario : Option Bool := do
  let p := earlyDefender
  let (ready, accelerator, damage) ← acceleratorDamageBoard .arcane 1
  let shield : ReplacementEffect :=
    { id := 0, source := accelerator, controller := p, stage := .prevention, action := .shieldPrevent 2 }
  let board := { ready with activeReplacements := [shield] }
  let prompt ← earlySteps board (⟨.player earlyAttacker, .playCard damage⟩ :: earlyPass)
  let .chooseReplacement _ .prevention [shieldId, barrier] false :: _ := prompt.pending | none
  let shieldFirst ← earlySteps prompt [⟨.player p, .pickReplacement (some shieldId)⟩]
  let barrierThenShield ← earlySteps prompt [⟨.player p, .pickReplacement (some barrier)⟩]
  pure (shieldId == shield.id &&
    (earlySteps prompt [⟨.player p, .pickReplacement none⟩]).isNone &&
    shieldFirst.lifeOf p == 40 && (shieldFirst.poolOf p).resources == 1 &&
    shieldFirst.activeReplacements.isEmpty &&
    barrierThenShield.lifeOf p == 40 && (barrierThenShield.poolOf p).resources == 0 &&
    barrierThenShield.activeReplacements == [{ shield with action := .shieldPrevent 1 }])

#guard acceleratorShieldOrderScenario == some true

#guard ((earlyPrintingCardId? "ARC006").bind throughArcDB.find?).any
  (fun card => card.front.name == "High Octane" && card.status == .full)

meta def highOctaneScenario : Option Bool := do
  let p := earlyAttacker
  let hand := Zone.player p .hand
  let deck := Zone.player p .deck
  let fixture : CardDef :=
    { id := ⟨"High Octane Boost fixture"⟩
      front :=
        { name := "High Octane Boost fixture"
          supertypes := [.class_ .mechanologist]
          types := [.action]
          subtypes := [.attack]
          cost := some { actionPoints := 1 }
          power := some 3
          keywords := [.boost] } }
  let cards : CardDB := ⟨fixture :: throughArcDB.cards⟩
  let start := { earlyBase with cards, boostsThisTurn := [p] }
  let (tail, mech) ← earlyPlace start p deck fixture.id.val
  let (middle, generic) ← earlyPlace tail p deck "WTR_191_R"
  let (drawReady, _) ← earlyPlace middle p deck "WTR_203_R"
  let (withFirst, first) ← earlyPlace drawReady p hand fixture.id.val
  let (withSecond, second) ← earlyPlace withFirst p hand fixture.id.val
  let (ready, octane) ← earlyPlace withSecond p hand "ARC_006_R"
  let resolved ← earlySteps ready (⟨.player p, .playCard octane⟩ :: earlyPass)
  let firstChoice ← earlySteps resolved [⟨.player p, .playCard first⟩]
  let declined ← earlySteps firstChoice [⟨.player p, .pickMay false⟩]
  let firstBoost ← earlySteps firstChoice [⟨.player p, .pickMay true⟩]
  let firstTrigger ← firstBoost.pendingTriggers.head?
  let answer (id : Nat) : List Action :=
    [⟨.player p, .pickTriggerStart p⟩, ⟨.player p, .pickTrigger id⟩] ++ earlyPass
  let firstGain ← earlySteps firstBoost (answer firstTrigger.id)
  let firstAttack ← earlySteps firstGain (earlyPass ++ earlyPass)
  let firstHit ← earlyDamage firstAttack
  let closed ← earlySteps firstHit (earlyPass ++ earlyPass)
  let secondBoost ← earlySteps closed
    [⟨.player p, .playCard second⟩, ⟨.player p, .pickMay true⟩]
  let secondTrigger ← secondBoost.pendingTriggers.head?
  let secondGain ← earlySteps secondBoost (answer secondTrigger.id)
  let secondAttack ← earlySteps secondGain (earlyPass ++ earlyPass)
  let secondHit ← (earlyDamage secondAttack).bind (earlySteps · earlyPass)
  let (expired, _) ← microStep { secondHit with pending := [.endTurnCleanup p] }
  let firstLink ← firstAttack.combat.bind CombatChain.activeLink?
  let secondLink ← secondAttack.combat.bind CombatChain.activeLink?
  pure (resolved.zone deck == [generic, mech] && (resolved.zone hand).length == 3 &&
    resolved.delayedTriggers.length == 1 && resolved.pendingTriggers.isEmpty &&
    (resolved.poolOf p).actionPoints == 4 && (resolved.poolOf p).resources == 7 &&
    declined.pendingTriggers.isEmpty && declined.boostsThisTurn == [p] &&
    firstBoost.pendingTriggers.length == 1 && secondBoost.pendingTriggers.length == 1 &&
    firstTrigger.sourceLki.name == "High Octane" && secondTrigger.sourceLki.name == "High Octane" &&
    (firstBoost.poolOf p).actionPoints == 3 && (firstGain.poolOf p).actionPoints == 4 &&
    (secondBoost.poolOf p).actionPoints == 3 && (secondGain.poolOf p).actionPoints == 4 &&
    !linkHasKeyword firstAttack firstLink .goAgain && linkHasKeyword secondAttack secondLink .goAgain &&
    (secondHit.poolOf p).actionPoints == 5 && expired.delayedTriggers.isEmpty)

#guard highOctaneScenario == some true

#guard ((earlyPrintingCardId? "ARC007").bind throughArcDB.find?).any
  (fun card => card.front.name == "Teklo Core" && card.status == .full &&
    card.specializations == ["Dash"])

meta def tekloCoreScenario : Option Bool := do
  let p := earlyAttacker
  let permanent := Zone.player p .permanent
  let grave := Zone.player p .graveyard
  let (ready, card) ← earlyPlace { earlyBase with cards := throughArcDB } p (.player p .hand) "ARC_007_B"
  let entered ← earlySteps ready (⟨.player p, .playCard card⟩ :: earlyPass)
  let core ← (entered.zone permanent).head?
  let steam (s : GameState) := (s.obj? core).map (·.counterCount .steam)
  let newActionPhase (s : GameState) := do
    let next := { s.setPool p {} with turn := s.turn + 2, pending := [.actionPhaseStart p] }
    ((advance 64 next []).toOption).map Prod.fst
  let resolve (s : GameState) := do
    let trigger ← s.pendingTriggers.head?
    earlySteps s ([⟨.player p, .pickTriggerStart p⟩, ⟨.player p, .pickTrigger trigger.id⟩] ++ earlyPass)
  let first ← newActionPhase entered
  let oneLeft ← resolve first
  let second ← newActionPhase oneLeft
  let depleted ← resolve second
  let destruction ← depleted.pendingTriggers.head?
  let spent ← resolve depleted
  let discarded ← (spent.zone grave).head?
  pure (card != core && steam entered == some 2 && entered.pendingTriggers.isEmpty &&
    first.pendingTriggers.length == 1 && second.pendingTriggers.length == 1 &&
    steam oneLeft == some 1 && (oneLeft.poolOf p).resources == 2 &&
    oneLeft.pendingTriggers.isEmpty && steam depleted == some 0 && (depleted.poolOf p).resources == 2 &&
    depleted.zone permanent == [core] && depleted.zone grave == [] &&
    depleted.pendingTriggers.length == 1 && destruction.source == core &&
    destruction.effect == .prim (.destroy .self_) &&
    spent.zone permanent == [] && (spent.cardDefOf? discarded).any (fun card => card.id == ⟨"ARC_007_B"⟩))

#guard tekloCoreScenario == some true

#guard ((earlyPrintingCardId? "ARC008").bind throughArcDB.find?).any
  (fun card => card.front.name == "Maximum Velocity" && card.status == .full)

meta def maximumVelocityScenario : Option Bool := do
  let p := earlyAttacker
  let q := earlyDefender
  let hand := Zone.player p .hand
  let deck := Zone.player p .deck
  let fixture : CardDef :=
    { id := ⟨"Maximum Velocity boost fixture"⟩
      front :=
        { name := "Maximum Velocity boost fixture"
          supertypes := [.class_ .mechanologist]
          types := [.action]
          subtypes := [.attack]
          cost := some { actionPoints := 1 }
          power := some 1
          keywords := [.boost] } }
  let cards : CardDB := ⟨fixture :: throughArcDB.cards⟩
  let stocked ← (List.range 3).foldlM
    (fun s _ => (earlyPlace s p deck "WTR_191_R").map Prod.fst) { earlyBase with cards }
  let (withFirst, first) ← earlyPlace stocked p hand fixture.id.val
  let (withSecond, second) ← earlyPlace withFirst p hand fixture.id.val
  let (withThird, third) ← earlyPlace withSecond p hand fixture.id.val
  let (withVelocity, velocity) ← earlyPlace withThird p hand "ARC_008_R"
  let (ready, defendingCard) ← earlyPlace withVelocity q (.player q .hand) "ARC_008_R"
  let playBoost (s : GameState) (id : ObjId) :=
    earlySteps s ([⟨.player p, .playCard id⟩, ⟨.player p, .pickMay true⟩] ++ earlyPass ++ earlyPass)
  let finish (s : GameState) := (earlyDamage s).bind (earlySteps · (earlyPass ++ earlyPass))
  let firstBoost ← playBoost ready first
  let firstLink ← firstBoost.combat.bind CombatChain.activeLink?
  let one ← finish firstBoost
  let two ← (playBoost one second).bind finish
  let three ← (playBoost two third).bind finish
  let announced : Action := ⟨.player p, .playCard velocity⟩
  let attack ← earlyAttack three (.playCard velocity)
  let velocityLink ← attack.combat.bind CombatChain.activeLink?
  pure ((earlySteps two [announced]).isNone &&
    !(legalActionsFor p { two with boostsThisTurn := q :: two.boostsThisTurn }).contains announced &&
    (legalActionsFor p three).contains announced &&
    canPlayCard { three with boostsThisTurn := p :: three.boostsThisTurn } p velocity &&
    canPitchCard ready p velocity && canDefendWith firstBoost firstLink q defendingCard &&
    !linkHasKeyword firstBoost firstLink .goAgain && three.boostsThisTurn == [p, p, p] &&
    linkAttackPower attack velocityLink == 10 && (attack.poolOf p).resources == 6)

#guard maximumVelocityScenario == some true

#guard ((earlyPrintingCardId? "ARC009").bind throughArcDB.find?).any
  (fun card => card.front.name == "Spark of Genius" && card.status == .full &&
    card.front.xCostFactor == 2 && card.specializations == ["Dash"])

meta def sparkOfGeniusScenario (x : Nat) (boosted : Bool) : Option Bool := do
  let p := earlyAttacker
  let q := earlyDefender
  let deck := Zone.player p .deck
  let hand := Zone.player p .hand
  let permanent := Zone.player p .permanent
  let item : CardDef :=
    { id := ⟨"Spark test item"⟩
      front :=
        { name := "Spark test item"
          supertypes := [.class_ .mechanologist]
          types := [.action]
          subtypes := [.item]
          cost := some { actionPoints := 1, resources := 2 } } }
  let wrong :=
    { item with
      id := ⟨"Spark generic item"⟩
      front := { item.front with name := "Spark generic item", supertypes := [.generic] } }
  let cards : CardDB := ⟨item :: wrong :: throughArcDB.cards⟩
  let base := { earlyBase.setPool p { actionPoints := 2, resources := 1 } with
    cards, boostsThisTurn := if boosted then [p] else [] }
  let (tail, _) ← earlyPlace base p deck "WTR_203_R"
  let (withGeneric, genericItem) ← earlyPlace tail p deck wrong.id.val
  let (withTwo, itemTwo) ← earlyPlace withGeneric p deck item.id.val
  let (withZero, itemZero) ← earlyPlace withTwo p deck "ARC_007_B"
  let (withPitch, blue) ← earlyPlace withZero p hand "WTR_100_B"
  let (ready, spark) ← earlyPlace withPitch p hand "ARC_009_Y"
  let choose (value : Option Nat) : Action := ⟨.player p, .pickVariableResources value⟩
  let pick (id : Option ObjId) : Action := ⟨.player p, .pickShuffleCard id⟩
  let play ← earlySteps ready [⟨.player p, .playCard spark⟩]
  let .chooseVariableResources _ _ _ _ _ 2 false :: _ := play.pending | none
  let .chooseVariableResources _ _ _ _ _ 0 false :: _ := (view q play).pending | none
  let paying ← earlySteps play [choose (some x)]
  let paid ← if x == 0 then some paying else earlySteps paying [⟨.player p, .pitchCard blue⟩]
  let search ← earlySteps paid earlyPass
  let wanted := if x == 0 then itemZero else itemTwo
  let wrongCost := if x == 0 then itemTwo else itemZero
  let invalidOptions := (earlySteps search [pick (some wrongCost)]).isNone &&
    (earlySteps search [pick (some genericItem)]).isNone
  let selected ← earlySteps search [pick (some wanted), pick none]
  let chosen ← (selected.zone permanent).head?
  let shuffled ← earlySteps selected [⟨.chance, .shuffleOrder ((selected.zone deck).reverse)⟩]
  let miss ← earlySteps search [pick none]
  let missed ← earlySteps miss [⟨.chance, .shuffleOrder ((miss.zone deck).reverse)⟩]
  let expectedId := if x == 0 then ⟨"ARC_007_B"⟩ else item.id
  pure ((earlySteps play [choose none]).isNone && (earlySteps play [choose (some 3)]).isNone &&
    (paid.poolOf p).resources == (if x == 0 then 1 else 0) && invalidOptions &&
    (selected.zone hand).length == (if x == 0 then 1 else 0) &&
    (view p search).selectionChoices.map Prod.fst == [wanted] &&
    (view q search).selectionChoices.isEmpty &&
    (shuffled.cardDefOf? chosen).any (fun card => card.id == expectedId) &&
    (shuffled.obj? chosen).any (fun obj => obj.counterCount .steam == (if x == 0 then 2 else 0)) &&
    (shuffled.zone deck).length == (if boosted then 2 else 3) &&
    (shuffled.zone hand).length == (if x == 0 then 1 else 0) + (if boosted then 1 else 0) &&
    missed.zone permanent == [] &&
    (missed.zone deck).length == (if boosted then 3 else 4))

#guard sparkOfGeniusScenario 0 false == some true
#guard sparkOfGeniusScenario 2 true == some true

#guard ((earlyPrintingCardId? "ARC010").bind throughArcDB.find?).any
  (fun card => card.front.name == "Induction Chamber" && card.status == .full)

meta def inductionChamberScenario : Option Bool := do
  let p := earlyAttacker
  let q := earlyDefender
  let permanent := Zone.player p .permanent
  let hand := Zone.player p .hand
  let (equipped, pistol) ← earlyPlace { earlyBase with cards := throughArcDB } p (.player p .weapon) "ARC_003"
  let (withAttack, ordinaryAttack) ← earlyPlace equipped p hand "WTR_100_B"
  let (ready, item) ← earlyPlace withAttack p hand "ARC_010_R"
  let installed ← earlySteps ready (⟨.player p, .playCard item⟩ :: earlyPass)
  let chamber ← (installed.zone permanent).head?
  let load (id : ObjId) (index : Nat) : List Action := ⟨.player p, .activateAbility id index none⟩ :: earlyPass
  let reaction (s : GameState) (attack : ActionKind) :=
    (earlyAttack s attack).bind (earlySteps · (⟨.player q, .defendDone⟩ :: earlyPass))
  let getLink (s : GameState) := s.combat.bind CombatChain.activeLink?
  let giveGoAgain (target : ObjId) : Action := ⟨.player p, .activateAbility chamber 1 (some target)⟩
  let steam (s : GameState) := (s.obj? chamber).map (·.counterCount .steam)
  let loadedPistol ← earlySteps installed (load pistol 1)
  let uncharged ← reaction loadedPistol (.attackWeapon pistol)
  let unchargedAttack ← (getLink uncharged).bind (·.attack)
  let loaded ← earlySteps loadedPistol (load chamber 0)
  let loadedAgain ← earlySteps loaded (load chamber 0)
  let wrongReaction ← reaction loaded (.playCard ordinaryAttack)
  let wrongTarget ← (getLink wrongReaction).bind (·.attack)
  let firstReaction ← reaction loadedAgain (.attackWeapon pistol)
  let link ← getLink firstReaction
  let target ← link.attack
  let paid ← earlySteps firstReaction [giveGoAgain target]
  let granted ← earlySteps paid earlyPass
  let grantedLink ← getLink granted
  let awarded ← earlySteps granted (earlyPass ++ earlyPass)
  let closed ← earlySteps awarded earlyPass
  let reloaded ← earlySteps closed (load pistol 1 ++ load chamber 0)
  let secondReaction ← reaction reloaded (.attackWeapon pistol)
  let newTarget ← (getLink secondReaction).bind (·.attack)
  pure (steam installed == some 0 && steam loaded == some 1 && steam loadedAgain == some 1 &&
    (loadedAgain.poolOf p).resources + 1 == (loaded.poolOf p).resources &&
    (loadedAgain.poolOf p).actionPoints == (loaded.poolOf p).actionPoints &&
    (earlySteps uncharged [giveGoAgain unchargedAttack]).isNone &&
    (earlySteps wrongReaction [giveGoAgain wrongTarget]).isNone &&
    !linkHasKeyword firstReaction link .goAgain && steam paid == some 0 &&
    linkHasKeyword granted grantedLink .goAgain &&
    (awarded.poolOf p).actionPoints == (granted.poolOf p).actionPoints + 1 &&
    steam reloaded == some 1 && (earlySteps secondReaction [giveGoAgain newTarget]).isNone)

#guard inductionChamberScenario == some true

#guard ((earlyPrintingCardId? "ARC011").bind throughArcDB.find?).any
  (fun card => card.front.name == "Pedal to the Metal" && card.status == .full)

meta def pedalToTheMetalScenario (cardId : String) (power : Int) (weaponNext blocked : Bool) :
    Option Bool := do
  let p := earlyAttacker
  let q := earlyDefender
  let hand := Zone.player p .hand
  let getLink (s : GameState) := s.combat.bind CombatChain.activeLink?
  let (equipped, pistol) ← earlyPlace { earlyBase with cards := throughArcDB } p
    (.player p .weapon) "ARC_003"
  let loaded ← earlySteps equipped (⟨.player p, .activateAbility pistol 1 none⟩ :: earlyPass)
  let (withDeck, _) ← earlyPlace loaded p (.player p .deck) "ARC_007_B"
  let (withFollowup, jab) ← earlyPlace withDeck p hand "WTR_100_B"
  let (withPedal, pedal) ← earlyPlace withFollowup p hand cardId
  let (withBlock, firstDefender) ← earlyPlace withPedal q (.player q .hand) "WTR_188_R"
  let (ready, secondDefender) ← earlyPlace withBlock q (.player q .hand) "WTR_188_R"
  let defending ← earlySteps ready
    ([⟨.player p, .playCard pedal⟩, ⟨.player p, .pickMay true⟩] ++ earlyPass ++ earlyPass)
  let pedalLink ← getLink defending
  let defenders : List Action := if blocked then
    [⟨.player q, .defendCard firstDefender⟩, ⟨.player q, .defendCard secondDefender⟩] else []
  let damage ← (earlySteps defending defenders).bind earlyDamage
  let resolved ← if blocked then some damage else do
    let trigger ← damage.pendingTriggers.head?
    earlySteps damage
      ([⟨.player p, .pickTriggerStart p⟩, ⟨.player p, .pickTrigger trigger.id⟩] ++ earlyPass)
  let closed ← earlySteps resolved (earlyPass ++ earlyPass)
  let nextAttack := if weaponNext then ActionKind.attackWeapon pistol else .playCard jab
  let laterAttack := if weaponNext then ActionKind.playCard jab else .attackWeapon pistol
  let next ← earlyAttack closed nextAttack
  let nextLink ← getLink next
  let nextDamage ← earlyDamage next
  let later ← (earlySteps nextDamage earlyPass).bind (earlyAttack · laterAttack)
  let laterLink ← getLink later
  pure (linkAttackPower defending pedalLink == power &&
    (defending.zone (.player p .banished)).map
      (fun id => (defending.cardDefOf? id).map (·.id.val)) == [some "ARC_007_B"] &&
    linkHasKeyword defending pedalLink .goAgain && !linkHasKeyword defending pedalLink .dominate &&
    damage.pendingTriggers.length == (if blocked then 0 else 1) &&
    closed.combat.isNone && linkHasKeyword next nextLink .dominate == !blocked &&
    !linkHasKeyword later laterLink .dominate)

#guard pedalToTheMetalScenario "ARC_011_R" 5 true false == some true
#guard pedalToTheMetalScenario "ARC_011_R" 5 false false == some true
#guard pedalToTheMetalScenario "ARC_011_R" 5 false true == some true
#guard (earlyPrintingCardId? "ARC012").map (·.val) == some "ARC_012_Y"
#guard pedalToTheMetalScenario "ARC_012_Y" 4 true false == some true
#guard pedalToTheMetalScenario "ARC_012_Y" 4 false true == some true
#guard (earlyPrintingCardId? "ARC013").map (·.val) == some "ARC_013_B"
#guard pedalToTheMetalScenario "ARC_013_B" 3 true false == some true
#guard pedalToTheMetalScenario "ARC_013_B" 3 false true == some true

#guard ((earlyPrintingCardId? "ARC014").bind throughArcDB.find?).any
  (fun card => card.front.name == "Pour the Mold" && card.status == .full)

meta def pourTheMoldScenario (boosted : Bool) : Option Bool := do
  let p := earlyAttacker
  let q := earlyDefender
  let hand := Zone.player p .hand
  let deck := Zone.player p .deck
  let arena := Zone.player p .permanent
  let base := { earlyBase with cards := throughArcDB, boostsThisTurn := [if boosted then p else q] }
  let (withDeck, hidden) ← earlyPlace base p deck "WTR_203_R"
  let (withGeneric, genericItem) ← earlyPlace withDeck p hand "WTR_170_B"
  let (withExpensive, expensiveItem) ← earlyPlace withGeneric p hand "ARC_010_R"
  let (withCore, core) ← earlyPlace withExpensive p hand "ARC_007_B"
  let (ready, mold) ← earlyPlace withCore p hand "ARC_014_R"
  let play : Action := ⟨.player p, .playCard mold⟩
  let pick (id : Option ObjId) : Action := ⟨.player p, .pickShuffleCard id⟩
  let choice ← earlySteps ready (play :: earlyPass)
  let declined ← earlySteps choice [pick none]
  let selected ← earlySteps choice [pick (some core)]
  let (placed, events) ← (step 64 selected (pick none)).toOption
  let entered ← (placed.zone arena).head?
  pure ((view p choice).selectionChoices == [(core, ⟨"ARC_007_B"⟩)] &&
    (view q choice).selectionChoices.isEmpty && viewZone p choice deck == .countOnly 1 &&
    (earlySteps choice [pick (some expensiveItem)]).isNone &&
    (earlySteps choice [pick (some genericItem)]).isNone &&
    declined.zone arena == [] && declined.zone hand == [core, expensiveItem, genericItem] &&
    events.contains (.moved core entered hand arena) && placed.zone deck == [hidden] &&
    (placed.cardDefOf? entered).any (fun card => card.id == ⟨"ARC_007_B"⟩) &&
    (placed.obj? entered).any (fun obj => obj.counterCount .steam == if boosted then 3 else 2) &&
    placed.zone hand == [expensiveItem, genericItem] && placed.poolOf p == ready.poolOf p)

#guard pourTheMoldScenario false == some true
#guard pourTheMoldScenario true == some true

meta def pourTheMoldCostScenario (moldId : String) (maxCost : Nat) : Option Bool := do
  let p := earlyAttacker
  let hand := Zone.player p .hand
  let item : CardDef :=
    { id := ⟨"One resource item fixture"⟩
      front :=
        { name := "One resource item fixture"
          supertypes := [.class_ .mechanologist]
          types := [.action]
          subtypes := [.item]
          cost := some { actionPoints := 1, resources := 1 } }
      status := .full }
  let cards : CardDB := ⟨item :: throughArcDB.cards⟩
  let (withZero, zero) ← earlyPlace { earlyBase with cards, boostsThisTurn := [p] } p hand "ARC_007_B"
  let (withOne, one) ← earlyPlace withZero p hand item.id.val
  let (withTwo, two) ← earlyPlace withOne p hand "ARC_010_R"
  let (ready, mold) ← earlyPlace withTwo p hand moldId
  let choosing ← earlySteps ready (⟨.player p, .playCard mold⟩ :: earlyPass)
  let pick (id : Option ObjId) : Action := ⟨.player p, .pickShuffleCard id⟩
  let eligible := if maxCost == 1 then [one, zero] else [two, one, zero]
  let wanted := if maxCost == 1 then one else two
  let resolved ← earlySteps choosing [pick (some wanted), pick none]
  let entered ← (resolved.zone (.player p .permanent)).head?
  pure ((view p choosing).selectionChoices.map Prod.fst == eligible &&
    (maxCost != 1 || (earlySteps choosing [pick (some two)]).isNone) &&
    (resolved.cardDefOf? entered).map (·.id) == (choosing.cardDefOf? wanted).map (·.id) &&
    (resolved.obj? entered).any (fun obj => obj.counterCount .steam == 1))

#guard (earlyPrintingCardId? "ARC015").map (·.val) == some "ARC_015_Y"
#guard pourTheMoldCostScenario "ARC_015_Y" 1 == some true
#guard (earlyPrintingCardId? "ARC016").map (·.val) == some "ARC_016_B"
#guard pourTheMoldCostScenario "ARC_016_B" 2 == some true

#guard ((earlyPrintingCardId? "ARC017").bind throughArcDB.find?).any
  (fun card => card.front.name == "Aether Sink" && card.status == .full)

meta def aetherSinkScenario : Option Bool := do
  let p := earlyAttacker
  let hand := Zone.player p .hand
  let arena := Zone.player p .permanent
  let damage (name : String) (amount : Int) : CardDef :=
    { id := ⟨name⟩
      front :=
        { name
          types := [.instant]
          cost := some {}
          playEffect := some { body := .prim (.dealDamage .arcane .controller (.const amount)) } } }
  let large := damage "Aether Sink damage 5 fixture" 5
  let small := damage "Aether Sink damage 1 fixture" 1
  let cards : CardDB := ⟨large :: small :: throughArcDB.cards⟩
  let (base, potion) ← earlyPlace { earlyBase with cards } p arena "WTR_170_B"
  let (withBig, bigDamage) ← earlyPlace base p hand large.id.val
  let (withSmall, smallDamage) ← earlyPlace withBig p hand small.id.val
  let (ready, item) ← earlyPlace withSmall p hand "ARC_017_Y"
  let play (id : ObjId) : List Action := ⟨.player p, .playCard id⟩ :: earlyPass
  let installed ← earlySteps ready (play item)
  let sink ← (installed.zone arena).head?
  let steam (s : GameState) := (s.obj? sink).map (·.counterCount .steam)
  let load : List Action := ⟨.player p, .activateAbility sink 0 none⟩ :: earlyPass
  let activate : Action := ⟨.player p, .activateAbility sink 1 none⟩
  let select (id : Nat) : Action := ⟨.player p, .pickReplacement (some id)⟩
  let loaded ← earlySteps installed load
  let announced ← earlySteps loaded [activate]
  let used ← earlySteps announced earlyPass
  let reloaded ← earlySteps used load
  let twice ← earlySteps reloaded (activate :: earlyPass)
  let offered ← earlySteps twice (play bigDamage)
  let .chooseReplacement _ .prevention [first, second] true :: _ := offered.pending | none
  let firstPaid ← earlySteps offered [select first]
  let .chooseReplacement _ .prevention [remaining] true :: _ := firstPaid.pending | none
  let prevented ← earlySteps firstPaid [select second]
  let minorHit ← earlySteps twice (play smallDamage)
  let .chooseReplacement _ .prevention [minorBarrier, _] true :: _ := minorHit.pending | none
  let minorPaid ← earlySteps minorHit [select minorBarrier]
  let (expired, _) ← (advance 64 { twice with pending := [.endTurnCleanup p] } []).toOption
  pure (steam installed == some 1 && steam loaded == some 1 &&
    (loaded.poolOf p).resources + 1 == (installed.poolOf p).resources &&
    steam announced == some 0 && (arcaneBarrierEffects announced p).isEmpty &&
    (earlySteps used [activate]).isNone && steam reloaded == some 1 &&
    steam twice == some 0 && first != second && remaining == second &&
    (arcaneBarrierEffects twice p).map (·.source) == [sink, sink] &&
    (twice.characteristics potion).all (fun c => !c.keywords.contains (.arcaneBarrier 2)) &&
    (earlySteps firstPaid [select first]).isNone &&
    prevented.lifeOf p + 1 == twice.lifeOf p &&
    (prevented.poolOf p).resources + 4 == (twice.poolOf p).resources &&
    minorPaid.lifeOf p == twice.lifeOf p &&
    (minorPaid.poolOf p).resources + 2 == (twice.poolOf p).resources &&
    (arcaneBarrierEffects expired p).isEmpty)

#guard aetherSinkScenario == some true

#guard ((earlyPrintingCardId? "ARC018").bind throughArcDB.find?).any
  (fun card => card.front.name == "Cognition Nodes" && card.status == .full)

meta def cognitionNodesScenario (blocked : Bool) : Option Bool := do
  let p := earlyAttacker
  let q := earlyDefender
  let hand := Zone.player p .hand
  let deck := Zone.player p .deck
  let arena := Zone.player p .permanent
  let getLink (s : GameState) := s.combat.bind CombatChain.activeLink?
  let (equipped, weapon) ← earlyPlace { earlyBase with cards := throughArcDB } p
    (.player p .weapon) "WTR_078"
  let (withDeck, top) ← earlyPlace equipped p deck "WTR_191_R"
  let (withJab, jab) ← earlyPlace withDeck p hand "WTR_100_B"
  let (withBlock, blocker) ← earlyPlace withJab q (.player q .hand) "WTR_100_B"
  let (ready, item) ← earlyPlace withBlock p hand "ARC_018_B"
  let installed ← earlySteps ready (⟨.player p, .playCard item⟩ :: earlyPass)
  let nodes ← (installed.zone arena).head?
  let steam (s : GameState) := (s.obj? nodes).map (·.counterCount .steam)
  let reaction (s : GameState) (attack : ActionKind) (blocks : List Action) :=
    (earlyAttack s attack).bind (earlySteps · (blocks ++ (⟨.player q, .defendDone⟩ :: earlyPass)))
  let use (target : ObjId) : Action := ⟨.player p, .activateAbility nodes 1 (some target)⟩
  let unloaded ← reaction installed (.playCard jab) []
  let unloadedTarget ← (getLink unloaded).bind (·.attack)
  let loaded ← earlySteps installed (⟨.player p, .activateAbility nodes 0 none⟩ :: earlyPass)
  let withWeapon ← reaction loaded (.attackWeapon weapon) []
  let weaponTarget ← (getLink withWeapon).bind (·.attack)
  let blocks := if blocked then [⟨.player q, .defendCard blocker⟩] else []
  let fighting ← reaction loaded (.playCard jab) blocks
  let link ← getLink fighting
  let target ← link.attack
  let paid ← earlySteps fighting [use target]
  let armed ← earlySteps paid earlyPass
  let damage ← earlySteps armed earlyPass
  let moved ← if blocked then some damage else do
    let trigger ← damage.pendingTriggers.head?
    earlySteps damage
      ([⟨.player p, .pickTriggerStart p⟩, ⟨.player p, .pickTrigger trigger.id⟩] ++ earlyPass)
  let resolved ← earlySteps moved earlyPass
  let resolvedLink ← getLink resolved
  pure (steam installed == some 0 && steam loaded == some 1 && steam paid == some 0 &&
    (earlySteps unloaded [use unloadedTarget]).isNone && (earlySteps withWeapon [use weaponTarget]).isNone &&
    (grantedAttackAbilities armed target).length == 1 &&
    damage.pendingTriggers.length == (if blocked then 0 else 1) &&
    resolvedLink.hit == !blocked && resolvedLink.linkId == link.linkId &&
    (resolved.poolOf p).actionPoints == (fighting.poolOf p).actionPoints + 1 &&
    if blocked then resolved.zone deck == [top] && (resolved.zone .combatChain).contains target
    else resolved.locate target == none &&
      (resolved.zone deck).map (fun id => (resolved.cardDefOf? id).map (·.id.val)) ==
        [some "WTR_191_R", some "WTR_100_B"])

#guard cognitionNodesScenario false == some true
#guard cognitionNodesScenario true == some true

#guard ((earlyPrintingCardId? "ARC019").bind throughArcDB.find?).any
  (fun card => card.front.name == "Convection Amplifier" && card.status == .full)

meta def convectionAmplifierScenario : Option Bool := do
  let p := earlyAttacker
  let hand := Zone.player p .hand
  let arena := Zone.player p .permanent
  let graveyard := Zone.player p .graveyard
  let getLink (s : GameState) := s.combat.bind CombatChain.activeLink?
  let (equipped, pistol) ← earlyPlace { earlyBase with cards := throughArcDB } p (.player p .weapon) "ARC_003"
  let (withAttack, jab) ← earlyPlace equipped p hand "WTR_100_B"
  let (withSecondAttack, laterJab) ← earlyPlace withAttack p hand "WTR_100_B"
  let (ready, item) ← earlyPlace withSecondAttack p hand "ARC_019_R"
  let installed ← earlySteps ready (⟨.player p, .playCard item⟩ :: earlyPass)
  let amplifier ← (installed.zone arena).head?
  let steam (s : GameState) := (s.obj? amplifier).map (·.counterCount .steam)
  let use : Action := ⟨.player p, .activateAbility amplifier 1 none⟩
  let first ← earlySteps installed (use :: earlyPass)
  let loaded ← earlySteps first (⟨.player p, .activateAbility pistol 1 none⟩ :: earlyPass)
  let weapon ← earlyAttack loaded (.attackWeapon pistol)
  let weaponLink ← getLink weapon
  let weaponHit ← earlyDamage weapon
  let weaponResolved ← earlySteps weaponHit earlyPass
  let closed ← earlySteps weaponResolved earlyPass
  let paid ← earlySteps closed [use]
  let destroy ← paid.pendingTriggers.head?
  let destroyed ← earlySteps paid
    ([⟨.player p, .pickTriggerStart p⟩, ⟨.player p, .pickTrigger destroy.id⟩] ++ earlyPass)
  let buffed ← earlySteps destroyed earlyPass
  let discard ← (buffed.zone graveyard).head?
  let attack ← earlyAttack buffed (.playCard jab)
  let link ← getLink attack
  let hit ← earlyDamage attack
  let later ← (earlySteps hit earlyPass).bind (earlyAttack · (.playCard laterJab))
  let laterLink ← getLink later
  pure (steam installed == some 2 && steam first == some 1 &&
    (first.poolOf p).actionPoints == (installed.poolOf p).actionPoints &&
    !linkHasKeyword weapon weaponLink .dominate &&
    (earlySteps weaponResolved [use]).isNone && closed.combat.isNone &&
    steam paid == some 0 && destroy.source == amplifier &&
    buffed.zone arena == [] &&
    (buffed.cardDefOf? discard).any (fun card => card.id == ⟨"ARC_019_R"⟩) &&
    linkHasKeyword attack link .dominate && !linkHasKeyword later laterLink .dominate)

#guard convectionAmplifierScenario == some true

meta def overLoopScenario (cardId : String) (power : Int) (blocked : Bool) : Option Bool := do
  let p := earlyAttacker
  let q := earlyDefender
  let deck := Zone.player p .deck
  let hand := Zone.player p .hand
  let getLink (s : GameState) := s.combat.bind CombatChain.activeLink?
  let (bottom, marker) ← earlyPlace { earlyBase with cards := throughArcDB } p deck "WTR_191_R"
  let (withBoost, _) ← earlyPlace bottom p deck "ARC_007_B"
  let (withBlock, first) ← earlyPlace withBoost q (.player q .hand) "WTR_188_R"
  let (withTwoBlocks, second) ← earlyPlace withBlock q (.player q .hand) "WTR_188_R"
  let (ready, attack) ← earlyPlace withTwoBlocks p hand cardId
  let attacking ← earlySteps ready
    ([⟨.player p, .playCard attack⟩, ⟨.player p, .pickMay true⟩] ++ earlyPass ++ earlyPass)
  let link ← getLink attacking
  let attackOnChain ← link.attack
  let blocks : List Action := if blocked then
    [⟨.player q, .defendCard first⟩, ⟨.player q, .defendCard second⟩] else []
  let damage ← (earlySteps attacking blocks).bind earlyDamage
  let settled ← if blocked then some damage else do
    let trigger ← damage.pendingTriggers.head?
    earlySteps damage
      ([⟨.player p, .pickTriggerStart p⟩, ⟨.player p, .pickTrigger trigger.id⟩] ++ earlyPass)
  let resolved ← earlySteps settled earlyPass
  let endingLink ← getLink resolved
  pure (linkAttackPower attacking link == power && linkHasKeyword attacking link .goAgain &&
    attacking.zone deck == [marker] && damage.pendingTriggers.length == (if blocked then 0 else 1) &&
    endingLink.linkId == link.linkId && endingLink.hit == !blocked &&
    (resolved.poolOf p).actionPoints == (ready.poolOf p).actionPoints &&
    if blocked then resolved.zone deck == [marker] && (resolved.zone .combatChain).contains attackOnChain
    else resolved.locate attackOnChain == none &&
      (resolved.zone deck).map (fun id => (resolved.cardDefOf? id).map (·.id.val)) ==
        [some "WTR_191_R", some cardId])

#guard (earlyPrintingCardId? "ARC020").map (·.val) == some "ARC_020_R"
#guard ["LGS013", "LGS013-P"].all fun number =>
  ((earlyPrintingCardId? number).bind throughArcDB.find?).any
    (fun card => card.id == ⟨"ARC_020_R"⟩ && card.status == .full)
#guard overLoopScenario "ARC_020_R" 5 false == some true
#guard overLoopScenario "ARC_020_R" 5 true == some true

#guard (earlyPrintingCardId? "ARC021").map (·.val) == some "ARC_021_Y"
#guard overLoopScenario "ARC_021_Y" 4 false == some true
#guard overLoopScenario "ARC_021_Y" 4 true == some true

#guard (earlyPrintingCardId? "ARC022").map (·.val) == some "ARC_022_B"
#guard overLoopScenario "ARC_022_B" 3 false == some true
#guard overLoopScenario "ARC_022_B" 3 true == some true

#guard
  (["HER001-P", "HER002-P", "HER003-P", "HER004-P"].map fun number =>
    ((earlyPrintingCardId? number).bind throughWtrDB.find?).map (·.front.name)) ==
  ["Rhinar, Reckless Rampage", "Bravo, Showstopper", "Katsu, the Wanderer", "Dorinthea Ironsong"].map some
