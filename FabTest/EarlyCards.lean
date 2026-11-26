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

meta def boostOnlyArcAttackScenario (cardId : String) (power : Int) (cost pitch : Nat) :
    Option Bool := do
  let p := earlyAttacker
  let deck := Zone.player p .deck
  let banished := Zone.player p .banished
  let card ← throughArcDB.find? ⟨cardId⟩
  let (base, attack) ← earlyPlace { earlyBase with cards := throughArcDB } p (.player p .hand) cardId
  let attempt (topCard : String) (boost gainsGoAgain : Bool) : Option Bool := do
    let (ready, top) ← earlyPlace base p deck topCard
    let paid ← earlySteps ready
      [⟨.player p, .playCard attack⟩, ⟨.player p, .pickMay boost⟩]
    let attacking ← earlySteps paid (earlyPass ++ earlyPass)
    let link ← attacking.combat.bind CombatChain.activeLink?
    let hit ← earlyDamage attacking
    let resolved ← earlySteps hit earlyPass
    let removed := (paid.zone banished).map (fun id => (paid.cardDefOf? id).map (·.id.val))
    let expectedAP := (ready.poolOf p).actionPoints - (if gainsGoAgain then 0 else 1)
    pure ((paid.poolOf p).resources + cost == (ready.poolOf p).resources &&
      paid.zone deck == (if boost then [] else [top]) &&
      removed == (if boost then [some topCard] else []) &&
      paid.boostsThisTurn == (if boost then [p] else []) &&
      linkAttackPower attacking link == power && linkHasKeyword attacking link .goAgain == gainsGoAgain &&
      hit.pendingTriggers.isEmpty && (resolved.poolOf p).actionPoints == expectedAP)
  let matched ← attempt "ARC_007_B" true true
  let otherClass ← attempt "WTR_191_R" true false
  let declined ← attempt "ARC_007_B" false false
  pure (card.status == .full && card.front.pitch == some pitch && card.front.defense == some 3 &&
    card.front.keywords == [.boost] && card.front.abilities.isEmpty && card.front.playEffect.isNone &&
    matched && otherClass && declined)

#guard (earlyPrintingCardId? "ARC023").map (·.val) == some "ARC_023_R"
#guard boostOnlyArcAttackScenario "ARC_023_R" 6 2 1 == some true

#guard (earlyPrintingCardId? "ARC024").map (·.val) == some "ARC_024_Y"
#guard boostOnlyArcAttackScenario "ARC_024_Y" 5 2 2 == some true

#guard (earlyPrintingCardId? "ARC025").map (·.val) == some "ARC_025_B"
#guard boostOnlyArcAttackScenario "ARC_025_B" 4 2 3 == some true

#guard (earlyPrintingCardId? "ARC026").map (·.val) == some "ARC_026_R"
#guard boostOnlyArcAttackScenario "ARC_026_R" 4 0 1 == some true

#guard (earlyPrintingCardId? "ARC027").map (·.val) == some "ARC_027_Y"
#guard boostOnlyArcAttackScenario "ARC_027_Y" 3 0 2 == some true

#guard (earlyPrintingCardId? "ARC028").map (·.val) == some "ARC_028_B"
#guard boostOnlyArcAttackScenario "ARC_028_B" 2 0 3 == some true

#guard (earlyPrintingCardId? "ARC029").map (·.val) == some "ARC_029_R"
#guard boostOnlyArcAttackScenario "ARC_029_R" 5 1 1 == some true

#guard (earlyPrintingCardId? "ARC030").map (·.val) == some "ARC_030_Y"
#guard boostOnlyArcAttackScenario "ARC_030_Y" 4 1 2 == some true

#guard (earlyPrintingCardId? "ARC031").map (·.val) == some "ARC_031_B"
#guard boostOnlyArcAttackScenario "ARC_031_B" 3 1 3 == some true

meta def lockedAndLoadedScenario (cardId : String) (bonus : Int) (boosted : Bool) : Option Bool := do
  let p := earlyAttacker
  let q := earlyDefender
  let hand := Zone.player p .hand
  let deck := Zone.player p .deck
  let getLink (s : GameState) := s.combat.bind CombatChain.activeLink?
  let base := { earlyBase with cards := throughArcDB, boostsThisTurn := [if boosted then p else q] }
  let (bottom, bottomCard) ← earlyPlace base p deck "WTR_203_R"
  let (withDeck, topCard) ← earlyPlace bottom p deck "ARC_007_B"
  let (withJab, jab) ← earlyPlace withDeck p hand "WTR_100_B"
  let (withAttack, attack) ← earlyPlace withJab p hand "ARC_020_R"
  let (ready, action) ← earlyPlace withAttack p hand cardId
  let cast ← earlySteps ready (⟨.player p, .playCard action⟩ :: earlyPass)
  let canOpt := match cast.pending with
    | .chooseOpt player top _ _ _ :: _ => player == p && top == topCard
    | _ => false
  let resolved ← if boosted then earlySteps cast [⟨.player p, .optPick false none⟩] else some cast
  let first ← earlyAttack resolved (.playCard jab)
  let jabLink ← getLink first
  let jabHit ← earlyDamage first
  let finished ← earlySteps jabHit earlyPass
  let buffed ← earlySteps finished
    ([⟨.player p, .playCard attack⟩, ⟨.player p, .pickMay false⟩] ++ earlyPass ++ earlyPass)
  let attackLink ← getLink buffed
  pure (canOpt == boosted && resolved.zone deck == (if boosted then [bottomCard, topCard] else [topCard, bottomCard]) &&
    (resolved.poolOf p).actionPoints == (ready.poolOf p).actionPoints &&
    (resolved.poolOf p).resources == (ready.poolOf p).resources &&
    linkAttackPower first jabLink == 1 && first.activeEffects.length == 1 &&
    linkAttackPower buffed attackLink == 5 + bonus && buffed.activeEffects.isEmpty)

#guard (earlyPrintingCardId? "ARC032").map (·.val) == some "ARC_032_R"
#guard lockedAndLoadedScenario "ARC_032_R" 3 false == some true
#guard lockedAndLoadedScenario "ARC_032_R" 3 true == some true

#guard (earlyPrintingCardId? "ARC033").map (·.val) == some "ARC_033_Y"
#guard lockedAndLoadedScenario "ARC_033_Y" 2 false == some true
#guard lockedAndLoadedScenario "ARC_033_Y" 2 true == some true

#guard (earlyPrintingCardId? "ARC034").map (·.val) == some "ARC_034_B"
#guard lockedAndLoadedScenario "ARC_034_B" 1 false == some true
#guard lockedAndLoadedScenario "ARC_034_B" 1 true == some true

#guard ((earlyPrintingCardId? "ARC035").bind throughArcDB.find?).any
  (fun card => card.front.name == "Dissipation Shield" && card.status == .full)

meta def dissipationShieldScenario : Option Bool := do
  let p := earlyAttacker
  let arena := Zone.player p .permanent
  let graveyard := Zone.player p .graveyard
  let (ready, card) ← earlyPlace { earlyBase with cards := throughArcDB } p (.player p .hand) "ARC_035_Y"
  let installed ← earlySteps ready (⟨.player p, .playCard card⟩ :: earlyPass)
  let shield ← (installed.zone arena).head?
  let counters (s : GameState) := (s.obj? shield).map (·.counterCount .steam)
  let start (s : GameState) := ((advance 64 { s with pending := [.actionPhaseStart p] } []).toOption).map Prod.fst
  let resolveStart (s : GameState) := do
    let trigger ← s.pendingTriggers.head?
    earlySteps s ([⟨.player p, .pickTriggerStart p⟩, ⟨.player p, .pickTrigger trigger.id⟩] ++ earlyPass)
  let atStart ← start installed
  let choice ← resolveStart atStart
  let kept ← earlySteps choice [⟨.player p, .pickMode 0⟩]
  let declined ← earlySteps choice [⟨.player p, .pickMode 1⟩]
  let empty := updateSingleObject installed shield (fun obj => obj.clearCounterVal .steam)
  let emptyStart ← start empty
  let lost ← resolveStart emptyStart
  let (paid, events) ← (step 64 kept ⟨.player p, .activateAbility shield 1 none⟩).toOption
  let discarded ← (paid.zone graveyard).head?
  let shieldActive ← earlySteps paid earlyPass
  let fixed ← shieldActive.activeReplacements.head?
  let hit (s : GameState) (kind : DamageKind) (amount : Int) :=
    execPrim s p shield [] (.dealDamage kind .controller (.const amount))
  let (spent, firstEvents, firstFrames) := hit shieldActive .physical 1
  let (nextHit, _, _) := hit spent .arcane 4
  let (largeHit, _, _) := hit shieldActive .arcane 5
  let (afterLifeLoss, _, _) := execPrim shieldActive p shield [] (.loseLife .controller (.const 1))
  let (expired, _) ← (advance 64 { shieldActive with pending := [.endTurnCleanup p] } []).toOption
  pure (counters installed == some 4 && counters kept == some 3 &&
    declined.zone arena == [] && lost.zone arena == [] &&
    paid.zone arena == [] && events.contains (.moved shield discarded arena graveyard) &&
    paid.activeReplacements.isEmpty && fixed.source == shield && fixed.action == .fixedPrevent 3 &&
    firstEvents.isEmpty && firstFrames.isEmpty && spent.lifeOf p == shieldActive.lifeOf p &&
    spent.activeReplacements.isEmpty && nextHit.lifeOf p == shieldActive.lifeOf p - 4 &&
    largeHit.lifeOf p == shieldActive.lifeOf p - 2 && largeHit.activeReplacements.isEmpty &&
    afterLifeLoss.lifeOf p == shieldActive.lifeOf p - 1 && afterLifeLoss.activeReplacements == [fixed] &&
    expired.activeReplacements.isEmpty)

#guard dissipationShieldScenario == some true

meta def fixedPreventionCombatScenario : Option Bool := do
  let p := earlyAttacker
  let q := earlyDefender
  let fixed : ReplacementEffect :=
    { id := 100, source := ⟨0⟩, controller := q, stage := .prevention, action := .fixedPrevent 3 }
  let shielded : ReplacementEffect := { fixed with id := 101, action := .shieldPrevent 5 }
  let board := { earlyBase with
    cards := throughArcDB, activeReplacements := [fixed, shielded] }
  let (ready, card) ← earlyPlace board p (.player p .hand) "WTR_100_B"
  let attack ← earlyAttack ready (.playCard card)
  let oldLink ← attack.combat.bind CombatChain.activeLink?
  let prompt ← earlyDamage attack
  let .chooseReplacement chooser .prevention [first, second] false :: _ := prompt.pending | none
  let choose (id : Nat) : Action := ⟨.player q, .pickReplacement (some id)⟩
  let fixedFirst ← earlySteps prompt [choose first]
  let shieldFirst ← earlySteps prompt [choose second]
  let newLink ← fixedFirst.combat.bind CombatChain.activeLink?
  let otherLink ← shieldFirst.combat.bind CombatChain.activeLink?
  let resolved ← earlySteps fixedFirst earlyPass
  pure (chooser == q && first == fixed.id && second == shielded.id &&
    fixedFirst.lifeOf q == ready.lifeOf q && shieldFirst.lifeOf q == ready.lifeOf q &&
    fixedFirst.activeReplacements == [shielded] &&
    shieldFirst.activeReplacements == [fixed, { shielded with action := .shieldPrevent 4 }] &&
    newLink.linkId == oldLink.linkId && otherLink.linkId == oldLink.linkId &&
    !newLink.hit && !otherLink.hit && newLink.damageDealt == 0 && otherLink.damageDealt == 0 &&
    (resolved.poolOf p).actionPoints == (ready.poolOf p).actionPoints)

#guard fixedPreventionCombatScenario == some true

meta def fixedPreventionDirectDamageScenario (kind : DamageKind) : Option Bool := do
  let p := earlyAttacker
  let fixed : ReplacementEffect :=
    { id := 100, source := ⟨0⟩, controller := p, stage := .prevention, action := .fixedPrevent 3 }
  let shielded : ReplacementEffect := { fixed with id := 101, action := .shieldPrevent 5 }
  let board := { earlyBase with activeReplacements := [fixed, shielded] }
  let (initial, _, frames) := execPrim board p ⟨0⟩ [] (.dealDamage kind .controller (.const 1))
  let (prompt, _) ← (advance 64 { initial with pending := frames } []).toOption
  let .chooseReplacement chooser .prevention [first, second] false :: _ := prompt.pending | none
  let fixedFirst ← earlySteps prompt [⟨.player p, .pickReplacement (some first)⟩]
  let shieldFirst ← earlySteps prompt [⟨.player p, .pickReplacement (some second)⟩]
  pure (chooser == p && first == fixed.id && second == shielded.id &&
    fixedFirst.lifeOf p == board.lifeOf p && shieldFirst.lifeOf p == board.lifeOf p &&
    fixedFirst.activeReplacements == [shielded] &&
    shieldFirst.activeReplacements == [fixed, { shielded with action := .shieldPrevent 4 }])

#guard fixedPreventionDirectDamageScenario .physical == some true
#guard fixedPreventionDirectDamageScenario .arcane == some true

#guard ((earlyPrintingCardId? "ARC036").bind throughArcDB.find?).any
  (fun card => card.front.name == "Hyper Driver" && card.status == .full)

meta def hyperDriverScenario : Option Bool := do
  let p := earlyAttacker
  let hand := Zone.player p .hand
  let arena := Zone.player p .permanent
  let deck := Zone.player p .deck
  let reserve := ["ARC_007_B", "ARC_007_B", "ARC_007_B", "WTR_191_R"]
  let withDeck ← reserve.foldlM
    (fun s id => (earlyPlace s p deck id).map Prod.fst) { earlyBase with cards := throughArcDB }
  let (withFirst, first) ← earlyPlace withDeck p hand "ARC_026_R"
  let (withSecond, second) ← earlyPlace withFirst p hand "ARC_026_R"
  let (withThird, third) ← earlyPlace withSecond p hand "ARC_026_R"
  let (withFourth, fourth) ← earlyPlace withThird p hand "ARC_026_R"
  let (ready, item) ← earlyPlace withFourth p hand "ARC_036_R"
  let installed ← earlySteps ready (⟨.player p, .playCard item⟩ :: earlyPass)
  let driver ← (installed.zone arena).head?
  let steam (s : GameState) := (s.obj? driver).map (·.counterCount .steam)
  let attack (id : ObjId) (s : GameState) :=
    earlySteps s [⟨.player p, .playCard id⟩, ⟨.player p, .pickMay true⟩]
  let resolveTrigger (s : GameState) := do
    let trigger ← s.pendingTriggers.head?
    earlySteps s ([⟨.player p, .pickTriggerStart p⟩, ⟨.player p, .pickTrigger trigger.id⟩] ++ earlyPass)
  let close (s : GameState) := do
    let attacking ← earlySteps s (earlyPass ++ earlyPass)
    let hit ← earlyDamage attacking
    earlySteps hit (earlyPass ++ earlyPass)
  let nextTurn (s : GameState) := do
    let (ended, _) ← microStep { s with pending := [.endTurnCleanup p] }
    return { ended.setPool p { actionPoints := 4 } with
      turn := s.turn + 2, pending := [.priority p 0], active := some p }
  let skipped ← earlySteps installed [⟨.player p, .playCard first⟩, ⟨.player p, .pickMay false⟩]
  let firstPaid ← attack first installed
  let firstUsed ← resolveTrigger firstPaid
  let firstClosed ← close firstUsed
  let secondPaid ← attack second firstClosed
  let secondClosed ← close secondPaid
  let thirdPaid ← (nextTurn secondClosed).bind (attack third)
  let thirdUsed ← resolveTrigger thirdPaid
  let thirdClosed ← close thirdUsed
  let fourthPaid ← (nextTurn thirdClosed).bind (attack fourth)
  let empty ← resolveTrigger fourthPaid
  let destroyed ← resolveTrigger empty
  let firstBanished ← (firstPaid.zone (.player p .banished)).head?
  pure (steam installed == some 3 && skipped.pendingTriggers.isEmpty && skipped.boostsThisTurn.isEmpty &&
    steam skipped == some 3 && firstPaid.pendingTriggers.length == 1 &&
    (firstPaid.cardDefOf? firstBanished).any (fun c => c.id == ⟨"WTR_191_R"⟩) &&
    steam firstUsed == some 2 && (firstUsed.poolOf p).resources == (installed.poolOf p).resources + 1 &&
    secondPaid.pendingTriggers.isEmpty && steam secondPaid == some 2 &&
    (secondPaid.poolOf p).resources == (firstUsed.poolOf p).resources &&
    steam thirdUsed == some 1 && (thirdUsed.poolOf p).resources == 1 &&
    steam empty == some 0 && empty.pendingTriggers.length == 1 &&
    (empty.poolOf p).resources == 1 && destroyed.zone arena == [])

#guard hyperDriverScenario == some true

#guard ((earlyPrintingCardId? "ARC037").bind throughArcDB.find?).any
  (fun card => card.front.name == "Optekal Monocle" && card.status == .full)

meta def optekalMonocleScenario : Option Bool := do
  let p := earlyAttacker
  let arena := Zone.player p .permanent
  let deck := Zone.player p .deck
  let (withBottom, bottom) ← earlyPlace { earlyBase with cards := throughArcDB } p deck "WTR_100_B"
  let (withTop, top) ← earlyPlace withBottom p deck "ARC_007_B"
  let (ready, item) ← earlyPlace withTop p (.player p .hand) "ARC_037_B"
  let installed ← earlySteps ready (⟨.player p, .playCard item⟩ :: earlyPass)
  let monocle ← (installed.zone arena).head?
  let steam (s : GameState) := (s.obj? monocle).map (·.counterCount .steam)
  let activate : Action := ⟨.player p, .activateAbility monocle 1 none⟩
  let keep : Action := ⟨.player p, .optPick true none⟩
  let stepOpt (s : GameState) := earlySteps s (activate :: (earlyPass ++ [keep]))
  let one ← ([0, 1, 2, 3] : List Nat).foldlM (fun s _ => stepOpt s) installed
  let paid ← earlySteps one [activate]
  let destruction ← paid.pendingTriggers.head?
  let destroyed ← earlySteps paid
    ([⟨.player p, .pickTriggerStart p⟩, ⟨.player p, .pickTrigger destruction.id⟩] ++ earlyPass)
  let opting ← earlySteps destroyed earlyPass
  let .chooseOpt chooser viewed _ _ _ :: _ := opting.pending | none
  let resolved ← earlySteps opting [⟨.player p, .optPick false none⟩]
  pure (steam installed == some 5 && steam one == some 1 && steam paid == some 0 &&
    destruction.source == monocle && destruction.effect == .prim (.destroy .self_) &&
    destroyed.zone arena == [] && opting.zone deck == [top, bottom] &&
    chooser == p && viewed == top && resolved.zone deck == [bottom, top] &&
    (one.poolOf p).actionPoints == (installed.poolOf p).actionPoints &&
    (resolved.poolOf p) == (installed.poolOf p) &&
    (earlySteps resolved [activate]).isNone)

#guard optekalMonocleScenario == some true

#guard ((earlyPrintingCardId? "ARC038").bind throughArcDB.find?).any
  (fun card => card.front.name == "Azalea, Ace in the Hole" && card.status == .full)

meta def azaleaScenario (heroId : String) (arrowTop : Bool) : Option Bool := do
  let p := earlyAttacker
  let deck := Zone.player p .deck
  let arsenal := Zone.player p .arsenal
  let hand := Zone.player p .hand
  let arrow := FabCards.ARC.Meta.ARC_043_R_meta
  let bow := FabCards.ARC.Meta.ARC_040_meta
  let db : CardDB := ⟨arrow :: bow :: throughArcDB.cards⟩
  let state := { earlyBase with cards := db }
  let (withHero, hero) ← earlyPlace state p (.player p .hero) heroId
  let (withBow, _) ← earlyPlace withHero p (.player p .weapon) bow.id.val
  let (withHand, handArrow) ← earlyPlace withBow p hand arrow.id.val
  let (withBottom, originalBottom) ← earlyPlace withHand p deck "WTR_191_R"
  let topCard := if arrowTop then arrow.id else ⟨"WTR_192_Y"⟩
  let (ready, originalTop) ← earlyPlace withBottom p deck topCard.val
  let (withArsenal, storedId) ← addObject ready arsenal
    { kind := .card ⟨ready.nextId⟩ ⟨"WTR_193_B"⟩, owner := p, controller := p,
      timestamp := ⟨0⟩, faceDown := true } .top
  let use : Action := ⟨.player p, .activateAbility hero 0 none⟩
  let empty ← earlySteps ready (use :: earlyPass)
  let rotated ← earlySteps withArsenal (use :: earlyPass)
  let freshId ← (rotated.zone arsenal).head?
  let movedBottom ← (rotated.zone deck).getLast?
  let stats ← rotated.characteristics freshId
  let expired := rotated.finishTurnEffects
  let canPlay := canPlayCard rotated p freshId
  let attackOk ← if arrowTop then do
      let attacking ← earlyAttack rotated (.playCard freshId)
      let link ← attacking.combat.bind CombatChain.activeLink?
      let (withoutLoaded, _) ← moveObj rotated freshId (.player p .graveyard)
      let (withOther, other) ← moveObj withoutLoaded handArrow arsenal
      let otherAttacking ← earlyAttack withOther (.playCard other)
      let otherLink ← otherAttacking.combat.bind CombatChain.activeLink?
      pure (canPlay && linkHasKeyword attacking link .dominate &&
        !linkHasKeyword otherAttacking otherLink .dominate &&
        !canPlayCard (rotated.setZone (.player p .weapon) []) p freshId)
    else pure canPlay
  pure (empty.zone deck == [originalTop, originalBottom] && empty.zone arsenal == [] &&
    !canPlayCard rotated p handArrow && (rotated.zone deck).head? == some originalBottom &&
    (rotated.cardDefOf? movedBottom).any (·.id == ⟨"WTR_193_B"⟩) &&
    (rotated.cardDefOf? freshId).any (·.id == topCard) && movedBottom != storedId &&
    freshId != originalTop && (rotated.obj? freshId).any (fun card => !card.faceDown) &&
    stats.keywords.contains .dominate == arrowTop && expired.activeEffects.isEmpty &&
    (rotated.poolOf p).actionPoints == (withArsenal.poolOf p).actionPoints &&
    !((step 64 rotated use).isOk) && attackOk)

#guard azaleaScenario "ARC_038" true == some true
#guard azaleaScenario "ARC_038" false == some true

#guard ((earlyPrintingCardId? "ARC039").bind throughArcDB.find?).any
  (fun card => card.front.name == "Azalea" && card.front.life == some 20 &&
    card.front.hasSubtype .young && card.status == .full)

#guard ["HER018", "HER018-P"].all
  (fun printing => earlyPrintingCardId? printing == some ⟨"ARC_038"⟩)
#guard ["HER014", "HER014-P"].all
  (fun printing => earlyPrintingCardId? printing == some ⟨"ARC_039"⟩)

#guard azaleaScenario "ARC_039" true == some true
#guard azaleaScenario "ARC_039" false == some true

#guard ((earlyPrintingCardId? "ARC040").bind throughArcDB.find?).any
  (fun card => card.front.name == "Death Dealer" && card.front.hasSubtype .bow && card.status == .full)

meta def deathDealerScenario : Option Bool := do
  let p := earlyAttacker
  let hand := Zone.player p .hand
  let arsenal := Zone.player p .arsenal
  let deck := Zone.player p .deck
  let arrow := FabCards.ARC.Meta.ARC_043_R_meta
  let state := { earlyBase with cards := ⟨arrow :: throughArcDB.cards⟩ }
  let (withBow, bow) ← earlyPlace state p (.player p .weapon) "ARC_040"
  let (withDeck, _) ← earlyPlace withBow p deck "WTR_192_Y"
  let (ordinaryHand, other) ← earlyPlace withDeck p hand "WTR_191_R"
  let (ready, arrowId) ← earlyPlace ordinaryHand p hand arrow.id.val
  let use : Action := ⟨.player p, .activateAbility bow 0 none⟩
  let pick (id : Option ObjId) : Action := ⟨.player p, .pickShuffleCard id⟩
  let choosing ← earlySteps ready (use :: earlyPass)
  let .chooseShuffleCards chooser 1 [candidate] [] true (some selection) :: _ := choosing.pending
    | none
  let loaded ← earlySteps choosing [pick (some arrowId), pick none]
  let declined ← earlySteps choosing [pick none]
  let (alreadyLoaded, old) ← earlyPlace ready p arsenal "WTR_193_B"
  let blocked ← earlySteps alreadyLoaded (use :: earlyPass)
  let noArrow ← earlySteps ordinaryHand (use :: (earlyPass ++ [pick none]))
  let loadedId ← (loaded.zone arsenal).head?
  let handIds := (loaded.zone hand).filterMap (fun id => (loaded.cardDefOf? id).map (·.id))
  pure (chooser == p && candidate == arrowId && !selection.searchesDeck && !selection.shuffleAfter &&
    (earlySteps choosing [pick (some other)]).isNone &&
    (loaded.zone deck).isEmpty && handIds == [⟨"WTR_192_Y"⟩, ⟨"WTR_191_R"⟩] &&
    (loaded.obj? loadedId).any (fun obj => !obj.faceDown) &&
    (loaded.cardDefOf? loadedId).any (fun c => c.id == arrow.id) &&
    (loaded.poolOf p).actionPoints == (ready.poolOf p).actionPoints &&
    (loaded.poolOf p).resources + 1 == (ready.poolOf p).resources &&
    !((step 64 loaded use).isOk) && !canAttackWithWeapon ready p bow &&
    (declined.zone arsenal).isEmpty && declined.zone deck == ready.zone deck &&
    declined.zone hand == ready.zone hand &&
    blocked.zone arsenal == [old] && blocked.zone deck == ready.zone deck &&
    blocked.zone hand == ready.zone hand &&
    (noArrow.zone arsenal).isEmpty && noArrow.zone deck == ready.zone deck &&
    noArrow.zone hand == ordinaryHand.zone hand)

#guard deathDealerScenario == some true

#guard ((earlyPrintingCardId? "ARC041").bind throughArcDB.find?).any
  (fun card => card.front.name == "Skullbone Crosswrap" && card.status == .full &&
    card.front.keywords.contains (.arcaneBarrier 1) && card.front.keywords.contains .bladeBreak)

meta def skullboneCrosswrapScenario : Option Bool := do
  let p := earlyAttacker
  let arsenal := Zone.player p .arsenal
  let deck := Zone.player p .deck
  let state := { earlyBase with cards := throughArcDB }
  let (withHead, head) ← earlyPlace state p (.player p .head) "ARC_041"
  let (withBottom, bottom) ← earlyPlace withHead p deck "WTR_193_B"
  let (empty, top) ← earlyPlace withBottom p deck "WTR_192_Y"
  let (ready, down) ← addObject empty arsenal
    { kind := .card ⟨empty.nextId⟩ ⟨"WTR_191_R"⟩, owner := p, controller := p,
      timestamp := ⟨0⟩, faceDown := true } .top
  let (faceUp, up) ← earlyPlace empty p arsenal "WTR_191_R"
  let use (target : Option ObjId) : Action := ⟨.player p, .activateAbility head 0 target⟩
  let (paid, events) ← (step 64 ready (use (some down))).toOption
  let viewed ← earlySteps paid earlyPass
  let .chooseOpt player viewedId _ _ _ :: _ := viewed.pending | none
  let done ← earlySteps viewed [⟨.player p, .optPick false none⟩]
  pure (viewZone earlyDefender ready arsenal == .entries [some .faceDown] &&
    viewZone earlyDefender paid arsenal != .entries [some .faceDown] &&
    paid.zone arsenal == [down] && (paid.obj? down).any (fun card => !card.faceDown) &&
    events.contains (.revealed p down ⟨"WTR_191_R"⟩) &&
    paid.zone deck == [top, bottom] && player == p && viewedId == top &&
    done.zone deck == [bottom, top] && (done.poolOf p) == (ready.poolOf p) &&
    ((step 64 empty (use none)).isOk == false) &&
    ((step 64 ready (use none)).isOk == false) &&
    ((step 64 faceUp (use (some up))).isOk == false) &&
    !((step 64 done (use (some down))).isOk))

#guard skullboneCrosswrapScenario == some true

#guard ((earlyPrintingCardId? "ARC042").bind throughArcDB.find?).any
  (fun card => card.status == .full && card.front.name == "Bull's Eye Bracers" &&
    card.front.keywords.contains (.arcaneBarrier 1))

meta def bullsEyeBracersScenario : Option Bool := do
  let p := earlyAttacker
  let arsenal := Zone.player p .arsenal
  let hand := Zone.player p .hand
  let deck := Zone.player p .deck
  let equipment := Zone.player p .arms
  let arrow := FabCards.ARC.Meta.ARC_043_R_meta
  let state := { earlyBase with cards := ⟨arrow :: throughArcDB.cards⟩ }
  let (withBow, _) ← earlyPlace state p (.player p .weapon) "ARC_040"
  let (withBracers, bracers) ← earlyPlace withBow p equipment "ARC_042"
  let (withDeck, _) ← earlyPlace withBracers p deck "WTR_193_B"
  let (withOtherArrow, otherArrow) ← earlyPlace withDeck p hand arrow.id.val
  let (ready, arrowId) ← earlyPlace withOtherArrow p hand arrow.id.val
  let use : Action := ⟨.player p, .activateAbility bracers 0 none⟩
  let pick (id : Option ObjId) : Action := ⟨.player p, .pickShuffleCard id⟩
  let paid ← earlySteps ready [use]
  let choosing ← earlySteps paid earlyPass
  let declined ← earlySteps choosing [pick none]
  let loaded ← earlySteps choosing [pick (some arrowId), pick none]
  let loadedId ← (loaded.zone arsenal).head?
  let power (s : GameState) (id : ObjId) := (s.characteristics id).bind (·.power)
  let announced ← earlySteps loaded [⟨.player p, .playCard loadedId⟩]
  let layer ← (announced.zone .stack).head?
  let attacking ← earlySteps announced (earlyPass ++ earlyPass)
  let link ← attacking.combat.bind CombatChain.activeLink?
  let (movedAside, _) ← moveObj loaded loadedId (.player p .graveyard)
  let (otherLoaded, otherId) ← moveObj movedAside otherArrow arsenal
  let otherAttack ← earlyAttack otherLoaded (.playCard otherId)
  let otherLink ← otherAttack.combat.bind CombatChain.activeLink?
  let (occupied, stored) ← earlyPlace ready p arsenal "WTR_191_R"
  let noLoad ← earlySteps occupied (use :: earlyPass)
  pure ((paid.zone equipment).isEmpty &&
    (paid.zone (.player p .graveyard)).any
      (fun id => (paid.cardDefOf? id).any (fun card => card.id == ⟨"ARC_042"⟩)) &&
    (declined.zone arsenal).isEmpty && declined.activeEffects.isEmpty &&
    (loaded.obj? loadedId).any (fun card => !card.faceDown) &&
    loaded.zone hand == [otherArrow] && loaded.zone deck == ready.zone deck &&
    (loaded.poolOf p) == (ready.poolOf p) &&
    power loaded loadedId == some 6 && power loaded.finishTurnEffects loadedId == some 5 &&
    power announced layer == some 6 && linkAttackPower attacking link == 6 &&
    linkAttackPower otherAttack otherLink == 5 &&
    noLoad.zone arsenal == [stored] && (noLoad.zone equipment).isEmpty &&
    noLoad.activeEffects.isEmpty && noLoad.zone hand == ready.zone hand)

#guard bullsEyeBracersScenario == some true

#guard ((earlyPrintingCardId? "ARC043").bind throughArcDB.find?).any
  (fun card => card.front.name == "Red in the Ledger" && card.status == .full)

meta def redInTheLedgerScenario : Option Bool := do
  let p := earlyAttacker
  let q := earlyDefender
  let arsenal := Zone.player p .arsenal
  let hand := Zone.player q .hand
  let base := { earlyBase with cards := throughArcDB }
  let (withBow, _) ← earlyPlace base p (.player p .weapon) "ARC_040"
  let (archer, arrow) ← earlyPlace withBow p arsenal "ARC_043_R"
  let attacking ← earlyAttack archer (.playCard arrow)
  let hit ← earlyDamage attacking
  let trigger ← hit.pendingTriggers.head?
  let applied ← earlySteps hit
    ([⟨.player p, .pickTriggerStart p⟩, ⟨.player p, .pickTrigger trigger.id⟩] ++ earlyPass)
  let closed ← earlySteps applied (earlyPass ++ earlyPass)
  let (withHero, hero) ← earlyPlace closed q (.player q .hero) "ARC_039"
  let (withBlade, blade) ← earlyPlace withHero q (.player q .weapon) "WTR_115"
  let (withFirst, first) ← earlyPlace withBlade q hand "WTR_218_R"
  let (withSecond, second) ← earlyPlace withFirst q hand "WTR_219_Y"
  let (prepared, instant) ← earlyPlace withSecond q hand "WTR_173_R"
  let next := { prepared.setPool q { actionPoints := 3, resources := 8 } with
    turn := prepared.turn + 1, active := some q, pending := [.actionPhaseStart q] }
  let (ready, _) ← microStep next
  let pass : List Action := [⟨.player q, .pass⟩, ⟨.player p, .pass⟩]
  let useHero : Action := ⟨.player q, .activateAbility hero 0 none⟩
  let useWeapon : Action := ⟨.player q, .attackWeapon blade⟩
  let playFirst : Action := ⟨.player q, .playCard first⟩
  let playSecond : Action := ⟨.player q, .playCard second⟩
  let afterCard ← earlySteps ready (playFirst :: pass)
  let afterHero ← earlySteps ready (useHero :: pass)
  let afterWeapon ← earlySteps ready [useWeapon]
  let afterInstant ← earlySteps afterCard (⟨.player q, .playCard instant⟩ :: pass)
  let (ended, _) ← microStep { afterInstant with pending := [.endPhaseStart q] }
  pure (closed.combat.isNone && closed.canTakeAction p &&
    closed.activeEffects.any (fun effect =>
      effect.target == .player q && effect.op == .limitActions 1 && effect.duration == .nextActionPhase) &&
    ready.canTakeAction q && (afterCard.poolOf q).actionPoints == (ready.poolOf q).actionPoints &&
    !afterCard.canTakeAction q && !afterHero.canTakeAction q && !afterWeapon.canTakeAction q &&
    (earlySteps afterCard [playSecond]).isNone && (earlySteps afterCard [useHero]).isNone &&
    (earlySteps afterCard [useWeapon]).isNone && (earlySteps afterHero [playFirst]).isNone &&
    afterInstant.lifeOf q == afterCard.lifeOf q + 3 && !afterInstant.canTakeAction q &&
    ended.activeEffects.all (fun effect => effect.op != .limitActions 0))

#guard redInTheLedgerScenario == some true

#guard ((earlyPrintingCardId? "ARC044").bind throughArcDB.find?).any
  (fun card => card.front.name == "Three of a Kind" && card.status == .full)

meta def threeOfAKindScenario : Option Bool := do
  let p := earlyAttacker
  let q := earlyDefender
  let hand := Zone.player p .hand
  let deck := Zone.player p .deck
  let arsenal := Zone.player p .arsenal
  let state := { earlyBase with cards := throughArcDB }
  let (withHero, hero) ← earlyPlace state p (.player p .hero) "ARC_038"
  let (withWeapon, weapon) ← earlyPlace withHero p (.player p .weapon) "WTR_115"
  let (withSpell, spell) ← earlyPlace withWeapon p hand "ARC_044_R"
  let (withInstant, inHand) ← earlyPlace withSpell p hand "WTR_173_R"
  let (withArsenal, stored) ← earlyPlace withInstant p arsenal "WTR_173_R"
  let (withEnemy, enemy) ← earlyPlace withArsenal q (.player q .hand) "WTR_173_R"
  let (withBanish, banished) ← earlyPlace withEnemy p (.player p .banished) "WTR_218_R"
  let (withDeck, _) ← ["WTR_191_R", "WTR_192_Y", "WTR_193_B"].foldlM
    (fun (s, _) key => earlyPlace s p deck key) (withBanish, spell)
  let permit : ContinuousEffect :=
    { id := withDeck.nextTimestamp, source := banished, controller := p, target := .obj banished
      op := .allowBanishedPlay none, timestamp := ⟨withDeck.nextTimestamp⟩ }
  let ready := { withDeck with activeEffects := [permit], nextTimestamp := withDeck.nextTimestamp + 1 }
  let resolved ← earlySteps ready (⟨.player p, .playCard spell⟩ :: earlyPass)
  let played ← earlySteps resolved (⟨.player p, .playCard stored⟩ :: earlyPass)
  let drawn := (resolved.zone hand).filterMap (fun id => (resolved.cardDefOf? id).map (·.id))
  pure (canPlayCard ready p inHand && canPlayCard ready p banished &&
    drawn == [⟨"WTR_191_R"⟩, ⟨"WTR_192_Y"⟩, ⟨"WTR_193_B"⟩, ⟨"WTR_173_R"⟩] &&
    (resolved.zone deck).isEmpty && (resolved.poolOf p).actionPoints == (ready.poolOf p).actionPoints &&
    !canPlayCard resolved p inHand && canPlayFromBanished resolved p banished && !canPlayCard resolved p banished &&
    canPlayCard resolved p stored && played.lifeOf p == resolved.lifeOf p + 3 &&
    canPlayCard resolved q enemy && canAttackWithWeapon resolved p weapon &&
    (availableActivations resolved p).contains (hero, 0, none, none) &&
    canPlayCard resolved.finishTurnEffects p inHand)

#guard threeOfAKindScenario == some true

#guard ((earlyPrintingCardId? "ARC045").bind throughArcDB.find?).any
  (fun card => card.front.name == "Endless Arrow" && card.status == .full)

meta def endlessArrowScenario : Option Bool := do
  let p := earlyAttacker
  let hand := Zone.player p .hand
  let arsenal := Zone.player p .arsenal
  let state := { earlyBase with cards := throughArcDB }
  let (withBow, bow) ← earlyPlace state p (.player p .weapon) "ARC_040"
  let (withDeck, _) ← earlyPlace withBow p (.player p .deck) "WTR_191_R"
  let (ready, arrow) ← earlyPlace withDeck p arsenal "ARC_045_R"
  let attacking ← earlyAttack ready (.playCard arrow)
  let link ← attacking.combat.bind CombatChain.activeLink?
  let attackId ← link.attack
  let hit ← earlyDamage attacking
  let trigger ← hit.pendingTriggers.head?
  let returned ← earlySteps hit
    ([⟨.player p, .pickTriggerStart p⟩, ⟨.player p, .pickTrigger trigger.id⟩] ++ earlyPass)
  let returnedId ← (returned.zone hand).head?
  let retained ← returned.combat.bind CombatChain.activeLink?
  let closed ← earlySteps returned (earlyPass ++ earlyPass)
  let use : Action := ⟨.player p, .activateAbility bow 0 none⟩
  let reloaded ← earlySteps closed
    (use :: (earlyPass ++ [⟨.player p, .pickShuffleCard (some returnedId)⟩, ⟨.player p, .pickShuffleCard none⟩]))
  let loadedId ← (reloaded.zone arsenal).head?
  let replay ← earlyAttack reloaded (.playCard loadedId)
  let replayLink ← replay.combat.bind CombatChain.activeLink?
  pure (retained.linkId == link.linkId && retained.hit && retained.damageDealt == 4 &&
    returnedId != arrow && returnedId != attackId && (returned.obj? attackId).isNone &&
    (returned.cardDefOf? returnedId).any (fun c => c.id == ⟨"ARC_045_R"⟩) &&
    !canPlayCard returned p returnedId && closed.combat.isNone &&
    loadedId != returnedId && canPlayCard reloaded p loadedId &&
    linkAttackPower replay replayLink == 4)

#guard endlessArrowScenario == some true

#guard ((earlyPrintingCardId? "ARC046").bind throughArcDB.find?).any
  (fun card => card.front.name == "Nock the Deathwhistle" && card.status == .full)

meta def nockTheDeathwhistleScenario : Option Bool := do
  let p := earlyAttacker
  let hand := Zone.player p .hand
  let deck := Zone.player p .deck
  let arsenal := Zone.player p .arsenal
  let state := { earlyBase with cards := throughArcDB }
  let (withBottom, bottom) ← earlyPlace state p deck "WTR_191_R"
  let (withArrow, arrow) ← earlyPlace withBottom p deck "ARC_045_R"
  let (withTop, top) ← earlyPlace withArrow p deck "WTR_192_Y"
  let (withHand, reserve) ← earlyPlace withTop p hand "WTR_193_B"
  let (ready, spell) ← earlyPlace withHand p hand "ARC_046_B"
  let play : Action := ⟨.player p, .playCard spell⟩
  let pick (id : Option ObjId) : Action := ⟨.player p, .pickShuffleCard id⟩
  let shuffle : Action := ⟨.chance, .shuffleOrder [bottom, top, arrow]⟩
  let reload : Action := ⟨.player p, .arsenalPut reserve⟩
  let declineReload : Action := ⟨.player p, .arsenalSkip⟩
  let choosing ← earlySteps ready (play :: earlyPass)
  let .chooseShuffleCards player 1 [candidate] [] false (some choice) :: _ := choosing.pending | none
  let selected ← earlySteps choosing [pick (some candidate)]
  let (shuffling, events) ← (step 64 selected (pick none)).toOption
  let .chanceShuffle zone :: _ := shuffling.pending | none
  let waitingReload ← earlySteps shuffling [shuffle]
  let .chooseArsenal chooser :: _ := waitingReload.pending | none
  let loaded ← earlySteps waitingReload [reload]
  let declined ← earlySteps choosing [pick none, shuffle, declineReload]
  let (occupied, stored) ← earlyPlace ready p arsenal "WTR_191_R"
  let stillOccupied ← earlySteps occupied (play :: (earlyPass ++ [pick none, shuffle]))
  let loadedId ← (loaded.zone arsenal).head?
  pure (player == p && candidate == arrow && choice.searchesDeck && choice.putOnTopAfterShuffle &&
    (view earlyDefender choosing).selectionChoices.isEmpty &&
    (earlySteps choosing [pick (some top)]).isNone &&
    zone == deck && events.contains (.revealed p arrow ⟨"ARC_045_R"⟩) && chooser == p &&
    waitingReload.zone deck == [arrow, bottom, top] && loaded.zone deck == [arrow, bottom, top] &&
    (loaded.obj? loadedId).any (·.faceDown) && (loaded.zone hand).isEmpty &&
    (loaded.poolOf p).actionPoints == (ready.poolOf p).actionPoints &&
    declined.zone deck == [bottom, top, arrow] && declined.zone arsenal == [] &&
    declined.zone hand == [reserve] && stillOccupied.zone deck == [bottom, top, arrow] &&
    stillOccupied.zone arsenal == [stored] && stillOccupied.zone hand == [reserve])

#guard nockTheDeathwhistleScenario == some true

#guard ((earlyPrintingCardId? "ARC047").bind throughArcDB.find?).any
  (fun card => card.front.name == "Rapid Fire" && card.status == .full)

meta def rapidFireScenario : Option Bool := do
  let p := earlyAttacker
  let arsenal := Zone.player p .arsenal
  let hand := Zone.player p .hand
  let state := { earlyBase with cards := throughArcDB }
  let (withBow, bow) ← earlyPlace state p (.player p .weapon) "ARC_040"
  let (withDeck, _) ← earlyPlace withBow p (.player p .deck) "WTR_192_Y"
  let (withSpell, spell) ← earlyPlace withDeck p hand "ARC_047_Y"
  let (withGeneric, generic) ← earlyPlace withSpell p hand "WTR_203_R"
  let (empty, second) ← earlyPlace withGeneric p hand "ARC_045_R"
  let (ready, first) ← earlyPlace empty p arsenal "ARC_045_R"
  let use : Action := ⟨.player p, .playCard spell⟩
  let buffed ← earlySteps ready (use :: earlyPass)
  let reload ← earlySteps empty (use :: (earlyPass ++ [⟨.player p, .arsenalPut generic⟩]))
  let reloadedGeneric ← (reload.zone arsenal).head?
  let nonArrow ← earlyAttack buffed (.playCard generic)
  let nonArrowLink ← nonArrow.combat.bind CombatChain.activeLink?
  let expired ← earlyAttack buffed.finishTurnEffects (.playCard first)
  let expiredLink ← expired.combat.bind CombatChain.activeLink?
  let firstAttack ← earlyAttack buffed (.playCard first)
  let firstLink ← firstAttack.combat.bind CombatChain.activeLink?
  let hit ← earlyDamage firstAttack
  let trigger ← hit.pendingTriggers.head?
  let returned ← earlySteps hit
    ([⟨.player p, .pickTriggerStart p⟩, ⟨.player p, .pickTrigger trigger.id⟩] ++ earlyPass)
  let closed ← earlySteps returned (earlyPass ++ earlyPass)
  let next ← earlySteps closed
    (⟨.player p, .activateAbility bow 0 none⟩ ::
      (earlyPass ++ [⟨.player p, .pickShuffleCard (some second)⟩, ⟨.player p, .pickShuffleCard none⟩]))
  let secondArrow ← (next.zone arsenal).head?
  let secondAttack ← earlyAttack next (.playCard secondArrow)
  let secondLink ← secondAttack.combat.bind CombatChain.activeLink?
  pure (buffed.zone arsenal == [first] &&
    (buffed.poolOf p).actionPoints == (ready.poolOf p).actionPoints &&
    (reload.obj? reloadedGeneric).any (·.faceDown) &&
    (reload.cardDefOf? reloadedGeneric).any (fun c => c.id == ⟨"WTR_203_R"⟩) &&
    !linkHasKeyword nonArrow nonArrowLink .goAgain && !linkHasKeyword expired expiredLink .goAgain &&
    linkHasKeyword firstAttack firstLink .goAgain && linkHasKeyword secondAttack secondLink .goAgain)

#guard rapidFireScenario == some true

#guard ((earlyPrintingCardId? "ARC048").bind throughArcDB.find?).any
  (fun card => card.front.name == "Take Cover" && card.front.defense == some 4 && card.status == .full)

meta def takeCoverScenario (cardId : String) (defense : Int) : Option Bool := do
  let p := earlyAttacker
  let q := earlyDefender
  let arsenal := Zone.player q .arsenal
  let hand := Zone.player q .hand
  let state := { earlyBase with cards := throughArcDB }
  let (withAttacker, attack) ← earlyPlace state p (.player p .hand) "WTR_203_R"
  let (withSink, sink) ← earlyPlace withAttacker q hand "WTR_215_R"
  let (withHand, handCopy) ← earlyPlace withSink q hand cardId
  let (ready, stored) ← addObject withHand arsenal
    { kind := .card ⟨withHand.nextId⟩ ⟨cardId⟩, owner := q, controller := q,
      timestamp := ⟨0⟩, faceDown := true } .top
  let attacking ← earlyAttack ready (.playCard attack)
  let reacting ← earlySteps attacking
    (⟨.player q, .defendDone⟩ :: (earlyPass ++ [⟨.player p, .pass⟩]))
  let play (id : ObjId) : List Action :=
    [⟨.player q, .playCard id⟩, ⟨.player q, .pass⟩, ⟨.player p, .pass⟩]
  let choosing ← earlySteps reacting (play stored)
  let .chooseArsenal reloader :: _ := choosing.pending | none
  let loaded ← earlySteps choosing [⟨.player q, .arsenalPut sink⟩]
  let skipped ← earlySteps choosing [⟨.player q, .arsenalSkip⟩]
  let noReload ← earlySteps reacting (play handCopy)
  let chain ← loaded.combat
  let link ← chain.activeLink?
  let defender ← link.defending.head?
  let loadedId ← (loaded.zone arsenal).head?
  pure (reloader == q && (choosing.zone arsenal).isEmpty &&
    chain.step == .reaction && (loaded.cardDefOf? defender).any (fun c => c.id == ⟨cardId⟩) &&
    (loaded.characteristics defender).any (fun c => c.defense == some defense) &&
    (loaded.obj? loadedId).any (·.faceDown) && canPlayCard loaded q loadedId &&
    (skipped.zone arsenal).isEmpty && skipped.zone hand == [handCopy, sink] &&
    noReload.zone arsenal == [stored] && noReload.zone hand == [sink])

#guard takeCoverScenario "ARC_048_R" 4 == some true

#guard ((earlyPrintingCardId? "ARC049").bind throughArcDB.find?).any
  (fun card => card.front.name == "Take Cover" && card.front.defense == some 3 && card.status == .full)

#guard takeCoverScenario "ARC_049_Y" 3 == some true

#guard ((earlyPrintingCardId? "ARC050").bind throughArcDB.find?).any
  (fun card => card.front.name == "Take Cover" && card.front.defense == some 2 && card.status == .full)

#guard takeCoverScenario "ARC_050_B" 2 == some true

#guard ((earlyPrintingCardId? "ARC051").bind throughArcDB.find?).any
  (fun card => card.front.name == "Silver the Tip" && card.front.pitch == some 1 && card.status == .full)

meta def silverTheTipScenario (cardId : String) (count : Nat) : Option Bool := do
  let p := earlyAttacker
  let q := earlyDefender
  let deck := Zone.player p .deck
  let arsenal := Zone.player p .arsenal
  let state := { earlyBase with cards := throughArcDB }
  let (s0, sixth) ← earlyPlace state p deck "ARC_043_R"
  let (s1, fifth) ← earlyPlace s0 p deck "WTR_192_Y"
  let (s2, fourth) ← earlyPlace s1 p deck "ARC_045_R"
  let (s3, third) ← earlyPlace s2 p deck "WTR_191_R"
  let (s4, second) ← earlyPlace s3 p deck "ARC_045_R"
  let (s5, first) ← earlyPlace s4 p deck "WTR_203_R"
  let (ready, spell) ← earlyPlace s5 p (.player p .hand) cardId
  let viewed := [first, second, third, fourth, fifth, sixth].take count
  let pick (id : Option ObjId) : Action := ⟨.player p, .pickShuffleCard id⟩
  let order (ids : List ObjId) : List Action := ids.map (fun id => pick (some id)) ++ [pick none]
  let use : Action := ⟨.player p, .playCard spell⟩
  let choosing ← earlySteps ready (use :: earlyPass)
  let .chooseShuffleCards chooser 1 candidates [] false (some choice) :: _ := choosing.pending | none
  let .chooseShuffleCards _ 0 [] [] _ (some redacted) :: _ := (view q choosing).pending | none
  let ordering ← earlySteps choosing [pick (some second), pick none]
  let remaining := (viewed.erase second).reverse
  let .chooseShuffleCards orderer slots _ [] false (some instruction) :: _ := ordering.pending | none
  let loaded ← earlySteps ordering (order remaining)
  let loadedId ← (loaded.zone arsenal).head?
  let declined ← earlySteps choosing (pick none :: order viewed.reverse)
  let (occupied, stored) ← earlyPlace ready p arsenal "WTR_193_B"
  let unchanged ← earlySteps occupied (use :: earlyPass)
  pure (chooser == p && candidates == (if count == 4 then [second, fourth] else [second]) &&
    choice.bottomSelection == some (.lookedAt viewed) && !choice.searchesDeck &&
    (view p choosing).selectionChoices.map Prod.fst == viewed &&
    (view q choosing).selectionChoices.isEmpty && redacted.bottomSelection.isNone &&
    viewZone p choosing deck == .countOnly 6 && (earlySteps choosing [pick (some sixth)]).isNone &&
    (earlySteps choosing [pick (some first)]).isNone &&
    orderer == p && slots == remaining.length && instruction.bottomSelection == some (.order remaining.length) &&
    (earlySteps ordering [pick none]).isNone && (earlySteps ordering [pick (some sixth)]).isNone &&
    (loaded.obj? loadedId).any (fun card => !card.faceDown) &&
    (loaded.cardDefOf? loadedId).any (fun card => card.id == ⟨"ARC_045_R"⟩) &&
    loaded.zone deck == (ready.zone deck).drop count ++ remaining &&
    (loaded.poolOf p).actionPoints == (ready.poolOf p).actionPoints &&
    declined.zone deck == (ready.zone deck).drop count ++ viewed.reverse && (declined.zone arsenal).isEmpty &&
    unchanged.zone deck == ready.zone deck && unchanged.zone arsenal == [stored])

#guard silverTheTipScenario "ARC_051_R" 4 == some true

#guard ((earlyPrintingCardId? "ARC052").bind throughArcDB.find?).any
  (fun card => card.front.name == "Silver the Tip" && card.front.pitch == some 2 && card.status == .full)

#guard silverTheTipScenario "ARC_052_Y" 3 == some true

#guard ((earlyPrintingCardId? "ARC053").bind throughArcDB.find?).any
  (fun card => card.front.name == "Silver the Tip" && card.front.pitch == some 3 && card.status == .full)

#guard silverTheTipScenario "ARC_053_B" 2 == some true

#guard ((earlyPrintingCardId? "ARC054").bind throughArcDB.find?).any
  (fun card => card.front.name == "Take Aim" && card.front.pitch == some 1 && card.status == .full)

meta def takeAimScenario (cardId : String) (expectedPower : Nat) : Option Bool := do
  let p := earlyAttacker
  let hand := Zone.player p .hand
  let arsenal := Zone.player p .arsenal
  let state := { earlyBase with cards := throughArcDB }
  let (withBow, bow) ← earlyPlace state p (.player p .weapon) "ARC_040"
  let (withDeck, _) ← earlyPlace withBow p (.player p .deck) "WTR_192_Y"
  let (withGeneric, generic) ← earlyPlace withDeck p hand "WTR_203_R"
  let (withSecond, second) ← earlyPlace withGeneric p hand "ARC_045_R"
  let (empty, spell) ← earlyPlace withSecond p hand cardId
  let (ready, first) ← earlyPlace empty p arsenal "ARC_045_R"
  let use : Action := ⟨.player p, .playCard spell⟩
  let gained ← earlySteps ready (use :: earlyPass)
  let viaReload ← earlySteps empty (use :: (earlyPass ++ [⟨.player p, .arsenalPut generic⟩]))
  let reserve ← (viaReload.zone arsenal).head?
  let genericAttack ← earlyAttack gained (.playCard generic)
  let genericLink ← genericAttack.combat.bind CombatChain.activeLink?
  let genericHit ← earlyDamage genericAttack
  let closed ← earlySteps genericHit (earlyPass ++ earlyPass)
  let expired ← earlyAttack gained.finishTurnEffects (.playCard first)
  let expiredLink ← expired.combat.bind CombatChain.activeLink?
  let arrowAttack ← earlyAttack closed (.playCard first)
  let arrowLink ← arrowAttack.combat.bind CombatChain.activeLink?
  let arrowHit ← earlyDamage arrowAttack
  let trigger ← arrowHit.pendingTriggers.head?
  let returned ← earlySteps arrowHit
    ([⟨.player p, .pickTriggerStart p⟩, ⟨.player p, .pickTrigger trigger.id⟩] ++ earlyPass)
  let finished ← earlySteps returned (earlyPass ++ earlyPass)
  let reloaded ← earlySteps finished
    (⟨.player p, .activateAbility bow 0 none⟩ ::
      (earlyPass ++ [⟨.player p, .pickShuffleCard (some second)⟩, ⟨.player p, .pickShuffleCard none⟩]))
  let nextArrow ← (reloaded.zone arsenal).head?
  let lastAttack ← earlyAttack reloaded (.playCard nextArrow)
  let lastLink ← lastAttack.combat.bind CombatChain.activeLink?
  pure (gained.zone arsenal == [first] && (gained.poolOf p) == (ready.poolOf p) &&
    (viaReload.obj? reserve).any (·.faceDown) &&
    (viaReload.cardDefOf? reserve).any (fun c => c.id == ⟨"WTR_203_R"⟩) &&
    linkAttackPower genericAttack genericLink == 4 && linkAttackPower expired expiredLink == 4 &&
    linkAttackPower arrowAttack arrowLink == expectedPower && linkAttackPower lastAttack lastLink == 4)

#guard takeAimScenario "ARC_054_R" 7 == some true

#guard ((earlyPrintingCardId? "ARC055").bind throughArcDB.find?).any
  (fun card => card.front.name == "Take Aim" && card.front.pitch == some 2 && card.status == .full)

#guard takeAimScenario "ARC_055_Y" 6 == some true

#guard ((earlyPrintingCardId? "ARC056").bind throughArcDB.find?).any
  (fun card => card.front.name == "Take Aim" && card.front.pitch == some 3 && card.status == .full)

#guard takeAimScenario "ARC_056_B" 5 == some true

#guard ((earlyPrintingCardId? "ARC057").bind throughArcDB.find?).any
  (fun card => card.front.name == "Head Shot" && card.front.pitch == some 1 && card.status == .full)

meta def headShotScenario (cardId : String) (basePower : Nat) : Option Bool := do
  let p := earlyAttacker
  let deck := Zone.player p .deck
  let hand := Zone.player p .hand
  let arsenal := Zone.player p .arsenal
  let state := { earlyBase with cards := throughArcDB }
  let (withBow, bow) ← earlyPlace state p (.player p .weapon) "ARC_040"
  let (withHead, head) ← earlyPlace withBow p (.player p .head) "ARC_041"
  let (withDeck, top) ← earlyPlace withHead p deck "WTR_192_Y"
  let (ready, arrow) ← earlyPlace withDeck p hand cardId
  let choose : Action := ⟨.player p, .pickShuffleCard (some arrow)⟩
  let confirm : Action := ⟨.player p, .pickShuffleCard none⟩
  let loaded ← earlySteps ready
    (⟨.player p, .activateAbility bow 0 none⟩ :: (earlyPass ++ [choose, confirm]))
  let loadedId ← (loaded.zone arsenal).head?
  let trigger ← loaded.pendingTriggers.head?
  let resolve (s : GameState) (id : Nat) :=
    earlySteps s ([⟨.player p, .pickTriggerStart p⟩, ⟨.player p, .pickTrigger id⟩] ++ earlyPass)
  let buffed ← resolve loaded trigger.id
  let attack ← earlyAttack buffed (.playCard loadedId)
  let link ← attack.combat.bind CombatChain.activeLink?
  let expired ← earlyAttack buffed.finishTurnEffects (.playCard loadedId)
  let expiredLink ← expired.combat.bind CombatChain.activeLink?
  let (faceDown, hidden) ← addObject withDeck arsenal
    { kind := .card ⟨withDeck.nextId⟩ ⟨cardId⟩, owner := p, controller := p,
      timestamp := ⟨0⟩, faceDown := true } .top
  let exposed ← earlySteps faceDown
    [⟨.player p, .activateAbility head 0 (some hidden)⟩]
  let flipped ← earlySteps exposed (earlyPass ++ [⟨.player p, .optPick true none⟩])
  let flippedAttack ← earlyAttack flipped (.playCard hidden)
  let flippedLink ← flippedAttack.combat.bind CombatChain.activeLink?
  pure ((loaded.zone deck).isEmpty &&
    (loaded.zone hand).any (fun id => (loaded.cardDefOf? id).any (fun card => card.id == ⟨"WTR_192_Y"⟩)) &&
    trigger.source == loadedId && loaded.pendingTriggers.length == 1 &&
    linkAttackPower attack link == basePower + 2 && linkAttackPower expired expiredLink == basePower &&
    (exposed.obj? hidden).any (fun card => !card.faceDown) && exposed.pendingTriggers.isEmpty &&
    flipped.zone deck == [top] && linkAttackPower flippedAttack flippedLink == basePower)

#guard headShotScenario "ARC_057_R" 4 == some true

#guard ((earlyPrintingCardId? "ARC058").bind throughArcDB.find?).any
  (fun card => card.front.name == "Head Shot" && card.front.pitch == some 2 && card.status == .full)

#guard headShotScenario "ARC_058_Y" 3 == some true

#guard ((earlyPrintingCardId? "ARC059").bind throughArcDB.find?).any
  (fun card => card.front.name == "Head Shot" && card.front.pitch == some 3 && card.status == .full)

#guard headShotScenario "ARC_059_B" 2 == some true

#guard ((earlyPrintingCardId? "ARC060").bind throughArcDB.find?).any
  (fun card => card.front.name == "Hamstring Shot" && card.front.pitch == some 1 && card.status == .full)

meta def hamstringShotScenario (cardId : String) (damage : Int) : Option Bool := do
  let p := earlyAttacker
  let q := earlyDefender
  let base := { earlyBase with cards := throughArcDB }
  let (withBow, _) ← earlyPlace base p (.player p .weapon) "ARC_040"
  let (archer, arrow) ← earlyPlace withBow p (.player p .arsenal) cardId
  let attacking ← earlyAttack archer (.playCard arrow)
  let hit ← earlyDamage attacking
  let trigger ← hit.pendingTriggers.head?
  let applied ← earlySteps hit
    ([⟨.player p, .pickTriggerStart p⟩, ⟨.player p, .pickTrigger trigger.id⟩] ++ earlyPass)
  let closed ← earlySteps applied (earlyPass ++ earlyPass)
  let (withBlade, blade) ← earlyPlace closed q (.player q .weapon) "WTR_115"
  let (withUtility, utility) ← earlyPlace withBlade q (.player q .hand) "WTR_218_R"
  let (prepared, action) ← earlyPlace withUtility q (.player q .hand) "WTR_203_R"
  let next := { prepared.setPool q { actionPoints := 3, resources := 6 } with
    turn := prepared.turn + 1, active := some q, pending := [.startPhaseWork q, .actionPhaseStart q] }
  let (start, _) ← microStep next
  let (ready, _) ← microStep start
  let pass : List Action := [⟨.player q, .pass⟩, ⟨.player p, .pass⟩]
  let afterUtility ← earlySteps ready (⟨.player q, .playCard utility⟩ :: pass)
  let firstAttack : Action := ⟨.player q, .playCard action⟩
  let byCard ← earlySteps afterUtility [firstAttack]
  let byWeapon ← earlySteps ready [⟨.player q, .attackWeapon blade⟩]
  let discount : ContinuousEffect :=
    { id := afterUtility.nextTimestamp, source := utility, controller := q,
      target := .nextAttackCard CardFilter.attackAction, op := .subCostRes 1
      timestamp := ⟨afterUtility.nextTimestamp⟩ }
  let reduced ← earlySteps { afterUtility with activeEffects := afterUtility.activeEffects ++ [discount] }
    [firstAttack]
  pure (hit.lifeOf q == base.lifeOf q - damage && closed.combat.isNone &&
    nextAttackSurcharge closed q == 0 && nextAttackSurcharge ready q == 1 &&
    nextAttackSurcharge ready p == 0 && nextAttackSurcharge afterUtility q == 1 &&
    (byCard.poolOf q).resources + 1 == (afterUtility.poolOf q).resources &&
    (byWeapon.poolOf q).resources + 2 == (ready.poolOf q).resources &&
    (reduced.poolOf q).resources == (afterUtility.poolOf q).resources &&
    nextAttackSurcharge byCard q == 0 && nextAttackSurcharge byWeapon q == 0 &&
    nextAttackSurcharge reduced q == 0 && nextAttackSurcharge ready.finishTurnEffects q == 0)

#guard hamstringShotScenario "ARC_060_R" 5 == some true

#guard ((earlyPrintingCardId? "ARC061").bind throughArcDB.find?).any
  (fun card => card.front.name == "Hamstring Shot" && card.front.pitch == some 2 && card.status == .full)

#guard hamstringShotScenario "ARC_061_Y" 4 == some true

#guard ((earlyPrintingCardId? "ARC062").bind throughArcDB.find?).any
  (fun card => card.front.name == "Hamstring Shot" && card.front.pitch == some 3 && card.status == .full)

#guard hamstringShotScenario "ARC_062_B" 3 == some true

#guard ((earlyPrintingCardId? "ARC063").bind throughArcDB.find?).any
  (fun card => card.front.name == "Ridge Rider Shot" && card.front.pitch == some 1 && card.status == .full)

meta def ridgeRiderShotScenario (cardId : String) : Option Bool := do
  let p := earlyAttacker
  let deck := Zone.player p .deck
  let arsenal := Zone.player p .arsenal
  let state := { earlyBase with cards := throughArcDB }
  let (withBow, bow) ← earlyPlace state p (.player p .weapon) "ARC_040"
  let (withHead, head) ← earlyPlace withBow p (.player p .head) "ARC_041"
  let (withBottom, bottom) ← earlyPlace withHead p deck "WTR_193_B"
  let (withLook, lookedAt) ← earlyPlace withBottom p deck "WTR_192_Y"
  let (withDeck, top) ← earlyPlace withLook p deck "WTR_191_R"
  let (ready, arrow) ← earlyPlace withDeck p (.player p .hand) cardId
  let loaded ← earlySteps ready
    (⟨.player p, .activateAbility bow 0 none⟩ ::
      (earlyPass ++ [⟨.player p, .pickShuffleCard (some arrow)⟩, ⟨.player p, .pickShuffleCard none⟩]))
  let loadedId ← (loaded.zone arsenal).head?
  let trigger ← loaded.pendingTriggers.head?
  let choosing ← earlySteps loaded
    ([⟨.player p, .pickTriggerStart p⟩, ⟨.player p, .pickTrigger trigger.id⟩] ++ earlyPass)
  let .chooseOpt chooser viewed _ _ _ :: _ := choosing.pending | none
  let resolved ← earlySteps choosing [⟨.player p, .optPick false none⟩]
  let (faceDown, hidden) ← addObject withDeck arsenal
    { kind := .card ⟨withDeck.nextId⟩ ⟨cardId⟩, owner := p, controller := p,
      timestamp := ⟨0⟩, faceDown := true } .top
  let flipped ← earlySteps faceDown [⟨.player p, .activateAbility head 0 (some hidden)⟩]
  let crosswrap ← earlySteps flipped (earlyPass ++ [⟨.player p, .optPick true none⟩])
  pure (trigger.source == loadedId && loaded.pendingTriggers.length == 1 &&
    loaded.zone deck == [lookedAt, bottom] && chooser == p && viewed == lookedAt &&
    resolved.zone deck == [bottom, lookedAt] && resolved.zone arsenal == [loadedId] &&
    (flipped.obj? hidden).any (fun card => !card.faceDown) &&
    flipped.pendingTriggers.isEmpty && crosswrap.pendingTriggers.isEmpty &&
    crosswrap.zone deck == [top, lookedAt, bottom])

#guard ridgeRiderShotScenario "ARC_063_R" == some true

#guard ((earlyPrintingCardId? "ARC064").bind throughArcDB.find?).any
  (fun card => card.front.name == "Ridge Rider Shot" && card.front.pitch == some 2 && card.status == .full)

#guard ridgeRiderShotScenario "ARC_064_Y" == some true

#guard ((earlyPrintingCardId? "ARC065").bind throughArcDB.find?).any
  (fun card => card.front.name == "Ridge Rider Shot" && card.front.pitch == some 3 && card.status == .full)

#guard ridgeRiderShotScenario "ARC_065_B" == some true

#guard ((earlyPrintingCardId? "ARC066").bind throughArcDB.find?).any
  (fun card => card.front.name == "Salvage Shot" && card.front.pitch == some 1 && card.status == .full)

meta def salvageShotScenario (cardId : String) (damage : Nat) : Option Bool := do
  let p := earlyAttacker
  let deck := Zone.player p .deck
  let arsenal := Zone.player p .arsenal
  let state := { earlyBase with cards := throughArcDB }
  let (withBow, _) ← earlyPlace state p (.player p .weapon) "ARC_040"
  let (withBottom, bottom) ← earlyPlace withBow p deck "WTR_193_B"
  let (withDeck, top) ← earlyPlace withBottom p deck "WTR_192_Y"
  let (ready, arrow) ← earlyPlace withDeck p arsenal cardId
  let attacking ← earlyAttack ready (.playCard arrow)
  let link ← attacking.combat.bind CombatChain.activeLink?
  let source ← link.attack
  let hit ← earlyDamage attacking
  let trigger ← hit.pendingTriggers.head?
  let returned ← earlySteps hit
    ([⟨.player p, .pickTriggerStart p⟩, ⟨.player p, .pickTrigger trigger.id⟩] ++ earlyPass)
  let retained ← returned.combat.bind CombatChain.activeLink?
  let newId ← (returned.zone deck).getLast?
  pure (trigger.source == source && retained.linkId == link.linkId && retained.hit &&
    retained.damageDealt == damage && returned.zone deck == [top, bottom, newId] &&
    newId != arrow && newId != source && (returned.obj? source).isNone &&
    (returned.cardDefOf? newId).any (fun card => card.id == ⟨cardId⟩))

#guard salvageShotScenario "ARC_066_R" 5 == some true

#guard ((earlyPrintingCardId? "ARC067").bind throughArcDB.find?).any
  (fun card => card.front.name == "Salvage Shot" && card.front.pitch == some 2 && card.status == .full)

#guard salvageShotScenario "ARC_067_Y" 4 == some true

#guard ((earlyPrintingCardId? "ARC068").bind throughArcDB.find?).any
  (fun card => card.front.name == "Salvage Shot" && card.front.pitch == some 3 && card.status == .full)

#guard salvageShotScenario "ARC_068_B" 3 == some true

#guard ((earlyPrintingCardId? "ARC069").bind throughArcDB.find?).any
  (fun card => card.front.name == "Searing Shot" && card.front.pitch == some 1 && card.status == .full)

meta def searingShotScenario (cardId : String) (damage : Int) : Option Bool := do
  let p := earlyAttacker
  let q := earlyDefender
  let state := { earlyBase with cards := throughArcDB }
  let (withBow, _) ← earlyPlace state p (.player p .weapon) "ARC_040"
  let (ready, arrow) ← earlyPlace withBow p (.player p .arsenal) cardId
  let attack ← earlyAttack ready (.playCard arrow)
  let hit ← earlyDamage attack
  let trigger ← hit.pendingTriggers.head?
  let stacked ← earlySteps hit [⟨.player p, .pickTriggerStart p⟩, ⟨.player p, .pickTrigger trigger.id⟩]
  let passed ← earlySteps stacked [⟨.player p, .pass⟩]
  let (resolved, events) ← (step 64 passed ⟨.player q, .pass⟩).toOption
  let retained ← resolved.combat.bind CombatChain.activeLink?
  pure (trigger.effect == .prim (.loseLife (.seated q) (.const 1)) &&
    hit.lifeOf q == ready.lifeOf q - damage && resolved.lifeOf q == hit.lifeOf q - 1 &&
    resolved.lifeOf p == ready.lifeOf p && retained.damageDealt == damage.toNat &&
    !events.any (fun event => match event with | .damageDealt _ _ _ => true | _ => false))

#guard searingShotScenario "ARC_069_R" 4 == some true

#guard ((earlyPrintingCardId? "ARC070").bind throughArcDB.find?).any
  (fun card => card.front.name == "Searing Shot" && card.front.pitch == some 2 && card.status == .full)

#guard searingShotScenario "ARC_070_Y" 3 == some true

#guard ((earlyPrintingCardId? "ARC071").bind throughArcDB.find?).any
  (fun card => card.front.name == "Searing Shot" && card.front.pitch == some 3 && card.status == .full)

#guard searingShotScenario "ARC_071_B" 2 == some true

#guard ((earlyPrintingCardId? "ARC072").bind throughArcDB.find?).any
  (fun card => card.front.name == "Sic 'Em Shot" && card.front.pitch == some 1 && card.status == .full)

meta def sicEmShotScenario (cardId : String) (power : Nat) : Option Bool := do
  let p := earlyAttacker
  let arsenal := Zone.player p .arsenal
  let state := { earlyBase with cards := throughArcDB }
  let (withBow, _) ← earlyPlace state p (.player p .weapon) "ARC_040"
  let (withHand, copy) ← earlyPlace withBow p (.player p .hand) cardId
  let (ready, arrow) ← earlyPlace withHand p arsenal cardId
  let attacking ← earlyAttack ready (.playCard arrow)
  let link ← attacking.combat.bind CombatChain.activeLink?
  let hit ← earlyDamage attacking
  let closed ← earlySteps hit (earlyPass ++ earlyPass)
  pure (!canPlayCard ready p copy && linkAttackPower attacking link == power &&
    linkHasKeyword attacking link .goAgain &&
    (closed.poolOf p).actionPoints == (ready.poolOf p).actionPoints)

#guard sicEmShotScenario "ARC_072_R" 4 == some true

#guard ((earlyPrintingCardId? "ARC073").bind throughArcDB.find?).any
  (fun card => card.front.name == "Sic 'Em Shot" && card.front.pitch == some 2 && card.status == .full)

#guard sicEmShotScenario "ARC_073_Y" 3 == some true

#guard ((earlyPrintingCardId? "ARC074").bind throughArcDB.find?).any
  (fun card => card.front.name == "Sic 'Em Shot" && card.front.pitch == some 3 && card.status == .full)

#guard sicEmShotScenario "ARC_074_B" 2 == some true

#guard ((earlyPrintingCardId? "ARC075").bind throughArcDB.find?).any
  (fun card => card.front.name == "Viserai, Rune Blood" && card.front.life == some 40 && card.status == .full)

meta def viseraiRunechantScenario (heroId : String) : Option Bool := do
  let p := earlyAttacker
  let q := earlyDefender
  let hand := Zone.player p .hand
  let arena := Zone.player p .permanent
  let runebladeAction := FabCards.ARC.Meta.ARC_081_R_meta
  let runebladeAttack := FabCards.ARC.Meta.ARC_080_R_meta
  let cards : CardDB := ⟨runebladeAction :: runebladeAttack :: throughArcDB.cards⟩
  let state := { earlyBase with cards }
  let (withHero, hero) ← earlyPlace state p (.player p .hero) heroId
  let (withBlade, blade) ← earlyPlace withHero p (.player p .weapon) "WTR_115"
  let (withFirst, first) ← earlyPlace withBlade p hand runebladeAction.id.val
  let (withSecond, second) ← earlyPlace withFirst p hand runebladeAction.id.val
  let (withUtility, utility) ← earlyPlace withSecond p hand "WTR_218_R"
  let (withAttack, attack) ← earlyPlace withUtility p hand "WTR_203_R"
  let (ready, classAttack) ← earlyPlace withAttack p hand runebladeAttack.id.val
  let play (id : ObjId) : Action := ⟨.player p, .playCard id⟩
  let start : Action := ⟨.player p, .pickTriggerStart p⟩
  let firstPlayed ← earlySteps ready (play first :: earlyPass)
  let genericPlayed ← earlySteps ready (play utility :: earlyPass)
  let (reset, _) ← microStep { firstPlayed with pending := [.endTurnCleanup p] }
  let heroQueued ← earlySteps genericPlayed [play second]
  let heroTrigger ← heroQueued.pendingTriggers.head?
  let made ← earlySteps heroQueued
    ([start, ⟨.player p, .pickTrigger heroTrigger.id⟩] ++ earlyPass ++ earlyPass)
  let token ← (made.zone arena).head?
  let classQueued ← earlySteps genericPlayed [play classAttack]
  let classTrigger ← classQueued.pendingTriggers.head?
  let classMade ← earlySteps classQueued ([start, ⟨.player p, .pickTrigger classTrigger.id⟩] ++ earlyPass)
  let cardQueued ← earlySteps made [play attack]
  let weaponQueued ← earlySteps made [⟨.player p, .attackWeapon blade⟩]
  let cardTrigger ← cardQueued.pendingTriggers.head?
  let weaponTrigger ← weaponQueued.pendingTriggers.head?
  let cast ← earlySteps cardQueued
    ([start, ⟨.player p, .pickTrigger cardTrigger.id (some q)⟩] ++ earlyPass)
  let weaponCast ← earlySteps weaponQueued
    ([start, ⟨.player p, .pickTrigger weaponTrigger.id (some q)⟩] ++ earlyPass)
  pure (firstPlayed.nonAttackActionsThisTurn == [p] && firstPlayed.pendingTriggers.isEmpty &&
    (firstPlayed.zone arena).isEmpty && genericPlayed.nonAttackActionsThisTurn == [p] &&
    genericPlayed.pendingTriggers.isEmpty && reset.nonAttackActionsThisTurn.isEmpty &&
    heroTrigger.source == hero && (made.cardDefOf? token).any (fun c => c.id == ⟨"ARC_112"⟩) &&
    (made.zone arena).length == 1 && classTrigger.source == hero &&
    (classMade.zone arena).length == 1 && classMade.pendingTriggers.isEmpty &&
    classMade.lifeOf q == ready.lifeOf q && cardTrigger.source == token && weaponTrigger.source == token &&
    cardTrigger.requiresOpposingHero && cardTrigger.targetChoices cardQueued == [(some q, none)] &&
    (earlySteps cardQueued [start, ⟨.player p, .pickTrigger cardTrigger.id (some p)⟩]).isNone &&
    cast.lifeOf q == made.lifeOf q - 1 && weaponCast.lifeOf q == made.lifeOf q - 1 &&
    (cast.zone arena).isEmpty && (weaponCast.zone arena).isEmpty &&
    (cast.zone .stack).length == 1 && (weaponCast.zone .stack).length == 1)

#guard viseraiRunechantScenario "ARC_075" == some true

#guard ((earlyPrintingCardId? "ARC076").bind throughArcDB.find?).any
  (fun card => card.front.name == "Viserai" && card.front.life == some 20 &&
    card.front.hasSubtype .young && card.status == .full)

#guard ["HER019", "HER019-P"].all
  (fun printing => earlyPrintingCardId? printing == some ⟨"ARC_075"⟩)
#guard ["HER015", "HER015-P"].all
  (fun printing => earlyPrintingCardId? printing == some ⟨"ARC_076"⟩)

#guard viseraiRunechantScenario "ARC_076" == some true

#guard ((earlyPrintingCardId? "ARC077-T").bind throughArcDB.find?).any
  (fun card => card.front.name == "Nebula Blade" && card.front.power == some 1 &&
    weaponAttackSpec? card == some (0, true, { actionPoints := 1, resources := 2 }))

meta def nebulaBladeScenario : Option Bool := do
  let p := earlyAttacker
  let q := earlyDefender
  let arena := Zone.player p .permanent
  let (withSword, sword) ← earlyPlace { earlyBase with cards := throughArcDB }
    p (.player p .weapon) "ARC_077"
  let (ready, utility) ← earlyPlace withSword p (.player p .hand) "WTR_218_R"
  let boosted ← earlySteps ready (⟨.player p, .playCard utility⟩ :: earlyPass)
  let unboostedAttack ← earlyAttack ready (.attackWeapon sword)
  let attack ← earlyAttack boosted (.attackWeapon sword)
  let unboostedLink ← unboostedAttack.combat.bind CombatChain.activeLink?
  let link ← attack.combat.bind CombatChain.activeLink?
  let damaged ← earlyDamage attack
  let onHit ← damaged.pendingTriggers.head?
  let after ← earlySteps damaged
    ([⟨.player p, .pickTriggerStart p⟩, ⟨.player p, .pickTrigger onHit.id⟩] ++ earlyPass)
  let token ← (after.zone arena).head?
  pure (linkAttackPower unboostedAttack unboostedLink == 1 &&
    linkAttackPower { unboostedAttack with nonAttackActionsThisTurn := [p, p] } unboostedLink == 4 &&
    linkAttackPower attack link == 4 && (attack.poolOf p).resources == (boosted.poolOf p).resources - 2 &&
    attack.activatedThisTurn.contains (sword, 0) && onHit.source == sword &&
    damaged.lifeOf q == ready.lifeOf q - 4 && (damaged.zone arena).isEmpty &&
    (after.zone arena).length == 1 &&
    (after.cardDefOf? token).any (fun card => card.id == FabCards.ARC.runechantToken.id))

#guard nebulaBladeScenario == some true

#guard ((earlyPrintingCardId? "ARC078-L").bind throughArcDB.find?).any
  (fun card => card.front.defense == some 2 && card.front.hasSubtype .arms &&
    card.front.keywords.contains .battleworn && card.status == .full)

meta def graspArknightScenario : Option Bool := do
  let p := earlyAttacker
  let q := earlyDefender
  let token := FabCards.ARC.runechantToken.id
  let (ready, grasp) ← earlyPlace { earlyBase with cards := throughArcDB }
    p (.player p .arms) "ARC_078"
  let withOpponent := createTokens ready q token 1
  let stocked := createTokens withOpponent p token 2
  let canAfford := stocked.setPool p { actionPoints := 1, resources := 4 }
  let short := stocked.setPool p { actionPoints := 1, resources := 3 }
  let openPlan ← activationPlan? withOpponent p grasp 0 none
  let stockedPlan ← activationPlan? canAfford p grasp 0 none
  let activate : Action := ⟨.player p, .activateAbility grasp 0 none⟩
  let cast ← earlySteps canAfford [activate]
  let resolved ← earlySteps cast earlyPass
  pure (openPlan.cost.resources == 2 && stockedPlan.cost.resources == 4 &&
    (earlySteps short [activate]).isNone && (cast.poolOf p).resources == 0 &&
    (cast.poolOf p).actionPoints == 0 && controlledPermanentCount cast p token == 2 &&
    (resolved.poolOf p).actionPoints == 1 && resolved.activatedThisTurn.contains (grasp, 0) &&
    controlledPermanentCount resolved p token == 3 &&
    controlledPermanentCount resolved q token == 1 &&
    (earlySteps (resolved.setPool p { actionPoints := 1, resources := 8 }) [activate]).isNone)

#guard graspArknightScenario == some true

#guard ((earlyPrintingCardId? "ARC079").bind throughArcDB.find?).any
  (fun card => card.front.hasSubtype .head && card.front.keywords.contains (.arcaneBarrier 1) &&
    card.status == .full)

meta def crownDichotomyScenario : Option Bool := do
  let p := earlyAttacker
  let q := earlyDefender
  let grave := Zone.player p .graveyard
  let hand := Zone.player p .hand
  let deck := Zone.player p .deck
  let attack := FabCards.ARC.Meta.ARC_080_R_meta
  let nonAttack := FabCards.ARC.Meta.ARC_081_R_meta
  let cards : CardDB := ⟨attack :: nonAttack :: throughArcDB.cards⟩
  let (withCrown, crown) ← earlyPlace { earlyBase with cards } p (.player p .head) "ARC_079"
  let (oneTarget, a) ← earlyPlace withCrown p grave attack.id.val
  let (withTargets, b) ← earlyPlace oneTarget p grave nonAttack.id.val
  let (withFiller, generic) ← earlyPlace withTargets p grave "WTR_203_R"
  let (ready, opponent) ← earlyPlace withFiller q (.player q .graveyard) attack.id.val
  let activate (first second : Option ObjId) : Action :=
    ⟨.player p, .activateAbility crown 0 first second⟩
  let cast ← earlySteps ready [activate (some a) (some b)]
  let order ← earlySteps cast earlyPass
  let firstTop ← earlySteps order [⟨.player p, .pickMode 0⟩]
  let secondTop ← earlySteps order [⟨.player p, .pickMode 1⟩]
  let (oneLost, _) ← moveObj cast b hand .top false
  let (bothLost, _) ← moveObj oneLost a hand .top false
  let single ← earlySteps oneLost earlyPass
  let empty ← earlySteps bothLost earlyPass
  let deckCards (s : GameState) := (s.zone deck).filterMap fun id => (s.cardDefOf? id).map (·.id)
  pure ((earlySteps oneTarget [activate (some a) none]).isNone &&
    (earlySteps ready [activate (some a) (some a)]).isNone &&
    (earlySteps ready [activate (some generic) (some b)]).isNone &&
    (earlySteps ready [activate (some opponent) (some b)]).isNone &&
    (earlySteps ready [activate (some b) (some a)]).isNone &&
    (cast.zone (.player p .head)).isEmpty && (cast.poolOf p).resources == 7 &&
    ((cast.zone grave).filterMap fun id => (cast.cardDefOf? id).map (·.id)).contains ⟨"ARC_079"⟩ &&
    deckCards firstTop == [attack.id, nonAttack.id] &&
    deckCards secondTop == [nonAttack.id, attack.id] &&
    deckCards single == [attack.id] && (deckCards empty).isEmpty &&
    (firstTop.poolOf p).actionPoints == 3)

#guard crownDichotomyScenario == some true

#guard ((earlyPrintingCardId? "ARC080").bind throughArcDB.find?).any
  (fun card => card.front.keywords.contains .dominate &&
    card.front.keywords.contains (.specialization "Viserai") && card.status == .full)

meta def arknightAscendancyScenario : Option Bool := do
  let p := earlyAttacker
  let q := earlyDefender
  let card := FabCards.ARC.ARC_080_R
  let token := FabCards.ARC.runechantToken.id
  let (withAttack, attack) ← earlyPlace { earlyBase with cards := throughArcDB }
    p (.player p .hand) card.id.val
  let (ready, defender) ← earlyPlace withAttack q (.player q .hand) "WTR_203_R"
  let opponent := createTokens ready q token 2
  let discounted := createTokens opponent p token 2
  let enough := createTokens discounted p token 7
  let paid ← earlySteps discounted [⟨.player p, .playCard attack⟩]
  let attacking ← earlyAttack ready (.playCard attack)
  let blocked ← earlySteps attacking [⟨.player q, .defendCard defender⟩]
  let fullHit ← earlyDamage attacking
  let partialHit ← earlyDamage blocked
  let fullTrigger ← fullHit.pendingTriggers.head?
  let partialTrigger ← partialHit.pendingTriggers.head?
  let resolve (s : GameState) (trigger : PendingTrigger) :=
    earlySteps s ([⟨.player p, .pickTriggerStart p⟩, ⟨.player p, .pickTrigger trigger.id⟩] ++ earlyPass)
  let full ← resolve fullHit fullTrigger
  let guardedResult ← resolve partialHit partialTrigger
  pure ((modifiedCardPlayCost opponent p card).resources == 6 &&
    (modifiedCardPlayCost discounted p card).resources == 4 &&
    (modifiedCardPlayCost enough p card).resources == 0 &&
    (paid.poolOf p).resources == 4 && paid.pendingTriggers.length == 2 &&
    fullHit.lifeOf q == ready.lifeOf q - 5 && partialHit.lifeOf q == ready.lifeOf q - 2 &&
    controlledPermanentCount full p token == 5 && controlledPermanentCount guardedResult p token == 2)

#guard arknightAscendancyScenario == some true

#guard ((earlyPrintingCardId? "ARC081").bind throughArcDB.find?).any
  (fun card => card.front.keywords.contains .goAgain && card.status == .full)

meta def mordredTideScenario : Option Bool := do
  let p := earlyAttacker
  let q := earlyDefender
  let hand := Zone.player p .hand
  let token := FabCards.ARC.runechantToken.id
  let quicken : CardId := ⟨"WTR_225"⟩
  let (withHero, hero) ← earlyPlace { earlyBase with cards := throughArcDB }
    p (.player p .hero) "ARC_075"
  let (withFirst, first) ← earlyPlace withHero p hand "ARC_081_R"
  let (withSecond, second) ← earlyPlace withFirst p hand "ARC_081_R"
  let (ready, utility) ← earlyPlace withSecond p hand "WTR_218_R"
  let opener ← earlySteps ready (⟨.player p, .playCard utility⟩ :: earlyPass)
  let resolve (s : GameState) (card : ObjId) : Option GameState := do
    let announced ← earlySteps s [⟨.player p, .playCard card⟩]
    let trigger ← announced.pendingTriggers.head?
    earlySteps announced
      ([⟨.player p, .pickTriggerStart p⟩, ⟨.player p, .pickTrigger trigger.id⟩] ++ earlyPass ++ earlyPass)
  let once ← resolve opener first
  let twice ← resolve once second
  let create (s : GameState) (target : PlayerId) (id : CardId) (count : Nat) :=
    (execPrim s p hero [] (.createToken (.seated target) id count)).1
  pure (controlledPermanentCount once p token == 1 && controlledPermanentCount twice p token == 3 &&
    controlledPermanentCount (create twice p token 3) p token == 8 &&
    controlledPermanentCount (create twice p token 0) p token == 3 &&
    controlledPermanentCount (create twice q token 1) q token == 1 &&
    controlledPermanentCount (create twice p quicken 1) p quicken == 1 &&
    controlledPermanentCount (create twice.finishTurnEffects p token 3) p token == 6)

#guard mordredTideScenario == some true

#guard ((earlyPrintingCardId? "ARC082").bind throughArcDB.find?).any
  (fun card => card.front.power == some 9 && card.front.pitch == some 2 &&
    card.front.defense == some 3 && card.status == .full)

meta def ninthBladeScenario : Option Bool := do
  let p := earlyAttacker
  let q := earlyDefender
  let card := FabCards.ARC.ARC_082_Y
  let token := FabCards.ARC.runechantToken.id
  let (withCard, attack) ← earlyPlace { earlyBase with cards := throughArcDB }
    p (.player p .hand) card.id.val
  let opposed := createTokens withCard q token 1
  let discounted := createTokens opposed p token 1
  let abundant := createTokens discounted p token 9
  let paid ← earlySteps discounted [⟨.player p, .playCard attack⟩]
  pure ((modifiedCardPlayCost opposed p card).resources == 9 &&
    (modifiedCardPlayCost discounted p card).resources == 8 &&
    (modifiedCardPlayCost abundant p card).resources == 0 &&
    (paid.poolOf p).resources == 0 && paid.pendingTriggers.length == 1)

#guard ninthBladeScenario == some true

#guard ((earlyPrintingCardId? "ARC083").bind throughArcDB.find?).any
  (fun card => card.front.keywords.contains .goAgain &&
    card.front.keywords.contains (.specialization "Viserai") && card.status == .full)

meta def becomeArknightScenario : Option Bool := do
  let p := earlyAttacker
  let q := earlyDefender
  let hand := Zone.player p .hand
  let deck := Zone.player p .deck
  let cardIds (s : GameState) (z : Zone) :=
    (s.zone z).filterMap (fun id => (s.cardDefOf? id).map (·.id))
  let (withTutor, tutor) ← earlyPlace { earlyBase with cards := throughArcDB }
    p hand "ARC_083_B"
  let (withAttack, handAttack) ← earlyPlace withTutor p hand "WTR_203_R"
  let (withAction, handAction) ← earlyPlace withAttack p hand "WTR_218_R"
  let (withOther, other) ← earlyPlace withAction p hand "WTR_225"
  let (withDeckAttack, deckAttack) ← earlyPlace withOther p deck "ARC_082_Y"
  let (withDeckAction, deckAction) ← earlyPlace withDeckAttack p deck "ARC_081_R"
  let (ready, wrongClass) ← earlyPlace withDeckAction p deck "WTR_203_R"
  let optionalChoice ← earlySteps ready (⟨.player p, .playCard tutor⟩ :: earlyPass)
  let declare (id : ObjId) : Action := ⟨.player p, .pickDiscardCard id⟩
  let search (id : ObjId) : Action := ⟨.player p, .pickShuffleCard (some id)⟩
  let confirm : Action := ⟨.player p, .pickShuffleCard none⟩
  let shuffle (s : GameState) := earlySteps s [⟨.chance, .shuffleOrder ((s.zone deck).reverse)⟩]
  let selecting ← earlySteps optionalChoice [⟨.player p, .pickMay true⟩]
  let attackSearch ← earlySteps selecting [declare handAction]
  let actionSearch ← earlySteps selecting [declare handAttack]
  let chosenAttack ← earlySteps attackSearch [search deckAttack]
  let (gotAttack, attackEvents) ← (step 64 chosenAttack confirm).toOption
  let gotAction ← earlySteps actionSearch [search deckAction, confirm]
  let declining ← earlySteps optionalChoice [⟨.player p, .pickMay false⟩]
  let failToFind ← earlySteps attackSearch [confirm]
  let done ← shuffle gotAttack
  let declined ← shuffle declining
  let failed ← shuffle failToFind
  let revealed := attackEvents.any fun
    | .revealed owner _ id => owner == p && id == ⟨"ARC_082_Y"⟩
    | _ => false
  pure ((earlySteps selecting [declare other]).isNone &&
    (earlySteps attackSearch [search wrongClass]).isNone &&
    (earlySteps actionSearch [search deckAttack]).isNone &&
    (view q selecting).selectionChoices.isEmpty &&
    revealed && (cardIds done hand).contains ⟨"ARC_082_Y"⟩ &&
    (cardIds gotAction hand).contains ⟨"ARC_081_R"⟩ &&
    (cardIds declined deck).length == 3 && (cardIds failed deck).length == 3 &&
    (cardIds declined hand).contains ⟨"WTR_218_R"⟩ &&
    !(cardIds failed hand).contains ⟨"WTR_218_R"⟩ && (done.poolOf p).actionPoints == 4)

#guard becomeArknightScenario == some true

#guard ((earlyPrintingCardId? "ARC084").bind throughArcDB.find?).any
  (fun card => card.front.keywords.contains .goAgain && card.status == .full)

meta def tomeArknightScenario (cards : List String) (shouldTake : Bool) : Option Bool := do
  let p := earlyAttacker
  let q := earlyDefender
  let deck := Zone.player p .deck
  let hand := Zone.player p .hand
  let names (s : GameState) (z : Zone) :=
    (s.zone z).filterMap (fun id => (s.cardDefOf? id).map (·.id.val))
  let noDraw : ContinuousEffect :=
    { id := 1, source := ⟨0⟩, controller := q, target := .player p, op := .cantDrawCards,
      duration := .thisActionPhase, timestamp := ⟨1⟩ }
  let (withTome, tome) ← earlyPlace { earlyBase with cards := throughArcDB, activeEffects := [noDraw] }
    p hand "ARC_084_B"
  let ready ← cards.reverse.foldlM (fun s name => (earlyPlace s p deck name).map Prod.fst) withTome
  let waiting ← earlySteps ready [⟨.player p, .playCard tome⟩, ⟨.player p, .pass⟩]
  let (done, events) ← (step 64 waiting ⟨.player q, .pass⟩).toOption
  let revealed := events.filterMap fun
    | .revealed player _ id => if player == p then some id.val else none
    | _ => none
  let top := cards.take 2
  pure (revealed == top && names done deck == (if shouldTake then cards.drop 2 else cards) &&
    names done hand == (if shouldTake then top.reverse else []) &&
    (done.poolOf p).actionPoints == 4 && (done.poolOf p).resources == 7)

#guard tomeArknightScenario ["WTR_203_R", "WTR_218_R", "ARC_081_R"] true == some true
#guard tomeArknightScenario ["WTR_218_R", "WTR_203_R"] true == some true
#guard tomeArknightScenario ["WTR_203_R", "ARC_082_Y"] false == some true
#guard tomeArknightScenario ["WTR_203_R", "WTR_225", "WTR_218_R"] false == some true
#guard tomeArknightScenario ["WTR_218_R"] false == some true

meta def spellbladeRunechantScenario (name : String) (power : Nat)
    (count : Nat := 2) (cost : Nat := 2) : Option Bool := do
  let p := earlyAttacker
  let q := earlyDefender
  let token := FabCards.ARC.runechantToken.id
  let (ready, attack) ← earlyPlace { earlyBase with cards := throughArcDB }
    p (.player p .hand) name
  let paid ← earlySteps ready [⟨.player p, .playCard attack⟩]
  let attacking ← earlySteps paid earlyPass
  let trigger ← attacking.pendingTriggers.head?
  let resolved ← earlySteps attacking
    ([⟨.player p, .pickTriggerStart p⟩, ⟨.player p, .pickTrigger trigger.id⟩] ++ earlyPass)
  let link ← resolved.combat.bind CombatChain.activeLink?
  pure (paid.pendingTriggers.isEmpty && controlledPermanentCount paid p token == 0 &&
    controlledPermanentCount attacking p token == 0 && attacking.pendingTriggers.length == 1 &&
    controlledPermanentCount resolved p token == count && resolved.pendingTriggers.isEmpty &&
    resolved.lifeOf q == ready.lifeOf q && linkAttackPower resolved link == power &&
    (resolved.poolOf p).resources == 8 - cost)

#guard spellbladeRunechantScenario "ARC_085_R" 4 == some true
#guard spellbladeRunechantScenario "ARC_086_Y" 3 == some true
#guard spellbladeRunechantScenario "ARC_087_B" 2 == some true

meta def reduceToRunechantScenario (name : String) (defense : Nat) : Option Bool := do
  let p := earlyAttacker
  let q := earlyDefender
  let hand := Zone.player q .hand
  let token := FabCards.ARC.runechantToken.id
  let state := ({ earlyBase with cards := throughArcDB }).setPool q { resources := 1 }
  let (withAttack, attack) ← earlyPlace state p (.player p .hand) "WTR_203_R"
  let (ready, reaction) ← earlyPlace withAttack q hand name
  let card ← ready.cardDefOf? reaction
  let stocked := createTokens ready q token 1
  let run (s : GameState) : Option GameState := do
    let attacking ← earlyAttack s (.playCard attack)
    let eligible ← earlySteps attacking
      (⟨.player q, .defendDone⟩ :: (earlyPass ++ [⟨.player p, .pass⟩]))
    earlySteps eligible
      [⟨.player q, .playCard reaction⟩, ⟨.player q, .pass⟩, ⟨.player p, .pass⟩]
  let paid ← run ready
  let waived ← run stocked
  let link ← paid.combat.bind CombatChain.activeLink?
  let discountedLink ← waived.combat.bind CombatChain.activeLink?
  pure ((modifiedCardPlayCost (createTokens ready p token 1) q card).resources == 1 &&
    (modifiedCardPlayCost stocked q card).resources == 0 &&
    (paid.poolOf q).resources == 0 && (waived.poolOf q).resources == 1 &&
    controlledPermanentCount paid q token == 1 && controlledPermanentCount waived q token == 2 &&
    linkTotalDefense paid link == defense && linkTotalDefense waived discountedLink == defense)

#guard reduceToRunechantScenario "ARC_088_R" 4 == some true
#guard reduceToRunechantScenario "ARC_089_Y" 3 == some true
#guard reduceToRunechantScenario "ARC_090_B" 2 == some true

meta def oathArknightScenario (name : String) (bonus : Int) : Option Bool := do
  let p := earlyAttacker
  let hand := Zone.player p .hand
  let token := FabCards.ARC.runechantToken.id
  let (withOath, oath) ← earlyPlace { earlyBase with cards := throughArcDB } p hand name
  let (withSword, sword) ← earlyPlace withOath p (.player p .weapon) "ARC_077"
  let (withGeneric, generic) ← earlyPlace withSword p hand "WTR_203_R"
  let (ready, runeblade) ← earlyPlace withGeneric p hand "ARC_085_R"
  let buffed ← earlySteps ready (⟨.player p, .playCard oath⟩ :: earlyPass)
  let (withProxy, proxy) ← addObject buffed .stack
    { kind := .attackProxy sword none, owner := p, controller := p, timestamp := ⟨0⟩ } .top
  let info : LayerInfo := { controller := p }
  let (genericInfo, waiting) := consumeNextAttackEffects buffed generic info
  let afterGeneric := { buffed with activeEffects := waiting }
  let (cardInfo, used) := consumeNextAttackEffects afterGeneric runeblade info
  let swordInfo := (consumeNextAttackEffects withProxy proxy info).1
  let expired := (consumeNextAttackEffects buffed.finishTurnEffects runeblade info).1
  pure (genericInfo.attackPowerBonus == 0 && cardInfo.attackPowerBonus == bonus &&
    swordInfo.attackPowerBonus == bonus && used.isEmpty && expired.attackPowerBonus == 0 &&
    (buffed.poolOf p).actionPoints == 4 && (buffed.poolOf p).resources == 6 &&
    controlledPermanentCount buffed p token == 1)

#guard oathArknightScenario "ARC_091_R" 3 == some true
#guard oathArknightScenario "ARC_092_Y" 2 == some true
#guard oathArknightScenario "ARC_093_B" 1 == some true

meta def discountedRunebladeScenario (name : String) (cost power : Nat) (goAgain : Bool) :
    Option Bool := do
  let p := earlyAttacker
  let q := earlyDefender
  let token := FabCards.ARC.runechantToken.id
  let (ready, attack) ← earlyPlace { earlyBase with cards := throughArcDB }
    p (.player p .hand) name
  let card ← ready.cardDefOf? attack
  let oneRune := createTokens ready p token 1
  let enough := createTokens oneRune p token cost
  let charging ← earlySteps oneRune [⟨.player p, .playCard attack⟩]
  let defending ← earlyAttack ready (.playCard attack)
  let link ← defending.combat.bind CombatChain.activeLink?
  pure ((modifiedCardPlayCost ready p card).resources == cost &&
    (modifiedCardPlayCost (createTokens ready q token 1) p card).resources == cost &&
    (modifiedCardPlayCost oneRune p card).resources == cost - 1 &&
    (modifiedCardPlayCost enough p card).resources == 0 &&
    (charging.poolOf p).resources == 8 - (cost - 1) &&
    charging.pendingTriggers.length == 1 && linkAttackPower defending link == power &&
    linkHasKeyword defending link .goAgain == goAgain)

#guard discountedRunebladeScenario "ARC_094_R" 3 6 false == some true
#guard discountedRunebladeScenario "ARC_095_Y" 3 5 false == some true
#guard discountedRunebladeScenario "ARC_096_B" 3 4 false == some true

meta def drawnToDarkDimensionScenario (name : String) (power : Nat) : Option Bool := do
  let p := earlyAttacker
  let hand := Zone.player p .hand
  let deck := Zone.player p .deck
  let token := FabCards.ARC.runechantToken.id
  let (withCard, attack) ← earlyPlace { earlyBase with cards := throughArcDB } p hand name
  let (ready, _) ← earlyPlace withCard p deck "WTR_218_R"
  let card ← ready.cardDefOf? attack
  let oneRune := createTokens ready p token 1
  let paid ← earlySteps ready [⟨.player p, .playCard attack⟩]
  let attacked ← earlySteps paid earlyPass
  let trigger ← attacked.pendingTriggers.head?
  let done ← earlySteps attacked
    ([⟨.player p, .pickTriggerStart p⟩, ⟨.player p, .pickTrigger trigger.id⟩] ++ earlyPass)
  let drawn ← (done.zone hand).head?
  let link ← done.combat.bind CombatChain.activeLink?
  pure ((modifiedCardPlayCost oneRune p card).resources == 1 &&
    paid.pendingTriggers.isEmpty && (paid.zone hand).isEmpty &&
    (attacked.zone hand).isEmpty && (attacked.zone deck).length == 1 &&
    (done.zone deck).isEmpty && (done.cardDefOf? drawn).any (fun c => c.id == ⟨"WTR_218_R"⟩) &&
    linkAttackPower done link == power)

#guard drawnToDarkDimensionScenario "ARC_097_R" 3 == some true
#guard drawnToDarkDimensionScenario "ARC_098_Y" 2 == some true
#guard drawnToDarkDimensionScenario "ARC_099_B" 1 == some true
#guard discountedRunebladeScenario "ARC_100_R" 3 4 true == some true
#guard discountedRunebladeScenario "ARC_101_Y" 3 3 true == some true
#guard discountedRunebladeScenario "ARC_102_B" 3 2 true == some true
#guard spellbladeRunechantScenario "ARC_103_R" 4 1 1 == some true
#guard spellbladeRunechantScenario "ARC_104_Y" 3 1 1 == some true
#guard spellbladeRunechantScenario "ARC_105_B" 2 1 1 == some true

meta def bloodspillInvocationScenario (name : String) (count : Nat) : Option Bool := do
  let p := earlyAttacker
  let q := earlyDefender
  let arena := Zone.player p .permanent
  let token := FabCards.ARC.runechantToken.id
  let (withCard, invocation) ← earlyPlace { earlyBase with cards := throughArcDB }
    p (.player p .hand) name
  let (withAttack, attack) ← earlyPlace withCard p (.player p .hand) "WTR_203_R"
  let (withWeapon, sword) ← earlyPlace withAttack p (.player p .weapon) "WTR_115"
  let (ready, enemyAttack) ← earlyPlace withWeapon q (.player q .hand) "WTR_203_R"
  let buffed ← earlySteps ready (⟨.player p, .playCard invocation⟩ :: earlyPass)
  let aura ← (buffed.zone arena).head?
  let attacking ← earlyAttack buffed (.playCard attack)
  let hit ← earlyDamage attacking
  let hitTrigger ← hit.pendingTriggers.head?
  let resolveHit ← earlySteps hit
    ([⟨.player p, .pickTriggerStart p⟩, ⟨.player p, .pickTrigger hitTrigger.id⟩] ++ earlyPass)
  let weaponHit ← (earlyAttack buffed (.attackWeapon sword)).bind earlyDamage
  let enemyTurn := { (buffed.setPool q { actionPoints := 1, resources := 4 }) with
    active := some q, pending := [.priority q 0] }
  let enemyPass : List Action := [⟨.player q, .pass⟩, ⟨.player p, .pass⟩]
  let incoming ← earlySteps enemyTurn (⟨.player q, .playCard enemyAttack⟩ :: enemyPass ++ enemyPass)
  let physical ← earlySteps incoming (⟨.player p, .defendDone⟩ :: enemyPass ++ enemyPass)
  let received (s : GameState) := s.pendingTriggers.any fun trigger =>
    trigger.source == aura && trigger.effect == .prim (.destroy .self_)
  let arcane (s : GameState) : Option GameState :=
    ((advance 64 { s with pending :=
      [.run q attack false [] [.prim (.dealDamage .arcane (.seated p) (.const 1))],
        .priority p 0] } []).toOption).map Prod.fst
  let unprotected ← arcane buffed
  let (barrierBoard, _) ← earlyPlace buffed p (.player p .head) "ARC_079"
  let prevention ← arcane barrierBoard
  let .chooseReplacement defender .prevention [barrier] true :: _ := prevention.pending | none
  let prevented ← earlySteps prevention [⟨.player p, .pickReplacement (some barrier)⟩]
  let declined ← earlySteps prevention [⟨.player p, .pickReplacement none⟩]
  pure ((buffed.poolOf p).actionPoints == 4 && (buffed.poolOf p).resources == 7 &&
    hitTrigger.source == aura && controlledPermanentCount resolveHit p token == count &&
    (resolveHit.zone arena).length == count && weaponHit.pendingTriggers.isEmpty &&
    weaponHit.zone arena == [aura] && physical.lifeOf p < buffed.lifeOf p && received physical &&
    unprotected.lifeOf p == buffed.lifeOf p - 1 && received unprotected &&
    defender == p && prevented.lifeOf p == buffed.lifeOf p && !received prevented &&
    declined.lifeOf p == buffed.lifeOf p - 1 && received declined)

#guard bloodspillInvocationScenario "ARC_106_R" 3 == some true
#guard bloodspillInvocationScenario "ARC_107_Y" 2 == some true
#guard bloodspillInvocationScenario "ARC_108_B" 1 == some true

meta def readRunesScenario (name : String) (count : Nat) : Option Bool := do
  let p := earlyAttacker
  let q := earlyDefender
  let token := FabCards.ARC.runechantToken.id
  let (ready, action) ← earlyPlace { earlyBase with cards := throughArcDB }
    p (.player p .hand) name
  let paid ← earlySteps ready [⟨.player p, .playCard action⟩]
  let done ← earlySteps paid earlyPass
  pure ((paid.poolOf p).resources == 8 && (done.poolOf p).actionPoints == 3 &&
    controlledPermanentCount paid p token == 0 && controlledPermanentCount done p token == count &&
    done.pendingTriggers.isEmpty && done.lifeOf q == ready.lifeOf q)

#guard readRunesScenario "ARC_109_R" 3 == some true
#guard readRunesScenario "ARC_110_Y" 2 == some true
#guard readRunesScenario "ARC_111_B" 1 == some true

#guard ((earlyPrintingCardId? "ARC112-T").bind throughArcDB.find?).any
  (fun card => card.front.hasType .token && card.front.hasSubtype .aura && card.status == .full)
#guard (throughArcDB.cards.filter (fun card => card.id == ⟨"ARC_112"⟩)).length == 1

#guard ((earlyPrintingCardId? "ARC113").bind throughArcDB.find?).any
  (fun card => card.front.life == some 30 && card.front.intellect == some 4 && card.status == .full)

meta def kanoScenario (heroName : String) (offTurn : Bool) : Option Bool := do
  let p := earlyAttacker
  let q := earlyDefender
  let deck := Zone.player p .deck
  let banished := Zone.player p .banished
  let initial := (earlyBase.setPool p { resources := 6 })
  let state := { initial with cards := throughArcDB, active := some (if offTurn then q else p) }
  let (withHero, hero) ← earlyPlace state p (.player p .hero) heroName
  let (bottom, hidden) ← earlyPlace withHero p deck "WTR_203_R"
  let (ready, top) ← earlyPlace bottom p deck "WTR_221_R"
  let activate : Action := ⟨.player p, .activateAbility hero 0 none⟩
  let choose (card : Option ObjId) : Action := ⟨.player p, .pickShuffleCard card⟩
  let choice ← earlySteps ready (activate :: earlyPass)
  let ineligible ← earlySteps bottom (activate :: earlyPass)
  let declined ← earlySteps choice [choose none]
  let exiled ← earlySteps choice [choose (some top), choose none]
  let permission ← (exiled.zone banished).head?
  let playing ← match exiled.pending with
    | .priority player _ :: _ =>
      if player == p then some exiled else earlySteps exiled [⟨.player player, .pass⟩]
    | _ => none
  let paid ← earlySteps playing [⟨.player p, .playCard permission⟩]
  let resolved ← earlySteps paid earlyPass
  pure ((view p choice).selectionChoices == [(top, ⟨"WTR_221_R"⟩)] &&
    (view q choice).selectionChoices.isEmpty &&
    (view p ineligible).selectionChoices == [(hidden, ⟨"WTR_203_R"⟩)] &&
    !(deckSearchVisible p choice deck) && !(deckSearchVisible q choice deck) &&
    (earlySteps choice [choose (some hidden)]).isNone &&
    (earlySteps ineligible [choose (some hidden)]).isNone &&
    declined.zone deck == [top, hidden] && (declined.zone banished).isEmpty &&
    exiled.zone deck == [hidden] && (exiled.obj? permission).any (fun obj => !obj.faceDown) &&
    canPlayFromBanished exiled p permission true && canPlayCard playing p permission &&
    !canPlayCard playing.finishTurnEffects p permission &&
    (exiled.poolOf p).resources == 3 && (paid.poolOf p).resources == 0 &&
    (paid.poolOf p).actionPoints == 0 &&
    (resolved.poolOf p).actionPoints == (if offTurn then 0 else 1))

#guard kanoScenario "ARC_113" false == some true
#guard kanoScenario "ARC_113" true == some true

#guard ((earlyPrintingCardId? "ARC114").bind throughArcDB.find?).any
  (fun card => card.front.life == some 15 && card.front.intellect == some 4 && card.status == .full)
#guard (earlyPrintingCardId? "HER016-P") == some ⟨"ARC_114"⟩
#guard (earlyPrintingCardId? "HER020-P") == some ⟨"ARC_113"⟩
#guard kanoScenario "ARC_114" false == some true
#guard kanoScenario "ARC_114" true == some true

#guard ((earlyPrintingCardId? "ARC115").bind throughArcDB.find?).any
  (fun card => card.front.hasType .weapon && card.front.hasSubtype .staff && card.status == .full)

meta def crucibleAetherweaveScenario : Option Bool := do
  let p := earlyAttacker
  let q := earlyDefender
  let hand := Zone.player p .hand
  let damageCard (name : String) (kind : DamageKind) (amount : Int := 2) : CardDef :=
    { id := ⟨name⟩
      front :=
        { name := name
          types := [.action]
          cost := some { actionPoints := 1 }
          playEffect := some { body := .prim (.dealDamage kind .opposingHero (.const amount)) } } }
  let arcane := damageCard "Crucible arcane fixture" .arcane
  let physical := damageCard "Crucible physical fixture" .physical
  let zeroSpell := damageCard "Crucible zero damage fixture" .arcane 0
  let cards : CardDB := ⟨arcane :: physical :: zeroSpell :: throughArcDB.cards⟩
  let (withStaff, staff) ← earlyPlace { earlyBase with cards } p (.player p .weapon) "ARC_115"
  let (withPhysical, punch) ← earlyPlace withStaff p hand physical.id.val
  let (withFirst, first) ← earlyPlace withPhysical p hand arcane.id.val
  let (withSecond, second) ← earlyPlace withFirst p hand arcane.id.val
  let (ready, zero) ← earlyPlace withSecond p hand zeroSpell.id.val
  let activate : Action := ⟨.player p, .activateAbility staff 0 none⟩
  let cast (s : GameState) (id : ObjId) :=
    earlySteps s (⟨.player p, .playCard id⟩ :: earlyPass)
  let primed ← earlySteps ready (activate :: earlyPass)
  let skip ← cast primed punch
  let boosted ← cast skip first
  let spent ← cast boosted second
  let expired ← cast primed.finishTurnEffects first
  let zeroed ← cast primed zero
  let afterZero ← cast zeroed first
  let waiting (s : GameState) := s.activeEffects.any (fun effect => effect.op == .addToNextArcaneCard 1)
  pure (!(canAttackWithWeapon ready p staff) && (primed.poolOf p).resources == 7 &&
    (primed.poolOf p).actionPoints == 4 && (earlySteps primed [activate]).isNone &&
    waiting primed && waiting skip && !waiting boosted &&
    skip.lifeOf q == ready.lifeOf q - 2 && boosted.lifeOf q == skip.lifeOf q - 3 &&
    spent.lifeOf q == boosted.lifeOf q - 2 && expired.lifeOf q == ready.lifeOf q - 2 &&
    zeroed.lifeOf q == ready.lifeOf q && !waiting zeroed &&
    afterZero.lifeOf q == ready.lifeOf q - 2)

#guard crucibleAetherweaveScenario == some true

#guard ((earlyPrintingCardId? "ARC116").bind throughArcDB.find?).any
  (fun card => card.front.hasSubtype .legs && card.front.keywords.contains (.arcaneBarrier 2) &&
    card.status == .full)

meta def stormStridersScenario : Option Bool := do
  let p := earlyAttacker
  let q := earlyDefender
  let hand := Zone.player p .hand
  let wizard : CardDef :=
    { id := ⟨"Storm Striders fixture"⟩
      front :=
        { name := "Storm Striders fixture"
          supertypes := [.class_ .wizard]
          types := [.action]
          cost := some { actionPoints := 1, resources := 1 }
          keywords := [.goAgain] } }
  let cards : CardDB := ⟨wizard :: throughArcDB.cards⟩
  let (geared, boots) ← earlyPlace { earlyBase with cards } p (.player p .legs) "ARC_116"
  let (withOther, nonWizard) ← earlyPlace geared p hand "WTR_221_R"
  let (withFirst, first) ← earlyPlace withOther p hand wizard.id.val
  let (ready, second) ← earlyPlace withFirst p hand wizard.id.val
  let ordinary (id : ObjId) : Action := ⟨.player p, .playCard id⟩
  let instant (id : ObjId) : Action := ⟨.player p, .playCard id true⟩
  let activate : Action := ⟨.player p, .activateAbility boots 0 none⟩
  let primed ← earlySteps ready (activate :: earlyPass)
  let otherPlayed ← earlySteps primed (ordinary nonWizard :: earlyPass)
  let (ordinaryPaid, _) ← (step 64 primed (ordinary first)).toOption
  let (instantPaid, _) ← (step 64 primed (instant first)).toOption
  let resolved ← earlySteps instantPaid earlyPass
  let offTurn := { ready.setPool p { resources := 3 } with active := some q }
  let offPrimed ← earlySteps offTurn (activate :: earlyPass)
  let offReady ← match offPrimed.pending with
    | .priority player _ :: _ =>
      if player == p then some offPrimed else earlySteps offPrimed [⟨.player player, .pass⟩]
    | _ => none
  let offResolved ← earlySteps offReady (instant first :: earlyPass)
  let hasTiming (s : GameState) := s.activeEffects.any (fun effect =>
    effect.appliesNextInstant p wizard.front)
  pure (!canPlayCard ready p first true && !(legalActions ready).contains (instant first) &&
    canPlayCard primed p first && canPlayCard primed p first true &&
    (legalActions primed).contains (ordinary first) && (legalActions primed).contains (instant first) &&
    (primed.zone (.player p .legs)).isEmpty && (primed.zone (.player p .graveyard)).length == 1 &&
    (primed.poolOf p).resources + 1 == (ready.poolOf p).resources &&
    !canPlayCard primed p nonWizard true && hasTiming otherPlayed &&
    !canPlayCard primed.finishTurnEffects p first true &&
    (ordinaryPaid.poolOf p).actionPoints + 1 == (primed.poolOf p).actionPoints &&
    (instantPaid.poolOf p).actionPoints == (primed.poolOf p).actionPoints &&
    (instantPaid.poolOf p).resources + 1 == (primed.poolOf p).resources &&
    !hasTiming ordinaryPaid && !hasTiming instantPaid &&
    !canPlayCard resolved p second true && (resolved.nonAttackActionsThisTurn.contains p) &&
    !canPlayCard offReady p first && canPlayCard offReady p first true &&
    (offResolved.poolOf p).actionPoints == 0 && (offResolved.poolOf p).resources == 1)

#guard stormStridersScenario == some true

#guard
  (["HER001-P", "HER002-P", "HER003-P", "HER004-P"].map fun number =>
    ((earlyPrintingCardId? number).bind throughWtrDB.find?).map (·.front.name)) ==
  ["Rhinar, Reckless Rampage", "Bravo, Showstopper", "Katsu, the Wanderer", "Dorinthea Ironsong"].map some
