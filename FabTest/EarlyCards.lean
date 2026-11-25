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

meta def adultDashSetupScenario : Option Bool := do
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
      pending := [.chooseLoadout player, .revealLoadouts] }
  let (hero, _) ← earlyPlace setup player (.player player .hero) "ARC_001"
  let loaded ← (List.range 59).foldlM
    (fun s _ => (earlyPlace s player deck "WTR_203_R").map Prod.fst) hero
  let (withExpensive, wrong) ← earlyPlace loaded player inventory "Dash-test-expensive"
  let (ready, allowed) ← earlyPlace withExpensive player inventory "Dash-test-item"
  let selected ← earlySteps ready [⟨.player player, .loadoutEquip allowed⟩]
  let id ← (selected.zone permanent).head?
  let revealed ← earlySteps selected [⟨.player player, .loadoutDone⟩]
  pure (!loadoutCanFinish ready player && loadoutCanFinish selected player &&
    loadoutEquipDest? ready player wrong == none && (selected.obj? id).any (·.faceDown) &&
    viewZone opponent selected permanent == .countOnly 0 &&
    viewZone opponent selected deck == .countOnly 60 &&
    (revealed.obj? id).any (fun obj => !obj.faceDown) && (revealed.zone deck).length == 59)

#guard adultDashSetupScenario == some true

#guard
  (["HER001-P", "HER002-P", "HER003-P", "HER004-P"].map fun number =>
    ((earlyPrintingCardId? number).bind throughWtrDB.find?).map (·.front.name)) ==
  ["Rhinar, Reckless Rampage", "Bravo, Showstopper", "Katsu, the Wanderer", "Dorinthea Ironsong"].map some
