module

import FabCards
import Fab.Engine.Step
meta import FabCards
meta import Fab.Engine.Step

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
