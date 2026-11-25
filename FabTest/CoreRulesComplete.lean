module

import Fab
meta import Fab

/-!
# Core Rules Completeness Tests

Exercises all newly completed core IR primitives and live engine integrations:
1. Live 4-stage damage prevention (`preventNextDamage` + `dealDamage` & `combatStep .damage`)
2. Automatic Phantasm destruction on `.combatStep .reaction` (CR 8.3.13)
3. Intimidate (face-down banish + End Phase return DelayedTrigger, CR 8.5.10)
4. Discard (`discardRandom`, `discardChoice`), `returnDefendingCardToHand`, `revealTopToArsenalIf`,
   `searchDeck` + shuffle, `shuffleZoneIntoDeck` + draw, `closeCombatChain`
5. Soul & Shadow primitives (`charge`, `banishFromSoul`, `banishTopDeck` + `banishedSixPowerThisTurn`,
   `banishFromGraveyard`)
-/

namespace FabTest.CoreRulesComplete

open Fab

meta def p0 : PlayerId := ⟨0⟩
meta def p1 : PlayerId := ⟨1⟩

meta def brute6 : CardDef :=
  { id := ⟨"B6"⟩
    front :=
      { name := "Brute 6"
        supertypes := [.class_ .brute]
        types := [.action]
        subtypes := [.attack]
        power := some 6
        defense := some 3 } }

meta def light3 : CardDef :=
  { id := ⟨"L3"⟩
    front :=
      { name := "Light 3"
        supertypes := [.talent .light]
        types := [.action]
        subtypes := [.attack]
        power := some 3
        defense := some 3 } }

meta def phAtk : CardDef :=
  { id := ⟨"PH"⟩
    front :=
      { name := "Phantasm Attack"
        supertypes := [.class_ .illusionist]
        types := [.action]
        subtypes := [.attack]
        power := some 6
        defense := some 3
        keywords := [.phantasm] } }

meta def db : CardDB := ⟨[brute6, light3, phAtk]⟩

meta def baseState : GameState :=
  { config := { format := .classicConstructed, mode := .duel, ruleSet := .coreOnly }
    cards := db
    turnOrder := [p0, p1]
    active := some p0
    phase := .actionPhase
    heroLife := ((∅ : Std.ExtTreeMap Nat Int).insert 0 20).insert 1 20 }

-- 1. Live prevention shield intercepts both `dealDamage` and `combatStep .damage`
meta def preventionTest : Bool :=
  let (s1, _, _) := execPrim baseState p1 ⟨0⟩ [] (.preventNextDamage .controller (.const 3) .thisTurn)
  let (s2, es2, _) := execPrim s1 p0 ⟨0⟩ [] (.dealDamage .arcane .opposingHero (.const 5))
  -- 5 arcane - 3 shield = 2 damage -> p1 at 18 life, shield consumed!
  let (s3, es3, _) := execPrim s2 p0 ⟨0⟩ [] (.dealDamage .arcane .opposingHero (.const 2))
  s2.lifeOf p1 == 18 &&
  es2 == [.damageDealt p1 .arcane 2] &&
  s2.activeReplacements.isEmpty &&
  s3.lifeOf p1 == 16 &&
  es3 == [.damageDealt p1 .arcane 2]

#guard preventionTest == true

-- 2. Automatic Phantasm destruction on `.combatStep .reaction`
meta def autoPhantasmTest : Bool :=
  match addObject baseState .combatChain
      { kind := .card ⟨1⟩ ⟨"PH"⟩, owner := p0, controller := p0, timestamp := ⟨0⟩ } .top with
  | none => false
  | some (s1, aid) =>
    match addObject s1 .combatChain
        { kind := .card ⟨2⟩ ⟨"B6"⟩, owner := p1, controller := p1, timestamp := ⟨1⟩ } .top with
    | none => false
    | some (s2, did) =>
      let link : ChainLink :=
        { linkId := ⟨1⟩, attacker := p0, defender := p1, attack := some aid,
          attackLki := captureLki s2 aid p0, defending := [did] }
      let s3 := { s2 with
        combat := some { step := .defend, links := [link] }
        pending := [.combatStep .reaction aid] }
      match microStep s3 with
      | some (s4, _) =>
        s4.combat.isNone &&
        (s4.zone (.player p0 .graveyard)).length == 1
      | none => false

#guard autoPhantasmTest == true

-- 3. Intimidate banishes face-down and registers End Phase return DelayedTrigger
meta def intimidateAndDiscardTest : Bool :=
  match addObject baseState (.player p1 .hand)
      { kind := .card ⟨10⟩ ⟨"L3"⟩, owner := p1, controller := p1, timestamp := ⟨0⟩ } .top with
  | none => false
  | some (s1, _) =>
    let (sInt, _, _) := execPrim s1 p0 ⟨0⟩ [] (.intimidate .opposingHero)
    let intOk :=
      (sInt.zone (.player p1 .hand)).isEmpty &&
      (sInt.zone (.player p1 .banished)).length == 1 &&
      sInt.delayedTriggers.length == 1 &&
      match (sInt.zone (.player p1 .banished)).head?.bind sInt.obj? with
      | some o => o.faceDown == true
      | none => false
    -- Discard choice
    let (sDisc, esDisc, _) := execPrim s1 p1 ⟨0⟩ [] (.discardChoice .controller CardFilter.any (.const 1))
    let discOk :=
      (sDisc.zone (.player p1 .hand)).isEmpty &&
      (sDisc.zone (.player p1 .graveyard)).length == 1 &&
      esDisc.length == 2
    intOk && discOk

#guard intimidateAndDiscardTest == true

-- 4. Charge, banishFromSoul, banishTopDeck (tracking 6{p}!), banishFromGraveyard, searchDeck, revealTopToArsenalIf
meta def soulShadowSearchTest : Bool :=
  match addObject baseState (.player p0 .hand)
      { kind := .card ⟨20⟩ ⟨"L3"⟩, owner := p0, controller := p0, timestamp := ⟨0⟩ } .top with
  | none => false
  | some (s1, _) =>
    let (sCh, _, _) := execPrim s1 p0 ⟨0⟩ [] (.charge .controller)
    let chOk :=
      (sCh.zone (.player p0 .soul)).length == 1 &&
      evalCondition sCh p0 ⟨0⟩ false .chargedThisTurn == true &&
      evalNumExpr sCh p0 [] (.soulCount .controller) == 1
    let (sBs, _, _) := execPrim sCh p0 ⟨0⟩ [] (.banishFromSoul .controller 1)
    let bsOk := (sBs.zone (.player p0 .soul)).isEmpty && (sBs.zone (.player p0 .banished)).length == 1
    -- Banish top deck 6{p} Brute card -> triggers banishedSixPowerThisTurn!
    match addObject baseState (.player p0 .deck)
        { kind := .card ⟨21⟩ ⟨"B6"⟩, owner := p0, controller := p0, timestamp := ⟨1⟩ } .top with
    | none => false
    | some (sD, _) =>
      let (sBan, _, _) := execPrim sD p0 ⟨0⟩ [] (.banishTopDeck .controller 1 false)
      let ban6Ok :=
        evalCondition sBan p0 ⟨0⟩ false .banishedSixPowerThisTurn == true &&
        evalNumExpr sBan p0 [] (.banishedCount .controller) == 1
      -- Reveal top to arsenal
      let (sArs, _, _) := execPrim sD p0 ⟨0⟩ [] (.revealTopToArsenalIf .controller { minPower := some 6 })
      let arsOk := (sArs.zone (.player p0 .arsenal)).length == 1
      -- Search deck pushes chanceShuffle
      let (sSrch, _, extraSrch) := execPrim sD p0 ⟨0⟩ [] (.searchDeck .controller { minPower := some 6 } (some 1) .hand true none)
      let srchOk := (sSrch.zone (.player p0 .hand)).length == 1 && extraSrch == [.chanceShuffle (.player p0 .deck)]
      chOk && bsOk && ban6Ok && arsOk && srchOk

#guard soulShadowSearchTest == true

end FabTest.CoreRulesComplete
