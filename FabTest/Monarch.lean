module

import Fab
import FabCards
meta import Fab
meta import FabCards

/-!
# Monarch (MON) card catalog and rules scenarios

Checks the Monarch catalog (`FabCards.monDB`) and exercises selected rules and card effects:
1. Catalog completeness: 307 logical cards, 1-to-1 ID match with `FabCards.MON.Meta.allMeta`,
   kernel-verified `FabCards.monDB_wf`.
2. Light Illusionist (Prism): *Herald of Erudition* automatic Phantasm pop vs *Smash with Big Tree*,
   *Spectral Shield* (Ward 1) mandatory damage prevention, *Arc Light Sentinel* (Spectra) chain close,
   *Prismatic Shield* token creation.
3. Light Warrior (Boltyn): *Tome of Divinity* (2 cards vs 3 cards after `charge`), Soul count & banish.
4. Shadow Brute (Levia): *Endless Maw* face-up vs face-down Blood Debt life loss, 6{p} banish flag
   (`banishedSixPowerThisTurn`), and *Blasmophet, the Soul Harvester* End Phase life reset.
5. Shadow Runeblade (Chane): *Soul Shackle* top-deck banish, *Ebon Fold* (Spellvoid 2) arcane prevention,
   *Ursur, the Soul Reaper* Ally.
6. Light Landmark & Generic: *Great Library of Solana* Landmark uniqueness in GSP,
   *Belittle* → *Minnowism* deck search + shuffle, *Captain's Call* modal play.
-/

namespace FabTest.Monarch

open Fab
open FabCards
open FabCards.MON

meta def p0 : PlayerId := ⟨0⟩
meta def p1 : PlayerId := ⟨1⟩

meta def monBaseState : GameState :=
  { config := { format := .classicConstructed, mode := .duel, ruleSet := .coreOnly }
    cards := monDB
    turnOrder := [p0, p1]
    active := some p0
    phase := .actionPhase
    pools := ((∅ : Std.ExtTreeMap Nat AssetPool).insert 0 { actionPoints := 1, resources := 4 }).insert 1 { actionPoints := 1, resources := 4 }
    heroLife := ((∅ : Std.ExtTreeMap Nat Int).insert 0 40).insert 1 40 }

-- 1. Catalog integrity: 307 cards and exact ID match with generated metadata
#guard monDB.cards.length == 307
#guard monDB.cards.all (fun c => c.status != .todo)
#guard monDB.cards.map (·.id) == FabCards.MON.Meta.allMeta.map (·.id)
#guard (monDB.find? ⟨"MON_000"⟩).map (·.front.name) == some "Great Library of Solana"
#guard (monDB.find? ⟨"MON_001"⟩).map (·.front.name) == some "Prism, Sculptor of Arc Light"
#guard (monDB.find? ⟨"MON_029"⟩).map (·.front.name) == some "Ser Boltyn, Breaker of Dawn"
#guard (monDB.find? ⟨"MON_104"⟩).map (·.front.name) == some "Spectral Shield"
#guard (monDB.find? ⟨"MON_119"⟩).map (·.front.name) == some "Levia, Shadowborn Abomination"
#guard (monDB.find? ⟨"MON_153"⟩).map (·.front.name) == some "Chane, Bound by Shadow"
#guard (monDB.find? ⟨"MON_186"⟩).map (·.front.name) == some "Soul Shackle"
#guard (monDB.find? ⟨"MON_219"⟩).map (·.front.name) == some "Blasmophet, the Soul Harvester"
#guard (monDB.find? ⟨"MON_220"⟩).map (·.front.name) == some "Ursur, the Soul Reaper"
#guard allCardsDB.cards.length == 532
#guard (allCardsDB.cards.map CardDef.uniqueKey).eraseDups.length == allCardsDB.cards.length
#guard (allCardsDB.find? ⟨"WTR_224_Y"⟩).map (·.sets) == some [.wtr, .mon]

/-- Kernel-checked `CardDB.WF` witness for the full 307-card Monarch database. -/
theorem monDB_is_wf : monDB.WF := monDB_wf

-- 2. Light Illusionist (Prism): Herald of Erudition Phantasm pop + Spectral Shield Ward 1 + Spectra
meta def prismScenario : Bool :=
  -- (a) Herald of Erudition (MON_004_Y) defended by 6{p} Smash with Big Tree (MON_227_Y) -> auto Phantasm pop
  let phantasmOk :=
    match addObject monBaseState .combatChain
        { kind := .card ⟨1⟩ ⟨"MON_004_Y"⟩, owner := p0, controller := p0, timestamp := ⟨0⟩ } .top with
    | none => false
    | some (s1, aid) =>
      match addObject s1 .combatChain
          { kind := .card ⟨2⟩ ⟨"MON_227_Y"⟩, owner := p1, controller := p1, timestamp := ⟨1⟩ } .top with
      | none => false
      | some (s2, did) =>
        let link : ChainLink :=
          { linkId := ⟨1⟩, attacker := p0, defender := p1, attack := some aid,
            attackLki := captureLki s2 aid p0, defending := [did] }
        let s3 := { s2 with
          combat := some { step := .defend, links := [link] }
          pending := [.combatStep .reaction aid] }
        match microStep s3 with
        | some (s4, _) => s4.combat.isNone && (s4.zone (.player p0 .graveyard)).length == 1
        | none => false
  -- (b) Prismatic Shield Red (MON_092_R) creates 3 Spectral Shield tokens + Ward 1 mandatory prevention
  let wardOk :=
    match MON_092_R.front.playEffect with
    | none => false
    | some eff =>
      let (sTok, _, _) := execPrim monBaseState p1 ⟨0⟩ [] (.createToken .controller ⟨"MON_104"⟩ 3)
      match sTok.zone (.player p1 .permanent) with
      | sid :: _ =>
        let wardRepl : ReplacementEffect :=
          { id := 1, source := sid, controller := p1, stage := .prevention,
            action := .wardPrevent 1, optional := false }
        let sArmed := { sTok with activeReplacements := [wardRepl] }
        let (sAfter, es) := applyDamageWithPrevention sArmed p1 .arcane 3
        -- 3 arcane - Ward 1 = 2 damage (p1 at 38), 1 Spectral Shield destroyed (2 remaining)
        eff.body == .prim (.createToken .controller ⟨"MON_104"⟩ 3) &&
        sAfter.lifeOf p1 == 38 &&
        (sAfter.zone (.player p1 .permanent)).length == 2 &&
        es == [.damageDealt p1 .arcane 2]
      | [] => false
  -- (c) Arc Light Sentinel (MON_005_Y) Spectra forced close
  let spectraOk :=
    match addObject monBaseState (.player p1 .permanent)
        { kind := .card ⟨5⟩ ⟨"MON_005_Y"⟩, owner := p1, controller := p1, timestamp := ⟨2⟩ } .top with
    | none => false
    | some (s1, auraId) =>
      let s2 := { s1 with combat := some { step := .attack, links := [] } }
      let (s3, _) := applySpectraClose s2 auraId
      s3.combat.isNone && (s3.zone (.player p1 .graveyard)).length == 1
  phantasmOk && wardOk && spectraOk

#guard prismScenario == true

-- 3. Light Warrior (Boltyn): Charge + Tome of Divinity (2 vs 3 cards) + Soul banish
meta def boltynScenario : Bool :=
  match addObject monBaseState (.player p0 .hand)
      { kind := .card ⟨10⟩ ⟨"MON_042_R"⟩, owner := p0, controller := p0, timestamp := ⟨0⟩ } .top with
  | none => false
  | some (s1, _) =>
    -- Before charge: Tome of Divinity evaluates to draw 2
    let noCharge := evalCondition s1 p0 ⟨0⟩ false .chargedThisTurn == false
    -- Charge Bolt of Courage into Soul
    let (sCh, _, _) := execPrim s1 p0 ⟨0⟩ [] (.charge .controller)
    let charged := evalCondition sCh p0 ⟨0⟩ false .chargedThisTurn == true &&
      evalNumExpr sCh p0 [] (.soulCount .controller) == 1
    -- Tome of Divinity (MON_065_Y) after charge pushes draw 3
    let tomeDraw3 :=
      match MON_065_Y.front.playEffect with
      | some ed =>
        let (sRun, _) := interpRunStep sCh p0 ⟨0⟩ false [] [ed.body] []
        match sRun.pending with
        | .run _ _ _ _ [.prim (.draw .controller (.const 3))] :: _ => true
        | _ => false
      | none => false
    -- Banish from Soul
    let (sBan, _, _) := execPrim sCh p0 ⟨0⟩ [] (.banishFromSoul .controller 1)
    let soulBanished := (sBan.zone (.player p0 .soul)).isEmpty &&
      (sBan.zone (.player p0 .banished)).length == 1
    noCharge && charged && tomeDraw3 && soulBanished

#guard boltynScenario == true

-- 4. Shadow Brute (Levia): Blood Debt (face-up vs face-down), 6{p} banish tracking, Blasmophet Ally
meta def leviaScenario : Bool :=
  -- (a) Endless Maw (MON_126_R, Blood Debt): face-up loses 1 life, face-down loses 0
  let bdOk :=
    match addObject monBaseState (.player p0 .banished)
        { kind := .card ⟨20⟩ ⟨"MON_126_R"⟩, owner := p0, controller := p0, timestamp := ⟨0⟩, faceDown := false } .top with
    | none => false
    | some (sUp, _) =>
      match addObject monBaseState (.player p0 .banished)
          { kind := .card ⟨21⟩ ⟨"MON_126_R"⟩, owner := p0, controller := p0, timestamp := ⟨0⟩, faceDown := true } .top with
      | none => false
      | some (sDn, _) =>
        let (sUpAfter, _) := applyBloodDebt sUp p0
        let (sDnAfter, _) := applyBloodDebt sDn p0
        sUpAfter.lifeOf p0 == 39 && sDnAfter.lifeOf p0 == 40
  -- (b) Banishing 6{p} Smash with Big Tree (MON_227_Y) from graveyard flags banishedSixPowerThisTurn
  let ban6Ok :=
    match addObject monBaseState (.player p0 .graveyard)
        { kind := .card ⟨22⟩ ⟨"MON_227_Y"⟩, owner := p0, controller := p0, timestamp := ⟨1⟩ } .top with
    | none => false
    | some (sGy, _) =>
      let (sBan, _, _) := execPrim sGy p0 ⟨0⟩ [] (.banishFromGraveyard .controller CardFilter.any 1)
      evalCondition sBan p0 ⟨0⟩ false .banishedSixPowerThisTurn == true &&
      (sBan.zone (.player p0 .banished)).length == 1
  -- (c) Blasmophet (MON_219) Demon Ally life reset at End Phase
  let allyOk :=
    match addObject monBaseState (.player p0 .permanent)
        { kind := .token ⟨"MON_219"⟩, owner := p0, controller := p0, timestamp := ⟨2⟩, life := some 2 } .top with
    | none => false
    | some (sAlly, aid) =>
      let sReset := resetAlliesLife sAlly
      match sReset.obj? aid with
      | some o => o.life == some 6
      | none => false
  bdOk && ban6Ok && allyOk

#guard leviaScenario == true

-- 5. Shadow Runeblade (Chane): Soul Shackle top-deck banish + Ebon Fold Spellvoid 2 + Ursur Ally
meta def chaneScenario : Bool :=
  -- (a) Soul Shackle (MON_186) banishes top card of deck
  let shackleOk :=
    match addObject monBaseState (.player p0 .deck)
        { kind := .card ⟨30⟩ ⟨"MON_203_R"⟩, owner := p0, controller := p0, timestamp := ⟨0⟩ } .top with
    | none => false
    | some (s1, _) =>
      let (s2, _, _) := execPrim s1 p0 ⟨0⟩ [] (.banishTopDeck .controller 1 false)
      (s2.zone (.player p0 .deck)).isEmpty && (s2.zone (.player p0 .banished)).length == 1
  -- (b) Ebon Fold (MON_188, Spellvoid 2) prevents 2 arcane damage and destroys itself
  let svOk :=
    match addObject monBaseState (.player p1 .head)
        { kind := .card ⟨31⟩ ⟨"MON_188"⟩, owner := p1, controller := p1, timestamp := ⟨1⟩ } .top with
    | none => false
    | some (s1, eid) =>
      let svRepl : ReplacementEffect :=
        { id := 2, source := eid, controller := p1, stage := .prevention,
          action := .spellvoidPrevent 2, optional := false }
      let sArmed := { s1 with activeReplacements := [svRepl] }
      let (sAfter, _) := applyDamageWithPrevention sArmed p1 .arcane 2
      sAfter.lifeOf p1 == 40 &&
      (sAfter.zone (.player p1 .head)).isEmpty &&
      (sAfter.zone (.player p1 .graveyard)).length == 1
  -- (c) Ursur (MON_220) token exists and has base life 6 & power 6
  let ursurOk :=
    MON_220.front.power == some 6 &&
    MON_220.front.life == some 6 &&
    MON_220.front.hasSubtype .ally &&
    MON_220.front.hasSubtype .demon
  shackleOk && svOk && ursurOk

#guard chaneScenario == true

-- 6. Landmark Uniqueness (Great Library of Solana) + Belittle -> Minnowism Search + Captain's Call Modal
meta def landmarkAndGenericScenario : Bool :=
  -- (a) Two Great Library of Solana (MON_000) in arena -> GSP destroys older one!
  let landmarkOk :=
    match addObject monBaseState (.player p0 .permanent)
        { kind := .card ⟨40⟩ ⟨"MON_000"⟩, owner := p0, controller := p0, timestamp := ⟨1⟩ } .top with
    | none => false
    | some (s1, _) =>
      match addObject s1 (.player p1 .permanent)
          { kind := .card ⟨41⟩ ⟨"MON_000"⟩, owner := p1, controller := p1, timestamp := ⟨2⟩ } .top with
      | none => false
      | some (s2, newLm) =>
        let s3 := gspRun s2
        (s3.zone (.player p0 .permanent)).isEmpty &&
        (s3.zone (.player p0 .graveyard)).length == 1 &&
        s3.zone (.player p1 .permanent) == [newLm]
  -- (b) Belittle (MON_266_R) deck search for Minnowism (MON_296_R)
  let belittleOk :=
    match addObject monBaseState (.player p0 .deck)
        { kind := .card ⟨42⟩ ⟨"MON_296_R"⟩, owner := p0, controller := p0, timestamp := ⟨3⟩ } .top with
    | none => false
    | some (s1, _) =>
      let (s2, _, extraF) := execPrim s1 p0 ⟨0⟩ [] (.searchDeck .controller minnowismFilter (some 1) .hand true none)
      (s2.zone (.player p0 .hand)).length == 1 &&
      extraF == [.chanceShuffle (.player p0 .deck)]
  -- (c) Captain's Call (MON_260_R) has 2 play-time modes
  let modalOk :=
    match MON_260_R.front.playEffect with
    | some ed => ed.modes.length == 2
    | none => false
  landmarkOk && belittleOk && modalOk

#guard landmarkAndGenericScenario == true

meta def placeMonCard (s : GameState) (p : PlayerId) (zone : ZoneKind) (cid : CardId)
    (faceDown := false) : Option (GameState × ObjId) :=
  addObject s (.player p zone)
    { kind := .card ⟨s.nextId⟩ cid, owner := p, controller := p,
      timestamp := ⟨s.nextTimestamp⟩, faceDown := faceDown } .top

meta def passToResolve (s : GameState) : Option (GameState × List Event) := do
  let (s1, _) ← (step 64 s ⟨.player p0, .pass⟩).toOption
  (step 64 s1 ⟨.player p1, .pass⟩).toOption

-- Tome of Torment uses the normal legal action, payment, and resolution path.
#guard (do
    let s0 := { monBaseState with pending := [.priority p0 0] }
    let (s1, _) ← placeMonCard s0 p0 .deck ⟨"MON_226_R"⟩
    let (s2, tome) ← placeMonCard s1 p0 .banished ⟨"MON_194_R"⟩
    let (s3, hidden) ← placeMonCard s2 p0 .banished ⟨"MON_194_R"⟩ true
    let (s4, noPermission) ← placeMonCard s3 p0 .banished ⟨"MON_226_R"⟩
    let play := { actor := .player p0, kind := .playCard tome : Action }
    let (sPaid, announced) ← (step 64 s4 play).toOption
    let layer ← (sPaid.zone .stack).head?
    let (sAfter, resolved) ← passToResolve sPaid
    let drawn ← (sAfter.zone (.player p0 .hand)).head?
    let resolvedCard ← (sAfter.zone (.player p0 .graveyard)).head?
    pure ((legalActions s4).contains play &&
      !canPlayCard s4 p0 hidden && !canPlayCard s4 p0 noPermission &&
      announced == [.moved tome layer (.player p0 .banished) .stack] &&
      evalCondition sPaid p0 layer false .playedFromBanished &&
      (sPaid.poolOf p0).actionPoints == 0 &&
      sPaid.playedBloodDebtThisTurn.getD p0.n 0 == 1 &&
      sPaid.playedNonAttackActionThisTurn.contains p0 &&
      resolved.any (· == .drawn p0 drawn) &&
      (sAfter.cardDefOf? resolvedCard).map (·.id) == some ⟨"MON_194_R"⟩ &&
      (sAfter.zone (.player p0 .banished)) == [noPermission, hidden] &&
      ((step 64 s4 ⟨.player p0, .playCard hidden⟩).toOption).isNone) : Option Bool) == some true

-- Deep Rooted Evil needs a qualifying banish, and the play origin survives entry to the chain.
#guard (do
    let s0 := { monBaseState with pending := [.priority p0 0] }
    let (s1, attack) ← placeMonCard s0 p0 .banished ⟨"MON_123_Y"⟩
    let (s2, _) ← placeMonCard s1 p0 .graveyard ⟨"MON_227_Y"⟩
    let (hiddenDeck, _) ← placeMonCard s2 p0 .deck ⟨"MON_227_Y"⟩
    let (hiddenBanish, _, _) := execPrim hiddenDeck p0 ⟨0⟩ [] (.banishTopDeck .controller 1 true)
    let (s3, _, _) := execPrim s2 p0 ⟨0⟩ [] (.banishFromGraveyard .controller CardFilter.any 1)
    let (sPaid, _) ← (step 64 s3 ⟨.player p0, .playCard attack⟩).toOption
    let (sAfter, _) ← passToResolve sPaid
    let link ← sAfter.combat.bind CombatChain.activeLink?
    let source ← link.attack
    pure (!canPlayCard s2 p0 attack && !canPlayCard hiddenBanish p0 attack && canPlayCard s3 p0 attack &&
      evalCondition sAfter p0 source false .playedFromBanished) : Option Bool) == some true

-- Eclipse counts previously played cards. Playing the sixth unlocks Eclipse even in banished.
#guard (do
    let s0 := { monBaseState with
      pending := [.priority p0 0]
      playedBloodDebtThisTurn := (∅ : Std.ExtTreeMap Nat Nat).insert p0.n 5 }
    let (s1, eclipse) ← placeMonCard s0 p0 .banished ⟨"MON_190_B"⟩
    let (s2, fromHand) ← placeMonCard s1 p0 .hand ⟨"MON_190_B"⟩
    let (s2', demigon) ← placeMonCard s2 p0 .banished ⟨"MON_168_R"⟩
    let (s3, tome) ← placeMonCard (s2'.setPool p0 { actionPoints := 2 }) p0 .hand ⟨"MON_194_R"⟩
    let (s4, _) ← (step 64 s3 ⟨.player p0, .playCard tome⟩).toOption
    let (postTome, _) ← passToResolve s4
    let (s5, _) ← (step 64 postTome ⟨.player p0, .playCard eclipse⟩).toOption
    let (s6, _) ← passToResolve s5
    let demon ← (s6.zone (.player p0 .permanent)).head?
    let (s7, _) ← microStep { s6 with pending := [.endTurnCleanup p0] }
    pure (!canPlayCard s3 p0 eclipse && !canPlayCard s3 p0 fromHand &&
      !canPlayCard s3 p0 demigon && canPlayCard postTome p0 demigon && canPlayCard s4 p0 fromHand &&
      (s6.cardDefOf? demon).map (·.id) == some ⟨"MON_220"⟩ &&
      (s6.obj? demon).bind (·.life) == some 6 &&
      s7.playedBloodDebtThisTurn.isEmpty && s7.playedNonAttackActionThisTurn.isEmpty) :
    Option Bool) == some true

-- Doomsday counts face-up Blood Debt in banished, regardless of play history.
#guard (do
    let s0 := { monBaseState with pending := [.priority p0 0] }
    let (s1, doom) ← placeMonCard s0 p0 .hand ⟨"MON_189_B"⟩
    let cards := ["MON_126_R", "MON_127_Y", "MON_128_B", "MON_129_R", "MON_130_Y"]
    let s2 ← cards.foldlM (fun s cid => (placeMonCard s p0 .banished ⟨cid⟩).map Prod.fst) s1
    let (s3, _) ← placeMonCard s2 p0 .banished ⟨"MON_194_R"⟩ true
    let (s4, _) ← placeMonCard s3 p0 .banished ⟨"MON_203_R"⟩
    let (s5, _) ← (step 64 s4 ⟨.player p0, .playCard doom⟩).toOption
    let (s6, _) ← passToResolve s5
    let demon ← (s6.zone (.player p0 .permanent)).head?
    pure (!canPlayCard s3 p0 doom && s4.playedBloodDebtThisTurn.isEmpty &&
      (s6.cardDefOf? demon).map (·.id) == some ⟨"MON_219"⟩ &&
      (s6.obj? demon).bind (·.life) == some 6) : Option Bool) == some true

-- Only the turn-player's Soul Shackle triggers, stacks, and banishes on resolution.
#guard (do
    let s0 := { monBaseState with pending := [.actionPhaseStart p0] }
    let (s1, _) ← placeMonCard s0 p0 .deck ⟨"MON_194_R"⟩
    let (s2, _) ← placeMonCard s1 p1 .deck ⟨"MON_194_R"⟩
    let (s3, source) ← addObject s2 (.player p0 .permanent)
      { kind := .token ⟨"MON_186"⟩, owner := p0, controller := p0, timestamp := ⟨0⟩ } .top
    let (s4, _) ← addObject s3 (.player p1 .permanent)
      { kind := .token ⟨"MON_186"⟩, owner := p1, controller := p1, timestamp := ⟨0⟩ } .top
    let (s5, _) ← (advance 64 s4 []).toOption
    let trigger ← s5.pendingTriggers.head?
    let (s6, _) ← (step 64 s5 ⟨.player p0, .pickTriggerStart p0⟩).toOption
    let (s7, _) ← (step 64 s6 ⟨.player p0, .pickTrigger trigger.id⟩).toOption
    let (s8, events) ← passToResolve s7
    let banished ← (s8.zone (.player p0 .banished)).head?
    pure (s5.pendingTriggers.length == 1 && trigger.source == source &&
      (s8.zone (.player p0 .deck)).isEmpty && (s8.zone (.player p1 .deck)).length == 1 &&
      s8.pendingTriggers.isEmpty && (s8.zone .stack).isEmpty &&
      events.contains (.banished p0 banished false)) : Option Bool) == some true

-- Each color of Ghostly Visit and Void Wraith can attack from banished and has Blood Debt.
meta def checkBanishedAttack (cid : CardId) : Option Bool := do
  let s0 := { monBaseState with pending := [.priority p0 0] }
  let (s, id) ← placeMonCard s0 p0 .banished cid
  let (unplayed, debt) ← microStep { s with pending := [.endPhaseStart p0] }
  let play := { actor := .player p0, kind := .playCard id : Action }
  let (sPaid, _) ← (step 64 s play).toOption
  let (resolved, _) ← passToResolve sPaid
  let attack ← resolved.combat.bind CombatChain.activeLink? >>= (·.attack)
  pure ((legalActions s).contains play && unplayed.lifeOf p0 == 39 && debt == [.lifeLost p0 1] &&
    (sPaid.zone (.player p0 .banished)).isEmpty &&
    (resolved.cardDefOf? attack).map (·.id) == some cid)

#guard ["MON_203_R", "MON_204_Y", "MON_205_B", "MON_209_R", "MON_210_Y", "MON_211_B"].all
  (fun cid => checkBanishedAttack ⟨cid⟩ == some true)

-- All three Prismatic Shield printings resolve through the stack with their printed token counts.
meta def checkPrismaticShield (cid : CardId) (count : Nat) : Option Bool := do
  let s0 := { monBaseState with pending := [.priority p0 0] }
  let (s, shield) ← placeMonCard s0 p0 .hand cid
  let (sPaid, _) ← (step 64 s ⟨.player p0, .playCard shield⟩).toOption
  let (resolved, _) ← passToResolve sPaid
  let tokens := resolved.zone (.player p0 .permanent)
  pure (tokens.length == count && tokens.all (fun id =>
    (resolved.obj? id).map (·.kind) == some (.token ⟨"MON_104"⟩)))

#guard checkPrismaticShield ⟨"MON_092_R"⟩ 3 == some true
#guard checkPrismaticShield ⟨"MON_093_Y"⟩ 2 == some true
#guard checkPrismaticShield ⟨"MON_094_B"⟩ 1 == some true

-- A newly played Landmark enters the arena and replaces the older Landmark.
#guard (do
    let s0 := { monBaseState with pending := [.priority p0 0] }
    let (s1, _) ← placeMonCard s0 p1 .permanent ⟨"MON_000"⟩
    let (s2, library) ← placeMonCard s1 p0 .hand ⟨"MON_000"⟩
    let (paid, _) ← (step 64 s2 ⟨.player p0, .playCard library⟩).toOption
    let (resolved, _) ← passToResolve paid
    let newest ← (resolved.zone (.player p0 .permanent)).head?
    pure ((resolved.cardDefOf? newest).map (·.id) == some ⟨"MON_000"⟩ &&
      (resolved.zone (.player p1 .permanent)).isEmpty &&
      (resolved.zone (.player p1 .graveyard)).length == 1) : Option Bool) == some true

-- An unpayable banished card restores its object, origin, and turn history on rollback.
#guard (do
    let s0 := { monBaseState.setPool p0 { actionPoints := 1 } with pending := [.priority p0 0] }
    let (s, id) ← placeMonCard s0 p0 .banished ⟨"MON_209_R"⟩
    let (after, _) ← (step 64 s ⟨.player p0, .playCard id⟩).toOption
    pure (decide (after = s)) : Option Bool) == some true

end FabTest.Monarch
