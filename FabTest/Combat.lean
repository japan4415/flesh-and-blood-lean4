module

import Fab
import FabCards
meta import Fab
meta import FabCards

/-!
# Tests: M5 Combat Chain 7 steps, Attack-Proxy, LKI, Equipment Wear, Dominate, Combo, and GSP
-/

open Fab
open FabCards

/-- Helper: add a physical card `cid` to player `p`'s zone `k`. -/
meta def cPlace (s : GameState) (p : PlayerId) (k : ZoneKind) (cid : CardId)
    (faceDown : Bool := false) : Option (GameState × ObjId) :=
  addObject s (.player p k)
    { kind := .card ⟨s.nextId⟩ cid
      owner := p
      controller := p
      faceDown := faceDown
      timestamp := ⟨0⟩ } .top

/-- Base 1v1 Action Phase state with `wtrDB`, P0 active, 1 AP, 40 life each. -/
meta def m5Base : GameState :=
  let s0 : GameState :=
    { config := GameConfig.ccDuel
      cards := wtrDB
      turn := 1
      active := some ⟨0⟩
      turnOrder := [⟨0⟩, ⟨1⟩]
      phase := .actionPhase
      pending := [.priority ⟨0⟩ 0, .endPhaseStart ⟨0⟩] }
  let s1 := (s0.setLife ⟨0⟩ 40).setLife ⟨1⟩ 40
  s1.setPool ⟨0⟩ { actionPoints := 1 }

/-- Helper: execute a sequence of actions with fuel 64. -/
meta def cSteps (s : GameState) : List Action → Option GameState
  | [] => some s
  | a :: rest =>
    match step 64 s a with
    | .ok (s', _) => cSteps s' rest
    | .error _ => none

/-- Helper: both players pass priority once (P0 then P1). -/
meta def passBoth : List Action :=
  [⟨.player ⟨0⟩, .pass⟩, ⟨.player ⟨1⟩, .pass⟩]

-- 1. Full 7-step Attack Action combat (CR 7.1-7.7):
--    P0 plays Wounding Blow Red (4{p}), P1 defends with 1 hand card (Wounding Blow Red, 3{d}) ->
--    Damage Step deals 1 damage (40 -> 39, hit = true) -> Close Step sends both cards to
--    respective graveyards and closes combat chain!
#guard match (do
    let (s1, wbAtk) ← cPlace m5Base ⟨0⟩ .hand ⟨"WTR_203_R"⟩
    let (s2, wbDef) ← cPlace s1 ⟨1⟩ .hand ⟨"WTR_203_R"⟩
    -- Layer Step -> Attack Step -> Defend Step (`defendPick P1`)
    let sDef ← cSteps s2 ([⟨.player ⟨0⟩, .playCard wbAtk⟩] ++ passBoth ++ passBoth)
    let onDefend := sDef.pending.head? == some (.defendPick ⟨1⟩)
    -- P1 defends with wbDef, done -> Reaction Step -> Damage Step -> Resolution Step
    let sRes ← cSteps sDef
      ([⟨.player ⟨1⟩, .defendCard wbDef⟩, ⟨.player ⟨1⟩, .defendDone⟩] ++
       passBoth ++ passBoth ++ passBoth)
    let hitOk := sRes.lifeOf ⟨1⟩ == 39 &&
      (sRes.combat.bind CombatChain.activeLink?).map (fun l => (l.hit, l.damageDealt)) == some (true, 1)
    -- Pass Resolution Step -> Close Step -> back to Action Phase priority with combat closed
    let sClosed ← cSteps sRes passBoth
    pure (onDefend && hitOk &&
      sClosed.combat == none &&
      (sClosed.zone .combatChain).isEmpty &&
      (sClosed.zone (.player ⟨0⟩ .graveyard)).length == 1 &&
      (sClosed.zone (.player ⟨1⟩ .graveyard)).length == 1 &&
      sClosed.physIds.length == 2)) with
  | some b => b
  | none => false

-- 2. Battleworn & Blade Break Equipment Wear + Identical `ObjId` Preservation (I11: CR 3.0.9, 7.7, 8.3.2, 8.3.3):
--    P0 attacks with Wounding Blow Red (4{p}). P1 defends with Tectonic Plating (Chest, 2{d}, Battleworn)
--    and Ironrot Helm (Head, 1{d}, Blade Break) -> total defense 3 -> 1 damage (40 -> 39).
--    Close Step: Tectonic Plating returns to Chest with IDENTICAL ObjId & 1 `-1{d}` counter (effDef = 1);
--    Ironrot Helm is destroyed into P1's graveyard!
#guard match (do
    let (s1, wbAtk) ← cPlace m5Base ⟨0⟩ .hand ⟨"WTR_203_R"⟩
    let (s2, platingId) ← cPlace s1 ⟨1⟩ .chest ⟨"WTR_041"⟩
    let (s3, helmId) ← cPlace s2 ⟨1⟩ .head ⟨"WTR_155"⟩
    let sDef ← cSteps s3 ([⟨.player ⟨0⟩, .playCard wbAtk⟩] ++ passBoth ++ passBoth)
    let sClosed ← cSteps sDef
      ([⟨.player ⟨1⟩, .defendCard platingId⟩, ⟨.player ⟨1⟩, .defendCard helmId⟩,
        ⟨.player ⟨1⟩, .defendDone⟩] ++
       passBoth ++ passBoth ++ passBoth ++ passBoth)
    pure (sClosed.lifeOf ⟨1⟩ == 39 &&
      sClosed.zone (.player ⟨1⟩ .chest) == [platingId] &&
      (sClosed.obj? platingId).map (·.minusDefenseCounters) == some 1 &&
      objEffectiveDefense sClosed platingId == some 1 &&
      (sClosed.zone (.player ⟨1⟩ .head)).isEmpty &&
      (sClosed.zone (.player ⟨1⟩ .graveyard)).length == 1 &&
      sClosed.physIds.length == 3)) with
  | some b => b
  | none => false

-- 3. Reaction Step: Attack Reaction (Ancestral Empowerment +1{p}, draw 1) + Defense Reaction
--    (Sink Below Red, 4{d}, decline `may`) join combat before Damage Step (CR 7.4, 7.5)!
--    Wounding Blow Red (4{p}) + Ancestral (+1{p} = 5{p}) vs 3{d} hand card + Sink Below (4{d} = 7{d}) -> 0 dmg!
#guard match (do
    let (s1, _) ← cPlace m5Base ⟨0⟩ .deck ⟨"WTR_188_R"⟩
    let (s2, wbAtk) ← cPlace s1 ⟨0⟩ .hand ⟨"WTR_203_R"⟩
    let (s3, ancId) ← cPlace s2 ⟨0⟩ .hand ⟨"WTR_082_R"⟩
    let (s4, defHand) ← cPlace s3 ⟨1⟩ .hand ⟨"WTR_098_R"⟩  -- Head Jab Red (2{d})
    let (s5, sinkId) ← cPlace s4 ⟨1⟩ .hand ⟨"WTR_215_R"⟩   -- Sink Below Red (4{d})
    -- Enter Defend Step, defend with defHand (2{d}), advance to Reaction Step
    let sReact ← cSteps s5
      ([⟨.player ⟨0⟩, .playCard wbAtk⟩] ++ passBoth ++ passBoth ++
       [⟨.player ⟨1⟩, .defendCard defHand⟩, ⟨.player ⟨1⟩, .defendDone⟩] ++ passBoth)
    let onReact := sReact.combat.map (·.step) == some .reaction
    -- P0 plays Ancestral Empowerment (+1{p} & draw 1), both pass -> resolves
    let sAfterAnc ← cSteps sReact ([⟨.player ⟨0⟩, .playCard ancId⟩] ++ passBoth)
    -- P0 passes -> P1 plays Sink Below Red (4{d}), P1 passes, P0 passes -> prompts `chooseMay` -> decline
    let sAfterSink ← cSteps sAfterAnc
      [⟨.player ⟨0⟩, .pass⟩, ⟨.player ⟨1⟩, .playCard sinkId⟩,
       ⟨.player ⟨1⟩, .pass⟩, ⟨.player ⟨0⟩, .pass⟩, ⟨.player ⟨1⟩, .pickMay false⟩]
    -- Both pass Reaction Step -> Damage Step (5{p} vs 6{d} = 0 dmg, hit = false)
    let sDmg ← cSteps sAfterSink passBoth
    pure (onReact &&
      (sAfterAnc.zone (.player ⟨0⟩ .hand)).length == 1 &&
      sDmg.lifeOf ⟨1⟩ == 40 &&
      (sDmg.combat.bind CombatChain.activeLink?).map (fun l => (l.hit, l.damageDealt)) == some (false, 0))) with
  | some b => b
  | none => false

-- 4. Dominate Hook (CR 8.3.4):
--    Demolition Crew Red (Dominate, 6{p}, cost 2{r}): P1 defends with 1st hand card ->
--    attempting a 2nd hand card is ILLEGAL, while defending additionally with Equipment IS legal!
#guard match (do
    let s0 := m5Base.setPool ⟨0⟩ { actionPoints := 1, resources := 2 }
    let (s1, demoId) ← cPlace s0 ⟨0⟩ .hand ⟨"WTR_179_R"⟩
    let (s2, h1) ← cPlace s1 ⟨1⟩ .hand ⟨"WTR_203_R"⟩
    let (s3, h2) ← cPlace s2 ⟨1⟩ .hand ⟨"WTR_188_R"⟩
    let (s4, eqId) ← cPlace s3 ⟨1⟩ .chest ⟨"WTR_041"⟩
    let sDef1 ← cSteps s4 ([⟨.player ⟨0⟩, .playCard demoId⟩] ++ passBoth ++ passBoth ++
      [⟨.player ⟨1⟩, .defendCard h1⟩])
    let secondHandRejected :=
      match step 64 sDef1 ⟨.player ⟨1⟩, .defendCard h2⟩ with
      | .error .illegal => true
      | _ => false
    let equipAccepted :=
      match step 64 sDef1 ⟨.player ⟨1⟩, .defendCard eqId⟩ with
      | .ok _ => true
      | .error _ => false
    pure (secondHandRejected && equipAccepted)) with
  | some b => b
  | none => false

-- 5. Multi-Link Ninja Combo Chain with Go Again (CR 7.6, 8.3.6):
--    Link 1: Surging Strike Red (5{p}, cost 2{r}, Go Again) -> hits P1 (40 -> 35), Resolution +1 AP!
--    Link 2: Whelming Gustwave Red (3{p}, cost 0, Combo off "Surging Strike" -> +1{p}=4{p} & Go Again!)
--            chains directly on the SAME open Combat Chain -> hits P1 (35 -> 31), +1 AP again!
#guard match (do
    let s0 := m5Base.setPool ⟨0⟩ { actionPoints := 1, resources := 2 }
    let (s1, surgeId) ← cPlace s0 ⟨0⟩ .hand ⟨"WTR_107_R"⟩
    let (s2, gustId) ← cPlace s1 ⟨0⟩ .hand ⟨"WTR_110_R"⟩
    -- Link 1: Surging Strike through Resolution Step
    let sRes1 ← cSteps s2
      ([⟨.player ⟨0⟩, .playCard surgeId⟩] ++ passBoth ++ passBoth ++
       [⟨.player ⟨1⟩, .defendDone⟩] ++ passBoth ++ passBoth ++ passBoth)
    let link1Ok := sRes1.lifeOf ⟨1⟩ == 35 &&
      (sRes1.poolOf ⟨0⟩).actionPoints == 1 &&
      sRes1.combat.map (fun cc => (cc.step, cc.links.length)) == some (.resolution, 1)
    -- Link 2: Play Whelming Gustwave during Resolution Step (Combo triggers +1{p} & Go Again!)
    let sRes2 ← cSteps sRes1
      ([⟨.player ⟨0⟩, .playCard gustId⟩] ++ passBoth ++ passBoth ++
       [⟨.player ⟨1⟩, .defendDone⟩] ++ passBoth ++ passBoth ++ passBoth)
    let link2Ok := sRes2.lifeOf ⟨1⟩ == 31 &&
      (sRes2.poolOf ⟨0⟩).actionPoints == 1 &&
      sRes2.combat.map (fun cc => (cc.step, cc.links.length)) == some (.resolution, 2)
    -- Close chain -> both attack cards go to graveyard
    let sClosed ← cSteps sRes2 passBoth
    pure (link1Ok && link2Ok &&
      sClosed.combat == none &&
      (sClosed.zone (.player ⟨0⟩ .graveyard)).length == 2)) with
  | some b => b
  | none => false

-- 6. Weapon Attack-Proxy + Weapon Identical `ObjId` Return + LKI Go Again (CR 1.4.3, 3.5.4b):
--    P0 attacks with Harmonized Kodachi (1{p}, cost 1{r}) via `.attackWeapon` -> creates proxy ->
--    deals 1 damage (40 -> 39) -> Close Step removes proxy and returns Kodachi to `.weapon`
--    with the EXACT SAME `ObjId`, preserving `physIds`!
#guard match (do
    let s0 := m5Base.setPool ⟨0⟩ { actionPoints := 1, resources := 1 }
    let (s1, kodachiId) ← cPlace s0 ⟨0⟩ .weapon ⟨"WTR_078"⟩
    let sClosed ← cSteps s1
      ([⟨.player ⟨0⟩, .attackWeapon kodachiId⟩] ++ passBoth ++ passBoth ++
       [⟨.player ⟨1⟩, .defendDone⟩] ++ passBoth ++ passBoth ++ passBoth ++ passBoth)
    -- Also verify LKI Go Again check works even after `link.attack = none` (Endless Arrow pattern)
    let lkiLink : ChainLink :=
      { linkId := ⟨1⟩
        attacker := ⟨0⟩
        defender := ⟨1⟩
        attack := none
        attackLki := { cardId := none, name := "Endless Arrow", owner := ⟨0⟩, controller := ⟨0⟩,
                       keywords := [.goAgain] } }
    pure (sClosed.lifeOf ⟨1⟩ == 39 &&
      sClosed.zone (.player ⟨0⟩ .weapon) == [kodachiId] &&
      (sClosed.zone .combatChain).isEmpty &&
      sClosed.physIds.length == 1 &&
      linkHasKeyword sClosed lkiLink .goAgain)) with
  | some b => b
  | none => false

-- 7. Game State Process (I12a + I17: CR 1.10.2):
--    Stray token in graveyard + dead Ally (life = 0) in permanent zone + hero at 0 life ->
--    `gspRun` cleans all three and produces a `Settled` state with `gspStep == none`!
#guard match (do
    let tok : Object := { kind := .token ⟨"WTR_075"⟩, owner := ⟨0⟩, controller := ⟨0⟩, timestamp := ⟨0⟩ }
    let (s1, _) ← addObject m5Base (.player ⟨0⟩ .graveyard) tok .top
    let ally : Object :=
      { kind := .token ⟨"WTR_225"⟩, owner := ⟨0⟩, controller := ⟨0⟩, life := some 0, timestamp := ⟨1⟩ }
    let (s2, _) ← addObject s1 (.player ⟨0⟩ .permanent) ally .top
    let s3 := s2.setLife ⟨1⟩ 0
    let sSettled := gspRun s3
    pure (decide (Settled sSettled) &&
      (gspStep sSettled).isNone &&
      (sSettled.zone (.player ⟨0⟩ .graveyard)).isEmpty &&
      (sSettled.zone (.player ⟨0⟩ .permanent)).isEmpty &&
      sSettled.result == some (.won [⟨0⟩]))) with
  | some b => b
  | none => false

/-- Play Leg Tap through resolution, checking payment, damage, and Go Again even on a miss. -/
meta def checkLegTap (cid : CardId) (power : Nat) : Option Bool := do
  let attacker : PlayerId := ⟨0⟩
  let defender : PlayerId := ⟨1⟩
  let s0 := m5Base.setPool attacker { actionPoints := 1, resources := 1 }
  let card ← s0.cards.find? cid
  let (s1, attack) ← cPlace s0 attacker .hand cid
  let (s2, defender1) ← cPlace s1 defender .hand ⟨"WTR_203_R"⟩
  let (s3, defender2) ← cPlace s2 defender .hand ⟨"WTR_204_Y"⟩
  let paid ← cSteps s3 [⟨.player attacker, .playCard attack⟩]
  let defense ← cSteps paid (passBoth ++ passBoth)
  let resolve : List Action := [⟨.player defender, .defendDone⟩] ++ passBoth ++ passBoth ++ passBoth
  let hit ← cSteps defense resolve
  let miss ← cSteps defense
    ([⟨.player defender, .defendCard defender1⟩, ⟨.player defender, .defendCard defender2⟩] ++ resolve)
  let closed ← cSteps hit passBoth
  let graveId ← (closed.zone (.player attacker .graveyard)).head?
  pure (card.status == .full &&
    (paid.poolOf attacker).actionPoints == 0 && (paid.poolOf attacker).resources == 0 &&
    hit.combat.map (·.step) == some .resolution && hit.lifeOf defender == 40 - Int.ofNat power &&
    miss.combat.map (·.step) == some .resolution && miss.lifeOf defender == 40 &&
    (hit.poolOf attacker).actionPoints == 1 && (miss.poolOf attacker).actionPoints == 1 &&
    closed.combat.isNone && (closed.poolOf attacker).actionPoints == 1 &&
    (closed.cardDefOf? graveId).map (·.id) == some cid)

#guard checkLegTap ⟨"WTR_101_R"⟩ 4 == some true
#guard checkLegTap ⟨"WTR_102_Y"⟩ 3 == some true
#guard checkLegTap ⟨"WTR_103_B"⟩ 2 == some true

/-- Run Snatch's hit, full block, and full prevention cases through the combat engine. -/
meta def checkSnatch (cid : CardId) (power : Nat) : Option Bool := do
  let attacker : PlayerId := ⟨0⟩
  let defender : PlayerId := ⟨1⟩
  let card ← m5Base.cards.find? cid
  let (s1, atk) ← cPlace m5Base attacker .hand cid
  let (s2, topId) ← cPlace s1 attacker .deck ⟨"WTR_188_R"⟩
  let (s3, block1) ← cPlace s2 defender .hand ⟨"WTR_203_R"⟩
  let (s4, block2) ← cPlace s3 defender .hand ⟨"WTR_204_Y"⟩
  let defense ← cSteps s4 ([⟨.player attacker, .playCard atk⟩] ++ passBoth ++ passBoth)
  let finishDefense : List Action := [⟨.player defender, .defendDone⟩] ++ passBoth ++ passBoth
  let hit ← cSteps defense finishDefense
  let blocked ← cSteps defense ([⟨.player defender, .defendCard block1⟩,
    ⟨.player defender, .defendCard block2⟩] ++ finishDefense)
  let (shielded, _, _) := execPrim defense defender ⟨0⟩ []
    (.preventNextDamage .controller (.const (Int.ofNat power)) .thisTurn)
  let prevented ← cSteps shielded finishDefense
  let trigger ← hit.pendingTriggers.head?
  let stacked ← cSteps hit [⟨.player attacker, .pickTriggerStart attacker⟩,
    ⟨.player attacker, .pickTrigger trigger.id⟩]
  let passed ← cSteps stacked [⟨.player attacker, .pass⟩]
  let (drawn, events) ← (step 64 passed ⟨.player defender, .pass⟩).toOption
  let drawnId ← (drawn.zone (.player attacker .hand)).head?
  pure (card.status == .full && hit.pendingTriggers.length == 1 &&
    hit.lifeOf defender == 40 - Int.ofNat power &&
    blocked.lifeOf defender == 40 && blocked.pendingTriggers.isEmpty &&
    prevented.lifeOf defender == 40 && prevented.pendingTriggers.isEmpty &&
    [blocked, prevented, hit, stacked].all (fun s => s.zone (.player attacker .deck) == [topId]) &&
    (stacked.zone .stack).length == 1 && (drawn.zone .stack).isEmpty &&
    drawn.pendingTriggers.isEmpty &&
    (drawn.zone (.player attacker .hand)).length == 1 &&
    (drawn.cardDefOf? drawnId).map (·.id) == some ⟨"WTR_188_R"⟩ &&
    events.countP (· == .drawn attacker drawnId) == 1)

#guard checkSnatch ⟨"WTR_167_R"⟩ 4 == some true
#guard checkSnatch ⟨"WTR_168_Y"⟩ 3 == some true
#guard checkSnatch ⟨"WTR_169_B"⟩ 2 == some true

/-- Play a sequence of prior attacks on one chain, then check the tested attack's combo and damage. -/
meta def checkComboAttack (preceding : List CardId) (cid : CardId) (power : Nat) (bonus : Int)
    (keywords : List KeywordInst := []) : Option Bool := do
  let attacker : PlayerId := ⟨0⟩
  let defender : PlayerId := ⟨1⟩
  let s0 := m5Base.setPool attacker { actionPoints := preceding.length + 1, resources := 8 }
  let card ← s0.cards.find? cid
  let (s1, id) ← cPlace s0 attacker .hand cid
  let finishAttack : List Action := [⟨.player defender, .defendDone⟩] ++ passBoth ++ passBoth ++ passBoth
  let enterAttack := fun (source : ObjId) => [⟨.player attacker, .playCard source⟩] ++ passBoth ++ passBoth
  let ready ← preceding.foldlM (fun s prior => do
    let (withPrior, priorId) ← cPlace s attacker .hand prior
    cSteps withPrior (enterAttack priorId ++ finishAttack)) s1
  let defending ← cSteps ready (enterAttack id)
  let active ← defending.combat.bind CombatChain.activeLink?
  let attack ← active.attack
  let (oneBlock, first) ← cPlace defending defender .hand ⟨"WTR_203_R"⟩
  let (twoBlocks, second) ← cPlace oneBlock defender .hand ⟨"WTR_204_Y"⟩
  let afterFirst ← cSteps twoBlocks [⟨.player defender, .defendCard first⟩]
  let secondBlock : Action := ⟨.player defender, .defendCard second⟩
  let resolved ← cSteps defending finishAttack
  let result ← resolved.combat.bind CombatChain.activeLink?
  pure (card.status == .full && (defending.cardDefOf? attack).map (·.id) == some cid &&
    defending.combat.map (·.links.length) == some (preceding.length + 1) &&
    active.powerBonus == bonus && result.damageDealt == power &&
    defending.lifeOf defender - resolved.lifeOf defender == Int.ofNat power &&
    linkHasKeyword defending active .goAgain == keywords.contains .goAgain &&
    linkHasKeyword defending active .dominate == keywords.contains .dominate &&
    (legalActions afterFirst).contains secondBlock == !(keywords.contains .dominate) &&
    (cSteps afterFirst [secondBlock]).isSome == !(keywords.contains .dominate) &&
    (resolved.poolOf attacker).actionPoints == (defending.poolOf attacker).actionPoints +
      (if keywords.contains .goAgain then 1 else 0))

/-- Blackout Kick checks the immediately preceding attack, even when an earlier link matches. -/
meta def checkBlackoutKick (cid : CardId) (basePower : Nat) : Bool :=
  checkComboAttack [⟨"WTR_104_R"⟩] cid (basePower + 3) 3 == some true &&
  checkComboAttack [] cid basePower 0 == some true &&
  checkComboAttack [⟨"WTR_104_R"⟩, ⟨"WTR_203_R"⟩] cid basePower 0 == some true

#guard checkBlackoutKick ⟨"WTR_089_R"⟩ 4
#guard checkBlackoutKick ⟨"WTR_090_Y"⟩ 3
#guard checkBlackoutKick ⟨"WTR_091_B"⟩ 2

/-- Rising Knee Thrust gets power and Go Again only immediately after Leg Tap. -/
meta def checkRisingKneeThrust (cid : CardId) (basePower : Nat) : Bool :=
  checkComboAttack [⟨"WTR_101_R"⟩] cid (basePower + 2) 2 [.goAgain] == some true &&
  checkComboAttack [] cid basePower 0 == some true &&
  checkComboAttack [⟨"WTR_101_R"⟩, ⟨"WTR_203_R"⟩] cid basePower 0 == some true

#guard checkRisingKneeThrust ⟨"WTR_104_R"⟩ 3
#guard checkRisingKneeThrust ⟨"WTR_105_Y"⟩ 2
#guard checkRisingKneeThrust ⟨"WTR_106_B"⟩ 1

/-- Open the Center gets power, Go Again, and Dominate only immediately after Head Jab. -/
meta def checkOpenTheCenter (cid : CardId) (basePower : Nat) : Bool :=
  checkComboAttack [⟨"WTR_098_R"⟩] cid (basePower + 1) 1 [.goAgain, .dominate] == some true &&
  checkComboAttack [] cid basePower 0 == some true &&
  checkComboAttack [⟨"WTR_098_R"⟩, ⟨"WTR_203_R"⟩] cid basePower 0 == some true

#guard checkOpenTheCenter ⟨"WTR_095_R"⟩ 5
#guard checkOpenTheCenter ⟨"WTR_096_Y"⟩ 4
