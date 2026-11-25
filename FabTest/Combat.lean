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

-- 1. Full 7-step Attack Action combat (CR 7.1-7.7).
/-- Check a plain attack card as a pitch, an attack, and a block on the combat chain. -/
meta def checkPlainAttack (cid : CardId) (pitch cost power defense : Nat) : Option Bool := do
  let attacker : PlayerId := ⟨0⟩
  let defender : PlayerId := ⟨1⟩
  let funded := m5Base.setPool attacker { actionPoints := 1, resources := cost + 1 }
  let card ← funded.cards.find? cid
  let (withAttack, attackId) ← cPlace funded attacker .hand cid
  let (ready, blockId) ← cPlace withAttack defender .hand cid
  let (pitched, pitchId, _) ← pitchOne withAttack attacker attackId
  let defending ← cSteps ready ([⟨.player attacker, .playCard attackId⟩] ++ passBoth ++ passBoth)
  let finishDefense := [⟨.player defender, .defendDone⟩] ++ passBoth ++ passBoth ++ passBoth
  let unblocked ← cSteps defending finishDefense
  let blocked ← cSteps defending ([⟨.player defender, .defendCard blockId⟩] ++ finishDefense)
  let closed ← cSteps blocked passBoth
  let damage := power - defense
  let attackGrave := closed.zone (.player attacker .graveyard)
  let defenseGrave := closed.zone (.player defender .graveyard)
  pure (card.status == .full && pitched.zone (.player attacker .pitch) == [pitchId] &&
    (pitched.poolOf attacker).resources == cost + 1 + pitch &&
    defending.pending.head? == some (.defendPick defender) &&
    (defending.poolOf attacker).resources == 1 &&
    unblocked.lifeOf defender == 40 - Int.ofNat power &&
    blocked.lifeOf defender == 40 - Int.ofNat damage &&
    (blocked.combat.bind CombatChain.activeLink?).map (fun l => (l.hit, l.damageDealt)) ==
      some (damage != 0, damage) &&
    (blocked.combat.bind CombatChain.activeLink?).map (linkTotalDefense blocked) == some defense &&
    (blocked.poolOf attacker).actionPoints == 0 &&
    closed.combat.isNone && (closed.zone .combatChain).isEmpty &&
    attackGrave.map (fun id => (closed.cardDefOf? id).map (·.id)) == [some cid] &&
    defenseGrave.map (fun id => (closed.cardDefOf? id).map (·.id)) == [some cid] &&
    closed.physIds.length == 2)

#guard checkPlainAttack ⟨"WTR_203_R"⟩ 1 0 4 3 == some true
#guard checkPlainAttack ⟨"WTR_204_Y"⟩ 2 0 3 3 == some true
#guard checkPlainAttack ⟨"WTR_205_B"⟩ 3 0 2 3 == some true
#guard checkPlainAttack ⟨"WTR_188_R"⟩ 1 3 7 3 == some true
#guard checkPlainAttack ⟨"WTR_189_Y"⟩ 2 3 6 3 == some true
#guard checkPlainAttack ⟨"WTR_190_B"⟩ 3 3 5 3 == some true

/-- Check Ironrot equipment loadout, defense, and Blade Break on chain close. -/
meta def checkIronrot (cid : CardId) (slot : ZoneKind) : Option Bool := do
  let attacker : PlayerId := ⟨0⟩
  let defender : PlayerId := ⟨1⟩
  let card ← m5Base.cards.find? cid
  let (inventory, unequipped) ← cPlace m5Base defender .inventory cid
  let equippedZone ← loadoutEquipDest? inventory defender unequipped
  let (equipped, equipment) ← moveObj inventory unequipped equippedZone .top false
  let (ready, attack) ← cPlace equipped attacker .hand ⟨"WTR_203_R"⟩
  let defense ← cSteps ready ([⟨.player attacker, .playCard attack⟩] ++ passBoth ++ passBoth)
  let finishDefense := [⟨.player defender, .defendDone⟩] ++ passBoth ++ passBoth ++ passBoth
  let blocked ← cSteps defense ([⟨.player defender, .defendCard equipment⟩] ++ finishDefense)
  let idle ← cSteps defense (finishDefense ++ passBoth)
  let passed ← cSteps blocked [⟨.player attacker, .pass⟩]
  let (closed, events) ← (step 64 passed ⟨.player defender, .pass⟩).toOption
  let graveyard := Zone.player defender .graveyard
  let broken ← (closed.zone graveyard).head?
  pure (card.status == .full && equippedZone == .player defender slot &&
    objEffectiveDefense equipped equipment == some 1 &&
    blocked.lifeOf defender == 37 && blocked.locate equipment == some .combatChain &&
    blocked.zone graveyard == [] && blocked.combat.map (·.step) == some .resolution &&
    closed.combat.isNone && closed.zone equippedZone == [] &&
    closed.zone graveyard == [broken] &&
    (closed.cardDefOf? broken).map (·.id) == some cid &&
    events.countP (· == .moved equipment broken .combatChain graveyard) == 1 &&
    idle.lifeOf defender == 36 && idle.combat.isNone &&
    idle.zone equippedZone == [equipment] && idle.zone graveyard == [])

#guard checkIronrot ⟨"WTR_155"⟩ .head == some true
#guard checkIronrot ⟨"WTR_156"⟩ .chest == some true
#guard checkIronrot ⟨"WTR_157"⟩ .arms == some true
#guard checkIronrot ⟨"WTR_158"⟩ .legs == some true

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
--    (Sink Below Red, 4{d}) join combat before Damage Step (CR 7.4, 7.5)!
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
    -- Sink Below resolves without a choice because P1 has no cards left in hand.
    let sAfterSink ← cSteps sAfterAnc
      [⟨.player ⟨0⟩, .pass⟩, ⟨.player ⟨1⟩, .playCard sinkId⟩,
       ⟨.player ⟨1⟩, .pass⟩, ⟨.player ⟨0⟩, .pass⟩]
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

/-- Check payment, damage, and an attack's printed Go Again even on a miss. -/
meta def checkGoAgainAttack (cid : CardId) (cost power : Nat) : Option Bool := do
  let attacker : PlayerId := ⟨0⟩
  let defender : PlayerId := ⟨1⟩
  let s0 := m5Base.setPool attacker { actionPoints := 1, resources := cost }
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

#guard checkGoAgainAttack ⟨"WTR_101_R"⟩ 1 4 == some true
#guard checkGoAgainAttack ⟨"WTR_102_Y"⟩ 1 3 == some true
#guard checkGoAgainAttack ⟨"WTR_103_B"⟩ 1 2 == some true
#guard checkGoAgainAttack ⟨"WTR_098_R"⟩ 0 3 == some true
#guard checkGoAgainAttack ⟨"WTR_099_Y"⟩ 0 2 == some true
#guard checkGoAgainAttack ⟨"WTR_100_B"⟩ 0 1 == some true
#guard checkGoAgainAttack ⟨"WTR_107_R"⟩ 2 5 == some true
#guard checkGoAgainAttack ⟨"WTR_108_Y"⟩ 2 4 == some true
#guard checkGoAgainAttack ⟨"WTR_109_B"⟩ 2 3 == some true

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

/-- Resolve Sigil of Solace from hand on the opponent's turn without spending an action point. -/
meta def checkSigilOfSolace (cid : CardId) (amount : Nat) : Option Bool := do
  let active : PlayerId := ⟨0⟩
  let caster : PlayerId := ⟨1⟩
  let card ← m5Base.cards.find? cid
  let (ready, sigil) ← cPlace m5Base caster .hand cid
  let priority ← cSteps ready [⟨.player active, .pass⟩]
  let stacked ← cSteps priority [⟨.player caster, .playCard sigil⟩]
  let layer ← (stacked.zone .stack).head?
  let passed ← cSteps stacked [⟨.player caster, .pass⟩]
  let (resolved, events) ← (step 64 passed ⟨.player active, .pass⟩).toOption
  let graveyard := Zone.player caster .graveyard
  let discarded ← (resolved.zone graveyard).head?
  pure (card.status == .full && stacked.zone .stack == [layer] &&
    stacked.zone (.player caster .hand) == [] &&
    stacked.lifeOf caster == 40 && passed.lifeOf caster == 40 &&
    resolved.lifeOf caster == 40 + Int.ofNat amount && resolved.lifeOf active == 40 &&
    resolved.active == some active && resolved.poolOf caster == ready.poolOf caster &&
    resolved.zone .stack == [] && resolved.zone graveyard == [discarded] &&
    (resolved.cardDefOf? discarded).map (·.id) == some cid &&
    events.countP (· == .moved layer discarded .stack graveyard) == 1)

#guard checkSigilOfSolace ⟨"WTR_173_R"⟩ 3 == some true
#guard checkSigilOfSolace ⟨"WTR_174_Y"⟩ 2 == some true
#guard checkSigilOfSolace ⟨"WTR_175_B"⟩ 1 == some true

/-- Play Sink Below in reaction and inspect both choices and an empty defender hand. -/
meta def checkSinkBelow (cid : CardId) (defenseValue : Nat) : Option Bool := do
  let attacker : PlayerId := ⟨0⟩
  let defender : PlayerId := ⟨1⟩
  let hand := Zone.player defender .hand
  let deck := Zone.player defender .deck
  let card ← m5Base.cards.find? cid
  let (withAttack, attack) ← cPlace m5Base attacker .hand ⟨"WTR_203_R"⟩
  let (deckBase, keptDeck) ← cPlace withAttack defender .deck ⟨"WTR_188_R"⟩
  let (withDeck, deckTop) ← cPlace deckBase defender .deck ⟨"WTR_189_Y"⟩
  let (noExtraHand, sink) ← cPlace withDeck defender .hand cid
  let (withChoice, chosen) ← cPlace noExtraHand defender .hand ⟨"WTR_204_Y"⟩
  let (withOther, keptHand) ← cPlace withChoice defender .hand ⟨"WTR_205_B"⟩
  let play := fun (s : GameState) =>
    cSteps s ([⟨.player attacker, .playCard attack⟩] ++ passBoth ++ passBoth ++
      [⟨.player defender, .defendDone⟩] ++ passBoth ++
      [⟨.player attacker, .pass⟩, ⟨.player defender, .playCard sink⟩,
       ⟨.player defender, .pass⟩, ⟨.player attacker, .pass⟩])
  let prompt ← play withOther
  let emptyResolved ← play noExtraHand
  let declined ← cSteps prompt [⟨.player defender, .pickMay false⟩]
  let choosing ← cSteps prompt [⟨.player defender, .pickMay true⟩]
  let (accepted, events) ← (step 64 choosing ⟨.player defender, .handToDeckPick chosen⟩).toOption
  let drawn ← (accepted.zone hand).head?
  let bottom ← (accepted.zone deck).getLast?
  let acceptedDamage ← cSteps accepted passBoth
  let declinedDamage ← cSteps declined passBoth
  let emptyDamage ← cSteps emptyResolved passBoth
  let damageOk := fun (s : GameState) =>
    s.lifeOf defender == 40 - Int.ofNat (4 - defenseValue) &&
    (s.combat.bind CombatChain.activeLink?).map (linkTotalDefense s) == some defenseValue
  pure (card.status == .full && prompt.zone hand == [keptHand, chosen] &&
    choosing.pending.head? == some (.chooseHandToDeck defender .bottom) &&
    declined.zone hand == [keptHand, chosen] && declined.zone deck == [deckTop, keptDeck] &&
    accepted.zone hand == [drawn, keptHand] && accepted.zone deck == [keptDeck, bottom] &&
    (accepted.cardDefOf? drawn).map (·.id) == some ⟨"WTR_189_Y"⟩ &&
    (accepted.cardDefOf? bottom).map (·.id) == some ⟨"WTR_204_Y"⟩ &&
    events.countP (· == .moved chosen bottom hand deck) == 1 &&
    events.countP (· == .drawn defender drawn) == 1 &&
    emptyResolved.zone .stack == [] && emptyResolved.zone hand == [] &&
    emptyResolved.zone deck == [deckTop, keptDeck] &&
    [acceptedDamage, declinedDamage, emptyDamage].all damageOk)

#guard checkSinkBelow ⟨"WTR_215_R"⟩ 4 == some true
#guard checkSinkBelow ⟨"WTR_216_Y"⟩ 3 == some true

/-- Check Disable's damage threshold and the arsenal move after its trigger resolves. -/
meta def checkDisable (cid : CardId) (power : Nat) : Option Bool := do
  let attacker : PlayerId := ⟨0⟩
  let defender : PlayerId := ⟨1⟩
  let funded := m5Base.setPool attacker { actionPoints := 1, resources := 5 }
  let card ← funded.cards.find? cid
  let (withAttack, attackId) ← cPlace funded attacker .hand cid
  let (withDeck, deckTop) ← cPlace withAttack defender .deck ⟨"WTR_188_R"⟩
  let arsenalZone := Zone.player defender .arsenal
  let deckZone := Zone.player defender .deck
  let (withArsenal, arsenalId) ← cPlace withDeck defender .arsenal ⟨"WTR_203_R"⟩ true
  let (ready, blocker) ← cPlace withArsenal defender .hand ⟨"WTR_204_Y"⟩
  let play := [⟨.player attacker, .playCard attackId⟩] ++ passBoth ++ passBoth
  let defense ← cSteps ready play
  let finishDefense := [⟨.player defender, .defendDone⟩] ++ passBoth ++ passBoth
  let (atFour, _, _) := execPrim defense defender ⟨0⟩ []
    (.preventNextDamage .controller (.const (Int.ofNat (power - 4))) .thisTurn)
  let (atThree, _, _) := execPrim defense defender ⟨0⟩ []
    (.preventNextDamage .controller (.const (Int.ofNat (power - 6))) .thisTurn)
  let crushed ← cSteps atFour finishDefense
  let blocked ← cSteps atThree ([⟨.player defender, .defendCard blocker⟩] ++ finishDefense)
  let stackCrush := fun (s : GameState) => do
    let trigger ← s.pendingTriggers.head?
    cSteps s [⟨.player attacker, .pickTriggerStart attacker⟩,
      ⟨.player attacker, .pickTrigger trigger.id⟩]
  let stacked ← stackCrush crushed
  let passed ← cSteps stacked [⟨.player attacker, .pass⟩]
  let (resolved, events) ← (step 64 passed ⟨.player defender, .pass⟩).toOption
  let bottom ← (resolved.zone deckZone).getLast?
  let emptyArsenal ← cSteps withDeck (play ++ finishDefense)
  let emptyStacked ← stackCrush emptyArsenal
  let emptyResolved ← cSteps emptyStacked passBoth
  pure (card.status == .full && (defense.poolOf attacker).resources == 0 &&
    crushed.lifeOf defender == 36 && crushed.pendingTriggers.length == 1 &&
    blocked.lifeOf defender == 37 && blocked.pendingTriggers.isEmpty &&
    [crushed, stacked, blocked].all (fun s => s.zone arsenalZone == [arsenalId] &&
      s.zone deckZone == [deckTop]) &&
    resolved.zone arsenalZone == [] && resolved.zone deckZone == [deckTop, bottom] &&
    (resolved.cardDefOf? bottom).map (·.id) == some ⟨"WTR_203_R"⟩ &&
    events.countP (· == .moved arsenalId bottom arsenalZone deckZone) == 1 &&
    emptyArsenal.lifeOf defender == 40 - Int.ofNat power &&
    emptyResolved.zone arsenalZone == [] && emptyResolved.zone deckZone == [deckTop] &&
    (emptyResolved.zone .stack).isEmpty)

#guard checkDisable ⟨"WTR_048_R"⟩ 9 == some true
#guard checkDisable ⟨"WTR_049_Y"⟩ 8 == some true
#guard checkDisable ⟨"WTR_050_B"⟩ 7 == some true

/-- Resolve Crippling Crush with different chance outcomes and with fewer than two cards. -/
meta def checkCripplingCrush : Option Bool := do
  let attacker : PlayerId := ⟨0⟩
  let defender : PlayerId := ⟨1⟩
  let cid : CardId := ⟨"WTR_043_R"⟩
  let funded := m5Base.setPool attacker { actionPoints := 1, resources := 7 }
  let card ← funded.cards.find? cid
  let bravo ← funded.cards.find? ⟨"WTR_038"⟩
  let (withHero, _) ← cPlace funded attacker .hero bravo.id
  let (withAttack, attack) ← cPlace withHero attacker .hand cid
  let (shortHand, first) ← cPlace withAttack defender .hand ⟨"WTR_203_R"⟩
  let (twoCards, second) ← cPlace shortHand defender .hand ⟨"WTR_204_Y"⟩
  let (threeCards, third) ← cPlace twoCards defender .hand ⟨"WTR_205_B"⟩
  let play := [⟨.player attacker, .playCard attack⟩] ++ passBoth ++ passBoth
  let damage := fun (s : GameState) (prevent : Int) => do
    let defense ← cSteps s play
    let (shielded, _, _) := execPrim defense defender ⟨0⟩ []
      (.preventNextDamage .controller (.const prevent) .thisTurn)
    cSteps shielded ([⟨.player defender, .defendDone⟩] ++ passBoth ++ passBoth)
  let resolveCrush := fun (s : GameState) => do
    let trigger ← s.pendingTriggers.head?
    cSteps s ([⟨.player attacker, .pickTriggerStart attacker⟩,
      ⟨.player attacker, .pickTrigger trigger.id⟩] ++ passBoth)
  let crushed ← damage threeCards 7
  let belowThreshold ← damage threeCards 8
  let chance ← resolveCrush crushed
  let hand := Zone.player defender .hand
  let graveyard := Zone.player defender .graveyard
  let shuffle := fun ids => (⟨.chance, .shuffleOrder ids⟩ : Action)
  let (resolved, events) ← (step 64 chance (shuffle [first, third, second])).toOption
  let other ← cSteps chance [shuffle [second, first, third]]
  let shortCrushed ← damage shortHand 7
  let shortResolved ← resolveCrush shortCrushed
  let discarded := resolved.zone graveyard
  pure (card.status == .full && decide (CardAllowedForHero funded.cards bravo cid) &&
    crushed.lifeOf defender == 36 && crushed.pendingTriggers.length == 1 &&
    belowThreshold.lifeOf defender == 37 && belowThreshold.pendingTriggers.isEmpty &&
    belowThreshold.zone hand == threeCards.zone hand &&
    chance.pending.head? == some (.chanceShuffle hand) &&
    chance.zone hand == threeCards.zone hand && chance.zone graveyard == [] &&
    (step 64 chance (shuffle [first, first, third])).toOption.isNone &&
    resolved.zone hand == [second] && other.zone hand == [third] &&
    discarded.length == 2 && discarded.all (fun id => events.contains (.discarded defender id)) &&
    (resolved.zone .stack).isEmpty && (shortResolved.zone .stack).isEmpty &&
    shortResolved.zone hand == [] && (shortResolved.zone graveyard).length == 1)

#guard checkCripplingCrush == some true

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
#guard checkOpenTheCenter ⟨"WTR_097_B"⟩ 3
