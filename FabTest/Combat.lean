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

-- 5. Multi-Link Ninja Combo Chain with Go Again (CR 7.6, 8.3.6).
/-- Check the power, Go Again, and hit trigger granted by Whelming Gustwave's combo. -/
meta def checkWhelmingGustwave (cid : CardId) (basePower : Nat) : Option Bool := do
  let attacker : PlayerId := ⟨0⟩
  let defender : PlayerId := ⟨1⟩
  let deck := Zone.player attacker .deck
  let hand := Zone.player attacker .hand
  let funded := m5Base.setPool attacker { actionPoints := 1, resources := 2 }
  let card ← funded.cards.find? cid
  let (withSurge, surge) ← cPlace funded attacker .hand ⟨"WTR_107_R"⟩
  let (withGust, gust) ← cPlace withSurge attacker .hand cid
  let (withJab, jab) ← cPlace withGust attacker .hand ⟨"WTR_098_R"⟩
  let (withDeck, top) ← cPlace withJab attacker .deck ⟨"WTR_188_R"⟩
  let (oneBlock, first) ← cPlace withDeck defender .hand ⟨"WTR_203_R"⟩
  let (ready, second) ← cPlace oneBlock defender .hand ⟨"WTR_204_Y"⟩
  let enter := fun id => [⟨.player attacker, .playCard id⟩] ++ passBoth ++ passBoth
  let toDamage := [⟨.player defender, .defendDone⟩] ++ passBoth ++ passBoth
  let finish := toDamage ++ passBoth
  let firstLink ← cSteps ready (enter surge ++ finish)
  let defense ← cSteps firstLink (enter gust)
  let hit ← cSteps defense toDamage
  let blocked ← cSteps defense ([⟨.player defender, .defendCard first⟩,
    ⟨.player defender, .defendCard second⟩] ++ finish)
  let trigger ← hit.pendingTriggers.head?
  let stacked ← cSteps hit [⟨.player attacker, .pickTriggerStart attacker⟩,
    ⟨.player attacker, .pickTrigger trigger.id⟩, ⟨.player attacker, .pass⟩]
  let (resolved, events) ← (step 64 stacked ⟨.player defender, .pass⟩).toOption
  let drawn ← (resolved.zone hand).head?
  let secondLink ← cSteps resolved passBoth
  let closed ← cSteps secondLink passBoth
  let standalone ← cSteps ready (enter gust ++ finish)
  let intervened ← cSteps firstLink (enter jab ++ finish ++ enter gust ++ finish)
  let withoutCombo := fun (s : GameState) =>
    (s.combat.bind CombatChain.activeLink?).map (fun link => (link.powerBonus, link.damageDealt)) ==
      some (0, basePower) &&
    (s.poolOf attacker).actionPoints == 0 && s.pendingTriggers.isEmpty && s.zone deck == [top]
  pure (card.status == .full && firstLink.lifeOf defender == 35 &&
    (firstLink.poolOf attacker).actionPoints == 1 &&
    firstLink.combat.map (fun cc => (cc.step, cc.links.length)) == some (.resolution, 1) &&
    hit.lifeOf defender == 35 - Int.ofNat (basePower + 1) &&
    (hit.combat.bind CombatChain.activeLink?).map (·.powerBonus) == some 1 &&
    hit.pendingTriggers.length == 1 && hit.zone deck == [top] && stacked.zone deck == [top] &&
    resolved.zone deck == [] && resolved.zone hand == [drawn, jab] &&
    (resolved.cardDefOf? drawn).map (·.id) == some ⟨"WTR_188_R"⟩ &&
    events.countP (· == .drawn attacker drawn) == 1 &&
    secondLink.combat.map (fun cc => (cc.step, cc.links.length)) == some (.resolution, 2) &&
    (secondLink.poolOf attacker).actionPoints == 1 &&
    blocked.lifeOf defender == 35 && blocked.pendingTriggers.isEmpty && blocked.zone deck == [top] &&
    (blocked.poolOf attacker).actionPoints == 1 &&
    closed.combat.isNone && (closed.zone (.player attacker .graveyard)).length == 2 &&
    withoutCombo standalone && withoutCombo intervened)

#guard checkWhelmingGustwave ⟨"WTR_110_R"⟩ 3 == some true
#guard checkWhelmingGustwave ⟨"WTR_111_Y"⟩ 2 == some true
#guard checkWhelmingGustwave ⟨"WTR_112_B"⟩ 1 == some true

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

/-- An on-play life condition is checked after payment and before either player responds. -/
meta def checkWoundedBull (cid : CardId) (power : Nat) : Option Bool := do
  let attacker : PlayerId := ⟨0⟩
  let defender : PlayerId := ⟨1⟩
  let funded := (m5Base.setLife attacker 39).setPool attacker { actionPoints := 1, resources := 3 }
  let card ← funded.cards.find? cid
  let (withBull, bull) ← cPlace funded attacker .hand cid
  let (withHealing, ownSigil) ← cPlace withBull attacker .hand ⟨"WTR_173_R"⟩
  let (ready, theirSigil) ← cPlace withHealing defender .hand ⟨"WTR_173_R"⟩
  let playBull : Action := ⟨.player attacker, .playCard bull⟩
  let paid ← cSteps ready [playBull]
  let trigger ← paid.pendingTriggers.head?
  let stacked ← cSteps paid [⟨.player attacker, .pickTriggerStart attacker⟩,
    ⟨.player attacker, .pickTrigger trigger.id⟩]
  let highLife ← cSteps stacked ([⟨.player attacker, .playCard ownSigil⟩] ++ passBoth)
  let boosted ← cSteps highLife passBoth
  let paidEqual ← cSteps (ready.setLife attacker 40) [playBull]
  let nowBehind ← cSteps paidEqual [⟨.player attacker, .pass⟩,
    ⟨.player defender, .playCard theirSigil⟩, ⟨.player defender, .pass⟩, ⟨.player attacker, .pass⟩]
  let finish := passBoth ++ passBoth ++ [⟨.player defender, .defendDone⟩] ++
    passBoth ++ passBoth ++ passBoth
  let withBonus ← cSteps boosted finish
  let withoutBonus ← cSteps nowBehind finish
  let broke := ready.setPool attacker { actionPoints := 1 }
  let unpaid ← cSteps broke [playBull]
  let cancelled ← cSteps unpaid [⟨.player attacker, .cancelPlay⟩]
  pure (card.status == .full && (paid.poolOf attacker).resources == 0 &&
    paid.pendingTriggers.length == 1 && (stacked.zone .stack).length == 2 &&
    highLife.lifeOf attacker == 42 && boosted.zone .stack == paid.zone .stack &&
    paidEqual.pendingTriggers.isEmpty && (paidEqual.zone .stack).length == 1 &&
    nowBehind.lifeOf defender == 43 &&
    withBonus.lifeOf defender == 40 - Int.ofNat (power + 1) &&
    withoutBonus.lifeOf defender == 43 - Int.ofNat power &&
    (withBonus.combat.bind CombatChain.activeLink?).map (·.powerBonus) == some 1 &&
    (withoutBonus.combat.bind CombatChain.activeLink?).map (·.powerBonus) == some 0 &&
    unpaid.pendingTriggers.isEmpty && cancelled.pendingTriggers.isEmpty &&
    cancelled.zone (.player attacker .hand) == ready.zone (.player attacker .hand))

#guard checkWoundedBull ⟨"WTR_200_R"⟩ 7 == some true
#guard checkWoundedBull ⟨"WTR_201_Y"⟩ 6 == some true
#guard checkWoundedBull ⟨"WTR_202_B"⟩ 5 == some true

/-- Play Scar for a Scar from arsenal on an open chain and test its on-play Go Again. -/
meta def checkScarForAScar (cid : CardId) (power : Nat) : Option Bool := do
  let attacker : PlayerId := ⟨0⟩
  let defender : PlayerId := ⟨1⟩
  let funded := m5Base.setLife attacker 34
  let card ← funded.cards.find? cid
  let (withJab, jab) ← cPlace funded attacker .hand ⟨"WTR_098_R"⟩
  let (withScar, scar) ← cPlace withJab attacker .arsenal cid true
  let (oneBlock, first) ← cPlace withScar defender .hand ⟨"WTR_203_R"⟩
  let (ready, second) ← cPlace oneBlock defender .hand ⟨"WTR_204_Y"⟩
  let finish := [⟨.player defender, .defendDone⟩] ++ passBoth ++ passBoth ++ passBoth
  let prior ← cSteps ready ([⟨.player attacker, .playCard jab⟩] ++ passBoth ++ passBoth ++ finish)
  let playScar : Action := ⟨.player attacker, .playCard scar⟩
  let paid ← cSteps prior [playScar]
  let trigger ← paid.pendingTriggers.head?
  let boosted ← cSteps paid ([⟨.player attacker, .pickTriggerStart attacker⟩,
    ⟨.player attacker, .pickTrigger trigger.id⟩] ++ passBoth)
  let defense ← cSteps boosted (passBoth ++ passBoth)
  let hit ← cSteps defense finish
  let blocked ← cSteps defense ([⟨.player defender, .defendCard first⟩,
    ⟨.player defender, .defendCard second⟩] ++ finish)
  let paidEqual ← cSteps (prior.setLife attacker (prior.lifeOf defender)) [playScar]
  let equal ← cSteps paidEqual (passBoth ++ passBoth ++ finish)
  pure (card.status == .full && prior.lifeOf defender == 37 && trigger.fromArsenal &&
    paid.pendingTriggers.length == 1 && paid.zone (.player attacker .arsenal) == [] &&
    paidEqual.pendingTriggers.isEmpty &&
    hit.lifeOf defender == 37 - Int.ofNat power && equal.lifeOf defender == hit.lifeOf defender &&
    blocked.lifeOf defender == 37 &&
    hit.combat.map (fun cc => (cc.step, cc.links.length)) == some (.resolution, 2) &&
    (hit.poolOf attacker).actionPoints == 1 && (blocked.poolOf attacker).actionPoints == 1 &&
    (equal.poolOf attacker).actionPoints == 0)

#guard checkScarForAScar ⟨"WTR_191_R"⟩ 4 == some true
#guard checkScarForAScar ⟨"WTR_192_Y"⟩ 3 == some true
#guard checkScarForAScar ⟨"WTR_193_B"⟩ 2 == some true

/-- Last Ditch Effort's trigger uses the deck at play time, before responses. -/
meta def checkLastDitchEffort : Option Bool := do
  let attacker : PlayerId := ⟨0⟩
  let defender : PlayerId := ⟨1⟩
  let cid : CardId := ⟨"WTR_161_B"⟩
  let deck := Zone.player attacker .deck
  let funded := m5Base.setPool attacker { actionPoints := 1, resources := 3 }
  let card ← funded.cards.find? cid
  let (withAttack, attack) ← cPlace funded attacker .hand cid
  let (ready, reserve) ← cPlace withAttack attacker .hand ⟨"WTR_203_R"⟩
  let play := [⟨.player attacker, .playCard attack⟩]
  let paidEmpty ← cSteps ready play
  let trigger ← paidEmpty.pendingTriggers.head?
  let (replenished, _) ← moveObj paidEmpty reserve deck .bottom false
  let stacked ← cSteps replenished [⟨.player attacker, .pickTriggerStart attacker⟩,
    ⟨.player attacker, .pickTrigger trigger.id⟩]
  let buffed ← cSteps stacked passBoth
  let (withDeck, deckCard) ← cPlace ready attacker .deck ⟨"WTR_204_Y"⟩
  let paidNonempty ← cSteps withDeck play
  let (depleted, _) ← moveObj paidNonempty deckCard (.player attacker .hand) .top false
  let finish := passBoth ++ passBoth ++ [⟨.player defender, .defendDone⟩] ++
    passBoth ++ passBoth ++ passBoth
  let boostedHit ← cSteps buffed finish
  let normalHit ← cSteps depleted finish
  let boostedLink ← boostedHit.combat.bind CombatChain.activeLink?
  let normalLink ← normalHit.combat.bind CombatChain.activeLink?
  pure (card.status == .full && card.front.pitch == some 3 && card.front.defense == some 3 &&
    (paidEmpty.poolOf attacker).resources == 0 && (paidEmpty.poolOf attacker).actionPoints == 0 &&
    paidEmpty.zone deck == [] && paidEmpty.pendingTriggers.length == 1 &&
    (replenished.zone deck).length == 1 && paidNonempty.pendingTriggers.isEmpty &&
    depleted.zone deck == [] && boostedLink.powerBonus == 4 && normalLink.powerBonus == 0 &&
    linkHasKeyword boostedHit boostedLink .goAgain && !linkHasKeyword normalHit normalLink .goAgain &&
    boostedHit.lifeOf defender == 32 && normalHit.lifeOf defender == 36 &&
    (boostedHit.poolOf attacker).actionPoints == 1 && (normalHit.poolOf attacker).actionPoints == 0)

#guard checkLastDitchEffort == some true

/-- Verify the first qualifying attack claims the bonus, including across plays and turn cleanup. -/
meta def checkNextAttackCardPower (cid : CardId) (cost bonus : Nat) (lowCost : Bool) : Option Bool := do
  let attacker : PlayerId := ⟨0⟩
  let defender : PlayerId := ⟨1⟩
  let funded := m5Base.setPool attacker { actionPoints := 1, resources := 12 }
  let card ← funded.cards.find? cid
  let low : CardId := ⟨"WTR_101_R"⟩
  let high : CardId := ⟨"WTR_107_R"⟩
  let eligible := if lowCost then low else high
  let ineligible := if lowCost then high else low
  let eligiblePower : Nat := if lowCost then 4 else 5
  let ineligiblePower : Nat := if lowCost then 5 else 4
  let (withBuff, buff) ← cPlace funded attacker .hand cid
  let (withSecondBuff, secondBuff) ← cPlace withBuff attacker .hand cid
  let (withOther, other) ← cPlace withSecondBuff attacker .hand ineligible
  let (withFirst, first) ← cPlace withOther attacker .hand eligible
  let (withSecond, second) ← cPlace withFirst attacker .hand eligible
  let (ready, instant) ← cPlace withSecond attacker .hand ⟨"WTR_173_R"⟩
  let play := fun id => [⟨.player attacker, .playCard id⟩]
  let fight := fun id => play id ++ passBoth ++ passBoth ++
    [⟨.player defender, .defendDone⟩] ++ passBoth ++ passBoth ++ passBoth
  let buffed ← cSteps ready (play buff ++ passBoth)
  let afterInstant ← cSteps buffed (play instant ++ passBoth)
  let afterOther ← cSteps afterInstant (fight other)
  let enhanced ← cSteps afterOther (fight first)
  let normal ← cSteps enhanced (fight second)
  let doubleBuff ← cSteps buffed (play secondBuff ++ passBoth)
  let doubleEnhanced ← cSteps doubleBuff (fight first)
  let unpaid ← cSteps (buffed.setPool attacker { actionPoints := 1 }) (play first)
  let cancelled ← cSteps unpaid [⟨.player attacker, .cancelPlay⟩]
  let ended ← cSteps buffed (passBoth ++ [⟨.player attacker, .arsenalSkip⟩])
  let combatDamage := fun (s : GameState) =>
    (s.combat.bind CombatChain.activeLink?).map (·.damageDealt)
  pure (card.status == .full && (buffed.poolOf attacker).actionPoints == 1 &&
    (buffed.poolOf attacker).resources == 12 - cost && buffed.activeEffects.length == 1 &&
    objEffectivePower buffed first == some (Int.ofNat eligiblePower) &&
    afterInstant.activeEffects == buffed.activeEffects &&
    combatDamage afterOther == some ineligiblePower && afterOther.activeEffects == buffed.activeEffects &&
    combatDamage enhanced == some (eligiblePower + bonus) && enhanced.activeEffects.isEmpty &&
    combatDamage normal == some eligiblePower &&
    doubleBuff.activeEffects.length == 2 &&
    combatDamage doubleEnhanced == some (eligiblePower + 2 * bonus) &&
    doubleEnhanced.activeEffects.isEmpty &&
    unpaid.activeEffects == buffed.activeEffects && cancelled.activeEffects == buffed.activeEffects &&
    cancelled.zone (.player attacker .hand) == buffed.zone (.player attacker .hand) &&
    ended.activeEffects.isEmpty && (ended.poolOf attacker).actionPoints == 0)

#guard checkNextAttackCardPower ⟨"WTR_218_R"⟩ 0 3 true == some true
#guard checkNextAttackCardPower ⟨"WTR_219_Y"⟩ 0 2 true == some true
#guard checkNextAttackCardPower ⟨"WTR_220_B"⟩ 0 1 true == some true
#guard checkNextAttackCardPower ⟨"WTR_221_R"⟩ 3 6 false == some true
#guard checkNextAttackCardPower ⟨"WTR_222_Y"⟩ 3 5 false == some true
#guard checkNextAttackCardPower ⟨"WTR_223_B"⟩ 3 4 false == some true

/-- Each cost filter keeps its effect until a qualifying attack is played. -/
meta def checkSloggismWithNimblism : Option Bool := do
  let attacker : PlayerId := ⟨0⟩
  let defender : PlayerId := ⟨1⟩
  let funded := m5Base.setPool attacker { actionPoints := 1, resources := 6 }
  let (withNimblism, nimblism) ← cPlace funded attacker .hand ⟨"WTR_220_B"⟩
  let (withSloggism, sloggism) ← cPlace withNimblism attacker .hand ⟨"WTR_221_R"⟩
  let (withSurge, surge) ← cPlace withSloggism attacker .hand ⟨"WTR_107_R"⟩
  let (ready, tap) ← cPlace withSurge attacker .hand ⟨"WTR_101_R"⟩
  let resolve := fun id => [⟨.player attacker, .playCard id⟩] ++ passBoth
  let fight := fun id => resolve id ++ passBoth ++
    [⟨.player defender, .defendDone⟩] ++ passBoth ++ passBoth ++ passBoth
  let both ← cSteps ready (resolve nimblism ++ resolve sloggism)
  let first ← cSteps both (fight surge)
  let last ← cSteps first (fight tap)
  pure (both.activeEffects.length == 2 &&
    first.activeEffects.map (·.op) == [.addPower 1] && first.lifeOf defender == 29 &&
    last.activeEffects.isEmpty && last.lifeOf defender == 24)

#guard checkSloggismWithNimblism == some true

/-- Check Awakening Bellow's hidden random card, return, and next Brute attack bonus. -/
meta def checkAwakeningBellow (cid : CardId) (bonus : Int) : Option Bool := do
  let attacker : PlayerId := ⟨0⟩
  let defender : PlayerId := ⟨1⟩
  let hand := Zone.player defender .hand
  let banished := Zone.player defender .banished
  let funded := m5Base.setPool attacker { actionPoints := 1, resources := 4 }
  let card ← funded.cards.find? cid
  let (withBellow, bellow) ← cPlace funded attacker .hand cid
  let (withJab, jab) ← cPlace withBellow attacker .hand ⟨"WTR_098_R"⟩
  let (withHunt, hunt) ← cPlace withJab attacker .hand ⟨"WTR_023_R"⟩
  let (withFirst, first) ← cPlace withHunt defender .hand ⟨"WTR_203_R"⟩
  let (ready, second) ← cPlace withFirst defender .hand ⟨"WTR_204_Y"⟩
  let firstCard ← ready.obj? first
  let secondCard ← ready.obj? second
  let play := fun id => [⟨.player attacker, .playCard id⟩]
  let choosing ← cSteps ready (play bellow)
  let declare := fun target => (⟨.player attacker, .pickHeroTarget target⟩ : Action)
  let (paidBellow, declaration) ← (step 64 choosing (declare defender)).toOption
  let chance ← cSteps paidBellow passBoth
  let shuffle := fun ids => (⟨.chance, .shuffleOrder ids⟩ : Action)
  let (buffed, events) ← (step 64 chance (shuffle [first, second])).toOption
  let other ← cSteps chance [shuffle [second, first]]
  let hidden ← (buffed.zone banished).head?
  let otherHidden ← (other.zone banished).head?
  let afterJab ← cSteps buffed (play jab ++ passBoth ++ passBoth ++
    [⟨.player defender, .defendDone⟩] ++ passBoth ++ passBoth ++ passBoth)
  let paid ← cSteps afterJab (play hunt)
  let attackLayer ← (paid.zone .stack).head?
  let atEnd ← cSteps buffed passBoth
  let returnTrigger ← atEnd.pendingTriggers.head?
  let returned ← cSteps atEnd [⟨.player attacker, .pickTriggerStart attacker⟩,
    ⟨.player attacker, .pickTrigger returnTrigger.id⟩]
  let returnedId ← (returned.zone hand).head?
  let ended ← cSteps returned [⟨.player attacker, .arsenalSkip⟩]
  let layer ← (choosing.zone .stack).head?
  let cancel := (⟨.player attacker, .cancelPlay⟩ : Action)
  let cancelled ← cSteps choosing [cancel]
  let unfunded := ready.setPool attacker { actionPoints := 1 }
  let pitching ← cSteps unfunded (play bellow ++ [declare attacker])
  let cancelledAfterTarget ← cSteps pitching [cancel]
  let selfBuffed ← cSteps pitching ([⟨.player attacker, .pitchCard jab⟩] ++ passBoth)
  let selfHidden ← (selfBuffed.zone (.player attacker .banished)).head?
  let atSelfEnd ← cSteps selfBuffed passBoth
  let selfTrigger ← atSelfEnd.pendingTriggers.head?
  let selfReturned ← cSteps atSelfEnd [⟨.player attacker, .pickTriggerStart attacker⟩,
    ⟨.player attacker, .pickTrigger selfTrigger.id⟩]
  let selfReturnedId ← (selfReturned.zone (.player attacker .hand)).head?
  let huntCard ← ready.obj? hunt
  let targetChecks := (choosing.pending.head? == some (.choosePlayHero attacker layer false none
      { actionPoints := 1, resources := 1 }) &&
    choosing.poolOf attacker == ready.poolOf attacker &&
    (legalActionsFor attacker choosing).contains (declare attacker) &&
    (legalActionsFor attacker choosing).contains (declare defender) &&
    (step 64 choosing (declare ⟨2⟩)).toOption.isNone &&
    (step 64 choosing ⟨.player defender, .pickHeroTarget defender⟩).toOption.isNone &&
    decide (cancelled = ready) && decide (cancelledAfterTarget = unfunded) &&
    declaration == [.targetedHero layer defender] &&
    (paidBellow.layerMeta.get? layer.n).bind (·.heroTarget) == some defender &&
    selfBuffed.zone hand == ready.zone hand &&
    selfBuffed.activeEffects.map (·.op) == buffed.activeEffects.map (·.op) &&
    (selfBuffed.obj? selfHidden).map (fun o => (o.kind, o.faceDown)) == some (huntCard.kind, true) &&
    (selfReturned.obj? selfReturnedId).map (fun o => (o.kind, o.faceDown)) ==
      some (huntCard.kind, false) &&
    selfReturned.pending.head? == some (.chooseArsenal attacker))
  pure (card.status == .full && targetChecks && chance.pending.head? == some (.chanceShuffle hand) &&
    chance.zone hand == ready.zone hand && chance.zone banished == [] &&
    (step 64 chance (shuffle [first, first])).toOption.isNone &&
    (buffed.poolOf attacker).resources == 3 && (buffed.poolOf attacker).actionPoints == 1 &&
    buffed.zone hand == [second] && buffed.zone banished == [hidden] &&
    (buffed.obj? hidden).map (fun o => (o.kind, o.faceDown)) == some (firstCard.kind, true) &&
    events.countP (· == .banished defender hidden true) == 1 &&
    other.zone hand == [first] &&
    (other.obj? otherHidden).map (fun o => (o.kind, o.faceDown)) == some (secondCard.kind, true) &&
    afterJab.lifeOf defender == 37 && afterJab.activeEffects == buffed.activeEffects &&
    (paid.layerMeta.get? attackLayer.n).map (·.attackPowerBonus) == some bonus &&
    paid.activeEffects.isEmpty && atEnd.phase == .endPhase && returnTrigger.source == hidden &&
    returned.zone hand == [returnedId, second] && returned.zone banished == [] &&
    returned.pending.head? == some (.chooseArsenal attacker) &&
    (returned.obj? returnedId).map (fun o => (o.kind, o.faceDown)) == some (firstCard.kind, false) &&
    ended.delayedTriggers.isEmpty && ended.activeEffects.isEmpty)

#guard checkAwakeningBellow ⟨"WTR_032_R"⟩ 3 == some true
#guard checkAwakeningBellow ⟨"WTR_033_Y"⟩ 2 == some true
#guard checkAwakeningBellow ⟨"WTR_034_B"⟩ 1 == some true

/-- Play an attack with Intimidate and use the remaining hand card to defend. -/
meta def checkIntimidateAttack (cid : CardId) (pitch cost power : Nat) : Option Bool := do
  let attacker : PlayerId := ⟨0⟩
  let defender : PlayerId := ⟨1⟩
  let funded := m5Base.setPool attacker { actionPoints := 1, resources := cost + 1 }
  let hand := Zone.player defender .hand
  let banished := Zone.player defender .banished
  let card ← funded.cards.find? cid
  let (withReserve, reserve) ← cPlace funded attacker .hand ⟨"WTR_205_B"⟩
  let (withAttack, attackId) ← cPlace withReserve attacker .hand cid
  let (withFirst, first) ← cPlace withAttack defender .hand ⟨"WTR_203_R"⟩
  let (ready, second) ← cPlace withFirst defender .hand ⟨"WTR_204_Y"⟩
  let paid ← cSteps ready [⟨.player attacker, .playCard attackId⟩]
  let attacking ← cSteps paid passBoth
  let link ← attacking.combat.bind CombatChain.activeLink?
  let trigger ← attacking.pendingTriggers.head?
  let choosing ← cSteps attacking [⟨.player attacker, .pickTriggerStart attacker⟩]
  let declare := fun p => (⟨.player attacker, .pickTrigger trigger.id (some p)⟩ : Action)
  let (stacked, declaration) ← (step 64 choosing (declare defender)).toOption
  let layer ← (stacked.zone .stack).head?
  let chance ← cSteps stacked passBoth
  let (intimidated, events) ← (step 64 chance ⟨.chance, .shuffleOrder [first, second]⟩).toOption
  let hidden ← (intimidated.zone banished).head?
  let defending ← cSteps intimidated passBoth
  let finishCombat := [⟨.player defender, .defendCard second⟩,
    ⟨.player defender, .defendDone⟩] ++ passBoth ++ passBoth ++ passBoth ++ passBoth
  let closed ← cSteps defending finishCombat
  let atEnd ← cSteps closed passBoth
  let delayed ← atEnd.pendingTriggers.head?
  let returned ← cSteps atEnd [⟨.player attacker, .pickTriggerStart attacker⟩,
    ⟨.player attacker, .pickTrigger delayed.id⟩]
  let returnedId ← (returned.zone hand).head?
  let selfIntimidated ← cSteps choosing ([declare attacker] ++ passBoth)
  let selfBanished ← (selfIntimidated.zone (.player attacker .banished)).head?
  let selfAtEnd ← cSteps selfIntimidated (passBoth ++ finishCombat ++ passBoth)
  let selfDelayed ← selfAtEnd.pendingTriggers.head?
  let selfReturned ← cSteps selfAtEnd [⟨.player attacker, .pickTriggerStart attacker⟩,
    ⟨.player attacker, .pickTrigger selfDelayed.id⟩]
  let selfReturnedId ← (selfReturned.zone (.player attacker .hand)).head?
  pure (card.status == .full && card.front.pitch == some pitch && card.front.defense == some 3 &&
    paid.pendingTriggers.isEmpty && paid.zone hand == ready.zone hand &&
    (paid.poolOf attacker).resources == 1 && (paid.poolOf attacker).actionPoints == 0 &&
    attacking.combat.map (·.step) == some .attack &&
    attacking.pending.head? == some (.chooseTriggerStart attacker) &&
    attacking.pendingTriggers.length == 1 && some trigger.source == link.attack &&
    (legalActionsFor attacker choosing).contains (declare defender) &&
    (legalActionsFor attacker choosing).contains (declare attacker) &&
    (step 64 choosing (declare ⟨2⟩)).toOption.isNone &&
    (step 64 choosing ⟨.player attacker, .pickTrigger trigger.id⟩).toOption.isNone &&
    stacked.pending.head? == some (.priority attacker 0) && (stacked.zone .stack).length == 1 &&
    declaration == [.targetedHero layer defender] &&
    chance.pending.head? == some (.chanceShuffle hand) && chance.zone banished == [] &&
    intimidated.zone hand == [second] && (intimidated.obj? hidden).map (·.faceDown) == some true &&
    events.countP (· == .banished defender hidden true) == 1 &&
    defending.pending.head? == some (.defendPick defender) &&
    (step 64 defending ⟨.player defender, .defendCard hidden⟩).toOption.isNone &&
    closed.combat.isNone && closed.lifeOf defender == 40 - Int.ofNat (power - 3) &&
    closed.delayedTriggers.length == 1 && delayed.source == hidden &&
    returned.zone banished == [] && returned.zone hand == [returnedId] &&
    (returned.obj? returnedId).map (fun o => (o.kind, o.faceDown)) ==
      (ready.obj? first).map (fun o => (o.kind, false)) &&
    selfIntimidated.zone hand == ready.zone hand &&
    selfIntimidated.zone (.player attacker .hand) == [] &&
    (selfIntimidated.obj? selfBanished).map (fun o => (o.kind, o.faceDown)) ==
      (ready.obj? reserve).map (fun o => (o.kind, true)) &&
    selfDelayed.source == selfBanished &&
    (selfReturned.obj? selfReturnedId).map (fun o => (o.kind, o.faceDown)) ==
      (ready.obj? reserve).map (fun o => (o.kind, false)) &&
    selfReturned.pending.head? == some (.chooseArsenal attacker))

#guard checkIntimidateAttack ⟨"WTR_023_R"⟩ 1 2 6 == some true
#guard checkIntimidateAttack ⟨"WTR_024_Y"⟩ 2 2 5 == some true
#guard checkIntimidateAttack ⟨"WTR_025_B"⟩ 3 2 4 == some true
#guard checkIntimidateAttack ⟨"WTR_026_R"⟩ 1 3 7 == some true
#guard checkIntimidateAttack ⟨"WTR_027_Y"⟩ 2 3 6 == some true
#guard checkIntimidateAttack ⟨"WTR_028_B"⟩ 3 3 5 == some true

/-- Verify Unmovable's own defense and final damage when played from hand or arsenal. -/
meta def checkUnmovable (cid : CardId) (pitch defense : Nat) (fromArsenal : Bool) :
    Option Bool := do
  let attacker : PlayerId := ⟨0⟩
  let defender : PlayerId := ⟨1⟩
  let origin : ZoneKind := if fromArsenal then .arsenal else .hand
  let fundedAttack := m5Base.setPool attacker { actionPoints := 1, resources := 6 }
  let funded := fundedAttack.setPool defender { resources := 3 }
  let card ← funded.cards.find? cid
  let (withBoost, boost) ← cPlace funded attacker .hand ⟨"WTR_223_B"⟩
  let (withAttack, attack) ← cPlace withBoost attacker .hand ⟨"WTR_188_R"⟩
  let (ready, reaction) ← cPlace withAttack defender origin cid fromArsenal
  let defend ← cSteps ready ([⟨.player attacker, .playCard boost⟩] ++ passBoth ++
    [⟨.player attacker, .playCard attack⟩] ++ passBoth ++ passBoth)
  let offered ← cSteps defend
    ([⟨.player defender, .defendDone⟩] ++ passBoth ++ [⟨.player attacker, .pass⟩])
  let paid ← cSteps offered [⟨.player defender, .playCard reaction⟩]
  let layer ← (paid.zone .stack).head?
  let resolved ← cSteps paid [⟨.player defender, .pass⟩, ⟨.player attacker, .pass⟩]
  let link ← resolved.combat.bind CombatChain.activeLink?
  let defendingCard ← link.defending.head?
  let chars ← resolved.characteristics defendingCard
  let damaged ← cSteps resolved passBoth
  let closed ← cSteps damaged (passBoth ++ passBoth)
  let cleared ← (closed.zone (.player defender .graveyard)).head?
  let effectiveDefense := defense + (if fromArsenal then 1 else 0)
  pure (card.status == .full && card.front.pitch == some pitch &&
    (step 64 defend ⟨.player defender, .defendCard reaction⟩).toOption.isNone &&
    (step 64 offered ⟨.player defender, .playCard reaction⟩).toOption.isSome &&
    paid.zone (.player defender origin) == [] && (paid.poolOf defender).resources == 0 &&
    (paid.obj? layer).map (·.faceDown) == some false &&
    (paid.layerMeta.get? layer.n).map (·.fromArsenal) == some fromArsenal &&
    resolved.zone .stack == [] && link.defenseBonus == 0 &&
    link.defendedFromHandCount == (if fromArsenal then 0 else 1) &&
    chars.baseDefense == some (Int.ofNat defense) &&
    chars.defense == some (Int.ofNat effectiveDefense) &&
    linkTotalDefense resolved link == effectiveDefense &&
    damaged.lifeOf defender == 40 - Int.ofNat (11 - effectiveDefense) &&
    closed.combat.isNone && closed.activeEffects.isEmpty &&
    (closed.cardDefOf? cleared).map (·.id) == some cid &&
    objEffectiveDefense closed cleared == some (Int.ofNat defense))

#guard checkUnmovable ⟨"WTR_212_R"⟩ 1 7 false == some true
#guard checkUnmovable ⟨"WTR_212_R"⟩ 1 7 true == some true

/-- A stacked defense reaction checks Dominate again after the layer above it defends. -/
meta def checkUnmovableAgainstDominate (fromArsenal : Bool) : Option Bool := do
  let attacker : PlayerId := ⟨0⟩
  let defender : PlayerId := ⟨1⟩
  let cid : CardId := ⟨"WTR_212_R"⟩
  let origin : ZoneKind := if fromArsenal then .arsenal else .hand
  let funded := m5Base.setPool defender { resources := 3 }
  let (withAttack, attack) ← cPlace funded attacker .hand ⟨"WTR_203_R"⟩
  let (withUnmovable, unmovableId) ← cPlace withAttack defender origin cid fromArsenal
  let (ready, sink) ← cPlace withUnmovable defender .hand ⟨"WTR_217_B"⟩
  let defend ← cSteps ready ([⟨.player attacker, .playCard attack⟩] ++ passBoth ++ passBoth)
  let combat := defend.combat.map fun cc =>
    cc.updateActiveLink fun link => { link with grantedKeywords := [.dominate] }
  let dominated := { defend with combat := combat }
  let stacked ← cSteps dominated ([⟨.player defender, .defendDone⟩] ++ passBoth ++
    [⟨.player attacker, .pass⟩, ⟨.player defender, .playCard unmovableId⟩,
     ⟨.player defender, .playCard sink⟩])
  let upperResolved ← cSteps stacked [⟨.player defender, .pass⟩, ⟨.player attacker, .pass⟩]
  let bothResolved ← cSteps upperResolved passBoth
  let link ← bothResolved.combat.bind CombatChain.activeLink?
  let grave := bothResolved.zone (.player defender .graveyard)
  pure ((stacked.zone .stack).length == 2 && (upperResolved.zone .stack).length == 1 &&
    bothResolved.zone .stack == [] && link.defendedFromHandCount == 1 &&
    link.defending.length == (if fromArsenal then 2 else 1) &&
    linkTotalDefense bothResolved link == (if fromArsenal then 10 else 2) &&
    (if fromArsenal then grave == [] else grave.map (fun id => (bothResolved.cardDefOf? id).map (·.id)) ==
      [some cid]))

#guard checkUnmovableAgainstDominate false == some true
#guard checkUnmovableAgainstDominate true == some true

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
#guard checkSinkBelow ⟨"WTR_217_B"⟩ 2 == some true

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

/-- Hurricane Technique can return on a combo hit and be replayed without the prior combo. -/
meta def checkHurricaneTechnique : Option Bool := do
  let attacker : PlayerId := ⟨0⟩
  let defender : PlayerId := ⟨1⟩
  let cid : CardId := ⟨"WTR_084_Y"⟩
  let hand := Zone.player attacker .hand
  let graveyard := Zone.player attacker .graveyard
  let funded := m5Base.setPool attacker { actionPoints := 1, resources := 3 }
  let card ← funded.cards.find? cid
  let (withLeg, leg) ← cPlace funded attacker .hand ⟨"WTR_101_R"⟩
  let (withKnee, knee) ← cPlace withLeg attacker .hand ⟨"WTR_104_R"⟩
  let (withHurricane, hurricane) ← cPlace withKnee attacker .hand cid
  let physical ← (withHurricane.obj? hurricane).bind (·.kind.phys?)
  let (oneBlock, first) ← cPlace withHurricane defender .hand ⟨"WTR_203_R"⟩
  let (ready, second) ← cPlace oneBlock defender .hand ⟨"WTR_204_Y"⟩
  let enter := fun id => [⟨.player attacker, .playCard id⟩] ++ passBoth ++ passBoth
  let toDamage := [⟨.player defender, .defendDone⟩] ++ passBoth ++ passBoth
  let finish := toDamage ++ passBoth
  let prior ← cSteps ready (enter leg ++ finish ++ enter knee ++ finish)
  let defense ← cSteps prior (enter hurricane)
  let hit ← cSteps defense toDamage
  let struck ← (hit.combat.bind CombatChain.activeLink?).bind (·.attack)
  let trigger ← hit.pendingTriggers.head?
  let stacked ← cSteps hit [⟨.player attacker, .pickTriggerStart attacker⟩,
    ⟨.player attacker, .pickTrigger trigger.id⟩, ⟨.player attacker, .pass⟩]
  let (resolved, events) ← (step 64 stacked ⟨.player defender, .pass⟩).toOption
  let returned ← (resolved.zone hand).head?
  let firstResolution ← cSteps resolved passBoth
  let replayed ← cSteps firstResolution (enter returned ++ finish)
  let replayLink ← replayed.combat.bind CombatChain.activeLink?
  let closed ← cSteps replayed passBoth
  let blocked ← cSteps defense ([⟨.player defender, .defendCard first⟩,
    ⟨.player defender, .defendCard second⟩] ++ finish)
  pure (card.status == .full && prior.lifeOf defender == 31 &&
    hit.lifeOf defender == 26 && hit.pendingTriggers.length == 1 &&
    hit.locate struck == some .combatChain && hit.zone hand == [] &&
    resolved.zone hand == [returned] && (resolved.obj? returned).bind (·.kind.phys?) == some physical &&
    resolved.locate struck == none &&
    events.countP (· == .moved struck returned .combatChain hand) == 1 &&
    (firstResolution.poolOf attacker).actionPoints == 1 &&
    replayed.lifeOf defender == 22 && replayLink.powerBonus == 0 && replayLink.damageDealt == 4 &&
    replayed.pendingTriggers.isEmpty && replayed.zone hand == [] &&
    (replayed.poolOf attacker).resources == 0 && (replayed.poolOf attacker).actionPoints == 0 &&
    closed.combat.isNone && (closed.zone graveyard).length == 3 &&
    blocked.locate struck == some .combatChain && blocked.zone hand == [] &&
    blocked.lifeOf defender == 31 && blocked.pendingTriggers.isEmpty &&
    (blocked.poolOf attacker).actionPoints == 1)

#guard checkHurricaneTechnique == some true

/-- Open the Center gets power, Go Again, and Dominate only immediately after Head Jab. -/
meta def checkOpenTheCenter (cid : CardId) (basePower : Nat) : Bool :=
  checkComboAttack [⟨"WTR_098_R"⟩] cid (basePower + 1) 1 [.goAgain, .dominate] == some true &&
  checkComboAttack [] cid basePower 0 == some true &&
  checkComboAttack [⟨"WTR_098_R"⟩, ⟨"WTR_203_R"⟩] cid basePower 0 == some true

#guard checkOpenTheCenter ⟨"WTR_095_R"⟩ 5
#guard checkOpenTheCenter ⟨"WTR_096_Y"⟩ 4
#guard checkOpenTheCenter ⟨"WTR_097_B"⟩ 3

/-- Pounding Gale doubles damage left after defense, then applies damage prevention. -/
meta def checkPoundingGale : Option Bool := do
  let attacker : PlayerId := ⟨0⟩
  let defender : PlayerId := ⟨1⟩
  let cid : CardId := ⟨"WTR_085_R"⟩
  let funded := m5Base.setPool attacker { actionPoints := 1, resources := 3 }
  let card ← funded.cards.find? cid
  let (withJab, jab) ← cPlace funded attacker .hand ⟨"WTR_098_R"⟩
  let (withCenter, center) ← cPlace withJab attacker .hand ⟨"WTR_095_R"⟩
  let (withGale, gale) ← cPlace withCenter attacker .hand cid
  let (oneBlock, first) ← cPlace withGale defender .hand ⟨"WTR_203_R"⟩
  let (ready, second) ← cPlace oneBlock defender .hand ⟨"WTR_204_Y"⟩
  let enter := fun id => [⟨.player attacker, .playCard id⟩] ++ passBoth ++ passBoth
  let toDamage := [⟨.player defender, .defendDone⟩] ++ passBoth ++ passBoth
  let finish := toDamage ++ passBoth
  let prior ← cSteps ready (enter jab ++ finish ++ enter center ++ finish)
  let combo ← cSteps prior (enter gale)
  let (shielded, _, _) := execPrim combo defender ⟨0⟩ []
    (.preventNextDamage .controller (.const 1) .thisTurn)
  let blockFirst : Action := ⟨.player defender, .defendCard first⟩
  let openHit ← cSteps combo toDamage
  let reduced ← cSteps combo (blockFirst :: toDamage)
  let prevented ← cSteps shielded (blockFirst :: toDamage)
  let blocked ← cSteps combo
    (blockFirst :: ⟨.player defender, .defendCard second⟩ :: toDamage)
  let standalone ← cSteps ready (enter gale ++ (blockFirst :: toDamage))
  let check := fun (s : GameState) (life : Int) (defense damage : Nat) =>
    s.lifeOf defender == life &&
    match s.combat.bind CombatChain.activeLink? with
    | some link =>
      linkAttackPower s link == 5 && linkTotalDefense s link == defense &&
      link.damageDealt == damage && link.hit == (damage != 0)
    | none => false
  pure (card.status == .full && prior.lifeOf defender == 31 &&
    check openHit 21 0 10 && check reduced 27 3 4 && check prevented 28 3 3 &&
    check blocked 31 6 0 && check standalone 38 3 2)

#guard checkPoundingGale == some true

/-- Fluster Fist counts prior hits, even when the same links were attacked in every case. -/
meta def checkFlusterFist (cid : CardId) (basePower : Nat) : Option Bool := do
  let attacker : PlayerId := ⟨0⟩
  let defender : PlayerId := ⟨1⟩
  let funded := m5Base.setPool attacker { actionPoints := 1, resources := 2 }
  let card ← funded.cards.find? cid
  let (withJab, jab) ← cPlace funded attacker .hand ⟨"WTR_098_R"⟩
  let (withCenter, center) ← cPlace withJab attacker .hand ⟨"WTR_095_R"⟩
  let (withFist, fist) ← cPlace withCenter attacker .hand cid
  let (ready, blockId) ← cPlace withFist defender .hand ⟨"WTR_203_R"⟩
  let enter := fun id => [⟨.player attacker, .playCard id⟩] ++ passBoth ++ passBoth
  let finish := [⟨.player defender, .defendDone⟩] ++ passBoth ++ passBoth ++ passBoth
  let jabDefense ← cSteps ready (enter jab)
  let jabHit ← cSteps jabDefense finish
  let jabMiss ← cSteps jabDefense ([⟨.player defender, .defendCard blockId⟩] ++ finish)
  let twoHits ← cSteps jabHit (enter center ++ finish)
  let oneHit ← cSteps jabMiss (enter center ++ finish)
  let (shielded, _, _) := execPrim jabMiss defender ⟨0⟩ []
    (.preventNextDamage .controller (.const 6) .thisTurn)
  let noHits ← cSteps shielded (enter center ++ finish)
  let check := fun (s : GameState) (bonus : Nat) => do
    let resolved ← cSteps s (enter fist ++ finish)
    let link ← resolved.combat.bind CombatChain.activeLink?
    pure (link.powerBonus == Int.ofNat bonus && link.damageDealt == basePower + bonus &&
      s.lifeOf defender - resolved.lifeOf defender == Int.ofNat (basePower + bonus) &&
      (resolved.poolOf attacker).actionPoints == 0)
  let twoOk ← check twoHits 2
  let oneOk ← check oneHit 1
  let zeroOk ← check noHits 0
  let standaloneOk ← check ready 0
  pure (card.status == .full && twoHits.lifeOf defender == 31 &&
    oneHit.lifeOf defender == 34 && noHits.lifeOf defender == 40 &&
    twoOk && oneOk && zeroOk && standaloneOk)

#guard checkFlusterFist ⟨"WTR_086_R"⟩ 4 == some true
#guard checkFlusterFist ⟨"WTR_087_Y"⟩ 3 == some true
#guard checkFlusterFist ⟨"WTR_088_B"⟩ 2 == some true
