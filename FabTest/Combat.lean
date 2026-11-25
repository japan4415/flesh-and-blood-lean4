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

/-- Use Cracked Baubles in Limited loadouts and in their pitch-only combat role. -/
meta def checkCrackedBauble : Option Bool := do
  let attacker : PlayerId := ⟨0⟩
  let defender : PlayerId := ⟨1⟩
  let cid : CardId := ⟨"WTR_224_Y"⟩
  let hero : CardId := ⟨"WTR_039"⟩
  let deck := List.replicate 30 cid
  let pool : DeckList := { hero := hero, pool := deck }
  let loadout : Loadout := { hero := hero, deck := deck }
  let funded := m5Base.setPool attacker { actionPoints := 1, resources := 1 }
  let card ← funded.cards.find? cid
  let (withBauble, bauble) ← cPlace funded attacker .hand cid
  let (withAttack, attack) ← cPlace withBauble attacker .hand ⟨"WTR_188_R"⟩
  let (ready, defenderBauble) ← cPlace withAttack defender .hand cid
  let choosing ← cSteps ready [⟨.player attacker, .playCard attack⟩]
  let (paid, events) ← (step 64 choosing ⟨.player attacker, .pitchCard bauble⟩).toOption
  let pitched ← (paid.zone (.player attacker .pitch)).head?
  let defending ← cSteps paid (passBoth ++ passBoth)
  pure (card.status == .full && card.isDeckCard && card.front.subtypes == [.gem] &&
    decide (CoreDeckValid wtrDB pool) && decide (LoadoutValid wtrDB .sealed pool loadout) &&
    decide (LoadoutValid wtrDB .draft pool loadout) &&
    (step 64 ready ⟨.player attacker, .playCard bauble⟩).toOption.isNone &&
    (step 64 defending ⟨.player defender, .defendCard defenderBauble⟩).toOption.isNone &&
    events.countP (· == .pitched attacker pitched 2 0) == 1 &&
    (paid.cardDefOf? pitched).map (·.id) == some cid &&
    (paid.poolOf attacker).resources == 0 && (paid.poolOf attacker).actionPoints == 0)

#guard checkCrackedBauble == some true

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
--    Head Jab Red (3{p}) + Ancestral (+1{p} = 4{p}) vs 2{d} hand card + Sink Below (4{d}) -> 0 dmg.
#guard match (do
    let (s1, _) ← cPlace m5Base ⟨0⟩ .deck ⟨"WTR_188_R"⟩
    let (s2, jab) ← cPlace s1 ⟨0⟩ .hand ⟨"WTR_098_R"⟩
    let (s3, ancId) ← cPlace s2 ⟨0⟩ .hand ⟨"WTR_082_R"⟩
    let (s4, defHand) ← cPlace s3 ⟨1⟩ .hand ⟨"WTR_098_R"⟩  -- Head Jab Red (2{d})
    let (s5, sinkId) ← cPlace s4 ⟨1⟩ .hand ⟨"WTR_215_R"⟩   -- Sink Below Red (4{d})
    -- Enter Defend Step, defend with defHand (2{d}), advance to Reaction Step
    let sReact ← cSteps s5
      ([⟨.player ⟨0⟩, .playCard jab⟩] ++ passBoth ++ passBoth ++
       [⟨.player ⟨1⟩, .defendCard defHand⟩, ⟨.player ⟨1⟩, .defendDone⟩] ++ passBoth)
    let onReact := sReact.combat.map (·.step) == some .reaction
    -- P0 plays Ancestral Empowerment (+1{p} & draw 1), both pass -> resolves
    let sAfterAnc ← cSteps sReact ([⟨.player ⟨0⟩, .playCard ancId⟩] ++ passBoth)
    -- Sink Below resolves without a choice because P1 has no cards left in hand.
    let sAfterSink ← cSteps sAfterAnc
      [⟨.player ⟨0⟩, .pass⟩, ⟨.player ⟨1⟩, .playCard sinkId⟩,
       ⟨.player ⟨1⟩, .pass⟩, ⟨.player ⟨0⟩, .pass⟩]
    -- Both pass Reaction Step -> Damage Step (4{p} vs 6{d} = 0 dmg, hit = false)
    let sDmg ← cSteps sAfterSink passBoth
    pure (onReact &&
      (sAfterAnc.zone (.player ⟨0⟩ .hand)).length == 1 &&
      (sAfterAnc.combat.bind CombatChain.activeLink?).map (linkAttackPower sAfterAnc) == some 4 &&
      sDmg.lifeOf ⟨1⟩ == 40 &&
      (sDmg.combat.bind CombatChain.activeLink?).map (fun l => (l.hit, l.damageDealt)) == some (false, 0))) with
  | some b => b
  | none => false

/-- Ancestral Empowerment declares a Ninja attack action and draws even if it loses that target. -/
meta def checkAncestralEmpowerment (fromArsenal : Bool) : Option Bool := do
  let player : PlayerId := ⟨0⟩
  let opponent : PlayerId := ⟨1⟩
  let hand := Zone.player player .hand
  let deck := Zone.player player .deck
  let grave := Zone.player player .graveyard
  let cid : CardId := ⟨"WTR_082_R"⟩
  let origin : ZoneKind := if fromArsenal then .arsenal else .hand
  let funded := m5Base.setPool player { actionPoints := 1, resources := 1 }
  let card ← funded.cards.find? cid
  let (withTop, _) ← cPlace funded player .deck ⟨"WTR_188_R"⟩
  let (withNinja, ninja) ← cPlace withTop player .hand ⟨"WTR_098_R"⟩
  let (withGeneric, generic) ← cPlace withNinja player .hand ⟨"WTR_203_R"⟩
  let (withWeapon, weapon) ← cPlace withGeneric player .weapon ⟨"WTR_078"⟩
  let (ready, reaction) ← cPlace withWeapon player origin cid fromArsenal
  let play id : Action := ⟨.player player, .playCard id⟩
  let toReaction := passBoth ++ passBoth ++ [⟨.player opponent, .defendDone⟩] ++ passBoth
  let ninjaReaction ← cSteps ready (play ninja :: toReaction)
  let genericReaction ← cSteps ready (play generic :: toReaction)
  let weaponReaction ← cSteps ready (⟨.player player, .attackWeapon weapon⟩ :: toReaction)
  let active (s : GameState) := s.combat.bind CombatChain.activeLink?
  let link ← active ninjaReaction
  let target ← link.attack
  let (declared, events) ← (step 64 ninjaReaction (play reaction)).toOption
  let layer ← (declared.zone .stack).head?
  let resolved ← cSteps declared passBoth
  let (lost, lostId) ← moveObj declared target grave .top false
  let (newAttack, replacement) ← moveObj lost lostId .combatChain .top false
  let replacementChain := newAttack.combat.map fun chain =>
    chain.updateActiveLink fun ln => { ln with attack := some replacement }
  let replaced := { newAttack with combat := replacementChain }
  let lostResolved ← cSteps lost passBoth
  let replacedResolved ← cSteps replaced passBoth
  let hit ← cSteps resolved (passBoth ++ passBoth)
  let denied (s : GameState) :=
    !(legalActionsFor player s).contains (play reaction) && (step 64 s (play reaction)).toOption.isNone
  let draws (s : GameState) :=
    (s.zone deck).isEmpty && ((s.zone hand).head?.bind s.cardDefOf?).map (·.id) == some ⟨"WTR_188_R"⟩
  pure (card.status == .full && card.front.pitch == some 1 && card.front.defense == some 3 &&
    denied ready && denied genericReaction && denied weaponReaction &&
    (legalActionsFor player ninjaReaction).contains (play reaction) &&
    events.contains (.targetedAttack layer target) &&
    ((declared.layerMeta.get? layer.n).bind (·.attackTarget)) == some target &&
    (declared.poolOf player).resources == 1 && (declared.poolOf player).actionPoints == 0 &&
    declared.zone deck == ready.zone deck && draws resolved && draws lostResolved && draws replacedResolved &&
    (active resolved).map (linkAttackPower resolved) == some 4 &&
    (active lostResolved).map (·.powerBonus) == some 0 &&
    (active replacedResolved).map (linkAttackPower replacedResolved) == some 3 &&
    (active hit).map (·.damageDealt) == some 4)

#guard checkAncestralEmpowerment false == some true
#guard checkAncestralEmpowerment true == some true

/-- Razor Reflex offers the mode for the current target and grants Go Again only on a card hit. -/
meta def checkRazorReflex (cid : CardId) (pitch bonus : Nat) (fromArsenal : Bool) :
    Option Bool := do
  let attacker : PlayerId := ⟨0⟩
  let defender : PlayerId := ⟨1⟩
  let funded := m5Base.setPool attacker { actionPoints := 1, resources := 4 }
  let card ← funded.cards.find? cid
  let (withCheap, cheap) ← cPlace funded attacker .hand ⟨"WTR_203_R"⟩
  let (withBoundary, boundary) ← cPlace withCheap attacker .hand ⟨"WTR_085_R"⟩
  let (withExpensive, expensive) ← cPlace withBoundary attacker .hand ⟨"WTR_188_R"⟩
  let (withDagger, dagger) ← cPlace withExpensive attacker .weapon ⟨"WTR_078"⟩
  let (withSword, sword) ← cPlace withDagger attacker .weapon ⟨"WTR_115"⟩
  let (withClub, club) ← cPlace withSword attacker .weapon ⟨"WTR_003"⟩
  let origin : ZoneKind := if fromArsenal then .arsenal else .hand
  let (withRazor, razor) ← cPlace withClub attacker origin cid fromArsenal
  let (withFirst, block1) ← cPlace withRazor defender .hand ⟨"WTR_203_R"⟩
  let (withSecond, block2) ← cPlace withFirst defender .hand ⟨"WTR_204_Y"⟩
  let (ready, block3) ← cPlace withSecond defender .hand ⟨"WTR_205_B"⟩
  let play id : Action := ⟨.player attacker, .playCard id⟩
  let attackWith id : Action := ⟨.player attacker, .attackWeapon id⟩
  let defend id : Action := ⟨.player defender, .defendCard id⟩
  let pick idx : Action := ⟨.player attacker, .pickMode idx⟩
  let cancel : Action := ⟨.player attacker, .cancelPlay⟩
  let done : Action := ⟨.player defender, .defendDone⟩
  let start a := cSteps ready (a :: (passBoth ++ passBoth))
  let enter s := cSteps s (done :: passBoth)
  let active (s : GameState) := s.combat.bind CombatChain.activeLink?
  let choose (s : GameState) (idx : Nat) := do
    let choosing ← cSteps s [play razor]
    let cancelled ← cSteps choosing [cancel]
    let link ← active s
    let target ← link.attack
    let (paid, events) ← (step 64 choosing (pick idx)).toOption
    let layer ← (paid.zone .stack).head?
    let applied ← cSteps paid passBoth
    let legal := legalActionsFor attacker choosing
    let rejected := (step 64 choosing (pick (1 - idx))).toOption.isNone
    pure (applied, legal == [pick idx, cancel, ⟨.player attacker, .concede⟩] &&
      rejected && decide (cancelled = s) &&
      (choosing.poolOf attacker).resources == (s.poolOf attacker).resources &&
      (paid.poolOf attacker).resources + 1 == (s.poolOf attacker).resources &&
      (paid.poolOf attacker).actionPoints == 0 &&
      events.contains (.targetedAttack layer target) &&
      ((paid.layerMeta.get? layer.n).bind (·.attackTarget)) == some target)
  let cheapDefense ← start (play cheap)
  let cheapReaction ← enter cheapDefense
  let blockedReaction ← cSteps cheapDefense ([defend block1, defend block2, defend block3, done] ++ passBoth)
  let boundaryDefense ← start (play boundary)
  let boundaryReaction ← enter boundaryDefense
  let expensiveDefense ← start (play expensive)
  let expensiveReaction ← enter expensiveDefense
  let daggerDefense ← start (attackWith dagger)
  let daggerReaction ← enter daggerDefense
  let swordDefense ← start (attackWith sword)
  let swordReaction ← enter swordDefense
  let clubDefense ← start (attackWith club)
  let clubReaction ← enter clubDefense
  let (buffed, validCardMode) ← choose cheapReaction 1
  let (blocked, validBlockedMode) ← choose blockedReaction 1
  let (atBoundary, validBoundaryMode) ← choose boundaryReaction 1
  let (withDaggerBonus, validDaggerMode) ← choose daggerReaction 0
  let (withSwordBonus, validSwordMode) ← choose swordReaction 0
  let hit ← cSteps buffed passBoth
  let trigger ← hit.pendingTriggers.head?
  let attacking ← active hit
  let triggerResolved ← cSteps hit ([⟨.player attacker, .pickTriggerStart attacker⟩,
    ⟨.player attacker, .pickTrigger trigger.id⟩] ++ passBoth)
  let granted ← active triggerResolved
  let cardFinished ← cSteps triggerResolved passBoth
  let blockedFinished ← cSteps blocked (passBoth ++ passBoth)
  let daggerFinished ← cSteps withDaggerBonus (passBoth ++ passBoth)
  let swordFinished ← cSteps withSwordBonus (passBoth ++ passBoth)
  let denied (s : GameState) :=
    !(legalActionsFor attacker s).contains (play razor) && (step 64 s (play razor)).toOption.isNone
  let damage (s : GameState) := (active s).map (·.damageDealt)
  pure (card.status == .full && card.front.pitch == some pitch && card.front.defense == some 2 &&
    denied expensiveReaction && denied clubReaction &&
    validCardMode && validBlockedMode && validBoundaryMode && validDaggerMode && validSwordMode &&
    (active atBoundary).map (linkAttackPower atBoundary) == some (5 + bonus) &&
    damage hit == some (4 + bonus) && some trigger.source == attacking.attack &&
    !linkHasKeyword hit attacking .goAgain &&
    linkHasKeyword triggerResolved granted .goAgain &&
    (cardFinished.poolOf attacker).actionPoints == 1 &&
    damage blockedFinished == some 0 && blockedFinished.pendingTriggers.isEmpty &&
    damage daggerFinished == some (1 + bonus) && daggerFinished.pendingTriggers.isEmpty &&
    damage swordFinished == some (3 + bonus) && swordFinished.pendingTriggers.isEmpty &&
    [blockedFinished, daggerFinished, swordFinished].all (fun s => (s.poolOf attacker).actionPoints == 0))

#guard checkRazorReflex ⟨"WTR_209_R"⟩ 1 3 false == some true
#guard checkRazorReflex ⟨"WTR_209_R"⟩ 1 3 true == some true

#guard checkRazorReflex ⟨"WTR_210_Y"⟩ 2 2 false == some true
#guard checkRazorReflex ⟨"WTR_210_Y"⟩ 2 2 true == some true

#guard checkRazorReflex ⟨"WTR_211_B"⟩ 3 1 false == some true
#guard checkRazorReflex ⟨"WTR_211_B"⟩ 3 1 true == some true

/-- A weapon reaction checks hand defense on the current link, including later reactions. -/
meta def checkWeaponReprise (cid : CardId) (pitch cost baseBonus repriseBonus : Nat)
    (glint fromArsenal : Bool) : Option Bool := do
  let attacker : PlayerId := ⟨0⟩
  let defender : PlayerId := ⟨1⟩
  let deck := Zone.player attacker .deck
  let hand := Zone.player attacker .hand
  let origin : ZoneKind := if fromArsenal then .arsenal else .hand
  let funded := m5Base.setPool attacker { actionPoints := 1, resources := 1 + cost }
  let card ← funded.cards.find? cid
  let (withTop, top) ← cPlace funded attacker .deck ⟨"WTR_188_R"⟩
  let (withSword, sword) ← cPlace withTop attacker .weapon ⟨"WTR_115"⟩
  let (withReaction, reaction) ← cPlace withSword attacker origin cid fromArsenal
  let (withNinja, ninja) ← cPlace withReaction attacker .hand ⟨"WTR_098_R"⟩
  let (withArmor, armor) ← cPlace withNinja defender .chest ⟨"WTR_041"⟩
  let (withBlock, block) ← cPlace withArmor defender .hand ⟨"WTR_203_R"⟩
  let play p id : Action := ⟨.player p, .playCard id⟩
  let swing : Action := ⟨.player attacker, .attackWeapon sword⟩
  let defend id : Action := ⟨.player defender, .defendCard id⟩
  let done : Action := ⟨.player defender, .defendDone⟩
  let active (s : GameState) := s.combat.bind CombatChain.activeLink?
  let beginning := passBoth ++ passBoth
  let enter := done :: passBoth
  let cast := play attacker reaction
  let defense ← cSteps withBlock (swing :: beginning)
  let unblocked ← cSteps defense enter
  let equipment ← cSteps defense (defend armor :: enter)
  let handBlock ← cSteps defense (defend block :: enter)
  let cardAttack ← cSteps withBlock (play attacker ninja :: (beginning ++ enter))
  let resolve (s : GameState) := cSteps s (cast :: passBoth)
  let bare ← resolve unblocked
  let armored ← resolve equipment
  let blocked ← resolve handBlock
  let delayed (arsenal : Bool) := do
    let zone : ZoneKind := if arsenal then .arsenal else .hand
    let (ready, sink) ← cPlace withArmor defender zone ⟨"WTR_215_R"⟩ arsenal
    let reacting ← cSteps ready (swing :: (beginning ++ enter))
    let ourLayer ← cSteps reacting [cast]
    let response ← cSteps ourLayer [⟨.player attacker, .pass⟩, play defender sink,
      ⟨.player defender, .pass⟩, ⟨.player attacker, .pass⟩]
    cSteps response passBoth
  let lateHand ← delayed false
  let lateArsenal ← delayed true
  let yields (s : GameState) (reprise : Bool) := do
    let link ← active s
    let finished ← cSteps s (passBoth ++ passBoth)
    let damage ← active finished
    let expectDamage := (3 + (if reprise then repriseBonus else baseBonus)) - linkTotalDefense s link
    let drawn := glint && reprise
    pure (linkAttackPower s link == 3 + (if reprise then repriseBonus else baseBonus) &&
      (link.defendedFromHandCount > 0) == reprise && linkHasKeyword s link .goAgain == glint &&
      (s.poolOf attacker).resources == 0 && (s.poolOf attacker).actionPoints == 0 &&
      (if drawn then (s.zone deck).isEmpty &&
          ((s.zone hand).head?.bind s.cardDefOf?).map (·.id) == some ⟨"WTR_188_R"⟩
        else s.zone deck == [top] && s.zone hand == [ninja]) &&
      damage.damageDealt == expectDamage &&
      (finished.poolOf attacker).actionPoints == (if glint then 1 else 0))
  let bareOk ← yields bare false
  let armorOk ← yields armored false
  let handOk ← yields blocked true
  let lateHandOk ← yields lateHand true
  let lateArsenalOk ← yields lateArsenal false
  pure (card.status == .full && card.front.pitch == some pitch && card.front.defense == some 3 &&
    !(legalActionsFor attacker cardAttack).contains cast &&
    (step 64 cardAttack cast).toOption.isNone &&
    bareOk && armorOk && handOk && lateHandOk && lateArsenalOk)

#guard checkWeaponReprise ⟨"WTR_118_B"⟩ 3 0 0 0 true false == some true
#guard checkWeaponReprise ⟨"WTR_118_B"⟩ 3 0 0 0 true true == some true

#guard checkWeaponReprise ⟨"WTR_123_R"⟩ 1 3 4 6 false false == some true
#guard checkWeaponReprise ⟨"WTR_123_R"⟩ 1 3 4 6 false true == some true

#guard checkWeaponReprise ⟨"WTR_124_Y"⟩ 2 3 3 5 false false == some true
#guard checkWeaponReprise ⟨"WTR_124_Y"⟩ 2 3 3 5 false true == some true

#guard checkWeaponReprise ⟨"WTR_125_B"⟩ 3 3 2 4 false false == some true
#guard checkWeaponReprise ⟨"WTR_125_B"⟩ 3 3 2 4 false true == some true

#guard checkWeaponReprise ⟨"WTR_132_R"⟩ 1 0 0 3 false false == some true
#guard checkWeaponReprise ⟨"WTR_132_R"⟩ 1 0 0 3 false true == some true

#guard checkWeaponReprise ⟨"WTR_133_Y"⟩ 2 0 0 2 false false == some true
#guard checkWeaponReprise ⟨"WTR_133_Y"⟩ 2 0 0 2 false true == some true

#guard checkWeaponReprise ⟨"WTR_134_B"⟩ 3 0 0 1 false false == some true
#guard checkWeaponReprise ⟨"WTR_134_B"⟩ 3 0 0 1 false true == some true

/-- Biting Blade boosts the targeted attack and, on Reprise, both equipped weapons for the turn. -/
meta def checkBitingBlade (cid : CardId) (pitch bonus : Nat) (fromArsenal : Bool) : Option Bool := do
  let attacker : PlayerId := ⟨0⟩
  let defender : PlayerId := ⟨1⟩
  let origin : ZoneKind := if fromArsenal then .arsenal else .hand
  let funded := m5Base.setPool attacker { actionPoints := 3, resources := 4 }
  let card ← funded.cards.find? cid
  let (one, first) ← cPlace funded attacker .weapon ⟨"WTR_078"⟩
  let (two, second) ← cPlace one attacker .weapon ⟨"WTR_078"⟩
  let (withOther, other) ← cPlace two defender .weapon ⟨"WTR_078"⟩
  let (withReserve, reserve) ← cPlace withOther attacker .inventory ⟨"WTR_078"⟩
  let (withGeneric, generic) ← cPlace withReserve attacker .hand ⟨"WTR_203_R"⟩
  let (withSpare, _) ← cPlace withGeneric attacker .hand ⟨"WTR_205_B"⟩
  let (withBlade, blade) ← cPlace withSpare attacker origin cid fromArsenal
  let (ready, block) ← cPlace withBlade defender .hand ⟨"WTR_203_R"⟩
  let swing id : Action := ⟨.player attacker, .attackWeapon id⟩
  let play id : Action := ⟨.player attacker, .playCard id⟩
  let done : Action := ⟨.player defender, .defendDone⟩
  let toDefense := passBoth ++ passBoth
  let toReaction := done :: passBoth
  let finish := passBoth ++ passBoth
  let active (s : GameState) := s.combat.bind CombatChain.activeLink?
  let defense ← cSteps ready (swing first :: toDefense)
  let bareReaction ← cSteps defense toReaction
  let (bare, _) ← (step 64 bareReaction (play blade)).toOption
  let bareResolved ← cSteps bare passBoth
  let reprising ← cSteps defense (⟨.player defender, .defendCard block⟩ :: toReaction)
  let paid ← cSteps reprising [play blade]
  let resolved ← cSteps paid passBoth
  let firstHit ← cSteps resolved finish
  let closed ← cSteps firstHit passBoth
  let genericHit ← cSteps closed (play generic :: (toDefense ++ toReaction ++ finish))
  let beforeSecond ← cSteps genericHit passBoth
  let secondHit ← cSteps beforeSecond (swing second :: (toDefense ++ toReaction ++ finish))
  let doneCombat ← cSteps secondHit passBoth
  let ended ← cSteps doneCombat (passBoth ++ [⟨.player attacker, .arsenalSkip⟩])
  let gotPower (s : GameState) (n : Nat) := (active s).map (linkAttackPower s) == some n
  let damage (s : GameState) := (active s).map (·.damageDealt)
  pure (card.status == .full && card.front.pitch == some pitch && card.front.defense == some 3 &&
    (paid.poolOf attacker).resources == 1 && (paid.poolOf attacker).actionPoints == 2 &&
    gotPower bareResolved (1 + bonus) && bareResolved.activeEffects.isEmpty &&
    objEffectivePower bareResolved second == some 1 &&
    gotPower resolved (2 + bonus) && damage firstHit == some (2 + bonus - 3) &&
    objEffectivePower resolved first == some 2 && objEffectivePower resolved second == some 2 &&
    objEffectivePower resolved other == some 1 && objEffectivePower resolved reserve == some 1 &&
    objEffectivePower resolved generic == some 4 &&
    damage genericHit == some 4 && damage secondHit == some 2 &&
    objEffectivePower doneCombat first == some 2 && objEffectivePower doneCombat second == some 2 &&
    ended.activeEffects.isEmpty && objEffectivePower ended first == some 1 &&
    objEffectivePower ended second == some 1)

#guard checkBitingBlade ⟨"WTR_135_R"⟩ 1 3 false == some true
#guard checkBitingBlade ⟨"WTR_135_R"⟩ 1 3 true == some true

#guard checkBitingBlade ⟨"WTR_136_Y"⟩ 2 2 false == some true
#guard checkBitingBlade ⟨"WTR_136_Y"⟩ 2 2 true == some true

#guard checkBitingBlade ⟨"WTR_137_B"⟩ 3 1 false == some true
#guard checkBitingBlade ⟨"WTR_137_B"⟩ 3 1 true == some true

/-- Pilgrimage gives its next weapon a conditional hit trigger and reveals only the deck top. -/
meta def checkNaturesPathPilgrimage (cid : CardId) (pitch bonus : Nat) (fromArsenal : Bool) :
    Option Bool := do
  let attacker : PlayerId := ⟨0⟩
  let defender : PlayerId := ⟨1⟩
  let deck := Zone.player attacker .deck
  let arsenal := Zone.player attacker .arsenal
  let origin : ZoneKind := if fromArsenal then .arsenal else .hand
  let funded := m5Base.setPool attacker { actionPoints := 2, resources := 2 }
  let card ← funded.cards.find? cid
  let (withWeapon, weapon) ← cPlace funded attacker .weapon ⟨"WTR_078"⟩
  let (withGeneric, generic) ← cPlace withWeapon attacker .hand ⟨"WTR_203_R"⟩
  let (withAction, pilgrim) ← cPlace withGeneric attacker origin cid fromArsenal
  let (ready, block) ← cPlace withAction defender .hand ⟨"WTR_188_R"⟩
  let (allReady, blockTwo) ← cPlace ready defender .hand ⟨"WTR_188_R"⟩
  let play id : Action := ⟨.player attacker, .playCard id⟩
  let swing : Action := ⟨.player attacker, .attackWeapon weapon⟩
  let defend id : Action := ⟨.player defender, .defendCard id⟩
  let active (s : GameState) := s.combat.bind CombatChain.activeLink?
  let done : Action := ⟨.player defender, .defendDone⟩
  let toDefense := passBoth ++ passBoth
  let fight := done :: (passBoth ++ passBoth)
  let paid ← cSteps allReady [play pilgrim]
  let buffed ← cSteps paid passBoth
  let genericHit ← cSteps buffed (play generic :: (toDefense ++ fight))
  let beforeWeapon ← cSteps genericHit (passBoth ++ passBoth)
  let actionId : CardId := ⟨"WTR_188_R"⟩
  let instantId : CardId := ⟨"WTR_173_R"⟩
  let (withTopAction, topAction) ← cPlace beforeWeapon attacker .deck actionId
  let (withTopInstant, topInstant) ← cPlace beforeWeapon attacker .deck instantId
  let (alreadyFilled, occupant) ← cPlace withTopAction attacker .arsenal instantId true
  let weaponHit (s : GameState) := cSteps s (swing :: (toDefense ++ fight))
  let hit ← weaponHit withTopAction
  let nonActionHit ← weaponHit withTopInstant
  let noDeckHit ← weaponHit beforeWeapon
  let occupiedHit ← weaponHit alreadyFilled
  let defending ← cSteps withTopAction (swing :: toDefense)
  let blocked ← cSteps defending (defend block :: defend blockTwo :: fight)
  let resolveHit (s : GameState) := do
    let trigger ← s.pendingTriggers.head?
    let stacked ← cSteps s [⟨.player attacker, .pickTriggerStart attacker⟩,
      ⟨.player attacker, .pickTrigger trigger.id⟩, ⟨.player attacker, .pass⟩]
    (step 64 stacked ⟨.player defender, .pass⟩).toOption
  let (resolved, reveals) ← resolveHit hit
  let arsenaled ← (resolved.zone arsenal).head?
  let (stayed, nonActionEvents) ← resolveHit nonActionHit
  let (empty, emptyEvents) ← resolveHit noDeckHit
  let (filledAfterHit, late) ← cPlace hit attacker .arsenal instantId true
  let (lateResolved, lateEvents) ← resolveHit filledAfterHit
  pure (card.status == .full && card.front.pitch == some pitch && card.front.defense == some 3 &&
    (paid.poolOf attacker).actionPoints == 1 && (paid.poolOf attacker).resources == 1 &&
    (buffed.poolOf attacker).actionPoints == 2 && buffed.activeEffects.length == 2 &&
    (active genericHit).map (·.damageDealt) == some 4 &&
    genericHit.pendingTriggers.isEmpty && beforeWeapon.activeEffects == buffed.activeEffects &&
    (active hit).map (·.damageDealt) == some (1 + bonus) && hit.activeEffects.isEmpty &&
    hit.pendingTriggers.length == 1 && hit.zone deck == [topAction] &&
    reveals == [.revealed attacker topAction actionId, .moved topAction arsenaled deck arsenal] &&
    (resolved.obj? arsenaled).any (·.faceDown) && resolved.zone deck == [] &&
    stayed.zone deck == [topInstant] && stayed.zone arsenal == [] &&
    nonActionEvents == [.revealed attacker topInstant instantId] &&
    empty.zone arsenal == [] && emptyEvents.isEmpty &&
    occupiedHit.pendingTriggers.isEmpty && occupiedHit.zone arsenal == [occupant] &&
    blocked.pendingTriggers.isEmpty && (active blocked).map (·.damageDealt) == some 0 &&
    lateResolved.zone arsenal == [late] && lateResolved.zone deck == [topAction] &&
    lateEvents == [.revealed attacker topAction actionId])

#guard checkNaturesPathPilgrimage ⟨"WTR_147_R"⟩ 1 3 false == some true
#guard checkNaturesPathPilgrimage ⟨"WTR_147_R"⟩ 1 3 true == some true

#guard checkNaturesPathPilgrimage ⟨"WTR_148_Y"⟩ 2 2 false == some true
#guard checkNaturesPathPilgrimage ⟨"WTR_148_Y"⟩ 2 2 true == some true

#guard checkNaturesPathPilgrimage ⟨"WTR_149_B"⟩ 3 1 false == some true
#guard checkNaturesPathPilgrimage ⟨"WTR_149_B"⟩ 3 1 true == some true

/-- Stroke draws under Reprise, then accepts a card for either end of the deck. -/
meta def checkStrokeOfForesight (cid : CardId) (pitch bonus : Nat) (fromArsenal : Bool) :
    Option Bool := do
  let attacker : PlayerId := ⟨0⟩
  let defender : PlayerId := ⟨1⟩
  let hand := Zone.player attacker .hand
  let deck := Zone.player attacker .deck
  let origin : ZoneKind := if fromArsenal then .arsenal else .hand
  let initial := m5Base.setPool attacker { actionPoints := 1, resources := 2 }
  let card ← initial.cards.find? cid
  let (withWeapon, weapon) ← cPlace initial attacker .weapon ⟨"WTR_078"⟩
  let (withReaction, reaction) ← cPlace withWeapon attacker origin cid fromArsenal
  let (withBlock, block) ← cPlace withReaction defender .hand ⟨"WTR_203_R"⟩
  let (withReserve, reserve) ← cPlace withBlock attacker .hand ⟨"WTR_205_B"⟩
  let (withBottom, bottom) ← cPlace withReserve attacker .deck ⟨"WTR_190_B"⟩
  let (withMiddle, middle) ← cPlace withBottom attacker .deck ⟨"WTR_189_Y"⟩
  let (ready, top) ← cPlace withMiddle attacker .deck ⟨"WTR_188_R"⟩
  let swing : Action := ⟨.player attacker, .attackWeapon weapon⟩
  let cast : Action := ⟨.player attacker, .playCard reaction⟩
  let defend : Action := ⟨.player defender, .defendCard block⟩
  let done : Action := ⟨.player defender, .defendDone⟩
  let pick index : Action := ⟨.player attacker, .pickMode index⟩
  let pickCard id : Action := ⟨.player attacker, .handToDeckPick id⟩
  let active (s : GameState) := s.combat.bind CombatChain.activeLink?
  let defendStep (s : GameState) := cSteps s (swing :: (passBoth ++ passBoth))
  let enter := done :: passBoth
  let defending ← defendStep ready
  let noReprise ← cSteps defending (enter ++ (cast :: passBoth))
  let reprising ← cSteps defending (defend :: enter)
  let paid ← cSteps reprising [cast]
  let passed ← cSteps paid [⟨.player attacker, .pass⟩]
  let (prompt, decisions) ← (step 64 passed ⟨.player defender, .pass⟩).toOption
  let drawn ← (prompt.zone hand).head?
  let topChoice ← cSteps prompt [pick 0]
  let bottomChoice ← cSteps prompt [pick 1]
  let (putTop, topEvents) ← (step 64 topChoice (pickCard reserve)).toOption
  let (putBottom, bottomEvents) ← (step 64 bottomChoice (pickCard drawn)).toOption
  let newTop ← (putTop.zone deck).head?
  let newBottom ← (putBottom.zone deck).getLast?
  let emptyDefending ← defendStep withBlock
  let emptyResult ← cSteps emptyDefending (defend :: (enter ++ (cast :: passBoth)))
  let reserveDefense ← defendStep withReserve
  let emptyDeckPrompt ← cSteps reserveDefense (defend :: (enter ++ (cast :: passBoth)))
  let putOnly ← cSteps emptyDeckPrompt [pick 1, pickCard reserve]
  let link ← active putTop
  let otherLink ← active noReprise
  pure (card.status == .full && card.front.pitch == some pitch && card.front.defense == some 3 &&
    (paid.poolOf attacker).resources == 0 && (paid.poolOf attacker).actionPoints == 0 &&
    paid.zone deck == [top, middle, bottom] && paid.zone hand == [reserve] &&
    noReprise.zone deck == paid.zone deck && noReprise.zone hand == [reserve] &&
    linkAttackPower noReprise otherLink == 1 + bonus && linkAttackPower putTop link == 1 + bonus &&
    decisions == [.moved top drawn deck hand, .drawn attacker drawn] &&
    (prompt.cardDefOf? drawn).map (·.id) == some ⟨"WTR_188_R"⟩ && prompt.zone hand == [drawn, reserve] &&
    (legalActionsFor attacker prompt).contains (pick 0) && (legalActionsFor attacker prompt).contains (pick 1) &&
    topChoice.pending.head? == some (.chooseHandToDeck attacker .top) &&
    bottomChoice.pending.head? == some (.chooseHandToDeck attacker .bottom) &&
    (step 64 topChoice (pickCard block)).toOption.isNone &&
    topEvents.head? == some (.moved reserve newTop hand deck) &&
    bottomEvents.head? == some (.moved drawn newBottom hand deck) &&
    putTop.zone deck == [newTop, middle, bottom] && putTop.zone hand == [drawn] &&
    putBottom.zone deck == [middle, bottom, newBottom] && putBottom.zone hand == [reserve] &&
    emptyResult.zone hand == [] && emptyResult.zone deck == [] && emptyResult.zone .stack == [] &&
    putOnly.zone hand == [] && (putOnly.zone deck).length == 1)

#guard checkStrokeOfForesight ⟨"WTR_138_R"⟩ 1 3 false == some true
#guard checkStrokeOfForesight ⟨"WTR_138_R"⟩ 1 3 true == some true

#guard checkStrokeOfForesight ⟨"WTR_139_Y"⟩ 2 2 false == some true
#guard checkStrokeOfForesight ⟨"WTR_139_Y"⟩ 2 2 true == some true

#guard checkStrokeOfForesight ⟨"WTR_140_B"⟩ 3 1 false == some true
#guard checkStrokeOfForesight ⟨"WTR_140_B"⟩ 3 1 true == some true

/-- Staunch Response pays its extra cost before resolving, including payments made by pitching. -/
meta def checkStaunchResponse (cid : CardId) (pitch printedDefense : Nat) (fromArsenal : Bool) :
    Option Bool := do
  let attacker : PlayerId := ⟨0⟩
  let defender : PlayerId := ⟨1⟩
  let defenderPitch := Zone.player defender .pitch
  let origin : ZoneKind := if fromArsenal then .arsenal else .hand
  let base := m5Base.setPool attacker { actionPoints := 1, resources := 3 }
  let card ← base.cards.find? cid
  let (withAttack, attack) ← cPlace base attacker .hand ⟨"WTR_188_R"⟩
  let (bare, response) ← cPlace withAttack defender origin cid fromArsenal
  let (firstReserve, first) ← cPlace bare defender .hand ⟨"WTR_205_B"⟩
  let (withPitch, second) ← cPlace firstReserve defender .hand ⟨"WTR_190_B"⟩
  let play p id : Action := ⟨.player p, .playCard id⟩
  let pick value : Action := ⟨.player defender, .pickMay value⟩
  let pitchCard id : Action := ⟨.player defender, .pitchCard id⟩
  let cancel : Action := ⟨.player defender, .cancelPlay⟩
  let resolve := [⟨.player defender, .pass⟩, ⟨.player attacker, .pass⟩]
  let preparer (s : GameState) :=
    cSteps s (play attacker attack :: (passBoth ++ passBoth ++
      [⟨.player defender, .defendDone⟩] ++ passBoth ++ [⟨.player attacker, .pass⟩]))
  let reactionWindow ← preparer (bare.setPool defender { resources := 6 })
  let choosing ← cSteps reactionWindow [play defender response]
  let layer ← (choosing.zone .stack).head?
  let declined ← cSteps choosing [pick false]
  let accepted ← cSteps choosing [pick true]
  let cancelled ← cSteps choosing [cancel]
  let unpayable ← preparer (bare.setPool defender { resources := 2 })
  let unpayableChoice ← cSteps unpayable [play defender response]
  let rolledBack ← cSteps unpayableChoice [pick true]
  let pitchWindow ← preparer withPitch
  let pitchChoice ← cSteps pitchWindow [play defender response, pick true]
  let partPaid ← cSteps pitchChoice [pitchCard first]
  let partialLayer ← (partPaid.zone .stack).head?
  let cancelledPitch ← cSteps partPaid [cancel]
  let fullyPitched ← cSteps partPaid [pitchCard second]
  let link (s : GameState) := s.combat.bind CombatChain.activeLink?
  let resultingDefense (s : GameState) (defn : Nat) := do
    let defended ← cSteps s resolve
    let active ← link defended
    let cardId ← active.defending.head?
    let damaged ← cSteps defended passBoth
    pure (active.defending.length == 1 &&
      (defended.cardDefOf? cardId).map (·.id) == some cid &&
      objEffectiveDefense defended cardId == some (Int.ofNat defn) &&
      linkTotalDefense defended active == defn &&
      (link damaged).map (·.damageDealt) == some (7 - defn) &&
      (damaged.poolOf defender).actionPoints == 0)
  let declinedOk ← resultingDefense declined printedDefense
  let bonusOk ← resultingDefense accepted (printedDefense + 3)
  let pitchedOk ← resultingDefense fullyPitched (printedDefense + 3)
  pure (card.status == .full && card.front.pitch == some pitch &&
    card.front.defense == some printedDefense &&
    (choosing.poolOf defender).resources == 6 && choosing.playRollback.isSome &&
    (legalActionsFor defender choosing).contains (pick false) &&
    (legalActionsFor defender choosing).contains (pick true) &&
    (step 64 choosing ⟨.player attacker, .pickMay true⟩).toOption.isNone &&
    (declined.poolOf defender).resources == 4 && (accepted.poolOf defender).resources == 0 &&
    ((declined.layerMeta.get? layer.n).map (·.additionalCostPaid)) == some false &&
    ((accepted.layerMeta.get? layer.n).map (·.additionalCostPaid)) == some true &&
    decide (cancelled = reactionWindow) && decide (rolledBack = unpayable) &&
    (partPaid.poolOf defender).resources == 3 && (partPaid.zone defenderPitch).length == 1 &&
    !evalCondition partPaid defender partialLayer fromArsenal .additionalCostPaid &&
    decide (cancelledPitch = pitchWindow) && (fullyPitched.zone defenderPitch).length == 2 &&
    (fullyPitched.poolOf defender).resources == 0 && declinedOk && bonusOk && pitchedOk)

#guard checkStaunchResponse ⟨"WTR_051_R"⟩ 1 7 false == some true
#guard checkStaunchResponse ⟨"WTR_051_R"⟩ 1 7 true == some true

#guard checkStaunchResponse ⟨"WTR_052_Y"⟩ 2 6 false == some true
#guard checkStaunchResponse ⟨"WTR_052_Y"⟩ 2 6 true == some true

#guard checkStaunchResponse ⟨"WTR_053_B"⟩ 3 5 false == some true
#guard checkStaunchResponse ⟨"WTR_053_B"⟩ 3 5 true == some true

/-- Demolition Crew reveals a qualifying card without moving it and attacks with Dominate. -/
meta def checkDemolitionCrew (cid : CardId) (pitch power : Nat) (fromArsenal : Bool) :
    Option Bool := do
  let attacker : PlayerId := ⟨0⟩
  let defender : PlayerId := ⟨1⟩
  let hand := Zone.player attacker .hand
  let origin : ZoneKind := if fromArsenal then .arsenal else .hand
  let funded := m5Base.setPool attacker { actionPoints := 1, resources := 2 }
  let card ← funded.cards.find? cid
  let (bare, attack) ← cPlace funded attacker origin cid fromArsenal
  let (below, low) ← cPlace bare attacker .hand ⟨"WTR_101_R"⟩
  let boundaryId : CardId := ⟨"WTR_107_R"⟩
  let highId : CardId := ⟨"WTR_190_B"⟩
  let (withChoice, boundary) ← cPlace below attacker .hand boundaryId
  let (withPitch, high) ← cPlace withChoice attacker .hand highId
  let (withBlock, block) ← cPlace withPitch defender .hand ⟨"WTR_203_R"⟩
  let (withSecond, second) ← cPlace withBlock defender .hand ⟨"WTR_188_R"⟩
  let (ready, armor) ← cPlace withSecond defender .chest ⟨"WTR_041"⟩
  let play : Action := ⟨.player attacker, .playCard attack⟩
  let pick id : Action := ⟨.player attacker, .pickHandCostCard id⟩
  let defend id : Action := ⟨.player defender, .defendCard id⟩
  let cancel : Action := ⟨.player attacker, .cancelPlay⟩
  let failed ← cSteps below [play]
  let choosing ← cSteps ready [play]
  let cancelled ← cSteps choosing [cancel]
  let (paid, events) ← (step 64 choosing (pick boundary)).toOption
  let (paidHigh, highEvents) ← (step 64 choosing (pick high)).toOption
  let needsPitch ← cSteps (ready.setPool attacker { actionPoints := 1 }) [play]
  let gathered ← cSteps needsPitch [⟨.player attacker, .pitchCard high⟩]
  let paidByPitch ← cSteps gathered [pick boundary]
  let defense ← cSteps paid (passBoth ++ passBoth)
  let active ← defense.combat.bind CombatChain.activeLink?
  let blocked ← cSteps defense [defend block]
  let defended ← cSteps blocked [defend armor]
  let finished ← cSteps defended ([⟨.player defender, .defendDone⟩] ++ passBoth ++ passBoth)
  let hit ← finished.combat.bind CombatChain.activeLink?
  pure (card.status == .full && card.front.pitch == some pitch && card.front.defense == some 2 &&
    decide (failed = below) && decide (cancelled = ready) &&
    (legalActionsFor attacker choosing).contains (pick boundary) &&
    (legalActionsFor attacker choosing).contains (pick high) &&
    !(legalActionsFor attacker choosing).contains (pick low) &&
    (step 64 choosing (pick low)).toOption.isNone &&
    (step 64 choosing (pick attack)).toOption.isNone &&
    (step 64 choosing ⟨.player defender, .pickHandCostCard boundary⟩).toOption.isNone &&
    (step 64 gathered (pick high)).toOption.isNone &&
    (paidByPitch.poolOf attacker).resources == 1 &&
    (paid.poolOf attacker).resources == 0 && (paid.poolOf attacker).actionPoints == 0 &&
    events == [.revealed attacker boundary boundaryId] &&
    highEvents == [.revealed attacker high highId] &&
    paid.zone hand == [high, boundary, low] && paidHigh.zone hand == paid.zone hand &&
    linkHasKeyword defense active .dominate && linkAttackPower defense active == power &&
    (step 64 blocked (defend second)).toOption.isNone &&
    hit.defending.length == 2 && hit.damageDealt == power - 5)

#guard checkDemolitionCrew ⟨"WTR_179_R"⟩ 1 6 false == some true
#guard checkDemolitionCrew ⟨"WTR_179_R"⟩ 1 6 true == some true

#guard checkDemolitionCrew ⟨"WTR_180_Y"⟩ 2 5 false == some true
#guard checkDemolitionCrew ⟨"WTR_180_Y"⟩ 2 5 true == some true

#guard checkDemolitionCrew ⟨"WTR_181_B"⟩ 3 4 false == some true
#guard checkDemolitionCrew ⟨"WTR_181_B"⟩ 3 4 true == some true

/-- Choose Enlightened Strike's mode before paying its cost, then resolve the chosen effect. -/
meta def checkEnlightenedStrike (fromArsenal : Bool) : Option Bool := do
  let attacker : PlayerId := ⟨0⟩
  let defender : PlayerId := ⟨1⟩
  let hand := Zone.player attacker .hand
  let deck := Zone.player attacker .deck
  let origin : ZoneKind := if fromArsenal then .arsenal else .hand
  let cid : CardId := ⟨"WTR_159_R"⟩
  let card ← m5Base.cards.find? cid
  let (bare, attack) ← cPlace m5Base attacker origin cid fromArsenal
  let (keptHand, kept) ← cPlace bare attacker .hand ⟨"WTR_203_R"⟩
  let (withCost, choice) ← cPlace keptHand attacker .hand ⟨"WTR_205_B"⟩
  let (withBottom, bottom) ← cPlace withCost attacker .deck ⟨"WTR_188_R"⟩
  let (ready, top) ← cPlace withBottom attacker .deck ⟨"WTR_189_Y"⟩
  let play : Action := ⟨.player attacker, .playCard attack⟩
  let pick mode : Action := ⟨.player attacker, .pickMode mode⟩
  let pay id : Action := ⟨.player attacker, .pickHandCostCard id⟩
  let cancel : Action := ⟨.player attacker, .cancelPlay⟩
  let active (s : GameState) := s.combat.bind CombatChain.activeLink?
  let done : Action := ⟨.player defender, .defendDone⟩
  let noCost ← cSteps bare [play, pick 2]
  let modePrompt ← cSteps ready [play]
  let cancelledMode ← cSteps modePrompt [cancel]
  let choose (mode : Nat) : Option (GameState × ObjId × Bool) := do
    let costPrompt ← cSteps modePrompt [pick mode]
    let cancelledCost ← cSteps costPrompt [cancel]
    let (paid, es) ← (step 64 costPrompt (pay choice)).toOption
    let moved ← (paid.zone deck).getLast?
    let layer ← (paid.zone .stack).head?
    let valid :=
      (legalActionsFor attacker costPrompt).contains (pay kept) &&
      (legalActionsFor attacker costPrompt).contains (pay choice) &&
      (step 64 costPrompt (pay top)).toOption.isNone &&
      decide (cancelledCost = ready) && costPrompt.zone deck == [top, bottom] &&
      paid.zone deck == [top, bottom, moved] && paid.zone hand == [kept] &&
      es == [.moved choice moved hand deck] &&
      ((paid.layerMeta.get? layer.n).bind (·.modeIdx)) == some mode &&
      (paid.poolOf attacker).actionPoints == 0
    pure (paid, moved, valid)
  let (drawPaid, drawBottom, drawCost) ← choose 0
  let (powerPaid, powerBottom, powerCost) ← choose 1
  let (againPaid, againBottom, againCost) ← choose 2
  let attacking ← cSteps drawPaid passBoth
  let trigger ← attacking.pendingTriggers.head?
  let drawLink ← active attacking
  let stacked ← cSteps attacking [⟨.player attacker, .pickTriggerStart attacker⟩,
    ⟨.player attacker, .pickTrigger trigger.id⟩]
  let drawn ← cSteps stacked passBoth
  let drawnCard ← (drawn.zone hand).head?
  let toDamage := done :: (passBoth ++ passBoth ++ passBoth)
  let afterDraw ← cSteps drawn (passBoth ++ toDamage)
  let afterPower ← cSteps powerPaid (passBoth ++ passBoth ++ toDamage)
  let afterAgain ← cSteps againPaid (passBoth ++ passBoth ++ toDamage)
  pure (card.status == .full && card.front.pitch == some 1 && card.front.defense == some 3 &&
    decide (noCost = bare) && decide (cancelledMode = ready) &&
    [0, 1, 2].all (fun m => (legalActionsFor attacker modePrompt).contains (pick m)) &&
    (step 64 modePrompt (pick 3)).toOption.isNone &&
    drawCost && powerCost && againCost &&
    some trigger.source == drawLink.attack &&
    (attacking.zone deck) == [top, bottom, drawBottom] && (stacked.zone deck) == attacking.zone deck &&
    attacking.combat.map (·.step) == some .attack &&
    (drawn.cardDefOf? drawnCard).map (·.id) == some ⟨"WTR_189_Y"⟩ &&
    drawn.zone deck == [bottom, drawBottom] && drawn.zone hand == [drawnCard, kept] &&
    (active afterDraw).map (·.damageDealt) == some 5 &&
    (active afterPower).map (·.damageDealt) == some 7 &&
    (active afterAgain).map (·.damageDealt) == some 5 &&
    afterPower.zone deck == [top, bottom, powerBottom] &&
    afterAgain.zone deck == [top, bottom, againBottom] &&
    afterPower.pendingTriggers.isEmpty && afterAgain.pendingTriggers.isEmpty &&
    (afterDraw.poolOf attacker).actionPoints == 0 &&
    (afterPower.poolOf attacker).actionPoints == 0 &&
    (afterAgain.poolOf attacker).actionPoints == 1)

#guard checkEnlightenedStrike false == some true
#guard checkEnlightenedStrike true == some true

/-- Quicken waits for a paid attack, then grants Go Again through its own triggered layer. -/
meta def checkQuicken (weaponAttack : Bool) (count : Nat) : Option Bool := do
  let player : PlayerId := ⟨0⟩
  let opponent : PlayerId := ⟨1⟩
  let tokens := Zone.player player .permanent
  let cid : CardId := ⟨"WTR_225"⟩
  let base := m5Base.setPool player { actionPoints := 1, resources := 1 }
  let card ← base.cards.find? cid
  let (withWeapon, weapon) ← cPlace base player .weapon ⟨"WTR_078"⟩
  let (withAttack, attack) ← cPlace withWeapon player .hand ⟨"WTR_205_B"⟩
  let (withAction, action) ← cPlace withAttack player .hand ⟨"WTR_218_R"⟩
  let (withDefense, block) ← cPlace withAction opponent .hand ⟨"WTR_188_R"⟩
  let ready := createTokens withDefense player cid count
  let tokenIds := ready.zone tokens
  let play id : Action := ⟨.player player, .playCard id⟩
  let swing : Action := ⟨.player player, .attackWeapon weapon⟩
  let nonAttack ← cSteps ready [play action]
  let noResources := ready.setPool player { actionPoints := 1 }
  let trying ← cSteps noResources [swing]
  let cancelled ← cSteps trying [⟨.player player, .cancelPlay⟩]
  let queued ← cSteps ready [if weaponAttack then swing else play attack]
  let stackAttack ← (queued.zone .stack).head?
  let order := queued.pendingTriggers.map fun trigger =>
    (⟨.player player, .pickTrigger trigger.id⟩ : Action)
  let stacked ← cSteps queued (⟨.player player, .pickTriggerStart player⟩ :: order)
  let triggered ← cSteps stacked ((List.replicate count passBoth).flatten)
  let staleRemoved ← if weaponAttack then do
    let (withoutWeapon, _) ← moveObj triggered weapon (.player player .graveyard) .top false
    pure ((gspRun withoutWeapon).zone .stack).isEmpty
  else some true
  let defended ← cSteps triggered (passBoth ++ passBoth ++
    [⟨.player opponent, .defendCard block⟩])
  let active (s : GameState) := s.combat.bind CombatChain.activeLink?
  let link ← active defended
  let after ← cSteps defended ([⟨.player opponent, .defendDone⟩] ++ passBoth ++ passBoth ++ passBoth)
  let closed ← cSteps after (passBoth ++
    (if weaponAttack then [play attack] else [swing]))
  let nextLayer ← (closed.zone .stack).head?
  pure (card.status == .full && card.front.hasType .token && card.front.hasSubtype .aura &&
    nonAttack.pendingTriggers.isEmpty && nonAttack.zone tokens == tokenIds &&
    trying.pendingTriggers.isEmpty && trying.zone tokens == tokenIds &&
    decide (cancelled = noResources) &&
    queued.zone tokens == tokenIds && queued.pendingTriggers.length == count &&
    queued.pendingTriggers.all (fun trigger => tokenIds.contains trigger.source) &&
    (queued.pendingTriggers.map (·.id)).eraseDups.length == count &&
    ((queued.layerMeta.get? stackAttack.n).map (·.attackKeywords)) == some [] &&
    (stacked.zone .stack).length == count + 1 && stacked.zone tokens == tokenIds &&
    triggered.zone tokens == [] && triggered.zone .stack == [stackAttack] &&
    staleRemoved &&
    ((triggered.layerMeta.get? stackAttack.n).map (·.attackKeywords)) == some [.goAgain] &&
    linkHasKeyword defended link .goAgain &&
    (active after).map (·.damageDealt) == some 0 &&
    (after.poolOf player).actionPoints == 1 &&
    closed.pendingTriggers.isEmpty &&
    ((closed.layerMeta.get? nextLayer.n).map (·.attackKeywords)) == some [])

#guard checkQuicken false 1 == some true
#guard checkQuicken true 2 == some true

/-- Flock creates Quicken during Attack Step, for an attack played after Flock. -/
meta def checkFlockOfTheFeatherWalkers (cid : CardId) (pitch power : Nat) (fromArsenal : Bool) :
    Option Bool := do
  let attacker : PlayerId := ⟨0⟩
  let defender : PlayerId := ⟨1⟩
  let hand := Zone.player attacker .hand
  let arena := Zone.player attacker .permanent
  let origin : ZoneKind := if fromArsenal then .arsenal else .hand
  let base := m5Base.setPool attacker { actionPoints := 2, resources := 1 }
  let card ← base.cards.find? cid
  let (withCard, flock) ← cPlace base attacker origin cid fromArsenal
  let (unqualified, expensive) ← cPlace withCard attacker .hand ⟨"WTR_107_R"⟩
  let boundaryId : CardId := ⟨"WTR_101_R"⟩
  let (withBoundary, boundary) ← cPlace unqualified attacker .hand boundaryId
  let (withFallback, nextAttack) ← cPlace withBoundary attacker .hand ⟨"WTR_203_R"⟩
  let (withFirst, first) ← cPlace withFallback defender .hand ⟨"WTR_188_R"⟩
  let (ready, second) ← cPlace withFirst defender .hand ⟨"WTR_189_Y"⟩
  let play id : Action := ⟨.player attacker, .playCard id⟩
  let pick id : Action := ⟨.player attacker, .pickHandCostCard id⟩
  let done : Action := ⟨.player defender, .defendDone⟩
  let defend id : Action := ⟨.player defender, .defendCard id⟩
  let active (s : GameState) := s.combat.bind CombatChain.activeLink?
  let resolveTrigger (s : GameState) (trigger : PendingTrigger) :=
    cSteps s ([⟨.player attacker, .pickTriggerStart attacker⟩, ⟨.player attacker, .pickTrigger trigger.id⟩] ++
      passBoth)
  let rejected ← cSteps unqualified [play flock]
  let choosing ← cSteps ready [play flock]
  let (paid, reveal) ← (step 64 choosing (pick boundary)).toOption
  let attacking ← cSteps paid passBoth
  let flockTrigger ← attacking.pendingTriggers.head?
  let flockLink ← active attacking
  let created ← resolveTrigger attacking flockTrigger
  let token ← (created.zone arena).head?
  let defending ← cSteps created (passBoth ++ [defend first, defend second])
  let blocked ← cSteps defending (done :: (passBoth ++ passBoth ++ passBoth))
  let closed ← cSteps blocked passBoth
  let next ← cSteps closed [play nextAttack]
  let quickenTrigger ← next.pendingTriggers.head?
  let quickened ← resolveTrigger next quickenTrigger
  let nextHit ← cSteps quickened (passBoth ++ passBoth ++
    (done :: (passBoth ++ passBoth ++ passBoth)))
  let endLink ← active nextHit
  let blockedLink ← active blocked
  pure (card.status == .full && card.front.pitch == some pitch && card.front.defense == some 2 &&
    decide (rejected = unqualified) &&
    !(legalActionsFor attacker choosing).contains (pick expensive) &&
    (legalActionsFor attacker choosing).contains (pick nextAttack) &&
    reveal == [.revealed attacker boundary boundaryId] && paid.zone hand == choosing.zone hand &&
    (paid.poolOf attacker).resources == 0 && (paid.poolOf attacker).actionPoints == 1 &&
    paid.zone arena == [] && attacking.zone arena == [] && attacking.pendingTriggers.length == 1 &&
    linkAttackPower attacking flockLink == power && some flockTrigger.source == flockLink.attack &&
    (created.cardDefOf? token).map (·.id) == some ⟨"WTR_225"⟩ &&
    !linkHasKeyword blocked blockedLink .goAgain && blockedLink.damageDealt == 0 &&
    blocked.zone arena == [token] && blocked.pendingTriggers.isEmpty &&
    (blocked.poolOf attacker).actionPoints == 1 &&
    quickenTrigger.source == token && next.zone arena == [token] && quickened.zone arena == [] &&
    endLink.damageDealt == 4 && linkHasKeyword nextHit endLink .goAgain &&
    (nextHit.poolOf attacker).actionPoints == 1)

#guard checkFlockOfTheFeatherWalkers ⟨"WTR_182_R"⟩ 1 5 false == some true
#guard checkFlockOfTheFeatherWalkers ⟨"WTR_182_R"⟩ 1 5 true == some true

#guard checkFlockOfTheFeatherWalkers ⟨"WTR_183_Y"⟩ 2 4 false == some true
#guard checkFlockOfTheFeatherWalkers ⟨"WTR_183_Y"⟩ 2 4 true == some true

#guard checkFlockOfTheFeatherWalkers ⟨"WTR_184_B"⟩ 3 3 false == some true
#guard checkFlockOfTheFeatherWalkers ⟨"WTR_184_B"⟩ 3 3 true == some true

/-- Emerging Power waits for its controller's action phase and the next Guardian attack action. -/
meta def checkEmergingPower (cid : CardId) (pitch bonus : Nat) : Option Bool := do
  let attacker : PlayerId := ⟨0⟩
  let defender : PlayerId := ⟨1⟩
  let card ← m5Base.cards.find? cid
  let funded := m5Base.setPool attacker { actionPoints := 1, resources := 7 }
  let (withAura, aura) ← cPlace funded attacker .hand cid
  let (withOtherAura, opponentAura) ← cPlace withAura defender .permanent cid
  let (withGeneric, genericAttack) ← cPlace withOtherAura attacker .hand ⟨"WTR_203_R"⟩
  let (withGuardian, guardianAttack) ← cPlace withGeneric attacker .hand ⟨"WTR_048_R"⟩
  let (ready, guardianWeapon) ← cPlace withGuardian attacker .weapon ⟨"WTR_040"⟩
  let auraZone := Zone.player attacker .permanent
  let graveyard := Zone.player attacker .graveyard
  let play id : Action := ⟨.player attacker, .playCard id⟩
  let attackWith id : Action := ⟨.player attacker, .attackWeapon id⟩
  let startActionPhase (s : GameState) (p : PlayerId) :=
    (advance 64 { s with active := some p, phase := .startPhase, pending := [.actionPhaseStart p] } []).toOption
  let resolve (s : GameState) (p : PlayerId) (trigger : PendingTrigger) :=
    cSteps s [⟨.player p, .pickTriggerStart p⟩, ⟨.player p, .pickTrigger trigger.id⟩,
      ⟨.player p, .pass⟩, ⟨.player (if p == attacker then defender else attacker), .pass⟩]
  let beginAttack (s : GameState) (a : Action) :=
    cSteps s (a :: (passBoth ++ passBoth))
  let attackPower (s : GameState) :=
    (s.combat.bind CombatChain.activeLink?).map (linkAttackPower s)
  let played ← cSteps ready (play aura :: passBoth)
  let permanent ← (played.zone auraZone).head?
  let (opponentStart, _) ← startActionPhase played defender
  let opponentTrigger ← opponentStart.pendingTriggers.head?
  let opponentFinished ← resolve opponentStart defender opponentTrigger
  let (turnStart, _) ← startActionPhase (played.setPool attacker { resources := 5 }) attacker
  let trigger ← turnStart.pendingTriggers.head?
  let resolved ← resolve turnStart attacker trigger
  let generic ← beginAttack resolved (play genericAttack)
  let weapon ← beginAttack (resolved.setPool attacker { actionPoints := 1, resources := 8 })
    (attackWith guardianWeapon)
  let guardian ← beginAttack resolved (play guardianAttack)
  let (expired, _) ← (advance 64 { resolved with pending := [.endTurnCleanup attacker] } []).toOption
  pure (card.status == .full && card.front.pitch == some pitch && card.front.defense == some 3 &&
    permanent != aura && (played.poolOf attacker).actionPoints == 1 &&
    (played.poolOf attacker).resources == 5 && played.pendingTriggers.isEmpty &&
    played.activeEffects.isEmpty && opponentStart.pendingTriggers.length == 1 &&
    opponentTrigger.source == opponentAura && opponentFinished.zone auraZone == [permanent] &&
    turnStart.phase == .actionPhase && (turnStart.poolOf attacker).actionPoints == 1 &&
    turnStart.pendingTriggers.length == 1 && trigger.source == permanent &&
    resolved.zone auraZone == [] &&
    (resolved.zone graveyard).filterMap (fun id => (resolved.cardDefOf? id).map (·.id)) == [cid] &&
    resolved.activeEffects.length == 1 &&
    attackPower generic == some 4 && generic.activeEffects == resolved.activeEffects &&
    attackPower weapon == some 4 && weapon.activeEffects == resolved.activeEffects &&
    attackPower guardian == some (9 + bonus) && guardian.activeEffects.isEmpty &&
    expired.activeEffects.isEmpty)

#guard checkEmergingPower ⟨"WTR_069_R"⟩ 1 3 == some true

#guard checkEmergingPower ⟨"WTR_070_Y"⟩ 2 2 == some true

#guard checkEmergingPower ⟨"WTR_071_B"⟩ 3 1 == some true

/-- Blessing checks its pitch condition on entry-trigger resolution and reveals cards next action phase. -/
meta def checkBlessingOfDeliverance (cid : CardId) (pitch count gain : Nat) : Option Bool := do
  let player : PlayerId := ⟨0⟩
  let card ← m5Base.cards.find? cid
  let deck := Zone.player player .deck
  let hand := Zone.player player .hand
  let permanent := Zone.player player .permanent
  let firstId : CardId := ⟨"WTR_188_R"⟩
  let secondId : CardId := ⟨"WTR_203_R"⟩
  let thirdId : CardId := ⟨"WTR_048_R"⟩
  let (base, aura) ← cPlace m5Base player .hand cid
  let (withCheapPitch, cheapPitch) ← cPlace base player .hand ⟨"WTR_205_B"⟩
  let (withExpensivePitch, expensivePitch) ← cPlace withCheapPitch player .hand ⟨"WTR_190_B"⟩
  let (withThird, third) ← cPlace withExpensivePitch player .deck thirdId
  let (withSecond, second) ← cPlace withThird player .deck secondId
  let (ready, first) ← cPlace withSecond player .deck firstId
  let play : Action := ⟨.player player, .playCard aura⟩
  let pitchCard id : Action := ⟨.player player, .pitchCard id⟩
  let orderTrigger (id : Nat) :=
    [⟨.player player, .pickTriggerStart player⟩, ⟨.player player, .pickTrigger id⟩]
  let entering ← cSteps ready ([play, pitchCard cheapPitch] ++ passBoth)
  let enteringQualified ← cSteps ready ([play, pitchCard expensivePitch] ++ passBoth)
  let entry ← entering.pendingTriggers.head?
  let qualifiedEntry ← enteringQualified.pendingTriggers.head?
  let entered ← (entering.zone permanent).head?
  let withoutDraw ← cSteps entering (orderTrigger entry.id ++ passBoth)
  let withDraw ← cSteps enteringQualified (orderTrigger qualifiedEntry.id ++ passBoth)
  let nextPhase := { withoutDraw with phase := .startPhase, pending := [.actionPhaseStart player] }
  let (turnStart, _) ← (advance 64 nextPhase []).toOption
  let start ← turnStart.pendingTriggers.head?
  let stacked ← cSteps turnStart (orderTrigger start.id ++ [⟨.player player, .pass⟩])
  let (resolved, es) ← (step 64 stacked ⟨.player ⟨1⟩, .pass⟩).toOption
  let revealed := es.filterMap fun
    | .revealed p id face => some (p, id, face)
    | _ => none
  let expected := [(player, first, firstId), (player, second, secondId), (player, third, thirdId)].take count
  pure (card.status == .full && card.front.pitch == some pitch && card.front.defense == some 3 &&
    entry.source == entered && entering.pendingTriggers.length == 1 &&
    enteringQualified.pendingTriggers.length == 1 && (entering.poolOf player).actionPoints == 1 &&
    entering.zone deck == [first, second, third] && withoutDraw.zone deck == [first, second, third] &&
    (withoutDraw.zone hand).length == 1 && withDraw.zone deck == [second, third] &&
    (withDraw.zone hand).length == 2 && withDraw.lifeOf player == 40 &&
    turnStart.pendingTriggers.length == 1 && start.source == entered &&
    revealed == expected && resolved.zone deck == withoutDraw.zone deck &&
    resolved.zone permanent == [] && resolved.lifeOf player == 40 + Int.ofNat gain)

#guard checkBlessingOfDeliverance ⟨"WTR_054_R"⟩ 1 3 2 == some true

#guard checkBlessingOfDeliverance ⟨"WTR_055_Y"⟩ 2 2 1 == some true

#guard checkBlessingOfDeliverance ⟨"WTR_056_B"⟩ 3 1 1 == some true

/-- Seismic Surge reduces the next Guardian attack action cost once per token. -/
meta def checkSeismicSurge : Option Bool := do
  let player : PlayerId := ⟨0⟩
  let cid : CardId := ⟨"WTR_075"⟩
  let card ← m5Base.cards.find? cid
  let arena := Zone.player player .permanent
  let base := m5Base.setPool player { resources := 3 }
  let (withGeneric, genericAttack) ← cPlace base player .hand ⟨"WTR_203_R"⟩
  let (withGuardian, guardianAttack) ← cPlace withGeneric player .hand ⟨"WTR_048_R"⟩
  let (ready, hammer) ← cPlace withGuardian player .weapon ⟨"WTR_040"⟩
  let createTokens := Frame.run player ⟨0⟩ false [] [.prim (.createToken .controller cid 2)]
  let phaseStart := { ready with phase := .startPhase, pending := [createTokens, .actionPhaseStart player] }
  let (prompt, _) ← (advance 64 phaseStart []).toOption
  let first ← prompt.pendingTriggers[0]?
  let second ← prompt.pendingTriggers[1]?
  let pick tid : Action := ⟨.player player, .pickTrigger tid⟩
  let ordered ← cSteps prompt
    [⟨.player player, .pickTriggerStart player⟩, pick first.id, pick second.id]
  let resolved ← cSteps ordered (passBoth ++ passBoth)
  let play id : Action := ⟨.player player, .playCard id⟩
  let generic ← cSteps resolved [play genericAttack]
  let weapon ← cSteps resolved [⟨.player player, .attackWeapon hammer⟩]
  let reduced ← cSteps resolved [play guardianAttack]
  let lowResources := resolved.setPool player { actionPoints := 1, resources := 2 }
  let choosing ← cSteps lowResources [play guardianAttack]
  let cancelled ← cSteps choosing [⟨.player player, .cancelPlay⟩]
  let (expired, _) ← (advance 64 { resolved with pending := [.endTurnCleanup player] } []).toOption
  pure (card.status == .full && (prompt.zone arena).length == 2 &&
    prompt.pendingTriggers.length == 2 && first.id != second.id && first.source != second.source &&
    resolved.zone arena == [] && resolved.activeEffects.length == 2 &&
    (resolved.poolOf player).actionPoints == 1 &&
    (generic.poolOf player).resources == 3 && generic.activeEffects == resolved.activeEffects &&
    (weapon.poolOf player).resources == 0 && weapon.activeEffects == resolved.activeEffects &&
    (reduced.poolOf player).resources == 0 && (reduced.poolOf player).actionPoints == 0 &&
    reduced.activeEffects.isEmpty &&
    (match choosing.pending.head? with
      | some (.choosePitch _ _ _ _ cost) => cost.resources == 3
      | _ => false) &&
    decide (cancelled = lowResources) && expired.activeEffects.isEmpty)

#guard checkSeismicSurge == some true

/-- Stonewall Confidence boosts defenders at the printed cost threshold while the aura is active. -/
meta def checkStonewallConfidence (cid : CardId) (pitch : Nat) (bonus : Int) : Option Bool := do
  let player : PlayerId := ⟨0⟩
  let opponent : PlayerId := ⟨1⟩
  let arena := Zone.player player .permanent
  let grave := Zone.player player .graveyard
  let funded := m5Base.setPool player { actionPoints := 1, resources := 2 }
  let base : GameState := { funded with pending := funded.pending ++ [.beginTurn] }
  let card ← base.cards.find? cid
  let (withAura, aura) ← cPlace base player .hand cid
  let (withHigh, high) ← cPlace withAura player .hand ⟨"WTR_188_R"⟩
  let (withLow, low) ← cPlace withHigh player .hand ⟨"WTR_107_R"⟩
  let (ready, attack) ← cPlace withLow opponent .hand ⟨"WTR_203_R"⟩
  let placed ← cSteps ready (⟨.player player, .playCard aura⟩ :: passBoth)
  let source ← (placed.zone arena).head?
  let turn ← cSteps placed (passBoth ++ [⟨.player player, .arsenalSkip⟩])
  let defending ← cSteps turn
    (⟨.player opponent, .playCard attack⟩ :: (passBoth.reverse ++ passBoth.reverse))
  let block id : Action := ⟨.player player, .defendCard id⟩
  let highBlocked ← cSteps defending [block high]
  let lowBlocked ← cSteps defending [block low]
  let link (s : GameState) := s.combat.bind CombatChain.activeLink?
  let highLink ← link highBlocked
  let lowLink ← link lowBlocked
  let highDefender ← highLink.defending.head?
  let lowDefender ← lowLink.defending.head?
  let (removed, _) ← moveObj highBlocked source grave .top false
  let finish : Action := ⟨.player player, .defendDone⟩
  let (withReaction, reaction) ← cPlace defending player .hand ⟨"WTR_214_B"⟩
  let fundedReaction := withReaction.setPool player { resources := 3 }
  let response ← cSteps fundedReaction (finish :: (passBoth.reverse ++ [⟨.player opponent, .pass⟩]))
  let reactionPaid ← cSteps response [⟨.player player, .playCard reaction⟩]
  let reactionLayer ← (reactionPaid.zone .stack).head?
  let reactionResolved ← cSteps reactionPaid passBoth
  let reactionDefender ← (link reactionResolved).bind (·.defending.head?)
  let playThrough := finish :: (List.replicate 4 passBoth.reverse).flatten
  let closed ← cSteps highBlocked playThrough
  let lower ← cSteps lowBlocked playThrough
  let prompt ← cSteps closed passBoth.reverse
  let trigger ← prompt.pendingTriggers.head?
  let stacked ← cSteps prompt
    [⟨.player player, .pickTriggerStart player⟩, ⟨.player player, .pickTrigger trigger.id⟩]
  let resolved ← cSteps stacked passBoth
  let spent ← (resolved.zone grave).head?
  pure (card.status == .full && card.front.pitch == some pitch &&
    (placed.poolOf player).actionPoints == 1 && (placed.poolOf player).resources == 0 &&
    objEffectiveDefense placed high == some 3 && objEffectiveDefense defending high == some 3 &&
    objEffectiveDefense highBlocked highDefender == some (3 + bonus) &&
    objEffectiveDefense lowBlocked lowDefender == some 2 &&
    objEffectiveDefense removed highDefender == some 3 &&
    objEffectiveDefense reactionPaid reactionLayer == some 5 &&
    objEffectiveDefense reactionResolved reactionDefender == some (5 + bonus) &&
    linkTotalDefense highBlocked highLink == (3 + bonus).toNat &&
    linkTotalDefense lowBlocked lowLink == 2 &&
    closed.lifeOf player == 40 && lower.lifeOf player == 38 &&
    prompt.active == some player && trigger.source == source &&
    resolved.zone arena == [] && (resolved.cardDefOf? spent).map (·.id) == some cid)

#guard checkStonewallConfidence ⟨"WTR_072_R"⟩ 1 4 == some true
#guard checkStonewallConfidence ⟨"WTR_073_Y"⟩ 2 3 == some true
#guard checkStonewallConfidence ⟨"WTR_074_B"⟩ 3 2 == some true

/-- Forged for War gives live equipment defense until the aura leaves the arena. -/
meta def checkForgedForWar : Option Bool := do
  let player : PlayerId := ⟨0⟩
  let opponent : PlayerId := ⟨1⟩
  let cid : CardId := ⟨"WTR_046_Y"⟩
  let arena := Zone.player player .permanent
  let grave := Zone.player player .graveyard
  let funded := m5Base.setPool player { actionPoints := 1, resources := 2 }
  let base : GameState := { funded with pending := funded.pending ++ [.beginTurn] }
  let card ← base.cards.find? cid
  let (withChest, chest) ← cPlace base player .chest ⟨"WTR_005"⟩
  let (withHead, head) ← cPlace withChest player .head ⟨"WTR_155"⟩
  let (withOpponent, otherChest) ← cPlace withHead opponent .chest ⟨"WTR_005"⟩
  let (withAura, aura) ← cPlace withOpponent player .hand cid
  let (ready, attack) ← cPlace withAura opponent .hand ⟨"WTR_203_R"⟩
  let (faceDown, _) ← cPlace ready player .permanent cid true
  let play : Action := ⟨.player player, .playCard aura⟩
  let paid ← cSteps ready [play]
  let placed ← cSteps paid passBoth
  let source ← (placed.zone arena).head?
  let (twoAuras, _) ← cPlace placed player .permanent cid
  let (removedEarly, _) ← moveObj placed source grave .top false
  let otherTurn ← cSteps placed passBoth
  let defending ← cSteps otherTurn
    (⟨.player opponent, .playCard attack⟩ :: (passBoth.reverse ++ passBoth.reverse))
  let blocked ← cSteps defending [⟨.player player, .defendCard chest⟩]
  let finish : Action := ⟨.player player, .defendDone⟩
  let closed ← cSteps blocked (finish :: (List.replicate 4 passBoth.reverse).flatten)
  let prompt ← cSteps closed passBoth.reverse
  let trigger ← prompt.pendingTriggers.head?
  let stacked ← cSteps prompt
    [⟨.player player, .pickTriggerStart player⟩, ⟨.player player, .pickTrigger trigger.id⟩]
  let resolved ← cSteps stacked passBoth
  let spent ← (resolved.zone grave).head?
  pure (card.status == .full && card.front.defense == some 3 && card.front.pitch == some 2 &&
    objEffectiveDefense faceDown chest == some 1 && objEffectiveDefense paid chest == some 1 &&
    objEffectiveDefense placed chest == some 2 && objEffectiveDefense placed head == some 2 &&
    objEffectiveDefense twoAuras chest == some 3 &&
    objEffectiveDefense placed otherChest == some 1 && objEffectiveDefense removedEarly chest == some 1 &&
    (placed.poolOf player).actionPoints == 1 && (placed.poolOf player).resources == 0 &&
    otherTurn.active == some opponent && (blocked.zone .combatChain).contains chest &&
    objEffectiveDefense blocked chest == some 2 && closed.lifeOf player == 38 &&
    (closed.obj? chest).map (·.minusDefenseCounters) == some 1 &&
    prompt.active == some player && trigger.source == source && objEffectiveDefense stacked chest == some 1 &&
    resolved.zone arena == [] && (resolved.cardDefOf? spent).map (·.id) == some cid &&
    objEffectiveDefense resolved chest == some 0 && objEffectiveDefense resolved head == some 1)

#guard checkForgedForWar == some true

/-- Show Time! lets Bravo privately search for a Guardian attack action, then draws next turn. -/
meta def checkShowTime : Option Bool := do
  let player : PlayerId := ⟨0⟩
  let opponent : PlayerId := ⟨1⟩
  let cid : CardId := ⟨"WTR_047_B"⟩
  let chosenCid : CardId := ⟨"WTR_048_R"⟩
  let alternateCid : CardId := ⟨"WTR_049_Y"⟩
  let deck := Zone.player player .deck
  let hand := Zone.player player .hand
  let arena := Zone.player player .permanent
  let grave := Zone.player player .graveyard
  let funded := m5Base.setPool player { actionPoints := 1, resources := 3 }
  let base : GameState := { funded with pending := funded.pending ++ [.beginTurn] }
  let card ← base.cards.find? cid
  let (withHero, _) ← cPlace base player .hero ⟨"WTR_038"⟩
  let (withAura, aura) ← cPlace withHero player .hand cid
  let (withChosen, chosen) ← cPlace withAura player .deck chosenCid
  let (withTwo, alternate) ← cPlace withChosen player .deck alternateCid
  let (withGeneric, generic) ← cPlace withTwo player .deck ⟨"WTR_203_R"⟩
  let (withNonAttack, nonAttack) ← cPlace withGeneric player .deck ⟨"WTR_072_R"⟩
  let (ready, _) ← cPlace withNonAttack player .deck ⟨"WTR_188_R"⟩
  let play : Action := ⟨.player player, .playCard aura⟩
  let choose (id : ObjId) : Action := ⟨.player player, .pickShuffleCard (some id)⟩
  let done : Action := ⟨.player player, .pickShuffleCard none⟩
  let shuffle (s : GameState) : Action := ⟨.chance, .shuffleOrder (s.zone deck).reverse⟩
  let order (id : Nat) : List Action :=
    [⟨.player player, .pickTriggerStart player⟩, ⟨.player player, .pickTrigger id⟩]
  let placed ← cSteps ready (play :: passBoth)
  let source ← (placed.zone arena).head?
  let enter ← placed.pendingTriggers.head?
  let picking ← cSteps placed (order enter.id ++ passBoth)
  let (declined, declinedEvents) ← (step 64 picking done).toOption
  let withoutCard ← cSteps declined [shuffle declined]
  let (picked, pickEvents) ← (step 64 picking (choose chosen)).toOption
  let (revealed, revealEvents) ← (step 64 picked done).toOption
  let moved ← (revealed.zone hand).head?
  let afterSearch ← cSteps revealed [shuffle revealed]
  let afterEnd ← cSteps afterSearch (passBoth ++ [⟨.player player, .arsenalSkip⟩])
  let nextTurn ← cSteps afterEnd passBoth.reverse
  let start ← nextTurn.pendingTriggers.head?
  let stacked ← cSteps nextTurn (order start.id ++ [⟨.player player, .pass⟩])
  let (finished, endEvents) ← (step 64 stacked ⟨.player opponent, .pass⟩).toOption
  let destroyed ← (finished.zone grave).head?
  pure (card.status == .full && card.front.pitch == some 3 && card.front.defense == some 3 &&
    card.front.keywords.contains (.specialization "Bravo") &&
    enter.source == source && start.source == source &&
    (afterSearch.poolOf player).actionPoints == 0 && (afterSearch.poolOf player).resources == 0 &&
    viewZone player ready deck == .countOnly 5 &&
    (match viewZone player picking deck with | .entries entries => entries.length == 5 | _ => false) &&
    viewZone opponent picking deck == .countOnly 5 &&
    (view player picking).selectionChoices == [(alternate, alternateCid), (chosen, chosenCid)] &&
    (view opponent picking).selectionChoices.isEmpty && view opponent picking == view opponent picked &&
    (step 64 picking (choose generic)).toOption.isNone &&
    (step 64 picking (choose nonAttack)).toOption.isNone &&
    (step 64 picking ⟨.player opponent, .pickShuffleCard (some chosen)⟩).toOption.isNone &&
    (step 64 picked (choose alternate)).toOption.isNone &&
    picked.zone deck == picking.zone deck && picked.zone hand == [] && pickEvents == [] &&
    revealEvents == [.revealed player chosen chosenCid, .moved chosen moved deck hand] &&
    revealed.pending.head? == some (.chanceShuffle deck) &&
    (afterSearch.cardDefOf? moved).map (·.id) == some chosenCid &&
    afterSearch.zone arena == [source] && viewZone player afterSearch deck == .countOnly 4 &&
    declinedEvents == [] && declined.pending.head? == some (.chanceShuffle deck) &&
    withoutCard.zone hand == [] && (withoutCard.zone deck).length == 5 &&
    (nextTurn.zone hand).length == 4 && finished.zone arena == [] &&
    (finished.cardDefOf? destroyed).map (·.id) == some cid &&
    endEvents.head? == some (.moved source destroyed arena grave) &&
    (finished.zone hand).length == 5 && (finished.zone deck).isEmpty)

#guard checkShowTime == some true

/-- Fyendal's Spring Tunic gains optional counters in the Start Phase and removes them as a cost. -/
meta def checkFyendalsSpringTunic : Option Bool := do
  let player : PlayerId := ⟨0⟩
  let opponent : PlayerId := ⟨1⟩
  let cid : CardId := ⟨"WTR_150"⟩
  let chest := Zone.player player .chest
  let grave := Zone.player player .graveyard
  let card ← m5Base.cards.find? cid
  let (equipped, tunic) ← cPlace (m5Base.setPool player {}) player .chest cid
  let (ready, otherTunic) ← cPlace equipped opponent .chest cid
  let openTurn := [Frame.startPhaseWork player, .actionPhaseStart player, .endPhaseStart player, .beginTurn]
  let first ← (advance 64 { ready with pending := openTurn } []).toOption.map Prod.fst
  let offer (s : GameState) (p : PlayerId) : Option GameState := do
    let trigger ← s.pendingTriggers.head?
    cSteps s [⟨.player p, .pickTriggerStart p⟩, ⟨.player p, .pickTrigger trigger.id⟩]
  let answer (s : GameState) (p : PlayerId) (yes : Bool) : Option GameState := do
    let choosing ← offer s p
    cSteps choosing [⟨.player p, .pickMay yes⟩]
  let charge : Action := ⟨.player player, .pickMay true⟩
  let activate : Action := ⟨.player player, .activateAbility tunic 1⟩
  let energy (s : GameState) (id : ObjId) := (s.obj? id).map (·.counterCount .energy)
  let choosing ← offer first player
  let firstTurn ← cSteps choosing [charge]
  let declined ← cSteps choosing [⟨.player player, .pickMay false⟩]
  let firstOpponent ← cSteps firstTurn passBoth
  let firstOpponentTurn ← answer firstOpponent opponent true
  let second ← cSteps firstOpponentTurn passBoth.reverse
  let secondTurn ← answer second player true
  let secondOpponent ← cSteps secondTurn passBoth
  let secondOpponentTurn ← answer secondOpponent opponent false
  let third ← cSteps secondOpponentTurn passBoth.reverse
  let thirdTurn ← answer third player true
  let thirdOpponent ← cSteps thirdTurn passBoth
  let thirdOpponentTurn ← answer thirdOpponent opponent false
  let atCap ← cSteps thirdOpponentTurn passBoth.reverse
  let priority ← cSteps thirdOpponentTurn [⟨.player opponent, .pass⟩]
  let paid ← cSteps priority [activate]
  let resolved ← cSteps paid passBoth
  let extra := updateSingleObject priority tunic (fun o => o.addCounterVal .energy 1)
  let paidExtra ← cSteps extra [activate]
  let attacker := ready.setPool opponent { actionPoints := 1 }
  let attackBase : GameState :=
    { attacker with active := some opponent, pending := [.priority opponent 0, .endPhaseStart opponent] }
  let (withAttack, attack) ← cPlace attackBase opponent .hand ⟨"WTR_203_R"⟩
  let defending ← cSteps withAttack
    (⟨.player opponent, .playCard attack⟩ :: (passBoth.reverse ++ passBoth.reverse))
  let worn ← cSteps defending ([⟨.player player, .defendCard tunic⟩, ⟨.player player, .defendDone⟩] ++
    (List.replicate 4 passBoth.reverse).flatten)
  let broken ← (worn.zone grave).head?
  pure (card.status == .full && card.front.defense == some 1 && card.front.keywords.contains .bladeBreak &&
    first.phase == .startPhase && choosing.phase == .startPhase &&
    (choosing.poolOf player).actionPoints == 0 && !(legalActionsFor player choosing).contains activate &&
    !(legalActionsFor player choosing).contains ⟨.player player, .pass⟩ &&
    (legalActionsFor player choosing).contains charge &&
    declined.phase == .actionPhase && energy declined tunic == some 0 &&
    firstTurn.phase == .actionPhase && (firstTurn.poolOf player).actionPoints == 1 &&
    energy firstTurn tunic == some 1 && energy firstOpponentTurn otherTunic == some 1 &&
    energy firstOpponentTurn tunic == some 1 &&
    energy secondTurn tunic == some 2 && !(legalActionsFor player secondTurn).contains activate &&
    energy thirdTurn tunic == some 3 && (legalActionsFor player thirdTurn).contains activate &&
    atCap.phase == .actionPhase && atCap.pending.head? == some (.priority player 0) &&
    atCap.pendingTriggers.isEmpty && energy atCap tunic == some 3 &&
    priority.active == some opponent && (legalActionsFor player priority).contains activate &&
    energy paid tunic == some 0 && (paid.poolOf player).resources == 0 &&
    !(legalActionsFor player paid).contains activate &&
    (resolved.poolOf player).resources == 1 && (resolved.poolOf player).actionPoints == 0 &&
    energy paidExtra tunic == some 1 && energy resolved otherTunic == some 1 &&
    worn.zone chest == [] && (worn.cardDefOf? broken).map (·.id) == some cid)

#guard checkFyendalsSpringTunic == some true

/-- Remembrance lets its caster choose up to three action cards, then banishes itself. -/
meta def checkRemembrance : Option Bool := do
  let attacker : PlayerId := ⟨0⟩
  let player : PlayerId := ⟨1⟩
  let cid : CardId := ⟨"WTR_163_Y"⟩
  let grave := Zone.player player .graveyard
  let deck := Zone.player player .deck
  let hand := Zone.player player .hand
  let banished := Zone.player player .banished
  let card ← m5Base.cards.find? cid
  let (withSpell, spell) ← cPlace m5Base player .hand cid
  let (withReserve, reserve) ← cPlace withSpell player .hand ⟨"WTR_203_R"⟩
  let (withTop, top) ← cPlace withReserve player .deck ⟨"WTR_191_R"⟩
  let (withFirst, first) ← cPlace withTop player .graveyard ⟨"WTR_203_R"⟩
  let (withKeep, keep) ← cPlace withFirst player .graveyard ⟨"WTR_204_Y"⟩
  let (withThird, third) ← cPlace withKeep player .graveyard ⟨"WTR_205_B"⟩
  let (withAction, nonAttack) ← cPlace withThird player .graveyard ⟨"WTR_218_R"⟩
  let (withInstant, instant) ← cPlace withAction player .graveyard ⟨"WTR_173_R"⟩
  let (ready, reaction) ← cPlace withInstant player .graveyard ⟨"WTR_215_R"⟩
  let choose (id : ObjId) : Action := ⟨.player player, .pickShuffleCard (some id)⟩
  let done : Action := ⟨.player player, .pickShuffleCard none⟩
  let shuffle (ids : List ObjId) : Action := ⟨.chance, .shuffleOrder ids⟩
  let paid ← cSteps ready
    [⟨.player attacker, .pass⟩, ⟨.player player, .playCard spell⟩]
  let layer ← (paid.zone .stack).head?
  let picking ← cSteps paid passBoth.reverse
  let limit ← cSteps picking [choose third, choose nonAttack, choose first]
  let (committed, moves) ← (step 64 limit done).toOption
  let resolved ← cSteps committed [shuffle (committed.zone deck).reverse]
  let spent ← (resolved.zone banished).head?
  let zero ← cSteps picking [done, shuffle [top]]
  pure (card.status == .full && card.front.pitch == some 2 && card.front.defense.isNone &&
    (paid.poolOf player).actionPoints == 0 && (paid.poolOf player).resources == 0 &&
    paid.zone grave == ready.zone grave && (step 64 paid (choose third)).toOption.isNone &&
    (legalActionsFor player picking).contains (choose keep) &&
    (legalActionsFor player picking).contains (choose nonAttack) &&
    (step 64 picking (choose instant)).toOption.isNone && (step 64 picking (choose reaction)).toOption.isNone &&
    (step 64 picking (choose layer)).toOption.isNone && (step 64 picking (choose reserve)).toOption.isNone &&
    (step 64 limit (choose keep)).toOption.isNone && limit.zone grave == ready.zone grave &&
    moves.length == 3 && committed.zone grave == [reaction, instant, keep] &&
    committed.pending.head? == some (.chanceShuffle deck) && committed.zone .stack == [layer] &&
    resolved.zone deck == (committed.zone deck).reverse && resolved.zone hand == [reserve] &&
    resolved.zone grave == [reaction, instant, keep] && resolved.zone .stack == [] &&
    (resolved.obj? spent).any (fun obj => !obj.faceDown) &&
    (resolved.cardDefOf? spent).map (·.id) == some cid &&
    zero.zone grave == ready.zone grave && zero.zone deck == [top] && zero.zone hand == [reserve] &&
    (zero.zone banished).any (fun id => (zero.cardDefOf? id).map (·.id) == some cid))

#guard checkRemembrance == some true

/-- Hope Merchant's Hood shuffles exactly the cards its controller chooses, then draws that many. -/
meta def checkHopeMerchantsHood : Option Bool := do
  let attacker : PlayerId := ⟨0⟩
  let player : PlayerId := ⟨1⟩
  let cid : CardId := ⟨"WTR_151"⟩
  let hand := Zone.player player .hand
  let deck := Zone.player player .deck
  let grave := Zone.player player .graveyard
  let head := Zone.player player .head
  let keepCid : CardId := ⟨"WTR_203_R"⟩
  let pickOneCid : CardId := ⟨"WTR_204_Y"⟩
  let pickTwoCid : CardId := ⟨"WTR_205_B"⟩
  let topCid : CardId := ⟨"WTR_188_R"⟩
  let bottomCid : CardId := ⟨"WTR_189_Y"⟩
  let card ← m5Base.cards.find? cid
  let (equipped, source) ← cPlace m5Base player .head cid
  let (withKeep, keep) ← cPlace equipped player .hand keepCid
  let (withOne, one) ← cPlace withKeep player .hand pickOneCid
  let (withHand, two) ← cPlace withOne player .hand pickTwoCid
  let (withDeckTop, top) ← cPlace withHand player .deck topCid
  let (withDeck, bottom) ← cPlace withDeckTop player .deck bottomCid
  let (ready, attack) ← cPlace withDeck attacker .hand ⟨"WTR_203_R"⟩
  let activate : Action := ⟨.player player, .activateAbility source 0⟩
  let choose (id : ObjId) : Action := ⟨.player player, .pickShuffleCard (some id)⟩
  let done : Action := ⟨.player player, .pickShuffleCard none⟩
  let shuffle (ids : List ObjId) : Action := ⟨.chance, .shuffleOrder ids⟩
  let announced ← cSteps ready [⟨.player attacker, .playCard attack⟩, ⟨.player attacker, .pass⟩]
  let attackLayer ← (announced.zone .stack).head?
  let (paid, payment) ← (step 64 announced activate).toOption
  let spent ← (paid.zone grave).head?
  let picking ← cSteps paid passBoth.reverse
  let pickingAgain ← cSteps picking [choose one]
  let beforeConfirm ← cSteps pickingAgain [choose two]
  let (committed, moves) ← (step 64 beforeConfirm done).toOption
  let inDeck ← (committed.zone deck).find? (fun id => (committed.cardDefOf? id).map (·.id) == some pickOneCid)
  let otherInDeck ← (committed.zone deck).find? (fun id => (committed.cardDefOf? id).map (·.id) == some pickTwoCid)
  let drawn ← cSteps committed [shuffle [top, bottom, inDeck, otherInDeck]]
  let zero ← cSteps picking [done]
  let zeroDrawn ← cSteps zero [shuffle [bottom, top]]
  let all ← cSteps picking [choose one, choose two, choose keep, done]
  pure (card.status == .full && card.front.defense == some 0 &&
    (legalActionsFor player announced).contains activate && paid.zone head == [] &&
    (paid.cardDefOf? spent).map (·.id) == some cid && payment.contains (.moved source spent head grave) &&
    (step 64 paid (choose one)).toOption.isNone &&
    (legalActionsFor player picking).contains (choose one) && (legalActionsFor player picking).contains done &&
    (view player picking).selectionChoices.contains (one, pickOneCid) &&
    (view attacker picking).selectionChoices.isEmpty && view attacker picking == view attacker beforeConfirm &&
    !(legalActionsFor attacker picking).any (fun a => match a.kind with | .pickShuffleCard _ => true | _ => false) &&
    (step 64 picking ⟨.player attacker, .pickShuffleCard (some one)⟩).toOption.isNone &&
    (step 64 picking (choose top)).toOption.isNone &&
    (step 64 pickingAgain (choose one)).toOption.isNone &&
    beforeConfirm.zone hand == announced.zone hand && beforeConfirm.zone deck == announced.zone deck &&
    committed.zone hand == [keep] && committed.pending.head? == some (.chanceShuffle deck) &&
    moves == [.moved one inDeck hand deck, .moved two otherInDeck hand deck] &&
    !(legalActionsFor player committed).contains done &&
    (drawn.zone hand).length == 3 && (drawn.zone hand).contains keep &&
    (drawn.zone hand).any (fun id => (drawn.cardDefOf? id).map (·.id) == some topCid) &&
    (drawn.zone hand).any (fun id => (drawn.cardDefOf? id).map (·.id) == some bottomCid) &&
    drawn.zone deck == [inDeck, otherInDeck] && drawn.zone .stack == [attackLayer] &&
    zero.pending.head? == some (.chanceShuffle deck) &&
    zeroDrawn.zone hand == announced.zone hand && zeroDrawn.zone .stack == [attackLayer] &&
    all.zone hand == [] && (all.zone deck).length == 5)

#guard checkHopeMerchantsHood == some true

/-- Bravo grants Dominate to every cost-3-or-more attack action card played that turn. -/
meta def checkBravoAbility (cid : CardId) (life : Int) (young : Bool) : Option Bool := do
  let player : PlayerId := ⟨0⟩
  let opponent : PlayerId := ⟨1⟩
  let card ← m5Base.cards.find? cid
  let (withHero, source) ← cPlace m5Base player .hero cid
  let (withWeapon, weapon) ← cPlace withHero player .weapon ⟨"WTR_040"⟩
  let (withReserve, red1) ← cPlace withWeapon player .hand ⟨"WTR_203_R"⟩
  let (withPitch, red2) ← cPlace withReserve player .hand ⟨"WTR_203_R"⟩
  let (withCheap, cheap) ← cPlace withPitch player .hand ⟨"WTR_107_R"⟩
  let (withFirst, first) ← cPlace withCheap player .hand ⟨"WTR_188_R"⟩
  let (withSecond, second) ← cPlace withFirst player .hand ⟨"WTR_188_R"⟩
  let (withBlock, block1) ← cPlace withSecond opponent .hand ⟨"WTR_203_R"⟩
  let (withBlocks, block2) ← cPlace withBlock opponent .hand ⟨"WTR_203_R"⟩
  let (ready, opposingAttack) ← cPlace withBlocks opponent .hand ⟨"WTR_188_R"⟩
  let activate : Action := ⟨.player player, .activateAbility source 0⟩
  let pitch id : Action := ⟨.player player, .pitchCard id⟩
  let play id : Action := ⟨.player player, .playCard id⟩
  let block id : Action := ⟨.player opponent, .defendCard id⟩
  let finish : Action := ⟨.player opponent, .defendDone⟩
  let defend (state : GameState) (action : Action) := cSteps state (action :: (passBoth ++ passBoth))
  let finishLink (state : GameState) := cSteps state (finish :: (passBoth ++ passBoth ++ passBoth))
  let dominates (s : GameState) :=
    (s.combat.bind CombatChain.activeLink?).any fun link => linkHasKeyword s link .dominate
  let hasDominate (s : GameState) (id : ObjId) :=
    (s.characteristics id).any (fun chars => chars.keywords.contains .dominate)
  let declaring ← cSteps ready [activate]
  let onePitch ← cSteps declaring [pitch red1]
  let cancelled ← cSteps onePitch [⟨.player player, .cancelPlay⟩]
  let paidByPitch ← cSteps onePitch [pitch red2]
  let fromPitch ← cSteps paidByPitch passBoth
  let funded := ready.setPool player { actionPoints := 4, resources := 12 }
  let paid ← cSteps funded [activate]
  let buffed ← cSteps paid passBoth
  let weaponDefend ← defend buffed ⟨.player player, .attackWeapon weapon⟩
  let cheapDefend ← defend buffed (play cheap)
  let firstDefend ← defend buffed (play first)
  let blocked ← cSteps firstDefend [block block1]
  let afterFirst ← finishLink blocked
  let secondDefend ← defend afterFirst (play second)
  let expired ← cSteps buffed (passBoth ++ [⟨.player player, .arsenalSkip⟩])
  pure (card.status == .full && card.front.life == some life && card.front.intellect == some 4 &&
    card.front.hasSubtype .young == young &&
    (legalActionsFor player declaring).contains (pitch red1) &&
    (legalActionsFor player onePitch).contains (pitch red2) && decide (cancelled = ready) &&
    (paidByPitch.poolOf player).actionPoints == 0 && (paidByPitch.poolOf player).resources == 0 &&
    (paidByPitch.zone (.player player .pitch)).length == 2 &&
    (fromPitch.poolOf player).actionPoints == 1 && fromPitch.activeEffects.length == 1 &&
    (paid.poolOf player).actionPoints == 3 && (paid.poolOf player).resources == 10 &&
    paid.activeEffects.isEmpty && (buffed.poolOf player).actionPoints == 4 &&
    buffed.activeEffects.length == 1 &&
    hasDominate buffed first && hasDominate buffed second &&
    !hasDominate paid first && !hasDominate buffed opposingAttack &&
    !(dominates weaponDefend) && !(dominates cheapDefend) &&
    dominates firstDefend && dominates secondDefend &&
    !(legalActionsFor opponent blocked).contains (block block2) &&
    firstDefend.activeEffects == buffed.activeEffects && secondDefend.activeEffects == buffed.activeEffects &&
    expired.activeEffects.isEmpty)

#guard checkBravoAbility ⟨"WTR_038"⟩ 40 false == some true
#guard checkBravoAbility ⟨"WTR_039"⟩ 20 true == some true

/-- Helm of Isen's Peak raises only its hero's intellect for that turn's refill. -/
meta def checkHelmOfIsensPeak : Option Bool := do
  let player : PlayerId := ⟨0⟩
  let opponent : PlayerId := ⟨1⟩
  let cid : CardId := ⟨"WTR_042"⟩
  let slot := Zone.player player .head
  let grave := Zone.player player .graveyard
  let pitch := Zone.player player .pitch
  let hand := Zone.player player .hand
  let base : GameState := { m5Base with pending := m5Base.pending ++ [.beginTurn] }
  let card ← base.cards.find? cid
  let (withHero, hero) ← cPlace base player .hero ⟨"WTR_038"⟩
  let (withOpponent, _) ← cPlace withHero opponent .hero ⟨"WTR_039"⟩
  let fill (p : PlayerId) (s : GameState) :=
    (List.replicate 6 ()).foldlM (fun state _ => (cPlace state p .deck ⟨"WTR_205_B"⟩).map Prod.fst) s
  let withDeck ← fill player withOpponent
  let fullDecks ← fill opponent withDeck
  let (equipped, source) ← cPlace fullDecks player .head cid
  let (ready, reserve) ← cPlace equipped player .hand ⟨"WTR_203_R"⟩
  let activate : Action := ⟨.player player, .activateAbility source 0⟩
  let choosing ← cSteps ready [activate]
  let canceled ← cSteps choosing [⟨.player player, .cancelPlay⟩]
  let (paid, events) ← (step 64 choosing ⟨.player player, .pitchCard reserve⟩).toOption
  let spent ← (paid.zone grave).head?
  let pitched ← (paid.zone pitch).head?
  let resolved ← cSteps paid passBoth
  let (drawing, _) ← microStep { resolved with pending := [.endTurnCleanup player] }
  let returning ← cSteps resolved passBoth
  let ended ← cSteps returning [⟨.player player, .pitchReturnPick pitched⟩]
  let normal ← cSteps equipped passBoth
  let (wearReady, wearSource) ← cPlace m5Base opponent .head cid
  let (withAttack, attack) ← cPlace wearReady player .hand ⟨"WTR_203_R"⟩
  let defending ← cSteps withAttack (⟨.player player, .playCard attack⟩ :: (passBoth ++ passBoth))
  let closed ← cSteps defending ([⟨.player opponent, .defendCard wearSource⟩,
    ⟨.player opponent, .defendDone⟩] ++ passBoth ++ passBoth ++ passBoth ++ passBoth)
  pure (card.status == .full && card.front.defense == some 1 && card.front.keywords.contains .battleworn &&
    choosing.zone slot == [source] && decide (canceled = ready) &&
    paid.zone slot == [] && (paid.cardDefOf? spent).map (·.id) == some cid &&
    events.contains (.moved source spent slot grave) &&
    (paid.poolOf player).actionPoints == 0 && (paid.poolOf player).resources == 0 &&
    paid.intellectOf player == 4 && resolved.intellectOf player == 5 && resolved.intellectOf opponent == 4 &&
    resolved.activeEffects.any (fun e => e.target == .objects [hero] && e.op == .addIntellect 1) &&
    (resolved.poolOf player).actionPoints == 0 &&
    drawing.intellectOf player == 5 && drawing.pending.head? == some (.draw player 5) &&
    (ended.zone hand).length == 5 && (normal.zone hand).length == 4 &&
    (ended.zone (.player opponent .hand)).length == 4 && ended.active == some opponent &&
    ended.intellectOf player == 4 && ended.activeEffects.isEmpty &&
    closed.lifeOf opponent == 37 && closed.zone (.player opponent .head) == [wearSource] &&
    (closed.obj? wearSource).map (·.minusDefenseCounters) == some 1)

#guard checkHelmOfIsensPeak == some true

/-- Tectonic Plating supports pitching and cancellation, with a token and Go Again on resolution. -/
meta def checkTectonicPlating : Option Bool := do
  let player : PlayerId := ⟨0⟩
  let opponent : PlayerId := ⟨1⟩
  let cid : CardId := ⟨"WTR_041"⟩
  let chest := Zone.player player .chest
  let arena := Zone.player player .permanent
  let pitch := Zone.player player .pitch
  let base : GameState := { m5Base with pending := m5Base.pending ++ [.beginTurn] }
  let card ← base.cards.find? cid
  let (equipped, source) ← cPlace base player .chest cid
  let (ready, pitchCard) ← cPlace equipped player .hand ⟨"WTR_203_R"⟩
  let activate : Action := ⟨.player player, .activateAbility source 0⟩
  let funded := equipped.setPool player { actionPoints := 1, resources := 1 }
  let fromPool ← cSteps funded [activate]
  let fromPoolResolved ← cSteps fromPool passBoth
  let unpayable := equipped.setPool player { actionPoints := 1 }
  let noAP := ready.setPool player {}
  let choosing ← cSteps ready [activate]
  let canceled ← cSteps choosing [⟨.player player, .cancelPlay⟩]
  let paid ← cSteps choosing [⟨.player player, .pitchCard pitchCard⟩]
  let pitched ← (paid.zone pitch).head?
  let resolved ← cSteps paid passBoth
  let surge ← (resolved.zone arena).head?
  let returning ← cSteps resolved passBoth
  let otherTurn ← cSteps returning [⟨.player player, .pitchReturnPick pitched⟩]
  let ownTurn ← cSteps otherTurn passBoth.reverse
  let trigger ← ownTurn.pendingTriggers.head?
  let stacked ← cSteps ownTurn [⟨.player player, .pickTriggerStart player⟩, ⟨.player player, .pickTrigger trigger.id⟩]
  let reduced ← cSteps stacked passBoth
  let (withAttack, attack) ← cPlace reduced player .hand ⟨"WTR_048_R"⟩
  let applying := withAttack.setPool player { actionPoints := 1, resources := 4 }
  let discounted ← cSteps applying [⟨.player player, .playCard attack⟩]
  pure (card.status == .full && card.front.defense == some 2 && card.front.keywords.contains .battleworn &&
    (legalActionsFor player ready).contains activate && !(legalActionsFor player unpayable).contains activate &&
    (step 64 noAP activate).toOption.isNone && (step 64 unpayable activate).toOption.isNone &&
    (match choosing.pending.head? with | some (.choosePitch _ _ _ _ cost) => cost.resources == 1 | _ => false) &&
    choosing.zone chest == [source] && choosing.activatedThisTurn.isEmpty &&
    (choosing.poolOf player).actionPoints == 1 && decide (canceled = ready) &&
    paid.zone chest == [source] && paid.zone arena == [] && paid.playRollback.isNone &&
    paid.activatedThisTurn.contains (source, 0) &&
    (paid.poolOf player).actionPoints == 0 && (paid.poolOf player).resources == 0 &&
    (paid.cardDefOf? pitched).map (·.id) == some ⟨"WTR_203_R"⟩ &&
    (resolved.poolOf player).actionPoints == 1 && (resolved.cardDefOf? surge).map (·.id) == some ⟨"WTR_075"⟩ &&
    fromPoolResolved.zone chest == [source] && (fromPoolResolved.zone arena).length == 1 &&
    (fromPool.poolOf player).resources == 0 && (fromPoolResolved.poolOf player).actionPoints == 1 &&
    (step 64 (resolved.setPool player { actionPoints := 1, resources := 1 }) activate).toOption.isNone &&
    otherTurn.active == some opponent && otherTurn.zone arena == [surge] &&
    ownTurn.active == some player && ownTurn.activatedThisTurn.isEmpty && trigger.source == surge &&
    reduced.zone arena == [] && reduced.activeEffects.length == 1 &&
    (legalActionsFor player applying).contains activate &&
    (discounted.poolOf player).resources == 0 && discounted.activeEffects.isEmpty)

#guard checkTectonicPlating == some true

/-- Anothos tracks its own activation, and its proxy sees cards pitched during the reaction step. -/
meta def checkAnothos : Option Bool := do
  let player : PlayerId := ⟨0⟩
  let defender : PlayerId := ⟨1⟩
  let cid : CardId := ⟨"WTR_040"⟩
  let card ← m5Base.cards.find? cid
  let funded := m5Base.setPool player { actionPoints := 2, resources := 3 }
  let (armed, weapon) ← cPlace funded player .weapon cid
  let (withCheap, _) ← cPlace armed player .pitch ⟨"WTR_203_R"⟩
  let (withQualifying, _) ← cPlace withCheap player .pitch ⟨"WTR_189_Y"⟩
  let (withReaction, overpower) ← cPlace withQualifying player .hand ⟨"WTR_123_R"⟩
  let (ready, pitchCard) ← cPlace withReaction player .hand ⟨"WTR_190_B"⟩
  let (twoQualifying, _) ← cPlace ready player .pitch ⟨"WTR_188_R"⟩
  let swing : Action := ⟨.player player, .attackWeapon weapon⟩
  let cast : Action := ⟨.player player, .playCard overpower⟩
  let defendDone : Action := ⟨.player defender, .defendDone⟩
  let beginAttack (s : GameState) := cSteps s (swing :: (passBoth ++ passBoth))
  let power (s : GameState) := (s.combat.bind CombatChain.activeLink?).map (linkAttackPower s)
  let damage (s : GameState) := (s.combat.bind CombatChain.activeLink?).map (·.damageDealt)
  let poor := ready.setPool player { actionPoints := 2 }
  let choosing ← cSteps poor [swing]
  let cancelled ← cSteps choosing [⟨.player player, .cancelPlay⟩]
  let normal ← beginAttack ready
  let boosted ← beginAttack twoQualifying
  let normalHit ← cSteps normal (defendDone :: (passBoth ++ passBoth ++ passBoth))
  let boostHit ← cSteps boosted (defendDone :: (passBoth ++ passBoth ++ passBoth))
  let reaction ← cSteps normal (defendDone :: passBoth)
  let paying ← cSteps reaction [cast]
  let paid ← cSteps paying [⟨.player player, .pitchCard pitchCard⟩]
  let overpowerHit ← cSteps paid (passBoth ++ passBoth)
  let closed ← cSteps normalHit passBoth
  let refunded := closed.setPool player { actionPoints := 1, resources := 3 }
  let (reset, _) ← microStep { closed with pending := [.endTurnCleanup player] }
  let nextTurn := (reset.setPool player { actionPoints := 1, resources := 3 })
  let nextTurn := { nextTurn with pending := [.priority player 0] }
  pure (card.status == .full && card.front.power == some 4 &&
    objEffectivePower ready weapon == some 4 && objEffectivePower twoQualifying weapon == some 6 &&
    decide (cancelled = poor) && choosing.activatedThisTurn.isEmpty &&
    normal.activatedThisTurn == [(weapon, 0)] &&
    (normal.poolOf player).actionPoints == 1 && (normal.poolOf player).resources == 0 &&
    power normal == some 4 && damage normalHit == some 4 &&
    power boosted == some 6 && damage boostHit == some 6 &&
    power paid == some 6 && damage overpowerHit == some 10 &&
    !(legalActionsFor player refunded).contains swing && (step 64 refunded swing).toOption.isNone &&
    reset.activatedThisTurn.isEmpty && (legalActionsFor player nextTurn).contains swing)

#guard checkAnothos == some true

/-- Each Kodachi may attack once and gains Go Again from a defined zero-cost pitch card. -/
meta def checkHarmonizedKodachi : Option Bool := do
  let player : PlayerId := ⟨0⟩
  let defender : PlayerId := ⟨1⟩
  let cid : CardId := ⟨"WTR_078"⟩
  let card ← m5Base.cards.find? cid
  let funded := m5Base.setPool player { actionPoints := 1, resources := 2 }
  let (armed, first) ← cPlace funded player .weapon cid
  let (paired, second) ← cPlace armed player .weapon cid
  let (withBauble, _) ← cPlace paired player .pitch ⟨"WTR_224_Y"⟩
  let (withCostOne, _) ← cPlace withBauble player .pitch ⟨"WTR_101_R"⟩
  let (withRazor, razor) ← cPlace withCostOne player .hand ⟨"WTR_209_R"⟩
  let (ready, latePitch) ← cPlace withRazor player .hand ⟨"WTR_205_B"⟩
  let (withCostZero, _) ← cPlace ready player .pitch ⟨"WTR_203_R"⟩
  let swing id : Action := ⟨.player player, .attackWeapon id⟩
  let done : Action := ⟨.player defender, .defendDone⟩
  let beginAttack := passBoth ++ passBoth
  let finish := done :: (passBoth ++ passBoth ++ passBoth)
  let active (s : GameState) := s.combat.bind CombatChain.activeLink?
  let without ← cSteps ready (swing first :: (beginAttack ++ finish))
  let firstHit ← cSteps withCostZero (swing first :: (beginAttack ++ finish))
  let firstClosed ← cSteps firstHit passBoth
  let secondHit ← cSteps firstClosed (swing second :: (beginAttack ++ finish))
  let lateStart := ready.setPool player { actionPoints := 1, resources := 1 }
  let reaction ← cSteps lateStart (swing first :: (beginAttack ++ [done] ++ passBoth))
  let unpaid ← cSteps reaction
    [⟨.player player, .playCard razor⟩, ⟨.player player, .pickMode 0⟩]
  let paid ← cSteps unpaid [⟨.player player, .pitchCard latePitch⟩]
  let lateHit ← cSteps paid (passBoth ++ passBoth ++ passBoth)
  let delayedCheck (s : GameState) := (active s).any (fun link => linkHasKeyword s link .goAgain)
  pure (card.status == .full && card.front.power == some 1 &&
    !delayedCheck without && (without.poolOf player).actionPoints == 0 &&
    delayedCheck firstHit && (firstHit.poolOf player).actionPoints == 1 &&
    !(legalActionsFor player firstClosed).contains (swing first) &&
    (legalActionsFor player firstClosed).contains (swing second) &&
    delayedCheck secondHit && (secondHit.poolOf player).actionPoints == 1 &&
    secondHit.activatedThisTurn == [(first, 0), (second, 0)] &&
    !delayedCheck reaction && delayedCheck paid && delayedCheck lateHit &&
    (active lateHit).map (·.damageDealt) == some 4 && (lateHit.poolOf player).actionPoints == 1)

#guard checkHarmonizedKodachi == some true

/-- Flic Flak applies only to the first subsequent defending card, even across combat chains. -/
meta def checkFlicFlak (cid : CardId) (pitch defense : Nat) : Option Bool := do
  let attacker : PlayerId := ⟨0⟩
  let defender : PlayerId := ⟨1⟩
  let card ← m5Base.cards.find? cid
  let funded := (m5Base.setPool attacker { actionPoints := 2 }).setPool defender { resources := 1 }
  let (withFirst, first) ← cPlace funded attacker .hand ⟨"WTR_203_R"⟩
  let (withSecond, second) ← cPlace withFirst attacker .hand ⟨"WTR_203_R"⟩
  let (withFlic, flic) ← cPlace withSecond defender .hand cid
  let (withCombo, combo) ← cPlace withFlic defender .hand ⟨"WTR_104_R"⟩
  let (withGeneric, genericBlock) ← cPlace withCombo defender .hand ⟨"WTR_205_B"⟩
  let (ready, reaction) ← cPlace withGeneric defender .hand ⟨"WTR_126_R"⟩
  let play id : Action := ⟨.player attacker, .playCard id⟩
  let block id : Action := ⟨.player defender, .defendCard id⟩
  let react id : Action := ⟨.player defender, .playCard id⟩
  let done : Action := ⟨.player defender, .defendDone⟩
  let firstPass : Action := ⟨.player attacker, .pass⟩
  let secondPass : Action := ⟨.player defender, .pass⟩
  let start (s : GameState) id := cSteps s (play id :: (passBoth ++ passBoth))
  let values (s : GameState) := (s.combat.bind CombatChain.activeLink?).map fun link =>
    link.defending.filterMap (objEffectiveDefense s)
  let firstDefense ← start ready first
  let added ← cSteps firstDefense (done :: (passBoth ++ [firstPass, react flic, secondPass, firstPass]))
  let firstClosed ← cSteps added (passBoth ++ passBoth ++ passBoth)
  let secondDefense ← start firstClosed second
  let comboFirst ← cSteps secondDefense [block combo, block genericBlock]
  let comboSecond ← cSteps secondDefense [block genericBlock, block combo]
  let reply ← cSteps secondDefense (done :: (passBoth ++ [firstPass, react reaction, secondPass, firstPass]))
  let (expired, _) ← (advance 64 { firstClosed with pending := [.endTurnCleanup attacker] } []).toOption
  pure (card.status == .full && card.front.pitch == some pitch && card.front.defense == some defense &&
    values added == some [Int.ofNat defense] && added.activeEffects.length == 1 &&
    firstClosed.combat.isNone && firstClosed.activeEffects == added.activeEffects &&
    values comboFirst == some [5, 3] && comboFirst.activeEffects.length == 1 &&
    values comboSecond == some [3, 3] && comboSecond.activeEffects.isEmpty &&
    reply.activeEffects.isEmpty && expired.activeEffects.isEmpty)

#guard checkFlicFlak ⟨"WTR_092_R"⟩ 1 4 == some true

#guard checkFlicFlak ⟨"WTR_093_Y"⟩ 2 3 == some true

#guard checkFlicFlak ⟨"WTR_094_B"⟩ 3 2 == some true

/-- A paid discard queues the Club's one power bonus for the turn (CR 6.6). -/
meta def checkRompingClub : Option Bool := do
  let attacker : PlayerId := ⟨0⟩
  let defender : PlayerId := ⟨1⟩
  let cid : CardId := ⟨"WTR_003"⟩
  let funded := m5Base.setPool attacker { actionPoints := 3, resources := 4 }
  let card ← funded.cards.find? cid
  let (armed, club) ← cPlace funded attacker .weapon cid
  let (withSwing, swing) ← cPlace armed attacker .hand ⟨"WTR_020_R"⟩
  let (qualified, _) ← cPlace withSwing attacker .hand ⟨"WTR_189_Y"⟩
  let (below, _) ← cPlace withSwing attacker .hand ⟨"WTR_190_B"⟩
  let play id : Action := ⟨.player attacker, .playCard id⟩
  let attack : Action := ⟨.player attacker, .attackWeapon club⟩
  let resolve := passBoth ++ passBoth ++ [⟨.player defender, .defendDone⟩] ++
    passBoth ++ passBoth ++ passBoth
  let unqualified ← cSteps below [play swing]
  let paid ← cSteps qualified [play swing]
  let trigger ← paid.pendingTriggers.head?
  let enhanced ← cSteps paid ([⟨.player attacker, .pickTriggerStart attacker⟩,
    ⟨.player attacker, .pickTrigger trigger.id⟩] ++ passBoth)
  let cardHit ← cSteps enhanced resolve
  let closed ← cSteps cardHit passBoth
  let (withSecondSwing, secondSwing) ← cPlace closed attacker .hand ⟨"WTR_020_R"⟩
  let (withSecondDiscard, _) ← cPlace withSecondSwing attacker .hand ⟨"WTR_189_Y"⟩
  let paidAgain ← cSteps withSecondDiscard [play secondSwing]
  let secondCardHit ← cSteps paidAgain resolve
  let beforeClub ← cSteps secondCardHit passBoth
  let clubHit ← cSteps beforeClub (attack :: resolve)
  let hitPower (s : GameState) := (s.combat.bind CombatChain.activeLink?).map (·.damageDealt)
  let (expired, _) ← (advance 64 { beforeClub with pending := [.endTurnCleanup attacker] } []).toOption
  pure (card.status == .full && card.front.power == some 4 &&
    unqualified.pendingTriggers.isEmpty && unqualified.triggeredThisTurn.isEmpty &&
    objEffectivePower paid club == some 4 && trigger.source == club &&
    paid.pendingTriggers.length == 1 && paid.triggeredThisTurn == [(club, 1)] &&
    enhanced.activatedThisTurn.isEmpty && objEffectivePower enhanced club == some 5 &&
    hitPower cardHit == some 7 && paidAgain.pendingTriggers.isEmpty &&
    paidAgain.triggeredThisTurn == paid.triggeredThisTurn &&
    objEffectivePower paidAgain club == some 5 && hitPower clubHit == some 5 &&
    clubHit.activatedThisTurn == [(club, 0)] &&
    (clubHit.poolOf attacker).resources == 0 && expired.triggeredThisTurn.isEmpty &&
    objEffectivePower expired club == some 4)

/-- An opposing effect can trigger the Club, even when two qualifying cards are discarded together. -/
meta def checkRompingClubEffectDiscard : Option Bool := do
  let attacker : PlayerId := ⟨0⟩
  let defender : PlayerId := ⟨1⟩
  let funded := m5Base.setPool attacker { actionPoints := 1, resources := 7 }
  let (armed, club) ← cPlace funded defender .weapon ⟨"WTR_003"⟩
  let (withAttack, crush) ← cPlace armed attacker .hand ⟨"WTR_043_R"⟩
  let (withFirst, _) ← cPlace withAttack defender .hand ⟨"WTR_188_R"⟩
  let (ready, _) ← cPlace withFirst defender .hand ⟨"WTR_189_Y"⟩
  let crushed ← cSteps ready ([⟨.player attacker, .playCard crush⟩] ++ passBoth ++ passBoth ++
    [⟨.player defender, .defendDone⟩] ++ passBoth ++ passBoth)
  let discard ← crushed.pendingTriggers.head?
  let discarded ← cSteps crushed ([⟨.player attacker, .pickTriggerStart attacker⟩,
    ⟨.player attacker, .pickTrigger discard.id⟩] ++ passBoth)
  let boost ← discarded.pendingTriggers.head?
  let resolved ← cSteps discarded ([⟨.player attacker, .pickTriggerStart defender⟩,
    ⟨.player defender, .pickTrigger boost.id⟩] ++ passBoth)
  pure (discard.controller == attacker && boost.source == club && boost.controller == defender &&
    (discarded.zone (.player defender .graveyard)).length == 2 &&
    discarded.pendingTriggers.length == 1 && discarded.triggeredThisTurn == [(club, 1)] &&
    objEffectivePower discarded club == some 4 && objEffectivePower resolved club == some 5)

#guard checkRompingClub == some true
#guard checkRompingClubEffectDiscard == some true

/-- Rhinar intimidates a declared hero for each qualifying discard during his action phase. -/
meta def checkRhinar (cid : CardId) (life : Nat) : Option Bool := do
  let player : PlayerId := ⟨0⟩
  let opponent : PlayerId := ⟨1⟩
  let funded := m5Base.setPool player { actionPoints := 2, resources := 2 }
  let card ← funded.cards.find? cid
  let (withHero, hero) ← cPlace (funded.setLife player (Int.ofNat life)) player .hero cid
  let (withFirst, first) ← cPlace withHero player .hand ⟨"WTR_020_R"⟩
  let (withGuard, guard) ← cPlace withFirst opponent .hand ⟨"WTR_203_R"⟩
  let (withOtherGuard, otherGuard) ← cPlace withGuard opponent .hand ⟨"WTR_204_Y"⟩
  let (ready, _) ← cPlace withOtherGuard player .hand ⟨"WTR_189_Y"⟩
  let (lowPower, _) ← cPlace withOtherGuard player .hand ⟨"WTR_190_B"⟩
  let play id : Action := ⟨.player player, .playCard id⟩
  let order : Action := ⟨.player player, .pickTriggerStart player⟩
  let target tid p : Action := ⟨.player player, .pickTrigger tid (some p)⟩
  let finishCombat := passBoth ++ passBoth ++ [⟨.player opponent, .defendDone⟩] ++
    passBoth ++ passBoth ++ passBoth ++ passBoth
  let hand := Zone.player opponent .hand
  let banished := Zone.player opponent .banished
  let rejected ← cSteps lowPower [play first]
  let paid ← cSteps ready [play first]
  let firstTrigger ← paid.pendingTriggers.head?
  let choosing ← cSteps paid [order]
  let (stacked, targetEvents) ← (step 64 choosing (target firstTrigger.id opponent)).toOption
  let triggerLayer ← (stacked.zone .stack).head?
  let chance ← cSteps stacked passBoth
  let (intimidated, banishEvents) ← (step 64 chance ⟨.chance, .shuffleOrder [guard, otherGuard]⟩).toOption
  let hidden ← (intimidated.zone banished).head?
  let closed ← cSteps intimidated finishCombat
  let (withSecond, second) ← cPlace closed player .hand ⟨"WTR_020_R"⟩
  let (withSecondCost, _) ← cPlace withSecond player .hand ⟨"WTR_189_Y"⟩
  let paidAgain ← cSteps withSecondCost [play second]
  let secondTrigger ← paidAgain.pendingTriggers.head?
  let intimidatedAgain ← cSteps paidAgain ([order, target secondTrigger.id opponent] ++ passBoth)
  let atEnd ← cSteps intimidatedAgain (finishCombat ++ passBoth)
  let firstReturn ← atEnd.pendingTriggers[0]?
  let secondReturn ← atEnd.pendingTriggers[1]?
  let returned ← cSteps atEnd [order, ⟨.player player, .pickTrigger firstReturn.id⟩,
    ⟨.player player, .pickTrigger secondReturn.id⟩]
  let (offTurnHero, _) ← cPlace (m5Base.setPool player { actionPoints := 1, resources := 7 })
    opponent .hero cid
  let (withCrush, crush) ← cPlace offTurnHero player .hand ⟨"WTR_043_R"⟩
  let (offTurn, _) ← cPlace withCrush opponent .hand ⟨"WTR_189_Y"⟩
  let crushed ← cSteps offTurn ([play crush] ++ passBoth ++ passBoth ++
    [⟨.player opponent, .defendDone⟩] ++ passBoth ++ passBoth)
  let discard ← crushed.pendingTriggers.head?
  let discarded ← cSteps crushed ([order, ⟨.player player, .pickTrigger discard.id⟩] ++ passBoth)
  let cards (s : GameState) (z : Zone) := (s.zone z).filterMap fun id => (s.cardDefOf? id).map (·.id)
  pure (card.status == .full && card.front.life == some life && card.front.intellect == some 4 &&
    rejected.pendingTriggers.isEmpty && paid.pendingTriggers.length == 1 && firstTrigger.source == hero &&
    paid.combat.isNone && !(legalActionsFor player choosing).contains ⟨.player player, .pickTrigger firstTrigger.id⟩ &&
    (legalActionsFor player choosing).contains (target firstTrigger.id player) &&
    (legalActionsFor player choosing).contains (target firstTrigger.id opponent) &&
    (step 64 choosing (target firstTrigger.id ⟨2⟩)).toOption.isNone &&
    targetEvents == [.targetedHero triggerLayer opponent] && chance.pending.head? == some (.chanceShuffle hand) &&
    intimidated.zone hand == [otherGuard] && (intimidated.obj? hidden).any (·.faceDown) &&
    banishEvents.contains (.banished opponent hidden true) && intimidated.delayedTriggers.length == 1 &&
    paidAgain.pendingTriggers.length == 1 && secondTrigger.source == hero && secondTrigger.id != firstTrigger.id &&
    intimidatedAgain.zone hand == [] && (intimidatedAgain.zone banished).length == 2 &&
    atEnd.pendingTriggers.length == 2 && returned.zone banished == [] &&
    (cards returned hand).length == 2 &&
    (cards returned hand).contains ⟨"WTR_203_R"⟩ && (cards returned hand).contains ⟨"WTR_204_Y"⟩ &&
    (discarded.zone (.player opponent .graveyard)).length == 1 && discarded.pendingTriggers.isEmpty)

#guard checkRhinar ⟨"WTR_001"⟩ 40 == some true

#guard checkRhinar ⟨"WTR_002"⟩ 20 == some true

/-- Mask of Momentum cares about the current hit streak, the hitting card, and its own use limit. -/
meta def checkMaskOfMomentum : Option Bool := do
  let attacker : PlayerId := ⟨0⟩
  let defender : PlayerId := ⟨1⟩
  let cid : CardId := ⟨"WTR_079"⟩
  let card ← m5Base.cards.find? cid
  let funded := m5Base.setPool attacker { actionPoints := 1, resources := 1 }
  let (equipped, mask) ← cPlace funded attacker .head cid
  let (withWeapon, weapon) ← cPlace equipped attacker .weapon ⟨"WTR_078"⟩
  let (withPitch, _) ← cPlace withWeapon attacker .pitch ⟨"WTR_203_R"⟩
  let (withFirst, first) ← cPlace withPitch attacker .hand ⟨"WTR_098_R"⟩
  let (withSecond, second) ← cPlace withFirst attacker .hand ⟨"WTR_098_R"⟩
  let (withThird, third) ← cPlace withSecond attacker .hand ⟨"WTR_098_R"⟩
  let (withFourth, fourth) ← cPlace withThird attacker .hand ⟨"WTR_098_R"⟩
  let (withDeck, top) ← cPlace withFourth attacker .deck ⟨"WTR_203_R"⟩
  let (ready, block) ← cPlace withDeck defender .hand ⟨"WTR_203_R"⟩
  let play id : Action := ⟨.player attacker, .playCard id⟩
  let swing : Action := ⟨.player attacker, .attackWeapon weapon⟩
  let enter (s : GameState) (a : Action) := cSteps s (a :: (passBoth ++ passBoth))
  let toDamage := [⟨.player defender, .defendDone⟩] ++ passBoth ++ passBoth
  let firstDefend ← enter ready (play first)
  let firstHit ← cSteps firstDefend (toDamage ++ passBoth)
  let secondDefend ← enter firstHit (play second)
  let secondHit ← cSteps secondDefend (toDamage ++ passBoth)
  let secondMiss ← cSteps secondDefend
    ([⟨.player defender, .defendCard block⟩] ++ toDamage ++ passBoth)
  let afterMiss ← enter secondMiss (play third)
  let brokenStreak ← cSteps afterMiss (toDamage ++ passBoth)
  let thirdDefend ← enter secondHit (play third)
  let thirdHit ← cSteps thirdDefend toDamage
  let trigger ← thirdHit.pendingTriggers.head?
  let drawn ← cSteps thirdHit ([⟨.player attacker, .pickTriggerStart attacker⟩,
    ⟨.player attacker, .pickTrigger trigger.id⟩] ++ passBoth)
  let resumable ← cSteps drawn passBoth
  let fourthDefend ← enter resumable (play fourth)
  let fourthHit ← cSteps fourthDefend (toDamage ++ passBoth)
  let weaponDefend ← enter secondHit swing
  let weaponHit ← cSteps weaponDefend (toDamage ++ passBoth)
  let mixedDefend ← enter weaponHit (play fourth)
  let mixedHit ← cSteps mixedDefend toDamage
  let mixedTrigger ← mixedHit.pendingTriggers.head?
  let closed ← cSteps secondHit passBoth
  let newDefend ← enter closed (play third)
  let newChain ← cSteps newDefend (toDamage ++ passBoth)
  let (otherSide, otherMask) ← cPlace funded defender .head cid
  let (wearReady, wearAttack) ← cPlace otherSide attacker .hand ⟨"WTR_203_R"⟩
  let wearDefend ← enter wearReady (play wearAttack)
  let worn ← cSteps wearDefend ([⟨.player defender, .defendCard otherMask⟩] ++
    toDamage ++ passBoth ++ passBoth)
  let wornCard ← (worn.zone (.player defender .graveyard)).head?
  pure (card.status == .full && card.front.defense == some 2 && card.front.keywords.contains .bladeBreak &&
    [firstHit, secondHit, brokenStreak, weaponHit, newChain].all
      (fun s => s.pendingTriggers.isEmpty && s.triggeredThisTurn.isEmpty && s.zone (.player attacker .deck) == [top]) &&
    thirdHit.pendingTriggers.length == 1 && trigger.source == mask &&
    thirdHit.zone (.player attacker .deck) == [top] && drawn.zone (.player attacker .deck) == [] &&
    (drawn.zone (.player attacker .hand)).length == 2 &&
    fourthHit.pendingTriggers.isEmpty && fourthHit.triggeredThisTurn == [(mask, 0)] &&
    mixedHit.pendingTriggers.length == 1 && mixedTrigger.source == mask &&
    worn.zone (.player defender .head) == [] && (worn.cardDefOf? wornCard).map (·.id) == some cid)

#guard checkMaskOfMomentum == some true

/-- Refraction Bolters is optional on a weapon hit and its Go Again only grants one action point. -/
meta def checkRefractionBolters : Option Bool := do
  let attacker : PlayerId := ⟨0⟩
  let defender : PlayerId := ⟨1⟩
  let cid : CardId := ⟨"WTR_117"⟩
  let card ← m5Base.cards.find? cid
  let funded := m5Base.setPool attacker { actionPoints := 1, resources := 1 }
  let (equipped, bolters) ← cPlace funded attacker .legs cid
  let (withWeapon, weapon) ← cPlace equipped attacker .weapon ⟨"WTR_115"⟩
  let (withBlock, block) ← cPlace withWeapon defender .hand ⟨"WTR_203_R"⟩
  let (withReaction, glint) ← cPlace withBlock attacker .hand ⟨"WTR_118_B"⟩
  let (ready, cardAttack) ← cPlace withReaction attacker .hand ⟨"WTR_203_R"⟩
  let play id : Action := ⟨.player attacker, .playCard id⟩
  let swing : Action := ⟨.player attacker, .attackWeapon weapon⟩
  let enter (s : GameState) (a : Action) := cSteps s (a :: (passBoth ++ passBoth))
  let done : Action := ⟨.player defender, .defendDone⟩
  let toDamage := done :: (passBoth ++ passBoth)
  let prompt (s : GameState) (tid : Nat) :=
    cSteps s ([⟨.player attacker, .pickTriggerStart attacker⟩, ⟨.player attacker, .pickTrigger tid⟩] ++ passBoth)
  let accept yes : Action := ⟨.player attacker, .pickMay yes⟩
  let legs := Zone.player attacker .legs
  let grave := Zone.player attacker .graveyard
  let hasGoAgain (s : GameState) :=
    (s.combat.bind CombatChain.activeLink?).any fun link => linkHasKeyword s link .goAgain
  let defending ← enter ready swing
  let hit ← cSteps defending toDamage
  let trigger ← hit.pendingTriggers.head?
  let choice ← prompt hit trigger.id
  let (destroyed, es) ← (step 64 choice (accept true)).toOption
  let spent ← (destroyed.zone grave).head?
  let finished ← cSteps destroyed passBoth
  let declined ← cSteps choice (accept false :: passBoth)
  let (removed, _) ← moveObj hit bolters grave .top false
  let sourceGone ← prompt removed trigger.id
  let goneFinished ← cSteps sourceGone passBoth
  let blocked ← cSteps defending (⟨.player defender, .defendCard block⟩ :: (toDamage ++ passBoth))
  let genericDefend ← enter ready (play cardAttack)
  let genericHit ← cSteps genericDefend (toDamage ++ passBoth)
  let reaction ← cSteps defending (done :: passBoth)
  let glintPaid ← cSteps reaction [play glint]
  let priorGoAgain ← cSteps glintPaid passBoth
  let secondHit ← cSteps priorGoAgain passBoth
  let secondTrigger ← secondHit.pendingTriggers.head?
  let secondChoice ← prompt secondHit secondTrigger.id
  let twiceGranted ← cSteps secondChoice (accept true :: passBoth)
  let (otherSide, otherBolters) ← cPlace funded defender .legs cid
  let (wearReady, wearAttack) ← cPlace otherSide attacker .hand ⟨"WTR_203_R"⟩
  let wearDefend ← enter wearReady (play wearAttack)
  let worn ← cSteps wearDefend ([⟨.player defender, .defendCard otherBolters⟩] ++
    toDamage ++ passBoth ++ passBoth)
  pure (card.status == .full && card.front.defense == some 1 && card.front.keywords.contains .battleworn &&
    hit.pendingTriggers.length == 1 && trigger.source == bolters && !hasGoAgain hit &&
    (legalActionsFor attacker choice).contains (accept true) &&
    (legalActionsFor attacker choice).contains (accept false) &&
    destroyed.zone legs == [] && es.contains (.moved bolters spent legs grave) &&
    (destroyed.cardDefOf? spent).map (·.id) == some cid &&
    hasGoAgain finished && (finished.poolOf attacker).actionPoints == 1 &&
    declined.zone legs == [bolters] && !hasGoAgain declined && (declined.poolOf attacker).actionPoints == 0 &&
    sourceGone.pending.head? == some (.priority attacker 0) &&
    !hasGoAgain goneFinished && (goneFinished.poolOf attacker).actionPoints == 0 &&
    blocked.pendingTriggers.isEmpty && genericHit.pendingTriggers.isEmpty &&
    hasGoAgain priorGoAgain && (twiceGranted.poolOf attacker).actionPoints == 1 &&
    worn.zone (.player defender .legs) == [otherBolters] &&
    (worn.obj? otherBolters).any (fun obj => obj.minusDefenseCounters == 1))

#guard checkRefractionBolters == some true

/-- Dorinthea can permit one extra attack with the weapon that hit, independently of action points. -/
meta def checkDorinthea (cid : CardId) (life : Nat) : Option Bool := do
  let attacker : PlayerId := ⟨0⟩
  let defender : PlayerId := ⟨1⟩
  let card ← m5Base.cards.find? cid
  let funded := (m5Base.setLife attacker (Int.ofNat life)).setPool attacker { actionPoints := 2, resources := 2 }
  let (withHero, hero) ← cPlace funded attacker .hero cid
  let (armed, weapon) ← cPlace withHero attacker .weapon ⟨"WTR_115"⟩
  let (withBlock, block) ← cPlace armed defender .hand ⟨"WTR_203_R"⟩
  let (ready, _) ← cPlace withBlock attacker .hand ⟨"WTR_203_R"⟩
  let swing : Action := ⟨.player attacker, .attackWeapon weapon⟩
  let enter (s : GameState) := cSteps s (swing :: (passBoth ++ passBoth))
  let done : Action := ⟨.player defender, .defendDone⟩
  let accept yes : Action := ⟨.player attacker, .pickMay yes⟩
  let toDamage := done :: (passBoth ++ passBoth)
  let defend ← enter ready
  let hit ← cSteps defend toDamage
  let trigger ← hit.pendingTriggers.head?
  let choice ← cSteps hit ([⟨.player attacker, .pickTriggerStart attacker⟩,
    ⟨.player attacker, .pickTrigger trigger.id⟩] ++ passBoth)
  let permitted ← cSteps choice (accept true :: passBoth)
  let declined ← cSteps choice (accept false :: passBoth)
  let (expired, _) ← (advance 64 { permitted with pending := [.endTurnCleanup attacker] } []).toOption
  let broke := permitted.setPool attacker { actionPoints := 1 }
  let paying ← cSteps broke [swing]
  let cancelled ← cSteps paying [⟨.player attacker, .cancelPlay⟩]
  let secondDefend ← enter permitted
  let secondDamage ← cSteps secondDefend toDamage
  let swordTrigger ← secondDamage.pendingTriggers.head?
  let second ← cSteps secondDamage ([⟨.player attacker, .pickTriggerStart attacker⟩,
    ⟨.player attacker, .pickTrigger swordTrigger.id⟩] ++ passBoth ++ passBoth)
  let extraFunded := second.setPool attacker { actionPoints := 1, resources := 1 }
  let blocked ← cSteps defend (⟨.player defender, .defendCard block⟩ :: (toDamage ++ passBoth))
  pure (card.status == .full && card.front.life == some life && card.front.intellect == some 4 &&
    hit.pendingTriggers.length == 1 && trigger.source == hero &&
    (legalActionsFor attacker choice).contains (accept true) &&
    (legalActionsFor attacker choice).contains (accept false) &&
    (permitted.poolOf attacker).actionPoints == 1 && (permitted.poolOf attacker).resources == 1 &&
    (legalActionsFor attacker permitted).contains swing &&
    !(legalActionsFor attacker declined).contains swing && declined.activeEffects.isEmpty &&
    expired.activeEffects.isEmpty && expired.triggeredThisTurn.isEmpty &&
    decide (cancelled = broke) && permitted.activeEffects.map (·.target) == [.obj weapon] &&
    secondDefend.activeEffects.isEmpty && (secondDefend.combat.map (·.links.length)) == some 2 &&
    secondDamage.pendingTriggers.length == 1 && swordTrigger.source == weapon &&
    second.pendingTriggers.isEmpty && second.triggeredThisTurn == [(hero, 0)] &&
    !(legalActionsFor attacker extraFunded).contains swing && (step 64 extraFunded swing).toOption.isNone &&
    blocked.pendingTriggers.isEmpty && blocked.triggeredThisTurn.isEmpty)

#guard checkDorinthea ⟨"WTR_113"⟩ 40 == some true

#guard checkDorinthea ⟨"WTR_114"⟩ 20 == some true

/-- Dawnblade's second hit and its counter retention both use the whole turn, across chains. -/
meta def checkDawnblade : Option Bool := do
  let attacker : PlayerId := ⟨0⟩
  let defender : PlayerId := ⟨1⟩
  let cid : CardId := ⟨"WTR_115"⟩
  let card ← m5Base.cards.find? cid
  let funded := m5Base.setPool attacker { actionPoints := 2, resources := 2 }
  let (withHero, hero) ← cPlace funded attacker .hero ⟨"WTR_113"⟩
  let (ready, sword) ← cPlace withHero attacker .weapon cid
  let swing : Action := ⟨.player attacker, .attackWeapon sword⟩
  let order : Action := ⟨.player attacker, .pickTriggerStart attacker⟩
  let choose tid : Action := ⟨.player attacker, .pickTrigger tid⟩
  let toDamage := [⟨.player defender, .defendDone⟩] ++ passBoth ++ passBoth
  let swingToDamage (s : GameState) := cSteps s (swing :: (passBoth ++ passBoth ++ toDamage))
  let first ← swingToDamage ready
  let permitTrigger ← first.pendingTriggers.head?
  let optional ← cSteps first ([order, choose permitTrigger.id] ++ passBoth)
  let firstClosed ← cSteps optional (⟨.player attacker, .pickMay true⟩ :: (passBoth ++ passBoth))
  let second ← swingToDamage firstClosed
  let counterTrigger ← second.pendingTriggers.head?
  let enhanced ← cSteps second ([order, choose counterTrigger.id] ++ passBoth)
  let secondClosed ← cSteps enhanced (passBoth ++ passBoth)
  let hitEnding ← cSteps secondClosed passBoth
  let retainTrigger ← hitEnding.pendingTriggers.head?
  let hitEnd ← cSteps hitEnding [order, choose retainTrigger.id]
  let nextTurn := { hitEnd with phase := .actionPhase, pending := [.priority attacker 0, .endPhaseStart attacker] }
  let retry := nextTurn.setPool attacker { actionPoints := 1, resources := 1 }
  let (withBlock, firstBlock) ← cPlace retry defender .hand ⟨"WTR_203_R"⟩
  let (blocking, secondBlock) ← cPlace withBlock defender .hand ⟨"WTR_204_Y"⟩
  let expectedMiss ← cSteps blocking (swing :: (passBoth ++ passBoth ++
    [⟨.player defender, .defendCard firstBlock⟩, ⟨.player defender, .defendCard secondBlock⟩] ++
    toDamage ++ passBoth ++ passBoth))
  let missedEnd ← cSteps expectedMiss passBoth
  let removeTrigger ← missedEnd.pendingTriggers.head?
  let cleared ← cSteps missedEnd [order, choose removeTrigger.id]
  let opposingEnd := { hitEnd with
    active := some defender
    phase := .actionPhase
    pending := [.endPhaseStart defender] }
  let (opponentFinished, _) ← (advance 64 opposingEnd []).toOption
  pure (card.status == .full && card.front.power == some 3 && permitTrigger.source == hero &&
    first.pendingTriggers.length == 1 && first.weaponHitsThisTurn == [sword] &&
    objEffectivePower firstClosed sword == some 3 && firstClosed.combat.isNone &&
    second.pendingTriggers.length == 1 && counterTrigger.source == sword &&
    second.weaponHitsThisTurn == [sword, sword] && objEffectivePower enhanced sword == some 4 &&
    secondClosed.combat.isNone && hitEnd.pendingTriggers.isEmpty &&
    hitEnd.weaponHitsThisTurn.isEmpty && objEffectivePower hitEnd sword == some 4 &&
    expectedMiss.weaponHitsThisTurn.isEmpty && expectedMiss.combat.isNone &&
    missedEnd.pendingTriggers.length == 1 && removeTrigger.source == sword &&
    objEffectivePower cleared sword == some 3 &&
    opponentFinished.pendingTriggers.isEmpty && objEffectivePower opponentFinished sword == some 4)

#guard checkDawnblade == some true

/-- Braveforge Bracers rewards a weapon hit once per turn and buffs the next weapon only. -/
meta def checkBraveforgeBracers : Option Bool := do
  let attacker : PlayerId := ⟨0⟩
  let defender : PlayerId := ⟨1⟩
  let cid : CardId := ⟨"WTR_116"⟩
  let card ← m5Base.cards.find? cid
  let funded := m5Base.setPool attacker { actionPoints := 3, resources := 4 }
  let (equipped, bracers) ← cPlace funded attacker .arms cid
  let (withDagger, first) ← cPlace equipped attacker .weapon ⟨"WTR_078"⟩
  let (withTwo, second) ← cPlace withDagger attacker .weapon ⟨"WTR_078"⟩
  let (withBlock, block) ← cPlace withTwo defender .hand ⟨"WTR_205_B"⟩
  let (withArmor, defendingBracers) ← cPlace withBlock defender .arms cid
  let (ready, attack) ← cPlace withArmor attacker .hand ⟨"WTR_203_R"⟩
  let activate : Action := ⟨.player attacker, .activateAbility bracers 0⟩
  let swing (id : ObjId) : Action := ⟨.player attacker, .attackWeapon id⟩
  let play : Action := ⟨.player attacker, .playCard attack⟩
  let defend (id : ObjId) : Action := ⟨.player defender, .defendCard id⟩
  let enter := passBoth ++ passBoth
  let fight := [⟨.player defender, .defendDone⟩] ++ passBoth ++ passBoth ++ passBoth
  let firstSwing ← cSteps ready (swing first :: enter)
  let blocked ← cSteps firstSwing (defend block :: (fight ++ passBoth))
  let hit ← cSteps firstSwing (fight ++ passBoth)
  let ordinaryHit ← cSteps ready (play :: (enter ++ fight ++ passBoth))
  let worn ← cSteps ready (play :: (enter ++ [defend defendingBracers] ++ fight ++ passBoth))
  let paid ← cSteps hit [activate]
  let buffed ← cSteps paid passBoth
  let afterCard ← cSteps buffed (play :: (enter ++ fight ++ passBoth))
  let enhanced ← cSteps afterCard (swing second :: (enter ++ fight))
  let link ← enhanced.combat.bind CombatChain.activeLink?
  pure (card.status == .full && card.front.defense == some 2 && card.front.keywords.contains .battleworn &&
    !(legalActionsFor attacker ready).contains activate &&
    !(legalActionsFor attacker blocked).contains activate &&
    !(legalActionsFor attacker ordinaryHit).contains activate &&
    (legalActionsFor attacker hit).contains activate && hit.weaponHitsThisTurn == [first] &&
    (paid.poolOf attacker).actionPoints == 1 && (paid.poolOf attacker).resources == 2 &&
    (buffed.poolOf attacker).actionPoints == 2 &&
    buffed.activeEffects.map (·.target) == [.nextAttack CardFilter.weaponAttack] &&
    !(legalActionsFor attacker buffed).contains activate && (step 64 buffed activate).toOption.isNone &&
    afterCard.lifeOf defender == 35 && afterCard.activeEffects == buffed.activeEffects &&
    link.attackSource == some second && link.damageDealt == 2 && enhanced.activeEffects.isEmpty &&
    worn.zone (.player defender .arms) == [defendingBracers] &&
    objEffectiveDefense worn defendingBracers == some 1)

#guard checkBraveforgeBracers == some true

/-- Heartened Cross Strap pays for up to two resources of the next attack action card. -/
meta def checkHeartenedCrossStrap : Option Bool := do
  let player : PlayerId := ⟨0⟩
  let opponent : PlayerId := ⟨1⟩
  let cid : CardId := ⟨"WTR_152"⟩
  let slot := Zone.player player .chest
  let grave := Zone.player player .graveyard
  let funded := m5Base.setPool player { actionPoints := 1, resources := 1 }
  let card ← funded.cards.find? cid
  let (equipped, source) ← cPlace funded player .chest cid
  let (withWeapon, weapon) ← cPlace equipped player .weapon ⟨"WTR_078"⟩
  let (withCheap, cheap) ← cPlace withWeapon player .hand ⟨"WTR_107_R"⟩
  let (withExtra, expensive) ← cPlace withCheap player .hand ⟨"WTR_200_R"⟩
  let (ready, zeroCost) ← cPlace withExtra player .hand ⟨"WTR_098_R"⟩
  let activate : Action := ⟨.player player, .activateAbility source 0⟩
  let play id : Action := ⟨.player player, .playCard id⟩
  let (paid, events) ← (step 64 ready activate).toOption
  let spent ← (paid.zone grave).head?
  let reduced ← cSteps paid passBoth
  let weaponPaid ← cSteps reduced [⟨.player player, .attackWeapon weapon⟩]
  let cheapPaid ← cSteps reduced [play cheap]
  let expensivePaid ← cSteps reduced [play expensive]
  let zeroPaid ← cSteps reduced [play zeroCost]
  let afterFight ← cSteps cheapPaid
    (passBoth ++ passBoth ++ [⟨.player opponent, .defendDone⟩] ++ passBoth ++ passBoth ++ passBoth)
  let second ← cSteps afterFight [play expensive]
  let canceled ← cSteps second [⟨.player player, .cancelPlay⟩]
  let ended ← cSteps reduced (passBoth ++ [⟨.player player, .arsenalSkip⟩])
  pure (card.status == .full && card.front.defense == some 0 &&
    paid.zone slot == [] && events.contains (.moved source spent slot grave) &&
    (paid.cardDefOf? spent).map (·.id) == some cid && (paid.poolOf player).actionPoints == 0 &&
    paid.activeEffects.isEmpty && (reduced.poolOf player).actionPoints == 1 &&
    reduced.activeEffects.length == 1 &&
    (weaponPaid.poolOf player).resources == 0 && weaponPaid.activeEffects == reduced.activeEffects &&
    (cheapPaid.poolOf player).resources == 1 && cheapPaid.activeEffects.isEmpty &&
    (expensivePaid.poolOf player).resources == 0 && expensivePaid.activeEffects.isEmpty &&
    (zeroPaid.poolOf player).resources == 1 && zeroPaid.activeEffects.isEmpty &&
    (afterFight.poolOf player).actionPoints == 1 && second.playRollback.isSome &&
    decide (canceled = afterFight) &&
    ended.activeEffects.isEmpty && (ended.poolOf player).actionPoints == 0)

#guard checkHeartenedCrossStrap == some true

/-- Goliath Gauntlet waits for a paid attack action card with a cost of at least two. -/
meta def checkGoliathGauntlet : Option Bool := do
  let player : PlayerId := ⟨0⟩
  let opponent : PlayerId := ⟨1⟩
  let cid : CardId := ⟨"WTR_153"⟩
  let slot := Zone.player player .arms
  let grave := Zone.player player .graveyard
  let funded := m5Base.setPool player { actionPoints := 1, resources := 7 }
  let card ← funded.cards.find? cid
  let (equipped, source) ← cPlace funded player .arms cid
  let (withWeapon, weapon) ← cPlace equipped player .weapon ⟨"WTR_078"⟩
  let (withCheap, cheap) ← cPlace withWeapon player .hand ⟨"WTR_101_R"⟩
  let (withFirst, first) ← cPlace withCheap player .hand ⟨"WTR_107_R"⟩
  let (ready, second) ← cPlace withFirst player .hand ⟨"WTR_107_R"⟩
  let activate : Action := ⟨.player player, .activateAbility source 0⟩
  let fight (s : GameState) (id : ObjId) := cSteps s
    ([⟨.player player, .playCard id⟩] ++ passBoth ++ passBoth ++
      [⟨.player opponent, .defendDone⟩] ++ passBoth ++ passBoth ++ passBoth)
  let (paid, events) ← (step 64 ready activate).toOption
  let spent ← (paid.zone grave).head?
  let buffed ← cSteps paid passBoth
  let afterWeapon ← cSteps buffed [⟨.player player, .attackWeapon weapon⟩]
  let afterCheap ← fight buffed cheap
  let boosted ← fight afterCheap first
  let normal ← fight boosted second
  let expired ← cSteps buffed (passBoth ++ [⟨.player player, .arsenalSkip⟩])
  let powerBonus (s : GameState) := (s.combat.bind CombatChain.activeLink?).map (·.powerBonus)
  pure (card.status == .full && card.front.defense == some 0 &&
    paid.zone slot == [] && events.contains (.moved source spent slot grave) &&
    (paid.cardDefOf? spent).map (·.id) == some cid && (paid.poolOf player).actionPoints == 0 &&
    paid.activeEffects.isEmpty && (buffed.poolOf player).actionPoints == 1 &&
    buffed.activeEffects.length == 1 &&
    afterWeapon.activeEffects == buffed.activeEffects && afterCheap.activeEffects == buffed.activeEffects &&
    powerBonus afterCheap == some 0 && powerBonus boosted == some 2 && powerBonus normal == some 0 &&
    afterCheap.lifeOf opponent == 36 && boosted.lifeOf opponent == 29 && normal.lifeOf opponent == 24 &&
    boosted.activeEffects.isEmpty && expired.activeEffects.isEmpty)

#guard checkGoliathGauntlet == some true

/-- Breaking Scales gives +1 power to a Combo card, even without its Combo predecessor. -/
meta def checkBreakingScales : Option Bool := do
  let attacker : PlayerId := ⟨0⟩
  let defender : PlayerId := ⟨1⟩
  let cid : CardId := ⟨"WTR_080"⟩
  let arms := Zone.player attacker .arms
  let grave := Zone.player attacker .graveyard
  let funded := m5Base.setPool attacker { actionPoints := 1, resources := 1 }
  let card ← funded.cards.find? cid
  let (equipped, source) ← cPlace funded attacker .arms cid
  let (withCombo, combo) ← cPlace equipped attacker .hand ⟨"WTR_104_R"⟩
  let (ready, normal) ← cPlace withCombo attacker .hand ⟨"WTR_203_R"⟩
  let play id : Action := ⟨.player attacker, .playCard id⟩
  let done : Action := ⟨.player defender, .defendDone⟩
  let activate id : Action := ⟨.player attacker, .activateAbility source 0 (some id)⟩
  let link (s : GameState) := s.combat.bind CombatChain.activeLink?
  let enter (id : ObjId) := cSteps ready (play id :: (passBoth ++ passBoth ++ [done] ++ passBoth))
  let reacting ← enter combo
  let target ← (link reacting).bind (·.attack)
  let wrong ← enter normal
  let wrongTarget ← (link wrong).bind (·.attack)
  let (paid, events) ← (step 64 reacting (activate target)).toOption
  let layer ← (paid.zone .stack).head?
  let spent ← (paid.zone grave).head?
  let buffed ← cSteps paid passBoth
  let before ← link paid
  let after ← link buffed
  let hit ← cSteps buffed (passBoth ++ passBoth ++ passBoth)
  let (wearReady, wearSource) ← cPlace m5Base defender .arms cid
  let (withAttack, attack) ← cPlace wearReady attacker .hand ⟨"WTR_203_R"⟩
  let defending ← cSteps withAttack (play attack :: (passBoth ++ passBoth))
  let closed ← cSteps defending
    ([⟨.player defender, .defendCard wearSource⟩, done] ++ passBoth ++ passBoth ++ passBoth ++ passBoth)
  pure (card.status == .full && card.front.defense == some 1 && card.front.keywords.contains .battleworn &&
    (legalActionsFor attacker reacting).contains (activate target) &&
    (step 64 wrong (activate wrongTarget)).toOption.isNone &&
    paid.zone arms == [] && (paid.cardDefOf? spent).map (·.id) == some cid &&
    events.contains (.moved source spent arms grave) && events.contains (.targetedAttack layer target) &&
    (paid.poolOf attacker).actionPoints == 0 && (paid.poolOf attacker).resources == 1 &&
    linkAttackPower paid before == 3 && linkAttackPower buffed after == 4 &&
    hit.lifeOf defender == 36 && (hit.poolOf attacker).actionPoints == 0 &&
    closed.lifeOf defender == 37 && closed.zone (.player defender .arms) == [wearSource] &&
    (closed.obj? wearSource).map (·.minusDefenseCounters) == some 1 &&
    objEffectiveDefense closed wearSource == some 0)

#guard checkBreakingScales == some true

/-- Snapdragon Scalers grants Go Again to a legal attack action card during the reaction step. -/
meta def checkSnapdragonScalers : Option Bool := do
  let attacker : PlayerId := ⟨0⟩
  let defender : PlayerId := ⟨1⟩
  let cid : CardId := ⟨"WTR_154"⟩
  let slot := Zone.player attacker .legs
  let grave := Zone.player attacker .graveyard
  let funded := m5Base.setPool attacker { actionPoints := 1, resources := 3 }
  let card ← funded.cards.find? cid
  let (equipped, source) ← cPlace funded attacker .legs cid
  let (withOther, other) ← cPlace equipped defender .legs cid
  let (withWeapon, weapon) ← cPlace withOther attacker .weapon ⟨"WTR_078"⟩
  let (withCheap, attack) ← cPlace withWeapon attacker .hand ⟨"WTR_203_R"⟩
  let (withBoundary, boundary) ← cPlace withCheap attacker .hand ⟨"WTR_101_R"⟩
  let (ready, expensive) ← cPlace withBoundary attacker .hand ⟨"WTR_107_R"⟩
  let activate target : Action := ⟨.player attacker, .activateAbility source 0 (some target)⟩
  let play id : Action := ⟨.player attacker, .playCard id⟩
  let done : Action := ⟨.player defender, .defendDone⟩
  let enter (a : Action) := cSteps ready (a :: (passBoth ++ passBoth ++ [done] ++ passBoth))
  let defending ← cSteps ready (play attack :: (passBoth ++ passBoth))
  let reaction ← cSteps defending (done :: passBoth)
  let target ← (reaction.combat.bind CombatChain.activeLink?).bind (·.attack)
  let current (s : GameState) := (s.combat.bind CombatChain.activeLink?).bind (·.attack)
  let onBoundary ← enter (play boundary)
  let onExpensive ← enter (play expensive)
  let onWeapon ← enter ⟨.player attacker, .attackWeapon weapon⟩
  let boundaryTarget ← current onBoundary
  let expensiveTarget ← current onExpensive
  let weaponTarget ← current onWeapon
  let defenderWindow ← cSteps reaction [⟨.player attacker, .pass⟩]
  let (paid, events) ← (step 64 reaction (activate target)).toOption
  let layer ← (paid.zone .stack).head?
  let spent ← (paid.zone grave).head?
  let enhanced ← cSteps paid passBoth
  let hit ← cSteps enhanced (passBoth ++ passBoth ++ passBoth)
  let normal ← cSteps reaction (passBoth ++ passBoth ++ passBoth)
  let (missingTarget, _) ← moveObj paid target grave .top false
  let unbound ← cSteps missingTarget passBoth
  let hasGoAgain (s : GameState) :=
    (s.combat.bind CombatChain.activeLink?).any fun link => linkHasKeyword s link .goAgain
  pure (card.status == .full && card.front.defense == some 0 &&
    (step 64 ready (activate attack)).toOption.isNone && (step 64 defending (activate target)).toOption.isNone &&
    (legalActionsFor attacker reaction).contains (activate target) &&
    (step 64 reaction ⟨.player attacker, .activateAbility source 0⟩).toOption.isNone &&
    (legalActionsFor attacker onBoundary).contains (activate boundaryTarget) &&
    (step 64 onExpensive (activate expensiveTarget)).toOption.isNone &&
    (step 64 onWeapon (activate weaponTarget)).toOption.isNone &&
    (step 64 defenderWindow ⟨.player defender, .activateAbility other 0 (some target)⟩).toOption.isNone &&
    paid.zone slot == [] && events.contains (.moved source spent slot grave) &&
    events.contains (.targetedAttack layer target) && (paid.cardDefOf? spent).map (·.id) == some cid &&
    (paid.poolOf attacker).actionPoints == 0 && !hasGoAgain paid && hasGoAgain enhanced &&
    (enhanced.poolOf attacker).actionPoints == 0 && (hit.poolOf attacker).actionPoints == 1 &&
    (normal.poolOf attacker).actionPoints == 0 && !hasGoAgain unbound)

#guard checkSnapdragonScalers == some true

/-- A legal earlier or defending card can be targeted without changing the active attack. -/
meta def checkSnapdragonOtherTarget (earlier : Bool) : Option Bool := do
  let attacker : PlayerId := ⟨0⟩
  let defender : PlayerId := ⟨1⟩
  let cheap : CardId := ⟨"WTR_203_R"⟩
  let funded := m5Base.setPool attacker { actionPoints := 2, resources := 3 }
  let (equipped, source) ← cPlace funded attacker .legs ⟨"WTR_154"⟩
  let (withFirst, first) ← cPlace equipped attacker .hand cheap
  let (withNext, next) ← cPlace withFirst attacker .hand ⟨"WTR_188_R"⟩
  let (ready, block) ← cPlace withNext defender .hand cheap
  let play id : Action := ⟨.player attacker, .playCard id⟩
  let finish : Action := ⟨.player defender, .defendDone⟩
  let activate id : Action := ⟨.player attacker, .activateAbility source 0 (some id)⟩
  let link (s : GameState) := s.combat.bind CombatChain.activeLink?
  let firstDefend ← cSteps ready (play first :: (passBoth ++ passBoth))
  let prior ← (link firstDefend).bind (·.attack)
  let afterFirst ← cSteps firstDefend (finish :: (passBoth ++ passBoth ++ passBoth))
  let secondDefend ← cSteps afterFirst (play next :: (passBoth ++ passBoth))
  let reacting ← cSteps secondDefend ([⟨.player defender, .defendCard block⟩, finish] ++ passBoth)
  let active ← link reacting
  let chosen ← if earlier then some prior else active.defending.head?
  let (paid, events) ← (step 64 reacting (activate chosen)).toOption
  let layer ← (paid.zone .stack).head?
  let affected ← cSteps paid passBoth
  let current ← link affected
  let finished ← cSteps affected (passBoth ++ passBoth ++ passBoth)
  pure ((legalActionsFor attacker reacting).contains (activate prior) &&
    active.defending.all (fun id => (legalActionsFor attacker reacting).contains (activate id)) &&
    !(active.attack.any (fun id => (legalActionsFor attacker reacting).contains (activate id))) &&
    events.contains (.targetedAttack layer chosen) &&
    (affected.characteristics chosen).any (fun chars => chars.keywords.contains .goAgain) &&
    !linkHasKeyword affected current .goAgain && (finished.poolOf attacker).actionPoints == 0)

#guard checkSnapdragonOtherTarget true == some true
#guard checkSnapdragonOtherTarget false == some true

/-- Barkbone Strapping can be spent in a reaction window, including while defending. -/
meta def checkBarkboneStrapping (roll : Nat) : Option Bool := do
  let attacker : PlayerId := ⟨0⟩
  let defender : PlayerId := ⟨1⟩
  let cid : CardId := ⟨"WTR_005"⟩
  let chest := Zone.player defender .chest
  let grave := Zone.player defender .graveyard
  let card ← m5Base.cards.find? cid
  let (equipped, source) ← cPlace m5Base defender .chest cid
  let (ready, attack) ← cPlace equipped attacker .hand ⟨"WTR_203_R"⟩
  let defending ← cSteps ready
    (⟨.player attacker, .playCard attack⟩ :: (passBoth ++ passBoth))
  let block : Action := ⟨.player defender, .defendCard source⟩
  let done : Action := ⟨.player defender, .defendDone⟩
  let activate : Action := ⟨.player defender, .activateAbility source 0⟩
  let attackerPass : Action := ⟨.player attacker, .pass⟩
  let fromSlot ← cSteps defending [done, attackerPass]
  let onChain ← cSteps defending [block, done, attackerPass]
  let (paidSlot, slotEvents) ← (step 64 fromSlot activate).toOption
  let (paidChain, chainEvents) ← (step 64 onChain activate).toOption
  let slotSpent ← (paidSlot.zone grave).head?
  let chainSpent ← (paidChain.zone grave).head?
  let rolling ← cSteps paidChain passBoth.reverse
  let (resolved, _) ← (step 64 rolling ⟨.chance, .die6Roll roll⟩).toOption
  let hit ← cSteps resolved (passBoth ++ passBoth)
  let worn ← cSteps defending ([block, done] ++ passBoth ++ passBoth ++ passBoth ++ passBoth)
  pure (card.status == .full && card.front.defense == some 1 && card.front.keywords.contains .battleworn &&
    (step 64 defending activate).toOption.isNone &&
    (legalActionsFor defender fromSlot).contains activate &&
    (legalActionsFor defender onChain).contains activate &&
    slotEvents.contains (.moved source slotSpent chest grave) &&
    chainEvents.contains (.moved source chainSpent .combatChain grave) &&
    (paidSlot.cardDefOf? slotSpent).map (·.id) == some cid &&
    (paidChain.cardDefOf? chainSpent).map (·.id) == some cid &&
    paidSlot.zone chest == [] && paidChain.zone chest == [] &&
    !(paidChain.zone .combatChain).contains source && (paidChain.zone .stack).length == 1 &&
    (paidChain.poolOf defender).resources == 0 && (rolling.poolOf defender).resources == 0 &&
    (resolved.poolOf defender).resources == roll / 2 && (resolved.poolOf defender).actionPoints == 0 &&
    (step 64 rolling ⟨.chance, .die6Roll 0⟩).toOption.isNone &&
    (step 64 rolling ⟨.chance, .die6Roll 7⟩).toOption.isNone &&
    hit.lifeOf defender == 36 && worn.lifeOf defender == 37 && worn.zone chest == [source] &&
    (worn.obj? source).map (·.minusDefenseCounters) == some 1 &&
    objEffectiveDefense worn source == some 0)

#guard [1, 2, 3, 4, 5, 6].all (fun roll => checkBarkboneStrapping roll == some true)

/-- Scabskin Leathers spends an AP, rounds the die down, and resets its limit next turn. -/
meta def checkScabskinLeathers (roll : Nat) : Option Bool := do
  let player : PlayerId := ⟨0⟩
  let opponent : PlayerId := ⟨1⟩
  let cid : CardId := ⟨"WTR_004"⟩
  let slot := Zone.player player .legs
  let funded := m5Base.setPool player { actionPoints := 2 }
  let base : GameState := { funded with pending := funded.pending ++ [.beginTurn] }
  let card ← base.cards.find? cid
  let (equipped, source) ← cPlace base player .legs cid
  let activate : Action := ⟨.player player, .activateAbility source 0⟩
  let noPoints := equipped.setPool player {}
  let paid ← cSteps equipped [activate]
  let rolling ← cSteps paid passBoth
  let resolved ← cSteps rolling [⟨.chance, .die6Roll roll⟩]
  let opponentTurn ← cSteps resolved passBoth
  let nextOwnTurn ← cSteps opponentTurn passBoth.reverse
  let reused ← cSteps nextOwnTurn [activate]
  let (wearReady, wornSource) ← cPlace m5Base opponent .legs cid
  let (withAttack, attack) ← cPlace wearReady player .hand ⟨"WTR_203_R"⟩
  let defending ← cSteps withAttack
    (⟨.player player, .playCard attack⟩ :: (passBoth ++ passBoth))
  let closed ← cSteps defending
    ([⟨.player opponent, .defendCard wornSource⟩, ⟨.player opponent, .defendDone⟩] ++
      passBoth ++ passBoth ++ passBoth ++ passBoth)
  pure (card.status == .full && card.front.defense == some 2 && card.front.keywords.contains .battleworn &&
    (legalActionsFor player equipped).contains activate && (step 64 noPoints activate).toOption.isNone &&
    paid.zone slot == [source] && paid.activatedThisTurn.contains (source, 0) &&
    (paid.poolOf player).actionPoints == 1 && (rolling.poolOf player).actionPoints == 1 &&
    (resolved.poolOf player).actionPoints == 1 + roll / 2 &&
    !(legalActionsFor player resolved).contains activate && (step 64 resolved activate).toOption.isNone &&
    opponentTurn.active == some opponent && nextOwnTurn.active == some player &&
    nextOwnTurn.activatedThisTurn.isEmpty && (reused.poolOf player).actionPoints == 0 &&
    reused.activatedThisTurn.contains (source, 0) &&
    closed.lifeOf opponent == 38 && closed.zone (.player opponent .legs) == [wornSource] &&
    (closed.obj? wornSource).map (·.minusDefenseCounters) == some 1 &&
    objEffectiveDefense closed wornSource == some 1)

#guard [1, 2, 3, 4, 5, 6].all (fun roll => checkScabskinLeathers roll == some true)

/-- Roll every Crazy Brew outcome through the activated layer and test the next attack. -/
meta def checkCrazyBrew (roll : Nat) : Option Bool := do
  let player : PlayerId := ⟨0⟩
  let opponent : PlayerId := ⟨1⟩
  let cid : CardId := ⟨"WTR_162_B"⟩
  let arena := Zone.player player .permanent
  let grave := Zone.player player .graveyard
  let funded := m5Base.setPool player { actionPoints := 2 }
  let card ← funded.cards.find? cid
  let (withBrew, item) ← cPlace funded player .hand cid
  let (ready, attack) ← cPlace withBrew player .hand ⟨"WTR_098_R"⟩
  let installed ← cSteps ready (⟨.player player, .playCard item⟩ :: passBoth)
  let source ← (installed.zone arena).head?
  let activate : Action := ⟨.player player, .activateAbility source 0⟩
  let (paid, events) ← (step 64 installed activate).toOption
  let spent ← (paid.zone grave).head?
  let rolling ← cSteps paid passBoth
  let resolved ← cSteps rolling [⟨.chance, .die6Roll roll⟩]
  let defending ← cSteps resolved
    (⟨.player player, .playCard attack⟩ :: (passBoth ++ passBoth))
  let link ← defending.combat.bind CombatChain.activeLink?
  let hit ← cSteps defending
    ([⟨.player opponent, .defendDone⟩] ++ passBoth ++ passBoth ++ passBoth)
  let high := 5 ≤ roll
  pure (card.status == .full && card.front.pitch == some 3 &&
    paid.zone arena == [] && (paid.cardDefOf? spent).map (·.id) == some cid &&
    events.contains (.moved source spent arena grave) &&
    (rolling.poolOf player).actionPoints == 0 && (rolling.poolOf player).resources == 0 &&
    rolling.lifeOf player == 40 && rolling.activeEffects.isEmpty &&
    (step 64 rolling ⟨.chance, .die6Roll 0⟩).toOption.isNone &&
    (step 64 rolling ⟨.chance, .die6Roll 7⟩).toOption.isNone &&
    (step 64 rolling ⟨.player player, .die6Roll roll⟩).toOption.isNone &&
    resolved.lifeOf player == (if roll ≤ 2 then 38 else if roll ≤ 4 then 42 else 40) &&
    (resolved.poolOf player).actionPoints == (if high then 2 else 1) &&
    (resolved.poolOf player).resources == (if high then 2 else 0) &&
    resolved.activeEffects.length == (if high then 1 else 0) &&
    link.powerBonus == (if high then 2 else 0) && defending.activeEffects.isEmpty &&
    hit.lifeOf opponent == (if high then 35 else 37))

#guard [1, 2, 3, 4, 5, 6].all (fun roll => checkCrazyBrew roll == some true)

/-- Energy Potion can respond to the opponent's attack and adds resources on resolution. -/
meta def checkEnergyPotion : Option Bool := do
  let player : PlayerId := ⟨0⟩
  let opponent : PlayerId := ⟨1⟩
  let cid : CardId := ⟨"WTR_170_B"⟩
  let arena := Zone.player player .permanent
  let grave := Zone.player player .graveyard
  let base : GameState := { m5Base with pending := m5Base.pending ++ [.beginTurn] }
  let card ← base.cards.find? cid
  let (ready, item) ← cPlace base player .hand cid
  let installed ← cSteps ready (⟨.player player, .playCard item⟩ :: passBoth)
  let source ← (installed.zone arena).head?
  let activate : Action := ⟨.player player, .activateAbility source 0⟩
  let next ← cSteps installed passBoth
  let (withAttack, attack) ← cPlace next opponent .hand ⟨"WTR_098_R"⟩
  let queued ← cSteps withAttack [⟨.player opponent, .playCard attack⟩]
  let attackLayer ← (queued.zone .stack).head?
  let window ← cSteps queued [⟨.player opponent, .pass⟩]
  let (paid, events) ← (step 64 window activate).toOption
  let spent ← (paid.zone grave).head?
  let resolved ← cSteps paid passBoth
  pure (card.status == .full && card.front.pitch == some 3 &&
    (step 64 ready ⟨.player player, .activateAbility item 0⟩).toOption.isNone &&
    next.active == some opponent && !(legalActionsFor player queued).contains activate &&
    (legalActionsFor player window).contains activate &&
    (step 64 queued ⟨.player opponent, .activateAbility source 0⟩).toOption.isNone &&
    paid.zone arena == [] && events.contains (.moved source spent arena grave) &&
    (paid.cardDefOf? spent).map (·.id) == some cid && (paid.zone .stack).length == 2 &&
    (paid.poolOf player).resources == 0 && (paid.poolOf player).actionPoints == 0 &&
    resolved.zone .stack == [attackLayer] && (resolved.poolOf player).resources == 2 &&
    (resolved.poolOf player).actionPoints == 0 &&
    (resolved.poolOf opponent).resources == (window.poolOf opponent).resources &&
    (step 64 resolved activate).toOption.isNone)

#guard checkEnergyPotion == some true

/-- Potion of Strength boosts exactly the next attack this turn and refunds its AP. -/
meta def checkPotionOfStrength (useWeapon : Bool) : Option Bool := do
  let player : PlayerId := ⟨0⟩
  let opponent : PlayerId := ⟨1⟩
  let cid : CardId := ⟨"WTR_171_B"⟩
  let arena := Zone.player player .permanent
  let grave := Zone.player player .graveyard
  let base : GameState := { m5Base with pending := m5Base.pending ++ [.beginTurn] }
  let withAssets := base.setPool player { actionPoints := 2, resources := 1 }
  let card ← withAssets.cards.find? cid
  let (withPotion, item) ← cPlace withAssets player .hand cid
  let (withWeapon, weapon) ← cPlace withPotion player .weapon ⟨"WTR_078"⟩
  let (withAttack, attack) ← cPlace withWeapon player .hand ⟨"WTR_098_R"⟩
  let (ready, instant) ← cPlace withAttack player .hand ⟨"WTR_173_R"⟩
  let play id : Action := ⟨.player player, .playCard id⟩
  let attackAction : Action := if useWeapon then ⟨.player player, .attackWeapon weapon⟩ else play attack
  let installed ← cSteps ready (play item :: passBoth)
  let source ← (installed.zone arena).head?
  let activate : Action := ⟨.player player, .activateAbility source 0⟩
  let paid ← cSteps installed [activate]
  let spent ← (paid.zone grave).head?
  let buffed ← cSteps paid passBoth
  let afterInstant ← cSteps buffed (play instant :: passBoth)
  let defending ← cSteps afterInstant ([attackAction] ++ passBoth ++ passBoth)
  let link ← defending.combat.bind CombatChain.activeLink?
  let afterHit ← cSteps defending
    ([⟨.player opponent, .defendDone⟩] ++ passBoth ++ passBoth ++ passBoth)
  let passedTurn ← cSteps buffed (passBoth ++ [⟨.player player, .arsenalSkip⟩])
  pure (card.status == .full && card.front.pitch == some 3 &&
    (installed.poolOf player).actionPoints == 1 && (paid.poolOf player).actionPoints == 0 &&
    paid.zone arena == [] && (paid.cardDefOf? spent).map (·.id) == some cid &&
    paid.activeEffects.isEmpty && (buffed.poolOf player).actionPoints == 1 &&
    buffed.activeEffects.length == 1 && afterInstant.activeEffects == buffed.activeEffects &&
    defending.activeEffects.isEmpty && link.powerBonus == 2 &&
    afterHit.lifeOf opponent == (if useWeapon then 37 else 35) &&
    passedTurn.active == some opponent && passedTurn.activeEffects.isEmpty)

#guard checkPotionOfStrength false == some true
#guard checkPotionOfStrength true == some true

/-- Timesnap Potion destroys itself as an activation cost and grants AP only on resolution. -/
meta def checkTimesnapPotion : Option Bool := do
  let player : PlayerId := ⟨0⟩
  let opponent : PlayerId := ⟨1⟩
  let cid : CardId := ⟨"WTR_172_B"⟩
  let funded := m5Base.setPool player { actionPoints := 2 }
  let card ← funded.cards.find? cid
  let (ready, item) ← cPlace funded player .hand cid
  let play : Action := ⟨.player player, .playCard item⟩
  let active ← cSteps ready (play :: passBoth)
  let arena := Zone.player player .permanent
  let grave := Zone.player player .graveyard
  let source ← (active.zone arena).head?
  let activate : Action := ⟨.player player, .activateAbility source 0⟩
  let noPoints := active.setPool player {}
  let duringOpponentTurn := { active with active := some opponent, pending := [.priority player 0] }
  let withCombat := { active with combat := some { step := .resolution } }
  let (paid, events) ← (step 64 active activate).toOption
  let spent ← (paid.zone grave).head?
  let ability ← (paid.zone .stack).head?
  let resolved ← cSteps paid passBoth
  pure (card.status == .full && card.front.pitch == some 3 &&
    (step 64 ready ⟨.player player, .activateAbility item 0⟩).toOption.isNone &&
    (active.poolOf player).actionPoints == 1 && (legalActionsFor player active).contains activate &&
    (step 64 active ⟨.player player, .activateAbility source 1⟩).toOption.isNone &&
    (step 64 noPoints activate).toOption.isNone &&
    (step 64 duringOpponentTurn activate).toOption.isNone &&
    (step 64 withCombat activate).toOption.isNone &&
    (step 64 active ⟨.player opponent, .activateAbility source 0⟩).toOption.isNone &&
    (paid.poolOf player).actionPoints == 0 && paid.zone arena == [] &&
    (paid.cardDefOf? spent).map (·.id) == some cid &&
    events.contains (.moved source spent arena grave) &&
    (paid.obj? ability).any (fun o => match o.kind with
      | .layer origin _ index isTrigger => origin == source && index == 0 && !isTrigger
      | _ => false) &&
    (resolved.poolOf player).actionPoints == 2 && (resolved.zone .stack).isEmpty &&
    (step 64 resolved activate).toOption.isNone)

#guard checkTimesnapPotion == some true

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

/-- A Mugenshi: RELEASE combo hit lets the player choose how many Lords of Wind to reveal. -/
meta def checkMugenshiRelease : Option Bool := do
  let attacker : PlayerId := ⟨0⟩
  let defender : PlayerId := ⟨1⟩
  let cid : CardId := ⟨"WTR_083_Y"⟩
  let lordCid : CardId := ⟨"WTR_081_B"⟩
  let deck := Zone.player attacker .deck
  let hand := Zone.player attacker .hand
  let base := m5Base.setPool attacker { actionPoints := 2, resources := 3 }
  let card ← base.cards.find? cid
  let (withGust, gust) ← cPlace base attacker .hand ⟨"WTR_110_R"⟩
  let (withRelease, release) ← cPlace withGust attacker .hand cid
  let (withLord, lord) ← cPlace withRelease attacker .deck lordCid
  let (withTwo, otherLord) ← cPlace withLord attacker .deck lordCid
  let (withOther, other) ← cPlace withTwo attacker .deck ⟨"WTR_188_R"⟩
  let (withBlock, firstBlock) ← cPlace withOther defender .hand ⟨"WTR_048_R"⟩
  let (ready, secondBlock) ← cPlace withBlock defender .hand ⟨"WTR_049_Y"⟩
  let enter (id : ObjId) : List Action := ⟨.player attacker, .playCard id⟩ :: (passBoth ++ passBoth)
  let toDamage := ⟨.player defender, .defendDone⟩ :: (passBoth ++ passBoth)
  let choice (id : ObjId) : Action := ⟨.player attacker, .pickShuffleCard (some id)⟩
  let done : Action := ⟨.player attacker, .pickShuffleCard none⟩
  let shuffle (s : GameState) : Action := ⟨.chance, .shuffleOrder (s.zone deck).reverse⟩
  let first ← cSteps ready (enter gust ++ toDamage ++ passBoth)
  let defending ← cSteps first (enter release)
  let hit ← cSteps defending toDamage
  let link ← hit.combat.bind CombatChain.activeLink?
  let trigger ← hit.pendingTriggers.head?
  let picking ← cSteps hit ([⟨.player attacker, .pickTriggerStart attacker⟩,
    ⟨.player attacker, .pickTrigger trigger.id⟩] ++ passBoth)
  let chosen ← cSteps picking [choice lord]
  let (committed, events) ← (step 64 chosen done).toOption
  let moved ← (committed.zone hand).head?
  let one ← cSteps committed [shuffle committed]
  let completed ← cSteps one passBoth
  let both ← cSteps picking [choice otherLord, choice lord, done]
  let all ← cSteps both [shuffle both]
  let declined ← cSteps picking [done]
  let noCards ← cSteps declined [shuffle declined]
  let blocked ← cSteps defending ([⟨.player defender, .defendCard firstBlock⟩,
    ⟨.player defender, .defendCard secondBlock⟩] ++ toDamage ++ passBoth)
  let standalone ← cSteps ready (enter release ++ toDamage ++ passBoth)
  pure (card.status == .full && card.front.keywords.contains (.specialization "Katsu") &&
    card.front.pitch == some 2 && card.front.defense == some 3 &&
    link.powerBonus == 1 && link.damageDealt == 5 &&
    (view attacker picking).selectionChoices == [(otherLord, lordCid), (lord, lordCid)] &&
    (view defender picking).selectionChoices == [] &&
    (step 64 picking (choice other)).toOption.isNone &&
    events == [.revealed attacker lord lordCid, .moved lord moved deck hand] &&
    committed.pending.head? == some (.chanceShuffle deck) &&
    one.zone hand == [moved] && (one.cardDefOf? moved).map (·.id) == some lordCid &&
    one.zone deck == [otherLord, other] && (completed.poolOf attacker).actionPoints == 1 &&
    all.zone deck == [other] &&
    (all.zone hand).map (fun id => (all.cardDefOf? id).map (·.id)) == [some lordCid, some lordCid] &&
    declined.pending.head? == some (.chanceShuffle deck) &&
    noCards.zone deck == (picking.zone deck).reverse && noCards.zone hand == [] &&
    (blocked.poolOf attacker).actionPoints == 1 && blocked.pendingTriggers.isEmpty &&
    blocked.lifeOf defender == first.lifeOf defender && blocked.zone deck == ready.zone deck &&
    (standalone.poolOf attacker).actionPoints == 1 && standalone.pendingTriggers.isEmpty &&
    standalone.lifeOf defender == 36 && standalone.zone deck == ready.zone deck)

#guard checkMugenshiRelease == some true

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

/-- A next-weapon effect survives other plays and reaches only the first paid weapon attack. -/
meta def checkNextWeaponBuff (cid : CardId) (pitch cost bonus : Nat) (givesGoAgain : Bool) :
    Option Bool := do
  let attacker : PlayerId := ⟨0⟩
  let defender : PlayerId := ⟨1⟩
  let funded := m5Base.setPool attacker { actionPoints := 3, resources := 2 * cost + 2 }
  let card ← funded.cards.find? cid
  let (withBuff, buff) ← cPlace funded attacker .hand cid
  let (withAttack, attack) ← cPlace withBuff attacker .hand ⟨"WTR_203_R"⟩
  let (withReserve, _) ← cPlace withAttack attacker .hand ⟨"WTR_205_B"⟩
  let (withWeapon, firstWeapon) ← cPlace withReserve attacker .weapon ⟨"WTR_078"⟩
  let (ready, secondWeapon) ← cPlace withWeapon attacker .weapon ⟨"WTR_078"⟩
  let play := fun id => [⟨.player attacker, .playCard id⟩]
  let swing := fun id => [⟨.player attacker, .attackWeapon id⟩]
  let fight := passBoth ++ passBoth ++ [⟨.player defender, .defendDone⟩] ++
    passBoth ++ passBoth ++ passBoth
  let buffed ← cSteps ready (play buff ++ passBoth)
  let afterCard ← cSteps buffed (play attack ++ fight ++ passBoth)
  let broke := afterCard.setPool attacker { actionPoints := 2 }
  let unpaid ← cSteps broke (swing firstWeapon)
  let cancelled ← cSteps unpaid [⟨.player attacker, .cancelPlay⟩]
  let paid ← cSteps afterCard (swing firstWeapon)
  let layer ← (paid.zone .stack).head?
  let info ← paid.layerMeta.get? layer.n
  let enhanced ← cSteps paid fight
  let enhancedLink ← enhanced.combat.bind CombatChain.activeLink?
  let firstClosed ← cSteps enhanced passBoth
  let normal ← cSteps firstClosed (swing secondWeapon ++ fight)
  let normalLink ← normal.combat.bind CombatChain.activeLink?
  let ended ← cSteps buffed (passBoth ++ [⟨.player attacker, .arsenalSkip⟩])
  let (withSecondBuff, secondBuff) ← cPlace buffed attacker .hand cid
  let doubleBuffed ← cSteps withSecondBuff (play secondBuff ++ passBoth)
  let doubleAttack ← cSteps doubleBuffed (swing firstWeapon ++ fight)
  let doubleLink ← doubleAttack.combat.bind CombatChain.activeLink?
  let paidAp := if givesGoAgain then 2 else 1
  let effectCount := if givesGoAgain then 2 else 1
  pure (card.status == .full && card.front.pitch == some pitch && card.front.defense == some 3 &&
    (buffed.poolOf attacker).actionPoints == 3 && (buffed.poolOf attacker).resources == cost + 2 &&
    objEffectivePower buffed firstWeapon == some 1 &&
    buffed.activeEffects.length == effectCount &&
    buffed.activeEffects.all (fun effect => effect.target == .nextAttack CardFilter.weaponAttack) &&
    afterCard.lifeOf defender == 36 && afterCard.activeEffects == buffed.activeEffects &&
    unpaid.activeEffects == broke.activeEffects && decide (cancelled = broke) &&
    paid.activeEffects.isEmpty && info.attackPowerBonus == Int.ofNat bonus &&
    info.attackKeywords.contains .goAgain == givesGoAgain &&
    enhancedLink.attackSource == some firstWeapon && enhancedLink.damageDealt == 1 + bonus &&
    (enhanced.poolOf attacker).actionPoints == paidAp &&
    normalLink.attackSource == some secondWeapon && normalLink.damageDealt == 1 &&
    (normal.poolOf attacker).actionPoints == paidAp - 1 &&
    ended.activeEffects.isEmpty && doubleAttack.activeEffects.isEmpty &&
    doubleLink.damageDealt == 1 + 2 * bonus &&
    (doubleAttack.poolOf attacker).actionPoints == (if givesGoAgain then 3 else 2))

#guard checkNextWeaponBuff ⟨"WTR_141_R"⟩ 1 0 3 false == some true
#guard checkNextWeaponBuff ⟨"WTR_142_Y"⟩ 2 0 2 false == some true
#guard checkNextWeaponBuff ⟨"WTR_143_B"⟩ 3 0 1 false == some true
#guard checkNextWeaponBuff ⟨"WTR_144_R"⟩ 1 2 3 true == some true
#guard checkNextWeaponBuff ⟨"WTR_145_Y"⟩ 2 2 2 true == some true
#guard checkNextWeaponBuff ⟨"WTR_146_B"⟩ 3 2 1 true == some true

/-- Breakneck Battery uses the power of the card discarded for its own play. -/
meta def checkBreakneckBattery (cid : CardId) (pitch power : Nat) (fromArsenal : Bool) :
    Option Bool := do
  let attacker : PlayerId := ⟨0⟩
  let defender : PlayerId := ⟨1⟩
  let hand := Zone.player attacker .hand
  let grave := Zone.player attacker .graveyard
  let origin : ZoneKind := if fromArsenal then .arsenal else .hand
  let funded := m5Base.setPool attacker { actionPoints := 1, resources := 2 }
  let card ← funded.cards.find? cid
  let (one, high) ← cPlace funded attacker .hand ⟨"WTR_189_Y"⟩
  let (two, low) ← cPlace one attacker .hand ⟨"WTR_190_B"⟩
  let (withCard, attack) ← cPlace two attacker origin cid fromArsenal
  let (withFirst, first) ← cPlace withCard defender .hand ⟨"WTR_203_R"⟩
  let (ready, second) ← cPlace withFirst defender .hand ⟨"WTR_204_Y"⟩
  let (trying, _) ← (step 64 ready ⟨.player attacker, .playCard attack⟩).toOption
  let layer ← (trying.zone .stack).head?
  let paidHigh ← cSteps trying [⟨.chance, .shuffleOrder [high, low]⟩]
  let paidLow ← cSteps trying [⟨.chance, .shuffleOrder [low, high]⟩]
  let highDiscard ← (paidHigh.zone grave).head?
  let lowDiscard ← (paidLow.zone grave).head?
  let threshold := Condition.lastDiscardedMatches { minPower := some 6 }
  let (moved, _) ← moveObj paidHigh highDiscard (.player attacker .banished) .top false
  let (unrelatedLow, _, _) := execPrim moved attacker layer [] (.discardHandPrefix 1)
  let (unrelatedHigh, _, _) := execPrim paidLow attacker layer [] (.discardHandPrefix 1)
  let startDefense := passBoth ++ passBoth
  let endDefense := [⟨.player defender, .defendDone⟩] ++ passBoth ++ passBoth ++ passBoth
  let blocks := [⟨.player defender, .defendCard first⟩, ⟨.player defender, .defendCard second⟩]
  let check := fun (state : GameState) (goAgain : Bool) => do
    let defending ← cSteps state startDefense
    let link ← defending.combat.bind CombatChain.activeLink?
    let src ← link.attack
    let hit ← cSteps defending endDefense
    let blocked ← cSteps defending (blocks ++ endDefense)
    let expectedAp := if goAgain then 1 else 0
    pure (linkHasKeyword defending link .goAgain == goAgain &&
      evalCondition defending attacker src fromArsenal threshold == goAgain &&
      (defending.poolOf attacker).actionPoints == 0 &&
      hit.lifeOf defender == 40 - Int.ofNat power && blocked.lifeOf defender == 40 &&
      (hit.poolOf attacker).actionPoints == expectedAp &&
      (blocked.poolOf attacker).actionPoints == expectedAp)
  let highOk ← check unrelatedLow true
  let lowOk ← check unrelatedHigh false
  pure (card.status == .full && card.front.pitch == some pitch && card.front.defense == some 3 &&
    trying.pending.head? == some (.chanceShuffle hand) &&
    (trying.poolOf attacker).actionPoints == 0 && (trying.poolOf attacker).resources == 0 &&
    (paidHigh.cardDefOf? highDiscard).map (·.id) == some ⟨"WTR_189_Y"⟩ &&
    (paidLow.cardDefOf? lowDiscard).map (·.id) == some ⟨"WTR_190_B"⟩ &&
    evalCondition paidHigh attacker layer fromArsenal threshold &&
    !evalCondition paidLow attacker layer fromArsenal threshold &&
    !evalCondition paidHigh attacker low fromArsenal threshold && highOk && lowOk)

#guard checkBreakneckBattery ⟨"WTR_011_R"⟩ 1 6 false == some true
#guard checkBreakneckBattery ⟨"WTR_011_R"⟩ 1 6 true == some true
#guard checkBreakneckBattery ⟨"WTR_012_Y"⟩ 2 5 false == some true
#guard checkBreakneckBattery ⟨"WTR_012_Y"⟩ 2 5 true == some true
#guard checkBreakneckBattery ⟨"WTR_013_B"⟩ 3 4 false == some true
#guard checkBreakneckBattery ⟨"WTR_013_B"⟩ 3 4 true == some true

/-- Savage Feast stacks its conditional draw when it attacks and before defense. -/
meta def checkSavageFeast (cid : CardId) (pitch power : Nat) (fromArsenal : Bool) : Option Bool := do
  let attacker : PlayerId := ⟨0⟩
  let defender : PlayerId := ⟨1⟩
  let hand := Zone.player attacker .hand
  let deck := Zone.player attacker .deck
  let grave := Zone.player attacker .graveyard
  let origin : ZoneKind := if fromArsenal then .arsenal else .hand
  let funded := m5Base.setPool attacker { actionPoints := 1, resources := 1 }
  let card ← funded.cards.find? cid
  let (withFeast, feast) ← cPlace funded attacker origin cid fromArsenal
  let (withHigh, high) ← cPlace withFeast attacker .hand ⟨"WTR_189_Y"⟩
  let (withLow, low) ← cPlace withHigh attacker .hand ⟨"WTR_190_B"⟩
  let (withBottom, bottom) ← cPlace withLow attacker .deck ⟨"WTR_204_Y"⟩
  let (ready, top) ← cPlace withBottom attacker .deck ⟨"WTR_203_R"⟩
  let paying ← cSteps ready [⟨.player attacker, .playCard feast⟩]
  let layer ← (paying.zone .stack).head?
  let paidHigh ← cSteps paying [⟨.chance, .shuffleOrder [high, low]⟩]
  let paidLow ← cSteps paying [⟨.chance, .shuffleOrder [low, high]⟩]
  let highDiscard ← (paidHigh.zone grave).head?
  let (movedHigh, _) ← moveObj paidHigh highDiscard (.player attacker .banished) .top false
  let (otherDiscard, _, _) := execPrim paidLow attacker layer [] (.discardHandPrefix 1)
  let highAttack ← cSteps movedHigh passBoth
  let highLink ← highAttack.combat.bind CombatChain.activeLink?
  let lowAttack ← cSteps otherDiscard passBoth
  let trigger ← highAttack.pendingTriggers.head?
  let stacked ← cSteps highAttack [⟨.player attacker, .pickTriggerStart attacker⟩,
    ⟨.player attacker, .pickTrigger trigger.id⟩, ⟨.player attacker, .pass⟩]
  let (drawn, events) ← (step 64 stacked ⟨.player defender, .pass⟩).toOption
  let drawnId ← (drawn.zone hand).head?
  let finish := passBoth ++ [⟨.player defender, .defendDone⟩] ++ passBoth ++ passBoth ++ passBoth
  let highHit ← cSteps drawn finish
  let lowHit ← cSteps lowAttack finish
  pure (card.status == .full && card.front.pitch == some pitch && card.front.defense == some 3 &&
    paying.pending.head? == some (.chanceShuffle hand) &&
    (paying.poolOf attacker).actionPoints == 0 && (paying.poolOf attacker).resources == 0 &&
    paidHigh.zone hand == [low] && paidLow.zone hand == [high] &&
    paidHigh.pendingTriggers.isEmpty && paidLow.pendingTriggers.isEmpty &&
    highAttack.combat.map (·.step) == some .attack && lowAttack.combat.map (·.step) == some .attack &&
    highAttack.pendingTriggers.length == 1 && lowAttack.pendingTriggers.isEmpty &&
    trigger.fromArsenal == fromArsenal && some trigger.source == highLink.attack &&
    highAttack.zone deck == [top, bottom] && stacked.zone deck == [top, bottom] &&
    drawn.zone deck == [bottom] && drawn.zone hand == [drawnId, low] &&
    (drawn.obj? drawnId).map (·.kind) == (ready.obj? top).map (·.kind) &&
    events.countP (· == .drawn attacker drawnId) == 1 &&
    highHit.zone deck == [bottom] && lowHit.zone deck == [top, bottom] &&
    highHit.lifeOf defender == 40 - Int.ofNat power && lowHit.lifeOf defender == highHit.lifeOf defender &&
    (highHit.poolOf attacker).actionPoints == 0 && (lowHit.poolOf attacker).actionPoints == 0)

#guard checkSavageFeast ⟨"WTR_014_R"⟩ 1 6 false == some true
#guard checkSavageFeast ⟨"WTR_014_R"⟩ 1 6 true == some true
#guard checkSavageFeast ⟨"WTR_015_Y"⟩ 2 5 false == some true
#guard checkSavageFeast ⟨"WTR_015_Y"⟩ 2 5 true == some true
#guard checkSavageFeast ⟨"WTR_016_B"⟩ 3 4 false == some true
#guard checkSavageFeast ⟨"WTR_016_B"⟩ 3 4 true == some true

/-- A weapon gets Go Again only when its granted hit trigger resolves. -/
meta def checkWarriorsValor (cid : CardId) (pitch bonus : Nat) : Option Bool := do
  let attacker : PlayerId := ⟨0⟩
  let defender : PlayerId := ⟨1⟩
  let funded := m5Base.setPool attacker { actionPoints := 1, resources := 4 }
  let card ← funded.cards.find? cid
  let (withValor, valor) ← cPlace funded attacker .hand cid
  let (withSecondValor, secondValor) ← cPlace withValor attacker .hand cid
  let (withJab, jab) ← cPlace withSecondValor attacker .hand ⟨"WTR_098_R"⟩
  let (equipped, weapon) ← cPlace withJab attacker .weapon ⟨"WTR_078"⟩
  let (withSecondWeapon, secondWeapon) ← cPlace equipped attacker .weapon ⟨"WTR_078"⟩
  let (withBlock, block) ← cPlace withSecondWeapon defender .hand ⟨"WTR_203_R"⟩
  let (ready, secondBlock) ← cPlace withBlock defender .hand ⟨"WTR_204_Y"⟩
  let play := fun id => (⟨.player attacker, .playCard id⟩ : Action)
  let swing := fun id => (⟨.player attacker, .attackWeapon id⟩ : Action)
  let defend := fun id => (⟨.player defender, .defendCard id⟩ : Action)
  let toDefend := passBoth ++ passBoth
  let toDamage := [⟨.player defender, .defendDone⟩] ++ passBoth ++ passBoth
  let activeLink := fun (s : GameState) => s.combat.bind CombatChain.activeLink?
  let ap := fun (s : GameState) => (s.poolOf attacker).actionPoints
  let start : Action := ⟨.player attacker, .pickTriggerStart attacker⟩
  let pick := fun (trig : PendingTrigger) => (⟨.player attacker, .pickTrigger trig.id⟩ : Action)
  let buffed ← cSteps ready (play valor :: passBoth)
  let afterJab ← cSteps buffed (play jab :: (toDefend ++ toDamage ++ passBoth))
  let beforeSwing ← cSteps afterJab passBoth
  let broke := beforeSwing.setPool attacker { actionPoints := 1 }
  let cancelled ← cSteps broke [swing weapon, ⟨.player attacker, .cancelPlay⟩]
  let paid ← cSteps beforeSwing [swing weapon]
  let proxy ← (paid.zone .stack).head?
  let pending ← paid.layerMeta.get? proxy.n
  let defending ← cSteps paid toDefend
  let defendLink ← activeLink defending
  let hit ← cSteps defending toDamage
  let hitLink ← activeLink hit
  let trigger ← hit.pendingTriggers.head?
  let stacked ← cSteps hit [start, pick trigger]
  let afterTrigger ← cSteps stacked passBoth
  let triggeredLink ← activeLink afterTrigger
  let resolved ← cSteps afterTrigger passBoth
  let ordinary ← cSteps resolved (passBoth ++ [swing secondWeapon] ++ toDefend ++ toDamage ++ passBoth)
  let ordinaryLink ← activeLink ordinary
  let blocked ← cSteps defending ([defend block, defend secondBlock] ++ toDamage ++ passBoth)
  let blockedLink ← activeLink blocked
  let (shielded, _, _) := execPrim defending defender ⟨0⟩ []
    (.preventNextDamage .controller (.const (Int.ofNat (1 + bonus))) .thisTurn)
  let prevented ← cSteps shielded (toDamage ++ passBoth)
  let preventedLink ← activeLink prevented
  let doubleBuffed ← cSteps buffed (play secondValor :: passBoth)
  let doubleHit ← cSteps doubleBuffed (swing weapon :: (toDefend ++ toDamage))
  let firstTrigger ← doubleHit.pendingTriggers[0]?
  let secondTrigger ← doubleHit.pendingTriggers[1]?
  let doubleResolved ← cSteps doubleHit ([start, pick firstTrigger, pick secondTrigger] ++
    passBoth ++ passBoth ++ passBoth)
  let doubleLink ← activeLink doubleResolved
  let ended ← cSteps buffed (passBoth ++ [⟨.player attacker, .arsenalSkip⟩])
  pure (card.status == .full && card.front.pitch == some pitch && card.front.defense == some 3 &&
    ap buffed == 1 && (buffed.poolOf attacker).resources == 3 && buffed.activeEffects.length == 2 &&
    afterJab.lifeOf defender == 37 && beforeSwing.activeEffects == buffed.activeEffects &&
    decide (cancelled = broke) && paid.activeEffects.isEmpty && pending.attackAbilities.length == 1 &&
    pending.attackPowerBonus == Int.ofNat bonus && !linkHasKeyword defending defendLink .goAgain &&
    hitLink.attackSource == some weapon && hitLink.damageDealt == 1 + bonus && hitLink.hit &&
    hit.pendingTriggers.length == 1 && some trigger.source == hitLink.attack &&
    !linkHasKeyword hit hitLink .goAgain && ap hit == 0 && ap stacked == 0 &&
    linkHasKeyword afterTrigger triggeredLink .goAgain && ap afterTrigger == 0 && ap resolved == 1 &&
    ordinaryLink.attackSource == some secondWeapon && ordinaryLink.damageDealt == 1 &&
    ordinaryLink.grantedAbilities.isEmpty && ap ordinary == 0 &&
    !blockedLink.hit && ap blocked == 0 && blocked.pendingTriggers.isEmpty &&
    !preventedLink.hit && ap prevented == 0 && prevented.pendingTriggers.isEmpty &&
    doubleHit.pendingTriggers.length == 2 && firstTrigger.id != secondTrigger.id &&
    doubleLink.damageDealt == 1 + 2 * bonus && doubleLink.grantedKeywords == [.goAgain] &&
    ap doubleResolved == 1 && ended.activeEffects.isEmpty)

#guard checkWarriorsValor ⟨"WTR_129_R"⟩ 1 3 == some true
#guard checkWarriorsValor ⟨"WTR_130_Y"⟩ 2 2 == some true
#guard checkWarriorsValor ⟨"WTR_131_B"⟩ 3 1 == some true

-- A queued Go Again belongs to the weapon attack.
#guard (do
  let attacker : PlayerId := ⟨0⟩
  let defender : PlayerId := ⟨1⟩
  let funded := m5Base.setPool attacker { actionPoints := 1, resources := 1 }
  let (equipped, weapon) ← cPlace funded attacker .weapon ⟨"WTR_078"⟩
  let flagged := applyChainLinkMod equipped attacker weapon []
    (.nextAttack CardFilter.weaponAttack) (.grantKeyword .goAgain) .thisTurn
  let (withSource, source) ← cPlace flagged attacker .permanent ⟨"WTR_203_R"⟩
  let (withProxy, proxy) ← addObject withSource .stack
    { kind := .attackProxy source none, owner := attacker, controller := attacker, timestamp := ⟨0⟩ }
    .top
  let (otherInfo, remaining) := consumeNextAttackEffects withProxy proxy { controller := attacker }
  let resolved ← cSteps flagged ([⟨.player attacker, .attackWeapon weapon⟩] ++ passBoth ++ passBoth ++
    [⟨.player defender, .defendDone⟩] ++ passBoth ++ passBoth ++ passBoth)
  let link ← resolved.combat.bind CombatChain.activeLink?
  let weaponFace ← resolved.objectFace? weapon
  pure (otherInfo.attackKeywords.isEmpty && remaining == flagged.activeEffects &&
    link.attackSource == some weapon && linkHasKeyword resolved link .goAgain &&
    !weaponFace.keywords.contains .goAgain && resolved.activeEffects.isEmpty &&
    (resolved.poolOf attacker).actionPoints == 1) : Option Bool) == some true

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

/-- The next eligible attack can be a Brute attack action or a weapon attack. -/
meta def checkPrimevalBellow (cid : CardId) (pitch bonus : Nat) (fromArsenal : Bool) :
    Option Bool := do
  let attacker : PlayerId := ⟨0⟩
  let defender : PlayerId := ⟨1⟩
  let origin : ZoneKind := if fromArsenal then .arsenal else .hand
  let funded := m5Base.setPool attacker { actionPoints := 3, resources := 4 }
  let card ← funded.cards.find? cid
  let (bare, bellow) ← cPlace funded attacker origin cid fromArsenal
  let play := fun id => (⟨.player attacker, .playCard id⟩ : Action)
  let rejected ← cSteps bare [play bellow]
  let (withPayment, reserve) ← cPlace bare attacker .hand ⟨"WTR_204_Y"⟩
  let (equipped, weapon) ← cPlace withPayment attacker .weapon ⟨"WTR_003"⟩
  let (paid, events) ← (step 64 equipped (play bellow)).toOption
  let discarded ← (paid.zone (.player attacker .graveyard)).head?
  let buffed ← cSteps paid passBoth
  let ended ← cSteps buffed passBoth
  let (withGeneric, genericAttack) ← cPlace buffed attacker .hand ⟨"WTR_203_R"⟩
  let fight := passBoth ++ passBoth ++ [⟨.player defender, .defendDone⟩] ++
    passBoth ++ passBoth ++ passBoth
  let genericHit ← cSteps withGeneric (play genericAttack :: fight)
  let beforeBrute ← cSteps genericHit passBoth
  let unfunded := beforeBrute.setPool attacker { actionPoints := 2 }
  let swing : Action := ⟨.player attacker, .attackWeapon weapon⟩
  let unpaidSwing ← cSteps unfunded [swing]
  let (withBrute, brute) ← cPlace beforeBrute attacker .hand ⟨"WTR_020_R"⟩
  let (ready, _) ← cPlace withBrute attacker .hand ⟨"WTR_204_Y"⟩
  let weaponFirst ← cSteps ready (swing :: fight)
  let weaponClosed ← cSteps weaponFirst passBoth
  let cardSecond ← cSteps weaponClosed (play brute :: fight)
  let cardFirst ← cSteps ready (play brute :: fight)
  let cardClosed ← cSteps cardFirst passBoth
  let weaponSecond ← cSteps cardClosed (swing :: fight)
  let damage := fun (s : GameState) =>
    (s.combat.bind CombatChain.activeLink?).map (·.damageDealt)
  pure (card.status == .full && card.front.pitch == some pitch && card.front.defense == some 3 &&
    decide (rejected = bare) && paid.activeEffects.isEmpty &&
    (paid.poolOf attacker).actionPoints == 2 && (paid.poolOf attacker).resources == 4 &&
    paid.zone (.player attacker .hand) == [] && events.contains (.discarded attacker discarded) &&
    (paid.obj? discarded).map (·.kind) == (equipped.obj? reserve).map (·.kind) &&
    (buffed.poolOf attacker).actionPoints == 3 && objEffectivePower buffed weapon == some 4 &&
    buffed.activeEffects.map (·.op) == [.addPower (Int.ofNat bonus)] && ended.activeEffects.isEmpty &&
    damage genericHit == some 4 && beforeBrute.activeEffects == buffed.activeEffects &&
    decide (unpaidSwing = unfunded) &&
    damage weaponFirst == some (4 + bonus) && weaponFirst.activeEffects.isEmpty &&
    damage cardSecond == some 7 && damage cardFirst == some (7 + bonus) &&
    cardFirst.activeEffects.isEmpty && damage weaponSecond == some 4)

#guard checkPrimevalBellow ⟨"WTR_035_R"⟩ 1 5 false == some true
#guard checkPrimevalBellow ⟨"WTR_035_R"⟩ 1 5 true == some true
#guard checkPrimevalBellow ⟨"WTR_036_Y"⟩ 2 4 false == some true
#guard checkPrimevalBellow ⟨"WTR_036_Y"⟩ 2 4 true == some true
#guard checkPrimevalBellow ⟨"WTR_037_B"⟩ 3 3 false == some true
#guard checkPrimevalBellow ⟨"WTR_037_B"⟩ 3 3 true == some true

/-- Bone Head Barrier prevents the rolled total across damage events in the same turn. -/
meta def checkBoneHeadBarrier (roll : Nat) (fromArsenal : Bool) : Option Bool := do
  let attacker : PlayerId := ⟨0⟩
  let defender : PlayerId := ⟨1⟩
  let origin : ZoneKind := if fromArsenal then .arsenal else .hand
  let cid : CardId := ⟨"WTR_010_Y"⟩
  let card ← m5Base.cards.find? cid
  let funded := m5Base.setPool defender { resources := 1 }
  let (withAttack, attack) ← cPlace funded attacker .hand ⟨"WTR_203_R"⟩
  let (ready, barrier) ← cPlace withAttack defender origin cid fromArsenal
  let cast : Action := ⟨.player defender, .playCard barrier⟩
  let paying ← cSteps ready [⟨.player attacker, .pass⟩]
  let paid ← cSteps paying [cast]
  let rolling ← cSteps paid [⟨.player defender, .pass⟩, ⟨.player attacker, .pass⟩]
  let (shielded, rollEvents) ← (step 64 rolling ⟨.chance, .die6Roll roll⟩).toOption
  let spentCard ← (shielded.zone (.player defender .graveyard)).head?
  let shield ← shielded.activeReplacements.head?
  let (other, otherEvents) := applyDamageWithPrevention shielded attacker .generic 1
  let (arcane, arcaneEvents) := applyDamageWithPrevention other defender .arcane 2
  let (zero, zeroEvents) := applyDamageWithPrevention arcane defender .generic 0
  let expired ← cSteps shielded (passBoth ++ [⟨.player attacker, .arsenalSkip⟩])
  let fight := passBoth ++ passBoth ++ [⟨.player defender, .defendDone⟩] ++
    passBoth ++ passBoth ++ passBoth
  let hit ← cSteps zero (⟨.player attacker, .playCard attack⟩ :: fight)
  let link ← hit.combat.bind CombatChain.activeLink?
  let afterCombat := 4 - (roll - 2)
  let afterArcane := 2 - roll
  let expectedArcane := if afterArcane == 0 then [] else [.damageDealt defender .arcane afterArcane]
  pure (card.status == .full && card.front.pitch == some 2 && card.front.defense.isNone &&
    (legalActionsFor defender paying).contains cast &&
    (paid.poolOf defender).resources == 0 && (paid.poolOf defender).actionPoints == 0 &&
    paid.activeReplacements.isEmpty && rolling.activeReplacements.isEmpty &&
    (step 64 rolling ⟨.chance, .die6Roll 0⟩).toOption.isNone &&
    (step 64 rolling ⟨.chance, .die6Roll 7⟩).toOption.isNone &&
    (shielded.cardDefOf? spentCard).map (·.id) == some cid &&
    shielded.activeReplacements.length == 1 && shield.action == .shieldPrevent roll &&
    other.activeReplacements == [shield] && otherEvents == [.damageDealt attacker .generic 1] &&
    arcaneEvents == expectedArcane &&
    arcane.activeReplacements.map (·.action) ==
      (if roll > 2 then [.shieldPrevent (roll - 2)] else []) &&
    zero.activeReplacements == arcane.activeReplacements && zeroEvents.isEmpty &&
    expired.activeReplacements.isEmpty &&
    hit.lifeOf defender == 40 - Int.ofNat (afterArcane + afterCombat) &&
    link.damageDealt == afterCombat && link.hit == decide (0 < afterCombat) &&
    hit.activeReplacements.isEmpty && !rollEvents.isEmpty)

#guard checkBoneHeadBarrier 1 false == some true
#guard checkBoneHeadBarrier 2 true == some true
#guard checkBoneHeadBarrier 3 false == some true
#guard checkBoneHeadBarrier 4 true == some true
#guard checkBoneHeadBarrier 5 false == some true
#guard checkBoneHeadBarrier 6 true == some true

/-- Bloodrush always buffs Brute attacks and only rewards its own qualifying discard. -/
meta def checkBloodrushBellow (fromArsenal highPayment : Bool) : Option Bool := do
  let attacker : PlayerId := ⟨0⟩
  let defender : PlayerId := ⟨1⟩
  let hand := Zone.player attacker .hand
  let deck := Zone.player attacker .deck
  let grave := Zone.player attacker .graveyard
  let origin : ZoneKind := if fromArsenal then .arsenal else .hand
  let funded := m5Base.setPool attacker { actionPoints := 4, resources := 4 }
  let cid : CardId := ⟨"WTR_007_Y"⟩
  let card ← funded.cards.find? cid
  let (bare, bellow) ← cPlace funded attacker origin cid fromArsenal
  let play := fun id => (⟨.player attacker, .playCard id⟩ : Action)
  let rejected ← cSteps bare [play bellow]
  let (withHigh, high) ← cPlace bare attacker .hand ⟨"WTR_189_Y"⟩
  let (withLow, low) ← cPlace withHigh attacker .hand ⟨"WTR_190_B"⟩
  let (withWeapon, weapon) ← cPlace withLow attacker .weapon ⟨"WTR_003"⟩
  let (withBottom, _) ← cPlace withWeapon attacker .deck ⟨"WTR_204_Y"⟩
  let (ready, _) ← cPlace withBottom attacker .deck ⟨"WTR_203_R"⟩
  let paying ← cSteps ready [play bellow]
  let order := if highPayment then [high, low] else [low, high]
  let paid ← cSteps paying [⟨.chance, .shuffleOrder order⟩]
  let discarded ← (paid.zone grave).head?
  let resolveClub (s : GameState) :=
    match s.pendingTriggers.head? with
    | none => some s
    | some trigger => cSteps s ([⟨.player attacker, .pickTriggerStart attacker⟩,
        ⟨.player attacker, .pickTrigger trigger.id⟩] ++ passBoth)
  let clubResolved ← resolveClub paid
  let buffed ← cSteps clubResolved passBoth
  let expired ← cSteps buffed (passBoth ++ [⟨.player attacker, .arsenalSkip⟩])
  let (withGeneric, generic) ← cPlace buffed attacker .hand ⟨"WTR_203_R"⟩
  let fight := passBoth ++ passBoth ++ [⟨.player defender, .defendDone⟩] ++
    passBoth ++ passBoth ++ passBoth
  let swing : Action := ⟨.player attacker, .attackWeapon weapon⟩
  let genericHit ← cSteps withGeneric (play generic :: fight)
  let beforeBrute ← cSteps genericHit passBoth
  let (bruteReady, brute) ← cPlace beforeBrute attacker .hand ⟨"WTR_020_R"⟩
  let playBrute := fun s => do
    let trying ← cSteps s [play brute]
    let paidAttack ← if trying.pending.head? == some (.chanceShuffle hand) then
      cSteps trying [⟨.chance, .shuffleOrder (trying.zone hand)⟩]
      else some trying
    let clubResolved ← resolveClub paidAttack
    cSteps clubResolved fight
  let weaponFirst ← cSteps bruteReady (swing :: fight)
  let weaponClosed ← cSteps weaponFirst passBoth
  let cardSecond ← playBrute weaponClosed
  let cardFirst ← playBrute bruteReady
  let cardClosed ← cSteps cardFirst passBoth
  let weaponSecond ← cSteps cardClosed (swing :: fight)
  let damage := fun (s : GameState) =>
    (s.combat.bind CombatChain.activeLink?).map (·.damageDealt)
  let buffs := if highPayment then [EffectOp.addPower 1, .addPower 2] else [.addPower 2]
  let finalBuffs := if highPayment then buffs else buffs ++ [.addPower 1]
  pure (card.status == .full && card.front.pitch == some 2 && card.front.defense == some 3 &&
    decide (rejected = bare) && paying.pending.head? == some (.chanceShuffle hand) &&
    (paid.poolOf attacker).actionPoints == 3 && (paid.poolOf attacker).resources == 3 &&
    (paid.cardDefOf? discarded).map (·.id) ==
      some (if highPayment then ⟨"WTR_189_Y"⟩ else ⟨"WTR_190_B"⟩) &&
    paid.activeEffects.isEmpty && paid.zone deck == ready.zone deck &&
    (buffed.poolOf attacker).actionPoints == (if highPayment then 4 else 3) &&
    (buffed.zone hand).length == (if highPayment then 3 else 1) &&
    (buffed.zone deck).length == (if highPayment then 0 else 2) &&
    objEffectivePower buffed weapon == some (if highPayment then 5 else 4) &&
    buffed.activeEffects.map (·.op) == buffs && expired.activeEffects.isEmpty &&
    damage genericHit == some 4 && damage weaponFirst == some (if highPayment then 7 else 6) &&
    damage cardSecond == some 9 && damage cardFirst == some 9 && damage weaponSecond == some 7 &&
    weaponSecond.activeEffects.map (·.op) == finalBuffs && cardSecond.activeEffects.map (·.op) == finalBuffs)

#guard checkBloodrushBellow false true == some true
#guard checkBloodrushBellow false false == some true
#guard checkBloodrushBellow true true == some true
#guard checkBloodrushBellow true false == some true

/-- Scour's attack trigger cycles a card by choice, and only an arsenal play gets Go Again. -/
meta def checkScourTheBattlescape (cid : CardId) (pitch power : Nat) (fromArsenal : Bool) :
    Option Bool := do
  let attacker : PlayerId := ⟨0⟩
  let defender : PlayerId := ⟨1⟩
  let hand := Zone.player attacker .hand
  let deck := Zone.player attacker .deck
  let origin : ZoneKind := if fromArsenal then .arsenal else .hand
  let card ← m5Base.cards.find? cid
  let (withBottom, bottom) ← cPlace m5Base attacker .deck ⟨"WTR_188_R"⟩
  let (withTop, top) ← cPlace withBottom attacker .deck ⟨"WTR_189_Y"⟩
  let (emptyHand, attack) ← cPlace withTop attacker origin cid fromArsenal
  let (withChoice, chosen) ← cPlace emptyHand attacker .hand ⟨"WTR_204_Y"⟩
  let (ready, kept) ← cPlace withChoice attacker .hand ⟨"WTR_205_B"⟩
  let play : Action := ⟨.player attacker, .playCard attack⟩
  let beginAttack := play :: passBoth
  let attacking ← cSteps ready beginAttack
  let trigger ← attacking.pendingTriggers.head?
  let beginResolve := [⟨.player attacker, .pickTriggerStart attacker⟩,
    ⟨.player attacker, .pickTrigger trigger.id⟩] ++ passBoth
  let prompt ← cSteps attacking beginResolve
  let declined ← cSteps prompt [⟨.player attacker, .pickMay false⟩]
  let choosing ← cSteps prompt [⟨.player attacker, .pickMay true⟩]
  let (accepted, events) ← (step 64 choosing ⟨.player attacker, .handToDeckPick chosen⟩).toOption
  let drawn ← (accepted.zone hand).head?
  let putBack ← (accepted.zone deck).getLast?
  let emptyAttacking ← cSteps emptyHand beginAttack
  let emptyTrigger ← emptyAttacking.pendingTriggers.head?
  let emptyResolved ← cSteps emptyAttacking ([⟨.player attacker, .pickTriggerStart attacker⟩,
    ⟨.player attacker, .pickTrigger emptyTrigger.id⟩] ++ passBoth)
  let fight := passBoth ++ [⟨.player defender, .defendDone⟩] ++
    passBoth ++ passBoth ++ passBoth
  let hit ← cSteps accepted fight
  let hitDeclined ← cSteps declined fight
  let hitEmpty ← cSteps emptyResolved fight
  let outcome := fun (s : GameState) =>
    (s.combat.bind CombatChain.activeLink?).any (fun link =>
      link.damageDealt == power && linkHasKeyword s link .goAgain == fromArsenal) &&
    (s.poolOf attacker).actionPoints == (if fromArsenal then 1 else 0)
  pure (card.status == .full && card.front.pitch == some pitch && card.front.defense == some 2 &&
    attacking.combat.map (·.step) == some .attack && attacking.pendingTriggers.length == 1 &&
    (attacking.poolOf attacker).actionPoints == 0 &&
    choosing.pending.head? == some (.chooseHandToDeck attacker .bottom) &&
    declined.zone hand == [kept, chosen] && declined.zone deck == [top, bottom] &&
    accepted.zone hand == [drawn, kept] && accepted.zone deck == [bottom, putBack] &&
    (accepted.cardDefOf? drawn).map (·.id) == some ⟨"WTR_189_Y"⟩ &&
    (accepted.cardDefOf? putBack).map (·.id) == some ⟨"WTR_204_Y"⟩ &&
    events.countP (· == .moved chosen putBack hand deck) == 1 &&
    events.countP (· == .drawn attacker drawn) == 1 &&
    emptyResolved.zone hand == [] && emptyResolved.zone deck == [top, bottom] &&
    outcome hit && outcome hitDeclined && outcome hitEmpty)

#guard checkScourTheBattlescape ⟨"WTR_194_R"⟩ 1 3 false == some true
#guard checkScourTheBattlescape ⟨"WTR_194_R"⟩ 1 3 true == some true
#guard checkScourTheBattlescape ⟨"WTR_195_Y"⟩ 2 2 false == some true
#guard checkScourTheBattlescape ⟨"WTR_195_Y"⟩ 2 2 true == some true
#guard checkScourTheBattlescape ⟨"WTR_196_B"⟩ 3 1 false == some true
#guard checkScourTheBattlescape ⟨"WTR_196_B"⟩ 3 1 true == some true

/-- Barraging Beatdown checks the live non-equipment defenders of the first Brute attack. -/
meta def checkBarragingBeatdown (cid : CardId) (pitch bonus : Nat) : Option Bool := do
  let attacker : PlayerId := ⟨0⟩
  let defender : PlayerId := ⟨1⟩
  let defenderHand := Zone.player defender .hand
  let banished := Zone.player defender .banished
  let funded := (m5Base.setPool attacker { actionPoints := 3, resources := 4 }).setPool defender
    { resources := 3 }
  let card ← funded.cards.find? cid
  let (withBellow, bellow) ← cPlace funded attacker .hand cid
  let (withWeapon, weapon) ← cPlace withBellow attacker .weapon ⟨"WTR_003"⟩
  let (withOther, other) ← cPlace withWeapon attacker .hand ⟨"WTR_203_R"⟩
  let (withHidden, hidden) ← cPlace withOther defender .hand ⟨"WTR_205_B"⟩
  let (withFirst, first) ← cPlace withHidden defender .hand ⟨"WTR_203_R"⟩
  let (withSecond, second) ← cPlace withFirst defender .hand ⟨"WTR_204_Y"⟩
  let (withArmor, armor) ← cPlace withSecond defender .chest ⟨"WTR_041"⟩
  let (ready, reaction) ← cPlace withArmor defender .arsenal ⟨"WTR_214_B"⟩ true
  let play := fun id => (⟨.player attacker, .playCard id⟩ : Action)
  let defend := fun id => (⟨.player defender, .defendCard id⟩ : Action)
  let done : Action := ⟨.player defender, .defendDone⟩
  let activeLink := fun (s : GameState) => s.combat.bind CombatChain.activeLink?
  let declaring ← cSteps ready [play bellow]
  let selfPaid ← cSteps declaring [⟨.player attacker, .pickHeroTarget attacker⟩]
  let selfBuffed ← cSteps selfPaid passBoth
  let selfHidden ← (selfBuffed.zone (.player attacker .banished)).head?
  let paid ← cSteps declaring [⟨.player attacker, .pickHeroTarget defender⟩]
  let chance ← cSteps paid passBoth
  let buffed ← cSteps chance [⟨.chance, .shuffleOrder [hidden, first, second]⟩]
  let intimidation ← (buffed.zone banished).head?
  let toDefend := passBoth ++ passBoth
  let finish := done :: (passBoth ++ passBoth ++ passBoth)
  let generic ← cSteps buffed (play other :: (toDefend ++ finish))
  let genericLink ← activeLink generic
  let beforeBrute ← cSteps generic passBoth
  let swing : Action := ⟨.player attacker, .attackWeapon weapon⟩
  let defending ← cSteps beforeBrute (swing :: toDefend)
  let weaponLink ← activeLink defending
  let unblocked ← cSteps defending finish
  let hitLink ← activeLink unblocked
  let oneBlock ← cSteps defending [defend armor, defend first]
  let oneLink ← activeLink oneBlock
  let twoBlocks ← cSteps oneBlock [defend second]
  let twoLink ← activeLink twoBlocks
  let oneHit ← cSteps oneBlock finish
  let twoHit ← cSteps twoBlocks finish
  let reactionStep ← cSteps oneBlock (done :: (passBoth ++ [⟨.player attacker, .pass⟩]))
  let resolved ← cSteps reactionStep [⟨.player defender, .playCard reaction⟩,
    ⟨.player defender, .pass⟩, ⟨.player attacker, .pass⟩]
  let resolvedLink ← activeLink resolved
  let toReturn ← resolvedLink.defending[1]?
  let (removed, _, _) := execPrim resolved attacker weapon []
    (.returnChosenDefendingCard toReturn)
  let removedLink ← activeLink removed
  let (cardReady, brute) ← cPlace beforeBrute attacker .hand ⟨"WTR_020_R"⟩
  let (readyWithCost, _) ← cPlace cardReady attacker .hand ⟨"WTR_204_Y"⟩
  let bruteHit ← cSteps readyWithCost (play brute :: (toDefend ++ finish))
  let bruteLink ← activeLink bruteHit
  let bruteClosed ← cSteps bruteHit passBoth
  let normal ← cSteps bruteClosed (swing :: (toDefend ++ finish))
  let normalLink ← activeLink normal
  let endPhase ← cSteps buffed passBoth
  let returnTrigger ← endPhase.pendingTriggers.head?
  let returned ← cSteps endPhase [⟨.player attacker, .pickTriggerStart attacker⟩,
    ⟨.player attacker, .pickTrigger returnTrigger.id⟩]
  let ended ← cSteps returned [⟨.player attacker, .arsenalSkip⟩]
  pure (card.status == .full && card.front.pitch == some pitch && card.front.defense == some 3 &&
    selfBuffed.zone defenderHand == ready.zone defenderHand &&
    (selfBuffed.obj? selfHidden).map (fun o => (o.kind, o.faceDown)) ==
      (ready.obj? other).map (fun o => (o.kind, true)) &&
    (paid.poolOf attacker).resources == 4 && (paid.poolOf attacker).actionPoints == 2 &&
    (buffed.poolOf attacker).actionPoints == 3 &&
    chance.pending.head? == some (.chanceShuffle defenderHand) && chance.activeEffects.length == 1 &&
    buffed.zone defenderHand == [first, second] && (buffed.obj? intimidation).any (·.faceDown) &&
    genericLink.damageDealt == 4 && beforeBrute.activeEffects == buffed.activeEffects &&
    defending.activeEffects.isEmpty && linkAttackPower defending weaponLink == 4 + bonus &&
    hitLink.damageDealt == 4 + bonus && nonEquipmentDefenderCount oneBlock oneLink == 1 &&
    linkAttackPower oneBlock oneLink == 4 + bonus && nonEquipmentDefenderCount twoBlocks twoLink == 2 &&
    (activeLink oneHit).map (·.damageDealt) == some (4 + bonus - linkTotalDefense oneBlock oneLink) &&
    (activeLink twoHit).map (·.damageDealt) == some 0 &&
    linkAttackPower twoBlocks twoLink == 4 && nonEquipmentDefenderCount resolved resolvedLink == 2 &&
    linkAttackPower resolved resolvedLink == 4 && linkAttackPower removed removedLink == 4 + bonus &&
    bruteLink.damageDealt == 7 + bonus && normalLink.damageDealt == 4 &&
    returnTrigger.source == intimidation && returned.zone banished == [] &&
    (returned.zone defenderHand).length == 3 && ended.activeEffects.isEmpty)

#guard checkBarragingBeatdown ⟨"WTR_017_R"⟩ 1 4 == some true
#guard checkBarragingBeatdown ⟨"WTR_018_Y"⟩ 2 3 == some true
#guard checkBarragingBeatdown ⟨"WTR_019_B"⟩ 3 2 == some true

/-- The printed power bonus tracks non-equipment defenders only while Brawnhide attacks. -/
meta def checkBarragingBrawnhide (cid : CardId) (pitch power : Nat) : Option Bool := do
  let attacker : PlayerId := ⟨0⟩
  let defender : PlayerId := ⟨1⟩
  let funded := m5Base.setPool attacker { actionPoints := 1, resources := 3 }
  let card ← funded.cards.find? cid
  let (withAttack, attack) ← cPlace funded attacker .hand cid
  let (withArmor, armor) ← cPlace withAttack defender .chest ⟨"WTR_041"⟩
  let (withCopy, defendingCopy) ← cPlace withArmor defender .hand cid
  let (ready, second) ← cPlace withCopy defender .hand ⟨"WTR_203_R"⟩
  let paid ← cSteps ready [⟨.player attacker, .playCard attack⟩]
  let layer ← (paid.zone .stack).head?
  let active := fun (s : GameState) => s.combat.bind CombatChain.activeLink?
  let defend := fun id => (⟨.player defender, .defendCard id⟩ : Action)
  let finish := [⟨.player defender, .defendDone⟩] ++ passBoth ++ passBoth ++ passBoth
  let defending ← cSteps paid (passBoth ++ passBoth)
  let attackLink ← active defending
  let activeAttack ← attackLink.attack
  let withEquipment ← cSteps defending [defend armor]
  let armorLink ← active withEquipment
  let withMixed ← cSteps withEquipment [defend defendingCopy]
  let mixedLink ← active withMixed
  let copy ← mixedLink.defending.getLast?
  let withTwo ← cSteps defending [defend defendingCopy, defend second]
  let twoLink ← active withTwo
  let toReturn ← twoLink.defending.head?
  let (oneRemoved, _, _) := execPrim withTwo attacker activeAttack []
    (.returnChosenDefendingCard toReturn)
  let removedLink ← active oneRemoved
  let lose : ContinuousEffect :=
    { id := 0, timestamp := ⟨0⟩, source := activeAttack, controller := defender,
      target := .obj activeAttack, op := .loseAllAbilities, duration := .thisChainLink }
  let silenced := { defending with activeEffects := [lose] }
  let hit ← cSteps defending finish
  let hitMixed ← cSteps withMixed finish
  let hitTwo ← cSteps withTwo finish
  pure (card.status == .full && card.front.pitch == some pitch && card.front.defense == some 2 &&
    (paid.poolOf attacker).resources == 0 && objEffectivePower ready attack == some (Int.ofNat power) &&
    objEffectivePower paid layer == some (Int.ofNat power) &&
    objEffectivePower defending activeAttack == some (Int.ofNat (power + 1)) &&
    objEffectivePower silenced activeAttack == some (Int.ofNat power) &&
    nonEquipmentDefenderCount withEquipment armorLink == 0 &&
    linkAttackPower withEquipment armorLink == power + 1 &&
    nonEquipmentDefenderCount withMixed mixedLink == 1 &&
    linkAttackPower withMixed mixedLink == power + 1 &&
    objEffectivePower withMixed copy == some (Int.ofNat power) && objEffectiveDefense withMixed copy == some 2 &&
    nonEquipmentDefenderCount withTwo twoLink == 2 && linkAttackPower withTwo twoLink == power &&
    nonEquipmentDefenderCount oneRemoved removedLink == 1 &&
    linkAttackPower oneRemoved removedLink == power + 1 &&
    (active hit).map (·.damageDealt) == some (power + 1) &&
    (active hitMixed).map (·.damageDealt) == some (power + 1 - linkTotalDefense withMixed mixedLink) &&
    (active hitTwo).map (·.damageDealt) == some (power - 5))

#guard checkBarragingBrawnhide ⟨"WTR_176_R"⟩ 1 7 == some true
#guard checkBarragingBrawnhide ⟨"WTR_177_Y"⟩ 2 6 == some true
#guard checkBarragingBrawnhide ⟨"WTR_178_B"⟩ 3 5 == some true

/-- Play an attack with Intimidate and use the remaining hand card to defend. -/
meta def checkIntimidateAttack (cid : CardId) (pitch cost power : Nat) (discardCost : Bool := false)
    (fromArsenal : Bool := false) : Option Bool := do
  let attacker : PlayerId := ⟨0⟩
  let defender : PlayerId := ⟨1⟩
  let funded := m5Base.setPool attacker { actionPoints := 1, resources := cost + 1 }
  let hand := Zone.player defender .hand
  let banished := Zone.player defender .banished
  let card ← funded.cards.find? cid
  let (withReserve, reserve) ← cPlace funded attacker .hand ⟨"WTR_205_B"⟩
  let origin : ZoneKind := if fromArsenal then .arsenal else .hand
  let (withAttack, attackId) ← cPlace withReserve attacker origin cid fromArsenal
  let (withFirst, first) ← cPlace withAttack defender .hand ⟨"WTR_203_R"⟩
  let (withoutSecondPaymentCard, second) ← cPlace withFirst defender .hand ⟨"WTR_204_Y"⟩
  let play : Action := ⟨.player attacker, .playCard attackId⟩
  let (ready, paid, paymentOk) ← if discardCost then do
    let (ready, paymentCard) ← cPlace withoutSecondPaymentCard attacker .hand ⟨"WTR_188_R"⟩
    let paying ← cSteps ready [play]
    let (paid, events) ← (step 64 paying ⟨.chance, .shuffleOrder [paymentCard, reserve]⟩).toOption
    let discarded ← (paid.zone (.player attacker .graveyard)).head?
    pure (ready, paid, paying.pending.head? == some (.chanceShuffle (.player attacker .hand)) &&
      paying.pendingTriggers.isEmpty && (paying.poolOf attacker).resources == 1 &&
      (paid.obj? discarded).map (·.kind) == (ready.obj? paymentCard).map (·.kind) &&
      events.contains (.discarded attacker discarded))
  else do
    let paid ← cSteps withoutSecondPaymentCard [play]
    pure (withoutSecondPaymentCard, paid, (paid.zone (.player attacker .graveyard)).isEmpty)
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
    paymentOk && paid.pendingTriggers.isEmpty && paid.zone hand == ready.zone hand &&
    paid.zone (.player attacker .hand) == [reserve] &&
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
#guard checkIntimidateAttack ⟨"WTR_006_R"⟩ 1 3 9 true == some true
#guard checkIntimidateAttack ⟨"WTR_006_R"⟩ 1 3 9 true true == some true

-- A different Brute hero cannot include Rhinar's specialization.
#guard (do
  let adult ← wtrDB.find? ⟨"WTR_001"⟩
  let young ← wtrDB.find? ⟨"WTR_002"⟩
  let other := { adult with front := { adult.front with name := "Other Brute" } }
  let cid : CardId := ⟨"WTR_006_R"⟩
  pure (decide (CardAllowedForHero wtrDB adult cid) && decide (CardAllowedForHero wtrDB young cid) &&
    !decide (CardAllowedForHero wtrDB other cid)) : Option Bool) == some true

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
#guard checkUnmovable ⟨"WTR_213_Y"⟩ 2 6 false == some true
#guard checkUnmovable ⟨"WTR_213_Y"⟩ 2 6 true == some true
#guard checkUnmovable ⟨"WTR_214_B"⟩ 3 5 false == some true
#guard checkUnmovable ⟨"WTR_214_B"⟩ 3 5 true == some true

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

/-- Rout chooses a live non-equipment defender when it resolves and preserves Reprise history. -/
meta def checkRout : Option Bool := do
  let attacker : PlayerId := ⟨0⟩
  let defender : PlayerId := ⟨1⟩
  let hand := Zone.player defender .hand
  let cid : CardId := ⟨"WTR_120_R"⟩
  let funded := (m5Base.setPool attacker { actionPoints := 1, resources := 3 }).setPool defender
    { resources := 6 }
  let card ← funded.cards.find? cid
  let (armed, weapon) ← cPlace funded attacker .weapon ⟨"WTR_115"⟩
  let (withRout, rout) ← cPlace armed attacker .hand cid
  let (withResponse, response) ← cPlace withRout attacker .hand ⟨"WTR_132_R"⟩
  let (withAttack, plain) ← cPlace withResponse attacker .hand ⟨"WTR_203_R"⟩
  let (withArmor, armor) ← cPlace withAttack defender .chest ⟨"WTR_041"⟩
  let (firstBlock, first) ← cPlace withArmor defender .hand ⟨"WTR_203_R"⟩
  let (secondBlock, second) ← cPlace firstBlock defender .hand ⟨"WTR_204_Y"⟩
  let (ready, unmovable) ← cPlace secondBlock defender .hand ⟨"WTR_212_R"⟩
  let active (s : GameState) := s.combat.bind CombatChain.activeLink?
  let play (id : ObjId) : Action := ⟨.player attacker, .playCard id⟩
  let block (id : ObjId) : Action := ⟨.player defender, .defendCard id⟩
  let pick (idx : Nat) : Action := ⟨.player attacker, .pickMode idx⟩
  let done : Action := ⟨.player defender, .defendDone⟩
  let toDefend := passBoth ++ passBoth
  let toReaction := done :: passBoth
  let defend ← cSteps ready (⟨.player attacker, .attackWeapon weapon⟩ :: toDefend)
  let blocks ← cSteps defend ([block armor, block first, block second] ++ toReaction)
  let [_, def1, def2] := (← active blocks).defending | none
  let paid ← cSteps blocks [play rout]
  let offered ← cSteps paid passBoth
  let skipped ← cSteps offered [pick 0]
  let returnedFirst ← cSteps offered [pick 1]
  let returnedSecond ← cSteps offered [pick 2]
  let link ← active returnedSecond
  let returned ← (returnedSecond.zone hand).head?
  let fromEquipment ← cSteps defend (block armor :: (toReaction ++ (play rout :: passBoth)))
  let unqualifiedAttack ← cSteps ready (play plain :: (toDefend ++ toReaction))
  let attack ← (← active paid).attack
  let invalid ← cSteps (removeNonPhysObj paid attack) passBoth
  let combat := defend.combat.map fun cc =>
    cc.updateActiveLink fun l => { l with grantedKeywords := [.dominate] }
  let dominated := { defend with combat := combat }
  let reaction ← cSteps dominated (toReaction ++ [play rout, ⟨.player attacker, .pass⟩,
    ⟨.player defender, .playCard unmovable⟩])
  let blockResolved ← cSteps reaction passBoth.reverse
  let blockLink ← active blockResolved
  let offeredAfterReaction ← cSteps blockResolved passBoth
  let returnedReaction ← cSteps offeredAfterReaction [pick 1]
  let linkAfterReaction ← active returnedReaction
  let reactionAgain ← (returnedReaction.zone hand).head?
  let reprise ← cSteps returnedReaction (play response :: passBoth)
  let target ← active reprise
  let playAgain : Action := ⟨.player defender, .playCard reactionAgain⟩
  let secondDefense ← cSteps reprise (⟨.player attacker, .pass⟩ :: playAgain :: passBoth.reverse)
  let secondLink ← active secondDefense
  pure (card.status == .full && card.front.pitch == some 1 && card.front.defense == some 3 &&
    (paid.poolOf attacker).resources == 0 && (active offered).map (·.powerBonus) == some 3 &&
    (legalActionsFor attacker offered).filter (·.kind != .concede) == [pick 0, pick 1, pick 2] &&
    (step 64 offered (pick 3)).toOption.isNone &&
    (active skipped).map (·.defending) == some [armor, def1, def2] &&
    (active returnedFirst).map (·.defending) == some [armor, def2] && link.defending == [armor, def1] &&
    link.defendedActionCount == 1 && link.defendingFromHand == [def1] &&
    link.defendedFromHandCount == 2 && returnedSecond.locate def2 == none &&
    (returnedSecond.cardDefOf? returned).map (·.id) == some ⟨"WTR_204_Y"⟩ &&
    (returnedSecond.obj? returned).any (fun obj => obj.owner == defender) &&
    (active fromEquipment).map (fun l => (l.powerBonus, l.defending)) == some (3, [armor]) &&
    !(legalActionsFor attacker fromEquipment).contains (pick 0) &&
    !(legalActionsFor attacker unqualifiedAttack).contains (play rout) &&
    (active invalid).map (fun l => (l.powerBonus, l.defending)) == some (0, [armor, def1, def2]) &&
    (legalActionsFor attacker invalid).contains (pick 0) &&
    blockLink.defendingFromHand.length == 1 &&
    (legalActionsFor attacker offeredAfterReaction).contains (pick 1) &&
    linkAfterReaction.defending.isEmpty && linkAfterReaction.defendingFromHand.isEmpty &&
    linkAfterReaction.defendedFromHandCount == 1 && target.powerBonus == 6 &&
    secondLink.defendingFromHand.length == 1 && secondLink.defendedFromHandCount == 2)

#guard checkRout == some true

/-- Optional graveyard costs bind a specific public card before pitching and pay only on success. -/
meta def checkNimbleStrike (cid : CardId) (pitch power : Nat) (fromArsenal : Bool) : Option Bool := do
  let player : PlayerId := ⟨0⟩
  let opponent : PlayerId := ⟨1⟩
  let graveyard := Zone.player player .graveyard
  let banished := Zone.player player .banished
  let origin : ZoneKind := if fromArsenal then .arsenal else .hand
  let card ← m5Base.cards.find? cid
  let (withStrike, strike) ← cPlace m5Base player origin cid fromArsenal
  let (withDiscard, inHand) ← cPlace withStrike player .hand ⟨"WTR_220_B"⟩
  let (withOpposing, opposing) ← cPlace withDiscard opponent .graveyard ⟨"WTR_218_R"⟩
  let (withWrong, wrong) ← cPlace withOpposing player .graveyard ⟨"WTR_188_R"⟩
  let (withFirst, first) ← cPlace withWrong player .graveyard ⟨"WTR_218_R"⟩
  let (ready, second) ← cPlace withFirst player .graveyard ⟨"WTR_219_Y"⟩
  let (withPitch, pitchId) ← cPlace ready player .hand ⟨"WTR_205_B"⟩
  let play : Action := ⟨.player player, .playCard strike⟩
  let pick (choice : Option ObjId) : Action := ⟨.player player, .pickGraveyardCost choice⟩
  let cancel : Action := ⟨.player player, .cancelPlay⟩
  let funded (s : GameState) := s.setPool player { actionPoints := 1, resources := 1 }
  let decision ← cSteps withPitch [play]
  let atPitch ← cSteps decision [pick (some first)]
  let rolledBack ← cSteps atPitch [cancel]
  let (cannotPay, _) ← moveObj ready inHand (.player player .deck) .top false
  let failed ← cSteps cannotPay [play, pick (some first)]
  let declined ← cSteps (funded ready) [play, pick none]
  let noChoice ← cSteps (funded withWrong) [play]
  let (paid, events) ← (step 64 atPitch ⟨.player player, .pitchCard pitchId⟩).toOption
  let paidId ← (paid.zone banished).head?
  let effectAttack (s : GameState) := cSteps s (passBoth ++ passBoth ++ [⟨.player opponent, .defendDone⟩] ++
    passBoth ++ passBoth ++ passBoth)
  let paidDamage ← effectAttack paid
  let declinedDamage ← effectAttack declined
  let noChoiceDamage ← effectAttack noChoice
  let link ← paidDamage.combat.bind CombatChain.activeLink?
  pure (card.status == .full && card.front.pitch == some pitch && card.front.defense == some 2 &&
    (legalActionsFor player decision).contains (pick (some first)) &&
    (legalActionsFor player decision).contains (pick (some second)) &&
    (step 64 decision (pick (some wrong))).toOption.isNone &&
    (step 64 decision (pick (some inHand))).toOption.isNone &&
    (step 64 decision (pick (some opposing))).toOption.isNone &&
    atPitch.zone graveyard == ready.zone graveyard && (atPitch.zone banished).isEmpty &&
    decide (rolledBack = withPitch) && decide (failed = cannotPay) && paid.zone graveyard == [second, wrong] &&
    events.contains (.moved first paidId graveyard banished) && events.contains (.banished player paidId false) &&
    (paid.cardDefOf? paidId).map (·.id) == some ⟨"WTR_218_R"⟩ &&
    (paid.poolOf player).resources == 2 && link.additionalCostPaid && link.powerBonus == 1 &&
    link.damageDealt == power + 1 && linkHasKeyword paidDamage link .goAgain &&
    (paidDamage.poolOf player).actionPoints == 1 &&
    declined.zone graveyard == ready.zone graveyard && (declined.zone banished).isEmpty &&
    (declinedDamage.poolOf player).actionPoints == 0 && (noChoiceDamage.poolOf player).actionPoints == 0 &&
    declinedDamage.lifeOf opponent == 40 - Int.ofNat power &&
    noChoiceDamage.lifeOf opponent == 40 - Int.ofNat power)

#guard checkNimbleStrike ⟨"WTR_185_R"⟩ 1 4 false == some true
#guard checkNimbleStrike ⟨"WTR_185_R"⟩ 1 4 true == some true
#guard checkNimbleStrike ⟨"WTR_186_Y"⟩ 2 3 false == some true
#guard checkNimbleStrike ⟨"WTR_186_Y"⟩ 2 3 true == some true

/-- Shunt deals one point of generic damage as it resolves against a weapon. -/
meta def checkSteelbladeShunt (cid : CardId) (pitch defense : Nat) (fromArsenal : Bool) :
    Option Bool := do
  let attacker : PlayerId := ⟨0⟩
  let defender : PlayerId := ⟨1⟩
  let origin : ZoneKind := if fromArsenal then .arsenal else .hand
  let funded := (m5Base.setPool attacker { actionPoints := 1, resources := 4 }).setPool defender
    { resources := 1 }
  let card ← funded.cards.find? cid
  let (withReaction, reaction) ← cPlace funded defender origin cid fromArsenal
  let (equipped, weapon) ← cPlace withReaction attacker .weapon ⟨"WTR_115"⟩
  let (ready, attackCard) ← cPlace equipped attacker .hand ⟨"WTR_188_R"⟩
  let activeLink := fun (s : GameState) => s.combat.bind CombatChain.activeLink?
  let toDefend := passBoth ++ passBoth
  let toOffer := [⟨.player defender, .defendDone⟩] ++ passBoth ++ [⟨.player attacker, .pass⟩]
  let play : Action := ⟨.player defender, .playCard reaction⟩
  let resolve := fun (s : GameState) => do
    let passed ← cSteps s [⟨.player defender, .pass⟩]
    (step 64 passed ⟨.player attacker, .pass⟩).toOption
  let defending ← cSteps ready (⟨.player attacker, .attackWeapon weapon⟩ :: toDefend)
  let offered ← cSteps defending toOffer
  let paid ← cSteps offered [play]
  let paidLink ← activeLink paid
  let (resolved, events) ← resolve paid
  let link ← activeLink resolved
  let defendingCard ← link.defending.head?
  let shuntDamage : Event := .damageDealt attacker .generic 1
  let damageOutput ← cSteps resolved passBoth
  let closed ← cSteps damageOutput (passBoth ++ passBoth)
  let grave := closed.zone (.player defender .graveyard)
  let (lethal, lethalEvents) ← resolve (paid.setLife attacker 1)
  let (shielded, _, _) := execPrim paid attacker ⟨0⟩ []
    (.preventNextDamage .controller (.const 1) .thisTurn)
  let (prevented, preventedEvents) ← resolve shielded
  let (cardDefense, cardEvents) ←
    (cSteps ready (⟨.player attacker, .playCard attackCard⟩ :: (toDefend ++ toOffer ++ [play]))).bind resolve
  let cardLink ← activeLink cardDefense
  let cardDamage ← cSteps cardDefense passBoth
  let nonweapon ← ready.objectFace? attackCard
  let changeType : ContinuousEffect :=
    { id := paid.nextTimestamp, timestamp := ⟨paid.nextTimestamp⟩, source := weapon,
      controller := attacker, target := .obj weapon, duration := .thisChainLink, op := .copyFace nonweapon }
  let (nonweaponDefense, nonweaponEvents) ← resolve { paid with activeEffects := [changeType] }
  pure (card.status == .full && card.front.pitch == some pitch &&
    card.front.defense == some (Int.ofNat defense) &&
    (step 64 defending ⟨.player defender, .defendCard reaction⟩).toOption.isNone &&
    (paid.poolOf defender).resources == 0 && paid.lifeOf attacker == 40 && paidLink.defending.isEmpty &&
    resolved.combat.map (·.step) == some .reaction && link.attackSource == some weapon &&
    resolved.lifeOf attacker == 39 && resolved.lifeOf defender == 40 &&
    events.countP (· == shuntDamage) == 1 && link.defending == [defendingCard] &&
    (resolved.cardDefOf? defendingCard).map (·.id) == some cid &&
    linkTotalDefense resolved link == defense &&
    link.defendedFromHandCount == (if fromArsenal then 0 else 1) &&
    damageOutput.lifeOf defender == 40 && closed.combat.isNone &&
    grave.map (fun id => (closed.cardDefOf? id).map (·.id)) == [some cid] &&
    lethal.lifeOf attacker == 0 && lethal.lifeOf defender == 40 &&
    lethal.result == some (.won [defender]) && (legalActions lethal).isEmpty &&
    lethalEvents.countP (· == shuntDamage) == 1 &&
    prevented.lifeOf attacker == 40 && !preventedEvents.contains shuntDamage &&
    (activeLink prevented).map (linkTotalDefense prevented) == some defense &&
    cardDefense.lifeOf attacker == 40 && !cardEvents.contains shuntDamage &&
    linkTotalDefense cardDefense cardLink == defense &&
    cardDamage.lifeOf defender == 40 - Int.ofNat (7 - defense) &&
    nonweaponDefense.lifeOf attacker == 40 && !nonweaponEvents.contains shuntDamage &&
    (activeLink nonweaponDefense).map (linkTotalDefense nonweaponDefense) == some defense)

#guard checkSteelbladeShunt ⟨"WTR_126_R"⟩ 1 6 false == some true
#guard checkSteelbladeShunt ⟨"WTR_126_R"⟩ 1 6 true == some true
#guard checkSteelbladeShunt ⟨"WTR_127_Y"⟩ 2 5 false == some true
#guard checkSteelbladeShunt ⟨"WTR_127_Y"⟩ 2 5 true == some true
#guard checkSteelbladeShunt ⟨"WTR_128_B"⟩ 3 4 false == some true
#guard checkSteelbladeShunt ⟨"WTR_128_B"⟩ 3 4 true == some true

-- The first reaction on the stack fails to resolve if another reaction has already defended Dominate.
#guard (do
  let attacker : PlayerId := ⟨0⟩
  let defender : PlayerId := ⟨1⟩
  let funded := (m5Base.setPool attacker { actionPoints := 1, resources := 1 }).setPool defender
    { resources := 1 }
  let (withWeapon, weapon) ← cPlace funded attacker .weapon ⟨"WTR_115"⟩
  let (withShunt, shunt) ← cPlace withWeapon defender .hand ⟨"WTR_126_R"⟩
  let (ready, sink) ← cPlace withShunt defender .hand ⟨"WTR_217_B"⟩
  let defending ← cSteps ready ([⟨.player attacker, .attackWeapon weapon⟩] ++ passBoth ++ passBoth)
  let combat := defending.combat.map fun cc =>
    cc.updateActiveLink fun link => { link with grantedKeywords := [.dominate] }
  let dominated := { defending with combat := combat }
  let stacked ← cSteps dominated ([⟨.player defender, .defendDone⟩] ++ passBoth ++
    [⟨.player attacker, .pass⟩, ⟨.player defender, .playCard shunt⟩, ⟨.player defender, .playCard sink⟩])
  let upperResolved ← cSteps stacked [⟨.player defender, .pass⟩, ⟨.player attacker, .pass⟩]
  let resolved ← cSteps upperResolved passBoth
  let link ← resolved.combat.bind CombatChain.activeLink?
  let grave := resolved.zone (.player defender .graveyard)
  pure (resolved.lifeOf attacker == 40 && linkTotalDefense resolved link == 2 &&
    grave.map (fun id => (resolved.cardDefOf? id).map (·.id)) == [some ⟨"WTR_126_R"⟩]) :
    Option Bool) == some true

/-- Verify Reckless Swing's additional cost and damage during Reaction Step. -/
meta def checkRecklessSwing (fromArsenal : Bool) : Option Bool := do
  let attacker : PlayerId := ⟨0⟩
  let defender : PlayerId := ⟨1⟩
  let hand := Zone.player defender .hand
  let grave := Zone.player defender .graveyard
  let cid : CardId := ⟨"WTR_008_B"⟩
  let origin : ZoneKind := if fromArsenal then .arsenal else .hand
  let funded := m5Base.setPool attacker { actionPoints := 1, resources := 3 }
  let card ← funded.cards.find? cid
  let (withAttack, attack) ← cPlace funded attacker .hand ⟨"WTR_188_R"⟩
  let (bare, reaction) ← cPlace withAttack defender origin cid fromArsenal
  let play : Action := ⟨.player defender, .playCard reaction⟩
  let toReaction := [⟨.player attacker, .playCard attack⟩] ++ passBoth ++ passBoth ++
    [⟨.player defender, .defendDone⟩] ++ passBoth ++ [⟨.player attacker, .pass⟩]
  let offeredBare ← cSteps bare toReaction
  let rejected ← cSteps offeredBare [play]
  let (withHigh, high) ← cPlace bare defender .hand ⟨"WTR_189_Y"⟩
  let (ready, low) ← cPlace withHigh defender .hand ⟨"WTR_190_B"⟩
  let paying ← cSteps ready (toReaction ++ [play])
  let paidHigh ← cSteps paying [⟨.chance, .shuffleOrder [high, low]⟩]
  let paidLow ← cSteps paying [⟨.chance, .shuffleOrder [low, high]⟩]
  let resolve := fun (s : GameState) => do
    let passed ← cSteps s [⟨.player defender, .pass⟩]
    (step 64 passed ⟨.player attacker, .pass⟩).toOption
  let (highResolved, highEvents) ← resolve paidHigh
  let (lowResolved, lowEvents) ← resolve paidLow
  let (lethal, _) ← resolve (paidHigh.setLife attacker 2)
  let highLink ← highResolved.combat.bind CombatChain.activeLink?
  let lowLink ← lowResolved.combat.bind CombatChain.activeLink?
  let highDamage ← cSteps highResolved passBoth
  let lowDamage ← cSteps lowResolved passBoth
  let highDiscard ← (paidHigh.zone grave).head?
  let lowDiscard ← (paidLow.zone grave).head?
  let reactionDamage : Event := .damageDealt attacker .generic 2
  pure (card.status == .full && card.front.pitch == some 3 && card.front.defense == some 4 &&
    decide (rejected = offeredBare) && paying.pending.head? == some (.chanceShuffle hand) &&
    paidHigh.lifeOf attacker == 40 && paidLow.lifeOf attacker == 40 &&
    paidHigh.zone hand == [low] && paidLow.zone hand == [high] &&
    (paidHigh.cardDefOf? highDiscard).map (·.id) == some ⟨"WTR_189_Y"⟩ &&
    (paidLow.cardDefOf? lowDiscard).map (·.id) == some ⟨"WTR_190_B"⟩ &&
    highResolved.lifeOf attacker == 38 && lowResolved.lifeOf attacker == 40 &&
    highEvents.countP (· == reactionDamage) == 1 && !lowEvents.contains reactionDamage &&
    lethal.result == some (.won [defender]) && lethal.lifeOf defender == 40 &&
    highResolved.combat.map (·.step) == some .reaction &&
    linkTotalDefense highResolved highLink == 4 && linkTotalDefense lowResolved lowLink == 4 &&
    highDamage.lifeOf defender == 37 && lowDamage.lifeOf defender == 37)

#guard checkRecklessSwing false == some true
#guard checkRecklessSwing true == some true

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

/-- Buckling Blow targets equipment when Crush is stacked and rechecks it when resolving. -/
meta def checkBucklingBlow (cid : CardId) (pitch power : Nat) : Option Bool := do
  let attacker : PlayerId := ⟨0⟩
  let defender : PlayerId := ⟨1⟩
  let chest := Zone.player defender .chest
  let grave := Zone.player defender .graveyard
  let funded := m5Base.setPool attacker { actionPoints := 1, resources := 4 }
  let card ← funded.cards.find? cid
  let (bare, attack) ← cPlace funded attacker .hand cid
  let (ownArmor, own) ← cPlace bare attacker .head ⟨"WTR_155"⟩
  let (withArmor, armor) ← cPlace ownArmor defender .chest ⟨"WTR_005"⟩
  let (withHood, hood) ← cPlace withArmor defender .head ⟨"WTR_151"⟩
  let (ready, hidden) ← cPlace withHood defender .arms ⟨"WTR_157"⟩ true
  let enter := ⟨.player attacker, .playCard attack⟩ :: (passBoth ++ passBoth)
  let hit := ⟨.player defender, .defendDone⟩ :: (passBoth ++ passBoth)
  let defending ← cSteps ready (enter ++ [⟨.player defender, .defendCard armor⟩])
  let prevent (n : Nat) :=
    (execPrim defending defender ⟨0⟩ [] (.preventNextDamage .controller (.const n) .thisTurn)).1
  let crushed ← cSteps (prevent (power - 5)) hit
  let short ← cSteps (prevent (power - 4)) hit
  let noTargets ← cSteps bare (enter ++ hit)
  let trigger ← crushed.pendingTriggers.head?
  let choosing ← cSteps crushed [⟨.player attacker, .pickTriggerStart attacker⟩]
  let target (id : ObjId) : Action := ⟨.player attacker, .pickTrigger trigger.id none (some id)⟩
  let (stacked, events) ← (step 64 choosing (target armor)).toOption
  let layer ← (stacked.zone .stack).head?
  let resolved ← cSteps stacked passBoth
  let closed ← cSteps resolved (passBoth ++ passBoth)
  let targetHood ← cSteps choosing [target hood]
  let resolvedHood ← cSteps targetHood passBoth
  let spentHood ← cSteps targetHood [⟨.player attacker, .pass⟩,
    ⟨.player defender, .activateAbility hood 0⟩, ⟨.player defender, .pass⟩, ⟨.player attacker, .pass⟩]
  let cancelled ← cSteps spentHood (⟨.chance, .shuffleOrder []⟩ :: passBoth)
  let removed ← (cancelled.zone grave).head?
  let counters (s : GameState) (id : ObjId) := (s.obj? id).map (·.minusDefenseCounters)
  pure (card.status == .full && card.front.pitch == some pitch && card.front.defense == some 3 &&
    (defending.poolOf attacker).resources == 0 &&
    crushed.lifeOf defender == 36 && short.lifeOf defender == 37 && short.pendingTriggers.isEmpty &&
    noTargets.lifeOf defender == 40 - Int.ofNat power && noTargets.pendingTriggers.isEmpty &&
    !(legalActionsFor attacker noTargets).any (fun a => match a.kind with | .pickTriggerStart _ => true | _ => false) &&
    (choosing.zone .combatChain).contains armor && legalFrameActions choosing == [target armor, target hood] &&
    (step 64 choosing (target own)).toOption.isNone && (step 64 choosing (target hidden)).toOption.isNone &&
    (step 64 choosing ⟨.player attacker, .pickTrigger trigger.id⟩).toOption.isNone &&
    (step 64 choosing ⟨.player defender, .pickTrigger trigger.id none (some armor)⟩).toOption.isNone &&
    events == [.targetedEquipment layer armor] && counters stacked armor == some 0 &&
    counters resolved armor == some 1 && counters resolved hood == some 0 &&
    closed.zone chest == [armor] && counters closed armor == some 2 &&
    counters resolvedHood hood == some 1 && counters resolvedHood armor == some 0 &&
    (cancelled.cardDefOf? removed).map (·.id) == some ⟨"WTR_151"⟩ &&
    counters cancelled removed == some 0 && counters cancelled armor == some 0 &&
    (cancelled.zone .stack).isEmpty)

#guard checkBucklingBlow ⟨"WTR_057_R"⟩ 1 8 == some true
#guard checkBucklingBlow ⟨"WTR_058_Y"⟩ 2 7 == some true
#guard checkBucklingBlow ⟨"WTR_059_B"⟩ 3 6 == some true

/-- Sand Sketched Plan searches without revealing and discards before shuffling the deck. -/
meta def checkSandSketchedPlan : Option Bool := do
  let player : PlayerId := ⟨0⟩
  let opponent : PlayerId := ⟨1⟩
  let cid : CardId := ⟨"WTR_009_B"⟩
  let highCid : CardId := ⟨"WTR_014_R"⟩
  let lowCid : CardId := ⟨"WTR_015_Y"⟩
  let hand := Zone.player player .hand
  let deck := Zone.player player .deck
  let grave := Zone.player player .graveyard
  let card ← m5Base.cards.find? cid
  let (withRhinar, rhinar) ← cPlace m5Base player .hero ⟨"WTR_001"⟩
  let (withOpponent, opponentCard) ← cPlace withRhinar opponent .hand ⟨"WTR_203_R"⟩
  let (bare, plan) ← cPlace withOpponent player .hand cid
  let (withLow, low) ← cPlace bare player .hand lowCid
  let (withBottom, bottom) ← cPlace withLow player .deck ⟨"WTR_205_B"⟩
  let (withHigh, high) ← cPlace withBottom player .deck highCid
  let (ready, top) ← cPlace withHigh player .deck ⟨"WTR_203_R"⟩
  let play := ⟨.player player, .playCard plan⟩ :: passBoth
  let choose (id : ObjId) : Action := ⟨.player player, .pickShuffleCard (some id)⟩
  let done : Action := ⟨.player player, .pickShuffleCard none⟩
  let shuffle (ids : List ObjId) : Action := ⟨.chance, .shuffleOrder ids⟩
  let picking ← cSteps ready play
  let chosen ← cSteps picking [choose high]
  let (randomDiscard, searchEvents) ← (step 64 chosen done).toOption
  let inHand ← (randomDiscard.zone hand).head?
  let (highDiscard, discardEvents) ← (step 64 randomDiscard (shuffle [inHand, low])).toOption
  let highInGrave ← (highDiscard.zone grave).head?
  let lowDiscard ← cSteps randomDiscard [shuffle [low, inHand]]
  let lowInGrave ← (lowDiscard.zone grave).head?
  let reward ← cSteps highDiscard [shuffle [bottom, top]]
  let trigger ← reward.pendingTriggers.head?
  let intimidation ← cSteps reward ([⟨.player player, .pickTriggerStart player⟩,
    ⟨.player player, .pickTrigger trigger.id (some opponent)⟩] ++ passBoth)
  let noReward ← cSteps lowDiscard [shuffle [top, bottom]]
  let empty ← cSteps bare play
  let emptyDone ← cSteps empty [shuffle []]
  let (emptyDeck, _) ← cPlace bare player .hand highCid
  let discardedWithoutSearch ← cSteps emptyDeck play
  let rewardedWithoutSearch ← cSteps discardedWithoutSearch [shuffle []]
  let (withOne, only) ← cPlace bare player .deck highCid
  let forcedDiscard ← cSteps withOne (play ++ [choose only, done])
  let singleReward ← cSteps forcedDiscard [shuffle []]
  pure (card.status == .full && card.front.pitch == some 3 && card.front.defense == some 3 &&
    card.front.keywords.contains (.specialization "Rhinar") &&
    (view player picking).selectionChoices.length == 3 && (view opponent picking).selectionChoices.isEmpty &&
    (step 64 picking done).toOption.isNone &&
    (randomDiscard.cardDefOf? inHand).map (·.id) == some highCid &&
    searchEvents == [.moved high inHand deck hand] &&
    randomDiscard.pending.head? == some (.chanceShuffle hand) && randomDiscard.zone deck == [top, bottom] &&
    highDiscard.pending.head? == some (.chanceShuffle deck) && lowDiscard.pending.head? == some (.chanceShuffle deck) &&
    discardEvents.contains (.discarded player highInGrave) &&
    (highDiscard.cardDefOf? highInGrave).map (·.id) == some highCid &&
    (lowDiscard.cardDefOf? lowInGrave).map (·.id) == some lowCid &&
    (highDiscard.poolOf player).actionPoints == 0 && (lowDiscard.poolOf player).actionPoints == 0 &&
    reward.zone deck == [bottom, top] && reward.zone hand == [low] &&
    (reward.poolOf player).actionPoints == 2 && (noReward.poolOf player).actionPoints == 0 &&
    noReward.zone hand == [inHand] && (reward.zone .stack).isEmpty &&
    trigger.source == rhinar && noReward.pendingTriggers.isEmpty &&
    reward.zone (.player opponent .hand) == [opponentCard] &&
    intimidation.zone (.player opponent .hand) == [] &&
    (intimidation.zone (.player opponent .banished)).length == 1 &&
    empty.pending.head? == some (.chanceShuffle deck) && (emptyDone.poolOf player).actionPoints == 0 &&
    discardedWithoutSearch.zone hand == [] && (discardedWithoutSearch.zone grave).length == 1 &&
    (rewardedWithoutSearch.poolOf player).actionPoints == 2 &&
    forcedDiscard.pending.head? == some (.chanceShuffle deck) && (forcedDiscard.zone grave).length == 1 &&
    (singleReward.poolOf player).actionPoints == 2)

#guard checkSandSketchedPlan == some true

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

/-- Cranial Crush suppresses only draws during the damaged player's next action phase. -/
meta def checkCranialCrush : Option Bool := do
  let attacker : PlayerId := ⟨0⟩
  let defender : PlayerId := ⟨1⟩
  let cid : CardId := ⟨"WTR_045_B"⟩
  let deck := Zone.player defender .deck
  let hand := Zone.player defender .hand
  let base := m5Base.setPool attacker { actionPoints := 1, resources := 6 }
  let card ← base.cards.find? cid
  let (withAttack, attack) ← cPlace { base with pending := base.pending ++ [.beginTurn] } attacker .hand cid
  let (withTome, tome) ← cPlace withAttack defender .arsenal ⟨"WTR_160_Y"⟩ true
  let (withPitch, pitch) ← cPlace withTome defender .hand ⟨"WTR_205_B"⟩
  let (withDeck, _) ← (List.replicate 7 ⟨"WTR_048_R"⟩).foldlM
    (fun (s, _) cardId => cPlace s defender .deck cardId) (withPitch, pitch)
  let (ready, _) ← (List.replicate 5 ⟨"WTR_203_R"⟩).foldlM
    (fun (s, _) cardId => cPlace s attacker .deck cardId) (withDeck, attack)
  let defend ← cSteps ready (⟨.player attacker, .playCard attack⟩ :: (passBoth ++ passBoth))
  let finish := ⟨.player defender, .defendDone⟩ :: (passBoth ++ passBoth)
  let prevent (damage : Nat) :=
    (execPrim defend defender ⟨0⟩ [] (.preventNextDamage .controller (.const damage) .thisTurn)).1
  let hit ← cSteps (prevent 4) finish
  let short ← cSteps (prevent 5) finish
  let trigger ← hit.pendingTriggers.head?
  let link ← hit.combat.bind CombatChain.activeLink?
  let stacked ← cSteps hit [⟨.player attacker, .pickTriggerStart attacker⟩, ⟨.player attacker, .pickTrigger trigger.id⟩]
  let waiting ← cSteps stacked passBoth
  let restricted ← cSteps waiting (List.replicate 3 passBoth).flatten
  let play : Action := ⟨.player defender, .playCard tome⟩
  let paid ← cSteps restricted [play, ⟨.player defender, .pitchCard pitch⟩, ⟨.player defender, .pass⟩]
  let (tomed, tomeEvents) ← (step 64 paid ⟨.player attacker, .pass⟩).toOption
  let pitched ← (tomed.zone (.player defender .pitch)).head?
  let afterTurn ← cSteps tomed (passBoth.reverse ++ [⟨.player defender, .arsenalSkip⟩,
    ⟨.player defender, .pitchReturnPick pitched⟩])
  let later ← cSteps afterTurn (passBoth ++ [⟨.player attacker, .arsenalSkip⟩])
  let top ← (restricted.zone deck).head?
  let (movedDirectly, _) ← moveObj restricted top hand .top false
  let affects (s : GameState) (p : PlayerId) := s.hasActionPhaseEffect p .cantDrawCards
  let another := (attackDamageTriggers hit { link with defender := ⟨3⟩ }).head?
  pure (card.status == .full && card.front.pitch == some 3 && card.front.defense == some 3 &&
    hit.lifeOf defender == 36 && short.lifeOf defender == 37 && short.pendingTriggers.isEmpty &&
    another.map (·.effect) ==
      some (.grant (.hero (.seated ⟨3⟩)) .cantDrawCards .nextActionPhase) &&
    waiting.activeEffects.map (fun e => (e.target, e.duration)) == [(.player defender, .nextActionPhase)] &&
    !affects waiting defender && (drawOne waiting defender).2.any (fun e => match e with | .drawn _ _ => true | _ => false) &&
    restricted.active == some defender && affects restricted defender && !affects restricted attacker &&
    (restricted.zone hand).length == 4 && (drawOne restricted defender).2 == [] &&
    (drawOne restricted attacker).2.any (fun e => match e with | .drawn _ _ => true | _ => false) &&
    (movedDirectly.zone hand).length == 5 &&
    (legalActionsFor defender restricted).contains play && tomed.zone deck == restricted.zone deck &&
    (tomed.zone hand).length == 3 && tomed.lifeOf defender == 39 && tomeEvents.contains (.lifeGained defender 3) &&
    !tomeEvents.any (fun e => match e with | .drawn _ _ => true | _ => false) &&
    afterTurn.activeEffects.isEmpty && (afterTurn.zone hand).length == 4 &&
    later.active == some defender && !affects later defender && (drawOne later defender).2.length == 2)

#guard checkCranialCrush == some true

/-- Spinal Crush removes printed and granted Go Again while leaving direct action-point gains intact. -/
meta def checkSpinalCrush : Option Bool := do
  let attacker : PlayerId := ⟨0⟩
  let defender : PlayerId := ⟨1⟩
  let cid : CardId := ⟨"WTR_044_R"⟩
  let base := m5Base.setPool attacker { actionPoints := 1, resources := 5 }
  let card ← base.cards.find? cid
  let (withAttack, spinal) ← cPlace { base with pending := base.pending ++ [.beginTurn] } attacker .hand cid
  let (withAttackAction, surge) ← cPlace withAttack defender .hand ⟨"WTR_107_R"⟩
  let (withAction, driving) ← cPlace withAttackAction defender .hand ⟨"WTR_144_R"⟩
  let (withPlain, plain) ← cPlace withAction defender .hand ⟨"WTR_203_R"⟩
  let (withWeapon, dagger) ← cPlace withPlain defender .weapon ⟨"WTR_078"⟩
  let (withChest, strap) ← cPlace withWeapon defender .chest ⟨"WTR_152"⟩
  let (withLegs, scalers) ← cPlace withChest defender .legs ⟨"WTR_154"⟩
  let (ready, potion) ← cPlace withLegs defender .permanent ⟨"WTR_172_B"⟩
  let defending ← cSteps ready (⟨.player attacker, .playCard spinal⟩ :: (passBoth ++ passBoth))
  let finish := ⟨.player defender, .defendDone⟩ :: (passBoth ++ passBoth)
  let prevent (n : Nat) :=
    (execPrim defending defender ⟨0⟩ [] (.preventNextDamage .controller (.const n) .thisTurn)).1
  let hit ← cSteps (prevent 5) finish
  let short ← cSteps (prevent 6) finish
  let trigger ← hit.pendingTriggers.head?
  let waiting ← cSteps hit ([⟨.player attacker, .pickTriggerStart attacker⟩,
    ⟨.player attacker, .pickTrigger trigger.id⟩] ++ passBoth)
  let nextTurn (s : GameState) := cSteps s (List.replicate 3 passBoth).flatten
  let restricted ← nextTurn waiting
  let noRestriction ← nextTurn short
  let funded (s : GameState) := s.setPool defender { actionPoints := 1, resources := 3 }
  let play (id : ObjId) : Action := ⟨.player defender, .playCard id⟩
  let revPass := passBoth.reverse
  let enter (action : Action) := action :: (revPass ++ revPass)
  let done : Action := ⟨.player attacker, .defendDone⟩
  let finishAttack := done :: (List.replicate 3 revPass).flatten
  let surgeBlocked ← cSteps (funded restricted) (enter (play surge) ++ finishAttack)
  let surgeNormal ← cSteps (funded noRestriction) (enter (play surge) ++ finishAttack)
  let drink ← cSteps (funded restricted) (⟨.player defender, .activateAbility potion 0⟩ :: revPass)
  let boosted ← cSteps drink (play driving :: revPass)
  let swung ← cSteps boosted (enter ⟨.player defender, .attackWeapon dagger⟩ ++ finishAttack)
  let weaponLink ← swung.combat.bind CombatChain.activeLink?
  let otherAction ← cSteps (funded restricted) (⟨.player defender, .activateAbility strap 0⟩ :: revPass)
  let reaction ← cSteps (funded restricted) (enter (play plain) ++ [done] ++ revPass)
  let plainLink ← reaction.combat.bind CombatChain.activeLink?
  let plainId ← plainLink.attack
  let granted ← cSteps reaction (⟨.player defender, .activateAbility scalers 0 (some plainId)⟩ :: revPass)
  let afterGrant ← granted.combat.bind CombatChain.activeLink?
  let otherTurn ← cSteps restricted (revPass ++ [⟨.player defender, .arsenalSkip⟩])
  let later ← cSteps otherTurn passBoth
  let affected (s : GameState) := s.hasActionPhaseEffect defender .cantGainGoAgain
  let hasKeyword (s : GameState) (id : ObjId) :=
    (s.characteristics id).any (fun chars => chars.keywords.contains .goAgain)
  pure (card.status == .full && card.front.pitch == some 1 && card.front.defense == some 3 &&
    hit.lifeOf defender == 36 && short.lifeOf defender == 37 && short.pendingTriggers.isEmpty &&
    !affected waiting && hasKeyword waiting surge && affected restricted && !hasKeyword restricted surge &&
    !affected noRestriction && hasKeyword noRestriction surge &&
    (surgeBlocked.poolOf defender).actionPoints == 0 && (surgeNormal.poolOf defender).actionPoints == 1 &&
    (drink.poolOf defender).actionPoints == 2 && (boosted.poolOf defender).actionPoints == 1 &&
    weaponLink.powerBonus == 3 && weaponLink.damageDealt == 4 &&
    !linkHasKeyword swung weaponLink .goAgain && (swung.poolOf defender).actionPoints == 0 &&
    (otherAction.poolOf defender).actionPoints == 0 && (otherAction.zone (.player defender .chest)).isEmpty &&
    otherAction.activeEffects.any (fun e => e.op == .subCostRes 2) &&
    !linkHasKeyword granted afterGrant .goAgain && !afterGrant.grantedKeywords.contains .goAgain &&
    (granted.zone (.player defender .legs)).isEmpty &&
    later.active == some defender && !affected later && hasKeyword later surge)

#guard checkSpinalCrush == some true

/-- Crush Confidence removes only the damaged hero's abilities through their next End Phase. -/
meta def checkCrushConfidence (cid : CardId) (pitch power : Nat) : Option Bool := do
  let attacker : PlayerId := ⟨0⟩
  let defender : PlayerId := ⟨1⟩
  let base := m5Base.setPool attacker { actionPoints := 1, resources := 3 }
  let card ← base.cards.find? cid
  let (withAttack, attack) ← cPlace { base with pending := base.pending ++ [.beginTurn] } attacker .hand cid
  let (withOwn, own) ← cPlace withAttack attacker .hero ⟨"WTR_038"⟩
  let (withHero, hero) ← cPlace withOwn defender .hero ⟨"WTR_038"⟩
  let (withTunic, tunic) ← cPlace withHero defender .chest ⟨"WTR_150"⟩
  let charged := updateSingleObject withTunic tunic (fun o => o.addCounterVal .energy 3)
  let (ready, _) ← cPlace charged defender .hand ⟨"WTR_203_R"⟩
  let defending ← cSteps ready (⟨.player attacker, .playCard attack⟩ :: (passBoth ++ passBoth))
  let finish := ⟨.player defender, .defendDone⟩ :: (passBoth ++ passBoth)
  let prevent (n : Nat) :=
    (execPrim defending defender ⟨0⟩ [] (.preventNextDamage .controller (.const n) .thisTurn)).1
  let hit ← cSteps (prevent (power - 4)) finish
  let short ← cSteps (prevent (power - 3)) finish
  let trigger ← hit.pendingTriggers.head?
  let resolved ← cSteps hit ([⟨.player attacker, .pickTriggerStart attacker⟩,
    ⟨.player attacker, .pickTrigger trigger.id⟩] ++ passBoth)
  let nextTurn (s : GameState) := cSteps s (List.replicate 3 passBoth).flatten
  let restricted ← nextTurn resolved
  let normal ← nextTurn short
  let funded (s : GameState) := s.setPool defender { actionPoints := 1, resources := 2 }
  let activate : Action := ⟨.player defender, .activateAbility hero 0⟩
  let useGear : Action := ⟨.player defender, .activateAbility tunic 1⟩
  let gearResolved ← cSteps restricted (useGear :: passBoth.reverse)
  let ending ← cSteps restricted passBoth.reverse
  let afterTurn ← cSteps ending [⟨.player defender, .arsenalSkip⟩]
  let later ← cSteps afterTurn passBoth
  let regained ← cSteps (funded later) (activate :: passBoth.reverse)
  let loses (s : GameState) (id : ObjId) := (s.characteristics id).any (·.abilitiesLost)
  let stats (s : GameState) := (s.characteristics hero).map (fun c => (c.name, c.life, c.intellect))
  let sameTurn := applyChainLinkMod { restricted with activeEffects := [] } attacker attack []
    (.hero (.seated defender)) .loseAllAbilities .untilEndOfNextTurn
  let stillActive := sameTurn.finishTurnEffects
  let future := { stillActive with turn := stillActive.turn + 1 }
  pure (card.status == .full && card.front.pitch == some pitch && card.front.defense == some 3 &&
    (defending.poolOf attacker).resources == 0 && hit.lifeOf defender == 36 && short.lifeOf defender == 37 &&
    short.pendingTriggers.isEmpty && !loses hit hero && loses resolved hero && !loses resolved own &&
    stats resolved == stats ready && !loses normal hero && (legalActionsFor defender (funded normal)).contains activate &&
    restricted.active == some defender && loses restricted hero && !loses restricted tunic &&
    !(legalActionsFor defender (funded restricted)).contains activate &&
    (step 64 (funded restricted) activate).toOption.isNone &&
    (legalActionsFor defender restricted).contains useGear && (gearResolved.poolOf defender).resources == 1 &&
    ending.phase == .endPhase && loses ending hero && !loses afterTurn hero &&
    later.active == some defender && (legalActionsFor defender (funded later)).contains activate &&
    (regained.poolOf defender).actionPoints == 1 && regained.activeEffects.any (fun e => e.op == .grantKeyword .dominate) &&
    loses stillActive hero && !loses future.finishTurnEffects hero)

#guard checkCrushConfidence ⟨"WTR_063_R"⟩ 1 7 == some true
#guard checkCrushConfidence ⟨"WTR_064_Y"⟩ 2 6 == some true
#guard checkCrushConfidence ⟨"WTR_065_B"⟩ 3 5 == some true

/-- Debilitate follows the damaged player's next turn and is used by their first paid attack. -/
meta def checkDebilitate (cid : CardId) (pitch power : Nat) : Option Bool := do
  let attacker : PlayerId := ⟨0⟩
  let defender : PlayerId := ⟨1⟩
  let base := m5Base.setPool attacker { actionPoints := 1, resources := 4 }
  let card ← base.cards.find? cid
  let (withAttack, attack) ← cPlace { base with pending := base.pending ++ [.beginTurn] } attacker .hand cid
  let (withPlain, plain) ← cPlace withAttack defender .hand ⟨"WTR_203_R"⟩
  let (withBuff, driving) ← cPlace withPlain defender .hand ⟨"WTR_144_R"⟩
  let (withDagger, dagger) ← cPlace withBuff defender .weapon ⟨"WTR_078"⟩
  let (withTwo, otherDagger) ← cPlace withDagger defender .weapon ⟨"WTR_078"⟩
  let (ready, potion) ← cPlace withTwo defender .permanent ⟨"WTR_172_B"⟩
  let defending ← cSteps ready (⟨.player attacker, .playCard attack⟩ :: (passBoth ++ passBoth))
  let finish := ⟨.player defender, .defendDone⟩ :: (passBoth ++ passBoth)
  let prevent (n : Nat) :=
    (execPrim defending defender ⟨0⟩ [] (.preventNextDamage .controller (.const n) .thisTurn)).1
  let hit ← cSteps (prevent (power - 4)) finish
  let short ← cSteps (prevent (power - 3)) finish
  let trigger ← hit.pendingTriggers.head?
  let waiting ← cSteps hit ([⟨.player attacker, .pickTriggerStart attacker⟩,
    ⟨.player attacker, .pickTrigger trigger.id⟩] ++ passBoth)
  let nextTurn (s : GameState) := cSteps s (List.replicate 3 passBoth).flatten
  let restricted ← nextTurn waiting
  let normal ← nextTurn short
  let funded := restricted.setPool defender { actionPoints := 1, resources := 3 }
  let revPass := passBoth.reverse
  let play (id : ObjId) : Action := ⟨.player defender, .playCard id⟩
  let swing (id : ObjId) : Action := ⟨.player defender, .attackWeapon id⟩
  let finishAttack (s : GameState) (action : Action) :=
    cSteps s ([action] ++ revPass ++ revPass ++ [⟨.player attacker, .defendDone⟩] ++
      (List.replicate 3 revPass).flatten)
  let announced ← cSteps restricted [swing dagger]
  let restored ← cSteps announced [⟨.player defender, .cancelPlay⟩]
  let plainFirst ← finishAttack funded (play plain)
  let plainNormal ← finishAttack normal (play plain)
  let drink ← cSteps funded (⟨.player defender, .activateAbility potion 0⟩ :: revPass)
  let firstWeapon ← finishAttack drink (swing dagger)
  let closed ← cSteps firstWeapon revPass
  let secondWeapon ← finishAttack closed (swing otherDagger)
  let beginning ← cSteps drink (play driving :: revPass)
  let modified ← finishAttack beginning (swing dagger)
  let otherTurn ← cSteps restricted (revPass ++ [⟨.player defender, .arsenalSkip⟩])
  let later ← cSteps otherTurn passBoth
  let attackData (s : GameState) :=
    (s.combat.bind CombatChain.activeLink?).map fun link => (link.powerBonus, link.damageDealt)
  let debuffs (s : GameState) := s.activeEffects.filter fun effect => effect.target == .nextAttackBy defender
  pure (card.status == .full && card.front.pitch == some pitch && card.front.defense == some 3 &&
    (defending.poolOf attacker).resources == 0 && hit.lifeOf defender == 36 && short.lifeOf defender == 37 &&
    short.pendingTriggers.isEmpty && (debuffs waiting).map (·.waitsForNextTurn) == [true] &&
    restricted.active == some defender && (debuffs restricted).map (·.waitsForNextTurn) == [false] &&
    decide (restored = restricted) && debuffs announced == debuffs restricted &&
    attackData plainFirst == some (-2, 2) && attackData plainNormal == some (0, 4) &&
    (debuffs plainFirst).isEmpty && debuffs drink == debuffs restricted &&
    attackData firstWeapon == some (-2, 0) && attackData secondWeapon == some (0, 1) &&
    debuffs beginning == debuffs restricted && attackData modified == some (1, 2) &&
    (debuffs modified).isEmpty && later.active == some defender && (debuffs later).isEmpty)

#guard checkDebilitate ⟨"WTR_066_R"⟩ 1 8 == some true
#guard checkDebilitate ⟨"WTR_067_Y"⟩ 2 7 == some true
#guard checkDebilitate ⟨"WTR_068_B"⟩ 3 6 == some true

/-- Cartilage Crush taxes the first paid action card, weapon attack, or action activation. -/
meta def checkCartilageCrush (cid : CardId) (pitch power : Nat) : Option Bool := do
  let attacker : PlayerId := ⟨0⟩
  let defender : PlayerId := ⟨1⟩
  let base := m5Base.setPool attacker { actionPoints := 1, resources := 3 }
  let card ← base.cards.find? cid
  let (withCrush, crush) ← cPlace { base with pending := base.pending ++ [.beginTurn] } attacker .hand cid
  let (withAttack, attack) ← cPlace withCrush defender .hand ⟨"WTR_203_R"⟩
  let (withItem, item) ← cPlace withAttack defender .hand ⟨"WTR_171_B"⟩
  let (withInstant, sigil) ← cPlace withItem defender .hand ⟨"WTR_173_R"⟩
  let (withDagger, dagger) ← cPlace withInstant defender .weapon ⟨"WTR_078"⟩
  let (withPotion, potion) ← cPlace withDagger defender .permanent ⟨"WTR_172_B"⟩
  let (withTunic, tunic) ← cPlace withPotion defender .chest ⟨"WTR_150"⟩
  let ready := updateSingleObject withTunic tunic (fun o => o.addCounterVal .energy 3)
  let defending ← cSteps ready (⟨.player attacker, .playCard crush⟩ :: (passBoth ++ passBoth))
  let finish := ⟨.player defender, .defendDone⟩ :: (passBoth ++ passBoth)
  let prevent (n : Nat) :=
    (execPrim defending defender ⟨0⟩ [] (.preventNextDamage .controller (.const n) .thisTurn)).1
  let hit ← cSteps (prevent (power - 4)) finish
  let short ← cSteps (prevent (power - 3)) finish
  let trigger ← hit.pendingTriggers.head?
  let waiting ← cSteps hit ([⟨.player attacker, .pickTriggerStart attacker⟩,
    ⟨.player attacker, .pickTrigger trigger.id⟩] ++ passBoth)
  let nextTurn (s : GameState) := cSteps s (List.replicate 3 passBoth).flatten
  let restricted ← nextTurn waiting
  let normal ← nextTurn short
  let fund (s : GameState) := s.setPool defender { actionPoints := 1, resources := 3 }
  let play (id : ObjId) : Action := ⟨.player defender, .playCard id⟩
  let swing : Action := ⟨.player defender, .attackWeapon dagger⟩
  let activate : Action := ⟨.player defender, .activateAbility potion 0⟩
  let activateTunic : Action := ⟨.player defender, .activateAbility tunic 1⟩
  let cancel : Action := ⟨.player defender, .cancelPlay⟩
  let revPass := passBoth.reverse
  let cardAnnouncement ← cSteps restricted [play attack]
  let afterCardCancel ← cSteps cardAnnouncement [cancel]
  let weaponAnnouncement ← cSteps restricted [swing]
  let afterWeaponCancel ← cSteps weaponAnnouncement [cancel]
  let activationAnnouncement ← cSteps restricted [activate]
  let afterActivationCancel ← cSteps activationAnnouncement [cancel]
  let paidWithPitch ← cSteps cardAnnouncement [⟨.player defender, .pitchCard item⟩]
  let paidWeapon ← cSteps (fund restricted) [swing]
  let afterSigil ← cSteps restricted (play sigil :: revPass)
  let afterTunic ← cSteps afterSigil (activateTunic :: revPass)
  let afterPotion ← cSteps afterTunic (activate :: revPass)
  let afterItem ← cSteps (fund afterPotion) (play item :: revPass)
  let itemFirst ← cSteps (fund restricted) (play item :: revPass)
  let normalAttack ← cSteps (fund normal) [play attack]
  let discount : ContinuousEffect :=
    { id := restricted.nextTimestamp, controller := defender, source := tunic
      target := .nextAttackCard CardFilter.any, op := .subCostRes 2
      duration := .thisTurn, timestamp := ⟨restricted.nextTimestamp⟩ }
  let lowered ← cSteps { restricted with activeEffects := discount :: restricted.activeEffects } [play attack]
  let otherTurn ← cSteps restricted (revPass ++ [⟨.player defender, .arsenalSkip⟩])
  let later ← cSteps otherTurn passBoth
  let resources (s : GameState) := (s.poolOf defender).resources
  let tax (s : GameState) := nextActionSurcharge s defender
  pure (card.status == .full && card.front.pitch == some pitch && card.front.defense == some 3 &&
    (defending.poolOf attacker).resources == 0 && hit.lifeOf defender == 36 && short.lifeOf defender == 37 &&
    short.pendingTriggers.isEmpty && tax waiting == 0 && tax normal == 0 &&
    restricted.active == some defender && tax restricted == 1 &&
    decide (afterCardCancel = restricted) && decide (afterWeaponCancel = restricted) &&
    decide (afterActivationCancel = restricted) &&
    tax paidWithPitch == 0 && resources paidWithPitch == 2 &&
    tax paidWeapon == 0 && resources paidWeapon == 1 &&
    tax afterSigil == 1 && resources afterSigil == 0 && afterSigil.lifeOf defender == 39 &&
    tax afterTunic == 1 && resources afterTunic == 1 &&
    tax afterPotion == 0 && resources afterPotion == 0 && (afterPotion.poolOf defender).actionPoints == 2 &&
    tax afterItem == 0 && resources afterItem == 3 && tax itemFirst == 0 && resources itemFirst == 2 &&
    tax normalAttack == 0 && resources normalAttack == 3 &&
    tax lowered == 0 && resources lowered == 0 && later.active == some defender && tax later == 0)

#guard checkCartilageCrush ⟨"WTR_060_R"⟩ 1 7 == some true
#guard checkCartilageCrush ⟨"WTR_061_Y"⟩ 2 6 == some true
#guard checkCartilageCrush ⟨"WTR_062_B"⟩ 3 5 == some true

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
