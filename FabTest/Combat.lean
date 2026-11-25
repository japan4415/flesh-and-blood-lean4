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
  let (expired, _) ← microStep { resolved with pending := [.endTurnCleanup attacker] }
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
  let (expired, _) ← microStep { resolved with pending := [.endTurnCleanup player] }
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
  let buffed ← cSteps paid passBoth
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
    cSteps paidAttack fight
  let weaponFirst ← cSteps bruteReady (swing :: fight)
  let weaponClosed ← cSteps weaponFirst passBoth
  let cardSecond ← playBrute weaponClosed
  let cardFirst ← playBrute bruteReady
  let cardClosed ← cSteps cardFirst passBoth
  let weaponSecond ← cSteps cardClosed (swing :: fight)
  let damage := fun (s : GameState) =>
    (s.combat.bind CombatChain.activeLink?).map (·.damageDealt)
  pure (card.status == .full && card.front.pitch == some 2 && card.front.defense == some 3 &&
    decide (rejected = bare) && paying.pending.head? == some (.chanceShuffle hand) &&
    (paid.poolOf attacker).actionPoints == 3 && (paid.poolOf attacker).resources == 3 &&
    (paid.cardDefOf? discarded).map (·.id) ==
      some (if highPayment then ⟨"WTR_189_Y"⟩ else ⟨"WTR_190_B"⟩) &&
    paid.activeEffects.isEmpty && paid.zone deck == ready.zone deck &&
    (buffed.poolOf attacker).actionPoints == (if highPayment then 4 else 3) &&
    (buffed.zone hand).length == (if highPayment then 3 else 1) &&
    (buffed.zone deck).length == (if highPayment then 0 else 2) &&
    objEffectivePower buffed weapon == some 4 &&
    buffed.activeEffects.map (·.op) == [.addPower 2] && expired.activeEffects.isEmpty &&
    damage genericHit == some 4 && damage weaponFirst == some 6 && damage cardSecond == some 9 &&
    damage cardFirst == some 9 && damage weaponSecond == some 6 &&
    weaponSecond.activeEffects == buffed.activeEffects && cardSecond.activeEffects == buffed.activeEffects)

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
  let (removed, _, _) := execPrim resolved attacker weapon []
    (.returnDefendingCardToHand CardFilter.nonEquipment)
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
  let (oneRemoved, _, _) := execPrim withTwo attacker activeAttack []
    (.returnDefendingCardToHand CardFilter.nonEquipment)
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
