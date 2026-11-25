module

import Fab
import FabCards
meta import Fab
meta import FabCards

/-!
# Tests: M4 Stack LIFO, priority, card play 9 steps, pitching & rollback, and IR interpreter
-/

open Fab
open FabCards

/-- Helper: add a physical card `cid` to player `p`'s zone `k`, returning `(s', id)`. -/
meta def placeCard (s : GameState) (p : PlayerId) (k : ZoneKind) (cid : CardId)
    (faceDown : Bool := false) : Option (GameState × ObjId) :=
  addObject s (.player p k)
    { kind := .card ⟨s.nextId⟩ cid
      owner := p
      controller := p
      faceDown := faceDown
      timestamp := ⟨0⟩ } .top

/-- Base 1v1 Action Phase state using the full 226-card `wtrDB`, with P0 active and 1 AP. -/
meta def m4BaseState : GameState :=
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
meta def runSteps (s : GameState) : List Action → Option GameState
  | [] => some s
  | a :: rest =>
    match step 64 s a with
    | .ok (s', _) => runSteps s' rest
    | .error _ => none

-- 1. Stack LIFO & Instant response (CR 1.11, 5.1, 5.3):
--    P0 plays Tome of Fyendal (Action, cost 1 {r}, draw 2), P0 retains priority, P0 passes ->
--    P1 responds with Sigil of Solace Red (Instant, cost 0, gain 3 life) -> P1 retains priority ->
--    both pass -> Sigil resolves FIRST (P1 = 43, P0 hand still 0) -> priority returns to active
--    P0 -> both pass -> Tome resolves SECOND (P0 draws 2 cards, Tome goes to graveyard).
#guard match (do
    let s0 := m4BaseState.setPool ⟨0⟩ { actionPoints := 1, resources := 1 }
    let (s1, d1) ← placeCard s0 ⟨0⟩ .deck ⟨"WTR_188_R"⟩
    let (s2, d2) ← placeCard s1 ⟨0⟩ .deck ⟨"WTR_203_R"⟩
    let _ := (d1, d2)
    let (s3, tomeId) ← placeCard s2 ⟨0⟩ .hand ⟨"WTR_160_Y"⟩
    let (s4, sigilId) ← placeCard s3 ⟨1⟩ .hand ⟨"WTR_173_R"⟩
    -- P0 plays Tome -> P0 retains priority, stack has 1 item
    let sPlayTome ← runSteps s4 [⟨.player ⟨0⟩, .playCard tomeId⟩]
    let p0Retained := sPlayTome.pending == [.priority ⟨0⟩ 0, .endPhaseStart ⟨0⟩] &&
      (sPlayTome.zone .stack).length == 1 && (sPlayTome.poolOf ⟨0⟩).actionPoints == 0 &&
      (sPlayTome.poolOf ⟨0⟩).resources == 0
    -- P0 passes, P1 plays Sigil -> P1 retains priority, stack has 2 items
    let sPlaySigil ← runSteps sPlayTome [⟨.player ⟨0⟩, .pass⟩, ⟨.player ⟨1⟩, .playCard sigilId⟩]
    let p1Retained := sPlaySigil.pending == [.priority ⟨1⟩ 0, .endPhaseStart ⟨0⟩] &&
      (sPlaySigil.zone .stack).length == 2
    -- P1 passes, P0 passes -> Sigil resolves LIFO first! Priority returns to P0 (active).
    let sAfterSigil ← runSteps sPlaySigil [⟨.player ⟨1⟩, .pass⟩, ⟨.player ⟨0⟩, .pass⟩]
    let lifoOk := sAfterSigil.lifeOf ⟨1⟩ == 43 &&
      (sAfterSigil.zone (.player ⟨0⟩ .hand)).isEmpty &&
      (sAfterSigil.zone .stack).length == 1 &&
      sAfterSigil.pending == [.priority ⟨0⟩ 0, .endPhaseStart ⟨0⟩]
    -- P0 passes, P1 passes -> Tome resolves second! P0 draws 2 cards, stack empty.
    let sAfterTome ← runSteps sAfterSigil [⟨.player ⟨0⟩, .pass⟩, ⟨.player ⟨1⟩, .pass⟩]
    let tomeOk := (sAfterTome.zone (.player ⟨0⟩ .hand)).length == 2 &&
      sAfterTome.lifeOf ⟨0⟩ == 40 &&
      (sAfterTome.zone .stack).isEmpty &&
      (sAfterTome.zone (.player ⟨0⟩ .graveyard)).length == 1 &&
      (sAfterTome.zone (.player ⟨1⟩ .graveyard)).length == 1 &&
      sAfterTome.physIds.length == 4
    pure (p0Retained && p1Retained && lifoOk && tomeOk)) with
  | some b => b
  | none => false

-- 2. Go Again on non-attack Action resolution (CR 5.3.4, 8.3.5):
--    P0 plays Awakening Bellow Red (cost 1 {r}, Go Again) -> AP 1 -> 0 -> resolves -> AP 0 -> 1,
--    enabling P0 to play a second Action (Tome of Fyendal, cost 1 {r}) on the same turn!
#guard match (do
    let s0 := m4BaseState.setPool ⟨0⟩ { actionPoints := 1, resources := 2 }
    let (s1, _) ← placeCard s0 ⟨0⟩ .deck ⟨"WTR_188_R"⟩
    let (s2, _) ← placeCard s1 ⟨0⟩ .deck ⟨"WTR_203_R"⟩
    let (s3, bellowId) ← placeCard s2 ⟨0⟩ .hand ⟨"WTR_032_R"⟩
    let (s4, tomeId) ← placeCard s3 ⟨0⟩ .hand ⟨"WTR_160_Y"⟩
    let sAfterBellow ← runSteps s4
      [⟨.player ⟨0⟩, .playCard bellowId⟩, ⟨.player ⟨0⟩, .pickHeroTarget ⟨1⟩⟩,
        ⟨.player ⟨0⟩, .pass⟩, ⟨.player ⟨1⟩, .pass⟩]
    let apRefilled := (sAfterBellow.poolOf ⟨0⟩).actionPoints == 1
    let sAfterTome ← runSteps sAfterBellow
      [⟨.player ⟨0⟩, .playCard tomeId⟩, ⟨.player ⟨0⟩, .pass⟩, ⟨.player ⟨1⟩, .pass⟩]
    pure (apRefilled && (sAfterTome.zone (.player ⟨0⟩ .hand)).length == 2)) with
  | some b => b
  | none => false

-- 3. Pitching during `choosePitch` & No Over-Pitching (CR 1.14.3b, 5.1.6):
--    P0 plays Tome of Fyendal (cost 1 {r}) with a Blue (pitch 3) and Red (pitch 1) in hand.
--    Pitching Blue generates 3 {r}, immediately pays 1 {r}, leaves 2 floating {r}, and retains
--    priority (cannot over-pitch the Red card).
#guard match (do
    let (s1, tomeId) ← placeCard m4BaseState ⟨0⟩ .hand ⟨"WTR_160_Y"⟩
    let (s2, blueCard) ← placeCard s1 ⟨0⟩ .hand ⟨"WTR_205_B"⟩
    let (s3, _) ← placeCard s2 ⟨0⟩ .hand ⟨"WTR_203_R"⟩
    let sPitchPrompt ← runSteps s3 [⟨.player ⟨0⟩, .playCard tomeId⟩]
    let askedPitch := match sPitchPrompt.pending with | .choosePitch ⟨0⟩ _ _ _ _ :: _ => true | _ => false
    let sPaid ← runSteps sPitchPrompt [⟨.player ⟨0⟩, .pitchCard blueCard⟩]
    pure (askedPitch &&
      sPaid.pending == [.priority ⟨0⟩ 0, .endPhaseStart ⟨0⟩] &&
      (sPaid.poolOf ⟨0⟩).resources == 2 &&
      (sPaid.poolOf ⟨0⟩).actionPoints == 0 &&
      (sPaid.zone (.player ⟨0⟩ .pitch)).length == 1 &&
      sPaid.playRollback == none)) with
  | some b => b
  | none => false

-- 4. Card Play Rollback (CR 5.1.1):
--    (a) Manual `cancelPlay` after pitching 1 card restores the exact pre-play state `s3`!
--    (b) Automatic rollback when pitching all pitchable cards still cannot cover cost 4 (`Disable`).
#guard match (do
    let (s1, sloggism) ← placeCard m4BaseState ⟨0⟩ .hand ⟨"WTR_221_R"⟩
    let (s2, red1) ← placeCard s1 ⟨0⟩ .hand ⟨"WTR_203_R"⟩
    let (s3, _) ← placeCard s2 ⟨0⟩ .hand ⟨"WTR_188_R"⟩
    -- (a) Play cost-2 Sloggism, pitch Red (1 {r}), then cancel -> exact rollback to s3!
    let sCancelled ← runSteps s3
      [⟨.player ⟨0⟩, .playCard sloggism⟩, ⟨.player ⟨0⟩, .pitchCard red1⟩, ⟨.player ⟨0⟩, .cancelPlay⟩]
    -- (b) Play cost-4 Disable with only 1 Blue (pitch 3) -> pitches Blue, still short -> auto-rollback!
    let (t1, disable) ← placeCard m4BaseState ⟨0⟩ .hand ⟨"WTR_048_R"⟩
    let (t2, blue1) ← placeCard t1 ⟨0⟩ .hand ⟨"WTR_205_B"⟩
    let tRolledBack ← runSteps t2
      [⟨.player ⟨0⟩, .playCard disable⟩, ⟨.player ⟨0⟩, .pitchCard blue1⟩]
    pure (sCancelled == s3 && tRolledBack == t2)) with
  | some b => b
  | none => false

/-- Pay a mandatory random discard after pitching and before granting priority. -/
meta def checkRandomDiscardAttack (cid : CardId) (pitch cost power : Nat) (fromArsenal : Bool) :
    Option Bool := do
  let player : PlayerId := ⟨0⟩
  let opponent : PlayerId := ⟨1⟩
  let zone := Zone.player player
  let origin : ZoneKind := if fromArsenal then .arsenal else .hand
  let funded := m4BaseState.setPool player { actionPoints := 1, resources := cost }
  let card ← funded.cards.find? cid
  let (empty, attack) ← placeCard funded player origin cid fromArsenal
  let play : Action := ⟨.player player, .playCard attack⟩
  let (rejected, rejectedEvents) ← (step 64 empty play).toOption
  let unfunded := empty.setPool player { actionPoints := 1 }
  let (one, payer) ← placeCard unfunded player .hand ⟨"WTR_205_B"⟩
  let pitchPayer : Action := ⟨.player player, .pitchCard payer⟩
  let afterPitchFailure ← runSteps one [play, pitchPayer]
  let (two, first) ← placeCard one player .hand ⟨"WTR_203_R"⟩
  let paidSingle ← runSteps two [play, pitchPayer]
  let (three, second) ← placeCard two player .hand ⟨"WTR_204_Y"⟩
  let buffed := applyChainLinkMod three player attack []
    (.nextAttack CardFilter.any) (.addPower (.const 2)) .thisTurn
  let askedPitch ← runSteps buffed [play]
  let cancelled ← runSteps askedPitch [⟨.player player, .cancelPlay⟩]
  let (paying, pitchEvents) ← (step 64 askedPitch pitchPayer).toOption
  let attackLayer ← (paying.zone .stack).head?
  let pitched ← (paying.zone (zone .pitch)).head?
  let choose := fun order => (⟨.chance, .shuffleOrder order⟩ : Action)
  let reject := fun action => (step 64 paying action).toOption.isNone
  let (played, firstEvents) ← (step 64 paying (choose [first, second])).toOption
  let (other, secondEvents) ← (step 64 paying (choose [second, first])).toOption
  let discardOk := fun (s : GameState) (events : List Event) picked left => do
    let discarded ← (s.zone (zone .graveyard)).head?
    pure (s.zone (zone .hand) == [left] && s.zone (zone .graveyard) == [discarded] &&
      (s.obj? discarded).map (·.kind) == (three.obj? picked).map (·.kind) &&
      events == [.moved picked discarded (zone .hand) (zone .graveyard),
        .discarded player discarded] &&
      s.playRollback.isNone && s.activeEffects.isEmpty && s.pending == buffed.pending &&
      (s.layerMeta.get? attackLayer.n).map (·.fromArsenal) == some fromArsenal &&
      (s.layerMeta.get? attackLayer.n).map (·.attackPowerBonus) == some 2)
  let firstCorrect ← discardOk played firstEvents first second
  let secondCorrect ← discardOk other secondEvents second first
  let pass := [⟨.player player, .pass⟩, ⟨.player opponent, .pass⟩]
  let finish := [⟨.player opponent, .defendDone⟩] ++ pass ++ pass
  let hit ← runSteps played (pass ++ pass ++ finish)
  let link ← hit.combat.bind CombatChain.activeLink?
  pure (card.status == .full && card.front.pitch == some pitch && card.front.defense == some 3 &&
    decide (rejected = empty) && decide (afterPitchFailure = one) &&
    !rejectedEvents.any (fun | .discarded _ _ => true | _ => false) &&
    (paidSingle.zone (zone .hand)).isEmpty && (paidSingle.zone (zone .graveyard)).length == 1 &&
    paidSingle.pending == buffed.pending && decide (cancelled = buffed) &&
    paying.pending.head? == some (.chanceShuffle (zone .hand)) &&
    (paying.poolOf player).actionPoints == 0 && (paying.poolOf player).resources == 3 - cost &&
    paying.zone (zone .hand) == [second, first] && (paying.zone (zone .graveyard)).isEmpty &&
    pitchEvents.contains (.pitched player pitched 3 0) &&
    paying.activeEffects == buffed.activeEffects &&
    paying.playRollback.isSome && reject (choose [first, first]) &&
    reject ⟨.player player, .cancelPlay⟩ && reject ⟨.player opponent, .pass⟩ &&
    firstCorrect && secondCorrect &&
    hit.lifeOf opponent == 40 - Int.ofNat (power + 2) && link.damageDealt == power + 2)

#guard checkRandomDiscardAttack ⟨"WTR_029_R"⟩ 1 2 8 false == some true
#guard checkRandomDiscardAttack ⟨"WTR_029_R"⟩ 1 2 8 true == some true
#guard checkRandomDiscardAttack ⟨"WTR_030_Y"⟩ 2 2 7 false == some true
#guard checkRandomDiscardAttack ⟨"WTR_030_Y"⟩ 2 2 7 true == some true
#guard checkRandomDiscardAttack ⟨"WTR_031_B"⟩ 3 2 6 false == some true
#guard checkRandomDiscardAttack ⟨"WTR_031_B"⟩ 3 2 6 true == some true
#guard checkRandomDiscardAttack ⟨"WTR_020_R"⟩ 1 1 7 false == some true
#guard checkRandomDiscardAttack ⟨"WTR_020_R"⟩ 1 1 7 true == some true

-- 5. Playing face-down card from Arsenal (CR 3.2.2) triggers `playedFromArsenal` on Tome of Fyendal:
--    Tome starts face-down in Arsenal, P0 has 1 floating {r}, 1 card in hand & 2 in deck.
--    Playing Tome draws 2 (hand = 3), then `playedFromArsenal` gains 3 life (40 -> 43)!
#guard match (do
    let s0 := m4BaseState.setPool ⟨0⟩ { actionPoints := 1, resources := 1 }
    let (s1, _) ← placeCard s0 ⟨0⟩ .deck ⟨"WTR_188_R"⟩
    let (s2, _) ← placeCard s1 ⟨0⟩ .deck ⟨"WTR_203_R"⟩
    let (s3, _) ← placeCard s2 ⟨0⟩ .hand ⟨"WTR_173_R"⟩
    let (s4, arsTome) ← placeCard s3 ⟨0⟩ .arsenal ⟨"WTR_160_Y"⟩ true
    let sDone ← runSteps s4
      [⟨.player ⟨0⟩, .playCard arsTome⟩, ⟨.player ⟨0⟩, .pass⟩, ⟨.player ⟨1⟩, .pass⟩]
    pure ((sDone.zone (.player ⟨0⟩ .arsenal)).isEmpty &&
      (sDone.zone (.player ⟨0⟩ .hand)).length == 3 &&
      sDone.lifeOf ⟨0⟩ == 43)) with
  | some b => b
  | none => false

/-- Resolve Tome from arsenal with a deck too small to draw two cards. -/
meta def checkTomeShortDraw (withCard : Bool) : Option Bool := do
  let player : PlayerId := ⟨0⟩
  let cid : CardId := ⟨"WTR_160_Y"⟩
  let funded := m4BaseState.setPool player { actionPoints := 1, resources := 1 }
  let card ← funded.cards.find? cid
  let (withHand, _) ← placeCard funded player .hand ⟨"WTR_203_R"⟩
  let withDeck ← if withCard then
    (placeCard withHand player .deck ⟨"WTR_191_R"⟩).map Prod.fst
    else some withHand
  let (ready, tome) ← placeCard withDeck player .arsenal cid true
  let beforeResolution ← runSteps ready [⟨.player player, .playCard tome⟩, ⟨.player player, .pass⟩]
  let (resolved, events) ← (step 64 beforeResolution ⟨.player ⟨1⟩, .pass⟩).toOption
  let drawn := if withCard then 1 else 0
  let gained := 1 + drawn
  let draws := events.filterMap fun
    | .drawn p id => if p == player then some id else none
    | _ => none
  pure (card.status == .full && card.front.pitch == some 2 && card.front.defense == some 2 &&
    resolved.zone (.player player .arsenal) == [] && resolved.zone (.player player .deck) == [] &&
    (resolved.zone (.player player .hand)).length == gained && draws.length == drawn &&
    events.countP (· == .lifeGained player gained) == 1 &&
    resolved.lifeOf player == 40 + Int.ofNat gained &&
    (resolved.poolOf player).actionPoints == 0 && (resolved.poolOf player).resources == 0)

#guard checkTomeShortDraw true == some true
#guard checkTomeShortDraw false == some true

-- 6. Optional choice `Effect.may` (I18) and `putHandOnDeck` via `Frame.run`:
--    Sink Below effect (`may (putHandOnDeck .bottom) (draw 1)`) ALWAYS prompts `chooseMay`.
--    Choosing `true` puts the hand card on deck bottom and draws 1; `false` leaves hand unchanged.
#guard match (do
    let (s1, dCard) ← placeCard m4BaseState ⟨0⟩ .deck ⟨"WTR_188_R"⟩
    let (s2, hCard) ← placeCard s1 ⟨0⟩ .hand ⟨"WTR_203_R"⟩
    let sinkEffect : Effect :=
      .may (.prim (.putHandOnDeck .controller .bottom)) (.prim (.draw .controller (.const 1)))
    let sStart := { s2 with pending := [.run ⟨0⟩ hCard false [] [sinkEffect]] }
    -- Advance 1 microStep -> must pause on `chooseMay`!
    match advance 16 sStart [] with
    | .ok (sMay, _) =>
      let prompted := match sMay.pending with | .chooseMay ⟨0⟩ _ _ _ _ _ :: _ => true | _ => false
      let sDecline ← runSteps sMay [⟨.player ⟨0⟩, .pickMay false⟩]
      let sAccept ← runSteps sMay [⟨.player ⟨0⟩, .pickMay true⟩, ⟨.player ⟨0⟩, .handToDeckPick hCard⟩]
      pure (prompted &&
        sDecline.zone (.player ⟨0⟩ .hand) == [hCard] &&
        (sAccept.zone (.player ⟨0⟩ .hand)).length == 1 &&
        (sAccept.zone (.player ⟨0⟩ .deck)).length == 1 &&
        sAccept.zone (.player ⟨0⟩ .hand) != [hCard] &&
        dCard != hCard)
    | .error _ => none) with
  | some b => b
  | none => false

-- 7. 6-sided Die Roll (`chanceDie6`), Remembrance (`banish .self_`), Token creation, and `Opt`:
--    (a) Crazy Brew die roll 5-6 grants +2 {r} and +2 AP; roll 1-2 loses 2 life and +1 AP.
--    (b) Remembrance (Instant) banishes itself on resolution instead of going to graveyard.
--    (c) `createToken` adds Seismic Surge preserving `physIds`; `opt 1` puts top card on bottom.
#guard match (do
    let brewEffect : Effect :=
      .rollDie6 ⟨0⟩
        (.cons 1 2 (.seqL [.prim (.loseLife .controller (.const 2)), .prim (.gainAP .controller (.const 1))])
        (.cons 3 4 (.seqL [.prim (.gainLife .controller (.const 2)), .prim (.gainAP .controller (.const 1))])
        (.cons 5 6 (.seqL [.prim (.gainResource .controller (.const 2)), .prim (.gainAP .controller (.const 2))])
        .nil)))
        .nop
    let sBrew := { m4BaseState with pending := [.run ⟨0⟩ ⟨0⟩ false [] [brewEffect]] }
    let sBrewPrompt ← match advance 16 sBrew [] with | .ok (s, _) => some s | .error _ => none
    let sRoll1 ← runSteps sBrewPrompt [⟨.chance, .die6Roll 1⟩]
    let sRoll6 ← runSteps sBrewPrompt [⟨.chance, .die6Roll 6⟩]
    -- (b) Remembrance shuffles deck and banishes itself
    let (r1, remId) ← placeCard m4BaseState ⟨0⟩ .hand ⟨"WTR_163_Y"⟩
    let rDone ← runSteps r1
      [⟨.player ⟨0⟩, .playCard remId⟩, ⟨.player ⟨0⟩, .pass⟩, ⟨.player ⟨1⟩, .pass⟩,
       ⟨.chance, .shuffleOrder []⟩]
    -- (c) Token creation + Opt 1 bottom
    let (o1, topC) ← placeCard m4BaseState ⟨0⟩ .deck ⟨"WTR_188_R"⟩
    let (o2, botC) ← placeCard o1 ⟨0⟩ .deck ⟨"WTR_203_R"⟩
    let tokOpt : Effect := .seqL
      [ .prim (.createToken .controller ⟨"WTR_075"⟩ 1)
      , .prim (.opt .controller 1) ]
    let oStart := { o2 with pending := [.run ⟨0⟩ ⟨0⟩ false [] [tokOpt]] }
    let oPrompt ← match advance 16 oStart [] with | .ok (s, _) => some s | .error _ => none
    let oDone ← runSteps oPrompt [⟨.player ⟨0⟩, .optPick false⟩]
    pure (sRoll1.lifeOf ⟨0⟩ == 38 && (sRoll1.poolOf ⟨0⟩).actionPoints == 2 &&
      (sRoll6.poolOf ⟨0⟩).resources == 2 && (sRoll6.poolOf ⟨0⟩).actionPoints == 3 &&
      (rDone.zone (.player ⟨0⟩ .banished)).length == 1 &&
      (rDone.zone (.player ⟨0⟩ .graveyard)).isEmpty &&
      (oDone.zone (.player ⟨0⟩ .permanent)).length == 1 &&
      oDone.physIds.length == o2.physIds.length &&
      oDone.zone (.player ⟨0⟩ .deck) == [topC, botC])) with
  | some b => b
  | none => false
