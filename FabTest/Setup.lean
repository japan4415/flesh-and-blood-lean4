module

import Fab
import FabDriver
import FabTest.Fixtures
meta import Fab
meta import FabDriver
meta import FabTest.Fixtures

/-!
# Tests: M2b Start-of-Game Procedure, step engine, Legal, and FabDriver
-/

open Fab
open FabDriver
open FabTest

/-- Build initial 1v1 Classic Constructed state with two valid Bravo decks. -/
meta def bravoMatchInitial : Option GameState :=
  GameState.initial GameConfig.ccDuel sampleDB [validBravoCCDeck, validBravoCCDeck]

-- 1. Initial state builds cleanly, places heroes with 40 life, puts 63 cards in each inventory
#guard match bravoMatchInitial with
  | some s =>
    (s.zone (.player ⟨0⟩ .hero)).length == 1 &&
    (s.zone (.player ⟨1⟩ .hero)).length == 1 &&
    s.lifeOf ⟨0⟩ == 40 &&
    s.lifeOf ⟨1⟩ == 40 &&
    (s.zone (.player ⟨0⟩ .inventory)).length == 63 &&
    (s.zone (.player ⟨1⟩ .inventory)).length == 63 &&
    s.physIds.length == 128 &&
    s.pending == [.chanceFirstPlayer]
  | none => false

-- 2. Full 1v1 CC Start-of-Game Procedure across 5 seeds completes cleanly and enters Turn 1:
--    - Head (Helm), Chest (Tectonic Plating), Weapon (Anothos) equipped FACE-UP
--    - Opening hand = 4 (Bravo Intellect), Deck = 56 (60 - 4), Inventory = 0
--    - Turn 1 Action Phase begins with first player holding 1 AP and priority
--    - Physical cards conserved (128 before and after)
meta def checkSeed (seed : UInt64) : Bool :=
  match bravoMatchInitial with
  | none => false
  | some s0 =>
    match runSetupLoop 64 200 ⟨seed⟩ s0 with
    | .error _ => false
    | .ok s =>
      let okP (p : PlayerId) : Bool :=
        (s.zone (.player p .hero)).length == 1 &&
        (s.zone (.player p .head)).length == 1 &&
        (s.zone (.player p .chest)).length == 1 &&
        (s.zone (.player p .weapon)).length == 1 &&
        (s.zone (.player p .hand)).length == 4 &&
        (s.zone (.player p .deck)).length == 56 &&
        (s.zone (.player p .inventory)).isEmpty &&
        (s.zone (.player p .head) ++ s.zone (.player p .chest) ++ s.zone (.player p .weapon)).all
          (fun id => (s.obj? id).map (·.faceDown) == some false)
      match s.active, s.pending with
      | some first, .priority p 0 :: _ =>
        p == first &&
        s.turn == 1 &&
        s.phase == .actionPhase &&
        (s.poolOf first).actionPoints == 1 &&
        s.result == none &&
        s.turnOrder.length == 2 &&
        s.physIds.length == 128 &&
        okP ⟨0⟩ && okP ⟨1⟩
      | _, _ => false

#guard checkSeed 1
#guard checkSeed 7
#guard checkSeed 42
#guard checkSeed 1337
#guard checkSeed 99999

-- 3. Deterministic reproducibility: same seed produces identical final GameState
#guard match bravoMatchInitial with
  | none => false
  | some s0 =>
    match runSetupLoop 64 200 ⟨42⟩ s0, runSetupLoop 64 200 ⟨42⟩ s0 with
    | .ok a, .ok b => a == b
    | _, _ => false

-- 4. Illegal actions rejected:
--    - Player cannot finish CC loadout before adding 60 deck-cards
#guard match bravoMatchInitial with
  | none => false
  | some s0 =>
    match step 64 s0 ⟨.chance, .chanceFirstChooser ⟨0⟩⟩ with
    | .ok (s1, _) =>
      match step 64 s1 ⟨.player ⟨0⟩, .pickFirstPlayer ⟨0⟩⟩ with
      | .ok (s2, _) =>
        match step 64 s2 ⟨.player ⟨0⟩, .loadoutDone⟩ with
        | .error .illegal => true
        | _ => false
      | .error _ => false
    | .error _ => false

-- 5. Bad shuffle permutation is rejected as illegal
#guard match bravoMatchInitial with
  | none => false
  | some s0 =>
    match runSetupLoop 64 130 ⟨1⟩ s0 with
    | .ok sMid =>
      match sMid.pending with
      | .chanceShuffle _ :: _ =>
        match step 64 sMid ⟨.chance, .shuffleOrder []⟩ with
        | .error .illegal => true
        | _ => false
      | _ => false
    | .error _ => false

-- 6. Insufficient fuel during openingDraws returns .error .fuelExhausted
#guard match bravoMatchInitial with
  | none => false
  | some s0 =>
    match runSetupLoop 64 131 ⟨1⟩ s0 with
    | .ok sPreLastShuffle =>
      match nextSetupAction ⟨1⟩ sPreLastShuffle with
      | some (a, _) =>
        match step 0 sPreLastShuffle a with
        | .error .fuelExhausted => true
        | _ => false
      | none => false
    | .error _ => false

-- 7. Concession in 1v1 immediately ends the game and rejects subsequent actions
#guard match bravoMatchInitial with
  | none => false
  | some s0 =>
    match step 64 s0 ⟨.player ⟨0⟩, .concede⟩ with
    | .ok (sEnd, _) =>
      sEnd.result == some (.won [⟨1⟩]) &&
      sEnd.pending.isEmpty &&
      (legalActions sEnd).isEmpty &&
      match step 64 sEnd ⟨.player ⟨1⟩, .concede⟩ with
      | .error .illegal => true
      | _ => false
    | .error _ => false
