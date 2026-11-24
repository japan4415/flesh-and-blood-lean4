module

import Fab
import FabDriver
import FabTest.Fixtures
meta import Fab
meta import FabDriver
meta import FabTest.Fixtures

/-!
# Tests: M3 Turn skeleton, End Phase (Arsenal, Pitch return, Turn 1 vs Turn 2+ refill), Hero defeat
-/

open Fab
open FabDriver
open FabTest

/-- Helper: obtain a post-setup Turn 1 Action Phase state with `turnOrder = [0, 1]`. -/
meta def turn1State : Option GameState := do
  let s0 ← GameState.initial GameConfig.ccDuel sampleDB [validBravoCCDeck, validBravoCCDeck]
  let s1 ← (step 64 s0 ⟨.chance, .chanceFirstChooser ⟨0⟩⟩).toOption.map Prod.fst
  let s2 ← (step 64 s1 ⟨.player ⟨0⟩, .pickFirstPlayer ⟨0⟩⟩).toOption.map Prod.fst
  (runSetupLoop 64 200 ⟨42⟩ s2).toOption

-- 1. Pass-only 1v1 game cycles smoothly through 4 full turns, alternating P0/P1 with 1 AP each
#guard match turn1State with
  | none => false
  | some s1 =>
    -- Each turn requires 3 actions: P_active pass, P_other pass, P_active arsenalSkip
    match runPassLoop 64 3 ⟨42⟩ s1 with
    | .ok s2 =>
      match runPassLoop 64 3 ⟨42⟩ s2 with
      | .ok s3 =>
        match runPassLoop 64 3 ⟨42⟩ s3 with
        | .ok s4 =>
          s1.turn == 1 && s1.active == some ⟨0⟩ && (s1.poolOf ⟨0⟩).actionPoints == 1 &&
          s2.turn == 2 && s2.active == some ⟨1⟩ && (s2.poolOf ⟨1⟩).actionPoints == 1 &&
          (s2.poolOf ⟨0⟩).actionPoints == 0 &&
          s3.turn == 3 && s3.active == some ⟨0⟩ && (s3.poolOf ⟨0⟩).actionPoints == 1 &&
          (s3.poolOf ⟨1⟩).actionPoints == 0 &&
          s4.turn == 4 && s4.active == some ⟨1⟩ && (s4.poolOf ⟨1⟩).actionPoints == 1 &&
          s4.physIds.length == 128
        | .error _ => false
      | .error _ => false
    | .error _ => false

-- 2. End Phase Arsenal placement (CR 4.4.3b): P0 puts 1 card face-down into empty Arsenal
--    Then on Turn 1 End Phase P0 refills from 3 back up to 4!
#guard match turn1State with
  | none => false
  | some s1 =>
    match (s1.zone (.player ⟨0⟩ .hand)).head? with
    | none => false
    | some c0 =>
      match step 64 s1 ⟨.player ⟨0⟩, .pass⟩ with
      | .ok (s1b, _) =>
        match step 64 s1b ⟨.player ⟨1⟩, .pass⟩ with
        | .ok (sArs, _) =>
          match step 64 sArs ⟨.player ⟨0⟩, .arsenalPut c0⟩ with
          | .ok (sTurn2, _) =>
            let ars := sTurn2.zone (.player ⟨0⟩ .arsenal)
            sTurn2.turn == 2 &&
            ars.length == 1 &&
            (ars.head?.bind sTurn2.obj?).map (·.faceDown) == some true &&
            (sTurn2.zone (.player ⟨0⟩ .hand)).length == 4 &&
            (sTurn2.zone (.player ⟨0⟩ .deck)).length == 55
          | .error _ => false
        | .error _ => false
      | .error _ => false

-- 3. Turn 1 (Turn 0) BOTH players refill to Intellect; Turn 2 ONLY Turn Player (P1) refills!
#guard match turn1State with
  | none => false
  | some s1 =>
    -- Discard 2 cards from P1's hand during Turn 1 (P1 is non-turn player)
    match s1.zone (.player ⟨1⟩ .hand) with
    | a :: b :: _ =>
      match discardOne s1 ⟨1⟩ a with
      | some (sa, _, _) =>
        match discardOne sa ⟨1⟩ b with
        | some (sb, _, _) =>
          -- End Turn 1: BOTH P0 and P1 draw up to Intellect (P1 goes 2 -> 4!)
          match runPassLoop 64 3 ⟨42⟩ sb with
          | .ok sTurn2 =>
            let p1RefilledOnTurn1 :=
              (sTurn2.zone (.player ⟨1⟩ .hand)).length == 4 &&
              (sTurn2.zone (.player ⟨1⟩ .deck)).length == 54
            -- Now during Turn 2 (P1's turn), discard 2 cards from P0 (non-turn player)
            -- and 1 card from P1 (turn player)
            match sTurn2.zone (.player ⟨0⟩ .hand), sTurn2.zone (.player ⟨1⟩ .hand) with
            | c :: d :: _, e :: _ =>
              match discardOne sTurn2 ⟨0⟩ c with
              | some (sc, _, _) =>
                match discardOne sc ⟨0⟩ d with
                | some (sd, _, _) =>
                  match discardOne sd ⟨1⟩ e with
                  | some (se, _, _) =>
                    -- End Turn 2: ONLY P1 refills (3 -> 4), P0 stays at 2!
                    match runPassLoop 64 3 ⟨42⟩ se with
                    | .ok sTurn3 =>
                      p1RefilledOnTurn1 &&
                      sTurn3.turn == 3 &&
                      (sTurn3.zone (.player ⟨1⟩ .hand)).length == 4 &&
                      (sTurn3.zone (.player ⟨0⟩ .hand)).length == 2
                    | .error _ => false
                  | none => false
                | none => false
              | none => false
            | _, _ => false
          | .error _ => false
        | none => false
      | none => false
    | _ => false

-- 4. End Phase Pitch-to-Deck-bottom ordering (CR 4.4.3c) and pool clearing (CR 4.4.3e):
--    P0 pitches two cards (cA, cB), then picks exact bottom order [cB, cA] at End Phase
#guard match turn1State with
  | none => false
  | some s1 =>
    match s1.zone (.player ⟨0⟩ .hand) with
    | cA :: cB :: _ =>
      match pitchOne s1 ⟨0⟩ cA with
      | some (sP1, pA, _) =>
        match pitchOne sP1 ⟨0⟩ cB with
        | some (sP2, pB, _) =>
          let pitchedOk :=
            (sP2.zone (.player ⟨0⟩ .pitch)).length == 2 &&
            0 < (sP2.poolOf ⟨0⟩).resources
          -- Pass both players, skip Arsenal -> prompts choosePitchOrder P0
          match step 64 sP2 ⟨.player ⟨0⟩, .pass⟩ with
          | .ok (sPass1, _) =>
            match step 64 sPass1 ⟨.player ⟨1⟩, .pass⟩ with
            | .ok (sArs, _) =>
              match step 64 sArs ⟨.player ⟨0⟩, .arsenalSkip⟩ with
              | .ok (sPitch1, _) =>
                -- Pick pB first (goes to bottom), then pA (goes below pB at very bottom)
                match step 64 sPitch1 ⟨.player ⟨0⟩, .pitchReturnPick pB⟩ with
                | .ok (sPitch2, _) =>
                  match step 64 sPitch2 ⟨.player ⟨0⟩, .pitchReturnPick pA⟩ with
                  | .ok (sTurn2, _) =>
                    pitchedOk &&
                    sTurn2.turn == 2 &&
                    (sTurn2.zone (.player ⟨0⟩ .pitch)).isEmpty &&
                    sTurn2.poolOf ⟨0⟩ == AssetPool.empty &&
                    (sTurn2.zone (.player ⟨0⟩ .hand)).length == 4 &&
                    sTurn2.physIds.length == 128
                  | .error _ => false
                | .error _ => false
              | .error _ => false
            | .error _ => false
          | .error _ => false
        | none => false
      | none => false
    | _ => false

-- 5. Hero defeat & simultaneous draw (CR 1.10.2a, 4.5)
#guard match turn1State with
  | none => false
  | some s1 =>
    let sP0Wins := checkHeroDefeat (s1.setLife ⟨1⟩ 0)
    let sP1Wins := checkHeroDefeat (s1.setLife ⟨0⟩ (-3))
    let sDraw := checkHeroDefeat ((s1.setLife ⟨0⟩ 0).setLife ⟨1⟩ 0)
    let sAlive := checkHeroDefeat s1
    sP0Wins.result == some (.won [⟨0⟩]) &&
    sP1Wins.result == some (.won [⟨1⟩]) &&
    sDraw.result == some (.draw .simultaneousHeroDeath) &&
    sAlive.result == none
