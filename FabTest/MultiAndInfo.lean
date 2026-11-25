module

import Fab
meta import Fab

/-!
# M9 Tests: UPF Multiplayer, I10 Non-Interference, I19 Loop Detector, and I12 Termination
-/

namespace FabTest.MultiAndInfo

open Fab

meta def p0 : PlayerId := ⟨0⟩
meta def p1 : PlayerId := ⟨1⟩
meta def p2 : PlayerId := ⟨2⟩
meta def p3 : PlayerId := ⟨3⟩

-- 1. UPF 4-player adjacency & player elimination
meta def upfTest : Bool :=
  let cfg : GameConfig := { format := .upf, mode := .upf 4, ruleSet := .coreOnly }
  let s0 : GameState :=
    { config := cfg
      cards := CardDB.empty
      turnOrder := [p0, p1, p2, p3]
      active := some p0
      phase := .actionPhase
      heroLife := ((((∅ : Std.ExtTreeMap Nat Int).insert 0 20).insert 1 20).insert 2 20).insert 3 20 }
  let adjOk :=
    canAttackTargetUpf s0 p0 p1 == true &&
    canAttackTargetUpf s0 p0 p3 == true &&
    canAttackTargetUpf s0 p0 p2 == false &&
    adjacentOpponents s0.turnOrder p1 == [p0, p2]
  -- Eliminate p1: p1 removed from turnOrder, now p0 and p2 become adjacent!
  let sElim := eliminatePlayer s0 p1
  let elimOk :=
    sElim.turnOrder == [p0, p2, p3] &&
    sElim.lifeOf p1 == 0 &&
    sElim.result.isNone &&
    canAttackTargetUpf sElim p0 p2 == true
  adjOk && elimOk

#guard upfTest == true

-- 2. I10 Hidden Information Non-Interference: Pitch deck-bottom order & opponent hand secrecy
meta def cardA : CardDef :=
  { id := ⟨"C_A"⟩
    front :=
      { name := "Alpha", types := [.action], subtypes := [.attack],
        pitch := some 1, cost := some { actionPoints := 1, resources := 0 }, power := some 4, defense := some 3 } }

meta def cardB : CardDef :=
  { id := ⟨"C_B"⟩
    front :=
      { name := "Beta", types := [.action], subtypes := [.attack],
        pitch := some 3, cost := some { actionPoints := 1, resources := 0 }, power := some 2, defense := some 3 } }

meta def infoTest : Bool :=
  let cfg : GameConfig := { format := .classicConstructed, mode := .duel, ruleSet := .coreOnly }
  let db : CardDB := ⟨[cardA, cardB]⟩
  let s0 : GameState :=
    { config := cfg, cards := db, turnOrder := [p0, p1], active := some p0,
      phase := .actionPhase, pending := [.priority p0 0],
      pools := (∅ : Std.ExtTreeMap Nat AssetPool).insert 0 { actionPoints := 1 },
      heroLife := ((∅ : Std.ExtTreeMap Nat Int).insert 0 20).insert 1 20 }
  match addObject s0 (.player p0 .deck)
      { kind := .card ⟨1⟩ ⟨"C_A"⟩, owner := p0, controller := p0, timestamp := ⟨0⟩ } .top with
  | none => false
  | some (s1, d1) =>
    match addObject s1 (.player p0 .deck)
        { kind := .card ⟨2⟩ ⟨"C_B"⟩, owner := p0, controller := p0, timestamp := ⟨1⟩ } .top with
    | none => false
    | some (s2, d2) =>
      -- Reorder p0's deck [d2, d1] -> [d1, d2] (simulating different Pitch return order)
      let sReord := s2.reorder (.player p0 .deck) [d1, d2]
      let deckOk :=
        view p0 sReord == view p0 s2 &&
        view p1 sReord == view p1 s2 &&
        legalActionsFor p0 sReord == legalActionsFor p0 s2
      -- Swap opponent p1's hidden hand contents -> p0's legalActionsFor unchanged!
      let sOppChanged := s2.setZone (.player p1 .hand) [⟨99⟩]
      let oppOk := legalActionsFor p0 sOppChanged == legalActionsFor p0 s2
      deckOk && oppOk

#guard infoTest == true

-- 3. I19 Forced Loop Detector (invariant under monotonic nextId/nextTimestamp increments)
meta def loopDetectTest : Bool :=
  let cfg : GameConfig := { format := .classicConstructed, mode := .duel, ruleSet := .tournament .swiss }
  let s0 : GameState :=
    { config := cfg, cards := CardDB.empty, turnOrder := [p0, p1], active := some p0,
      phase := .actionPhase, pending := [.priority p0 0], nextId := 10, nextTimestamp := 10,
      heroLife := ((∅ : Std.ExtTreeMap Nat Int).insert 0 20).insert 1 20 }
  -- Same canonical board after bouncing objects (nextId/nextTimestamp advanced!)
  let sBounced : GameState := { s0 with nextId := 42, nextTimestamp := 99 }
  -- Different board (life dropped to 19) is NOT a loop
  let sProgress := s0.setLife p1 19
  detectLoop [s0] sBounced == true &&
  findLoopStart? [s0] sBounced == some 0 &&
  detectLoop [s0] sProgress == false &&
  match step 5 sBounced ⟨.judge, .judgeLoopDraw⟩ with
  | .ok (sEnd, _) => sEnd.result == some (.draw .loop)
  | .error _ => false

#guard loopDetectTest == true

-- 4. I12 Effect IR structural measure strict decrease
meta def terminationMeasureTest : Bool :=
  let eSeq : Effect := .seqL [.nop, .grant .self_ (.addPower (.const 2)) .thisChainLink]
  let eIf : Effect := .ifThen .playedFromArsenal eSeq .nop
  todoSize [eSeq] < todoSize [eIf] &&
  todoSize [.nop, .grant .self_ (.addPower (.const 2)) .thisChainLink] < todoSize [eSeq]

#guard terminationMeasureTest == true

end FabTest.MultiAndInfo
