module

import Fab
import FabCards
meta import Fab
meta import FabCards

/-!
# Tests: M5b Tournament Rules (TRP: Time Limit / I14, Swiss Bo1 & Top Cut ID Ban, Judge Loop Draw)
-/

open Fab
open FabCards

/-- Helper: build an ongoing 1v1 Action Phase state with configurable `RuleSet` and hero lives. -/
meta def tournBase (rs : RuleSet) (turn : Nat := 2) (tp : PlayerId := ⟨1⟩)
    (life0 : Int := 40) (life1 : Int := 40) : GameState :=
  let s0 : GameState :=
    { config := GameConfig.ccDuel rs
      cards := wtrDB
      turn := turn
      active := some tp
      turnOrder := [⟨0⟩, ⟨1⟩]
      phase := .actionPhase
      pending := [.priority tp 0, .endPhaseStart tp, .beginTurn] }
  let s1 := (s0.setLife ⟨0⟩ life0).setLife ⟨1⟩ life1
  s1.setPool tp { actionPoints := 1 }

/-- Helper: add a physical card `cid` to player `p`'s zone `k`. -/
meta def tPlace (s : GameState) (p : PlayerId) (k : ZoneKind) (cid : CardId) :
    Option (GameState × ObjId) :=
  addObject s (.player p k)
    { kind := .card ⟨s.nextId⟩ cid
      owner := p
      controller := p
      timestamp := ⟨0⟩ } .top

/-- Helper: execute a sequence of actions with fuel 64. -/
meta def tSteps (s : GameState) : List Action → Option GameState
  | [] => some s
  | a :: rest =>
    match step 64 s a with
    | .ok (s', _) => tSteps s' rest
    | .error _ => none

-- 1. Swiss Round Time Limit End-of-Round Procedure (I14: TRP 4):
--    Clock fires at Turn 2 (even with life disparity 40 vs 1):
--    - Second clock signal is illegal.
--    - Turn 2 finishes -> additional Turn 3 begins (`timeLimitTurnsLeft = some 0`).
--    - Turn 3 finishes -> immediately ends in `GameResult.draw .timeLimit` (no life tiebreaker).
--    - Swiss Bo1 match records the draw in 1 game.
#guard match (do
    let s0 := tournBase (.tournament .swiss) (turn := 2) (tp := ⟨1⟩) (life0 := 40) (life1 := 1)
    let s1 ← match step 64 s0 ⟨.clock, .timeExpired⟩ with | .ok (s', _) => some s' | .error _ => none
    let secondBlocked :=
      match step 64 s1 ⟨.clock, .timeExpired⟩ with
      | .error .illegal => true
      | _ => false
    let afterClockOk := s1.result == none && s1.turn == 2 && s1.tournament.timeLimitTurnsLeft == some 1
    -- Finish Turn 2 (P1 passes, P0 passes) -> starts additional Turn 3 (P0 active)
    let sTurn3 ← tSteps s1 [⟨.player ⟨1⟩, .pass⟩, ⟨.player ⟨0⟩, .pass⟩]
    let turn3Ok := sTurn3.result == none && sTurn3.turn == 3 &&
      sTurn3.active == some ⟨0⟩ && sTurn3.tournament.timeLimitTurnsLeft == some 0
    -- Finish Turn 3 (P0 passes, P1 passes) -> immediately ends in .draw .timeLimit
    let sEnd ← tSteps sTurn3 [⟨.player ⟨0⟩, .pass⟩, ⟨.player ⟨1⟩, .pass⟩]
    let endOk := sEnd.result == some (.draw .timeLimit) && sEnd.turn == 3
    let matchAfter :=
      match sEnd.result with
      | some r => MatchState.swissBo1.recordGame r
      | none => MatchState.swissBo1
    let matchOk := matchAfter.outcome == some (.draw .timeLimit) && matchAfter.gamesPlayed == 1
    pure (secondBlocked && afterClockOk && turn3Ok && endOk && matchOk)) with
  | some b => b
  | none => false

-- 2. Lethal combat during the additional turn after time limit wins instead of drawing (TRP 4):
#guard match (do
    let s0 := tournBase (.tournament .swiss) (turn := 2) (tp := ⟨1⟩) (life0 := 40) (life1 := 2)
    let (s0a, wb) ← tPlace s0 ⟨0⟩ .hand ⟨"WTR_203_R"⟩
    let s1 ← match step 64 s0a ⟨.clock, .timeExpired⟩ with | .ok (s', _) => some s' | .error _ => none
    -- Finish Turn 2 -> additional Turn 3 (P0 active)
    let sTurn3 ← tSteps s1 [⟨.player ⟨1⟩, .pass⟩, ⟨.player ⟨0⟩, .pass⟩]
    -- P0 attacks with Wounding Blow Red (4{p}); P1 does not defend -> Damage Step deals 4 (2 -> -2) -> P0 wins!
    let sEnd ← tSteps sTurn3
      [⟨.player ⟨0⟩, .playCard wb⟩,
       ⟨.player ⟨0⟩, .pass⟩, ⟨.player ⟨1⟩, .pass⟩,
       ⟨.player ⟨0⟩, .pass⟩, ⟨.player ⟨1⟩, .pass⟩,
       ⟨.player ⟨1⟩, .defendDone⟩,
       ⟨.player ⟨0⟩, .pass⟩, ⟨.player ⟨1⟩, .pass⟩,
       ⟨.player ⟨0⟩, .pass⟩, ⟨.player ⟨1⟩, .pass⟩]
    let m1 := match sEnd.result with | some r => MatchState.swissBo1.recordGame r | none => MatchState.swissBo1
    pure (sEnd.result == some (.won [⟨0⟩]) && m1.outcome == some (.winner ⟨0⟩))) with
  | some b => b
  | none => false

-- 3. Swiss Bo1 Intentional Draw: offer -> self-accept illegal -> decline -> re-offer -> accept (TRP 4):
#guard match (do
    let s0 := tournBase (.tournament .swiss)
    let offerInLegal := ⟨.player ⟨0⟩, .offerDraw⟩ ∈ legalActions s0
    let s1 ← match step 64 s0 ⟨.player ⟨0⟩, .offerDraw⟩ with | .ok (s', _) => some s' | .error _ => none
    let selfAcceptBlocked :=
      match step 64 s1 ⟨.player ⟨0⟩, .acceptDraw⟩ with
      | .error .illegal => true
      | _ => false
    let oppCanAccept := ⟨.player ⟨1⟩, .acceptDraw⟩ ∈ legalActions s1 &&
      ⟨.player ⟨1⟩, .declineDraw⟩ ∈ legalActions s1 &&
      !(⟨.player ⟨0⟩, .acceptDraw⟩ ∈ legalActions s1)
    let s2 ← match step 64 s1 ⟨.player ⟨1⟩, .declineDraw⟩ with | .ok (s', _) => some s' | .error _ => none
    let declinedOk := s2.result == none && s2.tournament.idOffer == none
    let s3 ← match step 64 s2 ⟨.player ⟨1⟩, .offerDraw⟩ with | .ok (s', _) => some s' | .error _ => none
    let s4 ← match step 64 s3 ⟨.player ⟨0⟩, .acceptDraw⟩ with | .ok (s', _) => some s' | .error _ => none
    let m1 := match s4.result with | some r => MatchState.swissBo1.recordGame r | none => MatchState.swissBo1
    pure (offerInLegal && selfAcceptBlocked && oppCanAccept && declinedOk &&
      s4.result == some (.draw .agreed) &&
      (legalActions s4).isEmpty &&
      m1.outcome == some (.draw .agreed))) with
  | some b => b
  | none => false

-- 4. Top Cut prohibitions + Judge Loop Draw + Bo3 Match progression (TRP 4):
#guard match (do
    let s0 := tournBase (.tournament .topCut)
    let noIdOffer := match step 64 s0 ⟨.player ⟨0⟩, .offerDraw⟩ with | .error .illegal => true | _ => false
    let noIdInLegal := !(⟨.player ⟨0⟩, .offerDraw⟩ ∈ legalActions s0) &&
      !(⟨.player ⟨1⟩, .offerDraw⟩ ∈ legalActions s0)
    let noTimeLimit := match step 64 s0 ⟨.clock, .timeExpired⟩ with | .error .illegal => true | _ => false
    let sLoop ← match step 64 s0 ⟨.judge, .judgeLoopDraw⟩ with | .ok (s', _) => some s' | .error _ => none
    let loopOk := sLoop.result == some (.draw .loop)
    -- Bo3 match: loop draw doesn't end Top Cut match; two wins by P0 decide it
    let m1 := MatchState.topCutBo3.recordGame (.draw .loop)
    let m2 := m1.recordGame (.won [⟨0⟩])
    let m3 := m2.recordGame (.won [⟨0⟩])
    pure (noIdOffer && noIdInLegal && noTimeLimit && loopOk &&
      m1.outcome == none && m1.gamesPlayed == 1 &&
      m2.outcome == none && m2.p0Wins == 1 &&
      m3.outcome == some (.winner ⟨0⟩) && m3.gamesPlayed == 3)) with
  | some b => b
  | none => false

-- 5. Core-only ruleset rejects all tournament-specific actions (clock, ID, judge) (TRP 4):
#guard
  let s0 := tournBase .coreOnly
  (match step 64 s0 ⟨.clock, .timeExpired⟩ with | .error .illegal => true | _ => false) &&
  (match step 64 s0 ⟨.player ⟨0⟩, .offerDraw⟩ with | .error .illegal => true | _ => false) &&
  (match step 64 s0 ⟨.judge, .judgeLoopDraw⟩ with | .error .illegal => true | _ => false)
