module

public import Fab.State.GameConfig
public import Fab.State.Phase

/-!
# Tournament Match Model: Swiss Bo1 and Top Cut BoN (TRP 4)

Models Flesh and Blood match structure above individual games:
- Swiss rounds use Best-of-One (`MatchFormat.bo1`): a single game win or draw immediately decides
  the match (TRP 4).
- Top Cut / elimination rounds use untimed Bo1 or Best-of-N (`MatchFormat.boN winsNeeded`) where
  intentional draws and time-limit draws do not occur (TRP 4).
-/

@[expose] public section

namespace Fab

/-- Match format specifying how individual game outcomes decide a match (TRP 4). -/
inductive MatchFormat where
  /-- Standard Flesh and Blood Swiss Best-of-One: 1 game decides the match, draws stand (TRP 4). -/
  | bo1
  /-- Elimination Best-of-N: first player to reach `winsNeeded` wins takes the match; draws do not
  award match wins (TRP 4). -/
  | boN (winsNeeded : Nat)
deriving DecidableEq, Repr, Hashable

/-- Final outcome of a completed tournament match (TRP 4). -/
inductive MatchOutcome where
  /-- Player `p` won the match. -/
  | winner (p : PlayerId)
  /-- Match ended in a draw for the given reason (Swiss Bo1). -/
  | draw (reason : DrawReason)
deriving DecidableEq, Repr, Hashable

/-- State of a 1v1 tournament match tracking game wins across games (TRP 4). -/
structure MatchState where
  /-- Swiss or Top Cut stage. -/
  stage : TournamentStage
  /-- Match format (Swiss standard is `.bo1`). -/
  format : MatchFormat
  /-- Number of games won by player 0. -/
  p0Wins : Nat := 0
  /-- Number of games won by player 1. -/
  p1Wins : Nat := 0
  /-- Total games completed in this match. -/
  gamesPlayed : Nat := 0
  /-- Final match outcome once decided, `none` while match is still ongoing. -/
  outcome : Option MatchOutcome := none
deriving DecidableEq, Repr

namespace MatchState

/-- Initial Swiss Best-of-One match state (TRP 4). -/
def swissBo1 : MatchState :=
  { stage := .swiss, format := .bo1 }

/-- Initial Top Cut Best-of-1 untimed match state (TRP 4). -/
def topCutBo1 : MatchState :=
  { stage := .topCut, format := .boN 1 }

/-- Initial Top Cut Best-of-3 untimed match state (TRP 4). -/
def topCutBo3 : MatchState :=
  { stage := .topCut, format := .boN 2 }

/-- Game configuration corresponding to this match's tournament stage (TRP 4). -/
def gameConfig (m : MatchState) (fmt : Format := .classicConstructed)
    (banList : FormatBanList := .empty) : GameConfig :=
  { ruleSet := .tournament m.stage, format := fmt, mode := .duel, banList := banList }

/-- Record a completed 1v1 `GameResult` into the match state (TRP 4). No-op if the match is
already decided. -/
def recordGame (m : MatchState) (res : GameResult) : MatchState :=
  if m.outcome.isSome then m
  else
    let played := m.gamesPlayed + 1
    match m.format, res with
    | .bo1, .won [w] =>
      let w0 := if w == ⟨0⟩ then m.p0Wins + 1 else m.p0Wins
      let w1 := if w == ⟨1⟩ then m.p1Wins + 1 else m.p1Wins
      { m with p0Wins := w0, p1Wins := w1, gamesPlayed := played, outcome := some (.winner w) }
    | .bo1, .draw reason =>
      { m with gamesPlayed := played, outcome := some (.draw reason) }
    | .bo1, .won _ =>
      { m with gamesPlayed := played }
    | .boN needed, .won [w] =>
      let w0 := if w == ⟨0⟩ then m.p0Wins + 1 else m.p0Wins
      let w1 := if w == ⟨1⟩ then m.p1Wins + 1 else m.p1Wins
      let out :=
        if w == ⟨0⟩ && needed ≤ w0 then some (.winner ⟨0⟩)
        else if w == ⟨1⟩ && needed ≤ w1 then some (.winner ⟨1⟩)
        else none
      { m with p0Wins := w0, p1Wins := w1, gamesPlayed := played, outcome := out }
    | .boN _, .draw _ =>
      { m with gamesPlayed := played }
    | .boN _, .won _ =>
      { m with gamesPlayed := played }

/-- A Swiss Bo1 match is decided in exactly 1 game for any valid 1v1 win result (TRP 4). -/
theorem swissBo1_decides_win (w : PlayerId) :
    (MatchState.swissBo1.recordGame (.won [w])).outcome = some (.winner w) ∧
    (MatchState.swissBo1.recordGame (.won [w])).gamesPlayed = 1 := by
  simp [swissBo1, recordGame]

/-- A Swiss Bo1 match is decided in exactly 1 game for any draw result (TRP 4). -/
theorem swissBo1_decides_draw (r : DrawReason) :
    (MatchState.swissBo1.recordGame (.draw r)).outcome = some (.draw r) ∧
    (MatchState.swissBo1.recordGame (.draw r)).gamesPlayed = 1 := by
  simp [swissBo1, recordGame]

/-- A Top Cut match configuration always prohibits Intentional Draws and round time limits (TRP 4). -/
theorem topCut_config_rules (m : MatchState) (hm : m.stage = .topCut)
    (fmt : Format) (bl : FormatBanList) :
    (m.gameConfig fmt bl).ruleSet.allowsIntentionalDraw = false ∧
    (m.gameConfig fmt bl).ruleSet.hasTimeLimit = false := by
  simp [gameConfig, hm, RuleSet.allowsIntentionalDraw, RuleSet.hasTimeLimit]

end MatchState

end Fab

end
