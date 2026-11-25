module

public import Fab.State.GameConfig

/-!
# Tournament time-limit and intentional-draw state (TRP 4)

Tracks per-game tournament metadata independent of `BoardSnapshot` (so cancelling an in-progress
card play never undoes the round clock or an intentional-draw offer):
- `timeLimitTurnsLeft`: `none` before round time expires; `some 1` once `Actor.clock` signals
  time-up (current turn finishes + 1 additional turn); decrements to `some 0` when the additional
  turn begins; triggers `GameResult.draw .timeLimit` if the game is still undecided when the
  additional turn ends (TRP 4).
- `idOffer`: `some p` when player `p` has offered an Intentional Draw in a Swiss Bo1 round (TRP 4).
-/

@[expose] public section

namespace Fab

/-- Per-game tournament state carried on `GameState` (TRP 4). -/
structure TournamentState where
  /-- Additional turns remaining to start after round time expires: `none` while timed play is
  ongoing, `some 1` on the turn time expires (1 additional turn left to start), `some 0` during
  the final additional turn (TRP 4). -/
  timeLimitTurnsLeft : Option Nat := none
  /-- Player currently offering an Intentional Draw in Swiss rounds, if any (TRP 4). -/
  idOffer : Option PlayerId := none
deriving DecidableEq, Repr

namespace TournamentState

/-- Empty tournament state at the start of a game. -/
def empty : TournamentState := {}

/-- Start the End-of-Round Procedure when the round clock expires: the current turn finishes and
1 additional turn remains to be started (TRP 4). -/
def startTimeLimit (ts : TournamentState) : TournamentState :=
  { ts with timeLimitTurnsLeft := some 1 }

/-- Record an Intentional Draw offer from player `p` (TRP 4). -/
def setIdOffer (ts : TournamentState) (p : PlayerId) : TournamentState :=
  { ts with idOffer := some p }

/-- Clear any pending Intentional Draw offer (TRP 4). -/
def clearIdOffer (ts : TournamentState) : TournamentState :=
  { ts with idOffer := none }

/-- Advance the time-limit countdown at a turn boundary (`beginTurn`) (TRP 4):
- `none` → continues normal play (`some ts`).
- `some (k + 1)` → consumes 1 additional turn (`some { ts with timeLimitTurnsLeft := some k }`).
- `some 0` → additional turn has ended; returns `none` signaling `GameResult.draw .timeLimit`. -/
def tickAtTurnStart (ts : TournamentState) : Option TournamentState :=
  match ts.timeLimitTurnsLeft with
  | none => some ts
  | some 0 => none
  | some (k + 1) => some { ts with timeLimitTurnsLeft := some k }

/-- When `timeLimitTurnsLeft = some (k + 1)`, `tickAtTurnStart` strictly decrements the remaining
turn count by 1. -/
theorem tickAtTurnStart_succ (ts : TournamentState) (k : Nat)
    (h : ts.timeLimitTurnsLeft = some (k + 1)) :
    ts.tickAtTurnStart = some { ts with timeLimitTurnsLeft := some k } := by
  unfold tickAtTurnStart
  rw [h]

/-- When `timeLimitTurnsLeft = some 0`, `tickAtTurnStart` returns `none` (time-limit draw). -/
theorem tickAtTurnStart_zero (ts : TournamentState) (h : ts.timeLimitTurnsLeft = some 0) :
    ts.tickAtTurnStart = none := by
  unfold tickAtTurnStart
  rw [h]

end TournamentState

end Fab

end
