module

public import Fab.Core.Ids

/-!
# Phases and game results

Turn phases (CR 4.1-4.4) and game outcome values covering both Comprehensive Rules hero defeat /
simultaneous draw (CR 4.5) and Tournament Rules draws (TRP 4).
-/

@[expose] public section

namespace Fab

/-- Current phase of the game (CR 4.1-4.4). -/
inductive Phase where
  /-- Start-of-Game Procedure prior to Turn 1 (CR 4.1). -/
  | setup
  /-- Start Phase of a turn (CR 4.2). -/
  | startPhase
  /-- Action Phase of a turn (CR 4.3). -/
  | actionPhase
  /-- End Phase of a turn (CR 4.4). -/
  | endPhase
deriving DecidableEq, Repr, Hashable

/-- Why a game ended in a draw (CR 4.5) (TRP 4). -/
inductive DrawReason where
  /-- All remaining heroes died simultaneously (CR 1.10.2a, 4.5). -/
  | simultaneousHeroDeath
  /-- Tournament round time limit expired after the additional turn (TRP 4). -/
  | timeLimit
  /-- Judge declared a draw due to an unbreakable loop (TRP 4). -/
  | loop
  /-- Players agreed to an intentional draw in Swiss rounds (TRP 4). -/
  | agreed
deriving DecidableEq, Repr, Hashable

/-- Final outcome of a completed game (CR 4.5) (TRP 4). -/
inductive GameResult where
  /-- One or more winning players (singleton in 1v1). -/
  | won (winners : List PlayerId)
  /-- Game ended in a draw for the given reason. -/
  | draw (reason : DrawReason)
deriving DecidableEq, Repr, Hashable

end Fab

end
