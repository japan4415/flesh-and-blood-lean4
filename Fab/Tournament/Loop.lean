module

public import Fab.State.GameState

/-!
# Tournament Actions: Judge Loop Draw, Clock Time-Limit, and Intentional Draw (TRP 4)

Implements the pure state transitions for tournament-level actions outside normal CR game frames:
- `applyTimeExpired`: `Actor.clock` signals round time expiration (current turn + 1 additional turn).
- `applyOfferDraw` / `applyAcceptDraw` / `applyDeclineDraw`: Swiss Bo1 Intentional Draw negotiation.
- `applyJudgeLoopDraw`: `Actor.judge` declares a draw for an unbreakable mandatory loop (TRP 4).

Every transition preserves `WF`, `OwnerOk`, `RollbackOk`, `physIds` (I1), and `config`.
-/

@[expose] public section

namespace Fab

/-- Apply `Actor.clock` time-expired signal: starts the End-of-Round countdown (current turn
finishes + 1 additional turn) without touching board state or pending frames (TRP 4). -/
def applyTimeExpired (s : GameState) : GameState :=
  { s with tournament := s.tournament.startTimeLimit }

/-- Record an Intentional Draw offer from player `p` in a Swiss round (TRP 4). -/
def applyOfferDraw (s : GameState) (p : PlayerId) : GameState :=
  { s with tournament := s.tournament.setIdOffer p }

/-- Accept a pending Intentional Draw offer in a Swiss round, ending the game in `.draw .agreed`
(TRP 4). -/
def applyAcceptDraw (s : GameState) : GameState :=
  { s with
    result := some (.draw .agreed)
    pending := []
    playRollback := none
    tournament := s.tournament.clearIdOffer }

/-- Decline a pending Intentional Draw offer, clearing `idOffer` so play continues (TRP 4). -/
def applyDeclineDraw (s : GameState) : GameState :=
  { s with tournament := s.tournament.clearIdOffer }

/-- Apply `Actor.judge` mandatory loop draw ruling, ending the game in `.draw .loop` (TRP 4). -/
def applyJudgeLoopDraw (s : GameState) : GameState :=
  { s with
    result := some (.draw .loop)
    pending := []
    playRollback := none
    tournament := s.tournament.clearIdOffer }

/-- `applyTimeExpired` preserves `WF`, `OwnerOk`, `RollbackOk`, `physIds`, and `config`. -/
theorem applyTimeExpired_inv {s : GameState} (hwf : s.WF) (hok : s.OwnerOk) (hrb : s.RollbackOk) :
    (applyTimeExpired s).WF ∧ (applyTimeExpired s).OwnerOk ∧ (applyTimeExpired s).RollbackOk ∧
    (applyTimeExpired s).physIds = s.physIds ∧ (applyTimeExpired s).config = s.config :=
  ⟨GameState.WF.congr hwf rfl rfl rfl rfl,
   GameState.OwnerOk.congr hok rfl rfl,
   GameState.RollbackOk.preserve hrb rfl rfl (List.Perm.refl _),
   rfl, rfl⟩

/-- `applyOfferDraw` preserves `WF`, `OwnerOk`, `RollbackOk`, `physIds`, and `config`. -/
theorem applyOfferDraw_inv {s : GameState} (hwf : s.WF) (hok : s.OwnerOk) (hrb : s.RollbackOk)
    (p : PlayerId) :
    (applyOfferDraw s p).WF ∧ (applyOfferDraw s p).OwnerOk ∧ (applyOfferDraw s p).RollbackOk ∧
    (applyOfferDraw s p).physIds = s.physIds ∧ (applyOfferDraw s p).config = s.config :=
  ⟨GameState.WF.congr hwf rfl rfl rfl rfl,
   GameState.OwnerOk.congr hok rfl rfl,
   GameState.RollbackOk.preserve hrb rfl rfl (List.Perm.refl _),
   rfl, rfl⟩

/-- `applyAcceptDraw` preserves `WF`, `OwnerOk`, `RollbackOk`, `physIds`, and `config`. -/
theorem applyAcceptDraw_inv {s : GameState} (hwf : s.WF) (hok : s.OwnerOk) :
    (applyAcceptDraw s).WF ∧ (applyAcceptDraw s).OwnerOk ∧ (applyAcceptDraw s).RollbackOk ∧
    (applyAcceptDraw s).physIds = s.physIds ∧ (applyAcceptDraw s).config = s.config :=
  ⟨GameState.WF.congr hwf rfl rfl rfl rfl,
   GameState.OwnerOk.congr hok rfl rfl,
   GameState.RollbackOk.of_none rfl,
   rfl, rfl⟩

/-- `applyDeclineDraw` preserves `WF`, `OwnerOk`, `RollbackOk`, `physIds`, and `config`. -/
theorem applyDeclineDraw_inv {s : GameState} (hwf : s.WF) (hok : s.OwnerOk) (hrb : s.RollbackOk) :
    (applyDeclineDraw s).WF ∧ (applyDeclineDraw s).OwnerOk ∧ (applyDeclineDraw s).RollbackOk ∧
    (applyDeclineDraw s).physIds = s.physIds ∧ (applyDeclineDraw s).config = s.config :=
  ⟨GameState.WF.congr hwf rfl rfl rfl rfl,
   GameState.OwnerOk.congr hok rfl rfl,
   GameState.RollbackOk.preserve hrb rfl rfl (List.Perm.refl _),
   rfl, rfl⟩

/-- `applyJudgeLoopDraw` preserves `WF`, `OwnerOk`, `RollbackOk`, `physIds`, and `config`. -/
theorem applyJudgeLoopDraw_inv {s : GameState} (hwf : s.WF) (hok : s.OwnerOk) :
    (applyJudgeLoopDraw s).WF ∧ (applyJudgeLoopDraw s).OwnerOk ∧ (applyJudgeLoopDraw s).RollbackOk ∧
    (applyJudgeLoopDraw s).physIds = s.physIds ∧ (applyJudgeLoopDraw s).config = s.config :=
  ⟨GameState.WF.congr hwf rfl rfl rfl rfl,
   GameState.OwnerOk.congr hok rfl rfl,
   GameState.RollbackOk.of_none rfl,
   rfl, rfl⟩

end Fab

end
