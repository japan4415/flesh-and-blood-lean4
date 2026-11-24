module

public import Fab.Rules.Frames

/-!
# Independent legality specification `Legal`

Defines `Legal s a : Prop` directly from the Comprehensive Rules and Tournament Rules,
independently of `step` and `legalActions` (design.md §3 P1, §6.3).
-/

@[expose] public section

namespace Fab

/-- Legality of answering the top decision frame on `s.pending` (CR 4.1). -/
def LegalFrame (s : GameState) (a : Action) : Prop :=
  match s.pending, a.actor, a.kind with
  | .chanceFirstPlayer :: _, .chance, .chanceFirstChooser p =>
    p.n < s.playerCount
  | .chooseFirstPlayer chooser :: _, .player p, .pickFirstPlayer first =>
    p = chooser ∧ first.n < s.playerCount
  | .chooseLoadout p :: _, .player q, .loadoutEquip id =>
    q = p ∧ (loadoutEquipDest? s p id).isSome = true
  | .chooseLoadout p :: _, .player q, .loadoutToDeck id =>
    q = p ∧ loadoutCanAddDeck s p id = true
  | .chooseLoadout p :: _, .player q, .loadoutDone =>
    q = p ∧ loadoutCanFinish s p = true
  | .chanceShuffle z :: _, .chance, .shuffleOrder l =>
    z.Valid s.playerCount ∧ l.Perm (s.zone z)
  | _, _, _ => False

instance decidableLegalFrame (s : GameState) (a : Action) : Decidable (LegalFrame s a) := by
  unfold LegalFrame
  cases s.pending with
  | nil => exact isFalse id
  | cons f rest =>
    cases f <;> cases a.actor <;> cases a.kind <;> infer_instance

/-- Legality of conceding: in a 1v1 game, any seated player may concede at any time while the
game is ongoing (CR 4.5). -/
def LegalConcede (s : GameState) (a : Action) : Prop :=
  match a.actor, a.kind with
  | .player p, .concede => s.playerCount = 2 ∧ p.n < 2
  | _, _ => False

instance decidableLegalConcede (s : GameState) (a : Action) : Decidable (LegalConcede s a) := by
  unfold LegalConcede
  cases a.actor <;> cases a.kind <;> infer_instance

/-- Overall legality specification `Legal s a` (design.md §6.3). Nothing is legal after the game
has ended. -/
def Legal (s : GameState) (a : Action) : Prop :=
  s.result = none ∧ (LegalFrame s a ∨ LegalConcede s a)

instance decidableLegal (s : GameState) (a : Action) : Decidable (Legal s a) := by
  unfold Legal
  infer_instance

end Fab

end
