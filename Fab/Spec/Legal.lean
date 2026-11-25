module

public import Fab.Rules.Frames

/-!
# Independent legality specification `Legal`

Defines `Legal s a : Prop` directly from the Comprehensive Rules and Tournament Rules,
independently of `step` and `legalActions` (design.md §3 P1, §6.3).
-/

@[expose] public section

namespace Fab

/-- Legality of answering the top decision frame on `s.pending` (CR 1.11, 4.1-4.4). -/
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
  | .priority p _ :: _, .player q, .pass =>
    q = p
  | .priority p _ :: _, .player q, .playCard id =>
    q = p ∧ canPlayCard s p id = true
  | .priority p _ :: _, .player q, .attackWeapon wid =>
    q = p ∧ canAttackWithWeapon s p wid = true
  | .defendPick defender :: _, .player q, .defendCard id =>
    q = defender ∧
    match s.combat.bind CombatChain.activeLink? with
    | some link => canDefendWith s link defender id = true
    | none => False
  | .defendPick defender :: _, .player q, .defendDone =>
    q = defender
  | .chooseMode p _ _ modeCount _ :: _, .player q, .pickMode idx =>
    q = p ∧ idx < modeCount
  | .chooseMode p _ _ _ _ :: _, .player q, .cancelPlay =>
    q = p
  | .choosePitch p _ _ _ _ :: _, .player q, .pitchCard id =>
    q = p ∧ canPitchCard s p id = true
  | .choosePitch p _ _ _ _ :: _, .player q, .cancelPlay =>
    q = p
  | .chooseMay ctrl _ _ _ _ _ :: _, .player q, .pickMay _ =>
    q = ctrl
  | .chooseModal ctrl _ _ _ modes :: _, .player q, .pickMode idx =>
    q = ctrl ∧ idx < modes.length
  | .chanceDie6 _ _ _ _ _ _ _ :: _, .chance, .die6Roll roll =>
    1 ≤ roll ∧ roll ≤ 6
  | .chooseHandToDeck p _ :: _, .player q, .handToDeckPick id =>
    q = p ∧ id ∈ s.zone (.player p .hand)
  | .chooseOpt p _ :: _, .player q, .optPick _ =>
    q = p
  | .chooseArsenal tp :: _, .player q, .arsenalPut id =>
    q = tp ∧ (s.zone (.player tp .arsenal)).isEmpty = true ∧ id ∈ s.zone (.player tp .hand)
  | .chooseArsenal tp :: _, .player q, .arsenalSkip =>
    q = tp
  | .choosePitchOrder p :: _, .player q, .pitchReturnPick id =>
    q = p ∧ id ∈ s.zone (.player p .pitch)
  | _, _, _ => False

instance decidableLegalFrame (s : GameState) (a : Action) : Decidable (LegalFrame s a) := by
  unfold LegalFrame
  cases s.pending with
  | nil => exact isFalse id
  | cons f rest =>
    cases f <;> cases a.actor <;> cases a.kind <;>
      first | infer_instance | (dsimp only; cases s.combat.bind CombatChain.activeLink? <;> infer_instance)

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
