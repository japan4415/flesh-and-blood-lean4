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
  | .priority p _ :: _, .player q, .activateAbility source index target =>
    q = p ∧ (source, index, target) ∈ availableActivations s p
  | .defendPick defender :: _, .player q, .defendCard id =>
    q = defender ∧
    match s.combat.bind CombatChain.activeLink? with
    | some link => canDefendWith s link defender id = true
    | none => False
  | .defendPick defender :: _, .player q, .defendDone =>
    q = defender
  | .chooseMode p layerId _ modeCount _ :: _, .player q, .pickMode idx =>
    q = p ∧ idx < modeCount ∧ canPickCardMode s layerId idx = true
  | .chooseMode p _ _ _ _ :: _, .player q, .cancelPlay =>
    q = p
  | .choosePlayHero p _ _ _ _ :: _, .player q, .pickHeroTarget hero =>
    q = p ∧ hero ∈ s.turnOrder
  | .choosePlayHero p _ _ _ _ :: _, .player q, .cancelPlay =>
    q = p
  | .choosePlayWeapon p _ _ _ _ candidates :: _, .player q, .pickWeaponTarget id =>
    q = p ∧ id ∈ candidates
  | .choosePlayWeapon p _ _ _ _ _ :: _, .player q, .cancelPlay =>
    q = p
  | .choosePitch p _ _ _ _ :: _, .player q, .pitchCard id =>
    q = p ∧ canPitchCard s p id = true
  | .choosePitch p _ _ _ _ :: _, .player q, .cancelPlay =>
    q = p
  | .chooseOptionalResources p _ _ _ _ _ :: _, .player q, .pickMay _
  | .chooseOptionalResources p _ _ _ _ _ :: _, .player q, .cancelPlay =>
    q = p
  | .chooseVariableResources p _ _ _ _ limit :: _, .player q, .pickVariableResources amount =>
    q = p ∧ amount.all (· ≤ limit) = true
  | .chooseVariableResources p _ _ _ _ _ :: _, .player q, .cancelPlay =>
    q = p
  | .chooseGraveyardCost p _ _ _ _ candidates :: _, .player q, .pickGraveyardCost choice =>
    q = p ∧ choice.all candidates.contains = true
  | .chooseGraveyardCost p _ _ _ _ _ :: _, .player q, .cancelPlay =>
    q = p
  | .chooseHandCardCost p _ _ _ cost :: _, .player q, .pickHandCostCard id =>
    q = p ∧ canPickHandCostCard s p cost id = true
  | .chooseHandCardCost p _ _ _ _ :: _, .player q, .cancelPlay =>
    q = p
  | .chooseMay ctrl _ _ _ _ _ :: _, .player q, .pickMay _ =>
    q = ctrl
  | .chooseModal ctrl _ _ _ modes :: _, .player q, .pickMode idx =>
    q = ctrl ∧ idx < modes.length
  | .chanceDie6 _ _ _ _ _ _ _ :: _, .chance, .die6Roll roll =>
    1 ≤ roll ∧ roll ≤ 6
  | .chooseHandToDeck p _ :: _, .player q, .handToDeckPick id =>
    q = p ∧ id ∈ s.zone (.player p .hand)
  | .chooseDiscard p remaining candidates _ :: _, .player q, .pickDiscardCard id =>
    q = p ∧ 0 < remaining ∧ id ∈ candidates
  | .chooseShuffleCards p remaining candidates selected _ search :: _, .player q, .pickShuffleCard choice =>
    q = p ∧ match choice with
    | some id => 0 < remaining ∧ id ∈ candidates
    | none => shuffleSelectionCanConfirm selected search = true
  | .chooseOpt p _ :: _, .player q, .optPick _ =>
    q = p
  | .chooseArsenal tp :: _, .player q, .arsenalPut id =>
    q = tp ∧ (s.zone (.player tp .arsenal)).isEmpty = true ∧ id ∈ s.zone (.player tp .hand)
  | .chooseArsenal tp :: _, .player q, .arsenalSkip =>
    q = tp
  | .choosePitchOrder p :: _, .player q, .pitchReturnPick id =>
    q = p ∧ id ∈ s.zone (.player p .pitch)
  | .chooseTriggerStart tp :: _, .player q, .pickTriggerStart start =>
    q = tp ∧ start ∈ s.turnOrder
  | .chooseTriggerOrder p _ :: _, .player q, .pickTrigger tid hero equipment =>
    q = p ∧ (s.pendingTriggers.any fun t => t.matchesDeclaration s tid p hero equipment) = true
  | .chooseTriggerGraveyard p _ _ _ candidates _ :: _, .player q, .pickTriggerGraveyardCard id =>
    q = p ∧ id ∈ candidates
  | .chooseReplacement aff _ cands canDecl :: _, .player q, .pickReplacement choice =>
    q = aff ∧
    match choice with
    | some cid => cid ∈ cands
    | none => canDecl = true
  | _, _, _ => False

set_option maxHeartbeats 400000 in
instance decidableLegalFrame (s : GameState) (a : Action) : Decidable (LegalFrame s a) := by
  unfold LegalFrame
  cases s.pending with
  | nil => exact isFalse id
  | cons f rest =>
    cases f <;> cases a.actor <;> cases a.kind <;>
      first
      | infer_instance
      | (dsimp only; cases s.combat.bind CombatChain.activeLink? <;> infer_instance)
      | (rename_i choice; dsimp only; cases choice <;> infer_instance)

/-- Legality of conceding: in a 1v1 game, any seated player may concede at any time while the
game is ongoing (CR 4.5). -/
def LegalConcede (s : GameState) (a : Action) : Prop :=
  match a.actor, a.kind with
  | .player p, .concede => s.playerCount = 2 ∧ p.n < 2
  | _, _ => False

instance decidableLegalConcede (s : GameState) (a : Action) : Decidable (LegalConcede s a) := by
  unfold LegalConcede
  cases a.actor <;> cases a.kind <;> infer_instance

/-- Legality of tournament-level actions (clock time limit, Swiss intentional draw, judge loop
draw) (TRP 4). -/
def LegalTournament (s : GameState) (a : Action) : Prop :=
  match a.actor, a.kind with
  | .clock, .timeExpired =>
    s.config.ruleSet.hasTimeLimit = true ∧ s.tournament.timeLimitTurnsLeft = none
  | .judge, .judgeLoopDraw =>
    s.config.ruleSet.isTournament = true
  | .player p, .offerDraw =>
    s.playerCount = 2 ∧ p.n < 2 ∧ s.config.ruleSet.allowsIntentionalDraw = true ∧
    s.tournament.idOffer = none
  | .player p, .acceptDraw =>
    s.playerCount = 2 ∧ p.n < 2 ∧ s.config.ruleSet.allowsIntentionalDraw = true ∧
    match s.tournament.idOffer with
    | some q => q ≠ p
    | none => False
  | .player p, .declineDraw =>
    s.playerCount = 2 ∧ p.n < 2 ∧ s.config.ruleSet.allowsIntentionalDraw = true ∧
    match s.tournament.idOffer with
    | some q => q ≠ p
    | none => False
  | _, _ => False

instance decidableLegalTournament (s : GameState) (a : Action) : Decidable (LegalTournament s a) := by
  unfold LegalTournament
  cases a.actor <;> cases a.kind <;>
    first | infer_instance | (dsimp only; cases s.tournament.idOffer <;> infer_instance)

/-- Overall legality specification `Legal s a` (design.md §6.3). Nothing is legal after the game
has ended. -/
def Legal (s : GameState) (a : Action) : Prop :=
  s.result = none ∧ (LegalFrame s a ∨ LegalConcede s a ∨ LegalTournament s a)

instance decidableLegal (s : GameState) (a : Action) : Decidable (Legal s a) := by
  unfold Legal
  infer_instance

end Fab

end
