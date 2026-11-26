module

public import Fab.Spec.Legal

/-!
# The engine (`step`, `advance`, `legalActions`)

`step` checks `Legal`, applies the action, and runs `advance` through automatic work frames up
to `fuel` steps (design.md §6.1). `legalActions` constructively enumerates every legal player
action from the board state (design.md §6.3).
-/

@[expose] public section

namespace Fab

/-- Why `step` failed (design.md §6.1). -/
inductive RuleError where
  /-- The submitted `Action` does not satisfy `Legal`. -/
  | illegal
  /-- Automatic work did not reach a decision frame or game end within `fuel` steps. -/
  | fuelExhausted
  /-- Internal invariant violation (proved impossible under `WF ∧ OwnerOk` by I4). -/
  | internal (msg : String)
deriving DecidableEq, Repr

/-- Advance automatic work frames one `microStep` at a time up to `fuel` steps (structural
recursion on `fuel`: design.md §6.1). -/
def advance : Nat → GameState → List Event → Except RuleError (GameState × List Event)
  | 0, s, es =>
    match s.pending with
    | f :: _ => if f.isWork then .error .fuelExhausted else .ok (s, es)
    | [] => .ok (s, es)
  | n + 1, s, es =>
    match s.pending with
    | f :: _ =>
      if f.isWork then
        match microStep s with
        | some (s', es') => advance n s' (es ++ es')
        | none => .error (.internal "microStep")
      else .ok (s, es)
    | [] => .ok (s, es)

/-- Submit one `Action` and advance to the next decision point or end of game (design.md §6.1). -/
def step (fuel : Nat) (s : GameState) (a : Action) :
    Except RuleError (GameState × List Event) :=
  if Legal s a then
    match applyAction s a with
    | some (s1, es) => advance fuel s1 es
    | none => .error (.internal "applyAction")
  else
    .error .illegal

/-- Constructively enumerate all legal player actions answering the top frame (chance actions
are intentionally omitted: design.md §6.3). -/
def legalFrameActions (s : GameState) : List Action :=
  match s.pending with
  | .chooseFirstPlayer chooser :: _ =>
    (allPlayers s.playerCount).map fun first => ⟨.player chooser, .pickFirstPlayer first⟩
  | .chooseLoadout p :: _ =>
    let inv := s.zone (.player p .inventory)
    let equips := (inv.filter fun id => (loadoutEquipDest? s p id).isSome).map
      fun id => ⟨.player p, .loadoutEquip id⟩
    let toDeck := (inv.filter fun id => loadoutCanAddDeck s p id).map
      fun id => ⟨.player p, .loadoutToDeck id⟩
    let done := if loadoutCanFinish s p then [⟨.player p, .loadoutDone⟩] else []
    equips ++ toDeck ++ done
  | .priority p _ :: _ =>
    let candidates := playCardCandidateIds s p
    let plays := (candidates.filter (canPlayCard s p)).map fun id => ⟨.player p, .playCard id⟩
    let weapons := ((weaponAttackCandidateIds s p).filter (canAttackWithWeapon s p)).map
      fun wid => ⟨.player p, .attackWeapon wid⟩
    let abilities := (availableActivations s p).map fun (source, index, target, secondTarget) =>
      (⟨.player p, .activateAbility source index target secondTarget⟩ : Action)
    ⟨.player p, .pass⟩ :: (plays ++ weapons ++ abilities)
  | .defendPick defender :: _ =>
    let defs :=
      match s.combat.bind CombatChain.activeLink? with
      | some link =>
        ((defendCandidateIds s defender).filter (canDefendWith s link defender)).map
          fun id => ⟨.player defender, .defendCard id⟩
      | none => []
    defs ++ [⟨.player defender, .defendDone⟩]
  | .chooseMode p layerId _ modeCount _ :: _ =>
    (((List.range modeCount).filter (canPickCardMode s layerId)).map fun idx => ⟨.player p, .pickMode idx⟩) ++
      [⟨.player p, .cancelPlay⟩]
  | .choosePlayHero p _ _ _ _ :: _ =>
    (s.turnOrder.map fun hero => ⟨.player p, .pickHeroTarget hero⟩) ++
      [⟨.player p, .cancelPlay⟩]
  | .choosePlayWeapon p _ _ _ _ candidates :: _ =>
    candidates.map (fun id => ⟨.player p, .pickWeaponTarget id⟩) ++ [⟨.player p, .cancelPlay⟩]
  | .choosePitch p _ _ _ _ :: _ =>
    ((pitchableCards s p).map fun id => ⟨.player p, .pitchCard id⟩) ++
      [⟨.player p, .cancelPlay⟩]
  | .choosePreventionPitch p :: _ =>
    (pitchableCards s p).map fun id => ⟨.player p, .pitchCard id⟩
  | .chooseOptionalPlayCost p _ _ _ _ _ :: _ =>
    [⟨.player p, .pickMay true⟩, ⟨.player p, .pickMay false⟩, ⟨.player p, .cancelPlay⟩]
  | .chooseVariableResources p _ _ _ _ limit optional :: _ =>
    (if optional then [⟨.player p, .pickVariableResources none⟩] else []) ++
      (⟨.player p, .cancelPlay⟩ ::
        (List.range (limit + 1)).map fun x => ⟨.player p, .pickVariableResources (some x)⟩)
  | .chooseGraveyardCost p _ _ _ _ candidates :: _ =>
    [⟨.player p, .pickGraveyardCost none⟩, ⟨.player p, .cancelPlay⟩] ++
      candidates.map fun id => ⟨.player p, .pickGraveyardCost (some id)⟩
  | .chooseHandCardCost p _ _ _ cost :: _ =>
    (((s.zone (.player p .hand)).filter (canPickHandCostCard s p cost)).map fun id =>
      ⟨.player p, .pickHandCostCard id⟩) ++ [⟨.player p, .cancelPlay⟩]
  | .chooseMay ctrl _ _ _ _ _ :: _ =>
    [⟨.player ctrl, .pickMay true⟩, ⟨.player ctrl, .pickMay false⟩]
  | .chooseModal ctrl _ _ _ modes :: _ =>
    (List.range modes.length).map fun idx => ⟨.player ctrl, .pickMode idx⟩
  | .chooseHandToDeck p _ :: _ =>
    (s.zone (.player p .hand)).map fun id => ⟨.player p, .handToDeckPick id⟩
  | .chooseDiscard p remaining candidates _ :: _ =>
    if 0 < remaining then candidates.map (fun id => ⟨.player p, .pickDiscardCard id⟩) else []
  | .chooseShuffleCards p remaining candidates selected _ search :: _ =>
    (if shuffleSelectionCanConfirm selected search then [⟨.player p, .pickShuffleCard none⟩] else []) ++
      (if 0 < remaining then candidates.map (fun id => ⟨.player p, .pickShuffleCard (some id)⟩) else [])
  | .chooseOpt p _ others _ _ :: _ =>
    (none :: others.map some).flatMap fun choice =>
      [⟨.player p, .optPick true choice⟩, ⟨.player p, .optPick false choice⟩]
  | .chooseArsenal tp :: _ =>
    let puts :=
      if (s.zone (.player tp .arsenal)).isEmpty then
        (s.zone (.player tp .hand)).map fun id => ⟨.player tp, .arsenalPut id⟩
      else
        []
    puts ++ [⟨.player tp, .arsenalSkip⟩]
  | .choosePitchOrder p :: _ =>
    (s.zone (.player p .pitch)).map fun id => ⟨.player p, .pitchReturnPick id⟩
  | .chooseTriggerStart tp :: _ =>
    s.turnOrder.map fun start => ⟨.player tp, .pickTriggerStart start⟩
  | .chooseTriggerOrder p _ :: _ =>
    (s.pendingTriggers.filter fun t => t.controller == p).flatMap fun t =>
      (t.targetChoices s).map fun target => ⟨.player p, .pickTrigger t.id target.1 target.2⟩
  | .chooseTriggerGraveyard p _ _ _ candidates _ :: _ =>
    candidates.map fun id => ⟨.player p, .pickTriggerGraveyardCard id⟩
  | .chooseReplacement aff _ cands canDecl :: _ =>
    (cands.map fun cid => ⟨.player aff, .pickReplacement (some cid)⟩) ++
      (if canDecl then [⟨.player aff, .pickReplacement none⟩] else [])
  | _ => []

/-- Constructively enumerate legal concessions in a 1v1 game (CR 4.5). -/
def concedeActions (s : GameState) : List Action :=
  if s.playerCount = 2 then (allPlayers 2).map fun p => ⟨.player p, .concede⟩ else []

/-- Constructively enumerate legal player tournament actions (Swiss Bo1 Intentional Draw offer,
accept, or decline) (TRP 4). Clock and judge actions are non-player actors and omitted here. -/
def tournamentPlayerActions (s : GameState) : List Action :=
  if s.playerCount = 2 ∧ s.config.ruleSet.allowsIntentionalDraw = true then
    match s.tournament.idOffer with
    | none =>
      (allPlayers 2).map fun p => ⟨.player p, .offerDraw⟩
    | some q =>
      ((allPlayers 2).filter fun p => decide (q ≠ p)).flatMap fun p =>
        [⟨.player p, .acceptDraw⟩, ⟨.player p, .declineDraw⟩]
  else
    []

/-- All legal player actions in state `s` (empty once the game has ended). -/
def legalActions (s : GameState) : List Action :=
  if s.result = none then
    legalFrameActions s ++ concedeActions s ++ tournamentPlayerActions s
  else
    []

end Fab

end
