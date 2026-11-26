module

public import Fab.State.Zone
public import Fab.State.Combat
public import Fab.Core.Cost
public import Fab.Core.Property
public import Fab.Card.IR.Effect
public import Fab.Rules.Triggers
public import Fab.Rules.Replacement

/-!
# Actors, actions, and continuation frames

All player choices and external random/tournament inputs are modeled explicitly as `Action`s
answering the top `Frame` of `GameState.pending` (design.md §3 P4-P5, §6.2).
Frames never store stale copies of board lists; they store only the question being asked.
-/

@[expose] public section

namespace Fab

/-- All seated players `[0, 1, ..., n - 1]`. -/
def allPlayers (n : Nat) : List PlayerId :=
  (List.range n).map PlayerId.mk

/-- Every seated player `p` with `p.n < n` belongs to `allPlayers n`. -/
theorem mem_allPlayers_iff {n : Nat} {p : PlayerId} :
    p ∈ allPlayers n ↔ p.n < n := by
  unfold allPlayers
  simp only [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact hi
  · intro h; exact ⟨p.n, h, by cases p; rfl⟩

/-- Who supplies an `Action` (design.md §6.2). -/
inductive Actor where
  /-- A seated player making a strategic choice. -/
  | player (p : PlayerId)
  /-- External randomness (deck shuffle, random first-player-chooser selection). -/
  | chance
  /-- Tournament clock signaling end-of-round time limit (TRP 4). -/
  | clock
  /-- Tournament judge signaling a loop draw (TRP 4). -/
  | judge
deriving DecidableEq, Repr, Hashable

/-- Whether an `Actor` is a human/AI player (only player actions are enumerated by
`legalActions`: design.md §6.3). -/
def Actor.isPlayer : Actor → Bool
  | .player _ => true
  | _ => false

/-- Content of an `Action` answering a decision frame or conceding (CR 4.1-4.5). -/
inductive ActionKind where
  /-- Chance selects which player chooses who goes first (CR 4.1.3). -/
  | chanceFirstChooser (p : PlayerId)
  /-- Chosen player picks who takes the first turn (CR 4.1.3). -/
  | pickFirstPlayer (first : PlayerId)
  /-- Pre-game loadout: move equipment or weapon `id` from inventory to its arena zone (CR 4.1.4). -/
  | loadoutEquip (id : ObjId)
  /-- Pre-game loadout: move deck-card `id` from inventory into the starting deck (CR 4.1.4). -/
  | loadoutToDeck (id : ObjId)
  /-- Pre-game loadout: finish configuring equipment and starting deck (CR 4.1.4). -/
  | loadoutDone
  /-- Chance provides a shuffled permutation of a zone (CR 4.1.5). -/
  | shuffleOrder (order : List ObjId)
  /-- Pass priority (CR 1.11, 4.3.3). -/
  | pass
  /-- Announce playing card `id` from hand or arsenal while holding priority (CR 5.1.1). -/
  | playCard (id : ObjId) (asInstant : Bool := false)
  /-- Activate a weapon attack using weapon `weaponId` in the player's weapon zone (CR 1.4.3, 7.1). -/
  | attackWeapon (weaponId : ObjId)
  /-- Activate an indexed ability while holding priority. If the ability needs one target
  or a card selected to pay for it, supply that object in `target` (CR 5.2.2). -/
  | activateAbility (source : ObjId) (index : Nat) (target : Option ObjId := none)
      (secondTarget : Option ObjId := none)
  /-- Defend Step: declare card or equipment `id` as a defending card on the active link (CR 7.3). -/
  | defendCard (id : ObjId)
  /-- Defend Step: finish declaring defending cards for the active link (CR 7.3). -/
  | defendDone
  /-- Select modal branch index `idx` during play declaration or `Effect.chooseOne` (CR 5.1.2a). -/
  | pickMode (idx : Nat)
  /-- Declare a hero target for the card currently being played (CR 5.1.4a). -/
  | pickHeroTarget (hero : PlayerId)
  /-- Declare the weapon targeted by a card being played (CR 5.1.4a). -/
  | pickWeaponTarget (id : ObjId)
  /-- Pitch card `id` from hand to pay an asset cost during `choosePitch` (CR 1.14.3, 5.1.6). -/
  | pitchCard (id : ObjId)
  /-- Cancel and roll back an in-progress card play to the pre-play snapshot (CR 5.1.1). -/
  | cancelPlay
  /-- Answer an optional `"you may ..."` effect choice (I18). -/
  | pickMay (choice : Bool)
  /-- Declare X for a variable additional cost, or decline it (CR 5.1.3). -/
  | pickVariableResources (amount : Option Nat)
  /-- Chance provides a 6-sided die result (`1 ≤ roll ≤ 6`). -/
  | die6Roll (roll : Nat)
  /-- Pick a card from hand to place into the deck (e.g. Sink Below). -/
  | handToDeckPick (id : ObjId)
  /-- Select a card from hand for a discard effect (CR 8.5.5). -/
  | pickDiscardCard (id : ObjId)
  /-- Add a card to the selection or confirm it with `none` (CR 1.8.6, 8.5.20b). -/
  | pickShuffleCard (choice : Option ObjId)
  /-- Choose a card from hand to pay an additional cost (CR 5.1.9). -/
  | pickHandCostCard (id : ObjId)
  /-- Choose a graveyard card to banish as a play cost, or decline the optional cost (CR 5.1.3). -/
  | pickGraveyardCost (choice : Option ObjId)
  /-- Opt choice: place a viewed card on top or bottom. Omit the ID for the first candidate (CR 8.5.22). -/
  | optPick (putOnTop : Bool) (card : Option ObjId := none)
  /-- End Phase: put card `id` from hand face-down into an empty arsenal (CR 4.4.3b). -/
  | arsenalPut (id : ObjId)
  /-- End Phase: decline putting a card into the arsenal (CR 4.4.3b). -/
  | arsenalSkip
  /-- End Phase: put card `id` from pitch zone onto the bottom of owner's deck (CR 4.4.3c). -/
  | pitchReturnPick (id : ObjId)
  /-- Concede the game (CR 4.5). -/
  | concede
  /-- Tournament clock signals end-of-round time limit (current turn + 1 additional turn) (TRP 4). -/
  | timeExpired
  /-- Swiss round player offers an Intentional Draw to the opponent (TRP 4). -/
  | offerDraw
  /-- Swiss round opponent accepts a pending Intentional Draw offer (TRP 4). -/
  | acceptDraw
  /-- Swiss round opponent declines a pending Intentional Draw offer (TRP 4). -/
  | declineDraw
  /-- Tournament judge declares a draw due to an unbreakable mandatory loop (TRP 4). -/
  | judgeLoopDraw
  /-- Turn-player picks which seated player starts stacking simultaneous triggers (CR 6.6.6b). -/
  | pickTriggerStart (start : PlayerId)
  /-- Player picks a pending trigger to stack and declares its required target (CR 6.6.6). -/
  | pickTrigger (trigId : Nat) (hero : Option PlayerId := none) (equipment : Option ObjId := none)
  /-- Add a graveyard target to the selected triggered layer (CR 6.6.6a). -/
  | pickTriggerGraveyardCard (id : ObjId)
  /-- Affected player chooses an optional/competing replacement effect ID or declines (CR 6.5.1). -/
  | pickReplacement (choice : Option Nat)
deriving DecidableEq, Repr

/-- A single decision input paired with its `Actor`. -/
structure Action where
  /-- Who performs the action. -/
  actor : Actor
  /-- What action is performed. -/
  kind : ActionKind
deriving DecidableEq, Repr

/-- Additional cost paid by choosing a card in hand (CR 5.1.9). -/
inductive HandCardCost where
  /-- Place the chosen card on the bottom of the deck. -/
  | bottomDeck
  /-- Reveal the chosen card and keep it in hand. -/
  | reveal (filter : CardFilter)
deriving DecidableEq, Repr

/-- Two decisions when looking at the deck, optionally loading one card, and ordering the rest. -/
inductive DeckBottomSelection where
  /-- The chooser may see all these cards but may only select an eligible card. -/
  | lookedAt (cards : List ObjId)
  /-- The chooser must select every remaining viewed card in the final bottom-deck order. -/
  | order (count : Nat)
deriving DecidableEq, Repr

/-- Completion instructions for moving selected cards, including deck searches (CR 8.5.19). -/
structure DeckSearchChoice where
  /-- Zone that receives the chosen cards before the deck is shuffled. -/
  destination : Zone
  /-- Whether to reveal the chosen cards before moving them. -/
  reveal : Bool
  /-- Whether the player may finish without selecting a card. -/
  mayFail : Bool
  /-- Whether this particular search instruction ends with a shuffle. -/
  shuffleAfter : Bool := true
  /-- Permission granted to the selected card if it is moved to banished. -/
  playableDuration : Option Duration := none
  /-- Whether that permission allows the selected card to be played as though it were an instant. -/
  playAsInstant : Bool := false
  /-- Reduction in resource cost for the selected card played using this permission. -/
  resourceDiscount : Nat := 0
  /-- Cards viewed privately by the chooser independently of the selection's legal candidates. -/
  viewedCards : Option (List ObjId) := none
  /-- Whether this selection grants the chooser temporary visibility of their deck. -/
  searchesDeck : Bool := true
  /-- An extra counter for a single selected card entering the arena. -/
  entryCounter : Option CounterKind := none
  /-- Source and power bonus for the card selected into arsenal until the end of this turn. -/
  arsenalPowerBonus : Option (ObjId × Int) := none
  /-- Keep the selected deck card for placement on top after the shuffle. -/
  putOnTopAfterShuffle : Bool := false
  /-- Look at the deck or order the viewed cards that remain there. -/
  bottomSelection : Option DeckBottomSelection := none
deriving DecidableEq, Repr

/-- These selections reorder cards in their present deck. -/
def DeckSearchChoice.keepsSelectedInZone (choice : DeckSearchChoice) : Bool :=
  choice.putOnTopAfterShuffle || match choice.bottomSelection with
    | some (.order _) => true
    | _ => false

/-- Order choices require every card; searches may fail if their completion instructions permit it. -/
def shuffleSelectionCanConfirm (selected : List ObjId) (search : Option DeckSearchChoice) : Bool :=
  search.all fun choice =>
    match choice.bottomSelection with
    | some (.order count) => selected.length == count
    | _ => choice.mayFail || !selected.isEmpty

/-- The continuation of the prevention stage of an arcane damage event (CR 6.5.1, 8.3.8). -/
inductive ArcaneDamageStep where
  /-- Determine which prevention effects can still apply. -/
  | offer
  /-- Read the affected player's answer to the prevention prompt. -/
  | readChoice
  /-- Pay the selected effect's cost before applying it. -/
  | pay (effect : ReplacementEffect)
deriving DecidableEq, Repr

/-- Optional additional payment offered when declaring a card (CR 5.1.3, 8.3.9). -/
inductive OptionalPlayCost where
  /-- Add this number of resources to the announced asset cost. -/
  | resources (n : Nat)
  /-- Banish the top card of the deck after paying the assets. -/
  | boost
deriving DecidableEq, Repr

/-- Check an X declaration. An optional cost can be declined without choosing a value. -/
def validVariableResources (limit : Nat) (optional : Bool) : Option Nat → Bool
  | none => optional
  | some value => decide (value ≤ limit)

/-- Resume an effect after a card is chosen and discarded. -/
structure DiscardContinuation where
  /-- Player controlling the effect being resumed. -/
  controller : PlayerId
  /-- Source object of the suspended effect. -/
  source : ObjId
  /-- Whether the source was played from arsenal. -/
  fromArsenal : Bool
  /-- Numeric bindings available to the resumed effect. -/
  env : List (VarId × Int)
  /-- Predicate that determines which branch to run after the discard. -/
  classify : CardFilter
  /-- Effect to run when the discarded card matches the predicate. -/
  ifMatches : Effect
  /-- Effect to run when the discarded card does not match. -/
  otherwise : Effect
deriving DecidableEq, Repr

/-- Continuation stack frame: either a decision frame waiting for `step`, or a work frame
advanced automatically by `microStep` (design.md §6.2). -/
inductive Frame where
  /-- Chance decision: pick which player chooses who goes first (CR 4.1.3). -/
  | chanceFirstPlayer
  /-- Player decision: `chooser` selects who takes the first turn (CR 4.1.3). -/
  | chooseFirstPlayer (chooser : PlayerId)
  /-- Player decision: `p` incrementally configures armor, weapons, and deck from inventory
  (CR 4.1.4). -/
  | chooseLoadout (p : PlayerId)
  /-- Work frame: simultaneously reveal all non-Cloaked equipped cards in the arena (CR 4.1.4). -/
  | revealLoadouts
  /-- Chance decision: shuffle the contents of zone `z` (CR 4.1.5). -/
  | chanceShuffle (z : Zone)
  /-- Work frame: schedule opening Intellect draws for all players in turn order (CR 4.1.6). -/
  | openingDraws
  /-- Work frame: player `p` draws `n` cards one by one (CR 4.1.6, 4.4.3f). -/
  | draw (p : PlayerId) (n : Nat)
  /-- Work frame: begin the next turn for the next player in `turnOrder` (CR 4.0). -/
  | beginTurn
  /-- Work frame: Start Phase processing for turn-player `tp` (CR 4.2). -/
  | startPhaseWork (tp : PlayerId)
  /-- Work frame: Action Phase start, granting `tp` 1 AP and priority (CR 4.3.2). -/
  | actionPhaseStart (tp : PlayerId)
  /-- Player decision: `p` holds priority after `passCount` consecutive passes (CR 1.11, 4.3.3). -/
  | priority (p : PlayerId) (passCount : Nat)
  /-- Player decision: declare mode index for modal card `layerId` during play (CR 5.1.2a). -/
  | chooseMode (p : PlayerId) (layerId : ObjId) (fromArsenal : Bool) (modeCount : Nat)
      (cost : AssetCost)
  /-- Player decision: declare a hero target for a card before paying for it (CR 5.1.4a). -/
  | choosePlayHero (p : PlayerId) (layerId : ObjId) (fromArsenal : Bool) (modeIdx : Option Nat)
      (cost : AssetCost)
  /-- Player decision: choose the card-layer's weapon target before paying (CR 5.1.4a). -/
  | choosePlayWeapon (p : PlayerId) (layerId : ObjId) (fromArsenal : Bool) (modeIdx : Option Nat)
      (cost : AssetCost) (candidates : List ObjId)
  /-- Work frame: calculate/pay asset costs for `layerId`, prompting pitch or rolling back (CR 5.1.5, 5.1.6). -/
  | playPayCost (p : PlayerId) (layerId : ObjId) (fromArsenal : Bool) (modeIdx : Option Nat)
      (cost : AssetCost)
  /-- Work frame: pay the random-discard cost from the ordered hand and complete play
  (CR 5.1.9, 5.1.10). -/
  | payRandomDiscard (p : PlayerId) (layerId : ObjId) (fromArsenal : Bool)
      (modeIdx : Option Nat) (count : Nat)
  /-- Player decision: pitch a card from hand while paying `cost`, or cancel play (CR 1.14.3, 5.1.6). -/
  | choosePitch (p : PlayerId) (layerId : ObjId) (fromArsenal : Bool) (modeIdx : Option Nat)
      (cost : AssetCost)
  /-- Player decision: accept an optional additional cost or waive it (CR 5.1.5). -/
  | chooseOptionalPlayCost (p : PlayerId) (layerId : ObjId) (fromArsenal : Bool)
      (modeIdx : Option Nat) (cost : AssetCost) (extra : OptionalPlayCost)
  /-- Player decision: declare X for a variable resource cost (CR 5.1.3a). -/
  | chooseVariableResources (p : PlayerId) (layerId : ObjId) (fromArsenal : Bool)
      (modeIdx : Option Nat) (cost : AssetCost) (limit : Nat) (optional : Bool := true)
  /-- Player decision: declare an optional banish cost before paying assets (CR 5.1.3, 5.1.6). -/
  | chooseGraveyardCost (p : PlayerId) (layerId : ObjId) (fromArsenal : Bool)
      (modeIdx : Option Nat) (cost : AssetCost) (candidates : List ObjId)
  /-- Player decision: pay the additional cost by choosing a card from hand (CR 5.1.9). -/
  | chooseHandCardCost (p : PlayerId) (layerId : ObjId) (fromArsenal : Bool)
      (modeIdx : Option Nat) (cost : HandCardCost)
  /-- Work frame: begin resolving the top layer of the stack LIFO (CR 5.3). -/
  | resolveStack
  /-- Work frame: finish resolving `layerId` (Go Again +1 AP, move to graveyard/arena, priority to active) (CR 5.3.4, 5.3.5). -/
  | finishResolve (layerId : ObjId)
  /-- Work frame: advance the Combat Chain to `step` for attack object `atkId` (CR 7.1-7.7). -/
  | combatStep (step : CombatStep) (atkId : ObjId)
  /-- Player decision: defending player `defender` incrementally picks defending cards from hand
  and/or equipment during Defend Step (CR 7.3). -/
  | defendPick (defender : PlayerId)
  /-- Work frame: run Game State Process to fixed point before granting priority (CR 1.10.2). -/
  | gameStateProcess
  /-- Work frame: 1-step effect IR interpreter continuation (CR 1.7, 6.0). -/
  | run (ctrl : PlayerId) (src : ObjId) (fromArsenal : Bool) (env : List (VarId × Int))
      (todo : List Effect)
  /-- Player decision: answer `"you may body; if you do, ifDone"` (I18). -/
  | chooseMay (ctrl : PlayerId) (src : ObjId) (fromArsenal : Bool) (env : List (VarId × Int))
      (body ifDone : Effect)
  /-- Player decision: choose 1 branch from `Effect.chooseOne` (CR 1.7). -/
  | chooseModal (ctrl : PlayerId) (src : ObjId) (fromArsenal : Bool) (env : List (VarId × Int))
      (modes : List Effect)
  /-- Chance decision: 6-sided die roll feeding `bindVar`, `branches`, and `cont`. -/
  | chanceDie6 (ctrl : PlayerId) (src : ObjId) (fromArsenal : Bool) (env : List (VarId × Int))
      (bindVar : VarId) (branches : DieBranchList) (cont : Effect)
  /-- Player decision: pick a card from hand to place into the deck at `pos`. -/
  | chooseHandToDeck (p : PlayerId) (pos : DeckPos)
  /-- Player selects cards before discarding them together (CR 8.5.5). -/
  | chooseDiscard (p : PlayerId) (remaining : Nat) (candidates selected : List ObjId)
      (resume : Option DiscardContinuation := none)
  /-- Player selects cards for a single shuffle effect. Cards move when the selection is confirmed. -/
  | chooseShuffleCards (p : PlayerId) (remaining : Nat) (candidates selected : List ObjId)
      (drawSame : Bool) (search : Option DeckSearchChoice := none)
  /-- Work frame: expose up to `n` cards for `Opt` for player `p` (CR 8.5.22). -/
  | optStep (p : PlayerId) (n : Nat)
  /-- Player decision: place any remaining viewed card. The first `topCount` deck cards
  have already been placed in their chosen top order (CR 8.5.22). -/
  | chooseOpt (p : PlayerId) (cardId : ObjId) (others : List ObjId := [])
      (topCount : Nat := 0) (bottomCount : Nat := 0)
  /-- Work frame: End Phase start, scheduling Arsenal, Pitch return, and cleanup (CR 4.4). -/
  | endPhaseStart (tp : PlayerId)
  /-- Work frame: check arsenal eligibility after end-phase triggers have resolved (CR 4.4.3b). -/
  | endPhaseArsenal (tp : PlayerId)
  /-- Player decision: `tp` may put 1 card from hand face-down into an empty arsenal (CR 4.4.3b). -/
  | chooseArsenal (tp : PlayerId)
  /-- Work frame: check if player `p` has cards in pitch zone to return to deck bottom (CR 4.4.3c). -/
  | returnPitch (p : PlayerId)
  /-- Player decision: `p` picks one card from pitch zone to place on deck bottom (CR 4.4.3c). -/
  | choosePitchOrder (p : PlayerId)
  /-- Work frame: untap permanents, clear all asset pools, and draw up to Intellect (CR 4.4.3d, 4.4.3e, 4.4.3f). -/
  | endTurnCleanup (tp : PlayerId)
  /-- Work frame: expire turn effects after all end-phase draws (CR 4.4.4). -/
  | endTurnFinish
  /-- Work frame: flush pending triggered abilities onto the stack via turn-player start choice (CR 6.6.6b). -/
  | flushTriggers
  /-- Player decision: turn-player picks which player begins stacking simultaneous triggers (CR 6.6.6b). -/
  | chooseTriggerStart (turnPlayer : PlayerId)
  /-- Player decision: player `p` picks one of their pending triggers to stack, then passes clockwise
  to `remainingPlayers` (CR 6.6.6b). -/
  | chooseTriggerOrder (p : PlayerId) (remainingPlayers : List PlayerId)
  /-- Player decision: declare exactly the required graveyard targets for the chosen trigger. -/
  | chooseTriggerGraveyard (p : PlayerId) (remainingPlayers : List PlayerId) (trigger : PendingTrigger)
      (remaining : Nat) (candidates selected : List ObjId)
  /-- Player decision: affected player selects a replacement effect ID (or `none` if optional)
  at `stage` (CR 6.5.1). -/
  | chooseReplacement (affected : PlayerId) (stage : ReplacementStage) (candidates : List Nat)
      (canDecline : Bool)
  /-- Work: offer damage prevention, apply a choice, or settle its payment. -/
  | arcaneDamage (target : PlayerId) (effects : List ReplacementEffect) (damage : ReplacementState)
      (step : ArcaneDamageStep) (combatAttack : Option ObjId := none)
  /-- Decision: pitch a card to pay for the chosen prevention effect (CR 1.14.3). -/
  | choosePreventionPitch (p : PlayerId)
deriving DecidableEq, Repr

/-- Whether a frame is an automatic work frame processed by `microStep`. -/
def Frame.isWork : Frame → Bool
  | .revealLoadouts => true
  | .openingDraws => true
  | .draw _ _ => true
  | .beginTurn => true
  | .startPhaseWork _ => true
  | .actionPhaseStart _ => true
  | .playPayCost _ _ _ _ _ => true
  | .payRandomDiscard _ _ _ _ _ => true
  | .resolveStack => true
  | .finishResolve _ => true
  | .combatStep _ _ => true
  | .gameStateProcess => true
  | .run _ _ _ _ _ => true
  | .optStep _ _ => true
  | .endPhaseStart _ => true
  | .endPhaseArsenal _ => true
  | .returnPitch _ => true
  | .endTurnCleanup _ => true
  | .endTurnFinish => true
  | .flushTriggers => true
  | .arcaneDamage _ _ _ _ _ => true
  | _ => false

end Fab

end
