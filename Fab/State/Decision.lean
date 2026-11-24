module

public import Fab.State.Zone

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
  /-- End Phase: put card `id` from hand face-down into an empty arsenal (CR 4.4.3b). -/
  | arsenalPut (id : ObjId)
  /-- End Phase: decline putting a card into the arsenal (CR 4.4.3b). -/
  | arsenalSkip
  /-- End Phase: put card `id` from pitch zone onto the bottom of owner's deck (CR 4.4.3c). -/
  | pitchReturnPick (id : ObjId)
  /-- Concede the game (CR 4.5). -/
  | concede
deriving DecidableEq, Repr

/-- A single decision input paired with its `Actor`. -/
structure Action where
  /-- Who performs the action. -/
  actor : Actor
  /-- What action is performed. -/
  kind : ActionKind
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
  /-- Work frame: End Phase start, scheduling Arsenal, Pitch return, and cleanup (CR 4.4). -/
  | endPhaseStart (tp : PlayerId)
  /-- Player decision: `tp` may put 1 card from hand face-down into an empty arsenal (CR 4.4.3b). -/
  | chooseArsenal (tp : PlayerId)
  /-- Work frame: check if player `p` has cards in pitch zone to return to deck bottom (CR 4.4.3c). -/
  | returnPitch (p : PlayerId)
  /-- Player decision: `p` picks one card from pitch zone to place on deck bottom (CR 4.4.3c). -/
  | choosePitchOrder (p : PlayerId)
  /-- Work frame: untap permanents, clear all asset pools, and draw up to Intellect (CR 4.4.3d, 4.4.3e, 4.4.3f). -/
  | endTurnCleanup (tp : PlayerId)
deriving DecidableEq, Repr

/-- Whether a frame is an automatic work frame processed by `microStep`. -/
def Frame.isWork : Frame → Bool
  | .revealLoadouts => true
  | .openingDraws => true
  | .draw _ _ => true
  | .beginTurn => true
  | .startPhaseWork _ => true
  | .actionPhaseStart _ => true
  | .endPhaseStart _ => true
  | .returnPitch _ => true
  | .endTurnCleanup _ => true
  | _ => false

end Fab

end
