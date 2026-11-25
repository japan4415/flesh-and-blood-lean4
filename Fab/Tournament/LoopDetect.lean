module

public import Fab.Invariant.Tournament

/-!
# Forced Loop Detector & Soundness (TRP 4)

Implements canonical state projection (`canonicalBoard`) stripping monotonic `ObjId` / `nextId` /
`nextTimestamp` / `timestamp` counters so that forced loops cycling objects across zone boundaries
(which mint fresh `ObjId`s on every iteration) (CR 3.0.9) are detected soundly (`detectLoop`),
and connects detected loops to `Actor.judge` loop draw legality (TRP 4).
-/

@[expose] public section

namespace Fab

/-- Canonical representation of an `ObjectKind` stripping ephemeral `ObjId`s while preserving
logical card/token identity (TRP 4). -/
inductive CanonicalKind where
  /-- Physical card identified by its `CardId`. -/
  | card (cardId : CardId)
  /-- Token identified by its `CardId`. -/
  | token (cardId : CardId)
  /-- Ability layer identified by ability index and trigger flag. -/
  | layer (abilityIdx : Nat) (isTrigger : Bool)
  /-- Attack-proxy identified by source LKI card ID. -/
  | attackProxy (cardId : Option CardId)
deriving DecidableEq, Repr

/-- Project an `ObjectKind` to its `CanonicalKind`. -/
def canonicalKind : ObjectKind → CanonicalKind
  | .card _ cid => .card cid
  | .token cid => .token cid
  | .layer _ _ idx isTrig => .layer idx isTrig
  | .attackProxy _ lki => .attackProxy (lki.bind (·.cardId))

/-- Canonical representation of a single `Object` stripping monotonic `timestamp` (TRP 4). -/
structure CanonicalObj where
  /-- Logical object kind. -/
  kind : CanonicalKind
  /-- Owner seat. -/
  owner : PlayerId
  /-- Controller seat. -/
  controller : PlayerId
  /-- Tap state. -/
  tapped : Bool
  /-- Face-down state. -/
  faceDown : Bool
  /-- Active double-faced state. -/
  faceState : FaceState
  /-- `-1{d}` counters. -/
  minusDefenseCounters : Nat
  /-- `+1{p}` counters. -/
  plusPowerCounters : Nat
  /-- Auxiliary counters. -/
  extraCounters : List (String × Nat)
  /-- Living permanent life total. -/
  life : Option Int
deriving DecidableEq, Repr

/-- Project an `Object` to its `CanonicalObj`. -/
def canonicalObj (o : Object) : CanonicalObj :=
  { kind := canonicalKind o.kind
    owner := o.owner
    controller := o.controller
    tapped := o.tapped
    faceDown := o.faceDown
    faceState := o.faceState
    minusDefenseCounters := o.minusDefenseCounters
    plusPowerCounters := o.plusPowerCounters
    extraCounters := o.extraCounters
    life := o.life }

/-- Canonical board projection stripping monotonic `nextId`, `nextTimestamp`, and per-object
`ObjId`/`timestamp` values so repeated board positions in a forced loop match identically (TRP 4). -/
structure CanonicalBoard where
  /-- Canonical contents of every valid zone. -/
  zones : List (Zone × List (Option CanonicalObj))
  /-- Per-player asset pools. -/
  pools : List (PlayerId × AssetPool)
  /-- Per-player hero life totals. -/
  heroLife : List (PlayerId × Int)
  /-- Current phase. -/
  phase : Phase
  /-- Active turn-player. -/
  active : Option PlayerId
  /-- Turn order. -/
  turnOrder : List PlayerId
  /-- Combat chain step and link count (if open). -/
  combatStep : Option (CombatStep × Nat)
  /-- Number of pending continuation frames. -/
  pendingCount : Nat
  /-- Final game result (if ended). -/
  result : Option GameResult
deriving DecidableEq, Repr

/-- Compute the `CanonicalBoard` projection of `GameState` `s` (TRP 4). -/
def canonicalBoard (s : GameState) : CanonicalBoard :=
  { zones := (allZones s.playerCount).map fun z =>
      (z, (s.zone z).map fun id => (s.obj? id).map canonicalObj)
    pools := (allPlayers s.playerCount).map fun p => (p, s.poolOf p)
    heroLife := (allPlayers s.playerCount).map fun p => (p, s.lifeOf p)
    phase := s.phase
    active := s.active
    turnOrder := s.turnOrder
    combatStep := s.combat.map fun cc => (cc.step, cc.links.length)
    pendingCount := s.pending.length
    result := s.result }

/-- Detect whether `cur` repeats any earlier canonical board state in `history` (**I19**) (TRP 4). -/
def detectLoop (history : List GameState) (cur : GameState) : Bool :=
  history.any fun prev => canonicalBoard prev == canonicalBoard cur

/-- Find the index in `history` of the first state matching `cur`'s canonical board (TRP 4). -/
def findLoopStart? (history : List GameState) (cur : GameState) : Option Nat :=
  history.findIdx? fun prev => canonicalBoard prev == canonicalBoard cur

/-- **I19 (Forced Loop Detector Soundness & Completeness)** (TRP 4):
`detectLoop history cur = true` holds iff some prior state `prev ∈ history` has the exact same
canonical board projection as `cur`. -/
theorem detectLoop_iff (history : List GameState) (cur : GameState) :
    detectLoop history cur = true ↔ ∃ prev ∈ history, canonicalBoard prev = canonicalBoard cur := by
  unfold detectLoop
  simp [List.any_eq_true]

/-- **I19 (Soundness)** (TRP 4): whenever `detectLoop` signals a loop, there exists an exact
canonical board repetition in `history`. -/
theorem detectLoop_sound {history : List GameState} {cur : GameState}
    (h : detectLoop history cur = true) :
    ∃ prev ∈ history, canonicalBoard prev = canonicalBoard cur :=
  (detectLoop_iff history cur).mp h

/-- **I19 (Counter-Invariance)**: advancing monotonic `nextId` and `nextTimestamp` counters
(as occurs when objects cycle across zone boundaries) (CR 3.0.9) does NOT evade loop detection. -/
theorem canonicalBoard_ignores_counters (s : GameState) (nid nts : Nat) :
    canonicalBoard { s with nextId := nid, nextTimestamp := nts } = canonicalBoard s := rfl

/-- **I19 (Tournament Judge Integration)** (TRP 4): whenever a forced loop is detected on an
ongoing tournament game state `cur`, `Actor.judge` may legally end the game in `.draw .loop`. -/
theorem detectLoop_enables_judge_draw {fuel : Nat} {history : List GameState} {cur : GameState}
    (_hloop : detectLoop history cur = true)
    (hres : cur.result = none)
    (htourn : cur.config.ruleSet.isTournament = true) :
    step fuel cur ⟨.judge, .judgeLoopDraw⟩ = .ok (applyJudgeLoopDraw cur, []) ∧
    (applyJudgeLoopDraw cur).result = some (.draw .loop) :=
  judgeLoopDraw_ends_in_loop_draw hres htourn

end Fab

end
