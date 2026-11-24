module

public import Fab.State.Lki

/-!
# Game objects

Representation of Flesh and Blood game objects: physical cards, tokens, stack layers, and
attack-proxies (CR 1.3-1.4, 1.6). Supports double-faced cards (Transcend / Transform), face-down
states (Cloaked / Arsenal / Banished), tapping (CR 8.2), and counters (`-1{d}`, `+1{p}`).
-/

@[expose] public section

namespace Fab

/-- Which face of a double-faced card is currently active (Transcend / Transform / Demi-Hero). -/
inductive FaceState where
  /-- Standard front face. -/
  | front
  /-- Back face of a double-faced card. -/
  | back
deriving DecidableEq, Repr, Hashable

/-- Kind of game object (CR 1.3, 1.4.3, 1.6). -/
inductive ObjectKind where
  /-- Physical card from a player's card-pool, carrying a `PhysId` and `CardId`. -/
  | card (phys : PhysId) (cardId : CardId)
  /-- Token object without a `PhysId` (CR 1.3). -/
  | token (cardId : CardId)
  /-- Activated or triggered ability layer on the stack (CR 1.6). -/
  | layer (sourceObj : ObjId) (sourceLki : Option LkiSnapshot) (abilityIdx : Nat)
      (isTrigger : Bool)
  /-- Attack-proxy representing a weapon or permanent attack on the stack / combat chain
  (CR 1.4.3). -/
  | attackProxy (sourceObj : ObjId) (sourceLki : Option LkiSnapshot)
deriving DecidableEq, Repr

/-- Extract the `PhysId` of an object kind (`some` only for physical cards). -/
def ObjectKind.phys? : ObjectKind → Option PhysId
  | .card phys _ => some phys
  | .token _ => none
  | .layer _ _ _ _ => none
  | .attackProxy _ _ => none

/-- Extract the `CardId` of a card or token object kind. -/
def ObjectKind.cardId? : ObjectKind → Option CardId
  | .card _ cid => some cid
  | .token cid => some cid
  | .layer _ _ _ _ => none
  | .attackProxy _ _ => none

/-- A game object stored in `GameState.objects` (CR 1.3). -/
structure Object where
  /-- What kind of object this is (card, token, layer, or attack-proxy). -/
  kind : ObjectKind
  /-- Player who brought this card into the game or created this token (CR 1.3.1). -/
  owner : PlayerId
  /-- Base controller, overridable by Stage 2 continuous effects (CR 6.3.2). -/
  controller : PlayerId
  /-- Whether this permanent is tapped (CR 8.2). -/
  tapped : Bool := false
  /-- Whether this object is currently face-down (Arsenal, Banished, or Cloaked equipment). -/
  faceDown : Bool := false
  /-- Active face for double-faced cards. -/
  faceState : FaceState := .front
  /-- Number of `-1{d}` counters from Battleworn, Temper, or Guardwell (CR 8.3). -/
  minusDefenseCounters : Nat := 0
  /-- Number of `+1{p}` counters. -/
  plusPowerCounters : Nat := 0
  /-- Named auxiliary counters (for example, steam, aim, flow, verse). -/
  extraCounters : List (String × Nat) := []
  /-- Current life total for living objects such as Heroes and Allies (CR 2.5). -/
  life : Option Int := none
  /-- Timestamp when this object instance was created (CR 6.3.3). -/
  timestamp : Timestamp
deriving DecidableEq, Repr

/-- Reset transient state when an object crosses the Arena boundary or moves between Non-Arena
zones, producing a fresh object instance (CR 3.0.9). -/
def Object.resetOnZoneChange (o : Object) (ts : Timestamp) (faceDown : Bool := false) : Object :=
  { o with
    controller := o.owner
    tapped := false
    faceDown := faceDown
    minusDefenseCounters := 0
    plusPowerCounters := 0
    extraCounters := []
    timestamp := ts }

/-- Resetting an object on zone change preserves its `ObjectKind` (and thus `PhysId`). -/
theorem Object.resetOnZoneChange_kind (o : Object) (ts : Timestamp) (fd : Bool) :
    (o.resetOnZoneChange ts fd).kind = o.kind := rfl

/-- Resetting an object on zone change preserves its `owner`. -/
theorem Object.resetOnZoneChange_owner (o : Object) (ts : Timestamp) (fd : Bool) :
    (o.resetOnZoneChange ts fd).owner = o.owner := rfl

end Fab

end
