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

/-- Read counter count of kind `k` on object `o`. -/
def Object.counterCount (o : Object) : CounterKind → Nat :=
  readCounterCount o.minusDefenseCounters o.plusPowerCounters o.extraCounters

/-- Update counter `k` on object `o` by adding `delta`. -/
def Object.addCounterVal (o : Object) (k : CounterKind) (delta : Nat) : Object :=
  match k with
  | .minusOneDefense => { o with minusDefenseCounters := o.minusDefenseCounters + delta }
  | .plusOnePower => { o with plusPowerCounters := o.plusPowerCounters + delta }
  | .energy =>
    let cur := o.counterCount .energy
    let rest := o.extraCounters.filter (·.1 != "energy")
    { o with extraCounters := ("energy", cur + delta) :: rest }
  | .steam =>
    let cur := o.counterCount .steam
    let rest := o.extraCounters.filter (·.1 != "steam")
    { o with extraCounters := ("steam", cur + delta) :: rest }
  | .aim =>
    let cur := o.counterCount .aim
    let rest := o.extraCounters.filter (·.1 != "aim")
    { o with extraCounters := ("aim", cur + delta) :: rest }
  | .named lbl =>
    let cur := o.counterCount (.named lbl)
    let rest := o.extraCounters.filter (·.1 != lbl)
    { o with extraCounters := (lbl, cur + delta) :: rest }

/-- Remove all counters of kind `k` from object `o`. -/
def Object.clearCounterVal (o : Object) : CounterKind → Object
  | .minusOneDefense => { o with minusDefenseCounters := 0 }
  | .plusOnePower => { o with plusPowerCounters := 0 }
  | .energy => { o with extraCounters := o.extraCounters.filter (·.1 != "energy") }
  | .steam => { o with extraCounters := o.extraCounters.filter (·.1 != "steam") }
  | .aim => { o with extraCounters := o.extraCounters.filter (·.1 != "aim") }
  | .named lbl => { o with extraCounters := o.extraCounters.filter (·.1 != lbl) }

/-- Remove up to `n` counters of the specified kind. -/
def Object.removeCounterVal (o : Object) (k : CounterKind) (n : Nat) : Object :=
  let remaining := o.counterCount k - n
  let cleared := o.clearCounterVal k
  if remaining = 0 then cleared else cleared.addCounterVal k remaining

/-- `Object.addCounterVal` preserves `kind`. -/
theorem Object.addCounterVal_kind (o : Object) (k : CounterKind) (d : Nat) :
    (o.addCounterVal k d).kind = o.kind := by
  cases k <;> rfl

/-- `Object.addCounterVal` preserves `owner`. -/
theorem Object.addCounterVal_owner (o : Object) (k : CounterKind) (d : Nat) :
    (o.addCounterVal k d).owner = o.owner := by
  cases k <;> rfl

/-- `Object.clearCounterVal` preserves `kind`. -/
theorem Object.clearCounterVal_kind (o : Object) (k : CounterKind) :
    (o.clearCounterVal k).kind = o.kind := by
  cases k <;> rfl

/-- Removing counters preserves the physical/card identity of the object. -/
theorem Object.removeCounterVal_kind (o : Object) (k : CounterKind) (n : Nat) :
    (o.removeCounterVal k n).kind = o.kind := by
  unfold Object.removeCounterVal
  dsimp only
  split <;> simp only [Object.clearCounterVal_kind, Object.addCounterVal_kind]

/-- `Object.clearCounterVal` preserves `owner`. -/
theorem Object.clearCounterVal_owner (o : Object) (k : CounterKind) :
    (o.clearCounterVal k).owner = o.owner := by
  cases k <;> rfl

/-- Removing counters preserves ownership. -/
theorem Object.removeCounterVal_owner (o : Object) (k : CounterKind) (n : Nat) :
    (o.removeCounterVal k n).owner = o.owner := by
  unfold Object.removeCounterVal
  dsimp only
  split <;> simp only [Object.clearCounterVal_owner, Object.addCounterVal_owner]

/-- Add the counters a source receives when entering the arena (CR 3.0.5, 6.4). -/
def Object.withEntryCounters : Object → List (CounterKind × Nat) → Object
  | obj, [] => obj
  | obj, (kind, count) :: rest => (obj.addCounterVal kind count).withEntryCounters rest

/-- Entry counters preserve the physical or layered object kind. -/
@[simp] theorem Object.withEntryCounters_kind (o : Object) (counts : List (CounterKind × Nat)) :
    (o.withEntryCounters counts).kind = o.kind := by
  induction counts generalizing o with
  | nil => rfl
  | cons counter rest ih =>
    rcases counter with ⟨kind, count⟩
    simp only [Object.withEntryCounters, ih, Object.addCounterVal_kind]

/-- Entry counters preserve the object's owner. -/
@[simp] theorem Object.withEntryCounters_owner (o : Object) (counts : List (CounterKind × Nat)) :
    (o.withEntryCounters counts).owner = o.owner := by
  induction counts generalizing o with
  | nil => rfl
  | cons counter rest ih =>
    rcases counter with ⟨kind, count⟩
    simp only [Object.withEntryCounters, ih, Object.addCounterVal_owner]

end Fab

end
