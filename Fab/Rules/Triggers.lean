module

public import Fab.State.Lki
public import Fab.Card.IR.Effect
public import Fab.State.Phase

/-!
# Triggered Abilities, Delayed Triggers, and Simultaneous Trigger Stacking (CR 6.6)

Implements Flesh and Blood's unique simultaneous trigger ordering rule (CR 1.10.2d, 6.6.6b):
Unlike APNAP in other TCGs, when simultaneous triggered layers are added to the stack:
1. The **turn-player chooses any seated player `start`** to begin stacking triggers.
2. Proceeding **clockwise from `start`** around `turnOrder`, each player places all of their
   controlled pending triggers onto the stack in their chosen order.

In 1v1, this lets the turn-player completely control whether their own triggers or the opponent's
triggers sit on top of the stack (resolving first LIFO).

Proves **I19** (`rotateTurnOrderFrom_head`, `rotateTurnOrderFrom_perm`,
`rotateTurnOrderFrom_1v1`, `stackTriggersClockwise_1v1_lifo`).
-/

@[expose] public section

namespace Fab

/-- A pending triggered ability awaiting placement onto `Zone.stack` (CR 1.10.2d, 6.6). -/
structure PendingTrigger where
  /-- Unique identifier for this pending trigger instance. -/
  id : Nat
  /-- Source object that triggered (CR 6.6.5a). -/
  source : ObjId
  /-- Last Known Information of the source at trigger time (CR 1.2.3, 6.6). -/
  sourceLki : LkiSnapshot
  /-- Player who controls this triggered-layer (CR 6.6.5). -/
  controller : PlayerId
  /-- Ability index on the source card. -/
  abilityIdx : Nat := 0
  /-- Whether the card that created an on-play trigger was played from arsenal. -/
  fromArsenal : Bool := false
  /-- Effect body executed when this triggered-layer resolves. -/
  effect : Effect := .nop
  /-- Controller of the equipment this trigger must target, when required. -/
  equipmentTargetPlayer : Option PlayerId := none
  /-- Whether the trigger must choose one opposing hero. -/
  requiresOpposingHero : Bool := false
  /-- Number and filter of graveyard cards to target before the trigger is stacked. -/
  graveyardTargets : Option (Nat × CardFilter) := none
deriving DecidableEq, Repr

/-- Bind the hero declared for direct damage or damage after destroying the source. -/
def Effect.bindOpposingHeroDamage (effect : Effect) (hero : PlayerId) : Option Effect :=
  match effect with
  | .prim (.dealDamage kind (.ownerOfSlot 0) amount) =>
    some (.prim (.dealDamage kind (.seated hero) amount))
  | .seq (.cons (.prim (.destroy .self_)) (.cons (.prim (.dealDamage kind (.ownerOfSlot 0) amount)) .nil)) =>
    some (.seqL [.prim (.destroy .self_), .prim (.dealDamage kind (.seated hero) amount)])
  | _ => none

/-- The hero declarations available when stacking a pending trigger. -/
def PendingTrigger.heroChoices (t : PendingTrigger) (players : List PlayerId) :
    List (Option PlayerId) :=
  if t.requiresOpposingHero then (players.filter (· != t.controller)).map some
  else match t.effect with
  | .prim (.intimidate (.ownerOfSlot 0)) => players.map some
  | _ => [none]

/-- Bind the declared target into the supported triggered effect. -/
def PendingTrigger.declaredEffect (t : PendingTrigger) (hero : Option PlayerId)
    (equipment : Option ObjId) : Effect :=
  if t.requiresOpposingHero then (hero.bind t.effect.bindOpposingHeroDamage).getD .nop
  else match t.effect, equipment with
  | .prim (.addCounter (.slot 0) kind amount), some id => .prim (.addCounter (.declared id) kind amount)
  | _, _ => (hero.bind t.effect.bindHeroTarget).getD t.effect

/-- An event that a delayed trigger can watch (CR 6.6.3). -/
inductive DelayedTriggerWatch where
  /-- Trigger once at the beginning of this phase. -/
  | phase (phase : Phase)
  /-- Trigger every time the controller pays a boost cost in the specified turn. -/
  | boostThisTurn (turn : Nat)
deriving DecidableEq, Repr

/-- A delayed triggered ability waiting for a future phase/event even if its source leaves the
arena (e.g. Intimidate returning banished cards at End Phase) (CR 6.6.3, 8.5.10). -/
structure DelayedTrigger where
  /-- Unique identifier for this delayed trigger. -/
  id : Nat
  /-- Controller of the delayed trigger. -/
  controller : PlayerId
  /-- Source object that created the delayed trigger. -/
  source : ObjId
  /-- Identity at registration, for delayed effects created by a resolving layer. -/
  sourceLki : Option LkiSnapshot := none
  /-- Event that causes this delayed trigger to fire. -/
  watch : DelayedTriggerWatch
  /-- Effect executed when triggered. -/
  effect : Effect := .nop
deriving DecidableEq, Repr

/-- Rotate clockwise `turnOrder` so that the turn-player's chosen `start` player appears first,
followed by all other players in clockwise order (CR 6.6.6b). -/
def rotateTurnOrderFrom (order : List PlayerId) (start : PlayerId) : List PlayerId :=
  match order.idxOf? start with
  | none => order
  | some idx => order.drop idx ++ order.take idx

/-- **I19** (starting player is first): whenever `start ∈ order`, `rotateTurnOrderFrom order start`
begins with `start` (CR 6.6.6b). -/
theorem rotateTurnOrderFrom_head {order : List PlayerId} {start : PlayerId}
    (hmem : start ∈ order) :
    (rotateTurnOrderFrom order start).head? = some start := by
  unfold rotateTurnOrderFrom
  cases hi : order.idxOf? start with
  | none =>
    have := List.idxOf?_eq_none_iff.mp hi
    exact False.elim (this hmem)
  | some idx =>
    dsimp only
    have hlt : idx < order.length := by
      have := List.idxOf?_eq_some_iff.mp hi
      exact this.1
    have hget : order[idx] = start := (List.idxOf?_eq_some_iff.mp hi).2.1
    have hdrop : (order.drop idx).head? = some start := by
      rw [List.head?_drop, List.getElem?_eq_getElem hlt, hget]
    cases hd : order.drop idx with
    | nil => rw [hd] at hdrop; cases hdrop
    | cons x xs =>
      rw [hd] at hdrop
      simp only [List.head?_cons, Option.some.injEq] at hdrop
      subst hdrop
      rfl

/-- **I19** (all players visited clockwise): `rotateTurnOrderFrom order start` is always a
permutation of `order` (every seated player stacks their pending triggers exactly once)
(CR 6.6.6b). -/
theorem rotateTurnOrderFrom_perm (order : List PlayerId) (start : PlayerId) :
    (rotateTurnOrderFrom order start).Perm order := by
  unfold rotateTurnOrderFrom
  cases order.idxOf? start with
  | none => exact List.Perm.refl _
  | some idx =>
    dsimp only
    refine List.perm_append_comm.trans ?_
    rw [List.take_append_drop]

/-- **I19** (1v1 turn-player control): in a 1v1 turn order `[p0, p1]` with `p0 ≠ p1`, choosing `p0`
produces `[p0, p1]` and choosing `p1` produces `[p1, p0]` (CR 6.6.6b). -/
theorem rotateTurnOrderFrom_1v1 {p0 p1 : PlayerId} (hne : p0 ≠ p1) :
    rotateTurnOrderFrom [p0, p1] p0 = [p0, p1] ∧
    rotateTurnOrderFrom [p0, p1] p1 = [p1, p0] := by
  unfold rotateTurnOrderFrom
  have h0 : [p0, p1].idxOf? p0 = some 0 := by
    simp [List.idxOf?, List.findIdx?, List.findIdx?.go]
  have h1 : [p0, p1].idxOf? p1 = some 1 := by
    have hne' : (p0 == p1) = false := by simp [hne]
    simp [List.idxOf?, List.findIdx?, List.findIdx?.go, hne']
  rw [h0, h1]
  exact ⟨rfl, rfl⟩

/-- Stack triggers clockwise from `start` onto an existing LIFO `stack` (each player pushes their
ordered triggers onto the top of the stack in clockwise turn order) (CR 6.6.6b). -/
def stackTriggersClockwise (order : List PlayerId) (start : PlayerId)
    (perPlayer : PlayerId → List PendingTrigger) (stack : List PendingTrigger) :
    List PendingTrigger :=
  (rotateTurnOrderFrom order start).foldl
    (fun stk p => (perPlayer p).foldl (fun acc t => t :: acc) stk)
    stack

/-- **I19** (1v1 LIFO resolution order control): when `p0` has trigger `t0` and `p1` has trigger
`t1` (`p0 ≠ p1`), choosing `start = p0` leaves `t1` on TOP of the stack (so `t1` resolves first
LIFO), whereas choosing `start = p1` leaves `t0` on TOP of the stack (so `t0` resolves first LIFO)
(CR 6.6.6b). -/
theorem stackTriggersClockwise_1v1_lifo {p0 p1 : PlayerId} (hne : p0 ≠ p1)
    (t0 t1 : PendingTrigger) :
    let perPlayer : PlayerId → List PendingTrigger := fun p =>
      if p == p0 then [t0] else if p == p1 then [t1] else []
    stackTriggersClockwise [p0, p1] p0 perPlayer [] = [t1, t0] ∧
    stackTriggersClockwise [p0, p1] p1 perPlayer [] = [t0, t1] := by
  obtain ⟨h0, h1⟩ := rotateTurnOrderFrom_1v1 hne
  have hne1 : p1 ≠ p0 := fun e => hne e.symm
  unfold stackTriggersClockwise
  rw [h0, h1]
  simp [hne1]

end Fab

end
