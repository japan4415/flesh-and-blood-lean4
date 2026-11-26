module

public import Fab.Tournament.DeckLegality

/-!
# Booster Draft

A draft pod is separate from the two-seat game. A trusted caller supplies the contents of physical
boosters. Packs are treated as multisets, with a canonical display order rather than physical
shuffle order. A pick is locked on submission and all packs pass after every seat has picked
(TRP 8.2, 8.2.1).
-/

public section

namespace Fab.BoosterDraft

open scoped List

/-- Set-specific booster configuration and its basic-rarity logical card IDs (TRP 8.2). -/
structure Product where
  /-- Expansion supplied to the entire pod. -/
  set : SetCode
  /-- Number of draftable slots at the front of a booster. -/
  draftableSlots : Nat
  /-- Total physical slots, including the excluded slots at the back. -/
  totalSlots : Nat
  /-- Cards of basic rarity in this product, including reference tokens and adult heroes. -/
  basics : List CardId
deriving DecidableEq, Repr

/-- Physical booster slots in order. An excluded reference or insert may have no logical card ID. -/
abbrev Booster := List (Option CardId)

/-- The standard three boosters, in opening order, for one seat (TRP 8.2). -/
structure Boosters where
  /-- First booster, passed left. -/
  first : Booster
  /-- Second booster, passed right. -/
  second : Booster
  /-- Third booster, passed left. -/
  third : Booster
deriving DecidableEq, Repr

/-- Whether the format requires the complete pool and hero to be registered (TRP 3.7, 8.2). -/
inductive RegistrationPolicy where
  /-- Each game may use a different eligible hero. -/
  | optional
  /-- Each seat records its picks and fixes a hero for the event. -/
  | required
deriving DecidableEq, Repr

/-- The draft's public phase. Booster indices are zero-based. -/
inductive Phase where
  /-- Each seat may commit one pick from its current pack. -/
  | picking (booster : Nat)
  /-- Each seat may review its own pool before the next opening. -/
  | review (nextBooster : Nat)
  /-- All three boosters have been drafted. -/
  | complete
deriving DecidableEq, Repr

/-- Rejected draft, registration, or deck-construction request. -/
inductive Error where
  /-- The booster slot counts are inconsistent. -/
  | invalidProduct
  /-- The pod needs at least two seats. -/
  | tooFewSeats
  /-- The given seat and booster contain an invalid draftable slot or slot count. -/
  | invalidBooster (seat booster : Nat)
  /-- There is no such seat in the pod. -/
  | invalidSeat
  /-- This action is unavailable during the current phase. -/
  | wrongPhase
  /-- The seat has already locked its pick for this pass. -/
  | alreadyPicked
  /-- The card is absent from the seat's current pack. -/
  | cardUnavailable
  /-- This pod has no event registration. -/
  | registrationNotRequired
  /-- The seat has already fixed its event hero. -/
  | alreadyRegistered
  /-- The registration record differs from the multiset of drafted cards. -/
  | incorrectPool
  /-- The chosen hero is outside the seat's eligible young heroes. -/
  | heroUnavailable
  /-- The seat must register before constructing a game pool. -/
  | registrationRequired
  /-- The selected hero differs from the event registration. -/
  | wrongRegisteredHero
  /-- A requested basic card is unavailable to this hero in this set. -/
  | basicUnavailable
  /-- The game pool cannot supply the minimum number of deck cards. -/
  | insufficientDeckCards
  /-- The current pass or opening contains inconsistent pod data. -/
  | invalidRound
deriving DecidableEq, Repr

/-- The information visible to the requesting seat under the draft information policy. -/
structure View where
  /-- Shared phase, including the current or next booster. -/
  phase : Phase
  /-- Uncommitted current pack in canonical order, if the seat may view it. -/
  pack : Option (List CardId)
  /-- The seat's own previous picks, visible during review and after the draft. -/
  drafted : Option (List CardId)
deriving DecidableEq, Repr

/-- A hero and the basic-rarity supplies requested for a game. -/
structure DeckChoice where
  /-- Young hero from this draft product. -/
  hero : CardId
  /-- Basic cards for this game, such as weapons and Cracked Baubles. -/
  basics : List CardId := []
deriving DecidableEq, Repr

/-- Authoritative pod state. Present only `State.view` to an individual player. -/
structure State where private mk ::
  /-- Card definitions used both for booster validation and deck construction. -/
  db : CardDB
  /-- Product rules used throughout the draft. -/
  product : Product
  /-- Whether a hero must be registered. -/
  registration : RegistrationPolicy
  /-- Current draft phase. -/
  phase : Phase
  /-- Unfinished packs currently held by each seat. -/
  private packs : List (List CardId)
  /-- Future boosters grouped by opening round, then by seat. -/
  private unopened : List (List (List CardId))
  /-- Committed picks within the current pass, in seating order. -/
  private choices : List (Option CardId)
  /-- Picks from completed passes, in seating order. -/
  private pools : List (List CardId)
  /-- Fixed hero of each registered seat. -/
  private heroes : List (Option CardId)

private def draftable (db : CardDB) (product : Product) (id : CardId) : Bool :=
  !product.basics.contains id && (db.find? id).any fun card => card.sets.contains product.set

private def openBooster (db : CardDB) (product : Product) (seat round : Nat)
    (booster : Booster) : Except Error (List CardId) :=
  let slots := booster.take product.draftableSlots
  let cards := slots.filterMap id
  if booster.length = product.totalSlots && cards.length = product.draftableSlots &&
      cards.all (draftable db product) then
    .ok cards
  else
    .error (.invalidBooster seat round)

/-- Start a pod from seat-indexed, externally supplied boosters (TRP 4.13, 8.2). -/
def State.start (db : CardDB) (product : Product) (registration : RegistrationPolicy)
    (seats : List Boosters) : Except Error State := do
  if !(0 < product.draftableSlots && product.draftableSlots ≤ product.totalSlots) then
    throw .invalidProduct
  if seats.length < 2 then
    throw .tooFewSeats
  let participants := seats.zipIdx
  let first ← participants.mapM fun (p, seat) => openBooster db product seat 0 p.first
  let second ← participants.mapM fun (p, seat) => openBooster db product seat 1 p.second
  let third ← participants.mapM fun (p, seat) => openBooster db product seat 2 p.third
  return ⟨db, product, registration, .picking 0, first, [second, third],
    List.replicate seats.length none, List.replicate seats.length [], List.replicate seats.length none⟩

private def collectPicks : List (List CardId) → List CardId → Option (List (CardId × List CardId))
  | [], [] => some []
  | pack :: packs, card :: cards => do
    if card ∈ pack then
      return (card, pack.erase card) :: (← collectPicks packs cards)
    else none
  | _, _ => none

private theorem collectPicks_perm {packs : List (List CardId)} {picks : List CardId}
    {taken : List (CardId × List CardId)} (h : collectPicks packs picks = some taken) :
    (taken.map Prod.fst ++ (taken.map Prod.snd).flatten).Perm packs.flatten := by
  induction packs generalizing picks taken with
  | nil =>
    cases picks <;> simp_all [collectPicks]
  | cons pack packs ih =>
    cases picks with
    | nil => simp [collectPicks] at h
    | cons card picks =>
      by_cases mem : card ∈ pack
      · cases hs : collectPicks packs picks with
        | none => simp [collectPicks, mem, hs] at h
        | some rest =>
          simp [collectPicks, mem, hs] at h
          subst taken
          simp only [List.map_cons, List.flatten_cons, List.cons_append]
          calc
            _ ~ card :: (pack.erase card ++ (rest.map Prod.fst ++ (rest.map Prod.snd).flatten)) :=
              (List.perm_append_comm_assoc _ _ _).cons _
            _ ~ card :: (pack.erase card ++ packs.flatten) :=
              ((ih hs).append_left _).cons _
            _ ~ pack ++ packs.flatten :=
              (List.perm_cons_erase mem).symm.append_right _
      · simp [collectPicks, mem] at h

private theorem appendPicks_perm (pools : List (List CardId))
    (taken : List (CardId × List CardId)) (len : pools.length = taken.length) :
    (List.zipWith (fun pool pick => pick.1 :: pool) pools taken).flatten.Perm
      (taken.map Prod.fst ++ pools.flatten) := by
  induction pools generalizing taken with
  | nil => cases taken <;> simp_all
  | cons pool pools ih =>
    cases taken with
    | nil => simp at len
    | cons pick taken =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at len
      simp only [List.zipWith_cons_cons, List.flatten_cons, List.map_cons, List.cons_append]
      exact (((ih taken len).append_left pool).trans (List.perm_append_comm_assoc _ _ _)).cons _

/-- Each pass moves packs around the ring: the left neighbor has the next seat index. -/
private def passPacks (left : Bool) (packs : List (List CardId)) : List (List CardId) :=
  match (if left then packs.reverse else packs) with
  | [] => []
  | first :: rest =>
    let rotated := rest ++ [first]
    if left then rotated.reverse else rotated

private theorem passPacks_perm (left : Bool) (packs : List (List CardId)) :
    (passPacks left packs).Perm packs := by
  cases left
  · cases packs with
    | nil => rfl
    | cons head tail => exact List.perm_append_singleton head tail
  · have h := List.reverse_perm (l := packs)
    cases hr : packs.reverse with
    | nil => simpa [passPacks, hr] using h
    | cons head tail =>
      simp only [passPacks, ite_true, hr]
      exact (List.reverse_perm _).trans ((List.perm_append_singleton head tail).trans (hr ▸ h))

/-- Organizer-only multiset of all draftable cards, including unopened packs and committed pools. -/
def State.cardsInPod (s : State) : List CardId :=
  (s.pools.flatten ++ s.packs.flatten) ++ s.unopened.flatten.flatten

private def finishPass (s : State) (booster : Nat) (picks : List CardId) : Except Error State :=
  match collectPicks s.packs picks with
  | none => .error .invalidRound
  | some taken =>
    if s.pools.length ≠ taken.length then .error .invalidRound
    else
      let remaining := taken.map Prod.snd
      let pools := List.zipWith (fun pool pick => pick.1 :: pool) s.pools taken
      let phase :=
        if remaining.all List.isEmpty then
          if s.unopened.isEmpty then .complete else .review (booster + 1)
        else .picking booster
      .ok { s with
        phase
        pools
        packs := passPacks (booster % 2 == 0) remaining
        choices := List.replicate s.choices.length none }

private theorem finishPass_preserves {s next : State} {booster : Nat} {picks : List CardId}
    (h : finishPass s booster picks = .ok next) : next.cardsInPod.Perm s.cardsInPod := by
  cases ht : collectPicks s.packs picks with
  | none => simp [finishPass, ht] at h
  | some taken =>
    by_cases len : s.pools.length = taken.length
    · simp [finishPass, ht, len] at h
      subst next
      unfold State.cardsInPod
      apply List.Perm.append_right
      calc
        _ ~ (taken.map Prod.fst ++ s.pools.flatten) ++ (taken.map Prod.snd).flatten :=
          (appendPicks_perm s.pools taken len).append (passPacks_perm _ _).flatten
        _ ~ s.pools.flatten ++ (taken.map Prod.fst ++ (taken.map Prod.snd).flatten) := by
          rw [List.append_assoc]
          exact List.perm_append_comm_assoc _ _ _
        _ ~ _ := (collectPicks_perm ht).append_left _
    · simp [finishPass, ht, len] at h

/-- Lock one pick for the given seat. Only the final submission advances the synchronized pass. -/
def State.pick (s : State) (seat : PlayerId) (card : CardId) : Except Error State :=
  match s.phase with
  | .picking booster =>
    match s.choices[seat.n]?, s.packs[seat.n]? with
    | some none, some pack =>
      if card ∉ pack then .error .cardUnavailable
      else
        let choices := s.choices.set seat.n (some card)
        let next := { s with choices }
        if choices.all Option.isSome then
          finishPass next booster (choices.filterMap id)
        else
          .ok next
    | some (some _), _ => .error .alreadyPicked
    | _, _ => .error .invalidSeat
  | _ => .error .wrongPhase

/-- A successful pick transfers cards between locations without adding or losing any copy. -/
theorem State.pick_preserves {s next : State} {seat : PlayerId} {card : CardId}
    (h : s.pick seat card = .ok next) : next.cardsInPod.Perm s.cardsInPod := by
  cases phase : s.phase with
  | complete | review => simp [State.pick, phase] at h
  | picking booster =>
    cases choice : s.choices[seat.n]? with
    | none => simp [State.pick, phase, choice] at h
    | some option =>
      cases option with
      | some _ => simp [State.pick, phase, choice] at h
      | none =>
        cases pack : s.packs[seat.n]? with
        | none => simp [State.pick, phase, choice, pack] at h
        | some current =>
          by_cases mem : card ∈ current
          · simp only [State.pick, phase, choice, pack, mem, not_true_eq_false, ite_false] at h
            split at h
            · have preserved := finishPass_preserves h
              exact preserved
            · cases h
              exact List.Perm.rfl
          · simp [State.pick, phase, choice, pack, mem] at h

/-- End the review period and open the next booster at each seat (TRP 8.2.1). -/
def State.openNext (s : State) : Except Error State :=
  match s.phase with
  | .review booster =>
    match s.unopened with
    | packs :: rest =>
      if s.packs.all List.isEmpty then
        .ok { s with phase := .picking booster, packs, unopened := rest }
      else .error .invalidRound
    | [] => .error .invalidRound
  | _ => .error .wrongPhase

/-- Opening the next booster changes the location of those cards without changing the multiset. -/
theorem State.openNext_preserves {s next : State} (h : s.openNext = .ok next) :
    next.cardsInPod.Perm s.cardsInPod := by
  cases phase : s.phase with
  | complete | picking => simp [State.openNext, phase] at h
  | review booster =>
    cases pending : s.unopened with
    | nil => simp [State.openNext, phase, pending] at h
    | cons packs rest =>
      by_cases empty : s.packs.all List.isEmpty = true
      · simp [State.openNext, phase, pending, empty] at h
        subst next
        have hp : s.packs.flatten = [] :=
          List.flatten_eq_nil_iff.mpr fun pack mem =>
            List.isEmpty_iff.mp ((List.all_eq_true.mp empty) pack mem)
        simp [State.cardsInPod, hp, pending, List.append_assoc]
      · simp [State.openNext, phase, pending, empty] at h

/-- Project only information the requesting seat may see (TRP 8.2.1). -/
def State.view (s : State) (seat : PlayerId) : Option View := do
  let pool ← s.pools[seat.n]?
  match s.phase with
  | .picking _ =>
    let choice ← s.choices[seat.n]?
    let pack ← s.packs[seat.n]?
    let visible := if choice.isNone then some (pack.mergeSort fun a b => a.val ≤ b.val) else none
    return ⟨s.phase, visible, none⟩
  | .review _ | .complete => return ⟨s.phase, none, some pool.reverse⟩

private def validHero (s : State) (picks : List CardId) (hero : CardId) : Bool :=
  (s.product.basics.contains hero || picks.contains hero) &&
    (s.db.find? hero).any fun c => c.isYoungHero && c.sets.contains s.product.set

/-- Register all picks and lock the seat's young hero when required (TRP 3.7, 8.2.2). -/
def State.register (s : State) (seat : PlayerId) (hero : CardId) (recordedPicks : List CardId) :
    Except Error State := do
  if s.phase != .complete then
    throw .wrongPhase
  if s.registration != .required then
    throw .registrationNotRequired
  let some picks := s.pools[seat.n]? | throw .invalidSeat
  let some previous := s.heroes[seat.n]? | throw .invalidSeat
  if previous.isSome then
    throw .alreadyRegistered
  if !recordedPicks.isPerm picks then
    throw .incorrectPool
  if !validHero s picks hero then
    throw .heroUnavailable
  return { s with heroes := s.heroes.set seat.n (some hero) }

private def usableBasic (s : State) (heroDef : CardDef) (id : CardId) : Bool :=
  s.product.basics.contains id && decide (CardAllowedForHero s.db heroDef id) &&
    (s.db.find? id).any (fun c => c.isWeapon || c.isEquipment || c.isDeckCard)

/-- Build the game card-pool from compatible picks and permitted basic cards (TRP 8.2).
Off-class picks are still part of the complete registration record. -/
def State.deck (s : State) (seat : PlayerId) (choice : DeckChoice) : Except Error DeckList := do
  if s.phase != .complete then
    throw .wrongPhase
  let some picks := s.pools[seat.n]? | throw .invalidSeat
  if s.registration == .required then
    let some (some hero) := s.heroes[seat.n]? | throw .registrationRequired
    if hero != choice.hero then
      throw .wrongRegisteredHero
  if !validHero s picks choice.hero then
    throw .heroUnavailable
  let some heroDef := s.db.find? choice.hero | throw .heroUnavailable
  if !choice.basics.all (usableBasic s heroDef) then
    throw .basicUnavailable
  let pool := picks.filter (fun id => decide (CardAllowedForHero s.db heroDef id)) ++ choice.basics
  let deck := { hero := choice.hero, pool }
  if !decide (DraftDeckValid s.db deck) then
    throw .insufficientDeckCards
  return deck

end Fab.BoosterDraft

end
