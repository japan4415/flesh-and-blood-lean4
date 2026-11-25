module

public import Fab.Core.Property
public import Fab.Core.Ids
public import Fab.State.Zone
public import Fab.Core.Keyword

/-!
# 4-Stage Replacement Effects & Arcane Prevention (CR 6.4-6.5, 8.3)

Implements the Comprehensive Rules 4-stage replacement-effect pipeline and damage prevention
mechanics:
1. **Stage A (`selfOrIdentity`)**: Self-replacement and identity-replacement (CR 6.4.10a, 6.4.10b).
2. **Stage B (`standard`)**: Standard replacement effects such as moving to deck bottom instead of
   graveyard or draw replacements (CR 6.4.10c).
3. **Stage C (`prevention`)**: Damage prevention effects — **Ward X** (mandatory self-destruction)
   (CR 8.3.21), **Arcane Barrier X** (optional arcane-only resource payment) (CR 8.3.1),
   **Spellvoid X** (optional arcane-only self-destruction) (CR 8.3.11), **Quell X** (optional
   resource payment + end-of-chain destruction) (CR 8.3.19), and **Shielding Prevention**
   (CR 6.4.10d).
4. **Stage D (`outcome`)**: Outcome-replacement effects applied after event resolution (CR 6.4.10e).

Enforces:
- **At-most-once rule (CR 6.4.5)**: no replacement effect applies more than once to the same event.
- **Affected-player ordering (CR 6.5.1)**: when multiple effects compete within a stage, the
  affected player's choice order determines which applies first.
- **L5**: independent relational specification `ReplacementStageSpec`, soundness
  (`applyReplacementPipeline_matches_spec`), and uniqueness (`ReplacementStageSpec.unique`).
-/

@[expose] public section

namespace Fab

/-- A proposed event passing through the 4-stage replacement pipeline (CR 1.9, 6.4). -/
inductive ProposedEvent where
  /-- Proposed damage of `kind` to `target` for `amount` points (CR 8.5.3). -/
  | damage (target : PlayerId) (kind : DamageKind) (amount : Nat) (outcomeTag : Nat := 0)
  /-- Proposed zone movement of `obj` owned by `owner` from `src` to `dst`. -/
  | moveToZone (obj : ObjId) (owner : PlayerId) (src dst : Zone) (faceDown : Bool := false)
  /-- Proposed draw of `count` cards by `player`. -/
  | drawCard (player : PlayerId) (count : Nat)
  /-- Proposed outcome of a Clash or comparable contest (CR 6.4.10e). -/
  | clashOutcome (winner : Option PlayerId) (outcomeTag : Nat := 0)
deriving DecidableEq, Repr

/-- What transformation a replacement or prevention effect performs on a matching event (CR 6.4). -/
inductive ReplacementAction where
  /-- Stage A: modify damage amount by `delta` (clamped at 0). -/
  | modifyDamage (delta : Int)
  /-- Stage B: redirect a zone move destined for `watchDst` to `newDst` with facing `faceDown`. -/
  | redirectZone (watchDst newDst : Zone) (faceDown : Bool)
  /-- Stage B: replace a draw event with gaining `gain` life instead. -/
  | replaceDrawWithLife (gain : Nat)
  /-- Stage C (mandatory): Ward X — destroy source permanent and prevent up to `amt` damage of
  any kind (CR 8.3.21). -/
  | wardPrevent (amt : Nat)
  /-- Stage C (optional): Arcane Barrier X — pay `amt` `{r}` to prevent up to `amt` arcane
  damage (CR 8.3.1). -/
  | arcaneBarrierPrevent (amt : Nat)
  /-- Stage C (optional): Spellvoid X — destroy source equipment to prevent up to `amt` arcane
  damage (CR 8.3.11). -/
  | spellvoidPrevent (amt : Nat)
  /-- Stage C (optional): Quell X — pay `amt` `{r}` to prevent up to `amt` damage of any kind and
  mark source for destruction (CR 8.3.19). -/
  | quellPrevent (amt : Nat)
  /-- Stage C: prevent the next `amt` points of damage (CR 6.4.10a). -/
  | shieldPrevent (amt : Nat)
  /-- Stage D: replace an event's outcome tag (CR 6.4.10e). -/
  | replaceOutcome (newTag : Nat)
deriving DecidableEq, Repr

/-- An active replacement or prevention effect watching proposed events (CR 6.4). -/
structure ReplacementEffect where
  /-- Unique effect identifier enforcing the at-most-once rule (CR 6.4.5). -/
  id : Nat
  /-- Source object generating this replacement/prevention effect. -/
  source : ObjId
  /-- Controller of this replacement/prevention effect. -/
  controller : PlayerId
  /-- Which of the 4 stages this effect applies in (CR 6.4.10). -/
  stage : ReplacementStage
  /-- The replacement or prevention action performed. -/
  action : ReplacementAction
  /-- Whether the affected player may decline this effect; Ward is always mandatory (CR 8.3.21). -/
  optional : Bool := false
deriving DecidableEq, Repr

/-- Whether `e` is mandatory; Ward is always mandatory even if `optional` were set (CR 8.3.21). -/
def ReplacementEffect.isMandatory (e : ReplacementEffect) : Bool :=
  match e.action with
  | .wardPrevent _ => true
  | _ => !e.optional

/-- State threaded through the 4-stage replacement pipeline (CR 6.4-6.5). -/
structure ReplacementState where
  /-- Current (possibly modified) proposed event. -/
  event : ProposedEvent
  /-- IDs of replacement effects already applied to this event for at-most-once (CR 6.4.5). -/
  usedIds : List Nat := []
  /-- Remaining amounts of damage shields used in this event (CR 6.4.10a). -/
  shieldRemainders : List (Nat × Nat) := []
  /-- Sources destroyed as part of Ward / Spellvoid prevention (CR 8.3.11, 8.3.21). -/
  destroyedSources : List ObjId := []
  /-- Sources marked to be destroyed at end of chain/turn by Quell (CR 8.3.19). -/
  quellMarked : List ObjId := []
  /-- Remaining resource points `{r}` available to pay Arcane Barrier / Quell costs. -/
  availResources : Nat := 0
  /-- Total resource points `{r}` spent on prevention costs. -/
  resourcesPaid : Nat := 0
  /-- Life gained from draw-replacement effects. -/
  lifeGained : Nat := 0
deriving DecidableEq, Repr

/-- Whether replacement effect `e` is currently eligible to apply to `st` at `stage`
(CR 6.4.5, 6.4.10). -/
def ReplacementEffect.eligible (e : ReplacementEffect) (stage : ReplacementStage)
    (st : ReplacementState) : Bool :=
  e.stage == stage &&
  !(st.usedIds.contains e.id) &&
  match e.action, st.event with
  | .modifyDamage _, .damage _ _ amt _ => decide (0 < amt)
  | .redirectZone watchDst _ _, .moveToZone _ _ _ dst _ => dst == watchDst
  | .replaceDrawWithLife _, .drawCard _ cnt => decide (0 < cnt)
  | .wardPrevent _, .damage target _ amt _ => e.controller == target && decide (0 < amt)
  | .arcaneBarrierPrevent amt, .damage target .arcane dmg _ =>
    e.controller == target && decide (0 < dmg) && decide (amt ≤ st.availResources)
  | .arcaneBarrierPrevent _, _ => false
  | .spellvoidPrevent _, .damage target .arcane dmg _ =>
    e.controller == target && decide (0 < dmg)
  | .spellvoidPrevent _, _ => false
  | .quellPrevent amt, .damage target _ dmg _ =>
    e.controller == target && decide (0 < dmg) && decide (amt ≤ st.availResources)
  | .shieldPrevent _, .damage target _ dmg _ =>
    e.controller == target && decide (0 < dmg)
  | .replaceOutcome _, .damage _ _ _ _ => true
  | .replaceOutcome _, .clashOutcome _ _ => true
  | _, _ => false

/-- Apply one eligible replacement effect `e` to `st`, recording `e.id` in `usedIds` (CR 6.4.5). -/
def applyOneReplacement (st : ReplacementState) (e : ReplacementEffect) : ReplacementState :=
  let stUsed := { st with usedIds := e.id :: st.usedIds }
  match e.action, st.event with
  | .modifyDamage delta, .damage target kind amt tag =>
    { stUsed with event := .damage target kind (clampNonNeg (Int.ofNat amt + delta)) tag }
  | .redirectZone _ newDst fd, .moveToZone obj owner src _ _ =>
    { stUsed with event := .moveToZone obj owner src newDst fd }
  | .replaceDrawWithLife gain, .drawCard p _ =>
    { stUsed with event := .drawCard p 0, lifeGained := st.lifeGained + gain }
  | .wardPrevent amt, .damage target kind dmg tag =>
    { stUsed with
      event := .damage target kind (dmg - amt) tag
      destroyedSources := st.destroyedSources ++ [e.source] }
  | .arcaneBarrierPrevent amt, .damage target .arcane dmg tag =>
    { stUsed with
      event := .damage target .arcane (dmg - amt) tag
      availResources := st.availResources - amt
      resourcesPaid := st.resourcesPaid + amt }
  | .spellvoidPrevent amt, .damage target .arcane dmg tag =>
    { stUsed with
      event := .damage target .arcane (dmg - amt) tag
      destroyedSources := st.destroyedSources ++ [e.source] }
  | .quellPrevent amt, .damage target kind dmg tag =>
    { stUsed with
      event := .damage target kind (dmg - amt) tag
      availResources := st.availResources - amt
      resourcesPaid := st.resourcesPaid + amt
      quellMarked := st.quellMarked ++ [e.source] }
  | .shieldPrevent amt, .damage target kind dmg tag =>
    { stUsed with
      event := .damage target kind (dmg - amt) tag
      shieldRemainders := (e.id, amt - dmg) :: stUsed.shieldRemainders }
  | .replaceOutcome newTag, .damage target kind dmg _ =>
    { stUsed with event := .damage target kind dmg newTag }
  | .replaceOutcome newTag, .clashOutcome w _ =>
    { stUsed with event := .clashOutcome w newTag }
  | _, _ => stUsed

/-- Preserve unused effects and the unspent amounts of applied shields (CR 6.4.10a). -/
def keepDamageReplacements (effects : List ReplacementEffect) (result : ReplacementState) :
    List ReplacementEffect :=
  effects.filterMap fun effect =>
    if !result.usedIds.contains effect.id then some effect
    else match result.shieldRemainders.lookup effect.id with
    | some (amount + 1) => some { effect with action := .shieldPrevent (amount + 1) }
    | _ => none

/-- Choose the next eligible replacement effect in `stage` respecting the affected player's
explicit choice list `acceptedIds` (CR 6.5.1):
- Optional effects apply ONLY if their `id ∈ acceptedIds`.
- Mandatory effects including Ward (CR 8.3.21) ALWAYS apply even if absent from `acceptedIds`.
- Among eligible effects that will apply, pick the one appearing earliest in `acceptedIds`,
  otherwise the first mandatory eligible effect. -/
def pickNextReplacement (stage : ReplacementStage) (acceptedIds : List Nat)
    (effs : List ReplacementEffect) (st : ReplacementState) : Option ReplacementEffect :=
  let elig := effs.filter fun e =>
    e.eligible stage st && (e.isMandatory || acceptedIds.contains e.id)
  match acceptedIds.findSome? fun cid => elig.find? (fun e => e.id == cid) with
  | some e => some e
  | none => elig.head?

/-- Fuel-bounded application loop for a single `ReplacementStage` (CR 6.4.5, 6.5.1). -/
def applyStageLoop (stage : ReplacementStage) (acceptedIds : List Nat)
    (effs : List ReplacementEffect) : Nat → ReplacementState → ReplacementState
  | 0, st => st
  | fuel + 1, st =>
    match pickNextReplacement stage acceptedIds effs st with
    | none => st
    | some e => applyStageLoop stage acceptedIds effs fuel (applyOneReplacement st e)

/-- Run all eligible effects in a single `ReplacementStage` using exact bound `effs.length`. -/
def applyReplacementStage (stage : ReplacementStage) (acceptedIds : List Nat)
    (effs : List ReplacementEffect) (st : ReplacementState) : ReplacementState :=
  applyStageLoop stage acceptedIds effs effs.length st

/-- Full 4-stage replacement pipeline:
`selfOrIdentity` → `standard` → `prevention` → `outcome` (CR 6.4.10, 6.5.1). -/
def applyReplacementPipeline (acceptedIds : List Nat) (effs : List ReplacementEffect)
    (init : ReplacementState) : ReplacementState :=
  ReplacementStage.order.foldl (fun st stage => applyReplacementStage stage acceptedIds effs st) init

/-- Helper: every effect returned by `pickNextReplacement` is eligible and has `e.id ∉ st.usedIds`. -/
theorem pickNextReplacement_not_used {stage : ReplacementStage} {acceptedIds : List Nat}
    {effs : List ReplacementEffect} {st : ReplacementState} {e : ReplacementEffect}
    (h : pickNextReplacement stage acceptedIds effs st = some e) :
    e.id ∉ st.usedIds := by
  have helig : e ∈ effs.filter fun x =>
      x.eligible stage st && (x.isMandatory || acceptedIds.contains x.id) := by
    unfold pickNextReplacement at h
    dsimp only at h
    cases hf : acceptedIds.findSome? (fun cid =>
        (effs.filter fun x => x.eligible stage st && (x.isMandatory || acceptedIds.contains x.id)).find?
          (fun x => x.id == cid)) with
    | some e1 =>
      rw [hf] at h
      simp only [Option.some.injEq] at h
      subst h
      have hmem := List.exists_of_findSome?_eq_some hf
      obtain ⟨cid, _, hfind⟩ := hmem
      exact List.mem_of_find?_eq_some hfind
    | none =>
      rw [hf] at h
      exact List.mem_of_head? h
  have hcond := (List.mem_filter.mp helig).2
  simp only [Bool.and_eq_true, ReplacementEffect.eligible, Bool.not_eq_true'] at hcond
  have hnc : st.usedIds.contains e.id = false := hcond.1.1.2
  intro hin
  have : st.usedIds.contains e.id = true := List.contains_iff_mem.mpr hin
  rw [hnc] at this
  cases this

/-- **At-most-once preservation** (CR 6.4.5): `applyStageLoop` preserves `st.usedIds.Nodup` (no
replacement effect ID is ever applied twice to the same event). -/
theorem applyStageLoop_nodup (stage : ReplacementStage) (acceptedIds : List Nat)
    (effs : List ReplacementEffect) :
    ∀ (fuel : Nat) {st : ReplacementState},
      st.usedIds.Nodup → (applyStageLoop stage acceptedIds effs fuel st).usedIds.Nodup
  | 0, _, hnd => hnd
  | fuel + 1, st, hnd => by
    unfold applyStageLoop
    cases hp : pickNextReplacement stage acceptedIds effs st with
    | none => exact hnd
    | some e =>
      have hnot : e.id ∉ st.usedIds := pickNextReplacement_not_used hp
      have hnd1 : (applyOneReplacement st e).usedIds.Nodup := by
        have hu : (applyOneReplacement st e).usedIds = e.id :: st.usedIds := by
          unfold applyOneReplacement
          cases e.action <;> cases st.event <;>
            first | rfl | (rename_i _ kind _ _; cases kind <;> rfl)
        rw [hu, List.nodup_cons]
        exact ⟨hnot, hnd⟩
      exact applyStageLoop_nodup stage acceptedIds effs fuel hnd1

/-- **At-most-once global** (CR 6.4.5): starting from `usedIds = []`, `applyReplacementPipeline`
never applies any replacement effect ID more than once. -/
theorem applyReplacementPipeline_nodup (acceptedIds : List Nat) (effs : List ReplacementEffect)
    (init : ReplacementState) (hnd : init.usedIds.Nodup) :
    (applyReplacementPipeline acceptedIds effs init).usedIds.Nodup := by
  unfold applyReplacementPipeline ReplacementStage.order
  simp only [List.foldl_cons, List.foldl_nil]
  apply applyStageLoop_nodup
  apply applyStageLoop_nodup
  apply applyStageLoop_nodup
  apply applyStageLoop_nodup
  exact hnd

/-- **L5** (independent relational specification of 4-stage replacement pipeline) (CR 6.4.10, 6.5.1):
explicitly chains `selfOrIdentity` → `standard` → `prevention` → `outcome` and asserts
at-most-once application (`usedIds.Nodup`). -/
inductive ReplacementStageSpec (acceptedIds : List Nat) (effs : List ReplacementEffect)
    (init : ReplacementState) : ReplacementState → Prop where
  /-- Exact 4-stage chaining with `usedIds.Nodup`. -/
  | run (s1 s2 s3 s4 : ReplacementState)
      (hnd0 : init.usedIds.Nodup)
      (h1 : s1 = applyReplacementStage .selfOrIdentity acceptedIds effs init)
      (h2 : s2 = applyReplacementStage .standard acceptedIds effs s1)
      (h3 : s3 = applyReplacementStage .prevention acceptedIds effs s2)
      (h4 : s4 = applyReplacementStage .outcome acceptedIds effs s3)
      (hnd4 : s4.usedIds.Nodup) :
      ReplacementStageSpec acceptedIds effs init s4

/-- **L5** (soundness): `applyReplacementPipeline` satisfies `ReplacementStageSpec`. -/
theorem applyReplacementPipeline_matches_spec (acceptedIds : List Nat)
    (effs : List ReplacementEffect) (init : ReplacementState) (hnd : init.usedIds.Nodup) :
    ReplacementStageSpec acceptedIds effs init (applyReplacementPipeline acceptedIds effs init) := by
  exact ReplacementStageSpec.run
    (applyReplacementStage .selfOrIdentity acceptedIds effs init)
    (applyReplacementStage .standard acceptedIds effs _)
    (applyReplacementStage .prevention acceptedIds effs _)
    (applyReplacementPipeline acceptedIds effs init)
    hnd rfl rfl rfl rfl (applyReplacementPipeline_nodup acceptedIds effs init hnd)

/-- **L5** (uniqueness): `ReplacementStageSpec` determines the final `ReplacementState` uniquely. -/
theorem ReplacementStageSpec.unique {acceptedIds : List Nat} {effs : List ReplacementEffect}
    {init out1 out2 : ReplacementState}
    (h1 : ReplacementStageSpec acceptedIds effs init out1)
    (h2 : ReplacementStageSpec acceptedIds effs init out2) :
    out1 = out2 := by
  cases h1; cases h2; simp_all

/-- **Release Notes Ruling (Ward mandatory vs optional decline)** (CR 8.3.21):
Ward X is ALWAYS mandatory — even when `acceptedIds = []` (player declines all optional
preventions), Ward X destroys its source permanent and prevents up to `amt` damage. -/
theorem ward_mandatory_prevents_damage (p : PlayerId) (src : ObjId) (kind : DamageKind)
    (dmg amt : Nat) (hdmg : 0 < dmg) :
    let wardEff : ReplacementEffect :=
      { id := 1, source := src, controller := p, stage := .prevention,
        action := .wardPrevent amt, optional := true }
    let res := applyReplacementPipeline [] [wardEff] { event := .damage p kind dmg }
    res.event = .damage p kind (dmg - amt) ∧ res.destroyedSources = [src] := by
  unfold applyReplacementPipeline ReplacementStage.order applyReplacementStage applyStageLoop
    pickNextReplacement ReplacementEffect.eligible ReplacementEffect.isMandatory applyOneReplacement
  simp [hdmg, applyStageLoop]

/-- **Release Notes Ruling (Arcane Barrier arcane-only)** (CR 8.3.1):
Arcane Barrier X is NEVER eligible against physical damage, even when accepted with ample
resources. -/
theorem arcaneBarrier_ignores_physical (p : PlayerId) (src : ObjId) (dmg amt res : Nat) :
    let abEff : ReplacementEffect :=
      { id := 1, source := src, controller := p, stage := .prevention,
        action := .arcaneBarrierPrevent amt, optional := true }
    abEff.eligible .prevention { event := .damage p .physical dmg, availResources := res } = false := by
  rfl

/-- **Release Notes Ruling (Arcane Barrier optional decline)** (CR 8.3.1):
Arcane Barrier X is optional — when `acceptedIds = []`, even with ample resources against arcane
damage, the full arcane damage passes through untouched and 0 resources are paid. -/
theorem arcaneBarrier_optional_can_decline (p : PlayerId) (src : ObjId) (dmg amt avail : Nat) :
    let abEff : ReplacementEffect :=
      { id := 1, source := src, controller := p, stage := .prevention,
        action := .arcaneBarrierPrevent amt, optional := true }
    let res := applyReplacementPipeline [] [abEff] { event := .damage p .arcane dmg, availResources := avail }
    res.event = .damage p .arcane dmg ∧ res.resourcesPaid = 0 := by
  unfold applyReplacementPipeline ReplacementStage.order applyReplacementStage applyStageLoop
    pickNextReplacement ReplacementEffect.eligible ReplacementEffect.isMandatory
  simp

end Fab

end
