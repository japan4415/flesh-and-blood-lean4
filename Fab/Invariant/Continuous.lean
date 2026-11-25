module

public import Fab.Invariant.Step

/-!
# 8-Stage Continuous Effects, Dependency, I12c, and L5 Invariants (M6a)

Proves M6a theorems from `docs/roadmap.md`:
- **I12c** (inner total termination bound): `evalCharacteristics_steps_eq` (from `Continuous.lean`)
  and `empty_effects_eq_counters`
- **L5** (8-stage ordering, sub-stage precedence, dependency overriding timestamp, cyclic
  dependency timestamp fallback, and asset-cost calculation (CR 5.1.5)):
  `stage7_setBase_precedes_stage8_add`, `stage8_restrict_blocks_add`,
  `dependency_overrides_timestamp`, `cycle_falls_back_to_timestamp`,
  `assetCost_set_add_sub_example`
- **Duration expiry**: `expireEffects_removes_duration`, `expireEffects_keeps_other`
-/

@[expose] public section

namespace Fab

/-- When `activeEffects = []`, 8-stage evaluation reduces identically to printed characteristics
plus object counters (`+1{p}`, `-1{d}`) (CR 6.3.2). -/
theorem empty_effects_eq_counters (o : Object) (face : CardFace) (oid : ObjId) :
    evalCharacteristics [] o face oid = applyCounters o (DerivedChars.ofBase o face) := rfl

/-- **L5** (Stage 7 precedes Stage 8 regardless of timestamps) (CR 6.3.2g, 6.3.2h):
even when a Stage 8 `+delta{p}` effect has an EARLIER timestamp (`tAdd < tSet`) than a Stage 7
`setBasePower v` effect, Stage 7 sets base power to `v` FIRST and Stage 8 then adds `delta`
(yielding `v + delta`, never `v`). -/
theorem stage7_setBase_precedes_stage8_add (o : Object) (face : CardFace) (oid : ObjId)
    (v delta : Int) (tAdd tSet : Timestamp)
    (hcnt : o.plusPowerCounters = 0) :
    let eAdd : ContinuousEffect :=
      { id := 1, source := oid, controller := o.controller, target := .obj oid,
        op := .addPower delta, timestamp := tAdd }
    let eSet : ContinuousEffect :=
      { id := 2, source := oid, controller := o.controller, target := .obj oid,
        op := .setBasePower v, timestamp := tSet }
    (evalCharacteristics [eAdd, eSet] o face oid).power = some (v + delta) := by
  simp [evalCharacteristics, evalCharacteristicsWithSteps, EffectStage.all, applyStage,
    SubStage.all, applyBucket, applyBucketLoop, pickNextInBucket, pickEarliest, isIndependent,
    dependsOn, ContinuousEffect.appliesTo, EffectTarget.matches,
    EffectOp.stage, EffectOp.subStage, applyEffectOp, applyCounters, DerivedChars.ofBase, hcnt]

/-- **L5** (Sub-stage `restrict` precedes `add` regardless of timestamps) (CR 1.0.1a, 6.3.3):
a Stage 8 `lockPower` restriction blocks a Stage 8 `addPower` modifier even when `addPower` has
an earlier timestamp. -/
theorem stage8_restrict_blocks_add (o : Object) (face : CardFace) (oid : ObjId)
    (baseP delta : Int) (tAdd tLock : Timestamp)
    (hp : face.power = some baseP) :
    let eAdd : ContinuousEffect :=
      { id := 1, source := oid, controller := o.controller, target := .obj oid,
        op := .addPower delta, timestamp := tAdd }
    let eLock : ContinuousEffect :=
      { id := 2, source := oid, controller := o.controller, target := .obj oid,
        op := .lockPower, timestamp := tLock }
    (evalCharacteristics [eAdd, eLock] o face oid).power = some baseP := by
  simp [evalCharacteristics, evalCharacteristicsWithSteps, EffectStage.all, applyStage,
    SubStage.all, applyBucket, applyBucketLoop, pickNextInBucket, pickEarliest, isIndependent,
    dependsOn, ContinuousEffect.appliesTo, EffectTarget.matches,
    EffectOp.stage, EffectOp.subStage, applyEffectOp, applyCounters, DerivedChars.ofBase, hp]

/-- **L5** (Dependency overrides Timestamp within the same `(stage, subStage)` bucket) (CR 6.3.3):
Effect B (`timestamp = 1`, adds subtype `.arrow` to objects with subtype `.attack`) depends on
Effect A (`timestamp = 10`, adds subtype `.attack` to `oid`). Despite B having an earlier timestamp,
dependency causes A to apply first so B sees `.attack` and also applies `.arrow`. -/
theorem dependency_overrides_timestamp :
    let o : Object := { kind := .token ⟨"T"⟩, owner := ⟨0⟩, controller := ⟨0⟩, timestamp := ⟨0⟩ }
    let face : CardFace := { name := "Test", types := [.action], subtypes := [] }
    let oid : ObjId := ⟨7⟩
    let effB : ContinuousEffect :=
      { id := 1, source := oid, controller := ⟨0⟩,
        target := .matching (reqSubtype := some .attack),
        op := .addSubtype .arrow, timestamp := ⟨1⟩ }
    let effA : ContinuousEffect :=
      { id := 2, source := oid, controller := ⟨0⟩,
        target := .obj oid,
        op := .addSubtype .attack, timestamp := ⟨10⟩ }
    Subtype.arrow ∈ (evalCharacteristics [effB, effA] o face oid).subtypes := by
  decide

/-- **L5** (Cyclic Dependency Timestamp Fallback) (CR 6.3.3c):
when two effects in the same `(stage, subStage)` bucket mutually depend on each other (each
removing the condition of the other), evaluation terminates via timestamp fallback and applies
the earlier-timestamp effect first. -/
theorem cycle_falls_back_to_timestamp :
    let o : Object := { kind := .token ⟨"T"⟩, owner := ⟨0⟩, controller := ⟨0⟩, timestamp := ⟨0⟩ }
    let face : CardFace := { name := "Alpha", types := [.action] }
    let oid : ObjId := ⟨7⟩
    let effEarly : ContinuousEffect :=
      { id := 1, source := oid, controller := ⟨0⟩,
        target := .matching (reqName := some "Alpha"),
        op := .setName "Beta", timestamp := ⟨2⟩ }
    let effLate : ContinuousEffect :=
      { id := 2, source := oid, controller := ⟨0⟩,
        target := .matching (reqName := some "Alpha"),
        op := .setName "Gamma", timestamp := ⟨5⟩ }
    (evalCharacteristics [effLate, effEarly] o face oid).name = "Beta" := by
  decide

/-- `expireEffects` removes every active effect with duration `dur` (CR 4.4.3, 7.7). -/
theorem expireEffects_removes_duration (s : GameState) (dur : Duration) :
    ∀ e ∈ (s.expireEffects dur).activeEffects, e.duration ≠ dur := by
  intro e he
  unfold GameState.expireEffects at he
  rw [List.mem_filter] at he
  have hne := he.2
  intro heq
  subst heq
  simp at hne

/-- `expireEffects` retains every active effect with a different duration `dur' ≠ dur`. -/
theorem expireEffects_keeps_other {s : GameState} {dur : Duration} {e : ContinuousEffect}
    (hmem : e ∈ s.activeEffects) (hne : e.duration ≠ dur) :
    e ∈ (s.expireEffects dur).activeEffects := by
  unfold GameState.expireEffects
  rw [List.mem_filter]
  exact ⟨hmem, by simp [hne]⟩

end Fab

end
