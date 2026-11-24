module

public import Fab.Engine.Step
public import Fab.Rules.Setup

/-!
# Engine invariants (M2b + M3)

Proves the core engine theorems over `step`, `advance`, `Legal`, and `legalActions` (roadmap.md):
- **I1**: `step_physIds` (physical card conservation)
- **I3**: `step_wf` and `step_ownerOk` (structural and ownership invariants)
- **I4**: `step_not_internal` and `Reachable.not_internal` (no internal engine errors)
- **I6**: `legal_of_step_ok` (completeness), `step_sound` (soundness), and `legalActions_iff`
  (constructive enumeration matches `Legal`)
- **I15**: `advance_mono` and `step_mono` (fuel monotonicity)
- `Reachable`: inductive reachability from any valid `GameState.initial`
-/

@[expose] public section

namespace Fab

/-- Helper: if a player zone holds an object in a `WF` state, that player is seated. -/
theorem player_lt_of_mem_zone {s : GameState} (hwf : s.WF) {p : PlayerId} {k : ZoneKind}
    {id : ObjId} (hmem : id ∈ s.zone (.player p k)) :
    p.n < s.playerCount := by
  have hin : (Zone.player p k).key ∈ s.zones := by
    unfold GameState.zone at hmem
    cases hg : s.zones[(Zone.player p k).key]? with
    | none =>
      rw [Std.ExtTreeMap.getD_eq_getD_getElem?, hg] at hmem
      simp at hmem
    | some _ =>
      exact Std.ExtTreeMap.mem_iff_isSome_getElem?.mpr (by rw [hg]; rfl)
  obtain ⟨z, hz, hzk⟩ := hwf.zones_valid _ hin
  have heq : z = Zone.player p k := Zone.key_inj hzk
  subst heq
  unfold allZones at hz
  simp only [List.mem_cons, List.mem_flatMap, List.mem_range, List.mem_map] at hz
  rcases hz with h | h | ⟨i, hi, k', _, hpeq⟩
  · cases h
  · cases h
  · simp only [Zone.player.injEq] at hpeq
    cases hpeq.1
    exact hi

/-- Helper: `loadoutEquipDest?` returning `some dst` implies `id` is in `p`'s inventory and
`dst` is an Arena zone of player `p`. -/
theorem loadoutEquipDest?_spec {s : GameState} {p : PlayerId} {id : ObjId} {dst : Zone}
    (h : loadoutEquipDest? s p id = some dst) :
    id ∈ s.zone (.player p .inventory) ∧
    ∃ k : ZoneKind, dst = .player p k ∧ k.isArena = true := by
  unfold loadoutEquipDest? at h
  split at h
  · rename_i hmem
    refine ⟨hmem, ?_⟩
    cases hc : s.cardDefOf? id with
    | none => simp only [hc] at h; cases h
    | some c =>
      simp only [hc] at h
      cases hs : c.equipSlot? with
      | some slot =>
        simp only [hs] at h
        cases slot
        · dsimp only at h
          split at h
          · simp only [Option.some.injEq] at h; subst h; exact ⟨.head, rfl, rfl⟩
          · cases h
        · dsimp only at h
          split at h
          · simp only [Option.some.injEq] at h; subst h; exact ⟨.chest, rfl, rfl⟩
          · cases h
        · dsimp only at h
          split at h
          · simp only [Option.some.injEq] at h; subst h; exact ⟨.arms, rfl, rfl⟩
          · cases h
        · dsimp only at h
          split at h
          · simp only [Option.some.injEq] at h; subst h; exact ⟨.legs, rfl, rfl⟩
          · cases h
      | none =>
        simp only [hs] at h
        split at h
        · split at h
          · simp only [Option.some.injEq] at h; subst h; exact ⟨.weapon, rfl, rfl⟩
          · cases h
        · split at h
          · split at h
            · simp only [Option.some.injEq] at h; subst h; exact ⟨.weapon, rfl, rfl⟩
            · cases h
          · cases h
  · cases h

/-- Helper: `loadoutCanAddDeck` implies `id` is in `p`'s inventory. -/
theorem mem_inventory_of_loadoutCanAddDeck {s : GameState} {p : PlayerId} {id : ObjId}
    (h : loadoutCanAddDeck s p id = true) :
    id ∈ s.zone (.player p .inventory) := by
  unfold loadoutCanAddDeck at h
  split at h
  · assumption
  · cases h

/-- Applying a legal frame answer preserves `WF`. -/
theorem applyFrame_wf {s s' : GameState} {a : Action} {es : List Event}
    (hwf : s.WF) (hl : LegalFrame s a) (h : applyFrame s a = some (s', es)) : s'.WF := by
  unfold applyFrame at h
  unfold LegalFrame at hl
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact GameState.WF.congr hwf rfl rfl rfl rfl
  · split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact GameState.WF.congr hwf rfl rfl rfl rfl
    · cases h
  · split at h
    · split at h
      · cases h
      · split at h
        · cases h
        · rename_i hm
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, -⟩ := h
          exact GameState.WF.congr (moveObj_wf hwf hm) rfl rfl rfl rfl
    · cases h
  · split at h
    · split at h
      · cases h
      · rename_i hm
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact GameState.WF.congr (moveObj_wf hwf hm) rfl rfl rfl rfl
    · cases h
  · split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact GameState.WF.congr hwf rfl rfl rfl rfl
    · cases h
  · rename_i z rest l hp ha hk
    rw [hp, ha, hk] at hl
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact GameState.WF.congr (GameState.wf_reorder hwf hl.1 hl.2) rfl rfl rfl rfl
  · split at h
    · dsimp only at h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact GameState.WF.congr hwf rfl rfl rfl rfl
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact GameState.WF.congr hwf rfl rfl rfl rfl
    · cases h
  · split at h
    · split at h
      · cases h
      · rename_i hm
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact GameState.WF.congr (moveObj_wf hwf hm) rfl rfl rfl rfl
    · cases h
  · split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact GameState.WF.congr hwf rfl rfl rfl rfl
    · cases h
  · split at h
    · split at h
      · cases h
      · rename_i hm
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact GameState.WF.congr (moveObj_wf hwf hm) rfl rfl rfl rfl
    · cases h
  · cases h

/-- Applying any legal `Action` preserves `WF`. -/
theorem applyAction_wf {s s' : GameState} {a : Action} {es : List Event}
    (hwf : s.WF) (hl : Legal s a) (h : applyAction s a = some (s', es)) : s'.WF := by
  unfold applyAction at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact GameState.WF.congr hwf rfl rfl rfl rfl
  · rename_i hnc
    rcases hl.2 with hlf | hlc
    · exact applyFrame_wf hwf hlf h
    · unfold LegalConcede at hlc
      cases ha : a.actor <;> cases hk : a.kind <;> simp [ha, hk] at hlc
      exact False.elim (hnc _ ha hk)

/-- One `microStep` preserves `WF`. -/
theorem microStep_wf {s s' : GameState} {es : List Event}
    (hwf : s.WF) (h : microStep s = some (s', es)) : s'.WF := by
  unfold microStep at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact GameState.WF.congr (revealAllLoadouts_wf hwf) rfl rfl rfl rfl
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact GameState.WF.congr hwf rfl rfl rfl rfl
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact GameState.WF.congr hwf rfl rfl rfl rfl
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact GameState.WF.congr (drawOne_wf hwf) rfl rfl rfl rfl
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact GameState.WF.congr hwf rfl rfl rfl rfl
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact GameState.WF.congr hwf rfl rfl rfl rfl
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact GameState.WF.congr hwf rfl rfl rfl rfl
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact GameState.WF.congr hwf rfl rfl rfl rfl
  · split at h <;>
      (simp only [Option.some.injEq, Prod.mk.injEq] at h
       obtain ⟨rfl, -⟩ := h
       exact GameState.WF.congr hwf rfl rfl rfl rfl)
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact GameState.WF.congr (untapPlayer_wf hwf _) rfl rfl rfl rfl
  · cases h

/-- `advance` preserves `WF`. -/
theorem advance_wf :
    ∀ (n : Nat) {s s' : GameState} {es es' : List Event}, s.WF →
      advance n s es = .ok (s', es') → s'.WF
  | 0, s, s', es, es', hwf, h => by
    unfold advance at h
    split at h
    · split at h
      · cases h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact hwf
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact hwf
  | n + 1, s, s', es, es', hwf, h => by
    unfold advance at h
    split at h
    · split at h
      · split at h
        · rename_i s1 es1 hm
          exact advance_wf n (microStep_wf hwf hm) h
        · cases h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact hwf
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact hwf

/-- **I3**: `step` preserves structural well-formedness `WF`. -/
theorem step_wf {fuel : Nat} {s s' : GameState} {a : Action} {es : List Event}
    (hwf : s.WF) (h : step fuel s a = .ok (s', es)) : s'.WF := by
  unfold step at h
  split at h
  · rename_i hl
    split at h
    · rename_i s1 es1 ha
      exact advance_wf fuel (applyAction_wf hwf hl ha) h
    · cases h
  · cases h

/-- Applying a legal frame answer preserves `OwnerOk`. -/
theorem applyFrame_ownerOk {s s' : GameState} {a : Action} {es : List Event}
    (hwf : s.WF) (hok : s.OwnerOk) (hl : LegalFrame s a) (h : applyFrame s a = some (s', es)) :
    s'.OwnerOk := by
  unfold applyFrame at h
  unfold LegalFrame at hl
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact GameState.OwnerOk.congr hok rfl rfl
  · split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact GameState.OwnerOk.congr hok rfl rfl
    · cases h
  · split at h
    · split at h
      · cases h
      · split at h
        · cases h
        · rename_i hm
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, -⟩ := h
          exact GameState.OwnerOk.congr (moveObj_ownerOk hwf hok hm) rfl rfl
    · cases h
  · split at h
    · split at h
      · cases h
      · rename_i hm
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact GameState.OwnerOk.congr (moveObj_ownerOk hwf hok hm) rfl rfl
    · cases h
  · split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact GameState.OwnerOk.congr hok rfl rfl
    · cases h
  · rename_i z rest l hp ha hk
    rw [hp, ha, hk] at hl
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact GameState.OwnerOk.congr (GameState.ownerOk_reorder hok hl.2) rfl rfl
  · split at h
    · dsimp only at h
      split at h <;>
        (simp only [Option.some.injEq, Prod.mk.injEq] at h
         obtain ⟨rfl, -⟩ := h
         exact GameState.OwnerOk.congr hok rfl rfl)
    · cases h
  · split at h
    · split at h
      · cases h
      · rename_i hm
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact GameState.OwnerOk.congr (moveObj_ownerOk hwf hok hm) rfl rfl
    · cases h
  · split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact GameState.OwnerOk.congr hok rfl rfl
    · cases h
  · split at h
    · split at h
      · cases h
      · rename_i hm
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact GameState.OwnerOk.congr (moveObj_ownerOk hwf hok hm) rfl rfl
    · cases h
  · cases h

/-- Applying any legal `Action` preserves `OwnerOk`. -/
theorem applyAction_ownerOk {s s' : GameState} {a : Action} {es : List Event}
    (hwf : s.WF) (hok : s.OwnerOk) (hl : Legal s a) (h : applyAction s a = some (s', es)) :
    s'.OwnerOk := by
  unfold applyAction at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact GameState.OwnerOk.congr hok rfl rfl
  · rename_i hnc
    rcases hl.2 with hlf | hlc
    · exact applyFrame_ownerOk hwf hok hlf h
    · unfold LegalConcede at hlc
      cases ha : a.actor <;> cases hk : a.kind <;> simp [ha, hk] at hlc
      exact False.elim (hnc _ ha hk)

/-- One `microStep` preserves `OwnerOk`. -/
theorem microStep_ownerOk {s s' : GameState} {es : List Event}
    (hwf : s.WF) (hok : s.OwnerOk) (h : microStep s = some (s', es)) : s'.OwnerOk := by
  unfold microStep at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact GameState.OwnerOk.congr (revealAllLoadouts_ownerOk hok) rfl rfl
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact GameState.OwnerOk.congr hok rfl rfl
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact GameState.OwnerOk.congr hok rfl rfl
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact GameState.OwnerOk.congr (drawOne_ownerOk hwf hok) rfl rfl
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact GameState.OwnerOk.congr hok rfl rfl
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact GameState.OwnerOk.congr hok rfl rfl
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact GameState.OwnerOk.congr hok rfl rfl
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact GameState.OwnerOk.congr hok rfl rfl
  · split at h <;>
      (simp only [Option.some.injEq, Prod.mk.injEq] at h
       obtain ⟨rfl, -⟩ := h
       exact GameState.OwnerOk.congr hok rfl rfl)
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact GameState.OwnerOk.congr (untapPlayer_ownerOk hok _) rfl rfl
  · cases h

/-- `advance` preserves `OwnerOk`. -/
theorem advance_ownerOk :
    ∀ (n : Nat) {s s' : GameState} {es es' : List Event}, s.WF → s.OwnerOk →
      advance n s es = .ok (s', es') → s'.OwnerOk
  | 0, s, s', es, es', _, hok, h => by
    unfold advance at h
    split at h
    · split at h
      · cases h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact hok
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact hok
  | n + 1, s, s', es, es', hwf, hok, h => by
    unfold advance at h
    split at h
    · split at h
      · split at h
        · rename_i s1 es1 hm
          exact advance_ownerOk n (microStep_wf hwf hm) (microStep_ownerOk hwf hok hm) h
        · cases h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact hok
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact hok

/-- `step` preserves `OwnerOk`. -/
theorem step_ownerOk {fuel : Nat} {s s' : GameState} {a : Action} {es : List Event}
    (hwf : s.WF) (hok : s.OwnerOk) (h : step fuel s a = .ok (s', es)) : s'.OwnerOk := by
  unfold step at h
  split at h
  · rename_i hl
    split at h
    · rename_i s1 es1 ha
      exact advance_ownerOk fuel (applyAction_wf hwf hl ha) (applyAction_ownerOk hwf hok hl ha) h
    · cases h
  · cases h

/-- Applying a legal frame answer preserves `physIds` up to permutation. -/
theorem applyFrame_physIds {s s' : GameState} {a : Action} {es : List Event}
    (hwf : s.WF) (hl : LegalFrame s a) (h : applyFrame s a = some (s', es)) :
    s'.physIds.Perm s.physIds := by
  unfold applyFrame at h
  unfold LegalFrame at hl
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact List.Perm.refl _
  · split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact List.Perm.refl _
    · cases h
  · split at h
    · split at h
      · cases h
      · split at h
        · cases h
        · rename_i hm
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, -⟩ := h
          have hp := moveObj_physIds hwf hm
          exact hp
    · cases h
  · split at h
    · split at h
      · cases h
      · rename_i hm
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        have hp := moveObj_physIds hwf hm
        exact hp
    · cases h
  · split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact List.Perm.refl _
    · cases h
  · rename_i z rest l hp ha hk
    rw [hp, ha, hk] at hl
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact GameState.physIds_reorder hl.1 hl.2
  · split at h
    · dsimp only at h
      split at h <;>
        (simp only [Option.some.injEq, Prod.mk.injEq] at h
         obtain ⟨rfl, -⟩ := h
         exact List.Perm.refl _)
    · cases h
  · split at h
    · split at h
      · cases h
      · rename_i hm
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        have hp := moveObj_physIds hwf hm
        exact hp
    · cases h
  · split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact List.Perm.refl _
    · cases h
  · split at h
    · split at h
      · cases h
      · rename_i hm
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        have hp := moveObj_physIds hwf hm
        exact hp
    · cases h
  · cases h

/-- Applying any legal `Action` preserves `physIds` up to permutation. -/
theorem applyAction_physIds {s s' : GameState} {a : Action} {es : List Event}
    (hwf : s.WF) (hl : Legal s a) (h : applyAction s a = some (s', es)) :
    s'.physIds.Perm s.physIds := by
  unfold applyAction at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact List.Perm.refl _
  · rename_i hnc
    rcases hl.2 with hlf | hlc
    · exact applyFrame_physIds hwf hlf h
    · unfold LegalConcede at hlc
      cases ha : a.actor <;> cases hk : a.kind <;> simp [ha, hk] at hlc
      exact False.elim (hnc _ ha hk)

/-- One `microStep` preserves `physIds` up to permutation. -/
theorem microStep_physIds {s s' : GameState} {es : List Event}
    (hwf : s.WF) (h : microStep s = some (s', es)) :
    s'.physIds.Perm s.physIds := by
  unfold microStep at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    change (revealAllLoadouts s).physIds.Perm s.physIds
    rw [revealAllLoadouts_physIds]
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact List.Perm.refl _
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact List.Perm.refl _
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact drawOne_physIds hwf
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact List.Perm.refl _
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact List.Perm.refl _
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact List.Perm.refl _
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact List.Perm.refl _
  · split at h <;>
      (simp only [Option.some.injEq, Prod.mk.injEq] at h
       obtain ⟨rfl, -⟩ := h
       exact List.Perm.refl _)
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    change (untapPlayer s _).physIds.Perm s.physIds
    rw [untapPlayer_physIds]
  · cases h

/-- `advance` preserves `physIds` up to permutation. -/
theorem advance_physIds :
    ∀ (n : Nat) {s s' : GameState} {es es' : List Event}, s.WF →
      advance n s es = .ok (s', es') → s'.physIds.Perm s.physIds
  | 0, s, s', es, es', _, h => by
    unfold advance at h
    split at h
    · split at h
      · cases h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact List.Perm.refl _
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact List.Perm.refl _
  | n + 1, s, s', es, es', hwf, h => by
    unfold advance at h
    split at h
    · split at h
      · split at h
        · rename_i s1 es1 hm
          exact (advance_physIds n (microStep_wf hwf hm) h).trans (microStep_physIds hwf hm)
        · cases h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact List.Perm.refl _
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact List.Perm.refl _

/-- **I1**: `step` preserves the multiset of all physical cards across the entire game. -/
theorem step_physIds {fuel : Nat} {s s' : GameState} {a : Action} {es : List Event}
    (hwf : s.WF) (h : step fuel s a = .ok (s', es)) :
    s'.physIds.Perm s.physIds := by
  unfold step at h
  split at h
  · rename_i hl
    split at h
    · rename_i s1 es1 ha
      exact (advance_physIds fuel (applyAction_wf hwf hl ha) h).trans
        (applyAction_physIds hwf hl ha)
    · cases h
  · cases h

/-- **I6** (completeness): `step` accepts an action only if it satisfies `Legal`. -/
theorem legal_of_step_ok {fuel : Nat} {s : GameState} {a : Action} {r : GameState × List Event}
    (h : step fuel s a = .ok r) : Legal s a := by
  unfold step at h
  split at h
  · assumption
  · cases h

/-- Illegal actions are always rejected with `.error .illegal`. -/
theorem step_illegal {fuel : Nat} {s : GameState} {a : Action} (h : ¬ Legal s a) :
    step fuel s a = .error .illegal := by
  simp [step, h]

/-- **I15** (automatic work): increasing `fuel` preserves a successful `advance` result. -/
theorem advance_mono :
    ∀ (n : Nat) {m : Nat} {s : GameState} {es : List Event} {r : GameState × List Event},
      advance n s es = .ok r → n ≤ m → advance m s es = .ok r
  | 0, m, s, es, r, h, _ => by
    cases m with
    | zero => exact h
    | succ k =>
      unfold advance at h ⊢
      split at h
      · split at h
        · cases h
        · rename_i hf
          simpa [hf] using h
      · exact h
  | n + 1, m, s, es, r, h, hnm => by
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    unfold advance at h ⊢
    split at h
    · split at h
      · rename_i hf
        simp only [hf, ite_true] at h ⊢
        split at h
        · exact advance_mono n h (by omega)
        · cases h
      · rename_i hf
        simpa [hf] using h
    · exact h

/-- **I15**: increasing `fuel` preserves a successful `step` result. -/
theorem step_mono {n m : Nat} {s : GameState} {a : Action} {r : GameState × List Event}
    (h : step n s a = .ok r) (hnm : n ≤ m) : step m s a = .ok r := by
  by_cases hl : Legal s a
  · cases ha : applyAction s a with
    | none => simp [step, hl, ha] at h
    | some r1 =>
      simp only [step, hl, ha, ite_true] at h ⊢
      exact advance_mono n h hnm
  · simp [step, hl] at h

/-- **I6** (frame enumeration): `legalFrameActions` matches `LegalFrame` for player actions. -/
theorem legalFrameActions_iff (s : GameState) (a : Action) :
    a ∈ legalFrameActions s ↔ LegalFrame s a ∧ a.actor.isPlayer = true := by
  obtain ⟨actor, kind⟩ := a
  unfold legalFrameActions LegalFrame
  rcases hp : s.pending with _ | ⟨f, rest⟩
  · cases kind <;> cases actor <;> simp [Actor.isPlayer]
  · cases f with
    | chanceFirstPlayer =>
      cases actor <;> cases kind <;> simp [Actor.isPlayer]
    | chooseFirstPlayer chooser =>
      cases actor <;> cases kind <;> simp [Actor.isPlayer, mem_allPlayers_iff]
      grind
    | chooseLoadout p =>
      cases actor with
      | player q =>
        cases kind with
        | loadoutEquip id =>
          simp only [Actor.isPlayer, and_true, List.mem_append, List.mem_map, List.mem_filter,
            Action.mk.injEq, Actor.player.injEq, ActionKind.loadoutEquip.injEq]
          constructor
          · rintro ((⟨x, ⟨_, hdest⟩, rfl, rfl⟩ | ⟨_, _, _, hcontra⟩) | hdone)
            · exact ⟨rfl, hdest⟩
            · cases hcontra
            · split at hdone <;> simp at hdone
          · rintro ⟨rfl, hdest⟩
            left; left
            cases hd : loadoutEquipDest? s q id with
            | none => rw [hd] at hdest; simp at hdest
            | some dst =>
              exact ⟨id, ⟨(loadoutEquipDest?_spec hd).1, hdest⟩, rfl, rfl⟩
        | loadoutToDeck id =>
          simp only [Actor.isPlayer, and_true, List.mem_append, List.mem_map, List.mem_filter,
            Action.mk.injEq, Actor.player.injEq, ActionKind.loadoutToDeck.injEq]
          constructor
          · rintro ((⟨_, _, _, hcontra⟩ | ⟨x, ⟨_, hcan⟩, rfl, rfl⟩) | hdone)
            · cases hcontra
            · exact ⟨rfl, hcan⟩
            · split at hdone <;> simp at hdone
          · rintro ⟨rfl, hcan⟩
            left; right
            exact ⟨id, ⟨mem_inventory_of_loadoutCanAddDeck hcan, hcan⟩, rfl, rfl⟩
        | loadoutDone =>
          simp only [Actor.isPlayer, and_true, List.mem_append, List.mem_map, List.mem_filter,
            Action.mk.injEq, Actor.player.injEq]
          constructor
          · rintro ((⟨_, _, _, hcontra⟩ | ⟨_, _, _, hcontra⟩) | hdone)
            · cases hcontra
            · cases hcontra
            · split at hdone
              · rename_i hfin
                simp only [List.mem_singleton, Action.mk.injEq, Actor.player.injEq,
                  and_true] at hdone
                exact ⟨hdone, hfin⟩
              · simp at hdone
          · rintro ⟨rfl, hfin⟩
            right
            simp [hfin]
        | chanceFirstChooser _ | pickFirstPlayer _ | shuffleOrder _ | pass | arsenalPut _
        | arsenalSkip | pitchReturnPick _ | concede =>
          simp only [Actor.isPlayer, and_true, List.mem_append, List.mem_map, List.mem_filter,
            Action.mk.injEq, Actor.player.injEq, iff_false]
          rintro ((⟨_, _, _, hcontra⟩ | ⟨_, _, _, hcontra⟩) | hdone)
          · cases hcontra
          · cases hcontra
          · split at hdone <;> simp at hdone
      | chance | clock | judge =>
        cases kind <;> simp only [Actor.isPlayer, Bool.false_eq_true, and_false, iff_false,
          List.mem_append, List.mem_map, List.mem_filter, Action.mk.injEq]
        all_goals
          rintro ((⟨_, _, hcontra, _⟩ | ⟨_, _, hcontra, _⟩) | hdone)
          · cases hcontra
          · cases hcontra
          · split at hdone <;> simp at hdone
    | priority p _ =>
      cases actor <;> cases kind <;> simp [Actor.isPlayer]
    | chooseArsenal tp =>
      cases actor with
      | player q =>
        cases kind with
        | arsenalPut id =>
          simp only [Actor.isPlayer, and_true, List.mem_append, List.mem_singleton,
            Action.mk.injEq, Actor.player.injEq]
          constructor
          · rintro (hput | ⟨_, hcontra⟩)
            · split at hput
              · rename_i hemp
                simp only [List.mem_map, Action.mk.injEq, Actor.player.injEq,
                  ActionKind.arsenalPut.injEq] at hput
                obtain ⟨x, hx, rfl, rfl⟩ := hput
                exact ⟨rfl, hemp, hx⟩
              · simp at hput
            · cases hcontra
          · rintro ⟨rfl, hemp, hx⟩
            left
            simp only [hemp, ↓reduceIte, List.mem_map, Action.mk.injEq,
              ActionKind.arsenalPut.injEq]
            exact ⟨id, hx, trivial, rfl⟩
        | arsenalSkip =>
          simp only [Actor.isPlayer, and_true, List.mem_append, List.mem_singleton,
            Action.mk.injEq, Actor.player.injEq, and_true]
          constructor
          · rintro (hput | hskip)
            · split at hput
              · simp only [List.mem_map, Action.mk.injEq] at hput
                obtain ⟨_, _, _, hcontra⟩ := hput
                cases hcontra
              · simp at hput
            · exact hskip
          · intro hq
            right
            exact hq
        | chanceFirstChooser _ | pickFirstPlayer _ | loadoutEquip _ | loadoutToDeck _
        | loadoutDone | shuffleOrder _ | pass | pitchReturnPick _ | concede =>
          simp only [Actor.isPlayer, and_true, List.mem_append, List.mem_singleton,
            Action.mk.injEq, iff_false]
          rintro (hput | ⟨_, hcontra⟩)
          · split at hput
            · simp only [List.mem_map, Action.mk.injEq] at hput
              obtain ⟨_, _, _, hcontra⟩ := hput
              cases hcontra
            · simp at hput
          · cases hcontra
      | chance | clock | judge =>
        cases kind <;> simp only [Actor.isPlayer, Bool.false_eq_true, and_false, iff_false,
          List.mem_append, List.mem_singleton, Action.mk.injEq]
        all_goals
          rintro (hput | ⟨hcontra, _⟩)
          · split at hput
            · simp only [List.mem_map, Action.mk.injEq] at hput
              obtain ⟨_, _, hcontra, _⟩ := hput
              cases hcontra
            · simp at hput
          · cases hcontra
    | choosePitchOrder p =>
      cases actor <;> cases kind <;> simp [Actor.isPlayer]
      grind
    | revealLoadouts | chanceShuffle _ | openingDraws | draw _ _ | beginTurn
    | startPhaseWork _ | actionPhaseStart _ | endPhaseStart _ | returnPitch _
    | endTurnCleanup _ =>
      cases actor <;> cases kind <;> simp [Actor.isPlayer]

/-- **I6** (concession enumeration): `concedeActions` matches `LegalConcede` for player actions. -/
theorem concedeActions_iff (s : GameState) (a : Action) :
    a ∈ concedeActions s ↔ LegalConcede s a ∧ a.actor.isPlayer = true := by
  obtain ⟨actor, kind⟩ := a
  unfold concedeActions LegalConcede
  cases kind <;> cases actor <;> by_cases h : s.playerCount = 2 <;>
    simp [Actor.isPlayer, h, allPlayers]
  all_goals grind

/-- **I6** (enumeration): `legalActions` enumerates exactly the legal player actions. -/
theorem legalActions_iff (s : GameState) (a : Action) :
    a ∈ legalActions s ↔ Legal s a ∧ a.actor.isPlayer = true := by
  unfold legalActions Legal
  by_cases h : s.result = none
  · simp only [h, ite_true, true_and, List.mem_append]
    rw [legalFrameActions_iff, concedeActions_iff]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨Or.inl h1, h2⟩
      · exact ⟨Or.inr h1, h2⟩
    · rintro ⟨h1 | h1, h2⟩
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr ⟨h1, h2⟩
  · simp [h]

/-- Helper: `moveObj` always succeeds when `id` is in a valid `src`, `dst` is valid, and
`src ≠ Zone.normalize o.owner dst`. -/
theorem moveObj_isSome {s : GameState} (hwf : s.WF) {id : ObjId} {src dst : Zone} {pos : Pos}
    {fd : Bool} (hsrc : src ∈ allZones s.playerCount) (hid : id ∈ s.zone src)
    (hnorm_valid : ∀ o, s.obj? id = some o →
      (Zone.normalize o.owner dst).Valid s.playerCount ∧ src ≠ Zone.normalize o.owner dst) :
    (moveObj s id dst pos fd).isSome = true := by
  have hloc : s.locate id = some src := GameState.locate_eq hwf hsrc hid
  have hin : id.n ∈ s.objects := hwf.table_of_zone id (GameState.mem_zoneIds hsrc hid)
  obtain ⟨o, ho⟩ : ∃ o, s.obj? id = some o := by
    unfold GameState.obj?
    cases hg : s.objects[id.n]? with
    | none =>
      exfalso
      have := Std.ExtTreeMap.mem_iff_isSome_getElem?.mp hin
      rw [hg] at this; simp at this
    | some o => exact ⟨o, rfl⟩
  obtain ⟨hval, hne⟩ := hnorm_valid o ho
  unfold moveObj
  rw [hloc, ho]
  simp only [hne, false_or, hval, not_true_eq_false, ↓reduceIte]
  split <;> rfl

/-- Under `WF` and `OwnerOk`, every legal frame action applies without failing. -/
theorem applyFrame_isSome {s : GameState} {a : Action}
    (hwf : s.WF) (hok : s.OwnerOk) (hlf : LegalFrame s a) :
    (applyFrame s a).isSome = true := by
  obtain ⟨actor, kind⟩ := a
  unfold applyFrame
  unfold LegalFrame at hlf
  cases hp : s.pending with
  | nil => rw [hp] at hlf; exact False.elim hlf
  | cons f rest =>
    rw [hp] at hlf
    cases f with
    | chanceFirstPlayer =>
      cases actor <;> cases kind <;> simp at hlf ⊢
    | chooseFirstPlayer chooser =>
      cases actor <;> cases kind <;> simp at hlf ⊢
      exact hlf.1
    | chooseLoadout p =>
      cases actor with
      | player q =>
        cases kind with
        | loadoutEquip id =>
          obtain ⟨rfl, hsome⟩ := hlf
          simp only [↓reduceIte]
          cases hd : loadoutEquipDest? s q id with
          | none => rw [hd] at hsome; simp at hsome
          | some dst =>
            dsimp only
            obtain ⟨hmem_inv, k, rfl, hk_ar⟩ := loadoutEquipDest?_spec hd
            have hq : q.n < s.playerCount := player_lt_of_mem_zone hwf hmem_inv
            have hm : (moveObj s id (.player q k) .top true).isSome = true := by
              apply moveObj_isSome hwf (Zone.valid_player hq .inventory) hmem_inv
              intro o _
              have hnorm : Zone.normalize o.owner (.player q k) = .player q k := by
                simp [Zone.normalize, hk_ar]
              rw [hnorm]
              refine ⟨Zone.valid_player hq k, ?_⟩
              intro heq
              cases heq
              simp [ZoneKind.isArena] at hk_ar
            cases hm' : moveObj s id (.player q k) .top true with
            | none => rw [hm'] at hm; simp at hm
            | some _ => rfl
        | loadoutToDeck id =>
          obtain ⟨rfl, hcan⟩ := hlf
          simp only [hcan, and_self, ↓reduceIte]
          have hmem_inv : id ∈ s.zone (.player q .inventory) :=
            mem_inventory_of_loadoutCanAddDeck hcan
          have hq : q.n < s.playerCount := player_lt_of_mem_zone hwf hmem_inv
          have hm : (moveObj s id (.player q .deck) .bottom false).isSome = true := by
            apply moveObj_isSome hwf (Zone.valid_player hq .inventory) hmem_inv
            intro o ho
            have hown : o.owner = q := hok.owner q .inventory rfl id hmem_inv o ho
            have hnorm : Zone.normalize o.owner (.player q .deck) = .player q .deck := by
              simp [Zone.normalize, ZoneKind.isArena, hown]
            rw [hnorm]
            exact ⟨Zone.valid_player hq .deck, by intro heq; cases heq⟩
          cases hm' : moveObj s id (.player q .deck) .bottom false with
          | none => rw [hm'] at hm; simp at hm
          | some _ => rfl
        | loadoutDone =>
          obtain ⟨rfl, hfin⟩ := hlf
          simp [hfin]
        | chanceFirstChooser _ | pickFirstPlayer _ | shuffleOrder _ | pass | arsenalPut _
        | arsenalSkip | pitchReturnPick _ | concede =>
          exact False.elim hlf
      | chance | clock | judge =>
        cases kind <;> exact False.elim hlf
    | chanceShuffle z =>
      cases actor <;> cases kind <;> simp at hlf ⊢
    | priority p passCount =>
      cases actor <;> cases kind <;> simp at hlf ⊢
      subst hlf
      simp only [↓reduceIte]
      split <;> rfl
    | chooseArsenal tp =>
      cases actor with
      | player q =>
        cases kind with
        | arsenalPut id =>
          obtain ⟨rfl, hemp, hmem_hand⟩ := hlf
          simp only [hemp, hmem_hand, and_self, ↓reduceIte]
          have hq : q.n < s.playerCount := player_lt_of_mem_zone hwf hmem_hand
          have hm : (moveObj s id (.player q .arsenal) .top true).isSome = true := by
            apply moveObj_isSome hwf (Zone.valid_player hq .hand) hmem_hand
            intro o ho
            have hown : o.owner = q := hok.owner q .hand rfl id hmem_hand o ho
            have hnorm : Zone.normalize o.owner (.player q .arsenal) = .player q .arsenal := by
              simp [Zone.normalize, ZoneKind.isArena, hown]
            rw [hnorm]
            exact ⟨Zone.valid_player hq .arsenal, by intro heq; cases heq⟩
          cases hm' : moveObj s id (.player q .arsenal) .top true with
          | none => rw [hm'] at hm; simp at hm
          | some _ => rfl
        | arsenalSkip =>
          subst hlf
          simp
        | chanceFirstChooser _ | pickFirstPlayer _ | loadoutEquip _ | loadoutToDeck _
        | loadoutDone | shuffleOrder _ | pass | pitchReturnPick _ | concede =>
          exact False.elim hlf
      | chance | clock | judge =>
        cases kind <;> exact False.elim hlf
    | choosePitchOrder p =>
      cases actor with
      | player q =>
        cases kind with
        | pitchReturnPick id =>
          obtain ⟨rfl, hmem_pitch⟩ := hlf
          simp only [hmem_pitch, and_self, ↓reduceIte]
          have hq : q.n < s.playerCount := player_lt_of_mem_zone hwf hmem_pitch
          have hm : (moveObj s id (.player q .deck) .bottom false).isSome = true := by
            apply moveObj_isSome hwf (Zone.valid_player hq .pitch) hmem_pitch
            intro o ho
            have hown : o.owner = q := hok.owner q .pitch rfl id hmem_pitch o ho
            have hnorm : Zone.normalize o.owner (.player q .deck) = .player q .deck := by
              simp [Zone.normalize, ZoneKind.isArena, hown]
            rw [hnorm]
            exact ⟨Zone.valid_player hq .deck, by intro heq; cases heq⟩
          cases hm' : moveObj s id (.player q .deck) .bottom false with
          | none => rw [hm'] at hm; simp at hm
          | some _ => rfl
        | chanceFirstChooser _ | pickFirstPlayer _ | loadoutEquip _ | loadoutToDeck _
        | loadoutDone | shuffleOrder _ | pass | arsenalPut _ | arsenalSkip | concede =>
          exact False.elim hlf
      | chance | clock | judge =>
        cases kind <;> exact False.elim hlf
    | revealLoadouts | openingDraws | draw _ _ | beginTurn | startPhaseWork _
    | actionPhaseStart _ | endPhaseStart _ | returnPitch _ | endTurnCleanup _ =>
      cases actor <;> cases kind <;> exact False.elim hlf

/-- Under `WF` and `OwnerOk`, every legal action applies without failing. -/
theorem applyAction_isSome {s : GameState} {a : Action}
    (hwf : s.WF) (hok : s.OwnerOk) (hl : Legal s a) :
    (applyAction s a).isSome = true := by
  unfold applyAction
  split
  · rfl
  · rename_i hnc
    rcases hl.2 with hlf | hlc
    · exact applyFrame_isSome hwf hok hlf
    · unfold LegalConcede at hlc
      cases ha : a.actor <;> cases hk : a.kind <;> simp [ha, hk] at hlc
      exact False.elim (hnc _ ha hk)

/-- Every work frame on top of `s.pending` succeeds under `microStep`. -/
theorem microStep_isSome {s : GameState} {f : Frame} {rest : List Frame}
    (hp : s.pending = f :: rest) (hw : f.isWork = true) :
    (microStep s).isSome = true := by
  unfold microStep
  rw [hp]
  cases f with
  | revealLoadouts => rfl
  | openingDraws => rfl
  | draw p n => cases n <;> rfl
  | beginTurn => rfl
  | startPhaseWork _ => rfl
  | actionPhaseStart _ => rfl
  | endPhaseStart _ => rfl
  | returnPitch _ => dsimp only; split <;> rfl
  | endTurnCleanup _ => rfl
  | _ => simp [Frame.isWork] at hw

/-- `advance` never returns `.error (.internal _)` on any state. -/
theorem advance_not_internal :
    ∀ (n : Nat) (s : GameState) (es : List Event) (e : RuleError),
      advance n s es = .error e → e = .fuelExhausted
  | 0, s, es, e, h => by
    unfold advance at h
    split at h
    · split at h
      · simp only [Except.error.injEq] at h; exact h.symm
      · cases h
    · cases h
  | n + 1, s, es, e, h => by
    unfold advance at h
    split at h
    · rename_i f rest hp
      split at h
      · rename_i hw
        have hm := microStep_isSome hp hw
        cases hm' : microStep s with
        | none => rw [hm'] at hm; simp at hm
        | some res =>
          obtain ⟨s', es'⟩ := res
          rw [hm'] at h
          exact advance_not_internal n s' (es ++ es') e h
      · cases h
    · cases h

/-- **I6** (soundness): under `WF` and `OwnerOk`, a legal action never fails for any reason
other than `fuelExhausted`. -/
theorem step_sound {fuel : Nat} {s : GameState} {a : Action} {e : RuleError}
    (hwf : s.WF) (hok : s.OwnerOk) (hl : Legal s a) (h : step fuel s a = .error e) :
    e = .fuelExhausted := by
  unfold step at h
  simp only [hl, ↓reduceIte] at h
  have ha := applyAction_isSome hwf hok hl
  cases ha' : applyAction s a with
  | none => rw [ha'] at ha; simp at ha
  | some res =>
    obtain ⟨s1, es1⟩ := res
    rw [ha'] at h
    exact advance_not_internal fuel s1 es1 e h

/-- **I4**: under `WF` and `OwnerOk`, `step` never returns `RuleError.internal`. -/
theorem step_not_internal {fuel : Nat} {s : GameState} {a : Action} {msg : String}
    (hwf : s.WF) (hok : s.OwnerOk) :
    step fuel s a ≠ .error (.internal msg) := by
  intro h
  by_cases hl : Legal s a
  · have := step_sound hwf hok hl h
    cases this
  · rw [step_illegal hl] at h
    cases h

/-- Reachable game states: any valid initial state, closed under successful `step` transitions
(independent of `fuel` choice by I15: design.md §8). -/
inductive Reachable : GameState → Prop where
  /-- Any state produced by `GameState.initial` is reachable. -/
  | initial {cfg : GameConfig} {db : CardDB} {decks : List DeckList} {s : GameState} :
      GameState.initial cfg db decks = some s → Reachable s
  /-- Any state reached by a successful `step` from a reachable state is reachable. -/
  | step {s s' : GameState} {fuel : Nat} {a : Action} {es : List Event} :
      Reachable s → Fab.step fuel s a = .ok (s', es) → Reachable s'

/-- Every reachable state satisfies `WF` and `OwnerOk` (I3). -/
theorem Reachable.inv {s : GameState} (hr : Reachable s) : s.WF ∧ s.OwnerOk := by
  induction hr with
  | initial h => exact GameState.initial_inv h
  | step _ hstep ih => exact ⟨step_wf ih.1 hstep, step_ownerOk ih.1 ih.2 hstep⟩

/-- **I4** (global): no reachable state can ever trigger an internal engine error. -/
theorem Reachable.not_internal {s : GameState} (hr : Reachable s) (fuel : Nat) (a : Action)
    (msg : String) :
    Fab.step fuel s a ≠ .error (.internal msg) :=
  step_not_internal hr.inv.1 hr.inv.2

end Fab

end
