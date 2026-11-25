module

public import Fab.Engine.Step
public import Fab.Rules.Setup

/-!
# Engine invariants (M2b + M3 + M4)

Proves the core engine theorems over `step`, `advance`, `Legal`, and `legalActions` (roadmap.md):
- **I1**: `step_physIds` (physical card conservation)
- **I3**: `step_wf`, `step_ownerOk`, `step_rollbackOk` (structural, ownership, and rollback invariants)
- **I4**: `step_not_internal` and `Reachable.not_internal` (no internal engine errors)
- **I6**: `legal_of_step_ok` (completeness), `step_sound` (soundness), and `legalActions_iff`
  (constructive enumeration matches `Legal`)
- **I15**: `advance_mono` and `step_mono` (fuel monotonicity)
- `Reachable`: inductive reachability from any valid `GameState.initial`
-/

@[expose] public section

namespace Fab

/-- Combined invariant preservation bundle for a single transition `s → s'`. -/
structure StepPreserves (s s' : GameState) : Prop where
  /-- Structural well-formedness is preserved (I3). -/
  wf : s'.WF
  /-- Non-Arena ownership is preserved. -/
  ownerOk : s'.OwnerOk
  /-- Rollback snapshot invariant is preserved. -/
  rollbackOk : s'.RollbackOk
  /-- Multiset of physical cards is preserved (I1). -/
  physIds : s'.physIds.Perm s.physIds
  /-- Game configuration is immutable. -/
  config : s'.config = s.config

/-- Reflexivity of `StepPreserves` for any valid state. -/
theorem StepPreserves.refl {s : GameState} (hwf : s.WF) (hok : s.OwnerOk) (hrb : s.RollbackOk) :
    StepPreserves s s :=
  ⟨hwf, hok, hrb, List.Perm.refl _, rfl⟩

/-- Transitivity of `StepPreserves`. -/
theorem StepPreserves.trans {s1 s2 s3 : GameState}
    (h12 : StepPreserves s1 s2) (h23 : StepPreserves s2 s3) :
    StepPreserves s1 s3 :=
  ⟨h23.wf, h23.ownerOk, h23.rollbackOk, h23.physIds.trans h12.physIds, h23.config.trans h12.config⟩

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

/-- Helper: `canAttackWithWeapon` implies `wid` is in `p`'s weapon zone. -/
theorem mem_weapon_of_canAttackWithWeapon {s : GameState} {p : PlayerId} {wid : ObjId}
    (h : canAttackWithWeapon s p wid = true) :
    wid ∈ s.zone (.player p .weapon) := by
  unfold canAttackWithWeapon at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.2

/-- Helper: `canDefendWith` implies `id` is in `defendCandidateIds s p`. -/
theorem mem_defendCandidates_of_canDefendWith {s : GameState} {link : ChainLink}
    {p : PlayerId} {id : ObjId} (h : canDefendWith s link p id = true) :
    id ∈ defendCandidateIds s p := by
  unfold canDefendWith at h
  split at h
  · cases h
  · dsimp only at h
    split at h
    · cases h
    · rename_i hnot
      simp only [Bool.not_eq_true', Bool.or_eq_false_iff, not_and,
        Bool.not_eq_false] at hnot
      unfold defendCandidateIds
      rw [List.mem_append]
      by_cases hh : id ∈ s.zone (.player p .hand)
      · exact Or.inl hh
      · right
        have hfalse : decide (id ∈ s.zone (.player p .hand)) = false := by simp [hh]
        have heq := hnot hfalse
        simpa [decide_eq_true_eq] using heq

/-- Helper: `canPlayCard` implies `id` is in `p`'s hand or arsenal. -/
theorem mem_hand_or_arsenal_of_canPlayCard {s : GameState} {p : PlayerId} {id : ObjId}
    (h : canPlayCard s p id = true) :
    id ∈ s.zone (.player p .hand) ∨ id ∈ s.zone (.player p .arsenal) := by
  unfold canPlayCard at h
  dsimp only at h
  split at h
  · rename_i hor
    simpa [Bool.or_eq_true, decide_eq_true_eq] using hor
  · cases h

/-- Helper: `canPitchCard` implies `id` is in `p`'s hand. -/
theorem mem_hand_of_canPitchCard {s : GameState} {p : PlayerId} {id : ObjId}
    (h : canPitchCard s p id = true) :
    id ∈ s.zone (.player p .hand) := by
  unfold canPitchCard at h
  split at h
  · assumption
  · cases h

/-- Helper: `rollbackPlay` preserves `StepPreserves`. -/
theorem rollbackPlay_preserves {s : GameState} (hwf : s.WF) (hok : s.OwnerOk) (hrb : s.RollbackOk)
    (fallback : List Frame) :
    StepPreserves s (rollbackPlay s fallback) := by
  unfold rollbackPlay
  cases h : s.playRollback with
  | none =>
    dsimp only
    exact ⟨GameState.WF.congr hwf rfl rfl rfl rfl,
           GameState.OwnerOk.congr hok rfl rfl,
           GameState.RollbackOk.of_none rfl,
           List.Perm.refl _, rfl⟩
  | some snap =>
    dsimp only
    obtain ⟨hwf', hok', hperm⟩ := hrb snap h
    exact ⟨hwf', hok', GameState.RollbackOk.of_none rfl, hperm, rfl⟩

/-- Helper: moving an element to the back of a list produces a permutation. -/
theorem erase_append_singleton_perm {α : Type} [BEq α] [LawfulBEq α] {l : List α} {x : α}
    (h : x ∈ l) :
    (l.erase x ++ [x]).Perm l := by
  have h1 : (l.erase x ++ [x]).Perm (x :: l.erase x) := by
    have hc := List.perm_append_comm (l₁ := l.erase x) (l₂ := [x])
    simpa only [List.singleton_append] using hc
  exact h1.trans (List.perm_cons_erase h).symm

/-- Helper: restoring `s.snapshot` into any state with the same `config` yields `s.physIds`. -/
theorem restore_snapshot_physIds (s s1 : GameState) (hc : s1.config = s.config) :
    (s1.restore s.snapshot).physIds = s.physIds := by
  unfold GameState.physIds GameState.zoneIds GameState.playerCount GameState.restore
    GameState.snapshot GameState.zone GameState.obj?
  rw [hc]

/-- Helper: `spendAssetCost` preserves `StepPreserves` (only updates `pools`). -/
theorem spendAssetCost_preserves {s s' : GameState} {p : PlayerId} {cost : AssetCost}
    (hwf : s.WF) (hok : s.OwnerOk) (hrb : s.RollbackOk)
    (h : spendAssetCost s p cost = some s') :
    StepPreserves s s' ∧ s'.playRollback = s.playRollback := by
  unfold spendAssetCost at h
  dsimp only at h
  cases hs : (s.poolOf p).spend cost (cost.resources - (s.poolOf p).resources) with
  | none => rw [hs] at h; cases h
  | some pool' =>
    rw [hs] at h
    simp only [Option.some.injEq] at h
    subst h
    refine ⟨⟨GameState.WF.congr hwf rfl rfl rfl rfl,
             GameState.OwnerOk.congr hok rfl rfl,
             GameState.RollbackOk.preserve hrb rfl rfl (List.Perm.refl _),
             List.Perm.refl _, rfl⟩, rfl⟩

/-- Helper: `moveObj` preserves `StepPreserves` (keeping `playRollback` intact). -/
theorem moveObj_preserves {s s' : GameState} {id id' : ObjId} {dst : Zone} {pos : Pos} {fd : Bool}
    (hwf : s.WF) (hok : s.OwnerOk) (hrb : s.RollbackOk)
    (h : moveObj s id dst pos fd = some (s', id')) :
    StepPreserves s s' := by
  have hmeta := moveObj_config_rollback h
  have hp := moveObj_physIds hwf h
  exact ⟨moveObj_wf hwf h, moveObj_ownerOk hwf hok h,
         GameState.RollbackOk.preserve hrb hmeta.1 hmeta.2 hp, hp, hmeta.1⟩

/-- Helper: updating only metadata/pending fields preserves `StepPreserves`. -/
theorem sameBoard_preserves {s s' : GameState} (hwf : s.WF) (hok : s.OwnerOk) (hrb : s.RollbackOk)
    (hc : s'.config = s.config) (ho : s'.objects = s.objects) (hz : s'.zones = s.zones)
    (hn : s'.nextId = s.nextId) (hr : s'.playRollback = s.playRollback) :
    StepPreserves s s' := by
  have hp : s'.physIds = s.physIds := by
    unfold GameState.physIds GameState.zoneIds GameState.playerCount GameState.zone GameState.obj?
    rw [hc, ho, hz]
  have hperm : s'.physIds.Perm s.physIds := by rw [hp]
  exact ⟨GameState.WF.congr hwf hc ho hz hn,
         GameState.OwnerOk.congr hok ho hz,
         GameState.RollbackOk.preserve hrb hc hr hperm,
         hperm, hc⟩

/-- Applying a legal frame answer preserves `WF`, `OwnerOk`, `RollbackOk`, `physIds`, and `config`. -/
theorem applyFrame_preserves {s s' : GameState} {a : Action} {es : List Event}
    (hwf : s.WF) (hok : s.OwnerOk) (hrb : s.RollbackOk)
    (hl : LegalFrame s a) (h : applyFrame s a = some (s', es)) :
    StepPreserves s s' := by
  unfold applyFrame at h
  unfold LegalFrame at hl
  split at h
  · -- chanceFirstPlayer
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
    exact sameBoard_preserves hwf hok hrb rfl rfl rfl rfl rfl
  · -- chooseFirstPlayer
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
      exact sameBoard_preserves hwf hok hrb rfl rfl rfl rfl rfl
    · cases h
  · -- loadoutEquip
    split at h
    · split at h
      · cases h
      · split at h
        · cases h
        · rename_i hm
          simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
          have hp := moveObj_preserves hwf hok hrb hm
          exact hp.trans (sameBoard_preserves hp.wf hp.ownerOk hp.rollbackOk rfl rfl rfl rfl rfl)
    · cases h
  · -- loadoutToDeck
    split at h
    · split at h
      · cases h
      · rename_i hm
        simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
        have hp := moveObj_preserves hwf hok hrb hm
        exact hp.trans (sameBoard_preserves hp.wf hp.ownerOk hp.rollbackOk rfl rfl rfl rfl rfl)
    · cases h
  · -- loadoutDone
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
      exact sameBoard_preserves hwf hok hrb rfl rfl rfl rfl rfl
    · cases h
  · -- chanceShuffle
    rename_i z rest l hp ha hk
    rw [hp, ha, hk] at hl
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
    have hperm := GameState.physIds_reorder hl.1 hl.2
    exact ⟨GameState.WF.congr (GameState.wf_reorder hwf hl.1 hl.2) rfl rfl rfl rfl,
           GameState.OwnerOk.congr (GameState.ownerOk_reorder hok hl.2) rfl rfl,
           GameState.RollbackOk.preserve hrb rfl rfl hperm,
           hperm, rfl⟩
  · -- priority pass
    split at h
    · dsimp only at h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
        exact sameBoard_preserves hwf hok hrb rfl rfl rfl rfl rfl
      · split at h <;>
        · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
          exact sameBoard_preserves hwf hok hrb rfl rfl rfl rfl rfl
    · cases h
  · -- priority playCard
    split at h
    · dsimp only at h
      split at h
      · cases h
      · rename_i s1 layerId hm
        simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
        have hmeta := moveObj_config_rollback hm
        have hperm := moveObj_physIds hwf hm
        have hwf1 := moveObj_wf hwf hm
        have hok1 := moveObj_ownerOk hwf hok hm
        refine ⟨GameState.WF.congr hwf1 rfl rfl rfl rfl,
                GameState.OwnerOk.congr hok1 rfl rfl,
                ?_, hperm, hmeta.1⟩
        intro snap hs
        simp only [Option.some.injEq] at hs
        subst hs
        refine ⟨GameState.WF.congr hwf hmeta.1 rfl rfl rfl,
                GameState.OwnerOk.congr hok rfl rfl, ?_⟩
        change (s1.restore s.snapshot).physIds.Perm s1.physIds
        rw [restore_snapshot_physIds s s1 hmeta.1]
        exact hperm.symm
    · cases h
  · -- priority attackWeapon
    split at h
    · dsimp only at h
      split at h
      · cases h
      · rename_i s1 proxyId hadd
        simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
        have hcfg : s1.config = s.config := by
          unfold addObject at hadd
          split at hadd
          · dsimp only at hadd; simp only [Option.some.injEq, Prod.mk.injEq] at hadd
            obtain ⟨rfl, rfl⟩ := hadd; rfl
          · cases hadd
        have hwf1 := addObject_wf hwf hadd
        have hok1 := addObject_ownerOk hwf hok hadd
        have hperm : s1.physIds.Perm s.physIds := addObject_physIds hwf rfl hadd
        refine ⟨GameState.WF.congr hwf1 rfl rfl rfl rfl,
                GameState.OwnerOk.congr hok1 rfl rfl,
                ?_, hperm, hcfg⟩
        intro snap hs
        simp only [Option.some.injEq] at hs
        subst hs
        refine ⟨GameState.WF.congr hwf hcfg rfl rfl rfl,
                GameState.OwnerOk.congr hok rfl rfl, ?_⟩
        change (s1.restore s.snapshot).physIds.Perm s1.physIds
        rw [restore_snapshot_physIds s s1 hcfg]
        exact hperm.symm
    · cases h
  · -- defendPick defendCard
    split at h
    · split at h
      · dsimp only at h
        split at h
        · rename_i srcZ s1 id' _ hm
          simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
          have hp := moveObj_preserves hwf hok hrb hm
          exact hp.trans (sameBoard_preserves hp.wf hp.ownerOk hp.rollbackOk rfl rfl rfl rfl rfl)
        · cases h
      · cases h
    · cases h
  · -- defendPick defendDone
    split at h
    · dsimp only at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
      exact sameBoard_preserves hwf hok hrb rfl rfl rfl rfl rfl
    · cases h
  · -- chooseMode pickMode
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
      exact sameBoard_preserves hwf hok hrb rfl rfl rfl rfl rfl
    · cases h
  · -- chooseMode cancelPlay
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
      exact rollbackPlay_preserves hwf hok hrb _
    · cases h
  · -- choosePitch pitchCard
    split at h
    · split at h
      · cases h
      · rename_i s1 id1 es1 hpitch
        simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
        have hmeta := pitchOne_config_rollback hpitch
        have hperm := pitchOne_physIds hwf hpitch
        exact ⟨GameState.WF.congr (pitchOne_wf hwf hpitch) rfl rfl rfl rfl,
               GameState.OwnerOk.congr (pitchOne_ownerOk hwf hok hpitch) rfl rfl,
               GameState.RollbackOk.preserve hrb hmeta.1 hmeta.2 hperm,
               hperm, hmeta.1⟩
    · cases h
  · -- choosePitch cancelPlay
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
      exact rollbackPlay_preserves hwf hok hrb _
    · cases h
  · -- chooseMay pickMay
    split at h
    · split at h <;>
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
        exact sameBoard_preserves hwf hok hrb rfl rfl rfl rfl rfl
    · cases h
  · -- chooseModal pickMode
    split at h
    · dsimp only at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
      exact sameBoard_preserves hwf hok hrb rfl rfl rfl rfl rfl
    · cases h
  · -- chanceDie6 die6Roll
    split at h
    · dsimp only at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
      exact sameBoard_preserves hwf hok hrb rfl rfl rfl rfl rfl
    · cases h
  · -- chooseHandToDeck handToDeckPick
    split at h
    · dsimp only at h
      split at h
      · cases h
      · rename_i hm
        simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
        have hp := moveObj_preserves hwf hok hrb hm
        exact hp.trans (sameBoard_preserves hp.wf hp.ownerOk hp.rollbackOk rfl rfl rfl rfl rfl)
    · cases h
  · -- chooseOpt optPick
    rename_i p cardId rest q putOnTop _ _ _
    split at h
    · split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
        exact sameBoard_preserves hwf hok hrb rfl rfl rfl rfl rfl
      · dsimp only at h
        split at h
        · rename_i hmem
          simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
          have hp_lt : p.n < s.playerCount := player_lt_of_mem_zone hwf hmem
          have hz_valid : (Zone.player p .deck).Valid s.playerCount := Zone.valid_player hp_lt .deck
          have hperm_l : ((s.zone (.player p .deck)).erase cardId ++ [cardId]).Perm
              (s.zone (.player p .deck)) := erase_append_singleton_perm hmem
          have hperm := GameState.physIds_reorder hz_valid hperm_l
          exact ⟨GameState.WF.congr (GameState.wf_reorder hwf hz_valid hperm_l) rfl rfl rfl rfl,
                 GameState.OwnerOk.congr (GameState.ownerOk_reorder hok hperm_l) rfl rfl,
                 GameState.RollbackOk.preserve hrb rfl rfl hperm,
                 hperm, rfl⟩
        · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
          exact sameBoard_preserves hwf hok hrb rfl rfl rfl rfl rfl
    · cases h
  · -- chooseArsenal arsenalPut
    split at h
    · split at h
      · cases h
      · rename_i hm
        simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
        have hp := moveObj_preserves hwf hok hrb hm
        exact hp.trans (sameBoard_preserves hp.wf hp.ownerOk hp.rollbackOk rfl rfl rfl rfl rfl)
    · cases h
  · -- chooseArsenal arsenalSkip
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
      exact sameBoard_preserves hwf hok hrb rfl rfl rfl rfl rfl
    · cases h
  · -- choosePitchOrder pitchReturnPick
    split at h
    · split at h
      · cases h
      · rename_i hm
        simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
        have hp := moveObj_preserves hwf hok hrb hm
        exact hp.trans (sameBoard_preserves hp.wf hp.ownerOk hp.rollbackOk rfl rfl rfl rfl rfl)
    · cases h
  · cases h

/-- Applying any legal `Action` preserves `StepPreserves`. -/
theorem applyAction_preserves {s s' : GameState} {a : Action} {es : List Event}
    (hwf : s.WF) (hok : s.OwnerOk) (hrb : s.RollbackOk)
    (hl : Legal s a) (h : applyAction s a = some (s', es)) :
    StepPreserves s s' := by
  unfold applyAction at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
    exact ⟨GameState.WF.congr hwf rfl rfl rfl rfl,
           GameState.OwnerOk.congr hok rfl rfl,
           GameState.RollbackOk.of_none rfl,
           List.Perm.refl _, rfl⟩
  · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
    obtain ⟨hwf1, hok1, hrb1, hp1, hc1⟩ := applyTimeExpired_inv hwf hok hrb
    exact ⟨hwf1, hok1, hrb1, by rw [hp1], hc1⟩
  · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
    obtain ⟨hwf1, hok1, hrb1, hp1, hc1⟩ := applyJudgeLoopDraw_inv hwf hok
    exact ⟨hwf1, hok1, hrb1, by rw [hp1], hc1⟩
  · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
    obtain ⟨hwf1, hok1, hrb1, hp1, hc1⟩ := applyOfferDraw_inv hwf hok hrb _
    exact ⟨hwf1, hok1, hrb1, by rw [hp1], hc1⟩
  · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
    obtain ⟨hwf1, hok1, hrb1, hp1, hc1⟩ := applyAcceptDraw_inv hwf hok
    exact ⟨hwf1, hok1, hrb1, by rw [hp1], hc1⟩
  · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
    obtain ⟨hwf1, hok1, hrb1, hp1, hc1⟩ := applyDeclineDraw_inv hwf hok hrb
    exact ⟨hwf1, hok1, hrb1, by rw [hp1], hc1⟩
  · rename_i hnc hnt hnj hno hna hnd
    rcases hl.2 with hlf | hlc | hlt
    · exact applyFrame_preserves hwf hok hrb hlf h
    · unfold LegalConcede at hlc
      cases ha : a.actor <;> cases hk : a.kind <;> simp [ha, hk] at hlc
      exact False.elim (hnc _ ha hk)
    · unfold LegalTournament at hlt
      cases ha : a.actor <;> cases hk : a.kind <;> simp [ha, hk] at hlt
      · exact False.elim (hno _ ha hk)
      · exact False.elim (hna _ ha hk)
      · exact False.elim (hnd _ ha hk)
      · exact False.elim (hnt ha hk)
      · exact False.elim (hnj ha hk)

/-- Helper: `drawOne` preserves `config` and `playRollback`. -/
theorem drawOne_meta (s : GameState) (p : PlayerId) :
    (drawOne s p).1.config = s.config ∧ (drawOne s p).1.playRollback = s.playRollback := by
  unfold drawOne
  cases s.zone (.player p .deck) with
  | nil => exact ⟨rfl, rfl⟩
  | cons id _ =>
    dsimp only
    cases hm : moveObj s id (.player p .hand) .top false with
    | none => exact ⟨rfl, rfl⟩
    | some res => exact moveObj_config_rollback hm

/-- `gspRun` followed by setting `pending` preserves `StepPreserves`. -/
theorem gspRun_pending_preserves {s : GameState} (hwf : s.WF) (hok : s.OwnerOk)
    (hrb : s.RollbackOk) (newPending : List Frame) :
    StepPreserves s { gspRun s with pending := newPending } := by
  have hm := gspRun_meta s
  have hp := gspRun_physIds hwf
  exact ⟨GameState.WF.congr (gspRun_wf hwf) rfl rfl rfl rfl,
         GameState.OwnerOk.congr (gspRun_ownerOk hwf hok) rfl rfl,
         GameState.RollbackOk.preserve hrb hm.1 hm.2 hp,
         hp, hm.1⟩

/-- Same-board update followed by `gspRun` and setting `pending` preserves `StepPreserves`. -/
theorem sameBoard_gspRun_pending_preserves {s s1 : GameState} (hwf : s.WF) (hok : s.OwnerOk)
    (hrb : s.RollbackOk)
    (hc : s1.config = s.config) (ho : s1.objects = s.objects) (hz : s1.zones = s.zones)
    (hn : s1.nextId = s.nextId) (hr : s1.playRollback = s.playRollback)
    (newPending : List Frame) :
    StepPreserves s { gspRun s1 with pending := newPending } := by
  have hp1 := sameBoard_preserves hwf hok hrb hc ho hz hn hr
  exact hp1.trans (gspRun_pending_preserves hp1.wf hp1.ownerOk hp1.rollbackOk newPending)

/-- One `microStep` preserves `WF`, `OwnerOk`, `RollbackOk`, `physIds`, and `config` (L2 + L4). -/
theorem microStep_preserves {s s' : GameState} {es : List Event}
    (hwf : s.WF) (hok : s.OwnerOk) (hrb : s.RollbackOk)
    (h : microStep s = some (s', es)) :
    StepPreserves s s' := by
  unfold microStep at h
  split at h
  · -- revealLoadouts
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
    have hperm : (revealAllLoadouts s).physIds.Perm s.physIds := by rw [revealAllLoadouts_physIds]
    exact ⟨GameState.WF.congr (revealAllLoadouts_wf hwf) rfl rfl rfl rfl,
           GameState.OwnerOk.congr (revealAllLoadouts_ownerOk hok) rfl rfl,
           GameState.RollbackOk.preserve hrb rfl rfl hperm,
           hperm, rfl⟩
  · -- openingDraws
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
    exact sameBoard_preserves hwf hok hrb rfl rfl rfl rfl rfl
  · -- draw 0
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
    exact sameBoard_preserves hwf hok hrb rfl rfl rfl rfl rfl
  · -- draw (n + 1)
    rename_i p _ _ _
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
    have hmeta := drawOne_meta s p
    have hperm := drawOne_physIds hwf (p := p)
    exact ⟨GameState.WF.congr (drawOne_wf hwf) rfl rfl rfl rfl,
           GameState.OwnerOk.congr (drawOne_ownerOk hwf hok) rfl rfl,
           GameState.RollbackOk.preserve hrb hmeta.1 hmeta.2 hperm,
           hperm, hmeta.1⟩
  · -- beginTurn
    split at h
    · split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
        exact ⟨GameState.WF.congr hwf rfl rfl rfl rfl,
               GameState.OwnerOk.congr hok rfl rfl,
               GameState.RollbackOk.of_none rfl,
               List.Perm.refl _, rfl⟩
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
        exact sameBoard_preserves hwf hok hrb rfl rfl rfl rfl rfl
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
      exact sameBoard_preserves hwf hok hrb rfl rfl rfl rfl rfl
  · -- startPhaseWork
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
    exact sameBoard_preserves hwf hok hrb rfl rfl rfl rfl rfl
  · -- actionPhaseStart
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
    exact sameBoard_preserves hwf hok hrb rfl rfl rfl rfl rfl
  · -- playPayCost
    split at h
    · rename_i s1 hspend
      simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
      obtain ⟨hp1, _⟩ := spendAssetCost_preserves hwf hok hrb hspend
      exact ⟨GameState.WF.congr hp1.wf rfl rfl rfl rfl,
             GameState.OwnerOk.congr hp1.ownerOk rfl rfl,
             GameState.RollbackOk.of_none rfl,
             hp1.physIds, hp1.config⟩
    · split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
        exact sameBoard_preserves hwf hok hrb rfl rfl rfl rfl rfl
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
        exact rollbackPlay_preserves hwf hok hrb _
  · -- resolveStack
    split at h
    · split at h <;>
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
        exact sameBoard_preserves hwf hok hrb rfl rfl rfl rfl rfl
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
      exact sameBoard_preserves hwf hok hrb rfl rfl rfl rfl rfl
  · -- finishResolve
    rename_i layerId rest _
    dsimp only at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
    let info := s.layerMeta.getD layerId.n { controller := s.active.getD ⟨0⟩ }
    let s1 := if info.goAgain then
      s.setPool info.controller ((s.poolOf info.controller).addActionPoints 1) else s
    have hp1 : StepPreserves s s1 := by
      dsimp only [s1]
      split
      · exact sameBoard_preserves hwf hok hrb rfl rfl rfl rfl rfl
      · exact StepPreserves.refl hwf hok hrb
    let isDefReact :=
      match s1.cardDefOf? layerId with
      | some c => c.front.hasType .defenseReaction && s1.combat.isSome
      | none => false
    let p2 :=
      if layerId ∈ s1.zone .stack then
        if isDefReact then
          match moveObj s1 layerId .combatChain .top false with
          | some (sMoved, id') =>
            let cc' := sMoved.combat.map fun cc => cc.updateActiveLink fun l =>
              { l with
                defending := l.defending ++ [id']
                defendedFromHandCount := l.defendedFromHandCount + (if !info.fromArsenal then 1 else 0) }
            ({ sMoved with combat := cc' }, [Event.moved layerId id' .stack .combatChain])
          | none => (s1, [])
        else
          match s1.obj? layerId with
          | some o =>
            let isPerm :=
              match s1.cardDefOf? layerId with
              | some c => c.front.hasSubtype .aura || c.front.hasSubtype .item
              | none => false
            let dst := if isPerm then Zone.player info.controller .permanent
                       else Zone.player o.owner .graveyard
            match moveObj s1 layerId dst .top false with
            | some (sMoved, id') => (sMoved, [Event.moved layerId id' .stack dst])
            | none => (s1, [])
          | none => (s1, [])
      else
        (s1, [])
    have hp2 : StepPreserves s1 p2.1 := by
      dsimp only [p2]
      split
      · split
        · cases hm : moveObj s1 layerId .combatChain .top false with
          | none => exact StepPreserves.refl hp1.wf hp1.ownerOk hp1.rollbackOk
          | some res =>
            have hpm := moveObj_preserves hp1.wf hp1.ownerOk hp1.rollbackOk hm
            exact hpm.trans (sameBoard_preserves hpm.wf hpm.ownerOk hpm.rollbackOk rfl rfl rfl rfl rfl)
        · cases ho : s1.obj? layerId with
          | none => exact StepPreserves.refl hp1.wf hp1.ownerOk hp1.rollbackOk
          | some o =>
            dsimp only
            cases hm : moveObj s1 layerId _ .top false with
            | none => exact StepPreserves.refl hp1.wf hp1.ownerOk hp1.rollbackOk
            | some res => exact moveObj_preserves hp1.wf hp1.ownerOk hp1.rollbackOk hm
      · exact StepPreserves.refl hp1.wf hp1.ownerOk hp1.rollbackOk
    have hp12 := hp1.trans hp2
    let p2e : GameState := { p2.1 with layerMeta := p2.1.layerMeta.erase layerId.n }
    have hwf_e : p2e.WF := GameState.WF.congr hp12.wf rfl rfl rfl rfl
    have hok_e : p2e.OwnerOk := GameState.OwnerOk.congr hp12.ownerOk rfl rfl
    have hmeta3 := gspRun_meta p2e
    have hphys3 : (gspRun p2e).physIds.Perm p2.1.physIds := gspRun_physIds hwf_e
    have hp3 : StepPreserves p2.1
        { gspRun p2e with
            pending := Frame.priority ((gspRun p2e).active.getD ⟨0⟩) 0 :: rest } :=
      ⟨GameState.WF.congr (gspRun_wf hwf_e) rfl rfl rfl rfl,
       GameState.OwnerOk.congr (gspRun_ownerOk hwf_e hok_e) rfl rfl,
       GameState.RollbackOk.preserve hp12.rollbackOk hmeta3.1 hmeta3.2 hphys3,
       hphys3, hmeta3.1⟩
    exact hp12.trans hp3
  · -- combatStep .layer
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
    exact sameBoard_preserves hwf hok hrb rfl rfl rfl rfl rfl
  · -- combatStep .attack
    rename_i layerId rest _
    dsimp only at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
    let info := s.layerMeta.getD layerId.n { controller := s.active.getD ⟨0⟩ }
    obtain ⟨hwf1, hok1, hp1, hc1, hr1⟩ := enterAttackStep_inv hwf hok layerId info.controller
    exact ⟨GameState.WF.congr hwf1 rfl rfl rfl rfl,
           GameState.OwnerOk.congr hok1 rfl rfl,
           GameState.RollbackOk.preserve hrb hc1 hr1 hp1,
           hp1, hc1⟩
  · -- combatStep .defend
    split at h
    · dsimp only at h
      split at h <;>
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
        exact sameBoard_preserves hwf hok hrb rfl rfl rfl rfl rfl
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
      exact sameBoard_preserves hwf hok hrb rfl rfl rfl rfl rfl
  · -- combatStep .reaction
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
    exact sameBoard_preserves hwf hok hrb rfl rfl rfl rfl rfl
  · -- combatStep .damage
    rename_i atkId rest _
    dsimp only at h
    cases hcc : s.combat with
    | none =>
      rw [hcc] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
      exact sameBoard_preserves hwf hok hrb rfl rfl rfl rfl rfl
    | some cc =>
      rw [hcc] at h
      dsimp only at h
      cases hl : cc.activeLink? with
      | none =>
        rw [hl] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
        exact sameBoard_preserves hwf hok hrb rfl rfl rfl rfl rfl
      | some link =>
        rw [hl] at h
        dsimp only at h
        split at h <;>
        · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
          apply sameBoard_gspRun_pending_preserves hwf hok hrb <;> rfl
  · -- combatStep .resolution
    dsimp only at h
    split at h
    · split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
        split <;> exact sameBoard_preserves hwf hok hrb rfl rfl rfl rfl rfl
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
        exact sameBoard_preserves hwf hok hrb rfl rfl rfl rfl rfl
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
      exact sameBoard_preserves hwf hok hrb rfl rfl rfl rfl rfl
  · -- combatStep .close
    rename_i _ rest _
    have hinv := closeCombatChainStep_inv hwf hok
    cases hcc : closeCombatChainStep s with
    | mk s1 es1 =>
      rw [hcc] at h hinv
      dsimp only at h hinv
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      obtain ⟨hwf1, hok1, hp1, hc1, hr1⟩ := hinv
      have hp1s : StepPreserves s s1 :=
        ⟨hwf1, hok1, GameState.RollbackOk.preserve hrb hc1 hr1 hp1, hp1, hc1⟩
      exact hp1s.trans (gspRun_pending_preserves hwf1 hok1 hp1s.rollbackOk _)
  · -- gameStateProcess
    dsimp only at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
    exact gspRun_pending_preserves hwf hok hrb _
  · -- run (L4!)
    rename_i ctrl src fromArsenal env todo rest _
    simp only [Option.some.injEq] at h
    have hs' : s' = (interpRunStep s ctrl src fromArsenal env todo rest).1 :=
      congrArg Prod.fst h.symm
    subst hs'
    have hmeta := interpRunStep_meta s ctrl src fromArsenal env todo rest
    have hperm := interpRunStep_physIds hwf ctrl src fromArsenal env todo rest
    exact ⟨interpRunStep_wf hwf ctrl src fromArsenal env todo rest,
           interpRunStep_ownerOk hwf hok ctrl src fromArsenal env todo rest,
           GameState.RollbackOk.preserve hrb hmeta.1 hmeta.2 hperm,
           hperm, hmeta.1⟩
  · -- optStep 0
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
    exact sameBoard_preserves hwf hok hrb rfl rfl rfl rfl rfl
  · -- optStep (n + 1)
    split at h <;>
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
      exact sameBoard_preserves hwf hok hrb rfl rfl rfl rfl rfl
  · -- endPhaseStart
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
    exact sameBoard_preserves hwf hok hrb rfl rfl rfl rfl rfl
  · -- returnPitch
    split at h <;>
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
      exact sameBoard_preserves hwf hok hrb rfl rfl rfl rfl rfl
  · -- endTurnCleanup
    rename_i tp _ _
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
    have hperm : (untapPlayer s tp).physIds.Perm s.physIds := by rw [untapPlayer_physIds]
    exact ⟨GameState.WF.congr (untapPlayer_wf hwf tp) rfl rfl rfl rfl,
           GameState.OwnerOk.congr (untapPlayer_ownerOk hok tp) rfl rfl,
           GameState.RollbackOk.preserve hrb rfl rfl hperm,
           hperm, rfl⟩
  · cases h

/-- `advance` preserves `StepPreserves`. -/
theorem advance_preserves :
    ∀ (n : Nat) {s s' : GameState} {es es' : List Event},
      s.WF → s.OwnerOk → s.RollbackOk →
      advance n s es = .ok (s', es') → StepPreserves s s'
  | 0, s, s', es, es', hwf, hok, hrb, h => by
    unfold advance at h
    split at h
    · split at h
      · cases h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
        exact StepPreserves.refl hwf hok hrb
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
      exact StepPreserves.refl hwf hok hrb
  | n + 1, s, s', es, es', hwf, hok, hrb, h => by
    unfold advance at h
    split at h
    · split at h
      · split at h
        · rename_i s1 es1 hm
          have h1 := microStep_preserves hwf hok hrb hm
          exact h1.trans (advance_preserves n h1.wf h1.ownerOk h1.rollbackOk h)
        · cases h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
        exact StepPreserves.refl hwf hok hrb
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
      exact StepPreserves.refl hwf hok hrb

/-- Full step preservation bundle (I1 + I3 + RollbackOk). -/
theorem step_preserves {fuel : Nat} {s s' : GameState} {a : Action} {es : List Event}
    (hwf : s.WF) (hok : s.OwnerOk) (hrb : s.RollbackOk)
    (h : step fuel s a = .ok (s', es)) : StepPreserves s s' := by
  unfold step at h
  split at h
  · rename_i hl
    split at h
    · rename_i s1 es1 ha
      have h1 := applyAction_preserves hwf hok hrb hl ha
      exact h1.trans (advance_preserves fuel h1.wf h1.ownerOk h1.rollbackOk h)
    · cases h
  · cases h

/-- **I3**: `step` preserves structural well-formedness `WF`. -/
theorem step_wf {fuel : Nat} {s s' : GameState} {a : Action} {es : List Event}
    (hwf : s.WF) (hok : s.OwnerOk) (hrb : s.RollbackOk)
    (h : step fuel s a = .ok (s', es)) : s'.WF :=
  (step_preserves hwf hok hrb h).wf

/-- `step` preserves `OwnerOk`. -/
theorem step_ownerOk {fuel : Nat} {s s' : GameState} {a : Action} {es : List Event}
    (hwf : s.WF) (hok : s.OwnerOk) (hrb : s.RollbackOk)
    (h : step fuel s a = .ok (s', es)) : s'.OwnerOk :=
  (step_preserves hwf hok hrb h).ownerOk

/-- **I1**: `step` preserves the multiset of all physical cards across the entire game. -/
theorem step_physIds {fuel : Nat} {s s' : GameState} {a : Action} {es : List Event}
    (hwf : s.WF) (hok : s.OwnerOk) (hrb : s.RollbackOk)
    (h : step fuel s a = .ok (s', es)) : s'.physIds.Perm s.physIds :=
  (step_preserves hwf hok hrb h).physIds

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
        | chanceFirstChooser _ | pickFirstPlayer _ | shuffleOrder _ | pass | playCard _
        | attackWeapon _ | defendCard _ | defendDone
        | pickMode _ | pitchCard _ | cancelPlay | pickMay _ | die6Roll _ | handToDeckPick _
        | optPick _ | arsenalPut _ | arsenalSkip | pitchReturnPick _ | concede | timeExpired | offerDraw | acceptDraw | declineDraw | judgeLoopDraw =>
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
      cases actor with
      | player q =>
        cases kind with
        | pass =>
          simp only [Actor.isPlayer, and_true, List.mem_cons, List.mem_append, List.mem_map,
            List.mem_filter, Action.mk.injEq, Actor.player.injEq, and_true]
          constructor
          · rintro (hq | ⟨_, _, _, hcontra⟩ | ⟨_, _, _, hcontra⟩)
            · exact hq
            · cases hcontra
            · cases hcontra
          · intro hq; left; exact hq
        | playCard id =>
          simp only [Actor.isPlayer, and_true, List.mem_cons, List.mem_append, List.mem_map,
            List.mem_filter, Action.mk.injEq, Actor.player.injEq, ActionKind.playCard.injEq]
          constructor
          · rintro (⟨_, hcontra⟩ | ⟨x, ⟨_, hcan⟩, rfl, rfl⟩ | ⟨_, _, _, hcontra⟩)
            · cases hcontra
            · exact ⟨rfl, hcan⟩
            · cases hcontra
          · rintro ⟨rfl, hcan⟩
            right; left
            exact ⟨id, ⟨mem_hand_or_arsenal_of_canPlayCard hcan, hcan⟩, rfl, rfl⟩
        | attackWeapon wid =>
          simp only [Actor.isPlayer, and_true, List.mem_cons, List.mem_append, List.mem_map,
            List.mem_filter, Action.mk.injEq, Actor.player.injEq, ActionKind.attackWeapon.injEq]
          constructor
          · rintro (⟨_, hcontra⟩ | ⟨_, _, _, hcontra⟩ | ⟨x, ⟨_, hcan⟩, rfl, rfl⟩)
            · cases hcontra
            · cases hcontra
            · exact ⟨rfl, hcan⟩
          · rintro ⟨rfl, hcan⟩
            right; right
            exact ⟨wid, ⟨mem_weapon_of_canAttackWithWeapon hcan, hcan⟩, rfl, rfl⟩
        | chanceFirstChooser _ | pickFirstPlayer _ | loadoutEquip _ | loadoutToDeck _
        | loadoutDone | shuffleOrder _ | defendCard _ | defendDone | pickMode _ | pitchCard _
        | cancelPlay | pickMay _ | die6Roll _ | handToDeckPick _ | optPick _ | arsenalPut _
        | arsenalSkip | pitchReturnPick _ | concede | timeExpired | offerDraw | acceptDraw | declineDraw | judgeLoopDraw =>
          simp [Actor.isPlayer]
      | chance | clock | judge =>
        cases kind <;> simp [Actor.isPlayer]
    | defendPick defender =>
      cases actor with
      | player q =>
        cases kind with
        | defendCard id =>
          simp only [Actor.isPlayer, and_true, List.mem_append, List.mem_singleton,
            Action.mk.injEq, Actor.player.injEq]
          cases hc : s.combat.bind CombatChain.activeLink? with
          | none =>
            simp only [List.not_mem_nil, false_or, and_false, iff_false]
            rintro ⟨_, hcontra⟩; cases hcontra
          | some link =>
            simp only [List.mem_map, List.mem_filter, Action.mk.injEq, Actor.player.injEq,
              ActionKind.defendCard.injEq]
            constructor
            · rintro (⟨x, ⟨_, hcan⟩, rfl, rfl⟩ | ⟨_, hcontra⟩)
              · exact ⟨rfl, hcan⟩
              · cases hcontra
            · rintro ⟨rfl, hcan⟩
              left
              exact ⟨id, ⟨mem_defendCandidates_of_canDefendWith hcan, hcan⟩, rfl, rfl⟩
        | defendDone =>
          simp only [Actor.isPlayer, and_true, List.mem_append, List.mem_singleton,
            Action.mk.injEq, Actor.player.injEq, and_true]
          constructor
          · rintro (hdef | hq)
            · cases hc : s.combat.bind CombatChain.activeLink? with
              | none => simp [hc] at hdef
              | some link =>
                simp only [hc, List.mem_map, Action.mk.injEq] at hdef
                obtain ⟨_, _, _, hcontra⟩ := hdef
                cases hcontra
            · exact hq
          · intro hq; right; exact hq
        | chanceFirstChooser _ | pickFirstPlayer _ | loadoutEquip _ | loadoutToDeck _
        | loadoutDone | shuffleOrder _ | pass | playCard _ | attackWeapon _ | pickMode _
        | pitchCard _ | cancelPlay | pickMay _ | die6Roll _ | handToDeckPick _ | optPick _
        | arsenalPut _ | arsenalSkip | pitchReturnPick _ | concede | timeExpired | offerDraw | acceptDraw | declineDraw | judgeLoopDraw =>
          simp only [Actor.isPlayer, and_true, List.mem_append, List.mem_singleton,
            Action.mk.injEq, iff_false]
          rintro (hdef | ⟨_, hcontra⟩)
          · cases hc : s.combat.bind CombatChain.activeLink? with
            | none => simp [hc] at hdef
            | some link =>
              simp only [hc, List.mem_map, Action.mk.injEq] at hdef
              obtain ⟨_, _, _, hcontra⟩ := hdef
              cases hcontra
          · cases hcontra
      | chance | clock | judge =>
        cases kind <;> simp only [Actor.isPlayer, Bool.false_eq_true, and_false, iff_false,
          List.mem_append, List.mem_singleton, Action.mk.injEq]
        all_goals
          rintro (hdef | ⟨hcontra, _⟩)
          · cases hc : s.combat.bind CombatChain.activeLink? with
            | none => simp [hc] at hdef
            | some link =>
              simp only [hc, List.mem_map, Action.mk.injEq] at hdef
              obtain ⟨_, _, hcontra, _⟩ := hdef
              cases hcontra
          · cases hcontra
    | chooseMode p _ _ modeCount _ =>
      cases actor <;> cases kind <;> simp [Actor.isPlayer]
      all_goals grind
    | choosePitch p _ _ _ _ =>
      cases actor with
      | player q =>
        cases kind with
        | pitchCard id =>
          unfold pitchableCards
          simp only [Actor.isPlayer, and_true, List.mem_append, List.mem_map, List.mem_filter,
            List.mem_singleton, Action.mk.injEq, Actor.player.injEq, ActionKind.pitchCard.injEq]
          constructor
          · rintro (⟨x, ⟨_, hcan⟩, rfl, rfl⟩ | ⟨_, hcontra⟩)
            · exact ⟨rfl, hcan⟩
            · cases hcontra
          · rintro ⟨rfl, hcan⟩
            left
            exact ⟨id, ⟨mem_hand_of_canPitchCard hcan, hcan⟩, rfl, rfl⟩
        | cancelPlay =>
          simp only [Actor.isPlayer, and_true, List.mem_append, List.mem_map, List.mem_singleton,
            Action.mk.injEq, Actor.player.injEq, and_true]
          constructor
          · rintro (⟨_, _, _, hcontra⟩ | hq)
            · cases hcontra
            · exact hq
          · intro hq; right; exact hq
        | chanceFirstChooser _ | pickFirstPlayer _ | loadoutEquip _ | loadoutToDeck _
        | loadoutDone | shuffleOrder _ | pass | playCard _ | attackWeapon _ | defendCard _
        | defendDone | pickMode _ | pickMay _ | die6Roll _ | handToDeckPick _ | optPick _
        | arsenalPut _ | arsenalSkip | pitchReturnPick _ | concede | timeExpired | offerDraw | acceptDraw | declineDraw | judgeLoopDraw =>
          simp [Actor.isPlayer]
      | chance | clock | judge =>
        cases kind <;> simp [Actor.isPlayer]
    | chooseMay ctrl _ _ _ _ _ =>
      cases actor with
      | player q =>
        cases kind with
        | pickMay b =>
          cases b <;> simp [Actor.isPlayer, eq_comm]
        | chanceFirstChooser _ | pickFirstPlayer _ | loadoutEquip _ | loadoutToDeck _
        | loadoutDone | shuffleOrder _ | pass | playCard _ | attackWeapon _ | defendCard _
        | defendDone | pickMode _ | pitchCard _ | cancelPlay | die6Roll _ | handToDeckPick _
        | optPick _ | arsenalPut _ | arsenalSkip | pitchReturnPick _ | concede | timeExpired | offerDraw | acceptDraw | declineDraw | judgeLoopDraw =>
          simp [Actor.isPlayer]
      | chance | clock | judge =>
        cases kind <;> simp [Actor.isPlayer]
    | chooseModal ctrl _ _ _ modes =>
      cases actor <;> cases kind <;> simp [Actor.isPlayer]
      grind
    | chooseHandToDeck p _ =>
      cases actor <;> cases kind <;> simp [Actor.isPlayer]
      grind
    | chooseOpt p _ =>
      cases actor with
      | player q =>
        cases kind with
        | optPick b =>
          cases b <;> simp [Actor.isPlayer, eq_comm]
        | chanceFirstChooser _ | pickFirstPlayer _ | loadoutEquip _ | loadoutToDeck _
        | loadoutDone | shuffleOrder _ | pass | playCard _ | attackWeapon _ | defendCard _
        | defendDone | pickMode _ | pitchCard _ | cancelPlay | pickMay _ | die6Roll _
        | handToDeckPick _ | arsenalPut _ | arsenalSkip | pitchReturnPick _ | concede | timeExpired | offerDraw | acceptDraw | declineDraw | judgeLoopDraw =>
          simp [Actor.isPlayer]
      | chance | clock | judge =>
        cases kind <;> simp [Actor.isPlayer]
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
        | loadoutDone | shuffleOrder _ | pass | playCard _ | attackWeapon _ | defendCard _
        | defendDone | pickMode _ | pitchCard _ | cancelPlay | pickMay _ | die6Roll _
        | handToDeckPick _ | optPick _ | pitchReturnPick _ | concede | timeExpired | offerDraw | acceptDraw | declineDraw | judgeLoopDraw =>
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
    | startPhaseWork _ | actionPhaseStart _ | playPayCost _ _ _ _ _ | resolveStack
    | finishResolve _ | combatStep _ _ | gameStateProcess | run _ _ _ _ _
    | chanceDie6 _ _ _ _ _ _ _ | optStep _ _ | endPhaseStart _ | returnPitch _
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

/-- **I6** (tournament player action enumeration): `tournamentPlayerActions` matches
`LegalTournament` for player actions (Swiss Bo1 Intentional Draw). -/
theorem tournamentPlayerActions_iff (s : GameState) (a : Action) :
    a ∈ tournamentPlayerActions s ↔ LegalTournament s a ∧ a.actor.isPlayer = true := by
  obtain ⟨actor, kind⟩ := a
  unfold tournamentPlayerActions LegalTournament
  by_cases hcond : s.playerCount = 2 ∧ s.config.ruleSet.allowsIntentionalDraw = true
  · cases hoid : s.tournament.idOffer with
    | none =>
      cases actor <;> cases kind <;> simp [Actor.isPlayer, hcond, allPlayers]
      all_goals grind
    | some q =>
      cases actor <;> cases kind <;> simp [Actor.isPlayer, hcond, allPlayers]
      all_goals grind
  · cases actor <;> cases kind <;> simp [Actor.isPlayer, hcond]
    all_goals (intro h1 _ h2 _; exact hcond ⟨h1, h2⟩)

/-- **I6** (enumeration): `legalActions` enumerates exactly the legal player actions. -/
theorem legalActions_iff (s : GameState) (a : Action) :
    a ∈ legalActions s ↔ Legal s a ∧ a.actor.isPlayer = true := by
  unfold legalActions Legal
  by_cases h : s.result = none
  · simp only [h, ite_true, true_and, List.mem_append]
    rw [legalFrameActions_iff, concedeActions_iff, tournamentPlayerActions_iff]
    constructor
    · rintro ((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩)
      · exact ⟨Or.inl h1, h2⟩
      · exact ⟨Or.inr (Or.inl h1), h2⟩
      · exact ⟨Or.inr (Or.inr h1), h2⟩
    · rintro ⟨h1 | h1 | h1, h2⟩
      · exact Or.inl (Or.inl ⟨h1, h2⟩)
      · exact Or.inl (Or.inr ⟨h1, h2⟩)
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
              intro heq; cases heq; simp [ZoneKind.isArena] at hk_ar
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
        | chanceFirstChooser _ | pickFirstPlayer _ | shuffleOrder _ | pass | playCard _
        | attackWeapon _ | defendCard _ | defendDone
        | pickMode _ | pitchCard _ | cancelPlay | pickMay _ | die6Roll _ | handToDeckPick _
        | optPick _ | arsenalPut _ | arsenalSkip | pitchReturnPick _ | concede | timeExpired | offerDraw | acceptDraw | declineDraw | judgeLoopDraw =>
          exact False.elim hlf
      | chance | clock | judge =>
        cases kind <;> exact False.elim hlf
    | chanceShuffle z =>
      cases actor <;> cases kind <;> simp at hlf ⊢
    | priority p passCount =>
      cases actor with
      | player q =>
        cases kind with
        | pass =>
          subst hlf
          simp only [↓reduceIte]
          split
          · rfl
          · split <;> rfl
        | playCard id =>
          obtain ⟨rfl, hcan⟩ := hlf
          simp only [hcan, and_self, ↓reduceIte]
          have hm : (moveObj s id .stack .top false).isSome = true := by
            rcases mem_hand_or_arsenal_of_canPlayCard hcan with hmem | hmem
            · have hq : q.n < s.playerCount := player_lt_of_mem_zone hwf hmem
              apply moveObj_isSome hwf (Zone.valid_player hq .hand) hmem
              intro o _
              exact ⟨Zone.valid_stack s.playerCount, by intro heq; cases heq⟩
            · have hq : q.n < s.playerCount := player_lt_of_mem_zone hwf hmem
              apply moveObj_isSome hwf (Zone.valid_player hq .arsenal) hmem
              intro o _
              exact ⟨Zone.valid_stack s.playerCount, by intro heq; cases heq⟩
          cases hm' : moveObj s id .stack .top false with
          | none => rw [hm'] at hm; simp at hm
          | some _ => rfl
        | attackWeapon wid =>
          obtain ⟨rfl, hcan⟩ := hlf
          simp only [hcan, and_self, ↓reduceIte]
          have hadd : (addObject s .stack
              { kind := .attackProxy wid (some (captureLki s wid q))
                owner := q
                controller := q
                timestamp := ⟨s.nextTimestamp⟩ } .top).isSome = true := by
            unfold addObject
            have hv : Zone.stack.Valid s.playerCount := Zone.valid_stack s.playerCount
            have ha : Zone.stack.allowsOwner q = true := rfl
            simp [hv, ha]
          cases ha' : addObject s .stack
              { kind := .attackProxy wid (some (captureLki s wid q))
                owner := q
                controller := q
                timestamp := ⟨s.nextTimestamp⟩ } .top with
          | none => rw [ha'] at hadd; simp at hadd
          | some _ => rfl
        | chanceFirstChooser _ | pickFirstPlayer _ | loadoutEquip _ | loadoutToDeck _
        | loadoutDone | shuffleOrder _ | defendCard _ | defendDone | pickMode _ | pitchCard _
        | cancelPlay | pickMay _ | die6Roll _ | handToDeckPick _ | optPick _ | arsenalPut _
        | arsenalSkip | pitchReturnPick _ | concede | timeExpired | offerDraw | acceptDraw | declineDraw | judgeLoopDraw =>
          exact False.elim hlf
      | chance | clock | judge =>
        cases kind <;> exact False.elim hlf
    | defendPick defender =>
      cases actor with
      | player q =>
        cases kind with
        | defendCard id =>
          obtain ⟨rfl, hdef⟩ := hlf
          cases hc : s.combat.bind CombatChain.activeLink? with
          | none => rw [hc] at hdef; exact False.elim hdef
          | some link =>
            rw [hc] at hdef
            simp only [hdef, and_self, ↓reduceIte]
            have hcand := mem_defendCandidates_of_canDefendWith hdef
            unfold defendCandidateIds equipZoneIds at hcand
            simp only [List.mem_append] at hcand
            have hloc_and_move :
                ∃ srcZ, s.locate id = some srcZ ∧ (moveObj s id .combatChain .top false).isSome = true := by
              have aux : ∀ k : ZoneKind, id ∈ s.zone (.player q k) →
                  ∃ srcZ, s.locate id = some srcZ ∧ (moveObj s id .combatChain .top false).isSome = true := by
                intro k hmem
                have hq : q.n < s.playerCount := player_lt_of_mem_zone hwf hmem
                refine ⟨.player q k, GameState.locate_eq hwf (Zone.valid_player hq k) hmem, ?_⟩
                apply moveObj_isSome hwf (Zone.valid_player hq k) hmem
                intro o _
                exact ⟨Zone.valid_combatChain s.playerCount, by intro heq; cases heq⟩
              rcases hcand with hh | (((hhe | hch) | har) | hle)
              · exact aux .hand hh
              · exact aux .head hhe
              · exact aux .chest hch
              · exact aux .arms har
              · exact aux .legs hle
            obtain ⟨srcZ, hloc, hm⟩ := hloc_and_move
            rw [hloc]
            cases hm' : moveObj s id .combatChain .top false with
            | none => rw [hm'] at hm; simp at hm
            | some _ => rfl
        | defendDone =>
          subst hlf
          simp
        | chanceFirstChooser _ | pickFirstPlayer _ | loadoutEquip _ | loadoutToDeck _
        | loadoutDone | shuffleOrder _ | pass | playCard _ | attackWeapon _ | pickMode _
        | pitchCard _ | cancelPlay | pickMay _ | die6Roll _ | handToDeckPick _ | optPick _
        | arsenalPut _ | arsenalSkip | pitchReturnPick _ | concede | timeExpired | offerDraw | acceptDraw | declineDraw | judgeLoopDraw =>
          exact False.elim hlf
      | chance | clock | judge =>
        cases kind <;> exact False.elim hlf
    | chooseMode p _ _ modeCount _ =>
      cases actor with
      | player q =>
        cases kind with
        | pickMode idx =>
          obtain ⟨rfl, hlt⟩ := hlf
          simp [hlt]
        | cancelPlay =>
          subst hlf
          simp
        | chanceFirstChooser _ | pickFirstPlayer _ | loadoutEquip _ | loadoutToDeck _
        | loadoutDone | shuffleOrder _ | pass | playCard _ | attackWeapon _ | defendCard _
        | defendDone | pitchCard _ | pickMay _ | die6Roll _ | handToDeckPick _ | optPick _
        | arsenalPut _ | arsenalSkip | pitchReturnPick _ | concede | timeExpired | offerDraw | acceptDraw | declineDraw | judgeLoopDraw =>
          exact False.elim hlf
      | chance | clock | judge =>
        cases kind <;> exact False.elim hlf
    | choosePitch p _ _ _ _ =>
      cases actor with
      | player q =>
        cases kind with
        | pitchCard id =>
          obtain ⟨rfl, hcan⟩ := hlf
          simp only [hcan, and_self, ↓reduceIte]
          have hmem : id ∈ s.zone (.player q .hand) := mem_hand_of_canPitchCard hcan
          have hq : q.n < s.playerCount := player_lt_of_mem_zone hwf hmem
          have hpitch := pitchOne_isSome hwf hok hq hcan
          cases hp' : pitchOne s q id with
          | none => rw [hp'] at hpitch; simp at hpitch
          | some _ => rfl
        | cancelPlay =>
          subst hlf
          simp
        | chanceFirstChooser _ | pickFirstPlayer _ | loadoutEquip _ | loadoutToDeck _
        | loadoutDone | shuffleOrder _ | pass | playCard _ | attackWeapon _ | defendCard _
        | defendDone | pickMode _ | pickMay _ | die6Roll _ | handToDeckPick _ | optPick _
        | arsenalPut _ | arsenalSkip | pitchReturnPick _ | concede | timeExpired | offerDraw | acceptDraw | declineDraw | judgeLoopDraw =>
          exact False.elim hlf
      | chance | clock | judge =>
        cases kind <;> exact False.elim hlf
    | chooseMay ctrl _ _ _ _ _ =>
      cases actor with
      | player q =>
        cases kind with
        | pickMay b =>
          subst hlf
          cases b <;> simp
        | chanceFirstChooser _ | pickFirstPlayer _ | loadoutEquip _ | loadoutToDeck _
        | loadoutDone | shuffleOrder _ | pass | playCard _ | attackWeapon _ | defendCard _
        | defendDone | pickMode _ | pitchCard _ | cancelPlay | die6Roll _ | handToDeckPick _
        | optPick _ | arsenalPut _ | arsenalSkip | pitchReturnPick _ | concede | timeExpired | offerDraw | acceptDraw | declineDraw | judgeLoopDraw =>
          exact False.elim hlf
      | chance | clock | judge =>
        cases kind <;> exact False.elim hlf
    | chooseModal ctrl _ _ _ modes =>
      cases actor with
      | player q =>
        cases kind with
        | pickMode idx =>
          obtain ⟨rfl, hlt⟩ := hlf
          simp [hlt]
        | chanceFirstChooser _ | pickFirstPlayer _ | loadoutEquip _ | loadoutToDeck _
        | loadoutDone | shuffleOrder _ | pass | playCard _ | attackWeapon _ | defendCard _
        | defendDone | pitchCard _ | cancelPlay | pickMay _ | die6Roll _ | handToDeckPick _
        | optPick _ | arsenalPut _ | arsenalSkip | pitchReturnPick _ | concede | timeExpired | offerDraw | acceptDraw | declineDraw | judgeLoopDraw =>
          exact False.elim hlf
      | chance | clock | judge =>
        cases kind <;> exact False.elim hlf
    | chanceDie6 _ _ _ _ _ _ _ =>
      cases actor <;> cases kind <;> simp at hlf ⊢
      exact hlf
    | chooseHandToDeck p pos =>
      cases actor with
      | player q =>
        cases kind with
        | handToDeckPick id =>
          obtain ⟨rfl, hmem_hand⟩ := hlf
          simp only [hmem_hand, and_self, ↓reduceIte]
          have hq : q.n < s.playerCount := player_lt_of_mem_zone hwf hmem_hand
          have hm : ∀ (dp : Pos), (moveObj s id (.player q .deck) dp false).isSome = true := by
            intro dp
            apply moveObj_isSome hwf (Zone.valid_player hq .hand) hmem_hand
            intro o ho
            have hown : o.owner = q := hok.owner q .hand rfl id hmem_hand o ho
            have hnorm : Zone.normalize o.owner (.player q .deck) = .player q .deck := by
              simp [Zone.normalize, ZoneKind.isArena, hown]
            rw [hnorm]
            exact ⟨Zone.valid_player hq .deck, by intro heq; cases heq⟩
          split
          · rename_i hm'
            cases pos <;> dsimp only at hm'
            · have hsome := hm .top; rw [hm'] at hsome; simp at hsome
            · have hsome := hm .bottom; rw [hm'] at hsome; simp at hsome
            · have hsome := hm .top; rw [hm'] at hsome; simp at hsome
            · have hsome := hm .top; rw [hm'] at hsome; simp at hsome
          · rfl
        | chanceFirstChooser _ | pickFirstPlayer _ | loadoutEquip _ | loadoutToDeck _
        | loadoutDone | shuffleOrder _ | pass | playCard _ | attackWeapon _ | defendCard _
        | defendDone | pickMode _ | pitchCard _ | cancelPlay | pickMay _ | die6Roll _
        | optPick _ | arsenalPut _ | arsenalSkip | pitchReturnPick _ | concede | timeExpired | offerDraw | acceptDraw | declineDraw | judgeLoopDraw =>
          exact False.elim hlf
      | chance | clock | judge =>
        cases kind <;> exact False.elim hlf
    | chooseOpt p cardId =>
      cases actor with
      | player q =>
        cases kind with
        | optPick b =>
          subst hlf
          cases b
          · simp only [Bool.false_eq_true, ↓reduceIte]
            split <;> rfl
          · simp
        | chanceFirstChooser _ | pickFirstPlayer _ | loadoutEquip _ | loadoutToDeck _
        | loadoutDone | shuffleOrder _ | pass | playCard _ | attackWeapon _ | defendCard _
        | defendDone | pickMode _ | pitchCard _ | cancelPlay | pickMay _ | die6Roll _
        | handToDeckPick _ | arsenalPut _ | arsenalSkip | pitchReturnPick _ | concede | timeExpired | offerDraw | acceptDraw | declineDraw | judgeLoopDraw =>
          exact False.elim hlf
      | chance | clock | judge =>
        cases kind <;> exact False.elim hlf
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
        | loadoutDone | shuffleOrder _ | pass | playCard _ | attackWeapon _ | defendCard _
        | defendDone | pickMode _ | pitchCard _ | cancelPlay | pickMay _ | die6Roll _
        | handToDeckPick _ | optPick _ | pitchReturnPick _ | concede | timeExpired | offerDraw | acceptDraw | declineDraw | judgeLoopDraw =>
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
        | loadoutDone | shuffleOrder _ | pass | playCard _ | attackWeapon _ | defendCard _
        | defendDone | pickMode _ | pitchCard _ | cancelPlay | pickMay _ | die6Roll _
        | handToDeckPick _ | optPick _ | arsenalPut _ | arsenalSkip | concede | timeExpired | offerDraw | acceptDraw | declineDraw | judgeLoopDraw =>
          exact False.elim hlf
      | chance | clock | judge =>
        cases kind <;> exact False.elim hlf
    | revealLoadouts | openingDraws | draw _ _ | beginTurn | startPhaseWork _
    | actionPhaseStart _ | playPayCost _ _ _ _ _ | resolveStack | finishResolve _
    | combatStep _ _ | gameStateProcess | run _ _ _ _ _ | optStep _ _
    | endPhaseStart _ | returnPitch _ | endTurnCleanup _ =>
      cases actor <;> cases kind <;> exact False.elim hlf

/-- Under `WF` and `OwnerOk`, every legal action applies without failing. -/
theorem applyAction_isSome {s : GameState} {a : Action}
    (hwf : s.WF) (hok : s.OwnerOk) (hl : Legal s a) :
    (applyAction s a).isSome = true := by
  unfold applyAction
  split
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rename_i hnc hnt hnj hno hna hnd
    rcases hl.2 with hlf | hlc | hlt
    · exact applyFrame_isSome hwf hok hlf
    · unfold LegalConcede at hlc
      cases ha : a.actor <;> cases hk : a.kind <;> simp [ha, hk] at hlc
      exact False.elim (hnc _ ha hk)
    · unfold LegalTournament at hlt
      cases ha : a.actor <;> cases hk : a.kind <;> simp [ha, hk] at hlt
      · exact False.elim (hno _ ha hk)
      · exact False.elim (hna _ ha hk)
      · exact False.elim (hnd _ ha hk)
      · exact False.elim (hnt ha hk)
      · exact False.elim (hnj ha hk)

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
  | beginTurn =>
    dsimp only
    split
    · split <;> rfl
    · rfl
  | startPhaseWork _ => rfl
  | actionPhaseStart _ => rfl
  | playPayCost _ _ _ _ _ =>
    dsimp only
    split
    · rfl
    · split <;> rfl
  | resolveStack =>
    dsimp only
    split
    · split <;> rfl
    · rfl
  | finishResolve _ => rfl
  | combatStep cs _ =>
    cases cs with
    | layer | attack | reaction | close => rfl
    | defend =>
      dsimp only
      split
      · split <;> rfl
      · rfl
    | damage =>
      dsimp only
      split
      · split <;> rfl
      · rfl
    | resolution =>
      dsimp only
      split
      · split <;> rfl
      · rfl
  | gameStateProcess => rfl
  | run _ _ _ _ _ => rfl
  | optStep _ n =>
    cases n
    · rfl
    · dsimp only; split <;> rfl
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

/-- Every reachable state satisfies `WF`, `OwnerOk`, and `RollbackOk` (I3). -/
theorem Reachable.inv {s : GameState} (hr : Reachable s) :
    s.WF ∧ s.OwnerOk ∧ s.RollbackOk := by
  induction hr with
  | initial h =>
    have h1 := GameState.initial_inv h
    exact ⟨h1.1, h1.2, GameState.initial_rollbackOk h⟩
  | step _ hstep ih =>
    have hp := step_preserves ih.1 ih.2.1 ih.2.2 hstep
    exact ⟨hp.wf, hp.ownerOk, hp.rollbackOk⟩

/-- **I4** (global): no reachable state can ever trigger an internal engine error. -/
theorem Reachable.not_internal {s : GameState} (hr : Reachable s) (fuel : Nat) (a : Action)
    (msg : String) :
    Fab.step fuel s a ≠ .error (.internal msg) :=
  step_not_internal hr.inv.1 hr.inv.2.1

end Fab

end
