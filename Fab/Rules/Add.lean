module

public import Fab.Rules.Move

/-!
# Adding objects to the game

`addObject` places a newly created object (during Start-of-Game setup or token/layer/attack-proxy
creation) into a valid zone, minting a fresh `ObjId` and `Timestamp` while preserving `WF` and
`OwnerOk`.
-/

@[expose] public section

namespace Fab

/-- Whether placing an object owned by `owner` into zone `z` respects Non-Arena ownership
(CR 3.0). -/
def Zone.allowsOwner (z : Zone) (owner : PlayerId) : Bool :=
  match z with
  | .player p k => k.isArena || p == owner
  | .combatChain => true
  | .stack => true

/-- Insert a new object into zone `z` at `pos`, minting `⟨s.nextId⟩` and `⟨s.nextTimestamp⟩`.
Returns `none` if `z` is not valid or violates Non-Arena ownership. -/
def addObject (s : GameState) (z : Zone) (o : Object) (pos : Pos := .top) :
    Option (GameState × ObjId) :=
  if z.Valid s.playerCount ∧ z.allowsOwner o.owner = true then
    let id : ObjId := ⟨s.nextId⟩
    let o' : Object := { o with timestamp := ⟨s.nextTimestamp⟩ }
    let s1 := s.setZone z (pos.insert id (s.zone z))
    some ({ s1 with
              objects := s.objects.insert id.n o',
              nextId := s.nextId + 1,
              nextTimestamp := s.nextTimestamp + 1 }, id)
  else
    none

/-- `addObject` preserves `WF`. -/
theorem addObject_wf {s s' : GameState} {z : Zone} {o : Object} {pos : Pos} {id : ObjId}
    (hwf : s.WF) (h : addObject s z o pos = some (s', id)) : s'.WF := by
  unfold addObject at h
  split at h
  · rename_i hcond
    obtain ⟨hz, _⟩ := hcond
    dsimp only at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hs', rfl⟩ := h
    have hcount : s'.playerCount = s.playerCount := by rw [← hs']; rfl
    have hnd_all := allZones_nodup s.playerCount
    have hz_eq : ∀ z', s'.zone z' = if z' = z then pos.insert ⟨s.nextId⟩ (s.zone z) else s.zone z' := by
      intro z'
      rw [← hs']
      by_cases he : z' = z
      · subst he; simp [GameState.zone, GameState.setZone]
      · simp only [he, ↓reduceIte]
        exact GameState.zone_setZone_ne s he _
    have hp1 := flatMap_split (allZones s.playerCount) s.zone z hz
    have hp2 := flatMap_split (allZones s.playerCount) s'.zone z hz
    have hrest : ((allZones s.playerCount).erase z).flatMap s'.zone =
        ((allZones s.playerCount).erase z).flatMap s.zone := by
      apply flatMap_one_congr (allZones s.playerCount) hnd_all
      intro x _ hxz
      rw [hz_eq x]
      simp [hxz]
    rw [hrest, hz_eq z] at hp2
    simp only [↓reduceIte] at hp2
    have hids : s'.zoneIds.Perm (⟨s.nextId⟩ :: s.zoneIds) := by
      unfold GameState.zoneIds
      rw [hcount]
      refine hp2.trans ?_
      refine ((Pos.insert_perm pos ⟨s.nextId⟩ (s.zone z)).append_right _).trans ?_
      exact List.Perm.cons _ hp1.symm
    have hfresh : (⟨s.nextId⟩ : ObjId) ∉ s.zoneIds := fun hm => by
      have := hwf.lt_nextId ⟨s.nextId⟩ hm
      dsimp only at this
      omega
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact hids.nodup_iff.mpr (List.nodup_cons.mpr ⟨hfresh, hwf.nodup⟩)
    · intro x hx
      rw [← hs']
      rcases List.mem_cons.mp (hids.mem_iff.mp hx) with rfl | hm
      · simp [Std.ExtTreeMap.mem_insert]
      · simp only [Std.ExtTreeMap.mem_insert]
        exact Or.inr (hwf.table_of_zone x hm)
    · intro k hk
      rw [← hs'] at hk
      simp only [Std.ExtTreeMap.mem_insert, Nat.compare_eq_eq] at hk
      rcases hk with rfl | hk
      · exact ⟨⟨s.nextId⟩, hids.symm.subset List.mem_cons_self, rfl⟩
      · obtain ⟨x, hx, hxk⟩ := hwf.zone_of_table k hk
        exact ⟨x, hids.symm.subset (List.mem_cons_of_mem _ hx), hxk⟩
    · intro x hx
      have hn : s'.nextId = s.nextId + 1 := by rw [← hs']
      rw [hn]
      rcases List.mem_cons.mp (hids.mem_iff.mp hx) with rfl | hm
      · dsimp only
        omega
      · have := hwf.lt_nextId x hm
        omega
    · intro k hk
      rw [← hs'] at hk
      simp only [GameState.setZone, Std.ExtTreeMap.mem_insert, Nat.compare_eq_eq] at hk
      rw [hcount]
      rcases hk with rfl | hk
      · exact ⟨z, hz, rfl⟩
      · exact hwf.zones_valid k hk
  · cases h

/-- `addObject` preserves `OwnerOk`. -/
theorem addObject_ownerOk {s s' : GameState} {z : Zone} {o : Object} {pos : Pos} {id : ObjId}
    (hwf : s.WF) (hok : s.OwnerOk) (h : addObject s z o pos = some (s', id)) : s'.OwnerOk := by
  unfold addObject at h
  split at h
  · rename_i hcond
    obtain ⟨hz, hallow⟩ := hcond
    dsimp only at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hs', rfl⟩ := h
    refine ⟨fun p k hk x hx ox hox => ?_⟩
    rw [← hs'] at hx hox
    by_cases hzp : Zone.player p k = z
    · subst hzp
      have hx' : x ∈ pos.insert ⟨s.nextId⟩ (s.zone (.player p k)) := by
        simpa [GameState.zone, GameState.setZone] using hx
      rw [Pos.mem_insert_iff] at hx'
      rcases hx' with rfl | hxold
      · simp only [GameState.obj?, Std.ExtTreeMap.getElem?_insert, Nat.compare_eq_eq,
          ↓reduceIte, Option.some.injEq] at hox
        subst hox
        simp only [Zone.allowsOwner, hk, Bool.false_or, beq_iff_eq] at hallow
        exact hallow.symm
      · have hxne : s.nextId ≠ x.n := by
          have := hwf.lt_nextId x (GameState.mem_zoneIds hz hxold)
          omega
        simp only [GameState.obj?, Std.ExtTreeMap.getElem?_insert, Nat.compare_eq_eq, hxne,
          ↓reduceIte] at hox
        exact hok.owner p k hk x hxold ox hox
    · have hzo : (s.setZone z (pos.insert ⟨s.nextId⟩ (s.zone z))).zone (.player p k) =
          s.zone (.player p k) := GameState.zone_setZone_ne s hzp _
      change x ∈ (s.setZone z (pos.insert ⟨s.nextId⟩ (s.zone z))).zone (.player p k) at hx
      rw [hzo] at hx
      have hvalid_pk : Zone.player p k ∈ allZones s.playerCount := by
        by_cases hm : Zone.player p k ∈ allZones s.playerCount
        · exact hm
        · exfalso
          have hmem_zones : (Zone.player p k).key ∈ s.zones := by
            unfold GameState.zone at hx
            cases hg : s.zones[(Zone.player p k).key]? with
            | none =>
              rw [Std.ExtTreeMap.getD_eq_getD_getElem?, hg] at hx
              simp at hx
            | some l =>
              exact Std.ExtTreeMap.mem_iff_isSome_getElem?.mpr (by rw [hg]; rfl)
          obtain ⟨z2, hz2, hzk⟩ := hwf.zones_valid _ hmem_zones
          exact hm ((Zone.key_inj hzk) ▸ hz2)
      have hxne : s.nextId ≠ x.n := by
        have := hwf.lt_nextId x (GameState.mem_zoneIds hvalid_pk hx)
        omega
      simp only [GameState.obj?, Std.ExtTreeMap.getElem?_insert, Nat.compare_eq_eq, hxne,
        ↓reduceIte] at hox
      exact hok.owner p k hk x hx ox hox
  · cases h

/-- Adding a non-physical object (token, layer, or attack-proxy with `o.kind.phys? = none`)
preserves `physIds` (I1). -/
theorem addObject_physIds {s s' : GameState} {z : Zone} {o : Object} {pos : Pos} {id : ObjId}
    (hwf : s.WF) (hnp : o.kind.phys? = none) (h : addObject s z o pos = some (s', id)) :
    s'.physIds.Perm s.physIds := by
  unfold addObject at h
  split at h
  · rename_i hcond
    obtain ⟨hz, _⟩ := hcond
    dsimp only at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hs', rfl⟩ := h
    have hcount : s'.playerCount = s.playerCount := by rw [← hs']; rfl
    have hnd_all := allZones_nodup s.playerCount
    have hz_eq : ∀ z', s'.zone z' = if z' = z then pos.insert ⟨s.nextId⟩ (s.zone z) else s.zone z' := by
      intro z'
      rw [← hs']
      by_cases he : z' = z
      · subst he; simp [GameState.zone, GameState.setZone]
      · simp only [he, ↓reduceIte]
        exact GameState.zone_setZone_ne s he _
    have hp1 := flatMap_split (allZones s.playerCount) s.zone z hz
    have hp2 := flatMap_split (allZones s.playerCount) s'.zone z hz
    have hrest : ((allZones s.playerCount).erase z).flatMap s'.zone =
        ((allZones s.playerCount).erase z).flatMap s.zone := by
      apply flatMap_one_congr (allZones s.playerCount) hnd_all
      intro x _ hxz
      rw [hz_eq x]
      simp [hxz]
    rw [hrest, hz_eq z] at hp2
    simp only [↓reduceIte] at hp2
    have hids : s'.zoneIds.Perm (⟨s.nextId⟩ :: s.zoneIds) := by
      unfold GameState.zoneIds
      rw [hcount]
      refine hp2.trans ?_
      refine ((Pos.insert_perm pos ⟨s.nextId⟩ (s.zone z)).append_right _).trans ?_
      exact List.Perm.cons _ hp1.symm
    have hnew : ((s'.obj? ⟨s.nextId⟩).bind (fun o => o.kind.phys?)) = none := by
      rw [← hs']
      simp [GameState.obj?, hnp]
    have hold : ∀ x ∈ s.zoneIds,
        ((s'.obj? x).bind (fun o => o.kind.phys?)) =
        ((s.obj? x).bind (fun o => o.kind.phys?)) := by
      intro x hx
      have hne : s.nextId ≠ x.n := by
        have := hwf.lt_nextId x hx
        omega
      rw [← hs']
      simp [GameState.obj?, Std.ExtTreeMap.getElem?_insert, hne]
    unfold GameState.physIds
    have hp_fm := hids.filterMap (fun id => (s'.obj? id).bind (fun o => o.kind.phys?))
    rw [List.filterMap_cons, hnew] at hp_fm
    dsimp only at hp_fm
    rw [filterMap_congr_mem s.zoneIds _ _ hold] at hp_fm
    exact hp_fm
  · cases h

/-- Remove a non-physical object (`o.kind.phys? = none`, such as a token, layer, or attack-proxy)
from the game when it ceases to exist (CR 1.4.3, 1.10.2). No-op if absent or physical. -/
def removeNonPhysObj (s : GameState) (id : ObjId) : GameState :=
  match s.locate id, s.obj? id with
  | some src, some o =>
    if o.kind.phys?.isNone then
      let s1 := s.setZone src ((s.zone src).erase id)
      { s1 with objects := s.objects.erase id.n }
    else
      s
  | _, _ => s

/-- `removeNonPhysObj` preserves `WF`. -/
theorem removeNonPhysObj_wf {s : GameState} (hwf : s.WF) (id : ObjId) :
    (removeNonPhysObj s id).WF := by
  unfold removeNonPhysObj
  cases hloc : s.locate id with
  | none => exact hwf
  | some src =>
    cases ho : s.obj? id with
    | none => exact hwf
    | some o =>
      dsimp only
      split
      · obtain ⟨hsrc, hid_mem⟩ := GameState.locate_spec hloc
        have hnd_all := allZones_nodup s.playerCount
        have hz_eq : ∀ z', ({ s.setZone src ((s.zone src).erase id) with
            objects := s.objects.erase id.n }).zone z' =
            if z' = src then (s.zone src).erase id else s.zone z' := by
          intro z'
          by_cases he : z' = src
          · subst he; simp [GameState.zone, GameState.setZone]
          · simp only [he, ↓reduceIte]
            exact GameState.zone_setZone_ne s he _
        have hp1 := flatMap_split (allZones s.playerCount) s.zone src hsrc
        have hp2 := flatMap_split (allZones s.playerCount)
          ({ s.setZone src ((s.zone src).erase id) with objects := s.objects.erase id.n }).zone
          src hsrc
        have hrest : ((allZones s.playerCount).erase src).flatMap
            ({ s.setZone src ((s.zone src).erase id) with objects := s.objects.erase id.n }).zone =
            ((allZones s.playerCount).erase src).flatMap s.zone := by
          apply flatMap_one_congr (allZones s.playerCount) hnd_all
          intro x _ hxs
          rw [hz_eq x]
          simp [hxs]
        rw [hrest, hz_eq src] at hp2
        simp only [↓reduceIte] at hp2
        have hp_src : (s.zone src).Perm (id :: (s.zone src).erase id) :=
          List.perm_cons_erase hid_mem
        have hids : s.zoneIds.Perm (id :: ({ s.setZone src ((s.zone src).erase id) with
            objects := s.objects.erase id.n }).zoneIds) := by
          unfold GameState.zoneIds
          change (allZones s.playerCount).flatMap s.zone |>.Perm
            (id :: (allZones s.playerCount).flatMap _)
          refine hp1.trans ?_
          refine (hp_src.append_right _).trans ?_
          exact List.Perm.cons id hp2.symm
        have hnd_cons : (id :: ({ s.setZone src ((s.zone src).erase id) with
            objects := s.objects.erase id.n }).zoneIds).Nodup :=
          hids.nodup_iff.mp hwf.nodup
        rw [List.nodup_cons] at hnd_cons
        refine ⟨hnd_cons.2, ?_, ?_, ?_, ?_⟩
        · intro x hx
          have hxne : id.n ≠ x.n := by
            intro heq
            have hxeq : id = x := by cases id; cases x; simp_all
            exact hnd_cons.1 (hxeq ▸ hx)
          have hxold : x ∈ s.zoneIds := hids.symm.subset (List.mem_cons_of_mem _ hx)
          simp only [Std.ExtTreeMap.mem_erase, ne_eq, Nat.compare_eq_eq]
          exact ⟨hxne, hwf.table_of_zone x hxold⟩
        · intro k hk
          simp only [Std.ExtTreeMap.mem_erase, ne_eq, Nat.compare_eq_eq] at hk
          obtain ⟨x, hx, hxk⟩ := hwf.zone_of_table k hk.2
          rcases List.mem_cons.mp (hids.mem_iff.mp hx) with rfl | hx'
          · exact False.elim (hk.1 hxk)
          · exact ⟨x, hx', hxk⟩
        · intro x hx
          exact hwf.lt_nextId x (hids.symm.subset (List.mem_cons_of_mem _ hx))
        · intro k hk
          simp only [GameState.setZone, Std.ExtTreeMap.mem_insert, Nat.compare_eq_eq] at hk
          rcases hk with rfl | hk
          · exact ⟨src, hsrc, rfl⟩
          · exact hwf.zones_valid k hk
      · exact hwf

/-- `removeNonPhysObj` preserves `OwnerOk`. -/
theorem removeNonPhysObj_ownerOk {s : GameState} (hok : s.OwnerOk) (id : ObjId) :
    (removeNonPhysObj s id).OwnerOk := by
  unfold removeNonPhysObj
  cases hloc : s.locate id with
  | none => exact hok
  | some src =>
    cases ho : s.obj? id with
    | none => exact hok
    | some o =>
      dsimp only
      split
      · refine ⟨fun p k hk x hx ox hox => ?_⟩
        have hne : id.n ≠ x.n := by
          intro heq
          simp only [GameState.obj?, Std.ExtTreeMap.getElem?_erase, Nat.compare_eq_eq, heq,
            ↓reduceIte] at hox
          cases hox
        simp only [GameState.obj?, Std.ExtTreeMap.getElem?_erase, Nat.compare_eq_eq, hne,
          ↓reduceIte] at hox
        have hx_old : x ∈ s.zone (.player p k) := by
          by_cases hzs : Zone.player p k = src
          · subst hzs
            have : x ∈ (s.zone (.player p k)).erase id := by
              simpa [GameState.zone, GameState.setZone] using hx
            exact List.mem_of_mem_erase this
          · have hzo := GameState.zone_setZone_ne s hzs ((s.zone src).erase id)
            change x ∈ (s.setZone src ((s.zone src).erase id)).zone (.player p k) at hx
            rw [hzo] at hx
            exact hx
        exact hok.owner p k hk x hx_old ox hox
      · exact hok

/-- `removeNonPhysObj` preserves `physIds` (I1). -/
theorem removeNonPhysObj_physIds {s : GameState} (hwf : s.WF) (id : ObjId) :
    (removeNonPhysObj s id).physIds.Perm s.physIds := by
  unfold removeNonPhysObj
  cases hloc : s.locate id with
  | none => exact List.Perm.refl _
  | some src =>
    cases ho : s.obj? id with
    | none => exact List.Perm.refl _
    | some o =>
      dsimp only
      split
      · rename_i hnone
        have hnp : o.kind.phys? = none := by
          cases hp : o.kind.phys? with
          | none => rfl
          | some _ => rw [hp] at hnone; simp at hnone
        obtain ⟨hsrc, hid_mem⟩ := GameState.locate_spec hloc
        have hnd_all := allZones_nodup s.playerCount
        let s' : GameState :=
          { s.setZone src ((s.zone src).erase id) with objects := s.objects.erase id.n }
        have hz_eq : ∀ z', s'.zone z' = if z' = src then (s.zone src).erase id else s.zone z' := by
          intro z'
          by_cases he : z' = src
          · subst he; simp [s', GameState.zone, GameState.setZone]
          · simp only [he, ↓reduceIte]
            exact GameState.zone_setZone_ne s he _
        have hp1 := flatMap_split (allZones s.playerCount) s.zone src hsrc
        have hp2 := flatMap_split (allZones s.playerCount) s'.zone src hsrc
        have hrest : ((allZones s.playerCount).erase src).flatMap s'.zone =
            ((allZones s.playerCount).erase src).flatMap s.zone := by
          apply flatMap_one_congr (allZones s.playerCount) hnd_all
          intro x _ hxs
          rw [hz_eq x]
          simp [hxs]
        rw [hrest, hz_eq src] at hp2
        simp only [↓reduceIte] at hp2
        have hids : s.zoneIds.Perm (id :: s'.zoneIds) := by
          unfold GameState.zoneIds
          change (allZones s.playerCount).flatMap s.zone |>.Perm
            (id :: (allZones s.playerCount).flatMap s'.zone)
          refine hp1.trans ?_
          refine ((List.perm_cons_erase hid_mem).append_right _).trans ?_
          exact List.Perm.cons id hp2.symm
        have hnd_cons : (id :: s'.zoneIds).Nodup := hids.nodup_iff.mp hwf.nodup
        rw [List.nodup_cons] at hnd_cons
        have hold : ∀ x ∈ s'.zoneIds,
            ((s'.obj? x).bind (fun o => o.kind.phys?)) =
            ((s.obj? x).bind (fun o => o.kind.phys?)) := by
          intro x hx
          have hne : id.n ≠ x.n := by
            intro heq
            have hxeq : id = x := by cases id; cases x; simp_all
            exact hnd_cons.1 (hxeq ▸ hx)
          simp [s', GameState.obj?, Std.ExtTreeMap.getElem?_erase, hne]
        have hid_none : ((s.obj? id).bind (fun o => o.kind.phys?)) = none := by
          simp [ho, hnp]
        change s'.physIds.Perm s.physIds
        unfold GameState.physIds
        have hp_fm := hids.filterMap (fun x => (s.obj? x).bind (fun o => o.kind.phys?))
        rw [List.filterMap_cons, hid_none] at hp_fm
        dsimp only at hp_fm
        rw [filterMap_congr_mem s'.zoneIds _ _ hold]
        exact hp_fm.symm
      · exact List.Perm.refl _

/-- `removeNonPhysObj` preserves `config` and `playRollback`. -/
theorem removeNonPhysObj_meta (s : GameState) (id : ObjId) :
    (removeNonPhysObj s id).config = s.config ∧
    (removeNonPhysObj s id).playRollback = s.playRollback := by
  unfold removeNonPhysObj
  cases s.locate id with
  | none => exact ⟨rfl, rfl⟩
  | some _ =>
    cases s.obj? id with
    | none => exact ⟨rfl, rfl⟩
    | some _ =>
      dsimp only
      split <;> exact ⟨rfl, rfl⟩

end Fab

end
