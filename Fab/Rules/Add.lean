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

end Fab

end
