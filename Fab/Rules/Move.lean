module

public import Fab.State.GameState
public import Fab.Basic.ListLemmas

/-!
# Moving objects between zones

`moveObj` is the single primitive that moves an object from one zone to another (design.md §3, P6).
Its structural and physical-card invariants (I1, I2, `WF`, `OwnerOk`) are proved once here and
carry over to every rule and card action built on it.

Crossing the Arena boundary or moving between Non-Arena zones mints a fresh `ObjId` and resets
transient state (CR 3.0.9). Moving between two Arena zones (for example, Equipment defending on
the Combat Chain and returning to its armor zone on Close Step) preserves `ObjId`, counters, and
tapped state (CR 3.0.9, 7.7).
-/

@[expose] public section

namespace Fab

/-- Where in the destination zone list an object is inserted. For ordered zones (`deck`, `stack`,
`graveyard`), `top` is the head. -/
inductive Pos where
  /-- Insert at the head (top of deck, top of stack). -/
  | top
  /-- Insert at the end, for example bottom of deck during End Phase pitch return (CR 4.4.3c). -/
  | bottom
deriving DecidableEq, Repr, Hashable

/-- Insert an object identifier at the requested end of a zone list. -/
def Pos.insert : Pos → ObjId → List ObjId → List ObjId
  | .top, id, l => id :: l
  | .bottom, id, l => l ++ [id]

/-- Inserting produces a permutation of consing at the head. -/
theorem Pos.insert_perm (pos : Pos) (id : ObjId) (l : List ObjId) :
    (pos.insert id l).Perm (id :: l) := by
  cases pos
  · exact List.Perm.refl _
  · simp [Pos.insert]

/-- The inserted identifier is a member of the resulting list. -/
theorem Pos.mem_insert (pos : Pos) (id : ObjId) (l : List ObjId) :
    id ∈ pos.insert id l := by
  cases pos <;> simp [Pos.insert]

/-- Every member of `pos.insert id l` is either `id` or in `l`. -/
theorem Pos.mem_insert_iff (pos : Pos) (id x : ObjId) (l : List ObjId) :
    x ∈ pos.insert id l ↔ x = id ∨ x ∈ l := by
  cases pos <;> simp [Pos.insert, or_comm]

/-- Length increases by 1 on insert. -/
theorem Pos.insert_length (pos : Pos) (id : ObjId) (l : List ObjId) :
    (pos.insert id l).length = l.length + 1 := by
  cases pos <;> simp [Pos.insert]

namespace GameState

/-- Locate the zone currently holding `id`. -/
def locate (s : GameState) (id : ObjId) : Option Zone :=
  (allZones s.playerCount).find? (fun z => (s.zone z).contains id)

/-- A located object lies in a valid zone and is a member of that zone's list. -/
theorem locate_spec {s : GameState} {id : ObjId} {z : Zone} (h : s.locate id = some z) :
    z ∈ allZones s.playerCount ∧ id ∈ s.zone z := by
  unfold locate at h
  refine ⟨List.mem_of_find?_eq_some h, ?_⟩
  simpa using List.find?_some h

/-- An object in a valid zone belongs to `zoneIds`. -/
theorem mem_zoneIds {s : GameState} {z : Zone} {id : ObjId}
    (hz : z ∈ allZones s.playerCount) (h : id ∈ s.zone z) : id ∈ s.zoneIds := by
  unfold zoneIds
  exact List.mem_flatMap.mpr ⟨z, hz, h⟩

/-- Two distinct zone writes leave all other zones unchanged. -/
theorem zone_move {s : GameState} {src dst : Zone} (hne : src ≠ dst)
    (l1 l2 : List ObjId) (z : Zone) :
    ((s.setZone src l1).setZone dst l2).zone z =
      if z = dst then l2 else if z = src then l1 else s.zone z := by
  by_cases h1 : z = dst
  · subst h1; simp [zone_setZone_self]
  · by_cases h2 : z = src
    · subst h2
      rw [zone_setZone_ne _ h1, zone_setZone_self]
      simp [h1]
    · rw [zone_setZone_ne _ h1, zone_setZone_ne _ h2]
      simp [h1, h2]

end GameState

/-- Move `id` to `dst` at `pos` (with optional `faceDown` state on boundary crossing).
Returns the updated state and resulting `ObjId`. Preserves `ObjId` and transient state when both
source and normalized destination are Arena zones (CR 3.0.9). -/
def moveObj (s : GameState) (id : ObjId) (dst : Zone) (pos : Pos := .top)
    (faceDown : Bool := false) : Option (GameState × ObjId) :=
  match s.locate id, s.obj? id with
  | some src, some o =>
    let dst := Zone.normalize o.owner dst
    if src = dst ∨ ¬ dst.Valid s.playerCount then none
    else if Zone.crosses src dst then
      let id' : ObjId := ⟨s.nextId⟩
      let o' : Object := o.resetOnZoneChange ⟨s.nextTimestamp⟩ faceDown
      let s1 := (s.setZone src ((s.zone src).erase id)).setZone dst (pos.insert id' (s.zone dst))
      some ({ s1 with
                objects := (s.objects.erase id.n).insert id'.n o',
                nextId := s.nextId + 1,
                nextTimestamp := s.nextTimestamp + 1 }, id')
    else
      let s1 := (s.setZone src ((s.zone src).erase id)).setZone dst (pos.insert id (s.zone dst))
      some (s1, id)
  | _, _ => none

/-- Everything outside zones, objects, counters, pools, and hero life is unchanged
(config, cards, turn, active, and future metadata fields). -/
def SameMeta (s s' : GameState) : Prop :=
  { s' with
      objects := s.objects
      zones := s.zones
      nextId := s.nextId
      nextTimestamp := s.nextTimestamp
      pools := s.pools
      heroLife := s.heroLife } = s

namespace SameMeta

/-- Reflexivity of `SameMeta`. -/
theorem refl (s : GameState) : SameMeta s s := rfl

/-- Transitivity of `SameMeta`. -/
theorem trans {s s' s'' : GameState} (h1 : SameMeta s s') (h2 : SameMeta s' s'') :
    SameMeta s s'' := by
  unfold SameMeta at *
  have := congrArg (fun x : GameState =>
    ({ x with
         objects := s.objects, zones := s.zones, nextId := s.nextId,
         nextTimestamp := s.nextTimestamp, pools := s.pools, heroLife := s.heroLife } :
      GameState)) h2
  simp only at this
  rw [← h1]
  exact this

/-- `config` is preserved by `SameMeta`. -/
theorem config {s s' : GameState} (h : SameMeta s s') : s'.config = s.config := by
  unfold SameMeta at h
  have h2 := congrArg GameState.config h
  exact h2

/-- `cards` (`CardDB`) is preserved by `SameMeta`. -/
theorem cards {s s' : GameState} (h : SameMeta s s') : s'.cards = s.cards := by
  unfold SameMeta at h
  have h2 := congrArg GameState.cards h
  exact h2

/-- `turn` is preserved by `SameMeta`. -/
theorem turn {s s' : GameState} (h : SameMeta s s') : s'.turn = s.turn := by
  unfold SameMeta at h
  have h2 := congrArg GameState.turn h
  exact h2

/-- `active` is preserved by `SameMeta`. -/
theorem active {s s' : GameState} (h : SameMeta s s') : s'.active = s.active := by
  unfold SameMeta at h
  have h2 := congrArg GameState.active h
  exact h2

/-- `pending` is preserved by `SameMeta`. -/
theorem pending {s s' : GameState} (h : SameMeta s s') : s'.pending = s.pending := by
  unfold SameMeta at h
  have h2 := congrArg GameState.pending h
  exact h2

/-- `turnOrder` is preserved by `SameMeta`. -/
theorem turnOrder {s s' : GameState} (h : SameMeta s s') : s'.turnOrder = s.turnOrder := by
  unfold SameMeta at h
  have h2 := congrArg GameState.turnOrder h
  exact h2

/-- `phase` is preserved by `SameMeta`. -/
theorem phase {s s' : GameState} (h : SameMeta s s') : s'.phase = s.phase := by
  unfold SameMeta at h
  have h2 := congrArg GameState.phase h
  exact h2

/-- `result` is preserved by `SameMeta`. -/
theorem result {s s' : GameState} (h : SameMeta s s') : s'.result = s.result := by
  unfold SameMeta at h
  have h2 := congrArg GameState.result h
  exact h2

end SameMeta

namespace GameState

/-- Permutation characterization of `zoneIds` before and after a single object move. -/
theorem zoneIds_move {s s2 : GameState} {id id' : ObjId} {src dst : Zone} {pos : Pos}
    (hcfg : s2.config = s.config)
    (hsrc : src ∈ allZones s.playerCount) (hid : id ∈ s.zone src)
    (hdst : dst ∈ allZones s.playerCount) (hne : src ≠ dst)
    (hzones : s2.zones = ((s.setZone src ((s.zone src).erase id)).setZone dst
      (pos.insert id' (s.zone dst))).zones) :
    ∃ core : List ObjId, s.zoneIds.Perm (id :: core) ∧ s2.zoneIds.Perm (id' :: core) ∧
      (∀ x ∈ core, x ∈ s.zoneIds) := by
  have hz2 : ∀ z, s2.zone z =
      if z = dst then pos.insert id' (s.zone dst)
      else if z = src then (s.zone src).erase id else s.zone z := by
    intro z
    have : s2.zone z = ((s.setZone src ((s.zone src).erase id)).setZone dst
        (pos.insert id' (s.zone dst))).zone z := by simp [zone, hzones]
    rw [this, zone_move hne]
  have hcount : s2.playerCount = s.playerCount := by simp [playerCount, hcfg]
  have hnd := allZones_nodup s.playerCount
  obtain ⟨L, hL⟩ : ∃ L, L = allZones s.playerCount := ⟨_, rfl⟩
  rw [← hL] at hnd hsrc hdst
  have e1 := flatMap_two L s.zone src dst hsrc hdst hne
  have e2 := flatMap_two L s2.zone src dst hsrc hdst hne
  have hrest : ((L.erase src).erase dst).flatMap s2.zone =
      ((L.erase src).erase dst).flatMap s.zone := by
    apply flatMap_two_congr L hnd
    intro x _ hxa hxb
    rw [hz2 x]
    simp [hxa, hxb]
  rw [hrest] at e2
  have hA2 : s2.zone src = (s.zone src).erase id := by rw [hz2 src]; simp [hne]
  have hB2 : s2.zone dst = pos.insert id' (s.zone dst) := by rw [hz2 dst]; simp
  rw [hA2, hB2] at e2
  obtain ⟨R, hR⟩ : ∃ R, R = ((L.erase src).erase dst).flatMap s.zone := ⟨_, rfl⟩
  rw [← hR] at e1 e2
  have h1 : s.zoneIds.Perm (id :: ((s.zone src).erase id ++ (s.zone dst ++ R))) := by
    unfold zoneIds
    rw [← hL]
    refine e1.trans ?_
    exact (List.perm_cons_erase hid).append_right _
  have h2 : s2.zoneIds.Perm (id' :: ((s.zone src).erase id ++ (s.zone dst ++ R))) := by
    unfold zoneIds
    rw [hcount, ← hL]
    refine e2.trans ?_
    refine (((Pos.insert_perm pos id' (s.zone dst)).append_right R).append_left _).trans ?_
    exact List.perm_middle
  exact ⟨_, h1, h2, fun x hx => h1.symm.subset (List.mem_cons_of_mem _ hx)⟩

/-- Structural well-formedness preservation for any single-object move. -/
theorem wf_of_move {s s2 : GameState} {id id' : ObjId} {src dst : Zone} {pos : Pos}
    (hwf : s.WF) (hcfg : s2.config = s.config)
    (hsrc : src ∈ allZones s.playerCount) (hid : id ∈ s.zone src)
    (hdst : dst ∈ allZones s.playerCount) (hne : src ≠ dst)
    (hzones : s2.zones = ((s.setZone src ((s.zone src).erase id)).setZone dst
      (pos.insert id' (s.zone dst))).zones)
    (hobj : ∀ k, k ∈ s2.objects ↔ (k ∈ s.objects ∧ k ≠ id.n) ∨ k = id'.n)
    (hid' : id' = id ∨ id'.n = s.nextId)
    (hnext : s.nextId ≤ s2.nextId ∧ (id' = id ∨ id'.n < s2.nextId)) : s2.WF := by
  obtain ⟨core, h1, h2, hcore⟩ := zoneIds_move hcfg hsrc hid hdst hne hzones
  have hcount : s2.playerCount = s.playerCount := by simp [playerCount, hcfg]
  have hnd : (id :: core).Nodup := h1.nodup_iff.mp hwf.nodup
  rw [List.nodup_cons] at hnd
  have hlt : ∀ x ∈ core, x.n < s.nextId := fun x hx => hwf.lt_nextId x (hcore x hx)
  have hid'core : id' ∉ core := by
    rcases hid' with rfl | h
    · exact hnd.1
    · intro hm
      have := hlt id' hm
      omega
  have hne_id : ∀ x ∈ core, x.n ≠ id.n := fun x hx e => by
    have : x = id := by cases x; cases id; simp_all
    exact hnd.1 (this ▸ hx)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact h2.nodup_iff.mpr (List.nodup_cons.mpr ⟨hid'core, hnd.2⟩)
  · intro x hx
    rcases List.mem_cons.mp (h2.mem_iff.mp hx) with rfl | hm
    · exact (hobj _).mpr (Or.inr rfl)
    · exact (hobj _).mpr (Or.inl ⟨hwf.table_of_zone x (hcore x hm), hne_id x hm⟩)
  · intro k hk
    rcases (hobj k).mp hk with ⟨hk1, hk2⟩ | rfl
    · obtain ⟨x, hx, hxk⟩ := hwf.zone_of_table k hk1
      rcases List.mem_cons.mp (h1.mem_iff.mp hx) with rfl | hm
      · exact absurd hxk.symm hk2
      · exact ⟨x, h2.mem_iff.mpr (List.mem_cons_of_mem _ hm), hxk⟩
    · exact ⟨id', h2.symm.subset List.mem_cons_self, rfl⟩
  · intro x hx
    rcases List.mem_cons.mp (h2.mem_iff.mp hx) with rfl | hm
    · rcases hnext.2 with h | h
      · have := hwf.lt_nextId id (h1.symm.subset List.mem_cons_self)
        rw [h]
        omega
      · exact h
    · have := hlt x hm
      omega
  · intro k hk
    rw [hzones] at hk
    simp only [setZone, Std.ExtTreeMap.mem_insert] at hk
    rw [hcount]
    rcases hk with hk | hk | hk
    · exact ⟨dst, hdst, Nat.compare_eq_eq.mp hk⟩
    · exact ⟨src, hsrc, Nat.compare_eq_eq.mp hk⟩
    · exact hwf.zones_valid k hk

/-- In a well-formed game, an object appears in at most one valid zone (I2 position uniqueness). -/
theorem zone_unique {s : GameState} (hwf : s.WF) {z z' : Zone} {id : ObjId}
    (hz : z ∈ allZones s.playerCount) (hz' : z' ∈ allZones s.playerCount)
    (h : id ∈ s.zone z) (h' : id ∈ s.zone z') : z' = z := by
  by_cases hne : z' = z
  · exact hne
  exfalso
  have hperm := flatMap_split (allZones s.playerCount) s.zone z hz
  have hnd : (s.zone z ++ ((allZones s.playerCount).erase z).flatMap s.zone).Nodup :=
    (hperm.nodup_iff).mp hwf.nodup
  rw [List.nodup_append] at hnd
  have hmem : id ∈ ((allZones s.playerCount).erase z).flatMap s.zone :=
    List.mem_flatMap.mpr ⟨z', (List.mem_erase_of_ne hne).mpr hz', h'⟩
  exact hnd.2.2 id h id hmem rfl

/-- In a well-formed game, `locate` finds the unique zone holding `id`. -/
theorem locate_eq {s : GameState} (hwf : s.WF) {z : Zone} {id : ObjId}
    (hz : z ∈ allZones s.playerCount) (h : id ∈ s.zone z) : s.locate id = some z := by
  unfold locate
  apply find?_eq_some_of_unique _ _ z hz
  intro x hx
  simp only [List.contains_iff_mem]
  exact ⟨fun hm => zone_unique hwf hz hx h hm, fun e => e ▸ h⟩

end GameState

/-- Structured postcondition describing everything `moveObj` performs. -/
structure MoveSpec (s s' : GameState) (id id' : ObjId) (pos : Pos) (src dst : Zone) : Prop where
  /-- Source is a valid zone. -/
  src_mem : src ∈ allZones s.playerCount
  /-- Object was in source. -/
  id_mem : id ∈ s.zone src
  /-- Normalized destination is a valid zone. -/
  dst_mem : dst ∈ allZones s.playerCount
  /-- Source and normalized destination differ. -/
  ne : src ≠ dst
  /-- Config is unchanged. -/
  config : s'.config = s.config
  /-- Zones update only at `src` and `dst`. -/
  zones : s'.zones = ((s.setZone src ((s.zone src).erase id)).setZone dst
    (pos.insert id' (s.zone dst))).zones
  /-- New identifier is either unchanged (Arena move) or `⟨s.nextId⟩` (boundary crossing). -/
  fresh : id' = id ∨ id'.n = s.nextId
  /-- Counter monotonicity and freshness bound. -/
  next : s.nextId ≤ s'.nextId ∧ (id' = id ∨ id'.n < s'.nextId)
  /-- Object table domain loses `id` and gains `id'`. -/
  objects : ∀ k, k ∈ s'.objects ↔ (k ∈ s.objects ∧ k ≠ id.n) ∨ k = id'.n
  /-- Other object entries are untouched. -/
  objects_other : ∀ k, k ≠ id.n → k ≠ id'.n → s'.objects[k]? = s.objects[k]?
  /-- Object kind (and therefore `PhysId`) is preserved. -/
  kind : (s'.objects[id'.n]?).map (·.kind) = (s.objects[id.n]?).map (·.kind)
  /-- Moved object sits in destination. -/
  id'_mem : id' ∈ s'.zone dst
  /-- `id'` changes only when crossing the Arena boundary or moving between Non-Arena zones. -/
  crosses : Zone.crosses src dst = true ∨ id' = id
  /-- `locate` returned `src`. -/
  locate : s.locate id = some src
  /-- Owner is preserved. -/
  owner : (s'.objects[id'.n]?).map (·.owner) = (s.objects[id.n]?).map (·.owner)
  /-- Asset pools are untouched. -/
  pools : s'.pools = s.pools
  /-- Hero life totals are untouched. -/
  heroLife : s'.heroLife = s.heroLife
  /-- All other metadata is unchanged. -/
  other : SameMeta s s'

/-- Full specification of a successful `moveObj`, including the normalized destination. -/
theorem moveObj_spec_dst {s s' : GameState} {id id' : ObjId} {dst : Zone} {pos : Pos}
    {fd : Bool} (h : moveObj s id dst pos fd = some (s', id')) :
    ∃ src d, MoveSpec s s' id id' pos src d ∧
      ∃ o, s.obj? id = some o ∧ d = Zone.normalize o.owner dst := by
  unfold moveObj at h
  split at h
  · rename_i src o hloc hobj
    obtain ⟨hsrc, hid⟩ := GameState.locate_spec hloc
    simp only at h
    split at h
    · exact absurd h (by simp)
    · rename_i hcond
      simp only [not_or, Decidable.not_not] at hcond
      obtain ⟨hne, hvalid⟩ := hcond
      have hobj_id : id.n ∈ s.objects := by
        simp only [GameState.obj?] at hobj
        rw [Std.ExtTreeMap.mem_iff_isSome_getElem?, hobj]
        rfl
      split at h
      · rename_i hcr
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨src, Zone.normalize o.owner dst, ?_, o, hobj, rfl⟩
        refine ⟨hsrc, hid, hvalid, hne, rfl, rfl, Or.inr rfl, ⟨by simp, Or.inr (by simp)⟩,
          ?_, ?_, ?_, ?_, Or.inl hcr, hloc, ?_, rfl, rfl, rfl⟩
        · intro k
          simp only [Std.ExtTreeMap.mem_insert, Std.ExtTreeMap.mem_erase, Nat.compare_eq_eq,
            ne_eq]
          constructor
          · rintro (h | ⟨h1, h2⟩)
            · exact Or.inr h.symm
            · exact Or.inl ⟨h2, fun e => h1 e.symm⟩
          · rintro (⟨h1, h2⟩ | h)
            · exact Or.inr ⟨fun e => h2 e.symm, h1⟩
            · exact Or.inl h.symm
        · intro k hk1 hk2
          have hk2' : s.nextId ≠ k := fun e => hk2 e.symm
          have hk1' : id.n ≠ k := fun e => hk1 e.symm
          simp [Std.ExtTreeMap.getElem?_insert, Std.ExtTreeMap.getElem?_erase, hk1', hk2']
        · have hobj' : s.objects[id.n]? = some o := hobj
          simp [hobj', Object.resetOnZoneChange]
        · show _ ∈ ((s.setZone _ _).setZone _ _).zone _
          rw [GameState.zone_move hne]
          simpa using Pos.mem_insert pos _ _
        · have hobj' : s.objects[id.n]? = some o := hobj
          simp [hobj', Object.resetOnZoneChange]
      · rename_i hcr
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨src, Zone.normalize o.owner dst, ?_, o, hobj, rfl⟩
        refine ⟨hsrc, hid, hvalid, hne, rfl, rfl, Or.inl rfl, ⟨Nat.le_refl _, Or.inl rfl⟩,
          ?_, ?_, rfl, ?_, Or.inr rfl, hloc, rfl, rfl, rfl, rfl⟩
        · intro k
          change k ∈ s.objects ↔ _
          by_cases hk : k = id.n
          · subst hk; simp [hobj_id]
          · simp [hk]
        · intro k _ _
          rfl
        · show _ ∈ ((s.setZone _ _).setZone _ _).zone _
          rw [GameState.zone_move hne]
          simpa using Pos.mem_insert pos _ _
  · exact absurd h (by simp)

/-- Simplified specification of a successful `moveObj`. -/
theorem moveObj_spec {s s' : GameState} {id id' : ObjId} {dst : Zone} {pos : Pos} {fd : Bool}
    (h : moveObj s id dst pos fd = some (s', id')) :
    ∃ src d, MoveSpec s s' id id' pos src d := by
  obtain ⟨src, d, hs, -⟩ := moveObj_spec_dst h
  exact ⟨src, d, hs⟩

namespace MoveSpec

variable {s s' : GameState} {id id' : ObjId} {pos : Pos} {src dst : Zone}

/-- Destination zone after `moveObj`. -/
theorem zone_dst (hs : MoveSpec s s' id id' pos src dst) :
    s'.zone dst = pos.insert id' (s.zone dst) := by
  have : s'.zone dst = ((s.setZone src ((s.zone src).erase id)).setZone dst
      (pos.insert id' (s.zone dst))).zone dst := by simp [GameState.zone, hs.zones]
  rw [this, GameState.zone_move hs.ne]
  simp

/-- Source zone after `moveObj`. -/
theorem zone_src (hs : MoveSpec s s' id id' pos src dst) :
    s'.zone src = (s.zone src).erase id := by
  have : s'.zone src = ((s.setZone src ((s.zone src).erase id)).setZone dst
      (pos.insert id' (s.zone dst))).zone src := by simp [GameState.zone, hs.zones]
  rw [this, GameState.zone_move hs.ne]
  simp [hs.ne]

/-- Every zone other than `src` and `dst` is unchanged. -/
theorem zone_other (hs : MoveSpec s s' id id' pos src dst) {z : Zone} (h1 : z ≠ src)
    (h2 : z ≠ dst) : s'.zone z = s.zone z := by
  have : s'.zone z = ((s.setZone src ((s.zone src).erase id)).setZone dst
      (pos.insert id' (s.zone dst))).zone z := by simp [GameState.zone, hs.zones]
  rw [this, GameState.zone_move hs.ne]
  simp [h1, h2]

end MoveSpec

/-- `moveObj` preserves structural well-formedness `WF` (I3 one step). -/
theorem moveObj_wf {s s' : GameState} {id id' : ObjId} {dst : Zone} {pos : Pos} {fd : Bool}
    (hwf : s.WF) (h : moveObj s id dst pos fd = some (s', id')) : s'.WF := by
  obtain ⟨src, d, hs⟩ := moveObj_spec h
  exact GameState.wf_of_move hwf hs.config hs.src_mem hs.id_mem hs.dst_mem hs.ne hs.zones
    hs.objects hs.fresh hs.next

/-- `moveObj` preserves the multiset of physical card identifiers (I1 one step). -/
theorem moveObj_physIds {s s' : GameState} {id id' : ObjId} {dst : Zone} {pos : Pos} {fd : Bool}
    (hwf : s.WF) (h : moveObj s id dst pos fd = some (s', id')) :
    s'.physIds.Perm s.physIds := by
  obtain ⟨src, d, hs⟩ := moveObj_spec h
  obtain ⟨core, h1, h2, hcore⟩ :=
    GameState.zoneIds_move hs.config hs.src_mem hs.id_mem hs.dst_mem hs.ne hs.zones
  have hnd : (id :: core).Nodup := h1.nodup_iff.mp hwf.nodup
  rw [List.nodup_cons] at hnd
  have hne_id : ∀ x ∈ core, x.n ≠ id.n := fun x hx e => by
    have : x = id := by cases x; cases id; simp_all
    exact hnd.1 (this ▸ hx)
  have hne_id' : ∀ x ∈ core, x.n ≠ id'.n := fun x hx e => by
    rcases hs.fresh with h3 | h3
    · exact hne_id x hx (by rw [e, h3])
    · have := hwf.lt_nextId x (hcore x hx)
      omega
  have hobj_eq : ∀ x ∈ core, s'.obj? x = s.obj? x := fun x hx => by
    simp only [GameState.obj?]
    exact hs.objects_other x.n (hne_id x hx) (hne_id' x hx)
  have hid_eq : ((s'.obj? id').bind (·.kind.phys?)) = ((s.obj? id).bind (·.kind.phys?)) := by
    have hk := hs.kind
    simp only [GameState.obj?]
    rcases ha : s.objects[id.n]? with _ | o <;> rcases hb : s'.objects[id'.n]? with _ | o' <;>
      simp_all
  have hfm : core.filterMap (fun x => (s'.obj? x).bind (·.kind.phys?)) =
      core.filterMap (fun x => (s.obj? x).bind (·.kind.phys?)) := by
    apply filterMap_congr_mem
    intro x hx
    rw [hobj_eq x hx]
  have heq : (id' :: core).filterMap (fun x => (s'.obj? x).bind (·.kind.phys?)) =
      (id :: core).filterMap (fun x => (s.obj? x).bind (·.kind.phys?)) := by
    simp only [List.filterMap_cons, hid_eq, hfm]
  unfold GameState.physIds
  have p1 := List.Perm.filterMap (fun x => (s'.obj? x).bind (·.kind.phys?)) h2
  rw [heq] at p1
  exact p1.trans (List.Perm.filterMap _ h1).symm

/-- `moveObj` preserves Non-Arena ownership `OwnerOk` (CR 3.0). -/
theorem moveObj_ownerOk {s s' : GameState} {id id' : ObjId} {dst : Zone} {pos : Pos} {fd : Bool}
    (hwf : s.WF) (hok : s.OwnerOk) (h : moveObj s id dst pos fd = some (s', id')) :
    s'.OwnerOk := by
  obtain ⟨src, d, hs, o0, ho0, hd⟩ := moveObj_spec_dst h
  refine ⟨fun p k hk x hx o hox => ?_⟩
  by_cases hzd : Zone.player p k = d
  · rw [hzd, hs.zone_dst, Pos.mem_insert_iff] at hx
    rcases hx with rfl | hxold
    · have hown : o.owner = o0.owner := by
        have h1 := hs.owner
        simp only [GameState.obj?] at ho0 hox
        rw [hox, ho0] at h1
        simpa using h1
      rw [hown]
      have hnorm : Zone.normalize o0.owner dst = Zone.player p k := hzd.symm ▸ hd.symm
      cases dst with
      | combatChain => simp [Zone.normalize] at hnorm
      | stack => simp [Zone.normalize] at hnorm
      | player q l =>
        simp only [Zone.normalize] at hnorm
        split at hnorm
        · rename_i har
          cases hnorm
          rw [har] at hk
          cases hk
        · cases hnorm
          rfl
    · rw [← hzd] at hxold
      have hxne : x ≠ id' := by
        intro heq
        subst heq
        rcases hs.fresh with rfl | hfresh
        · have hsame := GameState.zone_unique hwf hs.src_mem (hzd ▸ hs.dst_mem) hs.id_mem hxold
          exact hs.ne (hsame.symm.trans hzd)
        · have := hwf.lt_nextId x (GameState.mem_zoneIds (hzd ▸ hs.dst_mem) hxold)
          omega
      have hxne_id : x ≠ id := by
        intro heq
        subst heq
        have hsame := GameState.zone_unique hwf hs.src_mem (hzd ▸ hs.dst_mem) hs.id_mem hxold
        exact hs.ne (hsame.symm.trans hzd)
      have hne1 : x.n ≠ id.n := fun e => hxne_id (by cases x; cases id; simp_all)
      have hne2 : x.n ≠ id'.n := fun e => hxne (by cases x; cases id'; simp_all)
      have hobj_eq : s'.obj? x = s.obj? x := hs.objects_other x.n hne1 hne2
      rw [hobj_eq] at hox
      exact hok.owner p k hk x hxold o hox
  · by_cases hzs : Zone.player p k = src
    · rw [hzs, hs.zone_src] at hx
      have hxold : x ∈ s.zone (Zone.player p k) := hzs ▸ List.mem_of_mem_erase hx
      have hnd_src : (s.zone src).Nodup := by
        have hp := flatMap_split (allZones s.playerCount) s.zone src hs.src_mem
        exact (List.nodup_append.mp (hp.nodup_iff.mp hwf.nodup)).1
      have hxne_id : x ≠ id := ((List.Nodup.mem_erase_iff hnd_src).mp hx).1
      have hxne_id' : x ≠ id' := by
        rcases hs.fresh with rfl | hfresh
        · exact hxne_id
        · intro heq; subst heq
          have := hwf.lt_nextId x (GameState.mem_zoneIds (hzs ▸ hs.src_mem) hxold)
          omega
      have hne1 : x.n ≠ id.n := fun e => hxne_id (by cases x; cases id; simp_all)
      have hne2 : x.n ≠ id'.n := fun e => hxne_id' (by cases x; cases id'; simp_all)
      have hobj_eq : s'.obj? x = s.obj? x := hs.objects_other x.n hne1 hne2
      rw [hobj_eq] at hox
      exact hok.owner p k hk x hxold o hox
    · rw [hs.zone_other hzs hzd] at hx
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
          obtain ⟨z, hz, hzk⟩ := hwf.zones_valid _ hmem_zones
          have heq := Zone.key_inj hzk
          exact hm (heq ▸ hz)
      have hxne_id : x ≠ id := by
        intro heq; subst heq
        exact hzs (GameState.zone_unique hwf hs.src_mem hvalid_pk hs.id_mem hx)
      have hxne_id' : x ≠ id' := by
        rcases hs.fresh with rfl | hfresh
        · exact hxne_id
        · intro heq; subst heq
          have := hwf.lt_nextId x (GameState.mem_zoneIds hvalid_pk hx)
          omega
      have hne1 : x.n ≠ id.n := fun e => hxne_id (by cases x; cases id; simp_all)
      have hne2 : x.n ≠ id'.n := fun e => hxne_id' (by cases x; cases id'; simp_all)
      have hobj_eq : s'.obj? x = s.obj? x := hs.objects_other x.n hne1 hne2
      rw [hobj_eq] at hox
      exact hok.owner p k hk x hx o hox

/-- Moving an object either keeps its `ObjId` (Arena-to-Arena) or mints a completely fresh `ObjId`
absent from `s.zoneIds` (CR 3.0.9). -/
theorem moveObj_fresh {s s' : GameState} {id id' : ObjId} {dst : Zone} {pos : Pos} {fd : Bool}
    (hwf : s.WF) (h : moveObj s id dst pos fd = some (s', id')) :
    id' = id ∨ id' ∉ s.zoneIds := by
  obtain ⟨src, d, hs⟩ := moveObj_spec h
  rcases hs.fresh with h1 | h1
  · exact Or.inl h1
  · refine Or.inr (fun hm => ?_)
    have := hwf.lt_nextId id' hm
    omega

/-- Moving between two Arena zones (for example, Equipment defending on the Combat Chain and
returning to its equipment zone) preserves both `ObjId` and the entire `Object` entry including
`-1{d}` counters and tapped state (CR 3.0.9, 7.7). -/
theorem moveObj_arena_preserves {s s' : GameState} {id id' : ObjId} {src dst : Zone}
    {pos : Pos} {fd : Bool}
    (hloc : s.locate id = some src)
    (hsrc : src.isArena = true) (hdst : dst.isArena = true)
    (h : moveObj s id dst pos fd = some (s', id')) :
    id' = id ∧ s'.objects = s.objects := by
  unfold moveObj at h
  rw [hloc] at h
  cases ho : s.obj? id with
  | none => rw [ho] at h; cases h
  | some o =>
    rw [ho] at h
    have hnorm : Zone.normalize o.owner dst = dst := by
      cases dst with
      | combatChain => rfl
      | stack => simp [Zone.isArena] at hdst
      | player q k =>
        simp only [Zone.isArena] at hdst
        simp [Zone.normalize, hdst]
    have hcross : Zone.crosses src (Zone.normalize o.owner dst) = false := by
      rw [hnorm]
      simp [Zone.crosses, hsrc, hdst]
    simp only at h
    split at h
    · cases h
    · rw [hcross] at h
      simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, rfl⟩

/-- Helper: `moveObj` preserves `config` and `playRollback`. -/
theorem moveObj_config_rollback {s s' : GameState} {id id' : ObjId} {dst : Zone} {pos : Pos}
    {fd : Bool} (h : moveObj s id dst pos fd = some (s', id')) :
    s'.config = s.config ∧ s'.playRollback = s.playRollback := by
  unfold moveObj at h
  split at h
  · dsimp only at h
    split at h
    · cases h
    · split at h <;>
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨rfl, rfl⟩
  · cases h

end Fab

end
