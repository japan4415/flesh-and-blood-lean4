module

public import Fab.Rules.Move
public import Fab.Rules.Add
public import Fab.Rules.Objects

/-!
# Game State Process (CR 1.10.2), termination (I12a), and `Settled` (I17)

Implements the Game State Process executed before granting priority:
1. Hero defeat / simultaneous draw check when hero life `≤ 0` (CR 1.10.2a, 4.5).
2. Clearing tokens and attack-proxies that sit in Non-Arena zones (CR 1.10.2).
3. Clearing dead living permanents (Allies with `life ≤ 0`) from Arena permanent zones (CR 1.10.2b).

Proves **I12a** (strictly decreasing measure `gspMeasure` guaranteeing termination) and
**I17** (the output of `gspRun` always satisfies `Settled`).
-/

@[expose] public section

namespace Fab

/-- Whether `id` is a non-physical token or attack-proxy that cannot exist in a Non-Arena zone. -/
def isStrayNonPhys (s : GameState) (id : ObjId) : Bool :=
  match s.obj? id with
  | some o =>
    match o.kind with
    | .token _ | .attackProxy _ _ => true
    | .card _ _ | .layer _ _ _ _ => false
  | none => false

/-- All tokens and attack-proxies currently sitting in Non-Arena zones (CR 1.10.2). -/
def nonArenaNonPhys (s : GameState) : List ObjId :=
  ((allZones s.playerCount).filter fun z => !z.isArena).flatMap fun z =>
    (s.zone z).filter (isStrayNonPhys s)

/-- Whether `id` is a living non-hero permanent with life `≤ 0` (CR 1.10.2b). -/
def isDeadAlly (s : GameState) (id : ObjId) : Bool :=
  match s.obj? id with
  | some o =>
    match o.life with
    | some hp => decide (hp ≤ 0)
    | none => false
  | none => false

/-- All dead living permanents (`life ≤ 0`) currently in Arena permanent zones (CR 1.10.2b). -/
def deadAllies (s : GameState) : List ObjId :=
  (allPlayers s.playerCount).flatMap fun p =>
    (s.zone (.player p .permanent)).filter (isDeadAlly s)

/-- A game state is `Settled` (GSP fixed point: **I17**) when no hero defeat is pending, no stray
tokens or attack-proxies occupy Non-Arena zones, and no dead living permanents remain in the Arena
(CR 1.10.2). -/
def Settled (s : GameState) : Prop :=
  (s.result = none → (checkHeroDefeat s).result = none) ∧
  nonArenaNonPhys s = [] ∧
  deadAllies s = []

instance decidableSettled (s : GameState) : Decidable (Settled s) := by
  unfold Settled
  infer_instance

/-- Total count of objects across all Non-Arena zones. -/
def nonArenaObjCount (s : GameState) : Nat :=
  (((allZones s.playerCount).filter fun z => !z.isArena).flatMap s.zone).length

/-- Total count of objects across all players' Arena permanent zones. -/
def permanentObjCount (s : GameState) : Nat :=
  ((allPlayers s.playerCount).flatMap fun p => s.zone (.player p .permanent)).length

/-- Weighted lexicographic measure strictly decreasing on every `gspStep` (**I12a**):
- Hero defeat drops `(if result.isNone then 1 else 0)` by 1.
- Removing a Non-Arena token/proxy drops `nonArenaObjCount` by 1.
- Clearing a dead Ally drops `permanentObjCount` by 1 and increases `nonArenaObjCount` by at most 1,
  so `nonArenaObjCount + 2 * permanentObjCount` strictly decreases by at least 1. -/
def gspMeasure (s : GameState) : Nat :=
  (if s.result.isNone then 1 else 0) + nonArenaObjCount s + 2 * permanentObjCount s

/-- Single Game State Process step returning `some s'` if any rule-based state action applied,
or `none` when `s` is already `Settled` (CR 1.10.2). -/
def gspStep (s : GameState) : Option GameState :=
  if s.result.isNone && (checkHeroDefeat s).result.isSome then
    some (checkHeroDefeat s)
  else
    match nonArenaNonPhys s with
    | id :: _ => some (removeNonPhysObj s id)
    | [] =>
      match deadAllies s with
      | id :: _ =>
        match s.obj? id with
        | some o =>
          if o.kind.phys?.isNone then
            some (removeNonPhysObj s id)
          else
            match moveObj s id (.player o.owner .graveyard) .top false with
            | some (s', _) => some s'
            | none => none
        | none => none
      | [] => none

/-- Helper: `flatMap` length equals sum of lengths over mapped list. -/
theorem length_flatMap_sum {α β : Type} (l : List α) (f : α → List β) :
    (l.flatMap f).length = (l.map (fun x => (f x).length)).sum := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [List.flatMap_cons, List.length_append, ih]

/-- Helper: if `f` and `g` agree everywhere except `a` (which appears once in `l`), where
`g a < f a`, then `(l.map g).sum < (l.map f).sum`. -/
theorem sum_map_lt_of_one {α : Type} {l : List α} {f g : α → Nat} {a : α}
    (hnd : l.Nodup) (hmem : a ∈ l) (hlt : g a < f a) (hother : ∀ x ∈ l, x ≠ a → g x = f x) :
    (l.map g).sum < (l.map f).sum := by
  induction l with
  | nil => cases hmem
  | cons x xs ih =>
    rw [List.nodup_cons] at hnd
    rcases List.mem_cons.mp hmem with rfl | htail
    · have hrest : xs.map g = xs.map f := by
        apply List.map_congr_left
        intro y hy
        exact hother y (List.mem_cons_of_mem _ hy) (fun heq => hnd.1 (heq ▸ hy))
      simp only [List.map_cons, List.sum_cons, hrest]
      omega
    · have hne : x ≠ a := fun heq => hnd.1 (heq ▸ htail)
      have hx := hother x List.mem_cons_self hne
      have hsub := ih hnd.2 htail (fun y hy hya => hother y (List.mem_cons_of_mem _ hy) hya)
      simp only [List.map_cons, List.sum_cons, hx]
      omega

/-- Helper: if `f` and `g` agree everywhere except `a` (which appears once in `l`), where
`g a ≤ f a + 1`, then `(l.map g).sum ≤ (l.map f).sum + 1`. -/
theorem sum_map_le_add_one {α : Type} {l : List α} {f g : α → Nat} {a : α}
    (hnd : l.Nodup) (hmem : a ∈ l) (hle : g a ≤ f a + 1) (hother : ∀ x ∈ l, x ≠ a → g x = f x) :
    (l.map g).sum ≤ (l.map f).sum + 1 := by
  induction l with
  | nil => cases hmem
  | cons x xs ih =>
    rw [List.nodup_cons] at hnd
    rcases List.mem_cons.mp hmem with rfl | htail
    · have hrest : xs.map g = xs.map f := by
        apply List.map_congr_left
        intro y hy
        exact hother y (List.mem_cons_of_mem _ hy) (fun heq => hnd.1 (heq ▸ hy))
      simp only [List.map_cons, List.sum_cons, hrest]
      omega
    · have hne : x ≠ a := fun heq => hnd.1 (heq ▸ htail)
      have hx := hother x List.mem_cons_self hne
      have hsub := ih hnd.2 htail (fun y hy hya => hother y (List.mem_cons_of_mem _ hy) hya)
      simp only [List.map_cons, List.sum_cons, hx]
      omega

/-- Helper: mapping an injective function over a `Nodup` list preserves `Nodup`. -/
theorem nodup_map_of_inj {α β : Type} {f : α → β} (hinj : ∀ a b, f a = f b → a = b)
    {l : List α} (hnd : l.Nodup) : (l.map f).Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons x xs ih =>
    rw [List.nodup_cons] at hnd
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih hnd.2⟩
    intro hmem
    rw [List.mem_map] at hmem
    obtain ⟨y, hy, hfy⟩ := hmem
    exact hnd.1 ((hinj y x hfy) ▸ hy)

/-- Helper: `flatMap` congruence on list elements. -/
theorem gsp_flatMap_congr {α β : Type} {l : List α} {f g : α → List β}
    (h : ∀ x ∈ l, f x = g x) : l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons]
    rw [h x List.mem_cons_self, ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]

/-- Helper: `allPlayers n` has no duplicates. -/
theorem allPlayers_nodup (n : Nat) : (allPlayers n).Nodup := by
  unfold allPlayers
  exact nodup_map_of_inj (fun a b h => by cases h; rfl) List.nodup_range

/-- Helper: `removeNonPhysObj` preserves `result`. -/
theorem removeNonPhysObj_result (s : GameState) (id : ObjId) :
    (removeNonPhysObj s id).result = s.result := by
  unfold removeNonPhysObj
  cases s.locate id with
  | none => rfl
  | some _ =>
    cases s.obj? id with
    | none => rfl
    | some _ => dsimp only; split <;> rfl

/-- Helper: erasing a member strictly decreases list length. -/
theorem length_erase_lt {α : Type} [BEq α] [LawfulBEq α] {l : List α} {x : α} (h : x ∈ l) :
    (l.erase x).length < l.length := by
  have h1 := (List.perm_cons_erase h).length_eq
  simp only [List.length_cons] at h1
  omega

/-- **I12a** (GSP termination measure): every `gspStep` strictly decreases `gspMeasure` on any
`WF` state (CR 1.10.2). -/
theorem gspStep_measure_lt {s s' : GameState} (hwf : s.WF) (h : gspStep s = some s') :
    gspMeasure s' < gspMeasure s := by
  unfold gspStep at h
  split at h
  · rename_i hdef
    simp only [Option.some.injEq] at h
    subst h
    simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, Option.isSome_iff_ne_none] at hdef
    obtain ⟨hnone, hsome⟩ := hdef
    have hnone' : (checkHeroDefeat s).result.isNone = false := by
      cases hr : (checkHeroDefeat s).result with
      | none => exact False.elim (hsome hr)
      | some _ => rfl
    have hna : nonArenaObjCount (checkHeroDefeat s) = nonArenaObjCount s := by
      unfold checkHeroDefeat
      split
      · rfl
      · cases livingPlayers s with
        | nil => rfl
        | cons _ ws => cases ws <;> rfl
    have hp : permanentObjCount (checkHeroDefeat s) = permanentObjCount s := by
      unfold checkHeroDefeat
      split
      · rfl
      · cases livingPlayers s with
        | nil => rfl
        | cons _ ws => cases ws <;> rfl
    unfold gspMeasure
    rw [hna, hp, hnone']
    simp [hnone]
  · cases hna_list : nonArenaNonPhys s with
    | cons id rest =>
      rw [hna_list] at h
      simp only [Option.some.injEq] at h
      subst h
      have hmem_all : id ∈ nonArenaNonPhys s := by rw [hna_list]; exact List.mem_cons_self
      unfold nonArenaNonPhys at hmem_all
      rw [List.mem_flatMap] at hmem_all
      obtain ⟨z, hz_filt, hid_filt⟩ := hmem_all
      rw [List.mem_filter] at hz_filt hid_filt
      obtain ⟨hz_valid, hz_na⟩ := hz_filt
      obtain ⟨hid_z, hstray⟩ := hid_filt
      have hloc : s.locate id = some z := GameState.locate_eq hwf hz_valid hid_z
      have hin : id.n ∈ s.objects := hwf.table_of_zone id (GameState.mem_zoneIds hz_valid hid_z)
      obtain ⟨o, ho⟩ : ∃ o, s.obj? id = some o := by
        unfold GameState.obj?
        cases hg : s.objects[id.n]? with
        | none =>
          exfalso; have := Std.ExtTreeMap.mem_iff_isSome_getElem?.mp hin; rw [hg] at this; simp at this
        | some o => exact ⟨o, rfl⟩
      have hnp : o.kind.phys?.isNone = true := by
        unfold isStrayNonPhys at hstray
        rw [ho] at hstray
        dsimp only at hstray
        cases hk : o.kind <;> rw [hk] at hstray <;> simp [ObjectKind.phys?] at hstray ⊢
      have hrem_eq : removeNonPhysObj s id =
          { s.setZone z ((s.zone z).erase id) with objects := s.objects.erase id.n } := by
        unfold removeNonPhysObj
        rw [hloc, ho]
        simp [hnp]
      have hres : (removeNonPhysObj s id).result = s.result := removeNonPhysObj_result s id
      have hperm_eq : permanentObjCount (removeNonPhysObj s id) = permanentObjCount s := by
        rw [hrem_eq]
        unfold permanentObjCount
        congr 1
        apply gsp_flatMap_congr
        intro p _
        have hne : Zone.player p .permanent ≠ z := by
          intro heq
          subst heq
          simp [Zone.isArena, ZoneKind.isArena] at hz_na
        exact GameState.zone_setZone_ne s hne _
      have hna_lt : nonArenaObjCount (removeNonPhysObj s id) < nonArenaObjCount s := by
        rw [hrem_eq]
        unfold nonArenaObjCount
        rw [length_flatMap_sum, length_flatMap_sum]
        have hnd : ((allZones s.playerCount).filter fun z => !z.isArena).Nodup :=
          (allZones_nodup s.playerCount).filter _
        have hz_in : z ∈ (allZones s.playerCount).filter fun z => !z.isArena :=
          List.mem_filter.mpr ⟨hz_valid, hz_na⟩
        apply sum_map_lt_of_one hnd hz_in
        · change ((s.setZone z ((s.zone z).erase id)).zone z).length < (s.zone z).length
          rw [GameState.zone_setZone_self]
          exact length_erase_lt hid_z
        · intro x _ hxz
          change ((s.setZone z ((s.zone z).erase id)).zone x).length = (s.zone x).length
          rw [GameState.zone_setZone_ne s hxz]
      unfold gspMeasure
      rw [hres, hperm_eq]
      omega
    | nil =>
      rw [hna_list] at h
      cases hda_list : deadAllies s with
      | nil => rw [hda_list] at h; cases h
      | cons id rest =>
        rw [hda_list] at h
        dsimp only at h
        have hmem_da : id ∈ deadAllies s := by rw [hda_list]; exact List.mem_cons_self
        unfold deadAllies at hmem_da
        rw [List.mem_flatMap] at hmem_da
        obtain ⟨p, hp_in, hid_filt⟩ := hmem_da
        rw [List.mem_filter] at hid_filt
        obtain ⟨hid_perm, _⟩ := hid_filt
        have hp_lt : p.n < s.playerCount := mem_allPlayers_iff.mp hp_in
        have hz_perm : (Zone.player p .permanent).Valid s.playerCount :=
          Zone.valid_player hp_lt .permanent
        have hloc : s.locate id = some (.player p .permanent) :=
          GameState.locate_eq hwf hz_perm hid_perm
        cases ho : s.obj? id with
        | none => rw [ho] at h; cases h
        | some o =>
          rw [ho] at h
          dsimp only at h
          split at h
          · rename_i hnp
            simp only [Option.some.injEq] at h
            subst h
            have hrem_eq : removeNonPhysObj s id =
                { s.setZone (.player p .permanent) ((s.zone (.player p .permanent)).erase id) with
                  objects := s.objects.erase id.n } := by
              unfold removeNonPhysObj
              rw [hloc, ho]
              simp [hnp]
            have hres : (removeNonPhysObj s id).result = s.result := removeNonPhysObj_result s id
            have hna_eq : nonArenaObjCount (removeNonPhysObj s id) = nonArenaObjCount s := by
              rw [hrem_eq]
              unfold nonArenaObjCount
              congr 1
              apply gsp_flatMap_congr
              intro z hz
              rw [List.mem_filter] at hz
              have hne : z ≠ .player p .permanent := by
                intro heq; subst heq; simp [Zone.isArena, ZoneKind.isArena] at hz
              exact GameState.zone_setZone_ne s hne _
            have hp_lt_cnt : permanentObjCount (removeNonPhysObj s id) < permanentObjCount s := by
              rw [hrem_eq]
              unfold permanentObjCount
              rw [length_flatMap_sum, length_flatMap_sum]
              apply sum_map_lt_of_one (allPlayers_nodup s.playerCount) hp_in
              · change ((s.setZone (.player p .permanent) _).zone (.player p .permanent)).length < _
                rw [GameState.zone_setZone_self]
                exact length_erase_lt hid_perm
              · intro q _ hqp
                have hne : Zone.player q .permanent ≠ Zone.player p .permanent := by
                  intro heq; cases heq; exact hqp rfl
                change ((s.setZone (.player p .permanent) _).zone (.player q .permanent)).length = _
                rw [GameState.zone_setZone_ne s hne]
            unfold gspMeasure
            rw [hres, hna_eq]
            omega
          · cases hm : moveObj s id (.player o.owner .graveyard) .top false with
            | none => rw [hm] at h; cases h
            | some res =>
              obtain ⟨s1, id1⟩ := res
              rw [hm] at h
              simp only [Option.some.injEq] at h
              subst h
              have hcfg_res : s1.config = s.config ∧ s1.result = s.result := by
                unfold moveObj at hm
                split at hm
                · dsimp only at hm
                  split at hm
                  · cases hm
                  · split at hm <;>
                    · simp only [Option.some.injEq] at hm
                      obtain ⟨rfl, rfl⟩ := hm; exact ⟨rfl, rfl⟩
                · cases hm
              have hcfg : s1.config = s.config := hcfg_res.1
              have hres : s1.result = s.result := hcfg_res.2
              have hcount : s1.playerCount = s.playerCount := by simp [GameState.playerCount, hcfg]
              have hnorm : Zone.normalize o.owner (.player o.owner .graveyard) =
                  .player o.owner .graveyard := by
                simp [Zone.normalize, ZoneKind.isArena]
              have hgy_valid : (Zone.player o.owner .graveyard).Valid s.playerCount := by
                unfold moveObj at hm
                rw [hloc, ho] at hm
                dsimp only at hm
                rw [hnorm] at hm
                split at hm
                · cases hm
                · rename_i hnot
                  simp only [not_or, Decidable.not_not] at hnot
                  exact hnot.2
              have hzones : ∀ z, s1.zone z =
                  if z = .player o.owner .graveyard then id1 :: s.zone (.player o.owner .graveyard)
                  else if z = .player p .permanent then (s.zone (.player p .permanent)).erase id
                  else s.zone z := by
                intro z
                unfold moveObj at hm
                rw [hloc, ho] at hm
                dsimp only at hm
                rw [hnorm] at hm
                split at hm
                · cases hm
                · have hne_pg : Zone.player p .permanent ≠ Zone.player o.owner .graveyard := by
                    intro heq; cases heq
                  split at hm <;>
                  · simp only [Option.some.injEq, Prod.mk.injEq] at hm
                    obtain ⟨rfl, rfl⟩ := hm
                    exact GameState.zone_move hne_pg _ _ z
              have hp_lt_cnt : permanentObjCount s1 < permanentObjCount s := by
                unfold permanentObjCount
                rw [hcount, length_flatMap_sum, length_flatMap_sum]
                apply sum_map_lt_of_one (allPlayers_nodup s.playerCount) hp_in
                · rw [hzones (.player p .permanent)]
                  have hne : Zone.player p .permanent ≠ Zone.player o.owner .graveyard := by
                    intro heq; cases heq
                  simp only [hne, ↓reduceIte]
                  exact length_erase_lt hid_perm
                · intro q _ hqp
                  rw [hzones (.player q .permanent)]
                  have hne1 : Zone.player q .permanent ≠ Zone.player o.owner .graveyard := by
                    intro heq; cases heq
                  have hne2 : Zone.player q .permanent ≠ Zone.player p .permanent := by
                    intro heq; cases heq; exact hqp rfl
                  simp [hne1, hne2]
              have hna_le : nonArenaObjCount s1 ≤ nonArenaObjCount s + 1 := by
                unfold nonArenaObjCount
                rw [hcount, length_flatMap_sum, length_flatMap_sum]
                have hnd : ((allZones s.playerCount).filter fun z => !z.isArena).Nodup :=
                  (allZones_nodup s.playerCount).filter _
                have hgy_in : Zone.player o.owner .graveyard ∈
                    (allZones s.playerCount).filter fun z => !z.isArena :=
                  List.mem_filter.mpr ⟨hgy_valid, by simp [Zone.isArena, ZoneKind.isArena]⟩
                apply sum_map_le_add_one hnd hgy_in
                · rw [hzones (.player o.owner .graveyard)]
                  simp
                · intro z hz hzne
                  rw [hzones z]
                  rw [List.mem_filter] at hz
                  have hnep : z ≠ .player p .permanent := by
                    intro heq; subst heq; simp [Zone.isArena, ZoneKind.isArena] at hz
                  simp [hzne, hnep]
              unfold gspMeasure
              rw [hres]
              omega

/-- `gspStep` preserves `WF`. -/
theorem gspStep_wf {s s' : GameState} (hwf : s.WF) (h : gspStep s = some s') : s'.WF := by
  unfold gspStep at h
  split at h
  · simp only [Option.some.injEq] at h; subst h; exact checkHeroDefeat_wf hwf
  · cases h1 : nonArenaNonPhys s with
    | cons id _ =>
      rw [h1] at h; simp only [Option.some.injEq] at h; subst h
      exact removeNonPhysObj_wf hwf id
    | nil =>
      rw [h1] at h
      cases h2 : deadAllies s with
      | nil => rw [h2] at h; cases h
      | cons id _ =>
        rw [h2] at h; dsimp only at h
        cases ho : s.obj? id with
        | none => rw [ho] at h; cases h
        | some o =>
          rw [ho] at h; dsimp only at h
          split at h
          · simp only [Option.some.injEq] at h; subst h; exact removeNonPhysObj_wf hwf id
          · cases hm : moveObj s id (.player o.owner .graveyard) .top false with
            | none => rw [hm] at h; cases h
            | some res =>
              rw [hm] at h; simp only [Option.some.injEq] at h; subst h
              exact moveObj_wf hwf hm

/-- `gspStep` preserves `OwnerOk`. -/
theorem gspStep_ownerOk {s s' : GameState} (hwf : s.WF) (hok : s.OwnerOk)
    (h : gspStep s = some s') : s'.OwnerOk := by
  unfold gspStep at h
  split at h
  · simp only [Option.some.injEq] at h; subst h; exact checkHeroDefeat_ownerOk hok
  · cases h1 : nonArenaNonPhys s with
    | cons id _ =>
      rw [h1] at h; simp only [Option.some.injEq] at h; subst h
      exact removeNonPhysObj_ownerOk hok id
    | nil =>
      rw [h1] at h
      cases h2 : deadAllies s with
      | nil => rw [h2] at h; cases h
      | cons id _ =>
        rw [h2] at h; dsimp only at h
        cases ho : s.obj? id with
        | none => rw [ho] at h; cases h
        | some o =>
          rw [ho] at h; dsimp only at h
          split at h
          · simp only [Option.some.injEq] at h; subst h; exact removeNonPhysObj_ownerOk hok id
          · cases hm : moveObj s id (.player o.owner .graveyard) .top false with
            | none => rw [hm] at h; cases h
            | some res =>
              rw [hm] at h; simp only [Option.some.injEq] at h; subst h
              exact moveObj_ownerOk hwf hok hm

/-- `gspStep` preserves `physIds` (I1). -/
theorem gspStep_physIds {s s' : GameState} (hwf : s.WF) (h : gspStep s = some s') :
    s'.physIds.Perm s.physIds := by
  unfold gspStep at h
  split at h
  · simp only [Option.some.injEq] at h; subst h; rw [checkHeroDefeat_physIds]
  · cases h1 : nonArenaNonPhys s with
    | cons id _ =>
      rw [h1] at h; simp only [Option.some.injEq] at h; subst h
      exact removeNonPhysObj_physIds hwf id
    | nil =>
      rw [h1] at h
      cases h2 : deadAllies s with
      | nil => rw [h2] at h; cases h
      | cons id _ =>
        rw [h2] at h; dsimp only at h
        cases ho : s.obj? id with
        | none => rw [ho] at h; cases h
        | some o =>
          rw [ho] at h; dsimp only at h
          split at h
          · simp only [Option.some.injEq] at h; subst h; exact removeNonPhysObj_physIds hwf id
          · cases hm : moveObj s id (.player o.owner .graveyard) .top false with
            | none => rw [hm] at h; cases h
            | some res =>
              rw [hm] at h; simp only [Option.some.injEq] at h; subst h
              exact moveObj_physIds hwf hm

/-- `gspStep` preserves `config` and `playRollback`. -/
theorem gspStep_meta {s s' : GameState} (h : gspStep s = some s') :
    s'.config = s.config ∧ s'.playRollback = s.playRollback := by
  unfold gspStep at h
  split at h
  · simp only [Option.some.injEq] at h; subst h
    unfold checkHeroDefeat
    split
    · exact ⟨rfl, rfl⟩
    · cases livingPlayers s with
      | nil => exact ⟨rfl, rfl⟩
      | cons _ ws => cases ws <;> exact ⟨rfl, rfl⟩
  · cases h1 : nonArenaNonPhys s with
    | cons id _ =>
      rw [h1] at h; simp only [Option.some.injEq] at h; subst h
      exact removeNonPhysObj_meta s id
    | nil =>
      rw [h1] at h
      cases h2 : deadAllies s with
      | nil => rw [h2] at h; cases h
      | cons id _ =>
        rw [h2] at h; dsimp only at h
        cases ho : s.obj? id with
        | none => rw [ho] at h; cases h
        | some o =>
          rw [ho] at h; dsimp only at h
          split at h
          · simp only [Option.some.injEq] at h; subst h; exact removeNonPhysObj_meta s id
          · cases hm : moveObj s id (.player o.owner .graveyard) .top false with
            | none => rw [hm] at h; cases h
            | some res =>
              rw [hm] at h; simp only [Option.some.injEq] at h; subst h
              unfold moveObj at hm
              split at hm
              · dsimp only at hm
                split at hm
                · cases hm
                · split at hm <;>
                  · simp only [Option.some.injEq] at hm
                    obtain ⟨rfl, rfl⟩ := hm; exact ⟨rfl, rfl⟩
              · cases hm

/-- When `gspStep` returns `none` on a `WF` state where every dead Ally is owned by a seated
player, the state is `Settled` (**I17**). -/
theorem settled_of_gspStep_none {s : GameState} (hwf : s.WF)
    (hown_seated : ∀ id o, s.obj? id = some o → o.owner.n < s.playerCount)
    (h : gspStep s = none) : Settled s := by
  unfold gspStep at h
  split at h
  · cases h
  · rename_i hno_def
    cases h1 : nonArenaNonPhys s with
    | cons _ _ => rw [h1] at h; cases h
    | nil =>
      rw [h1] at h
      refine ⟨?_, h1, ?_⟩
      · intro hres
        cases hcd : (checkHeroDefeat s).result with
        | none => rfl
        | some _ =>
          exfalso
          apply hno_def
          simp [hres, hcd]
      · cases h2 : deadAllies s with
        | nil => rfl
        | cons id _ =>
          exfalso
          rw [h2] at h
          dsimp only at h
          have hmem_da : id ∈ deadAllies s := by rw [h2]; exact List.mem_cons_self
          unfold deadAllies at hmem_da
          rw [List.mem_flatMap] at hmem_da
          obtain ⟨p, hp_in, hid_filt⟩ := hmem_da
          rw [List.mem_filter] at hid_filt
          obtain ⟨hid_perm, _⟩ := hid_filt
          have hp_lt : p.n < s.playerCount := mem_allPlayers_iff.mp hp_in
          have hz_perm : (Zone.player p .permanent).Valid s.playerCount :=
            Zone.valid_player hp_lt .permanent
          have hin : id.n ∈ s.objects := hwf.table_of_zone id (GameState.mem_zoneIds hz_perm hid_perm)
          cases ho : s.obj? id with
          | none =>
            have := Std.ExtTreeMap.mem_iff_isSome_getElem?.mp hin
            unfold GameState.obj? at ho
            rw [ho] at this; simp at this
          | some o =>
            rw [ho] at h
            dsimp only at h
            split at h
            · cases h
            · have hloc : s.locate id = some (.player p .permanent) :=
                GameState.locate_eq hwf hz_perm hid_perm
              have hgy_valid : (Zone.player o.owner .graveyard).Valid s.playerCount :=
                Zone.valid_player (hown_seated id o ho) .graveyard
              have hnorm : Zone.normalize o.owner (.player o.owner .graveyard) =
                  .player o.owner .graveyard := by simp [Zone.normalize, ZoneKind.isArena]
              have hmove_some : (moveObj s id (.player o.owner .graveyard) .top false).isSome = true := by
                unfold moveObj
                rw [hloc, ho]
                dsimp only
                rw [hnorm]
                have hne : Zone.player p .permanent ≠ Zone.player o.owner .graveyard := by
                  intro heq; cases heq
                simp only [hne, false_or, hgy_valid, not_true_eq_false, ↓reduceIte]
                split <;> rfl
              cases hm : moveObj s id (.player o.owner .graveyard) .top false with
              | none => rw [hm] at hmove_some; simp at hmove_some
              | some _ => rw [hm] at h; cases h

/-- Fuel-bounded GSP fixed-point loop (structural recursion on `n`). -/
def gspLoop : Nat → GameState → GameState
  | 0, s => s
  | n + 1, s =>
    match gspStep s with
    | some s' => gspLoop n s'
    | none => s

/-- Run the Game State Process to its fixed point using the exact termination bound `gspMeasure s`
(CR 1.10.2) (**I12a**). -/
def gspRun (s : GameState) : GameState :=
  gspLoop (gspMeasure s) s

/-- `gspLoop` preserves `WF`. -/
theorem gspLoop_wf : ∀ (n : Nat) {s : GameState}, s.WF → (gspLoop n s).WF
  | 0, _, hwf => hwf
  | n + 1, s, hwf => by
    unfold gspLoop
    cases hs : gspStep s with
    | none => exact hwf
    | some s' => exact gspLoop_wf n (gspStep_wf hwf hs)

/-- `gspLoop` preserves `OwnerOk`. -/
theorem gspLoop_ownerOk : ∀ (n : Nat) {s : GameState}, s.WF → s.OwnerOk → (gspLoop n s).OwnerOk
  | 0, _, _, hok => hok
  | n + 1, s, hwf, hok => by
    unfold gspLoop
    cases hs : gspStep s with
    | none => exact hok
    | some s' => exact gspLoop_ownerOk n (gspStep_wf hwf hs) (gspStep_ownerOk hwf hok hs)

/-- `gspLoop` preserves `physIds` (I1). -/
theorem gspLoop_physIds : ∀ (n : Nat) {s : GameState}, s.WF → (gspLoop n s).physIds.Perm s.physIds
  | 0, _, _ => List.Perm.refl _
  | n + 1, s, hwf => by
    unfold gspLoop
    cases hs : gspStep s with
    | none => exact List.Perm.refl _
    | some s' =>
      exact (gspLoop_physIds n (gspStep_wf hwf hs)).trans (gspStep_physIds hwf hs)

/-- `gspLoop` preserves `config` and `playRollback`. -/
theorem gspLoop_meta : ∀ (n : Nat) (s : GameState),
    (gspLoop n s).config = s.config ∧ (gspLoop n s).playRollback = s.playRollback
  | 0, _ => ⟨rfl, rfl⟩
  | n + 1, s => by
    unfold gspLoop
    cases hs : gspStep s with
    | none => exact ⟨rfl, rfl⟩
    | some s' =>
      have h1 := gspStep_meta hs
      have h2 := gspLoop_meta n s'
      exact ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩

/-- `gspRun` preserves `WF`. -/
theorem gspRun_wf {s : GameState} (hwf : s.WF) : (gspRun s).WF :=
  gspLoop_wf (gspMeasure s) hwf

/-- `gspRun` preserves `OwnerOk`. -/
theorem gspRun_ownerOk {s : GameState} (hwf : s.WF) (hok : s.OwnerOk) : (gspRun s).OwnerOk :=
  gspLoop_ownerOk (gspMeasure s) hwf hok

/-- `gspRun` preserves `physIds` (I1). -/
theorem gspRun_physIds {s : GameState} (hwf : s.WF) : (gspRun s).physIds.Perm s.physIds :=
  gspLoop_physIds (gspMeasure s) hwf

/-- `gspRun` preserves `config` and `playRollback`. -/
theorem gspRun_meta (s : GameState) :
    (gspRun s).config = s.config ∧ (gspRun s).playRollback = s.playRollback :=
  gspLoop_meta (gspMeasure s) s

/-- **I12a** (fixed point reached within `gspMeasure s` steps): once `gspLoop n s` finishes with
`gspMeasure s ≤ n`, no further `gspStep` is possible. -/
theorem gspLoop_fixed_point :
    ∀ (n : Nat) {s : GameState}, s.WF → gspMeasure s ≤ n → gspStep (gspLoop n s) = none
  | 0, s, hwf, hle => by
    unfold gspLoop
    cases hs : gspStep s with
    | none => rfl
    | some s' =>
      have hlt := gspStep_measure_lt hwf hs
      omega
  | n + 1, s, hwf, hle => by
    unfold gspLoop
    cases hs : gspStep s with
    | none => exact hs
    | some s' =>
      have hlt := gspStep_measure_lt hwf hs
      exact gspLoop_fixed_point n (gspStep_wf hwf hs) (by omega)

/-- **I12a + I17**: `gspRun s` always reaches a GSP fixed point (`gspStep (gspRun s) = none`). -/
theorem gspRun_fixed_point {s : GameState} (hwf : s.WF) : gspStep (gspRun s) = none :=
  gspLoop_fixed_point (gspMeasure s) hwf (Nat.le_refl _)

end Fab

end
