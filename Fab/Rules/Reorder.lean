module

public import Fab.Rules.Move

/-!
# Rearranging a zone

Shuffling a deck (CR 4.1.5) or ordering pitched cards onto the bottom of a deck (CR 4.4.3c)
replaces a zone's list with a permutation of the same object identifiers, preserving `WF`,
`OwnerOk`, and physical card conservation (I1).
-/

@[expose] public section

namespace Fab

/-- Place a viewed card during Opt, preserving the order of cards already placed on top (CR 8.5.22). -/
def optDeckOrder (deck : List ObjId) (topCount : Nat) (card : ObjId) (putOnTop : Bool) : List ObjId :=
  let fixed := deck.take topCount
  let undecided := deck.drop topCount
  if card ∈ undecided then
    if putOnTop then fixed ++ card :: undecided.erase card
    else fixed ++ (undecided.erase card ++ [card])
  else deck

/-- Placing an Opt card only permutes the deck. -/
theorem optDeckOrder_perm (deck : List ObjId) (topCount : Nat) (card : ObjId) (putOnTop : Bool) :
    (optDeckOrder deck topCount card putOnTop).Perm deck := by
  unfold optDeckOrder
  dsimp only
  split
  · rename_i member
    have erased := (List.perm_cons_erase member).symm
    cases putOnTop
    · simp only [Bool.false_eq_true, ↓reduceIte]
      simpa only [List.take_append_drop] using
        ((List.perm_append_comm (l₁ := (deck.drop topCount).erase card) (l₂ := [card])).trans
          erased).append_left (deck.take topCount)
    · simp only [↓reduceIte]
      simpa only [List.take_append_drop] using erased.append_left (deck.take topCount)
  · exact List.Perm.refl _

/-- Put cards on the bottom in choice order, keeping the other cards in order. -/
def deckBottomOrder (deck chosen : List ObjId) : List ObjId :=
  chosen.foldl (fun order card => optDeckOrder order 0 card false) deck

/-- Putting viewed cards on the bottom preserves the deck's multiset. -/
theorem deckBottomOrder_perm (deck chosen : List ObjId) : (deckBottomOrder deck chosen).Perm deck := by
  induction chosen generalizing deck with
  | nil => exact List.Perm.refl _
  | cons id rest ih =>
    exact (ih (optDeckOrder deck 0 id false)).trans (optDeckOrder_perm deck 0 id false)

namespace GameState

/-- Replace the contents of zone `z` by a rearrangement `l` of its objects. -/
def reorder (s : GameState) (z : Zone) (l : List ObjId) : GameState :=
  s.setZone z l

/-- Reordering a valid zone yields a permutation of `zoneIds`. -/
theorem zoneIds_reorder {s : GameState} {z : Zone} {l : List ObjId}
    (hz : z ∈ allZones s.playerCount) (hp : l.Perm (s.zone z)) :
    (s.reorder z l).zoneIds.Perm s.zoneIds := by
  have hnd := allZones_nodup s.playerCount
  have hcount : (s.reorder z l).playerCount = s.playerCount := rfl
  unfold zoneIds
  rw [hcount]
  obtain ⟨L, hL⟩ : ∃ L, L = allZones s.playerCount := ⟨_, rfl⟩
  rw [← hL] at hnd hz
  have e1 := flatMap_split L (s.reorder z l).zone z hz
  have e2 := flatMap_split L s.zone z hz
  have hrest : (L.erase z).flatMap (s.reorder z l).zone = (L.erase z).flatMap s.zone := by
    apply flatMap_one_congr L hnd
    intro x _ hx
    exact zone_setZone_ne s hx l
  rw [hrest] at e1
  have hz' : (s.reorder z l).zone z = l := zone_setZone_self s z l
  rw [hz'] at e1
  rw [← hL]
  exact e1.trans ((hp.append_right _).trans e2.symm)

/-- Reordering a valid zone preserves `WF`. -/
theorem wf_reorder {s : GameState} (hwf : s.WF) {z : Zone} {l : List ObjId}
    (hz : z ∈ allZones s.playerCount) (hp : l.Perm (s.zone z)) :
    (s.reorder z l).WF := by
  have hperm := zoneIds_reorder hz hp
  have hmem : ∀ x, x ∈ (s.reorder z l).zoneIds ↔ x ∈ s.zoneIds := fun x => hperm.mem_iff
  refine ⟨hperm.nodup_iff.mpr hwf.nodup, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact hwf.table_of_zone x ((hmem x).mp hx)
  · intro k hk
    obtain ⟨x, hx, hxk⟩ := hwf.zone_of_table k hk
    exact ⟨x, (hmem x).mpr hx, hxk⟩
  · intro x hx
    exact hwf.lt_nextId x ((hmem x).mp hx)
  · intro k hk
    simp only [reorder, setZone, Std.ExtTreeMap.mem_insert] at hk
    rcases hk with hk | hk
    · exact ⟨z, hz, Nat.compare_eq_eq.mp hk⟩
    · exact hwf.zones_valid k hk

/-- Reordering a valid zone preserves physical card identifiers (I1). -/
theorem physIds_reorder {s : GameState} {z : Zone} {l : List ObjId}
    (hz : z ∈ allZones s.playerCount) (hp : l.Perm (s.zone z)) :
    (s.reorder z l).physIds.Perm s.physIds := by
  unfold physIds
  exact List.Perm.filterMap _ (zoneIds_reorder hz hp)

/-- Reordering a zone by a permutation preserves `OwnerOk`. -/
theorem ownerOk_reorder {s : GameState} (hok : s.OwnerOk) {z : Zone} {l : List ObjId}
    (hp : l.Perm (s.zone z)) :
    (s.reorder z l).OwnerOk := by
  refine ⟨fun p k hk id hid o hobj => ?_⟩
  by_cases hz : Zone.player p k = z
  · subst hz
    rw [reorder, zone_setZone_self] at hid
    exact hok.owner p k hk id (hp.subset hid) o hobj
  · rw [reorder, zone_setZone_ne s hz] at hid
    exact hok.owner p k hk id hid o hobj

end GameState

end Fab

end
