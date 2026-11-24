module

public import Fab.Rules.Move

/-!
# Draw primitive

Drawing a card moves the top card of a player's deck to their hand (CR 4.1.6, 4.4.3f).
In Flesh and Blood, attempting to draw from an empty deck simply does nothing; there is no
deck-out loss or Burn Out rule (CR 4.5).
-/

@[expose] public section

namespace Fab

/-- Draw one card for player `p`. If `p`'s deck is empty, returns `(s, [])` unchanged (CR 4.5). -/
def drawOne (s : GameState) (p : PlayerId) : GameState × List Event :=
  match s.zone (.player p .deck) with
  | [] => (s, [])
  | top :: _ =>
    match moveObj s top (.player p .hand) .top false with
    | some (s', id') =>
      (s', [.moved top id' (.player p .deck) (.player p .hand), .drawn p id'])
    | none => (s, [])

/-- Drawing from an empty deck is a no-op with no events (CR 4.5). -/
theorem drawOne_empty_noop {s : GameState} {p : PlayerId}
    (h : s.zone (.player p .deck) = []) :
    drawOne s p = (s, []) := by
  unfold drawOne
  rw [h]

/-- `drawOne` preserves `WF`. -/
theorem drawOne_wf {s : GameState} {p : PlayerId} (hwf : s.WF) :
    (drawOne s p).1.WF := by
  unfold drawOne
  cases h : s.zone (.player p .deck) with
  | nil => exact hwf
  | cons top rest =>
    dsimp only
    cases hm : moveObj s top (.player p .hand) .top false with
    | none => exact hwf
    | some res =>
      obtain ⟨s', id'⟩ := res
      exact moveObj_wf hwf hm

/-- `drawOne` preserves the multiset of physical card identifiers (I1). -/
theorem drawOne_physIds {s : GameState} {p : PlayerId} (hwf : s.WF) :
    (drawOne s p).1.physIds.Perm s.physIds := by
  unfold drawOne
  cases h : s.zone (.player p .deck) with
  | nil => exact List.Perm.refl _
  | cons top rest =>
    dsimp only
    cases hm : moveObj s top (.player p .hand) .top false with
    | none => exact List.Perm.refl _
    | some res =>
      obtain ⟨s', id'⟩ := res
      exact moveObj_physIds hwf hm

/-- `drawOne` preserves `OwnerOk`. -/
theorem drawOne_ownerOk {s : GameState} {p : PlayerId} (hwf : s.WF) (hok : s.OwnerOk) :
    (drawOne s p).1.OwnerOk := by
  unfold drawOne
  cases h : s.zone (.player p .deck) with
  | nil => exact hok
  | cons top rest =>
    dsimp only
    cases hm : moveObj s top (.player p .hand) .top false with
    | none => exact hok
    | some res =>
      obtain ⟨s', id'⟩ := res
      exact moveObj_ownerOk hwf hok hm

/-- In a well-formed game with `OwnerOk`, drawing from a non-empty deck of a seated player
decrements deck length by 1 and increments hand length by 1. -/
theorem drawOne_lengths_of_ownerOk {s : GameState} {p : PlayerId} {top : ObjId} {rest : List ObjId}
    (hwf : s.WF) (hok : s.OwnerOk) (hp : p.n < s.playerCount)
    (hdeck : s.zone (.player p .deck) = top :: rest) :
    ((drawOne s p).1.zone (.player p .deck)).length + 1 = (s.zone (.player p .deck)).length ∧
    ((drawOne s p).1.zone (.player p .hand)).length = (s.zone (.player p .hand)).length + 1 := by
  have hvalid_d : Zone.player p .deck ∈ allZones s.playerCount := Zone.valid_player hp .deck
  have hvalid_h : Zone.player p .hand ∈ allZones s.playerCount := Zone.valid_player hp .hand
  have hmem_top : top ∈ s.zone (.player p .deck) := by rw [hdeck]; exact List.mem_cons_self
  have hloc : s.locate top = some (.player p .deck) := GameState.locate_eq hwf hvalid_d hmem_top
  have hin_obj : top.n ∈ s.objects := hwf.table_of_zone top (GameState.mem_zoneIds hvalid_d hmem_top)
  obtain ⟨o, ho⟩ : ∃ o, s.obj? top = some o := by
    unfold GameState.obj?
    cases hg : s.objects[top.n]? with
    | none =>
      exfalso
      have := Std.ExtTreeMap.mem_iff_isSome_getElem?.mp hin_obj
      rw [hg] at this
      simp at this
    | some o => exact ⟨o, rfl⟩
  have hown : o.owner = p := hok.owner p .deck rfl top hmem_top o ho
  have hmove_some : ∃ s' id', moveObj s top (.player p .hand) .top false = some (s', id') := by
    unfold moveObj
    rw [hloc, ho]
    have hnorm : Zone.normalize o.owner (.player p .hand) = .player p .hand := by
      simp [Zone.normalize, ZoneKind.isArena, hown]
    have hne : Zone.player p .deck ≠ Zone.player p .hand := by intro e; cases e
    simp only [hnorm, hne, false_or]
    have hv : Zone.Valid s.playerCount (.player p .hand) := hvalid_h
    simp only [hv, not_true_eq_false, ↓reduceIte]
    have hcr : Zone.crosses (.player p .deck) (.player p .hand) = true := rfl
    rw [hcr]
    exact ⟨_, _, rfl⟩
  obtain ⟨s', id', hm⟩ := hmove_some
  obtain ⟨src, d, hs, o1, ho1, hd⟩ := moveObj_spec_dst hm
  have hsrc : src = .player p .deck := by
    have := hs.locate; rw [hloc] at this; exact Option.some.inj this.symm
  have ho_eq : o1 = o := by rw [ho] at ho1; exact Option.some.inj ho1.symm
  have hdst : d = .player p .hand := by
    rw [hd, ho_eq, hown]; simp [Zone.normalize, ZoneKind.isArena]
  have heq : (drawOne s p).1 = s' := by
    unfold drawOne
    rw [hdeck]
    dsimp only
    rw [hm]
  rw [heq]
  subst hsrc
  subst hdst
  rw [hs.zone_src, hs.zone_dst, hdeck]
  simp [Pos.insert]

end Fab

end
