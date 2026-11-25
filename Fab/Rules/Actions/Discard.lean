module

public import Fab.Rules.Move

/-!
# Discard primitive

Discarding moves a card from a player's hand to their graveyard (CR 3.0, 3.10).
-/

@[expose] public section

namespace Fab

/-- Discard card `id` from player `p`'s hand to `p`'s graveyard. -/
def discardOne (s : GameState) (p : PlayerId) (id : ObjId) :
    Option (GameState × ObjId × List Event) :=
  if id ∈ s.zone (.player p .hand) then
    match moveRuleObj s id (.player p .graveyard) .top false with
    | none => none
    | some (s', id') =>
      some (s', id', ruleMoveEvents s id id' (.player p .hand) (.player p .graveyard) ++ [.discarded p id'])
  else
    none

/-- `discardOne` preserves `WF`. -/
theorem discardOne_wf {s s' : GameState} {p : PlayerId} {id id' : ObjId} {es : List Event}
    (hwf : s.WF) (h : discardOne s p id = some (s', id', es)) : s'.WF := by
  unfold discardOne at h
  split at h
  · cases hm : moveRuleObj s id (.player p .graveyard) .top false with
    | none => rw [hm] at h; cases h
    | some res =>
      obtain ⟨s1, id1⟩ := res
      rw [hm] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact moveObj_wf hwf hm
  · cases h

/-- `discardOne` preserves the multiset of physical card identifiers (I1). -/
theorem discardOne_physIds {s s' : GameState} {p : PlayerId} {id id' : ObjId} {es : List Event}
    (hwf : s.WF) (h : discardOne s p id = some (s', id', es)) : s'.physIds.Perm s.physIds := by
  unfold discardOne at h
  split at h
  · cases hm : moveRuleObj s id (.player p .graveyard) .top false with
    | none => rw [hm] at h; cases h
    | some res =>
      obtain ⟨s1, id1⟩ := res
      rw [hm] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact moveObj_physIds hwf hm
  · cases h

/-- `discardOne` preserves `OwnerOk`. -/
theorem discardOne_ownerOk {s s' : GameState} {p : PlayerId} {id id' : ObjId} {es : List Event}
    (hwf : s.WF) (hok : s.OwnerOk) (h : discardOne s p id = some (s', id', es)) : s'.OwnerOk := by
  unfold discardOne at h
  split at h
  · cases hm : moveRuleObj s id (.player p .graveyard) .top false with
    | none => rw [hm] at h; cases h
    | some res =>
      obtain ⟨s1, id1⟩ := res
      rw [hm] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact moveObj_ownerOk hwf hok hm
  · cases h

end Fab

end
