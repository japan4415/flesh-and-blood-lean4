module

public import Fab.Rules.Move

/-!
# Banish primitive

Banishing moves an object to its owner's banished zone, either face-up (public, as with Blood
Debt) or face-down (private, as with Intimidate) (CR 3.3, 8.3.12).
-/

@[expose] public section

namespace Fab

/-- Banish object `id` to its owner's banished zone with face-down flag `faceDown` (CR 3.3). -/
def banishOne (s : GameState) (id : ObjId) (faceDown : Bool := false) :
    Option (GameState × ObjId × List Event) :=
  match s.locate id, s.obj? id with
  | some src, some o =>
    let dst := Zone.player o.owner .banished
    match moveObj s id dst .top faceDown with
    | none => none
    | some (s', id') =>
      some (s', id', [.moved id id' src dst, .banished o.owner id' faceDown])
  | _, _ => none

/-- `banishOne` preserves `WF`. -/
theorem banishOne_wf {s s' : GameState} {id id' : ObjId} {fd : Bool} {es : List Event}
    (hwf : s.WF) (h : banishOne s id fd = some (s', id', es)) : s'.WF := by
  unfold banishOne at h
  split at h
  · rename_i src o _ _
    dsimp only at h
    cases hm : moveObj s id (Zone.player o.owner .banished) .top fd with
    | none => simp only [hm] at h; cases h
    | some res =>
      obtain ⟨s1, id1⟩ := res
      simp only [hm, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact moveObj_wf hwf hm
  · cases h

/-- `banishOne` preserves the multiset of physical card identifiers (I1). -/
theorem banishOne_physIds {s s' : GameState} {id id' : ObjId} {fd : Bool} {es : List Event}
    (hwf : s.WF) (h : banishOne s id fd = some (s', id', es)) : s'.physIds.Perm s.physIds := by
  unfold banishOne at h
  split at h
  · rename_i src o _ _
    dsimp only at h
    cases hm : moveObj s id (Zone.player o.owner .banished) .top fd with
    | none => simp only [hm] at h; cases h
    | some res =>
      obtain ⟨s1, id1⟩ := res
      simp only [hm, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact moveObj_physIds hwf hm
  · cases h

/-- `banishOne` preserves `OwnerOk`. -/
theorem banishOne_ownerOk {s s' : GameState} {id id' : ObjId} {fd : Bool} {es : List Event}
    (hwf : s.WF) (hok : s.OwnerOk) (h : banishOne s id fd = some (s', id', es)) : s'.OwnerOk := by
  unfold banishOne at h
  split at h
  · rename_i src o _ _
    dsimp only at h
    cases hm : moveObj s id (Zone.player o.owner .banished) .top fd with
    | none => simp only [hm] at h; cases h
    | some res =>
      obtain ⟨s1, id1⟩ := res
      simp only [hm, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact moveObj_ownerOk hwf hok hm
  · cases h

end Fab

end
