module

public import Fab.Card.CardDef

/-!
# Card database

`CardDB` stores logical card definitions indexed by `CardId` without referencing `GameState`
(design.md §4, §7.1). Theorems in the verified core quantify over all well-formed `CardDB`s.
-/

@[expose] public section

namespace Fab

/-- Collection of logical card definitions available in a game (design.md §6.1). -/
structure CardDB where
  /-- List of all logical card definitions in the database. -/
  cards : List CardDef
deriving DecidableEq, Repr

/-- Empty card database. -/
def CardDB.empty : CardDB := ⟨[]⟩

/-- Look up a logical card definition by its `CardId`. -/
def CardDB.find? (db : CardDB) (id : CardId) : Option CardDef :=
  db.cards.find? fun c => c.id == id

/-- Every `CardId` in `db.cards` is unique. -/
def CardDB.IdsUnique (db : CardDB) : Prop :=
  (db.cards.map (·.id)).Nodup

instance CardDB.decidableIdsUnique (db : CardDB) : Decidable db.IdsUnique := by
  unfold CardDB.IdsUnique
  infer_instance

/-- Static well-formedness of a `CardDB`. Expanded in M3b with IR binding and slot checks
(design.md §7.1). -/
def CardDB.WF (db : CardDB) : Prop :=
  db.IdsUnique

instance CardDB.decidableWF (db : CardDB) : Decidable db.WF := by
  unfold CardDB.WF
  infer_instance

/-- If `find?` returns `some c`, then `c` is in `db.cards` and has the requested `id`. -/
theorem CardDB.mem_of_find?_some {db : CardDB} {id : CardId} {c : CardDef}
    (h : db.find? id = some c) :
    c ∈ db.cards ∧ c.id = id := by
  unfold CardDB.find? at h
  have hmem := List.mem_of_find?_eq_some h
  have hpred := List.find?_some h
  simp only [beq_iff_eq] at hpred
  exact ⟨hmem, hpred⟩

/-- The empty `CardDB` is well formed. -/
theorem CardDB.wf_empty : CardDB.empty.WF := by
  decide

end Fab

end
