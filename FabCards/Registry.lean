module

public import FabCards.WTR
public import FabCards.MON

/-!
# CardDB registry and kernel-checked well-formedness

Aggregates the Welcome to Rathe (WTR) and Monarch (MON) card databases and proves `CardDB.WF`
(unique `CardId`s and static IR well-formedness for every card) directly in the Lean kernel.
-/

@[expose] public section

namespace FabCards

open Fab

private def ascendingIds : List CardId → Bool
  | a :: b :: rest => decide (a.val.toList < b.val.toList) && ascendingIds (b :: rest)
  | _ => true

private theorem ascendingIds_pairwise : ∀ ids, ascendingIds ids = true →
    ids.Pairwise (fun a b => a.val.toList < b.val.toList)
  | [], _ => .nil
  | [_], _ => .cons (by simp) .nil
  | a :: b :: rest, h => by
    simp only [ascendingIds, Bool.and_eq_true, decide_eq_true_eq] at h
    have tail := ascendingIds_pairwise (b :: rest) h.2
    refine List.pairwise_cons.mpr ⟨?_, tail⟩
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact h.1
    · exact Std.lt_trans h.1 ((List.pairwise_cons.mp tail).1 c hc)

private theorem checkedIds_unique (db : CardDB)
    (ids : ascendingIds (db.cards.map (·.id)) = true) : db.IdsUnique :=
  (ascendingIds_pairwise _ ids).imp (fun hlt heq => by cases heq; exact Std.lt_irrefl hlt)

/-- Complete Welcome to Rathe (WTR) logical card database (226 cards). -/
def wtrDB : CardDB :=
  ⟨FabCards.WTR.wtrCards⟩

/-- Every drafted WTR card passes static IR well-formedness (`CardDB.WF`). -/
theorem draftedWtrDB_wf : (⟨FabCards.WTR.draftedCards⟩ : CardDB).WF := by
  decide +kernel

/-- The full 226-card Welcome to Rathe `CardDB` is statically well-formed. -/
theorem wtrDB_wf : wtrDB.WF := by
  exact ⟨checkedIds_unique wtrDB (by decide +kernel), List.all_eq_true.mp (by decide +kernel)⟩

/-- Monarch (MON — Set 4) logical card database (307 cards). -/
def monDB : CardDB :=
  ⟨FabCards.MON.monCards⟩

/-- The full 307-card Monarch `CardDB` is statically well-formed. -/
theorem monDB_wf : monDB.WF := by
  exact ⟨checkedIds_unique monDB (by decide +kernel), List.all_eq_true.mp (by decide +kernel)⟩

/-- Combined multi-set database. Cracked Bauble keeps its WTR ID and gains the MON printing. -/
def allCardsDB : CardDB :=
  let wtr := wtrDB.cards.map fun c =>
    if c.id == ⟨"WTR_224_Y"⟩ then { c with sets := [.wtr, .mon] } else c
  ⟨monDB.cards.filter (fun c => c.id != ⟨"MON_306_Y"⟩) ++ wtr⟩

/-- The combined catalog has unique card IDs and well-formed IR. -/
theorem allCardsDB_wf : allCardsDB.WF := by
  refine ⟨checkedIds_unique allCardsDB (by decide +kernel), ?_⟩
  intro c hc
  simp only [allCardsDB, List.mem_append] at hc
  rcases hc with hmon | hwtr
  · exact monDB_wf.2 c (List.mem_filter.mp hmon).1
  · obtain ⟨base, hb, rfl⟩ := List.mem_map.mp hwtr
    split <;> exact wtrDB_wf.2 base hb

end FabCards

end
