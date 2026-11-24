module

public import FabCards.WTR

/-!
# CardDB registry and kernel-checked well-formedness

Aggregates the Welcome to Rathe (WTR) card database and proves `CardDB.WF` (unique `CardId`s
and static IR well-formedness for every card) directly in the Lean kernel (roadmap.md M3b).
-/

@[expose] public section

namespace FabCards

open Fab

/-- Complete Welcome to Rathe (WTR) logical card database (226 cards). -/
def wtrDB : CardDB :=
  ⟨FabCards.WTR.wtrCards⟩

/-- Every drafted WTR card passes static IR well-formedness (`CardDB.WF`). -/
theorem draftedWtrDB_wf : (⟨FabCards.WTR.draftedCards⟩ : CardDB).WF := by
  decide +kernel

/-- The full 226-card Welcome to Rathe `CardDB` is statically well-formed. -/
theorem wtrDB_wf : wtrDB.WF := by
  decide +kernel

end FabCards

end
