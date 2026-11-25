module

public import FabCards.ThroughWtr
public import FabCards.LSS
public import FabCards.ARC

@[expose] public section

namespace FabCards

open Fab

/-- Verified logical cards and special-use promos registered through Arcane Rising so far. -/
def throughArcDB : CardDB :=
  ⟨(LSS.LSS_002_Y :: ARC.arcCards) ++ throughWtrDB.cards⟩

/-- Registered card IDs are unique and the effect syntax of each registered card is valid. -/
theorem throughArcDB_wf : throughArcDB.WF := by
  refine ⟨by decide +kernel, ?_⟩
  have early : (⟨LSS.LSS_002_Y :: ARC.arcCards⟩ : CardDB).WF := by decide +kernel
  intro card member
  change card ∈ (LSS.LSS_002_Y :: ARC.arcCards) ++ throughWtrDB.cards at member
  rcases List.mem_append.mp member with h | h
  · exact early.2 card h
  · exact throughWtrDB_wf.2 card h

end FabCards

end
