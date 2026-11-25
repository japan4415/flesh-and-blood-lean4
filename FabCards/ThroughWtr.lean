module

public import FabCards.Registry
public import FabCards.IRA

@[expose] public section

namespace FabCards

open Fab

/-- Logical cards implemented through the original Welcome to Rathe release. -/
def throughWtrDB : CardDB :=
  ⟨IRA.iraCards ++ wtrDB.cards⟩

/-- The combined database has unique card identifiers and valid static IR. -/
theorem throughWtrDB_wf : throughWtrDB.WF := by
  refine ⟨by decide +kernel, ?_⟩
  have hira : (⟨IRA.iraCards⟩ : CardDB).WF := by decide +kernel
  intro card member
  change card ∈ IRA.iraCards ++ wtrDB.cards at member
  rcases List.mem_append.mp member with h | h
  · exact hira.2 card h
  · exact wtrDB_wf.2 card h

end FabCards

end
