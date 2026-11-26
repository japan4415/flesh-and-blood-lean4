module

public import FabCards.ThroughWtr
public import FabCards.LSS
public import FabCards.ARC

@[expose] public section

namespace FabCards

open Fab

/-- Arcane Rising additions, including the rule-defined token required by Runeblade effects. -/
def throughArcAdditions : List CardDef :=
  LSS.LSS_002_Y :: ARC.runechantToken :: ARC.arcCards

/-- Verified logical cards and special-use promos registered through Arcane Rising so far. -/
def throughArcDB : CardDB :=
  ⟨throughArcAdditions ++ throughWtrDB.cards⟩

/-- Registered card IDs are unique and the effect syntax of each registered card is valid. -/
theorem throughArcDB_wf : throughArcDB.WF := by
  have additions : (⟨throughArcAdditions⟩ : CardDB).WF := by decide +kernel
  refine ⟨?_, ?_⟩
  · let arcId : CardId → Bool := fun id =>
      match id.val.toList with
      | 'A' :: 'R' :: 'C' :: '_' :: _ | 'L' :: 'S' :: 'S' :: '_' :: _ => true
      | _ => false
    have added : (throughArcAdditions.map CardDef.id).all arcId = true := by decide +kernel
    have earlier : (throughWtrDB.cards.map CardDef.id).all (fun id => !arcId id) = true := by
      decide +kernel
    change ((throughArcAdditions ++ throughWtrDB.cards).map CardDef.id).Nodup
    rw [List.map_append, List.nodup_append]
    refine ⟨additions.1, throughWtrDB_wf.1, ?_⟩
    intro id inAdded other inEarlier heq
    subst other
    have hAdded := List.all_eq_true.mp added id inAdded
    have hEarlier := List.all_eq_true.mp earlier id inEarlier
    rw [hAdded] at hEarlier
    exact Bool.noConfusion hEarlier
  · intro card member
    change card ∈ throughArcAdditions ++ throughWtrDB.cards at member
    rcases List.mem_append.mp member with h | h
    · exact additions.2 card h
    · exact throughWtrDB_wf.2 card h

end FabCards

end
