module

public import FabCards.ThroughWtr
public import FabCards.LSS
public import FabCards.ARC

@[expose] public section

namespace FabCards

open Fab

/-- Arcane Rising cards and the special-use promo registered before their release. -/
def throughArcAdditions : List CardDef :=
  LSS.LSS_002_Y :: ARC.arcCards

/-- Verified logical cards and special-use promos registered through Arcane Rising so far. -/
def throughArcDB : CardDB :=
  ⟨throughArcAdditions ++ throughWtrDB.cards⟩

/-- Appending checked databases preserves well-formedness when their card IDs are separated
by a boolean predicate. -/
private theorem append_wf_of_separated_ids (first second : CardDB) (isFirst : CardId → Bool)
    (firstWf : first.WF) (secondWf : second.WF)
    (firstIds : (first.cards.map CardDef.id).all isFirst = true)
    (secondIds : (second.cards.map CardDef.id).all (fun id => !isFirst id) = true) :
    (⟨first.cards ++ second.cards⟩ : CardDB).WF := by
  refine ⟨?_, ?_⟩
  · change ((first.cards ++ second.cards).map CardDef.id).Nodup
    rw [List.map_append, List.nodup_append]
    refine ⟨firstWf.1, secondWf.1, ?_⟩
    intro id inFirst other inSecond same
    subst other
    have belongs := List.all_eq_true.mp firstIds id inFirst
    have excluded := List.all_eq_true.mp secondIds id inSecond
    rw [belongs] at excluded
    exact Bool.noConfusion excluded
  · intro card member
    change card ∈ first.cards ++ second.cards at member
    rcases List.mem_append.mp member with included | included
    · exact firstWf.2 card included
    · exact secondWf.2 card included

private def arcAdditionId (id : CardId) : Bool :=
  match id.val.toList with
  | 'A' :: 'R' :: 'C' :: '_' :: _ | 'L' :: 'S' :: 'S' :: '_' :: _ => true
  | _ => false

private theorem throughArcAdditions_wf : (⟨throughArcAdditions⟩ : CardDB).WF := by
  decide +kernel

private theorem throughArcAdditions_tagged :
    (throughArcAdditions.map CardDef.id).all arcAdditionId = true := by
  decide +kernel

private theorem throughWtrCards_not_tagged :
    (throughWtrDB.cards.map CardDef.id).all (fun id => !arcAdditionId id) = true := by
  decide +kernel

/-- Registered card IDs are unique and the effect syntax of each registered card is valid. -/
theorem throughArcDB_wf : throughArcDB.WF :=
  append_wf_of_separated_ids ⟨throughArcAdditions⟩ throughWtrDB arcAdditionId
    throughArcAdditions_wf throughWtrDB_wf throughArcAdditions_tagged throughWtrCards_not_tagged

end FabCards

end
