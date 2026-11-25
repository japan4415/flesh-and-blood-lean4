module

public import Fab.Card.CardDef

@[expose] public section

namespace FabCards
namespace IRA

open Fab

/-- Ira, Crimson Haze, with the current Young subtype. -/
def IRA_001 : CardDef :=
  { id := ⟨"IRA_001"⟩
    front :=
      { name := "Ira, Crimson Haze"
        supertypes := [.class_ .ninja]
        types := [.hero]
        subtypes := [.young]
        intellect := some 4
        life := some 20
        abilities := [.static_ none (.attackOrdinal 2) (.addPower (.const 1))] }
    sets := [⟨"IRA"⟩]
    status := .full }

/-- Logical cards first published in the Ira Welcome Deck. -/
def iraCards : List CardDef := [IRA_001]

end IRA
end FabCards

end
