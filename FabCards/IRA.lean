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

/-- Edge of Autumn. -/
def IRA_002 : CardDef :=
  { id := ⟨"IRA_002"⟩
    front := { name := "Edge of Autumn", supertypes := [.class_ .ninja], types := [.weapon]
               subtypes := [.sword, .twoHanded], power := some 1
               abilities := [
                 .activated .action true { actionPoints := 1, resources := 1 } [] none false
                   { body := .prim .weaponAttack }
                 , .static_ none .self_ (.grantKeyword .goAgain)] }
    sets := [⟨"IRA"⟩]
    status := .full }

/-- Logical cards first published in the Ira Welcome Deck. -/
def iraCards : List CardDef := [IRA_001, IRA_002]

end IRA
end FabCards

end
