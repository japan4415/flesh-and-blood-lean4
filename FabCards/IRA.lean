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

/-- Shared printed attributes for Ira Welcome Deck attack action cards. -/
def iraAttackCard (id name : String) (supertype : Supertype) (pitch cost : Nat)
    (power defense : Int) (keywords : List KeywordInst := [])
    (abilities : List Ability := []) (playEffect : Option EffectDef := none) : CardDef :=
  { id := ⟨id⟩
    front := { name, supertypes := [supertype], types := [.action], subtypes := [.attack]
               color := some (if pitch == 1 then .red else if pitch == 2 then .yellow else .blue)
               pitch := some pitch, cost := some { actionPoints := 1, resources := cost }
               power := some power, defense := some defense, keywords, abilities, playEffect }
    sets := [⟨"IRA"⟩]
    status := .full }

/-- Whirling Mist Blossom. -/
def IRA_003_Y : CardDef :=
  iraAttackCard "IRA_003_Y" "Whirling Mist Blossom" (.class_ .ninja) 2 1 2 2
    [.specialization "Ira", .goAgain]
    [.triggered (.onConsecutiveHitLink 2) false none none { body := .prim (.draw .controller (.const 2)) }]

/-- Salt the Wound. -/
def IRA_004_Y : CardDef :=
  iraAttackCard "IRA_004_Y" "Salt the Wound" (.class_ .ninja) 2 0 2 3
    (abilities := [.static_ none .self_ (.addPower .chainHits)])

/-- Logical cards first published in the Ira Welcome Deck. -/
def iraCards : List CardDef := [IRA_001, IRA_002, IRA_003_Y, IRA_004_Y]

end IRA
end FabCards

end
