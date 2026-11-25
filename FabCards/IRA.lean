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

/-- Bittering Thorns. -/
def IRA_005_Y : CardDef :=
  iraAttackCard "IRA_005_Y" "Bittering Thorns" (.class_ .ninja) 2 1 3 2 [.goAgain]
    [.triggered .onHit false none none
      { body := .grant (.nextAttack CardFilter.any) (.addPower (.const 1)) .thisTurn }]

/-- Torrent of Tempo. -/
def IRA_006_R : CardDef :=
  iraAttackCard "IRA_006_R" "Torrent of Tempo" (.class_ .ninja) 1 1 5 3 []
    [.triggered .onHit false none none
      { body := .grant .self_ (.grantKeyword .goAgain) .thisChainLink }]

/-- Flying Kick. -/
def IRA_007_R : CardDef :=
  iraAttackCard "IRA_007_R" "Flying Kick" (.class_ .ninja) 1 2 5 3
    (playEffect := some
      { body := .ifThen (.chainLinkAtLeast 3)
          (.grant .self_ (.addPower (.const 2)) .thisChainLink) .nop })

/-- Brutal Assault. -/
def IRA_010_B : CardDef :=
  iraAttackCard "IRA_010_B" "Brutal Assault" .generic 3 2 4 3

/-- Logical cards first published in the Ira Welcome Deck. -/
def iraCards : List CardDef := [IRA_001, IRA_002, IRA_003_Y, IRA_004_Y, IRA_005_Y, IRA_006_R, IRA_007_R, IRA_010_B]

end IRA
end FabCards

end
