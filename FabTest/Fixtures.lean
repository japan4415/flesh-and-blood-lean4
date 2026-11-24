module

public import Fab
public meta import Fab

/-!
# Test fixtures (Welcome to Rathe sample cards)

Small hand-authored WTR sample cards used by M1 unit tests to exercise 1v1 Classic Constructed
deck legality, Name + Pitch uniqueness, Legendary limits, Specializations, and pre-game loadouts.
-/

public section

namespace FabTest

open Fab

/-- Bravo, Showstopper (WTR Adult Guardian Hero). -/
meta def bravoAdult : CardDef :=
  { id := ⟨"WTR_038"⟩
    front :=
      { name := "Bravo, Showstopper"
        supertypes := [.class_ .guardian]
        types := [.hero]
        intellect := some 4
        life := some 40 }
    sets := [.wtr]
    status := .drafted }

/-- Bravo (WTR Young Guardian Hero, illegal in Classic Constructed). -/
meta def bravoYoung : CardDef :=
  { id := ⟨"WTR_039"⟩
    front :=
      { name := "Bravo"
        supertypes := [.class_ .guardian]
        types := [.hero]
        subtypes := [.young]
        intellect := some 4
        life := some 20 }
    sets := [.wtr]
    status := .drafted }

/-- Dorinthea Ironsong (WTR Adult Warrior Hero, space-separated surname). -/
meta def dorintheaAdult : CardDef :=
  { id := ⟨"WTR_113"⟩
    front :=
      { name := "Dorinthea Ironsong"
        supertypes := [.class_ .warrior]
        types := [.hero]
        intellect := some 4
        life := some 40 }
    sets := [.wtr]
    status := .drafted }

/-- Anothos (WTR Guardian 2H Hammer Weapon). -/
meta def anothos : CardDef :=
  { id := ⟨"WTR_040"⟩
    front :=
      { name := "Anothos"
        supertypes := [.class_ .guardian]
        types := [.weapon]
        subtypes := [.hammer, .twoHanded]
        power := some 4 }
    sets := [.wtr]
    status := .drafted }

/-- Harmonized Kodachi (WTR Ninja 1H Dagger Weapon, modeled Generic-free for 1H+1H test). -/
meta def dawnblade : CardDef :=
  { id := ⟨"WTR_115"⟩
    front :=
      { name := "Dawnblade"
        supertypes := [.class_ .warrior]
        types := [.weapon]
        subtypes := [.sword, .oneHanded]
        power := some 3 }
    sets := [.wtr]
    status := .drafted }

/-- Second 1H Warrior weapon fixture for testing dual 1H weapon loadout. -/
meta def hatchet : CardDef :=
  { id := ⟨"WTR_115B"⟩
    front :=
      { name := "Hatchet of Body"
        supertypes := [.class_ .warrior]
        types := [.weapon]
        subtypes := [.sword, .oneHanded]
        power := some 2 }
    sets := [.wtr]
    status := .drafted }

/-- Tectonic Plating (WTR Legendary Guardian Chest Equipment). -/
meta def tectonicPlating : CardDef :=
  { id := ⟨"WTR_041"⟩
    front :=
      { name := "Tectonic Plating"
        supertypes := [.class_ .guardian]
        types := [.equipment]
        subtypes := [.chest]
        defense := some 2
        keywords := [.legendary, .battleworn] }
    sets := [.wtr]
    status := .drafted }

/-- Helm of Isen's Peak (WTR Guardian Head Equipment). -/
meta def helmOfIsensPeak : CardDef :=
  { id := ⟨"WTR_042"⟩
    front :=
      { name := "Helm of Isen's Peak"
        supertypes := [.class_ .guardian]
        types := [.equipment]
        subtypes := [.head]
        defense := some 1
        keywords := [.bladeBreak] }
    sets := [.wtr]
    status := .drafted }

/-- Crippling Crush (WTR Guardian Bravo Specialization Red). -/
meta def cripplingCrush : CardDef :=
  { id := ⟨"WTR_043"⟩
    front :=
      { name := "Crippling Crush"
        supertypes := [.class_ .guardian]
        types := [.action]
        subtypes := [.attack]
        color := some .red
        pitch := some 1
        cost := some { actionPoints := 1, resources := 7 }
        power := some 11
        defense := some 3
        keywords := [.crush, .specialization "Bravo"] }
    sets := [.wtr]
    status := .drafted }

/-- Ironsong Determination (WTR Warrior Dorinthea Specialization Yellow). -/
meta def ironsongDetermination : CardDef :=
  { id := ⟨"WTR_120"⟩
    front :=
      { name := "Ironsong Determination"
        supertypes := [.class_ .warrior]
        types := [.action]
        color := some .yellow
        pitch := some 2
        cost := some { actionPoints := 1, resources := 1 }
        defense := some 3
        keywords := [.goAgain, .specialization "Dorinthea"] }
    sets := [.wtr]
    status := .drafted }

/-- Helper creating a Red/Yellow/Blue Generic attack or defense reaction fixture. -/
meta def mkGenericCard (id : String) (name : String) (col : ColorStrip) (pitch : Nat)
    (power : Option Int) (def_ : Int) (ty : CardType := .action)
    (subs : List Subtype := [.attack]) : CardDef :=
  { id := ⟨id⟩
    front :=
      { name := name
        supertypes := [.generic]
        types := [ty]
        subtypes := subs
        color := some col
        pitch := some pitch
        cost := some { actionPoints := if ty == .action then 1 else 0, resources := 0 }
        power := power
        defense := some def_ }
    sets := [.wtr]
    status := .drafted }

/-- 20 distinct Generic WTR-style logical cards (7 card names × 3 colors minus 1) for building
60-card CC decks cleanly. -/
meta def genericPoolCards : List CardDef :=
  [ mkGenericCard "WTR_215_R" "Sink Below" .red 1 none 4 .defenseReaction []
  , mkGenericCard "WTR_216_Y" "Sink Below" .yellow 2 none 3 .defenseReaction []
  , mkGenericCard "WTR_217_B" "Sink Below" .blue 3 none 2 .defenseReaction []
  , mkGenericCard "WTR_191_R" "Wounding Blow" .red 1 (some 4) 2
  , mkGenericCard "WTR_192_Y" "Wounding Blow" .yellow 2 (some 3) 2
  , mkGenericCard "WTR_193_B" "Wounding Blow" .blue 3 (some 2) 2
  , mkGenericCard "WTR_173_R" "Pummel" .red 1 none 2 .attackReaction []
  , mkGenericCard "WTR_174_Y" "Pummel" .yellow 2 none 2 .attackReaction []
  , mkGenericCard "WTR_175_B" "Pummel" .blue 3 none 2 .attackReaction []
  , mkGenericCard "WTR_179_R" "Scar for a Scar" .red 1 (some 4) 2
  , mkGenericCard "WTR_180_Y" "Scar for a Scar" .yellow 2 (some 3) 2
  , mkGenericCard "WTR_181_B" "Scar for a Scar" .blue 3 (some 2) 2
  , mkGenericCard "WTR_182_R" "Snatch" .red 1 (some 4) 2
  , mkGenericCard "WTR_183_Y" "Snatch" .yellow 2 (some 3) 2
  , mkGenericCard "WTR_184_B" "Snatch" .blue 3 (some 2) 2
  , mkGenericCard "WTR_185_R" "Energy Potion" .red 1 none 0 .action [.item]
  , mkGenericCard "WTR_186_Y" "Potion of Strength" .yellow 2 none 0 .action [.item]
  , mkGenericCard "WTR_187_B" "Timesnap Potion" .blue 3 none 0 .action [.item]
  , mkGenericCard "WTR_188_R" "Barraging Brawnhide" .red 1 (some 5) 2
  , mkGenericCard "WTR_189_Y" "Barraging Brawnhide" .yellow 2 (some 4) 2
  , mkGenericCard "WTR_190_B" "Barraging Brawnhide" .blue 3 (some 3) 2
  ]

/-- Sample `CardDB` containing WTR hero, equipment, weapon, specialization, and generic cards. -/
meta def sampleDB : CardDB :=
  ⟨[ bravoAdult, bravoYoung, dorintheaAdult, anothos, dawnblade, hatchet,
     tectonicPlating, helmOfIsensPeak, cripplingCrush, ironsongDetermination ] ++
    genericPoolCards⟩

/-- 60 legal Generic deck-cards (20 unique `(name, pitch)` cards × 3 copies each). -/
meta def valid60Deck : List CardId :=
  (genericPoolCards.take 20).flatMap fun c => [c.id, c.id, c.id]

/-- Valid 1v1 Classic Constructed Bravo card-pool (3 arena cards + 60 deck cards = 63 ≤ 80). -/
meta def validBravoCCDeck : DeckList :=
  { hero := bravoAdult.id
    pool := [anothos.id, tectonicPlating.id, helmOfIsensPeak.id] ++ valid60Deck }

/-- Valid Start-of-Game loadout matching `validBravoCCDeck`. -/
meta def validBravoCCLoadout : Loadout :=
  { hero := bravoAdult.id
    head := some helmOfIsensPeak.id
    chest := some tectonicPlating.id
    weapons := [anothos.id]
    deck := valid60Deck
    inventory := [] }

end FabTest

end
