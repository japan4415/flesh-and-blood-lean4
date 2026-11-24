module

public import Fab.Core.Ids
public import Fab.Core.Supertype
public import Fab.Core.CardType
public import Fab.Core.Property
public import Fab.Core.Cost
public import Fab.Core.Keyword

/-!
# Card definitions

Static logical card definitions (`CardFace` and `CardDef`). Each unique `(name, pitch)`
combination is a distinct logical card (CR 2.6, 2.8). Double-faced cards (Transcend / Transform /
Demi-Hero) use `back`, and split cards with Meld (CR 8.3.38) use `splitRight`.

This module belongs to the `Card` layer and must not import `GameState` (design.md §4).
-/

@[expose] public section

namespace Fab

/-- Implementation status of a card definition (roadmap.md). -/
inductive ImplStatus where
  /-- Generated metadata block only; effects not yet transcribed. -/
  | todo
  /-- Effects transcribed into IR syntax only; not yet verified by scenario tests. -/
  | drafted
  /-- Partially implemented (for example, awaiting multiplayer or advanced mechanics). -/
  | «partial»
  /-- Fully implemented and covered by scenario tests. -/
  | full
deriving DecidableEq, Repr, Hashable

/-- One face of a card (front face, back face of a double-faced card, or right half of a split
card) (CR 2.0-2.16). -/
structure CardFace where
  /-- Printed card name (CR 2.6). -/
  name : String
  /-- Printed supertypes: classes, talents, and/or Generic (CR 2.11). -/
  supertypes : List Supertype := []
  /-- Printed functional card types (CR 2.15). -/
  types : List CardType := []
  /-- Printed subtypes (CR 2.16). -/
  subtypes : List Subtype := []
  /-- Printed color strip (CR 2.0). -/
  color : Option ColorStrip := none
  /-- Printed pitch value `{p}` (CR 2.8). `none` means the card cannot be pitched. -/
  pitch : Option Nat := none
  /-- Printed asset-cost (CR 2.2, 1.14.2). -/
  cost : Option AssetCost := none
  /-- Printed power `{p}` (CR 2.7). -/
  power : Option Int := none
  /-- Printed defense `{d}` (CR 2.3). -/
  defense : Option Int := none
  /-- Printed intellect `{i}` on hero cards (CR 2.4). -/
  intellect : Option Nat := none
  /-- Printed life total `{h}` on hero and ally cards (CR 2.5). -/
  life : Option Int := none
  /-- Printed ability and meta-static keywords (CR 8.3). -/
  keywords : List KeywordInst := []
deriving DecidableEq, Repr, Hashable

/-- Logical card definition uniquely identified by `CardId` (representing a `(name, pitch)` card)
(CR 2.6, 2.8). Abilities and effect IR fields are added in M3b. -/
structure CardDef where
  /-- Stable logical card identifier. -/
  id : CardId
  /-- Primary (front) face of the card. -/
  front : CardFace
  /-- Optional back face for double-faced cards (Transcend / Transform / Demi-Hero). -/
  back : Option CardFace := none
  /-- Optional right half for split cards with Meld (CR 8.3.38). -/
  splitRight : Option CardFace := none
  /-- Expansion sets in which this logical card was printed. -/
  sets : List SetCode := []
  /-- Current implementation status. -/
  status : ImplStatus := .todo
deriving DecidableEq, Repr, Hashable

/-- Unique card identity key `(name, pitch)` used for deck copy limits (CR 2.6, 2.8). -/
def CardDef.uniqueKey (c : CardDef) : String × Option Nat :=
  (c.front.name, c.front.pitch)

/-- Whether a face has card type `t`. -/
def CardFace.hasType (f : CardFace) (t : CardType) : Bool :=
  f.types.contains t

/-- Whether a face has subtype `st`. -/
def CardFace.hasSubtype (f : CardFace) (st : Subtype) : Bool :=
  f.subtypes.contains st

/-- Whether a card is a Hero card (CR 2.15.6g). -/
def CardDef.isHero (c : CardDef) : Bool :=
  c.front.hasType .hero

/-- Whether a card is a Young hero (CR 2.16). -/
def CardDef.isYoungHero (c : CardDef) : Bool :=
  c.isHero && c.front.hasSubtype .young

/-- Whether a card is an Adult hero eligible for Classic Constructed (not Young and not
Pit-Fighter) (TRP 1). -/
def CardDef.isAdultHero (c : CardDef) : Bool :=
  c.isHero && !c.front.hasSubtype .young && !c.front.hasSubtype .pitFighter

/-- Whether a card is a Weapon card (CR 2.15.6m). -/
def CardDef.isWeapon (c : CardDef) : Bool :=
  c.front.hasType .weapon

/-- Whether a card is an Equipment card (CR 2.15.6f). -/
def CardDef.isEquipment (c : CardDef) : Bool :=
  c.front.hasType .equipment

/-- Whether a card is a one-handed weapon (CR 2.16). -/
def CardDef.isOneHanded (c : CardDef) : Bool :=
  c.isWeapon && c.front.hasSubtype .oneHanded

/-- Whether a card is a two-handed weapon (CR 2.16). -/
def CardDef.isTwoHanded (c : CardDef) : Bool :=
  c.isWeapon && c.front.hasSubtype .twoHanded

/-- Whether a card is an Off-Hand equipment (occupies a weapon zone) (CR 2.16). -/
def CardDef.isOffHand (c : CardDef) : Bool :=
  c.isEquipment && c.front.hasSubtype .offHand

/-- Equipment armor slot for this card (`head`, `chest`, `arms`, or `legs`), if any. -/
def CardDef.equipSlot? (c : CardDef) : Option EquipSlot :=
  if c.isEquipment then
    c.front.subtypes.findSome? Subtype.toEquipSlot?
  else
    none

/-- Whether a card is an arena-card (Hero, Weapon, Equipment, Demi-Hero, Companion, Token, or
Macro) rather than a deck-card (CR 1.3.2, 4.1.4). -/
def CardDef.isArenaCard (c : CardDef) : Bool :=
  c.front.hasType .hero ||
  c.front.hasType .weapon ||
  c.front.hasType .equipment ||
  c.front.hasType .demiHero ||
  c.front.hasType .companion ||
  c.front.hasType .token ||
  c.front.hasType .macro

/-- Whether a card is a deck-card eligible to start in the main deck (CR 1.3.2, 4.1.4). -/
def CardDef.isDeckCard (c : CardDef) : Bool :=
  !c.isArenaCard

/-- Whether a card has the `Legendary` meta-static keyword (CR 8.3.15). -/
def CardDef.isLegendary (c : CardDef) : Bool :=
  c.front.keywords.contains .legendary

/-- Whether a card has the `Unlimited` meta-static keyword. -/
def CardDef.isUnlimited (c : CardDef) : Bool :=
  c.front.keywords.contains .unlimited

/-- Whether a card has the `Universal` meta-static keyword. -/
def CardDef.isUniversal (c : CardDef) : Bool :=
  c.front.keywords.contains .universal

/-- Extract all hero specialization names required by this card (CR 8.3.16). -/
def CardDef.specializations (c : CardDef) : List String :=
  c.front.keywords.filterMap fun
    | .specialization h => some h
    | _ => none

/-- Whether a hero face name matches a specialization hero name (handles exact match,
`"Hero, Subtitle"`, and `"Hero Surname"` such as `"Dorinthea Ironsong"`) (CR 8.3.16). -/
def CardFace.matchesHeroName (heroFace : CardFace) (specName : String) : Bool :=
  heroFace.name == specName ||
  heroFace.name.startsWith (specName ++ ",") ||
  heroFace.name.startsWith (specName ++ " ")

/-- An adult hero is always a hero. -/
theorem CardDef.isHero_of_isAdultHero {c : CardDef} (h : c.isAdultHero = true) :
    c.isHero = true := by
  unfold CardDef.isAdultHero at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1

/-- A hero card is never a deck-card. -/
theorem CardDef.not_isDeckCard_of_isHero {c : CardDef} (h : c.isHero = true) :
    c.isDeckCard = false := by
  unfold CardDef.isDeckCard CardDef.isArenaCard CardDef.isHero at *
  simp [h]

end Fab

end
