module

/-!
# Card types, equipment slots, and subtypes

Functional types and subtypes printed in a card's type box (CR 2.14-2.16).
-/

@[expose] public section

namespace Fab

/-- Functional card types (CR 2.15). -/
inductive CardType where
  /-- Action card (CR 2.15.6a). -/
  | action
  /-- Attack Reaction card (CR 2.15.6b). -/
  | attackReaction
  /-- Block card (CR 2.15.6c). -/
  | block
  /-- Companion card. -/
  | companion
  /-- Defense Reaction card (CR 2.15.6d). -/
  | defenseReaction
  /-- Demi-Hero card (CR 2.15.6e). -/
  | demiHero
  /-- Equipment card (CR 2.15.6f). -/
  | equipment
  /-- Hero card (CR 2.15.6g). -/
  | hero
  /-- Instant card (CR 2.15.6h). -/
  | instant
  /-- Macro object (CR 2.15.6i). -/
  | macro
  /-- Mentor card (CR 2.15.6j). -/
  | mentor
  /-- Resource card (CR 2.15.6k). -/
  | resource
  /-- Token object (CR 2.15.6l). -/
  | token
  /-- Weapon card (CR 2.15.6m). -/
  | weapon
deriving DecidableEq, Repr, Hashable

/-- The four armor equipment zones in the arena (CR 3.0, 3.1, 3.4, 3.8, 3.11). -/
inductive EquipSlot where
  /-- Head equipment zone. -/
  | head
  /-- Chest equipment zone. -/
  | chest
  /-- Arms equipment zone. -/
  | arms
  /-- Legs equipment zone. -/
  | legs
deriving DecidableEq, Repr, Hashable

/-- Card subtypes appearing after the dash in the type box (CR 2.16). -/
inductive Subtype where
  /-- Affliction subtype. -/
  | affliction
  /-- Ally subtype. -/
  | ally
  /-- Arms equipment subtype. -/
  | arms
  /-- Arrow subtype. -/
  | arrow
  /-- Ash subtype. -/
  | ash
  /-- Attack action subtype. -/
  | attack
  /-- Aura subtype. -/
  | aura
  /-- Base equipment subtype (for Evo). -/
  | base
  /-- Bow weapon subtype. -/
  | bow
  /-- Chest equipment subtype. -/
  | chest
  /-- Claw weapon subtype. -/
  | claw
  /-- Club weapon subtype (WTR). -/
  | club
  /-- Construct subtype. -/
  | construct
  /-- Dagger weapon subtype (WTR). -/
  | dagger
  /-- Evo equipment subtype. -/
  | evo
  /-- Figment subtype. -/
  | figment
  /-- Flail weapon subtype. -/
  | flail
  /-- Gun weapon subtype. -/
  | gun
  /-- Hammer weapon subtype (WTR). -/
  | hammer
  /-- Head equipment subtype. -/
  | head
  /-- Invocation subtype. -/
  | invocation
  /-- Item subtype (WTR). -/
  | item
  /-- Landmark subtype. -/
  | landmark
  /-- Legs equipment subtype. -/
  | legs
  /-- Off-Hand equipment subtype (occupies a weapon zone). -/
  | offHand
  /-- One-handed weapon subtype (1H). -/
  | oneHanded
  /-- Orb weapon subtype. -/
  | orb
  /-- Pistol weapon subtype. -/
  | pistol
  /-- Pit-Fighter hero subtype (UPF / multiplayer). -/
  | pitFighter
  /-- Polearm weapon subtype. -/
  | polearm
  /-- Scepter weapon subtype. -/
  | scepter
  /-- Scythe weapon subtype. -/
  | scythe
  /-- Staff weapon subtype. -/
  | staff
  /-- Sword weapon subtype (WTR). -/
  | sword
  /-- Two-handed weapon subtype (2H). -/
  | twoHanded
  /-- Wrench weapon subtype. -/
  | wrench
  /-- Young hero subtype (Blitz / Limited). -/
  | young
deriving DecidableEq, Repr, Hashable

/-- Map an armor subtype to its corresponding `EquipSlot`, if any. -/
def Subtype.toEquipSlot? : Subtype → Option EquipSlot
  | .head => some .head
  | .chest => some .chest
  | .arms => some .arms
  | .legs => some .legs
  | _ => none

end Fab

end
