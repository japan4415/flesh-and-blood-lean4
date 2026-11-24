module

/-!
# Supertypes (Class, Talent, Generic)

Supertypes govern card-pool and deck legality relative to a player's hero (CR 1.1, 2.11).
-/

@[expose] public section

namespace Fab

/-- Hero and card classes (CR 2.11.6). -/
inductive ClassType where
  /-- Adjudicator class. -/
  | adjudicator
  /-- Assassin class. -/
  | assassin
  /-- Bard class. -/
  | bard
  /-- Brute class (WTR). -/
  | brute
  /-- Guardian class (WTR). -/
  | guardian
  /-- Illusionist class. -/
  | illusionist
  /-- Mechanologist class. -/
  | mechanologist
  /-- Merchant class. -/
  | merchant
  /-- Necromancer class. -/
  | necromancer
  /-- Ninja class (WTR). -/
  | ninja
  /-- Pirate class. -/
  | pirate
  /-- Ranger class. -/
  | ranger
  /-- Runeblade class. -/
  | runeblade
  /-- Shapeshifter class. -/
  | shapeshifter
  /-- Thief class. -/
  | thief
  /-- Warrior class (WTR). -/
  | warrior
  /-- Wizard class. -/
  | wizard
deriving DecidableEq, Repr, Hashable

/-- Hero and card talents (CR 2.11.7). -/
inductive Talent where
  /-- Chaos talent. -/
  | chaos
  /-- Draconic talent. -/
  | draconic
  /-- Earth talent. -/
  | earth
  /-- Elemental talent. -/
  | elemental
  /-- Ice talent. -/
  | ice
  /-- Light talent. -/
  | light
  /-- Lightning talent. -/
  | lightning
  /-- Mystic talent. -/
  | mystic
  /-- Revered talent. -/
  | revered
  /-- Reviled talent. -/
  | reviled
  /-- Royal talent. -/
  | royal
  /-- Shadow talent. -/
  | shadow
deriving DecidableEq, Repr, Hashable

/-- A supertype printed on a card: either a class, a talent, or Generic (CR 2.11). -/
inductive Supertype where
  /-- A class supertype. -/
  | class_ (c : ClassType)
  /-- A talent supertype. -/
  | talent (t : Talent)
  /-- Generic supertype, playable with any hero (CR 2.11.5). -/
  | generic
deriving DecidableEq, Repr, Hashable

/-- A card's supertypes match a hero's supertypes when every non-generic supertype on the card
is among the hero's supertypes (CR 1.1.3, 2.11). -/
def Supertype.matchesHero (heroSupertypes cardSupertypes : List Supertype) : Prop :=
  ∀ s ∈ cardSupertypes, s = .generic ∨ s ∈ heroSupertypes

instance Supertype.decidableMatchesHero (heroSupertypes cardSupertypes : List Supertype) :
    Decidable (Supertype.matchesHero heroSupertypes cardSupertypes) := by
  unfold Supertype.matchesHero
  infer_instance

/-- Generic cards match any hero's supertypes (CR 2.11.5). -/
theorem Supertype.matchesHero_generic (heroSupertypes : List Supertype) :
    Supertype.matchesHero heroSupertypes [.generic] := by
  intro s hs
  simp only [List.mem_singleton] at hs
  exact Or.inl hs

/-- Cards with no supertypes match any hero. -/
theorem Supertype.matchesHero_nil (heroSupertypes : List Supertype) :
    Supertype.matchesHero heroSupertypes [] := by
  intro s hs
  cases hs

/-- A hero's own supertypes always match themselves. -/
theorem Supertype.matchesHero_self (heroSupertypes : List Supertype) :
    Supertype.matchesHero heroSupertypes heroSupertypes := by
  intro s hs
  exact Or.inr hs

/-- Adding supertypes to a hero preserves matching for any card. -/
theorem Supertype.matchesHero_mono {h1 h2 card : List Supertype}
    (hsub : ∀ s ∈ h1, s ∈ h2) (hm : Supertype.matchesHero h1 card) :
    Supertype.matchesHero h2 card := by
  intro s hs
  cases hm s hs with
  | inl hg => exact Or.inl hg
  | inr hh => exact Or.inr (hsub s hh)

end Fab

end
