module

public import Fab.Card.CardDB
public import Fab.Core.Mode

/-!
# Deck construction and pre-game loadout

Core Rules deck / card-pool legality (CR 1.1, 2.6, 2.8, 2.11, 8.3.15-16) and the Start-of-Game
loadout split from registered card-pool into arena equipment, weapons, starting deck, and
remaining inventory (CR 4.1.4).
-/

@[expose] public section

namespace Fab

/-- A player's registered card-pool: one hero card plus all arena-cards and deck-cards in the
card-pool (CR 1.1, 4.1.4). -/
structure DeckList where
  /-- Chosen hero card. -/
  hero : CardId
  /-- Non-hero arena-cards (weapons, equipment) and deck-cards registered in the card-pool. -/
  pool : List CardId
deriving DecidableEq, Repr

/-- A player's Start-of-Game loadout choice partitioning their registered card-pool into arena
slots, starting main deck, and remaining inventory (CR 4.1.4). -/
structure Loadout where
  /-- Hero card placed in the hero zone (CR 4.1.2). -/
  hero : CardId
  /-- Optional head equipment placed in the head zone. -/
  head : Option CardId := none
  /-- Optional chest equipment placed in the chest zone. -/
  chest : Option CardId := none
  /-- Optional arms equipment placed in the arms zone. -/
  arms : Option CardId := none
  /-- Optional legs equipment placed in the legs zone. -/
  legs : Option CardId := none
  /-- Weapons and/or off-hand equipment placed in weapon zones (up to 2). -/
  weapons : List CardId := []
  /-- Starting main deck cards, shuffled at setup (CR 4.1.5). -/
  deck : List CardId := []
  /-- Remaining unused cards placed in the inventory zone. -/
  inventory : List CardId := []
deriving DecidableEq, Repr

/-- All non-hero cards placed across arena slots, weapons, starting deck, and inventory. -/
def Loadout.allPoolCards (l : Loadout) : List CardId :=
  l.head.toList ++ l.chest.toList ++ l.arms.toList ++ l.legs.toList ++
    l.weapons ++ l.deck ++ l.inventory

/-- Whether a single pool card `cid` satisfies hero supertype, specialization, and non-hero
requirements relative to `heroDef` (CR 1.1.3, 2.11, 8.3.16). -/
def CardAllowedForHero (db : CardDB) (heroDef : CardDef) (cid : CardId) : Prop :=
  ∃ c, db.find? cid = some c ∧
    c.isHero = false ∧
    (c.isUniversal = true ∨ Supertype.matchesHero heroDef.front.supertypes c.front.supertypes) ∧
    (∀ spec ∈ c.specializations, heroDef.front.matchesHeroName spec = true)

/-- Decidability of `∃ a, o = some a ∧ P a` when `P` is decidable. -/
def decidableExistsSome {α : Type} {P : α → Prop} [DecidablePred P] (o : Option α) :
    Decidable (∃ a, o = some a ∧ P a) :=
  match o with
  | none => isFalse (by rintro ⟨_, h, _⟩; cases h)
  | some a => decidable_of_iff (P a) (by simp)

/-- Decidability of `∀ a, o = some a → P a` when `P` is decidable. -/
def decidableForallSome {α : Type} {P : α → Prop} [DecidablePred P] (o : Option α) :
    Decidable (∀ a, o = some a → P a) :=
  match o with
  | none => isTrue (by intro _ h; cases h)
  | some a => decidable_of_iff (P a) (by simp)

instance decidableCardAllowedForHero (db : CardDB) (heroDef : CardDef) (cid : CardId) :
    Decidable (CardAllowedForHero db heroDef cid) := by
  unfold CardAllowedForHero
  exact decidableExistsSome (db.find? cid)

/-- Count how many cards in `ids` have card name `name`, used for the `Legendary` 1-copy limit
(CR 8.3.15). -/
def countByName (db : CardDB) (ids : List CardId) (name : String) : Nat :=
  (ids.filter fun cid =>
    match db.find? cid with
    | some c => c.front.name == name
    | none => false).length

/-- Count how many cards in `ids` have unique key `(name, pitch)`, used for constructed copy
limits (CR 2.6, 2.8). -/
def countByUniqueKey (db : CardDB) (ids : List CardId) (key : String × Option Nat) : Nat :=
  (ids.filter fun cid =>
    match db.find? cid with
    | some c => c.uniqueKey == key
    | none => false).length

/-- Every `Legendary` card in `ids` appears at most once by card name across all pitch values
(CR 8.3.15). -/
def LegendaryLimitOk (db : CardDB) (ids : List CardId) : Prop :=
  ∀ cid ∈ ids, ∀ c, db.find? cid = some c → c.isLegendary = true →
    countByName db ids c.front.name ≤ 1

instance decidableLegendaryLimitOk (db : CardDB) (ids : List CardId) :
    Decidable (LegendaryLimitOk db ids) := by
  unfold LegendaryLimitOk
  haveI : ∀ cid, Decidable (∀ c, db.find? cid = some c → c.isLegendary = true →
      countByName db ids c.front.name ≤ 1) :=
    fun cid => decidableForallSome (db.find? cid)
  infer_instance

/-- Core Rules card-pool legality, independent of tournament format (CR 1.1, 2.11, 8.3.15-16). -/
def CoreDeckValid (db : CardDB) (deck : DeckList) : Prop :=
  ∃ heroDef, db.find? deck.hero = some heroDef ∧
    heroDef.isHero = true ∧
    (∀ cid ∈ deck.pool, CardAllowedForHero db heroDef cid) ∧
    LegendaryLimitOk db deck.pool

instance decidableCoreDeckValid (db : CardDB) (deck : DeckList) :
    Decidable (CoreDeckValid db deck) := by
  unfold CoreDeckValid
  exact decidableExistsSome (db.find? deck.hero)

/-- Whether an optional equipment card fits the given armor slot `slot` (CR 3.1, 3.4, 3.8, 3.11). -/
def EquipSlotValid (db : CardDB) (slot : EquipSlot) (ocid : Option CardId) : Prop :=
  match ocid with
  | none => True
  | some cid => ∃ c, db.find? cid = some c ∧ c.equipSlot? = some slot

instance decidableEquipSlotValid (db : CardDB) (slot : EquipSlot) (ocid : Option CardId) :
    Decidable (EquipSlotValid db slot ocid) := by
  unfold EquipSlotValid
  cases ocid with
  | none => exact isTrue trivial
  | some cid => exact decidableExistsSome (db.find? cid)

/-- Whether the weapon-zone loadout is legal for standard two-weapon-zone heroes:
up to 2 cards; each is a 1H weapon, 2H weapon, or Off-Hand equipment; if any card is 2H then no
other weapon/off-hand may be equipped (CR 3.16, 4.1.4). -/
def WeaponsValid (db : CardDB) (weapons : List CardId) : Prop :=
  weapons.length ≤ 2 ∧
  (∀ cid ∈ weapons, ∃ c, db.find? cid = some c ∧
    (c.isOneHanded = true ∨ c.isTwoHanded = true ∨ c.isOffHand = true)) ∧
  ((∃ cid ∈ weapons, ∃ c, db.find? cid = some c ∧ c.isTwoHanded = true) →
    weapons.length = 1)

instance decidableWeaponsValid (db : CardDB) (weapons : List CardId) :
    Decidable (WeaponsValid db weapons) := by
  unfold WeaponsValid
  haveI : ∀ cid, Decidable (∃ c, db.find? cid = some c ∧
      (c.isOneHanded = true ∨ c.isTwoHanded = true ∨ c.isOffHand = true)) :=
    fun cid => decidableExistsSome (db.find? cid)
  haveI : ∀ cid, Decidable (∃ c, db.find? cid = some c ∧ c.isTwoHanded = true) :=
    fun cid => decidableExistsSome (db.find? cid)
  infer_instance

/-- Every card placed into the starting main deck must be a deck-card (not Hero / Weapon /
Equipment) (CR 4.1.4). -/
def StartingDeckCardsValid (db : CardDB) (deck : List CardId) : Prop :=
  ∀ cid ∈ deck, ∃ c, db.find? cid = some c ∧ c.isDeckCard = true

instance decidableStartingDeckCardsValid (db : CardDB) (deck : List CardId) :
    Decidable (StartingDeckCardsValid db deck) := by
  unfold StartingDeckCardsValid
  haveI : ∀ cid, Decidable (∃ c, db.find? cid = some c ∧ c.isDeckCard = true) :=
    fun cid => decidableExistsSome (db.find? cid)
  infer_instance

/-- Start-of-Game loadout legality relative to a registered `DeckList` and `Format` (CR 4.1.4).
Requires exact multiset preservation (`List.Perm`) between the registered pool and the
partitioned loadout. -/
def LoadoutValid (db : CardDB) (fmt : Format) (deck : DeckList) (loadout : Loadout) : Prop :=
  loadout.hero = deck.hero ∧
  loadout.allPoolCards.Perm deck.pool ∧
  EquipSlotValid db .head loadout.head ∧
  EquipSlotValid db .chest loadout.chest ∧
  EquipSlotValid db .arms loadout.arms ∧
  EquipSlotValid db .legs loadout.legs ∧
  WeaponsValid db loadout.weapons ∧
  StartingDeckCardsValid db loadout.deck ∧
  fmt.spec.deckSize.Satisfied loadout.deck.length

instance decidableLoadoutValid (db : CardDB) (fmt : Format) (deck : DeckList) (loadout : Loadout) :
    Decidable (LoadoutValid db fmt deck loadout) := by
  unfold LoadoutValid
  infer_instance

/-- A valid loadout preserves the exact multiset of registered pool cards, I13 part 1 (CR 4.1.4). -/
theorem LoadoutValid.pool_perm {db : CardDB} {fmt : Format} {deck : DeckList} {loadout : Loadout}
    (h : LoadoutValid db fmt deck loadout) :
    loadout.allPoolCards.Perm deck.pool :=
  h.2.1

/-- A valid loadout preserves the exact total card count of the registered pool. -/
theorem LoadoutValid.pool_length {db : CardDB} {fmt : Format} {deck : DeckList} {loadout : Loadout}
    (h : LoadoutValid db fmt deck loadout) :
    loadout.allPoolCards.length = deck.pool.length :=
  h.2.1.length_eq

/-- Every card placed anywhere in a valid loadout (equipment, weapons, deck, or inventory)
remains allowed for the hero whenever the registered card-pool satisfies `CoreDeckValid`
(CR 1.1, 4.1.4). -/
theorem LoadoutValid.allCards_allowed {db : CardDB} {fmt : Format} {deck : DeckList}
    {loadout : Loadout}
    (hcore : CoreDeckValid db deck)
    (hload : LoadoutValid db fmt deck loadout) :
    ∃ heroDef, db.find? loadout.hero = some heroDef ∧
      ∀ cid ∈ loadout.allPoolCards, CardAllowedForHero db heroDef cid := by
  obtain ⟨heroDef, hhero, _, hall, _⟩ := hcore
  refine ⟨heroDef, ?_, ?_⟩
  · rw [hload.1]
    exact hhero
  · intro cid hmem
    exact hall cid (hload.2.1.subset hmem)

end Fab

end
