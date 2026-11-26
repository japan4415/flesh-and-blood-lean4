module

public import Fab.Rules.Deck

/-!
# Tournament deck legality (Classic Constructed and other formats)

Format-specific deck construction legality from the Tournament Rules and Policy (TRP 1).
Primary initial focus is 1v1 Classic Constructed (CC): Adult hero, max 80 card-pool, min 60
starting deck, max 3 copies per unique `(name, pitch)` card, and banned / Living Legend checks.
-/

@[expose] public section

namespace Fab

/-- Whether a registered draft game pool has a young hero, compatible cards, and enough
deck-cards for the starting deck (TRP 8.2). The pod validates draft provenance. -/
def DraftDeckValid (db : CardDB) (deck : DeckList) : Prop :=
  (∃ heroDef, db.find? deck.hero = some heroDef ∧ heroDef.isYoungHero = true ∧
    ∀ cid ∈ deck.pool, CardAllowedForHero db heroDef cid) ∧
  Format.draft.spec.deckSize.Satisfied
    (deck.pool.countP fun id => (db.find? id).any CardDef.isDeckCard)

instance decidableDraftDeckValid (db : CardDB) (deck : DeckList) :
    Decidable (DraftDeckValid db deck) := by
  unfold DraftDeckValid
  haveI : Decidable (∃ heroDef, db.find? deck.hero = some heroDef ∧ heroDef.isYoungHero = true ∧
      ∀ cid ∈ deck.pool, CardAllowedForHero db heroDef cid) :=
    decidableExistsSome (db.find? deck.hero)
  infer_instance

/-- Format-specific banned, Living Legend, and restricted lists passed externally so theorems
remain independent of periodic B&R updates (TRP 1). -/
structure FormatBanList where
  /-- Banned card names (applies across all pitch values of the named card). -/
  banned : List String := []
  /-- Hero names retired via Living Legend in this format. -/
  livingLegendHeroes : List String := []
  /-- Restricted card names (1 copy limit, used in Living Legend format). -/
  restricted : List String := []
deriving DecidableEq, Repr

/-- Empty ban list (useful for testing and unrestricted casual games). -/
def FormatBanList.empty : FormatBanList := {}

/-- Every non-Unlimited unique `(name, pitch)` card in `ids` appears at most `limit` times
(CR 2.6, 2.8) (TRP 1). -/
def CopyLimitOk (db : CardDB) (limit : Nat) (ids : List CardId) : Prop :=
  ∀ cid ∈ ids, ∀ c, db.find? cid = some c → c.isUnlimited = false →
    countByUniqueKey db ids c.uniqueKey ≤ limit

instance decidableCopyLimitOk (db : CardDB) (limit : Nat) (ids : List CardId) :
    Decidable (CopyLimitOk db limit ids) := by
  unfold CopyLimitOk
  haveI : ∀ cid, Decidable (∀ c, db.find? cid = some c → c.isUnlimited = false →
      countByUniqueKey db ids c.uniqueKey ≤ limit) :=
    fun cid => decidableForallSome (db.find? cid)
  infer_instance

/-- No card in `ids` has a card name present in `bans.banned` (TRP 1). -/
def NoBannedCards (db : CardDB) (bans : FormatBanList) (ids : List CardId) : Prop :=
  ∀ cid ∈ ids, ∀ c, db.find? cid = some c → c.front.name ∉ bans.banned

instance decidableNoBannedCards (db : CardDB) (bans : FormatBanList) (ids : List CardId) :
    Decidable (NoBannedCards db bans ids) := by
  unfold NoBannedCards
  haveI : ∀ cid, Decidable (∀ c, db.find? cid = some c → c.front.name ∉ bans.banned) :=
    fun cid => decidableForallSome (db.find? cid)
  infer_instance

/-- Classic Constructed (CC) registered card-pool legality (TRP 1):
- Satisfies `CoreDeckValid`
- Hero is an Adult hero (not Young, not Pit-Fighter) and not retired in Living Legend
- Total non-hero card-pool size is at most 80
- At most 3 copies per unique `(name, pitch)` card (unless Unlimited)
- No banned cards -/
def CCDeckValid (db : CardDB) (bans : FormatBanList) (deck : DeckList) : Prop :=
  CoreDeckValid db deck ∧
  (∃ heroDef, db.find? deck.hero = some heroDef ∧
    heroDef.isAdultHero = true ∧
    heroDef.front.name ∉ bans.livingLegendHeroes ∧
    heroDef.front.name ∉ bans.banned) ∧
  deck.pool.length ≤ 80 ∧
  CopyLimitOk db 3 deck.pool ∧
  NoBannedCards db bans deck.pool

instance decidableCCDeckValid (db : CardDB) (bans : FormatBanList) (deck : DeckList) :
    Decidable (CCDeckValid db bans deck) := by
  unfold CCDeckValid
  haveI : Decidable (∃ heroDef, db.find? deck.hero = some heroDef ∧
      heroDef.isAdultHero = true ∧
      heroDef.front.name ∉ bans.livingLegendHeroes ∧
      heroDef.front.name ∉ bans.banned) :=
    decidableExistsSome (db.find? deck.hero)
  infer_instance

/-- Every legal Classic Constructed deck satisfies Core Rules deck legality, I13 (TRP 1) (CR 1.1). -/
theorem ccDeckValid_coreDeckValid {db : CardDB} {bans : FormatBanList} {deck : DeckList}
    (h : CCDeckValid db bans deck) :
    CoreDeckValid db deck :=
  h.1

/-- Any valid Classic Constructed loadout starts with at least 60 cards in the main deck
(CR 4.1.4) (TRP 1). -/
theorem ccLoadoutValid_deck_ge_60 {db : CardDB} {deck : DeckList} {loadout : Loadout}
    (h : LoadoutValid db .classicConstructed deck loadout) :
    60 ≤ loadout.deck.length :=
  h.2.2.2.2.2.2.2.2

/-- Any valid Classic Constructed deck paired with a valid CC loadout has at most 80 total
non-hero cards distributed across arena, deck, and inventory (CR 4.1.4) (TRP 1). -/
theorem ccLoadoutValid_total_le_80 {db : CardDB} {bans : FormatBanList} {deck : DeckList}
    {loadout : Loadout}
    (hcc : CCDeckValid db bans deck)
    (hload : LoadoutValid db .classicConstructed deck loadout) :
    loadout.allPoolCards.length ≤ 80 := by
  rw [hload.pool_length]
  exact hcc.2.2.1

/-- Combining CC deck legality and CC loadout legality yields exact multiset preservation and
hero-legality of every card in the loadout (I13 summary theorem). -/
theorem ccLoadoutValid_sound {db : CardDB} {bans : FormatBanList} {deck : DeckList}
    {loadout : Loadout}
    (hcc : CCDeckValid db bans deck)
    (hload : LoadoutValid db .classicConstructed deck loadout) :
    loadout.allPoolCards.Perm deck.pool ∧
    60 ≤ loadout.deck.length ∧
    loadout.allPoolCards.length ≤ 80 ∧
    (∃ heroDef, db.find? loadout.hero = some heroDef ∧
      ∀ cid ∈ loadout.allPoolCards, CardAllowedForHero db heroDef cid) :=
  ⟨hload.pool_perm,
   ccLoadoutValid_deck_ge_60 hload,
   ccLoadoutValid_total_le_80 hcc hload,
   hload.allCards_allowed hcc.1⟩

end Fab

end
