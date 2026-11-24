module

import Fab.Card.CardDB
import Fab.Rules.Deck
import Fab.Tournament.DeckLegality
import FabTest.Fixtures
meta import Fab.Card.CardDB
meta import Fab.Rules.Deck
meta import Fab.Tournament.DeckLegality
meta import FabTest.Fixtures

/-!
# Tests: 1v1 Classic Constructed deck legality and Start-of-Game loadout (M1)
-/

open Fab
open FabTest

-- CardDB well-formedness
#guard decide sampleDB.WF

-- Valid 1v1 CC Bravo deck and loadout pass
#guard decide (CoreDeckValid sampleDB validBravoCCDeck)
#guard decide (CCDeckValid sampleDB .empty validBravoCCDeck)
#guard decide (LoadoutValid sampleDB .classicConstructed validBravoCCDeck validBravoCCLoadout)

-- 3 Red + 3 Yellow + 3 Blue of "Sink Below" = 9 total copies by name is LEGAL (Name + Pitch key!)
#guard decide (CopyLimitOk sampleDB 3 valid60Deck)

-- 4 copies of the SAME (Name + Pitch) card is ILLEGAL in CC
#guard !decide (CCDeckValid sampleDB .empty
  { validBravoCCDeck with pool := ⟨"WTR_215_R"⟩ :: validBravoCCDeck.pool })

-- Young hero is ILLEGAL in Classic Constructed (but legal under CoreDeckValid)
#guard decide (CoreDeckValid sampleDB { validBravoCCDeck with hero := bravoYoung.id })
#guard !decide (CCDeckValid sampleDB .empty { validBravoCCDeck with hero := bravoYoung.id })

-- Living Legend hero is ILLEGAL in CC when listed in FormatBanList
#guard !decide (CCDeckValid sampleDB
  { livingLegendHeroes := ["Bravo, Showstopper"] } validBravoCCDeck)

-- Banned card name is ILLEGAL in CC across all pitch values
#guard !decide (CCDeckValid sampleDB { banned := ["Sink Below"] } validBravoCCDeck)

-- Wrong class card (Warrior Dawnblade in Guardian Bravo deck) is ILLEGAL
#guard !decide (CoreDeckValid sampleDB
  { validBravoCCDeck with pool := dawnblade.id :: validBravoCCDeck.pool })

-- Bravo Specialization ("Bravo, Showstopper") is LEGAL in Bravo, ILLEGAL in Dorinthea
#guard decide (CCDeckValid sampleDB .empty
  { validBravoCCDeck with pool := cripplingCrush.id :: validBravoCCDeck.pool })
#guard !decide (CoreDeckValid sampleDB
  { hero := dorintheaAdult.id, pool := [cripplingCrush.id] })

-- Dorinthea Specialization matches space-separated "Dorinthea Ironsong"
#guard decide (CoreDeckValid sampleDB
  { hero := dorintheaAdult.id, pool := [ironsongDetermination.id, dawnblade.id, hatchet.id] })

-- Dual 1H weapons are LEGAL in loadout
#guard decide (WeaponsValid sampleDB [dawnblade.id, hatchet.id])

-- 2H weapon + 1H weapon is ILLEGAL in loadout
#guard !decide (WeaponsValid sampleDB [anothos.id, dawnblade.id])

-- Legendary equipment (Tectonic Plating) limited to 1 copy
#guard !decide (CoreDeckValid sampleDB
  { validBravoCCDeck with pool := tectonicPlating.id :: validBravoCCDeck.pool })

-- Card-pool over 80 cards is ILLEGAL in CC (63 + 18 = 81)
#guard !decide (CCDeckValid sampleDB .empty
  { validBravoCCDeck with
    pool := validBravoCCDeck.pool ++ List.replicate 18 ⟨"WTR_190_B"⟩ })

-- CC loadout with 59 deck cards is ILLEGAL
#guard !decide (LoadoutValid sampleDB .classicConstructed validBravoCCDeck
  { validBravoCCLoadout with
    deck := valid60Deck.drop 1
    inventory := valid60Deck.take 1 })

-- CC loadout with card not matching registered pool (Perm violation) is ILLEGAL
#guard !decide (LoadoutValid sampleDB .classicConstructed validBravoCCDeck
  { validBravoCCLoadout with
    weapons := []
    inventory := [] })

-- CC loadout placing chest armor in head slot is ILLEGAL
#guard !decide (LoadoutValid sampleDB .classicConstructed validBravoCCDeck
  { validBravoCCLoadout with
    head := some tectonicPlating.id
    chest := some helmOfIsensPeak.id })

-- CC loadout putting a weapon into the starting main deck is ILLEGAL
#guard !decide (LoadoutValid sampleDB .classicConstructed validBravoCCDeck
  { validBravoCCLoadout with
    weapons := []
    deck := anothos.id :: valid60Deck })
