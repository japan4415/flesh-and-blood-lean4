module

/-!
# Formats and game modes

Constructed and limited formats from the Tournament Rules and Policy (TRP 1) and game modes.
Initial focus is 1v1 Classic Constructed (CC); types support all official formats.
-/

@[expose] public section

namespace Fab

/-- Game mode determining player count and seating rules. -/
inductive Mode where
  /-- Standard 1v1 two-player game. -/
  | duel
  /-- Ultimate Pit Fight (multiplayer free-for-all). -/
  | upf (players : Nat)
deriving DecidableEq, Repr, Hashable

/-- Official Flesh and Blood tournament formats (TRP 1). -/
inductive Format where
  /-- Classic Constructed: Adult hero, max 80 card-pool, min 60 deck, max 3 per unique card. -/
  | classicConstructed
  /-- Blitz: Young hero, max 52 card-pool, exact 40 deck, max 2 per unique card. -/
  | blitz
  /-- Living Legend: Adult hero (including LL heroes), max 80 card-pool, min 60 deck, max 3. -/
  | livingLegend
  /-- Sealed limited: Young hero, min 30 deck, no copy limit. -/
  | sealed
  /-- Booster Draft limited: Young hero, min 30 deck, no copy limit. -/
  | draft
  /-- Commoner: Young hero, max 52 card-pool, exact 40 deck, max 2, rarity restricted. -/
  | commoner
  /-- Ultimate Pit Fight multiplayer format. -/
  | upf
deriving DecidableEq, Repr, Hashable

/-- Deck-size constraint shape for a format. -/
inductive DeckSizeRule where
  /-- Deck must have at least `min` cards (CC, LL, Limited). -/
  | atLeast (min : Nat)
  /-- Deck must have exactly `exact` cards (Blitz, Commoner). -/
  | exact (exact : Nat)
deriving DecidableEq, Repr, Hashable

/-- Check whether a starting deck length satisfies a `DeckSizeRule`. -/
def DeckSizeRule.Satisfied (r : DeckSizeRule) (n : Nat) : Prop :=
  match r with
  | .atLeast m => m ≤ n
  | .exact m => n = m

instance DeckSizeRule.decidableSatisfied (r : DeckSizeRule) (n : Nat) :
    Decidable (r.Satisfied n) := by
  cases r <;> unfold DeckSizeRule.Satisfied <;> infer_instance

/-- Static deckbuilding parameters of a format (TRP 1). -/
structure FormatSpec where
  /-- Whether the hero must be an Adult hero (`true`) or Young hero (`false`). -/
  requiresAdultHero : Bool
  /-- Optional upper bound on total non-hero cards in the registered card-pool. -/
  maxCardPool : Option Nat
  /-- Starting main-deck size requirement during start-of-game loadout (CR 4.1.4). -/
  deckSize : DeckSizeRule
  /-- Optional maximum copies per unique `(name, pitch)` card (CR 2.6, 2.8). -/
  maxCopies : Option Nat
deriving DecidableEq, Repr, Hashable

/-- Return the static deckbuilding specification for each official format (TRP 1). -/
def Format.spec : Format → FormatSpec
  | .classicConstructed =>
      { requiresAdultHero := true
        maxCardPool := some 80
        deckSize := .atLeast 60
        maxCopies := some 3 }
  | .blitz =>
      { requiresAdultHero := false
        maxCardPool := some 52
        deckSize := .exact 40
        maxCopies := some 2 }
  | .livingLegend =>
      { requiresAdultHero := true
        maxCardPool := some 80
        deckSize := .atLeast 60
        maxCopies := some 3 }
  | .sealed =>
      { requiresAdultHero := false
        maxCardPool := none
        deckSize := .atLeast 30
        maxCopies := none }
  | .draft =>
      { requiresAdultHero := false
        maxCardPool := none
        deckSize := .atLeast 30
        maxCopies := none }
  | .commoner =>
      { requiresAdultHero := false
        maxCardPool := some 52
        deckSize := .exact 40
        maxCopies := some 2 }
  | .upf =>
      { requiresAdultHero := false
        maxCardPool := none
        deckSize := .atLeast 60
        maxCopies := some 2 }

/-- Number of players required by a mode. -/
def Mode.playerCount : Mode → Nat
  | .duel => 2
  | .upf n => n

end Fab

end
