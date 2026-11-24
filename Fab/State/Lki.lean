module

public import Fab.Card.CardDef

/-!
# Last Known Information (LKI)

Immutable snapshot of an object's properties immediately before it leaves a zone or ceases to
exist (CR 1.2.3). Used when a chain link persists after its attacking card leaves the combat
chain (CR 3.5.4b) or when a previous weapon attack-proxy ceases to exist (CR 1.4.3).
-/

@[expose] public section

namespace Fab

/-- Immutable Last Known Information snapshot of an object (CR 1.2.3). -/
structure LkiSnapshot where
  /-- Logical card identifier, if derived from a card or token. -/
  cardId : Option CardId
  /-- Effective card name at the moment of the snapshot. -/
  name : String
  /-- Owner of the object. -/
  owner : PlayerId
  /-- Controller of the object at the moment of the snapshot. -/
  controller : PlayerId
  /-- Effective functional card types. -/
  types : List CardType := []
  /-- Effective subtypes. -/
  subtypes : List Subtype := []
  /-- Effective supertypes. -/
  supertypes : List Supertype := []
  /-- Effective power `{p}`, if any. -/
  power : Option Int := none
  /-- Effective defense `{d}`, if any. -/
  defense : Option Int := none
  /-- Effective keywords, such as Go Again checked at Resolution Step (CR 7.6.2). -/
  keywords : List KeywordInst := []
  /-- Number of `-1{d}` counters on the object. -/
  minusDefenseCounters : Nat := 0
  /-- Number of `+1{p}` counters on the object. -/
  plusPowerCounters : Nat := 0
deriving DecidableEq, Repr

/-- Construct an `LkiSnapshot` from a `CardFace` and basic counters. -/
def LkiSnapshot.ofFace (owner controller : PlayerId) (cardId : Option CardId)
    (face : CardFace) (minusDef plusPow : Nat := 0) : LkiSnapshot :=
  { cardId := cardId
    name := face.name
    owner := owner
    controller := controller
    types := face.types
    subtypes := face.subtypes
    supertypes := face.supertypes
    power := face.power
    defense := face.defense
    keywords := face.keywords
    minusDefenseCounters := minusDef
    plusPowerCounters := plusPow }

end Fab

end
