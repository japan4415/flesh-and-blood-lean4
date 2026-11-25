module

public import Fab.Core.Ids
public import Fab.Core.Supertype
public import Fab.Core.CardType
public import Fab.Core.Property
public import Fab.Core.Keyword

/-!
# Effect IR filters, references, expressions, and conditions

Pure syntactic building blocks for the Flesh and Blood effect IR (CR 1.7, 6.0-6.6).
This module belongs to the `Card` layer and does not import `GameState`.
-/

@[expose] public section

namespace Fab

/-- Lexical variable identifier bound by IR combinators such as die rolls or reveals. -/
structure VarId where
  /-- Zero-based binder identifier. -/
  n : Nat
deriving DecidableEq, Repr, Hashable, Ord

/-- Escape-hatch identifier for rare custom card effects (design.md §7.1). -/
structure CustomId where
  /-- Unique custom handler name. -/
  val : String
deriving DecidableEq, Repr, Hashable, Ord

/-- Zone reference in the IR, independent of `GameState` (CR 3.0-3.16). -/
inductive ZoneRef where
  /-- Player's hand (CR 3.10). -/
  | hand
  /-- Player's main deck (CR 3.7). -/
  | deck
  /-- Player's arsenal (CR 3.2). -/
  | arsenal
  /-- Player's pitch zone (CR 3.14). -/
  | pitch
  /-- Player's graveyard (CR 3.0). -/
  | graveyard
  /-- Player's banished zone (CR 3.3). -/
  | banished
  /-- Player's permanent / arena zone (CR 3.0.5, 3.13). -/
  | arena
  /-- Player's equipment zones (Head / Chest / Arms / Legs). -/
  | equipment
  /-- Player's weapon zones (CR 3.16). -/
  | weapon
  /-- Shared combat chain zone (CR 3.5). -/
  | combatChain
  /-- Player's soul zone (CR 3.9). -/
  | soul
  /-- Player's inventory zone (CR 4.1.4). -/
  | inventory
  /-- Any zone (used in replacement watchers such as "from anywhere"). -/
  | any
deriving DecidableEq, Repr

/-- Player reference in the IR. -/
inductive PlayerRef where
  /-- Controller of the source card or ability. -/
  | controller
  /-- An opposing hero (in 1v1, the opponent). -/
  | opposingHero
  /-- The attacking hero on the current combat chain. -/
  | attackingHero
  /-- The defending hero on the current combat chain. -/
  | defendingHero
  /-- The current turn player. -/
  | turnPlayer
  /-- Owner or controller of target slot `i`. -/
  | ownerOfSlot (i : Nat)
  /-- A player bound to a target slot during declaration. -/
  | seated (p : PlayerId)
deriving DecidableEq, Repr

/-- Counter kinds tracked on arena objects (CR 2.0, 8.3). -/
inductive CounterKind where
  /-- `-1{d}` defense counter (Battleworn, Temper, Guardwell, Buckling Blow). -/
  | minusOneDefense
  /-- `+1{p}` power counter (Dawnblade). -/
  | plusOnePower
  /-- Energy counter (Fyendal's Spring Tunic). -/
  | energy
  /-- Steam counter (Mechanologist items). -/
  | steam
  /-- Aim counter (Ranger arrows). -/
  | aim
  /-- Named generic counter for future sets. -/
  | named (label : String)
deriving DecidableEq, Repr

/-- Placement position when putting a card into a deck (CR 3.7). -/
inductive DeckPos where
  /-- Top of the deck. -/
  | top
  /-- Bottom of the deck. -/
  | bottom
  /-- Controller chooses top or bottom of the deck (Stroke of Foresight). -/
  | topOrBottom
  /-- Shuffled into the deck (Remembrance, Hope Merchant's Hood). -/
  | shuffle
deriving DecidableEq, Repr

/-- Duration of a continuous effect, play permission, or damage prevention shield (CR 6.2). -/
inductive Duration where
  /-- Lasts until the current chain link ends (CR 7.0). -/
  | thisChainLink
  /-- Lasts until the current combat chain closes (CR 7.7). -/
  | thisCombatChain
  /-- Lasts until the end of the current turn (CR 4.4.3). -/
  | thisTurn
  /-- Lasts during the affected player's next action phase (Spinal Crush, Cranial Crush). -/
  | nextActionPhase
  /-- The action phase in which a previously scheduled restriction is active (CR 4.3, 4.4). -/
  | thisActionPhase
  /-- Lasts until the end of the affected player's next turn (Crush Confidence). -/
  | untilEndOfNextTurn
  /-- Lasts as long as the source object remains in the arena (CR 6.2.2). -/
  | whileSourceInArena
  /-- Permanent continuous effect (no automatic expiration). -/
  | permanent
deriving DecidableEq, Repr

/-- Pure syntactic filter matching card or object characteristics (CR 2.0-2.16). -/
structure CardFilter where
  /-- Required supertypes (all listed must be present, e.g., Brute, Guardian, Ninja). -/
  supertypes : List Supertype := []
  /-- Required functional card types (all listed must be present). -/
  types : List CardType := []
  /-- Any of these subtypes must be present when non-empty (e.g., club or hammer). -/
  anySubtypes : List Subtype := []
  /-- Required subtypes (all listed must be present). -/
  subtypes : List Subtype := []
  /-- Excluded card types (e.g., non-equipment defending cards). -/
  excludeTypes : List CardType := []
  /-- Required printed or granted keywords (e.g., Combo). -/
  keywords : List KeywordInst := []
  /-- When non-empty, card name must appear in this list (e.g., Lord of Wind, Nimblism). -/
  nameIn : List String := []
  /-- Minimum printed or effective resource cost (inclusive). -/
  minCost : Option Nat := none
  /-- Maximum printed or effective resource cost (inclusive). -/
  maxCost : Option Nat := none
  /-- Minimum printed or effective power `{p}` (inclusive). -/
  minPower : Option Int := none
  /-- Maximum printed or effective power `{p}` (inclusive). -/
  maxPower : Option Int := none
  /-- Optional color strip filter. -/
  color : Option ColorStrip := none
  /-- Optional flag requiring a weapon attack (attack-proxy or weapon). -/
  isWeaponAttack : Bool := false
deriving DecidableEq, Repr

/-- Empty card filter matching any card or object. -/
def CardFilter.any : CardFilter := {}

/-- Filter matching any attack action card. -/
def CardFilter.attackAction : CardFilter :=
  { types := [.action], subtypes := [.attack] }

/-- Filter matching any weapon attack. -/
def CardFilter.weaponAttack : CardFilter :=
  { isWeaponAttack := true }

/-- Filter matching any non-equipment card. -/
def CardFilter.nonEquipment : CardFilter :=
  { excludeTypes := [.equipment] }

/-- Target category for a play-time target slot (CR 5.1.2c). -/
inductive TargetKind where
  /-- A hero. -/
  | hero
  /-- An attack action card on the combat chain or stack. -/
  | attackAction
  /-- A weapon attack on the combat chain. -/
  | weaponAttack
  /-- A weapon permanent controlled by a player. -/
  | weapon (p : PlayerRef)
  /-- An equipment permanent controlled by a player. -/
  | equipment (p : PlayerRef)
  /-- A defending card on the current chain link. -/
  | defendingCard
  /-- A card in a specific player's zone (e.g., graveyard for Lord of Wind / Remembrance). -/
  | cardInZone (p : PlayerRef) (z : ZoneRef)
deriving DecidableEq, Repr

/-- Specification of a single target slot declared when playing or activating (CR 5.1.2c). -/
structure TargetSpec where
  /-- Category of legal targets. -/
  kind : TargetKind
  /-- Additional characteristic filter on legal targets. -/
  filter : CardFilter := {}
  /-- Minimum number of targets required (`0` for "up to N"). -/
  minCount : Nat := 1
  /-- Maximum number of targets allowed (`none` means X or unbounded). -/
  maxCount : Option Nat := some 1
deriving DecidableEq, Repr

/-- Object reference inside an effect body. -/
inductive ObjRef where
  /-- The source card or ability object itself ("this"). -/
  | self_
  /-- The object(s) chosen for target slot `i` (0-indexed into `EffectDef.targets`). -/
  | slot (i : Nat)
  /-- The object bound to a target slot when a layer was put on the stack. -/
  | declared (id : ObjId)
  /-- A lexically bound object variable. -/
  | var (v : VarId)
  /-- The active attack on the current chain link. -/
  | currentAttack
  /-- The card discarded as an additional cost or triggering event. -/
  | lastDiscarded
deriving DecidableEq, Repr

/-- Integer-valued expression inside an effect body. -/
inductive NumExpr where
  /-- Constant integer value. -/
  | const (n : Int)
  /-- The chosen value of `X` from play/cost declaration (CR 5.1.2). -/
  | xValue
  /-- Integer value bound to lexical variable `v` (e.g., die roll or reveal count). -/
  | varVal (v : VarId)
  /-- Number of cards currently in player `p`'s hand (Tome of Fyendal). -/
  | handCount (p : PlayerRef)
  /-- Number of attacks that have hit on the current combat chain (Fluster Fist). -/
  | chainHits
  /-- Half of bound variable `v`, rounded down (Scabskin Leathers, Barkbone Strapping). -/
  | halfRoundDown (v : VarId)
  /-- Number of cards currently in player `p`'s Soul sub-zone (MON: Boltyn / Light). -/
  | soulCount (p : PlayerRef)
  /-- Number of cards currently in player `p`'s Banished zone (MON: Shadow / Chane / Levia). -/
  | banishedCount (p : PlayerRef)
deriving DecidableEq, Repr

/-- Boolean condition checked by static abilities, triggers, or `ifThen` combinators. -/
inductive Condition where
  /-- Always true. -/
  | always
  /-- `Combo`: previous chain link attack had name `name` (CR 8.3.6). -/
  | prevChainLinkNamed (name : String)
  /-- `Reprise`: defending hero defended with a card from hand this chain link (CR 8.3.8). -/
  | defendedFromHandThisLink
  /-- Current attack is defended by fewer than `n` non-equipment cards (Barraging Beatdown/Brawnhide). -/
  | defendedByFewerNonEquip (n : Nat)
  /-- Source card was played from arsenal (Tome of Fyendal, Unmovable, Scour the Battlescape). -/
  | playedFromArsenal
  /-- Optional additional cost was paid (Staunch Response, Regurgitating Slog, Lord of Wind). -/
  | additionalCostPaid
  /-- Last card discarded to pay for the source matches `f` (Bloodrush Bellow, Savage Feast). -/
  | lastDiscardedMatches (f : CardFilter)
  /-- Player `p` has at least `n` cards matching `f` in zone `z` (Anothos, Kodachi, Blessing). -/
  | zoneCountGe (p : PlayerRef) (z : ZoneRef) (f : CardFilter) (n : Nat)
  /-- Player `p`'s zone `z` is empty (Last Ditch Effort, Nature's Path Pilgrimage). -/
  | zoneEmpty (p : PlayerRef) (z : ZoneRef)
  /-- Controller has strictly less life than an opposing hero (Heart of Fyendal, Scar for a Scar). -/
  | lessLifeThanOpponent
  /-- A weapon controlled by controller has hit this turn (Braveforge Bracers). -/
  | weaponHitThisTurn
  /-- Source is defending a weapon attack (Steelblade Shunt). -/
  | defendingWeaponAttack
  /-- Source weapon has not hit this turn (Dawnblade). -/
  | sourceNotHitThisTurn
  /-- The source is still an object in the arena (CR 3.0.5, 3.0.9). -/
  | sourceInArena
  /-- Source has fewer than `n` counters of kind `k` (Fyendal's Spring Tunic). -/
  | sourceCounterLt (k : CounterKind) (n : Nat)
  /-- Controller has charged their hero's soul this turn (MON: Light Warrior). -/
  | chargedThisTurn
  /-- Controller has banished a card with `≥ 6{p}` this turn (MON: Levia / Shadow Brute). -/
  | banishedSixPowerThisTurn
  /-- Source card was played from the banished zone (MON: Shadow / Chane). -/
  | playedFromBanished
  /-- Conjunction of two conditions. -/
  | and_ (a b : Condition)
  /-- Disjunction of two conditions. -/
  | or_ (a b : Condition)
  /-- Negation of a condition. -/
  | not_ (c : Condition)
deriving DecidableEq, Repr

end Fab

end
