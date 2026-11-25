module

public import Fab.Core.Cost
public import Fab.Card.IR.Filter

/-!
# Effect IR syntax (abilities, primitives, combinators, continuous mods)

Deeply embedded effect IR for Flesh and Blood cards (CR 1.7, 5.1, 6.0-6.6).
Uses `mutual` list types (`EffectList`, `DieBranchList`) instead of nested `List Effect`
so Lean v4.36 derives `DecidableEq` and `Repr` cleanly (design.md §7.1).
-/

@[expose] public section

namespace Fab

/-- Timing speed at which an activated ability can be activated (CR 5.2). -/
inductive ActivationSpeed where
  /-- Action speed: requires an Action Point during own Action Phase with empty stack. -/
  | action
  /-- Instant speed: playable whenever holding priority (CR 5.2). -/
  | instant
  /-- Attack Reaction speed: playable during Reaction Step as attacking player (CR 7.4). -/
  | attackReaction
  /-- Defense Reaction speed: playable during Reaction Step as defending player (CR 7.4). -/
  | defenseReaction
deriving DecidableEq, Repr

/-- Trigger condition for a triggered ability (CR 6.6). -/
inductive Trigger where
  /-- When this card is played (CR 5.1). -/
  | onPlay
  /-- When this attacks (CR 7.2). -/
  | onAttack
  /-- When this hits (CR 7.5). -/
  | onHit
  /-- When this hits a hero specifically (CR 7.5). -/
  | onHitHero
  /-- When this attack deals at least 4 damage to a hero (CR 8.4.2). -/
  | onCrush
  /-- General damage threshold trigger: deals at least `minDmg` damage. -/
  | onDealDamage (minDmg : Nat) (toHero : Bool)
  /-- When this defends (CR 7.3). -/
  | onDefend
  /-- When the combat chain closes (CR 7.7). -/
  | onChainClose
  /-- When this enters the arena (CR 3.0.5). -/
  | onEnterArena
  /-- When this leaves the arena (CR 3.0.5). -/
  | onLeaveArena
  /-- When this is destroyed (CR 1.10). -/
  | onDestroy
  /-- When this goes from having counters of the specified kind to having none (CR 6.6.5c). -/
  | onCountersEmptied (kind : CounterKind)
  /-- When this is banished (CR 3.3). -/
  | onBanish
  /-- When this is pitched, as on Heart of Fyendal (CR 1.14.3). -/
  | onPitch
  /-- Whenever controller discards a card matching `f` (Rhinar, Romping Club). -/
  | onDiscard (f : CardFilter) (duringActionPhase : Bool)
  /-- At the start of controller's turn (Fyendal's Spring Tunic). -/
  | onStartOfTurn
  /-- At the beginning of controller's action phase (Guardian Auras, Seismic Surge). -/
  | onStartOfActionPhase
  /-- At the beginning of controller's end phase (Dawnblade, Blood Debt). -/
  | onStartOfEndPhase
  /-- When an attack action card you control hits (Katsu). -/
  | onAttackActionHit
  /-- When a weapon attack you control hits (Dorinthea, Refraction Bolters). -/
  | onWeaponAttackHit
  /-- When you play an attack action card or activate a weapon attack (Quicken). -/
  | onPlayAttackOrWeapon
  /-- When an attack action card you control is the `minLink`-th or higher chain link in a row to hit (Mask of Momentum). -/
  | onConsecutiveHitLink (minLink : Nat)
  /-- Whenever controller charges their hero's soul (MON: Boltyn). -/
  | onCharge
deriving DecidableEq, Repr

/-- Non-asset additional or activation cost (CR 1.14, 5.1.5). -/
inductive ExtraCost where
  /-- Destroy the source permanent (equipment / item activation cost). -/
  | destroySelf
  /-- Discard `n` cards at random from controller's hand (Brute cards). -/
  | discardRandom (n : Nat)
  /-- Choose and discard `n` cards matching `f` from hand. -/
  | discardChoice (f : CardFilter) (n : Nat)
  /-- Put a card from hand on the bottom of deck (Enlightened Strike). -/
  | putHandCardOnDeckBottom
  /-- Reveal a card from hand matching `f` (Demolition Crew, Flock of the Feather Walkers). -/
  | revealHandCard (f : CardFilter)
  /-- Banish `n` cards matching `f` from controller's graveyard (Nimble Strike, Regurgitating Slog). -/
  | banishFromGraveyard (f : CardFilter) (n : Nat)
  /-- Remove `n` counters of kind `k` from the source object (Fyendal's Spring Tunic). -/
  | removeCounters (k : CounterKind) (n : Nat)
  /-- Pay `n` additional generic resources `{r}` (Staunch Response). -/
  | payResources (n : Nat)
  /-- Pay `{x}` generic resources, binding `NumExpr.xValue` (Lord of Wind). -/
  | payX
deriving DecidableEq, Repr

/-- Specification of an additional cost on a card or activated ability (CR 5.1.5). -/
structure ExtraCostSpec where
  /-- The additional cost to pay. -/
  cost : ExtraCost
  /-- Whether paying this additional cost is optional ("you may ..."). -/
  optional : Bool := false
  /-- Optional condition gating when this additional cost applies (e.g., Lord of Wind Combo). -/
  cond : Option Condition := none
deriving DecidableEq, Repr

/-- Scope to which a continuous modification applies (CR 6.2-6.3). -/
inductive ModScope where
  /-- The source object itself. -/
  | self_
  /-- A specific object reference (e.g., target slot 0 or `currentAttack`). -/
  | obj (ref : ObjRef)
  /-- The paid attack layer bound to an attack-play trigger at runtime (CR 6.6.5). -/
  | paidAttack (id : ObjId)
  /-- Every attack from the weapon declared in the card's target slot. -/
  | targetedWeaponAttacks
  /-- The next card matching `f` played by controller during the duration. -/
  | nextCardPlayed (f : CardFilter)
  /-- The next attack matching `f` made by controller during the duration. -/
  | nextAttack (f : CardFilter)
  /-- Every attack matching `f` made by controller during the duration. -/
  | allAttacks (f : CardFilter)
  /-- The specified attack of this controller in each turn, counting weapons and attack cards. -/
  | attackOrdinal (ordinal : Nat)
  /-- The next card matching `f` controller defends with during the duration (Flic Flak). -/
  | nextDefend (f : CardFilter)
  /-- All cards/objects matching `f` controlled by player `p` (Forged for War, Stonewall Confidence). -/
  | allMatching (p : PlayerRef) (f : CardFilter)
  /-- All arena objects of the given type controlled by player `p` when the effect is generated. -/
  | arenaObjectsOfType (p : PlayerRef) (kind : CardType)
  /-- Player `p`'s hero (Helm of Isen's Peak, Crush Confidence). -/
  | hero (p : PlayerRef)
  /-- Player `p`'s first action during their next turn (Cartilage Crush). -/
  | firstActionNextTurn (p : PlayerRef)
  /-- Player `p`'s first attack during their next turn (Debilitate). -/
  | firstAttackNextTurn (p : PlayerRef)
  /-- Player `p`'s action cards, activated abilities, and attacks (Spinal Crush). -/
  | playerActionsAndAttacks (p : PlayerRef)
deriving DecidableEq, Repr

/-- Atomic discrete effect primitive executed by the M4/M5 interpreter (CR 1.7, 6.0). -/
inductive Prim where
  /-- Initiate a weapon attack using the source weapon (CR 1.4.3, 7.2). -/
  | weaponAttack
  /-- Player `p` draws `n` cards (CR 8.5.7). -/
  | draw (p : PlayerRef) (n : NumExpr)
  /-- Player `p` discards `n` random cards from hand. -/
  | discardRandom (p : PlayerRef) (n : NumExpr)
  /-- Discard the first `n` cards of the controller's hand after a chance permutation. -/
  | discardHandPrefix (n : Nat)
  /-- Player `p` chooses and discards `n` cards matching `f` from hand. -/
  | discardChoice (p : PlayerRef) (f : CardFilter) (n : NumExpr)
  /-- Deal `n` damage of kind `kind` to player `p`'s hero (CR 7.5, 8.5.3). -/
  | dealDamage (kind : DamageKind) (p : PlayerRef) (n : NumExpr)
  /-- Player `p` gains `n` life `{h}` (CR 8.5). -/
  | gainLife (p : PlayerRef) (n : NumExpr)
  /-- Player `p` loses `n` life `{h}`. -/
  | loseLife (p : PlayerRef) (n : NumExpr)
  /-- Player `p` gains `n` Action Points (CR 1.14.2). -/
  | gainAP (p : PlayerRef) (n : NumExpr)
  /-- Player `p` gains `n` Resource Points `{r}` (CR 1.14.2). -/
  | gainResource (p : PlayerRef) (n : NumExpr)
  /-- Player `p` gains `n` Chi Points `{c}` (CR 1.14.2). -/
  | gainChi (p : PlayerRef) (n : NumExpr)
  /-- Target opposing player `p` is intimidated (random face-down banish until End Phase) (CR 8.5.10). -/
  | intimidate (p : PlayerRef)
  /-- Banish the first card in the targeted hand after an Intimidate chance permutation. -/
  | intimidateHandFront (target : PlayerId)
  /-- Player `p` opts `n` (look at top `n` cards, put any on top or bottom) (CR 8.5.22). -/
  | opt (p : PlayerRef) (n : Nat)
  /-- Name an action card, then open boosters for matching cards (CR 1.9.1a). -/
  | openBoosters (name : Option String := none)
  /-- Create `n` copies of token `tokenId` under player `p`'s control (CR 8.5.2). -/
  | createToken (p : PlayerRef) (tokenId : CardId) (n : Nat)
  /-- Destroy object `o` (CR 8.5.5). -/
  | destroy (o : ObjRef)
  /-- Banish object `o`, optionally face-down (CR 8.5.1). -/
  | banish (o : ObjRef) (faceDown : Bool)
  /-- Move object `o` to zone `dst` with deck position `pos` and facing `faceDown`. -/
  | moveCard (o : ObjRef) (dst : ZoneRef) (pos : DeckPos) (faceDown : Bool)
  /-- Player `p` puts a chosen card from hand to deck position `pos` (Sink Below, Stroke of Foresight). -/
  | putHandOnDeck (p : PlayerRef) (pos : DeckPos)
  /-- Put a card from player `p`'s arsenal on the bottom of its owner's deck (Disable). -/
  | putArsenalOnDeckBottom (p : PlayerRef)
  /-- Choose a matching defending card on the active link to return to its owner's hand (Rout). -/
  | returnDefendingCardToHand (f : CardFilter)
  /-- Return the defending card picked during resolution. -/
  | returnChosenDefendingCard (id : ObjId)
  /-- Search `p`'s deck for up to `maxCount` cards matching `f`, move to `dst`, optionally reveal,
  and normally shuffle; optionally allow playing the banished card for `playableDuration`. -/
  | searchDeck (p : PlayerRef) (f : CardFilter) (maxCount : Option Nat) (dst : ZoneRef)
      (reveal : Bool) (playableDuration : Option Duration) (shuffleAfter : Bool := true)
      (exactCost : Option NumExpr := none)
  /-- Optionally put one matching card from hand into the arena with an additional entry counter. -/
  | putHandPermanent (p : PlayerRef) (f : CardFilter) (entryCounter : Option CounterKind := none)
  /-- Randomize the order of a player's zone using a chance decision (CR 8.5.20). -/
  | shuffleZone (p : PlayerRef) (z : ZoneRef)
  /-- Player `p` chooses up to `maxCount` cards matching `f` from `src` to shuffle into their deck.
  If `drawSame`, they then draw that many cards (Remembrance, Hope Merchant's Hood). -/
  | shuffleZoneIntoDeck (p : PlayerRef) (src : ZoneRef) (f : CardFilter)
      (maxCount : Option Nat) (drawSame : Bool)
  /-- Reveal the top card of `p`'s deck; if it matches `f`, put it into `p`'s arsenal (Nature's Path Pilgrimage). -/
  | revealTopToArsenalIf (p : PlayerRef) (f : CardFilter)
  /-- Add `n` counters of kind `k` onto object `o`. -/
  | addCounter (o : ObjRef) (k : CounterKind) (n : NumExpr)
  /-- Remove up to n counters of kind k from object o (CR 1.0.1b). -/
  | removeCounter (o : ObjRef) (k : CounterKind) (n : NumExpr)
  /-- Remove all counters of kind `k` from object `o` (Dawnblade). -/
  | removeAllCounters (o : ObjRef) (k : CounterKind)
  /-- Create a prevention shield for player `p` preventing the next `n` damage during `dur` (Bone Head Barrier). -/
  | preventNextDamage (p : PlayerRef) (n : NumExpr) (dur : Duration)
  /-- Prevent up to `n` damage from the next single event this turn (CR 6.4.10i). -/
  | preventDamageOnce (p : PlayerRef) (n : NumExpr)
  /-- Immediately close the combat chain (Phantasm, Spectra) (CR 7.7). -/
  | closeCombatChain
  /-- Charge: put a card from player `p`'s hand into their hero's Soul (CR 3.9, 8.5). -/
  | charge (p : PlayerRef)
  /-- Banish up to `n` cards from player `p`'s Soul (MON: Boltyn / Light) (CR 3.9). -/
  | banishFromSoul (p : PlayerRef) (n : Nat)
  /-- Banish the top `n` cards of player `p`'s deck, optionally face-down (MON: Chane / Levia) (CR 3.3). -/
  | banishTopDeck (p : PlayerRef) (n : Nat) (faceDown : Bool)
  /-- Banish up to `n` cards matching `f` from player `p`'s graveyard (MON: Levia / Shadow Brute) (CR 3.3). -/
  | banishFromGraveyard (p : PlayerRef) (f : CardFilter) (n : Nat)
deriving DecidableEq, Repr

/-- Event pattern watched by a static replacement ability (CR 6.4). -/
inductive ReplacementWatch where
  /-- Source object would be put into its owner's graveyard from `fromZone` (Drone of Brutality). -/
  | selfWouldGoToGraveyard (fromZone : ZoneRef)
  /-- Source object would deal damage to a hero (Pounding Gale). -/
  | selfWouldDealDamageToHero
deriving DecidableEq, Repr

mutual

/-- Deeply embedded discrete effect syntax (CR 1.7, 6.0). -/
inductive Effect where
  /-- Do nothing. -/
  | nop
  /-- Execute an atomic primitive. -/
  | prim (p : Prim)
  /-- Execute a sequence of effects in order. -/
  | seq (es : EffectList)
  /-- Conditional branch on `cond`. -/
  | ifThen (cond : Condition) (thenBranch : Effect) (elseBranch : Effect)
  /-- Optional choice: controller may perform `body`; if performed, execute `ifDone` (I18). -/
  | may (body : Effect) (ifDone : Effect)
  /-- Modal choice: choose 1 branch from `modes` (Enlightened Strike, Pummel, Razor Reflex). -/
  | chooseOne (modes : EffectList)
  /-- Roll a 6-sided die, bind the result (1-6) to `bindVar`, run matching `branches`, then `cont`. -/
  | rollDie6 (bindVar : VarId) (branches : DieBranchList) (cont : Effect)
  /-- Reveal the top `n` cards of `p`'s deck, bind the count matching `f` to `bindVar`, then run `cont` (Blessing of Deliverance). -/
  | bindRevealTopCount (p : PlayerRef) (n : Nat) (f : CardFilter) (bindVar : VarId) (cont : Effect)
  /-- Banish up to n cards from the top of a deck face up, then bind the number that match f (CR 8.5.1). -/
  | bindBanishTopCount (p : PlayerRef) (n : Nat) (f : CardFilter) (bindVar : VarId) (cont : Effect)
  /-- Trigger this body each time the controller boosts later in the same turn (CR 6.6.3, 8.3.9). -/
  | onBoostThisTurn (body : Effect)
  /-- Discard the first card in a randomized hand, then execute the branch matching its face. -/
  | discardTopOfHand (p : PlayerRef) (f : CardFilter) (ifMatches otherwise : Effect)
  /-- Apply a continuous modification `mod` over `scope` for duration `dur` (CR 6.2). -/
  | grant (scope : ModScope) (mod : ContinuousMod) (dur : Duration)
  /-- Rare escape hatch for card-specific logic that does not yet fit IR (design.md §7.1). -/
  | custom (id : CustomId) (args : List String)
deriving DecidableEq, Repr

/-- Monomorphic list of effects (avoids nested `List Effect` for `DecidableEq`). -/
inductive EffectList where
  /-- Empty effect sequence. -/
  | nil
  /-- Head effect followed by tail sequence. -/
  | cons (head : Effect) (tail : EffectList)
deriving DecidableEq, Repr

/-- Outcome range branches for a 6-sided die roll (e.g., Crazy Brew 1-2 / 3-4 / 5-6). -/
inductive DieBranchList where
  /-- No further die branches. -/
  | nil
  /-- If rolled value is in `[lo, hi]` (inclusive), execute `body`. -/
  | cons (lo hi : Nat) (body : Effect) (tail : DieBranchList)
deriving DecidableEq, Repr

/-- Continuous modification applied by static abilities or `Effect.grant` (CR 6.2-6.3). -/
inductive ContinuousMod where
  /-- Modify power `{p}` by `delta` (positive or negative). -/
  | addPower (delta : NumExpr)
  /-- Modify defense `{d}` by `delta`. -/
  | addDefense (delta : NumExpr)
  /-- Static defense bonus that applies only while the affected card is defending (CR 7.3). -/
  | addDefenseWhileDefending (delta : Int)
  /-- Modify hero intellect `{i}` by `delta` (Helm of Isen's Peak). -/
  | addIntellect (delta : Int)
  /-- Modify resource cost `{r}` by `delta` (negative reduces, positive increases; Seismic Surge, Cartilage Crush). -/
  | modifyCost (delta : Int)
  /-- Grant a keyword such as `goAgain` or `dominate`. -/
  | grantKeyword (kw : KeywordInst)
  /-- Grant a triggered ability to the affected object(s) (Pummel, Razor Reflex, Whelming Gustwave, Steelblade Supremacy). -/
  | grantTrigger (trigger : Trigger) (cond : Option Condition) (body : Effect)
  /-- Grant a conditional power modifier (Barraging Beatdown). -/
  | conditionalPower (cond : Condition) (delta : Int)
  /-- Affected hero loses all abilities (Crush Confidence). -/
  | loseAllAbilities
  /-- Affected objects lose and cannot gain Go Again (Spinal Crush). -/
  | cantGainGoAgain
  /-- Affected player cannot draw cards (Cranial Crush). -/
  | cantDrawCards
  /-- Affected weapon may attack an additional time this turn (Dorinthea). -/
  | additionalWeaponAttack
  /-- Damage dealt by affected attack to a hero is doubled (Pounding Gale). -/
  | doubleDamageToHero
  /-- Affected card may be played from its owner's banished zone during duration (MON: Shadow). -/
  | playableFromBanished
deriving DecidableEq, Repr

end

/-- Convert a standard `List Effect` into `EffectList`. -/
def EffectList.ofList : List Effect → EffectList
  | [] => .nil
  | e :: es => .cons e (EffectList.ofList es)

/-- Convenience constructor for `Effect.seq` from a `List Effect`. -/
def Effect.seqL (es : List Effect) : Effect :=
  .seq (EffectList.ofList es)

/-- Bind a hero declared for an Intimidate, preserving the order of resolution (CR 8.5.10b). -/
def Effect.bindIntimidateTarget (effect : Effect) (hero : PlayerId) : Option Effect :=
  match effect with
  | .prim (.intimidate (.ownerOfSlot 0)) => some (.prim (.intimidate (.seated hero)))
  | .seq effects => (bindSequence effects).map .seq
  | _ => none
where
  bindSequence : EffectList → Option EffectList
  | .nil => none
  | .cons (.prim (.intimidate (.ownerOfSlot 0))) rest =>
    some (.cons (.prim (.intimidate (.seated hero))) rest)
  | .cons other rest => (bindSequence rest).map (.cons other)

/-- Convenience constructor for `Effect.chooseOne` from a `List Effect`. -/
def Effect.chooseOneL (modes : List Effect) : Effect :=
  .chooseOne (EffectList.ofList modes)

/-- A single modal branch declaring its own play-time target slots and resolution body;
modes are declared before targets, as on Pummel and Razor Reflex (CR 5.1.2a, 5.1.2c). -/
structure ModeSpec where
  /-- Target slots specific to this mode. -/
  targets : List TargetSpec := []
  /-- Resolution effect body for this mode. -/
  body : Effect := .nop
  /-- A triggered ability created by this mode and checked when the attack becomes attacking. -/
  onAttack : Option Effect := none
deriving DecidableEq, Repr

/-- A complete discrete effect declaration separating play-time mode/target/cost declarations from
the effect body (CR 5.1.2-5.1.5). When `modes` is non-empty, the player chooses one `ModeSpec`
before declaring that mode's targets. -/
structure EffectDef where
  /-- Optional play-time modal choices, each with its own target slots (CR 5.1.2a). -/
  modes : List ModeSpec := []
  /-- Target slots declared at play/activation time (used when `modes` is empty), referenced via `ObjRef.slot i`. -/
  targets : List TargetSpec := []
  /-- Additional non-asset or optional costs declared at play time. -/
  extraCosts : List ExtraCostSpec := []
  /-- After paying X, shuffle X matching target cards from the controller's graveyard,
  then resolve the attached effect. The targets are declared when the trigger is stacked. -/
  onPayX : Option (CardFilter × Effect) := none
  /-- Discrete effect body executed on resolution (used when `modes` is empty). -/
  body : Effect := .nop
deriving DecidableEq, Repr

/-- An ability printed on a card face (CR 1.7, 5.2, 6.2, 6.4, 6.6). -/
inductive Ability where
  /-- Activated ability with timing speed, cost, optional once-per-turn cap, and resolution effect (CR 5.2). -/
  | activated
      (speed : ActivationSpeed)
      (oncePerTurn : Bool := false)
      (cost : AssetCost := {})
      (extraCosts : List ExtraCostSpec := [])
      (cond : Option Condition := none)
      (grantsGoAgain : Bool := false)
      (effect : EffectDef)
  /-- Triggered ability firing on `trigger` when `cond` holds (CR 6.6).
  `ordinal := some k` restricts firing to the `k`-th occurrence per turn (e.g., 1 for Katsu/Dorinthea, 2 for Dawnblade). -/
  | triggered
      (trigger : Trigger)
      (oncePerTurn : Bool := false)
      (ordinal : Option Nat := none)
      (cond : Option Condition := none)
      (effect : EffectDef)
  /-- Static ability generating a continuous effect while active (CR 6.2). -/
  | static_
      (cond : Option Condition := none)
      (scope : ModScope := .self_)
      (mod : ContinuousMod)
  /-- Static replacement ability intercepting matching events (CR 6.4). -/
  | replacement
      (stage : ReplacementStage)
      (watch : ReplacementWatch)
      (effect : EffectDef)
  /-- May place one matching main-deck card into the arena during setup (CR 4.1.5b). -/
  | setupPermanent (filter : CardFilter)
deriving DecidableEq, Repr

end Fab

end
