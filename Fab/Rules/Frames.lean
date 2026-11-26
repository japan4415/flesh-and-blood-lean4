module

public import Fab.Rules.Move
public import Fab.Rules.Reorder
public import Fab.Rules.Objects
public import Fab.Rules.Interp
public import Fab.Rules.Combat
public import Fab.Rules.CombatKeywords
public import Fab.Rules.Actions.Draw
public import Fab.Rules.Actions.Pitch
public import Fab.Tournament.Loop

/-!
# Frame transitions and automatic work (`microStep`)

Implements applying player/chance answers (`applyFrame`, `applyAction`) and single-step
automatic work (`microStep`) for:
- Start-of-Game Procedure (CR 4.1)
- Turn structure: Start Phase (CR 4.2), Action Phase (CR 4.3), End Phase (CR 4.4)
- End-of-turn procedure: optional Arsenal placement (CR 4.4.3b), Pitch-to-deck-bottom ordering
  (CR 4.4.3c), untap (CR 4.4.3d), clearing all asset pools (CR 4.4.3e), and Intellect refill
  with Turn 1 both-player draw (CR 4.4.3f)
- Concession (CR 4.5)
-/

@[expose] public section

namespace Fab

/-- Clockwise turn order starting from `first` among `n` seated players (CR 4.1.3). -/
def clockwiseFrom (n : Nat) (first : PlayerId) : List PlayerId :=
  (List.range n).map fun i => ⟨(first.n + i) % n⟩

/-- Next player clockwise after `p` in `turnOrder`. Defaults to `p` if `turnOrder` is empty. -/
def nextInOrder (order : List PlayerId) (p : PlayerId) : PlayerId :=
  match order.idxOf? p with
  | none => order.headD p
  | some idx =>
    if order.isEmpty then p
    else order.getD ((idx + 1) % order.length) p

/-- Whether a weapon zone currently holds a two-handed weapon (CR 3.16). -/
def GameState.hasTwoHandedEquipped (s : GameState) (p : PlayerId) : Bool :=
  (s.zone (.player p .weapon)).any fun wid =>
    match s.cardDefOf? wid with
    | some c => c.isTwoHanded
    | none => false

/-- Whether the hero permits a deck card to start in the arena (CR 4.1.5b). -/
def setupPermanentAllowed (s : GameState) (p : PlayerId) (card : CardDef) : Bool :=
  card.isDeckCard && ((s.zone (.player p .hero)).head?.bind s.objectFace?).any (fun hero =>
    hero.abilities.any fun
      | .setupPermanent filter => cardFaceMatches filter card.front
      | _ => false)

/-- Determine the target arena zone when player `p` equips card `id` from inventory during
Start-of-Game loadout, or `none` if `id` cannot be legally equipped right now (CR 4.1.4). -/
def loadoutEquipDest? (s : GameState) (p : PlayerId) (id : ObjId) : Option Zone :=
  if id ∈ s.zone (.player p .inventory) then
    match s.cardDefOf? id with
    | none => none
    | some c =>
      match c.equipSlot? with
      | some .head =>
        if (s.zone (.player p .head)).isEmpty then some (.player p .head) else none
      | some .chest =>
        if (s.zone (.player p .chest)).isEmpty then some (.player p .chest) else none
      | some .arms =>
        if (s.zone (.player p .arms)).isEmpty then some (.player p .arms) else none
      | some .legs =>
        if (s.zone (.player p .legs)).isEmpty then some (.player p .legs) else none
      | none =>
        let ws := s.zone (.player p .weapon)
        if c.isTwoHanded then
          if ws.isEmpty then some (.player p .weapon) else none
        else if c.isOneHanded || c.isOffHand then
          if ws.length < 2 && !s.hasTwoHandedEquipped p then some (.player p .weapon) else none
        else if c.isEquipment && c.front.keywords.contains .modular then
          if (s.zone (.player p .head)).isEmpty then some (.player p .head)
          else if (s.zone (.player p .chest)).isEmpty then some (.player p .chest)
          else if (s.zone (.player p .arms)).isEmpty then some (.player p .arms)
          else if (s.zone (.player p .legs)).isEmpty then some (.player p .legs)
          else none
        else if (s.zone (.player p .permanent)).isEmpty && setupPermanentAllowed s p c then
          some (.player p .permanent)
        else
          none
  else
    none

/-- Whether player `p` may move `id` from inventory to their starting deck during loadout
(CR 4.1.4). -/
def loadoutCanAddDeck (s : GameState) (p : PlayerId) (id : ObjId) : Bool :=
  if id ∈ s.zone (.player p .inventory) then
    match s.cardDefOf? id with
    | some c => c.isDeckCard
    | none => false
  else
    false

/-- Whether player `p` has enough cards in their starting deck to finish loadout for the
configured format (CR 4.1.4). -/
def loadoutCanFinish (s : GameState) (p : PlayerId) : Bool :=
  let deckSize := (s.zone (.player p .deck)).length + (s.zone (.player p .permanent)).length
  decide (s.config.format.spec.deckSize.Satisfied deckSize)

/-- Effective hero intellect of player `p`, defaulting to 4 if absent (CR 2.4, 4.1.6). -/
def GameState.intellectOf (s : GameState) (p : PlayerId) : Nat :=
  let hero := (s.zone (.player p .hero)).head?.bind s.characteristics
  clampNonNeg ((hero.bind (·.intellect)).getD 4)

/-- How many cards player `p` needs to draw to refill up to their hero's Intellect
(0 if already at or above Intellect) (CR 4.4.3f). -/
def GameState.refillCount (s : GameState) (p : PlayerId) : Nat :=
  s.intellectOf p - (s.zone (.player p .hand)).length

/-- Flip a single object face-up if it does not have `Cloaked` (CR 4.1.4). -/
def revealObject (db : CardDB) (o : Object) : Object :=
  let isCloaked :=
    match o.kind.cardId? with
    | some cid =>
      match db.find? cid with
      | some c => c.front.keywords.contains .cloaked
      | none => false
    | none => false
  if isCloaked then o else { o with faceDown := false }

/-- `revealObject` preserves `kind`. -/
theorem revealObject_kind (db : CardDB) (o : Object) :
    (revealObject db o).kind = o.kind := by
  unfold revealObject
  dsimp only
  split <;> (try split) <;> (try split) <;> rfl

/-- `revealObject` preserves `owner`. -/
theorem revealObject_owner (db : CardDB) (o : Object) :
    (revealObject db o).owner = o.owner := by
  unfold revealObject
  dsimp only
  split <;> (try split) <;> (try split) <;> rfl

/-- All equipped objects and selected starting permanents across all players. -/
def loadoutArenaIds (s : GameState) : List ObjId :=
  (allPlayers s.playerCount).flatMap fun p =>
    s.zone (.player p .head) ++ s.zone (.player p .chest) ++
    s.zone (.player p .arms) ++ s.zone (.player p .legs) ++
    s.zone (.player p .weapon) ++ s.zone (.player p .permanent)

/-- Simultaneously reveal the loadout across all players (CR 4.1.4, 4.1.6). -/
def revealAllLoadouts (s : GameState) : GameState :=
  let objs' := (loadoutArenaIds s).foldl (fun m id =>
    match m[id.n]? with
    | some o => m.insert id.n (revealObject s.cards o)
    | none => m) s.objects
  { s with objects := objs' }

/-- Helper lemma: updating existing entries in `objects` via `foldl` preserves key membership,
`kind`, and `owner`. -/
theorem foldl_reveal_preserves (db : CardDB) (ids : List ObjId) (m : Std.ExtTreeMap Nat Object) :
    let m' := ids.foldl (fun acc id =>
      match acc[id.n]? with
      | some o => acc.insert id.n (revealObject db o)
      | none => acc) m
    (∀ (k : Nat), k ∈ m' ↔ k ∈ m) ∧
    (∀ (k : Nat), (m'[k]?).map Object.kind = (m[k]?).map Object.kind) ∧
    (∀ (k : Nat), (m'[k]?).map Object.owner = (m[k]?).map Object.owner) := by
  induction ids generalizing m with
  | nil => exact ⟨fun _ => Iff.rfl, fun _ => rfl, fun _ => rfl⟩
  | cons id rest ih =>
    dsimp only [List.foldl_cons]
    cases hg : m[id.n]? with
    | none => exact ih m
    | some o =>
      dsimp only
      have hin : id.n ∈ m := Std.ExtTreeMap.mem_iff_isSome_getElem?.mpr (by rw [hg]; rfl)
      have hstep := ih (m.insert id.n (revealObject db o))
      refine ⟨?_, ?_, ?_⟩
      · intro k
        rw [hstep.1 k]
        simp only [Std.ExtTreeMap.mem_insert, Nat.compare_eq_eq]
        constructor
        · rintro (rfl | hk); exact hin; exact hk
        · intro hk; exact Or.inr hk
      · intro k
        rw [hstep.2.1 k]
        by_cases hk : id.n = k
        · subst hk
          simp only [Std.ExtTreeMap.getElem?_insert, Nat.compare_eq_eq, ↓reduceIte, hg,
            Option.map_some, revealObject_kind]
        · simp only [Std.ExtTreeMap.getElem?_insert, Nat.compare_eq_eq, hk, ↓reduceIte]
      · intro k
        rw [hstep.2.2 k]
        by_cases hk : id.n = k
        · subst hk
          simp only [Std.ExtTreeMap.getElem?_insert, Nat.compare_eq_eq, ↓reduceIte, hg,
            Option.map_some, revealObject_owner]
        · simp only [Std.ExtTreeMap.getElem?_insert, Nat.compare_eq_eq, hk, ↓reduceIte]

/-- `revealAllLoadouts` preserves `WF`. -/
theorem revealAllLoadouts_wf {s : GameState} (hwf : s.WF) :
    (revealAllLoadouts s).WF := by
  unfold revealAllLoadouts
  exact GameState.WF.congr_mem hwf rfl
    (foldl_reveal_preserves s.cards (loadoutArenaIds s) s.objects).1 rfl rfl

/-- `revealAllLoadouts` preserves `OwnerOk`. -/
theorem revealAllLoadouts_ownerOk {s : GameState} (hok : s.OwnerOk) :
    (revealAllLoadouts s).OwnerOk := by
  refine ⟨fun p k hk id hid o hobj => ?_⟩
  have hown := (foldl_reveal_preserves s.cards (loadoutArenaIds s) s.objects).2.2 id.n
  change (revealAllLoadouts s).objects[id.n]? = some o at hobj
  have hzone : (revealAllLoadouts s).zone (.player p k) = s.zone (.player p k) := rfl
  rw [hzone] at hid
  unfold revealAllLoadouts at hobj
  dsimp only at hobj
  rw [hobj] at hown
  cases hg : s.objects[id.n]? with
  | none => rw [hg] at hown; simp at hown
  | some o0 =>
    rw [hg] at hown
    simp only [Option.map_some, Option.some.injEq] at hown
    rw [hown]
    exact hok.owner p k hk id hid o0 hg

/-- `revealAllLoadouts` preserves `physIds` (I1). -/
theorem revealAllLoadouts_physIds (s : GameState) :
    (revealAllLoadouts s).physIds = s.physIds := by
  unfold GameState.physIds
  have hids : (revealAllLoadouts s).zoneIds = s.zoneIds := rfl
  rw [hids]
  apply filterMap_congr_mem
  intro id _
  have hk := (foldl_reveal_preserves s.cards (loadoutArenaIds s) s.objects).2.1 id.n
  simp only [GameState.obj?, revealAllLoadouts]
  cases h1 : ((loadoutArenaIds s).foldl (fun m id =>
      match m[id.n]? with
      | some o => m.insert id.n (revealObject s.cards o)
      | none => m) s.objects)[id.n]? with
  | none =>
    rw [h1] at hk
    cases h2 : s.objects[id.n]? with
    | none => rfl
    | some o2 => rw [h2] at hk; simp at hk
  | some o1 =>
    rw [h1] at hk
    cases h2 : s.objects[id.n]? with
    | none => rw [h2] at hk; simp at hk
    | some o2 =>
      rw [h2] at hk
      simp only [Option.map_some, Option.some.injEq] at hk
      simp [hk]

/-- Turn-player selected for turn index `turnIdx` (0-based before increment) from `turnOrder`. -/
def turnPlayerAt (order : List PlayerId) (turnIdx : Nat) : PlayerId :=
  if order.isEmpty then ⟨0⟩
  else order.getD (turnIdx % order.length) ⟨0⟩

/-- Standard frame sequence for a single turn of turn-player `tp`: Start Phase → Action Phase →
End Phase (CR 4.2-4.4). -/
def turnFrames (tp : PlayerId) : List Frame :=
  [.startPhaseWork tp, .actionPhaseStart tp, .endPhaseStart tp]

/-- Draw frames scheduled during End Phase cleanup (CR 4.4.3f):
- On Turn 1 (first turn of the game), **all** players draw up to their hero's Intellect.
- On Turn ≥ 2, **only** the turn-player `tp` draws up to their hero's Intellect. -/
def endPhaseDrawFrames (s : GameState) (tp : PlayerId) : List Frame :=
  let targets := if s.turn = 1 then s.turnOrder else [tp]
  targets.map fun q => Frame.draw q (s.refillCount q)

/-- All pitchable cards currently in player `p`'s hand (CR 1.14.3). -/
def pitchableCards (s : GameState) (p : PlayerId) : List ObjId :=
  (s.zone (.player p .hand)).filter (canPitchCard s p)

/-- Whether player `p` may legally pitch a card to pay `cost` under no over-pitching: there must
be a positive resource or chi deficit and at least one pitchable card in hand (CR 1.14.3b). -/
def canPitchForCost (s : GameState) (p : PlayerId) (cost : AssetCost) : Bool :=
  (0 < (s.poolOf p).resourceDeficit cost || 0 < (s.poolOf p).chiDeficit cost) &&
  !(pitchableCards s p).isEmpty

/-- Whether the defense reaction can defend this link from its original zone (CR 7.4.2d, 8.3.4). -/
def canLinkTakeDefenseReaction (s : GameState) (link : ChainLink) (p : PlayerId)
    (fromHand : Bool) : Bool :=
  link.defender == p &&
    !(fromHand && linkHasKeyword s link .dominate && 1 ≤ link.defendingFromHand.length)

/-- A card or selected mode with a required single-attack target needs a matching active attack. -/
def hasRequiredAttackTarget (s : GameState) (card : CardDef) (modeIdx : Option Nat) : Bool :=
  match singleAttackTargetSpec card modeIdx with
  | none => true
  | some spec =>
    (s.combat.bind CombatChain.activeLink?).any fun link => (matchingActiveAttack s link spec).isSome

/-- A printed play mode is available when its required attack target can be declared. -/
def canPickCardMode (s : GameState) (layerId : ObjId) (idx : Nat) : Bool :=
  ((s.cardDefOf? layerId).map fun card => hasRequiredAttackTarget s card (some idx)).getD true

/-- An attack reaction with modes must have at least one available mode before it can be played. -/
def attackReactionCanTarget (s : GameState) (card : CardDef) : Bool :=
  let modeCount := (card.front.playEffect.map (·.modes.length)).getD 0
  if modeCount = 0 then hasRequiredAttackTarget s card none
  else (List.range modeCount).any fun idx => hasRequiredAttackTarget s card (some idx)

/-- The public weapon permanents matching a card's single required weapon target (CR 1.8.5). -/
def cardWeaponTargetChoices (s : GameState) (p : PlayerId) (card : CardDef) : Option (List ObjId) := do
  let effect ← card.front.playEffect
  let [spec] := effect.targets | none
  let controller ← match spec.kind with
    | .weapon who => some (some (evalPlayerRef s p who))
    | .anyWeapon => some none
    | _ => none
  if spec.minCount != 1 || spec.maxCount != some 1 then none else
    some ((activationArenaZones s).flatMap s.zone |>.filter fun id =>
      (s.obj? id).any (fun obj => !obj.faceDown) &&
        match s.objectFace? id, s.characteristics id with
        | some face, some chars =>
          controller.all (· == chars.controller) && chars.types.contains .weapon &&
            cardFaceMatches spec.filter { face with
              types := chars.types, subtypes := chars.subtypes, keywords := chars.keywords,
              cost := chars.baseCost }
        | _, _ => false)

/-- Card IDs that might supply plays during priority (CR 5.1.1a). -/
def playCardCandidateIds (s : GameState) (p : PlayerId) : List ObjId :=
  s.zone (.player p .hand) ++ s.zone (.player p .arsenal) ++ s.zone (.player p .banished)

/-- A face-up banished card requires a live play permission belonging to this player (CR 5.1.1a). -/
def canPlayFromBanished (s : GameState) (p : PlayerId) (id : ObjId)
    (asInstant : Bool := false) : Bool :=
  (s.zone (.player p .banished)).contains id &&
    (s.obj? id).any (fun obj => !obj.faceDown) &&
    s.activeEffects.any fun effect =>
      effect.controller == p && effect.target == .obj id &&
      match effect.op with
      | .allowBanishedPlayAsInstant _ => true
      | .allowBanishedPlay attack =>
        !asInstant && attack.all (fun source => ((s.combat.bind CombatChain.activeLink?).bind (·.attack)) == some source)
      | _ => false

/-- Resource discount granted by this player's instant-speed permission for a banished card. -/
def banishedPlayDiscount (s : GameState) (p : PlayerId) (id : ObjId) : Nat :=
  if canPlayFromBanished s p id true then
    s.activeEffects.foldl (fun amount effect =>
      match effect.op with
      | .allowBanishedPlayAsInstant discount =>
        if effect.controller == p && effect.target == .obj id then amount + discount else amount
      | _ => amount) 0
  else 0

/-- Whether this effect applies to the player's next matching action card (CR 8.1.1d). -/
def ContinuousEffect.appliesNextInstant (effect : ContinuousEffect) (p : PlayerId) (face : CardFace) :
    Bool :=
  effect.target == .player p && !effect.waitsForNextTurn && face.hasType .action &&
    match effect.op with
    | .nextCardAsInstant filter _ => cardFaceMatches filter face
    | _ => false

/-- Whether player `p` may announce playing card `id` from an allowed zone while holding priority
(CR 5.1.1, 4.3, 3.2.2, 7.1, 7.4, 7.6).
- Instants: playable anytime on priority.
- Actions: own Action Phase, empty stack, ≥1 AP, and either combat chain closed or (for Attack
  Action cards) in Resolution Step to continue a combat chain.
- Attack Reactions: Reaction Step as the attacking player (CR 7.4).
- Defense Reactions: Reaction Step as the defending player, respecting Dominate from hand (CR 7.4, 8.3.4). -/
def canPlayCard (s : GameState) (p : PlayerId) (id : ObjId) (asInstant : Bool := false) : Bool :=
  let fromHand := id ∈ s.zone (.player p .hand)
  let fromArsenal := id ∈ s.zone (.player p .arsenal)
  if fromHand || fromArsenal || canPlayFromBanished s p id then
    match s.cardDefOf? id with
    | none => false
    | some c =>
      let meetsRequirement := c.front.playRequirement.all fun
        | .boostedAtLeast count => decide (count ≤ s.boostsThisTurn.count p)
      -- An arrow can only be played from arsenal while its player controls a bow (CR 8.2.6).
      let arrowAllowed :=
        if (s.characteristics id).any (fun chars => chars.subtypes.contains .arrow) then
          fromArsenal && ((activationArenaZones s).flatMap s.zone).any fun bow =>
            (s.obj? bow).any (fun obj => !obj.faceDown) &&
              (s.characteristics bow).any (fun chars =>
                chars.controller == p && chars.types.contains .weapon && chars.subtypes.contains .bow)
        else true
      let arsenalRequired := s.activeEffects.any fun effect =>
        effect.target == .player p && effect.op == .onlyPlayFromArsenal && !effect.waitsForNextTurn
      let hasTimingPermission := s.activeEffects.any (·.appliesNextInstant p c.front)
      if !c.isDeckCard || !meetsRequirement || !arrowAllowed || (arsenalRequired && !fromArsenal) ||
          (asInstant && !hasTimingPermission) then
        false
      else if c.front.hasType .instant then
        true
      else if c.front.hasType .action && (asInstant || canPlayFromBanished s p id true) then
        s.canTakeAction p && (cardWeaponTargetChoices s p c).all (fun targets => !targets.isEmpty)
      else if c.front.hasType .action then
        let chainOk :=
          match s.combat with
          | none => true
          | some cc => cc.step == .resolution && c.front.hasSubtype .attack
        s.phase == .actionPhase &&
        s.active == some p &&
        (s.zone .stack).isEmpty &&
        chainOk &&
        (cardWeaponTargetChoices s p c).all (fun targets => !targets.isEmpty) &&
        s.canTakeAction p &&
        1 ≤ (s.poolOf p).actionPoints
      else if c.front.hasType .attackReaction then
        match s.combat with
        | some cc =>
          cc.step == .reaction &&
          match cc.activeLink? with
          | some link => link.attacker == p && attackReactionCanTarget s c
          | none => false
        | none => false
      else if c.front.hasType .defenseReaction then
        match s.combat with
        | some cc =>
          cc.step == .reaction &&
          match cc.activeLink? with
          | some link => canLinkTakeDefenseReaction s link p fromHand
          | none => false
        | none => false
      else
        false
  else
    false

/-- Whether object `id` on `Zone.stack` is an Attack layer (Attack Action card or weapon
`attackProxy`) that enters the Combat Chain on resolution (CR 7.1, 7.2). -/
def isAttackLayer (s : GameState) (id : ObjId) : Bool :=
  match s.obj? id with
  | none => false
  | some o =>
    match o.kind with
    | .attackProxy _ _ => true
    | .card _ _ =>
      match s.cardDefOf? id with
      | some c => c.front.hasType .action && c.front.hasSubtype .attack
      | none => false
    | _ => false

/-- Strip a trailing `.combatStep .close _` frame when chaining a new attack during Resolution
Step so the Combat Chain remains open for Link 2+ (CR 7.6). -/
def dropPendingClose : List Frame → List Frame
  | .combatStep .close _ :: tail => tail
  | rest => rest

/-- Base `AssetCost` of playing card `c`, applying resource floor semantics (CR 5.1.5). -/
def cardPlayCost (c : CardDef) : AssetCost :=
  let base := c.front.cost.getD {}
  let ap := if c.front.hasType .action then max base.actionPoints 1 else base.actionPoints
  { base with actionPoints := ap }

/-- Check whether an effect increases the cost of the player's next action. -/
def ContinuousEffect.isNextActionCostFor (effect : ContinuousEffect) (p : PlayerId) : Bool :=
  !effect.waitsForNextTurn && effect.target == .nextActionBy p &&
    (match effect.op with | .addCostRes _ => true | _ => false)

/-- Consume the next-action surcharge and one use of each action allowance on a paid action. -/
def effectsAfterPayingAction (effects : List ContinuousEffect) (p : PlayerId) : List ContinuousEffect :=
  (effects.filter (fun effect => !effect.isNextActionCostFor p)).map fun effect =>
    match effect.op with
    | .limitActions remaining =>
      if effect.duration == .thisActionPhase && effect.target == .player p then
        { effect with op := .limitActions (remaining - 1) }
      else effect
    | _ => effect

/-- Sum the waiting increases before applying any discounts (CR 5.1.7). -/
def nextActionSurcharge (s : GameState) (p : PlayerId) : Nat :=
  s.activeEffects.foldl (fun total effect =>
    match effect.op with
    | .addCostRes n => if effect.isNextActionCostFor p then total + n else total
    | _ => total) 0

/-- Resource surcharges applying to the player's first attack (CR 5.1.7). -/
def nextAttackSurcharge (s : GameState) (p : PlayerId) : Nat :=
  s.activeEffects.foldl (fun total effect =>
    match effect.target, effect.op with
    | .nextAttackBy player, .addCostRes amount =>
      if player == p && !effect.waitsForNextTurn then total + amount else total
    | _, _ => total) 0

/-- Count face-up permanents with a given card ID using their effective controller. -/
def controlledPermanentCount (s : GameState) (p : PlayerId) (card : CardId) : Nat :=
  let permanents := (allPlayers s.playerCount).flatMap fun owner => s.zone (.player owner .permanent)
  (permanents.filter fun obj =>
    (s.obj? obj).any (fun o => !o.faceDown && o.kind.cardId? == some card) &&
      (s.characteristics obj).any (fun chars => chars.controller == p)).length

/-- Resource adjustments from the announced card's own static abilities (CR 5.1.7). -/
def cardStaticResourceAdjustment (s : GameState) (p : PlayerId) (card : CardDef) : Int :=
  card.front.abilities.foldl (fun total ability =>
    match ability with
    | .static_ none .self_ (.modifyPlayCostPerPermanent permanent delta) =>
      total + delta * Int.ofNat (controlledPermanentCount s p permanent)
    | _ => total) 0

/-- Resource adjustments applying to the announced action (CR 5.1.7). -/
def cardResourceAdjustment (s : GameState) (p : PlayerId) (card : CardDef) : Int :=
  cardStaticResourceAdjustment s p card +
  (if card.front.hasType .action then
    let attackSurcharge := if card.front.hasSubtype .attack then nextAttackSurcharge s p else 0
    s.activeEffects.foldl (fun total effect =>
      match effect.target with
      | .nextAttackCard filter =>
        if card.front.hasSubtype .attack && effect.controller == p &&
            !filter.isWeaponAttack && cardFaceMatches filter card.front then
          match effect.op with
          | .addCostRes n => total + Int.ofNat n
          | .subCostRes n => total - Int.ofNat n
          | _ => total
        else total
      | _ => total) (Int.ofNat (nextActionSurcharge s p + attackSurcharge))
  else 0)

/-- Apply the announcing player's action and next-attack cost modifiers (CR 5.1.7). -/
def modifiedCardPlayCost (s : GameState) (p : PlayerId) (card : CardDef)
    (additionalResources : Nat := 0) (banishedDiscount : Nat := 0) : AssetCost :=
  let printed := cardPlayCost card
  let base := Int.ofNat (printed.resources + additionalResources)
  { printed with resources := clampNonNeg (base + cardResourceAdjustment s p card - Int.ofNat banishedDiscount) }

/-- Number of play-time modes (`ModeSpec`s) declared on `c`'s `playEffect` (CR 5.1.2a). -/
def cardModeCount (c : CardDef) : Nat :=
  match c.front.playEffect with
  | some ed => ed.modes.length
  | none => 0

/-- Extract the discrete resolution `Effect` of card `c` given an optional chosen mode index. -/
def cardResolveEffect (c : CardDef) (modeIdx : Option Nat) : Effect :=
  match c.front.playEffect with
  | none => .nop
  | some ed =>
    match modeIdx with
    | some idx =>
      match ed.modes[idx]? with
      | some ms => ms.body
      | none => ed.body
    | none => ed.body

/-- Matching targets in the controller's graveyard (CR 1.8.5d). -/
def graveyardTargetChoices (s : GameState) (p : PlayerId) (filter : CardFilter) : List ObjId :=
  (s.zone (.player p .graveyard)).filter fun id =>
    (s.objectFace? id).any (cardFaceMatches filter)

/-- Before an attack joins the chain, Combo reads its last existing attack (CR 8.3.6). -/
def playCostCondition (s : GameState) (p : PlayerId) (source : ObjId) (fromArsenal : Bool) :
    Condition → Bool
  | .prevChainLinkNamed name =>
    (s.combat.bind CombatChain.activeLink?).any (fun link => link.attackLki.name == name)
  | condition => evalCondition s p source fromArsenal condition

/-- Resource-equivalent assets available from pitching are private to the payer (CR 1.14.3). -/
def potentialResourceEnergy (s : GameState) (p : PlayerId) : Nat :=
  (pitchableCards s p).foldl (fun amount id => amount + ((s.objectFace? id).bind (·.pitch)).getD 0)
    (s.poolOf p).totalEnergy

/-- Bound the offered X choices by the energy available to pay the printed cost (CR 5.1.3a). -/
def printedXLimit (s : GameState) (p : PlayerId) (card : CardDef)
    (banishedDiscount : Nat := 0) : Nat :=
  let base := cardPlayCost card
  let available := Int.ofNat (potentialResourceEnergy s p) - Int.ofNat (base.resources + base.chi)
  (available - cardResourceAdjustment s p card + Int.ofNat banishedDiscount).toNat / card.front.xCostFactor

/-- Declare supported variable or additional costs before asset payment (CR 5.1.3, 5.1.6). -/
def cardPaymentFrame (s : GameState) (p : PlayerId) (layerId : ObjId) (fromArsenal : Bool)
    (modeIdx : Option Nat) (cost : AssetCost) : Frame :=
  let card := s.cardDefOf? layerId
  let face : Option CardFace := card.map (·.front)
  let playEffect : Option EffectDef := face.bind (·.playEffect)
  let discount := ((s.layerMeta.get? layerId.n).map (·.banishedResourceDiscount)).getD 0
  let printedLimit := card.bind fun c =>
    if c.front.xCostFactor > 0 then some (printedXLimit s p c discount) else none
  if let some limit := printedLimit then
    .chooseVariableResources p layerId fromArsenal modeIdx cost limit false
  else if face.any (fun face => face.keywords.contains .boost) && !(s.zone (.player p .deck)).isEmpty then
    .chooseOptionalPlayCost p layerId fromArsenal modeIdx cost .boost
  else match playEffect with
  | some { extraCosts := [{ cost := .payResources extra, optional := true, cond := none }], .. } =>
    .chooseOptionalPlayCost p layerId fromArsenal modeIdx cost (.resources extra)
  | some { extraCosts := [{ cost := .payX, optional := true, cond := cond }],
           onPayX := some (filter, _), .. } =>
    if cond.all (playCostCondition s p layerId fromArsenal) then
      .chooseVariableResources p layerId fromArsenal modeIdx cost
        (graveyardTargetChoices s p filter).length
    else .playPayCost p layerId fromArsenal modeIdx cost
  | some { extraCosts := [{ cost := .banishFromGraveyard filter 1, optional := true, cond := none }], .. } =>
    let candidates := (s.zone (.player p .graveyard)).filter fun id =>
      (s.objectFace? id).any (cardFaceMatches filter)
    if candidates.isEmpty then .playPayCost p layerId fromArsenal modeIdx cost
    else .chooseGraveyardCost p layerId fromArsenal modeIdx cost candidates
  | _ => .playPayCost p layerId fromArsenal modeIdx cost

/-- Targets printed on the card or selected play-time mode (CR 5.1.4a). -/
def cardPlayTargets (card : CardDef) (modeIdx : Option Nat) : List TargetSpec :=
  (card.front.playEffect.map fun effect =>
    (modeIdx.bind (fun idx => effect.modes[idx]?)).map (·.targets) |>.getD effect.targets).getD []

/-- Legal candidates for a hero declared before paying for a card (CR 5.1.4a). -/
def cardPlayHeroChoices (s : GameState) (p : PlayerId) (layerId : ObjId)
    (modeIdx : Option Nat) : List PlayerId :=
  let targets := ((s.cardDefOf? layerId).map (cardPlayTargets · modeIdx)).getD []
  if targets == [{ kind := .opposingHero }] then s.turnOrder.filter (· != p) else s.turnOrder

/-- Select target declaration or cost payment after any required mode has been chosen (CR 5.1.4a). -/
def cardPlayTargetFrame (s : GameState) (p : PlayerId) (layerId : ObjId) (fromArsenal : Bool)
    (modeIdx : Option Nat) (cost : AssetCost) : Frame :=
  let pay := cardPaymentFrame s p layerId fromArsenal modeIdx cost
  match s.cardDefOf? layerId with
  | none => pay
  | some card =>
    let targets := cardPlayTargets card modeIdx
    match cardWeaponTargetChoices s p card with
    | some weapons => .choosePlayWeapon p layerId fromArsenal modeIdx cost weapons
    | none =>
      let body := cardResolveEffect card modeIdx
      let needsPair := targets == [{ kind := .hero }, { kind := .hero }] &&
        match body with
        | .prim (.dealArcaneDamageToPair (.ownerOfSlot 0) (.ownerOfSlot 1) _) => true
        | _ => false
      let needsSingle := (targets == [{ kind := .hero }] || targets == [{ kind := .opposingHero }]) &&
        (body.bindHeroTarget p).isSome
      if needsPair || needsSingle then .choosePlayHero p layerId fromArsenal modeIdx cost else pay

/-- Bind the unique attack target before payment. Hero targets use their existing choice frame. -/
def cardAttackTarget? (s : GameState) (layerId : ObjId) (modeIdx : Option Nat) : Option ObjId := do
  let card ← s.cardDefOf? layerId
  let spec ← singleAttackTargetSpec card modeIdx
  let link ← s.combat.bind CombatChain.activeLink?
  matchingActiveAttack s link spec

/-- Record an automatically declared attack target in the layer's metadata. -/
def layerMetaWithAttackTarget (s : GameState) (p : PlayerId) (layerId : ObjId)
    (target : Option ObjId) : Std.ExtTreeMap Nat LayerInfo :=
  match target with
  | none => s.layerMeta
  | some attack =>
    let info := s.layerMeta.getD layerId.n { controller := p }
    s.layerMeta.insert layerId.n { info with attackTarget := some attack }

/-- Read the card-layer's resolution effect with its declared hero target bound. -/
def cardLayerEffect (s : GameState) (layerId : ObjId) (info : LayerInfo) : Effect :=
  match s.cardDefOf? layerId with
  | none => .nop
  | some card =>
    let effect := cardResolveEffect card info.modeIdx
    if info.weaponTarget.any (fun id => !(cardWeaponTargetChoices s info.controller card).any (·.contains id)) then
      .nop
    else match effect, info.heroTarget, info.secondHeroTarget with
    | .prim (.dealArcaneDamageToPair (.ownerOfSlot 0) (.ownerOfSlot 1) amount), some first, some second =>
      .prim (.dealArcaneDamageToPair (.seated first) (.seated second) amount)
    | _, target, _ => (target.bind effect.bindHeroTarget).getD effect

/-- Whether the card-layer is a defense reaction. -/
def isDefenseReactionLayer (s : GameState) (id : ObjId) : Bool :=
  (s.cardDefOf? id).any fun card => card.front.hasType .defenseReaction

/-- Recheck whether a defense reaction can become a defender when it resolves (CR 5.3.2b). -/
def canResolveDefenseReaction (s : GameState) (info : LayerInfo) : Bool :=
  (s.combat.bind CombatChain.activeLink?).any fun link =>
    canLinkTakeDefenseReaction s link info.controller !info.fromArsenal

/-- Apply a next-defender effect to the first defending card, in declaration order (CR 7.3.2c). -/
def nextDefendEffects (s : GameState) (p : PlayerId) (id : ObjId) (sourceLayer : Option ObjId := none) :
    List ContinuousEffect :=
  let matchesDefender (filter : CardFilter) :=
    match s.objectFace? id, s.characteristics id with
    | some printed, some effective =>
      cardFaceMatches filter { printed with keywords := effective.keywords }
    | _, _ => false
  s.activeEffects.filterMap fun effect =>
    match effect.target with
    | .nextDefend filter =>
      if effect.controller != p || sourceLayer == some effect.source then some effect
      else if matchesDefender filter then
        some { effect with target := .obj id, duration := .thisChainLink }
      else none
    | _ => some effect

/-- Keep a defense reaction's card-specific modifier when it becomes a defender. The engine
rekeys the object on this move, while its defense effect still applies (CR 3.0.9, 5.3.6b). -/
def defenseReactionEffects (effects : List ContinuousEffect) (layer card : ObjId) :
    List ContinuousEffect :=
  effects.map fun effect =>
    match effect.op with
    | .addDefense _ =>
      if effect.target == .obj layer && effect.duration == .thisChainLink then
        { effect with target := .obj card, source := if effect.source == layer then card else effect.source }
      else
        effect
    | _ => effect

/-- Roll back an in-progress card play to the saved pre-play snapshot (CR 5.1.1), falling back to
`fallback` if no snapshot was present. -/
def rollbackPlay (s : GameState) (fallback : List Frame) : GameState :=
  match s.playRollback with
  | some snap => s.restore snap
  | none => { s with pending := fallback }

/-- Spend `cost` from player `p`'s pool when `canPay` holds, using chi for generic resources only
as needed (CR 1.14.2b, 5.1.6). -/
def spendAssetCost (s : GameState) (p : PlayerId) (cost : AssetCost) : Option GameState :=
  let pool := s.poolOf p
  let chiForRes := cost.resources - pool.resources
  match pool.spend cost chiForRes with
  | some pool' => some (s.setPool p pool')
  | none => none

/-- Equipment characteristics checked for a requirement tied to a player (CR 1.8.5). -/
def equipmentControlledBy (s : GameState) (p : PlayerId) (id : ObjId) : Bool :=
  (s.obj? id).any (fun o => !o.faceDown) &&
    (s.characteristics id).any (fun c => c.controller == p && c.types.contains .equipment)

/-- A target must still be equipment in the arena controlled by the required player (CR 1.8.9, 3.1). -/
def matchesTriggerEquipment (s : GameState) (p : PlayerId) (id : ObjId) : Bool :=
  ((activationArenaZones s).flatMap s.zone).contains id && equipmentControlledBy s p id

/-- Legal declarations for a pending trigger. Equipment defending on the chain is in the arena. -/
def PendingTrigger.targetChoices (t : PendingTrigger) (s : GameState) :
    List (Option PlayerId × Option ObjId) :=
  match t.equipmentTargetPlayer with
  | some p =>
    ((activationArenaZones s).flatMap s.zone).filterMap fun id =>
      if equipmentControlledBy s p id then some (none, some id) else none
  | none => (t.heroChoices s.turnOrder).map fun p => (p, none)

/-- Match a declaration against a trigger and its target choices (CR 6.6.6a). -/
def PendingTrigger.matchesDeclaration (t : PendingTrigger) (s : GameState) (id : Nat) (p : PlayerId)
    (hero : Option PlayerId) (equipment : Option ObjId) : Bool :=
  t.id == id && t.controller == p && (t.targetChoices s).contains (hero, equipment)

/-- Advance to the next player in `order` who still controls at least one pending triggered ability,
returning `[.chooseTriggerOrder q rem]` or `[]` when all pending triggers are stacked (CR 6.6.6b). -/
def nextTriggerFrame (s : GameState) : List PlayerId → List Frame
  | [] => []
  | q :: rem =>
    if s.pendingTriggers.any (fun t => t.controller == q) then
      [.chooseTriggerOrder q rem]
    else
      nextTriggerFrame s rem

/-- Players receive no priority in the Start or End Phase (CR 4.2.1, 4.4.1). -/
def phaseResolvesWithoutPriority (phase : Phase) : Bool :=
  phase == .startPhase || phase == .endPhase

/-- Resolve remaining Start or End Phase layers without granting priority (CR 4.2.2, 4.4.2). -/
def afterLayerResolution (s : GameState) : Frame :=
  if phaseResolvesWithoutPriority s.phase then .resolveStack else .priority (s.active.getD ⟨0⟩) 0

/-- The source of a resolving ability layer, or the resolving card itself. -/
def resolvingSource (s : GameState) (layer : ObjId) : ObjId :=
  match (s.obj? layer).map Object.kind with
  | some (.layer src _ _ _) => src
  | _ => layer

/-- Whether the engine supports the required declarations for a triggered effect (CR 6.6.6a). -/
def supportsTriggerTargets (effect : EffectDef) (damageRecipient : Option PlayerId := none) : Bool :=
  effect.targets.isEmpty ||
    (effect.targets == [{ kind := .hero }] &&
      effect.body == .prim (.intimidate (.ownerOfSlot 0))) ||
    (effect.targets == [{ kind := .opposingHero }] &&
      (effect.body.bindOpposingHeroDamage ⟨0⟩).isSome) ||
    (damageRecipient.isSome && effect.targets == [{ kind := .equipment .defendingHero }] &&
      match effect.body with
      | .prim (.addCounter (.slot 0) _ _) => true
      | _ => false)

/-- Find matching triggers and their once-per-turn flags (CR 6.6). -/
def matchingCardTriggers (s : GameState) (source : ObjId) (controller : PlayerId) (fromArsenal : Bool)
    (abilities : List Ability) (matchesEvent : Trigger → Option Condition → Bool)
    (matchesOrdinal : Option Nat → Bool := Option.isNone) (damageRecipient : Option PlayerId := none) :
    List (PendingTrigger × Bool) :=
  abilities.zipIdx.filterMap fun (ability, abilityIdx) =>
    match ability with
    | .triggered trigger once ordinal cond eff =>
      if matchesOrdinal ordinal && matchesEvent trigger cond && supportsTriggerTargets eff damageRecipient && eff.modes.isEmpty &&
          eff.extraCosts.isEmpty then
        some ({
          id := 0
          source := source
          sourceLki := captureLki s source controller
          controller := controller
          abilityIdx := abilityIdx
          fromArsenal := fromArsenal
          effect := eff.body
          requiresOpposingHero := eff.targets == [{ kind := .opposingHero }]
          equipmentTargetPlayer := if eff.targets == [{ kind := .equipment .defendingHero }] then
            damageRecipient else none }, once)
      else none
    | _ => none

/-- Collect matching unrestricted triggers that require no modes or additional costs (CR 6.6). -/
def collectCardTriggers (s : GameState) (source : ObjId) (controller : PlayerId) (fromArsenal : Bool)
    (abilities : List Ability) (matchesEvent : Trigger → Option Condition → Bool)
    (damageRecipient : Option PlayerId := none) :
    List PendingTrigger :=
  let triggers := (matchingCardTriggers s source controller fromArsenal abilities matchesEvent
    (damageRecipient := damageRecipient)).filterMap
    fun (trigger, once) => if once then none else some trigger
  triggers.zipIdx.map fun (trigger, idx) => { trigger with id := s.nextTimestamp + idx }

/-- Collect relevant abilities on installed arena objects under the player's control (CR 1.7.4, 3.0.14b). -/
def installedCardTriggers (s : GameState) (p : PlayerId) (matchesEvent : Trigger → Bool)
    (matchesOrdinal : Option Nat → Bool := Option.isNone) :
    List (PendingTrigger × Bool) :=
  ((installedArenaZones s).flatMap s.zone).flatMap fun source =>
    if (s.characteristics source).any (fun c => c.controller == p && !c.abilitiesLost) &&
        (s.obj? source).any (fun obj => !obj.faceDown) then
      let abilities := ((s.objectFace? source).map (·.abilities)).getD []
      matchingCardTriggers s source p false abilities (matchesOrdinal := matchesOrdinal) fun event cond =>
        matchesEvent event && (cond.map (evalCondition s p source false)).getD true
    else []

/-- Find arena abilities triggered by the card just discarded (CR 3.10, 6.6.5). -/
def discardEventTriggers (s : GameState) (p : PlayerId) (discarded : ObjId) :
    List (PendingTrigger × Bool) :=
  match s.objectFace? discarded with
  | none => []
  | some face =>
    installedCardTriggers s p fun
      | .onDiscard filter duringAction =>
        (!duringAction || (s.phase == .actionPhase && s.active == some p)) &&
          cardFaceMatches filter face
      | _ => false

/-- Queue abilities in event order, consuming a once-per-turn use as soon as it triggers (CR 6.6.5e). -/
def queueCardTriggers (s : GameState) (candidates : List (PendingTrigger × Bool)) : GameState :=
  let collected := candidates.foldl (fun (used, pending) (trigger, once) =>
    let key := (trigger.source, trigger.abilityIdx)
    if once && used.contains key then (used, pending)
    else (if once then key :: used else used, trigger :: pending)) (s.triggeredThisTurn, [])
  let triggers := collected.2.reverse.zipIdx.map fun (trigger, idx) =>
    { trigger with id := s.nextTimestamp + idx }
  { s with
    triggeredThisTurn := collected.1
    pendingTriggers := if triggers.isEmpty then s.pendingTriggers else s.pendingTriggers ++ triggers
    nextTimestamp := s.nextTimestamp + triggers.length }

/-- Queue pitch triggers without interrupting the payment that caused them (CR 6.6.6). -/
def queuePitchTriggers (s : GameState) (p : PlayerId) (pitched : ObjId) : GameState :=
  let abilities := ((s.objectFace? pitched).map (·.abilities)).getD []
  let triggers := collectCardTriggers s pitched p false abilities fun trigger cond =>
    trigger == .onPitch && (cond.map (evalCondition s p pitched false)).getD true
  { s with
    pendingTriggers := s.pendingTriggers ++ triggers
    nextTimestamp := s.nextTimestamp + triggers.length }

/-- Queue supported rule-event triggers in event order (CR 6.6). -/
def queueRuleEventTriggers (s : GameState) (events : List Event) : GameState :=
  queueCardTriggers s (events.flatMap fun
    | .discarded p id => discardEventTriggers s p id
    | .damageDealt p _ amount =>
      if amount > 0 && s.result.isNone then installedCardTriggers s p (· == .onControllerDamaged)
      else []
    | .moved _ id _ (.player owner .arsenal) =>
      if (s.obj? id).any (fun card => !card.faceDown) &&
          (s.characteristics id).any (fun chars => !chars.abilitiesLost) then
        let abilities := ((s.objectFace? id).map (·.abilities)).getD []
        matchingCardTriggers s id owner false abilities fun trigger cond =>
          trigger == .onArsenalFaceUp &&
            (cond.map (evalCondition s owner id false)).getD true
      else []
    | .countersEmptied source kind =>
      match s.characteristics source with
      | some chars =>
        if chars.abilitiesLost then [] else
          let abilities := ((s.objectFace? source).map (·.abilities)).getD []
          matchingCardTriggers s source chars.controller false abilities fun trigger cond =>
            trigger == .onCountersEmptied kind &&
              (cond.map (evalCondition s chars.controller source false)).getD true
      | none => []
    | _ => [])

/-- Queue triggers for events returned by discard effects (CR 6.6). -/
abbrev queueDiscardTriggers := queueRuleEventTriggers

/-- The controller credited with an attack action card's hit (CR 7.5.3). -/
def attackActionHitController? (s : GameState) (link : ChainLink) : Option PlayerId := do
  if !link.hit || link.attackSource.isSome then none else
    let attack ← link.attack.bind s.characteristics
    if attack.types.contains .action && attack.subtypes.contains .attack then
      some attack.controller else none

/-- Count uninterrupted hits ending at the active link (CR 7.5.3). -/
def consecutiveChainHits (s : GameState) : Nat :=
  ((s.combat.map (·.links)).getD []).takeWhile (·.hit) |>.length

/-- Find installed arena abilities triggered by a successful attack (CR 7.5.3). -/
def installedHitTriggers (s : GameState) (link : ChainLink) : List (PendingTrigger × Bool) :=
  let source := link.attackSource.or link.attack
  match source.bind s.characteristics with
  | some attack =>
    let isAction := link.attackSource.isNone && attack.types.contains .action && attack.subtypes.contains .attack
    let isWeapon := link.attackSource.isSome && attack.types.contains .weapon
    let streak := consecutiveChainHits s
    let count := s.attackActionHitsThisTurn.count attack.controller
    installedCardTriggers s attack.controller (matchesOrdinal := fun ordinal => ordinal.all (· == count)) fun
      | .onConsecutiveHitLink minLink => isAction && minLink ≤ streak
      | .onWeaponAttackHit => isWeapon
      | .onAttackActionHit => isAction
      | _ => false
  | none => []

/-- Identify the live weapon that sourced the link's attack (CR 1.4.3, 7.5.3). -/
def hitWeapon? (s : GameState) (link : ChainLink) : Option ObjId := do
  let source ← link.attackSource
  if (s.characteristics source).any (·.types.contains .weapon) then some source else none

/-- Abilities granted to this exact attack card or weapon by a continuous effect. -/
def grantedAttackAbilities (s : GameState) (source : ObjId) : List Ability :=
  s.activeEffects.filterMap fun effect =>
    match effect.target, effect.op with
    | .obj id, .grantAttackAbility ability => if id == source then some ability else none
    | _, _ => none

/-- Collect hit triggers on the source weapon, including exact per-turn hit ordinals (CR 6.6.5d). -/
def weaponHitTriggers (s : GameState) (link : ChainLink) : List (PendingTrigger × Bool) :=
  match hitWeapon? s link with
  | some source =>
    if (s.obj? source).any (·.faceDown) || (s.characteristics source).any (·.abilitiesLost) then [] else
      let printed := ((s.objectFace? source).map (·.abilities)).getD []
      let abilities := printed ++ grantedAttackAbilities s source
      let count := s.weaponHitsThisTurn.count source
      matchingCardTriggers s source link.attacker false abilities
        (fun trigger cond =>
          trigger == .onHit && (cond.map (evalCondition s link.attacker source false)).getD true)
        (fun ordinal => ordinal.all (· == count))
  | none => []

/-- Collect printed and granted hit and Crush triggers (CR 6.6, 7.5.5, 8.4.2). -/
def attackDamageTriggers (s : GameState) (link : ChainLink) : List PendingTrigger :=
  match link.attack with
  | none => []
  | some source =>
    let printed := ((s.objectFace? source).map (·.abilities)).getD []
    let abilities := printed ++ link.grantedAbilities ++ grantedAttackAbilities s source
    let triggers := collectCardTriggers s source link.attacker false abilities
      (damageRecipient := some link.defender) fun trigger cond =>
        let matchesEvent := match trigger with
          | .onHit | .onHitHero => link.hit
          | .onConsecutiveHitLink minimum => link.hit && minimum ≤ consecutiveChainHits s
          | .onCrush => crushTriggered link
          | _ => false
        matchesEvent && (cond.map (evalCondition s link.attacker source false)).getD true
    triggers.map fun trigger =>
      match trigger.effect with
      | .prim (.createTokenForAttackDamage player token) =>
        { trigger with effect := .prim (.createToken player token link.damageDealt) }
      | .grant (.hero .defendingHero) mod dur =>
        { trigger with effect := .grant (.hero (.seated link.defender)) mod dur }
      | .grant (.playerActionsAndAttacks .defendingHero) mod dur =>
        { trigger with effect := .grant (.playerActionsAndAttacks (.seated link.defender)) mod dur }
      | .grant (.firstAttackNextTurn .defendingHero) mod dur =>
        { trigger with effect := .grant (.firstAttackNextTurn (.seated link.defender)) mod dur }
      | .grant (.firstActionNextTurn .defendingHero) mod dur =>
        { trigger with effect := .grant (.firstActionNextTurn (.seated link.defender)) mod dur }
      | .prim (.discardChoice .defendingHero filter count) =>
        { trigger with effect := .prim (.discardChoice (.seated link.defender) filter count) }
      | .prim (.loseLife .defendingHero amount) =>
        { trigger with effect := .prim (.loseLife (.seated link.defender) amount) }
      | _ => trigger

/-- Record a resolved damage event on the current combat link and queue its hit triggers (CR 7.5). -/
def finishCombatDamage (s : GameState) (attack : ObjId) (amount : Nat)
    (rest : List Frame) : GameState :=
  match s.combat with
  | none => { s with pending := rest }
  | some cc =>
    let tp := s.active.getD ⟨0⟩
    let next := [.priority tp 0, .combatStep .resolution attack] ++ rest
    match cc.activeLink? with
    | none => { s with combat := some { cc with step := .damage }, pending := next }
    | some link =>
      let hit := didCombatHit amount
      let damagedLink := { link with hit, damageDealt := amount }
      let cc' := { cc with step := .damage }.updateActiveLink fun _ => damagedLink
      let weaponHit := if hit then hitWeapon? s damagedLink else none
      let cardHit := attackActionHitController? s damagedLink
      let withDamage := { s with
        combat := some cc'
        weaponHitsThisTurn := weaponHit.toList ++ s.weaponHitsThisTurn
        attackActionHitsThisTurn := cardHit.toList ++ s.attackActionHitsThisTurn }
      let damageTriggers := if hit && withDamage.result.isNone then
        (attackDamageTriggers withDamage damagedLink).map (fun trigger => (trigger, false)) ++
          installedHitTriggers withDamage damagedLink ++ weaponHitTriggers withDamage damagedLink ++
          installedCardTriggers withDamage damagedLink.defender (· == .onControllerDamaged)
        else []
      let queued := queueCardTriggers withDamage damageTriggers
      let settled := gspRun queued
      let triggers := if queued.pendingTriggers.isEmpty then [] else [.flushTriggers]
      { settled with pending := triggers ++ next }

/-- The damage kind carried by a damage-prevention continuation. -/
def preventionDamageKind (damage : ReplacementState) : DamageKind :=
  match damage.event with
  | .damage _ kind _ _ => kind
  | _ => .arcane

/-- Complete one target's prevention, committing all life changes after the last choice. -/
def finishArcaneBatch (s : GameState) (p : PlayerId) (result : ReplacementState)
    (batch : ArcaneDamageBatch) (rest : List Frame) : GameState × List Event :=
  let (prepared, preventionEvents) := settleDamagePrevention s result
  let prepared := queueRuleEventTriggers prepared preventionEvents
  let batch := { batch with settled := (p, remainingDamage result.event) :: batch.settled }
  if batch.remaining.isEmpty then
    let events := batch.settled.reverse.filterMap fun (target, amount) =>
      if amount == 0 then none else some (.damageDealt target .arcane amount)
    let damaged := checkHeroDefeat (applyArcaneBatchLosses prepared batch)
    let queued := queueRuleEventTriggers damaged events
    ({ queued with pending := if damaged.result.isSome then [] else rest }, preventionEvents ++ events)
  else
    ({ prepared with pending := nextArcaneBatchFrame prepared batch ++ rest }, preventionEvents)

/-- Finish a damage event's outcome stage, including its combat link when applicable (CR 6.4.10, 7.5). -/
def finishArcaneDamage (s : GameState) (p : PlayerId) (effects : List ReplacementEffect)
    (damage : ReplacementState) (rest : List Frame) (attack : Option ObjId := none) : GameState × List Event :=
  let result := applyReplacementStage .outcome [] effects damage
  match result.batch with
  | some batch => finishArcaneBatch s p result batch rest
  | none =>
    let (settled, events) := settleDamage s p (preventionDamageKind damage) result
    let finished := match attack with
      | some id => finishCombatDamage settled id (remainingDamage result.event) rest
      | none =>
        let queued := queueRuleEventTriggers settled events
        { settled with
          pendingTriggers := queued.pendingTriggers
          nextTimestamp := queued.nextTimestamp
          triggeredThisTurn := queued.triggeredThisTurn
          pending := if settled.result.isSome then [] else rest }
    (finished, events)

/-- Apply one prevention choice at a time so the affected player can choose its order and pitch
to pay a barrier without gaining priority during resolution (CR 1.14.3, 6.5.1, 8.3.8). -/
def advanceArcaneDamage (s : GameState) (p : PlayerId) (effects : List ReplacementEffect)
    (damage : ReplacementState) (stage : ArcaneDamageStep) (rest : List Frame)
    (attack : Option ObjId := none) :
    GameState × List Event :=
  match stage with
  | .offer =>
    let publicChoices := effects.filter fun effect =>
      let energy := max (preventionResourceCost effect) (s.poolOf p).totalEnergy
      effect.eligible .prevention { damage with availResources := energy }
    let energy := potentialResourceEnergy s p
    let available := publicChoices.filter fun e => decide (preventionResourceCost e ≤ energy)
    let prompt := Frame.chooseReplacement p .prevention (available.map (·.id)) (!available.any (·.isMandatory))
    let waiting := { s with pending := prompt :: .arcaneDamage p effects damage .readChoice attack :: rest }
    match publicChoices with
    | [] => finishArcaneDamage s p effects damage rest attack
    | [e] =>
      if e.isMandatory && preventionResourceCost e == 0 then
        ({ s with pending := .arcaneDamage p effects (applyOneReplacement damage e) .offer attack :: rest }, [])
      else (waiting, [])
    | _ => (waiting, [])
  | .readChoice =>
    match (s.chosenReplacements.getLast?.join).bind (fun id => effects.find? (·.id == id)) with
    | none => finishArcaneDamage s p effects damage rest attack
    | some choice =>
      ({ s with pending := .arcaneDamage p effects damage (.pay choice) attack :: rest }, [])
  | .pay effect =>
    let cost := { resources := preventionResourceCost effect : AssetCost }
    let resume := Frame.arcaneDamage p effects damage (.pay effect) attack
    match spendAssetCost s p cost with
    | some board =>
      let result := applyOneReplacement { damage with availResources := (s.poolOf p).totalEnergy } effect
      ({ board with pending := .arcaneDamage p effects result .offer attack :: rest }, [])
    | none =>
      if canPitchForCost s p cost then
        ({ s with pending := .choosePreventionPitch p :: resume :: rest }, [])
      else
        ({ s with pending := .arcaneDamage p (effects.eraseP (·.id == effect.id)) damage .offer attack :: rest }, [])

/-- Collect the card's own on-play triggers once its costs have been paid (CR 5.1, 6.6.5). -/
def playedCardTriggers (s : GameState) (source : ObjId) (controller : PlayerId)
    (fromArsenal : Bool) : List PendingTrigger :=
  match s.objectFace? source with
  | none => []
  | some face =>
    collectCardTriggers s source controller fromArsenal face.abilities fun trigger cond =>
      trigger == .onPlay && (cond.map (evalCondition s controller source fromArsenal)).getD true

/-- Collect an attack's own triggered abilities when it becomes attacking (CR 7.2.3). -/
def attackingCardTriggers (s : GameState) (source : ObjId) (controller : PlayerId)
    (fromArsenal : Bool) (granted : List Ability := []) : List PendingTrigger :=
  let printed := ((s.objectFace? source).map (·.abilities)).getD []
  collectCardTriggers s source controller fromArsenal (printed ++ granted) fun trigger cond =>
    trigger == .onAttack && (cond.map (evalCondition s controller source fromArsenal)).getD true

/-- Read the face used to match a pending attack and whether the attack is a proxy (CR 1.4.3a). -/
def attackLayerFace? (s : GameState) (layerId : ObjId) : Option (CardFace × Bool) :=
  match (s.obj? layerId).map Object.kind with
  | some (.attackProxy source _) => (s.objectFace? source).map fun face => (face, true)
  | some (.card _ _) => do
    let face ← s.objectFace? layerId
    if face.hasType .action && face.hasSubtype .attack then some (face, false) else none
  | _ => none

/-- Apply matching attack modifiers after successful payment. Card-cost filters read
the unmodified cost (CR 2.2.4b, 5.1.7, 5.2.2a). -/
def consumeNextAttackEffects (s : GameState) (layerId : ObjId) (info : LayerInfo) :
    LayerInfo × List ContinuousEffect :=
  match attackLayerFace? s layerId with
  | none => (info, s.activeEffects)
  | some (face, isProxy) =>
    let isWeapon := isProxy && face.hasType .weapon
    s.activeEffects.foldr (fun effect (layer, rest) =>
      let affected := match effect.target with
        | .nextAttackBy player => player
        | _ => effect.controller
      let eligible := match effect.target with
        | .nextAttackCard filter =>
          !isProxy && !filter.isWeaponAttack && cardFaceMatches filter face
        | .nextAttack filter | .allAttacks filter =>
          (!filter.isWeaponAttack || isWeapon) && cardFaceMatches filter face
        | .nextAttackBy _ => true
        | _ => false
      if affected == info.controller && eligible && !effect.waitsForNextTurn then
        match effect.op with
        | .addPower bonus =>
          let remaining := match effect.target with
            | .allAttacks _ => effect :: rest
            | _ => rest
          ({ layer with attackPowerBonus := layer.attackPowerBonus + bonus }, remaining)
        | .addPowerIfFewerDefenders limit bonus =>
          ({ layer with attackPowerForFewerDefenders := (limit, bonus) ::
              layer.attackPowerForFewerDefenders }, rest)
        | .grantKeyword keyword =>
          if keyword == .goAgain && !layerCanGainGoAgain s layerId info.controller then (layer, rest)
          else ({ layer with attackKeywords := insertUnique keyword layer.attackKeywords }, rest)
        | .grantAttackAbility ability =>
          ({ layer with attackAbilities := ability :: layer.attackAbilities }, rest)
        | .addCostRes _ | .subCostRes _ =>
          match effect.target with
          | .nextAttackCard _ | .nextAttackBy _ => (layer, rest)
          | _ => (layer, effect :: rest)
        | _ => (layer, effect :: rest)
      else (layer, effect :: rest)) (info, [])

/-- Read a single unconditional, mandatory random-discard cost (CR 5.1.8, 5.1.9). -/
def cardPlayRandomDiscardCost (s : GameState) (layerId : ObjId) : Nat :=
  match (s.cardDefOf? layerId).bind (·.front.playEffect) with
  | some { extraCosts := [{ cost := .discardRandom count, optional := false, cond := none }], .. } =>
    count
  | _ => 0

mutual
/-- Bind the attack referenced by an attack-play triggered effect. -/
def Effect.bindPlayedAttack (attack : ObjId) : Effect → Effect
  | .grant (.obj .currentAttack) mod duration => .grant (.paidAttack attack) mod duration
  | .seq effects => .seq (effects.bindPlayedAttack attack)
  | effect => effect

/-- Bind an attack reference throughout a sequence of triggered effects. -/
def EffectList.bindPlayedAttack (attack : ObjId) : EffectList → EffectList
  | .nil => .nil
  | .cons first rest => .cons (first.bindPlayedAttack attack) (rest.bindPlayedAttack attack)
end

/-- Collect an active permanent's triggered abilities matching the given event (CR 6.6). -/
def permanentTriggers (s : GameState) (source : ObjId) (p : PlayerId) (fromArsenal : Bool)
    (event : Trigger) : List PendingTrigger :=
  if (s.characteristics source).any (fun c => c.controller == p && !c.abilitiesLost) &&
      (s.obj? source).any (fun obj => !obj.faceDown) then
    let abilities := ((s.objectFace? source).map (·.abilities)).getD []
    collectCardTriggers s source p fromArsenal abilities fun trigger cond =>
      trigger == event && (cond.map (evalCondition s p source fromArsenal)).getD true
  else []

/-- Collect triggered abilities of face-up permanents controlled by the player (CR 6.6). -/
def controlledPermanentTriggers (s : GameState) (p : PlayerId) (event : Trigger) :
    List PendingTrigger :=
  let permanents := (allPlayers s.playerCount).flatMap fun owner => s.zone (.player owner .permanent)
  permanents.flatMap fun source => permanentTriggers s source p false event

/-- Collect arena triggers caused by paying for a card or weapon attack (CR 5.1.10, 6.6.5). -/
def arenaAttackPlayTriggers (s : GameState) (layerId : ObjId) (p : PlayerId) :
    List PendingTrigger :=
  if (attackLayerFace? s layerId).isNone then [] else
    (controlledPermanentTriggers s p .onPlayAttackOrWeapon).map fun trigger =>
      { trigger with effect := trigger.effect.bindPlayedAttack layerId }

/-- Collect card-play triggers from installed objects after a successful card payment. -/
def installedCardPlayTriggers (s : GameState) (layerId : ObjId) (p : PlayerId) : List (PendingTrigger × Bool) :=
  match s.objectFace? layerId with
  | none => []
  | some face =>
    installedCardTriggers s p fun
      | .onPlayCard filter => cardFaceMatches filter face
      | _ => false

/-- Collect an entering permanent's abilities using the new object in the arena (CR 3.0.5, 6.6.5). -/
def permanentEntryTriggers (s : GameState) (fromArsenal : Bool) (events : List Event) :
    List PendingTrigger :=
  events.flatMap fun
    | .moved _ source .stack (.player controller .permanent) =>
      permanentTriggers s source controller fromArsenal .onEnterArena
    | _ => []

/-- Put pending triggers ahead of the next priority window after a layer resolves (CR 6.6.6). -/
def afterPermanentEntry (s : GameState) (triggers : List PendingTrigger) (rest : List Frame) : GameState :=
  let queued := triggers.zipIdx.map fun (trigger, index) => { trigger with id := s.nextTimestamp + index }
  let flush := if (s.pendingTriggers ++ queued).isEmpty then [] else [.flushTriggers]
  { s with
    pendingTriggers := s.pendingTriggers ++ queued
    nextTimestamp := s.nextTimestamp + queued.length
    pending := flush ++ (afterLayerResolution s :: rest) }

/-- Read the supported single, required hand-card cost (CR 5.1.9). -/
def cardPlayHandCost? (s : GameState) (layerId : ObjId) : Option HandCardCost :=
  match (s.cardDefOf? layerId).bind (·.front.playEffect) with
  | some { extraCosts := [{ cost := .putHandCardOnDeckBottom, optional := false, cond := none }], .. } =>
    some .bottomDeck
  | some { extraCosts := [{ cost := .revealHandCard f, optional := false, cond := none }], .. } =>
    some (.reveal f)
  | _ => none

/-- Read the public identity of a card that meets a reveal cost. -/
def revealCostCard? (s : GameState) (id : ObjId) (filter : CardFilter) : Option CardId := do
  let face ← s.objectFace? id
  if cardFaceMatches filter face then (s.cardDefOf? id).map (·.id) else none

/-- A cost card must be in the payer's current hand (CR 5.1.9). -/
def canPickHandCostCard (s : GameState) (p : PlayerId) (cost : HandCardCost) (id : ObjId) : Bool :=
  (s.zone (.player p .hand)).contains id &&
    match cost with
    | .bottomDeck => true
    | .reveal filter => (revealCostCard? s id filter).isSome

/-- Find the source and index of a limited weapon attack when its payment completes (CR 5.2.2). -/
def paidWeaponActivation? (s : GameState) (layerId : ObjId) : Option (ObjId × Nat) := do
  let layer ← s.obj? layerId
  match layer.kind with
  | .attackProxy source _ =>
    let card ← s.cardDefOf? source
    let index ← limitedWeaponAttackIndex? card
    return (source, index)
  | _ => none

/-- Create the on-play trigger after the variable additional cost has been paid (CR 5.1.10, 6.6.5). -/
def variablePaymentTrigger (s : GameState) (p : PlayerId) (source : ObjId) (fromArsenal : Bool) :
    Option PendingTrigger := do
  let info ← s.layerMeta.get? source.n
  let amount ← info.variableResources
  let defn ← (s.objectFace? source).bind (·.playEffect)
  let (filter, body) ← defn.onPayX
  if amount ≤ (graveyardTargetChoices s p filter).length then
    some
      { id := 0
        source := source
        sourceLki := captureLki s source p
        controller := p
        fromArsenal := fromArsenal
        effect := body.bindPlayedAttack source
        graveyardTargets := some (amount, filter) }
  else none

/-- Read the announced card's chosen resolution effect and any immediate on-play ability. -/
def cardAnnouncedArcaneDamage (card : CardDef) (modeIdx : Option Nat) : Bool :=
  let body := card.front.playEffect.bind fun effect =>
    match modeIdx with
    | none => some effect.body
    | some index => (effect.modes[index]?).map (·.body)
  body.any (·.hasArcaneDamage) || card.front.abilities.any fun
    | .triggered .onPlay _ _ _ effect => effect.body.hasArcaneDamage
    | _ => false

/-- Bind active arcane damage bonuses to a paid card, retaining them through resolution. -/
def bindNextArcaneCard (effects : List ContinuousEffect) (p : PlayerId)
    (source : ObjId) : List ContinuousEffect :=
  effects.map fun effect =>
    match effect.target, effect.op with
    | .player player, .addToNextArcaneCard amount =>
      if effect.controller == p && player == p && !effect.waitsForNextTurn then
        { effect with target := .obj source, op := .addArcaneDamageFromSource amount }
      else effect
    | _, _ => effect

/-- Finalize a paid layer, then stack triggers queued during play and return priority (CR 5.1.10, 6.6.6). -/
def finishPaidPlay (s : GameState) (p : PlayerId) (layerId : ObjId) (fromArsenal : Bool)
    (modeIdx : Option Nat) (rest : List Frame) (discarded : Option CardFace := none)
    (boostPaid : Option Bool := none) : GameState :=
  let card := s.cardDefOf? layerId
  let isAttack := card.any (fun c => c.front.hasSubtype .attack)
  let hasBoostGoAgain := boostPaid.getD false && layerCanGainGoAgain s layerId p
  let hasGoAgain := (card.any (fun c => c.front.keywords.contains .goAgain) || hasBoostGoAgain) &&
    !isAttack && s.active == some p && layerCanGainGoAgain s layerId p
  let modeOnAttack : Option Effect := do
    let effect ← card.bind (·.front.playEffect)
    let index ← modeIdx
    let mode ← effect.modes[index]?
    mode.onAttack
  let info : LayerInfo :=
    { controller := p
      fromArsenal := fromArsenal
      modeIdx := modeIdx
      heroTarget := (s.layerMeta.get? layerId.n).bind (·.heroTarget)
      secondHeroTarget := (s.layerMeta.get? layerId.n).bind (·.secondHeroTarget)
      attackTarget := (s.layerMeta.get? layerId.n).bind (·.attackTarget)
      weaponTarget := (s.layerMeta.get? layerId.n).bind (·.weaponTarget)
      variableResources := (s.layerMeta.get? layerId.n).bind (·.variableResources)
      additionalCostPaid := boostPaid.isSome || (s.layerMeta.get? layerId.n).any
        (fun info => info.payAdditionalResources || info.additionalCostPaid || info.variableResources.isSome)
      discardedForPlay := discarded
      attackKeywords := if isAttack && hasBoostGoAgain then [.goAgain] else []
      attackAbilities :=
        (modeOnAttack.map fun body => Ability.triggered .onAttack false none none { body := body }).toList
      goAgain := hasGoAgain }
  let (updatedInfo, remainingEffects) := consumeNextAttackEffects s layerId info
  let dealsArcane := card.any (cardAnnouncedArcaneDamage · modeIdx)
  let remainingEffects := if dealsArcane then bindNextArcaneCard remainingEffects p layerId
    else remainingEffects
  let remainingEffects := remainingEffects.filterMap fun effect =>
    if card.any (fun c => effect.appliesNextInstant p c.front) then
      match effect.op with
      | .nextCardAsInstant _ (bonus + 1) =>
        if dealsArcane then
          some { effect with target := .obj layerId, op := .addArcaneDamageFromSource (bonus + 1) }
        else none
      | _ => none
    else some effect
  let isAction := card.any (fun c => c.front.hasType .action) ||
    (s.obj? layerId).any (fun obj => match obj.kind with | .attackProxy _ _ => true | _ => false)
  let remainingEffects := if isAction then effectsAfterPayingAction remainingEffects p
    else remainingEffects
  let activation := paidWeaponActivation? s layerId
  let effects := match activation with
    | some (weapon, index) =>
      if s.activatedThisTurn.contains (weapon, index) then
        remainingEffects.eraseP (fun effect => effect.allowsWeaponAttack p weapon)
      else remainingEffects
    | none => remainingEffects
  let s := { s with layerMeta := s.layerMeta.insert layerId.n updatedInfo }
  let newTriggers := playedCardTriggers s layerId p fromArsenal ++
    (variablePaymentTrigger s p layerId fromArsenal).toList ++ arenaAttackPlayTriggers s layerId p
  let queued := queueCardTriggers s
    (newTriggers.map (·, false) ++ installedCardPlayTriggers s layerId p)
  let flush := if queued.pendingTriggers.isEmpty then [] else [.flushTriggers]
  let nonAttack := card.any (fun c => c.front.hasType .action && !c.front.hasSubtype .attack)
  { s with
    activeEffects := effects
    pendingTriggers := queued.pendingTriggers
    nextTimestamp := queued.nextTimestamp
    triggeredThisTurn := queued.triggeredThisTurn
    playRollback := none
    activatedThisTurn := s.activatedThisTurn ++ activation.toList
    nonAttackActionsThisTurn := if nonAttack then p :: s.nonAttackActionsThisTurn else s.nonAttackActionsThisTurn
    pending := flush ++ (.priority p 0 :: rest) }

/-- Pay the declared boost cost before returning priority and grant its keyword to the paid layer
(CR 5.1.9, 8.3.9). -/
def finishBoostedPlay (s : GameState) (p : PlayerId) (layerId : ObjId) (fromArsenal : Bool)
    (modeIdx : Option Nat) (rest : List Frame) : GameState × List Event :=
  let (boosted, goAgain, events) := applyBoost s p false
  let paid := if events.isEmpty then none else some goAgain
  let delayed := boosted.delayedTriggers.filterMap fun trigger =>
    if paid.isSome && trigger.controller == p && trigger.watch == .boostThisTurn boosted.turn then
      let pending : PendingTrigger :=
        { id := trigger.id
          source := trigger.source
          sourceLki := trigger.sourceLki.getD (captureLki boosted trigger.source p)
          controller := p
          effect := trigger.effect }
      some (pending, false)
    else none
  let installed := if paid.isSome then installedCardTriggers boosted p (· == .onBoost) else []
  let queued := queueCardTriggers boosted (delayed ++ installed)
  (finishPaidPlay queued p layerId fromArsenal modeIdx rest none paid, events)

/-- The declarations and payment for a supported activated ability (CR 5.2.2). -/
structure ActivationPlan where
  /-- Source and additional costs fixed at declaration. -/
  payment : ActivationPayment
  /-- Assets the controller must pay before activating. -/
  cost : AssetCost
  /-- Whether its layer grants Go Again on resolution. -/
  goAgain : Bool
  /-- Resolution effect stored on the activated layer. -/
  body : Effect
  /-- Required target and its resolution-time eligibility filter. -/
  target : Option (TargetSpec × ObjId)
  /-- Declared graveyard targets and their independent eligibility filters. -/
  graveyardTargets : List (TargetSpec × ObjId)

/-- Public zones that can contain an attack action card targeted by an activation (CR 1.8.5a). -/
def activationTargetZones (s : GameState) : List Zone :=
  .stack :: activationArenaZones s

/-- Check an attack target. Weapon attacks target the active link's attack object (CR 1.8.5, 7.4). -/
def matchesActivationTarget (s : GameState) (spec : TargetSpec) (id : ObjId) : Bool :=
  if spec.kind == .weaponAttack then
    (s.combat.bind CombatChain.activeLink?).any fun link => matchingActiveAttack s link spec == some id
  else
    spec.kind == .attackAction &&
      ((activationTargetZones s).flatMap s.zone).contains id &&
      (s.obj? id).any (fun obj => !obj.faceDown && match obj.kind with
        | .card _ _ => true
        | _ => false) &&
      match s.objectFace? id, s.characteristics id with
      | some face, some chars =>
        chars.types.contains .action && chars.subtypes.contains .attack &&
          cardFaceMatches spec.filter { face with
            types := chars.types, subtypes := chars.subtypes, keywords := chars.keywords,
            cost := chars.baseCost }
      | _, _ => false

/-- Check a declared graveyard target against its public location and card filter (CR 1.8). -/
def matchesActivationGraveyardTarget (s : GameState) (p : PlayerId) (spec : TargetSpec)
    (id : ObjId) : Bool :=
  (s.zone (.player p .graveyard)).contains id &&
    (s.obj? id).any (fun obj => match obj.kind with | .card _ _ => true | _ => false) &&
    (s.objectFace? id).any (cardFaceMatches spec.filter)

/-- Two independently targeted cards that the controller orders on top of their deck. -/
def activationGraveyardTargetSpecs? (effect : EffectDef) : Option (TargetSpec × TargetSpec) :=
  match effect.targets with
  | [first, second] =>
    let supported (spec : TargetSpec) :=
      spec.kind == .cardInZone .controller .graveyard && spec.minCount == 1 && spec.maxCount == some 1
    let move (slot : Nat) := Effect.prim (.moveCard (.slot slot) .deck .top false)
    if supported first && supported second && effect.body == .seqL [move 0, move 1] then
      some (first, second)
    else none
  | _ => none

/-- Recheck each target independently and let its controller choose how to order valid cards. -/
def activationGraveyardResolution (s : GameState) (p : PlayerId)
    (targets : List (TargetSpec × ObjId)) : Effect :=
  let move (id : ObjId) := Effect.prim (.moveCard (.declared id) .deck .top false)
  match (targets.filter (fun (spec, id) => matchesActivationGraveyardTarget s p spec id)).map Prod.snd with
  | [first, second] =>
    .chooseOne (.ofList [.seqL [move second, move first], .seqL [move first, move second]])
  | [only] => move only
  | _ => .nop

/-- Bind the declared target of an attack modifier (CR 5.1.4a, 5.2.2b, 6.2.2a). -/
def activationResolution? (s : GameState) (effect : EffectDef) (target : Option ObjId) :
    Option (Effect × Option (TargetSpec × ObjId)) :=
  match effect.targets, target, effect.body with
  | [], none, body => some (body, none)
  | [spec], some id, .grant (.obj (.slot 0)) mod duration =>
    let supported := match mod with
      | .addPower _ | .grantKeyword _ => duration == .thisTurn || duration == .thisChainLink
      | .grantTrigger .onHit _ _ => spec.kind == .attackAction && duration == .thisCombatChain
      | _ => false
    if supported && spec.minCount == 1 && spec.maxCount == some 1 && matchesActivationTarget s spec id then
      some (.grant (.paidAttack id) mod duration, some (spec, id))
    else none
  | _, _, _ => none

/-- Check supported activation requirements using public turn information (CR 5.2.2). -/
def activationConditionMet (s : GameState) (p : PlayerId) : Option Condition → Bool
  | none => true
  | some .weaponHitThisTurn => hasWeaponHitThisTurn s p
  | some (.boostedThisTurn n) => decide (n ≤ s.boostsThisTurn.count p)
  | some _ => false

/-- A player can pay a face-up cost with a face-down card in their arsenal (CR 3.3, 5.2.2b). -/
def canTurnArsenalCardFaceUp (s : GameState) (p : PlayerId) (card : ObjId) : Bool :=
  (s.zone (.player p .arsenal)).contains card &&
    (s.obj? card).any (·.faceDown) && (s.cardDefOf? card).isSome

/-- Read an activation surcharge determined by the arena when the cost is locked in. -/
def activationPermanentSurcharge (s : GameState) (p : PlayerId) : List ExtraCostSpec → Option Nat
  | [{ cost := .resourcePerControlledPermanent card, optional := false, cond := none }] =>
    some (controlledPermanentCount s p card)
  | _ => none

/-- Read the announced ability and its payable costs from a visible arena source (CR 5.2.2). -/
def activationPlan? (s : GameState) (p : PlayerId) (source : ObjId) (index : Nat)
    (target : Option ObjId) (secondTarget : Option ObjId := none) : Option ActivationPlan := do
  let origin ← (activationArenaZones s).find? (fun z => (s.zone z).contains source)
  let obj ← s.obj? source
  if obj.owner.n ≥ s.playerCount || obj.faceDown then none else
  let terms ← (do
    let chars ← s.characteristics source
    let face ← s.objectFace? source
    let .activated speed once cost extra condition goAgain effect ← face.abilities[index]? | none
    let timely := match speed with
      | .action =>
        s.phase == .actionPhase && s.active == some p && s.combat.isNone &&
          (s.zone .stack).isEmpty && s.canTakeAction p
      | .instant => true
      | .attackReaction =>
        s.combat.any fun cc => cc.step == .reaction && cc.activeLink?.any (fun link => link.attacker == p)
      | _ => false
    let destroy := extra == [{ cost := .destroySelf }]
    let removeCounters := match extra with
      | [{ cost := .removeCounters kind n, optional := false, cond := none }] => some (kind, n)
      | _ => none
    let turnArsenalFaceUp := extra == [{ cost := .turnArsenalFaceUp }]
    let arsenalCard := if turnArsenalFaceUp then target.filter (canTurnArsenalCardFaceUp s p) else none
    let canRemove := removeCounters.any fun (kind, n) => decide (n ≤ obj.counterCount kind)
    let surcharge := activationPermanentSurcharge s p extra
    if !timely || chars.abilitiesLost || chars.controller != p || !activationConditionMet s p condition ||
        (once && s.activatedThisTurn.contains (source, index)) ||
        !(extra.isEmpty || destroy || canRemove || arsenalCard.isSome || surcharge.isSome) ||
        !(effect.modes.isEmpty && effect.extraCosts.isEmpty) ||
        effect.body == .prim .weaponAttack then none else
    let (body, declared, graveyard) ← match activationGraveyardTargetSpecs? effect with
      | some (first, second) => do
        let a ← target
        let b ← secondTarget
        if !turnArsenalFaceUp && a != b && matchesActivationGraveyardTarget s p first a &&
            matchesActivationGraveyardTarget s p second b then
          some (.nop, none, [(first, a), (second, b)])
        else none
      | none => do
        if secondTarget.isSome then none else
        let (body, declared) ← activationResolution? s effect (if turnArsenalFaceUp then none else target)
        some (body, declared, [])
    let cost := { cost with resources := cost.resources + surcharge.getD 0 }
    some (speed, once, cost, destroy, removeCounters, arsenalCard, goAgain, body, declared, graveyard))
  let (speed, once, cost, destroy, removeCounters, arsenalCard, goAgain, body, declared, graveyard) := terms
  let isAction := speed == .action
  let cost := if isAction then
      { cost with actionPoints := max cost.actionPoints 1, resources := cost.resources + nextActionSurcharge s p }
    else cost
  let pool := s.poolOf p
  if cost.actionPoints ≤ pool.actionPoints && (pool.canPay cost || canPitchForCost s p cost) then
    let payment : ActivationPayment :=
      { source, index, origin, owner := obj.owner, destroySource := destroy, oncePerTurn := once,
        removeCounters, isAction, turnArsenalFaceUp := arsenalCard.map (p, ·) }
    some ⟨payment, cost, goAgain, body, declared, graveyard⟩
  else none

/-- The indexed abilities currently available to a player holding priority. -/
def availableActivations (s : GameState) (p : PlayerId) : List (ObjId × Nat × Option ObjId × Option ObjId) :=
  let sources := (activationArenaZones s).flatMap s.zone
  let candidates := sources.flatMap fun source =>
    let abilities := ((s.objectFace? source).map (·.abilities)).getD []
    abilities.zipIdx.flatMap fun (ability, index) =>
      match ability with
      | .activated _ _ _ extra _ _ effect =>
        if extra == [{ cost := .turnArsenalFaceUp }] then
          (s.zone (.player p .arsenal)).map (fun id => (source, index, some id, none))
        else if effect.targets.isEmpty then [(source, index, none, none)]
        else match activationGraveyardTargetSpecs? effect with
          | some (first, second) =>
            let cards := s.zone (.player p .graveyard)
            let firstChoices := cards.filter (matchesActivationGraveyardTarget s p first)
            let secondChoices := cards.filter (matchesActivationGraveyardTarget s p second)
            firstChoices.flatMap fun a => secondChoices.map fun b => (source, index, some a, some b)
          | none => ((activationTargetZones s).flatMap s.zone).map fun id => (source, index, some id, none)
      | _ => []
  candidates.filter fun (source, index, target, secondTarget) =>
    (activationPlan? s p source index target secondTarget).isSome

/-- Pay the cost taken from an activation's source before returning priority (CR 5.2.2b). -/
def payActivationSource (s : GameState) (payment : ActivationPayment) :
    Option (GameState × List Event) := do
  match payment.turnArsenalFaceUp with
  | some (p, id) =>
    if canTurnArsenalCardFaceUp s p id then
      let card ← s.cardDefOf? id
      let paid := updateSingleObject s id (fun obj => { obj with faceDown := false })
      some (paid, [.revealed p id card.id])
    else none
  | none =>
    if !payment.destroySource then
      match payment.removeCounters with
      | none => some (s, [])
      | some (kind, n) =>
        if (s.obj? payment.source).any (fun o => decide (n ≤ o.counterCount kind)) then
          let events := counterRemovalEvents s payment.source kind n
          let paid := updateSingleObject s payment.source (fun o => o.removeCounterVal kind n)
          some (queueRuleEventTriggers paid events, events)
        else none
    else
      let graveyard := Zone.player payment.owner .graveyard
      let (paid, spent) ← moveRuleObj s payment.source graveyard .top false
      some (paid, ruleMoveEvents s payment.source spent payment.origin graveyard)

/-- Finish an activation after paying its assets and effect-costs (CR 5.2.2b). -/
def finishPaidActivation (s : GameState) (p : PlayerId) (layerId : ObjId)
    (payment : ActivationPayment) (rest : List Frame) : Option (GameState × List Event) := do
  let (paid, events) ← payActivationSource s payment
  let info := paid.layerMeta.getD layerId.n { controller := p }
  let uses := if payment.oncePerTurn then (payment.source, payment.index) :: paid.activatedThisTurn
    else paid.activatedThisTurn
  let flush := if paid.pendingTriggers.isEmpty then [] else [.flushTriggers]
  let isWeaponAttack := (paid.obj? layerId).any fun layer =>
    match layer.kind with
    | .attackProxy _ _ => true
    | _ => false
  let finished := if isWeaponAttack then
      finishPaidPlay paid p layerId false none rest
    else { paid with
      activatedThisTurn := uses
      activeEffects := if payment.isAction then effectsAfterPayingAction paid.activeEffects p
        else paid.activeEffects
      layerMeta := paid.layerMeta.insert layerId.n { info with activationPayment := none }
      playRollback := none
      pending := flush ++ (.priority p 0 :: rest) }
  return (finished, events)

/-- Announce an activation and enter the normal asset payment procedure (CR 5.2.2). -/
def startActivation (s : GameState) (p : PlayerId) (source : ObjId) (index : Nat)
    (target : Option ObjId) (rest : List Frame) (secondTarget : Option ObjId := none) :
    Option (GameState × List Event) := do
  let plan ← activationPlan? s p source index target secondTarget
  let layer : Object :=
    { kind := .layer source (some (captureLki s source p)) index false
      owner := p, controller := p, timestamp := ⟨s.nextTimestamp⟩ }
  let (stacked, layerId) ← addObject s .stack layer .top
  let info : LayerInfo := {
    controller := p, goAgain := plan.goAgain && layerCanGainGoAgain stacked layerId p,
    triggerEffect := some plan.body,
    activationTarget := plan.target, activationGraveyardTargets := plan.graveyardTargets,
    activationPayment := some plan.payment }
  some ({ stacked with
    layerMeta := stacked.layerMeta.insert layerId.n info
    playRollback := some s.snapshot
    pending := .playPayCost p layerId false none plan.cost :: rest },
    plan.target.toList.map (fun declared => .targetedAttack layerId declared.2))

/-- The scope of a deck-search play permission (CR 5.1.1a). -/
def searchPlayOp (s : GameState) (asInstant : Bool) (discount : Nat) : Duration → Option EffectOp
  | .thisTurn =>
    some (if asInstant then .allowBanishedPlayAsInstant discount else .allowBanishedPlay none)
  | .thisChainLink =>
    ((s.combat.bind CombatChain.activeLink?).bind (·.attack)).map
      (fun attack => EffectOp.allowBanishedPlay (some attack))
  | _ => none

/-- Apply a selection's entry counter before its arena movement is observed by rule events. -/
def applySelectionEntryCounter (s : GameState) (events : List Event)
    (selection : Option DeckSearchChoice) : GameState :=
  match selection.bind (·.entryCounter) with
  | none => s
  | some kind =>
    let entered := events.findSome? fun
      | .moved _ id _ dst => if dst.isArena then some id else none
      | _ => none
    match entered with
    | none => s
    | some id => updateSingleObject s id (fun obj => obj.addCounterVal kind 1)

/-- Resolve a confirmed search or shuffle selection, then schedule shuffle and draw (CR 8.5.19, 8.5.20b). -/
def confirmShuffleCards (s : GameState) (p : PlayerId) (selected : List ObjId)
    (drawSame : Bool) (search : Option DeckSearchChoice) (rest : List Frame) : GameState × List Event :=
  let deck := Zone.player p .deck
  let destination := (search.map (·.destination)).getD deck
  let position := if search.isSome then Pos.top else Pos.bottom
  let revealed := if search.any (·.reveal) then selected.reverse.filterMap (fun id =>
    (s.cardDefOf? id).map (fun card => Event.revealed p id card.id)) else []
  let putOnTop := search.any (·.putOnTopAfterShuffle)
  let movers := if search.any (·.keepsSelectedInZone) then [] else selected.reverse
  let moved := moveManyObjs s movers destination position false
  let placeAfterShuffle := if putOnTop then selected.head?.toList.map (fun id =>
      Frame.run p id false [] [.prim (.putChosenDeckCardOnTop (.seated p) id)])
    else []
  let events := moved.2
  let entered := applySelectionEntryCounter moved.1 events search
  let draw := if drawSame && !events.isEmpty then [.draw p events.length] else []
  let shuffle := if search.all (·.shuffleAfter) then [.chanceShuffle deck] else []
  let bottomSelection := match search.bind (·.bottomSelection) with
    | some (.lookedAt viewed) =>
      let remaining := viewed.filter (moved.1.zone deck).contains
      if remaining.isEmpty then [] else
        let choice : DeckSearchChoice :=
          { destination := deck, reveal := false, mayFail := false, shuffleAfter := false,
            searchesDeck := false, bottomSelection := some (.order remaining.length) }
        [.chooseShuffleCards p remaining.length remaining [] false (some choice)]
    | some (.order _) =>
      [.run p ⟨0⟩ false [] [.prim (.putChosenDeckCardsOnBottom (.seated p) selected.reverse)]]
    | none => []
  let banished := events.filterMap fun
    | .moved _ id _ (.player owner .banished) => if owner == p then some id else none
    | _ => none
  let permissions : List ContinuousEffect := ((search.bind (·.playableDuration)).bind fun duration =>
    (searchPlayOp s (search.any (·.playAsInstant)) ((search.map (·.resourceDiscount)).getD 0) duration).map fun op =>
      banished.zipIdx.map fun (id, index) =>
        let timestamp := moved.1.nextTimestamp + index
        { id := timestamp
          source := id
          controller := p
          target := .obj id
          op := op
          duration := duration
          timestamp := ⟨timestamp⟩ }).getD []
  let bonuses : List ContinuousEffect := match search.bind (·.arsenalPowerBonus) with
    | none => []
    | some (source, amount) =>
      let loaded := events.filterMap fun
        | .moved _ id _ (.player owner .arsenal) => if owner == p then some id else none
        | _ => none
      loaded.zipIdx.map fun (id, index) =>
        let timestamp := entered.nextTimestamp + permissions.length + index
        { id := timestamp, source, controller := p, target := .arsenalCard id
          op := .addPower amount, timestamp := ⟨timestamp⟩ }
  let finished := { entered with
    pending := shuffle ++ placeAfterShuffle ++ bottomSelection ++ draw ++ rest
    activeEffects := entered.activeEffects ++ permissions ++ bonuses
    nextTimestamp := entered.nextTimestamp + permissions.length + bonuses.length }
  let recorded := revealed ++ events ++ banished.map (fun id => .banished p id false)
  (queueRuleEventTriggers finished recorded, recorded)

/-- Add a triggered layer with its declared targets, then continue trigger ordering (CR 6.6.6). -/
def stackPendingTrigger (s : GameState) (p : PlayerId) (trig : PendingTrigger)
    (hero : Option PlayerId) (equipment : Option ObjId) (graveyard : List ObjId)
    (rem : List PlayerId) (rest : List Frame) : Option (GameState × List Event) := do
  let layerObj : Object :=
    { kind := .layer trig.source (some trig.sourceLki) trig.abilityIdx true
      owner := p
      controller := p
      timestamp := ⟨s.nextTimestamp⟩ }
  let (s1, lid) ← addObject s .stack layerObj .top
  let remTrigs := s1.pendingTriggers.filter (fun t => t.id != trig.id)
  let info : LayerInfo :=
    { controller := p
      fromArsenal := trig.fromArsenal
      triggerEffect := some (trig.declaredEffect hero equipment)
      triggerOpposingHero := if trig.requiresOpposingHero then hero else none
      triggerEquipment := trig.equipmentTargetPlayer.bind fun player => equipment.map (player, ·)
      triggerGraveyard := trig.graveyardTargets.map fun (_, filter) => (filter, graveyard) }
  let s2 := { s1 with pendingTriggers := remTrigs, layerMeta := s1.layerMeta.insert lid.n info }
  let events := (hero.map (.targetedHero lid)).toList ++ (equipment.map (.targetedEquipment lid)).toList ++
    graveyard.map (.targetedGraveyardCard lid)
  some ({ s2 with pending := nextTriggerFrame s2 (p :: rem) ++ rest }, events)

/-- Recheck each declared graveyard target and shuffle only if some remain (CR 1.8.9, 5.3.4b). -/
def withGraveyardTargetShuffle (s : GameState) (info : LayerInfo) (effect : Effect) : Effect :=
  match info.triggerGraveyard with
  | none => effect
  | some (filter, targets) =>
    let eligible := graveyardTargetChoices s info.controller filter
    let remaining := targets.filter eligible.contains
    if remaining.isEmpty then effect
    else .seqL (remaining.map (fun id => .prim (.moveCard (.declared id) .deck .bottom false)) ++
      [.prim (.shuffleZone .controller .deck), effect])

/-- Apply a decision answer to the top frame of `s.pending` (CR 1.11, 4.1-4.4, 5.1). -/
def applyFrame (s : GameState) (a : Action) : Option (GameState × List Event) :=
  match s.pending, a.actor, a.kind with
  | .chanceFirstPlayer :: rest, .chance, .chanceFirstChooser chooser =>
    some ({ s with pending := .chooseFirstPlayer chooser :: rest }, [])
  | .chooseFirstPlayer chooser :: rest, .player p, .pickFirstPlayer first =>
    if p = chooser then
      let order := clockwiseFrom s.playerCount first
      let loadouts := order.map Frame.chooseLoadout
      let shuffles := order.map fun q => Frame.chanceShuffle (.player q .deck)
      some ({ s with
                turnOrder := order
                active := some first
                pending := loadouts ++ [.revealLoadouts] ++ shuffles ++
                  [.openingDraws, .beginTurn] ++ rest },
            [])
    else
      none
  | .chooseLoadout p :: rest, .player q, .loadoutEquip id =>
    if p = q then
      match loadoutEquipDest? s p id with
      | none => none
      | some dst =>
        match moveObj s id dst .top true with
        | none => none
        | some (s1, id') =>
          let events := if dst == .player p .permanent then []
            else [Event.moved id id' (.player p .inventory) dst]
          some ({ s1 with pending := .chooseLoadout p :: rest },
                events)
    else
      none
  | .chooseLoadout p :: rest, .player q, .loadoutToDeck id =>
    if p = q ∧ loadoutCanAddDeck s p id = true then
      match moveObj s id (.player p .deck) .bottom false with
      | none => none
      | some (s1, id') =>
        some ({ s1 with pending := .chooseLoadout p :: rest },
              [.moved id id' (.player p .inventory) (.player p .deck)])
    else
      none
  | .chooseLoadout p :: rest, .player q, .loadoutDone =>
    if p = q ∧ loadoutCanFinish s p = true then
      some ({ s with pending := rest }, [])
    else
      none
  | .chanceShuffle z :: rest, .chance, .shuffleOrder l =>
    some ({ s.reorder z l with pending := rest }, [])
  | .priority p passCount :: rest, .player q, .pass =>
    if p = q then
      let nextPass := passCount + 1
      if nextPass < s.turnOrder.length then
        let nextP := nextInOrder s.turnOrder p
        some ({ s with pending := .priority nextP nextPass :: rest }, [])
      else if (s.zone .stack).isEmpty then
        some ({ s with pending := rest }, [])
      else
        some ({ s with pending := .resolveStack :: rest }, [])
    else
      none
  | .priority p _ :: rest, .player q, .playCard id asInstant =>
    if p = q ∧ canPlayCard s p id asInstant = true then
      let fromArsenal := id ∈ s.zone (.player p .arsenal)
      let srcZone := (s.locate id).getD (.player p .hand)
      let snap := s.snapshot
      let discount := banishedPlayDiscount s p id
      let printedCost := match s.cardDefOf? id with
        | some c => modifiedCardPlayCost s p c (banishedDiscount := discount)
        | none => {}
      let cost := if asInstant || canPlayFromBanished s p id true then
          { printedCost with actionPoints := 0 }
        else printedCost
      let modes := match s.cardDefOf? id with | some c => cardModeCount c | none => 0
      let isAtkCard := match s.cardDefOf? id with
        | some c => c.front.hasType .action && c.front.hasSubtype .attack
        | none => false
      let rest' := if isAtkCard then dropPendingClose rest else rest
      match moveObj s id .stack .top false with
      | none => none
      | some (moved, layerId) =>
        let layerMeta := if discount = 0 then moved.layerMeta else
          moved.layerMeta.insert layerId.n { controller := p, banishedResourceDiscount := discount }
        let s1 := { moved with layerMeta }
        let effects := if fromArsenal then s1.activeEffects.map (·.followArsenalCard id layerId)
          else s1.activeEffects
        let target := if 0 < modes then none else cardAttackTarget? s1 layerId none
        let nextFrame :=
          if 0 < modes then
            Frame.chooseMode p layerId fromArsenal modes cost
          else
            cardPlayTargetFrame s1 p layerId fromArsenal none cost
        some ({ s1 with
                  playRollback := some snap
                  activeEffects := effects
                  layerMeta := layerMetaWithAttackTarget s1 p layerId target
                  pending := nextFrame :: rest' },
              [.moved id layerId srcZone .stack] ++ (target.map (.targetedAttack layerId)).toList)
    else
      none
  | .priority p _ :: rest, .player q, .attackWeapon wid =>
    if p = q ∧ canAttackWithWeapon s p wid = true then
      let snap := s.snapshot
      let base := match s.cardDefOf? wid with | some c => weaponAttackCost c | none => { actionPoints := 1 }
      let cost := { base with resources := base.resources + nextActionSurcharge s p + nextAttackSurcharge s p }
      let lki := captureLki s wid p
      let proxyObj : Object :=
        { kind := .attackProxy wid (some lki)
          owner := p
          controller := p
          timestamp := ⟨s.nextTimestamp⟩ }
      match addObject s .stack proxyObj .top with
      | none => none
      | some (s1, proxyId) =>
        let payment := (s.cardDefOf? wid).bind fun card =>
          (weaponAttackCounterCost? card).bind fun (index, kind, n) => do
            let weapon ← s.obj? wid
            let origin ← s.locate wid
            some {
              source := wid, index, origin, owner := weapon.owner, destroySource := false
              oncePerTurn := false, removeCounters := some (kind, n), isAction := true }
        let layers := payment.elim s1.layerMeta fun cost =>
          s1.layerMeta.insert proxyId.n { controller := p, activationPayment := some cost }
        let rest' := dropPendingClose rest
        some ({ s1 with
                  layerMeta := layers
                  playRollback := some snap
                  pending := .playPayCost p proxyId false none cost :: rest' },
              [])
    else
      none
  | .priority p _ :: rest, .player q, .activateAbility source index target secondTarget =>
    if p = q then startActivation s p source index target rest secondTarget else none
  | .defendPick defender :: rest, .player q, .defendCard id =>
    match s.combat.bind CombatChain.activeLink? with
    | some link =>
      if defender = q ∧ canDefendWith s link defender id = true then
        let fromHand := id ∈ s.zone (.player defender .hand)
        let isAction := match s.objectFace? id with | some f => f.hasType .action | none => false
        match s.locate id, moveObj s id .combatChain .top false with
        | some srcZ, some (s1, id') =>
          let cc' := s1.combat.map fun cc => cc.updateActiveLink fun l =>
            l.addDefender id' fromHand isAction
          some ({ s1 with
                    combat := cc'
                    activeEffects := nextDefendEffects s1 defender id'
                    pending := .defendPick defender :: rest },
                [.moved id id' srcZ .combatChain])
        | _, _ => none
      else
        none
    | none => none
  | .defendPick defender :: rest, .player q, .defendDone =>
    if defender = q then
      let tp := s.active.getD ⟨0⟩
      some ({ s with pending := .gameStateProcess :: .priority tp 0 :: rest }, [])
    else
      none
  | .chooseMode p layerId fromArsenal modeCount cost :: rest, .player q, .pickMode idx =>
    if p = q ∧ idx < modeCount ∧ canPickCardMode s layerId idx = true then
      let target := cardAttackTarget? s layerId (some idx)
      some ({ s with
                layerMeta := layerMetaWithAttackTarget s p layerId target
                pending := cardPlayTargetFrame s p layerId fromArsenal (some idx) cost :: rest },
            (target.map (.targetedAttack layerId)).toList)
    else
      none
  | .chooseMode p _ _ _ _ :: rest, .player q, .cancelPlay =>
    if p = q then
      some (rollbackPlay s rest, [])
    else
      none
  | .choosePlayHero p layerId fromArsenal modeIdx cost :: rest, .player q, .pickHeroTarget hero =>
    if p = q ∧ hero ∈ cardPlayHeroChoices s p layerId modeIdx then
      let info := s.layerMeta.getD layerId.n { controller := p }
      let targets := ((s.cardDefOf? layerId).map (cardPlayTargets · modeIdx)).getD []
      let needSecond := targets.length == 2 && info.heroTarget.isNone
      let declared := if info.heroTarget.isNone then { info with heroTarget := some hero }
        else { info with secondHeroTarget := some hero }
      let next : Frame := if needSecond then .choosePlayHero p layerId fromArsenal modeIdx cost
        else cardPaymentFrame s p layerId fromArsenal modeIdx cost
      some ({ s with layerMeta := s.layerMeta.insert layerId.n declared, pending := next :: rest },
        [.targetedHero layerId hero])
    else
      none
  | .choosePlayHero p _ _ _ _ :: rest, .player q, .cancelPlay =>
    if p = q then
      some (rollbackPlay s rest, [])
    else
      none
  | .chooseArcaneDamageOrder p controller source damages :: rest, .player q, .pickHeroTarget hero =>
    if p = q ∧ hero ∈ damages.map Prod.fst then
      let remaining := damages.filter (fun damage => damage.1 == hero) ++
        damages.filter (fun damage => damage.1 != hero)
      let batch : ArcaneDamageBatch := { controller, source, remaining }
      some ({ s with pending := nextArcaneBatchFrame s batch ++ rest }, [])
    else none
  | .choosePlayWeapon p layerId fromArsenal modeIdx cost candidates :: rest, .player q, .pickWeaponTarget id =>
    if p = q ∧ id ∈ candidates then
      let info := s.layerMeta.getD layerId.n { controller := p }
      some ({ s with
        layerMeta := s.layerMeta.insert layerId.n { info with weaponTarget := some id }
        pending := cardPaymentFrame s p layerId fromArsenal modeIdx cost :: rest },
        [.targetedWeapon layerId id])
    else none
  | .choosePlayWeapon p _ _ _ _ _ :: rest, .player q, .cancelPlay =>
    if p = q then some (rollbackPlay s rest, []) else none
  | .choosePitch p layerId fromArsenal modeIdx cost :: rest, .player q, .pitchCard id =>
    if p = q ∧ canPitchCard s p id = true then
      match pitchOne s p id with
      | none => none
      | some (s1, pitched, es) =>
        some ({ queuePitchTriggers s1 p pitched with pending := .playPayCost p layerId fromArsenal modeIdx cost :: rest }, es)
    else
      none
  | .choosePitch p _ _ _ _ :: rest, .player q, .cancelPlay =>
    if p = q then
      some (rollbackPlay s rest, [])
    else
      none
  | .chooseOptionalPlayCost p layerId fromArsenal modeIdx cost extra :: rest, .player q,
      .pickMay accept =>
    if p = q then
      let info := s.layerMeta.getD layerId.n { controller := p }
      let total := match extra with
        | .resources n =>
          if !accept then cost
          else match info.banishedResourceDiscount, s.cardDefOf? layerId with
          | d + 1, some card =>
            { modifiedCardPlayCost s p card n (d + 1) with actionPoints := cost.actionPoints }
          | _, _ => { cost with resources := cost.resources + n }
        | .boost => cost
      let declared := match extra with
        | .resources _ => { info with payAdditionalResources := accept }
        | .boost => { info with boostChosen := accept }
      some ({ s with
                layerMeta := s.layerMeta.insert layerId.n declared
                pending := .playPayCost p layerId fromArsenal modeIdx total :: rest }, [])
    else
      none
  | .chooseOptionalPlayCost p _ _ _ _ _ :: rest, .player q, .cancelPlay =>
    if p = q then some (rollbackPlay s rest, []) else none
  | .chooseVariableResources p layerId fromArsenal modeIdx cost limit optional :: rest, .player q,
      .pickVariableResources amount =>
    if p = q ∧ validVariableResources limit optional amount = true then
      let info := s.layerMeta.getD layerId.n { controller := p }
      let total := match amount, s.cardDefOf? layerId with
        | some x, some card =>
          { modifiedCardPlayCost s p card (x * max 1 card.front.xCostFactor)
              info.banishedResourceDiscount with
            actionPoints := cost.actionPoints }
        | _, _ => cost
      some ({ s with
        layerMeta := s.layerMeta.insert layerId.n { info with variableResources := amount }
        pending := .playPayCost p layerId fromArsenal modeIdx total :: rest }, [])
    else none
  | .chooseVariableResources p _ _ _ _ _ _ :: rest, .player q, .cancelPlay =>
    if p = q then some (rollbackPlay s rest, []) else none
  | .chooseGraveyardCost p layerId fromArsenal modeIdx cost candidates :: rest, .player q,
      .pickGraveyardCost choice =>
    if p = q ∧ choice.all candidates.contains = true then
      let info := s.layerMeta.getD layerId.n { controller := p }
      some ({ s with
        layerMeta := s.layerMeta.insert layerId.n { info with graveyardCost := choice }
        pending := .playPayCost p layerId fromArsenal modeIdx cost :: rest }, [])
    else none
  | .chooseGraveyardCost p _ _ _ _ _ :: rest, .player q, .cancelPlay =>
    if p = q then some (rollbackPlay s rest, []) else none
  | .chooseHandCardCost p layerId fromArsenal modeIdx cost :: rest, .player q, .pickHandCostCard id =>
    if p = q ∧ canPickHandCostCard s p cost id = true then
      match cost with
      | .bottomDeck =>
        let deck := Zone.player p .deck
        match moveObj s id deck .bottom false with
        | some (moved, newId) =>
          some (finishPaidPlay moved p layerId fromArsenal modeIdx rest,
            [.moved id newId (.player p .hand) deck])
        | none => none
      | .reveal filter =>
        match revealCostCard? s id filter with
        | some card =>
          some (finishPaidPlay s p layerId fromArsenal modeIdx rest, [.revealed p id card])
        | none => none
    else none
  | .chooseHandCardCost p _ _ _ _ :: rest, .player q, .cancelPlay =>
    if p = q then some (rollbackPlay s rest, []) else none
  | .chooseMay ctrl src fromArsenal env body ifDone :: rest, .player q, .pickMay choice =>
    if ctrl = q then
      if choice then
        some ({ s with pending := .run ctrl src fromArsenal env [body, ifDone] :: rest }, [])
      else
        some ({ s with pending := rest }, [])
    else
      none
  | .chooseModal ctrl src fromArsenal env modes :: rest, .player q, .pickMode idx =>
    if ctrl = q ∧ idx < modes.length then
      let chosen := modes.getD idx .nop
      some ({ s with pending := .run ctrl src fromArsenal env [chosen] :: rest }, [])
    else
      none
  | .chanceDie6 ctrl src fromArsenal env bindVar branches cont :: rest, .chance, .die6Roll roll =>
    if 1 ≤ roll ∧ roll ≤ 6 then
      let branchBody := branches.select roll
      let env' := (bindVar, Int.ofNat roll) :: env
      some ({ s with pending := .run ctrl src fromArsenal env' [branchBody, cont] :: rest }, [])
    else
      none
  | .chooseHandToDeck p pos :: rest, .player q, .handToDeckPick id =>
    if p = q ∧ id ∈ s.zone (.player p .hand) then
      let dstPos : Pos := match pos with | .bottom => .bottom | _ => .top
      match moveObj s id (.player p .deck) dstPos false with
      | none => none
      | some (s1, id') =>
        some ({ s1 with pending := rest }, [.moved id id' (.player p .hand) (.player p .deck)])
    else
      none
  | .chooseDiscard p remaining candidates selected resume :: rest, .player q, .pickDiscardCard id =>
    if q = p ∧ 0 < remaining ∧ id ∈ candidates then
      if remaining = 1 then
        let (discarded, events) := discardManyObjs s p (id :: selected).reverse
        let continuation := resume.bind fun plan =>
          (events.findSome? fun
            | .discarded _ moved => discarded.objectFace? moved
            | _ => none).map fun face =>
              let effect := if cardFaceMatches plan.classify face then plan.ifMatches else plan.otherwise
              Frame.run plan.controller plan.source plan.fromArsenal plan.env [effect]
        some ({ queueRuleEventTriggers discarded events with pending := continuation.toList ++ rest }, events)
      else
        some ({ s with pending :=
          .chooseDiscard p (remaining - 1) (candidates.erase id) (id :: selected) resume :: rest }, [])
    else none
  | .chooseShuffleCards p remaining candidates selected drawSame search :: rest, .player q, .pickShuffleCard choice =>
    if p = q then
      match choice with
      | some id =>
        if 0 < remaining ∧ id ∈ candidates then
          let next := Frame.chooseShuffleCards p (remaining - 1)
            (candidates.filter (· != id)) (id :: selected) drawSame search
          some ({ s with pending := next :: rest }, [])
        else none
      | none =>
        if shuffleSelectionCanConfirm selected search then
          some (confirmShuffleCards s p selected drawSame search rest)
        else none
    else none
  | .chooseOpt p cardId others topCount bottomCount :: rest, .player q, .optPick putOnTop selection =>
    if q = p ∧ selection.all others.contains = true then
      let chosen := selection.getD cardId
      let todo := (cardId :: others).erase chosen
      let top := topCount + if putOnTop then 1 else 0
      let bottom := bottomCount + if putOnTop then 0 else 1
      let pending := match todo with
        | [] => rest
        | next :: remaining =>
          .chooseOpt p next remaining top bottom :: rest
      let events := if todo.isEmpty then [Event.opted p top bottom] else []
      let deckZone := Zone.player p .deck
      if deckZone.Valid s.playerCount then
        let order := optDeckOrder (s.zone deckZone) topCount chosen putOnTop
        some ({ s.reorder deckZone order with pending }, events)
      else
        some ({ s with pending }, events)
    else
      none
  | .chooseArsenal tp :: rest, .player q, .arsenalPut id =>
    if tp = q ∧ (s.zone (.player tp .arsenal)).isEmpty ∧ id ∈ s.zone (.player tp .hand) then
      match moveObj s id (.player tp .arsenal) .top true with
      | none => none
      | some (s1, id') =>
        some ({ s1 with pending := rest },
              [.moved id id' (.player tp .hand) (.player tp .arsenal)])
    else
      none
  | .chooseArsenal tp :: rest, .player q, .arsenalSkip =>
    if tp = q then
      some ({ s with pending := rest }, [])
    else
      none
  | .choosePitchOrder p :: rest, .player q, .pitchReturnPick id =>
    if p = q ∧ id ∈ s.zone (.player p .pitch) then
      match moveObj s id (.player p .deck) .bottom false with
      | none => none
      | some (s1, id') =>
        some ({ s1 with pending := .returnPitch p :: rest },
              [.moved id id' (.player p .pitch) (.player p .deck)])
    else
      none
  | .chooseTriggerStart tp :: rest, .player q, .pickTriggerStart start =>
    if tp = q ∧ start ∈ s.turnOrder then
      let order := rotateTurnOrderFrom s.turnOrder start
      some ({ s with pending := nextTriggerFrame s order ++ rest }, [])
    else
      none
  | .chooseTriggerOrder p rem :: rest, .player q, .pickTrigger tid hero equipment =>
    if p = q then
      match s.pendingTriggers.find? (fun t => t.matchesDeclaration s tid p hero equipment) with
      | none => none
      | some trig =>
        match trig.graveyardTargets with
        | some (remaining + 1, filter) =>
          let candidates := graveyardTargetChoices s p filter
          some ({ s with pending := .chooseTriggerGraveyard p rem trig (remaining + 1) candidates [] :: rest }, [])
        | _ => stackPendingTrigger s p trig hero equipment [] rem rest
    else
      none
  | .chooseTriggerGraveyard p rem trig remaining candidates selected :: rest, .player q,
      .pickTriggerGraveyardCard id =>
    if p = q ∧ id ∈ candidates then
      if 1 < remaining then
        let next := Frame.chooseTriggerGraveyard p rem trig (remaining - 1)
          (candidates.erase id) (id :: selected)
        some ({ s with pending := next :: rest }, [])
      else
        stackPendingTrigger s p trig none none (id :: selected).reverse rem rest
    else none
  | .choosePreventionPitch p :: rest, .player q, .pitchCard id =>
    if p = q ∧ canPitchCard s p id = true then
      match pitchOne s p id with
      | none => none
      | some (s1, pitched, es) =>
        some ({ queuePitchTriggers s1 p pitched with pending := rest }, es)
    else none
  | .chooseReplacement aff _ cands canDecl :: rest, .player q, .pickReplacement choice =>
    let validChoice : Bool :=
      match choice with
      | some cid => cands.contains cid
      | none => canDecl
    if aff = q ∧ validChoice = true then
      some ({ s with
                chosenReplacements := s.chosenReplacements ++ [choice]
                pending := rest }, [])
    else
      none
  | _, _, _ => none

/-- Apply any legal `Action` (concession in 1v1, tournament action, or an answer to the top
frame). -/
def applyAction (s : GameState) (a : Action) : Option (GameState × List Event) :=
  match a.actor, a.kind with
  | .player p, .concede =>
    let winners := (allPlayers s.playerCount).filter (· != p)
    some ({ s with result := some (.won winners), pending := [], playRollback := none }, [])
  | .clock, .timeExpired =>
    some (applyTimeExpired s, [])
  | .judge, .judgeLoopDraw =>
    some (applyJudgeLoopDraw s, [])
  | .player p, .offerDraw =>
    some (applyOfferDraw s p, [])
  | .player _, .acceptDraw =>
    some (applyAcceptDraw s, [])
  | .player _, .declineDraw =>
    some (applyDeclineDraw s, [])
  | _, _ => applyFrame s a

/-- Stack installed and delayed end-phase triggers before the rest of the phase (CR 4.4.2). -/
def beginEndPhase (s : GameState) (tp : PlayerId) (rest : List Frame) : GameState :=
  let phaseState := { s.expireEffects .thisActionPhase with phase := .endPhase }
  let queued := queueCardTriggers phaseState (installedCardTriggers phaseState tp (· == .onStartOfEndPhase))
  let selected := s.delayedTriggers.partition fun trigger => trigger.watch == .phase .endPhase
  let delayed := selected.1.map fun trigger =>
    { id := trigger.id
      source := trigger.source
      sourceLki := captureLki s trigger.source trigger.controller
      controller := trigger.controller
      abilityIdx := 0
      effect := trigger.effect : PendingTrigger }
  let pendingTriggers := queued.pendingTriggers ++ delayed
  let triggerFrames := if pendingTriggers.isEmpty then [] else [.flushTriggers, .resolveStack]
  { phaseState with
    nextTimestamp := queued.nextTimestamp
    triggeredThisTurn := queued.triggeredThisTurn
    delayedTriggers := selected.2
    pendingTriggers := pendingTriggers
    pending := triggerFrames ++ [.endPhaseArsenal tp] ++
      s.turnOrder.map Frame.returnPitch ++ [.endTurnCleanup tp] ++ rest }

/-- Advance a single automatic work frame on top of `s.pending` (non-recursive: design.md §6.1). -/
def microStep (s : GameState) : Option (GameState × List Event) :=
  match s.pending with
  | .revealLoadouts :: rest =>
    let s1 := revealAllLoadouts s
    some ({ s1 with pending := rest }, [])
  | .openingDraws :: rest =>
    let draws := s.turnOrder.map fun p => Frame.draw p (s.intellectOf p)
    some ({ s with pending := draws ++ rest }, [])
  | .draw _ 0 :: rest =>
    some ({ s with pending := rest }, [])
  | .draw p (n + 1) :: rest =>
    let (s1, es) := drawOne s p
    some ({ s1 with pending := .draw p n :: rest }, es)
  | .beginTurn :: rest =>
    match s.tournament.tickAtTurnStart with
    | none =>
      if s.result.isNone then
        some ({ s with
                  result := some (.draw .timeLimit)
                  pending := []
                  playRollback := none }, [])
      else
        some ({ s with pending := [] }, [])
    | some ts' =>
      let tp := turnPlayerAt s.turnOrder s.turn
      some ({ s with
                turn := s.turn + 1
                active := some tp
                phase := .startPhase
                tournament := ts'
                pending := turnFrames tp ++ [.beginTurn] ++ rest },
            [])
  | .startPhaseWork tp :: rest =>
    let starting := { s.startTurnEffects with phase := .startPhase }
    let queued := queueCardTriggers starting (installedCardTriggers starting tp (· == .onStartOfTurn))
    let triggers := if queued.pendingTriggers.isEmpty then [] else [.flushTriggers, .resolveStack]
    some ({ queued with pending := triggers ++ rest }, [])
  | .actionPhaseStart tp :: rest =>
    let s1 := { s.startActionPhaseEffects tp with phase := .actionPhase }
    let triggers := (controlledPermanentTriggers s1 tp .onStartOfActionPhase).zipIdx.map
      fun (trigger, index) => { trigger with id := s1.nextTimestamp + index }
    let s2 := s1.setPool tp ((s.poolOf tp).addActionPoints 1)
    let flush := if triggers.isEmpty then [] else [.flushTriggers]
    some ({ s2 with
              pendingTriggers := s2.pendingTriggers ++ triggers
              nextTimestamp := s2.nextTimestamp + triggers.length
              pending := flush ++ (.priority tp 0 :: rest) }, [])
  | .playPayCost p layerId fromArsenal modeIdx cost :: rest =>
    match spendAssetCost s p cost with
    | some s1 =>
      if (s.layerMeta.get? layerId.n).any (·.boostChosen) then
        some (finishBoostedPlay s1 p layerId fromArsenal modeIdx rest)
      else if let some payment := (s.layerMeta.get? layerId.n).bind (·.activationPayment) then
        match finishPaidActivation s1 p layerId payment rest with
        | some finished => some finished
        | none => some (rollbackPlay s rest, [])
      else if let some selected := (s.layerMeta.get? layerId.n).bind (·.graveyardCost) then
        let graveyard := Zone.player p .graveyard
        let banished := Zone.player p .banished
        if s1.locate selected == some graveyard then
          match moveObj s1 selected banished .top false with
          | some (moved, id) =>
            let info := moved.layerMeta.getD layerId.n { controller := p }
            let layerMeta := moved.layerMeta.insert layerId.n { info with additionalCostPaid := true }
            let paid := { moved with layerMeta := layerMeta }
            some (finishPaidPlay paid p layerId fromArsenal modeIdx rest,
              [.moved selected id graveyard banished, .banished p id false])
          | none => some (rollbackPlay s rest, [])
        else some (rollbackPlay s rest, [])
      else
      match cardPlayHandCost? s layerId with
      | some handCost =>
        if (s1.zone (.player p .hand)).any (canPickHandCostCard s1 p handCost) then
          some ({ s1 with pending := .chooseHandCardCost p layerId fromArsenal modeIdx handCost :: rest }, [])
        else
          some (rollbackPlay s rest, [])
      | none =>
        let count := cardPlayRandomDiscardCost s layerId
        if count = 0 then
          some (finishPaidPlay s1 p layerId fromArsenal modeIdx rest, [])
        else if count ≤ (s1.zone (.player p .hand)).length then
          let hand := Zone.player p .hand
          let pay := Frame.payRandomDiscard p layerId fromArsenal modeIdx count :: rest
          let next := if count < (s1.zone hand).length then .chanceShuffle hand :: pay else pay
          some ({ s1 with pending := next }, [])
        else
          some (rollbackPlay s rest, [])
    | none =>
      if canPitchForCost s p cost then
        some ({ s with pending := .choosePitch p layerId fromArsenal modeIdx cost :: rest }, [])
      else
        some (rollbackPlay s rest, [])
  | .arcaneDamage p effects proposed stage attack :: rest =>
    some (advanceArcaneDamage s p effects proposed stage rest attack)
  | .payRandomDiscard p layerId fromArsenal modeIdx count :: rest =>
    let (paid, events) := discardManyObjs s p ((s.zone (.player p .hand)).take count)
    let discarded := events.reverse.findSome? fun
      | .discarded _ id => paid.objectFace? id
      | _ => none
    some (finishPaidPlay (queueRuleEventTriggers paid events) p layerId fromArsenal modeIdx rest discarded, events)
  | .resolveStack :: rest =>
    match s.zone .stack with
    | topId :: _ =>
      if isAttackLayer s topId then
        some ({ s with pending := .combatStep .attack topId :: rest }, [])
      else
        let info := s.layerMeta.getD topId.n
          { controller := s.active.getD ⟨0⟩ }
        let eff :=
          if (isDefenseReactionLayer s topId && !canResolveDefenseReaction s info) ||
              !(info.activationTarget.all fun (spec, target) => matchesActivationTarget s spec target) ||
              !(info.triggerEquipment.all fun (player, target) => matchesTriggerEquipment s player target) ||
              !(info.triggerOpposingHero.all fun target =>
                target != info.controller && s.turnOrder.contains target) then
            .nop
          else if !info.activationGraveyardTargets.isEmpty then
            activationGraveyardResolution s info.controller info.activationGraveyardTargets
          else
            match info.triggerEffect with
            | some teff => withGraveyardTargetShuffle s info teff
            | none => cardLayerEffect s topId info
        some ({ s with
                  pending := .run info.controller (resolvingSource s topId) info.fromArsenal [] [eff] ::
                    .finishResolve topId :: rest },
              [])
    | [] =>
      let next := if phaseResolvesWithoutPriority s.phase then rest else afterLayerResolution s :: rest
      some ({ s with pending := .gameStateProcess :: next }, [])
  | .finishResolve layerId :: rest =>
    let info := s.layerMeta.getD layerId.n { controller := s.active.getD ⟨0⟩ }
    let isDefReact := isDefenseReactionLayer s layerId
    let joinsDefense := isDefReact && canResolveDefenseReaction s info
    let s1 :=
      if info.goAgain && layerCanGainGoAgain s layerId info.controller && (!isDefReact || joinsDefense) then
        s.setPool info.controller ((s.poolOf info.controller).addActionPoints 1)
      else
        s
    let (s2, es) :=
      if layerId ∈ s1.zone .stack then
        if joinsDefense then
          match moveObj s1 layerId .combatChain .top false with
          | some (sMoved, id') =>
            let cc' := sMoved.combat.map fun cc => cc.updateActiveLink fun l =>
              l.addDefender id' (!info.fromArsenal) false
            ({ sMoved with
                combat := cc'
                activeEffects := defenseReactionEffects
                  (nextDefendEffects sMoved info.controller id' (some layerId)) layerId id' },
             [.moved layerId id' .stack .combatChain])
          | none => (s1, [])
        else
          match s1.obj? layerId with
          | some o =>
            match o.kind with
            | .layer _ _ _ _ => (removeNonPhysObj s1 layerId, [])
            | _ =>
              let isPerm :=
                match s1.cardDefOf? layerId with
                | some c => c.front.hasSubtype .aura || c.front.hasSubtype .item
                | none => false
              let dst := if isPerm then Zone.player info.controller .permanent
                         else Zone.player o.owner .graveyard
              match moveRuleObj s1 layerId dst .top false with
              | some (sMoved, id') => (sMoved, ruleMoveEvents s1 layerId id' .stack dst)
              | none => (s1, [])
          | none => (s1, [])
      else
        (s1, [])
    let triggers := permanentEntryTriggers s2 info.fromArsenal es
    let s3 := gspRun { s2 with layerMeta := s2.layerMeta.erase layerId.n }
    some (afterPermanentEntry s3 triggers rest, es)
  | .combatStep .layer _ :: rest =>
    some ({ s with pending := rest }, [])
  | .combatStep .attack layerId :: rest =>
    let info := s.layerMeta.getD layerId.n { controller := s.active.getD ⟨0⟩ }
    let eff := cardLayerEffect s layerId info
    let (s1, atkId, es) := enterAttackStep s layerId info.controller
    let tp := s1.active.getD ⟨0⟩
    let effFrames :=
      if eff == .nop then [] else [.run info.controller atkId info.fromArsenal [] [eff]]
    let attackTriggers := attackingCardTriggers s1 atkId info.controller info.fromArsenal info.attackAbilities
    let triggerFrames := if attackTriggers.isEmpty && eff == .nop then [] else [.flushTriggers]
    some ({ s1 with
              pendingTriggers := s1.pendingTriggers ++ attackTriggers
              nextTimestamp := s1.nextTimestamp + attackTriggers.length
              pending := effFrames ++ [.gameStateProcess] ++ triggerFrames ++
                [.priority tp 0, .combatStep .defend atkId] ++ rest },
          es)
  | .combatStep .defend atkId :: rest =>
    match s.combat with
    | some cc =>
      let cc' := { cc with step := .defend }
      match cc'.activeLink? with
      | some link =>
        some ({ s with
                  combat := some cc'
                  pending := .defendPick link.defender :: .combatStep .reaction atkId :: rest }, [])
      | none =>
        some ({ s with combat := some cc', pending := .combatStep .reaction atkId :: rest }, [])
    | none =>
      some ({ s with pending := rest }, [])
  | .combatStep .reaction atkId :: rest =>
    let tp := s.active.getD ⟨0⟩
    let phantasmHit :=
      match s.combat.bind CombatChain.activeLink? with
      | some link => phantasmTriggered s link
      | none => false
    if phantasmHit then
      let (s1, es) := applyPhantasmClose s
      let s2 := gspRun s1
      some ({ s2 with pending := .priority tp 0 :: rest }, es)
    else
      let cc' := s.combat.map fun cc => { cc with step := .reaction }
      some ({ s with
                combat := cc'
                pending := .gameStateProcess :: .priority tp 0 :: .combatStep .damage atkId :: rest }, [])
  | .combatStep .damage atkId :: rest =>
    match s.combat.bind CombatChain.activeLink? with
    | some link =>
      let amount := linkDamageBeforePrevention s link
      match damagePreventionFrame? s link.defender .physical amount (some atkId) with
      | some prevention => some ({ s with pending := prevention :: rest }, [])
      | none =>
        let (settled, events) := applyDamageWithPrevention s link.defender .physical amount
        let dealt := events.reverse.findSome? fun
          | .damageDealt _ .physical n => some n
          | _ => none
        some (finishCombatDamage settled atkId (dealt.getD 0) rest, events)
    | none => some (finishCombatDamage s atkId 0 rest, [])
  | .combatStep .resolution atkId :: rest =>
    let tp := s.active.getD ⟨0⟩
    match s.combat with
    | some cc =>
      match cc.activeLink? with
      | some link =>
        let grantGA := linkHasKeyword s link .goAgain && !link.goAgainGranted
        let cc' := { cc with step := .resolution }.updateActiveLink fun l =>
          { l with goAgainGranted := l.goAgainGranted || grantGA }
        let s1 := { s with combat := some cc' }
        let s2 :=
          if grantGA then
            s1.setPool link.attacker ((s1.poolOf link.attacker).addActionPoints 1)
          else
            s1
        some ({ s2 with
                  pending := .gameStateProcess :: .priority tp 0 :: .combatStep .close atkId :: rest }, [])
      | none =>
        some ({ s with
                  combat := some { cc with step := .resolution }
                  pending := .priority tp 0 :: .combatStep .close atkId :: rest }, [])
    | none =>
      some ({ s with pending := rest }, [])
  | .combatStep .close _ :: rest =>
    let (s1, es) := closeCombatChainStep s
    let s2 := gspRun s1
    let tp := s2.active.getD ⟨0⟩
    some ({ s2 with pending := .priority tp 0 :: rest }, es)
  | .gameStateProcess :: rest =>
    let s1 := gspRun s
    some ({ s1 with pending := rest }, [])
  | .run ctrl src fromArsenal env todo :: rest =>
    let ran := interpRunStep s ctrl src fromArsenal env todo rest
    some (queueRuleEventTriggers ran.1 ran.2, ran.2)
  | .optStep _ 0 :: rest =>
    some ({ s with pending := rest }, [])
  | .optStep p (n + 1) :: rest =>
    match s.zone (.player p .deck) with
    | topId :: tail =>
      some ({ s with pending := .chooseOpt p topId (tail.take n) 0 :: rest }, [])
    | [] =>
      some ({ s with pending := rest }, [])
  | .endPhaseStart tp :: rest =>
    let debt := applyBloodDebt s tp
    some (beginEndPhase debt.1 tp rest, debt.2)
  | .endPhaseArsenal tp :: rest =>
    let next :=
      if (s.zone (.player tp .arsenal)).isEmpty && !(s.zone (.player tp .hand)).isEmpty then
        .chooseArsenal tp :: rest
      else
        rest
    some ({ s with pending := next }, [])
  | .returnPitch p :: rest =>
    if (s.zone (.player p .pitch)).isEmpty then
      some ({ s with pending := rest }, [])
    else
      some ({ s with pending := .choosePitchOrder p :: rest }, [])
  | .endTurnCleanup tp :: rest =>
    let s0 := resetAlliesLife s
    let s1 := untapPlayer s0 tp
    let s2 := { s1 with
      pools := ∅
      activeReplacements := []
      chargedThisTurn := []
      boostsThisTurn := []
      delayedTriggers := s.delayedTriggers.filter fun trigger => trigger.watch != .boostThisTurn s.turn
      banishedSixPowerThisTurn := []
      activatedThisTurn := []
      weaponHitsThisTurn := []
      attackActionHitsThisTurn := []
      nonAttackActionsThisTurn := []
      arcaneDamageThisTurn := []
      attacksThisTurn := []
      triggeredThisTurn := [] }
    let draws := endPhaseDrawFrames s2 tp
    some ({ s2 with pending := draws ++ [.endTurnFinish] ++ rest }, [])
  | .endTurnFinish :: rest =>
    some ({ s.finishTurnEffects with pending := rest }, [])
  | .flushTriggers :: rest =>
    let triggers := s.pendingTriggers.filter fun t => !(t.targetChoices s).isEmpty
    if triggers.isEmpty then
      some ({ s with pendingTriggers := [], pending := rest }, [])
    else
      let tp := s.active.getD ⟨0⟩
      some ({ s with pendingTriggers := triggers, pending := .chooseTriggerStart tp :: rest }, [])
  | _ => none

end Fab

end
