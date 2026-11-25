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
  decide (s.config.format.spec.deckSize.Satisfied (s.zone (.player p .deck)).length)

/-- Hero intellect of player `p`, defaulting to 4 if absent (CR 2.4, 4.1.6). -/
def GameState.intellectOf (s : GameState) (p : PlayerId) : Nat :=
  match s.zone (.player p .hero) with
  | hid :: _ =>
    match s.cardDefOf? hid with
    | some c => c.front.intellect.getD 4
    | none => 4
  | [] => 4

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

/-- All equipped armor and weapon object identifiers across all players. -/
def loadoutArenaIds (s : GameState) : List ObjId :=
  (allPlayers s.playerCount).flatMap fun p =>
    s.zone (.player p .head) ++ s.zone (.player p .chest) ++
    s.zone (.player p .arms) ++ s.zone (.player p .legs) ++
    s.zone (.player p .weapon)

/-- Simultaneously reveal all non-Cloaked equipped armor and weapon cards across all players
(CR 4.1.4). -/
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
    !(fromHand && linkHasKeyword s link .dominate && 1 ≤ link.defendedFromHandCount)

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

/-- Whether player `p` may announce playing card `id` from hand or arsenal while holding priority
(CR 5.1.1, 4.3, 3.2.2, 7.1, 7.4, 7.6).
- Instants: playable anytime on priority.
- Actions: own Action Phase, empty stack, ≥1 AP, and either combat chain closed or (for Attack
  Action cards) in Resolution Step to continue a combat chain.
- Attack Reactions: Reaction Step as the attacking player (CR 7.4).
- Defense Reactions: Reaction Step as the defending player, respecting Dominate from hand (CR 7.4, 8.3.4). -/
def canPlayCard (s : GameState) (p : PlayerId) (id : ObjId) : Bool :=
  let fromHand := id ∈ s.zone (.player p .hand)
  let fromArsenal := id ∈ s.zone (.player p .arsenal)
  if fromHand || fromArsenal then
    match s.cardDefOf? id with
    | none => false
    | some c =>
      if !c.isDeckCard then
        false
      else if c.front.hasType .instant then
        true
      else if c.front.hasType .action then
        let chainOk :=
          match s.combat with
          | none => true
          | some cc => cc.step == .resolution && c.front.hasSubtype .attack
        s.phase == .actionPhase &&
        s.active == some p &&
        (s.zone .stack).isEmpty &&
        chainOk &&
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

/-- Apply the announcing player's next-attack card cost modifiers (CR 5.1.2a, 5.1.7). -/
def modifiedCardPlayCost (s : GameState) (p : PlayerId) (card : CardDef) : AssetCost :=
  let base := cardPlayCost card
  if card.front.hasType .action && card.front.hasSubtype .attack then
    let delta := s.activeEffects.foldl (fun total effect =>
      match effect.target with
      | .nextAttackCard filter =>
        if effect.controller == p && !filter.isWeaponAttack && cardFaceMatches filter card.front then
          match effect.op with
          | .addCostRes n => total + Int.ofNat n
          | .subCostRes n => total - Int.ofNat n
          | _ => total
        else total
      | _ => total) (0 : Int)
    { base with resources := clampNonNeg (Int.ofNat base.resources + delta) }
  else base

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

/-- Offer an optional resource cost once targets have been declared (CR 5.1.5). -/
def cardPaymentFrame (s : GameState) (p : PlayerId) (layerId : ObjId) (fromArsenal : Bool)
    (modeIdx : Option Nat) (cost : AssetCost) : Frame :=
  match (s.cardDefOf? layerId).bind (·.front.playEffect) with
  | some { extraCosts := [{ cost := .payResources extra, optional := true, cond := none }], .. } =>
    .chooseOptionalResources p layerId fromArsenal modeIdx cost extra
  | _ => .playPayCost p layerId fromArsenal modeIdx cost

/-- Select target declaration or cost payment after any required mode has been chosen (CR 5.1.4a). -/
def cardPlayTargetFrame (s : GameState) (p : PlayerId) (layerId : ObjId) (fromArsenal : Bool)
    (modeIdx : Option Nat) (cost : AssetCost) : Frame :=
  let pay := cardPaymentFrame s p layerId fromArsenal modeIdx cost
  match s.cardDefOf? layerId with
  | none => pay
  | some card =>
    let targets := card.front.playEffect.map fun effect =>
      (modeIdx.bind (fun idx => effect.modes[idx]?)).map (·.targets) |>.getD effect.targets
    if targets == some [{ kind := .hero }] &&
        ((cardResolveEffect card modeIdx).bindIntimidateTarget p).isSome then
      .choosePlayHero p layerId fromArsenal modeIdx cost
    else
      pay

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
  | some attack => s.layerMeta.insert layerId.n { controller := p, attackTarget := some attack }

/-- Read the card-layer's resolution effect with its declared hero target bound. -/
def cardLayerEffect (s : GameState) (layerId : ObjId) (info : LayerInfo) : Effect :=
  match s.cardDefOf? layerId with
  | none => .nop
  | some card =>
    let effect := cardResolveEffect card info.modeIdx
    (info.heroTarget.bind effect.bindIntimidateTarget).getD effect

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

/-- Advance to the next player in `order` who still controls at least one pending triggered ability,
returning `[.chooseTriggerOrder q rem]` or `[]` when all pending triggers are stacked (CR 6.6.6b). -/
def nextTriggerFrame (s : GameState) : List PlayerId → List Frame
  | [] => []
  | q :: rem =>
    if s.pendingTriggers.any (fun t => t.controller == q) then
      [.chooseTriggerOrder q rem]
    else
      nextTriggerFrame s rem

/-- Resolve remaining end-phase layers without granting priority (CR 4.4.1, 4.4.2). -/
def afterLayerResolution (s : GameState) : Frame :=
  if s.phase = .endPhase then .resolveStack else .priority (s.active.getD ⟨0⟩) 0

/-- The source of a resolving ability layer, or the resolving card itself. -/
def resolvingSource (s : GameState) (layer : ObjId) : ObjId :=
  match (s.obj? layer).map Object.kind with
  | some (.layer src _ _ _) => src
  | _ => layer

/-- Whether the engine supports the required declarations for a triggered effect (CR 6.6.6a). -/
def supportsTriggerTargets (effect : EffectDef) : Bool :=
  effect.targets.isEmpty ||
    (effect.targets == [{ kind := .hero }] &&
      effect.body == .prim (.intimidate (.ownerOfSlot 0)))

/-- Find matching triggers and their once-per-turn flags (CR 6.6). -/
def matchingCardTriggers (s : GameState) (source : ObjId) (controller : PlayerId) (fromArsenal : Bool)
    (abilities : List Ability) (matchesEvent : Trigger → Option Condition → Bool)
    (matchesOrdinal : Option Nat → Bool := Option.isNone) : List (PendingTrigger × Bool) :=
  abilities.zipIdx.filterMap fun (ability, abilityIdx) =>
    match ability with
    | .triggered trigger once ordinal cond eff =>
      if matchesOrdinal ordinal && matchesEvent trigger cond && supportsTriggerTargets eff && eff.modes.isEmpty &&
          eff.extraCosts.isEmpty then
        some ({
          id := 0
          source := source
          sourceLki := captureLki s source controller
          controller := controller
          abilityIdx := abilityIdx
          fromArsenal := fromArsenal
          effect := eff.body }, once)
      else none
    | _ => none

/-- Collect matching unrestricted triggers that require no modes or additional costs (CR 6.6). -/
def collectCardTriggers (s : GameState) (source : ObjId) (controller : PlayerId) (fromArsenal : Bool)
    (abilities : List Ability) (matchesEvent : Trigger → Option Condition → Bool) :
    List PendingTrigger :=
  let triggers := (matchingCardTriggers s source controller fromArsenal abilities matchesEvent).filterMap
    fun (trigger, once) => if once then none else some trigger
  triggers.zipIdx.map fun (trigger, idx) => { trigger with id := s.nextTimestamp + idx }

/-- Zones holding installed arena objects, excluding cards underneath a hero (CR 3.0.14b). -/
def installedArenaZones (s : GameState) : List Zone :=
  (allZones s.playerCount).filter fun
    | .player _ kind => kind.isArena && kind != .soul
    | _ => false

/-- Collect relevant abilities on installed arena objects under the player's control (CR 1.7.4, 3.0.14b). -/
def installedCardTriggers (s : GameState) (p : PlayerId) (matchesEvent : Trigger → Bool) :
    List (PendingTrigger × Bool) :=
  ((installedArenaZones s).flatMap s.zone).flatMap fun source =>
    if (s.characteristics source).any (fun c => c.controller == p && !c.abilitiesLost) &&
        (s.obj? source).any (fun obj => !obj.faceDown) then
      let abilities := ((s.objectFace? source).map (·.abilities)).getD []
      matchingCardTriggers s source p false abilities fun event cond =>
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

/-- Queue discard abilities in event order (CR 6.6). -/
def queueDiscardTriggers (s : GameState) (events : List Event) : GameState :=
  queueCardTriggers s (events.flatMap fun
    | .discarded p id => discardEventTriggers s p id
    | _ => [])

/-- Find installed arena abilities triggered by a successful attack (CR 7.5.3). -/
def installedHitTriggers (s : GameState) (link : ChainLink) : List (PendingTrigger × Bool) :=
  let source := link.attackSource.or link.attack
  match source.bind s.characteristics with
  | some attack =>
    let isAction := link.attackSource.isNone && attack.types.contains .action && attack.subtypes.contains .attack
    let isWeapon := link.attackSource.isSome && attack.types.contains .weapon
    let streak := ((s.combat.map fun chain => chain.links.takeWhile (·.hit)).getD []).length
    installedCardTriggers s attack.controller fun
      | .onConsecutiveHitLink minLink => isAction && minLink ≤ streak
      | .onWeaponAttackHit => isWeapon
      | _ => false
  | none => []

/-- Identify the live weapon that sourced the link's attack (CR 1.4.3, 7.5.3). -/
def hitWeapon? (s : GameState) (link : ChainLink) : Option ObjId := do
  let source ← link.attackSource
  if (s.characteristics source).any (·.types.contains .weapon) then some source else none

/-- Collect hit triggers on the source weapon, including exact per-turn hit ordinals (CR 6.6.5d). -/
def weaponHitTriggers (s : GameState) (link : ChainLink) : List (PendingTrigger × Bool) :=
  match hitWeapon? s link with
  | some source =>
    if (s.obj? source).any (·.faceDown) || (s.characteristics source).any (·.abilitiesLost) then [] else
      let abilities := ((s.objectFace? source).map (·.abilities)).getD []
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
    collectCardTriggers s source link.attacker false (printed ++ link.grantedAbilities)
      fun trigger cond =>
        let matchesEvent := match trigger with
          | .onHit => link.hit
          | .onCrush => crushTriggered link
          | _ => false
        matchesEvent && (cond.map (evalCondition s link.attacker source false)).getD true

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
      let eligible := match effect.target with
        | .nextAttackCard filter =>
          !isProxy && !filter.isWeaponAttack && cardFaceMatches filter face
        | .nextAttack filter | .allAttacks filter =>
          (!filter.isWeaponAttack || isWeapon) && cardFaceMatches filter face
        | _ => false
      if effect.controller == info.controller && eligible then
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
          ({ layer with attackKeywords := insertUnique keyword layer.attackKeywords }, rest)
        | .grantAttackAbility ability =>
          ({ layer with attackAbilities := ability :: layer.attackAbilities }, rest)
        | .addCostRes _ | .subCostRes _ =>
          match effect.target with
          | .nextAttackCard _ => (layer, rest)
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

/-- Finalize a paid layer, then stack triggers queued during play and return priority (CR 5.1.10, 6.6.6). -/
def finishPaidPlay (s : GameState) (p : PlayerId) (layerId : ObjId) (fromArsenal : Bool)
    (modeIdx : Option Nat) (rest : List Frame) (discarded : Option CardFace := none) : GameState :=
  let card := s.cardDefOf? layerId
  let hasGoAgain :=
    match card with
    | some c => c.front.keywords.contains .goAgain && !c.front.hasSubtype .attack
    | none => false
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
      attackTarget := (s.layerMeta.get? layerId.n).bind (·.attackTarget)
      additionalCostPaid := (s.layerMeta.get? layerId.n).any (·.payAdditionalResources)
      discardedForPlay := discarded
      attackAbilities :=
        (modeOnAttack.map fun body => Ability.triggered .onAttack false none none { body := body }).toList
      goAgain := hasGoAgain }
  let (updatedInfo, remainingEffects) := consumeNextAttackEffects s layerId info
  let activation := paidWeaponActivation? s layerId
  let effects := match activation with
    | some (weapon, index) =>
      if s.activatedThisTurn.contains (weapon, index) then
        remainingEffects.eraseP (fun effect => effect.allowsWeaponAttack p weapon)
      else remainingEffects
    | none => remainingEffects
  let s := { s with layerMeta := s.layerMeta.insert layerId.n updatedInfo }
  let newTriggers := playedCardTriggers s layerId p fromArsenal ++ arenaAttackPlayTriggers s layerId p
  let triggers := newTriggers.zipIdx.map fun (trigger, index) =>
    { trigger with id := s.nextTimestamp + index }
  let pendingTriggers := s.pendingTriggers ++ triggers
  let flush := if pendingTriggers.isEmpty then [] else [.flushTriggers]
  { s with
    activeEffects := effects
    playRollback := none
    activatedThisTurn := s.activatedThisTurn ++ activation.toList
    pendingTriggers := pendingTriggers
    nextTimestamp := s.nextTimestamp + triggers.length
    pending := flush ++ (.priority p 0 :: rest) }

/-- The declarations and payment for a supported activated ability (CR 5.2.2). -/
structure ActivationPlan where
  /-- Public zone of the source at announcement. -/
  origin : Zone
  /-- Owner of the source, whose graveyard takes a destroyed card. -/
  owner : PlayerId
  /-- The player's pool after paying the asset cost. -/
  pool : AssetPool
  /-- Whether destruction of the source is a required cost. -/
  destroySource : Bool
  /-- Whether this indexed ability has a once-per-turn limit. -/
  oncePerTurn : Bool
  /-- Whether its layer grants Go Again on resolution. -/
  goAgain : Bool
  /-- Resolution effect stored on the activated layer. -/
  body : Effect
  /-- Required target and its resolution-time eligibility filter. -/
  target : Option (TargetSpec × ObjId)

/-- Arena zones where public activated abilities are functional (CR 1.7.4). -/
def activationArenaZones (s : GameState) : List Zone :=
  .combatChain :: installedArenaZones s

/-- Public zones that can contain an attack action card targeted by an activation (CR 1.8.5a). -/
def activationTargetZones (s : GameState) : List Zone :=
  .stack :: activationArenaZones s

/-- Check an attack action card target, including cards on earlier links (CR 1.8.5, 1.8.9). -/
def matchesActivationTarget (s : GameState) (spec : TargetSpec) (id : ObjId) : Bool :=
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

/-- Bind a declared single target to a turn-duration attack modifier (CR 5.1.4a, 5.2.2b, 6.2.2a). -/
def activationResolution? (s : GameState) (effect : EffectDef) (target : Option ObjId) :
    Option (Effect × Option (TargetSpec × ObjId)) :=
  match effect.targets, target, effect.body with
  | [], none, body => some (body, none)
  | [spec], some id, .grant (.obj (.slot 0)) mod .thisTurn =>
    if spec.minCount == 1 && spec.maxCount == some 1 && matchesActivationTarget s spec id then
      match mod with
      | .addPower _ | .grantKeyword _ =>
        some (.grant (.paidAttack id) mod .thisTurn, some (spec, id))
      | _ => none
    else none
  | _, _, _ => none

/-- Read the announced ability and its payable costs from a visible arena source (CR 5.2.2). -/
def activationPlan? (s : GameState) (p : PlayerId) (source : ObjId) (index : Nat) (target : Option ObjId) :
    Option ActivationPlan := do
  let origin ← (activationArenaZones s).find? (fun z => (s.zone z).contains source)
  let obj ← s.obj? source
  if obj.owner.n ≥ s.playerCount || obj.faceDown then none else
  let terms ← (do
    let chars ← s.characteristics source
    let face ← s.objectFace? source
    let .activated speed once cost extra none goAgain effect ← face.abilities[index]? | none
    let timely := match speed with
      | .action => s.phase == .actionPhase && s.active == some p && s.combat.isNone && (s.zone .stack).isEmpty
      | .instant => true
      | .attackReaction =>
        s.combat.any fun cc => cc.step == .reaction && cc.activeLink?.any (fun link => link.attacker == p)
      | _ => false
    let destroy := extra == [{ cost := .destroySelf }]
    if !timely || chars.abilitiesLost || chars.controller != p ||
        (once && s.activatedThisTurn.contains (source, index)) ||
        !(extra.isEmpty || destroy) ||
        !(effect.modes.isEmpty && effect.extraCosts.isEmpty) ||
        effect.body == .prim .weaponAttack then none else
    let (body, declared) ← activationResolution? s effect target
    some (speed, once, cost, destroy, goAgain, body, declared))
  let (speed, once, cost, destroy, goAgain, body, declared) := terms
  let cost := if speed == .action then { cost with actionPoints := max cost.actionPoints 1 } else cost
  let pool := s.poolOf p
  let paid ← pool.spend cost (cost.resources - pool.resources)
  some ⟨origin, obj.owner, paid, destroy, once, goAgain, body, declared⟩

/-- The indexed abilities currently available to a player holding priority. -/
def availableActivations (s : GameState) (p : PlayerId) : List (ObjId × Nat × Option ObjId) :=
  let sources := (activationArenaZones s).flatMap s.zone
  let candidates := sources.flatMap fun source =>
    let abilities := ((s.objectFace? source).map (·.abilities)).getD []
    abilities.zipIdx.flatMap fun (ability, index) =>
      match ability with
      | .activated _ _ _ _ _ _ effect =>
        if effect.targets.isEmpty then [(source, index, none)]
        else ((activationTargetZones s).flatMap s.zone).map fun id => (source, index, some id)
      | _ => []
  candidates.filter fun (source, index, target) => (activationPlan? s p source index target).isSome

/-- Pay a permanent's destruction cost before priority returns (CR 5.2.2b). -/
def payActivationSource (s : GameState) (source : ObjId) (plan : ActivationPlan) :
    Option (GameState × List Event) := do
  if !plan.destroySource then some (s, []) else
    let graveyard := Zone.player plan.owner .graveyard
    let (paid, spent) ← moveObj s source graveyard .top false
    some (paid, [.moved source spent plan.origin graveyard])

/-- Commit a paid activated layer with the source's last known information (CR 5.2.2). -/
def startActivation (s : GameState) (p : PlayerId) (source : ObjId) (index : Nat)
    (target : Option ObjId) (rest : List Frame) :
    Option (GameState × List Event) := do
  let plan ← activationPlan? s p source index target
  let (paid, events) ← payActivationSource (s.setPool p plan.pool) source plan
  let layer : Object :=
    { kind := .layer source (some (captureLki s source p)) index false
      owner := p, controller := p, timestamp := ⟨paid.nextTimestamp⟩ }
  let (stacked, layerId) ← addObject paid .stack layer .top
  let info : LayerInfo := {
    controller := p, goAgain := plan.goAgain, triggerEffect := some plan.body, activationTarget := plan.target }
  let uses := if plan.oncePerTurn then (source, index) :: stacked.activatedThisTurn else stacked.activatedThisTurn
  some ({ stacked with
    activatedThisTurn := uses
    layerMeta := stacked.layerMeta.insert layerId.n info
    pending := .priority p 0 :: rest }, events ++
      plan.target.toList.map (fun declared => .targetedAttack layerId declared.2))

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
          some ({ s1 with pending := .chooseLoadout p :: rest },
                [.moved id id' (.player p .inventory) dst])
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
  | .priority p _ :: rest, .player q, .playCard id =>
    if p = q ∧ canPlayCard s p id = true then
      let fromArsenal := id ∈ s.zone (.player p .arsenal)
      let srcZone := if fromArsenal then Zone.player p .arsenal else Zone.player p .hand
      let snap := s.snapshot
      let cost := match s.cardDefOf? id with | some c => modifiedCardPlayCost s p c | none => {}
      let modes := match s.cardDefOf? id with | some c => cardModeCount c | none => 0
      let isAtkCard := match s.cardDefOf? id with
        | some c => c.front.hasType .action && c.front.hasSubtype .attack
        | none => false
      let rest' := if isAtkCard then dropPendingClose rest else rest
      match moveObj s id .stack .top false with
      | none => none
      | some (s1, layerId) =>
        let target := if 0 < modes then none else cardAttackTarget? s1 layerId none
        let nextFrame :=
          if 0 < modes then
            Frame.chooseMode p layerId fromArsenal modes cost
          else
            cardPlayTargetFrame s1 p layerId fromArsenal none cost
        some ({ s1 with
                  playRollback := some snap
                  layerMeta := layerMetaWithAttackTarget s1 p layerId target
                  pending := nextFrame :: rest' },
              [.moved id layerId srcZone .stack] ++ (target.map (.targetedAttack layerId)).toList)
    else
      none
  | .priority p _ :: rest, .player q, .attackWeapon wid =>
    if p = q ∧ canAttackWithWeapon s p wid = true then
      let snap := s.snapshot
      let cost := match s.cardDefOf? wid with | some c => weaponAttackCost c | none => { actionPoints := 1 }
      let lki := captureLki s wid p
      let proxyObj : Object :=
        { kind := .attackProxy wid (some lki)
          owner := p
          controller := p
          timestamp := ⟨s.nextTimestamp⟩ }
      match addObject s .stack proxyObj .top with
      | none => none
      | some (s1, proxyId) =>
        let rest' := dropPendingClose rest
        some ({ s1 with
                  playRollback := some snap
                  pending := .playPayCost p proxyId false none cost :: rest' },
              [])
    else
      none
  | .priority p _ :: rest, .player q, .activateAbility source index target =>
    if p = q then startActivation s p source index target rest else none
  | .defendPick defender :: rest, .player q, .defendCard id =>
    match s.combat.bind CombatChain.activeLink? with
    | some link =>
      if defender = q ∧ canDefendWith s link defender id = true then
        let fromHand := id ∈ s.zone (.player defender .hand)
        let isAction := match s.objectFace? id with | some f => f.hasType .action | none => false
        match s.locate id, moveObj s id .combatChain .top false with
        | some srcZ, some (s1, id') =>
          let cc' := s1.combat.map fun cc => cc.updateActiveLink fun l =>
            { l with
              defending := l.defending ++ [id']
              defendedFromHandCount := l.defendedFromHandCount + (if fromHand then 1 else 0)
              defendedActionCount := l.defendedActionCount + (if isAction then 1 else 0) }
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
    if p = q ∧ hero ∈ s.turnOrder then
      let info : LayerInfo := { controller := p, heroTarget := some hero }
      some ({ s with
                layerMeta := s.layerMeta.insert layerId.n info
                pending := cardPaymentFrame s p layerId fromArsenal modeIdx cost :: rest },
            [.targetedHero layerId hero])
    else
      none
  | .choosePlayHero p _ _ _ _ :: rest, .player q, .cancelPlay =>
    if p = q then
      some (rollbackPlay s rest, [])
    else
      none
  | .choosePitch p layerId fromArsenal modeIdx cost :: rest, .player q, .pitchCard id =>
    if p = q ∧ canPitchCard s p id = true then
      match pitchOne s p id with
      | none => none
      | some (s1, pitched, es) =>
        let abilities := ((s1.objectFace? pitched).map (·.abilities)).getD []
        let triggers := collectCardTriggers s1 pitched p false abilities fun trigger cond =>
          trigger == .onPitch && (cond.map (evalCondition s1 p pitched false)).getD true
        some ({ s1 with
                  pendingTriggers := s1.pendingTriggers ++ triggers
                  nextTimestamp := s1.nextTimestamp + triggers.length
                  pending := .playPayCost p layerId fromArsenal modeIdx cost :: rest }, es)
    else
      none
  | .choosePitch p _ _ _ _ :: rest, .player q, .cancelPlay =>
    if p = q then
      some (rollbackPlay s rest, [])
    else
      none
  | .chooseOptionalResources p layerId fromArsenal modeIdx cost extra :: rest, .player q,
      .pickMay accept =>
    if p = q then
      let total := if accept then { cost with resources := cost.resources + extra } else cost
      let info := s.layerMeta.getD layerId.n { controller := p }
      some ({ s with
                layerMeta := s.layerMeta.insert layerId.n { info with payAdditionalResources := accept }
                pending := .playPayCost p layerId fromArsenal modeIdx total :: rest }, [])
    else
      none
  | .chooseOptionalResources p _ _ _ _ _ :: rest, .player q, .cancelPlay =>
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
  | .chooseOpt p cardId :: rest, .player q, .optPick putOnTop =>
    if p = q then
      if putOnTop then
        some ({ s with pending := rest }, [])
      else
        let deck := s.zone (.player p .deck)
        if cardId ∈ deck then
          let deck' := deck.erase cardId ++ [cardId]
          some ({ s.reorder (.player p .deck) deck' with pending := rest }, [])
        else
          some ({ s with pending := rest }, [])
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
  | .chooseTriggerOrder p rem :: rest, .player q, .pickTrigger tid target =>
    if p = q then
      match s.pendingTriggers.find? (fun t => t.matchesDeclaration tid p target s.turnOrder) with
      | none => none
      | some trig =>
        let layerObj : Object :=
          { kind := .layer trig.source (some trig.sourceLki) trig.abilityIdx true
            owner := p
            controller := p
            timestamp := ⟨s.nextTimestamp⟩ }
        match addObject s .stack layerObj .top with
        | none => none
        | some (s1, lid) =>
          let remTrigs := s1.pendingTriggers.filter (fun t => t.id != tid)
          let info : LayerInfo :=
            { controller := p
              fromArsenal := trig.fromArsenal
              modeIdx := none
              goAgain := false
              triggerEffect := some (trig.declaredEffect target) }
          let s2 := { s1 with
            pendingTriggers := remTrigs
            layerMeta := s1.layerMeta.insert lid.n info }
          let nextF := nextTriggerFrame s2 (p :: rem)
          some ({ s2 with pending := nextF ++ rest }, (target.map (.targetedHero lid)).toList)
    else
      none
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
  let phaseState := { s with phase := .endPhase }
  let queued := queueCardTriggers phaseState (installedCardTriggers phaseState tp (· == .onStartOfEndPhase))
  let selected := s.delayedTriggers.partition fun trigger => trigger.watchPhase == .endPhase
  let delayed := selected.1.map fun trigger =>
    { id := trigger.id
      source := trigger.source
      sourceLki := captureLki s trigger.source trigger.controller
      controller := trigger.controller
      abilityIdx := 0
      effect := trigger.effect : PendingTrigger }
  let pendingTriggers := queued.pendingTriggers ++ delayed
  let triggerFrames := if pendingTriggers.isEmpty then [] else [.flushTriggers, .resolveStack]
  { s with
    phase := .endPhase
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
  | .startPhaseWork _ :: rest =>
    some ({ s with phase := .startPhase, pending := rest }, [])
  | .actionPhaseStart tp :: rest =>
    let s1 := { s with phase := .actionPhase }
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
  | .payRandomDiscard p layerId fromArsenal modeIdx count :: rest =>
    let (paid, events) := discardManyObjs s p ((s.zone (.player p .hand)).take count)
    let discarded := events.reverse.findSome? fun
      | .discarded _ id => paid.objectFace? id
      | _ => none
    some (finishPaidPlay (queueDiscardTriggers paid events) p layerId fromArsenal modeIdx rest discarded, events)
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
              !(info.activationTarget.all fun (spec, target) => matchesActivationTarget s spec target) then
            .nop
          else
            match info.triggerEffect with
            | some teff => teff
            | none => cardLayerEffect s topId info
        some ({ s with
                  pending := .run info.controller (resolvingSource s topId) info.fromArsenal [] [eff] ::
                    .finishResolve topId :: rest },
              [])
    | [] =>
      let next := if s.phase = .endPhase then rest else afterLayerResolution s :: rest
      some ({ s with pending := .gameStateProcess :: next }, [])
  | .finishResolve layerId :: rest =>
    let info := s.layerMeta.getD layerId.n { controller := s.active.getD ⟨0⟩ }
    let isDefReact := isDefenseReactionLayer s layerId
    let joinsDefense := isDefReact && canResolveDefenseReaction s info
    let s1 :=
      if info.goAgain && (!isDefReact || joinsDefense) then
        s.setPool info.controller ((s.poolOf info.controller).addActionPoints 1)
      else
        s
    let (s2, es) :=
      if layerId ∈ s1.zone .stack then
        if joinsDefense then
          match moveObj s1 layerId .combatChain .top false with
          | some (sMoved, id') =>
            let cc' := sMoved.combat.map fun cc => cc.updateActiveLink fun l =>
              { l with
                defending := l.defending ++ [id']
                defendedFromHandCount := l.defendedFromHandCount + (if !info.fromArsenal then 1 else 0) }
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
              match moveObj s1 layerId dst .top false with
              | some (sMoved, id') => (sMoved, [.moved layerId id' .stack dst])
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
    let tp := s.active.getD ⟨0⟩
    match s.combat with
    | some cc =>
      match cc.activeLink? with
      | some link =>
        let rawDmg := linkDamageBeforePrevention s link
        let (s2, es) := applyDamageWithPrevention s link.defender .physical rawDmg
        let finalDmg :=
          match es.reverse.find? fun | .damageDealt _ .physical _ => true | _ => false with
          | some (.damageDealt _ _ d) => d
          | _ => 0
        let isHit := didCombatHit finalDmg
        let damagedLink := { link with hit := isHit, damageDealt := finalDmg }
        let cc' := { cc with step := .damage }.updateActiveLink fun _ => damagedLink
        let weaponHit := if isHit then hitWeapon? s2 damagedLink else none
        let withDamage := { s2 with
          combat := some cc'
          weaponHitsThisTurn := weaponHit.toList ++ s2.weaponHitsThisTurn }
        let damageTriggers := if isHit && withDamage.result.isNone then
          (attackDamageTriggers withDamage damagedLink).map (fun trigger => (trigger, false)) ++
            installedHitTriggers withDamage damagedLink ++ weaponHitTriggers withDamage damagedLink
          else []
        let queued := queueCardTriggers withDamage damageTriggers
        let s3 := gspRun queued
        let triggers := if queued.pendingTriggers.isEmpty then [] else [.flushTriggers]
        some ({ s3 with pending := triggers ++ [.priority tp 0, .combatStep .resolution atkId] ++ rest }, es)
      | none =>
        some ({ s with
                  combat := some { cc with step := .damage }
                  pending := .priority tp 0 :: .combatStep .resolution atkId :: rest }, [])
    | none =>
      some ({ s with pending := rest }, [])
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
    some (queueDiscardTriggers ran.1 ran.2, ran.2)
  | .optStep _ 0 :: rest =>
    some ({ s with pending := rest }, [])
  | .optStep p (n + 1) :: rest =>
    match s.zone (.player p .deck) with
    | topId :: _ =>
      some ({ s with pending := .chooseOpt p topId :: .optStep p n :: rest }, [])
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
    let s2 := ({ s1 with
      pools := ∅
      activeReplacements := []
      chargedThisTurn := []
      banishedSixPowerThisTurn := []
      activatedThisTurn := []
      weaponHitsThisTurn := []
      triggeredThisTurn := [] }).expireEffects .thisTurn
    let draws := endPhaseDrawFrames s2 tp
    some ({ s2 with pending := draws ++ rest }, [])
  | .flushTriggers :: rest =>
    if s.pendingTriggers.isEmpty then
      some ({ s with pending := rest }, [])
    else
      let tp := s.active.getD ⟨0⟩
      some ({ s with pending := .chooseTriggerStart tp :: rest }, [])
  | _ => none

end Fab

end
