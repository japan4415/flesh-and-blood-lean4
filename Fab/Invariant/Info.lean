module

public import Fab.Invariant.Step

/-!
# Hidden Information Non-Interference (I10)

Formalizes player observation `view p s` and proves **I10** (Hidden Information Non-Interference):
- Every player's Deck including Pitch deck-bottom return order (CR 4.4.3c) is normally
  count-only. While searching a deck, the searching player may see its contents (CR 8.5.19).
- Every opponent `q ≠ p`'s Hand, Inventory, and face-down Arsenal / Banished / Cloaked Equipment
  cards are hidden from player `p`.
- `legalActionsFor p s` (the set of legal actions available to player `p`) depends **strictly** on
  `p`-observable information and is completely invariant under:
  1. Arbitrary reordering or replacement of ANY player's Deck (preserving `p`'s deck length),
  2. Arbitrary modification of any opponent `q ≠ p`'s hidden zones (`hand`, `arsenal`, `banished`,
     `inventory`, `deck`).
-/

@[expose] public section

namespace Fab

/-- Observable representation of a single object from observer `p`'s perspective (CR 3.0). -/
inductive VisibleObj where
  /-- Publicly visible or owner-visible object with full attributes. -/
  | faceUp (o : Object)
  /-- Hidden face-down object (opponent Arsenal, Banished, or Cloaked equipment). -/
  | faceDown
deriving DecidableEq, Repr

/-- Observable representation of a single zone from observer `p`'s perspective (CR 3.0). -/
inductive VisibleZone where
  /-- Fully hidden zone whose card order/identities are secret; only its cardinality is known
  (all Decks, opponent Hand, opponent Inventory). -/
  | countOnly (len : Nat)
  /-- Zone whose entries are visible individually when face-up and masked when face-down. -/
  | entries (objs : List (Option VisibleObj))
deriving DecidableEq, Repr

/-- Whether zone `z` is completely hidden (count-only) to observer `p` (CR 3.0, 4.4.3c). -/
def Zone.isCountOnlyFor (p : PlayerId) : Zone → Bool
  | .player _ .deck => true
  | .player _ .outside => true
  | .player q .hand => q != p
  | .player q .inventory => q != p
  | _ => false

/-- The search decision gives only its player temporary access to the deck (CR 8.5.19). -/
def deckSearchVisible (p : PlayerId) (s : GameState) (z : Zone) : Bool :=
  match s.pending with
  | .chooseShuffleCards q _ _ _ _ (some choice) :: _ =>
    choice.searchesDeck && p == q && z == .player q .deck
  | _ => false

/-- Project one zone `z` into observer `p`'s `VisibleZone` (CR 3.0). -/
def viewZone (p : PlayerId) (s : GameState) (z : Zone) : VisibleZone :=
  let ids := s.zone z
  let beforeReveal := s.phase == .setup && s.pending.contains .revealLoadouts
  let hiddenLoadoutCount := match z with
    | .player q .permanent => if beforeReveal && q != p then some 0 else none
    | .player q .deck =>
      if beforeReveal && q != p then some (ids.length + (s.zone (.player q .permanent)).length) else none
    | _ => none
  if let some count := hiddenLoadoutCount then
    .countOnly count
  else if z.isCountOnlyFor p && !deckSearchVisible p s z then
    .countOnly ids.length
  else
    .entries (ids.map fun id =>
      (s.obj? id).map fun o =>
        if o.faceDown && o.owner != p then .faceDown else .faceUp o)

/-- Complete observable view of `GameState` for player `p` (**I10**). -/
structure PlayerView where
  /-- Fixed game configuration. -/
  config : GameConfig
  /-- Observable projection of every valid zone in `allZones`. -/
  zones : List (Zone × VisibleZone)
  /-- Asset pools. -/
  pools : Std.ExtTreeMap Nat AssetPool
  /-- Hero life totals. -/
  heroLife : Std.ExtTreeMap Nat Int
  /-- Turn counter, active player, turn order, phase, result. -/
  turn : Nat
  /-- Active turn-player. -/
  active : Option PlayerId
  /-- Clockwise turn order. -/
  turnOrder : List PlayerId
  /-- Current phase. -/
  phase : Phase
  /-- Game outcome. -/
  result : Option GameResult
  /-- Combat chain state. -/
  combat : Option CombatChain
  /-- Weapons that have hit during the current turn, including closed chains. -/
  weaponHitsThisTurn : List ObjId
  /-- Tournament clock & ID offer state. -/
  tournament : TournamentState
  /-- Pending continuation frames, with other players' private selections masked. -/
  pending : List Frame
  /-- Pending triggers. -/
  pendingTriggers : List PendingTrigger
  /-- Card identities for the current player's visible selections. -/
  selectionChoices : List (ObjId × CardId)
deriving DecidableEq, Repr

/-- Compute observer `p`'s observable view `view p s` of `GameState` `s` (**I10**). -/
def view (p : PlayerId) (s : GameState) : PlayerView :=
  let identify (q : PlayerId) (ids : List ObjId) :=
    if p == q then ids.filterMap (fun id => (s.cardDefOf? id).map (fun card => (id, card.id)))
    else []
  let selectionChoices := match s.pending with
    | .chooseShuffleCards q _ candidates _ _ search :: _ =>
      let viewed := match search.bind (·.bottomSelection) with
        | some (.lookedAt cards) => cards
        | _ => (search.bind (·.viewedCards)).getD candidates
      identify q viewed
    | .chooseDiscard q _ candidates _ _ :: _ => identify q candidates
    | .chooseOpt q first others _ _ :: _ => identify q (first :: others)
    | _ => []
  { config := s.config
    zones := (allZones s.playerCount).map fun z => (z, viewZone p s z)
    pools := s.pools
    heroLife := s.heroLife
    turn := s.turn
    active := s.active
    turnOrder := s.turnOrder
    phase := s.phase
    result := s.result
    combat := s.combat
    weaponHitsThisTurn := s.weaponHitsThisTurn
    tournament := s.tournament
    pending := s.pending.map fun frame =>
      match frame with
      | .chooseShuffleCards q _ _ _ drawSame search =>
        if p == q then frame else
          .chooseShuffleCards q 0 [] [] drawSame (search.map (fun choice => { choice with bottomSelection := none, viewedCards := none }))
      | .chooseDiscard q _ _ _ _ =>
        if p == q then frame else .chooseDiscard q 0 [] []
      | .chooseOpt q _ _ _ _ =>
        if p == q then frame else .chooseOpt q ⟨0⟩
      | .chooseReplacement q stage _ canDecline =>
        if p == q then frame else .chooseReplacement q stage [] canDecline
      | .chooseVariableResources q layer arsenal mode cost _ false =>
        if p == q then frame else .chooseVariableResources q layer arsenal mode cost 0 false
      | _ => frame
    pendingTriggers := s.pendingTriggers
    selectionChoices := selectionChoices }

/-- All legal actions belonging to player `p` in state `s`. -/
def legalActionsFor (p : PlayerId) (s : GameState) : List Action :=
  (legalActions s).filter fun a => a.actor == .player p

/-- Whether zone `z` is a hidden zone for observer `p` whose contents/ordering do not affect `p`'s
own legal moves: any player's Deck (only length matters for `p`'s own loadout) and any opponent's
Hand, Arsenal, Banished, or Inventory (CR 3.0, 4.4.3c). -/
def Zone.isSecretTo (p : PlayerId) : Zone → Bool
  | .player _ .deck => true
  | .player _ .outside => true
  | .player q .hand => q != p
  | .player q .arsenal => q != p
  | .player q .banished => q != p
  | .player q .inventory => q != p
  | _ => false

/-- Equivalence relation capturing hidden-information indistinguishability for observer `p`
(**I10**): `s1` and `s2` agree on all public metadata, object table, all zones not secret to `p`,
and the length of `p`'s own deck, while allowing completely arbitrary deck orders (e.g. Pitch
return order) and arbitrary contents/orders in opponent hidden zones. -/
structure HiddenEquiv (p : PlayerId) (s1 s2 : GameState) : Prop where
  /-- Same configuration. -/
  config : s1.config = s2.config
  /-- Same card database. -/
  cards : s1.cards = s2.cards
  /-- Same object definitions (for all visible objects). -/
  objects : s1.objects = s2.objects
  /-- Same pools. -/
  pools : s1.pools = s2.pools
  /-- Same hero life totals. -/
  heroLife : s1.heroLife = s2.heroLife
  /-- Same turn counter. -/
  turn : s1.turn = s2.turn
  /-- Same active player. -/
  active : s1.active = s2.active
  /-- Same continuation stack. -/
  pending : s1.pending = s2.pending
  /-- Same turn order. -/
  turnOrder : s1.turnOrder = s2.turnOrder
  /-- Same phase. -/
  phase : s1.phase = s2.phase
  /-- Same result. -/
  result : s1.result = s2.result
  /-- Same combat chain. -/
  combat : s1.combat = s2.combat
  /-- Same public declaration of which stack cards were played from arsenal. -/
  stackPlayFromArsenal : s1.stackPlayFromArsenal = s2.stackPlayFromArsenal
  /-- Same public weapon hit history. -/
  weaponHitsThisTurn : s1.weaponHitsThisTurn = s2.weaponHitsThisTurn
  /-- Same public history of paid boost costs this turn. -/
  boostsThisTurn : s1.boostsThisTurn = s2.boostsThisTurn
  /-- Same tournament state. -/
  tournament : s1.tournament = s2.tournament
  /-- Same public history of this turn's limited activations. -/
  activatedThisTurn : s1.activatedThisTurn = s2.activatedThisTurn
  /-- Same active continuous effects. -/
  activeEffects : s1.activeEffects = s2.activeEffects
  /-- Same pending triggers. -/
  pendingTriggers : s1.pendingTriggers = s2.pendingTriggers
  /-- Same contents on every zone that is NOT secret to `p`. -/
  visibleZones : ∀ z : Zone, z.isSecretTo p = false → s1.zone z = s2.zone z
  /-- Same deck length for `p` (deck order/contents remain completely secret!). -/
  ownDeckLen : (s1.zone (.player p .deck)).length = (s2.zone (.player p .deck)).length

/-- Helper: `HiddenEquiv p s1 s2` preserves `playerCount`. -/
theorem HiddenEquiv.playerCount {p : PlayerId} {s1 s2 : GameState} (h : HiddenEquiv p s1 s2) :
    s1.playerCount = s2.playerCount := by
  simp [GameState.playerCount, h.config]

/-- Helper: `HiddenEquiv p s1 s2` preserves `cardDefOf?` and `objectFace?`. -/
theorem HiddenEquiv.cardDef_face {p : PlayerId} {s1 s2 : GameState} (h : HiddenEquiv p s1 s2)
    (id : ObjId) :
    s1.cardDefOf? id = s2.cardDefOf? id ∧ s1.objectFace? id = s2.objectFace? id := by
  have ho : s1.obj? id = s2.obj? id := by simp [GameState.obj?, h.objects]
  constructor
  · unfold GameState.cardDefOf?; rw [ho, h.cards]
  · unfold GameState.objectFace?; rw [ho, h.cards]

/-- Helper: `HiddenEquiv p s1 s2` preserves `loadoutEquipDest? s p id`. -/
theorem HiddenEquiv.loadoutEquipDest {p : PlayerId} {s1 s2 : GameState} (h : HiddenEquiv p s1 s2)
    (id : ObjId) :
    loadoutEquipDest? s1 p id = loadoutEquipDest? s2 p id := by
  have hinv : s1.zone (.player p .inventory) = s2.zone (.player p .inventory) :=
    h.visibleZones _ (by simp [Zone.isSecretTo])
  have hhe : s1.zone (.player p .head) = s2.zone (.player p .head) := h.visibleZones _ rfl
  have hch : s1.zone (.player p .chest) = s2.zone (.player p .chest) := h.visibleZones _ rfl
  have har : s1.zone (.player p .arms) = s2.zone (.player p .arms) := h.visibleZones _ rfl
  have hle : s1.zone (.player p .legs) = s2.zone (.player p .legs) := h.visibleZones _ rfl
  have hwe : s1.zone (.player p .weapon) = s2.zone (.player p .weapon) := h.visibleZones _ rfl
  have hp : s1.zone (.player p .permanent) = s2.zone (.player p .permanent) := h.visibleZones _ rfl
  have hstart (card : CardDef) : setupPermanentAllowed s1 p card = setupPermanentAllowed s2 p card := by
    unfold setupPermanentAllowed
    rw [h.visibleZones (.player p .hero) rfl]
    cases (s2.zone (.player p .hero)).head? with
    | none => rfl
    | some hero => simp [(h.cardDef_face hero).2]
  have h2h : s1.hasTwoHandedEquipped p = s2.hasTwoHandedEquipped p := by
    unfold GameState.hasTwoHandedEquipped
    rw [hwe]
    congr 1; funext wid
    rw [(h.cardDef_face wid).1]
  unfold loadoutEquipDest?
  rw [hinv, (h.cardDef_face id).1, hhe, hch, har, hle, hwe, h2h, hp]
  simp only [hstart]

/-- The cards and active combat link determine whether an attack target can be declared. -/
private theorem HiddenEquiv.matchingActiveAttack_eq {p : PlayerId} {s1 s2 : GameState}
    (h : HiddenEquiv p s1 s2) (link : ChainLink) (spec : TargetSpec) :
    matchingActiveAttack s1 link spec = matchingActiveAttack s2 link spec := by
  unfold matchingActiveAttack
  rw [h.visibleZones .combatChain rfl]
  cases link.attack with
  | none => rfl
  | some attack =>
    cases link.attackSource with
    | none => cases spec.kind <;> simp [(h.cardDef_face attack).2]
    | some source => cases spec.kind <;> simp [(h.cardDef_face source).2]

/-- Legal reaction targets are independent of hidden zones. -/
theorem HiddenEquiv.hasRequiredAttackTarget_eq {p : PlayerId} {s1 s2 : GameState}
    (h : HiddenEquiv p s1 s2) (card : CardDef) (modeIdx : Option Nat) :
    hasRequiredAttackTarget s1 card modeIdx = hasRequiredAttackTarget s2 card modeIdx := by
  simp only [hasRequiredAttackTarget, h.combat, h.matchingActiveAttack_eq]

/-- Helper: `HiddenEquiv p s1 s2` preserves `canPickCardMode`. -/
theorem HiddenEquiv.canPickCardMode_eq {p : PlayerId} {s1 s2 : GameState}
    (h : HiddenEquiv p s1 s2) (layerId : ObjId) (idx : Nat) :
    canPickCardMode s1 layerId idx = canPickCardMode s2 layerId idx := by
  simp only [canPickCardMode, (h.cardDef_face layerId).1, h.hasRequiredAttackTarget_eq]

private theorem activationArenaZone_visible {s : GameState} {p : PlayerId} {z : Zone}
    (hz : z ∈ activationArenaZones s) : z.isSecretTo p = false := by
  rcases List.mem_cons.mp hz with rfl | hinstalled
  · rfl
  · have ha := (List.mem_filter.mp hinstalled).2
    cases z with
    | player q kind => cases kind <;> simp_all [Zone.isSecretTo, ZoneKind.isArena]
    | combatChain | stack => rfl

private theorem HiddenEquiv.arenaZones_eq {p : PlayerId} {s1 s2 : GameState}
    (h : HiddenEquiv p s1 s2) : activationArenaZones s1 = activationArenaZones s2 := by
  unfold activationArenaZones installedArenaZones
  rw [h.playerCount]

private theorem HiddenEquiv.arenaContents_eq {p : PlayerId} {s1 s2 : GameState}
    (h : HiddenEquiv p s1 s2) :
    (activationArenaZones s1).flatMap s1.zone = (activationArenaZones s2).flatMap s2.zone := by
  rw [h.arenaZones_eq]
  have hvisible (z : Zone) (hm : z ∈ activationArenaZones s2) : s1.zone z = s2.zone z :=
    h.visibleZones z (activationArenaZone_visible hm)
  generalize heq : activationArenaZones s2 = zones at *
  clear heq
  induction zones with
  | nil => rfl
  | cons z zs ih =>
    simp only [List.flatMap_cons, hvisible z (by simp), ih (fun a ha => hvisible a (by simp [ha]))]

private theorem HiddenEquiv.characteristics_eq {p : PlayerId} {s1 s2 : GameState}
    (h : HiddenEquiv p s1 s2) (id : ObjId) :
    s1.characteristics id = s2.characteristics id := by
  have ho : s1.obj? id = s2.obj? id := by simp [GameState.obj?, h.objects]
  have hsource : s1.arenaDefenseSourceEffects = s2.arenaDefenseSourceEffects := by
    funext defending source
    have hobj : s1.obj? source = s2.obj? source := by simp [GameState.obj?, h.objects]
    unfold GameState.arenaDefenseSourceEffects
    rw [hobj, (h.cardDef_face source).1, h.activeEffects]
  have hstatic : s1.arenaDefenseEffects id = s2.arenaDefenseEffects id := by
    unfold GameState.arenaDefenseEffects
    rw [h.arenaContents_eq, h.combat, hsource, h.activeEffects]
  have hphase : s1.hasActionPhaseEffect = s2.hasActionPhaseEffect := by
    funext player op
    simp only [GameState.hasActionPhaseEffect, h.phase, h.active, h.activeEffects]
  have hlife : s1.lessLifeThanOpponent = s2.lessLifeThanOpponent := by
    funext player
    unfold GameState.lessLifeThanOpponent GameState.lifeOf
    rw [h.playerCount, h.heroLife]
  have hconditional : s1.conditionalSelfStaticEffects id = s2.conditionalSelfStaticEffects id := by
    funext obj face effects
    delta GameState.conditionalSelfStaticEffects
    rw [h.arenaContents_eq, hlife, h.stackPlayFromArsenal, h.combat]
  unfold GameState.characteristics
  rw [ho, (h.cardDef_face id).1, h.activeEffects, hstatic, hconditional, hphase,
    h.visibleZones .stack rfl, h.arenaContents_eq]

private theorem HiddenEquiv.nameRestricted_eq {p : PlayerId} {s1 s2 : GameState}
    (h : HiddenEquiv p s1 s2) (id : ObjId) :
    s1.isCardNameRestricted id = s2.isCardNameRestricted id := by
  delta GameState.isCardNameRestricted
  rw [h.activeEffects, h.arenaContents_eq, h.characteristics_eq id]

private theorem HiddenEquiv.canTakeAction_eq {p : PlayerId} {s1 s2 : GameState}
    (h : HiddenEquiv p s1 s2) : s1.canTakeAction p = s2.canTakeAction p := by
  simp only [GameState.canTakeAction, GameState.hasActionPhaseEffect, h.phase, h.active, h.activeEffects]

private theorem HiddenEquiv.triggerTargetChoices_eq {p : PlayerId} {s1 s2 : GameState}
    (h : HiddenEquiv p s1 s2) (t : PendingTrigger) :
    t.targetChoices s1 = t.targetChoices s2 := by
  have htarget : equipmentControlledBy s1 = equipmentControlledBy s2 := by
    funext player id
    have ho : s1.obj? id = s2.obj? id := by simp [GameState.obj?, h.objects]
    simp only [equipmentControlledBy, ho, h.characteristics_eq]
  unfold PendingTrigger.targetChoices
  split
  · rw [h.arenaContents_eq, htarget]
  · rw [h.turnOrder]

/-- The attack keywords used to check defense legality agree under `HiddenEquiv`. -/
theorem HiddenEquiv.linkHasKeyword_eq_of_ne_goAgain {p : PlayerId} {s1 s2 : GameState}
    (h : HiddenEquiv p s1 s2) (link : ChainLink) (kw : KeywordInst) (hgo : kw ≠ .goAgain) :
    linkHasKeyword s1 link kw = linkHasKeyword s2 link kw := by
  unfold linkHasKeyword
  simp only [hgo, false_and, ↓reduceIte]
  have hmods : linkWeaponAttackModifiers s1 link = linkWeaponAttackModifiers s2 link := by
    simp only [linkWeaponAttackModifiers, h.activeEffects]
  rw [hmods]
  cases link.attack with
  | none => rfl
  | some aid => simp [h.characteristics_eq aid]

/-- Helper: `HiddenEquiv p s1 s2` preserves `canPlayCard s p id`. -/
theorem HiddenEquiv.canPlayCard_eq {p : PlayerId} {s1 s2 : GameState} (h : HiddenEquiv p s1 s2)
    (id : ObjId) (asInstant : Bool := false) :
    canPlayCard s1 p id asInstant = canPlayCard s2 p id asInstant := by
  have hh : s1.zone (.player p .hand) = s2.zone (.player p .hand) :=
    h.visibleZones _ (by simp [Zone.isSecretTo])
  have ha : s1.zone (.player p .arsenal) = s2.zone (.player p .arsenal) :=
    h.visibleZones _ (by simp [Zone.isSecretTo])
  have hb : s1.zone (.player p .banished) = s2.zone (.player p .banished) :=
    h.visibleZones _ (by simp [Zone.isSecretTo])
  have hbanished (asInstant : Bool) :
      canPlayFromBanished s1 p id asInstant = canPlayFromBanished s2 p id asInstant := by
    have hobj : s1.obj? id = s2.obj? id := by simp [GameState.obj?, h.objects]
    delta canPlayFromBanished
    rw [hb, hobj, h.combat, h.activeEffects]
  have hs : s1.zone .stack = s2.zone .stack := h.visibleZones _ rfl
  have hp : s1.poolOf p = s2.poolOf p := by simp [GameState.poolOf, h.pools]
  have hdom (link : ChainLink) : linkHasKeyword s1 link .dominate = linkHasKeyword s2 link .dominate :=
    h.linkHasKeyword_eq_of_ne_goAgain link .dominate (by decide)
  have hdefense (link : ChainLink) :
      linkForbidsDefenseReactions s1 link = linkForbidsDefenseReactions s2 link := by
    have hchain : s1.zone .combatChain = s2.zone .combatChain := h.visibleZones _ rfl
    have habilities : activeAttackPrintedAbilities s1 = activeAttackPrintedAbilities s2 := by
      funext source
      have ho : s1.obj? source = s2.obj? source := by simp [GameState.obj?, h.objects]
      unfold activeAttackPrintedAbilities
      rw [hchain, ho, h.characteristics_eq source, (h.cardDef_face source).2]
    unfold linkForbidsDefenseReactions
    rw [habilities]
  have hweapon (card : CardDef) : cardWeaponTargetChoices s1 p card = cardWeaponTargetChoices s2 p card := by
    have hobj (id : ObjId) : s1.obj? id = s2.obj? id := by simp [GameState.obj?, h.objects]
    have hface (id : ObjId) : s1.objectFace? id = s2.objectFace? id := (h.cardDef_face id).2
    have href (who : PlayerRef) : evalPlayerRef s1 p who = evalPlayerRef s2 p who := by
      cases who <;> simp only [evalPlayerRef, h.playerCount, h.active]
    unfold cardWeaponTargetChoices
    simp only [href, h.arenaContents_eq, hobj, hface, h.characteristics_eq]
  unfold canPlayCard
  simp only [hbanished]
  rw [hh, ha, (h.cardDef_face id).1, hs, hp, h.phase, h.active, h.combat,
    h.boostsThisTurn, h.canTakeAction_eq, h.activeEffects]
  simp only [canLinkTakeDefenseReaction, hdom, hdefense, attackReactionCanTarget, h.hasRequiredAttackTarget_eq,
    hweapon, h.characteristics_eq, h.nameRestricted_eq, h.arenaContents_eq, GameState.obj?, h.objects] <;> rfl

/-- The current weapon attack candidates depend on the visible weapon zone and combat chain. -/
theorem HiddenEquiv.weaponAttackCandidateIds_eq {p : PlayerId} {s1 s2 : GameState}
    (h : HiddenEquiv p s1 s2) : weaponAttackCandidateIds s1 p = weaponAttackCandidateIds s2 p := by
  unfold weaponAttackCandidateIds
  rw [h.combat, h.visibleZones (.player p .weapon) rfl, h.visibleZones .combatChain rfl]

/-- Helper: `HiddenEquiv p s1 s2` preserves `canAttackWithWeapon s p wid`. -/
theorem HiddenEquiv.canAttackWithWeapon_eq {p : PlayerId} {s1 s2 : GameState}
    (h : HiddenEquiv p s1 s2) (wid : ObjId) :
    canAttackWithWeapon s1 p wid = canAttackWithWeapon s2 p wid := by
  have hs : s1.zone .stack = s2.zone .stack := h.visibleZones _ rfl
  have hp : s1.poolOf p = s2.poolOf p := by simp [GameState.poolOf, h.pools]
  have hwid : s1.obj? wid = s2.obj? wid := by simp [GameState.obj?, h.objects]
  unfold canAttackWithWeapon
  rw [h.combat, h.phase, h.active, hs, hp, h.weaponAttackCandidateIds_eq,
      (h.cardDef_face wid).1, h.activatedThisTurn, h.activeEffects, hwid, h.canTakeAction_eq]

/-- Helper: `HiddenEquiv p s1 s2` preserves `canPitchCard s p id`. -/
theorem HiddenEquiv.canPitchCard_eq {p : PlayerId} {s1 s2 : GameState}
    (h : HiddenEquiv p s1 s2) (id : ObjId) :
    canPitchCard s1 p id = canPitchCard s2 p id := by
  have hh : s1.zone (.player p .hand) = s2.zone (.player p .hand) :=
    h.visibleZones _ (by simp [Zone.isSecretTo])
  have ho : s1.obj? id = s2.obj? id := by simp [GameState.obj?, h.objects]
  have haf : ∀ o, s1.activeFace? o = s2.activeFace? o := by
    intro o; unfold GameState.activeFace?; rw [h.cards]
  unfold canPitchCard
  rw [hh, ho, h.nameRestricted_eq id]
  cases s2.obj? id with
  | none => rfl
  | some o => simp [haf]

private theorem HiddenEquiv.controlledPermanentCount_eq {p : PlayerId} {s1 s2 : GameState}
    (h : HiddenEquiv p s1 s2) (card : CardId) :
    controlledPermanentCount s1 p card = controlledPermanentCount s2 p card := by
  have hzone (owner : PlayerId) :
      s1.zone (.player owner .permanent) = s2.zone (.player owner .permanent) :=
    h.visibleZones _ rfl
  have hobj (id : ObjId) : s1.obj? id = s2.obj? id := by simp [GameState.obj?, h.objects]
  simp only [controlledPermanentCount, h.playerCount, hzone, hobj, h.characteristics_eq]

private theorem HiddenEquiv.availableActivations_eq {p : PlayerId} {s1 s2 : GameState}
    (h : HiddenEquiv p s1 s2) : availableActivations s1 p = availableActivations s2 p := by
  have hz := h.arenaZones_eq
  have hvisible (z : Zone) (hm : z ∈ activationArenaZones s2) : s1.zone z = s2.zone z :=
    h.visibleZones z (activationArenaZone_visible hm)
  have hfind (id : ObjId) :
      (activationArenaZones s2).find? (fun z => (s1.zone z).contains id) =
        (activationArenaZones s2).find? (fun z => (s2.zone z).contains id) := by
    generalize heq : activationArenaZones s2 = zones at *
    clear heq hz
    induction zones with
    | nil => rfl
    | cons z zs ih =>
      simp only [List.find?_cons, hvisible z (by simp), ih (fun a ha => hvisible a (by simp [ha]))]
  have hsources : (activationArenaZones s2).flatMap s1.zone = (activationArenaZones s2).flatMap s2.zone := by
    simpa only [hz] using h.arenaContents_eq
  have htargets : (activationTargetZones s1).flatMap s1.zone = (activationTargetZones s2).flatMap s2.zone := by
    simp only [activationTargetZones, List.flatMap_cons, hz, hsources, h.visibleZones .stack rfl]
  have hmatching (spec : TargetSpec) (id : ObjId) :
      matchesActivationTarget s1 spec id = matchesActivationTarget s2 spec id := by
    have ho : s1.obj? id = s2.obj? id := by simp [GameState.obj?, h.objects]
    simp only [matchesActivationTarget, h.combat, h.matchingActiveAttack_eq,
      htargets, ho, (h.cardDef_face id).2, h.characteristics_eq id]
  have hresolution (effect : EffectDef) (target : Option ObjId) :
      activationResolution? s1 effect target = activationResolution? s2 effect target := by
    unfold activationResolution?
    split <;> simp only [hmatching]
  have hcanPitch (cost : AssetCost) : canPitchForCost s1 p cost = canPitchForCost s2 p cost := by
    unfold canPitchForCost pitchableCards
    rw [h.visibleZones _ (by simp [Zone.isSecretTo]), funext h.canPitchCard_eq]
    simp [GameState.poolOf, h.pools] <;> rfl
  have hcondition : activationConditionMet s1 p = activationConditionMet s2 p := by
    funext condition
    cases condition with
    | none => rfl
    | some condition =>
      cases condition <;>
        first
        | rfl
        | simp only [activationConditionMet, hasWeaponHitThisTurn,
            h.weaponHitsThisTurn, h.characteristics_eq, h.boostsThisTurn]
  have ha : s1.zone (.player p .arsenal) = s2.zone (.player p .arsenal) :=
    h.visibleZones _ (by simp [Zone.isSecretTo])
  have hturn : canTurnArsenalCardFaceUp s1 p = canTurnArsenalCardFaceUp s2 p := by
    funext id
    simp only [canTurnArsenalCardFaceUp, ha, GameState.obj?, h.objects, (h.cardDef_face id).1]
  have hsurcharge : activationPermanentSurcharge s1 p = activationPermanentSurcharge s2 p := by
    funext extra
    unfold activationPermanentSurcharge
    rw [show controlledPermanentCount s1 p = controlledPermanentCount s2 p from
      funext h.controlledPermanentCount_eq]
  have hgrave : s1.zone (.player p .graveyard) = s2.zone (.player p .graveyard) :=
    h.visibleZones _ rfl
  have hgraveTarget (spec : TargetSpec) (id : ObjId) :
      matchesActivationGraveyardTarget s1 p spec id = matchesActivationGraveyardTarget s2 p spec id := by
    have ho : s1.obj? id = s2.obj? id := by simp [GameState.obj?, h.objects]
    simp only [matchesActivationGraveyardTarget, hgrave, ho, (h.cardDef_face id).2]
  have hplan (id : ObjId) (index : Nat) (target secondTarget : Option ObjId) :
      activationPlan? s1 p id index target secondTarget =
        activationPlan? s2 p id index target secondTarget := by
    have ho : s1.obj? id = s2.obj? id := by simp [GameState.obj?, h.objects]
    have hp : s1.poolOf p = s2.poolOf p := by simp [GameState.poolOf, h.pools]
    unfold activationPlan?
    rw [hz, hfind, ho, h.characteristics_eq, (h.cardDef_face id).2, hp, h.playerCount,
      h.phase, h.active, h.combat, h.visibleZones .stack rfl, h.activatedThisTurn, h.canTakeAction_eq]
    have hcost : nextActionSurcharge s1 p = nextActionSurcharge s2 p := by
      simp only [nextActionSurcharge, h.activeEffects]
    simp only [hresolution, hcanPitch, hcondition, hcost, hturn, hsurcharge, hgraveTarget]
  have hface (id : ObjId) := (h.cardDef_face id).2
  have hgraveFilter : matchesActivationGraveyardTarget s1 p = matchesActivationGraveyardTarget s2 p :=
    funext fun spec => funext (hgraveTarget spec)
  unfold availableActivations
  simp only [hz, hsources, hface, hplan, htargets, ha, hgrave, hgraveFilter]

/-- Candidate defenders depend only on the defender’s visible zones and permissions. -/
private theorem HiddenEquiv.defendCandidateIds_eq {p : PlayerId} {s1 s2 : GameState}
    (h : HiddenEquiv p s1 s2) : defendCandidateIds s1 p = defendCandidateIds s2 p := by
  unfold defendCandidateIds equipZoneIds canDefendFromArsenal
  rw [h.visibleZones (.player p .hand) (by simp [Zone.isSecretTo]),
    h.visibleZones _ rfl, h.visibleZones _ rfl, h.visibleZones _ rfl, h.visibleZones _ rfl,
    h.activeEffects, h.visibleZones (.player p .arsenal) (by simp [Zone.isSecretTo])]

/-- Helper: `HiddenEquiv p s1 s2` preserves `canDefendWith s link p id`. -/
theorem HiddenEquiv.canDefendWith_eq {p : PlayerId} {s1 s2 : GameState}
    (h : HiddenEquiv p s1 s2) (link : ChainLink) (id : ObjId) :
    canDefendWith s1 link p id = canDefendWith s2 link p id := by
  have hh : s1.zone (.player p .hand) = s2.zone (.player p .hand) :=
    h.visibleZones _ (by simp [Zone.isSecretTo])
  have ha : s1.zone (.player p .arsenal) = s2.zone (.player p .arsenal) :=
    h.visibleZones _ (by simp [Zone.isSecretTo])
  unfold canDefendWith
  rw [h.defendCandidateIds_eq, hh, ha, (h.cardDef_face id).2, h.nameRestricted_eq id]
  rw [h.linkHasKeyword_eq_of_ne_goAgain link .dominate (by decide),
      h.linkHasKeyword_eq_of_ne_goAgain link .overpower (by decide)]

/-- **I10 (Hidden Information Non-Interference — Core Theorem)**:
If two game states `s1` and `s2` satisfy `HiddenEquiv p s1 s2` (differing arbitrarily in ANY
player's Deck order/contents or any opponent `q ≠ p`'s hidden Hand / Arsenal / Banished /
Inventory), then player `p` has the **exact same list of legal actions** in `s1` and `s2`
(CR 3.0, 4.4.3c). -/
theorem hiddenEquiv_legalActionsFor_eq {p : PlayerId} {s1 s2 : GameState}
    (h : HiddenEquiv p s1 s2) :
    legalActionsFor p s1 = legalActionsFor p s2 := by
  unfold legalActionsFor legalActions
  rw [h.result]
  split
  · simp only [List.filter_append]
    congr 1
    · congr 1
      · -- legalFrameActions filtered to `.player p`
        unfold legalFrameActions
        rw [h.pending]
        cases s2.pending with
        | nil => rfl
        | cons f rest =>
          cases f with
          | chooseFirstPlayer chooser =>
            dsimp only
            rw [h.playerCount]
          | chooseLoadout q =>
            dsimp only
            by_cases hqp : q = p
            · subst hqp
              have hinv : s1.zone (.player q .inventory) = s2.zone (.player q .inventory) :=
                h.visibleZones _ (by simp [Zone.isSecretTo])
              have hadd : ∀ id, loadoutCanAddDeck s1 q id = loadoutCanAddDeck s2 q id := by
                intro id; unfold loadoutCanAddDeck; rw [hinv, (h.cardDef_face id).1]
              have hfin : loadoutCanFinish s1 q = loadoutCanFinish s2 q := by
                unfold loadoutCanFinish
                rw [h.config, h.ownDeckLen, h.visibleZones (.player q .permanent) rfl]
              have hdest : ∀ id, (loadoutEquipDest? s1 q id).isSome = (loadoutEquipDest? s2 q id).isSome :=
                fun id => by rw [h.loadoutEquipDest id]
              rw [hinv, hfin]
              simp only [hdest, hadd]
            · have hne : (Actor.player q == Actor.player p) = false := by simp [hqp]
              simp only [List.filter_append]
              have hnil : ∀ (l : List ObjId) (g : ObjId → ActionKind),
                  List.filter (fun a => a.actor == Actor.player p)
                    (l.map fun id => Action.mk (.player q) (g id)) = [] := by
                intro l g
                induction l with
                | nil => rfl
                | cons x xs ih => simp [hne, ih]
              rw [hnil, hnil, hnil, hnil]
              split <;> split <;> simp [hne]
          | priority q _ =>
            dsimp only
            by_cases hqp : q = p
            · subst hqp
              have hh : s1.zone (.player q .hand) = s2.zone (.player q .hand) :=
                h.visibleZones _ (by simp [Zone.isSecretTo])
              have ha : s1.zone (.player q .arsenal) = s2.zone (.player q .arsenal) :=
                h.visibleZones _ (by simp [Zone.isSecretTo])
              have hb : s1.zone (.player q .banished) = s2.zone (.player q .banished) :=
                h.visibleZones _ (by simp [Zone.isSecretTo])
              have hcards : playCardCandidateIds s1 q = playCardCandidateIds s2 q := by
                simp only [playCardCandidateIds, hh, ha, hb]
              have hwep : canAttackWithWeapon s1 q = canAttackWithWeapon s2 q :=
                funext h.canAttackWithWeapon_eq
              have hplay :
                  (fun play : ObjId × Bool => canPlayCard s1 q play.1 play.2) =
                    (fun play : ObjId × Bool => canPlayCard s2 q play.1 play.2) := by
                funext play
                exact h.canPlayCard_eq play.1 play.2
              rw [hcards, h.weaponAttackCandidateIds_eq, hwep, h.availableActivations_eq, hplay]
            · have hne : (Actor.player q == Actor.player p) = false := by simp [hqp]
              simp only [List.filter_cons, hne, List.filter_append]
              have hnil : ∀ {α : Type} (l : List α) (g : α → ActionKind),
                  List.filter (fun a => a.actor == Actor.player p)
                    (l.map fun id => Action.mk (.player q) (g id)) = [] := by
                intro α l g
                induction l with
                | nil => rfl
                | cons x xs ih => simp [hne, ih]
              rw [hnil, hnil, hnil, hnil, hnil, hnil]
          | defendPick defender =>
            dsimp only
            by_cases hdp : defender = p
            · subst hdp
              rw [h.combat]
              cases s2.combat.bind CombatChain.activeLink? with
              | none => rfl
              | some link =>
                dsimp only
                have hdef : canDefendWith s1 link defender = canDefendWith s2 link defender :=
                  funext (h.canDefendWith_eq link)
                rw [h.defendCandidateIds_eq, hdef]
            · have hne : (Actor.player defender == Actor.player p) = false := by simp [hdp]
              simp only [List.filter_append, List.filter_cons, List.filter_nil, hne]
              have hnil : ∀ (l : List ObjId),
                  List.filter (fun a => a.actor == Actor.player p)
                    (l.map fun id => Action.mk (.player defender) (.defendCard id)) = [] := by
                intro l
                induction l with
                | nil => rfl
                | cons x xs ih => simp [hne, ih]
              cases s1.combat.bind CombatChain.activeLink? <;>
                cases s2.combat.bind CombatChain.activeLink? <;> simp [hnil]
          | chooseMode _ layerId _ _ _ =>
            dsimp only
            rw [show canPickCardMode s1 layerId = canPickCardMode s2 layerId from
              funext (h.canPickCardMode_eq layerId)]
          | choosePlayHero _ layerId _ _ _ =>
            dsimp only
            simp only [cardPlayHeroChoices, (h.cardDef_face layerId).1, h.turnOrder]
          | choosePitch q _ _ _ _ =>
            dsimp only
            by_cases hqp : q = p
            · subst hqp
              have hpitch : pitchableCards s1 q = pitchableCards s2 q := by
                unfold pitchableCards
                rw [h.visibleZones _ (by simp [Zone.isSecretTo]), funext h.canPitchCard_eq]
              rw [hpitch]
            · have hne : (Actor.player q == Actor.player p) = false := by simp [hqp]
              simp only [List.filter_append, List.filter_cons, List.filter_nil, hne]
              have hnil : ∀ (l : List ObjId),
                  List.filter (fun a => a.actor == Actor.player p)
                    (l.map fun id => Action.mk (.player q) (.pitchCard id)) = [] := by
                intro l; induction l with | nil => rfl | cons x xs ih => simp [hne, ih]
              rw [hnil, hnil]
          | choosePlayWeapon _ _ _ _ _ _ | chooseOptionalPlayCost _ _ _ _ _ _ => rfl
          | chooseGraveyardCost _ _ _ _ _ _ | chooseVariableResources _ _ _ _ _ _ _ => rfl
          | chooseHandCardCost q _ _ _ cost =>
            dsimp only
            by_cases hqp : q = p
            · subst hqp
              have hh := h.visibleZones (.player q .hand) (by simp [Zone.isSecretTo])
              have hf : canPickHandCostCard s1 q cost = canPickHandCostCard s2 q cost := by
                funext id
                cases cost with
                | putOnDeck _ => simp [canPickHandCostCard, hh]
                | reveal filter =>
                  simp [canPickHandCostCard, revealCostCard?, hh,
                    (h.cardDef_face id).1, (h.cardDef_face id).2]
              rw [hh, hf]
            · have hne : (Actor.player q == Actor.player p) = false := by simp [hqp]
              simp only [List.filter_append, List.filter_cons, List.filter_nil, hne]
              have hnil : ∀ (l : List ObjId),
                  List.filter (fun a => a.actor == Actor.player p)
                    (l.map fun id => Action.mk (.player q) (.pickHandCostCard id)) = [] := by
                intro l; induction l with | nil => rfl | cons x xs ih => simp [hne, ih]
              rw [hnil, hnil]
          | chooseMay _ _ _ _ _ _ => rfl
          | chooseModal _ _ _ _ _ => rfl
          | chooseHandToDeck q _ =>
            dsimp only
            by_cases hqp : q = p
            · subst hqp
              rw [h.visibleZones (.player q .hand) (by simp [Zone.isSecretTo])]
            · have hne : (Actor.player q == Actor.player p) = false := by simp [hqp]
              have hnil : ∀ (l : List ObjId),
                  List.filter (fun a => a.actor == Actor.player p)
                    (l.map fun id => Action.mk (.player q) (.handToDeckPick id)) = [] := by
                intro l; induction l with | nil => rfl | cons x xs ih => simp [hne, ih]
              rw [hnil, hnil]
          | chooseDiscard _ _ _ _ _ | chooseShuffleCards _ _ _ _ _ _ | chooseOpt _ _ _ _ _ => rfl
          | chooseArsenal tp =>
            dsimp only
            by_cases htp : tp = p
            · subst htp
              rw [h.visibleZones (.player tp .arsenal) (by simp [Zone.isSecretTo]),
                  h.visibleZones (.player tp .hand) (by simp [Zone.isSecretTo])]
            · have hne : (Actor.player tp == Actor.player p) = false := by simp [htp]
              simp only [List.filter_append, List.filter_cons, List.filter_nil, hne]
              have hnil : ∀ (l : List ObjId),
                  List.filter (fun a => a.actor == Actor.player p)
                    (l.map fun id => Action.mk (.player tp) (.arsenalPut id)) = [] := by
                intro l; induction l with | nil => rfl | cons x xs ih => simp [hne, ih]
              by_cases he1 : (s1.zone (.player tp .arsenal)).isEmpty = true <;>
                by_cases he2 : (s2.zone (.player tp .arsenal)).isEmpty = true <;>
                simp [he1, he2, hnil]
          | choosePitchOrder q =>
            dsimp only
            rw [h.visibleZones (.player q .pitch) rfl]
          | chooseTriggerStart _ =>
            dsimp only
            rw [h.turnOrder]
          | chooseTriggerOrder _ _ =>
            dsimp only
            simp only [h.pendingTriggers, h.triggerTargetChoices_eq]
          | choosePreventionPitch q =>
            dsimp only
            by_cases hqp : q = p
            · subst hqp
              unfold pitchableCards
              rw [h.visibleZones (.player q .hand) (by simp [Zone.isSecretTo]),
                funext h.canPitchCard_eq]
            · have hne : (Actor.player q == Actor.player p) = false := by simp [hqp]
              have hnil : ∀ (l : List ObjId),
                  List.filter (fun a => a.actor == Actor.player p)
                    (l.map fun id => Action.mk (.player q) (.pitchCard id)) = [] := by
                intro l; induction l with | nil => rfl | cons x xs ih => simp [hne, ih]
              rw [hnil, hnil]
          | chooseReplacement _ _ _ _ | chooseTriggerGraveyard _ _ _ _ _ _
          | chooseArcaneDamageOrder _ _ _ _ => rfl
          | chanceFirstPlayer | revealLoadouts | chanceShuffle _ | openingDraws | draw _ _
          | beginTurn | startPhaseWork _ | actionPhaseStart _ | playPayCost _ _ _ _ _
          | payRandomDiscard _ _ _ _ _
          | resolveStack | finishResolve _ | combatStep _ _ | gameStateProcess | run _ _ _ _ _
          | chanceDie6 _ _ _ _ _ _ _ | optStep _ _ | endPhaseStart _ | endPhaseArsenal _ | returnPitch _
          | arcaneDamage _ _ _ _ _ | endTurnCleanup _ | endTurnFinish | flushTriggers => rfl
      · -- concedeActions
        unfold concedeActions
        rw [h.playerCount]
    · -- tournamentPlayerActions
      unfold tournamentPlayerActions
      rw [h.playerCount, h.config, h.tournament]
  · rfl

/-- **I10 Corollary (Pitch Deck-Bottom Order Secrecy)** (CR 4.4.3c):
Reordering a deck that the observer is not currently searching leaves both their view
and legal actions unchanged. -/
theorem reorder_deck_noninterference {s : GameState} (p q : PlayerId) {l : List ObjId}
    (hperm : l.Perm (s.zone (.player q .deck))) (hhidden : deckSearchVisible p s (.player q .deck) = false) :
    view p (s.reorder (.player q .deck) l) = view p s ∧
    legalActionsFor p (s.reorder (.player q .deck) l) = legalActionsFor p s := by
  have hlen : l.length = (s.zone (.player q .deck)).length := hperm.length_eq
  have heq : HiddenEquiv p (s.reorder (.player q .deck) l) s :=
    { config := rfl, cards := rfl, objects := rfl, pools := rfl, heroLife := rfl,
      turn := rfl, active := rfl, pending := rfl, turnOrder := rfl, phase := rfl,
      result := rfl, combat := rfl, weaponHitsThisTurn := rfl, tournament := rfl,
      activatedThisTurn := rfl, activeEffects := rfl, boostsThisTurn := rfl,
      stackPlayFromArsenal := by
        funext id
        unfold GameState.stackPlayFromArsenal GameState.reorder
        rw [GameState.zone_setZone_ne s (show Zone.stack ≠ .player q .deck from by intro he; cases he) l] <;> rfl,
      pendingTriggers := rfl,
      visibleZones := fun z hns => by
        have hne : z ≠ .player q .deck := by
          intro he; subst he; simp [Zone.isSecretTo] at hns
        exact GameState.zone_setZone_ne s hne l,
      ownDeckLen := by
        by_cases hqp : p = q
        · subst hqp
          unfold GameState.reorder
          rw [GameState.zone_setZone_self]
          exact hlen
        · have hne : Zone.player p .deck ≠ Zone.player q .deck := by
            intro he; cases he; exact hqp rfl
          unfold GameState.reorder
          rw [GameState.zone_setZone_ne s hne l] }
  constructor
  · unfold view
    dsimp only
    congr 1
    apply List.map_congr_left
    intro z _
    congr 1
    unfold viewZone
    have hpermanent (owner : PlayerId) :
        (s.setZone (.player q .deck) l).zone (.player owner .permanent) =
          s.zone (.player owner .permanent) :=
      GameState.zone_setZone_ne s (by intro he; cases he) l
    have hphase : (s.setZone (.player q .deck) l).phase = s.phase := rfl
    have hpending : (s.setZone (.player q .deck) l).pending = s.pending := rfl
    by_cases hzd : z = .player q .deck
    · subst hzd
      have hsearch : deckSearchVisible p (s.setZone (.player q .deck) l) (.player q .deck) =
          deckSearchVisible p s (.player q .deck) := rfl
      simp [Zone.isCountOnlyFor, hsearch, hhidden, GameState.reorder, GameState.zone_setZone_self,
        hlen, hpermanent, hphase, hpending]
    · simp only [GameState.reorder, GameState.zone_setZone_ne s hzd l, hpermanent, hphase, hpending]
      rfl
  · exact hiddenEquiv_legalActionsFor_eq heq

/-- **I10 Corollary (Opponent Hand Secrecy)**:
Replacing opponent `q ≠ p`'s hand with any list `l` (same length preserves `view p s` as well)
never affects `legalActionsFor p s`. -/
theorem opp_hand_noninterference {s : GameState} {p q : PlayerId} (hne : q ≠ p) (l : List ObjId) :
    legalActionsFor p (s.setZone (.player q .hand) l) = legalActionsFor p s := by
  apply hiddenEquiv_legalActionsFor_eq
  exact
    { config := rfl, cards := rfl, objects := rfl, pools := rfl, heroLife := rfl,
      turn := rfl, active := rfl, pending := rfl, turnOrder := rfl, phase := rfl,
      result := rfl, combat := rfl, weaponHitsThisTurn := rfl, tournament := rfl,
      activatedThisTurn := rfl, activeEffects := rfl, boostsThisTurn := rfl,
      stackPlayFromArsenal := by
        funext id
        unfold GameState.stackPlayFromArsenal
        rw [GameState.zone_setZone_ne s (show Zone.stack ≠ .player q .hand from by intro he; cases he) l] <;> rfl,
      pendingTriggers := rfl,
      visibleZones := fun z hns => by
        have hnez : z ≠ .player q .hand := by
          intro he; subst he; simp [Zone.isSecretTo, hne] at hns
        exact GameState.zone_setZone_ne s hnez l,
      ownDeckLen := by
        have hnez : Zone.player p .deck ≠ Zone.player q .hand := by intro he; cases he
        rw [GameState.zone_setZone_ne s hnez l] }

end Fab

end
