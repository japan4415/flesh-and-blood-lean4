module

public import Fab.Invariant.Step

/-!
# Hidden Information Non-Interference (I10)

Formalizes player observation `view p s` and proves **I10** (Hidden Information Non-Interference):
- Every player's Deck including Pitch deck-bottom return order (CR 4.4.3c) is hidden — only its
  length is observable.
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
  | .player q .hand => q != p
  | .player q .inventory => q != p
  | _ => false

/-- Project one zone `z` into observer `p`'s `VisibleZone` (CR 3.0). -/
def viewZone (p : PlayerId) (s : GameState) (z : Zone) : VisibleZone :=
  let ids := s.zone z
  if z.isCountOnlyFor p then
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
  /-- Tournament clock & ID offer state. -/
  tournament : TournamentState
  /-- Pending continuation frames. -/
  pending : List Frame
  /-- Pending triggers. -/
  pendingTriggers : List PendingTrigger
deriving DecidableEq, Repr

/-- Compute observer `p`'s observable view `view p s` of `GameState` `s` (**I10**). -/
def view (p : PlayerId) (s : GameState) : PlayerView :=
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
    tournament := s.tournament
    pending := s.pending
    pendingTriggers := s.pendingTriggers }

/-- All legal actions belonging to player `p` in state `s`. -/
def legalActionsFor (p : PlayerId) (s : GameState) : List Action :=
  (legalActions s).filter fun a => a.actor == .player p

/-- Whether zone `z` is a hidden zone for observer `p` whose contents/ordering do not affect `p`'s
own legal moves: any player's Deck (only length matters for `p`'s own loadout) and any opponent's
Hand, Arsenal, Banished, or Inventory (CR 3.0, 4.4.3c). -/
def Zone.isSecretTo (p : PlayerId) : Zone → Bool
  | .player _ .deck => true
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
  have h2h : s1.hasTwoHandedEquipped p = s2.hasTwoHandedEquipped p := by
    unfold GameState.hasTwoHandedEquipped
    rw [hwe]
    congr 1; funext wid
    rw [(h.cardDef_face wid).1]
  unfold loadoutEquipDest?
  rw [hinv, (h.cardDef_face id).1, hhe, hch, har, hle, hwe, h2h]

/-- The cards and active combat link determine whether an attack target can be declared. -/
theorem HiddenEquiv.hasRequiredAttackTarget_eq {p : PlayerId} {s1 s2 : GameState}
    (h : HiddenEquiv p s1 s2) (card : CardDef) (modeIdx : Option Nat) :
    hasRequiredAttackTarget s1 card modeIdx = hasRequiredAttackTarget s2 card modeIdx := by
  have hm (link : ChainLink) (spec : TargetSpec) :
      matchingActiveAttack s1 link spec = matchingActiveAttack s2 link spec := by
    unfold matchingActiveAttack
    rw [h.visibleZones .combatChain rfl]
    cases link.attack with
    | none => rfl
    | some attack =>
      cases link.attackSource with
      | none => cases spec.kind <;> simp [(h.cardDef_face attack).2]
      | some source => cases spec.kind <;> simp [(h.cardDef_face source).2]
  simp only [hasRequiredAttackTarget, h.combat, hm]

/-- Helper: `HiddenEquiv p s1 s2` preserves `canPickCardMode`. -/
theorem HiddenEquiv.canPickCardMode_eq {p : PlayerId} {s1 s2 : GameState}
    (h : HiddenEquiv p s1 s2) (layerId : ObjId) (idx : Nat) :
    canPickCardMode s1 layerId idx = canPickCardMode s2 layerId idx := by
  simp only [canPickCardMode, (h.cardDef_face layerId).1, h.hasRequiredAttackTarget_eq]

/-- The attack keywords used to check defense legality agree under `HiddenEquiv`. -/
theorem HiddenEquiv.linkHasKeyword_eq_of_ne_goAgain {p : PlayerId} {s1 s2 : GameState}
    (h : HiddenEquiv p s1 s2) (link : ChainLink) (kw : KeywordInst) (hgo : kw ≠ .goAgain) :
    linkHasKeyword s1 link kw = linkHasKeyword s2 link kw := by
  unfold linkHasKeyword
  simp only [ite_eq_right hgo]
  cases link.attack with
  | none => rfl
  | some aid => simp [(h.cardDef_face aid).2]

/-- Helper: `HiddenEquiv p s1 s2` preserves `canPlayCard s p id`. -/
theorem HiddenEquiv.canPlayCard_eq {p : PlayerId} {s1 s2 : GameState} (h : HiddenEquiv p s1 s2)
    (id : ObjId) :
    canPlayCard s1 p id = canPlayCard s2 p id := by
  have hh : s1.zone (.player p .hand) = s2.zone (.player p .hand) :=
    h.visibleZones _ (by simp [Zone.isSecretTo])
  have ha : s1.zone (.player p .arsenal) = s2.zone (.player p .arsenal) :=
    h.visibleZones _ (by simp [Zone.isSecretTo])
  have hs : s1.zone .stack = s2.zone .stack := h.visibleZones _ rfl
  have hp : s1.poolOf p = s2.poolOf p := by simp [GameState.poolOf, h.pools]
  have hdom (link : ChainLink) : linkHasKeyword s1 link .dominate = linkHasKeyword s2 link .dominate :=
    h.linkHasKeyword_eq_of_ne_goAgain link .dominate (by decide)
  unfold canPlayCard
  rw [hh, ha, (h.cardDef_face id).1, hs, hp, h.phase, h.active, h.combat]
  simp only [canLinkTakeDefenseReaction, hdom, attackReactionCanTarget, h.hasRequiredAttackTarget_eq]

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
  unfold canAttackWithWeapon
  rw [h.combat, h.phase, h.active, hs, hp, h.weaponAttackCandidateIds_eq,
      (h.cardDef_face wid).1, h.activatedThisTurn, h.activeEffects]

private theorem activationArenaZone_visible {s : GameState} {p : PlayerId} {z : Zone}
    (hz : z ∈ activationArenaZones s) : z.isSecretTo p = false := by
  rcases List.mem_cons.mp hz with rfl | hinstalled
  · rfl
  · have ha := (List.mem_filter.mp hinstalled).2
    cases z with
    | player q kind => cases kind <;> simp_all [Zone.isSecretTo, ZoneKind.isArena]
    | combatChain | stack => rfl

private theorem HiddenEquiv.availableActivations_eq {p : PlayerId} {s1 s2 : GameState}
    (h : HiddenEquiv p s1 s2) : availableActivations s1 p = availableActivations s2 p := by
  have hz : activationArenaZones s1 = activationArenaZones s2 := by
    unfold activationArenaZones installedArenaZones
    rw [h.playerCount]
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
    generalize heq : activationArenaZones s2 = zones at *
    clear heq hz hfind
    induction zones with
    | nil => rfl
    | cons z zs ih =>
      simp only [List.flatMap_cons, hvisible z (by simp), ih (fun a ha => hvisible a (by simp [ha]))]
  have hplan (id : ObjId) (index : Nat) : activationPlan? s1 p id index = activationPlan? s2 p id index := by
    have ho : s1.obj? id = s2.obj? id := by simp [GameState.obj?, h.objects]
    have hc : s1.characteristics id = s2.characteristics id := by
      unfold GameState.characteristics
      rw [ho, (h.cardDef_face id).1, h.activeEffects]
    have hp : s1.poolOf p = s2.poolOf p := by simp [GameState.poolOf, h.pools]
    unfold activationPlan?
    rw [hz, hfind, ho, hc, (h.cardDef_face id).2, hp, h.playerCount,
      h.phase, h.active, h.combat, h.visibleZones .stack rfl, h.activatedThisTurn]
  have hface (id : ObjId) := (h.cardDef_face id).2
  unfold availableActivations
  simp only [hz, hsources, hface, hplan]

/-- Helper: `HiddenEquiv p s1 s2` preserves `canDefendWith s link p id`. -/
theorem HiddenEquiv.canDefendWith_eq {p : PlayerId} {s1 s2 : GameState}
    (h : HiddenEquiv p s1 s2) (link : ChainLink) (id : ObjId) :
    canDefendWith s1 link p id = canDefendWith s2 link p id := by
  have hh : s1.zone (.player p .hand) = s2.zone (.player p .hand) :=
    h.visibleZones _ (by simp [Zone.isSecretTo])
  have heq : equipZoneIds s1 p = equipZoneIds s2 p := by
    unfold equipZoneIds
    rw [h.visibleZones _ rfl, h.visibleZones _ rfl, h.visibleZones _ rfl, h.visibleZones _ rfl]
  unfold canDefendWith
  rw [hh, heq, (h.cardDef_face id).2]
  rw [h.linkHasKeyword_eq_of_ne_goAgain link .dominate (by decide),
      h.linkHasKeyword_eq_of_ne_goAgain link .overpower (by decide)]

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
  rw [hh, ho]
  cases s2.obj? id with
  | none => rfl
  | some o => simp [haf]

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
                unfold loadoutCanFinish; rw [h.config, h.ownDeckLen]
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
              have hplay : canPlayCard s1 q = canPlayCard s2 q := funext h.canPlayCard_eq
              have hwep : canAttackWithWeapon s1 q = canAttackWithWeapon s2 q :=
                funext h.canAttackWithWeapon_eq
              rw [hh, ha, h.weaponAttackCandidateIds_eq, hplay, hwep, h.availableActivations_eq]
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
                have hcand : defendCandidateIds s1 defender = defendCandidateIds s2 defender := by
                  unfold defendCandidateIds equipZoneIds
                  rw [h.visibleZones _ (by simp [Zone.isSecretTo]),
                      h.visibleZones _ rfl, h.visibleZones _ rfl,
                      h.visibleZones _ rfl, h.visibleZones _ rfl]
                have hdef : canDefendWith s1 link defender = canDefendWith s2 link defender :=
                  funext (h.canDefendWith_eq link)
                rw [hcand, hdef]
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
          | choosePlayHero _ _ _ _ _ =>
            dsimp only
            rw [h.turnOrder]
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
          | chooseOptionalResources _ _ _ _ _ _ => rfl
          | chooseHandCardCost q _ _ _ cost =>
            dsimp only
            by_cases hqp : q = p
            · subst hqp
              have hh := h.visibleZones (.player q .hand) (by simp [Zone.isSecretTo])
              have hf : canPickHandCostCard s1 q cost = canPickHandCostCard s2 q cost := by
                funext id
                cases cost with
                | bottomDeck => simp [canPickHandCostCard, hh]
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
          | chooseOpt _ _ => rfl
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
            rw [h.pendingTriggers, h.turnOrder]
          | chooseReplacement _ _ _ _ => rfl
          | chanceFirstPlayer | revealLoadouts | chanceShuffle _ | openingDraws | draw _ _
          | beginTurn | startPhaseWork _ | actionPhaseStart _ | playPayCost _ _ _ _ _
          | payRandomDiscard _ _ _ _ _
          | resolveStack | finishResolve _ | combatStep _ _ | gameStateProcess | run _ _ _ _ _
          | chanceDie6 _ _ _ _ _ _ _ | optStep _ _ | endPhaseStart _ | endPhaseArsenal _ | returnPitch _
          | endTurnCleanup _ | flushTriggers => rfl
      · -- concedeActions
        unfold concedeActions
        rw [h.playerCount]
    · -- tournamentPlayerActions
      unfold tournamentPlayerActions
      rw [h.playerCount, h.config, h.tournament]
  · rfl

/-- **I10 Corollary (Pitch Deck-Bottom Order Secrecy)** (CR 4.4.3c):
Reordering ANY player `q`'s deck into any permutation `l` (including `p`'s own deck after Pitch
return!) leaves BOTH `view p s` AND `legalActionsFor p s` completely unchanged. -/
theorem reorder_deck_noninterference {s : GameState} (p q : PlayerId) {l : List ObjId}
    (hperm : l.Perm (s.zone (.player q .deck))) :
    view p (s.reorder (.player q .deck) l) = view p s ∧
    legalActionsFor p (s.reorder (.player q .deck) l) = legalActionsFor p s := by
  have hlen : l.length = (s.zone (.player q .deck)).length := hperm.length_eq
  have heq : HiddenEquiv p (s.reorder (.player q .deck) l) s :=
    { config := rfl, cards := rfl, objects := rfl, pools := rfl, heroLife := rfl,
      turn := rfl, active := rfl, pending := rfl, turnOrder := rfl, phase := rfl,
      result := rfl, combat := rfl, tournament := rfl,
      activatedThisTurn := rfl, activeEffects := rfl,
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
    congr 1
    apply List.map_congr_left
    intro z _
    congr 1
    unfold viewZone
    by_cases hzd : z = .player q .deck
    · subst hzd
      simp [Zone.isCountOnlyFor, GameState.reorder, GameState.zone_setZone_self, hlen]
    · simp only [GameState.reorder, GameState.zone_setZone_ne s hzd l]
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
      result := rfl, combat := rfl, tournament := rfl,
      activatedThisTurn := rfl, activeEffects := rfl,
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
