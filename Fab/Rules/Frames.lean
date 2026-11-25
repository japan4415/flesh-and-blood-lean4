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

/-- Test a printed restriction using the turn history and face-up banished cards. -/
def meetsPlayRestriction (s : GameState) (p : PlayerId) : PlayRestriction → Bool
  | .always => true
  | .banishedSixPowerThisTurn => s.banishedSixPowerThisTurn.contains p
  | .banishedBloodDebtAtLeast n => n ≤ bloodDebtCount s p
  | .playedBloodDebtAtLeast n => n ≤ s.playedBloodDebtThisTurn.getD p.n 0
  | .playedNonAttackActionThisTurn => s.playedNonAttackActionThisTurn.contains p

/-- Candidate objects for card play before checking permissions or timing. -/
def playCandidateIds (s : GameState) (p : PlayerId) : List ObjId :=
  (s.zone (.player p .hand) ++ s.zone (.player p .arsenal)) ++ s.zone (.player p .banished)

/-- Whether `id` is face-up and its printed permission allows play from banished. -/
def canPlayFromBanished (s : GameState) (p : PlayerId) (id : ObjId) (c : CardDef) : Bool :=
  match s.obj? id, c.front.playFromBanished with
  | some o, some req => !o.faceDown && meetsPlayRestriction s p req
  | _, _ => false

/-- Whether player `p` may announce playing card `id` while holding priority
(CR 5.1.1, 4.3, 3.2.2, 7.1, 7.4, 7.6).
- Instants: playable anytime on priority.
- Actions: own Action Phase, empty stack, ≥1 AP, and either combat chain closed or (for Attack
  Action cards) in Resolution Step to continue a combat chain.
- Attack Reactions: Reaction Step as the attacking player (CR 7.4).
- Defense Reactions: Reaction Step as the defending player, respecting Dominate from hand (CR 7.4, 8.3.4). -/
def canPlayCard (s : GameState) (p : PlayerId) (id : ObjId) : Bool :=
  let fromHand := id ∈ s.zone (.player p .hand)
  let fromArsenal := id ∈ s.zone (.player p .arsenal)
  if id ∈ playCandidateIds s p then
    match s.cardDefOf? id with
    | none => false
    | some c =>
      if !c.isDeckCard || !meetsPlayRestriction s p c.front.playRestriction ||
          (!(fromHand || fromArsenal) && !canPlayFromBanished s p id c) then
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
          | some link => link.attacker == p
          | none => false
        | none => false
      else if c.front.hasType .defenseReaction then
        match s.combat with
        | some cc =>
          cc.step == .reaction &&
          match cc.activeLink? with
          | some link =>
            link.defender == p &&
            !(fromHand && linkHasKeyword s link .dominate && 1 ≤ link.defendedFromHandCount)
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

/-- Whether a resolving card enters the arena as a permanent. -/
def resolvesAsPermanent (s : GameState) (id : ObjId) : Bool :=
  (s.cardDefOf? id).any fun c =>
    c.front.hasSubtype .aura || c.front.hasSubtype .item ||
      c.front.hasSubtype .landmark || c.front.hasSubtype .ally

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

/-- Source of a resolving ability layer, or the card itself for an ordinary card layer. -/
def resolvingSource (s : GameState) (layerId : ObjId) : ObjId :=
  match (s.obj? layerId).map Object.kind with
  | some (ObjectKind.layer src _ _ _) => src
  | _ => layerId

/-- Collect targetless start-of-action-phase abilities controlled by the turn-player. -/
def startActionPhaseTriggers (s : GameState) (tp : PlayerId) : List PendingTrigger :=
  let sources := (allZones s.playerCount).flatMap fun z =>
    match z with
    | .player _ k => if k.isArena && k != .soul then s.zone z else []
    | _ => []
  let triggers : List PendingTrigger := sources.flatMap fun src =>
    match s.obj? src, s.objectFace? src with
    | some o, some face =>
      if o.controller == tp && !o.faceDown then
        face.abilities.zipIdx.filterMap fun (ability, idx) =>
          match ability with
          | .triggered .onStartOfActionPhase optional none cond ed =>
            if ed.targets.isEmpty && ed.modes.isEmpty && ed.extraCosts.isEmpty &&
                (cond.all (evalCondition s tp src false)) then
              some {
                id := 0
                source := src
                sourceLki := captureLki s src tp
                controller := tp
                abilityIdx := idx
                effect := if optional then .may ed.body .nop else ed.body }
            else none
          | _ => none
      else []
    | _, _ => []
  triggers.zipIdx.map fun (trig, idx) => { trig with id := s.nextTimestamp + idx }

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
      let srcKind := if fromArsenal then ZoneKind.arsenal
        else if id ∈ s.zone (.player p .hand) then .hand else .banished
      let srcZone := Zone.player p srcKind
      let snap := s.snapshot
      let cost := match s.cardDefOf? id with | some c => cardPlayCost c | none => {}
      let modes := match s.cardDefOf? id with | some c => cardModeCount c | none => 0
      let isAtkCard := match s.cardDefOf? id with
        | some c => c.front.hasType .action && c.front.hasSubtype .attack
        | none => false
      let rest' := if isAtkCard then dropPendingClose rest else rest
      match moveObj s id .stack .top false with
      | none => none
      | some (s1, layerId) =>
        let layerMeta := if srcKind == .banished then
          s1.layerMeta.insert layerId.n { controller := p, fromBanished := true }
          else s1.layerMeta
        let nextFrame :=
          if 0 < modes then
            Frame.chooseMode p layerId fromArsenal modes cost
          else
            Frame.playPayCost p layerId fromArsenal none cost
        some ({ s1 with layerMeta := layerMeta, playRollback := some snap, pending := nextFrame :: rest' },
              [.moved id layerId srcZone .stack])
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
          some ({ s1 with combat := cc', pending := .defendPick defender :: rest },
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
    if p = q ∧ idx < modeCount then
      some ({ s with pending := .playPayCost p layerId fromArsenal (some idx) cost :: rest }, [])
    else
      none
  | .chooseMode p _ _ _ _ :: rest, .player q, .cancelPlay =>
    if p = q then
      some (rollbackPlay s rest, [])
    else
      none
  | .choosePitch p layerId fromArsenal modeIdx cost :: rest, .player q, .pitchCard id =>
    if p = q ∧ canPitchCard s p id = true then
      match pitchOne s p id with
      | none => none
      | some (s1, _, es) =>
        some ({ s1 with pending := .playPayCost p layerId fromArsenal modeIdx cost :: rest }, es)
    else
      none
  | .choosePitch p _ _ _ _ :: rest, .player q, .cancelPlay =>
    if p = q then
      some (rollbackPlay s rest, [])
    else
      none
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
  | .chooseTriggerOrder p rem :: rest, .player q, .pickTrigger tid =>
    if p = q then
      match s.pendingTriggers.find? (fun t => t.id == tid && t.controller == p) with
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
              fromArsenal := false
              modeIdx := none
              goAgain := false
              triggerEffect := some trig.effect }
          let s2 := { s1 with
            pendingTriggers := remTrigs
            layerMeta := s1.layerMeta.insert lid.n info }
          let nextF := nextTriggerFrame s2 (p :: rem)
          some ({ s2 with pending := nextF ++ rest }, [])
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
    let s1 := s.setPool tp ((s.poolOf tp).addActionPoints 1)
    let triggers := startActionPhaseTriggers s1 tp
    let trigFrames := if triggers.isEmpty then [] else [.flushTriggers]
    some ({ s1 with
      phase := .actionPhase
      pendingTriggers := s1.pendingTriggers ++ triggers
      nextTimestamp := s1.nextTimestamp + triggers.length
      pending := trigFrames ++ [.priority tp 0] ++ rest }, [])
  | .playPayCost p layerId fromArsenal modeIdx cost :: rest =>
    match spendAssetCost s p cost with
    | some s1 =>
      let card := s1.cardDefOf? layerId
      let hasGoAgain := card.any fun c => c.front.keywords.contains .goAgain && !c.front.hasSubtype .attack
      let playedBloodDebt := if card.any (fun c => c.front.keywords.contains .bloodDebt) then
        s1.playedBloodDebtThisTurn.insert p.n (s1.playedBloodDebtThisTurn.getD p.n 0 + 1)
        else s1.playedBloodDebtThisTurn
      let playedNonAttackAction := if card.any (fun c => c.front.hasType .action && !c.front.hasSubtype .attack) &&
          !s1.playedNonAttackActionThisTurn.contains p then
        p :: s1.playedNonAttackActionThisTurn
        else s1.playedNonAttackActionThisTurn
      let info : LayerInfo :=
        { controller := p
          fromArsenal := fromArsenal
          modeIdx := modeIdx
          goAgain := hasGoAgain
          fromBanished := (s1.layerMeta.getD layerId.n { controller := p }).fromBanished }
      some ({ s1 with
                layerMeta := s1.layerMeta.insert layerId.n info
                playedBloodDebtThisTurn := playedBloodDebt
                playedNonAttackActionThisTurn := playedNonAttackAction
                playRollback := none
                pending := .priority p 0 :: rest },
            [])
    | none =>
      if canPitchForCost s p cost then
        some ({ s with pending := .choosePitch p layerId fromArsenal modeIdx cost :: rest }, [])
      else
        some (rollbackPlay s rest, [])
  | .resolveStack :: rest =>
    match s.zone .stack with
    | topId :: _ =>
      if isAttackLayer s topId then
        some ({ s with pending := .combatStep .attack topId :: rest }, [])
      else
        let info := s.layerMeta.getD topId.n
          { controller := s.active.getD ⟨0⟩ }
        let eff :=
          match info.triggerEffect with
          | some teff => teff
          | none =>
            match s.cardDefOf? topId with
            | some c => cardResolveEffect c info.modeIdx
            | none => .nop
        some ({ s with
                  pending := .run info.controller (resolvingSource s topId) info.fromArsenal [] [eff] ::
                    .finishResolve topId :: rest },
              [])
    | [] =>
      let tp := s.active.getD ⟨0⟩
      some ({ s with pending := .gameStateProcess :: .priority tp 0 :: rest }, [])
  | .finishResolve layerId :: rest =>
    let info := s.layerMeta.getD layerId.n { controller := s.active.getD ⟨0⟩ }
    let s1 :=
      if info.goAgain then
        s.setPool info.controller ((s.poolOf info.controller).addActionPoints 1)
      else
        s
    let isDefReact :=
      match s1.cardDefOf? layerId with
      | some c => c.front.hasType .defenseReaction && s1.combat.isSome
      | none => false
    let (s2, es) :=
      if layerId ∈ s1.zone .stack then
        if isDefReact then
          match moveObj s1 layerId .combatChain .top false with
          | some (sMoved, id') =>
            let cc' := sMoved.combat.map fun cc => cc.updateActiveLink fun l =>
              { l with
                defending := l.defending ++ [id']
                defendedFromHandCount := l.defendedFromHandCount +
                  (if !info.fromArsenal && !info.fromBanished then 1 else 0) }
            ({ sMoved with combat := cc' }, [.moved layerId id' .stack .combatChain])
          | none => (s1, [])
        else
          match s1.obj? layerId with
          | some o =>
            match o.kind with
            | .layer _ _ _ _ => (removeNonPhysObj s1 layerId, [])
            | _ =>
              let dst := if resolvesAsPermanent s1 layerId then Zone.player info.controller .permanent
                         else Zone.player o.owner .graveyard
              match moveObj s1 layerId dst .top false with
              | some (sMoved, id') => (sMoved, [.moved layerId id' .stack dst])
              | none => (s1, [])
          | none => (s1, [])
      else
        (s1, [])
    let s3 := gspRun { s2 with layerMeta := s2.layerMeta.erase layerId.n }
    let tp := s3.active.getD ⟨0⟩
    some ({ s3 with pending := .priority tp 0 :: rest }, es)
  | .combatStep .layer _ :: rest =>
    some ({ s with pending := rest }, [])
  | .combatStep .attack layerId :: rest =>
    let info := s.layerMeta.getD layerId.n { controller := s.active.getD ⟨0⟩ }
    let eff :=
      match s.cardDefOf? layerId with
      | some c => cardResolveEffect c info.modeIdx
      | none => .nop
    let (s1, atkId, es) := enterAttackStep s layerId info.controller
    let tp := s1.active.getD ⟨0⟩
    let effFrames :=
      if eff == .nop then [] else [.run info.controller atkId info.fromArsenal [] [eff]]
    some ({ s1 with
              pending := effFrames ++ [.gameStateProcess, .priority tp 0, .combatStep .defend atkId] ++ rest },
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
        let atkP := linkAttackPower s link
        let totD := linkTotalDefense s link
        let rawDmg := calcCombatDamage atkP totD
        let (s2, es) := applyDamageWithPrevention s link.defender .physical rawDmg
        let finalDmg :=
          match es.reverse.find? fun | .damageDealt _ .physical _ => true | _ => false with
          | some (.damageDealt _ _ d) => d
          | _ => 0
        let isHit := didCombatHit finalDmg
        let cc' := { cc with step := .damage }.updateActiveLink fun l =>
          { l with hit := isHit, damageDealt := finalDmg }
        let s3 := gspRun { s2 with combat := some cc' }
        some ({ s3 with pending := .priority tp 0 :: .combatStep .resolution atkId :: rest }, es)
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
    some (interpRunStep s ctrl src fromArsenal env todo rest)
  | .optStep _ 0 :: rest =>
    some ({ s with pending := rest }, [])
  | .optStep p (n + 1) :: rest =>
    match s.zone (.player p .deck) with
    | topId :: _ =>
      some ({ s with pending := .chooseOpt p topId :: .optStep p n :: rest }, [])
    | [] =>
      some ({ s with pending := rest }, [])
  | .endPhaseStart tp :: rest =>
    let (sBd, esBd) := applyBloodDebt s tp
    let (fired, kept) := sBd.delayedTriggers.partition fun dt => dt.watchPhase == .endPhase
    let newTrigs := fired.map fun dt =>
      { id := dt.id
        source := dt.source
        sourceLki := captureLki sBd dt.source dt.controller
        controller := dt.controller
        abilityIdx := 0
        effect := dt.effect : PendingTrigger }
    let s1 :=
      if fired.isEmpty then sBd
      else { sBd with
        delayedTriggers := kept
        pendingTriggers := sBd.pendingTriggers ++ newTrigs }
    let trigFrames := if fired.isEmpty then [] else [.flushTriggers]
    let pitchReturns := s1.turnOrder.map Frame.returnPitch
    let arsenalFrames :=
      if (s1.zone (.player tp .arsenal)).isEmpty && !(s1.zone (.player tp .hand)).isEmpty then
        [.chooseArsenal tp]
      else
        []
    some ({ s1 with
              phase := .endPhase
              pending := trigFrames ++ arsenalFrames ++ pitchReturns ++ [.endTurnCleanup tp] ++ rest },
          esBd)
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
      playedBloodDebtThisTurn := ∅
      playedNonAttackActionThisTurn := []
      activatedThisTurn := [] }).expireEffects .thisTurn
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
