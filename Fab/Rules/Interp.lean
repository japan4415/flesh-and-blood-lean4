module

public import Fab.Rules.Move
public import Fab.Rules.Reorder
public import Fab.Rules.Add
public import Fab.Rules.Objects
public import Fab.Rules.Actions.Banish
public import Fab.Rules.Actions.Discard

/-!
# Effect IR 1-step interpreter and L4 invariants

Executes one step of a `Frame.run` continuation over any deeply embedded `Effect` (CR 1.7, 6.0).
Every `Effect` and `Prim` is total: impossible instructions are skipped (CR 1.0.1b) rather than
producing `RuleError.internal`), and every step is proved to preserve `WF`, `OwnerOk`, and
`physIds` (L4), as well as forcing an explicit `chooseMay` decision on `Effect.may` (I18).
-/

@[expose] public section

namespace Fab

/-- Convert a monomorphic `EffectList` to a standard `List Effect`. -/
def EffectList.toList : EffectList → List Effect
  | .nil => []
  | .cons h t => h :: t.toList

/-- Select the matching branch for a 6-sided die result `roll` (defaulting to `.nop`). -/
def DieBranchList.select (roll : Nat) : DieBranchList → Effect
  | .nil => .nop
  | .cons lo hi body tail =>
    if lo ≤ roll && roll ≤ hi then body else tail.select roll

/-- Resolve a `PlayerRef` to a concrete `PlayerId` (defaults to `ctrl` when unavailable). -/
def evalPlayerRef (s : GameState) (ctrl : PlayerId) : PlayerRef → PlayerId
  | .controller => ctrl
  | .opposingHero =>
    match (allPlayers s.playerCount).find? (· != ctrl) with
    | some opp => opp
    | none => ctrl
  | .attackingHero => s.active.getD ctrl
  | .defendingHero =>
    let atk := s.active.getD ctrl
    match (allPlayers s.playerCount).find? (· != atk) with
    | some defP => defP
    | none => ctrl
  | .turnPlayer => s.active.getD ctrl
  | .ownerOfSlot _ => ctrl
  | .seated p => p

/-- Look up a bound integer variable in `env` (defaulting to 0 if unbound). -/
def lookupVar (env : List (VarId × Int)) (v : VarId) : Int :=
  match env.find? (fun p => p.1 == v) with
  | some (_, val) => val
  | none => 0

/-- Read source counters from the live object or a matching resolving layer's snapshot. -/
def effectSourceCounterCount (s : GameState) (source : ObjId) (kind : CounterKind) : Nat :=
  match s.obj? source with
  | some obj => obj.counterCount kind
  | none =>
    ((s.zone .stack).head?.bind s.obj?).map (fun layer =>
      match layer.kind with
      | .layer original (some lki) _ _ => if original == source then lki.counterCount kind else 0
      | _ => 0) |>.getD 0

/-- Evaluate a `NumExpr` in the current state and lexical environment. -/
def evalNumExpr (s : GameState) (ctrl : PlayerId) (env : List (VarId × Int))
    (value : NumExpr) (source : Option ObjId := none) : Int :=
  match value with
  | .const n => n
  | .xValue =>
    Int.ofNat ((source.bind fun id => (s.layerMeta.get? id.n).bind (·.variableResources)).getD 0)
  | .sourceCounterCount kind =>
    Int.ofNat ((source.map (fun id => effectSourceCounterCount s id kind)).getD 0)
  | .varVal v => lookupVar env v
  | .handCount p =>
    let target := evalPlayerRef s ctrl p
    Int.ofNat (s.zone (.player target .hand)).length
  | .chainHits =>
    match s.combat with
    | some cc => Int.ofNat (cc.links.filter (·.hit)).length
    | none => 0
  | .halfRoundDown v =>
    let raw := lookupVar env v
    if raw ≤ 0 then 0 else Int.ofNat (raw.toNat / 2)
  | .soulCount p =>
    let target := evalPlayerRef s ctrl p
    Int.ofNat (s.zone (.player target .soul)).length
  | .banishedCount p =>
    let target := evalPlayerRef s ctrl p
    Int.ofNat (s.zone (.player target .banished)).length
  | .arcaneDamageDealtTo p => Int.ofNat (s.arcaneDamageDealtTo ctrl (evalPlayerRef s ctrl p))
  | .sourceArcaneDamage => Int.ofNat ((source.map s.arcaneDamageFrom).getD 0)

/-- The required single-attack target of a card or its chosen mode (CR 5.1.4a). -/
def singleAttackTargetSpec (card : CardDef) (modeIdx : Option Nat) : Option TargetSpec := do
  let effect ← card.front.playEffect
  let targets := (modeIdx.bind (fun idx => effect.modes[idx]?)).map (·.targets) |>.getD effect.targets
  match targets with
  | [spec@{ kind := .attackAction, minCount := 1, maxCount := some 1, .. }]
  | [spec@{ kind := .weaponAttack, minCount := 1, maxCount := some 1, .. }] => some spec
  | _ => none

/-- The only attack a reaction can target on the active link, if it matches the slot (CR 7.4). -/
def matchingActiveAttack (s : GameState) (link : ChainLink) (spec : TargetSpec) : Option ObjId := do
  let attack ← link.attack
  if !(s.zone .combatChain).contains attack then none else
    match spec.kind, link.attackSource with
    | .attackAction, none =>
      let face ← s.objectFace? attack
      if face.hasType .action && face.hasSubtype .attack && cardFaceMatches spec.filter face then
        some attack else none
    | .weaponAttack, some source =>
      let face ← s.objectFace? source
      if face.hasType .weapon && cardFaceMatches spec.filter face then some attack else none
    | _, _ => none

/-- Map an IR `ZoneRef` for player `p` to a concrete `Zone`. -/
def zoneOfRef (p : PlayerId) : ZoneRef → Option Zone
  | .hand => some (.player p .hand)
  | .deck => some (.player p .deck)
  | .arsenal => some (.player p .arsenal)
  | .pitch => some (.player p .pitch)
  | .graveyard => some (.player p .graveyard)
  | .banished => some (.player p .banished)
  | .arena => some (.player p .permanent)
  | .weapon => some (.player p .weapon)
  | .combatChain => some .combatChain
  | .soul => some (.player p .soul)
  | .inventory => some (.player p .inventory)
  | .equipment => none
  | .any => none

/-- Count objects matching `f` in player `p`'s zone `zr`. -/
def countMatchingInZone (s : GameState) (p : PlayerId) (zr : ZoneRef) (f : CardFilter) : Nat :=
  match zoneOfRef p zr with
  | none => 0
  | some z =>
    ((s.zone z).filter fun id =>
      match s.objectFace? id with
      | some face => cardFaceMatches f face
      | none => false).length

/-- Report the transition to zero counters on a public arena object (CR 6.6.5c). -/
def counterRemovalEvents (s : GameState) (source : ObjId) (kind : CounterKind) (amount : Nat) :
    List Event :=
  if (s.locate source).any Zone.isArena && (s.obj? source).any (fun obj =>
    let current := obj.counterCount kind
    !obj.faceDown && current > 0 && current ≤ amount) then
    [.countersEmptied source kind]
  else []

/-- Count live defenders whose current type does not include Equipment (CR 7.0.5). -/
def nonEquipmentDefenderCount (s : GameState) (link : ChainLink) : Nat :=
  link.defending.countP fun id =>
    s.locate id == some .combatChain && !(s.characteristics id).any (·.types.contains .equipment)

/-- Whether a weapon the player currently controls has hit this turn. -/
def hasWeaponHitThisTurn (s : GameState) (p : PlayerId) : Bool :=
  s.weaponHitsThisTurn.any fun weapon =>
    (s.characteristics weapon).any fun c => c.controller == p && c.types.contains .weapon

/-- Evaluate an IR condition in the current game state. -/
def evalCondition (s : GameState) (ctrl : PlayerId) (src : ObjId) (fromArsenal : Bool) :
    Condition → Bool
  | .always => true
  | .playedFromArsenal => fromArsenal
  | .zoneCountGe p zr f n =>
    let target := evalPlayerRef s ctrl p
    n ≤ countMatchingInZone s target zr f
  | .zoneEmpty p zr =>
    let target := evalPlayerRef s ctrl p
    match zoneOfRef target zr with
    | some z => (s.zone z).isEmpty
    | none => false
  | .nonAttackActionPlayedThisTurn => s.nonAttackActionsThisTurn.contains ctrl
  | .sourceDealtArcaneDamage => decide (0 < s.arcaneDamageFrom src)
  | .lessLifeThanOpponent =>
    (allPlayers s.playerCount).any fun opp => opp != ctrl && s.lifeOf ctrl < s.lifeOf opp
  | .sourceInArena =>
    (s.locate src).any fun
      | .player _ .soul => false
      | zone => zone.isArena
  | .sourceCounterLt k n =>
    match s.obj? src with
    | some o => o.counterCount k < n
    | none => false
  | .and_ a b => evalCondition s ctrl src fromArsenal a && evalCondition s ctrl src fromArsenal b
  | .or_ a b => evalCondition s ctrl src fromArsenal a || evalCondition s ctrl src fromArsenal b
  | .not_ c => !evalCondition s ctrl src fromArsenal c
  -- Combat chain conditions read the active/previous ChainLink (CR 3.5.4, 8.3.6, 8.3.8)
  | .prevChainLinkNamed name =>
    match s.combat.bind CombatChain.prevLink? with
    | some prev => prev.attackLki.name == name
    | none => false
  | .chainLinkAtLeast minimum =>
    (s.combat.bind CombatChain.activeLink?).any fun link =>
      link.attack == some src && decide (minimum ≤ link.linkId.n)
  | .defendedFromHandThisLink =>
    match s.combat.bind CombatChain.activeLink? with
    | some cur => decide (0 < cur.defendedFromHandCount)
    | none => false
  | .defendedByFewerNonEquip n =>
    match s.combat.bind CombatChain.activeLink? with
    | some cur => decide (nonEquipmentDefenderCount s cur < n)
    | none => false
  | .additionalCostPaid =>
    match s.layerMeta.get? src.n with
    | some info => info.additionalCostPaid
    | none =>
      (s.combat.bind CombatChain.activeLink?).any fun link =>
        link.attack == some src && link.additionalCostPaid
  | .lastDiscardedMatches filter =>
    let discarded := match s.layerMeta.get? src.n with
      | some info => info.discardedForPlay
      | none =>
        (s.combat.bind CombatChain.activeLink?).bind fun link =>
          if link.attack == some src then link.discardedForPlay else none
    discarded.any (cardFaceMatches filter)
  | .weaponHitThisTurn => hasWeaponHitThisTurn s ctrl
  | .defendingWeaponAttack =>
    match s.combat.bind CombatChain.activeLink? with
    | some cur =>
      let source := cur.attackSource.or cur.attack
      let types := (source.bind s.characteristics).map (·.types) |>.getD cur.attackLki.types
      types.contains .weapon
    | none => false
  | .sourceNotHitThisTurn => !s.weaponHitsThisTurn.contains src
  | .chargedThisTurn => s.chargedThisTurn.contains ctrl
  | .boostedThisTurn n => decide (n ≤ s.boostsThisTurn.count ctrl)
  | .banishedSixPowerThisTurn => s.banishedSixPowerThisTurn.contains ctrl
  | .playedFromBanished =>
    match s.locate src with
    | some (.player _ .banished) => true
    | _ => false

/-- Resolve an `ObjRef` to a concrete `ObjId` if available. -/
def evalObjRef (src : ObjId) : ObjRef → Option ObjId
  | .self_ => some src
  | .declared id => some id
  | _ => none

/-- Create `n` copies of token `tokId` in `p`'s permanent zone (CR 8.5.2). -/
def createTokens (s : GameState) (p : PlayerId) (tokId : CardId) : Nat → GameState
  | 0 => s
  | n + 1 =>
    let tok : Object :=
      { kind := .token tokId
        owner := p
        controller := p
        timestamp := ⟨s.nextTimestamp⟩ }
    match addObject s (.player p .permanent) tok .top with
    | some (s1, _) => createTokens s1 p tokId n
    | none => s

/-- Apply one addition per active effect to a nonempty token creation batch (CR 6.4). -/
def tokenCreationCount (s : GameState) (p : PlayerId) (token : CardId) (amount : Nat) : Nat :=
  if amount == 0 then 0 else
    s.activeEffects.foldl (fun total effect =>
      match effect.target, effect.op with
      | .player player, .addTokenCreation id extra =>
        if player == p && id == token && !effect.waitsForNextTurn then total + extra else total
      | _, _ => total) amount

/-- `createTokens` preserves `WF`. -/
theorem createTokens_wf (p : PlayerId) (tokId : CardId) :
    ∀ (n : Nat) {s : GameState}, s.WF → (createTokens s p tokId n).WF
  | 0, _, hwf => hwf
  | n + 1, s, hwf => by
    unfold createTokens
    dsimp only
    split
    · rename_i s1 id hm
      exact createTokens_wf p tokId n (addObject_wf hwf hm)
    · exact hwf

/-- `createTokens` preserves `OwnerOk`. -/
theorem createTokens_ownerOk (p : PlayerId) (tokId : CardId) :
    ∀ (n : Nat) {s : GameState}, s.WF → s.OwnerOk → (createTokens s p tokId n).OwnerOk
  | 0, _, _, hok => hok
  | n + 1, s, hwf, hok => by
    unfold createTokens
    dsimp only
    split
    · rename_i s1 id hm
      exact createTokens_ownerOk p tokId n (addObject_wf hwf hm) (addObject_ownerOk hwf hok hm)
    · exact hok

/-- `createTokens` preserves `physIds` (tokens have no `PhysId`: I1). -/
theorem createTokens_physIds (p : PlayerId) (tokId : CardId) :
    ∀ (n : Nat) {s : GameState}, s.WF → (createTokens s p tokId n).physIds.Perm s.physIds
  | 0, _, _ => List.Perm.refl _
  | n + 1, s, hwf => by
    unfold createTokens
    dsimp only
    split
    · rename_i s1 id hm
      have hp1 : s1.physIds.Perm s.physIds := addObject_physIds hwf rfl hm
      have hp2 := createTokens_physIds p tokId n (addObject_wf hwf hm)
      exact hp2.trans hp1
    · exact List.Perm.refl _

/-- `createTokens` preserves `config` and `playRollback`. -/
theorem createTokens_meta (p : PlayerId) (tokId : CardId) :
    ∀ (n : Nat) (s : GameState),
      (createTokens s p tokId n).config = s.config ∧
      (createTokens s p tokId n).playRollback = s.playRollback
  | 0, _ => ⟨rfl, rfl⟩
  | n + 1, s => by
    unfold createTokens
    dsimp only
    split
    · rename_i s1 id hm
      have h1 : s1.config = s.config ∧ s1.playRollback = s.playRollback := by
        unfold addObject at hm
        split at hm
        · dsimp only at hm
          simp only [Option.some.injEq, Prod.mk.injEq] at hm
          obtain ⟨rfl, rfl⟩ := hm
          exact ⟨rfl, rfl⟩
        · cases hm
      have h2 := createTokens_meta p tokId n s1
      exact ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩
    · exact ⟨rfl, rfl⟩

/-- Update a single object `target` in `s.objects` via `f` (if present). -/
def updateSingleObject (s : GameState) (target : ObjId) (f : Object → Object) : GameState :=
  match s.objects[target.n]? with
  | none => s
  | some o => { s with objects := s.objects.insert target.n (f o) }

/-- `updateSingleObject` preserves `WF`. -/
theorem updateSingleObject_wf {s : GameState} (hwf : s.WF) (target : ObjId) (f : Object → Object) :
    (updateSingleObject s target f).WF := by
  unfold updateSingleObject
  cases hg : s.objects[target.n]? with
  | none => exact hwf
  | some o =>
    have hin : target.n ∈ s.objects := Std.ExtTreeMap.mem_iff_isSome_getElem?.mpr (by rw [hg]; rfl)
    refine GameState.WF.congr_mem hwf rfl (fun k => ?_) rfl rfl
    simp only [Std.ExtTreeMap.mem_insert, Nat.compare_eq_eq]
    constructor
    · rintro (rfl | hk); exact hin; exact hk
    · intro hk; exact Or.inr hk

/-- `updateSingleObject` preserves `OwnerOk` when `f` preserves `owner`. -/
theorem updateSingleObject_ownerOk {s : GameState} (hok : s.OwnerOk) (target : ObjId)
    {f : Object → Object} (hown : ∀ o, (f o).owner = o.owner) :
    (updateSingleObject s target f).OwnerOk := by
  unfold updateSingleObject
  cases hg : s.objects[target.n]? with
  | none => exact hok
  | some o =>
    refine ⟨fun p k hk id hid o' hobj => ?_⟩
    change id ∈ s.zone (.player p k) at hid
    change (s.objects.insert target.n (f o))[id.n]? = some o' at hobj
    by_cases he : target.n = id.n
    · rw [← he] at hobj
      simp only [Std.ExtTreeMap.getElem?_insert, Nat.compare_eq_eq, ↓reduceIte,
        Option.some.injEq] at hobj
      subst hobj
      rw [hown o]
      have hg' : s.obj? id = some o := by
        unfold GameState.obj?
        rw [← he]
        exact hg
      exact hok.owner p k hk id hid o hg'
    · simp only [Std.ExtTreeMap.getElem?_insert, Nat.compare_eq_eq, he, ↓reduceIte] at hobj
      exact hok.owner p k hk id hid o' hobj

/-- `updateSingleObject` preserves `physIds` when `f` preserves `kind`. -/
theorem updateSingleObject_physIds (s : GameState) (target : ObjId)
    {f : Object → Object} (hkind : ∀ o, (f o).kind = o.kind) :
    (updateSingleObject s target f).physIds = s.physIds := by
  unfold updateSingleObject
  cases hg : s.objects[target.n]? with
  | none => rfl
  | some o =>
    unfold GameState.physIds
    have hids : ({ s with objects := s.objects.insert target.n (f o) }).zoneIds = s.zoneIds := rfl
    rw [hids]
    apply filterMap_congr_mem
    intro id _
    simp only [GameState.obj?]
    by_cases he : target.n = id.n
    · rw [← he]
      simp [hg, hkind o]
    · simp [Std.ExtTreeMap.getElem?_insert, he]

/-- `updateSingleObject` preserves `config` and `playRollback`. -/
theorem updateSingleObject_meta (s : GameState) (target : ObjId) (f : Object → Object) :
    (updateSingleObject s target f).config = s.config ∧
    (updateSingleObject s target f).playRollback = s.playRollback := by
  unfold updateSingleObject
  cases s.objects[target.n]? <;> exact ⟨rfl, rfl⟩

/-- Helper: `moveObj` preserves `turn`, `tournament`, and `result`. -/
theorem moveObj_ttr_core {s s' : GameState} {id id' : ObjId} {dst : Zone} {pos : Pos}
    {fd : Bool} (h : moveObj s id dst pos fd = some (s', id')) :
    s'.turn = s.turn ∧ s'.tournament = s.tournament ∧ s'.result = s.result := by
  unfold moveObj at h
  split at h
  · dsimp only at h
    split at h
    · cases h
    · split at h <;>
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨rfl, rfl, rfl⟩
  · cases h

/-- Helper: `checkHeroDefeat` preserves `config` and `playRollback`. -/
theorem checkHeroDefeat_config_rollback (s : GameState) :
    (checkHeroDefeat s).config = s.config ∧ (checkHeroDefeat s).playRollback = s.playRollback := by
  unfold checkHeroDefeat
  split
  · exact ⟨rfl, rfl⟩
  · split <;> exact ⟨rfl, rfl⟩

/-- Helper: `checkHeroDefeat` preserves `turn`, `tournament`, and never clears a set `result`. -/
theorem checkHeroDefeat_ttr_core (s : GameState) :
    (checkHeroDefeat s).turn = s.turn ∧ (checkHeroDefeat s).tournament = s.tournament ∧
    ((checkHeroDefeat s).result = none → s.result = none) := by
  unfold checkHeroDefeat
  split
  · exact ⟨rfl, rfl, id⟩
  · cases livingPlayers s with
    | nil => exact ⟨rfl, rfl, fun h => by cases h⟩
    | cons _ ws =>
      cases ws with
      | nil => exact ⟨rfl, rfl, fun h => by cases h⟩
      | cons _ _ => exact ⟨rfl, rfl, id⟩

/-- Move a list of objects to `dst` at `pos` with facing `fd`, skipping any object that cannot be
moved (CR 1.0.1b). -/
def moveManyObjs (s : GameState) (ids : List ObjId) (dst : Zone) (pos : Pos) (fd : Bool) :
    GameState × List Event :=
  match ids with
  | [] => (s, [])
  | id :: rest =>
    let (s1, es1) :=
      match s.locate id with
      | some srcZ =>
        match moveRuleObj s id dst pos fd with
        | some (sm, id') => (sm, ruleMoveEvents s id id' srcZ dst)
        | none => (s, [])
      | none => (s, [])
    let (s2, es2) := moveManyObjs s1 rest dst pos fd
    (s2, es1 ++ es2)

/-- `moveManyObjs` preserves `WF`, `OwnerOk`, `physIds` (I1), `config`, and `playRollback`. -/
theorem moveManyObjs_inv (dst : Zone) (pos : Pos) (fd : Bool) :
    ∀ (ids : List ObjId) {s : GameState}, s.WF → s.OwnerOk →
      (moveManyObjs s ids dst pos fd).1.WF ∧
      (moveManyObjs s ids dst pos fd).1.OwnerOk ∧
      (moveManyObjs s ids dst pos fd).1.physIds.Perm s.physIds ∧
      (moveManyObjs s ids dst pos fd).1.config = s.config ∧
      (moveManyObjs s ids dst pos fd).1.playRollback = s.playRollback
  | [], _, hwf, hok => ⟨hwf, hok, List.Perm.refl _, rfl, rfl⟩
  | id :: rest, s, hwf, hok => by
    unfold moveManyObjs
    have h1 : let p1 := match s.locate id with
        | some srcZ =>
          match moveRuleObj s id dst pos fd with
          | some (sm, id') => (sm, ruleMoveEvents s id id' srcZ dst)
          | none => (s, [])
        | none => (s, [])
        p1.1.WF ∧ p1.1.OwnerOk ∧ p1.1.physIds.Perm s.physIds ∧
        p1.1.config = s.config ∧ p1.1.playRollback = s.playRollback := by
      cases s.locate id with
      | none => exact ⟨hwf, hok, List.Perm.refl _, rfl, rfl⟩
      | some srcZ =>
        dsimp only
        cases hm : moveRuleObj s id dst pos fd with
        | none => exact ⟨hwf, hok, List.Perm.refl _, rfl, rfl⟩
        | some res =>
          have hmeta := moveObj_config_rollback hm
          exact ⟨moveObj_wf hwf hm, moveObj_ownerOk hwf hok hm,
                 moveObj_physIds hwf hm, hmeta.1, hmeta.2⟩
    obtain ⟨hwf1, hok1, hp1, hc1, hr1⟩ := h1
    obtain ⟨hwf2, hok2, hp2, hc2, hr2⟩ := moveManyObjs_inv dst pos fd rest hwf1 hok1
    exact ⟨hwf2, hok2, hp2.trans hp1, hc2.trans hc1, hr2.trans hr1⟩

/-- `moveManyObjs` preserves `turn`, `tournament`, and `result`. -/
theorem moveManyObjs_ttr (dst : Zone) (pos : Pos) (fd : Bool) :
    ∀ (ids : List ObjId) (s : GameState),
      (moveManyObjs s ids dst pos fd).1.turn = s.turn ∧
      (moveManyObjs s ids dst pos fd).1.tournament = s.tournament ∧
      (moveManyObjs s ids dst pos fd).1.result = s.result
  | [], _ => ⟨rfl, rfl, rfl⟩
  | id :: rest, s => by
    unfold moveManyObjs
    let p1 := match s.locate id with
      | some srcZ =>
        match moveRuleObj s id dst pos fd with
        | some (sm, id') => (sm, ruleMoveEvents s id id' srcZ dst)
        | none => (s, [])
      | none => (s, [])
    have h1 : p1.1.turn = s.turn ∧ p1.1.tournament = s.tournament ∧ p1.1.result = s.result := by
      dsimp only [p1]
      cases s.locate id with
      | none => exact ⟨rfl, rfl, rfl⟩
      | some _ =>
        dsimp only
        cases hm : moveRuleObj s id dst pos fd with
        | none => exact ⟨rfl, rfl, rfl⟩
        | some _ => exact moveObj_ttr_core hm
    have h2 := moveManyObjs_ttr dst pos fd rest p1.1
    exact ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.trans h1.2.2⟩

/-- Discard a list of cards from `p`'s hand via `discardOne` (CR 3.0, 3.10). -/
def discardManyObjs (s : GameState) (p : PlayerId) : List ObjId → GameState × List Event
  | [] => (s, [])
  | id :: rest =>
    let (s1, es1) :=
      match discardOne s p id with
      | some (sd, _, es) => (sd, es)
      | none => (s, [])
    let (s2, es2) := discardManyObjs s1 p rest
    (s2, es1 ++ es2)

/-- `discardManyObjs` preserves `WF`, `OwnerOk`, `physIds` (I1), `config`, and `playRollback`. -/
theorem discardManyObjs_inv (p : PlayerId) :
    ∀ (ids : List ObjId) {s : GameState}, s.WF → s.OwnerOk →
      (discardManyObjs s p ids).1.WF ∧
      (discardManyObjs s p ids).1.OwnerOk ∧
      (discardManyObjs s p ids).1.physIds.Perm s.physIds ∧
      (discardManyObjs s p ids).1.config = s.config ∧
      (discardManyObjs s p ids).1.playRollback = s.playRollback
  | [], _, hwf, hok => ⟨hwf, hok, List.Perm.refl _, rfl, rfl⟩
  | id :: rest, s, hwf, hok => by
    unfold discardManyObjs
    have h1 : let p1 := match discardOne s p id with
        | some (sd, _, es) => (sd, es)
        | none => (s, [])
        p1.1.WF ∧ p1.1.OwnerOk ∧ p1.1.physIds.Perm s.physIds ∧
        p1.1.config = s.config ∧ p1.1.playRollback = s.playRollback := by
      cases hd : discardOne s p id with
      | none => exact ⟨hwf, hok, List.Perm.refl _, rfl, rfl⟩
      | some res =>
        obtain ⟨sd, idd, esd⟩ := res
        dsimp only
        have hmeta : sd.config = s.config ∧ sd.playRollback = s.playRollback := by
          unfold discardOne at hd
          split at hd
          · cases hm : moveRuleObj s id (.player p .graveyard) .top false with
            | none => rw [hm] at hd; cases hd
            | some rm =>
              obtain ⟨sm, idm⟩ := rm
              rw [hm] at hd; simp only [Option.some.injEq, Prod.mk.injEq] at hd
              obtain ⟨rfl, rfl, rfl⟩ := hd
              exact moveObj_config_rollback hm
          · cases hd
        exact ⟨discardOne_wf hwf hd, discardOne_ownerOk hwf hok hd,
               discardOne_physIds hwf hd, hmeta.1, hmeta.2⟩
    obtain ⟨hwf1, hok1, hp1, hc1, hr1⟩ := h1
    obtain ⟨hwf2, hok2, hp2, hc2, hr2⟩ := discardManyObjs_inv p rest hwf1 hok1
    exact ⟨hwf2, hok2, hp2.trans hp1, hc2.trans hc1, hr2.trans hr1⟩

/-- `discardManyObjs` preserves `turn`, `tournament`, and `result`. -/
theorem discardManyObjs_ttr (p : PlayerId) :
    ∀ (ids : List ObjId) (s : GameState),
      (discardManyObjs s p ids).1.turn = s.turn ∧
      (discardManyObjs s p ids).1.tournament = s.tournament ∧
      (discardManyObjs s p ids).1.result = s.result
  | [], _ => ⟨rfl, rfl, rfl⟩
  | id :: rest, s => by
    unfold discardManyObjs
    let p1 := match discardOne s p id with
      | some (sd, _, es) => (sd, es)
      | none => (s, [])
    have h1 : p1.1.turn = s.turn ∧ p1.1.tournament = s.tournament ∧ p1.1.result = s.result := by
      dsimp only [p1]
      cases hd : discardOne s p id with
      | none => exact ⟨rfl, rfl, rfl⟩
      | some res =>
        obtain ⟨sd, idd, esd⟩ := res
        dsimp only
        unfold discardOne at hd
        split at hd
        · cases hm : moveRuleObj s id (.player p .graveyard) .top false with
          | none => rw [hm] at hd; cases hd
          | some rm =>
            obtain ⟨sm, idm⟩ := rm
            rw [hm] at hd; simp only [Option.some.injEq, Prod.mk.injEq] at hd
            obtain ⟨rfl, rfl, rfl⟩ := hd
            exact moveObj_ttr_core hm
        · cases hd
    have h2 := discardManyObjs_ttr p rest p1.1
    exact ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.trans h1.2.2⟩

/-- Banish a list of objects via `banishOne`, recording `p ∈ banishedSixPowerThisTurn` whenever a
card with printed power `≥ 6` is banished (CR 3.3). -/
def banishManyObjs (s : GameState) (p : PlayerId) (fd : Bool) :
    List ObjId → GameState × List Event
  | [] => (s, [])
  | id :: rest =>
    let isSix :=
      match s.objectFace? id with
      | some face =>
        match face.power with
        | some pw => decide (6 ≤ pw)
        | none => false
      | none => false
    let (s1, es1) :=
      match banishOne s id fd with
      | some (sb, _, es) =>
        let sb' :=
          if isSix && !(sb.banishedSixPowerThisTurn.contains p) then
            { sb with banishedSixPowerThisTurn := p :: sb.banishedSixPowerThisTurn }
          else
            sb
        (sb', es)
      | none => (s, [])
    let (s2, es2) := banishManyObjs s1 p fd rest
    (s2, es1 ++ es2)

/-- `banishManyObjs` preserves `WF`, `OwnerOk`, `physIds` (I1), `config`, and `playRollback`. -/
theorem banishManyObjs_inv (p : PlayerId) (fd : Bool) :
    ∀ (ids : List ObjId) {s : GameState}, s.WF → s.OwnerOk →
      (banishManyObjs s p fd ids).1.WF ∧
      (banishManyObjs s p fd ids).1.OwnerOk ∧
      (banishManyObjs s p fd ids).1.physIds.Perm s.physIds ∧
      (banishManyObjs s p fd ids).1.config = s.config ∧
      (banishManyObjs s p fd ids).1.playRollback = s.playRollback
  | [], _, hwf, hok => ⟨hwf, hok, List.Perm.refl _, rfl, rfl⟩
  | id :: rest, s, hwf, hok => by
    unfold banishManyObjs
    dsimp only
    let isSix :=
      match s.objectFace? id with
      | some face => match face.power with | some pw => decide (6 ≤ pw) | none => false
      | none => false
    have h1 : let p1 := match banishOne s id fd with
        | some (sb, _, es) =>
          let sb' :=
            if isSix && !(sb.banishedSixPowerThisTurn.contains p) then
              { sb with banishedSixPowerThisTurn := p :: sb.banishedSixPowerThisTurn }
            else sb
          (sb', es)
        | none => (s, [])
        p1.1.WF ∧ p1.1.OwnerOk ∧ p1.1.physIds.Perm s.physIds ∧
        p1.1.config = s.config ∧ p1.1.playRollback = s.playRollback := by
      cases hb : banishOne s id fd with
      | none => exact ⟨hwf, hok, List.Perm.refl _, rfl, rfl⟩
      | some res =>
        obtain ⟨sb, idb, esb⟩ := res
        dsimp only
        have hmeta : sb.config = s.config ∧ sb.playRollback = s.playRollback := by
          unfold banishOne at hb
          split at hb
          · rename_i src0 o0 _ _
            dsimp only at hb
            cases hm : moveObj s id (Zone.player o0.owner .banished) .top fd with
            | none => rw [hm] at hb; cases hb
            | some rm =>
              obtain ⟨sm, idm⟩ := rm
              rw [hm] at hb; simp only [Option.some.injEq, Prod.mk.injEq] at hb
              obtain ⟨rfl, rfl, rfl⟩ := hb
              exact moveObj_config_rollback hm
          · cases hb
        have hwf1 := banishOne_wf hwf hb
        have hok1 := banishOne_ownerOk hwf hok hb
        have hp1 := banishOne_physIds hwf hb
        cases (isSix && !sb.banishedSixPowerThisTurn.contains p) with
        | true =>
          exact ⟨GameState.WF.congr hwf1 rfl rfl rfl rfl,
                 GameState.OwnerOk.congr hok1 rfl rfl,
                 hp1, hmeta.1, hmeta.2⟩
        | false => exact ⟨hwf1, hok1, hp1, hmeta.1, hmeta.2⟩
    obtain ⟨hwf1, hok1, hp1, hc1, hr1⟩ := h1
    obtain ⟨hwf2, hok2, hp2, hc2, hr2⟩ := banishManyObjs_inv p fd rest hwf1 hok1
    exact ⟨hwf2, hok2, hp2.trans hp1, hc2.trans hc1, hr2.trans hr1⟩

/-- `banishManyObjs` preserves `turn`, `tournament`, and `result`. -/
theorem banishManyObjs_ttr (p : PlayerId) (fd : Bool) :
    ∀ (ids : List ObjId) (s : GameState),
      (banishManyObjs s p fd ids).1.turn = s.turn ∧
      (banishManyObjs s p fd ids).1.tournament = s.tournament ∧
      (banishManyObjs s p fd ids).1.result = s.result
  | [], _ => ⟨rfl, rfl, rfl⟩
  | id :: rest, s => by
    unfold banishManyObjs
    dsimp only
    let isSix :=
      match s.objectFace? id with
      | some face => match face.power with | some pw => decide (6 ≤ pw) | none => false
      | none => false
    let p1 := match banishOne s id fd with
      | some (sb, _, es) =>
        let sb' :=
          if isSix && !(sb.banishedSixPowerThisTurn.contains p) then
            { sb with banishedSixPowerThisTurn := p :: sb.banishedSixPowerThisTurn }
          else sb
        (sb', es)
      | none => (s, [])
    have h1 : p1.1.turn = s.turn ∧ p1.1.tournament = s.tournament ∧ p1.1.result = s.result := by
      dsimp only [p1]
      cases hb : banishOne s id fd with
      | none => exact ⟨rfl, rfl, rfl⟩
      | some res =>
        obtain ⟨sb, idb, esb⟩ := res
        dsimp only
        have httr : sb.turn = s.turn ∧ sb.tournament = s.tournament ∧ sb.result = s.result := by
          unfold banishOne at hb
          split at hb
          · rename_i src0 o0 _ _
            dsimp only at hb
            cases hm : moveObj s id (Zone.player o0.owner .banished) .top fd with
            | none => rw [hm] at hb; cases hb
            | some rm =>
              obtain ⟨sm, idm⟩ := rm
              rw [hm] at hb; simp only [Option.some.injEq, Prod.mk.injEq] at hb
              obtain ⟨rfl, rfl, rfl⟩ := hb
              exact moveObj_ttr_core hm
          · cases hb
        cases (isSix && !sb.banishedSixPowerThisTurn.contains p) <;> exact httr
    have h2 := banishManyObjs_ttr p fd rest p1.1
    exact ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.trans h1.2.2⟩

/-- Destroy a list of objects (removing non-physical tokens/proxies or moving physical cards to
owner's graveyard) (CR 8.5.5). -/
def destroyManyObjs (s : GameState) : List ObjId → GameState × List Event
  | [] => (s, [])
  | id :: rest =>
    let (s1, es1) :=
      match s.locate id, s.obj? id with
      | some srcZ, some o =>
        if o.kind.phys?.isNone then
          (removeNonPhysObj s id, [])
        else
          match moveRuleObj s id (.player o.owner .graveyard) .top false with
          | some (sm, id') => (sm, ruleMoveEvents s id id' srcZ (.player o.owner .graveyard))
          | none => (s, [])
      | _, _ => (s, [])
    let (s2, es2) := destroyManyObjs s1 rest
    (s2, es1 ++ es2)

/-- `destroyManyObjs` preserves `WF`, `OwnerOk`, `physIds` (I1), `config`, and `playRollback`. -/
theorem destroyManyObjs_inv :
    ∀ (ids : List ObjId) {s : GameState}, s.WF → s.OwnerOk →
      (destroyManyObjs s ids).1.WF ∧
      (destroyManyObjs s ids).1.OwnerOk ∧
      (destroyManyObjs s ids).1.physIds.Perm s.physIds ∧
      (destroyManyObjs s ids).1.config = s.config ∧
      (destroyManyObjs s ids).1.playRollback = s.playRollback
  | [], _, hwf, hok => ⟨hwf, hok, List.Perm.refl _, rfl, rfl⟩
  | id :: rest, s, hwf, hok => by
    unfold destroyManyObjs
    have h1 : let p1 := match s.locate id, s.obj? id with
        | some srcZ, some o =>
          if o.kind.phys?.isNone then (removeNonPhysObj s id, [])
          else
            match moveRuleObj s id (.player o.owner .graveyard) .top false with
            | some (sm, id') => (sm, ruleMoveEvents s id id' srcZ (.player o.owner .graveyard))
            | none => (s, [])
        | _, _ => (s, [])
        p1.1.WF ∧ p1.1.OwnerOk ∧ p1.1.physIds.Perm s.physIds ∧
        p1.1.config = s.config ∧ p1.1.playRollback = s.playRollback := by
      cases s.locate id with
      | none => exact ⟨hwf, hok, List.Perm.refl _, rfl, rfl⟩
      | some srcZ =>
        cases s.obj? id with
        | none => exact ⟨hwf, hok, List.Perm.refl _, rfl, rfl⟩
        | some o =>
          dsimp only
          split
          · have hm := removeNonPhysObj_meta s id
            exact ⟨removeNonPhysObj_wf hwf id, removeNonPhysObj_ownerOk hok id,
                   removeNonPhysObj_physIds hwf id, hm.1, hm.2⟩
          · cases hm : moveRuleObj s id (.player o.owner .graveyard) .top false with
            | none => exact ⟨hwf, hok, List.Perm.refl _, rfl, rfl⟩
            | some _ =>
              have hmeta := moveObj_config_rollback hm
              exact ⟨moveObj_wf hwf hm, moveObj_ownerOk hwf hok hm,
                     moveObj_physIds hwf hm, hmeta.1, hmeta.2⟩
    obtain ⟨hwf1, hok1, hp1, hc1, hr1⟩ := h1
    obtain ⟨hwf2, hok2, hp2, hc2, hr2⟩ := destroyManyObjs_inv rest hwf1 hok1
    exact ⟨hwf2, hok2, hp2.trans hp1, hc2.trans hc1, hr2.trans hr1⟩

/-- `destroyManyObjs` preserves `turn`, `tournament`, and `result`. -/
theorem destroyManyObjs_ttr :
    ∀ (ids : List ObjId) (s : GameState),
      (destroyManyObjs s ids).1.turn = s.turn ∧
      (destroyManyObjs s ids).1.tournament = s.tournament ∧
      (destroyManyObjs s ids).1.result = s.result
  | [], _ => ⟨rfl, rfl, rfl⟩
  | id :: rest, s => by
    unfold destroyManyObjs
    let p1 := match s.locate id, s.obj? id with
      | some srcZ, some o =>
        if o.kind.phys?.isNone then (removeNonPhysObj s id, [])
        else
          match moveRuleObj s id (.player o.owner .graveyard) .top false with
          | some (sm, id') => (sm, ruleMoveEvents s id id' srcZ (.player o.owner .graveyard))
          | none => (s, [])
      | _, _ => (s, [])
    have h1 : p1.1.turn = s.turn ∧ p1.1.tournament = s.tournament ∧ p1.1.result = s.result := by
      dsimp only [p1]
      cases s.locate id with
      | none => exact ⟨rfl, rfl, rfl⟩
      | some _ =>
        cases s.obj? id with
        | none => exact ⟨rfl, rfl, rfl⟩
        | some o =>
          dsimp only
          split
          · unfold removeNonPhysObj
            cases s.locate id with
            | none => exact ⟨rfl, rfl, rfl⟩
            | some _ =>
              cases s.obj? id with
              | none => exact ⟨rfl, rfl, rfl⟩
              | some _ => dsimp only; split <;> exact ⟨rfl, rfl, rfl⟩
          · cases hm : moveRuleObj s id (.player o.owner .graveyard) .top false with
            | none => exact ⟨rfl, rfl, rfl⟩
            | some _ => exact moveObj_ttr_core hm
    have h2 := destroyManyObjs_ttr rest p1.1
    exact ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.trans h1.2.2⟩

/-- Extract remaining damage amount from a `ProposedEvent` after replacement/prevention. -/
def remainingDamage : ProposedEvent → Nat
  | .damage _ _ d _ => d
  | _ => 0

/-- Deduct resolved damage and credit positive arcane damage to its source. -/
def applyResolvedDamage (s : GameState) (target : PlayerId) (kind : DamageKind)
    (amount : Nat) (origin : Option (PlayerId × ObjId)) : GameState :=
  let history := match kind, origin with
    | .arcane, some (controller, source) =>
      { controller, source, target, amount } :: s.arcaneDamageThisTurn
    | _, _ => s.arcaneDamageThisTurn
  { s.setLife target (s.lifeOf target - Int.ofNat amount) with arcaneDamageThisTurn := history }

/-- Settle costs and consumed effects before making the life change of a damage event. -/
def settleDamagePrevention (s : GameState) (result : ReplacementState) : GameState × List Event :=
  let remaining := keepDamageReplacements s.activeReplacements result
  destroyManyObjs { s with activeReplacements := remaining } result.destroyedSources

/-- Commit damage after replacement choices, consuming shields and destroying prevention sources
before updating life (CR 6.4, 6.5). -/
def settleDamage (s : GameState) (target : PlayerId) (kind : DamageKind) (result : ReplacementState) :
    GameState × List Event :=
  let (settled, events) := settleDamagePrevention s result
  let amount := remainingDamage result.event
  if amount = 0 then (settled, events)
  else (checkHeroDefeat (applyResolvedDamage settled target kind amount result.damageSource),
    events ++ [.damageDealt target kind amount])

/-- Settling an event preserves structural and rollback invariants. -/
theorem settleDamage_inv {s : GameState} (hwf : s.WF) (hok : s.OwnerOk) (p : PlayerId)
    (kind : DamageKind) (damage : ReplacementState) :
    (settleDamage s p kind damage).1.WF ∧
    (settleDamage s p kind damage).1.OwnerOk ∧
    (settleDamage s p kind damage).1.physIds.Perm s.physIds ∧
    (settleDamage s p kind damage).1.config = s.config ∧
    (settleDamage s p kind damage).1.playRollback = s.playRollback := by
  let board := { s with activeReplacements := keepDamageReplacements s.activeReplacements damage }
  let settled := (destroyManyObjs board damage.destroyedSources).1
  have hb := destroyManyObjs_inv damage.destroyedSources
    (GameState.WF.congr (s := s) (s2 := board) hwf rfl rfl rfl rfl)
    (GameState.OwnerOk.congr (s := s) (s2 := board) hok rfl rfl)
  obtain ⟨hw, ho, hp, hc, hr⟩ := hb
  unfold settleDamage settleDamagePrevention
  dsimp only
  split
  · exact ⟨hw, ho, hp, hc, hr⟩
  · let final := applyResolvedDamage settled p kind (remainingDamage damage.event) damage.damageSource
    have hfinal := checkHeroDefeat_config_rollback final
    exact ⟨checkHeroDefeat_wf (GameState.WF.congr hw rfl rfl rfl rfl),
      checkHeroDefeat_ownerOk (GameState.OwnerOk.congr ho rfl rfl),
      by rw [checkHeroDefeat_physIds]; exact hp, hfinal.1.trans hc, hfinal.2.trans hr⟩

/-- Settling damage preserves turn and tournament state, and never reopens a finished game. -/
theorem settleDamage_ttr (s : GameState) (p : PlayerId) (kind : DamageKind) (damage : ReplacementState) :
    (settleDamage s p kind damage).1.turn = s.turn ∧
    (settleDamage s p kind damage).1.tournament = s.tournament ∧
    ((settleDamage s p kind damage).1.result = none → s.result = none) := by
  let board := { s with activeReplacements := keepDamageReplacements s.activeReplacements damage }
  let settled := (destroyManyObjs board damage.destroyedSources).1
  have hb := destroyManyObjs_ttr damage.destroyedSources board
  unfold settleDamage settleDamagePrevention
  dsimp only
  split
  · exact ⟨hb.1, hb.2.1, fun hr => hb.2.2 ▸ hr⟩
  · have hc := checkHeroDefeat_ttr_core
      (applyResolvedDamage settled p kind (remainingDamage damage.event) damage.damageSource)
    exact ⟨hc.1.trans hb.1, hc.2.1.trans hb.2.1, fun hr => hb.2.2 ▸ hc.2.2 hr⟩

/-- Apply damage through the four-stage pipeline when there are no prevention choices
(CR 6.4, 6.5, 7.5). -/
def applyDamageWithPrevention (s : GameState) (target : PlayerId) (kind : DamageKind) (amt : Nat)
    (origin : Option (PlayerId × ObjId) := none) : GameState × List Event :=
  if amt = 0 then (s, [])
  else settleDamage s target kind (applyReplacementPipeline [] s.activeReplacements
    { event := .damage target kind amt, availResources := (s.poolOf target).resources,
      damageSource := origin })

/-- Apply all prepared life changes of one simultaneous damage event (CR 4.5.3a). -/
def applyArcaneBatchLosses (s : GameState) (batch : ArcaneDamageBatch) : GameState :=
  let damage := batch.settled.reverse.filter (fun (_, amount) => decide (0 < amount))
  let life := damage.foldl (fun totals (target, amount) =>
    totals.insert target.n (totals.getD target.n 0 - Int.ofNat amount)) s.heroLife
  let history := damage.foldl (fun history (target, amount) =>
    { controller := batch.controller, source := batch.source, target, amount } :: history)
    s.arcaneDamageThisTurn
  { s with heroLife := life, arcaneDamageThisTurn := history }

/-- Automatic damage preserves the structural and rollback invariants. -/
theorem applyDamageWithPrevention_inv {s : GameState} (hwf : s.WF) (hok : s.OwnerOk)
    (target : PlayerId) (kind : DamageKind) (amt : Nat) (origin : Option (PlayerId × ObjId) := none) :
    (applyDamageWithPrevention s target kind amt origin).1.WF ∧
    (applyDamageWithPrevention s target kind amt origin).1.OwnerOk ∧
    (applyDamageWithPrevention s target kind amt origin).1.physIds.Perm s.physIds ∧
    (applyDamageWithPrevention s target kind amt origin).1.config = s.config ∧
    (applyDamageWithPrevention s target kind amt origin).1.playRollback = s.playRollback := by
  unfold applyDamageWithPrevention
  split
  · exact ⟨hwf, hok, List.Perm.refl _, rfl, rfl⟩
  · exact settleDamage_inv hwf hok _ _ _

/-- Automatic damage preserves turn and tournament state, and never reopens a finished game. -/
theorem applyDamageWithPrevention_ttr (s : GameState) (target : PlayerId)
    (kind : DamageKind) (amt : Nat) (origin : Option (PlayerId × ObjId) := none) :
    (applyDamageWithPrevention s target kind amt origin).1.turn = s.turn ∧
    (applyDamageWithPrevention s target kind amt origin).1.tournament = s.tournament ∧
    ((applyDamageWithPrevention s target kind amt origin).1.result = none → s.result = none) := by
  unfold applyDamageWithPrevention
  split
  · exact ⟨rfl, rfl, id⟩
  · exact settleDamage_ttr _ _ _ _

/-- Arcane Barrier applies only while its sources are public and have their abilities (CR 8.3.8). -/
def arcaneBarrierEffects (s : GameState) (p : PlayerId) : List ReplacementEffect :=
  let sources := ((activationArenaZones s).flatMap s.zone).eraseDups
  let barriers := sources.flatMap fun source =>
    if !(s.obj? source).any (fun obj => !obj.faceDown) then [] else
      match s.characteristics source with
      | some chars =>
        if chars.controller == p && !chars.abilitiesLost then
          chars.keywords.filterMap fun
            | .arcaneBarrier (n + 1) => some (source, n + 1)
            | _ => none
        else []
      | none => []
  let firstId := s.activeReplacements.foldl (fun id effect => max id (effect.id + 1)) s.nextTimestamp
  barriers.zipIdx.map fun ((source, cost), index) =>
    { id := firstId + index, source, controller := p, stage := .prevention,
      action := .arcaneBarrierPrevent cost, optional := true }

/-- Resource cost of a paid prevention effect (CR 8.3.8). -/
def preventionResourceCost (effect : ReplacementEffect) : Nat :=
  match effect.action with
  | .arcaneBarrierPrevent n | .quellPrevent n => n
  | _ => 0

/-- Open a prevention choice when Arcane Barrier is available or fixed prevention competes
with another eligible effect (CR 6.4.10, 6.5.1). -/
def damagePreventionFrame? (s : GameState) (p : PlayerId) (kind : DamageKind) (amount : Nat)
    (attack : Option ObjId := none) (origin : Option (PlayerId × ObjId) := none)
    (batch : Option ArcaneDamageBatch := none) : Option Frame :=
  if amount = 0 then none
  else
    let barriers := if kind == .arcane then arcaneBarrierEffects s p else []
    let effects := s.activeReplacements ++ barriers
    let proposed : ReplacementState := { event := .damage p kind amount, damageSource := origin, batch }
    let damage := applyReplacementStage .standard [] effects
      (applyReplacementStage .selfOrIdentity [] effects proposed)
    let candidates := effects.filter fun effect =>
      let offeredEnergy := max (preventionResourceCost effect) (s.poolOf p).totalEnergy
      effect.eligible .prevention { damage with availResources := offeredEnergy }
    let hasFixed := candidates.any fun effect =>
      match effect.action with
      | .fixedPrevent _ => true
      | _ => false
    if batch.isSome || !barriers.isEmpty || (hasFixed && candidates.length > 1) then
      some (.arcaneDamage p effects damage .offer attack)
    else none

/-- Prepare prevention for the next target without changing any hero's life. -/
def nextArcaneBatchFrame (s : GameState) (batch : ArcaneDamageBatch) : List Frame :=
  match batch.remaining with
  | [] => []
  | (target, amount) :: remaining =>
    (damagePreventionFrame? s target .arcane amount none (some (batch.controller, batch.source))
      (some { batch with remaining })).toList

/-- Whether public board state presents a possible replacement for arcane damage to a hero. -/
def hasArcaneReplacement (s : GameState) (target : PlayerId) (amount : Nat) : Bool :=
  !((arcaneBarrierEffects s target).isEmpty) ||
    s.activeReplacements.any fun effect =>
      let offer : ReplacementState :=
        { event := .damage target .arcane amount, availResources := (s.poolOf target).totalEnergy }
      effect.controller == target && effect.eligible effect.stage offer

/-- Banish the first card in a hand and schedule its return at the beginning of the end phase. -/
def intimidateHandFront (s : GameState) (ctrl target : PlayerId) : GameState × List Event × List Frame :=
  match s.zone (.player target .hand) with
  | [] => (s, [], [])
  | cid :: _ =>
    match banishOne s cid true with
    | none => (s, [], [])
    | some (s1, banId, es) =>
      let dt : DelayedTrigger :=
        { id := s1.nextTimestamp
          controller := ctrl
          source := banId
          watch := .phase .endPhase
          effect := .prim (.moveCard .self_ .hand .top false) }
      ({ s1 with
          delayedTriggers := s1.delayedTriggers ++ [dt]
          nextTimestamp := s1.nextTimestamp + 1 }, es, [])

/-- Intimidate preserves physical cards, ownership, board well-formedness, and rollback metadata. -/
theorem intimidateHandFront_inv {s : GameState} (ctrl target : PlayerId) (hwf : s.WF) (hok : s.OwnerOk) :
    (intimidateHandFront s ctrl target).1.WF ∧
    (intimidateHandFront s ctrl target).1.OwnerOk ∧
    (intimidateHandFront s ctrl target).1.physIds.Perm s.physIds ∧
    (intimidateHandFront s ctrl target).1.config = s.config ∧
    (intimidateHandFront s ctrl target).1.playRollback = s.playRollback := by
  unfold intimidateHandFront
  cases s.zone (.player target .hand) with
  | nil => exact ⟨hwf, hok, List.Perm.refl _, rfl, rfl⟩
  | cons cid _ =>
    dsimp only
    cases hb : banishOne s cid true with
    | none => exact ⟨hwf, hok, List.Perm.refl _, rfl, rfl⟩
    | some res =>
      obtain ⟨s1, banId, es1⟩ := res
      dsimp only
      have hmeta : s1.config = s.config ∧ s1.playRollback = s.playRollback := by
        unfold banishOne at hb
        split at hb
        · rename_i src0 o0 _ _
          dsimp only at hb
          cases hm : moveObj s cid (Zone.player o0.owner .banished) .top true with
          | none => rw [hm] at hb; cases hb
          | some rm =>
            obtain ⟨sm, idm⟩ := rm
            rw [hm] at hb; simp only [Option.some.injEq, Prod.mk.injEq] at hb
            obtain ⟨rfl, rfl, rfl⟩ := hb
            exact moveObj_config_rollback hm
        · cases hb
      have hp := banishOne_physIds hwf hb
      exact ⟨GameState.WF.congr (banishOne_wf hwf hb) rfl rfl rfl rfl,
             GameState.OwnerOk.congr (banishOne_ownerOk hwf hok hb) rfl rfl,
             hp, hmeta.1, hmeta.2⟩

/-- Intimidate preserves turn, tournament state, and result. -/
theorem intimidateHandFront_ttr (s : GameState) (ctrl target : PlayerId) :
    (intimidateHandFront s ctrl target).1.turn = s.turn ∧
    (intimidateHandFront s ctrl target).1.tournament = s.tournament ∧
    ((intimidateHandFront s ctrl target).1.result = none → s.result = none) := by
  unfold intimidateHandFront
  cases s.zone (.player target .hand) with
  | nil => exact ⟨rfl, rfl, id⟩
  | cons cid _ =>
    dsimp only
    cases hb : banishOne s cid true with
    | none => exact ⟨rfl, rfl, id⟩
    | some res =>
      obtain ⟨s1, _, _⟩ := res; dsimp only
      unfold banishOne at hb; split at hb
      · rename_i src0 o0 _ _
        dsimp only at hb
        cases hm : moveObj s cid (Zone.player o0.owner .banished) .top true with
        | none => rw [hm] at hb; cases hb
        | some rm =>
          obtain ⟨sm, idm⟩ := rm
          rw [hm] at hb; simp only [Option.some.injEq, Prod.mk.injEq] at hb
          obtain ⟨rfl, rfl, rfl⟩ := hb
          have h := moveObj_ttr_core hm
          exact ⟨h.1, h.2.1, fun hr => h.2.2 ▸ hr⟩
      · cases hb

/-- Keep a pair only when its two positions satisfy the filters in either order. -/
def matchingRevealedPair (s : GameState) (first second : CardFilter) : List ObjId → List ObjId
  | [a, b] =>
    let fits (id : ObjId) (filter : CardFilter) :=
      (s.objectFace? id).any (cardFaceMatches filter)
    if (fits a first && fits b second) || (fits a second && fits b first) then
      [a, b]
    else []
  | _ => []

/-- Add bonuses bound to this damage source before applying prevention (CR 6.4). -/
def modifiedDamageAmount (s : GameState) (source : ObjId) (kind : DamageKind) (amount : Nat) : Nat :=
  if kind != .arcane || amount == 0 then amount else
    s.activeEffects.foldl (fun total effect =>
      match effect.target, effect.op with
      | .obj object, .addArcaneDamageFromSource additional =>
        if object == source && !effect.waitsForNextTurn then total + additional else total
      | _, _ => total) amount

/-- Execute a single atomic `Prim`, returning `(newState, emittedEvents, pushedFrames)`.
Total by design: impossible instructions become no-ops (CR 1.0.1b). -/
def execPrim (s : GameState) (ctrl : PlayerId) (src : ObjId) (env : List (VarId × Int))
    (p : Prim) : GameState × List Event × List Frame :=
  match p with
  | .draw pref n =>
    let target := evalPlayerRef s ctrl pref
    let cnt := clampNonNeg (evalNumExpr s ctrl env n (some src))
    (s, [], [.draw target cnt])
  | .gainLife pref n =>
    let target := evalPlayerRef s ctrl pref
    let amt := clampNonNeg (evalNumExpr s ctrl env n (some src))
    let events := if amt = 0 then [] else [.lifeGained target amt]
    (s.setLife target (s.lifeOf target + Int.ofNat amt), events, [])
  | .loseLife pref n =>
    let target := evalPlayerRef s ctrl pref
    let amt := clampNonNeg (evalNumExpr s ctrl env n (some src))
    let s1 := checkHeroDefeat (s.setLife target (s.lifeOf target - Int.ofNat amt))
    (s1, [], [])
  | .dealDamage kind pref n =>
    let target := evalPlayerRef s ctrl pref
    let amt := modifiedDamageAmount s src kind (clampNonNeg (evalNumExpr s ctrl env n (some src)))
    match damagePreventionFrame? s target kind amt none (some (ctrl, src)) with
    | some frame => (s, [], [frame])
    | none =>
      let (s1, es) := applyDamageWithPrevention s target kind amt (some (ctrl, src))
      (s1, es, [])
  | .dealArcaneDamageToPair first second amount =>
    let p := evalPlayerRef s ctrl first
    let q := evalPlayerRef s ctrl second
    let damage (base : Nat) := modifiedDamageAmount s src .arcane base
    let remaining := if p == q then [(p, damage (amount + amount))] else
      [(p, damage amount), (q, damage amount)]
    let batch : ArcaneDamageBatch := { controller := ctrl, source := src, remaining }
    let frames :=
      if amount == 0 then []
      else if p != q && hasArcaneReplacement s p (damage amount) && hasArcaneReplacement s q (damage amount) then
        [.chooseArcaneDamageOrder (s.active.getD ctrl) ctrl src remaining]
      else nextArcaneBatchFrame s batch
    (s, [], frames)
  | .gainAP pref n =>
    let target := evalPlayerRef s ctrl pref
    let amt := clampNonNeg (evalNumExpr s ctrl env n (some src))
    (s.setPool target ((s.poolOf target).addActionPoints amt), [], [])
  | .gainResource pref n =>
    let target := evalPlayerRef s ctrl pref
    let amt := clampNonNeg (evalNumExpr s ctrl env n (some src))
    (s.setPool target ((s.poolOf target).addResources amt), [], [])
  | .gainChi pref n =>
    let target := evalPlayerRef s ctrl pref
    let amt := clampNonNeg (evalNumExpr s ctrl env n (some src))
    (s.setPool target ((s.poolOf target).addChi amt), [], [])
  | .opt pref n =>
    let target := evalPlayerRef s ctrl pref
    (s, [], [.optStep target n])
  | .optValue pref n =>
    let target := evalPlayerRef s ctrl pref
    let count := clampNonNeg (evalNumExpr s ctrl env n (some src))
    (s, [], [.optStep target count])
  | .openBoosters none =>
    let names := (s.cards.cards.filterMap (fun card =>
      if card.front.hasType .action then some card.front.name else none)).eraseDups
    let choices := names.map fun name => Effect.prim (.openBoosters (some name))
    if choices.isEmpty then (s, [], [])
    else (s, [], [.chooseModal ctrl src false env choices])
  | .openBoosters (some name) =>
    match s.unopenedBoosters.find? (fun pack => pack.1 == ctrl) with
    | none => (s, [], [])
    | some pack =>
      let contents := pack.2.filter (s.zone (.player ctrl .outside)).contains
      let cards := contents.filterMap fun id => (s.obj? id).bind (·.kind.cardId?)
      let matchingCards := contents.filter fun id => (s.objectFace? id).any (·.name == name)
      let remaining := s.unopenedBoosters.erase pack
      let after :=
        if matchingCards.isEmpty then
          if remaining.any (fun next => next.1 == ctrl) then
            [.chooseMay ctrl src false env (.prim (.openBoosters (some name))) .nop]
          else []
        else
          let moves := matchingCards.map fun id => Effect.prim (.moveCard (.declared id) .hand .top false)
          [.run ctrl src false env moves]
      ({ s with unopenedBoosters := remaining }, [.boosterOpened ctrl cards], after)
  | .createToken pref tokId n =>
    let target := evalPlayerRef s ctrl pref
    (createTokens s target tokId (tokenCreationCount s target tokId n), [], [])
  | .createTokenForAttackDamage _ _ =>
    (s, [], [])
  | .destroy oref =>
    match evalObjRef src oref with
    | none => (s, [], [])
    | some oid =>
      match s.locate oid, s.obj? oid with
      | some srcZ, some o =>
        match moveRuleObj s oid (.player o.owner .graveyard) .top false with
        | some (s1, oid') => (s1, ruleMoveEvents s oid oid' srcZ (.player o.owner .graveyard), [])
        | none => (s, [], [])
      | _, _ => (s, [], [])
  | .banish oref fd =>
    match evalObjRef src oref with
    | none => (s, [], [])
    | some oid =>
      match banishOne s oid fd with
      | some (s1, _, es) => (s1, es, [])
      | none => (s, [], [])
  | .moveCard oref dstRef dpos fd =>
    match evalObjRef src oref with
    | none => (s, [], [])
    | some oid =>
      match s.locate oid, s.obj? oid with
      | some srcZ, some o =>
        match zoneOfRef o.owner dstRef with
        | none => (s, [], [])
        | some dstZ =>
          let pos : Pos := match dpos with | .bottom => .bottom | _ => .top
          match moveRuleObj s oid dstZ pos fd with
          | some (s1, oid') => (s1, ruleMoveEvents s oid oid' srcZ dstZ, [])
          | none => (s, [], [])
      | _, _ => (s, [], [])
  | .putHandOnDeck pref dpos =>
    let target := evalPlayerRef s ctrl pref
    if (s.zone (.player target .hand)).isEmpty then
      (s, [], [])
    else
      (s, [], [.chooseHandToDeck target dpos])
  | .cycleArsenal pref subtype keyword =>
    let player := evalPlayerRef s ctrl pref
    let arsenal := Zone.player player .arsenal
    let deck := Zone.player player .deck
    match s.zone arsenal with
    | [] => (s, [], [])
    | stored :: _ =>
      match moveObj s stored deck .bottom false with
      | none => (s, [], [])
      | some (cycled, bottom) =>
        let events := [Event.moved stored bottom arsenal deck]
        match cycled.zone deck with
        | [] => (cycled, events, [])
        | top :: _ =>
          match moveObj cycled top arsenal .top false with
          | none => (cycled, events, [])
          | some (loaded, loadedId) =>
            let granted :=
              if (loaded.characteristics loadedId).any (fun chars => chars.subtypes.contains subtype) then
                let effect : ContinuousEffect :=
                  { id := loaded.nextTimestamp, source := src, controller := player
                    target := .arsenalCard loadedId, op := .grantKeyword keyword
                    timestamp := ⟨loaded.nextTimestamp⟩ }
                { loaded with activeEffects := loaded.activeEffects ++ [effect]
                              nextTimestamp := loaded.nextTimestamp + 1 }
              else loaded
            (granted, events ++ [.moved top loadedId deck arsenal], [])
  | .putArsenalOnDeckBottom pref =>
    let target := evalPlayerRef s ctrl pref
    match s.zone (.player target .arsenal) with
    | aid :: _ =>
      match moveObj s aid (.player target .deck) .bottom false with
      | some (s1, aid') => (s1, [.moved aid aid' (.player target .arsenal) (.player target .deck)], [])
      | none => (s, [], [])
    | [] => (s, [], [])
  | .addCounter oref k n =>
    match evalObjRef src oref with
    | none => (s, [], [])
    | some oid =>
      let amt := clampNonNeg (evalNumExpr s ctrl env n (some src))
      (updateSingleObject s oid (fun o => o.addCounterVal k amt), [], [])
  | .removeCounter oref k n =>
    match evalObjRef src oref with
    | none => (s, [], [])
    | some oid =>
      let amount := clampNonNeg (evalNumExpr s ctrl env n (some src))
      (updateSingleObject s oid (fun o => o.removeCounterVal k amount), counterRemovalEvents s oid k amount, [])
  | .removeAllCounters oref k =>
    match evalObjRef src oref with
    | none => (s, [], [])
    | some oid =>
      let amount := ((s.obj? oid).map (·.counterCount k)).getD 0
      (updateSingleObject s oid (fun o => o.clearCounterVal k), counterRemovalEvents s oid k amount, [])
  | .discardRandom pref n =>
    let target := evalPlayerRef s ctrl pref
    let cnt := clampNonNeg (evalNumExpr s ctrl env n (some src))
    let hand := Zone.player target .hand
    if 0 < cnt ∧ cnt < (s.zone hand).length then
      (s, [], [.chanceShuffle hand, .run target src false [] [.prim (.discardHandPrefix cnt)]])
    else
      let (s1, es) := discardManyObjs s target ((s.zone hand).take cnt)
      (s1, es, [])
  | .discardHandPrefix cnt =>
    let (s1, es) := discardManyObjs s ctrl ((s.zone (.player ctrl .hand)).take cnt)
    (s1, es, [])
  | .discardChoice pref f n =>
    let target := evalPlayerRef s ctrl pref
    let cnt := clampNonNeg (evalNumExpr s ctrl env n (some src))
    let matching := (s.zone (.player target .hand)).filter fun id =>
      match s.objectFace? id with
      | some face => cardFaceMatches f face
      | none => false
    if 0 < cnt && cnt < matching.length then
      (s, [], [.chooseDiscard target cnt matching []])
    else
      let (s1, es) := discardManyObjs s target (matching.take cnt)
      (s1, es, [])
  | .intimidate pref =>
    let target := evalPlayerRef s ctrl pref
    let hand := Zone.player target .hand
    if 1 < (s.zone hand).length then
      (s, [], [.chanceShuffle hand, .run ctrl src false [] [.prim (.intimidateHandFront target)]])
    else intimidateHandFront s ctrl target
  | .intimidateHandFront target => intimidateHandFront s ctrl target
  | .returnDefendingCardToHand f =>
    let choices := ((s.combat.bind CombatChain.activeLink?).map (·.defending)).getD []
    let choices := choices.filter fun id =>
      s.locate id == some .combatChain && (s.objectFace? id).any (cardFaceMatches f)
    if choices.isEmpty then (s, [], [])
    else (s, [], [.chooseModal ctrl src false env
      (.nop :: choices.map (fun id => .prim (.returnChosenDefendingCard id)))])
  | .returnChosenDefendingCard id =>
    match s.combat.bind CombatChain.activeLink? with
    | none => (s, [], [])
    | some link =>
      if link.defending.contains id && s.locate id == some .combatChain then
        match s.obj? id with
        | none => (s, [], [])
        | some o =>
          let isAction := (s.objectFace? id).any (·.hasType .action)
          match moveObj s id (.player o.owner .hand) .top false with
          | none => (s, [], [])
          | some (s1, id') =>
            let cc' := s1.combat.map fun cc => cc.updateActiveLink fun l =>
              l.removeDefender id isAction
            ({ s1 with combat := cc' }, [.moved id id' .combatChain (.player o.owner .hand)], [])
      else (s, [], [])
  | .searchDeck pref f maxCount dstRef reveal playable shuffleAfter exactCost =>
    let target := evalPlayerRef s ctrl pref
    let price := exactCost.map (fun expr => clampNonNeg (evalNumExpr s ctrl env expr (some src)))
    match zoneOfRef target dstRef with
    | none => (s, [], [])
    | some dstZ =>
      let matching := (s.zone (.player target .deck)).filter fun id =>
        match s.objectFace? id with
        | some face => cardFaceMatches f face && price.all (fun n => face.cost.any (·.resources == n))
        | none => false
      let limit := min (maxCount.getD matching.length) matching.length
      let choice : DeckSearchChoice :=
        { destination := dstZ
          reveal := reveal
          mayFail := f != CardFilter.any || price.isSome
          shuffleAfter := shuffleAfter
          playableDuration := playable }
      let follow := if maxCount == some 0 || (s.zone (.player target .deck)).isEmpty then
          if shuffleAfter then [.chanceShuffle (.player target .deck)] else []
        else [.chooseShuffleCards target limit matching [] false (some choice)]
      (s, [], follow)
  | .searchDeckToTop pref filter bound =>
    let player := evalPlayerRef s ctrl pref
    let deck := Zone.player player .deck
    let filter := match bound with
      | none => filter
      | some maximum =>
        let cap := clampNonNeg (evalNumExpr s ctrl env maximum (some src))
        { filter with maxCost := some (min (filter.maxCost.getD cap) cap) }
    let candidates := (s.zone deck).filter fun id => (s.objectFace? id).any (cardFaceMatches filter)
    let choice : DeckSearchChoice :=
      { destination := deck, reveal := true, mayFail := true, putOnTopAfterShuffle := true }
    (s, [], if (s.zone deck).isEmpty then [.chanceShuffle deck]
      else [.chooseShuffleCards player 1 candidates [] false (some choice)])
  | .putChosenDeckCardOnTop pref id =>
    let deck := Zone.player (evalPlayerRef s ctrl pref) .deck
    if deck.Valid s.playerCount then
      (s.reorder deck (optDeckOrder (s.zone deck) 0 id true), [], [])
    else (s, [], [])
  | .lookDeckToArsenal pref count filter =>
    let player := evalPlayerRef s ctrl pref
    let arsenal := Zone.player player .arsenal
    let viewed := (s.zone (.player player .deck)).take count
    if !(s.zone arsenal).isEmpty || viewed.isEmpty then (s, [], [])
    else
      let candidates := viewed.filter fun id => (s.objectFace? id).any (cardFaceMatches filter)
      let choice : DeckSearchChoice :=
        { destination := arsenal, reveal := false, mayFail := true,
          shuffleAfter := false, searchesDeck := false, bottomSelection := some (.lookedAt viewed) }
      (s, [], [.chooseShuffleCards player 1 candidates [] false (some choice)])
  | .lookTopToBanishedAsInstant pref filter discountFromDamage =>
    let discount := if discountFromDamage then s.arcaneDamageFrom src else 0
    let player := evalPlayerRef s ctrl pref
    let viewed := (s.zone (.player player .deck)).take 1
    let candidates := viewed.filter fun id =>
      (s.objectFace? id).any (cardFaceMatches filter)
    let choice : DeckSearchChoice :=
      { destination := .player player .banished, reveal := false, mayFail := true,
        shuffleAfter := false, playableDuration := some .thisTurn, playAsInstant := true,
        resourceDiscount := discount, viewedCards := some viewed, searchesDeck := false }
    (s, [], if viewed.isEmpty || (discountFromDamage && discount == 0) then [] else
      [.chooseShuffleCards player candidates.length candidates [] false (some choice)])
  | .putChosenDeckCardsOnBottom pref ids =>
    let deck := Zone.player (evalPlayerRef s ctrl pref) .deck
    if deck.Valid s.playerCount then
      (s.reorder deck (deckBottomOrder (s.zone deck) ids), [], [])
    else (s, [], [])
  | .revealTopPairToHand pref first second =>
    let player := evalPlayerRef s ctrl pref
    let top := (s.zone (.player player .deck)).take 2
    let revealed := top.filterMap fun id =>
      (s.cardDefOf? id).map (fun card => Event.revealed player id card.id)
    let (moved, events) :=
      moveManyObjs s (matchingRevealedPair s first second top) (.player player .hand) .top false
    (moved, revealed ++ events, [])
  | .reload pref =>
    let player := evalPlayerRef s ctrl pref
    (s, [], if (s.zone (.player player .arsenal)).isEmpty && !(s.zone (.player player .hand)).isEmpty
      then [.chooseArsenal player] else [])
  | .putHandArsenal pref filter drawAfter powerBonus =>
    let target := evalPlayerRef s ctrl pref
    let hand := s.zone (.player target .hand)
    let arsenal := Zone.player target .arsenal
    if hand.isEmpty || !(s.zone arsenal).isEmpty then (s, [], [])
    else
      let matching := hand.filter fun id => (s.objectFace? id).any (cardFaceMatches filter)
      let choice : DeckSearchChoice :=
        { destination := arsenal, reveal := false, mayFail := true,
          shuffleAfter := false, searchesDeck := false, arsenalPowerBonus := powerBonus.map (src, ·) }
      (s, [], [.chooseShuffleCards target 1 matching [] drawAfter (some choice)])
  | .putHandPermanent pref filter entryCounter =>
    let target := evalPlayerRef s ctrl pref
    let hand := s.zone (.player target .hand)
    let matching := hand.filter fun id => (s.objectFace? id).any (cardFaceMatches filter)
    let choice : DeckSearchChoice :=
      { destination := .player target .permanent, reveal := false, mayFail := true,
        shuffleAfter := false, searchesDeck := false, entryCounter }
    (s, [], if hand.isEmpty then [] else [.chooseShuffleCards target 1 matching [] false (some choice)])
  | .shuffleZone pref ref =>
    (s, [], ((zoneOfRef (evalPlayerRef s ctrl pref) ref).map Frame.chanceShuffle).toList)
  | .shuffleZoneIntoDeck pref srcRef f maxCount drawSame =>
    let target := evalPlayerRef s ctrl pref
    match zoneOfRef target srcRef with
    | none => (s, [], [])
    | some srcZ =>
      let matching := (s.zone srcZ).filter fun id =>
        match s.objectFace? id with
        | some face => cardFaceMatches f face
        | none => false
      let limit := min (maxCount.getD matching.length) matching.length
      let follow := if limit = 0 then [.chanceShuffle (.player target .deck)]
        else [.chooseShuffleCards target limit matching [] drawSame]
      (s, [], follow)
  | .revealTopToArsenalIf pref f =>
    let target := evalPlayerRef s ctrl pref
    let deck := Zone.player target .deck
    let arsenal := Zone.player target .arsenal
    match s.zone deck with
    | [] => (s, [], [])
    | topId :: _ =>
      let revealed := ((s.cardDefOf? topId).map fun card => Event.revealed target topId card.id).toList
      if (s.objectFace? topId).any (cardFaceMatches f) && (s.zone arsenal).isEmpty then
        match moveObj s topId arsenal .top true with
        | some (s1, id') => (s1, revealed ++ [.moved topId id' deck arsenal], [])
        | none => (s, revealed, [])
      else
        (s, revealed, [])
  | .preventNextDamage pref n _ | .preventDamageOnce pref n =>
    let target := evalPlayerRef s ctrl pref
    let amt := clampNonNeg (evalNumExpr s ctrl env n (some src))
    if amt = 0 then
      (s, [], [])
    else
      let re : ReplacementEffect :=
        { id := s.nextTimestamp
          source := src
          controller := target
          stage := .prevention
          action := match p with
            | .preventDamageOnce _ _ => .fixedPrevent amt
            | _ => .shieldPrevent amt
          optional := false }
      ({ s with
          activeReplacements := s.activeReplacements ++ [re]
          nextTimestamp := s.nextTimestamp + 1 }, [], [])
  | .closeCombatChain =>
    (s, [], [.combatStep .close src])
  | .charge pref =>
    let target := evalPlayerRef s ctrl pref
    match s.zone (.player target .hand) with
    | [] => (s, [], [])
    | cid :: _ =>
      match moveObj s cid (.player target .soul) .bottom false with
      | none => (s, [], [])
      | some (s1, id') =>
        let ch' := if s1.chargedThisTurn.contains target then s1.chargedThisTurn
                   else target :: s1.chargedThisTurn
        ({ s1 with chargedThisTurn := ch' }, [.moved cid id' (.player target .hand) (.player target .soul)], [])
  | .banishFromSoul pref n =>
    let target := evalPlayerRef s ctrl pref
    let picked := (s.zone (.player target .soul)).take n
    let (s1, es) := banishManyObjs s target false picked
    (s1, es, [])
  | .banishTopDeck pref n fd =>
    let target := evalPlayerRef s ctrl pref
    let picked := (s.zone (.player target .deck)).take n
    let (s1, es) := banishManyObjs s target fd picked
    (s1, es, [])
  | .banishFromGraveyard pref f n =>
    let target := evalPlayerRef s ctrl pref
    let matching := (s.zone (.player target .graveyard)).filter fun id =>
      match s.objectFace? id with
      | some face => cardFaceMatches f face
      | none => false
    let (s1, es) := banishManyObjs s target false (matching.take n)
    (s1, es, [])
  | .weaponAttack =>
    (s, [], [])

/-- **L4** (bundled preservation for `execPrim`): every primitive preserves `WF`, `OwnerOk`,
`physIds` (I1), `config`, and `playRollback`. -/
theorem execPrim_inv {s : GameState} (hwf : s.WF) (hok : s.OwnerOk) (ctrl : PlayerId)
    (src : ObjId) (env : List (VarId × Int)) (p : Prim) :
    (execPrim s ctrl src env p).1.WF ∧
    (execPrim s ctrl src env p).1.OwnerOk ∧
    (execPrim s ctrl src env p).1.physIds.Perm s.physIds ∧
    (execPrim s ctrl src env p).1.config = s.config ∧
    (execPrim s ctrl src env p).1.playRollback = s.playRollback := by
  cases p with
  | draw _ _ | opt _ _ | optValue _ _ | weaponAttack | closeCombatChain | createTokenForAttackDamage _ _ =>
    exact ⟨hwf, hok, List.Perm.refl _, rfl, rfl⟩
  | openBoosters name =>
    cases name <;> unfold execPrim <;> dsimp only <;> split <;>
      exact ⟨GameState.WF.congr hwf rfl rfl rfl rfl,
             GameState.OwnerOk.congr hok rfl rfl, List.Perm.refl _, rfl, rfl⟩
  | gainLife _ _ | gainAP _ _ | gainResource _ _ | gainChi _ _ =>
    exact ⟨GameState.WF.congr hwf rfl rfl rfl rfl,
           GameState.OwnerOk.congr hok rfl rfl,
           List.Perm.refl _, rfl, rfl⟩
  | loseLife pref n =>
    unfold execPrim; dsimp only
    let s1 := s.setLife (evalPlayerRef s ctrl pref)
      (s.lifeOf (evalPlayerRef s ctrl pref) - Int.ofNat (clampNonNeg (evalNumExpr s ctrl env n (some src))))
    have hwf1 : s1.WF := GameState.WF.congr hwf rfl rfl rfl rfl
    have hok1 : s1.OwnerOk := GameState.OwnerOk.congr hok rfl rfl
    have hm := checkHeroDefeat_config_rollback s1
    exact ⟨checkHeroDefeat_wf hwf1, checkHeroDefeat_ownerOk hok1,
           by rw [checkHeroDefeat_physIds]; exact List.Perm.refl _, hm.1, hm.2⟩
  | dealDamage kind pref n =>
    unfold execPrim
    dsimp only
    split
    · exact ⟨hwf, hok, List.Perm.refl _, rfl, rfl⟩
    · exact applyDamageWithPrevention_inv hwf hok (evalPlayerRef s ctrl pref) kind
        (modifiedDamageAmount s src kind (clampNonNeg (evalNumExpr s ctrl env n (some src))))
        (some (ctrl, src))
  | dealArcaneDamageToPair _ _ _ => exact ⟨hwf, hok, List.Perm.refl _, rfl, rfl⟩
  | createToken pref tokId n =>
    let target := evalPlayerRef s ctrl pref
    let count := tokenCreationCount s target tokId n
    have hm := createTokens_meta target tokId count s
    exact ⟨createTokens_wf _ _ _ hwf, createTokens_ownerOk _ _ _ hwf hok,
           createTokens_physIds _ _ _ hwf, hm.1, hm.2⟩
  | destroy oref =>
    unfold execPrim; dsimp only
    cases evalObjRef src oref with
    | none => exact ⟨hwf, hok, List.Perm.refl _, rfl, rfl⟩
    | some oid =>
      dsimp only
      split
      · rename_i srcZ o _ _
        cases hm : moveRuleObj s oid (.player o.owner .graveyard) .top false with
        | none => exact ⟨hwf, hok, List.Perm.refl _, rfl, rfl⟩
        | some _ =>
          have hmeta := moveObj_config_rollback hm
          exact ⟨moveObj_wf hwf hm, moveObj_ownerOk hwf hok hm,
                 moveObj_physIds hwf hm, hmeta.1, hmeta.2⟩
      · exact ⟨hwf, hok, List.Perm.refl _, rfl, rfl⟩
  | banish oref fd =>
    unfold execPrim; dsimp only
    cases evalObjRef src oref with
    | none => exact ⟨hwf, hok, List.Perm.refl _, rfl, rfl⟩
    | some oid =>
      dsimp only
      cases hb : banishOne s oid fd with
      | none => exact ⟨hwf, hok, List.Perm.refl _, rfl, rfl⟩
      | some res =>
        obtain ⟨s1, id1, es1⟩ := res
        dsimp only
        have hmeta : s1.config = s.config ∧ s1.playRollback = s.playRollback := by
          unfold banishOne at hb
          split at hb
          · rename_i src0 o0 _ _
            dsimp only at hb
            cases hm : moveObj s oid (Zone.player o0.owner .banished) .top fd with
            | none => rw [hm] at hb; cases hb
            | some rm =>
              obtain ⟨sm, idm⟩ := rm
              rw [hm] at hb; simp only [Option.some.injEq, Prod.mk.injEq] at hb
              obtain ⟨rfl, rfl, rfl⟩ := hb
              exact moveObj_config_rollback hm
          · cases hb
        exact ⟨banishOne_wf hwf hb, banishOne_ownerOk hwf hok hb,
               banishOne_physIds hwf hb, hmeta.1, hmeta.2⟩
  | moveCard oref dstRef dpos fd =>
    unfold execPrim; dsimp only
    cases evalObjRef src oref with
    | none => exact ⟨hwf, hok, List.Perm.refl _, rfl, rfl⟩
    | some oid =>
      dsimp only
      split
      · rename_i srcZ o _ _
        cases zoneOfRef o.owner dstRef with
        | none => exact ⟨hwf, hok, List.Perm.refl _, rfl, rfl⟩
        | some dstZ =>
          dsimp only
          split
          · rename_i s1 oid' hm
            have hmeta := moveObj_config_rollback hm
            exact ⟨moveObj_wf hwf hm, moveObj_ownerOk hwf hok hm,
                   moveObj_physIds hwf hm, hmeta.1, hmeta.2⟩
          · exact ⟨hwf, hok, List.Perm.refl _, rfl, rfl⟩
      · exact ⟨hwf, hok, List.Perm.refl _, rfl, rfl⟩
  | putHandOnDeck _ _ =>
    unfold execPrim; dsimp only; split <;> exact ⟨hwf, hok, List.Perm.refl _, rfl, rfl⟩
  | cycleArsenal pref subtype _ =>
    unfold execPrim
    dsimp only
    let player := evalPlayerRef s ctrl pref
    cases s.zone (.player player .arsenal) with
    | nil => exact ⟨hwf, hok, List.Perm.refl _, rfl, rfl⟩
    | cons stored _ =>
      dsimp only
      cases hc : moveObj s stored (.player player .deck) .bottom false with
      | none => exact ⟨hwf, hok, List.Perm.refl _, rfl, rfl⟩
      | some moved =>
        obtain ⟨cycled, bottom⟩ := moved
        dsimp only
        have hwfc := moveObj_wf hwf hc
        have hokc := moveObj_ownerOk hwf hok hc
        have hpc := moveObj_physIds hwf hc
        have hmc := moveObj_config_rollback hc
        cases cycled.zone (.player player .deck) with
        | nil => exact ⟨hwfc, hokc, hpc, hmc.1, hmc.2⟩
        | cons top _ =>
          dsimp only
          cases hl : moveObj cycled top (.player player .arsenal) .top false with
          | none => exact ⟨hwfc, hokc, hpc, hmc.1, hmc.2⟩
          | some loadedCard =>
            obtain ⟨loaded, loadedId⟩ := loadedCard
            dsimp only
            have hwfl := moveObj_wf hwfc hl
            have hokl := moveObj_ownerOk hwfc hokc hl
            have hpl := (moveObj_physIds hwfc hl).trans hpc
            have hml := moveObj_config_rollback hl
            split
            · exact ⟨GameState.WF.congr hwfl rfl rfl rfl rfl, GameState.OwnerOk.congr hokl rfl rfl,
                hpl, hml.1.trans hmc.1, hml.2.trans hmc.2⟩
            · exact ⟨hwfl, hokl, hpl, hml.1.trans hmc.1, hml.2.trans hmc.2⟩
  | putArsenalOnDeckBottom pref =>
    unfold execPrim; dsimp only
    cases s.zone (.player (evalPlayerRef s ctrl pref) .arsenal) with
    | nil => exact ⟨hwf, hok, List.Perm.refl _, rfl, rfl⟩
    | cons aid _ =>
      dsimp only
      cases hm : moveObj s aid (.player (evalPlayerRef s ctrl pref) .deck) .bottom false with
      | none => exact ⟨hwf, hok, List.Perm.refl _, rfl, rfl⟩
      | some _ =>
        have hmeta := moveObj_config_rollback hm
        exact ⟨moveObj_wf hwf hm, moveObj_ownerOk hwf hok hm,
               moveObj_physIds hwf hm, hmeta.1, hmeta.2⟩
  | addCounter oref k n =>
    unfold execPrim; dsimp only
    cases evalObjRef src oref with
    | none => exact ⟨hwf, hok, List.Perm.refl _, rfl, rfl⟩
    | some oid =>
      have hm := updateSingleObject_meta s oid (fun o => o.addCounterVal k (clampNonNeg (evalNumExpr s ctrl env n (some src))))
      exact ⟨updateSingleObject_wf hwf oid _,
             updateSingleObject_ownerOk hok oid (fun o => Object.addCounterVal_owner o k _),
             by rw [updateSingleObject_physIds s oid (fun o => Object.addCounterVal_kind o k _)],
             hm.1, hm.2⟩
  | removeCounter oref k n =>
    unfold execPrim; dsimp only
    cases evalObjRef src oref with
    | none => exact ⟨hwf, hok, List.Perm.refl _, rfl, rfl⟩
    | some oid =>
      let amount := clampNonNeg (evalNumExpr s ctrl env n (some src))
      have hm := updateSingleObject_meta s oid (fun o => o.removeCounterVal k amount)
      exact ⟨updateSingleObject_wf hwf oid _,
        updateSingleObject_ownerOk hok oid (fun o => Object.removeCounterVal_owner o k _),
        by rw [updateSingleObject_physIds s oid (fun o => Object.removeCounterVal_kind o k _)],
        hm.1, hm.2⟩
  | removeAllCounters oref k =>
    unfold execPrim; dsimp only
    cases evalObjRef src oref with
    | none => exact ⟨hwf, hok, List.Perm.refl _, rfl, rfl⟩
    | some oid =>
      have hm := updateSingleObject_meta s oid (fun o => o.clearCounterVal k)
      exact ⟨updateSingleObject_wf hwf oid _,
             updateSingleObject_ownerOk hok oid (fun o => Object.clearCounterVal_owner o k),
             by rw [updateSingleObject_physIds s oid (fun o => Object.clearCounterVal_kind o k)],
             hm.1, hm.2⟩
  | discardRandom pref n =>
    unfold execPrim; dsimp only
    split
    · exact ⟨hwf, hok, List.Perm.refl _, rfl, rfl⟩
    · exact discardManyObjs_inv (evalPlayerRef s ctrl pref) _ hwf hok
  | discardHandPrefix _ =>
    exact discardManyObjs_inv ctrl _ hwf hok
  | discardChoice pref f n =>
    unfold execPrim; dsimp only
    split
    · exact ⟨hwf, hok, List.Perm.refl _, rfl, rfl⟩
    · exact discardManyObjs_inv (evalPlayerRef s ctrl pref) _ hwf hok
  | intimidate pref =>
    unfold execPrim; dsimp only
    split
    · exact ⟨hwf, hok, List.Perm.refl _, rfl, rfl⟩
    · exact intimidateHandFront_inv ctrl (evalPlayerRef s ctrl pref) hwf hok
  | intimidateHandFront target => exact intimidateHandFront_inv ctrl target hwf hok
  | returnDefendingCardToHand f =>
    unfold execPrim; dsimp only
    split <;> exact ⟨hwf, hok, List.Perm.refl _, rfl, rfl⟩
  | returnChosenDefendingCard id =>
    unfold execPrim; dsimp only
    cases s.combat.bind CombatChain.activeLink? with
    | none => exact ⟨hwf, hok, List.Perm.refl _, rfl, rfl⟩
    | some link =>
      dsimp only
      split
      · cases s.obj? id with
        | none => exact ⟨hwf, hok, List.Perm.refl _, rfl, rfl⟩
        | some o =>
          dsimp only
          cases hm : moveObj s id (.player o.owner .hand) .top false with
          | none => exact ⟨hwf, hok, List.Perm.refl _, rfl, rfl⟩
          | some res =>
            obtain ⟨s1, id'⟩ := res
            dsimp only
            have hmeta := moveObj_config_rollback hm
            have hp := moveObj_physIds hwf hm
            exact ⟨GameState.WF.congr (moveObj_wf hwf hm) rfl rfl rfl rfl,
                   GameState.OwnerOk.congr (moveObj_ownerOk hwf hok hm) rfl rfl,
                   hp, hmeta.1, hmeta.2⟩
      · exact ⟨hwf, hok, List.Perm.refl _, rfl, rfl⟩
  | searchDeck pref f maxCount dstRef _ _ _ _ =>
    unfold execPrim; dsimp only
    cases zoneOfRef (evalPlayerRef s ctrl pref) dstRef with
    | none => exact ⟨hwf, hok, List.Perm.refl _, rfl, rfl⟩
    | some _ => exact ⟨hwf, hok, List.Perm.refl _, rfl, rfl⟩
  | putHandArsenal _ _ _ _ =>
    unfold execPrim; dsimp only; split <;> exact ⟨hwf, hok, List.Perm.refl _, rfl, rfl⟩
  | searchDeckToTop _ _ _ | reload _ | lookTopToBanishedAsInstant _ _ _ => exact ⟨hwf, hok, List.Perm.refl _, rfl, rfl⟩
  | lookDeckToArsenal _ _ _ =>
    unfold execPrim; dsimp only; split <;> exact ⟨hwf, hok, List.Perm.refl _, rfl, rfl⟩
  | revealTopPairToHand pref first second =>
    let player := evalPlayerRef s ctrl pref
    let ids := matchingRevealedPair s first second ((s.zone (.player player .deck)).take 2)
    exact moveManyObjs_inv (.player player .hand) .top false ids hwf hok
  | putChosenDeckCardsOnBottom pref ids =>
    unfold execPrim; dsimp only
    split
    · rename_i valid
      have perm := deckBottomOrder_perm (s.zone (.player (evalPlayerRef s ctrl pref) .deck)) ids
      exact ⟨GameState.wf_reorder hwf valid perm, GameState.ownerOk_reorder hok perm,
        GameState.physIds_reorder valid perm, rfl, rfl⟩
    · exact ⟨hwf, hok, List.Perm.refl _, rfl, rfl⟩
  | putChosenDeckCardOnTop pref id =>
    unfold execPrim; dsimp only
    split
    · rename_i valid
      have perm := optDeckOrder_perm (s.zone (.player (evalPlayerRef s ctrl pref) .deck)) 0 id true
      exact ⟨GameState.wf_reorder hwf valid perm, GameState.ownerOk_reorder hok perm,
        GameState.physIds_reorder valid perm, rfl, rfl⟩
    · exact ⟨hwf, hok, List.Perm.refl _, rfl, rfl⟩
  | putHandPermanent _ _ _ => exact ⟨hwf, hok, List.Perm.refl _, rfl, rfl⟩
  | shuffleZone _ _ => exact ⟨hwf, hok, List.Perm.refl _, rfl, rfl⟩
  | shuffleZoneIntoDeck pref srcRef f maxCount drawSame =>
    unfold execPrim; dsimp only
    cases zoneOfRef (evalPlayerRef s ctrl pref) srcRef with
    | none => exact ⟨hwf, hok, List.Perm.refl _, rfl, rfl⟩
    | some _ => exact ⟨hwf, hok, List.Perm.refl _, rfl, rfl⟩
  | revealTopToArsenalIf pref _ =>
    unfold execPrim; dsimp only
    cases s.zone (.player (evalPlayerRef s ctrl pref) .deck) with
    | nil => exact ⟨hwf, hok, List.Perm.refl _, rfl, rfl⟩
    | cons topId _ =>
      dsimp only
      split
      · cases hm : moveObj s topId (.player (evalPlayerRef s ctrl pref) .arsenal) .top true with
        | none => exact ⟨hwf, hok, List.Perm.refl _, rfl, rfl⟩
        | some res =>
          obtain ⟨s1, id'⟩ := res
          dsimp only
          have hmeta := moveObj_config_rollback hm
          exact ⟨moveObj_wf hwf hm, moveObj_ownerOk hwf hok hm,
                 moveObj_physIds hwf hm, hmeta.1, hmeta.2⟩
      · exact ⟨hwf, hok, List.Perm.refl _, rfl, rfl⟩
  | preventNextDamage pref n _ | preventDamageOnce pref n =>
    unfold execPrim; dsimp only
    split
    · exact ⟨hwf, hok, List.Perm.refl _, rfl, rfl⟩
    · exact ⟨GameState.WF.congr hwf rfl rfl rfl rfl,
             GameState.OwnerOk.congr hok rfl rfl,
             List.Perm.refl _, rfl, rfl⟩
  | charge pref =>
    unfold execPrim; dsimp only
    cases s.zone (.player (evalPlayerRef s ctrl pref) .hand) with
    | nil => exact ⟨hwf, hok, List.Perm.refl _, rfl, rfl⟩
    | cons cid _ =>
      dsimp only
      cases hm : moveObj s cid (.player (evalPlayerRef s ctrl pref) .soul) .bottom false with
      | none => exact ⟨hwf, hok, List.Perm.refl _, rfl, rfl⟩
      | some res =>
        obtain ⟨s1, id'⟩ := res
        dsimp only
        have hmeta := moveObj_config_rollback hm
        have hp := moveObj_physIds hwf hm
        exact ⟨GameState.WF.congr (moveObj_wf hwf hm) rfl rfl rfl rfl,
               GameState.OwnerOk.congr (moveObj_ownerOk hwf hok hm) rfl rfl,
               hp, hmeta.1, hmeta.2⟩
  | banishFromSoul pref n =>
    exact banishManyObjs_inv (evalPlayerRef s ctrl pref) false _ hwf hok
  | banishTopDeck pref n fd =>
    exact banishManyObjs_inv (evalPlayerRef s ctrl pref) fd _ hwf hok
  | banishFromGraveyard pref f n =>
    exact banishManyObjs_inv (evalPlayerRef s ctrl pref) false _ hwf hok

/-- **L4** (`WF` preservation for `execPrim`): any primitive preserves `WF`. -/
theorem execPrim_wf {s : GameState} (hwf : s.WF) (hok : s.OwnerOk) (ctrl : PlayerId) (src : ObjId)
    (env : List (VarId × Int)) (p : Prim) :
    (execPrim s ctrl src env p).1.WF :=
  (execPrim_inv hwf hok ctrl src env p).1

/-- **L4** (`OwnerOk` preservation for `execPrim`): any primitive preserves `OwnerOk`. -/
theorem execPrim_ownerOk {s : GameState} (hwf : s.WF) (hok : s.OwnerOk) (ctrl : PlayerId)
    (src : ObjId) (env : List (VarId × Int)) (p : Prim) :
    (execPrim s ctrl src env p).1.OwnerOk :=
  (execPrim_inv hwf hok ctrl src env p).2.1

/-- **L4** (I1 `physIds` preservation for `execPrim`): any primitive preserves physical cards. -/
theorem execPrim_physIds {s : GameState} (hwf : s.WF) (hok : s.OwnerOk) (ctrl : PlayerId)
    (src : ObjId) (env : List (VarId × Int)) (p : Prim) :
    (execPrim s ctrl src env p).1.physIds.Perm s.physIds :=
  (execPrim_inv hwf hok ctrl src env p).2.2.1

/-- `execPrim` preserves `config` and `playRollback`. -/
theorem execPrim_meta {s : GameState} (hwf : s.WF) (hok : s.OwnerOk) (ctrl : PlayerId)
    (src : ObjId) (env : List (VarId × Int)) (p : Prim) :
    (execPrim s ctrl src env p).1.config = s.config ∧
    (execPrim s ctrl src env p).1.playRollback = s.playRollback :=
  ⟨(execPrim_inv hwf hok ctrl src env p).2.2.2.1, (execPrim_inv hwf hok ctrl src env p).2.2.2.2⟩

/-- `execPrim` preserves `turn` and `tournament`, and never clears a set `result`. -/
theorem execPrim_ttr_core (s : GameState) (ctrl : PlayerId) (src : ObjId)
    (env : List (VarId × Int)) (p : Prim) :
    (execPrim s ctrl src env p).1.turn = s.turn ∧
    (execPrim s ctrl src env p).1.tournament = s.tournament ∧
    ((execPrim s ctrl src env p).1.result = none → s.result = none) := by
  cases p with
  | draw _ _ | opt _ _ | optValue _ _ | weaponAttack | closeCombatChain | createTokenForAttackDamage _ _
  | gainLife _ _ | gainAP _ _ | gainResource _ _ | gainChi _ _ =>
    exact ⟨rfl, rfl, id⟩
  | openBoosters name =>
    cases name <;> unfold execPrim <;> dsimp only <;> split <;> exact ⟨rfl, rfl, id⟩
  | loseLife _ _ =>
    exact checkHeroDefeat_ttr_core _
  | dealDamage kind pref n =>
    unfold execPrim
    dsimp only
    split
    · exact ⟨rfl, rfl, id⟩
    · exact applyDamageWithPrevention_ttr s (evalPlayerRef s ctrl pref) kind
        (modifiedDamageAmount s src kind (clampNonNeg (evalNumExpr s ctrl env n (some src))))
        (some (ctrl, src))
  | dealArcaneDamageToPair _ _ _ => exact ⟨rfl, rfl, id⟩
  | createToken pref tokId n =>
    have hc : ∀ (k : Nat) (st : GameState),
        (createTokens st (evalPlayerRef s ctrl pref) tokId k).turn = st.turn ∧
        (createTokens st (evalPlayerRef s ctrl pref) tokId k).tournament = st.tournament ∧
        (createTokens st (evalPlayerRef s ctrl pref) tokId k).result = st.result := by
      intro k
      induction k with
      | zero => intro _; exact ⟨rfl, rfl, rfl⟩
      | succ k ih =>
        intro st
        unfold createTokens; dsimp only
        cases ha : addObject st (.player (evalPlayerRef s ctrl pref) .permanent)
            { kind := .token tokId, owner := evalPlayerRef s ctrl pref,
              controller := evalPlayerRef s ctrl pref, timestamp := ⟨st.nextTimestamp⟩ } .top with
        | none => exact ⟨rfl, rfl, rfl⟩
        | some res =>
          have h1 : res.1.turn = st.turn ∧ res.1.tournament = st.tournament ∧ res.1.result = st.result := by
            unfold addObject at ha; split at ha
            · simp only [Option.some.injEq] at ha; subst ha; exact ⟨rfl, rfl, rfl⟩
            · cases ha
          have h2 := ih res.1
          exact ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.trans h1.2.2⟩
    have h := hc (tokenCreationCount s (evalPlayerRef s ctrl pref) tokId n) s
    exact ⟨h.1, h.2.1, fun hr => h.2.2 ▸ hr⟩
  | destroy oref =>
    unfold execPrim; dsimp only
    cases evalObjRef src oref with
    | none => exact ⟨rfl, rfl, id⟩
    | some oid =>
      dsimp only
      split
      · rename_i srcZ o _ _
        cases hm : moveRuleObj s oid (.player o.owner .graveyard) .top false with
        | none => exact ⟨rfl, rfl, id⟩
        | some _ =>
          have h := moveObj_ttr_core hm
          exact ⟨h.1, h.2.1, fun hr => h.2.2 ▸ hr⟩
      · exact ⟨rfl, rfl, id⟩
  | banish oref fd =>
    unfold execPrim; dsimp only
    cases evalObjRef src oref with
    | none => exact ⟨rfl, rfl, id⟩
    | some oid =>
      dsimp only
      cases hb : banishOne s oid fd with
      | none => exact ⟨rfl, rfl, id⟩
      | some res =>
        obtain ⟨s1, _, _⟩ := res; dsimp only
        unfold banishOne at hb; split at hb
        · rename_i src0 o0 _ _
          dsimp only at hb
          cases hm : moveObj s oid (Zone.player o0.owner .banished) .top fd with
          | none => rw [hm] at hb; cases hb
          | some rm =>
            obtain ⟨sm, idm⟩ := rm
            rw [hm] at hb; simp only [Option.some.injEq, Prod.mk.injEq] at hb
            obtain ⟨rfl, rfl, rfl⟩ := hb
            have h := moveObj_ttr_core hm
            exact ⟨h.1, h.2.1, fun hr => h.2.2 ▸ hr⟩
        · cases hb
  | moveCard oref dstRef dpos fd =>
    unfold execPrim; dsimp only
    cases evalObjRef src oref with
    | none => exact ⟨rfl, rfl, id⟩
    | some oid =>
      dsimp only
      split
      · rename_i srcZ o _ _
        cases zoneOfRef o.owner dstRef with
        | none => exact ⟨rfl, rfl, id⟩
        | some dstZ =>
          dsimp only
          split
          · rename_i s1 oid' hm
            have h := moveObj_ttr_core hm
            exact ⟨h.1, h.2.1, fun hr => h.2.2 ▸ hr⟩
          · exact ⟨rfl, rfl, id⟩
      · exact ⟨rfl, rfl, id⟩
  | putHandOnDeck _ _ =>
    unfold execPrim; dsimp only; split <;> exact ⟨rfl, rfl, id⟩
  | cycleArsenal pref subtype _ =>
    unfold execPrim
    dsimp only
    let player := evalPlayerRef s ctrl pref
    cases s.zone (.player player .arsenal) with
    | nil => exact ⟨rfl, rfl, id⟩
    | cons stored _ =>
      dsimp only
      cases hc : moveObj s stored (.player player .deck) .bottom false with
      | none => exact ⟨rfl, rfl, id⟩
      | some moved =>
        obtain ⟨cycled, bottom⟩ := moved
        dsimp only
        have hmc := moveObj_ttr_core hc
        cases cycled.zone (.player player .deck) with
        | nil => exact ⟨hmc.1, hmc.2.1, fun hr => hmc.2.2 ▸ hr⟩
        | cons top _ =>
          dsimp only
          cases hl : moveObj cycled top (.player player .arsenal) .top false with
          | none => exact ⟨hmc.1, hmc.2.1, fun hr => hmc.2.2 ▸ hr⟩
          | some loadedCard =>
            obtain ⟨loaded, loadedId⟩ := loadedCard
            dsimp only
            have hml := moveObj_ttr_core hl
            split <;>
              exact ⟨hml.1.trans hmc.1, hml.2.1.trans hmc.2.1, fun hr => hmc.2.2 ▸ hml.2.2 ▸ hr⟩
  | putArsenalOnDeckBottom pref =>
    unfold execPrim; dsimp only
    cases s.zone (.player (evalPlayerRef s ctrl pref) .arsenal) with
    | nil => exact ⟨rfl, rfl, id⟩
    | cons aid _ =>
      dsimp only
      cases hm : moveObj s aid (.player (evalPlayerRef s ctrl pref) .deck) .bottom false with
      | none => exact ⟨rfl, rfl, id⟩
      | some _ =>
        have h := moveObj_ttr_core hm
        exact ⟨h.1, h.2.1, fun hr => h.2.2 ▸ hr⟩
  | addCounter oref _ _ =>
    unfold execPrim; dsimp only
    cases evalObjRef src oref with
    | none => exact ⟨rfl, rfl, id⟩
    | some oid =>
      dsimp only; unfold updateSingleObject
      cases s.objects[oid.n]? <;> exact ⟨rfl, rfl, id⟩
  | removeCounter oref _ _ | removeAllCounters oref _ =>
    unfold execPrim; dsimp only
    cases evalObjRef src oref with
    | none => exact ⟨rfl, rfl, id⟩
    | some oid =>
      dsimp only; unfold updateSingleObject
      cases s.objects[oid.n]? <;> exact ⟨rfl, rfl, id⟩
  | discardRandom pref n =>
    unfold execPrim; dsimp only
    split
    · exact ⟨rfl, rfl, id⟩
    · have h := discardManyObjs_ttr (evalPlayerRef s ctrl pref)
        ((s.zone (.player (evalPlayerRef s ctrl pref) .hand)).take
          (clampNonNeg (evalNumExpr s ctrl env n (some src)))) s
      exact ⟨h.1, h.2.1, fun hr => h.2.2 ▸ hr⟩
  | discardHandPrefix cnt =>
    have h := discardManyObjs_ttr ctrl ((s.zone (.player ctrl .hand)).take cnt) s
    exact ⟨h.1, h.2.1, fun hr => h.2.2 ▸ hr⟩
  | discardChoice pref f n =>
    unfold execPrim; dsimp only
    split
    · exact ⟨rfl, rfl, id⟩
    ·
      have h := discardManyObjs_ttr (evalPlayerRef s ctrl pref)
        (((s.zone (.player (evalPlayerRef s ctrl pref) .hand)).filter fun id =>
            match s.objectFace? id with | some face => cardFaceMatches f face | none => false).take
          (clampNonNeg (evalNumExpr s ctrl env n (some src)))) s
      exact ⟨h.1, h.2.1, fun hr => h.2.2 ▸ hr⟩
  | intimidate pref =>
    unfold execPrim; dsimp only
    split
    · exact ⟨rfl, rfl, id⟩
    · exact intimidateHandFront_ttr s ctrl (evalPlayerRef s ctrl pref)
  | intimidateHandFront target => exact intimidateHandFront_ttr s ctrl target
  | returnDefendingCardToHand f =>
    unfold execPrim; dsimp only
    split <;> exact ⟨rfl, rfl, id⟩
  | returnChosenDefendingCard did =>
    unfold execPrim; dsimp only
    cases s.combat.bind CombatChain.activeLink? with
    | none => exact ⟨rfl, rfl, id⟩
    | some link =>
      dsimp only
      split
      · cases s.obj? did with
        | none => exact ⟨rfl, rfl, id⟩
        | some o =>
          dsimp only
          cases hm : moveObj s did (.player o.owner .hand) .top false with
          | none => exact ⟨rfl, rfl, id⟩
          | some _ =>
            have h := moveObj_ttr_core hm
            exact ⟨h.1, h.2.1, fun hr => h.2.2 ▸ hr⟩
      · exact ⟨rfl, rfl, id⟩
  | searchDeck pref f maxCount dstRef _ _ _ _ =>
    unfold execPrim; dsimp only
    cases zoneOfRef (evalPlayerRef s ctrl pref) dstRef with
    | none => exact ⟨rfl, rfl, id⟩
    | some _ => exact ⟨rfl, rfl, id⟩
  | putHandArsenal _ _ _ _ =>
    unfold execPrim; dsimp only; split <;> exact ⟨rfl, rfl, id⟩
  | searchDeckToTop _ _ _ | reload _ | lookTopToBanishedAsInstant _ _ _ => exact ⟨rfl, rfl, id⟩
  | revealTopPairToHand pref first second =>
    let player := evalPlayerRef s ctrl pref
    let ids := matchingRevealedPair s first second ((s.zone (.player player .deck)).take 2)
    have ht := moveManyObjs_ttr (.player player .hand) .top false ids s
    exact ⟨ht.1, ht.2.1, fun hr => ht.2.2 ▸ hr⟩
  | putChosenDeckCardOnTop _ _ | lookDeckToArsenal _ _ _ | putChosenDeckCardsOnBottom _ _ =>
    unfold execPrim; dsimp only; split <;> exact ⟨rfl, rfl, id⟩
  | putHandPermanent _ _ _ => exact ⟨rfl, rfl, id⟩
  | shuffleZone _ _ => exact ⟨rfl, rfl, id⟩
  | shuffleZoneIntoDeck pref srcRef f maxCount _ =>
    unfold execPrim; dsimp only
    cases zoneOfRef (evalPlayerRef s ctrl pref) srcRef with
    | none => exact ⟨rfl, rfl, id⟩
    | some _ => exact ⟨rfl, rfl, id⟩
  | revealTopToArsenalIf pref _ =>
    unfold execPrim; dsimp only
    cases s.zone (.player (evalPlayerRef s ctrl pref) .deck) with
    | nil => exact ⟨rfl, rfl, id⟩
    | cons topId _ =>
      dsimp only
      split
      · cases hm : moveObj s topId (.player (evalPlayerRef s ctrl pref) .arsenal) .top true with
        | none => exact ⟨rfl, rfl, id⟩
        | some _ =>
          have h := moveObj_ttr_core hm
          exact ⟨h.1, h.2.1, fun hr => h.2.2 ▸ hr⟩
      · exact ⟨rfl, rfl, id⟩
  | preventNextDamage _ _ _ | preventDamageOnce _ _ =>
    unfold execPrim; dsimp only; split <;> exact ⟨rfl, rfl, id⟩
  | charge pref =>
    unfold execPrim; dsimp only
    cases s.zone (.player (evalPlayerRef s ctrl pref) .hand) with
    | nil => exact ⟨rfl, rfl, id⟩
    | cons cid _ =>
      dsimp only
      cases hm : moveObj s cid (.player (evalPlayerRef s ctrl pref) .soul) .bottom false with
      | none => exact ⟨rfl, rfl, id⟩
      | some _ =>
        have h := moveObj_ttr_core hm
        exact ⟨h.1, h.2.1, fun hr => h.2.2 ▸ hr⟩
  | banishFromSoul pref n =>
    have h := banishManyObjs_ttr (evalPlayerRef s ctrl pref) false
      ((s.zone (.player (evalPlayerRef s ctrl pref) .soul)).take n) s
    exact ⟨h.1, h.2.1, fun hr => h.2.2 ▸ hr⟩
  | banishTopDeck pref n fd =>
    have h := banishManyObjs_ttr (evalPlayerRef s ctrl pref) fd
      ((s.zone (.player (evalPlayerRef s ctrl pref) .deck)).take n) s
    exact ⟨h.1, h.2.1, fun hr => h.2.2 ▸ hr⟩
  | banishFromGraveyard pref f n =>
    have h := banishManyObjs_ttr (evalPlayerRef s ctrl pref) false
      (((s.zone (.player (evalPlayerRef s ctrl pref) .graveyard)).filter fun id =>
          match s.objectFace? id with | some face => cardFaceMatches f face | none => false).take n) s
    exact ⟨h.1, h.2.1, fun hr => h.2.2 ▸ hr⟩

/-- Whether an effect scope designates the source object itself. -/
def ModScope.isSelf : ModScope → Bool
  | .self_ | .obj .self_ => true
  | _ => false

/-- Whether a layer is eligible to have Go Again under active player restrictions (CR 8.3.5). -/
def layerCanGainGoAgain (s : GameState) (id : ObjId) (p : PlayerId) : Bool :=
  if !s.hasActionPhaseEffect p .cantGainGoAgain then true else
  match (s.obj? id).map Object.kind with
  | some (.attackProxy _ _) => false
  | some (.layer _ _ _ triggered) => triggered
  | _ => !(s.characteristics id).any (fun c => c.types.contains .action)

/-- Modify the source action or the paid attack bound to a trigger (CR 5.3.5, 8.3.5). -/
def modifyPendingAction (s : GameState) (ctrl : PlayerId) (src : ObjId)
    (env : List (VarId × Int)) (scope : ModScope) (mod : ContinuousMod) (dur : Duration) :
    Option (ObjId × LayerInfo) := do
  let target ← match scope with
    | .self_ | .obj .self_ => some src
    | .paidAttack id => some id
    | _ => none
  if s.locate target != some .stack then none else
    let info ← s.layerMeta.get? target.n
    let isProxy := (s.obj? target).any fun o => match o.kind with
      | .attackProxy _ _ => true
      | _ => false
    let face := (s.cardDefOf? target).map (·.front)
    let isAttack := isProxy || face.any (fun f => f.hasType .action && f.hasSubtype .attack)
    let bindsAttack := dur == .thisChainLink || (dur == .thisTurn && !scope.isSelf)
    match isAttack, bindsAttack, dur, mod with
    | true, true, _, .addPower d =>
      some (target, { info with attackPowerBonus := info.attackPowerBonus + evalNumExpr s ctrl env d (some src) })
    | true, true, _, .grantKeyword kw =>
      if kw == .goAgain && !layerCanGainGoAgain s target info.controller then some (target, info)
      else some (target, { info with attackKeywords := insertUnique kw info.attackKeywords })
    | false, _, .thisTurn, .grantKeyword .goAgain =>
      if scope.isSelf && face.any (·.hasType .action) then
        some (target, { info with goAgain := layerCanGainGoAgain s target info.controller })
      else none
    | _, _, _, _ => none

/-- Put a resolving defense reaction's self-granted defense on the card (CR 5.3.4, 6.3.2h). -/
def defenseReactionGrant (s : GameState) (ctrl : PlayerId) (src : ObjId)
    (env : List (VarId × Int)) (scope : ModScope) (mod : ContinuousMod) (dur : Duration) :
    Option ContinuousEffect := do
  let .addDefense delta := mod | none
  if dur != .thisChainLink || !scope.isSelf || s.locate src != some .stack then none else
    let face ← s.objectFace? src
    if !face.hasType .defenseReaction then none else
      some { id := s.nextTimestamp
             source := src
             controller := ctrl
             target := .obj src
             op := .addDefense (evalNumExpr s ctrl env delta (some src))
             duration := dur
             timestamp := ⟨s.nextTimestamp⟩ }

/-- Recheck the identity and eligibility of the declared attack before applying a targeted effect. -/
def declaredAttackStillMatches (s : GameState) (src : ObjId) (link : ChainLink) : Bool :=
  (do
    let info ← s.layerMeta.get? src.n
    let target ← info.attackTarget
    let card ← s.cardDefOf? src
    let spec ← singleAttackTargetSpec card info.modeIdx
    pure (matchingActiveAttack s link spec == some target) : Option Bool).getD false

/-- Match a player restriction and the scope on which it can be scheduled (CR 4.3, 6.2). -/
def actionPhaseRestriction? (scope : ModScope) (mod : ContinuousMod) : Option (PlayerRef × EffectOp) :=
  match scope, mod with
  | .hero player, .cantDrawCards => some (player, .cantDrawCards)
  | .playerActionsAndAttacks player, .cantGainGoAgain => some (player, .cantGainGoAgain)
  | .playerActionsAndAttacks player, .limitActions count => some (player, .limitActions count)
  | _, _ => none

/-- Apply combat buffs to a pending attack card or the active `ChainLink`, and register
turn- and chain-scoped continuous effects in `s.activeEffects` (CR 6.2-6.3, 7.4). -/
def applyChainLinkMod (s : GameState) (ctrl : PlayerId) (src : ObjId)
    (env : List (VarId × Int)) (scope : ModScope) (mod : ContinuousMod) (dur : Duration) : GameState :=
  if let some (target, info) := modifyPendingAction s ctrl src env scope mod dur then
    { s with layerMeta := s.layerMeta.insert target.n info }
  else if let some effect := defenseReactionGrant s ctrl src env scope mod dur then
    { s with activeEffects := s.activeEffects ++ [effect], nextTimestamp := s.nextTimestamp + 1 }
  else match dur, s.combat with
  | .thisChainLink, some cc =>
    let cc' := cc.updateActiveLink fun link =>
      let targetSlotOk := match scope with
        | .obj (.slot i) => i == 0 && declaredAttackStillMatches s src link
        | .paidAttack id => link.attack == some id
        | _ => true
      let targetsAttack := match scope with
        | .self_ | .obj .self_ => link.attack == some src
        | .obj .currentAttack => link.attack.isSome
        | .obj (.slot _) | .paidAttack _ => targetSlotOk
        | _ => false
      if !targetSlotOk then link else match mod with
      | .addPower d => { link with powerBonus := link.powerBonus + evalNumExpr s ctrl env d (some src) }
      | .addDefense d => { link with defenseBonus := link.defenseBonus + evalNumExpr s ctrl env d (some src) }
      | .grantKeyword kw =>
        if scope.isSelf && !targetsAttack then link
        else if kw == .goAgain then
          if s.hasActionPhaseEffect link.attacker .cantGainGoAgain || link.attackLki.keywords.contains kw then link
          else { link with grantedKeywords := insertUnique kw link.grantedKeywords }
        else { link with grantedKeywords := kw :: link.grantedKeywords }
      | .doubleDamageToHero =>
        if targetsAttack then { link with damageMultiplier := link.damageMultiplier * 2 } else link
      | .grantTrigger trigger cond body =>
        if targetsAttack then
          { link with grantedAbilities := link.grantedAbilities ++
              [.triggered trigger false none cond { body := body }] }
        else link
      | _ => link
    { s with combat := some cc' }
  | .nextActionPhase, _ =>
    match actionPhaseRestriction? scope mod with
    | some (player, op) =>
      let effect : ContinuousEffect :=
        { id := s.nextTimestamp, source := src, controller := ctrl
          target := .player (evalPlayerRef s ctrl player), op := op
          duration := .nextActionPhase, timestamp := ⟨s.nextTimestamp⟩ }
      { s with activeEffects := s.activeEffects ++ [effect], nextTimestamp := s.nextTimestamp + 1 }
    | none => s
  | .untilEndOfNextTurn, _ =>
    let timed : Option (PlayerId × EffectTarget × EffectOp × Bool) := match scope, mod with
      | .hero player, .loseAllAbilities =>
        let affected := evalPlayerRef s ctrl player
        some (affected, .objects (s.zone (.player affected .hero)), .loseAllAbilities, false)
      | .firstAttackNextTurn player, .addPower delta =>
        let affected := evalPlayerRef s ctrl player
        some (affected, .nextAttackBy affected, .addPower (evalNumExpr s ctrl env delta (some src)), true)
      | .firstAttackNextTurn player, .modifyCost delta =>
        if 0 < delta then
          let affected := evalPlayerRef s ctrl player
          some (affected, .nextAttackBy affected, .addCostRes delta.toNat, true)
        else none
      | .firstActionNextTurn player, .modifyCost delta =>
        if 0 < delta then
          let affected := evalPlayerRef s ctrl player
          some (affected, .nextActionBy affected, .addCostRes delta.toNat, true)
        else none
      | _, _ => none
    match timed with
    | some (affected, target, op, waits) =>
      let effect : ContinuousEffect :=
        { id := s.nextTimestamp, source := src, controller := ctrl
          target := target, op := op
          duration := dur, endAfterTurnOf := some (affected, s.turn), waitsForNextTurn := waits
          timestamp := ⟨s.nextTimestamp⟩ }
      { s with activeEffects := s.activeEffects ++ [effect], nextTimestamp := s.nextTimestamp + 1 }
    | none => s
  | .thisTurn, _ | .thisCombatChain, _ =>
    let weaponTarget := (s.layerMeta.get? src.n).bind (·.weaponTarget)
    let op? : Option EffectOp :=
      match mod with
      | .addPower d => some (.addPower (evalNumExpr s ctrl env d (some src)))
      | .addDefense d => some (.addDefense (evalNumExpr s ctrl env d (some src)))
      | .addIntellect d => some (.addIntellect d)
      | .additionalWeaponAttack => some .allowWeaponAttack
      | .onlyPlayFromArsenal =>
        match scope with
        | .player _ => some .onlyPlayFromArsenal
        | _ => none
      | .modifyCost d =>
        if 0 ≤ d then some (.addCostRes d.toNat) else some (.subCostRes (-d).toNat)
      | .addTokenCreation token amount => some (.addTokenCreation token amount)
      | .addToNextArcaneCard amount => some (.addToNextArcaneCard amount)
      | .nextCardAsInstant filter bonus => some (.nextCardAsInstant filter bonus)
      | .grantKeyword kw => some (.grantKeyword kw)
      | .grantTrigger trigger cond body =>
        match scope with
        | .nextAttack _ | .paidAttack _ =>
          some (.grantAttackAbility (.triggered trigger false none cond { body := body }))
        | .obj (.slot 0) =>
          weaponTarget.map (fun _ => .grantAttackAbility (.triggered trigger false none cond { body := body }))
        | _ => none
      | .conditionalPower (.defendedByFewerNonEquip limit) bonus =>
        match scope with
        | .nextAttack _ => some (.addPowerIfFewerDefenders limit bonus)
        | _ => none
      | _ => none
    match op? with
    | some op =>
      let target : EffectTarget := match scope, op with
        | .nextCardPlayed filter, .addPower _
        | .nextCardPlayed filter, .addCostRes _
        | .nextCardPlayed filter, .subCostRes _ => .nextAttackCard filter
        | .nextAttack filter, .addPower _
        | .nextAttack filter, .grantKeyword _
        | .nextAttack filter, .grantAttackAbility _
        | .nextAttack filter, .addPowerIfFewerDefenders _ _ => .nextAttack filter
        | .nextDefend filter, .addDefense _ => .nextDefend filter
        | .allAttacks filter, .addPower _ => .allAttacks filter
        | .self_, .addPower _ | .obj .self_, .addPower _ =>
          if s.locate src == some (.player ctrl .arsenal) &&
              (s.obj? src).any (fun card => !card.faceDown) then .arsenalCard src else .obj src
        | .self_, .grantKeyword _ | .obj .self_, .grantKeyword _ => .obj src
        | .obj .currentAttack, .allowWeaponAttack =>
          (((s.combat.bind CombatChain.activeLink?).bind (·.attackSource)).map EffectTarget.obj).getD (.objects [])
        | .player player, .onlyPlayFromArsenal => .player (evalPlayerRef s ctrl player)
        | .player player, .addTokenCreation _ _ | .player player, .addToNextArcaneCard _
        | .player player, .nextCardAsInstant _ _ =>
          .player (evalPlayerRef s ctrl player)
        | .hero player, .addIntellect _ =>
          .objects (s.zone (.player (evalPlayerRef s ctrl player) .hero))
        | .allMatching player filter, _ => .matchingCard (evalPlayerRef s ctrl player) filter
        | .paidAttack id, _ => .obj id
        | .obj (.slot 0), _ => (weaponTarget.map EffectTarget.obj).getD (.objects [])
        | .targetedWeaponAttacks, _ => (weaponTarget.map EffectTarget.weaponAttacks).getD (.objects [])
        | .arenaObjectsOfType player kind, _ =>
          let affected := evalPlayerRef s ctrl player
          let arena := (allZones s.playerCount).filter Zone.isArena
          .objects ((arena.flatMap s.zone).filter fun id =>
            (s.obj? id).any (fun obj => !obj.faceDown) &&
            (s.characteristics id).any (fun c => c.controller == affected && c.types.contains kind))
        | _, _ => .matching (ctrl := some ctrl)
      let eff : ContinuousEffect :=
        { id := s.nextTimestamp
          source := src
          controller := ctrl
          target := target
          op := op
          duration := dur
          timestamp := ⟨s.nextTimestamp⟩ }
      { s with
        activeEffects := s.activeEffects ++ [eff]
        nextTimestamp := s.nextTimestamp + 1 }
    | none => s
  | _, _ => s

/-- `applyChainLinkMod` preserves the board structure and `playRollback`. -/
theorem applyChainLinkMod_fields (s : GameState) (ctrl : PlayerId) (src : ObjId)
    (env : List (VarId × Int)) (scope : ModScope) (mod : ContinuousMod) (dur : Duration) :
    (applyChainLinkMod s ctrl src env scope mod dur).config = s.config ∧
    (applyChainLinkMod s ctrl src env scope mod dur).objects = s.objects ∧
    (applyChainLinkMod s ctrl src env scope mod dur).zones = s.zones ∧
    (applyChainLinkMod s ctrl src env scope mod dur).nextId = s.nextId ∧
    (applyChainLinkMod s ctrl src env scope mod dur).playRollback = s.playRollback := by
  unfold applyChainLinkMod
  split
  · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · split
    · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    · cases dur <;> cases s.combat <;>
      first
      | exact ⟨rfl, rfl, rfl, rfl, rfl⟩
      | (dsimp only; split <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩)

/-- Execute a single step of `Frame.run ctrl src fromArsenal env todo :: rest` (CR 1.7, 6.0).
Always succeeds (total), never returning `none`. -/
def interpRunStep (s : GameState) (ctrl : PlayerId) (src : ObjId) (fromArsenal : Bool)
    (env : List (VarId × Int)) (todo : List Effect) (rest : List Frame) :
    GameState × List Event :=
  match todo with
  | [] => ({ s with pending := rest }, [])
  | .nop :: more =>
    ({ s with pending := .run ctrl src fromArsenal env more :: rest }, [])
  | .prim p :: more =>
    let (s1, es, extra) := execPrim s ctrl src env p
    ({ s1 with pending := extra ++ [.run ctrl src fromArsenal env more] ++ rest }, es)
  | .seq es :: more =>
    ({ s with pending := .run ctrl src fromArsenal env (es.toList ++ more) :: rest }, [])
  | .ifThen cond t e :: more =>
    let chosen := if evalCondition s ctrl src fromArsenal cond then t else e
    ({ s with pending := .run ctrl src fromArsenal env (chosen :: more) :: rest }, [])
  | .may body ifDone :: more =>
    ({ s with
        pending := .chooseMay ctrl src fromArsenal env body ifDone ::
          .run ctrl src fromArsenal env more :: rest }, [])
  | .chooseOne modes :: more =>
    let ms := modes.toList
    if ms.isEmpty then
      ({ s with pending := .run ctrl src fromArsenal env more :: rest }, [])
    else
      ({ s with
          pending := .chooseModal ctrl src fromArsenal env ms ::
            .run ctrl src fromArsenal env more :: rest }, [])
  | .rollDie6 bindVar branches cont :: more =>
    ({ s with
        pending := .chanceDie6 ctrl src fromArsenal env bindVar branches cont ::
          .run ctrl src fromArsenal env more :: rest }, [])
  | .bindRevealTopCount pref n f bindVar cont :: more =>
    let target := evalPlayerRef s ctrl pref
    let topN := (s.zone (.player target .deck)).take n
    let revealed := topN.filterMap fun id =>
      (s.cardDefOf? id).map fun card => Event.revealed target id card.id
    let matched := topN.countP fun id =>
      (s.objectFace? id).any (cardFaceMatches f)
    ({ s with
        pending := .run ctrl src fromArsenal ((bindVar, Int.ofNat matched) :: env) [cont] ::
          .run ctrl src fromArsenal env more :: rest }, revealed)
  | .bindBanishTopCount pref n filter bindVar cont :: more =>
    let player := evalPlayerRef s ctrl pref
    let top := (s.zone (.player player .deck)).take n
    let (banished, events) := banishManyObjs s player false top
    let matched := events.countP fun
      | .banished _ id false => (banished.objectFace? id).any (cardFaceMatches filter)
      | _ => false
    ({ banished with
        pending := .run ctrl src fromArsenal ((bindVar, Int.ofNat matched) :: env) [cont] ::
          .run ctrl src fromArsenal env more :: rest }, events)
  | .onBoostThisTurn body :: more =>
    let delayed : DelayedTrigger :=
      { id := s.nextTimestamp
        controller := ctrl
        source := src
        sourceLki := some (captureLki s src ctrl)
        watch := .boostThisTurn s.turn
        effect := body }
    ({ s with
        delayedTriggers := s.delayedTriggers ++ [delayed]
        nextTimestamp := s.nextTimestamp + 1
        pending := .run ctrl src fromArsenal env more :: rest }, [])
  | .discardTopOfHand pref filter ifMatches otherwise :: more =>
    let player := evalPlayerRef s ctrl pref
    let (discarded, events) := discardManyObjs s player ((s.zone (.player player .hand)).take 1)
    let matched := events.any fun
      | .discarded _ id => (discarded.objectFace? id).any (cardFaceMatches filter)
      | _ => false
    let next := if matched then ifMatches else otherwise
    ({ discarded with pending := .run ctrl src fromArsenal env (next :: more) :: rest }, events)
  | .discardChosen pref eligible classify ifMatches otherwise :: more =>
    let player := evalPlayerRef s ctrl pref
    let choices := (s.zone (.player player .hand)).filter fun id =>
      (s.objectFace? id).any (cardFaceMatches eligible)
    let extra := if choices.isEmpty then [] else
      [.chooseDiscard player 1 choices [] (some ⟨ctrl, src, fromArsenal, env, classify, ifMatches, otherwise⟩)]
    ({ s with pending := extra ++ [.run ctrl src fromArsenal env more] ++ rest }, [])
  | .grant scope mod dur :: more =>
    let s1 := applyChainLinkMod s ctrl src env scope mod dur
    ({ s1 with pending := .run ctrl src fromArsenal env more :: rest }, [])
  | .custom _ _ :: more =>
    ({ s with pending := .run ctrl src fromArsenal env more :: rest }, [])

/-- **L4** (`WF` preservation for `interpRunStep`): stepping any `Effect` preserves `WF`. -/
theorem interpRunStep_wf {s : GameState} (hwf : s.WF) (hok : s.OwnerOk) (ctrl : PlayerId)
    (src : ObjId) (fromArsenal : Bool) (env : List (VarId × Int)) (todo : List Effect)
    (rest : List Frame) :
    (interpRunStep s ctrl src fromArsenal env todo rest).1.WF := by
  cases todo with
  | nil => exact GameState.WF.congr hwf rfl rfl rfl rfl
  | cons eff more =>
    cases eff with
    | nop | seq _ | ifThen _ _ _ | may _ _ | rollDie6 _ _ _ | bindRevealTopCount _ _ _ _ _
    | onBoostThisTurn _ | discardChosen _ _ _ _ _ | custom _ _ =>
      exact GameState.WF.congr hwf rfl rfl rfl rfl
    | bindBanishTopCount pref n _ _ _ =>
      let target := evalPlayerRef s ctrl pref
      have h := banishManyObjs_inv target false ((s.zone (.player target .deck)).take n) hwf hok
      exact GameState.WF.congr h.1 rfl rfl rfl rfl
    | discardTopOfHand pref _ _ _ =>
      exact GameState.WF.congr (discardManyObjs_inv (evalPlayerRef s ctrl pref) _ hwf hok).1 rfl rfl rfl rfl
    | grant scope mod dur =>
      have hf := applyChainLinkMod_fields s ctrl src env scope mod dur
      exact GameState.WF.congr hwf hf.1 hf.2.1 hf.2.2.1 hf.2.2.2.1
    | chooseOne modes =>
      unfold interpRunStep; dsimp only
      split <;> exact GameState.WF.congr hwf rfl rfl rfl rfl
    | prim p =>
      unfold interpRunStep
      exact GameState.WF.congr (execPrim_wf hwf hok ctrl src env p) rfl rfl rfl rfl

/-- **L4** (`OwnerOk` preservation for `interpRunStep`): stepping any `Effect` preserves `OwnerOk`. -/
theorem interpRunStep_ownerOk {s : GameState} (hwf : s.WF) (hok : s.OwnerOk) (ctrl : PlayerId)
    (src : ObjId) (fromArsenal : Bool) (env : List (VarId × Int)) (todo : List Effect)
    (rest : List Frame) :
    (interpRunStep s ctrl src fromArsenal env todo rest).1.OwnerOk := by
  cases todo with
  | nil => exact GameState.OwnerOk.congr hok rfl rfl
  | cons eff more =>
    cases eff with
    | nop | seq _ | ifThen _ _ _ | may _ _ | rollDie6 _ _ _ | bindRevealTopCount _ _ _ _ _
    | onBoostThisTurn _ | discardChosen _ _ _ _ _ | custom _ _ =>
      exact GameState.OwnerOk.congr hok rfl rfl
    | bindBanishTopCount pref n _ _ _ =>
      let target := evalPlayerRef s ctrl pref
      have h := banishManyObjs_inv target false ((s.zone (.player target .deck)).take n) hwf hok
      exact GameState.OwnerOk.congr h.2.1 rfl rfl
    | discardTopOfHand pref _ _ _ =>
      exact GameState.OwnerOk.congr (discardManyObjs_inv (evalPlayerRef s ctrl pref) _ hwf hok).2.1 rfl rfl
    | grant scope mod dur =>
      have hf := applyChainLinkMod_fields s ctrl src env scope mod dur
      exact GameState.OwnerOk.congr hok hf.2.1 hf.2.2.1
    | chooseOne modes =>
      unfold interpRunStep; dsimp only
      split <;> exact GameState.OwnerOk.congr hok rfl rfl
    | prim p =>
      unfold interpRunStep
      exact GameState.OwnerOk.congr (execPrim_ownerOk hwf hok ctrl src env p) rfl rfl

/-- **L4** (I1 `physIds` preservation for `interpRunStep`): stepping any `Effect` preserves physical
cards. -/
theorem interpRunStep_physIds {s : GameState} (hwf : s.WF) (hok : s.OwnerOk) (ctrl : PlayerId)
    (src : ObjId) (fromArsenal : Bool) (env : List (VarId × Int)) (todo : List Effect)
    (rest : List Frame) :
    (interpRunStep s ctrl src fromArsenal env todo rest).1.physIds.Perm s.physIds := by
  cases todo with
  | nil => exact List.Perm.refl _
  | cons eff more =>
    cases eff with
    | nop | seq _ | ifThen _ _ _ | may _ _ | rollDie6 _ _ _ | bindRevealTopCount _ _ _ _ _
    | onBoostThisTurn _ | discardChosen _ _ _ _ _ | custom _ _ =>
      exact List.Perm.refl _
    | bindBanishTopCount pref n _ _ _ =>
      let target := evalPlayerRef s ctrl pref
      have h := banishManyObjs_inv target false ((s.zone (.player target .deck)).take n) hwf hok
      exact h.2.2.1
    | discardTopOfHand pref _ _ _ =>
      exact (discardManyObjs_inv (evalPlayerRef s ctrl pref) _ hwf hok).2.2.1
    | grant scope mod dur =>
      have hf := applyChainLinkMod_fields s ctrl src env scope mod dur
      have hp : (interpRunStep s ctrl src fromArsenal env (.grant scope mod dur :: more) rest).1.physIds =
          s.physIds := by
        unfold interpRunStep GameState.physIds GameState.zoneIds GameState.playerCount GameState.zone GameState.obj?
        simp only [hf.1, hf.2.1, hf.2.2.1]
      rw [hp]
    | chooseOne modes =>
      unfold interpRunStep; dsimp only
      split <;> exact List.Perm.refl _
    | prim p =>
      unfold interpRunStep
      exact execPrim_physIds hwf hok ctrl src env p

/-- `interpRunStep` preserves `config` and `playRollback`. -/
theorem interpRunStep_meta {s : GameState} (hwf : s.WF) (hok : s.OwnerOk) (ctrl : PlayerId)
    (src : ObjId) (fromArsenal : Bool) (env : List (VarId × Int)) (todo : List Effect)
    (rest : List Frame) :
    (interpRunStep s ctrl src fromArsenal env todo rest).1.config = s.config ∧
    (interpRunStep s ctrl src fromArsenal env todo rest).1.playRollback = s.playRollback := by
  cases todo with
  | nil => exact ⟨rfl, rfl⟩
  | cons eff more =>
    cases eff with
    | nop | seq _ | ifThen _ _ _ | may _ _ | rollDie6 _ _ _ | bindRevealTopCount _ _ _ _ _
    | onBoostThisTurn _ | discardChosen _ _ _ _ _ | custom _ _ =>
      exact ⟨rfl, rfl⟩
    | bindBanishTopCount pref n _ _ _ =>
      let target := evalPlayerRef s ctrl pref
      have h := banishManyObjs_inv target false ((s.zone (.player target .deck)).take n) hwf hok
      exact h.2.2.2
    | discardTopOfHand pref _ _ _ =>
      exact (discardManyObjs_inv (evalPlayerRef s ctrl pref) _ hwf hok).2.2.2
    | grant scope mod dur =>
      have hf := applyChainLinkMod_fields s ctrl src env scope mod dur
      exact ⟨hf.1, hf.2.2.2.2⟩
    | chooseOne modes =>
      unfold interpRunStep; dsimp only
      split <;> exact ⟨rfl, rfl⟩
    | prim p =>
      unfold interpRunStep
      exact execPrim_meta hwf hok ctrl src env p

/-- **I18** (mandatory prompt for optional choices): `Effect.may` always pushes a `chooseMay`
decision frame for the player rather than deciding silently. -/
theorem interpRunStep_may_prompts (s : GameState) (ctrl : PlayerId) (src : ObjId)
    (fromArsenal : Bool) (env : List (VarId × Int)) (body ifDone : Effect) (more : List Effect)
    (rest : List Frame) :
    (interpRunStep s ctrl src fromArsenal env (.may body ifDone :: more) rest).1.pending =
      .chooseMay ctrl src fromArsenal env body ifDone ::
      .run ctrl src fromArsenal env more :: rest := rfl

end Fab

end
