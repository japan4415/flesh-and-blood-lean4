module

public import Fab.Rules.Move
public import Fab.Rules.Add
public import Fab.Rules.Objects
public import Fab.Rules.Actions.Banish

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

/-- Look up the `CardFace` of an object in `s.cards` (front or back based on `faceState`). -/
def GameState.objectFace? (s : GameState) (id : ObjId) : Option CardFace :=
  match s.obj? id with
  | none => none
  | some o =>
    match o.kind.cardId? with
    | none => none
    | some cid =>
      match s.cards.find? cid with
      | none => none
      | some def_ =>
        match o.faceState with
        | .front => some def_.front
        | .back => def_.back

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

/-- Look up a bound integer variable in `env` (defaulting to 0 if unbound). -/
def lookupVar (env : List (VarId × Int)) (v : VarId) : Int :=
  match env.find? (fun p => p.1 == v) with
  | some (_, val) => val
  | none => 0

/-- Evaluate a `NumExpr` in the current state and lexical environment. -/
def evalNumExpr (s : GameState) (ctrl : PlayerId) (env : List (VarId × Int)) : NumExpr → Int
  | .const n => n
  | .xValue => 0
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

/-- Test whether a `CardFace` matches a syntactic `CardFilter`. -/
def cardFaceMatches (f : CardFilter) (face : CardFace) : Bool :=
  f.supertypes.all (face.supertypes.contains ·) &&
  f.types.all (face.types.contains ·) &&
  f.subtypes.all (face.subtypes.contains ·) &&
  (f.anySubtypes.isEmpty || f.anySubtypes.any (face.subtypes.contains ·)) &&
  f.excludeTypes.all (fun t => !face.types.contains t) &&
  f.keywords.all (face.keywords.contains ·) &&
  (f.nameIn.isEmpty || f.nameIn.contains face.name) &&
  (match f.minCost with
    | none => true
    | some lo =>
      match face.cost with
      | some c => lo ≤ c.resources
      | none => false) &&
  (match f.maxCost with
    | none => true
    | some hi =>
      match face.cost with
      | some c => c.resources ≤ hi
      | none => false) &&
  (match f.minPower with
    | none => true
    | some lo =>
      match face.power with
      | some p => lo ≤ p
      | none => false) &&
  (match f.maxPower with
    | none => true
    | some hi =>
      match face.power with
      | some p => p ≤ hi
      | none => false) &&
  (match f.color with
    | none => true
    | some col => face.color == some col)

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

/-- Read counter count of kind `k` on object `o`. -/
def Object.counterCount (o : Object) : CounterKind → Nat
  | .minusOneDefense => o.minusDefenseCounters
  | .plusOnePower => o.plusPowerCounters
  | .energy => (o.extraCounters.find? (·.1 == "energy")).map (·.2) |>.getD 0
  | .steam => (o.extraCounters.find? (·.1 == "steam")).map (·.2) |>.getD 0
  | .aim => (o.extraCounters.find? (·.1 == "aim")).map (·.2) |>.getD 0
  | .named lbl => (o.extraCounters.find? (·.1 == lbl)).map (·.2) |>.getD 0

/-- Update counter `k` on object `o` by adding `delta`. -/
def Object.addCounterVal (o : Object) (k : CounterKind) (delta : Nat) : Object :=
  match k with
  | .minusOneDefense => { o with minusDefenseCounters := o.minusDefenseCounters + delta }
  | .plusOnePower => { o with plusPowerCounters := o.plusPowerCounters + delta }
  | .energy =>
    let cur := o.counterCount .energy
    let rest := o.extraCounters.filter (·.1 != "energy")
    { o with extraCounters := ("energy", cur + delta) :: rest }
  | .steam =>
    let cur := o.counterCount .steam
    let rest := o.extraCounters.filter (·.1 != "steam")
    { o with extraCounters := ("steam", cur + delta) :: rest }
  | .aim =>
    let cur := o.counterCount .aim
    let rest := o.extraCounters.filter (·.1 != "aim")
    { o with extraCounters := ("aim", cur + delta) :: rest }
  | .named lbl =>
    let cur := o.counterCount (.named lbl)
    let rest := o.extraCounters.filter (·.1 != lbl)
    { o with extraCounters := (lbl, cur + delta) :: rest }

/-- Remove all counters of kind `k` from object `o`. -/
def Object.clearCounterVal (o : Object) : CounterKind → Object
  | .minusOneDefense => { o with minusDefenseCounters := 0 }
  | .plusOnePower => { o with plusPowerCounters := 0 }
  | .energy => { o with extraCounters := o.extraCounters.filter (·.1 != "energy") }
  | .steam => { o with extraCounters := o.extraCounters.filter (·.1 != "steam") }
  | .aim => { o with extraCounters := o.extraCounters.filter (·.1 != "aim") }
  | .named lbl => { o with extraCounters := o.extraCounters.filter (·.1 != lbl) }

/-- `Object.addCounterVal` preserves `kind`. -/
theorem Object.addCounterVal_kind (o : Object) (k : CounterKind) (d : Nat) :
    (o.addCounterVal k d).kind = o.kind := by
  cases k <;> rfl

/-- `Object.addCounterVal` preserves `owner`. -/
theorem Object.addCounterVal_owner (o : Object) (k : CounterKind) (d : Nat) :
    (o.addCounterVal k d).owner = o.owner := by
  cases k <;> rfl

/-- `Object.clearCounterVal` preserves `kind`. -/
theorem Object.clearCounterVal_kind (o : Object) (k : CounterKind) :
    (o.clearCounterVal k).kind = o.kind := by
  cases k <;> rfl

/-- `Object.clearCounterVal` preserves `owner`. -/
theorem Object.clearCounterVal_owner (o : Object) (k : CounterKind) :
    (o.clearCounterVal k).owner = o.owner := by
  cases k <;> rfl

/-- Evaluate a syntactic `Condition` in the current game state. -/
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
  | .lessLifeThanOpponent =>
    let opp := evalPlayerRef s ctrl .opposingHero
    s.lifeOf ctrl < s.lifeOf opp
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
  | .defendedFromHandThisLink =>
    match s.combat.bind CombatChain.activeLink? with
    | some cur => decide (0 < cur.defendedFromHandCount)
    | none => false
  | .defendedByFewerNonEquip n =>
    match s.combat.bind CombatChain.activeLink? with
    | some cur =>
      let nonEq := (cur.defending.filter fun id =>
        match s.objectFace? id with
        | some face => !face.hasType .equipment
        | none => true).length
      decide (nonEq < n)
    | none => false
  | .additionalCostPaid => false
  | .lastDiscardedMatches _ => false
  | .weaponHitThisTurn =>
    match s.combat with
    | some cc => cc.links.any fun l => l.hit && l.attackSource.isSome
    | none => false
  | .defendingWeaponAttack =>
    match s.combat.bind CombatChain.activeLink? with
    | some cur => cur.attackSource.isSome
    | none => false
  | .sourceNotHitThisTurn =>
    match s.combat with
    | some cc => !(cc.links.any fun l => l.hit && l.attackSource == some src)
    | none => true

/-- Resolve an `ObjRef` to a concrete `ObjId` if available. -/
def evalObjRef (src : ObjId) : ObjRef → Option ObjId
  | .self_ => some src
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

/-- Execute a single atomic `Prim`, returning `(newState, emittedEvents, pushedFrames)`.
Total by design: impossible instructions become no-ops (CR 1.0.1b). -/
def execPrim (s : GameState) (ctrl : PlayerId) (src : ObjId) (env : List (VarId × Int))
    (p : Prim) : GameState × List Event × List Frame :=
  match p with
  | .draw pref n =>
    let target := evalPlayerRef s ctrl pref
    let cnt := clampNonNeg (evalNumExpr s ctrl env n)
    (s, [], [.draw target cnt])
  | .gainLife pref n =>
    let target := evalPlayerRef s ctrl pref
    let amt := clampNonNeg (evalNumExpr s ctrl env n)
    (s.setLife target (s.lifeOf target + Int.ofNat amt), [], [])
  | .loseLife pref n =>
    let target := evalPlayerRef s ctrl pref
    let amt := clampNonNeg (evalNumExpr s ctrl env n)
    let s1 := checkHeroDefeat (s.setLife target (s.lifeOf target - Int.ofNat amt))
    (s1, [], [])
  | .dealDamage kind pref n =>
    let target := evalPlayerRef s ctrl pref
    let amt := clampNonNeg (evalNumExpr s ctrl env n)
    if amt = 0 then
      (s, [], [])
    else
      let s1 := checkHeroDefeat (s.setLife target (s.lifeOf target - Int.ofNat amt))
      (s1, [.damageDealt target kind amt], [])
  | .gainAP pref n =>
    let target := evalPlayerRef s ctrl pref
    let amt := clampNonNeg (evalNumExpr s ctrl env n)
    (s.setPool target ((s.poolOf target).addActionPoints amt), [], [])
  | .gainResource pref n =>
    let target := evalPlayerRef s ctrl pref
    let amt := clampNonNeg (evalNumExpr s ctrl env n)
    (s.setPool target ((s.poolOf target).addResources amt), [], [])
  | .gainChi pref n =>
    let target := evalPlayerRef s ctrl pref
    let amt := clampNonNeg (evalNumExpr s ctrl env n)
    (s.setPool target ((s.poolOf target).addChi amt), [], [])
  | .opt pref n =>
    let target := evalPlayerRef s ctrl pref
    (s, [], [.optStep target n])
  | .createToken pref tokId n =>
    let target := evalPlayerRef s ctrl pref
    (createTokens s target tokId n, [], [])
  | .destroy oref =>
    match evalObjRef src oref with
    | none => (s, [], [])
    | some oid =>
      match s.locate oid, s.obj? oid with
      | some srcZ, some o =>
        match moveObj s oid (.player o.owner .graveyard) .top false with
        | some (s1, oid') => (s1, [.moved oid oid' srcZ (.player o.owner .graveyard)], [])
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
          match moveObj s oid dstZ pos fd with
          | some (s1, oid') => (s1, [.moved oid oid' srcZ dstZ], [])
          | none => (s, [], [])
      | _, _ => (s, [], [])
  | .putHandOnDeck pref dpos =>
    let target := evalPlayerRef s ctrl pref
    if (s.zone (.player target .hand)).isEmpty then
      (s, [], [])
    else
      (s, [], [.chooseHandToDeck target dpos])
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
      let amt := clampNonNeg (evalNumExpr s ctrl env n)
      (updateSingleObject s oid (fun o => o.addCounterVal k amt), [], [])
  | .removeAllCounters oref k =>
    match evalObjRef src oref with
    | none => (s, [], [])
    | some oid =>
      (updateSingleObject s oid (fun o => o.clearCounterVal k), [], [])
  -- Combat, search, intimidate, and prevention primitives expand in M5/M6
  | .weaponAttack | .discardRandom _ _ | .discardChoice _ _ _ | .intimidate _
  | .returnDefendingCardToHand _ | .searchDeck _ _ _ _ _ _ | .shuffleZoneIntoDeck _ _ _ _ _
  | .revealTopToArsenalIf _ _ | .preventNextDamage _ _ _ | .closeCombatChain =>
    (s, [], [])

/-- **L4** (`WF` preservation for `execPrim`): any primitive preserves `WF`. -/
theorem execPrim_wf {s : GameState} (hwf : s.WF) (ctrl : PlayerId) (src : ObjId)
    (env : List (VarId × Int)) (p : Prim) :
    (execPrim s ctrl src env p).1.WF := by
  cases p with
  | draw _ _ | opt _ _ | weaponAttack | discardRandom _ _ | discardChoice _ _ _
  | intimidate _ | returnDefendingCardToHand _ | searchDeck _ _ _ _ _ _
  | shuffleZoneIntoDeck _ _ _ _ _ | revealTopToArsenalIf _ _ | preventNextDamage _ _ _
  | closeCombatChain => exact hwf
  | gainLife _ _ => exact GameState.WF.congr hwf rfl rfl rfl rfl
  | loseLife _ _ => exact checkHeroDefeat_wf (GameState.WF.congr hwf rfl rfl rfl rfl)
  | dealDamage _ _ _ =>
    unfold execPrim
    dsimp only
    split
    · exact hwf
    · exact checkHeroDefeat_wf (GameState.WF.congr hwf rfl rfl rfl rfl)
  | gainAP _ _ | gainResource _ _ | gainChi _ _ =>
    exact GameState.WF.congr hwf rfl rfl rfl rfl
  | createToken pref tokId n =>
    exact createTokens_wf (evalPlayerRef s ctrl pref) tokId n hwf
  | destroy oref =>
    unfold execPrim
    dsimp only
    cases evalObjRef src oref with
    | none => exact hwf
    | some oid =>
      dsimp only
      split
      · rename_i srcZ o _ _
        cases hm : moveObj s oid (.player o.owner .graveyard) .top false with
        | none => exact hwf
        | some res => exact moveObj_wf hwf hm
      · exact hwf
  | banish oref fd =>
    unfold execPrim
    dsimp only
    cases evalObjRef src oref with
    | none => exact hwf
    | some oid =>
      dsimp only
      cases hb : banishOne s oid fd with
      | none => exact hwf
      | some res => exact banishOne_wf hwf hb
  | moveCard oref dstRef dpos fd =>
    unfold execPrim
    dsimp only
    cases evalObjRef src oref with
    | none => exact hwf
    | some oid =>
      dsimp only
      split
      · rename_i srcZ o _ _
        cases zoneOfRef o.owner dstRef with
        | none => exact hwf
        | some dstZ =>
          dsimp only
          split
          · rename_i s1 oid' hm
            exact moveObj_wf hwf hm
          · exact hwf
      · exact hwf
  | putHandOnDeck _ _ =>
    unfold execPrim
    dsimp only
    split <;> exact hwf
  | putArsenalOnDeckBottom pref =>
    unfold execPrim
    dsimp only
    cases s.zone (.player (evalPlayerRef s ctrl pref) .arsenal) with
    | nil => exact hwf
    | cons aid _ =>
      dsimp only
      cases hm : moveObj s aid (.player (evalPlayerRef s ctrl pref) .deck) .bottom false with
      | none => exact hwf
      | some res => exact moveObj_wf hwf hm
  | addCounter oref k n =>
    unfold execPrim
    dsimp only
    cases evalObjRef src oref with
    | none => exact hwf
    | some oid => exact updateSingleObject_wf hwf oid _
  | removeAllCounters oref k =>
    unfold execPrim
    dsimp only
    cases evalObjRef src oref with
    | none => exact hwf
    | some oid => exact updateSingleObject_wf hwf oid _

/-- **L4** (`OwnerOk` preservation for `execPrim`): any primitive preserves `OwnerOk`. -/
theorem execPrim_ownerOk {s : GameState} (hwf : s.WF) (hok : s.OwnerOk) (ctrl : PlayerId)
    (src : ObjId) (env : List (VarId × Int)) (p : Prim) :
    (execPrim s ctrl src env p).1.OwnerOk := by
  cases p with
  | draw _ _ | opt _ _ | weaponAttack | discardRandom _ _ | discardChoice _ _ _
  | intimidate _ | returnDefendingCardToHand _ | searchDeck _ _ _ _ _ _
  | shuffleZoneIntoDeck _ _ _ _ _ | revealTopToArsenalIf _ _ | preventNextDamage _ _ _
  | closeCombatChain => exact hok
  | gainLife _ _ => exact GameState.OwnerOk.congr hok rfl rfl
  | loseLife _ _ => exact checkHeroDefeat_ownerOk (GameState.OwnerOk.congr hok rfl rfl)
  | dealDamage _ _ _ =>
    unfold execPrim
    dsimp only
    split
    · exact hok
    · exact checkHeroDefeat_ownerOk (GameState.OwnerOk.congr hok rfl rfl)
  | gainAP _ _ | gainResource _ _ | gainChi _ _ =>
    exact GameState.OwnerOk.congr hok rfl rfl
  | createToken pref tokId n =>
    exact createTokens_ownerOk (evalPlayerRef s ctrl pref) tokId n hwf hok
  | destroy oref =>
    unfold execPrim
    dsimp only
    cases evalObjRef src oref with
    | none => exact hok
    | some oid =>
      dsimp only
      split
      · rename_i srcZ o _ _
        cases hm : moveObj s oid (.player o.owner .graveyard) .top false with
        | none => exact hok
        | some res => exact moveObj_ownerOk hwf hok hm
      · exact hok
  | banish oref fd =>
    unfold execPrim
    dsimp only
    cases evalObjRef src oref with
    | none => exact hok
    | some oid =>
      dsimp only
      cases hb : banishOne s oid fd with
      | none => exact hok
      | some res => exact banishOne_ownerOk hwf hok hb
  | moveCard oref dstRef dpos fd =>
    unfold execPrim
    dsimp only
    cases evalObjRef src oref with
    | none => exact hok
    | some oid =>
      dsimp only
      split
      · rename_i srcZ o _ _
        cases zoneOfRef o.owner dstRef with
        | none => exact hok
        | some dstZ =>
          dsimp only
          split
          · rename_i s1 oid' hm
            exact moveObj_ownerOk hwf hok hm
          · exact hok
      · exact hok
  | putHandOnDeck _ _ =>
    unfold execPrim
    dsimp only
    split <;> exact hok
  | putArsenalOnDeckBottom pref =>
    unfold execPrim
    dsimp only
    cases s.zone (.player (evalPlayerRef s ctrl pref) .arsenal) with
    | nil => exact hok
    | cons aid _ =>
      dsimp only
      cases hm : moveObj s aid (.player (evalPlayerRef s ctrl pref) .deck) .bottom false with
      | none => exact hok
      | some res => exact moveObj_ownerOk hwf hok hm
  | addCounter oref k n =>
    unfold execPrim
    dsimp only
    cases evalObjRef src oref with
    | none => exact hok
    | some oid => exact updateSingleObject_ownerOk hok oid (fun o => Object.addCounterVal_owner o k _)
  | removeAllCounters oref k =>
    unfold execPrim
    dsimp only
    cases evalObjRef src oref with
    | none => exact hok
    | some oid => exact updateSingleObject_ownerOk hok oid (fun o => Object.clearCounterVal_owner o k)

/-- **L4** (I1 `physIds` preservation for `execPrim`): any primitive preserves physical cards. -/
theorem execPrim_physIds {s : GameState} (hwf : s.WF) (ctrl : PlayerId) (src : ObjId)
    (env : List (VarId × Int)) (p : Prim) :
    (execPrim s ctrl src env p).1.physIds.Perm s.physIds := by
  cases p with
  | draw _ _ | opt _ _ | weaponAttack | discardRandom _ _ | discardChoice _ _ _
  | intimidate _ | returnDefendingCardToHand _ | searchDeck _ _ _ _ _ _
  | shuffleZoneIntoDeck _ _ _ _ _ | revealTopToArsenalIf _ _ | preventNextDamage _ _ _
  | closeCombatChain | gainLife _ _ | gainAP _ _ | gainResource _ _ | gainChi _ _ =>
    exact List.Perm.refl _
  | loseLife _ _ =>
    unfold execPrim
    dsimp only
    rw [checkHeroDefeat_physIds]
    exact List.Perm.refl _
  | dealDamage _ _ _ =>
    unfold execPrim
    dsimp only
    split
    · exact List.Perm.refl _
    · rw [checkHeroDefeat_physIds]
      exact List.Perm.refl _
  | createToken pref tokId n =>
    exact createTokens_physIds (evalPlayerRef s ctrl pref) tokId n hwf
  | destroy oref =>
    unfold execPrim
    dsimp only
    cases evalObjRef src oref with
    | none => exact List.Perm.refl _
    | some oid =>
      dsimp only
      split
      · rename_i srcZ o _ _
        cases hm : moveObj s oid (.player o.owner .graveyard) .top false with
        | none => exact List.Perm.refl _
        | some res => exact moveObj_physIds hwf hm
      · exact List.Perm.refl _
  | banish oref fd =>
    unfold execPrim
    dsimp only
    cases evalObjRef src oref with
    | none => exact List.Perm.refl _
    | some oid =>
      dsimp only
      cases hb : banishOne s oid fd with
      | none => exact List.Perm.refl _
      | some res => exact banishOne_physIds hwf hb
  | moveCard oref dstRef dpos fd =>
    unfold execPrim
    dsimp only
    cases evalObjRef src oref with
    | none => exact List.Perm.refl _
    | some oid =>
      dsimp only
      split
      · rename_i srcZ o _ _
        cases zoneOfRef o.owner dstRef with
        | none => exact List.Perm.refl _
        | some dstZ =>
          dsimp only
          split
          · rename_i s1 oid' hm
            exact moveObj_physIds hwf hm
          · exact List.Perm.refl _
      · exact List.Perm.refl _
  | putHandOnDeck _ _ =>
    unfold execPrim
    dsimp only
    split <;> exact List.Perm.refl _
  | putArsenalOnDeckBottom pref =>
    unfold execPrim
    dsimp only
    cases s.zone (.player (evalPlayerRef s ctrl pref) .arsenal) with
    | nil => exact List.Perm.refl _
    | cons aid _ =>
      dsimp only
      cases hm : moveObj s aid (.player (evalPlayerRef s ctrl pref) .deck) .bottom false with
      | none => exact List.Perm.refl _
      | some res => exact moveObj_physIds hwf hm
  | addCounter oref k n =>
    unfold execPrim
    dsimp only
    cases evalObjRef src oref with
    | none => exact List.Perm.refl _
    | some oid =>
      rw [updateSingleObject_physIds s oid (fun o => Object.addCounterVal_kind o k _)]
  | removeAllCounters oref k =>
    unfold execPrim
    dsimp only
    cases evalObjRef src oref with
    | none => exact List.Perm.refl _
    | some oid =>
      rw [updateSingleObject_physIds s oid (fun o => Object.clearCounterVal_kind o k)]

/-- Helper: `moveObj` preserves `config` and `playRollback`. -/
theorem moveObj_config_rollback {s s' : GameState} {id id' : ObjId} {dst : Zone} {pos : Pos}
    {fd : Bool} (h : moveObj s id dst pos fd = some (s', id')) :
    s'.config = s.config ∧ s'.playRollback = s.playRollback := by
  unfold moveObj at h
  split at h
  · dsimp only at h
    split at h
    · cases h
    · split at h <;>
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨rfl, rfl⟩
  · cases h

/-- Helper: `checkHeroDefeat` preserves `config` and `playRollback`. -/
theorem checkHeroDefeat_config_rollback (s : GameState) :
    (checkHeroDefeat s).config = s.config ∧ (checkHeroDefeat s).playRollback = s.playRollback := by
  unfold checkHeroDefeat
  split
  · exact ⟨rfl, rfl⟩
  · split <;> exact ⟨rfl, rfl⟩

/-- `execPrim` preserves `config` and `playRollback`. -/
theorem execPrim_meta (s : GameState) (ctrl : PlayerId) (src : ObjId)
    (env : List (VarId × Int)) (p : Prim) :
    (execPrim s ctrl src env p).1.config = s.config ∧
    (execPrim s ctrl src env p).1.playRollback = s.playRollback := by
  cases p with
  | draw _ _ | opt _ _ | weaponAttack | discardRandom _ _ | discardChoice _ _ _
  | intimidate _ | returnDefendingCardToHand _ | searchDeck _ _ _ _ _ _
  | shuffleZoneIntoDeck _ _ _ _ _ | revealTopToArsenalIf _ _ | preventNextDamage _ _ _
  | closeCombatChain | gainLife _ _ | gainAP _ _ | gainResource _ _ | gainChi _ _ =>
    exact ⟨rfl, rfl⟩
  | loseLife _ _ =>
    exact checkHeroDefeat_config_rollback _
  | dealDamage _ _ _ =>
    unfold execPrim; dsimp only
    split
    · exact ⟨rfl, rfl⟩
    · exact checkHeroDefeat_config_rollback _
  | createToken pref tokId n =>
    exact createTokens_meta (evalPlayerRef s ctrl pref) tokId n s
  | destroy oref =>
    unfold execPrim; dsimp only
    cases evalObjRef src oref with
    | none => exact ⟨rfl, rfl⟩
    | some oid =>
      dsimp only
      split
      · rename_i srcZ o _ _
        cases hm : moveObj s oid (.player o.owner .graveyard) .top false with
        | none => exact ⟨rfl, rfl⟩
        | some res => exact moveObj_config_rollback hm
      · exact ⟨rfl, rfl⟩
  | banish oref fd =>
    unfold execPrim; dsimp only
    cases evalObjRef src oref with
    | none => exact ⟨rfl, rfl⟩
    | some oid =>
      dsimp only
      cases hb : banishOne s oid fd with
      | none => exact ⟨rfl, rfl⟩
      | some res =>
        obtain ⟨s1, id1, es1⟩ := res
        dsimp only
        unfold banishOne at hb
        split at hb
        · rename_i src0 o0 _ _
          dsimp only at hb
          cases hm : moveObj s oid (Zone.player o0.owner .banished) .top fd with
          | none => simp only [hm] at hb; cases hb
          | some rm =>
            obtain ⟨sm, idm⟩ := rm
            simp only [hm, Option.some.injEq, Prod.mk.injEq] at hb
            obtain ⟨rfl, rfl, rfl⟩ := hb
            exact moveObj_config_rollback hm
        · cases hb
  | moveCard oref dstRef dpos fd =>
    unfold execPrim; dsimp only
    cases evalObjRef src oref with
    | none => exact ⟨rfl, rfl⟩
    | some oid =>
      dsimp only
      split
      · rename_i srcZ o _ _
        cases zoneOfRef o.owner dstRef with
        | none => exact ⟨rfl, rfl⟩
        | some dstZ =>
          dsimp only
          split
          · rename_i s1 oid' hm
            exact moveObj_config_rollback hm
          · exact ⟨rfl, rfl⟩
      · exact ⟨rfl, rfl⟩
  | putHandOnDeck _ _ =>
    unfold execPrim; dsimp only; split <;> exact ⟨rfl, rfl⟩
  | putArsenalOnDeckBottom pref =>
    unfold execPrim; dsimp only
    cases s.zone (.player (evalPlayerRef s ctrl pref) .arsenal) with
    | nil => exact ⟨rfl, rfl⟩
    | cons aid _ =>
      dsimp only
      cases hm : moveObj s aid (.player (evalPlayerRef s ctrl pref) .deck) .bottom false with
      | none => exact ⟨rfl, rfl⟩
      | some res => exact moveObj_config_rollback hm
  | addCounter oref _ _ =>
    unfold execPrim; dsimp only
    cases evalObjRef src oref with
    | none => exact ⟨rfl, rfl⟩
    | some oid => exact updateSingleObject_meta s oid _
  | removeAllCounters oref _ =>
    unfold execPrim; dsimp only
    cases evalObjRef src oref with
    | none => exact ⟨rfl, rfl⟩
    | some oid => exact updateSingleObject_meta s oid _

/-- Apply a `.thisChainLink` continuous modification directly to the active `ChainLink` if a
combat chain is open (CR 6.2, 7.4). -/
def applyChainLinkMod (s : GameState) (ctrl : PlayerId) (env : List (VarId × Int))
    (mod : ContinuousMod) (dur : Duration) : GameState :=
  match dur, s.combat with
  | .thisChainLink, some cc =>
    let cc' := cc.updateActiveLink fun link =>
      match mod with
      | .addPower d => { link with powerBonus := link.powerBonus + evalNumExpr s ctrl env d }
      | .addDefense d => { link with defenseBonus := link.defenseBonus + evalNumExpr s ctrl env d }
      | .grantKeyword kw => { link with grantedKeywords := kw :: link.grantedKeywords }
      | _ => link
    { s with combat := some cc' }
  | _, _ => s

/-- `applyChainLinkMod` only updates `combat`, preserving board structure and `playRollback`. -/
theorem applyChainLinkMod_fields (s : GameState) (ctrl : PlayerId) (env : List (VarId × Int))
    (mod : ContinuousMod) (dur : Duration) :
    (applyChainLinkMod s ctrl env mod dur).config = s.config ∧
    (applyChainLinkMod s ctrl env mod dur).objects = s.objects ∧
    (applyChainLinkMod s ctrl env mod dur).zones = s.zones ∧
    (applyChainLinkMod s ctrl env mod dur).nextId = s.nextId ∧
    (applyChainLinkMod s ctrl env mod dur).playRollback = s.playRollback := by
  unfold applyChainLinkMod
  cases dur <;> cases s.combat <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

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
    let matched := (topN.filter fun id =>
      match s.objectFace? id with
      | some face => cardFaceMatches f face
      | none => false).length
    ({ s with
        pending := .run ctrl src fromArsenal ((bindVar, Int.ofNat matched) :: env) [cont] ::
          .run ctrl src fromArsenal env more :: rest }, [])
  | .grant _ mod dur :: more =>
    let s1 := applyChainLinkMod s ctrl env mod dur
    ({ s1 with pending := .run ctrl src fromArsenal env more :: rest }, [])
  | .custom _ _ :: more =>
    ({ s with pending := .run ctrl src fromArsenal env more :: rest }, [])

/-- **L4** (`WF` preservation for `interpRunStep`): stepping any `Effect` preserves `WF`. -/
theorem interpRunStep_wf {s : GameState} (hwf : s.WF) (ctrl : PlayerId) (src : ObjId)
    (fromArsenal : Bool) (env : List (VarId × Int)) (todo : List Effect) (rest : List Frame) :
    (interpRunStep s ctrl src fromArsenal env todo rest).1.WF := by
  cases todo with
  | nil => exact GameState.WF.congr hwf rfl rfl rfl rfl
  | cons eff more =>
    cases eff with
    | nop | seq _ | ifThen _ _ _ | may _ _ | rollDie6 _ _ _ | bindRevealTopCount _ _ _ _ _
    | custom _ _ =>
      exact GameState.WF.congr hwf rfl rfl rfl rfl
    | grant _ mod dur =>
      have hf := applyChainLinkMod_fields s ctrl env mod dur
      exact GameState.WF.congr hwf hf.1 hf.2.1 hf.2.2.1 hf.2.2.2.1
    | chooseOne modes =>
      unfold interpRunStep; dsimp only
      split <;> exact GameState.WF.congr hwf rfl rfl rfl rfl
    | prim p =>
      unfold interpRunStep
      exact GameState.WF.congr (execPrim_wf hwf ctrl src env p) rfl rfl rfl rfl

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
    | custom _ _ =>
      exact GameState.OwnerOk.congr hok rfl rfl
    | grant _ mod dur =>
      have hf := applyChainLinkMod_fields s ctrl env mod dur
      exact GameState.OwnerOk.congr hok hf.2.1 hf.2.2.1
    | chooseOne modes =>
      unfold interpRunStep; dsimp only
      split <;> exact GameState.OwnerOk.congr hok rfl rfl
    | prim p =>
      unfold interpRunStep
      exact GameState.OwnerOk.congr (execPrim_ownerOk hwf hok ctrl src env p) rfl rfl

/-- **L4** (I1 `physIds` preservation for `interpRunStep`): stepping any `Effect` preserves physical
cards. -/
theorem interpRunStep_physIds {s : GameState} (hwf : s.WF) (ctrl : PlayerId) (src : ObjId)
    (fromArsenal : Bool) (env : List (VarId × Int)) (todo : List Effect) (rest : List Frame) :
    (interpRunStep s ctrl src fromArsenal env todo rest).1.physIds.Perm s.physIds := by
  cases todo with
  | nil => exact List.Perm.refl _
  | cons eff more =>
    cases eff with
    | nop | seq _ | ifThen _ _ _ | may _ _ | rollDie6 _ _ _ | bindRevealTopCount _ _ _ _ _
    | custom _ _ =>
      exact List.Perm.refl _
    | grant scope mod dur =>
      have hf := applyChainLinkMod_fields s ctrl env mod dur
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
      exact execPrim_physIds hwf ctrl src env p

/-- `interpRunStep` preserves `config` and `playRollback`. -/
theorem interpRunStep_meta (s : GameState) (ctrl : PlayerId) (src : ObjId) (fromArsenal : Bool)
    (env : List (VarId × Int)) (todo : List Effect) (rest : List Frame) :
    (interpRunStep s ctrl src fromArsenal env todo rest).1.config = s.config ∧
    (interpRunStep s ctrl src fromArsenal env todo rest).1.playRollback = s.playRollback := by
  cases todo with
  | nil => exact ⟨rfl, rfl⟩
  | cons eff more =>
    cases eff with
    | nop | seq _ | ifThen _ _ _ | may _ _ | rollDie6 _ _ _ | bindRevealTopCount _ _ _ _ _
    | custom _ _ =>
      exact ⟨rfl, rfl⟩
    | grant _ mod dur =>
      have hf := applyChainLinkMod_fields s ctrl env mod dur
      exact ⟨hf.1, hf.2.2.2.2⟩
    | chooseOne modes =>
      unfold interpRunStep; dsimp only
      split <;> exact ⟨rfl, rfl⟩
    | prim p =>
      unfold interpRunStep
      exact execPrim_meta s ctrl src env p

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
