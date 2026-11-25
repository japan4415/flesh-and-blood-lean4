module

public import Fab.Rules.Move
public import Fab.Rules.Add
public import Fab.Rules.Interp
public import Fab.Rules.Gsp

/-!
# Combat Chain rules, Attack-Proxy, LKI, Equipment Wear, and L5 Damage Spec

Implements the Combat Chain mechanics (CR 1.2.3, 1.4.3, 3.5, 7.0-7.7):
- Capturing immutable `LkiSnapshot` for every `ChainLink` (CR 1.2.3, 3.5.4b)
- Attack-Proxy creation for weapon attacks and stale proxy cleanup on Link 2+ (CR 1.4.3)
- Defend Step legality with Dominate (CR 8.3.4) and Overpower (CR 8.3.26) hooks (CR 7.3)
- Combat damage calculation `{p} - {d}` and Hit determination (CR 7.5) with independent relational
  specification `CombatDamageSpec` (**L5**)
- Close Step (CR 7.7) equipment wear — Battleworn (CR 8.3.2), Blade Break (CR 8.3.3),
  Temper (CR 8.3.10), Guardwell (CR 8.3.36) — arena return preserving identical `ObjId`, and
  graveyard cleanup (**I11**)
-/

@[expose] public section

namespace Fab

/-- Capture an immutable `LkiSnapshot` of object `id` in state `s` (CR 1.2.3).
For an `attackProxy` carrying `sourceLki`, uses that snapshot directly. -/
def captureLki (s : GameState) (id : ObjId) (fallbackOwner : PlayerId) : LkiSnapshot :=
  match s.obj? id with
  | none =>
    { cardId := none, name := "", owner := fallbackOwner, controller := fallbackOwner }
  | some o =>
    match o.kind with
    | .attackProxy _ (some lki) => lki
    | _ =>
      match s.objectFace? id with
      | some face =>
        LkiSnapshot.ofFace o.owner o.controller o.kind.cardId? face
          o.minusDefenseCounters o.plusPowerCounters
      | none =>
        { cardId := o.kind.cardId?, name := "", owner := o.owner, controller := o.controller,
          minusDefenseCounters := o.minusDefenseCounters,
          plusPowerCounters := o.plusPowerCounters }

/-- Find self-scoped static modifiers that are active on the weapon (CR 1.4.3a, 6.3.1). -/
def weaponStaticModifiers (s : GameState) (source : ObjId) (chars : DerivedChars) :
    List ContinuousMod :=
  if (s.obj? source).any (·.faceDown) || chars.abilitiesLost then [] else
    let abilities := ((s.objectFace? source).map (·.abilities)).getD []
    abilities.filterMap fun
      | .static_ cond scope mod =>
        if scope.isSelf && (cond.map (evalCondition s chars.controller source false)).getD true
        then some mod else none
      | _ => none

/-- Apply the active weapon's self-scoped static power to its live characteristics (CR 1.4.3a). -/
def weaponStaticPower (s : GameState) (source : ObjId) (chars : DerivedChars) (power : Int) : Int :=
  if chars.powerLocked then power else
    (weaponStaticModifiers s source chars).foldl (fun total modifier =>
      match modifier with
      | .addPower amount => total + evalNumExpr s chars.controller [] amount
      | _ => total) power

/-- Effective power `{p}` of an object on the board via the 8-stage continuous-effect evaluator
(including `+1{p}` counters) (CR 2.7, 6.3.2). -/
def objEffectivePower (s : GameState) (id : ObjId) : Option Int :=
  match s.obj? id with
  | none => none
  | some o =>
    match o.kind with
    | .attackProxy source (some lki) =>
      let live := do
        let chars ← s.characteristics source
        let power ← chars.power
        return weaponStaticPower s source chars power
      live.orElse fun _ => lki.power.map (· + Int.ofNat lki.plusPowerCounters)
    | _ => do
      let chars ← s.characteristics id
      let power ← chars.power
      if (s.locate id).any (fun | .player _ .weapon => true | _ => false) then
        return weaponStaticPower s id chars power
      if o.faceDown || chars.abilitiesLost || chars.powerLocked || s.locate id != some .combatChain then
        return power
      let link := s.combat.bind fun chain => chain.links.find? (·.attack == some id)
      match link, s.objectFace? id with
      | some attack, some face =>
        let defenders := nonEquipmentDefenderCount s attack
        let bonus := face.abilities.foldl (fun total ability =>
          match ability with
          | .static_ (some (.defendedByFewerNonEquip limit)) scope (.addPower (.const delta)) =>
            if scope.isSelf && decide (defenders < limit) then total + delta else total
          | _ => total) 0
        return power + bonus
      | _, _ => return power

/-- Effective defense `{d}` of an object on the board via the 8-stage continuous-effect evaluator
(including `-1{d}` counters) (CR 2.3, 6.3.2). -/
def objEffectiveDefense (s : GameState) (id : ObjId) : Option Int :=
  (s.characteristics id).bind (·.defense)

/-- Effective attack power `{p}` of a `ChainLink` — falls back to `attackLki` if the attack left
the combat chain (CR 3.5.4b) — clamped to `Nat` (CR 2.0.3, 7.5.2). -/
def linkAttackPower (s : GameState) (link : ChainLink) : Nat :=
  let basePow : Int :=
    match link.attack.bind (objEffectivePower s) with
    | some p => p
    | none => (link.attackLki.power.getD 0) + Int.ofNat link.attackLki.plusPowerCounters
  let conditionalPower := link.powerForFewerDefenders.foldl (fun total (limit, bonus) =>
    if nonEquipmentDefenderCount s link < limit then total + bonus else total) 0
  clampNonNeg (basePow + link.powerBonus + conditionalPower)

/-- Sum of effective defense values `{d}` of all defending cards on a `ChainLink` (CR 7.5.2). -/
def linkTotalDefense (s : GameState) (link : ChainLink) : Nat :=
  let cardSum : Nat :=
    (link.defending.map fun id => clampNonNeg ((objEffectiveDefense s id).getD 0)).sum
  clampNonNeg (Int.ofNat cardSum + link.defenseBonus)

/-- Physical combat damage dealt given attack power and total defense: `max(0, atk - def)`
(CR 7.5.2). -/
def calcCombatDamage (atkPower totalDef : Nat) : Nat :=
  atkPower - totalDef

/-- Combat damage proposed to the defending hero after defense and before prevention (CR 7.5.2). -/
def linkDamageBeforePrevention (s : GameState) (link : ChainLink) : Nat :=
  calcCombatDamage (linkAttackPower s link) (linkTotalDefense s link) * link.damageMultiplier

/-- Whether a combat attack hits: strictly positive damage dealt (CR 7.5.3). -/
def didCombatHit (dmg : Nat) : Bool :=
  decide (0 < dmg)

/-- **L5** (independent relational specification of Combat Damage Step) (CR 7.5.2, 7.5.3):
relates `(atkPower, totalDef)` to `(damageDealt, hit)` independently of `calcCombatDamage`. -/
inductive CombatDamageSpec (atkPower totalDef : Nat) : Nat → Bool → Prop where
  /-- Defense meets or exceeds attack power: 0 damage, does not hit. -/
  | blocked (h : atkPower ≤ totalDef) : CombatDamageSpec atkPower totalDef 0 false
  /-- Attack power strictly exceeds defense: deals difference and hits. -/
  | hit (h : totalDef < atkPower) : CombatDamageSpec atkPower totalDef (atkPower - totalDef) true

/-- **L5** (soundness/agreement): `calcCombatDamage` and `didCombatHit` satisfy `CombatDamageSpec`. -/
theorem combatDamage_matches_spec (atkPower totalDef : Nat) :
    CombatDamageSpec atkPower totalDef
      (calcCombatDamage atkPower totalDef)
      (didCombatHit (calcCombatDamage atkPower totalDef)) := by
  unfold calcCombatDamage didCombatHit
  by_cases h : totalDef < atkPower
  · have hpos : 0 < atkPower - totalDef := by omega
    simp only [hpos, decide_true]
    exact CombatDamageSpec.hit h
  · have hle : atkPower ≤ totalDef := by omega
    have hzero : atkPower - totalDef = 0 := by omega
    rw [hzero]
    exact CombatDamageSpec.blocked hle

/-- **L5** (uniqueness): `CombatDamageSpec` determines `(damage, hit)` uniquely. -/
theorem CombatDamageSpec.unique {p d dmg1 dmg2 : Nat} {hit1 hit2 : Bool}
    (h1 : CombatDamageSpec p d dmg1 hit1) (h2 : CombatDamageSpec p d dmg2 hit2) :
    dmg1 = dmg2 ∧ hit1 = hit2 := by
  cases h1 <;> cases h2 <;> first | exact ⟨rfl, rfl⟩ | omega

/-- A weapon proxy inherits Go Again from the source's current static abilities (CR 1.4.3a). -/
def weaponAttackHasGoAgain (s : GameState) (link : ChainLink) : Bool :=
  let hasGoAgain : Option Bool := do
    let attack ← link.attack.bind s.obj?
    let .attackProxy source _ := attack.kind | none
    let chars ← s.characteristics source
    return (weaponStaticModifiers s source chars).contains (.grantKeyword .goAgain)
  hasGoAgain.getD false

/-- Whether a `ChainLink`'s attack has keyword `kw` — dynamically granted, printed on the
live attack card, or preserved in `attackLki` (CR 3.5.4b). -/
def linkHasKeyword (s : GameState) (link : ChainLink) (kw : KeywordInst) : Bool :=
  link.grantedKeywords.contains kw ||
  link.attackLki.keywords.contains kw ||
  (if kw = .goAgain then weaponAttackHasGoAgain s link else false) ||
  match link.attack.bind s.objectFace? with
  | some face => face.keywords.contains kw
  | none => false

/-- All currently un-defended armor equipment `ObjId`s in player `p`'s Arena equipment slots. -/
def equipZoneIds (s : GameState) (p : PlayerId) : List ObjId :=
  s.zone (.player p .head) ++ s.zone (.player p .chest) ++
  s.zone (.player p .arms) ++ s.zone (.player p .legs)

/-- All candidate defending `ObjId`s for player `p` during Defend Step: hand cards plus
un-defended Arena equipment (CR 7.3.2). -/
def defendCandidateIds (s : GameState) (p : PlayerId) : List ObjId :=
  s.zone (.player p .hand) ++ equipZoneIds s p

/-- Whether player `p` may legally declare `id` as a defending card on `link` during Defend Step
(CR 7.3.2), enforcing Dominate (CR 8.3.4) and Overpower (CR 8.3.26) hooks. -/
def canDefendWith (s : GameState) (link : ChainLink) (p : PlayerId) (id : ObjId) : Bool :=
  if p != link.defender then
    false
  else
    let fromHand := id ∈ s.zone (.player p .hand)
    let fromEquip := id ∈ equipZoneIds s p
    if !(fromHand || fromEquip) then
      false
    else
      match s.objectFace? id with
      | none => false
      | some face =>
        if face.defense.isNone || face.hasType .defenseReaction then
          false
        else if fromHand && linkHasKeyword s link .dominate && 1 ≤ link.defendedFromHandCount then
          false
        else if face.hasType .action && linkHasKeyword s link .overpower &&
            1 ≤ link.defendedActionCount then
          false
        else
          true

/-- Read the index, use limit and cost of the weapon's attack ability (CR 5.2.2, 8.3.1). -/
def weaponAttackSpec? (c : CardDef) : Option (Nat × Bool × AssetCost) :=
  c.front.abilities.zipIdx.findSome? fun (ability, index) =>
    match ability with
    | .activated .action once cost _ _ _ ed =>
      if ed.body == .prim .weaponAttack then
        some (index, once, { cost with actionPoints := max cost.actionPoints 1 })
      else none
    | _ => none

/-- Read the weapon's attack cost, falling back to the standard action point. -/
def weaponAttackCost (c : CardDef) : AssetCost :=
  ((weaponAttackSpec? c).map fun (_, _, cost) => cost).getD { actionPoints := 1 }

/-- The ability index that a successful activation uses up for this turn. -/
def limitedWeaponAttackIndex? (c : CardDef) : Option Nat := do
  let (index, once, _) ← weaponAttackSpec? c
  if once then some index else none

/-- Whether player `p` may activate a weapon attack with `weaponId` while holding priority
(CR 1.4.3, 7.1, 7.6): must be `p`'s Action Phase, empty stack, combat chain either closed or in
Resolution Step, `weaponId ∈ weapon zone`, and `1 ≤ AP`. -/
def canAttackWithWeapon (s : GameState) (p : PlayerId) (weaponId : ObjId) : Bool :=
  let chainReady :=
    match s.combat with
    | none => true
    | some cc => cc.step == .resolution
  s.phase == .actionPhase &&
  s.active == some p &&
  (s.zone .stack).isEmpty &&
  chainReady &&
  1 ≤ (s.poolOf p).actionPoints &&
  (weaponId ∈ s.zone (.player p .weapon)) &&
  match s.cardDefOf? weaponId with
  | some c =>
    c.isWeapon &&
      !((limitedWeaponAttackIndex? c).any fun index => s.activatedThisTurn.contains (weaponId, index))
  | none => false

/-- Return an Arena equipment card `id` from `Zone.combatChain` during Close Step (CR 7.7),
applying Battleworn (CR 8.3.2), Blade Break (CR 8.3.3), Temper (CR 8.3.10), or Guardwell
(CR 8.3.36). Surviving equipment returns via Arena → Arena `moveObj`, preserving exact `ObjId`
and counters (CR 3.0.9). -/
def applyEquipmentWear (s : GameState) (id : ObjId) : GameState × List Event :=
  match s.obj? id, s.cardDefOf? id with
  | some o, some c =>
    let kws := c.front.keywords
    let slotZone : Zone :=
      match c.equipSlot? with
      | some .head => .player o.owner .head
      | some .chest => .player o.owner .chest
      | some .arms => .player o.owner .arms
      | some .legs => .player o.owner .legs
      | none => .player o.owner .weapon
    if kws.contains .bladeBreak then
      match moveObj s id (.player o.owner .graveyard) .top false with
      | some (s1, id') => (s1, [.moved id id' .combatChain (.player o.owner .graveyard)])
      | none => (s, [])
    else if kws.contains .temper then
      let s1 := updateSingleObject s id fun obj => obj.addCounterVal .minusOneDefense 1
      let effDef := (objEffectiveDefense s1 id).getD 0
      if effDef ≤ 0 then
        match moveObj s1 id (.player o.owner .graveyard) .top false with
        | some (s2, id') => (s2, [.moved id id' .combatChain (.player o.owner .graveyard)])
        | none => (s1, [])
      else
        match moveObj s1 id slotZone .top false with
        | some (s2, id') => (s2, [.moved id id' .combatChain slotZone])
        | none => (s1, [])
    else if kws.contains .battleworn then
      let s1 := updateSingleObject s id fun obj => obj.addCounterVal .minusOneDefense 1
      match moveObj s1 id slotZone .top false with
      | some (s2, id') => (s2, [.moved id id' .combatChain slotZone])
      | none => (s1, [])
    else if kws.contains .guardwell then
      let curDef := clampNonNeg ((objEffectiveDefense s id).getD 0)
      let s1 := updateSingleObject s id fun obj => obj.addCounterVal .minusOneDefense curDef
      match moveObj s1 id slotZone .top false with
      | some (s2, id') => (s2, [.moved id id' .combatChain slotZone])
      | none => (s1, [])
    else
      match moveObj s id slotZone .top false with
      | some (s1, id') => (s1, [.moved id id' .combatChain slotZone])
      | none => (s, [])
  | _, _ => (s, [])

/-- `applyEquipmentWear` preserves `WF`. -/
theorem applyEquipmentWear_wf {s : GameState} (hwf : s.WF) (id : ObjId) :
    (applyEquipmentWear s id).1.WF := by
  unfold applyEquipmentWear
  cases s.obj? id with
  | none => exact hwf
  | some o =>
    cases s.cardDefOf? id with
    | none => exact hwf
    | some c =>
      dsimp only
      split
      · cases hm : moveObj s id _ .top false with
        | none => exact hwf
        | some res => exact moveObj_wf hwf hm
      · split
        · have hwf1 := updateSingleObject_wf hwf id (fun obj => obj.addCounterVal .minusOneDefense 1)
          split
          · cases hm : moveObj _ id _ .top false with
            | none => exact hwf1
            | some res => exact moveObj_wf hwf1 hm
          · cases hm : moveObj _ id _ .top false with
            | none => exact hwf1
            | some res => exact moveObj_wf hwf1 hm
        · split
          · have hwf1 := updateSingleObject_wf hwf id (fun obj => obj.addCounterVal .minusOneDefense 1)
            cases hm : moveObj _ id _ .top false with
            | none => exact hwf1
            | some res => exact moveObj_wf hwf1 hm
          · split
            · have hwf1 := updateSingleObject_wf hwf id
                (fun obj => obj.addCounterVal .minusOneDefense (clampNonNeg ((objEffectiveDefense s id).getD 0)))
              cases hm : moveObj _ id _ .top false with
              | none => exact hwf1
              | some res => exact moveObj_wf hwf1 hm
            · cases hm : moveObj s id _ .top false with
              | none => exact hwf
              | some res => exact moveObj_wf hwf hm

/-- `applyEquipmentWear` preserves `OwnerOk`. -/
theorem applyEquipmentWear_ownerOk {s : GameState} (hwf : s.WF) (hok : s.OwnerOk) (id : ObjId) :
    (applyEquipmentWear s id).1.OwnerOk := by
  unfold applyEquipmentWear
  cases s.obj? id with
  | none => exact hok
  | some o =>
    cases s.cardDefOf? id with
    | none => exact hok
    | some c =>
      dsimp only
      split
      · cases hm : moveObj s id _ .top false with
        | none => exact hok
        | some res => exact moveObj_ownerOk hwf hok hm
      · split
        · have hwf1 := updateSingleObject_wf hwf id (fun obj => obj.addCounterVal .minusOneDefense 1)
          have hok1 := updateSingleObject_ownerOk hok id (fun obj => Object.addCounterVal_owner obj .minusOneDefense 1)
          split
          · cases hm : moveObj _ id _ .top false with
            | none => exact hok1
            | some res => exact moveObj_ownerOk hwf1 hok1 hm
          · cases hm : moveObj _ id _ .top false with
            | none => exact hok1
            | some res => exact moveObj_ownerOk hwf1 hok1 hm
        · split
          · have hwf1 := updateSingleObject_wf hwf id (fun obj => obj.addCounterVal .minusOneDefense 1)
            have hok1 := updateSingleObject_ownerOk hok id (fun obj => Object.addCounterVal_owner obj .minusOneDefense 1)
            cases hm : moveObj _ id _ .top false with
            | none => exact hok1
            | some res => exact moveObj_ownerOk hwf1 hok1 hm
          · split
            · have hwf1 := updateSingleObject_wf hwf id
                (fun obj => obj.addCounterVal .minusOneDefense (clampNonNeg ((objEffectiveDefense s id).getD 0)))
              have hok1 := updateSingleObject_ownerOk hok id
                (fun obj => Object.addCounterVal_owner obj .minusOneDefense (clampNonNeg ((objEffectiveDefense s id).getD 0)))
              cases hm : moveObj _ id _ .top false with
              | none => exact hok1
              | some res => exact moveObj_ownerOk hwf1 hok1 hm
            · cases hm : moveObj s id _ .top false with
              | none => exact hok
              | some res => exact moveObj_ownerOk hwf hok hm

/-- `applyEquipmentWear` preserves `physIds` (I1). -/
theorem applyEquipmentWear_physIds {s : GameState} (hwf : s.WF) (id : ObjId) :
    (applyEquipmentWear s id).1.physIds.Perm s.physIds := by
  unfold applyEquipmentWear
  cases s.obj? id with
  | none => exact List.Perm.refl _
  | some o =>
    cases s.cardDefOf? id with
    | none => exact List.Perm.refl _
    | some c =>
      dsimp only
      split
      · cases hm : moveObj s id _ .top false with
        | none => exact List.Perm.refl _
        | some res => exact moveObj_physIds hwf hm
      · split
        · have hwf1 := updateSingleObject_wf hwf id (fun obj => obj.addCounterVal .minusOneDefense 1)
          have hp1 := updateSingleObject_physIds s id (fun obj => Object.addCounterVal_kind obj .minusOneDefense 1)
          split
          · cases hm : moveObj _ id _ .top false with
            | none => rw [hp1]
            | some res => exact (moveObj_physIds hwf1 hm).trans (by rw [hp1])
          · cases hm : moveObj _ id _ .top false with
            | none => rw [hp1]
            | some res => exact (moveObj_physIds hwf1 hm).trans (by rw [hp1])
        · split
          · have hwf1 := updateSingleObject_wf hwf id (fun obj => obj.addCounterVal .minusOneDefense 1)
            have hp1 := updateSingleObject_physIds s id (fun obj => Object.addCounterVal_kind obj .minusOneDefense 1)
            cases hm : moveObj _ id _ .top false with
            | none => rw [hp1]
            | some res => exact (moveObj_physIds hwf1 hm).trans (by rw [hp1])
          · split
            · have hwf1 := updateSingleObject_wf hwf id
                (fun obj => obj.addCounterVal .minusOneDefense (clampNonNeg ((objEffectiveDefense s id).getD 0)))
              have hp1 := updateSingleObject_physIds s id
                (fun obj => Object.addCounterVal_kind obj .minusOneDefense (clampNonNeg ((objEffectiveDefense s id).getD 0)))
              cases hm : moveObj _ id _ .top false with
              | none => rw [hp1]
              | some res => exact (moveObj_physIds hwf1 hm).trans (by rw [hp1])
            · cases hm : moveObj s id _ .top false with
              | none => exact List.Perm.refl _
              | some res => exact moveObj_physIds hwf hm

/-- `applyEquipmentWear` preserves `config` and `playRollback`. -/
theorem applyEquipmentWear_meta (s : GameState) (id : ObjId) :
    (applyEquipmentWear s id).1.config = s.config ∧
    (applyEquipmentWear s id).1.playRollback = s.playRollback := by
  unfold applyEquipmentWear
  cases s.obj? id with
  | none => exact ⟨rfl, rfl⟩
  | some o =>
    cases s.cardDefOf? id with
    | none => exact ⟨rfl, rfl⟩
    | some c =>
      dsimp only
      split
      · cases hm : moveObj s id _ .top false with
        | none => exact ⟨rfl, rfl⟩
        | some res => exact moveObj_config_rollback hm
      · split
        · have hm1 := updateSingleObject_meta s id (fun obj => obj.addCounterVal .minusOneDefense 1)
          split
          · cases hm : moveObj _ id _ .top false with
            | none => exact hm1
            | some res =>
              have h2 := moveObj_config_rollback hm
              exact ⟨h2.1.trans hm1.1, h2.2.trans hm1.2⟩
          · cases hm : moveObj _ id _ .top false with
            | none => exact hm1
            | some res =>
              have h2 := moveObj_config_rollback hm
              exact ⟨h2.1.trans hm1.1, h2.2.trans hm1.2⟩
        · split
          · have hm1 := updateSingleObject_meta s id (fun obj => obj.addCounterVal .minusOneDefense 1)
            cases hm : moveObj _ id _ .top false with
            | none => exact hm1
            | some res =>
              have h2 := moveObj_config_rollback hm
              exact ⟨h2.1.trans hm1.1, h2.2.trans hm1.2⟩
          · split
            · have hm1 := updateSingleObject_meta s id
                (fun obj => obj.addCounterVal .minusOneDefense (clampNonNeg ((objEffectiveDefense s id).getD 0)))
              cases hm : moveObj _ id _ .top false with
              | none => exact hm1
              | some res =>
                have h2 := moveObj_config_rollback hm
                exact ⟨h2.1.trans hm1.1, h2.2.trans hm1.2⟩
            · cases hm : moveObj s id _ .top false with
              | none => exact ⟨rfl, rfl⟩
              | some res => exact moveObj_config_rollback hm

/-- Clean up a single object `id` from `Zone.combatChain` during Close Step (CR 7.7). -/
def closeChainObj (s : GameState) (id : ObjId) : GameState × List Event :=
  match s.obj? id with
  | none => (s, [])
  | some o =>
    match o.kind with
    | .attackProxy _ _ | .token _ | .layer _ _ _ _ =>
      (removeNonPhysObj s id, [])
    | .card _ _ =>
      match s.cardDefOf? id with
      | some c =>
        if c.isWeapon then
          match moveObj s id (.player o.owner .weapon) .top false with
          | some (s1, id') => (s1, [.moved id id' .combatChain (.player o.owner .weapon)])
          | none => (s, [])
        else if c.isEquipment then
          applyEquipmentWear s id
        else
          match moveObj s id (.player o.owner .graveyard) .top false with
          | some (s1, id') => (s1, [.moved id id' .combatChain (.player o.owner .graveyard)])
          | none => (s, [])
      | none =>
        match moveObj s id (.player o.owner .graveyard) .top false with
        | some (s1, id') => (s1, [.moved id id' .combatChain (.player o.owner .graveyard)])
        | none => (s, [])

/-- Clean up a list of objects from `Zone.combatChain`. -/
def closeChainList (s : GameState) : List ObjId → GameState × List Event
  | [] => (s, [])
  | id :: rest =>
    let (s1, es1) := closeChainObj s id
    let (s2, es2) := closeChainList s1 rest
    (s2, es1 ++ es2)

/-- Complete Close Step (CR 7.7): wear/return equipment and weapons, send non-equipment cards to
owner's graveyard, remove attack-proxies, expire chain-scoped continuous effects, and clear
`s.combat := none`. -/
def closeCombatChainStep (s : GameState) : GameState × List Event :=
  let (s1, es) := closeChainList s (s.zone .combatChain)
  let s2 := (s1.expireEffects .thisChainLink).expireEffects .thisCombatChain
  ({ s2 with combat := none }, es)

/-- `closeChainObj` preserves `WF`. -/
theorem closeChainObj_wf {s : GameState} (hwf : s.WF) (id : ObjId) :
    (closeChainObj s id).1.WF := by
  unfold closeChainObj
  cases s.obj? id with
  | none => exact hwf
  | some o =>
    dsimp only
    cases o.kind with
    | attackProxy _ _ | token _ | layer _ _ _ _ => exact removeNonPhysObj_wf hwf id
    | card _ _ =>
      dsimp only
      cases s.cardDefOf? id with
      | none =>
        dsimp only
        cases hm : moveObj s id (.player o.owner .graveyard) .top false with
        | none => exact hwf
        | some res => exact moveObj_wf hwf hm
      | some c =>
        dsimp only
        split
        · cases hm : moveObj s id _ .top false with
          | none => exact hwf
          | some res => exact moveObj_wf hwf hm
        · split
          · exact applyEquipmentWear_wf hwf id
          · cases hm : moveObj s id _ .top false with
            | none => exact hwf
            | some res => exact moveObj_wf hwf hm

/-- `closeChainObj` preserves `OwnerOk`. -/
theorem closeChainObj_ownerOk {s : GameState} (hwf : s.WF) (hok : s.OwnerOk) (id : ObjId) :
    (closeChainObj s id).1.OwnerOk := by
  unfold closeChainObj
  cases s.obj? id with
  | none => exact hok
  | some o =>
    dsimp only
    cases o.kind with
    | attackProxy _ _ | token _ | layer _ _ _ _ => exact removeNonPhysObj_ownerOk hok id
    | card _ _ =>
      dsimp only
      cases s.cardDefOf? id with
      | none =>
        dsimp only
        cases hm : moveObj s id (.player o.owner .graveyard) .top false with
        | none => exact hok
        | some res => exact moveObj_ownerOk hwf hok hm
      | some c =>
        dsimp only
        split
        · cases hm : moveObj s id _ .top false with
          | none => exact hok
          | some res => exact moveObj_ownerOk hwf hok hm
        · split
          · exact applyEquipmentWear_ownerOk hwf hok id
          · cases hm : moveObj s id _ .top false with
            | none => exact hok
            | some res => exact moveObj_ownerOk hwf hok hm

/-- `closeChainObj` preserves `physIds` (I1). -/
theorem closeChainObj_physIds {s : GameState} (hwf : s.WF) (id : ObjId) :
    (closeChainObj s id).1.physIds.Perm s.physIds := by
  unfold closeChainObj
  cases s.obj? id with
  | none => exact List.Perm.refl _
  | some o =>
    dsimp only
    cases o.kind with
    | attackProxy _ _ | token _ | layer _ _ _ _ => exact removeNonPhysObj_physIds hwf id
    | card _ _ =>
      dsimp only
      cases s.cardDefOf? id with
      | none =>
        dsimp only
        cases hm : moveObj s id (.player o.owner .graveyard) .top false with
        | none => exact List.Perm.refl _
        | some res => exact moveObj_physIds hwf hm
      | some c =>
        dsimp only
        split
        · cases hm : moveObj s id _ .top false with
          | none => exact List.Perm.refl _
          | some res => exact moveObj_physIds hwf hm
        · split
          · exact applyEquipmentWear_physIds hwf id
          · cases hm : moveObj s id _ .top false with
            | none => exact List.Perm.refl _
            | some res => exact moveObj_physIds hwf hm

/-- `closeChainObj` preserves `config` and `playRollback`. -/
theorem closeChainObj_meta (s : GameState) (id : ObjId) :
    (closeChainObj s id).1.config = s.config ∧
    (closeChainObj s id).1.playRollback = s.playRollback := by
  unfold closeChainObj
  cases s.obj? id with
  | none => exact ⟨rfl, rfl⟩
  | some o =>
    dsimp only
    cases o.kind with
    | attackProxy _ _ | token _ | layer _ _ _ _ => exact removeNonPhysObj_meta s id
    | card _ _ =>
      dsimp only
      cases s.cardDefOf? id with
      | none =>
        dsimp only
        cases hm : moveObj s id (.player o.owner .graveyard) .top false with
        | none => exact ⟨rfl, rfl⟩
        | some res => exact moveObj_config_rollback hm
      | some c =>
        dsimp only
        split
        · cases hm : moveObj s id _ .top false with
          | none => exact ⟨rfl, rfl⟩
          | some res => exact moveObj_config_rollback hm
        · split
          · exact applyEquipmentWear_meta s id
          · cases hm : moveObj s id _ .top false with
            | none => exact ⟨rfl, rfl⟩
            | some res => exact moveObj_config_rollback hm

/-- `closeChainList` preserves `WF`, `OwnerOk`, `physIds`, `config`, and `playRollback`. -/
theorem closeChainList_inv :
    ∀ (ids : List ObjId) {s : GameState}, s.WF → s.OwnerOk →
      (closeChainList s ids).1.WF ∧
      (closeChainList s ids).1.OwnerOk ∧
      (closeChainList s ids).1.physIds.Perm s.physIds ∧
      (closeChainList s ids).1.config = s.config ∧
      (closeChainList s ids).1.playRollback = s.playRollback
  | [], _, hwf, hok => ⟨hwf, hok, List.Perm.refl _, rfl, rfl⟩
  | id :: rest, s, hwf, hok => by
    unfold closeChainList
    have hwf1 := closeChainObj_wf hwf id
    have hok1 := closeChainObj_ownerOk hwf hok id
    have hp1 := closeChainObj_physIds hwf id
    have hm1 := closeChainObj_meta s id
    obtain ⟨hwf2, hok2, hp2, hc2, hr2⟩ := closeChainList_inv rest hwf1 hok1
    exact ⟨hwf2, hok2, hp2.trans hp1, hc2.trans hm1.1, hr2.trans hm1.2⟩

/-- `closeCombatChainStep` preserves `WF`, `OwnerOk`, `physIds`, `config`, and `playRollback`. -/
theorem closeCombatChainStep_inv {s : GameState} (hwf : s.WF) (hok : s.OwnerOk) :
    (closeCombatChainStep s).1.WF ∧
    (closeCombatChainStep s).1.OwnerOk ∧
    (closeCombatChainStep s).1.physIds.Perm s.physIds ∧
    (closeCombatChainStep s).1.config = s.config ∧
    (closeCombatChainStep s).1.playRollback = s.playRollback := by
  unfold closeCombatChainStep
  have hinv := closeChainList_inv (s.zone .combatChain) hwf hok
  cases hcl : closeChainList s (s.zone .combatChain) with
  | mk s1 es =>
    rw [hcl] at hinv
    obtain ⟨hwf1, hok1, hp1, hc1, hr1⟩ := hinv
    dsimp only [GameState.expireEffects]
    exact ⟨GameState.WF.congr hwf1 rfl rfl rfl rfl,
           GameState.OwnerOk.congr hok1 rfl rfl,
           hp1, hc1, hr1⟩

/-- Remove any stale `attackProxy` on `Zone.combatChain` whose `sourceObj` equals `weaponId`
when the same weapon attacks again on a subsequent Chain Link (CR 1.4.3).
The previous link's `attackLki` remains intact in `CombatChain.links`. -/
def removeStaleProxies (s : GameState) (weaponId : ObjId) : List ObjId → GameState
  | [] => s
  | id :: rest =>
    let s1 :=
      match s.obj? id with
      | some o =>
        match o.kind with
        | .attackProxy src _ => if src == weaponId then removeNonPhysObj s id else s
        | _ => s
      | none => s
    removeStaleProxies s1 weaponId rest

/-- `removeStaleProxies` preserves `WF`, `OwnerOk`, `physIds`, `config`, and `playRollback`. -/
theorem removeStaleProxies_inv (weaponId : ObjId) :
    ∀ (ids : List ObjId) {s : GameState}, s.WF → s.OwnerOk →
      (removeStaleProxies s weaponId ids).WF ∧
      (removeStaleProxies s weaponId ids).OwnerOk ∧
      (removeStaleProxies s weaponId ids).physIds.Perm s.physIds ∧
      (removeStaleProxies s weaponId ids).config = s.config ∧
      (removeStaleProxies s weaponId ids).playRollback = s.playRollback
  | [], _, hwf, hok => ⟨hwf, hok, List.Perm.refl _, rfl, rfl⟩
  | id :: rest, s, hwf, hok => by
    unfold removeStaleProxies
    have h1 : let s1 :=
      match s.obj? id with
      | some o =>
        match o.kind with
        | .attackProxy src _ => if src == weaponId then removeNonPhysObj s id else s
        | _ => s
      | none => s
      s1.WF ∧ s1.OwnerOk ∧ s1.physIds.Perm s.physIds ∧
      s1.config = s.config ∧ s1.playRollback = s.playRollback := by
      cases s.obj? id with
      | none => exact ⟨hwf, hok, List.Perm.refl _, rfl, rfl⟩
      | some o =>
        dsimp only
        cases o.kind with
        | attackProxy src _ =>
          dsimp only
          by_cases heq : (src == weaponId) = true
          · simp only [heq, ↓reduceIte]
            have hm := removeNonPhysObj_meta s id
            exact ⟨removeNonPhysObj_wf hwf id, removeNonPhysObj_ownerOk hok id,
                   removeNonPhysObj_physIds hwf id, hm.1, hm.2⟩
          · simp only [heq]
            exact ⟨hwf, hok, List.Perm.refl _, rfl, rfl⟩
        | card _ _ | token _ | layer _ _ _ _ => exact ⟨hwf, hok, List.Perm.refl _, rfl, rfl⟩
    obtain ⟨hwf1, hok1, hp1, hc1, hr1⟩ := h1
    obtain ⟨hwf2, hok2, hp2, hc2, hr2⟩ := removeStaleProxies_inv weaponId rest hwf1 hok1
    exact ⟨hwf2, hok2, hp2.trans hp1, hc2.trans hc1, hr2.trans hr1⟩

/-- Transition an attack card or weapon attack-proxy `layerId` from `Zone.stack` onto a new
`ChainLink` on `Zone.combatChain` at the start of Attack Step (CR 1.4.3, 7.2). -/
def enterAttackStep (s : GameState) (layerId : ObjId) (attacker : PlayerId) :
    GameState × ObjId × List Event :=
  let defender := evalPlayerRef s attacker .opposingHero
  let srcWeapon? : Option ObjId :=
    match s.obj? layerId with
    | some o =>
      match o.kind with
      | .attackProxy wid _ => some wid
      | _ => none
    | none => none
  -- If same weapon attacks again on Link 2+, clean up old attack-proxy (CR 1.4.3)
  let s0 :=
    match srcWeapon? with
    | some wid => removeStaleProxies s wid (s.zone .combatChain)
    | none => s
  -- Move weapon source to combat chain (Arena -> Arena preserves ObjId) if still in weapon zone
  let (s1, esWep) :=
    match srcWeapon? with
    | some wid =>
      if wid ∈ s0.zone (.player attacker .weapon) then
        match moveObj s0 wid .combatChain .top false with
        | some (sw, wid') => (sw, [Event.moved wid wid' (.player attacker .weapon) .combatChain])
        | none => (s0, [])
      else
        (s0, [])
    | none => (s0, [])
  -- Move the attack card / attack-proxy from stack to combatChain
  let (s2, atkId, esAtk) :=
    match moveObj s1 layerId .combatChain .top false with
    | some (sa, aid) => (sa, aid, [Event.moved layerId aid .stack .combatChain])
    | none => (s1, layerId, [])
  let lki := captureLki s2 atkId attacker
  let attackInfo := s.layerMeta.getD layerId.n { controller := attacker }
  let prevLinks := match s2.combat with | some cc => cc.links | none => []
  let newLink : ChainLink :=
    { linkId := ⟨prevLinks.length + 1⟩
      attacker := attacker
      defender := defender
      attack := some atkId
      attackSource := srcWeapon?
      attackLki := lki
      discardedForPlay := attackInfo.discardedForPlay
      additionalCostPaid := attackInfo.additionalCostPaid
      powerBonus := attackInfo.attackPowerBonus
      powerForFewerDefenders := attackInfo.attackPowerForFewerDefenders
      grantedKeywords := attackInfo.attackKeywords
      grantedAbilities := attackInfo.attackAbilities }
  let s3 := { s2 with
    combat := some { step := .attack, links := newLink :: prevLinks }
    layerMeta := s2.layerMeta.erase layerId.n }
  (s3, atkId, esWep ++ esAtk)

/-- `enterAttackStep` preserves `WF`, `OwnerOk`, `physIds`, `config`, and `playRollback`. -/
theorem enterAttackStep_inv {s : GameState} (hwf : s.WF) (hok : s.OwnerOk)
    (layerId : ObjId) (attacker : PlayerId) :
    (enterAttackStep s layerId attacker).1.WF ∧
    (enterAttackStep s layerId attacker).1.OwnerOk ∧
    (enterAttackStep s layerId attacker).1.physIds.Perm s.physIds ∧
    (enterAttackStep s layerId attacker).1.config = s.config ∧
    (enterAttackStep s layerId attacker).1.playRollback = s.playRollback := by
  unfold enterAttackStep
  dsimp only
  let srcWeapon? : Option ObjId :=
    match s.obj? layerId with
    | some o =>
      match o.kind with
      | .attackProxy wid _ => some wid
      | _ => none
    | none => none
  let s0 :=
    match srcWeapon? with
    | some wid => removeStaleProxies s wid (s.zone .combatChain)
    | none => s
  have h0 : s0.WF ∧ s0.OwnerOk ∧ s0.physIds.Perm s.physIds ∧
      s0.config = s.config ∧ s0.playRollback = s.playRollback := by
    dsimp only [s0]
    cases srcWeapon? with
    | none => exact ⟨hwf, hok, List.Perm.refl _, rfl, rfl⟩
    | some wid => exact removeStaleProxies_inv wid (s.zone .combatChain) hwf hok
  obtain ⟨hwf0, hok0, hp0, hc0, hr0⟩ := h0
  let p1 :=
    match srcWeapon? with
    | some wid =>
      if wid ∈ s0.zone (.player attacker .weapon) then
        match moveObj s0 wid .combatChain .top false with
        | some (sw, wid') => (sw, [Event.moved wid wid' (.player attacker .weapon) .combatChain])
        | none => (s0, [])
      else
        (s0, [])
    | none => (s0, [])
  have h1 : p1.1.WF ∧ p1.1.OwnerOk ∧ p1.1.physIds.Perm s0.physIds ∧
      p1.1.config = s0.config ∧ p1.1.playRollback = s0.playRollback := by
    dsimp only [p1]
    cases srcWeapon? with
    | none => exact ⟨hwf0, hok0, List.Perm.refl _, rfl, rfl⟩
    | some wid =>
      dsimp only
      split
      · cases hm : moveObj s0 wid .combatChain .top false with
        | none => exact ⟨hwf0, hok0, List.Perm.refl _, rfl, rfl⟩
        | some res =>
          have hmeta := moveObj_config_rollback hm
          exact ⟨moveObj_wf hwf0 hm, moveObj_ownerOk hwf0 hok0 hm,
                 moveObj_physIds hwf0 hm, hmeta.1, hmeta.2⟩
      · exact ⟨hwf0, hok0, List.Perm.refl _, rfl, rfl⟩
  obtain ⟨hwf1, hok1, hp1, hc1, hr1⟩ := h1
  let p2 :=
    match moveObj p1.1 layerId .combatChain .top false with
    | some (sa, aid) => (sa, aid, [Event.moved layerId aid .stack .combatChain])
    | none => (p1.1, layerId, [])
  have h2 : p2.1.WF ∧ p2.1.OwnerOk ∧ p2.1.physIds.Perm p1.1.physIds ∧
      p2.1.config = p1.1.config ∧ p2.1.playRollback = p1.1.playRollback := by
    dsimp only [p2]
    cases hm : moveObj p1.1 layerId .combatChain .top false with
    | none => exact ⟨hwf1, hok1, List.Perm.refl _, rfl, rfl⟩
    | some res =>
      have hmeta := moveObj_config_rollback hm
      exact ⟨moveObj_wf hwf1 hm, moveObj_ownerOk hwf1 hok1 hm,
             moveObj_physIds hwf1 hm, hmeta.1, hmeta.2⟩
  obtain ⟨hwf2, hok2, hp2, hc2, hr2⟩ := h2
  exact ⟨GameState.WF.congr hwf2 rfl rfl rfl rfl,
         GameState.OwnerOk.congr hok2 rfl rfl,
         (hp2.trans hp1).trans hp0,
         (hc2.trans hc1).trans hc0,
         (hr2.trans hr1).trans hr0⟩

end Fab

end
