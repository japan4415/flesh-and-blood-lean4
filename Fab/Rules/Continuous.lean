module

public import Fab.State.Object
public import Fab.Card.CardDef
public import Fab.Card.IR.Effect
public import Fab.Core.Cost

/-!
# 8-Stage Continuous Effects, Dependency Resolution, I12c, and L5 (CR 6.2-6.3, 5.1.5)

Implements the Comprehensive Rules 8-stage continuous effect evaluation system:
- Stage 1: Copyable properties (CR 6.3.2a)
- Stage 2: Controller (CR 6.3.2b)
- Stage 3: Name, Color Strip, Text Box (CR 6.3.2c)
- Stage 4: Types, Subtypes (CR 6.3.2d)
- Stage 5: Supertypes — Class / Talent (CR 6.3.2e)
- Stage 6: Abilities & Keywords (CR 6.3.2f)
- Stage 7: Base values of numeric properties (CR 6.3.2g)
- Stage 8: Modified numeric properties & counters (CR 6.3.2h)

Within each stage, effects apply by sub-stage order (CR 6.3.3):
  `restrict` → `set` → `mulDiv` → `add` → `sub`
and within each `(stage, subStage)` bucket by **Dependency** (independent effects before dependent
effects), falling back to earliest `Timestamp` on cycles (CR 6.3.3).

Proves:
- **I12c** (inner total termination bound): every bucket loop strictly decreases remaining effect
  count, terminating in at most `effs.length` total applications even under cyclic dependencies.
- **L5 (Continuous Effects)**: independent relational specification `StageOrderSpec`, soundness
  (`evalCharacteristics_matches_spec`), and uniqueness (`StageOrderSpec.unique`).
- **L5 (Asset Cost Calculation)**: Set → Increase → Decrease (floor 0) (CR 5.1.5) independent
  relational specification `AssetCostSpec`, soundness, and uniqueness.
-/

@[expose] public section

namespace Fab

/-- The 8 continuous-effect evaluation stages in strict CR order (CR 6.3.2). -/
inductive EffectStage where
  /-- Stage 1: Copyable properties (CR 6.3.2a). -/
  | stage1Copy
  /-- Stage 2: Controller (CR 6.3.2b). -/
  | stage2Controller
  /-- Stage 3: Name, Color Strip, Text Box (CR 6.3.2c). -/
  | stage3NameColorText
  /-- Stage 4: Types and Subtypes (CR 6.3.2d). -/
  | stage4TypeSubtype
  /-- Stage 5: Supertypes — Class and Talent (CR 6.3.2e). -/
  | stage5Supertype
  /-- Stage 6: Abilities and Keywords (CR 6.3.2f). -/
  | stage6Ability
  /-- Stage 7: Base values of numeric properties (CR 6.3.2g). -/
  | stage7BaseNumeric
  /-- Stage 8: Modified values of numeric properties and counters (CR 6.3.2h). -/
  | stage8ModNumeric
deriving DecidableEq, Repr, Hashable

/-- All 8 stages in strict evaluation order (CR 6.3.2). -/
def EffectStage.all : List EffectStage :=
  [.stage1Copy, .stage2Controller, .stage3NameColorText, .stage4TypeSubtype,
   .stage5Supertype, .stage6Ability, .stage7BaseNumeric, .stage8ModNumeric]

/-- Sub-stage precedence order within a single continuous-effect stage (CR 6.3.3). -/
inductive SubStage where
  /-- Restriction / lock preventing further modification of a property. -/
  | restrict
  /-- Setting a property value directly (copy, controller, set base value). -/
  | set
  /-- Multiplication and division of numeric values. -/
  | mulDiv
  /-- Addition of numeric values, types, subtypes, supertypes, or keywords. -/
  | add
  /-- Subtraction of numeric values or removal of keywords / abilities. -/
  | sub
deriving DecidableEq, Repr, Hashable

/-- All 5 sub-stages in strict evaluation order (CR 6.3.3). -/
def SubStage.all : List SubStage :=
  [.restrict, .set, .mulDiv, .add, .sub]

/-- Derived object characteristics computed by the 8-stage continuous-effect system
(CR 2.0-2.12, 6.3.2). -/
structure DerivedChars where
  /-- Effective controller (Stage 2) (CR 1.3.1, 6.3.2b). -/
  controller : PlayerId
  /-- Effective card name (Stage 3) (CR 2.6, 6.3.2c). -/
  name : String
  /-- Effective color strip (Stage 3) (CR 2.8, 6.3.2c). -/
  color : Option ColorStrip := none
  /-- Effective card types (Stage 4) (CR 2.10, 6.3.2d). -/
  types : List CardType := []
  /-- Effective card subtypes (Stage 4) (CR 2.12, 6.3.2d). -/
  subtypes : List Subtype := []
  /-- Effective card supertypes (Stage 5) (CR 2.11, 6.3.2e). -/
  supertypes : List Supertype := []
  /-- Effective keywords (Stage 6) (CR 6.3.2f, 8.3). -/
  keywords : List KeywordInst := []
  /-- Effective base power `{p}` (Stage 7) (CR 2.7, 6.3.2g). -/
  basePower : Option Int := none
  /-- Effective modified power `{p}` (Stage 8) (CR 2.7, 6.3.2h). -/
  power : Option Int := none
  /-- Effective base defense `{d}` (Stage 7) (CR 2.3, 6.3.2g). -/
  baseDefense : Option Int := none
  /-- Effective modified defense `{d}` (Stage 8) (CR 2.3, 6.3.2h). -/
  defense : Option Int := none
  /-- Effective base asset cost (Stage 7) (CR 2.2, 6.3.2g). -/
  baseCost : Option AssetCost := none
  /-- Effective modified asset cost (Stage 8) (CR 2.2, 6.3.2h). -/
  cost : Option AssetCost := none
  /-- Effective intellect `{i}` (Stage 8) (CR 2.4). -/
  intellect : Option Int := none
  /-- Effective base life `{h}` (CR 2.5). -/
  life : Option Int := none
  /-- Whether power modifications are locked by a Stage 8 restriction (CR 1.0.1a, 6.3.3). -/
  powerLocked : Bool := false
  /-- Whether printed/granted abilities were stripped by a Stage 6 effect (CR 6.3.2f). -/
  abilitiesLost : Bool := false
deriving DecidableEq, Repr

/-- Initialize `DerivedChars` from an object's base controller and active `CardFace` (CR 2.0). -/
def DerivedChars.ofBase (o : Object) (face : CardFace) : DerivedChars :=
  { controller := o.controller
    name := face.name
    color := face.color
    types := face.types
    subtypes := face.subtypes
    supertypes := face.supertypes
    keywords := face.keywords
    basePower := face.power
    power := face.power
    baseDefense := face.defense
    defense := face.defense
    baseCost := face.cost
    cost := face.cost
    intellect := face.intellect.map Int.ofNat
    life := face.life }

/-- Atomic continuous-effect operation across all 8 CR stages (CR 6.3.2). -/
inductive EffectOp where
  /-- Stage 1: copy all copyable characteristics of `face` (CR 6.3.2a). -/
  | copyFace (face : CardFace)
  /-- Stage 2: change controller to `p` (CR 6.3.2b). -/
  | setController (p : PlayerId)
  /-- Stage 3: change card name (CR 6.3.2c). -/
  | setName (name : String)
  /-- Stage 3: change color strip (CR 6.3.2c). -/
  | setColor (c : Option ColorStrip)
  /-- Stage 4: add card type `t` (CR 6.3.2d). -/
  | addType (t : CardType)
  /-- Stage 4: add subtype `st` (CR 6.3.2d). -/
  | addSubtype (st : Subtype)
  /-- Stage 4: replace subtypes with `sts` (CR 6.3.2d). -/
  | setSubtypes (sts : List Subtype)
  /-- Stage 5: add supertype `st` (CR 6.3.2e). -/
  | addSupertype (st : Supertype)
  /-- Stage 6: grant keyword `kw` (CR 6.3.2f). -/
  | grantKeyword (kw : KeywordInst)
  /-- Stage 6: grant an ability to the next matching attack (CR 6.3.2f). -/
  | grantAttackAbility (ability : Ability)
  /-- Stage 6: allow one extra activation of the affected weapon's attack ability (CR 5.2.3c). -/
  | allowWeaponAttack
  /-- Allow the designated card to be played from banished, optionally on a specific attack's link. -/
  | allowBanishedPlay (attack : Option ObjId)
  /-- Stage 6: remove keyword `kw` (CR 6.3.2f). -/
  | loseKeyword (kw : KeywordInst)
  /-- Stage 6: lose all abilities and keywords (CR 6.3.2f). -/
  | loseAllAbilities
  /-- Player restriction checked when a draw would occur (CR 8.5.6). -/
  | cantDrawCards
  /-- Player restriction removes and prohibits Go Again during the affected action phase. -/
  | cantGainGoAgain
  /-- The affected player can pay for this many more actions. -/
  | limitActions (remaining : Nat)
  /-- Restrict the player to card plays originating in arsenal. -/
  | onlyPlayFromArsenal
  /-- Stage 7: set base power `{p}` to `v` (CR 6.3.2g). -/
  | setBasePower (v : Int)
  /-- Stage 7: set base defense `{d}` to `v` (CR 6.3.2g). -/
  | setBaseDefense (v : Int)
  /-- Stage 7: set base generic resource cost `{r}` to `v` (CR 6.3.2g). -/
  | setBaseCostRes (v : Nat)
  /-- Stage 8 (restrict): lock power so subsequent Stage 8 power modifiers have no effect (CR 6.3.3). -/
  | lockPower
  /-- Stage 8 (mulDiv): multiply power by `factor` (CR 6.3.2h). -/
  | mulPower (factor : Nat)
  /-- Stage 8 (mulDiv): halve/divide power by `divisor` (rounded down; no-op if `divisor = 0`) (CR 6.3.2h). -/
  | divPower (divisor : Nat)
  /-- Stage 8 (add): add `delta` to power `{p}` (CR 6.3.2h). -/
  | addPower (delta : Int)
  /-- Stage 8: add power to the next attack while below the non-equipment defender limit (CR 6.3.2h). -/
  | addPowerIfFewerDefenders (limit : Nat) (delta : Int)
  /-- Stage 8 (sub): subtract `delta` from power `{p}` (CR 6.3.2h). -/
  | subPower (delta : Nat)
  /-- Stage 8 (add): add `delta` to defense `{d}` (CR 6.3.2h). -/
  | addDefense (delta : Int)
  /-- Stage 8 (sub): subtract `delta` from defense `{d}` (CR 6.3.2h). -/
  | subDefense (delta : Nat)
  /-- Stage 8 (add): increase resource cost `{r}` by `delta` (CR 5.1.5, 6.3.2h). -/
  | addCostRes (delta : Nat)
  /-- Stage 8 (sub): reduce resource cost `{r}` by `delta` (CR 5.1.5, 6.3.2h). -/
  | subCostRes (delta : Nat)
  /-- Stage 8 (add): modify hero intellect `{i}` by `delta` (CR 2.4, 6.3.2h). -/
  | addIntellect (delta : Int)
deriving DecidableEq, Repr

/-- Which of the 8 stages an `EffectOp` belongs to (CR 6.3.2). -/
def EffectOp.stage : EffectOp → EffectStage
  | .copyFace _ => .stage1Copy
  | .setController _ => .stage2Controller
  | .setName _ | .setColor _ => .stage3NameColorText
  | .addType _ | .addSubtype _ | .setSubtypes _ => .stage4TypeSubtype
  | .addSupertype _ => .stage5Supertype
  | .grantKeyword _ | .grantAttackAbility _ | .allowWeaponAttack | .allowBanishedPlay _ | .loseKeyword _ | .loseAllAbilities
  | .cantDrawCards | .cantGainGoAgain | .limitActions _ | .onlyPlayFromArsenal => .stage6Ability
  | .setBasePower _ | .setBaseDefense _ | .setBaseCostRes _ => .stage7BaseNumeric
  | .lockPower | .mulPower _ | .divPower _ | .addPower _ | .subPower _
  | .addDefense _ | .subDefense _ | .addCostRes _ | .subCostRes _
  | .addIntellect _ | .addPowerIfFewerDefenders _ _ => .stage8ModNumeric

/-- Which sub-stage within its stage an `EffectOp` belongs to (CR 6.3.3). -/
def EffectOp.subStage : EffectOp → SubStage
  | .lockPower | .cantDrawCards | .cantGainGoAgain | .limitActions _ | .onlyPlayFromArsenal => .restrict
  | .copyFace _ | .setController _ | .setName _ | .setColor _ | .setSubtypes _
  | .setBasePower _ | .setBaseDefense _ | .setBaseCostRes _ => .set
  | .mulPower _ | .divPower _ => .mulDiv
  | .addType _ | .addSubtype _ | .addSupertype _ | .grantKeyword _ | .grantAttackAbility _ | .allowWeaponAttack | .allowBanishedPlay _
  | .addPower _ | .addDefense _ | .addCostRes _ | .addIntellect _
  | .addPowerIfFewerDefenders _ _ => .add
  | .loseKeyword _ | .loseAllAbilities | .subPower _ | .subDefense _ | .subCostRes _ => .sub

/-- Helper: append an element to a list only if not already present. -/
def insertUnique {α : Type} [BEq α] (x : α) (xs : List α) : List α :=
  if xs.contains x then xs else xs ++ [x]

/-- Apply one `EffectOp` to a `DerivedChars` value (CR 6.3.2). -/
def applyEffectOp (c : DerivedChars) (op : EffectOp) : DerivedChars :=
  match op with
  | .copyFace face =>
    { c with
      name := face.name
      color := face.color
      types := face.types
      subtypes := face.subtypes
      supertypes := face.supertypes
      keywords := face.keywords
      basePower := face.power
      power := face.power
      baseDefense := face.defense
      defense := face.defense
      baseCost := face.cost
      cost := face.cost
      intellect := face.intellect.map Int.ofNat
      life := face.life }
  | .setController p => { c with controller := p }
  | .setName n => { c with name := n }
  | .setColor col => { c with color := col }
  | .addType t => { c with types := insertUnique t c.types }
  | .addSubtype st => { c with subtypes := insertUnique st c.subtypes }
  | .setSubtypes sts => { c with subtypes := sts }
  | .addSupertype st => { c with supertypes := insertUnique st c.supertypes }
  | .grantKeyword (.arcaneBarrier n) => { c with keywords := .arcaneBarrier n :: c.keywords }
  | .grantKeyword kw => { c with keywords := insertUnique kw c.keywords }
  | .grantAttackAbility _ | .allowWeaponAttack | .allowBanishedPlay _
  | .cantDrawCards | .cantGainGoAgain | .limitActions _ | .onlyPlayFromArsenal => c
  | .loseKeyword kw => { c with keywords := c.keywords.filter (· != kw) }
  | .loseAllAbilities => { c with keywords := [], abilitiesLost := true }
  | .setBasePower v => { c with basePower := some v, power := some v }
  | .setBaseDefense v => { c with baseDefense := some v, defense := some v }
  | .setBaseCostRes v =>
    let newCost := match c.baseCost with
      | some ac => some { ac with resources := v }
      | none => some { resources := v }
    { c with baseCost := newCost, cost := newCost }
  | .lockPower => { c with powerLocked := true }
  | .mulPower factor =>
    if c.powerLocked then c
    else { c with power := c.power.map (· * Int.ofNat factor) }
  | .divPower divisor =>
    if c.powerLocked || divisor == 0 then c
    else { c with power := c.power.map (· / Int.ofNat divisor) }
  | .addPower d =>
    if c.powerLocked then c
    else { c with power := c.power.map (· + d) }
  | .addPowerIfFewerDefenders _ _ => c
  | .subPower d =>
    if c.powerLocked then c
    else { c with power := c.power.map (· - Int.ofNat d) }
  | .addDefense d => { c with defense := c.defense.map (· + d) }
  | .subDefense d => { c with defense := c.defense.map (· - Int.ofNat d) }
  | .addCostRes d => { c with cost := c.cost.map fun ac => { ac with resources := ac.resources + d } }
  | .subCostRes d => { c with cost := c.cost.map fun ac => { ac with resources := ac.resources - d } }
  | .addIntellect d => { c with intellect := c.intellect.map (· + d) }

/-- Target selector for a continuous effect, evaluated against live `DerivedChars` (CR 6.2-6.3). -/
inductive EffectTarget where
  /-- Applies specifically to object `id`. -/
  | obj (id : ObjId)
  /-- Attacks made with an identified weapon (CR 1.4.3d). -/
  | weaponAttacks (source : ObjId)
  /-- Restricts the specified player rather than altering an object's characteristics. -/
  | player (p : PlayerId)
  /-- Applies to each object selected when the effect was generated (CR 6.2.2c). -/
  | objects (ids : List ObjId)
  /-- Applies to any object whose derived characteristics satisfy `reqType`/`reqSubtype`/
  `reqSupertype`/`reqMinPower`/`reqName` and optional controller restriction. -/
  | matching
      (ctrl : Option PlayerId := none)
      (reqType : Option CardType := none)
      (reqSubtype : Option Subtype := none)
      (reqSupertype : Option Supertype := none)
      (reqMinPower : Option Int := none)
      (reqName : Option String := none)
  /-- Applies to cards a player controls that satisfy the full filter (CR 6.2.2). -/
  | matchingCard (controller : PlayerId) (filter : CardFilter)
  /-- Waits for the controller to play an attack action card matching the filter. -/
  | nextAttackCard (filter : CardFilter)
  /-- Waits for the controller to pay for an attack matching the filter, including an attack-proxy. -/
  | nextAttack (filter : CardFilter)
  /-- The next paid attack of a specific affected player (Debilitate). -/
  | nextAttackBy (p : PlayerId)
  /-- Additional resources for the specified player's next played or activated action. -/
  | nextActionBy (p : PlayerId)
  /-- Waits for the controller's next defending card and applies if it matches the filter. -/
  | nextDefend (filter : CardFilter)
  /-- A card with an effect that follows it specifically when it is played from arsenal. -/
  | arsenalCard (id : ObjId)
  /-- Applies to each paid attack matching the filter while the effect is active. -/
  | allAttacks (filter : CardFilter)
deriving DecidableEq, Repr

/-- Whether `target` currently matches object `id` with derived characteristics `c`. -/
def EffectTarget.matches (t : EffectTarget) (c : DerivedChars) (id : ObjId) : Bool :=
  match t with
  | .obj tid => tid == id
  | .arsenalCard tid => tid == id
  | .objects ids => ids.contains id
  | .player _ | .weaponAttacks _ | .nextAttackCard _ | .nextAttack _ | .nextAttackBy _ | .nextActionBy _
  | .nextDefend _ | .allAttacks _ => false
  | .matchingCard controller filter =>
    c.controller == controller && !filter.isWeaponAttack &&
      cardFaceMatches filter {
        name := c.name, types := c.types, subtypes := c.subtypes,
        supertypes := c.supertypes, color := c.color, keywords := c.keywords,
        cost := c.baseCost, power := c.power }
  | .matching ctrl reqT reqSub reqSup reqMinP reqName =>
    (match ctrl with | some p => c.controller == p | none => true) &&
    (match reqT with | some ty => c.types.contains ty | none => true) &&
    (match reqSub with | some st => c.subtypes.contains st | none => true) &&
    (match reqSup with | some sp => c.supertypes.contains sp | none => true) &&
    (match reqMinP with
     | some mp => match c.power with | some pw => decide (mp ≤ pw) | none => false
     | none => true) &&
    (match reqName with | some nm => c.name == nm | none => true)

/-- An active continuous effect registered on the game state (CR 6.2-6.3). -/
structure ContinuousEffect where
  /-- Unique identifier for deterministic tiebreaking. -/
  id : Nat
  /-- Source object that generated this effect. -/
  source : ObjId
  /-- Controller of the effect. -/
  controller : PlayerId
  /-- Which object(s) this effect applies to. -/
  target : EffectTarget
  /-- The characteristic modification to apply. -/
  op : EffectOp
  /-- How long this effect remains active. -/
  duration : Duration := .thisTurn
  /-- On a turn after creation, expire at the specified player's turn end. -/
  endAfterTurnOf : Option (PlayerId × Nat) := none
  /-- Wait until the beginning of the same future turn, rather than applying immediately. -/
  waitsForNextTurn : Bool := false
  /-- Timestamp when this continuous effect was generated (CR 6.3.3). -/
  timestamp : Timestamp
deriving DecidableEq, Repr

/-- Preserve a public arsenal effect when its card is played or enters the combat chain
(CR 3.0.9, 3.0.9b). -/
def ContinuousEffect.followArsenalCard (e : ContinuousEffect) (previous current : ObjId) : ContinuousEffect :=
  if e.target == .arsenalCard previous then { e with target := .arsenalCard current }
  else e

/-- Whether `e` currently applies to `(c, oid)`. -/
def ContinuousEffect.appliesTo (e : ContinuousEffect) (c : DerivedChars) (oid : ObjId) : Bool :=
  e.target.matches c oid

/-- Strictly earlier timestamp comparison (breaking ties by `id`) (CR 6.3.3). -/
def ContinuousEffect.earlierThan (a b : ContinuousEffect) : Bool :=
  a.timestamp.n < b.timestamp.n || (a.timestamp.n == b.timestamp.n && a.id < b.id)

/-- Dependency relation within the same `(stage, subStage)` bucket (CR 6.3.3):
effect `b` depends on distinct effect `a` at state `(c, oid)` if applying `a` (when `a` applies)
changes whether `b` applies to `(c, oid)` or changes the result of applying `b` (for example,
`a` sets a subtype or keyword that enables/disables `b`). -/
def dependsOn (c : DerivedChars) (oid : ObjId) (a b : ContinuousEffect) : Bool :=
  if a.id == b.id then false
  else if !a.appliesTo c oid then false
  else
    let cAfterA := applyEffectOp c a.op
    b.appliesTo cAfterA oid != b.appliesTo c oid

/-- Whether `e` is independent of all other effects in `rem` at `(c, oid)` (CR 6.3.3). -/
def isIndependent (c : DerivedChars) (oid : ObjId) (rem : List ContinuousEffect)
    (e : ContinuousEffect) : Bool :=
  !(rem.any fun a => dependsOn c oid a e)

/-- Pick the effect with earliest timestamp (tie-broken by `id`) from a non-empty list. -/
def pickEarliest : List ContinuousEffect → Option ContinuousEffect
  | [] => none
  | x :: xs =>
    some (xs.foldl (fun best cur => if cur.earlierThan best then cur else best) x)

/-- Every element returned by `pickEarliest` belongs to the input list. -/
theorem pickEarliest_mem {l : List ContinuousEffect} {e : ContinuousEffect}
    (h : pickEarliest l = some e) : e ∈ l := by
  cases l with
  | nil => cases h
  | cons x xs =>
    unfold pickEarliest at h
    simp only [Option.some.injEq] at h
    subst h
    have aux : ∀ (acc : ContinuousEffect) (ys : List ContinuousEffect),
        (acc ∈ x :: xs) → (∀ y ∈ ys, y ∈ x :: xs) →
        ys.foldl (fun best cur => if cur.earlierThan best then cur else best) acc ∈ x :: xs := by
      intro acc ys
      induction ys generalizing acc with
      | nil => intro hacc _; exact hacc
      | cons y ys' ih =>
        intro hacc hys
        simp only [List.foldl_cons]
        apply ih
        · split
          · exact hys y List.mem_cons_self
          · exact hacc
        · intro z hz; exact hys z (List.mem_cons_of_mem _ hz)
    exact aux x xs List.mem_cons_self (fun y hy => List.mem_cons_of_mem _ hy)

/-- Pick the next effect to apply from a single `(stage, subStage)` bucket `rem` (CR 6.3.3):
1. Prefer independent effects (earliest timestamp among them).
2. If every remaining effect participates in a dependency cycle (`indep = []`), fall back to the
   earliest timestamp in `rem` (CR 6.3.3c). -/
def pickNextInBucket (c : DerivedChars) (oid : ObjId) (rem : List ContinuousEffect) :
    Option ContinuousEffect :=
  let indep := rem.filter (isIndependent c oid rem)
  match pickEarliest indep with
  | some e => some e
  | none => pickEarliest rem

/-- `pickNextInBucket` always returns an element of `rem`. -/
theorem pickNextInBucket_mem {c : DerivedChars} {oid : ObjId} {rem : List ContinuousEffect}
    {e : ContinuousEffect} (h : pickNextInBucket c oid rem = some e) : e ∈ rem := by
  unfold pickNextInBucket at h
  dsimp only at h
  cases hp : pickEarliest (rem.filter (isIndependent c oid rem)) with
  | some e1 =>
    rw [hp] at h
    simp only [Option.some.injEq] at h
    subst h
    exact (List.mem_filter.mp (pickEarliest_mem hp)).1
  | none =>
    rw [hp] at h
    exact pickEarliest_mem h

/-- `pickNextInBucket` always succeeds on a non-empty bucket. -/
theorem pickNextInBucket_isSome {c : DerivedChars} {oid : ObjId} {x : ContinuousEffect}
    {xs : List ContinuousEffect} :
    (pickNextInBucket c oid (x :: xs)).isSome = true := by
  unfold pickNextInBucket
  dsimp only
  cases pickEarliest ((x :: xs).filter (isIndependent c oid (x :: xs))) with
  | some _ => rfl
  | none => rfl

/-- Remove the first occurrence of `e` (by `id`) from `rem`. -/
def removeEffectById (eid : Nat) : List ContinuousEffect → List ContinuousEffect
  | [] => []
  | x :: xs => if x.id == eid then xs else x :: removeEffectById eid xs

/-- Removing an effect that is present strictly decreases list length (**I12c** measure). -/
theorem removeEffectById_length_lt {l : List ContinuousEffect} {e : ContinuousEffect}
    (h : e ∈ l) : (removeEffectById e.id l).length < l.length := by
  induction l with
  | nil => cases h
  | cons x xs ih =>
    unfold removeEffectById
    rcases List.mem_cons.mp h with rfl | htail
    · simp
    · by_cases heq : (x.id == e.id) = true
      · simp [heq]
      · simp only [heq, Bool.false_eq_true, ↓reduceIte, List.length_cons]
        have := ih htail
        omega

/-- Apply all effects in a single `(stage, subStage)` bucket using fuel-bounded structural
recursion (`fuel = rem.length`) (**I12c**), returning `(derivedChars, stepsExecuted)`. -/
def applyBucketLoop (oid : ObjId) :
    Nat → DerivedChars → List ContinuousEffect → DerivedChars × Nat
  | 0, c, _ => (c, 0)
  | fuel + 1, c, rem =>
    match pickNextInBucket c oid rem with
    | none => (c, 0)
    | some e =>
      let c1 := if e.appliesTo c oid then applyEffectOp c e.op else c
      let rem' := removeEffectById e.id rem
      let (cFinal, n) := applyBucketLoop oid fuel c1 rem'
      (cFinal, n + 1)

/-- Evaluate one `(stage, subStage)` bucket using its exact termination bound `bucket.length`
(**I12c**) (CR 6.3.3). -/
def applyBucket (oid : ObjId) (c : DerivedChars) (bucket : List ContinuousEffect) :
    DerivedChars × Nat :=
  applyBucketLoop oid bucket.length c bucket

/-- **I12c** (bucket termination bound): `applyBucketLoop oid fuel c rem` executes at most `fuel`
effect applications, and when `rem.length ≤ fuel` it consumes every effect in `rem` in exact
`rem.length` steps (even under dependency cycles). -/
theorem applyBucketLoop_steps_le (oid : ObjId) :
    ∀ (fuel : Nat) (c : DerivedChars) (rem : List ContinuousEffect),
      (applyBucketLoop oid fuel c rem).2 ≤ fuel
  | 0, _, _ => Nat.le_refl 0
  | fuel + 1, c, rem => by
    unfold applyBucketLoop
    cases pickNextInBucket c oid rem with
    | none => exact Nat.zero_le _
    | some e =>
      dsimp only
      have ih := applyBucketLoop_steps_le oid fuel
        (if e.appliesTo c oid then applyEffectOp c e.op else c)
        (removeEffectById e.id rem)
      omega

/-- **I12c** (bucket exactness): when `rem.length ≤ fuel`, `applyBucketLoop` processes all
`rem.length` effects without hitting fuel exhaustion. -/
theorem applyBucketLoop_exhausts (oid : ObjId) :
    ∀ (fuel : Nat) (c : DerivedChars) (rem : List ContinuousEffect),
      rem.length ≤ fuel → (applyBucketLoop oid fuel c rem).2 = rem.length
  | 0, c, rem, hle => by
    have : rem = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; rfl
  | fuel + 1, c, rem, hle => by
    cases rem with
    | nil => rfl
    | cons x xs =>
      unfold applyBucketLoop
      have hsome := pickNextInBucket_isSome (c := c) (oid := oid) (x := x) (xs := xs)
      cases hp : pickNextInBucket c oid (x :: xs) with
      | none => rw [hp] at hsome; simp at hsome
      | some e =>
        dsimp only
        have hmem := pickNextInBucket_mem hp
        have hlt := removeEffectById_length_lt hmem
        have hlen : (removeEffectById e.id (x :: xs)).length = xs.length := by
          have aux : ∀ (l : List ContinuousEffect) (eid : Nat),
              (∃ y ∈ l, y.id = eid) → (removeEffectById eid l).length + 1 = l.length := by
            intro l eid
            induction l with
            | nil => rintro ⟨_, h, _⟩; cases h
            | cons a as iha =>
              rintro ⟨y, hy, hyd⟩
              unfold removeEffectById
              by_cases he : (a.id == eid) = true
              · simp [he]
              · simp only [he, Bool.false_eq_true, ↓reduceIte, List.length_cons]
                rcases List.mem_cons.mp hy with rfl | hyt
                · exfalso; exact he (by simp [hyd])
                · have := iha ⟨y, hyt, hyd⟩; omega
          have := aux (x :: xs) e.id ⟨e, hmem, rfl⟩
          simp only [List.length_cons] at this
          omega
        have ih := applyBucketLoop_exhausts oid fuel
          (if e.appliesTo c oid then applyEffectOp c e.op else c)
          (removeEffectById e.id (x :: xs))
          (by simp only [List.length_cons] at hle; omega)
        rw [ih, hlen]
        rfl

/-- Evaluate a single `EffectStage` across all 5 sub-stages in strict order (CR 6.3.3). -/
def applyStage (oid : ObjId) (effs : List ContinuousEffect) (st : EffectStage)
    (c : DerivedChars) : DerivedChars × Nat :=
  SubStage.all.foldl (fun (acc, steps) ss =>
    let bucket := effs.filter fun e => e.op.stage == st && e.op.subStage == ss
    let (c', n) := applyBucket oid acc bucket
    (c', steps + n)) (c, 0)

/-- Apply object counters (`+1{p}` and `-1{d}`) at the end of Stage 8 (CR 6.3.2h, 8.3). -/
def applyCounters (o : Object) (c : DerivedChars) : DerivedChars :=
  { c with
    power :=
      if c.powerLocked then c.power
      else c.power.map (· + Int.ofNat o.plusPowerCounters)
    defense := c.defense.map (· - Int.ofNat o.minusDefenseCounters) }

/-- Full 8-stage continuous-effect evaluator returning `(derivedChars, totalSteps)`
(CR 6.3.2, 6.3.3). -/
def evalCharacteristicsWithSteps (effs : List ContinuousEffect) (o : Object) (face : CardFace)
    (oid : ObjId) : DerivedChars × Nat :=
  let base := DerivedChars.ofBase o face
  let (afterStages, totalSteps) :=
    EffectStage.all.foldl (fun (acc, steps) st =>
      let (c', n) := applyStage oid effs st acc
      (c', steps + n)) (base, 0)
  (applyCounters o afterStages, totalSteps)

/-- Full 8-stage continuous-effect evaluator returning `DerivedChars` (CR 6.3.2, 6.3.3). -/
def evalCharacteristics (effs : List ContinuousEffect) (o : Object) (face : CardFace)
    (oid : ObjId) : DerivedChars :=
  (evalCharacteristicsWithSteps effs o face oid).1

/-- Helper: partition sum across disjoint predicates equals total length. -/
theorem filter_partition_sum {α : Type} (l : List α) {β : Type} [DecidableEq β]
    (keys : List β) (hnd : keys.Nodup) (f : α → β) (hcov : ∀ x ∈ l, f x ∈ keys) :
    (keys.map fun k => (l.filter fun x => decide (f x = k)).length).sum = l.length := by
  induction l with
  | nil =>
    have h0 : ∀ ks : List β, (ks.map fun _ => (0 : Nat)).sum = 0 := by
      intro ks; induction ks with | nil => rfl | cons _ t iht => simp [iht]
    simpa using h0 keys
  | cons x xs ih =>
    have hxs : ∀ y ∈ xs, f y ∈ keys := fun y hy => hcov y (List.mem_cons_of_mem _ hy)
    have hx : f x ∈ keys := hcov x List.mem_cons_self
    have ih' := ih hxs
    have step : ∀ (ks : List β), ks.Nodup → f x ∈ ks →
        (ks.map fun k => ((x :: xs).filter fun y => decide (f y = k)).length).sum =
        (ks.map fun k => (xs.filter fun y => decide (f y = k)).length).sum + 1 := by
      intro ks
      induction ks with
      | nil => intro _ hmem; cases hmem
      | cons k kt ihk =>
        intro hknd hmem
        rw [List.nodup_cons] at hknd
        simp only [List.map_cons, List.sum_cons]
        rcases List.mem_cons.mp hmem with rfl | htail
        · have hrest : kt.map (fun k' => ((x :: xs).filter fun y => decide (f y = k')).length) =
              kt.map (fun k' => (xs.filter fun y => decide (f y = k')).length) := by
            apply List.map_congr_left
            intro k' hk'
            have hne : f x ≠ k' := fun heq => hknd.1 (heq ▸ hk')
            simp [hne]
          rw [List.filter_cons, hrest]
          simp only [decide_true, ↓reduceIte, List.length_cons]
          omega
        · have hne : f x ≠ k := fun heq => hknd.1 (heq ▸ htail)
          have hsub := ihk hknd.2 htail
          rw [List.filter_cons]
          simp only [hne, decide_false, Bool.false_eq_true, ↓reduceIte]
          omega
    rw [step keys hnd hx, ih']
    rfl

/-- **I12c** (global inner termination bound): across all 8 stages × 5 sub-stages,
`evalCharacteristicsWithSteps` executes **exact `effs.length` total applications** — every effect
belongs to a unique `(stage, subStage)` bucket and terminates in `effs.length` steps even under
arbitrary dependency cycles (CR 6.3.2, 6.3.3). -/
theorem evalCharacteristics_steps_eq (effs : List ContinuousEffect) (o : Object) (face : CardFace)
    (oid : ObjId) :
    (evalCharacteristicsWithSteps effs o face oid).2 = effs.length := by
  have hfold_sub : ∀ (st : EffectStage) (c0 : DerivedChars) (s0 : Nat) (subs : List SubStage),
      (subs.foldl (fun (acc, steps) ss =>
        let bucket := effs.filter fun e => e.op.stage == st && e.op.subStage == ss
        let (c', n) := applyBucket oid acc bucket
        (c', steps + n)) (c0, s0)).2 =
      s0 + (subs.map fun ss =>
        (effs.filter fun e => e.op.stage == st && e.op.subStage == ss).length).sum := by
    intro st c0 s0 subs
    induction subs generalizing c0 s0 with
    | nil => simp
    | cons ss rest ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [ih]
      have hex : (applyBucket oid c0
          (effs.filter fun e => e.op.stage == st && e.op.subStage == ss)).2 =
          (effs.filter fun e => e.op.stage == st && e.op.subStage == ss).length :=
        applyBucketLoop_exhausts oid _ c0 _ (Nat.le_refl _)
      rw [hex]
      omega
  have hfold_stage : ∀ (c0 : DerivedChars) (s0 : Nat) (sts : List EffectStage),
      (sts.foldl (fun (acc, steps) st =>
        let (c', n) := applyStage oid effs st acc
        (c', steps + n)) (c0, s0)).2 =
      s0 + (sts.map fun st =>
        (SubStage.all.map fun ss =>
          (effs.filter fun e => e.op.stage == st && e.op.subStage == ss).length).sum).sum := by
    intro c0 s0 sts
    induction sts generalizing c0 s0 with
    | nil => simp
    | cons st rest ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [ih]
      have hs := hfold_sub st c0 0 SubStage.all
      unfold applyStage
      rw [hs]
      omega
  unfold evalCharacteristicsWithSteps
  dsimp only
  rw [hfold_stage]
  simp only [Nat.zero_add]
  let pairs : List (EffectStage × SubStage) :=
    EffectStage.all.flatMap fun st => SubStage.all.map fun ss => (st, ss)
  have hsum_eq : (EffectStage.all.map fun st =>
      (SubStage.all.map fun ss =>
        (effs.filter fun e => e.op.stage == st && e.op.subStage == ss).length).sum).sum =
      (pairs.map fun p => (effs.filter fun e => decide ((e.op.stage, e.op.subStage) = p)).length).sum := by
    dsimp only [pairs, EffectStage.all, SubStage.all]
    simp only [List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil, List.append_nil,
      List.cons_append, List.nil_append, List.sum_cons, List.sum_nil, Nat.add_zero]
    have hpred : ∀ (st : EffectStage) (ss : SubStage),
        (effs.filter fun e => e.op.stage == st && e.op.subStage == ss) =
        (effs.filter fun e => decide ((e.op.stage, e.op.subStage) = (st, ss))) := by
      intro st ss
      apply congrArg (fun p => effs.filter p)
      funext e
      by_cases h1 : e.op.stage = st <;> by_cases h2 : e.op.subStage = ss <;> simp [h1, h2]
    simp only [hpred, Nat.add_assoc]
  rw [hsum_eq]
  have hp_nd : pairs.Nodup := by decide
  have hp_cov : ∀ e ∈ effs, (e.op.stage, e.op.subStage) ∈ pairs := by
    intro e _
    cases e.op.stage <;> cases e.op.subStage <;> decide
  exact filter_partition_sum effs pairs hp_nd (fun e => (e.op.stage, e.op.subStage)) hp_cov

/-- **L5** (independent relational specification of 8-stage continuous effect evaluation)
(CR 6.3.2, 6.3.3): explicitly chains Stage 1 → Stage 2 → Stage 3 → Stage 4 → Stage 5 → Stage 6 →
Stage 7 → Stage 8 → Counters. -/
inductive StageOrderSpec (effs : List ContinuousEffect) (o : Object) (face : CardFace)
    (oid : ObjId) : DerivedChars → Prop where
  /-- Exact 8-stage derivation from printed base characteristics followed by object counters. -/
  | eval
      (c0 c1 c2 c3 c4 c5 c6 c7 c8 cOut : DerivedChars)
      (h0 : c0 = DerivedChars.ofBase o face)
      (h1 : c1 = (applyStage oid effs .stage1Copy c0).1)
      (h2 : c2 = (applyStage oid effs .stage2Controller c1).1)
      (h3 : c3 = (applyStage oid effs .stage3NameColorText c2).1)
      (h4 : c4 = (applyStage oid effs .stage4TypeSubtype c3).1)
      (h5 : c5 = (applyStage oid effs .stage5Supertype c4).1)
      (h6 : c6 = (applyStage oid effs .stage6Ability c5).1)
      (h7 : c7 = (applyStage oid effs .stage7BaseNumeric c6).1)
      (h8 : c8 = (applyStage oid effs .stage8ModNumeric c7).1)
      (hOut : cOut = applyCounters o c8) :
      StageOrderSpec effs o face oid cOut

/-- **L5** (soundness): `evalCharacteristics` satisfies the independent `StageOrderSpec`. -/
theorem evalCharacteristics_matches_spec (effs : List ContinuousEffect) (o : Object)
    (face : CardFace) (oid : ObjId) :
    StageOrderSpec effs o face oid (evalCharacteristics effs o face oid) := by
  exact StageOrderSpec.eval
    (DerivedChars.ofBase o face)
    (applyStage oid effs .stage1Copy (DerivedChars.ofBase o face)).1
    (applyStage oid effs .stage2Controller _).1
    (applyStage oid effs .stage3NameColorText _).1
    (applyStage oid effs .stage4TypeSubtype _).1
    (applyStage oid effs .stage5Supertype _).1
    (applyStage oid effs .stage6Ability _).1
    (applyStage oid effs .stage7BaseNumeric _).1
    (applyStage oid effs .stage8ModNumeric _).1
    (evalCharacteristics effs o face oid)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

/-- **L5** (uniqueness): `StageOrderSpec` determines derived characteristics uniquely. -/
theorem StageOrderSpec.unique {effs : List ContinuousEffect} {o : Object} {face : CardFace}
    {oid : ObjId} {c1 c2 : DerivedChars}
    (h1 : StageOrderSpec effs o face oid c1) (h2 : StageOrderSpec effs o face oid c2) :
    c1 = c2 := by
  cases h1
  cases h2
  simp_all

/-! ### Asset Cost Calculation (CR 5.1.5) & L5 Relational Specification -/

/-- Calculate the final `AssetCost` following cost-calculation order (CR 5.1.5):
1. Optional cost-setting replacement (`setRes`),
2. All cost increases (`increases`),
3. All cost reductions (`reductions`), floored at 0 (CR 2.0.3, 5.1.5). -/
def calcFinalAssetCost (base : AssetCost) (setRes : Option Nat)
    (increases reductions : List Nat) : AssetCost :=
  let afterSet := match setRes with | some v => v | none => base.resources
  let afterInc := afterSet + increases.sum
  let finalRes := afterInc - reductions.sum
  { base with resources := finalRes }

/-- **L5** (independent relational specification of asset-cost calculation) (CR 5.1.5):
relates `(base, setRes, increases, reductions)` to the final resource cost via explicit
Set → Increase → Reduce (floor 0) steps. -/
inductive AssetCostSpec (base : AssetCost) (setRes : Option Nat)
    (increases reductions : List Nat) : AssetCost → Prop where
  /-- Reduction meets or exceeds `afterSet + increases`: resource cost floors at 0. -/
  | floored (afterSet : Nat)
      (hSet : afterSet = setRes.getD base.resources)
      (hLe : afterSet + increases.sum ≤ reductions.sum) :
      AssetCostSpec base setRes increases reductions { base with resources := 0 }
  /-- `afterSet + increases` exceeds reduction: exact positive difference remains. -/
  | positive (afterSet : Nat)
      (hSet : afterSet = setRes.getD base.resources)
      (hLt : reductions.sum < afterSet + increases.sum) :
      AssetCostSpec base setRes increases reductions
        { base with resources := afterSet + increases.sum - reductions.sum }

/-- **L5** (soundness): `calcFinalAssetCost` satisfies `AssetCostSpec` (CR 5.1.5). -/
theorem calcFinalAssetCost_matches_spec (base : AssetCost) (setRes : Option Nat)
    (increases reductions : List Nat) :
    AssetCostSpec base setRes increases reductions
      (calcFinalAssetCost base setRes increases reductions) := by
  unfold calcFinalAssetCost
  dsimp only
  have hset : (match setRes with | some v => v | none => base.resources) =
      setRes.getD base.resources := by cases setRes <;> rfl
  by_cases h : reductions.sum < setRes.getD base.resources + increases.sum
  · rw [hset]
    exact AssetCostSpec.positive (setRes.getD base.resources) rfl h
  · have hle : setRes.getD base.resources + increases.sum ≤ reductions.sum := by omega
    have hz : setRes.getD base.resources + increases.sum - reductions.sum = 0 := by omega
    rw [hset, hz]
    exact AssetCostSpec.floored (setRes.getD base.resources) rfl hle

/-- **L5** (uniqueness): `AssetCostSpec` determines the final `AssetCost` uniquely. -/
theorem AssetCostSpec.unique {base : AssetCost} {setRes : Option Nat}
    {inc red : List Nat} {out1 out2 : AssetCost}
    (h1 : AssetCostSpec base setRes inc red out1)
    (h2 : AssetCostSpec base setRes inc red out2) :
    out1 = out2 := by
  cases h1 with
  | floored a1 hs1 hl1 =>
    cases h2 with
    | floored _ _ _ => rfl
    | positive a2 hs2 hlt2 => subst hs1 hs2; omega
  | positive a1 hs1 hlt1 =>
    cases h2 with
    | floored a2 hs2 hl2 => subst hs1 hs2; omega
    | positive a2 hs2 _ => subst hs1 hs2; rfl

end Fab

end
