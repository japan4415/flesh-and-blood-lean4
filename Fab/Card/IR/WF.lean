module

public import Fab.Card.CardDef

/-!
# Static well-formedness of the Effect IR

Decidable static checks verifying target-slot bounds, lexical variable bindings, `X` cost
availability, modal non-emptiness, die-roll bounds, and target count ranges across `Effect`,
`EffectDef`, `Ability`, `CardFace`, and `CardDef` (design.md §7.1).
-/

@[expose] public section

namespace Fab

/-- Check whether a `PlayerRef` stays within `numSlots` declared target slots. -/
def PlayerRef.wfBool (numSlots : Nat) : PlayerRef → Bool
  | .ownerOfSlot i => decide (i < numSlots)
  | _ => true

/-- Check whether an `ObjRef` stays within `numSlots` target slots and bound variables `env`. -/
def ObjRef.wfBool (numSlots : Nat) (env : List VarId) : ObjRef → Bool
  | .slot i => decide (i < numSlots)
  | .declared _ => false
  | .var v => env.contains v
  | _ => true

/-- Check whether a `NumExpr` references only bound variables in `env`, and uses `xValue` only
when `hasX` is true. -/
def NumExpr.wfBool (numSlots : Nat) (env : List VarId) (hasX : Bool) : NumExpr → Bool
  | .const _ => true
  | .xValue => hasX
  | .sourceCounterCount _ => true
  | .varVal v => env.contains v
  | .handCount p => p.wfBool numSlots
  | .chainHits => true
  | .halfRoundDown v => env.contains v
  | .soulCount p => p.wfBool numSlots
  | .banishedCount p => p.wfBool numSlots

/-- Check whether a `Condition` stays within `numSlots` target slots. -/
def Condition.wfBool (numSlots : Nat) : Condition → Bool
  | .zoneCountGe p _ _ _ => p.wfBool numSlots
  | .zoneEmpty p _ => p.wfBool numSlots
  | .and_ a b => a.wfBool numSlots && b.wfBool numSlots
  | .or_ a b => a.wfBool numSlots && b.wfBool numSlots
  | .not_ c => c.wfBool numSlots
  | _ => true

/-- Check whether a `ModScope` stays within `numSlots` target slots and bound variables `env`. -/
def ModScope.wfBool (numSlots : Nat) (env : List VarId) : ModScope → Bool
  | .self_ => true
  | .obj ref => ref.wfBool numSlots env
  | .paidAttack _ => false
  | .targetedWeaponAttacks => decide (0 < numSlots)
  | .nextCardPlayed _ => true
  | .nextAttack _ => true
  | .allAttacks _ => true
  | .attackOrdinal n => decide (0 < n)
  | .nextDefend _ => true
  | .allMatching p _ => p.wfBool numSlots
  | .arenaObjectsOfType p _ => p.wfBool numSlots
  | .hero p | .player p => p.wfBool numSlots
  | .firstActionNextTurn p => p.wfBool numSlots
  | .firstAttackNextTurn p => p.wfBool numSlots
  | .playerActionsAndAttacks p => p.wfBool numSlots

/-- Check whether a `TargetKind` stays within `numSlots` target slots. -/
def TargetKind.wfBool (numSlots : Nat) : TargetKind → Bool
  | .weapon p => p.wfBool numSlots
  | .equipment p => p.wfBool numSlots
  | .cardInZone p _ => p.wfBool numSlots
  | _ => true

/-- Check whether a `TargetSpec` has a valid count range (`minCount ≤ maxCount` when bounded). -/
def TargetSpec.wfBool (numSlots : Nat) (t : TargetSpec) : Bool :=
  t.kind.wfBool numSlots &&
  match t.maxCount with
  | none => true
  | some hi => decide (t.minCount ≤ hi)

/-- Check whether a `Prim` stays within `numSlots`, `env`, and `hasX`. -/
def Prim.wfBool (numSlots : Nat) (env : List VarId) (hasX : Bool) : Prim → Bool
  | .weaponAttack => true
  | .draw p n => p.wfBool numSlots && n.wfBool numSlots env hasX
  | .discardRandom p n => p.wfBool numSlots && n.wfBool numSlots env hasX
  | .discardHandPrefix _ => true
  | .discardChoice p _ n => p.wfBool numSlots && n.wfBool numSlots env hasX
  | .dealDamage _ p n => p.wfBool numSlots && n.wfBool numSlots env hasX
  | .gainLife p n => p.wfBool numSlots && n.wfBool numSlots env hasX
  | .loseLife p n => p.wfBool numSlots && n.wfBool numSlots env hasX
  | .gainAP p n => p.wfBool numSlots && n.wfBool numSlots env hasX
  | .gainResource p n => p.wfBool numSlots && n.wfBool numSlots env hasX
  | .gainChi p n => p.wfBool numSlots && n.wfBool numSlots env hasX
  | .intimidate p => p.wfBool numSlots
  | .intimidateHandFront _ => true
  | .opt p _ => p.wfBool numSlots
  | .openBoosters _ => true
  | .createToken p _ _ | .createTokenForAttackDamage p _ => p.wfBool numSlots
  | .destroy o => o.wfBool numSlots env
  | .banish o _ => o.wfBool numSlots env
  | .moveCard o _ _ _ => o.wfBool numSlots env
  | .putHandOnDeck p _ => p.wfBool numSlots
  | .cycleArsenal p _ _ => p.wfBool numSlots
  | .putArsenalOnDeckBottom p => p.wfBool numSlots
  | .returnDefendingCardToHand _ | .returnChosenDefendingCard _ => true
  | .searchDeck p _ _ _ _ _ _ price =>
    p.wfBool numSlots && price.all (·.wfBool numSlots env hasX)
  | .putHandArsenal p _ _ _ => p.wfBool numSlots
  | .searchDeckToTop p _ | .putChosenDeckCardOnTop p _ | .reload p
  | .lookDeckToArsenal p _ _ | .putChosenDeckCardsOnBottom p _ => p.wfBool numSlots
  | .putHandPermanent p _ _ => p.wfBool numSlots
  | .shuffleZone p _ => p.wfBool numSlots
  | .shuffleZoneIntoDeck p _ _ _ _ => p.wfBool numSlots
  | .revealTopToArsenalIf p _ => p.wfBool numSlots
  | .addCounter o _ n | .removeCounter o _ n => o.wfBool numSlots env && n.wfBool numSlots env hasX
  | .removeAllCounters o _ => o.wfBool numSlots env
  | .preventNextDamage p n _ => p.wfBool numSlots && n.wfBool numSlots env hasX
  | .preventDamageOnce p n => p.wfBool numSlots && n.wfBool numSlots env hasX
  | .closeCombatChain => true
  | .charge p => p.wfBool numSlots
  | .banishFromSoul p _ => p.wfBool numSlots
  | .banishTopDeck p _ _ => p.wfBool numSlots
  | .banishFromGraveyard p _ _ => p.wfBool numSlots

/-- Whether `EffectList` is non-empty. -/
def EffectList.isNonEmpty : EffectList → Bool
  | .nil => false
  | .cons _ _ => true

mutual

/-- Static well-formedness check for `Effect`. -/
def Effect.wfBool (numSlots : Nat) (env : List VarId) (hasX : Bool) : Effect → Bool
  | .nop => true
  | .prim p => p.wfBool numSlots env hasX
  | .seq es => es.wfBool numSlots env hasX
  | .ifThen c t e =>
    c.wfBool numSlots && t.wfBool numSlots env hasX && e.wfBool numSlots env hasX
  | .may body ifDone =>
    body.wfBool numSlots env hasX && ifDone.wfBool numSlots env hasX
  | .chooseOne modes =>
    modes.isNonEmpty && modes.wfBool numSlots env hasX
  | .rollDie6 bindVar branches cont =>
    let env' := bindVar :: env
    branches.wfBool numSlots env' hasX && cont.wfBool numSlots env' hasX
  | .bindRevealTopCount p _ _ bindVar cont | .bindBanishTopCount p _ _ bindVar cont =>
    p.wfBool numSlots && cont.wfBool numSlots (bindVar :: env) hasX
  | .onBoostThisTurn body => body.wfBool 0 [] false
  | .discardTopOfHand p _ ifMatches otherwise =>
    p.wfBool numSlots && ifMatches.wfBool numSlots env hasX && otherwise.wfBool numSlots env hasX
  | .grant scope mod _ =>
    scope.wfBool numSlots env && mod.wfBool numSlots env hasX
  | .custom id _ => !id.val.isEmpty

/-- Static well-formedness check for `EffectList`. -/
def EffectList.wfBool (numSlots : Nat) (env : List VarId) (hasX : Bool) : EffectList → Bool
  | .nil => true
  | .cons h t => h.wfBool numSlots env hasX && t.wfBool numSlots env hasX

/-- Static well-formedness check for `DieBranchList` (each range must satisfy `1 ≤ lo ≤ hi ≤ 6`). -/
def DieBranchList.wfBool (numSlots : Nat) (env : List VarId) (hasX : Bool) : DieBranchList → Bool
  | .nil => true
  | .cons lo hi body tail =>
    decide (1 ≤ lo ∧ lo ≤ hi ∧ hi ≤ 6) &&
    body.wfBool numSlots env hasX &&
    tail.wfBool numSlots env hasX

/-- Static well-formedness check for `ContinuousMod`. -/
def ContinuousMod.wfBool (numSlots : Nat) (env : List VarId) (hasX : Bool) : ContinuousMod → Bool
  | .addPower d => d.wfBool numSlots env hasX
  | .addDefense d => d.wfBool numSlots env hasX
  | .addDefenseWhileDefending _ => true
  | .addIntellect _ => true
  | .modifyCost _ | .modifyPlayCostPerPermanent _ _ => true
  | .grantKeyword _ => true
  | .grantTrigger _ cond body =>
    (match cond with | none => true | some c => c.wfBool numSlots) &&
    body.wfBool numSlots env hasX
  | .conditionalPower c _ => c.wfBool numSlots
  | .loseAllAbilities => true
  | .cantGainGoAgain | .limitActions _ => true
  | .cantDrawCards | .onlyPlayFromArsenal => true
  | .additionalWeaponAttack => true
  | .doubleDamageToHero => true
  | .playableFromBanished => true

end

/-- Whether an extra-cost list declares `{x}` (binding `NumExpr.xValue`). -/
def hasXCost (ecs : List ExtraCostSpec) : Bool :=
  ecs.any fun ec => ec.cost == .payX

/-- Static well-formedness check for a `ModeSpec`. -/
def ModeSpec.wfBool (m : ModeSpec) (hasX : Bool) : Bool :=
  let numSlots := m.targets.length
  m.targets.all (TargetSpec.wfBool numSlots) &&
  m.body.wfBool numSlots [] hasX &&
  (m.onAttack.map (·.wfBool 0 [] false)).getD true

/-- Static well-formedness check for `EffectDef`, allowing inherited `hasX` from an enclosing
ability cost. Checks both direct targets/body and every per-mode `ModeSpec` (CR 5.1.2a). -/
def EffectDef.wfBool (ed : EffectDef) (inheritedHasX : Bool := false) : Bool :=
  let numSlots := ed.targets.length
  let hasX := inheritedHasX || hasXCost ed.extraCosts
  ed.extraCosts.all (fun ec => match ec.cond with | none => true | some c => c.wfBool numSlots) &&
  ed.targets.all (TargetSpec.wfBool numSlots) &&
  ed.body.wfBool numSlots [] hasX &&
  ed.onPayX.all (fun (_, body) => hasX && body.wfBool 0 [] true) &&
  ed.modes.all (fun m => m.wfBool hasX)

/-- Static well-formedness check for `Ability`. -/
def Ability.wfBool : Ability → Bool
  | .activated _ _ _ extraCosts cond _ effect =>
    let hasX := hasXCost extraCosts
    (match cond with | none => true | some c => c.wfBool effect.targets.length) &&
    effect.wfBool hasX
  | .triggered _ _ ordinal cond effect =>
    (match ordinal with | none => true | some k => decide (0 < k)) &&
    (match cond with | none => true | some c => c.wfBool effect.targets.length) &&
    effect.wfBool false
  | .static_ cond scope mod =>
    (match cond with | none => true | some c => c.wfBool 0) &&
    scope.wfBool 0 [] &&
    mod.wfBool 0 [] false
  | .replacement _ _ effect =>
    effect.wfBool false
  | .setupPermanent _ => true

/-- Static well-formedness check for a `CardFace`. -/
def CardFace.wfBool (f : CardFace) : Bool :=
  !f.name.isEmpty &&
  f.abilities.all Ability.wfBool &&
  match f.playEffect with
  | none => true
  | some ed => ed.wfBool (f.xCostFactor > 0)

/-- Static well-formedness check for a `CardDef` (front face and optional back/split faces). -/
def CardDef.wfBool (c : CardDef) : Bool :=
  !c.id.val.isEmpty &&
  c.front.wfBool &&
  (match c.back with | none => true | some b => b.wfBool) &&
  (match c.splitRight with | none => true | some r => r.wfBool)

/-- Static well-formedness proposition for a `CardDef`. -/
def CardDef.WF (c : CardDef) : Prop :=
  c.wfBool = true

instance CardDef.decidableWF (c : CardDef) : Decidable c.WF := by
  unfold CardDef.WF
  infer_instance

/-- `Effect.nop` is always statically well-formed. -/
theorem Effect.wfBool_nop (numSlots : Nat) (env : List VarId) (hasX : Bool) :
    Effect.nop.wfBool numSlots env hasX = true := rfl

/-- A well-formed `Effect.chooseOne` always has at least one mode. -/
theorem Effect.chooseOne_nonEmpty_of_wf {numSlots : Nat} {env : List VarId} {hasX : Bool}
    {modes : EffectList}
    (h : (Effect.chooseOne modes).wfBool numSlots env hasX = true) :
    modes.isNonEmpty = true := by
  unfold Effect.wfBool at h
  simp only [Bool.and_eq_true] at h
  exact h.1

/-- An out-of-bounds target slot fails `ObjRef.wfBool`. -/
theorem ObjRef.wfBool_slot_false_of_ge {numSlots i : Nat} {env : List VarId}
    (h : numSlots ≤ i) :
    (ObjRef.slot i).wfBool numSlots env = false := by
  unfold ObjRef.wfBool
  simp only [decide_eq_false_iff_not]
  omega

/-- An unbound variable fails `NumExpr.wfBool`. -/
theorem NumExpr.wfBool_varVal_false_of_not_mem {numSlots : Nat} {env : List VarId} {hasX : Bool}
    {v : VarId} (h : env.contains v = false) :
    (NumExpr.varVal v).wfBool numSlots env hasX = false :=
  h

/-- Using `xValue` without an `ExtraCost.payX` declaration fails `NumExpr.wfBool`. -/
theorem NumExpr.wfBool_xValue_false (numSlots : Nat) (env : List VarId) :
    NumExpr.xValue.wfBool numSlots env false = false := rfl

end Fab

end
