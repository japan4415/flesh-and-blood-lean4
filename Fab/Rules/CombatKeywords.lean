module

public import Fab.Rules.Combat
public import Fab.Rules.Actions.Banish

/-!
# Combat Keywords & End-Phase Triggers (CR 8.3)

Implements and verifies core Flesh and Blood combat and turn-end keywords:
- **Combo** (CR 8.3.6): checks previous `ChainLink`'s `attackLki.name` (even if the card left the chain).
- **Crush** (CR 8.3.7): triggers when an attack deals `≥ 4` combat damage.
- **Reprise** (CR 8.3.8): active when the defending hero defended with a card from hand.
- **Boost** (CR 8.3.9): banishes top card of deck face-up; if Mechanologist, grants `Go Again`.
- **Blood Debt** (CR 8.3.12): loses 1 life per **face-up** Blood Debt card in the Banished zone at
  End Phase (face-down banished cards do NOT trigger Blood Debt).
- **Phantasm** (CR 8.3.13): destroys the attack and closes the Combat Chain if defended by a
  non-Illusionist Attack Action card with derived effective power `≥ 6`.
- **Spectra** (CR 8.3.14): destroys the Spectra permanent and closes the Combat Chain when targeted
  by an attack.
- **Stealth** (CR 8.3.24): identifies Stealth attacks for Assassin reaction/contract hooks.
-/

@[expose] public section

namespace Fab

/-- **Combo** (CR 8.3.6): true iff the immediately preceding `ChainLink` on the active combat chain
had an attack whose `LkiSnapshot.name` is in `prevNames`. -/
def comboActive (s : GameState) (prevNames : List String) : Bool :=
  match s.combat.bind CombatChain.prevLink? with
  | some prev => prevNames.contains prev.attackLki.name
  | none => false

/-- **Crush** (CR 8.3.7): true iff the attack on `link` dealt 4 or more damage. -/
def crushTriggered (link : ChainLink) : Bool :=
  decide (4 ≤ link.damageDealt)

/-- **Reprise** (CR 8.3.8): true iff the defending hero defended `link` with at least one card from
hand. -/
def repriseActive (link : ChainLink) : Bool :=
  decide (0 < link.defendedFromHandCount)

/-- **Stealth** (CR 8.3.24): true iff object `id` has the `Stealth` keyword in its derived
characteristics. -/
def isStealthAttack (s : GameState) (id : ObjId) : Bool :=
  match s.characteristics id with
  | some dc => dc.keywords.contains .stealth
  | none => false

/-- Whether defending object `id` triggers **Phantasm** (CR 8.3.13): it is a non-Illusionist Attack
Action card with derived effective power `≥ 6`. -/
def triggersPhantasmDef (s : GameState) (id : ObjId) : Bool :=
  match s.characteristics id with
  | some dc =>
    dc.types.contains .action &&
    dc.subtypes.contains .attack &&
    !(dc.supertypes.contains (.class_ .illusionist)) &&
    match dc.power with
    | some p => decide (6 ≤ p)
    | none => false
  | none => false

/-- **Phantasm** (CR 8.3.13): true iff `link`'s attack has `Phantasm` and is defended by a
non-Illusionist Attack Action card with effective power `≥ 6`. -/
def phantasmTriggered (s : GameState) (link : ChainLink) : Bool :=
  linkHasKeyword s link .phantasm && link.defending.any (triggersPhantasmDef s)

/-- Destroy object `id` by moving physical cards to owner's graveyard and removing non-physical
objects (tokens, layers, attack-proxies) (CR 8.5.4). -/
def destroyObjToGraveyard (s : GameState) (id : ObjId) : GameState × List Event :=
  match s.locate id, s.obj? id with
  | some srcZ, some o =>
    if o.kind.phys?.isNone then
      (removeNonPhysObj s id, [])
    else
      match moveObj s id (.player o.owner .graveyard) .top false with
      | some (s1, id') => (s1, [.moved id id' srcZ (.player o.owner .graveyard)])
      | none => (s, [])
  | _, _ => (s, [])

/-- `destroyObjToGraveyard` preserves `WF`, `OwnerOk`, `physIds`, `config`, and `playRollback`. -/
theorem destroyObjToGraveyard_inv {s : GameState} (hwf : s.WF) (hok : s.OwnerOk) (id : ObjId) :
    (destroyObjToGraveyard s id).1.WF ∧
    (destroyObjToGraveyard s id).1.OwnerOk ∧
    (destroyObjToGraveyard s id).1.physIds.Perm s.physIds ∧
    (destroyObjToGraveyard s id).1.config = s.config ∧
    (destroyObjToGraveyard s id).1.playRollback = s.playRollback := by
  unfold destroyObjToGraveyard
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
      · cases hm : moveObj s id (.player o.owner .graveyard) .top false with
        | none => exact ⟨hwf, hok, List.Perm.refl _, rfl, rfl⟩
        | some res =>
          have hmeta := moveObj_config_rollback hm
          exact ⟨moveObj_wf hwf hm, moveObj_ownerOk hwf hok hm,
                 moveObj_physIds hwf hm, hmeta.1, hmeta.2⟩

/-- `destroyObjToGraveyard` preserves `turn`, `tournament`, and `result`. -/
theorem destroyObjToGraveyard_ttr (s : GameState) (id : ObjId) :
    (destroyObjToGraveyard s id).1.turn = s.turn ∧
    (destroyObjToGraveyard s id).1.tournament = s.tournament ∧
    (destroyObjToGraveyard s id).1.result = s.result := by
  unfold destroyObjToGraveyard
  cases s.locate id with
  | none => exact ⟨rfl, rfl, rfl⟩
  | some srcZ =>
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
      · cases hm : moveObj s id (.player o.owner .graveyard) .top false with
        | none => exact ⟨rfl, rfl, rfl⟩
        | some res =>
          unfold moveObj at hm
          split at hm
          · dsimp only at hm
            split at hm
            · cases hm
            · split at hm <;>
              · simp only [Option.some.injEq] at hm
                subst hm; exact ⟨rfl, rfl, rfl⟩
          · cases hm

/-- Resolve **Phantasm** destruction (CR 8.3.13): destroys the active link's attack and immediately
closes the Combat Chain. -/
def applyPhantasmClose (s : GameState) : GameState × List Event :=
  let (s1, es1) :=
    match s.combat.bind CombatChain.activeLink? with
    | some link =>
      match link.attack with
      | some atkId => destroyObjToGraveyard s atkId
      | none => (s, [])
    | none => (s, [])
  let (s2, es2) := closeCombatChainStep s1
  (s2, es1 ++ es2)

/-- `applyPhantasmClose` preserves `WF`, `OwnerOk`, `physIds`, `config`, and `playRollback`. -/
theorem applyPhantasmClose_inv {s : GameState} (hwf : s.WF) (hok : s.OwnerOk) :
    (applyPhantasmClose s).1.WF ∧
    (applyPhantasmClose s).1.OwnerOk ∧
    (applyPhantasmClose s).1.physIds.Perm s.physIds ∧
    (applyPhantasmClose s).1.config = s.config ∧
    (applyPhantasmClose s).1.playRollback = s.playRollback := by
  unfold applyPhantasmClose
  have h1 : let p1 := match s.combat.bind CombatChain.activeLink? with
      | some link =>
        match link.attack with
        | some atkId => destroyObjToGraveyard s atkId
        | none => (s, [])
      | none => (s, [])
      p1.1.WF ∧ p1.1.OwnerOk ∧ p1.1.physIds.Perm s.physIds ∧
      p1.1.config = s.config ∧ p1.1.playRollback = s.playRollback := by
    cases s.combat.bind CombatChain.activeLink? with
    | none => exact ⟨hwf, hok, List.Perm.refl _, rfl, rfl⟩
    | some link =>
      dsimp only
      cases link.attack with
      | none => exact ⟨hwf, hok, List.Perm.refl _, rfl, rfl⟩
      | some atkId => exact destroyObjToGraveyard_inv hwf hok atkId
  obtain ⟨hwf1, hok1, hp1, hc1, hr1⟩ := h1
  obtain ⟨hwf2, hok2, hp2, hc2, hr2⟩ := closeCombatChainStep_inv hwf1 hok1
  exact ⟨hwf2, hok2, hp2.trans hp1, hc2.trans hc1, hr2.trans hr1⟩

/-- Resolve **Spectra** destruction (CR 8.3.14): destroys the targeted Spectra permanent and
immediately closes the Combat Chain. -/
def applySpectraClose (s : GameState) (targetId : ObjId) : GameState × List Event :=
  let (s1, es1) := destroyObjToGraveyard s targetId
  let (s2, es2) := closeCombatChainStep s1
  (s2, es1 ++ es2)

/-- `applySpectraClose` preserves `WF`, `OwnerOk`, `physIds`, `config`, and `playRollback`. -/
theorem applySpectraClose_inv {s : GameState} (hwf : s.WF) (hok : s.OwnerOk) (targetId : ObjId) :
    (applySpectraClose s targetId).1.WF ∧
    (applySpectraClose s targetId).1.OwnerOk ∧
    (applySpectraClose s targetId).1.physIds.Perm s.physIds ∧
    (applySpectraClose s targetId).1.config = s.config ∧
    (applySpectraClose s targetId).1.playRollback = s.playRollback := by
  unfold applySpectraClose
  obtain ⟨hwf1, hok1, hp1, hc1, hr1⟩ := destroyObjToGraveyard_inv hwf hok targetId
  obtain ⟨hwf2, hok2, hp2, hc2, hr2⟩ := closeCombatChainStep_inv hwf1 hok1
  exact ⟨hwf2, hok2, hp2.trans hp1, hc2.trans hc1, hr2.trans hr1⟩

/-- Resolve **Boost** (CR 8.3.9): banishes the top card of `p`'s deck face-up; if the banished card
is a Mechanologist card, returns `true` and grants `.goAgain` to the active `ChainLink`. -/
def applyBoost (s : GameState) (p : PlayerId) : GameState × Bool × List Event :=
  match s.zone (.player p .deck) with
  | [] => (s, false, [])
  | topId :: _ =>
    let isMech :=
      match s.cardDefOf? topId with
      | some c => c.front.supertypes.contains (.class_ .mechanologist)
      | none => false
    match banishOne s topId false with
    | none => (s, false, [])
    | some (s1, _, es) =>
      let s2 :=
        if isMech then
          { s1 with combat := s1.combat.map fun cc => cc.updateActiveLink fun l =>
              { l with grantedKeywords := .goAgain :: l.grantedKeywords } }
        else
          s1
      (s2, isMech, es)

/-- `applyBoost` preserves `WF`, `OwnerOk`, `physIds`, `config`, and `playRollback`. -/
theorem applyBoost_inv {s : GameState} (hwf : s.WF) (hok : s.OwnerOk) (p : PlayerId) :
    (applyBoost s p).1.WF ∧
    (applyBoost s p).1.OwnerOk ∧
    (applyBoost s p).1.physIds.Perm s.physIds ∧
    (applyBoost s p).1.config = s.config ∧
    (applyBoost s p).1.playRollback = s.playRollback := by
  unfold applyBoost
  cases s.zone (.player p .deck) with
  | nil => exact ⟨hwf, hok, List.Perm.refl _, rfl, rfl⟩
  | cons topId _ =>
    dsimp only
    cases hb : banishOne s topId false with
    | none => exact ⟨hwf, hok, List.Perm.refl _, rfl, rfl⟩
    | some res =>
      obtain ⟨s1, id1, es1⟩ := res
      dsimp only
      have hwf1 := banishOne_wf hwf hb
      have hok1 := banishOne_ownerOk hwf hok hb
      have hp1 := banishOne_physIds hwf hb
      have hmeta : s1.config = s.config ∧ s1.playRollback = s.playRollback := by
        unfold banishOne at hb
        split at hb
        · rename_i src0 o0 _ _
          dsimp only at hb
          cases hm : moveObj s topId (Zone.player o0.owner .banished) .top false with
          | none => simp only [hm] at hb; cases hb
          | some rm =>
            obtain ⟨sm, idm⟩ := rm
            simp only [hm, Option.some.injEq, Prod.mk.injEq] at hb
            obtain ⟨rfl, rfl, rfl⟩ := hb
            exact moveObj_config_rollback hm
        · cases hb
      cases (match s.cardDefOf? topId with
        | some c => c.front.supertypes.contains (.class_ .mechanologist)
        | none => false) with
      | true =>
        exact ⟨GameState.WF.congr hwf1 rfl rfl rfl rfl,
               GameState.OwnerOk.congr hok1 rfl rfl,
               hp1, hmeta.1, hmeta.2⟩
      | false =>
        exact ⟨hwf1, hok1, hp1, hmeta.1, hmeta.2⟩

/-- Whether object `id` is a **face-up** card with **Blood Debt** (CR 8.3.12). -/
def isFaceUpBloodDebt (s : GameState) (id : ObjId) : Bool :=
  match s.obj? id, s.cardDefOf? id with
  | some o, some c => !o.faceDown && c.front.keywords.contains .bloodDebt
  | _, _ => false

/-- Number of face-up Blood Debt cards in player `p`'s Banished zone (CR 8.3.12). -/
def bloodDebtCount (s : GameState) (p : PlayerId) : Nat :=
  ((s.zone (.player p .banished)).filter (isFaceUpBloodDebt s)).length

/-- Apply **Blood Debt** at the beginning of player `p`'s End Phase (CR 8.3.12):
player `p` loses 1 life for each face-up Blood Debt card in their Banished zone.
No-op when `bloodDebtCount s p = 0`. -/
def applyBloodDebt (s : GameState) (p : PlayerId) : GameState × List Event :=
  let cnt := bloodDebtCount s p
  if cnt = 0 then
    (s, [])
  else
    let s1 := checkHeroDefeat (s.setLife p (s.lifeOf p - Int.ofNat cnt))
    (s1, [.lifeLost p cnt])

/-- When `bloodDebtCount s p = 0`, `applyBloodDebt` returns `(s, [])` unchanged. -/
theorem applyBloodDebt_zero {s : GameState} {p : PlayerId} (hz : bloodDebtCount s p = 0) :
    applyBloodDebt s p = (s, []) := by
  unfold applyBloodDebt
  simp [hz]

/-- `applyBloodDebt` preserves `WF`, `OwnerOk`, `physIds` (equality), `config`, and `playRollback`. -/
theorem applyBloodDebt_inv {s : GameState} (hwf : s.WF) (hok : s.OwnerOk) (p : PlayerId) :
    (applyBloodDebt s p).1.WF ∧
    (applyBloodDebt s p).1.OwnerOk ∧
    (applyBloodDebt s p).1.physIds = s.physIds ∧
    (applyBloodDebt s p).1.config = s.config ∧
    (applyBloodDebt s p).1.playRollback = s.playRollback := by
  unfold applyBloodDebt
  dsimp only
  split
  · exact ⟨hwf, hok, rfl, rfl, rfl⟩
  · have hwf1 : (s.setLife p (s.lifeOf p - Int.ofNat (bloodDebtCount s p))).WF :=
      GameState.WF.congr hwf rfl rfl rfl rfl
    have hok1 : (s.setLife p (s.lifeOf p - Int.ofNat (bloodDebtCount s p))).OwnerOk :=
      GameState.OwnerOk.congr hok rfl rfl
    have hchk_wf : (checkHeroDefeat (s.setLife p (s.lifeOf p - Int.ofNat (bloodDebtCount s p)))).WF := by
      unfold checkHeroDefeat
      split
      · exact hwf1
      · cases livingPlayers _ with
        | nil => exact GameState.WF.congr hwf1 rfl rfl rfl rfl
        | cons _ ws =>
          cases ws with
          | nil => exact GameState.WF.congr hwf1 rfl rfl rfl rfl
          | cons _ _ => exact hwf1
    have hchk_ok : (checkHeroDefeat (s.setLife p (s.lifeOf p - Int.ofNat (bloodDebtCount s p)))).OwnerOk := by
      unfold checkHeroDefeat
      split
      · exact hok1
      · cases livingPlayers _ with
        | nil => exact GameState.OwnerOk.congr hok1 rfl rfl
        | cons _ ws =>
          cases ws with
          | nil => exact GameState.OwnerOk.congr hok1 rfl rfl
          | cons _ _ => exact hok1
    have hchk_phys : (checkHeroDefeat (s.setLife p (s.lifeOf p - Int.ofNat (bloodDebtCount s p)))).physIds = s.physIds := by
      unfold checkHeroDefeat
      split
      · rfl
      · cases livingPlayers _ with
        | nil => rfl
        | cons _ ws => cases ws <;> rfl
    have hchk_meta :
        (checkHeroDefeat (s.setLife p (s.lifeOf p - Int.ofNat (bloodDebtCount s p)))).config = s.config ∧
        (checkHeroDefeat (s.setLife p (s.lifeOf p - Int.ofNat (bloodDebtCount s p)))).playRollback = s.playRollback := by
      unfold checkHeroDefeat
      split
      · exact ⟨rfl, rfl⟩
      · cases livingPlayers _ with
        | nil => exact ⟨rfl, rfl⟩
        | cons _ ws => cases ws <;> exact ⟨rfl, rfl⟩
    exact ⟨hchk_wf, hchk_ok, hchk_phys, hchk_meta.1, hchk_meta.2⟩

/-- `applyBloodDebt` preserves `turn` and `tournament`, and never clears a set `result`. -/
theorem applyBloodDebt_ttr (s : GameState) (p : PlayerId) :
    (applyBloodDebt s p).1.turn = s.turn ∧
    (applyBloodDebt s p).1.tournament = s.tournament ∧
    ((applyBloodDebt s p).1.result = none → s.result = none) := by
  unfold applyBloodDebt
  dsimp only
  split
  · exact ⟨rfl, rfl, id⟩
  · unfold checkHeroDefeat
    split
    · exact ⟨rfl, rfl, id⟩
    · cases livingPlayers _ with
      | nil => exact ⟨rfl, rfl, fun h => by cases h⟩
      | cons _ ws =>
        cases ws with
        | nil => exact ⟨rfl, rfl, fun h => by cases h⟩
        | cons _ _ => exact ⟨rfl, rfl, id⟩

end Fab

end
