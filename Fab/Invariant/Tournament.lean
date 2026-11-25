module

public import Fab.Invariant.Step
public import Fab.Tournament.Match

/-!
# Tournament Rules and Policy invariants (M5b)

Proves M5b theorems from `docs/roadmap.md` and `docs/tournament-model.md`:
- **I14** (End-of-Round time limit termination bound): once `Actor.clock` signals `timeExpired`
  at turn `T`, every subsequent ongoing state across any trace of `step`s satisfies
  `s'.turn ≤ T + 1` (current turn finishes + at most 1 additional turn), and reaching `beginTurn`
  after the additional turn (`timeLimitTurnsLeft = some 0`) immediately ends the game in
  `GameResult.draw .timeLimit` (TRP 4):
  `timeExpired_sets_bound`, `microStep_preserves_timeLimit`, `advance_preserves_timeLimit`,
  `step_preserves_timeLimit`, `timeLimit_at_most_two_turns`, `beginTurn_zero_ends_timeLimit`
- **Top Cut Intentional Draw Prohibition**: under `RuleSet.tournament .topCut`, none of
  `offerDraw`, `acceptDraw`, `declineDraw` is `Legal` or present in `legalActions` (TRP 4):
  `topCut_forbids_intentional_draw`, `topCut_legalActions_no_draw`
- **Swiss Bo1 Intentional Draw & Clock/Judge Ruleset Guards**:
  `swiss_offer_accept_draws`, `swiss_self_accept_forbidden`, `topCut_forbids_timeExpired`,
  `coreOnly_forbids_timeExpired`, `clock_second_timeExpired_forbidden`,
  `judgeLoopDraw_legal_iff`, `judgeLoopDraw_ends_in_loop_draw`, `coreOnly_forbids_judgeLoopDraw`
-/

@[expose] public section

namespace Fab

/-- Invariant asserting that whenever `s` is still ongoing (`s.result = none`), a tournament
time-limit countdown `k` is active and `s.turn + k ≤ deadline` (**I14**) (TRP 4). -/
def TimeLimitBounded (deadline : Nat) (s : GameState) : Prop :=
  s.result = none → ∃ k, s.tournament.timeLimitTurnsLeft = some k ∧ s.turn + k ≤ deadline

/-- Helper: `removeNonPhysObj` preserves `turn`, `tournament`, and `result`. -/
theorem removeNonPhysObj_turn_tournament_result (s : GameState) (id : ObjId) :
    (removeNonPhysObj s id).turn = s.turn ∧ (removeNonPhysObj s id).tournament = s.tournament ∧
    (removeNonPhysObj s id).result = s.result := by
  unfold removeNonPhysObj
  cases s.locate id with
  | none => exact ⟨rfl, rfl, rfl⟩
  | some _ =>
    cases s.obj? id with
    | none => exact ⟨rfl, rfl, rfl⟩
    | some _ => dsimp only; split <;> exact ⟨rfl, rfl, rfl⟩

/-- Helper: `moveObj` preserves `turn`, `tournament`, and `result`. -/
theorem moveObj_turn_tournament_result {s s' : GameState} {id id' : ObjId} {dst : Zone}
    {pos : Pos} {fd : Bool} (h : moveObj s id dst pos fd = some (s', id')) :
    s'.turn = s.turn ∧ s'.tournament = s.tournament ∧ s'.result = s.result := by
  unfold moveObj at h
  split at h
  · dsimp only at h
    split at h
    · cases h
    · split at h <;>
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl, rfl⟩
  · cases h

/-- Helper: `gspStep` preserves `turn` and `tournament`. -/
theorem gspStep_turn_tournament {s s' : GameState} (h : gspStep s = some s') :
    s'.turn = s.turn ∧ s'.tournament = s.tournament := by
  unfold gspStep at h
  split at h
  · simp only [Option.some.injEq] at h; subst h
    unfold checkHeroDefeat
    split
    · exact ⟨rfl, rfl⟩
    · cases livingPlayers s with
      | nil => exact ⟨rfl, rfl⟩
      | cons _ ws => cases ws <;> exact ⟨rfl, rfl⟩
  · cases h1 : nonArenaNonPhys s with
    | cons id _ =>
      rw [h1] at h; simp only [Option.some.injEq] at h; subst h
      have hr := removeNonPhysObj_turn_tournament_result s id
      exact ⟨hr.1, hr.2.1⟩
    | nil =>
      rw [h1] at h
      cases h2 : gspPermanentsToClear s with
      | nil => rw [h2] at h; cases h
      | cons id _ =>
        rw [h2] at h; dsimp only at h
        cases ho : s.obj? id with
        | none => rw [ho] at h; cases h
        | some o =>
          rw [ho] at h; dsimp only at h
          split at h
          · simp only [Option.some.injEq] at h; subst h
            have hr := removeNonPhysObj_turn_tournament_result s id
            exact ⟨hr.1, hr.2.1⟩
          · cases hm : moveObj s id (.player o.owner .graveyard) .top false with
            | none => rw [hm] at h; cases h
            | some _ =>
              rw [hm] at h; simp only [Option.some.injEq] at h; subst h
              have hm' := moveObj_turn_tournament_result hm
              exact ⟨hm'.1, hm'.2.1⟩

/-- Helper: `gspLoop` preserves `turn` and `tournament`. -/
theorem gspLoop_turn_tournament :
    ∀ (n : Nat) (s : GameState),
      (gspLoop n s).turn = s.turn ∧ (gspLoop n s).tournament = s.tournament
  | 0, _ => ⟨rfl, rfl⟩
  | n + 1, s => by
    unfold gspLoop
    cases hs : gspStep s with
    | none => exact ⟨rfl, rfl⟩
    | some s' =>
      have h1 := gspStep_turn_tournament hs
      have h2 := gspLoop_turn_tournament n s'
      exact ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩

/-- Helper: `gspRun` preserves `turn` and `tournament`. -/
theorem gspRun_turn_tournament (s : GameState) :
    (gspRun s).turn = s.turn ∧ (gspRun s).tournament = s.tournament :=
  gspLoop_turn_tournament (gspMeasure s) s

/-- Helper: `addObject` preserves `turn`, `tournament`, and `result`. -/
theorem addObject_turn_tournament_result {s s' : GameState} {z : Zone} {o : Object} {pos : Pos}
    {id' : ObjId} (h : addObject s z o pos = some (s', id')) :
    s'.turn = s.turn ∧ s'.tournament = s.tournament ∧ s'.result = s.result := by
  unfold addObject at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl, rfl⟩
  · cases h

/-- Helper: `drawOne` preserves `turn`, `tournament`, and `result`. -/
theorem drawOne_turn_tournament_result (s : GameState) (p : PlayerId) :
    (drawOne s p).1.turn = s.turn ∧ (drawOne s p).1.tournament = s.tournament ∧
    (drawOne s p).1.result = s.result := by
  unfold drawOne
  cases s.zone (.player p .deck) with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons id _ =>
    dsimp only
    cases hm : moveObj s id (.player p .hand) .top false with
    | none => exact ⟨rfl, rfl, rfl⟩
    | some res => exact moveObj_turn_tournament_result hm

/-- Helper: `updateSingleObject` preserves `turn`, `tournament`, and `result`. -/
theorem updateSingleObject_turn_tournament_result (s : GameState) (id : ObjId)
    (f : Object → Object) :
    (updateSingleObject s id f).turn = s.turn ∧ (updateSingleObject s id f).tournament = s.tournament ∧
    (updateSingleObject s id f).result = s.result := by
  unfold updateSingleObject
  cases s.objects[id.n]? <;> exact ⟨rfl, rfl, rfl⟩

/-- Helper: `applyEquipmentWear` preserves `turn`, `tournament`, and `result`. -/
theorem applyEquipmentWear_turn_tournament_result (s : GameState) (id : ObjId) :
    (applyEquipmentWear s id).1.turn = s.turn ∧ (applyEquipmentWear s id).1.tournament = s.tournament ∧
    (applyEquipmentWear s id).1.result = s.result := by
  unfold applyEquipmentWear
  cases s.obj? id with
  | none => exact ⟨rfl, rfl, rfl⟩
  | some _ =>
    cases s.cardDefOf? id with
    | none => exact ⟨rfl, rfl, rfl⟩
    | some _ =>
      dsimp only
      split
      · cases hm : moveObj s id _ .top false with
        | none => exact ⟨rfl, rfl, rfl⟩
        | some _ => exact moveObj_turn_tournament_result hm
      · split
        · have hu := updateSingleObject_turn_tournament_result s id
            (fun obj => obj.addCounterVal .minusOneDefense 1)
          split
          · cases hm : moveObj _ id _ .top false with
            | none => exact hu
            | some _ =>
              have hm' := moveObj_turn_tournament_result hm
              exact ⟨hm'.1.trans hu.1, hm'.2.1.trans hu.2.1, hm'.2.2.trans hu.2.2⟩
          · cases hm : moveObj _ id _ .top false with
            | none => exact hu
            | some _ =>
              have hm' := moveObj_turn_tournament_result hm
              exact ⟨hm'.1.trans hu.1, hm'.2.1.trans hu.2.1, hm'.2.2.trans hu.2.2⟩
        · split
          · have hu := updateSingleObject_turn_tournament_result s id
              (fun obj => obj.addCounterVal .minusOneDefense 1)
            cases hm : moveObj _ id _ .top false with
            | none => exact hu
            | some _ =>
              have hm' := moveObj_turn_tournament_result hm
              exact ⟨hm'.1.trans hu.1, hm'.2.1.trans hu.2.1, hm'.2.2.trans hu.2.2⟩
          · split
            · have hu := updateSingleObject_turn_tournament_result s id
                (fun obj => obj.addCounterVal .minusOneDefense (clampNonNeg ((objEffectiveDefense s id).getD 0)))
              cases hm : moveObj _ id _ .top false with
              | none => exact hu
              | some _ =>
                have hm' := moveObj_turn_tournament_result hm
                exact ⟨hm'.1.trans hu.1, hm'.2.1.trans hu.2.1, hm'.2.2.trans hu.2.2⟩
            · cases hm : moveObj s id _ .top false with
              | none => exact ⟨rfl, rfl, rfl⟩
              | some _ => exact moveObj_turn_tournament_result hm

/-- Helper: `closeChainObj` preserves `turn`, `tournament`, and `result`. -/
theorem closeChainObj_turn_tournament_result (s : GameState) (id : ObjId) :
    (closeChainObj s id).1.turn = s.turn ∧ (closeChainObj s id).1.tournament = s.tournament ∧
    (closeChainObj s id).1.result = s.result := by
  unfold closeChainObj
  cases s.obj? id with
  | none => exact ⟨rfl, rfl, rfl⟩
  | some o =>
    dsimp only
    cases o.kind with
    | attackProxy _ _ | token _ | layer _ _ _ _ =>
      exact removeNonPhysObj_turn_tournament_result s id
    | card _ _ =>
      dsimp only
      cases s.cardDefOf? id with
      | none =>
        dsimp only
        cases hm : moveObj s id (.player o.owner .graveyard) .top false with
        | none => exact ⟨rfl, rfl, rfl⟩
        | some _ => exact moveObj_turn_tournament_result hm
      | some _ =>
        dsimp only
        split
        · cases hm : moveObj s id _ .top false with
          | none => exact ⟨rfl, rfl, rfl⟩
          | some _ => exact moveObj_turn_tournament_result hm
        · split
          · exact applyEquipmentWear_turn_tournament_result s id
          · cases hm : moveObj s id _ .top false with
            | none => exact ⟨rfl, rfl, rfl⟩
            | some _ => exact moveObj_turn_tournament_result hm

/-- Helper: `closeChainList` preserves `turn`, `tournament`, and `result`. -/
theorem closeChainList_turn_tournament_result (s : GameState) :
    ∀ ids, (closeChainList s ids).1.turn = s.turn ∧
      (closeChainList s ids).1.tournament = s.tournament ∧
      (closeChainList s ids).1.result = s.result
  | [] => ⟨rfl, rfl, rfl⟩
  | id :: rest => by
    unfold closeChainList
    have h1 := closeChainObj_turn_tournament_result s id
    have h2 := closeChainList_turn_tournament_result (closeChainObj s id).1 rest
    exact ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.trans h1.2.2⟩

/-- Helper: `removeStaleProxies` preserves `turn`, `tournament`, and `result`. -/
theorem removeStaleProxies_turn_tournament_result (wid : ObjId) :
    ∀ ids (s : GameState),
      (removeStaleProxies s wid ids).turn = s.turn ∧
      (removeStaleProxies s wid ids).tournament = s.tournament ∧
      (removeStaleProxies s wid ids).result = s.result
  | [], _ => ⟨rfl, rfl, rfl⟩
  | id :: rest, s => by
    unfold removeStaleProxies
    let s1 :=
      match s.obj? id with
      | some o =>
        match o.kind with
        | .attackProxy src _ => if src == wid then removeNonPhysObj s id else s
        | _ => s
      | none => s
    have h1 : s1.turn = s.turn ∧ s1.tournament = s.tournament ∧ s1.result = s.result := by
      dsimp only [s1]
      cases s.obj? id with
      | none => exact ⟨rfl, rfl, rfl⟩
      | some o =>
        dsimp only
        cases o.kind with
        | attackProxy src _ =>
          dsimp only
          by_cases he : (src == wid) = true
          · simp only [he, ↓reduceIte]
            exact removeNonPhysObj_turn_tournament_result s id
          · simp only [he]
            exact ⟨rfl, rfl, rfl⟩
        | _ => exact ⟨rfl, rfl, rfl⟩
    have h2 := removeStaleProxies_turn_tournament_result wid rest s1
    exact ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.trans h1.2.2⟩

/-- Helper: `enterAttackStep` preserves `turn`, `tournament`, and `result`. -/
theorem enterAttackStep_turn_tournament_result (s : GameState) (layerId : ObjId) (atk : PlayerId) :
    (enterAttackStep s layerId atk).1.turn = s.turn ∧
    (enterAttackStep s layerId atk).1.tournament = s.tournament ∧
    (enterAttackStep s layerId atk).1.result = s.result := by
  unfold enterAttackStep
  dsimp only
  let srcW : Option ObjId :=
    match s.obj? layerId with
    | some o => match o.kind with | .attackProxy wid _ => some wid | _ => none
    | none => none
  let s0 := match srcW with | some wid => removeStaleProxies s wid (s.zone .combatChain) | none => s
  have h0 : s0.turn = s.turn ∧ s0.tournament = s.tournament ∧ s0.result = s.result := by
    dsimp only [s0]
    cases srcW with
    | none => exact ⟨rfl, rfl, rfl⟩
    | some wid => exact removeStaleProxies_turn_tournament_result wid (s.zone .combatChain) s
  let p1 :=
    match srcW with
    | some wid =>
      if wid ∈ s0.zone (.player atk .weapon) then
        match moveObj s0 wid .combatChain .top false with
        | some (sw, wid') => (sw, [Event.moved wid wid' (.player atk .weapon) .combatChain])
        | none => (s0, [])
      else (s0, [])
    | none => (s0, [])
  have h1 : p1.1.turn = s0.turn ∧ p1.1.tournament = s0.tournament ∧ p1.1.result = s0.result := by
    dsimp only [p1]
    cases srcW with
    | none => exact ⟨rfl, rfl, rfl⟩
    | some wid =>
      dsimp only
      split
      · cases hm : moveObj s0 wid .combatChain .top false with
        | none => exact ⟨rfl, rfl, rfl⟩
        | some _ => exact moveObj_turn_tournament_result hm
      · exact ⟨rfl, rfl, rfl⟩
  let p2 :=
    match moveObj p1.1 layerId .combatChain .top false with
    | some (sa, aid) => (sa, aid, [Event.moved layerId aid .stack .combatChain])
    | none => (p1.1, layerId, [])
  have h2 : p2.1.turn = p1.1.turn ∧ p2.1.tournament = p1.1.tournament ∧ p2.1.result = p1.1.result := by
    dsimp only [p2]
    cases hm : moveObj p1.1 layerId .combatChain .top false with
    | none => exact ⟨rfl, rfl, rfl⟩
    | some _ => exact moveObj_turn_tournament_result hm
  exact ⟨(h2.1.trans h1.1).trans h0.1,
         (h2.2.1.trans h1.2.1).trans h0.2.1,
         (h2.2.2.trans h1.2.2).trans h0.2.2⟩

/-- Helper: `checkHeroDefeat` preserves `turn` and `tournament`, and never clears a set `result`. -/
theorem checkHeroDefeat_ttr (s : GameState) :
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

/-- Helper: `createTokens` preserves `turn`, `tournament`, and `result`. -/
theorem createTokens_ttr (p : PlayerId) (tokId : CardId) :
    ∀ (n : Nat) (s : GameState),
      (createTokens s p tokId n).turn = s.turn ∧
      (createTokens s p tokId n).tournament = s.tournament ∧
      (createTokens s p tokId n).result = s.result
  | 0, _ => ⟨rfl, rfl, rfl⟩
  | n + 1, s => by
    unfold createTokens
    dsimp only
    cases ha : addObject s (.player p .permanent)
        { kind := .token tokId, owner := p, controller := p, timestamp := ⟨s.nextTimestamp⟩ } .top with
    | none => exact ⟨rfl, rfl, rfl⟩
    | some res =>
      have h1 := addObject_turn_tournament_result ha
      have h2 := createTokens_ttr p tokId n res.1
      exact ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.trans h1.2.2⟩

/-- Helper: `execPrim` preserves `turn` and `tournament`, and never clears a set `result`. -/
theorem execPrim_ttr (s : GameState) (ctrl : PlayerId) (src : ObjId)
    (env : List (VarId × Int)) (p : Prim) :
    (execPrim s ctrl src env p).1.turn = s.turn ∧
    (execPrim s ctrl src env p).1.tournament = s.tournament ∧
    ((execPrim s ctrl src env p).1.result = none → s.result = none) :=
  execPrim_ttr_core s ctrl src env p

/-- Helper: `interpRunStep` preserves `turn` and `tournament`, and never clears a set `result`. -/
theorem interpRunStep_ttr (s : GameState) (ctrl : PlayerId) (src : ObjId)
    (fa : Bool) (env : List (VarId × Int)) (todo : List Effect) (rest : List Frame) :
    (interpRunStep s ctrl src fa env todo rest).1.turn = s.turn ∧
    (interpRunStep s ctrl src fa env todo rest).1.tournament = s.tournament ∧
    ((interpRunStep s ctrl src fa env todo rest).1.result = none → s.result = none) := by
  cases todo with
  | nil => exact ⟨rfl, rfl, id⟩
  | cons eff more =>
    cases eff with
    | nop | seq _ | ifThen _ _ _ | may _ _ | rollDie6 _ _ _ | bindRevealTopCount _ _ _ _ _
    | custom _ _ =>
      exact ⟨rfl, rfl, id⟩
    | grant _ mod dur =>
      unfold interpRunStep applyChainLinkMod
      dsimp only
      cases dur <;> cases s.combat <;>
        first
        | exact ⟨rfl, rfl, id⟩
        | (dsimp only; cases mod <;>
            first | exact ⟨rfl, rfl, id⟩ | (dsimp only; split <;> exact ⟨rfl, rfl, id⟩))
    | chooseOne _ =>
      unfold interpRunStep; dsimp only; split <;> exact ⟨rfl, rfl, id⟩
    | prim p =>
      unfold interpRunStep
      exact execPrim_ttr s ctrl src env p

/-- Helper: `TimeLimitBounded` is preserved whenever `turn` and `tournament` are unchanged and
`s'.result = none → s.result = none`. -/
theorem timeLimitBounded_of_eq {deadline : Nat} {s s' : GameState}
    (hb : TimeLimitBounded deadline s)
    (ht : s'.turn = s.turn) (htourn : s'.tournament = s.tournament)
    (hres : s'.result = none → s.result = none) :
    TimeLimitBounded deadline s' := by
  intro hr'
  obtain ⟨k, hk, hle⟩ := hb (hres hr')
  exact ⟨k, by rw [htourn]; exact hk, by rw [ht]; exact hle⟩

/-- Helper: `gspRun` only ever sets `result` from `none` to `some`, never back to `none`. -/
theorem gspStep_result_none {s s' : GameState} (h : gspStep s = some s') (hr : s'.result = none) :
    s.result = none := by
  unfold gspStep at h
  split at h
  · simp only [Option.some.injEq] at h; subst h
    rename_i hdef
    simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, Option.isSome_iff_ne_none] at hdef
    exact hdef.1
  · cases h1 : nonArenaNonPhys s with
    | cons id _ =>
      rw [h1] at h; simp only [Option.some.injEq] at h; subst h
      rw [← (removeNonPhysObj_turn_tournament_result s id).2.2]; exact hr
    | nil =>
      rw [h1] at h
      cases h2 : gspPermanentsToClear s with
      | nil => rw [h2] at h; cases h
      | cons id _ =>
        rw [h2] at h; dsimp only at h
        cases ho : s.obj? id with
        | none => rw [ho] at h; cases h
        | some o =>
          rw [ho] at h; dsimp only at h
          split at h
          · simp only [Option.some.injEq] at h; subst h
            rw [← (removeNonPhysObj_turn_tournament_result s id).2.2]; exact hr
          · cases hm : moveObj s id (.player o.owner .graveyard) .top false with
            | none => rw [hm] at h; cases h
            | some _ =>
              rw [hm] at h; simp only [Option.some.injEq] at h; subst h
              rw [← (moveObj_turn_tournament_result hm).2.2]; exact hr

/-- Helper: `gspLoop` never clears a set `result`. -/
theorem gspLoop_result_none :
    ∀ (n : Nat) {s : GameState}, (gspLoop n s).result = none → s.result = none
  | 0, _, hr => hr
  | n + 1, s, hr => by
    unfold gspLoop at hr
    cases hs : gspStep s with
    | none => rw [hs] at hr; exact hr
    | some s' =>
      rw [hs] at hr
      exact gspStep_result_none hs (gspLoop_result_none n hr)

/-- Helper: `gspRun` never clears a set `result`. -/
theorem gspRun_result_none {s : GameState} (hr : (gspRun s).result = none) : s.result = none :=
  gspLoop_result_none (gspMeasure s) hr

/-- Helper: `closeCombatChainStep` preserves `turn`, `tournament`, and `result`. -/
theorem closeCombatChainStep_ttr (s : GameState) :
    (closeCombatChainStep s).1.turn = s.turn ∧
    (closeCombatChainStep s).1.tournament = s.tournament ∧
    (closeCombatChainStep s).1.result = s.result := by
  unfold closeCombatChainStep
  exact closeChainList_turn_tournament_result s (s.zone .combatChain)

/-- Helper: `applyPhantasmClose` preserves `turn`, `tournament`, and `result`. -/
theorem applyPhantasmClose_ttr (s : GameState) :
    (applyPhantasmClose s).1.turn = s.turn ∧
    (applyPhantasmClose s).1.tournament = s.tournament ∧
    (applyPhantasmClose s).1.result = s.result := by
  unfold applyPhantasmClose
  cases s.combat.bind CombatChain.activeLink? with
  | none =>
    dsimp only
    exact closeCombatChainStep_ttr s
  | some link =>
    dsimp only
    cases link.attack with
    | none =>
      dsimp only
      exact closeCombatChainStep_ttr s
    | some atkId =>
      dsimp only
      have hd := destroyObjToGraveyard_ttr s atkId
      have hcl := closeCombatChainStep_ttr (destroyObjToGraveyard s atkId).1
      exact ⟨hcl.1.trans hd.1, hcl.2.1.trans hd.2.1, hcl.2.2.trans hd.2.2⟩

/-- Helper: `spendAssetCost` preserves `turn`, `tournament`, and `result`. -/
theorem spendAssetCost_ttr {s s1 : GameState} {p : PlayerId} {cost : AssetCost}
    (h : spendAssetCost s p cost = some s1) :
    s1.turn = s.turn ∧ s1.tournament = s.tournament ∧ s1.result = s.result := by
  unfold spendAssetCost at h
  dsimp only at h
  cases hp : (s.poolOf p).spend cost (cost.resources - (s.poolOf p).resources) with
  | none => rw [hp] at h; cases h
  | some _ => rw [hp] at h; simp only [Option.some.injEq] at h; subst h; exact ⟨rfl, rfl, rfl⟩

/-- Helper: `pitchOne` preserves `turn`, `tournament`, and `result`. -/
theorem pitchOne_ttr {s s1 : GameState} {p : PlayerId} {id id1 : ObjId} {es : List Event}
    (h : pitchOne s p id = some (s1, id1, es)) :
    s1.turn = s.turn ∧ s1.tournament = s.tournament ∧ s1.result = s.result := by
  unfold pitchOne at h
  split at h
  · cases ho : s.obj? id with
    | none => rw [ho] at h; cases h
    | some o =>
      rw [ho] at h; dsimp only at h
      cases hf : s.activeFace? o with
      | none => rw [hf] at h; cases h
      | some face =>
        rw [hf] at h; dsimp only at h
        cases hp : face.pitch with
        | none => rw [hp] at h; cases h
        | some v =>
          rw [hp] at h; dsimp only at h
          cases hm : moveObj s id (.player p .pitch) .top false with
          | none => rw [hm] at h; cases h
          | some res =>
            obtain ⟨sm, idm⟩ := res
            rw [hm] at h; dsimp only at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, -, -⟩ := h
            have hm' := moveObj_turn_tournament_result hm
            exact ⟨hm'.1, hm'.2.1, hm'.2.2⟩
  · cases h

/-- Helper: `rollbackPlay` preserves `turn`, `tournament`, and `result`. -/
theorem rollbackPlay_ttr (s : GameState) (fallback : List Frame) :
    (rollbackPlay s fallback).turn = s.turn ∧
    (rollbackPlay s fallback).tournament = s.tournament ∧
    (rollbackPlay s fallback).result = s.result := by
  unfold rollbackPlay
  cases s.playRollback <;> exact ⟨rfl, rfl, rfl⟩

/-- Helper: `gspRun` followed by updating `pending` preserves `TimeLimitBounded`. -/
theorem timeLimitBounded_gspRun_pending {deadline : Nat} {s s1 : GameState}
    (hb : TimeLimitBounded deadline s)
    (ht : s1.turn = s.turn) (htourn : s1.tournament = s.tournament)
    (hres : s1.result = none → s.result = none) (newPending : List Frame) :
    TimeLimitBounded deadline { gspRun s1 with pending := newPending } := by
  have hg := gspRun_turn_tournament s1
  exact timeLimitBounded_of_eq hb (hg.1.trans ht) (hg.2.trans htourn)
    (fun hr => hres (gspRun_result_none hr))

/-- **I14** (microStep preservation): every `microStep` preserves `TimeLimitBounded deadline`.
In particular, `beginTurn` either terminates in `.draw .timeLimit` (when `k = 0`) or increments
`turn` by 1 while decrementing `timeLimitTurnsLeft` by 1, preserving `turn + k ≤ deadline` (TRP 4). -/
theorem microStep_preserves_timeLimit {deadline : Nat} {s s' : GameState} {es : List Event}
    (hb : TimeLimitBounded deadline s) (h : microStep s = some (s', es)) :
    TimeLimitBounded deadline s' := by
  unfold microStep at h
  split at h
  · -- revealLoadouts
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
    exact timeLimitBounded_of_eq hb rfl rfl id
  · -- openingDraws
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
    exact timeLimitBounded_of_eq hb rfl rfl id
  · -- draw 0
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
    exact timeLimitBounded_of_eq hb rfl rfl id
  · -- draw (n + 1)
    rename_i p _ _ _
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
    have hd := drawOne_turn_tournament_result s p
    exact timeLimitBounded_of_eq hb hd.1 hd.2.1 (fun hr => hd.2.2 ▸ hr)
  · -- beginTurn
    cases htick : s.tournament.tickAtTurnStart with
    | none =>
      rw [htick] at h
      dsimp only at h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
        intro hr; cases hr
      · rename_i hnn
        simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
        intro hr
        exfalso
        rw [hr] at hnn
        exact hnn rfl
    | some ts' =>
      rw [htick] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
      intro hr
      obtain ⟨k, hk, hle⟩ := hb hr
      unfold TournamentState.tickAtTurnStart at htick
      rw [hk] at htick
      cases k with
      | zero => cases htick
      | succ k' =>
        simp only [Option.some.injEq] at htick
        subst htick
        exact ⟨k', rfl, by dsimp only; omega⟩
  · -- startPhaseWork
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
    exact timeLimitBounded_of_eq hb rfl rfl id
  · -- actionPhaseStart
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
    exact timeLimitBounded_of_eq hb rfl rfl id
  · -- playPayCost
    split at h
    · rename_i s1 hsp
      simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
      have hs1 := spendAssetCost_ttr hsp
      exact timeLimitBounded_of_eq hb hs1.1 hs1.2.1 (fun hr => hs1.2.2 ▸ hr)
    · split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
        exact timeLimitBounded_of_eq hb rfl rfl id
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
        unfold rollbackPlay
        cases s.playRollback <;> exact timeLimitBounded_of_eq hb rfl rfl id
  · -- resolveStack
    split at h
    · split at h <;>
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
        exact timeLimitBounded_of_eq hb rfl rfl id
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
      exact timeLimitBounded_of_eq hb rfl rfl id
  · -- finishResolve
    rename_i layerId rest _
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
    let info := s.layerMeta.getD layerId.n { controller := s.active.getD ⟨0⟩ }
    let s1 := if info.goAgain then
      s.setPool info.controller ((s.poolOf info.controller).addActionPoints 1) else s
    have h1 : s1.turn = s.turn ∧ s1.tournament = s.tournament ∧ s1.result = s.result := by
      dsimp only [s1]; split <;> exact ⟨rfl, rfl, rfl⟩
    let isDefReact :=
      match s1.cardDefOf? layerId with
      | some c => c.front.hasType .defenseReaction && s1.combat.isSome
      | none => false
    let p2 :=
      if layerId ∈ s1.zone .stack then
        if isDefReact then
          match moveObj s1 layerId .combatChain .top false with
          | some (sMoved, id') =>
            let cc' := sMoved.combat.map fun cc => cc.updateActiveLink fun l =>
              { l with
                defending := l.defending ++ [id']
                defendedFromHandCount := l.defendedFromHandCount + (if !info.fromArsenal then 1 else 0) }
            ({ sMoved with combat := cc' }, [Event.moved layerId id' .stack .combatChain])
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
              | some (sMoved, id') => (sMoved, [Event.moved layerId id' .stack dst])
              | none => (s1, [])
          | none => (s1, [])
      else (s1, [])
    have h2 : p2.1.turn = s1.turn ∧ p2.1.tournament = s1.tournament ∧ p2.1.result = s1.result := by
      dsimp only [p2]
      split
      · split
        · cases hm : moveObj s1 layerId .combatChain .top false with
          | none => exact ⟨rfl, rfl, rfl⟩
          | some _ =>
            have hm' := moveObj_turn_tournament_result hm
            exact ⟨hm'.1, hm'.2.1, hm'.2.2⟩
        · cases s1.obj? layerId with
          | none => exact ⟨rfl, rfl, rfl⟩
          | some o =>
            dsimp only
            cases o.kind with
            | layer _ _ _ _ => exact removeNonPhysObj_turn_tournament_result s1 layerId
            | card _ _ | token _ | attackProxy _ _ =>
              dsimp only
              cases hm : moveObj s1 layerId _ .top false with
              | none => exact ⟨rfl, rfl, rfl⟩
              | some _ => exact moveObj_turn_tournament_result hm
      · exact ⟨rfl, rfl, rfl⟩
    have hg := gspRun_turn_tournament { p2.1 with layerMeta := p2.1.layerMeta.erase layerId.n }
    exact timeLimitBounded_of_eq hb (hg.1.trans (h2.1.trans h1.1)) (hg.2.trans (h2.2.1.trans h1.2.1))
      (fun hr => by
        have hr1 : ({ p2.1 with layerMeta := p2.1.layerMeta.erase layerId.n }).result = none :=
          gspRun_result_none hr
        exact h1.2.2 ▸ h2.2.2 ▸ hr1)
  · -- combatStep .layer
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
    exact timeLimitBounded_of_eq hb rfl rfl id
  · -- combatStep .attack
    rename_i layerId rest _
    let atk := (s.layerMeta.getD layerId.n { controller := s.active.getD ⟨0⟩ }).controller
    cases hea : enterAttackStep s layerId atk with
    | mk s1 p =>
      cases p with
      | mk atkId es1 =>
        have he := enterAttackStep_turn_tournament_result s layerId atk
        dsimp only at h
        rw [hea] at h he
        dsimp only at h he
        simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
        exact timeLimitBounded_of_eq hb he.1 he.2.1 (fun hr => he.2.2 ▸ hr)
  · -- combatStep .defend
    split at h
    · dsimp only at h
      split at h <;>
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
        exact timeLimitBounded_of_eq hb rfl rfl id
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
      exact timeLimitBounded_of_eq hb rfl rfl id
  · -- combatStep .reaction
    dsimp only at h
    cases hact : s.combat.bind CombatChain.activeLink? with
    | none =>
      rw [hact] at h; dsimp only at h
      simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact timeLimitBounded_of_eq hb rfl rfl id
    | some _ =>
      rw [hact] at h; dsimp only at h
      split at h
      · have hph_ttr := applyPhantasmClose_ttr s
        simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
        exact timeLimitBounded_gspRun_pending hb hph_ttr.1 hph_ttr.2.1 (fun hr => hph_ttr.2.2 ▸ hr) _
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
        exact timeLimitBounded_of_eq hb rfl rfl id
  · -- combatStep .damage
    dsimp only at h
    cases hcc : s.combat with
    | none =>
      rw [hcc] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
      exact timeLimitBounded_of_eq hb rfl rfl id
    | some cc =>
      rw [hcc] at h; dsimp only at h
      cases hl : cc.activeLink? with
      | none =>
        rw [hl] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
        exact timeLimitBounded_of_eq hb rfl rfl id
      | some link =>
        rw [hl] at h; dsimp only at h
        have hd_ttr := applyDamageWithPrevention_ttr s link.defender .physical
          (linkDamageBeforePrevention s link)
        cases hd : applyDamageWithPrevention s link.defender .physical
            (linkDamageBeforePrevention s link) with
        | mk s2 es2 =>
          rw [hd] at h hd_ttr; dsimp only at h hd_ttr
          simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
          refine timeLimitBounded_gspRun_pending hb ?_ ?_ ?_ _
          · exact hd_ttr.1
          · exact hd_ttr.2.1
          · exact hd_ttr.2.2
  · -- combatStep .resolution
    dsimp only at h
    split at h
    · split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
        split <;> exact timeLimitBounded_of_eq hb rfl rfl id
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
        exact timeLimitBounded_of_eq hb rfl rfl id
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
      exact timeLimitBounded_of_eq hb rfl rfl id
  · -- combatStep .close
    cases hcc : closeCombatChainStep s with
    | mk s1 es1 =>
      have hc1 : s1.turn = s.turn ∧ s1.tournament = s.tournament ∧ s1.result = s.result := by
        unfold closeCombatChainStep at hcc
        have hcl := closeChainList_turn_tournament_result s (s.zone .combatChain)
        simp only [Prod.mk.injEq] at hcc
        obtain ⟨rfl, -⟩ := hcc
        exact hcl
      rw [hcc] at h; dsimp only at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
      have hg := gspRun_turn_tournament s1
      exact timeLimitBounded_of_eq hb (hg.1.trans hc1.1) (hg.2.trans hc1.2.1)
        (fun hr => hc1.2.2 ▸ gspRun_result_none hr)
  · -- gameStateProcess
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
    have hg := gspRun_turn_tournament s
    exact timeLimitBounded_of_eq hb hg.1 hg.2 (fun hr => gspRun_result_none hr)
  · -- run
    rename_i ctrl src fa env todo rest _
    simp only [Option.some.injEq] at h
    have hs' : s' = (interpRunStep s ctrl src fa env todo rest).1 := congrArg Prod.fst h.symm
    subst hs'
    have hi := interpRunStep_ttr s ctrl src fa env todo rest
    exact timeLimitBounded_of_eq hb hi.1 hi.2.1 hi.2.2
  · -- optStep 0
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
    exact timeLimitBounded_of_eq hb rfl rfl id
  · -- optStep (n + 1)
    split at h <;>
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
      exact timeLimitBounded_of_eq hb rfl rfl id
  · -- endPhaseStart
    rename_i tp rest _
    have hbd := applyBloodDebt_ttr s tp
    cases hba : applyBloodDebt s tp with
    | mk sBd esBd =>
      rw [hba] at h hbd
      dsimp only at h hbd
      simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
      split <;> exact timeLimitBounded_of_eq hb hbd.1 hbd.2.1 hbd.2.2
  · -- returnPitch
    split at h <;>
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
      exact timeLimitBounded_of_eq hb rfl rfl id
  · -- endTurnCleanup
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
    exact timeLimitBounded_of_eq hb rfl rfl id
  · -- flushTriggers
    split at h <;>
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
      exact timeLimitBounded_of_eq hb rfl rfl id
  · cases h

/-- **I14** (`advance` preservation): `advance` preserves `TimeLimitBounded deadline`. -/
theorem advance_preserves_timeLimit {deadline : Nat} :
    ∀ (n : Nat) {s s' : GameState} {es es' : List Event},
      TimeLimitBounded deadline s → advance n s es = .ok (s', es') → TimeLimitBounded deadline s'
  | 0, s, s', es, es', hb, h => by
    unfold advance at h
    split at h
    · split at h
      · cases h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; exact hb
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; exact hb
  | n + 1, s, s', es, es', hb, h => by
    unfold advance at h
    split at h
    · split at h
      · cases hm : microStep s with
        | none => rw [hm] at h; cases h
        | some res =>
          obtain ⟨s1, es1⟩ := res
          rw [hm] at h
          exact advance_preserves_timeLimit n (microStep_preserves_timeLimit hb hm) h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; exact hb
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; exact hb

/-- Helper: `applyFrame` preserves `turn`, `tournament`, and `result`. -/
theorem applyFrame_turn_tournament_result {s s' : GameState} {a : Action} {es : List Event}
    (h : applyFrame s a = some (s', es)) :
    s'.turn = s.turn ∧ s'.tournament = s.tournament ∧ s'.result = s.result := by
  unfold applyFrame at h
  split at h
  · -- chanceFirstPlayer
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; exact ⟨rfl, rfl, rfl⟩
  · -- chooseFirstPlayer
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; exact ⟨rfl, rfl, rfl⟩
    · cases h
  · -- chooseLoadout loadoutEquip
    split at h
    · split at h
      · cases h
      · split at h
        · cases h
        · rename_i hm
          simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
          have hm' := moveObj_turn_tournament_result hm
          exact ⟨hm'.1, hm'.2.1, hm'.2.2⟩
    · cases h
  · -- chooseLoadout loadoutToDeck
    split at h
    · split at h
      · cases h
      · rename_i hm
        simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
        have hm' := moveObj_turn_tournament_result hm
        exact ⟨hm'.1, hm'.2.1, hm'.2.2⟩
    · cases h
  · -- chooseLoadout loadoutDone
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; exact ⟨rfl, rfl, rfl⟩
    · cases h
  · -- chanceShuffle
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; exact ⟨rfl, rfl, rfl⟩
  · -- priority pass
    split at h
    · dsimp only at h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; exact ⟨rfl, rfl, rfl⟩
      · split at h <;>
        · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; exact ⟨rfl, rfl, rfl⟩
    · cases h
  · -- priority playCard
    split at h
    · dsimp only at h
      split at h
      · cases h
      · rename_i _ _ hm
        simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
        have hm' := moveObj_turn_tournament_result hm
        exact ⟨hm'.1, hm'.2.1, hm'.2.2⟩
    · cases h
  · -- priority attackWeapon
    split at h
    · dsimp only at h
      split at h
      · cases h
      · rename_i _ _ ha
        simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
        have ha' := addObject_turn_tournament_result ha
        exact ⟨ha'.1, ha'.2.1, ha'.2.2⟩
    · cases h
  · -- defendPick defendCard
    split at h
    · split at h
      · dsimp only at h
        split at h
        · rename_i _ _ _ _ hm
          simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
          have hm' := moveObj_turn_tournament_result hm
          exact ⟨hm'.1, hm'.2.1, hm'.2.2⟩
        · cases h
      · cases h
    · cases h
  · -- defendPick defendDone
    split at h
    · dsimp only at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; exact ⟨rfl, rfl, rfl⟩
    · cases h
  · -- chooseMode pickMode
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; exact ⟨rfl, rfl, rfl⟩
    · cases h
  · -- chooseMode cancelPlay
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
      unfold rollbackPlay; cases s.playRollback <;> exact ⟨rfl, rfl, rfl⟩
    · cases h
  · -- choosePitch pitchCard
    split at h
    · split at h
      · cases h
      · rename_i _ _ _ hpitch
        simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
        have hp' := pitchOne_ttr hpitch
        exact ⟨hp'.1, hp'.2.1, hp'.2.2⟩
    · cases h
  · -- choosePitch cancelPlay
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
      unfold rollbackPlay; cases s.playRollback <;> exact ⟨rfl, rfl, rfl⟩
    · cases h
  · -- chooseMay pickMay
    split at h
    · split at h <;>
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; exact ⟨rfl, rfl, rfl⟩
    · cases h
  · -- chooseModal pickMode
    split at h
    · dsimp only at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; exact ⟨rfl, rfl, rfl⟩
    · cases h
  · -- chanceDie6 die6Roll
    split at h
    · dsimp only at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; exact ⟨rfl, rfl, rfl⟩
    · cases h
  · -- chooseHandToDeck handToDeckPick
    split at h
    · dsimp only at h
      split at h
      · cases h
      · rename_i hm
        simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
        have hm' := moveObj_turn_tournament_result hm
        exact ⟨hm'.1, hm'.2.1, hm'.2.2⟩
    · cases h
  · -- chooseOpt optPick
    split at h
    · split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; exact ⟨rfl, rfl, rfl⟩
      · dsimp only at h
        split at h <;>
        · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; exact ⟨rfl, rfl, rfl⟩
    · cases h
  · -- chooseArsenal arsenalPut
    split at h
    · split at h
      · cases h
      · rename_i hm
        simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
        have hm' := moveObj_turn_tournament_result hm
        exact ⟨hm'.1, hm'.2.1, hm'.2.2⟩
    · cases h
  · -- chooseArsenal arsenalSkip
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; exact ⟨rfl, rfl, rfl⟩
    · cases h
  · -- choosePitchOrder pitchReturnPick
    split at h
    · split at h
      · cases h
      · rename_i hm
        simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
        have hm' := moveObj_turn_tournament_result hm
        exact ⟨hm'.1, hm'.2.1, hm'.2.2⟩
    · cases h
  · -- chooseTriggerStart
    split at h
    · dsimp only at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; exact ⟨rfl, rfl, rfl⟩
    · cases h
  · -- chooseTriggerOrder
    split at h
    · split at h
      · cases h
      · dsimp only at h
        split at h
        · cases h
        · rename_i _ _ ha
          simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
          have ha' := addObject_turn_tournament_result ha
          exact ⟨ha'.1, ha'.2.1, ha'.2.2⟩
    · cases h
  · -- chooseReplacement
    dsimp only at h
    split at h <;>
    · split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h; exact ⟨rfl, rfl, rfl⟩
      · cases h
  · cases h

/-- Helper: none of the tournament `ActionKind`s ever satisfies `LegalFrame`. -/
theorem legalFrame_not_tournament {s : GameState} {actor : Actor} {kind : ActionKind}
    (hk : kind = .timeExpired ∨ kind = .offerDraw ∨ kind = .acceptDraw ∨
          kind = .declineDraw ∨ kind = .judgeLoopDraw) :
    ¬ LegalFrame s ⟨actor, kind⟩ := by
  intro hlf
  unfold LegalFrame at hlf
  rcases hk with rfl | rfl | rfl | rfl | rfl <;>
    (cases hp : s.pending with
     | nil => rw [hp] at hlf; exact hlf
     | cons f _ => rw [hp] at hlf; cases f <;> cases actor <;> exact hlf)

/-- **I14** (`step` preservation): every legal `step` preserves `TimeLimitBounded deadline`.
Crucially, `timeExpired` cannot fire a second time because `LegalTournament` requires
`timeLimitTurnsLeft = none` (TRP 4). -/
theorem step_preserves_timeLimit {deadline fuel : Nat} {s s' : GameState} {a : Action}
    {es : List Event}
    (hb : TimeLimitBounded deadline s) (h : step fuel s a = .ok (s', es)) :
    TimeLimitBounded deadline s' := by
  unfold step at h
  split at h
  · rename_i hleg
    cases ha : applyAction s a with
    | none => rw [ha] at h; cases h
    | some res =>
      obtain ⟨s1, es1⟩ := res
      rw [ha] at h
      have hb1 : TimeLimitBounded deadline s1 := by
        unfold applyAction at ha
        split at ha
        · -- concede
          simp only [Option.some.injEq, Prod.mk.injEq] at ha; obtain ⟨rfl, -⟩ := ha
          intro hr; cases hr
        · -- timeExpired: impossible since timeLimitTurnsLeft is already `some k`
          rename_i hact hkind
          obtain ⟨k, hk, _⟩ := hb hleg.1
          rcases hleg.2 with hlf | hlc | hlt
          · have ha_eq : a = ⟨.clock, .timeExpired⟩ := by cases a; simp_all
            rw [ha_eq] at hlf
            exact False.elim (legalFrame_not_tournament (Or.inl rfl) hlf)
          · unfold LegalConcede at hlc; simp [hact, hkind] at hlc
          · unfold LegalTournament at hlt
            simp [hact, hkind] at hlt
            rw [hk] at hlt
            cases hlt.2
        · -- judgeLoopDraw
          simp only [Option.some.injEq, Prod.mk.injEq] at ha; obtain ⟨rfl, -⟩ := ha
          intro hr; cases hr
        · -- offerDraw
          simp only [Option.some.injEq, Prod.mk.injEq] at ha; obtain ⟨rfl, -⟩ := ha
          intro hr
          obtain ⟨k, hk, hle⟩ := hb hr
          exact ⟨k, hk, hle⟩
        · -- acceptDraw
          simp only [Option.some.injEq, Prod.mk.injEq] at ha; obtain ⟨rfl, -⟩ := ha
          intro hr; cases hr
        · -- declineDraw
          simp only [Option.some.injEq, Prod.mk.injEq] at ha; obtain ⟨rfl, -⟩ := ha
          intro hr
          obtain ⟨k, hk, hle⟩ := hb hr
          exact ⟨k, hk, hle⟩
        · -- applyFrame
          have hf := applyFrame_turn_tournament_result ha
          exact timeLimitBounded_of_eq hb hf.1 hf.2.1 (fun hr => hf.2.2 ▸ hr)
      exact advance_preserves_timeLimit fuel hb1 h
  · cases h

/-- Multi-step reachability relation starting from an arbitrary state `s0`. -/
inductive ReachableFrom (s0 : GameState) : GameState → Prop where
  /-- Zero steps from `s0`. -/
  | refl : ReachableFrom s0 s0
  /-- One additional successful `step`. -/
  | step {s s' : GameState} {fuel : Nat} {a : Action} {es : List Event} :
      ReachableFrom s0 s → Fab.step fuel s a = .ok (s', es) → ReachableFrom s0 s'

/-- **I14** (clock activation): firing `⟨.clock, .timeExpired⟩` on state `s` establishes
`TimeLimitBounded (s.turn + 1)` on the resulting state (TRP 4). -/
theorem timeExpired_sets_bound {fuel : Nat} {s s1 : GameState} {es : List Event}
    (h : step fuel s ⟨.clock, .timeExpired⟩ = .ok (s1, es)) :
    TimeLimitBounded (s.turn + 1) s1 := by
  unfold step at h
  split at h
  · unfold applyAction at h
    dsimp only at h
    have hb0 : TimeLimitBounded (s.turn + 1) (applyTimeExpired s) := by
      intro _
      exact ⟨1, rfl, Nat.le_refl _⟩
    exact advance_preserves_timeLimit fuel hb0 h
  · cases h

/-- **I14** (at most 2 turns after time limit — current turn + 1 additional turn):
after `Actor.clock` signals `timeExpired` at turn `T = s.turn`, EVERY subsequent ongoing state
`s'` reachable by any sequence of `step`s satisfies `s'.turn ≤ T + 1` (the game can never enter
turn `T + 2` undecided) (TRP 4). -/
theorem timeLimit_at_most_two_turns {fuel : Nat} {s s1 s' : GameState} {es : List Event}
    (hclk : step fuel s ⟨.clock, .timeExpired⟩ = .ok (s1, es))
    (hreach : ReachableFrom s1 s')
    (hongoing : s'.result = none) :
    s'.turn ≤ s.turn + 1 := by
  have hb1 : TimeLimitBounded (s.turn + 1) s1 := timeExpired_sets_bound hclk
  have hb' : TimeLimitBounded (s.turn + 1) s' := by
    clear hongoing
    induction hreach with
    | refl => exact hb1
    | step _ hstep ih => exact step_preserves_timeLimit ih hstep
  obtain ⟨k, _, hle⟩ := hb' hongoing
  omega

/-- **I14** (exact termination at end of additional turn): when `timeLimitTurnsLeft = some 0`
(the additional turn has just ended) and the game is still undecided, `microStep` on `.beginTurn`
immediately terminates the game with `GameResult.draw .timeLimit` (TRP 4). -/
theorem beginTurn_zero_ends_timeLimit {s : GameState} {rest : List Frame}
    (hp : s.pending = .beginTurn :: rest)
    (hzero : s.tournament.timeLimitTurnsLeft = some 0)
    (hres : s.result = none) :
    microStep s = some ({ s with result := some (.draw .timeLimit), pending := [], playRollback := none }, []) := by
  unfold microStep
  rw [hp]
  dsimp only
  rw [TournamentState.tickAtTurnStart_zero s.tournament hzero]
  simp [hres]

/-- **Top Cut Intentional Draw Prohibition**: under `RuleSet.tournament .topCut`, none of
`offerDraw`, `acceptDraw`, or `declineDraw` is `Legal` for any actor (TRP 4). -/
theorem topCut_forbids_intentional_draw {s : GameState}
    (htc : s.config.ruleSet = .tournament .topCut) (actor : Actor) :
    ¬ Legal s ⟨actor, .offerDraw⟩ ∧
    ¬ Legal s ⟨actor, .acceptDraw⟩ ∧
    ¬ Legal s ⟨actor, .declineDraw⟩ := by
  have hno : s.config.ruleSet.allowsIntentionalDraw = false := by
    rw [htc]; rfl
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, hlf | hlc | hlt⟩
    · exact legalFrame_not_tournament (Or.inr (Or.inl rfl)) hlf
    · unfold LegalConcede at hlc; cases actor <;> simp at hlc
    · unfold LegalTournament at hlt; cases actor <;> simp [hno] at hlt
  · rintro ⟨_, hlf | hlc | hlt⟩
    · exact legalFrame_not_tournament (Or.inr (Or.inr (Or.inl rfl))) hlf
    · unfold LegalConcede at hlc; cases actor <;> simp at hlc
    · unfold LegalTournament at hlt; cases actor <;> simp [hno] at hlt
  · rintro ⟨_, hlf | hlc | hlt⟩
    · exact legalFrame_not_tournament (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hlf
    · unfold LegalConcede at hlc; cases actor <;> simp at hlc
    · unfold LegalTournament at hlt; cases actor <;> simp [hno] at hlt

/-- **Top Cut Intentional Draw Enumeration**: under `RuleSet.tournament .topCut`, `legalActions s`
never contains `offerDraw`, `acceptDraw`, or `declineDraw` (TRP 4). -/
theorem topCut_legalActions_no_draw {s : GameState}
    (htc : s.config.ruleSet = .tournament .topCut) (p : PlayerId) :
    ⟨.player p, .offerDraw⟩ ∉ legalActions s ∧
    ⟨.player p, .acceptDraw⟩ ∉ legalActions s ∧
    ⟨.player p, .declineDraw⟩ ∉ legalActions s := by
  obtain ⟨h1, h2, h3⟩ := topCut_forbids_intentional_draw htc (.player p)
  refine ⟨?_, ?_, ?_⟩
  · intro h; exact h1 (legalActions_iff s _ |>.mp h).1
  · intro h; exact h2 (legalActions_iff s _ |>.mp h).1
  · intro h; exact h3 (legalActions_iff s _ |>.mp h).1

/-- In Swiss 1v1, the player who offered an Intentional Draw cannot accept their own offer (TRP 4). -/
theorem swiss_self_accept_forbidden {s : GameState} {p : PlayerId}
    (hoff : s.tournament.idOffer = some p) :
    ¬ Legal s ⟨.player p, .acceptDraw⟩ := by
  rintro ⟨_, hlf | hlc | hlt⟩
  · exact legalFrame_not_tournament (Or.inr (Or.inr (Or.inl rfl))) hlf
  · unfold LegalConcede at hlc; simp at hlc
  · unfold LegalTournament at hlt
    simp [hoff] at hlt

/-- In Swiss 1v1, once `p` offers an Intentional Draw and opponent `q ≠ p` accepts, the game ends
immediately with `result = some (.draw .agreed)` (TRP 4). -/
theorem swiss_accept_draw_ends_game {fuel : Nat} {s : GameState} {p q : PlayerId}
    (hres : s.result = none)
    (h2 : s.playerCount = 2)
    (hq : q.n < 2)
    (hsw : s.config.ruleSet = .tournament .swiss)
    (hoff : s.tournament.idOffer = some p)
    (hne : p ≠ q) :
    step fuel s ⟨.player q, .acceptDraw⟩ = .ok (applyAcceptDraw s, []) ∧
    (applyAcceptDraw s).result = some (.draw .agreed) := by
  have hleg : Legal s ⟨.player q, .acceptDraw⟩ := by
    refine ⟨hres, Or.inr (Or.inr ?_)⟩
    unfold LegalTournament
    simp [h2, hq, hsw, RuleSet.allowsIntentionalDraw, hoff, hne]
  constructor
  · unfold step
    simp only [hleg, ↓reduceIte, applyAction]
    cases fuel <;> simp [advance, applyAcceptDraw]
  · rfl

/-- `Actor.clock` time-expired signal is forbidden in Top Cut and Core-only games (TRP 4). -/
theorem nonSwiss_forbids_timeExpired {s : GameState}
    (hno : s.config.ruleSet.hasTimeLimit = false) :
    ¬ Legal s ⟨.clock, .timeExpired⟩ := by
  rintro ⟨_, hlf | hlc | hlt⟩
  · exact legalFrame_not_tournament (Or.inl rfl) hlf
  · unfold LegalConcede at hlc; simp at hlc
  · unfold LegalTournament at hlt; simp [hno] at hlt

/-- `Actor.clock` cannot fire `timeExpired` a second time once a countdown is active (TRP 4). -/
theorem clock_second_timeExpired_forbidden {s : GameState} {k : Nat}
    (hact : s.tournament.timeLimitTurnsLeft = some k) :
    ¬ Legal s ⟨.clock, .timeExpired⟩ := by
  rintro ⟨_, hlf | hlc | hlt⟩
  · exact legalFrame_not_tournament (Or.inl rfl) hlf
  · unfold LegalConcede at hlc; simp at hlc
  · unfold LegalTournament at hlt; simp [hact] at hlt

/-- `Actor.judge` loop draw is legal iff the game is ongoing under a tournament ruleset (TRP 4). -/
theorem judgeLoopDraw_legal_iff (s : GameState) :
    Legal s ⟨.judge, .judgeLoopDraw⟩ ↔
      s.result = none ∧ s.config.ruleSet.isTournament = true := by
  unfold Legal
  constructor
  · rintro ⟨hres, hlf | hlc | hlt⟩
    · exact False.elim (legalFrame_not_tournament (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) hlf)
    · unfold LegalConcede at hlc; simp at hlc
    · exact ⟨hres, hlt⟩
  · rintro ⟨hres, ht⟩
    exact ⟨hres, Or.inr (Or.inr ht)⟩

/-- `Actor.judge` loop draw immediately ends any ongoing tournament game in `.draw .loop` (TRP 4). -/
theorem judgeLoopDraw_ends_in_loop_draw {fuel : Nat} {s : GameState}
    (hres : s.result = none) (ht : s.config.ruleSet.isTournament = true) :
    step fuel s ⟨.judge, .judgeLoopDraw⟩ = .ok (applyJudgeLoopDraw s, []) ∧
    (applyJudgeLoopDraw s).result = some (.draw .loop) := by
  have hleg : Legal s ⟨.judge, .judgeLoopDraw⟩ :=
    (judgeLoopDraw_legal_iff s).mpr ⟨hres, ht⟩
  constructor
  · unfold step
    simp only [hleg, ↓reduceIte, applyAction]
    cases fuel <;> simp [advance, applyJudgeLoopDraw]
  · rfl

/-- In a `coreOnly` game, `Actor.judge` cannot invoke `judgeLoopDraw` (TRP 4). -/
theorem coreOnly_forbids_judgeLoopDraw {s : GameState} (h : s.config.ruleSet = .coreOnly) :
    ¬ Legal s ⟨.judge, .judgeLoopDraw⟩ := by
  rw [judgeLoopDraw_legal_iff, h]
  simp [RuleSet.isTournament]

end Fab

end
