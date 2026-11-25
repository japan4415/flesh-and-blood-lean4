module

public import Fab.Invariant.Step

/-!
# Stack, priority, rollback, and interpreter invariants (M4)

Proves M4 theorems from `docs/roadmap.md`:
- **I9** (Stack LIFO, priority retention, automatic end-phase resolution):
  `playCard_pushes_stack_top`, `playPayCost_retains_priority`, `resolveStack_lifo`,
  `finishResolve_continues_stack`
- **I16** (Priority passing): `priority_pass_rotates`, `priority_all_passed_resolves_stack`,
  `priority_all_passed_ends_action_phase`
- **I18** (Mandatory prompt on optional choices): `run_may_prompts`
- **No Over-Pitching**: `playPayCost_no_pitch_when_canPay`
- **Play rollback exactness**: `cancelPlay_restores_exact`, `playPayCost_unpayable_restores_exact`
- **I5** (Progress on M4 decision frames): `progress_m4_decisions`
-/

@[expose] public section

namespace Fab

/-- **I16** (priority rotation): passing priority when fewer than `turnOrder.length` players have
passed rotates priority to the next player clockwise and increments `passCount` (CR 1.11). -/
theorem priority_pass_rotates {s : GameState} {p : PlayerId} {passCount : Nat} {rest : List Frame}
    (hp : s.pending = .priority p passCount :: rest)
    (hlt : passCount + 1 < s.turnOrder.length) :
    applyFrame s ⟨.player p, .pass⟩ =
      some ({ s with pending := .priority (nextInOrder s.turnOrder p) (passCount + 1) :: rest }, []) := by
  unfold applyFrame
  rw [hp]
  simp [hlt]

/-- **I16** (all-pass resolves stack): when all players pass consecutively and the stack is
non-empty, `resolveStack` is scheduled to resolve the top layer (CR 1.11, 5.3). -/
theorem priority_all_passed_resolves_stack {s : GameState} {p : PlayerId} {passCount : Nat}
    {rest : List Frame} {topId : ObjId} {below : List ObjId}
    (hp : s.pending = .priority p passCount :: rest)
    (hge : ¬ (passCount + 1 < s.turnOrder.length))
    (hstack : s.zone .stack = topId :: below) :
    applyFrame s ⟨.player p, .pass⟩ =
      some ({ s with pending := .resolveStack :: rest }, []) := by
  unfold applyFrame
  rw [hp]
  simp [hge, hstack]

/-- **I16** (all-pass ends Action Phase): when all players pass consecutively and the stack is
empty, priority pops and control advances to `rest` (End Phase) (CR 4.3.3). -/
theorem priority_all_passed_ends_action_phase {s : GameState} {p : PlayerId} {passCount : Nat}
    {rest : List Frame}
    (hp : s.pending = .priority p passCount :: rest)
    (hge : ¬ (passCount + 1 < s.turnOrder.length))
    (hemp : s.zone .stack = []) :
    applyFrame s ⟨.player p, .pass⟩ =
      some ({ s with pending := rest }, []) := by
  unfold applyFrame
  rw [hp]
  simp [hge, hemp]

/-- **I9** (Stack LIFO push): playing a card moves it to the top (head) of `Zone.stack`
(CR 5.1.1b). -/
theorem playCard_pushes_stack_top {s s1 sOut : GameState} {p : PlayerId} {passCount : Nat}
    {rest : List Frame} {id layerId : ObjId} {es : List Event}
    (hp : s.pending = .priority p passCount :: rest)
    (hcan : canPlayCard s p id = true)
    (hm : moveObj s id .stack .top false = some (s1, layerId))
    (happ : applyFrame s ⟨.player p, .playCard id⟩ = some (sOut, es)) :
    sOut.zone .stack = layerId :: s.zone .stack := by
  unfold applyFrame at happ
  rw [hp] at happ
  dsimp only at happ
  simp only [hcan, and_self, ↓reduceIte, hm, Option.some.injEq, Prod.mk.injEq] at happ
  obtain ⟨rfl, _⟩ := happ
  change s1.zone .stack = layerId :: s.zone .stack
  unfold moveObj at hm
  split at hm
  · rename_i src o hloc ho
    dsimp only at hm
    split at hm
    · cases hm
    · split at hm <;>
      · simp only [Option.some.injEq, Prod.mk.injEq] at hm
        obtain ⟨rfl, rfl⟩ := hm
        simp [GameState.zone, GameState.setZone, Pos.insert, Zone.normalize]
  · cases hm

/-- **I9** (priority retention & no over-pitching): when `p`'s pool can already pay `cost`
and the layer has neither a chosen hand-card cost nor a random-discard cost,
`playPayCost` spends the cost immediately without prompting `choosePitch`, clears `playRollback`,
and retains priority for `p` with `passCount = 0` after any on-play triggers are stacked
(CR 1.14.3b, 5.1.1i, 6.6.6). -/
theorem playPayCost_retains_priority {s : GameState} {p : PlayerId} {layerId : ObjId}
    {fromArsenal : Bool} {modeIdx : Option Nat} {cost : AssetCost} {rest : List Frame}
    (hp : s.pending = .playPayCost p layerId fromArsenal modeIdx cost :: rest)
    (hpay : (s.poolOf p).canPay cost) (hhand : cardPlayHandCost? s layerId = none)
    (hdiscard : cardPlayRandomDiscardCost s layerId = 0) :
    ∃ s' es, microStep s = some (s', es) ∧
      (s'.pending = .priority p 0 :: rest ∨ s'.pending = .flushTriggers :: .priority p 0 :: rest) ∧
      s'.playRollback = none ∧
      (s'.poolOf p).actionPoints + cost.actionPoints = (s.poolOf p).actionPoints ∧
      (s'.poolOf p).totalEnergy + (cost.resources + cost.chi) = (s.poolOf p).totalEnergy := by
  have hsp : ∃ pool', (s.poolOf p).spend cost (cost.resources - (s.poolOf p).resources) = some pool' := by
    unfold AssetPool.canPay at hpay
    refine ⟨{ actionPoints := (s.poolOf p).actionPoints - cost.actionPoints
              resources := (s.poolOf p).resources - (cost.resources - (cost.resources - (s.poolOf p).resources))
              chi := (s.poolOf p).chi - (cost.chi + (cost.resources - (s.poolOf p).resources)) }, ?_⟩
    unfold AssetPool.spend
    dsimp only
    have hcond : cost.actionPoints ≤ (s.poolOf p).actionPoints ∧
        cost.resources - (s.poolOf p).resources ≤ cost.resources ∧
        cost.chi + (cost.resources - (s.poolOf p).resources) ≤ (s.poolOf p).chi ∧
        cost.resources - (cost.resources - (s.poolOf p).resources) ≤ (s.poolOf p).resources := by
      omega
    simp only [hcond, and_self, ite_true]
  obtain ⟨pool', hpool'⟩ := hsp
  have hacc := AssetPool.spend_accounting hpool'
  have hspend : spendAssetCost s p cost = some (s.setPool p pool') := by
    unfold spendAssetCost
    dsimp only
    rw [hpool']
  unfold microStep
  rw [hp]
  dsimp only
  rw [hspend]
  simp only [hhand, hdiscard, ↓reduceIte]
  refine ⟨_, [], rfl, ?_, rfl, ?_, ?_⟩
  · unfold finishPaidPlay
    dsimp only
    split <;> split <;> first | exact Or.inl rfl | exact Or.inr rfl
  · change ((s.setPool p pool').poolOf p).actionPoints + cost.actionPoints = _
    rw [GameState.poolOf_setPool_self]
    exact hacc.1
  · change ((s.setPool p pool').poolOf p).totalEnergy + (cost.resources + cost.chi) = _
    rw [GameState.poolOf_setPool_self]
    exact hacc.2

/-- **I9** (Stack LIFO resolution): `resolveStack` resolves a non-attack head layer `topId` of
`s.zone .stack` before any layer beneath it (CR 5.3). -/
theorem resolveStack_lifo {s : GameState} {topId : ObjId} {below : List ObjId}
    {rest : List Frame}
    (hp : s.pending = .resolveStack :: rest)
    (hstack : s.zone .stack = topId :: below)
    (hna : isAttackLayer s topId = false) :
    ∃ ctrl fa eff,
      microStep s = some ({ s with
        pending := .run ctrl (resolvingSource s topId) fa [] [eff] :: .finishResolve topId :: rest }, []) := by
  unfold microStep
  rw [hp]
  dsimp only
  rw [hstack]
  simp only [hna, Bool.false_eq_true, ↓reduceIte]
  exact ⟨_, _, _, rfl⟩

/-- **I9**: after a layer resolves, end-phase layers resolve automatically. Otherwise the
turn-player regains priority with `passCount = 0` (CR 4.4.2, 5.3.5). -/
theorem finishResolve_continues_stack {s s' : GameState} {layerId : ObjId} {rest : List Frame}
    {es : List Event}
    (hp : s.pending = .finishResolve layerId :: rest)
    (hm : microStep s = some (s', es)) :
    s'.pending = (if s'.phase = .endPhase then .resolveStack else
      .priority (s'.active.getD ⟨0⟩) 0) :: rest := by
  unfold microStep at hm
  rw [hp] at hm
  simp only [Option.some.injEq, Prod.mk.injEq] at hm
  obtain ⟨rfl, -⟩ := hm
  rfl

/-- **I18** (mandatory prompt for optional choices): `microStep` on `Frame.run` with head
`Effect.may` always prompts `Frame.chooseMay` rather than deciding silently. -/
theorem run_may_prompts {s : GameState} {ctrl : PlayerId} {src : ObjId} {fa : Bool}
    {env : List (VarId × Int)} {body ifDone : Effect} {more : List Effect} {rest : List Frame}
    (hp : s.pending = .run ctrl src fa env (.may body ifDone :: more) :: rest) :
    microStep s = some ({ s with
      pending := .chooseMay ctrl src fa env body ifDone ::
        .run ctrl src fa env more :: rest }, []) := by
  unfold microStep
  rw [hp]
  rfl

/-- **Play Rollback Exactness**: cancelling a card play during `choosePitch` when `playRollback`
holds `s0.snapshot` restores the exact pre-play board state `s0` (provided fixed metadata matches
and `s0.playRollback = none`) (CR 5.1.1). -/
theorem cancelPlay_restores_exact {s0 s : GameState} {p : PlayerId} {layerId : ObjId}
    {fromArsenal : Bool} {modeIdx : Option Nat} {cost : AssetCost} {rest : List Frame}
    (hp : s.pending = .choosePitch p layerId fromArsenal modeIdx cost :: rest)
    (hrb : s.playRollback = some s0.snapshot)
    (h0rb : s0.playRollback = none)
    (hcfg : s.config = s0.config) (hcards : s.cards = s0.cards)
    (hturn : s.turn = s0.turn) (hact : s.active = s0.active)
    (hord : s.turnOrder = s0.turnOrder) (hph : s.phase = s0.phase)
    (hres : s.result = s0.result) (htourn : s.tournament = s0.tournament) :
    applyFrame s ⟨.player p, .cancelPlay⟩ = some (s0, []) := by
  unfold applyFrame
  rw [hp]
  simp only [↓reduceIte, rollbackPlay, hrb, Option.some.injEq, Prod.mk.injEq, and_true]
  cases s; cases s0
  simp only [GameState.restore, GameState.snapshot] at *
  subst h0rb hcfg hcards hturn hact hord hph hres htourn
  rfl

/-- **Automatic Rollback Exactness**: when `playPayCost` cannot pay and cannot pitch, it rolls back
to the exact pre-play board state `s0` (CR 5.1.1). -/
theorem playPayCost_unpayable_restores_exact {s0 s : GameState} {p : PlayerId} {layerId : ObjId}
    {fromArsenal : Bool} {modeIdx : Option Nat} {cost : AssetCost} {rest : List Frame}
    (hp : s.pending = .playPayCost p layerId fromArsenal modeIdx cost :: rest)
    (hnsp : spendAssetCost s p cost = none)
    (hnpitch : canPitchForCost s p cost = false)
    (hrb : s.playRollback = some s0.snapshot)
    (h0rb : s0.playRollback = none)
    (hcfg : s.config = s0.config) (hcards : s.cards = s0.cards)
    (hturn : s.turn = s0.turn) (hact : s.active = s0.active)
    (hord : s.turnOrder = s0.turnOrder) (hph : s.phase = s0.phase)
    (hres : s.result = s0.result) (htourn : s.tournament = s0.tournament) :
    microStep s = some (s0, []) := by
  unfold microStep
  rw [hp]
  dsimp only
  rw [hnsp, hnpitch]
  simp only [Bool.false_eq_true, ↓reduceIte, rollbackPlay, hrb, Option.some.injEq, Prod.mk.injEq,
    and_true]
  cases s; cases s0
  simp only [GameState.restore, GameState.snapshot] at *
  subst h0rb hcfg hcards hturn hact hord hph hres htourn
  rfl

/-- **I5** (Progress on M4 decision frames): every new M4 decision frame on an ongoing state has a
legal non-concede action (either a player action in `legalActions` or a chance die roll). -/
theorem progress_m4_decisions {s : GameState} (hres : s.result = none) :
    (∀ p lid fa mc cost rest, s.pending = .chooseMode p lid fa mc cost :: rest →
      ∃ a ∈ legalActions s, a.kind ≠ .concede) ∧
    (∀ p lid fa mi cost rest, s.pending = .choosePitch p lid fa mi cost :: rest →
      ∃ a ∈ legalActions s, a.kind ≠ .concede) ∧
    (∀ p lid fa mi cost extra rest,
      s.pending = .chooseOptionalResources p lid fa mi cost extra :: rest →
      ∃ a ∈ legalActions s, a.kind ≠ .concede) ∧
    (∀ p lid fa mi cost rest, s.pending = .chooseHandCardCost p lid fa mi cost :: rest →
      ∃ a ∈ legalActions s, a.kind ≠ .concede) ∧
    (∀ ctrl src fa env b i rest, s.pending = .chooseMay ctrl src fa env b i :: rest →
      ∃ a ∈ legalActions s, a.kind ≠ .concede) ∧
    (∀ ctrl src fa env m ms rest, s.pending = .chooseModal ctrl src fa env (m :: ms) :: rest →
      ∃ a ∈ legalActions s, a.kind ≠ .concede) ∧
    (∀ p pos c cs rest, s.pending = .chooseHandToDeck p pos :: rest →
      s.zone (.player p .hand) = c :: cs →
      ∃ a ∈ legalActions s, a.kind ≠ .concede) ∧
    (∀ p cid rest, s.pending = .chooseOpt p cid :: rest →
      ∃ a ∈ legalActions s, a.kind ≠ .concede) ∧
    (∀ ctrl src fa env bv br ct rest,
      s.pending = .chanceDie6 ctrl src fa env bv br ct :: rest →
      ∃ a, Legal s a ∧ a.actor = .chance) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p lid fa mc cost rest hp
    refine ⟨⟨.player p, .cancelPlay⟩, ?_, by simp⟩
    rw [legalActions_iff]
    exact ⟨⟨hres, Or.inl (by simp [LegalFrame, hp])⟩, rfl⟩
  · intro p lid fa mi cost rest hp
    refine ⟨⟨.player p, .cancelPlay⟩, ?_, by simp⟩
    rw [legalActions_iff]
    exact ⟨⟨hres, Or.inl (by simp [LegalFrame, hp])⟩, rfl⟩
  · intro p lid fa mi cost extra rest hp
    refine ⟨⟨.player p, .pickMay false⟩, ?_, by simp⟩
    rw [legalActions_iff]
    exact ⟨⟨hres, Or.inl (by simp [LegalFrame, hp])⟩, rfl⟩
  · intro p lid fa mi cost rest hp
    refine ⟨⟨.player p, .cancelPlay⟩, ?_, by simp⟩
    rw [legalActions_iff]
    exact ⟨⟨hres, Or.inl (by simp [LegalFrame, hp])⟩, rfl⟩
  · intro ctrl src fa env b i rest hp
    refine ⟨⟨.player ctrl, .pickMay false⟩, ?_, by simp⟩
    rw [legalActions_iff]
    exact ⟨⟨hres, Or.inl (by simp [LegalFrame, hp])⟩, rfl⟩
  · intro ctrl src fa env m ms rest hp
    refine ⟨⟨.player ctrl, .pickMode 0⟩, ?_, by simp⟩
    rw [legalActions_iff]
    exact ⟨⟨hres, Or.inl (by simp [LegalFrame, hp])⟩, rfl⟩
  · intro p pos c cs rest hp hne
    refine ⟨⟨.player p, .handToDeckPick c⟩, ?_, by simp⟩
    rw [legalActions_iff]
    exact ⟨⟨hres, Or.inl (by simp [LegalFrame, hp, hne])⟩, rfl⟩
  · intro p cid rest hp
    refine ⟨⟨.player p, .optPick true⟩, ?_, by simp⟩
    rw [legalActions_iff]
    exact ⟨⟨hres, Or.inl (by simp [LegalFrame, hp])⟩, rfl⟩
  · intro ctrl src fa env bv br ct rest hp
    exact ⟨⟨.chance, .die6Roll 1⟩, ⟨hres, Or.inl (by simp [LegalFrame, hp])⟩, rfl⟩

/-- **I5**: a player declaring a hero target can always cancel the in-progress play. -/
theorem progress_choosePlayHero {s : GameState} (hres : s.result = none)
    {p : PlayerId} {lid : ObjId} {fromArsenal : Bool} {mode : Option Nat} {cost : AssetCost}
    {rest : List Frame} (hp : s.pending = .choosePlayHero p lid fromArsenal mode cost :: rest) :
    ∃ a ∈ legalActions s, a.kind ≠ .concede := by
  refine ⟨⟨.player p, .cancelPlay⟩, ?_, by simp⟩
  rw [legalActions_iff]
  exact ⟨⟨hres, Or.inl (by simp [LegalFrame, hp])⟩, rfl⟩

end Fab

end
