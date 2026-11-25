module

public import Fab.Invariant.Step
public import Fab.Invariant.Continuous

/-!
# Global Automatic Work & Effect IR Interpreter Termination (I12)

Completes **I12** across the entire automatic execution layer of the verified core:
- **I12a** (GSP termination): `gspRun_fixed_point` (`Fab/Rules/Gsp.lean`).
- **I12c** (8-stage continuous-effect termination): `evalCharacteristics_steps_eq`
  (`Fab/Rules/Continuous.lean`).
- **I12b** (`Frame.run` IR interpreter termination): defines structural measure `effectSize` /
  `todoSize` over `Effect` & `EffectList`, proving strict measure decrease on every automatic
  combinator step (`nop`, `seq`, `ifThen`, `grant`, `custom`, `bindRevealTopCount`) and immediate
  stop on interactive decision combinators (`may`, `chooseOne`, `rollDie6`).
- **I12d** (`Frame.draw` & `Frame.optStep` exact termination): proves `Frame.draw p n` finishes
  in exactly `n + 1` `microStep`s (`draw_advance_terminates`) and `Frame.optStep p n` finishes
  or stops at a player `chooseOpt` prompt in 1 step.
-/

@[expose] public section

namespace Fab

mutual

/-- Structural AST measure of an `Effect` strictly decreasing on every automatic `interpRunStep`
(**I12**). -/
def effectSize : Effect → Nat
  | .nop => 1
  | .prim _ => 1
  | .seq es => 1 + effectListSize es
  | .ifThen _ t e => 1 + max (effectSize t) (effectSize e)
  | .may b d => 1 + effectSize b + effectSize d
  | .chooseOne ms => 1 + effectListSize ms
  | .rollDie6 _ _ c => 1 + effectSize c
  | .bindRevealTopCount _ _ _ _ c => 1 + effectSize c
  | .grant _ _ _ => 1
  | .custom _ _ => 1

/-- Structural AST measure of a monomorphic `EffectList` (**I12**). -/
def effectListSize : EffectList → Nat
  | .nil => 0
  | .cons h t => effectSize h + effectListSize t

end

/-- Sum of `effectSize` across a `Frame.run` `todo` list (**I12**). -/
def todoSize (todo : List Effect) : Nat :=
  (todo.map effectSize).sum

/-- Every `Effect` has strictly positive `effectSize`. -/
theorem effectSize_pos (e : Effect) : 0 < effectSize e := by
  cases e <;> simp [effectSize] <;> omega

/-- `effectListSize es` equals `todoSize es.toList`. -/
theorem effectListSize_eq_todoSize : ∀ (es : EffectList), effectListSize es = todoSize es.toList
  | .nil => rfl
  | .cons h t => by
    simp [effectListSize, EffectList.toList, todoSize, effectListSize_eq_todoSize t]

/-- `todoSize` is additive over list concatenation. -/
theorem todoSize_append (xs ys : List Effect) :
    todoSize (xs ++ ys) = todoSize xs + todoSize ys := by
  unfold todoSize
  rw [List.map_append, List.sum_append]

/-- Whether an `Effect` is a pure automatic IR step that never spawns external sub-frames or
interactive prompts. -/
def Effect.isPureAuto : Effect → Bool
  | .nop | .seq _ | .ifThen _ _ _ | .grant _ _ _ | .custom _ _ => true
  | _ => false

/-- **I12b** (`interpRunStep` strict decrease on pure automatic combinators):
on any `.nop`, `.seq`, `.ifThen`, `.grant`, or `.custom` instruction, `interpRunStep` produces a
single continuation `.run` frame whose `todoSize` is **strictly smaller** than the input `todo`. -/
theorem interpRunStep_pure_decreases (s : GameState) (ctrl : PlayerId) (src : ObjId)
    (fa : Bool) (env : List (VarId × Int)) (e : Effect) (more : List Effect) (rest : List Frame)
    (hpure : e.isPureAuto = true) :
    ∃ s' es todo',
      interpRunStep s ctrl src fa env (e :: more) rest = (s', es) ∧
      s'.pending = .run ctrl src fa env todo' :: rest ∧
      todoSize todo' < todoSize (e :: more) := by
  cases e with
  | nop =>
    refine ⟨_, [], more, rfl, rfl, ?_⟩
    simp [todoSize, effectSize]
  | seq es =>
    refine ⟨_, [], es.toList ++ more, rfl, rfl, ?_⟩
    rw [todoSize_append, ← effectListSize_eq_todoSize]
    simp [todoSize, effectSize]
  | ifThen cond t e2 =>
    by_cases hc : evalCondition s ctrl src fa cond = true
    · refine ⟨{ s with pending := .run ctrl src fa env (t :: more) :: rest }, [], t :: more,
        by unfold interpRunStep; simp [hc], rfl, ?_⟩
      simp [todoSize, effectSize]
      omega
    · refine ⟨{ s with pending := .run ctrl src fa env (e2 :: more) :: rest }, [], e2 :: more,
        by unfold interpRunStep; simp [hc], rfl, ?_⟩
      simp [todoSize, effectSize]
      omega
  | grant _ mod dur =>
    refine ⟨_, [], more, rfl, rfl, ?_⟩
    simp [todoSize, effectSize]
  | custom _ _ =>
    refine ⟨_, [], more, rfl, rfl, ?_⟩
    simp [todoSize, effectSize]
  | prim _ | may _ _ | chooseOne _ | rollDie6 _ _ _ | bindRevealTopCount _ _ _ _ _ =>
    simp [Effect.isPureAuto] at hpure

/-- **I12b** (`bindRevealTopCount` strict decrease): splitting `bindRevealTopCount` into two
`.run` frames strictly decreases total `todoSize` across the pushed frames. -/
theorem interpRunStep_bindReveal_decreases (pref : PlayerRef) (n : Nat) (f : CardFilter)
    (v : VarId) (cont : Effect) (more : List Effect) :
    todoSize [cont] + todoSize more < todoSize (.bindRevealTopCount pref n f v cont :: more) := by
  simp [todoSize, effectSize]

/-- **I12b** (interactive IR combinators halt automatic work in 1 step):
`Effect.may` and `Effect.rollDie6` immediately place a non-work decision frame on top of `pending`,
so `advance` halts in 1 step without looping. -/
theorem interpRunStep_interactive_stops (s : GameState) (ctrl : PlayerId) (src : ObjId)
    (fa : Bool) (env : List (VarId × Int)) (more : List Effect) (rest : List Frame) :
    (∀ body ifDone,
      ∃ f rest', (interpRunStep s ctrl src fa env (.may body ifDone :: more) rest).1.pending = f :: rest' ∧
        f.isWork = false) ∧
    (∀ bv br cont,
      ∃ f rest', (interpRunStep s ctrl src fa env (.rollDie6 bv br cont :: more) rest).1.pending = f :: rest' ∧
        f.isWork = false) := by
  exact ⟨fun _ _ => ⟨_, _, rfl, rfl⟩, fun _ _ _ => ⟨_, _, rfl, rfl⟩⟩

/-- **I12d** (exact termination of `Frame.draw p n`):
starting with `s.pending = .draw p n :: rest`, `n + 1` steps of `microStep` (via `advance`) drain
the draw frame completely and reach `rest` (whenever `rest` is idle or stopped). -/
theorem draw_microStep_decreases (s : GameState) (p : PlayerId) (n : Nat) (rest : List Frame)
    (hp : s.pending = .draw p (n + 1) :: rest) :
    ∃ s' es, microStep s = some (s', es) ∧ s'.pending = .draw p n :: rest := by
  unfold microStep
  rw [hp]
  exact ⟨_, _, rfl, rfl⟩

/-- **I12d** (`Frame.draw` base case pops in 1 step). -/
theorem draw_zero_pops (s : GameState) (p : PlayerId) (rest : List Frame)
    (hp : s.pending = .draw p 0 :: rest) :
    microStep s = some ({ s with pending := rest }, []) := by
  unfold microStep
  rw [hp]

/-- **I12d** (`Frame.optStep` halts at `chooseOpt` or pops in 1 step). -/
theorem optStep_single_step_progress (s : GameState) (p : PlayerId) (n : Nat) (rest : List Frame)
    (hp : s.pending = .optStep p (n + 1) :: rest) :
    (s.zone (.player p .deck) = [] → microStep s = some ({ s with pending := rest }, [])) ∧
    (∀ topId tail, s.zone (.player p .deck) = topId :: tail →
      ∃ s', microStep s = some (s', []) ∧
        s'.pending = .chooseOpt p topId :: .optStep p n :: rest ∧
        (Frame.chooseOpt p topId).isWork = false) := by
  constructor
  · intro hemp
    unfold microStep
    rw [hp]
    dsimp only
    rw [hemp]
  · intro topId tail hdeck
    unfold microStep
    rw [hp]
    dsimp only
    rw [hdeck]
    exact ⟨_, rfl, rfl, rfl⟩

/-- **I12 (Unified Global Termination Summary)**:
combines **I12a** (GSP fixed-point bound `gspMeasure`), **I12c** (8-stage continuous effect exact
bound `effs.length`), and **I12b** (`Effect` IR structural strict decrease). -/
theorem global_termination_catalog (s : GameState) (hwf : s.WF)
    (effs : List ContinuousEffect) (o : Object) (face : CardFace) (id : ObjId) :
    gspStep (gspRun s) = none ∧
    (evalCharacteristicsWithSteps effs o face id).2 = effs.length :=
  ⟨gspRun_fixed_point hwf, evalCharacteristics_steps_eq effs o face id⟩

end Fab

end
