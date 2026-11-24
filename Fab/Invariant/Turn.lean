module

public import Fab.Invariant.Step

/-!
# Turn, End Phase, asset-clearing, and progress invariants (M3)

Proves M3 theorems from `docs/roadmap.md`:
- **I5** (Progress and `TopIdle`): `advance_idle`, `step_idle`, `progress_decision`
- **I8** (Turn-level asset accounting): `actionPhaseStart_adds_ap`, `endTurnCleanup_clears_pools`
- **I9** (Turn phase order and 1v1 alternation): `turnFrames_eq`, `turnPlayerAt_alternates_1v1`
- **I20** (End Phase Pitch return and Turn 1 / Turn ≥ 2 Intellect refill):
  `returnPitch_empty_pops`, `returnPitch_nonempty_prompts`, `endPhaseDrawFrames_turn1`,
  `endPhaseDrawFrames_later`, `refillCount_zero_of_ge`
-/

@[expose] public section

namespace Fab

/-- **I9** (phase order): every turn progresses strictly through Start → Action → End Phase
(CR 4.2-4.4). -/
theorem turnFrames_eq (tp : PlayerId) :
    turnFrames tp = [.startPhaseWork tp, .actionPhaseStart tp, .endPhaseStart tp] := rfl

/-- **I9** (1v1 alternation): in a 2-player turn order `[a, b]`, turn players alternate every
turn (CR 4.0). -/
theorem turnPlayerAt_alternates_1v1 (a b : PlayerId) (t : Nat) :
    turnPlayerAt [a, b] (2 * t) = a ∧ turnPlayerAt [a, b] (2 * t + 1) = b := by
  unfold turnPlayerAt
  simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, List.length_cons, List.length_nil]
  have h0 : 2 * t % 2 = 0 := by omega
  have h1 : (2 * t + 1) % 2 = 1 := by omega
  constructor
  · rw [h0]; rfl
  · rw [h1]; rfl

/-- **I8** (Action Phase AP grant): `actionPhaseStart tp` grants `tp` exactly +1 Action Point and
leaves all other players' pools unchanged (CR 4.3.2). -/
theorem actionPhaseStart_adds_ap {s s' : GameState} {tp : PlayerId} {rest : List Frame}
    {es : List Event}
    (hp : s.pending = .actionPhaseStart tp :: rest)
    (hm : microStep s = some (s', es)) :
    (s'.poolOf tp).actionPoints = (s.poolOf tp).actionPoints + 1 ∧
    (∀ q, q ≠ tp → s'.poolOf q = s.poolOf q) ∧
    s'.phase = .actionPhase := by
  unfold microStep at hm
  rw [hp] at hm
  simp only [Option.some.injEq, Prod.mk.injEq] at hm
  obtain ⟨rfl, -⟩ := hm
  refine ⟨?_, ?_, rfl⟩
  · change ((s.setPool tp ((s.poolOf tp).addActionPoints 1)).poolOf tp).actionPoints = _
    rw [GameState.poolOf_setPool_self]
    rfl
  · intro q hq
    change (s.setPool tp ((s.poolOf tp).addActionPoints 1)).poolOf q = s.poolOf q
    exact GameState.poolOf_setPool_ne s hq _

/-- **I8** (End Phase asset clearing): `endTurnCleanup` clears EVERY player's Action Points,
Resource Points, and Chi Points to `AssetPool.empty` (CR 4.4.3e). -/
theorem endTurnCleanup_clears_pools {s s' : GameState} {tp : PlayerId} {rest : List Frame}
    {es : List Event}
    (hp : s.pending = .endTurnCleanup tp :: rest)
    (hm : microStep s = some (s', es)) :
    ∀ p : PlayerId, s'.poolOf p = AssetPool.empty := by
  unfold microStep at hm
  rw [hp] at hm
  simp only [Option.some.injEq, Prod.mk.injEq] at hm
  obtain ⟨rfl, -⟩ := hm
  intro p
  rfl

/-- **I20** (Pitch return base case): when a player's pitch zone is empty, `returnPitch` pops
cleanly without prompting (CR 4.4.3c). -/
theorem returnPitch_empty_pops {s : GameState} {p : PlayerId} {rest : List Frame}
    (hp : s.pending = .returnPitch p :: rest)
    (hemp : s.zone (.player p .pitch) = []) :
    microStep s = some ({ s with pending := rest }, []) := by
  unfold microStep
  rw [hp]
  dsimp only
  rw [hemp]
  rfl

/-- **I20** (Pitch return recursive step): when a player's pitch zone is non-empty, `returnPitch`
prompts `choosePitchOrder p` so the owner picks the exact hidden deck-bottom order (CR 4.4.3c). -/
theorem returnPitch_nonempty_prompts {s : GameState} {p : PlayerId} {rest : List Frame}
    {c : ObjId} {cs : List ObjId}
    (hp : s.pending = .returnPitch p :: rest)
    (hne : s.zone (.player p .pitch) = c :: cs) :
    microStep s = some ({ s with pending := .choosePitchOrder p :: rest }, []) := by
  unfold microStep
  rw [hp]
  dsimp only
  rw [hne]
  rfl

/-- **I20** (Turn 1 both-player refill): on Turn 1 (first turn of the game), End Phase cleanup
schedules Intellect refill draws for EVERY player in `turnOrder` (CR 4.4.3f). -/
theorem endPhaseDrawFrames_turn1 {s : GameState} {tp : PlayerId} (h1 : s.turn = 1) :
    endPhaseDrawFrames s tp = s.turnOrder.map (fun q => Frame.draw q (s.refillCount q)) := by
  unfold endPhaseDrawFrames
  simp [h1]

/-- **I20** (Turn ≥ 2 turn-player refill): on turns after Turn 1, End Phase cleanup schedules
Intellect refill draws for ONLY the turn-player `tp` (CR 4.4.3f). -/
theorem endPhaseDrawFrames_later {s : GameState} {tp : PlayerId} (h : s.turn ≠ 1) :
    endPhaseDrawFrames s tp = [Frame.draw tp (s.refillCount tp)] := by
  unfold endPhaseDrawFrames
  simp [h]

/-- **I20** (no over-drawing): a player already holding at least Intellect cards draws 0 cards
during End Phase refill (CR 4.4.3f). -/
theorem refillCount_zero_of_ge {s : GameState} {p : PlayerId}
    (h : s.intellectOf p ≤ (s.zone (.player p .hand)).length) :
    s.refillCount p = 0 := by
  unfold GameState.refillCount
  omega

/-- A state is `TopIdle` when the top of `pending` is not a work frame (i.e. it is waiting for a
decision or the stack is empty). -/
def TopIdle (s : GameState) : Prop :=
  match s.pending with
  | [] => True
  | f :: _ => f.isWork = false

/-- `advance` always stops in a `TopIdle` state when it succeeds. -/
theorem advance_idle :
    ∀ (n : Nat) {s s' : GameState} {es es' : List Event},
      advance n s es = .ok (s', es') → TopIdle s'
  | 0, s, s', es, es', h => by
    unfold advance at h
    cases hp : s.pending with
    | nil =>
      rw [hp] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      simp [TopIdle, hp]
    | cons f rest =>
      rw [hp] at h
      dsimp only at h
      split at h
      · cases h
      · rename_i hnw
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        unfold TopIdle
        rw [hp]
        dsimp only
        cases hw : f.isWork
        · rfl
        · exact False.elim (hnw hw)
  | n + 1, s, s', es, es', h => by
    unfold advance at h
    cases hp : s.pending with
    | nil =>
      rw [hp] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      simp [TopIdle, hp]
    | cons f rest =>
      rw [hp] at h
      dsimp only at h
      split at h
      · split at h
        · exact advance_idle n h
        · cases h
      · rename_i hnw
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        unfold TopIdle
        rw [hp]
        dsimp only
        cases hw : f.isWork
        · rfl
        · exact False.elim (hnw hw)

/-- `step` always leaves the game in a `TopIdle` state when it succeeds. -/
theorem step_idle {fuel : Nat} {s s' : GameState} {a : Action} {es : List Event}
    (h : step fuel s a = .ok (s', es)) : TopIdle s' := by
  unfold step at h
  split at h
  · split at h
    · exact advance_idle fuel h
    · cases h
  · cases h

/-- **I5** (Progress on decision frames): on any ongoing state with at least 2 players, every
decision frame except an incomplete `chooseLoadout` has a legal non-concede action (either a
player action in `legalFrameActions`, or a legal `Actor.chance` answer). -/
theorem progress_turn_decisions {s : GameState}
    (hres : s.result = none) (hplayers : 0 < s.playerCount) :
    (∀ p n rest, s.pending = .priority p n :: rest →
      ∃ a ∈ legalActions s, a.kind ≠ .concede) ∧
    (∀ tp rest, s.pending = .chooseArsenal tp :: rest →
      ∃ a ∈ legalActions s, a.kind ≠ .concede) ∧
    (∀ chooser rest, s.pending = .chooseFirstPlayer chooser :: rest →
      ∃ a ∈ legalActions s, a.kind ≠ .concede) ∧
    (∀ p rest c cs, s.pending = .choosePitchOrder p :: rest →
      s.zone (.player p .pitch) = c :: cs →
      ∃ a ∈ legalActions s, a.kind ≠ .concede) ∧
    (∀ rest, s.pending = .chanceFirstPlayer :: rest →
      ∃ a, Legal s a ∧ a.actor = .chance) ∧
    (∀ z rest, s.pending = .chanceShuffle z :: rest → z.Valid s.playerCount →
      ∃ a, Legal s a ∧ a.actor = .chance) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p n rest hp
    refine ⟨⟨.player p, .pass⟩, ?_, by simp⟩
    rw [legalActions_iff]
    exact ⟨⟨hres, Or.inl (by simp [LegalFrame, hp])⟩, rfl⟩
  · intro tp rest hp
    refine ⟨⟨.player tp, .arsenalSkip⟩, ?_, by simp⟩
    rw [legalActions_iff]
    exact ⟨⟨hres, Or.inl (by simp [LegalFrame, hp])⟩, rfl⟩
  · intro chooser rest hp
    refine ⟨⟨.player chooser, .pickFirstPlayer ⟨0⟩⟩, ?_, by simp⟩
    rw [legalActions_iff]
    exact ⟨⟨hres, Or.inl (by simp [LegalFrame, hp, hplayers])⟩, rfl⟩
  · intro p rest c cs hp hne
    refine ⟨⟨.player p, .pitchReturnPick c⟩, ?_, by simp⟩
    rw [legalActions_iff]
    exact ⟨⟨hres, Or.inl (by simp [LegalFrame, hp, hne])⟩, rfl⟩
  · intro rest hp
    exact ⟨⟨.chance, .chanceFirstChooser ⟨0⟩⟩,
      ⟨hres, Or.inl (by simp [LegalFrame, hp, hplayers])⟩, rfl⟩
  · intro z rest hp hz
    exact ⟨⟨.chance, .shuffleOrder (s.zone z)⟩,
      ⟨hres, Or.inl (by simp [LegalFrame, hp, hz, List.Perm.refl])⟩, rfl⟩

end Fab

end
