module

public import Fab.Invariant.Step

/-!
# Replacement, Simultaneous Triggers, and Combat Keyword Invariants (M6b)

Proves M6b theorems from `docs/roadmap.md`:
- **I19** (Simultaneous Trigger Stacking): `flushTriggers_empty_pops`,
  `flushTriggers_prompts_turn_player`, `chooseTriggerStart_sets_clockwise_order`
- **I5** (Progress on M6b decision frames): `progress_m6b_decisions`
- **Combat Keywords (CR 8.3)**: `crushTriggered_iff`, `repriseActive_iff`,
  `comboActive_reads_prevLink_lki`, `phantasm_ignores_illusionist`, `bloodDebt_ignores_faceDown`
- Re-exports **L5** (`ReplacementStageSpec`, `applyReplacementPipeline_matches_spec`,
  `applyReplacementPipeline_nodup`) and Release Notes rulings (`ward_mandatory_prevents_damage`,
  `arcaneBarrier_ignores_physical`, `arcaneBarrier_optional_can_decline`) via `Fab.Rules.Replacement`.
-/

@[expose] public section

namespace Fab

/-- **I19** (no pending triggers): `flushTriggers` pops immediately when `pendingTriggers = []`
(CR 6.6). -/
theorem flushTriggers_empty_pops {s : GameState} {rest : List Frame}
    (hp : s.pending = .flushTriggers :: rest) (hemp : s.pendingTriggers = []) :
    microStep s = some ({ s with pending := rest }, []) := by
  unfold microStep
  rw [hp]
  dsimp only
  rw [hemp]
  rfl

/-- **I19** (turn-player start selection): when at least one trigger is pending, `flushTriggers`
prompts the turn-player (`s.active.getD ⟨0⟩`) with `chooseTriggerStart` (CR 6.6.6b). -/
theorem flushTriggers_prompts_turn_player {s : GameState} {t : PendingTrigger}
    {ts : List PendingTrigger} {rest : List Frame}
    (hp : s.pending = .flushTriggers :: rest) (hne : s.pendingTriggers = t :: ts) :
    microStep s = some ({ s with pending := .chooseTriggerStart (s.active.getD ⟨0⟩) :: rest }, []) := by
  unfold microStep
  rw [hp]
  dsimp only
  rw [hne]
  rfl

/-- **I19** (clockwise start rotation): answering `chooseTriggerStart tp` with `start ∈ s.turnOrder`
starts stacking triggers from `rotateTurnOrderFrom s.turnOrder start` (CR 6.6.6b). -/
theorem chooseTriggerStart_sets_clockwise_order {s : GameState} {tp start : PlayerId}
    {rest : List Frame}
    (hp : s.pending = .chooseTriggerStart tp :: rest)
    (hmem : start ∈ s.turnOrder) :
    applyFrame s ⟨.player tp, .pickTriggerStart start⟩ =
      some ({ s with pending := nextTriggerFrame s (rotateTurnOrderFrom s.turnOrder start) ++ rest }, []) := by
  unfold applyFrame
  rw [hp]
  simp [hmem]

/-- **I5** (Progress on M6b decision frames): every M6b decision frame on an ongoing state has a
legal non-concede player action in `legalActions` whenever its domain is non-empty. -/
theorem progress_m6b_decisions {s : GameState} (hres : s.result = none) :
    (∀ tp p ps rest, s.pending = .chooseTriggerStart tp :: rest →
      s.turnOrder = p :: ps →
      ∃ a ∈ legalActions s, a.kind ≠ .concede) ∧
    (∀ p rem rest t target, s.pending = .chooseTriggerOrder p rem :: rest →
      t ∈ s.pendingTriggers → t.controller = p → target ∈ t.heroChoices s.turnOrder →
      ∃ a ∈ legalActions s, a.kind ≠ .concede) ∧
    (∀ aff st c cs cd rest, s.pending = .chooseReplacement aff st (c :: cs) cd :: rest →
      ∃ a ∈ legalActions s, a.kind ≠ .concede) ∧
    (∀ aff st cands rest, s.pending = .chooseReplacement aff st cands true :: rest →
      ∃ a ∈ legalActions s, a.kind ≠ .concede) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro tp p ps rest hp hord
    refine ⟨⟨.player tp, .pickTriggerStart p⟩, ?_, by simp⟩
    rw [legalActions_iff]
    exact ⟨⟨hres, Or.inl (by simp [LegalFrame, hp, hord])⟩, rfl⟩
  · intro p rem rest t target hp hmem hctrl htarget
    refine ⟨⟨.player p, .pickTrigger t.id target⟩, ?_, by simp⟩
    rw [legalActions_iff]
    refine ⟨⟨hres, Or.inl ?_⟩, rfl⟩
    unfold LegalFrame
    rw [hp]
    refine ⟨rfl, ?_⟩
    rw [List.any_eq_true]
    exact ⟨t, hmem, by simp [PendingTrigger.matchesDeclaration, hctrl, htarget]⟩
  · intro aff st c cs cd rest hp
    refine ⟨⟨.player aff, .pickReplacement (some c)⟩, ?_, by simp⟩
    rw [legalActions_iff]
    exact ⟨⟨hres, Or.inl (by simp [LegalFrame, hp])⟩, rfl⟩
  · intro aff st cands rest hp
    refine ⟨⟨.player aff, .pickReplacement none⟩, ?_, by simp⟩
    rw [legalActions_iff]
    exact ⟨⟨hres, Or.inl (by simp [LegalFrame, hp])⟩, rfl⟩

/-- **Crush** (CR 8.3.7): `crushTriggered link` holds iff `4 ≤ link.damageDealt`. -/
theorem crushTriggered_iff (link : ChainLink) :
    crushTriggered link = true ↔ 4 ≤ link.damageDealt := by
  unfold crushTriggered
  simp

/-- **Reprise** (CR 8.3.8): `repriseActive link` holds iff at least one card defended from hand. -/
theorem repriseActive_iff (link : ChainLink) :
    repriseActive link = true ↔ 0 < link.defendedFromHandCount := by
  unfold repriseActive
  simp

/-- **Combo + LKI** (CR 8.3.6, 3.5.4b): `comboActive` inspects `prevLink.attackLki.name` directly,
so Combo still activates even after the previous link's physical card left the Combat Chain
(`prevLink.attack = none`). -/
theorem comboActive_reads_prevLink_lki {s : GameState} {cc : CombatChain}
    {cur prev : ChainLink} {older : List ChainLink} {names : List String}
    (hcc : s.combat = some cc) (hlinks : cc.links = cur :: prev :: older)
    (hmem : prev.attackLki.name ∈ names) :
    comboActive s names = true := by
  unfold comboActive
  rw [hcc]
  dsimp only [Option.bind, CombatChain.prevLink?]
  rw [hlinks]
  simpa using hmem

/-- **Phantasm vs Illusionist** (CR 8.3.13): a defending card whose derived supertypes include
`ClassType.illusionist` NEVER triggers Phantasm, regardless of its power. -/
theorem phantasm_ignores_illusionist {s : GameState} {id : ObjId} {dc : DerivedChars}
    (hc : s.characteristics id = some dc)
    (hill : Supertype.class_ .illusionist ∈ dc.supertypes) :
    triggersPhantasmDef s id = false := by
  unfold triggersPhantasmDef
  rw [hc]
  simp [hill]

/-- **Blood Debt face-down exemption** (CR 8.3.12): a face-down banished card NEVER counts toward
Blood Debt. -/
theorem bloodDebt_ignores_faceDown {s : GameState} {id : ObjId} {o : Object}
    (ho : s.obj? id = some o) (hfd : o.faceDown = true) :
    isFaceUpBloodDebt s id = false := by
  unfold isFaceUpBloodDebt
  rw [ho]
  cases s.cardDefOf? id <;> simp [hfd]

end Fab

end
