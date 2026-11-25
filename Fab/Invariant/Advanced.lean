module

public import Fab.Rules.Advanced
public import Fab.Invariant.Step

/-!
# Advanced Mechanics Invariants (M8, CR Chapter 8-9)

Proves M8 correctness properties:
- **Double-faced cards**: `transcendCard_yields_back_face`, `transformObject_flips_preserving_objId`
- **Split / Meld (CR 8.3.38)**: `meld_both_combines_costs_and_resolves_right_first`
- **Cloaked equipment (CR 8.3.29)**: `revealObject_keeps_cloaked_faceDown`,
  `turnEquipmentFaceUp_sets_faceUp`
- **Ally End Phase life reset (CR 4.4.3a)**: `resetAllyLife_restores_base`
- **Landmark uniqueness in GSP** (CR 1.10.2b): `settled_has_no_older_landmarks`
- **Tap / Untap (CR 8.2)**: `payTapCost_taps_and_blocks_second_tap`
- **Clash symmetry (CR 8.5.39)**: `resolveClash_symm`
- **Mark idempotence (CR 8.5.48)**: `markPlayer_marks`, `clearMark_clears`
-/

@[expose] public section

namespace Fab

/-- **Transcend back-face preservation** (CR 8.3.37): when `transcendCard s id` succeeds, the
resulting card `id'` in the owner's hand has `faceState = .back`. -/
theorem transcendCard_yields_back_face {s s' : GameState} {id id' : ObjId} {es : List Event}
    (h : transcendCard s id = some (s', id', es)) :
    (s'.obj? id').map (·.faceState) = some .back := by
  unfold transcendCard at h
  cases hloc : s.locate id with
  | none => rw [hloc] at h; cases h
  | some srcZ =>
    cases ho : s.obj? id with
    | none => rw [hloc, ho] at h; cases h
    | some o =>
      cases hc : s.cardDefOf? id with
      | none => rw [hloc, ho, hc] at h; cases h
      | some c =>
        rw [hloc, ho, hc] at h
        dsimp only at h
        split at h
        · let sF := updateSingleObject s id fun obj => { obj with faceState := .back }
          have hoRaw : s.objects[id.n]? = some o := ho
          have hoF : sF.obj? id = some { o with faceState := .back } := by
            unfold sF updateSingleObject GameState.obj?
            rw [hoRaw]
            simp
          cases hm : moveObj sF id (.player o.owner .hand) .top false with
          | none => rw [hm] at h; cases h
          | some res =>
            obtain ⟨s1, newId⟩ := res
            rw [hm] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, -⟩ := h
            unfold moveObj at hm
            cases hlocF : sF.locate id with
            | none => rw [hlocF] at hm; cases hm
            | some srcF =>
              rw [hlocF, hoF] at hm
              dsimp only at hm
              split at hm
              · cases hm
              · split at hm
                · simp only [Option.some.injEq, Prod.mk.injEq] at hm
                  obtain ⟨rfl, rfl⟩ := hm
                  simp [GameState.obj?, Object.resetOnZoneChange]
                · simp only [Option.some.injEq, Prod.mk.injEq] at hm
                  obtain ⟨rfl, rfl⟩ := hm
                  change (sF.obj? id).map (·.faceState) = some .back
                  rw [hoF]
                  rfl
        · cases h

/-- **Transform preserves ObjId** (CR 3.0.9, 8.2): transforming a double-faced object flips its
`faceState` under the exact same `ObjId`. -/
theorem transformObject_flips_preserving_objId {s : GameState} {id : ObjId} {o : Object}
    {c : CardDef} {bf : CardFace}
    (ho : s.obj? id = some o) (hc : s.cardDefOf? id = some c) (hb : c.back = some bf) :
    ((transformObject s id).obj? id).map (·.faceState) = some o.faceState.flip := by
  unfold transformObject
  rw [hc]
  dsimp only
  rw [hb]
  simp only [Option.isSome_some, ↓reduceIte]
  unfold updateSingleObject GameState.obj?
  have hoRaw : s.objects[id.n]? = some o := ho
  rw [hoRaw]
  simp

/-- **Meld combined cost & right-first resolution** (CR 8.3.38): melding `.both` halves sums
resource and chi costs and queues right-half resolution strictly before left-half resolution. -/
theorem meld_both_combines_costs_and_resolves_right_first (c : CardDef) :
    (meldEffectiveCost c .both).resources =
      (meldEffectiveCost c .left).resources + (meldEffectiveCost c .right).resources ∧
    (meldEffectiveCost c .both).chi =
      (meldEffectiveCost c .left).chi + (meldEffectiveCost c .right).chi ∧
    meldResolveEffects c .both =
      meldResolveEffects c .right ++ meldResolveEffects c .left := by
  unfold meldEffectiveCost meldResolveEffects
  exact ⟨rfl, rfl, rfl⟩

/-- **Cloaked Start-of-Game protection** (CR 4.1.4, 8.3.29): `revealObject` leaves any face-down
object with `.cloaked` strictly face-down. -/
theorem revealObject_keeps_cloaked_faceDown {db : CardDB} {o : Object} {cid : CardId}
    {c : CardDef} (hcid : o.kind.cardId? = some cid) (hfind : db.find? cid = some c)
    (hclk : c.front.keywords.contains .cloaked = true) (hfd : o.faceDown = true) :
    (revealObject db o).faceDown = true := by
  simp only [revealObject, hcid, hfind, hclk, ↓reduceIte, hfd]

/-- **Cloaked turn face-up** (CR 8.3.29): `turnEquipmentFaceUp` flips an existing object face-up
preserving its exact `ObjId`. -/
theorem turnEquipmentFaceUp_sets_faceUp {s : GameState} {id : ObjId} {o : Object}
    (ho : s.obj? id = some o) :
    ((turnEquipmentFaceUp s id).obj? id).map (·.faceDown) = some false := by
  unfold turnEquipmentFaceUp updateSingleObject GameState.obj?
  have hoRaw : s.objects[id.n]? = some o := ho
  rw [hoRaw]
  simp

/-- **Ally End Phase life reset** (CR 4.4.3a): `resetAllyLife` restores a damaged front-face Ally
object's `life` back to its printed base life. -/
theorem resetAllyLife_restores_base {db : CardDB} {o : Object} {cid : CardId} {c : CardDef}
    {baseHp : Int}
    (hcid : o.kind.cardId? = some cid) (hfind : db.find? cid = some c)
    (hfs : o.faceState = .front) (hally : c.front.hasSubtype .ally = true)
    (hlife : c.front.life = some baseHp) :
    (resetAllyLife db o).life = some baseHp := by
  unfold resetAllyLife
  rw [hcid]
  dsimp only
  rw [hfind]
  dsimp only
  rw [hfs]
  simp [hally, hlife]

/-- **Landmark uniqueness in Settled states** (CR 1.10.2b): in any `Settled` state (such as
the output of `gspRun`), `olderLandmarks s = []` (no duplicate Landmarks remain in the Arena). -/
theorem settled_has_no_older_landmarks {s : GameState} (hs : Settled s) :
    olderLandmarks s = [] :=
  hs.2.2.2

/-- **Tap cost enforcement** (CR 8.2): paying a `{t}` cost marks the object tapped and forbids
paying `{t}` a second time until untapped. -/
theorem payTapCost_taps_and_blocks_second_tap {s s' : GameState} {p : PlayerId} {id : ObjId}
    (h : payTapCost s p id = some s') :
    canPayTapCost s' p id = false := by
  unfold payTapCost at h
  split at h
  · rename_i hcan
    simp only [Option.some.injEq] at h
    subst h
    unfold canPayTapCost at hcan ⊢
    cases hloc : s.locate id with
    | none => rw [hloc] at hcan; cases hcan
    | some z =>
      cases ho : s.obj? id with
      | none => rw [hloc, ho] at hcan; cases hcan
      | some o =>
        have hloc' : (tapObject s id).locate id = some z := by
          unfold tapObject updateSingleObject
          have hoRaw : s.objects[id.n]? = some o := ho
          rw [hoRaw]
          exact hloc
        have ho' : (tapObject s id).obj? id = some { o with tapped := true } := by
          unfold tapObject updateSingleObject GameState.obj?
          have hoRaw : s.objects[id.n]? = some o := ho
          rw [hoRaw]
          simp
        rw [hloc', ho']
        simp
  · cases h

/-- **Clash symmetry** (CR 8.5.39): swapping the two clashing players `pA` and `pB` produces the
exact same winner (or tie). -/
theorem resolveClash_symm (s : GameState) (pA pB : PlayerId) :
    resolveClash s pA pB = resolveClash s pB pA := by
  unfold resolveClash
  cases topDeckPower? s pA with
  | none =>
    cases topDeckPower? s pB <;> rfl
  | some pa =>
    cases topDeckPower? s pB with
    | none => rfl
    | some pb =>
      by_cases h1 : pa > pb
      · have h2 : ¬ (pb > pa) := by omega
        simp [h1, h2]
      · by_cases h2 : pb > pa
        · simp [h1, h2]
        · simp [h1, h2]

/-- **Mark set/clear** (CR 8.5.48): `markPlayer` sets `isPlayerMarked = true` and `clearMark`
sets `isPlayerMarked = false`. -/
theorem markPlayer_and_clearMark (s : GameState) (p : PlayerId) :
    isPlayerMarked (markPlayer s p) p = true ∧
    isPlayerMarked (clearMark s p) p = false := by
  constructor
  · unfold isPlayerMarked markPlayer
    by_cases h : p ∈ s.markedPlayers <;> simp [h]
  · unfold isPlayerMarked clearMark
    simp

end Fab

end
