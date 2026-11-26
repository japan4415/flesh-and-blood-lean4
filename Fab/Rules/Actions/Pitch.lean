module

public import Fab.Rules.Move

/-!
# Pitch primitive

Pitching moves a pitchable card from a player's hand to their pitch zone and generates resource
points `{r}` or chi points `{c}` equal to its printed pitch value (CR 1.14.3, 2.8, 3.14).
-/

@[expose] public section

namespace Fab

/-- Look up the currently active `CardFace` of an object in `s.cards` (respecting `faceState`
for double-faced cards such as Transcend). -/
def GameState.activeFace? (s : GameState) (o : Object) : Option CardFace :=
  match o.kind.cardId? with
  | none => none
  | some cid =>
    match s.cards.find? cid with
    | none => none
    | some def_ =>
      match o.faceState with
      | .front => some def_.front
      | .back => def_.back

/-- Pitch card `id` from player `p`'s hand into `p`'s pitch zone, adding the value and kind of its
active face's printed pitch assets (CR 1.14.3, 2.8.2, 3.14). -/
def pitchOne (s : GameState) (p : PlayerId) (id : ObjId) :
    Option (GameState × ObjId × List Event) :=
  if id ∈ s.zone (.player p .hand) then
    match s.obj? id with
    | none => none
    | some o =>
      match s.activeFace? o with
      | none => none
      | some face =>
        match face.pitch with
        | none => none
        | some v =>
          match moveObj s id (.player p .pitch) .top false with
          | none => none
          | some (s1, id') =>
            let isChi := face.pitchAsset == .chi
            let r := if isChi then 0 else v
            let c := if isChi then v else 0
            let pool' := ((s1.poolOf p).addResources r).addChi c
            let s2 := s1.setPool p pool'
            some (s2, id', [.moved id id' (.player p .hand) (.player p .pitch),
                            .pitched p id' r c])
  else
    none

/-- `pitchOne` preserves `WF`. -/
theorem pitchOne_wf {s s' : GameState} {p : PlayerId} {id id' : ObjId} {es : List Event}
    (hwf : s.WF) (h : pitchOne s p id = some (s', id', es)) : s'.WF := by
  unfold pitchOne at h
  split at h
  · cases ho : s.obj? id with
    | none => simp only [ho] at h; cases h
    | some o =>
      simp only [ho] at h
      cases hf : s.activeFace? o with
      | none => simp only [hf] at h; cases h
      | some face =>
        simp only [hf] at h
        cases hp : face.pitch with
        | none => simp only [hp] at h; cases h
        | some v =>
          simp only [hp] at h
          cases hm : moveObj s id (.player p .pitch) .top false with
          | none => simp only [hm] at h; cases h
          | some res =>
            obtain ⟨s1, id1⟩ := res
            simp only [hm, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            exact GameState.WF.congr (moveObj_wf hwf hm) rfl rfl rfl rfl
  · cases h

/-- `pitchOne` preserves the multiset of physical card identifiers (I1). -/
theorem pitchOne_physIds {s s' : GameState} {p : PlayerId} {id id' : ObjId} {es : List Event}
    (hwf : s.WF) (h : pitchOne s p id = some (s', id', es)) : s'.physIds.Perm s.physIds := by
  unfold pitchOne at h
  split at h
  · cases ho : s.obj? id with
    | none => simp only [ho] at h; cases h
    | some o =>
      simp only [ho] at h
      cases hf : s.activeFace? o with
      | none => simp only [hf] at h; cases h
      | some face =>
        simp only [hf] at h
        cases hp : face.pitch with
        | none => simp only [hp] at h; cases h
        | some v =>
          simp only [hp] at h
          cases hm : moveObj s id (.player p .pitch) .top false with
          | none => simp only [hm] at h; cases h
          | some res =>
            obtain ⟨s1, id1⟩ := res
            simp only [hm, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            change s1.physIds.Perm s.physIds
            exact moveObj_physIds hwf hm
  · cases h

/-- `pitchOne` preserves `OwnerOk`. -/
theorem pitchOne_ownerOk {s s' : GameState} {p : PlayerId} {id id' : ObjId} {es : List Event}
    (hwf : s.WF) (hok : s.OwnerOk) (h : pitchOne s p id = some (s', id', es)) : s'.OwnerOk := by
  unfold pitchOne at h
  split at h
  · cases ho : s.obj? id with
    | none => simp only [ho] at h; cases h
    | some o =>
      simp only [ho] at h
      cases hf : s.activeFace? o with
      | none => simp only [hf] at h; cases h
      | some face =>
        simp only [hf] at h
        cases hp : face.pitch with
        | none => simp only [hp] at h; cases h
        | some v =>
          simp only [hp] at h
          cases hm : moveObj s id (.player p .pitch) .top false with
          | none => simp only [hm] at h; cases h
          | some res =>
            obtain ⟨s1, id1⟩ := res
            simp only [hm, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            exact GameState.OwnerOk.congr (moveObj_ownerOk hwf hok hm) rfl rfl
  · cases h

/-- Pitching adds exact pitch value to player `p`'s total energy (`resources + chi`) and leaves
every other player's asset pool unchanged, I8 one step (CR 1.14.3, 2.8). -/
theorem pitchOne_adds_assets {s s' : GameState} {p : PlayerId} {id id' : ObjId}
    {o : Object} {face : CardFace} {v : Nat} {es : List Event}
    (ho : s.obj? id = some o) (hf : s.activeFace? o = some face) (hp : face.pitch = some v)
    (h : pitchOne s p id = some (s', id', es)) :
    (s'.poolOf p).totalEnergy = (s.poolOf p).totalEnergy + v ∧
    (∀ q, q ≠ p → s'.poolOf q = s.poolOf q) := by
  unfold pitchOne at h
  split at h
  · simp only [ho, hf, hp] at h
    cases hm : moveObj s id (.player p .pitch) .top false with
    | none => simp only [hm] at h; cases h
    | some res =>
      obtain ⟨s1, id1⟩ := res
      simp only [hm, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, _, hs⟩ := moveObj_spec hm
      obtain ⟨rfl, rfl, rfl⟩ := h
      have hpool1 : ∀ q, s1.poolOf q = s.poolOf q := fun q => by
        simp [GameState.poolOf, hs.pools]
      constructor
      · rw [GameState.poolOf_setPool_self, hpool1 p]
        cases face.pitchAsset <;>
          simp [AssetPool.totalEnergy, AssetPool.addResources, AssetPool.addChi] <;> omega
      · intro q hqp
        rw [GameState.poolOf_setPool_ne _ hqp, hpool1 q]
  · cases h

/-- `pitchOne` preserves `config` and `playRollback`. -/
theorem pitchOne_config_rollback {s s' : GameState} {p : PlayerId} {id id' : ObjId}
    {es : List Event} (h : pitchOne s p id = some (s', id', es)) :
    s'.config = s.config ∧ s'.playRollback = s.playRollback := by
  unfold pitchOne at h
  split at h
  · cases ho : s.obj? id with
    | none => simp only [ho] at h; cases h
    | some o =>
      simp only [ho] at h
      cases hf : s.activeFace? o with
      | none => simp only [hf] at h; cases h
      | some face =>
        simp only [hf] at h
        cases hp : face.pitch with
        | none => simp only [hp] at h; cases h
        | some v =>
          simp only [hp] at h
          cases hm : moveObj s id (.player p .pitch) .top false with
          | none => simp only [hm] at h; cases h
          | some res =>
            obtain ⟨s1, id1⟩ := res
            simp only [hm, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            unfold moveObj at hm
            split at hm
            · dsimp only at hm
              split at hm
              · cases hm
              · split at hm <;>
                · simp only [Option.some.injEq, Prod.mk.injEq] at hm
                  obtain ⟨rfl, rfl⟩ := hm
                  exact ⟨rfl, rfl⟩
            · cases hm
  · cases h

/-- Whether card `id` in player `p`'s hand has a printed pitch value and can be pitched (CR 1.14.3). -/
def canPitchCard (s : GameState) (p : PlayerId) (id : ObjId) : Bool :=
  if id ∈ s.zone (.player p .hand) then
    match s.obj? id with
    | none => false
    | some o =>
      match s.activeFace? o with
      | none => false
      | some face => face.pitch.isSome && !s.isCardNameRestricted id
  else
    false

/-- Under `WF` and `OwnerOk`, pitching any card satisfying `canPitchCard` succeeds. -/
theorem pitchOne_isSome {s : GameState} {p : PlayerId} {id : ObjId}
    (hwf : s.WF) (hok : s.OwnerOk) (hp_valid : p.n < s.playerCount)
    (hc : canPitchCard s p id = true) :
    (pitchOne s p id).isSome = true := by
  unfold canPitchCard at hc
  unfold pitchOne
  split at hc
  · rename_i hmem
    simp only [hmem, ↓reduceIte]
    cases ho : s.obj? id with
    | none => simp only [ho] at hc; cases hc
    | some o =>
      simp only [ho] at hc ⊢
      cases hf : s.activeFace? o with
      | none => simp only [hf] at hc; cases hc
      | some face =>
        simp only [hf] at hc ⊢
        cases hp : face.pitch with
        | none => simp only [hp] at hc; cases hc
        | some v =>
          have hloc : s.locate id = some (.player p .hand) :=
            GameState.locate_eq hwf (Zone.valid_player hp_valid .hand) hmem
          have hown : o.owner = p := hok.owner p .hand rfl id hmem o ho
          have hnorm : Zone.normalize o.owner (.player p .pitch) = .player p .pitch := by
            simp [Zone.normalize, ZoneKind.isArena, hown]
          have hval : (Zone.player p .pitch).Valid s.playerCount := Zone.valid_player hp_valid .pitch
          have hm : (moveObj s id (.player p .pitch) .top false).isSome = true := by
            unfold moveObj
            rw [hloc, ho]
            dsimp only
            rw [hnorm]
            have hne : Zone.player p .hand ≠ Zone.player p .pitch := by intro heq; cases heq
            simp only [hne, false_or, hval, not_true_eq_false, ↓reduceIte]
            split <;> rfl
          cases hm' : moveObj s id (.player p .pitch) .top false with
          | none => rw [hm'] at hm; simp at hm
          | some _ => rfl
  · cases hc

end Fab

end
