module

public import Fab.Rules.Move

/-!
# Object-table updates and hero defeat checks

Pure object-table transformations for untapping a player's permanents at End Phase (CR 4.4.3d) and
hero life defeat / simultaneous draw checks (CR 1.10.2a, 4.5).
-/

@[expose] public section

namespace Fab

/-- Untap a single object if it is controlled by player `p` (CR 4.4.3d). -/
def untapIfControlled (p : PlayerId) (o : Object) : Object :=
  if o.controller == p then { o with tapped := false } else o

/-- `untapIfControlled` is idempotent. -/
theorem untapIfControlled_idem (p : PlayerId) (o : Object) :
    untapIfControlled p (untapIfControlled p o) = untapIfControlled p o := by
  unfold untapIfControlled
  by_cases h : (o.controller == p) = true
  · simp [h]
  · simp [h]

/-- `untapIfControlled` preserves `kind`. -/
theorem untapIfControlled_kind (p : PlayerId) (o : Object) :
    (untapIfControlled p o).kind = o.kind := by
  unfold untapIfControlled
  split <;> rfl

/-- `untapIfControlled` preserves `owner`. -/
theorem untapIfControlled_owner (p : PlayerId) (o : Object) :
    (untapIfControlled p o).owner = o.owner := by
  unfold untapIfControlled
  split <;> rfl

/-- Map a pure object update across every entry in `s.objects`. -/
def GameState.mapObjects (s : GameState) (f : Object → Object) : GameState :=
  { s with objects := s.objects.map fun _ o => f o }

/-- Untap all permanents controlled by player `p` (CR 4.4.3d). -/
def untapPlayer (s : GameState) (p : PlayerId) : GameState :=
  s.mapObjects (untapIfControlled p)

/-- `mapObjects` preserves `WF`. -/
theorem GameState.mapObjects_wf {s : GameState} (hwf : s.WF) (f : Object → Object) :
    (s.mapObjects f).WF := by
  refine GameState.WF.congr_mem hwf rfl ?_ rfl rfl
  intro k
  simp [GameState.mapObjects]

/-- `mapObjects` preserves `OwnerOk` whenever `f` preserves `owner`. -/
theorem GameState.mapObjects_ownerOk {s : GameState} (hok : s.OwnerOk) {f : Object → Object}
    (hf : ∀ o, (f o).owner = o.owner) : (s.mapObjects f).OwnerOk := by
  refine ⟨fun p k hk id hid o hobj => ?_⟩
  have hzone : (s.mapObjects f).zone (.player p k) = s.zone (.player p k) := rfl
  rw [hzone] at hid
  simp only [GameState.obj?, GameState.mapObjects, Std.ExtTreeMap.getElem?_map] at hobj
  cases hg : s.objects[id.n]? with
  | none => rw [hg] at hobj; simp at hobj
  | some o0 =>
    rw [hg] at hobj
    simp only [Option.map_some, Option.some.injEq] at hobj
    subst hobj
    rw [hf o0]
    exact hok.owner p k hk id hid o0 hg

/-- `mapObjects` preserves `physIds` whenever `f` preserves `kind`. -/
theorem GameState.mapObjects_physIds (s : GameState) {f : Object → Object}
    (hf : ∀ o, (f o).kind = o.kind) : (s.mapObjects f).physIds = s.physIds := by
  unfold GameState.physIds
  have hids : (s.mapObjects f).zoneIds = s.zoneIds := rfl
  rw [hids]
  apply filterMap_congr_mem
  intro id _
  simp only [GameState.obj?, GameState.mapObjects, Std.ExtTreeMap.getElem?_map]
  cases hg : s.objects[id.n]? with
  | none => rfl
  | some o0 => simp [hf o0]

/-- `untapPlayer` preserves `WF`. -/
theorem untapPlayer_wf {s : GameState} (hwf : s.WF) (p : PlayerId) :
    (untapPlayer s p).WF :=
  GameState.mapObjects_wf hwf (untapIfControlled p)

/-- `untapPlayer` preserves `OwnerOk`. -/
theorem untapPlayer_ownerOk {s : GameState} (hok : s.OwnerOk) (p : PlayerId) :
    (untapPlayer s p).OwnerOk :=
  GameState.mapObjects_ownerOk hok (untapIfControlled_owner p)

/-- `untapPlayer` preserves `physIds` (I1). -/
theorem untapPlayer_physIds (s : GameState) (p : PlayerId) :
    (untapPlayer s p).physIds = s.physIds :=
  GameState.mapObjects_physIds s (untapIfControlled_kind p)

/-- `untapPlayer` is idempotent (CR 4.4.3d). -/
theorem untapPlayer_idem (s : GameState) (p : PlayerId) :
    untapPlayer (untapPlayer s p) p = untapPlayer s p := by
  unfold untapPlayer GameState.mapObjects
  congr 1
  apply Std.ExtTreeMap.ext_getElem?
  intro k
  simp only [Std.ExtTreeMap.getElem?_map]
  cases s.objects[k]? with
  | none => rfl
  | some o => simp [untapIfControlled_idem]

/-- Players whose hero currently has positive life (`0 < lifeOf p`) (CR 1.10.2a, 4.5). -/
def livingPlayers (s : GameState) : List PlayerId :=
  (allPlayers s.playerCount).filter fun p => decide (0 < s.lifeOf p)

/-- Check for hero defeat (life ≤ 0): if no heroes survive, the game is a simultaneous draw; if
exactly one hero survives, that player wins (CR 1.10.2a, 4.5). -/
def checkHeroDefeat (s : GameState) : GameState :=
  if s.result.isSome then s
  else
    match livingPlayers s with
    | [] => { s with result := some (.draw .simultaneousHeroDeath), pending := [] }
    | [w] => { s with result := some (.won [w]), pending := [] }
    | _ :: _ :: _ => s

/-- `checkHeroDefeat` preserves `WF`. -/
theorem checkHeroDefeat_wf {s : GameState} (hwf : s.WF) :
    (checkHeroDefeat s).WF := by
  unfold checkHeroDefeat
  split
  · exact hwf
  · split <;> exact GameState.WF.congr hwf rfl rfl rfl rfl

/-- `checkHeroDefeat` preserves `OwnerOk`. -/
theorem checkHeroDefeat_ownerOk {s : GameState} (hok : s.OwnerOk) :
    (checkHeroDefeat s).OwnerOk := by
  unfold checkHeroDefeat
  split
  · exact hok
  · split <;> exact GameState.OwnerOk.congr hok rfl rfl

/-- `checkHeroDefeat` preserves `physIds` (I1). -/
theorem checkHeroDefeat_physIds (s : GameState) :
    (checkHeroDefeat s).physIds = s.physIds := by
  unfold checkHeroDefeat
  split
  · rfl
  · split <;> rfl

/-- **I7** (1v1 win/draw uniqueness): in an ongoing 2-player game, `checkHeroDefeat` yields:
- `none` when both heroes have positive life
- `some (.won [⟨0⟩])` when only player 0 survives
- `some (.won [⟨1⟩])` when only player 1 survives
- `some (.draw .simultaneousHeroDeath)` when both heroes are at 0 or less (CR 1.10.2a, 4.5). -/
theorem checkHeroDefeat_1v1 {s : GameState} (hp : s.playerCount = 2) (hr : s.result = none) :
    (0 < s.lifeOf ⟨0⟩ ∧ 0 < s.lifeOf ⟨1⟩ → (checkHeroDefeat s).result = none) ∧
    (0 < s.lifeOf ⟨0⟩ ∧ s.lifeOf ⟨1⟩ ≤ 0 → (checkHeroDefeat s).result = some (.won [⟨0⟩])) ∧
    (s.lifeOf ⟨0⟩ ≤ 0 ∧ 0 < s.lifeOf ⟨1⟩ → (checkHeroDefeat s).result = some (.won [⟨1⟩])) ∧
    (s.lifeOf ⟨0⟩ ≤ 0 ∧ s.lifeOf ⟨1⟩ ≤ 0 →
      (checkHeroDefeat s).result = some (.draw .simultaneousHeroDeath)) := by
  have hlp : livingPlayers s =
      ([⟨0⟩, ⟨1⟩] : List PlayerId).filter (fun p => decide (0 < s.lifeOf p)) := by
    unfold livingPlayers allPlayers
    rw [hp]
    rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨h0, h1⟩
    unfold checkHeroDefeat
    rw [hr, hlp]
    simp [h0, h1, hr]
  · rintro ⟨h0, h1⟩
    have hn1 : ¬ (0 < s.lifeOf ⟨1⟩) := by omega
    unfold checkHeroDefeat
    rw [hr, hlp]
    simp [h0, hn1]
  · rintro ⟨h0, h1⟩
    have hn0 : ¬ (0 < s.lifeOf ⟨0⟩) := by omega
    unfold checkHeroDefeat
    rw [hr, hlp]
    simp [hn0, h1]
  · rintro ⟨h0, h1⟩
    have hn0 : ¬ (0 < s.lifeOf ⟨0⟩) := by omega
    have hn1 : ¬ (0 < s.lifeOf ⟨1⟩) := by omega
    unfold checkHeroDefeat
    rw [hr, hlp]
    simp [hn0, hn1]

end Fab

end
