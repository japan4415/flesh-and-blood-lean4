module

public import Fab.Rules.CombatKeywords
public import Fab.Rules.Actions.Draw

/-!
# Advanced Mechanics: Chapter 8-9 (M8)

Implements Flesh and Blood's Chapter 8-9 advanced card and game mechanics:
1. **Double-Faced Cards**:
   - **Transcend** (CR 8.3.37): flip `.front → .back` and move to owner's hand preserving back face
     (enabling Chi pitching, e.g. Inner Chi).
   - **Transform** (CR 8.2): flip face in place in the Arena preserving exact `ObjId`.
   - **Demi-Hero** (CR 2.15.6e): identify Demi-Hero cards.
2. **Split / Meld Cards** (CR 8.3.38):
   - Play left half, right half, or both halves (Meld) with combined `AssetCost`, combined name,
     and right-before-left stack resolution order.
3. **Equipment Extensions**:
   - **Evo** (CR 8.3.28): equip Evo equipment on top of existing Base/Equipment in an armor slot
     while keeping underlying cards in the slot tail (`underlyingEquipment`).
   - **Modular** (CR 8.3.30): equip into any open armor slot.
   - **Cloaked** (CR 8.3.29): turn face-down Cloaked equipment face-up in the Arena preserving
     exact `ObjId`.
4. **Permanent Combat (Ally)**:
   - Ally identification, attack eligibility, `AttackTarget` (`hero`, `ally`, `spectra`), and
     damage routing (`damageAttackTarget`).
5. **Tap / Untap** (CR 8.2): `tapObject`, `untapObject`, `canPayTapCost`, `payTapCost`.
6. **Soul / Charge** (CR 3.9, 8.2): `putIntoSoul`, `chargeFromHand`, `soulCount`.
7. **Clash / Wager / Mark / Gold / Fealty** (CR 8.2, 8.5):
   - `resolveClash` (top-of-deck power comparison) (CR 8.5.39)
   - `WagerSpec` & `resolveWager` (prize token generation on hit) (CR 8.5.42)
   - `markPlayer` / `clearMark` / `isPlayerMarked` (CR 8.5.48)
   - `crackGold` (destroy Gold token + draw 1) & `crackFealty` (destroy Fealty + Draconic grant)
-/

@[expose] public section

namespace Fab

-- ---------------------------------------------------------------------------
-- 1. Double-Faced Cards: Transcend, Transform, Demi-Hero (CR 2.15.6e, 8.2, 8.3.37)
-- ---------------------------------------------------------------------------

/-- Flip a `FaceState` between `.front` and `.back`. -/
def FaceState.flip : FaceState → FaceState
  | .front => .back
  | .back => .front

/-- **Transcend** (CR 8.3.37): flip double-faced card `id` from `.front` to `.back` and move it to
its owner's hand, preserving `faceState = .back` on the newly created hand object so its back face
(e.g. Inner Chi) can be pitched for `{c}`. -/
def transcendCard (s : GameState) (id : ObjId) : Option (GameState × ObjId × List Event) :=
  match s.locate id, s.obj? id, s.cardDefOf? id with
  | some srcZ, some o, some c =>
    if c.back.isSome && o.faceState == .front then
      let sFlipped := updateSingleObject s id fun obj => { obj with faceState := .back }
      match moveObj sFlipped id (.player o.owner .hand) .top false with
      | some (s1, id') => some (s1, id', [.moved id id' srcZ (.player o.owner .hand)])
      | none => none
    else
      none
  | _, _, _ => none

/-- `transcendCard` preserves `WF`, `OwnerOk`, `physIds` (I1), `config`, and `playRollback`. -/
theorem transcendCard_inv {s s' : GameState} {id id' : ObjId} {es : List Event}
    (hwf : s.WF) (hok : s.OwnerOk) (h : transcendCard s id = some (s', id', es)) :
    s'.WF ∧ s'.OwnerOk ∧ s'.physIds.Perm s.physIds ∧
    s'.config = s.config ∧ s'.playRollback = s.playRollback := by
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
        · let f : Object → Object := fun obj => { obj with faceState := .back }
          have hwf1 := updateSingleObject_wf hwf id f
          have hok1 := updateSingleObject_ownerOk (f := f) hok id (fun _ => rfl)
          have hp1 := updateSingleObject_physIds (f := f) s id (fun _ => rfl)
          have hm1 := updateSingleObject_meta s id f
          cases hm : moveObj (updateSingleObject s id f)
              id (.player o.owner .hand) .top false with
          | none => rw [hm] at h; cases h
          | some res =>
            obtain ⟨s1, newId⟩ := res
            rw [hm] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, -⟩ := h
            have hmeta := moveObj_config_rollback hm
            exact ⟨moveObj_wf hwf1 hm, moveObj_ownerOk hwf1 hok1 hm,
                   (moveObj_physIds hwf1 hm).trans (by rw [hp1]),
                   hmeta.1.trans hm1.1, hmeta.2.trans hm1.2⟩
        · cases h

/-- **Transform** (CR 8.2): flip double-faced permanent `id` between `.front` and `.back` in place
in the Arena, preserving its exact `ObjId` and counters (CR 3.0.9). -/
def transformObject (s : GameState) (id : ObjId) : GameState :=
  match s.cardDefOf? id with
  | some c =>
    if c.back.isSome then
      updateSingleObject s id fun o => { o with faceState := o.faceState.flip }
    else
      s
  | none => s

/-- `transformObject` preserves `WF`, `OwnerOk`, `physIds` (I1), `config`, and `playRollback`. -/
theorem transformObject_inv {s : GameState} (hwf : s.WF) (hok : s.OwnerOk) (id : ObjId) :
    (transformObject s id).WF ∧ (transformObject s id).OwnerOk ∧
    (transformObject s id).physIds = s.physIds ∧
    (transformObject s id).config = s.config ∧
    (transformObject s id).playRollback = s.playRollback := by
  unfold transformObject
  cases s.cardDefOf? id with
  | none => exact ⟨hwf, hok, rfl, rfl, rfl⟩
  | some c =>
    dsimp only
    split
    · have hm := updateSingleObject_meta s id (fun o => { o with faceState := o.faceState.flip })
      exact ⟨updateSingleObject_wf hwf id _, updateSingleObject_ownerOk hok id (fun _ => rfl),
             updateSingleObject_physIds s id (fun _ => rfl), hm.1, hm.2⟩
    · exact ⟨hwf, hok, rfl, rfl, rfl⟩

/-- Whether object `id`'s currently active face is a **Demi-Hero** (CR 2.15.6e). -/
def isDemiHeroCard (s : GameState) (id : ObjId) : Bool :=
  match s.objectFace? id with
  | some face => face.hasType .demiHero
  | none => false

-- ---------------------------------------------------------------------------
-- 2. Split / Meld Cards (CR 8.3.38)
-- ---------------------------------------------------------------------------

/-- How a split card with **Meld** is played (CR 8.3.38). -/
inductive MeldMode where
  /-- Play only the left (primary/front) half. -/
  | left
  /-- Play only the right (`splitRight`) half. -/
  | right
  /-- Meld: pay combined cost to play both halves; right resolves first, then left (CR 8.3.38). -/
  | both
deriving DecidableEq, Repr, Hashable

/-- Whether card `c` supports Meld (has a `splitRight` face and `.meld` keyword) (CR 8.3.38). -/
def CardDef.canMeld (c : CardDef) : Bool :=
  c.splitRight.isSome && c.front.keywords.contains .meld

/-- Effective `AssetCost` of playing split/Meld card `c` in mode `m` (CR 8.3.38). -/
def meldEffectiveCost (c : CardDef) (m : MeldMode) : AssetCost :=
  let lCost := c.front.cost.getD {}
  let rCost := (c.splitRight.bind (·.cost)).getD {}
  match m with
  | .left => lCost
  | .right => rCost
  | .both =>
    { actionPoints := max lCost.actionPoints rCost.actionPoints
      resources := lCost.resources + rCost.resources
      chi := lCost.chi + rCost.chi }

/-- Effective name of split/Meld card `c` in mode `m` (CR 8.3.38). -/
def meldEffectiveName (c : CardDef) (m : MeldMode) : String :=
  match m with
  | .left => c.front.name
  | .right => (c.splitRight.map (·.name)).getD c.front.name
  | .both => c.front.name ++ " // " ++ (c.splitRight.map (·.name)).getD ""

/-- Resolution effects of split/Meld card `c` in mode `m`: when melded (`.both`), the **right**
half resolves before the **left** half (CR 8.3.38). -/
def meldResolveEffects (c : CardDef) (m : MeldMode) : List Effect :=
  let lEff := match c.front.playEffect with | some ed => ed.body | none => .nop
  let rEff := match c.splitRight.bind (·.playEffect) with | some ed => ed.body | none => .nop
  match m with
  | .left => [lEff]
  | .right => [rEff]
  | .both => [rEff, lEff]

-- ---------------------------------------------------------------------------
-- 3. Equipment Extensions: Evo, Modular, Cloaked (CR 8.3.28, 8.3.29, 8.3.30)
-- ---------------------------------------------------------------------------

/-- Map an `EquipSlot` to player `p`'s corresponding Arena equipment `Zone`. -/
def equipSlotZone (p : PlayerId) : EquipSlot → Zone
  | .head => .player p .head
  | .chest => .player p .chest
  | .arms => .player p .arms
  | .legs => .player p .legs

/-- Underlying equipment cards currently beneath the topmost Evo in `p`'s armor `slot`
(CR 8.3.28). -/
def underlyingEquipment (s : GameState) (p : PlayerId) (slot : EquipSlot) : List ObjId :=
  (s.zone (equipSlotZone p slot)).drop 1

/-- Whether card `c` is an **Evo** equipment card for `slot` (CR 8.3.28). -/
def isEvoForSlot (c : CardDef) (slot : EquipSlot) : Bool :=
  c.isEquipment &&
  (c.front.hasSubtype .evo || c.front.keywords.contains .evo) &&
  c.equipSlot? == some slot

/-- **Evo Equip** (CR 8.3.28): move Evo card `evoId` onto the `.top` of `p`'s armor `slot` zone
over an existing Base/Equipment card, preserving underlying cards in the zone tail. -/
def equipEvo (s : GameState) (p : PlayerId) (evoId : ObjId) (slot : EquipSlot) :
    Option (GameState × ObjId × List Event) :=
  let dst := equipSlotZone p slot
  match s.locate evoId, s.cardDefOf? evoId with
  | some srcZ, some c =>
    if isEvoForSlot c slot && !(s.zone dst).isEmpty then
      match moveObj s evoId dst .top false with
      | some (s1, id') => some (s1, id', [.moved evoId id' srcZ dst])
      | none => none
    else
      none
  | _, _ => none

/-- `equipEvo` preserves `WF`, `OwnerOk`, `physIds` (I1), `config`, and `playRollback`. -/
theorem equipEvo_inv {s s' : GameState} {p : PlayerId} {evoId id' : ObjId} {slot : EquipSlot}
    {es : List Event} (hwf : s.WF) (hok : s.OwnerOk)
    (h : equipEvo s p evoId slot = some (s', id', es)) :
    s'.WF ∧ s'.OwnerOk ∧ s'.physIds.Perm s.physIds ∧
    s'.config = s.config ∧ s'.playRollback = s.playRollback := by
  unfold equipEvo at h
  dsimp only at h
  cases hloc : s.locate evoId with
  | none => rw [hloc] at h; cases h
  | some srcZ =>
    cases hc : s.cardDefOf? evoId with
    | none => rw [hloc, hc] at h; cases h
    | some c =>
      rw [hloc, hc] at h
      dsimp only at h
      split at h
      · cases hm : moveObj s evoId (equipSlotZone p slot) .top false with
        | none => rw [hm] at h; cases h
        | some res =>
          obtain ⟨s1, newId⟩ := res
          rw [hm] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, -⟩ := h
          have hmeta := moveObj_config_rollback hm
          exact ⟨moveObj_wf hwf hm, moveObj_ownerOk hwf hok hm,
                 moveObj_physIds hwf hm, hmeta.1, hmeta.2⟩
      · cases h

/-- Whether card `c` is **Modular** equipment (can be equipped in any open armor slot)
(CR 8.3.30). -/
def isModularEquip (c : CardDef) : Bool :=
  c.isEquipment && c.front.keywords.contains .modular

/-- **Cloaked** turn face-up (CR 8.3.29): turn a face-down Cloaked equipment object face-up in
place in the Arena, preserving its exact `ObjId` (CR 3.0.9). -/
def turnEquipmentFaceUp (s : GameState) (id : ObjId) : GameState :=
  updateSingleObject s id fun o => { o with faceDown := false }

/-- `turnEquipmentFaceUp` preserves `WF`, `OwnerOk`, `physIds` (I1), `config`, and `playRollback`. -/
theorem turnEquipmentFaceUp_inv {s : GameState} (hwf : s.WF) (hok : s.OwnerOk) (id : ObjId) :
    (turnEquipmentFaceUp s id).WF ∧ (turnEquipmentFaceUp s id).OwnerOk ∧
    (turnEquipmentFaceUp s id).physIds = s.physIds ∧
    (turnEquipmentFaceUp s id).config = s.config ∧
    (turnEquipmentFaceUp s id).playRollback = s.playRollback := by
  unfold turnEquipmentFaceUp
  have hm := updateSingleObject_meta s id (fun o => { o with faceDown := false })
  exact ⟨updateSingleObject_wf hwf id _, updateSingleObject_ownerOk hok id (fun _ => rfl),
         updateSingleObject_physIds s id (fun _ => rfl), hm.1, hm.2⟩

-- ---------------------------------------------------------------------------
-- 4. Permanent Combat: Allies & Attack Targets (CR 2.5, 4.4.3a, 7.0)
-- ---------------------------------------------------------------------------

/-- Whether object `id` is an Ally permanent (CR 2.16). -/
def isAllyObj (s : GameState) (id : ObjId) : Bool :=
  match s.objectFace? id with
  | some face => face.hasSubtype .ally
  | none => false

/-- Whether player `p` can initiate an attack with Ally `allyId` in their permanent zone
(untapped, own Action Phase, empty stack, ≥1 AP) (CR 7.1, 8.2). -/
def canAttackWithAlly (s : GameState) (p : PlayerId) (allyId : ObjId) : Bool :=
  s.phase == .actionPhase &&
  s.active == some p &&
  (s.zone .stack).isEmpty &&
  1 ≤ (s.poolOf p).actionPoints &&
  (allyId ∈ s.zone (.player p .permanent)) &&
  isAllyObj s allyId &&
  match s.obj? allyId with
  | some o => !o.tapped && o.controller == p
  | none => false

/-- Valid combat attack targets in Flesh and Blood (CR 7.1, 8.3.14). -/
inductive AttackTarget where
  /-- Opposing Hero. -/
  | hero (p : PlayerId)
  /-- Living Ally permanent with its own life total. -/
  | ally (id : ObjId)
  /-- Permanent with Spectra (destroying it and closing the chain). -/
  | spectra (id : ObjId)
deriving DecidableEq, Repr

/-- Apply `dmg` combat damage to an `AttackTarget`, running GSP / hero defeat checks as needed
(CR 1.10.2, 7.5, 8.3.14). -/
def damageAttackTarget (s : GameState) (tgt : AttackTarget) (dmg : Nat) :
    GameState × List Event :=
  match tgt with
  | .hero p =>
    if dmg = 0 then (s, [])
    else
      let s1 := checkHeroDefeat (s.setLife p (s.lifeOf p - Int.ofNat dmg))
      (s1, [.damageDealt p .physical dmg])
  | .ally aid =>
    if dmg = 0 then (s, [])
    else
      let s1 := updateSingleObject s aid fun o =>
        { o with life := o.life.map (· - Int.ofNat dmg) }
      (gspRun s1, [])
  | .spectra sid =>
    applySpectraClose s sid

/-- `damageAttackTarget` preserves `WF`, `OwnerOk`, `physIds` (I1), `config`, and `playRollback`. -/
theorem damageAttackTarget_inv {s : GameState} (hwf : s.WF) (hok : s.OwnerOk)
    (tgt : AttackTarget) (dmg : Nat) :
    (damageAttackTarget s tgt dmg).1.WF ∧
    (damageAttackTarget s tgt dmg).1.OwnerOk ∧
    (damageAttackTarget s tgt dmg).1.physIds.Perm s.physIds ∧
    (damageAttackTarget s tgt dmg).1.config = s.config ∧
    (damageAttackTarget s tgt dmg).1.playRollback = s.playRollback := by
  cases tgt with
  | hero p =>
    unfold damageAttackTarget
    dsimp only
    split
    · exact ⟨hwf, hok, List.Perm.refl _, rfl, rfl⟩
    · have hwf1 : (s.setLife p (s.lifeOf p - Int.ofNat dmg)).WF :=
        GameState.WF.congr hwf rfl rfl rfl rfl
      have hok1 : (s.setLife p (s.lifeOf p - Int.ofNat dmg)).OwnerOk :=
        GameState.OwnerOk.congr hok rfl rfl
      have hm : (checkHeroDefeat (s.setLife p (s.lifeOf p - Int.ofNat dmg))).config = s.config ∧
          (checkHeroDefeat (s.setLife p (s.lifeOf p - Int.ofNat dmg))).playRollback = s.playRollback := by
        unfold checkHeroDefeat
        split
        · exact ⟨rfl, rfl⟩
        · cases livingPlayers _ with
          | nil => exact ⟨rfl, rfl⟩
          | cons _ ws => cases ws <;> exact ⟨rfl, rfl⟩
      exact ⟨checkHeroDefeat_wf hwf1, checkHeroDefeat_ownerOk hok1,
             by rw [checkHeroDefeat_physIds]; exact List.Perm.refl _, hm.1, hm.2⟩
  | ally aid =>
    unfold damageAttackTarget
    dsimp only
    split
    · exact ⟨hwf, hok, List.Perm.refl _, rfl, rfl⟩
    · let f : Object → Object := fun o => { o with life := o.life.map (· - Int.ofNat dmg) }
      have hwf1 := updateSingleObject_wf hwf aid f
      have hok1 := updateSingleObject_ownerOk (f := f) hok aid (fun _ => rfl)
      have hp1 := updateSingleObject_physIds (f := f) s aid (fun _ => rfl)
      have hm1 := updateSingleObject_meta s aid f
      have hmg := gspRun_meta (updateSingleObject s aid f)
      exact ⟨gspRun_wf hwf1, gspRun_ownerOk hwf1 hok1,
             (gspRun_physIds hwf1).trans (by rw [hp1]),
             hmg.1.trans hm1.1, hmg.2.trans hm1.2⟩
  | spectra sid =>
    exact applySpectraClose_inv hwf hok sid

-- ---------------------------------------------------------------------------
-- 5. Tap / Untap (CR 8.2)
-- ---------------------------------------------------------------------------

/-- Tap permanent `id` (`tapped := true`) (CR 8.2). -/
def tapObject (s : GameState) (id : ObjId) : GameState :=
  updateSingleObject s id fun o => { o with tapped := true }

/-- Untap permanent `id` (`tapped := false`) (CR 8.2). -/
def untapObject (s : GameState) (id : ObjId) : GameState :=
  updateSingleObject s id fun o => { o with tapped := false }

/-- Whether player `p` can pay a `{t}` (tap) cost using permanent `id`: must reside in an Arena
zone, be controlled by `p`, and be currently untapped (CR 8.2). -/
def canPayTapCost (s : GameState) (p : PlayerId) (id : ObjId) : Bool :=
  match s.locate id, s.obj? id with
  | some z, some o => z.isArena && o.controller == p && !o.tapped
  | _, _ => false

/-- Pay a `{t}` (tap) cost on permanent `id` for player `p` (CR 8.2). -/
def payTapCost (s : GameState) (p : PlayerId) (id : ObjId) : Option GameState :=
  if canPayTapCost s p id then some (tapObject s id) else none

/-- `tapObject` preserves `WF`, `OwnerOk`, `physIds` (I1), `config`, and `playRollback`. -/
theorem tapObject_inv {s : GameState} (hwf : s.WF) (hok : s.OwnerOk) (id : ObjId) :
    (tapObject s id).WF ∧ (tapObject s id).OwnerOk ∧
    (tapObject s id).physIds = s.physIds ∧
    (tapObject s id).config = s.config ∧
    (tapObject s id).playRollback = s.playRollback := by
  unfold tapObject
  have hm := updateSingleObject_meta s id (fun o => { o with tapped := true })
  exact ⟨updateSingleObject_wf hwf id _, updateSingleObject_ownerOk hok id (fun _ => rfl),
         updateSingleObject_physIds s id (fun _ => rfl), hm.1, hm.2⟩

/-- `untapObject` preserves `WF`, `OwnerOk`, `physIds` (I1), `config`, and `playRollback`. -/
theorem untapObject_inv {s : GameState} (hwf : s.WF) (hok : s.OwnerOk) (id : ObjId) :
    (untapObject s id).WF ∧ (untapObject s id).OwnerOk ∧
    (untapObject s id).physIds = s.physIds ∧
    (untapObject s id).config = s.config ∧
    (untapObject s id).playRollback = s.playRollback := by
  unfold untapObject
  have hm := updateSingleObject_meta s id (fun o => { o with tapped := false })
  exact ⟨updateSingleObject_wf hwf id _, updateSingleObject_ownerOk hok id (fun _ => rfl),
         updateSingleObject_physIds s id (fun _ => rfl), hm.1, hm.2⟩

-- ---------------------------------------------------------------------------
-- 6. Soul / Charge (CR 3.9, 8.2)
-- ---------------------------------------------------------------------------

/-- Number of cards currently in player `p`'s Soul sub-zone (CR 3.9). -/
def soulCount (s : GameState) (p : PlayerId) : Nat :=
  (s.zone (.player p .soul)).length

/-- Place card `id` face-up into player `p`'s Soul sub-zone (CR 3.9). -/
def putIntoSoul (s : GameState) (p : PlayerId) (id : ObjId) :
    Option (GameState × ObjId × List Event) :=
  match s.locate id with
  | none => none
  | some srcZ =>
    match moveObj s id (.player p .soul) .bottom false with
    | none => none
    | some (s1, id') => some (s1, id', [.moved id id' srcZ (.player p .soul)])

/-- **Charge** (CR 8.2): put card `id` from player `p`'s hand face-up into their Hero's Soul. -/
def chargeFromHand (s : GameState) (p : PlayerId) (id : ObjId) :
    Option (GameState × ObjId × List Event) :=
  if id ∈ s.zone (.player p .hand) then
    putIntoSoul s p id
  else
    none

/-- `putIntoSoul` preserves `WF`, `OwnerOk`, `physIds` (I1), `config`, and `playRollback`. -/
theorem putIntoSoul_inv {s s' : GameState} {p : PlayerId} {id id' : ObjId} {es : List Event}
    (hwf : s.WF) (hok : s.OwnerOk) (h : putIntoSoul s p id = some (s', id', es)) :
    s'.WF ∧ s'.OwnerOk ∧ s'.physIds.Perm s.physIds ∧
    s'.config = s.config ∧ s'.playRollback = s.playRollback := by
  unfold putIntoSoul at h
  cases hloc : s.locate id with
  | none => rw [hloc] at h; cases h
  | some srcZ =>
    rw [hloc] at h
    cases hm : moveObj s id (.player p .soul) .bottom false with
    | none => rw [hm] at h; cases h
    | some res =>
      obtain ⟨s1, newId⟩ := res
      rw [hm] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, -⟩ := h
      have hmeta := moveObj_config_rollback hm
      exact ⟨moveObj_wf hwf hm, moveObj_ownerOk hwf hok hm,
             moveObj_physIds hwf hm, hmeta.1, hmeta.2⟩

/-- `chargeFromHand` preserves `WF`, `OwnerOk`, `physIds` (I1), `config`, and `playRollback`. -/
theorem chargeFromHand_inv {s s' : GameState} {p : PlayerId} {id id' : ObjId} {es : List Event}
    (hwf : s.WF) (hok : s.OwnerOk) (h : chargeFromHand s p id = some (s', id', es)) :
    s'.WF ∧ s'.OwnerOk ∧ s'.physIds.Perm s.physIds ∧
    s'.config = s.config ∧ s'.playRollback = s.playRollback := by
  unfold chargeFromHand at h
  split at h
  · exact putIntoSoul_inv hwf hok h
  · cases h

-- ---------------------------------------------------------------------------
-- 7. Clash, Wager, Mark, Gold, Fealty (CR 8.2, 8.5)
-- ---------------------------------------------------------------------------

/-- Top-of-deck printed power `{p}` of player `p`'s deck for Clash (CR 8.5.39). -/
def topDeckPower? (s : GameState) (p : PlayerId) : Option Int :=
  match s.zone (.player p .deck) with
  | [] => none
  | topId :: _ => (s.objectFace? topId).bind (·.power)

/-- **Clash** (CR 8.5.39): compare the power `{p}` of the top card of `pA`'s and `pB`'s decks.
A card with power beats a card without power (or an empty deck); strictly higher power wins;
ties or neither having power yield `none`. -/
def resolveClash (s : GameState) (pA pB : PlayerId) : Option PlayerId :=
  match topDeckPower? s pA, topDeckPower? s pB with
  | some pa, some pb =>
    if pa > pb then some pA
    else if pb > pa then some pB
    else none
  | some _, none => some pA
  | none, some _ => some pB
  | none, none => none

/-- A **Wager** prize attached to an attack (CR 8.5.42). -/
structure WagerSpec where
  /-- Player who receives the wager prize if the attack hits. -/
  beneficiary : PlayerId
  /-- Token card ID awarded on hit (e.g. Gold, Might, Agility, Vigor). -/
  prizeToken : CardId
  /-- Number of tokens created on hit. -/
  prizeCount : Nat := 1
deriving DecidableEq, Repr

/-- Resolve a **Wager** once combat hit status is known (CR 8.5.42). -/
def resolveWager (s : GameState) (w : WagerSpec) (attackHit : Bool) : GameState :=
  if attackHit then createTokens s w.beneficiary w.prizeToken w.prizeCount else s

/-- `resolveWager` preserves `WF`, `OwnerOk`, `physIds` (I1), `config`, and `playRollback`. -/
theorem resolveWager_inv {s : GameState} (hwf : s.WF) (hok : s.OwnerOk)
    (w : WagerSpec) (hit : Bool) :
    (resolveWager s w hit).WF ∧ (resolveWager s w hit).OwnerOk ∧
    (resolveWager s w hit).physIds.Perm s.physIds ∧
    (resolveWager s w hit).config = s.config ∧
    (resolveWager s w hit).playRollback = s.playRollback := by
  unfold resolveWager
  split
  · have hm := createTokens_meta w.beneficiary w.prizeToken w.prizeCount s
    exact ⟨createTokens_wf w.beneficiary w.prizeToken w.prizeCount hwf,
           createTokens_ownerOk w.beneficiary w.prizeToken w.prizeCount hwf hok,
           createTokens_physIds w.beneficiary w.prizeToken w.prizeCount hwf,
           hm.1, hm.2⟩
  · exact ⟨hwf, hok, List.Perm.refl _, rfl, rfl⟩

/-- Whether player `p` is currently **Marked** (CR 8.5.48). -/
def isPlayerMarked (s : GameState) (p : PlayerId) : Bool :=
  s.markedPlayers.contains p

/-- Mark player `p` (idempotent) (CR 8.5.48). -/
def markPlayer (s : GameState) (p : PlayerId) : GameState :=
  if s.markedPlayers.contains p then s
  else { s with markedPlayers := p :: s.markedPlayers }

/-- Remove the Marked condition from player `p` (CR 8.5.48). -/
def clearMark (s : GameState) (p : PlayerId) : GameState :=
  { s with markedPlayers := s.markedPlayers.filter (· != p) }

/-- Canonical token ID for **Gold** tokens (CR 9). -/
def goldTokenId : CardId := ⟨"TOK_GOLD"⟩

/-- Canonical token ID for **Fealty** tokens (CR 9). -/
def fealtyTokenId : CardId := ⟨"TOK_FEALTY"⟩

/-- Crack a **Gold** token `tokId` controlled by `p`: destroys the Gold token and draws 1 card
(CR 9). -/
def crackGold (s : GameState) (p : PlayerId) (tokId : ObjId) : GameState × List Event :=
  let (s1, es1) := destroyObjToGraveyard s tokId
  let (s2, es2) := drawOne s1 p
  (s2, es1 ++ es2)

/-- `crackGold` preserves `WF`, `OwnerOk`, `physIds` (I1), `config`, and `playRollback`. -/
theorem crackGold_inv {s : GameState} (hwf : s.WF) (hok : s.OwnerOk)
    (p : PlayerId) (tokId : ObjId) :
    (crackGold s p tokId).1.WF ∧ (crackGold s p tokId).1.OwnerOk ∧
    (crackGold s p tokId).1.physIds.Perm s.physIds ∧
    (crackGold s p tokId).1.config = s.config ∧
    (crackGold s p tokId).1.playRollback = s.playRollback := by
  unfold crackGold
  obtain ⟨hwf1, hok1, hp1, hc1, hr1⟩ := destroyObjToGraveyard_inv hwf hok tokId
  have hd_meta := drawOne_meta (destroyObjToGraveyard s tokId).1 p
  exact ⟨drawOne_wf hwf1, drawOne_ownerOk hwf1 hok1,
         (drawOne_physIds hwf1).trans hp1,
         hd_meta.1.trans hc1, hd_meta.2.trans hr1⟩

/-- Crack a **Fealty** token `tokId` controlled by `p`: destroys the Fealty token and registers a
Stage 5 continuous effect granting `Supertype.talent .draconic` to `targetObj` for `.thisTurn`
(CR 6.3.2, 9). -/
def crackFealty (s : GameState) (p : PlayerId) (tokId targetObj : ObjId) :
    GameState × List Event :=
  let (s1, es1) := destroyObjToGraveyard s tokId
  let ce : ContinuousEffect :=
    { id := s1.nextTimestamp
      source := tokId
      controller := p
      target := .obj targetObj
      op := .addSupertype (.talent .draconic)
      duration := .thisTurn
      timestamp := ⟨s1.nextTimestamp⟩ }
  ({ s1 with
      activeEffects := s1.activeEffects ++ [ce]
      nextTimestamp := s1.nextTimestamp + 1 }, es1)

/-- `crackFealty` preserves `WF`, `OwnerOk`, `physIds` (I1), `config`, and `playRollback`. -/
theorem crackFealty_inv {s : GameState} (hwf : s.WF) (hok : s.OwnerOk)
    (p : PlayerId) (tokId targetObj : ObjId) :
    (crackFealty s p tokId targetObj).1.WF ∧ (crackFealty s p tokId targetObj).1.OwnerOk ∧
    (crackFealty s p tokId targetObj).1.physIds.Perm s.physIds ∧
    (crackFealty s p tokId targetObj).1.config = s.config ∧
    (crackFealty s p tokId targetObj).1.playRollback = s.playRollback := by
  unfold crackFealty
  obtain ⟨hwf1, hok1, hp1, hc1, hr1⟩ := destroyObjToGraveyard_inv hwf hok tokId
  exact ⟨GameState.WF.congr hwf1 rfl rfl rfl rfl,
         GameState.OwnerOk.congr hok1 rfl rfl,
         hp1, hc1, hr1⟩

end Fab

end
