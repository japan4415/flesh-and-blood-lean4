module

public import Fab.Invariant.Step

/-!
# Combat Chain, LKI, Equipment Wear, and GSP invariants (M5)

Proves M5 theorems from `docs/roadmap.md`:
- **I11** (Combat Chain 7-step progression, Go Again +1 AP via live/LKI, Battleworn identical
  `ObjId` return & counter, Blade Break destruction, Dominate/Overpower hooks):
  `combatStep_chain_order`, `resolutionStep_grants_goAgain_lki`, `battleworn_preserves_objId`,
  `bladeBreak_destroys`, `dominate_blocks_second_hand_card`, `overpower_blocks_second_action`
- **I12a & I17** (GSP termination and fixed-point `Settled` before priority):
  `gameStateProcess_fixed_point`
- **I5** (Progress on `defendPick`): `progress_defendPick`
-/

@[expose] public section

namespace Fab

/-- **I11** (7-step progression): `CombatStep.next?` traverses strictly through all 7 steps
Layer → Attack → Defend → Reaction → Damage → Resolution → Close (CR 7.1-7.7). -/
theorem combatStep_chain_order :
    CombatStep.layer.next? = some .attack ∧
    CombatStep.attack.next? = some .defend ∧
    CombatStep.defend.next? = some .reaction ∧
    CombatStep.reaction.next? = some .damage ∧
    CombatStep.damage.next? = some .resolution ∧
    CombatStep.resolution.next? = some .close ∧
    CombatStep.close.next? = none := by
  decide

/-- **I11** (Go Again via LKI at Resolution Step) (CR 3.5.4b, 7.6.2): even when `link.attack = none`
(for example, after *Endless Arrow* or *Hurricane Technique* left the combat chain), if
`link.attackLki` had `Go Again`, it is allowed, and `goAgainGranted = false`, Resolution Step grants the attacker
exact +1 AP. -/
theorem resolutionStep_grants_goAgain_lki {s s' : GameState} {atkId : ObjId} {rest : List Frame}
    {cc : CombatChain} {link : ChainLink} {older : List ChainLink} {es : List Event}
    (hp : s.pending = .combatStep .resolution atkId :: rest)
    (hcc : s.combat = some cc)
    (hlinks : cc.links = link :: older)
    (hga : link.attackLki.keywords.contains .goAgain = true)
    (hallowed : s.hasActionPhaseEffect link.attacker .cantGainGoAgain = false)
    (hnot : link.goAgainGranted = false)
    (hm : microStep s = some (s', es)) :
    (s'.poolOf link.attacker).actionPoints = (s.poolOf link.attacker).actionPoints + 1 := by
  have hhas : linkHasKeyword s link .goAgain = true := by
    unfold linkHasKeyword
    rw [hga]
    simp [hallowed]
  unfold microStep at hm
  rw [hp] at hm
  dsimp only at hm
  rw [hcc] at hm
  simp only [CombatChain.activeLink?, hlinks, List.head?_cons, hhas, hnot, Bool.not_false,
    Bool.and_self, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hm
  obtain ⟨rfl, -⟩ := hm
  simp only [GameState.poolOf, GameState.setPool, Std.ExtTreeMap.getD_insert_self,
    AssetPool.addActionPoints]

/-- **I11** (Battleworn identical `ObjId` return and `-1{d}` counter) (CR 3.0.9, 7.7, 8.3.2):
a Battleworn equipment card on `Zone.combatChain` (without Blade Break or Temper) returns to its
armor zone on Close Step with the **exact same `ObjId`** and `minusDefenseCounters + 1`. -/
theorem battleworn_preserves_objId {s : GameState} {id : ObjId} {o : Object} {c : CardDef}
    {slot : EquipSlot}
    (hloc : s.locate id = some .combatChain)
    (ho : s.obj? id = some o)
    (hc : s.cardDefOf? id = some c)
    (hslot : c.equipSlot? = some slot)
    (hown : o.owner.n < s.playerCount)
    (hnbb : c.front.keywords.contains .bladeBreak = false)
    (hntemp : c.front.keywords.contains .temper = false)
    (hbw : c.front.keywords.contains .battleworn = true) :
    let dst : Zone :=
      match slot with
      | .head => .player o.owner .head
      | .chest => .player o.owner .chest
      | .arms => .player o.owner .arms
      | .legs => .player o.owner .legs
    let (s', es) := applyEquipmentWear s id
    id ∈ s'.zone dst ∧
    es = [.moved id id .combatChain dst] ∧
    (s'.obj? id).map (·.minusDefenseCounters) = some (o.minusDefenseCounters + 1) := by
  unfold applyEquipmentWear
  rw [ho, hc]
  dsimp only
  simp only [hslot, hnbb, hntemp, hbw, Bool.false_eq_true, ↓reduceIte]
  let dst : Zone :=
    match slot with
    | .head => .player o.owner .head
    | .chest => .player o.owner .chest
    | .arms => .player o.owner .arms
    | .legs => .player o.owner .legs
  let s1 := updateSingleObject s id fun obj => obj.addCounterVal .minusOneDefense 1
  have ho_raw : s.objects[id.n]? = some o := ho
  have hs1_eq : s1 = { s with objects := s.objects.insert id.n (o.addCounterVal .minusOneDefense 1) } := by
    unfold s1 updateSingleObject
    rw [ho_raw]
  have hloc1 : s1.locate id = some .combatChain := by
    rw [hs1_eq]; exact hloc
  have ho1 : s1.obj? id = some (o.addCounterVal .minusOneDefense 1) := by
    rw [hs1_eq]
    simp [GameState.obj?]
  have hdst_arena : dst.isArena = true := by cases slot <;> rfl
  have hdst_valid : dst.Valid s1.playerCount := by
    have hc1 : s1.playerCount = s.playerCount := by rw [hs1_eq]; rfl
    rw [hc1]
    cases slot <;> exact Zone.valid_player hown _
  have hnorm : Zone.normalize (o.addCounterVal .minusOneDefense 1).owner dst = dst := by
    cases slot <;> rfl
  have hne : Zone.combatChain ≠ dst := by
    dsimp only [dst]
    cases slot <;> (intro h; cases h)
  have hnot_cross : Zone.crosses .combatChain dst = false := by
    unfold Zone.crosses
    rw [hdst_arena]
    rfl
  have hmove : moveObj s1 id dst .top false =
      some ((s1.setZone .combatChain ((s1.zone .combatChain).erase id)).setZone dst
        (id :: s1.zone dst), id) := by
    unfold moveObj
    rw [hloc1, ho1]
    dsimp only
    rw [hnorm]
    simp only [hne, false_or, hdst_valid, not_true_eq_false, ↓reduceIte, hnot_cross,
      Bool.false_eq_true, Pos.insert]
  cases slot <;> (
    dsimp only [dst] at hmove ⊢
    change id ∈ (match moveObj s1 id _ .top false with
        | some (s2, id') => (s2, [Event.moved id id' .combatChain _])
        | none => (s1, [])).1.zone _ ∧ _
    rw [hmove]
    dsimp only
    refine ⟨by simp [GameState.zone_setZone_self], rfl, ?_⟩
    change (s1.obj? id).map (·.minusDefenseCounters) = some (o.minusDefenseCounters + 1)
    rw [ho1]
    rfl
  )

/-- **I11** (Blade Break destruction) (CR 7.7, 8.3.3): a Blade Break equipment card on
`Zone.combatChain` moves to its owner's graveyard on Close Step. -/
theorem bladeBreak_destroys {s : GameState} {id : ObjId} {o : Object} {c : CardDef}
    (hloc : s.locate id = some .combatChain)
    (ho : s.obj? id = some o)
    (hc : s.cardDefOf? id = some c)
    (hown : o.owner.n < s.playerCount)
    (hbb : c.front.keywords.contains .bladeBreak = true) :
    let (s', _) := applyEquipmentWear s id
    (s'.zone (.player o.owner .graveyard)).length = (s.zone (.player o.owner .graveyard)).length + 1 := by
  unfold applyEquipmentWear
  rw [ho, hc]
  dsimp only
  rw [hbb]
  simp only [↓reduceIte]
  have hval : (Zone.player o.owner .graveyard).Valid s.playerCount :=
    Zone.valid_player hown .graveyard
  have hnorm : Zone.normalize o.owner (.player o.owner .graveyard) = .player o.owner .graveyard := by
    simp [Zone.normalize, ZoneKind.isArena]
  have hne : Zone.combatChain ≠ .player o.owner .graveyard := by intro h; cases h
  have hcross : Zone.crosses .combatChain (.player o.owner .graveyard) = true := rfl
  have hm : moveObj s id (.player o.owner .graveyard) .top false =
      some ({ (s.setZone .combatChain ((s.zone .combatChain).erase id)).setZone
                (.player o.owner .graveyard) (⟨s.nextId⟩ :: s.zone (.player o.owner .graveyard)) with
              objects := (s.objects.erase id.n).insert s.nextId (o.resetOnZoneChange ⟨s.nextTimestamp⟩ false)
              nextId := s.nextId + 1
              nextTimestamp := s.nextTimestamp + 1 }, ⟨s.nextId⟩) := by
    unfold moveObj
    rw [hloc, ho]
    dsimp only
    rw [hnorm]
    simp only [hne, false_or, hval, not_true_eq_false, ↓reduceIte, hcross, Pos.insert]
  rw [hm]
  dsimp only
  have hz : ({ (s.setZone .combatChain ((s.zone .combatChain).erase id)).setZone
      (.player o.owner .graveyard) (⟨s.nextId⟩ :: s.zone (.player o.owner .graveyard)) with
      objects := (s.objects.erase id.n).insert s.nextId (o.resetOnZoneChange ⟨s.nextTimestamp⟩ false)
      nextId := s.nextId + 1
      nextTimestamp := s.nextTimestamp + 1 }).zone (.player o.owner .graveyard) =
      ⟨s.nextId⟩ :: s.zone (.player o.owner .graveyard) := by
    simp [GameState.zone, GameState.setZone]
  rw [hz]
  rfl

/-- **I11** (Dominate defense hook) (CR 8.3.4): once a Dominate attack has been defended by at least
1 card from hand, no further card from hand may be declared in Defend Step. -/
theorem dominate_blocks_second_hand_card {s : GameState} {link : ChainLink}
    {p : PlayerId} {id : ObjId}
    (hhand : id ∈ s.zone (.player p .hand))
    (hdom : linkHasKeyword s link .dominate = true)
    (hcnt : 1 ≤ link.defendedFromHandCount) :
    canDefendWith s link p id = false := by
  unfold canDefendWith
  split
  · rfl
  · dsimp only
    simp only [hhand, decide_true, Bool.true_or, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    cases s.objectFace? id with
    | none => rfl
    | some face =>
      dsimp only
      split
      · rfl
      · simp [hdom, hcnt]

/-- **I11** (Overpower defense hook) (CR 8.3.26): once an Overpower attack has been defended by at
least 1 action card, no further action card may be declared in Defend Step. -/
theorem overpower_blocks_second_action {s : GameState} {link : ChainLink}
    {p : PlayerId} {id : ObjId} {face : CardFace}
    (hface : s.objectFace? id = some face)
    (hact : face.hasType .action = true)
    (hov : linkHasKeyword s link .overpower = true)
    (hcnt : 1 ≤ link.defendedActionCount) :
    canDefendWith s link p id = false := by
  unfold canDefendWith
  split
  · rfl
  · dsimp only
    split
    · rfl
    · rw [hface]
      dsimp only
      split
      · rfl
      · split
        · rfl
        · simp [hact, hov, hcnt]

/-- **I12a + I17**: stepping a `.gameStateProcess` frame always reaches a GSP fixed point
(`gspStep s' = none`). -/
theorem gameStateProcess_fixed_point {s s' : GameState} {rest : List Frame} {es : List Event}
    (hwf : s.WF)
    (hp : s.pending = .gameStateProcess :: rest)
    (hm : microStep s = some (s', es)) :
    gspStep s' = none := by
  unfold microStep at hm
  rw [hp] at hm
  simp only [Option.some.injEq, Prod.mk.injEq] at hm
  obtain ⟨rfl, -⟩ := hm
  have hfp := gspRun_fixed_point hwf
  generalize gspRun s = t at hfp ⊢
  have hcd : (checkHeroDefeat { t with pending := rest }).result = (checkHeroDefeat t).result := by
    have hlp : livingPlayers { t with pending := rest } = livingPlayers t := rfl
    unfold checkHeroDefeat
    dsimp only
    rw [hlp]
    split
    · rfl
    · cases livingPlayers t with
      | nil => rfl
      | cons _ ws => cases ws <;> rfl
  unfold gspStep at hfp ⊢
  rw [hcd]
  change (if t.result.isNone && (checkHeroDefeat t).result.isSome then _ else _) = none
  split at hfp
  · cases hfp
  · rename_i hnd
    simp only [hnd]
    change (match nonArenaNonPhys t with
      | id :: _ => some (removeNonPhysObj { t with pending := rest } id)
      | [] =>
        match gspPermanentsToClear t with
        | id :: _ =>
          match t.obj? id with
          | some o =>
            if o.kind.phys?.isNone then some (removeNonPhysObj { t with pending := rest } id)
            else
              match moveObj { t with pending := rest } id (.player o.owner .graveyard) .top false with
              | some (s', _) => some s'
              | none => none
          | none => none
        | [] => none) = none
    cases hna : nonArenaNonPhys t with
    | cons _ _ => rw [hna] at hfp; cases hfp
    | nil =>
      rw [hna] at hfp
      dsimp only at hfp ⊢
      cases hda : gspPermanentsToClear t with
      | nil => rfl
      | cons id _ =>
        rw [hda] at hfp
        dsimp only at hfp ⊢
        cases ho : t.obj? id with
        | none => rfl
        | some o =>
          rw [ho] at hfp
          dsimp only at hfp ⊢
          split at hfp
          · cases hfp
          · rename_i hphys
            simp only [hphys]
            have hm_none : moveObj t id (.player o.owner .graveyard) .top false = none := by
              cases hmt : moveObj t id (.player o.owner .graveyard) .top false with
              | none => rfl
              | some _ => rw [hmt] at hfp; cases hfp
            have hm_eq : (moveObj { t with pending := rest } id (.player o.owner .graveyard) .top false).isNone =
                (moveObj t id (.player o.owner .graveyard) .top false).isNone := by
              unfold moveObj
              have hloc' : ({ t with pending := rest }).locate id = t.locate id := rfl
              have ho' : ({ t with pending := rest }).obj? id = t.obj? id := rfl
              have hpc' : ({ t with pending := rest }).playerCount = t.playerCount := rfl
              rw [hloc', ho']
              cases t.locate id with
              | none => rfl
              | some src =>
                cases t.obj? id with
                | none => rfl
                | some obj =>
                  dsimp only
                  rw [hpc']
                  by_cases hbad : src = Zone.normalize obj.owner (.player o.owner .graveyard) ∨
                      ¬(Zone.normalize obj.owner (.player o.owner .graveyard)).Valid t.playerCount
                  · simp [hbad]
                  · simp only [hbad, ↓reduceIte]
                    split <;> rfl
            rw [hm_none] at hm_eq
            cases hm : moveObj { t with pending := rest } id (.player o.owner .graveyard) .top false with
            | none => rfl
            | some _ => rw [hm] at hm_eq; simp at hm_eq

/-- **I5** (Progress on `defendPick`): `defendDone` is always a legal non-concede action. -/
theorem progress_defendPick {s : GameState} {defender : PlayerId} {rest : List Frame}
    (hres : s.result = none)
    (hp : s.pending = .defendPick defender :: rest) :
    ∃ a ∈ legalActions s, a.kind ≠ .concede := by
  refine ⟨⟨.player defender, .defendDone⟩, ?_, by simp⟩
  rw [legalActions_iff]
  exact ⟨⟨hres, Or.inl (by simp [LegalFrame, hp])⟩, rfl⟩

end Fab

end
