module

import Fab
meta import Fab

/-!
# M6b Replacement, Arcane Prevention, Simultaneous Triggers, and Combat Keyword Tests

Regression tests covering official Flesh and Blood Release Notes rulings (CR 6.4-6.6, 8.3):
1. 4-stage replacement pipeline ordering (Stage A → B → C → D) & at-most-once rule (CR 6.4.5, 6.4.10)
2. Ward X mandatory self-destruction vs Arcane Barrier X optional arcane-only + Spellvoid + Quell
3. Simultaneous trigger stacking in 1v1 controlled by turn-player start choice (CR 6.6.6b)
4. Delayed trigger firing at End Phase (CR 6.6.3)
5. Combat keywords: Combo + LKI, Crush (3 vs 4 dmg), Reprise (hand vs equip), Phantasm (6{p}
   non-Illusionist vs 5{p} vs 6{p} Illusionist), Spectra forced close, Boost (Mechanologist vs
   non-Mechanologist), Blood Debt (face-up vs face-down at End Phase)
-/

namespace FabTest.Effects

open Fab

meta def p0 : PlayerId := ⟨0⟩
meta def p1 : PlayerId := ⟨1⟩

-- ---------------------------------------------------------------------------
-- 1. 4-Stage Replacement Pipeline & At-Most-Once (CR 6.4.5, 6.4.10)
-- ---------------------------------------------------------------------------

meta def stageOrderTest : Bool :=
  let effs : List ReplacementEffect :=
    [ { id := 10, source := ⟨1⟩, controller := p1, stage := .outcome,
        action := .replaceOutcome 7, optional := false }
    , { id := 20, source := ⟨2⟩, controller := p1, stage := .prevention,
        action := .shieldPrevent 3, optional := false }
    , { id := 30, source := ⟨3⟩, controller := p0, stage := .selfOrIdentity,
        action := .modifyDamage 2, optional := false } ]
  let init : ReplacementState := { event := .damage p1 .physical 4 }
  -- Stage A: 4 + 2 = 6; Stage C: 6 - 3 = 3; Stage D: outcomeTag = 7
  let res := applyReplacementPipeline [] effs init
  res.event == .damage p1 .physical 3 7 &&
  res.usedIds == [10, 20, 30]

#guard stageOrderTest == true

-- ---------------------------------------------------------------------------
-- 2. Release Notes: Ward (mandatory) vs Arcane Barrier (optional, arcane-only)
--    vs Spellvoid (arcane-only destroy) vs Quell (any damage + mark)
-- ---------------------------------------------------------------------------

meta def wardVsArcaneBarrierTest : Bool :=
  let wardEff : ReplacementEffect :=
    { id := 1, source := ⟨10⟩, controller := p1, stage := .prevention,
      action := .wardPrevent 2, optional := true } -- even if marked optional, Ward is mandatory!
  let abEff : ReplacementEffect :=
    { id := 2, source := ⟨11⟩, controller := p1, stage := .prevention,
      action := .arcaneBarrierPrevent 2, optional := true }
  -- Case 1: 3 arcane damage, player declines all optional effects ([]):
  -- Ward 2 STILL fires (mandatory), destroying ⟨10⟩ and reducing damage 3 -> 1; AB does not fire.
  let rDecline := applyReplacementPipeline [] [wardEff, abEff]
    { event := .damage p1 .arcane 3, availResources := 5 }
  -- Case 2: 3 arcane damage, player accepts AB first ([2]):
  -- AB 2 pays 2{r} (3 -> 1), then Ward 2 still fires (mandatory) destroying ⟨10⟩ (1 -> 0).
  let rAcceptAB := applyReplacementPipeline [2] [wardEff, abEff]
    { event := .damage p1 .arcane 3, availResources := 5 }
  -- Case 3: 3 physical damage, player tries to accept AB ([2]):
  -- AB ignores physical damage (0{r} paid); Ward 2 fires (3 -> 1).
  let rPhysical := applyReplacementPipeline [2] [wardEff, abEff]
    { event := .damage p1 .physical 3, availResources := 5 }
  rDecline.event == .damage p1 .arcane 1 &&
  rDecline.destroyedSources == [⟨10⟩] &&
  rDecline.resourcesPaid == 0 &&
  rAcceptAB.event == .damage p1 .arcane 0 &&
  rAcceptAB.resourcesPaid == 2 &&
  rAcceptAB.destroyedSources == [⟨10⟩] &&
  rPhysical.event == .damage p1 .physical 1 &&
  rPhysical.resourcesPaid == 0

#guard wardVsArcaneBarrierTest == true

meta def spellvoidAndQuellTest : Bool :=
  let sv : ReplacementEffect :=
    { id := 1, source := ⟨20⟩, controller := p1, stage := .prevention,
      action := .spellvoidPrevent 2, optional := true }
  let ql : ReplacementEffect :=
    { id := 2, source := ⟨21⟩, controller := p1, stage := .prevention,
      action := .quellPrevent 1, optional := true }
  -- Arcane 4: accept Spellvoid 2 then Quell 1 -> 4 - 2 - 1 = 1, ⟨20⟩ destroyed, ⟨21⟩ quellMarked, 1{r} paid.
  let rArc := applyReplacementPipeline [1, 2] [sv, ql]
    { event := .damage p1 .arcane 4, availResources := 3 }
  -- Physical 4: Spellvoid ignores physical, Quell 1 prevents 1 -> 3, 1{r} paid, ⟨21⟩ quellMarked.
  let rPhys := applyReplacementPipeline [1, 2] [sv, ql]
    { event := .damage p1 .physical 4, availResources := 3 }
  rArc.event == .damage p1 .arcane 1 &&
  rArc.destroyedSources == [⟨20⟩] &&
  rArc.quellMarked == [⟨21⟩] &&
  rArc.resourcesPaid == 1 &&
  rPhys.event == .damage p1 .physical 3 &&
  rPhys.destroyedSources == [] &&
  rPhys.quellMarked == [⟨21⟩]

#guard spellvoidAndQuellTest == true

-- ---------------------------------------------------------------------------
-- 3. Simultaneous Trigger Stacking in 1v1 via `step` (CR 6.6.6b, I19)
-- ---------------------------------------------------------------------------

meta def dummyLki (p : PlayerId) (nm : String) : LkiSnapshot :=
  { cardId := none, name := nm, owner := p, controller := p }

meta def simultaneousTrigger1v1Test : Bool :=
  let sBase : GameState :=
    { config := { format := .classicConstructed, mode := .duel, ruleSet := .coreOnly }
      cards := CardDB.empty
      turnOrder := [p0, p1]
      active := some p0
      phase := .actionPhase
      pending := [.flushTriggers]
      pendingTriggers :=
        [ { id := 100, source := ⟨1⟩, sourceLki := dummyLki p0 "P0 Trig",
            controller := p0, effect := .prim (.gainLife .controller (.const 1)) }
        , { id := 200, source := ⟨2⟩, sourceLki := dummyLki p1 "P1 Trig",
            controller := p1, effect := .prim (.gainLife .controller (.const 2)) } ] }
  -- Advance flushTriggers -> chooseTriggerStart p0
  match advance 10 sBase [] with
  | .error _ => false
  | .ok (sPrompt, _) =>
    -- Branch A: P0 chooses start = p0 -> P0 stacks first, then P1 stacks on top (P1 resolves first!)
    let branchA :=
      match step 10 sPrompt ⟨.player p0, .pickTriggerStart p0⟩ with
      | .ok (s1, _) =>
        match step 10 s1 ⟨.player p0, .pickTrigger 100⟩ with
        | .ok (s2, _) =>
          match step 10 s2 ⟨.player p1, .pickTrigger 200⟩ with
          | .ok (s3, _) =>
            match s3.zone .stack with
            | [topId, botId] =>
              (s3.layerMeta.getD topId.n { controller := p0 }).controller == p1 &&
              (s3.layerMeta.getD botId.n { controller := p1 }).controller == p0
            | _ => false
          | .error _ => false
        | .error _ => false
      | .error _ => false
    -- Branch B: P0 chooses start = p1 -> P1 stacks first, then P0 stacks on top (P0 resolves first!)
    let branchB :=
      match step 10 sPrompt ⟨.player p0, .pickTriggerStart p1⟩ with
      | .ok (s1, _) =>
        match step 10 s1 ⟨.player p1, .pickTrigger 200⟩ with
        | .ok (s2, _) =>
          match step 10 s2 ⟨.player p0, .pickTrigger 100⟩ with
          | .ok (s3, _) =>
            match s3.zone .stack with
            | [topId, botId] =>
              (s3.layerMeta.getD topId.n { controller := p1 }).controller == p0 &&
              (s3.layerMeta.getD botId.n { controller := p0 }).controller == p1
            | _ => false
          | .error _ => false
        | .error _ => false
      | .error _ => false
    branchA && branchB

#guard simultaneousTrigger1v1Test == true

-- ---------------------------------------------------------------------------
-- 4. Combat Keywords: Combo + LKI, Crush, Reprise, Phantasm, Spectra, Boost, Blood Debt
-- ---------------------------------------------------------------------------

meta def mkTestCard (cid : String) (nm : String) (st : List Supertype) (ts : List CardType)
    (subs : List Subtype) (pow : Option Int) (defV : Option Int) (kws : List KeywordInst) : CardDef :=
  { id := ⟨cid⟩
    front :=
      { name := nm
        supertypes := st
        types := ts
        subtypes := subs
        power := pow
        defense := defV
        keywords := kws } }

meta def phantasmCard : CardDef :=
  mkTestCard "PH-1" "Herald of Erudition" [.class_ .illusionist] [.action] [.attack] (some 5) (some 3) [.phantasm]

meta def brute6Def : CardDef :=
  mkTestCard "BR-6" "Savage Feast" [.class_ .brute] [.action] [.attack] (some 6) (some 3) []

meta def brute5Def : CardDef :=
  mkTestCard "BR-5" "Pack Hunt" [.class_ .brute] [.action] [.attack] (some 5) (some 3) []

meta def illusionist6Def : CardDef :=
  mkTestCard "IL-6" "Phantasmaclasm" [.class_ .illusionist] [.action] [.attack] (some 6) (some 3) [.phantasm]

meta def spectraAuraDef : CardDef :=
  mkTestCard "SP-1" "Merciful Retribution" [.class_ .illusionist] [.instant] [.aura] none none [.spectra]

meta def mechCardDef : CardDef :=
  mkTestCard "ME-1" "Zero to Sixty" [.class_ .mechanologist] [.action] [.attack] (some 4) (some 2) [.boost]

meta def genericCardDef : CardDef :=
  mkTestCard "GE-1" "Sink Below" [.generic] [.defenseReaction] [] none (some 4) []

meta def bloodDebtCardDef : CardDef :=
  mkTestCard "BD-1" "Shadow Puppetry" [.talent .shadow] [.instant] [] none (some 3) [.bloodDebt]

meta def testDB : CardDB :=
  ⟨[phantasmCard, brute6Def, brute5Def, illusionist6Def, spectraAuraDef,
    mechCardDef, genericCardDef, bloodDebtCardDef]⟩

meta def combatKeywordsTest : Bool :=
  let cfg : GameConfig := { format := .classicConstructed, mode := .duel, ruleSet := .coreOnly }
  let s0 : GameState :=
    { config := cfg, cards := testDB, turnOrder := [p0, p1], active := some p0,
      heroLife := ((∅ : Std.ExtTreeMap Nat Int).insert 0 20).insert 1 20 }
  -- Add objects for Phantasm test
  match addObject s0 .combatChain { kind := .card ⟨1⟩ ⟨"PH-1"⟩, owner := p0, controller := p0, timestamp := ⟨0⟩ } .top with
  | none => false
  | some (s1, phId) =>
    match addObject s1 .combatChain { kind := .card ⟨2⟩ ⟨"BR-6"⟩, owner := p1, controller := p1, timestamp := ⟨1⟩ } .top with
    | none => false
    | some (s2, br6Id) =>
      match addObject s2 .combatChain { kind := .card ⟨3⟩ ⟨"BR-5"⟩, owner := p1, controller := p1, timestamp := ⟨2⟩ } .top with
      | none => false
      | some (s3, br5Id) =>
        match addObject s3 .combatChain { kind := .card ⟨4⟩ ⟨"IL-6"⟩, owner := p1, controller := p1, timestamp := ⟨3⟩ } .top with
        | none => false
        | some (s4, il6Id) =>
          let mkLink (defs : List ObjId) (dmg : Nat) (fromH : Nat) : ChainLink :=
            { linkId := ⟨2⟩, attacker := p0, defender := p1, attack := some phId,
              attackLki := captureLki s4 phId p0, defending := defs,
              damageDealt := dmg, defendedFromHandCount := fromH }
          let prevLink : ChainLink :=
            { linkId := ⟨1⟩, attacker := p0, defender := p1, attack := none, -- left chain!
              attackLki := { cardId := some ⟨"WTR081"⟩, name := "Surging Strike",
                             owner := p0, controller := p0 } }
          let linkPop := mkLink [br6Id] 4 1
          let linkFive := mkLink [br5Id] 3 0
          let linkIll := mkLink [il6Id] 0 1
          let sWithCC := { s4 with combat := some { step := .defend, links := [linkPop, prevLink] } }
          let (sPopped, _) := applyPhantasmClose sWithCC
          -- Check Phantasm, Combo+LKI, Crush, Reprise
          phantasmTriggered sWithCC linkPop == true &&
          phantasmTriggered sWithCC linkFive == false &&
          phantasmTriggered sWithCC linkIll == false &&
          sPopped.combat.isNone == true &&
          !(sPopped.zone (.player p0 .graveyard)).isEmpty &&
          comboActive sWithCC ["Surging Strike"] == true &&
          comboActive sWithCC ["Whelming Gustwave"] == false &&
          crushTriggered linkPop == true &&
          crushTriggered linkFive == false &&
          repriseActive linkPop == true &&
          repriseActive linkFive == false

#guard combatKeywordsTest == true

meta def spectraBoostBloodDebtTest : Bool :=
  let cfg : GameConfig := { format := .classicConstructed, mode := .duel, ruleSet := .coreOnly }
  let s0 : GameState :=
    { config := cfg, cards := testDB, turnOrder := [p0, p1], active := some p0,
      heroLife := ((∅ : Std.ExtTreeMap Nat Int).insert 0 20).insert 1 20 }
  -- Spectra aura on p1's permanent zone + open combat chain
  match addObject s0 (.player p1 .permanent)
      { kind := .card ⟨10⟩ ⟨"SP-1"⟩, owner := p1, controller := p1, timestamp := ⟨0⟩ } .top with
  | none => false
  | some (s1, spId) =>
    let dummyLink : ChainLink :=
      { linkId := ⟨1⟩, attacker := p0, defender := p1, attack := none,
        attackLki := dummyLki p0 "Attack" }
    let sSpec := { s1 with combat := some { step := .attack, links := [dummyLink] } }
    let (sSpecDone, _) := applySpectraClose sSpec spId
    let specOk := sSpecDone.combat.isNone && (sSpecDone.zone (.player p1 .graveyard)).length == 1
    -- Boost test: Mechanologist card on top of deck grants Go Again; Generic card does not
    match addObject sSpec (.player p0 .deck)
        { kind := .card ⟨11⟩ ⟨"ME-1"⟩, owner := p0, controller := p0, timestamp := ⟨1⟩ } .top with
    | none => false
    | some (sB1, _) =>
      let (sB1Done, boosted1, _) := applyBoost sB1 p0
      let boostMechOk := boosted1 == true &&
        match sB1Done.combat.bind CombatChain.activeLink? with
        | some l => l.grantedKeywords.contains .goAgain
        | none => false
      match addObject sSpec (.player p0 .deck)
          { kind := .card ⟨12⟩ ⟨"GE-1"⟩, owner := p0, controller := p0, timestamp := ⟨2⟩ } .top with
      | none => false
      | some (sB2, _) =>
        let (sB2Done, boosted2, _) := applyBoost sB2 p0
        let boostGenOk := boosted2 == false &&
          match sB2Done.combat.bind CombatChain.activeLink? with
          | some l => !(l.grantedKeywords.contains .goAgain)
          | none => false
        -- Blood Debt test: 1 face-up + 1 face-down Blood Debt in p0's banished zone -> only 1 life lost at End Phase!
        match addObject s0 (.player p0 .banished)
            { kind := .card ⟨13⟩ ⟨"BD-1"⟩, owner := p0, controller := p0, faceDown := false, timestamp := ⟨3⟩ } .top with
        | none => false
        | some (sD1, _) =>
          match addObject sD1 (.player p0 .banished)
              { kind := .card ⟨14⟩ ⟨"BD-1"⟩, owner := p0, controller := p0, faceDown := true, timestamp := ⟨4⟩ } .top with
          | none => false
          | some (sD2, _) =>
            let sEnd := { sD2 with pending := [.endPhaseStart p0] }
            match microStep sEnd with
            | some (sAfterEnd, es) =>
              let bdOk := bloodDebtCount sD2 p0 == 1 &&
                sAfterEnd.lifeOf p0 == 19 &&
                es == [.lifeLost p0 1]
              specOk && boostMechOk && boostGenOk && bdOk
            | none => false

#guard spectraBoostBloodDebtTest == true

end FabTest.Effects
