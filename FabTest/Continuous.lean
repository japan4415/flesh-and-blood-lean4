module

import Fab
import FabCards
meta import Fab
meta import FabCards

/-!
# Tests: M6a 8-Stage Continuous Effects, Dependency, Cycle Fallback, I12c, and Asset Cost L5
-/

open Fab
open FabCards

meta def testObj : Object :=
  { kind := .card ⟨0⟩ ⟨"WTR_203_R"⟩
    owner := ⟨0⟩
    controller := ⟨0⟩
    minusDefenseCounters := 1
    plusPowerCounters := 1
    timestamp := ⟨0⟩ }

meta def testFace : CardFace :=
  { name := "Wounding Blow"
    supertypes := [.generic]
    types := [.action]
    subtypes := [.attack]
    color := some .red
    pitch := some 1
    cost := some { actionPoints := 1, resources := 2 }
    power := some 4
    defense := some 3 }

-- 1. All 8 stages in strict CR 6.3.2 order + counters (Stage 1 -> 8 -> Counters):
--    - Stage 2: change controller to P1
--    - Stage 3: rename to "Mimicked Strike"
--    - Stage 4: add subtype .arrow
--    - Stage 5: add supertype .class .ranger
--    - Stage 6: grant Go Again (add) then lose Dominate (sub)
--    - Stage 7: set base power to 5 (even with later timestamp 99!)
--    - Stage 8: mulPower 2 (mulDiv, ts=50), addPower 3 (add, ts=1), subPower 1 (sub, ts=2)
--    - Counters: +1{p} counter and -1{d} counter
--    Expected power: (5 * 2 + 3 - 1) + 1 = 13; defense: 3 - 1 = 2; totalSteps = 9 (I12c)!
#guard
  let oid : ObjId := ⟨42⟩
  let effs : List ContinuousEffect :=
    [ { id := 1, source := oid, controller := ⟨0⟩, target := .obj oid, op := .addPower 3, timestamp := ⟨1⟩ }
    , { id := 2, source := oid, controller := ⟨0⟩, target := .obj oid, op := .subPower 1, timestamp := ⟨2⟩ }
    , { id := 3, source := oid, controller := ⟨0⟩, target := .obj oid, op := .mulPower 2, timestamp := ⟨50⟩ }
    , { id := 4, source := oid, controller := ⟨0⟩, target := .obj oid, op := .setBasePower 5, timestamp := ⟨99⟩ }
    , { id := 5, source := oid, controller := ⟨0⟩, target := .obj oid, op := .setController ⟨1⟩, timestamp := ⟨10⟩ }
    , { id := 6, source := oid, controller := ⟨0⟩, target := .obj oid, op := .setName "Mimicked Strike", timestamp := ⟨11⟩ }
    , { id := 7, source := oid, controller := ⟨0⟩, target := .obj oid, op := .addSubtype .arrow, timestamp := ⟨12⟩ }
    , { id := 8, source := oid, controller := ⟨0⟩, target := .obj oid, op := .addSupertype (.class_ .ranger), timestamp := ⟨13⟩ }
    , { id := 9, source := oid, controller := ⟨0⟩, target := .obj oid, op := .grantKeyword .goAgain, timestamp := ⟨14⟩ }
    ]
  let (d, steps) := evalCharacteristicsWithSteps effs testObj testFace oid
  steps == effs.length &&
  d.controller == ⟨1⟩ &&
  d.name == "Mimicked Strike" &&
  d.subtypes.contains .arrow &&
  d.supertypes.contains (.class_ .ranger) &&
  d.keywords.contains .goAgain &&
  d.basePower == some 5 &&
  d.power == some 13 &&
  d.defense == some 2

-- 2. Stage 1 Copy copies printed face before Stage 7/8 modifications apply:
#guard
  let oid : ObjId := ⟨10⟩
  let copySrc : CardFace :=
    { name := "Crippling Crush", types := [.action], subtypes := [.attack], power := some 11, defense := some 3 }
  let effs : List ContinuousEffect :=
    [ { id := 1, source := oid, controller := ⟨0⟩, target := .obj oid, op := .addPower 2, timestamp := ⟨1⟩ }
    , { id := 2, source := oid, controller := ⟨0⟩, target := .obj oid, op := .copyFace copySrc, timestamp := ⟨20⟩ }
    ]
  let d := evalCharacteristics effs { testObj with plusPowerCounters := 0, minusDefenseCounters := 0 } testFace oid
  d.name == "Crippling Crush" && d.basePower == some 11 && d.power == some 13

-- 3. Dependency overrides Timestamp in same (stage, subStage) bucket (CR 6.3.3):
--    Effect B (ts=1) grants +4{p} to cards with subtype .arrow? Here Stage 4 adds .arrow when
--    object has .attack; Effect A (ts=10) adds .attack.
#guard
  let oid : ObjId := ⟨7⟩
  let bareFace : CardFace := { name := "Bare", types := [.action], subtypes := [] }
  let effB : ContinuousEffect :=
    { id := 1, source := oid, controller := ⟨0⟩,
      target := .matching (reqSubtype := some .attack), op := .addSubtype .arrow, timestamp := ⟨1⟩ }
  let effA : ContinuousEffect :=
    { id := 2, source := oid, controller := ⟨0⟩,
      target := .obj oid, op := .addSubtype .attack, timestamp := ⟨10⟩ }
  let d := evalCharacteristics [effB, effA] testObj bareFace oid
  d.subtypes.contains .attack && d.subtypes.contains .arrow

-- 4. Cyclic Dependency falls back to earliest Timestamp (CR 6.3.3c) and terminates (I12c):
#guard
  let oid : ObjId := ⟨7⟩
  let alphaFace : CardFace := { name := "Alpha", types := [.action] }
  let eEarly : ContinuousEffect :=
    { id := 1, source := oid, controller := ⟨0⟩,
      target := .matching (reqName := some "Alpha"), op := .setName "Beta", timestamp := ⟨2⟩ }
  let eLate : ContinuousEffect :=
    { id := 2, source := oid, controller := ⟨0⟩,
      target := .matching (reqName := some "Alpha"), op := .setName "Gamma", timestamp := ⟨5⟩ }
  let (d, steps) := evalCharacteristicsWithSteps [eLate, eEarly] testObj alphaFace oid
  d.name == "Beta" && steps == 2

-- 5. Asset Cost Calculation L5 (CR 5.1.5): Set -> Increase -> Reduce (floor 0):
#guard
  let base : AssetCost := { actionPoints := 1, resources := 5 }
  let c1 := calcFinalAssetCost base (some 2) [1, 2] [3]    -- set 2 + 3 - 3 = 2
  let c2 := calcFinalAssetCost base none [1] [10]           -- 5 + 1 - 10 = 0 (floored)
  let c3 := calcFinalAssetCost base (some 0) [2] [1]        -- set 0 + 2 - 1 = 1
  c1.resources == 2 && c2.resources == 0 && c3.resources == 1

-- 6. Live GameState integration: `Effect.grant` (.thisTurn) updates `s.characteristics`
--    and expires cleanly at End Phase (`endTurnCleanup`) (CR 4.4.3, 6.2):
#guard match (do
    let s0 : GameState :=
      { config := GameConfig.ccDuel
        cards := wtrDB
        turn := 2
        active := some ⟨0⟩
        turnOrder := [⟨0⟩, ⟨1⟩]
        phase := .actionPhase
        pending := [.priority ⟨0⟩ 0, .endPhaseStart ⟨0⟩] }
    let s0 := ((s0.setLife ⟨0⟩ 40).setLife ⟨1⟩ 40).setPool ⟨0⟩ { actionPoints := 2, resources := 2 }
    let (s1, wb) ← addObject s0 (.player ⟨0⟩ .hand)
      { kind := .card ⟨0⟩ ⟨"WTR_203_R"⟩, owner := ⟨0⟩, controller := ⟨0⟩, timestamp := ⟨0⟩ } .top
    -- Awakening Bellow Red (WTR_032_R): cost 1{r}, Go Again, grants +3{p} until end of turn
    let (s2, bellow) ← addObject s1 (.player ⟨0⟩ .hand)
      { kind := .card ⟨1⟩ ⟨"WTR_032_R"⟩, owner := ⟨0⟩, controller := ⟨0⟩, timestamp := ⟨1⟩ } .top
    -- Play Awakening Bellow Red and let it resolve
    let s3 ← match step 64 s2 ⟨.player ⟨0⟩, .playCard bellow⟩ with | .ok (s', _) => some s' | .error _ => none
    let s4 ← match step 64 s3 ⟨.player ⟨0⟩, .pass⟩ with | .ok (s', _) => some s' | .error _ => none
    let s5 ← match step 64 s4 ⟨.player ⟨1⟩, .pass⟩ with | .ok (s', _) => some s' | .error _ => none
    -- Wounding Blow Red base power 4 + Awakening Bellow +3 = 7 via 8-stage `characteristics`!
    let buffedPow := (s5.characteristics wb).bind (·.power)
    -- Pass Action Phase -> End Phase (skip arsenal) -> `untilEndOfTurn` effect expires!
    let s6 ← match step 64 s5 ⟨.player ⟨0⟩, .pass⟩ with | .ok (s', _) => some s' | .error _ => none
    let s7 ← match step 64 s6 ⟨.player ⟨1⟩, .pass⟩ with | .ok (s', _) => some s' | .error _ => none
    let s8 ← match step 64 s7 ⟨.player ⟨0⟩, .arsenalSkip⟩ with | .ok (s', _) => some s' | .error _ => none
    let unbuffedPow := (s8.characteristics wb).bind (·.power)
    pure (buffedPow == some 7 && s8.activeEffects.isEmpty && unbuffedPow == some 4)) with
  | some b => b
  | none => false
