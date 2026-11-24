module

import Fab
import FabTest.Fixtures
meta import Fab
meta import FabTest.Fixtures

/-!
# Tests: M2a zones, moveObj (Arena preservation vs boundary crossing), and basic actions
-/

open Fab
open FabTest

/-- Build a small 2-player state with P0 having:
- Chest equipment `tectonicPlating` with 1 `-1{d}` counter
- Hand holding Red `Sink Below` (pitch 1), Blue `Wounding Blow` (pitch 3), and non-pitchable `anothos`
- Deck holding Yellow `Sink Below` (pitch 2) -/
meta def m2aState : Option (GameState × ObjId × ObjId × ObjId × ObjId × ObjId) := do
  let s0 : GameState := { config := GameConfig.ccDuel, cards := sampleDB }
  let p0 : PlayerId := ⟨0⟩
  let (s1, eqId) ← addObject s0 (.player p0 .chest)
    { kind := .card ⟨0⟩ tectonicPlating.id, owner := p0, controller := p0,
      minusDefenseCounters := 1, timestamp := ⟨0⟩ }
  let (s2, redId) ← addObject s1 (.player p0 .hand)
    { kind := .card ⟨1⟩ ⟨"WTR_215_R"⟩, owner := p0, controller := p0, timestamp := ⟨0⟩ }
  let (s3, blueId) ← addObject s2 (.player p0 .hand)
    { kind := .card ⟨2⟩ ⟨"WTR_193_B"⟩, owner := p0, controller := p0, timestamp := ⟨0⟩ }
  let (s4, weapHandId) ← addObject s3 (.player p0 .hand)
    { kind := .card ⟨3⟩ anothos.id, owner := p0, controller := p0, timestamp := ⟨0⟩ }
  let (s5, deckId) ← addObject s4 (.player p0 .deck)
    { kind := .card ⟨4⟩ ⟨"WTR_216_Y"⟩, owner := p0, controller := p0, timestamp := ⟨0⟩ }
  some (s5, eqId, redId, blueId, weapHandId, deckId)

-- 1. Arena-to-Arena move (Chest -> Combat Chain -> Chest) preserves ObjId AND -1{d} counters!
#guard match m2aState with
  | some (s, eqId, _, _, _, _) =>
    match moveObj s eqId .combatChain with
    | some (s1, eqId1) =>
      match moveObj s1 eqId1 (.player ⟨0⟩ .chest) with
      | some (s2, eqId2) =>
        eqId1 == eqId && eqId2 == eqId &&
        (s2.obj? eqId2).map (·.minusDefenseCounters) == some 1 &&
        s2.physIds.length == s.physIds.length
      | none => false
    | none => false
  | none => false

-- 2. Non-Arena -> Arena -> Non-Arena (Hand -> Combat Chain -> Graveyard) mints fresh ObjIds
#guard match m2aState with
  | some (s, _, redId, _, _, _) =>
    match moveObj s redId .combatChain with
    | some (s1, ccId) =>
      match moveObj s1 ccId (.player ⟨0⟩ .graveyard) with
      | some (s2, gyId) =>
        ccId != redId && gyId != ccId && gyId != redId &&
        (gyId ∈ s2.zone (.player ⟨0⟩ .graveyard)) &&
        !(redId ∈ s2.zone (.player ⟨0⟩ .hand))
      | none => false
    | none => false
  | none => false

-- 3. drawOne moves top of deck to hand, then drawing from empty deck is a safe no-op (no loss!)
#guard match m2aState with
  | some (s, _, _, _, _, _) =>
    let (s1, evs1) := drawOne s ⟨0⟩
    let (s2, evs2) := drawOne s1 ⟨0⟩
    (s1.zone (.player ⟨0⟩ .deck)).isEmpty &&
    (s1.zone (.player ⟨0⟩ .hand)).length == (s.zone (.player ⟨0⟩ .hand)).length + 1 &&
    evs1.length == 2 &&
    s2 == s1 && evs2.isEmpty
  | none => false

-- 4. pitchOne: pitching Red gives +1{r}, pitching Blue gives +3{r} (total 4), non-pitchable fails
#guard match m2aState with
  | some (s, _, redId, blueId, weapHandId, _) =>
    match pitchOne s ⟨0⟩ redId with
    | some (s1, pitchRedId, _) =>
      match pitchOne s1 ⟨0⟩ blueId with
      | some (s2, pitchBlueId, _) =>
        (s1.poolOf ⟨0⟩).resources == 1 &&
        (s2.poolOf ⟨0⟩).resources == 4 &&
        (s2.poolOf ⟨1⟩).resources == 0 &&
        (pitchRedId ∈ s2.zone (.player ⟨0⟩ .pitch)) &&
        (pitchBlueId ∈ s2.zone (.player ⟨0⟩ .pitch)) &&
        (pitchOne s2 ⟨0⟩ weapHandId).isNone
      | none => false
    | none => false
  | none => false

-- 5. discardOne and banishOne (face-down for Intimidate / face-up for Blood Debt)
#guard match m2aState with
  | some (s, _, redId, blueId, _, _) =>
    match discardOne s ⟨0⟩ redId with
    | some (s1, gyId, _) =>
      match banishOne s1 blueId true with
      | some (s2, banId, _) =>
        (gyId ∈ s2.zone (.player ⟨0⟩ .graveyard)) &&
        (banId ∈ s2.zone (.player ⟨0⟩ .banished)) &&
        (s2.obj? banId).map (·.faceDown) == some true
      | none => false
    | none => false
  | none => false
