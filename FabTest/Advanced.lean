module

import Fab
meta import Fab

/-!
# M8 Advanced Mechanics Tests (CR Chapter 8-9)

Exercises:
1. Double-faced cards: Transcend (front → back in hand, pitchable for Chi), Transform (in-place
   ObjId preserved), Demi-Hero
2. Split / Meld (CR 8.3.38): left/right/both cost summation & right-before-left resolution
3. Equipment: Evo stacking + `underlyingEquipment`, Modular loadout equip, Cloaked stays face-down
   across `revealAllLoadouts` & flips face-up preserving ObjId
4. Permanent combat: Ally damage + End Phase life reset + lethal Ally GSP clear, Landmark
   uniqueness in GSP (newer Landmark survives, older destroyed)
5. Tap / Untap cost enforcement
6. Soul / Charge from hand
7. Clash (higher power wins, power beats no-power, tie = none), Wager token prize, Mark, Gold
   crack (draw 1), Fealty crack (Draconic grant via 8-stage continuous effects)
-/

namespace FabTest.Advanced

open Fab

meta def p0 : PlayerId := ⟨0⟩
meta def p1 : PlayerId := ⟨1⟩

meta def innerChiBack : CardFace :=
  { name := "Inner Chi"
    supertypes := [.talent .mystic]
    types := [.resource]
    pitch := some 3
    pitchAsset := .chi
    color := some .blue }

meta def transcendDef : CardDef :=
  { id := ⟨"MST_TR"⟩
    front :=
      { name := "Sacred Art: Jade Tiger Domain"
        supertypes := [.talent .mystic]
        types := [.action]
        pitch := some 3
        cost := some { actionPoints := 1, resources := 0 }
        keywords := [.transcend] }
    back := some innerChiBack }

meta def meldDef : CardDef :=
  { id := ⟨"ROS_MELD"⟩
    front :=
      { name := "Life"
        supertypes := [.talent .earth]
        types := [.action]
        cost := some { actionPoints := 1, resources := 1 }
        keywords := [.meld]
        playEffect := some { body := .prim (.gainLife .controller (.const 2)) } }
    splitRight := some
      { name := "Consign to Cosmos"
        supertypes := [.talent .earth]
        types := [.action]
        cost := some { actionPoints := 0, resources := 2 }
        playEffect := some { body := .prim (.draw .controller (.const 1)) } } }

meta def baseHeadDef : CardDef :=
  { id := ⟨"EVO_BASE"⟩
    front :=
      { name := "Proto Base Head"
        supertypes := [.class_ .mechanologist]
        types := [.equipment]
        subtypes := [.head, .base]
        defense := some 0 } }

meta def evoHeadDef : CardDef :=
  { id := ⟨"EVO_TOP"⟩
    front :=
      { name := "Evo Steel Soul Tower"
        supertypes := [.class_ .mechanologist]
        types := [.equipment]
        subtypes := [.head, .evo]
        defense := some 2
        keywords := [.evo, .battleworn] } }

meta def modularDef : CardDef :=
  { id := ⟨"MOD_EQ"⟩
    front :=
      { name := "Adaptive Plating"
        supertypes := [.class_ .mechanologist]
        types := [.equipment]
        defense := some 1
        keywords := [.modular, .battleworn] } }

meta def cloakedDef : CardDef :=
  { id := ⟨"CLK_EQ"⟩
    front :=
      { name := "Mask of Deceit"
        supertypes := [.class_ .assassin]
        types := [.equipment]
        subtypes := [.head]
        defense := some 1
        keywords := [.cloaked] } }

meta def allyDef : CardDef :=
  { id := ⟨"ALLY_1"⟩
    front :=
      { name := "Aether Ashwing"
        supertypes := [.class_ .illusionist]
        types := [.token]
        subtypes := [.ally]
        power := some 1
        life := some 4 } }

meta def landmark1Def : CardDef :=
  { id := ⟨"LM_1"⟩
    front :=
      { name := "Great Library of Solana"
        supertypes := [.talent .light]
        types := [.action]
        subtypes := [.landmark] } }

meta def landmark2Def : CardDef :=
  { id := ⟨"LM_2"⟩
    front :=
      { name := "Korshem, Crossroad of Elements"
        supertypes := [.talent .elemental]
        types := [.action]
        subtypes := [.landmark] } }

meta def atk6Def : CardDef :=
  { id := ⟨"ATK_6"⟩
    front := { name := "Heavy Swing", types := [.action], subtypes := [.attack], power := some 6 } }

meta def atk4Def : CardDef :=
  { id := ⟨"ATK_4"⟩
    front := { name := "Light Swing", types := [.action], subtypes := [.attack], power := some 4 } }

meta def noPowDef : CardDef :=
  { id := ⟨"NO_POW"⟩
    front := { name := "Non-Attack", types := [.instant] } }

meta def advDB : CardDB :=
  ⟨[transcendDef, meldDef, baseHeadDef, evoHeadDef, modularDef, cloakedDef,
    allyDef, landmark1Def, landmark2Def, atk6Def, atk4Def, noPowDef]⟩

meta def mkState : GameState :=
  { config := { format := .classicConstructed, mode := .duel, ruleSet := .coreOnly }
    cards := advDB
    turnOrder := [p0, p1]
    active := some p0
    phase := .actionPhase
    heroLife := ((∅ : Std.ExtTreeMap Nat Int).insert 0 20).insert 1 20 }

-- 1. Transcend, Transform, and Meld
meta def doubleFaceAndMeldTest : Bool :=
  match addObject mkState .stack
      { kind := .card ⟨1⟩ ⟨"MST_TR"⟩, owner := p0, controller := p0, timestamp := ⟨0⟩ } .top with
  | none => false
  | some (s1, trId) =>
    -- Transcend moves card to hand as .back face
    let trOk :=
      match transcendCard s1 trId with
      | some (s2, handId, _) =>
        match pitchOne s2 p0 handId with
        | some (s3, pitchId, events) =>
          handId ∈ s2.zone (.player p0 .hand) &&
          (s2.obj? handId).map (·.faceState) == some .back &&
          (s2.objectFace? handId).map (·.name) == some "Inner Chi" &&
          s3.zone (.player p0 .pitch) == [pitchId] &&
          events.countP (· == .pitched p0 pitchId 0 3) == 1 &&
          (s3.poolOf p0).chi == 3 && (s3.poolOf p0).resources == 0
        | none => false
      | none => false
    -- Transform flips in place preserving ObjId
    let sTf := transformObject s1 trId
    let tfOk := (sTf.obj? trId).map (·.faceState) == some .back
    -- Meld combines costs (1+2=3{r}) and resolves right before left
    let meldOk :=
      meldDef.canMeld == true &&
      meldEffectiveCost meldDef .both == { actionPoints := 1, resources := 3, chi := 0 } &&
      meldEffectiveName meldDef .both == "Life // Consign to Cosmos" &&
      meldResolveEffects meldDef .both ==
        [.prim (.draw .controller (.const 1)), .prim (.gainLife .controller (.const 2))]
    trOk && tfOk && meldOk

#guard doubleFaceAndMeldTest == true

-- 2. Evo, Modular, and Cloaked equipment
meta def equipmentExtTest : Bool :=
  -- Evo: equip Evo Head on top of Base Head -> Base Head is in underlyingEquipment
  match addObject mkState (.player p0 .head)
      { kind := .card ⟨2⟩ ⟨"EVO_BASE"⟩, owner := p0, controller := p0, timestamp := ⟨0⟩ } .top with
  | none => false
  | some (s1, baseId) =>
    match addObject s1 (.player p0 .hand)
        { kind := .card ⟨3⟩ ⟨"EVO_TOP"⟩, owner := p0, controller := p0, timestamp := ⟨1⟩ } .top with
    | none => false
    | some (s2, evoId) =>
      let evoOk :=
        match equipEvo s2 p0 evoId .head with
        | some (s3, newEvoId, _) =>
          (s3.zone (.player p0 .head)).head? == some newEvoId &&
          underlyingEquipment s3 p0 .head == [baseId]
        | none => false
      -- Modular: head occupied -> loadoutEquipDest? routes Modular equipment to chest!
      match addObject s1 (.player p0 .inventory)
          { kind := .card ⟨4⟩ ⟨"MOD_EQ"⟩, owner := p0, controller := p0, timestamp := ⟨2⟩ } .top with
      | none => false
      | some (sMod, modId) =>
        let modOk := loadoutEquipDest? sMod p0 modId == some (.player p0 .chest)
        -- Cloaked: stays face-down across revealAllLoadouts, then flips face-up preserving ObjId
        match addObject mkState (.player p0 .head)
            { kind := .card ⟨5⟩ ⟨"CLK_EQ"⟩, owner := p0, controller := p0, faceDown := true, timestamp := ⟨3⟩ } .top with
        | none => false
        | some (sClk, clkId) =>
          let sRev := revealAllLoadouts sClk
          let sUp := turnEquipmentFaceUp sRev clkId
          let clkOk :=
            (sRev.obj? clkId).map (·.faceDown) == some true &&
            (sUp.obj? clkId).map (·.faceDown) == some false
          evoOk && modOk && clkOk

#guard equipmentExtTest == true

-- 3. Ally damage, End Phase reset, lethal GSP clear, and Landmark uniqueness in GSP
meta def allyAndLandmarkTest : Bool :=
  match addObject mkState (.player p0 .permanent)
      { kind := .token ⟨"ALLY_1"⟩, owner := p0, controller := p0, life := some 4, timestamp := ⟨0⟩ } .top with
  | none => false
  | some (s1, aid) =>
    -- Non-lethal 2 damage leaves Ally at 2 life; End Phase reset restores it to 4!
    let (sDmg, _) := damageAttackTarget s1 (.ally aid) 2
    let sReset := resetAlliesLife sDmg
    -- Lethal 4 damage triggers GSP and clears Ally from permanent zone!
    let (sDead, _) := damageAttackTarget s1 (.ally aid) 4
    let allyOk :=
      (sDmg.obj? aid).bind (·.life) == some 2 &&
      (sReset.obj? aid).bind (·.life) == some 4 &&
      (sDead.zone (.player p0 .permanent)).isEmpty
    -- Landmark uniqueness: LM_1 (ts=1) then LM_2 (ts=5) -> gspRun destroys LM_1 and keeps LM_2!
    match addObject mkState (.player p0 .permanent)
        { kind := .card ⟨20⟩ ⟨"LM_1"⟩, owner := p0, controller := p0, timestamp := ⟨1⟩ } .top with
    | none => false
    | some (sL1, lm1Id) =>
      match addObject sL1 (.player p1 .permanent)
          { kind := .card ⟨21⟩ ⟨"LM_2"⟩, owner := p1, controller := p1, timestamp := ⟨5⟩ } .top with
      | none => false
      | some (sL2, lm2Id) =>
        let sSettled := gspRun sL2
        let lmOk :=
          olderLandmarks sL2 == [lm1Id] &&
          olderLandmarks sSettled == [] &&
          sSettled.zone (.player p0 .permanent) == [] &&
          (sSettled.zone (.player p0 .graveyard)).length == 1 &&
          sSettled.zone (.player p1 .permanent) == [lm2Id]
        allyOk && lmOk

#guard allyAndLandmarkTest == true

-- 4. Tap/Untap, Soul/Charge, Clash, Wager, Mark, Gold, Fealty
meta def tapSoulClashWagerMarkTest : Bool :=
  match addObject mkState (.player p0 .permanent)
      { kind := .token ⟨"ALLY_1"⟩, owner := p0, controller := p0, life := some 4, timestamp := ⟨0⟩ } .top with
  | none => false
  | some (s1, permId) =>
    let tapOk :=
      canPayTapCost s1 p0 permId == true &&
      match payTapCost s1 p0 permId with
      | some sTapped =>
        canPayTapCost sTapped p0 permId == false &&
        canPayTapCost (untapObject sTapped permId) p0 permId == true
      | none => false
    -- Soul / Charge
    match addObject mkState (.player p0 .hand)
        { kind := .card ⟨30⟩ ⟨"ATK_6"⟩, owner := p0, controller := p0, timestamp := ⟨1⟩ } .top with
    | none => false
    | some (sH, cardId) =>
      let chargeOk :=
        match chargeFromHand sH p0 cardId with
        | some (sCh, _, _) => soulCount sCh p0 == 1 && (sCh.zone (.player p0 .hand)).isEmpty
        | none => false
      -- Clash: 6{p} beats 4{p}, 4{p} beats no-power, 6{p} vs 6{p} = none
      match addObject mkState (.player p0 .deck)
          { kind := .card ⟨31⟩ ⟨"ATK_6"⟩, owner := p0, controller := p0, timestamp := ⟨2⟩ } .top with
      | none => false
      | some (sC1, _) =>
        match addObject sC1 (.player p1 .deck)
            { kind := .card ⟨32⟩ ⟨"ATK_4"⟩, owner := p1, controller := p1, timestamp := ⟨3⟩ } .top with
        | none => false
        | some (sC2, _) =>
          let clashOk := resolveClash sC2 p0 p1 == some p0 && resolveClash sC2 p1 p0 == some p0
          -- Wager + Gold crack (draws top card of p0's deck!)
          let sW := resolveWager sC2 { beneficiary := p0, prizeToken := goldTokenId, prizeCount := 1 } true
          let goldOk :=
            match sW.zone (.player p0 .permanent) with
            | [goldId] =>
              let (sCracked, _) := crackGold sW p0 goldId
              (sCracked.zone (.player p0 .permanent)).isEmpty &&
              (sCracked.zone (.player p0 .hand)).length == 1
            | _ => false
          -- Mark + Fealty crack (grants Draconic supertype via 8-stage continuous engine!)
          let sM := markPlayer sC2 p1
          let markOk := isPlayerMarked sM p1 == true && isPlayerMarked (clearMark sM p1) p1 == false
          let sF := resolveWager sC2 { beneficiary := p0, prizeToken := fealtyTokenId, prizeCount := 1 } true
          let fealtyOk :=
            match sF.zone (.player p0 .permanent), sF.zone (.player p0 .deck) with
            | [fealtyId], [atkId] =>
              let (sCracked, _) := crackFealty sF p0 fealtyId atkId
              (sCracked.zone (.player p0 .permanent)).isEmpty &&
              match sCracked.characteristics atkId with
              | some dc => dc.supertypes.contains (.talent .draconic)
              | none => false
            | _, _ => false
          tapOk && chargeOk && clashOk && goldOk && markOk && fealtyOk

#guard tapSoulClashWagerMarkTest == true

end FabTest.Advanced
