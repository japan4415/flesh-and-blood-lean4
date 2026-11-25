module

import Fab
import FabCards
meta import Fab
meta import FabCards

/-!
# Tests: M3b Effect IR syntax, static well-formedness (`CardDB.WF`), and WTR CardDB
-/

open Fab
open FabCards

-- 1. Full 226-card WTR CardDB is kernel-checked well-formed (`wtrDB_wf`) and has 226 unique cards
#guard wtrDB.cards.length == 226
#guard (wtrDB.cards.map (·.id)).eraseDups.length == 226
#guard decide wtrDB.WF

-- 2. Representative cards across Gem, Brute, Guardian, Ninja, Warrior, Generic, and Tokens are
--    present in `wtrDB` with their expected status and printed properties
#guard match wtrDB.find? ⟨"WTR_000_B"⟩ with
  | some c => c.front.name == "Heart of Fyendal" && c.front.hasSubtype .gem && c.isLegendary && c.status == .full
  | none => false

#guard match wtrDB.find? ⟨"WTR_038"⟩ with
  | some c => c.front.name == "Bravo, Showstopper" && c.isAdultHero && c.front.life == some 40 && c.status == .drafted
  | none => false

#guard match wtrDB.find? ⟨"WTR_081_B"⟩ with
  | some c => c.front.name == "Lord of Wind" && c.front.keywords.contains .combo && c.status == .drafted
  | none => false

#guard match wtrDB.find? ⟨"WTR_115"⟩ with
  | some c => c.front.name == "Dawnblade" && c.isTwoHanded && c.front.abilities.length == 3 && c.status == .drafted
  | none => false

#guard match wtrDB.find? ⟨"WTR_206_R"⟩ with
  | some c =>
    c.front.name == "Pummel" &&
    c.status == .drafted &&
    match c.front.playEffect with
    | some ed => ed.modes.length == 2
    | none => false
  | none => false

-- 3. Conditional 'go again' text (Scar for a Scar) is NOT falsely extracted as static printed goAgain,
--    while standalone 'Go again' (Head Jab) IS extracted
#guard match wtrDB.find? ⟨"WTR_191_R"⟩, wtrDB.find? ⟨"WTR_098_R"⟩ with
  | some scar, some jab =>
    !scar.front.keywords.contains .goAgain &&
    jab.front.keywords.contains .goAgain
  | _, _ => false

-- 4. Static IR WF rejects out-of-bounds target slots
meta def badSlotCard : CardDef :=
  { id := ⟨"BAD_SLOT"⟩
    front :=
      { name := "Bad Slot"
        playEffect := some
          { targets := []
            body := .grant (.obj (.slot 0)) (.addPower (.const 2)) .thisChainLink } } }

#guard !badSlotCard.wfBool

-- 5. Static IR WF rejects unbound lexical variables
meta def badVarCard : CardDef :=
  { id := ⟨"BAD_VAR"⟩
    front :=
      { name := "Bad Var"
        playEffect := some
          { body := .prim (.gainLife .controller (.varVal ⟨0⟩)) } } }

#guard !badVarCard.wfBool

-- 6. Static IR WF rejects `NumExpr.xValue` when no `ExtraCost.payX` is declared
meta def badXCard : CardDef :=
  { id := ⟨"BAD_X"⟩
    front :=
      { name := "Bad X"
        playEffect := some
          { body := .grant .self_ (.addPower .xValue) .thisChainLink } } }

#guard !badXCard.wfBool

-- 7. Static IR WF rejects empty `chooseOne` and out-of-range die roll branches (0 or 7)
meta def badChooseCard : CardDef :=
  { id := ⟨"BAD_CHOOSE"⟩
    front :=
      { name := "Bad Choose"
        playEffect := some { body := .chooseOne .nil } } }

meta def badDieCard : CardDef :=
  { id := ⟨"BAD_DIE"⟩
    front :=
      { name := "Bad Die"
        playEffect := some
          { body := .rollDie6 ⟨0⟩ (.cons 1 7 .nop .nil) .nop } } }

#guard !badChooseCard.wfBool
#guard !badDieCard.wfBool

-- 8. `CardDB.WF` rejects duplicate `CardId`s and invalid cards
#guard !decide ({ cards := [FabCards.WTR.WTR_098_R, FabCards.WTR.WTR_098_R] } : CardDB).WF
#guard !decide ({ cards := [badSlotCard] } : CardDB).WF
