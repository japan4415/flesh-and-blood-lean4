module

public import Fab.Tournament.Booster
public import FabCards.Draft
public import FabCards.Registry

/-!
# Welcome to Rathe booster opening

Slot counts follow the official product specification. Rarities follow the Collector's Centre
collector numbers. The last slot is represented by one logical face of a physical token.
-/

public section

namespace FabCards

open Fab

private inductive Rarity where
  | basic | common | rare | superRare | majestic | legendary | fabled
deriving DecidableEq

private def wtrRarity (n : Nat) : Rarity :=
  if n == 0 then .fabled
  else if [4, 41, 79, 116, 150].contains n then .legendary
  else if n ≤ 3 || (38 ≤ n && n ≤ 40) || (75 ≤ n && n ≤ 78) ||
      (113 ≤ n && n ≤ 115) || 224 ≤ n then .basic
  else if (6 ≤ n && n ≤ 7) || (43 ≤ n && n ≤ 44) || (81 ≤ n && n ≤ 82) ||
      (118 ≤ n && n ≤ 119) || (159 ≤ n && n ≤ 160) then .majestic
  else if (8 ≤ n && n ≤ 10) || (45 ≤ n && n ≤ 47) || (83 ≤ n && n ≤ 85) ||
      (120 ≤ n && n ≤ 122) || (161 ≤ n && n ≤ 163) then .superRare
  else if (11 ≤ n && n ≤ 19) || (48 ≤ n && n ≤ 56) || (86 ≤ n && n ≤ 94) ||
      (123 ≤ n && n ≤ 131) || (164 ≤ n && n ≤ 175) then .rare
  else .common

private def wtrCatalog : List (CardDef × Rarity) :=
  wtrDB.cards.filterMap fun card =>
    match card.id.val.splitOn "_" with
    | ["WTR", number] | ["WTR", number, _] => do
      let n ← number.toNat?
      if n ≤ 225 then some (card, wtrRarity n) else none
    | _ => none

/-- WTR booster candidates in a canonical opening order. Class slots can draw from all four WTR
classes. The last slot is excluded from the draft pool. -/
def wtrBoosterLayout : BoosterPack.Layout :=
  let pool (accepts : CardDef → Rarity → Bool) :=
    (wtrCatalog.filter fun (card, rarity) => accepts card rarity).map (·.1.id)
  let genericCommons := pool fun card rarity =>
    rarity == .common && !card.isEquipment && card.front.supertypes.contains .generic
  let classCommons := pool fun card rarity =>
    rarity == .common && !card.isEquipment &&
      [ClassType.brute, .guardian, .ninja, .warrior].any fun c =>
        card.front.supertypes.contains (.class_ c)
  List.replicate 4 genericCommons ++ List.replicate 7 classCommons ++ [
    pool fun _ rarity => rarity == .rare,
    pool fun _ rarity => [.rare, .superRare, .majestic].contains rarity,
    pool fun card rarity => rarity == .common && card.isEquipment,
    pool fun _ rarity => rarity != .basic,
    wtrDraft.basics
  ]

/-- The WTR opening layout accounts for all physical slots in the draft product. -/
theorem wtrBoosterLayout_length : wtrBoosterLayout.length = wtrDraft.totalSlots := by
  rfl

/-- Open one WTR booster using one candidate index per slot. The resulting physical slots can
be supplied directly to `BoosterDraft.State.start`. -/
def openWtrBooster (indices : List Nat) : Option BoosterDraft.Booster :=
  (BoosterPack.openSlots wtrBoosterLayout indices).map (List.map some)

/-- Every successful WTR opening has the physical slot count required by the draft product. -/
theorem openWtrBooster_length {indices : List Nat} {booster : BoosterDraft.Booster}
    (h : openWtrBooster indices = some booster) : booster.length = wtrDraft.totalSlots := by
  cases opening : BoosterPack.openSlots wtrBoosterLayout indices with
  | none => simp [openWtrBooster, opening] at h
  | some cards =>
    simp [openWtrBooster, opening] at h
    subst booster
    simpa only [List.length_map, wtrBoosterLayout_length] using
      (BoosterPack.openSlots_fits opening).length_eq

end FabCards

end
