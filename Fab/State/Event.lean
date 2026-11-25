module

public import Fab.State.Zone
public import Fab.Core.Property

/-!
# Events and 4-stage replacement classification

Events emitted by board-modifying primitives and the four replacement-effect precedence stages
defined in the Comprehensive Rules (CR 1.9, 6.4-6.5).
-/

@[expose] public section

namespace Fab

/-- Observable game events proposed and emitted through `perform` (CR 1.9). -/
inductive Event where
  /-- An object moved from `src` to `dst` (`newId` differs from `oldId` iff `Zone.crosses`). -/
  | moved (oldId newId : ObjId) (src dst : Zone)
  /-- Player `player` drew object `obj` from deck to hand (CR 4.1.6, 4.4.3f). -/
  | drawn (player : PlayerId) (obj : ObjId)
  /-- A private card's identity became public through a reveal effect (CR 8.5.17). -/
  | revealed (player : PlayerId) (obj : ObjId) (card : CardId)
  /-- Player `player` pitched object `obj` generating `resources` `{r}` and `chi` `{c}` (CR 1.14.3). -/
  | pitched (player : PlayerId) (obj : ObjId) (resources chi : Nat)
  /-- Player `player` discarded object `obj` from hand to graveyard. -/
  | discarded (player : PlayerId) (obj : ObjId)
  /-- Object `obj` was banished to `owner`'s banished zone, optionally face-down (CR 3.3). -/
  | banished (owner : PlayerId) (obj : ObjId) (faceDown : Bool)
  /-- The given layer declared a hero as a target (CR 6.6.6a). -/
  | targetedHero (layer : ObjId) (target : PlayerId)
  /-- The given layer declared an attack as a target (CR 5.1.4a). -/
  | targetedAttack (layer target : ObjId)
  /-- The given layer declared a weapon permanent as a target (CR 5.1.4a). -/
  | targetedWeapon (layer target : ObjId)
  /-- The given triggered layer declared an equipment as a target (CR 6.6.6a). -/
  | targetedEquipment (layer target : ObjId)
  /-- `amount` damage of kind `kind` (physical or arcane) was dealt to `target`. -/
  | damageDealt (target : PlayerId) (kind : DamageKind) (amount : Nat)
  /-- Player `player` gained `amount` life. -/
  | lifeGained (player : PlayerId) (amount : Nat)
  /-- Player `player` lost `amount` life. -/
  | lifeLost (player : PlayerId) (amount : Nat)
deriving DecidableEq, Repr

end Fab

end
