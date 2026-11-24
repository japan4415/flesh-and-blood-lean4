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

/-- The four replacement-effect application stages in strict precedence order (CR 6.4.10, 6.5.1). -/
inductive ReplacementStage where
  /-- Stage A: Self-replacement and identity-replacement effects (CR 6.4.10a, 6.4.10b). -/
  | selfOrIdentity
  /-- Stage B: Standard replacement effects (CR 6.4.10c). -/
  | standard
  /-- Stage C: Prevention effects, including Ward, Arcane Barrier, Spellvoid, Quell (CR 6.4.10d). -/
  | prevention
  /-- Stage D: Outcome-replacement effects applied after the event concludes (CR 6.4.10e). -/
  | outcome
deriving DecidableEq, Repr, Hashable

/-- Precedence order of replacement stages (CR 6.5.1). -/
def ReplacementStage.order : List ReplacementStage :=
  [.selfOrIdentity, .standard, .prevention, .outcome]

/-- Observable game events proposed and emitted through `perform` (CR 1.9). -/
inductive Event where
  /-- An object moved from `src` to `dst` (`newId` differs from `oldId` iff `Zone.crosses`). -/
  | moved (oldId newId : ObjId) (src dst : Zone)
  /-- Player `player` drew object `obj` from deck to hand (CR 4.1.6, 4.4.3f). -/
  | drawn (player : PlayerId) (obj : ObjId)
  /-- Player `player` pitched object `obj` generating `resources` `{r}` and `chi` `{c}` (CR 1.14.3). -/
  | pitched (player : PlayerId) (obj : ObjId) (resources chi : Nat)
  /-- Player `player` discarded object `obj` from hand to graveyard. -/
  | discarded (player : PlayerId) (obj : ObjId)
  /-- Object `obj` was banished to `owner`'s banished zone, optionally face-down (CR 3.3). -/
  | banished (owner : PlayerId) (obj : ObjId) (faceDown : Bool)
  /-- `amount` damage of kind `kind` (physical or arcane) was dealt to `target`. -/
  | damageDealt (target : PlayerId) (kind : DamageKind) (amount : Nat)
  /-- Player `player` gained `amount` life. -/
  | lifeGained (player : PlayerId) (amount : Nat)
  /-- Player `player` lost `amount` life. -/
  | lifeLost (player : PlayerId) (amount : Nat)
deriving DecidableEq, Repr

end Fab

end
