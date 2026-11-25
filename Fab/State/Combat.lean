module

public import Fab.State.Lki

/-!
# Combat Chain state

Models the Flesh and Blood Combat Chain and its 7 steps (CR 3.5, 7.0-7.7):
Layer (7.1) → Attack (7.2) → Defend (7.3) → Reaction (7.4) → Damage (7.5) →
Resolution (7.6) → Close (7.7).

Every `ChainLink` retains an immutable `attackLki : LkiSnapshot` so properties such as Go Again
and card name remain readable even if the attack card leaves the combat chain (CR 1.2.3, 3.5.4b)
or a previous weapon attack-proxy ceases to exist (CR 1.4.3).
-/

@[expose] public section

namespace Fab

/-- The seven sequential steps of a Flesh and Blood Combat Chain (CR 7.1-7.7). -/
inductive CombatStep where
  /-- Step 1: Attack layer sits on the stack before entering the combat chain (CR 7.1). -/
  | layer
  /-- Step 2: Attack enters the new chain link and becomes attacking (CR 7.2). -/
  | attack
  /-- Step 3: Defending hero declares defending cards from hand and/or equipment (CR 7.3). -/
  | defend
  /-- Step 4: Attack Reactions, Defense Reactions, and Instants on the stack (CR 7.4). -/
  | reaction
  /-- Step 5: Combat damage calculation `{p} - {d}` and Hit determination (CR 7.5). -/
  | damage
  /-- Step 6: Go Again +1 AP and opportunity to continue with a new chain link (CR 7.6). -/
  | resolution
  /-- Step 7: Equipment wear, arena return preserving `ObjId`, graveyard cleanup (CR 7.7). -/
  | close
deriving DecidableEq, Repr, Hashable

/-- Strictly next step in the 7-step Combat Chain progression (CR 7.1-7.7). -/
def CombatStep.next? : CombatStep → Option CombatStep
  | .layer => some .attack
  | .attack => some .defend
  | .defend => some .reaction
  | .reaction => some .damage
  | .damage => some .resolution
  | .resolution => some .close
  | .close => none

/-- Full ordered list of the 7 Combat Chain steps (CR 7.1-7.7). -/
def CombatStep.allSteps : List CombatStep :=
  [.layer, .attack, .defend, .reaction, .damage, .resolution, .close]

/-- A single Chain Link on an open Combat Chain (CR 3.5.4). -/
structure ChainLink where
  /-- One-based link ordinal within this combat chain. -/
  linkId : LinkId
  /-- Attacking player. -/
  attacker : PlayerId
  /-- Defending hero's player. -/
  defender : PlayerId
  /-- Attacking card or `attackProxy` `ObjId` currently on `Zone.combatChain`, if still present. -/
  attack : Option ObjId := none
  /-- Weapon or permanent attack source `ObjId` on `Zone.combatChain`, if this is a weapon attack (CR 1.4.3). -/
  attackSource : Option ObjId := none
  /-- Immutable Last Known Information captured for this link's attack (CR 1.2.3, 3.5.4b). -/
  attackLki : LkiSnapshot
  /-- Temporary power `{p}` modifier granted to this chain link (Attack Reactions, Combo buffs). -/
  powerBonus : Int := 0
  /-- Temporary defense `{d}` modifier granted to this chain link. -/
  defenseBonus : Int := 0
  /-- Keywords dynamically granted to this link's attack (e.g., Go Again, Dominate). -/
  grantedKeywords : List KeywordInst := []
  /-- Defending card and equipment `ObjId`s on `Zone.combatChain` defending this link. -/
  defending : List ObjId := []
  /-- Number of cards defended from hand on this link for Dominate (CR 8.3.4) and Reprise (CR 8.3.8). -/
  defendedFromHandCount : Nat := 0
  /-- Number of action cards defending on this link for Overpower (CR 8.3.26). -/
  defendedActionCount : Nat := 0
  /-- Whether this link's attack hit during the Damage Step (CR 7.5.3). -/
  hit : Bool := false
  /-- Amount of physical damage dealt by this link during the Damage Step (CR 7.5.2). -/
  damageDealt : Nat := 0
  /-- Whether Go Again +1 AP has already been granted during Resolution Step (CR 7.6.2). -/
  goAgainGranted : Bool := false
deriving DecidableEq, Repr

/-- Active Combat Chain state while a combat chain is open (CR 3.5, 7.0).
`links` stores the most recent (active) chain link at the head (`links.head?`), followed by
previous links in reverse chronological order so Combo checks `links[1]?` in O(1). -/
structure CombatChain where
  /-- Current step of the active chain link. -/
  step : CombatStep
  /-- Chain links on this combat chain, head being the active link. -/
  links : List ChainLink := []
deriving DecidableEq, Repr

/-- Active (most recent) chain link on a combat chain, if any. -/
def CombatChain.activeLink? (cc : CombatChain) : Option ChainLink :=
  cc.links.head?

/-- Previous chain link on a combat chain, used for Combo checks (CR 8.3.6). -/
def CombatChain.prevLink? (cc : CombatChain) : Option ChainLink :=
  match cc.links with
  | _ :: prev :: _ => some prev
  | _ => none

/-- Replace the active (head) chain link of a combat chain. -/
def CombatChain.updateActiveLink (cc : CombatChain) (f : ChainLink → ChainLink) : CombatChain :=
  match cc.links with
  | cur :: older => { cc with links := f cur :: older }
  | [] => cc

end Fab

end
