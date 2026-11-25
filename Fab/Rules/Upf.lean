module

public import Fab.Rules.CombatKeywords
public import Fab.Rules.Actions.Banish

/-!
# Ultimate Pit Fight (UPF) Multiplayer Rules (M9, CR Chapter 10)

Implements multiplayer (3+ player) Ultimate Pit Fight rules:
- Circular adjacency (`isAdjacentInOrder`, `adjacentOpponents`) enforcing the UPF adjacent-player
  attack restriction (`canAttackTargetUpf`).
- Eliminated player cleanup (`eliminatePlayer`): removes an eliminated player from `turnOrder`,
  removes their non-physical tokens/proxies, and returns their physical cards sitting in other
  zones cleanly to their banished zone while preserving `WF`, `OwnerOk`, and **I1** (`physIds`).
-/

@[expose] public section

namespace Fab

/-- Whether players `a` and `b` are adjacent (immediate clockwise or counter-clockwise neighbors)
in circular seating `order` (CR 10.1). -/
def isAdjacentInOrder (order : List PlayerId) (a b : PlayerId) : Bool :=
  if a == b then false
  else
    match order.idxOf? a, order.idxOf? b with
    | some ia, some ib =>
      let n := order.length
      if n == 0 then false
      else ((ia + 1) % n == ib) || ((ib + 1) % n == ia)
    | _, _ => false

/-- Adjacency in circular seating is irreflexive. -/
theorem isAdjacentInOrder_irrefl (order : List PlayerId) (a : PlayerId) :
    isAdjacentInOrder order a a = false := by
  unfold isAdjacentInOrder
  simp

/-- Adjacency in circular seating is symmetric (CR 10.1). -/
theorem isAdjacentInOrder_symm (order : List PlayerId) (a b : PlayerId) :
    isAdjacentInOrder order a b = isAdjacentInOrder order b a := by
  unfold isAdjacentInOrder
  by_cases hab : a = b
  · subst hab; simp
  · have h1 : (a == b) = false := by simp [hab]
    have h2 : (b == a) = false := by simp [Ne.symm hab]
    rw [h1, h2]
    dsimp only
    cases order.idxOf? a with
    | none =>
      cases order.idxOf? b <;> rfl
    | some ia =>
      cases order.idxOf? b with
      | none => rfl
      | some ib =>
        dsimp only
        cases (order.length == 0) with
        | true => rfl
        | false => exact Bool.or_comm _ _

/-- All players in `order` adjacent to `p` (valid UPF attack targets) (CR 10.1). -/
def adjacentOpponents (order : List PlayerId) (p : PlayerId) : List PlayerId :=
  order.filter fun q => isAdjacentInOrder order p q

/-- Whether `attacker` may legally target `target` with an attack under `s.config.mode`:
in 1v1 duel any distinct seated opponent is valid; in UPF only adjacent players in `s.turnOrder`
may be attacked (CR 10.1). -/
def canAttackTargetUpf (s : GameState) (attacker target : PlayerId) : Bool :=
  match s.config.mode with
  | .duel => attacker != target && s.turnOrder.contains target
  | .upf _ => isAdjacentInOrder s.turnOrder attacker target

/-- Clean up a single object `id` owned by eliminated player `p`: non-physical objects are removed;
physical cards sitting outside `p`'s banished zone are moved face-down into `p`'s banished zone so
no other player's zones or shared zones retain eliminated players' cards (CR 10.1). -/
def cleanupEliminatedObj (s : GameState) (p : PlayerId) (id : ObjId) : GameState :=
  match s.locate id, s.obj? id with
  | some srcZ, some o =>
    if o.owner == p then
      if o.kind.phys?.isNone then
        removeNonPhysObj s id
      else if srcZ == Zone.player p .banished then
        s
      else
        match moveObj s id (.player p .banished) .top true with
        | some (s1, _) => s1
        | none => s
    else
      s
  | _, _ => s

/-- `cleanupEliminatedObj` preserves `WF`, `OwnerOk`, `physIds` (I1), `config`, and `playRollback`. -/
theorem cleanupEliminatedObj_inv {s : GameState} (hwf : s.WF) (hok : s.OwnerOk)
    (p : PlayerId) (id : ObjId) :
    (cleanupEliminatedObj s p id).WF ∧
    (cleanupEliminatedObj s p id).OwnerOk ∧
    (cleanupEliminatedObj s p id).physIds.Perm s.physIds ∧
    (cleanupEliminatedObj s p id).config = s.config ∧
    (cleanupEliminatedObj s p id).playRollback = s.playRollback := by
  unfold cleanupEliminatedObj
  cases s.locate id with
  | none => exact ⟨hwf, hok, List.Perm.refl _, rfl, rfl⟩
  | some srcZ =>
    cases s.obj? id with
    | none => exact ⟨hwf, hok, List.Perm.refl _, rfl, rfl⟩
    | some o =>
      dsimp only
      split
      · split
        · have hm := removeNonPhysObj_meta s id
          exact ⟨removeNonPhysObj_wf hwf id, removeNonPhysObj_ownerOk hok id,
                 removeNonPhysObj_physIds hwf id, hm.1, hm.2⟩
        · split
          · exact ⟨hwf, hok, List.Perm.refl _, rfl, rfl⟩
          · cases hm : moveObj s id (.player p .banished) .top true with
            | none => exact ⟨hwf, hok, List.Perm.refl _, rfl, rfl⟩
            | some res =>
              have hmeta := moveObj_config_rollback hm
              exact ⟨moveObj_wf hwf hm, moveObj_ownerOk hwf hok hm,
                     moveObj_physIds hwf hm, hmeta.1, hmeta.2⟩
      · exact ⟨hwf, hok, List.Perm.refl _, rfl, rfl⟩

/-- Clean up a list of objects belonging to eliminated player `p`. -/
def cleanupEliminatedList (s : GameState) (p : PlayerId) : List ObjId → GameState
  | [] => s
  | id :: rest => cleanupEliminatedList (cleanupEliminatedObj s p id) p rest

/-- `cleanupEliminatedList` preserves `WF`, `OwnerOk`, `physIds` (I1), `config`, and `playRollback`. -/
theorem cleanupEliminatedList_inv (p : PlayerId) :
    ∀ (ids : List ObjId) {s : GameState}, s.WF → s.OwnerOk →
      (cleanupEliminatedList s p ids).WF ∧
      (cleanupEliminatedList s p ids).OwnerOk ∧
      (cleanupEliminatedList s p ids).physIds.Perm s.physIds ∧
      (cleanupEliminatedList s p ids).config = s.config ∧
      (cleanupEliminatedList s p ids).playRollback = s.playRollback
  | [], _, hwf, hok => ⟨hwf, hok, List.Perm.refl _, rfl, rfl⟩
  | id :: rest, s, hwf, hok => by
    unfold cleanupEliminatedList
    obtain ⟨hwf1, hok1, hp1, hc1, hr1⟩ := cleanupEliminatedObj_inv hwf hok p id
    obtain ⟨hwf2, hok2, hp2, hc2, hr2⟩ := cleanupEliminatedList_inv p rest hwf1 hok1
    exact ⟨hwf2, hok2, hp2.trans hp1, hc2.trans hc1, hr2.trans hr1⟩

/-- Eliminate player `p` from a multiplayer UPF game: removes `p`'s objects from shared and other
players' zones, removes `p` from `turnOrder`, sets `p`'s life to 0, and checks hero defeat
(CR 10.1). -/
def eliminatePlayer (s : GameState) (p : PlayerId) : GameState :=
  let s1 := cleanupEliminatedList s p s.zoneIds
  let s2 := { s1.setLife p 0 with
    turnOrder := s1.turnOrder.filter (· != p) }
  checkHeroDefeat s2

/-- `eliminatePlayer` preserves `WF`, `OwnerOk`, `physIds` (I1), `config`, and `playRollback`. -/
theorem eliminatePlayer_inv {s : GameState} (hwf : s.WF) (hok : s.OwnerOk) (p : PlayerId) :
    (eliminatePlayer s p).WF ∧
    (eliminatePlayer s p).OwnerOk ∧
    (eliminatePlayer s p).physIds.Perm s.physIds ∧
    (eliminatePlayer s p).config = s.config ∧
    (eliminatePlayer s p).playRollback = s.playRollback := by
  unfold eliminatePlayer
  obtain ⟨hwf1, hok1, hp1, hc1, hr1⟩ := cleanupEliminatedList_inv p s.zoneIds hwf hok
  let s1 := cleanupEliminatedList s p s.zoneIds
  let s2 : GameState := { s1.setLife p 0 with turnOrder := s1.turnOrder.filter (· != p) }
  have hwf2 : s2.WF := GameState.WF.congr hwf1 rfl rfl rfl rfl
  have hok2 : s2.OwnerOk := GameState.OwnerOk.congr hok1 rfl rfl
  have hp2 : s2.physIds = s1.physIds := rfl
  have hchk_meta : (checkHeroDefeat s2).config = s2.config ∧
      (checkHeroDefeat s2).playRollback = s2.playRollback := by
    unfold checkHeroDefeat
    split
    · exact ⟨rfl, rfl⟩
    · cases livingPlayers s2 with
      | nil => exact ⟨rfl, rfl⟩
      | cons _ ws => cases ws <;> exact ⟨rfl, rfl⟩
  refine ⟨checkHeroDefeat_wf hwf2, checkHeroDefeat_ownerOk hok2, ?_,
          hchk_meta.1.trans hc1, hchk_meta.2.trans hr1⟩
  rw [checkHeroDefeat_physIds, hp2]
  exact hp1

/-- After `eliminatePlayer s p`, player `p` is no longer in `turnOrder` (CR 10.1). -/
theorem eliminatePlayer_removes_from_turnOrder (s : GameState) (p : PlayerId) :
    p ∉ (eliminatePlayer s p).turnOrder := by
  unfold eliminatePlayer
  dsimp only
  have hnot : p ∉ (cleanupEliminatedList s p s.zoneIds).turnOrder.filter (· != p) := by
    simp
  unfold checkHeroDefeat
  split
  · exact hnot
  · cases livingPlayers _ with
    | nil => exact hnot
    | cons _ ws => cases ws <;> exact hnot

/-- In a 4-player UPF seating `[0, 1, 2, 3]`, player 0 is adjacent to players 1 and 3, and NOT
adjacent to opposite player 2 (CR 10.1). -/
theorem upf_4player_adjacency :
    let ord : List PlayerId := [⟨0⟩, ⟨1⟩, ⟨2⟩, ⟨3⟩]
    isAdjacentInOrder ord ⟨0⟩ ⟨1⟩ = true ∧
    isAdjacentInOrder ord ⟨0⟩ ⟨3⟩ = true ∧
    isAdjacentInOrder ord ⟨0⟩ ⟨2⟩ = false ∧
    isAdjacentInOrder ord ⟨1⟩ ⟨3⟩ = false := by
  decide

end Fab

end
