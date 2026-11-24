module

public import Fab.Rules.Move
public import Fab.Rules.Reorder
public import Fab.Rules.Actions.Draw

/-!
# Frame transitions and automatic work (`microStep`)

Implements applying player/chance answers (`applyFrame`, `applyAction`) and single-step
automatic work (`microStep`) for the Start-of-Game Procedure (CR 4.1) and concession (CR 4.5).
-/

@[expose] public section

namespace Fab

/-- Clockwise turn order starting from `first` among `n` seated players (CR 4.1.3). -/
def clockwiseFrom (n : Nat) (first : PlayerId) : List PlayerId :=
  (List.range n).map fun i => ⟨(first.n + i) % n⟩

/-- Look up the `CardDef` of an object in `s.cards`. -/
def GameState.cardDefOf? (s : GameState) (id : ObjId) : Option CardDef :=
  match s.obj? id with
  | none => none
  | some o =>
    match o.kind.cardId? with
    | none => none
    | some cid => s.cards.find? cid

/-- Whether a weapon zone currently holds a two-handed weapon (CR 3.16). -/
def GameState.hasTwoHandedEquipped (s : GameState) (p : PlayerId) : Bool :=
  (s.zone (.player p .weapon)).any fun wid =>
    match s.cardDefOf? wid with
    | some c => c.isTwoHanded
    | none => false

/-- Determine the target arena zone when player `p` equips card `id` from inventory during
Start-of-Game loadout, or `none` if `id` cannot be legally equipped right now (CR 4.1.4). -/
def loadoutEquipDest? (s : GameState) (p : PlayerId) (id : ObjId) : Option Zone :=
  if id ∈ s.zone (.player p .inventory) then
    match s.cardDefOf? id with
    | none => none
    | some c =>
      match c.equipSlot? with
      | some .head =>
        if (s.zone (.player p .head)).isEmpty then some (.player p .head) else none
      | some .chest =>
        if (s.zone (.player p .chest)).isEmpty then some (.player p .chest) else none
      | some .arms =>
        if (s.zone (.player p .arms)).isEmpty then some (.player p .arms) else none
      | some .legs =>
        if (s.zone (.player p .legs)).isEmpty then some (.player p .legs) else none
      | none =>
        let ws := s.zone (.player p .weapon)
        if c.isTwoHanded then
          if ws.isEmpty then some (.player p .weapon) else none
        else if c.isOneHanded || c.isOffHand then
          if ws.length < 2 && !s.hasTwoHandedEquipped p then some (.player p .weapon) else none
        else
          none
  else
    none

/-- Whether player `p` may move `id` from inventory to their starting deck during loadout
(CR 4.1.4). -/
def loadoutCanAddDeck (s : GameState) (p : PlayerId) (id : ObjId) : Bool :=
  if id ∈ s.zone (.player p .inventory) then
    match s.cardDefOf? id with
    | some c => c.isDeckCard
    | none => false
  else
    false

/-- Whether player `p` has enough cards in their starting deck to finish loadout for the
configured format (CR 4.1.4). -/
def loadoutCanFinish (s : GameState) (p : PlayerId) : Bool :=
  decide (s.config.format.spec.deckSize.Satisfied (s.zone (.player p .deck)).length)

/-- Hero intellect of player `p`, defaulting to 4 if absent (CR 2.4, 4.1.6). -/
def GameState.intellectOf (s : GameState) (p : PlayerId) : Nat :=
  match s.zone (.player p .hero) with
  | hid :: _ =>
    match s.cardDefOf? hid with
    | some c => c.front.intellect.getD 4
    | none => 4
  | [] => 4

/-- Flip a single object face-up if it is in an arena equipment/weapon zone and does not have
`Cloaked` (CR 4.1.4). -/
def revealObject (db : CardDB) (o : Object) : Object :=
  let isCloaked :=
    match o.kind.cardId? with
    | some cid =>
      match db.find? cid with
      | some c => c.front.keywords.contains .cloaked
      | none => false
    | none => false
  if isCloaked then o else { o with faceDown := false }

/-- `revealObject` preserves `kind`. -/
theorem revealObject_kind (db : CardDB) (o : Object) :
    (revealObject db o).kind = o.kind := by
  unfold revealObject
  dsimp only
  split <;> (try split) <;> (try split) <;> rfl

/-- `revealObject` preserves `owner`. -/
theorem revealObject_owner (db : CardDB) (o : Object) :
    (revealObject db o).owner = o.owner := by
  unfold revealObject
  dsimp only
  split <;> (try split) <;> (try split) <;> rfl

/-- All equipped armor and weapon object identifiers across all players. -/
def loadoutArenaIds (s : GameState) : List ObjId :=
  (allPlayers s.playerCount).flatMap fun p =>
    s.zone (.player p .head) ++ s.zone (.player p .chest) ++
    s.zone (.player p .arms) ++ s.zone (.player p .legs) ++
    s.zone (.player p .weapon)

/-- Simultaneously reveal all non-Cloaked equipped armor and weapon cards across all players
(CR 4.1.4). -/
def revealAllLoadouts (s : GameState) : GameState :=
  let objs' := (loadoutArenaIds s).foldl (fun m id =>
    match m[id.n]? with
    | some o => m.insert id.n (revealObject s.cards o)
    | none => m) s.objects
  { s with objects := objs' }

/-- Helper lemma: updating existing entries in `objects` via `foldl` preserves key membership,
`kind`, and `owner`. -/
theorem foldl_reveal_preserves (db : CardDB) (ids : List ObjId) (m : Std.ExtTreeMap Nat Object) :
    let m' := ids.foldl (fun acc id =>
      match acc[id.n]? with
      | some o => acc.insert id.n (revealObject db o)
      | none => acc) m
    (∀ (k : Nat), k ∈ m' ↔ k ∈ m) ∧
    (∀ (k : Nat), (m'[k]?).map Object.kind = (m[k]?).map Object.kind) ∧
    (∀ (k : Nat), (m'[k]?).map Object.owner = (m[k]?).map Object.owner) := by
  induction ids generalizing m with
  | nil => exact ⟨fun _ => Iff.rfl, fun _ => rfl, fun _ => rfl⟩
  | cons id rest ih =>
    dsimp only [List.foldl_cons]
    cases hg : m[id.n]? with
    | none => exact ih m
    | some o =>
      dsimp only
      have hin : id.n ∈ m := Std.ExtTreeMap.mem_iff_isSome_getElem?.mpr (by rw [hg]; rfl)
      have hstep := ih (m.insert id.n (revealObject db o))
      refine ⟨?_, ?_, ?_⟩
      · intro k
        rw [hstep.1 k]
        simp only [Std.ExtTreeMap.mem_insert, Nat.compare_eq_eq]
        constructor
        · rintro (rfl | hk); exact hin; exact hk
        · intro hk; exact Or.inr hk
      · intro k
        rw [hstep.2.1 k]
        by_cases hk : id.n = k
        · subst hk
          simp only [Std.ExtTreeMap.getElem?_insert, Nat.compare_eq_eq, ↓reduceIte, hg,
            Option.map_some, revealObject_kind]
        · simp only [Std.ExtTreeMap.getElem?_insert, Nat.compare_eq_eq, hk, ↓reduceIte]
      · intro k
        rw [hstep.2.2 k]
        by_cases hk : id.n = k
        · subst hk
          simp only [Std.ExtTreeMap.getElem?_insert, Nat.compare_eq_eq, ↓reduceIte, hg,
            Option.map_some, revealObject_owner]
        · simp only [Std.ExtTreeMap.getElem?_insert, Nat.compare_eq_eq, hk, ↓reduceIte]

/-- `revealAllLoadouts` preserves `WF`. -/
theorem revealAllLoadouts_wf {s : GameState} (hwf : s.WF) :
    (revealAllLoadouts s).WF := by
  unfold revealAllLoadouts
  exact GameState.WF.congr_mem hwf rfl
    (foldl_reveal_preserves s.cards (loadoutArenaIds s) s.objects).1 rfl rfl

/-- `revealAllLoadouts` preserves `OwnerOk`. -/
theorem revealAllLoadouts_ownerOk {s : GameState} (hok : s.OwnerOk) :
    (revealAllLoadouts s).OwnerOk := by
  refine ⟨fun p k hk id hid o hobj => ?_⟩
  have hown := (foldl_reveal_preserves s.cards (loadoutArenaIds s) s.objects).2.2 id.n
  change (revealAllLoadouts s).objects[id.n]? = some o at hobj
  have hzone : (revealAllLoadouts s).zone (.player p k) = s.zone (.player p k) := rfl
  rw [hzone] at hid
  unfold revealAllLoadouts at hobj
  dsimp only at hobj
  rw [hobj] at hown
  cases hg : s.objects[id.n]? with
  | none => rw [hg] at hown; simp at hown
  | some o0 =>
    rw [hg] at hown
    simp only [Option.map_some, Option.some.injEq] at hown
    rw [hown]
    exact hok.owner p k hk id hid o0 hg

/-- `revealAllLoadouts` preserves `physIds` (I1). -/
theorem revealAllLoadouts_physIds (s : GameState) :
    (revealAllLoadouts s).physIds = s.physIds := by
  unfold GameState.physIds
  have hids : (revealAllLoadouts s).zoneIds = s.zoneIds := rfl
  rw [hids]
  apply filterMap_congr_mem
  intro id _
  have hk := (foldl_reveal_preserves s.cards (loadoutArenaIds s) s.objects).2.1 id.n
  simp only [GameState.obj?, revealAllLoadouts]
  cases h1 : ((loadoutArenaIds s).foldl (fun m id =>
      match m[id.n]? with
      | some o => m.insert id.n (revealObject s.cards o)
      | none => m) s.objects)[id.n]? with
  | none =>
    rw [h1] at hk
    cases h2 : s.objects[id.n]? with
    | none => rfl
    | some o2 => rw [h2] at hk; simp at hk
  | some o1 =>
    rw [h1] at hk
    cases h2 : s.objects[id.n]? with
    | none => rw [h2] at hk; simp at hk
    | some o2 =>
      rw [h2] at hk
      simp only [Option.map_some, Option.some.injEq] at hk
      simp [hk]

/-- Apply a decision answer to the top frame of `s.pending` (CR 4.1). -/
def applyFrame (s : GameState) (a : Action) : Option (GameState × List Event) :=
  match s.pending, a.actor, a.kind with
  | .chanceFirstPlayer :: rest, .chance, .chanceFirstChooser chooser =>
    some ({ s with pending := .chooseFirstPlayer chooser :: rest }, [])
  | .chooseFirstPlayer chooser :: rest, .player p, .pickFirstPlayer first =>
    if p = chooser then
      let order := clockwiseFrom s.playerCount first
      let loadouts := order.map Frame.chooseLoadout
      let shuffles := order.map fun q => Frame.chanceShuffle (.player q .deck)
      some ({ s with
                turnOrder := order
                active := some first
                pending := loadouts ++ [.revealLoadouts] ++ shuffles ++ [.openingDraws] ++ rest },
            [])
    else
      none
  | .chooseLoadout p :: rest, .player q, .loadoutEquip id =>
    if p = q then
      match loadoutEquipDest? s p id with
      | none => none
      | some dst =>
        match moveObj s id dst .top true with
        | none => none
        | some (s1, id') =>
          some ({ s1 with pending := .chooseLoadout p :: rest },
                [.moved id id' (.player p .inventory) dst])
    else
      none
  | .chooseLoadout p :: rest, .player q, .loadoutToDeck id =>
    if p = q ∧ loadoutCanAddDeck s p id = true then
      match moveObj s id (.player p .deck) .bottom false with
      | none => none
      | some (s1, id') =>
        some ({ s1 with pending := .chooseLoadout p :: rest },
              [.moved id id' (.player p .inventory) (.player p .deck)])
    else
      none
  | .chooseLoadout p :: rest, .player q, .loadoutDone =>
    if p = q ∧ loadoutCanFinish s p = true then
      some ({ s with pending := rest }, [])
    else
      none
  | .chanceShuffle z :: rest, .chance, .shuffleOrder l =>
    some ({ s.reorder z l with pending := rest }, [])
  | _, _, _ => none

/-- Apply any legal `Action` (either concession in 1v1 or an answer to the top frame). -/
def applyAction (s : GameState) (a : Action) : Option (GameState × List Event) :=
  match a.actor, a.kind with
  | .player p, .concede =>
    let winners := (allPlayers s.playerCount).filter (· != p)
    some ({ s with result := some (.won winners), pending := [] }, [])
  | _, _ => applyFrame s a

/-- Advance a single automatic work frame on top of `s.pending` (non-recursive: design.md §6.1). -/
def microStep (s : GameState) : Option (GameState × List Event) :=
  match s.pending with
  | .revealLoadouts :: rest =>
    let s1 := revealAllLoadouts s
    some ({ s1 with pending := rest }, [])
  | .openingDraws :: rest =>
    let draws := s.turnOrder.map fun p => Frame.draw p (s.intellectOf p)
    some ({ s with pending := draws ++ rest }, [])
  | .draw _ 0 :: rest =>
    some ({ s with pending := rest }, [])
  | .draw p (n + 1) :: rest =>
    let (s1, es) := drawOne s p
    some ({ s1 with pending := .draw p n :: rest }, es)
  | _ => none

end Fab

end
