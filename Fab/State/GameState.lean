module

public import Fab.State.Zone
public import Fab.State.Object
public import Fab.State.GameConfig
public import Fab.State.Event
public import Fab.State.Phase
public import Fab.State.Decision
public import Fab.Tournament.TimeLimit
public import Fab.Rules.Continuous
public import Fab.Rules.Replacement
public import Fab.Rules.Triggers
public import Fab.Core.Cost
public import Fab.Card.CardDB
public import Std.Data.ExtTreeMap

/-!
# Game state and structural invariants

The game state holds the fixed `config` and `cards` (`CardDB`), the object table (`Std.ExtTreeMap`),
the zone lists (source of truth for object locations), per-player asset pools, hero life totals,
and monotonic counters (design.md §5.2-5.3).

Structural well-formedness `WF` and Non-Arena ownership `OwnerOk` are defined here so every
primitive can state and prove its preservation independently.
-/

@[expose] public section

namespace Fab

/-- Per-layer metadata tracked while a card or ability layer sits on the stack (CR 5.1, 5.3). -/
structure LayerInfo where
  /-- Player who played or activated this layer. -/
  controller : PlayerId
  /-- Whether this card-layer was played from the player's arsenal (Tome of Fyendal, Unmovable). -/
  fromArsenal : Bool := false
  /-- Chosen modal index when the card has play-time `ModeSpec`s (CR 5.1.2a). -/
  modeIdx : Option Nat := none
  /-- Hero declared as a target before paying for a card-layer (CR 5.1.4a). -/
  heroTarget : Option PlayerId := none
  /-- Whether this layer has Go Again on resolution (CR 5.3.4, 8.3.5). -/
  goAgain : Bool := false
  /-- Power granted to an attack card before the card enters the combat chain. -/
  attackPowerBonus : Int := 0
  /-- Keywords granted to an attack card before the card enters the combat chain. -/
  attackKeywords : List KeywordInst := []
  /-- Optional explicit effect body for triggered/activated ability layers (CR 6.6). -/
  triggerEffect : Option Effect := none
deriving DecidableEq, Repr

/-- Snapshot of mutable board state saved at the start of playing a card so illegal or unpayable
plays roll back cleanly to the exact pre-play state (CR 5.1.1). -/
structure BoardSnapshot where
  /-- Saved object table. -/
  objects : Std.ExtTreeMap Nat Object
  /-- Saved zone contents. -/
  zones : Std.ExtTreeMap Nat (List ObjId)
  /-- Saved per-player asset pools. -/
  pools : Std.ExtTreeMap Nat AssetPool
  /-- Saved per-player hero life totals. -/
  heroLife : Std.ExtTreeMap Nat Int
  /-- Saved `nextId` counter. -/
  nextId : Nat
  /-- Saved `nextTimestamp` counter. -/
  nextTimestamp : Nat
  /-- Saved continuation stack (starts with the `priority` frame where play was announced). -/
  pending : List Frame
  /-- Saved stack layer metadata. -/
  layerMeta : Std.ExtTreeMap Nat LayerInfo
  /-- Saved combat chain state. -/
  combat : Option CombatChain := none
  /-- Saved active continuous effects. -/
  activeEffects : List ContinuousEffect := []
  /-- Saved pending triggered abilities. -/
  pendingTriggers : List PendingTrigger := []
  /-- Saved delayed triggered abilities. -/
  delayedTriggers : List DelayedTrigger := []
  /-- Saved recorded replacement-effect choices. -/
  chosenReplacements : List (Option Nat) := []
  /-- Saved list of currently Marked players (CR 8.5.48). -/
  markedPlayers : List PlayerId := []
  /-- Saved active replacement / prevention effects (CR 6.4-6.5). -/
  activeReplacements : List ReplacementEffect := []
  /-- Saved players who charged their hero's soul this turn. -/
  chargedThisTurn : List PlayerId := []
  /-- Saved players who banished a 6+ power card this turn. -/
  banishedSixPowerThisTurn : List PlayerId := []
  /-- Saved once-per-turn activated ability usages `(objId, abilityIdx)`. -/
  activatedThisTurn : List (ObjId × Nat) := []
deriving DecidableEq, Repr

/-- Complete state of a Flesh and Blood game (M2-M5 core). -/
structure GameState where
  /-- Fixed ruleset, format, mode, and ban list (design.md §6.1). -/
  config : GameConfig
  /-- Fixed logical card database read by the engine (design.md §6.1). -/
  cards : CardDB
  /-- Object attribute table keyed by `ObjId.n` (extensional map for `DecidableEq`). -/
  objects : Std.ExtTreeMap Nat Object := ∅
  /-- Contents of every zone keyed by `Zone.key`. Missing entry means empty list. -/
  zones : Std.ExtTreeMap Nat (List ObjId) := ∅
  /-- Per-player turn-scoped asset pools (AP, Resource, Chi) keyed by `PlayerId.n` (CR 1.14.2). -/
  pools : Std.ExtTreeMap Nat AssetPool := ∅
  /-- Per-player hero life totals keyed by `PlayerId.n` (CR 2.5). -/
  heroLife : Std.ExtTreeMap Nat Int := ∅
  /-- Next `ObjId` counter (CR 3.0.9). -/
  nextId : Nat := 0
  /-- Next `Timestamp` counter (CR 6.3.3). -/
  nextTimestamp : Nat := 0
  /-- Turn counter (0 before first turn begins). -/
  turn : Nat := 0
  /-- Current turn-player, once the game has started (CR 4.0). -/
  active : Option PlayerId := none
  /-- Continuation stack; head is the active frame (design.md §6.2). -/
  pending : List Frame := []
  /-- Clockwise turn order starting from the first-turn player (CR 4.1.3). -/
  turnOrder : List PlayerId := []
  /-- Current phase of the game (CR 4.1-4.4). -/
  phase : Phase := .setup
  /-- Final game outcome once the game has ended, `none` while ongoing (CR 4.5). -/
  result : Option GameResult := none
  /-- Metadata for layers currently on the stack, keyed by `ObjId.n` (CR 5.1, 5.3). -/
  layerMeta : Std.ExtTreeMap Nat LayerInfo := ∅
  /-- Saved pre-play snapshot while playing a card, used for play rollback (CR 5.1.1). -/
  playRollback : Option BoardSnapshot := none
  /-- Active Combat Chain state when a combat chain is open, `none` when closed (CR 3.5, 7.0). -/
  combat : Option CombatChain := none
  /-- Per-game tournament clock and intentional-draw state (TRP 4). -/
  tournament : TournamentState := {}
  /-- Active continuous effects evaluated by the 8-stage `characteristics` engine (CR 6.2-6.3). -/
  activeEffects : List ContinuousEffect := []
  /-- Pending triggered abilities waiting to be stacked via `flushTriggers` (CR 6.6). -/
  pendingTriggers : List PendingTrigger := []
  /-- Active delayed triggers waiting for future phases/events (CR 6.6.3). -/
  delayedTriggers : List DelayedTrigger := []
  /-- Replacement-effect choices recorded via `chooseReplacement` (CR 6.5.1). -/
  chosenReplacements : List (Option Nat) := []
  /-- Players currently Marked by Mark effects (CR 8.5.48). -/
  markedPlayers : List PlayerId := []
  /-- Active replacement and damage-prevention effects evaluated on proposed events (CR 6.4-6.5). -/
  activeReplacements : List ReplacementEffect := []
  /-- Players who have charged their hero's soul this turn (CR 8.5). -/
  chargedThisTurn : List PlayerId := []
  /-- Players who have banished a card with `≥ 6{p}` this turn (MON: Levia / Shadow Brute). -/
  banishedSixPowerThisTurn : List PlayerId := []
  /-- Once-per-turn activated abilities already used this turn (CR 5.2). -/
  activatedThisTurn : List (ObjId × Nat) := []
deriving DecidableEq, Repr

/-- List of every valid zone in an `n`-player game (CR 3.0). -/
def allZones (n : Nat) : List Zone :=
  Zone.combatChain :: Zone.stack ::
    (List.range n).flatMap (fun i => ZoneKind.all.map (Zone.player ⟨i⟩))

/-- Whether `z` is a valid zone in an `n`-player game. -/
def Zone.Valid (n : Nat) (z : Zone) : Prop :=
  z ∈ allZones n

instance Zone.decidableValid (n : Nat) (z : Zone) : Decidable (z.Valid n) := by
  unfold Zone.Valid
  infer_instance

/-- Every zone appears once in `allZones n`. -/
theorem allZones_nodup (n : Nat) : (allZones n).Nodup := by
  unfold allZones
  rw [List.nodup_cons, List.nodup_cons]
  refine ⟨?_, ?_, ?_⟩
  · simp
  · simp
  · show List.Pairwise (· ≠ ·) _
    rw [List.pairwise_flatMap]
    refine ⟨fun i _ => ?_, ?_⟩
    · show List.Pairwise (· ≠ ·) _
      refine List.Pairwise.map (Zone.player ⟨i⟩) ?_ ZoneKind.all_nodup
      intro a b hab h
      simp only [Zone.player.injEq, true_and] at h
      exact hab h
    · refine List.Pairwise.imp ?_ List.nodup_range
      intro a b hab x hxa y hxb
      simp only [List.mem_map] at hxa hxb
      obtain ⟨k, -, rfl⟩ := hxa
      obtain ⟨l, -, rfl⟩ := hxb
      intro h
      simp only [Zone.player.injEq, PlayerId.mk.injEq] at h
      exact hab h.1

/-- Every player zone of a seated player is valid. -/
theorem Zone.valid_player {n : Nat} {p : PlayerId} (h : p.n < n) (k : ZoneKind) :
    (Zone.player p k).Valid n := by
  unfold Zone.Valid allZones
  simp only [List.mem_cons, List.mem_flatMap, List.mem_range, List.mem_map]
  right; right
  exact ⟨p.n, h, k, ZoneKind.mem_all k, rfl⟩

/-- The shared Combat Chain zone is valid. -/
theorem Zone.valid_combatChain (n : Nat) : Zone.combatChain.Valid n := by
  simp [Zone.Valid, allZones]

/-- The shared Stack zone is valid. -/
theorem Zone.valid_stack (n : Nat) : Zone.stack.Valid n := by
  simp [Zone.Valid, allZones]

namespace GameState

/-- Number of seated players in the game. -/
def playerCount (s : GameState) : Nat :=
  s.config.mode.playerCount

/-- Contents of zone `z`. -/
def zone (s : GameState) (z : Zone) : List ObjId :=
  s.zones.getD z.key []

/-- Replace the contents of zone `z`. -/
def setZone (s : GameState) (z : Zone) (l : List ObjId) : GameState :=
  { s with zones := s.zones.insert z.key l }

/-- Look up an object's attributes by `ObjId`. -/
def obj? (s : GameState) (id : ObjId) : Option Object :=
  s.objects[id.n]?

/-- Look up the `CardDef` of an object in `s.cards`. -/
def cardDefOf? (s : GameState) (id : ObjId) : Option CardDef :=
  match s.obj? id with
  | none => none
  | some o =>
    match o.kind.cardId? with
    | none => none
    | some cid => s.cards.find? cid

/-- Current turn-scoped asset pool of player `p` (CR 1.14.2). -/
def poolOf (s : GameState) (p : PlayerId) : AssetPool :=
  s.pools.getD p.n AssetPool.empty

/-- Replace the asset pool of player `p`. -/
def setPool (s : GameState) (p : PlayerId) (pool : AssetPool) : GameState :=
  { s with pools := s.pools.insert p.n pool }

/-- Current hero life total of player `p` (CR 2.5). -/
def lifeOf (s : GameState) (p : PlayerId) : Int :=
  s.heroLife.getD p.n 0

/-- Replace the hero life total of player `p`. -/
def setLife (s : GameState) (p : PlayerId) (life : Int) : GameState :=
  { s with heroLife := s.heroLife.insert p.n life }

/-- Concatenation of all object identifiers across all valid zones. -/
def zoneIds (s : GameState) : List ObjId :=
  (allZones s.playerCount).flatMap s.zone

/-- All physical card identifiers across all zones. Tokens, layers, and attack-proxies have none
(I1: design.md §5.1). -/
def physIds (s : GameState) : List PhysId :=
  s.zoneIds.filterMap (fun id => (s.obj? id).bind (·.kind.phys?))

/-- Reading a zone just written yields the written list. -/
theorem zone_setZone_self (s : GameState) (z : Zone) (l : List ObjId) :
    (s.setZone z l).zone z = l := by
  simp [zone, setZone]

/-- Writing a zone does not change any other zone. -/
theorem zone_setZone_ne (s : GameState) {z z' : Zone} (h : z' ≠ z) (l : List ObjId) :
    (s.setZone z l).zone z' = s.zone z' := by
  have hk : z'.key ≠ z.key := fun e => h (Zone.key_inj e)
  have hk' : z.key ≠ z'.key := fun e => hk e.symm
  simp [zone, setZone, Std.ExtTreeMap.getD_insert, hk']

/-- Reading a pool just written yields the written pool. -/
theorem poolOf_setPool_self (s : GameState) (p : PlayerId) (pool : AssetPool) :
    (s.setPool p pool).poolOf p = pool := by
  simp [poolOf, setPool]

/-- Writing player `p`'s pool does not change another player `q`'s pool. -/
theorem poolOf_setPool_ne (s : GameState) {p q : PlayerId} (h : q ≠ p) (pool : AssetPool) :
    (s.setPool p pool).poolOf q = s.poolOf q := by
  have hn : p.n ≠ q.n := fun e => h (by cases p; cases q; simp_all)
  simp [poolOf, setPool, Std.ExtTreeMap.getD_insert, hn]

/-- Structural well-formedness `WF` holding in every intermediate state (design.md §5.3):
1. Each `ObjId` appears in at most one zone (I2 position uniqueness).
2. Every `ObjId` on a zone has an entry in `objects`.
3. Every entry in `objects` appears on some zone.
4. Every `ObjId` on a zone is strictly below `nextId`.
5. Every key in `zones` corresponds to a valid zone in `allZones s.playerCount`. -/
structure WF (s : GameState) : Prop where
  /-- Each `ObjId` sits in exactly one place (`zoneIds` has no duplicates). -/
  nodup : s.zoneIds.Nodup
  /-- Every `ObjId` on a zone exists in `objects`. -/
  table_of_zone : ∀ id ∈ s.zoneIds, id.n ∈ s.objects
  /-- Every key in `objects` appears on some zone. -/
  zone_of_table : ∀ k, k ∈ s.objects → ∃ id ∈ s.zoneIds, id.n = k
  /-- Every `ObjId` on a zone is below `nextId`. -/
  lt_nextId : ∀ id ∈ s.zoneIds, id.n < s.nextId
  /-- Only valid zones of the game are stored in `zones`. -/
  zones_valid : ∀ k, k ∈ s.zones → ∃ z ∈ allZones s.playerCount, z.key = k

/-- `WF` depends only on `config`, the domain of `objects`, `zones`, and `nextId`. -/
theorem WF.congr_mem {s s2 : GameState} (hwf : s.WF) (hc : s2.config = s.config)
    (ho : ∀ k, k ∈ s2.objects ↔ k ∈ s.objects) (hz : s2.zones = s.zones)
    (hn : s2.nextId = s.nextId) : s2.WF := by
  have hcount : s2.playerCount = s.playerCount := by simp [playerCount, hc]
  have hzone : ∀ z, s2.zone z = s.zone z := fun z => by simp [zone, hz]
  have hids : s2.zoneIds = s.zoneIds := by
    unfold zoneIds
    rw [hcount]
    have : s2.zone = s.zone := funext hzone
    rw [this]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hids]; exact hwf.nodup
  · intro x hx; rw [hids] at hx; exact (ho _).mpr (hwf.table_of_zone x hx)
  · intro k hk; rw [hids]; exact hwf.zone_of_table k ((ho k).mp hk)
  · intro x hx; rw [hids] at hx; rw [hn]; exact hwf.lt_nextId x hx
  · intro k hk; rw [hz] at hk; rw [hcount]; exact hwf.zones_valid k hk

/-- `WF` preserved when `config`, `objects`, `zones`, and `nextId` are unchanged. -/
theorem WF.congr {s s2 : GameState} (hwf : s.WF) (hc : s2.config = s.config)
    (ho : s2.objects = s.objects) (hz : s2.zones = s.zones) (hn : s2.nextId = s.nextId) :
    s2.WF :=
  WF.congr_mem hwf hc (fun k => by rw [ho]) hz hn

/-- Non-Arena ownership invariant `OwnerOk`: every object in a player's Non-Arena zone is owned
by that player (CR 3.0). -/
structure OwnerOk (s : GameState) : Prop where
  /-- Every object in a Non-Arena zone of player `p` has `owner = p`. -/
  owner : ∀ (p : PlayerId) (k : ZoneKind), k.isArena = false →
    ∀ id ∈ s.zone (.player p k), ∀ o, s.obj? id = some o → o.owner = p

/-- `OwnerOk` depends only on `objects` and `zones`. -/
theorem OwnerOk.congr {s s2 : GameState} (h : s.OwnerOk) (ho : s2.objects = s.objects)
    (hz : s2.zones = s.zones) : s2.OwnerOk := by
  refine ⟨fun p k hk id hid o hobj => ?_⟩
  have hzone : s2.zone (.player p k) = s.zone (.player p k) := by simp [zone, hz]
  have hobj' : s2.obj? id = s.obj? id := by simp [obj?, ho]
  rw [hzone] at hid
  rw [hobj'] at hobj
  exact h.owner p k hk id hid o hobj

/-- An empty game state with no objects satisfies `WF`. -/
theorem empty_wf (cfg : GameConfig) (db : CardDB) :
    ({ config := cfg, cards := db } : GameState).WF := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold zoneIds zone
    have : ∀ z ∈ allZones cfg.mode.playerCount,
        (∅ : Std.ExtTreeMap Nat (List ObjId)).getD z.key [] = [] := by
      intro z _; rfl
    have hnil : (allZones cfg.mode.playerCount).flatMap
        (fun z => (∅ : Std.ExtTreeMap Nat (List ObjId)).getD z.key []) = [] := by
      rw [List.flatMap_eq_nil_iff]
      exact this
    change ((allZones cfg.mode.playerCount).flatMap
        (fun z => (∅ : Std.ExtTreeMap Nat (List ObjId)).getD z.key [])).Nodup
    rw [hnil]
    exact List.nodup_nil
  · intro id hid
    exfalso
    unfold zoneIds zone at hid
    rw [List.mem_flatMap] at hid
    obtain ⟨z, _, hz⟩ := hid
    change id ∈ (∅ : Std.ExtTreeMap Nat (List ObjId)).getD z.key [] at hz
    simp at hz
  · intro k hk
    simp at hk
  · intro id hid
    exfalso
    unfold zoneIds zone at hid
    rw [List.mem_flatMap] at hid
    obtain ⟨z, _, hz⟩ := hid
    change id ∈ (∅ : Std.ExtTreeMap Nat (List ObjId)).getD z.key [] at hz
    simp at hz
  · intro k hk
    simp at hk

/-- An empty game state satisfies `OwnerOk`. -/
theorem empty_ownerOk (cfg : GameConfig) (db : CardDB) :
    ({ config := cfg, cards := db } : GameState).OwnerOk := by
  refine ⟨fun p k _ id hid _ _ => ?_⟩
  unfold zone at hid
  change id ∈ (∅ : Std.ExtTreeMap Nat (List ObjId)).getD (Zone.player p k).key [] at hid
  simp at hid

/-- Capture the current board state for potential card-play rollback (CR 5.1.1). -/
def snapshot (s : GameState) : BoardSnapshot :=
  { objects := s.objects
    zones := s.zones
    pools := s.pools
    heroLife := s.heroLife
    nextId := s.nextId
    nextTimestamp := s.nextTimestamp
    pending := s.pending
    layerMeta := s.layerMeta
    combat := s.combat
    activeEffects := s.activeEffects
    pendingTriggers := s.pendingTriggers
    delayedTriggers := s.delayedTriggers
    chosenReplacements := s.chosenReplacements
    markedPlayers := s.markedPlayers
    activeReplacements := s.activeReplacements
    chargedThisTurn := s.chargedThisTurn
    banishedSixPowerThisTurn := s.banishedSixPowerThisTurn
    activatedThisTurn := s.activatedThisTurn }

/-- Restore a saved `BoardSnapshot` and clear `playRollback` (CR 5.1.1). -/
def restore (s : GameState) (snap : BoardSnapshot) : GameState :=
  { s with
    objects := snap.objects
    zones := snap.zones
    pools := snap.pools
    heroLife := snap.heroLife
    nextId := snap.nextId
    nextTimestamp := snap.nextTimestamp
    pending := snap.pending
    layerMeta := snap.layerMeta
    combat := snap.combat
    activeEffects := snap.activeEffects
    pendingTriggers := snap.pendingTriggers
    delayedTriggers := snap.delayedTriggers
    chosenReplacements := snap.chosenReplacements
    markedPlayers := snap.markedPlayers
    activeReplacements := snap.activeReplacements
    chargedThisTurn := snap.chargedThisTurn
    banishedSixPowerThisTurn := snap.banishedSixPowerThisTurn
    activatedThisTurn := snap.activatedThisTurn
    playRollback := none }

/-- Evaluate the 8-stage derived characteristics of object `id` in state `s` (CR 6.3.2). -/
def characteristics (s : GameState) (id : ObjId) : Option DerivedChars :=
  match s.obj? id, s.cardDefOf? id with
  | some o, some c =>
    let face := match o.faceState with
      | .front => c.front
      | .back => c.back.getD c.front
    some (evalCharacteristics s.activeEffects o face id)
  | _, _ => none

/-- Expire all active continuous effects matching duration `dur` (CR 4.4.3, 7.7). -/
def expireEffects (s : GameState) (dur : Duration) : GameState :=
  { s with activeEffects := s.activeEffects.filter fun e => e.duration != dur }

/-- Restoring a snapshot taken from `s` (when `s.playRollback = none`) returns the exact state `s`. -/
theorem restore_snapshot {s : GameState} (h : s.playRollback = none) :
    s.restore s.snapshot = s := by
  cases s
  simp only [restore, snapshot] at *
  subst h
  rfl

/-- Saved rollback snapshot invariant: whenever `playRollback = some snap`, restoring `snap` yields
a `WF`, `OwnerOk` state with a permutation of the current physical card multiset. -/
def RollbackOk (s : GameState) : Prop :=
  ∀ snap, s.playRollback = some snap →
    (s.restore snap).WF ∧ (s.restore snap).OwnerOk ∧ (s.restore snap).physIds.Perm s.physIds

/-- Any state with `playRollback = none` trivially satisfies `RollbackOk`. -/
theorem RollbackOk.of_none {s : GameState} (h : s.playRollback = none) : s.RollbackOk := by
  intro snap hs
  rw [h] at hs
  cases hs

/-- `RollbackOk` is preserved whenever `config` and `playRollback` are unchanged and `physIds` is
a permutation of the old `physIds`. -/
theorem RollbackOk.preserve {s s' : GameState} (hrb : s.RollbackOk)
    (hc : s'.config = s.config) (hr : s'.playRollback = s.playRollback)
    (hp : s'.physIds.Perm s.physIds) : s'.RollbackOk := by
  intro snap hs
  rw [hr] at hs
  obtain ⟨hwf, hok, hperm⟩ := hrb snap hs
  have hwf' : (s'.restore snap).WF := GameState.WF.congr hwf hc rfl rfl rfl
  have hok' : (s'.restore snap).OwnerOk := GameState.OwnerOk.congr hok rfl rfl
  have hphys : (s'.restore snap).physIds = (s.restore snap).physIds := by
    unfold physIds zoneIds playerCount restore zone obj?
    rw [hc]
  refine ⟨hwf', hok', ?_⟩
  rw [hphys]
  exact hperm.trans hp.symm

end GameState

end Fab

end
