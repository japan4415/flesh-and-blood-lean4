module

public import Fab.Tournament.DraftSwiss
public import FabDriver.BrowserDuel

public section

namespace FabDriver

open Fab

private structure BrowserTable where
  duel : Option BrowserDuel := none
  revision : Nat := 0

/-- Host-side tournament, retained for all three rounds in the browser. -/
structure BrowserSwiss where
  private mk ::
  private draft : BoosterDraft.State
  private event : DraftSwiss.State
  private heroes : Array (Option String)
  private tables : Array BrowserTable
  private rng : Rng

/-- Create the three-round event once the eight-seat draft is complete. -/
@[export fab_swiss_start]
def startBrowserSwiss (draft : BoosterDraft.State) (seed : UInt32) : Option BrowserSwiss := do
  if draft.phase != .complete then none else do
    let (order, rng) := (⟨seed.toUInt64⟩ : Rng).shuffle (List.range 8)
    let event ← DraftSwiss.start order
    return ⟨draft, event, Array.replicate 8 none, Array.replicate 4 {}, rng⟩

private def BrowserSwiss.locate (s : BrowserSwiss) (seat : Nat) :
    Option (Nat × DraftSwiss.Table × Nat) := do
  let (table, index) ← s.event.current.zipIdx.find? fun (table, _) => table.contains seat
  return (index, table, if table.first == seat then 0 else 1)

private def BrowserSwiss.hero (s : BrowserSwiss) (seat : Nat) : Option String :=
  s.heroes[seat]?.join

private def BrowserSwiss.openTable (s : BrowserSwiss) (index : Nat)
    (table : DraftSwiss.Table) : Option BrowserSwiss := do
  let first ← s.hero table.first
  let second ← s.hero table.second
  let (seed, rng) := s.rng.nextNat (2 ^ 32)
  let duel ← startBrowserDuel s.draft table.first table.second first second (UInt32.ofNat seed)
  return { s with tables := s.tables.set! index ⟨some duel, 1⟩, rng }

/-- Lock a drafted hero for this seat. The first match starts once both seats have chosen. -/
@[export fab_swiss_select]
def browserSwissSelect (s : BrowserSwiss) (seat round revision : UInt32)
    (hero : String) : Option BrowserSwiss := do
  if s.event.round != round.toNat || (s.hero seat.toNat).isSome then none else do
    let (index, table, _) ← s.locate seat.toNat
    let current ← s.tables[index]?
    if current.revision != revision.toNat ||
        !(browserDraftHeroes s.draft seat |>.splitOn " " |>.contains hero) || hero.isEmpty then none else do
      let s := { s with heroes := s.heroes.set! seat.toNat (some hero) }
      if (s.hero (table.opponent seat.toNat)).isSome then s.openTable index table else some s

/-- Accept a legal move only at the seat's current board revision and record a terminal result. -/
@[export fab_swiss_move]
def browserSwissMove (s : BrowserSwiss) (seat round revision action : UInt32) : Option BrowserSwiss := do
  if s.event.round != round.toNat then none else do
    let (index, pairing, side) ← s.locate seat.toNat
    let table ← s.tables[index]?
    if table.revision != revision.toNat || pairing.outcome.isSome then none else do
      let duel ← table.duel
      let duel ← browserDuelMove duel (UInt32.ofNat side) action
      let event ← match duel.game.result with
        | none => some s.event
        | some result => s.event.record index result
      return { s with event, tables := s.tables.set! index ⟨some duel, table.revision + 1⟩ }

/-- Close the decided round and deal fresh games for the next pairing using the same draft pool. -/
@[export fab_swiss_next]
def browserSwissNext (s : BrowserSwiss) : Option BrowserSwiss := do
  let event ← s.event.next
  let initial := { s with event, tables := Array.replicate 4 {} }
  event.current.zipIdx.foldlM (fun next (table, index) => next.openTable index table) initial

/-- Public round, pairings, and standings (seat numbers in the browser start at one). -/
@[export fab_swiss_public]
def browserSwissPublic (s : BrowserSwiss) : String :=
  let header := ["v", toString s.event.round, toString DraftSwiss.roundCount,
    if s.event.finished then "final" else if s.event.roundDecided then "review" else "playing"]
  let pairings := s.event.current.map fun table =>
    let result := match table.outcome with
      | none => "-"
      | some (.draw _) => "draw"
      | some (.winner p) => if p.n == 0 then "first" else "second"
    ["p", toString (table.first + 1), toString (table.second + 1), result]
  let standings := s.event.standings.map fun row =>
    ["s", toString (row.seat + 1), toString row.wins, toString row.losses, toString row.draws]
  String.intercalate "\n" ((header :: pairings ++ standings).map (String.intercalate "\t"))

/-- Project the current table to just this seat. The board tail uses the duel's normal codec. -/
@[export fab_swiss_private]
def browserSwissPrivate (s : BrowserSwiss) (seat : UInt32) : String := (do
  let (index, pairing, side) ← s.locate seat.toNat
  let table ← s.tables[index]?
  let ownHero := s.hero seat.toNat
  let header := String.intercalate "\t" [toString (pairing.opponent seat.toNat + 1),
    toString side, toString table.revision, ownHero.getD ""]
  let options := if ownHero.isSome then "" else browserDraftHeroes s.draft seat
  let board := (table.duel.map fun duel => browserDuelView duel (UInt32.ofNat side)).getD ""
  return String.intercalate "\n" [header, options, board]).getD ""

end FabDriver

end
