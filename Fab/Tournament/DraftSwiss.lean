module

public import Fab.Tournament.Match

public section

namespace Fab.DraftSwiss

/-- A single draft pod plays three best-of-one Swiss rounds. -/
def roundCount : Nat := 3

/-- A pairing uses pod seats; a game's local players 0 and 1 follow this order. -/
structure Table where
  /-- The seat that plays as local player zero. -/
  first : Nat
  /-- The seat that plays as local player one. -/
  second : Nat
  /-- The recorded best-of-one outcome, in local player IDs. -/
  outcome : Option MatchOutcome := none
deriving DecidableEq, Repr

/-- A round's four tables. -/
abbrev Round := List Table

/-- The initial seat permutation breaks otherwise equal pairings and standings. -/
structure State where
  /-- One shuffled permutation of all eight seats. -/
  order : List Nat
  /-- Closed rounds in chronological order. -/
  previous : List Round
  /-- Tables and results for the current round. -/
  current : Round
deriving Repr

/-- One-based number of the current round. -/
def State.round (s : State) : Nat := s.previous.length + 1

/-- Whether every table in the current round has a result. -/
def State.roundDecided (s : State) : Bool :=
  s.current.all (·.outcome.isSome)

/-- Whether the third round has been decided. -/
def State.finished (s : State) : Bool :=
  s.round == roundCount && s.roundDecided

/-- Whether the pod seat is playing at this table. -/
def Table.contains (t : Table) (seat : Nat) : Bool :=
  t.first == seat || t.second == seat

/-- Opponent of a seat belonging to this table. -/
def Table.opponent (t : Table) (seat : Nat) : Nat :=
  if t.first == seat then t.second else t.first

/-- Record only a valid, first result at a table in the current round. -/
def State.record (s : State) (index : Nat) (result : GameResult) : Option State := do
  let table ← s.current[index]?
  if table.outcome.isSome then none else do
    let outcome ← (MatchState.swissBo1.recordGame result).outcome
    let invalid := match outcome with | .winner p => decide (p.n > 1) | .draw _ => false
    if invalid then none
    else return { s with current := s.current.set index { table with outcome := some outcome } }

private def matchings : Nat → List Nat → List Round
  | _, [] => [[]]
  | 0, _ => []
  | n + 1, first :: rest => rest.zipIdx.flatMap fun (second, i) =>
      (matchings n (rest.eraseIdx i)).map (fun tables => ⟨first, second, none⟩ :: tables)

/-- The record and exact comparison numerators for TRP A.4 within a pod without byes. -/
structure Standing where
  /-- The seat in the pod. -/
  seat : Nat
  /-- Wins, equal to match points in a pod without byes. -/
  wins : Nat
  /-- Losses in the completed rounds. -/
  losses : Nat
  /-- Draws in the completed rounds. -/
  draws : Nat
  /-- Cumulative match points numerator. -/
  cumulative : Nat
  /-- Sum of the opponents' loss counts. -/
  opponentLosses : Nat
  /-- Sum of the opponents' cumulative match points numerators. -/
  opponentCumulative : Nat
deriving DecidableEq, Repr

private def score (rounds : List Round) (seat : Nat) : Standing :=
  rounds.zipIdx.foldl (fun standing (tables, index) =>
    match tables.find? (·.contains seat) with
    | none => standing
    | some table =>
      match table.outcome with
      | some (.winner p) =>
        if seat == (if p.n == 0 then table.first else table.second) then
          -- The zero-based index gives weight 2^R - 2^(r-1); the denominator is common.
          { standing with wins := standing.wins + 1
                          cumulative := standing.cumulative + (2 ^ rounds.length - 2 ^ index) }
        else { standing with losses := standing.losses + 1 }
      | some (.draw _) => { standing with draws := standing.draws + 1 }
      | none => standing) ⟨seat, 0, 0, 0, 0, 0, 0⟩

private def compareKeys : List Nat → List Nat → Ordering
  | [], [] => .eq
  | [], _ => .lt
  | _, [] => .gt
  | a :: as, b :: bs => match compare a b with
    | .eq => compareKeys as bs
    | other => other

private def rankSeats (order : List Nat) (rounds : List Round) : List Standing :=
  let records := order.map (score rounds)
  let decorate (row : Standing) :=
    let opponents := rounds.filterMap fun tables =>
      (tables.find? (·.contains row.seat)).map (·.opponent row.seat)
    let peers := opponents.filterMap fun seat => records.find? (·.seat == seat)
    { row with opponentLosses := (peers.map (·.losses)).sum
               opponentCumulative := (peers.map (·.cumulative)).sum }
  let key (row : Standing) :=
    [row.wins, row.cumulative, rounds.length - row.losses,
      rounds.length ^ 2 - row.opponentLosses, row.opponentCumulative]
  (records.map decorate).mergeSort fun a b => compareKeys (key a) (key b) != .lt

/-- Standings incorporate the current round only once all four matches are decided. -/
def State.standings (s : State) : List Standing :=
  rankSeats s.order (if s.roundDecided then s.previous ++ [s.current] else s.previous)

private def pairings (order : List Nat) (rounds : List Round) : Option Round :=
  let prior := rounds.flatten
  let points (seat : Nat) := (score rounds seat).wins
  let played (table : Table) := prior.any fun other =>
    other.contains table.first && other.contains table.second
  -- Try all 105 perfect matchings for eight seats. Prefer the most same-score pairs,
  -- then the lowest combined score gap. Equal costs preserve the seeded seat order.
  let cost (tables : Round) :=
    let gaps := tables.map fun t =>
      let a := points t.first
      let b := points t.second
      max a b - min a b
    [gaps.countP (· != 0), gaps.sum]
  let candidates := (matchings 4 order).filter (fun tables => !tables.any played)
  (candidates.mergeSort fun a b => compareKeys (cost a) (cost b) != .gt).head?

/-- Start with exactly the eight seats, in a caller-supplied random order. -/
def start (order : List Nat) : Option State := do
  if order.mergeSort != List.range 8 then none else do
    let current ← pairings order []
    return ⟨order, [], current⟩

/-- Advance after all current matches report an outcome, up to the third round. -/
def State.next (s : State) : Option State := do
  if !s.roundDecided || s.finished then none else do
    let completed := s.previous ++ [s.current]
    let current ← pairings s.order completed
    return { s with previous := completed, current }

end Fab.DraftSwiss

end
