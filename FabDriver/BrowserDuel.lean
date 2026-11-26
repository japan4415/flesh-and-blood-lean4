module

public import FabDriver.Run

public section

namespace FabDriver

open Fab

/-- Host-side state for one browser duel. Randomness advances only on accepted transitions. -/
structure BrowserDuel where
  /-- Authoritative Lean engine state. -/
  game : GameState
  /-- Randomness for chance frames. -/
  rng : Rng

private def draftChoice (draft : BoosterDraft.State) (seat : PlayerId)
    (hero : CardId) : Option BoosterDraft.DeckChoice := do
  let picks ← (draft.view seat).bind (·.drafted)
  let heroDef ← draft.db.find? hero
  let allowed id := decide (CardAllowedForHero draft.db heroDef id)
  let count := picks.countP fun id => allowed id && (draft.db.find? id).any CardDef.isDeckCard
  let weapons := draft.product.basics.filter fun id => allowed id && (draft.db.find? id).any CardDef.isWeapon
  let basics := weapons ++ List.replicate (30 - count) ⟨"WTR_224_Y"⟩
  let choice : BoosterDraft.DeckChoice := ⟨hero, basics⟩
  let _ ← (draft.deck seat choice).toOption
  return choice

/-- Young heroes available to this seat for a duel from its completed WTR draft. -/
@[export fab_duel_heroes]
def browserDraftHeroes (draft : BoosterDraft.State) (seat : UInt32) : String :=
  let options := draft.product.basics.filter fun id =>
    (draft.db.find? id).any CardDef.isYoungHero && (draftChoice draft ⟨seat.toNat⟩ id).isSome
  String.intercalate " " (options.map (·.val))

private def chanceInput (duel : BrowserDuel) : Option (ActionKind × Rng) :=
  match duel.game.pending with
  | .chanceFirstPlayer :: _ =>
    let (i, rng) := duel.rng.nextNat duel.game.playerCount
    some (.chanceFirstChooser ⟨i⟩, rng)
  | .chanceShuffle zone :: _ =>
    let (order, rng) := duel.rng.shuffle (duel.game.zone zone)
    some (.shuffleOrder order, rng)
  | .chanceDie6 .. :: _ =>
    let (roll, rng) := duel.rng.nextNat 6
    some (.die6Roll (roll + 1), rng)
  | _ => none

private def chance : Nat → BrowserDuel → Option BrowserDuel
  | 0, _ => none
  | n + 1, duel =>
    match chanceInput duel with
    | none => some duel
    | some (kind, rng) => do
      let result ← (step 2048 duel.game ⟨.chance, kind⟩).toOption
      chance n ⟨result.1, rng⟩

/-- Start a two-player Lean game from the adjacent pair's own drafted cards and basic supplies. -/
@[export fab_duel_start]
def startBrowserDuel (draft : BoosterDraft.State) (pair : UInt32) (first second : String)
    (seed : UInt32) : Option BrowserDuel := do
  if pair ≥ 4 then none else do
    let a : PlayerId := ⟨pair.toNat * 2⟩
    let b : PlayerId := ⟨a.n + 1⟩
    let first ← draftChoice draft a ⟨first⟩
    let second ← draftChoice draft b ⟨second⟩
    let game ← GameState.initialDraft draft (a, first) (b, second)
    chance 16 ⟨game, ⟨seed.toUInt64⟩⟩

private def actionPreview : ActionKind → String × Option ObjId × String
  | .pickFirstPlayer p => ("first", none, toString p.n)
  | .loadoutEquip id => ("equip", some id, "")
  | .loadoutToDeck id => ("deck", some id, "")
  | .loadoutDone => ("ready", none, "")
  | .pass => ("pass", none, "")
  | .playCard id instant => (if instant then "instant" else "play", some id, "")
  | .attackWeapon id => ("attack", some id, "")
  | .activateAbility obj idx target second =>
    ("ability", some obj, String.intercalate " " ([toString (idx + 1)] ++
      ([target, second].filterMap id |>.map fun o => toString o.n)))
  | .defendCard id => ("defend", some id, "")
  | .defendDone => ("defendDone", none, "")
  | .pitchCard id => ("pitch", some id, "")
  | .cancelPlay => ("cancel", none, "")
  | .pickMode idx => ("mode", none, toString (idx + 1))
  | .pickHeroTarget p => ("heroTarget", none, toString p.n)
  | .pickWeaponTarget id => ("weaponTarget", some id, "")
  | .pickMay yes => (if yes then "yes" else "no", none, "")
  | .pickVariableResources x => ("resources", none, (x.map toString).getD "-")
  | .handToDeckPick id => ("handToDeck", some id, "")
  | .pickDiscardCard id => ("discard", some id, "")
  | .pickShuffleCard id => (if id.isSome then "select" else "confirm", id, "")
  | .pickHandCostCard id => ("handCost", some id, "")
  | .pickGraveyardCost id => (if id.isSome then "graveCost" else "no", id, "")
  | .optPick top id => (if top then "top" else "bottom", id, "")
  | .arsenalPut id => ("arsenal", some id, "")
  | .arsenalSkip => ("skipArsenal", none, "")
  | .pitchReturnPick id => ("pitchReturn", some id, "")
  | .concede => ("concede", none, "")
  | .pickTriggerStart p => ("triggerStart", none, toString p.n)
  | .pickTrigger trigger hero equipment =>
    ("trigger", equipment, toString trigger ++ " " ++ ((hero.map (toString ∘ (·.n))).getD "-"))
  | .pickTriggerGraveyardCard id => ("graveTarget", some id, "")
  | .pickReplacement choice => ("replacement", none, (choice.map toString).getD "-")
  | _ => ("choose", none, "")
private def visibleObjects (s : GameState) (zone : Zone) : VisibleZone → List (Option (ObjId × Object))
  | .countOnly _ => []
  | .entries entries => entries.zip (s.zone zone) |>.map fun (visible, obj) =>
    match visible with
    | some (.faceUp o) => some (obj, o)
    | _ => none

private def shownCard (known : List (ObjId × CardId)) (obj : Object) : Option CardId :=
  match obj.kind with
  | .layer source .. | .attackProxy source _ => known.lookup source
  | kind => kind.cardId?

private def zoneRow (s : GameState) (known : List (ObjId × CardId))
    (zone : Zone) (name : String) (visible : VisibleZone) : String :=
  let data := match visible with
    | .countOnly count => [toString count, ""]
    | .entries entries =>
      let labels := (visibleObjects s zone visible).map fun entry =>
        (entry.map fun (id, obj) => toString id.n ++ ":" ++
          ((shownCard known obj).map (·.val)).getD "?").getD "-"
      [toString entries.length, String.intercalate " " labels]
  String.intercalate "\t" (["z", name] ++ data)

private def resultName (p : PlayerId) : Option GameResult → String
  | some (.won players) => if players.contains p then "win" else "loss"
  | some (.draw _) => "draw"
  | none => "-"

private def fillerIndex (actions : List Action) : Nat := actions.length

private def fillDeck (p : PlayerId) : Nat → GameState → Option GameState
  | 0, _ => none
  | n + 1, s =>
    if loadoutCanFinish s p then some s
    else do
      let action ← (legalFrameActions s).find? fun action =>
        action.actor == .player p && match action.kind with | .loadoutToDeck _ => true | _ => false
      let next ← (step 2048 s action).toOption
      fillDeck p n next.1

private def canFill (s : GameState) (p : PlayerId) : Bool :=
  s.pending.head? == some (.chooseLoadout p) && !loadoutCanFinish s p

/-- Submit an index in the requesting player's current list of legal actions. -/
@[export fab_duel_move]
def browserDuelMove (duel : BrowserDuel) (seat index : UInt32) : Option BrowserDuel := do
  if seat ≥ 2 then none else do
    let p : PlayerId := ⟨seat.toNat⟩
    let s := duel.game
    let actions := legalActionsFor p s
    if index.toNat == fillerIndex actions && canFill s p then
      let next ← fillDeck p 31 s
      return { duel with game := next }
    else
      let action ← actions[index.toNat]?
      let next ← (step 2048 s action).toOption
      chance 16 { duel with game := next.1 }

/-- Encode the requesting player's board projection and legal controls for a browser duel. -/
@[export fab_duel_view]
def browserDuelView (duel : BrowserDuel) (seat : UInt32) : String :=
  if seat ≥ 2 then "" else
    let s := duel.game
    let p : PlayerId := ⟨seat.toNat⟩
    let q : PlayerId := ⟨1 - p.n⟩
    let assets := s.poolOf p
    let actions := legalActionsFor p s
    let playerField (id : Option PlayerId) := (id.map (toString ∘ (·.n))).getD "-"
    let acting := match (legalFrameActions s).head?.map (·.actor) with
      | some (.player who) => some who
      | _ => none
    let phase := match s.phase with
      | .setup => "setup" | .startPhase => "startPhase"
      | .actionPhase => "actionPhase" | .endPhase => "endPhase"
    let header := String.intercalate "\t" ["v", phase, toString s.turn,
      playerField s.active, playerField acting, toString (s.lifeOf p), toString (s.lifeOf q),
      toString assets.resources, toString assets.actionPoints, toString assets.chi, resultName p s.result]
    let combat := (s.combat.bind CombatChain.activeLink?).map fun link =>
      String.intercalate "\t" ["c", toString (linkAttackPower s link), toString (linkTotalDefense s link)]
    let namedZones : List (String × ZoneKind) := [
      ("hero", .hero), ("head", .head), ("chest", .chest), ("arms", .arms), ("legs", .legs),
      ("weapon", .weapon), ("permanent", .permanent), ("deck", .deck), ("hand", .hand),
      ("arsenal", .arsenal), ("pitch", .pitch), ("graveyard", .graveyard),
      ("banished", .banished), ("inventory", .inventory), ("soul", .soul)]
    let named := ([(p, "self"), (q, "opponent")].flatMap fun (who, side) =>
      namedZones.map fun (name, kind) => (side ++ "." ++ name, Zone.player who kind)) ++
      [("chain", .combatChain), ("stack", .stack)]
    let zones := named.map fun (name, zone) => (name, zone, viewZone p s zone)
    let known := (view p s).selectionChoices ++ (zones.flatMap fun (_, zone, visible) =>
      (visibleObjects s zone visible).filterMap fun entry => do
        let (id, obj) ← entry
        let card ← obj.kind.cardId?
        return (id, card))
    let moves := actions.zipIdx.map fun (action, index) =>
      let (kind, obj, info) := actionPreview action.kind
      let id := (obj.map (toString ∘ (·.n))).getD "-"
      let card := ((obj.bind fun id => known.lookup id).map (·.val)).getD "-"
      String.intercalate "\t" ["a", toString index, kind, id, card, info]
    let fill := if canFill s p then ["a\t" ++ toString (fillerIndex actions) ++ "\tfill\t-\t-\t"] else []
    String.intercalate "\n" ([header] ++ combat.toList ++
      (zones.map fun (name, zone, visible) => zoneRow s known zone name visible) ++ moves ++ fill)

end FabDriver

end
