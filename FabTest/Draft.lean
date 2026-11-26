module

import Fab.Rules.Setup
import FabCards.Booster
import FabCards.Draft
import FabCards.ThroughArc
import FabDriver.BrowserDuel
meta import Fab.Rules.Setup
meta import FabCards.Booster
meta import FabCards.Draft
meta import FabCards.ThroughArc
meta import FabDriver.BrowserDuel

/-!
# Booster Draft regression tests

Exercise the public draft, registration and game setup APIs using the early set products.
-/

namespace FabTest

open Fab FabCards Fab.BoosterDraft

private def hood : CardId := ⟨"ARC_155"⟩
private def gloves : CardId := ⟨"ARC_157"⟩
private def skullcap : CardId := ⟨"ARC_150"⟩
private def plunder : CardId := ⟨"ARC_170_R"⟩
private def dash : CardId := ⟨"ARC_002"⟩
private def azalea : CardId := ⟨"ARC_039"⟩
private def pistol : CardId := ⟨"ARC_003"⟩
private def bauble : CardId := ⟨"WTR_224_Y"⟩

private def failsWith {α : Type} (result : Except Error α) (expected : Error) : Bool :=
  match result with
  | .ok _ => false
  | .error actual => actual == expected

private def sameBoosters (cards : List CardId) (extra : Option CardId := none) : Boosters :=
  let booster := cards.map some ++ [extra]
  ⟨booster, booster, booster⟩

private def packAt (s : State) (seat : Nat) : Option (List CardId) :=
  (s.view ⟨seat⟩).bind (·.pack)

private def poolAt (s : State) (seat : Nat) : Option (List CardId) :=
  (s.view ⟨seat⟩).bind (·.drafted)

private def pickBySeat (s : State) (picks : List CardId) : Except Error State :=
  picks.zipIdx.foldlM (fun state (card, seat) => state.pick ⟨seat⟩ card) s

private def rotatesAndHides : Except Error Bool := do
  let product := { arcDraft with totalSlots := 3, draftableSlots := 2 }
  let seats := [hood, gloves, skullcap].map fun card => sameBoosters [card, card] (some dash)
  let s ← State.start throughArcDB product .optional seats
  let first ← s.pick ⟨0⟩ hood
  let rejected := failsWith (first.pick ⟨0⟩ hood) .alreadyPicked &&
    failsWith (first.pick ⟨1⟩ hood) .cardUnavailable &&
    failsWith (first.pick ⟨3⟩ hood) .invalidSeat &&
    failsWith first.openNext .wrongPhase
  let hidden := packAt first 0 == none && packAt first 1 == some [gloves, gloves] &&
    poolAt first 0 == none && poolAt first 1 == none && (first.view ⟨3⟩).isNone
  let pass ← (← first.pick ⟨1⟩ gloves).pick ⟨2⟩ skullcap
  let afterLeft := packAt pass 0 == some [skullcap] && packAt pass 1 == some [hood] &&
    packAt pass 2 == some [gloves]
  let review ← pickBySeat pass [skullcap, hood, gloves]
  let canReview := review.phase == .review 1 && packAt review 0 == none &&
    poolAt review 0 == some [hood, skullcap] && poolAt review 1 == some [gloves, hood] &&
    failsWith (review.pick ⟨0⟩ hood) .wrongPhase
  let second ← review.openNext
  let pass ← pickBySeat second [hood, gloves, skullcap]
  let afterRight := packAt pass 0 == some [gloves] && packAt pass 1 == some [skullcap] &&
    packAt pass 2 == some [hood] && poolAt pass 0 == none
  let review ← pickBySeat pass [gloves, skullcap, hood]
  let third ← review.openNext
  let pass ← pickBySeat third [hood, gloves, skullcap]
  let done ← pickBySeat pass [skullcap, hood, gloves]
  return rejected && hidden && afterLeft && canReview && afterRight && done.phase == .complete &&
    poolAt done 0 == some [hood, skullcap, hood, gloves, hood, skullcap] &&
    done.cardsInPod.isPerm s.cardsInPod && !done.cardsInPod.contains dash

#guard rotatesAndHides.toOption == some true

#guard failsWith
  (State.start throughArcDB arcDraft .optional (List.replicate 8 (sameBoosters [plunder])))
  (.invalidBooster 0 0)
#guard failsWith
  (State.start throughArcDB arcDraft .optional
    (List.replicate 8 (sameBoosters (dash :: List.replicate 14 plunder))))
  (.invalidBooster 0 0)
#guard failsWith
  (State.start throughArcDB arcDraft .optional
    (List.replicate 8 (sameBoosters (⟨"WTR_159_R"⟩ :: List.replicate 14 plunder))))
  (.invalidBooster 0 0)
#guard failsWith
  (State.start throughArcDB arcDraft .optional [sameBoosters (List.replicate 15 plunder)])
  .tooFewSeats

private def pickAvailable (s : State) (seatCount : Nat) : Except Error State :=
  (List.range seatCount).foldlM (fun state n => do
    let some card := (packAt state n).bind List.head? | throw .invalidRound
    state.pick ⟨n⟩ card) s

private def draftAll (db : CardDB) (product : Product) (registration : RegistrationPolicy)
    (boosters : Boosters) : Except Error State := do
  let start ← State.start db product registration (List.replicate 8 boosters)
  (List.range 3).foldlM (fun state round => do
    let active ← if round = 0 then pure state else state.openNext
    (List.range product.draftableSlots).foldlM (fun state _ => pickAvailable state 8) active) start

private def competitiveArc : Except Error Bool := do
  let nonMatching : CardId := ⟨"ARC_004"⟩
  let boosters := sameBoosters (nonMatching :: skullcap :: List.replicate 13 plunder) (some azalea)
  let done ← draftAll throughArcDB arcDraft .required boosters
  let some picks := poolAt done 0 | throw .invalidRound
  let dashChoice : DeckChoice := ⟨dash, [pistol, bauble]⟩
  let azaleaChoice : DeckChoice := ⟨azalea, [bauble]⟩
  let required := failsWith (done.deck ⟨0⟩ dashChoice) .registrationRequired
  let rejectsWrongPool := failsWith (done.register ⟨0⟩ dash (picks.drop 1)) .incorrectPool
  let rejectsAdult :=
    failsWith (done.register ⟨0⟩ ⟨"ARC_001"⟩ picks) .heroUnavailable
  let registered ← done.register ⟨0⟩ dash picks.reverse
  let some secondPicks := poolAt registered 1 | throw .invalidRound
  let registered ← registered.register ⟨1⟩ azalea secondPicks
  let deck ← registered.deck ⟨0⟩ dashChoice
  let other ← registered.deck ⟨1⟩ azaleaChoice
  let ready := (GameState.initialDraft registered (⟨0⟩, dashChoice) (⟨1⟩, azaleaChoice)).isSome
  return done.phase == .complete && picks.length == 45 && required && rejectsWrongPool &&
    rejectsAdult && failsWith (registered.register ⟨0⟩ dash picks) .alreadyRegistered &&
    failsWith (registered.deck ⟨0⟩ azaleaChoice) .wrongRegisteredHero &&
    failsWith (registered.deck ⟨0⟩ ⟨dash, [hood]⟩) .basicUnavailable &&
    deck.pool.contains nonMatching && !other.pool.contains nonMatching &&
    deck.pool.count plunder == 39 && deck.pool.count bauble == 1 &&
    deck.pool.count pistol == 1 && ready &&
    (GameState.initialDraft registered (⟨0⟩, dashChoice) (⟨0⟩, dashChoice)).isNone

#guard competitiveArc.toOption == some true

private def casualWtr : Except Error Bool := do
  let heart : CardId := ⟨"WTR_000_B"⟩
  let rhinar : CardId := ⟨"WTR_002"⟩
  let bravo : CardId := ⟨"WTR_039"⟩
  let brute : CardId := ⟨"WTR_005"⟩
  let boosters := sameBoosters (heart :: List.replicate 14 brute)
  let done ← draftAll throughArcDB wtrDraft .optional boosters
  let first ← done.deck ⟨0⟩ ⟨rhinar, List.replicate 27 bauble⟩
  let second ← done.deck ⟨0⟩ ⟨bravo, List.replicate 27 bauble⟩
  return failsWith (done.deck ⟨0⟩ ⟨bravo, List.replicate 26 bauble⟩) .insufficientDeckCards &&
    first.hero == rhinar && second.hero == bravo && first.pool.contains brute &&
    !second.pool.contains brute && first.pool.count heart == 3 && second.pool.count bauble == 27 &&
    decide (DraftDeckValid throughArcDB first) && !decide (CoreDeckValid throughArcDB first)

#guard casualWtr.toOption == some true

private def wtrChoices : List Nat := List.range 4 ++ List.range 7 ++ [0, 1, 0, 0, 1]

#guard wtrBoosterLayout.map List.length ==
  List.replicate 4 48 ++ List.replicate 7 72 ++ [48, 73, 12, 211, 15]
#guard (openWtrBooster (wtrChoices.take 15)).isNone
#guard (openWtrBooster (wtrChoices ++ [0])).isNone
#guard (openWtrBooster (48 :: wtrChoices.drop 1)).isNone

private def openAndDraftWtr : Except Error Bool := do
  let some booster := openWtrBooster wtrChoices | throw .invalidRound
  let heart : CardId := ⟨"WTR_000_B"⟩
  let token : CardId := ⟨"WTR_002"⟩
  let done ← draftAll throughArcDB wtrDraft .optional ⟨booster, booster, booster⟩
  let some picks := poolAt done 0 | throw .invalidRound
  return booster[14]? == some (some heart) && booster[15]? == some (some token) &&
    picks.length == 45 && picks.count heart == 3 && !picks.contains token

#guard openAndDraftWtr.toOption == some true

private def browserDuel : Option Bool := do
  let hero := "WTR_039"
  let brute : CardId := ⟨"WTR_005"⟩
  let done ← (draftAll throughArcDB wtrDraft .optional (sameBoosters (List.replicate 15 brute))).toOption
  let duel ← FabDriver.startBrowserDuel done 0 hero hero 17
  let move (duel : FabDriver.BrowserDuel) (p : PlayerId) (kind : ActionKind) := do
    let (_, index) ← (legalActionsFor p duel.game).zipIdx.find? fun (action, _) => action.kind == kind
    FabDriver.browserDuelMove duel (UInt32.ofNat p.n) (UInt32.ofNat index)
  let .player chooser ← (legalFrameActions duel.game).head?.map (·.actor) | none
  let duel ← move duel chooser (.pickFirstPlayer ⟨0⟩)
  let complete (duel : FabDriver.BrowserDuel) (p : PlayerId) := do
    let fill := (legalActionsFor p duel.game).length
    let duel ← FabDriver.browserDuelMove duel (UInt32.ofNat p.n) (UInt32.ofNat fill)
    move duel p .loadoutDone
  let duel ← complete duel ⟨0⟩
  let duel ← complete duel ⟨1⟩
  let firstView := (FabDriver.browserDuelView duel 0).splitOn "\n"
  let secondView := (FabDriver.browserDuelView duel 1).splitOn "\n"
  let hidden (rows : List String) :=
    rows.contains "z\topponent.hand\t4\t" && rows.contains "z\tself.deck\t26\t"
  let finished ← move duel ⟨1⟩ .concede
  return done.phase == .complete && duel.game.phase == .actionPhase &&
    hidden firstView && hidden secondView &&
    (FabDriver.browserDuelMove duel 0 0xffffffff).isNone &&
    finished.game.result == some (.won [⟨0⟩])

#guard browserDuel == some true

end FabTest
