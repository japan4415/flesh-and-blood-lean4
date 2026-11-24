module

public import Fab.Rules.Add
public import Fab.Rules.Deck
public import Fab.Tournament.DeckLegality

/-!
# Start-of-Game initial state construction

Creates the initial `GameState` from a valid `GameConfig`, `CardDB`, and legal player `DeckList`s
(CR 4.1.1-4.1.2). Each player's hero starts face-up in their hero zone (with starting life set to
its printed life total) and their entire registered card-pool starts in their inventory zone,
ready for the Start-of-Game frames (`chanceFirstPlayer` → `chooseFirstPlayer` → `chooseLoadout` →
`revealLoadouts` → `chanceShuffle` → `openingDraws`).
-/

@[expose] public section

namespace Fab

/-- Add a list of card identifiers to player `p`'s inventory zone with sequential `PhysId`s. -/
def addPoolCards (s : GameState) (p : PlayerId) (physStart : Nat) :
    List CardId → Option (GameState × Nat)
  | [] => some (s, physStart)
  | cid :: rest =>
    match addObject s (.player p .inventory)
        { kind := .card ⟨physStart⟩ cid, owner := p, controller := p,
          faceDown := true, timestamp := ⟨0⟩ } .bottom with
    | none => none
    | some (s1, _) => addPoolCards s1 p (physStart + 1) rest

/-- `addPoolCards` preserves `WF` and `OwnerOk`. -/
theorem addPoolCards_inv {s s' : GameState} {p : PlayerId} {ph ph' : Nat} {cids : List CardId}
    (hwf : s.WF) (hok : s.OwnerOk) (h : addPoolCards s p ph cids = some (s', ph')) :
    s'.WF ∧ s'.OwnerOk := by
  induction cids generalizing s ph with
  | nil =>
    simp only [addPoolCards, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hwf, hok⟩
  | cons cid rest ih =>
    unfold addPoolCards at h
    cases ha : addObject s (.player p .inventory)
        { kind := .card ⟨ph⟩ cid, owner := p, controller := p,
          faceDown := true, timestamp := ⟨0⟩ } .bottom with
    | none => simp only [ha] at h; cases h
    | some res =>
      obtain ⟨s1, _⟩ := res
      simp only [ha] at h
      exact ih (addObject_wf hwf ha) (addObject_ownerOk hwf hok ha) h

/-- Starting life total printed on a hero card, defaulting to 40 (CR 2.5, 4.1.2). -/
def heroStartingLife (db : CardDB) (hero : CardId) : Int :=
  match db.find? hero with
  | some c => c.front.life.getD 40
  | none => 40

/-- Place each player's hero in their hero zone (setting starting hero life) and registered
card-pool in their inventory zone (CR 4.1.2). -/
def addDecks (s : GameState) (seat : Nat) (physStart : Nat) :
    List DeckList → Option (GameState × Nat)
  | [] => some (s, physStart)
  | d :: rest =>
    let p : PlayerId := ⟨seat⟩
    let life := heroStartingLife s.cards d.hero
    match addObject s (.player p .hero)
        { kind := .card ⟨physStart⟩ d.hero, owner := p, controller := p,
          life := some life, timestamp := ⟨0⟩ } .top with
    | none => none
    | some (s1, _) =>
      let s2 := s1.setLife p life
      match addPoolCards s2 p (physStart + 1) d.pool with
      | none => none
      | some (s3, ph') => addDecks s3 (seat + 1) ph' rest

/-- `addDecks` preserves `WF` and `OwnerOk`. -/
theorem addDecks_inv {s s' : GameState} {seat ph ph' : Nat} {decks : List DeckList}
    (hwf : s.WF) (hok : s.OwnerOk) (h : addDecks s seat ph decks = some (s', ph')) :
    s'.WF ∧ s'.OwnerOk := by
  induction decks generalizing s seat ph with
  | nil =>
    simp only [addDecks, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hwf, hok⟩
  | cons d rest ih =>
    unfold addDecks at h
    dsimp only at h
    cases ha : addObject s (.player ⟨seat⟩ .hero)
        { kind := .card ⟨ph⟩ d.hero, owner := ⟨seat⟩, controller := ⟨seat⟩,
          life := some (heroStartingLife s.cards d.hero), timestamp := ⟨0⟩ } .top with
    | none => simp only [ha] at h; cases h
    | some res =>
      obtain ⟨s1, _⟩ := res
      simp only [ha] at h
      have hwf1 : s1.WF := addObject_wf hwf ha
      have hok1 : s1.OwnerOk := addObject_ownerOk hwf hok ha
      have hwf2 : (s1.setLife ⟨seat⟩ (heroStartingLife s.cards d.hero)).WF :=
        GameState.WF.congr hwf1 rfl rfl rfl rfl
      have hok2 : (s1.setLife ⟨seat⟩ (heroStartingLife s.cards d.hero)).OwnerOk :=
        GameState.OwnerOk.congr hok1 rfl rfl
      cases hp : addPoolCards (s1.setLife ⟨seat⟩ (heroStartingLife s.cards d.hero))
          ⟨seat⟩ (ph + 1) d.pool with
      | none => simp only [hp] at h; cases h
      | some res2 =>
        obtain ⟨s3, ph2⟩ := res2
        simp only [hp] at h
        obtain ⟨hwf3, hok3⟩ := addPoolCards_inv hwf2 hok2 hp
        exact ih hwf3 hok3 h

/-- Check whether a deck list is legal for the configured format. -/
def deckLegalForConfig (cfg : GameConfig) (db : CardDB) (d : DeckList) : Bool :=
  match cfg.format with
  | .classicConstructed => decide (CCDeckValid db cfg.banList d)
  | _ => decide (CoreDeckValid db d)

/-- Build the initial `GameState` for a game if configuration, `CardDB`, and all decks are valid
(CR 4.1.1-4.1.2). -/
def GameState.initial (cfg : GameConfig) (db : CardDB) (decks : List DeckList) :
    Option GameState :=
  if cfg.Valid ∧ db.WF ∧ decks.length = cfg.mode.playerCount ∧
      decks.all (deckLegalForConfig cfg db) then
    let s0 : GameState := { config := cfg, cards := db }
    match addDecks s0 0 0 decks with
    | none => none
    | some (s1, _) =>
      some { s1 with pending := [.chanceFirstPlayer], phase := .setup, result := none }
  else
    none

/-- Every initial state created by `GameState.initial` satisfies `WF` and `OwnerOk`. -/
theorem GameState.initial_inv {cfg : GameConfig} {db : CardDB} {decks : List DeckList}
    {s : GameState} (h : GameState.initial cfg db decks = some s) :
    s.WF ∧ s.OwnerOk := by
  unfold GameState.initial at h
  split at h
  · dsimp only at h
    cases ha : addDecks ({ config := cfg, cards := db } : GameState) 0 0 decks with
    | none => simp only [ha] at h; cases h
    | some res =>
      obtain ⟨s1, ph⟩ := res
      simp only [ha, Option.some.injEq] at h
      subst h
      obtain ⟨hwf1, hok1⟩ := addDecks_inv (empty_wf cfg db) (empty_ownerOk cfg db) ha
      exact ⟨GameState.WF.congr hwf1 rfl rfl rfl rfl, GameState.OwnerOk.congr hok1 rfl rfl⟩
  · cases h

/-- `GameState.initial` satisfies `WF`. -/
theorem GameState.initial_wf {cfg : GameConfig} {db : CardDB} {decks : List DeckList}
    {s : GameState} (h : GameState.initial cfg db decks = some s) : s.WF :=
  (GameState.initial_inv h).1

/-- `GameState.initial` satisfies `OwnerOk`. -/
theorem GameState.initial_ownerOk {cfg : GameConfig} {db : CardDB} {decks : List DeckList}
    {s : GameState} (h : GameState.initial cfg db decks = some s) : s.OwnerOk :=
  (GameState.initial_inv h).2

/-- `GameState.initial` preserves `CardDB.WF`. -/
theorem GameState.initial_cards_wf {cfg : GameConfig} {db : CardDB} {decks : List DeckList}
    {s : GameState} (h : GameState.initial cfg db decks = some s) : s.cards.WF := by
  unfold GameState.initial at h
  split at h
  · rename_i hcond
    dsimp only at h
    cases ha : addDecks ({ config := cfg, cards := db } : GameState) 0 0 decks with
    | none => simp only [ha] at h; cases h
    | some res =>
      obtain ⟨s1, ph⟩ := res
      simp only [ha, Option.some.injEq] at h
      subst h
      have hcards : s1.cards = db := by
        have haux : ∀ (s0 s' : GameState) (seat ph0 ph' : Nat) (ds : List DeckList),
            addDecks s0 seat ph0 ds = some (s', ph') → s'.cards = s0.cards := by
          intro s0 s' seat ph0 ph' ds hd
          induction ds generalizing s0 seat ph0 with
          | nil =>
            simp only [addDecks, Option.some.injEq, Prod.mk.injEq] at hd
            exact hd.1 ▸ rfl
          | cons d rest ih =>
            unfold addDecks at hd
            dsimp only at hd
            cases h1 : addObject s0 (.player ⟨seat⟩ .hero)
                { kind := .card ⟨ph0⟩ d.hero, owner := ⟨seat⟩, controller := ⟨seat⟩,
                  life := some (heroStartingLife s0.cards d.hero), timestamp := ⟨0⟩ } .top with
            | none => simp only [h1] at hd; cases hd
            | some r1 =>
              obtain ⟨sa, _⟩ := r1
              simp only [h1] at hd
              have hsa : sa.cards = s0.cards := by
                unfold addObject at h1
                split at h1
                · simp only [Option.some.injEq, Prod.mk.injEq] at h1
                  rw [← h1.1]; rfl
                · cases h1
              cases h2 : addPoolCards (sa.setLife ⟨seat⟩ (heroStartingLife s0.cards d.hero))
                  ⟨seat⟩ (ph0 + 1) d.pool with
              | none => simp only [h2] at hd; cases hd
              | some r2 =>
                obtain ⟨sb, ph2⟩ := r2
                simp only [h2] at hd
                have hsb : sb.cards =
                    (sa.setLife ⟨seat⟩ (heroStartingLife s0.cards d.hero)).cards := by
                  have hpool : ∀ (sx sy : GameState) (px : PlayerId) (p0 p1 : Nat)
                      (cs : List CardId),
                      addPoolCards sx px p0 cs = some (sy, p1) → sy.cards = sx.cards := by
                    intro sx sy px p0 p1 cs hp
                    induction cs generalizing sx p0 with
                    | nil =>
                      simp only [addPoolCards, Option.some.injEq, Prod.mk.injEq] at hp
                      exact hp.1 ▸ rfl
                    | cons c cs' ihc =>
                      unfold addPoolCards at hp
                      cases h3 : addObject sx (.player px .inventory)
                          { kind := .card ⟨p0⟩ c, owner := px, controller := px,
                            faceDown := true, timestamp := ⟨0⟩ } .bottom with
                      | none => simp only [h3] at hp; cases hp
                      | some r3 =>
                        obtain ⟨sc, _⟩ := r3
                        simp only [h3] at hp
                        have hsc : sc.cards = sx.cards := by
                          unfold addObject at h3
                          split at h3
                          · simp only [Option.some.injEq, Prod.mk.injEq] at h3
                            rw [← h3.1]; rfl
                          · cases h3
                        exact (ihc sc (p0 + 1) hp).trans hsc
                  exact hpool _ _ _ _ _ _ h2
                exact (ih sb (seat + 1) ph2 hd).trans (hsb.trans hsa)
        exact haux _ _ _ _ _ _ ha
      change s1.cards.WF
      rw [hcards]
      exact hcond.2.1
  · cases h

end Fab

end
