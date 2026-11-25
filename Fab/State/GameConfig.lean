module

public import Fab.Core.Mode
public import Fab.Tournament.DeckLegality

/-!
# Game configuration

Immutable ruleset, format, mode, and ban list stored in `GameState.config` for the duration of a
game (design.md §6.1).
-/

@[expose] public section

namespace Fab

/-- Tournament round stage governing time-limit and intentional-draw rules (TRP 4). -/
inductive TournamentStage where
  /-- Swiss round (Bo1, intentional draw permitted, time limit adds +1 turn then draw). -/
  | swiss
  /-- Top Cut / single-elimination round (intentional draw prohibited). -/
  | topCut
deriving DecidableEq, Repr, Hashable

/-- Which rules framework applies to the game (design.md §6.1). -/
inductive RuleSet where
  /-- Comprehensive Rules only. -/
  | coreOnly
  /-- Tournament Rules and Policy applied alongside the Comprehensive Rules. -/
  | tournament (stage : TournamentStage)
deriving DecidableEq, Repr, Hashable

/-- Whether `rs` enables Tournament Rules and Policy (TRP 4). -/
def RuleSet.isTournament : RuleSet → Bool
  | .coreOnly => false
  | .tournament _ => true

/-- Whether `rs` uses round time-limit End-of-Round Procedure: Swiss rounds are timed, whereas
Top Cut / elimination rounds are untimed (TRP 4). -/
def RuleSet.hasTimeLimit : RuleSet → Bool
  | .tournament .swiss => true
  | .tournament .topCut => false
  | .coreOnly => false

/-- Whether `rs` permits Intentional Draws: allowed in Swiss rounds, prohibited in Top Cut
(TRP 4). -/
def RuleSet.allowsIntentionalDraw : RuleSet → Bool
  | .tournament .swiss => true
  | .tournament .topCut => false
  | .coreOnly => false

/-- Fixed configuration of a game, chosen at initial state and unchanged by `step`. -/
structure GameConfig where
  /-- Core-only or tournament ruleset. -/
  ruleSet : RuleSet := .coreOnly
  /-- Deckbuilding and game format (initial target: `classicConstructed`). -/
  format : Format := .classicConstructed
  /-- Player count / seating mode (initial target: `duel`). -/
  mode : Mode := .duel
  /-- Format-specific banned, Living Legend, and restricted card lists. -/
  banList : FormatBanList := .empty
deriving DecidableEq, Repr

/-- Standard 1v1 Classic Constructed configuration. -/
def GameConfig.ccDuel (ruleSet : RuleSet := .coreOnly) (banList : FormatBanList := .empty) :
    GameConfig :=
  { ruleSet := ruleSet, format := .classicConstructed, mode := .duel, banList := banList }

/-- Whether a `GameConfig` combines a valid player count and compatible mode/format. -/
def GameConfig.Valid (cfg : GameConfig) : Prop :=
  2 ≤ cfg.mode.playerCount ∧
  match cfg.format, cfg.mode with
  | .upf, .upf _ => True
  | .upf, .duel => False
  | _, .duel => True
  | _, .upf _ => False

instance GameConfig.decidableValid (cfg : GameConfig) : Decidable cfg.Valid := by
  unfold GameConfig.Valid
  cases cfg.format <;> cases cfg.mode <;> infer_instance

/-- Standard 1v1 Classic Constructed configuration is valid. -/
theorem GameConfig.valid_ccDuel (rs : RuleSet) (bl : FormatBanList) :
    (GameConfig.ccDuel rs bl).Valid :=
  ⟨Nat.le_refl 2, trivial⟩

end Fab

end
