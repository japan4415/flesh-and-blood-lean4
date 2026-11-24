module

public import Fab.Basic.RulesVersion
public import Fab.Basic.ListLemmas
public import Fab.Core.Ids
public import Fab.Core.Supertype
public import Fab.Core.CardType
public import Fab.Core.Property
public import Fab.Core.Cost
public import Fab.Core.Keyword
public import Fab.Core.Mode
public import Fab.Card.IR.Filter
public import Fab.Card.IR.Effect
public import Fab.Card.CardDef
public import Fab.Card.IR.WF
public import Fab.Card.CardDB
public import Fab.Rules.Deck
public import Fab.Tournament.DeckLegality
public import Fab.State.Zone
public import Fab.State.Lki
public import Fab.State.Object
public import Fab.State.GameConfig
public import Fab.State.Event
public import Fab.State.Phase
public import Fab.State.Decision
public import Fab.State.GameState
public import Fab.Rules.Move
public import Fab.Rules.Add
public import Fab.Rules.Reorder
public import Fab.Rules.Objects
public import Fab.Rules.Interp
public import Fab.Rules.Setup
public import Fab.Rules.Frames
public import Fab.Rules.Actions.Draw
public import Fab.Rules.Actions.Pitch
public import Fab.Rules.Actions.Discard
public import Fab.Rules.Actions.Banish
public import Fab.Spec.Legal
public import Fab.Engine.Step
public import Fab.Invariant.Step
public import Fab.Invariant.Turn
public import Fab.Invariant.Stack

/-!
# Fab

The verified core: a formalization of the Flesh and Blood Comprehensive Rules and Tournament Rules
and Policy in Lean 4 (see `docs/design.md`).
-/
