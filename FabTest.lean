module

public import Fab
public import FabCards
public import FabDriver
public import FabTest.RulesVersion
public import FabTest.Fixtures
public import FabTest.Core
public import FabTest.Deck
public import FabTest.Actions
public import FabTest.Setup
public import FabTest.Turn
public import FabTest.IR
public import FabTest.Stack
public import FabTest.Combat
public import FabTest.Tournament
public import FabTest.Continuous

/-!
# FabTest

Test driver for `lake test`. Tests are checked at build time (`#guard`, `example ... := by decide`).
-/
