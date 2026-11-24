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

/-!
# FabTest

Test driver for `lake test`. Tests are checked at build time (`#guard`, `example ... := by decide`).
-/
