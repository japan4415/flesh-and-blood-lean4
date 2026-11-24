module

import Fab.Basic.RulesVersion
meta import Fab.Basic.RulesVersion

/-!
# Tests: rules version
-/

open Fab

#guard comprehensiveRulesVersion == ⟨⟨2, 15, 0⟩, ⟨2026, 9, 28⟩⟩
#guard tournamentRulesVersion == ⟨2025, 5, 30⟩
#guard decide comprehensiveRulesVersion.date.WellFormed
#guard decide tournamentRulesVersion.WellFormed
#guard !decide (RulesDate.WellFormed ⟨2026, 13, 1⟩)
#guard !decide (RulesDate.WellFormed ⟨2026, 1, 0⟩)
