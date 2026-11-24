module

import Fab.Core.Supertype
import Fab.Core.Property
import Fab.Core.Cost
import Fab.Core.Mode
meta import Fab.Core.Supertype
meta import Fab.Core.Property
meta import Fab.Core.Cost
meta import Fab.Core.Mode

/-!
# Tests: Core types and L0 arithmetic
-/

open Fab

-- Supertype matching
#guard decide (Supertype.matchesHero [.class_ .guardian] [.generic])
#guard decide (Supertype.matchesHero [.class_ .guardian] [.class_ .guardian])
#guard !decide (Supertype.matchesHero [.class_ .guardian] [.class_ .warrior])
#guard decide (Supertype.matchesHero [.class_ .runeblade, .talent .shadow] [.talent .shadow])
#guard !decide (Supertype.matchesHero [.class_ .guardian] [.talent .ice, .class_ .guardian])

-- Numeric clamping
#guard clampNonNeg (-3) == 0
#guard clampNonNeg 0 == 0
#guard clampNonNeg 5 == 5

-- Asset costs and Chi payment rules (CR 1.14.2b)
#guard decide (({ actionPoints := 1, resources := 2, chi := 0 } : AssetPool).canPay
  { actionPoints := 1, resources := 2 })
-- Chi can pay for generic resource costs
#guard decide (({ actionPoints := 1, resources := 0, chi := 3 } : AssetPool).canPay
  { actionPoints := 1, resources := 3, chi := 0 })
-- Generic resources CANNOT pay strict Chi costs
#guard !decide (({ actionPoints := 1, resources := 5, chi := 0 } : AssetPool).canPay
  { actionPoints := 1, resources := 0, chi := 1 })
-- Mixed Chi + Resource cost paid by Chi covering both
#guard (({ actionPoints := 1, resources := 1, chi := 3 } : AssetPool).spend
  { actionPoints := 1, resources := 2, chi := 1 } 1) ==
  some { actionPoints := 0, resources := 0, chi := 1 }
-- No over-pitching: deficit is 0 once pool can pay
#guard !decide (({ actionPoints := 1, resources := 3, chi := 0 } : AssetPool).needsResources
  { actionPoints := 1, resources := 2 })
#guard decide (({ actionPoints := 1, resources := 1, chi := 0 } : AssetPool).needsResources
  { actionPoints := 1, resources := 2 })

-- Format specifications
#guard Format.classicConstructed.spec.requiresAdultHero == true
#guard Format.classicConstructed.spec.maxCardPool == some 80
#guard decide (Format.classicConstructed.spec.deckSize.Satisfied 60)
#guard !decide (Format.classicConstructed.spec.deckSize.Satisfied 59)
