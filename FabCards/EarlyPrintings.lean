module

public import Fab.Core.Ids

/-!
# Early printings

Collector numbers from early products that share a logical card with another printing.
-/

@[expose] public section

namespace FabCards

open Fab

/-- Resolve an early collector number to an existing, stable logical card identifier. -/
def earlyPrintingCardId? : String → Option CardId
  -- The four Slingshot Underground artist proofs use the equivalent WTR cards
  -- under the authorized-test-print list (TRP A.6).
  | "OXO001" | "OXO001-P" => some ⟨"WTR_155"⟩
  | "OXO002" | "OXO002-P" => some ⟨"WTR_156"⟩
  | "OXO003" | "OXO003-P" => some ⟨"WTR_157"⟩
  | "OXO004" | "OXO004-P" => some ⟨"WTR_158"⟩
  | "IRA001" | "IRA001-P" => some ⟨"IRA_001"⟩
  | "IRA002" | "IRA002-P" => some ⟨"IRA_002"⟩
  | "IRA003" | "IRA003-P" => some ⟨"IRA_003_Y"⟩
  | "IRA004" | "IRA004-P" => some ⟨"IRA_004_Y"⟩
  | "IRA005" | "IRA005-P" => some ⟨"IRA_005_Y"⟩
  | "IRA006" | "IRA006-P" => some ⟨"IRA_006_R"⟩
  | "IRA007" | "IRA007-P" => some ⟨"IRA_007_R"⟩
  | "IRA008" | "IRA008-P" => some ⟨"WTR_100_B"⟩
  | "IRA009" | "IRA009-P" => some ⟨"WTR_191_R"⟩
  | "IRA010" | "IRA010-P" => some ⟨"IRA_010_B"⟩
  | "IRA011" | "IRA011-P" => some ⟨"IRA_011_B"⟩
  | "IRA012" | "IRA012-P" => some ⟨"IRA_012_Y"⟩
  | _ => none

end FabCards

end
