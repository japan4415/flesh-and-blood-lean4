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
  | _ => none

end FabCards

end
