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
  -- The first LGS promo print run shares logical cards with the WTR booster.
  | "LGS001" | "LGS001-P" => some ⟨"WTR_003"⟩
  | "LGS002" | "LGS002-P" => some ⟨"WTR_040"⟩
  | "LGS003" | "LGS003-P" => some ⟨"WTR_078"⟩
  | "LGS004" | "LGS004-P" => some ⟨"WTR_115"⟩
  | "LGS005" | "LGS005-P" => some ⟨"WTR_031_B"⟩
  | "LGS006" | "LGS006-P" => some ⟨"WTR_054_R"⟩
  | "LGS007" | "LGS007-P" => some ⟨"WTR_110_R"⟩
  | "LGS008" | "LGS008-P" => some ⟨"WTR_132_R"⟩
  -- Welcome to Rathe Hero Deck — Bravo.
  | "BVO001" => some ⟨"WTR_038"⟩
  | "BVO002" => some ⟨"WTR_039"⟩
  | "BVO003" => some ⟨"WTR_040"⟩
  | "BVO004" => some ⟨"WTR_042"⟩
  | "BVO005" => some ⟨"WTR_156"⟩
  | "BVO006" => some ⟨"WTR_153"⟩
  | "BVO007" => some ⟨"WTR_158"⟩
  | "BVO008" => some ⟨"WTR_057_R"⟩
  | "BVO009" => some ⟨"WTR_060_R"⟩
  | "BVO010" => some ⟨"WTR_066_R"⟩
  | "BVO011" => some ⟨"WTR_048_R"⟩
  | "BVO012" => some ⟨"WTR_069_R"⟩
  | "BVO013" => some ⟨"WTR_067_Y"⟩
  | "BVO014" => some ⟨"WTR_070_Y"⟩
  | "BVO015" => some ⟨"IRA_012_Y"⟩
  | "BVO016" => some ⟨"WTR_059_B"⟩
  | "BVO017" => some ⟨"WTR_062_B"⟩
  | "BVO018" => some ⟨"WTR_065_B"⟩
  | "BVO019" => some ⟨"WTR_050_B"⟩
  | "BVO020" => some ⟨"WTR_053_B"⟩
  | "BVO021" => some ⟨"WTR_056_B"⟩
  | "BVO022" => some ⟨"WTR_074_B"⟩
  | "BVO023" => some ⟨"WTR_178_B"⟩
  | "BVO024" => some ⟨"WTR_190_B"⟩
  | "BVO025" => some ⟨"WTR_166_B"⟩
  | "BVO026" => some ⟨"WTR_202_B"⟩
  | "BVO027" => some ⟨"WTR_208_B"⟩
  | "BVO028" => some ⟨"WTR_171_B"⟩
  | "BVO029" => some ⟨"WTR_223_B"⟩
  -- Welcome to Rathe Hero Deck — Dorinthea.
  | "TEA001" => some ⟨"WTR_113"⟩
  | "TEA002" => some ⟨"WTR_114"⟩
  | "TEA003" => some ⟨"WTR_115"⟩
  | "TEA004" => some ⟨"WTR_151"⟩
  | "TEA005" => some ⟨"WTR_156"⟩
  | "TEA006" => some ⟨"WTR_157"⟩
  | "TEA007" => some ⟨"WTR_117"⟩
  | "TEA008" => some ⟨"WTR_135_R"⟩
  | "TEA009" => some ⟨"WTR_138_R"⟩
  | "TEA010" => some ⟨"WTR_123_R"⟩
  | "TEA011" => some ⟨"WTR_126_R"⟩
  | "TEA012" => some ⟨"WTR_144_R"⟩
  | "TEA013" => some ⟨"WTR_147_R"⟩
  | "TEA014" => some ⟨"WTR_141_R"⟩
  | "TEA015" => some ⟨"WTR_203_R"⟩
  | "TEA016" => some ⟨"WTR_209_R"⟩
  | "TEA017" => some ⟨"WTR_139_Y"⟩
  | "TEA018" => some ⟨"WTR_130_Y"⟩
  | "TEA019" => some ⟨"IRA_012_Y"⟩
  | "TEA020" => some ⟨"WTR_137_B"⟩
  | "TEA021" => some ⟨"WTR_134_B"⟩
  | "TEA022" => some ⟨"WTR_146_B"⟩
  | "TEA023" => some ⟨"WTR_149_B"⟩
  | "TEA024" => some ⟨"WTR_143_B"⟩
  | "TEA025" => some ⟨"WTR_131_B"⟩
  | "TEA026" => some ⟨"WTR_184_B"⟩
  | "TEA027" => some ⟨"WTR_196_B"⟩
  | "TEA028" => some ⟨"WTR_170_B"⟩
  | "TEA029" => some ⟨"WTR_175_B"⟩
  | "TEA030" => some ⟨"WTR_225"⟩
  -- Welcome to Rathe Hero Deck — Katsu.
  | "KSU001" => some ⟨"WTR_076"⟩
  | "KSU002" => some ⟨"WTR_077"⟩
  | "KSU003" => some ⟨"WTR_078"⟩
  | "KSU004" => some ⟨"WTR_078"⟩
  | "KSU005" => some ⟨"WTR_155"⟩
  | "KSU006" => some ⟨"WTR_152"⟩
  | "KSU007" => some ⟨"WTR_080"⟩
  | "KSU008" => some ⟨"WTR_158"⟩
  | "KSU009" => some ⟨"WTR_089_R"⟩
  | "KSU010" => some ⟨"WTR_086_R"⟩
  | "KSU011" => some ⟨"WTR_098_R"⟩
  | "KSU012" => some ⟨"WTR_101_R"⟩
  | "KSU013" => some ⟨"WTR_095_R"⟩
  | "KSU014" => some ⟨"WTR_104_R"⟩
  | "KSU015" => some ⟨"WTR_107_R"⟩
  | "KSU016" => some ⟨"WTR_110_R"⟩
  | "KSU017" => some ⟨"WTR_191_R"⟩
  | "KSU018" => some ⟨"WTR_102_Y"⟩
  | "KSU019" => some ⟨"WTR_105_Y"⟩
  | "KSU020" => some ⟨"WTR_108_Y"⟩
  | "KSU021" => some ⟨"IRA_012_Y"⟩
  | "KSU022" => some ⟨"WTR_088_B"⟩
  | "KSU023" => some ⟨"WTR_100_B"⟩
  | "KSU024" => some ⟨"WTR_112_B"⟩
  | "KSU025" => some ⟨"WTR_094_B"⟩
  | "KSU026" => some ⟨"WTR_196_B"⟩
  | "KSU027" => some ⟨"WTR_205_B"⟩
  | "KSU028" => some ⟨"IRA_011_B"⟩
  | "KSU029" => some ⟨"WTR_170_B"⟩
  | "KSU030" => some ⟨"WTR_175_B"⟩
  -- Welcome to Rathe Hero Deck — Rhinar.
  | "RNR001" => some ⟨"WTR_001"⟩
  | "RNR002" => some ⟨"WTR_002"⟩
  | "RNR003" => some ⟨"WTR_003"⟩
  | "RNR004" => some ⟨"WTR_155"⟩
  | "RNR005" => some ⟨"WTR_005"⟩
  | "RNR006" => some ⟨"WTR_157"⟩
  | "RNR007" => some ⟨"WTR_154"⟩
  | "RNR008" => some ⟨"WTR_011_R"⟩
  | "RNR009" => some ⟨"WTR_023_R"⟩
  | "RNR010" => some ⟨"WTR_014_R"⟩
  | "RNR011" => some ⟨"WTR_020_R"⟩
  | "RNR012" => some ⟨"WTR_026_R"⟩
  | "RNR013" => some ⟨"WTR_029_R"⟩
  | "RNR014" => some ⟨"WTR_032_R"⟩
  | "RNR015" => some ⟨"WTR_164_R"⟩
  | "RNR016" => some ⟨"WTR_021_Y"⟩
  | "RNR017" => some ⟨"WTR_027_Y"⟩
  | "RNR018" => some ⟨"WTR_018_Y"⟩
  | "RNR019" => some ⟨"WTR_177_Y"⟩
  | "RNR020" => some ⟨"WTR_189_Y"⟩
  | "RNR021" => some ⟨"WTR_201_Y"⟩
  | "RNR022" => some ⟨"IRA_012_Y"⟩
  | "RNR023" => some ⟨"WTR_031_B"⟩
  | "RNR024" => some ⟨"WTR_034_B"⟩
  | "RNR025" => some ⟨"WTR_019_B"⟩
  | "RNR026" => some ⟨"WTR_037_B"⟩
  | "RNR027" => some ⟨"WTR_184_B"⟩
  | "RNR028" => some ⟨"WTR_196_B"⟩
  | "RNR029" => some ⟨"WTR_172_B"⟩
  | "RNR030" => some ⟨"WTR_175_B"⟩
  | "RNR031" => some ⟨"WTR_225"⟩
  | _ => none

end FabCards

end
