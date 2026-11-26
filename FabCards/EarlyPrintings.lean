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
  -- Mighty Ape special-use promo, distributed at Auckland Armageddon in October 2019.
  | "LSS002" | "LSS002-P" => some ⟨"LSS_002_Y"⟩
  -- 2019 The Calling prize and participation printings.
  | "FAB001" | "FAB001-P" => some ⟨"WTR_150"⟩
  | "HER005" | "HER005-P" => some ⟨"WTR_002"⟩
  | "HER006" | "HER006-P" => some ⟨"WTR_039"⟩
  | "HER007" | "HER007-P" => some ⟨"WTR_077"⟩
  | "HER008" | "HER008-P" => some ⟨"WTR_114"⟩
  -- Cold foil hero participation printings from the 2020 Auckland Calling.
  | "HER001" | "HER001-P" => some ⟨"WTR_001"⟩
  | "HER002" | "HER002-P" => some ⟨"WTR_038"⟩
  | "HER003" | "HER003-P" => some ⟨"WTR_076"⟩
  | "HER004" | "HER004-P" => some ⟨"WTR_113"⟩
  | "ARC000" => some ⟨"ARC_000_B"⟩
  | "ARC001" | "HER017" | "HER017-P" => some ⟨"ARC_001"⟩
  | "ARC002" | "HER013" | "HER013-P" => some ⟨"ARC_002"⟩
  | "ARC003" | "LGS009" | "LGS009-P" => some ⟨"ARC_003"⟩
  | "ARC004" => some ⟨"ARC_004"⟩
  | "ARC005" => some ⟨"ARC_005"⟩
  | "ARC006" => some ⟨"ARC_006_R"⟩
  | "ARC007" => some ⟨"ARC_007_B"⟩
  | "ARC008" => some ⟨"ARC_008_R"⟩
  | "ARC009" => some ⟨"ARC_009_Y"⟩
  | "ARC010" => some ⟨"ARC_010_R"⟩
  | "ARC011" => some ⟨"ARC_011_R"⟩
  | "ARC012" => some ⟨"ARC_012_Y"⟩
  | "ARC013" => some ⟨"ARC_013_B"⟩
  | "ARC014" => some ⟨"ARC_014_R"⟩
  | "ARC015" => some ⟨"ARC_015_Y"⟩
  | "ARC016" => some ⟨"ARC_016_B"⟩
  | "ARC017" => some ⟨"ARC_017_Y"⟩
  | "ARC018" => some ⟨"ARC_018_B"⟩
  | "ARC019" => some ⟨"ARC_019_R"⟩
  | "ARC020" | "LGS013" | "LGS013-P" => some ⟨"ARC_020_R"⟩
  | "ARC021" => some ⟨"ARC_021_Y"⟩
  | "ARC022" => some ⟨"ARC_022_B"⟩
  | "ARC023" => some ⟨"ARC_023_R"⟩
  | "ARC024" => some ⟨"ARC_024_Y"⟩
  | "ARC025" => some ⟨"ARC_025_B"⟩
  | "ARC026" => some ⟨"ARC_026_R"⟩
  | "ARC027" => some ⟨"ARC_027_Y"⟩
  | "ARC028" => some ⟨"ARC_028_B"⟩
  | "ARC029" => some ⟨"ARC_029_R"⟩
  | "ARC030" => some ⟨"ARC_030_Y"⟩
  | "ARC031" => some ⟨"ARC_031_B"⟩
  | "ARC032" => some ⟨"ARC_032_R"⟩
  | "ARC033" => some ⟨"ARC_033_Y"⟩
  | "ARC034" => some ⟨"ARC_034_B"⟩
  | "ARC035" => some ⟨"ARC_035_Y"⟩
  | "ARC036" => some ⟨"ARC_036_R"⟩
  | "ARC037" => some ⟨"ARC_037_B"⟩
  | "ARC038" | "HER018" | "HER018-P" => some ⟨"ARC_038"⟩
  | "ARC039" | "HER014" | "HER014-P" => some ⟨"ARC_039"⟩
  | "ARC040" => some ⟨"ARC_040"⟩
  | "ARC041" => some ⟨"ARC_041"⟩
  | "ARC042" => some ⟨"ARC_042"⟩
  | "ARC043" => some ⟨"ARC_043_R"⟩
  | "ARC044" => some ⟨"ARC_044_R"⟩
  | "ARC045" => some ⟨"ARC_045_R"⟩
  | "ARC046" => some ⟨"ARC_046_B"⟩
  | "ARC047" => some ⟨"ARC_047_Y"⟩
  | "ARC048" => some ⟨"ARC_048_R"⟩
  | "ARC049" => some ⟨"ARC_049_Y"⟩
  | "ARC050" => some ⟨"ARC_050_B"⟩
  | "ARC051" => some ⟨"ARC_051_R"⟩
  | "ARC052" => some ⟨"ARC_052_Y"⟩
  | "ARC053" => some ⟨"ARC_053_B"⟩
  | "ARC054" => some ⟨"ARC_054_R"⟩
  | "ARC055" => some ⟨"ARC_055_Y"⟩
  | "ARC056" => some ⟨"ARC_056_B"⟩
  | "ARC057" => some ⟨"ARC_057_R"⟩
  | "ARC058" => some ⟨"ARC_058_Y"⟩
  | "ARC059" => some ⟨"ARC_059_B"⟩
  | "ARC060" => some ⟨"ARC_060_R"⟩
  | "ARC061" => some ⟨"ARC_061_Y"⟩
  | "ARC062" => some ⟨"ARC_062_B"⟩
  | "ARC063" => some ⟨"ARC_063_R"⟩
  | "ARC064" => some ⟨"ARC_064_Y"⟩
  | "ARC065" => some ⟨"ARC_065_B"⟩
  | "ARC066" => some ⟨"ARC_066_R"⟩
  | "ARC067" => some ⟨"ARC_067_Y"⟩
  | "ARC068" => some ⟨"ARC_068_B"⟩
  | "ARC069" => some ⟨"ARC_069_R"⟩
  | "ARC070" => some ⟨"ARC_070_Y"⟩
  | "ARC071" => some ⟨"ARC_071_B"⟩
  | "ARC072" => some ⟨"ARC_072_R"⟩
  | "ARC073" => some ⟨"ARC_073_Y"⟩
  | "ARC074" => some ⟨"ARC_074_B"⟩
  | "ARC075" | "HER019" | "HER019-P" => some ⟨"ARC_075"⟩
  | "ARC076" | "HER015" | "HER015-P" => some ⟨"ARC_076"⟩
  | "ARC077" | "ARC077-T" => some ⟨"ARC_077"⟩
  | "ARC078" | "ARC078-L" => some ⟨"ARC_078"⟩
  | "ARC079" => some ⟨"ARC_079"⟩
  | "ARC080" => some ⟨"ARC_080_R"⟩
  | "ARC081" => some ⟨"ARC_081_R"⟩
  | "ARC082" => some ⟨"ARC_082_Y"⟩
  | "ARC083" => some ⟨"ARC_083_B"⟩
  | "ARC084" => some ⟨"ARC_084_B"⟩
  | "ARC085" => some ⟨"ARC_085_R"⟩
  | "ARC086" => some ⟨"ARC_086_Y"⟩
  | "ARC087" => some ⟨"ARC_087_B"⟩
  | "ARC088" => some ⟨"ARC_088_R"⟩
  | "ARC089" => some ⟨"ARC_089_Y"⟩
  | "ARC090" => some ⟨"ARC_090_B"⟩
  | "ARC091" => some ⟨"ARC_091_R"⟩
  | "ARC092" => some ⟨"ARC_092_Y"⟩
  | "ARC093" => some ⟨"ARC_093_B"⟩
  | "ARC094" => some ⟨"ARC_094_R"⟩
  | "ARC095" => some ⟨"ARC_095_Y"⟩
  | "ARC096" => some ⟨"ARC_096_B"⟩
  | "ARC097" => some ⟨"ARC_097_R"⟩
  | "ARC098" => some ⟨"ARC_098_Y"⟩
  | "ARC099" => some ⟨"ARC_099_B"⟩
  | "ARC100" => some ⟨"ARC_100_R"⟩
  | "ARC101" => some ⟨"ARC_101_Y"⟩
  | "ARC102" => some ⟨"ARC_102_B"⟩
  | "ARC103" => some ⟨"ARC_103_R"⟩
  | "ARC104" => some ⟨"ARC_104_Y"⟩
  | "ARC105" => some ⟨"ARC_105_B"⟩
  | "ARC106" => some ⟨"ARC_106_R"⟩
  | "ARC107" => some ⟨"ARC_107_Y"⟩
  | "ARC108" => some ⟨"ARC_108_B"⟩
  | "ARC109" => some ⟨"ARC_109_R"⟩
  | "ARC110" => some ⟨"ARC_110_Y"⟩
  | "ARC111" => some ⟨"ARC_111_B"⟩
  | "ARC112" | "ARC112-T" => some ⟨"ARC_112"⟩
  | "ARC113" | "HER020" | "HER020-P" => some ⟨"ARC_113"⟩
  | "ARC114" | "HER016" | "HER016-P" => some ⟨"ARC_114"⟩
  | "ARC115" => some ⟨"ARC_115"⟩
  | "ARC116" => some ⟨"ARC_116"⟩
  | "ARC117" => some ⟨"ARC_117"⟩
  | "ARC118" => some ⟨"ARC_118_R"⟩
  | "ARC119" => some ⟨"ARC_119_Y"⟩
  | "ARC120" => some ⟨"ARC_120_R"⟩
  | "ARC121" => some ⟨"ARC_121_Y"⟩
  | "ARC122" => some ⟨"ARC_122_R"⟩
  | "ARC123" => some ⟨"ARC_123_R"⟩
  | "ARC124" => some ⟨"ARC_124_Y"⟩
  -- Arcane Rising reprint of the existing WTR resource.
  | "ARC218" => some ⟨"WTR_224_Y"⟩
  | _ => none

end FabCards

end
