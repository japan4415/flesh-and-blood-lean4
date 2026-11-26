module

public import Fab.Tournament.Draft

@[expose] public section

namespace FabCards

open Fab

/-- Welcome to Rathe draft boosters have fifteen draftable slots and one basic-rarity slot
(TRP Appendix F; official Welcome to Rathe Collector's Centre). -/
def wtrDraft : BoosterDraft.Product :=
  ⟨.wtr, 15, 16, [
    "WTR_001", "WTR_002", "WTR_003", "WTR_038", "WTR_039", "WTR_040", "WTR_075",
    "WTR_076", "WTR_077", "WTR_078", "WTR_113", "WTR_114", "WTR_115", "WTR_224_Y", "WTR_225"
  ].map CardId.mk⟩

/-- Arcane Rising draft boosters have the same slot counts. ARC218 is a reprint of WTR224
(TRP Appendix F; official Arcane Rising Collector's Centre). -/
def arcDraft : BoosterDraft.Product :=
  ⟨.arc, 15, 16, [
    "ARC_001", "ARC_002", "ARC_003", "ARC_038", "ARC_039", "ARC_040", "ARC_075", "ARC_076",
    "ARC_077", "ARC_112", "ARC_113", "ARC_114", "ARC_115", "WTR_224_Y"
  ].map CardId.mk⟩

end FabCards

end
