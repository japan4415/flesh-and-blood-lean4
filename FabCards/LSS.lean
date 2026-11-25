module

public import Fab.Card.CardDef

@[expose] public section

namespace FabCards.LSS

open Fab

/-- Go Bananas, a special-use promo for social play (CR 1.9.1a). -/
def LSS_002_Y : CardDef :=
  { id := ⟨"LSS_002_Y"⟩
    front :=
      { name := "Go Bananas", supertypes := [.generic], types := [.instant]
        color := some .yellow, pitch := some 2, cost := some {}
        playEffect := some { body := .prim (.openBoosters none) } }
    sets := [⟨"LSS"⟩]
    status := .full }

end FabCards.LSS

end
