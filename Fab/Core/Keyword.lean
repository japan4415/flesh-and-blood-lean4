module

/-!
# Keywords

Ability and meta-static keywords printed on cards (CR 8.1-8.3).
Includes all WTR keywords and core FaB keywords for forward compatibility.
-/

@[expose] public section

namespace Fab

/-- A keyword instance printed on or granted to an object (CR 8.3). -/
inductive KeywordInst where
  /-- Action / attack grants +1 AP on resolution or Resolution Step (CR 8.3.5). -/
  | goAgain
  /-- Defending hero cannot defend with more than one card from hand (CR 8.3.4). -/
  | dominate
  /-- Defending hero cannot defend with more than one action card (CR 8.3.26). -/
  | overpower
  /-- Equipment gets a `-1{d}` counter on combat chain close if it defended (CR 8.3.2). -/
  | battleworn
  /-- Equipment is destroyed on combat chain close if it defended (CR 8.3.3). -/
  | bladeBreak
  /-- Equipment gets `-1{d}` on close if it defended and is destroyed at 0 or less (CR 8.3.10). -/
  | temper
  /-- Equipment gets `-1{d}` counters equal to its `{d}` on close if it defended (CR 8.3.36). -/
  | guardwell
  /-- Attack checks whether a named card was the previous link on the chain (CR 8.3.6). -/
  | combo
  /-- Attack triggers when dealing 4 or more damage to a hero (CR 8.3.7). -/
  | crush
  /-- Attack reaction / effect checks whether defender defended from hand (CR 8.3.8). -/
  | reprise
  /-- At most 1 copy by card name in a constructed card-pool (CR 8.3.15). -/
  | legendary
  /-- Card may only be included in a card-pool whose hero matches `heroName` (CR 8.3.16). -/
  | specialization (heroName : String)
  /-- Exempt from standard copy limits in deck construction. -/
  | unlimited
  /-- Card may be included in any hero's card-pool regardless of supertypes. -/
  | universal
  /-- Prevent up to `n` arcane damage by paying `{r}` equal to `n` (CR 8.3.1). -/
  | arcaneBarrier (n : Nat)
  /-- Prevent up to `n` arcane damage by destroying this object (CR 8.3.11). -/
  | spellvoid (n : Nat)
  /-- Prevent up to `n` damage by paying `{r}` equal to `n` and destroying at end of chain (CR 8.3.19). -/
  | quell (n : Nat)
  /-- Mandatory replacement: destroy this to prevent `n` damage to your hero (CR 8.3.21). -/
  | ward (n : Nat)
  /-- Destroy attack and close chain if defended by non-Illusionist 6+ power attack action (CR 8.3.13). -/
  | phantasm
  /-- Permanent can be attacked; when targeted by an attack, destroy it and close chain (CR 8.3.14). -/
  | spectra
  /-- Lose 1 life at beginning of end phase while face-up in banished zone (CR 8.3.12). -/
  | bloodDebt
  /-- Optional banish top of deck for go again (CR 8.3.9). -/
  | boost
  /-- Stealth label keyword (CR 8.3.24). -/
  | stealth
  /-- Flip to back face and put into owner's hand (CR 8.3). -/
  | transcend
  /-- Split card may be played for both halves via alternative cost (CR 8.3.38). -/
  | meld
  /-- Equipment may be equipped on top of a Base equipment. -/
  | evo
  /-- Equipment may be placed in any equipment slot. -/
  | modular
  /-- Equipment starts the game face-down in the arena. -/
  | cloaked
  /-- Attack gains +`n` power if defended by equipment. -/
  | piercing (n : Nat)
  /-- Card may be played / defended from banished or arsenal under ambush rules. -/
  | ambush
  /-- Card ceases to exist if it would be put into a graveyard or deck. -/
  | ephemeral
deriving DecidableEq, Repr, Hashable

end Fab

end
