module

/-!
# Rules version

The versions of the Flesh and Blood Comprehensive Rules (CR) and Tournament Rules and Policy (TRP)
that every `(CR ...)` / `(TRP ...)` citation in this repository refers to (design.md §9).
-/

@[expose] public section

namespace Fab

/-- A calendar date identifying when an official rules document was published or updated. -/
structure RulesDate where
  /-- Year. -/
  year : Nat
  /-- Month, 1 to 12. -/
  month : Nat
  /-- Day of month, 1 to 31. -/
  day : Nat
deriving DecidableEq, Repr

/-- Semantic version `[major].[minor].[patch]` used by the Flesh and Blood Comprehensive Rules. -/
structure SemVer where
  /-- Major version number. -/
  major : Nat
  /-- Minor version number. -/
  minor : Nat
  /-- Patch version number. -/
  patch : Nat
deriving DecidableEq, Repr

/-- Version metadata for the Comprehensive Rules (semantic version plus release date). -/
structure ComprehensiveRulesVersion where
  /-- Semantic version number on `rules.fabtcg.com`. -/
  semver : SemVer
  /-- Publication date. -/
  date : RulesDate
deriving DecidableEq, Repr

/-- The Flesh and Blood Comprehensive Rules version that citations `(CR ...)` refer to.
Hosted on `https://rules.fabtcg.com`. -/
def comprehensiveRulesVersion : ComprehensiveRulesVersion :=
  ⟨⟨2, 15, 0⟩, ⟨2026, 9, 28⟩⟩

/-- The Flesh and Blood Tournament Rules and Policy date that citations `(TRP ...)` refer to.
Hosted on `https://rules.fabtcg.com`. -/
def tournamentRulesVersion : RulesDate :=
  ⟨2025, 5, 30⟩

/-- A calendar date is well formed when its month and day are in basic calendar range. -/
def RulesDate.WellFormed (d : RulesDate) : Prop :=
  1 ≤ d.month ∧ d.month ≤ 12 ∧ 1 ≤ d.day ∧ d.day ≤ 31

instance RulesDate.decidableWellFormed (d : RulesDate) : Decidable d.WellFormed := by
  unfold RulesDate.WellFormed; infer_instance

/-- The Comprehensive Rules release date is well formed. -/
theorem comprehensiveRulesVersion_wellFormed :
    comprehensiveRulesVersion.date.WellFormed := by decide

/-- The Tournament Rules and Policy update date is well formed. -/
theorem tournamentRulesVersion_wellFormed :
    tournamentRulesVersion.WellFormed := by decide

end Fab

end
