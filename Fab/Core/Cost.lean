module

/-!
# Asset costs and asset pools

Asset-costs (Action Points, Resource Points, Chi Points, Life Points) and their payment arithmetic
(CR 1.14.2, 5.1.5-5.1.6). Chi points can pay both chi costs and generic resource costs (CR 1.14.2b).
-/

@[expose] public section

namespace Fab

/-- Asset-cost required to play a card or activate an ability (CR 1.14.2). -/
structure AssetCost where
  /-- Action points required (1 for standard Actions, 0 for Instants and Reactions). -/
  actionPoints : Nat := 0
  /-- Generic resource points `{r}` required. -/
  resources : Nat := 0
  /-- Chi points `{c}` required (payable only with chi). -/
  chi : Nat := 0
  /-- Life points required as an asset-cost. -/
  life : Nat := 0
deriving DecidableEq, Repr, Hashable

/-- A player's currently available turn-scoped asset points (CR 1.14.2, 4.4.3e). -/
structure AssetPool where
  /-- Current Action Points. -/
  actionPoints : Nat := 0
  /-- Current Resource Points `{r}`. -/
  resources : Nat := 0
  /-- Current Chi Points `{c}`. -/
  chi : Nat := 0
deriving DecidableEq, Repr, Hashable

/-- The zero asset-cost. -/
def AssetCost.zero : AssetCost := {}

/-- The empty asset pool, matching End Phase cleanup (CR 4.4.3e). -/
def AssetPool.empty : AssetPool := {}

/-- Add two asset costs component-wise. -/
def AssetCost.add (a b : AssetCost) : AssetCost :=
  { actionPoints := a.actionPoints + b.actionPoints
    resources := a.resources + b.resources
    chi := a.chi + b.chi
    life := a.life + b.life }

/-- Apply a resource cost increase and reduction, floored at zero (CR 5.1.5). -/
def AssetCost.modifyResources (c : AssetCost) (increase reduction : Nat) : AssetCost :=
  { c with resources := c.resources + increase - reduction }

/-- Resource cost after modification is unchanged when increase equals reduction. -/
theorem AssetCost.modifyResources_cancel (c : AssetCost) (n : Nat) :
    (c.modifyResources n n).resources = c.resources := by
  unfold AssetCost.modifyResources
  dsimp only
  omega

/-- Reducing a resource cost never increases it. -/
theorem AssetCost.modifyResources_reduce_le (c : AssetCost) (r : Nat) :
    (c.modifyResources 0 r).resources ≤ c.resources := by
  unfold AssetCost.modifyResources
  dsimp only
  omega

/-- Add resource points `{r}` to a pool, for example by pitching a card (CR 1.14.3). -/
def AssetPool.addResources (p : AssetPool) (n : Nat) : AssetPool :=
  { p with resources := p.resources + n }

/-- Add chi points `{c}` to a pool, for example by pitching a chi card (CR 1.14.3). -/
def AssetPool.addChi (p : AssetPool) (n : Nat) : AssetPool :=
  { p with chi := p.chi + n }

/-- Add action points, for example at Action Phase start or via Go Again (CR 4.3.2, 7.6.2). -/
def AssetPool.addActionPoints (p : AssetPool) (n : Nat) : AssetPool :=
  { p with actionPoints := p.actionPoints + n }

/-- Total energy-like points (resources plus chi) in an asset pool. -/
def AssetPool.totalEnergy (p : AssetPool) : Nat :=
  p.resources + p.chi

/-- Whether a pool can pay the AP, resource, and chi portions of an `AssetCost`.
Chi may cover generic resource costs once strict chi costs are satisfied (CR 1.14.2b). -/
def AssetPool.canPay (p : AssetPool) (c : AssetCost) : Prop :=
  c.actionPoints ≤ p.actionPoints ∧
  c.chi ≤ p.chi ∧
  c.resources + c.chi ≤ p.resources + p.chi

instance AssetPool.decidableCanPay (p : AssetPool) (c : AssetCost) :
    Decidable (p.canPay c) := by
  unfold AssetPool.canPay
  infer_instance

/-- How much generic resource deficit remains before the pool can satisfy `c`, used to enforce
no over-pitching (CR 1.14.3b). -/
def AssetPool.resourceDeficit (p : AssetPool) (c : AssetCost) : Nat :=
  let spareChi := p.chi - c.chi
  c.resources - (p.resources + spareChi)

/-- How much strict chi deficit remains before the pool can satisfy `c` (CR 1.14.3b). -/
def AssetPool.chiDeficit (p : AssetPool) (c : AssetCost) : Nat :=
  c.chi - p.chi

/-- Whether pitching for generic resources is currently legal when deficit > 0 (CR 1.14.3b). -/
def AssetPool.needsResources (p : AssetPool) (c : AssetCost) : Prop :=
  0 < p.resourceDeficit c

instance AssetPool.decidableNeedsResources (p : AssetPool) (c : AssetCost) :
    Decidable (p.needsResources c) := by
  unfold AssetPool.needsResources
  infer_instance

/-- Pay an `AssetCost` from an `AssetPool`, consuming strict chi first, then chi/resources for
generic resources (preferring chi for resources only when resources are insufficient, or consuming
explicitly chosen chi amount `chiForRes`) (CR 1.14.2b, 5.1.6). -/
def AssetPool.spend (p : AssetPool) (c : AssetCost) (chiForRes : Nat := 0) :
    Option AssetPool :=
  let totalChi := c.chi + chiForRes
  if c.actionPoints ≤ p.actionPoints ∧
      chiForRes ≤ c.resources ∧
      totalChi ≤ p.chi ∧
      c.resources - chiForRes ≤ p.resources then
    some
      { actionPoints := p.actionPoints - c.actionPoints
        resources := p.resources - (c.resources - chiForRes)
        chi := p.chi - totalChi }
  else
    none

/-- If `spend` succeeds, then `canPay` holds (soundness of `spend`). -/
theorem AssetPool.canPay_of_spend_some {p p' : AssetPool} {c : AssetCost} {chiForRes : Nat}
    (h : p.spend c chiForRes = some p') :
    p.canPay c := by
  unfold AssetPool.spend at h
  dsimp only at h
  split at h
  · rename_i hcond
    unfold AssetPool.canPay
    omega
  · cases h

/-- If `canPay` holds, there exists a valid `chiForRes` choice for which `spend` succeeds
(completeness of `spend`). -/
theorem AssetPool.exists_spend_of_canPay {p : AssetPool} {c : AssetCost}
    (h : p.canPay c) :
    ∃ chiForRes p', p.spend c chiForRes = some p' := by
  unfold AssetPool.canPay at h
  refine ⟨c.resources - p.resources, ?_, ?_⟩
  · exact
      { actionPoints := p.actionPoints - c.actionPoints
        resources := p.resources - (c.resources - (c.resources - p.resources))
        chi := p.chi - (c.chi + (c.resources - p.resources)) }
  · unfold AssetPool.spend
    dsimp only
    have hcond : c.actionPoints ≤ p.actionPoints ∧
        c.resources - p.resources ≤ c.resources ∧
        c.chi + (c.resources - p.resources) ≤ p.chi ∧
        c.resources - (c.resources - p.resources) ≤ p.resources := by omega
    simp only [hcond, and_self, ite_true]

/-- Paying an asset-cost deducts exact action points and exact combined resources + chi
(CR 1.14.2). -/
theorem AssetPool.spend_accounting {p p' : AssetPool} {c : AssetCost} {chiForRes : Nat}
    (h : p.spend c chiForRes = some p') :
    p'.actionPoints + c.actionPoints = p.actionPoints ∧
    p'.totalEnergy + (c.resources + c.chi) = p.totalEnergy := by
  unfold AssetPool.spend at h
  dsimp only at h
  split at h
  · rename_i hcond
    cases h
    unfold AssetPool.totalEnergy
    dsimp only
    omega
  · cases h

/-- When `canPay` holds (with sufficient chi), there is no resource deficit, so pitching for
resources is illegal under no over-pitching (CR 1.14.3b). -/
theorem AssetPool.not_needsResources_of_canPay {p : AssetPool} {c : AssetCost}
    (h : p.canPay c) :
    ¬ p.needsResources c := by
  unfold AssetPool.canPay at h
  unfold AssetPool.needsResources AssetPool.resourceDeficit
  dsimp only
  omega

/-- Generic resources alone cannot pay a non-zero strict chi cost (CR 1.14.2b). -/
theorem AssetPool.not_canPay_chi_without_chi {p : AssetPool} {c : AssetCost}
    (hp : p.chi = 0) (hc : 0 < c.chi) :
    ¬ p.canPay c := by
  unfold AssetPool.canPay
  omega

end Fab

end
