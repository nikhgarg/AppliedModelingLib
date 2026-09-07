import AppliedModelingLib.MechanismDesign.Auctions.Combinatorial

/-!
# The source-feasible generalized Vickrey auction

LOS02 Section 3 defines an allocation as a partial assignment of goods, so
Equation (4) maximizes over feasible allocations, not arbitrary overlapping
bundles. This module supplies that restriction at the paper use site of the
reusable Clarke-pivot identities. Reports and deviations use the source's
nonnegative valuation domain. No efficiency conclusion is assumed: the
maximization premise is the definition of the source GVA allocation rule.
-/

namespace LOS02CombinatorialAuctions
namespace SourceGVA

open AppliedModelingLib.Auction

/-- Section 3's valuation and message domain, on the fixed finite bidder and
goods carriers. -/
def Admissible {Bidder Item : Type*} [Fintype Bidder] [Fintype Item]
    (D : CombinatorialReport Bidder Item) : Prop :=
  ∀ i S, 0 ≤ D i S

/-- Equation (4), with the source outcome space of feasible partial allocations. -/
def MaximizesFeasible {Bidder Item : Type*} [Fintype Bidder] [Fintype Item]
    (alloc : CombinatorialReport Bidder Item → BundleAllocation Bidder Item) : Prop := by
  classical
  exact ∀ D, Admissible D →
    IsFeasibleBundleAllocation (alloc D) Finset.univ ∧
    ∀ A, IsFeasibleBundleAllocation A Finset.univ →
      allocationValue D A ≤ allocationValue D (alloc D)

/-- Definition 3.2: fixing every other declaration, no legal report improves utility. -/
def Truthful {Bidder Item : Type*} [Fintype Bidder] [Fintype Item]
    (M : CombinatorialAuction Bidder Item) : Prop := by
  classical
  exact ∀ D, Admissible D → ∀ i (report : Bundle Item → ℝ),
    (∀ S, 0 ≤ report S) →
    M.utility D (Function.update D i report) i ≤ M.utility D D i

/-- Equations (5)–(6): the Clarke-pivot payment for the chosen allocation rule. -/
noncomputable def auction {Bidder Item : Type*} [Fintype Bidder]
    (alloc : CombinatorialReport Bidder Item → BundleAllocation Bidder Item) :
    CombinatorialAuction Bidder Item := by
  classical
  exact generalizedVickreyAuction alloc

private theorem admissible_update {Bidder Item : Type*} [Fintype Bidder] [Fintype Item]
    [DecidableEq Bidder]
    {D : CombinatorialReport Bidder Item} (hD : Admissible D)
    (i : Bidder) (report : Bundle Item → ℝ) (hr : ∀ S, 0 ≤ report S) :
    Admissible (Function.update D i report) := by
  intro j S
  by_cases hji : j = i
  · subst j
    simpa using hr S
  · simpa [Function.update, hji] using hD j S

/-- Theorem 4.1 on the source outcome and declaration spaces. -/
theorem truthful {Bidder Item : Type*} [Fintype Bidder] [Fintype Item]
    (alloc : CombinatorialReport Bidder Item → BundleAllocation Bidder Item)
    (hmax : MaximizesFeasible alloc) :
    Truthful (auction alloc) := by
  classical
  intro D hD i report hr
  change (generalizedVickreyAuction alloc).utility D (Function.update D i report) i ≤
    (generalizedVickreyAuction alloc).utility D D i
  rw [generalizedVickreyAuction_utility_update_eq,
    generalizedVickreyAuction_utility_truth_eq]
  exact sub_le_sub_right ((hmax D hD).2 _
    ((hmax _ (admissible_update hD i report hr)).1)) _

/-- Proposition 4.2 uses only the truthful bidder's nonnegative valuation. -/
theorem truthful_utility_nonneg {Bidder Item : Type*}
    [Fintype Bidder] [Fintype Item]
    (alloc : CombinatorialReport Bidder Item → BundleAllocation Bidder Item)
    (hmax : MaximizesFeasible alloc)
    (D : CombinatorialReport Bidder Item) (hD : Admissible D) (i : Bidder) :
    0 ≤ (auction alloc).utility D D i := by
  classical
  change 0 ≤ (generalizedVickreyAuction alloc).utility D D i
  rw [generalizedVickreyAuction_utility_truth_eq]
  have hz : Admissible (reportsWithoutBidder D i) :=
    admissible_update hD i (fun _ => 0) (fun _ => le_refl 0)
  have halloc := (hmax D hD).2 _ ((hmax _ hz).1)
  have hsplit := allocationValue_eq_self_add_except D
    (alloc (reportsWithoutBidder D i)) i
  have hnonneg := hD i ((alloc (reportsWithoutBidder D i)) i)
  linarith

end SourceGVA
end LOS02CombinatorialAuctions
