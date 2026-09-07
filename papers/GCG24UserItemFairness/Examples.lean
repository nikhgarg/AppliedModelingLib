import GCG24UserItemFairness.Symmetry

namespace GCG24UserItemFairness

/-- A `2 × 2` utility matrix with opposite user preferences. -/
def twoByTwoUtility : User 2 → Item 2 → ℝ :=
  fun u j => if u = j then 10 else 1

/-- A tiny instance useful for notation and smoke tests. -/
noncomputable def twoByTwoModel : RecommendationModel 2 2 where
  utility := twoByTwoUtility

/-- A deterministic policy that recommends item `u` to user `u`. -/
noncomputable def diagonalPolicy : Policy 2 2 :=
  AppliedModelingLib.Policy.pure (fun u => u)

/-- A deterministic policy that flips the two users' preferred items. -/
noncomputable def swappedPolicy : Policy 2 2 :=
  AppliedModelingLib.Policy.pure (fun u => if u = 0 then (1 : Item 2) else 0)

/-- In the toy instance, each user's favorite item has utility `10`. -/
theorem twoByTwoModel_bestItemUtility_eq (u : User 2) :
    RecommendationModel.bestItemUtility twoByTwoModel u = 10 := by
  apply le_antisymm
  · unfold RecommendationModel.bestItemUtility AppliedModelingLib.finiteMax
    apply Finset.sup'_le
    intro j _hj
    fin_cases u <;> fin_cases j <;> norm_num [twoByTwoModel, twoByTwoUtility]
  · simpa [RecommendationModel.bestItemUtility, twoByTwoModel, twoByTwoUtility] using
      (AppliedModelingLib.le_finiteMax (twoByTwoModel.utility u) u)

/-- In the toy instance, each item has total utility `11` across the two users. -/
theorem twoByTwoModel_itemNormalizer_eq (j : Item 2) :
    RecommendationModel.itemNormalizer twoByTwoModel j = 11 := by
  fin_cases j <;>
    norm_num [RecommendationModel.itemNormalizer, twoByTwoModel, twoByTwoUtility]

/-- Under the favorite-item policy, each item receives raw utility `10`. -/
theorem twoByTwoModel_diagonal_rawItemUtility_eq (j : Item 2) :
    RecommendationModel.rawItemUtility twoByTwoModel diagonalPolicy j = 10 := by
  fin_cases j <;>
    norm_num [RecommendationModel.rawItemUtility, diagonalPolicy, twoByTwoModel,
      twoByTwoUtility, AppliedModelingLib.Policy.pure, PMF.pure_apply]

/-- In the two-item diverse-preferences toy instance, recommending each user
their favorite item gives every user her maximum normalized utility. -/
theorem paper_example1_diagonal_userFairness_eq_one :
    RecommendationModel.userFairness twoByTwoModel diagonalPolicy = 1 := by
  unfold RecommendationModel.userFairness
  apply AppliedModelingLib.finiteMin_eq_of_forall
  intro u
  have hraw : RecommendationModel.rawUserUtility twoByTwoModel diagonalPolicy u = 10 := by
    unfold RecommendationModel.rawUserUtility
    rw [diagonalPolicy, AppliedModelingLib.Policy.agentScore_pure]
    fin_cases u <;> norm_num [twoByTwoModel, twoByTwoUtility]
  rw [RecommendationModel.normalizedUserUtility, hraw,
    twoByTwoModel_bestItemUtility_eq]
  norm_num

/-- In the same toy instance, the favorite-item policy gives both items the
same normalized utility. -/
theorem paper_example1_diagonal_itemFairness_eq :
    RecommendationModel.itemFairness twoByTwoModel diagonalPolicy = (10 : ℝ) / 11 := by
  unfold RecommendationModel.itemFairness
  apply AppliedModelingLib.finiteMin_eq_of_forall
  intro j
  rw [RecommendationModel.normalizedItemUtility,
    twoByTwoModel_itemNormalizer_eq,
    twoByTwoModel_diagonal_rawItemUtility_eq]
  norm_num

/-- The homogeneous-preferences algebra in Example 1: if the second item
bounds item fairness and user fairness is bounded by the first-item probability
plus `ε`, then the two fairness objectives obey the displayed linear tradeoff. -/
theorem paper_example1_homogeneous_tradeoff_bound
    {epsilon rho1 rho2 Umin Imin : ℝ}
    (hrho : rho2 = 1 - rho1)
    (hitem : Imin ≤ rho2)
    (huser : Umin ≤ rho1 + epsilon) :
    Umin + Imin ≤ 1 + epsilon := by
  nlinarith

/-- The obvious two-type partition for the `2 × 2` toy instance. -/
def twoTypeAssignment : RecommendationModel.UserTypeAssignment 2 2 where
  toType := fun u => u

/-- A toy estimated model that swaps the two rows of the utility matrix. -/
noncomputable def twoByTwoEstimated : EstimatedRecommendationModel 2 2 where
  trueModel := twoByTwoModel
  estimatedUtility u j := twoByTwoUtility (if u = 0 then (1 : User 2) else 0) j

end GCG24UserItemFairness
