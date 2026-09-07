import Mathlib.Order.Interval.Finset.Fin
import GCG24UserItemFairness.OpposingTypes

open scoped BigOperators
open AppliedModelingLib

namespace GCG24UserItemFairness
namespace OpposingTypes

/-!
Appendix E helper definitions for Theorem 4.

The paper's misestimation construction has three estimated user types: the two
opposing known types and a cold-start type whose estimated values are the
average of those two rows.  The true cold-start row is one of the two opposing
rows.  This file isolates the model definitions and the utility bounds used in
the final price-of-misestimation argument.
-/

/-- The first item, corresponding to paper index `1`. -/
def theorem4FirstItem {n : ℕ} [NeZero n] : Item n :=
  ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩

/-- The second item, corresponding to paper index `2`. -/
def theorem4SecondItem {n : ℕ} (hn : 1 < n) : Item n :=
  ⟨1, hn⟩

/-- The last item, corresponding to paper index `n`. -/
def theorem4LastItem {n : ℕ} [NeZero n] : Item n :=
  reverseItem theorem4FirstItem

@[simp] theorem theorem4FirstItem_val {n : ℕ} [NeZero n] :
    (theorem4FirstItem : Item n).val = 0 := rfl

@[simp] theorem theorem4SecondItem_val {n : ℕ} (hn : 1 < n) :
    (theorem4SecondItem hn : Item n).val = 1 := rfl

@[simp] theorem reverseItem_theorem4LastItem {n : ℕ} [NeZero n] :
    reverseItem (theorem4LastItem : Item n) = theorem4FirstItem := by
  simp [theorem4LastItem, reverseItem_reverseItem]

theorem reverseItem_ne_of_ne_reverse {n : ℕ} {i j : Item n}
    (h : i ≠ reverseItem j) :
    reverseItem i ≠ j := by
  intro hrev
  apply h
  calc
    i = reverseItem (reverseItem i) := (reverseItem_reverseItem i).symm
    _ = reverseItem j := by rw [hrev]

theorem eq_theorem4FirstItem_of_val_eq_zero {n : ℕ} [NeZero n]
    {j : Item n} (hj : j.val = 0) :
    j = theorem4FirstItem := by
  ext
  simpa using hj

theorem theorem4FirstItem_ne_of_val_pos {n : ℕ} [NeZero n]
    {j : Item n} (hj : 0 < j.val) :
    j ≠ theorem4FirstItem := by
  intro h
  rw [h] at hj
  simp at hj

theorem theorem4FirstItem_val_lt_of_ne {n : ℕ} [NeZero n]
    {j : Item n} (hj : j ≠ theorem4FirstItem) :
    (theorem4FirstItem : Item n).val < j.val := by
  have hval_ne : j.val ≠ 0 := by
    intro hzero
    exact hj (eq_theorem4FirstItem_of_val_eq_zero hzero)
  simpa using Nat.pos_of_ne_zero hval_ne

/--
In the strictly decreasing value vector, every non-first item has value at most
the second item.
-/
theorem theorem4_value_le_second_of_ne_first
    {n : ℕ} [NeZero n] {v : Item n → ℝ}
    (hn : 1 < n) (hdec : StrictlyDecreasingByIndex v)
    {j : Item n} (hj : j ≠ theorem4FirstItem) :
    v j ≤ v (theorem4SecondItem hn) := by
  have hjpos : 0 < j.val := by
    have hval_ne : j.val ≠ 0 := by
      intro hzero
      exact hj (eq_theorem4FirstItem_of_val_eq_zero hzero)
    exact Nat.pos_of_ne_zero hval_ne
  have hle : (theorem4SecondItem hn : Item n).val ≤ j.val := by
    simpa using hjpos
  exact value_antitone_of_val_le hdec hle

/--
The geometric value vector used for the small-`v₂` witness in Theorem 4.
The first item has value `1`; each later item is smaller by the ratio
`min (1/2) (eps / (2n))`.
-/
noncomputable def theorem4SmallValueVector {n : ℕ} (eps : ℝ) : Item n → ℝ :=
  fun j => (min (1 / 2 : ℝ) (eps / (2 * (n : ℝ)))) ^ j.val

theorem theorem4SmallValueVector_ratio_pos
    {n : ℕ} [NeZero n] {eps : ℝ} (heps : 0 < eps) :
    0 < min (1 / 2 : ℝ) (eps / (2 * (n : ℝ))) := by
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hden_pos : 0 < 2 * (n : ℝ) := mul_pos (by norm_num) hnpos
  exact lt_min (by norm_num) (div_pos heps hden_pos)

theorem theorem4SmallValueVector_ratio_lt_one
    {n : ℕ} {eps : ℝ} :
    min (1 / 2 : ℝ) (eps / (2 * (n : ℝ))) < 1 := by
  exact lt_of_le_of_lt (min_le_left _ _) (by norm_num)

theorem theorem4SmallValueVector_ratio_lt_eps_div_card
    {n : ℕ} [NeZero n] {eps : ℝ} (heps : 0 < eps) :
    min (1 / 2 : ℝ) (eps / (2 * (n : ℝ))) < eps / (n : ℝ) := by
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hdiv_pos : 0 < eps / (n : ℝ) := div_pos heps hnpos
  have hhalf :
      eps / (2 * (n : ℝ)) = eps / (n : ℝ) / 2 := by
    ring
  have hhalf_lt : eps / (2 * (n : ℝ)) < eps / (n : ℝ) := by
    rw [hhalf]
    linarith
  exact lt_of_le_of_lt (min_le_right _ _) hhalf_lt

theorem theorem4SmallValueVector_pos
    {n : ℕ} [NeZero n] {eps : ℝ} (heps : 0 < eps) :
    ∀ j : Item n, 0 < theorem4SmallValueVector eps j := by
  intro j
  exact pow_pos (theorem4SmallValueVector_ratio_pos heps) j.val

theorem theorem4SmallValueVector_strictlyDecreasing
    {n : ℕ} [NeZero n] {eps : ℝ} (heps : 0 < eps) :
    StrictlyDecreasingByIndex (theorem4SmallValueVector (n := n) eps) := by
  intro i j hij
  exact (pow_right_strictAnti₀
    (theorem4SmallValueVector_ratio_pos (n := n) heps)
    (theorem4SmallValueVector_ratio_lt_one (n := n) (eps := eps))) hij

theorem theorem4SmallValueVector_first_eq_one
    {n : ℕ} [NeZero n] {eps : ℝ} :
    theorem4SmallValueVector (n := n) eps theorem4FirstItem = 1 := by
  simp [theorem4SmallValueVector]

theorem theorem4SmallValueVector_second_eq_ratio
    {n : ℕ} [NeZero n] {eps : ℝ} (hn : 1 < n) :
    theorem4SmallValueVector (n := n) eps (theorem4SecondItem hn) =
      min (1 / 2 : ℝ) (eps / (2 * (n : ℝ))) := by
  simp [theorem4SmallValueVector]

/--
Appendix E, Theorem 4 value-vector witness: for any `eps > 0`, there is a
positive strictly decreasing value vector whose second value is below
`eps * v₁ / n`.
-/
theorem theorem4_valueVector_exists_small_second
    {n : ℕ} [NeZero n] (hn : 1 < n) {eps : ℝ} (heps : 0 < eps) :
    ∃ v : Item n → ℝ,
      (∀ j : Item n, 0 < v j) ∧
      StrictlyDecreasingByIndex v ∧
      v (theorem4SecondItem hn) <
        eps / (n : ℝ) * v theorem4FirstItem := by
  refine ⟨theorem4SmallValueVector (n := n) eps,
    theorem4SmallValueVector_pos heps,
    theorem4SmallValueVector_strictlyDecreasing heps, ?_⟩
  rw [theorem4SmallValueVector_first_eq_one,
    theorem4SmallValueVector_second_eq_ratio hn, mul_one]
  exact theorem4SmallValueVector_ratio_lt_eps_div_card heps

/-- The first item attains the finite maximum of a strictly decreasing vector. -/
theorem theorem4_finiteMax_eq_first
    {n : ℕ} [NeZero n] {v : Item n → ℝ}
    (hdec : StrictlyDecreasingByIndex v) :
    AppliedModelingLib.finiteMax v = v theorem4FirstItem := by
  apply le_antisymm
  · obtain ⟨j, hj⟩ := AppliedModelingLib.exists_finiteMax_eq v
    rw [hj]
    have hle : (theorem4FirstItem : Item n).val ≤ j.val := by
      simp
    exact value_antitone_of_val_le hdec hle
  · exact AppliedModelingLib.le_finiteMax v theorem4FirstItem

/--
The estimated three-type reduced model from Appendix E. Types `0` and `1` are
the known opposing rows, while type `2` is the cold-start row estimated as the
average of the two.
-/
noncomputable def theorem4EstimatedReducedModel {n : ℕ}
    (beta : ℝ) (v : Item n → ℝ) :
    TypeWeightedRecommendationModel 3 n where
  utility k j :=
    if k = (0 : UserType 3) then v j
    else if k = (1 : UserType 3) then v (reverseItem j)
    else (v j + v (reverseItem j)) / 2
  weight k :=
    if k = (0 : UserType 3) then beta
    else if k = (1 : UserType 3) then beta
    else 1 - 2 * beta

/--
In the corrected three-mass estimated model, occurrence of all declared types
makes the cold-start mass `1 - 2 * beta` positive. This derives the upper beta
domain used by the theorem construction from the source model itself.
-/
theorem theorem4_beta_lt_half_of_estimated_reduction
    {m n : Nat} [NeZero m] [NeZero n]
    (Sest : RecommendationModel.SymmetricData m n 3)
    (hTypesEst : Function.Surjective Sest.types.toType)
    {beta : Real} {v : Item n -> Real}
    (hredEst :
      (Sest.canonicalReductionOfSurjective hTypesEst).reduced =
        theorem4EstimatedReducedModel beta v) :
    beta < 1 / 2 := by
  let repsEst : UserTypeAssignment.TypeRepresentatives Sest.types :=
    AppliedModelingLib.Policy.FiberRepresentatives.ofSurjective hTypesEst
  have hWeight :
      (Sest.canonicalReductionOfSurjective hTypesEst).reduced.PositiveWeights := by
    simpa [RecommendationModel.SymmetricData.canonicalReductionOfSurjective, repsEst] using
      (Sest.canonicalReduction repsEst).reduced_positiveWeights_of_representatives repsEst
  rw [hredEst] at hWeight
  have hcold : 0 < 1 - 2 * beta := by
    simpa [theorem4EstimatedReducedModel] using hWeight (2 : UserType 3)
  linarith

/--
The Theorem 4 beta domain entails at least three items. This is a numerical
consequence of `1 / n < beta < 1 / 2`, not a separate source assumption.
-/
theorem theorem4_at_least_three_items_of_beta_domain
    {n : Nat} [NeZero n] {beta : Real}
    (hbeta : (n : Real)⁻¹ < beta)
    (hbeta_half : beta < 1 / 2) :
    2 < n := by
  by_contra hnot
  have hn : n <= 2 := Nat.le_of_not_gt hnot
  have hn_ne_zero : n ≠ 0 := NeZero.ne n
  interval_cases n
  · exact hn_ne_zero rfl
  · norm_num at hbeta hbeta_half
    linarith
  · norm_num at hbeta hbeta_half
    linarith

/--
The true three-type model when the cold-start type's actual preferences are the
first opposing row.
-/
noncomputable def theorem4TrueReducedModelTypeZero {n : ℕ}
    (beta : ℝ) (v : Item n → ℝ) :
    TypeWeightedRecommendationModel 3 n where
  utility k j :=
    if k = (0 : UserType 3) then v j
    else if k = (1 : UserType 3) then v (reverseItem j)
    else v j
  weight k :=
    if k = (0 : UserType 3) then beta
    else if k = (1 : UserType 3) then beta
    else 1 - 2 * beta

/--
The true three-type model when the cold-start type's actual preferences are the
second opposing row.
-/
noncomputable def theorem4TrueReducedModelTypeOne {n : ℕ}
    (beta : ℝ) (v : Item n → ℝ) :
    TypeWeightedRecommendationModel 3 n where
  utility k j :=
    if k = (0 : UserType 3) then v j
    else if k = (1 : UserType 3) then v (reverseItem j)
    else v (reverseItem j)
  weight k :=
    if k = (0 : UserType 3) then beta
    else if k = (1 : UserType 3) then beta
    else 1 - 2 * beta

@[simp] theorem theorem4EstimatedReducedModel_utility_zero {n : ℕ}
    (beta : ℝ) (v : Item n → ℝ) (j : Item n) :
    (theorem4EstimatedReducedModel beta v).utility 0 j = v j := by
  simp [theorem4EstimatedReducedModel]

@[simp] theorem theorem4EstimatedReducedModel_utility_one {n : ℕ}
    (beta : ℝ) (v : Item n → ℝ) (j : Item n) :
    (theorem4EstimatedReducedModel beta v).utility 1 j =
      v (reverseItem j) := by
  simp [theorem4EstimatedReducedModel]

@[simp] theorem theorem4EstimatedReducedModel_utility_two {n : ℕ}
    (beta : ℝ) (v : Item n → ℝ) (j : Item n) :
    (theorem4EstimatedReducedModel beta v).utility 2 j =
      (v j + v (reverseItem j)) / 2 := by
  have h20 : (2 : UserType 3) ≠ 0 := by decide
  have h21 : (2 : UserType 3) ≠ 1 := by decide
  simp [theorem4EstimatedReducedModel, h20, h21]

@[simp] theorem theorem4TrueReducedModelTypeZero_utility_two {n : ℕ}
    (beta : ℝ) (v : Item n → ℝ) (j : Item n) :
    (theorem4TrueReducedModelTypeZero beta v).utility 2 j = v j := by
  have h20 : (2 : UserType 3) ≠ 0 := by decide
  have h21 : (2 : UserType 3) ≠ 1 := by decide
  simp [theorem4TrueReducedModelTypeZero, h20, h21]

@[simp] theorem theorem4TrueReducedModelTypeOne_utility_two {n : ℕ}
    (beta : ℝ) (v : Item n → ℝ) (j : Item n) :
    (theorem4TrueReducedModelTypeOne beta v).utility 2 j =
      v (reverseItem j) := by
  have h20 : (2 : UserType 3) ≠ 0 := by decide
  simp [theorem4TrueReducedModelTypeOne, h20]

theorem theorem4TrueReducedModelTypeZero_bestItemUtility_zero
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hdec : StrictlyDecreasingByIndex v) :
    TypeWeightedRecommendationModel.bestItemUtility
        (theorem4TrueReducedModelTypeZero beta v) 0 =
      v theorem4FirstItem := by
  change AppliedModelingLib.finiteMax (fun j : Item n => v j) =
    v theorem4FirstItem
  exact theorem4_finiteMax_eq_first hdec

theorem theorem4TrueReducedModelTypeZero_bestItemUtility_one
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hdec : StrictlyDecreasingByIndex v) :
    TypeWeightedRecommendationModel.bestItemUtility
        (theorem4TrueReducedModelTypeZero beta v) 1 =
      v theorem4FirstItem := by
  change AppliedModelingLib.finiteMax (fun j : Item n => v (reverseItem j)) =
    v theorem4FirstItem
  rw [finiteMax_reverseItem]
  exact theorem4_finiteMax_eq_first hdec

theorem theorem4TrueReducedModelTypeZero_bestItemUtility_two
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hdec : StrictlyDecreasingByIndex v) :
    TypeWeightedRecommendationModel.bestItemUtility
        (theorem4TrueReducedModelTypeZero beta v) 2 =
      v theorem4FirstItem := by
  change AppliedModelingLib.finiteMax (fun j : Item n => v j) =
    v theorem4FirstItem
  exact theorem4_finiteMax_eq_first hdec

theorem theorem4TrueReducedModelTypeOne_bestItemUtility_zero
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hdec : StrictlyDecreasingByIndex v) :
    TypeWeightedRecommendationModel.bestItemUtility
        (theorem4TrueReducedModelTypeOne beta v) 0 =
      v theorem4FirstItem := by
  change AppliedModelingLib.finiteMax (fun j : Item n => v j) =
    v theorem4FirstItem
  exact theorem4_finiteMax_eq_first hdec

theorem theorem4TrueReducedModelTypeOne_bestItemUtility_one
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hdec : StrictlyDecreasingByIndex v) :
    TypeWeightedRecommendationModel.bestItemUtility
        (theorem4TrueReducedModelTypeOne beta v) 1 =
      v theorem4FirstItem := by
  change AppliedModelingLib.finiteMax (fun j : Item n => v (reverseItem j)) =
    v theorem4FirstItem
  rw [finiteMax_reverseItem]
  exact theorem4_finiteMax_eq_first hdec

theorem theorem4TrueReducedModelTypeOne_bestItemUtility_two
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hdec : StrictlyDecreasingByIndex v) :
    TypeWeightedRecommendationModel.bestItemUtility
        (theorem4TrueReducedModelTypeOne beta v) 2 =
      v theorem4FirstItem := by
  change AppliedModelingLib.finiteMax (fun j : Item n => v (reverseItem j)) =
    v theorem4FirstItem
  rw [finiteMax_reverseItem]
  exact theorem4_finiteMax_eq_first hdec

/-- The estimated cold-start row's paper value `(v_j + v_{n-j+1}) / 2`. -/
noncomputable def theorem4AverageUtility {n : ℕ} (v : Item n → ℝ)
    (j : Item n) : ℝ :=
  (v j + v (reverseItem j)) / 2

@[simp] theorem theorem4AverageUtility_reverse {n : ℕ} [NeZero n]
    (v : Item n → ℝ) (j : Item n) :
    theorem4AverageUtility v (reverseItem j) =
      theorem4AverageUtility v j := by
  unfold theorem4AverageUtility
  rw [reverseItem_reverseItem]
  ring

/-- A pair attaining the cold-start estimated row maximum. -/
noncomputable def theorem4BestAverageItem {n : ℕ} [NeZero n]
    (v : Item n → ℝ) : Item n :=
  Classical.choose
    (AppliedModelingLib.exists_finiteMax_eq (theorem4AverageUtility v))

theorem theorem4BestAverageItem_spec {n : ℕ} [NeZero n]
    (v : Item n → ℝ) :
    AppliedModelingLib.finiteMax (theorem4AverageUtility v) =
      theorem4AverageUtility v (theorem4BestAverageItem v) := by
  exact Classical.choose_spec
    (AppliedModelingLib.exists_finiteMax_eq (theorem4AverageUtility v))

/--
For a cold-start user whose true row is the first opposing type, orient an
estimated-best mirror pair toward the larger true utility.
-/
noncomputable def theorem4BestAverageItemTypeZero {n : ℕ} [NeZero n]
    (v : Item n → ℝ) : Item n :=
  let j := theorem4BestAverageItem v
  if v j < v (reverseItem j) then reverseItem j else j

/-- The mirror-oriented estimated-best item for the second true cold-start row. -/
noncomputable def theorem4BestAverageItemTypeOne {n : ℕ} [NeZero n]
    (v : Item n → ℝ) : Item n :=
  reverseItem (theorem4BestAverageItemTypeZero v)

theorem theorem4AverageUtility_bestAverageItemTypeZero
    {n : ℕ} [NeZero n] (v : Item n → ℝ) :
    theorem4AverageUtility v (theorem4BestAverageItemTypeZero v) =
      AppliedModelingLib.finiteMax (theorem4AverageUtility v) := by
  unfold theorem4BestAverageItemTypeZero
  by_cases h :
      v (theorem4BestAverageItem v) <
        v (reverseItem (theorem4BestAverageItem v))
  · simp [h, theorem4BestAverageItem_spec]
  · simp [h, theorem4BestAverageItem_spec]

theorem theorem4AverageUtility_le_value_bestAverageItemTypeZero
    {n : ℕ} [NeZero n] (v : Item n → ℝ) :
    theorem4AverageUtility v (theorem4BestAverageItemTypeZero v) ≤
      v (theorem4BestAverageItemTypeZero v) := by
  unfold theorem4BestAverageItemTypeZero
  by_cases h :
      v (theorem4BestAverageItem v) <
        v (reverseItem (theorem4BestAverageItem v))
  · simp [h, theorem4AverageUtility, reverseItem_reverseItem]
    linarith
  · have hle :
        v (reverseItem (theorem4BestAverageItem v)) ≤
          v (theorem4BestAverageItem v) := le_of_not_gt h
    simp [h, theorem4AverageUtility]
    linarith

theorem theorem4AverageUtility_bestAverageItemTypeOne
    {n : ℕ} [NeZero n] (v : Item n → ℝ) :
    theorem4AverageUtility v (theorem4BestAverageItemTypeOne v) =
      AppliedModelingLib.finiteMax (theorem4AverageUtility v) := by
  simp [theorem4BestAverageItemTypeOne,
    theorem4AverageUtility_bestAverageItemTypeZero]

theorem theorem4AverageUtility_le_reverse_value_bestAverageItemTypeOne
    {n : ℕ} [NeZero n] (v : Item n → ℝ) :
    theorem4AverageUtility v (theorem4BestAverageItemTypeOne v) ≤
      v (reverseItem (theorem4BestAverageItemTypeOne v)) := by
  simpa [theorem4BestAverageItemTypeOne, reverseItem_reverseItem] using
    theorem4AverageUtility_le_value_bestAverageItemTypeZero v

theorem theorem4AverageUtility_finiteMax_pos
    {n : ℕ} [NeZero n] {v : Item n → ℝ}
    (hpos : ∀ j, 0 < v j) :
    0 < AppliedModelingLib.finiteMax (theorem4AverageUtility v) := by
  have hfirst :
      0 < theorem4AverageUtility v theorem4FirstItem := by
    unfold theorem4AverageUtility
    nlinarith [hpos theorem4FirstItem,
      hpos (reverseItem theorem4FirstItem)]
  exact lt_of_lt_of_le hfirst
    (AppliedModelingLib.le_finiteMax (theorem4AverageUtility v) theorem4FirstItem)

theorem theorem4AverageUtility_endpoint_half_lt_finiteMax
    {n : ℕ} [NeZero n] {v : Item n → ℝ}
    (hfirst_pos : 0 < v theorem4FirstItem)
    (hlast_pos : 0 < v theorem4LastItem) :
    v theorem4FirstItem / 2 <
      AppliedModelingLib.finiteMax (theorem4AverageUtility v) := by
  have havg :
      v theorem4FirstItem / 2 <
        theorem4AverageUtility v theorem4FirstItem := by
    have hrev_pos : 0 < v (reverseItem theorem4FirstItem) := by
      simpa [theorem4LastItem] using hlast_pos
    unfold theorem4AverageUtility
    nlinarith
  exact lt_of_lt_of_le havg
    (AppliedModelingLib.le_finiteMax (theorem4AverageUtility v) theorem4FirstItem)

theorem theorem4EstimatedReducedModel_bestItemUtility_zero
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hdec : StrictlyDecreasingByIndex v) :
    TypeWeightedRecommendationModel.bestItemUtility
        (theorem4EstimatedReducedModel beta v) 0 =
      v theorem4FirstItem := by
  change AppliedModelingLib.finiteMax (fun j : Item n => v j) =
    v theorem4FirstItem
  exact theorem4_finiteMax_eq_first hdec

theorem theorem4EstimatedReducedModel_bestItemUtility_one
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hdec : StrictlyDecreasingByIndex v) :
    TypeWeightedRecommendationModel.bestItemUtility
        (theorem4EstimatedReducedModel beta v) 1 =
      v theorem4FirstItem := by
  change AppliedModelingLib.finiteMax (fun j : Item n => v (reverseItem j)) =
    v theorem4FirstItem
  rw [finiteMax_reverseItem]
  exact theorem4_finiteMax_eq_first hdec

theorem theorem4EstimatedReducedModel_bestItemUtility_two
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ} :
    TypeWeightedRecommendationModel.bestItemUtility
        (theorem4EstimatedReducedModel beta v) 2 =
      AppliedModelingLib.finiteMax (theorem4AverageUtility v) := by
  change AppliedModelingLib.finiteMax
      (fun j : Item n => (v j + v (reverseItem j)) / 2) =
    AppliedModelingLib.finiteMax (theorem4AverageUtility v)
  rfl

noncomputable def theorem4NoFairnessChoiceTypeZero {n : ℕ} [NeZero n]
    (v : Item n → ℝ) : UserType 3 → Item n :=
  fun k =>
    if k = (0 : UserType 3) then theorem4FirstItem
    else if k = (1 : UserType 3) then theorem4LastItem
    else theorem4BestAverageItemTypeZero v

noncomputable def theorem4NoFairnessChoiceTypeOne {n : ℕ} [NeZero n]
    (v : Item n → ℝ) : UserType 3 → Item n :=
  fun k =>
    if k = (0 : UserType 3) then theorem4FirstItem
    else if k = (1 : UserType 3) then theorem4LastItem
    else theorem4BestAverageItemTypeOne v

/--
The no-item-fairness policy from Theorem 4, oriented for a cold-start user whose
true row is the first opposing type.
-/
noncomputable def theorem4NoFairnessPolicyTypeZero {n : ℕ} [NeZero n]
    (v : Item n → ℝ) : TypePolicy 3 n :=
  AppliedModelingLib.Policy.pure (theorem4NoFairnessChoiceTypeZero v)

/--
The no-item-fairness policy from Theorem 4, oriented for a cold-start user whose
true row is the second opposing type.
-/
noncomputable def theorem4NoFairnessPolicyTypeOne {n : ℕ} [NeZero n]
    (v : Item n → ℝ) : TypePolicy 3 n :=
  AppliedModelingLib.Policy.pure (theorem4NoFairnessChoiceTypeOne v)

/--
The source-faithful no-item-fairness cold-start row: split evenly across the
estimated-best mirror pair.  This tie-break keeps the row estimated-optimal
while giving either possible true cold-start type the pair average.
-/
noncomputable def theorem4NoFairnessColdStartMixedPolicy {n : ℕ} [NeZero n]
    (v : Item n → ℝ) : PMF (Item n) :=
  AppliedModelingLib.Policy.averageOn
    (fun b : Bool =>
      PMF.pure
        (if b then theorem4BestAverageItemTypeZero v
         else theorem4BestAverageItemTypeOne v))
    (Finset.univ : Finset Bool)
    (by simp)

/--
The no-item-fairness policy for the paper's actual two-type true population
and three-type estimated population.  The known estimated rows choose their
best endpoints, and the collapsed cold-start row mixes over an estimated-best
mirror pair.
-/
noncomputable def theorem4NoFairnessPolicyCollapsed {n : ℕ} [NeZero n]
    (v : Item n → ℝ) : TypePolicy 3 n :=
  fun k =>
    if k = (0 : UserType 3) then PMF.pure theorem4FirstItem
    else if k = (1 : UserType 3) then PMF.pure theorem4LastItem
    else theorem4NoFairnessColdStartMixedPolicy v

theorem theorem4NoFairnessColdStartMixedPolicy_agentScore
    {n : ℕ} [NeZero n] (v : Item n → ℝ) (score : Item n → ℝ) :
    AppliedModelingLib.pmfExp (theorem4NoFairnessColdStartMixedPolicy v) score =
      (score (theorem4BestAverageItemTypeZero v) +
        score (theorem4BestAverageItemTypeOne v)) / 2 := by
  classical
  have hsum_pure :
      ∀ a : Item n, ∀ c : ℝ,
        (∑ x : Item n,
            ((if x = a then (1 : ENNReal) else 0).toReal) * score x * c) =
          score a * c := by
    intro a c
    calc
      (∑ x : Item n,
          ((if x = a then (1 : ENNReal) else 0).toReal) * score x * c)
          = ∑ x : Item n, if x = a then score a * c else 0 := by
              refine Finset.sum_congr rfl ?_
              intro x _
              by_cases hx : x = a
              · subst x
                simp
              · simp [hx]
      _ = score a * c := by
            simp
  unfold theorem4NoFairnessColdStartMixedPolicy AppliedModelingLib.pmfExp
  simp [AppliedModelingLib.Policy.averageOn_apply_toReal]
  calc
    (∑ x : Item n,
        ((if x = theorem4BestAverageItemTypeZero v then (1 : ENNReal) else 0).toReal +
              (if x = theorem4BestAverageItemTypeOne v then (1 : ENNReal) else 0).toReal) /
            2 * score x)
        =
          ∑ x : Item n,
            ((if x = theorem4BestAverageItemTypeZero v then (1 : ENNReal) else 0).toReal *
                score x * (1 / 2 : ℝ) +
              (if x = theorem4BestAverageItemTypeOne v then (1 : ENNReal) else 0).toReal *
                score x * (1 / 2 : ℝ)) := by
            refine Finset.sum_congr rfl ?_
            intro x _
            ring
    _ = score (theorem4BestAverageItemTypeZero v) * (1 / 2 : ℝ) +
          score (theorem4BestAverageItemTypeOne v) * (1 / 2 : ℝ) := by
            rw [Finset.sum_add_distrib,
              hsum_pure (theorem4BestAverageItemTypeZero v) (1 / 2 : ℝ),
              hsum_pure (theorem4BestAverageItemTypeOne v) (1 / 2 : ℝ)]
    _ = (score (theorem4BestAverageItemTypeZero v) +
          score (theorem4BestAverageItemTypeOne v)) / 2 := by
            ring

theorem theorem4EstimatedReducedModel_nonnegativeWeights
    {n : ℕ} {beta : ℝ} {v : Item n → ℝ}
    (hbeta : 0 ≤ beta) (hcold : 0 ≤ 1 - 2 * beta) :
    (theorem4EstimatedReducedModel beta v).NonnegativeWeights := by
  intro k
  fin_cases k <;> simp [theorem4EstimatedReducedModel, hbeta, hcold]

theorem theorem4EstimatedReducedModel_nonnegativeUtilities
    {n : ℕ} {beta : ℝ} {v : Item n → ℝ}
    (hpos : ∀ j, 0 < v j) :
    (theorem4EstimatedReducedModel beta v).NonnegativeUtilities := by
  intro k j
  fin_cases k
  · simp [theorem4EstimatedReducedModel, (hpos j).le]
  · simp [theorem4EstimatedReducedModel, (hpos (reverseItem j)).le]
  · simp [theorem4EstimatedReducedModel]
    nlinarith [hpos j, hpos (reverseItem j)]

theorem theorem4EstimatedReducedModel_rowHasPositiveItem
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hpos : ∀ j, 0 < v j) :
    (theorem4EstimatedReducedModel beta v).RowHasPositiveItem := by
  intro k
  refine ⟨theorem4FirstItem, ?_⟩
  fin_cases k
  · simp [theorem4EstimatedReducedModel, hpos theorem4FirstItem]
  · simp [theorem4EstimatedReducedModel, hpos (reverseItem theorem4FirstItem)]
  · simp [theorem4EstimatedReducedModel]
    nlinarith [hpos theorem4FirstItem,
      hpos (reverseItem theorem4FirstItem)]

/-! ### Appendix E, Lemma 12: mirror symmetrization -/

/-- Appendix E's averaged first known-type row. -/
noncomputable def theorem4SymmetricX {n : ℕ}
    (ρ : TypePolicy 3 n) (j : Item n) : ℝ :=
  ((ρ 0 j).toReal + (ρ 1 (reverseItem j)).toReal) / 2

/-- Appendix E's averaged second known-type row. -/
noncomputable def theorem4SymmetricY {n : ℕ}
    (ρ : TypePolicy 3 n) (j : Item n) : ℝ :=
  ((ρ 1 j).toReal + (ρ 0 (reverseItem j)).toReal) / 2

/-- Appendix E's averaged cold-start row. -/
noncomputable def theorem4SymmetricZ {n : ℕ}
    (ρ : TypePolicy 3 n) (j : Item n) : ℝ :=
  ((ρ 2 j).toReal + (ρ 2 (reverseItem j)).toReal) / 2

theorem theorem4SymmetricX_nonneg {n : ℕ}
    (ρ : TypePolicy 3 n) (j : Item n) :
    0 ≤ theorem4SymmetricX ρ j := by
  unfold theorem4SymmetricX
  have h0 : 0 ≤ (ρ 0 j).toReal := ENNReal.toReal_nonneg
  have h1 : 0 ≤ (ρ 1 (reverseItem j)).toReal := ENNReal.toReal_nonneg
  nlinarith

theorem theorem4SymmetricY_nonneg {n : ℕ}
    (ρ : TypePolicy 3 n) (j : Item n) :
    0 ≤ theorem4SymmetricY ρ j := by
  unfold theorem4SymmetricY
  have h0 : 0 ≤ (ρ 1 j).toReal := ENNReal.toReal_nonneg
  have h1 : 0 ≤ (ρ 0 (reverseItem j)).toReal := ENNReal.toReal_nonneg
  nlinarith

theorem theorem4SymmetricZ_nonneg {n : ℕ}
    (ρ : TypePolicy 3 n) (j : Item n) :
    0 ≤ theorem4SymmetricZ ρ j := by
  unfold theorem4SymmetricZ
  have h0 : 0 ≤ (ρ 2 j).toReal := ENNReal.toReal_nonneg
  have h1 : 0 ≤ (ρ 2 (reverseItem j)).toReal := ENNReal.toReal_nonneg
  nlinarith

theorem theorem4SymmetricX_sum_eq_one {n : ℕ}
    (ρ : TypePolicy 3 n) :
    (∑ j : Item n, theorem4SymmetricX ρ j) = 1 := by
  unfold theorem4SymmetricX
  calc
    (∑ j : Item n,
        ((ρ 0 j).toReal + (ρ 1 (reverseItem j)).toReal) / 2)
        =
        ((∑ j : Item n, (ρ 0 j).toReal) +
          (∑ j : Item n, (ρ 1 (reverseItem j)).toReal)) / 2 := by
          rw [← Finset.sum_add_distrib, Finset.sum_div]
    _ = ((∑ j : Item n, (ρ 0 j).toReal) +
          (∑ j : Item n, (ρ 1 j).toReal)) / 2 := by
          have hrev :
              (∑ j : Item n, (ρ 1 (reverseItem j)).toReal) =
                ∑ j : Item n, (ρ 1 j).toReal :=
            sum_reverseItem (fun j : Item n => (ρ 1 j).toReal)
          rw [hrev]
    _ = 1 := by
          rw [AppliedModelingLib.pmfToRealSum (ρ 0),
            AppliedModelingLib.pmfToRealSum (ρ 1)]
          norm_num

theorem theorem4SymmetricY_sum_eq_one {n : ℕ}
    (ρ : TypePolicy 3 n) :
    (∑ j : Item n, theorem4SymmetricY ρ j) = 1 := by
  unfold theorem4SymmetricY
  calc
    (∑ j : Item n,
        ((ρ 1 j).toReal + (ρ 0 (reverseItem j)).toReal) / 2)
        =
        ((∑ j : Item n, (ρ 1 j).toReal) +
          (∑ j : Item n, (ρ 0 (reverseItem j)).toReal)) / 2 := by
          rw [← Finset.sum_add_distrib, Finset.sum_div]
    _ = ((∑ j : Item n, (ρ 1 j).toReal) +
          (∑ j : Item n, (ρ 0 j).toReal)) / 2 := by
          have hrev :
              (∑ j : Item n, (ρ 0 (reverseItem j)).toReal) =
                ∑ j : Item n, (ρ 0 j).toReal :=
            sum_reverseItem (fun j : Item n => (ρ 0 j).toReal)
          rw [hrev]
    _ = 1 := by
          rw [AppliedModelingLib.pmfToRealSum (ρ 0),
            AppliedModelingLib.pmfToRealSum (ρ 1)]
          norm_num

theorem theorem4SymmetricZ_sum_eq_one {n : ℕ}
    (ρ : TypePolicy 3 n) :
    (∑ j : Item n, theorem4SymmetricZ ρ j) = 1 := by
  unfold theorem4SymmetricZ
  calc
    (∑ j : Item n,
        ((ρ 2 j).toReal + (ρ 2 (reverseItem j)).toReal) / 2)
        =
        ((∑ j : Item n, (ρ 2 j).toReal) +
          (∑ j : Item n, (ρ 2 (reverseItem j)).toReal)) / 2 := by
          rw [← Finset.sum_add_distrib, Finset.sum_div]
    _ = ((∑ j : Item n, (ρ 2 j).toReal) +
          (∑ j : Item n, (ρ 2 j).toReal)) / 2 := by
          have hrev :
              (∑ j : Item n, (ρ 2 (reverseItem j)).toReal) =
                ∑ j : Item n, (ρ 2 j).toReal :=
            sum_reverseItem (fun j : Item n => (ρ 2 j).toReal)
          rw [hrev]
    _ = 1 := by
          rw [AppliedModelingLib.pmfToRealSum (ρ 2)]
          norm_num

/-- Appendix E Lemma 12's mirror-averaged policy. -/
noncomputable def theorem4SymmetrizedPolicy {n : ℕ}
    (ρ : TypePolicy 3 n) : TypePolicy 3 n :=
  fun k =>
    if k = (0 : UserType 3) then
      pmfOfRealVector (theorem4SymmetricX ρ)
        (theorem4SymmetricX_nonneg ρ)
        (theorem4SymmetricX_sum_eq_one ρ)
    else if k = (1 : UserType 3) then
      pmfOfRealVector (theorem4SymmetricY ρ)
        (theorem4SymmetricY_nonneg ρ)
        (theorem4SymmetricY_sum_eq_one ρ)
    else
      pmfOfRealVector (theorem4SymmetricZ ρ)
        (theorem4SymmetricZ_nonneg ρ)
        (theorem4SymmetricZ_sum_eq_one ρ)

@[simp] theorem theorem4SymmetrizedPolicy_zero_toReal {n : ℕ}
    (ρ : TypePolicy 3 n) (j : Item n) :
    ((theorem4SymmetrizedPolicy ρ 0) j).toReal =
      theorem4SymmetricX ρ j := by
  simp [theorem4SymmetrizedPolicy]

@[simp] theorem theorem4SymmetrizedPolicy_one_toReal {n : ℕ}
    (ρ : TypePolicy 3 n) (j : Item n) :
    ((theorem4SymmetrizedPolicy ρ 1) j).toReal =
      theorem4SymmetricY ρ j := by
  simp [theorem4SymmetrizedPolicy]

@[simp] theorem theorem4SymmetrizedPolicy_two_toReal {n : ℕ}
    (ρ : TypePolicy 3 n) (j : Item n) :
    ((theorem4SymmetrizedPolicy ρ 2) j).toReal =
      theorem4SymmetricZ ρ j := by
  have h20 : (2 : UserType 3) ≠ 0 := by decide
  have h21 : (2 : UserType 3) ≠ 1 := by decide
  simp [theorem4SymmetrizedPolicy, h20, h21]

/-- The mirror-symmetric subspace `S'` in Appendix E. -/
def Theorem4MirrorSymmetricPolicy {n : ℕ} (ρ : TypePolicy 3 n) : Prop :=
  (∀ j : Item n, ρ 1 (reverseItem j) = ρ 0 j) ∧
    (∀ j : Item n, ρ 2 (reverseItem j) = ρ 2 j)

theorem theorem4SymmetrizedPolicy_mirrorSymmetric {n : ℕ} [NeZero n]
    (ρ : TypePolicy 3 n) :
    Theorem4MirrorSymmetricPolicy (theorem4SymmetrizedPolicy ρ) := by
  constructor
  · intro j
    apply (ENNReal.toReal_eq_toReal_iff'
      ((theorem4SymmetrizedPolicy ρ 1).apply_ne_top (reverseItem j))
      ((theorem4SymmetrizedPolicy ρ 0).apply_ne_top j)).mp
    simp [theorem4SymmetricX, theorem4SymmetricY,
      reverseItem_reverseItem, add_comm]
  · intro j
    apply (ENNReal.toReal_eq_toReal_iff'
      ((theorem4SymmetrizedPolicy ρ 2).apply_ne_top (reverseItem j))
      ((theorem4SymmetrizedPolicy ρ 2).apply_ne_top j)).mp
    simp [theorem4SymmetricZ, reverseItem_reverseItem, add_comm]

theorem theorem4AverageUtility_pos {n : ℕ} {v : Item n → ℝ}
    (hpos : ∀ j : Item n, 0 < v j) (j : Item n) :
    0 < theorem4AverageUtility v j := by
  unfold theorem4AverageUtility
  nlinarith [hpos j, hpos (reverseItem j)]

theorem theorem4EstimatedReducedModel_itemNormalizer_eq_average
    {n : ℕ} (beta : ℝ) (v : Item n → ℝ) (j : Item n) :
    TypeWeightedRecommendationModel.itemNormalizer
        (theorem4EstimatedReducedModel beta v) j =
      theorem4AverageUtility v j := by
  unfold TypeWeightedRecommendationModel.itemNormalizer
    theorem4EstimatedReducedModel theorem4AverageUtility
  have huniv : (Finset.univ : Finset (UserType 3)) = {0, 1, 2} := by
    decide
  rw [huniv]
  simp
  ring

theorem theorem4EstimatedReducedModel_rawItemUtility_symmetrized_eq_average
    {n : ℕ} [NeZero n] (beta : ℝ) (v : Item n → ℝ)
    (ρ : TypePolicy 3 n) (j : Item n) :
    TypeWeightedRecommendationModel.rawItemUtility
        (theorem4EstimatedReducedModel beta v)
        (theorem4SymmetrizedPolicy ρ) j =
      (TypeWeightedRecommendationModel.rawItemUtility
          (theorem4EstimatedReducedModel beta v) ρ j +
        TypeWeightedRecommendationModel.rawItemUtility
          (theorem4EstimatedReducedModel beta v) ρ (reverseItem j)) / 2 := by
  unfold TypeWeightedRecommendationModel.rawItemUtility
    theorem4EstimatedReducedModel
  have huniv : (Finset.univ : Finset (UserType 3)) = {0, 1, 2} := by
    decide
  rw [huniv]
  simp [theorem4SymmetrizedPolicy, theorem4SymmetricX, theorem4SymmetricY,
    theorem4SymmetricZ, reverseItem_reverseItem]
  ring

theorem theorem4EstimatedReducedModel_normalizedItemUtility_symmetrized_eq_average
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hpos : ∀ j : Item n, 0 < v j)
    (ρ : TypePolicy 3 n) (j : Item n) :
    TypeWeightedRecommendationModel.normalizedItemUtility
        (theorem4EstimatedReducedModel beta v)
        (theorem4SymmetrizedPolicy ρ) j =
      (TypeWeightedRecommendationModel.normalizedItemUtility
          (theorem4EstimatedReducedModel beta v) ρ j +
        TypeWeightedRecommendationModel.normalizedItemUtility
          (theorem4EstimatedReducedModel beta v) ρ (reverseItem j)) / 2 := by
  unfold TypeWeightedRecommendationModel.normalizedItemUtility
  rw [theorem4EstimatedReducedModel_itemNormalizer_eq_average,
    theorem4EstimatedReducedModel_itemNormalizer_eq_average,
    theorem4EstimatedReducedModel_rawItemUtility_symmetrized_eq_average]
  have hden_pos : 0 < theorem4AverageUtility v j :=
    theorem4AverageUtility_pos hpos j
  have hden_ne : theorem4AverageUtility v j ≠ 0 := ne_of_gt hden_pos
  have hrev :
      theorem4AverageUtility v (reverseItem j) =
        theorem4AverageUtility v j := by
    simp [theorem4AverageUtility_reverse]
  simp [hden_ne, hrev]
  field_simp [hden_ne]

theorem theorem4EstimatedReducedModel_itemFairness_le_symmetrized
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hpos : ∀ j : Item n, 0 < v j)
    (ρ : TypePolicy 3 n) :
    TypeWeightedRecommendationModel.itemFairness
        (theorem4EstimatedReducedModel beta v) ρ ≤
      TypeWeightedRecommendationModel.itemFairness
        (theorem4EstimatedReducedModel beta v)
        (theorem4SymmetrizedPolicy ρ) := by
  unfold TypeWeightedRecommendationModel.itemFairness
  apply AppliedModelingLib.le_finiteMin
  intro j
  rw [theorem4EstimatedReducedModel_normalizedItemUtility_symmetrized_eq_average
    hpos ρ j]
  have hj :
      AppliedModelingLib.finiteMin
          (TypeWeightedRecommendationModel.normalizedItemUtility
            (theorem4EstimatedReducedModel beta v) ρ) ≤
        TypeWeightedRecommendationModel.normalizedItemUtility
          (theorem4EstimatedReducedModel beta v) ρ j :=
    AppliedModelingLib.finiteMin_le
      (TypeWeightedRecommendationModel.normalizedItemUtility
        (theorem4EstimatedReducedModel beta v) ρ) j
  have hrev :
      AppliedModelingLib.finiteMin
          (TypeWeightedRecommendationModel.normalizedItemUtility
            (theorem4EstimatedReducedModel beta v) ρ) ≤
        TypeWeightedRecommendationModel.normalizedItemUtility
          (theorem4EstimatedReducedModel beta v) ρ (reverseItem j) :=
    AppliedModelingLib.finiteMin_le
      (TypeWeightedRecommendationModel.normalizedItemUtility
        (theorem4EstimatedReducedModel beta v) ρ) (reverseItem j)
  nlinarith

theorem theorem4EstimatedReducedModel_feasibleAtLevel_symmetrized
    {n : ℕ} [NeZero n] {beta gamma : ℝ} {v : Item n → ℝ}
    (hpos : ∀ j : Item n, 0 < v j)
    {ρ : TypePolicy 3 n}
    (hfeas :
      TypeWeightedRecommendationModel.feasibleAtLevel
        (theorem4EstimatedReducedModel beta v) gamma ρ) :
    TypeWeightedRecommendationModel.feasibleAtLevel
        (theorem4EstimatedReducedModel beta v) gamma
        (theorem4SymmetrizedPolicy ρ) := by
  exact hfeas.trans
    (theorem4EstimatedReducedModel_itemFairness_le_symmetrized hpos ρ)

theorem theorem4EstimatedReducedModel_rawTypeUtility_symmetrized_zero
    {n : ℕ} [NeZero n] (beta : ℝ) (v : Item n → ℝ)
    (ρ : TypePolicy 3 n) :
    TypeWeightedRecommendationModel.rawTypeUtility
        (theorem4EstimatedReducedModel beta v)
        (theorem4SymmetrizedPolicy ρ) 0 =
      (TypeWeightedRecommendationModel.rawTypeUtility
          (theorem4EstimatedReducedModel beta v) ρ 0 +
        TypeWeightedRecommendationModel.rawTypeUtility
          (theorem4EstimatedReducedModel beta v) ρ 1) / 2 := by
  unfold TypeWeightedRecommendationModel.rawTypeUtility
    AppliedModelingLib.Policy.agentScore AppliedModelingLib.pmfExp
  simp [theorem4EstimatedReducedModel, theorem4SymmetrizedPolicy,
    theorem4SymmetricX]
  have hrev :
      (∑ j : Item n, (ρ 1 (reverseItem j)).toReal * v j) =
        ∑ j : Item n, (ρ 1 j).toReal * v (reverseItem j) := by
    calc
      (∑ j : Item n, (ρ 1 (reverseItem j)).toReal * v j)
          =
          ∑ j : Item n,
            (ρ 1 (reverseItem j)).toReal *
              v (reverseItem (reverseItem j)) := by
            simp [reverseItem_reverseItem]
      _ = ∑ j : Item n, (ρ 1 j).toReal * v (reverseItem j) := by
            simpa using
              (sum_reverseItem
                (fun j : Item n => (ρ 1 j).toReal * v (reverseItem j)))
  calc
    (∑ x : Item n,
        (((ρ 0) x).toReal + ((ρ 1) (reverseItem x)).toReal) / 2 *
          v x)
        =
        ∑ x : Item n,
          (((ρ 0) x).toReal * v x +
            ((ρ 1) (reverseItem x)).toReal * v x) / 2 := by
          refine Finset.sum_congr rfl ?_
          intro x _hx
          ring
    _ 
        =
        (∑ x : Item n,
          (((ρ 0) x).toReal * v x +
            ((ρ 1) (reverseItem x)).toReal * v x)) / 2 := by
          rw [Finset.sum_div]
    _ =
        ((∑ x : Item n, ((ρ 0) x).toReal * v x) +
          (∑ x : Item n, ((ρ 1) (reverseItem x)).toReal * v x)) / 2 := by
          rw [Finset.sum_add_distrib]
    _ =
        ((∑ x : Item n, ((ρ 0) x).toReal * v x) +
          (∑ x : Item n, ((ρ 1) x).toReal * v (reverseItem x))) / 2 := by
          rw [hrev]

theorem theorem4EstimatedReducedModel_rawTypeUtility_symmetrized_one
    {n : ℕ} [NeZero n] (beta : ℝ) (v : Item n → ℝ)
    (ρ : TypePolicy 3 n) :
    TypeWeightedRecommendationModel.rawTypeUtility
        (theorem4EstimatedReducedModel beta v)
        (theorem4SymmetrizedPolicy ρ) 1 =
      (TypeWeightedRecommendationModel.rawTypeUtility
          (theorem4EstimatedReducedModel beta v) ρ 0 +
        TypeWeightedRecommendationModel.rawTypeUtility
          (theorem4EstimatedReducedModel beta v) ρ 1) / 2 := by
  unfold TypeWeightedRecommendationModel.rawTypeUtility
    AppliedModelingLib.Policy.agentScore AppliedModelingLib.pmfExp
  simp [theorem4EstimatedReducedModel, theorem4SymmetrizedPolicy,
    theorem4SymmetricY]
  have hrev :
      (∑ j : Item n,
          (ρ 0 (reverseItem j)).toReal * v (reverseItem j)) =
        ∑ j : Item n, (ρ 0 j).toReal * v j := by
    simpa using
      (sum_reverseItem (fun j : Item n => (ρ 0 j).toReal * v j))
  calc
    (∑ x : Item n,
        (((ρ 1) x).toReal + ((ρ 0) (reverseItem x)).toReal) / 2 *
          v (reverseItem x))
        =
        ∑ x : Item n,
          (((ρ 1) x).toReal * v (reverseItem x) +
            ((ρ 0) (reverseItem x)).toReal * v (reverseItem x)) / 2 := by
          refine Finset.sum_congr rfl ?_
          intro x _hx
          ring
    _ =
        (∑ x : Item n,
          (((ρ 1) x).toReal * v (reverseItem x) +
            ((ρ 0) (reverseItem x)).toReal * v (reverseItem x))) / 2 := by
          rw [Finset.sum_div]
    _ =
        ((∑ x : Item n, ((ρ 1) x).toReal * v (reverseItem x)) +
          (∑ x : Item n,
            ((ρ 0) (reverseItem x)).toReal * v (reverseItem x))) / 2 := by
          rw [Finset.sum_add_distrib]
    _ =
        ((∑ x : Item n, ((ρ 0) x).toReal * v x) +
          (∑ x : Item n, ((ρ 1) x).toReal * v (reverseItem x))) / 2 := by
          rw [hrev]
          ring

theorem theorem4EstimatedReducedModel_rawTypeUtility_symmetrized_two
    {n : ℕ} [NeZero n] (beta : ℝ) (v : Item n → ℝ)
    (ρ : TypePolicy 3 n) :
    TypeWeightedRecommendationModel.rawTypeUtility
        (theorem4EstimatedReducedModel beta v)
        (theorem4SymmetrizedPolicy ρ) 2 =
      TypeWeightedRecommendationModel.rawTypeUtility
        (theorem4EstimatedReducedModel beta v) ρ 2 := by
  unfold TypeWeightedRecommendationModel.rawTypeUtility
    AppliedModelingLib.Policy.agentScore AppliedModelingLib.pmfExp
  simp [theorem4EstimatedReducedModel, theorem4SymmetrizedPolicy,
    theorem4SymmetricZ]
  have hrev :
      (∑ j : Item n,
          (ρ 2 (reverseItem j)).toReal *
            ((v j + v (reverseItem j)) / 2)) =
        ∑ j : Item n,
          (ρ 2 j).toReal * ((v j + v (reverseItem j)) / 2) := by
    calc
      (∑ j : Item n,
          (ρ 2 (reverseItem j)).toReal *
            ((v j + v (reverseItem j)) / 2))
          =
          ∑ j : Item n,
            (ρ 2 (reverseItem j)).toReal *
              theorem4AverageUtility v (reverseItem j) := by
            simp [theorem4AverageUtility, reverseItem_reverseItem,
              add_comm]
      _ = ∑ j : Item n,
            (ρ 2 j).toReal * theorem4AverageUtility v j := by
            simpa using
              (sum_reverseItem
                (fun j : Item n =>
                  (ρ 2 j).toReal * theorem4AverageUtility v j))
      _ = ∑ j : Item n,
            (ρ 2 j).toReal * ((v j + v (reverseItem j)) / 2) := by
            simp [theorem4AverageUtility]
  calc
    (∑ x : Item n,
        (((ρ 2) x).toReal + ((ρ 2) (reverseItem x)).toReal) / 2 *
          ((v x + v (reverseItem x)) / 2))
        =
        ∑ x : Item n,
          (((ρ 2) x).toReal * ((v x + v (reverseItem x)) / 2) +
            ((ρ 2) (reverseItem x)).toReal *
              ((v x + v (reverseItem x)) / 2)) / 2 := by
          refine Finset.sum_congr rfl ?_
          intro x _hx
          ring
    _ =
        (∑ x : Item n,
          (((ρ 2) x).toReal * ((v x + v (reverseItem x)) / 2) +
            ((ρ 2) (reverseItem x)).toReal *
              ((v x + v (reverseItem x)) / 2))) / 2 := by
          rw [Finset.sum_div]
    _ =
        ((∑ x : Item n,
            ((ρ 2) x).toReal * ((v x + v (reverseItem x)) / 2)) +
          (∑ x : Item n,
            ((ρ 2) (reverseItem x)).toReal *
              ((v x + v (reverseItem x)) / 2))) / 2 := by
          rw [Finset.sum_add_distrib]
    _ =
        ∑ x : Item n,
          ((ρ 2) x).toReal * ((v x + v (reverseItem x)) / 2) := by
          rw [hrev]
          ring

theorem theorem4EstimatedReducedModel_bestItemUtility_one_eq_zero
    {n : ℕ} [NeZero n] (beta : ℝ) (v : Item n → ℝ) :
    TypeWeightedRecommendationModel.bestItemUtility
        (theorem4EstimatedReducedModel beta v) 1 =
      TypeWeightedRecommendationModel.bestItemUtility
        (theorem4EstimatedReducedModel beta v) 0 := by
  unfold TypeWeightedRecommendationModel.bestItemUtility
  change AppliedModelingLib.finiteMax (fun j : Item n => v (reverseItem j)) =
    AppliedModelingLib.finiteMax v
  exact finiteMax_reverseItem v

theorem theorem4EstimatedReducedModel_normalizedTypeUtility_symmetrized_zero
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hpos : ∀ j : Item n, 0 < v j)
    (ρ : TypePolicy 3 n) :
    TypeWeightedRecommendationModel.normalizedTypeUtility
        (theorem4EstimatedReducedModel beta v)
        (theorem4SymmetrizedPolicy ρ) 0 =
      (TypeWeightedRecommendationModel.normalizedTypeUtility
          (theorem4EstimatedReducedModel beta v) ρ 0 +
        TypeWeightedRecommendationModel.normalizedTypeUtility
          (theorem4EstimatedReducedModel beta v) ρ 1) / 2 := by
  unfold TypeWeightedRecommendationModel.normalizedTypeUtility
  rw [theorem4EstimatedReducedModel_rawTypeUtility_symmetrized_zero]
  rw [theorem4EstimatedReducedModel_bestItemUtility_one_eq_zero]
  have hbest_pos :
      0 < TypeWeightedRecommendationModel.bestItemUtility
          (theorem4EstimatedReducedModel beta v) 0 :=
    TypeWeightedRecommendationModel.bestItemUtility_pos_of_rowHasPositiveItem
      (theorem4EstimatedReducedModel beta v)
      (theorem4EstimatedReducedModel_rowHasPositiveItem hpos) 0
  field_simp [ne_of_gt hbest_pos]

theorem theorem4EstimatedReducedModel_normalizedTypeUtility_symmetrized_one
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hpos : ∀ j : Item n, 0 < v j)
    (ρ : TypePolicy 3 n) :
    TypeWeightedRecommendationModel.normalizedTypeUtility
        (theorem4EstimatedReducedModel beta v)
        (theorem4SymmetrizedPolicy ρ) 1 =
      (TypeWeightedRecommendationModel.normalizedTypeUtility
          (theorem4EstimatedReducedModel beta v) ρ 0 +
        TypeWeightedRecommendationModel.normalizedTypeUtility
          (theorem4EstimatedReducedModel beta v) ρ 1) / 2 := by
  unfold TypeWeightedRecommendationModel.normalizedTypeUtility
  rw [theorem4EstimatedReducedModel_rawTypeUtility_symmetrized_one]
  rw [theorem4EstimatedReducedModel_bestItemUtility_one_eq_zero]
  have hbest_pos :
      0 < TypeWeightedRecommendationModel.bestItemUtility
          (theorem4EstimatedReducedModel beta v) 0 :=
    TypeWeightedRecommendationModel.bestItemUtility_pos_of_rowHasPositiveItem
      (theorem4EstimatedReducedModel beta v)
      (theorem4EstimatedReducedModel_rowHasPositiveItem hpos) 0
  field_simp [ne_of_gt hbest_pos]

theorem theorem4EstimatedReducedModel_normalizedTypeUtility_symmetrized_two
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (ρ : TypePolicy 3 n) :
    TypeWeightedRecommendationModel.normalizedTypeUtility
        (theorem4EstimatedReducedModel beta v)
        (theorem4SymmetrizedPolicy ρ) 2 =
      TypeWeightedRecommendationModel.normalizedTypeUtility
        (theorem4EstimatedReducedModel beta v) ρ 2 := by
  unfold TypeWeightedRecommendationModel.normalizedTypeUtility
  rw [theorem4EstimatedReducedModel_rawTypeUtility_symmetrized_two]

theorem theorem4EstimatedReducedModel_typeFairness_le_symmetrized
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hpos : ∀ j : Item n, 0 < v j)
    (ρ : TypePolicy 3 n) :
    TypeWeightedRecommendationModel.typeFairness
        (theorem4EstimatedReducedModel beta v) ρ ≤
      TypeWeightedRecommendationModel.typeFairness
        (theorem4EstimatedReducedModel beta v)
        (theorem4SymmetrizedPolicy ρ) := by
  unfold TypeWeightedRecommendationModel.typeFairness
  apply AppliedModelingLib.le_finiteMin
  intro k
  fin_cases k
  · change AppliedModelingLib.finiteMin
        (TypeWeightedRecommendationModel.normalizedTypeUtility
          (theorem4EstimatedReducedModel beta v) ρ) ≤
      TypeWeightedRecommendationModel.normalizedTypeUtility
        (theorem4EstimatedReducedModel beta v)
        (theorem4SymmetrizedPolicy ρ) (0 : UserType 3)
    rw [theorem4EstimatedReducedModel_normalizedTypeUtility_symmetrized_zero
      hpos ρ]
    have h0 :=
      AppliedModelingLib.finiteMin_le
        (TypeWeightedRecommendationModel.normalizedTypeUtility
          (theorem4EstimatedReducedModel beta v) ρ) (0 : UserType 3)
    have h1 :=
      AppliedModelingLib.finiteMin_le
        (TypeWeightedRecommendationModel.normalizedTypeUtility
          (theorem4EstimatedReducedModel beta v) ρ) (1 : UserType 3)
    nlinarith
  · change AppliedModelingLib.finiteMin
        (TypeWeightedRecommendationModel.normalizedTypeUtility
          (theorem4EstimatedReducedModel beta v) ρ) ≤
      TypeWeightedRecommendationModel.normalizedTypeUtility
        (theorem4EstimatedReducedModel beta v)
        (theorem4SymmetrizedPolicy ρ) (1 : UserType 3)
    rw [theorem4EstimatedReducedModel_normalizedTypeUtility_symmetrized_one
      hpos ρ]
    have h0 :=
      AppliedModelingLib.finiteMin_le
        (TypeWeightedRecommendationModel.normalizedTypeUtility
          (theorem4EstimatedReducedModel beta v) ρ) (0 : UserType 3)
    have h1 :=
      AppliedModelingLib.finiteMin_le
        (TypeWeightedRecommendationModel.normalizedTypeUtility
          (theorem4EstimatedReducedModel beta v) ρ) (1 : UserType 3)
    nlinarith
  · change AppliedModelingLib.finiteMin
        (TypeWeightedRecommendationModel.normalizedTypeUtility
          (theorem4EstimatedReducedModel beta v) ρ) ≤
      TypeWeightedRecommendationModel.normalizedTypeUtility
        (theorem4EstimatedReducedModel beta v)
        (theorem4SymmetrizedPolicy ρ) (2 : UserType 3)
    rw [theorem4EstimatedReducedModel_normalizedTypeUtility_symmetrized_two]
    exact AppliedModelingLib.finiteMin_le
      (TypeWeightedRecommendationModel.normalizedTypeUtility
        (theorem4EstimatedReducedModel beta v) ρ) (2 : UserType 3)

/--
Appendix E, Lemma 12: any policy solving the estimated maximal-item-fairness
problem can be mirror-symmetrized into the subspace `S'` without losing
estimated optimality.
-/
theorem theorem4_symmetrizedPolicy_isOptimalAtLevel
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hpos : ∀ j : Item n, 0 < v j)
    {ρ : TypePolicy 3 n}
    (hopt :
      TypeWeightedRecommendationModel.IsOptimalAtLevel
        (theorem4EstimatedReducedModel beta v) 1 ρ) :
    TypeWeightedRecommendationModel.IsOptimalAtLevel
        (theorem4EstimatedReducedModel beta v) 1
        (theorem4SymmetrizedPolicy ρ) ∧
      Theorem4MirrorSymmetricPolicy (theorem4SymmetrizedPolicy ρ) := by
  let T := theorem4EstimatedReducedModel beta v
  have hfeas :
      TypeWeightedRecommendationModel.feasibleAtLevel T 1
        (theorem4SymmetrizedPolicy ρ) :=
    theorem4EstimatedReducedModel_feasibleAtLevel_symmetrized hpos hopt.1
  have htype_lower :
      TypeWeightedRecommendationModel.typeFairness T ρ ≤
        TypeWeightedRecommendationModel.typeFairness T
          (theorem4SymmetrizedPolicy ρ) :=
    theorem4EstimatedReducedModel_typeFairness_le_symmetrized hpos ρ
  have htype_upper :
      TypeWeightedRecommendationModel.typeFairness T
          (theorem4SymmetrizedPolicy ρ) ≤
        TypeWeightedRecommendationModel.typeFairness T ρ :=
    TypeWeightedRecommendationModel.typeFairness_le_of_isOptimalAtLevel
      T (theorem4EstimatedReducedModel_rowHasPositiveItem hpos)
      hopt hfeas
  have htype_eq :
      TypeWeightedRecommendationModel.typeFairness T
          (theorem4SymmetrizedPolicy ρ) =
        TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel T 1 := by
    apply le_antisymm
    · exact htype_upper.trans_eq hopt.2
    · rw [← hopt.2]
      exact htype_lower
  exact ⟨⟨hfeas, htype_eq⟩,
    theorem4SymmetrizedPolicy_mirrorSymmetric ρ⟩

/-! ### Appendix E, Problem 11: estimated LP in `S'` coordinates -/

/--
Problem 11's item value in the paper's `x,z,λ` notation after restricting to
the mirror-symmetric subspace `S'`.
-/
noncomputable def theorem4Problem11ItemValue {n : ℕ}
    (beta : ℝ) (v x z : Item n → ℝ) (j : Item n) : ℝ :=
  2 * beta *
      (pairShare (1 / 2) v j * x j +
        (1 - pairShare (1 / 2) v j) * x (reverseItem j)) +
    (1 - 2 * beta) * z j

theorem theorem4Problem11ItemValue_reverse_eq
    {n : ℕ} {beta : ℝ} {v x z : Item n → ℝ}
    (hpos : ∀ j : Item n, 0 < v j)
    (hzmirror : ∀ j : Item n, z (reverseItem j) = z j)
    (j : Item n) :
    theorem4Problem11ItemValue beta v x z (reverseItem j) =
      theorem4Problem11ItemValue beta v x z j := by
  have hq :
      pairShare (1 / 2) v (reverseItem j) =
        1 - pairShare (1 / 2) v j := by
    simpa [reverseItem_reverseItem] using
      pairShare_half_eq_one_sub_reverse (reverseItem j) hpos
  unfold theorem4Problem11ItemValue
  rw [hq, hzmirror j, reverseItem_reverseItem]
  ring

theorem theorem4Problem11ItemValue_lt_of_same_x_strict_z
    {n : ℕ} {beta : ℝ} {v x x' z z' : Item n → ℝ} {j : Item n}
    (hcold_pos : 0 < 1 - 2 * beta)
    (hxj : x' j = x j)
    (hxrevj : x' (reverseItem j) = x (reverseItem j))
    (hzlt : z j < z' j) :
    theorem4Problem11ItemValue beta v x z j <
      theorem4Problem11ItemValue beta v x' z' j := by
  unfold theorem4Problem11ItemValue
  rw [hxj, hxrevj]
  have hzterm :
      (1 - 2 * beta) * z j < (1 - 2 * beta) * z' j :=
    mul_lt_mul_of_pos_left hzlt hcold_pos
  linarith only [hzterm]

/-- Problem 11's item value for a type policy in `S'`. -/
noncomputable def theorem4Problem11PolicyItemValue {n : ℕ}
    (beta : ℝ) (v : Item n → ℝ) (ρ : TypePolicy 3 n)
    (j : Item n) : ℝ :=
  theorem4Problem11ItemValue beta v
    (fun l : Item n => (ρ 0 l).toReal)
    (fun l : Item n => (ρ 2 l).toReal) j

/--
Problem 11 translation: on the mirror-symmetric subspace `S'`, the estimated
normalized item utility is exactly the paper's linear expression in `x` and
`z`.
-/
theorem theorem4EstimatedReducedModel_normalizedItemUtility_eq_problem11
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hpos : ∀ j : Item n, 0 < v j)
    {ρ : TypePolicy 3 n}
    (hsym : Theorem4MirrorSymmetricPolicy ρ)
    (j : Item n) :
    TypeWeightedRecommendationModel.normalizedItemUtility
        (theorem4EstimatedReducedModel beta v) ρ j =
      theorem4Problem11PolicyItemValue beta v ρ j := by
  have hy :
      (ρ 1 j).toReal = (ρ 0 (reverseItem j)).toReal := by
    have h := hsym.1 (reverseItem j)
    simpa [reverseItem_reverseItem] using congrArg ENNReal.toReal h
  unfold TypeWeightedRecommendationModel.normalizedItemUtility
  rw [theorem4EstimatedReducedModel_itemNormalizer_eq_average]
  have hden_avg : theorem4AverageUtility v j ≠ 0 :=
    ne_of_gt (theorem4AverageUtility_pos hpos j)
  simp [hden_avg]
  unfold TypeWeightedRecommendationModel.rawItemUtility
    theorem4EstimatedReducedModel theorem4Problem11PolicyItemValue
    theorem4Problem11ItemValue theorem4AverageUtility pairShare
  have huniv : (Finset.univ : Finset (UserType 3)) = {0, 1, 2} := by
    decide
  rw [huniv]
  simp [hy]
  have hsum_pos : 0 < v j + v (reverseItem j) := by
    nlinarith [hpos j, hpos (reverseItem j)]
  have hsum_ne : v j + v (reverseItem j) ≠ 0 := ne_of_gt hsum_pos
  have hpair_denom_ne :
      (2 : ℝ)⁻¹ * v j + (1 - (2 : ℝ)⁻¹) *
          v (reverseItem j) ≠ 0 := by
    nlinarith
  have hcomp :
      1 - typeOneShare (2 : ℝ)⁻¹ (v j) (v (reverseItem j)) =
        (1 - (2 : ℝ)⁻¹) * v (reverseItem j) /
          ((2 : ℝ)⁻¹ * v j + (1 - (2 : ℝ)⁻¹) *
            v (reverseItem j)) :=
    one_sub_typeOneShare_eq hpair_denom_ne
  rw [hcomp]
  unfold typeOneShare
  norm_num
  field_simp [hsum_ne]
  ring

/-- Problem 11 epigraph feasibility in the paper's `x,z,λ` notation. -/
def theorem4Problem11LPFeasible {n : ℕ}
    (beta : ℝ) (v : Item n → ℝ) (ρ : TypePolicy 3 n) (ell : ℝ) : Prop :=
  ∀ j : Item n, ell ≤ theorem4Problem11PolicyItemValue beta v ρ j

/--
For a mirror-symmetric policy, Problem 11 epigraph feasibility is equivalent to
being below the reduced estimated item-fairness value.
-/
theorem theorem4Problem11LPFeasible_iff_le_itemFairness
    {n : ℕ} [NeZero n] {beta ell : ℝ} {v : Item n → ℝ}
    (hpos : ∀ j : Item n, 0 < v j)
    {ρ : TypePolicy 3 n}
    (hsym : Theorem4MirrorSymmetricPolicy ρ) :
    theorem4Problem11LPFeasible beta v ρ ell ↔
      ell ≤
        TypeWeightedRecommendationModel.itemFairness
          (theorem4EstimatedReducedModel beta v) ρ := by
  constructor
  · intro h
    unfold TypeWeightedRecommendationModel.itemFairness
    apply AppliedModelingLib.le_finiteMin
    intro j
    rw [theorem4EstimatedReducedModel_normalizedItemUtility_eq_problem11
      hpos hsym j]
    exact h j
  · intro h j
    rw [← theorem4EstimatedReducedModel_normalizedItemUtility_eq_problem11
      hpos hsym j]
    exact h.trans
      (AppliedModelingLib.finiteMin_le
        (TypeWeightedRecommendationModel.normalizedItemUtility
          (theorem4EstimatedReducedModel beta v) ρ) j)

/-- A policy/value pair is optimal for the Problem 11 epigraph LP. -/
def Theorem4Problem11PolicyOptimal {n : ℕ} [NeZero n]
    (beta : ℝ) (v : Item n → ℝ) (ρ : TypePolicy 3 n) (ell : ℝ) : Prop :=
  Theorem4MirrorSymmetricPolicy ρ ∧
    theorem4Problem11LPFeasible beta v ρ ell ∧
      ∀ (ρ' : TypePolicy 3 n) (ell' : ℝ),
        Theorem4MirrorSymmetricPolicy ρ' →
          theorem4Problem11LPFeasible beta v ρ' ell' → ell' ≤ ell

/--
Literal Problem 11 equality-program optimality.  Unlike the epigraph
predicate above, every comparison policy must equalize all item expressions.
This is the premise written in Appendix E before Lemma 13.
-/
def Theorem4Problem11EqualityLPOptimal {n : ℕ}
    (beta : ℝ) (v : Item n → ℝ) (ρ : TypePolicy 3 n) (ell : ℝ) : Prop :=
  Theorem4MirrorSymmetricPolicy ρ ∧
    (∀ j : Item n, theorem4Problem11PolicyItemValue beta v ρ j = ell) ∧
      ∀ (ρ' : TypePolicy 3 n) (ell' : ℝ),
        Theorem4MirrorSymmetricPolicy ρ' →
          (∀ j : Item n,
            theorem4Problem11PolicyItemValue beta v ρ' j = ell') →
          ell' ≤ ell

/--
An estimated `γ = 1` optimum in the mirror-symmetric subspace solves the
Problem 11 epigraph LP with objective value equal to its item-fairness value.
-/
theorem theorem4Problem11PolicyOptimal_of_isOptimalAtLevel
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hbeta : 0 ≤ beta) (hcold : 0 ≤ 1 - 2 * beta)
    (hpos : ∀ j : Item n, 0 < v j)
    {ρ : TypePolicy 3 n}
    (hsym : Theorem4MirrorSymmetricPolicy ρ)
    (hopt :
      TypeWeightedRecommendationModel.IsOptimalAtLevel
        (theorem4EstimatedReducedModel beta v) 1 ρ) :
    Theorem4Problem11PolicyOptimal beta v ρ
      (TypeWeightedRecommendationModel.itemFairness
        (theorem4EstimatedReducedModel beta v) ρ) := by
  let T := theorem4EstimatedReducedModel beta v
  refine ⟨hsym, ?_, ?_⟩
  · exact (theorem4Problem11LPFeasible_iff_le_itemFairness
      hpos hsym).mpr le_rfl
  · intro ρ' ell' hsym' hfeas'
    have hell_le_item :
        ell' ≤ TypeWeightedRecommendationModel.itemFairness T ρ' :=
      (theorem4Problem11LPFeasible_iff_le_itemFairness
        hpos hsym').mp hfeas'
    have hbdd :
        BddAbove (TypeWeightedRecommendationModel.attainableItemFairnessSet T) :=
      TypeWeightedRecommendationModel.attainableItemFairnessSet_bddAbove_of_nonnegative
        T
        (theorem4EstimatedReducedModel_nonnegativeWeights hbeta hcold)
        (theorem4EstimatedReducedModel_nonnegativeUtilities hpos)
    have hmem :
        TypeWeightedRecommendationModel.itemFairness T ρ' ∈
          TypeWeightedRecommendationModel.attainableItemFairnessSet T := by
      exact ⟨ρ', rfl⟩
    have hitem_le_opt :
        TypeWeightedRecommendationModel.itemFairness T ρ' ≤
          TypeWeightedRecommendationModel.optimalItemFairness T :=
      le_csSup hbdd hmem
    have hopt_le_item :
        TypeWeightedRecommendationModel.optimalItemFairness T ≤
          TypeWeightedRecommendationModel.itemFairness T ρ := by
      simpa [TypeWeightedRecommendationModel.feasibleAtLevel] using hopt.1
    exact hell_le_item.trans (hitem_le_opt.trans hopt_le_item)

/--
Problem 11 optimality bridge: an epigraph-optimal mirror-symmetric policy has
objective value exactly equal to its reduced estimated item-fairness.
-/
theorem theorem4Problem11PolicyOptimal_itemFairness_eq
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hpos : ∀ j : Item n, 0 < v j)
    {ρ : TypePolicy 3 n} {ell : ℝ}
    (hopt : Theorem4Problem11PolicyOptimal beta v ρ ell) :
    TypeWeightedRecommendationModel.itemFairness
        (theorem4EstimatedReducedModel beta v) ρ = ell := by
  let T := theorem4EstimatedReducedModel beta v
  have hell_le_item :
      ell ≤ TypeWeightedRecommendationModel.itemFairness T ρ :=
    (theorem4Problem11LPFeasible_iff_le_itemFairness
      hpos hopt.1).mp hopt.2.1
  have hfeas_item :
      theorem4Problem11LPFeasible beta v ρ
        (TypeWeightedRecommendationModel.itemFairness T ρ) :=
    (theorem4Problem11LPFeasible_iff_le_itemFairness
      hpos hopt.1).mpr le_rfl
  have hitem_le_ell :
      TypeWeightedRecommendationModel.itemFairness T ρ ≤ ell :=
    hopt.2.2 ρ (TypeWeightedRecommendationModel.itemFairness T ρ)
      hopt.1 hfeas_item
  exact le_antisymm hitem_le_ell hell_le_item

/--
Problem 11 / Problem 1 bridge: every Problem 11 epigraph optimum is feasible
for the reduced estimated model at maximal item-fairness level `γ = 1`.

The proof uses Lemma 12's symmetrization dominance: arbitrary policies cannot
attain larger item fairness than their mirror-symmetrizations, and Problem 11
is optimal over that mirror-symmetric subspace.
-/
theorem theorem4Problem11PolicyOptimal_feasibleAtLevel_one
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hbeta : 0 ≤ beta) (hcold : 0 ≤ 1 - 2 * beta)
    (hpos : ∀ j : Item n, 0 < v j)
    {ρ : TypePolicy 3 n} {ell : ℝ}
    (hopt : Theorem4Problem11PolicyOptimal beta v ρ ell) :
    TypeWeightedRecommendationModel.feasibleAtLevel
      (theorem4EstimatedReducedModel beta v) 1 ρ := by
  let T := theorem4EstimatedReducedModel beta v
  have hitem_eq :
      TypeWeightedRecommendationModel.itemFairness T ρ = ell :=
    theorem4Problem11PolicyOptimal_itemFairness_eq hpos hopt
  have hItemNonempty :
      (TypeWeightedRecommendationModel.attainableItemFairnessSet T).Nonempty := by
    refine ⟨TypeWeightedRecommendationModel.itemFairness T
      (TypeWeightedRecommendationModel.uniformTypePolicy (K := 3) (n := n)), ?_⟩
    exact ⟨TypeWeightedRecommendationModel.uniformTypePolicy (K := 3) (n := n), rfl⟩
  have hoptItem_le_ell :
      TypeWeightedRecommendationModel.optimalItemFairness T ≤ ell := by
    unfold TypeWeightedRecommendationModel.optimalItemFairness
    refine csSup_le hItemNonempty ?_
    intro r hr
    obtain ⟨ρ', rfl⟩ := hr
    let ρsym : TypePolicy 3 n := theorem4SymmetrizedPolicy ρ'
    have hsym : Theorem4MirrorSymmetricPolicy ρsym := by
      dsimp [ρsym]
      exact theorem4SymmetrizedPolicy_mirrorSymmetric ρ'
    have hfeas_sym :
        theorem4Problem11LPFeasible beta v ρsym
          (TypeWeightedRecommendationModel.itemFairness T ρsym) :=
      (theorem4Problem11LPFeasible_iff_le_itemFairness
        hpos hsym).mpr le_rfl
    have hsym_le_ell :
        TypeWeightedRecommendationModel.itemFairness T ρsym ≤ ell :=
      hopt.2.2 ρsym (TypeWeightedRecommendationModel.itemFairness T ρsym)
        hsym hfeas_sym
    have hle_sym :
        TypeWeightedRecommendationModel.itemFairness T ρ' ≤
          TypeWeightedRecommendationModel.itemFairness T ρsym := by
      dsimp [T, ρsym]
      exact theorem4EstimatedReducedModel_itemFairness_le_symmetrized hpos ρ'
    exact hle_sym.trans hsym_le_ell
  have hoptItem_le_item :
      TypeWeightedRecommendationModel.optimalItemFairness T ≤
        TypeWeightedRecommendationModel.itemFairness T ρ := by
    rw [hitem_eq]
    exact hoptItem_le_ell
  simpa [TypeWeightedRecommendationModel.feasibleAtLevel] using hoptItem_le_item

/--
Problem 11 / Problem 1 bridge in the other direction: a mirror-symmetric policy
that is feasible at maximal estimated item fairness solves the Problem 11
epigraph LP with objective equal to its item-fairness value.
-/
theorem theorem4Problem11PolicyOptimal_of_feasibleAtLevel_one
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hbeta : 0 ≤ beta) (hcold : 0 ≤ 1 - 2 * beta)
    (hpos : ∀ j : Item n, 0 < v j)
    {ρ : TypePolicy 3 n}
    (hsym : Theorem4MirrorSymmetricPolicy ρ)
    (hfeas :
      TypeWeightedRecommendationModel.feasibleAtLevel
        (theorem4EstimatedReducedModel beta v) 1 ρ) :
    Theorem4Problem11PolicyOptimal beta v ρ
      (TypeWeightedRecommendationModel.itemFairness
        (theorem4EstimatedReducedModel beta v) ρ) := by
  let T := theorem4EstimatedReducedModel beta v
  refine ⟨hsym, ?_, ?_⟩
  · exact (theorem4Problem11LPFeasible_iff_le_itemFairness
      hpos hsym).mpr le_rfl
  · intro ρ' ell' hsym' hfeas'
    have hell'_le_item :
        ell' ≤ TypeWeightedRecommendationModel.itemFairness T ρ' :=
      (theorem4Problem11LPFeasible_iff_le_itemFairness
        hpos hsym').mp hfeas'
    have hbdd :
        BddAbove (TypeWeightedRecommendationModel.attainableItemFairnessSet T) :=
      TypeWeightedRecommendationModel.attainableItemFairnessSet_bddAbove_of_nonnegative
        T
        (theorem4EstimatedReducedModel_nonnegativeWeights hbeta hcold)
        (theorem4EstimatedReducedModel_nonnegativeUtilities hpos)
    have hmem :
        TypeWeightedRecommendationModel.itemFairness T ρ' ∈
          TypeWeightedRecommendationModel.attainableItemFairnessSet T := by
      exact ⟨ρ', rfl⟩
    have hitem_le_opt :
        TypeWeightedRecommendationModel.itemFairness T ρ' ≤
          TypeWeightedRecommendationModel.optimalItemFairness T :=
      le_csSup hbdd hmem
    have hopt_le_item :
        TypeWeightedRecommendationModel.optimalItemFairness T ≤
          TypeWeightedRecommendationModel.itemFairness T ρ := by
      simpa [TypeWeightedRecommendationModel.feasibleAtLevel] using hfeas
    exact hell'_le_item.trans (hitem_le_opt.trans hopt_le_item)

/--
Problem 11 / Lemma 12 bridge: any reduced estimated policy feasible at maximal
item fairness has a mirror-symmetrization that solves the Problem 11 epigraph
LP.
-/
theorem theorem4Problem11PolicyOptimal_symmetrized_of_feasibleAtLevel_one
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hbeta : 0 ≤ beta) (hcold : 0 ≤ 1 - 2 * beta)
    (hpos : ∀ j : Item n, 0 < v j)
    {ρ : TypePolicy 3 n}
    (hfeas :
      TypeWeightedRecommendationModel.feasibleAtLevel
        (theorem4EstimatedReducedModel beta v) 1 ρ) :
    Theorem4Problem11PolicyOptimal beta v (theorem4SymmetrizedPolicy ρ)
      (TypeWeightedRecommendationModel.itemFairness
        (theorem4EstimatedReducedModel beta v)
        (theorem4SymmetrizedPolicy ρ)) := by
  have hsym :
      Theorem4MirrorSymmetricPolicy (theorem4SymmetrizedPolicy ρ) :=
    theorem4SymmetrizedPolicy_mirrorSymmetric ρ
  have hfeas_sym :
      TypeWeightedRecommendationModel.feasibleAtLevel
        (theorem4EstimatedReducedModel beta v) 1
        (theorem4SymmetrizedPolicy ρ) :=
    theorem4EstimatedReducedModel_feasibleAtLevel_symmetrized hpos hfeas
  exact theorem4Problem11PolicyOptimal_of_feasibleAtLevel_one
    hbeta hcold hpos hsym hfeas_sym

/-- An optimal Problem 11 epigraph value is the minimum item value of its policy. -/
theorem theorem4Problem11PolicyOptimal_value_eq_finiteMin
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    {ρ : TypePolicy 3 n} {ell : ℝ}
    (hopt : Theorem4Problem11PolicyOptimal beta v ρ ell) :
    ell =
      AppliedModelingLib.finiteMin
        (fun j : Item n => theorem4Problem11PolicyItemValue beta v ρ j) := by
  let value : Item n → ℝ :=
    fun j : Item n => theorem4Problem11PolicyItemValue beta v ρ j
  have hell_le_min : ell ≤ AppliedModelingLib.finiteMin value := by
    apply AppliedModelingLib.le_finiteMin
    intro j
    exact hopt.2.1 j
  have hmin_feas :
      theorem4Problem11LPFeasible beta v ρ
        (AppliedModelingLib.finiteMin value) := by
    intro j
    exact AppliedModelingLib.finiteMin_le value j
  have hmin_le_ell :
      AppliedModelingLib.finiteMin value ≤ ell :=
    hopt.2.2 ρ (AppliedModelingLib.finiteMin value) hopt.1 hmin_feas
  exact le_antisymm hell_le_min hmin_le_ell

/--
Problem 11 equality-form optimal package. This is the formal target for the
remaining Appendix E Lemmas 13-15 selected-BFS argument.
-/
structure Theorem4Problem11EqualizedBasicOptimal {n : ℕ} [NeZero n]
    (beta : ℝ) (v : Item n → ℝ) (ρ : TypePolicy 3 n) (ell : ℝ) :
    Prop where
  mirror : Theorem4MirrorSymmetricPolicy ρ
  item_eq :
    ∀ j : Item n, theorem4Problem11PolicyItemValue beta v ρ j = ell
  optimal : Theorem4Problem11PolicyOptimal beta v ρ ell
  basic_feasible : TypePolicy.BasicFeasibleSupportCertificate ρ

/-- Problem 11's real-vector epigraph feasibility in the paper's `x,z,λ` variables. -/
structure Theorem4Problem11RealLPFeasible {n : ℕ}
    (beta : ℝ) (v : Item n → ℝ)
    (x z : Item n → ℝ) (ell : ℝ) : Prop where
  x_nonneg : ∀ j : Item n, 0 ≤ x j
  z_nonneg : ∀ j : Item n, 0 ≤ z j
  sum_x : (∑ j : Item n, x j) = 1
  sum_z : (∑ j : Item n, z j) = 1
  z_mirror : ∀ j : Item n, z (reverseItem j) = z j
  item_le :
    ∀ j : Item n, ell ≤ theorem4Problem11ItemValue beta v x z j

/--
Rebuild the three estimated Problem 11 rows from real `x` and mirror-symmetric
`z` coordinates. Row `1` is the mirror of row `0`; row `2` is the cold-start
row.
-/
noncomputable def theorem4Problem11PolicyOfRealVectors {n : ℕ}
    (x z : Item n → ℝ)
    (hx : ∀ j : Item n, 0 ≤ x j)
    (hz : ∀ j : Item n, 0 ≤ z j)
    (hsx : (∑ j : Item n, x j) = 1)
    (hsz : (∑ j : Item n, z j) = 1) :
    TypePolicy 3 n :=
  fun k =>
    if k = 0 then
      pmfOfRealVector x hx hsx
    else if k = 1 then
      pmfOfRealVector (fun j : Item n => x (reverseItem j))
        (fun j => hx (reverseItem j))
        (by rw [sum_reverseItem, hsx])
    else
      pmfOfRealVector z hz hsz

@[simp] theorem theorem4Problem11PolicyOfRealVectors_zero_toReal {n : ℕ}
    (x z : Item n → ℝ)
    (hx : ∀ j : Item n, 0 ≤ x j)
    (hz : ∀ j : Item n, 0 ≤ z j)
    (hsx : (∑ j : Item n, x j) = 1)
    (hsz : (∑ j : Item n, z j) = 1)
    (j : Item n) :
    ((theorem4Problem11PolicyOfRealVectors x z hx hz hsx hsz 0) j).toReal =
      x j := by
  simp [theorem4Problem11PolicyOfRealVectors]

@[simp] theorem theorem4Problem11PolicyOfRealVectors_one_toReal {n : ℕ}
    (x z : Item n → ℝ)
    (hx : ∀ j : Item n, 0 ≤ x j)
    (hz : ∀ j : Item n, 0 ≤ z j)
    (hsx : (∑ j : Item n, x j) = 1)
    (hsz : (∑ j : Item n, z j) = 1)
    (j : Item n) :
    ((theorem4Problem11PolicyOfRealVectors x z hx hz hsx hsz 1) j).toReal =
      x (reverseItem j) := by
  simp [theorem4Problem11PolicyOfRealVectors]

@[simp] theorem theorem4Problem11PolicyOfRealVectors_two_toReal {n : ℕ}
    (x z : Item n → ℝ)
    (hx : ∀ j : Item n, 0 ≤ x j)
    (hz : ∀ j : Item n, 0 ≤ z j)
    (hsx : (∑ j : Item n, x j) = 1)
    (hsz : (∑ j : Item n, z j) = 1)
    (j : Item n) :
    ((theorem4Problem11PolicyOfRealVectors x z hx hz hsx hsz 2) j).toReal =
      z j := by
  simp [theorem4Problem11PolicyOfRealVectors]

theorem theorem4Problem11PolicyOfRealVectors_mirrorSymmetric {n : ℕ}
    {x z : Item n → ℝ}
    {hx : ∀ j : Item n, 0 ≤ x j}
    {hz : ∀ j : Item n, 0 ≤ z j}
    {hsx : (∑ j : Item n, x j) = 1}
    {hsz : (∑ j : Item n, z j) = 1}
    (hzmirror : ∀ j : Item n, z (reverseItem j) = z j) :
    Theorem4MirrorSymmetricPolicy
      (theorem4Problem11PolicyOfRealVectors x z hx hz hsx hsz) := by
  constructor
  · intro j
    apply (ENNReal.toReal_eq_toReal_iff'
      ((theorem4Problem11PolicyOfRealVectors x z hx hz hsx hsz 1).apply_ne_top
        (reverseItem j))
      ((theorem4Problem11PolicyOfRealVectors x z hx hz hsx hsz 0).apply_ne_top
        j)).mp
    simp [reverseItem_reverseItem]
  · intro j
    apply (ENNReal.toReal_eq_toReal_iff'
      ((theorem4Problem11PolicyOfRealVectors x z hx hz hsx hsz 2).apply_ne_top
        (reverseItem j))
      ((theorem4Problem11PolicyOfRealVectors x z hx hz hsx hsz 2).apply_ne_top
        j)).mp
    simpa using hzmirror j

theorem theorem4Problem11PolicyOfRealVectors_itemValue_eq {n : ℕ}
    {beta : ℝ} {v x z : Item n → ℝ}
    {hx : ∀ j : Item n, 0 ≤ x j}
    {hz : ∀ j : Item n, 0 ≤ z j}
    {hsx : (∑ j : Item n, x j) = 1}
    {hsz : (∑ j : Item n, z j) = 1}
    (j : Item n) :
    theorem4Problem11PolicyItemValue beta v
        (theorem4Problem11PolicyOfRealVectors x z hx hz hsx hsz) j =
      theorem4Problem11ItemValue beta v x z j := by
  unfold theorem4Problem11PolicyItemValue theorem4Problem11ItemValue
  simp

theorem theorem4Problem11RealLPFeasible_of_policy {n : ℕ} [NeZero n]
    {beta : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 3 n} {ell : ℝ}
    (hsym : Theorem4MirrorSymmetricPolicy ρ)
    (hfeas : theorem4Problem11LPFeasible beta v ρ ell) :
    Theorem4Problem11RealLPFeasible beta v
      (fun j : Item n => (ρ 0 j).toReal)
      (fun j : Item n => (ρ 2 j).toReal) ell := by
  exact
    { x_nonneg := fun j => ENNReal.toReal_nonneg
      z_nonneg := fun j => ENNReal.toReal_nonneg
      sum_x := AppliedModelingLib.pmfToRealSum (ρ 0)
      sum_z := AppliedModelingLib.pmfToRealSum (ρ 2)
      z_mirror := fun j => by
        exact congrArg ENNReal.toReal (hsym.2 j)
      item_le := hfeas }

/--
Paper-local weak-duality certificate for Problem 11. The weights are finite
dual multipliers for the item epigraph constraints. Symmetry of `w` makes the
two known-type rows combine into coefficients `4β w_j q_j`; `A` and `B` are
the resulting row-budget upper bounds for the known-type and cold-start rows.
-/
structure Theorem4Problem11DualCertificate {n : ℕ}
    (beta : ℝ) (v : Item n → ℝ)
    (w : Item n → ℝ) (A B ell : ℝ) : Prop where
  weight_nonneg : ∀ j : Item n, 0 ≤ w j
  weight_mirror : ∀ j : Item n, w (reverseItem j) = w j
  weight_sum : (∑ j : Item n, w j) = 1
  x_coeff_le :
    ∀ j : Item n, 4 * beta * w j * pairShare (1 / 2) v j ≤ A
  z_coeff_le :
    ∀ j : Item n, (1 - 2 * beta) * w j ≤ B
  objective : A + B = ell

/--
Problem 11 weak duality in the paper's `x,z,λ` variables: any finite dual
certificate upper-bounds every real feasible solution.
-/
theorem theorem4Problem11DualCertificate_upper_bound {n : ℕ}
    {beta : ℝ} {v : Item n → ℝ}
    (hpos : ∀ j : Item n, 0 < v j)
    {w : Item n → ℝ} {A B ell : ℝ}
    (cert : Theorem4Problem11DualCertificate beta v w A B ell)
    {x z : Item n → ℝ} {ell' : ℝ}
    (hfeas : Theorem4Problem11RealLPFeasible beta v x z ell') :
    ell' ≤ ell := by
  have hweighted :
      (∑ j : Item n, w j * ell') ≤
        ∑ j : Item n, w j * theorem4Problem11ItemValue beta v x z j := by
    refine Finset.sum_le_sum ?_
    intro j _hj
    exact mul_le_mul_of_nonneg_left (hfeas.item_le j)
      (cert.weight_nonneg j)
  have hleft :
      (∑ j : Item n, w j * ell') = ell' := by
    calc
      (∑ j : Item n, w j * ell') = (∑ j : Item n, w j) * ell' := by
        rw [Finset.sum_mul]
      _ = ell' := by
        rw [cert.weight_sum]
        ring
  have hmirror_known :
      (∑ j : Item n,
          w j * (2 * beta *
            ((1 - pairShare (1 / 2) v j) * x (reverseItem j)))) =
        ∑ j : Item n,
          w j * (2 * beta * (pairShare (1 / 2) v j * x j)) := by
    let f : Item n → ℝ :=
      fun j => w j * (2 * beta *
        ((1 - pairShare (1 / 2) v j) * x (reverseItem j)))
    have hrev := (sum_reverseItem f).symm
    dsimp [f] at hrev
    calc
      (∑ j : Item n,
          w j * (2 * beta *
            ((1 - pairShare (1 / 2) v j) * x (reverseItem j))))
          =
        ∑ j : Item n,
          w (reverseItem j) *
            (2 * beta *
              ((1 - pairShare (1 / 2) v (reverseItem j)) *
                x (reverseItem (reverseItem j)))) := hrev
      _ =
        ∑ j : Item n,
          w j * (2 * beta * (pairShare (1 / 2) v j * x j)) := by
          refine Finset.sum_congr rfl ?_
          intro j _hj
          rw [cert.weight_mirror j, reverseItem_reverseItem]
          have hq :
              1 - pairShare (1 / 2) v (reverseItem j) =
                pairShare (1 / 2) v j := by
            exact (pairShare_half_eq_one_sub_reverse j hpos).symm
          rw [hq]
  have hright_split :
      (∑ j : Item n, w j * theorem4Problem11ItemValue beta v x z j) =
        (∑ j : Item n,
          (4 * beta * w j * pairShare (1 / 2) v j) * x j) +
        (∑ j : Item n,
          ((1 - 2 * beta) * w j) * z j) := by
    unfold theorem4Problem11ItemValue
    have hknown :
        (∑ j : Item n,
            w j *
              (2 * beta *
                (pairShare (1 / 2) v j * x j +
                  (1 - pairShare (1 / 2) v j) * x (reverseItem j)))) =
          ∑ j : Item n,
            (4 * beta * w j * pairShare (1 / 2) v j) * x j := by
      calc
        (∑ j : Item n,
            w j *
              (2 * beta *
                (pairShare (1 / 2) v j * x j +
                  (1 - pairShare (1 / 2) v j) * x (reverseItem j))))
            =
          (∑ j : Item n,
            w j * (2 * beta * (pairShare (1 / 2) v j * x j))) +
          (∑ j : Item n,
            w j * (2 * beta *
              ((1 - pairShare (1 / 2) v j) * x (reverseItem j)))) := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl ?_
            intro j _hj
            ring
        _ =
          (∑ j : Item n,
            w j * (2 * beta * (pairShare (1 / 2) v j * x j))) +
          (∑ j : Item n,
            w j * (2 * beta * (pairShare (1 / 2) v j * x j))) := by
            rw [hmirror_known]
        _ =
          ∑ j : Item n,
            (4 * beta * w j * pairShare (1 / 2) v j) * x j := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl ?_
            intro j _hj
            ring
    have hcold :
        (∑ j : Item n, w j * ((1 - 2 * beta) * z j)) =
          ∑ j : Item n, ((1 - 2 * beta) * w j) * z j := by
      refine Finset.sum_congr rfl ?_
      intro j _hj
      ring
    calc
      (∑ j : Item n,
          w j *
            (2 * beta *
                (pairShare (1 / 2) v j * x j +
                  (1 - pairShare (1 / 2) v j) * x (reverseItem j)) +
              (1 - 2 * beta) * z j))
          =
        (∑ j : Item n,
            w j *
              (2 * beta *
                (pairShare (1 / 2) v j * x j +
                  (1 - pairShare (1 / 2) v j) * x (reverseItem j)))) +
        (∑ j : Item n, w j * ((1 - 2 * beta) * z j)) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl ?_
          intro j _hj
          ring
      _ =
        (∑ j : Item n,
          (4 * beta * w j * pairShare (1 / 2) v j) * x j) +
        (∑ j : Item n,
          ((1 - 2 * beta) * w j) * z j) := by
          rw [hknown, hcold]
  have hx_budget :
      (∑ j : Item n,
          (4 * beta * w j * pairShare (1 / 2) v j) * x j) ≤ A := by
    calc
      (∑ j : Item n,
          (4 * beta * w j * pairShare (1 / 2) v j) * x j)
          ≤ ∑ j : Item n, A * x j := by
            refine Finset.sum_le_sum ?_
            intro j _hj
            exact mul_le_mul_of_nonneg_right (cert.x_coeff_le j)
              (hfeas.x_nonneg j)
      _ = A := by
            rw [← Finset.mul_sum, hfeas.sum_x]
            ring
  have hz_budget :
      (∑ j : Item n, ((1 - 2 * beta) * w j) * z j) ≤ B := by
    calc
      (∑ j : Item n, ((1 - 2 * beta) * w j) * z j)
          ≤ ∑ j : Item n, B * z j := by
            refine Finset.sum_le_sum ?_
            intro j _hj
            exact mul_le_mul_of_nonneg_right (cert.z_coeff_le j)
              (hfeas.z_nonneg j)
      _ = B := by
            rw [← Finset.mul_sum, hfeas.sum_z]
            ring
  calc
    ell' = ∑ j : Item n, w j * ell' := hleft.symm
    _ ≤ ∑ j : Item n, w j * theorem4Problem11ItemValue beta v x z j :=
      hweighted
    _ = (∑ j : Item n,
          (4 * beta * w j * pairShare (1 / 2) v j) * x j) +
        (∑ j : Item n,
          ((1 - 2 * beta) * w j) * z j) := hright_split
    _ ≤ A + B := add_le_add hx_budget hz_budget
    _ = ell := cert.objective

theorem theorem4Problem11DualCertificate_weighted_itemValue_le {n : ℕ}
    {beta : ℝ} {v : Item n → ℝ}
    (hpos : ∀ j : Item n, 0 < v j)
    {w : Item n → ℝ} {A B ell : ℝ}
    (cert : Theorem4Problem11DualCertificate beta v w A B ell)
    {x z : Item n → ℝ} {ell' : ℝ}
    (hfeas : Theorem4Problem11RealLPFeasible beta v x z ell') :
    (∑ j : Item n, w j * theorem4Problem11ItemValue beta v x z j) ≤ ell := by
  have hmirror_known :
      (∑ j : Item n,
          w j * (2 * beta *
            ((1 - pairShare (1 / 2) v j) * x (reverseItem j)))) =
        ∑ j : Item n,
          w j * (2 * beta * (pairShare (1 / 2) v j * x j)) := by
    let f : Item n → ℝ :=
      fun j => w j * (2 * beta *
        ((1 - pairShare (1 / 2) v j) * x (reverseItem j)))
    have hrev := (sum_reverseItem f).symm
    dsimp [f] at hrev
    calc
      (∑ j : Item n,
          w j * (2 * beta *
            ((1 - pairShare (1 / 2) v j) * x (reverseItem j))))
          =
        ∑ j : Item n,
          w (reverseItem j) *
            (2 * beta *
              ((1 - pairShare (1 / 2) v (reverseItem j)) *
                x (reverseItem (reverseItem j)))) := hrev
      _ =
        ∑ j : Item n,
          w j * (2 * beta * (pairShare (1 / 2) v j * x j)) := by
          refine Finset.sum_congr rfl ?_
          intro j _hj
          rw [cert.weight_mirror j, reverseItem_reverseItem]
          have hq :
              1 - pairShare (1 / 2) v (reverseItem j) =
                pairShare (1 / 2) v j := by
            exact (pairShare_half_eq_one_sub_reverse j hpos).symm
          rw [hq]
  have hright_split :
      (∑ j : Item n, w j * theorem4Problem11ItemValue beta v x z j) =
        (∑ j : Item n,
          (4 * beta * w j * pairShare (1 / 2) v j) * x j) +
        (∑ j : Item n,
          ((1 - 2 * beta) * w j) * z j) := by
    unfold theorem4Problem11ItemValue
    have hknown :
        (∑ j : Item n,
            w j *
              (2 * beta *
                (pairShare (1 / 2) v j * x j +
                  (1 - pairShare (1 / 2) v j) * x (reverseItem j)))) =
          ∑ j : Item n,
            (4 * beta * w j * pairShare (1 / 2) v j) * x j := by
      calc
        (∑ j : Item n,
            w j *
              (2 * beta *
                (pairShare (1 / 2) v j * x j +
                  (1 - pairShare (1 / 2) v j) * x (reverseItem j))))
            =
          (∑ j : Item n,
            w j * (2 * beta * (pairShare (1 / 2) v j * x j))) +
          (∑ j : Item n,
            w j * (2 * beta *
              ((1 - pairShare (1 / 2) v j) * x (reverseItem j)))) := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl ?_
            intro j _hj
            ring
        _ =
          (∑ j : Item n,
            w j * (2 * beta * (pairShare (1 / 2) v j * x j))) +
          (∑ j : Item n,
            w j * (2 * beta * (pairShare (1 / 2) v j * x j))) := by
            rw [hmirror_known]
        _ =
          ∑ j : Item n,
            (4 * beta * w j * pairShare (1 / 2) v j) * x j := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl ?_
            intro j _hj
            ring
    have hcold :
        (∑ j : Item n, w j * ((1 - 2 * beta) * z j)) =
          ∑ j : Item n, ((1 - 2 * beta) * w j) * z j := by
      refine Finset.sum_congr rfl ?_
      intro j _hj
      ring
    calc
      (∑ j : Item n,
          w j *
            (2 * beta *
                (pairShare (1 / 2) v j * x j +
                  (1 - pairShare (1 / 2) v j) * x (reverseItem j)) +
              (1 - 2 * beta) * z j))
          =
        (∑ j : Item n,
            w j *
              (2 * beta *
                (pairShare (1 / 2) v j * x j +
                  (1 - pairShare (1 / 2) v j) * x (reverseItem j)))) +
        (∑ j : Item n, w j * ((1 - 2 * beta) * z j)) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl ?_
          intro j _hj
          ring
      _ =
        (∑ j : Item n,
          (4 * beta * w j * pairShare (1 / 2) v j) * x j) +
        (∑ j : Item n,
          ((1 - 2 * beta) * w j) * z j) := by
          rw [hknown, hcold]
  have hx_budget :
      (∑ j : Item n,
          (4 * beta * w j * pairShare (1 / 2) v j) * x j) ≤ A := by
    calc
      (∑ j : Item n,
          (4 * beta * w j * pairShare (1 / 2) v j) * x j)
          ≤ ∑ j : Item n, A * x j := by
            refine Finset.sum_le_sum ?_
            intro j _hj
            exact mul_le_mul_of_nonneg_right (cert.x_coeff_le j)
              (hfeas.x_nonneg j)
      _ = A := by
            rw [← Finset.mul_sum, hfeas.sum_x]
            ring
  have hz_budget :
      (∑ j : Item n, ((1 - 2 * beta) * w j) * z j) ≤ B := by
    calc
      (∑ j : Item n, ((1 - 2 * beta) * w j) * z j)
          ≤ ∑ j : Item n, B * z j := by
            refine Finset.sum_le_sum ?_
            intro j _hj
            exact mul_le_mul_of_nonneg_right (cert.z_coeff_le j)
              (hfeas.z_nonneg j)
      _ = B := by
            rw [← Finset.mul_sum, hfeas.sum_z]
            ring
  calc
    (∑ j : Item n, w j * theorem4Problem11ItemValue beta v x z j)
        =
      (∑ j : Item n,
          (4 * beta * w j * pairShare (1 / 2) v j) * x j) +
        (∑ j : Item n,
          ((1 - 2 * beta) * w j) * z j) := hright_split
    _ ≤ A + B := add_le_add hx_budget hz_budget
    _ = ell := cert.objective

theorem theorem4Problem11DualCertificate_weighted_itemValue_eq_budget_sum {n : ℕ}
    {beta : ℝ} {v : Item n → ℝ}
    (hpos : ∀ j : Item n, 0 < v j)
    {w : Item n → ℝ} {A B ell : ℝ}
    (cert : Theorem4Problem11DualCertificate beta v w A B ell)
    (x z : Item n → ℝ) :
    (∑ j : Item n, w j * theorem4Problem11ItemValue beta v x z j) =
      (∑ j : Item n,
        (4 * beta * w j * pairShare (1 / 2) v j) * x j) +
      (∑ j : Item n, ((1 - 2 * beta) * w j) * z j) := by
  have hmirror_known :
      (∑ j : Item n,
          w j * (2 * beta *
            ((1 - pairShare (1 / 2) v j) * x (reverseItem j)))) =
        ∑ j : Item n,
          w j * (2 * beta * (pairShare (1 / 2) v j * x j)) := by
    let f : Item n → ℝ :=
      fun j => w j * (2 * beta *
        ((1 - pairShare (1 / 2) v j) * x (reverseItem j)))
    have hrev := (sum_reverseItem f).symm
    dsimp [f] at hrev
    calc
      (∑ j : Item n,
          w j * (2 * beta *
            ((1 - pairShare (1 / 2) v j) * x (reverseItem j))))
          =
        ∑ j : Item n,
          w (reverseItem j) *
            (2 * beta *
              ((1 - pairShare (1 / 2) v (reverseItem j)) *
                x (reverseItem (reverseItem j)))) := hrev
      _ =
        ∑ j : Item n,
          w j * (2 * beta * (pairShare (1 / 2) v j * x j)) := by
          refine Finset.sum_congr rfl ?_
          intro j _hj
          rw [cert.weight_mirror j, reverseItem_reverseItem]
          have hq :
              1 - pairShare (1 / 2) v (reverseItem j) =
                pairShare (1 / 2) v j := by
            exact (pairShare_half_eq_one_sub_reverse j hpos).symm
          rw [hq]
  unfold theorem4Problem11ItemValue
  have hknown :
      (∑ j : Item n,
          w j *
            (2 * beta *
              (pairShare (1 / 2) v j * x j +
                (1 - pairShare (1 / 2) v j) * x (reverseItem j)))) =
        ∑ j : Item n,
          (4 * beta * w j * pairShare (1 / 2) v j) * x j := by
    calc
      (∑ j : Item n,
          w j *
            (2 * beta *
              (pairShare (1 / 2) v j * x j +
                (1 - pairShare (1 / 2) v j) * x (reverseItem j))))
          =
        (∑ j : Item n,
          w j * (2 * beta * (pairShare (1 / 2) v j * x j))) +
        (∑ j : Item n,
          w j * (2 * beta *
            ((1 - pairShare (1 / 2) v j) * x (reverseItem j)))) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl ?_
          intro j _hj
          ring
      _ =
        (∑ j : Item n,
          w j * (2 * beta * (pairShare (1 / 2) v j * x j))) +
        (∑ j : Item n,
          w j * (2 * beta * (pairShare (1 / 2) v j * x j))) := by
          rw [hmirror_known]
      _ =
        ∑ j : Item n,
          (4 * beta * w j * pairShare (1 / 2) v j) * x j := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl ?_
          intro j _hj
          ring
  have hcold :
      (∑ j : Item n, w j * ((1 - 2 * beta) * z j)) =
        ∑ j : Item n, ((1 - 2 * beta) * w j) * z j := by
    refine Finset.sum_congr rfl ?_
    intro j _hj
    ring
  calc
    (∑ j : Item n,
        w j *
          (2 * beta *
              (pairShare (1 / 2) v j * x j +
                (1 - pairShare (1 / 2) v j) * x (reverseItem j)) +
            (1 - 2 * beta) * z j))
        =
      (∑ j : Item n,
          w j *
            (2 * beta *
              (pairShare (1 / 2) v j * x j +
                (1 - pairShare (1 / 2) v j) * x (reverseItem j)))) +
      (∑ j : Item n, w j * ((1 - 2 * beta) * z j)) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl ?_
        intro j _hj
        ring
    _ =
      (∑ j : Item n,
        (4 * beta * w j * pairShare (1 / 2) v j) * x j) +
      (∑ j : Item n, ((1 - 2 * beta) * w j) * z j) := by
        rw [hknown, hcold]

theorem theorem4Problem11DualCertificate_itemValue_eq_of_tight {n : ℕ}
    {beta : ℝ} {v : Item n → ℝ}
    (hpos : ∀ j : Item n, 0 < v j)
    {w : Item n → ℝ} {A B ell : ℝ}
    (hweight_pos : ∀ j : Item n, 0 < w j)
    (cert : Theorem4Problem11DualCertificate beta v w A B ell)
    {x z : Item n → ℝ} {ell' : ℝ}
    (hfeas : Theorem4Problem11RealLPFeasible beta v x z ell')
    (htight : ell' = ell) :
    ∀ j : Item n, theorem4Problem11ItemValue beta v x z j = ell' := by
  classical
  intro j0
  refine le_antisymm ?_ (hfeas.item_le j0)
  by_contra hnot_le
  have hstrict :
      ell' < theorem4Problem11ItemValue beta v x z j0 :=
    lt_of_not_ge hnot_le
  let gap : Item n → ℝ :=
    fun j => w j * (theorem4Problem11ItemValue beta v x z j - ell')
  have hgap_nonneg : ∀ j : Item n, 0 ≤ gap j := by
    intro j
    dsimp [gap]
    exact mul_nonneg (cert.weight_nonneg j)
      (sub_nonneg.mpr (hfeas.item_le j))
  have hgap_j0_pos : 0 < gap j0 := by
    dsimp [gap]
    exact mul_pos (hweight_pos j0) (sub_pos.mpr hstrict)
  have hgap_sum_pos : 0 < ∑ j : Item n, gap j := by
    exact lt_of_lt_of_le hgap_j0_pos
      (Finset.single_le_sum
        (fun j _hj => hgap_nonneg j) (Finset.mem_univ j0))
  have hgap_sum_eq :
      (∑ j : Item n, gap j) =
        (∑ j : Item n, w j * theorem4Problem11ItemValue beta v x z j) -
          ell' := by
    dsimp [gap]
    calc
      (∑ j : Item n,
          w j * (theorem4Problem11ItemValue beta v x z j - ell')) =
        ∑ j : Item n,
          (w j * theorem4Problem11ItemValue beta v x z j - w j * ell') := by
          refine Finset.sum_congr rfl ?_
          intro j _hj
          ring
      _ =
        (∑ j : Item n, w j * theorem4Problem11ItemValue beta v x z j) -
          ∑ j : Item n, w j * ell' := by
          rw [Finset.sum_sub_distrib]
      _ =
        (∑ j : Item n, w j * theorem4Problem11ItemValue beta v x z j) -
          ell' := by
          have hsum_w_ell :
              (∑ j : Item n, w j * ell') = ell' := by
            rw [← Finset.sum_mul, cert.weight_sum]
            ring
          rw [hsum_w_ell]
  have hweighted_gt :
      ell' < ∑ j : Item n, w j * theorem4Problem11ItemValue beta v x z j := by
    have hdiff_pos :
        0 <
          (∑ j : Item n, w j * theorem4Problem11ItemValue beta v x z j) -
            ell' := by
      rwa [← hgap_sum_eq]
    linarith
  have hweighted_le :
      (∑ j : Item n, w j * theorem4Problem11ItemValue beta v x z j) ≤ ell' := by
    have hle :=
      theorem4Problem11DualCertificate_weighted_itemValue_le hpos cert hfeas
    rwa [← htight] at hle
  linarith

private theorem theorem4_weighted_budget_lt_of_coeff_lt {n : ℕ}
    {c x : Item n → ℝ} {A : ℝ} {j0 : Item n}
    (hcoeff : ∀ j : Item n, c j ≤ A)
    (hx_nonneg : ∀ j : Item n, 0 ≤ x j)
    (hsum : (∑ j : Item n, x j) = 1)
    (hstrict : c j0 < A)
    (hxpos : 0 < x j0) :
    (∑ j : Item n, c j * x j) < A := by
  classical
  let gap : Item n → ℝ := fun j => (A - c j) * x j
  have hgap_nonneg : ∀ j : Item n, 0 ≤ gap j := by
    intro j
    dsimp [gap]
    exact mul_nonneg (sub_nonneg.mpr (hcoeff j)) (hx_nonneg j)
  have hgap_j0_pos : 0 < gap j0 := by
    dsimp [gap]
    exact mul_pos (sub_pos.mpr hstrict) hxpos
  have hgap_sum_pos : 0 < ∑ j : Item n, gap j := by
    exact lt_of_lt_of_le hgap_j0_pos
      (Finset.single_le_sum
        (fun j _hj => hgap_nonneg j) (Finset.mem_univ j0))
  have hgap_sum_eq :
      (∑ j : Item n, gap j) =
        A - ∑ j : Item n, c j * x j := by
    dsimp [gap]
    calc
      (∑ j : Item n, (A - c j) * x j) =
          ∑ j : Item n, (A * x j - c j * x j) := by
          refine Finset.sum_congr rfl ?_
          intro j _hj
          ring
      _ =
          (∑ j : Item n, A * x j) -
            ∑ j : Item n, c j * x j := by
          rw [Finset.sum_sub_distrib]
      _ =
          A - ∑ j : Item n, c j * x j := by
          rw [← Finset.mul_sum, hsum]
          ring
  have hdiff_pos : 0 < A - ∑ j : Item n, c j * x j := by
    rwa [← hgap_sum_eq]
  linarith

theorem theorem4Problem11DualCertificate_x_eq_zero_of_tight_coeff_lt {n : ℕ}
    {beta : ℝ} {v : Item n → ℝ}
    (hpos : ∀ j : Item n, 0 < v j)
    {w : Item n → ℝ} {A B ell : ℝ}
    (cert : Theorem4Problem11DualCertificate beta v w A B ell)
    {x z : Item n → ℝ} {ell' : ℝ}
    (hfeas : Theorem4Problem11RealLPFeasible beta v x z ell')
    (hitem : ∀ j : Item n, theorem4Problem11ItemValue beta v x z j = ell')
    (htight : ell' = ell)
    {j0 : Item n}
    (hstrict : 4 * beta * w j0 * pairShare (1 / 2) v j0 < A) :
    x j0 = 0 := by
  by_contra hx_ne
  have hxpos : 0 < x j0 :=
    lt_of_le_of_ne (hfeas.x_nonneg j0) (Ne.symm hx_ne)
  have hx_budget_lt :
      (∑ j : Item n,
          (4 * beta * w j * pairShare (1 / 2) v j) * x j) < A :=
    theorem4_weighted_budget_lt_of_coeff_lt
      (c := fun j : Item n => 4 * beta * w j * pairShare (1 / 2) v j)
      (x := x) (A := A) (j0 := j0)
      cert.x_coeff_le hfeas.x_nonneg hfeas.sum_x hstrict hxpos
  have hz_budget_le :
      (∑ j : Item n, ((1 - 2 * beta) * w j) * z j) ≤ B := by
    calc
      (∑ j : Item n, ((1 - 2 * beta) * w j) * z j)
          ≤ ∑ j : Item n, B * z j := by
            refine Finset.sum_le_sum ?_
            intro j _hj
            exact mul_le_mul_of_nonneg_right (cert.z_coeff_le j)
              (hfeas.z_nonneg j)
      _ = B := by
            rw [← Finset.mul_sum, hfeas.sum_z]
            ring
  have hweighted_eq :
      (∑ j : Item n, w j * theorem4Problem11ItemValue beta v x z j) = ell' := by
    calc
      (∑ j : Item n, w j * theorem4Problem11ItemValue beta v x z j) =
          ∑ j : Item n, w j * ell' := by
          refine Finset.sum_congr rfl ?_
          intro j _hj
          rw [hitem j]
      _ = ell' := by
          rw [← Finset.sum_mul, cert.weight_sum]
          ring
  have hweighted_lt :
      (∑ j : Item n, w j * theorem4Problem11ItemValue beta v x z j) < ell := by
    rw [theorem4Problem11DualCertificate_weighted_itemValue_eq_budget_sum
      hpos cert x z]
    exact lt_of_lt_of_le
      (add_lt_add_of_lt_of_le hx_budget_lt hz_budget_le)
      (le_of_eq cert.objective)
  linarith

theorem theorem4Problem11DualCertificate_z_eq_zero_of_tight_coeff_lt {n : ℕ}
    {beta : ℝ} {v : Item n → ℝ}
    (hpos : ∀ j : Item n, 0 < v j)
    {w : Item n → ℝ} {A B ell : ℝ}
    (cert : Theorem4Problem11DualCertificate beta v w A B ell)
    {x z : Item n → ℝ} {ell' : ℝ}
    (hfeas : Theorem4Problem11RealLPFeasible beta v x z ell')
    (hitem : ∀ j : Item n, theorem4Problem11ItemValue beta v x z j = ell')
    (htight : ell' = ell)
    {j0 : Item n}
    (hstrict : (1 - 2 * beta) * w j0 < B) :
    z j0 = 0 := by
  by_contra hz_ne
  have hzpos : 0 < z j0 :=
    lt_of_le_of_ne (hfeas.z_nonneg j0) (Ne.symm hz_ne)
  have hx_budget_le :
      (∑ j : Item n,
          (4 * beta * w j * pairShare (1 / 2) v j) * x j) ≤ A := by
    calc
      (∑ j : Item n,
          (4 * beta * w j * pairShare (1 / 2) v j) * x j)
          ≤ ∑ j : Item n, A * x j := by
            refine Finset.sum_le_sum ?_
            intro j _hj
            exact mul_le_mul_of_nonneg_right (cert.x_coeff_le j)
              (hfeas.x_nonneg j)
      _ = A := by
            rw [← Finset.mul_sum, hfeas.sum_x]
            ring
  have hz_budget_lt :
      (∑ j : Item n, ((1 - 2 * beta) * w j) * z j) < B :=
    theorem4_weighted_budget_lt_of_coeff_lt
      (c := fun j : Item n => (1 - 2 * beta) * w j)
      (x := z) (A := B) (j0 := j0)
      cert.z_coeff_le hfeas.z_nonneg hfeas.sum_z hstrict hzpos
  have hweighted_eq :
      (∑ j : Item n, w j * theorem4Problem11ItemValue beta v x z j) = ell' := by
    calc
      (∑ j : Item n, w j * theorem4Problem11ItemValue beta v x z j) =
          ∑ j : Item n, w j * ell' := by
          refine Finset.sum_congr rfl ?_
          intro j _hj
          rw [hitem j]
      _ = ell' := by
          rw [← Finset.sum_mul, cert.weight_sum]
          ring
  have hweighted_lt :
      (∑ j : Item n, w j * theorem4Problem11ItemValue beta v x z j) < ell := by
    rw [theorem4Problem11DualCertificate_weighted_itemValue_eq_budget_sum
      hpos cert x z]
    exact lt_of_lt_of_eq
      (add_lt_add_of_le_of_lt hx_budget_le hz_budget_lt)
      cert.objective
  linarith

/-- Raw symmetric dual weight used by the closed-form Problem 11 certificate. -/
noncomputable def theorem4Problem11ClosedDualRawWeight {n : ℕ}
    (v : Item n → ℝ) (t j : Item n) : ℝ :=
  if j.val < t.val then
    pairShare (1 / 2) v t / pairShare (1 / 2) v j
  else if (reverseItem t).val < j.val then
    pairShare (1 / 2) v t / pairShare (1 / 2) v (reverseItem j)
  else
    1

theorem theorem4Problem11ClosedDualRawWeight_before {n : ℕ}
    {v : Item n → ℝ} {t j : Item n}
    (hj : j.val < t.val) :
    theorem4Problem11ClosedDualRawWeight v t j =
      pairShare (1 / 2) v t / pairShare (1 / 2) v j := by
  simp [theorem4Problem11ClosedDualRawWeight, hj]

theorem theorem4Problem11ClosedDualRawWeight_after {n : ℕ}
    {v : Item n → ℝ} {t j : Item n}
    (hleft : t.val ≤ (reverseItem t).val)
    (hj : (reverseItem t).val < j.val) :
    theorem4Problem11ClosedDualRawWeight v t j =
      pairShare (1 / 2) v t /
        pairShare (1 / 2) v (reverseItem j) := by
  have hnleft : ¬ j.val < t.val := by omega
  simp [theorem4Problem11ClosedDualRawWeight, hnleft, hj]

theorem theorem4Problem11ClosedDualRawWeight_middle {n : ℕ}
    {v : Item n → ℝ} {t j : Item n}
    (hnleft : ¬ j.val < t.val)
    (hnafter : ¬ (reverseItem t).val < j.val) :
    theorem4Problem11ClosedDualRawWeight v t j = 1 := by
  simp [theorem4Problem11ClosedDualRawWeight, hnleft, hnafter]

/--
Closed-form Problem 11 dual denominator. This is defined as the finite raw
weight sum; later coordinate lemmas identify it with the paper's displayed
`2 + 2 q_t L_t + tail` denominator.
-/
noncomputable def theorem4Problem11ClosedDualDenominator {n : ℕ}
    (v : Item n → ℝ) (t : Item n) : ℝ :=
  ∑ j : Item n, theorem4Problem11ClosedDualRawWeight v t j

/-- Normalized closed-form Problem 11 dual weights. -/
noncomputable def theorem4Problem11ClosedDualWeight {n : ℕ}
    (v : Item n → ℝ) (t j : Item n) : ℝ :=
  theorem4Problem11ClosedDualRawWeight v t j /
    theorem4Problem11ClosedDualDenominator v t

/-- Known-type row budget in the closed Problem 11 dual certificate. -/
noncomputable def theorem4Problem11ClosedKnownBudget {n : ℕ}
    (beta : ℝ) (v : Item n → ℝ) (t : Item n) : ℝ :=
  4 * beta * pairShare (1 / 2) v t /
    theorem4Problem11ClosedDualDenominator v t

/-- Cold-start row budget in the closed Problem 11 dual certificate. -/
noncomputable def theorem4Problem11ClosedColdBudget {n : ℕ}
    (beta : ℝ) (v : Item n → ℝ) (t : Item n) : ℝ :=
  (1 - 2 * beta) / theorem4Problem11ClosedDualDenominator v t

/-- Closed-form Problem 11 value supplied by the finite dual certificate. -/
noncomputable def theorem4Problem11ClosedDualValue {n : ℕ}
    (beta : ℝ) (v : Item n → ℝ) (t : Item n) : ℝ :=
  theorem4Problem11ClosedKnownBudget beta v t +
    theorem4Problem11ClosedColdBudget beta v t

theorem theorem4Problem11ClosedDualRawWeight_pos {n : ℕ}
    {v : Item n → ℝ} {t j : Item n}
    (hpos : ∀ j : Item n, 0 < v j) :
    0 < theorem4Problem11ClosedDualRawWeight v t j := by
  unfold theorem4Problem11ClosedDualRawWeight
  by_cases hjt : j.val < t.val
  · rw [if_pos hjt]
    exact div_pos
      (pairShare_pos t (by norm_num : (0 : ℝ) < 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1) hpos)
      (pairShare_pos j (by norm_num : (0 : ℝ) < 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1) hpos)
  · by_cases htj : (reverseItem t).val < j.val
    · rw [if_neg hjt, if_pos htj]
      exact div_pos
        (pairShare_pos t (by norm_num : (0 : ℝ) < 1 / 2)
          (by norm_num : (1 / 2 : ℝ) < 1) hpos)
        (pairShare_pos (reverseItem j)
          (by norm_num : (0 : ℝ) < 1 / 2)
          (by norm_num : (1 / 2 : ℝ) < 1) hpos)
    · simp [hjt, htj]

theorem theorem4Problem11ClosedDualRawWeight_nonneg {n : ℕ}
    {v : Item n → ℝ} {t j : Item n}
    (hpos : ∀ j : Item n, 0 < v j) :
    0 ≤ theorem4Problem11ClosedDualRawWeight v t j :=
  (theorem4Problem11ClosedDualRawWeight_pos (v := v) (t := t) (j := j)
    hpos).le

theorem theorem4Problem11ClosedDualDenominator_pos {n : ℕ}
    {v : Item n → ℝ} {t : Item n}
    (hpos : ∀ j : Item n, 0 < v j)
    (hleft : t.val ≤ (reverseItem t).val) :
    0 < theorem4Problem11ClosedDualDenominator v t := by
  have hnonneg :
      ∀ j : Item n, 0 ≤ theorem4Problem11ClosedDualRawWeight v t j :=
    fun j => theorem4Problem11ClosedDualRawWeight_nonneg
      (v := v) (t := t) (j := j) hpos
  have ht_weight :
      theorem4Problem11ClosedDualRawWeight v t t = 1 := by
    unfold theorem4Problem11ClosedDualRawWeight
    have hnot_after : ¬ (reverseItem t).val < t.val := by omega
    simp [hnot_after]
  have hle :
      theorem4Problem11ClosedDualRawWeight v t t ≤
        ∑ j : Item n, theorem4Problem11ClosedDualRawWeight v t j :=
    Finset.single_le_sum (fun j _hj => hnonneg j) (Finset.mem_univ t)
  unfold theorem4Problem11ClosedDualDenominator
  linarith

theorem theorem4Problem11ClosedDualRawWeight_mirror {n : ℕ}
    {v : Item n → ℝ} {t : Item n}
    (hleft : t.val ≤ (reverseItem t).val) (j : Item n) :
    theorem4Problem11ClosedDualRawWeight v t (reverseItem j) =
      theorem4Problem11ClosedDualRawWeight v t j := by
  unfold theorem4Problem11ClosedDualRawWeight
  by_cases hj_left : j.val < t.val
  · have hrev_after :
        (reverseItem t).val < (reverseItem j).val :=
      reverseItem_val_lt_of_val_lt hj_left
    have hrev_not_left : ¬ (reverseItem j).val < t.val := by omega
    simp [hj_left, hrev_not_left, hrev_after, reverseItem_reverseItem]
  · by_cases hj_after : (reverseItem t).val < j.val
    · have hrev_left :
          (reverseItem j).val < t.val := by
        simpa [reverseItem_reverseItem] using
          (reverseItem_val_lt_of_val_lt hj_after)
      have hj_not_left : ¬ j.val < t.val := by omega
      simp [hrev_left, hj_not_left, hj_after]
    · have hrev_not_left : ¬ (reverseItem j).val < t.val := by
        simp [reverseItem] at hj_left hj_after hleft ⊢
        omega
      have hrev_not_after :
          ¬ (reverseItem t).val < (reverseItem j).val := by
        simp [reverseItem] at hj_left hj_after hleft ⊢
        omega
      simp [hj_left, hj_after, hrev_not_left, hrev_not_after]

theorem theorem4Problem11ClosedDualWeight_nonneg {n : ℕ}
    {v : Item n → ℝ} {t j : Item n}
    (hpos : ∀ j : Item n, 0 < v j)
    (hleft : t.val ≤ (reverseItem t).val) :
    0 ≤ theorem4Problem11ClosedDualWeight v t j := by
  unfold theorem4Problem11ClosedDualWeight
  exact div_nonneg
    (theorem4Problem11ClosedDualRawWeight_nonneg
      (v := v) (t := t) (j := j) hpos)
    (theorem4Problem11ClosedDualDenominator_pos
      (v := v) (t := t) hpos hleft).le

theorem theorem4Problem11ClosedDualWeight_pos {n : ℕ}
    {v : Item n → ℝ} {t j : Item n}
    (hpos : ∀ j : Item n, 0 < v j)
    (hleft : t.val ≤ (reverseItem t).val) :
    0 < theorem4Problem11ClosedDualWeight v t j := by
  unfold theorem4Problem11ClosedDualWeight
  exact div_pos
    (theorem4Problem11ClosedDualRawWeight_pos
      (v := v) (t := t) (j := j) hpos)
    (theorem4Problem11ClosedDualDenominator_pos
      (v := v) (t := t) hpos hleft)

theorem theorem4Problem11ClosedDualWeight_mirror {n : ℕ}
    {v : Item n → ℝ} {t : Item n}
    (hleft : t.val ≤ (reverseItem t).val) (j : Item n) :
    theorem4Problem11ClosedDualWeight v t (reverseItem j) =
      theorem4Problem11ClosedDualWeight v t j := by
  unfold theorem4Problem11ClosedDualWeight
  rw [theorem4Problem11ClosedDualRawWeight_mirror hleft j]

theorem theorem4Problem11ClosedDualWeight_sum_eq_one {n : ℕ}
    {v : Item n → ℝ} {t : Item n}
    (hpos : ∀ j : Item n, 0 < v j)
    (hleft : t.val ≤ (reverseItem t).val) :
    (∑ j : Item n, theorem4Problem11ClosedDualWeight v t j) = 1 := by
  have hDpos :
      0 < theorem4Problem11ClosedDualDenominator v t :=
    theorem4Problem11ClosedDualDenominator_pos
      (v := v) (t := t) hpos hleft
  unfold theorem4Problem11ClosedDualWeight
    theorem4Problem11ClosedDualDenominator
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt hDpos)

theorem theorem4Problem11ClosedDualRawWeight_mul_pairShare_le {n : ℕ}
    {v : Item n → ℝ} {t j : Item n}
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hleft : t.val ≤ (reverseItem t).val) :
    theorem4Problem11ClosedDualRawWeight v t j *
        pairShare (1 / 2) v j ≤
      pairShare (1 / 2) v t := by
  by_cases hj_left : j.val < t.val
  · unfold theorem4Problem11ClosedDualRawWeight
    have hqj_pos : 0 < pairShare (2 : ℝ)⁻¹ v j :=
      pairShare_pos j
        (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)
        (by norm_num : ((2 : ℝ)⁻¹) < 1) hpos
    simp [hj_left]
    change pairShare (2 : ℝ)⁻¹ v t / pairShare (2 : ℝ)⁻¹ v j *
        pairShare (2 : ℝ)⁻¹ v j ≤ pairShare (2 : ℝ)⁻¹ v t
    field_simp [ne_of_gt hqj_pos]
    exact le_rfl
  · by_cases hj_after : (reverseItem t).val < j.val
    · unfold theorem4Problem11ClosedDualRawWeight
      have hrev_left :
          (reverseItem j).val < t.val := by
        simpa [reverseItem_reverseItem] using
          (reverseItem_val_lt_of_val_lt hj_after)
      have hqrev_pos : 0 < pairShare (2 : ℝ)⁻¹ v (reverseItem j) :=
        pairShare_pos (reverseItem j)
          (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)
          (by norm_num : ((2 : ℝ)⁻¹) < 1) hpos
      have hqj_le_qrev :
          pairShare (2 : ℝ)⁻¹ v j ≤
            pairShare (2 : ℝ)⁻¹ v (reverseItem j) := by
        have hrev_lt_j : (reverseItem j).val < j.val := by
          omega
        exact (pairShare_strictAnti_index
          (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)
          (by norm_num : ((2 : ℝ)⁻¹) < 1)
          hpos hdec hrev_lt_j).le
      simp [hj_left, hj_after]
      change pairShare (2 : ℝ)⁻¹ v t /
            pairShare (2 : ℝ)⁻¹ v (reverseItem j) *
          pairShare (2 : ℝ)⁻¹ v j ≤
        pairShare (2 : ℝ)⁻¹ v t
      calc
        pairShare (2 : ℝ)⁻¹ v t /
            pairShare (2 : ℝ)⁻¹ v (reverseItem j) *
            pairShare (2 : ℝ)⁻¹ v j
            ≤
          pairShare (2 : ℝ)⁻¹ v t /
            pairShare (2 : ℝ)⁻¹ v (reverseItem j) *
            pairShare (2 : ℝ)⁻¹ v (reverseItem j) := by
            exact mul_le_mul_of_nonneg_left hqj_le_qrev
              (div_nonneg
                (pairShare_pos t
                  (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)
                  (by norm_num : ((2 : ℝ)⁻¹) < 1) hpos).le
                hqrev_pos.le)
        _ = pairShare (2 : ℝ)⁻¹ v t := by
            field_simp [ne_of_gt hqrev_pos]
    · unfold theorem4Problem11ClosedDualRawWeight
      have ht_le_j : t.val ≤ j.val := by omega
      have hqj_le_qt :
          pairShare (2 : ℝ)⁻¹ v j ≤ pairShare (2 : ℝ)⁻¹ v t := by
        rcases lt_or_eq_of_le ht_le_j with htj | htj
        · exact (pairShare_strictAnti_index
            (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)
            (by norm_num : ((2 : ℝ)⁻¹) < 1)
            hpos hdec htj).le
        · have hj_eq : j = t := Fin.ext htj.symm
          subst j
          exact le_rfl
      simpa [hj_left, hj_after] using hqj_le_qt

theorem theorem4Problem11ClosedDualRawWeight_le_one {n : ℕ}
    {v : Item n → ℝ} {t j : Item n}
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hleft : t.val ≤ (reverseItem t).val) :
    theorem4Problem11ClosedDualRawWeight v t j ≤ 1 := by
  by_cases hj_left : j.val < t.val
  · unfold theorem4Problem11ClosedDualRawWeight
    have hqj_pos : 0 < pairShare (2 : ℝ)⁻¹ v j :=
      pairShare_pos j
        (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)
        (by norm_num : ((2 : ℝ)⁻¹) < 1) hpos
    have hqt_le_qj :
        pairShare (2 : ℝ)⁻¹ v t ≤ pairShare (2 : ℝ)⁻¹ v j :=
      (pairShare_strictAnti_index
        (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)
        (by norm_num : ((2 : ℝ)⁻¹) < 1)
        hpos hdec hj_left).le
    simp [hj_left]
    change pairShare (2 : ℝ)⁻¹ v t / pairShare (2 : ℝ)⁻¹ v j ≤ 1
    calc
      pairShare (2 : ℝ)⁻¹ v t / pairShare (2 : ℝ)⁻¹ v j
          = pairShare (2 : ℝ)⁻¹ v t *
              (pairShare (2 : ℝ)⁻¹ v j)⁻¹ := by
            ring
      _ ≤ pairShare (2 : ℝ)⁻¹ v j *
            (pairShare (2 : ℝ)⁻¹ v j)⁻¹ := by
            exact mul_le_mul_of_nonneg_right hqt_le_qj
              (inv_nonneg.mpr hqj_pos.le)
      _ = 1 := by
            field_simp [ne_of_gt hqj_pos]
  · by_cases hj_after : (reverseItem t).val < j.val
    · unfold theorem4Problem11ClosedDualRawWeight
      have hrev_left :
          (reverseItem j).val < t.val := by
        simpa [reverseItem_reverseItem] using
          (reverseItem_val_lt_of_val_lt hj_after)
      have hqrev_pos : 0 < pairShare (2 : ℝ)⁻¹ v (reverseItem j) :=
        pairShare_pos (reverseItem j)
          (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)
          (by norm_num : ((2 : ℝ)⁻¹) < 1) hpos
      have hqt_le_qrev :
          pairShare (2 : ℝ)⁻¹ v t ≤
            pairShare (2 : ℝ)⁻¹ v (reverseItem j) :=
        (pairShare_strictAnti_index
          (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)
          (by norm_num : ((2 : ℝ)⁻¹) < 1)
          hpos hdec hrev_left).le
      simp [hj_left, hj_after]
      change pairShare (2 : ℝ)⁻¹ v t /
          pairShare (2 : ℝ)⁻¹ v (reverseItem j) ≤ 1
      calc
        pairShare (2 : ℝ)⁻¹ v t /
            pairShare (2 : ℝ)⁻¹ v (reverseItem j)
            =
          pairShare (2 : ℝ)⁻¹ v t *
            (pairShare (2 : ℝ)⁻¹ v (reverseItem j))⁻¹ := by
            ring
        _ ≤
          pairShare (2 : ℝ)⁻¹ v (reverseItem j) *
            (pairShare (2 : ℝ)⁻¹ v (reverseItem j))⁻¹ := by
            exact mul_le_mul_of_nonneg_right hqt_le_qrev
              (inv_nonneg.mpr hqrev_pos.le)
        _ = 1 := by
            field_simp [ne_of_gt hqrev_pos]
    · unfold theorem4Problem11ClosedDualRawWeight
      simp [hj_left, hj_after]

theorem theorem4Problem11ClosedDualRawWeight_mul_pairShare_lt_of_pivot_lt {n : ℕ}
    {v : Item n → ℝ} {t j : Item n}
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hleft : t.val ≤ (reverseItem t).val)
    (hj : t.val < j.val) :
    theorem4Problem11ClosedDualRawWeight v t j *
        pairShare (1 / 2) v j <
      pairShare (1 / 2) v t := by
  have hnot_left : ¬ j.val < t.val := by omega
  by_cases hj_after : (reverseItem t).val < j.val
  · unfold theorem4Problem11ClosedDualRawWeight
    have hrev_left :
        (reverseItem j).val < t.val := by
      simpa [reverseItem_reverseItem] using
        (reverseItem_val_lt_of_val_lt hj_after)
    have hrev_lt_j : (reverseItem j).val < j.val := by omega
    have hqj_lt_qrev :
        pairShare (2 : ℝ)⁻¹ v j <
          pairShare (2 : ℝ)⁻¹ v (reverseItem j) :=
      pairShare_strictAnti_index
        (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)
        (by norm_num : ((2 : ℝ)⁻¹) < 1)
        hpos hdec hrev_lt_j
    have hqt_pos : 0 < pairShare (2 : ℝ)⁻¹ v t :=
      pairShare_pos t (by norm_num) (by norm_num) hpos
    have hqrev_pos : 0 < pairShare (2 : ℝ)⁻¹ v (reverseItem j) :=
      pairShare_pos (reverseItem j) (by norm_num) (by norm_num) hpos
    simp [hnot_left, hj_after]
    change pairShare (2 : ℝ)⁻¹ v t /
          pairShare (2 : ℝ)⁻¹ v (reverseItem j) *
        pairShare (2 : ℝ)⁻¹ v j <
      pairShare (2 : ℝ)⁻¹ v t
    calc
      pairShare (2 : ℝ)⁻¹ v t /
            pairShare (2 : ℝ)⁻¹ v (reverseItem j) *
          pairShare (2 : ℝ)⁻¹ v j
          <
        pairShare (2 : ℝ)⁻¹ v t /
            pairShare (2 : ℝ)⁻¹ v (reverseItem j) *
          pairShare (2 : ℝ)⁻¹ v (reverseItem j) := by
          exact mul_lt_mul_of_pos_left hqj_lt_qrev
            (div_pos hqt_pos hqrev_pos)
      _ = pairShare (2 : ℝ)⁻¹ v t := by
          field_simp [ne_of_gt hqrev_pos]
  · unfold theorem4Problem11ClosedDualRawWeight
    have hqj_lt_qt :
        pairShare (2 : ℝ)⁻¹ v j < pairShare (2 : ℝ)⁻¹ v t :=
      pairShare_strictAnti_index
        (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)
        (by norm_num : ((2 : ℝ)⁻¹) < 1)
        hpos hdec hj
    simpa [hnot_left, hj_after] using hqj_lt_qt

theorem theorem4Problem11ClosedDualRawWeight_lt_one_of_lt_pivot {n : ℕ}
    {v : Item n → ℝ} {t j : Item n}
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hj : j.val < t.val) :
    theorem4Problem11ClosedDualRawWeight v t j < 1 := by
  unfold theorem4Problem11ClosedDualRawWeight
  have hqt_lt_qj :
      pairShare (2 : ℝ)⁻¹ v t < pairShare (2 : ℝ)⁻¹ v j :=
    pairShare_strictAnti_index
      (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)
      (by norm_num : ((2 : ℝ)⁻¹) < 1)
      hpos hdec hj
  have hqj_pos : 0 < pairShare (2 : ℝ)⁻¹ v j :=
    pairShare_pos j (by norm_num) (by norm_num) hpos
  simp [hj]
  rw [div_lt_iff₀ hqj_pos]
  nlinarith

theorem theorem4Problem11ClosedDualWeight_x_coeff_le {n : ℕ}
    {beta : ℝ} {v : Item n → ℝ} {t j : Item n}
    (hbeta : 0 ≤ beta)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hleft : t.val ≤ (reverseItem t).val) :
    4 * beta * theorem4Problem11ClosedDualWeight v t j *
        pairShare (1 / 2) v j ≤
      theorem4Problem11ClosedKnownBudget beta v t := by
  have hDpos :
      0 < theorem4Problem11ClosedDualDenominator v t :=
    theorem4Problem11ClosedDualDenominator_pos
      (v := v) (t := t) hpos hleft
  have hraw :
      theorem4Problem11ClosedDualRawWeight v t j *
          pairShare (1 / 2) v j ≤
        pairShare (1 / 2) v t :=
    theorem4Problem11ClosedDualRawWeight_mul_pairShare_le
      hpos hdec hleft
  unfold theorem4Problem11ClosedDualWeight
    theorem4Problem11ClosedKnownBudget
  calc
    4 * beta *
          (theorem4Problem11ClosedDualRawWeight v t j /
            theorem4Problem11ClosedDualDenominator v t) *
          pairShare (1 / 2) v j
        =
      (4 * beta / theorem4Problem11ClosedDualDenominator v t) *
        (theorem4Problem11ClosedDualRawWeight v t j *
          pairShare (1 / 2) v j) := by
        ring
    _ ≤
      (4 * beta / theorem4Problem11ClosedDualDenominator v t) *
        pairShare (1 / 2) v t := by
        exact mul_le_mul_of_nonneg_left hraw
          (div_nonneg (mul_nonneg (by norm_num) hbeta) hDpos.le)
    _ = 4 * beta * pairShare (1 / 2) v t /
          theorem4Problem11ClosedDualDenominator v t := by
        ring

theorem theorem4Problem11ClosedDualWeight_z_coeff_le {n : ℕ}
    {beta : ℝ} {v : Item n → ℝ} {t j : Item n}
    (hcold : 0 ≤ 1 - 2 * beta)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hleft : t.val ≤ (reverseItem t).val) :
    (1 - 2 * beta) * theorem4Problem11ClosedDualWeight v t j ≤
      theorem4Problem11ClosedColdBudget beta v t := by
  have hDpos :
      0 < theorem4Problem11ClosedDualDenominator v t :=
    theorem4Problem11ClosedDualDenominator_pos
      (v := v) (t := t) hpos hleft
  have hraw :
      theorem4Problem11ClosedDualRawWeight v t j ≤ 1 :=
    theorem4Problem11ClosedDualRawWeight_le_one hpos hdec hleft
  unfold theorem4Problem11ClosedDualWeight
    theorem4Problem11ClosedColdBudget
  calc
    (1 - 2 * beta) *
        (theorem4Problem11ClosedDualRawWeight v t j /
          theorem4Problem11ClosedDualDenominator v t)
        =
      ((1 - 2 * beta) / theorem4Problem11ClosedDualDenominator v t) *
        theorem4Problem11ClosedDualRawWeight v t j := by
        ring
    _ ≤ ((1 - 2 * beta) /
          theorem4Problem11ClosedDualDenominator v t) * 1 := by
        exact mul_le_mul_of_nonneg_left hraw
          (div_nonneg hcold hDpos.le)
    _ = (1 - 2 * beta) /
          theorem4Problem11ClosedDualDenominator v t := by
        ring

theorem theorem4Problem11ClosedDualWeight_x_coeff_lt_of_pivot_lt {n : ℕ}
    {beta : ℝ} {v : Item n → ℝ} {t j : Item n}
    (hbeta_pos : 0 < beta)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hleft : t.val ≤ (reverseItem t).val)
    (hj : t.val < j.val) :
    4 * beta * theorem4Problem11ClosedDualWeight v t j *
        pairShare (1 / 2) v j <
      theorem4Problem11ClosedKnownBudget beta v t := by
  have hDpos :
      0 < theorem4Problem11ClosedDualDenominator v t :=
    theorem4Problem11ClosedDualDenominator_pos
      (v := v) (t := t) hpos hleft
  have hraw :
      theorem4Problem11ClosedDualRawWeight v t j *
          pairShare (1 / 2) v j <
        pairShare (1 / 2) v t :=
    theorem4Problem11ClosedDualRawWeight_mul_pairShare_lt_of_pivot_lt
      hpos hdec hleft hj
  unfold theorem4Problem11ClosedDualWeight
    theorem4Problem11ClosedKnownBudget
  calc
    4 * beta *
          (theorem4Problem11ClosedDualRawWeight v t j /
            theorem4Problem11ClosedDualDenominator v t) *
          pairShare (1 / 2) v j
        =
      (4 * beta / theorem4Problem11ClosedDualDenominator v t) *
        (theorem4Problem11ClosedDualRawWeight v t j *
          pairShare (1 / 2) v j) := by
        ring
    _ <
      (4 * beta / theorem4Problem11ClosedDualDenominator v t) *
        pairShare (1 / 2) v t := by
        exact mul_lt_mul_of_pos_left hraw
          (div_pos (by positivity : 0 < 4 * beta) hDpos)
    _ = 4 * beta * pairShare (1 / 2) v t /
          theorem4Problem11ClosedDualDenominator v t := by
        ring

theorem theorem4Problem11ClosedDualWeight_z_coeff_lt_of_lt_pivot {n : ℕ}
    {beta : ℝ} {v : Item n → ℝ} {t j : Item n}
    (hbeta_half : beta < 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hleft : t.val ≤ (reverseItem t).val)
    (hj : j.val < t.val) :
    (1 - 2 * beta) * theorem4Problem11ClosedDualWeight v t j <
      theorem4Problem11ClosedColdBudget beta v t := by
  have hDpos :
      0 < theorem4Problem11ClosedDualDenominator v t :=
    theorem4Problem11ClosedDualDenominator_pos
      (v := v) (t := t) hpos hleft
  have hraw :
      theorem4Problem11ClosedDualRawWeight v t j < 1 :=
    theorem4Problem11ClosedDualRawWeight_lt_one_of_lt_pivot
      hpos hdec hj
  have hcold_pos : 0 < 1 - 2 * beta := by nlinarith
  unfold theorem4Problem11ClosedDualWeight
    theorem4Problem11ClosedColdBudget
  calc
    (1 - 2 * beta) *
        (theorem4Problem11ClosedDualRawWeight v t j /
          theorem4Problem11ClosedDualDenominator v t)
        =
      ((1 - 2 * beta) / theorem4Problem11ClosedDualDenominator v t) *
        theorem4Problem11ClosedDualRawWeight v t j := by
        ring
    _ < ((1 - 2 * beta) /
          theorem4Problem11ClosedDualDenominator v t) * 1 := by
        exact mul_lt_mul_of_pos_left hraw
          (div_pos hcold_pos hDpos)
    _ = (1 - 2 * beta) /
          theorem4Problem11ClosedDualDenominator v t := by
        ring

/--
Closed-form finite dual certificate for Problem 11 at any pivot on the left
half of the item line.
-/
theorem theorem4Problem11ClosedDualCertificate {n : ℕ}
    {beta : ℝ} {v : Item n → ℝ} {t : Item n}
    (hbeta : 0 ≤ beta) (hcold : 0 ≤ 1 - 2 * beta)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hleft : t.val ≤ (reverseItem t).val) :
    Theorem4Problem11DualCertificate beta v
      (theorem4Problem11ClosedDualWeight v t)
      (theorem4Problem11ClosedKnownBudget beta v t)
      (theorem4Problem11ClosedColdBudget beta v t)
      (theorem4Problem11ClosedDualValue beta v t) where
  weight_nonneg := fun j =>
    theorem4Problem11ClosedDualWeight_nonneg hpos hleft
  weight_mirror := fun j =>
    theorem4Problem11ClosedDualWeight_mirror hleft j
  weight_sum :=
    theorem4Problem11ClosedDualWeight_sum_eq_one hpos hleft
  x_coeff_le := fun j =>
    theorem4Problem11ClosedDualWeight_x_coeff_le
      hbeta hpos hdec hleft
  z_coeff_le := fun j =>
    theorem4Problem11ClosedDualWeight_z_coeff_le
      hcold hpos hdec hleft
  objective := by
    unfold theorem4Problem11ClosedDualValue
    rfl

theorem theorem4Problem11PolicyOptimal_item_eq_of_closedDual_tight {n : ℕ}
    [NeZero n] {beta : ℝ} {v : Item n → ℝ} {t : Item n}
    {ρ : TypePolicy 3 n} {ell : ℝ}
    (hbeta_pos : 0 < beta)
    (hbeta_half : beta < 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hleft : t.val ≤ (reverseItem t).val)
    (hvalue : ell = theorem4Problem11ClosedDualValue beta v t)
    (hopt : Theorem4Problem11PolicyOptimal beta v ρ ell) :
    ∀ j : Item n, theorem4Problem11PolicyItemValue beta v ρ j = ell := by
  let x : Item n → ℝ := fun j => (ρ 0 j).toReal
  let z : Item n → ℝ := fun j => (ρ 2 j).toReal
  let cert :
      Theorem4Problem11DualCertificate beta v
        (theorem4Problem11ClosedDualWeight v t)
        (theorem4Problem11ClosedKnownBudget beta v t)
        (theorem4Problem11ClosedColdBudget beta v t)
        (theorem4Problem11ClosedDualValue beta v t) :=
    theorem4Problem11ClosedDualCertificate
      hbeta_pos.le (by nlinarith) hpos hdec hleft
  have hfeas : Theorem4Problem11RealLPFeasible beta v x z ell := by
    dsimp [x, z]
    exact theorem4Problem11RealLPFeasible_of_policy hopt.1 hopt.2.1
  have hitem :
      ∀ j : Item n, theorem4Problem11ItemValue beta v x z j = ell := by
    exact theorem4Problem11DualCertificate_itemValue_eq_of_tight hpos
      (fun j => theorem4Problem11ClosedDualWeight_pos
        (v := v) (t := t) (j := j) hpos hleft)
      cert hfeas hvalue
  intro j
  simpa [x, z, theorem4Problem11PolicyItemValue,
    theorem4Problem11ItemValue] using hitem j

/--
Closed-form Problem 11 dual upper bound for every real feasible solution.
-/
theorem theorem4Problem11ClosedDual_upper_bound {n : ℕ}
    {beta : ℝ} {v : Item n → ℝ} {t : Item n}
    (hbeta : 0 ≤ beta) (hcold : 0 ≤ 1 - 2 * beta)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hleft : t.val ≤ (reverseItem t).val)
    {x z : Item n → ℝ} {ell : ℝ}
    (hfeas : Theorem4Problem11RealLPFeasible beta v x z ell) :
    ell ≤ theorem4Problem11ClosedDualValue beta v t := by
  exact theorem4Problem11DualCertificate_upper_bound hpos
    (theorem4Problem11ClosedDualCertificate
      hbeta hcold hpos hdec hleft)
    hfeas

/--
The paper's equality-form optimal basic feasible solution data for Problem 11,
before rebuilding the PMF policy.
-/
structure Theorem4Problem11EqualityFormOptimalBFS {n : ℕ}
    (beta : ℝ) (v : Item n → ℝ)
    (x z : Item n → ℝ) (ell : ℝ) : Prop where
  feasible : Theorem4Problem11RealLPFeasible beta v x z ell
  item_eq :
    ∀ j : Item n, theorem4Problem11ItemValue beta v x z j = ell
  optimal :
    ∀ {x' z' : Item n → ℝ} {ell' : ℝ},
      Theorem4Problem11RealLPFeasible beta v x' z' ell' → ell' ≤ ell
  basic_feasible :
    TypePolicy.BasicFeasibleSupportCertificate
      (theorem4Problem11PolicyOfRealVectors x z
        feasible.x_nonneg feasible.z_nonneg feasible.sum_x feasible.sum_z)

/--
Closed-dual tightness bridge for Problem 11: once a real `x,z` solution is
feasible and equalizes every item at the closed dual value for a left-half
pivot, the finite dual upper bound supplies the optimality field required by
the paper's equality-form optimal BFS package.
-/
theorem theorem4Problem11EqualityFormOptimalBFS_of_closedDual_tight {n : ℕ}
    {beta : ℝ} {v x z : Item n → ℝ} {t : Item n}
    (hbeta : 0 ≤ beta) (hcold : 0 ≤ 1 - 2 * beta)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hleft : t.val ≤ (reverseItem t).val)
    (hfeas :
      Theorem4Problem11RealLPFeasible beta v x z
        (theorem4Problem11ClosedDualValue beta v t))
    (hitem_eq :
      ∀ j : Item n,
        theorem4Problem11ItemValue beta v x z j =
          theorem4Problem11ClosedDualValue beta v t)
    (hbasic :
      TypePolicy.BasicFeasibleSupportCertificate
        (theorem4Problem11PolicyOfRealVectors x z
          hfeas.x_nonneg hfeas.z_nonneg hfeas.sum_x hfeas.sum_z)) :
    Theorem4Problem11EqualityFormOptimalBFS beta v x z
      (theorem4Problem11ClosedDualValue beta v t) where
  feasible := hfeas
  item_eq := hitem_eq
  optimal := fun hfeas' =>
    theorem4Problem11ClosedDual_upper_bound
      hbeta hcold hpos hdec hleft hfeas'
  basic_feasible := hbasic

theorem theorem4Problem11PolicyOptimal_of_equalityFormOptimalBFS {n : ℕ}
    [NeZero n] {beta : ℝ} {v x z : Item n → ℝ} {ell : ℝ}
    (h : Theorem4Problem11EqualityFormOptimalBFS beta v x z ell) :
    Theorem4Problem11PolicyOptimal beta v
      (theorem4Problem11PolicyOfRealVectors x z
        h.feasible.x_nonneg h.feasible.z_nonneg
        h.feasible.sum_x h.feasible.sum_z) ell := by
  let ρ : TypePolicy 3 n :=
    theorem4Problem11PolicyOfRealVectors x z
      h.feasible.x_nonneg h.feasible.z_nonneg
      h.feasible.sum_x h.feasible.sum_z
  refine ⟨?_, ?_, ?_⟩
  · dsimp [ρ]
    exact theorem4Problem11PolicyOfRealVectors_mirrorSymmetric
      h.feasible.z_mirror
  · intro j
    rw [theorem4Problem11PolicyOfRealVectors_itemValue_eq]
    exact le_of_eq (h.item_eq j).symm
  · intro ρ' ell' hsym' hfeas'
    exact h.optimal (theorem4Problem11RealLPFeasible_of_policy hsym' hfeas')

/--
A feasible real Problem 11 policy at a closed dual value is globally optimal.
This is the direct finite-duality bridge and does not use a basic-feasibility
or support certificate.
-/
theorem theorem4Problem11PolicyOptimal_of_closedDual_feasible {n : ℕ}
    [NeZero n] {beta : ℝ} {v x z : Item n → ℝ} {t : Item n}
    (hbeta : 0 ≤ beta) (hcold : 0 ≤ 1 - 2 * beta)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hleft : t.val ≤ (reverseItem t).val)
    (hfeas :
      Theorem4Problem11RealLPFeasible beta v x z
        (theorem4Problem11ClosedDualValue beta v t)) :
    Theorem4Problem11PolicyOptimal beta v
      (theorem4Problem11PolicyOfRealVectors x z
        hfeas.x_nonneg hfeas.z_nonneg hfeas.sum_x hfeas.sum_z)
      (theorem4Problem11ClosedDualValue beta v t) := by
  let ρ : TypePolicy 3 n :=
    theorem4Problem11PolicyOfRealVectors x z
      hfeas.x_nonneg hfeas.z_nonneg hfeas.sum_x hfeas.sum_z
  refine ⟨?_, ?_, ?_⟩
  · dsimp [ρ]
    exact theorem4Problem11PolicyOfRealVectors_mirrorSymmetric hfeas.z_mirror
  · intro j
    rw [theorem4Problem11PolicyOfRealVectors_itemValue_eq]
    exact hfeas.item_le j
  · intro ρ' ell' hsym' hfeas'
    exact theorem4Problem11ClosedDual_upper_bound
      hbeta hcold hpos hdec hleft
      (theorem4Problem11RealLPFeasible_of_policy hsym' hfeas')

theorem theorem4Problem11EqualizedBasicOptimal_of_equalityFormOptimalBFS
    {n : ℕ} [NeZero n] {beta : ℝ} {v x z : Item n → ℝ} {ell : ℝ}
    (h : Theorem4Problem11EqualityFormOptimalBFS beta v x z ell) :
    Theorem4Problem11EqualizedBasicOptimal beta v
      (theorem4Problem11PolicyOfRealVectors x z
        h.feasible.x_nonneg h.feasible.z_nonneg
        h.feasible.sum_x h.feasible.sum_z) ell := by
  refine
    { mirror := ?_
      item_eq := ?_
      optimal := theorem4Problem11PolicyOptimal_of_equalityFormOptimalBFS h
      basic_feasible := h.basic_feasible }
  · exact theorem4Problem11PolicyOfRealVectors_mirrorSymmetric
      h.feasible.z_mirror
  · intro j
    rw [theorem4Problem11PolicyOfRealVectors_itemValue_eq]
    exact h.item_eq j

/--
Problem 11 / Problem 1 bridge for the equality-form package consumed by
Lemmas 13--15.
-/
theorem theorem4Problem11EqualizedBasicOptimal_feasibleAtLevel_one
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hbeta : 0 ≤ beta) (hcold : 0 ≤ 1 - 2 * beta)
    (hpos : ∀ j : Item n, 0 < v j)
    {ρ : TypePolicy 3 n} {ell : ℝ}
    (h : Theorem4Problem11EqualizedBasicOptimal beta v ρ ell) :
    TypeWeightedRecommendationModel.feasibleAtLevel
      (theorem4EstimatedReducedModel beta v) 1 ρ := by
  exact theorem4Problem11PolicyOptimal_feasibleAtLevel_one
    hbeta hcold hpos h.optimal

/--
Problem 11 / Problem 1 bridge for the paper's real equality-form optimal BFS
data after rebuilding the three-type policy.
-/
theorem theorem4Problem11EqualityFormOptimalBFS_feasibleAtLevel_one
    {n : ℕ} [NeZero n] {beta : ℝ} {v x z : Item n → ℝ} {ell : ℝ}
    (hbeta : 0 ≤ beta) (hcold : 0 ≤ 1 - 2 * beta)
    (hpos : ∀ j : Item n, 0 < v j)
    (h : Theorem4Problem11EqualityFormOptimalBFS beta v x z ell) :
    TypeWeightedRecommendationModel.feasibleAtLevel
      (theorem4EstimatedReducedModel beta v) 1
      (theorem4Problem11PolicyOfRealVectors x z
        h.feasible.x_nonneg h.feasible.z_nonneg
        h.feasible.sum_x h.feasible.sum_z) := by
  exact theorem4Problem11PolicyOptimal_feasibleAtLevel_one
    hbeta hcold hpos
    (theorem4Problem11PolicyOptimal_of_equalityFormOptimalBFS h)

theorem theorem4UniformTypePolicy_mirrorSymmetric {n : ℕ} [NeZero n] :
    Theorem4MirrorSymmetricPolicy
      (TypeWeightedRecommendationModel.uniformTypePolicy (K := 3) (n := n)) := by
  constructor
  · intro j
    simp [TypeWeightedRecommendationModel.uniformTypePolicy]
  · intro j
    simp [TypeWeightedRecommendationModel.uniformTypePolicy]

theorem theorem4Problem11UniformPolicyItemValue_eq_inv_card
    {n : ℕ} [NeZero n] (beta : ℝ) (v : Item n → ℝ) (j : Item n) :
    theorem4Problem11PolicyItemValue beta v
        (TypeWeightedRecommendationModel.uniformTypePolicy (K := 3) (n := n)) j =
      (n : ℝ)⁻¹ := by
  unfold theorem4Problem11PolicyItemValue theorem4Problem11ItemValue
  simp [TypeWeightedRecommendationModel.uniformTypePolicy_apply_toReal]
  ring

theorem theorem4Problem11PolicyOptimal_value_pos
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    {ρ : TypePolicy 3 n} {ell : ℝ}
    (hopt : Theorem4Problem11PolicyOptimal beta v ρ ell) :
    0 < ell := by
  let ρu : TypePolicy 3 n :=
    TypeWeightedRecommendationModel.uniformTypePolicy (K := 3) (n := n)
  have hinv_pos : 0 < (n : ℝ)⁻¹ := by
    have hnpos_nat : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
    exact inv_pos.mpr (by exact_mod_cast hnpos_nat)
  have hsym : Theorem4MirrorSymmetricPolicy ρu :=
    theorem4UniformTypePolicy_mirrorSymmetric
  have hfeas : theorem4Problem11LPFeasible beta v ρu ((n : ℝ)⁻¹) := by
    intro j
    rw [theorem4Problem11UniformPolicyItemValue_eq_inv_card]
  have hle : (n : ℝ)⁻¹ ≤ ell :=
    hopt.2.2 ρu ((n : ℝ)⁻¹) hsym hfeas
  exact lt_of_lt_of_le hinv_pos hle

/--
Appendix E, Lemma 14 value-uniqueness component: any two Problem 11 epigraph
optima have the same objective value. The remaining policy-uniqueness part is
the sparse pivot comparison.
-/
theorem theorem4Problem11PolicyOptimal_value_unique
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    {ρ ρ' : TypePolicy 3 n} {ell ell' : ℝ}
    (hopt : Theorem4Problem11PolicyOptimal beta v ρ ell)
    (hopt' : Theorem4Problem11PolicyOptimal beta v ρ' ell') :
    ell = ell' := by
  have hle : ell' ≤ ell :=
    hopt.2.2 ρ' ell' hopt'.1 hopt'.2.1
  have hge : ell ≤ ell' :=
    hopt'.2.2 ρ ell hopt.1 hopt.2.1
  exact le_antisymm hge hle

theorem theorem4Problem11EqualizedBasicOptimal_value_unique
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    {ρ ρ' : TypePolicy 3 n} {ell ell' : ℝ}
    (h : Theorem4Problem11EqualizedBasicOptimal beta v ρ ell)
    (h' : Theorem4Problem11EqualizedBasicOptimal beta v ρ' ell') :
    ell = ell' := by
  exact theorem4Problem11PolicyOptimal_value_unique h.optimal h'.optimal

theorem theorem4Problem11_item_coverage_of_equalized_policyOptimal
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    {ρ : TypePolicy 3 n} {ell : ℝ}
    (h : Theorem4Problem11EqualizedBasicOptimal beta v ρ ell) :
    ∀ j : Item n,
      ρ 0 j ≠ 0 ∨ ρ 0 (reverseItem j) ≠ 0 ∨ ρ 2 j ≠ 0 := by
  intro j
  by_contra hnone
  push Not at hnone
  have hitem := h.item_eq j
  have hzero :
      theorem4Problem11PolicyItemValue beta v ρ j = 0 := by
    unfold theorem4Problem11PolicyItemValue theorem4Problem11ItemValue
    simp [hnone.1, hnone.2.1, hnone.2.2]
  have hell_pos : 0 < ell :=
    theorem4Problem11PolicyOptimal_value_pos h.optimal
  rw [hzero] at hitem
  linarith

theorem theorem4Problem11_type_item_coverage_of_equalizedBasicOptimal
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    {ρ : TypePolicy 3 n} {ell : ℝ}
    (h : Theorem4Problem11EqualizedBasicOptimal beta v ρ ell) :
    ∀ j : Item n, ∃ k : UserType 3, ρ k j ≠ 0 := by
  intro j
  rcases theorem4Problem11_item_coverage_of_equalized_policyOptimal h j with
    h0 | h0rev | h2
  · exact ⟨0, h0⟩
  · refine ⟨1, ?_⟩
    have hmirror :
        ρ 1 j = ρ 0 (reverseItem j) := by
      simpa [reverseItem_reverseItem] using h.mirror.1 (reverseItem j)
    rwa [hmirror]
  · exact ⟨2, h2⟩

theorem theorem4Problem11_sharedItemsBound_of_equalizedBasicOptimal
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    {ρ : TypePolicy 3 n} {ell : ℝ}
    (h : Theorem4Problem11EqualizedBasicOptimal beta v ρ ell) :
    TypePolicy.SharedItemsBound ρ := by
  have hactive : TypePolicy.ActivePairsBound ρ :=
    TypePolicy.activePairsBound_of_basicFeasibleSupportCertificate
      ρ h.basic_feasible
  exact TypePolicy.sharedItemsBound_of_activePairsBound_of_item_coverage
    ρ hactive
    (theorem4Problem11_type_item_coverage_of_equalizedBasicOptimal h)

def Theorem4Problem11PolicyNoStrictPointwiseImprovement {n : ℕ}
    (beta : ℝ) (v : Item n → ℝ) (ρ : TypePolicy 3 n) : Prop :=
  ¬ ∃ ρ' : TypePolicy 3 n,
    Theorem4MirrorSymmetricPolicy ρ' ∧
      ∀ j : Item n,
        theorem4Problem11PolicyItemValue beta v ρ j <
          theorem4Problem11PolicyItemValue beta v ρ' j

theorem theorem4Problem11_noStrictPointwiseImprovement_of_policyOptimal_equalized
    {n : ℕ} [NeZero n]
    {beta : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 3 n} {ell : ℝ}
    (hitem_eq :
      ∀ l : Item n, theorem4Problem11PolicyItemValue beta v ρ l = ell)
    (hopt : Theorem4Problem11PolicyOptimal beta v ρ ell) :
    Theorem4Problem11PolicyNoStrictPointwiseImprovement beta v ρ := by
  intro himprove
  rcases himprove with ⟨ρ', hsym', hstrict⟩
  let gap : Item n → ℝ :=
    fun j => theorem4Problem11PolicyItemValue beta v ρ' j - ell
  let delta : ℝ := AppliedModelingLib.finiteMin gap
  have hgap_pos : ∀ j : Item n, 0 < gap j := by
    intro j
    dsimp [gap]
    have hbase : theorem4Problem11PolicyItemValue beta v ρ j = ell :=
      hitem_eq j
    have hlt := hstrict j
    rw [hbase] at hlt
    linarith
  have hdelta_pos : 0 < delta := by
    dsimp [delta]
    exact AppliedModelingLib.finiteMin_pos gap hgap_pos
  have hfeas' :
      theorem4Problem11LPFeasible beta v ρ' (ell + delta) := by
    intro j
    have hle := AppliedModelingLib.finiteMin_le gap j
    dsimp [delta, gap] at hle
    linarith
  have hle : ell + delta ≤ ell :=
    hopt.2.2 ρ' (ell + delta) hsym' hfeas'
  linarith

theorem theorem4Problem11_noStrictPointwiseImprovement_of_equalizedBasicOptimal
    {n : ℕ} [NeZero n]
    {beta : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 3 n} {ell : ℝ}
    (h : Theorem4Problem11EqualizedBasicOptimal beta v ρ ell) :
    Theorem4Problem11PolicyNoStrictPointwiseImprovement beta v ρ := by
  exact theorem4Problem11_noStrictPointwiseImprovement_of_policyOptimal_equalized
    h.item_eq h.optimal

/-! ### Appendix E, Lemma 17: no right-half `x` support -/

/--
Lemma 17 perturbation of the Problem 11 known-type row: remove the donor mass
at `j`, move all but `eps` of it to the mirror item, and spread `eps` over the
unaffected coordinates through `r`.
-/
noncomputable def theorem4Problem11RightHalfShiftX {n : ℕ}
    (x r : Item n → ℝ) (j : Item n) (eps : ℝ) : Item n → ℝ :=
  lemma4GapExchangeX x j (reverseItem j) (x j) eps r

theorem theorem4Problem11RightHalfShiftX_donor_eq_zero
    {n : ℕ} {x r : Item n → ℝ} {j : Item n} {eps : ℝ}
    (hne : j ≠ reverseItem j) (hrj : r j = 0) :
    theorem4Problem11RightHalfShiftX x r j eps j = 0 := by
  unfold theorem4Problem11RightHalfShiftX lemma4GapExchangeX
  simp [hne, hrj]

theorem theorem4Problem11RightHalfShiftX_receiver_eq
    {n : ℕ} {x r : Item n → ℝ} {j : Item n} {eps : ℝ}
    (hne : j ≠ reverseItem j) (hrrev : r (reverseItem j) = 0) :
    theorem4Problem11RightHalfShiftX x r j eps (reverseItem j) =
      x (reverseItem j) + (x j - eps) := by
  unfold theorem4Problem11RightHalfShiftX lemma4GapExchangeX
  simp [hne.symm, hrrev]

theorem theorem4Problem11RightHalfShiftX_other_eq
    {n : ℕ} {x r : Item n → ℝ} {j l : Item n} {eps : ℝ}
    (hlj : l ≠ j) (hlrev : l ≠ reverseItem j) :
    theorem4Problem11RightHalfShiftX x r j eps l =
      x l + eps * r l := by
  unfold theorem4Problem11RightHalfShiftX lemma4GapExchangeX
  simp [hlj, hlrev]

theorem theorem4Problem11RightHalfShiftX_sum_eq
    {n : ℕ} {x r : Item n → ℝ} {j : Item n} {eps : ℝ}
    (hrsum : (∑ l : Item n, r l) = 1) :
    (∑ l : Item n, theorem4Problem11RightHalfShiftX x r j eps l) =
      ∑ l : Item n, x l := by
  exact lemma4GapExchangeX_sum_eq x j (reverseItem j) (x j) eps r hrsum

theorem theorem4Problem11RightHalfShiftX_nonneg
    {n : ℕ} {x r : Item n → ℝ} {j : Item n} {eps : ℝ}
    (hx_nonneg : ∀ l : Item n, 0 ≤ x l)
    (hne : j ≠ reverseItem j)
    (hr_nonneg : ∀ l : Item n, 0 ≤ r l)
    (hrj : r j = 0) (hrrev : r (reverseItem j) = 0)
    (heps_pos : 0 < eps) (heps_lt : eps < x j) :
    ∀ l : Item n, 0 ≤ theorem4Problem11RightHalfShiftX x r j eps l := by
  intro l
  by_cases hlj : l = j
  · subst l
    rw [theorem4Problem11RightHalfShiftX_donor_eq_zero hne hrj]
  · by_cases hlrev : l = reverseItem j
    · subst l
      rw [theorem4Problem11RightHalfShiftX_receiver_eq hne hrrev]
      nlinarith [hx_nonneg (reverseItem j), heps_lt]
    · rw [theorem4Problem11RightHalfShiftX_other_eq hlj hlrev]
      exact add_nonneg (hx_nonneg l)
        (mul_nonneg heps_pos.le (hr_nonneg l))

/--
Appendix E, Lemma 17 real-vector perturbation. If a Problem 11 solution gives
positive known-type mass to an item strictly after its mirror, then shifting
that mass left and spreading a tiny amount over the remaining coordinates
strictly improves every Problem 11 item value.
-/
theorem theorem4Problem11_rightHalfShift_exists_strictlyImproves
    {n : ℕ} {beta : ℝ} {v x z : Item n → ℝ} {j : Item n}
    (hn : 2 < n)
    (hbeta_pos : 0 < beta)
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hj_right : (reverseItem j).val < j.val)
    (hx_nonneg : ∀ l : Item n, 0 ≤ x l)
    (hsumx : (∑ l : Item n, x l) = 1)
    (hxj_pos : 0 < x j) :
    ∃ x' : Item n → ℝ,
      (∀ l : Item n, 0 ≤ x' l) ∧
      (∑ l : Item n, x' l) = 1 ∧
      ∀ l : Item n,
        theorem4Problem11ItemValue beta v x z l <
          theorem4Problem11ItemValue beta v x' z l := by
  classical
  let a : Item n := reverseItem j
  have hne : j ≠ a := by
    intro h
    have hval := congrArg Fin.val h
    dsimp [a] at hval
    omega
  have hane : a ≠ j := hne.symm
  have ha_lt_rev : a.val < (reverseItem a).val := by
    simpa [a, reverseItem_reverseItem] using hj_right
  let qa : ℝ := pairShare (1 / 2) v a
  have hqa_half : (1 / 2 : ℝ) < qa := by
    dsimp [qa]
    exact half_lt_pairShare_half_of_val_lt_reverse a hpos hdec ha_lt_rev
  have hqa_lt_one : qa < 1 := by
    dsimp [qa]
    exact pairShare_lt_one a (by norm_num) (by norm_num) hpos
  let cap : ℝ := (2 * qa - 1) * x j
  have hcap_pos : 0 < cap := by
    dsimp [cap]
    nlinarith
  let eps : ℝ := min (x j) cap / 2
  have hmin_pos : 0 < min (x j) cap := lt_min hxj_pos hcap_pos
  have heps_pos : 0 < eps := by
    dsimp [eps]
    nlinarith
  have heps_lt_min : eps < min (x j) cap := by
    dsimp [eps]
    nlinarith
  have heps_lt_xj : eps < x j :=
    lt_of_lt_of_le heps_lt_min (min_le_left _ _)
  have heps_lt_cap : eps < cap :=
    lt_of_lt_of_le heps_lt_min (min_le_right _ _)
  obtain ⟨r, hr_nonneg, hr_pos, hrj, hra, hrsum⟩ :=
    lemma4_redistribution_exists_of_two_lt hn hne
  let x' : Item n → ℝ := theorem4Problem11RightHalfShiftX x r j eps
  have hx'_nonneg : ∀ l : Item n, 0 ≤ x' l := by
    intro l
    exact theorem4Problem11RightHalfShiftX_nonneg
      hx_nonneg hne hr_nonneg hrj hra heps_pos heps_lt_xj l
  have hx'_sum : (∑ l : Item n, x' l) = 1 := by
    dsimp [x']
    rw [theorem4Problem11RightHalfShiftX_sum_eq hrsum, hsumx]
  refine ⟨x', hx'_nonneg, hx'_sum, ?_⟩
  intro l
  have hq_pos : 0 < pairShare (1 / 2) v l :=
    pairShare_pos l (by norm_num) (by norm_num) hpos
  have hq_lt_one : pairShare (1 / 2) v l < 1 :=
    pairShare_lt_one l (by norm_num) (by norm_num) hpos
  unfold theorem4Problem11ItemValue
  by_cases hlj : l = j
  · subst l
    have hxj' : x' j = 0 := by
      dsimp [x']
      exact theorem4Problem11RightHalfShiftX_donor_eq_zero hne hrj
    have hxa' : x' a = x a + (x j - eps) := by
      dsimp [x']
      exact theorem4Problem11RightHalfShiftX_receiver_eq hne hra
    have hshare :
        pairShare (1 / 2) v j = 1 - qa := by
      dsimp [qa, a]
      rw [pairShare_half_eq_one_sub_reverse j hpos]
    dsimp [a] at *
    rw [hxj', hxa', hshare]
    have heps_small : qa * eps < cap := by
      have hqa_pos : 0 < qa := lt_trans (by norm_num) hqa_half
      have hqa_le_one : qa ≤ 1 := hqa_lt_one.le
      have hmul_le : qa * eps ≤ eps := by nlinarith
      exact lt_of_le_of_lt hmul_le heps_lt_cap
    dsimp [cap] at heps_small
    nlinarith
  · by_cases hla : l = a
    · subst l
      have hxj' : x' j = 0 := by
        dsimp [x']
        exact theorem4Problem11RightHalfShiftX_donor_eq_zero hne hrj
      have hxa' : x' a = x a + (x j - eps) := by
        dsimp [x']
        exact theorem4Problem11RightHalfShiftX_receiver_eq hne hra
      have hrev_a : reverseItem a = j := by
        dsimp [a]
        rw [reverseItem_reverseItem]
      rw [hxa', hrev_a, hxj']
      have heps_small : qa * eps < cap := by
        have hqa_pos : 0 < qa := lt_trans (by norm_num) hqa_half
        have hqa_le_one : qa ≤ 1 := hqa_lt_one.le
        have hmul_le : qa * eps ≤ eps := by nlinarith
        exact lt_of_le_of_lt hmul_le heps_lt_cap
      dsimp [qa, cap] at *
      nlinarith
    · have hlrev_ne_j : reverseItem l ≠ j := by
        intro h
        apply hla
        calc
          l = reverseItem j := by
            rw [← h, reverseItem_reverseItem]
          _ = a := rfl
      have hlrev_ne_a : reverseItem l ≠ a := by
        intro h
        apply hlj
        calc
          l = reverseItem a := by
            rw [← h, reverseItem_reverseItem]
          _ = j := by
            dsimp [a]
            rw [reverseItem_reverseItem]
      have hxl' : x' l = x l + eps * r l := by
        dsimp [x']
        exact theorem4Problem11RightHalfShiftX_other_eq hlj hla
      have hxrev' :
          x' (reverseItem l) =
            x (reverseItem l) + eps * r (reverseItem l) := by
        dsimp [x']
        exact theorem4Problem11RightHalfShiftX_other_eq hlrev_ne_j hlrev_ne_a
      rw [hxl', hxrev']
      have hrl_pos : 0 < r l := hr_pos hlj hla
      have hrrev_pos : 0 < r (reverseItem l) :=
        hr_pos hlrev_ne_j hlrev_ne_a
      have hleft_pos :
          0 < pairShare (1 / 2) v l * (eps * r l) :=
        mul_pos hq_pos (mul_pos heps_pos hrl_pos)
      have hright_pos :
          0 < (1 - pairShare (1 / 2) v l) *
            (eps * r (reverseItem l)) :=
        mul_pos (sub_pos.mpr hq_lt_one) (mul_pos heps_pos hrrev_pos)
      nlinarith

theorem theorem4Problem11_typeZero_zero_after_mirror_of_noStrictPointwiseImprovement
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    {ρ : TypePolicy 3 n}
    (hn : 2 < n)
    (hbeta_pos : 0 < beta)
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hsym : Theorem4MirrorSymmetricPolicy ρ)
    (hno : Theorem4Problem11PolicyNoStrictPointwiseImprovement beta v ρ) :
    ∀ j : Item n, (reverseItem j).val < j.val → ρ 0 j = 0 := by
  intro j hj_right
  by_contra hρj_ne
  let x : Item n → ℝ := fun l => (ρ 0 l).toReal
  let z : Item n → ℝ := fun l => (ρ 2 l).toReal
  have hx_nonneg : ∀ l : Item n, 0 ≤ x l := by
    intro l
    exact ENNReal.toReal_nonneg
  have hsumx : (∑ l : Item n, x l) = 1 := by
    dsimp [x]
    exact AppliedModelingLib.pmfToRealSum (ρ 0)
  have hxj_pos : 0 < x j := by
    have htoReal_ne : (ρ 0 j).toReal ≠ 0 := by
      intro hzero
      rcases (ENNReal.toReal_eq_zero_iff (ρ 0 j)).mp hzero with hzero_enn | htop
      · exact hρj_ne hzero_enn
      · exact (ρ 0).apply_ne_top j htop
    exact lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm htoReal_ne)
  obtain ⟨x', hx'_nonneg, hx'_sum, hstrict⟩ :=
    theorem4Problem11_rightHalfShift_exists_strictlyImproves
      hn hbeta_pos hpos hdec hj_right hx_nonneg hsumx hxj_pos
      (z := z)
  let y' : Item n → ℝ := fun l => x' (reverseItem l)
  have hy'_nonneg : ∀ l : Item n, 0 ≤ y' l := by
    intro l
    exact hx'_nonneg (reverseItem l)
  have hy'_sum : (∑ l : Item n, y' l) = 1 := by
    dsimp [y']
    rw [sum_reverseItem x', hx'_sum]
  let ρ' : TypePolicy 3 n := fun k =>
    if k = 0 then
      pmfOfRealVector x' hx'_nonneg hx'_sum
    else if k = 1 then
      pmfOfRealVector y' hy'_nonneg hy'_sum
    else
      ρ 2
  have hsym' : Theorem4MirrorSymmetricPolicy ρ' := by
    constructor
    · intro l
      apply (ENNReal.toReal_eq_toReal_iff'
        ((ρ' 1).apply_ne_top (reverseItem l))
        ((ρ' 0).apply_ne_top l)).mp
      simp [ρ', y', reverseItem_reverseItem]
    · intro l
      have h := hsym.2 l
      simpa [ρ'] using h
  apply hno
  refine ⟨ρ', hsym', ?_⟩
  intro l
  unfold theorem4Problem11PolicyItemValue
  simpa [theorem4Problem11ItemValue, x, z, ρ'] using hstrict l

/-- Problem 11 no-gap condition for the known-type row `x`. -/
def Theorem4Problem11TypeZeroZeroClosed {n : ℕ}
    (ρ : TypePolicy 3 n) : Prop :=
  ∀ {j i : Item n}, j.val < i.val → ρ 0 j = 0 → ρ 0 i = 0

/--
Problem 11 no-gap condition for the cold-start row on the half-problem:
once `z_i` is positive, all later half-side `z_j` are positive.
-/
def Theorem4Problem11ColdStartPositiveClosed {n : ℕ}
    (ρ : TypePolicy 3 n) : Prop :=
  ∀ {i j : Item n}, i.val < j.val → j.val ≤ (reverseItem j).val →
    ρ 2 i ≠ 0 → ρ 2 j ≠ 0

/--
Exact Appendix E Lemma 13 perturbation certificate for an `x` support gap:
an earlier zero and a later positive known-type coordinate yield a
mirror-symmetric policy that strictly improves every Problem 11 item value.
-/
def Theorem4Problem11TypeZeroGapStrictImprovement {n : ℕ}
    (beta : ℝ) (v : Item n → ℝ) (ρ : TypePolicy 3 n) : Prop :=
  ∀ {i j : Item n}, i.val < j.val → ρ 0 i = 0 → ρ 0 j ≠ 0 →
    ∃ ρ' : TypePolicy 3 n,
      Theorem4MirrorSymmetricPolicy ρ' ∧
        ∀ l : Item n,
          theorem4Problem11PolicyItemValue beta v ρ l <
            theorem4Problem11PolicyItemValue beta v ρ' l

/--
Exact Appendix E Lemma 13 perturbation certificate for a `z` support gap:
an earlier positive and a later zero cold-start coordinate yield a
mirror-symmetric policy that strictly improves every Problem 11 item value.
-/
def Theorem4Problem11ColdStartGapStrictImprovement {n : ℕ}
    (beta : ℝ) (v : Item n → ℝ) (ρ : TypePolicy 3 n) : Prop :=
  ∀ {i j : Item n}, i.val < j.val → j.val ≤ (reverseItem j).val →
    ρ 2 i ≠ 0 → ρ 2 j = 0 →
    ∃ ρ' : TypePolicy 3 n,
      Theorem4MirrorSymmetricPolicy ρ' ∧
        ∀ l : Item n,
          theorem4Problem11PolicyItemValue beta v ρ l <
            theorem4Problem11PolicyItemValue beta v ρ' l

/--
The mirror-pair swap used in Appendix E, Lemma 13 perturbations.  It exchanges
the half-side coordinates `i` and `j` and simultaneously exchanges their mirror
coordinates, preserving the cold-start row sum by reindexing.
-/
noncomputable def theorem4Problem11MirrorPairSwap {n : ℕ}
    (i j : Item n) : Equiv.Perm (Item n) :=
  (Equiv.swap i j).trans (Equiv.swap (reverseItem i) (reverseItem j))

theorem theorem4Problem11MirrorPairSwap_sum_eq {n : ℕ}
    (z : Item n → ℝ) (i j : Item n) :
    (∑ l : Item n, z (theorem4Problem11MirrorPairSwap i j l)) =
      ∑ l : Item n, z l := by
  exact Equiv.sum_comp (theorem4Problem11MirrorPairSwap i j) z

theorem theorem4Problem11MirrorPairSwap_apply_left
    {n : ℕ} {i j : Item n}
    (hj_revi : j ≠ reverseItem i)
    (hj_revj : j ≠ reverseItem j) :
    theorem4Problem11MirrorPairSwap i j i = j := by
  unfold theorem4Problem11MirrorPairSwap
  rw [Equiv.trans_apply, Equiv.swap_apply_left]
  exact Equiv.swap_apply_of_ne_of_ne hj_revi hj_revj

theorem theorem4Problem11MirrorPairSwap_apply_right
    {n : ℕ} {i j : Item n}
    (hij : i ≠ j)
    (hi_revi : i ≠ reverseItem i)
    (hi_revj : i ≠ reverseItem j) :
    theorem4Problem11MirrorPairSwap i j j = i := by
  unfold theorem4Problem11MirrorPairSwap
  rw [Equiv.trans_apply, Equiv.swap_apply_right]
  exact Equiv.swap_apply_of_ne_of_ne hi_revi hi_revj

theorem theorem4Problem11MirrorPairSwap_apply_reverse_left
    {n : ℕ} {i j : Item n}
    (hrevi_i : reverseItem i ≠ i)
    (hrevi_j : reverseItem i ≠ j) :
    theorem4Problem11MirrorPairSwap i j (reverseItem i) = reverseItem j := by
  unfold theorem4Problem11MirrorPairSwap
  rw [Equiv.trans_apply]
  rw [Equiv.swap_apply_of_ne_of_ne hrevi_i hrevi_j]
  exact Equiv.swap_apply_left (reverseItem i) (reverseItem j)

theorem theorem4Problem11MirrorPairSwap_apply_reverse_right
    {n : ℕ} {i j : Item n}
    (hrevj_i : reverseItem j ≠ i)
    (hrevj_j : reverseItem j ≠ j) :
    theorem4Problem11MirrorPairSwap i j (reverseItem j) = reverseItem i := by
  unfold theorem4Problem11MirrorPairSwap
  rw [Equiv.trans_apply]
  rw [Equiv.swap_apply_of_ne_of_ne hrevj_i hrevj_j]
  exact Equiv.swap_apply_right (reverseItem i) (reverseItem j)

theorem theorem4Problem11MirrorPairSwap_apply_of_distinct
    {n : ℕ} {i j l : Item n}
    (hli : l ≠ i) (hlj : l ≠ j)
    (hlrevi : l ≠ reverseItem i) (hlrevj : l ≠ reverseItem j) :
    theorem4Problem11MirrorPairSwap i j l = l := by
  unfold theorem4Problem11MirrorPairSwap
  rw [Equiv.trans_apply]
  rw [Equiv.swap_apply_of_ne_of_ne hli hlj]
  exact Equiv.swap_apply_of_ne_of_ne hlrevi hlrevj

theorem theorem4Problem11MirrorPairSwap_preserves_mirror_value
    {n : ℕ} {z : Item n → ℝ} {i j l : Item n}
    (hzmirror : ∀ u : Item n, z (reverseItem u) = z u)
    (hij : i ≠ j)
    (hi_revi : i ≠ reverseItem i)
    (hj_revj : j ≠ reverseItem j)
    (hi_revj : i ≠ reverseItem j)
    (hj_revi : j ≠ reverseItem i) :
    z (theorem4Problem11MirrorPairSwap i j (reverseItem l)) =
      z (theorem4Problem11MirrorPairSwap i j l) := by
  classical
  by_cases hli : l = i
  · subst l
    rw [theorem4Problem11MirrorPairSwap_apply_reverse_left
      hi_revi.symm hj_revi.symm]
    rw [theorem4Problem11MirrorPairSwap_apply_left hj_revi hj_revj]
    exact hzmirror j
  · by_cases hlj : l = j
    · subst l
      rw [theorem4Problem11MirrorPairSwap_apply_reverse_right
        hi_revj.symm hj_revj.symm]
      rw [theorem4Problem11MirrorPairSwap_apply_right hij hi_revi hi_revj]
      exact hzmirror i
    · by_cases hlrevi : l = reverseItem i
      · subst l
        rw [reverseItem_reverseItem]
        rw [theorem4Problem11MirrorPairSwap_apply_left hj_revi hj_revj]
        rw [theorem4Problem11MirrorPairSwap_apply_reverse_left
          hi_revi.symm hj_revi.symm]
        exact (hzmirror j).symm
      · by_cases hlrevj : l = reverseItem j
        · subst l
          rw [reverseItem_reverseItem]
          rw [theorem4Problem11MirrorPairSwap_apply_right hij hi_revi hi_revj]
          rw [theorem4Problem11MirrorPairSwap_apply_reverse_right
            hi_revj.symm hj_revj.symm]
          exact (hzmirror i).symm
        · have hrev_li : reverseItem l ≠ i := by
            intro h
            apply hlrevi
            calc
              l = reverseItem i := by
                rw [← h, reverseItem_reverseItem]
              _ = reverseItem i := rfl
          have hrev_lj : reverseItem l ≠ j := by
            intro h
            apply hlrevj
            calc
              l = reverseItem j := by
                rw [← h, reverseItem_reverseItem]
              _ = reverseItem j := rfl
          have hrev_lrevi : reverseItem l ≠ reverseItem i := by
            intro h
            apply hli
            calc
              l = reverseItem (reverseItem l) := by
                rw [reverseItem_reverseItem]
              _ = reverseItem (reverseItem i) := by
                rw [h]
              _ = i := by
                rw [reverseItem_reverseItem]
              _ = i := rfl
          have hrev_lrevj : reverseItem l ≠ reverseItem j := by
            intro h
            apply hlj
            calc
              l = reverseItem (reverseItem l) := by
                rw [reverseItem_reverseItem]
              _ = reverseItem (reverseItem j) := by
                rw [h]
              _ = j := by
                rw [reverseItem_reverseItem]
              _ = j := rfl
          rw [theorem4Problem11MirrorPairSwap_apply_of_distinct
            hrev_li hrev_lj hrev_lrevi hrev_lrevj]
          rw [theorem4Problem11MirrorPairSwap_apply_of_distinct
            hli hlj hlrevi hlrevj]
          exact hzmirror l

/-- Cold-start row after the Lemma 13 mirror-pair swap. -/
noncomputable def theorem4Problem11MirrorPairSwapVector {n : ℕ}
    (z : Item n → ℝ) (i j : Item n) : Item n → ℝ :=
  fun l => z (theorem4Problem11MirrorPairSwap i j l)

theorem theorem4Problem11MirrorPairSwapVector_nonneg {n : ℕ}
    {z : Item n → ℝ} {i j : Item n}
    (hz_nonneg : ∀ l : Item n, 0 ≤ z l) :
    ∀ l : Item n, 0 ≤ theorem4Problem11MirrorPairSwapVector z i j l := by
  intro l
  exact hz_nonneg (theorem4Problem11MirrorPairSwap i j l)

theorem theorem4Problem11MirrorPairSwapVector_sum_eq {n : ℕ}
    (z : Item n → ℝ) (i j : Item n) :
    (∑ l : Item n, theorem4Problem11MirrorPairSwapVector z i j l) =
      ∑ l : Item n, z l := by
  unfold theorem4Problem11MirrorPairSwapVector
  exact theorem4Problem11MirrorPairSwap_sum_eq z i j

theorem theorem4Problem11MirrorPairSwapVector_mirror
    {n : ℕ} {z : Item n → ℝ} {i j : Item n}
    (hzmirror : ∀ u : Item n, z (reverseItem u) = z u)
    (hij : i ≠ j)
    (hi_revi : i ≠ reverseItem i)
    (hj_revj : j ≠ reverseItem j)
    (hi_revj : i ≠ reverseItem j)
    (hj_revi : j ≠ reverseItem i) :
    ∀ l : Item n,
      theorem4Problem11MirrorPairSwapVector z i j (reverseItem l) =
        theorem4Problem11MirrorPairSwapVector z i j l := by
  intro l
  unfold theorem4Problem11MirrorPairSwapVector
  exact theorem4Problem11MirrorPairSwap_preserves_mirror_value
    hzmirror hij hi_revi hj_revj hi_revj hj_revi

/-- Transfer `delta` of known-type mass from `j` to `i`. -/
noncomputable def theorem4Problem11TwoPointXTransfer {n : ℕ}
    (x : Item n → ℝ) (i j : Item n) (delta : ℝ) : Item n → ℝ :=
  fun l => x l + (if l = i then delta else 0) +
    (if l = j then -delta else 0)

theorem theorem4Problem11TwoPointXTransfer_sum_eq {n : ℕ}
    (x : Item n → ℝ) (i j : Item n) (delta : ℝ) :
    (∑ l : Item n, theorem4Problem11TwoPointXTransfer x i j delta l) =
      ∑ l : Item n, x l := by
  unfold theorem4Problem11TwoPointXTransfer
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp

theorem theorem4Problem11TwoPointXTransfer_nonneg {n : ℕ}
    {x : Item n → ℝ} {i j : Item n} {delta : ℝ}
    (hx_nonneg : ∀ l : Item n, 0 ≤ x l)
    (hij : i ≠ j)
    (hdelta_nonneg : 0 ≤ delta)
    (hdelta_le : delta ≤ x j) :
    ∀ l : Item n, 0 ≤ theorem4Problem11TwoPointXTransfer x i j delta l := by
  intro l
  unfold theorem4Problem11TwoPointXTransfer
  by_cases hli : l = i
  · subst l
    simp [hij, add_nonneg (hx_nonneg i) hdelta_nonneg]
  · by_cases hlj : l = j
    · subst l
      simp [hij.symm, hdelta_le]
    · simpa [hli, hlj] using hx_nonneg l

theorem theorem4Problem11TwoPointXTransfer_apply_of_ne {n : ℕ}
    {x : Item n → ℝ} {i j l : Item n} {delta : ℝ}
    (hli : l ≠ i)
    (hlj : l ≠ j) :
    theorem4Problem11TwoPointXTransfer x i j delta l = x l := by
  unfold theorem4Problem11TwoPointXTransfer
  rw [if_neg hli, if_neg hlj]
  ring

theorem theorem4Problem11_symmetricRedistribution_pos {n : ℕ}
    {r : Item n → ℝ} {eps : ℝ} {l : Item n}
    (heps_pos : 0 < eps)
    (hrl_pos : 0 < r l)
    (hrrev_nonneg : 0 ≤ r (reverseItem l)) :
    0 < eps * r l + eps * r (reverseItem l) := by
  have hleft_pos : 0 < eps * r l := mul_pos heps_pos hrl_pos
  have hright_nonneg : 0 ≤ eps * r (reverseItem l) :=
    mul_nonneg heps_pos.le hrrev_nonneg
  exact add_pos_of_pos_of_nonneg hleft_pos hright_nonneg

/--
Cold-start-row transfer for the non-center part of Appendix E, Lemma 13:
move `d` symmetrically from the earlier mirror pair to the later mirror pair,
then reserve `eps` of that moved mass for a symmetric redistribution `r`.
-/
noncomputable def theorem4Problem11ColdStartPairZTransfer {n : ℕ}
    (z r : Item n → ℝ) (i j : Item n) (d eps : ℝ) : Item n → ℝ :=
  fun l =>
    z l +
      (if l = i then -d else 0) +
      (if l = reverseItem i then -d else 0) +
      (if l = j then d - eps else 0) +
      (if l = reverseItem j then d - eps else 0) +
      eps * r l + eps * r (reverseItem l)

theorem theorem4Problem11ColdStartPairZTransfer_apply_of_ne {n : ℕ}
    {z r : Item n → ℝ} {i j l : Item n} {d eps : ℝ}
    (hli : l ≠ i)
    (hlrevi : l ≠ reverseItem i)
    (hlj : l ≠ j)
    (hlrevj : l ≠ reverseItem j) :
    theorem4Problem11ColdStartPairZTransfer z r i j d eps l =
      z l + eps * r l + eps * r (reverseItem l) := by
  unfold theorem4Problem11ColdStartPairZTransfer
  rw [if_neg hli, if_neg hlrevi, if_neg hlj, if_neg hlrevj]
  ring

theorem theorem4Problem11ColdStartPairZTransfer_sum_eq {n : ℕ}
    (z r : Item n → ℝ) (i j : Item n) (d eps : ℝ)
    (hrsum : (∑ l : Item n, r l) = 1) :
    (∑ l : Item n,
        theorem4Problem11ColdStartPairZTransfer z r i j d eps l) =
      ∑ l : Item n, z l := by
  unfold theorem4Problem11ColdStartPairZTransfer
  repeat rw [Finset.sum_add_distrib]
  rw [← Finset.mul_sum, ← Finset.mul_sum, sum_reverseItem r, hrsum]
  simp
  ring

set_option linter.unusedSimpArgs false in
theorem theorem4Problem11ColdStartPairZTransfer_mirror {n : ℕ}
    {z r : Item n → ℝ} {i j : Item n} {d eps : ℝ}
    (hzmirror : ∀ l : Item n, z (reverseItem l) = z l)
    (hi_revi : i ≠ reverseItem i)
    (hj_revj : j ≠ reverseItem j)
    (hij : i ≠ j)
    (hi_revj : i ≠ reverseItem j)
    (hj_revi : j ≠ reverseItem i) :
    ∀ l : Item n,
      theorem4Problem11ColdStartPairZTransfer z r i j d eps
          (reverseItem l) =
        theorem4Problem11ColdStartPairZTransfer z r i j d eps l := by
  intro l
  unfold theorem4Problem11ColdStartPairZTransfer
  have hrevi_revj : reverseItem i ≠ reverseItem j := by
    intro h
    apply hij
    calc
      i = reverseItem (reverseItem i) := by rw [reverseItem_reverseItem]
      _ = reverseItem (reverseItem j) := by rw [h]
      _ = j := by rw [reverseItem_reverseItem]
  have hrevj_revi : reverseItem j ≠ reverseItem i := hrevi_revj.symm
  by_cases hli : l = i
  · subst l
    simp [reverseItem_reverseItem, hi_revi, hi_revi.symm, hij, hij.symm,
      hi_revj, hi_revj.symm, hj_revi, hj_revi.symm, hj_revj,
      hj_revj.symm, hrevi_revj, hrevj_revi, hzmirror i]
    ring_nf
  · by_cases hlrevi : l = reverseItem i
    · subst l
      simp [reverseItem_reverseItem, hi_revi, hi_revi.symm, hij, hij.symm,
        hi_revj, hi_revj.symm, hj_revi, hj_revi.symm, hj_revj,
        hj_revj.symm, hrevi_revj, hrevj_revi, hzmirror i]
      ring_nf
    · by_cases hlj : l = j
      · subst l
        simp [reverseItem_reverseItem, hi_revi, hi_revi.symm, hij,
          hij.symm, hi_revj, hi_revj.symm, hj_revi, hj_revi.symm,
          hj_revj, hj_revj.symm, hrevi_revj, hrevj_revi, hzmirror j]
        ring_nf
      · by_cases hlrevj : l = reverseItem j
        · subst l
          simp [reverseItem_reverseItem, hi_revi, hi_revi.symm, hij,
            hij.symm, hi_revj, hi_revj.symm, hj_revi, hj_revi.symm,
            hj_revj, hj_revj.symm, hrevi_revj, hrevj_revi, hzmirror j]
          ring_nf
        · have hrev_li : reverseItem l ≠ i := by
            intro h
            apply hlrevi
            calc
              l = reverseItem (reverseItem l) := by
                rw [reverseItem_reverseItem]
              _ = reverseItem i := by rw [h]
          have hrev_lrevi : reverseItem l ≠ reverseItem i := by
            intro h
            apply hli
            calc
              l = reverseItem (reverseItem l) := by
                rw [reverseItem_reverseItem]
              _ = reverseItem (reverseItem i) := by rw [h]
              _ = i := by rw [reverseItem_reverseItem]
          have hrev_lj : reverseItem l ≠ j := by
            intro h
            apply hlrevj
            calc
              l = reverseItem (reverseItem l) := by
                rw [reverseItem_reverseItem]
              _ = reverseItem j := by rw [h]
          have hrev_lrevj : reverseItem l ≠ reverseItem j := by
            intro h
            apply hlj
            calc
              l = reverseItem (reverseItem l) := by
                rw [reverseItem_reverseItem]
              _ = reverseItem (reverseItem j) := by rw [h]
              _ = j := by rw [reverseItem_reverseItem]
          simp [reverseItem_reverseItem, hli, hlrevi, hlj, hlrevj, hrev_li,
            hrev_lrevi, hrev_lj, hrev_lrevj, hzmirror l]
          ring_nf

set_option maxHeartbeats 800000 in
-- This certificate has a large case split over the four touched mirror coordinates.
theorem theorem4Problem11_coldStartGap_pairTransfer_exists_strictlyImproves
    {n : ℕ} {beta : ℝ} {v x z : Item n → ℝ} {i j : Item n}
    (hn : 2 < n)
    (hbeta_pos : 0 < beta)
    (hbeta_half : beta < 1 / 2)
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hij : i.val < j.val)
    (hj_left : j.val < (reverseItem j).val)
    (hx_nonneg : ∀ l : Item n, 0 ≤ x l)
    (hz_nonneg : ∀ l : Item n, 0 ≤ z l)
    (hsumx : (∑ l : Item n, x l) = 1)
    (hsumz : (∑ l : Item n, z l) = 1)
    (hzmirror : ∀ l : Item n, z (reverseItem l) = z l)
    (hzi_pos : 0 < z i)
    (hzj : z j = 0)
    (hxj_pos : 0 < x j)
    (hxrevi : x (reverseItem i) = 0)
    (hxrevj : x (reverseItem j) = 0) :
    ∃ x' z' : Item n → ℝ,
      (∀ l : Item n, 0 ≤ x' l) ∧
      (∀ l : Item n, 0 ≤ z' l) ∧
      (∑ l : Item n, x' l) = 1 ∧
      (∑ l : Item n, z' l) = 1 ∧
      (∀ l : Item n, z' (reverseItem l) = z' l) ∧
      ∀ l : Item n,
        theorem4Problem11ItemValue beta v x z l <
          theorem4Problem11ItemValue beta v x' z' l := by
  classical
  let cold : ℝ := 1 - 2 * beta
  have hcold_pos : 0 < cold := by
    dsimp [cold]
    nlinarith
  have hi_left : i.val < (reverseItem i).val := by
    have hrev_lt : (reverseItem j).val < (reverseItem i).val :=
      reverseItem_val_lt_of_val_lt hij
    exact lt_trans (lt_trans hij hj_left) hrev_lt
  have hji_ne : j ≠ i := by
    intro h
    subst j
    omega
  have hij_ne : i ≠ j := hji_ne.symm
  have hi_revi : i ≠ reverseItem i := by
    intro h
    have hval := congrArg Fin.val h
    omega
  have hj_revj : j ≠ reverseItem j := by
    intro h
    have hval := congrArg Fin.val h
    omega
  have hi_revj : i ≠ reverseItem j := by
    intro h
    have hji : j.val < i.val := by
      calc
        j.val < (reverseItem j).val := hj_left
        _ = i.val := by exact congrArg Fin.val h.symm
    omega
  have hj_revi : j ≠ reverseItem i := by
    intro h
    have hji : j.val < i.val := by
      calc
        j.val < (reverseItem j).val := hj_left
        _ = i.val := by
          rw [h, reverseItem_reverseItem]
    omega
  have hrevi_j : reverseItem i ≠ j := hj_revi.symm
  have hrevj_i : reverseItem j ≠ i := hi_revj.symm
  have hrevi_revj : reverseItem i ≠ reverseItem j := by
    intro h
    apply hij_ne
    calc
      i = reverseItem (reverseItem i) := by rw [reverseItem_reverseItem]
      _ = reverseItem (reverseItem j) := by rw [h]
      _ = j := by rw [reverseItem_reverseItem]
  have hrevj_revi : reverseItem j ≠ reverseItem i := hrevi_revj.symm
  let qi : ℝ := pairShare (1 / 2) v i
  let qj : ℝ := pairShare (1 / 2) v j
  have hqj_lt_qi : qj < qi := by
    dsimp [qi, qj]
    exact pairShare_strictAnti_index (by norm_num) (by norm_num)
      hpos hdec hij
  have hqi_pos : 0 < qi := by
    dsimp [qi]
    exact pairShare_pos i (by norm_num) (by norm_num) hpos
  have hqj_pos : 0 < qj := by
    dsimp [qj]
    exact pairShare_pos j (by norm_num) (by norm_num) hpos
  have hqj_lt_one : qj < 1 := by
    dsimp [qj]
    exact pairShare_lt_one j (by norm_num) (by norm_num) hpos
  let deltaBound : ℝ := cold * z i / (4 * beta * qi)
  have hdeltaDen_pos : 0 < 4 * beta * qi := by
    nlinarith
  have hdeltaBound_pos : 0 < deltaBound := by
    dsimp [deltaBound]
    exact div_pos (mul_pos hcold_pos hzi_pos) hdeltaDen_pos
  let delta : ℝ := min (x j) deltaBound / 2
  have hmin_delta_pos : 0 < min (x j) deltaBound :=
    lt_min hxj_pos hdeltaBound_pos
  have hdelta_pos : 0 < delta := by
    dsimp [delta]
    nlinarith
  have hdelta_lt_min : delta < min (x j) deltaBound := by
    dsimp [delta]
    nlinarith
  have hdelta_lt_xj : delta < x j :=
    lt_of_lt_of_le hdelta_lt_min (min_le_left _ _)
  have hdelta_lt_bound : delta < deltaBound :=
    lt_of_lt_of_le hdelta_lt_min (min_le_right _ _)
  have hupper_lt_zi :
      2 * beta * qi * delta / cold < z i := by
    have hmul : 2 * beta * qi * delta < cold * z i := by
      have := hdelta_lt_bound
      dsimp [deltaBound] at this
      rw [lt_div_iff₀ hdeltaDen_pos] at this
      nlinarith
    rw [div_lt_iff₀ hcold_pos]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  let lower : ℝ := 2 * beta * qj * delta / cold
  let upper : ℝ := 2 * beta * qi * delta / cold
  have hlower_lt_upper : lower < upper := by
    have hfactor_pos : 0 < 2 * beta * delta / cold := by
      exact div_pos (by nlinarith) hcold_pos
    calc
      lower = qj * (2 * beta * delta / cold) := by
        dsimp [lower]
        ring
      _ < qi * (2 * beta * delta / cold) :=
        mul_lt_mul_of_pos_right hqj_lt_qi hfactor_pos
      _ = upper := by
        dsimp [upper]
        ring
  obtain ⟨d, hd_lower, hd_upper⟩ := exists_between hlower_lt_upper
  have hlower_pos : 0 < lower := by
    dsimp [lower]
    have htwo_beta_pos : 0 < 2 * beta := by nlinarith
    exact div_pos
      (mul_pos (mul_pos htwo_beta_pos hqj_pos) hdelta_pos) hcold_pos
  have hd_pos : 0 < d := lt_trans hlower_pos hd_lower
  have hd_nonneg : 0 ≤ d := hd_pos.le
  have hd_lt_zi : d < z i := lt_trans hd_upper hupper_lt_zi
  let slack : ℝ := d - lower
  have hslack_pos : 0 < slack := by
    dsimp [slack]
    linarith
  let eps : ℝ := min d slack / 2
  have hmin_eps_pos : 0 < min d slack := lt_min hd_pos hslack_pos
  have heps_pos : 0 < eps := by
    dsimp [eps]
    nlinarith
  have heps_lt_min : eps < min d slack := by
    dsimp [eps]
    nlinarith
  have heps_lt_d : eps < d :=
    lt_of_lt_of_le heps_lt_min (min_le_left _ _)
  have heps_lt_slack : eps < slack :=
    lt_of_lt_of_le heps_lt_min (min_le_right _ _)
  obtain ⟨r, hr_nonneg, hr_pos, hrj, hrrevj, hrsum⟩ :=
    lemma4_redistribution_exists_of_two_lt hn hj_revj
  let x' : Item n → ℝ :=
    theorem4Problem11TwoPointXTransfer x i j delta
  let z' : Item n → ℝ :=
    theorem4Problem11ColdStartPairZTransfer z r i j d eps
  have hx'_nonneg : ∀ l : Item n, 0 ≤ x' l := by
    intro l
    exact theorem4Problem11TwoPointXTransfer_nonneg
      hx_nonneg hij_ne hdelta_pos.le hdelta_lt_xj.le l
  have hz'_sum : (∑ l : Item n, z' l) = 1 := by
    dsimp [z']
    rw [theorem4Problem11ColdStartPairZTransfer_sum_eq
      z r i j d eps hrsum, hsumz]
  have hx'_sum : (∑ l : Item n, x' l) = 1 := by
    dsimp [x']
    rw [theorem4Problem11TwoPointXTransfer_sum_eq x i j delta, hsumx]
  have hz'_mirror : ∀ l : Item n, z' (reverseItem l) = z' l := by
    dsimp [z']
    exact theorem4Problem11ColdStartPairZTransfer_mirror
      hzmirror hi_revi hj_revj hij_ne hi_revj hj_revi
  have hzrevj : z (reverseItem j) = 0 := by
    rw [hzmirror j, hzj]
  have hz'_nonneg : ∀ l : Item n, 0 ≤ z' l := by
    intro l
    dsimp [z']
    unfold theorem4Problem11ColdStartPairZTransfer
    by_cases hli : l = i
    · subst l
      have hredistrib_nonneg :
          0 ≤ eps * r i + eps * r (reverseItem i) := by
        exact add_nonneg
          (mul_nonneg heps_pos.le (hr_nonneg i))
          (mul_nonneg heps_pos.le (hr_nonneg (reverseItem i)))
      simp [hi_revi, hij_ne, hi_revj]
      nlinarith [hd_lt_zi.le, hredistrib_nonneg]
    · by_cases hlrevi : l = reverseItem i
      · subst l
        have hredistrib_nonneg :
            0 ≤ eps * r (reverseItem i) + eps * r i := by
          exact add_nonneg
            (mul_nonneg heps_pos.le (hr_nonneg (reverseItem i)))
            (mul_nonneg heps_pos.le (hr_nonneg i))
        simp [reverseItem_reverseItem, hi_revi.symm, hrevi_j,
          hrevi_revj]
        rw [hzmirror i]
        nlinarith [hd_lt_zi.le, hredistrib_nonneg]
      · by_cases hlj : l = j
        · subst l
          simp [hzj, hj_revj, hij_ne.symm, hj_revi, hrj, hrrevj]
          exact heps_lt_d.le
        · by_cases hlrevj : l = reverseItem j
          · subst l
            simp [reverseItem_reverseItem, hzrevj, hj_revj.symm,
              hrevj_i, hrevj_revi, hrj, hrrevj]
            exact heps_lt_d.le
          · have hredistrib_nonneg :
                0 ≤ eps * r l + eps * r (reverseItem l) := by
              exact add_nonneg
                (mul_nonneg heps_pos.le (hr_nonneg l))
                (mul_nonneg heps_pos.le (hr_nonneg (reverseItem l)))
            simpa [hli, hlrevi, hlj, hlrevj, add_assoc] using
              add_nonneg (hz_nonneg l) hredistrib_nonneg
  have hx'i : x' i = x i + delta := by
    dsimp [x']
    unfold theorem4Problem11TwoPointXTransfer
    simp [hij_ne]
  have hx'j : x' j = x j - delta := by
    dsimp [x']
    unfold theorem4Problem11TwoPointXTransfer
    simp [hij_ne.symm]
    ring
  have hx'revi : x' (reverseItem i) = 0 := by
    dsimp [x']
    unfold theorem4Problem11TwoPointXTransfer
    simp [hxrevi, hi_revi.symm, hrevi_j]
  have hx'revj : x' (reverseItem j) = 0 := by
    dsimp [x']
    unfold theorem4Problem11TwoPointXTransfer
    simp [hxrevj, hrevj_i, hj_revj.symm]
  have hz'i :
      z' i = z i - d + eps * r i + eps * r (reverseItem i) := by
    dsimp [z']
    unfold theorem4Problem11ColdStartPairZTransfer
    simp [hi_revi, hij_ne, hi_revj]
    ring
  have hz'j : z' j = d - eps := by
    dsimp [z']
    unfold theorem4Problem11ColdStartPairZTransfer
    simp [hzj, hj_revj, hij_ne.symm, hj_revi, hrj, hrrevj]
  have hstrict_i :
      theorem4Problem11ItemValue beta v x z i <
        theorem4Problem11ItemValue beta v x' z' i := by
    unfold theorem4Problem11ItemValue
    dsimp [qi, cold] at *
    rw [hxrevi, hx'i, hx'revi, hz'i]
    have hmain_gain : 0 < 2 * beta * qi * delta - cold * d := by
      have hlt := hd_upper
      dsimp [upper] at hlt
      rw [lt_div_iff₀ hcold_pos] at hlt
      have hlt' : cold * d < 2 * beta * qi * delta := by
        nlinarith [hlt]
      exact sub_pos.mpr hlt'
    have hredistrib_nonneg :
        0 ≤ cold * (eps * r i + eps * r (reverseItem i)) := by
      exact mul_nonneg hcold_pos.le
        (add_nonneg
          (mul_nonneg heps_pos.le (hr_nonneg i))
          (mul_nonneg heps_pos.le (hr_nonneg (reverseItem i))))
    linarith only [hmain_gain, hredistrib_nonneg]
  have hstrict_j :
      theorem4Problem11ItemValue beta v x z j <
        theorem4Problem11ItemValue beta v x' z' j := by
    unfold theorem4Problem11ItemValue
    change
      2 * beta * (qj * x j + (1 - qj) * x (reverseItem j)) +
          cold * z j <
        2 * beta * (qj * x' j + (1 - qj) * x' (reverseItem j)) +
          cold * z' j
    rw [hzj, hxrevj, hx'j, hx'revj, hz'j]
    have hmain_gain : 0 < cold * (d - eps) - 2 * beta * qj * delta := by
      have heps_small := heps_lt_slack
      dsimp [slack, lower] at heps_small
      have hlt :
          cold * eps <
            cold * (d - 2 * beta * qj * delta / cold) :=
        mul_lt_mul_of_pos_left heps_small hcold_pos
      rw [mul_sub, mul_div_cancel₀ _ (ne_of_gt hcold_pos)] at hlt
      nlinarith only [hlt]
    nlinarith only [hmain_gain]
  refine ⟨x', z', hx'_nonneg, hz'_nonneg, hx'_sum, hz'_sum,
    hz'_mirror, ?_⟩
  intro l
  by_cases hli : l = i
  · subst l
    exact hstrict_i
  · by_cases hlj : l = j
    · subst l
      exact hstrict_j
    · by_cases hlrevi : l = reverseItem i
      · subst l
        have horig :=
          theorem4Problem11ItemValue_reverse_eq
            (beta := beta) (v := v) (x := x) (z := z) hpos hzmirror i
        have hnew :=
          theorem4Problem11ItemValue_reverse_eq
            (beta := beta) (v := v) (x := x') (z := z') hpos hz'_mirror i
        rw [horig, hnew]
        exact hstrict_i
      · by_cases hlrevj : l = reverseItem j
        · subst l
          have horig :=
            theorem4Problem11ItemValue_reverse_eq
              (beta := beta) (v := v) (x := x) (z := z) hpos hzmirror j
          have hnew :=
            theorem4Problem11ItemValue_reverse_eq
              (beta := beta) (v := v) (x := x') (z := z') hpos hz'_mirror j
          rw [horig, hnew]
          exact hstrict_j
        · have hrev_li : reverseItem l ≠ i := by
            exact reverseItem_ne_of_ne_reverse hlrevi
          have hrev_lj : reverseItem l ≠ j := by
            exact reverseItem_ne_of_ne_reverse hlrevj
          have hxl' : x' l = x l := by
            dsimp [x']
            exact theorem4Problem11TwoPointXTransfer_apply_of_ne hli hlj
          have hxrev' : x' (reverseItem l) = x (reverseItem l) := by
            dsimp [x']
            exact theorem4Problem11TwoPointXTransfer_apply_of_ne hrev_li hrev_lj
          have hzl' :
              z' l = z l + eps * r l + eps * r (reverseItem l) := by
            dsimp [z']
            exact theorem4Problem11ColdStartPairZTransfer_apply_of_ne
              hli hlrevi hlj hlrevj
          have hrl_pos : 0 < r l := hr_pos hlj hlrevj
          have hredistrib_pos :
              0 < eps * r l + eps * r (reverseItem l) := by
            exact theorem4Problem11_symmetricRedistribution_pos
              (n := n) (r := r) (eps := eps) (l := l)
              heps_pos hrl_pos (hr_nonneg (reverseItem l))
          have hzlt : z l < z' l := by
            rw [hzl']
            calc
              z l < z l + (eps * r l + eps * r (reverseItem l)) :=
                lt_add_of_pos_right (z l) hredistrib_pos
              _ = z l + eps * r l + eps * r (reverseItem l) := by ring
          exact theorem4Problem11ItemValue_lt_of_same_x_strict_z
            (n := n) (beta := beta) (v := v) (x := x) (x' := x')
            (z := z) (z' := z') (j := l) hcold_pos hxl' hxrev' hzlt

theorem theorem4Problem11_typeZeroGap_pairSwap_exists_strictlyImproves
    {n : ℕ} {beta ell : ℝ} {v x z : Item n → ℝ} {i j : Item n}
    (hn : 2 < n)
    (hbeta_pos : 0 < beta)
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hij : i.val < j.val)
    (hi_left : i.val < (reverseItem i).val)
    (hj_left : j.val < (reverseItem j).val)
    (hx_nonneg : ∀ l : Item n, 0 ≤ x l)
    (hz_nonneg : ∀ l : Item n, 0 ≤ z l)
    (hsumx : (∑ l : Item n, x l) = 1)
    (hsumz : (∑ l : Item n, z l) = 1)
    (hzmirror : ∀ l : Item n, z (reverseItem l) = z l)
    (hxi : x i = 0)
    (hxj_pos : 0 < x j)
    (hxrevi : x (reverseItem i) = 0)
    (hxrevj : x (reverseItem j) = 0)
    (hi_eq : theorem4Problem11ItemValue beta v x z i = ell)
    (hj_eq : theorem4Problem11ItemValue beta v x z j = ell) :
    ∃ x' z' : Item n → ℝ,
      (∀ l : Item n, 0 ≤ x' l) ∧
      (∀ l : Item n, 0 ≤ z' l) ∧
      (∑ l : Item n, x' l) = 1 ∧
      (∑ l : Item n, z' l) = 1 ∧
      (∀ l : Item n, z' (reverseItem l) = z' l) ∧
      ∀ l : Item n,
        theorem4Problem11ItemValue beta v x z l <
          theorem4Problem11ItemValue beta v x' z' l := by
  classical
  have hji_ne : j ≠ i := by
    intro h
    subst j
    omega
  have hij_ne : i ≠ j := hji_ne.symm
  have hi_revi : i ≠ reverseItem i := by
    intro h
    have hval := congrArg Fin.val h
    omega
  have hj_revj : j ≠ reverseItem j := by
    intro h
    have hval := congrArg Fin.val h
    omega
  have hi_revj : i ≠ reverseItem j := by
    intro h
    have hji : j.val < i.val := by
      calc
        j.val < (reverseItem j).val := hj_left
        _ = i.val := by
          exact congrArg Fin.val h.symm
    omega
  have hj_revi : j ≠ reverseItem i := by
    intro h
    have hji : j.val < i.val := by
      calc
        j.val < (reverseItem j).val := hj_left
        _ = i.val := by
          rw [h, reverseItem_reverseItem]
    omega
  have hrevi_j : reverseItem i ≠ j := hj_revi.symm
  have hrevj_i : reverseItem j ≠ i := hi_revj.symm
  have hrevj_j : reverseItem j ≠ j := hj_revj.symm
  have hrevi_i : reverseItem i ≠ i := hi_revi.symm
  let qi : ℝ := pairShare (1 / 2) v i
  let qj : ℝ := pairShare (1 / 2) v j
  have hqj_lt_qi : qj < qi := by
    dsimp [qi, qj]
    exact pairShare_strictAnti_index (by norm_num) (by norm_num)
      hpos hdec hij
  have hqi_pos : 0 < qi := by
    dsimp [qi]
    exact pairShare_pos i (by norm_num) (by norm_num) hpos
  have hqi_lt_one : qi < 1 := by
    dsimp [qi]
    exact pairShare_lt_one i (by norm_num) (by norm_num) hpos
  have hqj_lt_one : qj < 1 := by
    dsimp [qj]
    exact pairShare_lt_one j (by norm_num) (by norm_num) hpos
  let cap : ℝ := (qi - qj) * x j
  have hcap_pos : 0 < cap := by
    dsimp [cap]
    nlinarith
  let eps : ℝ := min (x j) cap / 2
  have hmin_pos : 0 < min (x j) cap := lt_min hxj_pos hcap_pos
  have heps_pos : 0 < eps := by
    dsimp [eps]
    nlinarith
  have heps_lt_min : eps < min (x j) cap := by
    dsimp [eps]
    nlinarith
  have heps_lt_xj : eps < x j :=
    lt_of_lt_of_le heps_lt_min (min_le_left _ _)
  have heps_lt_cap : eps < cap :=
    lt_of_lt_of_le heps_lt_min (min_le_right _ _)
  have hqi_eps_lt_cap : qi * eps < cap := by
    have hmul_le : qi * eps ≤ eps := by nlinarith
    exact lt_of_le_of_lt hmul_le heps_lt_cap
  obtain ⟨r, hr_nonneg, hr_pos, hrj, hri, hrsum⟩ :=
    lemma4_redistribution_exists_of_two_lt hn hji_ne
  let x' : Item n → ℝ := lemma4GapExchangeX x j i (x j) eps r
  let z' : Item n → ℝ := theorem4Problem11MirrorPairSwapVector z i j
  have hx'_nonneg : ∀ l : Item n, 0 ≤ x' l := by
    intro l
    exact lemma4GapExchangeX_nonneg hx_nonneg rfl hxi hji_ne
      hr_nonneg hrj hri heps_pos heps_lt_xj l
  have hz'_nonneg : ∀ l : Item n, 0 ≤ z' l :=
    theorem4Problem11MirrorPairSwapVector_nonneg hz_nonneg
  have hx'_sum : (∑ l : Item n, x' l) = 1 := by
    dsimp [x']
    rw [lemma4GapExchangeX_sum_eq x j i (x j) eps r hrsum, hsumx]
  have hz'_sum : (∑ l : Item n, z' l) = 1 := by
    dsimp [z']
    rw [theorem4Problem11MirrorPairSwapVector_sum_eq z i j, hsumz]
  have hz'_mirror : ∀ l : Item n, z' (reverseItem l) = z' l := by
    dsimp [z']
    exact theorem4Problem11MirrorPairSwapVector_mirror
      hzmirror hij_ne hi_revi hj_revj hi_revj hj_revi
  have hx'i : x' i = x j - eps := by
    dsimp [x']
    simp [lemma4GapExchangeX, hxi, hji_ne.symm, hri]
  have hx'j : x' j = 0 := by
    dsimp [x']
    simp [lemma4GapExchangeX, hrj, hji_ne]
  have hx'revi :
      x' (reverseItem i) = eps * r (reverseItem i) := by
    dsimp [x']
    simp [lemma4GapExchangeX, hxrevi, hrevi_j, hrevi_i]
  have hx'revj :
      x' (reverseItem j) = eps * r (reverseItem j) := by
    dsimp [x']
    simp [lemma4GapExchangeX, hxrevj, hrevj_j, hrevj_i]
  have hz'i : z' i = z j := by
    dsimp [z']
    unfold theorem4Problem11MirrorPairSwapVector
    rw [theorem4Problem11MirrorPairSwap_apply_left hj_revi hj_revj]
  have hz'j : z' j = z i := by
    dsimp [z']
    unfold theorem4Problem11MirrorPairSwapVector
    rw [theorem4Problem11MirrorPairSwap_apply_right hij_ne hi_revi hi_revj]
  have hitem_ij :
      (1 - 2 * beta) * z i =
        2 * beta * (qj * x j) + (1 - 2 * beta) * z j := by
    have hi_s : (1 - 2 * beta) * z i = ell := by
      unfold theorem4Problem11ItemValue at hi_eq
      rw [hxi, hxrevi] at hi_eq
      linarith
    have hj_s :
        2 * beta * (qj * x j) + (1 - 2 * beta) * z j = ell := by
      unfold theorem4Problem11ItemValue at hj_eq
      rw [hxrevj] at hj_eq
      linarith
    exact hi_s.trans hj_s.symm
  have hstrict_i :
      theorem4Problem11ItemValue beta v x z i <
        theorem4Problem11ItemValue beta v x' z' i := by
    unfold theorem4Problem11ItemValue
    dsimp [qi, qj] at *
    rw [hxi, hxrevi, hx'i, hx'revi, hz'i]
    have hnonneg_extra :
        0 ≤ (1 - qi) * (eps * r (reverseItem i)) := by
      exact mul_nonneg (sub_nonneg.mpr hqi_lt_one.le)
        (mul_nonneg heps_pos.le (hr_nonneg (reverseItem i)))
    rw [hitem_ij]
    nlinarith [hqi_eps_lt_cap, hnonneg_extra]
  have hstrict_j :
      theorem4Problem11ItemValue beta v x z j <
        theorem4Problem11ItemValue beta v x' z' j := by
    unfold theorem4Problem11ItemValue
    dsimp [qi, qj] at *
    rw [hxrevj, hx'j, hx'revj, hz'j]
    rw [hitem_ij]
    have hrrevj_pos : 0 < r (reverseItem j) :=
      hr_pos hrevj_j hrevj_i
    have hgain_pos :
        0 < (1 - qj) * (eps * r (reverseItem j)) := by
      exact mul_pos (sub_pos.mpr hqj_lt_one)
        (mul_pos heps_pos hrrevj_pos)
    nlinarith
  refine ⟨x', z', hx'_nonneg, hz'_nonneg, hx'_sum, hz'_sum,
    hz'_mirror, ?_⟩
  intro l
  by_cases hli : l = i
  · subst l
    exact hstrict_i
  · by_cases hlj : l = j
    · subst l
      exact hstrict_j
    · by_cases hlrevi : l = reverseItem i
      · subst l
        have horig :=
          theorem4Problem11ItemValue_reverse_eq
            (beta := beta) (v := v) (x := x) (z := z) hpos hzmirror i
        have hnew :=
          theorem4Problem11ItemValue_reverse_eq
            (beta := beta) (v := v) (x := x') (z := z') hpos hz'_mirror i
        rw [horig, hnew]
        exact hstrict_i
      · by_cases hlrevj : l = reverseItem j
        · subst l
          have horig :=
            theorem4Problem11ItemValue_reverse_eq
              (beta := beta) (v := v) (x := x) (z := z) hpos hzmirror j
          have hnew :=
            theorem4Problem11ItemValue_reverse_eq
              (beta := beta) (v := v) (x := x') (z := z') hpos hz'_mirror j
          rw [horig, hnew]
          exact hstrict_j
        · have hrev_li : reverseItem l ≠ i := by
            intro h
            apply hlrevi
            calc
              l = reverseItem (reverseItem l) := by
                rw [reverseItem_reverseItem]
              _ = reverseItem i := by
                rw [h]
          have hrev_lj : reverseItem l ≠ j := by
            intro h
            apply hlrevj
            calc
              l = reverseItem (reverseItem l) := by
                rw [reverseItem_reverseItem]
              _ = reverseItem j := by
                rw [h]
          have hzl' : z' l = z l := by
            dsimp [z']
            unfold theorem4Problem11MirrorPairSwapVector
            rw [theorem4Problem11MirrorPairSwap_apply_of_distinct
              hli hlj hlrevi hlrevj]
          have hxl' : x' l = x l + eps * r l := by
            dsimp [x']
            simp [lemma4GapExchangeX, hlj, hli]
          have hxrev' :
              x' (reverseItem l) =
                x (reverseItem l) + eps * r (reverseItem l) := by
            dsimp [x']
            simp [lemma4GapExchangeX, hrev_lj, hrev_li]
          unfold theorem4Problem11ItemValue
          rw [hzl', hxl', hxrev']
          have hq_pos : 0 < pairShare (1 / 2) v l :=
            pairShare_pos l (by norm_num) (by norm_num) hpos
          have hq_lt_one : pairShare (1 / 2) v l < 1 :=
            pairShare_lt_one l (by norm_num) (by norm_num) hpos
          have hrl_pos : 0 < r l := hr_pos hlj hli
          have hrrev_pos : 0 < r (reverseItem l) :=
            hr_pos hrev_lj hrev_li
          have hleft_pos :
              0 < pairShare (1 / 2) v l * (eps * r l) :=
            mul_pos hq_pos (mul_pos heps_pos hrl_pos)
          have hright_pos :
              0 < (1 - pairShare (1 / 2) v l) *
                (eps * r (reverseItem l)) :=
            mul_pos (sub_pos.mpr hq_lt_one)
              (mul_pos heps_pos hrrev_pos)
          have hsum_pos :
              0 <
                pairShare (1 / 2) v l * (eps * r l) +
                  (1 - pairShare (1 / 2) v l) *
                    (eps * r (reverseItem l)) :=
            add_pos hleft_pos hright_pos
          nlinarith only [hbeta_pos, hsum_pos]

theorem theorem4Problem11_typeZeroGapStrictImprovement_left_of_equalizedBasicOptimal
    {n : ℕ} [NeZero n] {beta ell : ℝ} {v : Item n → ℝ}
    {ρ : TypePolicy 3 n}
    (hn : 2 < n)
    (hbeta_pos : 0 < beta)
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (h : Theorem4Problem11EqualizedBasicOptimal beta v ρ ell)
    (hright_zero :
      ∀ u : Item n, (reverseItem u).val < u.val → ρ 0 u = 0)
    {i j : Item n}
    (hij : i.val < j.val)
    (hxi_zero : ρ 0 i = 0)
    (hxj_ne : ρ 0 j ≠ 0)
    (hj_left : j.val < (reverseItem j).val) :
    ∃ ρ' : TypePolicy 3 n,
      Theorem4MirrorSymmetricPolicy ρ' ∧
        ∀ l : Item n,
          theorem4Problem11PolicyItemValue beta v ρ l <
            theorem4Problem11PolicyItemValue beta v ρ' l := by
  classical
  let x : Item n → ℝ := fun l => (ρ 0 l).toReal
  let z : Item n → ℝ := fun l => (ρ 2 l).toReal
  have hi_left : i.val < (reverseItem i).val := by
    have hrev_lt : (reverseItem j).val < (reverseItem i).val :=
      reverseItem_val_lt_of_val_lt hij
    exact lt_trans (lt_trans hij hj_left) hrev_lt
  have hx_nonneg : ∀ l : Item n, 0 ≤ x l := by
    intro l
    exact ENNReal.toReal_nonneg
  have hz_nonneg : ∀ l : Item n, 0 ≤ z l := by
    intro l
    exact ENNReal.toReal_nonneg
  have hsumx : (∑ l : Item n, x l) = 1 := by
    dsimp [x]
    exact AppliedModelingLib.pmfToRealSum (ρ 0)
  have hsumz : (∑ l : Item n, z l) = 1 := by
    dsimp [z]
    exact AppliedModelingLib.pmfToRealSum (ρ 2)
  have hzmirror : ∀ l : Item n, z (reverseItem l) = z l := by
    intro l
    dsimp [z]
    exact congrArg ENNReal.toReal (h.mirror.2 l)
  have hxi : x i = 0 := by
    dsimp [x]
    simp [hxi_zero]
  have hxj_pos : 0 < x j := by
    have htoReal_ne : (ρ 0 j).toReal ≠ 0 := by
      intro hzero
      rcases (ENNReal.toReal_eq_zero_iff (ρ 0 j)).mp hzero with hzero_enn | htop
      · exact hxj_ne hzero_enn
      · exact (ρ 0).apply_ne_top j htop
    exact lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm htoReal_ne)
  have hxrevi_policy : ρ 0 (reverseItem i) = 0 := by
    apply hright_zero
    simpa [reverseItem_reverseItem] using hi_left
  have hxrevj_policy : ρ 0 (reverseItem j) = 0 := by
    apply hright_zero
    simpa [reverseItem_reverseItem] using hj_left
  have hxrevi : x (reverseItem i) = 0 := by
    dsimp [x]
    simp [hxrevi_policy]
  have hxrevj : x (reverseItem j) = 0 := by
    dsimp [x]
    simp [hxrevj_policy]
  have hi_eq : theorem4Problem11ItemValue beta v x z i = ell := by
    simpa [theorem4Problem11PolicyItemValue, x, z] using h.item_eq i
  have hj_eq : theorem4Problem11ItemValue beta v x z j = ell := by
    simpa [theorem4Problem11PolicyItemValue, x, z] using h.item_eq j
  obtain ⟨x', z', hx'_nonneg, hz'_nonneg, hx'_sum, hz'_sum,
      hz'_mirror, hstrict⟩ :=
    theorem4Problem11_typeZeroGap_pairSwap_exists_strictlyImproves
      hn hbeta_pos hpos hdec hij hi_left hj_left hx_nonneg hz_nonneg
      hsumx hsumz hzmirror hxi hxj_pos hxrevi hxrevj hi_eq hj_eq
  let y' : Item n → ℝ := fun l => x' (reverseItem l)
  have hy'_nonneg : ∀ l : Item n, 0 ≤ y' l := by
    intro l
    exact hx'_nonneg (reverseItem l)
  have hy'_sum : (∑ l : Item n, y' l) = 1 := by
    dsimp [y']
    rw [sum_reverseItem x', hx'_sum]
  let ρ' : TypePolicy 3 n := fun k =>
    if k = 0 then
      pmfOfRealVector x' hx'_nonneg hx'_sum
    else if k = 1 then
      pmfOfRealVector y' hy'_nonneg hy'_sum
    else
      pmfOfRealVector z' hz'_nonneg hz'_sum
  have hsym' : Theorem4MirrorSymmetricPolicy ρ' := by
    constructor
    · intro l
      apply (ENNReal.toReal_eq_toReal_iff'
        ((ρ' 1).apply_ne_top (reverseItem l))
        ((ρ' 0).apply_ne_top l)).mp
      simp [ρ', y', reverseItem_reverseItem]
    · intro l
      apply (ENNReal.toReal_eq_toReal_iff'
        ((ρ' 2).apply_ne_top (reverseItem l))
        ((ρ' 2).apply_ne_top l)).mp
      simp [ρ', hz'_mirror l]
  refine ⟨ρ', hsym', ?_⟩
  intro l
  unfold theorem4Problem11PolicyItemValue
  simpa [ρ', x, z] using hstrict l

theorem theorem4Problem11_typeZeroGapStrictImprovement_noncenter_of_equalizedBasicOptimal
    {n : ℕ} [NeZero n] {beta ell : ℝ} {v : Item n → ℝ}
    {ρ : TypePolicy 3 n}
    (hn : 2 < n)
    (hbeta_pos : 0 < beta)
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (h : Theorem4Problem11EqualizedBasicOptimal beta v ρ ell)
    (hright_zero :
      ∀ u : Item n, (reverseItem u).val < u.val → ρ 0 u = 0)
    {i j : Item n}
    (hij : i.val < j.val)
    (hxi_zero : ρ 0 i = 0)
    (hxj_ne : ρ 0 j ≠ 0)
    (hj_noncenter : j ≠ reverseItem j) :
    ∃ ρ' : TypePolicy 3 n,
      Theorem4MirrorSymmetricPolicy ρ' ∧
        ∀ l : Item n,
          theorem4Problem11PolicyItemValue beta v ρ l <
            theorem4Problem11PolicyItemValue beta v ρ' l := by
  by_cases hj_left : j.val < (reverseItem j).val
  · exact theorem4Problem11_typeZeroGapStrictImprovement_left_of_equalizedBasicOptimal
      hn hbeta_pos hpos hdec h hright_zero hij hxi_zero hxj_ne hj_left
  · have hj_right : (reverseItem j).val < j.val := by
      have hne_val : j.val ≠ (reverseItem j).val := by
        intro hval
        apply hj_noncenter
        ext
        exact hval
      omega
    have hzj : ρ 0 j = 0 := hright_zero j hj_right
    exact False.elim (hxj_ne hzj)

/--
Center-case cold-start transfer for Appendix E, Lemma 13.  When the donor
`j` is its own mirror, the `z`-row cannot be handled by a mirror-pair swap; we
instead move equal mass `d` away from `i` and its mirror and put `2d` on the
center item.
-/
noncomputable def theorem4Problem11CenterZTransfer {n : ℕ}
    (z : Item n → ℝ) (i c : Item n) (d : ℝ) : Item n → ℝ :=
  fun l =>
    z l +
      (if l = i then -d else 0) +
      (if l = reverseItem i then -d else 0) +
      (if l = c then 2 * d else 0)

theorem theorem4Problem11CenterZTransfer_sum_eq {n : ℕ}
    (z : Item n → ℝ) (i c : Item n) (d : ℝ) :
    (∑ l : Item n, theorem4Problem11CenterZTransfer z i c d l) =
      ∑ l : Item n, z l := by
  unfold theorem4Problem11CenterZTransfer
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib]
  simp
  ring

theorem theorem4Problem11CenterZTransfer_nonneg {n : ℕ}
    {z : Item n → ℝ} {i c : Item n} {d : ℝ}
    (hz_nonneg : ∀ l : Item n, 0 ≤ z l)
    (hzmirror : ∀ l : Item n, z (reverseItem l) = z l)
    (hi_revi : i ≠ reverseItem i)
    (hi_c : i ≠ c)
    (hrevi_c : reverseItem i ≠ c)
    (hd_nonneg : 0 ≤ d)
    (hd_le : d ≤ z i) :
    ∀ l : Item n, 0 ≤ theorem4Problem11CenterZTransfer z i c d l := by
  intro l
  unfold theorem4Problem11CenterZTransfer
  by_cases hli : l = i
  · subst l
    simp [hi_revi, hi_c, hd_le]
  · by_cases hlrevi : l = reverseItem i
    · subst l
      simp [hi_revi.symm, hrevi_c, hzmirror i, hd_le]
    · by_cases hlc : l = c
      · subst l
        have htwo_nonneg : 0 ≤ 2 * d := by nlinarith
        simp [hi_c.symm, hrevi_c.symm, add_nonneg (hz_nonneg c) htwo_nonneg]
      · simpa [hli, hlrevi, hlc] using hz_nonneg l

theorem theorem4Problem11CenterZTransfer_mirror {n : ℕ}
    {z : Item n → ℝ} {i c : Item n} {d : ℝ}
    (hzmirror : ∀ l : Item n, z (reverseItem l) = z l)
    (hc : reverseItem c = c)
    (hi_revi : i ≠ reverseItem i)
    (hi_c : i ≠ c)
    (hrevi_c : reverseItem i ≠ c) :
    ∀ l : Item n,
      theorem4Problem11CenterZTransfer z i c d (reverseItem l) =
        theorem4Problem11CenterZTransfer z i c d l := by
  intro l
  unfold theorem4Problem11CenterZTransfer
  by_cases hli : l = i
  · subst l
    simp [hi_revi, hi_revi.symm, hi_c, hrevi_c, hzmirror i]
  · by_cases hlrevi : l = reverseItem i
    · subst l
      simp [reverseItem_reverseItem, hi_revi, hi_revi.symm, hi_c,
        hrevi_c, hzmirror i]
    · by_cases hlc : l = c
      · subst l
        simp [hc, hi_c.symm, hrevi_c.symm]
      · have hrev_ne_i : reverseItem l ≠ i := by
          intro h
          apply hlrevi
          calc
            l = reverseItem (reverseItem l) := by
              rw [reverseItem_reverseItem]
            _ = reverseItem i := by
              rw [h]
        have hrev_ne_revi : reverseItem l ≠ reverseItem i := by
          intro h
          apply hli
          calc
            l = reverseItem (reverseItem l) := by
              rw [reverseItem_reverseItem]
            _ = reverseItem (reverseItem i) := by
              rw [h]
            _ = i := by
              rw [reverseItem_reverseItem]
        have hrev_ne_c : reverseItem l ≠ c := by
          intro h
          apply hlc
          calc
            l = reverseItem (reverseItem l) := by
              rw [reverseItem_reverseItem]
            _ = reverseItem c := by
              rw [h]
            _ = c := hc
        simp [hli, hlrevi, hlc, hrev_ne_i, hrev_ne_revi, hrev_ne_c,
          hzmirror l]

noncomputable def theorem4Problem11ColdStartCenterZTransfer {n : ℕ}
    (z r : Item n → ℝ) (i c : Item n) (d eps : ℝ) : Item n → ℝ :=
  fun l =>
    z l +
      (if l = i then -d else 0) +
      (if l = reverseItem i then -d else 0) +
      (if l = c then 2 * d - 2 * eps else 0) +
      eps * r l + eps * r (reverseItem l)

theorem theorem4Problem11ColdStartCenterZTransfer_sum_eq {n : ℕ}
    (z r : Item n → ℝ) (i c : Item n) (d eps : ℝ)
    (hrsum : (∑ l : Item n, r l) = 1) :
    (∑ l : Item n,
        theorem4Problem11ColdStartCenterZTransfer z r i c d eps l) =
      ∑ l : Item n, z l := by
  unfold theorem4Problem11ColdStartCenterZTransfer
  repeat rw [Finset.sum_add_distrib]
  rw [← Finset.mul_sum, ← Finset.mul_sum, sum_reverseItem r, hrsum]
  simp
  ring

set_option linter.unusedSimpArgs false in
theorem theorem4Problem11ColdStartCenterZTransfer_mirror {n : ℕ}
    {z r : Item n → ℝ} {i c : Item n} {d eps : ℝ}
    (hzmirror : ∀ l : Item n, z (reverseItem l) = z l)
    (hc : reverseItem c = c)
    (hi_revi : i ≠ reverseItem i)
    (hi_c : i ≠ c)
    (hrevi_c : reverseItem i ≠ c) :
    ∀ l : Item n,
      theorem4Problem11ColdStartCenterZTransfer z r i c d eps
          (reverseItem l) =
        theorem4Problem11ColdStartCenterZTransfer z r i c d eps l := by
  intro l
  unfold theorem4Problem11ColdStartCenterZTransfer
  by_cases hli : l = i
  · subst l
    simp [reverseItem_reverseItem, hi_revi, hi_revi.symm, hi_c, hrevi_c,
      hzmirror i]
    ring
  · by_cases hlrevi : l = reverseItem i
    · subst l
      simp [reverseItem_reverseItem, hi_revi, hi_revi.symm, hi_c,
        hrevi_c, hzmirror i]
      ring
    · by_cases hlc : l = c
      · subst l
        simp [hc, hi_c.symm, hrevi_c.symm]
      · have hrev_ne_i : reverseItem l ≠ i :=
          reverseItem_ne_of_ne_reverse hlrevi
        have hrev_ne_revi : reverseItem l ≠ reverseItem i := by
          intro h
          apply hli
          calc
            l = reverseItem (reverseItem l) := (reverseItem_reverseItem l).symm
            _ = reverseItem (reverseItem i) := by rw [h]
            _ = i := reverseItem_reverseItem i
        have hrev_ne_c : reverseItem l ≠ c := by
          intro h
          apply hlc
          calc
            l = reverseItem (reverseItem l) := (reverseItem_reverseItem l).symm
            _ = reverseItem c := by rw [h]
            _ = c := hc
        simp [reverseItem_reverseItem, hli, hlrevi, hlc, hrev_ne_i,
          hrev_ne_revi, hrev_ne_c, hzmirror l]
        ring

theorem theorem4Problem11ColdStartCenterZTransfer_nonneg {n : ℕ}
    {z r : Item n → ℝ} {i c : Item n} {d eps : ℝ}
    (hz_nonneg : ∀ l : Item n, 0 ≤ z l)
    (hzmirror : ∀ l : Item n, z (reverseItem l) = z l)
    (hc : reverseItem c = c)
    (hi_revi : i ≠ reverseItem i)
    (hi_c : i ≠ c)
    (hrevi_c : reverseItem i ≠ c)
    (hr_nonneg : ∀ l : Item n, 0 ≤ r l)
    (hrc : r c = 0)
    (hd_nonneg : 0 ≤ d)
    (heps_nonneg : 0 ≤ eps)
    (heps_le_d : eps ≤ d)
    (hd_le : d ≤ z i) :
    ∀ l : Item n,
      0 ≤ theorem4Problem11ColdStartCenterZTransfer z r i c d eps l := by
  intro l
  unfold theorem4Problem11ColdStartCenterZTransfer
  by_cases hli : l = i
  · subst l
    have hredistrib_nonneg :
        0 ≤ eps * r i + eps * r (reverseItem i) := by
      exact add_nonneg
        (mul_nonneg heps_nonneg (hr_nonneg i))
        (mul_nonneg heps_nonneg (hr_nonneg (reverseItem i)))
    simp [hi_revi, hi_c]
    nlinarith [hd_le, hredistrib_nonneg]
  · by_cases hlrevi : l = reverseItem i
    · subst l
      have hredistrib_nonneg :
          0 ≤ eps * r (reverseItem i) + eps * r i := by
        exact add_nonneg
          (mul_nonneg heps_nonneg (hr_nonneg (reverseItem i)))
          (mul_nonneg heps_nonneg (hr_nonneg i))
      simp [reverseItem_reverseItem, hi_revi.symm, hrevi_c]
      rw [hzmirror i]
      nlinarith [hd_le, hredistrib_nonneg]
    · by_cases hlc : l = c
      · subst l
        simp [hc, hi_c.symm, hrevi_c.symm, hrc]
        nlinarith [hz_nonneg c, heps_le_d]
      · have hredistrib_nonneg :
            0 ≤ eps * r l + eps * r (reverseItem l) := by
          exact add_nonneg
            (mul_nonneg heps_nonneg (hr_nonneg l))
            (mul_nonneg heps_nonneg (hr_nonneg (reverseItem l)))
        simpa [hli, hlrevi, hlc, add_assoc] using
          add_nonneg (hz_nonneg l) hredistrib_nonneg

theorem theorem4Problem11ColdStartCenterZTransfer_apply_center {n : ℕ}
    {z r : Item n → ℝ} {i c : Item n} {d eps : ℝ}
    (hc : reverseItem c = c)
    (hi_c : i ≠ c)
    (hrevi_c : reverseItem i ≠ c)
    (hrc : r c = 0) :
    theorem4Problem11ColdStartCenterZTransfer z r i c d eps c =
      z c + (2 * d - 2 * eps) := by
  unfold theorem4Problem11ColdStartCenterZTransfer
  simp [hc, hi_c.symm, hrevi_c.symm, hrc]

theorem theorem4Problem11ColdStartCenterZTransfer_apply_of_ne {n : ℕ}
    {z r : Item n → ℝ} {i c l : Item n} {d eps : ℝ}
    (hli : l ≠ i)
    (hlrevi : l ≠ reverseItem i)
    (hlc : l ≠ c) :
    theorem4Problem11ColdStartCenterZTransfer z r i c d eps l =
      z l + eps * r l + eps * r (reverseItem l) := by
  unfold theorem4Problem11ColdStartCenterZTransfer
  rw [if_neg hli, if_neg hlrevi, if_neg hlc]
  ring

theorem theorem4Problem11_typeZeroGap_centerTransfer_exists_strictlyImproves
    {n : ℕ} {beta ell : ℝ} {v x z : Item n → ℝ} {i c : Item n}
    (hn : 2 < n)
    (hbeta_pos : 0 < beta)
    (hbeta_half : beta < 1 / 2)
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hic : i.val < c.val)
    (hc_center : reverseItem c = c)
    (hx_nonneg : ∀ l : Item n, 0 ≤ x l)
    (hz_nonneg : ∀ l : Item n, 0 ≤ z l)
    (hsumx : (∑ l : Item n, x l) = 1)
    (hsumz : (∑ l : Item n, z l) = 1)
    (hzmirror : ∀ l : Item n, z (reverseItem l) = z l)
    (hxi : x i = 0)
    (hxc_pos : 0 < x c)
    (hxrevi : x (reverseItem i) = 0)
    (hi_eq : theorem4Problem11ItemValue beta v x z i = ell)
    (hc_eq : theorem4Problem11ItemValue beta v x z c = ell) :
    ∃ x' z' : Item n → ℝ,
      (∀ l : Item n, 0 ≤ x' l) ∧
      (∀ l : Item n, 0 ≤ z' l) ∧
      (∑ l : Item n, x' l) = 1 ∧
      (∑ l : Item n, z' l) = 1 ∧
      (∀ l : Item n, z' (reverseItem l) = z' l) ∧
      ∀ l : Item n,
        theorem4Problem11ItemValue beta v x z l <
          theorem4Problem11ItemValue beta v x' z' l := by
  classical
  let cold : ℝ := 1 - 2 * beta
  have hcold_pos : 0 < cold := by
    dsimp [cold]
    nlinarith
  have hci_ne : c ≠ i := by
    intro h
    subst c
    omega
  have hic_ne : i ≠ c := hci_ne.symm
  have hi_left : i.val < (reverseItem i).val := by
    have hrev_lt : c.val < (reverseItem i).val := by
      simpa [hc_center] using reverseItem_val_lt_of_val_lt hic
    exact lt_trans hic hrev_lt
  have hi_revi : i ≠ reverseItem i := by
    intro h
    have hval := congrArg Fin.val h
    omega
  have hrevi_c : reverseItem i ≠ c := by
    intro h
    have hrev_lt : c.val < (reverseItem i).val := by
      simpa [hc_center] using reverseItem_val_lt_of_val_lt hic
    have hval := congrArg Fin.val h
    omega
  let qi : ℝ := pairShare (1 / 2) v i
  have hqi_half : (1 / 2 : ℝ) < qi := by
    dsimp [qi]
    exact half_lt_pairShare_half_of_val_lt_reverse i hpos hdec hi_left
  have hqi_pos : 0 < qi := lt_trans (by norm_num) hqi_half
  have hqi_lt_one : qi < 1 := by
    dsimp [qi]
    exact pairShare_lt_one i (by norm_num) (by norm_num) hpos
  have hitem_ic : cold * z i = 2 * beta * x c + cold * z c := by
    have hi_s : cold * z i = ell := by
      unfold theorem4Problem11ItemValue at hi_eq
      rw [hxi, hxrevi] at hi_eq
      linarith
    have hc_s : 2 * beta * x c + cold * z c = ell := by
      unfold theorem4Problem11ItemValue at hc_eq
      rw [hc_center] at hc_eq
      ring_nf at hc_eq ⊢
      linarith
    exact hi_s.trans hc_s.symm
  let lower : ℝ := beta * x c / cold
  let upper : ℝ := 2 * beta * qi * x c / cold
  have hlower_lt_upper : lower < upper := by
    dsimp [lower, upper]
    rw [div_lt_div_iff₀ hcold_pos hcold_pos]
    have hmul : beta * x c < 2 * beta * qi * x c := by
      have htwo_qi : (1 : ℝ) < 2 * qi := by
        nlinarith
      have hbxc_pos : 0 < beta * x c :=
        mul_pos hbeta_pos hxc_pos
      calc
        beta * x c = 1 * (beta * x c) := by ring
        _ < (2 * qi) * (beta * x c) :=
          mul_lt_mul_of_pos_right htwo_qi hbxc_pos
        _ = 2 * beta * qi * x c := by ring
    exact mul_lt_mul_of_pos_right hmul hcold_pos
  obtain ⟨d, hd_lower, hd_upper⟩ := exists_between hlower_lt_upper
  have hlower_pos : 0 < lower := by
    dsimp [lower]
    exact div_pos (mul_pos hbeta_pos hxc_pos) hcold_pos
  have hd_pos : 0 < d := lt_trans hlower_pos hd_lower
  have hd_nonneg : 0 ≤ d := hd_pos.le
  have hcenter_gain : 2 * beta * x c < 2 * cold * d := by
    have htmp : beta * x c < cold * d := by
      have := hd_lower
      dsimp [lower] at this
      rw [div_lt_iff₀ hcold_pos] at this
      simpa [mul_comm, mul_left_comm, mul_assoc] using this
    nlinarith
  have hcold_d_lt : cold * d < 2 * beta * qi * x c := by
    have := hd_upper
    dsimp [upper] at this
    rw [lt_div_iff₀ hcold_pos] at this
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  have hd_lt_zi : d < z i := by
    have hcold_d_lt_z : cold * d < cold * z i := by
      calc
        cold * d < 2 * beta * qi * x c := hcold_d_lt
        _ < 2 * beta * x c := by nlinarith
        _ ≤ 2 * beta * x c + cold * z c := by
          nlinarith [hz_nonneg c, hcold_pos]
        _ = cold * z i := hitem_ic.symm
    nlinarith [hcold_pos, hcold_d_lt_z]
  let slack : ℝ := 2 * beta * qi * x c - cold * d
  have hslack_pos : 0 < slack := by
    dsimp [slack]
    linarith
  let epsBound : ℝ := slack / (2 * beta * qi)
  have hden_pos : 0 < 2 * beta * qi := by
    nlinarith
  have hepsBound_pos : 0 < epsBound := by
    dsimp [epsBound]
    exact div_pos hslack_pos hden_pos
  let eps : ℝ := min (x c) epsBound / 2
  have hmin_pos : 0 < min (x c) epsBound :=
    lt_min hxc_pos hepsBound_pos
  have heps_pos : 0 < eps := by
    dsimp [eps]
    nlinarith
  have heps_lt_min : eps < min (x c) epsBound := by
    dsimp [eps]
    nlinarith
  have heps_lt_xc : eps < x c :=
    lt_of_lt_of_le heps_lt_min (min_le_left _ _)
  have heps_lt_bound : eps < epsBound :=
    lt_of_lt_of_le heps_lt_min (min_le_right _ _)
  have hqi_eps_slack : 2 * beta * qi * eps < slack := by
    have := heps_lt_bound
    dsimp [epsBound] at this
    rw [lt_div_iff₀ hden_pos] at this
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  obtain ⟨r, hr_nonneg, hr_pos, hrc, hri, hrsum⟩ :=
    lemma4_redistribution_exists_of_two_lt hn hci_ne
  let x' : Item n → ℝ := lemma4GapExchangeX x c i (x c) eps r
  let z' : Item n → ℝ := theorem4Problem11CenterZTransfer z i c d
  have hx'_nonneg : ∀ l : Item n, 0 ≤ x' l := by
    intro l
    exact lemma4GapExchangeX_nonneg hx_nonneg rfl hxi hci_ne
      hr_nonneg hrc hri heps_pos heps_lt_xc l
  have hz'_nonneg : ∀ l : Item n, 0 ≤ z' l :=
    theorem4Problem11CenterZTransfer_nonneg hz_nonneg hzmirror
      hi_revi hic_ne hrevi_c hd_nonneg hd_lt_zi.le
  have hx'_sum : (∑ l : Item n, x' l) = 1 := by
    dsimp [x']
    rw [lemma4GapExchangeX_sum_eq x c i (x c) eps r hrsum, hsumx]
  have hz'_sum : (∑ l : Item n, z' l) = 1 := by
    dsimp [z']
    rw [theorem4Problem11CenterZTransfer_sum_eq z i c d, hsumz]
  have hz'_mirror : ∀ l : Item n, z' (reverseItem l) = z' l := by
    dsimp [z']
    exact theorem4Problem11CenterZTransfer_mirror
      hzmirror hc_center hi_revi hic_ne hrevi_c
  have hx'i : x' i = x c - eps := by
    dsimp [x']
    simp [lemma4GapExchangeX, hxi, hci_ne.symm, hri]
  have hx'c : x' c = 0 := by
    dsimp [x']
    simp [lemma4GapExchangeX, hrc, hci_ne]
  have hx'revi :
      x' (reverseItem i) = eps * r (reverseItem i) := by
    dsimp [x']
    simp [lemma4GapExchangeX, hxrevi, hrevi_c, hi_revi.symm]
  have hz'i : z' i = z i - d := by
    dsimp [z']
    unfold theorem4Problem11CenterZTransfer
    simp [hi_revi, hic_ne]
    ring
  have hz'c : z' c = z c + 2 * d := by
    dsimp [z']
    unfold theorem4Problem11CenterZTransfer
    simp [hic_ne.symm, hrevi_c.symm]
  have hstrict_i :
      theorem4Problem11ItemValue beta v x z i <
        theorem4Problem11ItemValue beta v x' z' i := by
    unfold theorem4Problem11ItemValue
    dsimp [qi, cold] at *
    rw [hxi, hxrevi, hx'i, hx'revi, hz'i]
    have hnonneg_extra :
        0 ≤ (1 - pairShare (1 / 2) v i) *
          (eps * r (reverseItem i)) := by
      exact mul_nonneg (sub_nonneg.mpr hqi_lt_one.le)
        (mul_nonneg heps_pos.le (hr_nonneg (reverseItem i)))
    have hscaled_extra :
        0 ≤ 2 * beta *
          ((1 - pairShare (1 / 2) v i) *
            (eps * r (reverseItem i))) := by
      nlinarith only [hbeta_pos, hnonneg_extra]
    dsimp [slack, qi, cold] at hqi_eps_slack
    have hgain_pos :
        0 <
          2 * beta *
              (pairShare (1 / 2) v i * (x c - eps) +
                (1 - pairShare (1 / 2) v i) *
                  (eps * r (reverseItem i))) -
            (1 - 2 * beta) * d := by
      nlinarith only [hqi_eps_slack, hscaled_extra]
    nlinarith only [hgain_pos]
  have hstrict_c :
      theorem4Problem11ItemValue beta v x z c <
        theorem4Problem11ItemValue beta v x' z' c := by
    unfold theorem4Problem11ItemValue
    rw [hc_center, hx'c, hz'c]
    dsimp [cold] at *
    nlinarith only [hcenter_gain]
  refine ⟨x', z', hx'_nonneg, hz'_nonneg, hx'_sum, hz'_sum,
    hz'_mirror, ?_⟩
  intro l
  by_cases hli : l = i
  · subst l
    exact hstrict_i
  · by_cases hlrevi : l = reverseItem i
    · subst l
      have horig :=
        theorem4Problem11ItemValue_reverse_eq
          (beta := beta) (v := v) (x := x) (z := z) hpos hzmirror i
      have hnew :=
        theorem4Problem11ItemValue_reverse_eq
          (beta := beta) (v := v) (x := x') (z := z') hpos hz'_mirror i
      rw [horig, hnew]
      exact hstrict_i
    · by_cases hlc : l = c
      · subst l
        exact hstrict_c
      · have hrev_li : reverseItem l ≠ i := by
          intro h
          apply hlrevi
          calc
            l = reverseItem (reverseItem l) := by
              rw [reverseItem_reverseItem]
            _ = reverseItem i := by
              rw [h]
        have hrev_lc : reverseItem l ≠ c := by
          intro h
          apply hlc
          calc
            l = reverseItem (reverseItem l) := by
              rw [reverseItem_reverseItem]
            _ = reverseItem c := by
              rw [h]
            _ = c := hc_center
        have hzl' : z' l = z l := by
          dsimp [z']
          unfold theorem4Problem11CenterZTransfer
          simp [hli, hlrevi, hlc]
        have hxl' : x' l = x l + eps * r l := by
          dsimp [x']
          simp [lemma4GapExchangeX, hlc, hli]
        have hxrev' :
            x' (reverseItem l) =
              x (reverseItem l) + eps * r (reverseItem l) := by
          dsimp [x']
          simp [lemma4GapExchangeX, hrev_lc, hrev_li]
        unfold theorem4Problem11ItemValue
        rw [hzl', hxl', hxrev']
        have hq_pos : 0 < pairShare (1 / 2) v l :=
          pairShare_pos l (by norm_num) (by norm_num) hpos
        have hq_lt_one : pairShare (1 / 2) v l < 1 :=
          pairShare_lt_one l (by norm_num) (by norm_num) hpos
        have hrl_pos : 0 < r l := hr_pos hlc hli
        have hrrev_pos : 0 < r (reverseItem l) :=
          hr_pos hrev_lc hrev_li
        have hleft_pos :
            0 < pairShare (1 / 2) v l * (eps * r l) :=
          mul_pos hq_pos (mul_pos heps_pos hrl_pos)
        have hright_pos :
            0 < (1 - pairShare (1 / 2) v l) *
              (eps * r (reverseItem l)) :=
          mul_pos (sub_pos.mpr hq_lt_one)
            (mul_pos heps_pos hrrev_pos)
        have hsum_pos :
            0 <
              pairShare (1 / 2) v l * (eps * r l) +
                (1 - pairShare (1 / 2) v l) *
                  (eps * r (reverseItem l)) :=
          add_pos hleft_pos hright_pos
        nlinarith only [hbeta_pos, hsum_pos]

theorem theorem4Problem11_typeZeroGapStrictImprovement_center_of_equalizedBasicOptimal
    {n : ℕ} [NeZero n] {beta ell : ℝ} {v : Item n → ℝ}
    {ρ : TypePolicy 3 n}
    (hn : 2 < n)
    (hbeta_pos : 0 < beta)
    (hbeta_half : beta < 1 / 2)
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (h : Theorem4Problem11EqualizedBasicOptimal beta v ρ ell)
    (hright_zero :
      ∀ u : Item n, (reverseItem u).val < u.val → ρ 0 u = 0)
    {i j : Item n}
    (hij : i.val < j.val)
    (hxi_zero : ρ 0 i = 0)
    (hxj_ne : ρ 0 j ≠ 0)
    (hj_center : reverseItem j = j) :
    ∃ ρ' : TypePolicy 3 n,
      Theorem4MirrorSymmetricPolicy ρ' ∧
        ∀ l : Item n,
          theorem4Problem11PolicyItemValue beta v ρ l <
            theorem4Problem11PolicyItemValue beta v ρ' l := by
  classical
  let x : Item n → ℝ := fun l => (ρ 0 l).toReal
  let z : Item n → ℝ := fun l => (ρ 2 l).toReal
  have hi_left : i.val < (reverseItem i).val := by
    have hrev_lt : j.val < (reverseItem i).val := by
      simpa [hj_center] using reverseItem_val_lt_of_val_lt hij
    exact lt_trans hij hrev_lt
  have hx_nonneg : ∀ l : Item n, 0 ≤ x l := by
    intro l
    exact ENNReal.toReal_nonneg
  have hz_nonneg : ∀ l : Item n, 0 ≤ z l := by
    intro l
    exact ENNReal.toReal_nonneg
  have hsumx : (∑ l : Item n, x l) = 1 := by
    dsimp [x]
    exact AppliedModelingLib.pmfToRealSum (ρ 0)
  have hsumz : (∑ l : Item n, z l) = 1 := by
    dsimp [z]
    exact AppliedModelingLib.pmfToRealSum (ρ 2)
  have hzmirror : ∀ l : Item n, z (reverseItem l) = z l := by
    intro l
    dsimp [z]
    exact congrArg ENNReal.toReal (h.mirror.2 l)
  have hxi : x i = 0 := by
    dsimp [x]
    simp [hxi_zero]
  have hxj_pos : 0 < x j := by
    have htoReal_ne : (ρ 0 j).toReal ≠ 0 := by
      intro hzero
      rcases (ENNReal.toReal_eq_zero_iff (ρ 0 j)).mp hzero with hzero_enn | htop
      · exact hxj_ne hzero_enn
      · exact (ρ 0).apply_ne_top j htop
    exact lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm htoReal_ne)
  have hxrevi_policy : ρ 0 (reverseItem i) = 0 := by
    apply hright_zero
    simpa [reverseItem_reverseItem] using hi_left
  have hxrevi : x (reverseItem i) = 0 := by
    dsimp [x]
    simp [hxrevi_policy]
  have hi_eq : theorem4Problem11ItemValue beta v x z i = ell := by
    simpa [theorem4Problem11PolicyItemValue, x, z] using h.item_eq i
  have hj_eq : theorem4Problem11ItemValue beta v x z j = ell := by
    simpa [theorem4Problem11PolicyItemValue, x, z] using h.item_eq j
  obtain ⟨x', z', hx'_nonneg, hz'_nonneg, hx'_sum, hz'_sum,
      hz'_mirror, hstrict⟩ :=
    theorem4Problem11_typeZeroGap_centerTransfer_exists_strictlyImproves
      hn hbeta_pos hbeta_half hpos hdec hij hj_center hx_nonneg hz_nonneg
      hsumx hsumz hzmirror hxi hxj_pos hxrevi hi_eq hj_eq
  let y' : Item n → ℝ := fun l => x' (reverseItem l)
  have hy'_nonneg : ∀ l : Item n, 0 ≤ y' l := by
    intro l
    exact hx'_nonneg (reverseItem l)
  have hy'_sum : (∑ l : Item n, y' l) = 1 := by
    dsimp [y']
    rw [sum_reverseItem x', hx'_sum]
  let ρ' : TypePolicy 3 n := fun k =>
    if k = 0 then
      pmfOfRealVector x' hx'_nonneg hx'_sum
    else if k = 1 then
      pmfOfRealVector y' hy'_nonneg hy'_sum
    else
      pmfOfRealVector z' hz'_nonneg hz'_sum
  have hsym' : Theorem4MirrorSymmetricPolicy ρ' := by
    constructor
    · intro l
      apply (ENNReal.toReal_eq_toReal_iff'
        ((ρ' 1).apply_ne_top (reverseItem l))
        ((ρ' 0).apply_ne_top l)).mp
      simp [ρ', y', reverseItem_reverseItem]
    · intro l
      apply (ENNReal.toReal_eq_toReal_iff'
        ((ρ' 2).apply_ne_top (reverseItem l))
        ((ρ' 2).apply_ne_top l)).mp
      simp [ρ', hz'_mirror l]
  refine ⟨ρ', hsym', ?_⟩
  intro l
  unfold theorem4Problem11PolicyItemValue
  simpa [ρ', x, z] using hstrict l

theorem theorem4Problem11_typeZeroGapStrictImprovement_of_equalizedBasicOptimal
    {n : ℕ} [NeZero n] {beta ell : ℝ} {v : Item n → ℝ}
    {ρ : TypePolicy 3 n}
    (hn : 2 < n)
    (hbeta_pos : 0 < beta)
    (hbeta_half : beta < 1 / 2)
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (h : Theorem4Problem11EqualizedBasicOptimal beta v ρ ell) :
    Theorem4Problem11TypeZeroGapStrictImprovement beta v ρ := by
  have hno : Theorem4Problem11PolicyNoStrictPointwiseImprovement beta v ρ :=
    theorem4Problem11_noStrictPointwiseImprovement_of_equalizedBasicOptimal h
  have hright_zero :
      ∀ u : Item n, (reverseItem u).val < u.val → ρ 0 u = 0 :=
    theorem4Problem11_typeZero_zero_after_mirror_of_noStrictPointwiseImprovement
      hn hbeta_pos hpos hdec h.mirror hno
  intro i j hij hxi_zero hxj_ne
  by_cases hj_center' : j = reverseItem j
  · exact theorem4Problem11_typeZeroGapStrictImprovement_center_of_equalizedBasicOptimal
      hn hbeta_pos hbeta_half hpos hdec h hright_zero hij hxi_zero hxj_ne
      hj_center'.symm
  · exact theorem4Problem11_typeZeroGapStrictImprovement_noncenter_of_equalizedBasicOptimal
      hn hbeta_pos hpos hdec h hright_zero hij hxi_zero hxj_ne hj_center'

theorem theorem4Problem11_coldStartGapStrictImprovement_noncenter_of_equalizedBasicOptimal
    {n : ℕ} [NeZero n] {beta ell : ℝ} {v : Item n → ℝ}
    {ρ : TypePolicy 3 n}
    (hn : 2 < n)
    (hbeta_pos : 0 < beta)
    (hbeta_half : beta < 1 / 2)
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (h : Theorem4Problem11EqualizedBasicOptimal beta v ρ ell)
    (hright_zero :
      ∀ u : Item n, (reverseItem u).val < u.val → ρ 0 u = 0)
    {i j : Item n}
    (hij : i.val < j.val)
    (hj_half : j.val ≤ (reverseItem j).val)
    (hzi_ne : ρ 2 i ≠ 0)
    (hzj_zero : ρ 2 j = 0)
    (hj_noncenter : j ≠ reverseItem j) :
    ∃ ρ' : TypePolicy 3 n,
      Theorem4MirrorSymmetricPolicy ρ' ∧
        ∀ l : Item n,
          theorem4Problem11PolicyItemValue beta v ρ l <
            theorem4Problem11PolicyItemValue beta v ρ' l := by
  classical
  let x : Item n → ℝ := fun l => (ρ 0 l).toReal
  let z : Item n → ℝ := fun l => (ρ 2 l).toReal
  have hj_left : j.val < (reverseItem j).val := by
    have hne_val : j.val ≠ (reverseItem j).val := by
      intro hval
      apply hj_noncenter
      ext
      exact hval
    omega
  have hi_left : i.val < (reverseItem i).val := by
    have hrev_lt : (reverseItem j).val < (reverseItem i).val :=
      reverseItem_val_lt_of_val_lt hij
    exact lt_trans (lt_trans hij hj_left) hrev_lt
  have hx_nonneg : ∀ l : Item n, 0 ≤ x l := by
    intro l
    exact ENNReal.toReal_nonneg
  have hz_nonneg : ∀ l : Item n, 0 ≤ z l := by
    intro l
    exact ENNReal.toReal_nonneg
  have hsumx : (∑ l : Item n, x l) = 1 := by
    dsimp [x]
    exact AppliedModelingLib.pmfToRealSum (ρ 0)
  have hsumz : (∑ l : Item n, z l) = 1 := by
    dsimp [z]
    exact AppliedModelingLib.pmfToRealSum (ρ 2)
  have hzmirror : ∀ l : Item n, z (reverseItem l) = z l := by
    intro l
    dsimp [z]
    exact congrArg ENNReal.toReal (h.mirror.2 l)
  have hzi_pos : 0 < z i := by
    dsimp [z]
    have htoReal_ne : (ρ 2 i).toReal ≠ 0 := by
      intro hzero
      rcases (ENNReal.toReal_eq_zero_iff (ρ 2 i)).mp hzero with hzero_enn | htop
      · exact hzi_ne hzero_enn
      · exact (ρ 2).apply_ne_top i htop
    exact lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm htoReal_ne)
  have hzj : z j = 0 := by
    dsimp [z]
    simp [hzj_zero]
  have hxrevi_policy : ρ 0 (reverseItem i) = 0 := by
    apply hright_zero
    simpa [reverseItem_reverseItem] using hi_left
  have hxrevj_policy : ρ 0 (reverseItem j) = 0 := by
    apply hright_zero
    simpa [reverseItem_reverseItem] using hj_left
  have hxrevi : x (reverseItem i) = 0 := by
    dsimp [x]
    simp [hxrevi_policy]
  have hxrevj : x (reverseItem j) = 0 := by
    dsimp [x]
    simp [hxrevj_policy]
  have hxj_ne_policy : ρ 0 j ≠ 0 := by
    rcases theorem4Problem11_item_coverage_of_equalized_policyOptimal h j with
      hxj_ne | hxrevj_ne | hzj_ne
    · exact hxj_ne
    · exact False.elim (hxrevj_ne hxrevj_policy)
    · exact False.elim (hzj_ne hzj_zero)
  have hxj_pos : 0 < x j := by
    dsimp [x]
    have htoReal_ne : (ρ 0 j).toReal ≠ 0 := by
      intro hzero
      rcases (ENNReal.toReal_eq_zero_iff (ρ 0 j)).mp hzero with hzero_enn | htop
      · exact hxj_ne_policy hzero_enn
      · exact (ρ 0).apply_ne_top j htop
    exact lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm htoReal_ne)
  obtain ⟨x', z', hx'_nonneg, hz'_nonneg, hx'_sum, hz'_sum,
      hz'_mirror, hstrict⟩ :=
    theorem4Problem11_coldStartGap_pairTransfer_exists_strictlyImproves
      hn hbeta_pos hbeta_half hpos hdec hij hj_left hx_nonneg hz_nonneg
      hsumx hsumz hzmirror hzi_pos hzj hxj_pos hxrevi hxrevj
  let y' : Item n → ℝ := fun l => x' (reverseItem l)
  have hy'_nonneg : ∀ l : Item n, 0 ≤ y' l := by
    intro l
    exact hx'_nonneg (reverseItem l)
  have hy'_sum : (∑ l : Item n, y' l) = 1 := by
    dsimp [y']
    rw [sum_reverseItem x', hx'_sum]
  let ρ' : TypePolicy 3 n := fun k =>
    if k = 0 then
      pmfOfRealVector x' hx'_nonneg hx'_sum
    else if k = 1 then
      pmfOfRealVector y' hy'_nonneg hy'_sum
    else
      pmfOfRealVector z' hz'_nonneg hz'_sum
  have hsym' : Theorem4MirrorSymmetricPolicy ρ' := by
    constructor
    · intro l
      apply (ENNReal.toReal_eq_toReal_iff'
        ((ρ' 1).apply_ne_top (reverseItem l))
        ((ρ' 0).apply_ne_top l)).mp
      simp [ρ', y', reverseItem_reverseItem]
    · intro l
      apply (ENNReal.toReal_eq_toReal_iff'
        ((ρ' 2).apply_ne_top (reverseItem l))
        ((ρ' 2).apply_ne_top l)).mp
      simp [ρ', hz'_mirror l]
  refine ⟨ρ', hsym', ?_⟩
  intro l
  unfold theorem4Problem11PolicyItemValue
  simpa [ρ', x, z] using hstrict l

set_option maxHeartbeats 800000 in
-- The center cold-start certificate combines a center-specific z-transfer with a full item split.
theorem theorem4Problem11_coldStartGap_centerTransfer_exists_strictlyImproves
    {n : ℕ} {beta : ℝ} {v x z : Item n → ℝ} {i c : Item n}
    (hn : 2 < n)
    (hbeta_pos : 0 < beta)
    (hbeta_half : beta < 1 / 2)
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hic : i.val < c.val)
    (hc_center : reverseItem c = c)
    (hx_nonneg : ∀ l : Item n, 0 ≤ x l)
    (hz_nonneg : ∀ l : Item n, 0 ≤ z l)
    (hsumx : (∑ l : Item n, x l) = 1)
    (hsumz : (∑ l : Item n, z l) = 1)
    (hzmirror : ∀ l : Item n, z (reverseItem l) = z l)
    (hzi_pos : 0 < z i)
    (hzc : z c = 0)
    (hxc_pos : 0 < x c)
    (hxrevi : x (reverseItem i) = 0) :
    ∃ x' z' : Item n → ℝ,
      (∀ l : Item n, 0 ≤ x' l) ∧
      (∀ l : Item n, 0 ≤ z' l) ∧
      (∑ l : Item n, x' l) = 1 ∧
      (∑ l : Item n, z' l) = 1 ∧
      (∀ l : Item n, z' (reverseItem l) = z' l) ∧
      ∀ l : Item n,
        theorem4Problem11ItemValue beta v x z l <
          theorem4Problem11ItemValue beta v x' z' l := by
  classical
  let cold : ℝ := 1 - 2 * beta
  have hcold_pos : 0 < cold := by
    dsimp [cold]
    nlinarith
  have hci_ne : c ≠ i := by
    intro h
    subst c
    omega
  have hic_ne : i ≠ c := hci_ne.symm
  have hi_left : i.val < (reverseItem i).val := by
    have hrev_lt : c.val < (reverseItem i).val := by
      simpa [hc_center] using reverseItem_val_lt_of_val_lt hic
    exact lt_trans hic hrev_lt
  have hi_revi : i ≠ reverseItem i := by
    intro h
    have hval := congrArg Fin.val h
    omega
  have hrevi_c : reverseItem i ≠ c := by
    intro h
    have hrev_lt : c.val < (reverseItem i).val := by
      simpa [hc_center] using reverseItem_val_lt_of_val_lt hic
    have hval := congrArg Fin.val h
    omega
  let qi : ℝ := pairShare (1 / 2) v i
  have hqi_half : (1 / 2 : ℝ) < qi := by
    dsimp [qi]
    exact half_lt_pairShare_half_of_val_lt_reverse i hpos hdec hi_left
  have hqi_pos : 0 < qi := lt_trans (by norm_num) hqi_half
  let deltaBound : ℝ := cold * z i / (4 * beta * qi)
  have hdeltaDen_pos : 0 < 4 * beta * qi := by
    nlinarith
  have hdeltaBound_pos : 0 < deltaBound := by
    dsimp [deltaBound]
    exact div_pos (mul_pos hcold_pos hzi_pos) hdeltaDen_pos
  let delta : ℝ := min (x c) deltaBound / 2
  have hmin_delta_pos : 0 < min (x c) deltaBound :=
    lt_min hxc_pos hdeltaBound_pos
  have hdelta_pos : 0 < delta := by
    dsimp [delta]
    nlinarith
  have hdelta_lt_min : delta < min (x c) deltaBound := by
    dsimp [delta]
    nlinarith
  have hdelta_lt_xc : delta < x c :=
    lt_of_lt_of_le hdelta_lt_min (min_le_left _ _)
  have hdelta_lt_bound : delta < deltaBound :=
    lt_of_lt_of_le hdelta_lt_min (min_le_right _ _)
  have hupper_lt_zi :
      2 * beta * qi * delta / cold < z i := by
    have hmul : 2 * beta * qi * delta < cold * z i := by
      have := hdelta_lt_bound
      dsimp [deltaBound] at this
      rw [lt_div_iff₀ hdeltaDen_pos] at this
      nlinarith
    rw [div_lt_iff₀ hcold_pos]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  let lower : ℝ := beta * delta / cold
  let upper : ℝ := 2 * beta * qi * delta / cold
  have hlower_lt_upper : lower < upper := by
    have hfactor_pos : 0 < beta * delta / cold :=
      div_pos (mul_pos hbeta_pos hdelta_pos) hcold_pos
    have htwo_qi : (1 : ℝ) < 2 * qi := by nlinarith
    calc
      lower = 1 * (beta * delta / cold) := by
        dsimp [lower]
        ring
      _ < (2 * qi) * (beta * delta / cold) :=
        mul_lt_mul_of_pos_right htwo_qi hfactor_pos
      _ = upper := by
        dsimp [upper]
        ring
  obtain ⟨d, hd_lower, hd_upper⟩ := exists_between hlower_lt_upper
  have hlower_pos : 0 < lower := by
    dsimp [lower]
    exact div_pos (mul_pos hbeta_pos hdelta_pos) hcold_pos
  have hd_pos : 0 < d := lt_trans hlower_pos hd_lower
  have hd_nonneg : 0 ≤ d := hd_pos.le
  have hd_lt_zi : d < z i := lt_trans hd_upper hupper_lt_zi
  let slack : ℝ := d - lower
  have hslack_pos : 0 < slack := by
    dsimp [slack]
    linarith
  let eps : ℝ := min d slack / 2
  have hmin_eps_pos : 0 < min d slack := lt_min hd_pos hslack_pos
  have heps_pos : 0 < eps := by
    dsimp [eps]
    nlinarith
  have heps_lt_min : eps < min d slack := by
    dsimp [eps]
    nlinarith
  have heps_lt_d : eps < d :=
    lt_of_lt_of_le heps_lt_min (min_le_left _ _)
  have heps_lt_slack : eps < slack :=
    lt_of_lt_of_le heps_lt_min (min_le_right _ _)
  obtain ⟨r, hr_nonneg, hr_pos, hrc, hri, hrsum⟩ :=
    lemma4_redistribution_exists_of_two_lt hn hci_ne
  let x' : Item n → ℝ := theorem4Problem11TwoPointXTransfer x i c delta
  let z' : Item n → ℝ :=
    theorem4Problem11ColdStartCenterZTransfer z r i c d eps
  have hx'_nonneg : ∀ l : Item n, 0 ≤ x' l := by
    intro l
    exact theorem4Problem11TwoPointXTransfer_nonneg
      hx_nonneg hic_ne hdelta_pos.le hdelta_lt_xc.le l
  have hz'_nonneg : ∀ l : Item n, 0 ≤ z' l := by
    intro l
    dsimp [z']
    exact theorem4Problem11ColdStartCenterZTransfer_nonneg
      hz_nonneg hzmirror hc_center hi_revi hic_ne hrevi_c hr_nonneg hrc
      hd_nonneg heps_pos.le heps_lt_d.le hd_lt_zi.le l
  have hx'_sum : (∑ l : Item n, x' l) = 1 := by
    dsimp [x']
    rw [theorem4Problem11TwoPointXTransfer_sum_eq x i c delta, hsumx]
  have hz'_sum : (∑ l : Item n, z' l) = 1 := by
    dsimp [z']
    rw [theorem4Problem11ColdStartCenterZTransfer_sum_eq z r i c d eps hrsum,
      hsumz]
  have hz'_mirror : ∀ l : Item n, z' (reverseItem l) = z' l := by
    dsimp [z']
    exact theorem4Problem11ColdStartCenterZTransfer_mirror
      hzmirror hc_center hi_revi hic_ne hrevi_c
  have hx'i : x' i = x i + delta := by
    dsimp [x']
    unfold theorem4Problem11TwoPointXTransfer
    simp [hic_ne]
  have hx'c : x' c = x c - delta := by
    dsimp [x']
    unfold theorem4Problem11TwoPointXTransfer
    simp [hic_ne.symm]
    ring
  have hx'revi : x' (reverseItem i) = 0 := by
    dsimp [x']
    unfold theorem4Problem11TwoPointXTransfer
    simp [hxrevi, hi_revi.symm, hrevi_c]
  have hz'i :
      z' i = z i - d + eps * r i + eps * r (reverseItem i) := by
    dsimp [z']
    unfold theorem4Problem11ColdStartCenterZTransfer
    simp [hi_revi, hic_ne]
    ring
  have hz'c : z' c = z c + (2 * d - 2 * eps) := by
    dsimp [z']
    exact theorem4Problem11ColdStartCenterZTransfer_apply_center
      hc_center hic_ne hrevi_c hrc
  have hstrict_i :
      theorem4Problem11ItemValue beta v x z i <
        theorem4Problem11ItemValue beta v x' z' i := by
    unfold theorem4Problem11ItemValue
    change
      2 * beta * (qi * x i + (1 - qi) * x (reverseItem i)) +
          cold * z i <
        2 * beta * (qi * x' i + (1 - qi) * x' (reverseItem i)) +
          cold * z' i
    rw [hxrevi, hx'i, hx'revi, hz'i]
    have hmain_gain : 0 < 2 * beta * qi * delta - cold * d := by
      have hlt := hd_upper
      dsimp [upper] at hlt
      rw [lt_div_iff₀ hcold_pos] at hlt
      have hlt' : cold * d < 2 * beta * qi * delta := by
        nlinarith [hlt]
      exact sub_pos.mpr hlt'
    have hredistrib_nonneg :
        0 ≤ cold * (eps * r i + eps * r (reverseItem i)) := by
      exact mul_nonneg hcold_pos.le
        (add_nonneg
          (mul_nonneg heps_pos.le (hr_nonneg i))
          (mul_nonneg heps_pos.le (hr_nonneg (reverseItem i))))
    nlinarith only [hmain_gain, hredistrib_nonneg]
  have hstrict_c :
      theorem4Problem11ItemValue beta v x z c <
        theorem4Problem11ItemValue beta v x' z' c := by
    unfold theorem4Problem11ItemValue
    rw [hc_center, hx'c, hz'c, hzc]
    have hcenter_gain : 0 < cold * (2 * d - 2 * eps) - 2 * beta * delta := by
      have heps_small := heps_lt_slack
      dsimp [slack, lower] at heps_small
      have hlt :
          cold * eps < cold * (d - beta * delta / cold) :=
        mul_lt_mul_of_pos_left heps_small hcold_pos
      rw [mul_sub, mul_div_cancel₀ _ (ne_of_gt hcold_pos)] at hlt
      nlinarith only [hlt]
    ring_nf at hcenter_gain ⊢
    linarith
  refine ⟨x', z', hx'_nonneg, hz'_nonneg, hx'_sum, hz'_sum,
    hz'_mirror, ?_⟩
  intro l
  by_cases hli : l = i
  · subst l
    exact hstrict_i
  · by_cases hlrevi : l = reverseItem i
    · subst l
      have horig :=
        theorem4Problem11ItemValue_reverse_eq
          (beta := beta) (v := v) (x := x) (z := z) hpos hzmirror i
      have hnew :=
        theorem4Problem11ItemValue_reverse_eq
          (beta := beta) (v := v) (x := x') (z := z') hpos hz'_mirror i
      rw [horig, hnew]
      exact hstrict_i
    · by_cases hlc : l = c
      · subst l
        exact hstrict_c
      · have hrev_li : reverseItem l ≠ i :=
          reverseItem_ne_of_ne_reverse hlrevi
        have hrev_lc : reverseItem l ≠ c := by
          have hl_rev_c : l ≠ reverseItem c := by
            simpa [hc_center] using hlc
          exact reverseItem_ne_of_ne_reverse hl_rev_c
        have hxl' : x' l = x l := by
          dsimp [x']
          exact theorem4Problem11TwoPointXTransfer_apply_of_ne hli hlc
        have hxrev' : x' (reverseItem l) = x (reverseItem l) := by
          dsimp [x']
          exact theorem4Problem11TwoPointXTransfer_apply_of_ne hrev_li hrev_lc
        have hzl' :
            z' l = z l + eps * r l + eps * r (reverseItem l) := by
          dsimp [z']
          exact theorem4Problem11ColdStartCenterZTransfer_apply_of_ne
            hli hlrevi hlc
        have hrl_pos : 0 < r l := hr_pos hlc hli
        have hredistrib_pos :
            0 < eps * r l + eps * r (reverseItem l) := by
          exact theorem4Problem11_symmetricRedistribution_pos
            (n := n) (r := r) (eps := eps) (l := l)
            heps_pos hrl_pos (hr_nonneg (reverseItem l))
        have hzlt : z l < z' l := by
          rw [hzl']
          calc
            z l < z l + (eps * r l + eps * r (reverseItem l)) :=
              lt_add_of_pos_right (z l) hredistrib_pos
            _ = z l + eps * r l + eps * r (reverseItem l) := by ring
        exact theorem4Problem11ItemValue_lt_of_same_x_strict_z
          (n := n) (beta := beta) (v := v) (x := x) (x' := x')
          (z := z) (z' := z') (j := l) hcold_pos hxl' hxrev' hzlt

theorem theorem4Problem11_coldStartGapStrictImprovement_center_of_equalizedBasicOptimal
    {n : ℕ} [NeZero n] {beta ell : ℝ} {v : Item n → ℝ}
    {ρ : TypePolicy 3 n}
    (hn : 2 < n)
    (hbeta_pos : 0 < beta)
    (hbeta_half : beta < 1 / 2)
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (h : Theorem4Problem11EqualizedBasicOptimal beta v ρ ell)
    (hright_zero :
      ∀ u : Item n, (reverseItem u).val < u.val → ρ 0 u = 0)
    {i j : Item n}
    (hij : i.val < j.val)
    (hzi_ne : ρ 2 i ≠ 0)
    (hzj_zero : ρ 2 j = 0)
    (hj_center : reverseItem j = j) :
    ∃ ρ' : TypePolicy 3 n,
      Theorem4MirrorSymmetricPolicy ρ' ∧
        ∀ l : Item n,
          theorem4Problem11PolicyItemValue beta v ρ l <
            theorem4Problem11PolicyItemValue beta v ρ' l := by
  classical
  let x : Item n → ℝ := fun l => (ρ 0 l).toReal
  let z : Item n → ℝ := fun l => (ρ 2 l).toReal
  have hi_left : i.val < (reverseItem i).val := by
    have hrev_lt : j.val < (reverseItem i).val := by
      simpa [hj_center] using reverseItem_val_lt_of_val_lt hij
    exact lt_trans hij hrev_lt
  have hx_nonneg : ∀ l : Item n, 0 ≤ x l := by
    intro l
    exact ENNReal.toReal_nonneg
  have hz_nonneg : ∀ l : Item n, 0 ≤ z l := by
    intro l
    exact ENNReal.toReal_nonneg
  have hsumx : (∑ l : Item n, x l) = 1 := by
    dsimp [x]
    exact AppliedModelingLib.pmfToRealSum (ρ 0)
  have hsumz : (∑ l : Item n, z l) = 1 := by
    dsimp [z]
    exact AppliedModelingLib.pmfToRealSum (ρ 2)
  have hzmirror : ∀ l : Item n, z (reverseItem l) = z l := by
    intro l
    dsimp [z]
    exact congrArg ENNReal.toReal (h.mirror.2 l)
  have hzi_pos : 0 < z i := by
    dsimp [z]
    have htoReal_ne : (ρ 2 i).toReal ≠ 0 := by
      intro hzero
      rcases (ENNReal.toReal_eq_zero_iff (ρ 2 i)).mp hzero with hzero_enn | htop
      · exact hzi_ne hzero_enn
      · exact (ρ 2).apply_ne_top i htop
    exact lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm htoReal_ne)
  have hzj : z j = 0 := by
    dsimp [z]
    simp [hzj_zero]
  have hxrevi_policy : ρ 0 (reverseItem i) = 0 := by
    apply hright_zero
    simpa [reverseItem_reverseItem] using hi_left
  have hxrevi : x (reverseItem i) = 0 := by
    dsimp [x]
    simp [hxrevi_policy]
  have hxj_ne_policy : ρ 0 j ≠ 0 := by
    rcases theorem4Problem11_item_coverage_of_equalized_policyOptimal h j with
      hxj_ne | hxrevj_ne | hzj_ne
    · exact hxj_ne
    · rw [hj_center] at hxrevj_ne
      exact hxrevj_ne
    · exact False.elim (hzj_ne hzj_zero)
  have hxj_pos : 0 < x j := by
    dsimp [x]
    have htoReal_ne : (ρ 0 j).toReal ≠ 0 := by
      intro hzero
      rcases (ENNReal.toReal_eq_zero_iff (ρ 0 j)).mp hzero with hzero_enn | htop
      · exact hxj_ne_policy hzero_enn
      · exact (ρ 0).apply_ne_top j htop
    exact lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm htoReal_ne)
  obtain ⟨x', z', hx'_nonneg, hz'_nonneg, hx'_sum, hz'_sum,
      hz'_mirror, hstrict⟩ :=
    theorem4Problem11_coldStartGap_centerTransfer_exists_strictlyImproves
      hn hbeta_pos hbeta_half hpos hdec hij hj_center hx_nonneg hz_nonneg
      hsumx hsumz hzmirror hzi_pos hzj hxj_pos hxrevi
  let y' : Item n → ℝ := fun l => x' (reverseItem l)
  have hy'_nonneg : ∀ l : Item n, 0 ≤ y' l := by
    intro l
    exact hx'_nonneg (reverseItem l)
  have hy'_sum : (∑ l : Item n, y' l) = 1 := by
    dsimp [y']
    rw [sum_reverseItem x', hx'_sum]
  let ρ' : TypePolicy 3 n := fun k =>
    if k = 0 then
      pmfOfRealVector x' hx'_nonneg hx'_sum
    else if k = 1 then
      pmfOfRealVector y' hy'_nonneg hy'_sum
    else
      pmfOfRealVector z' hz'_nonneg hz'_sum
  have hsym' : Theorem4MirrorSymmetricPolicy ρ' := by
    constructor
    · intro l
      apply (ENNReal.toReal_eq_toReal_iff'
        ((ρ' 1).apply_ne_top (reverseItem l))
        ((ρ' 0).apply_ne_top l)).mp
      simp [ρ', y', reverseItem_reverseItem]
    · intro l
      apply (ENNReal.toReal_eq_toReal_iff'
        ((ρ' 2).apply_ne_top (reverseItem l))
        ((ρ' 2).apply_ne_top l)).mp
      simp [ρ', hz'_mirror l]
  refine ⟨ρ', hsym', ?_⟩
  intro l
  unfold theorem4Problem11PolicyItemValue
  simpa [ρ', x, z] using hstrict l

theorem theorem4Problem11_coldStartGapStrictImprovement_of_equalizedBasicOptimal
    {n : ℕ} [NeZero n] {beta ell : ℝ} {v : Item n → ℝ}
    {ρ : TypePolicy 3 n}
    (hn : 2 < n)
    (hbeta_pos : 0 < beta)
    (hbeta_half : beta < 1 / 2)
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (h : Theorem4Problem11EqualizedBasicOptimal beta v ρ ell) :
    Theorem4Problem11ColdStartGapStrictImprovement beta v ρ := by
  have hno : Theorem4Problem11PolicyNoStrictPointwiseImprovement beta v ρ :=
    theorem4Problem11_noStrictPointwiseImprovement_of_equalizedBasicOptimal h
  have hright_zero :
      ∀ u : Item n, (reverseItem u).val < u.val → ρ 0 u = 0 :=
    theorem4Problem11_typeZero_zero_after_mirror_of_noStrictPointwiseImprovement
      hn hbeta_pos hpos hdec h.mirror hno
  intro i j hij hj_half hzi_ne hzj_zero
  by_cases hj_center : j = reverseItem j
  · exact theorem4Problem11_coldStartGapStrictImprovement_center_of_equalizedBasicOptimal
      hn hbeta_pos hbeta_half hpos hdec h hright_zero hij hzi_ne hzj_zero
      hj_center.symm
  · exact theorem4Problem11_coldStartGapStrictImprovement_noncenter_of_equalizedBasicOptimal
      hn hbeta_pos hbeta_half hpos hdec h hright_zero hij hj_half hzi_ne
      hzj_zero hj_center

theorem theorem4Problem11_typeZeroZeroClosed_of_gapStrictImprovement
    {n : ℕ} {beta : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 3 n}
    (hgap : Theorem4Problem11TypeZeroGapStrictImprovement beta v ρ)
    (hno : Theorem4Problem11PolicyNoStrictPointwiseImprovement beta v ρ) :
    Theorem4Problem11TypeZeroZeroClosed ρ := by
  intro i j hij hi_zero
  by_contra hj_ne
  exact hno (hgap hij hi_zero hj_ne)

theorem theorem4Problem11_coldStartPositiveClosed_of_gapStrictImprovement
    {n : ℕ} {beta : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 3 n}
    (hgap : Theorem4Problem11ColdStartGapStrictImprovement beta v ρ)
    (hno : Theorem4Problem11PolicyNoStrictPointwiseImprovement beta v ρ) :
    Theorem4Problem11ColdStartPositiveClosed ρ := by
  intro i j hij hj_half hi_pos hj_zero
  exact hno (hgap hij hj_half hi_pos hj_zero)

/-- Items used with positive probability by Problem 11's known-type row. -/
noncomputable def theorem4Problem11TypeZeroActiveItems {n : ℕ}
    (ρ : TypePolicy 3 n) : Finset (Item n) :=
  Finset.univ.filter fun j => ρ 0 j ≠ 0

theorem theorem4Problem11TypeZeroActiveItems_nonempty {n : ℕ} [NeZero n]
    (ρ : TypePolicy 3 n) :
    (theorem4Problem11TypeZeroActiveItems ρ).Nonempty := by
  rcases TypePolicy.exists_active_item_for_type ρ 0 with ⟨j, hj⟩
  exact ⟨j, by simp [theorem4Problem11TypeZeroActiveItems, hj]⟩

/-- Problem 11 pivot candidate: the last item with positive known-type mass. -/
noncomputable def theorem4Problem11LastActiveTypeZero {n : ℕ} [NeZero n]
    (ρ : TypePolicy 3 n) : Item n :=
  (theorem4Problem11TypeZeroActiveItems ρ).max'
    (theorem4Problem11TypeZeroActiveItems_nonempty ρ)

theorem theorem4Problem11LastActiveTypeZero_active {n : ℕ} [NeZero n]
    (ρ : TypePolicy 3 n) :
    ρ 0 (theorem4Problem11LastActiveTypeZero ρ) ≠ 0 := by
  have hmem :=
    Finset.max'_mem (theorem4Problem11TypeZeroActiveItems ρ)
      (theorem4Problem11TypeZeroActiveItems_nonempty ρ)
  simpa [theorem4Problem11LastActiveTypeZero,
    theorem4Problem11TypeZeroActiveItems] using hmem

theorem theorem4Problem11_typeZero_zero_after_lastActive {n : ℕ}
    [NeZero n] (ρ : TypePolicy 3 n) {j : Item n}
    (hj : (theorem4Problem11LastActiveTypeZero ρ).val < j.val) :
    ρ 0 j = 0 := by
  by_contra hne
  have hmem : j ∈ theorem4Problem11TypeZeroActiveItems ρ := by
    simp [theorem4Problem11TypeZeroActiveItems, hne]
  have hle :
      j ≤ theorem4Problem11LastActiveTypeZero ρ := by
    simpa [theorem4Problem11LastActiveTypeZero] using
      (theorem4Problem11TypeZeroActiveItems ρ).le_max' j hmem
  have hle_val : j.val ≤ (theorem4Problem11LastActiveTypeZero ρ).val := hle
  omega

theorem theorem4Problem11_typeZero_active_before_lastActive_of_zeroClosed
    {n : ℕ} [NeZero n] (ρ : TypePolicy 3 n)
    (hx : Theorem4Problem11TypeZeroZeroClosed ρ) {j : Item n}
    (hj : j.val < (theorem4Problem11LastActiveTypeZero ρ).val) :
    ρ 0 j ≠ 0 := by
  by_contra hz
  exact theorem4Problem11LastActiveTypeZero_active ρ (hx hj hz)

theorem theorem4Problem11LastActiveTypeZero_le_reverse_of_equalizedBasicOptimal
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    {ρ : TypePolicy 3 n} {ell : ℝ}
    (hn : 2 < n)
    (hbeta_pos : 0 < beta)
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (h : Theorem4Problem11EqualizedBasicOptimal beta v ρ ell) :
    (theorem4Problem11LastActiveTypeZero ρ).val ≤
      (reverseItem (theorem4Problem11LastActiveTypeZero ρ)).val := by
  have hno : Theorem4Problem11PolicyNoStrictPointwiseImprovement beta v ρ :=
    theorem4Problem11_noStrictPointwiseImprovement_of_equalizedBasicOptimal h
  have hright_zero :
      ∀ j : Item n, (reverseItem j).val < j.val → ρ 0 j = 0 :=
    theorem4Problem11_typeZero_zero_after_mirror_of_noStrictPointwiseImprovement
      hn hbeta_pos hpos hdec h.mirror hno
  by_contra hnot
  have hrev_lt :
      (reverseItem (theorem4Problem11LastActiveTypeZero ρ)).val <
        (theorem4Problem11LastActiveTypeZero ρ).val := by
    omega
  have hz0 :=
    hright_zero (theorem4Problem11LastActiveTypeZero ρ) hrev_lt
  exact theorem4Problem11LastActiveTypeZero_active ρ hz0

theorem theorem4Problem11_sharedItems_of_active_types
    {n : ℕ} (ρ : TypePolicy 3 n) {j : Item n}
    {k k' : UserType 3}
    (hne : k ≠ k') (hk : ρ k j ≠ 0) (hk' : ρ k' j ≠ 0) :
    j ∈ TypePolicy.sharedItems ρ := by
  simp [TypePolicy.sharedItems]
  exact ⟨k, k', hne, hk, hk'⟩

/-! ### Appendix E, Lemma 15: ruling out pivot `t = 1` -/

/-- Lemma 15's closed-form `λ` when the Problem 11 pivot is item `1`. -/
noncomputable def theorem4Problem11PivotOneLambda {n : ℕ} [NeZero n]
    (beta : ℝ) (v : Item n → ℝ) : ℝ :=
  (2 * beta * pairShare (1 / 2) v theorem4FirstItem +
      (1 / 2) * (1 - 2 * beta)) /
    (1 + (1 / 2) * ((n : ℝ) - 2))

/-- Lemma 15's closed-form pivot coordinate `z₁` when the pivot is item `1`. -/
noncomputable def theorem4Problem11PivotOneZ {n : ℕ} [NeZero n]
    (beta : ℝ) (v : Item n → ℝ) : ℝ :=
  (1 / 2) *
    (1 - ((n : ℝ) - 2) *
      theorem4Problem11PivotOneLambda beta v / (1 - 2 * beta))

theorem theorem4Problem11PivotOneLambda_gt_inv_card
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hn : 1 < n)
    (hbeta : (n : ℝ)⁻¹ < beta)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v) :
    (n : ℝ)⁻¹ < theorem4Problem11PivotOneLambda beta v := by
  have hnpos_nat : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  have hinv_pos : 0 < (n : ℝ)⁻¹ := inv_pos.mpr hnpos
  have hbeta_pos : 0 < beta := lt_trans hinv_pos hbeta
  have hfirst_before :
      (theorem4FirstItem : Item n).val <
        (reverseItem (theorem4FirstItem : Item n)).val := by
    simp [theorem4FirstItem, reverseItem]
    omega
  have hq :
      (1 / 2 : ℝ) <
        pairShare (1 / 2) v (theorem4FirstItem : Item n) :=
    half_lt_pairShare_half_of_val_lt_reverse
      (theorem4FirstItem : Item n) hpos hdec hfirst_before
  have hnum :
      (1 / 2 : ℝ) <
        2 * beta * pairShare (1 / 2) v (theorem4FirstItem : Item n) +
          (1 / 2) * (1 - 2 * beta) := by
    nlinarith
  have hden_eq :
      1 + (1 / 2 : ℝ) * ((n : ℝ) - 2) = (n : ℝ) / 2 := by
    ring
  have hden_pos : 0 < (n : ℝ) / 2 := by positivity
  have hscale :
      (n : ℝ)⁻¹ * ((n : ℝ) / 2) = (1 / 2 : ℝ) := by
    field_simp [ne_of_gt hnpos]
  unfold theorem4Problem11PivotOneLambda
  rw [hden_eq]
  rw [lt_div_iff₀ hden_pos]
  rw [hscale]
  exact hnum

theorem theorem4Problem11PivotOneZ_neg
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hn : 2 < n)
    (hbeta : (n : ℝ)⁻¹ < beta)
    (hbeta_half : beta < 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v) :
    theorem4Problem11PivotOneZ beta v < 0 := by
  have hnpos_nat : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  have hn_one : 1 < n := by omega
  have hlambda :
      (n : ℝ)⁻¹ < theorem4Problem11PivotOneLambda beta v :=
    theorem4Problem11PivotOneLambda_gt_inv_card
      hn_one hbeta hpos hdec
  have hnminus_pos : 0 < (n : ℝ) - 2 := by
    have hn_real : (2 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    linarith
  have hthreshold :
      1 - 2 * beta < ((n : ℝ) - 2) * (n : ℝ)⁻¹ := by
    have hcalc :
        ((n : ℝ) - 2) * (n : ℝ)⁻¹ =
          1 - 2 * (n : ℝ)⁻¹ := by
      field_simp [ne_of_gt hnpos]
    rw [hcalc]
    nlinarith
  have hprod :
      1 - 2 * beta <
        ((n : ℝ) - 2) * theorem4Problem11PivotOneLambda beta v := by
    exact lt_trans hthreshold
      (mul_lt_mul_of_pos_left hlambda hnminus_pos)
  have hcold_pos : 0 < 1 - 2 * beta := by
    nlinarith
  have hdiv :
      1 <
        ((n : ℝ) - 2) * theorem4Problem11PivotOneLambda beta v /
          (1 - 2 * beta) := by
    rw [lt_div_iff₀ hcold_pos]
    simpa using hprod
  unfold theorem4Problem11PivotOneZ
  nlinarith

/--
If Lemma 15's pivot-one closed form is imposed on an actual PMF coordinate,
the pivot-one case is impossible under the Theorem 4 `β > 1/n` assumptions.
-/
theorem theorem4Problem11PivotOne_closedZ_impossible
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hn : 2 < n)
    (hbeta : (n : ℝ)⁻¹ < beta)
    (hbeta_half : beta < 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (ρ : TypePolicy 3 n)
    (hz :
      (ρ 2 theorem4FirstItem).toReal =
        theorem4Problem11PivotOneZ beta v) :
    False := by
  have hneg :
      theorem4Problem11PivotOneZ beta v < 0 :=
    theorem4Problem11PivotOneZ_neg hn hbeta hbeta_half hpos hdec
  have hnonneg : 0 ≤ (ρ 2 theorem4FirstItem).toReal :=
    ENNReal.toReal_nonneg
  rw [hz] at hnonneg
  linarith

/-! ### Appendix E, Lemma 13 pivot-support interface -/

/--
Appendix E, Lemma 13 pivot-support shape for Problem 11: the known-type row
has no mass strictly after the pivot, while the cold-start row has no mass
strictly before the pivot or its mirror.
-/
def Theorem4Problem11PivotSupport {n : ℕ}
    (ρ : TypePolicy 3 n) (t : Item n) : Prop :=
  (∀ j : Item n, t.val < j.val → ρ 0 j = 0) ∧
    (∀ j : Item n, j.val < t.val →
      ρ 2 j = 0 ∧ ρ 2 (reverseItem j) = 0)

theorem theorem4Problem11PolicyOptimal_pivotSupport_of_closedDual_tight {n : ℕ}
    [NeZero n] {beta : ℝ} {v : Item n → ℝ} {t : Item n}
    {ρ : TypePolicy 3 n} {ell : ℝ}
    (hbeta_pos : 0 < beta)
    (hbeta_half : beta < 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hleft : t.val ≤ (reverseItem t).val)
    (hvalue : ell = theorem4Problem11ClosedDualValue beta v t)
    (hopt : Theorem4Problem11PolicyOptimal beta v ρ ell) :
    Theorem4Problem11PivotSupport ρ t := by
  let x : Item n → ℝ := fun j => (ρ 0 j).toReal
  let z : Item n → ℝ := fun j => (ρ 2 j).toReal
  let cert :
      Theorem4Problem11DualCertificate beta v
        (theorem4Problem11ClosedDualWeight v t)
        (theorem4Problem11ClosedKnownBudget beta v t)
        (theorem4Problem11ClosedColdBudget beta v t)
        (theorem4Problem11ClosedDualValue beta v t) :=
    theorem4Problem11ClosedDualCertificate
      hbeta_pos.le (by nlinarith) hpos hdec hleft
  have hfeas : Theorem4Problem11RealLPFeasible beta v x z ell := by
    dsimp [x, z]
    exact theorem4Problem11RealLPFeasible_of_policy hopt.1 hopt.2.1
  have hitem :
      ∀ j : Item n, theorem4Problem11ItemValue beta v x z j = ell := by
    have hpolicy :=
      theorem4Problem11PolicyOptimal_item_eq_of_closedDual_tight
        hbeta_pos hbeta_half hpos hdec hleft hvalue hopt
    intro j
    simpa [x, z, theorem4Problem11PolicyItemValue,
      theorem4Problem11ItemValue] using hpolicy j
  constructor
  · intro j hj
    have hx : x j = 0 :=
      theorem4Problem11DualCertificate_x_eq_zero_of_tight_coeff_lt
        hpos cert hfeas hitem hvalue
        (theorem4Problem11ClosedDualWeight_x_coeff_lt_of_pivot_lt
          hbeta_pos hpos hdec hleft hj)
    apply pmf_apply_eq_zero_of_toReal_eq_zero
    simpa [x] using hx
  · intro j hj
    have hz : ρ 2 j = 0 := by
      have hzreal : z j = 0 :=
        theorem4Problem11DualCertificate_z_eq_zero_of_tight_coeff_lt
          hpos cert hfeas hitem hvalue
          (theorem4Problem11ClosedDualWeight_z_coeff_lt_of_lt_pivot
            hbeta_half hpos hdec hleft hj)
      apply pmf_apply_eq_zero_of_toReal_eq_zero
      simpa [z] using hzreal
    constructor
    · exact hz
    · rw [hopt.1.2 j, hz]

theorem theorem4Problem11PivotSupport_basicFeasibleSupportCertificate {n : ℕ}
    {ρ : TypePolicy 3 n} {t : Item n}
    (hmirror : Theorem4MirrorSymmetricPolicy ρ)
    (hleft : t.val ≤ (reverseItem t).val)
    (hpivot : Theorem4Problem11PivotSupport ρ t) :
    TypePolicy.BasicFeasibleSupportCertificate ρ := by
  classical
  let D0 : Type := {j : Item n // j ∈ (Finset.Ioi t : Finset (Item n))}
  let D1 : Type :=
    {j : Item n // j ∈ (Finset.Iio (reverseItem t) : Finset (Item n))}
  let D2 : Type := {j : Item n // j ∈ (Finset.Iio t : Finset (Item n))}
  let D3 : Type :=
    {j : Item n // j ∈ (Finset.Ioi (reverseItem t) : Finset (Item n))}
  let Domain : Type := (D0 ⊕ D1) ⊕ (D2 ⊕ D3)
  let f :
      Domain →
        {p : UserType 3 × Item n // p ∈ TypePolicy.inactiveTypeItemPairs ρ} :=
    fun d =>
      match d with
      | Sum.inl (Sum.inl j) =>
          ⟨(0, j.1), by
            have hj : t.val < j.1.val := by
              have hj' : t < j.1 := Finset.mem_Ioi.mp j.2
              exact hj'
            exact (TypePolicy.mem_inactiveTypeItemPairs ρ (0, j.1)).2
              (hpivot.1 j.1 hj)⟩
      | Sum.inl (Sum.inr j) =>
          ⟨(1, j.1), by
            have hj : j.1.val < (reverseItem t).val := by
              have hj' : j.1 < reverseItem t := Finset.mem_Iio.mp j.2
              exact hj'
            have hrev_after : t.val < (reverseItem j.1).val := by
              simpa [reverseItem_reverseItem] using
                (reverseItem_val_lt_of_val_lt hj)
            have hx : ρ 0 (reverseItem j.1) = 0 :=
              hpivot.1 (reverseItem j.1) hrev_after
            have hy : ρ 1 j.1 = 0 := by
              have hmir : ρ 1 j.1 = ρ 0 (reverseItem j.1) := by
                simpa [reverseItem_reverseItem] using
                  hmirror.1 (reverseItem j.1)
              rw [hmir, hx]
            exact (TypePolicy.mem_inactiveTypeItemPairs ρ (1, j.1)).2 hy⟩
      | Sum.inr (Sum.inl j) =>
          ⟨(2, j.1), by
            have hj : j.1.val < t.val := by
              have hj' : j.1 < t := Finset.mem_Iio.mp j.2
              exact hj'
            exact (TypePolicy.mem_inactiveTypeItemPairs ρ (2, j.1)).2
              (hpivot.2 j.1 hj).1⟩
      | Sum.inr (Sum.inr j) =>
          ⟨(2, j.1), by
            have hj : (reverseItem t).val < j.1.val := by
              have hj' : reverseItem t < j.1 := Finset.mem_Ioi.mp j.2
              exact hj'
            have hrev_before : (reverseItem j.1).val < t.val := by
              simpa [reverseItem_reverseItem] using
                (reverseItem_val_lt_of_val_lt hj)
            have hz : ρ 2 j.1 = 0 := by
              have hzero := (hpivot.2 (reverseItem j.1) hrev_before).2
              simpa [reverseItem_reverseItem] using hzero
            exact (TypePolicy.mem_inactiveTypeItemPairs ρ (2, j.1)).2 hz⟩
  have hf : Function.Injective f := by
    intro a b hab
    have hpair := congrArg (fun q :
      {p : UserType 3 × Item n // p ∈ TypePolicy.inactiveTypeItemPairs ρ} =>
        q.1) hab
    cases a with
    | inl a01 =>
        cases a01 with
        | inl a0 =>
            cases b with
            | inl b01 =>
                cases b01 with
                | inl b0 =>
                    have hitem : a0.1 = b0.1 := by
                      simpa [f] using congrArg Prod.snd hpair
                    exact congrArg Sum.inl (congrArg Sum.inl (Subtype.ext hitem))
                | inr b1 =>
                    have htype := congrArg Prod.fst hpair
                    simp [f] at htype
            | inr b23 =>
                cases b23 with
                | inl b2 =>
                    have htype := congrArg Prod.fst hpair
                    simp [f] at htype
                | inr b3 =>
                    have htype := congrArg Prod.fst hpair
                    simp [f] at htype
        | inr a1 =>
            cases b with
            | inl b01 =>
                cases b01 with
                | inl b0 =>
                    have htype := congrArg Prod.fst hpair
                    simp [f] at htype
                | inr b1 =>
                    have hitem : a1.1 = b1.1 := by
                      simpa [f] using congrArg Prod.snd hpair
                    exact congrArg Sum.inl (congrArg Sum.inr (Subtype.ext hitem))
            | inr b23 =>
                cases b23 with
                | inl b2 =>
                    have htype := congrArg Prod.fst hpair
                    simp [f] at htype
                | inr b3 =>
                    have htype := congrArg Prod.fst hpair
                    simp [f] at htype
    | inr a23 =>
        cases a23 with
        | inl a2 =>
            cases b with
            | inl b01 =>
                cases b01 with
                | inl b0 =>
                    have htype := congrArg Prod.fst hpair
                    simp [f] at htype
                | inr b1 =>
                    have htype := congrArg Prod.fst hpair
                    simp [f] at htype
            | inr b23 =>
                cases b23 with
                | inl b2 =>
                    have hitem : a2.1 = b2.1 := by
                      simpa [f] using congrArg Prod.snd hpair
                    exact congrArg Sum.inr (congrArg Sum.inl (Subtype.ext hitem))
                | inr b3 =>
                    have hitem : a2.1 = b3.1 := by
                      simpa [f] using congrArg Prod.snd hpair
                    have ha : a2.1.val < t.val := by
                      have ha' : a2.1 < t := Finset.mem_Iio.mp a2.2
                      exact ha'
                    have hb : (reverseItem t).val < a2.1.val := by
                      have hb' : reverseItem t < b3.1 :=
                        Finset.mem_Ioi.mp b3.2
                      rw [hitem]
                      exact hb'
                    omega
        | inr a3 =>
            cases b with
            | inl b01 =>
                cases b01 with
                | inl b0 =>
                    have htype := congrArg Prod.fst hpair
                    simp [f] at htype
                | inr b1 =>
                    have htype := congrArg Prod.fst hpair
                    simp [f] at htype
            | inr b23 =>
                cases b23 with
                | inl b2 =>
                    have hitem : a3.1 = b2.1 := by
                      simpa [f] using congrArg Prod.snd hpair
                    have ha : (reverseItem t).val < a3.1.val := by
                      have ha' : reverseItem t < a3.1 :=
                        Finset.mem_Ioi.mp a3.2
                      exact ha'
                    have hb : a3.1.val < t.val := by
                      have hb' : b2.1 < t := Finset.mem_Iio.mp b2.2
                      rw [hitem]
                      exact hb'
                    omega
                | inr b3 =>
                    have hitem : a3.1 = b3.1 := by
                      simpa [f] using congrArg Prod.snd hpair
                    exact congrArg Sum.inr (congrArg Sum.inr (Subtype.ext hitem))
  have hcard :=
    Fintype.card_le_of_injective f hf
  have hD0 : Fintype.card D0 = n - 1 - t.val := by
    dsimp [D0]
    rw [Fintype.card_coe, Fin.card_Ioi]
  have hD1 : Fintype.card D1 = (reverseItem t).val := by
    dsimp [D1]
    rw [Fintype.card_coe, Fin.card_Iio]
  have hD2 : Fintype.card D2 = t.val := by
    dsimp [D2]
    rw [Fintype.card_coe, Fin.card_Iio]
  have hD3 : Fintype.card D3 = n - 1 - (reverseItem t).val := by
    dsimp [D3]
    rw [Fintype.card_coe, Fin.card_Ioi]
  have hDomain_card : Fintype.card Domain = 2 * n - 2 := by
    dsimp [Domain]
    rw [Fintype.card_sum, Fintype.card_sum, Fintype.card_sum,
      hD0, hD1, hD2, hD3]
    simp [reverseItem]
    omega
  have hinactive_card :
      Fintype.card
          {p : UserType 3 × Item n // p ∈ TypePolicy.inactiveTypeItemPairs ρ} =
        TypePolicy.inactiveTypeItemPairsCard ρ := by
    simpa [TypePolicy.inactiveTypeItemPairsCard,
      TypePolicy.inactiveTypeItemPairs] using
      (Fintype.card_coe (TypePolicy.inactiveTypeItemPairs ρ))
  unfold TypePolicy.BasicFeasibleSupportCertificate
  rw [← hinactive_card]
  have hzero_count :
      2 * n - 2 ≤
        Fintype.card
          {p : UserType 3 × Item n // p ∈ TypePolicy.inactiveTypeItemPairs ρ} := by
    simpa [hDomain_card] using hcard
  omega

theorem theorem4Problem11PolicyOptimal_equalizedBasicOptimal_of_closedDual_tight
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ} {t : Item n}
    {ρ : TypePolicy 3 n} {ell : ℝ}
    (hbeta_pos : 0 < beta)
    (hbeta_half : beta < 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hleft : t.val ≤ (reverseItem t).val)
    (hvalue : ell = theorem4Problem11ClosedDualValue beta v t)
    (hopt : Theorem4Problem11PolicyOptimal beta v ρ ell) :
    Theorem4Problem11EqualizedBasicOptimal beta v ρ ell where
  mirror := hopt.1
  item_eq :=
    theorem4Problem11PolicyOptimal_item_eq_of_closedDual_tight
      hbeta_pos hbeta_half hpos hdec hleft hvalue hopt
  optimal := hopt
  basic_feasible :=
    theorem4Problem11PivotSupport_basicFeasibleSupportCertificate
      hopt.1 hleft
      (theorem4Problem11PolicyOptimal_pivotSupport_of_closedDual_tight
        hbeta_pos hbeta_half hpos hdec hleft hvalue hopt)

theorem theorem4Problem11PivotSupport_of_lastActive_noGap_of_sharedBound
    {n : ℕ} [NeZero n] {ρ : TypePolicy 3 n}
    (hmirror : Theorem4MirrorSymmetricPolicy ρ)
    (hx : Theorem4Problem11TypeZeroZeroClosed ρ)
    (hz : Theorem4Problem11ColdStartPositiveClosed ρ)
    (hshared : TypePolicy.SharedItemsBound ρ)
    (hleft :
      (theorem4Problem11LastActiveTypeZero ρ).val ≤
        (reverseItem (theorem4Problem11LastActiveTypeZero ρ)).val) :
    Theorem4Problem11PivotSupport ρ
      (theorem4Problem11LastActiveTypeZero ρ) := by
  classical
  let t : Item n := theorem4Problem11LastActiveTypeZero ρ
  constructor
  · intro j hj
    exact theorem4Problem11_typeZero_zero_after_lastActive ρ hj
  · intro j hjt
    have hxt : ρ 0 t ≠ 0 := by
      dsimp [t]
      exact theorem4Problem11LastActiveTypeZero_active ρ
    have hxj : ρ 0 j ≠ 0 := by
      exact theorem4Problem11_typeZero_active_before_lastActive_of_zeroClosed
        ρ hx (by simpa [t] using hjt)
    have hrev_t_lt_rev_j :
        (reverseItem t).val < (reverseItem j).val :=
      reverseItem_val_lt_of_val_lt hjt
    have ht_lt_rev_j : t.val < (reverseItem j).val :=
      lt_of_le_of_lt (by simpa [t] using hleft) hrev_t_lt_rev_j
    have hj_lt_rev_j : j.val < (reverseItem j).val := by
      exact lt_trans hjt ht_lt_rev_j
    have hj_ne_rev : j ≠ reverseItem j := by
      intro h
      have hval := congrArg Fin.val h
      omega
    have hj_ne_t : j ≠ t := by
      intro h
      subst h
      omega
    have hrevj_ne_t : reverseItem j ≠ t := by
      intro h
      have hval := congrArg Fin.val h
      omega
    have hcontradict_shared (hzj_ne : ρ 2 j ≠ 0) : False := by
      have hzt : ρ 2 t ≠ 0 := hz hjt (by simpa [t] using hleft) hzj_ne
      have hzrevj : ρ 2 (reverseItem j) ≠ 0 := by
        rw [hmirror.2 j]
        exact hzj_ne
      have hyrevj : ρ 1 (reverseItem j) ≠ 0 := by
        rw [hmirror.1 j]
        exact hxj
      have hj_shared : j ∈ TypePolicy.sharedItems ρ :=
        theorem4Problem11_sharedItems_of_active_types ρ
          (by decide : (0 : UserType 3) ≠ 2) hxj hzj_ne
      have hrevj_shared : reverseItem j ∈ TypePolicy.sharedItems ρ :=
        theorem4Problem11_sharedItems_of_active_types ρ
          (by decide : (1 : UserType 3) ≠ 2) hyrevj hzrevj
      have ht_shared : t ∈ TypePolicy.sharedItems ρ :=
        theorem4Problem11_sharedItems_of_active_types ρ
          (by decide : (0 : UserType 3) ≠ 2) hxt hzt
      have hsubset :
          ({j, reverseItem j, t} : Finset (Item n)) ⊆
            TypePolicy.sharedItems ρ := by
        intro u hu
        simp at hu
        rcases hu with rfl | rfl | rfl
        · exact hj_shared
        · exact hrevj_shared
        · exact ht_shared
      have hcard_three :
          ({j, reverseItem j, t} : Finset (Item n)).card = 3 := by
        simp [hj_ne_rev, hj_ne_t, hrevj_ne_t]
      have hthree : 3 ≤ (TypePolicy.sharedItems ρ).card := by
        calc
          3 = ({j, reverseItem j, t} : Finset (Item n)).card :=
            hcard_three.symm
          _ ≤ (TypePolicy.sharedItems ρ).card :=
            Finset.card_le_card hsubset
      have htwo : (TypePolicy.sharedItems ρ).card ≤ 2 := by
        simpa [TypePolicy.SharedItemsBound] using hshared
      omega
    have hzj_zero : ρ 2 j = 0 := by
      by_contra hzj_ne
      exact hcontradict_shared hzj_ne
    constructor
    · exact hzj_zero
    · rw [hmirror.2 j]
      exact hzj_zero

theorem theorem4Problem11PivotSupport_of_equalizedBasicOptimal_noGap
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    {ρ : TypePolicy 3 n} {ell : ℝ}
    (hn : 2 < n)
    (hbeta_pos : 0 < beta)
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (h : Theorem4Problem11EqualizedBasicOptimal beta v ρ ell)
    (hx : Theorem4Problem11TypeZeroZeroClosed ρ)
    (hz : Theorem4Problem11ColdStartPositiveClosed ρ) :
    Theorem4Problem11PivotSupport ρ
      (theorem4Problem11LastActiveTypeZero ρ) := by
  have hshared : TypePolicy.SharedItemsBound ρ :=
    theorem4Problem11_sharedItemsBound_of_equalizedBasicOptimal h
  have hleft :
      (theorem4Problem11LastActiveTypeZero ρ).val ≤
        (reverseItem (theorem4Problem11LastActiveTypeZero ρ)).val := by
    exact theorem4Problem11LastActiveTypeZero_le_reverse_of_equalizedBasicOptimal
      hn hbeta_pos hpos hdec h
  exact theorem4Problem11PivotSupport_of_lastActive_noGap_of_sharedBound
    h.mirror hx hz hshared hleft

theorem theorem4Problem11PivotSupport_of_equalizedBasicOptimal_gapStrictImprovements
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    {ρ : TypePolicy 3 n} {ell : ℝ}
    (hn : 2 < n)
    (hbeta_pos : 0 < beta)
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (h : Theorem4Problem11EqualizedBasicOptimal beta v ρ ell)
    (hxgap : Theorem4Problem11TypeZeroGapStrictImprovement beta v ρ)
    (hzgap : Theorem4Problem11ColdStartGapStrictImprovement beta v ρ) :
    Theorem4Problem11PivotSupport ρ
      (theorem4Problem11LastActiveTypeZero ρ) := by
  have hno : Theorem4Problem11PolicyNoStrictPointwiseImprovement beta v ρ :=
    theorem4Problem11_noStrictPointwiseImprovement_of_equalizedBasicOptimal h
  have hx : Theorem4Problem11TypeZeroZeroClosed ρ :=
    theorem4Problem11_typeZeroZeroClosed_of_gapStrictImprovement hxgap hno
  have hz : Theorem4Problem11ColdStartPositiveClosed ρ :=
    theorem4Problem11_coldStartPositiveClosed_of_gapStrictImprovement hzgap hno
  exact theorem4Problem11PivotSupport_of_equalizedBasicOptimal_noGap
    hn hbeta_pos hpos hdec h hx hz

theorem theorem4Problem11PivotSupport_of_equalizedBasicOptimal
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    {ρ : TypePolicy 3 n} {ell : ℝ}
    (hn : 2 < n)
    (hbeta_pos : 0 < beta)
    (hbeta_half : beta < 1 / 2)
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (h : Theorem4Problem11EqualizedBasicOptimal beta v ρ ell) :
    Theorem4Problem11PivotSupport ρ
      (theorem4Problem11LastActiveTypeZero ρ) := by
  exact theorem4Problem11PivotSupport_of_equalizedBasicOptimal_gapStrictImprovements
    hn hbeta_pos hpos hdec h
    (theorem4Problem11_typeZeroGapStrictImprovement_of_equalizedBasicOptimal
      hn hbeta_pos hbeta_half hpos hdec h)
    (theorem4Problem11_coldStartGapStrictImprovement_of_equalizedBasicOptimal
      hn hbeta_pos hbeta_half hpos hdec h)

theorem theorem4Problem11PivotSupport_typeZero_zero_of_pivot_first
    {n : ℕ} [NeZero n] {ρ : TypePolicy 3 n} {t j : Item n}
    (hpivot : Theorem4Problem11PivotSupport ρ t)
    (ht : t = theorem4FirstItem)
    (hj : j ≠ theorem4FirstItem) :
    ρ 0 j = 0 := by
  have hlt : t.val < j.val := by
    simpa [ht] using theorem4FirstItem_val_lt_of_ne hj
  exact hpivot.1 j hlt

theorem theorem4Problem11PivotSupport_typeZero_reverse_zero_of_lt_pivot
    {n : ℕ} [NeZero n] {ρ : TypePolicy 3 n} {t j : Item n}
    (hpivot : Theorem4Problem11PivotSupport ρ t)
    (hleft : t.val ≤ (reverseItem t).val)
    (hj : j.val < t.val) :
    ρ 0 (reverseItem j) = 0 := by
  have hrev_t_lt_rev_j :
      (reverseItem t).val < (reverseItem j).val :=
    reverseItem_val_lt_of_val_lt hj
  have ht_lt_rev_j : t.val < (reverseItem j).val :=
    lt_of_le_of_lt hleft hrev_t_lt_rev_j
  exact hpivot.1 (reverseItem j) ht_lt_rev_j

theorem theorem4Problem11PivotSupport_typeZero_reverse_zero_of_pivot_lt_left
    {n : ℕ} {ρ : TypePolicy 3 n} {t j : Item n}
    (hpivot : Theorem4Problem11PivotSupport ρ t)
    (hj : t.val < j.val)
    (hjleft : j.val ≤ (reverseItem j).val) :
    ρ 0 (reverseItem j) = 0 := by
  have ht_lt_rev_j : t.val < (reverseItem j).val :=
    lt_of_lt_of_le hj hjleft
  exact hpivot.1 (reverseItem j) ht_lt_rev_j

theorem theorem4Problem11PolicyItemValue_eq_known_of_lt_pivot
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    {ρ : TypePolicy 3 n} {t j : Item n}
    (hpivot : Theorem4Problem11PivotSupport ρ t)
    (hleft : t.val ≤ (reverseItem t).val)
    (hj : j.val < t.val) :
    theorem4Problem11PolicyItemValue beta v ρ j =
      2 * beta * pairShare (1 / 2) v j * (ρ 0 j).toReal := by
  have hz : ρ 2 j = 0 := (hpivot.2 j hj).1
  have hxrev :
      ρ 0 (reverseItem j) = 0 :=
    theorem4Problem11PivotSupport_typeZero_reverse_zero_of_lt_pivot
      hpivot hleft hj
  unfold theorem4Problem11PolicyItemValue theorem4Problem11ItemValue
  simp [hz, hxrev]
  ring

theorem theorem4Problem11PolicyItemValue_eq_cold_of_pivot_lt_left
    {n : ℕ} {beta : ℝ} {v : Item n → ℝ}
    {ρ : TypePolicy 3 n} {t j : Item n}
    (hpivot : Theorem4Problem11PivotSupport ρ t)
    (hj : t.val < j.val)
    (hjleft : j.val ≤ (reverseItem j).val) :
    theorem4Problem11PolicyItemValue beta v ρ j =
      (1 - 2 * beta) * (ρ 2 j).toReal := by
  have hx : ρ 0 j = 0 := hpivot.1 j hj
  have hxrev :
      ρ 0 (reverseItem j) = 0 :=
    theorem4Problem11PivotSupport_typeZero_reverse_zero_of_pivot_lt_left
      hpivot hj hjleft
  unfold theorem4Problem11PolicyItemValue theorem4Problem11ItemValue
  simp [hx, hxrev]

theorem theorem4Problem11PolicyItemValue_eq_cold_of_pivot_lt_and_pivot_lt_reverse
    {n : ℕ} {beta : ℝ} {v : Item n → ℝ}
    {ρ : TypePolicy 3 n} {t j : Item n}
    (hpivot : Theorem4Problem11PivotSupport ρ t)
    (hj : t.val < j.val)
    (hjrev : t.val < (reverseItem j).val) :
    theorem4Problem11PolicyItemValue beta v ρ j =
      (1 - 2 * beta) * (ρ 2 j).toReal := by
  have hx : ρ 0 j = 0 := hpivot.1 j hj
  have hxrev : ρ 0 (reverseItem j) = 0 :=
    hpivot.1 (reverseItem j) hjrev
  unfold theorem4Problem11PolicyItemValue theorem4Problem11ItemValue
  simp [hx, hxrev]

theorem theorem4Problem11PivotSupport_typeZero_toReal_eq_of_lt_pivots
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    {ρ ρ' : TypePolicy 3 n} {t t' j : Item n}
    (hbeta_pos : 0 < beta)
    (hpos : ∀ l : Item n, 0 < v l)
    (hpivot : Theorem4Problem11PivotSupport ρ t)
    (hpivot' : Theorem4Problem11PivotSupport ρ' t')
    (hleft : t.val ≤ (reverseItem t).val)
    (hleft' : t'.val ≤ (reverseItem t').val)
    (hitem :
      theorem4Problem11PolicyItemValue beta v ρ j =
        theorem4Problem11PolicyItemValue beta v ρ' j)
    (hj : j.val < t.val)
    (hj' : j.val < t'.val) :
    (ρ 0 j).toReal = (ρ' 0 j).toReal := by
  have hknown :=
    theorem4Problem11PolicyItemValue_eq_known_of_lt_pivot
      (beta := beta) (v := v) (ρ := ρ) hpivot hleft hj
  have hknown' :=
    theorem4Problem11PolicyItemValue_eq_known_of_lt_pivot
      (beta := beta) (v := v) (ρ := ρ') hpivot' hleft' hj'
  have hcoef_pos :
      0 < 2 * beta * pairShare (1 / 2) v j := by
    have hq_pos : 0 < pairShare (1 / 2) v j :=
      pairShare_pos j (by norm_num) (by norm_num) hpos
    positivity
  have hmul :
      (2 * beta * pairShare (1 / 2) v j) * (ρ 0 j).toReal =
        (2 * beta * pairShare (1 / 2) v j) * (ρ' 0 j).toReal := by
    rw [← hknown, hitem, hknown']
  exact mul_left_cancel₀ (ne_of_gt hcoef_pos) hmul

theorem theorem4Problem11PivotSupport_cold_toReal_eq_of_pivots_lt_left
    {n : ℕ} {beta : ℝ} {v : Item n → ℝ}
    {ρ ρ' : TypePolicy 3 n} {t t' j : Item n}
    (hbeta_half : beta < 1 / 2)
    (hpivot : Theorem4Problem11PivotSupport ρ t)
    (hpivot' : Theorem4Problem11PivotSupport ρ' t')
    (hitem :
      theorem4Problem11PolicyItemValue beta v ρ j =
        theorem4Problem11PolicyItemValue beta v ρ' j)
    (hj : t.val < j.val)
    (hj' : t'.val < j.val)
    (hjleft : j.val ≤ (reverseItem j).val) :
    (ρ 2 j).toReal = (ρ' 2 j).toReal := by
  have hcold :=
    theorem4Problem11PolicyItemValue_eq_cold_of_pivot_lt_left
      (beta := beta) (v := v) (ρ := ρ) hpivot hj hjleft
  have hcold' :=
    theorem4Problem11PolicyItemValue_eq_cold_of_pivot_lt_left
      (beta := beta) (v := v) (ρ := ρ') hpivot' hj' hjleft
  have hcoef_pos : 0 < 1 - 2 * beta := by
    nlinarith
  have hmul :
      (1 - 2 * beta) * (ρ 2 j).toReal =
        (1 - 2 * beta) * (ρ' 2 j).toReal := by
    rw [← hcold, hitem, hcold']
  exact mul_left_cancel₀ (ne_of_gt hcoef_pos) hmul

theorem theorem4Problem11EqualizedBasicOptimal_typeZero_toReal_eq_of_before_both_lastActive
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    {ρ ρ' : TypePolicy 3 n} {ell ell' : ℝ} {j : Item n}
    (hn : 2 < n)
    (hbeta_pos : 0 < beta)
    (hbeta_half : beta < 1 / 2)
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (h : Theorem4Problem11EqualizedBasicOptimal beta v ρ ell)
    (h' : Theorem4Problem11EqualizedBasicOptimal beta v ρ' ell')
    (hj : j.val < (theorem4Problem11LastActiveTypeZero ρ).val)
    (hj' : j.val < (theorem4Problem11LastActiveTypeZero ρ').val) :
    (ρ 0 j).toReal = (ρ' 0 j).toReal := by
  have hpivot :
      Theorem4Problem11PivotSupport ρ
        (theorem4Problem11LastActiveTypeZero ρ) :=
    theorem4Problem11PivotSupport_of_equalizedBasicOptimal
      hn hbeta_pos hbeta_half hpos hdec h
  have hpivot' :
      Theorem4Problem11PivotSupport ρ'
        (theorem4Problem11LastActiveTypeZero ρ') :=
    theorem4Problem11PivotSupport_of_equalizedBasicOptimal
      hn hbeta_pos hbeta_half hpos hdec h'
  have hleft :
      (theorem4Problem11LastActiveTypeZero ρ).val ≤
        (reverseItem (theorem4Problem11LastActiveTypeZero ρ)).val :=
    theorem4Problem11LastActiveTypeZero_le_reverse_of_equalizedBasicOptimal
      hn hbeta_pos hpos hdec h
  have hleft' :
      (theorem4Problem11LastActiveTypeZero ρ').val ≤
        (reverseItem (theorem4Problem11LastActiveTypeZero ρ')).val :=
    theorem4Problem11LastActiveTypeZero_le_reverse_of_equalizedBasicOptimal
      hn hbeta_pos hpos hdec h'
  have hell : ell = ell' :=
    theorem4Problem11EqualizedBasicOptimal_value_unique h h'
  have hitem :
      theorem4Problem11PolicyItemValue beta v ρ j =
        theorem4Problem11PolicyItemValue beta v ρ' j := by
    calc
      theorem4Problem11PolicyItemValue beta v ρ j = ell := h.item_eq j
      _ = ell' := hell
      _ = theorem4Problem11PolicyItemValue beta v ρ' j := (h'.item_eq j).symm
  exact theorem4Problem11PivotSupport_typeZero_toReal_eq_of_lt_pivots
    hbeta_pos hpos hpivot hpivot' hleft hleft' hitem hj hj'

theorem theorem4Problem11EqualizedBasicOptimal_cold_toReal_eq_of_both_lastActive_before_left
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    {ρ ρ' : TypePolicy 3 n} {ell ell' : ℝ} {j : Item n}
    (hn : 2 < n)
    (hbeta_pos : 0 < beta)
    (hbeta_half : beta < 1 / 2)
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (h : Theorem4Problem11EqualizedBasicOptimal beta v ρ ell)
    (h' : Theorem4Problem11EqualizedBasicOptimal beta v ρ' ell')
    (hj : (theorem4Problem11LastActiveTypeZero ρ).val < j.val)
    (hj' : (theorem4Problem11LastActiveTypeZero ρ').val < j.val)
    (hjleft : j.val ≤ (reverseItem j).val) :
    (ρ 2 j).toReal = (ρ' 2 j).toReal := by
  have hpivot :
      Theorem4Problem11PivotSupport ρ
        (theorem4Problem11LastActiveTypeZero ρ) :=
    theorem4Problem11PivotSupport_of_equalizedBasicOptimal
      hn hbeta_pos hbeta_half hpos hdec h
  have hpivot' :
      Theorem4Problem11PivotSupport ρ'
        (theorem4Problem11LastActiveTypeZero ρ') :=
    theorem4Problem11PivotSupport_of_equalizedBasicOptimal
      hn hbeta_pos hbeta_half hpos hdec h'
  have hell : ell = ell' :=
    theorem4Problem11EqualizedBasicOptimal_value_unique h h'
  have hitem :
      theorem4Problem11PolicyItemValue beta v ρ j =
        theorem4Problem11PolicyItemValue beta v ρ' j := by
    calc
      theorem4Problem11PolicyItemValue beta v ρ j = ell := h.item_eq j
      _ = ell' := hell
      _ = theorem4Problem11PolicyItemValue beta v ρ' j := (h'.item_eq j).symm
  exact theorem4Problem11PivotSupport_cold_toReal_eq_of_pivots_lt_left
    hbeta_half hpivot hpivot' hitem hj hj' hjleft

private theorem theorem4_sum_eq_left_part_add_pivot_of_after_zero {n : ℕ}
    (x : Item n → ℝ) (t : Item n)
    (hzero : ∀ {j : Item n}, t.val < j.val → x j = 0) :
    (∑ j : Item n, x j) =
      (∑ j : Item n, if j.val < t.val then x j else 0) + x t := by
  classical
  calc
    (∑ j : Item n, x j)
        = ∑ j : Item n,
            ((if j.val < t.val then x j else 0) +
              (if j = t then x t else 0)) := by
          refine Finset.sum_congr rfl ?_
          intro j _hj
          by_cases hlt : j.val < t.val
          · have hne : j ≠ t := by
              intro h
              subst h
              omega
            simp [hlt, hne]
          · by_cases heq : j = t
            · subst heq
              simp
            · have hgt : t.val < j.val := by
                have hne_val : j.val ≠ t.val := by
                  intro hval
                  exact heq (Fin.ext hval)
                omega
              simp [hlt, heq, hzero hgt]
    _ = (∑ j : Item n, if j.val < t.val then x j else 0) +
          (∑ j : Item n, if j = t then x t else 0) := by
          rw [Finset.sum_add_distrib]
    _ = (∑ j : Item n, if j.val < t.val then x j else 0) + x t := by
          simp

private theorem theorem4_sum_eq_left_part_add_pivot_add_right_part {n : ℕ}
    (x : Item n → ℝ) (t : Item n) :
    (∑ j : Item n, x j) =
      (∑ j : Item n, if j.val < t.val then x j else 0) + x t +
        (∑ j : Item n, if t.val < j.val then x j else 0) := by
  classical
  calc
    (∑ j : Item n, x j)
        = ∑ j : Item n,
            ((if j.val < t.val then x j else 0) +
              (if j = t then x t else 0) +
              (if t.val < j.val then x j else 0)) := by
          refine Finset.sum_congr rfl ?_
          intro j _hj
          by_cases hlt : j.val < t.val
          · have hne : j ≠ t := by
              intro h
              subst h
              omega
            have hnlt : ¬ t.val < j.val := by omega
            simp [hlt, hne, hnlt]
          · by_cases heq : j = t
            · subst heq
              simp
            · have hgt : t.val < j.val := by
                have hne_val : j.val ≠ t.val := by
                  intro hval
                  exact heq (Fin.ext hval)
                omega
              simp [hlt, heq, hgt]
    _ =
        ((∑ j : Item n, if j.val < t.val then x j else 0) +
          (∑ j : Item n, if j = t then x t else 0)) +
          (∑ j : Item n, if t.val < j.val then x j else 0) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ = (∑ j : Item n, if j.val < t.val then x j else 0) + x t +
        (∑ j : Item n, if t.val < j.val then x j else 0) := by
          simp

theorem theorem4Problem11PivotSupport_typeZero_pivot_toReal_eq_one_sub_leftSum
    {n : ℕ} [NeZero n] {ρ : TypePolicy 3 n} {t : Item n}
    (hpivot : Theorem4Problem11PivotSupport ρ t) :
    (ρ 0 t).toReal =
      1 - (∑ j : Item n, if j.val < t.val then (ρ 0 j).toReal else 0) := by
  have hsplit :=
    theorem4_sum_eq_left_part_add_pivot_of_after_zero
      (fun j : Item n => (ρ 0 j).toReal) t
      (fun {j} hj => by simp [hpivot.1 j hj])
  have hsum : (∑ j : Item n, (ρ 0 j).toReal) = 1 :=
    AppliedModelingLib.pmfToRealSum (ρ 0)
  nlinarith

theorem theorem4Problem11PivotSupport_policyItemValue_eq_at_left_pivot
    {n : ℕ} {beta : ℝ} {v : Item n → ℝ}
    {ρ : TypePolicy 3 n} {t : Item n}
    (hpivot : Theorem4Problem11PivotSupport ρ t)
    (ht_left : t.val < (reverseItem t).val) :
    theorem4Problem11PolicyItemValue beta v ρ t =
      2 * beta * pairShare (1 / 2) v t * (ρ 0 t).toReal +
        (1 - 2 * beta) * (ρ 2 t).toReal := by
  have hxrev : ρ 0 (reverseItem t) = 0 :=
    hpivot.1 (reverseItem t) ht_left
  unfold theorem4Problem11PolicyItemValue theorem4Problem11ItemValue
  simp [hxrev]
  ring

/-- Appendix E, Lemma 15's `L_t = ∑_{j<t} 1/q_j`. -/
noncomputable def theorem4Problem11LeftSum {n : ℕ}
    (v : Item n → ℝ) (t : Item n) : ℝ :=
  ∑ j : Item n,
    if j.val < t.val then (pairShare (1 / 2) v j)⁻¹ else 0

theorem theorem4Problem11LeftSum_nonneg {n : ℕ}
    {v : Item n → ℝ}
    (hpos : ∀ j : Item n, 0 < v j) (t : Item n) :
    0 ≤ theorem4Problem11LeftSum v t := by
  unfold theorem4Problem11LeftSum
  refine Finset.sum_nonneg ?_
  intro j _hj
  by_cases hjt : j.val < t.val
  · have hq_nonneg : 0 ≤ pairShare (1 / 2) v j :=
      (pairShare_pos j
        (by norm_num : (0 : ℝ) < 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1) hpos).le
    simpa [hjt] using hq_nonneg
  · simp [hjt]

theorem theorem4Problem11LeftSum_next_eq {n : ℕ}
    {v : Item n → ℝ} {t u : Item n}
    (hnext : u.val = t.val + 1) :
    theorem4Problem11LeftSum v u =
      theorem4Problem11LeftSum v t +
        (pairShare (1 / 2) v t)⁻¹ := by
  simpa [theorem4Problem11LeftSum, problem6LeftSum] using
    (problem6LeftSum_next_eq
      (alpha := (1 / 2 : ℝ)) (v := v) (t := t) (u := u) hnext)

private theorem theorem4Problem11ClosedDualRawWeight_left_part_sum_eq
    {n : ℕ} {v : Item n → ℝ} {t : Item n} :
    (∑ j : Item n, if j.val < t.val then
        theorem4Problem11ClosedDualRawWeight v t j else 0) =
      pairShare (1 / 2) v t * theorem4Problem11LeftSum v t := by
  unfold theorem4Problem11LeftSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro j _hj
  by_cases hjt : j.val < t.val
  · rw [if_pos hjt, if_pos hjt,
      theorem4Problem11ClosedDualRawWeight_before hjt]
    ring
  · simp [hjt]

private theorem theorem4Problem11ClosedDualRawWeight_right_part_sum_eq
    {n : ℕ} {v : Item n → ℝ} {t : Item n}
    (hleft : t.val ≤ (reverseItem t).val) :
    (∑ j : Item n, if (reverseItem t).val < j.val then
        theorem4Problem11ClosedDualRawWeight v t j else 0) =
      pairShare (1 / 2) v t * theorem4Problem11LeftSum v t := by
  have hleft_sum :
      (∑ j : Item n, if j.val < t.val then
          theorem4Problem11ClosedDualRawWeight v t j else 0) =
        pairShare (1 / 2) v t * theorem4Problem11LeftSum v t :=
    theorem4Problem11ClosedDualRawWeight_left_part_sum_eq
  have hrev :=
    (sum_reverseItem
      (fun j : Item n =>
        if j.val < t.val then
          theorem4Problem11ClosedDualRawWeight v t j else 0)).symm
  have hright_eq_left :
      (∑ j : Item n, if (reverseItem t).val < j.val then
          theorem4Problem11ClosedDualRawWeight v t j else 0) =
        (∑ j : Item n, if (reverseItem j).val < t.val then
          theorem4Problem11ClosedDualRawWeight v t (reverseItem j) else 0) := by
    refine Finset.sum_congr rfl ?_
    intro j _hj
    have hiff :
        (reverseItem j).val < t.val ↔ (reverseItem t).val < j.val := by
      constructor
      · intro h
        simpa [reverseItem_reverseItem] using
          (reverseItem_val_lt_of_val_lt h)
      · intro h
        simpa [reverseItem_reverseItem] using
          (reverseItem_val_lt_of_val_lt h)
    by_cases hafter : (reverseItem t).val < j.val
    · have hbefore : (reverseItem j).val < t.val := hiff.mpr hafter
      simp [hafter, hbefore,
        theorem4Problem11ClosedDualRawWeight_mirror hleft j]
    · have hbefore : ¬ (reverseItem j).val < t.val := by
        intro h
        exact hafter (hiff.mp h)
      simp [hafter, hbefore]
  calc
    (∑ j : Item n, if (reverseItem t).val < j.val then
        theorem4Problem11ClosedDualRawWeight v t j else 0)
        =
      (∑ j : Item n, if (reverseItem j).val < t.val then
          theorem4Problem11ClosedDualRawWeight v t (reverseItem j) else 0) :=
      hright_eq_left
    _ =
      (∑ j : Item n, if j.val < t.val then
          theorem4Problem11ClosedDualRawWeight v t j else 0) := hrev.symm
    _ = pairShare (1 / 2) v t * theorem4Problem11LeftSum v t := hleft_sum

private theorem theorem4Problem11_middle_const_sum_eq {n : ℕ}
    {t : Item n}
    (hleft : t.val ≤ (reverseItem t).val) :
    (∑ j : Item n,
        if j.val < t.val then (0 : ℝ)
        else if (reverseItem t).val < j.val then 0 else 1) =
      (n : ℝ) - 2 * (t.val : ℝ) := by
  let left : ℝ :=
    ∑ j : Item n, if j.val < t.val then (1 : ℝ) else 0
  let middle : ℝ :=
    ∑ j : Item n,
      if j.val < t.val then (0 : ℝ)
      else if (reverseItem t).val < j.val then 0 else 1
  let right : ℝ :=
    ∑ j : Item n, if (reverseItem t).val < j.val then (1 : ℝ) else 0
  have hpoint :
      ∀ j : Item n,
        (1 : ℝ) =
          (if j.val < t.val then (1 : ℝ) else 0) +
          (if j.val < t.val then (0 : ℝ)
           else if (reverseItem t).val < j.val then 0 else 1) +
          (if (reverseItem t).val < j.val then (1 : ℝ) else 0) := by
    intro j
    by_cases hj_left : j.val < t.val
    · have hnot_after : ¬ (reverseItem t).val < j.val := by omega
      simp [hj_left, hnot_after]
    · by_cases hj_after : (reverseItem t).val < j.val
      · simp [hj_left, hj_after]
      · simp [hj_left, hj_after]
  have hpartition :
      (n : ℝ) = left + middle + right := by
    have htotal : (∑ _j : Item n, (1 : ℝ)) = (n : ℝ) := by
      simp [Item]
    calc
      (n : ℝ) = ∑ _j : Item n, (1 : ℝ) := htotal.symm
      _ =
        ∑ j : Item n,
          ((if j.val < t.val then (1 : ℝ) else 0) +
          (if j.val < t.val then (0 : ℝ)
           else if (reverseItem t).val < j.val then 0 else 1) +
          (if (reverseItem t).val < j.val then (1 : ℝ) else 0)) := by
          refine Finset.sum_congr rfl ?_
          intro j _hj
          exact hpoint j
      _ = left + middle + right := by
          dsimp [left, middle, right]
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hleft_sum : left = (t.val : ℝ) := by
    dsimp [left]
    simpa using problem6_sum_left_const_eq t (1 : ℝ)
  have hright_sum : right = (t.val : ℝ) := by
    dsimp [right]
    have hright :=
      problem6_sum_right_const_eq (reverseItem t) (1 : ℝ)
    have hrev_add : (reverseItem t).val + t.val + 1 = n := by
      simp [reverseItem]
      omega
    have hright_count :
        (n : ℝ) - ((reverseItem t).val : ℝ) - 1 =
          (t.val : ℝ) := by
      have hcast :
          ((reverseItem t).val : ℝ) + (t.val : ℝ) + 1 = (n : ℝ) := by
        exact_mod_cast hrev_add
      nlinarith
    rw [hright]
    nlinarith
  change middle = (n : ℝ) - 2 * (t.val : ℝ)
  nlinarith

private theorem theorem4Problem11ClosedDualRawWeight_middle_part_sum_eq
    {n : ℕ} {v : Item n → ℝ} {t : Item n}
    (hleft : t.val ≤ (reverseItem t).val) :
    (∑ j : Item n,
        if j.val < t.val then (0 : ℝ)
        else if (reverseItem t).val < j.val then 0
        else theorem4Problem11ClosedDualRawWeight v t j) =
      (n : ℝ) - 2 * (t.val : ℝ) := by
  calc
    (∑ j : Item n,
        if j.val < t.val then (0 : ℝ)
        else if (reverseItem t).val < j.val then 0
        else theorem4Problem11ClosedDualRawWeight v t j)
        =
      ∑ j : Item n,
        if j.val < t.val then (0 : ℝ)
        else if (reverseItem t).val < j.val then 0 else 1 := by
        refine Finset.sum_congr rfl ?_
        intro j _hj
        by_cases hj_left : j.val < t.val
        · simp [hj_left]
        · by_cases hj_after : (reverseItem t).val < j.val
          · simp [hj_left, hj_after]
          · simp [hj_left, hj_after,
              theorem4Problem11ClosedDualRawWeight_middle hj_left hj_after]
    _ = (n : ℝ) - 2 * (t.val : ℝ) :=
      theorem4Problem11_middle_const_sum_eq hleft

/--
The raw closed-dual denominator equals the paper's full mirrored-policy
denominator `2 q_t L_t + n - 2(t-1)` in zero-based notation.
-/
theorem theorem4Problem11ClosedDualDenominator_eq
    {n : ℕ} {v : Item n → ℝ} {t : Item n}
    (hleft : t.val ≤ (reverseItem t).val) :
    theorem4Problem11ClosedDualDenominator v t =
      2 * pairShare (1 / 2) v t * theorem4Problem11LeftSum v t +
        ((n : ℝ) - 2 * (t.val : ℝ)) := by
  let leftPart : ℝ :=
    ∑ j : Item n, if j.val < t.val then
      theorem4Problem11ClosedDualRawWeight v t j else 0
  let middlePart : ℝ :=
    ∑ j : Item n,
      if j.val < t.val then (0 : ℝ)
      else if (reverseItem t).val < j.val then 0
      else theorem4Problem11ClosedDualRawWeight v t j
  let rightPart : ℝ :=
    ∑ j : Item n, if (reverseItem t).val < j.val then
      theorem4Problem11ClosedDualRawWeight v t j else 0
  have hsplit :
      theorem4Problem11ClosedDualDenominator v t =
        leftPart + middlePart + rightPart := by
    unfold theorem4Problem11ClosedDualDenominator
    calc
      (∑ j : Item n, theorem4Problem11ClosedDualRawWeight v t j)
          =
        ∑ j : Item n,
          ((if j.val < t.val then
              theorem4Problem11ClosedDualRawWeight v t j else 0) +
           (if j.val < t.val then (0 : ℝ)
            else if (reverseItem t).val < j.val then 0
            else theorem4Problem11ClosedDualRawWeight v t j) +
           (if (reverseItem t).val < j.val then
              theorem4Problem11ClosedDualRawWeight v t j else 0)) := by
          refine Finset.sum_congr rfl ?_
          intro j _hj
          by_cases hj_left : j.val < t.val
          · have hnot_after : ¬ (reverseItem t).val < j.val := by omega
            simp [hj_left, hnot_after]
          · by_cases hj_after : (reverseItem t).val < j.val
            · simp [hj_left, hj_after]
            · simp [hj_left, hj_after]
      _ = leftPart + middlePart + rightPart := by
          dsimp [leftPart, middlePart, rightPart]
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hleft_sum :
      leftPart =
        pairShare (1 / 2) v t * theorem4Problem11LeftSum v t := by
    dsimp [leftPart]
    exact theorem4Problem11ClosedDualRawWeight_left_part_sum_eq
  have hmiddle_sum :
      middlePart = (n : ℝ) - 2 * (t.val : ℝ) := by
    dsimp [middlePart]
    exact theorem4Problem11ClosedDualRawWeight_middle_part_sum_eq hleft
  have hright_sum :
      rightPart =
        pairShare (1 / 2) v t * theorem4Problem11LeftSum v t := by
    dsimp [rightPart]
    exact theorem4Problem11ClosedDualRawWeight_right_part_sum_eq hleft
  rw [hsplit, hleft_sum, hmiddle_sum, hright_sum]
  ring

/-- Closed Problem 11 dual value in the same full-policy denominator form as Lemma 15. -/
theorem theorem4Problem11ClosedDualValue_eq_fullPolicy_formula
    {n : ℕ} {beta : ℝ} {v : Item n → ℝ} {t : Item n}
    (hleft : t.val ≤ (reverseItem t).val) :
    theorem4Problem11ClosedDualValue beta v t =
      (4 * beta * pairShare (1 / 2) v t + (1 - 2 * beta)) /
        (2 * pairShare (1 / 2) v t * theorem4Problem11LeftSum v t +
          ((n : ℝ) - 2 * (t.val : ℝ))) := by
  unfold theorem4Problem11ClosedDualValue
    theorem4Problem11ClosedKnownBudget
    theorem4Problem11ClosedColdBudget
  rw [theorem4Problem11ClosedDualDenominator_eq hleft]
  ring

theorem theorem4Problem11ClosedDualValue_pos {n : ℕ}
    {beta : ℝ} {v : Item n → ℝ} {t : Item n}
    (hbeta_pos : 0 < beta) (hbeta_half : beta < 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hleft : t.val ≤ (reverseItem t).val) :
    0 < theorem4Problem11ClosedDualValue beta v t := by
  have hDpos :
      0 < theorem4Problem11ClosedDualDenominator v t :=
    theorem4Problem11ClosedDualDenominator_pos
      (v := v) (t := t) hpos hleft
  have hknown_nonneg :
      0 ≤ theorem4Problem11ClosedKnownBudget beta v t := by
    unfold theorem4Problem11ClosedKnownBudget
    exact div_nonneg
      (mul_nonneg
        (mul_nonneg (by positivity) hbeta_pos.le)
        (pairShare_pos t (by norm_num) (by norm_num) hpos).le)
      hDpos.le
  have hcold_pos :
      0 < theorem4Problem11ClosedColdBudget beta v t := by
    unfold theorem4Problem11ClosedColdBudget
    exact div_pos (by nlinarith) hDpos
  unfold theorem4Problem11ClosedDualValue
  positivity

/-- Closed-form Problem 11 known-type row for a fixed pivot. -/
noncomputable def theorem4Problem11ClosedX {n : ℕ}
    (beta : ℝ) (v : Item n → ℝ) (t j : Item n) : ℝ :=
  if j.val < t.val then
    theorem4Problem11ClosedDualValue beta v t /
      (2 * beta * pairShare (1 / 2) v j)
  else if j = t then
    1 -
      (∑ l : Item n,
        if l.val < t.val then
          theorem4Problem11ClosedDualValue beta v t /
            (2 * beta * pairShare (1 / 2) v l)
        else 0)
  else
    0

theorem theorem4Problem11ClosedX_before {n : ℕ}
    {beta : ℝ} {v : Item n → ℝ} {t j : Item n}
    (hj : j.val < t.val) :
    theorem4Problem11ClosedX beta v t j =
      theorem4Problem11ClosedDualValue beta v t /
        (2 * beta * pairShare (1 / 2) v j) := by
  simp [theorem4Problem11ClosedX, hj]

theorem theorem4Problem11ClosedX_at {n : ℕ}
    {beta : ℝ} {v : Item n → ℝ} {t : Item n} :
    theorem4Problem11ClosedX beta v t t =
      1 -
        (∑ l : Item n,
          if l.val < t.val then
          theorem4Problem11ClosedDualValue beta v t /
            (2 * beta * pairShare (1 / 2) v l)
        else 0) := by
  simp [theorem4Problem11ClosedX]

theorem theorem4Problem11ClosedX_at_eq_one_sub_leftSum {n : ℕ}
    {beta : ℝ} {v : Item n → ℝ} {t : Item n}
    (hbeta_pos : 0 < beta)
    (hpos : ∀ j : Item n, 0 < v j) :
    theorem4Problem11ClosedX beta v t t =
      1 -
        (theorem4Problem11ClosedDualValue beta v t / (2 * beta)) *
          theorem4Problem11LeftSum v t := by
  rw [theorem4Problem11ClosedX_at]
  congr 1
  unfold theorem4Problem11LeftSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro j _hj
  by_cases hj : j.val < t.val
  · have hbeta_ne : beta ≠ 0 := ne_of_gt hbeta_pos
    have hq_ne : pairShare (1 / 2) v j ≠ 0 :=
      ne_of_gt (pairShare_pos j (by norm_num) (by norm_num) hpos)
    rw [if_pos hj, if_pos hj]
    field_simp [hbeta_ne, hq_ne]
  · simp [hj]

theorem theorem4Problem11ClosedX_after {n : ℕ}
    {beta : ℝ} {v : Item n → ℝ} {t j : Item n}
    (hj : t.val < j.val) :
    theorem4Problem11ClosedX beta v t j = 0 := by
  have hnleft : ¬ j.val < t.val := by omega
  have hne : j ≠ t := by
    intro h
    subst h
    omega
  simp [theorem4Problem11ClosedX, hnleft, hne]

/-- The closed-form Problem 11 known-type row has total mass one by construction. -/
theorem theorem4Problem11ClosedX_sum_eq_one {n : ℕ}
    (beta : ℝ) (v : Item n → ℝ) (t : Item n) :
    (∑ j : Item n, theorem4Problem11ClosedX beta v t j) = 1 := by
  have hsplit :=
    theorem4_sum_eq_left_part_add_pivot_of_after_zero
      (theorem4Problem11ClosedX beta v t) t
      (fun {j} hj => theorem4Problem11ClosedX_after hj)
  have hleft :
      (∑ j : Item n,
        if j.val < t.val then theorem4Problem11ClosedX beta v t j else 0) =
      (∑ j : Item n,
        if j.val < t.val then
          theorem4Problem11ClosedDualValue beta v t /
            (2 * beta * pairShare (1 / 2) v j)
        else 0) := by
    refine Finset.sum_congr rfl ?_
    intro j _hj
    by_cases hjt : j.val < t.val
    · rw [if_pos hjt, if_pos hjt,
        theorem4Problem11ClosedX_before hjt]
    · simp [hjt]
  rw [hsplit, hleft, theorem4Problem11ClosedX_at]
  ring

theorem theorem4Problem11ClosedX_nonneg {n : ℕ}
    {beta : ℝ} {v : Item n → ℝ} {t : Item n}
    (hbeta_pos : 0 < beta) (hbeta_half : beta < 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hleft : t.val ≤ (reverseItem t).val)
    (hpivot : 0 ≤ theorem4Problem11ClosedX beta v t t) :
    ∀ j : Item n, 0 ≤ theorem4Problem11ClosedX beta v t j := by
  intro j
  by_cases hj_left : j.val < t.val
  · rw [theorem4Problem11ClosedX_before hj_left]
    exact div_nonneg
      (theorem4Problem11ClosedDualValue_pos
        hbeta_pos hbeta_half hpos hleft).le
      (mul_nonneg
        (mul_nonneg (by positivity) hbeta_pos.le)
        (pairShare_pos j (by norm_num) (by norm_num) hpos).le)
  · by_cases hj_eq : j = t
    · subst j
      exact hpivot
    · have htj : t.val < j.val := by
        have hne_val : j.val ≠ t.val := by
          intro hval
          exact hj_eq (Fin.ext hval)
        omega
      rw [theorem4Problem11ClosedX_after htj]

/-- The total interior cold-start mass in the closed Problem 11 solution. -/
noncomputable def theorem4Problem11ClosedZInteriorMass {n : ℕ}
    (beta : ℝ) (v : Item n → ℝ) (t : Item n) : ℝ :=
  ∑ l : Item n,
    if t.val < l.val ∧ l.val < (reverseItem t).val then
      theorem4Problem11ClosedDualValue beta v t / (1 - 2 * beta)
    else 0

/-- Endpoint cold-start mass at the pivot and mirror pivot. -/
noncomputable def theorem4Problem11ClosedZEndpointMass {n : ℕ}
    (beta : ℝ) (v : Item n → ℝ) (t : Item n) : ℝ :=
  if t = reverseItem t then
    1
  else
    (1 - theorem4Problem11ClosedZInteriorMass beta v t) / 2

/-- Closed-form Problem 11 cold-start row for a fixed left-half pivot. -/
noncomputable def theorem4Problem11ClosedZ {n : ℕ}
    (beta : ℝ) (v : Item n → ℝ) (t j : Item n) : ℝ :=
  if j.val < t.val then
    0
  else if (reverseItem t).val < j.val then
    0
  else if j = t ∨ j = reverseItem t then
    theorem4Problem11ClosedZEndpointMass beta v t
  else
    theorem4Problem11ClosedDualValue beta v t / (1 - 2 * beta)

theorem theorem4Problem11ClosedZ_before {n : ℕ}
    {beta : ℝ} {v : Item n → ℝ} {t j : Item n}
    (hj : j.val < t.val) :
    theorem4Problem11ClosedZ beta v t j = 0 := by
  simp [theorem4Problem11ClosedZ, hj]

theorem theorem4Problem11ClosedZ_after {n : ℕ}
    {beta : ℝ} {v : Item n → ℝ} {t j : Item n}
    (hleft : t.val ≤ (reverseItem t).val)
    (hj : (reverseItem t).val < j.val) :
    theorem4Problem11ClosedZ beta v t j = 0 := by
  have hnleft : ¬ j.val < t.val := by omega
  simp [theorem4Problem11ClosedZ, hnleft, hj]

theorem theorem4Problem11ClosedZ_endpoint {n : ℕ}
    {beta : ℝ} {v : Item n → ℝ} {t j : Item n}
    (hnleft : ¬ j.val < t.val)
    (hnafter : ¬ (reverseItem t).val < j.val)
    (hj : j = t ∨ j = reverseItem t) :
    theorem4Problem11ClosedZ beta v t j =
      theorem4Problem11ClosedZEndpointMass beta v t := by
  simp [theorem4Problem11ClosedZ, hnleft, hnafter, hj]

theorem theorem4Problem11ClosedZ_interior {n : ℕ}
    {beta : ℝ} {v : Item n → ℝ} {t j : Item n}
    (hj_left : t.val < j.val)
    (hj_right : j.val < (reverseItem t).val) :
    theorem4Problem11ClosedZ beta v t j =
      theorem4Problem11ClosedDualValue beta v t / (1 - 2 * beta) := by
  have hnleft : ¬ j.val < t.val := by omega
  have hnafter : ¬ (reverseItem t).val < j.val := by omega
  have hne_left : j ≠ t := by
    intro h
    subst h
    omega
  have hne_right : j ≠ reverseItem t := by
    intro h
    subst h
    omega
  have hnot_endpoint : ¬ (j = t ∨ j = reverseItem t) := by
    intro h
    exact h.elim hne_left hne_right
  simp [theorem4Problem11ClosedZ, hnleft, hnafter, hnot_endpoint]

theorem theorem4Problem11ClosedZ_mirror {n : ℕ}
    {beta : ℝ} {v : Item n → ℝ} {t j : Item n}
    (hleft : t.val ≤ (reverseItem t).val) :
    theorem4Problem11ClosedZ beta v t (reverseItem j) =
      theorem4Problem11ClosedZ beta v t j := by
  by_cases hj_before : j.val < t.val
  · have hrev_after :
        (reverseItem t).val < (reverseItem j).val :=
      reverseItem_val_lt_of_val_lt hj_before
    rw [theorem4Problem11ClosedZ_after hleft hrev_after,
      theorem4Problem11ClosedZ_before hj_before]
  · by_cases hj_after : (reverseItem t).val < j.val
    · have hrev_before :
          (reverseItem j).val < t.val := by
        simpa [reverseItem_reverseItem] using
          reverseItem_val_lt_of_val_lt hj_after
      rw [theorem4Problem11ClosedZ_before hrev_before,
        theorem4Problem11ClosedZ_after hleft hj_after]
    · have hrev_not_before : ¬ (reverseItem j).val < t.val := by
        simp [reverseItem] at hj_before hj_after hleft ⊢
        omega
      have hrev_not_after :
          ¬ (reverseItem t).val < (reverseItem j).val := by
        simp [reverseItem] at hj_before hj_after hleft ⊢
        omega
      by_cases hj_endpoint : j = t ∨ j = reverseItem t
      · have hrev_endpoint :
            reverseItem j = t ∨ reverseItem j = reverseItem t := by
          rcases hj_endpoint with rfl | rfl
          · exact Or.inr rfl
          · exact Or.inl (reverseItem_reverseItem _)
        rw [theorem4Problem11ClosedZ_endpoint
            hrev_not_before hrev_not_after hrev_endpoint,
          theorem4Problem11ClosedZ_endpoint
            hj_before hj_after hj_endpoint]
      · have hj_left_strict : t.val < j.val := by
          have hne : j ≠ t := by
            intro h
            exact hj_endpoint (Or.inl h)
          have hne_val : j.val ≠ t.val := by
            intro hval
            exact hne (Fin.ext hval)
          omega
        have hj_right_strict : j.val < (reverseItem t).val := by
          have hne : j ≠ reverseItem t := by
            intro h
            exact hj_endpoint (Or.inr h)
          have hne_val : j.val ≠ (reverseItem t).val := by
            intro hval
            exact hne (Fin.ext hval)
          omega
        have hrev_left_strict :
            t.val < (reverseItem j).val := by
          simpa [reverseItem_reverseItem] using
            reverseItem_val_lt_of_val_lt hj_right_strict
        have hrev_right_strict :
            (reverseItem j).val < (reverseItem t).val :=
          reverseItem_val_lt_of_val_lt hj_left_strict
        rw [theorem4Problem11ClosedZ_interior
            hrev_left_strict hrev_right_strict,
          theorem4Problem11ClosedZ_interior
            hj_left_strict hj_right_strict]

private theorem theorem4Problem11_strict_middle_const_sum_eq {n : ℕ}
    {t : Item n}
    (hstrict : t.val < (reverseItem t).val) :
    (∑ j : Item n,
        if t.val < j.val ∧ j.val < (reverseItem t).val
        then (1 : ℝ) else 0) =
      (n : ℝ) - 2 * (t.val : ℝ) - 2 := by
  let strictMiddle : ℝ :=
    ∑ j : Item n,
      if t.val < j.val ∧ j.val < (reverseItem t).val
      then (1 : ℝ) else 0
  have hne : t ≠ reverseItem t := by
    intro h
    have hval := congrArg Fin.val h
    omega
  have hpoint :
      ∀ j : Item n,
        (if j.val < t.val then (0 : ℝ)
         else if (reverseItem t).val < j.val then 0 else 1) =
          (if j = t then (1 : ℝ) else 0) +
          (if j = reverseItem t then (1 : ℝ) else 0) +
          (if t.val < j.val ∧ j.val < (reverseItem t).val
           then (1 : ℝ) else 0) := by
    intro j
    by_cases hjt : j = t
    · subst j
      have hnleft : ¬ t.val < t.val := by omega
      have hnafter : ¬ (reverseItem t).val < t.val := by omega
      have hnot_int :
          ¬ (t.val < t.val ∧ t.val < (reverseItem t).val) := by
        omega
      rw [if_neg hnleft, if_neg hnafter, if_pos rfl,
        if_neg hne, if_neg hnot_int]
      ring
    · by_cases hjrev : j = reverseItem t
      · subst j
        have hnleft : ¬ (reverseItem t).val < t.val := by omega
        have hnafter :
            ¬ (reverseItem t).val < (reverseItem t).val := by omega
        have hnot_int :
            ¬ (t.val < (reverseItem t).val ∧
              (reverseItem t).val < (reverseItem t).val) := by
          omega
        rw [if_neg hnleft, if_neg hnafter, if_neg hne.symm,
          if_pos rfl, if_neg hnot_int]
        ring
      · by_cases hj_left : j.val < t.val
        · have hnot_after : ¬ (reverseItem t).val < j.val := by omega
          have hnot_int :
              ¬ (t.val < j.val ∧ j.val < (reverseItem t).val) := by
            omega
          rw [if_pos hj_left, if_neg hjt, if_neg hjrev,
            if_neg hnot_int]
          ring
        · by_cases hj_after : (reverseItem t).val < j.val
          · have hnot_int :
                ¬ (t.val < j.val ∧ j.val < (reverseItem t).val) := by
              omega
            rw [if_neg hj_left, if_pos hj_after, if_neg hjt,
              if_neg hjrev, if_neg hnot_int]
            ring
          · have hj_left_strict : t.val < j.val := by
              have hne_val : j.val ≠ t.val := by
                intro hval
                exact hjt (Fin.ext hval)
              omega
            have hj_right_strict : j.val < (reverseItem t).val := by
              have hne_val : j.val ≠ (reverseItem t).val := by
                intro hval
                exact hjrev (Fin.ext hval)
              omega
            simp [hj_left, hj_after, hjt, hjrev,
              hj_left_strict, hj_right_strict]
  have hsplit :
      (∑ j : Item n,
          if j.val < t.val then (0 : ℝ)
          else if (reverseItem t).val < j.val then 0 else 1) =
        1 + 1 + strictMiddle := by
    calc
      (∑ j : Item n,
          if j.val < t.val then (0 : ℝ)
          else if (reverseItem t).val < j.val then 0 else 1)
          =
        ∑ j : Item n,
          ((if j = t then (1 : ℝ) else 0) +
          (if j = reverseItem t then (1 : ℝ) else 0) +
          (if t.val < j.val ∧ j.val < (reverseItem t).val
           then (1 : ℝ) else 0)) := by
          refine Finset.sum_congr rfl ?_
          intro j _hj
          exact hpoint j
      _ =
        (∑ j : Item n, if j = t then (1 : ℝ) else 0) +
          (∑ j : Item n, if j = reverseItem t then (1 : ℝ) else 0) +
          (∑ j : Item n,
            if t.val < j.val ∧ j.val < (reverseItem t).val
            then (1 : ℝ) else 0) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      _ = 1 + 1 + strictMiddle := by
          simp [strictMiddle]
  have hinclusive :=
    theorem4Problem11_middle_const_sum_eq (le_of_lt hstrict)
  dsimp [strictMiddle] at hsplit
  nlinarith

theorem theorem4Problem11ClosedZInteriorMass_eq {n : ℕ}
    {beta : ℝ} {v : Item n → ℝ} {t : Item n}
    (hstrict : t.val < (reverseItem t).val) :
    theorem4Problem11ClosedZInteriorMass beta v t =
      ((n : ℝ) - 2 * (t.val : ℝ) - 2) *
        (theorem4Problem11ClosedDualValue beta v t / (1 - 2 * beta)) := by
  unfold theorem4Problem11ClosedZInteriorMass
  calc
    (∑ l : Item n,
        if t.val < l.val ∧ l.val < (reverseItem t).val then
          theorem4Problem11ClosedDualValue beta v t / (1 - 2 * beta)
        else 0)
        =
      (∑ l : Item n,
        if t.val < l.val ∧ l.val < (reverseItem t).val
        then (1 : ℝ) else 0) *
        (theorem4Problem11ClosedDualValue beta v t / (1 - 2 * beta)) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl ?_
        intro l _hl
        by_cases hlt :
            t.val < l.val ∧ l.val < (reverseItem t).val
        · simp [hlt]
        · simp
    _ =
      ((n : ℝ) - 2 * (t.val : ℝ) - 2) *
        (theorem4Problem11ClosedDualValue beta v t / (1 - 2 * beta)) := by
        rw [theorem4Problem11_strict_middle_const_sum_eq hstrict]

/-- The closed-form Problem 11 cold-start row has total mass one. -/
theorem theorem4Problem11ClosedZ_sum_eq_one {n : ℕ}
    {beta : ℝ} {v : Item n → ℝ} {t : Item n}
    (hleft : t.val ≤ (reverseItem t).val) :
    (∑ j : Item n, theorem4Problem11ClosedZ beta v t j) = 1 := by
  by_cases hcenter : t = reverseItem t
  · have hzero : ∀ j : Item n, j ≠ t →
        theorem4Problem11ClosedZ beta v t j = 0 := by
      intro j hj_ne
      have hval_ne : j.val ≠ t.val := by
        intro hval
        exact hj_ne (Fin.ext hval)
      rcases lt_or_gt_of_ne hval_ne with hjt | htj
      · exact theorem4Problem11ClosedZ_before hjt
      · have hafter : (reverseItem t).val < j.val := by
          simpa [← hcenter] using htj
        exact theorem4Problem11ClosedZ_after hleft hafter
    have hsingle :
        (∑ j : Item n, theorem4Problem11ClosedZ beta v t j) =
          theorem4Problem11ClosedZ beta v t t := by
      apply Finset.sum_eq_single t
      · intro j _hj hj_ne
        exact hzero j hj_ne
      · intro hnot
        simp at hnot
    have ht :
        theorem4Problem11ClosedZ beta v t t = 1 := by
      have hnleft : ¬ t.val < t.val := by omega
      have hnafter : ¬ (reverseItem t).val < t.val := by
        rw [← hcenter]
        omega
      rw [theorem4Problem11ClosedZ_endpoint
        hnleft hnafter (Or.inl rfl)]
      unfold theorem4Problem11ClosedZEndpointMass
      rw [if_pos hcenter]
    rw [hsingle, ht]
  · have ht_lt_rev : t.val < (reverseItem t).val := by
      have hne_val : t.val ≠ (reverseItem t).val := by
        intro hval
        exact hcenter (Fin.ext hval)
      omega
    let E : ℝ := theorem4Problem11ClosedZEndpointMass beta v t
    let I : ℝ := theorem4Problem11ClosedDualValue beta v t / (1 - 2 * beta)
    have hpoint :
        ∀ j : Item n,
          theorem4Problem11ClosedZ beta v t j =
            (if j = t then E else 0) +
            (if j = reverseItem t then E else 0) +
            (if t.val < j.val ∧ j.val < (reverseItem t).val then I else 0) := by
      intro j
      by_cases hj_t : j = t
      · subst j
        have hnleft : ¬ t.val < t.val := by omega
        have hnafter : ¬ (reverseItem t).val < t.val := by omega
        have hnot_int :
            ¬ (t.val < t.val ∧ t.val < (reverseItem t).val) := by omega
        rw [theorem4Problem11ClosedZ_endpoint
          hnleft hnafter (Or.inl rfl)]
        rw [if_pos rfl, if_neg hcenter, if_neg hnot_int]
        ring
      · by_cases hj_rev : j = reverseItem t
        · subst j
          have hnleft : ¬ (reverseItem t).val < t.val := by omega
          have hnafter : ¬ (reverseItem t).val < (reverseItem t).val := by omega
          have hnot_int :
              ¬ (t.val < (reverseItem t).val ∧
                (reverseItem t).val < (reverseItem t).val) := by omega
          have hrev_ne_t : reverseItem t ≠ t := by
            intro h
            exact hcenter h.symm
          rw [theorem4Problem11ClosedZ_endpoint
              hnleft hnafter (Or.inr rfl)]
          rw [if_neg hrev_ne_t, if_pos rfl, if_neg hnot_int]
          ring
        · by_cases hj_before : j.val < t.val
          · have hnot_int :
                ¬ (t.val < j.val ∧ j.val < (reverseItem t).val) := by
              omega
            rw [theorem4Problem11ClosedZ_before hj_before]
            rw [if_neg hj_t, if_neg hj_rev, if_neg hnot_int]
            ring
          · by_cases hj_after : (reverseItem t).val < j.val
            · have hnot_int :
                  ¬ (t.val < j.val ∧ j.val < (reverseItem t).val) := by
                omega
              rw [theorem4Problem11ClosedZ_after hleft hj_after]
              rw [if_neg hj_t, if_neg hj_rev, if_neg hnot_int]
              ring
            · have hj_left_strict : t.val < j.val := by
                have hne_val : j.val ≠ t.val := by
                  intro hval
                  exact hj_t (Fin.ext hval)
                omega
              have hj_right_strict : j.val < (reverseItem t).val := by
                have hne_val : j.val ≠ (reverseItem t).val := by
                  intro hval
                  exact hj_rev (Fin.ext hval)
                omega
              rw [theorem4Problem11ClosedZ_interior
                hj_left_strict hj_right_strict]
              rw [if_neg hj_t, if_neg hj_rev,
                if_pos ⟨hj_left_strict, hj_right_strict⟩]
              simp [I]
    calc
      (∑ j : Item n, theorem4Problem11ClosedZ beta v t j)
          =
        ∑ j : Item n,
          ((if j = t then E else 0) +
            (if j = reverseItem t then E else 0) +
            (if t.val < j.val ∧ j.val < (reverseItem t).val then I else 0)) := by
          refine Finset.sum_congr rfl ?_
          intro j _hj
          rw [hpoint j]
      _ =
        (∑ j : Item n, if j = t then E else 0) +
          (∑ j : Item n, if j = reverseItem t then E else 0) +
          (∑ j : Item n,
            if t.val < j.val ∧ j.val < (reverseItem t).val then I else 0) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      _ =
        E + E + theorem4Problem11ClosedZInteriorMass beta v t := by
          simp [theorem4Problem11ClosedZInteriorMass, I]
      _ = 1 := by
          have hE :
              E = (1 - theorem4Problem11ClosedZInteriorMass beta v t) / 2 := by
            dsimp [E]
            simp [theorem4Problem11ClosedZEndpointMass, hcenter]
          rw [hE]
          ring

theorem theorem4Problem11ClosedZ_nonneg {n : ℕ}
    {beta : ℝ} {v : Item n → ℝ} {t : Item n}
    (hbeta_pos : 0 < beta) (hbeta_half : beta < 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hleft : t.val ≤ (reverseItem t).val)
    (hendpoint : 0 ≤ theorem4Problem11ClosedZEndpointMass beta v t) :
    ∀ j : Item n, 0 ≤ theorem4Problem11ClosedZ beta v t j := by
  intro j
  by_cases hj_before : j.val < t.val
  · rw [theorem4Problem11ClosedZ_before hj_before]
  · by_cases hj_after : (reverseItem t).val < j.val
    · rw [theorem4Problem11ClosedZ_after hleft hj_after]
    · by_cases hj_endpoint : j = t ∨ j = reverseItem t
      · rw [theorem4Problem11ClosedZ_endpoint
          hj_before hj_after hj_endpoint]
        exact hendpoint
      · have hj_left_strict : t.val < j.val := by
          have hne : j ≠ t := by
            intro h
            exact hj_endpoint (Or.inl h)
          have hne_val : j.val ≠ t.val := by
            intro hval
            exact hne (Fin.ext hval)
          omega
        have hj_right_strict : j.val < (reverseItem t).val := by
          have hne : j ≠ reverseItem t := by
            intro h
            exact hj_endpoint (Or.inr h)
          have hne_val : j.val ≠ (reverseItem t).val := by
            intro hval
            exact hne (Fin.ext hval)
          omega
        rw [theorem4Problem11ClosedZ_interior
          hj_left_strict hj_right_strict]
        exact div_nonneg
          (theorem4Problem11ClosedDualValue_pos
            hbeta_pos hbeta_half hpos hleft).le
          (by nlinarith : 0 ≤ 1 - 2 * beta)

theorem theorem4Problem11Closed_item_eq_before {n : ℕ}
    {beta : ℝ} {v : Item n → ℝ} {t j : Item n}
    (hbeta_pos : 0 < beta)
    (hpos : ∀ j : Item n, 0 < v j)
    (hleft : t.val ≤ (reverseItem t).val)
    (hj : j.val < t.val) :
    theorem4Problem11ItemValue beta v
      (theorem4Problem11ClosedX beta v t)
      (theorem4Problem11ClosedZ beta v t) j =
        theorem4Problem11ClosedDualValue beta v t := by
  have hrev_after :
      t.val < (reverseItem j).val := by
    have hrev : (reverseItem t).val < (reverseItem j).val :=
      reverseItem_val_lt_of_val_lt hj
    omega
  have hbeta_ne : beta ≠ 0 := ne_of_gt hbeta_pos
  have hq_ne : pairShare (1 / 2) v j ≠ 0 :=
    ne_of_gt (pairShare_pos j (by norm_num) (by norm_num) hpos)
  unfold theorem4Problem11ItemValue
  rw [theorem4Problem11ClosedX_before hj,
    theorem4Problem11ClosedX_after hrev_after,
    theorem4Problem11ClosedZ_before hj]
  field_simp [hbeta_ne, hq_ne]
  ring

theorem theorem4Problem11Closed_item_eq_after {n : ℕ}
    {beta : ℝ} {v : Item n → ℝ} {t j : Item n}
    (hbeta_pos : 0 < beta)
    (hpos : ∀ j : Item n, 0 < v j)
    (hleft : t.val ≤ (reverseItem t).val)
    (hj : (reverseItem t).val < j.val) :
    theorem4Problem11ItemValue beta v
      (theorem4Problem11ClosedX beta v t)
      (theorem4Problem11ClosedZ beta v t) j =
        theorem4Problem11ClosedDualValue beta v t := by
  have hrev_before :
      (reverseItem j).val < t.val := by
    simpa [reverseItem_reverseItem] using
      reverseItem_val_lt_of_val_lt hj
  have htj : t.val < j.val := by omega
  have hbeta_ne : beta ≠ 0 := ne_of_gt hbeta_pos
  have hqrev_ne : pairShare (1 / 2) v (reverseItem j) ≠ 0 :=
    ne_of_gt (pairShare_pos (reverseItem j)
      (by norm_num) (by norm_num) hpos)
  have hq :
      1 - pairShare (1 / 2) v j =
        pairShare (1 / 2) v (reverseItem j) := by
    simpa [reverseItem_reverseItem] using
      (pairShare_half_eq_one_sub_reverse (reverseItem j) hpos).symm
  unfold theorem4Problem11ItemValue
  rw [theorem4Problem11ClosedX_after htj,
    theorem4Problem11ClosedX_before hrev_before,
    theorem4Problem11ClosedZ_after hleft hj, hq]
  field_simp [hbeta_ne, hqrev_ne]
  ring

theorem theorem4Problem11Closed_item_eq_interior {n : ℕ}
    {beta : ℝ} {v : Item n → ℝ} {t j : Item n}
    (hbeta_half : beta < 1 / 2)
    (hleft_j : t.val < j.val)
    (hright_j : j.val < (reverseItem t).val) :
    theorem4Problem11ItemValue beta v
      (theorem4Problem11ClosedX beta v t)
      (theorem4Problem11ClosedZ beta v t) j =
        theorem4Problem11ClosedDualValue beta v t := by
  have hrev_after :
      t.val < (reverseItem j).val := by
    simpa [reverseItem_reverseItem] using
      reverseItem_val_lt_of_val_lt hright_j
  have hc_ne : 1 - 2 * beta ≠ 0 := by nlinarith
  unfold theorem4Problem11ItemValue
  rw [theorem4Problem11ClosedX_after hleft_j,
    theorem4Problem11ClosedX_after hrev_after,
    theorem4Problem11ClosedZ_interior hleft_j hright_j]
  field_simp [hc_ne]
  ring

theorem theorem4Problem11Closed_item_eq_pivot_of_lt_mirror {n : ℕ}
    {beta : ℝ} {v : Item n → ℝ} {t : Item n}
    (hbeta_pos : 0 < beta)
    (hbeta_half : beta < 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hstrict : t.val < (reverseItem t).val) :
    theorem4Problem11ItemValue beta v
      (theorem4Problem11ClosedX beta v t)
      (theorem4Problem11ClosedZ beta v t) t =
        theorem4Problem11ClosedDualValue beta v t := by
  have hbeta_ne : beta ≠ 0 := ne_of_gt hbeta_pos
  have hc_ne : 1 - 2 * beta ≠ 0 := by nlinarith
  have hden_pos :
      0 <
        2 * pairShare (1 / 2) v t * theorem4Problem11LeftSum v t +
          ((n : ℝ) - 2 * (t.val : ℝ)) := by
    have hDpos :
        0 < theorem4Problem11ClosedDualDenominator v t :=
      theorem4Problem11ClosedDualDenominator_pos
        (v := v) (t := t) hpos (le_of_lt hstrict)
    rwa [theorem4Problem11ClosedDualDenominator_eq (le_of_lt hstrict)] at hDpos
  have hden_ne :
      2 * pairShare (1 / 2) v t * theorem4Problem11LeftSum v t +
          ((n : ℝ) - 2 * (t.val : ℝ)) ≠ 0 :=
    ne_of_gt hden_pos
  have hx_t :
      theorem4Problem11ClosedX beta v t t =
        1 -
          (theorem4Problem11ClosedDualValue beta v t / (2 * beta)) *
            theorem4Problem11LeftSum v t :=
    theorem4Problem11ClosedX_at_eq_one_sub_leftSum hbeta_pos hpos
  have hx_rev :
      theorem4Problem11ClosedX beta v t (reverseItem t) = 0 :=
    theorem4Problem11ClosedX_after hstrict
  have hz_t :
      theorem4Problem11ClosedZ beta v t t =
        theorem4Problem11ClosedZEndpointMass beta v t := by
    have hnleft : ¬ t.val < t.val := by omega
    have hnafter : ¬ (reverseItem t).val < t.val := by omega
    exact theorem4Problem11ClosedZ_endpoint
      hnleft hnafter (Or.inl rfl)
  have hendpoint :
      theorem4Problem11ClosedZEndpointMass beta v t =
        (1 -
          (((n : ℝ) - 2 * (t.val : ℝ) - 2) *
            (theorem4Problem11ClosedDualValue beta v t /
              (1 - 2 * beta)))) / 2 := by
    unfold theorem4Problem11ClosedZEndpointMass
    have hne : t ≠ reverseItem t := by
      intro h
      have hval := congrArg Fin.val h
      omega
    rw [if_neg hne, theorem4Problem11ClosedZInteriorMass_eq hstrict]
  unfold theorem4Problem11ItemValue
  rw [hx_t, hx_rev, hz_t, hendpoint,
    theorem4Problem11ClosedDualValue_eq_fullPolicy_formula
      (le_of_lt hstrict)]
  field_simp [hbeta_ne, hc_ne, hden_ne]
  ring

theorem theorem4Problem11Closed_item_eq_mirror_pivot_of_lt_mirror {n : ℕ}
    {beta : ℝ} {v : Item n → ℝ} {t : Item n}
    (hbeta_pos : 0 < beta)
    (hbeta_half : beta < 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hstrict : t.val < (reverseItem t).val) :
    theorem4Problem11ItemValue beta v
      (theorem4Problem11ClosedX beta v t)
      (theorem4Problem11ClosedZ beta v t) (reverseItem t) =
        theorem4Problem11ClosedDualValue beta v t := by
  have hbeta_ne : beta ≠ 0 := ne_of_gt hbeta_pos
  have hc_ne : 1 - 2 * beta ≠ 0 := by nlinarith
  have hden_pos :
      0 <
        2 * pairShare (1 / 2) v t * theorem4Problem11LeftSum v t +
          ((n : ℝ) - 2 * (t.val : ℝ)) := by
    have hDpos :
        0 < theorem4Problem11ClosedDualDenominator v t :=
      theorem4Problem11ClosedDualDenominator_pos
        (v := v) (t := t) hpos (le_of_lt hstrict)
    rwa [theorem4Problem11ClosedDualDenominator_eq (le_of_lt hstrict)] at hDpos
  have hden_ne :
      2 * pairShare (1 / 2) v t * theorem4Problem11LeftSum v t +
          ((n : ℝ) - 2 * (t.val : ℝ)) ≠ 0 :=
    ne_of_gt hden_pos
  have hx_t :
      theorem4Problem11ClosedX beta v t t =
        1 -
          (theorem4Problem11ClosedDualValue beta v t / (2 * beta)) *
            theorem4Problem11LeftSum v t :=
    theorem4Problem11ClosedX_at_eq_one_sub_leftSum hbeta_pos hpos
  have hx_rev :
      theorem4Problem11ClosedX beta v t (reverseItem t) = 0 :=
    theorem4Problem11ClosedX_after hstrict
  have hz_rev :
      theorem4Problem11ClosedZ beta v t (reverseItem t) =
        theorem4Problem11ClosedZEndpointMass beta v t := by
    have hnleft : ¬ (reverseItem t).val < t.val := by omega
    have hnafter :
        ¬ (reverseItem t).val < (reverseItem t).val := by omega
    exact theorem4Problem11ClosedZ_endpoint
      hnleft hnafter (Or.inr rfl)
  have hendpoint :
      theorem4Problem11ClosedZEndpointMass beta v t =
        (1 -
          (((n : ℝ) - 2 * (t.val : ℝ) - 2) *
            (theorem4Problem11ClosedDualValue beta v t /
              (1 - 2 * beta)))) / 2 := by
    unfold theorem4Problem11ClosedZEndpointMass
    have hne : t ≠ reverseItem t := by
      intro h
      have hval := congrArg Fin.val h
      omega
    rw [if_neg hne, theorem4Problem11ClosedZInteriorMass_eq hstrict]
  have hq :
      1 - pairShare (1 / 2) v (reverseItem t) =
        pairShare (1 / 2) v t :=
    (pairShare_half_eq_one_sub_reverse t hpos).symm
  unfold theorem4Problem11ItemValue
  rw [hx_rev, reverseItem_reverseItem, hx_t, hz_rev, hendpoint, hq,
    theorem4Problem11ClosedDualValue_eq_fullPolicy_formula
      (le_of_lt hstrict)]
  field_simp [hbeta_ne, hc_ne, hden_ne]
  ring

theorem theorem4Problem11Closed_item_eq_center {n : ℕ}
    {beta : ℝ} {v : Item n → ℝ} {t : Item n}
    (hbeta_pos : 0 < beta)
    (hpos : ∀ j : Item n, 0 < v j)
    (hcenter : t.val = (reverseItem t).val) :
    theorem4Problem11ItemValue beta v
      (theorem4Problem11ClosedX beta v t)
      (theorem4Problem11ClosedZ beta v t) t =
        theorem4Problem11ClosedDualValue beta v t := by
  have hbeta_ne : beta ≠ 0 := ne_of_gt hbeta_pos
  have hcenter_item : t = reverseItem t := Fin.ext hcenter
  have hq : pairShare (1 / 2) v t = (1 / 2 : ℝ) :=
    pairShare_half_eq_half_of_val_eq_reverse t hpos hcenter
  have hcenter_nat : 2 * t.val + 1 = n :=
    (val_eq_reverseItem_iff t).mp hcenter
  have hcenter_real : (n : ℝ) - 2 * (t.val : ℝ) = 1 := by
    have hcast : (2 * t.val + 1 : ℝ) = (n : ℝ) := by
      exact_mod_cast hcenter_nat
    nlinarith
  have hden_pos :
      0 <
        2 * pairShare (1 / 2) v t * theorem4Problem11LeftSum v t +
          ((n : ℝ) - 2 * (t.val : ℝ)) := by
    have hDpos :
        0 < theorem4Problem11ClosedDualDenominator v t :=
      theorem4Problem11ClosedDualDenominator_pos
        (v := v) (t := t) hpos (le_of_eq hcenter)
    rwa [theorem4Problem11ClosedDualDenominator_eq (le_of_eq hcenter)] at hDpos
  have hden_ne :
      2 * pairShare (1 / 2) v t * theorem4Problem11LeftSum v t +
          ((n : ℝ) - 2 * (t.val : ℝ)) ≠ 0 :=
    ne_of_gt hden_pos
  have hcenter_den_ne : 1 + theorem4Problem11LeftSum v t ≠ 0 := by
    have hL_nonneg : 0 ≤ theorem4Problem11LeftSum v t :=
      theorem4Problem11LeftSum_nonneg hpos t
    nlinarith
  have hx_t :
      theorem4Problem11ClosedX beta v t t =
        1 -
          (theorem4Problem11ClosedDualValue beta v t / (2 * beta)) *
            theorem4Problem11LeftSum v t :=
    theorem4Problem11ClosedX_at_eq_one_sub_leftSum hbeta_pos hpos
  have hz_t : theorem4Problem11ClosedZ beta v t t = 1 := by
    have hnleft : ¬ t.val < t.val := by omega
    have hnafter : ¬ (reverseItem t).val < t.val := by
      rw [hcenter]
      omega
    rw [theorem4Problem11ClosedZ_endpoint
      hnleft hnafter (Or.inl rfl)]
    unfold theorem4Problem11ClosedZEndpointMass
    rw [if_pos hcenter_item]
  unfold theorem4Problem11ItemValue
  rw [← hcenter_item, hx_t, hz_t, hq,
    theorem4Problem11ClosedDualValue_eq_fullPolicy_formula
      (le_of_eq hcenter)]
  rw [hcenter_real, hq]
  ring_nf
  field_simp [hbeta_ne]
  ring_nf

theorem theorem4Problem11Closed_item_eq {n : ℕ}
    {beta : ℝ} {v : Item n → ℝ} {t : Item n}
    (hbeta_pos : 0 < beta)
    (hbeta_half : beta < 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hleft : t.val ≤ (reverseItem t).val) :
    ∀ j : Item n,
      theorem4Problem11ItemValue beta v
        (theorem4Problem11ClosedX beta v t)
        (theorem4Problem11ClosedZ beta v t) j =
          theorem4Problem11ClosedDualValue beta v t := by
  intro j
  by_cases hcenter : t.val = (reverseItem t).val
  · by_cases hjt : j = t
    · subst j
      exact theorem4Problem11Closed_item_eq_center
        hbeta_pos hpos hcenter
    · have hval_ne : j.val ≠ t.val := by
        intro hval
        exact hjt (Fin.ext hval)
      rcases lt_or_gt_of_ne hval_ne with hj_before | hj_after
      · exact theorem4Problem11Closed_item_eq_before
          hbeta_pos hpos hleft hj_before
      · have hj_after_rev : (reverseItem t).val < j.val := by
          omega
        exact theorem4Problem11Closed_item_eq_after
          hbeta_pos hpos hleft hj_after_rev
  · have hstrict : t.val < (reverseItem t).val := by omega
    by_cases hjt : j = t
    · subst j
      exact theorem4Problem11Closed_item_eq_pivot_of_lt_mirror
        hbeta_pos hbeta_half hpos hstrict
    · by_cases hjrev : j = reverseItem t
      · subst j
        exact theorem4Problem11Closed_item_eq_mirror_pivot_of_lt_mirror
          hbeta_pos hbeta_half hpos hstrict
      · by_cases hj_before : j.val < t.val
        · exact theorem4Problem11Closed_item_eq_before
            hbeta_pos hpos hleft hj_before
        · by_cases hj_after : (reverseItem t).val < j.val
          · exact theorem4Problem11Closed_item_eq_after
              hbeta_pos hpos hleft hj_after
          · have hj_left : t.val < j.val := by
              have hne_val : j.val ≠ t.val := by
                intro hval
                exact hjt (Fin.ext hval)
              omega
            have hj_right : j.val < (reverseItem t).val := by
              have hne_val : j.val ≠ (reverseItem t).val := by
                intro hval
                exact hjrev (Fin.ext hval)
              omega
            exact theorem4Problem11Closed_item_eq_interior
              hbeta_half hj_left hj_right

theorem theorem4Problem11Closed_realLPFeasible {n : ℕ}
    {beta : ℝ} {v : Item n → ℝ} {t : Item n}
    (hbeta_pos : 0 < beta)
    (hbeta_half : beta < 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hleft : t.val ≤ (reverseItem t).val)
    (hpivot : 0 ≤ theorem4Problem11ClosedX beta v t t)
    (hendpoint : 0 ≤ theorem4Problem11ClosedZEndpointMass beta v t) :
    Theorem4Problem11RealLPFeasible beta v
      (theorem4Problem11ClosedX beta v t)
      (theorem4Problem11ClosedZ beta v t)
      (theorem4Problem11ClosedDualValue beta v t) where
  x_nonneg :=
    theorem4Problem11ClosedX_nonneg
      hbeta_pos hbeta_half hpos hleft hpivot
  z_nonneg :=
    theorem4Problem11ClosedZ_nonneg
      hbeta_pos hbeta_half hpos hleft hendpoint
  sum_x := theorem4Problem11ClosedX_sum_eq_one beta v t
  sum_z := theorem4Problem11ClosedZ_sum_eq_one hleft
  z_mirror := fun j => theorem4Problem11ClosedZ_mirror (t := t) (j := j) hleft
  item_le := fun j =>
    le_of_eq
      ((theorem4Problem11Closed_item_eq
        hbeta_pos hbeta_half hpos hleft j).symm)

noncomputable def theorem4Problem11ClosedPolicy {n : ℕ}
    (beta : ℝ) (v : Item n → ℝ) (t : Item n)
    (hbeta_pos : 0 < beta)
    (hbeta_half : beta < 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hleft : t.val ≤ (reverseItem t).val)
    (hpivot : 0 ≤ theorem4Problem11ClosedX beta v t t)
    (hendpoint : 0 ≤ theorem4Problem11ClosedZEndpointMass beta v t) :
    TypePolicy 3 n :=
  theorem4Problem11PolicyOfRealVectors
    (theorem4Problem11ClosedX beta v t)
    (theorem4Problem11ClosedZ beta v t)
    (theorem4Problem11ClosedX_nonneg
      hbeta_pos hbeta_half hpos hleft hpivot)
    (theorem4Problem11ClosedZ_nonneg
      hbeta_pos hbeta_half hpos hleft hendpoint)
    (theorem4Problem11ClosedX_sum_eq_one beta v t)
    (theorem4Problem11ClosedZ_sum_eq_one hleft)

/--
The closed-form policy is globally optimal directly from its primal
feasibility and the closed dual certificate.
-/
theorem theorem4Problem11ClosedPolicyOptimal_of_witness {n : ℕ}
    [NeZero n] {beta : ℝ} {v : Item n → ℝ} {t : Item n}
    (hbeta_pos : 0 < beta)
    (hbeta_half : beta < 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hleft : t.val ≤ (reverseItem t).val)
    (hpivot : 0 ≤ theorem4Problem11ClosedX beta v t t)
    (hendpoint : 0 ≤ theorem4Problem11ClosedZEndpointMass beta v t) :
    Theorem4Problem11PolicyOptimal beta v
      (theorem4Problem11ClosedPolicy beta v t
        hbeta_pos hbeta_half hpos hleft hpivot hendpoint)
      (theorem4Problem11ClosedDualValue beta v t) := by
  let hfeas :
      Theorem4Problem11RealLPFeasible beta v
        (theorem4Problem11ClosedX beta v t)
        (theorem4Problem11ClosedZ beta v t)
        (theorem4Problem11ClosedDualValue beta v t) :=
    theorem4Problem11Closed_realLPFeasible
      hbeta_pos hbeta_half hpos hleft hpivot hendpoint
  simpa [theorem4Problem11ClosedPolicy, hfeas] using
    (theorem4Problem11PolicyOptimal_of_closedDual_feasible
      hbeta_pos.le (by nlinarith) hpos hdec hleft hfeas)

theorem theorem4Problem11ClosedPolicy_pivotSupport {n : ℕ}
    {beta : ℝ} {v : Item n → ℝ} {t : Item n}
    (hbeta_pos : 0 < beta)
    (hbeta_half : beta < 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hleft : t.val ≤ (reverseItem t).val)
    (hpivot : 0 ≤ theorem4Problem11ClosedX beta v t t)
    (hendpoint : 0 ≤ theorem4Problem11ClosedZEndpointMass beta v t) :
    Theorem4Problem11PivotSupport
      (theorem4Problem11ClosedPolicy beta v t
        hbeta_pos hbeta_half hpos hleft hpivot hendpoint) t := by
  constructor
  · intro j hj
    apply pmf_apply_eq_zero_of_toReal_eq_zero
    simp [theorem4Problem11ClosedPolicy,
      theorem4Problem11ClosedX_after hj]
  · intro j hj
    constructor
    · apply pmf_apply_eq_zero_of_toReal_eq_zero
      simp [theorem4Problem11ClosedPolicy,
        theorem4Problem11ClosedZ_before hj]
    · apply pmf_apply_eq_zero_of_toReal_eq_zero
      have hrev_after :
          (reverseItem t).val < (reverseItem j).val :=
        reverseItem_val_lt_of_val_lt hj
      simp [theorem4Problem11ClosedPolicy,
        theorem4Problem11ClosedZ_after hleft hrev_after]

theorem theorem4Problem11ClosedPolicy_basicFeasibleSupportCertificate {n : ℕ}
    {beta : ℝ} {v : Item n → ℝ} {t : Item n}
    (hbeta_pos : 0 < beta)
    (hbeta_half : beta < 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hleft : t.val ≤ (reverseItem t).val)
    (hpivot : 0 ≤ theorem4Problem11ClosedX beta v t t)
    (hendpoint : 0 ≤ theorem4Problem11ClosedZEndpointMass beta v t) :
    TypePolicy.BasicFeasibleSupportCertificate
      (theorem4Problem11ClosedPolicy beta v t
        hbeta_pos hbeta_half hpos hleft hpivot hendpoint) := by
  classical
  let ρ : TypePolicy 3 n :=
    theorem4Problem11ClosedPolicy beta v t
      hbeta_pos hbeta_half hpos hleft hpivot hendpoint
  let D0 : Type := {j : Item n // j ∈ (Finset.Ioi t : Finset (Item n))}
  let D1 : Type :=
    {j : Item n // j ∈ (Finset.Iio (reverseItem t) : Finset (Item n))}
  let D2 : Type := {j : Item n // j ∈ (Finset.Iio t : Finset (Item n))}
  let D3 : Type :=
    {j : Item n // j ∈ (Finset.Ioi (reverseItem t) : Finset (Item n))}
  let Domain : Type := (D0 ⊕ D1) ⊕ (D2 ⊕ D3)
  let f :
      Domain →
        {p : UserType 3 × Item n // p ∈ TypePolicy.inactiveTypeItemPairs ρ} :=
    fun d =>
      match d with
      | Sum.inl (Sum.inl j) =>
          ⟨(0, j.1), by
            have hj : t.val < j.1.val := by
              have hj' : t < j.1 := Finset.mem_Ioi.mp j.2
              exact hj'
            have hz : ρ 0 j.1 = 0 := by
              apply pmf_apply_eq_zero_of_toReal_eq_zero
              simp [ρ, theorem4Problem11ClosedPolicy,
                theorem4Problem11ClosedX_after hj]
            exact (TypePolicy.mem_inactiveTypeItemPairs ρ (0, j.1)).2 hz⟩
      | Sum.inl (Sum.inr j) =>
          ⟨(1, j.1), by
            have hj : j.1.val < (reverseItem t).val := by
              have hj' : j.1 < reverseItem t := Finset.mem_Iio.mp j.2
              exact hj'
            have hrev_after : t.val < (reverseItem j.1).val := by
              simpa [reverseItem_reverseItem] using
                (reverseItem_val_lt_of_val_lt hj)
            have hz : ρ 1 j.1 = 0 := by
              apply pmf_apply_eq_zero_of_toReal_eq_zero
              simp [ρ, theorem4Problem11ClosedPolicy,
                theorem4Problem11ClosedX_after hrev_after]
            exact (TypePolicy.mem_inactiveTypeItemPairs ρ (1, j.1)).2 hz⟩
      | Sum.inr (Sum.inl j) =>
          ⟨(2, j.1), by
            have hj : j.1.val < t.val := by
              have hj' : j.1 < t := Finset.mem_Iio.mp j.2
              exact hj'
            have hz : ρ 2 j.1 = 0 := by
              apply pmf_apply_eq_zero_of_toReal_eq_zero
              simp [ρ, theorem4Problem11ClosedPolicy,
                theorem4Problem11ClosedZ_before hj]
            exact (TypePolicy.mem_inactiveTypeItemPairs ρ (2, j.1)).2 hz⟩
      | Sum.inr (Sum.inr j) =>
          ⟨(2, j.1), by
            have hj : (reverseItem t).val < j.1.val := by
              have hj' : reverseItem t < j.1 := Finset.mem_Ioi.mp j.2
              exact hj'
            have hz : ρ 2 j.1 = 0 := by
              apply pmf_apply_eq_zero_of_toReal_eq_zero
              simp [ρ, theorem4Problem11ClosedPolicy,
                theorem4Problem11ClosedZ_after hleft hj]
            exact (TypePolicy.mem_inactiveTypeItemPairs ρ (2, j.1)).2 hz⟩
  have hf : Function.Injective f := by
    intro a b hab
    have hpair := congrArg (fun q :
      {p : UserType 3 × Item n // p ∈ TypePolicy.inactiveTypeItemPairs ρ} =>
        q.1) hab
    cases a with
    | inl a01 =>
        cases a01 with
        | inl a0 =>
            cases b with
            | inl b01 =>
                cases b01 with
                | inl b0 =>
                    have hitem : a0.1 = b0.1 := by
                      simpa [f] using congrArg Prod.snd hpair
                    exact congrArg Sum.inl (congrArg Sum.inl (Subtype.ext hitem))
                | inr b1 =>
                    have htype := congrArg Prod.fst hpair
                    simp [f] at htype
            | inr b23 =>
                cases b23 with
                | inl b2 =>
                    have htype := congrArg Prod.fst hpair
                    simp [f] at htype
                | inr b3 =>
                    have htype := congrArg Prod.fst hpair
                    simp [f] at htype
        | inr a1 =>
            cases b with
            | inl b01 =>
                cases b01 with
                | inl b0 =>
                    have htype := congrArg Prod.fst hpair
                    simp [f] at htype
                | inr b1 =>
                    have hitem : a1.1 = b1.1 := by
                      simpa [f] using congrArg Prod.snd hpair
                    exact congrArg Sum.inl (congrArg Sum.inr (Subtype.ext hitem))
            | inr b23 =>
                cases b23 with
                | inl b2 =>
                    have htype := congrArg Prod.fst hpair
                    simp [f] at htype
                | inr b3 =>
                    have htype := congrArg Prod.fst hpair
                    simp [f] at htype
    | inr a23 =>
        cases a23 with
        | inl a2 =>
            cases b with
            | inl b01 =>
                cases b01 with
                | inl b0 =>
                    have htype := congrArg Prod.fst hpair
                    simp [f] at htype
                | inr b1 =>
                    have htype := congrArg Prod.fst hpair
                    simp [f] at htype
            | inr b23 =>
                cases b23 with
                | inl b2 =>
                    have hitem : a2.1 = b2.1 := by
                      simpa [f] using congrArg Prod.snd hpair
                    exact congrArg Sum.inr (congrArg Sum.inl (Subtype.ext hitem))
                | inr b3 =>
                    have hitem : a2.1 = b3.1 := by
                      simpa [f] using congrArg Prod.snd hpair
                    have ha : a2.1.val < t.val := by
                      have ha' : a2.1 < t := Finset.mem_Iio.mp a2.2
                      exact ha'
                    have hb : (reverseItem t).val < a2.1.val := by
                      have hb' : reverseItem t < b3.1 :=
                        Finset.mem_Ioi.mp b3.2
                      rw [hitem]
                      exact hb'
                    omega
        | inr a3 =>
            cases b with
            | inl b01 =>
                cases b01 with
                | inl b0 =>
                    have htype := congrArg Prod.fst hpair
                    simp [f] at htype
                | inr b1 =>
                    have htype := congrArg Prod.fst hpair
                    simp [f] at htype
            | inr b23 =>
                cases b23 with
                | inl b2 =>
                    have hitem : a3.1 = b2.1 := by
                      simpa [f] using congrArg Prod.snd hpair
                    have ha : (reverseItem t).val < a3.1.val := by
                      have ha' : reverseItem t < a3.1 :=
                        Finset.mem_Ioi.mp a3.2
                      exact ha'
                    have hb : a3.1.val < t.val := by
                      have hb' : b2.1 < t := Finset.mem_Iio.mp b2.2
                      rw [hitem]
                      exact hb'
                    omega
                | inr b3 =>
                    have hitem : a3.1 = b3.1 := by
                      simpa [f] using congrArg Prod.snd hpair
                    exact congrArg Sum.inr (congrArg Sum.inr (Subtype.ext hitem))
  have hcard :=
    Fintype.card_le_of_injective f hf
  have hD0 : Fintype.card D0 = n - 1 - t.val := by
    dsimp [D0]
    rw [Fintype.card_coe, Fin.card_Ioi]
  have hD1 : Fintype.card D1 = (reverseItem t).val := by
    dsimp [D1]
    rw [Fintype.card_coe, Fin.card_Iio]
  have hD2 : Fintype.card D2 = t.val := by
    dsimp [D2]
    rw [Fintype.card_coe, Fin.card_Iio]
  have hD3 : Fintype.card D3 = n - 1 - (reverseItem t).val := by
    dsimp [D3]
    rw [Fintype.card_coe, Fin.card_Ioi]
  have hDomain_card : Fintype.card Domain = 2 * n - 2 := by
    dsimp [Domain]
    rw [Fintype.card_sum, Fintype.card_sum, Fintype.card_sum,
      hD0, hD1, hD2, hD3]
    simp [reverseItem]
    omega
  have hinactive_card :
      Fintype.card
          {p : UserType 3 × Item n // p ∈ TypePolicy.inactiveTypeItemPairs ρ} =
        TypePolicy.inactiveTypeItemPairsCard ρ := by
    simpa [TypePolicy.inactiveTypeItemPairsCard,
      TypePolicy.inactiveTypeItemPairs] using
      (Fintype.card_coe (TypePolicy.inactiveTypeItemPairs ρ))
  unfold TypePolicy.BasicFeasibleSupportCertificate
  rw [← hinactive_card]
  have hzero_count :
      2 * n - 2 ≤
        Fintype.card
          {p : UserType 3 × Item n // p ∈ TypePolicy.inactiveTypeItemPairs ρ} := by
    simpa [hDomain_card] using hcard
  omega

theorem theorem4Problem11ClosedDualValue_eq_pivotOneLambda {n : ℕ}
    [NeZero n] {beta : ℝ} {v : Item n → ℝ} {t : Item n}
    (hn : 1 < n) (ht : t = theorem4FirstItem) :
    theorem4Problem11ClosedDualValue beta v t =
      theorem4Problem11PivotOneLambda beta v := by
  subst t
  have hleft :
      (theorem4FirstItem : Item n).val ≤
        (reverseItem (theorem4FirstItem : Item n)).val := by
    simp [theorem4FirstItem, reverseItem]
  have hleftsum :
      theorem4Problem11LeftSum v (theorem4FirstItem : Item n) = 0 := by
    unfold theorem4Problem11LeftSum
    simp [theorem4FirstItem]
  have hnpos_nat : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hn_ne : (n : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hnpos_nat)
  rw [theorem4Problem11ClosedDualValue_eq_fullPolicy_formula hleft]
  unfold theorem4Problem11PivotOneLambda
  rw [hleftsum]
  simp [theorem4FirstItem]
  field_simp [hn_ne]
  ring

theorem theorem4Problem11ClosedZ_first_eq_pivotOneZ {n : ℕ}
    [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hn : 1 < n) :
    theorem4Problem11ClosedZ beta v theorem4FirstItem theorem4FirstItem =
      theorem4Problem11PivotOneZ beta v := by
  have hstrict :
      (theorem4FirstItem : Item n).val <
        (reverseItem (theorem4FirstItem : Item n)).val := by
    simp [theorem4FirstItem, reverseItem]
    omega
  have hz_endpoint :
      theorem4Problem11ClosedZ beta v theorem4FirstItem theorem4FirstItem =
        theorem4Problem11ClosedZEndpointMass beta v theorem4FirstItem := by
    have hnleft :
        ¬ (theorem4FirstItem : Item n).val <
          (theorem4FirstItem : Item n).val := by omega
    have hnafter :
        ¬ (reverseItem (theorem4FirstItem : Item n)).val <
          (theorem4FirstItem : Item n).val := by omega
    exact theorem4Problem11ClosedZ_endpoint
      hnleft hnafter (Or.inl rfl)
  rw [hz_endpoint]
  unfold theorem4Problem11ClosedZEndpointMass
  have hne :
      (theorem4FirstItem : Item n) ≠
        reverseItem (theorem4FirstItem : Item n) := by
    intro h
    have hval := congrArg Fin.val h
    simp [theorem4FirstItem, reverseItem] at hval
    omega
  rw [if_neg hne, theorem4Problem11ClosedZInteriorMass_eq hstrict,
    theorem4Problem11ClosedDualValue_eq_pivotOneLambda hn rfl]
  unfold theorem4Problem11PivotOneZ
  simp [theorem4FirstItem]
  ring

theorem theorem4Problem11ClosedPolicy_first_closedZ_eq_pivotOneZ {n : ℕ}
    [NeZero n] {beta : ℝ} {v : Item n → ℝ} {t : Item n}
    (hn : 1 < n)
    (hbeta_pos : 0 < beta)
    (hbeta_half : beta < 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hleft : t.val ≤ (reverseItem t).val)
    (hpivot : 0 ≤ theorem4Problem11ClosedX beta v t t)
    (hendpoint : 0 ≤ theorem4Problem11ClosedZEndpointMass beta v t)
    (ht : t = theorem4FirstItem) :
    ((theorem4Problem11ClosedPolicy beta v t
        hbeta_pos hbeta_half hpos hleft hpivot hendpoint) 2
      theorem4FirstItem).toReal =
      theorem4Problem11PivotOneZ beta v := by
  subst t
  simp [theorem4Problem11ClosedPolicy,
    theorem4Problem11ClosedZ_first_eq_pivotOneZ hn]

structure Theorem4Problem11ClosedPivotBounds {n : ℕ}
    (beta : ℝ) (v : Item n → ℝ) (t : Item n) : Prop where
  known_pivot :
    (1 - 2 * beta) * theorem4Problem11LeftSum v t ≤
      2 * beta * ((n : ℝ) - 2 * (t.val : ℝ))
  cold_endpoint :
    (((n : ℝ) - 2 * (t.val : ℝ) - 2) *
        (4 * beta * pairShare (1 / 2) v t + (1 - 2 * beta))) ≤
      (1 - 2 * beta) *
        (2 * pairShare (1 / 2) v t *
            theorem4Problem11LeftSum v t +
          ((n : ℝ) - 2 * (t.val : ℝ)))

def Theorem4Problem11ColdEndpointBound {n : ℕ}
    (beta : ℝ) (v : Item n → ℝ) (t : Item n) : Prop :=
  (((n : ℝ) - 2 * (t.val : ℝ) - 2) *
      (4 * beta * pairShare (1 / 2) v t + (1 - 2 * beta))) ≤
    (1 - 2 * beta) *
      (2 * pairShare (1 / 2) v t *
          theorem4Problem11LeftSum v t +
        ((n : ℝ) - 2 * (t.val : ℝ)))

noncomputable def theorem4Problem11ColdEndpointCrossingSet {n : ℕ}
    (beta : ℝ) (v : Item n → ℝ) : Finset (Item n) :=
  by
    classical
    exact Finset.univ.filter
      (fun t : Item n => Theorem4Problem11ColdEndpointBound beta v t)

theorem theorem4Problem11ColdEndpointBound_of_center {n : ℕ}
    {beta : ℝ} {v : Item n → ℝ} {c : Item n}
    (hbeta_pos : 0 < beta)
    (hbeta_half : beta < 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hcenter : c.val = (OpposingTypes.reverseItem c).val) :
    Theorem4Problem11ColdEndpointBound beta v c := by
  unfold Theorem4Problem11ColdEndpointBound
  have hq_pos : 0 < pairShare (1 / 2) v c :=
    pairShare_pos c (by norm_num) (by norm_num) hpos
  have hL_nonneg : 0 ≤ theorem4Problem11LeftSum v c :=
    theorem4Problem11LeftSum_nonneg hpos c
  have htail : (n : ℝ) - 2 * (c.val : ℝ) - 2 = -1 := by
    have hc_nat : 2 * c.val + 1 = n :=
      (val_eq_reverseItem_iff c).mp hcenter
    have hc_real : (2 * c.val + 1 : ℝ) = (n : ℝ) := by
      exact_mod_cast hc_nat
    nlinarith
  rw [htail]
  nlinarith [mul_nonneg hq_pos.le hL_nonneg]

theorem theorem4Problem11ColdEndpointCrossingSet_nonempty_of_center
    {n : ℕ} {beta : ℝ} {v : Item n → ℝ} {c : Item n}
    (hbeta_pos : 0 < beta)
    (hbeta_half : beta < 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hcenter : c.val = (OpposingTypes.reverseItem c).val) :
    (theorem4Problem11ColdEndpointCrossingSet beta v).Nonempty := by
  have hcold :
      Theorem4Problem11ColdEndpointBound beta v c :=
    theorem4Problem11ColdEndpointBound_of_center
      hbeta_pos hbeta_half hpos hcenter
  exact ⟨c, by
    simpa [theorem4Problem11ColdEndpointCrossingSet] using hcold⟩

theorem theorem4Problem11ColdEndpointBound_of_succ_center {n : ℕ}
    {beta : ℝ} {v : Item n → ℝ} {c : Item n}
    (hbeta_pos : 0 < beta)
    (hbeta_half : beta < 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hsucc : c.val + 1 = (OpposingTypes.reverseItem c).val) :
    Theorem4Problem11ColdEndpointBound beta v c := by
  unfold Theorem4Problem11ColdEndpointBound
  have hq_pos : 0 < pairShare (1 / 2) v c :=
    pairShare_pos c (by norm_num) (by norm_num) hpos
  have hL_nonneg : 0 ≤ theorem4Problem11LeftSum v c :=
    theorem4Problem11LeftSum_nonneg hpos c
  have htail : (n : ℝ) - 2 * (c.val : ℝ) - 2 = 0 := by
    have hc_nat : 2 * c.val + 2 = n := by
      simp [reverseItem] at hsucc
      omega
    have hc_real : (2 * c.val + 2 : ℝ) = (n : ℝ) := by
      exact_mod_cast hc_nat
    nlinarith
  rw [htail]
  nlinarith [mul_nonneg hq_pos.le hL_nonneg]

theorem theorem4Problem11ColdEndpointCrossingSet_nonempty_of_succ_center
    {n : ℕ} {beta : ℝ} {v : Item n → ℝ} {c : Item n}
    (hbeta_pos : 0 < beta)
    (hbeta_half : beta < 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hsucc : c.val + 1 = (OpposingTypes.reverseItem c).val) :
    (theorem4Problem11ColdEndpointCrossingSet beta v).Nonempty := by
  have hcold :
      Theorem4Problem11ColdEndpointBound beta v c :=
    theorem4Problem11ColdEndpointBound_of_succ_center
      hbeta_pos hbeta_half hpos hsucc
  exact ⟨c, by
    simpa [theorem4Problem11ColdEndpointCrossingSet] using hcold⟩

noncomputable def theorem4Problem11FirstColdEndpointPivot {n : ℕ}
    (beta : ℝ) (v : Item n → ℝ)
    (hnonempty :
      (theorem4Problem11ColdEndpointCrossingSet beta v).Nonempty) :
    Item n :=
  Classical.choose
    (Finset.exists_min_image
      (theorem4Problem11ColdEndpointCrossingSet beta v)
      (fun t : Item n => t.val) hnonempty)

theorem theorem4Problem11FirstColdEndpointPivot_mem_crossingSet {n : ℕ}
    {beta : ℝ} {v : Item n → ℝ}
    (hnonempty :
      (theorem4Problem11ColdEndpointCrossingSet beta v).Nonempty) :
    theorem4Problem11FirstColdEndpointPivot beta v hnonempty ∈
      theorem4Problem11ColdEndpointCrossingSet beta v := by
  exact (Classical.choose_spec
    (Finset.exists_min_image
      (theorem4Problem11ColdEndpointCrossingSet beta v)
      (fun t : Item n => t.val) hnonempty)).1

theorem theorem4Problem11FirstColdEndpointPivot_min {n : ℕ}
    {beta : ℝ} {v : Item n → ℝ}
    (hnonempty :
      (theorem4Problem11ColdEndpointCrossingSet beta v).Nonempty)
    {u : Item n}
    (hu : u ∈ theorem4Problem11ColdEndpointCrossingSet beta v) :
    (theorem4Problem11FirstColdEndpointPivot beta v hnonempty).val ≤
      u.val := by
  exact (Classical.choose_spec
    (Finset.exists_min_image
      (theorem4Problem11ColdEndpointCrossingSet beta v)
      (fun t : Item n => t.val) hnonempty)).2 u hu

theorem theorem4Problem11FirstColdEndpointPivot_closedPivotBounds
    {n : ℕ} {beta : ℝ} {v : Item n → ℝ}
    (hbeta_pos : 0 < beta)
    (hbeta_half : beta < 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hnonempty :
      (theorem4Problem11ColdEndpointCrossingSet beta v).Nonempty) :
    Theorem4Problem11ClosedPivotBounds beta v
      (theorem4Problem11FirstColdEndpointPivot beta v hnonempty) := by
  classical
  let t : Item n := theorem4Problem11FirstColdEndpointPivot beta v hnonempty
  have htmem :
      t ∈ theorem4Problem11ColdEndpointCrossingSet beta v := by
    simpa [t] using
      theorem4Problem11FirstColdEndpointPivot_mem_crossingSet
        (beta := beta) (v := v) hnonempty
  have hmin :
      ∀ u : Item n,
        u ∈ theorem4Problem11ColdEndpointCrossingSet beta v →
          t.val ≤ u.val := by
    intro u hu
    simpa [t] using
      theorem4Problem11FirstColdEndpointPivot_min
        (beta := beta) (v := v) hnonempty hu
  change Theorem4Problem11ClosedPivotBounds beta v t
  constructor
  · by_cases ht0 : t.val = 0
    · have hLzero : theorem4Problem11LeftSum v t = 0 := by
        unfold theorem4Problem11LeftSum
        refine Finset.sum_eq_zero ?_
        intro j _hj
        have hnlt : ¬ j.val < t.val := by omega
        simp [hnlt]
      have hn_nonneg : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
      have htwo_beta_nonneg : 0 ≤ 2 * beta := by nlinarith
      have hrhs_nonneg : 0 ≤ 2 * beta * (n : ℝ) :=
        mul_nonneg htwo_beta_nonneg hn_nonneg
      rw [hLzero, ht0]
      ring_nf
      nlinarith [hrhs_nonneg]
    · have htpos : 0 < t.val := Nat.pos_of_ne_zero ht0
      let p : Item n := ⟨t.val - 1, by omega⟩
      have hpnext : t.val = p.val + 1 := by
        dsimp [p]
        omega
      have hp_not :
          ¬ Theorem4Problem11ColdEndpointBound beta v p := by
        intro hp
        have hp_mem :
            p ∈ theorem4Problem11ColdEndpointCrossingSet beta v := by
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ p, hp⟩
        have hminp := hmin p hp_mem
        dsimp [p] at hminp
        omega
      have hp_lt :
          (1 - 2 * beta) *
              (2 * pairShare (1 / 2) v p *
                  theorem4Problem11LeftSum v p +
                ((n : ℝ) - 2 * (p.val : ℝ))) <
            ((n : ℝ) - 2 * (p.val : ℝ) - 2) *
              (4 * beta * pairShare (1 / 2) v p +
                (1 - 2 * beta)) := by
        unfold Theorem4Problem11ColdEndpointBound at hp_not
        exact not_le.mp hp_not
      have hnext_real : (t.val : ℝ) = (p.val : ℝ) + 1 := by
        exact_mod_cast hpnext
      have hpN_eq :
          (n : ℝ) - 2 * (p.val : ℝ) =
            (n : ℝ) - 2 * (t.val : ℝ) + 2 := by
        nlinarith [hnext_real]
      have hpTail_eq :
          (n : ℝ) - 2 * (p.val : ℝ) - 2 =
            (n : ℝ) - 2 * (t.val : ℝ) := by
        nlinarith [hnext_real]
      rw [hpN_eq] at hp_lt
      have hmul_lt :
          (1 - 2 * beta) *
              (pairShare (1 / 2) v p *
                  theorem4Problem11LeftSum v p + 1) <
            2 * beta * pairShare (1 / 2) v p *
              ((n : ℝ) - 2 * (t.val : ℝ)) := by
        nlinarith [hp_lt, hnext_real]
      have hq_pos : 0 < pairShare (1 / 2) v p :=
        pairShare_pos p
          (by norm_num : (0 : ℝ) < 1 / 2)
          (by norm_num : (1 / 2 : ℝ) < 1) hpos
      have hq_ne : pairShare (1 / 2) v p ≠ 0 := ne_of_gt hq_pos
      rw [theorem4Problem11LeftSum_next_eq
        (v := v) (t := p) (u := t) hpnext]
      refine le_of_mul_le_mul_left ?_ hq_pos
      calc
        pairShare (1 / 2) v p *
            ((1 - 2 * beta) *
              (theorem4Problem11LeftSum v p +
                (pairShare (1 / 2) v p)⁻¹)) =
          (1 - 2 * beta) *
            (pairShare (1 / 2) v p *
              theorem4Problem11LeftSum v p + 1) := by
            field_simp [hq_ne]
        _ ≤
          pairShare (1 / 2) v p *
            (2 * beta * ((n : ℝ) - 2 * (t.val : ℝ))) := by
            nlinarith [le_of_lt hmul_lt]
  · have hcold : Theorem4Problem11ColdEndpointBound beta v t := by
      simpa [theorem4Problem11ColdEndpointCrossingSet] using htmem
    simpa [Theorem4Problem11ColdEndpointBound] using hcold

theorem theorem4Problem11ClosedPivotBounds_exists_of_center {n : ℕ}
    {beta : ℝ} {v : Item n → ℝ} {c : Item n}
    (hbeta_pos : 0 < beta)
    (hbeta_half : beta < 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hcenter : c.val = (OpposingTypes.reverseItem c).val) :
    ∃ t : Item n,
      t.val ≤ (reverseItem t).val ∧
        Theorem4Problem11ClosedPivotBounds beta v t := by
  let hnonempty :
      (theorem4Problem11ColdEndpointCrossingSet beta v).Nonempty :=
    theorem4Problem11ColdEndpointCrossingSet_nonempty_of_center
      hbeta_pos hbeta_half hpos hcenter
  let t : Item n := theorem4Problem11FirstColdEndpointPivot beta v hnonempty
  have hcold :
      Theorem4Problem11ColdEndpointBound beta v c :=
    theorem4Problem11ColdEndpointBound_of_center
      hbeta_pos hbeta_half hpos hcenter
  have hc_mem :
      c ∈ theorem4Problem11ColdEndpointCrossingSet beta v := by
    simpa [theorem4Problem11ColdEndpointCrossingSet] using hcold
  have ht_le_c : t.val ≤ c.val := by
    simpa [t] using
      theorem4Problem11FirstColdEndpointPivot_min
        (beta := beta) (v := v) hnonempty hc_mem
  exact ⟨t,
    val_le_reverseItem_of_val_le_center_eq_reverse ht_le_c hcenter,
    by
      simpa [t] using
        theorem4Problem11FirstColdEndpointPivot_closedPivotBounds
          hbeta_pos hbeta_half hpos hnonempty⟩

theorem theorem4Problem11ClosedPivotBounds_exists_of_succ_center {n : ℕ}
    {beta : ℝ} {v : Item n → ℝ} {c : Item n}
    (hbeta_pos : 0 < beta)
    (hbeta_half : beta < 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hsucc : c.val + 1 = (reverseItem c).val) :
    ∃ t : Item n,
      t.val ≤ (reverseItem t).val ∧
        Theorem4Problem11ClosedPivotBounds beta v t := by
  let hnonempty :
      (theorem4Problem11ColdEndpointCrossingSet beta v).Nonempty :=
    theorem4Problem11ColdEndpointCrossingSet_nonempty_of_succ_center
      hbeta_pos hbeta_half hpos hsucc
  let t : Item n := theorem4Problem11FirstColdEndpointPivot beta v hnonempty
  have hcold :
      Theorem4Problem11ColdEndpointBound beta v c :=
    theorem4Problem11ColdEndpointBound_of_succ_center
      hbeta_pos hbeta_half hpos hsucc
  have hc_mem :
      c ∈ theorem4Problem11ColdEndpointCrossingSet beta v := by
    simpa [theorem4Problem11ColdEndpointCrossingSet] using hcold
  have ht_le_c : t.val ≤ c.val := by
    simpa [t] using
      theorem4Problem11FirstColdEndpointPivot_min
        (beta := beta) (v := v) hnonempty hc_mem
  exact ⟨t,
    val_le_reverseItem_of_val_le_succ_center ht_le_c hsucc,
    by
      simpa [t] using
        theorem4Problem11FirstColdEndpointPivot_closedPivotBounds
          hbeta_pos hbeta_half hpos hnonempty⟩

theorem theorem4Problem11ClosedX_pivot_nonneg_of_bounds {n : ℕ}
    {beta : ℝ} {v : Item n → ℝ} {t : Item n}
    (hbeta_pos : 0 < beta)
    (hbeta_half : beta < 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hleft : t.val ≤ (reverseItem t).val)
    (hbounds : Theorem4Problem11ClosedPivotBounds beta v t) :
    0 ≤ theorem4Problem11ClosedX beta v t t := by
  have hbeta_ne : beta ≠ 0 := ne_of_gt hbeta_pos
  have hden_pos :
      0 <
        2 * pairShare (1 / 2) v t * theorem4Problem11LeftSum v t +
          ((n : ℝ) - 2 * (t.val : ℝ)) := by
    have hDpos :
        0 < theorem4Problem11ClosedDualDenominator v t :=
      theorem4Problem11ClosedDualDenominator_pos
        (v := v) (t := t) hpos hleft
    rwa [theorem4Problem11ClosedDualDenominator_eq hleft] at hDpos
  have hden_ne :
      2 * pairShare (1 / 2) v t * theorem4Problem11LeftSum v t +
          ((n : ℝ) - 2 * (t.val : ℝ)) ≠ 0 :=
    ne_of_gt hden_pos
  rw [theorem4Problem11ClosedX_at_eq_one_sub_leftSum hbeta_pos hpos,
    theorem4Problem11ClosedDualValue_eq_fullPolicy_formula hleft]
  field_simp [hbeta_ne, hden_ne]
  nlinarith [hbounds.known_pivot]

theorem theorem4Problem11ClosedZEndpointMass_nonneg_of_bounds {n : ℕ}
    {beta : ℝ} {v : Item n → ℝ} {t : Item n}
    (hbeta_pos : 0 < beta)
    (hbeta_half : beta < 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hleft : t.val ≤ (reverseItem t).val)
    (hbounds : Theorem4Problem11ClosedPivotBounds beta v t) :
    0 ≤ theorem4Problem11ClosedZEndpointMass beta v t := by
  by_cases hcenter : t = reverseItem t
  · unfold theorem4Problem11ClosedZEndpointMass
    rw [if_pos hcenter]
    norm_num
  · have hstrict : t.val < (reverseItem t).val := by
      have hne_val : t.val ≠ (reverseItem t).val := by
        intro hval
        exact hcenter (Fin.ext hval)
      omega
    have hc_ne : 1 - 2 * beta ≠ 0 := by nlinarith
    have hden_pos :
        0 <
          2 * pairShare (1 / 2) v t * theorem4Problem11LeftSum v t +
            ((n : ℝ) - 2 * (t.val : ℝ)) := by
      have hDpos :
          0 < theorem4Problem11ClosedDualDenominator v t :=
        theorem4Problem11ClosedDualDenominator_pos
          (v := v) (t := t) hpos hleft
      rwa [theorem4Problem11ClosedDualDenominator_eq hleft] at hDpos
    have hden_ne :
        2 * pairShare (1 / 2) v t * theorem4Problem11LeftSum v t +
            ((n : ℝ) - 2 * (t.val : ℝ)) ≠ 0 :=
      ne_of_gt hden_pos
    unfold theorem4Problem11ClosedZEndpointMass
    rw [if_neg hcenter, theorem4Problem11ClosedZInteriorMass_eq hstrict,
      theorem4Problem11ClosedDualValue_eq_fullPolicy_formula hleft]
    have hc_pos : 0 < 1 - 2 * beta := by nlinarith
    apply div_nonneg
    · rw [sub_nonneg]
      calc
        ((n : ℝ) - 2 * (t.val : ℝ) - 2) *
            ((4 * beta * pairShare (1 / 2) v t + (1 - 2 * beta)) /
              (2 * pairShare (1 / 2) v t *
                  theorem4Problem11LeftSum v t +
                ((n : ℝ) - 2 * (t.val : ℝ))) /
              (1 - 2 * beta))
            =
          (((n : ℝ) - 2 * (t.val : ℝ) - 2) *
              ((4 * beta * pairShare (1 / 2) v t + (1 - 2 * beta)) /
                (2 * pairShare (1 / 2) v t *
                    theorem4Problem11LeftSum v t +
                  ((n : ℝ) - 2 * (t.val : ℝ))))) /
            (1 - 2 * beta) := by
            ring
        _ ≤ 1 := by
            rw [div_le_iff₀ hc_pos]
            calc
              ((n : ℝ) - 2 * (t.val : ℝ) - 2) *
                  ((4 * beta * pairShare (1 / 2) v t +
                      (1 - 2 * beta)) /
                    (2 * pairShare (1 / 2) v t *
                        theorem4Problem11LeftSum v t +
                      ((n : ℝ) - 2 * (t.val : ℝ))))
                  =
                (((n : ℝ) - 2 * (t.val : ℝ) - 2) *
                    (4 * beta * pairShare (1 / 2) v t +
                      (1 - 2 * beta))) /
                  (2 * pairShare (1 / 2) v t *
                      theorem4Problem11LeftSum v t +
                    ((n : ℝ) - 2 * (t.val : ℝ))) := by
                  ring
              _ ≤ 1 * (1 - 2 * beta) := by
                  rw [div_le_iff₀ hden_pos]
                  nlinarith [hbounds.cold_endpoint]
    · norm_num

theorem theorem4Problem11Closed_nonnegativePivots_of_bounds {n : ℕ}
    {beta : ℝ} {v : Item n → ℝ} {t : Item n}
    (hbeta_pos : 0 < beta)
    (hbeta_half : beta < 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hleft : t.val ≤ (reverseItem t).val)
    (hbounds : Theorem4Problem11ClosedPivotBounds beta v t) :
    0 ≤ theorem4Problem11ClosedX beta v t t ∧
      0 ≤ theorem4Problem11ClosedZEndpointMass beta v t :=
  ⟨theorem4Problem11ClosedX_pivot_nonneg_of_bounds
      hbeta_pos hbeta_half hpos hleft hbounds,
    theorem4Problem11ClosedZEndpointMass_nonneg_of_bounds
      hbeta_pos hbeta_half hpos hleft hbounds⟩

/--
At least one left-half closed-form policy attains the Problem 11 optimum.
The construction uses the center (or the left item of the central pair) and
the closed primal-dual witness, without selecting a basic feasible solution.
-/
theorem theorem4Problem11ClosedPolicyOptimal_exists {n : ℕ}
    [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hbeta_pos : 0 < beta)
    (hbeta_half : beta < 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v) :
    ∃ (t : Item n) (ρ : TypePolicy 3 n),
      t.val ≤ (reverseItem t).val ∧
        Theorem4Problem11PolicyOptimal beta v ρ
          (theorem4Problem11ClosedDualValue beta v t) := by
  rcases midpoint_center_or_succ_center (n := n) with
    ⟨c, hcenter⟩ | ⟨c, hsucc⟩
  · rcases theorem4Problem11ClosedPivotBounds_exists_of_center
      hbeta_pos hbeta_half hpos hcenter with ⟨t, hleft, hbounds⟩
    rcases theorem4Problem11Closed_nonnegativePivots_of_bounds
      hbeta_pos hbeta_half hpos hleft hbounds with ⟨hpivot, hendpoint⟩
    exact ⟨t,
      theorem4Problem11ClosedPolicy beta v t
        hbeta_pos hbeta_half hpos hleft hpivot hendpoint,
      hleft,
      theorem4Problem11ClosedPolicyOptimal_of_witness
        hbeta_pos hbeta_half hpos hdec hleft hpivot hendpoint⟩
  · rcases theorem4Problem11ClosedPivotBounds_exists_of_succ_center
      hbeta_pos hbeta_half hpos hsucc with ⟨t, hleft, hbounds⟩
    rcases theorem4Problem11Closed_nonnegativePivots_of_bounds
      hbeta_pos hbeta_half hpos hleft hbounds with ⟨hpivot, hendpoint⟩
    exact ⟨t,
      theorem4Problem11ClosedPolicy beta v t
        hbeta_pos hbeta_half hpos hleft hpivot hendpoint,
      hleft,
      theorem4Problem11ClosedPolicyOptimal_of_witness
        hbeta_pos hbeta_half hpos hdec hleft hpivot hendpoint⟩

/--
An optimizer of the literal equality form of Problem 11 is also optimal for
its epigraph form.  The proof is source-faithful: a closed primal-dual policy
is an equality-form comparison witness, and its dual certificate bounds every
epigraph-feasible comparison policy.
-/
theorem theorem4Problem11PolicyOptimal_of_equalityLPOptimal {n : ℕ}
    [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    {ρ : TypePolicy 3 n} {ell : ℝ}
    (hbeta_pos : 0 < beta)
    (hbeta_half : beta < 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (h : Theorem4Problem11EqualityLPOptimal beta v ρ ell) :
    Theorem4Problem11PolicyOptimal beta v ρ ell := by
  rcases theorem4Problem11ClosedPolicyOptimal_exists
      hbeta_pos hbeta_half hpos hdec with
    ⟨t, ρclosed, hleft, hclosed⟩
  have hclosed_eq :
      ∀ j : Item n,
        theorem4Problem11PolicyItemValue beta v ρclosed j =
          theorem4Problem11ClosedDualValue beta v t := by
    exact theorem4Problem11PolicyOptimal_item_eq_of_closedDual_tight
      hbeta_pos hbeta_half hpos hdec hleft rfl hclosed
  have hclosed_le : theorem4Problem11ClosedDualValue beta v t ≤ ell :=
    h.2.2 ρclosed (theorem4Problem11ClosedDualValue beta v t)
      hclosed.1 hclosed_eq
  refine ⟨h.1, ?_, ?_⟩
  · intro j
    exact le_of_eq (h.2.1 j).symm
  · intro ρ' ell' hsym' hfeas'
    exact (hclosed.2.2 ρ' ell' hsym' hfeas').trans hclosed_le

/--
Every equalized global Problem 11 optimum has the Lemma 13 pivot-support
shape at its last active known-type item.  That item is also the minimum
known-type cutoff with the same right-zero property.
-/
theorem theorem4Problem11PolicyOptimal_lastActive_pivotSupport {n : ℕ}
    [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    {ρ : TypePolicy 3 n} {ell : ℝ}
    (hn : 2 < n)
    (hbeta_pos : 0 < beta)
    (hbeta_half : beta < 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hitem_eq : ∀ j : Item n,
      theorem4Problem11PolicyItemValue beta v ρ j = ell)
    (hopt : Theorem4Problem11PolicyOptimal beta v ρ ell) :
    let t := theorem4Problem11LastActiveTypeZero ρ
    t.val ≤ (reverseItem t).val ∧
      Theorem4Problem11PivotSupport ρ t ∧
      ∀ s : Item n,
        (∀ j : Item n, s.val < j.val → ρ 0 j = 0) → t.val ≤ s.val := by
  rcases theorem4Problem11ClosedPolicyOptimal_exists
      hbeta_pos hbeta_half hpos hdec with
    ⟨t0, ρclosed, hleft0, hclosed_opt⟩
  have hvalue : ell = theorem4Problem11ClosedDualValue beta v t0 :=
    theorem4Problem11PolicyOptimal_value_unique hopt hclosed_opt
  have hpivot0 : Theorem4Problem11PivotSupport ρ t0 :=
    theorem4Problem11PolicyOptimal_pivotSupport_of_closedDual_tight
      hbeta_pos hbeta_half hpos hdec hleft0 hvalue hopt
  have hno : Theorem4Problem11PolicyNoStrictPointwiseImprovement beta v ρ :=
    theorem4Problem11_noStrictPointwiseImprovement_of_policyOptimal_equalized
      hitem_eq hopt
  have hright_zero :
      ∀ j : Item n, (reverseItem j).val < j.val → ρ 0 j = 0 :=
    theorem4Problem11_typeZero_zero_after_mirror_of_noStrictPointwiseImprovement
      hn hbeta_pos hpos hdec hopt.1 hno
  let t : Item n := theorem4Problem11LastActiveTypeZero ρ
  have hleft : t.val ≤ (reverseItem t).val := by
    by_contra hnot
    have hrev_lt : (reverseItem t).val < t.val := by omega
    exact theorem4Problem11LastActiveTypeZero_active ρ
      (hright_zero t hrev_lt)
  have ht_le_t0 : t.val ≤ t0.val := by
    by_contra hnot
    have ht0_lt : t0.val < t.val := by omega
    exact theorem4Problem11LastActiveTypeZero_active ρ
      (hpivot0.1 t ht0_lt)
  have hpivot : Theorem4Problem11PivotSupport ρ t := by
    constructor
    · intro j hj
      exact theorem4Problem11_typeZero_zero_after_lastActive ρ hj
    · intro j hj
      exact hpivot0.2 j (lt_of_lt_of_le hj ht_le_t0)
  have hminimum :
      ∀ s : Item n,
        (∀ j : Item n, s.val < j.val → ρ 0 j = 0) → t.val ≤ s.val := by
    intro s hs
    by_contra hnot
    have hs_lt : s.val < t.val := by omega
    exact theorem4Problem11LastActiveTypeZero_active ρ (hs t hs_lt)
  exact ⟨hleft, hpivot, hminimum⟩

theorem theorem4Problem11EqualityFormOptimalBFS_of_closed_witness {n : ℕ}
    {beta : ℝ} {v : Item n → ℝ} {t : Item n}
    (hbeta_pos : 0 < beta)
    (hbeta_half : beta < 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hleft : t.val ≤ (reverseItem t).val)
    (hpivot : 0 ≤ theorem4Problem11ClosedX beta v t t)
    (hendpoint : 0 ≤ theorem4Problem11ClosedZEndpointMass beta v t)
    (hbasic :
      TypePolicy.BasicFeasibleSupportCertificate
        (theorem4Problem11PolicyOfRealVectors
          (theorem4Problem11ClosedX beta v t)
          (theorem4Problem11ClosedZ beta v t)
          (theorem4Problem11ClosedX_nonneg
            hbeta_pos hbeta_half hpos hleft hpivot)
          (theorem4Problem11ClosedZ_nonneg
            hbeta_pos hbeta_half hpos hleft hendpoint)
          (theorem4Problem11ClosedX_sum_eq_one beta v t)
          (theorem4Problem11ClosedZ_sum_eq_one hleft))) :
    Theorem4Problem11EqualityFormOptimalBFS beta v
      (theorem4Problem11ClosedX beta v t)
      (theorem4Problem11ClosedZ beta v t)
      (theorem4Problem11ClosedDualValue beta v t) := by
  let hfeas :=
    theorem4Problem11Closed_realLPFeasible
      hbeta_pos hbeta_half hpos hleft hpivot hendpoint
  exact theorem4Problem11EqualityFormOptimalBFS_of_closedDual_tight
    hbeta_pos.le (by nlinarith) hpos hdec hleft hfeas
    (theorem4Problem11Closed_item_eq
      hbeta_pos hbeta_half hpos hleft)
    hbasic

theorem theorem4Problem11EqualityFormOptimalBFS_of_closed_bounds {n : ℕ}
    {beta : ℝ} {v : Item n → ℝ} {t : Item n}
    (hbeta_pos : 0 < beta)
    (hbeta_half : beta < 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hleft : t.val ≤ (reverseItem t).val)
    (hbounds : Theorem4Problem11ClosedPivotBounds beta v t) :
    Theorem4Problem11EqualityFormOptimalBFS beta v
      (theorem4Problem11ClosedX beta v t)
      (theorem4Problem11ClosedZ beta v t)
      (theorem4Problem11ClosedDualValue beta v t) := by
  have hnonneg :=
    theorem4Problem11Closed_nonnegativePivots_of_bounds
      hbeta_pos hbeta_half hpos hleft hbounds
  let hpivot : 0 ≤ theorem4Problem11ClosedX beta v t t := hnonneg.1
  let hendpoint : 0 ≤ theorem4Problem11ClosedZEndpointMass beta v t :=
    hnonneg.2
  have hbasic :
      TypePolicy.BasicFeasibleSupportCertificate
        (theorem4Problem11PolicyOfRealVectors
          (theorem4Problem11ClosedX beta v t)
          (theorem4Problem11ClosedZ beta v t)
          (theorem4Problem11ClosedX_nonneg
            hbeta_pos hbeta_half hpos hleft hpivot)
          (theorem4Problem11ClosedZ_nonneg
            hbeta_pos hbeta_half hpos hleft hendpoint)
          (theorem4Problem11ClosedX_sum_eq_one beta v t)
          (theorem4Problem11ClosedZ_sum_eq_one hleft)) := by
    simpa [theorem4Problem11ClosedPolicy, hpivot, hendpoint] using
      theorem4Problem11ClosedPolicy_basicFeasibleSupportCertificate
        hbeta_pos hbeta_half hpos hleft hpivot hendpoint
  exact theorem4Problem11EqualityFormOptimalBFS_of_closed_witness
    hbeta_pos hbeta_half hpos hdec hleft hpivot hendpoint hbasic

theorem theorem4Problem11EqualityFormOptimalBFS_exists_closed_of_center
    {n : ℕ} {beta : ℝ} {v : Item n → ℝ} {c : Item n}
    (hbeta_pos : 0 < beta)
    (hbeta_half : beta < 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter : c.val = (OpposingTypes.reverseItem c).val) :
    ∃ t : Item n,
      Theorem4Problem11EqualityFormOptimalBFS beta v
        (theorem4Problem11ClosedX beta v t)
        (theorem4Problem11ClosedZ beta v t)
        (theorem4Problem11ClosedDualValue beta v t) := by
  rcases theorem4Problem11ClosedPivotBounds_exists_of_center
      hbeta_pos hbeta_half hpos hcenter with
    ⟨t, hleft, hbounds⟩
  exact ⟨t,
    theorem4Problem11EqualityFormOptimalBFS_of_closed_bounds
      hbeta_pos hbeta_half hpos hdec hleft hbounds⟩

theorem theorem4Problem11EqualityFormOptimalBFS_exists_closed_of_succ_center
    {n : ℕ} {beta : ℝ} {v : Item n → ℝ} {c : Item n}
    (hbeta_pos : 0 < beta)
    (hbeta_half : beta < 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hsucc : c.val + 1 = (OpposingTypes.reverseItem c).val) :
    ∃ t : Item n,
      Theorem4Problem11EqualityFormOptimalBFS beta v
        (theorem4Problem11ClosedX beta v t)
        (theorem4Problem11ClosedZ beta v t)
        (theorem4Problem11ClosedDualValue beta v t) := by
  rcases theorem4Problem11ClosedPivotBounds_exists_of_succ_center
      hbeta_pos hbeta_half hpos hsucc with
    ⟨t, hleft, hbounds⟩
  exact ⟨t,
    theorem4Problem11EqualityFormOptimalBFS_of_closed_bounds
      hbeta_pos hbeta_half hpos hdec hleft hbounds⟩

/-- Lemma 15: before the pivot, `x_j = λ / (2β q_j)`. -/
theorem theorem4Problem11Lemma15_typeZero_before_eq
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    {ρ : TypePolicy 3 n} {ell : ℝ} {t j : Item n}
    (hbeta_pos : 0 < beta)
    (hpos : ∀ l : Item n, 0 < v l)
    (h : Theorem4Problem11EqualizedBasicOptimal beta v ρ ell)
    (hpivot : Theorem4Problem11PivotSupport ρ t)
    (hleft : t.val ≤ (reverseItem t).val)
    (hj : j.val < t.val) :
    (ρ 0 j).toReal = ell / (2 * beta * pairShare (1 / 2) v j) := by
  have hknown :=
    theorem4Problem11PolicyItemValue_eq_known_of_lt_pivot
      (beta := beta) (v := v) (ρ := ρ) hpivot hleft hj
  have hmul :
      2 * beta * pairShare (1 / 2) v j * (ρ 0 j).toReal = ell := by
    rw [← hknown]
    exact h.item_eq j
  have hcoef_ne : 2 * beta * pairShare (1 / 2) v j ≠ 0 := by
    have hq_pos : 0 < pairShare (1 / 2) v j :=
      pairShare_pos j (by norm_num) (by norm_num) hpos
    exact ne_of_gt (by positivity : 0 < 2 * beta * pairShare (1 / 2) v j)
  rw [eq_div_iff hcoef_ne]
  nlinarith [hmul]

/-- Lemma 15: after the pivot, the known-type coordinate is zero. -/
theorem theorem4Problem11Lemma15_typeZero_after_eq_zero
    {n : ℕ} {ρ : TypePolicy 3 n} {t j : Item n}
    (hpivot : Theorem4Problem11PivotSupport ρ t)
    (hj : t.val < j.val) :
    (ρ 0 j).toReal = 0 := by
  simp [hpivot.1 j hj]

/--
Lemma 15: the pivot known-type coordinate is
`1 - (λ / (2β)) L_t`.
-/
theorem theorem4Problem11Lemma15_typeZero_pivot_eq_one_sub_leftSum
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    {ρ : TypePolicy 3 n} {ell : ℝ} {t : Item n}
    (hbeta_pos : 0 < beta)
    (hpos : ∀ l : Item n, 0 < v l)
    (h : Theorem4Problem11EqualizedBasicOptimal beta v ρ ell)
    (hpivot : Theorem4Problem11PivotSupport ρ t)
    (hleft : t.val ≤ (reverseItem t).val) :
    (ρ 0 t).toReal =
      1 - (ell / (2 * beta)) * theorem4Problem11LeftSum v t := by
  have hx_t :=
    theorem4Problem11PivotSupport_typeZero_pivot_toReal_eq_one_sub_leftSum
      hpivot
  have hsum :
      (∑ j : Item n, if j.val < t.val then (ρ 0 j).toReal else 0) =
        (ell / (2 * beta)) * theorem4Problem11LeftSum v t := by
    unfold theorem4Problem11LeftSum
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j _hj
    by_cases hjt : j.val < t.val
    · have hq_ne : pairShare (1 / 2) v j ≠ 0 :=
        ne_of_gt (pairShare_pos j (by norm_num) (by norm_num) hpos)
      have hbeta_ne : beta ≠ 0 := ne_of_gt hbeta_pos
      rw [if_pos hjt, if_pos hjt,
        theorem4Problem11Lemma15_typeZero_before_eq
          hbeta_pos hpos h hpivot hleft hjt]
      field_simp [hbeta_ne, hq_ne]
    · simp [hjt]
  rw [hx_t, hsum]

/-- Lemma 15: before the pivot, `z_j = 0`. -/
theorem theorem4Problem11Lemma15_cold_before_eq_zero
    {n : ℕ} {ρ : TypePolicy 3 n} {t j : Item n}
    (hpivot : Theorem4Problem11PivotSupport ρ t)
    (hj : j.val < t.val) :
    (ρ 2 j).toReal = 0 := by
  simp [(hpivot.2 j hj).1]

/-- Lemma 15: before the pivot, the mirrored cold-start coordinate is zero. -/
theorem theorem4Problem11Lemma15_cold_reverse_before_eq_zero
    {n : ℕ} {ρ : TypePolicy 3 n} {t j : Item n}
    (hpivot : Theorem4Problem11PivotSupport ρ t)
    (hj : j.val < t.val) :
    (ρ 2 (reverseItem j)).toReal = 0 := by
  simp [(hpivot.2 j hj).2]

/--
Lemma 15: strictly between the pivot and its mirror, the cold-start coordinate
is `λ / (1 - 2β)`.
-/
theorem theorem4Problem11Lemma15_cold_between_pivot_and_mirror_eq
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    {ρ : TypePolicy 3 n} {ell : ℝ} {t j : Item n}
    (hbeta_half : beta < 1 / 2)
    (h : Theorem4Problem11EqualizedBasicOptimal beta v ρ ell)
    (hpivot : Theorem4Problem11PivotSupport ρ t)
    (hjt : t.val < j.val)
    (hjrev_t : j.val < (reverseItem t).val) :
    (ρ 2 j).toReal = ell / (1 - 2 * beta) := by
  have ht_rev_j : t.val < (reverseItem j).val := by
    have h :=
      reverseItem_val_lt_of_val_lt hjrev_t
    simpa [reverseItem_reverseItem] using h
  have hcold :=
    theorem4Problem11PolicyItemValue_eq_cold_of_pivot_lt_and_pivot_lt_reverse
      (beta := beta) (v := v) (ρ := ρ) hpivot hjt ht_rev_j
  have hmul : (1 - 2 * beta) * (ρ 2 j).toReal = ell := by
    rw [← hcold]
    exact h.item_eq j
  have hc_ne : 1 - 2 * beta ≠ 0 := by nlinarith
  calc
    (ρ 2 j).toReal =
        ((1 - 2 * beta) * (ρ 2 j).toReal) / (1 - 2 * beta) := by
          field_simp [hc_ne]
    _ = ell / (1 - 2 * beta) := by
          rw [hmul]

/--
Summing the Problem 11 item values collapses the mirrored known-type row into
the same `q_j x_j` sum.
-/
theorem theorem4Problem11_sum_policyItemValue_eq
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hpos : ∀ j : Item n, 0 < v j)
    (ρ : TypePolicy 3 n) :
    (∑ j : Item n, theorem4Problem11PolicyItemValue beta v ρ j) =
      4 * beta *
          (∑ j : Item n,
            pairShare (1 / 2) v j * (ρ 0 j).toReal) +
        (1 - 2 * beta) := by
  have hsum_z : (∑ j : Item n, (ρ 2 j).toReal) = 1 :=
    AppliedModelingLib.pmfToRealSum (ρ 2)
  have hsum_rev :
      (∑ j : Item n,
          (1 - pairShare (1 / 2) v j) *
            (ρ 0 (reverseItem j)).toReal) =
        ∑ j : Item n,
          pairShare (1 / 2) v j * (ρ 0 j).toReal := by
    have hreindex :
        (∑ j : Item n,
            (1 - pairShare (1 / 2) v j) *
              (ρ 0 (reverseItem j)).toReal) =
          ∑ j : Item n,
            (1 - pairShare (1 / 2) v (reverseItem j)) *
              (ρ 0 j).toReal := by
      simpa [reverseItem_reverseItem] using
        (sum_reverseItem
          (fun j : Item n =>
            (1 - pairShare (1 / 2) v (reverseItem j)) *
              (ρ 0 j).toReal))
    rw [hreindex]
    refine Finset.sum_congr rfl ?_
    intro j _hj
    have hq :
        1 - pairShare (1 / 2) v (reverseItem j) =
          pairShare (1 / 2) v j :=
      (pairShare_half_eq_one_sub_reverse j hpos).symm
    rw [hq]
  unfold theorem4Problem11PolicyItemValue theorem4Problem11ItemValue
  have hknown :
      (∑ j : Item n,
        2 * beta *
            (pairShare (1 / 2) v j * (ρ 0 j).toReal +
              (1 - pairShare (1 / 2) v j) *
                (ρ 0 (reverseItem j)).toReal)) =
        2 * beta *
          ((∑ j : Item n,
              pairShare (1 / 2) v j * (ρ 0 j).toReal) +
            (∑ j : Item n,
              (1 - pairShare (1 / 2) v j) *
                (ρ 0 (reverseItem j)).toReal)) := by
    rw [← Finset.mul_sum, Finset.sum_add_distrib]
  have hcold :
      (∑ j : Item n, (1 - 2 * beta) * (ρ 2 j).toReal) =
        (1 - 2 * beta) * (∑ j : Item n, (ρ 2 j).toReal) := by
    rw [← Finset.mul_sum]
  rw [Finset.sum_add_distrib, hknown, hcold, hsum_rev, hsum_z]
  ring

/--
Lemma 15 sum identity: under pivot support, the weighted known-type mass is
`t * λ/(2β) + q_t (1 - (λ/(2β))L_t)`.
-/
theorem theorem4Problem11Lemma15_sum_typeZero_q_of_pivot
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    {ρ : TypePolicy 3 n} {ell : ℝ} {t : Item n}
    (hbeta_pos : 0 < beta)
    (hpos : ∀ l : Item n, 0 < v l)
    (h : Theorem4Problem11EqualizedBasicOptimal beta v ρ ell)
    (hpivot : Theorem4Problem11PivotSupport ρ t)
    (hleft : t.val ≤ (reverseItem t).val) :
    (∑ j : Item n, pairShare (1 / 2) v j * (ρ 0 j).toReal) =
      (t.val : ℝ) * (ell / (2 * beta)) +
        pairShare (1 / 2) v t *
          (1 - (ell / (2 * beta)) * theorem4Problem11LeftSum v t) := by
  have hsplit :=
    theorem4_sum_eq_left_part_add_pivot_of_after_zero
      (fun j : Item n =>
        pairShare (1 / 2) v j * (ρ 0 j).toReal) t
      (fun {j} hj => by
        change pairShare (1 / 2) v j * (ρ 0 j).toReal = 0
        rw [theorem4Problem11Lemma15_typeZero_after_eq_zero hpivot hj]
        ring)
  have hleft_sum :
      (∑ j : Item n,
        if j.val < t.val then
          pairShare (1 / 2) v j * (ρ 0 j).toReal else 0) =
        (t.val : ℝ) * (ell / (2 * beta)) := by
    calc
      (∑ j : Item n,
        if j.val < t.val then
          pairShare (1 / 2) v j * (ρ 0 j).toReal else 0)
          = ∑ j : Item n,
              if j.val < t.val then ell / (2 * beta) else 0 := by
              refine Finset.sum_congr rfl ?_
              intro j _hj
              by_cases hjt : j.val < t.val
              · have hq_ne : pairShare (1 / 2) v j ≠ 0 :=
                  ne_of_gt (pairShare_pos j (by norm_num) (by norm_num) hpos)
                have hbeta_ne : beta ≠ 0 := ne_of_gt hbeta_pos
                rw [if_pos hjt, if_pos hjt,
                  theorem4Problem11Lemma15_typeZero_before_eq
                    hbeta_pos hpos h hpivot hleft hjt]
                field_simp [hbeta_ne, hq_ne]
              · simp [hjt]
      _ = (t.val : ℝ) * (ell / (2 * beta)) := by
              exact problem6_sum_left_const_eq t (ell / (2 * beta))
  have hpivot_x :=
    theorem4Problem11Lemma15_typeZero_pivot_eq_one_sub_leftSum
      hbeta_pos hpos h hpivot hleft
  rw [hsplit, hleft_sum]
  change
    (t.val : ℝ) * (ell / (2 * beta)) +
        pairShare (1 / 2) v t * (ρ 0 t).toReal =
      (t.val : ℝ) * (ell / (2 * beta)) +
        pairShare (1 / 2) v t *
          (1 - ell / (2 * beta) * theorem4Problem11LeftSum v t)
  rw [hpivot_x]

/--
Lemma 15 closed-value algebra: summing all equality-form item constraints gives
the paper's denominator equation for `λ`.
-/
theorem theorem4Problem11Lemma15_lambda_mul_denominator_eq
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    {ρ : TypePolicy 3 n} {ell : ℝ} {t : Item n}
    (hbeta_pos : 0 < beta)
    (hpos : ∀ l : Item n, 0 < v l)
    (h : Theorem4Problem11EqualizedBasicOptimal beta v ρ ell)
    (hpivot : Theorem4Problem11PivotSupport ρ t)
    (hleft : t.val ≤ (reverseItem t).val) :
    ell *
        ((n : ℝ) - 2 * (t.val : ℝ) +
          2 * pairShare (1 / 2) v t * theorem4Problem11LeftSum v t) =
      4 * beta * pairShare (1 / 2) v t + (1 - 2 * beta) := by
  let q : ℝ := pairShare (1 / 2) v t
  let L : ℝ := theorem4Problem11LeftSum v t
  have hsum_values :=
    theorem4Problem11_sum_policyItemValue_eq
      (beta := beta) (v := v) hpos ρ
  have hsum_eq :
      (∑ j : Item n, theorem4Problem11PolicyItemValue beta v ρ j) =
        (n : ℝ) * ell := by
    calc
      (∑ j : Item n, theorem4Problem11PolicyItemValue beta v ρ j)
          = ∑ _j : Item n, ell := by
            apply Finset.sum_congr rfl
            intro j _hj
            exact h.item_eq j
      _ = (n : ℝ) * ell := by
            simp [Item]
  have hsum_q :=
    theorem4Problem11Lemma15_sum_typeZero_q_of_pivot
      hbeta_pos hpos h hpivot hleft
  have heq :
      (n : ℝ) * ell =
        4 * beta *
            ((t.val : ℝ) * (ell / (2 * beta)) +
              pairShare (1 / 2) v t *
                (1 - (ell / (2 * beta)) * theorem4Problem11LeftSum v t)) +
          (1 - 2 * beta) := by
    rw [← hsum_eq, hsum_values, hsum_q]
  have hbeta_ne : beta ≠ 0 := ne_of_gt hbeta_pos
  field_simp [hbeta_ne] at heq ⊢
  ring_nf at heq ⊢
  nlinarith

/--
Lemma 15 closed `λ` formula in the non-center case, using Lean's zero-based
item index: the paper's `n - 2t` is
`n - 2 * (t.val + 1)`.
-/
theorem theorem4Problem11Lemma15_lambda_eq_of_pivot_lt_mirror
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    {ρ : TypePolicy 3 n} {ell : ℝ} {t : Item n}
    (hbeta_pos : 0 < beta)
    (hpos : ∀ l : Item n, 0 < v l)
    (h : Theorem4Problem11EqualizedBasicOptimal beta v ρ ell)
    (hpivot : Theorem4Problem11PivotSupport ρ t)
    (ht_left : t.val < (reverseItem t).val) :
    ell =
      (2 * beta * pairShare (1 / 2) v t + (1 / 2) * (1 - 2 * beta)) /
        (1 + pairShare (1 / 2) v t * theorem4Problem11LeftSum v t +
          (1 / 2) * ((n : ℝ) - 2 * ((t.val : ℝ) + 1))) := by
  let q : ℝ := pairShare (1 / 2) v t
  let L : ℝ := theorem4Problem11LeftSum v t
  let D : ℝ :=
    1 + q * L + (1 / 2) * ((n : ℝ) - 2 * ((t.val : ℝ) + 1))
  let N : ℝ := 2 * beta * q + (1 / 2) * (1 - 2 * beta)
  have hmul :=
    theorem4Problem11Lemma15_lambda_mul_denominator_eq
      hbeta_pos hpos h hpivot (le_of_lt ht_left)
  have hA :
      (n : ℝ) - 2 * (t.val : ℝ) +
          2 * pairShare (1 / 2) v t * theorem4Problem11LeftSum v t =
        2 * D := by
    dsimp [D, q, L]
    ring
  have hB :
      4 * beta * pairShare (1 / 2) v t + (1 - 2 * beta) =
        2 * N := by
    dsimp [N, q]
    ring
  have hD_pos : 0 < D := by
    have hq_nonneg : 0 ≤ q := by
      dsimp [q]
      exact (pairShare_pos t (by norm_num) (by norm_num) hpos).le
    have hL_nonneg : 0 ≤ L := by
      dsimp [L]
      exact theorem4Problem11LeftSum_nonneg hpos t
    have htail_nat : 2 * (t.val + 1) ≤ n := by
      simp [reverseItem] at ht_left
      omega
    have htail_real :
        0 ≤ (n : ℝ) - 2 * ((t.val : ℝ) + 1) := by
      have hcast : (2 * (t.val + 1) : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast htail_nat
      nlinarith
    dsimp [D]
    nlinarith [mul_nonneg hq_nonneg hL_nonneg]
  change ell = N / D
  rw [eq_div_iff (ne_of_gt hD_pos)]
  have hmulD : ell * (2 * D) = 2 * N := by
    rw [← hA, ← hB]
    exact hmul
  nlinarith

/--
Lemma 15 non-center pivot coordinate: at the pivot, the cold-start mass is the
paper's closed `z_t` formula. Lean's zero-based index turns the paper's
`n - 2t` tail term into `n - 2 * (t.val + 1)`.
-/
theorem theorem4Problem11Lemma15_cold_pivot_eq_of_pivot_lt_mirror
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    {ρ : TypePolicy 3 n} {ell : ℝ} {t : Item n}
    (hbeta_pos : 0 < beta)
    (hbeta_half : beta < 1 / 2)
    (hpos : ∀ l : Item n, 0 < v l)
    (h : Theorem4Problem11EqualizedBasicOptimal beta v ρ ell)
    (hpivot : Theorem4Problem11PivotSupport ρ t)
    (ht_left : t.val < (reverseItem t).val) :
    (ρ 2 t).toReal =
      (1 / 2) *
        (1 -
          (((n : ℝ) - 2 * ((t.val : ℝ) + 1)) * ell /
            (1 - 2 * beta))) := by
  have hx :=
    theorem4Problem11Lemma15_typeZero_pivot_eq_one_sub_leftSum
      hbeta_pos hpos h hpivot (le_of_lt ht_left)
  have hitem_pivot :=
    theorem4Problem11PivotSupport_policyItemValue_eq_at_left_pivot
      (beta := beta) (v := v) (ρ := ρ) hpivot ht_left
  have hitem_linear :
      2 * beta * pairShare (1 / 2) v t * (ρ 0 t).toReal +
          (1 - 2 * beta) * (ρ 2 t).toReal = ell := by
    rw [← hitem_pivot]
    exact h.item_eq t
  have hbeta_ne : beta ≠ 0 := ne_of_gt hbeta_pos
  have hzt_linear :
      (1 - 2 * beta) * (ρ 2 t).toReal =
        ell - 2 * beta * pairShare (1 / 2) v t +
          pairShare (1 / 2) v t * ell * theorem4Problem11LeftSum v t := by
    rw [hx] at hitem_linear
    field_simp [hbeta_ne] at hitem_linear
    ring_nf at hitem_linear ⊢
    nlinarith
  have hden :=
    theorem4Problem11Lemma15_lambda_mul_denominator_eq
      hbeta_pos hpos h hpivot (le_of_lt ht_left)
  have htarget_mul :
      2 * (1 - 2 * beta) * (ρ 2 t).toReal =
        (1 - 2 * beta) -
          ((n : ℝ) - 2 * ((t.val : ℝ) + 1)) * ell := by
    ring_nf at hden hzt_linear ⊢
    nlinarith
  have hc_pos : 0 < 1 - 2 * beta := by nlinarith
  have hdenom_ne : 2 * (1 - 2 * beta) ≠ 0 := by positivity
  calc
    (ρ 2 t).toReal =
        (2 * (1 - 2 * beta) * (ρ 2 t).toReal) /
          (2 * (1 - 2 * beta)) := by
          field_simp [hdenom_ne]
    _ =
        ((1 - 2 * beta) -
          ((n : ℝ) - 2 * ((t.val : ℝ) + 1)) * ell) /
          (2 * (1 - 2 * beta)) := by
          rw [htarget_mul]
    _ =
        (1 / 2) *
          (1 -
            (((n : ℝ) - 2 * ((t.val : ℝ) + 1)) * ell /
              (1 - 2 * beta))) := by
          field_simp [ne_of_gt hc_pos]

/--
Lemma 15 non-center mirror-pivot coordinate: mirror symmetry gives the same
closed `z_t` formula at `\bar t`.
-/
theorem theorem4Problem11Lemma15_cold_mirror_pivot_eq_of_pivot_lt_mirror
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    {ρ : TypePolicy 3 n} {ell : ℝ} {t : Item n}
    (hbeta_pos : 0 < beta)
    (hbeta_half : beta < 1 / 2)
    (hpos : ∀ l : Item n, 0 < v l)
    (h : Theorem4Problem11EqualizedBasicOptimal beta v ρ ell)
    (hpivot : Theorem4Problem11PivotSupport ρ t)
    (ht_left : t.val < (reverseItem t).val) :
    (ρ 2 (reverseItem t)).toReal =
      (1 / 2) *
        (1 -
          (((n : ℝ) - 2 * ((t.val : ℝ) + 1)) * ell /
            (1 - 2 * beta))) := by
  calc
    (ρ 2 (reverseItem t)).toReal = (ρ 2 t).toReal := by
      exact congrArg ENNReal.toReal (h.mirror.2 t)
    _ =
        (1 / 2) *
          (1 -
            (((n : ℝ) - 2 * ((t.val : ℝ) + 1)) * ell /
              (1 - 2 * beta))) := by
          exact theorem4Problem11Lemma15_cold_pivot_eq_of_pivot_lt_mirror
            hbeta_pos hbeta_half hpos h hpivot ht_left

/--
Lemma 15 center case, cold-start coordinate: if the pivot is its own mirror,
then all non-pivot cold-start coordinates are zero by pivot support, so
`z_t = 1`.
-/
theorem theorem4Problem11Lemma15_cold_center_eq_one
    {n : ℕ} [NeZero n] {ρ : TypePolicy 3 n} {t : Item n}
    (hpivot : Theorem4Problem11PivotSupport ρ t)
    (ht_center : (reverseItem t).val = t.val) :
    (ρ 2 t).toReal = 1 := by
  have hzero : ∀ j : Item n, j ≠ t → (ρ 2 j).toReal = 0 := by
    intro j hj_ne
    have hval_ne : j.val ≠ t.val := by
      intro hval
      exact hj_ne (Fin.ext hval)
    rcases lt_or_gt_of_ne hval_ne with hjt | htj
    · have hz : ρ 2 j = 0 := (hpivot.2 j hjt).1
      simp [hz]
    · have hrev_lt : (reverseItem j).val < t.val := by
        have hrev : (reverseItem j).val < (reverseItem t).val :=
          reverseItem_val_lt_of_val_lt htj
        simpa [ht_center] using hrev
      have hz_rev : ρ 2 (reverseItem (reverseItem j)) = 0 :=
        (hpivot.2 (reverseItem j) hrev_lt).2
      have hz : ρ 2 j = 0 := by
        simpa [reverseItem_reverseItem] using hz_rev
      simp [hz]
  have hsum_single :
      (∑ j : Item n, (ρ 2 j).toReal) = (ρ 2 t).toReal := by
    apply Finset.sum_eq_single t
    · intro j _hj hj_ne
      exact hzero j hj_ne
    · intro hnot
      simp at hnot
  have hsum : (∑ j : Item n, (ρ 2 j).toReal) = 1 :=
    AppliedModelingLib.pmfToRealSum (ρ 2)
  rw [hsum] at hsum_single
  exact hsum_single.symm

/--
Auxiliary full-policy center-case value identity corresponding to Lemma 15.

The paper's displayed center `λ` formula is written for its half-LP convention.
In the full mirrored-policy Problem 11 encoding used here, an exact center pivot
has `q_t = 1/2`, `n - 2*t.val = 1`, and the denominator equation simplifies to
`λ = 1 / (1 + L_t)`.
-/
theorem theorem4Problem11Lemma15_lambda_eq_of_center_fullPolicy
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    {ρ : TypePolicy 3 n} {ell : ℝ} {t : Item n}
    (hbeta_pos : 0 < beta)
    (hpos : ∀ l : Item n, 0 < v l)
    (h : Theorem4Problem11EqualizedBasicOptimal beta v ρ ell)
    (hpivot : Theorem4Problem11PivotSupport ρ t)
    (hcenter : t.val = (reverseItem t).val) :
    ell = 1 / (1 + theorem4Problem11LeftSum v t) := by
  let L : ℝ := theorem4Problem11LeftSum v t
  have hmul :=
    theorem4Problem11Lemma15_lambda_mul_denominator_eq
      hbeta_pos hpos h hpivot (le_of_eq hcenter)
  have hq : pairShare (1 / 2) v t = (1 / 2 : ℝ) :=
    pairShare_half_eq_half_of_val_eq_reverse t hpos hcenter
  have hcenter_nat : 2 * t.val + 1 = n :=
    (val_eq_reverseItem_iff t).mp hcenter
  have hcenter_real : (2 : ℝ) * (t.val : ℝ) + 1 = (n : ℝ) := by
    exact_mod_cast hcenter_nat
  have hden_eq :
      (n : ℝ) - 2 * (t.val : ℝ) +
          2 * pairShare (1 / 2) v t * theorem4Problem11LeftSum v t =
        1 + L := by
    dsimp [L]
    rw [hq]
    nlinarith
  have hnum_eq :
      4 * beta * pairShare (1 / 2) v t + (1 - 2 * beta) = 1 := by
    rw [hq]
    ring
  have hmul_one : ell * (1 + L) = 1 := by
    rw [hden_eq, hnum_eq] at hmul
    exact hmul
  have hden_pos : 0 < 1 + L := by
    have hL_nonneg : 0 ≤ L := by
      dsimp [L]
      exact theorem4Problem11LeftSum_nonneg hpos t
    nlinarith
  rw [eq_div_iff (ne_of_gt hden_pos)]
  exact hmul_one

/--
The center-item equation used by the paper's half-LP display in Appendix E,
Lemma 15.  For an exact center pivot the paper writes the known-type
contribution as `2β q_t x_t`; the full mirrored-policy encoding has the
separate mirror term as well.
-/
def Theorem4Problem11CenterHalfLPItemEquation {n : ℕ}
    (beta : ℝ) (v : Item n → ℝ) (ρ : TypePolicy 3 n)
    (ell : ℝ) (t : Item n) : Prop :=
  ell =
    2 * beta * pairShare (1 / 2) v t * (ρ 0 t).toReal +
      (1 - 2 * beta) * (ρ 2 t).toReal

/--
Appendix E, Lemma 15 center `λ` formula in the paper's half-LP convention.

This proves the displayed source formula exactly once the center item equation
is read in the half-LP convention above.  The full mirrored-policy Problem 11
interface instead uses `theorem4Problem11Lemma15_lambda_eq_of_center_fullPolicy`.
-/
theorem theorem4Problem11Lemma15_lambda_eq_of_center_halfLPConvention
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    {ρ : TypePolicy 3 n} {ell : ℝ} {t : Item n}
    (hbeta_pos : 0 < beta)
    (hpos : ∀ l : Item n, 0 < v l)
    (h : Theorem4Problem11EqualizedBasicOptimal beta v ρ ell)
    (hpivot : Theorem4Problem11PivotSupport ρ t)
    (hcenter : t.val = (reverseItem t).val)
    (hhalf :
      Theorem4Problem11CenterHalfLPItemEquation beta v ρ ell t) :
    ell =
      (2 * beta * pairShare (1 / 2) v t + (1 - 2 * beta)) /
        (1 + pairShare (1 / 2) v t * theorem4Problem11LeftSum v t) := by
  let q : ℝ := pairShare (1 / 2) v t
  let L : ℝ := theorem4Problem11LeftSum v t
  have hx :=
    theorem4Problem11Lemma15_typeZero_pivot_eq_one_sub_leftSum
      hbeta_pos hpos h hpivot (le_of_eq hcenter)
  have hz :=
    theorem4Problem11Lemma15_cold_center_eq_one hpivot hcenter.symm
  have hbeta_ne : beta ≠ 0 := ne_of_gt hbeta_pos
  have hitem := hhalf
  dsimp [Theorem4Problem11CenterHalfLPItemEquation] at hitem
  rw [hx, hz] at hitem
  have hmul :
      ell * (1 + q * L) =
        2 * beta * q + (1 - 2 * beta) := by
    dsimp [q, L] at hitem ⊢
    field_simp [hbeta_ne] at hitem
    ring_nf at hitem ⊢
    nlinarith
  have hden_pos : 0 < 1 + q * L := by
    have hq_nonneg : 0 ≤ q := by
      dsimp [q]
      exact (pairShare_pos t (by norm_num) (by norm_num) hpos).le
    have hL_nonneg : 0 ≤ L := by
      dsimp [L]
      exact theorem4Problem11LeftSum_nonneg hpos t
    nlinarith [mul_nonneg hq_nonneg hL_nonneg]
  change ell = (2 * beta * q + (1 - 2 * beta)) / (1 + q * L)
  rw [eq_div_iff (ne_of_gt hden_pos)]
  exact hmul

theorem theorem4Problem11EqualizedBasicOptimal_not_lastActive_lt
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    {ρ ρ' : TypePolicy 3 n} {ell ell' : ℝ}
    (hn : 2 < n)
    (hbeta_pos : 0 < beta)
    (hbeta_half : beta < 1 / 2)
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (h : Theorem4Problem11EqualizedBasicOptimal beta v ρ ell)
    (h' : Theorem4Problem11EqualizedBasicOptimal beta v ρ' ell') :
    ¬ (theorem4Problem11LastActiveTypeZero ρ).val <
      (theorem4Problem11LastActiveTypeZero ρ').val := by
  intro htt'
  let t : Item n := theorem4Problem11LastActiveTypeZero ρ
  let t' : Item n := theorem4Problem11LastActiveTypeZero ρ'
  have hpivot :
      Theorem4Problem11PivotSupport ρ t := by
    dsimp [t]
    exact theorem4Problem11PivotSupport_of_equalizedBasicOptimal
      hn hbeta_pos hbeta_half hpos hdec h
  have hpivot' :
      Theorem4Problem11PivotSupport ρ' t' := by
    dsimp [t']
    exact theorem4Problem11PivotSupport_of_equalizedBasicOptimal
      hn hbeta_pos hbeta_half hpos hdec h'
  have hleft' : t'.val ≤ (reverseItem t').val := by
    dsimp [t']
    exact theorem4Problem11LastActiveTypeZero_le_reverse_of_equalizedBasicOptimal
      hn hbeta_pos hpos hdec h'
  have hrev_t'_lt_rev_t :
      (reverseItem t').val < (reverseItem t).val := by
    exact reverseItem_val_lt_of_val_lt htt'
  have ht_left : t.val < (reverseItem t).val := by
    have ht'_lt_rev_t : t'.val < (reverseItem t).val :=
      lt_of_le_of_lt hleft' hrev_t'_lt_rev_t
    exact lt_trans htt' ht'_lt_rev_t
  have ht'_lt_rev_t : t'.val < (reverseItem t).val :=
    lt_of_le_of_lt hleft' hrev_t'_lt_rev_t
  let q : ℝ := pairShare (1 / 2) v t
  let a : ℝ := 2 * beta * q
  let c : ℝ := 1 - 2 * beta
  let leftx : ℝ :=
    ∑ j : Item n, if j.val < t.val then (ρ 0 j).toReal else 0
  let leftx' : ℝ :=
    ∑ j : Item n, if j.val < t.val then (ρ' 0 j).toReal else 0
  let rightx' : ℝ :=
    ∑ j : Item n, if t.val < j.val then (ρ' 0 j).toReal else 0
  have hq_pos : 0 < q := by
    dsimp [q]
    exact pairShare_pos t (by norm_num) (by norm_num) hpos
  have ha_pos : 0 < a := by
    dsimp [a]
    positivity
  have hc_pos : 0 < c := by
    dsimp [c]
    nlinarith
  have hleft_eq : leftx = leftx' := by
    unfold leftx leftx'
    refine Finset.sum_congr rfl ?_
    intro j _hj
    by_cases hjt : j.val < t.val
    · have hjt' : j.val < t'.val := lt_trans hjt htt'
      have hx_eq :
          (ρ 0 j).toReal = (ρ' 0 j).toReal := by
        dsimp [t, t'] at hjt hjt'
        exact theorem4Problem11EqualizedBasicOptimal_typeZero_toReal_eq_of_before_both_lastActive
          hn hbeta_pos hbeta_half hpos hdec h h' hjt hjt'
      simp [hjt, hx_eq]
    · simp [hjt]
  have hx_t_eq :
      (ρ 0 t).toReal = 1 - leftx := by
    dsimp [leftx]
    exact theorem4Problem11PivotSupport_typeZero_pivot_toReal_eq_one_sub_leftSum
      hpivot
  have hitem_t :
      theorem4Problem11PolicyItemValue beta v ρ t =
        a * (ρ 0 t).toReal + c * (ρ 2 t).toReal := by
    dsimp [a, c, q]
    exact theorem4Problem11PivotSupport_policyItemValue_eq_at_left_pivot
      hpivot ht_left
  have hitem_t' :
      theorem4Problem11PolicyItemValue beta v ρ' t =
        a * (ρ' 0 t).toReal := by
    have hknown :=
      theorem4Problem11PolicyItemValue_eq_known_of_lt_pivot
        (beta := beta) (v := v) (ρ := ρ') hpivot' hleft' htt'
    dsimp [a, q]
    simpa [t] using hknown
  have hell : ell = ell' :=
    theorem4Problem11EqualizedBasicOptimal_value_unique h h'
  have hmain :
      a * (1 - leftx) + c * (ρ 2 t).toReal =
        a * (ρ' 0 t).toReal := by
    nlinarith [hitem_t, hitem_t', h.item_eq t, h'.item_eq t, hell, hx_t_eq]
  have hz_nonneg : 0 ≤ (ρ 2 t).toReal := ENNReal.toReal_nonneg
  have hprefix_ge : 1 ≤ leftx' + (ρ' 0 t).toReal := by
    nlinarith [hmain, hleft_eq, ha_pos, mul_nonneg hc_pos.le hz_nonneg]
  have hx'_pivot_pos : 0 < (ρ' 0 t').toReal := by
    dsimp [t']
    exact typePolicy_toReal_pos_of_ne_zero ρ'
      (theorem4Problem11LastActiveTypeZero_active ρ')
  have hrightx'_pos : 0 < rightx' := by
    have hle : (ρ' 0 t').toReal ≤ rightx' := by
      have htt_fin : t < t' := by exact htt'
      unfold rightx'
      simpa [htt_fin] using
        Finset.single_le_sum
          (s := (Finset.univ : Finset (Item n)))
          (f := fun j : Item n => if t.val < j.val then (ρ' 0 j).toReal else 0)
          (fun j _hj => by
            by_cases hj : t.val < j.val
            · simp [hj, ENNReal.toReal_nonneg]
            · simp [hj])
          (by simp : t' ∈ (Finset.univ : Finset (Item n)))
    exact lt_of_lt_of_le hx'_pivot_pos hle
  have hsplit' :=
    theorem4_sum_eq_left_part_add_pivot_add_right_part
      (fun j : Item n => (ρ' 0 j).toReal) t
  have hsum' : (∑ j : Item n, (ρ' 0 j).toReal) = 1 :=
    AppliedModelingLib.pmfToRealSum (ρ' 0)
  have hprefix_lt : leftx' + (ρ' 0 t).toReal < 1 := by
    have hsum_split :
        (∑ j : Item n, (ρ' 0 j).toReal) =
          leftx' + (ρ' 0 t).toReal + rightx' := by
      simpa [leftx', rightx'] using hsplit'
    nlinarith
  linarith

theorem theorem4Problem11EqualizedBasicOptimal_lastActive_eq
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    {ρ ρ' : TypePolicy 3 n} {ell ell' : ℝ}
    (hn : 2 < n)
    (hbeta_pos : 0 < beta)
    (hbeta_half : beta < 1 / 2)
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (h : Theorem4Problem11EqualizedBasicOptimal beta v ρ ell)
    (h' : Theorem4Problem11EqualizedBasicOptimal beta v ρ' ell') :
    theorem4Problem11LastActiveTypeZero ρ =
      theorem4Problem11LastActiveTypeZero ρ' := by
  have hnot_lt :
      ¬ (theorem4Problem11LastActiveTypeZero ρ).val <
        (theorem4Problem11LastActiveTypeZero ρ').val :=
    theorem4Problem11EqualizedBasicOptimal_not_lastActive_lt
      hn hbeta_pos hbeta_half hpos hdec h h'
  have hnot_gt :
      ¬ (theorem4Problem11LastActiveTypeZero ρ').val <
        (theorem4Problem11LastActiveTypeZero ρ).val :=
    theorem4Problem11EqualizedBasicOptimal_not_lastActive_lt
      hn hbeta_pos hbeta_half hpos hdec h' h
  apply Fin.ext
  omega

theorem theorem4Problem11EqualizedBasicOptimal_typeZero_toReal_eq
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    {ρ ρ' : TypePolicy 3 n} {ell ell' : ℝ}
    (hn : 2 < n)
    (hbeta_pos : 0 < beta)
    (hbeta_half : beta < 1 / 2)
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (h : Theorem4Problem11EqualizedBasicOptimal beta v ρ ell)
    (h' : Theorem4Problem11EqualizedBasicOptimal beta v ρ' ell')
    (j : Item n) :
    (ρ 0 j).toReal = (ρ' 0 j).toReal := by
  let t : Item n := theorem4Problem11LastActiveTypeZero ρ
  let t' : Item n := theorem4Problem11LastActiveTypeZero ρ'
  have ht_eq : t = t' := by
    dsimp [t, t']
    exact theorem4Problem11EqualizedBasicOptimal_lastActive_eq
      hn hbeta_pos hbeta_half hpos hdec h h'
  have hpivot :
      Theorem4Problem11PivotSupport ρ t := by
    dsimp [t]
    exact theorem4Problem11PivotSupport_of_equalizedBasicOptimal
      hn hbeta_pos hbeta_half hpos hdec h
  have hpivot' :
      Theorem4Problem11PivotSupport ρ' t' := by
    dsimp [t']
    exact theorem4Problem11PivotSupport_of_equalizedBasicOptimal
      hn hbeta_pos hbeta_half hpos hdec h'
  by_cases hjlt : j.val < t.val
  · have hjlt' : j.val < t'.val := by simpa [← ht_eq] using hjlt
    dsimp [t, t'] at hjlt hjlt'
    exact theorem4Problem11EqualizedBasicOptimal_typeZero_toReal_eq_of_before_both_lastActive
      hn hbeta_pos hbeta_half hpos hdec h h' hjlt hjlt'
  · by_cases hjeq : j = t
    · subst j
      let leftx : ℝ :=
        ∑ l : Item n, if l.val < t.val then (ρ 0 l).toReal else 0
      let leftx' : ℝ :=
        ∑ l : Item n, if l.val < t.val then (ρ' 0 l).toReal else 0
      have hleft_eq : leftx = leftx' := by
        unfold leftx leftx'
        refine Finset.sum_congr rfl ?_
        intro l _hl
        by_cases hlt : l.val < t.val
        · have hlt' : l.val < t'.val := by simpa [← ht_eq] using hlt
          have hx_eq :
              (ρ 0 l).toReal = (ρ' 0 l).toReal := by
            dsimp [t, t'] at hlt hlt'
            exact theorem4Problem11EqualizedBasicOptimal_typeZero_toReal_eq_of_before_both_lastActive
              hn hbeta_pos hbeta_half hpos hdec h h' hlt hlt'
          simp [hlt, hx_eq]
        · simp [hlt]
      have hx_t :
          (ρ 0 t).toReal = 1 - leftx := by
        dsimp [leftx]
        exact theorem4Problem11PivotSupport_typeZero_pivot_toReal_eq_one_sub_leftSum
          hpivot
      have hx_t' :
          (ρ' 0 t).toReal = 1 - leftx' := by
        have hx_raw :=
          theorem4Problem11PivotSupport_typeZero_pivot_toReal_eq_one_sub_leftSum
            hpivot'
        dsimp [leftx']
        simpa [ht_eq] using hx_raw
      nlinarith
    · have hjgt : t.val < j.val := by
        have hne_val : j.val ≠ t.val := by
          intro hval
          exact hjeq (Fin.ext hval)
        omega
      have hx : ρ 0 j = 0 := hpivot.1 j hjgt
      have hjgt' : t'.val < j.val := by simpa [← ht_eq] using hjgt
      have hx' : ρ' 0 j = 0 := hpivot'.1 j hjgt'
      simp [hx, hx']

theorem theorem4Problem11EqualizedBasicOptimal_cold_toReal_eq
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    {ρ ρ' : TypePolicy 3 n} {ell ell' : ℝ}
    (hn : 2 < n)
    (hbeta_pos : 0 < beta)
    (hbeta_half : beta < 1 / 2)
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (h : Theorem4Problem11EqualizedBasicOptimal beta v ρ ell)
    (h' : Theorem4Problem11EqualizedBasicOptimal beta v ρ' ell')
    (j : Item n) :
    (ρ 2 j).toReal = (ρ' 2 j).toReal := by
  have hell : ell = ell' :=
    theorem4Problem11EqualizedBasicOptimal_value_unique h h'
  have hxj :
      (ρ 0 j).toReal = (ρ' 0 j).toReal :=
    theorem4Problem11EqualizedBasicOptimal_typeZero_toReal_eq
      hn hbeta_pos hbeta_half hpos hdec h h' j
  have hxrev :
      (ρ 0 (reverseItem j)).toReal =
        (ρ' 0 (reverseItem j)).toReal :=
    theorem4Problem11EqualizedBasicOptimal_typeZero_toReal_eq
      hn hbeta_pos hbeta_half hpos hdec h h' (reverseItem j)
  have hitem :
      theorem4Problem11PolicyItemValue beta v ρ j =
        theorem4Problem11PolicyItemValue beta v ρ' j := by
    calc
      theorem4Problem11PolicyItemValue beta v ρ j = ell := h.item_eq j
      _ = ell' := hell
      _ = theorem4Problem11PolicyItemValue beta v ρ' j := (h'.item_eq j).symm
  have hc_pos : 0 < 1 - 2 * beta := by nlinarith
  unfold theorem4Problem11PolicyItemValue theorem4Problem11ItemValue at hitem
  change
    2 * beta *
          (pairShare (1 / 2) v j * (ρ 0 j).toReal +
            (1 - pairShare (1 / 2) v j) *
              (ρ 0 (reverseItem j)).toReal) +
        (1 - 2 * beta) * (ρ 2 j).toReal =
      2 * beta *
          (pairShare (1 / 2) v j * (ρ' 0 j).toReal +
            (1 - pairShare (1 / 2) v j) *
              (ρ' 0 (reverseItem j)).toReal) +
        (1 - 2 * beta) * (ρ' 2 j).toReal at hitem
  rw [hxj, hxrev] at hitem
  nlinarith

theorem theorem4Problem11EqualizedBasicOptimal_policy_eq
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    {ρ ρ' : TypePolicy 3 n} {ell ell' : ℝ}
    (hn : 2 < n)
    (hbeta_pos : 0 < beta)
    (hbeta_half : beta < 1 / 2)
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (h : Theorem4Problem11EqualizedBasicOptimal beta v ρ ell)
    (h' : Theorem4Problem11EqualizedBasicOptimal beta v ρ' ell') :
    ρ = ρ' := by
  funext k
  fin_cases k
  · apply pmf_eq_of_forall_toReal_eq
    intro j
    change ((ρ 0) j).toReal = ((ρ' 0) j).toReal
    exact theorem4Problem11EqualizedBasicOptimal_typeZero_toReal_eq
      hn hbeta_pos hbeta_half hpos hdec h h' j
  · apply pmf_eq_of_forall_toReal_eq
    intro j
    change ((ρ 1) j).toReal = ((ρ' 1) j).toReal
    have hmirror :
        ρ 1 j = ρ 0 (reverseItem j) := by
      simpa [reverseItem_reverseItem] using h.mirror.1 (reverseItem j)
    have hmirror' :
        ρ' 1 j = ρ' 0 (reverseItem j) := by
      simpa [reverseItem_reverseItem] using h'.mirror.1 (reverseItem j)
    rw [hmirror, hmirror']
    exact theorem4Problem11EqualizedBasicOptimal_typeZero_toReal_eq
      hn hbeta_pos hbeta_half hpos hdec h h' (reverseItem j)
  · apply pmf_eq_of_forall_toReal_eq
    intro j
    change ((ρ 2) j).toReal = ((ρ' 2) j).toReal
    exact theorem4Problem11EqualizedBasicOptimal_cold_toReal_eq
      hn hbeta_pos hbeta_half hpos hdec h h' j

theorem theorem4Problem11PolicyOptimal_policy_eq_of_closedDual_tight
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ} {t : Item n}
    {ρ ρ' : TypePolicy 3 n} {ell ell' : ℝ}
    (hn : 2 < n)
    (hbeta_pos : 0 < beta)
    (hbeta_half : beta < 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hleft : t.val ≤ (reverseItem t).val)
    (hvalue : ell = theorem4Problem11ClosedDualValue beta v t)
    (hvalue' : ell' = theorem4Problem11ClosedDualValue beta v t)
    (hopt : Theorem4Problem11PolicyOptimal beta v ρ ell)
    (hopt' : Theorem4Problem11PolicyOptimal beta v ρ' ell') :
    ρ = ρ' := by
  exact theorem4Problem11EqualizedBasicOptimal_policy_eq
    hn hbeta_pos hbeta_half hpos hdec
    (theorem4Problem11PolicyOptimal_equalizedBasicOptimal_of_closedDual_tight
      hbeta_pos hbeta_half hpos hdec hleft hvalue hopt)
    (theorem4Problem11PolicyOptimal_equalizedBasicOptimal_of_closedDual_tight
      hbeta_pos hbeta_half hpos hdec hleft hvalue' hopt')

theorem theorem4Problem11PolicyOptimal_pairwise_unique_of_closed_policyOptimal
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ} {t : Item n}
    {ρclosed : TypePolicy 3 n}
    (hn : 2 < n)
    (hbeta_pos : 0 < beta)
    (hbeta_half : beta < 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hleft : t.val ≤ (reverseItem t).val)
    (hclosed :
      Theorem4Problem11PolicyOptimal beta v ρclosed
        (theorem4Problem11ClosedDualValue beta v t)) :
    ∀ (ρa ρb : TypePolicy 3 n) (ella ellb : ℝ),
      Theorem4Problem11PolicyOptimal beta v ρa ella →
      Theorem4Problem11PolicyOptimal beta v ρb ellb →
      ρa = ρb := by
  intro ρa ρb ella ellb hopt_a hopt_b
  have ha :
      ella = theorem4Problem11ClosedDualValue beta v t :=
    theorem4Problem11PolicyOptimal_value_unique hopt_a hclosed
  have hb :
      ellb = theorem4Problem11ClosedDualValue beta v t :=
    theorem4Problem11PolicyOptimal_value_unique hopt_b hclosed
  exact theorem4Problem11PolicyOptimal_policy_eq_of_closedDual_tight
    hn hbeta_pos hbeta_half hpos hdec hleft ha hb hopt_a hopt_b

/--
Problem 11 / estimated Problem 1 bridge: if the selected equality-form
Problem 11 optimum is the unique epigraph-optimal mirror-symmetric policy,
then it solves the reduced estimated `γ = 1` user-fairness problem.

The uniqueness hypothesis is the exact LP-selection seam left by the paper's
basic-feasible-solution argument.
-/
theorem theorem4Problem11EqualizedBasicOptimal_isOptimalAtLevel_of_policyOptimal_unique
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hbeta : 0 ≤ beta) (hcold : 0 ≤ 1 - 2 * beta)
    (hpos : ∀ j : Item n, 0 < v j)
    {ρ : TypePolicy 3 n} {ell : ℝ}
    (h : Theorem4Problem11EqualizedBasicOptimal beta v ρ ell)
    (hunique :
      ∀ (ρ' : TypePolicy 3 n) (ell' : ℝ),
        Theorem4Problem11PolicyOptimal beta v ρ' ell' → ρ' = ρ) :
    TypeWeightedRecommendationModel.IsOptimalAtLevel
      (theorem4EstimatedReducedModel beta v) 1 ρ := by
  let T := theorem4EstimatedReducedModel beta v
  have hfeas :
      TypeWeightedRecommendationModel.feasibleAtLevel T 1 ρ :=
    theorem4Problem11EqualizedBasicOptimal_feasibleAtLevel_one
      hbeta hcold hpos h
  refine ⟨hfeas, ?_⟩
  apply le_antisymm
  · have hbdd :
        BddAbove (TypeWeightedRecommendationModel.attainableTypeFairnessAtLevel T 1) :=
      TypeWeightedRecommendationModel.attainableTypeFairnessAtLevel_bddAbove_of_rowHasPositiveItem
        T (theorem4EstimatedReducedModel_rowHasPositiveItem hpos) 1
    have hmem :
        TypeWeightedRecommendationModel.typeFairness T ρ ∈
          TypeWeightedRecommendationModel.attainableTypeFairnessAtLevel T 1 := by
      exact ⟨ρ, hfeas, rfl⟩
    exact le_csSup hbdd hmem
  · unfold TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
    refine csSup_le ?_ ?_
    · exact ⟨TypeWeightedRecommendationModel.typeFairness T ρ,
        ⟨ρ, hfeas, rfl⟩⟩
    · intro r hr
      rcases hr with ⟨ρ', hfeas', rfl⟩
      let ρsym : TypePolicy 3 n := theorem4SymmetrizedPolicy ρ'
      have hopt_sym :
          Theorem4Problem11PolicyOptimal beta v ρsym
            (TypeWeightedRecommendationModel.itemFairness T ρsym) := by
        dsimp [ρsym, T]
        exact theorem4Problem11PolicyOptimal_symmetrized_of_feasibleAtLevel_one
          hbeta hcold hpos hfeas'
      have hρsym_eq : ρsym = ρ :=
        hunique ρsym (TypeWeightedRecommendationModel.itemFairness T ρsym)
          hopt_sym
      have htype_le_sym :
          TypeWeightedRecommendationModel.typeFairness T ρ' ≤
            TypeWeightedRecommendationModel.typeFairness T ρsym := by
        dsimp [T, ρsym]
        exact theorem4EstimatedReducedModel_typeFairness_le_symmetrized
          hpos ρ'
      simpa [hρsym_eq] using htype_le_sym

/--
Problem 11 / estimated Problem 1 bridge using the paper's Lemma 14 uniqueness:
if every epigraph-optimal mirror-symmetric policy is supplied as an
equality-form basic optimum, then the selected equality-form optimum solves the
reduced estimated `γ = 1` user-fairness problem.
-/
theorem theorem4Problem11EqualizedBasicOptimal_isOptimalAtLevel_of_equalized_selection
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hn : 2 < n)
    (hbeta_pos : 0 < beta) (hbeta_half : beta < 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    {ρ : TypePolicy 3 n} {ell : ℝ}
    (h : Theorem4Problem11EqualizedBasicOptimal beta v ρ ell)
    (hselection :
      ∀ (ρ' : TypePolicy 3 n) (ell' : ℝ),
        Theorem4Problem11PolicyOptimal beta v ρ' ell' →
          Theorem4Problem11EqualizedBasicOptimal beta v ρ' ell') :
    TypeWeightedRecommendationModel.IsOptimalAtLevel
      (theorem4EstimatedReducedModel beta v) 1 ρ := by
  have hbeta_nonneg : 0 ≤ beta := hbeta_pos.le
  have hcold : 0 ≤ 1 - 2 * beta := by nlinarith
  refine theorem4Problem11EqualizedBasicOptimal_isOptimalAtLevel_of_policyOptimal_unique
    hbeta_nonneg hcold hpos h ?_
  intro ρ' ell' hopt'
  have h' : Theorem4Problem11EqualizedBasicOptimal beta v ρ' ell' :=
    hselection ρ' ell' hopt'
  exact theorem4Problem11EqualizedBasicOptimal_policy_eq
    hn hbeta_pos hbeta_half hpos hdec h' h

/--
The same estimated-optimality bridge after rebuilding a policy from the
paper's real equality-form Problem 11 BFS data.
-/
theorem theorem4Problem11EqualityFormOptimalBFS_isOptimalAtLevel_of_equalized_selection
    {n : ℕ} [NeZero n] {beta : ℝ} {v x z : Item n → ℝ} {ell : ℝ}
    (hn : 2 < n)
    (hbeta_pos : 0 < beta) (hbeta_half : beta < 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (h : Theorem4Problem11EqualityFormOptimalBFS beta v x z ell)
    (hselection :
      ∀ (ρ' : TypePolicy 3 n) (ell' : ℝ),
        Theorem4Problem11PolicyOptimal beta v ρ' ell' →
          Theorem4Problem11EqualizedBasicOptimal beta v ρ' ell') :
    TypeWeightedRecommendationModel.IsOptimalAtLevel
      (theorem4EstimatedReducedModel beta v) 1
      (theorem4Problem11PolicyOfRealVectors x z
        h.feasible.x_nonneg h.feasible.z_nonneg
        h.feasible.sum_x h.feasible.sum_z) := by
  exact theorem4Problem11EqualizedBasicOptimal_isOptimalAtLevel_of_equalized_selection
    hn hbeta_pos hbeta_half hpos hdec
    (theorem4Problem11EqualizedBasicOptimal_of_equalityFormOptimalBFS h)
    hselection

theorem theorem4Problem11PivotSupport_typeZero_first_toReal_eq_one
    {n : ℕ} [NeZero n] {ρ : TypePolicy 3 n} {t : Item n}
    (hpivot : Theorem4Problem11PivotSupport ρ t)
    (ht : t = theorem4FirstItem) :
    (ρ 0 theorem4FirstItem).toReal = 1 := by
  have hsum_single :
      (∑ j : Item n, (ρ 0 j).toReal) =
        (ρ 0 theorem4FirstItem).toReal := by
    apply Finset.sum_eq_single theorem4FirstItem
    · intro j _hj hj_ne
      have hz :
          ρ 0 j = 0 :=
        theorem4Problem11PivotSupport_typeZero_zero_of_pivot_first
          hpivot ht hj_ne
      simp [hz]
    · intro hnot
      simp at hnot
  have hsum : (∑ j : Item n, (ρ 0 j).toReal) = 1 :=
    AppliedModelingLib.pmfToRealSum (ρ 0)
  rw [hsum] at hsum_single
  exact hsum_single.symm

theorem theorem4Problem11PivotSupport_typeZero_reverse_first_toReal_eq_zero
    {n : ℕ} [NeZero n] {ρ : TypePolicy 3 n} {t : Item n}
    (hn : 1 < n)
    (hpivot : Theorem4Problem11PivotSupport ρ t)
    (ht : t = theorem4FirstItem) :
    (ρ 0 (reverseItem theorem4FirstItem)).toReal = 0 := by
  have hne :
      reverseItem (theorem4FirstItem : Item n) ≠ theorem4FirstItem := by
    intro h
    have hval := congrArg Fin.val h
    simp [theorem4FirstItem, reverseItem] at hval
    omega
  have hz :
      ρ 0 (reverseItem theorem4FirstItem) = 0 :=
    theorem4Problem11PivotSupport_typeZero_zero_of_pivot_first
      hpivot ht hne
  simp [hz]

theorem theorem4Problem11PivotSupport_sum_typeZero_q_of_pivot_first
    {n : ℕ} [NeZero n] {v : Item n → ℝ}
    {ρ : TypePolicy 3 n} {t : Item n}
    (hpivot : Theorem4Problem11PivotSupport ρ t)
    (ht : t = theorem4FirstItem) :
    (∑ j : Item n,
        pairShare (1 / 2) v j * (ρ 0 j).toReal) =
      pairShare (1 / 2) v theorem4FirstItem := by
  have hxfirst :=
    theorem4Problem11PivotSupport_typeZero_first_toReal_eq_one
      hpivot ht
  have hsum_single :
      (∑ j : Item n,
          pairShare (1 / 2) v j * (ρ 0 j).toReal) =
        pairShare (1 / 2) v theorem4FirstItem *
          (ρ 0 theorem4FirstItem).toReal := by
    apply Finset.sum_eq_single theorem4FirstItem
    · intro j _hj hj_ne
      have hz :
          ρ 0 j = 0 :=
        theorem4Problem11PivotSupport_typeZero_zero_of_pivot_first
          hpivot ht hj_ne
      simp [hz]
    · intro hnot
      simp at hnot
  rw [hsum_single, hxfirst]
  ring

theorem theorem4Problem11PivotSupport_sum_typeZero_reverse_q_of_pivot_first
    {n : ℕ} [NeZero n] {v : Item n → ℝ}
    (hpos : ∀ j : Item n, 0 < v j)
    {ρ : TypePolicy 3 n} {t : Item n}
    (hpivot : Theorem4Problem11PivotSupport ρ t)
    (ht : t = theorem4FirstItem) :
    (∑ j : Item n,
        (1 - pairShare (1 / 2) v j) *
          (ρ 0 (reverseItem j)).toReal) =
      pairShare (1 / 2) v theorem4FirstItem := by
  have hreindex :
      (∑ j : Item n,
          (1 - pairShare (1 / 2) v j) *
            (ρ 0 (reverseItem j)).toReal) =
        ∑ j : Item n,
          (1 - pairShare (1 / 2) v (reverseItem j)) *
            (ρ 0 j).toReal := by
    simpa [reverseItem_reverseItem] using
      (sum_reverseItem
        (fun j : Item n =>
          (1 - pairShare (1 / 2) v (reverseItem j)) *
            (ρ 0 j).toReal))
  have hxfirst :=
    theorem4Problem11PivotSupport_typeZero_first_toReal_eq_one
      hpivot ht
  have hsum_single :
      (∑ j : Item n,
          (1 - pairShare (1 / 2) v (reverseItem j)) *
            (ρ 0 j).toReal) =
        (1 - pairShare (1 / 2) v (reverseItem theorem4FirstItem)) *
          (ρ 0 theorem4FirstItem).toReal := by
    apply Finset.sum_eq_single theorem4FirstItem
    · intro j _hj hj_ne
      have hz :
          ρ 0 j = 0 :=
        theorem4Problem11PivotSupport_typeZero_zero_of_pivot_first
          hpivot ht hj_ne
      simp [hz]
    · intro hnot
      simp at hnot
  have hq :
      1 - pairShare (1 / 2) v (reverseItem theorem4FirstItem) =
        pairShare (1 / 2) v theorem4FirstItem :=
    (pairShare_half_eq_one_sub_reverse theorem4FirstItem hpos).symm
  rw [hreindex, hsum_single, hxfirst, hq]
  ring

theorem theorem4Problem11PivotSupport_sum_itemValue_of_pivot_first
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hpos : ∀ j : Item n, 0 < v j)
    {ρ : TypePolicy 3 n} {t : Item n}
    (hpivot : Theorem4Problem11PivotSupport ρ t)
    (ht : t = theorem4FirstItem) :
    (∑ j : Item n, theorem4Problem11PolicyItemValue beta v ρ j) =
      4 * beta * pairShare (1 / 2) v theorem4FirstItem +
        (1 - 2 * beta) := by
  have hsum_q :=
    theorem4Problem11PivotSupport_sum_typeZero_q_of_pivot_first
      (v := v) hpivot ht
  have hsum_rev :=
    theorem4Problem11PivotSupport_sum_typeZero_reverse_q_of_pivot_first
      hpos hpivot ht
  have hsum_z : (∑ j : Item n, (ρ 2 j).toReal) = 1 :=
    AppliedModelingLib.pmfToRealSum (ρ 2)
  unfold theorem4Problem11PolicyItemValue theorem4Problem11ItemValue
  have hleft :
      (∑ j : Item n,
        2 * beta *
            (pairShare (1 / 2) v j * (ρ 0 j).toReal +
              (1 - pairShare (1 / 2) v j) *
                (ρ 0 (reverseItem j)).toReal)) =
        2 * beta *
          ((∑ j : Item n,
              pairShare (1 / 2) v j * (ρ 0 j).toReal) +
            (∑ j : Item n,
              (1 - pairShare (1 / 2) v j) *
                (ρ 0 (reverseItem j)).toReal)) := by
    rw [← Finset.mul_sum, Finset.sum_add_distrib]
  have hright :
      (∑ j : Item n, (1 - 2 * beta) * (ρ 2 j).toReal) =
        (1 - 2 * beta) * (∑ j : Item n, (ρ 2 j).toReal) := by
    rw [← Finset.mul_sum]
  rw [Finset.sum_add_distrib, hleft, hright, hsum_q, hsum_rev, hsum_z]
  ring

theorem theorem4Problem11PivotOneLambda_eq_of_equalized_pivotSupport
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hpos : ∀ j : Item n, 0 < v j)
    {ρ : TypePolicy 3 n} {ell : ℝ} {t : Item n}
    (h : Theorem4Problem11EqualizedBasicOptimal beta v ρ ell)
    (hpivot : Theorem4Problem11PivotSupport ρ t)
    (ht : t = theorem4FirstItem) :
    ell = theorem4Problem11PivotOneLambda beta v := by
  have hnpos_nat : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hn_ne : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hnpos_nat)
  have hsum_values :=
    theorem4Problem11PivotSupport_sum_itemValue_of_pivot_first
      (beta := beta) hpos hpivot ht
  have hsum_eq :
      (∑ j : Item n, theorem4Problem11PolicyItemValue beta v ρ j) =
        (n : ℝ) * ell := by
    calc
      (∑ j : Item n, theorem4Problem11PolicyItemValue beta v ρ j)
          = ∑ _j : Item n, ell := by
            apply Finset.sum_congr rfl
            intro j _hj
            exact h.item_eq j
      _ = (n : ℝ) * ell := by
            simp [Item]
  have hell_mul :
      (n : ℝ) * ell =
        4 * beta * pairShare (1 / 2) v theorem4FirstItem +
          (1 - 2 * beta) := by
    rw [← hsum_eq]
    exact hsum_values
  have hden_eq :
      1 + (1 / 2 : ℝ) * ((n : ℝ) - 2) = (n : ℝ) / 2 := by
    ring
  unfold theorem4Problem11PivotOneLambda
  rw [hden_eq]
  rw [eq_div_iff (by positivity : (n : ℝ) / 2 ≠ 0)]
  nlinarith

theorem theorem4Problem11PivotOne_closedZ_of_equalized_pivotSupport
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hn : 1 < n)
    (hbeta_half : beta < 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    {ρ : TypePolicy 3 n} {ell : ℝ} {t : Item n}
    (h : Theorem4Problem11EqualizedBasicOptimal beta v ρ ell)
    (hpivot : Theorem4Problem11PivotSupport ρ t)
    (ht : t = theorem4FirstItem) :
    (ρ 2 theorem4FirstItem).toReal =
      theorem4Problem11PivotOneZ beta v := by
  let q := pairShare (1 / 2) v theorem4FirstItem
  have hxfirst :
      (ρ 0 theorem4FirstItem).toReal = 1 :=
    theorem4Problem11PivotSupport_typeZero_first_toReal_eq_one
      hpivot ht
  have hxrev :
      (ρ 0 (reverseItem theorem4FirstItem)).toReal = 0 :=
    theorem4Problem11PivotSupport_typeZero_reverse_first_toReal_eq_zero
      hn hpivot ht
  have hellambda :
      ell = theorem4Problem11PivotOneLambda beta v :=
    theorem4Problem11PivotOneLambda_eq_of_equalized_pivotSupport
      hpos h hpivot ht
  have hfirst_value :
      2 * beta * q + (1 - 2 * beta) *
          (ρ 2 theorem4FirstItem).toReal = ell := by
    have hitem := h.item_eq theorem4FirstItem
    unfold theorem4Problem11PolicyItemValue theorem4Problem11ItemValue at hitem
    change
      2 * beta *
          (q * (ρ 0 theorem4FirstItem).toReal +
            (1 - q) * (ρ 0 (reverseItem theorem4FirstItem)).toReal) +
        (1 - 2 * beta) * (ρ 2 theorem4FirstItem).toReal = ell at hitem
    rw [hxfirst, hxrev] at hitem
    nlinarith
  have hdelta_ne : 1 - 2 * beta ≠ 0 := by
    nlinarith
  have hz :
      (ρ 2 theorem4FirstItem).toReal =
        (ell - 2 * beta * q) / (1 - 2 * beta) := by
    rw [eq_div_iff hdelta_ne]
    nlinarith
  have hnpos_nat : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hn_ne : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hnpos_nat)
  have hden_eq :
      1 + (1 / 2 : ℝ) * ((n : ℝ) - 2) = (n : ℝ) / 2 := by
    ring
  have hlambda_mul :
      (n : ℝ) * theorem4Problem11PivotOneLambda beta v =
        4 * beta * q + (1 - 2 * beta) := by
    unfold theorem4Problem11PivotOneLambda
    change
      (n : ℝ) *
          ((2 * beta * q + (1 / 2) * (1 - 2 * beta)) /
            (1 + (1 / 2) * ((n : ℝ) - 2))) =
        4 * beta * q + (1 - 2 * beta)
    rw [hden_eq]
    field_simp [hn_ne]
    ring
  rw [hz, hellambda]
  unfold theorem4Problem11PivotOneZ
  field_simp [hdelta_ne]
  nlinarith

/--
Once Lemma 13's pivot is strictly after item `1`, the cold-start row gives zero
probability to both extreme items.
-/
theorem theorem4Problem11PivotSupport_no_extremes_of_first_lt
    {n : ℕ} [NeZero n] {ρ : TypePolicy 3 n} {t : Item n}
    (hpivot : Theorem4Problem11PivotSupport ρ t)
    (hfirst_lt : (theorem4FirstItem : Item n).val < t.val) :
    ρ 2 theorem4FirstItem = 0 ∧ ρ 2 theorem4LastItem = 0 := by
  have hzero := hpivot.2 theorem4FirstItem hfirst_lt
  constructor
  · exact hzero.1
  · simpa [theorem4LastItem] using hzero.2

/--
Appendix E Lemmas 13 and 15 combine to give the no-extreme cold-start
certificate: Lemma 13 supplies the pivot-support shape, and Lemma 15's
closed-form pivot-one coordinate rules out `t = 1`.
-/
theorem theorem4Problem11_no_extremes_of_pivotSupport_of_closedZ
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hn : 2 < n)
    (hbeta : (n : ℝ)⁻¹ < beta)
    (hbeta_half : beta < 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    {ρ : TypePolicy 3 n} {t : Item n}
    (hpivot : Theorem4Problem11PivotSupport ρ t)
    (hclosed_first :
      t = theorem4FirstItem →
        (ρ 2 theorem4FirstItem).toReal =
          theorem4Problem11PivotOneZ beta v) :
    ρ 2 theorem4FirstItem = 0 ∧ ρ 2 theorem4LastItem = 0 := by
  by_cases ht : t = theorem4FirstItem
  · exact False.elim
      (theorem4Problem11PivotOne_closedZ_impossible
        hn hbeta hbeta_half hpos hdec ρ (hclosed_first ht))
  · have hfirst_lt : (theorem4FirstItem : Item n).val < t.val :=
      theorem4FirstItem_val_lt_of_ne ht
    exact theorem4Problem11PivotSupport_no_extremes_of_first_lt
      hpivot hfirst_lt

theorem theorem4Problem11ClosedPolicy_no_extremes {n : ℕ} [NeZero n]
    {beta : ℝ} {v : Item n → ℝ} {t : Item n}
    (hn : 2 < n)
    (hbeta_pos : 0 < beta)
    (hbeta : (n : ℝ)⁻¹ < beta)
    (hbeta_half : beta < 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hleft : t.val ≤ (reverseItem t).val)
    (hpivot : 0 ≤ theorem4Problem11ClosedX beta v t t)
    (hendpoint : 0 ≤ theorem4Problem11ClosedZEndpointMass beta v t) :
    (theorem4Problem11ClosedPolicy beta v t
        hbeta_pos hbeta_half hpos hleft hpivot hendpoint) 2
          theorem4FirstItem = 0 ∧
      (theorem4Problem11ClosedPolicy beta v t
        hbeta_pos hbeta_half hpos hleft hpivot hendpoint) 2
          theorem4LastItem = 0 := by
  let ρ : TypePolicy 3 n :=
    theorem4Problem11ClosedPolicy beta v t
      hbeta_pos hbeta_half hpos hleft hpivot hendpoint
  have hpiv : Theorem4Problem11PivotSupport ρ t := by
    dsimp [ρ]
    exact theorem4Problem11ClosedPolicy_pivotSupport
      hbeta_pos hbeta_half hpos hleft hpivot hendpoint
  exact theorem4Problem11_no_extremes_of_pivotSupport_of_closedZ
    hn hbeta hbeta_half hpos hdec hpiv
    (fun ht => by
      exact theorem4Problem11ClosedPolicy_first_closedZ_eq_pivotOneZ
        (by omega : 1 < n)
        hbeta_pos hbeta_half hpos hleft hpivot hendpoint ht)

theorem theorem4Problem11_no_extremes_of_equalized_pivotSupport
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hn : 2 < n)
    (hbeta : (n : ℝ)⁻¹ < beta)
    (hbeta_half : beta < 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    {ρ : TypePolicy 3 n} {ell : ℝ} {t : Item n}
    (h : Theorem4Problem11EqualizedBasicOptimal beta v ρ ell)
    (hpivot : Theorem4Problem11PivotSupport ρ t) :
    ρ 2 theorem4FirstItem = 0 ∧ ρ 2 theorem4LastItem = 0 := by
  exact theorem4Problem11_no_extremes_of_pivotSupport_of_closedZ
    hn hbeta hbeta_half hpos hdec hpivot
    (fun ht =>
      theorem4Problem11PivotOne_closedZ_of_equalized_pivotSupport
        (by omega : 1 < n) hbeta_half hpos h hpivot ht)

theorem theorem4Problem11_no_extremes_of_equalized_noGap
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hn : 2 < n)
    (hbeta : (n : ℝ)⁻¹ < beta)
    (hbeta_half : beta < 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    {ρ : TypePolicy 3 n} {ell : ℝ}
    (h : Theorem4Problem11EqualizedBasicOptimal beta v ρ ell)
    (hx : Theorem4Problem11TypeZeroZeroClosed ρ)
    (hz : Theorem4Problem11ColdStartPositiveClosed ρ) :
    ρ 2 theorem4FirstItem = 0 ∧ ρ 2 theorem4LastItem = 0 := by
  have hnpos_nat : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  have hbeta_pos : 0 < beta := lt_trans (inv_pos.mpr hnpos) hbeta
  have hpivot :
      Theorem4Problem11PivotSupport ρ
        (theorem4Problem11LastActiveTypeZero ρ) :=
    theorem4Problem11PivotSupport_of_equalizedBasicOptimal_noGap
      hn hbeta_pos hpos hdec h hx hz
  exact theorem4Problem11_no_extremes_of_equalized_pivotSupport
    hn hbeta hbeta_half hpos hdec h hpivot

theorem theorem4Problem11_no_extremes_of_equalized
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hn : 2 < n)
    (hbeta : (n : ℝ)⁻¹ < beta)
    (hbeta_half : beta < 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    {ρ : TypePolicy 3 n} {ell : ℝ}
    (h : Theorem4Problem11EqualizedBasicOptimal beta v ρ ell) :
    ρ 2 theorem4FirstItem = 0 ∧ ρ 2 theorem4LastItem = 0 := by
  have hnpos_nat : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnpos_nat
  have hbeta_pos : 0 < beta := lt_trans (inv_pos.mpr hnpos) hbeta
  have hpivot :
      Theorem4Problem11PivotSupport ρ
        (theorem4Problem11LastActiveTypeZero ρ) :=
    theorem4Problem11PivotSupport_of_equalizedBasicOptimal
      hn hbeta_pos hbeta_half hpos hdec h
  exact theorem4Problem11_no_extremes_of_equalized_pivotSupport
    hn hbeta hbeta_half hpos hdec h hpivot

theorem theorem4NoFairnessPolicyTypeZero_estimated_typeFairness_eq_one
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hpos : ∀ j, 0 < v j) (hdec : StrictlyDecreasingByIndex v) :
    TypeWeightedRecommendationModel.typeFairness
        (theorem4EstimatedReducedModel beta v)
        (theorem4NoFairnessPolicyTypeZero v) = 1 := by
  unfold TypeWeightedRecommendationModel.typeFairness
  apply AppliedModelingLib.finiteMin_eq_of_forall
  intro k
  fin_cases k
  · unfold TypeWeightedRecommendationModel.normalizedTypeUtility
    simp [TypeWeightedRecommendationModel.rawTypeUtility_pure,
      theorem4NoFairnessPolicyTypeZero, theorem4NoFairnessChoiceTypeZero,
      theorem4EstimatedReducedModel_bestItemUtility_zero hdec]
    exact ne_of_gt (hpos theorem4FirstItem)
  · unfold TypeWeightedRecommendationModel.normalizedTypeUtility
    simp [TypeWeightedRecommendationModel.rawTypeUtility_pure,
      theorem4NoFairnessPolicyTypeZero, theorem4NoFairnessChoiceTypeZero,
      theorem4EstimatedReducedModel_bestItemUtility_one hdec, theorem4LastItem]
    rw [reverseItem_reverseItem]
    exact div_self (ne_of_gt (hpos theorem4FirstItem))
  · unfold TypeWeightedRecommendationModel.normalizedTypeUtility
    simp [TypeWeightedRecommendationModel.rawTypeUtility_pure,
      theorem4NoFairnessPolicyTypeZero, theorem4NoFairnessChoiceTypeZero,
      theorem4EstimatedReducedModel_bestItemUtility_two]
    change theorem4AverageUtility v (theorem4BestAverageItemTypeZero v) /
        AppliedModelingLib.finiteMax (theorem4AverageUtility v) = 1
    rw [theorem4AverageUtility_bestAverageItemTypeZero]
    exact div_self
      (ne_of_gt (theorem4AverageUtility_finiteMax_pos hpos))

theorem theorem4NoFairnessPolicyTypeOne_estimated_typeFairness_eq_one
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hpos : ∀ j, 0 < v j) (hdec : StrictlyDecreasingByIndex v) :
    TypeWeightedRecommendationModel.typeFairness
        (theorem4EstimatedReducedModel beta v)
        (theorem4NoFairnessPolicyTypeOne v) = 1 := by
  unfold TypeWeightedRecommendationModel.typeFairness
  apply AppliedModelingLib.finiteMin_eq_of_forall
  intro k
  fin_cases k
  · unfold TypeWeightedRecommendationModel.normalizedTypeUtility
    simp [TypeWeightedRecommendationModel.rawTypeUtility_pure,
      theorem4NoFairnessPolicyTypeOne, theorem4NoFairnessChoiceTypeOne,
      theorem4EstimatedReducedModel_bestItemUtility_zero hdec]
    exact ne_of_gt (hpos theorem4FirstItem)
  · unfold TypeWeightedRecommendationModel.normalizedTypeUtility
    simp [TypeWeightedRecommendationModel.rawTypeUtility_pure,
      theorem4NoFairnessPolicyTypeOne, theorem4NoFairnessChoiceTypeOne,
      theorem4EstimatedReducedModel_bestItemUtility_one hdec, theorem4LastItem]
    rw [reverseItem_reverseItem]
    exact div_self (ne_of_gt (hpos theorem4FirstItem))
  · unfold TypeWeightedRecommendationModel.normalizedTypeUtility
    simp [TypeWeightedRecommendationModel.rawTypeUtility_pure,
      theorem4NoFairnessPolicyTypeOne, theorem4NoFairnessChoiceTypeOne,
      theorem4EstimatedReducedModel_bestItemUtility_two]
    change theorem4AverageUtility v (theorem4BestAverageItemTypeOne v) /
        AppliedModelingLib.finiteMax (theorem4AverageUtility v) = 1
    rw [theorem4AverageUtility_bestAverageItemTypeOne]
    exact div_self
      (ne_of_gt (theorem4AverageUtility_finiteMax_pos hpos))

theorem theorem4NoFairnessPolicyTypeZero_estimated_optimalAtLevel_zero
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hbeta : 0 ≤ beta) (hcold : 0 ≤ 1 - 2 * beta)
    (hpos : ∀ j, 0 < v j) (hdec : StrictlyDecreasingByIndex v) :
    TypeWeightedRecommendationModel.IsOptimalAtLevel
        (theorem4EstimatedReducedModel beta v) 0
        (theorem4NoFairnessPolicyTypeZero v) := by
  refine ⟨?_, ?_⟩
  · exact TypeWeightedRecommendationModel.feasibleAtLevel_zero_of_nonnegative
      (theorem4EstimatedReducedModel beta v)
      (theorem4EstimatedReducedModel_nonnegativeWeights hbeta hcold)
      (theorem4EstimatedReducedModel_nonnegativeUtilities hpos)
      (theorem4NoFairnessPolicyTypeZero v)
  · rw [theorem4NoFairnessPolicyTypeZero_estimated_typeFairness_eq_one
      hpos hdec]
    rw [TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel_zero_eq_one
      (theorem4EstimatedReducedModel beta v)
      (theorem4EstimatedReducedModel_nonnegativeWeights hbeta hcold)
      (theorem4EstimatedReducedModel_nonnegativeUtilities hpos)
      (theorem4EstimatedReducedModel_rowHasPositiveItem hpos)]

theorem theorem4NoFairnessPolicyTypeOne_estimated_optimalAtLevel_zero
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hbeta : 0 ≤ beta) (hcold : 0 ≤ 1 - 2 * beta)
    (hpos : ∀ j, 0 < v j) (hdec : StrictlyDecreasingByIndex v) :
    TypeWeightedRecommendationModel.IsOptimalAtLevel
        (theorem4EstimatedReducedModel beta v) 0
        (theorem4NoFairnessPolicyTypeOne v) := by
  refine ⟨?_, ?_⟩
  · exact TypeWeightedRecommendationModel.feasibleAtLevel_zero_of_nonnegative
      (theorem4EstimatedReducedModel beta v)
      (theorem4EstimatedReducedModel_nonnegativeWeights hbeta hcold)
      (theorem4EstimatedReducedModel_nonnegativeUtilities hpos)
      (theorem4NoFairnessPolicyTypeOne v)
  · rw [theorem4NoFairnessPolicyTypeOne_estimated_typeFairness_eq_one
      hpos hdec]
    rw [TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel_zero_eq_one
      (theorem4EstimatedReducedModel beta v)
      (theorem4EstimatedReducedModel_nonnegativeWeights hbeta hcold)
      (theorem4EstimatedReducedModel_nonnegativeUtilities hpos)
      (theorem4EstimatedReducedModel_rowHasPositiveItem hpos)]

theorem theorem4NoFairnessPolicyCollapsed_estimated_typeFairness_eq_one
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hpos : ∀ j, 0 < v j) (hdec : StrictlyDecreasingByIndex v) :
    TypeWeightedRecommendationModel.typeFairness
        (theorem4EstimatedReducedModel beta v)
        (theorem4NoFairnessPolicyCollapsed v) = 1 := by
  unfold TypeWeightedRecommendationModel.typeFairness
  apply AppliedModelingLib.finiteMin_eq_of_forall
  intro k
  fin_cases k
  · unfold TypeWeightedRecommendationModel.normalizedTypeUtility
      TypeWeightedRecommendationModel.rawTypeUtility AppliedModelingLib.Policy.agentScore
    simp [theorem4NoFairnessPolicyCollapsed,
      theorem4EstimatedReducedModel_bestItemUtility_zero hdec]
    exact ne_of_gt (hpos theorem4FirstItem)
  · unfold TypeWeightedRecommendationModel.normalizedTypeUtility
      TypeWeightedRecommendationModel.rawTypeUtility AppliedModelingLib.Policy.agentScore
    simp [theorem4NoFairnessPolicyCollapsed,
      theorem4EstimatedReducedModel_bestItemUtility_one hdec, theorem4LastItem]
    rw [reverseItem_reverseItem]
    exact div_self (ne_of_gt (hpos theorem4FirstItem))
  · unfold TypeWeightedRecommendationModel.normalizedTypeUtility
      TypeWeightedRecommendationModel.rawTypeUtility AppliedModelingLib.Policy.agentScore
    have h20 : (2 : UserType 3) ≠ 0 := by decide
    have h21 : (2 : UserType 3) ≠ 1 := by decide
    simp [theorem4NoFairnessPolicyCollapsed, h20, h21,
      theorem4EstimatedReducedModel_bestItemUtility_two]
    rw [theorem4NoFairnessColdStartMixedPolicy_agentScore]
    change
      ((theorem4AverageUtility v (theorem4BestAverageItemTypeZero v) +
            theorem4AverageUtility v (theorem4BestAverageItemTypeOne v)) /
          2) /
        AppliedModelingLib.finiteMax (theorem4AverageUtility v) = 1
    rw [theorem4AverageUtility_bestAverageItemTypeZero,
      theorem4AverageUtility_bestAverageItemTypeOne]
    rw [show (AppliedModelingLib.finiteMax (theorem4AverageUtility v) +
          AppliedModelingLib.finiteMax (theorem4AverageUtility v)) / 2 =
        AppliedModelingLib.finiteMax (theorem4AverageUtility v) by ring]
    exact div_self
      (ne_of_gt (theorem4AverageUtility_finiteMax_pos hpos))

theorem theorem4NoFairnessPolicyCollapsed_estimated_optimalAtLevel_zero
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hbeta : 0 ≤ beta) (hcold : 0 ≤ 1 - 2 * beta)
    (hpos : ∀ j, 0 < v j) (hdec : StrictlyDecreasingByIndex v) :
    TypeWeightedRecommendationModel.IsOptimalAtLevel
        (theorem4EstimatedReducedModel beta v) 0
        (theorem4NoFairnessPolicyCollapsed v) := by
  refine ⟨?_, ?_⟩
  · exact TypeWeightedRecommendationModel.feasibleAtLevel_zero_of_nonnegative
      (theorem4EstimatedReducedModel beta v)
      (theorem4EstimatedReducedModel_nonnegativeWeights hbeta hcold)
      (theorem4EstimatedReducedModel_nonnegativeUtilities hpos)
      (theorem4NoFairnessPolicyCollapsed v)
  · rw [theorem4NoFairnessPolicyCollapsed_estimated_typeFairness_eq_one
      hpos hdec]
    rw [TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel_zero_eq_one
      (theorem4EstimatedReducedModel beta v)
      (theorem4EstimatedReducedModel_nonnegativeWeights hbeta hcold)
      (theorem4EstimatedReducedModel_nonnegativeUtilities hpos)
      (theorem4EstimatedReducedModel_rowHasPositiveItem hpos)]

theorem theorem4NoFairnessColdStartMixedPolicy_trueTypeZero_rawUtility_eq
    {n : ℕ} [NeZero n] (v : Item n → ℝ) :
    AppliedModelingLib.pmfExp (theorem4NoFairnessColdStartMixedPolicy v) v =
      AppliedModelingLib.finiteMax (theorem4AverageUtility v) := by
  rw [theorem4NoFairnessColdStartMixedPolicy_agentScore]
  simpa [theorem4BestAverageItemTypeOne, theorem4AverageUtility] using
    theorem4AverageUtility_bestAverageItemTypeZero v

theorem theorem4NoFairnessColdStartMixedPolicy_trueTypeOne_rawUtility_eq
    {n : ℕ} [NeZero n] (v : Item n → ℝ) :
    AppliedModelingLib.pmfExp (theorem4NoFairnessColdStartMixedPolicy v)
        (fun j : Item n => v (reverseItem j)) =
      AppliedModelingLib.finiteMax (theorem4AverageUtility v) := by
  rw [theorem4NoFairnessColdStartMixedPolicy_agentScore]
  unfold theorem4BestAverageItemTypeOne
  rw [reverseItem_reverseItem]
  rw [add_comm]
  simpa [theorem4AverageUtility] using
    theorem4AverageUtility_bestAverageItemTypeZero v

theorem theorem4NoFairnessPolicyCollapsed_trueHalf_normalizedRowUtility_ge_half
    {n : ℕ} [NeZero n] {v : Item n → ℝ}
    (hpos : ∀ j, 0 < v j) (hdec : StrictlyDecreasingByIndex v)
    (kTrue : UserType 2) (kEst : UserType 3)
    (hknown0 : kEst = 0 → kTrue = 0)
    (hknown1 : kEst = 1 → kTrue = 1) :
    (1 / 2 : ℝ) ≤
      AppliedModelingLib.pmfExp ((theorem4NoFairnessPolicyCollapsed v) kEst)
          ((twoTypeReducedModel (1 / 2 : ℝ) v).utility kTrue) /
        TypeWeightedRecommendationModel.bestItemUtility
          (twoTypeReducedModel (1 / 2 : ℝ) v) kTrue := by
  have hbest0 :
      TypeWeightedRecommendationModel.bestItemUtility
          (twoTypeReducedModel (1 / 2 : ℝ) v) 0 =
        v theorem4FirstItem := by
    simpa [TypeWeightedRecommendationModel.bestItemUtility, twoTypeReducedModel]
      using theorem4_finiteMax_eq_first (n := n) (v := v) hdec
  have hbest1 :
      TypeWeightedRecommendationModel.bestItemUtility
          (twoTypeReducedModel (1 / 2 : ℝ) v) 1 =
        v theorem4FirstItem := by
    rw [twoTypeReducedModel_bestItemUtility_one_eq_zero
      (alpha := (1 / 2 : ℝ)) (v := v)]
    exact hbest0
  have hbest0_inv :
      TypeWeightedRecommendationModel.bestItemUtility
          (twoTypeReducedModel ((2 : ℝ)⁻¹) v) 0 =
        v theorem4FirstItem := by
    simpa using hbest0
  have hbest1_inv :
      TypeWeightedRecommendationModel.bestItemUtility
          (twoTypeReducedModel ((2 : ℝ)⁻¹) v) 1 =
        v theorem4FirstItem := by
    simpa using hbest1
  have hraw_cold0 :
      AppliedModelingLib.pmfExp (theorem4NoFairnessColdStartMixedPolicy v)
          ((twoTypeReducedModel ((2 : ℝ)⁻¹) v).utility 0) =
        AppliedModelingLib.finiteMax (theorem4AverageUtility v) := by
    simpa [twoTypeReducedModel] using
      theorem4NoFairnessColdStartMixedPolicy_trueTypeZero_rawUtility_eq v
  have hraw_cold1 :
      AppliedModelingLib.pmfExp (theorem4NoFairnessColdStartMixedPolicy v)
          ((twoTypeReducedModel ((2 : ℝ)⁻¹) v).utility 1) =
        AppliedModelingLib.finiteMax (theorem4AverageUtility v) := by
    simpa [twoTypeReducedModel] using
      theorem4NoFairnessColdStartMixedPolicy_trueTypeOne_rawUtility_eq v
  have hhalf :
      v theorem4FirstItem / 2 <
        AppliedModelingLib.finiteMax (theorem4AverageUtility v) :=
    theorem4AverageUtility_endpoint_half_lt_finiteMax
      (hpos theorem4FirstItem) (hpos theorem4LastItem)
  fin_cases kEst
  · have hkTrue : kTrue = 0 := hknown0 rfl
    subst kTrue
    simp [theorem4NoFairnessPolicyCollapsed]
    rw [hbest0_inv, div_self (ne_of_gt (hpos theorem4FirstItem))]
    norm_num
  · have hkTrue : kTrue = 1 := hknown1 rfl
    subst kTrue
    simp [theorem4NoFairnessPolicyCollapsed, theorem4LastItem]
    rw [reverseItem_reverseItem]
    rw [hbest1_inv, div_self (ne_of_gt (hpos theorem4FirstItem))]
    norm_num
  · have h20 : (2 : UserType 3) ≠ 0 := by decide
    have h21 : (2 : UserType 3) ≠ 1 := by decide
    fin_cases kTrue
    · simp [theorem4NoFairnessPolicyCollapsed, h20, h21]
      rw [hraw_cold0, hbest0_inv]
      rw [le_div_iff₀ (hpos theorem4FirstItem)]
      nlinarith
    · simp [theorem4NoFairnessPolicyCollapsed, h20, h21]
      rw [hraw_cold1, hbest1_inv]
      rw [le_div_iff₀ (hpos theorem4FirstItem)]
      nlinarith

theorem theorem4NoFairnessPolicyTypeZero_true_typeFairness_ge_half
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hpos : ∀ j, 0 < v j) (hdec : StrictlyDecreasingByIndex v) :
    (1 / 2 : ℝ) ≤
      TypeWeightedRecommendationModel.typeFairness
        (theorem4TrueReducedModelTypeZero beta v)
        (theorem4NoFairnessPolicyTypeZero v) := by
  unfold TypeWeightedRecommendationModel.typeFairness
  apply AppliedModelingLib.le_finiteMin
  intro k
  fin_cases k
  · unfold TypeWeightedRecommendationModel.normalizedTypeUtility
    simp [TypeWeightedRecommendationModel.rawTypeUtility_pure,
      theorem4NoFairnessPolicyTypeZero, theorem4NoFairnessChoiceTypeZero,
      theorem4TrueReducedModelTypeZero]
    unfold TypeWeightedRecommendationModel.bestItemUtility
    simp
    rw [theorem4_finiteMax_eq_first hdec]
    rw [div_self (ne_of_gt (hpos theorem4FirstItem))]
    norm_num
  · unfold TypeWeightedRecommendationModel.normalizedTypeUtility
    simp [TypeWeightedRecommendationModel.rawTypeUtility_pure,
      theorem4NoFairnessPolicyTypeZero, theorem4NoFairnessChoiceTypeZero,
      theorem4TrueReducedModelTypeZero, theorem4LastItem]
    rw [reverseItem_reverseItem]
    unfold TypeWeightedRecommendationModel.bestItemUtility
    simp
    rw [finiteMax_reverseItem, theorem4_finiteMax_eq_first hdec]
    rw [div_self (ne_of_gt (hpos theorem4FirstItem))]
    norm_num
  · unfold TypeWeightedRecommendationModel.normalizedTypeUtility
    simp [TypeWeightedRecommendationModel.rawTypeUtility_pure,
      theorem4NoFairnessPolicyTypeZero, theorem4NoFairnessChoiceTypeZero,
      theorem4TrueReducedModelTypeZero]
    have hhalf :
        v theorem4FirstItem / 2 <
          AppliedModelingLib.finiteMax (theorem4AverageUtility v) :=
      theorem4AverageUtility_endpoint_half_lt_finiteMax
        (hpos theorem4FirstItem) (hpos theorem4LastItem)
    have hle_avg :
        AppliedModelingLib.finiteMax (theorem4AverageUtility v) ≤
          v (theorem4BestAverageItemTypeZero v) := by
      rw [← theorem4AverageUtility_bestAverageItemTypeZero v]
      exact theorem4AverageUtility_le_value_bestAverageItemTypeZero v
    have hhalf_value :
        v theorem4FirstItem / 2 <
          v (theorem4BestAverageItemTypeZero v) :=
      lt_of_lt_of_le hhalf hle_avg
    unfold TypeWeightedRecommendationModel.bestItemUtility
    simp
    rw [theorem4_finiteMax_eq_first hdec]
    rw [le_div_iff₀ (hpos theorem4FirstItem)]
    nlinarith

theorem theorem4NoFairnessPolicyTypeOne_true_typeFairness_ge_half
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hpos : ∀ j, 0 < v j) (hdec : StrictlyDecreasingByIndex v) :
    (1 / 2 : ℝ) ≤
      TypeWeightedRecommendationModel.typeFairness
        (theorem4TrueReducedModelTypeOne beta v)
        (theorem4NoFairnessPolicyTypeOne v) := by
  unfold TypeWeightedRecommendationModel.typeFairness
  apply AppliedModelingLib.le_finiteMin
  intro k
  fin_cases k
  · unfold TypeWeightedRecommendationModel.normalizedTypeUtility
    simp [TypeWeightedRecommendationModel.rawTypeUtility_pure,
      theorem4NoFairnessPolicyTypeOne, theorem4NoFairnessChoiceTypeOne,
      theorem4TrueReducedModelTypeOne]
    unfold TypeWeightedRecommendationModel.bestItemUtility
    simp
    rw [theorem4_finiteMax_eq_first hdec]
    rw [div_self (ne_of_gt (hpos theorem4FirstItem))]
    norm_num
  · unfold TypeWeightedRecommendationModel.normalizedTypeUtility
    simp [TypeWeightedRecommendationModel.rawTypeUtility_pure,
      theorem4NoFairnessPolicyTypeOne, theorem4NoFairnessChoiceTypeOne,
      theorem4TrueReducedModelTypeOne, theorem4LastItem]
    rw [reverseItem_reverseItem]
    unfold TypeWeightedRecommendationModel.bestItemUtility
    simp
    rw [finiteMax_reverseItem, theorem4_finiteMax_eq_first hdec]
    rw [div_self (ne_of_gt (hpos theorem4FirstItem))]
    norm_num
  · unfold TypeWeightedRecommendationModel.normalizedTypeUtility
    simp [TypeWeightedRecommendationModel.rawTypeUtility_pure,
      theorem4NoFairnessPolicyTypeOne, theorem4NoFairnessChoiceTypeOne,
      theorem4TrueReducedModelTypeOne]
    have hhalf :
        v theorem4FirstItem / 2 <
          AppliedModelingLib.finiteMax (theorem4AverageUtility v) :=
      theorem4AverageUtility_endpoint_half_lt_finiteMax
        (hpos theorem4FirstItem) (hpos theorem4LastItem)
    have hle_avg :
        AppliedModelingLib.finiteMax (theorem4AverageUtility v) ≤
          v (reverseItem (theorem4BestAverageItemTypeOne v)) := by
      rw [← theorem4AverageUtility_bestAverageItemTypeOne v]
      exact theorem4AverageUtility_le_reverse_value_bestAverageItemTypeOne v
    have hhalf_value :
        v theorem4FirstItem / 2 <
          v (reverseItem (theorem4BestAverageItemTypeOne v)) :=
      lt_of_lt_of_le hhalf hle_avg
    unfold TypeWeightedRecommendationModel.bestItemUtility
    simp
    rw [finiteMax_reverseItem, theorem4_finiteMax_eq_first hdec]
    rw [le_div_iff₀ (hpos theorem4FirstItem)]
    nlinarith

/--
Appendix E, Theorem 4 utility bound for a cold-start user of the first true
type: if the estimated optimum gives the cold-start row no probability on item
`1`, and `v₂` is below `eps/n` times `v₁`, then this user's normalized utility
is below `eps/n`.
-/
theorem paper_theorem4_coldStart_typeZero_normalizedUtility_lt
    {n : ℕ} [NeZero n] {beta eps : ℝ} {v : Item n → ℝ}
    (hn : 1 < n)
    (hdec : StrictlyDecreasingByIndex v)
    (hfirst_pos : 0 < v theorem4FirstItem)
    (hsmall : v (theorem4SecondItem hn) <
      eps / (n : ℝ) * v theorem4FirstItem)
    (ρ : TypePolicy 3 n)
    (hno_first : ρ 2 theorem4FirstItem = 0) :
    TypeWeightedRecommendationModel.normalizedTypeUtility
        (theorem4TrueReducedModelTypeZero beta v) ρ 2 <
      eps / (n : ℝ) := by
  have hraw :
      TypeWeightedRecommendationModel.rawTypeUtility
          (theorem4TrueReducedModelTypeZero beta v) ρ 2 <
        eps / (n : ℝ) * v theorem4FirstItem := by
    unfold TypeWeightedRecommendationModel.rawTypeUtility
      AppliedModelingLib.Policy.agentScore
    change AppliedModelingLib.pmfExp (ρ 2) (fun j : Item n => v j) <
      eps / (n : ℝ) * v theorem4FirstItem
    refine AppliedModelingLib.pmfExp_lt_of_support_forall_lt
      (ρ 2) v (eps / (n : ℝ) * v theorem4FirstItem) ?_
    intro j hmass
    have hj_ne : j ≠ theorem4FirstItem := by
      intro hj
      subst j
      have hmass_zero : ((ρ 2 theorem4FirstItem).toReal) = 0 := by
        simpa [hno_first]
      linarith
    exact lt_of_le_of_lt
      (theorem4_value_le_second_of_ne_first hn hdec hj_ne) hsmall
  unfold TypeWeightedRecommendationModel.normalizedTypeUtility
  rw [theorem4TrueReducedModelTypeZero_bestItemUtility_two hdec]
  rw [div_lt_iff₀ hfirst_pos]
  exact hraw

/--
Appendix E, Theorem 4 utility bound for a cold-start user of the second true
type: if the estimated optimum gives the cold-start row no probability on item
`n`, and `v₂` is below `eps/n` times `v₁`, then this user's normalized utility
is below `eps/n`.
-/
theorem paper_theorem4_coldStart_typeOne_normalizedUtility_lt
    {n : ℕ} [NeZero n] {beta eps : ℝ} {v : Item n → ℝ}
    (hn : 1 < n)
    (hdec : StrictlyDecreasingByIndex v)
    (hfirst_pos : 0 < v theorem4FirstItem)
    (hsmall : v (theorem4SecondItem hn) <
      eps / (n : ℝ) * v theorem4FirstItem)
    (ρ : TypePolicy 3 n)
    (hno_last : ρ 2 theorem4LastItem = 0) :
    TypeWeightedRecommendationModel.normalizedTypeUtility
        (theorem4TrueReducedModelTypeOne beta v) ρ 2 <
      eps / (n : ℝ) := by
  have hraw :
      TypeWeightedRecommendationModel.rawTypeUtility
          (theorem4TrueReducedModelTypeOne beta v) ρ 2 <
        eps / (n : ℝ) * v theorem4FirstItem := by
    unfold TypeWeightedRecommendationModel.rawTypeUtility
      AppliedModelingLib.Policy.agentScore
    change AppliedModelingLib.pmfExp (ρ 2)
        (fun j : Item n => v (reverseItem j)) <
      eps / (n : ℝ) * v theorem4FirstItem
    refine AppliedModelingLib.pmfExp_lt_of_support_forall_lt
      (ρ 2) (fun j : Item n => v (reverseItem j))
      (eps / (n : ℝ) * v theorem4FirstItem) ?_
    intro j hmass
    have hj_ne_last : j ≠ theorem4LastItem := by
      intro hj
      subst j
      have hmass_zero : ((ρ 2 theorem4LastItem).toReal) = 0 := by
        simpa [hno_last]
      linarith
    have hrev_ne_first : reverseItem j ≠ theorem4FirstItem := by
      intro hrev
      have hj_last : j = theorem4LastItem := by
        have h := congrArg reverseItem hrev
        simpa [theorem4LastItem, reverseItem_reverseItem] using h
      exact hj_ne_last hj_last
    exact lt_of_le_of_lt
      (theorem4_value_le_second_of_ne_first hn hdec hrev_ne_first)
      hsmall
  unfold TypeWeightedRecommendationModel.normalizedTypeUtility
  rw [theorem4TrueReducedModelTypeOne_bestItemUtility_two hdec]
  rw [div_lt_iff₀ hfirst_pos]
  exact hraw

theorem paper_theorem4_coldStart_typeZero_typeFairness_lt
    {n : ℕ} [NeZero n] {beta eps : ℝ} {v : Item n → ℝ}
    (hn : 1 < n)
    (hdec : StrictlyDecreasingByIndex v)
    (hfirst_pos : 0 < v theorem4FirstItem)
    (hsmall : v (theorem4SecondItem hn) <
      eps / (n : ℝ) * v theorem4FirstItem)
    (ρ : TypePolicy 3 n)
    (hno_first : ρ 2 theorem4FirstItem = 0) :
    TypeWeightedRecommendationModel.typeFairness
        (theorem4TrueReducedModelTypeZero beta v) ρ <
      eps / (n : ℝ) := by
  exact lt_of_le_of_lt
    (AppliedModelingLib.finiteMin_le
      (TypeWeightedRecommendationModel.normalizedTypeUtility
        (theorem4TrueReducedModelTypeZero beta v) ρ) 2)
    (paper_theorem4_coldStart_typeZero_normalizedUtility_lt
      hn hdec hfirst_pos hsmall ρ hno_first)

theorem paper_theorem4_coldStart_typeOne_typeFairness_lt
    {n : ℕ} [NeZero n] {beta eps : ℝ} {v : Item n → ℝ}
    (hn : 1 < n)
    (hdec : StrictlyDecreasingByIndex v)
    (hfirst_pos : 0 < v theorem4FirstItem)
    (hsmall : v (theorem4SecondItem hn) <
      eps / (n : ℝ) * v theorem4FirstItem)
    (ρ : TypePolicy 3 n)
    (hno_last : ρ 2 theorem4LastItem = 0) :
    TypeWeightedRecommendationModel.typeFairness
        (theorem4TrueReducedModelTypeOne beta v) ρ <
      eps / (n : ℝ) := by
  exact lt_of_le_of_lt
    (AppliedModelingLib.finiteMin_le
      (TypeWeightedRecommendationModel.normalizedTypeUtility
        (theorem4TrueReducedModelTypeOne beta v) ρ) 2)
    (paper_theorem4_coldStart_typeOne_normalizedUtility_lt
      hn hdec hfirst_pos hsmall ρ hno_last)

end OpposingTypes

namespace EstimatedRecommendationModel

theorem liftedPolicy_eq_of_typeAssignment_eq
    {m n K : ℕ}
    (R R' : ReductionWitness m n K)
    (htypes : R.data.types = R'.data.types)
    (ρ : TypePolicy K n) :
    R.liftedPolicy ρ = R'.liftedPolicy ρ := by
  funext u
  simp [ReductionWitness.liftedPolicy, htypes]

/--
Estimated-problem lift bridge: a reduced optimum for a reduction witness of
the estimated model solves the original estimated problem after lifting.
-/
theorem solvesEstimatedProblem_liftedPolicy_of_reduced
    {m n K : ℕ} [NeZero m] [NeZero n] [NeZero K]
    (E : EstimatedRecommendationModel m n)
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    {γ : ℝ} {ρ : TypePolicy K n}
    (hestimated : E.estimatedModel = R.data.model)
    (hrow : R.data.model.RowHasPositiveItem)
    (hopt : TypeWeightedRecommendationModel.IsOptimalAtLevel
      R.reduced γ ρ) :
    E.SolvesEstimatedProblem γ (R.liftedPolicy ρ) := by
  unfold SolvesEstimatedProblem
  rw [hestimated]
  exact R.isOptimalAtLevel_liftedPolicy_of_reduced_auto_nonempty
    reps hrow γ ρ hopt

/--
Same bridge when the policy is displayed using a second reduction witness with
the same user-type assignment, as in Theorem 4's true/estimated pair.
-/
theorem solvesEstimatedProblem_liftedPolicy_of_reduced_typeAssignment_eq
    {m n K : ℕ} [NeZero m] [NeZero n] [NeZero K]
    (E : EstimatedRecommendationModel m n)
    (Rest Rout : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives Rest.data.types)
    {γ : ℝ} {ρ : TypePolicy K n}
    (hestimated : E.estimatedModel = Rest.data.model)
    (htypes : Rest.data.types = Rout.data.types)
    (hrow : Rest.data.model.RowHasPositiveItem)
    (hopt : TypeWeightedRecommendationModel.IsOptimalAtLevel
      Rest.reduced γ ρ) :
    E.SolvesEstimatedProblem γ (Rout.liftedPolicy ρ) := by
  have hsolve :=
    E.solvesEstimatedProblem_liftedPolicy_of_reduced
      Rest reps hestimated hrow hopt
  have hlift : Rest.liftedPolicy ρ = Rout.liftedPolicy ρ :=
    liftedPolicy_eq_of_typeAssignment_eq Rest Rout htypes ρ
  simpa [hlift] using hsolve

private theorem theorem4_estimatedModel_original_rowHasPositiveItem_of_reduction
    {m n : ℕ} [NeZero n]
    (R : ReductionWitness m n 3)
    {beta : ℝ} {v : Item n → ℝ}
    (hred :
      R.reduced = OpposingTypes.theorem4EstimatedReducedModel beta v)
    (hpos : ∀ j : Item n, 0 < v j) :
    R.data.model.RowHasPositiveItem := by
  intro u
  refine ⟨OpposingTypes.theorem4FirstItem, ?_⟩
  rw [R.utility_agrees u OpposingTypes.theorem4FirstItem, hred]
  let k : UserType 3 := R.data.types.toType u
  change 0 <
    (OpposingTypes.theorem4EstimatedReducedModel beta v).utility k
      OpposingTypes.theorem4FirstItem
  by_cases hk0 : k = 0
  · simp [OpposingTypes.theorem4EstimatedReducedModel, hk0,
      hpos OpposingTypes.theorem4FirstItem]
  · by_cases hk1 : k = 1
    · simp [OpposingTypes.theorem4EstimatedReducedModel, hk1,
        hpos (OpposingTypes.reverseItem OpposingTypes.theorem4FirstItem)]
    · simp [OpposingTypes.theorem4EstimatedReducedModel, hk0, hk1]
      nlinarith [hpos OpposingTypes.theorem4FirstItem,
        hpos (OpposingTypes.reverseItem OpposingTypes.theorem4FirstItem)]

/--
Theorem 4 estimated-model packaging: any reduced optimum for the Appendix E
estimated three-type model lifts to a policy solving the original estimated
problem.
-/
theorem theorem4_solvesEstimatedProblem_from_estimated_reduction
    {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n)
    (R : ReductionWitness m n 3)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    {beta γ : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 3 n}
    (hestimated : E.estimatedModel = R.data.model)
    (hred :
      R.reduced = OpposingTypes.theorem4EstimatedReducedModel beta v)
    (hpos : ∀ j : Item n, 0 < v j)
    (hopt : TypeWeightedRecommendationModel.IsOptimalAtLevel
      (OpposingTypes.theorem4EstimatedReducedModel beta v) γ ρ) :
    E.SolvesEstimatedProblem γ (R.liftedPolicy ρ) := by
  have hoptR :
      TypeWeightedRecommendationModel.IsOptimalAtLevel R.reduced γ ρ := by
    simpa [hred] using hopt
  exact E.solvesEstimatedProblem_liftedPolicy_of_reduced
    R reps hestimated
    (theorem4_estimatedModel_original_rowHasPositiveItem_of_reduction
      R hred hpos)
    hoptR

theorem theorem4_solvesEstimatedProblem_from_estimated_reduction_typeAssignment_eq
    {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n)
    (Rest Rout : ReductionWitness m n 3)
    (reps : UserTypeAssignment.TypeRepresentatives Rest.data.types)
    {beta γ : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 3 n}
    (hestimated : E.estimatedModel = Rest.data.model)
    (htypes : Rest.data.types = Rout.data.types)
    (hred :
      Rest.reduced = OpposingTypes.theorem4EstimatedReducedModel beta v)
    (hpos : ∀ j : Item n, 0 < v j)
    (hopt : TypeWeightedRecommendationModel.IsOptimalAtLevel
      (OpposingTypes.theorem4EstimatedReducedModel beta v) γ ρ) :
    E.SolvesEstimatedProblem γ (Rout.liftedPolicy ρ) := by
  have hoptR :
      TypeWeightedRecommendationModel.IsOptimalAtLevel Rest.reduced γ ρ := by
    simpa [hred] using hopt
  exact E.solvesEstimatedProblem_liftedPolicy_of_reduced_typeAssignment_eq
    Rest Rout reps hestimated htypes
    (theorem4_estimatedModel_original_rowHasPositiveItem_of_reduction
      Rest hred hpos)
    hoptR

/--
The no-fairness first-row policy solves the original estimated problem at
`γ = 0` after lifting through the estimated reduction witness.
-/
theorem theorem4_noFairnessPolicyTypeZero_solvesEstimatedProblem_zero_from_reduction
    {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n)
    (R : ReductionWitness m n 3)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    {beta : ℝ} {v : Item n → ℝ}
    (hestimated : E.estimatedModel = R.data.model)
    (hred :
      R.reduced = OpposingTypes.theorem4EstimatedReducedModel beta v)
    (hbeta : 0 ≤ beta) (hcold : 0 ≤ 1 - 2 * beta)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : OpposingTypes.StrictlyDecreasingByIndex v) :
    E.SolvesEstimatedProblem 0
      (R.liftedPolicy (OpposingTypes.theorem4NoFairnessPolicyTypeZero v)) := by
  exact E.theorem4_solvesEstimatedProblem_from_estimated_reduction
    R reps hestimated hred hpos
    (OpposingTypes.theorem4NoFairnessPolicyTypeZero_estimated_optimalAtLevel_zero
      hbeta hcold hpos hdec)

/--
The no-fairness second-row policy solves the original estimated problem at
`γ = 0` after lifting through the estimated reduction witness.
-/
theorem theorem4_noFairnessPolicyTypeOne_solvesEstimatedProblem_zero_from_reduction
    {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n)
    (R : ReductionWitness m n 3)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    {beta : ℝ} {v : Item n → ℝ}
    (hestimated : E.estimatedModel = R.data.model)
    (hred :
      R.reduced = OpposingTypes.theorem4EstimatedReducedModel beta v)
    (hbeta : 0 ≤ beta) (hcold : 0 ≤ 1 - 2 * beta)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : OpposingTypes.StrictlyDecreasingByIndex v) :
    E.SolvesEstimatedProblem 0
      (R.liftedPolicy (OpposingTypes.theorem4NoFairnessPolicyTypeOne v)) := by
  exact E.theorem4_solvesEstimatedProblem_from_estimated_reduction
    R reps hestimated hred hpos
    (OpposingTypes.theorem4NoFairnessPolicyTypeOne_estimated_optimalAtLevel_zero
      hbeta hcold hpos hdec)

/--
Appendix E Problem 11 packaging: a selected equality-form optimum solving the
reduced estimated `γ = 1` problem also solves the original estimated problem.
-/
theorem theorem4_problem11EqualizedBasicOptimal_solvesEstimatedProblem_one_from_reduction
    {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n)
    (R : ReductionWitness m n 3)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    {beta : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 3 n} {ell : ℝ}
    (hn : 2 < n)
    (hestimated : E.estimatedModel = R.data.model)
    (hred :
      R.reduced = OpposingTypes.theorem4EstimatedReducedModel beta v)
    (hbeta_pos : 0 < beta) (hbeta_half : beta < 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : OpposingTypes.StrictlyDecreasingByIndex v)
    (h :
      OpposingTypes.Theorem4Problem11EqualizedBasicOptimal beta v ρ ell)
    (hselection :
      ∀ (ρ' : TypePolicy 3 n) (ell' : ℝ),
        OpposingTypes.Theorem4Problem11PolicyOptimal beta v ρ' ell' →
          OpposingTypes.Theorem4Problem11EqualizedBasicOptimal beta v ρ' ell') :
    E.SolvesEstimatedProblem 1 (R.liftedPolicy ρ) := by
  have hopt :
      TypeWeightedRecommendationModel.IsOptimalAtLevel
        (OpposingTypes.theorem4EstimatedReducedModel beta v) 1 ρ :=
    OpposingTypes.theorem4Problem11EqualizedBasicOptimal_isOptimalAtLevel_of_equalized_selection
      hn hbeta_pos hbeta_half hpos hdec h hselection
  exact E.theorem4_solvesEstimatedProblem_from_estimated_reduction
    R reps hestimated hred hpos hopt

/--
Same Problem 11 packaging after rebuilding the selected policy from real
equality-form BFS data.
-/
theorem theorem4_problem11EqualityFormOptimalBFS_solvesEstimatedProblem_one_from_reduction
    {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n)
    (R : ReductionWitness m n 3)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    {beta : ℝ} {v x z : Item n → ℝ} {ell : ℝ}
    (hn : 2 < n)
    (hestimated : E.estimatedModel = R.data.model)
    (hred :
      R.reduced = OpposingTypes.theorem4EstimatedReducedModel beta v)
    (hbeta_pos : 0 < beta) (hbeta_half : beta < 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : OpposingTypes.StrictlyDecreasingByIndex v)
    (h :
      OpposingTypes.Theorem4Problem11EqualityFormOptimalBFS beta v x z ell)
    (hselection :
      ∀ (ρ' : TypePolicy 3 n) (ell' : ℝ),
        OpposingTypes.Theorem4Problem11PolicyOptimal beta v ρ' ell' →
          OpposingTypes.Theorem4Problem11EqualizedBasicOptimal beta v ρ' ell') :
    E.SolvesEstimatedProblem 1
      (R.liftedPolicy
        (OpposingTypes.theorem4Problem11PolicyOfRealVectors x z
          h.feasible.x_nonneg h.feasible.z_nonneg
          h.feasible.sum_x h.feasible.sum_z)) := by
  have hopt :
      TypeWeightedRecommendationModel.IsOptimalAtLevel
        (OpposingTypes.theorem4EstimatedReducedModel beta v) 1
        (OpposingTypes.theorem4Problem11PolicyOfRealVectors x z
          h.feasible.x_nonneg h.feasible.z_nonneg
          h.feasible.sum_x h.feasible.sum_z) :=
    OpposingTypes.theorem4Problem11EqualityFormOptimalBFS_isOptimalAtLevel_of_equalized_selection
      hn hbeta_pos hbeta_half hpos hdec h hselection
  exact E.theorem4_solvesEstimatedProblem_from_estimated_reduction
    R reps hestimated hred hpos hopt

/--
Problem 11 estimated-problem packaging using the paper's Lemma 14 shape
directly: uniqueness of the epigraph-optimal mirror-symmetric policy is enough
to show the selected equalized optimum solves the estimated `γ = 1` problem.
-/
theorem theorem4_problem11EqualizedBasicOptimal_solvesEstimatedProblem_one_from_reduction_of_policyOptimal_unique
    {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n)
    (R : ReductionWitness m n 3)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    {beta : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 3 n} {ell : ℝ}
    (hestimated : E.estimatedModel = R.data.model)
    (hred :
      R.reduced = OpposingTypes.theorem4EstimatedReducedModel beta v)
    (hbeta : 0 ≤ beta) (hcold : 0 ≤ 1 - 2 * beta)
    (hpos : ∀ j : Item n, 0 < v j)
    (h :
      OpposingTypes.Theorem4Problem11EqualizedBasicOptimal beta v ρ ell)
    (hunique :
      ∀ (ρ' : TypePolicy 3 n) (ell' : ℝ),
        OpposingTypes.Theorem4Problem11PolicyOptimal beta v ρ' ell' →
          ρ' = ρ) :
    E.SolvesEstimatedProblem 1 (R.liftedPolicy ρ) := by
  have hopt :
      TypeWeightedRecommendationModel.IsOptimalAtLevel
        (OpposingTypes.theorem4EstimatedReducedModel beta v) 1 ρ :=
    OpposingTypes.theorem4Problem11EqualizedBasicOptimal_isOptimalAtLevel_of_policyOptimal_unique
      hbeta hcold hpos h hunique
  exact E.theorem4_solvesEstimatedProblem_from_estimated_reduction
    R reps hestimated hred hpos hopt

/--
Same uniqueness-based estimated-problem bridge after rebuilding the selected
policy from real equality-form BFS data.
-/
theorem theorem4_problem11EqualityFormOptimalBFS_solvesEstimatedProblem_one_from_reduction_of_policyOptimal_unique
    {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n)
    (R : ReductionWitness m n 3)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    {beta : ℝ} {v x z : Item n → ℝ} {ell : ℝ}
    (hestimated : E.estimatedModel = R.data.model)
    (hred :
      R.reduced = OpposingTypes.theorem4EstimatedReducedModel beta v)
    (hbeta : 0 ≤ beta) (hcold : 0 ≤ 1 - 2 * beta)
    (hpos : ∀ j : Item n, 0 < v j)
    (h :
      OpposingTypes.Theorem4Problem11EqualityFormOptimalBFS beta v x z ell)
    (hunique :
      ∀ (ρ' : TypePolicy 3 n) (ell' : ℝ),
        OpposingTypes.Theorem4Problem11PolicyOptimal beta v ρ' ell' →
          ρ' =
            OpposingTypes.theorem4Problem11PolicyOfRealVectors x z
              h.feasible.x_nonneg h.feasible.z_nonneg
              h.feasible.sum_x h.feasible.sum_z) :
    E.SolvesEstimatedProblem 1
      (R.liftedPolicy
        (OpposingTypes.theorem4Problem11PolicyOfRealVectors x z
          h.feasible.x_nonneg h.feasible.z_nonneg
          h.feasible.sum_x h.feasible.sum_z)) := by
  let ρ : TypePolicy 3 n :=
    OpposingTypes.theorem4Problem11PolicyOfRealVectors x z
      h.feasible.x_nonneg h.feasible.z_nonneg
      h.feasible.sum_x h.feasible.sum_z
  have heq :
      OpposingTypes.Theorem4Problem11EqualizedBasicOptimal beta v ρ ell := by
    dsimp [ρ]
    exact OpposingTypes.theorem4Problem11EqualizedBasicOptimal_of_equalityFormOptimalBFS
      h
  change E.SolvesEstimatedProblem 1 (R.liftedPolicy ρ)
  exact E.theorem4_problem11EqualizedBasicOptimal_solvesEstimatedProblem_one_from_reduction_of_policyOptimal_unique
    R reps hestimated hred hbeta hcold hpos heq
    (by
      intro ρ' ell' hopt'
      dsimp [ρ]
      exact hunique ρ' ell' hopt')

private theorem theorem4_trueModelTypeZero_original_nonnegative_of_reduction
    {m n : ℕ} [NeZero n]
    (R : ReductionWitness m n 3)
    {beta : ℝ} {v : Item n → ℝ}
    (hred :
      R.reduced = OpposingTypes.theorem4TrueReducedModelTypeZero beta v)
    (hpos : ∀ j : Item n, 0 < v j) :
    R.data.model.Nonnegative := by
  intro u j
  rw [R.utility_agrees u j, hred]
  let k : UserType 3 := R.data.types.toType u
  change 0 ≤ (OpposingTypes.theorem4TrueReducedModelTypeZero beta v).utility k j
  by_cases hk0 : k = 0
  · simp [OpposingTypes.theorem4TrueReducedModelTypeZero, hk0, (hpos j).le]
  · by_cases hk1 : k = 1
    · simp [OpposingTypes.theorem4TrueReducedModelTypeZero, hk1,
        (hpos (OpposingTypes.reverseItem j)).le]
    · simp [OpposingTypes.theorem4TrueReducedModelTypeZero, hk0, hk1,
        (hpos j).le]

private theorem theorem4_trueModelTypeOne_original_nonnegative_of_reduction
    {m n : ℕ} [NeZero n]
    (R : ReductionWitness m n 3)
    {beta : ℝ} {v : Item n → ℝ}
    (hred :
      R.reduced = OpposingTypes.theorem4TrueReducedModelTypeOne beta v)
    (hpos : ∀ j : Item n, 0 < v j) :
    R.data.model.Nonnegative := by
  intro u j
  rw [R.utility_agrees u j, hred]
  let k : UserType 3 := R.data.types.toType u
  change 0 ≤ (OpposingTypes.theorem4TrueReducedModelTypeOne beta v).utility k j
  by_cases hk0 : k = 0
  · simp [OpposingTypes.theorem4TrueReducedModelTypeOne, hk0, (hpos j).le]
  · simp [OpposingTypes.theorem4TrueReducedModelTypeOne, hk0,
      (hpos (OpposingTypes.reverseItem j)).le]

private theorem theorem4_trueModelTypeZero_original_rowHasPositiveItem_of_reduction
    {m n : ℕ} [NeZero n]
    (R : ReductionWitness m n 3)
    {beta : ℝ} {v : Item n → ℝ}
    (hred :
      R.reduced = OpposingTypes.theorem4TrueReducedModelTypeZero beta v)
    (hpos : ∀ j : Item n, 0 < v j) :
    R.data.model.RowHasPositiveItem := by
  intro u
  refine ⟨OpposingTypes.theorem4FirstItem, ?_⟩
  rw [R.utility_agrees u OpposingTypes.theorem4FirstItem, hred]
  let k : UserType 3 := R.data.types.toType u
  change 0 <
    (OpposingTypes.theorem4TrueReducedModelTypeZero beta v).utility k
      OpposingTypes.theorem4FirstItem
  by_cases hk0 : k = 0
  · simp [OpposingTypes.theorem4TrueReducedModelTypeZero, hk0,
      hpos OpposingTypes.theorem4FirstItem]
  · by_cases hk1 : k = 1
    · simp [OpposingTypes.theorem4TrueReducedModelTypeZero, hk1,
        hpos (OpposingTypes.reverseItem OpposingTypes.theorem4FirstItem)]
    · simp [OpposingTypes.theorem4TrueReducedModelTypeZero, hk0, hk1,
        hpos OpposingTypes.theorem4FirstItem]

private theorem theorem4_trueModelTypeOne_original_rowHasPositiveItem_of_reduction
    {m n : ℕ} [NeZero n]
    (R : ReductionWitness m n 3)
    {beta : ℝ} {v : Item n → ℝ}
    (hred :
      R.reduced = OpposingTypes.theorem4TrueReducedModelTypeOne beta v)
    (hpos : ∀ j : Item n, 0 < v j) :
    R.data.model.RowHasPositiveItem := by
  intro u
  refine ⟨OpposingTypes.theorem4FirstItem, ?_⟩
  rw [R.utility_agrees u OpposingTypes.theorem4FirstItem, hred]
  let k : UserType 3 := R.data.types.toType u
  change 0 <
    (OpposingTypes.theorem4TrueReducedModelTypeOne beta v).utility k
      OpposingTypes.theorem4FirstItem
  by_cases hk0 : k = 0
  · simp [OpposingTypes.theorem4TrueReducedModelTypeOne, hk0,
      hpos OpposingTypes.theorem4FirstItem]
  · simp [OpposingTypes.theorem4TrueReducedModelTypeOne, hk0,
      hpos (OpposingTypes.reverseItem OpposingTypes.theorem4FirstItem)]

private theorem theorem4_trueHalf_original_rowHasPositiveItem_of_reduction
    {m n : ℕ} [NeZero n]
    (R : ReductionWitness m n 2)
    {v : Item n → ℝ}
    (hred :
      R.reduced = OpposingTypes.twoTypeReducedModel (1 / 2 : ℝ) v)
    (hpos : ∀ j : Item n, 0 < v j) :
    R.data.model.RowHasPositiveItem := by
  intro u
  refine ⟨OpposingTypes.theorem4FirstItem, ?_⟩
  rw [R.utility_agrees u OpposingTypes.theorem4FirstItem, hred]
  let k : UserType 2 := R.data.types.toType u
  change 0 <
    (OpposingTypes.twoTypeReducedModel (1 / 2 : ℝ) v).utility k
      OpposingTypes.theorem4FirstItem
  by_cases hk0 : k = 0
  · simp [OpposingTypes.twoTypeReducedModel, hk0,
      hpos OpposingTypes.theorem4FirstItem]
  · simp [OpposingTypes.twoTypeReducedModel, hk0,
      hpos (OpposingTypes.reverseItem OpposingTypes.theorem4FirstItem)]

private theorem theorem4_trueHalf_original_nonnegative_of_reduction
    {m n : ℕ} [NeZero n]
    (R : ReductionWitness m n 2)
    {v : Item n → ℝ}
    (hred :
      R.reduced = OpposingTypes.twoTypeReducedModel (1 / 2 : ℝ) v)
    (hpos : ∀ j : Item n, 0 < v j) :
    R.data.model.Nonnegative := by
  intro u j
  rw [R.utility_agrees u j, hred]
  let k : UserType 2 := R.data.types.toType u
  change 0 ≤ (OpposingTypes.twoTypeReducedModel (1 / 2 : ℝ) v).utility k j
  by_cases hk0 : k = 0
  · simp [OpposingTypes.twoTypeReducedModel, hk0, (hpos j).le]
  · simp [OpposingTypes.twoTypeReducedModel, hk0,
      (hpos (OpposingTypes.reverseItem j)).le]

/--
Theorem 4 true-model baseline, odd midpoint case, lifted from the two-type
half-population reduced model to the original true model.
-/
theorem theorem4_trueModel_original_optimalUserFairnessAtLevel_one_gt_inv_card_half_center
    {m n : ℕ} [NeZero m] [NeZero n]
    (R : ReductionWitness m n 2)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    {v : Item n → ℝ} {c : Item n}
    (hn : 1 < n)
    (hred :
      R.reduced = OpposingTypes.twoTypeReducedModel (1 / 2 : ℝ) v)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : OpposingTypes.StrictlyDecreasingByIndex v)
    (hcenter : c.val = (OpposingTypes.reverseItem c).val) :
    (n : ℝ)⁻¹ <
      RecommendationModel.optimalUserFairnessAtLevel R.data.model 1 := by
  have hrow : R.data.model.RowHasPositiveItem :=
    theorem4_trueHalf_original_rowHasPositiveItem_of_reduction R hred hpos
  rcases OpposingTypes.problem6EqualizedBasicOptimal_feasibleAtLevel_one_exists
      (alpha := (1 / 2 : ℝ)) (v := v)
      (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) hpos hdec with
    ⟨ρ, _ell, _hclosed, hfeasTwo⟩
  have hfeasR :
      TypeWeightedRecommendationModel.feasibleAtLevel R.reduced 1 ρ := by
    simpa [hred] using hfeasTwo
  have hRedNonempty :
      (TypeWeightedRecommendationModel.attainableTypeFairnessAtLevel
        R.reduced 1).Nonempty := by
    exact ⟨TypeWeightedRecommendationModel.typeFairness R.reduced ρ,
      ⟨ρ, hfeasR, rfl⟩⟩
  have hOrigFeas :
      RecommendationModel.feasibleAtLevel R.data.model 1
        (R.liftedPolicy ρ) := by
    unfold RecommendationModel.feasibleAtLevel
    rw [R.optimalItemFairness_eq_reduced reps]
    rw [R.itemFairness_liftedPolicy_eq_itemFairness ρ]
    exact hfeasR
  have hOrigNonempty :
      (RecommendationModel.attainableUserFairnessAtLevel
        R.data.model 1).Nonempty := by
    exact ⟨RecommendationModel.userFairness R.data.model (R.liftedPolicy ρ),
      ⟨R.liftedPolicy ρ, hOrigFeas, rfl⟩⟩
  have heq :
      RecommendationModel.optimalUserFairnessAtLevel R.data.model 1 =
        TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
          R.reduced 1 :=
    R.optimalUserFairnessAtLevel_eq_reduced_of_nonempty
      reps hrow 1 hOrigNonempty hRedNonempty
  rw [heq, hred]
  exact
    OpposingTypes.theorem4_trueModel_optimalTypeFairnessAtLevel_one_gt_inv_card_half_center
      hn hpos hdec hcenter

/--
Theorem 4 true-model baseline, even midpoint case, lifted from the two-type
half-population reduced model to the original true model.
-/
theorem theorem4_trueModel_original_optimalUserFairnessAtLevel_one_gt_inv_card_half_succ_center
    {m n : ℕ} [NeZero m] [NeZero n]
    (R : ReductionWitness m n 2)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    {v : Item n → ℝ} {c : Item n}
    (hred :
      R.reduced = OpposingTypes.twoTypeReducedModel (1 / 2 : ℝ) v)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : OpposingTypes.StrictlyDecreasingByIndex v)
    (hsucc : c.val + 1 = (OpposingTypes.reverseItem c).val) :
    (n : ℝ)⁻¹ <
      RecommendationModel.optimalUserFairnessAtLevel R.data.model 1 := by
  have hrow : R.data.model.RowHasPositiveItem :=
    theorem4_trueHalf_original_rowHasPositiveItem_of_reduction R hred hpos
  rcases OpposingTypes.problem6EqualizedBasicOptimal_feasibleAtLevel_one_exists
      (alpha := (1 / 2 : ℝ)) (v := v)
      (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) hpos hdec with
    ⟨ρ, _ell, _hclosed, hfeasTwo⟩
  have hfeasR :
      TypeWeightedRecommendationModel.feasibleAtLevel R.reduced 1 ρ := by
    simpa [hred] using hfeasTwo
  have hRedNonempty :
      (TypeWeightedRecommendationModel.attainableTypeFairnessAtLevel
        R.reduced 1).Nonempty := by
    exact ⟨TypeWeightedRecommendationModel.typeFairness R.reduced ρ,
      ⟨ρ, hfeasR, rfl⟩⟩
  have hOrigFeas :
      RecommendationModel.feasibleAtLevel R.data.model 1
        (R.liftedPolicy ρ) := by
    unfold RecommendationModel.feasibleAtLevel
    rw [R.optimalItemFairness_eq_reduced reps]
    rw [R.itemFairness_liftedPolicy_eq_itemFairness ρ]
    exact hfeasR
  have hOrigNonempty :
      (RecommendationModel.attainableUserFairnessAtLevel
        R.data.model 1).Nonempty := by
    exact ⟨RecommendationModel.userFairness R.data.model (R.liftedPolicy ρ),
      ⟨R.liftedPolicy ρ, hOrigFeas, rfl⟩⟩
  have heq :
      RecommendationModel.optimalUserFairnessAtLevel R.data.model 1 =
        TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
          R.reduced 1 :=
    R.optimalUserFairnessAtLevel_eq_reduced_of_nonempty
      reps hrow 1 hOrigNonempty hRedNonempty
  rw [heq, hred]
  exact
    OpposingTypes.theorem4_trueModel_optimalTypeFairnessAtLevel_one_gt_inv_card_half_succ_center
      hpos hdec hsucc

/--
Theorem 4 true-model baseline for an estimated recommendation model, odd
midpoint case.
-/
theorem theorem4_trueModel_optimalUserFairnessAtLevel_one_gt_inv_card_half_center_from_reduction
    {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n)
    (R : ReductionWitness m n 2)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    {v : Item n → ℝ} {c : Item n}
    (hn : 1 < n)
    (htrue : E.trueModel = R.data.model)
    (hred :
      R.reduced = OpposingTypes.twoTypeReducedModel (1 / 2 : ℝ) v)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : OpposingTypes.StrictlyDecreasingByIndex v)
    (hcenter : c.val = (OpposingTypes.reverseItem c).val) :
    (n : ℝ)⁻¹ <
      RecommendationModel.optimalUserFairnessAtLevel E.trueModel 1 := by
  rw [htrue]
  exact theorem4_trueModel_original_optimalUserFairnessAtLevel_one_gt_inv_card_half_center
    R reps hn hred hpos hdec hcenter

/--
Theorem 4 true-model baseline for an estimated recommendation model, even
midpoint case.
-/
theorem theorem4_trueModel_optimalUserFairnessAtLevel_one_gt_inv_card_half_succ_center_from_reduction
    {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n)
    (R : ReductionWitness m n 2)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    {v : Item n → ℝ} {c : Item n}
    (htrue : E.trueModel = R.data.model)
    (hred :
      R.reduced = OpposingTypes.twoTypeReducedModel (1 / 2 : ℝ) v)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : OpposingTypes.StrictlyDecreasingByIndex v)
    (hsucc : c.val + 1 = (OpposingTypes.reverseItem c).val) :
    (n : ℝ)⁻¹ <
      RecommendationModel.optimalUserFairnessAtLevel E.trueModel 1 := by
  rw [htrue]
  exact theorem4_trueModel_original_optimalUserFairnessAtLevel_one_gt_inv_card_half_succ_center
    R reps hred hpos hdec hsucc

theorem theorem4_coldUser_typeZero_normalizedUserUtility_eq
    {m n : ℕ} [NeZero n]
    (E : EstimatedRecommendationModel m n)
    (Rtrue : ReductionWitness m n 2)
    (Rest : ReductionWitness m n 3)
    {beta : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 3 n}
    (u : User m)
    (htrue : E.trueModel = Rtrue.data.model)
    (hredTrue :
      Rtrue.reduced = OpposingTypes.twoTypeReducedModel (1 / 2 : ℝ) v)
    (htrueType : Rtrue.data.types.toType u = 0)
    (hestimatedType : Rest.data.types.toType u = 2) :
    RecommendationModel.normalizedUserUtility E.trueModel
        (Rest.liftedPolicy ρ) u =
      TypeWeightedRecommendationModel.normalizedTypeUtility
        (OpposingTypes.theorem4TrueReducedModelTypeZero beta v) ρ 2 := by
  have hrow :
      E.trueModel.utility u =
        (OpposingTypes.theorem4TrueReducedModelTypeZero beta v).utility 2 := by
    funext j
    rw [htrue, Rtrue.utility_agrees u j, hredTrue, htrueType]
    simp [OpposingTypes.twoTypeReducedModel,
      OpposingTypes.theorem4TrueReducedModelTypeZero]
  unfold RecommendationModel.normalizedUserUtility
    TypeWeightedRecommendationModel.normalizedTypeUtility
  congr 1
  · unfold RecommendationModel.rawUserUtility
      TypeWeightedRecommendationModel.rawTypeUtility
      AppliedModelingLib.Policy.agentScore AppliedModelingLib.pmfExp
      ReductionWitness.liftedPolicy UserTypeAssignment.liftTypePolicy
      AppliedModelingLib.Policy.liftAlong
    refine Finset.sum_congr rfl ?_
    intro j _hj
    rw [htrue, Rtrue.utility_agrees u j, hredTrue, htrueType,
      hestimatedType]
    simp [OpposingTypes.twoTypeReducedModel,
      OpposingTypes.theorem4TrueReducedModelTypeZero]
  · unfold RecommendationModel.bestItemUtility
      TypeWeightedRecommendationModel.bestItemUtility
    rw [hrow]

theorem theorem4_coldUser_typeOne_normalizedUserUtility_eq
    {m n : ℕ} [NeZero n]
    (E : EstimatedRecommendationModel m n)
    (Rtrue : ReductionWitness m n 2)
    (Rest : ReductionWitness m n 3)
    {beta : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 3 n}
    (u : User m)
    (htrue : E.trueModel = Rtrue.data.model)
    (hredTrue :
      Rtrue.reduced = OpposingTypes.twoTypeReducedModel (1 / 2 : ℝ) v)
    (htrueType : Rtrue.data.types.toType u = 1)
    (hestimatedType : Rest.data.types.toType u = 2) :
    RecommendationModel.normalizedUserUtility E.trueModel
        (Rest.liftedPolicy ρ) u =
      TypeWeightedRecommendationModel.normalizedTypeUtility
        (OpposingTypes.theorem4TrueReducedModelTypeOne beta v) ρ 2 := by
  have hrow :
      E.trueModel.utility u =
        (OpposingTypes.theorem4TrueReducedModelTypeOne beta v).utility 2 := by
    funext j
    rw [htrue, Rtrue.utility_agrees u j, hredTrue, htrueType]
    simp [OpposingTypes.twoTypeReducedModel,
      OpposingTypes.theorem4TrueReducedModelTypeOne]
  unfold RecommendationModel.normalizedUserUtility
    TypeWeightedRecommendationModel.normalizedTypeUtility
  congr 1
  · unfold RecommendationModel.rawUserUtility
      TypeWeightedRecommendationModel.rawTypeUtility
      AppliedModelingLib.Policy.agentScore AppliedModelingLib.pmfExp
      ReductionWitness.liftedPolicy UserTypeAssignment.liftTypePolicy
      AppliedModelingLib.Policy.liftAlong
    refine Finset.sum_congr rfl ?_
    intro j _hj
    rw [htrue, Rtrue.utility_agrees u j, hredTrue, htrueType,
      hestimatedType]
    simp [OpposingTypes.twoTypeReducedModel,
      OpposingTypes.theorem4TrueReducedModelTypeOne]
  · unfold RecommendationModel.bestItemUtility
      TypeWeightedRecommendationModel.bestItemUtility
    rw [hrow]

/--
Theorem 4 large-misestimation bridge for a concrete cold-start user whose true
row is the first opposing row, while the estimated reduction collapses that
user into the cold-start estimated type.
-/
theorem theorem4_misestimation_with_fairness_large_from_trueHalf_coldUser_typeZero
    {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n)
    (Rtrue : ReductionWitness m n 2)
    (Rest : ReductionWitness m n 3)
    {beta eps : ℝ} {v : Item n → ℝ}
    (u : User m)
    (hn : 1 < n)
    (htrue : E.trueModel = Rtrue.data.model)
    (hredTrue :
      Rtrue.reduced = OpposingTypes.twoTypeReducedModel (1 / 2 : ℝ) v)
    (htrueType : Rtrue.data.types.toType u = 0)
    (hestimatedType : Rest.data.types.toType u = 2)
    (heps : 0 < eps)
    (hbase :
      (n : ℝ)⁻¹ <
        RecommendationModel.optimalUserFairnessAtLevel E.trueModel 1)
    (hdec : OpposingTypes.StrictlyDecreasingByIndex v)
    (hfirst_pos : 0 < v OpposingTypes.theorem4FirstItem)
    (hsmall : v (OpposingTypes.theorem4SecondItem hn) <
      eps / (n : ℝ) * v OpposingTypes.theorem4FirstItem)
    (ρ : TypePolicy 3 n)
    (hno_first : ρ 2 OpposingTypes.theorem4FirstItem = 0) :
    1 - eps < E.priceOfMisestimation 1 (Rest.liftedPolicy ρ) := by
  have hcold :
      TypeWeightedRecommendationModel.normalizedTypeUtility
          (OpposingTypes.theorem4TrueReducedModelTypeZero beta v) ρ 2 <
        eps / (n : ℝ) :=
    OpposingTypes.paper_theorem4_coldStart_typeZero_normalizedUtility_lt
      hn hdec hfirst_pos hsmall ρ hno_first
  have hnorm :
      RecommendationModel.normalizedUserUtility E.trueModel
          (Rest.liftedPolicy ρ) u <
        eps / (n : ℝ) := by
    rw [theorem4_coldUser_typeZero_normalizedUserUtility_eq
      E Rtrue Rest u htrue hredTrue htrueType hestimatedType]
    exact hcold
  have huser :
      RecommendationModel.userFairness E.trueModel (Rest.liftedPolicy ρ) <
        eps / (n : ℝ) :=
    lt_of_le_of_lt
      (RecommendationModel.userFairness_le_normalizedUserUtility
        E.trueModel (Rest.liftedPolicy ρ) u) hnorm
  exact E.priceOfMisestimation_gt_one_sub_of_userFairness_lt_div_card
    eps (Rest.liftedPolicy ρ) heps hbase huser

/--
Theorem 4 large-misestimation bridge for a concrete cold-start user whose true
row is the second opposing row, while the estimated reduction collapses that
user into the cold-start estimated type.
-/
theorem theorem4_misestimation_with_fairness_large_from_trueHalf_coldUser_typeOne
    {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n)
    (Rtrue : ReductionWitness m n 2)
    (Rest : ReductionWitness m n 3)
    {beta eps : ℝ} {v : Item n → ℝ}
    (u : User m)
    (hn : 1 < n)
    (htrue : E.trueModel = Rtrue.data.model)
    (hredTrue :
      Rtrue.reduced = OpposingTypes.twoTypeReducedModel (1 / 2 : ℝ) v)
    (htrueType : Rtrue.data.types.toType u = 1)
    (hestimatedType : Rest.data.types.toType u = 2)
    (heps : 0 < eps)
    (hbase :
      (n : ℝ)⁻¹ <
        RecommendationModel.optimalUserFairnessAtLevel E.trueModel 1)
    (hdec : OpposingTypes.StrictlyDecreasingByIndex v)
    (hfirst_pos : 0 < v OpposingTypes.theorem4FirstItem)
    (hsmall : v (OpposingTypes.theorem4SecondItem hn) <
      eps / (n : ℝ) * v OpposingTypes.theorem4FirstItem)
    (ρ : TypePolicy 3 n)
    (hno_last : ρ 2 OpposingTypes.theorem4LastItem = 0) :
    1 - eps < E.priceOfMisestimation 1 (Rest.liftedPolicy ρ) := by
  have hcold :
      TypeWeightedRecommendationModel.normalizedTypeUtility
          (OpposingTypes.theorem4TrueReducedModelTypeOne beta v) ρ 2 <
        eps / (n : ℝ) :=
    OpposingTypes.paper_theorem4_coldStart_typeOne_normalizedUtility_lt
      hn hdec hfirst_pos hsmall ρ hno_last
  have hnorm :
      RecommendationModel.normalizedUserUtility E.trueModel
          (Rest.liftedPolicy ρ) u <
        eps / (n : ℝ) := by
    rw [theorem4_coldUser_typeOne_normalizedUserUtility_eq
      E Rtrue Rest u htrue hredTrue htrueType hestimatedType]
    exact hcold
  have huser :
      RecommendationModel.userFairness E.trueModel (Rest.liftedPolicy ρ) <
        eps / (n : ℝ) :=
    lt_of_le_of_lt
      (RecommendationModel.userFairness_le_normalizedUserUtility
        E.trueModel (Rest.liftedPolicy ρ) u) hnorm
  exact E.priceOfMisestimation_gt_one_sub_of_userFairness_lt_div_card
    eps (Rest.liftedPolicy ρ) heps hbase huser

/--
Theorem 4 source-level fairness side, first true cold-start row, from real
Problem 11 BFS data: the lifted policy solves the estimated `γ = 1` problem
and has price of misestimation above `1 - eps` for the true two-row model.
-/
theorem theorem4_misestimation_with_fairness_large_from_trueHalf_coldUser_typeZero_equalityFormOptimalBFS
    {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n)
    (Rtrue : ReductionWitness m n 2)
    (Rest : ReductionWitness m n 3)
    (repsEst : UserTypeAssignment.TypeRepresentatives Rest.data.types)
    {beta eps : ℝ} {v x z : Item n → ℝ} {ell : ℝ}
    (u : User m)
    (hn : 2 < n)
    (htrue : E.trueModel = Rtrue.data.model)
    (hestimated : E.estimatedModel = Rest.data.model)
    (hredTrue :
      Rtrue.reduced = OpposingTypes.twoTypeReducedModel (1 / 2 : ℝ) v)
    (hredEst :
      Rest.reduced = OpposingTypes.theorem4EstimatedReducedModel beta v)
    (htrueType : Rtrue.data.types.toType u = 0)
    (hestimatedType : Rest.data.types.toType u = 2)
    (heps : 0 < eps)
    (hbase :
      (n : ℝ)⁻¹ <
        RecommendationModel.optimalUserFairnessAtLevel E.trueModel 1)
    (hbeta : (n : ℝ)⁻¹ < beta)
    (hbeta_half : beta < 1 / 2)
    (hdec : OpposingTypes.StrictlyDecreasingByIndex v)
    (hpos : ∀ j : Item n, 0 < v j)
    (hsmall : v (OpposingTypes.theorem4SecondItem (by omega : 1 < n)) <
      eps / (n : ℝ) * v OpposingTypes.theorem4FirstItem)
    (hbfs :
      OpposingTypes.Theorem4Problem11EqualityFormOptimalBFS beta v x z ell)
    (hunique :
      ∀ (ρ' : TypePolicy 3 n) (ell' : ℝ),
        OpposingTypes.Theorem4Problem11PolicyOptimal beta v ρ' ell' →
          ρ' =
            OpposingTypes.theorem4Problem11PolicyOfRealVectors x z
              hbfs.feasible.x_nonneg hbfs.feasible.z_nonneg
              hbfs.feasible.sum_x hbfs.feasible.sum_z) :
    E.SolvesEstimatedProblem 1
        (Rest.liftedPolicy
          (OpposingTypes.theorem4Problem11PolicyOfRealVectors x z
            hbfs.feasible.x_nonneg hbfs.feasible.z_nonneg
            hbfs.feasible.sum_x hbfs.feasible.sum_z)) ∧
      1 - eps <
        E.priceOfMisestimation 1
          (Rest.liftedPolicy
            (OpposingTypes.theorem4Problem11PolicyOfRealVectors x z
              hbfs.feasible.x_nonneg hbfs.feasible.z_nonneg
              hbfs.feasible.sum_x hbfs.feasible.sum_z)) := by
  let ρ : TypePolicy 3 n :=
    OpposingTypes.theorem4Problem11PolicyOfRealVectors x z
      hbfs.feasible.x_nonneg hbfs.feasible.z_nonneg
      hbfs.feasible.sum_x hbfs.feasible.sum_z
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hbeta_pos : 0 < beta :=
    lt_trans (inv_pos.mpr hnpos) hbeta
  have hcold : 0 ≤ 1 - 2 * beta := by
    nlinarith
  have hsolve :
      E.SolvesEstimatedProblem 1 (Rest.liftedPolicy ρ) := by
    dsimp [ρ]
    exact E.theorem4_problem11EqualityFormOptimalBFS_solvesEstimatedProblem_one_from_reduction_of_policyOptimal_unique
      Rest repsEst hestimated hredEst hbeta_pos.le hcold hpos hbfs hunique
  have heq :
      OpposingTypes.Theorem4Problem11EqualizedBasicOptimal beta v ρ ell := by
    dsimp [ρ]
    exact OpposingTypes.theorem4Problem11EqualizedBasicOptimal_of_equalityFormOptimalBFS
      hbfs
  have hno :=
    OpposingTypes.theorem4Problem11_no_extremes_of_equalized
      hn hbeta hbeta_half hpos hdec heq
  have hprice :
      1 - eps < E.priceOfMisestimation 1 (Rest.liftedPolicy ρ) :=
    E.theorem4_misestimation_with_fairness_large_from_trueHalf_coldUser_typeZero
      (beta := beta) Rtrue Rest u (by omega : 1 < n)
      htrue hredTrue htrueType hestimatedType heps hbase hdec
      (hpos OpposingTypes.theorem4FirstItem) hsmall ρ hno.1
  exact ⟨hsolve, hprice⟩

/--
Theorem 4 source-level fairness side, second true cold-start row, from real
Problem 11 BFS data.
-/
theorem theorem4_misestimation_with_fairness_large_from_trueHalf_coldUser_typeOne_equalityFormOptimalBFS
    {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n)
    (Rtrue : ReductionWitness m n 2)
    (Rest : ReductionWitness m n 3)
    (repsEst : UserTypeAssignment.TypeRepresentatives Rest.data.types)
    {beta eps : ℝ} {v x z : Item n → ℝ} {ell : ℝ}
    (u : User m)
    (hn : 2 < n)
    (htrue : E.trueModel = Rtrue.data.model)
    (hestimated : E.estimatedModel = Rest.data.model)
    (hredTrue :
      Rtrue.reduced = OpposingTypes.twoTypeReducedModel (1 / 2 : ℝ) v)
    (hredEst :
      Rest.reduced = OpposingTypes.theorem4EstimatedReducedModel beta v)
    (htrueType : Rtrue.data.types.toType u = 1)
    (hestimatedType : Rest.data.types.toType u = 2)
    (heps : 0 < eps)
    (hbase :
      (n : ℝ)⁻¹ <
        RecommendationModel.optimalUserFairnessAtLevel E.trueModel 1)
    (hbeta : (n : ℝ)⁻¹ < beta)
    (hbeta_half : beta < 1 / 2)
    (hdec : OpposingTypes.StrictlyDecreasingByIndex v)
    (hpos : ∀ j : Item n, 0 < v j)
    (hsmall : v (OpposingTypes.theorem4SecondItem (by omega : 1 < n)) <
      eps / (n : ℝ) * v OpposingTypes.theorem4FirstItem)
    (hbfs :
      OpposingTypes.Theorem4Problem11EqualityFormOptimalBFS beta v x z ell)
    (hunique :
      ∀ (ρ' : TypePolicy 3 n) (ell' : ℝ),
        OpposingTypes.Theorem4Problem11PolicyOptimal beta v ρ' ell' →
          ρ' =
            OpposingTypes.theorem4Problem11PolicyOfRealVectors x z
              hbfs.feasible.x_nonneg hbfs.feasible.z_nonneg
              hbfs.feasible.sum_x hbfs.feasible.sum_z) :
    E.SolvesEstimatedProblem 1
        (Rest.liftedPolicy
          (OpposingTypes.theorem4Problem11PolicyOfRealVectors x z
            hbfs.feasible.x_nonneg hbfs.feasible.z_nonneg
            hbfs.feasible.sum_x hbfs.feasible.sum_z)) ∧
      1 - eps <
        E.priceOfMisestimation 1
          (Rest.liftedPolicy
            (OpposingTypes.theorem4Problem11PolicyOfRealVectors x z
              hbfs.feasible.x_nonneg hbfs.feasible.z_nonneg
              hbfs.feasible.sum_x hbfs.feasible.sum_z)) := by
  let ρ : TypePolicy 3 n :=
    OpposingTypes.theorem4Problem11PolicyOfRealVectors x z
      hbfs.feasible.x_nonneg hbfs.feasible.z_nonneg
      hbfs.feasible.sum_x hbfs.feasible.sum_z
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hbeta_pos : 0 < beta :=
    lt_trans (inv_pos.mpr hnpos) hbeta
  have hcold : 0 ≤ 1 - 2 * beta := by
    nlinarith
  have hsolve :
      E.SolvesEstimatedProblem 1 (Rest.liftedPolicy ρ) := by
    dsimp [ρ]
    exact E.theorem4_problem11EqualityFormOptimalBFS_solvesEstimatedProblem_one_from_reduction_of_policyOptimal_unique
      Rest repsEst hestimated hredEst hbeta_pos.le hcold hpos hbfs hunique
  have heq :
      OpposingTypes.Theorem4Problem11EqualizedBasicOptimal beta v ρ ell := by
    dsimp [ρ]
    exact OpposingTypes.theorem4Problem11EqualizedBasicOptimal_of_equalityFormOptimalBFS
      hbfs
  have hno :=
    OpposingTypes.theorem4Problem11_no_extremes_of_equalized
      hn hbeta hbeta_half hpos hdec heq
  have hprice :
      1 - eps < E.priceOfMisestimation 1 (Rest.liftedPolicy ρ) :=
    E.theorem4_misestimation_with_fairness_large_from_trueHalf_coldUser_typeOne
      (beta := beta) Rtrue Rest u (by omega : 1 < n)
      htrue hredTrue htrueType hestimatedType heps hbase hdec
      (hpos OpposingTypes.theorem4FirstItem) hsmall ρ hno.2
  exact ⟨hsolve, hprice⟩

theorem theorem4_misestimation_with_fairness_large_from_smallValueVector_closed_problem11_trueHalf_coldUser_typeZero_center
    {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n)
    (Rtrue : ReductionWitness m n 2)
    (Rest : ReductionWitness m n 3)
    (repsTrue : UserTypeAssignment.TypeRepresentatives Rtrue.data.types)
    (repsEst : UserTypeAssignment.TypeRepresentatives Rest.data.types)
    {beta eps : ℝ} {c : Item n}
    (u : User m)
    (hn : 2 < n)
    (htrue : E.trueModel = Rtrue.data.model)
    (hestimated : E.estimatedModel = Rest.data.model)
    (hredTrue :
      Rtrue.reduced = OpposingTypes.twoTypeReducedModel (1 / 2 : ℝ)
        (OpposingTypes.theorem4SmallValueVector (n := n) eps))
    (hredEst :
      Rest.reduced = OpposingTypes.theorem4EstimatedReducedModel beta
        (OpposingTypes.theorem4SmallValueVector (n := n) eps))
    (htrueType : Rtrue.data.types.toType u = 0)
    (hestimatedType : Rest.data.types.toType u = 2)
    (heps : 0 < eps)
    (hbeta : (n : ℝ)⁻¹ < beta)
    (hbeta_half : beta < 1 / 2)
    (hcenter : c.val = (OpposingTypes.reverseItem c).val) :
    ∃ ρ : TypePolicy 3 n,
      E.SolvesEstimatedProblem 1 (Rest.liftedPolicy ρ) ∧
        1 - eps < E.priceOfMisestimation 1 (Rest.liftedPolicy ρ) := by
  let v : Item n → ℝ := OpposingTypes.theorem4SmallValueVector (n := n) eps
  have hpos : ∀ j : Item n, 0 < v j :=
    OpposingTypes.theorem4SmallValueVector_pos (n := n) (eps := eps) heps
  have hdec : OpposingTypes.StrictlyDecreasingByIndex v :=
    OpposingTypes.theorem4SmallValueVector_strictlyDecreasing
      (n := n) (eps := eps) heps
  have hsmall : v (OpposingTypes.theorem4SecondItem (by omega : 1 < n)) <
      eps / (n : ℝ) * v OpposingTypes.theorem4FirstItem := by
    dsimp [v]
    rw [OpposingTypes.theorem4SmallValueVector_first_eq_one
        (n := n) (eps := eps),
      OpposingTypes.theorem4SmallValueVector_second_eq_ratio
        (n := n) (eps := eps) (by omega : 1 < n)]
    simpa using
      OpposingTypes.theorem4SmallValueVector_ratio_lt_eps_div_card
        (n := n) (eps := eps) heps
  have hbase :
      (n : ℝ)⁻¹ <
        RecommendationModel.optimalUserFairnessAtLevel E.trueModel 1 :=
    E.theorem4_trueModel_optimalUserFairnessAtLevel_one_gt_inv_card_half_center_from_reduction
      Rtrue repsTrue (by omega : 1 < n) htrue hredTrue hpos hdec hcenter
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hbeta_pos : 0 < beta :=
    lt_trans (inv_pos.mpr hnpos) hbeta
  rcases OpposingTypes.theorem4Problem11ClosedPivotBounds_exists_of_center
      hbeta_pos hbeta_half hpos hcenter with
    ⟨t, hleft, hbounds⟩
  have hbfs :
      OpposingTypes.Theorem4Problem11EqualityFormOptimalBFS beta v
        (OpposingTypes.theorem4Problem11ClosedX beta v t)
        (OpposingTypes.theorem4Problem11ClosedZ beta v t)
        (OpposingTypes.theorem4Problem11ClosedDualValue beta v t) :=
    OpposingTypes.theorem4Problem11EqualityFormOptimalBFS_of_closed_bounds
      hbeta_pos hbeta_half hpos hdec hleft hbounds
  let ρ : TypePolicy 3 n :=
    OpposingTypes.theorem4Problem11PolicyOfRealVectors
      (OpposingTypes.theorem4Problem11ClosedX beta v t)
      (OpposingTypes.theorem4Problem11ClosedZ beta v t)
      hbfs.feasible.x_nonneg hbfs.feasible.z_nonneg
      hbfs.feasible.sum_x hbfs.feasible.sum_z
  refine ⟨ρ, ?_⟩
  dsimp [ρ, v] at hbfs ⊢
  exact E.theorem4_misestimation_with_fairness_large_from_trueHalf_coldUser_typeZero_equalityFormOptimalBFS
    Rtrue Rest repsEst u hn htrue hestimated hredTrue hredEst htrueType
    hestimatedType heps hbase hbeta hbeta_half hdec hpos hsmall hbfs
    (by
      intro ρ' ell' hopt'
      exact
        (OpposingTypes.theorem4Problem11PolicyOptimal_pairwise_unique_of_closed_policyOptimal
          hn hbeta_pos hbeta_half hpos hdec hleft
          (OpposingTypes.theorem4Problem11PolicyOptimal_of_equalityFormOptimalBFS
            hbfs))
          ρ' ρ ell'
          (OpposingTypes.theorem4Problem11ClosedDualValue beta v t)
          hopt'
          (OpposingTypes.theorem4Problem11PolicyOptimal_of_equalityFormOptimalBFS
            hbfs))

theorem theorem4_misestimation_with_fairness_large_from_smallValueVector_closed_problem11_trueHalf_coldUser_typeOne_center
    {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n)
    (Rtrue : ReductionWitness m n 2)
    (Rest : ReductionWitness m n 3)
    (repsTrue : UserTypeAssignment.TypeRepresentatives Rtrue.data.types)
    (repsEst : UserTypeAssignment.TypeRepresentatives Rest.data.types)
    {beta eps : ℝ} {c : Item n}
    (u : User m)
    (hn : 2 < n)
    (htrue : E.trueModel = Rtrue.data.model)
    (hestimated : E.estimatedModel = Rest.data.model)
    (hredTrue :
      Rtrue.reduced = OpposingTypes.twoTypeReducedModel (1 / 2 : ℝ)
        (OpposingTypes.theorem4SmallValueVector (n := n) eps))
    (hredEst :
      Rest.reduced = OpposingTypes.theorem4EstimatedReducedModel beta
        (OpposingTypes.theorem4SmallValueVector (n := n) eps))
    (htrueType : Rtrue.data.types.toType u = 1)
    (hestimatedType : Rest.data.types.toType u = 2)
    (heps : 0 < eps)
    (hbeta : (n : ℝ)⁻¹ < beta)
    (hbeta_half : beta < 1 / 2)
    (hcenter : c.val = (OpposingTypes.reverseItem c).val) :
    ∃ ρ : TypePolicy 3 n,
      E.SolvesEstimatedProblem 1 (Rest.liftedPolicy ρ) ∧
        1 - eps < E.priceOfMisestimation 1 (Rest.liftedPolicy ρ) := by
  let v : Item n → ℝ := OpposingTypes.theorem4SmallValueVector (n := n) eps
  have hpos : ∀ j : Item n, 0 < v j :=
    OpposingTypes.theorem4SmallValueVector_pos (n := n) (eps := eps) heps
  have hdec : OpposingTypes.StrictlyDecreasingByIndex v :=
    OpposingTypes.theorem4SmallValueVector_strictlyDecreasing
      (n := n) (eps := eps) heps
  have hsmall : v (OpposingTypes.theorem4SecondItem (by omega : 1 < n)) <
      eps / (n : ℝ) * v OpposingTypes.theorem4FirstItem := by
    dsimp [v]
    rw [OpposingTypes.theorem4SmallValueVector_first_eq_one
        (n := n) (eps := eps),
      OpposingTypes.theorem4SmallValueVector_second_eq_ratio
        (n := n) (eps := eps) (by omega : 1 < n)]
    simpa using
      OpposingTypes.theorem4SmallValueVector_ratio_lt_eps_div_card
        (n := n) (eps := eps) heps
  have hbase :
      (n : ℝ)⁻¹ <
        RecommendationModel.optimalUserFairnessAtLevel E.trueModel 1 :=
    E.theorem4_trueModel_optimalUserFairnessAtLevel_one_gt_inv_card_half_center_from_reduction
      Rtrue repsTrue (by omega : 1 < n) htrue hredTrue hpos hdec hcenter
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hbeta_pos : 0 < beta :=
    lt_trans (inv_pos.mpr hnpos) hbeta
  rcases OpposingTypes.theorem4Problem11ClosedPivotBounds_exists_of_center
      hbeta_pos hbeta_half hpos hcenter with
    ⟨t, hleft, hbounds⟩
  have hbfs :
      OpposingTypes.Theorem4Problem11EqualityFormOptimalBFS beta v
        (OpposingTypes.theorem4Problem11ClosedX beta v t)
        (OpposingTypes.theorem4Problem11ClosedZ beta v t)
        (OpposingTypes.theorem4Problem11ClosedDualValue beta v t) :=
    OpposingTypes.theorem4Problem11EqualityFormOptimalBFS_of_closed_bounds
      hbeta_pos hbeta_half hpos hdec hleft hbounds
  let ρ : TypePolicy 3 n :=
    OpposingTypes.theorem4Problem11PolicyOfRealVectors
      (OpposingTypes.theorem4Problem11ClosedX beta v t)
      (OpposingTypes.theorem4Problem11ClosedZ beta v t)
      hbfs.feasible.x_nonneg hbfs.feasible.z_nonneg
      hbfs.feasible.sum_x hbfs.feasible.sum_z
  refine ⟨ρ, ?_⟩
  dsimp [ρ, v] at hbfs ⊢
  exact E.theorem4_misestimation_with_fairness_large_from_trueHalf_coldUser_typeOne_equalityFormOptimalBFS
    Rtrue Rest repsEst u hn htrue hestimated hredTrue hredEst htrueType
    hestimatedType heps hbase hbeta hbeta_half hdec hpos hsmall hbfs
    (by
      intro ρ' ell' hopt'
      exact
        (OpposingTypes.theorem4Problem11PolicyOptimal_pairwise_unique_of_closed_policyOptimal
          hn hbeta_pos hbeta_half hpos hdec hleft
          (OpposingTypes.theorem4Problem11PolicyOptimal_of_equalityFormOptimalBFS
            hbfs))
          ρ' ρ ell'
          (OpposingTypes.theorem4Problem11ClosedDualValue beta v t)
          hopt'
          (OpposingTypes.theorem4Problem11PolicyOptimal_of_equalityFormOptimalBFS
            hbfs))

theorem theorem4_misestimation_with_fairness_large_from_smallValueVector_closed_problem11_trueHalf_coldUser_typeZero_succ_center
    {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n)
    (Rtrue : ReductionWitness m n 2)
    (Rest : ReductionWitness m n 3)
    (repsTrue : UserTypeAssignment.TypeRepresentatives Rtrue.data.types)
    (repsEst : UserTypeAssignment.TypeRepresentatives Rest.data.types)
    {beta eps : ℝ} {c : Item n}
    (u : User m)
    (hn : 2 < n)
    (htrue : E.trueModel = Rtrue.data.model)
    (hestimated : E.estimatedModel = Rest.data.model)
    (hredTrue :
      Rtrue.reduced = OpposingTypes.twoTypeReducedModel (1 / 2 : ℝ)
        (OpposingTypes.theorem4SmallValueVector (n := n) eps))
    (hredEst :
      Rest.reduced = OpposingTypes.theorem4EstimatedReducedModel beta
        (OpposingTypes.theorem4SmallValueVector (n := n) eps))
    (htrueType : Rtrue.data.types.toType u = 0)
    (hestimatedType : Rest.data.types.toType u = 2)
    (heps : 0 < eps)
    (hbeta : (n : ℝ)⁻¹ < beta)
    (hbeta_half : beta < 1 / 2)
    (hsucc : c.val + 1 = (OpposingTypes.reverseItem c).val) :
    ∃ ρ : TypePolicy 3 n,
      E.SolvesEstimatedProblem 1 (Rest.liftedPolicy ρ) ∧
        1 - eps < E.priceOfMisestimation 1 (Rest.liftedPolicy ρ) := by
  let v : Item n → ℝ := OpposingTypes.theorem4SmallValueVector (n := n) eps
  have hpos : ∀ j : Item n, 0 < v j :=
    OpposingTypes.theorem4SmallValueVector_pos (n := n) (eps := eps) heps
  have hdec : OpposingTypes.StrictlyDecreasingByIndex v :=
    OpposingTypes.theorem4SmallValueVector_strictlyDecreasing
      (n := n) (eps := eps) heps
  have hsmall : v (OpposingTypes.theorem4SecondItem (by omega : 1 < n)) <
      eps / (n : ℝ) * v OpposingTypes.theorem4FirstItem := by
    dsimp [v]
    rw [OpposingTypes.theorem4SmallValueVector_first_eq_one
        (n := n) (eps := eps),
      OpposingTypes.theorem4SmallValueVector_second_eq_ratio
        (n := n) (eps := eps) (by omega : 1 < n)]
    simpa using
      OpposingTypes.theorem4SmallValueVector_ratio_lt_eps_div_card
        (n := n) (eps := eps) heps
  have hbase :
      (n : ℝ)⁻¹ <
        RecommendationModel.optimalUserFairnessAtLevel E.trueModel 1 :=
    E.theorem4_trueModel_optimalUserFairnessAtLevel_one_gt_inv_card_half_succ_center_from_reduction
      Rtrue repsTrue htrue hredTrue hpos hdec hsucc
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hbeta_pos : 0 < beta :=
    lt_trans (inv_pos.mpr hnpos) hbeta
  rcases OpposingTypes.theorem4Problem11ClosedPivotBounds_exists_of_succ_center
      hbeta_pos hbeta_half hpos hsucc with
    ⟨t, hleft, hbounds⟩
  have hbfs :
      OpposingTypes.Theorem4Problem11EqualityFormOptimalBFS beta v
        (OpposingTypes.theorem4Problem11ClosedX beta v t)
        (OpposingTypes.theorem4Problem11ClosedZ beta v t)
        (OpposingTypes.theorem4Problem11ClosedDualValue beta v t) :=
    OpposingTypes.theorem4Problem11EqualityFormOptimalBFS_of_closed_bounds
      hbeta_pos hbeta_half hpos hdec hleft hbounds
  let ρ : TypePolicy 3 n :=
    OpposingTypes.theorem4Problem11PolicyOfRealVectors
      (OpposingTypes.theorem4Problem11ClosedX beta v t)
      (OpposingTypes.theorem4Problem11ClosedZ beta v t)
      hbfs.feasible.x_nonneg hbfs.feasible.z_nonneg
      hbfs.feasible.sum_x hbfs.feasible.sum_z
  refine ⟨ρ, ?_⟩
  dsimp [ρ, v] at hbfs ⊢
  exact E.theorem4_misestimation_with_fairness_large_from_trueHalf_coldUser_typeZero_equalityFormOptimalBFS
    Rtrue Rest repsEst u hn htrue hestimated hredTrue hredEst htrueType
    hestimatedType heps hbase hbeta hbeta_half hdec hpos hsmall hbfs
    (by
      intro ρ' ell' hopt'
      exact
        (OpposingTypes.theorem4Problem11PolicyOptimal_pairwise_unique_of_closed_policyOptimal
          hn hbeta_pos hbeta_half hpos hdec hleft
          (OpposingTypes.theorem4Problem11PolicyOptimal_of_equalityFormOptimalBFS
            hbfs))
          ρ' ρ ell'
          (OpposingTypes.theorem4Problem11ClosedDualValue beta v t)
          hopt'
          (OpposingTypes.theorem4Problem11PolicyOptimal_of_equalityFormOptimalBFS
            hbfs))

theorem theorem4_misestimation_with_fairness_large_from_smallValueVector_closed_problem11_trueHalf_coldUser_typeOne_succ_center
    {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n)
    (Rtrue : ReductionWitness m n 2)
    (Rest : ReductionWitness m n 3)
    (repsTrue : UserTypeAssignment.TypeRepresentatives Rtrue.data.types)
    (repsEst : UserTypeAssignment.TypeRepresentatives Rest.data.types)
    {beta eps : ℝ} {c : Item n}
    (u : User m)
    (hn : 2 < n)
    (htrue : E.trueModel = Rtrue.data.model)
    (hestimated : E.estimatedModel = Rest.data.model)
    (hredTrue :
      Rtrue.reduced = OpposingTypes.twoTypeReducedModel (1 / 2 : ℝ)
        (OpposingTypes.theorem4SmallValueVector (n := n) eps))
    (hredEst :
      Rest.reduced = OpposingTypes.theorem4EstimatedReducedModel beta
        (OpposingTypes.theorem4SmallValueVector (n := n) eps))
    (htrueType : Rtrue.data.types.toType u = 1)
    (hestimatedType : Rest.data.types.toType u = 2)
    (heps : 0 < eps)
    (hbeta : (n : ℝ)⁻¹ < beta)
    (hbeta_half : beta < 1 / 2)
    (hsucc : c.val + 1 = (OpposingTypes.reverseItem c).val) :
    ∃ ρ : TypePolicy 3 n,
      E.SolvesEstimatedProblem 1 (Rest.liftedPolicy ρ) ∧
        1 - eps < E.priceOfMisestimation 1 (Rest.liftedPolicy ρ) := by
  let v : Item n → ℝ := OpposingTypes.theorem4SmallValueVector (n := n) eps
  have hpos : ∀ j : Item n, 0 < v j :=
    OpposingTypes.theorem4SmallValueVector_pos (n := n) (eps := eps) heps
  have hdec : OpposingTypes.StrictlyDecreasingByIndex v :=
    OpposingTypes.theorem4SmallValueVector_strictlyDecreasing
      (n := n) (eps := eps) heps
  have hsmall : v (OpposingTypes.theorem4SecondItem (by omega : 1 < n)) <
      eps / (n : ℝ) * v OpposingTypes.theorem4FirstItem := by
    dsimp [v]
    rw [OpposingTypes.theorem4SmallValueVector_first_eq_one
        (n := n) (eps := eps),
      OpposingTypes.theorem4SmallValueVector_second_eq_ratio
        (n := n) (eps := eps) (by omega : 1 < n)]
    simpa using
      OpposingTypes.theorem4SmallValueVector_ratio_lt_eps_div_card
        (n := n) (eps := eps) heps
  have hbase :
      (n : ℝ)⁻¹ <
        RecommendationModel.optimalUserFairnessAtLevel E.trueModel 1 :=
    E.theorem4_trueModel_optimalUserFairnessAtLevel_one_gt_inv_card_half_succ_center_from_reduction
      Rtrue repsTrue htrue hredTrue hpos hdec hsucc
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hbeta_pos : 0 < beta :=
    lt_trans (inv_pos.mpr hnpos) hbeta
  rcases OpposingTypes.theorem4Problem11ClosedPivotBounds_exists_of_succ_center
      hbeta_pos hbeta_half hpos hsucc with
    ⟨t, hleft, hbounds⟩
  have hbfs :
      OpposingTypes.Theorem4Problem11EqualityFormOptimalBFS beta v
        (OpposingTypes.theorem4Problem11ClosedX beta v t)
        (OpposingTypes.theorem4Problem11ClosedZ beta v t)
        (OpposingTypes.theorem4Problem11ClosedDualValue beta v t) :=
    OpposingTypes.theorem4Problem11EqualityFormOptimalBFS_of_closed_bounds
      hbeta_pos hbeta_half hpos hdec hleft hbounds
  let ρ : TypePolicy 3 n :=
    OpposingTypes.theorem4Problem11PolicyOfRealVectors
      (OpposingTypes.theorem4Problem11ClosedX beta v t)
      (OpposingTypes.theorem4Problem11ClosedZ beta v t)
      hbfs.feasible.x_nonneg hbfs.feasible.z_nonneg
      hbfs.feasible.sum_x hbfs.feasible.sum_z
  refine ⟨ρ, ?_⟩
  dsimp [ρ, v] at hbfs ⊢
  exact E.theorem4_misestimation_with_fairness_large_from_trueHalf_coldUser_typeOne_equalityFormOptimalBFS
    Rtrue Rest repsEst u hn htrue hestimated hredTrue hredEst htrueType
    hestimatedType heps hbase hbeta hbeta_half hdec hpos hsmall hbfs
    (by
      intro ρ' ell' hopt'
      exact
        (OpposingTypes.theorem4Problem11PolicyOptimal_pairwise_unique_of_closed_policyOptimal
          hn hbeta_pos hbeta_half hpos hdec hleft
          (OpposingTypes.theorem4Problem11PolicyOptimal_of_equalityFormOptimalBFS
            hbfs))
          ρ' ρ ell'
          (OpposingTypes.theorem4Problem11ClosedDualValue beta v t)
          hopt'
          (OpposingTypes.theorem4Problem11PolicyOptimal_of_equalityFormOptimalBFS
            hbfs))

/--
Theorem 4 no-fairness price bound, first true cold-start row, lifted to the
original model through the paper's reduction witness.
-/
theorem theorem4_misestimation_without_fairness_le_half_typeZero_from_reduction
    {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n)
    (R : ReductionWitness m n 3)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    {beta : ℝ} {v : Item n → ℝ}
    (htrue : E.trueModel = R.data.model)
    (hred :
      R.reduced = OpposingTypes.theorem4TrueReducedModelTypeZero beta v)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : OpposingTypes.StrictlyDecreasingByIndex v) :
    E.priceOfMisestimation 0
      (R.liftedPolicy (OpposingTypes.theorem4NoFairnessPolicyTypeZero v)) ≤
        (1 / 2 : ℝ) := by
  let ρ : TypePolicy 3 n := OpposingTypes.theorem4NoFairnessPolicyTypeZero v
  have hbaseR :
      RecommendationModel.optimalUserFairnessAtLevel R.data.model 0 = 1 := by
    exact R.data.model.optimalUserFairnessAtLevel_zero_eq_one
      (theorem4_trueModelTypeZero_original_nonnegative_of_reduction
        R hred hpos)
      (theorem4_trueModelTypeZero_original_rowHasPositiveItem_of_reduction
        R hred hpos)
  have hbaseE :
      RecommendationModel.optimalUserFairnessAtLevel E.trueModel 0 = 1 := by
    rw [htrue]
    exact hbaseR
  have htype :
      (1 / 2 : ℝ) ≤ TypeWeightedRecommendationModel.typeFairness R.reduced ρ := by
    rw [hred]
    dsimp [ρ]
    exact OpposingTypes.theorem4NoFairnessPolicyTypeZero_true_typeFairness_ge_half
      hpos hdec
  have huserR :
      (1 / 2 : ℝ) ≤
        RecommendationModel.userFairness R.data.model (R.liftedPolicy ρ) := by
    rw [R.userFairness_liftedPolicy_eq_typeFairness reps ρ]
    exact htype
  have huserE :
      (1 / 2 : ℝ) ≤
        RecommendationModel.userFairness E.trueModel (R.liftedPolicy ρ) := by
    rw [htrue]
    exact huserR
  exact E.priceOfMisestimation_at_zero_le_half_of_userFairness_ge_half
    (R.liftedPolicy ρ) hbaseE huserE

/--
Theorem 4 no-fairness price bound, second true cold-start row, lifted to the
original model through the paper's reduction witness.
-/
theorem theorem4_misestimation_without_fairness_le_half_typeOne_from_reduction
    {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n)
    (R : ReductionWitness m n 3)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    {beta : ℝ} {v : Item n → ℝ}
    (htrue : E.trueModel = R.data.model)
    (hred :
      R.reduced = OpposingTypes.theorem4TrueReducedModelTypeOne beta v)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : OpposingTypes.StrictlyDecreasingByIndex v) :
    E.priceOfMisestimation 0
      (R.liftedPolicy (OpposingTypes.theorem4NoFairnessPolicyTypeOne v)) ≤
        (1 / 2 : ℝ) := by
  let ρ : TypePolicy 3 n := OpposingTypes.theorem4NoFairnessPolicyTypeOne v
  have hbaseR :
      RecommendationModel.optimalUserFairnessAtLevel R.data.model 0 = 1 := by
    exact R.data.model.optimalUserFairnessAtLevel_zero_eq_one
      (theorem4_trueModelTypeOne_original_nonnegative_of_reduction
        R hred hpos)
      (theorem4_trueModelTypeOne_original_rowHasPositiveItem_of_reduction
        R hred hpos)
  have hbaseE :
      RecommendationModel.optimalUserFairnessAtLevel E.trueModel 0 = 1 := by
    rw [htrue]
    exact hbaseR
  have htype :
      (1 / 2 : ℝ) ≤ TypeWeightedRecommendationModel.typeFairness R.reduced ρ := by
    rw [hred]
    dsimp [ρ]
    exact OpposingTypes.theorem4NoFairnessPolicyTypeOne_true_typeFairness_ge_half
      hpos hdec
  have huserR :
      (1 / 2 : ℝ) ≤
        RecommendationModel.userFairness R.data.model (R.liftedPolicy ρ) := by
    rw [R.userFairness_liftedPolicy_eq_typeFairness reps ρ]
    exact htype
  have huserE :
      (1 / 2 : ℝ) ≤
        RecommendationModel.userFairness E.trueModel (R.liftedPolicy ρ) := by
    rw [htrue]
    exact huserR
  exact E.priceOfMisestimation_at_zero_le_half_of_userFairness_ge_half
    (R.liftedPolicy ρ) hbaseE huserE

/--
Theorem 4 no-fairness price bound for the source model: the true population has
the two opposing rows, while the estimated model collapses cold-start users
into the averaged third row.  The displayed no-fairness policy is pure on the
known estimated rows and splits the cold-start row evenly across an
estimated-best mirror pair.
-/
theorem theorem4_misestimation_without_fairness_le_half_trueHalf_collapsed_from_reductions
    {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n)
    (Rtrue : ReductionWitness m n 2)
    (Rest : ReductionWitness m n 3)
    (repsEst : UserTypeAssignment.TypeRepresentatives Rest.data.types)
    {beta : ℝ} {v : Item n → ℝ}
    (htrue : E.trueModel = Rtrue.data.model)
    (hestimated : E.estimatedModel = Rest.data.model)
    (hredTrue :
      Rtrue.reduced = OpposingTypes.twoTypeReducedModel (1 / 2 : ℝ) v)
    (hredEst :
      Rest.reduced = OpposingTypes.theorem4EstimatedReducedModel beta v)
    (hknown0 :
      ∀ u : User m, Rest.data.types.toType u = 0 →
        Rtrue.data.types.toType u = 0)
    (hknown1 :
      ∀ u : User m, Rest.data.types.toType u = 1 →
        Rtrue.data.types.toType u = 1)
    (hbeta : 0 ≤ beta) (hcold : 0 ≤ 1 - 2 * beta)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : OpposingTypes.StrictlyDecreasingByIndex v) :
    let ρ : TypePolicy 3 n :=
      OpposingTypes.theorem4NoFairnessPolicyCollapsed v
    E.SolvesEstimatedProblem 0 (Rest.liftedPolicy ρ) ∧
      E.priceOfMisestimation 0 (Rest.liftedPolicy ρ) ≤ (1 / 2 : ℝ) := by
  let ρ : TypePolicy 3 n :=
    OpposingTypes.theorem4NoFairnessPolicyCollapsed v
  have hsolve :
      E.SolvesEstimatedProblem 0 (Rest.liftedPolicy ρ) := by
    dsimp [ρ]
    exact E.theorem4_solvesEstimatedProblem_from_estimated_reduction
      Rest repsEst hestimated hredEst hpos
      (OpposingTypes.theorem4NoFairnessPolicyCollapsed_estimated_optimalAtLevel_zero
        hbeta hcold hpos hdec)
  have hbaseR :
      RecommendationModel.optimalUserFairnessAtLevel Rtrue.data.model 0 = 1 := by
    exact Rtrue.data.model.optimalUserFairnessAtLevel_zero_eq_one
      (theorem4_trueHalf_original_nonnegative_of_reduction
        Rtrue hredTrue hpos)
      (theorem4_trueHalf_original_rowHasPositiveItem_of_reduction
        Rtrue hredTrue hpos)
  have hbaseE :
      RecommendationModel.optimalUserFairnessAtLevel E.trueModel 0 = 1 := by
    rw [htrue]
    exact hbaseR
  have huserR :
      (1 / 2 : ℝ) ≤
        RecommendationModel.userFairness Rtrue.data.model
          (Rest.liftedPolicy ρ) := by
    unfold RecommendationModel.userFairness
    apply AppliedModelingLib.le_finiteMin
    intro u
    have hraw :
        RecommendationModel.rawUserUtility Rtrue.data.model
            (Rest.liftedPolicy ρ) u =
          AppliedModelingLib.pmfExp (ρ (Rest.data.types.toType u))
            ((OpposingTypes.twoTypeReducedModel (1 / 2 : ℝ) v).utility
              (Rtrue.data.types.toType u)) := by
      unfold RecommendationModel.rawUserUtility AppliedModelingLib.Policy.agentScore
        AppliedModelingLib.pmfExp ReductionWitness.liftedPolicy
        UserTypeAssignment.liftTypePolicy AppliedModelingLib.Policy.liftAlong
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [Rtrue.utility_agrees u j, hredTrue]
    have hbest :
        RecommendationModel.bestItemUtility Rtrue.data.model u =
          TypeWeightedRecommendationModel.bestItemUtility
            (OpposingTypes.twoTypeReducedModel (1 / 2 : ℝ) v)
            (Rtrue.data.types.toType u) := by
      rw [Rtrue.bestItemUtility_eq_bestTypeUtility u, hredTrue]
    unfold RecommendationModel.normalizedUserUtility
    rw [hraw, hbest]
    exact
      OpposingTypes.theorem4NoFairnessPolicyCollapsed_trueHalf_normalizedRowUtility_ge_half
        hpos hdec (Rtrue.data.types.toType u) (Rest.data.types.toType u)
        (fun h0 => hknown0 u h0)
        (fun h1 => hknown1 u h1)
  have huserE :
      (1 / 2 : ℝ) ≤
        RecommendationModel.userFairness E.trueModel
          (Rest.liftedPolicy ρ) := by
    rw [htrue]
    exact huserR
  refine ⟨hsolve, ?_⟩
  exact E.priceOfMisestimation_at_zero_le_half_of_userFairness_ge_half
    (Rest.liftedPolicy ρ) hbaseE huserE

/--
Theorem 4 fairness-constrained misestimation bridge, first true cold-start type.

The remaining estimated-LP obligation is exactly the paper's Appendix E
no-extreme-item certificate for the estimated optimum: the cold-start type's
row assigns zero mass to item `1`.
-/
theorem theorem4_misestimation_with_fairness_large_typeZero_from_reduction
    {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n)
    (R : ReductionWitness m n 3)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    {beta eps : ℝ} {v : Item n → ℝ}
    (hn : 1 < n)
    (htrue : E.trueModel = R.data.model)
    (hred :
      R.reduced = OpposingTypes.theorem4TrueReducedModelTypeZero beta v)
    (heps : 0 < eps)
    (hbase :
      (n : ℝ)⁻¹ <
        RecommendationModel.optimalUserFairnessAtLevel E.trueModel 1)
    (hdec : OpposingTypes.StrictlyDecreasingByIndex v)
    (hfirst_pos : 0 < v OpposingTypes.theorem4FirstItem)
    (hsmall : v (OpposingTypes.theorem4SecondItem hn) <
      eps / (n : ℝ) * v OpposingTypes.theorem4FirstItem)
    (ρ : TypePolicy 3 n)
    (hno_first : ρ 2 OpposingTypes.theorem4FirstItem = 0) :
    1 - eps < E.priceOfMisestimation 1 (R.liftedPolicy ρ) := by
  have htype :
      TypeWeightedRecommendationModel.typeFairness
          (OpposingTypes.theorem4TrueReducedModelTypeZero beta v) ρ <
        eps / (n : ℝ) :=
    OpposingTypes.paper_theorem4_coldStart_typeZero_typeFairness_lt
      hn hdec hfirst_pos hsmall ρ hno_first
  have htypeR :
      TypeWeightedRecommendationModel.typeFairness R.reduced ρ <
        eps / (n : ℝ) := by
    rw [hred]
    exact htype
  have huserR :
      RecommendationModel.userFairness R.data.model (R.liftedPolicy ρ) <
        eps / (n : ℝ) := by
    rw [R.userFairness_liftedPolicy_eq_typeFairness reps ρ]
    exact htypeR
  have huserE :
      RecommendationModel.userFairness E.trueModel (R.liftedPolicy ρ) <
        eps / (n : ℝ) := by
    rw [htrue]
    exact huserR
  exact E.priceOfMisestimation_gt_one_sub_of_userFairness_lt_div_card
    eps (R.liftedPolicy ρ) heps hbase huserE

/--
Theorem 4 fairness-constrained misestimation bridge, second true cold-start
type.

The remaining estimated-LP obligation is the mirror no-extreme-item
certificate: the cold-start type's row assigns zero mass to item `n`.
-/
theorem theorem4_misestimation_with_fairness_large_typeOne_from_reduction
    {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n)
    (R : ReductionWitness m n 3)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    {beta eps : ℝ} {v : Item n → ℝ}
    (hn : 1 < n)
    (htrue : E.trueModel = R.data.model)
    (hred :
      R.reduced = OpposingTypes.theorem4TrueReducedModelTypeOne beta v)
    (heps : 0 < eps)
    (hbase :
      (n : ℝ)⁻¹ <
        RecommendationModel.optimalUserFairnessAtLevel E.trueModel 1)
    (hdec : OpposingTypes.StrictlyDecreasingByIndex v)
    (hfirst_pos : 0 < v OpposingTypes.theorem4FirstItem)
    (hsmall : v (OpposingTypes.theorem4SecondItem hn) <
      eps / (n : ℝ) * v OpposingTypes.theorem4FirstItem)
    (ρ : TypePolicy 3 n)
    (hno_last : ρ 2 OpposingTypes.theorem4LastItem = 0) :
    1 - eps < E.priceOfMisestimation 1 (R.liftedPolicy ρ) := by
  have htype :
      TypeWeightedRecommendationModel.typeFairness
          (OpposingTypes.theorem4TrueReducedModelTypeOne beta v) ρ <
        eps / (n : ℝ) :=
    OpposingTypes.paper_theorem4_coldStart_typeOne_typeFairness_lt
      hn hdec hfirst_pos hsmall ρ hno_last
  have htypeR :
      TypeWeightedRecommendationModel.typeFairness R.reduced ρ <
        eps / (n : ℝ) := by
    rw [hred]
    exact htype
  have huserR :
      RecommendationModel.userFairness R.data.model (R.liftedPolicy ρ) <
        eps / (n : ℝ) := by
    rw [R.userFairness_liftedPolicy_eq_typeFairness reps ρ]
    exact htypeR
  have huserE :
      RecommendationModel.userFairness E.trueModel (R.liftedPolicy ρ) <
        eps / (n : ℝ) := by
    rw [htrue]
    exact huserR
  exact E.priceOfMisestimation_gt_one_sub_of_userFairness_lt_div_card
    eps (R.liftedPolicy ρ) heps hbase huserE

/--
Theorem 4 fairness-constrained misestimation bridge, first true cold-start
type, using the Problem 11 pivot-support/closed-form certificate rather than a
bare no-first-item assumption.
-/
theorem theorem4_misestimation_with_fairness_large_typeZero_from_problem11_certificate
    {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n)
    (R : ReductionWitness m n 3)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    {beta eps : ℝ} {v : Item n → ℝ}
    (hn : 2 < n)
    (htrue : E.trueModel = R.data.model)
    (hred :
      R.reduced = OpposingTypes.theorem4TrueReducedModelTypeZero beta v)
    (heps : 0 < eps)
    (hbase :
      (n : ℝ)⁻¹ <
        RecommendationModel.optimalUserFairnessAtLevel E.trueModel 1)
    (hbeta : (n : ℝ)⁻¹ < beta)
    (hbeta_half : beta < 1 / 2)
    (hdec : OpposingTypes.StrictlyDecreasingByIndex v)
    (hpos : ∀ j : Item n, 0 < v j)
    (hsmall : v (OpposingTypes.theorem4SecondItem (by omega : 1 < n)) <
      eps / (n : ℝ) * v OpposingTypes.theorem4FirstItem)
    (ρ : TypePolicy 3 n) (t : Item n)
    (hpivot : OpposingTypes.Theorem4Problem11PivotSupport ρ t)
    (hclosed_first :
      t = OpposingTypes.theorem4FirstItem →
        (ρ 2 OpposingTypes.theorem4FirstItem).toReal =
          OpposingTypes.theorem4Problem11PivotOneZ beta v) :
    1 - eps < E.priceOfMisestimation 1 (R.liftedPolicy ρ) := by
  have hno :=
    OpposingTypes.theorem4Problem11_no_extremes_of_pivotSupport_of_closedZ
      hn hbeta hbeta_half hpos hdec hpivot hclosed_first
  exact E.theorem4_misestimation_with_fairness_large_typeZero_from_reduction
    R reps (by omega : 1 < n) htrue hred heps hbase hdec
    (hpos OpposingTypes.theorem4FirstItem) hsmall ρ hno.1

/--
Theorem 4 fairness-constrained misestimation bridge, second true cold-start
type, using the Problem 11 pivot-support/closed-form certificate.
-/
theorem theorem4_misestimation_with_fairness_large_typeOne_from_problem11_certificate
    {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n)
    (R : ReductionWitness m n 3)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    {beta eps : ℝ} {v : Item n → ℝ}
    (hn : 2 < n)
    (htrue : E.trueModel = R.data.model)
    (hred :
      R.reduced = OpposingTypes.theorem4TrueReducedModelTypeOne beta v)
    (heps : 0 < eps)
    (hbase :
      (n : ℝ)⁻¹ <
        RecommendationModel.optimalUserFairnessAtLevel E.trueModel 1)
    (hbeta : (n : ℝ)⁻¹ < beta)
    (hbeta_half : beta < 1 / 2)
    (hdec : OpposingTypes.StrictlyDecreasingByIndex v)
    (hpos : ∀ j : Item n, 0 < v j)
    (hsmall : v (OpposingTypes.theorem4SecondItem (by omega : 1 < n)) <
      eps / (n : ℝ) * v OpposingTypes.theorem4FirstItem)
    (ρ : TypePolicy 3 n) (t : Item n)
    (hpivot : OpposingTypes.Theorem4Problem11PivotSupport ρ t)
    (hclosed_first :
      t = OpposingTypes.theorem4FirstItem →
        (ρ 2 OpposingTypes.theorem4FirstItem).toReal =
          OpposingTypes.theorem4Problem11PivotOneZ beta v) :
    1 - eps < E.priceOfMisestimation 1 (R.liftedPolicy ρ) := by
  have hno :=
    OpposingTypes.theorem4Problem11_no_extremes_of_pivotSupport_of_closedZ
      hn hbeta hbeta_half hpos hdec hpivot hclosed_first
  exact E.theorem4_misestimation_with_fairness_large_typeOne_from_reduction
    R reps (by omega : 1 < n) htrue hred heps hbase hdec
    (hpos OpposingTypes.theorem4FirstItem) hsmall ρ hno.2

/--
Theorem 4 fairness-constrained misestimation bridge, first true cold-start
type, from the equality-form Problem 11 optimum plus Lemma 13 pivot support.

The Lemma 15 pivot-one closed-coordinate calculation is discharged internally.
-/
theorem theorem4_misestimation_with_fairness_large_typeZero_from_equalized_problem11
    {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n)
    (R : ReductionWitness m n 3)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    {beta eps : ℝ} {v : Item n → ℝ}
    (hn : 2 < n)
    (htrue : E.trueModel = R.data.model)
    (hred :
      R.reduced = OpposingTypes.theorem4TrueReducedModelTypeZero beta v)
    (heps : 0 < eps)
    (hbase :
      (n : ℝ)⁻¹ <
        RecommendationModel.optimalUserFairnessAtLevel E.trueModel 1)
    (hbeta : (n : ℝ)⁻¹ < beta)
    (hbeta_half : beta < 1 / 2)
    (hdec : OpposingTypes.StrictlyDecreasingByIndex v)
    (hpos : ∀ j : Item n, 0 < v j)
    (hsmall : v (OpposingTypes.theorem4SecondItem (by omega : 1 < n)) <
      eps / (n : ℝ) * v OpposingTypes.theorem4FirstItem)
    (ρ : TypePolicy 3 n) (ell : ℝ) (t : Item n)
    (heq :
      OpposingTypes.Theorem4Problem11EqualizedBasicOptimal beta v ρ ell)
    (hpivot : OpposingTypes.Theorem4Problem11PivotSupport ρ t) :
    1 - eps < E.priceOfMisestimation 1 (R.liftedPolicy ρ) := by
  have hno :=
    OpposingTypes.theorem4Problem11_no_extremes_of_equalized_pivotSupport
      hn hbeta hbeta_half hpos hdec heq hpivot
  exact E.theorem4_misestimation_with_fairness_large_typeZero_from_reduction
    R reps (by omega : 1 < n) htrue hred heps hbase hdec
    (hpos OpposingTypes.theorem4FirstItem) hsmall ρ hno.1

/--
Theorem 4 fairness-constrained misestimation bridge, second true cold-start
type, from the equality-form Problem 11 optimum plus Lemma 13 pivot support.

The Lemma 15 pivot-one closed-coordinate calculation is discharged internally.
-/
theorem theorem4_misestimation_with_fairness_large_typeOne_from_equalized_problem11
    {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n)
    (R : ReductionWitness m n 3)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    {beta eps : ℝ} {v : Item n → ℝ}
    (hn : 2 < n)
    (htrue : E.trueModel = R.data.model)
    (hred :
      R.reduced = OpposingTypes.theorem4TrueReducedModelTypeOne beta v)
    (heps : 0 < eps)
    (hbase :
      (n : ℝ)⁻¹ <
        RecommendationModel.optimalUserFairnessAtLevel E.trueModel 1)
    (hbeta : (n : ℝ)⁻¹ < beta)
    (hbeta_half : beta < 1 / 2)
    (hdec : OpposingTypes.StrictlyDecreasingByIndex v)
    (hpos : ∀ j : Item n, 0 < v j)
    (hsmall : v (OpposingTypes.theorem4SecondItem (by omega : 1 < n)) <
      eps / (n : ℝ) * v OpposingTypes.theorem4FirstItem)
    (ρ : TypePolicy 3 n) (ell : ℝ) (t : Item n)
    (heq :
      OpposingTypes.Theorem4Problem11EqualizedBasicOptimal beta v ρ ell)
    (hpivot : OpposingTypes.Theorem4Problem11PivotSupport ρ t) :
    1 - eps < E.priceOfMisestimation 1 (R.liftedPolicy ρ) := by
  have hno :=
    OpposingTypes.theorem4Problem11_no_extremes_of_equalized_pivotSupport
      hn hbeta hbeta_half hpos hdec heq hpivot
  exact E.theorem4_misestimation_with_fairness_large_typeOne_from_reduction
    R reps (by omega : 1 < n) htrue hred heps hbase hdec
    (hpos OpposingTypes.theorem4FirstItem) hsmall ρ hno.2

/--
Theorem 4 fairness-constrained misestimation bridge, first true cold-start
type, from an equality-form Problem 11 optimum.  Lemma 13 pivot support and the
Lemma 15 pivot-one coordinate contradiction are discharged internally.
-/
theorem theorem4_misestimation_with_fairness_large_typeZero_from_equalized_problem11_auto
    {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n)
    (R : ReductionWitness m n 3)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    {beta eps : ℝ} {v : Item n → ℝ}
    (hn : 2 < n)
    (htrue : E.trueModel = R.data.model)
    (hred :
      R.reduced = OpposingTypes.theorem4TrueReducedModelTypeZero beta v)
    (heps : 0 < eps)
    (hbase :
      (n : ℝ)⁻¹ <
        RecommendationModel.optimalUserFairnessAtLevel E.trueModel 1)
    (hbeta : (n : ℝ)⁻¹ < beta)
    (hbeta_half : beta < 1 / 2)
    (hdec : OpposingTypes.StrictlyDecreasingByIndex v)
    (hpos : ∀ j : Item n, 0 < v j)
    (hsmall : v (OpposingTypes.theorem4SecondItem (by omega : 1 < n)) <
      eps / (n : ℝ) * v OpposingTypes.theorem4FirstItem)
    (ρ : TypePolicy 3 n) (ell : ℝ)
    (heq :
      OpposingTypes.Theorem4Problem11EqualizedBasicOptimal beta v ρ ell) :
    1 - eps < E.priceOfMisestimation 1 (R.liftedPolicy ρ) := by
  have hno :=
    OpposingTypes.theorem4Problem11_no_extremes_of_equalized
      hn hbeta hbeta_half hpos hdec heq
  exact E.theorem4_misestimation_with_fairness_large_typeZero_from_reduction
    R reps (by omega : 1 < n) htrue hred heps hbase hdec
    (hpos OpposingTypes.theorem4FirstItem) hsmall ρ hno.1

/--
Theorem 4 fairness-constrained misestimation bridge, second true cold-start
type, from an equality-form Problem 11 optimum.  Lemma 13 pivot support and the
Lemma 15 pivot-one coordinate contradiction are discharged internally.
-/
theorem theorem4_misestimation_with_fairness_large_typeOne_from_equalized_problem11_auto
    {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n)
    (R : ReductionWitness m n 3)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    {beta eps : ℝ} {v : Item n → ℝ}
    (hn : 2 < n)
    (htrue : E.trueModel = R.data.model)
    (hred :
      R.reduced = OpposingTypes.theorem4TrueReducedModelTypeOne beta v)
    (heps : 0 < eps)
    (hbase :
      (n : ℝ)⁻¹ <
        RecommendationModel.optimalUserFairnessAtLevel E.trueModel 1)
    (hbeta : (n : ℝ)⁻¹ < beta)
    (hbeta_half : beta < 1 / 2)
    (hdec : OpposingTypes.StrictlyDecreasingByIndex v)
    (hpos : ∀ j : Item n, 0 < v j)
    (hsmall : v (OpposingTypes.theorem4SecondItem (by omega : 1 < n)) <
      eps / (n : ℝ) * v OpposingTypes.theorem4FirstItem)
    (ρ : TypePolicy 3 n) (ell : ℝ)
    (heq :
      OpposingTypes.Theorem4Problem11EqualizedBasicOptimal beta v ρ ell) :
    1 - eps < E.priceOfMisestimation 1 (R.liftedPolicy ρ) := by
  have hno :=
    OpposingTypes.theorem4Problem11_no_extremes_of_equalized
      hn hbeta hbeta_half hpos hdec heq
  exact E.theorem4_misestimation_with_fairness_large_typeOne_from_reduction
    R reps (by omega : 1 < n) htrue hred heps hbase hdec
    (hpos OpposingTypes.theorem4FirstItem) hsmall ρ hno.2

/--
Theorem 4 fairness-constrained misestimation bridge, first true cold-start
type, from the paper's real equality-form Problem 11 optimal BFS data.
-/
theorem theorem4_misestimation_with_fairness_large_typeZero_from_equalityFormOptimalBFS
    {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n)
    (R : ReductionWitness m n 3)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    {beta eps : ℝ} {v x z : Item n → ℝ} {ell : ℝ}
    (hn : 2 < n)
    (htrue : E.trueModel = R.data.model)
    (hred :
      R.reduced = OpposingTypes.theorem4TrueReducedModelTypeZero beta v)
    (heps : 0 < eps)
    (hbase :
      (n : ℝ)⁻¹ <
        RecommendationModel.optimalUserFairnessAtLevel E.trueModel 1)
    (hbeta : (n : ℝ)⁻¹ < beta)
    (hbeta_half : beta < 1 / 2)
    (hdec : OpposingTypes.StrictlyDecreasingByIndex v)
    (hpos : ∀ j : Item n, 0 < v j)
    (hsmall : v (OpposingTypes.theorem4SecondItem (by omega : 1 < n)) <
      eps / (n : ℝ) * v OpposingTypes.theorem4FirstItem)
    (hbfs :
      OpposingTypes.Theorem4Problem11EqualityFormOptimalBFS beta v x z ell) :
    1 - eps <
      E.priceOfMisestimation 1
        (R.liftedPolicy
          (OpposingTypes.theorem4Problem11PolicyOfRealVectors x z
            hbfs.feasible.x_nonneg hbfs.feasible.z_nonneg
            hbfs.feasible.sum_x hbfs.feasible.sum_z)) := by
  let ρ : TypePolicy 3 n :=
    OpposingTypes.theorem4Problem11PolicyOfRealVectors x z
      hbfs.feasible.x_nonneg hbfs.feasible.z_nonneg
      hbfs.feasible.sum_x hbfs.feasible.sum_z
  have heq :
      OpposingTypes.Theorem4Problem11EqualizedBasicOptimal beta v ρ ell := by
    dsimp [ρ]
    exact OpposingTypes.theorem4Problem11EqualizedBasicOptimal_of_equalityFormOptimalBFS
      hbfs
  change 1 - eps < E.priceOfMisestimation 1 (R.liftedPolicy ρ)
  exact E.theorem4_misestimation_with_fairness_large_typeZero_from_equalized_problem11_auto
    R reps hn htrue hred heps hbase hbeta hbeta_half hdec hpos hsmall ρ ell heq

/--
Theorem 4 fairness-constrained misestimation bridge, second true cold-start
type, from the paper's real equality-form Problem 11 optimal BFS data.
-/
theorem theorem4_misestimation_with_fairness_large_typeOne_from_equalityFormOptimalBFS
    {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n)
    (R : ReductionWitness m n 3)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    {beta eps : ℝ} {v x z : Item n → ℝ} {ell : ℝ}
    (hn : 2 < n)
    (htrue : E.trueModel = R.data.model)
    (hred :
      R.reduced = OpposingTypes.theorem4TrueReducedModelTypeOne beta v)
    (heps : 0 < eps)
    (hbase :
      (n : ℝ)⁻¹ <
        RecommendationModel.optimalUserFairnessAtLevel E.trueModel 1)
    (hbeta : (n : ℝ)⁻¹ < beta)
    (hbeta_half : beta < 1 / 2)
    (hdec : OpposingTypes.StrictlyDecreasingByIndex v)
    (hpos : ∀ j : Item n, 0 < v j)
    (hsmall : v (OpposingTypes.theorem4SecondItem (by omega : 1 < n)) <
      eps / (n : ℝ) * v OpposingTypes.theorem4FirstItem)
    (hbfs :
      OpposingTypes.Theorem4Problem11EqualityFormOptimalBFS beta v x z ell) :
    1 - eps <
      E.priceOfMisestimation 1
        (R.liftedPolicy
          (OpposingTypes.theorem4Problem11PolicyOfRealVectors x z
            hbfs.feasible.x_nonneg hbfs.feasible.z_nonneg
            hbfs.feasible.sum_x hbfs.feasible.sum_z)) := by
  let ρ : TypePolicy 3 n :=
    OpposingTypes.theorem4Problem11PolicyOfRealVectors x z
      hbfs.feasible.x_nonneg hbfs.feasible.z_nonneg
      hbfs.feasible.sum_x hbfs.feasible.sum_z
  have heq :
      OpposingTypes.Theorem4Problem11EqualizedBasicOptimal beta v ρ ell := by
    dsimp [ρ]
    exact OpposingTypes.theorem4Problem11EqualizedBasicOptimal_of_equalityFormOptimalBFS
      hbfs
  change 1 - eps < E.priceOfMisestimation 1 (R.liftedPolicy ρ)
  exact E.theorem4_misestimation_with_fairness_large_typeOne_from_equalized_problem11_auto
    R reps hn htrue hred heps hbase hbeta hbeta_half hdec hpos hsmall ρ ell heq

theorem theorem4_misestimation_with_fairness_large_typeZero_from_closed_problem11_center
    {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n)
    (R : ReductionWitness m n 3)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    {beta eps : ℝ} {v : Item n → ℝ} {c : Item n}
    (hn : 2 < n)
    (htrue : E.trueModel = R.data.model)
    (hred :
      R.reduced = OpposingTypes.theorem4TrueReducedModelTypeZero beta v)
    (heps : 0 < eps)
    (hbase :
      (n : ℝ)⁻¹ <
        RecommendationModel.optimalUserFairnessAtLevel E.trueModel 1)
    (hbeta : (n : ℝ)⁻¹ < beta)
    (hbeta_half : beta < 1 / 2)
    (hdec : OpposingTypes.StrictlyDecreasingByIndex v)
    (hpos : ∀ j : Item n, 0 < v j)
    (hsmall : v (OpposingTypes.theorem4SecondItem (by omega : 1 < n)) <
      eps / (n : ℝ) * v OpposingTypes.theorem4FirstItem)
    (hcenter : c.val = (OpposingTypes.reverseItem c).val) :
    ∃ ρ : TypePolicy 3 n,
      1 - eps < E.priceOfMisestimation 1 (R.liftedPolicy ρ) := by
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hbeta_pos : 0 < beta :=
    lt_trans (inv_pos.mpr hnpos) hbeta
  rcases OpposingTypes.theorem4Problem11EqualityFormOptimalBFS_exists_closed_of_center
      hbeta_pos hbeta_half hpos hdec hcenter with
    ⟨t, hbfs⟩
  let ρ : TypePolicy 3 n :=
    OpposingTypes.theorem4Problem11PolicyOfRealVectors
      (OpposingTypes.theorem4Problem11ClosedX beta v t)
      (OpposingTypes.theorem4Problem11ClosedZ beta v t)
      hbfs.feasible.x_nonneg hbfs.feasible.z_nonneg
      hbfs.feasible.sum_x hbfs.feasible.sum_z
  refine ⟨ρ, ?_⟩
  dsimp [ρ]
  exact E.theorem4_misestimation_with_fairness_large_typeZero_from_equalityFormOptimalBFS
    R reps hn htrue hred heps hbase hbeta hbeta_half hdec hpos hsmall hbfs

theorem theorem4_misestimation_with_fairness_large_typeOne_from_closed_problem11_center
    {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n)
    (R : ReductionWitness m n 3)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    {beta eps : ℝ} {v : Item n → ℝ} {c : Item n}
    (hn : 2 < n)
    (htrue : E.trueModel = R.data.model)
    (hred :
      R.reduced = OpposingTypes.theorem4TrueReducedModelTypeOne beta v)
    (heps : 0 < eps)
    (hbase :
      (n : ℝ)⁻¹ <
        RecommendationModel.optimalUserFairnessAtLevel E.trueModel 1)
    (hbeta : (n : ℝ)⁻¹ < beta)
    (hbeta_half : beta < 1 / 2)
    (hdec : OpposingTypes.StrictlyDecreasingByIndex v)
    (hpos : ∀ j : Item n, 0 < v j)
    (hsmall : v (OpposingTypes.theorem4SecondItem (by omega : 1 < n)) <
      eps / (n : ℝ) * v OpposingTypes.theorem4FirstItem)
    (hcenter : c.val = (OpposingTypes.reverseItem c).val) :
    ∃ ρ : TypePolicy 3 n,
      1 - eps < E.priceOfMisestimation 1 (R.liftedPolicy ρ) := by
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hbeta_pos : 0 < beta :=
    lt_trans (inv_pos.mpr hnpos) hbeta
  rcases OpposingTypes.theorem4Problem11EqualityFormOptimalBFS_exists_closed_of_center
      hbeta_pos hbeta_half hpos hdec hcenter with
    ⟨t, hbfs⟩
  let ρ : TypePolicy 3 n :=
    OpposingTypes.theorem4Problem11PolicyOfRealVectors
      (OpposingTypes.theorem4Problem11ClosedX beta v t)
      (OpposingTypes.theorem4Problem11ClosedZ beta v t)
      hbfs.feasible.x_nonneg hbfs.feasible.z_nonneg
      hbfs.feasible.sum_x hbfs.feasible.sum_z
  refine ⟨ρ, ?_⟩
  dsimp [ρ]
  exact E.theorem4_misestimation_with_fairness_large_typeOne_from_equalityFormOptimalBFS
    R reps hn htrue hred heps hbase hbeta hbeta_half hdec hpos hsmall hbfs

theorem theorem4_misestimation_with_fairness_large_typeZero_from_closed_problem11_succ_center
    {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n)
    (R : ReductionWitness m n 3)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    {beta eps : ℝ} {v : Item n → ℝ} {c : Item n}
    (hn : 2 < n)
    (htrue : E.trueModel = R.data.model)
    (hred :
      R.reduced = OpposingTypes.theorem4TrueReducedModelTypeZero beta v)
    (heps : 0 < eps)
    (hbase :
      (n : ℝ)⁻¹ <
        RecommendationModel.optimalUserFairnessAtLevel E.trueModel 1)
    (hbeta : (n : ℝ)⁻¹ < beta)
    (hbeta_half : beta < 1 / 2)
    (hdec : OpposingTypes.StrictlyDecreasingByIndex v)
    (hpos : ∀ j : Item n, 0 < v j)
    (hsmall : v (OpposingTypes.theorem4SecondItem (by omega : 1 < n)) <
      eps / (n : ℝ) * v OpposingTypes.theorem4FirstItem)
    (hsucc : c.val + 1 = (OpposingTypes.reverseItem c).val) :
    ∃ ρ : TypePolicy 3 n,
      1 - eps < E.priceOfMisestimation 1 (R.liftedPolicy ρ) := by
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hbeta_pos : 0 < beta :=
    lt_trans (inv_pos.mpr hnpos) hbeta
  rcases OpposingTypes.theorem4Problem11EqualityFormOptimalBFS_exists_closed_of_succ_center
      hbeta_pos hbeta_half hpos hdec hsucc with
    ⟨t, hbfs⟩
  let ρ : TypePolicy 3 n :=
    OpposingTypes.theorem4Problem11PolicyOfRealVectors
      (OpposingTypes.theorem4Problem11ClosedX beta v t)
      (OpposingTypes.theorem4Problem11ClosedZ beta v t)
      hbfs.feasible.x_nonneg hbfs.feasible.z_nonneg
      hbfs.feasible.sum_x hbfs.feasible.sum_z
  refine ⟨ρ, ?_⟩
  dsimp [ρ]
  exact E.theorem4_misestimation_with_fairness_large_typeZero_from_equalityFormOptimalBFS
    R reps hn htrue hred heps hbase hbeta hbeta_half hdec hpos hsmall hbfs

theorem theorem4_misestimation_with_fairness_large_typeOne_from_closed_problem11_succ_center
    {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n)
    (R : ReductionWitness m n 3)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    {beta eps : ℝ} {v : Item n → ℝ} {c : Item n}
    (hn : 2 < n)
    (htrue : E.trueModel = R.data.model)
    (hred :
      R.reduced = OpposingTypes.theorem4TrueReducedModelTypeOne beta v)
    (heps : 0 < eps)
    (hbase :
      (n : ℝ)⁻¹ <
        RecommendationModel.optimalUserFairnessAtLevel E.trueModel 1)
    (hbeta : (n : ℝ)⁻¹ < beta)
    (hbeta_half : beta < 1 / 2)
    (hdec : OpposingTypes.StrictlyDecreasingByIndex v)
    (hpos : ∀ j : Item n, 0 < v j)
    (hsmall : v (OpposingTypes.theorem4SecondItem (by omega : 1 < n)) <
      eps / (n : ℝ) * v OpposingTypes.theorem4FirstItem)
    (hsucc : c.val + 1 = (OpposingTypes.reverseItem c).val) :
    ∃ ρ : TypePolicy 3 n,
      1 - eps < E.priceOfMisestimation 1 (R.liftedPolicy ρ) := by
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hbeta_pos : 0 < beta :=
    lt_trans (inv_pos.mpr hnpos) hbeta
  rcases OpposingTypes.theorem4Problem11EqualityFormOptimalBFS_exists_closed_of_succ_center
      hbeta_pos hbeta_half hpos hdec hsucc with
    ⟨t, hbfs⟩
  let ρ : TypePolicy 3 n :=
    OpposingTypes.theorem4Problem11PolicyOfRealVectors
      (OpposingTypes.theorem4Problem11ClosedX beta v t)
      (OpposingTypes.theorem4Problem11ClosedZ beta v t)
      hbfs.feasible.x_nonneg hbfs.feasible.z_nonneg
      hbfs.feasible.sum_x hbfs.feasible.sum_z
  refine ⟨ρ, ?_⟩
  dsimp [ρ]
  exact E.theorem4_misestimation_with_fairness_large_typeOne_from_equalityFormOptimalBFS
    R reps hn htrue hred heps hbase hbeta hbeta_half hdec hpos hsmall hbfs

/--
Theorem 4 closed Problem 11 construction, first true cold-start row, with the
paper's geometric value vector instantiated.
-/
theorem theorem4_misestimation_with_fairness_large_typeZero_from_smallValueVector_closed_problem11_center
    {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n)
    (R : ReductionWitness m n 3)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    {beta eps : ℝ} {c : Item n}
    (hn : 2 < n)
    (htrue : E.trueModel = R.data.model)
    (hred :
      R.reduced = OpposingTypes.theorem4TrueReducedModelTypeZero beta
        (OpposingTypes.theorem4SmallValueVector (n := n) eps))
    (heps : 0 < eps)
    (hbase :
      (n : ℝ)⁻¹ <
        RecommendationModel.optimalUserFairnessAtLevel E.trueModel 1)
    (hbeta : (n : ℝ)⁻¹ < beta)
    (hbeta_half : beta < 1 / 2)
    (hcenter : c.val = (OpposingTypes.reverseItem c).val) :
    ∃ ρ : TypePolicy 3 n,
      1 - eps < E.priceOfMisestimation 1 (R.liftedPolicy ρ) := by
  have hsmall :
      OpposingTypes.theorem4SmallValueVector (n := n) eps
          (OpposingTypes.theorem4SecondItem (by omega : 1 < n)) <
        eps / (n : ℝ) *
          OpposingTypes.theorem4SmallValueVector (n := n) eps
            OpposingTypes.theorem4FirstItem := by
    rw [OpposingTypes.theorem4SmallValueVector_first_eq_one (n := n) (eps := eps),
      OpposingTypes.theorem4SmallValueVector_second_eq_ratio
        (n := n) (eps := eps) (by omega : 1 < n)]
    simpa using
      OpposingTypes.theorem4SmallValueVector_ratio_lt_eps_div_card
        (n := n) (eps := eps) heps
  exact E.theorem4_misestimation_with_fairness_large_typeZero_from_closed_problem11_center
    R reps hn htrue hred heps hbase hbeta hbeta_half
    (OpposingTypes.theorem4SmallValueVector_strictlyDecreasing
      (n := n) (eps := eps) heps)
    (OpposingTypes.theorem4SmallValueVector_pos
      (n := n) (eps := eps) heps)
    hsmall hcenter

/--
Theorem 4 closed Problem 11 construction, second true cold-start row, with the
paper's geometric value vector instantiated.
-/
theorem theorem4_misestimation_with_fairness_large_typeOne_from_smallValueVector_closed_problem11_center
    {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n)
    (R : ReductionWitness m n 3)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    {beta eps : ℝ} {c : Item n}
    (hn : 2 < n)
    (htrue : E.trueModel = R.data.model)
    (hred :
      R.reduced = OpposingTypes.theorem4TrueReducedModelTypeOne beta
        (OpposingTypes.theorem4SmallValueVector (n := n) eps))
    (heps : 0 < eps)
    (hbase :
      (n : ℝ)⁻¹ <
        RecommendationModel.optimalUserFairnessAtLevel E.trueModel 1)
    (hbeta : (n : ℝ)⁻¹ < beta)
    (hbeta_half : beta < 1 / 2)
    (hcenter : c.val = (OpposingTypes.reverseItem c).val) :
    ∃ ρ : TypePolicy 3 n,
      1 - eps < E.priceOfMisestimation 1 (R.liftedPolicy ρ) := by
  have hsmall :
      OpposingTypes.theorem4SmallValueVector (n := n) eps
          (OpposingTypes.theorem4SecondItem (by omega : 1 < n)) <
        eps / (n : ℝ) *
          OpposingTypes.theorem4SmallValueVector (n := n) eps
            OpposingTypes.theorem4FirstItem := by
    rw [OpposingTypes.theorem4SmallValueVector_first_eq_one (n := n) (eps := eps),
      OpposingTypes.theorem4SmallValueVector_second_eq_ratio
        (n := n) (eps := eps) (by omega : 1 < n)]
    simpa using
      OpposingTypes.theorem4SmallValueVector_ratio_lt_eps_div_card
        (n := n) (eps := eps) heps
  exact E.theorem4_misestimation_with_fairness_large_typeOne_from_closed_problem11_center
    R reps hn htrue hred heps hbase hbeta hbeta_half
    (OpposingTypes.theorem4SmallValueVector_strictlyDecreasing
      (n := n) (eps := eps) heps)
    (OpposingTypes.theorem4SmallValueVector_pos
      (n := n) (eps := eps) heps)
    hsmall hcenter

/--
Theorem 4 closed Problem 11 construction, first true cold-start row and even
midpoint, with the paper's geometric value vector instantiated.
-/
theorem theorem4_misestimation_with_fairness_large_typeZero_from_smallValueVector_closed_problem11_succ_center
    {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n)
    (R : ReductionWitness m n 3)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    {beta eps : ℝ} {c : Item n}
    (hn : 2 < n)
    (htrue : E.trueModel = R.data.model)
    (hred :
      R.reduced = OpposingTypes.theorem4TrueReducedModelTypeZero beta
        (OpposingTypes.theorem4SmallValueVector (n := n) eps))
    (heps : 0 < eps)
    (hbase :
      (n : ℝ)⁻¹ <
        RecommendationModel.optimalUserFairnessAtLevel E.trueModel 1)
    (hbeta : (n : ℝ)⁻¹ < beta)
    (hbeta_half : beta < 1 / 2)
    (hsucc : c.val + 1 = (OpposingTypes.reverseItem c).val) :
    ∃ ρ : TypePolicy 3 n,
      1 - eps < E.priceOfMisestimation 1 (R.liftedPolicy ρ) := by
  have hsmall :
      OpposingTypes.theorem4SmallValueVector (n := n) eps
          (OpposingTypes.theorem4SecondItem (by omega : 1 < n)) <
        eps / (n : ℝ) *
          OpposingTypes.theorem4SmallValueVector (n := n) eps
            OpposingTypes.theorem4FirstItem := by
    rw [OpposingTypes.theorem4SmallValueVector_first_eq_one (n := n) (eps := eps),
      OpposingTypes.theorem4SmallValueVector_second_eq_ratio
        (n := n) (eps := eps) (by omega : 1 < n)]
    simpa using
      OpposingTypes.theorem4SmallValueVector_ratio_lt_eps_div_card
        (n := n) (eps := eps) heps
  exact E.theorem4_misestimation_with_fairness_large_typeZero_from_closed_problem11_succ_center
    R reps hn htrue hred heps hbase hbeta hbeta_half
    (OpposingTypes.theorem4SmallValueVector_strictlyDecreasing
      (n := n) (eps := eps) heps)
    (OpposingTypes.theorem4SmallValueVector_pos
      (n := n) (eps := eps) heps)
    hsmall hsucc

/--
Theorem 4 closed Problem 11 construction, second true cold-start row and even
midpoint, with the paper's geometric value vector instantiated.
-/
theorem theorem4_misestimation_with_fairness_large_typeOne_from_smallValueVector_closed_problem11_succ_center
    {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n)
    (R : ReductionWitness m n 3)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    {beta eps : ℝ} {c : Item n}
    (hn : 2 < n)
    (htrue : E.trueModel = R.data.model)
    (hred :
      R.reduced = OpposingTypes.theorem4TrueReducedModelTypeOne beta
        (OpposingTypes.theorem4SmallValueVector (n := n) eps))
    (heps : 0 < eps)
    (hbase :
      (n : ℝ)⁻¹ <
        RecommendationModel.optimalUserFairnessAtLevel E.trueModel 1)
    (hbeta : (n : ℝ)⁻¹ < beta)
    (hbeta_half : beta < 1 / 2)
    (hsucc : c.val + 1 = (OpposingTypes.reverseItem c).val) :
    ∃ ρ : TypePolicy 3 n,
      1 - eps < E.priceOfMisestimation 1 (R.liftedPolicy ρ) := by
  have hsmall :
      OpposingTypes.theorem4SmallValueVector (n := n) eps
          (OpposingTypes.theorem4SecondItem (by omega : 1 < n)) <
        eps / (n : ℝ) *
          OpposingTypes.theorem4SmallValueVector (n := n) eps
            OpposingTypes.theorem4FirstItem := by
    rw [OpposingTypes.theorem4SmallValueVector_first_eq_one (n := n) (eps := eps),
      OpposingTypes.theorem4SmallValueVector_second_eq_ratio
        (n := n) (eps := eps) (by omega : 1 < n)]
    simpa using
      OpposingTypes.theorem4SmallValueVector_ratio_lt_eps_div_card
        (n := n) (eps := eps) heps
  exact E.theorem4_misestimation_with_fairness_large_typeOne_from_closed_problem11_succ_center
    R reps hn htrue hred heps hbase hbeta hbeta_half
    (OpposingTypes.theorem4SmallValueVector_strictlyDecreasing
      (n := n) (eps := eps) heps)
    (OpposingTypes.theorem4SmallValueVector_pos
      (n := n) (eps := eps) heps)
    hsmall hsucc

/--
Theorem 4, both bullets for the first true cold-start row and odd midpoint,
using the paper's geometric value vector and the closed Problem 11 witness.
-/
theorem theorem4_misestimation_tradeoff_typeZero_from_smallValueVector_closed_problem11_center
    {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n)
    (R : ReductionWitness m n 3)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    {beta eps : ℝ} {c : Item n}
    (hn : 2 < n)
    (htrue : E.trueModel = R.data.model)
    (hred :
      R.reduced = OpposingTypes.theorem4TrueReducedModelTypeZero beta
        (OpposingTypes.theorem4SmallValueVector (n := n) eps))
    (heps : 0 < eps)
    (hbase :
      (n : ℝ)⁻¹ <
        RecommendationModel.optimalUserFairnessAtLevel E.trueModel 1)
    (hbeta : (n : ℝ)⁻¹ < beta)
    (hbeta_half : beta < 1 / 2)
    (hcenter : c.val = (OpposingTypes.reverseItem c).val) :
    E.priceOfMisestimation 0
        (R.liftedPolicy
          (OpposingTypes.theorem4NoFairnessPolicyTypeZero
            (OpposingTypes.theorem4SmallValueVector (n := n) eps))) ≤
      (1 / 2 : ℝ) ∧
    ∃ ρ : TypePolicy 3 n,
      1 - eps < E.priceOfMisestimation 1 (R.liftedPolicy ρ) := by
  have hpos :
      ∀ j : Item n,
        0 < OpposingTypes.theorem4SmallValueVector (n := n) eps j :=
    OpposingTypes.theorem4SmallValueVector_pos (n := n) (eps := eps) heps
  have hdec :
      OpposingTypes.StrictlyDecreasingByIndex
        (OpposingTypes.theorem4SmallValueVector (n := n) eps) :=
    OpposingTypes.theorem4SmallValueVector_strictlyDecreasing
      (n := n) (eps := eps) heps
  constructor
  · exact E.theorem4_misestimation_without_fairness_le_half_typeZero_from_reduction
      R reps htrue hred hpos hdec
  · exact E.theorem4_misestimation_with_fairness_large_typeZero_from_smallValueVector_closed_problem11_center
      R reps hn htrue hred heps hbase hbeta hbeta_half hcenter

/--
Theorem 4, both bullets for the second true cold-start row and odd midpoint,
using the paper's geometric value vector and the closed Problem 11 witness.
-/
theorem theorem4_misestimation_tradeoff_typeOne_from_smallValueVector_closed_problem11_center
    {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n)
    (R : ReductionWitness m n 3)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    {beta eps : ℝ} {c : Item n}
    (hn : 2 < n)
    (htrue : E.trueModel = R.data.model)
    (hred :
      R.reduced = OpposingTypes.theorem4TrueReducedModelTypeOne beta
        (OpposingTypes.theorem4SmallValueVector (n := n) eps))
    (heps : 0 < eps)
    (hbase :
      (n : ℝ)⁻¹ <
        RecommendationModel.optimalUserFairnessAtLevel E.trueModel 1)
    (hbeta : (n : ℝ)⁻¹ < beta)
    (hbeta_half : beta < 1 / 2)
    (hcenter : c.val = (OpposingTypes.reverseItem c).val) :
    E.priceOfMisestimation 0
        (R.liftedPolicy
          (OpposingTypes.theorem4NoFairnessPolicyTypeOne
            (OpposingTypes.theorem4SmallValueVector (n := n) eps))) ≤
      (1 / 2 : ℝ) ∧
    ∃ ρ : TypePolicy 3 n,
      1 - eps < E.priceOfMisestimation 1 (R.liftedPolicy ρ) := by
  have hpos :
      ∀ j : Item n,
        0 < OpposingTypes.theorem4SmallValueVector (n := n) eps j :=
    OpposingTypes.theorem4SmallValueVector_pos (n := n) (eps := eps) heps
  have hdec :
      OpposingTypes.StrictlyDecreasingByIndex
        (OpposingTypes.theorem4SmallValueVector (n := n) eps) :=
    OpposingTypes.theorem4SmallValueVector_strictlyDecreasing
      (n := n) (eps := eps) heps
  constructor
  · exact E.theorem4_misestimation_without_fairness_le_half_typeOne_from_reduction
      R reps htrue hred hpos hdec
  · exact E.theorem4_misestimation_with_fairness_large_typeOne_from_smallValueVector_closed_problem11_center
      R reps hn htrue hred heps hbase hbeta hbeta_half hcenter

/--
Theorem 4, both bullets for the first true cold-start row and even midpoint,
using the paper's geometric value vector and the closed Problem 11 witness.
-/
theorem theorem4_misestimation_tradeoff_typeZero_from_smallValueVector_closed_problem11_succ_center
    {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n)
    (R : ReductionWitness m n 3)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    {beta eps : ℝ} {c : Item n}
    (hn : 2 < n)
    (htrue : E.trueModel = R.data.model)
    (hred :
      R.reduced = OpposingTypes.theorem4TrueReducedModelTypeZero beta
        (OpposingTypes.theorem4SmallValueVector (n := n) eps))
    (heps : 0 < eps)
    (hbase :
      (n : ℝ)⁻¹ <
        RecommendationModel.optimalUserFairnessAtLevel E.trueModel 1)
    (hbeta : (n : ℝ)⁻¹ < beta)
    (hbeta_half : beta < 1 / 2)
    (hsucc : c.val + 1 = (OpposingTypes.reverseItem c).val) :
    E.priceOfMisestimation 0
        (R.liftedPolicy
          (OpposingTypes.theorem4NoFairnessPolicyTypeZero
            (OpposingTypes.theorem4SmallValueVector (n := n) eps))) ≤
      (1 / 2 : ℝ) ∧
    ∃ ρ : TypePolicy 3 n,
      1 - eps < E.priceOfMisestimation 1 (R.liftedPolicy ρ) := by
  have hpos :
      ∀ j : Item n,
        0 < OpposingTypes.theorem4SmallValueVector (n := n) eps j :=
    OpposingTypes.theorem4SmallValueVector_pos (n := n) (eps := eps) heps
  have hdec :
      OpposingTypes.StrictlyDecreasingByIndex
        (OpposingTypes.theorem4SmallValueVector (n := n) eps) :=
    OpposingTypes.theorem4SmallValueVector_strictlyDecreasing
      (n := n) (eps := eps) heps
  constructor
  · exact E.theorem4_misestimation_without_fairness_le_half_typeZero_from_reduction
      R reps htrue hred hpos hdec
  · exact E.theorem4_misestimation_with_fairness_large_typeZero_from_smallValueVector_closed_problem11_succ_center
      R reps hn htrue hred heps hbase hbeta hbeta_half hsucc

/--
Theorem 4, both bullets for the second true cold-start row and even midpoint,
using the paper's geometric value vector and the closed Problem 11 witness.
-/
theorem theorem4_misestimation_tradeoff_typeOne_from_smallValueVector_closed_problem11_succ_center
    {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n)
    (R : ReductionWitness m n 3)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    {beta eps : ℝ} {c : Item n}
    (hn : 2 < n)
    (htrue : E.trueModel = R.data.model)
    (hred :
      R.reduced = OpposingTypes.theorem4TrueReducedModelTypeOne beta
        (OpposingTypes.theorem4SmallValueVector (n := n) eps))
    (heps : 0 < eps)
    (hbase :
      (n : ℝ)⁻¹ <
        RecommendationModel.optimalUserFairnessAtLevel E.trueModel 1)
    (hbeta : (n : ℝ)⁻¹ < beta)
    (hbeta_half : beta < 1 / 2)
    (hsucc : c.val + 1 = (OpposingTypes.reverseItem c).val) :
    E.priceOfMisestimation 0
        (R.liftedPolicy
          (OpposingTypes.theorem4NoFairnessPolicyTypeOne
            (OpposingTypes.theorem4SmallValueVector (n := n) eps))) ≤
      (1 / 2 : ℝ) ∧
    ∃ ρ : TypePolicy 3 n,
      1 - eps < E.priceOfMisestimation 1 (R.liftedPolicy ρ) := by
  have hpos :
      ∀ j : Item n,
        0 < OpposingTypes.theorem4SmallValueVector (n := n) eps j :=
    OpposingTypes.theorem4SmallValueVector_pos (n := n) (eps := eps) heps
  have hdec :
      OpposingTypes.StrictlyDecreasingByIndex
        (OpposingTypes.theorem4SmallValueVector (n := n) eps) :=
    OpposingTypes.theorem4SmallValueVector_strictlyDecreasing
      (n := n) (eps := eps) heps
  constructor
  · exact E.theorem4_misestimation_without_fairness_le_half_typeOne_from_reduction
      R reps htrue hred hpos hdec
  · exact E.theorem4_misestimation_with_fairness_large_typeOne_from_smallValueVector_closed_problem11_succ_center
      R reps hn htrue hred heps hbase hbeta hbeta_half hsucc

/--
Theorem 4 fairness-constrained misestimation bridge, first true cold-start
type, from the equality-form Problem 11 optimum plus the two no-gap
conclusions that complete Appendix E Lemma 13.
-/
theorem theorem4_misestimation_with_fairness_large_typeZero_from_equalized_problem11_noGap
    {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n)
    (R : ReductionWitness m n 3)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    {beta eps : ℝ} {v : Item n → ℝ}
    (hn : 2 < n)
    (htrue : E.trueModel = R.data.model)
    (hred :
      R.reduced = OpposingTypes.theorem4TrueReducedModelTypeZero beta v)
    (heps : 0 < eps)
    (hbase :
      (n : ℝ)⁻¹ <
        RecommendationModel.optimalUserFairnessAtLevel E.trueModel 1)
    (hbeta : (n : ℝ)⁻¹ < beta)
    (hbeta_half : beta < 1 / 2)
    (hdec : OpposingTypes.StrictlyDecreasingByIndex v)
    (hpos : ∀ j : Item n, 0 < v j)
    (hsmall : v (OpposingTypes.theorem4SecondItem (by omega : 1 < n)) <
      eps / (n : ℝ) * v OpposingTypes.theorem4FirstItem)
    (ρ : TypePolicy 3 n) (ell : ℝ)
    (heq :
      OpposingTypes.Theorem4Problem11EqualizedBasicOptimal beta v ρ ell)
    (hx : OpposingTypes.Theorem4Problem11TypeZeroZeroClosed ρ)
    (hz : OpposingTypes.Theorem4Problem11ColdStartPositiveClosed ρ) :
    1 - eps < E.priceOfMisestimation 1 (R.liftedPolicy ρ) := by
  have hno :=
    OpposingTypes.theorem4Problem11_no_extremes_of_equalized_noGap
      hn hbeta hbeta_half hpos hdec heq hx hz
  exact E.theorem4_misestimation_with_fairness_large_typeZero_from_reduction
    R reps (by omega : 1 < n) htrue hred heps hbase hdec
    (hpos OpposingTypes.theorem4FirstItem) hsmall ρ hno.1

/--
Theorem 4 fairness-constrained misestimation bridge, second true cold-start
type, from the equality-form Problem 11 optimum plus the two no-gap
conclusions that complete Appendix E Lemma 13.
-/
theorem theorem4_misestimation_with_fairness_large_typeOne_from_equalized_problem11_noGap
    {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n)
    (R : ReductionWitness m n 3)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    {beta eps : ℝ} {v : Item n → ℝ}
    (hn : 2 < n)
    (htrue : E.trueModel = R.data.model)
    (hred :
      R.reduced = OpposingTypes.theorem4TrueReducedModelTypeOne beta v)
    (heps : 0 < eps)
    (hbase :
      (n : ℝ)⁻¹ <
        RecommendationModel.optimalUserFairnessAtLevel E.trueModel 1)
    (hbeta : (n : ℝ)⁻¹ < beta)
    (hbeta_half : beta < 1 / 2)
    (hdec : OpposingTypes.StrictlyDecreasingByIndex v)
    (hpos : ∀ j : Item n, 0 < v j)
    (hsmall : v (OpposingTypes.theorem4SecondItem (by omega : 1 < n)) <
      eps / (n : ℝ) * v OpposingTypes.theorem4FirstItem)
    (ρ : TypePolicy 3 n) (ell : ℝ)
    (heq :
      OpposingTypes.Theorem4Problem11EqualizedBasicOptimal beta v ρ ell)
    (hx : OpposingTypes.Theorem4Problem11TypeZeroZeroClosed ρ)
    (hz : OpposingTypes.Theorem4Problem11ColdStartPositiveClosed ρ) :
    1 - eps < E.priceOfMisestimation 1 (R.liftedPolicy ρ) := by
  have hno :=
    OpposingTypes.theorem4Problem11_no_extremes_of_equalized_noGap
      hn hbeta hbeta_half hpos hdec heq hx hz
  exact E.theorem4_misestimation_with_fairness_large_typeOne_from_reduction
    R reps (by omega : 1 < n) htrue hred heps hbase hdec
    (hpos OpposingTypes.theorem4FirstItem) hsmall ρ hno.2

end EstimatedRecommendationModel
end GCG24UserItemFairness
