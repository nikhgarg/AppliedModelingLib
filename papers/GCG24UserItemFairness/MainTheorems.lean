import GCG24UserItemFairness.Misestimation

/-!
# Paper-Facing Theorems: User-Item Fairness Tradeoffs in Recommendations

This file is the public theorem interface for the user-item fairness
formalization. Detailed LP, symmetry, and utility-preservation lemmas live in
the sibling files.
-/

namespace GCG24UserItemFairness
namespace ReductionWitness

/--
Symmetric item-fairness reduction theorem.

The item-fairness values attainable by type-symmetric user-level policies are
exactly the values attainable by the reduced type-level problem.
-/
theorem paper_symmetric_item_fairness_value_set_reduction
    {m n K : ℕ} [NeZero m] [NeZero n] [NeZero K]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types) :
    RecommendationModel.symmetricAttainableItemFairnessSet R.data =
      TypeWeightedRecommendationModel.attainableItemFairnessSet R.reduced := by
  exact R.symmetricAttainableItemFairnessSet_eq_reduced reps

/--
Symmetric optimal item-fairness reduction theorem.

The optimum item-fairness value over type-symmetric user-level policies equals
the optimum item-fairness value in the reduced type-level problem.
-/
theorem paper_symmetric_optimal_item_fairness_reduction
    {m n K : ℕ} [NeZero m] [NeZero n] [NeZero K]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types) :
    RecommendationModel.symmetricOptimalItemFairness R.data =
      TypeWeightedRecommendationModel.optimalItemFairness R.reduced := by
  exact R.symmetricOptimalItemFairness_eq_reduced reps

/--
Proposition 1 symmetric LP-reduction target.

Every type-symmetric original optimal policy is represented by a reduced
type-level policy. This is the unconditional part of the paper's symmetry
reduction that follows from chosen representatives for each user type.
-/
theorem paper_symmetric_lp_reduction_target
    {m n K : ℕ} [NeZero m] [NeZero n] [NeZero K]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (γ : ℝ) :
    LPReductionTarget R γ := by
  exact lpReductionTarget_of_representatives R reps γ

/--
Proposition 1, paper-named wrapper for the symmetric LP-reduction target used
by Theorems 3 and 4.
-/
theorem paper_proposition1_symmetric_lp_reduction_target
    {m n K : ℕ} [NeZero m] [NeZero n] [NeZero K]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (γ : ℝ) :
    LPReductionTarget R γ := by
  exact paper_symmetric_lp_reduction_target R reps γ

/--
Pointwise form of the symmetric LP-reduction target.

If a user-level optimum is already type-symmetric, then it is exactly the lift
of some type-level policy.
-/
theorem paper_symmetric_original_optimum_has_type_representative
    {m n K : ℕ} [NeZero m] [NeZero n] [NeZero K]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (γ : ℝ) {ρ : Policy m n}
    (hρ : UserTypeAssignment.IsTypeSymmetric R.data.types ρ)
    (hopt : RecommendationModel.IsOptimalAtLevel R.data.model γ ρ) :
    ∃ ρK : TypePolicy K n, R.liftedPolicy ρK = ρ := by
  exact lpReductionTarget_of_representatives R reps γ ρ ⟨hρ, hopt⟩

/--
Proposition 1, pointwise paper-named wrapper: a symmetric user-level optimum
has a reduced type-policy representative.
-/
theorem paper_proposition1_symmetric_original_optimum_has_type_representative
    {m n K : ℕ} [NeZero m] [NeZero n] [NeZero K]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (γ : ℝ) {ρ : Policy m n}
    (hρ : UserTypeAssignment.IsTypeSymmetric R.data.types ρ)
    (hopt : RecommendationModel.IsOptimalAtLevel R.data.model γ ρ) :
    ∃ ρK : TypePolicy K n, R.liftedPolicy ρK = ρ := by
  exact paper_symmetric_original_optimum_has_type_representative
    R reps γ hρ hopt

/--
Original/reduced optimal user-fairness value reduction.

This replaces the earlier opaque optimal-value equality assumption with the
standard side conditions needed to reason about `sSup` on real-valued feasible
sets: both feasible value sets are nonempty and bounded above.
-/
theorem paper_original_reduced_user_optimal_value_reduction
    {m n K : ℕ} [NeZero m] [NeZero n] [NeZero K]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (hRow : R.data.model.RowHasPositiveItem)
    (γ : ℝ)
    (hOrigNonempty :
      (RecommendationModel.attainableUserFairnessAtLevel R.data.model γ).Nonempty)
    (hOrigBdd :
      BddAbove (RecommendationModel.attainableUserFairnessAtLevel R.data.model γ))
    (hRedNonempty :
      (TypeWeightedRecommendationModel.attainableTypeFairnessAtLevel
        R.reduced γ).Nonempty)
    (hRedBdd :
      BddAbove (TypeWeightedRecommendationModel.attainableTypeFairnessAtLevel
        R.reduced γ)) :
    RecommendationModel.optimalUserFairnessAtLevel R.data.model γ =
      TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel R.reduced γ := by
  exact R.optimalUserFairnessAtLevel_eq_reduced_of_bddAbove_nonempty
    reps hRow γ hOrigNonempty hOrigBdd hRedNonempty hRedBdd

/--
Original/reduced optimal user-fairness value reduction with automatic
boundedness.

The remaining side condition is now only nonemptiness of the original and
reduced feasible value sets; row positivity gives the common `≤ 1` upper bound.
-/
theorem paper_original_reduced_user_optimal_value_reduction_of_nonempty
    {m n K : ℕ} [NeZero m] [NeZero n] [NeZero K]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (hRow : R.data.model.RowHasPositiveItem)
    (γ : ℝ)
    (hOrigNonempty :
      (RecommendationModel.attainableUserFairnessAtLevel R.data.model γ).Nonempty)
    (hRedNonempty :
      (TypeWeightedRecommendationModel.attainableTypeFairnessAtLevel
        R.reduced γ).Nonempty) :
    RecommendationModel.optimalUserFairnessAtLevel R.data.model γ =
      TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel R.reduced γ := by
  exact R.optimalUserFairnessAtLevel_eq_reduced_of_nonempty
    reps hRow γ hOrigNonempty hRedNonempty

/--
Original/reduced optimal user-fairness value reduction for strict item-fairness
fractions.

Under the paper's positive-utility assumption, the original and reduced
feasible value sets are automatically nonempty for every `γ < 1`; exact
item-fairness optimum attainment is only needed at the maximal boundary
`γ = 1`.
-/
theorem paper_original_reduced_user_optimal_value_reduction_of_gamma_lt_one
    {m n K : ℕ} [NeZero m] [NeZero n] [NeZero K]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (hPos : R.data.model.Positive)
    (γ : ℝ) (hγ : γ < 1) :
    RecommendationModel.optimalUserFairnessAtLevel R.data.model γ =
      TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel R.reduced γ := by
  exact R.optimalUserFairnessAtLevel_eq_reduced_of_gamma_lt_one
    reps hPos γ hγ

/--
Original/reduced optimal user-fairness value reduction at the maximal
item-fairness boundary.

The previous nonemptiness side conditions are discharged by compactness of the
original and reduced finite policy simplexes.
-/
theorem paper_original_reduced_user_optimal_value_reduction_one_of_positive
    {m n K : ℕ} [NeZero m] [NeZero n] [NeZero K]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (hPos : R.data.model.Positive) :
    RecommendationModel.optimalUserFairnessAtLevel R.data.model 1 =
      TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel R.reduced 1 := by
  exact R.optimalUserFairnessAtLevel_eq_reduced_one_of_positive reps hPos

/--
Baseline original/reduced optimal user-fairness value reduction.

For `γ = 0`, nonnegative utilities automatically make both original and
reduced feasible value sets nonempty; row positivity supplies boundedness.
-/
theorem paper_original_reduced_user_optimal_value_reduction_zero
    {m n K : ℕ} [NeZero m] [NeZero n] [NeZero K]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (hRow : R.data.model.RowHasPositiveItem)
    (hNonneg : R.data.model.Nonnegative) :
    RecommendationModel.optimalUserFairnessAtLevel R.data.model 0 =
      TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel R.reduced 0 := by
  have hOrigNonempty :
      (RecommendationModel.attainableUserFairnessAtLevel R.data.model 0).Nonempty :=
    RecommendationModel.attainableUserFairnessAtLevel_zero_nonempty_of_nonnegative
      R.data.model hNonneg
  have hRedWeight : R.reduced.NonnegativeWeights :=
    R.reduced_nonnegativeWeights
  have hRedUtil : R.reduced.NonnegativeUtilities :=
    R.reduced_nonnegativeUtilities_of_nonnegative reps hNonneg
  have hRedNonempty :
      (TypeWeightedRecommendationModel.attainableTypeFairnessAtLevel
        R.reduced 0).Nonempty :=
    TypeWeightedRecommendationModel.attainableTypeFairnessAtLevel_zero_nonempty_of_nonnegative
      R.reduced hRedWeight hRedUtil
  exact R.optimalUserFairnessAtLevel_eq_reduced_of_nonempty
    reps hRow 0 hOrigNonempty hRedNonempty

/--
Reduced-to-original optimum theorem under the explicit supremum conditions used
by the value-reduction theorem.
-/
theorem paper_reduced_optimum_lifts_to_original
    {m n K : ℕ} [NeZero m] [NeZero n] [NeZero K]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (hRow : R.data.model.RowHasPositiveItem)
    (γ : ℝ) (ρ : TypePolicy K n)
    (hOrigNonempty :
      (RecommendationModel.attainableUserFairnessAtLevel R.data.model γ).Nonempty)
    (hOrigBdd :
      BddAbove (RecommendationModel.attainableUserFairnessAtLevel R.data.model γ))
    (hRedNonempty :
      (TypeWeightedRecommendationModel.attainableTypeFairnessAtLevel
        R.reduced γ).Nonempty)
    (hRedBdd :
      BddAbove (TypeWeightedRecommendationModel.attainableTypeFairnessAtLevel
        R.reduced γ))
    (hopt : TypeWeightedRecommendationModel.IsOptimalAtLevel R.reduced γ ρ) :
    RecommendationModel.IsOptimalAtLevel R.data.model γ (R.liftedPolicy ρ) := by
  have hUserOptEq :=
    R.optimalUserFairnessAtLevel_eq_reduced_of_bddAbove_nonempty
      reps hRow γ hOrigNonempty hOrigBdd hRedNonempty hRedBdd
  exact R.isOptimalAtLevel_liftedPolicy_of_reduced reps γ ρ
    (R.optimalItemFairness_eq_reduced reps) hUserOptEq hopt

/--
Reduced-to-original optimum theorem with automatic boundedness.

Only nonemptiness of the original and reduced feasible value sets remains
explicit; row positivity supplies the `≤ 1` bounds needed by `sSup`.
-/
theorem paper_reduced_optimum_lifts_to_original_of_nonempty
    {m n K : ℕ} [NeZero m] [NeZero n] [NeZero K]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (hRow : R.data.model.RowHasPositiveItem)
    (γ : ℝ) (ρ : TypePolicy K n)
    (hOrigNonempty :
      (RecommendationModel.attainableUserFairnessAtLevel R.data.model γ).Nonempty)
    (hRedNonempty :
      (TypeWeightedRecommendationModel.attainableTypeFairnessAtLevel
        R.reduced γ).Nonempty)
    (hopt : TypeWeightedRecommendationModel.IsOptimalAtLevel R.reduced γ ρ) :
    RecommendationModel.IsOptimalAtLevel R.data.model γ (R.liftedPolicy ρ) := by
  have hUserOptEq :=
    R.optimalUserFairnessAtLevel_eq_reduced_of_nonempty
      reps hRow γ hOrigNonempty hRedNonempty
  exact R.isOptimalAtLevel_liftedPolicy_of_reduced reps γ ρ
    (R.optimalItemFairness_eq_reduced reps) hUserOptEq hopt

/--
Reduced-to-original optimum theorem with feasible-set nonemptiness discharged
from the supplied reduced optimum.

This version applies at the maximal item-fairness boundary `γ = 1` as soon as
a reduced optimum is available.
-/
theorem paper_reduced_optimum_lifts_to_original_auto_nonempty
    {m n K : ℕ} [NeZero m] [NeZero n] [NeZero K]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (hRow : R.data.model.RowHasPositiveItem)
    (γ : ℝ) (ρ : TypePolicy K n)
    (hopt : TypeWeightedRecommendationModel.IsOptimalAtLevel R.reduced γ ρ) :
    RecommendationModel.IsOptimalAtLevel R.data.model γ (R.liftedPolicy ρ) := by
  exact R.isOptimalAtLevel_liftedPolicy_of_reduced_auto_nonempty
    reps hRow γ ρ hopt

/--
Reduced-to-original optimum existence at the maximal item-fairness boundary:
compactness gives a reduced optimum, and the reduction bridge lifts it to an
original optimum.
-/
theorem paper_exists_lifted_reduced_optimum_at_level_one_of_nonnegative
    {m n K : ℕ} [NeZero m] [NeZero n] [NeZero K]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (hNonneg : R.data.model.Nonnegative)
    (hRow : R.data.model.RowHasPositiveItem) :
    ∃ ρ : TypePolicy K n,
      RecommendationModel.IsOptimalAtLevel
        R.data.model 1 (R.liftedPolicy ρ) := by
  obtain ⟨ρ, hopt⟩ :=
    TypeWeightedRecommendationModel.exists_isOptimalAtLevel_one_of_nonnegative
      R.reduced R.reduced_nonnegativeWeights
      (R.reduced_nonnegativeUtilities_of_nonnegative reps hNonneg)
  exact ⟨ρ, paper_reduced_optimum_lifts_to_original_auto_nonempty
    R reps hRow 1 ρ hopt⟩

/--
Reduced-to-original optimum theorem for strict item-fairness fractions.

For `γ < 1`, positive utilities discharge the feasible-value nonemptiness
conditions used by the value-reduction theorem.
-/
theorem paper_reduced_optimum_lifts_to_original_of_gamma_lt_one
    {m n K : ℕ} [NeZero m] [NeZero n] [NeZero K]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (hPos : R.data.model.Positive)
    (γ : ℝ) (hγ : γ < 1) (ρ : TypePolicy K n)
    (hopt : TypeWeightedRecommendationModel.IsOptimalAtLevel R.reduced γ ρ) :
    RecommendationModel.IsOptimalAtLevel R.data.model γ (R.liftedPolicy ρ) := by
  have hUserOptEq :=
    R.optimalUserFairnessAtLevel_eq_reduced_of_gamma_lt_one
      reps hPos γ hγ
  exact R.isOptimalAtLevel_liftedPolicy_of_reduced reps γ ρ
    (R.optimalItemFairness_eq_reduced reps) hUserOptEq hopt

/--
Symmetric original-to-reduced optimum theorem under the explicit supremum
conditions used by the value-reduction theorem.
-/
theorem paper_symmetric_original_optimum_descends_to_reduced
    {m n K : ℕ} [NeZero m] [NeZero n] [NeZero K]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (hRow : R.data.model.RowHasPositiveItem)
    (γ : ℝ) {ρ : Policy m n}
    (hρ : UserTypeAssignment.IsTypeSymmetric R.data.types ρ)
    (hOrigNonempty :
      (RecommendationModel.attainableUserFairnessAtLevel R.data.model γ).Nonempty)
    (hOrigBdd :
      BddAbove (RecommendationModel.attainableUserFairnessAtLevel R.data.model γ))
    (hRedNonempty :
      (TypeWeightedRecommendationModel.attainableTypeFairnessAtLevel
        R.reduced γ).Nonempty)
    (hRedBdd :
      BddAbove (TypeWeightedRecommendationModel.attainableTypeFairnessAtLevel
        R.reduced γ))
    (hopt : RecommendationModel.IsOptimalAtLevel R.data.model γ ρ) :
    ∃ ρK : TypePolicy K n,
      R.liftedPolicy ρK = ρ ∧
        TypeWeightedRecommendationModel.IsOptimalAtLevel R.reduced γ ρK := by
  have hUserOptEq :=
    R.optimalUserFairnessAtLevel_eq_reduced_of_bddAbove_nonempty
      reps hRow γ hOrigNonempty hOrigBdd hRedNonempty hRedBdd
  exact R.exists_reducedOptimalAtLevel_of_original_symmetric_optimal
    reps γ hρ (R.optimalItemFairness_eq_reduced reps) hUserOptEq hopt

/--
Symmetric original-to-reduced optimum theorem with automatic boundedness.

Only nonemptiness of the original and reduced feasible value sets remains
explicit; row positivity supplies the `≤ 1` bounds needed by `sSup`.
-/
theorem paper_symmetric_original_optimum_descends_to_reduced_of_nonempty
    {m n K : ℕ} [NeZero m] [NeZero n] [NeZero K]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (hRow : R.data.model.RowHasPositiveItem)
    (γ : ℝ) {ρ : Policy m n}
    (hρ : UserTypeAssignment.IsTypeSymmetric R.data.types ρ)
    (hOrigNonempty :
      (RecommendationModel.attainableUserFairnessAtLevel R.data.model γ).Nonempty)
    (hRedNonempty :
      (TypeWeightedRecommendationModel.attainableTypeFairnessAtLevel
        R.reduced γ).Nonempty)
    (hopt : RecommendationModel.IsOptimalAtLevel R.data.model γ ρ) :
    ∃ ρK : TypePolicy K n,
      R.liftedPolicy ρK = ρ ∧
        TypeWeightedRecommendationModel.IsOptimalAtLevel R.reduced γ ρK := by
  have hUserOptEq :=
    R.optimalUserFairnessAtLevel_eq_reduced_of_nonempty
      reps hRow γ hOrigNonempty hRedNonempty
  exact R.exists_reducedOptimalAtLevel_of_original_symmetric_optimal
    reps γ hρ (R.optimalItemFairness_eq_reduced reps) hUserOptEq hopt

/--
Symmetric original-to-reduced optimum theorem with feasible-set nonemptiness
discharged from the supplied original optimum.

This version applies at the maximal item-fairness boundary `γ = 1` as soon as a
type-symmetric original optimum is available.
-/
theorem paper_symmetric_original_optimum_descends_to_reduced_auto_nonempty
    {m n K : ℕ} [NeZero m] [NeZero n] [NeZero K]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (hRow : R.data.model.RowHasPositiveItem)
    (γ : ℝ) {ρ : Policy m n}
    (hρ : UserTypeAssignment.IsTypeSymmetric R.data.types ρ)
    (hopt : RecommendationModel.IsOptimalAtLevel R.data.model γ ρ) :
    ∃ ρK : TypePolicy K n,
      R.liftedPolicy ρK = ρ ∧
        TypeWeightedRecommendationModel.IsOptimalAtLevel R.reduced γ ρK := by
  exact R.exists_reducedOptimalAtLevel_of_original_symmetric_optimal_auto_nonempty
    reps hRow γ hρ hopt

/--
Symmetric original-to-reduced optimum existence at the maximal item-fairness
boundary: Proposition 2 supplies a type-symmetric original optimum, and the
reduction bridge descends it to a reduced optimum.
-/
theorem paper_exists_reduced_optimum_from_symmetric_original_at_level_one_of_positive
    {m n K : ℕ} [NeZero m] [NeZero n] [NeZero K]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (hPos : R.data.model.Positive) :
    ∃ ρK : TypePolicy K n,
      TypeWeightedRecommendationModel.IsOptimalAtLevel R.reduced 1 ρK := by
  have hRow : R.data.model.RowHasPositiveItem :=
    RecommendationModel.rowHasPositiveItem_of_positive R.data.model hPos
  obtain ⟨ρ, hopt⟩ :=
    RecommendationModel.exists_isOptimalAtLevel_one_of_nonnegative
      R.data.model (RecommendationModel.nonnegative_of_positive R.data.model hPos)
  obtain ⟨ρsym, hsym, hoptSym⟩ :=
    R.data.exists_typeSymmetric_isOptimalAtLevel_of_isOptimalAtLevel
      reps hRow hopt
  obtain ⟨ρK, _hlift, hoptK⟩ :=
    paper_symmetric_original_optimum_descends_to_reduced_auto_nonempty
      R reps hRow 1 hsym hoptSym
  exact ⟨ρK, hoptK⟩

/--
Symmetric original-to-reduced optimum theorem for strict item-fairness
fractions.

For `γ < 1`, positive utilities discharge the feasible-value nonemptiness
conditions used by the value-reduction theorem.
-/
theorem paper_symmetric_original_optimum_descends_to_reduced_of_gamma_lt_one
    {m n K : ℕ} [NeZero m] [NeZero n] [NeZero K]
    (R : ReductionWitness m n K)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (hPos : R.data.model.Positive)
    (γ : ℝ) (hγ : γ < 1) {ρ : Policy m n}
    (hρ : UserTypeAssignment.IsTypeSymmetric R.data.types ρ)
    (hopt : RecommendationModel.IsOptimalAtLevel R.data.model γ ρ) :
    ∃ ρK : TypePolicy K n,
      R.liftedPolicy ρK = ρ ∧
        TypeWeightedRecommendationModel.IsOptimalAtLevel R.reduced γ ρK := by
  have hUserOptEq :=
    R.optimalUserFairnessAtLevel_eq_reduced_of_gamma_lt_one
      reps hPos γ hγ
  exact R.exists_reducedOptimalAtLevel_of_original_symmetric_optimal
    reps γ hρ (R.optimalItemFairness_eq_reduced reps) hUserOptEq hopt

end ReductionWitness

namespace RecommendationModel

/--
Appendix C, Lemma 1: under the paper's strictly positive utility assumption,
the optimal minimum item fairness value is strictly positive.
-/
theorem paper_lemma1_optimal_item_fairness_positive
    {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n) (hPos : W.Positive) :
    0 < W.optimalItemFairness := by
  exact W.optimalItemFairness_pos_of_columnHasPositiveDemand
    (W.nonnegative_of_positive hPos)
    (W.columnHasPositiveDemand_of_positive hPos)

/--
Appendix C, Lemma 2 in max-min LP epigraph form.

The LP that maximizes `ell` subject to `ell ≤ I_j(ρ,w)` for every item has the
same optimal value as the paper's item-fairness objective `I^*_min(w)`.
-/
theorem paper_lemma2_item_fairness_lp_value_eq
    {m n : ℕ} [NeZero n]
    (W : RecommendationModel m n) (hNonneg : W.Nonnegative) :
    W.optimalItemFairnessLPValue = W.optimalItemFairness := by
  exact W.optimalItemFairnessLPValue_eq_optimalItemFairness_of_nonnegative
    hNonneg

/--
Appendix C, Lemma 2's full equality-form LP conclusion.

Under the source's strictly positive utility model, a policy solves the
original max-min item-fairness problem exactly when it is the policy component
of an optimizer of the equality-form LP with `I_j(rho) = ell` for every item.
This proves equality of the two optimizer sets, not merely equality of their
objective values.
-/
theorem paper_lemma2_item_fairness_equality_lp_solution_set_of_positive
    {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n) (hPos : W.Positive) (rho : Policy m n) :
    W.itemFairness rho = W.optimalItemFairness ↔
      ∃ ell : ℝ,
        W.itemFairnessEqualityLPFeasible rho ell ∧
          ∀ rho' : Policy m n, ∀ ell' : ℝ,
            W.itemFairnessEqualityLPFeasible rho' ell' → ell' ≤ ell := by
  constructor
  · intro hopt
    refine ⟨W.itemFairness rho, ?_, ?_⟩
    · exact W.itemFairnessEqualityLPFeasible_of_optimal_of_slackImprovement
        (W.nonnegative_of_positive hPos) hopt
        (W.itemFairnessSlackImprovementProperty_of_positive_of_optimal hPos hopt)
    · intro rho' ell' hfeas
      have hitem : W.itemFairness rho' = ell' :=
        W.itemFairness_eq_of_itemFairnessEqualityLPFeasible rho' ell' hfeas
      rw [← hitem, hopt]
      exact le_csSup
        (W.attainableItemFairnessSet_bddAbove_of_nonnegative
          (W.nonnegative_of_positive hPos))
        ⟨rho', rfl⟩
  · rintro ⟨ell, hfeas, hmax⟩
    obtain ⟨rhoopt, hopt⟩ :=
      W.optimalItemFairness_attained_of_nonnegative
        (W.nonnegative_of_positive hPos)
    have hoptfeas : W.itemFairnessEqualityLPFeasible rhoopt
        (W.itemFairness rhoopt) :=
      W.itemFairnessEqualityLPFeasible_of_optimal_of_slackImprovement
        (W.nonnegative_of_positive hPos) hopt
        (W.itemFairnessSlackImprovementProperty_of_positive_of_optimal hPos hopt)
    have hopt_le_ell : W.itemFairness rhoopt ≤ ell :=
      hmax rhoopt (W.itemFairness rhoopt) hoptfeas
    have hell_eq : W.itemFairness rho = ell :=
      W.itemFairness_eq_of_itemFairnessEqualityLPFeasible rho ell hfeas
    have hell_le_opt : ell ≤ W.optimalItemFairness := by
      rw [← hell_eq]
      exact le_csSup
        (W.attainableItemFairnessSet_bddAbove_of_nonnegative
          (W.nonnegative_of_positive hPos))
        ⟨rho, rfl⟩
    rw [hopt] at hopt_le_ell
    exact hell_eq.trans (le_antisymm hell_le_opt hopt_le_ell)

/--
Appendix C, Lemma 2 proof component: an attained item-fairness optimum admits
no alternative policy that strictly improves every normalized item utility.
-/
theorem paper_lemma2_noStrictPointwiseImprovement_of_optimal
    {m n : ℕ} [NeZero n]
    (W : RecommendationModel m n) (hNonneg : W.Nonnegative)
    {ρ : Policy m n}
    (hopt : W.itemFairness ρ = W.optimalItemFairness) :
    W.ItemFairnessNoStrictPointwiseImprovement ρ := by
  exact W.itemFairness_noStrictPointwiseImprovement_of_optimal hNonneg hopt

/--
Appendix C, Lemma 2 equality-form LP interface.

This is the source proof's exact remaining seam: once the paper's slack-item
perturbation is available for every attained optimum, the equality-form LP
`I_j(ρ) = ell` has optimal value `I^*_min(w)`.
-/
theorem paper_lemma2_item_fairness_equality_lp_value_eq_of_attained_of_slackImprovement
    {m n : ℕ} [NeZero n]
    (W : RecommendationModel m n) (hNonneg : W.Nonnegative)
    (hatt : ∃ ρ : Policy m n, W.itemFairness ρ = W.optimalItemFairness)
    (hslack :
      ∀ ρ : Policy m n,
        W.itemFairness ρ = W.optimalItemFairness →
          W.ItemFairnessSlackImprovementProperty ρ) :
    W.optimalItemFairnessEqualityLPValue = W.optimalItemFairness := by
  exact
    W.optimalItemFairnessEqualityLPValue_eq_optimalItemFairness_of_nonnegative_of_attained_of_slackImprovement
      hNonneg hatt hslack

/--
Appendix C, Lemma 2 equality-form LP interface under the paper's strictly
positive utility assumption.

The source slack-item probability-transfer proof is formalized; this wrapper
now only keeps the finite-dimensional optimum-attainment condition explicit.
-/
theorem paper_lemma2_item_fairness_equality_lp_value_eq_of_positive_of_attained
    {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n) (hPos : W.Positive)
    (hatt : ∃ ρ : Policy m n, W.itemFairness ρ = W.optimalItemFairness) :
    W.optimalItemFairnessEqualityLPValue = W.optimalItemFairness := by
  exact
    W.optimalItemFairnessEqualityLPValue_eq_optimalItemFairness_of_positive_of_attained
      hPos hatt

/--
Appendix C, Lemma 2 equality-form LP interface under the paper's strictly
positive utility assumption.

The finite-dimensional item-fairness optimum is attained, and the paper's
slack-item probability-transfer proof equalizes every attained optimum.
-/
theorem paper_lemma2_item_fairness_equality_lp_value_eq_of_positive
    {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n) (hPos : W.Positive) :
    W.optimalItemFairnessEqualityLPValue = W.optimalItemFairness := by
  exact W.optimalItemFairnessEqualityLPValue_eq_optimalItemFairness_of_positive
    hPos

/--
Problem 1 baseline theorem.

With nonnegative utilities and a positive row normalizer for every user, the
unconstrained user-fairness optimum `U^*_min(w)` equals `1`. The witness is the
deterministic policy that recommends a best item to each user.
-/
theorem paper_unconstrained_user_fairness_optimum_eq_one
    {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n)
    (hNonneg : W.Nonnegative) (hRow : W.RowHasPositiveItem) :
    W.optimalUserFairnessAtLevel 0 = 1 := by
  exact W.optimalUserFairnessAtLevel_zero_eq_one hNonneg hRow

/--
Appendix D, Lemma 3: in the two-opposing-type model and without item-fairness
constraints, the user-fairness optimum is `1`.
-/
theorem paper_lemma3_unconstrained_user_fairness_eq_one
    {n : ℕ} [NeZero n] (alpha : ℝ) (v : Item n → ℝ)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (_hdec : OpposingTypes.StrictlyDecreasingByIndex v) :
    TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
      (OpposingTypes.twoTypeReducedModel alpha v) 0 = 1 := by
  have hWeight : (OpposingTypes.twoTypeReducedModel alpha v).NonnegativeWeights :=
    TypeWeightedRecommendationModel.nonnegativeWeights_of_positiveWeights
      (OpposingTypes.twoTypeReducedModel alpha v)
      (OpposingTypes.twoTypeReducedModel_positiveWeights alpha v halpha0 halpha1)
  have hUtility : (OpposingTypes.twoTypeReducedModel alpha v).NonnegativeUtilities :=
    TypeWeightedRecommendationModel.nonnegativeUtilities_of_positiveUtilities
      (OpposingTypes.twoTypeReducedModel alpha v)
      (OpposingTypes.twoTypeReducedModel_positiveUtilities alpha v hpos)
  exact TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel_zero_eq_one
    (OpposingTypes.twoTypeReducedModel alpha v) hWeight hUtility
    (OpposingTypes.twoTypeReducedModel_rowHasPositiveItem alpha v hpos)

/--
Price-of-fairness identity at an arbitrary item-fairness fraction.

Once the unconstrained optimum is normalized to `1`, the paper's price of
fairness is exactly `1 - U^*_min(γ,w)`.
-/
theorem paper_priceOfFairnessAt_eq_one_sub_optimalUserFairnessAtLevel
    {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n)
    (hNonneg : W.Nonnegative) (hRow : W.RowHasPositiveItem) (γ : ℝ) :
    W.priceOfFairnessAt γ = 1 - W.optimalUserFairnessAtLevel γ := by
  exact W.priceOfFairnessAt_eq_one_sub_optimalUserFairnessAtLevel
    hNonneg hRow γ

/--
Price-of-fairness identity for the maximal item-fairness problem.
-/
theorem paper_priceOfFairness_eq_one_sub_optimalUserFairnessAtLevel_one
    {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n)
    (hNonneg : W.Nonnegative) (hRow : W.RowHasPositiveItem) :
    W.priceOfFairness = 1 - W.optimalUserFairnessAtLevel 1 := by
  exact W.priceOfFairness_eq_one_sub_optimalUserFairnessAtLevel_one
    hNonneg hRow

/--
Theorem 3 algebraic monotonicity bridge.

If the maximal-item-fairness constrained optimum increases between two utility
matrices, then the price of fairness decreases. The paper-specific work in
Theorem 3 is therefore the finite LP proof that
`U^*_min(1, α)` increases with preference diversity.
-/
theorem paper_theorem3_price_decreases_from_constrained_optimum_increase
    {m n : ℕ} [NeZero m] [NeZero n]
    (W W' : RecommendationModel m n)
    (hNonneg : W.Nonnegative) (hRow : W.RowHasPositiveItem)
    (hNonneg' : W'.Nonnegative) (hRow' : W'.RowHasPositiveItem)
    (hopt :
      W.optimalUserFairnessAtLevel 1 ≤ W'.optimalUserFairnessAtLevel 1) :
    W'.priceOfFairness ≤ W.priceOfFairness := by
  exact W.priceOfFairness_le_of_optimalUserFairnessAtLevel_one_le
    W' hNonneg hRow hNonneg' hRow' hopt

/--
Strict form of the Theorem 3 algebraic monotonicity bridge.
-/
theorem paper_theorem3_price_strictly_decreases_from_constrained_optimum_increase
    {m n : ℕ} [NeZero m] [NeZero n]
    (W W' : RecommendationModel m n)
    (hNonneg : W.Nonnegative) (hRow : W.RowHasPositiveItem)
    (hNonneg' : W'.Nonnegative) (hRow' : W'.RowHasPositiveItem)
    (hopt :
      W.optimalUserFairnessAtLevel 1 < W'.optimalUserFairnessAtLevel 1) :
    W'.priceOfFairness < W.priceOfFairness := by
  exact W.priceOfFairness_lt_of_optimalUserFairnessAtLevel_one_lt
    W' hNonneg hRow hNonneg' hRow' hopt

end RecommendationModel

namespace RecommendationModel.SymmetricData

/--
Proposition 2, part 1: `S_symm` satisfies the paper's symmetric-optimum
existence condition.

Given any optimum for the maximal item-fairness problem, averaging the policy
inside each equal-utility user type produces an optimum in `S_symm`.
-/
theorem paper_proposition2_symmetric_optimum_exists
    {m n K : ℕ} [NeZero m] [NeZero n] [NeZero K]
    (S : RecommendationModel.SymmetricData m n K)
    (reps : UserTypeAssignment.TypeRepresentatives S.types)
    (hRow : S.model.RowHasPositiveItem)
    {ρ : Policy m n}
    (hopt : RecommendationModel.IsOptimalAtLevel S.model 1 ρ) :
    ∃ ρsym : Policy m n,
      UserTypeAssignment.IsTypeSymmetric S.types ρsym ∧
        RecommendationModel.IsOptimalAtLevel S.model 1 ρsym := by
  exact S.exists_typeSymmetric_isOptimalAtLevel_of_isOptimalAtLevel
    reps hRow hopt

/--
Proposition 2, part 1 with optimum existence discharged.

Under the paper's strictly positive utilities, compactness gives an optimum for
the maximal item-fairness problem at `γ = 1`; symmetrization then preserves
optimality.
-/
theorem paper_proposition2_symmetric_optimum_exists_of_positive
    {m n K : ℕ} [NeZero m] [NeZero n] [NeZero K]
    (S : RecommendationModel.SymmetricData m n K)
    (reps : UserTypeAssignment.TypeRepresentatives S.types)
    (hPos : S.model.Positive) :
    ∃ ρsym : Policy m n,
      UserTypeAssignment.IsTypeSymmetric S.types ρsym ∧
        RecommendationModel.IsOptimalAtLevel S.model 1 ρsym := by
  have hRow : S.model.RowHasPositiveItem :=
    RecommendationModel.rowHasPositiveItem_of_positive S.model hPos
  obtain ⟨ρ, hopt⟩ :=
    RecommendationModel.exists_isOptimalAtLevel_one_of_nonnegative
      S.model (RecommendationModel.nonnegative_of_positive S.model hPos)
  exact S.exists_typeSymmetric_isOptimalAtLevel_of_isOptimalAtLevel
    reps hRow hopt

end RecommendationModel.SymmetricData

namespace OpposingTypes

/--
Appendix D, Lemma 9, scalar monotonicity in `α`.

For a fixed opposing item pair with positive utilities, the paper's
`q_j(α)` strictly increases as the mass `α` on the first type increases.
-/
theorem paper_lemma9_typeOneShare_strictly_increases_in_alpha
    {alpha alpha' left right : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (hlt : alpha < alpha')
    (hleft : 0 < left) (hright : 0 < right) :
    typeOneShare alpha left right <
      typeOneShare alpha' left right := by
  exact typeOneShare_strictMono_alpha
    halpha0 halpha1 halpha0' halpha1' hlt hleft hright

/--
Appendix E, Lemma 16, scalar midpoint comparison: if the left-side utility is
larger, then the midpoint share is above `1/2`.
-/
theorem paper_lemma16_half_lt_typeOneShare_half_of_right_lt_left
    {left right : ℝ}
    (hleft : 0 < left) (hright : 0 < right) (hlt : right < left) :
    (1 / 2 : ℝ) < typeOneShare (1 / 2) left right := by
  exact half_lt_typeOneShare_half_of_right_lt_left hleft hright hlt

/--
Appendix E, Lemma 16, scalar midpoint comparison: if the left-side utility is
smaller, then the midpoint share is below `1/2`.
-/
theorem paper_lemma16_typeOneShare_half_lt_half_of_left_lt_right
    {left right : ℝ}
    (hleft : 0 < left) (hright : 0 < right) (hlt : left < right) :
    typeOneShare (1 / 2) left right < (1 / 2 : ℝ) := by
  exact typeOneShare_half_lt_half_of_left_lt_right hleft hright hlt

/--
Appendix E, Lemma 16, scalar midpoint comparison: equal opposing utilities
give midpoint share exactly `1/2`.
-/
theorem paper_lemma16_typeOneShare_half_eq_half_of_eq
    {left right : ℝ}
    (hleft : 0 < left) (heq : left = right) :
    typeOneShare (1 / 2) left right = (1 / 2 : ℝ) := by
  exact typeOneShare_half_eq_half_of_eq hleft heq

/--
Appendix D, Lemma 9, indexed form: for each item `j`, the paper's
`q_j(α)` strictly increases as `α` increases.
-/
theorem paper_lemma9_pairShare_strictly_increases_in_alpha
    {n : ℕ} {alpha alpha' : ℝ} {v : Item n → ℝ} (j : Item n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (hlt : alpha < alpha')
    (hpos : ∀ j : Item n, 0 < v j) :
    pairShare alpha v j < pairShare alpha' v j := by
  exact pairShare_strictMono_alpha j
    halpha0 halpha1 halpha0' halpha1' hlt hpos

/--
Appendix D, Lemma 9, indexed form: `q_j(α)` weakly increases as `α`
increases.
-/
theorem paper_lemma9_pairShare_weakly_increases_in_alpha
    {n : ℕ} {alpha alpha' : ℝ} {v : Item n → ℝ} (j : Item n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (hpos : ∀ j : Item n, 0 < v j) :
    pairShare alpha v j ≤ pairShare alpha' v j := by
  exact pairShare_mono_alpha j
    halpha0 halpha1 halpha0' halpha1' halpha_le hpos

/--
Appendix D, Lemma 9 consequence: `q_j(α)⁻¹` weakly decreases as `α`
increases.
-/
theorem paper_lemma9_pairShare_inv_weakly_decreases_in_alpha
    {n : ℕ} {alpha alpha' : ℝ} {v : Item n → ℝ} (j : Item n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (hpos : ∀ j : Item n, 0 < v j) :
    (pairShare alpha' v j)⁻¹ ≤ (pairShare alpha v j)⁻¹ := by
  exact pairShare_inv_antitone_alpha j
    halpha0 halpha1 halpha0' halpha1' halpha_le hpos

/--
Appendix D, Lemma 9, indexed form: for a strictly decreasing value vector,
`q_j(α)` strictly decreases as the item index `j` increases.
-/
theorem paper_lemma9_pairShare_strictly_decreases_in_index
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {i j : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hij : i.val < j.val) :
    pairShare alpha v j < pairShare alpha v i := by
  exact pairShare_strictAnti_index halpha0 halpha1 hpos hdec hij

/--
Appendix D, Lemma 4 exchange algebra: if `q_i < q_j < 1`, then the item-`j`
perturbation coefficient is strictly positive.
-/
theorem paper_lemma4_exchange_margin_pos
    {qi qj : ℝ}
    (hqi1 : qi < 1) (hqij : qi < qj) :
    0 < qj - qi * ((1 - qj) / (1 - qi)) := by
  exact lemma4_exchange_margin_pos hqi1 hqij

/--
Appendix D, Lemma 4 exchange algebra: the transfer from item `j` to item `i`
keeps `y_j` above `y_i`.
-/
theorem paper_lemma4_exchange_transfer_lt
    {qi qj c yi yj : ℝ}
    (hqi0 : 0 < qi) (hqi1 : qi < 1) (hqj1 : qj < 1)
    (hqij : qi < qj) (hc : 0 < c) (hyi : 0 ≤ yi)
    (heq : qi * c + (1 - qi) * yi = (1 - qj) * yj) :
    yi + qi * c / (1 - qi) < yj := by
  exact lemma4_exchange_transfer_lt
    hqi0 hqi1 hqj1 hqij hc hyi heq

/--
Appendix D, Lemma 4 exchange algebra: after the transfer, item `j` keeps more
than the original `y_i` mass.
-/
theorem paper_lemma4_exchange_yj_sub_transfer_gt_yi
    {qi qj c yi yj : ℝ}
    (hqi0 : 0 < qi) (hqi1 : qi < 1) (hqj1 : qj < 1)
    (hqij : qi < qj) (hc : 0 < c) (hyi : 0 ≤ yi)
    (heq : qi * c + (1 - qi) * yi = (1 - qj) * yj) :
    yi < yj - qi * c / (1 - qi) := by
  exact lemma4_exchange_yj_sub_transfer_gt_yi
    hqi0 hqi1 hqj1 hqij hc hyi heq

/--
Appendix D, Lemma 4 exchange algebra: the exact transfer preserves item `i`
before the small positive `ε₂` perturbation.
-/
theorem paper_lemma4_exchange_i_value_eq
    {qi c yi : ℝ} (hqi1 : qi < 1) :
    (1 - qi) * (yi + qi * c / (1 - qi)) =
      qi * c + (1 - qi) * yi := by
  exact lemma4_exchange_i_value_eq hqi1

/--
Appendix D, Lemma 4 exchange algebra: the exact transfer strictly improves
item `j` before the small `ε` terms.
-/
theorem paper_lemma4_exchange_j_value_gt
    {qi qj c yj : ℝ}
    (hqi1 : qi < 1) (hqij : qi < qj) (hc : 0 < c) :
    qj * c + (1 - qj) * (yj - qi * c / (1 - qi)) >
      (1 - qj) * yj := by
  exact lemma4_exchange_j_value_gt hqi1 hqij hc

/--
Appendix D, Lemma 4 exchange algebra: there are small positive `ε₁, ε₂`
making both affected item values strictly larger after the perturbation.
-/
theorem paper_lemma4_exchange_exists_pos_eps_i_j_value_gt
    {qi qj c yi yj : ℝ}
    (hqi1 : qi < 1) (hqij : qi < qj) (hc : 0 < c) :
    ∃ eps1 eps2 : ℝ,
      0 < eps1 ∧ 0 < eps2 ∧
      (1 - qi) * (yi + qi * c / (1 - qi) + eps2) >
        qi * c + (1 - qi) * yi ∧
      qj * (c - eps1) +
          (1 - qj) * (yj - qi * c / (1 - qi) - eps2) >
        (1 - qj) * yj := by
  exact lemma4_exchange_exists_pos_eps_i_j_value_gt hqi1 hqij hc

/--
Appendix D, Lemma 4 exchange algebra with validity bounds: `ε₁, ε₂` can be
chosen below arbitrary positive caps.
-/
theorem paper_lemma4_exchange_exists_bounded_pos_eps_i_j_value_gt
    {qi qj c yi yj b1 b2 : ℝ}
    (hqi1 : qi < 1) (hqij : qi < qj) (hc : 0 < c)
    (hb1 : 0 < b1) (hb2 : 0 < b2) :
    ∃ eps1 eps2 : ℝ,
      0 < eps1 ∧ eps1 < b1 ∧
      0 < eps2 ∧ eps2 < b2 ∧
      (1 - qi) * (yi + qi * c / (1 - qi) + eps2) >
        qi * c + (1 - qi) * yi ∧
      qj * (c - eps1) +
          (1 - qj) * (yj - qi * c / (1 - qi) - eps2) >
        (1 - qj) * yj := by
  exact lemma4_exchange_exists_bounded_pos_eps_i_j_value_gt
    hqi1 hqij hc hb1 hb2

/--
Appendix D, Lemma 4 exchange algebra: the donor coordinate remains
nonnegative after the exact transfer.
-/
theorem paper_lemma4_exchange_yj_after_nonneg
    {qi qj c yi yj : ℝ}
    (hqi0 : 0 < qi) (hqi1 : qi < 1) (hqj1 : qj < 1)
    (hqij : qi < qj) (hc : 0 < c) (hyi : 0 ≤ yi)
    (heq : qi * c + (1 - qi) * yi = (1 - qj) * yj) :
    0 ≤ yj - qi * c / (1 - qi) := by
  exact lemma4_exchange_yj_after_nonneg
    hqi0 hqi1 hqj1 hqij hc hyi heq

/--
Appendix D, Lemma 4 exchange algebra: the receiver coordinate remains below
one after the exact transfer.
-/
theorem paper_lemma4_exchange_yi_after_lt_one
    {qi qj c yi yj : ℝ}
    (hqi0 : 0 < qi) (hqi1 : qi < 1) (hqj1 : qj < 1)
    (hqij : qi < qj) (hc : 0 < c) (hyi : 0 ≤ yi)
    (hyj_le_one : yj ≤ 1)
    (heq : qi * c + (1 - qi) * yi = (1 - qj) * yj) :
    yi + qi * c / (1 - qi) < 1 := by
  exact lemma4_exchange_yi_after_lt_one
    hqi0 hqi1 hqj1 hqij hc hyi hyj_le_one heq

/--
Appendix D, Lemma 4 indexed exchange margin: if `j` is before `i`, then
`q_j > q_i`, so the item-`j` perturbation has positive slack.
-/
theorem paper_lemma4_pairShare_exchange_margin_pos
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {i j : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hji : j.val < i.val) :
    0 < pairShare alpha v j -
      pairShare alpha v i *
        ((1 - pairShare alpha v j) / (1 - pairShare alpha v i)) := by
  exact lemma4_pairShare_exchange_margin_pos
    halpha0 halpha1 hpos hdec hji

/--
Appendix D, Lemma 4 indexed exchange transfer bound:
`y_i + q_i c/(1-q_i) < y_j`.
-/
theorem paper_lemma4_pairShare_exchange_transfer_lt
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {i j : Item n}
    {c yi yj : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hji : j.val < i.val)
    (hc : 0 < c) (hyi : 0 ≤ yi)
    (heq :
      pairShare alpha v i * c +
        (1 - pairShare alpha v i) * yi =
          (1 - pairShare alpha v j) * yj) :
    yi + pairShare alpha v i * c /
        (1 - pairShare alpha v i) < yj := by
  exact lemma4_pairShare_exchange_transfer_lt
    halpha0 halpha1 hpos hdec hji hc hyi heq

/--
Appendix D, Lemma 4 indexed exchange transfer bound:
`y_j - q_i c/(1-q_i) > y_i`.
-/
theorem paper_lemma4_pairShare_exchange_yj_sub_transfer_gt_yi
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {i j : Item n}
    {c yi yj : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hji : j.val < i.val)
    (hc : 0 < c) (hyi : 0 ≤ yi)
    (heq :
      pairShare alpha v i * c +
        (1 - pairShare alpha v i) * yi =
          (1 - pairShare alpha v j) * yj) :
    yi < yj - pairShare alpha v i * c /
        (1 - pairShare alpha v i) := by
  exact lemma4_pairShare_exchange_yj_sub_transfer_gt_yi
    halpha0 halpha1 hpos hdec hji hc hyi heq

/--
Appendix D, Lemma 4 indexed exchange algebra: the exact transfer preserves
item `i` before the small positive `ε₂` perturbation.
-/
theorem paper_lemma4_pairShare_exchange_i_value_eq
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {i : Item n}
    {c yi : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j) :
    (1 - pairShare alpha v i) *
        (yi + pairShare alpha v i * c /
          (1 - pairShare alpha v i)) =
      pairShare alpha v i * c +
        (1 - pairShare alpha v i) * yi := by
  exact lemma4_pairShare_exchange_i_value_eq
    halpha0 halpha1 hpos

/--
Appendix D, Lemma 4 indexed exchange algebra: moving positive `x_i` mass to
an earlier zero coordinate `j` strictly improves item `j`.
-/
theorem paper_lemma4_pairShare_exchange_j_value_gt
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {i j : Item n}
    {c yj : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hji : j.val < i.val)
    (hc : 0 < c) :
    pairShare alpha v j * c +
        (1 - pairShare alpha v j) *
          (yj - pairShare alpha v i * c /
            (1 - pairShare alpha v i)) >
      (1 - pairShare alpha v j) * yj := by
  exact lemma4_pairShare_exchange_j_value_gt
    halpha0 halpha1 hpos hdec hji hc

/--
Appendix D, Lemma 4 indexed exchange algebra: small positive `ε₁, ε₂` can be
chosen so both affected item values strictly increase.
-/
theorem paper_lemma4_pairShare_exchange_exists_pos_eps_i_j_value_gt
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {i j : Item n}
    {c yi yj : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hji : j.val < i.val)
    (hc : 0 < c) :
    ∃ eps1 eps2 : ℝ,
      0 < eps1 ∧ 0 < eps2 ∧
      (1 - pairShare alpha v i) *
          (yi + pairShare alpha v i * c /
            (1 - pairShare alpha v i) + eps2) >
        pairShare alpha v i * c +
          (1 - pairShare alpha v i) * yi ∧
      pairShare alpha v j * (c - eps1) +
          (1 - pairShare alpha v j) *
            (yj - pairShare alpha v i * c /
              (1 - pairShare alpha v i) - eps2) >
        (1 - pairShare alpha v j) * yj := by
  exact lemma4_pairShare_exchange_exists_pos_eps_i_j_value_gt
    halpha0 halpha1 hpos hdec hji hc

/--
Appendix D, Lemma 4 indexed exchange algebra with validity bounds: the small
positive `ε₁, ε₂` can also be chosen below arbitrary positive caps.
-/
theorem paper_lemma4_pairShare_exchange_exists_bounded_pos_eps_i_j_value_gt
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {i j : Item n}
    {c yi yj b1 b2 : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hji : j.val < i.val)
    (hc : 0 < c) (hb1 : 0 < b1) (hb2 : 0 < b2) :
    ∃ eps1 eps2 : ℝ,
      0 < eps1 ∧ eps1 < b1 ∧
      0 < eps2 ∧ eps2 < b2 ∧
      (1 - pairShare alpha v i) *
          (yi + pairShare alpha v i * c /
            (1 - pairShare alpha v i) + eps2) >
        pairShare alpha v i * c +
          (1 - pairShare alpha v i) * yi ∧
      pairShare alpha v j * (c - eps1) +
          (1 - pairShare alpha v j) *
            (yj - pairShare alpha v i * c /
              (1 - pairShare alpha v i) - eps2) >
        (1 - pairShare alpha v j) * yj := by
  exact lemma4_pairShare_exchange_exists_bounded_pos_eps_i_j_value_gt
    halpha0 halpha1 hpos hdec hji hc hb1 hb2

/--
Appendix D, Lemma 4 indexed perturbation construction: an earlier zero `x_j`
and a later positive `x_i` admit the paper's `ε₁, ε₂` exchange, producing
nonnegative row vectors with the same row sums and strictly larger item value at
every item. The vector `r` abstracts the paper's redistribution of `ε₁` over
unaffected items.
-/
theorem paper_lemma4_pairShare_gap_exchange_exists_strictly_improves
    {n : ℕ} {alpha : ℝ} {v x y r : Item n → ℝ} {i j : Item n}
    {c ell : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hji : j.val < i.val)
    (hx_nonneg : ∀ l : Item n, 0 ≤ x l)
    (hy_nonneg : ∀ l : Item n, 0 ≤ y l)
    (hxi : x i = c) (hxj : x j = 0) (hc : 0 < c)
    (hsumx : (∑ l : Item n, x l) = 1)
    (hsumy : (∑ l : Item n, y l) = 1)
    (hr_nonneg : ∀ l : Item n, 0 ≤ r l)
    (hr_pos : ∀ {l : Item n}, l ≠ i → l ≠ j → 0 < r l)
    (hri : r i = 0) (hrj : r j = 0)
    (hrsum : (∑ l : Item n, r l) = 1)
    (hi_eq :
      pairShare alpha v i * x i +
        (1 - pairShare alpha v i) * y i = ell)
    (hj_eq :
      pairShare alpha v j * x j +
        (1 - pairShare alpha v j) * y j = ell) :
    ∃ eps1 eps2 : ℝ, ∃ x' y' : Item n → ℝ,
      0 < eps1 ∧ eps1 < c ∧ 0 < eps2 ∧
      (eps2 < y j - pairShare alpha v i * c /
        (1 - pairShare alpha v i)) ∧
      (∀ l : Item n, 0 ≤ x' l) ∧
      (∀ l : Item n, 0 ≤ y' l) ∧
      (∑ l : Item n, x' l) = 1 ∧
      (∑ l : Item n, y' l) = 1 ∧
      (∀ l : Item n,
        pairShare alpha v l * x l +
          (1 - pairShare alpha v l) * y l <
        pairShare alpha v l * x' l +
          (1 - pairShare alpha v l) * y' l) := by
  exact lemma4_pairShare_gap_exchange_exists_strictly_improves
    halpha0 halpha1 hpos hdec hji hx_nonneg hy_nonneg hxi hxj hc
    hsumx hsumy hr_nonneg hr_pos hri hrj hrsum hi_eq hj_eq

/--
Appendix D, Lemma 4 no-gap consequence for the first row: if the equalized
Problem 6 policy admits no feasible policy that strictly improves every item
value, then an earlier zero `x_j` rules out later positive `x_i`.
-/
theorem paper_lemma4_twoTypeXZeroClosed_of_noStrictPointwiseImprovement
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 2 n} {ell : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hredistrib :
      ∀ {i j : Item n}, j.val < i.val →
        ∃ r : Item n → ℝ,
          (∀ l : Item n, 0 ≤ r l) ∧
          (∀ {l : Item n}, l ≠ i → l ≠ j → 0 < r l) ∧
          r i = 0 ∧ r j = 0 ∧
          (∑ l : Item n, r l) = 1)
    (hitem_eq :
      ∀ l : Item n,
        pairShare alpha v l * (ρ 0 l).toReal +
          (1 - pairShare alpha v l) * (ρ 1 l).toReal = ell)
    (hno : Problem6PolicyNoStrictPointwiseImprovement alpha v ρ) :
    TypePolicy.TwoTypeXZeroClosed ρ := by
  exact lemma4_twoTypeXZeroClosed_of_noStrictPointwiseImprovement
    halpha0 halpha1 hpos hdec hredistrib hitem_eq hno

/--
Appendix D, Lemma 4 symmetric indexed perturbation construction: an earlier
positive `y_i` and later zero `y_j` admit the symmetric exchange, producing
nonnegative row vectors with the same row sums and strictly larger item value at
every item.
-/
theorem paper_lemma4_pairShare_y_gap_exchange_exists_strictly_improves
    {n : ℕ} {alpha : ℝ} {v x y r : Item n → ℝ} {i j : Item n}
    {c ell : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hij : i.val < j.val)
    (hx_nonneg : ∀ l : Item n, 0 ≤ x l)
    (hy_nonneg : ∀ l : Item n, 0 ≤ y l)
    (hyi : y i = c) (hyj : y j = 0) (hc : 0 < c)
    (hsumx : (∑ l : Item n, x l) = 1)
    (hsumy : (∑ l : Item n, y l) = 1)
    (hr_nonneg : ∀ l : Item n, 0 ≤ r l)
    (hr_pos : ∀ {l : Item n}, l ≠ i → l ≠ j → 0 < r l)
    (hri : r i = 0) (hrj : r j = 0)
    (hrsum : (∑ l : Item n, r l) = 1)
    (hi_eq :
      pairShare alpha v i * x i +
        (1 - pairShare alpha v i) * y i = ell)
    (hj_eq :
      pairShare alpha v j * x j +
        (1 - pairShare alpha v j) * y j = ell) :
    ∃ eps1 eps2 : ℝ, ∃ x' y' : Item n → ℝ,
      0 < eps1 ∧ eps1 < c ∧ 0 < eps2 ∧
      (eps2 < x j - (1 - pairShare alpha v i) * c /
        pairShare alpha v i) ∧
      (∀ l : Item n, 0 ≤ x' l) ∧
      (∀ l : Item n, 0 ≤ y' l) ∧
      (∑ l : Item n, x' l) = 1 ∧
      (∑ l : Item n, y' l) = 1 ∧
      (∀ l : Item n,
        pairShare alpha v l * x l +
          (1 - pairShare alpha v l) * y l <
        pairShare alpha v l * x' l +
          (1 - pairShare alpha v l) * y' l) := by
  exact lemma4_pairShare_y_gap_exchange_exists_strictly_improves
    halpha0 halpha1 hpos hdec hij hx_nonneg hy_nonneg hyi hyj hc
    hsumx hsumy hr_nonneg hr_pos hri hrj hrsum hi_eq hj_eq

/--
Appendix D, Lemma 4 no-gap consequence for the second row: if the equalized
Problem 6 policy admits no feasible policy that strictly improves every item
value, then a later zero `y_j` rules out earlier positive `y_i`.
-/
theorem paper_lemma4_twoTypeYZeroClosed_of_noStrictPointwiseImprovement
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 2 n} {ell : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hredistrib :
      ∀ {i j : Item n}, i.val < j.val →
        ∃ r : Item n → ℝ,
          (∀ l : Item n, 0 ≤ r l) ∧
          (∀ {l : Item n}, l ≠ i → l ≠ j → 0 < r l) ∧
          r i = 0 ∧ r j = 0 ∧
          (∑ l : Item n, r l) = 1)
    (hitem_eq :
      ∀ l : Item n,
        pairShare alpha v l * (ρ 0 l).toReal +
          (1 - pairShare alpha v l) * (ρ 1 l).toReal = ell)
    (hno : Problem6PolicyNoStrictPointwiseImprovement alpha v ρ) :
    TypePolicy.TwoTypeYZeroClosed ρ := by
  exact lemma4_twoTypeYZeroClosed_of_noStrictPointwiseImprovement
    halpha0 halpha1 hpos hdec hredistrib hitem_eq hno

/--
Appendix D, Lemma 4 threshold-support conclusion from the perturbation
argument and the Proposition 2 shared-item bound.
-/
theorem paper_lemma4_twoTypeThresholdSupport_of_noStrictPointwiseImprovement
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 2 n} {ell : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hredistrib :
      ∀ {i j : Item n}, i ≠ j →
        ∃ r : Item n → ℝ,
          (∀ l : Item n, 0 ≤ r l) ∧
          (∀ {l : Item n}, l ≠ i → l ≠ j → 0 < r l) ∧
          r i = 0 ∧ r j = 0 ∧
          (∑ l : Item n, r l) = 1)
    (hitem_eq :
      ∀ l : Item n,
        pairShare alpha v l * (ρ 0 l).toReal +
          (1 - pairShare alpha v l) * (ρ 1 l).toReal = ell)
    (hno : Problem6PolicyNoStrictPointwiseImprovement alpha v ρ)
    (hshared : TypePolicy.SharedItemsBound ρ) :
    TypePolicy.TwoTypeThresholdSupport ρ := by
  exact lemma4_twoTypeThresholdSupport_of_noStrictPointwiseImprovement
    halpha0 halpha1 hpos hdec hredistrib hitem_eq hno hshared

/--
Appendix D, Lemma 4 redistribution vector: for `2 < n`, the paper's uniform
`1/(n-2)` distribution over items outside an exchanged pair exists.
-/
theorem paper_lemma4_redistribution_exists_of_two_lt
    {n : ℕ} (hn : 2 < n) {i j : Item n} (hij : i ≠ j) :
    ∃ r : Item n → ℝ,
      (∀ l : Item n, 0 ≤ r l) ∧
      (∀ {l : Item n}, l ≠ i → l ≠ j → 0 < r l) ∧
      r i = 0 ∧ r j = 0 ∧
      (∑ l : Item n, r l) = 1 := by
  exact lemma4_redistribution_exists_of_two_lt hn hij

/--
Appendix D, Lemma 4 threshold-support conclusion with the paper's uniform
redistribution vector discharged by `2 < n`.
-/
theorem paper_lemma4_twoTypeThresholdSupport_of_noStrictPointwiseImprovement_of_two_lt
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 2 n} {ell : ℝ}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hitem_eq :
      ∀ l : Item n,
        pairShare alpha v l * (ρ 0 l).toReal +
          (1 - pairShare alpha v l) * (ρ 1 l).toReal = ell)
    (hno : Problem6PolicyNoStrictPointwiseImprovement alpha v ρ)
    (hshared : TypePolicy.SharedItemsBound ρ) :
    TypePolicy.TwoTypeThresholdSupport ρ := by
  exact lemma4_twoTypeThresholdSupport_of_noStrictPointwiseImprovement_of_two_lt
    hn halpha0 halpha1 hpos hdec hitem_eq hno hshared

/--
Problem 6 optimality bridge: an optimal epigraph value is the minimum item
value of its policy.
-/
theorem paper_problem6_policyOptimal_value_eq_finiteMin
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 2 n} {ell : ℝ}
    (hopt : Problem6PolicyOptimal alpha v ρ ell) :
    ell =
      AppliedModelingLib.finiteMin (fun l : Item n =>
        pairShare alpha v l * (ρ 0 l).toReal +
          (1 - pairShare alpha v l) * (ρ 1 l).toReal) := by
  exact problem6PolicyOptimal_value_eq_finiteMin hopt

/-- Problem 6 optimality bridge: positive utilities give a positive optimal value. -/
theorem paper_problem6_policyOptimal_value_pos
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 2 n} {ell : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hopt : Problem6PolicyOptimal alpha v ρ ell) :
    0 < ell := by
  exact problem6PolicyOptimal_value_pos halpha0 halpha1 hpos hopt

/--
Appendix D, Lemma 4 optimality bridge: an optimal Problem 6 policy admits no
feasible policy that strictly improves every item value.
-/
theorem paper_problem6_noStrictPointwiseImprovement_of_policyOptimal
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 2 n} {ell : ℝ}
    (hopt : Problem6PolicyOptimal alpha v ρ ell) :
    Problem6PolicyNoStrictPointwiseImprovement alpha v ρ := by
  exact problem6_noStrictPointwiseImprovement_of_policyOptimal hopt

/--
Appendix D, Lemma 4 optimality bridge: an equalized optimal Problem 6 policy
admits no feasible policy that strictly improves every item value.
-/
theorem paper_problem6_noStrictPointwiseImprovement_of_policyOptimal_equalized
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 2 n} {ell : ℝ}
    (hitem_eq :
      ∀ l : Item n,
        pairShare alpha v l * (ρ 0 l).toReal +
          (1 - pairShare alpha v l) * (ρ 1 l).toReal = ell)
    (hopt : Problem6PolicyOptimal alpha v ρ ell) :
    Problem6PolicyNoStrictPointwiseImprovement alpha v ρ := by
  exact problem6_noStrictPointwiseImprovement_of_policyOptimal_equalized
    hitem_eq hopt

/--
Appendix D, Lemma 4 support bridge: an equalized optimal Problem 6 policy with
positive utilities covers every item.
-/
theorem paper_problem6_item_coverage_of_equalized_policyOptimal
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 2 n} {ell : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hitem_eq :
      ∀ l : Item n,
        pairShare alpha v l * (ρ 0 l).toReal +
          (1 - pairShare alpha v l) * (ρ 1 l).toReal = ell)
    (hopt : Problem6PolicyOptimal alpha v ρ ell) :
    ∀ j : Item n, ∃ k : UserType 2, ρ k j ≠ 0 := by
  exact problem6_item_coverage_of_equalized_policyOptimal
    halpha0 halpha1 hpos hitem_eq hopt

/--
Appendix D, Lemma 4 support bridge for the paper's equality-form optimal BFS
package: item coverage plus the basic-feasible support count give the shared
item bound.
-/
theorem paper_problem6_sharedItemsBound_of_equalizedBasicOptimal
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 2 n} {ell : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (h : Problem6EqualizedBasicOptimal alpha v ρ ell) :
    TypePolicy.SharedItemsBound ρ := by
  exact problem6_sharedItemsBound_of_equalizedBasicOptimal
    halpha0 halpha1 hpos h

/--
Appendix D, Lemma 4 threshold-support conclusion for an equalized optimal
Problem 6 policy, with the paper's redistribution vector discharged by `2 < n`.
-/
theorem paper_lemma4_twoTypeThresholdSupport_of_policyOptimal_equalized_of_two_lt
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 2 n} {ell : ℝ}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hitem_eq :
      ∀ l : Item n,
        pairShare alpha v l * (ρ 0 l).toReal +
          (1 - pairShare alpha v l) * (ρ 1 l).toReal = ell)
    (hopt : Problem6PolicyOptimal alpha v ρ ell)
    (hshared : TypePolicy.SharedItemsBound ρ) :
    TypePolicy.TwoTypeThresholdSupport ρ := by
  exact lemma4_twoTypeThresholdSupport_of_policyOptimal_equalized_of_two_lt
    hn halpha0 halpha1 hpos hdec hitem_eq hopt hshared

/--
Appendix D, Lemma 4 to Lemma 5 bridge: threshold support plus item
equalization gives the sparse equalized real Problem 6 shape.
-/
theorem paper_lemma4_sparseEqualized_of_twoTypeThresholdSupport
    {n : ℕ}
    {alpha : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 2 n} {ell : ℝ}
    (hitem_eq :
      ∀ l : Item n,
        pairShare alpha v l * (ρ 0 l).toReal +
          (1 - pairShare alpha v l) * (ρ 1 l).toReal = ell)
    (hthreshold : TypePolicy.TwoTypeThresholdSupport ρ) :
    ∃ t : Item n,
      Problem6SparseEqualized alpha v t
        (fun l : Item n => (ρ 0 l).toReal)
        (fun l : Item n => (ρ 1 l).toReal) ell := by
  exact problem6SparseEqualized_of_twoTypeThresholdSupport
    hitem_eq hthreshold

/--
Appendix D, Lemma 4 to Lemma 5 bridge for an equalized optimal Problem 6
policy: the Lemma 4 threshold pivot gives a sparse equalized real solution.
-/
theorem paper_lemma4_sparseEqualized_of_policyOptimal_equalized_of_two_lt
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 2 n} {ell : ℝ}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hitem_eq :
      ∀ l : Item n,
        pairShare alpha v l * (ρ 0 l).toReal +
          (1 - pairShare alpha v l) * (ρ 1 l).toReal = ell)
    (hopt : Problem6PolicyOptimal alpha v ρ ell)
    (hshared : TypePolicy.SharedItemsBound ρ) :
    ∃ t : Item n,
      Problem6SparseEqualized alpha v t
        (fun l : Item n => (ρ 0 l).toReal)
        (fun l : Item n => (ρ 1 l).toReal) ell := by
  exact problem6SparseEqualized_of_policyOptimal_equalized_of_two_lt
    hn halpha0 halpha1 hpos hdec hitem_eq hopt hshared

/--
Appendix D, Lemma 4 to Lemma 5 bridge retaining the paper's pivot
`max {j : x_j > 0}`: an equalized optimal Problem 6 policy gives an active
sparse equalized solution.
-/
theorem paper_lemma4_sparseEqualizedActive_of_policyOptimal_equalized_of_two_lt
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 2 n} {ell : ℝ}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hitem_eq :
      ∀ l : Item n,
        pairShare alpha v l * (ρ 0 l).toReal +
          (1 - pairShare alpha v l) * (ρ 1 l).toReal = ell)
    (hopt : Problem6PolicyOptimal alpha v ρ ell)
    (hshared : TypePolicy.SharedItemsBound ρ) :
    Problem6SparseEqualizedActive alpha v (TypePolicy.lastActiveTypeZero ρ)
      (fun l : Item n => (ρ 0 l).toReal)
      (fun l : Item n => (ρ 1 l).toReal) ell := by
  exact problem6SparseEqualizedActive_of_policyOptimal_equalized_of_two_lt
    hn halpha0 halpha1 hpos hdec hitem_eq hopt hshared

/--
Appendix D, Lemma 4 active-sparse bridge for the paper's equality-form optimal
BFS package.
-/
theorem paper_lemma4_sparseEqualizedActive_of_equalizedBasicOptimal_of_two_lt
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 2 n} {ell : ℝ}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (h : Problem6EqualizedBasicOptimal alpha v ρ ell) :
    Problem6SparseEqualizedActive alpha v (TypePolicy.lastActiveTypeZero ρ)
      (fun l : Item n => (ρ 0 l).toReal)
      (fun l : Item n => (ρ 1 l).toReal) ell := by
  exact problem6SparseEqualizedActive_of_equalizedBasicOptimal_of_two_lt
    hn halpha0 halpha1 hpos hdec h

/--
Appendix D, Lemma 4 indexed exchange algebra: after the exact transfer, the
donor coordinate remains nonnegative.
-/
theorem paper_lemma4_pairShare_exchange_yj_after_nonneg
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {i j : Item n}
    {c yi yj : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hji : j.val < i.val)
    (hc : 0 < c) (hyi : 0 ≤ yi)
    (heq :
      pairShare alpha v i * c +
        (1 - pairShare alpha v i) * yi =
          (1 - pairShare alpha v j) * yj) :
    0 ≤ yj - pairShare alpha v i * c /
        (1 - pairShare alpha v i) := by
  exact lemma4_pairShare_exchange_yj_after_nonneg
    halpha0 halpha1 hpos hdec hji hc hyi heq

/--
Appendix D, Lemma 4 indexed exchange algebra: after the exact transfer, the
receiver coordinate remains below one.
-/
theorem paper_lemma4_pairShare_exchange_yi_after_lt_one
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {i j : Item n}
    {c yi yj : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hji : j.val < i.val)
    (hc : 0 < c) (hyi : 0 ≤ yi) (hyj_le_one : yj ≤ 1)
    (heq :
      pairShare alpha v i * c +
        (1 - pairShare alpha v i) * yi =
          (1 - pairShare alpha v j) * yj) :
    yi + pairShare alpha v i * c /
        (1 - pairShare alpha v i) < 1 := by
  exact lemma4_pairShare_exchange_yi_after_lt_one
    halpha0 halpha1 hpos hdec hji hc hyi hyj_le_one heq

/--
Appendix D, Lemma 11 algebra: the ratio `q_t(α)/q_j(α)` after expanding the
paper's `q` denominators.
-/
theorem paper_lemma11_pairShare_div_pairShare_eq
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} (t j : Item n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j) :
    pairShare alpha v t / pairShare alpha v j =
      (v t / v j) *
        ((alpha * v j + (1 - alpha) * v (reverseItem j)) /
          (alpha * v t + (1 - alpha) * v (reverseItem t))) := by
  exact pairShare_div_pairShare_eq t j halpha0 halpha1 hpos

/--
Appendix D, Lemma 11 algebra: the ratio `(1-q_t(α))/(1-q_j(α))` after
expanding the paper's `q` denominators.
-/
theorem paper_lemma11_one_sub_pairShare_div_one_sub_pairShare_eq
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} (t j : Item n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j) :
    (1 - pairShare alpha v t) / (1 - pairShare alpha v j) =
      (v (reverseItem t) / v (reverseItem j)) *
        ((alpha * v j + (1 - alpha) * v (reverseItem j)) /
          (alpha * v t + (1 - alpha) * v (reverseItem t))) := by
  exact one_sub_pairShare_div_one_sub_pairShare_eq
    t j halpha0 halpha1 hpos

/--
Appendix D, Lemma 11 mirror-paired pre-pivot algebra:
`q_t/q_j + (1-q_t)/(1-q_{n-j+1})` equals the paper's `h_t(α)` expression.
-/
theorem paper_lemma11_paired_q_term_eq
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} (t j : Item n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j) :
    pairShare alpha v t / pairShare alpha v j +
        (1 - pairShare alpha v t) /
          (1 - pairShare alpha v (reverseItem j)) =
      1 + (v (reverseItem j) / v j) *
        (((1 - alpha) * v t + alpha * v (reverseItem t)) /
          (alpha * v t + (1 - alpha) * v (reverseItem t))) := by
  exact lemma11_paired_q_term_eq t j halpha0 halpha1 hpos

/--
Appendix D, Lemma 11 scalar monotonicity template: the paper's derivative sign
argument in two-point, denominator-cleared form.
-/
theorem paper_lemma11_affine_ratio_antitone_of_cross
    {A B C X alpha alpha' : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (hA : 0 < A) (hB : 0 < B)
    (hcross : B * X ≤ A * C) :
    (C + alpha' * (X - C)) / (B + alpha' * (A - B)) ≤
      (C + alpha * (X - C)) / (B + alpha * (A - B)) := by
  exact lemma11_affine_ratio_antitone_of_cross
    halpha0 halpha1 halpha0' halpha1' halpha_le hA hB hcross

/--
Appendix D, Lemma 11 middle-term monotonicity: the denominator ratio appearing
in `(1-q_t)/(1-q_j)` decreases with `α` for `j > t`.
-/
theorem paper_lemma11_middle_denominator_ratio_antitone
    {n : ℕ} {alpha alpha' : ℝ} {v : Item n → ℝ} {t j : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (htj : t.val < j.val) :
    (alpha' * v j + (1 - alpha') * v (reverseItem j)) /
        (alpha' * v t + (1 - alpha') * v (reverseItem t)) ≤
      (alpha * v j + (1 - alpha) * v (reverseItem j)) /
        (alpha * v t + (1 - alpha) * v (reverseItem t)) := by
  exact lemma11_middle_denominator_ratio_antitone
    halpha0 halpha1 halpha0' halpha1' halpha_le hpos hdec htj

/--
Appendix D, Lemma 11 right-side term monotonicity:
`(1-q_t(α))/(1-q_j(α))` decreases with `α` for `j > t`.
-/
theorem paper_lemma11_right_term_antitone
    {n : ℕ} {alpha alpha' : ℝ} {v : Item n → ℝ} {t j : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (htj : t.val < j.val) :
    (1 - pairShare alpha' v t) / (1 - pairShare alpha' v j) ≤
      (1 - pairShare alpha v t) / (1 - pairShare alpha v j) := by
  exact lemma11_right_term_antitone
    halpha0 halpha1 halpha0' halpha1' halpha_le hpos hdec htj

/--
Appendix D, Lemma 11 paired-term monotonicity for pivots at or before their
mirror.
-/
theorem paper_lemma11_paired_denominator_ratio_antitone
    {n : ℕ} {alpha alpha' : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter : t.val ≤ (reverseItem t).val) :
    ((1 - alpha') * v t + alpha' * v (reverseItem t)) /
        (alpha' * v t + (1 - alpha') * v (reverseItem t)) ≤
      ((1 - alpha) * v t + alpha * v (reverseItem t)) /
        (alpha * v t + (1 - alpha) * v (reverseItem t)) := by
  exact lemma11_paired_denominator_ratio_antitone
    halpha0 halpha1 halpha0' halpha1' halpha_le hpos hdec hcenter

/--
Appendix D, Lemma 11 paired `h_t(α)` expression monotonicity after the paper's
mirror-pair expansion.
-/
theorem paper_lemma11_pairedExpression_antitone
    {n : ℕ} {alpha alpha' : ℝ} {v : Item n → ℝ} {t j : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter : t.val ≤ (reverseItem t).val) :
    1 + (v (reverseItem j) / v j) *
        (((1 - alpha') * v t + alpha' * v (reverseItem t)) /
          (alpha' * v t + (1 - alpha') * v (reverseItem t))) ≤
      1 + (v (reverseItem j) / v j) *
        (((1 - alpha) * v t + alpha * v (reverseItem t)) /
          (alpha * v t + (1 - alpha) * v (reverseItem t))) := by
  exact lemma11_pairedExpression_antitone
    halpha0 halpha1 halpha0' halpha1' halpha_le hpos hdec hcenter

/--
Appendix D, Lemma 11 mirror-paired term monotonicity:
`q_t/q_j + (1-q_t)/(1-q_{n-j+1})` decreases with `α`.
-/
theorem paper_lemma11_paired_q_term_antitone
    {n : ℕ} {alpha alpha' : ℝ} {v : Item n → ℝ} {t j : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter : t.val ≤ (reverseItem t).val) :
    pairShare alpha' v t / pairShare alpha' v j +
        (1 - pairShare alpha' v t) /
          (1 - pairShare alpha' v (reverseItem j)) ≤
      pairShare alpha v t / pairShare alpha v j +
        (1 - pairShare alpha v t) /
          (1 - pairShare alpha v (reverseItem j)) := by
  exact lemma11_paired_q_term_antitone
    halpha0 halpha1 halpha0' halpha1' halpha_le hpos hdec hcenter

/--
Appendix D, Lemma 11 paired-sum monotonicity: summing the paper's mirror-paired
pre-pivot terms preserves the antitonicity in `α`.
-/
theorem paper_lemma11_pairedWeightedSum_antitone
    {n : ℕ} {alpha alpha' : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter : t.val ≤ (reverseItem t).val) :
    (∑ j : Item n, if j.val < t.val then
        pairShare alpha' v t / pairShare alpha' v j +
          (1 - pairShare alpha' v t) /
            (1 - pairShare alpha' v (reverseItem j)) else 0) ≤
      (∑ j : Item n, if j.val < t.val then
        pairShare alpha v t / pairShare alpha v j +
          (1 - pairShare alpha v t) /
            (1 - pairShare alpha v (reverseItem j)) else 0) := by
  exact lemma11_pairedWeightedSum_antitone
    halpha0 halpha1 halpha0' halpha1' halpha_le hpos hdec hcenter

/--
Appendix D, Lemma 11 right-side sum monotonicity:
`(1-q_t)R_t` decreases with `α` for a fixed pivot.
-/
theorem paper_lemma11_rightWeightedSum_antitone
    {n : ℕ} {alpha alpha' : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v) :
    (1 - pairShare alpha' v t) * problem6RightSum alpha' v t ≤
      (1 - pairShare alpha v t) * problem6RightSum alpha v t := by
  exact lemma11_rightWeightedSum_antitone
    halpha0 halpha1 halpha0' halpha1' halpha_le hpos hdec

/--
Appendix D, Lemma 11 denominator decomposition:
`q_t L_t + (1-q_t)R_t` is the paper's mirror-paired pre-pivot sum plus the
unpaired residual right-side sum.
-/
theorem paper_lemma11_weightedCore_eq_paired_add_residual
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (hcenter : t.val ≤ (reverseItem t).val) :
    pairShare alpha v t * problem6LeftSum alpha v t +
        (1 - pairShare alpha v t) * problem6RightSum alpha v t =
      (∑ j : Item n, if j.val < t.val then
        pairShare alpha v t / pairShare alpha v j +
          (1 - pairShare alpha v t) /
            (1 - pairShare alpha v (reverseItem j)) else 0) +
      (∑ j : Item n, if t.val < j.val ∧
          t.val ≤ (reverseItem j).val then
        (1 - pairShare alpha v t) / (1 - pairShare alpha v j) else 0) := by
  exact lemma11_weightedCore_eq_paired_add_residual hcenter

/--
Appendix D, Lemma 11 residual right-sum monotonicity: after mirror pairing,
the remaining post-pivot complement-ratio terms decrease with `α`.
-/
theorem paper_lemma11_residualRightSum_antitone
    {n : ℕ} {alpha alpha' : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v) :
    (∑ j : Item n, if t.val < j.val ∧
          t.val ≤ (reverseItem j).val then
        (1 - pairShare alpha' v t) / (1 - pairShare alpha' v j) else 0) ≤
      (∑ j : Item n, if t.val < j.val ∧
          t.val ≤ (reverseItem j).val then
        (1 - pairShare alpha v t) / (1 - pairShare alpha v j) else 0) := by
  exact lemma11_residualRightSum_antitone
    halpha0 halpha1 halpha0' halpha1' halpha_le hpos hdec

/--
Appendix D, Lemma 11 fixed-pivot denominator-core monotonicity:
`q_t L_t + (1-q_t)R_t` decreases with `α`.
-/
theorem paper_lemma11_fixedPivotWeightedCore_antitone
    {n : ℕ} {alpha alpha' : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter : t.val ≤ (reverseItem t).val) :
    pairShare alpha' v t * problem6LeftSum alpha' v t +
        (1 - pairShare alpha' v t) * problem6RightSum alpha' v t ≤
      pairShare alpha v t * problem6LeftSum alpha v t +
        (1 - pairShare alpha v t) * problem6RightSum alpha v t := by
  exact lemma11_fixedPivotWeightedCore_antitone
    halpha0 halpha1 halpha0' halpha1' halpha_le hpos hdec hcenter

/--
Appendix D, Lemma 11 fixed-pivot denominator monotonicity: the full closed-form
denominator decreases with `α`.
-/
theorem paper_lemma11_fixedPivotDenominator_antitone
    {n : ℕ} {alpha alpha' : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter : t.val ≤ (reverseItem t).val) :
    problem6ClosedDenominator alpha' v t ≤
      problem6ClosedDenominator alpha v t := by
  exact lemma11_fixedPivotDenominator_antitone
    halpha0 halpha1 halpha0' halpha1' halpha_le hpos hdec hcenter

/--
Appendix D, Lemma 11 fixed-pivot closed-value monotonicity: holding the pivot
fixed, the closed-form value `I^*_{min}` increases with `α`.
-/
theorem paper_lemma11_fixedPivotClosedValue_monotone
    {n : ℕ} {alpha alpha' : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter : t.val ≤ (reverseItem t).val) :
    problem6ClosedValue alpha v t ≤
      problem6ClosedValue alpha' v t := by
  exact lemma11_fixedPivotClosedValue_monotone
    halpha0 halpha1 halpha0' halpha1' halpha_le hpos hdec hcenter

/-- Problem 6 setup: `q_j(α)` is strictly positive. -/
theorem paper_problem6_pairShare_pos
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} (j : Item n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j) :
    0 < pairShare alpha v j := by
  exact pairShare_pos j halpha0 halpha1 hpos

/-- Problem 6 setup: `q_j(α)` is strictly below one. -/
theorem paper_problem6_pairShare_lt_one
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} (j : Item n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j) :
    pairShare alpha v j < 1 := by
  exact pairShare_lt_one j halpha0 halpha1 hpos

/-- Problem 6 setup: the complementary share `1 - q_j(α)` is strictly positive. -/
theorem paper_problem6_one_sub_pairShare_pos
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} (j : Item n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j) :
    0 < 1 - pairShare alpha v j := by
  exact one_sub_pairShare_pos j halpha0 halpha1 hpos

/--
Appendix E, Lemma 16, indexed form: `q_j(1/2) > 1/2` when item `j` has
higher value than its opposite item.
-/
theorem paper_lemma16_half_lt_pairShare_half_of_reverse_lt
    {n : ℕ} {v : Item n → ℝ} (j : Item n)
    (hpos : ∀ j : Item n, 0 < v j)
    (hlt : v (reverseItem j) < v j) :
    (1 / 2 : ℝ) < pairShare (1 / 2) v j := by
  exact half_lt_pairShare_half_of_reverse_lt j hpos hlt

/--
Appendix E, Lemma 16, indexed form: `q_j(1/2) < 1/2` when item `j` has
lower value than its opposite item.
-/
theorem paper_lemma16_pairShare_half_lt_half_of_lt_reverse
    {n : ℕ} {v : Item n → ℝ} (j : Item n)
    (hpos : ∀ j : Item n, 0 < v j)
    (hlt : v j < v (reverseItem j)) :
    pairShare (1 / 2) v j < (1 / 2 : ℝ) := by
  exact pairShare_half_lt_half_of_lt_reverse j hpos hlt

/--
Appendix E, Lemma 16, indexed form: `q_j(1/2) = 1/2` when item `j` and its
opposite have equal value.
-/
theorem paper_lemma16_pairShare_half_eq_half_of_eq_reverse
    {n : ℕ} {v : Item n → ℝ} (j : Item n)
    (hpos : ∀ j : Item n, 0 < v j)
    (heq : v j = v (reverseItem j)) :
    pairShare (1 / 2) v j = (1 / 2 : ℝ) := by
  exact pairShare_half_eq_half_of_eq_reverse j hpos heq

/--
Appendix E, Lemma 16, indexed order form under the paper's strictly decreasing
value vector assumption.
-/
theorem paper_lemma16_half_lt_pairShare_half_of_val_lt_reverse
    {n : ℕ} {v : Item n → ℝ} (j : Item n)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hval : j.val < (reverseItem j).val) :
    (1 / 2 : ℝ) < pairShare (1 / 2) v j := by
  exact half_lt_pairShare_half_of_val_lt_reverse j hpos hdec hval

/--
Appendix E, Lemma 16, indexed order form under the paper's strictly decreasing
value vector assumption.
-/
theorem paper_lemma16_pairShare_half_lt_half_of_reverse_val_lt
    {n : ℕ} {v : Item n → ℝ} (j : Item n)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hval : (reverseItem j).val < j.val) :
    pairShare (1 / 2) v j < (1 / 2 : ℝ) := by
  exact pairShare_half_lt_half_of_reverse_val_lt j hpos hdec hval

/--
Appendix E, Lemma 16, indexed order form for the middle item.
-/
theorem paper_lemma16_pairShare_half_eq_half_of_val_eq_reverse
    {n : ℕ} {v : Item n → ℝ} (j : Item n)
    (hpos : ∀ j : Item n, 0 < v j)
    (hval : j.val = (reverseItem j).val) :
    pairShare (1 / 2) v j = (1 / 2 : ℝ) := by
  exact pairShare_half_eq_half_of_val_eq_reverse j hpos hval

/-- Appendix E, Lemma 16, zero-based midpoint arithmetic for `j` before center. -/
theorem paper_lemma16_val_lt_reverseItem_iff
    {n : ℕ} (j : Item n) :
    j.val < (reverseItem j).val ↔ 2 * j.val + 1 < n := by
  exact val_lt_reverseItem_iff j

/-- Appendix E, Lemma 16, zero-based midpoint arithmetic for `j` after center. -/
theorem paper_lemma16_reverseItem_val_lt_iff
    {n : ℕ} (j : Item n) :
    (reverseItem j).val < j.val ↔ n < 2 * j.val + 1 := by
  exact reverseItem_val_lt_iff j

/-- Appendix E, Lemma 16, zero-based midpoint arithmetic for the center item. -/
theorem paper_lemma16_val_eq_reverseItem_iff
    {n : ℕ} (j : Item n) :
    j.val = (reverseItem j).val ↔ 2 * j.val + 1 = n := by
  exact val_eq_reverseItem_iff j

/-- Appendix E, Lemma 16, zero-based arithmetic for `j` at or before center. -/
theorem paper_lemma16_val_le_reverseItem_iff
    {n : ℕ} (j : Item n) :
    j.val ≤ (reverseItem j).val ↔ 2 * j.val + 1 ≤ n := by
  exact val_le_reverseItem_iff j

/--
Problem 6 setup: in the two-type opposing-preference model, item normalizers
are the denominators of `q_j(α)`.
-/
theorem paper_problem6_twoType_itemNormalizer_eq
    {n : ℕ} (alpha : ℝ) (v : Item n → ℝ) (j : Item n) :
    TypeWeightedRecommendationModel.itemNormalizer
      (twoTypeReducedModel alpha v) j =
      alpha * v j + (1 - alpha) * v (reverseItem j) := by
  exact twoTypeReducedModel_itemNormalizer_eq alpha v j

/-- The two opposing types have the same best-item denominator. -/
theorem paper_problem6_twoType_bestItemUtility_one_eq_zero
    {n : ℕ} [NeZero n] (alpha : ℝ) (v : Item n → ℝ) :
    TypeWeightedRecommendationModel.bestItemUtility
        (twoTypeReducedModel alpha v) 1 =
      TypeWeightedRecommendationModel.bestItemUtility
        (twoTypeReducedModel alpha v) 0 := by
  exact twoTypeReducedModel_bestItemUtility_one_eq_zero alpha v

/-- Positive base values make the common best-item denominator positive. -/
theorem paper_problem6_twoType_bestItemUtility_zero_pos
    {n : ℕ} [NeZero n] (alpha : ℝ) (v : Item n → ℝ)
    (hpos : ∀ j : Item n, 0 < v j) :
    0 < TypeWeightedRecommendationModel.bestItemUtility
      (twoTypeReducedModel alpha v) 0 := by
  exact twoTypeReducedModel_bestItemUtility_zero_pos alpha v hpos

/-- Positive base values give each opposing type a positive row normalizer. -/
theorem paper_problem6_twoType_rowHasPositiveItem
    {n : ℕ} [NeZero n] (alpha : ℝ) (v : Item n → ℝ)
    (hpos : ∀ j : Item n, 0 < v j) :
    (twoTypeReducedModel alpha v).RowHasPositiveItem := by
  exact twoTypeReducedModel_rowHasPositiveItem alpha v hpos

/--
Problem 6 setup: in the two-type opposing-preference model, normalized item
utility expands as `q_j(α) x_j + (1 - q_j(α)) y_j`.
-/
theorem paper_problem6_normalizedItemUtility_eq_pairShare
    {n : ℕ} (alpha : ℝ) (v : Item n → ℝ) (ρ : TypePolicy 2 n)
    (j : Item n)
    (hden : 0 < alpha * v j + (1 - alpha) * v (reverseItem j)) :
    TypeWeightedRecommendationModel.normalizedItemUtility
      (twoTypeReducedModel alpha v) ρ j =
      pairShare alpha v j * (ρ 0 j).toReal +
        (1 - pairShare alpha v j) * (ρ 1 j).toReal := by
  exact twoTypeReducedModel_normalizedItemUtility_eq_pairShare
    alpha v ρ j hden

/--
Problem 6 LP feasibility is exactly the item-fairness epigraph for the
two-type opposing-preference reduced model.
-/
theorem paper_problem6_LPFeasible_iff_le_itemFairness
    {n : ℕ} [NeZero n]
    (alpha : ℝ) (v : Item n → ℝ) (ρ : TypePolicy 2 n) (ell : ℝ)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j) :
    problem6LPFeasible alpha v ρ ell ↔
      ell ≤ TypeWeightedRecommendationModel.itemFairness
        (twoTypeReducedModel alpha v) ρ := by
  exact problem6LPFeasible_iff_le_itemFairness
    alpha v ρ ell halpha0 halpha1 hpos

/--
Problem 6 LP objective equivalence: maximizing the paper's `λ` in the
opposing-preference LP has the same value as the reduced type-level
item-fairness optimum.
-/
theorem paper_problem6_LPOptimalValue_eq_optimalItemFairness
    {n : ℕ} [NeZero n]
    (alpha : ℝ) (v : Item n → ℝ)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j) :
    problem6LPOptimalValue alpha v =
      TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel alpha v) := by
  exact problem6LPOptimalValue_eq_optimalItemFairness
    alpha v halpha0 halpha1 hpos

/-- Problem 6 LP row constraint `∑_j x_j = 1`. -/
theorem paper_problem6_typeZero_sum_eq_one
    {n : ℕ} (ρ : TypePolicy 2 n) :
    (∑ j : Item n, (ρ 0 j).toReal) = 1 := by
  exact problem6_typeZero_sum_eq_one ρ

/-- Problem 6 LP row constraint `∑_j y_j = 1`. -/
theorem paper_problem6_typeOne_sum_eq_one
    {n : ℕ} (ρ : TypePolicy 2 n) :
    (∑ j : Item n, (ρ 1 j).toReal) = 1 := by
  exact problem6_typeOne_sum_eq_one ρ

/--
Problem 6 real-vector feasibility extracted from a policy satisfying the
paper's epigraph constraints.
-/
theorem paper_problem6_realLPFeasible_of_policy
    {n : ℕ}
    {alpha : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 2 n} {ell : ℝ}
    (hfeas : problem6LPFeasible alpha v ρ ell) :
    Problem6RealLPFeasible alpha v
      (fun j : Item n => (ρ 0 j).toReal)
      (fun j : Item n => (ρ 1 j).toReal) ell := by
  exact problem6RealLPFeasible_of_policy hfeas

/--
Problem 6 equality-form extraction: real `x,y,λ` optimal BFS data rebuilds an
optimal two-type policy for the epigraph LP.
-/
theorem paper_problem6_policyOptimal_of_equalityFormOptimalBFS
    {n : ℕ}
    {alpha : ℝ} {v : Item n → ℝ}
    {x y : Item n → ℝ} {ell : ℝ}
    (h : Problem6EqualityFormOptimalBFS alpha v x y ell) :
    Problem6PolicyOptimal alpha v
      (problem6PolicyOfRealVectors x y
        h.feasible.x_nonneg h.feasible.y_nonneg
        h.feasible.sum_x h.feasible.sum_y) ell := by
  exact problem6PolicyOptimal_of_equalityFormOptimalBFS h

/--
Problem 6 equality-form extraction: the paper's real optimal BFS supplies the
`Problem6EqualizedBasicOptimal` package consumed by Lemmas 4-11.
-/
theorem paper_problem6_equalizedBasicOptimal_of_equalityFormOptimalBFS
    {n : ℕ}
    {alpha : ℝ} {v : Item n → ℝ}
    {x y : Item n → ℝ} {ell : ℝ}
    (h : Problem6EqualityFormOptimalBFS alpha v x y ell) :
    Problem6EqualizedBasicOptimal alpha v
      (problem6PolicyOfRealVectors x y
        h.feasible.x_nonneg h.feasible.y_nonneg
        h.feasible.sum_x h.feasible.sum_y) ell := by
  exact problem6EqualizedBasicOptimal_of_equalityFormOptimalBFS h

/--
Problem 6 equality-form extraction: the paper's real optimal BFS carries the
basic-feasible support-count certificate for its rebuilt policy.
-/
theorem paper_problem6_basicFeasibleSupportCertificate_of_equalityFormOptimalBFS
    {n : ℕ}
    {alpha : ℝ} {v : Item n → ℝ}
    {x y : Item n → ℝ} {ell : ℝ}
    (h : Problem6EqualityFormOptimalBFS alpha v x y ell) :
    TypePolicy.BasicFeasibleSupportCertificate
      (problem6PolicyOfRealVectors x y
        h.feasible.x_nonneg h.feasible.y_nonneg
        h.feasible.sum_x h.feasible.sum_y) := by
  exact h.basic_feasible

/--
Problem 6 optimal-BFS package: expose the basic-feasible support-count
certificate used by Appendix D, Lemma 4.
-/
theorem paper_problem6_equalizedBasicOptimal_basicFeasibleSupportCertificate
    {n : ℕ}
    {alpha : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 2 n} {ell : ℝ}
    (h : Problem6EqualizedBasicOptimal alpha v ρ ell) :
    TypePolicy.BasicFeasibleSupportCertificate ρ := by
  exact h.basic_feasible

/--
Appendix D, Lemma 4, Part 1 directly from the paper's Problem 6
equalized optimal BFS package: at most `n + 1` positive `x_j,y_j` variables.
-/
theorem paper_lemma4_problem6_active_pairs_le_n_add_one_of_equalizedBasicOptimal
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 2 n} {ell : ℝ}
    (h : Problem6EqualizedBasicOptimal alpha v ρ ell) :
    TypePolicy.activeTypeItemPairsCard ρ ≤ n + 1 := by
  exact TypePolicy.activePairsCard_le_n_add_one_of_basicFeasibleSupportCertificate_two
    ρ h.basic_feasible

/--
Appendix D, Lemma 4, Part 1 directly from the paper's Problem 6
equalized optimal BFS package: at least `n - 1` zero `x_j,y_j` variables.
-/
theorem paper_lemma4_problem6_inactive_pairs_ge_n_sub_one_of_equalizedBasicOptimal
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 2 n} {ell : ℝ}
    (h : Problem6EqualizedBasicOptimal alpha v ρ ell) :
    n - 1 ≤ TypePolicy.inactiveTypeItemPairsCard ρ := by
  exact TypePolicy.inactivePairsCard_ge_n_sub_one_of_basicFeasibleSupportCertificate_two
    ρ h.basic_feasible

/--
Problem 6 optimality certificate wrapper for the paper's eventual closed-form
LP solution.
-/
theorem paper_problem6_LPOptimalValue_eq_of_certificate
    {n : ℕ} [NeZero n]
    (alpha : ℝ) (v : Item n → ℝ) (ell : ℝ)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (cert : Problem6OptimalityCertificate alpha v ell) :
    problem6LPOptimalValue alpha v = ell := by
  exact problem6LPOptimalValue_eq_of_certificate
    alpha v ell halpha0 halpha1 hpos cert

/--
Problem 6 optimal-value theorem for an already-optimal epigraph policy/value
pair.
-/
theorem paper_problem6_LPOptimalValue_eq_of_policyOptimal
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 2 n} {ell : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hopt : Problem6PolicyOptimal alpha v ρ ell) :
    problem6LPOptimalValue alpha v = ell := by
  exact problem6LPOptimalValue_eq_of_policyOptimal
    halpha0 halpha1 hpos hopt

/--
Problem 6 / Problem 1 bridge: every Problem 6 optimal policy is feasible for
the reduced maximal-item-fairness problem at level `γ = 1`.
-/
theorem paper_problem6_policyOptimal_feasibleAtLevel_one
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 2 n} {ell : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hopt : Problem6PolicyOptimal alpha v ρ ell) :
    TypeWeightedRecommendationModel.feasibleAtLevel
      (twoTypeReducedModel alpha v) 1 ρ := by
  exact problem6PolicyOptimal_feasibleAtLevel_one
    halpha0 halpha1 hpos hopt

/--
Problem 6 / Problem 1 bridge in the other direction: a policy feasible at
maximal item-fairness level `γ = 1` solves Problem 6 with its item-fairness
value.
-/
theorem paper_problem6_policyOptimal_of_feasibleAtLevel_one
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 2 n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hfeas :
      TypeWeightedRecommendationModel.feasibleAtLevel
        (twoTypeReducedModel alpha v) 1 ρ) :
    Problem6PolicyOptimal alpha v ρ
      (TypeWeightedRecommendationModel.itemFairness
        (twoTypeReducedModel alpha v) ρ) := by
  exact problem6PolicyOptimal_of_feasibleAtLevel_one
    halpha0 halpha1 hpos hfeas

/--
The selected equality-form optimal BFS policy is feasible for the reduced
maximal-item-fairness problem.
-/
theorem paper_problem6_equalizedBasicOptimal_feasibleAtLevel_one
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 2 n} {ell : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (h : Problem6EqualizedBasicOptimal alpha v ρ ell) :
    TypeWeightedRecommendationModel.feasibleAtLevel
      (twoTypeReducedModel alpha v) 1 ρ := by
  exact problem6EqualizedBasicOptimal_feasibleAtLevel_one
    halpha0 halpha1 hpos h

/--
The selected equality-form optimal BFS policy contributes its type-fairness
value to the reduced `γ = 1` feasible-value set.
-/
theorem paper_problem6_equalizedBasicOptimal_typeFairness_mem_attainable_one
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 2 n} {ell : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (h : Problem6EqualizedBasicOptimal alpha v ρ ell) :
    TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel alpha v) ρ ∈
      TypeWeightedRecommendationModel.attainableTypeFairnessAtLevel
        (twoTypeReducedModel alpha v) 1 := by
  exact problem6EqualizedBasicOptimal_typeFairness_mem_attainable_one
    halpha0 halpha1 hpos h

/--
The selected equality-form optimal BFS policy's type fairness is below the
reduced `U^*_min(1, α)` optimum.
-/
theorem paper_problem6_equalizedBasicOptimal_typeFairness_le_optimalTypeFairnessAtLevel_one
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 2 n} {ell : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (h : Problem6EqualizedBasicOptimal alpha v ρ ell) :
    TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel alpha v) ρ ≤
      TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel alpha v) 1 := by
  exact problem6EqualizedBasicOptimal_typeFairness_le_optimalTypeFairnessAtLevel_one
    halpha0 halpha1 hpos h

/--
If the selected equality-form optimal BFS policy dominates all reduced
`γ = 1` feasible policies in type fairness, then it realizes
`U^*_min(1, α)`.
-/
theorem paper_problem6_equalizedBasicOptimal_optimalTypeFairnessAtLevel_one_eq_of_upper_bound
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 2 n} {ell : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (h : Problem6EqualizedBasicOptimal alpha v ρ ell)
    (hupper :
      ∀ ρ' : TypePolicy 2 n,
        TypeWeightedRecommendationModel.feasibleAtLevel
          (twoTypeReducedModel alpha v) 1 ρ' →
        TypeWeightedRecommendationModel.typeFairness
          (twoTypeReducedModel alpha v) ρ' ≤
        TypeWeightedRecommendationModel.typeFairness
          (twoTypeReducedModel alpha v) ρ) :
    TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel alpha v) 1 =
      TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel alpha v) ρ := by
  exact problem6EqualizedBasicOptimal_optimalTypeFairnessAtLevel_one_eq_of_upper_bound
    halpha0 halpha1 hpos h hupper

/--
Upper-bound bridge, uniqueness form: a reduced `γ = 1` feasible policy that
is equalized and satisfies the shared-item sparsity bound is the selected
equality-form optimal BFS policy.
-/
theorem paper_problem6_equalizedBasicOptimal_policy_eq_of_feasibleAtLevel_one_equalized_shared
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {ρ ρ' : TypePolicy 2 n} {ell : ℝ}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (h : Problem6EqualizedBasicOptimal alpha v ρ ell)
    (hfeas' :
      TypeWeightedRecommendationModel.feasibleAtLevel
        (twoTypeReducedModel alpha v) 1 ρ')
    (hitem_eq' :
      ∀ l : Item n,
        pairShare alpha v l * (ρ' 0 l).toReal +
          (1 - pairShare alpha v l) * (ρ' 1 l).toReal =
        TypeWeightedRecommendationModel.itemFairness
          (twoTypeReducedModel alpha v) ρ')
    (hshared' : TypePolicy.SharedItemsBound ρ') :
    ρ' = ρ := by
  exact problem6EqualizedBasicOptimal_policy_eq_of_feasibleAtLevel_one_equalized_shared
    hn halpha0 halpha1 hpos hdec h hfeas' hitem_eq' hshared'

/--
The selected equality-form optimal BFS policy has the same type-fairness value
as any reduced `γ = 1` feasible, equalized, shared policy.
-/
theorem paper_problem6_equalizedBasicOptimal_typeFairness_eq_of_feasibleAtLevel_one_equalized_shared
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {ρ ρ' : TypePolicy 2 n} {ell : ℝ}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (h : Problem6EqualizedBasicOptimal alpha v ρ ell)
    (hfeas' :
      TypeWeightedRecommendationModel.feasibleAtLevel
        (twoTypeReducedModel alpha v) 1 ρ')
    (hitem_eq' :
      ∀ l : Item n,
        pairShare alpha v l * (ρ' 0 l).toReal +
          (1 - pairShare alpha v l) * (ρ' 1 l).toReal =
        TypeWeightedRecommendationModel.itemFairness
          (twoTypeReducedModel alpha v) ρ')
    (hshared' : TypePolicy.SharedItemsBound ρ') :
    TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel alpha v) ρ' =
      TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel alpha v) ρ := by
  exact problem6EqualizedBasicOptimal_typeFairness_eq_of_feasibleAtLevel_one_equalized_shared
    hn halpha0 halpha1 hpos hdec h hfeas' hitem_eq' hshared'

/--
If every reduced `γ = 1` feasible policy is in the equalized/shared canonical
form, then the selected equality-form optimal BFS policy realizes
`U^*_min(1, α)`.
-/
theorem paper_problem6_equalizedBasicOptimal_optimalTypeFairnessAtLevel_one_eq_of_all_feasible_equalized_shared
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 2 n} {ell : ℝ}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (h : Problem6EqualizedBasicOptimal alpha v ρ ell)
    (hcanonical :
      ∀ ρ' : TypePolicy 2 n,
        TypeWeightedRecommendationModel.feasibleAtLevel
          (twoTypeReducedModel alpha v) 1 ρ' →
        (∀ l : Item n,
          pairShare alpha v l * (ρ' 0 l).toReal +
            (1 - pairShare alpha v l) * (ρ' 1 l).toReal =
          TypeWeightedRecommendationModel.itemFairness
            (twoTypeReducedModel alpha v) ρ') ∧
        TypePolicy.SharedItemsBound ρ') :
    TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel alpha v) 1 =
      TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel alpha v) ρ := by
  exact problem6EqualizedBasicOptimal_optimalTypeFairnessAtLevel_one_eq_of_all_feasible_equalized_shared
    hn halpha0 halpha1 hpos hdec h hcanonical

/--
Proposition-1-shaped upper-bound bridge: if every reduced `γ = 1` feasible
policy has an equalized/shared canonical representative with weakly larger type
fairness, then the selected equality-form optimal BFS policy realizes
`U^*_min(1, α)`.
-/
theorem paper_problem6_equalizedBasicOptimal_optimalTypeFairnessAtLevel_one_eq_of_feasible_canonicalization
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 2 n} {ell : ℝ}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (h : Problem6EqualizedBasicOptimal alpha v ρ ell)
    (hcanonical :
      ∀ ρ' : TypePolicy 2 n,
        TypeWeightedRecommendationModel.feasibleAtLevel
          (twoTypeReducedModel alpha v) 1 ρ' →
        ∃ ρbar : TypePolicy 2 n,
          TypeWeightedRecommendationModel.feasibleAtLevel
            (twoTypeReducedModel alpha v) 1 ρbar ∧
          (∀ l : Item n,
            pairShare alpha v l * (ρbar 0 l).toReal +
              (1 - pairShare alpha v l) * (ρbar 1 l).toReal =
            TypeWeightedRecommendationModel.itemFairness
              (twoTypeReducedModel alpha v) ρbar) ∧
          TypePolicy.SharedItemsBound ρbar ∧
          TypeWeightedRecommendationModel.typeFairness
            (twoTypeReducedModel alpha v) ρ' ≤
          TypeWeightedRecommendationModel.typeFairness
            (twoTypeReducedModel alpha v) ρbar) :
    TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel alpha v) 1 =
      TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel alpha v) ρ := by
  exact problem6EqualizedBasicOptimal_optimalTypeFairnessAtLevel_one_eq_of_feasible_canonicalization
    hn halpha0 halpha1 hpos hdec h hcanonical

/--
Problem 6 equality-form helper: for an equality-form optimal BFS policy, every
item equality is equality to the reduced item-fairness value itself.
-/
theorem paper_problem6_equalizedBasicOptimal_item_value_eq_itemFairness
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 2 n} {ell : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (h : Problem6EqualizedBasicOptimal alpha v ρ ell)
    (l : Item n) :
    pairShare alpha v l * (ρ 0 l).toReal +
        (1 - pairShare alpha v l) * (ρ 1 l).toReal =
      TypeWeightedRecommendationModel.itemFairness
        (twoTypeReducedModel alpha v) ρ := by
  exact problem6EqualizedBasicOptimal_item_value_eq_itemFairness
    halpha0 halpha1 hpos h l

/--
Proposition-1/LP-selection bridge: dominating equality-form optimal BFS
representatives supply the canonical equalized/shared representatives used by
the reduced `γ = 1` optimality bridge.
-/
theorem paper_problem6_feasibleCanonicalization_of_equalizedBasicOptimal_dominance
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdom :
      ∀ ρ' : TypePolicy 2 n,
        TypeWeightedRecommendationModel.feasibleAtLevel
          (twoTypeReducedModel alpha v) 1 ρ' →
        ∃ (ρbar : TypePolicy 2 n) (ellbar : ℝ),
          Problem6EqualizedBasicOptimal alpha v ρbar ellbar ∧
          TypeWeightedRecommendationModel.typeFairness
            (twoTypeReducedModel alpha v) ρ' ≤
          TypeWeightedRecommendationModel.typeFairness
            (twoTypeReducedModel alpha v) ρbar) :
      ∀ ρ' : TypePolicy 2 n,
        TypeWeightedRecommendationModel.feasibleAtLevel
          (twoTypeReducedModel alpha v) 1 ρ' →
        ∃ ρbar : TypePolicy 2 n,
          TypeWeightedRecommendationModel.feasibleAtLevel
            (twoTypeReducedModel alpha v) 1 ρbar ∧
          (∀ l : Item n,
            pairShare alpha v l * (ρbar 0 l).toReal +
              (1 - pairShare alpha v l) * (ρbar 1 l).toReal =
            TypeWeightedRecommendationModel.itemFairness
              (twoTypeReducedModel alpha v) ρbar) ∧
          TypePolicy.SharedItemsBound ρbar ∧
          TypeWeightedRecommendationModel.typeFairness
            (twoTypeReducedModel alpha v) ρ' ≤
          TypeWeightedRecommendationModel.typeFairness
            (twoTypeReducedModel alpha v) ρbar := by
  exact problem6_feasibleCanonicalization_of_equalizedBasicOptimal_dominance
    halpha0 halpha1 hpos hdom

/--
Selected-policy optimality bridge in LP-selection form: if every reduced
`γ = 1` feasible policy is weakly dominated by some equality-form optimal BFS
representative, then the selected equality-form optimal BFS policy realizes
`U^*_min(1, α)`.
-/
theorem paper_problem6_equalizedBasicOptimal_optimalTypeFairnessAtLevel_one_eq_of_equalizedBasicOptimal_dominance
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 2 n} {ell : ℝ}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (h : Problem6EqualizedBasicOptimal alpha v ρ ell)
    (hdom :
      ∀ ρ' : TypePolicy 2 n,
        TypeWeightedRecommendationModel.feasibleAtLevel
          (twoTypeReducedModel alpha v) 1 ρ' →
        ∃ (ρbar : TypePolicy 2 n) (ellbar : ℝ),
          Problem6EqualizedBasicOptimal alpha v ρbar ellbar ∧
          TypeWeightedRecommendationModel.typeFairness
            (twoTypeReducedModel alpha v) ρ' ≤
          TypeWeightedRecommendationModel.typeFairness
            (twoTypeReducedModel alpha v) ρbar) :
    TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel alpha v) 1 =
      TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel alpha v) ρ := by
  exact problem6EqualizedBasicOptimal_optimalTypeFairnessAtLevel_one_eq_of_equalizedBasicOptimal_dominance
    hn halpha0 halpha1 hpos hdec h hdom

/--
Selected-policy optimality bridge from a single optimal-at-level equality-form
BFS representative.
-/
theorem paper_problem6_equalizedBasicOptimal_optimalTypeFairnessAtLevel_one_eq_of_equalizedBasicOptimal_isOptimalAtLevel
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ}
    {ρ ρstar : TypePolicy 2 n} {ell ellstar : ℝ}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (h : Problem6EqualizedBasicOptimal alpha v ρ ell)
    (hstar : Problem6EqualizedBasicOptimal alpha v ρstar ellstar)
    (hstar_opt :
      TypeWeightedRecommendationModel.IsOptimalAtLevel
        (twoTypeReducedModel alpha v) 1 ρstar) :
    TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel alpha v) 1 =
      TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel alpha v) ρ := by
  exact problem6EqualizedBasicOptimal_optimalTypeFairnessAtLevel_one_eq_of_equalizedBasicOptimal_isOptimalAtLevel
    hn halpha0 halpha1 hpos hdec h hstar hstar_opt

/--
Appendix D, Lemma 5: the closed-form value for any sparse equalized
Problem 6 solution.
-/
theorem paper_lemma5_problem6_closed_value
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    {x y : Item n → ℝ} {ell : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (h : Problem6SparseEqualized alpha v t x y ell) :
    ell = problem6ClosedValue alpha v t := by
  exact problem6SparseEqualized_value_eq_closed
    halpha0 halpha1 hpos h

/-- Appendix D, Lemma 5: the closed-form value is positive. -/
theorem paper_lemma5_problem6_closed_value_pos
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} (t : Item n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j) :
    0 < problem6ClosedValue alpha v t := by
  exact problem6ClosedValue_pos t halpha0 halpha1 hpos

/-- Appendix D, Lemma 5: the closed-form `x_j` coordinates sum to one. -/
theorem paper_lemma5_problem6_closedX_sum_eq_one
    {n : ℕ} (alpha : ℝ) (v : Item n → ℝ) (t : Item n) :
    (∑ j : Item n, problem6ClosedX alpha v t j) = 1 := by
  exact problem6ClosedX_sum_eq_one alpha v t

/-- Appendix D, Lemma 5: the closed-form `y_j` coordinates sum to one. -/
theorem paper_lemma5_problem6_closedY_sum_eq_one
    {n : ℕ} (alpha : ℝ) (v : Item n → ℝ) (t : Item n) :
    (∑ j : Item n, problem6ClosedY alpha v t j) = 1 := by
  exact problem6ClosedY_sum_eq_one alpha v t

/--
Appendix D, Lemma 5: the closed-form coordinates equalize every Problem 6
item constraint.
-/
theorem paper_lemma5_problem6_closed_item_eq
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} (t j : Item n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j) :
    pairShare alpha v j * problem6ClosedX alpha v t j +
        (1 - pairShare alpha v j) * problem6ClosedY alpha v t j =
      problem6ClosedValue alpha v t := by
  exact problem6Closed_item_eq t j halpha0 halpha1 hpos

/--
Appendix D, Lemma 5: the closed-form coordinates satisfy the sparse,
equalized real LP shape for any pivot.
-/
theorem paper_lemma5_problem6_closed_sparseEqualized
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} (t : Item n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j) :
    Problem6SparseEqualized alpha v t
      (problem6ClosedX alpha v t) (problem6ClosedY alpha v t)
      (problem6ClosedValue alpha v t) := by
  exact problem6Closed_sparseEqualized t halpha0 halpha1 hpos

/--
Appendix D, Lemma 5 to Problem 6 policy bridge: under pivot nonnegativity,
all closed-form `x_j` coordinates are nonnegative.
-/
theorem paper_lemma5_problem6_closedX_nonneg
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hpivot : Problem6ClosedNonnegativePivots alpha v t)
    (j : Item n) :
    0 ≤ problem6ClosedX alpha v t j := by
  exact problem6ClosedX_nonneg halpha0 halpha1 hpos hpivot j

/--
Appendix D, Lemma 5 to Problem 6 policy bridge: under pivot nonnegativity,
all closed-form `y_j` coordinates are nonnegative.
-/
theorem paper_lemma5_problem6_closedY_nonneg
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hpivot : Problem6ClosedNonnegativePivots alpha v t)
    (j : Item n) :
    0 ≤ problem6ClosedY alpha v t j := by
  exact problem6ClosedY_nonneg halpha0 halpha1 hpos hpivot j

/--
Problem 6 policy bridge: the closed-form coordinates build a feasible
two-type policy whenever the pivot coordinates are nonnegative.
-/
theorem paper_problem6_closedPolicy_feasible
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hpivot : Problem6ClosedNonnegativePivots alpha v t) :
    problem6LPFeasible alpha v
      (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot)
      (problem6ClosedValue alpha v t) := by
  exact problem6ClosedPolicy_feasible halpha0 halpha1 hpos hpivot

/--
Problem 6 policy bridge: denominator bounds imply nonnegative closed-form
pivot coordinates.
-/
theorem paper_problem6_closedNonnegativePivots_of_denominatorBounds
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hbounds : Problem6ClosedPivotDenominatorBounds alpha v t) :
    Problem6ClosedNonnegativePivots alpha v t := by
  exact problem6ClosedNonnegativePivots_of_denominatorBounds
    halpha0 halpha1 hpos hbounds

/--
Problem 6 policy bridge: nonnegative closed-form pivot coordinates imply the
denominator bounds.
-/
theorem paper_problem6_closedPivotDenominatorBounds_of_nonnegativePivots
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hpivot : Problem6ClosedNonnegativePivots alpha v t) :
    Problem6ClosedPivotDenominatorBounds alpha v t := by
  exact problem6ClosedPivotDenominatorBounds_of_nonnegativePivots
    halpha0 halpha1 hpos hpivot

/--
Appendix D, Lemma 5 gap algebra: the left denominator slack is the upper
gap inequality written as denominator form.
-/
theorem paper_lemma5_problem6_closedDenominator_sub_leftSum_eq
    {n : ℕ} (alpha : ℝ) (v : Item n → ℝ) (t : Item n) :
    problem6ClosedDenominator alpha v t -
        problem6LeftSum alpha v t =
      1 - (1 - pairShare alpha v t) *
        problem6PivotGap alpha v t := by
  exact problem6ClosedDenominator_sub_leftSum_eq alpha v t

/--
Appendix D, Lemma 5 gap algebra: the right denominator slack is the lower
gap inequality written as denominator form.
-/
theorem paper_lemma5_problem6_closedDenominator_sub_rightSum_eq
    {n : ℕ} (alpha : ℝ) (v : Item n → ℝ) (t : Item n) :
    problem6ClosedDenominator alpha v t -
        problem6RightSum alpha v t =
      1 + pairShare alpha v t * problem6PivotGap alpha v t := by
  exact problem6ClosedDenominator_sub_rightSum_eq alpha v t

/--
Appendix D, Lemma 5 pivot feasibility: lower and upper bounds on the crossing
gap imply the denominator bounds for the closed-form pivot.
-/
theorem paper_lemma5_problem6_closedPivotDenominatorBounds_of_pivotGap_bounds
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hlower : - (pairShare alpha v t)⁻¹ ≤
      problem6PivotGap alpha v t)
    (hupper : problem6PivotGap alpha v t ≤
      (1 - pairShare alpha v t)⁻¹) :
    Problem6ClosedPivotDenominatorBounds alpha v t := by
  exact problem6ClosedPivotDenominatorBounds_of_pivotGap_bounds
    halpha0 halpha1 hpos hlower hupper

/--
Appendix D, Lemma 5 pivot existence: a finite crossing argument selects a
closed-form pivot whose denominator bounds hold.
-/
theorem paper_lemma5_problem6_closedPivotDenominatorBounds_exists
    {n : ℕ} [NeZero n] {alpha : ℝ} {v : Item n → ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j) :
    ∃ t : Item n, Problem6ClosedPivotDenominatorBounds alpha v t := by
  exact problem6ClosedPivotDenominatorBounds_exists
    halpha0 halpha1 hpos

/--
Appendix D, Lemma 5 denominator-bound bridge: an active sparse equalized
solution supplies the closed-form denominator bounds at the same pivot.
-/
theorem paper_lemma5_problem6_closedPivotDenominatorBounds_of_sparseEqualizedActive
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    {x y : Item n → ℝ} {ell : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (h : Problem6SparseEqualizedActive alpha v t x y ell) :
    Problem6ClosedPivotDenominatorBounds alpha v t := by
  exact problem6ClosedPivotDenominatorBounds_of_sparseEqualizedActive
    halpha0 halpha1 hpos h

/--
Problem 6 policy bridge: denominator bounds are enough for closed-policy
feasibility.
-/
theorem paper_problem6_closedPolicy_feasible_of_denominatorBounds
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hbounds : Problem6ClosedPivotDenominatorBounds alpha v t) :
    problem6LPFeasible alpha v
      (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos
        (problem6ClosedNonnegativePivots_of_denominatorBounds
          halpha0 halpha1 hpos hbounds))
      (problem6ClosedValue alpha v t) := by
  exact problem6ClosedPolicy_feasible_of_denominatorBounds
    halpha0 halpha1 hpos hbounds

/--
Appendix D, Lemma 5 closed-policy bridge: the closed-form policy has the
threshold support shape used in Lemma 4.
-/
theorem paper_problem6_closedPolicy_twoTypeThresholdSupport
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hpivot : Problem6ClosedNonnegativePivots alpha v t) :
    TypePolicy.TwoTypeThresholdSupport
      (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot) := by
  exact problem6ClosedPolicy_twoTypeThresholdSupport
    halpha0 halpha1 hpos hpivot

/--
Appendix D, Lemma 5 closed-policy bridge: threshold support gives the paper's
basic-feasible support-count certificate for the closed-form policy.
-/
theorem paper_problem6_closedPolicy_basicFeasibleSupportCertificate
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hpivot : Problem6ClosedNonnegativePivots alpha v t) :
    TypePolicy.BasicFeasibleSupportCertificate
      (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot) := by
  exact problem6ClosedPolicy_basicFeasibleSupportCertificate
    halpha0 halpha1 hpos hpivot

/--
Problem 6 dual certificate: the paper's closed-form dual weights sum to one.
-/
theorem paper_problem6_closedDualWeight_sum_eq_one
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j) :
    (∑ j : Item n, problem6ClosedDualWeight alpha v t j) = 1 := by
  exact problem6ClosedDualWeight_sum_eq_one
    (alpha := alpha) (v := v) (t := t) halpha0 halpha1 hpos

/--
Problem 6 dual certificate: the closed-form dual weights upper-bound every
feasible Problem 6 LP value by the Lemma 5 closed value at pivot `t`.
-/
theorem paper_problem6_closedDual_upper_bound
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (ρ : TypePolicy 2 n) (ell : ℝ)
    (hfeas : problem6LPFeasible alpha v ρ ell) :
    ell ≤ problem6ClosedValue alpha v t := by
  exact problem6ClosedDual_upper_bound
    halpha0 halpha1 hpos hdec ρ ell hfeas

/--
Problem 6 closed-form optimality certificate: denominator bounds now supply
both primal feasibility and the closed-form dual upper bound.
-/
theorem paper_problem6_closedOptimalityCertificate_of_denominatorBounds
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hbounds : Problem6ClosedPivotDenominatorBounds alpha v t) :
    Problem6ClosedOptimalityCertificate alpha v t := by
  exact problem6ClosedOptimalityCertificate_of_denominatorBounds
    halpha0 halpha1 hpos hdec hbounds

/--
Appendix D, Lemma 5 full certificate: the finite pivot choice and closed dual
produce a closed-form optimality certificate.
-/
theorem paper_problem6_closedOptimalityCertificate_exists
    {n : ℕ} [NeZero n] {alpha : ℝ} {v : Item n → ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v) :
    ∃ t : Item n, Problem6ClosedOptimalityCertificate alpha v t := by
  exact problem6ClosedOptimalityCertificate_exists
    halpha0 halpha1 hpos hdec

/--
Appendix D, Lemma 5 canonical-pivot certificate: the first crossing pivot
supplies the full closed-form optimality certificate.
-/
theorem paper_problem6_firstClosedPivot_optimalityCertificate
    {n : ℕ} [NeZero n] {alpha : ℝ} {v : Item n → ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v) :
    Problem6ClosedOptimalityCertificate alpha v
      (problem6FirstClosedPivot alpha v halpha0 halpha1 hpos) := by
  exact problem6FirstClosedPivot_optimalityCertificate
    halpha0 halpha1 hpos hdec

/--
Appendix D, Lemma 5 closed-policy bridge: a closed-form optimality certificate
builds the paper's equality-form optimal BFS package; the support-count field
comes from the closed policy's threshold support.
-/
theorem paper_problem6_equalizedBasicOptimal_of_closed_certificate
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (cert : Problem6ClosedOptimalityCertificate alpha v t) :
    let hpivot : Problem6ClosedNonnegativePivots alpha v t :=
      problem6ClosedNonnegativePivots_of_denominatorBounds
        halpha0 halpha1 hpos cert.denominator_bounds
    Problem6EqualizedBasicOptimal alpha v
      (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot)
      (problem6ClosedValue alpha v t) := by
  exact problem6EqualizedBasicOptimal_of_closed_certificate
    halpha0 halpha1 hpos cert

/--
Appendix D, Lemma 5 canonical-pivot BFS package: the first crossing pivot
builds the paper's equality-form optimal BFS policy.
-/
theorem paper_problem6_firstClosedPivot_equalizedBasicOptimal
    {n : ℕ} [NeZero n] {alpha : ℝ} {v : Item n → ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v) :
    let t : Item n :=
      problem6FirstClosedPivot alpha v halpha0 halpha1 hpos
    let cert : Problem6ClosedOptimalityCertificate alpha v t :=
      problem6FirstClosedPivot_optimalityCertificate
        halpha0 halpha1 hpos hdec
    let hpivot : Problem6ClosedNonnegativePivots alpha v t :=
      problem6ClosedNonnegativePivots_of_denominatorBounds
        halpha0 halpha1 hpos cert.denominator_bounds
    Problem6EqualizedBasicOptimal alpha v
      (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot)
      (problem6ClosedValue alpha v t) := by
  exact problem6FirstClosedPivot_equalizedBasicOptimal
    halpha0 halpha1 hpos hdec

/--
Appendix D, Lemma 5 existence as an equality-form optimal BFS package: the
closed-form pivot, policy, and value solve Problem 6.
-/
theorem paper_problem6_equalizedBasicOptimal_exists_closed
    {n : ℕ} [NeZero n] {alpha : ℝ} {v : Item n → ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v) :
    ∃ t : Item n,
      ∃ cert : Problem6ClosedOptimalityCertificate alpha v t,
        let hpivot : Problem6ClosedNonnegativePivots alpha v t :=
          problem6ClosedNonnegativePivots_of_denominatorBounds
            halpha0 halpha1 hpos cert.denominator_bounds
        Problem6EqualizedBasicOptimal alpha v
          (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot)
          (problem6ClosedValue alpha v t) := by
  exact problem6EqualizedBasicOptimal_exists_closed
    halpha0 halpha1 hpos hdec

/--
Appendix D, Lemma 5 existence, paper-facing form: Problem 6 has an
equality-form optimal BFS representative.
-/
theorem paper_problem6_equalizedBasicOptimal_exists
    {n : ℕ} [NeZero n] {alpha : ℝ} {v : Item n → ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v) :
    ∃ (ρ : TypePolicy 2 n) (ell : ℝ),
      Problem6EqualizedBasicOptimal alpha v ρ ell := by
  exact problem6EqualizedBasicOptimal_exists
    halpha0 halpha1 hpos hdec

/--
Problem 6/Problem 1 bridge: the Lemma 5 equality-form optimum supplies a
reduced `γ = 1` feasible policy.
-/
theorem paper_problem6_equalizedBasicOptimal_feasibleAtLevel_one_exists
    {n : ℕ} [NeZero n] {alpha : ℝ} {v : Item n → ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v) :
    ∃ (ρ : TypePolicy 2 n) (ell : ℝ),
      Problem6EqualizedBasicOptimal alpha v ρ ell ∧
        TypeWeightedRecommendationModel.feasibleAtLevel
          (twoTypeReducedModel alpha v) 1 ρ := by
  exact problem6EqualizedBasicOptimal_feasibleAtLevel_one_exists
    halpha0 halpha1 hpos hdec

/--
Appendix D, Lemma 4/5 bridge: an equalized optimal Problem 6 policy supplies
the closed-form optimality certificate at its active sparse pivot.
-/
theorem paper_problem6_closedOptimalityCertificate_of_policyOptimal_equalized_of_two_lt
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 2 n} {ell : ℝ}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hitem_eq :
      ∀ l : Item n,
        pairShare alpha v l * (ρ 0 l).toReal +
          (1 - pairShare alpha v l) * (ρ 1 l).toReal = ell)
    (hopt : Problem6PolicyOptimal alpha v ρ ell)
    (hshared : TypePolicy.SharedItemsBound ρ) :
    Problem6ClosedOptimalityCertificate alpha v
      (TypePolicy.lastActiveTypeZero ρ) := by
  exact problem6ClosedOptimalityCertificate_of_policyOptimal_equalized_of_two_lt
    hn halpha0 halpha1 hpos hdec hitem_eq hopt hshared

/--
Appendix D, Lemma 4/5 bridge for the paper's equality-form optimal BFS
package: the selected active pivot supplies the closed-form optimality
certificate.
-/
theorem paper_problem6_closedOptimalityCertificate_of_equalizedBasicOptimal_of_two_lt
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 2 n} {ell : ℝ}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (h : Problem6EqualizedBasicOptimal alpha v ρ ell) :
    Problem6ClosedOptimalityCertificate alpha v
      (TypePolicy.lastActiveTypeZero ρ) := by
  exact problem6ClosedOptimalityCertificate_of_equalizedBasicOptimal_of_two_lt
    hn halpha0 halpha1 hpos hdec h

/--
Problem 6 closed-form optimal-value wrapper: a denominator-bound plus
upper-bound certificate proves the LP optimum equals the Lemma 5 value.
-/
theorem paper_problem6_LPOptimalValue_eq_closedValue_of_closed_certificate
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (cert : Problem6ClosedOptimalityCertificate alpha v t) :
    problem6LPOptimalValue alpha v = problem6ClosedValue alpha v t := by
  exact problem6LPOptimalValue_eq_closedValue_of_closed_certificate
    halpha0 halpha1 hpos cert

/--
Appendix D, Lemma 4/5 optimal-value bridge: an equalized optimal Problem 6
policy identifies the LP optimum with the Lemma 5 closed value at its active
sparse pivot.
-/
theorem paper_problem6_LPOptimalValue_eq_closedValue_of_policyOptimal_equalized_of_two_lt
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 2 n} {ell : ℝ}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hitem_eq :
      ∀ l : Item n,
        pairShare alpha v l * (ρ 0 l).toReal +
          (1 - pairShare alpha v l) * (ρ 1 l).toReal = ell)
    (hopt : Problem6PolicyOptimal alpha v ρ ell)
    (hshared : TypePolicy.SharedItemsBound ρ) :
    problem6LPOptimalValue alpha v =
      problem6ClosedValue alpha v (TypePolicy.lastActiveTypeZero ρ) := by
  exact problem6LPOptimalValue_eq_closedValue_of_policyOptimal_equalized_of_two_lt
    hn halpha0 halpha1 hpos hdec hitem_eq hopt hshared

/--
Appendix D, Lemma 4/5 optimal-value bridge for the paper's equality-form
optimal BFS package.
-/
theorem paper_problem6_LPOptimalValue_eq_closedValue_of_equalizedBasicOptimal_of_two_lt
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 2 n} {ell : ℝ}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (h : Problem6EqualizedBasicOptimal alpha v ρ ell) :
    problem6LPOptimalValue alpha v =
      problem6ClosedValue alpha v (TypePolicy.lastActiveTypeZero ρ) := by
  exact problem6LPOptimalValue_eq_closedValue_of_equalizedBasicOptimal_of_two_lt
    hn halpha0 halpha1 hpos hdec h

/--
Appendix D, Lemma 11 interval form: if the same pivot has closed-form
optimality certificates at `α` and `α'`, then the Problem 6 LP optimum is
monotone on that fixed-pivot interval.
-/
theorem paper_lemma11_problem6LPOptimalValue_mono_of_fixed_pivot_cert
    {n : ℕ} [NeZero n]
    {alpha alpha' : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter : t.val ≤ (reverseItem t).val)
    (cert : Problem6ClosedOptimalityCertificate alpha v t)
    (cert' : Problem6ClosedOptimalityCertificate alpha' v t) :
    problem6LPOptimalValue alpha v ≤ problem6LPOptimalValue alpha' v := by
  exact lemma11_problem6LPOptimalValue_mono_of_fixed_pivot_cert
    halpha0 halpha1 halpha0' halpha1' halpha_le
    hpos hdec hcenter cert cert'

/--
Appendix D, Lemma 11 selected-policy fixed-interval form: if two equalized
optimal policies select the same first-half pivot, then the Problem 6 LP
optimum is monotone between their `α` values.
-/
theorem paper_lemma11_problem6LPOptimalValue_mono_of_same_selected_pivot
    {n : ℕ} [NeZero n]
    {alpha alpha' : ℝ} {v : Item n → ℝ}
    {ρ ρ' : TypePolicy 2 n} {ell ell' : ℝ}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hpivot :
      TypePolicy.lastActiveTypeZero ρ =
        TypePolicy.lastActiveTypeZero ρ')
    (hcenter :
      (TypePolicy.lastActiveTypeZero ρ).val ≤
        (reverseItem (TypePolicy.lastActiveTypeZero ρ)).val)
    (hitem_eq :
      ∀ l : Item n,
        pairShare alpha v l * (ρ 0 l).toReal +
          (1 - pairShare alpha v l) * (ρ 1 l).toReal = ell)
    (hitem_eq' :
      ∀ l : Item n,
        pairShare alpha' v l * (ρ' 0 l).toReal +
          (1 - pairShare alpha' v l) * (ρ' 1 l).toReal = ell')
    (hopt : Problem6PolicyOptimal alpha v ρ ell)
    (hopt' : Problem6PolicyOptimal alpha' v ρ' ell')
    (hshared : TypePolicy.SharedItemsBound ρ)
    (hshared' : TypePolicy.SharedItemsBound ρ') :
    problem6LPOptimalValue alpha v ≤ problem6LPOptimalValue alpha' v := by
  exact lemma11_problem6LPOptimalValue_mono_of_same_selected_pivot
    hn halpha0 halpha1 halpha0' halpha1' halpha_le
    hpos hdec hpivot hcenter hitem_eq hitem_eq'
    hopt hopt' hshared hshared'

/--
Appendix D, Lemma 11 selected-policy fixed-interval form for the paper's
equality-form optimal BFS package.
-/
theorem paper_lemma11_problem6LPOptimalValue_mono_of_same_selected_equalizedBasicOptimal
    {n : ℕ} [NeZero n]
    {alpha alpha' : ℝ} {v : Item n → ℝ}
    {ρ ρ' : TypePolicy 2 n} {ell ell' : ℝ}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hpivot :
      TypePolicy.lastActiveTypeZero ρ =
        TypePolicy.lastActiveTypeZero ρ')
    (hcenter :
      (TypePolicy.lastActiveTypeZero ρ).val ≤
        (reverseItem (TypePolicy.lastActiveTypeZero ρ)).val)
    (h : Problem6EqualizedBasicOptimal alpha v ρ ell)
    (h' : Problem6EqualizedBasicOptimal alpha' v ρ' ell') :
    problem6LPOptimalValue alpha v ≤ problem6LPOptimalValue alpha' v := by
  exact lemma11_problem6LPOptimalValue_mono_of_same_selected_equalizedBasicOptimal
    hn halpha0 halpha1 halpha0' halpha1' halpha_le
    hpos hdec hpivot hcenter h h'

/--
Appendix D, Lemma 11 canonical first-pivot interval form: if the paper's
canonical Lemma 5 first crossing pivot stays fixed on an `A(t)` interval, then
the Problem 6 LP optimum is monotone there.
-/
theorem paper_lemma11_problem6LPOptimalValue_mono_of_same_firstClosedPivot
    {n : ℕ} [NeZero n]
    {alpha alpha' : ℝ} {v : Item n → ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hpivot :
      problem6FirstClosedPivot alpha v halpha0 halpha1 hpos =
        problem6FirstClosedPivot alpha' v halpha0' halpha1' hpos)
    (hcenter :
      (problem6FirstClosedPivot alpha v halpha0 halpha1 hpos).val ≤
        (reverseItem
          (problem6FirstClosedPivot alpha v halpha0 halpha1 hpos)).val) :
    problem6LPOptimalValue alpha v ≤ problem6LPOptimalValue alpha' v := by
  exact lemma11_problem6LPOptimalValue_mono_of_same_firstClosedPivot
    halpha0 halpha1 halpha0' halpha1' halpha_le
    hpos hdec hpivot hcenter

/--
Appendix D, Lemma 11 reduced-model form: on a certified fixed-pivot interval,
the reduced optimal item fairness is monotone in `α`.
-/
theorem paper_lemma11_reducedOptimalItemFairness_mono_of_fixed_pivot_cert
    {n : ℕ} [NeZero n]
    {alpha alpha' : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter : t.val ≤ (reverseItem t).val)
    (cert : Problem6ClosedOptimalityCertificate alpha v t)
    (cert' : Problem6ClosedOptimalityCertificate alpha' v t) :
    TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel alpha v) ≤
      TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel alpha' v) := by
  exact lemma11_reducedOptimalItemFairness_mono_of_fixed_pivot_cert
    halpha0 halpha1 halpha0' halpha1' halpha_le
    hpos hdec hcenter cert cert'

/--
Appendix D, Lemma 11 reduced-model selected-policy form: the reduced optimal
item fairness is monotone on a same-selected-pivot interval.
-/
theorem paper_lemma11_reducedOptimalItemFairness_mono_of_same_selected_pivot
    {n : ℕ} [NeZero n]
    {alpha alpha' : ℝ} {v : Item n → ℝ}
    {ρ ρ' : TypePolicy 2 n} {ell ell' : ℝ}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hpivot :
      TypePolicy.lastActiveTypeZero ρ =
        TypePolicy.lastActiveTypeZero ρ')
    (hcenter :
      (TypePolicy.lastActiveTypeZero ρ).val ≤
        (reverseItem (TypePolicy.lastActiveTypeZero ρ)).val)
    (hitem_eq :
      ∀ l : Item n,
        pairShare alpha v l * (ρ 0 l).toReal +
          (1 - pairShare alpha v l) * (ρ 1 l).toReal = ell)
    (hitem_eq' :
      ∀ l : Item n,
        pairShare alpha' v l * (ρ' 0 l).toReal +
          (1 - pairShare alpha' v l) * (ρ' 1 l).toReal = ell')
    (hopt : Problem6PolicyOptimal alpha v ρ ell)
    (hopt' : Problem6PolicyOptimal alpha' v ρ' ell')
    (hshared : TypePolicy.SharedItemsBound ρ)
    (hshared' : TypePolicy.SharedItemsBound ρ') :
    TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel alpha v) ≤
      TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel alpha' v) := by
  exact lemma11_reducedOptimalItemFairness_mono_of_same_selected_pivot
    hn halpha0 halpha1 halpha0' halpha1' halpha_le
    hpos hdec hpivot hcenter hitem_eq hitem_eq'
    hopt hopt' hshared hshared'

/--
Appendix D, Lemma 11 reduced-model selected-policy form for the paper's
equality-form optimal BFS package.
-/
theorem paper_lemma11_reducedOptimalItemFairness_mono_of_same_selected_equalizedBasicOptimal
    {n : ℕ} [NeZero n]
    {alpha alpha' : ℝ} {v : Item n → ℝ}
    {ρ ρ' : TypePolicy 2 n} {ell ell' : ℝ}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hpivot :
      TypePolicy.lastActiveTypeZero ρ =
        TypePolicy.lastActiveTypeZero ρ')
    (hcenter :
      (TypePolicy.lastActiveTypeZero ρ).val ≤
        (reverseItem (TypePolicy.lastActiveTypeZero ρ)).val)
    (h : Problem6EqualizedBasicOptimal alpha v ρ ell)
    (h' : Problem6EqualizedBasicOptimal alpha' v ρ' ell') :
    TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel alpha v) ≤
      TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel alpha' v) := by
  exact lemma11_reducedOptimalItemFairness_mono_of_same_selected_equalizedBasicOptimal
    hn halpha0 halpha1 halpha0' halpha1' halpha_le
    hpos hdec hpivot hcenter h h'

/--
Appendix D, Lemma 11 canonical first-pivot reduced-model form: the reduced
optimal item-fairness value is monotone on each first-half `A(t)` interval for
the canonical Lemma 5 first crossing pivot.
-/
theorem paper_lemma11_reducedOptimalItemFairness_mono_of_same_firstClosedPivot
    {n : ℕ} [NeZero n]
    {alpha alpha' : ℝ} {v : Item n → ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hpivot :
      problem6FirstClosedPivot alpha v halpha0 halpha1 hpos =
        problem6FirstClosedPivot alpha' v halpha0' halpha1' hpos)
    (hcenter :
      (problem6FirstClosedPivot alpha v halpha0 halpha1 hpos).val ≤
        (reverseItem
          (problem6FirstClosedPivot alpha v halpha0 halpha1 hpos)).val) :
    TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel alpha v) ≤
      TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel alpha' v) := by
  exact lemma11_reducedOptimalItemFairness_mono_of_same_firstClosedPivot
    halpha0 halpha1 halpha0' halpha1' halpha_le
    hpos hdec hpivot hcenter

/--
Appendix D, Lemma 8 finite-stitch core: a finite chain of adjacent
same-selected-pivot first-half intervals gives monotonicity of the reduced
optimal item-fairness value.
-/
theorem paper_lemma8_reducedOptimalItemFairness_mono_of_same_selected_equalizedBasicOptimal_chain
    {n : ℕ} [NeZero n]
    {v : Item n → ℝ} (r : ℕ)
    (alphaSeq : ℕ → ℝ)
    (ρSeq : ℕ → TypePolicy 2 n)
    (ellSeq : ℕ → ℝ)
    (hn : 2 < n)
    (halpha0 : ∀ i, i ≤ r → 0 < alphaSeq i)
    (halpha1 : ∀ i, i ≤ r → alphaSeq i < 1)
    (hstep : ∀ i, i < r → alphaSeq i ≤ alphaSeq (i + 1))
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hpivot :
      ∀ i, i < r →
        TypePolicy.lastActiveTypeZero (ρSeq i) =
          TypePolicy.lastActiveTypeZero (ρSeq (i + 1)))
    (hcenter :
      ∀ i, i < r →
        (TypePolicy.lastActiveTypeZero (ρSeq i)).val ≤
          (reverseItem (TypePolicy.lastActiveTypeZero (ρSeq i))).val)
    (hopt :
      ∀ i, i ≤ r →
        Problem6EqualizedBasicOptimal (alphaSeq i) v (ρSeq i) (ellSeq i)) :
    TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel (alphaSeq 0) v) ≤
      TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel (alphaSeq r) v) := by
  exact lemma8_reducedOptimalItemFairness_mono_of_same_selected_equalizedBasicOptimal_chain
    r alphaSeq ρSeq ellSeq hn halpha0 halpha1 hstep hpos hdec hpivot hcenter hopt

/--
Appendix D, Lemma 8 finite-stitch core with explicit boundary repeats: adjacent
steps may either stay in one same-selected-pivot interval or repeat the same
`α` at a partition boundary.
-/
theorem paper_lemma8_reducedOptimalItemFairness_mono_of_same_selected_or_equal_alpha_chain
    {n : ℕ} [NeZero n]
    {v : Item n → ℝ} (r : ℕ)
    (alphaSeq : ℕ → ℝ)
    (ρSeq : ℕ → TypePolicy 2 n)
    (ellSeq : ℕ → ℝ)
    (hn : 2 < n)
    (halpha0 : ∀ i, i ≤ r → 0 < alphaSeq i)
    (halpha1 : ∀ i, i ≤ r → alphaSeq i < 1)
    (hstep : ∀ i, i < r → alphaSeq i ≤ alphaSeq (i + 1))
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hpivot_or_eq :
      ∀ i, i < r →
        TypePolicy.lastActiveTypeZero (ρSeq i) =
          TypePolicy.lastActiveTypeZero (ρSeq (i + 1)) ∨
        alphaSeq i = alphaSeq (i + 1))
    (hcenter :
      ∀ i, i < r →
        (TypePolicy.lastActiveTypeZero (ρSeq i)).val ≤
          (reverseItem (TypePolicy.lastActiveTypeZero (ρSeq i))).val)
    (hopt :
      ∀ i, i ≤ r →
        Problem6EqualizedBasicOptimal (alphaSeq i) v (ρSeq i) (ellSeq i)) :
    TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel (alphaSeq 0) v) ≤
      TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel (alphaSeq r) v) := by
  exact lemma8_reducedOptimalItemFairness_mono_of_same_selected_or_equal_alpha_chain
    r alphaSeq ρSeq ellSeq hn halpha0 halpha1 hstep hpos hdec hpivot_or_eq
    hcenter hopt

/--
Appendix D, Lemma 8 finite-stitch core for closed-form certificates: adjacent
steps may either stay in one certified fixed-pivot interval or repeat the same
`α` at a partition boundary.
-/
theorem paper_lemma8_reducedOptimalItemFairness_mono_of_closedPivot_cert_or_equal_alpha_chain
    {n : ℕ} [NeZero n]
    {v : Item n → ℝ} (r : ℕ)
    (alphaSeq : ℕ → ℝ)
    (pivotSeq : ℕ → Item n)
    (halpha0 : ∀ i, i ≤ r → 0 < alphaSeq i)
    (halpha1 : ∀ i, i ≤ r → alphaSeq i < 1)
    (hstep : ∀ i, i < r → alphaSeq i ≤ alphaSeq (i + 1))
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hcert :
      ∀ i, ∀ hi : i ≤ r,
        Problem6ClosedOptimalityCertificate (alphaSeq i) v (pivotSeq i))
    (hpivot_or_eq :
      ∀ i, i < r →
        pivotSeq i = pivotSeq (i + 1) ∨
        alphaSeq i = alphaSeq (i + 1))
    (hcenter :
      ∀ i, i < r →
        (pivotSeq i).val ≤ (reverseItem (pivotSeq i)).val) :
    TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel (alphaSeq 0) v) ≤
      TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel (alphaSeq r) v) := by
  exact lemma8_reducedOptimalItemFairness_mono_of_closedPivot_cert_or_equal_alpha_chain
    r alphaSeq pivotSeq halpha0 halpha1 hstep hpos hdec hcert hpivot_or_eq
    hcenter

/--
Appendix D, Lemma 8 finite-stitch core for closed-form denominator bounds.
-/
theorem paper_lemma8_reducedOptimalItemFairness_mono_of_closedPivotBounds_or_equal_alpha_chain
    {n : ℕ} [NeZero n]
    {v : Item n → ℝ} (r : ℕ)
    (alphaSeq : ℕ → ℝ)
    (pivotSeq : ℕ → Item n)
    (halpha0 : ∀ i, i ≤ r → 0 < alphaSeq i)
    (halpha1 : ∀ i, i ≤ r → alphaSeq i < 1)
    (hstep : ∀ i, i < r → alphaSeq i ≤ alphaSeq (i + 1))
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hbounds :
      ∀ i, ∀ hi : i ≤ r,
        Problem6ClosedPivotDenominatorBounds (alphaSeq i) v (pivotSeq i))
    (hpivot_or_eq :
      ∀ i, i < r →
        pivotSeq i = pivotSeq (i + 1) ∨
        alphaSeq i = alphaSeq (i + 1))
    (hcenter :
      ∀ i, i < r →
        (pivotSeq i).val ≤ (reverseItem (pivotSeq i)).val) :
    TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel (alphaSeq 0) v) ≤
      TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel (alphaSeq r) v) := by
  exact lemma8_reducedOptimalItemFairness_mono_of_closedPivotBounds_or_equal_alpha_chain
    r alphaSeq pivotSeq halpha0 halpha1 hstep hpos hdec hbounds
    hpivot_or_eq hcenter

/--
Appendix D, Lemma 8 canonical finite-stitch core with explicit boundary
repeats: adjacent steps may either stay in one `A(t)` interval for the
canonical Lemma 5 first crossing pivot or repeat the same `α` at a partition
boundary.
-/
theorem paper_lemma8_reducedOptimalItemFairness_mono_of_same_firstClosedPivot_or_equal_alpha_chain
    {n : ℕ} [NeZero n]
    {v : Item n → ℝ} (r : ℕ)
    (alphaSeq : ℕ → ℝ)
    (pivotSeq : ℕ → Item n)
    (halpha0 : ∀ i, i ≤ r → 0 < alphaSeq i)
    (halpha1 : ∀ i, i ≤ r → alphaSeq i < 1)
    (hstep : ∀ i, i < r → alphaSeq i ≤ alphaSeq (i + 1))
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hpivot_def :
      ∀ i, ∀ hi : i ≤ r,
        pivotSeq i =
          problem6FirstClosedPivot (alphaSeq i) v
            (halpha0 i hi) (halpha1 i hi) hpos)
    (hpivot_or_eq :
      ∀ i, i < r →
        pivotSeq i = pivotSeq (i + 1) ∨
        alphaSeq i = alphaSeq (i + 1))
    (hcenter :
      ∀ i, i < r →
        (pivotSeq i).val ≤ (reverseItem (pivotSeq i)).val) :
    TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel (alphaSeq 0) v) ≤
      TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel (alphaSeq r) v) := by
  exact lemma8_reducedOptimalItemFairness_mono_of_same_firstClosedPivot_or_equal_alpha_chain
    r alphaSeq pivotSeq halpha0 halpha1 hstep hpos hdec hpivot_def
    hpivot_or_eq hcenter

/--
Appendix D, Lemma 8 canonical finite-stitch core, odd-center first-half case:
Lemma 10 and canonical first-pivot monotonicity supply the pivot-before-mirror
condition for the canonical `A(t)` chain.
-/
theorem paper_lemma8_reducedOptimalItemFairness_mono_firstHalf_center_firstClosedPivot_chain
    {n : ℕ} [NeZero n]
    {v : Item n → ℝ} {c : Item n}
    (r : ℕ)
    (alphaSeq : ℕ → ℝ)
    (pivotSeq : ℕ → Item n)
    (halpha0 : ∀ i, i ≤ r → 0 < alphaSeq i)
    (halpha1 : ∀ i, i ≤ r → alphaSeq i < 1)
    (halpha_half : ∀ i, i ≤ r → alphaSeq i ≤ 1 / 2)
    (hstep : ∀ i, i < r → alphaSeq i ≤ alphaSeq (i + 1))
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter_c : c.val = (reverseItem c).val)
    (hpivot_def :
      ∀ i, ∀ hi : i ≤ r,
        pivotSeq i =
          problem6FirstClosedPivot (alphaSeq i) v
            (halpha0 i hi) (halpha1 i hi) hpos)
    (hpivot_or_eq :
      ∀ i, i < r →
        pivotSeq i = pivotSeq (i + 1) ∨
        alphaSeq i = alphaSeq (i + 1)) :
    TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel (alphaSeq 0) v) ≤
      TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel (alphaSeq r) v) := by
  exact lemma8_reducedOptimalItemFairness_mono_firstHalf_center_firstClosedPivot_chain
    r alphaSeq pivotSeq halpha0 halpha1 halpha_half hstep hpos hdec
    hcenter_c hpivot_def hpivot_or_eq

/--
Appendix D, Lemma 8 canonical finite-stitch core, even-center first-half case.
-/
theorem paper_lemma8_reducedOptimalItemFairness_mono_firstHalf_succ_center_firstClosedPivot_chain
    {n : ℕ} [NeZero n]
    {v : Item n → ℝ} {c : Item n}
    (r : ℕ)
    (alphaSeq : ℕ → ℝ)
    (pivotSeq : ℕ → Item n)
    (halpha0 : ∀ i, i ≤ r → 0 < alphaSeq i)
    (halpha1 : ∀ i, i ≤ r → alphaSeq i < 1)
    (halpha_half : ∀ i, i ≤ r → alphaSeq i ≤ 1 / 2)
    (hstep : ∀ i, i < r → alphaSeq i ≤ alphaSeq (i + 1))
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hsucc : c.val + 1 = (reverseItem c).val)
    (hpivot_def :
      ∀ i, ∀ hi : i ≤ r,
        pivotSeq i =
          problem6FirstClosedPivot (alphaSeq i) v
            (halpha0 i hi) (halpha1 i hi) hpos)
    (hpivot_or_eq :
      ∀ i, i < r →
        pivotSeq i = pivotSeq (i + 1) ∨
        alphaSeq i = alphaSeq (i + 1)) :
    TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel (alphaSeq 0) v) ≤
      TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel (alphaSeq r) v) := by
  exact lemma8_reducedOptimalItemFairness_mono_firstHalf_succ_center_firstClosedPivot_chain
    r alphaSeq pivotSeq halpha0 halpha1 halpha_half hstep hpos hdec
    hsucc hpivot_def hpivot_or_eq

/--
Appendix D, Lemma 8 finite-stitch core, odd-center case: along a first-half
finite chain, Lemma 10 supplies the pivot-before-mirror side condition.
-/
theorem paper_lemma8_reducedOptimalItemFairness_mono_firstHalf_center_chain
    {n : ℕ} [NeZero n]
    {v : Item n → ℝ} {c : Item n}
    (r : ℕ)
    (alphaSeq : ℕ → ℝ)
    (ρSeq : ℕ → TypePolicy 2 n)
    (ellSeq : ℕ → ℝ)
    {ρhalf : TypePolicy 2 n} {ellHalf : ℝ}
    (hn : 2 < n)
    (halpha0 : ∀ i, i ≤ r → 0 < alphaSeq i)
    (halpha1 : ∀ i, i ≤ r → alphaSeq i < 1)
    (halpha_half : ∀ i, i ≤ r → alphaSeq i ≤ 1 / 2)
    (hstep : ∀ i, i < r → alphaSeq i ≤ alphaSeq (i + 1))
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter_c : c.val = (reverseItem c).val)
    (hpivot_or_eq :
      ∀ i, i < r →
        TypePolicy.lastActiveTypeZero (ρSeq i) =
          TypePolicy.lastActiveTypeZero (ρSeq (i + 1)) ∨
        alphaSeq i = alphaSeq (i + 1))
    (hopt :
      ∀ i, i ≤ r →
        Problem6EqualizedBasicOptimal (alphaSeq i) v (ρSeq i) (ellSeq i))
    (hhalf :
      Problem6EqualizedBasicOptimal (1 / 2) v ρhalf ellHalf) :
    TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel (alphaSeq 0) v) ≤
      TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel (alphaSeq r) v) := by
  exact lemma8_reducedOptimalItemFairness_mono_firstHalf_center_chain
    r alphaSeq ρSeq ellSeq hn halpha0 halpha1 halpha_half hstep hpos hdec
    hcenter_c hpivot_or_eq hopt hhalf

/--
Appendix D, Lemma 8 finite-stitch core, even-center case: along a first-half
finite chain, Lemma 10 supplies the pivot-before-mirror side condition.
-/
theorem paper_lemma8_reducedOptimalItemFairness_mono_firstHalf_succ_center_chain
    {n : ℕ} [NeZero n]
    {v : Item n → ℝ} {c : Item n}
    (r : ℕ)
    (alphaSeq : ℕ → ℝ)
    (ρSeq : ℕ → TypePolicy 2 n)
    (ellSeq : ℕ → ℝ)
    {ρhalf : TypePolicy 2 n} {ellHalf : ℝ}
    (hn : 2 < n)
    (halpha0 : ∀ i, i ≤ r → 0 < alphaSeq i)
    (halpha1 : ∀ i, i ≤ r → alphaSeq i < 1)
    (halpha_half : ∀ i, i ≤ r → alphaSeq i ≤ 1 / 2)
    (hstep : ∀ i, i < r → alphaSeq i ≤ alphaSeq (i + 1))
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hsucc : c.val + 1 = (reverseItem c).val)
    (hpivot_or_eq :
      ∀ i, i < r →
        TypePolicy.lastActiveTypeZero (ρSeq i) =
          TypePolicy.lastActiveTypeZero (ρSeq (i + 1)) ∨
        alphaSeq i = alphaSeq (i + 1))
    (hopt :
      ∀ i, i ≤ r →
        Problem6EqualizedBasicOptimal (alphaSeq i) v (ρSeq i) (ellSeq i))
    (hhalf :
      Problem6EqualizedBasicOptimal (1 / 2) v ρhalf ellHalf) :
    TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel (alphaSeq 0) v) ≤
      TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel (alphaSeq r) v) := by
  exact lemma8_reducedOptimalItemFairness_mono_firstHalf_succ_center_chain
    r alphaSeq ρSeq ellSeq hn halpha0 halpha1 halpha_half hstep hpos hdec
    hsucc hpivot_or_eq hopt hhalf

/--
Appendix D, Lemma 8 finite-stitch core, odd-center case, with the midpoint
optimum supplied by the Lemma 5 closed form.
-/
theorem paper_lemma8_reducedOptimalItemFairness_mono_firstHalf_center_chain_of_closed_half
    {n : ℕ} [NeZero n]
    {v : Item n → ℝ} {c : Item n}
    (r : ℕ)
    (alphaSeq : ℕ → ℝ)
    (ρSeq : ℕ → TypePolicy 2 n)
    (ellSeq : ℕ → ℝ)
    (hn : 2 < n)
    (halpha0 : ∀ i, i ≤ r → 0 < alphaSeq i)
    (halpha1 : ∀ i, i ≤ r → alphaSeq i < 1)
    (halpha_half : ∀ i, i ≤ r → alphaSeq i ≤ 1 / 2)
    (hstep : ∀ i, i < r → alphaSeq i ≤ alphaSeq (i + 1))
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter_c : c.val = (reverseItem c).val)
    (hpivot_or_eq :
      ∀ i, i < r →
        TypePolicy.lastActiveTypeZero (ρSeq i) =
          TypePolicy.lastActiveTypeZero (ρSeq (i + 1)) ∨
        alphaSeq i = alphaSeq (i + 1))
    (hopt :
      ∀ i, i ≤ r →
        Problem6EqualizedBasicOptimal (alphaSeq i) v (ρSeq i) (ellSeq i)) :
    TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel (alphaSeq 0) v) ≤
      TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel (alphaSeq r) v) := by
  exact lemma8_reducedOptimalItemFairness_mono_firstHalf_center_chain_of_closed_half
    r alphaSeq ρSeq ellSeq hn halpha0 halpha1 halpha_half hstep hpos hdec
    hcenter_c hpivot_or_eq hopt

/--
Appendix D, Lemma 8 finite-stitch core, even-center case, with the midpoint
optimum supplied by the Lemma 5 closed form.
-/
theorem paper_lemma8_reducedOptimalItemFairness_mono_firstHalf_succ_center_chain_of_closed_half
    {n : ℕ} [NeZero n]
    {v : Item n → ℝ} {c : Item n}
    (r : ℕ)
    (alphaSeq : ℕ → ℝ)
    (ρSeq : ℕ → TypePolicy 2 n)
    (ellSeq : ℕ → ℝ)
    (hn : 2 < n)
    (halpha0 : ∀ i, i ≤ r → 0 < alphaSeq i)
    (halpha1 : ∀ i, i ≤ r → alphaSeq i < 1)
    (halpha_half : ∀ i, i ≤ r → alphaSeq i ≤ 1 / 2)
    (hstep : ∀ i, i < r → alphaSeq i ≤ alphaSeq (i + 1))
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hsucc : c.val + 1 = (reverseItem c).val)
    (hpivot_or_eq :
      ∀ i, i < r →
        TypePolicy.lastActiveTypeZero (ρSeq i) =
          TypePolicy.lastActiveTypeZero (ρSeq (i + 1)) ∨
        alphaSeq i = alphaSeq (i + 1))
    (hopt :
      ∀ i, i ≤ r →
        Problem6EqualizedBasicOptimal (alphaSeq i) v (ρSeq i) (ellSeq i)) :
    TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel (alphaSeq 0) v) ≤
      TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel (alphaSeq r) v) := by
  exact lemma8_reducedOptimalItemFairness_mono_firstHalf_succ_center_chain_of_closed_half
    r alphaSeq ρSeq ellSeq hn halpha0 halpha1 halpha_half hstep hpos hdec
    hsucc hpivot_or_eq hopt

/--
Appendix D, Lemma 5: before the pivot, `x_j = I^*_min / q_j`.
-/
theorem paper_lemma5_problem6_x_before_pivot
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {t j : Item n}
    {x y : Item n → ℝ} {ell : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (h : Problem6SparseEqualized alpha v t x y ell)
    (hj : j.val < t.val) :
    x j = problem6ClosedValue alpha v t / pairShare alpha v j := by
  exact problem6SparseEqualized_x_before_eq_closed
    halpha0 halpha1 hpos h hj

/-- Appendix D, Lemma 5: after the pivot, `x_j = 0`. -/
theorem paper_lemma5_problem6_x_after_pivot
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {t j : Item n}
    {x y : Item n → ℝ} {ell : ℝ}
    (h : Problem6SparseEqualized alpha v t x y ell)
    (hj : t.val < j.val) :
    x j = 0 := by
  exact h.x_after_pivot_zero hj

/-- Appendix D, Lemma 5: pivot formula for `x_t`. -/
theorem paper_lemma5_problem6_x_at_pivot
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    {x y : Item n → ℝ} {ell : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (h : Problem6SparseEqualized alpha v t x y ell) :
    x t = 1 - problem6ClosedValue alpha v t *
      problem6LeftSum alpha v t := by
  exact problem6SparseEqualized_x_pivot_eq_closed
    halpha0 halpha1 hpos h

/-- Appendix D, Lemma 5: before the pivot, `y_j = 0`. -/
theorem paper_lemma5_problem6_y_before_pivot
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {t j : Item n}
    {x y : Item n → ℝ} {ell : ℝ}
    (h : Problem6SparseEqualized alpha v t x y ell)
    (hj : j.val < t.val) :
    y j = 0 := by
  exact h.y_before_pivot_zero hj

/-- Appendix D, Lemma 5: pivot formula for `y_t`. -/
theorem paper_lemma5_problem6_y_at_pivot
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    {x y : Item n → ℝ} {ell : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (h : Problem6SparseEqualized alpha v t x y ell) :
    y t = 1 - problem6ClosedValue alpha v t *
      problem6RightSum alpha v t := by
  exact problem6SparseEqualized_y_pivot_eq_closed
    halpha0 halpha1 hpos h

/--
Appendix D, Lemma 5: after the pivot, `y_j = I^*_min / (1 - q_j)`.
-/
theorem paper_lemma5_problem6_y_after_pivot
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {t j : Item n}
    {x y : Item n → ℝ} {ell : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (h : Problem6SparseEqualized alpha v t x y ell)
    (hj : t.val < j.val) :
    y j = problem6ClosedValue alpha v t /
      (1 - pairShare alpha v j) := by
  exact problem6SparseEqualized_y_after_eq_closed
    halpha0 halpha1 hpos h hj

/--
Appendix D, Lemma 4 uniqueness, same-pivot case: two sparse equalized
solutions with the same pivot have identical value and coordinates.
-/
theorem paper_lemma4_sparseEqualized_eq_of_same_pivot
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    {x y x' y' : Item n → ℝ} {ell ell' : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (h : Problem6SparseEqualized alpha v t x y ell)
    (h' : Problem6SparseEqualized alpha v t x' y' ell') :
    ell = ell' ∧ x = x' ∧ y = y' := by
  exact problem6SparseEqualized_eq_of_same_pivot
    halpha0 halpha1 hpos h h'

/--
Appendix D, Lemma 4 uniqueness for active sparse equalized solutions: equal
optimal values force the pivots, values, and coordinates to agree.
-/
theorem paper_lemma4_sparseEqualizedActive_eq_of_equal_value
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {t t' : Item n}
    {x y x' y' : Item n → ℝ} {ell ell' : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (h : Problem6SparseEqualizedActive alpha v t x y ell)
    (h' : Problem6SparseEqualizedActive alpha v t' x' y' ell')
    (hell : ell = ell') :
    t = t' ∧ ell = ell' ∧ x = x' ∧ y = y' := by
  exact problem6SparseEqualizedActive_eq_of_equal_value
    halpha0 halpha1 hpos h h' hell

/--
Appendix D, Lemma 4 uniqueness for equalized optimal Problem 6 policies,
conditional on the paper's shared-item sparsity bound and `2 < n`.
-/
theorem paper_lemma4_policyOptimal_equalized_unique_sparseActive_of_two_lt
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ}
    {ρ ρ' : TypePolicy 2 n} {ell ell' : ℝ}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hitem_eq :
      ∀ l : Item n,
        pairShare alpha v l * (ρ 0 l).toReal +
          (1 - pairShare alpha v l) * (ρ 1 l).toReal = ell)
    (hitem_eq' :
      ∀ l : Item n,
        pairShare alpha v l * (ρ' 0 l).toReal +
          (1 - pairShare alpha v l) * (ρ' 1 l).toReal = ell')
    (hopt : Problem6PolicyOptimal alpha v ρ ell)
    (hopt' : Problem6PolicyOptimal alpha v ρ' ell')
    (hshared : TypePolicy.SharedItemsBound ρ)
    (hshared' : TypePolicy.SharedItemsBound ρ') :
    ∃ t : Item n,
      Problem6SparseEqualizedActive alpha v t
        (fun l : Item n => (ρ 0 l).toReal)
        (fun l : Item n => (ρ 1 l).toReal) ell ∧
      Problem6SparseEqualizedActive alpha v t
        (fun l : Item n => (ρ' 0 l).toReal)
        (fun l : Item n => (ρ' 1 l).toReal) ell' ∧
      ell = ell' ∧
      (fun l : Item n => (ρ 0 l).toReal) =
        (fun l : Item n => (ρ' 0 l).toReal) ∧
      (fun l : Item n => (ρ 1 l).toReal) =
        (fun l : Item n => (ρ' 1 l).toReal) := by
  exact problem6PolicyOptimal_equalized_unique_sparseActive_of_two_lt
    hn halpha0 halpha1 hpos hdec hitem_eq hitem_eq'
    hopt hopt' hshared hshared'

/--
Appendix D, Lemma 4 uniqueness for the paper's equality-form optimal BFS
package.
-/
theorem paper_lemma4_equalizedBasicOptimal_unique_sparseActive_of_two_lt
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ}
    {ρ ρ' : TypePolicy 2 n} {ell ell' : ℝ}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (h : Problem6EqualizedBasicOptimal alpha v ρ ell)
    (h' : Problem6EqualizedBasicOptimal alpha v ρ' ell') :
    ∃ t : Item n,
      Problem6SparseEqualizedActive alpha v t
        (fun l : Item n => (ρ 0 l).toReal)
        (fun l : Item n => (ρ 1 l).toReal) ell ∧
      Problem6SparseEqualizedActive alpha v t
        (fun l : Item n => (ρ' 0 l).toReal)
        (fun l : Item n => (ρ' 1 l).toReal) ell' ∧
      ell = ell' ∧
      (fun l : Item n => (ρ 0 l).toReal) =
        (fun l : Item n => (ρ' 0 l).toReal) ∧
      (fun l : Item n => (ρ 1 l).toReal) =
        (fun l : Item n => (ρ' 1 l).toReal) := by
  exact problem6EqualizedBasicOptimal_unique_sparseActive_of_two_lt
    hn halpha0 halpha1 hpos hdec h h'

/--
Appendix D, Lemma 7 sparse-solution form: as `α` increases, the active pivot
`t = max {j : x_j > 0}` cannot move left.
-/
theorem paper_lemma7_sparseActive_pivot_mono_of_alpha_lt
    {n : ℕ} {alpha alpha' : ℝ} {v : Item n → ℝ}
    {t t' : Item n} {x y x' y' : Item n → ℝ} {ell ell' : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_lt : alpha < alpha')
    (hpos : ∀ j : Item n, 0 < v j)
    (h : Problem6SparseEqualizedActive alpha v t x y ell)
    (h' : Problem6SparseEqualizedActive alpha' v t' x' y' ell') :
    t.val ≤ t'.val := by
  exact lemma7_sparseActive_pivot_mono_of_alpha_lt
    halpha0 halpha1 halpha0' halpha1' halpha_lt hpos h h'

/--
Appendix D, Lemma 7 for equalized optimal Problem 6 policies, conditional on
the Lemma 4 active-sparse bridge hypotheses.
-/
theorem paper_lemma7_policyOptimal_lastActive_mono_of_alpha_lt
    {n : ℕ} [NeZero n]
    {alpha alpha' : ℝ} {v : Item n → ℝ}
    {ρ ρ' : TypePolicy 2 n} {ell ell' : ℝ}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_lt : alpha < alpha')
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hitem_eq :
      ∀ l : Item n,
        pairShare alpha v l * (ρ 0 l).toReal +
          (1 - pairShare alpha v l) * (ρ 1 l).toReal = ell)
    (hitem_eq' :
      ∀ l : Item n,
        pairShare alpha' v l * (ρ' 0 l).toReal +
          (1 - pairShare alpha' v l) * (ρ' 1 l).toReal = ell')
    (hopt : Problem6PolicyOptimal alpha v ρ ell)
    (hopt' : Problem6PolicyOptimal alpha' v ρ' ell')
    (hshared : TypePolicy.SharedItemsBound ρ)
    (hshared' : TypePolicy.SharedItemsBound ρ') :
    (TypePolicy.lastActiveTypeZero ρ).val ≤
      (TypePolicy.lastActiveTypeZero ρ').val := by
  exact lemma7_policyOptimal_lastActive_mono_of_alpha_lt
    hn halpha0 halpha1 halpha0' halpha1' halpha_lt
    hpos hdec hitem_eq hitem_eq' hopt hopt' hshared hshared'

/--
Appendix D, Lemma 7 for the paper's equality-form optimal BFS package.
-/
theorem paper_lemma7_equalizedBasicOptimal_lastActive_mono_of_alpha_lt
    {n : ℕ} [NeZero n]
    {alpha alpha' : ℝ} {v : Item n → ℝ}
    {ρ ρ' : TypePolicy 2 n} {ell ell' : ℝ}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_lt : alpha < alpha')
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (h : Problem6EqualizedBasicOptimal alpha v ρ ell)
    (h' : Problem6EqualizedBasicOptimal alpha' v ρ' ell') :
    (TypePolicy.lastActiveTypeZero ρ).val ≤
      (TypePolicy.lastActiveTypeZero ρ').val := by
  exact lemma7_equalizedBasicOptimal_lastActive_mono_of_alpha_lt
    hn halpha0 halpha1 halpha0' halpha1' halpha_lt
    hpos hdec h h'

/--
Same-`α` selected-pivot uniqueness for equality-form optimal BFS packages.
-/
theorem paper_problem6EqualizedBasicOptimal_lastActive_eq_of_same_alpha
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ}
    {ρ ρ' : TypePolicy 2 n} {ell ell' : ℝ}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (h : Problem6EqualizedBasicOptimal alpha v ρ ell)
    (h' : Problem6EqualizedBasicOptimal alpha v ρ' ell') :
    TypePolicy.lastActiveTypeZero ρ =
      TypePolicy.lastActiveTypeZero ρ' := by
  exact problem6EqualizedBasicOptimal_lastActive_eq_of_same_alpha
    hn halpha0 halpha1 hpos hdec h h'

/--
Appendix D, Lemma 7 in non-strict form for equality-form optimal BFS packages.
-/
theorem paper_lemma7_equalizedBasicOptimal_lastActive_mono_of_alpha_le
    {n : ℕ} [NeZero n]
    {alpha alpha' : ℝ} {v : Item n → ℝ}
    {ρ ρ' : TypePolicy 2 n} {ell ell' : ℝ}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (h : Problem6EqualizedBasicOptimal alpha v ρ ell)
    (h' : Problem6EqualizedBasicOptimal alpha' v ρ' ell') :
    (TypePolicy.lastActiveTypeZero ρ).val ≤
      (TypePolicy.lastActiveTypeZero ρ').val := by
  exact lemma7_equalizedBasicOptimal_lastActive_mono_of_alpha_le
    hn halpha0 halpha1 halpha0' halpha1' halpha_le hpos hdec h h'

/--
Appendix D, Lemma 8 interval step: the selected-pivot set `A(t)` is an
interval for equality-form optimal BFS selections.
-/
theorem paper_lemma8_selectedPivot_eq_of_between_equalizedBasicOptimal_endpoints
    {n : ℕ} [NeZero n]
    {alphaLeft alpha alphaRight : ℝ} {v : Item n → ℝ}
    {ρLeft ρ ρRight : TypePolicy 2 n} {ellLeft ell ellRight : ℝ}
    (hn : 2 < n)
    (halphaLeft0 : 0 < alphaLeft) (halphaLeft1 : alphaLeft < 1)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halphaRight0 : 0 < alphaRight) (halphaRight1 : alphaRight < 1)
    (hleft : alphaLeft ≤ alpha)
    (hright : alpha ≤ alphaRight)
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hpivot :
      TypePolicy.lastActiveTypeZero ρLeft =
        TypePolicy.lastActiveTypeZero ρRight)
    (hLeft :
      Problem6EqualizedBasicOptimal alphaLeft v ρLeft ellLeft)
    (h : Problem6EqualizedBasicOptimal alpha v ρ ell)
    (hRight :
      Problem6EqualizedBasicOptimal alphaRight v ρRight ellRight) :
    TypePolicy.lastActiveTypeZero ρ =
      TypePolicy.lastActiveTypeZero ρLeft := by
  exact lemma8_selectedPivot_eq_of_between_equalizedBasicOptimal_endpoints
    hn halphaLeft0 halphaLeft1 halpha0 halpha1 halphaRight0 halphaRight1
    hleft hright hpos hdec hpivot hLeft h hRight

/--
Appendix D, Lemma 8 interval step for the canonical first pivot: if the
canonical `A(t)` selector agrees at two endpoints, it agrees throughout the
intermediate interval.
-/
theorem paper_lemma8_firstClosedPivot_eq_of_between_endpoints
    {n : ℕ} [NeZero n]
    {alphaLeft alpha alphaRight : ℝ} {v : Item n → ℝ}
    (halphaLeft0 : 0 < alphaLeft) (halphaLeft1 : alphaLeft < 1)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halphaRight0 : 0 < alphaRight) (halphaRight1 : alphaRight < 1)
    (hleft : alphaLeft ≤ alpha)
    (hright : alpha ≤ alphaRight)
    (hpos : ∀ j : Item n, 0 < v j)
    (hpivot :
      problem6FirstClosedPivot alphaLeft v halphaLeft0 halphaLeft1 hpos =
        problem6FirstClosedPivot alphaRight v
          halphaRight0 halphaRight1 hpos) :
    problem6FirstClosedPivot alpha v halpha0 halpha1 hpos =
      problem6FirstClosedPivot alphaLeft v halphaLeft0 halphaLeft1 hpos := by
  exact lemma8_firstClosedPivot_eq_of_between_endpoints
    halphaLeft0 halphaLeft1 halpha0 halpha1 halphaRight0 halphaRight1
    hleft hright hpos hpivot

/--
Appendix D, Lemma 8 canonical `A(t)` definition: every interior parameter
belongs to the region of its canonical first pivot.
-/
theorem paper_lemma8_problem6FirstClosedPivotRegion_mem
    {n : ℕ} [NeZero n] {alpha : ℝ} {v : Item n → ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j) :
    alpha ∈
      problem6FirstClosedPivotRegion v hpos
        (problem6FirstClosedPivot alpha v halpha0 halpha1 hpos) := by
  exact problem6FirstClosedPivotRegion_mem halpha0 halpha1 hpos

/-- Appendix D, Lemma 8 canonical `A(t)` cover of `(0,1)`. -/
theorem paper_lemma8_problem6FirstClosedPivotRegion_cover
    {n : ℕ} [NeZero n] {alpha : ℝ} {v : Item n → ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j) :
    ∃ t : Item n, alpha ∈ problem6FirstClosedPivotRegion v hpos t := by
  exact problem6FirstClosedPivotRegion_cover halpha0 halpha1 hpos

/-- Appendix D, Lemma 8 canonical `A(t)` uniqueness. -/
theorem paper_lemma8_problem6FirstClosedPivotRegion_unique
    {n : ℕ} [NeZero n] {alpha : ℝ} {v : Item n → ℝ}
    {t u : Item n}
    (hpos : ∀ j : Item n, 0 < v j)
    (ht : alpha ∈ problem6FirstClosedPivotRegion v hpos t)
    (hu : alpha ∈ problem6FirstClosedPivotRegion v hpos u) :
    t = u := by
  exact problem6FirstClosedPivotRegion_unique hpos ht hu

/-- Appendix D, Lemma 8 canonical `A(t)` interval property. -/
theorem paper_lemma8_problem6FirstClosedPivotRegion_interval
    {n : ℕ} [NeZero n]
    {alphaLeft alpha alphaRight : ℝ} {v : Item n → ℝ} {t : Item n}
    (hpos : ∀ j : Item n, 0 < v j)
    (hLeft : alphaLeft ∈ problem6FirstClosedPivotRegion v hpos t)
    (hRight : alphaRight ∈ problem6FirstClosedPivotRegion v hpos t)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hleft : alphaLeft ≤ alpha)
    (hright : alpha ≤ alphaRight) :
    alpha ∈ problem6FirstClosedPivotRegion v hpos t := by
  exact problem6FirstClosedPivotRegion_interval
    hpos hLeft hRight halpha0 halpha1 hleft hright

/-- Appendix D, Lemma 8 canonical `A(t)` consecutive order property. -/
theorem paper_lemma8_problem6FirstClosedPivotRegion_order
    {n : ℕ} [NeZero n]
    {alpha beta : ℝ} {v : Item n → ℝ} {t u : Item n}
    (hpos : ∀ j : Item n, 0 < v j)
    (halpha : alpha ∈ problem6FirstClosedPivotRegion v hpos t)
    (hbeta : beta ∈ problem6FirstClosedPivotRegion v hpos u)
    (hle : alpha ≤ beta) :
    t.val ≤ u.val := by
  exact problem6FirstClosedPivotRegion_order hpos halpha hbeta hle

/-- Appendix D, Lemma 8 boundary-gap continuity on compact subintervals. -/
theorem paper_lemma8_problem6BoundaryGap_continuousOn_Icc
    {n : ℕ} {alphaLeft alphaRight : ℝ} {v : Item n → ℝ}
    {t : Item n}
    (halphaLeft0 : 0 < alphaLeft) (halphaRight1 : alphaRight < 1)
    (hpos : ∀ j : Item n, 0 < v j) :
    ContinuousOn (fun alpha => problem6BoundaryGap alpha v t)
      (Set.Icc alphaLeft alphaRight) := by
  exact problem6BoundaryGap_continuousOn_Icc
    halphaLeft0 halphaRight1 hpos

/--
Appendix D, Lemma 8 IVT boundary step: a lower-crossing sign change produces
a tight boundary point.
-/
theorem paper_lemma8_problem6BoundaryGap_exists_zero_of_lower_crossing_changes
    {n : ℕ} {alphaLeft alphaRight : ℝ} {v : Item n → ℝ}
    {t : Item n}
    (halphaLeft0 : 0 < alphaLeft) (halphaRight1 : alphaRight < 1)
    (hleft_le_right : alphaLeft ≤ alphaRight)
    (hpos : ∀ j : Item n, 0 < v j)
    (hcross_left :
      - (pairShare alphaLeft v t)⁻¹ ≤ problem6PivotGap alphaLeft v t)
    (hnot_cross_right :
      ¬ - (pairShare alphaRight v t)⁻¹ ≤
        problem6PivotGap alphaRight v t) :
    ∃ alphaBoundary : ℝ,
      alphaLeft ≤ alphaBoundary ∧ alphaBoundary ≤ alphaRight ∧
      0 < alphaBoundary ∧ alphaBoundary < 1 ∧
      problem6PivotGap alphaBoundary v t =
        - (pairShare alphaBoundary v t)⁻¹ := by
  exact problem6BoundaryGap_exists_zero_of_lower_crossing_changes
    halphaLeft0 halphaRight1 hleft_le_right hpos
    hcross_left hnot_cross_right

/-- Appendix D, Lemma 8: the boundary gap is strictly decreasing in `α`. -/
theorem paper_lemma8_problem6BoundaryGap_strictAnti_alpha
    {n : ℕ} {alpha alpha' : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_lt : alpha < alpha')
    (hpos : ∀ j : Item n, 0 < v j) :
    problem6BoundaryGap alpha' v t <
      problem6BoundaryGap alpha v t := by
  exact problem6BoundaryGap_strictAnti_alpha
    t halpha0 halpha1 halpha0' halpha1' halpha_lt hpos

/--
Appendix D, Lemma 8: at a tight boundary for `t`, the next pivot has positive
boundary gap.
-/
theorem paper_lemma8_problem6BoundaryGap_next_pos_of_boundary
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {t u : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hnext : u.val = t.val + 1)
    (hboundary :
      problem6PivotGap alpha v t = - (pairShare alpha v t)⁻¹) :
    0 < problem6BoundaryGap alpha v u := by
  exact problem6BoundaryGap_next_pos_of_boundary
    halpha0 halpha1 hpos hnext hboundary

/--
Appendix D, Lemma 8 adjacent canonical boundary existence: if the canonical
first pivot changes from `t` to `t+1`, the tight boundary equation for `t`
has a solution between the two parameters.
-/
theorem paper_lemma8_problem6FirstClosedPivot_adjacentBoundary_exists
    {n : ℕ} [NeZero n]
    {alphaLeft alphaRight : ℝ} {v : Item n → ℝ} {t u : Item n}
    (halphaLeft0 : 0 < alphaLeft) (halphaLeft1 : alphaLeft < 1)
    (halphaRight0 : 0 < alphaRight) (halphaRight1 : alphaRight < 1)
    (hleft_le_right : alphaLeft ≤ alphaRight)
    (hpos : ∀ j : Item n, 0 < v j)
    (hleft_pivot :
      problem6FirstClosedPivot alphaLeft v
        halphaLeft0 halphaLeft1 hpos = t)
    (hright_pivot :
      problem6FirstClosedPivot alphaRight v
        halphaRight0 halphaRight1 hpos = u)
    (hnext : u.val = t.val + 1) :
    ∃ alphaBoundary : ℝ,
      alphaLeft ≤ alphaBoundary ∧ alphaBoundary ≤ alphaRight ∧
      0 < alphaBoundary ∧ alphaBoundary < 1 ∧
      problem6PivotGap alphaBoundary v t =
        - (pairShare alphaBoundary v t)⁻¹ := by
  exact problem6FirstClosedPivot_adjacentBoundary_exists
    halphaLeft0 halphaLeft1 halphaRight0 halphaRight1
    hleft_le_right hpos hleft_pivot hright_pivot hnext

/--
Appendix D, Lemma 8: a tight boundary reached from a left interval still has
canonical first pivot `t`.
-/
theorem paper_lemma8_problem6FirstClosedPivot_eq_of_left_pivot_and_boundary
    {n : ℕ} [NeZero n]
    {alphaLeft alphaBoundary : ℝ} {v : Item n → ℝ} {t : Item n}
    (halphaLeft0 : 0 < alphaLeft) (halphaLeft1 : alphaLeft < 1)
    (halphaBoundary0 : 0 < alphaBoundary)
    (halphaBoundary1 : alphaBoundary < 1)
    (hleft_le_boundary : alphaLeft ≤ alphaBoundary)
    (hpos : ∀ j : Item n, 0 < v j)
    (hleft_pivot :
      problem6FirstClosedPivot alphaLeft v
        halphaLeft0 halphaLeft1 hpos = t)
    (hboundary :
      problem6PivotGap alphaBoundary v t =
        - (pairShare alphaBoundary v t)⁻¹) :
    problem6FirstClosedPivot alphaBoundary v
      halphaBoundary0 halphaBoundary1 hpos = t := by
  exact problem6FirstClosedPivot_eq_of_left_pivot_and_boundary
    halphaLeft0 halphaLeft1 halphaBoundary0 halphaBoundary1
    hleft_le_boundary hpos hleft_pivot hboundary

/--
Appendix D, Lemma 8 no-skip bridge: if the canonical first pivot jumps past
`t+1`, some intermediate parameter has first pivot exactly `t+1`.
-/
theorem paper_lemma8_problem6FirstClosedPivot_successor_exists_of_pivot_jump
    {n : ℕ} [NeZero n]
    {alphaLeft alphaRight : ℝ} {v : Item n → ℝ} {t u : Item n}
    (halphaLeft0 : 0 < alphaLeft) (halphaLeft1 : alphaLeft < 1)
    (halphaRight0 : 0 < alphaRight) (halphaRight1 : alphaRight < 1)
    (hleft_le_right : alphaLeft ≤ alphaRight)
    (hpos : ∀ j : Item n, 0 < v j)
    (hleft_pivot :
      problem6FirstClosedPivot alphaLeft v
        halphaLeft0 halphaLeft1 hpos = t)
    (hright_pivot :
      problem6FirstClosedPivot alphaRight v
        halphaRight0 halphaRight1 hpos = u)
    (hskip : t.val + 1 < u.val) :
    ∃ (alphaMid : ℝ) (halphaMid0 : 0 < alphaMid)
      (halphaMid1 : alphaMid < 1) (s : Item n),
      alphaLeft ≤ alphaMid ∧ alphaMid ≤ alphaRight ∧
      s.val = t.val + 1 ∧
      problem6FirstClosedPivot alphaMid v
        halphaMid0 halphaMid1 hpos = s := by
  exact problem6FirstClosedPivot_successor_exists_of_pivot_jump
    halphaLeft0 halphaLeft1 halphaRight0 halphaRight1
    hleft_le_right hpos hleft_pivot hright_pivot hskip

/--
Appendix D, Lemma 6, mirror-pair algebra for
`1/q_j - 1/(1-q_{n-j+1})`.
-/
theorem paper_lemma6_pairShare_mirror_inverse_gap_eq
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} (j : Item n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j) :
    (pairShare alpha v j)⁻¹ -
        (1 - pairShare alpha v (reverseItem j))⁻¹ =
      v (reverseItem j) / v j * (1 - 2 * alpha) /
        (alpha * (1 - alpha)) := by
  exact pairShare_inv_sub_inv_one_sub_reverse_eq
    j halpha0 halpha1 hpos

/--
Appendix D, Lemma 6, nonnegativity of the mirror-pair inverse gap for
`α ≤ 1/2`.
-/
theorem paper_lemma6_pairShare_mirror_inverse_gap_nonneg
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} (j : Item n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha_half : alpha ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j) :
    0 ≤ (pairShare alpha v j)⁻¹ -
        (1 - pairShare alpha v (reverseItem j))⁻¹ := by
  exact pairShare_inv_sub_inv_one_sub_reverse_nonneg_of_alpha_le_half
    j halpha0 halpha1 halpha_half hpos

/--
Appendix D, Lemma 6 coordinate dominance: before the pivot, closed-form
`x_j` dominates mirrored `y_{n-j+1}` under the paper's `α ≤ 1/2` condition.
-/
theorem paper_lemma6_closedX_sub_closedY_reverse_nonneg
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {t j : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha_half : alpha ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hj : j.val < t.val)
    (hrev : t.val < (reverseItem j).val) :
    0 ≤ problem6ClosedX alpha v t j -
      problem6ClosedY alpha v t (reverseItem j) := by
  exact problem6ClosedX_sub_closedY_reverse_nonneg_of_alpha_le_half
    halpha0 halpha1 halpha_half hpos hj hrev

/--
Appendix D, Lemma 6 summation setup: reindex the closed type-1 raw utility
by mirror items.
-/
theorem paper_lemma6_closedTypeOneRawUtility_eq_mirror_sum
    {n : ℕ} (alpha : ℝ) (v : Item n → ℝ) (t : Item n) :
    problem6ClosedTypeOneRawUtility alpha v t =
      ∑ j : Item n, v j * problem6ClosedY alpha v t (reverseItem j) := by
  exact problem6ClosedTypeOneRawUtility_eq_mirror_sum alpha v t

/-- Appendix D, Lemma 6 summation setup: mirrored `y` masses sum to one. -/
theorem paper_lemma6_closedY_reverse_sum_eq_one
    {n : ℕ} (alpha : ℝ) (v : Item n → ℝ) (t : Item n) :
    (∑ j : Item n, problem6ClosedY alpha v t (reverseItem j)) = 1 := by
  exact problem6ClosedY_reverse_sum_eq_one alpha v t

/--
Appendix D, Lemma 6 summation identity: the closed-form raw utility gap is a
weighted sum of mirror-coordinate gaps.
-/
theorem paper_lemma6_closedRawUtility_sub_eq_mirror_gap_sum
    {n : ℕ} (alpha : ℝ) (v : Item n → ℝ) (t : Item n) :
    problem6ClosedTypeZeroRawUtility alpha v t -
        problem6ClosedTypeOneRawUtility alpha v t =
      ∑ j : Item n,
        v j * (problem6ClosedX alpha v t j -
          problem6ClosedY alpha v t (reverseItem j)) := by
  exact problem6ClosedRawUtility_sub_eq_mirror_gap_sum alpha v t

/--
Appendix D, Lemma 6 finite-sum comparison: left-side mirror gaps imply
type-0 raw utility dominates type-1 raw utility.
-/
theorem paper_lemma6_closedTypeOneRawUtility_le_typeZeroRawUtility_of_left_gaps
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (hdec : StrictlyDecreasingByIndex v)
    (hleft :
      ∀ j : Item n, j.val ≤ t.val →
        0 ≤ problem6ClosedX alpha v t j -
          problem6ClosedY alpha v t (reverseItem j))
    (hy_nonneg :
      ∀ j : Item n, 0 ≤ problem6ClosedY alpha v t (reverseItem j)) :
    problem6ClosedTypeOneRawUtility alpha v t ≤
      problem6ClosedTypeZeroRawUtility alpha v t := by
  exact problem6ClosedTypeOneRawUtility_le_typeZeroRawUtility_of_left_gaps
    hdec hleft hy_nonneg

/--
Appendix D, Lemma 6 finite-sum comparison in the paper's strict pre-pivot
form: the pivot gap cancels in the constant-weight decomposition.
-/
theorem paper_lemma6_closedTypeOneRawUtility_le_typeZeroRawUtility_of_strict_left_gaps
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (hdec : StrictlyDecreasingByIndex v)
    (hleft :
      ∀ j : Item n, j.val < t.val →
        0 ≤ problem6ClosedX alpha v t j -
          problem6ClosedY alpha v t (reverseItem j))
    (hy_nonneg :
      ∀ j : Item n, 0 ≤ problem6ClosedY alpha v t (reverseItem j)) :
    problem6ClosedTypeOneRawUtility alpha v t ≤
      problem6ClosedTypeZeroRawUtility alpha v t := by
  exact problem6ClosedTypeOneRawUtility_le_typeZeroRawUtility_of_strict_left_gaps
    hdec hleft hy_nonneg

/--
Appendix D, Lemma 6 comparison specialized to `α ≤ 1/2`, with the remaining
pivot-gap and mirror-index obligations explicit.
-/
theorem paper_lemma6_closedTypeOneRawUtility_le_typeZeroRawUtility_of_alpha_le_half
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha_half : alpha ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hpivot : Problem6ClosedNonnegativePivots alpha v t)
    (hmirror :
      ∀ j : Item n, j.val < t.val → t.val < (reverseItem j).val)
    (hpivot_gap :
      0 ≤ problem6ClosedX alpha v t t -
        problem6ClosedY alpha v t (reverseItem t)) :
    problem6ClosedTypeOneRawUtility alpha v t ≤
      problem6ClosedTypeZeroRawUtility alpha v t := by
  exact problem6ClosedTypeOneRawUtility_le_typeZeroRawUtility_of_alpha_le_half
    halpha0 halpha1 halpha_half hpos hdec hpivot hmirror hpivot_gap

/--
Appendix D, Lemma 6 comparison specialized to `α ≤ 1/2`: if the closed-form
pivot is at or before its mirror, type-0 raw utility dominates type-1 raw
utility without a separate pivot-gap assumption.
-/
theorem paper_lemma6_closedTypeOneRawUtility_le_typeZeroRawUtility_of_alpha_le_half_of_pivot_le_reverse
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha_half : alpha ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hpivot : Problem6ClosedNonnegativePivots alpha v t)
    (hcenter : t.val ≤ (reverseItem t).val) :
    problem6ClosedTypeOneRawUtility alpha v t ≤
      problem6ClosedTypeZeroRawUtility alpha v t := by
  exact problem6ClosedTypeOneRawUtility_le_typeZeroRawUtility_of_alpha_le_half_of_pivot_le_reverse
    halpha0 halpha1 halpha_half hpos hdec hpivot hcenter

/-- Appendix D, Lemma 6: closed-policy type-0 raw utility expansion. -/
theorem paper_lemma6_closedPolicy_rawTypeUtility_zero_eq
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hpivot : Problem6ClosedNonnegativePivots alpha v t) :
    TypeWeightedRecommendationModel.rawTypeUtility
      (twoTypeReducedModel alpha v)
      (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot) 0 =
      problem6ClosedTypeZeroRawUtility alpha v t := by
  exact problem6ClosedPolicy_rawTypeUtility_zero_eq
    halpha0 halpha1 hpos hpivot

/-- Appendix D, Lemma 6: closed-policy type-1 raw utility expansion. -/
theorem paper_lemma6_closedPolicy_rawTypeUtility_one_eq
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hpivot : Problem6ClosedNonnegativePivots alpha v t) :
    TypeWeightedRecommendationModel.rawTypeUtility
      (twoTypeReducedModel alpha v)
      (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot) 1 =
      problem6ClosedTypeOneRawUtility alpha v t := by
  exact problem6ClosedPolicy_rawTypeUtility_one_eq
    halpha0 halpha1 hpos hpivot

/--
Theorem 3 closed-form expansion for type `1`'s raw utility: pivot mirror value
plus the tail correction weighted by `I^*_{min}/(1-q_j)`.
-/
theorem paper_theorem3_closedTypeOneRawUtility_eq_pivot_add_tail
    {n : ℕ} (alpha : ℝ) (v : Item n → ℝ) (t : Item n) :
    problem6ClosedTypeOneRawUtility alpha v t =
      v (reverseItem t) +
        ∑ j : Item n,
          if t.val < j.val then
            problem6ClosedValue alpha v t / (1 - pairShare alpha v j) *
              (v (reverseItem j) - v (reverseItem t))
          else 0 := by
  exact problem6ClosedTypeOneRawUtility_eq_pivot_add_tail alpha v t

/--
Theorem 3 displayed formula for type `1`'s normalized utility of the closed
Problem 6 policy, with the best-item denominator explicit.
-/
theorem paper_theorem3_closedPolicy_normalizedTypeUtility_one_eq_pivot_add_tail
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hpivot : Problem6ClosedNonnegativePivots alpha v t) :
    TypeWeightedRecommendationModel.normalizedTypeUtility
        (twoTypeReducedModel alpha v)
        (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot) 1 =
      (v (reverseItem t) +
        ∑ j : Item n,
          if t.val < j.val then
            problem6ClosedValue alpha v t / (1 - pairShare alpha v j) *
              (v (reverseItem j) - v (reverseItem t))
          else 0) /
        TypeWeightedRecommendationModel.bestItemUtility
          (twoTypeReducedModel alpha v) 1 := by
  exact problem6ClosedPolicy_normalizedTypeUtility_one_eq_pivot_add_tail
    halpha0 halpha1 hpos hpivot

/--
Theorem 3 tail-gap positivity: for items after the pivot, the mirror value is
strictly above the pivot mirror value.
-/
theorem paper_theorem3_tailGap_pos_of_pivot_lt
    {n : ℕ} {v : Item n → ℝ} {t j : Item n}
    (hdec : StrictlyDecreasingByIndex v)
    (htj : t.val < j.val) :
    0 < v (reverseItem j) - v (reverseItem t) := by
  exact theorem3_tailGap_pos_of_pivot_lt hdec htj

/--
The reciprocal tail factor `1/(1-q_j(α))` is increasing in `α`.
-/
theorem paper_theorem3_one_sub_pairShare_inv_mono_alpha
    {n : ℕ} {alpha alpha' : ℝ} {v : Item n → ℝ} (j : Item n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (hpos : ∀ l : Item n, 0 < v l) :
    (1 - pairShare alpha v j)⁻¹ ≤
      (1 - pairShare alpha' v j)⁻¹ := by
  exact one_sub_pairShare_inv_mono_alpha j
    halpha0 halpha1 halpha0' halpha1' halpha_le hpos

/-- Appendix D, Lemma 5: fixed-pivot left inverse sum decreases with `α`. -/
theorem paper_lemma5_problem6LeftSum_antitone_alpha
    {n : ℕ} {alpha alpha' : ℝ} {v : Item n → ℝ} (t : Item n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (hpos : ∀ j : Item n, 0 < v j) :
    problem6LeftSum alpha' v t ≤ problem6LeftSum alpha v t := by
  exact problem6LeftSum_antitone_alpha t
    halpha0 halpha1 halpha0' halpha1' halpha_le hpos

/-- Appendix D, Lemma 5: fixed-pivot right inverse-complement sum increases with `α`. -/
theorem paper_lemma5_problem6RightSum_mono_alpha
    {n : ℕ} {alpha alpha' : ℝ} {v : Item n → ℝ} (t : Item n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (hpos : ∀ j : Item n, 0 < v j) :
    problem6RightSum alpha v t ≤ problem6RightSum alpha' v t := by
  exact problem6RightSum_mono_alpha t
    halpha0 halpha1 halpha0' halpha1' halpha_le hpos

/-- Appendix D, Lemma 5: the fixed-pivot crossing gap decreases with `α`. -/
theorem paper_lemma5_problem6PivotGap_antitone_alpha
    {n : ℕ} {alpha alpha' : ℝ} {v : Item n → ℝ} (t : Item n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (hpos : ∀ j : Item n, 0 < v j) :
    problem6PivotGap alpha' v t ≤ problem6PivotGap alpha v t := by
  exact problem6PivotGap_antitone_alpha t
    halpha0 halpha1 halpha0' halpha1' halpha_le hpos

/--
Appendix D, Lemma 5 crossing monotonicity: if pivot `t` crosses at the larger
`α'`, then it has already crossed at the smaller `α`.
-/
theorem paper_lemma5_problem6PivotGap_lower_crossing_of_alpha_le
    {n : ℕ} {alpha alpha' : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (hpos : ∀ j : Item n, 0 < v j)
    (hcross' :
      - (pairShare alpha' v t)⁻¹ ≤ problem6PivotGap alpha' v t) :
    - (pairShare alpha v t)⁻¹ ≤ problem6PivotGap alpha v t := by
  exact problem6PivotGap_lower_crossing_of_alpha_le
    halpha0 halpha1 halpha0' halpha1' halpha_le hpos hcross'

/-- Appendix D, Lemma 5: the lower crossing set is nonempty. -/
theorem paper_lemma5_problem6PivotCrossingSet_nonempty
    {n : ℕ} [NeZero n] {alpha : ℝ} {v : Item n → ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j) :
    (problem6PivotCrossingSet alpha v).Nonempty := by
  exact problem6PivotCrossingSet_nonempty
    halpha0 halpha1 hpos

/--
Appendix D, Lemma 5: the canonical first crossing pivot satisfies the
closed-form denominator bounds.
-/
theorem paper_lemma5_problem6FirstClosedPivot_denominatorBounds
    {n : ℕ} [NeZero n] {alpha : ℝ} {v : Item n → ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j) :
    Problem6ClosedPivotDenominatorBounds alpha v
      (problem6FirstClosedPivot alpha v halpha0 halpha1 hpos) := by
  exact problem6FirstClosedPivot_denominatorBounds
    halpha0 halpha1 hpos

/--
Appendix D, Lemma 5 converse slack bridge: denominator bounds imply the lower
crossing inequality used to define the canonical first pivot.
-/
theorem paper_lemma5_problem6PivotGap_lower_bound_of_closedPivotDenominatorBounds
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hbounds : Problem6ClosedPivotDenominatorBounds alpha v t) :
    - (pairShare alpha v t)⁻¹ ≤ problem6PivotGap alpha v t := by
  exact problem6PivotGap_lower_bound_of_closedPivotDenominatorBounds
    halpha0 halpha1 hpos hbounds

/--
Appendix D, Lemma 5 converse slack bridge: denominator bounds imply the upper
crossing inequality for the pivot gap.
-/
theorem paper_lemma5_problem6PivotGap_upper_bound_of_closedPivotDenominatorBounds
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hbounds : Problem6ClosedPivotDenominatorBounds alpha v t) :
    problem6PivotGap alpha v t ≤ (1 - pairShare alpha v t)⁻¹ := by
  exact problem6PivotGap_upper_bound_of_closedPivotDenominatorBounds
    halpha0 halpha1 hpos hbounds

/--
Appendix D, Lemma 5: any denominator-bounded closed-form pivot lies weakly
after the canonical first crossing pivot.
-/
theorem paper_lemma5_problem6FirstClosedPivot_le_of_closedPivotDenominatorBounds
    {n : ℕ} [NeZero n] {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hbounds : Problem6ClosedPivotDenominatorBounds alpha v t) :
    (problem6FirstClosedPivot alpha v halpha0 halpha1 hpos).val ≤ t.val := by
  exact problem6FirstClosedPivot_le_of_closedPivotDenominatorBounds
    halpha0 halpha1 hpos hbounds

/--
Appendix D, Lemma 8 boundary stitch: if adjacent pivots meet at a tight lower
crossing boundary, both closed-form pivots satisfy the Lemma 5 denominator
bounds.
-/
theorem paper_lemma8_problem6ClosedPivotDenominatorBounds_adjacent_of_boundary
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {t u : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hnext : u.val = t.val + 1)
    (hboundary :
      problem6PivotGap alpha v t = - (pairShare alpha v t)⁻¹) :
    Problem6ClosedPivotDenominatorBounds alpha v t ∧
      Problem6ClosedPivotDenominatorBounds alpha v u := by
  exact problem6ClosedPivotDenominatorBounds_adjacent_of_boundary
    halpha0 halpha1 hpos hnext hboundary

/--
Appendix D, Lemma 8 boundary stitch: at an adjacent tight-crossing boundary,
the two adjacent closed-form values agree.
-/
theorem paper_lemma8_problem6ClosedValue_eq_of_adjacent_boundary
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {t u : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hnext : u.val = t.val + 1)
    (hboundary :
      problem6PivotGap alpha v t = - (pairShare alpha v t)⁻¹) :
    problem6ClosedValue alpha v t =
      problem6ClosedValue alpha v u := by
  exact problem6ClosedValue_eq_of_adjacent_boundary
    halpha0 halpha1 hpos hdec hnext hboundary

/--
Appendix D, Lemma 8 boundary stitch: a certified interval with pivot `t`
stitches through a tight adjacent boundary to a certified interval with pivot
`t+1`.
-/
theorem paper_lemma8_reducedOptimalItemFairness_mono_across_adjacent_closed_boundary
    {n : ℕ} [NeZero n]
    {alphaLeft alphaBoundary alphaRight : ℝ}
    {v : Item n → ℝ} {t u : Item n}
    (halphaLeft0 : 0 < alphaLeft) (halphaLeft1 : alphaLeft < 1)
    (halphaBoundary0 : 0 < alphaBoundary)
    (halphaBoundary1 : alphaBoundary < 1)
    (halphaRight0 : 0 < alphaRight) (halphaRight1 : alphaRight < 1)
    (hleft_le_boundary : alphaLeft ≤ alphaBoundary)
    (hboundary_le_right : alphaBoundary ≤ alphaRight)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter_t : t.val ≤ (reverseItem t).val)
    (hcenter_u : u.val ≤ (reverseItem u).val)
    (hleft_bounds : Problem6ClosedPivotDenominatorBounds alphaLeft v t)
    (hnext : u.val = t.val + 1)
    (hboundary :
      problem6PivotGap alphaBoundary v t =
        - (pairShare alphaBoundary v t)⁻¹)
    (hright_bounds : Problem6ClosedPivotDenominatorBounds alphaRight v u) :
    TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel alphaLeft v) ≤
      TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel alphaRight v) := by
  exact
    lemma8_reducedOptimalItemFairness_mono_across_adjacent_closed_boundary
      halphaLeft0 halphaLeft1
      halphaBoundary0 halphaBoundary1
      halphaRight0 halphaRight1
      hleft_le_boundary hboundary_le_right
      hpos hdec hcenter_t hcenter_u hleft_bounds
      hnext hboundary hright_bounds

/--
Appendix D, Lemma 8 boundary stitch for canonical first-crossing pivots,
odd-center case.
-/
theorem paper_lemma8_reducedOptimalItemFairness_mono_across_adjacent_firstClosedPivot_boundary_center
    {n : ℕ} [NeZero n]
    {alphaLeft alphaBoundary alphaRight : ℝ}
    {v : Item n → ℝ} {c t u : Item n}
    (halphaLeft0 : 0 < alphaLeft) (halphaLeft1 : alphaLeft < 1)
    (halphaBoundary0 : 0 < alphaBoundary)
    (halphaBoundary1 : alphaBoundary < 1)
    (halphaRight0 : 0 < alphaRight) (halphaRight1 : alphaRight < 1)
    (hleft_le_boundary : alphaLeft ≤ alphaBoundary)
    (hboundary_le_right : alphaBoundary ≤ alphaRight)
    (halphaLeft_half : alphaLeft ≤ 1 / 2)
    (halphaRight_half : alphaRight ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter_c : c.val = (reverseItem c).val)
    (hleft_pivot :
      problem6FirstClosedPivot alphaLeft v
        halphaLeft0 halphaLeft1 hpos = t)
    (hright_pivot :
      problem6FirstClosedPivot alphaRight v
        halphaRight0 halphaRight1 hpos = u)
    (hnext : u.val = t.val + 1)
    (hboundary :
      problem6PivotGap alphaBoundary v t =
        - (pairShare alphaBoundary v t)⁻¹) :
    TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel alphaLeft v) ≤
      TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel alphaRight v) := by
  exact
    lemma8_reducedOptimalItemFairness_mono_across_adjacent_firstClosedPivot_boundary_center
      halphaLeft0 halphaLeft1
      halphaBoundary0 halphaBoundary1
      halphaRight0 halphaRight1
      hleft_le_boundary hboundary_le_right
      halphaLeft_half halphaRight_half
      hpos hdec hcenter_c hleft_pivot hright_pivot
      hnext hboundary

/--
Appendix D, Lemma 8 boundary stitch for canonical first-crossing pivots,
even-center case.
-/
theorem paper_lemma8_reducedOptimalItemFairness_mono_across_adjacent_firstClosedPivot_boundary_succ_center
    {n : ℕ} [NeZero n]
    {alphaLeft alphaBoundary alphaRight : ℝ}
    {v : Item n → ℝ} {c t u : Item n}
    (halphaLeft0 : 0 < alphaLeft) (halphaLeft1 : alphaLeft < 1)
    (halphaBoundary0 : 0 < alphaBoundary)
    (halphaBoundary1 : alphaBoundary < 1)
    (halphaRight0 : 0 < alphaRight) (halphaRight1 : alphaRight < 1)
    (hleft_le_boundary : alphaLeft ≤ alphaBoundary)
    (hboundary_le_right : alphaBoundary ≤ alphaRight)
    (halphaLeft_half : alphaLeft ≤ 1 / 2)
    (halphaRight_half : alphaRight ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hsucc : c.val + 1 = (reverseItem c).val)
    (hleft_pivot :
      problem6FirstClosedPivot alphaLeft v
        halphaLeft0 halphaLeft1 hpos = t)
    (hright_pivot :
      problem6FirstClosedPivot alphaRight v
        halphaRight0 halphaRight1 hpos = u)
    (hnext : u.val = t.val + 1)
    (hboundary :
      problem6PivotGap alphaBoundary v t =
        - (pairShare alphaBoundary v t)⁻¹) :
    TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel alphaLeft v) ≤
      TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel alphaRight v) := by
  exact
    lemma8_reducedOptimalItemFairness_mono_across_adjacent_firstClosedPivot_boundary_succ_center
      halphaLeft0 halphaLeft1
      halphaBoundary0 halphaBoundary1
      halphaRight0 halphaRight1
      hleft_le_boundary hboundary_le_right
      halphaLeft_half halphaRight_half
      hpos hdec hsucc hleft_pivot hright_pivot
      hnext hboundary

/--
Appendix D, Lemma 8 finite boundary stitch: a finite chain of certified
adjacent tight-boundary crossings implies reduced item-fairness monotonicity.
-/
theorem paper_lemma8_reducedOptimalItemFairness_mono_of_adjacent_closedBoundary_chain
    {n : ℕ} [NeZero n]
    {v : Item n → ℝ} (r : ℕ)
    (alphaSeq boundarySeq : ℕ → ℝ)
    (pivotSeq : ℕ → Item n)
    (halpha0 : ∀ i, i ≤ r → 0 < alphaSeq i)
    (halpha1 : ∀ i, i ≤ r → alphaSeq i < 1)
    (hboundary0 : ∀ i, i < r → 0 < boundarySeq i)
    (hboundary1 : ∀ i, i < r → boundarySeq i < 1)
    (hleft_le_boundary :
      ∀ i, i < r → alphaSeq i ≤ boundarySeq i)
    (hboundary_le_right :
      ∀ i, i < r → boundarySeq i ≤ alphaSeq (i + 1))
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hbounds :
      ∀ i, ∀ hi : i ≤ r,
        Problem6ClosedPivotDenominatorBounds (alphaSeq i) v (pivotSeq i))
    (hcenter :
      ∀ i, ∀ hi : i ≤ r,
        (pivotSeq i).val ≤ (reverseItem (pivotSeq i)).val)
    (hnext :
      ∀ i, i < r → (pivotSeq (i + 1)).val = (pivotSeq i).val + 1)
    (hboundary :
      ∀ i, ∀ hi : i < r,
        problem6PivotGap (boundarySeq i) v (pivotSeq i) =
          - (pairShare (boundarySeq i) v (pivotSeq i))⁻¹) :
    TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel (alphaSeq 0) v) ≤
      TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel (alphaSeq r) v) := by
  exact
    lemma8_reducedOptimalItemFairness_mono_of_adjacent_closedBoundary_chain
      r alphaSeq boundarySeq pivotSeq halpha0 halpha1
      hboundary0 hboundary1 hleft_le_boundary hboundary_le_right
      hpos hdec hbounds hcenter hnext hboundary

/--
Appendix D, Lemma 8 finite boundary stitch for canonical first-crossing
pivots, odd-center case.
-/
theorem paper_lemma8_reducedOptimalItemFairness_mono_firstHalf_center_adjacentBoundary_chain
    {n : ℕ} [NeZero n]
    {v : Item n → ℝ} {c : Item n}
    (r : ℕ)
    (alphaSeq boundarySeq : ℕ → ℝ)
    (pivotSeq : ℕ → Item n)
    (halpha0 : ∀ i, i ≤ r → 0 < alphaSeq i)
    (halpha1 : ∀ i, i ≤ r → alphaSeq i < 1)
    (halpha_half : ∀ i, i ≤ r → alphaSeq i ≤ 1 / 2)
    (hboundary0 : ∀ i, i < r → 0 < boundarySeq i)
    (hboundary1 : ∀ i, i < r → boundarySeq i < 1)
    (hleft_le_boundary :
      ∀ i, i < r → alphaSeq i ≤ boundarySeq i)
    (hboundary_le_right :
      ∀ i, i < r → boundarySeq i ≤ alphaSeq (i + 1))
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter_c : c.val = (reverseItem c).val)
    (hpivot_def :
      ∀ i, ∀ hi : i ≤ r,
        problem6FirstClosedPivot (alphaSeq i) v
          (halpha0 i hi) (halpha1 i hi) hpos = pivotSeq i)
    (hnext :
      ∀ i, i < r → (pivotSeq (i + 1)).val = (pivotSeq i).val + 1)
    (hboundary :
      ∀ i, ∀ hi : i < r,
        problem6PivotGap (boundarySeq i) v (pivotSeq i) =
          - (pairShare (boundarySeq i) v (pivotSeq i))⁻¹) :
    TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel (alphaSeq 0) v) ≤
      TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel (alphaSeq r) v) := by
  exact
    lemma8_reducedOptimalItemFairness_mono_firstHalf_center_adjacentBoundary_chain
      r alphaSeq boundarySeq pivotSeq halpha0 halpha1 halpha_half
      hboundary0 hboundary1 hleft_le_boundary hboundary_le_right
      hpos hdec hcenter_c hpivot_def hnext hboundary

/--
Appendix D, Lemma 8 finite boundary stitch for canonical first-crossing
pivots, even-center case.
-/
theorem paper_lemma8_reducedOptimalItemFairness_mono_firstHalf_succ_center_adjacentBoundary_chain
    {n : ℕ} [NeZero n]
    {v : Item n → ℝ} {c : Item n}
    (r : ℕ)
    (alphaSeq boundarySeq : ℕ → ℝ)
    (pivotSeq : ℕ → Item n)
    (halpha0 : ∀ i, i ≤ r → 0 < alphaSeq i)
    (halpha1 : ∀ i, i ≤ r → alphaSeq i < 1)
    (halpha_half : ∀ i, i ≤ r → alphaSeq i ≤ 1 / 2)
    (hboundary0 : ∀ i, i < r → 0 < boundarySeq i)
    (hboundary1 : ∀ i, i < r → boundarySeq i < 1)
    (hleft_le_boundary :
      ∀ i, i < r → alphaSeq i ≤ boundarySeq i)
    (hboundary_le_right :
      ∀ i, i < r → boundarySeq i ≤ alphaSeq (i + 1))
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hsucc : c.val + 1 = (reverseItem c).val)
    (hpivot_def :
      ∀ i, ∀ hi : i ≤ r,
        problem6FirstClosedPivot (alphaSeq i) v
          (halpha0 i hi) (halpha1 i hi) hpos = pivotSeq i)
    (hnext :
      ∀ i, i < r → (pivotSeq (i + 1)).val = (pivotSeq i).val + 1)
    (hboundary :
      ∀ i, ∀ hi : i < r,
        problem6PivotGap (boundarySeq i) v (pivotSeq i) =
          - (pairShare (boundarySeq i) v (pivotSeq i))⁻¹) :
    TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel (alphaSeq 0) v) ≤
      TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel (alphaSeq r) v) := by
  exact
    lemma8_reducedOptimalItemFairness_mono_firstHalf_succ_center_adjacentBoundary_chain
      r alphaSeq boundarySeq pivotSeq halpha0 halpha1 halpha_half
      hboundary0 hboundary1 hleft_le_boundary hboundary_le_right
      hpos hdec hsucc hpivot_def hnext hboundary

/--
Appendix D, Lemma 8 adjacent canonical-pivot change, odd-center case: the
boundary point is constructed internally from the endpoint pivot change.
-/
theorem paper_lemma8_reducedOptimalItemFairness_mono_across_adjacent_firstClosedPivot_change_center
    {n : ℕ} [NeZero n]
    {alphaLeft alphaRight : ℝ}
    {v : Item n → ℝ} {c t u : Item n}
    (halphaLeft0 : 0 < alphaLeft) (halphaLeft1 : alphaLeft < 1)
    (halphaRight0 : 0 < alphaRight) (halphaRight1 : alphaRight < 1)
    (hleft_le_right : alphaLeft ≤ alphaRight)
    (halphaLeft_half : alphaLeft ≤ 1 / 2)
    (halphaRight_half : alphaRight ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter_c : c.val = (reverseItem c).val)
    (hleft_pivot :
      problem6FirstClosedPivot alphaLeft v
        halphaLeft0 halphaLeft1 hpos = t)
    (hright_pivot :
      problem6FirstClosedPivot alphaRight v
        halphaRight0 halphaRight1 hpos = u)
    (hnext : u.val = t.val + 1) :
    TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel alphaLeft v) ≤
      TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel alphaRight v) := by
  exact
    lemma8_reducedOptimalItemFairness_mono_across_adjacent_firstClosedPivot_change_center
      halphaLeft0 halphaLeft1 halphaRight0 halphaRight1
      hleft_le_right halphaLeft_half halphaRight_half
      hpos hdec hcenter_c hleft_pivot hright_pivot hnext

/--
Appendix D, Lemma 8 adjacent canonical-pivot change, even-center case.
-/
theorem paper_lemma8_reducedOptimalItemFairness_mono_across_adjacent_firstClosedPivot_change_succ_center
    {n : ℕ} [NeZero n]
    {alphaLeft alphaRight : ℝ}
    {v : Item n → ℝ} {c t u : Item n}
    (halphaLeft0 : 0 < alphaLeft) (halphaLeft1 : alphaLeft < 1)
    (halphaRight0 : 0 < alphaRight) (halphaRight1 : alphaRight < 1)
    (hleft_le_right : alphaLeft ≤ alphaRight)
    (halphaLeft_half : alphaLeft ≤ 1 / 2)
    (halphaRight_half : alphaRight ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hsucc : c.val + 1 = (reverseItem c).val)
    (hleft_pivot :
      problem6FirstClosedPivot alphaLeft v
        halphaLeft0 halphaLeft1 hpos = t)
    (hright_pivot :
      problem6FirstClosedPivot alphaRight v
        halphaRight0 halphaRight1 hpos = u)
    (hnext : u.val = t.val + 1) :
    TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel alphaLeft v) ≤
      TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel alphaRight v) := by
  exact
    lemma8_reducedOptimalItemFairness_mono_across_adjacent_firstClosedPivot_change_succ_center
      halphaLeft0 halphaLeft1 halphaRight0 halphaRight1
      hleft_le_right halphaLeft_half halphaRight_half
      hpos hdec hsucc hleft_pivot hright_pivot hnext

/--
Appendix D, Lemma 8 finite adjacent canonical-pivot change chain,
odd-center case.
-/
theorem paper_lemma8_reducedOptimalItemFairness_mono_firstHalf_center_adjacentPivotChange_chain
    {n : ℕ} [NeZero n]
    {v : Item n → ℝ} {c : Item n}
    (r : ℕ)
    (alphaSeq : ℕ → ℝ)
    (pivotSeq : ℕ → Item n)
    (halpha0 : ∀ i, i ≤ r → 0 < alphaSeq i)
    (halpha1 : ∀ i, i ≤ r → alphaSeq i < 1)
    (halpha_half : ∀ i, i ≤ r → alphaSeq i ≤ 1 / 2)
    (hstep : ∀ i, i < r → alphaSeq i ≤ alphaSeq (i + 1))
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter_c : c.val = (reverseItem c).val)
    (hpivot_def :
      ∀ i, ∀ hi : i ≤ r,
        problem6FirstClosedPivot (alphaSeq i) v
          (halpha0 i hi) (halpha1 i hi) hpos = pivotSeq i)
    (hnext :
      ∀ i, i < r → (pivotSeq (i + 1)).val = (pivotSeq i).val + 1) :
    TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel (alphaSeq 0) v) ≤
      TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel (alphaSeq r) v) := by
  exact
    lemma8_reducedOptimalItemFairness_mono_firstHalf_center_adjacentPivotChange_chain
      r alphaSeq pivotSeq halpha0 halpha1 halpha_half hstep
      hpos hdec hcenter_c hpivot_def hnext

/--
Appendix D, Lemma 8 finite adjacent canonical-pivot change chain,
even-center case.
-/
theorem paper_lemma8_reducedOptimalItemFairness_mono_firstHalf_succ_center_adjacentPivotChange_chain
    {n : ℕ} [NeZero n]
    {v : Item n → ℝ} {c : Item n}
    (r : ℕ)
    (alphaSeq : ℕ → ℝ)
    (pivotSeq : ℕ → Item n)
    (halpha0 : ∀ i, i ≤ r → 0 < alphaSeq i)
    (halpha1 : ∀ i, i ≤ r → alphaSeq i < 1)
    (halpha_half : ∀ i, i ≤ r → alphaSeq i ≤ 1 / 2)
    (hstep : ∀ i, i < r → alphaSeq i ≤ alphaSeq (i + 1))
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hsucc : c.val + 1 = (reverseItem c).val)
    (hpivot_def :
      ∀ i, ∀ hi : i ≤ r,
        problem6FirstClosedPivot (alphaSeq i) v
          (halpha0 i hi) (halpha1 i hi) hpos = pivotSeq i)
    (hnext :
      ∀ i, i < r → (pivotSeq (i + 1)).val = (pivotSeq i).val + 1) :
    TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel (alphaSeq 0) v) ≤
      TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel (alphaSeq r) v) := by
  exact
    lemma8_reducedOptimalItemFairness_mono_firstHalf_succ_center_adjacentPivotChange_chain
      r alphaSeq pivotSeq halpha0 halpha1 halpha_half hstep
      hpos hdec hsucc hpivot_def hnext

/--
Appendix D, Lemma 8 global canonical first-pivot stitch, odd-center case:
the no-skip adjacent-pivot construction connects any endpoint canonical
first pivots in the first half.
-/
theorem paper_lemma8_reducedOptimalItemFairness_mono_firstHalf_center_of_firstClosedPivot_endpoints
    {n : ℕ} [NeZero n]
    {alphaLeft alphaRight : ℝ} {v : Item n → ℝ} {c t u : Item n}
    (halphaLeft0 : 0 < alphaLeft) (halphaLeft1 : alphaLeft < 1)
    (halphaRight0 : 0 < alphaRight) (halphaRight1 : alphaRight < 1)
    (hleft_le_right : alphaLeft ≤ alphaRight)
    (halphaLeft_half : alphaLeft ≤ 1 / 2)
    (halphaRight_half : alphaRight ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter_c : c.val = (reverseItem c).val)
    (hleft_pivot :
      problem6FirstClosedPivot alphaLeft v
        halphaLeft0 halphaLeft1 hpos = t)
    (hright_pivot :
      problem6FirstClosedPivot alphaRight v
        halphaRight0 halphaRight1 hpos = u) :
    TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel alphaLeft v) ≤
      TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel alphaRight v) := by
  exact
    lemma8_reducedOptimalItemFairness_mono_firstHalf_center_of_firstClosedPivot_endpoints
      halphaLeft0 halphaLeft1 halphaRight0 halphaRight1
      hleft_le_right halphaLeft_half halphaRight_half
      hpos hdec hcenter_c hleft_pivot hright_pivot

/--
Appendix D, Lemma 8 global canonical first-pivot stitch, even-center case:
the same endpoint stitch applies when the middle items are adjacent.
-/
theorem paper_lemma8_reducedOptimalItemFairness_mono_firstHalf_succ_center_of_firstClosedPivot_endpoints
    {n : ℕ} [NeZero n]
    {alphaLeft alphaRight : ℝ} {v : Item n → ℝ} {c t u : Item n}
    (halphaLeft0 : 0 < alphaLeft) (halphaLeft1 : alphaLeft < 1)
    (halphaRight0 : 0 < alphaRight) (halphaRight1 : alphaRight < 1)
    (hleft_le_right : alphaLeft ≤ alphaRight)
    (halphaLeft_half : alphaLeft ≤ 1 / 2)
    (halphaRight_half : alphaRight ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hsucc : c.val + 1 = (reverseItem c).val)
    (hleft_pivot :
      problem6FirstClosedPivot alphaLeft v
        halphaLeft0 halphaLeft1 hpos = t)
    (hright_pivot :
      problem6FirstClosedPivot alphaRight v
        halphaRight0 halphaRight1 hpos = u) :
    TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel alphaLeft v) ≤
      TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel alphaRight v) := by
  exact
    lemma8_reducedOptimalItemFairness_mono_firstHalf_succ_center_of_firstClosedPivot_endpoints
      halphaLeft0 halphaLeft1 halphaRight0 halphaRight1
      hleft_le_right halphaLeft_half halphaRight_half
      hpos hdec hsucc hleft_pivot hright_pivot

/--
Appendix D, Lemma 8 paper-style form, odd-center case: for any first-half
`α ≤ α'`, reduced optimal item fairness is monotone.
-/
theorem paper_lemma8_reducedOptimalItemFairness_mono_firstHalf_center_of_alpha_le
    {n : ℕ} [NeZero n]
    {alpha alpha' : ℝ} {v : Item n → ℝ} {c : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (halpha_half : alpha ≤ 1 / 2)
    (halpha_half' : alpha' ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter_c : c.val = (reverseItem c).val) :
    TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel alpha v) ≤
      TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel alpha' v) := by
  exact
    lemma8_reducedOptimalItemFairness_mono_firstHalf_center_of_alpha_le
      halpha0 halpha1 halpha0' halpha1' halpha_le
      halpha_half halpha_half' hpos hdec hcenter_c

/--
Appendix D, Lemma 8 paper-style form, even-center case.
-/
theorem paper_lemma8_reducedOptimalItemFairness_mono_firstHalf_succ_center_of_alpha_le
    {n : ℕ} [NeZero n]
    {alpha alpha' : ℝ} {v : Item n → ℝ} {c : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (halpha_half : alpha ≤ 1 / 2)
    (halpha_half' : alpha' ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hsucc : c.val + 1 = (reverseItem c).val) :
    TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel alpha v) ≤
      TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel alpha' v) := by
  exact
    lemma8_reducedOptimalItemFairness_mono_firstHalf_succ_center_of_alpha_le
      halpha0 halpha1 halpha0' halpha1' halpha_le
      halpha_half halpha_half' hpos hdec hsucc

/--
Appendix D, Lemma 7-style monotonicity for the canonical Lemma 5 pivot:
as `α` increases, the first crossing pivot weakly moves right.
-/
theorem paper_lemma7_problem6FirstClosedPivot_mono_alpha
    {n : ℕ} [NeZero n] {alpha alpha' : ℝ} {v : Item n → ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (hpos : ∀ j : Item n, 0 < v j) :
    (problem6FirstClosedPivot alpha v halpha0 halpha1 hpos).val ≤
      (problem6FirstClosedPivot alpha' v halpha0' halpha1' hpos).val := by
  exact problem6FirstClosedPivot_mono_alpha
    halpha0 halpha1 halpha0' halpha1' halpha_le hpos

/--
Appendix D, Lemma 10 / Lemma 8 bridge: for `α ≤ 1/2`, the canonical first
closed pivot lies before its mirror in the exact-center case.
-/
theorem paper_lemma10_problem6FirstClosedPivot_le_reverse_of_alpha_le_half_center
    {n : ℕ} [NeZero n] {alpha : ℝ} {v : Item n → ℝ} {c : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha_half : alpha ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hcenter : c.val = (reverseItem c).val) :
    (problem6FirstClosedPivot alpha v halpha0 halpha1 hpos).val ≤
      (reverseItem
        (problem6FirstClosedPivot alpha v halpha0 halpha1 hpos)).val := by
  exact problem6FirstClosedPivot_le_reverse_of_alpha_le_half_center
    halpha0 halpha1 halpha_half hpos hcenter

/--
Appendix D, Lemma 10 / Lemma 8 bridge: for `α ≤ 1/2`, the canonical first
closed pivot lies before its mirror in the even-center case.
-/
theorem paper_lemma10_problem6FirstClosedPivot_le_reverse_of_alpha_le_half_succ_center
    {n : ℕ} [NeZero n] {alpha : ℝ} {v : Item n → ℝ} {c : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha_half : alpha ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hsucc : c.val + 1 = (reverseItem c).val) :
    (problem6FirstClosedPivot alpha v halpha0 halpha1 hpos).val ≤
      (reverseItem
        (problem6FirstClosedPivot alpha v halpha0 halpha1 hpos)).val := by
  exact problem6FirstClosedPivot_le_reverse_of_alpha_le_half_succ_center
    halpha0 halpha1 halpha_half hpos hsucc

/--
Theorem 3 fixed-pivot multiplier monotonicity:
`I^*_{min}(α)/(1-q_j(α))` is increasing on a fixed-pivot first-half interval.
-/
theorem paper_theorem3_fixedPivot_tailMultiplier_mono
    {n : ℕ} {alpha alpha' : ℝ} {v : Item n → ℝ} {t j : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter : t.val ≤ (reverseItem t).val) :
    problem6ClosedValue alpha v t / (1 - pairShare alpha v j) ≤
      problem6ClosedValue alpha' v t / (1 - pairShare alpha' v j) := by
  exact theorem3_fixedPivot_tailMultiplier_mono
    halpha0 halpha1 halpha0' halpha1' halpha_le hpos hdec hcenter

/-- Type-1's best-item denominator in the opposing model is independent of `α`. -/
theorem paper_theorem3_bestItemUtility_one_eq_of_alpha
    {n : ℕ} [NeZero n] (alpha alpha' : ℝ) (v : Item n → ℝ) :
    TypeWeightedRecommendationModel.bestItemUtility
        (twoTypeReducedModel alpha v) 1 =
      TypeWeightedRecommendationModel.bestItemUtility
        (twoTypeReducedModel alpha' v) 1 := by
  exact twoTypeReducedModel_bestItemUtility_one_eq_of_alpha alpha alpha' v

/--
Theorem 3 fixed-pivot raw utility monotonicity for type `1`.
-/
theorem paper_theorem3_fixedPivot_closedTypeOneRawUtility_mono
    {n : ℕ} {alpha alpha' : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter : t.val ≤ (reverseItem t).val) :
    problem6ClosedTypeOneRawUtility alpha v t ≤
      problem6ClosedTypeOneRawUtility alpha' v t := by
  exact theorem3_fixedPivot_closedTypeOneRawUtility_mono
    halpha0 halpha1 halpha0' halpha1' halpha_le hpos hdec hcenter

/--
Theorem 3 fixed-pivot normalized utility monotonicity for type `1`.
-/
theorem paper_theorem3_fixedPivot_closedPolicy_normalizedTypeUtility_one_mono
    {n : ℕ} [NeZero n]
    {alpha alpha' : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter : t.val ≤ (reverseItem t).val)
    (hpivot : Problem6ClosedNonnegativePivots alpha v t)
    (hpivot' : Problem6ClosedNonnegativePivots alpha' v t) :
    TypeWeightedRecommendationModel.normalizedTypeUtility
        (twoTypeReducedModel alpha v)
        (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot) 1 ≤
      TypeWeightedRecommendationModel.normalizedTypeUtility
        (twoTypeReducedModel alpha' v)
        (problem6ClosedPolicy alpha' v t halpha0' halpha1' hpos hpivot') 1 := by
  exact theorem3_fixedPivot_closedPolicy_normalizedTypeUtility_one_mono
    halpha0 halpha1 halpha0' halpha1' halpha_le hpos hdec hcenter hpivot hpivot'

/--
Theorem 3 same-selected-pivot interval step for actual equality-form optimal
BFS policies: selected type fairness is monotone on a first-half interval where
the selected pivot does not change.
-/
theorem paper_theorem3_typeFairness_mono_of_same_selected_equalizedBasicOptimal
    {n : ℕ} [NeZero n]
    {alpha alpha' : ℝ} {v : Item n → ℝ}
    {ρ ρ' : TypePolicy 2 n} {ell ell' : ℝ}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_half : alpha ≤ 1 / 2)
    (halpha_half' : alpha' ≤ 1 / 2)
    (halpha_le : alpha ≤ alpha')
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hpivot :
      TypePolicy.lastActiveTypeZero ρ =
        TypePolicy.lastActiveTypeZero ρ')
    (hcenter :
      (TypePolicy.lastActiveTypeZero ρ).val ≤
        (reverseItem (TypePolicy.lastActiveTypeZero ρ)).val)
    (h : Problem6EqualizedBasicOptimal alpha v ρ ell)
    (h' : Problem6EqualizedBasicOptimal alpha' v ρ' ell') :
    TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel alpha v) ρ ≤
      TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel alpha' v) ρ' := by
  exact theorem3_typeFairness_mono_of_same_selected_equalizedBasicOptimal
    hn halpha0 halpha1 halpha0' halpha1' halpha_half halpha_half'
    halpha_le hpos hdec hpivot hcenter h h'

/--
Theorem 3 finite-stitch core: a first-half chain whose adjacent steps either
stay in one selected-pivot interval or repeat the same `α` has monotone
selected type fairness.
-/
theorem paper_theorem3_typeFairness_mono_of_same_selected_or_equal_alpha_chain
    {n : ℕ} [NeZero n]
    {v : Item n → ℝ} (r : ℕ)
    (alphaSeq : ℕ → ℝ)
    (ρSeq : ℕ → TypePolicy 2 n)
    (ellSeq : ℕ → ℝ)
    (hn : 2 < n)
    (halpha0 : ∀ i, i ≤ r → 0 < alphaSeq i)
    (halpha1 : ∀ i, i ≤ r → alphaSeq i < 1)
    (halpha_half : ∀ i, i ≤ r → alphaSeq i ≤ 1 / 2)
    (hstep : ∀ i, i < r → alphaSeq i ≤ alphaSeq (i + 1))
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hpivot_or_eq :
      ∀ i, i < r →
        TypePolicy.lastActiveTypeZero (ρSeq i) =
          TypePolicy.lastActiveTypeZero (ρSeq (i + 1)) ∨
        alphaSeq i = alphaSeq (i + 1))
    (hcenter :
      ∀ i, i < r →
        (TypePolicy.lastActiveTypeZero (ρSeq i)).val ≤
          (reverseItem (TypePolicy.lastActiveTypeZero (ρSeq i))).val)
    (hopt :
      ∀ i, i ≤ r →
        Problem6EqualizedBasicOptimal (alphaSeq i) v (ρSeq i) (ellSeq i)) :
    TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel (alphaSeq 0) v) (ρSeq 0) ≤
      TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel (alphaSeq r) v) (ρSeq r) := by
  exact theorem3_typeFairness_mono_of_same_selected_or_equal_alpha_chain
    r alphaSeq ρSeq ellSeq hn halpha0 halpha1 halpha_half hstep hpos hdec
    hpivot_or_eq hcenter hopt

/--
Theorem 3 finite-stitch core, odd-center case: Lemma 10 supplies the
pivot-before-mirror side condition throughout the first-half chain.
-/
theorem paper_theorem3_typeFairness_mono_firstHalf_center_chain
    {n : ℕ} [NeZero n]
    {v : Item n → ℝ} {c : Item n}
    (r : ℕ)
    (alphaSeq : ℕ → ℝ)
    (ρSeq : ℕ → TypePolicy 2 n)
    (ellSeq : ℕ → ℝ)
    {ρhalf : TypePolicy 2 n} {ellHalf : ℝ}
    (hn : 2 < n)
    (halpha0 : ∀ i, i ≤ r → 0 < alphaSeq i)
    (halpha1 : ∀ i, i ≤ r → alphaSeq i < 1)
    (halpha_half : ∀ i, i ≤ r → alphaSeq i ≤ 1 / 2)
    (hstep : ∀ i, i < r → alphaSeq i ≤ alphaSeq (i + 1))
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter_c : c.val = (reverseItem c).val)
    (hpivot_or_eq :
      ∀ i, i < r →
        TypePolicy.lastActiveTypeZero (ρSeq i) =
          TypePolicy.lastActiveTypeZero (ρSeq (i + 1)) ∨
        alphaSeq i = alphaSeq (i + 1))
    (hopt :
      ∀ i, i ≤ r →
        Problem6EqualizedBasicOptimal (alphaSeq i) v (ρSeq i) (ellSeq i))
    (hhalf :
      Problem6EqualizedBasicOptimal (1 / 2) v ρhalf ellHalf) :
    TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel (alphaSeq 0) v) (ρSeq 0) ≤
      TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel (alphaSeq r) v) (ρSeq r) := by
  exact theorem3_typeFairness_mono_firstHalf_center_chain
    r alphaSeq ρSeq ellSeq hn halpha0 halpha1 halpha_half hstep hpos hdec
    hcenter_c hpivot_or_eq hopt hhalf

/--
Theorem 3 finite-stitch core, even-center case: Lemma 10 supplies the
pivot-before-mirror side condition throughout the first-half chain.
-/
theorem paper_theorem3_typeFairness_mono_firstHalf_succ_center_chain
    {n : ℕ} [NeZero n]
    {v : Item n → ℝ} {c : Item n}
    (r : ℕ)
    (alphaSeq : ℕ → ℝ)
    (ρSeq : ℕ → TypePolicy 2 n)
    (ellSeq : ℕ → ℝ)
    {ρhalf : TypePolicy 2 n} {ellHalf : ℝ}
    (hn : 2 < n)
    (halpha0 : ∀ i, i ≤ r → 0 < alphaSeq i)
    (halpha1 : ∀ i, i ≤ r → alphaSeq i < 1)
    (halpha_half : ∀ i, i ≤ r → alphaSeq i ≤ 1 / 2)
    (hstep : ∀ i, i < r → alphaSeq i ≤ alphaSeq (i + 1))
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hsucc : c.val + 1 = (reverseItem c).val)
    (hpivot_or_eq :
      ∀ i, i < r →
        TypePolicy.lastActiveTypeZero (ρSeq i) =
          TypePolicy.lastActiveTypeZero (ρSeq (i + 1)) ∨
        alphaSeq i = alphaSeq (i + 1))
    (hopt :
      ∀ i, i ≤ r →
        Problem6EqualizedBasicOptimal (alphaSeq i) v (ρSeq i) (ellSeq i))
    (hhalf :
      Problem6EqualizedBasicOptimal (1 / 2) v ρhalf ellHalf) :
    TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel (alphaSeq 0) v) (ρSeq 0) ≤
      TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel (alphaSeq r) v) (ρSeq r) := by
  exact theorem3_typeFairness_mono_firstHalf_succ_center_chain
    r alphaSeq ρSeq ellSeq hn halpha0 halpha1 halpha_half hstep hpos hdec
    hsucc hpivot_or_eq hopt hhalf

/--
Theorem 3 finite-stitch core, odd-center case, with the midpoint optimum
supplied by the Lemma 5 closed form.
-/
theorem paper_theorem3_typeFairness_mono_firstHalf_center_chain_of_closed_half
    {n : ℕ} [NeZero n]
    {v : Item n → ℝ} {c : Item n}
    (r : ℕ)
    (alphaSeq : ℕ → ℝ)
    (ρSeq : ℕ → TypePolicy 2 n)
    (ellSeq : ℕ → ℝ)
    (hn : 2 < n)
    (halpha0 : ∀ i, i ≤ r → 0 < alphaSeq i)
    (halpha1 : ∀ i, i ≤ r → alphaSeq i < 1)
    (halpha_half : ∀ i, i ≤ r → alphaSeq i ≤ 1 / 2)
    (hstep : ∀ i, i < r → alphaSeq i ≤ alphaSeq (i + 1))
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter_c : c.val = (reverseItem c).val)
    (hpivot_or_eq :
      ∀ i, i < r →
        TypePolicy.lastActiveTypeZero (ρSeq i) =
          TypePolicy.lastActiveTypeZero (ρSeq (i + 1)) ∨
        alphaSeq i = alphaSeq (i + 1))
    (hopt :
      ∀ i, i ≤ r →
        Problem6EqualizedBasicOptimal (alphaSeq i) v (ρSeq i) (ellSeq i)) :
    TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel (alphaSeq 0) v) (ρSeq 0) ≤
      TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel (alphaSeq r) v) (ρSeq r) := by
  exact theorem3_typeFairness_mono_firstHalf_center_chain_of_closed_half
    r alphaSeq ρSeq ellSeq hn halpha0 halpha1 halpha_half hstep hpos hdec
    hcenter_c hpivot_or_eq hopt

/--
Theorem 3 finite-stitch core, even-center case, with the midpoint optimum
supplied by the Lemma 5 closed form.
-/
theorem paper_theorem3_typeFairness_mono_firstHalf_succ_center_chain_of_closed_half
    {n : ℕ} [NeZero n]
    {v : Item n → ℝ} {c : Item n}
    (r : ℕ)
    (alphaSeq : ℕ → ℝ)
    (ρSeq : ℕ → TypePolicy 2 n)
    (ellSeq : ℕ → ℝ)
    (hn : 2 < n)
    (halpha0 : ∀ i, i ≤ r → 0 < alphaSeq i)
    (halpha1 : ∀ i, i ≤ r → alphaSeq i < 1)
    (halpha_half : ∀ i, i ≤ r → alphaSeq i ≤ 1 / 2)
    (hstep : ∀ i, i < r → alphaSeq i ≤ alphaSeq (i + 1))
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hsucc : c.val + 1 = (reverseItem c).val)
    (hpivot_or_eq :
      ∀ i, i < r →
        TypePolicy.lastActiveTypeZero (ρSeq i) =
          TypePolicy.lastActiveTypeZero (ρSeq (i + 1)) ∨
        alphaSeq i = alphaSeq (i + 1))
    (hopt :
      ∀ i, i ≤ r →
        Problem6EqualizedBasicOptimal (alphaSeq i) v (ρSeq i) (ellSeq i)) :
    TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel (alphaSeq 0) v) (ρSeq 0) ≤
      TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel (alphaSeq r) v) (ρSeq r) := by
  exact theorem3_typeFairness_mono_firstHalf_succ_center_chain_of_closed_half
    r alphaSeq ρSeq ellSeq hn halpha0 halpha1 halpha_half hstep hpos hdec
    hsucc hpivot_or_eq hopt

/--
Theorem 3 reduced-optimum bridge: along a first-half finite chain, if each
selected equality-form optimal BFS policy also upper-bounds all reduced
`γ = 1` feasible policies in type fairness, then `U^*_min(1, α)` is monotone.
-/
theorem paper_theorem3_optimalTypeFairnessAtLevel_one_mono_of_same_selected_or_equal_alpha_chain_of_upper_bound
    {n : ℕ} [NeZero n]
    {v : Item n → ℝ} (r : ℕ)
    (alphaSeq : ℕ → ℝ)
    (ρSeq : ℕ → TypePolicy 2 n)
    (ellSeq : ℕ → ℝ)
    (hn : 2 < n)
    (halpha0 : ∀ i, i ≤ r → 0 < alphaSeq i)
    (halpha1 : ∀ i, i ≤ r → alphaSeq i < 1)
    (halpha_half : ∀ i, i ≤ r → alphaSeq i ≤ 1 / 2)
    (hstep : ∀ i, i < r → alphaSeq i ≤ alphaSeq (i + 1))
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hpivot_or_eq :
      ∀ i, i < r →
        TypePolicy.lastActiveTypeZero (ρSeq i) =
          TypePolicy.lastActiveTypeZero (ρSeq (i + 1)) ∨
        alphaSeq i = alphaSeq (i + 1))
    (hcenter :
      ∀ i, i < r →
        (TypePolicy.lastActiveTypeZero (ρSeq i)).val ≤
          (reverseItem (TypePolicy.lastActiveTypeZero (ρSeq i))).val)
    (hopt :
      ∀ i, i ≤ r →
        Problem6EqualizedBasicOptimal (alphaSeq i) v (ρSeq i) (ellSeq i))
    (hupper :
      ∀ i, i ≤ r →
        ∀ ρ' : TypePolicy 2 n,
          TypeWeightedRecommendationModel.feasibleAtLevel
            (twoTypeReducedModel (alphaSeq i) v) 1 ρ' →
          TypeWeightedRecommendationModel.typeFairness
            (twoTypeReducedModel (alphaSeq i) v) ρ' ≤
          TypeWeightedRecommendationModel.typeFairness
            (twoTypeReducedModel (alphaSeq i) v) (ρSeq i)) :
    TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel (alphaSeq 0) v) 1 ≤
      TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel (alphaSeq r) v) 1 := by
  exact theorem3_optimalTypeFairnessAtLevel_one_mono_of_same_selected_or_equal_alpha_chain_of_upper_bound
    r alphaSeq ρSeq ellSeq hn halpha0 halpha1 halpha_half hstep hpos hdec
    hpivot_or_eq hcenter hopt hupper

/-- Theorem 3 reduced-optimum bridge, odd-center first-half chain. -/
theorem paper_theorem3_optimalTypeFairnessAtLevel_one_mono_firstHalf_center_chain_of_upper_bound
    {n : ℕ} [NeZero n]
    {v : Item n → ℝ} {c : Item n}
    (r : ℕ)
    (alphaSeq : ℕ → ℝ)
    (ρSeq : ℕ → TypePolicy 2 n)
    (ellSeq : ℕ → ℝ)
    {ρhalf : TypePolicy 2 n} {ellHalf : ℝ}
    (hn : 2 < n)
    (halpha0 : ∀ i, i ≤ r → 0 < alphaSeq i)
    (halpha1 : ∀ i, i ≤ r → alphaSeq i < 1)
    (halpha_half : ∀ i, i ≤ r → alphaSeq i ≤ 1 / 2)
    (hstep : ∀ i, i < r → alphaSeq i ≤ alphaSeq (i + 1))
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter_c : c.val = (reverseItem c).val)
    (hpivot_or_eq :
      ∀ i, i < r →
        TypePolicy.lastActiveTypeZero (ρSeq i) =
          TypePolicy.lastActiveTypeZero (ρSeq (i + 1)) ∨
        alphaSeq i = alphaSeq (i + 1))
    (hopt :
      ∀ i, i ≤ r →
        Problem6EqualizedBasicOptimal (alphaSeq i) v (ρSeq i) (ellSeq i))
    (hhalf :
      Problem6EqualizedBasicOptimal (1 / 2) v ρhalf ellHalf)
    (hupper :
      ∀ i, i ≤ r →
        ∀ ρ' : TypePolicy 2 n,
          TypeWeightedRecommendationModel.feasibleAtLevel
            (twoTypeReducedModel (alphaSeq i) v) 1 ρ' →
          TypeWeightedRecommendationModel.typeFairness
            (twoTypeReducedModel (alphaSeq i) v) ρ' ≤
          TypeWeightedRecommendationModel.typeFairness
            (twoTypeReducedModel (alphaSeq i) v) (ρSeq i)) :
    TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel (alphaSeq 0) v) 1 ≤
      TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel (alphaSeq r) v) 1 := by
  exact theorem3_optimalTypeFairnessAtLevel_one_mono_firstHalf_center_chain_of_upper_bound
    r alphaSeq ρSeq ellSeq hn halpha0 halpha1 halpha_half hstep hpos hdec
    hcenter_c hpivot_or_eq hopt hhalf hupper

/-- Theorem 3 reduced-optimum bridge, even-center first-half chain. -/
theorem paper_theorem3_optimalTypeFairnessAtLevel_one_mono_firstHalf_succ_center_chain_of_upper_bound
    {n : ℕ} [NeZero n]
    {v : Item n → ℝ} {c : Item n}
    (r : ℕ)
    (alphaSeq : ℕ → ℝ)
    (ρSeq : ℕ → TypePolicy 2 n)
    (ellSeq : ℕ → ℝ)
    {ρhalf : TypePolicy 2 n} {ellHalf : ℝ}
    (hn : 2 < n)
    (halpha0 : ∀ i, i ≤ r → 0 < alphaSeq i)
    (halpha1 : ∀ i, i ≤ r → alphaSeq i < 1)
    (halpha_half : ∀ i, i ≤ r → alphaSeq i ≤ 1 / 2)
    (hstep : ∀ i, i < r → alphaSeq i ≤ alphaSeq (i + 1))
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hsucc : c.val + 1 = (reverseItem c).val)
    (hpivot_or_eq :
      ∀ i, i < r →
        TypePolicy.lastActiveTypeZero (ρSeq i) =
          TypePolicy.lastActiveTypeZero (ρSeq (i + 1)) ∨
        alphaSeq i = alphaSeq (i + 1))
    (hopt :
      ∀ i, i ≤ r →
        Problem6EqualizedBasicOptimal (alphaSeq i) v (ρSeq i) (ellSeq i))
    (hhalf :
      Problem6EqualizedBasicOptimal (1 / 2) v ρhalf ellHalf)
    (hupper :
      ∀ i, i ≤ r →
        ∀ ρ' : TypePolicy 2 n,
          TypeWeightedRecommendationModel.feasibleAtLevel
            (twoTypeReducedModel (alphaSeq i) v) 1 ρ' →
          TypeWeightedRecommendationModel.typeFairness
            (twoTypeReducedModel (alphaSeq i) v) ρ' ≤
          TypeWeightedRecommendationModel.typeFairness
            (twoTypeReducedModel (alphaSeq i) v) (ρSeq i)) :
    TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel (alphaSeq 0) v) 1 ≤
      TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel (alphaSeq r) v) 1 := by
  exact theorem3_optimalTypeFairnessAtLevel_one_mono_firstHalf_succ_center_chain_of_upper_bound
    r alphaSeq ρSeq ellSeq hn halpha0 halpha1 halpha_half hstep hpos hdec
    hsucc hpivot_or_eq hopt hhalf hupper

/--
Theorem 3 reduced-optimum bridge, odd-center first-half chain, with the
midpoint optimum supplied by the Lemma 5 closed form.
-/
theorem paper_theorem3_optimalTypeFairnessAtLevel_one_mono_firstHalf_center_chain_of_upper_bound_closed_half
    {n : ℕ} [NeZero n]
    {v : Item n → ℝ} {c : Item n}
    (r : ℕ)
    (alphaSeq : ℕ → ℝ)
    (ρSeq : ℕ → TypePolicy 2 n)
    (ellSeq : ℕ → ℝ)
    (hn : 2 < n)
    (halpha0 : ∀ i, i ≤ r → 0 < alphaSeq i)
    (halpha1 : ∀ i, i ≤ r → alphaSeq i < 1)
    (halpha_half : ∀ i, i ≤ r → alphaSeq i ≤ 1 / 2)
    (hstep : ∀ i, i < r → alphaSeq i ≤ alphaSeq (i + 1))
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter_c : c.val = (reverseItem c).val)
    (hpivot_or_eq :
      ∀ i, i < r →
        TypePolicy.lastActiveTypeZero (ρSeq i) =
          TypePolicy.lastActiveTypeZero (ρSeq (i + 1)) ∨
        alphaSeq i = alphaSeq (i + 1))
    (hopt :
      ∀ i, i ≤ r →
        Problem6EqualizedBasicOptimal (alphaSeq i) v (ρSeq i) (ellSeq i))
    (hupper :
      ∀ i, i ≤ r →
        ∀ ρ' : TypePolicy 2 n,
          TypeWeightedRecommendationModel.feasibleAtLevel
            (twoTypeReducedModel (alphaSeq i) v) 1 ρ' →
          TypeWeightedRecommendationModel.typeFairness
            (twoTypeReducedModel (alphaSeq i) v) ρ' ≤
          TypeWeightedRecommendationModel.typeFairness
            (twoTypeReducedModel (alphaSeq i) v) (ρSeq i)) :
    TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel (alphaSeq 0) v) 1 ≤
      TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel (alphaSeq r) v) 1 := by
  exact theorem3_optimalTypeFairnessAtLevel_one_mono_firstHalf_center_chain_of_upper_bound_closed_half
    r alphaSeq ρSeq ellSeq hn halpha0 halpha1 halpha_half hstep hpos hdec
    hcenter_c hpivot_or_eq hopt hupper

/--
Theorem 3 reduced-optimum bridge, even-center first-half chain, with the
midpoint optimum supplied by the Lemma 5 closed form.
-/
theorem paper_theorem3_optimalTypeFairnessAtLevel_one_mono_firstHalf_succ_center_chain_of_upper_bound_closed_half
    {n : ℕ} [NeZero n]
    {v : Item n → ℝ} {c : Item n}
    (r : ℕ)
    (alphaSeq : ℕ → ℝ)
    (ρSeq : ℕ → TypePolicy 2 n)
    (ellSeq : ℕ → ℝ)
    (hn : 2 < n)
    (halpha0 : ∀ i, i ≤ r → 0 < alphaSeq i)
    (halpha1 : ∀ i, i ≤ r → alphaSeq i < 1)
    (halpha_half : ∀ i, i ≤ r → alphaSeq i ≤ 1 / 2)
    (hstep : ∀ i, i < r → alphaSeq i ≤ alphaSeq (i + 1))
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hsucc : c.val + 1 = (reverseItem c).val)
    (hpivot_or_eq :
      ∀ i, i < r →
        TypePolicy.lastActiveTypeZero (ρSeq i) =
          TypePolicy.lastActiveTypeZero (ρSeq (i + 1)) ∨
        alphaSeq i = alphaSeq (i + 1))
    (hopt :
      ∀ i, i ≤ r →
        Problem6EqualizedBasicOptimal (alphaSeq i) v (ρSeq i) (ellSeq i))
    (hupper :
      ∀ i, i ≤ r →
        ∀ ρ' : TypePolicy 2 n,
          TypeWeightedRecommendationModel.feasibleAtLevel
            (twoTypeReducedModel (alphaSeq i) v) 1 ρ' →
          TypeWeightedRecommendationModel.typeFairness
            (twoTypeReducedModel (alphaSeq i) v) ρ' ≤
          TypeWeightedRecommendationModel.typeFairness
            (twoTypeReducedModel (alphaSeq i) v) (ρSeq i)) :
    TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel (alphaSeq 0) v) 1 ≤
      TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel (alphaSeq r) v) 1 := by
  exact theorem3_optimalTypeFairnessAtLevel_one_mono_firstHalf_succ_center_chain_of_upper_bound_closed_half
    r alphaSeq ρSeq ellSeq hn halpha0 halpha1 halpha_half hstep hpos hdec
    hsucc hpivot_or_eq hopt hupper

/--
Theorem 3 reduced-optimum bridge with the Proposition-1-shaped
canonicalization assumption: along a first-half finite chain, canonical
equalized/shared representatives identify each selected policy with
`U^*_min(1, α)`, so the reduced type-fairness optimum is monotone.
-/
theorem paper_theorem3_optimalTypeFairnessAtLevel_one_mono_of_same_selected_or_equal_alpha_chain_of_feasible_canonicalization
    {n : ℕ} [NeZero n]
    {v : Item n → ℝ} (r : ℕ)
    (alphaSeq : ℕ → ℝ)
    (ρSeq : ℕ → TypePolicy 2 n)
    (ellSeq : ℕ → ℝ)
    (hn : 2 < n)
    (halpha0 : ∀ i, i ≤ r → 0 < alphaSeq i)
    (halpha1 : ∀ i, i ≤ r → alphaSeq i < 1)
    (halpha_half : ∀ i, i ≤ r → alphaSeq i ≤ 1 / 2)
    (hstep : ∀ i, i < r → alphaSeq i ≤ alphaSeq (i + 1))
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hpivot_or_eq :
      ∀ i, i < r →
        TypePolicy.lastActiveTypeZero (ρSeq i) =
          TypePolicy.lastActiveTypeZero (ρSeq (i + 1)) ∨
        alphaSeq i = alphaSeq (i + 1))
    (hcenter :
      ∀ i, i < r →
        (TypePolicy.lastActiveTypeZero (ρSeq i)).val ≤
          (reverseItem (TypePolicy.lastActiveTypeZero (ρSeq i))).val)
    (hopt :
      ∀ i, i ≤ r →
        Problem6EqualizedBasicOptimal (alphaSeq i) v (ρSeq i) (ellSeq i))
    (hcanonical :
      ∀ i, i ≤ r →
        ∀ ρ' : TypePolicy 2 n,
          TypeWeightedRecommendationModel.feasibleAtLevel
            (twoTypeReducedModel (alphaSeq i) v) 1 ρ' →
          ∃ ρbar : TypePolicy 2 n,
            TypeWeightedRecommendationModel.feasibleAtLevel
              (twoTypeReducedModel (alphaSeq i) v) 1 ρbar ∧
            (∀ l : Item n,
              pairShare (alphaSeq i) v l * (ρbar 0 l).toReal +
                (1 - pairShare (alphaSeq i) v l) * (ρbar 1 l).toReal =
              TypeWeightedRecommendationModel.itemFairness
                (twoTypeReducedModel (alphaSeq i) v) ρbar) ∧
            TypePolicy.SharedItemsBound ρbar ∧
            TypeWeightedRecommendationModel.typeFairness
              (twoTypeReducedModel (alphaSeq i) v) ρ' ≤
            TypeWeightedRecommendationModel.typeFairness
              (twoTypeReducedModel (alphaSeq i) v) ρbar) :
    TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel (alphaSeq 0) v) 1 ≤
      TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel (alphaSeq r) v) 1 := by
  exact theorem3_optimalTypeFairnessAtLevel_one_mono_of_same_selected_or_equal_alpha_chain_of_feasible_canonicalization
    r alphaSeq ρSeq ellSeq hn halpha0 halpha1 halpha_half hstep hpos hdec
    hpivot_or_eq hcenter hopt hcanonical

/--
Theorem 3 reduced-optimum bridge, odd-center first-half chain, with
Proposition-1-shaped canonicalization of reduced `γ = 1` feasible policies.
-/
theorem paper_theorem3_optimalTypeFairnessAtLevel_one_mono_firstHalf_center_chain_of_feasible_canonicalization
    {n : ℕ} [NeZero n]
    {v : Item n → ℝ} {c : Item n}
    (r : ℕ)
    (alphaSeq : ℕ → ℝ)
    (ρSeq : ℕ → TypePolicy 2 n)
    (ellSeq : ℕ → ℝ)
    {ρhalf : TypePolicy 2 n} {ellHalf : ℝ}
    (hn : 2 < n)
    (halpha0 : ∀ i, i ≤ r → 0 < alphaSeq i)
    (halpha1 : ∀ i, i ≤ r → alphaSeq i < 1)
    (halpha_half : ∀ i, i ≤ r → alphaSeq i ≤ 1 / 2)
    (hstep : ∀ i, i < r → alphaSeq i ≤ alphaSeq (i + 1))
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter_c : c.val = (reverseItem c).val)
    (hpivot_or_eq :
      ∀ i, i < r →
        TypePolicy.lastActiveTypeZero (ρSeq i) =
          TypePolicy.lastActiveTypeZero (ρSeq (i + 1)) ∨
        alphaSeq i = alphaSeq (i + 1))
    (hopt :
      ∀ i, i ≤ r →
        Problem6EqualizedBasicOptimal (alphaSeq i) v (ρSeq i) (ellSeq i))
    (hhalf :
      Problem6EqualizedBasicOptimal (1 / 2) v ρhalf ellHalf)
    (hcanonical :
      ∀ i, i ≤ r →
        ∀ ρ' : TypePolicy 2 n,
          TypeWeightedRecommendationModel.feasibleAtLevel
            (twoTypeReducedModel (alphaSeq i) v) 1 ρ' →
          ∃ ρbar : TypePolicy 2 n,
            TypeWeightedRecommendationModel.feasibleAtLevel
              (twoTypeReducedModel (alphaSeq i) v) 1 ρbar ∧
            (∀ l : Item n,
              pairShare (alphaSeq i) v l * (ρbar 0 l).toReal +
                (1 - pairShare (alphaSeq i) v l) * (ρbar 1 l).toReal =
              TypeWeightedRecommendationModel.itemFairness
                (twoTypeReducedModel (alphaSeq i) v) ρbar) ∧
            TypePolicy.SharedItemsBound ρbar ∧
            TypeWeightedRecommendationModel.typeFairness
              (twoTypeReducedModel (alphaSeq i) v) ρ' ≤
            TypeWeightedRecommendationModel.typeFairness
              (twoTypeReducedModel (alphaSeq i) v) ρbar) :
    TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel (alphaSeq 0) v) 1 ≤
      TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel (alphaSeq r) v) 1 := by
  exact theorem3_optimalTypeFairnessAtLevel_one_mono_firstHalf_center_chain_of_feasible_canonicalization
    r alphaSeq ρSeq ellSeq hn halpha0 halpha1 halpha_half hstep hpos hdec
    hcenter_c hpivot_or_eq hopt hhalf hcanonical

/--
Theorem 3 reduced-optimum bridge, even-center first-half chain, with
Proposition-1-shaped canonicalization of reduced `γ = 1` feasible policies.
-/
theorem paper_theorem3_optimalTypeFairnessAtLevel_one_mono_firstHalf_succ_center_chain_of_feasible_canonicalization
    {n : ℕ} [NeZero n]
    {v : Item n → ℝ} {c : Item n}
    (r : ℕ)
    (alphaSeq : ℕ → ℝ)
    (ρSeq : ℕ → TypePolicy 2 n)
    (ellSeq : ℕ → ℝ)
    {ρhalf : TypePolicy 2 n} {ellHalf : ℝ}
    (hn : 2 < n)
    (halpha0 : ∀ i, i ≤ r → 0 < alphaSeq i)
    (halpha1 : ∀ i, i ≤ r → alphaSeq i < 1)
    (halpha_half : ∀ i, i ≤ r → alphaSeq i ≤ 1 / 2)
    (hstep : ∀ i, i < r → alphaSeq i ≤ alphaSeq (i + 1))
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hsucc : c.val + 1 = (reverseItem c).val)
    (hpivot_or_eq :
      ∀ i, i < r →
        TypePolicy.lastActiveTypeZero (ρSeq i) =
          TypePolicy.lastActiveTypeZero (ρSeq (i + 1)) ∨
        alphaSeq i = alphaSeq (i + 1))
    (hopt :
      ∀ i, i ≤ r →
        Problem6EqualizedBasicOptimal (alphaSeq i) v (ρSeq i) (ellSeq i))
    (hhalf :
      Problem6EqualizedBasicOptimal (1 / 2) v ρhalf ellHalf)
    (hcanonical :
      ∀ i, i ≤ r →
        ∀ ρ' : TypePolicy 2 n,
          TypeWeightedRecommendationModel.feasibleAtLevel
            (twoTypeReducedModel (alphaSeq i) v) 1 ρ' →
          ∃ ρbar : TypePolicy 2 n,
            TypeWeightedRecommendationModel.feasibleAtLevel
              (twoTypeReducedModel (alphaSeq i) v) 1 ρbar ∧
            (∀ l : Item n,
              pairShare (alphaSeq i) v l * (ρbar 0 l).toReal +
                (1 - pairShare (alphaSeq i) v l) * (ρbar 1 l).toReal =
              TypeWeightedRecommendationModel.itemFairness
                (twoTypeReducedModel (alphaSeq i) v) ρbar) ∧
            TypePolicy.SharedItemsBound ρbar ∧
            TypeWeightedRecommendationModel.typeFairness
              (twoTypeReducedModel (alphaSeq i) v) ρ' ≤
            TypeWeightedRecommendationModel.typeFairness
              (twoTypeReducedModel (alphaSeq i) v) ρbar) :
    TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel (alphaSeq 0) v) 1 ≤
      TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel (alphaSeq r) v) 1 := by
  exact theorem3_optimalTypeFairnessAtLevel_one_mono_firstHalf_succ_center_chain_of_feasible_canonicalization
    r alphaSeq ρSeq ellSeq hn halpha0 halpha1 halpha_half hstep hpos hdec
    hsucc hpivot_or_eq hopt hhalf hcanonical

/--
Theorem 3 reduced-optimum bridge, odd-center first-half chain, with
Proposition-1-shaped canonicalization and the Lemma 5 closed midpoint optimum.
-/
theorem paper_theorem3_optimalTypeFairnessAtLevel_one_mono_firstHalf_center_chain_of_feasible_canonicalization_closed_half
    {n : ℕ} [NeZero n]
    {v : Item n → ℝ} {c : Item n}
    (r : ℕ)
    (alphaSeq : ℕ → ℝ)
    (ρSeq : ℕ → TypePolicy 2 n)
    (ellSeq : ℕ → ℝ)
    (hn : 2 < n)
    (halpha0 : ∀ i, i ≤ r → 0 < alphaSeq i)
    (halpha1 : ∀ i, i ≤ r → alphaSeq i < 1)
    (halpha_half : ∀ i, i ≤ r → alphaSeq i ≤ 1 / 2)
    (hstep : ∀ i, i < r → alphaSeq i ≤ alphaSeq (i + 1))
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter_c : c.val = (reverseItem c).val)
    (hpivot_or_eq :
      ∀ i, i < r →
        TypePolicy.lastActiveTypeZero (ρSeq i) =
          TypePolicy.lastActiveTypeZero (ρSeq (i + 1)) ∨
        alphaSeq i = alphaSeq (i + 1))
    (hopt :
      ∀ i, i ≤ r →
        Problem6EqualizedBasicOptimal (alphaSeq i) v (ρSeq i) (ellSeq i))
    (hcanonical :
      ∀ i, i ≤ r →
        ∀ ρ' : TypePolicy 2 n,
          TypeWeightedRecommendationModel.feasibleAtLevel
            (twoTypeReducedModel (alphaSeq i) v) 1 ρ' →
          ∃ ρbar : TypePolicy 2 n,
            TypeWeightedRecommendationModel.feasibleAtLevel
              (twoTypeReducedModel (alphaSeq i) v) 1 ρbar ∧
            (∀ l : Item n,
              pairShare (alphaSeq i) v l * (ρbar 0 l).toReal +
                (1 - pairShare (alphaSeq i) v l) * (ρbar 1 l).toReal =
              TypeWeightedRecommendationModel.itemFairness
                (twoTypeReducedModel (alphaSeq i) v) ρbar) ∧
            TypePolicy.SharedItemsBound ρbar ∧
            TypeWeightedRecommendationModel.typeFairness
              (twoTypeReducedModel (alphaSeq i) v) ρ' ≤
            TypeWeightedRecommendationModel.typeFairness
              (twoTypeReducedModel (alphaSeq i) v) ρbar) :
    TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel (alphaSeq 0) v) 1 ≤
      TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel (alphaSeq r) v) 1 := by
  exact theorem3_optimalTypeFairnessAtLevel_one_mono_firstHalf_center_chain_of_feasible_canonicalization_closed_half
    r alphaSeq ρSeq ellSeq hn halpha0 halpha1 halpha_half hstep hpos hdec
    hcenter_c hpivot_or_eq hopt hcanonical

/--
Theorem 3 reduced-optimum bridge, even-center first-half chain, with
Proposition-1-shaped canonicalization and the Lemma 5 closed midpoint optimum.
-/
theorem paper_theorem3_optimalTypeFairnessAtLevel_one_mono_firstHalf_succ_center_chain_of_feasible_canonicalization_closed_half
    {n : ℕ} [NeZero n]
    {v : Item n → ℝ} {c : Item n}
    (r : ℕ)
    (alphaSeq : ℕ → ℝ)
    (ρSeq : ℕ → TypePolicy 2 n)
    (ellSeq : ℕ → ℝ)
    (hn : 2 < n)
    (halpha0 : ∀ i, i ≤ r → 0 < alphaSeq i)
    (halpha1 : ∀ i, i ≤ r → alphaSeq i < 1)
    (halpha_half : ∀ i, i ≤ r → alphaSeq i ≤ 1 / 2)
    (hstep : ∀ i, i < r → alphaSeq i ≤ alphaSeq (i + 1))
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hsucc : c.val + 1 = (reverseItem c).val)
    (hpivot_or_eq :
      ∀ i, i < r →
        TypePolicy.lastActiveTypeZero (ρSeq i) =
          TypePolicy.lastActiveTypeZero (ρSeq (i + 1)) ∨
        alphaSeq i = alphaSeq (i + 1))
    (hopt :
      ∀ i, i ≤ r →
        Problem6EqualizedBasicOptimal (alphaSeq i) v (ρSeq i) (ellSeq i))
    (hcanonical :
      ∀ i, i ≤ r →
        ∀ ρ' : TypePolicy 2 n,
          TypeWeightedRecommendationModel.feasibleAtLevel
            (twoTypeReducedModel (alphaSeq i) v) 1 ρ' →
          ∃ ρbar : TypePolicy 2 n,
            TypeWeightedRecommendationModel.feasibleAtLevel
              (twoTypeReducedModel (alphaSeq i) v) 1 ρbar ∧
            (∀ l : Item n,
              pairShare (alphaSeq i) v l * (ρbar 0 l).toReal +
                (1 - pairShare (alphaSeq i) v l) * (ρbar 1 l).toReal =
              TypeWeightedRecommendationModel.itemFairness
                (twoTypeReducedModel (alphaSeq i) v) ρbar) ∧
            TypePolicy.SharedItemsBound ρbar ∧
            TypeWeightedRecommendationModel.typeFairness
              (twoTypeReducedModel (alphaSeq i) v) ρ' ≤
            TypeWeightedRecommendationModel.typeFairness
              (twoTypeReducedModel (alphaSeq i) v) ρbar) :
    TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel (alphaSeq 0) v) 1 ≤
      TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel (alphaSeq r) v) 1 := by
  exact theorem3_optimalTypeFairnessAtLevel_one_mono_firstHalf_succ_center_chain_of_feasible_canonicalization_closed_half
    r alphaSeq ρSeq ellSeq hn halpha0 halpha1 halpha_half hstep hpos hdec
    hsucc hpivot_or_eq hopt hcanonical

/--
Theorem 3 reduced-optimum bridge in LP-selection form: along a first-half
finite chain, dominating equality-form optimal BFS representatives identify
the reduced `γ = 1` type-fairness optimum and yield monotonicity.
-/
theorem paper_theorem3_optimalTypeFairnessAtLevel_one_mono_of_same_selected_or_equal_alpha_chain_of_equalizedBasicOptimal_dominance
    {n : ℕ} [NeZero n]
    {v : Item n → ℝ} (r : ℕ)
    (alphaSeq : ℕ → ℝ)
    (ρSeq : ℕ → TypePolicy 2 n)
    (ellSeq : ℕ → ℝ)
    (hn : 2 < n)
    (halpha0 : ∀ i, i ≤ r → 0 < alphaSeq i)
    (halpha1 : ∀ i, i ≤ r → alphaSeq i < 1)
    (halpha_half : ∀ i, i ≤ r → alphaSeq i ≤ 1 / 2)
    (hstep : ∀ i, i < r → alphaSeq i ≤ alphaSeq (i + 1))
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hpivot_or_eq :
      ∀ i, i < r →
        TypePolicy.lastActiveTypeZero (ρSeq i) =
          TypePolicy.lastActiveTypeZero (ρSeq (i + 1)) ∨
        alphaSeq i = alphaSeq (i + 1))
    (hcenter :
      ∀ i, i < r →
        (TypePolicy.lastActiveTypeZero (ρSeq i)).val ≤
          (reverseItem (TypePolicy.lastActiveTypeZero (ρSeq i))).val)
    (hopt :
      ∀ i, i ≤ r →
        Problem6EqualizedBasicOptimal (alphaSeq i) v (ρSeq i) (ellSeq i))
    (hdom :
      ∀ i, i ≤ r →
        ∀ ρ' : TypePolicy 2 n,
          TypeWeightedRecommendationModel.feasibleAtLevel
            (twoTypeReducedModel (alphaSeq i) v) 1 ρ' →
        ∃ (ρbar : TypePolicy 2 n) (ellbar : ℝ),
          Problem6EqualizedBasicOptimal (alphaSeq i) v ρbar ellbar ∧
          TypeWeightedRecommendationModel.typeFairness
            (twoTypeReducedModel (alphaSeq i) v) ρ' ≤
          TypeWeightedRecommendationModel.typeFairness
            (twoTypeReducedModel (alphaSeq i) v) ρbar) :
    TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel (alphaSeq 0) v) 1 ≤
      TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel (alphaSeq r) v) 1 := by
  exact theorem3_optimalTypeFairnessAtLevel_one_mono_of_same_selected_or_equal_alpha_chain_of_equalizedBasicOptimal_dominance
    r alphaSeq ρSeq ellSeq hn halpha0 halpha1 halpha_half hstep hpos hdec
    hpivot_or_eq hcenter hopt hdom

/--
Theorem 3 reduced-optimum bridge, odd-center first-half chain, in the
LP-selection dominance form.
-/
theorem paper_theorem3_optimalTypeFairnessAtLevel_one_mono_firstHalf_center_chain_of_equalizedBasicOptimal_dominance
    {n : ℕ} [NeZero n]
    {v : Item n → ℝ} {c : Item n}
    (r : ℕ)
    (alphaSeq : ℕ → ℝ)
    (ρSeq : ℕ → TypePolicy 2 n)
    (ellSeq : ℕ → ℝ)
    {ρhalf : TypePolicy 2 n} {ellHalf : ℝ}
    (hn : 2 < n)
    (halpha0 : ∀ i, i ≤ r → 0 < alphaSeq i)
    (halpha1 : ∀ i, i ≤ r → alphaSeq i < 1)
    (halpha_half : ∀ i, i ≤ r → alphaSeq i ≤ 1 / 2)
    (hstep : ∀ i, i < r → alphaSeq i ≤ alphaSeq (i + 1))
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter_c : c.val = (reverseItem c).val)
    (hpivot_or_eq :
      ∀ i, i < r →
        TypePolicy.lastActiveTypeZero (ρSeq i) =
          TypePolicy.lastActiveTypeZero (ρSeq (i + 1)) ∨
        alphaSeq i = alphaSeq (i + 1))
    (hopt :
      ∀ i, i ≤ r →
        Problem6EqualizedBasicOptimal (alphaSeq i) v (ρSeq i) (ellSeq i))
    (hhalf :
      Problem6EqualizedBasicOptimal (1 / 2) v ρhalf ellHalf)
    (hdom :
      ∀ i, i ≤ r →
        ∀ ρ' : TypePolicy 2 n,
          TypeWeightedRecommendationModel.feasibleAtLevel
            (twoTypeReducedModel (alphaSeq i) v) 1 ρ' →
        ∃ (ρbar : TypePolicy 2 n) (ellbar : ℝ),
          Problem6EqualizedBasicOptimal (alphaSeq i) v ρbar ellbar ∧
          TypeWeightedRecommendationModel.typeFairness
            (twoTypeReducedModel (alphaSeq i) v) ρ' ≤
          TypeWeightedRecommendationModel.typeFairness
            (twoTypeReducedModel (alphaSeq i) v) ρbar) :
    TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel (alphaSeq 0) v) 1 ≤
      TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel (alphaSeq r) v) 1 := by
  exact theorem3_optimalTypeFairnessAtLevel_one_mono_firstHalf_center_chain_of_equalizedBasicOptimal_dominance
    r alphaSeq ρSeq ellSeq hn halpha0 halpha1 halpha_half hstep hpos hdec
    hcenter_c hpivot_or_eq hopt hhalf hdom

/--
Theorem 3 reduced-optimum bridge, even-center first-half chain, in the
LP-selection dominance form.
-/
theorem paper_theorem3_optimalTypeFairnessAtLevel_one_mono_firstHalf_succ_center_chain_of_equalizedBasicOptimal_dominance
    {n : ℕ} [NeZero n]
    {v : Item n → ℝ} {c : Item n}
    (r : ℕ)
    (alphaSeq : ℕ → ℝ)
    (ρSeq : ℕ → TypePolicy 2 n)
    (ellSeq : ℕ → ℝ)
    {ρhalf : TypePolicy 2 n} {ellHalf : ℝ}
    (hn : 2 < n)
    (halpha0 : ∀ i, i ≤ r → 0 < alphaSeq i)
    (halpha1 : ∀ i, i ≤ r → alphaSeq i < 1)
    (halpha_half : ∀ i, i ≤ r → alphaSeq i ≤ 1 / 2)
    (hstep : ∀ i, i < r → alphaSeq i ≤ alphaSeq (i + 1))
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hsucc : c.val + 1 = (reverseItem c).val)
    (hpivot_or_eq :
      ∀ i, i < r →
        TypePolicy.lastActiveTypeZero (ρSeq i) =
          TypePolicy.lastActiveTypeZero (ρSeq (i + 1)) ∨
        alphaSeq i = alphaSeq (i + 1))
    (hopt :
      ∀ i, i ≤ r →
        Problem6EqualizedBasicOptimal (alphaSeq i) v (ρSeq i) (ellSeq i))
    (hhalf :
      Problem6EqualizedBasicOptimal (1 / 2) v ρhalf ellHalf)
    (hdom :
      ∀ i, i ≤ r →
        ∀ ρ' : TypePolicy 2 n,
          TypeWeightedRecommendationModel.feasibleAtLevel
            (twoTypeReducedModel (alphaSeq i) v) 1 ρ' →
        ∃ (ρbar : TypePolicy 2 n) (ellbar : ℝ),
          Problem6EqualizedBasicOptimal (alphaSeq i) v ρbar ellbar ∧
          TypeWeightedRecommendationModel.typeFairness
            (twoTypeReducedModel (alphaSeq i) v) ρ' ≤
          TypeWeightedRecommendationModel.typeFairness
            (twoTypeReducedModel (alphaSeq i) v) ρbar) :
    TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel (alphaSeq 0) v) 1 ≤
      TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel (alphaSeq r) v) 1 := by
  exact theorem3_optimalTypeFairnessAtLevel_one_mono_firstHalf_succ_center_chain_of_equalizedBasicOptimal_dominance
    r alphaSeq ρSeq ellSeq hn halpha0 halpha1 halpha_half hstep hpos hdec
    hsucc hpivot_or_eq hopt hhalf hdom

/--
Theorem 3 reduced-optimum bridge, odd-center first-half chain, in the
LP-selection dominance form, with the Lemma 5 closed midpoint optimum.
-/
theorem paper_theorem3_optimalTypeFairnessAtLevel_one_mono_firstHalf_center_chain_of_equalizedBasicOptimal_dominance_closed_half
    {n : ℕ} [NeZero n]
    {v : Item n → ℝ} {c : Item n}
    (r : ℕ)
    (alphaSeq : ℕ → ℝ)
    (ρSeq : ℕ → TypePolicy 2 n)
    (ellSeq : ℕ → ℝ)
    (hn : 2 < n)
    (halpha0 : ∀ i, i ≤ r → 0 < alphaSeq i)
    (halpha1 : ∀ i, i ≤ r → alphaSeq i < 1)
    (halpha_half : ∀ i, i ≤ r → alphaSeq i ≤ 1 / 2)
    (hstep : ∀ i, i < r → alphaSeq i ≤ alphaSeq (i + 1))
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter_c : c.val = (reverseItem c).val)
    (hpivot_or_eq :
      ∀ i, i < r →
        TypePolicy.lastActiveTypeZero (ρSeq i) =
          TypePolicy.lastActiveTypeZero (ρSeq (i + 1)) ∨
        alphaSeq i = alphaSeq (i + 1))
    (hopt :
      ∀ i, i ≤ r →
        Problem6EqualizedBasicOptimal (alphaSeq i) v (ρSeq i) (ellSeq i))
    (hdom :
      ∀ i, i ≤ r →
        ∀ ρ' : TypePolicy 2 n,
          TypeWeightedRecommendationModel.feasibleAtLevel
            (twoTypeReducedModel (alphaSeq i) v) 1 ρ' →
        ∃ (ρbar : TypePolicy 2 n) (ellbar : ℝ),
          Problem6EqualizedBasicOptimal (alphaSeq i) v ρbar ellbar ∧
          TypeWeightedRecommendationModel.typeFairness
            (twoTypeReducedModel (alphaSeq i) v) ρ' ≤
          TypeWeightedRecommendationModel.typeFairness
            (twoTypeReducedModel (alphaSeq i) v) ρbar) :
    TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel (alphaSeq 0) v) 1 ≤
      TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel (alphaSeq r) v) 1 := by
  exact theorem3_optimalTypeFairnessAtLevel_one_mono_firstHalf_center_chain_of_equalizedBasicOptimal_dominance_closed_half
    r alphaSeq ρSeq ellSeq hn halpha0 halpha1 halpha_half hstep hpos hdec
    hcenter_c hpivot_or_eq hopt hdom

/--
Theorem 3 reduced-optimum bridge, even-center first-half chain, in the
LP-selection dominance form, with the Lemma 5 closed midpoint optimum.
-/
theorem paper_theorem3_optimalTypeFairnessAtLevel_one_mono_firstHalf_succ_center_chain_of_equalizedBasicOptimal_dominance_closed_half
    {n : ℕ} [NeZero n]
    {v : Item n → ℝ} {c : Item n}
    (r : ℕ)
    (alphaSeq : ℕ → ℝ)
    (ρSeq : ℕ → TypePolicy 2 n)
    (ellSeq : ℕ → ℝ)
    (hn : 2 < n)
    (halpha0 : ∀ i, i ≤ r → 0 < alphaSeq i)
    (halpha1 : ∀ i, i ≤ r → alphaSeq i < 1)
    (halpha_half : ∀ i, i ≤ r → alphaSeq i ≤ 1 / 2)
    (hstep : ∀ i, i < r → alphaSeq i ≤ alphaSeq (i + 1))
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hsucc : c.val + 1 = (reverseItem c).val)
    (hpivot_or_eq :
      ∀ i, i < r →
        TypePolicy.lastActiveTypeZero (ρSeq i) =
          TypePolicy.lastActiveTypeZero (ρSeq (i + 1)) ∨
        alphaSeq i = alphaSeq (i + 1))
    (hopt :
      ∀ i, i ≤ r →
        Problem6EqualizedBasicOptimal (alphaSeq i) v (ρSeq i) (ellSeq i))
    (hdom :
      ∀ i, i ≤ r →
        ∀ ρ' : TypePolicy 2 n,
          TypeWeightedRecommendationModel.feasibleAtLevel
            (twoTypeReducedModel (alphaSeq i) v) 1 ρ' →
        ∃ (ρbar : TypePolicy 2 n) (ellbar : ℝ),
          Problem6EqualizedBasicOptimal (alphaSeq i) v ρbar ellbar ∧
          TypeWeightedRecommendationModel.typeFairness
            (twoTypeReducedModel (alphaSeq i) v) ρ' ≤
          TypeWeightedRecommendationModel.typeFairness
            (twoTypeReducedModel (alphaSeq i) v) ρbar) :
    TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel (alphaSeq 0) v) 1 ≤
      TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel (alphaSeq r) v) 1 := by
  exact theorem3_optimalTypeFairnessAtLevel_one_mono_firstHalf_succ_center_chain_of_equalizedBasicOptimal_dominance_closed_half
    r alphaSeq ρSeq ellSeq hn halpha0 halpha1 halpha_half hstep hpos hdec
    hsucc hpivot_or_eq hopt hdom

/--
Theorem 3 canonical closed-policy first-half monotonicity, odd-center case:
after the Appendix D Lemma 8 no-skip stitch, the closed Problem 6 solution's
type fairness is monotone for any `α ≤ α' ≤ 1/2`.
-/
theorem paper_theorem3_typeFairness_mono_firstHalf_center_of_alpha_le
    {n : ℕ} [NeZero n]
    {alpha alpha' : ℝ} {v : Item n → ℝ} {c : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (halpha_half : alpha ≤ 1 / 2)
    (halpha_half' : alpha' ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter_c : c.val = (reverseItem c).val) :
    TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel alpha v)
        (problem6FirstClosedPolicy alpha v halpha0 halpha1 hpos) ≤
      TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel alpha' v)
        (problem6FirstClosedPolicy alpha' v halpha0' halpha1' hpos) := by
  exact
    theorem3_typeFairness_mono_firstHalf_center_of_alpha_le
      halpha0 halpha1 halpha0' halpha1' halpha_le
      halpha_half halpha_half' hpos hdec hcenter_c

/--
Theorem 3 canonical closed-policy first-half monotonicity, even-center case.
-/
theorem paper_theorem3_typeFairness_mono_firstHalf_succ_center_of_alpha_le
    {n : ℕ} [NeZero n]
    {alpha alpha' : ℝ} {v : Item n → ℝ} {c : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (halpha_half : alpha ≤ 1 / 2)
    (halpha_half' : alpha' ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hsucc : c.val + 1 = (reverseItem c).val) :
    TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel alpha v)
        (problem6FirstClosedPolicy alpha v halpha0 halpha1 hpos) ≤
      TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel alpha' v)
        (problem6FirstClosedPolicy alpha' v halpha0' halpha1' hpos) := by
  exact
    theorem3_typeFairness_mono_firstHalf_succ_center_of_alpha_le
      halpha0 halpha1 halpha0' halpha1' halpha_le
      halpha_half halpha_half' hpos hdec hsucc

/--
Problem 6 canonical closed-policy optimality bridge: under the
Proposition-1-shaped feasible-policy canonicalization assumption, the Lemma 5
first-closed policy realizes the reduced `U^*_min(1, α)` value.
-/
theorem paper_problem6_firstClosedPolicy_optimalTypeFairnessAtLevel_one_eq_of_feasible_canonicalization
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hcanonical :
      ∀ ρ' : TypePolicy 2 n,
        TypeWeightedRecommendationModel.feasibleAtLevel
          (twoTypeReducedModel alpha v) 1 ρ' →
        ∃ ρbar : TypePolicy 2 n,
          TypeWeightedRecommendationModel.feasibleAtLevel
            (twoTypeReducedModel alpha v) 1 ρbar ∧
          (∀ l : Item n,
            pairShare alpha v l * (ρbar 0 l).toReal +
              (1 - pairShare alpha v l) * (ρbar 1 l).toReal =
            TypeWeightedRecommendationModel.itemFairness
              (twoTypeReducedModel alpha v) ρbar) ∧
          TypePolicy.SharedItemsBound ρbar ∧
          TypeWeightedRecommendationModel.typeFairness
            (twoTypeReducedModel alpha v) ρ' ≤
          TypeWeightedRecommendationModel.typeFairness
            (twoTypeReducedModel alpha v) ρbar) :
    TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel alpha v) 1 =
      TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel alpha v)
        (problem6FirstClosedPolicy alpha v halpha0 halpha1 hpos) := by
  exact
    problem6FirstClosedPolicy_optimalTypeFairnessAtLevel_one_eq_of_feasible_canonicalization
      hn halpha0 halpha1 hpos hdec hcanonical

/--
Theorem 3 reduced-optimum monotonicity, odd-center first-half endpoint form,
conditional only on the Proposition-1-shaped feasible-policy canonicalization
assumption at the two endpoints.
-/
theorem paper_theorem3_optimalTypeFairnessAtLevel_one_mono_firstHalf_center_of_alpha_le_of_feasible_canonicalization
    {n : ℕ} [NeZero n]
    {alpha alpha' : ℝ} {v : Item n → ℝ} {c : Item n}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (halpha_half : alpha ≤ 1 / 2)
    (halpha_half' : alpha' ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter_c : c.val = (reverseItem c).val)
    (hcanonical :
      ∀ ρ : TypePolicy 2 n,
        TypeWeightedRecommendationModel.feasibleAtLevel
          (twoTypeReducedModel alpha v) 1 ρ →
        ∃ ρbar : TypePolicy 2 n,
          TypeWeightedRecommendationModel.feasibleAtLevel
            (twoTypeReducedModel alpha v) 1 ρbar ∧
          (∀ l : Item n,
            pairShare alpha v l * (ρbar 0 l).toReal +
              (1 - pairShare alpha v l) * (ρbar 1 l).toReal =
            TypeWeightedRecommendationModel.itemFairness
              (twoTypeReducedModel alpha v) ρbar) ∧
          TypePolicy.SharedItemsBound ρbar ∧
          TypeWeightedRecommendationModel.typeFairness
            (twoTypeReducedModel alpha v) ρ ≤
          TypeWeightedRecommendationModel.typeFairness
            (twoTypeReducedModel alpha v) ρbar)
    (hcanonical' :
      ∀ ρ : TypePolicy 2 n,
        TypeWeightedRecommendationModel.feasibleAtLevel
          (twoTypeReducedModel alpha' v) 1 ρ →
        ∃ ρbar : TypePolicy 2 n,
          TypeWeightedRecommendationModel.feasibleAtLevel
            (twoTypeReducedModel alpha' v) 1 ρbar ∧
          (∀ l : Item n,
            pairShare alpha' v l * (ρbar 0 l).toReal +
              (1 - pairShare alpha' v l) * (ρbar 1 l).toReal =
            TypeWeightedRecommendationModel.itemFairness
              (twoTypeReducedModel alpha' v) ρbar) ∧
          TypePolicy.SharedItemsBound ρbar ∧
          TypeWeightedRecommendationModel.typeFairness
            (twoTypeReducedModel alpha' v) ρ ≤
          TypeWeightedRecommendationModel.typeFairness
            (twoTypeReducedModel alpha' v) ρbar) :
    TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel alpha v) 1 ≤
      TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel alpha' v) 1 := by
  exact
    theorem3_optimalTypeFairnessAtLevel_one_mono_firstHalf_center_of_alpha_le_of_feasible_canonicalization
      hn halpha0 halpha1 halpha0' halpha1' halpha_le
      halpha_half halpha_half' hpos hdec hcenter_c hcanonical hcanonical'

/--
Theorem 3 reduced-optimum monotonicity, even-center first-half endpoint form,
conditional only on the Proposition-1-shaped feasible-policy canonicalization
assumption at the two endpoints.
-/
theorem paper_theorem3_optimalTypeFairnessAtLevel_one_mono_firstHalf_succ_center_of_alpha_le_of_feasible_canonicalization
    {n : ℕ} [NeZero n]
    {alpha alpha' : ℝ} {v : Item n → ℝ} {c : Item n}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (halpha_half : alpha ≤ 1 / 2)
    (halpha_half' : alpha' ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hsucc : c.val + 1 = (reverseItem c).val)
    (hcanonical :
      ∀ ρ : TypePolicy 2 n,
        TypeWeightedRecommendationModel.feasibleAtLevel
          (twoTypeReducedModel alpha v) 1 ρ →
        ∃ ρbar : TypePolicy 2 n,
          TypeWeightedRecommendationModel.feasibleAtLevel
            (twoTypeReducedModel alpha v) 1 ρbar ∧
          (∀ l : Item n,
            pairShare alpha v l * (ρbar 0 l).toReal +
              (1 - pairShare alpha v l) * (ρbar 1 l).toReal =
            TypeWeightedRecommendationModel.itemFairness
              (twoTypeReducedModel alpha v) ρbar) ∧
          TypePolicy.SharedItemsBound ρbar ∧
          TypeWeightedRecommendationModel.typeFairness
            (twoTypeReducedModel alpha v) ρ ≤
          TypeWeightedRecommendationModel.typeFairness
            (twoTypeReducedModel alpha v) ρbar)
    (hcanonical' :
      ∀ ρ : TypePolicy 2 n,
        TypeWeightedRecommendationModel.feasibleAtLevel
          (twoTypeReducedModel alpha' v) 1 ρ →
        ∃ ρbar : TypePolicy 2 n,
          TypeWeightedRecommendationModel.feasibleAtLevel
            (twoTypeReducedModel alpha' v) 1 ρbar ∧
          (∀ l : Item n,
            pairShare alpha' v l * (ρbar 0 l).toReal +
              (1 - pairShare alpha' v l) * (ρbar 1 l).toReal =
            TypeWeightedRecommendationModel.itemFairness
              (twoTypeReducedModel alpha' v) ρbar) ∧
          TypePolicy.SharedItemsBound ρbar ∧
          TypeWeightedRecommendationModel.typeFairness
            (twoTypeReducedModel alpha' v) ρ ≤
          TypeWeightedRecommendationModel.typeFairness
            (twoTypeReducedModel alpha' v) ρbar) :
    TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel alpha v) 1 ≤
      TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel alpha' v) 1 := by
  exact
    theorem3_optimalTypeFairnessAtLevel_one_mono_firstHalf_succ_center_of_alpha_le_of_feasible_canonicalization
      hn halpha0 halpha1 halpha0' halpha1' halpha_le
      halpha_half halpha_half' hpos hdec hsucc hcanonical hcanonical'

/--
Problem 6 canonical closed-policy optimality bridge in the first half: the
type-`1` utility dual supplies the Proposition-1-shaped feasible-policy
canonicalization, so the Lemma 5 first-closed policy realizes reduced
`U^*_min(1, α)` whenever the first closed pivot lies at or before its mirror.
-/
theorem paper_problem6_firstClosedPolicy_optimalTypeFairnessAtLevel_one_eq_of_alpha_le_half_of_pivot_le_reverse
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha_half : alpha ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter :
      (problem6FirstClosedPivot alpha v halpha0 halpha1 hpos).val ≤
        (reverseItem
          (problem6FirstClosedPivot alpha v halpha0 halpha1 hpos)).val) :
    TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel alpha v) 1 =
      TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel alpha v)
        (problem6FirstClosedPolicy alpha v halpha0 halpha1 hpos) := by
  exact
    problem6FirstClosedPolicy_optimalTypeFairnessAtLevel_one_eq_of_alpha_le_half_of_pivot_le_reverse
      halpha0 halpha1 halpha_half hpos hdec hcenter

/--
Problem 6 canonical closed-policy optimality bridge, odd-center first-half
case.  Lemma 10 supplies the pivot-before-mirror side condition.
-/
theorem paper_problem6_firstClosedPolicy_optimalTypeFairnessAtLevel_one_eq_firstHalf_center
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {c : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha_half : alpha ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter_c : c.val = (reverseItem c).val) :
    TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel alpha v) 1 =
      TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel alpha v)
        (problem6FirstClosedPolicy alpha v halpha0 halpha1 hpos) := by
  exact
    problem6FirstClosedPolicy_optimalTypeFairnessAtLevel_one_eq_firstHalf_center
      halpha0 halpha1 halpha_half hpos hdec hcenter_c

/--
Problem 6 canonical closed-policy optimality bridge, even-center first-half
case.  Lemma 10 supplies the pivot-before-mirror side condition.
-/
theorem paper_problem6_firstClosedPolicy_optimalTypeFairnessAtLevel_one_eq_firstHalf_succ_center
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {c : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha_half : alpha ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hsucc : c.val + 1 = (reverseItem c).val) :
    TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel alpha v) 1 =
      TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel alpha v)
        (problem6FirstClosedPolicy alpha v halpha0 halpha1 hpos) := by
  exact
    problem6FirstClosedPolicy_optimalTypeFairnessAtLevel_one_eq_firstHalf_succ_center
      halpha0 halpha1 halpha_half hpos hdec hsucc

/--
Theorem 3 reduced-optimum monotonicity, odd-center first-half endpoint form,
with the feasible-policy canonicalization discharged by the type-`1` utility
dual.
-/
theorem paper_theorem3_optimalTypeFairnessAtLevel_one_mono_firstHalf_center_of_alpha_le
    {n : ℕ} [NeZero n]
    {alpha alpha' : ℝ} {v : Item n → ℝ} {c : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (halpha_half : alpha ≤ 1 / 2)
    (halpha_half' : alpha' ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter_c : c.val = (reverseItem c).val) :
    TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel alpha v) 1 ≤
      TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel alpha' v) 1 := by
  exact
    theorem3_optimalTypeFairnessAtLevel_one_mono_firstHalf_center_of_alpha_le
      halpha0 halpha1 halpha0' halpha1' halpha_le
      halpha_half halpha_half' hpos hdec hcenter_c

/--
Theorem 3 reduced-optimum monotonicity, even-center first-half endpoint form,
with the feasible-policy canonicalization discharged by the type-`1` utility
dual.
-/
theorem paper_theorem3_optimalTypeFairnessAtLevel_one_mono_firstHalf_succ_center_of_alpha_le
    {n : ℕ} [NeZero n]
    {alpha alpha' : ℝ} {v : Item n → ℝ} {c : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (halpha_half : alpha ≤ 1 / 2)
    (halpha_half' : alpha' ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hsucc : c.val + 1 = (reverseItem c).val) :
    TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel alpha v) 1 ≤
      TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel alpha' v) 1 := by
  exact
    theorem3_optimalTypeFairnessAtLevel_one_mono_firstHalf_succ_center_of_alpha_le
      halpha0 halpha1 halpha0' halpha1' halpha_le
      halpha_half halpha_half' hpos hdec hsucc

/--
Theorem 3 paper-facing price monotonicity, odd-center first-half form. The two
original recommendation models are connected to the opposing two-type reduced
models by reduction witnesses; the first-closed reduced policy supplies the
`γ = 1` feasible witnesses needed on both the original and reduced sides.
-/
theorem paper_theorem3_price_decreases_firstHalf_center_of_reduction
    {m n : ℕ} [NeZero m] [NeZero n]
    (R R' : ReductionWitness m n 2)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (reps' : UserTypeAssignment.TypeRepresentatives R'.data.types)
    {alpha alpha' : ℝ} {v : Item n → ℝ} {c : Item n}
    (hred : R.reduced = twoTypeReducedModel alpha v)
    (hred' : R'.reduced = twoTypeReducedModel alpha' v)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (halpha_half : alpha ≤ 1 / 2)
    (halpha_half' : alpha' ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter_c : c.val = (reverseItem c).val)
    (hNonneg : R.data.model.Nonnegative)
    (hRow : R.data.model.RowHasPositiveItem)
    (hNonneg' : R'.data.model.Nonnegative)
    (hRow' : R'.data.model.RowHasPositiveItem) :
    RecommendationModel.priceOfFairness R'.data.model ≤
      RecommendationModel.priceOfFairness R.data.model := by
  let ρred : TypePolicy 2 n :=
    problem6FirstClosedPolicy alpha v halpha0 halpha1 hpos
  let ρred' : TypePolicy 2 n :=
    problem6FirstClosedPolicy alpha' v halpha0' halpha1' hpos
  have hReducedFeas :
      TypeWeightedRecommendationModel.feasibleAtLevel R.reduced 1 ρred := by
    rw [hred]
    exact problem6FirstClosedPolicy_feasibleAtLevel_one
      halpha0 halpha1 hpos hdec
  have hReducedFeas' :
      TypeWeightedRecommendationModel.feasibleAtLevel R'.reduced 1 ρred' := by
    rw [hred']
    exact problem6FirstClosedPolicy_feasibleAtLevel_one
      halpha0' halpha1' hpos hdec
  have hOrigNonempty :
      (RecommendationModel.attainableUserFairnessAtLevel
        R.data.model 1).Nonempty := by
    refine ⟨RecommendationModel.userFairness R.data.model
      (R.liftedPolicy ρred), ?_⟩
    refine ⟨R.liftedPolicy ρred, ?_, rfl⟩
    unfold RecommendationModel.feasibleAtLevel
    rw [R.optimalItemFairness_eq_reduced reps]
    rw [R.itemFairness_liftedPolicy_eq_itemFairness ρred]
    exact hReducedFeas
  have hOrigNonempty' :
      (RecommendationModel.attainableUserFairnessAtLevel
        R'.data.model 1).Nonempty := by
    refine ⟨RecommendationModel.userFairness R'.data.model
      (R'.liftedPolicy ρred'), ?_⟩
    refine ⟨R'.liftedPolicy ρred', ?_, rfl⟩
    unfold RecommendationModel.feasibleAtLevel
    rw [R'.optimalItemFairness_eq_reduced reps']
    rw [R'.itemFairness_liftedPolicy_eq_itemFairness ρred']
    exact hReducedFeas'
  have hRedNonempty :
      (TypeWeightedRecommendationModel.attainableTypeFairnessAtLevel
        R.reduced 1).Nonempty := by
    refine ⟨TypeWeightedRecommendationModel.typeFairness R.reduced ρred, ?_⟩
    exact ⟨ρred, hReducedFeas, rfl⟩
  have hRedNonempty' :
      (TypeWeightedRecommendationModel.attainableTypeFairnessAtLevel
        R'.reduced 1).Nonempty := by
    refine ⟨TypeWeightedRecommendationModel.typeFairness R'.reduced ρred', ?_⟩
    exact ⟨ρred', hReducedFeas', rfl⟩
  have hUserEq :
      RecommendationModel.optimalUserFairnessAtLevel R.data.model 1 =
        TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
          R.reduced 1 :=
    R.optimalUserFairnessAtLevel_eq_reduced_of_nonempty
      reps hRow 1 hOrigNonempty hRedNonempty
  have hUserEq' :
      RecommendationModel.optimalUserFairnessAtLevel R'.data.model 1 =
        TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
          R'.reduced 1 :=
    R'.optimalUserFairnessAtLevel_eq_reduced_of_nonempty
      reps' hRow' 1 hOrigNonempty' hRedNonempty'
  have hred_mono :
      TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
          R.reduced 1 ≤
        TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
          R'.reduced 1 := by
    rw [hred, hred']
    exact theorem3_optimalTypeFairnessAtLevel_one_mono_firstHalf_center_of_alpha_le
      halpha0 halpha1 halpha0' halpha1' halpha_le
      halpha_half halpha_half' hpos hdec hcenter_c
  have huser_mono :
      RecommendationModel.optimalUserFairnessAtLevel R.data.model 1 ≤
        RecommendationModel.optimalUserFairnessAtLevel R'.data.model 1 := by
    rw [hUserEq, hUserEq']
    exact hred_mono
  exact R.data.model.priceOfFairness_le_of_optimalUserFairnessAtLevel_one_le
    R'.data.model hNonneg hRow hNonneg' hRow' huser_mono

/--
Theorem 3 paper-facing price monotonicity, even-center first-half form. The two
original recommendation models are connected to the opposing two-type reduced
models by reduction witnesses; the first-closed reduced policy supplies the
`γ = 1` feasible witnesses needed on both the original and reduced sides.
-/
theorem paper_theorem3_price_decreases_firstHalf_succ_center_of_reduction
    {m n : ℕ} [NeZero m] [NeZero n]
    (R R' : ReductionWitness m n 2)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (reps' : UserTypeAssignment.TypeRepresentatives R'.data.types)
    {alpha alpha' : ℝ} {v : Item n → ℝ} {c : Item n}
    (hred : R.reduced = twoTypeReducedModel alpha v)
    (hred' : R'.reduced = twoTypeReducedModel alpha' v)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (halpha_half : alpha ≤ 1 / 2)
    (halpha_half' : alpha' ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hsucc : c.val + 1 = (reverseItem c).val)
    (hNonneg : R.data.model.Nonnegative)
    (hRow : R.data.model.RowHasPositiveItem)
    (hNonneg' : R'.data.model.Nonnegative)
    (hRow' : R'.data.model.RowHasPositiveItem) :
    RecommendationModel.priceOfFairness R'.data.model ≤
      RecommendationModel.priceOfFairness R.data.model := by
  let ρred : TypePolicy 2 n :=
    problem6FirstClosedPolicy alpha v halpha0 halpha1 hpos
  let ρred' : TypePolicy 2 n :=
    problem6FirstClosedPolicy alpha' v halpha0' halpha1' hpos
  have hReducedFeas :
      TypeWeightedRecommendationModel.feasibleAtLevel R.reduced 1 ρred := by
    rw [hred]
    exact problem6FirstClosedPolicy_feasibleAtLevel_one
      halpha0 halpha1 hpos hdec
  have hReducedFeas' :
      TypeWeightedRecommendationModel.feasibleAtLevel R'.reduced 1 ρred' := by
    rw [hred']
    exact problem6FirstClosedPolicy_feasibleAtLevel_one
      halpha0' halpha1' hpos hdec
  have hOrigNonempty :
      (RecommendationModel.attainableUserFairnessAtLevel
        R.data.model 1).Nonempty := by
    refine ⟨RecommendationModel.userFairness R.data.model
      (R.liftedPolicy ρred), ?_⟩
    refine ⟨R.liftedPolicy ρred, ?_, rfl⟩
    unfold RecommendationModel.feasibleAtLevel
    rw [R.optimalItemFairness_eq_reduced reps]
    rw [R.itemFairness_liftedPolicy_eq_itemFairness ρred]
    exact hReducedFeas
  have hOrigNonempty' :
      (RecommendationModel.attainableUserFairnessAtLevel
        R'.data.model 1).Nonempty := by
    refine ⟨RecommendationModel.userFairness R'.data.model
      (R'.liftedPolicy ρred'), ?_⟩
    refine ⟨R'.liftedPolicy ρred', ?_, rfl⟩
    unfold RecommendationModel.feasibleAtLevel
    rw [R'.optimalItemFairness_eq_reduced reps']
    rw [R'.itemFairness_liftedPolicy_eq_itemFairness ρred']
    exact hReducedFeas'
  have hRedNonempty :
      (TypeWeightedRecommendationModel.attainableTypeFairnessAtLevel
        R.reduced 1).Nonempty := by
    refine ⟨TypeWeightedRecommendationModel.typeFairness R.reduced ρred, ?_⟩
    exact ⟨ρred, hReducedFeas, rfl⟩
  have hRedNonempty' :
      (TypeWeightedRecommendationModel.attainableTypeFairnessAtLevel
        R'.reduced 1).Nonempty := by
    refine ⟨TypeWeightedRecommendationModel.typeFairness R'.reduced ρred', ?_⟩
    exact ⟨ρred', hReducedFeas', rfl⟩
  have hUserEq :
      RecommendationModel.optimalUserFairnessAtLevel R.data.model 1 =
        TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
          R.reduced 1 :=
    R.optimalUserFairnessAtLevel_eq_reduced_of_nonempty
      reps hRow 1 hOrigNonempty hRedNonempty
  have hUserEq' :
      RecommendationModel.optimalUserFairnessAtLevel R'.data.model 1 =
        TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
          R'.reduced 1 :=
    R'.optimalUserFairnessAtLevel_eq_reduced_of_nonempty
      reps' hRow' 1 hOrigNonempty' hRedNonempty'
  have hred_mono :
      TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
          R.reduced 1 ≤
        TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
          R'.reduced 1 := by
    rw [hred, hred']
    exact theorem3_optimalTypeFairnessAtLevel_one_mono_firstHalf_succ_center_of_alpha_le
      halpha0 halpha1 halpha0' halpha1' halpha_le
      halpha_half halpha_half' hpos hdec hsucc
  have huser_mono :
      RecommendationModel.optimalUserFairnessAtLevel R.data.model 1 ≤
        RecommendationModel.optimalUserFairnessAtLevel R'.data.model 1 := by
    rw [hUserEq, hUserEq']
    exact hred_mono
  exact R.data.model.priceOfFairness_le_of_optimalUserFairnessAtLevel_one_le
    R'.data.model hNonneg hRow hNonneg' hRow' huser_mono

/--
Theorem 3 reduced-optimum monotonicity, first-half endpoint form.  The
odd/even midpoint split is discharged internally.
-/
theorem paper_theorem3_optimalTypeFairnessAtLevel_one_mono_firstHalf_of_alpha_le
    {n : ℕ} [NeZero n]
    {alpha alpha' : ℝ} {v : Item n → ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (halpha_half : alpha ≤ 1 / 2)
    (halpha_half' : alpha' ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v) :
    TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel alpha v) 1 ≤
      TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel alpha' v) 1 := by
  rcases midpoint_center_or_succ_center (n := n) with hcenter | hsucc
  · rcases hcenter with ⟨c, hcenter⟩
    exact
      paper_theorem3_optimalTypeFairnessAtLevel_one_mono_firstHalf_center_of_alpha_le
        halpha0 halpha1 halpha0' halpha1' halpha_le
        halpha_half halpha_half' hpos hdec hcenter
  · rcases hsucc with ⟨c, hsucc⟩
    exact
      paper_theorem3_optimalTypeFairnessAtLevel_one_mono_firstHalf_succ_center_of_alpha_le
        halpha0 halpha1 halpha0' halpha1' halpha_le
        halpha_half halpha_half' hpos hdec hsucc

/--
Theorem 3 reduced-optimum monotonicity, second-half endpoint form.  The paper
derives the second half by reflecting `α` around `1 / 2`; here that reflection
is the mirror-policy equivalence for the two-type reduced model.
-/
theorem paper_theorem3_optimalTypeFairnessAtLevel_one_antitone_secondHalf_of_alpha_le
    {n : ℕ} [NeZero n]
    {alpha alpha' : ℝ} {v : Item n → ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (halpha_half : 1 / 2 ≤ alpha)
    (halpha_half' : 1 / 2 ≤ alpha')
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v) :
    TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel alpha' v) 1 ≤
      TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel alpha v) 1 := by
  have hbeta0 : 0 < 1 - alpha' := by linarith
  have hbeta1 : 1 - alpha' < 1 := by linarith
  have hbeta0' : 0 < 1 - alpha := by linarith
  have hbeta1' : 1 - alpha < 1 := by linarith
  have hbeta_le : 1 - alpha' ≤ 1 - alpha := by linarith
  have hbeta_half : 1 - alpha' ≤ 1 / 2 := by linarith
  have hbeta_half' : 1 - alpha ≤ 1 / 2 := by linarith
  have hmono :
      TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
          (twoTypeReducedModel (1 - alpha') v) 1 ≤
        TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
          (twoTypeReducedModel (1 - alpha) v) 1 :=
    paper_theorem3_optimalTypeFairnessAtLevel_one_mono_firstHalf_of_alpha_le
      (alpha := 1 - alpha') (alpha' := 1 - alpha) (v := v)
      hbeta0 hbeta1 hbeta0' hbeta1' hbeta_le
      hbeta_half hbeta_half' hpos hdec
  rw [twoTypeReducedModel_optimalTypeFairnessAtLevel_one_mirror_eq
        (alpha := alpha') (v := v),
      twoTypeReducedModel_optimalTypeFairnessAtLevel_one_mirror_eq
        (alpha := alpha) (v := v)] at hmono
  exact hmono

/--
Theorem 3 paper-facing price monotonicity, first-half form.  The two original
recommendation models are connected to the opposing two-type reduced models by
reduction witnesses, and the odd/even midpoint split is discharged internally.
-/
theorem paper_theorem3_price_decreases_firstHalf_of_reduction
    {m n : ℕ} [NeZero m] [NeZero n]
    (R R' : ReductionWitness m n 2)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (reps' : UserTypeAssignment.TypeRepresentatives R'.data.types)
    {alpha alpha' : ℝ} {v : Item n → ℝ}
    (hred : R.reduced = twoTypeReducedModel alpha v)
    (hred' : R'.reduced = twoTypeReducedModel alpha' v)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (halpha_half : alpha ≤ 1 / 2)
    (halpha_half' : alpha' ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hNonneg : R.data.model.Nonnegative)
    (hRow : R.data.model.RowHasPositiveItem)
    (hNonneg' : R'.data.model.Nonnegative)
    (hRow' : R'.data.model.RowHasPositiveItem) :
    RecommendationModel.priceOfFairness R'.data.model ≤
      RecommendationModel.priceOfFairness R.data.model := by
  rcases midpoint_center_or_succ_center (n := n) with hcenter | hsucc
  · rcases hcenter with ⟨c, hcenter⟩
    exact
      paper_theorem3_price_decreases_firstHalf_center_of_reduction
        R R' reps reps' hred hred' halpha0 halpha1 halpha0' halpha1'
        halpha_le halpha_half halpha_half' hpos hdec hcenter hNonneg hRow
        hNonneg' hRow'
  · rcases hsucc with ⟨c, hsucc⟩
    exact
      paper_theorem3_price_decreases_firstHalf_succ_center_of_reduction
        R R' reps reps' hred hred' halpha0 halpha1 halpha0' halpha1'
        halpha_le halpha_half halpha_half' hpos hdec hsucc hNonneg hRow
        hNonneg' hRow'

/--
Theorem 3 paper-facing price monotonicity, second-half form.  On the far side
of the symmetry point the constrained user optimum moves in the opposite
direction, so the price of fairness weakly increases with `α`.
-/
theorem paper_theorem3_price_increases_secondHalf_of_reduction
    {m n : ℕ} [NeZero m] [NeZero n]
    (R R' : ReductionWitness m n 2)
    (reps : UserTypeAssignment.TypeRepresentatives R.data.types)
    (reps' : UserTypeAssignment.TypeRepresentatives R'.data.types)
    {alpha alpha' : ℝ} {v : Item n → ℝ}
    (hred : R.reduced = twoTypeReducedModel alpha v)
    (hred' : R'.reduced = twoTypeReducedModel alpha' v)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (halpha_half : 1 / 2 ≤ alpha)
    (halpha_half' : 1 / 2 ≤ alpha')
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hNonneg : R.data.model.Nonnegative)
    (hRow : R.data.model.RowHasPositiveItem)
    (hNonneg' : R'.data.model.Nonnegative)
    (hRow' : R'.data.model.RowHasPositiveItem) :
    RecommendationModel.priceOfFairness R.data.model ≤
      RecommendationModel.priceOfFairness R'.data.model := by
  let ρred : TypePolicy 2 n :=
    problem6FirstClosedPolicy alpha v halpha0 halpha1 hpos
  let ρred' : TypePolicy 2 n :=
    problem6FirstClosedPolicy alpha' v halpha0' halpha1' hpos
  have hReducedFeas :
      TypeWeightedRecommendationModel.feasibleAtLevel R.reduced 1 ρred := by
    rw [hred]
    exact problem6FirstClosedPolicy_feasibleAtLevel_one
      halpha0 halpha1 hpos hdec
  have hReducedFeas' :
      TypeWeightedRecommendationModel.feasibleAtLevel R'.reduced 1 ρred' := by
    rw [hred']
    exact problem6FirstClosedPolicy_feasibleAtLevel_one
      halpha0' halpha1' hpos hdec
  have hOrigNonempty :
      (RecommendationModel.attainableUserFairnessAtLevel
        R.data.model 1).Nonempty := by
    refine ⟨RecommendationModel.userFairness R.data.model
      (R.liftedPolicy ρred), ?_⟩
    refine ⟨R.liftedPolicy ρred, ?_, rfl⟩
    unfold RecommendationModel.feasibleAtLevel
    rw [R.optimalItemFairness_eq_reduced reps]
    rw [R.itemFairness_liftedPolicy_eq_itemFairness ρred]
    exact hReducedFeas
  have hOrigNonempty' :
      (RecommendationModel.attainableUserFairnessAtLevel
        R'.data.model 1).Nonempty := by
    refine ⟨RecommendationModel.userFairness R'.data.model
      (R'.liftedPolicy ρred'), ?_⟩
    refine ⟨R'.liftedPolicy ρred', ?_, rfl⟩
    unfold RecommendationModel.feasibleAtLevel
    rw [R'.optimalItemFairness_eq_reduced reps']
    rw [R'.itemFairness_liftedPolicy_eq_itemFairness ρred']
    exact hReducedFeas'
  have hRedNonempty :
      (TypeWeightedRecommendationModel.attainableTypeFairnessAtLevel
        R.reduced 1).Nonempty := by
    refine ⟨TypeWeightedRecommendationModel.typeFairness R.reduced ρred, ?_⟩
    exact ⟨ρred, hReducedFeas, rfl⟩
  have hRedNonempty' :
      (TypeWeightedRecommendationModel.attainableTypeFairnessAtLevel
        R'.reduced 1).Nonempty := by
    refine ⟨TypeWeightedRecommendationModel.typeFairness R'.reduced ρred', ?_⟩
    exact ⟨ρred', hReducedFeas', rfl⟩
  have hUserEq :
      RecommendationModel.optimalUserFairnessAtLevel R.data.model 1 =
        TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
          R.reduced 1 :=
    R.optimalUserFairnessAtLevel_eq_reduced_of_nonempty
      reps hRow 1 hOrigNonempty hRedNonempty
  have hUserEq' :
      RecommendationModel.optimalUserFairnessAtLevel R'.data.model 1 =
        TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
          R'.reduced 1 :=
    R'.optimalUserFairnessAtLevel_eq_reduced_of_nonempty
      reps' hRow' 1 hOrigNonempty' hRedNonempty'
  have hred_mono :
      TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
          R'.reduced 1 ≤
        TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
          R.reduced 1 := by
    rw [hred, hred']
    exact
      paper_theorem3_optimalTypeFairnessAtLevel_one_antitone_secondHalf_of_alpha_le
        halpha0 halpha1 halpha0' halpha1' halpha_le
        halpha_half halpha_half' hpos hdec
  have huser_mono :
      RecommendationModel.optimalUserFairnessAtLevel R'.data.model 1 ≤
        RecommendationModel.optimalUserFairnessAtLevel R.data.model 1 := by
    rw [hUserEq, hUserEq']
    exact hred_mono
  exact R'.data.model.priceOfFairness_le_of_optimalUserFairnessAtLevel_one_le
    R.data.model hNonneg' hRow' hNonneg hRow huser_mono

/--
Appendix D, Lemma 6 normalization bridge: raw closed-form comparison implies
normalized type-utility comparison when the two best-item denominators agree.
-/
theorem paper_lemma6_closedPolicy_normalizedType_one_le_zero_of_raw
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hpivot : Problem6ClosedNonnegativePivots alpha v t)
    (hbest :
      TypeWeightedRecommendationModel.bestItemUtility
          (twoTypeReducedModel alpha v) 1 =
        TypeWeightedRecommendationModel.bestItemUtility
          (twoTypeReducedModel alpha v) 0)
    (hbest_pos :
      0 < TypeWeightedRecommendationModel.bestItemUtility
        (twoTypeReducedModel alpha v) 0)
    (hraw :
      problem6ClosedTypeOneRawUtility alpha v t ≤
        problem6ClosedTypeZeroRawUtility alpha v t) :
    TypeWeightedRecommendationModel.normalizedTypeUtility
        (twoTypeReducedModel alpha v)
        (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot) 1 ≤
      TypeWeightedRecommendationModel.normalizedTypeUtility
        (twoTypeReducedModel alpha v)
        (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot) 0 := by
  exact problem6ClosedPolicy_normalizedType_one_le_zero_of_raw
    halpha0 halpha1 hpos hpivot hbest hbest_pos hraw

/--
Appendix D, Lemma 6 normalized-utility comparison under `α ≤ 1/2`, with the
remaining pivot-gap and equal-best-denominator obligations explicit.
-/
theorem paper_lemma6_closedPolicy_normalizedType_one_le_zero_of_alpha_le_half
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha_half : alpha ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hpivot : Problem6ClosedNonnegativePivots alpha v t)
    (hcenter : t.val ≤ (reverseItem t).val)
    (hpivot_gap :
      0 ≤ problem6ClosedX alpha v t t -
        problem6ClosedY alpha v t (reverseItem t))
    (hbest :
      TypeWeightedRecommendationModel.bestItemUtility
          (twoTypeReducedModel alpha v) 1 =
        TypeWeightedRecommendationModel.bestItemUtility
          (twoTypeReducedModel alpha v) 0)
    (hbest_pos :
      0 < TypeWeightedRecommendationModel.bestItemUtility
        (twoTypeReducedModel alpha v) 0) :
    TypeWeightedRecommendationModel.normalizedTypeUtility
        (twoTypeReducedModel alpha v)
        (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot) 1 ≤
      TypeWeightedRecommendationModel.normalizedTypeUtility
        (twoTypeReducedModel alpha v)
        (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot) 0 := by
  exact problem6ClosedPolicy_normalizedType_one_le_zero_of_alpha_le_half
    halpha0 halpha1 halpha_half hpos hdec hpivot hcenter hpivot_gap
    hbest hbest_pos

/--
Appendix D, Lemma 6 normalized-utility comparison under `α ≤ 1/2`, with the
pivot-gap obligation removed.
-/
theorem paper_lemma6_closedPolicy_normalizedType_one_le_zero_of_alpha_le_half_of_pivot_le_reverse
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha_half : alpha ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hpivot : Problem6ClosedNonnegativePivots alpha v t)
    (hcenter : t.val ≤ (reverseItem t).val)
    (hbest :
      TypeWeightedRecommendationModel.bestItemUtility
          (twoTypeReducedModel alpha v) 1 =
        TypeWeightedRecommendationModel.bestItemUtility
          (twoTypeReducedModel alpha v) 0)
    (hbest_pos :
      0 < TypeWeightedRecommendationModel.bestItemUtility
        (twoTypeReducedModel alpha v) 0) :
    TypeWeightedRecommendationModel.normalizedTypeUtility
        (twoTypeReducedModel alpha v)
        (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot) 1 ≤
      TypeWeightedRecommendationModel.normalizedTypeUtility
        (twoTypeReducedModel alpha v)
        (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot) 0 := by
  exact problem6ClosedPolicy_normalizedType_one_le_zero_of_alpha_le_half_of_pivot_le_reverse
    halpha0 halpha1 halpha_half hpos hdec hpivot hcenter hbest hbest_pos

/--
Appendix D, Lemma 6 normalized-utility comparison under `α ≤ 1/2`, with the
common best-item denominator discharged by the opposing-preference model.
-/
theorem paper_lemma6_closedPolicy_normalizedType_one_le_zero_of_alpha_le_half_auto_best
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha_half : alpha ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hpivot : Problem6ClosedNonnegativePivots alpha v t)
    (hcenter : t.val ≤ (reverseItem t).val)
    (hpivot_gap :
      0 ≤ problem6ClosedX alpha v t t -
        problem6ClosedY alpha v t (reverseItem t)) :
    TypeWeightedRecommendationModel.normalizedTypeUtility
        (twoTypeReducedModel alpha v)
        (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot) 1 ≤
      TypeWeightedRecommendationModel.normalizedTypeUtility
        (twoTypeReducedModel alpha v)
        (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot) 0 := by
  exact problem6ClosedPolicy_normalizedType_one_le_zero_of_alpha_le_half_auto_best
    halpha0 halpha1 halpha_half hpos hdec hpivot hcenter hpivot_gap

/--
Appendix D, Lemma 6 normalized-utility comparison under `α ≤ 1/2`, with the
common best-item denominator discharged and no pivot-gap side condition.
-/
theorem paper_lemma6_closedPolicy_normalizedType_one_le_zero_of_alpha_le_half_auto_best_of_pivot_le_reverse
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha_half : alpha ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hpivot : Problem6ClosedNonnegativePivots alpha v t)
    (hcenter : t.val ≤ (reverseItem t).val) :
    TypeWeightedRecommendationModel.normalizedTypeUtility
        (twoTypeReducedModel alpha v)
        (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot) 1 ≤
      TypeWeightedRecommendationModel.normalizedTypeUtility
        (twoTypeReducedModel alpha v)
        (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot) 0 := by
  exact problem6ClosedPolicy_normalizedType_one_le_zero_of_alpha_le_half_auto_best_of_pivot_le_reverse
    halpha0 halpha1 halpha_half hpos hdec hpivot hcenter

/--
Appendix D, Lemma 6 consequence: under the paper's remaining pivot-gap
condition, the closed policy's type fairness is type `1`'s normalized utility.
-/
theorem paper_lemma6_closedPolicy_typeFairness_eq_one_of_alpha_le_half
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha_half : alpha ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hpivot : Problem6ClosedNonnegativePivots alpha v t)
    (hcenter : t.val ≤ (reverseItem t).val)
    (hpivot_gap :
      0 ≤ problem6ClosedX alpha v t t -
        problem6ClosedY alpha v t (reverseItem t)) :
    TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel alpha v)
        (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot) =
      TypeWeightedRecommendationModel.normalizedTypeUtility
        (twoTypeReducedModel alpha v)
        (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot) 1 := by
  exact problem6ClosedPolicy_typeFairness_eq_one_of_alpha_le_half
    halpha0 halpha1 halpha_half hpos hdec hpivot hcenter hpivot_gap

/--
Appendix D, Lemma 6 consequence with the pivot-gap side condition removed.
-/
theorem paper_lemma6_closedPolicy_typeFairness_eq_one_of_alpha_le_half_of_pivot_le_reverse
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha_half : alpha ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hpivot : Problem6ClosedNonnegativePivots alpha v t)
    (hcenter : t.val ≤ (reverseItem t).val) :
    TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel alpha v)
        (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot) =
      TypeWeightedRecommendationModel.normalizedTypeUtility
        (twoTypeReducedModel alpha v)
        (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot) 1 := by
  exact problem6ClosedPolicy_typeFairness_eq_one_of_alpha_le_half_of_pivot_le_reverse
    halpha0 halpha1 halpha_half hpos hdec hpivot hcenter

/--
Appendix D, Lemma 6 consequence from a closed-form optimality certificate,
with the pivot-gap side condition removed.
-/
theorem paper_lemma6_closedPolicy_typeFairness_eq_one_of_closed_certificate_alpha_le_half_of_pivot_le_reverse
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha_half : alpha ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (cert : Problem6ClosedOptimalityCertificate alpha v t)
    (hcenter : t.val ≤ (reverseItem t).val) :
    let hpivot : Problem6ClosedNonnegativePivots alpha v t :=
      problem6ClosedNonnegativePivots_of_denominatorBounds
        halpha0 halpha1 hpos cert.denominator_bounds
    TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel alpha v)
        (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot) =
      TypeWeightedRecommendationModel.normalizedTypeUtility
        (twoTypeReducedModel alpha v)
        (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot) 1 := by
  exact problem6ClosedPolicy_typeFairness_eq_one_of_closed_certificate_alpha_le_half_of_pivot_le_reverse
    halpha0 halpha1 halpha_half hpos hdec cert hcenter

/--
Appendix D, Lemma 6 consequence for the paper's equality-form optimal BFS
package, conditional on the selected pivot being at or before its mirror.
-/
theorem paper_lemma6_closedPolicy_typeFairness_eq_one_of_equalizedBasicOptimal_alpha_le_half_of_pivot_le_reverse
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 2 n} {ell : ℝ}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha_half : alpha ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (h : Problem6EqualizedBasicOptimal alpha v ρ ell)
    (hcenter :
      (TypePolicy.lastActiveTypeZero ρ).val ≤
        (reverseItem (TypePolicy.lastActiveTypeZero ρ)).val) :
    let t : Item n := TypePolicy.lastActiveTypeZero ρ
    let cert : Problem6ClosedOptimalityCertificate alpha v t :=
      problem6ClosedOptimalityCertificate_of_equalizedBasicOptimal_of_two_lt
        hn halpha0 halpha1 hpos hdec h
    let hpivot : Problem6ClosedNonnegativePivots alpha v t :=
      problem6ClosedNonnegativePivots_of_denominatorBounds
        halpha0 halpha1 hpos cert.denominator_bounds
    TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel alpha v)
        (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot) =
      TypeWeightedRecommendationModel.normalizedTypeUtility
        (twoTypeReducedModel alpha v)
        (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot) 1 := by
  exact problem6ClosedPolicy_typeFairness_eq_one_of_equalizedBasicOptimal_alpha_le_half_of_pivot_le_reverse
    hn halpha0 halpha1 halpha_half hpos hdec h hcenter

/--
Appendix D, Lemma 6 stitched with Lemma 10 for the paper's equality-form
optimal BFS package, odd-center case.
-/
theorem paper_lemma6_closedPolicy_typeFairness_eq_one_of_equalizedBasicOptimal_alpha_le_half_center
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ}
    {ρ ρhalf : TypePolicy 2 n} {ell ellHalf : ℝ} {c : Item n}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha_half : alpha ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter_c : c.val = (reverseItem c).val)
    (h : Problem6EqualizedBasicOptimal alpha v ρ ell)
    (hhalf : Problem6EqualizedBasicOptimal (1 / 2) v ρhalf ellHalf) :
    let t : Item n := TypePolicy.lastActiveTypeZero ρ
    let cert : Problem6ClosedOptimalityCertificate alpha v t :=
      problem6ClosedOptimalityCertificate_of_equalizedBasicOptimal_of_two_lt
        hn halpha0 halpha1 hpos hdec h
    let hpivot : Problem6ClosedNonnegativePivots alpha v t :=
      problem6ClosedNonnegativePivots_of_denominatorBounds
        halpha0 halpha1 hpos cert.denominator_bounds
    TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel alpha v)
        (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot) =
      TypeWeightedRecommendationModel.normalizedTypeUtility
        (twoTypeReducedModel alpha v)
        (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot) 1 := by
  exact problem6ClosedPolicy_typeFairness_eq_one_of_equalizedBasicOptimal_alpha_le_half_center
    hn halpha0 halpha1 halpha_half hpos hdec hcenter_c h hhalf

/--
Appendix D, Lemma 6 stitched with Lemma 10 for the paper's equality-form
optimal BFS package, even-center case.
-/
theorem paper_lemma6_closedPolicy_typeFairness_eq_one_of_equalizedBasicOptimal_alpha_le_half_succ_center
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ}
    {ρ ρhalf : TypePolicy 2 n} {ell ellHalf : ℝ} {c : Item n}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha_half : alpha ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hsucc : c.val + 1 = (reverseItem c).val)
    (h : Problem6EqualizedBasicOptimal alpha v ρ ell)
    (hhalf : Problem6EqualizedBasicOptimal (1 / 2) v ρhalf ellHalf) :
    let t : Item n := TypePolicy.lastActiveTypeZero ρ
    let cert : Problem6ClosedOptimalityCertificate alpha v t :=
      problem6ClosedOptimalityCertificate_of_equalizedBasicOptimal_of_two_lt
        hn halpha0 halpha1 hpos hdec h
    let hpivot : Problem6ClosedNonnegativePivots alpha v t :=
      problem6ClosedNonnegativePivots_of_denominatorBounds
        halpha0 halpha1 hpos cert.denominator_bounds
    TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel alpha v)
        (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot) =
      TypeWeightedRecommendationModel.normalizedTypeUtility
        (twoTypeReducedModel alpha v)
        (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot) 1 := by
  exact problem6ClosedPolicy_typeFairness_eq_one_of_equalizedBasicOptimal_alpha_le_half_succ_center
    hn halpha0 halpha1 halpha_half hpos hdec hsucc h hhalf

/--
Appendix D, Lemma 5/6 bridge: the selected equality-form optimal BFS policy is
the Lemma 5 closed-form policy at its active pivot.
-/
theorem paper_lemma6_equalizedBasicOptimal_policy_eq_closedPolicy_of_two_lt
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 2 n} {ell : ℝ}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (h : Problem6EqualizedBasicOptimal alpha v ρ ell) :
    let t : Item n := TypePolicy.lastActiveTypeZero ρ
    let cert : Problem6ClosedOptimalityCertificate alpha v t :=
      problem6ClosedOptimalityCertificate_of_equalizedBasicOptimal_of_two_lt
        hn halpha0 halpha1 hpos hdec h
    let hpivot : Problem6ClosedNonnegativePivots alpha v t :=
      problem6ClosedNonnegativePivots_of_denominatorBounds
        halpha0 halpha1 hpos cert.denominator_bounds
    ρ = problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot := by
  exact problem6EqualizedBasicOptimal_policy_eq_closedPolicy_of_two_lt
    hn halpha0 halpha1 hpos hdec h

/--
Appendix D, Lemma 6 for the actual selected equality-form optimal BFS policy,
conditional on the selected pivot being at or before its mirror.
-/
theorem paper_lemma6_equalizedBasicOptimal_typeFairness_eq_one_of_alpha_le_half_of_pivot_le_reverse
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 2 n} {ell : ℝ}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha_half : alpha ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (h : Problem6EqualizedBasicOptimal alpha v ρ ell)
    (hcenter :
      (TypePolicy.lastActiveTypeZero ρ).val ≤
        (reverseItem (TypePolicy.lastActiveTypeZero ρ)).val) :
    TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel alpha v) ρ =
      TypeWeightedRecommendationModel.normalizedTypeUtility
        (twoTypeReducedModel alpha v) ρ 1 := by
  exact problem6EqualizedBasicOptimal_typeFairness_eq_one_of_alpha_le_half_of_pivot_le_reverse
    hn halpha0 halpha1 halpha_half hpos hdec h hcenter

/--
Appendix D, Lemma 6 stitched with Lemma 10 for the actual selected
equality-form optimal BFS policy, odd-center case.
-/
theorem paper_lemma6_equalizedBasicOptimal_typeFairness_eq_one_of_alpha_le_half_center
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ}
    {ρ ρhalf : TypePolicy 2 n} {ell ellHalf : ℝ} {c : Item n}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha_half : alpha ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter_c : c.val = (reverseItem c).val)
    (h : Problem6EqualizedBasicOptimal alpha v ρ ell)
    (hhalf : Problem6EqualizedBasicOptimal (1 / 2) v ρhalf ellHalf) :
    TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel alpha v) ρ =
      TypeWeightedRecommendationModel.normalizedTypeUtility
        (twoTypeReducedModel alpha v) ρ 1 := by
  exact problem6EqualizedBasicOptimal_typeFairness_eq_one_of_alpha_le_half_center
    hn halpha0 halpha1 halpha_half hpos hdec hcenter_c h hhalf

/--
Appendix D, Lemma 6 stitched with Lemma 10 for the actual selected
equality-form optimal BFS policy, even-center case.
-/
theorem paper_lemma6_equalizedBasicOptimal_typeFairness_eq_one_of_alpha_le_half_succ_center
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ}
    {ρ ρhalf : TypePolicy 2 n} {ell ellHalf : ℝ} {c : Item n}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha_half : alpha ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hsucc : c.val + 1 = (reverseItem c).val)
    (h : Problem6EqualizedBasicOptimal alpha v ρ ell)
    (hhalf : Problem6EqualizedBasicOptimal (1 / 2) v ρhalf ellHalf) :
    TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel alpha v) ρ =
      TypeWeightedRecommendationModel.normalizedTypeUtility
        (twoTypeReducedModel alpha v) ρ 1 := by
  exact problem6EqualizedBasicOptimal_typeFairness_eq_one_of_alpha_le_half_succ_center
    hn halpha0 halpha1 halpha_half hpos hdec hsucc h hhalf

/--
Appendix D, Lemma 6 stitched with Lemma 10, odd-center case, with the
midpoint optimum supplied by the Lemma 5 closed form.
-/
theorem paper_lemma6_equalizedBasicOptimal_typeFairness_eq_one_of_alpha_le_half_center_of_closed_half
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ}
    {ρ : TypePolicy 2 n} {ell : ℝ} {c : Item n}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha_half : alpha ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter_c : c.val = (reverseItem c).val)
    (h : Problem6EqualizedBasicOptimal alpha v ρ ell) :
    TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel alpha v) ρ =
      TypeWeightedRecommendationModel.normalizedTypeUtility
        (twoTypeReducedModel alpha v) ρ 1 := by
  exact problem6EqualizedBasicOptimal_typeFairness_eq_one_of_alpha_le_half_center_of_closed_half
    hn halpha0 halpha1 halpha_half hpos hdec hcenter_c h

/--
Appendix D, Lemma 6 stitched with Lemma 10, even-center case, with the
midpoint optimum supplied by the Lemma 5 closed form.
-/
theorem paper_lemma6_equalizedBasicOptimal_typeFairness_eq_one_of_alpha_le_half_succ_center_of_closed_half
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ}
    {ρ : TypePolicy 2 n} {ell : ℝ} {c : Item n}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha_half : alpha ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hsucc : c.val + 1 = (reverseItem c).val)
    (h : Problem6EqualizedBasicOptimal alpha v ρ ell) :
    TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel alpha v) ρ =
      TypeWeightedRecommendationModel.normalizedTypeUtility
        (twoTypeReducedModel alpha v) ρ 1 := by
  exact problem6EqualizedBasicOptimal_typeFairness_eq_one_of_alpha_le_half_succ_center_of_closed_half
    hn halpha0 halpha1 halpha_half hpos hdec hsucc h

/--
Appendix D, Lemma 6 mirror-index condition: a pivot at or before center sends
every pre-pivot item to a post-pivot mirror.
-/
theorem paper_lemma6_reverseItem_after_pivot_of_before_pivot_of_pivot_le_reverse
    {n : ℕ} {t j : Item n}
    (hcenter : t.val ≤ (reverseItem t).val)
    (hj : j.val < t.val) :
    t.val < (reverseItem j).val := by
  exact reverseItem_after_pivot_of_before_pivot_of_pivot_le_reverse
    hcenter hj

/--
Appendix D, Lemma 10 setup: at `α = 1/2`, opposite items have complementary
shares.
-/
theorem paper_lemma10_pairShare_half_add_reverse_eq_one
    {n : ℕ} {v : Item n → ℝ} (j : Item n)
    (hpos : ∀ j : Item n, 0 < v j) :
    pairShare (1 / 2) v j +
        pairShare (1 / 2) v (reverseItem j) = 1 := by
  exact pairShare_half_add_reverse_eq_one j hpos

/-- Appendix D, Lemma 10 setup: `q_j(1/2) = 1 - q_{n-j+1}(1/2)`. -/
theorem paper_lemma10_pairShare_half_eq_one_sub_reverse
    {n : ℕ} {v : Item n → ℝ} (j : Item n)
    (hpos : ∀ j : Item n, 0 < v j) :
    pairShare (1 / 2) v j =
      1 - pairShare (1 / 2) v (reverseItem j) := by
  exact pairShare_half_eq_one_sub_reverse j hpos

/--
Appendix D, Lemma 10 exact-center mirror indexing: when the candidate pivot is
its own mirror, post-pivot mirrors are exactly the pre-pivot items.
-/
theorem paper_lemma10_pivot_lt_reverseItem_iff_val_lt_pivot_of_pivot_eq_reverse
    {n : ℕ} {t j : Item n}
    (hcenter : t.val = (reverseItem t).val) :
    t.val < (reverseItem j).val ↔ j.val < t.val := by
  exact pivot_lt_reverseItem_iff_val_lt_pivot_of_pivot_eq_reverse
    (t := t) (j := j) hcenter

/--
Appendix D, Lemma 10 even-center mirror indexing: when the candidate pivot is
immediately before its mirror, post-pivot mirrors are exactly the pivot and
pre-pivot items.
-/
theorem paper_lemma10_pivot_lt_reverseItem_iff_val_le_pivot_of_pivot_succ_reverse
    {n : ℕ} {t j : Item n}
    (hsucc : t.val + 1 = (reverseItem t).val) :
    t.val < (reverseItem j).val ↔ j.val ≤ t.val := by
  exact pivot_lt_reverseItem_iff_val_le_pivot_of_pivot_succ_reverse
    (t := t) (j := j) hsucc

/--
Appendix D, Lemma 10 exact-center case: at `α = 1/2`, the Lemma 5 left and
right inverse-share sums coincide.
-/
theorem paper_lemma10_LeftSum_half_eq_RightSum_half_of_center
    {n : ℕ} {v : Item n → ℝ} {t : Item n}
    (hpos : ∀ j : Item n, 0 < v j)
    (hcenter : t.val = (reverseItem t).val) :
    problem6LeftSum (1 / 2) v t = problem6RightSum (1 / 2) v t := by
  exact problem6LeftSum_half_eq_rightSum_half_of_pivot_eq_reverse
    (v := v) (t := t) hpos hcenter

/--
Appendix D, Lemma 10 even-center case: the right inverse-share sum is the left
sum plus the pivot inverse-share term.
-/
theorem paper_lemma10_RightSum_half_eq_LeftSum_half_add_inv_pairShare_of_succ_center
    {n : ℕ} {v : Item n → ℝ} {t : Item n}
    (hpos : ∀ j : Item n, 0 < v j)
    (hsucc : t.val + 1 = (reverseItem t).val) :
    problem6RightSum (1 / 2) v t =
      problem6LeftSum (1 / 2) v t + (pairShare (1 / 2) v t)⁻¹ := by
  exact
    problem6RightSum_half_eq_leftSum_half_add_inv_pairShare_of_pivot_succ_reverse
      (v := v) (t := t) hpos hsucc

/--
Appendix D, Lemma 10 exact-center case: the closed-form denominator simplifies
to `1 + L_t`.
-/
theorem paper_lemma10_ClosedDenominator_half_center_eq_one_add_LeftSum
    {n : ℕ} {v : Item n → ℝ} {t : Item n}
    (hpos : ∀ j : Item n, 0 < v j)
    (hcenter : t.val = (reverseItem t).val) :
    problem6ClosedDenominator (1 / 2) v t =
      1 + problem6LeftSum (1 / 2) v t := by
  exact problem6ClosedDenominator_half_center_eq_one_add_leftSum
    (v := v) (t := t) hpos hcenter

/--
Appendix D, Lemma 10 even-center case: the closed-form denominator equals the
right inverse-share sum.
-/
theorem paper_lemma10_ClosedDenominator_half_succ_center_eq_RightSum
    {n : ℕ} {v : Item n → ℝ} {t : Item n}
    (hpos : ∀ j : Item n, 0 < v j)
    (hsucc : t.val + 1 = (reverseItem t).val) :
    problem6ClosedDenominator (1 / 2) v t =
      problem6RightSum (1 / 2) v t := by
  exact problem6ClosedDenominator_half_succ_center_eq_rightSum
    (v := v) (t := t) hpos hsucc

/--
Appendix D, Lemma 10 exact-center case: the midpoint Lemma 5 construction has
the denominator bounds needed for nonnegative pivot masses.
-/
theorem paper_lemma10_ClosedPivotDenominatorBounds_half_center
    {n : ℕ} {v : Item n → ℝ} {t : Item n}
    (hpos : ∀ j : Item n, 0 < v j)
    (hcenter : t.val = (reverseItem t).val) :
    Problem6ClosedPivotDenominatorBounds (1 / 2) v t := by
  exact problem6ClosedPivotDenominatorBounds_half_center
    (v := v) (t := t) hpos hcenter

/--
Appendix D, Lemma 10 even-center case: the midpoint Lemma 5 construction has
the denominator bounds needed for nonnegative pivot masses.
-/
theorem paper_lemma10_ClosedPivotDenominatorBounds_half_succ_center
    {n : ℕ} {v : Item n → ℝ} {t : Item n}
    (hpos : ∀ j : Item n, 0 < v j)
    (hsucc : t.val + 1 = (reverseItem t).val) :
    Problem6ClosedPivotDenominatorBounds (1 / 2) v t := by
  exact problem6ClosedPivotDenominatorBounds_half_succ_center
    (v := v) (t := t) hpos hsucc

/--
Appendix D, Lemma 4 comparison core: a sparse equalized solution with a pivot
to the right of another sparse equalized candidate cannot have a larger value
under the paper's nonnegativity side conditions.
-/
theorem paper_lemma4_sparseEqualized_value_le_of_candidate_before_general
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {c t : Item n}
    {x y x' y' : Item n → ℝ} {ell ell' : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hct : c.val < t.val)
    (h : Problem6SparseEqualized alpha v t x y ell)
    (hcand : Problem6SparseEqualized alpha v c x' y' ell')
    (hx_nonneg : ∀ j : Item n, 0 ≤ x j)
    (hy'_pivot_nonneg : 0 ≤ y' c) :
    ell ≤ ell' := by
  exact problem6SparseEqualized_value_le_of_candidate_before_general
    halpha0 halpha1 hpos hct h hcand hx_nonneg hy'_pivot_nonneg

/--
Appendix D, Lemma 10 comparison core: a sparse equalized solution with a pivot
to the right of another sparse equalized candidate cannot have a larger value
under the paper's nonnegativity side conditions.
-/
theorem paper_lemma10_sparseEqualized_value_le_of_candidate_before
    {n : ℕ} {v : Item n → ℝ} {c t : Item n}
    {x y x' y' : Item n → ℝ} {ell ell' : ℝ}
    (hpos : ∀ j : Item n, 0 < v j)
    (hct : c.val < t.val)
    (h : Problem6SparseEqualized (1 / 2) v t x y ell)
    (hcand : Problem6SparseEqualized (1 / 2) v c x' y' ell')
    (hx_nonneg : ∀ j : Item n, 0 ≤ x j)
    (hy'_pivot_nonneg : 0 ≤ y' c) :
    ell ≤ ell' := by
  exact problem6SparseEqualized_value_le_of_candidate_before
    hpos hct h hcand hx_nonneg hy'_pivot_nonneg

/--
Appendix D, Lemma 4 comparison for Lemma 5 closed forms: a nonnegative
closed-form pivot to the right of a nonnegative closed-form candidate cannot
have a larger value.
-/
theorem paper_lemma4_closedValue_le_of_closed_candidate_before_general
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {c t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hct : c.val < t.val)
    (hpivot : Problem6ClosedNonnegativePivots alpha v t)
    (hcandidate : Problem6ClosedNonnegativePivots alpha v c) :
    problem6ClosedValue alpha v t ≤
      problem6ClosedValue alpha v c := by
  exact problem6ClosedValue_le_of_closed_candidate_before_general
    halpha0 halpha1 hpos hct hpivot hcandidate

/--
Appendix D, Lemma 10 comparison for Lemma 5 closed forms: a nonnegative
closed-form pivot to the right of a nonnegative closed-form candidate cannot
have a larger value.
-/
theorem paper_lemma10_closedValue_le_of_closed_candidate_before
    {n : ℕ} {v : Item n → ℝ} {c t : Item n}
    (hpos : ∀ j : Item n, 0 < v j)
    (hct : c.val < t.val)
    (hpivot : Problem6ClosedNonnegativePivots (1 / 2) v t)
    (hcandidate : Problem6ClosedNonnegativePivots (1 / 2) v c) :
    problem6ClosedValue (1 / 2) v t ≤
      problem6ClosedValue (1 / 2) v c := by
  exact problem6ClosedValue_le_of_closed_candidate_before
    hpos hct hpivot hcandidate

/--
Appendix D, Lemma 10 exact-center comparison: a nonnegative closed-form pivot
strictly after an exact center candidate has value no larger than that candidate.
-/
theorem paper_lemma10_closedValue_le_of_center_candidate_before
    {n : ℕ} {v : Item n → ℝ} {c t : Item n}
    (hpos : ∀ j : Item n, 0 < v j)
    (hcenter : c.val = (reverseItem c).val)
    (hct : c.val < t.val)
    (hpivot : Problem6ClosedNonnegativePivots (1 / 2) v t) :
    problem6ClosedValue (1 / 2) v t ≤
      problem6ClosedValue (1 / 2) v c := by
  exact problem6ClosedValue_le_of_center_candidate_before
    hpos hcenter hct hpivot

/--
Appendix D, Lemma 10 even-center comparison: a nonnegative closed-form pivot
strictly after the candidate immediately before its mirror has value no larger
than that candidate.
-/
theorem paper_lemma10_closedValue_le_of_succ_center_candidate_before
    {n : ℕ} {v : Item n → ℝ} {c t : Item n}
    (hpos : ∀ j : Item n, 0 < v j)
    (hsucc : c.val + 1 = (reverseItem c).val)
    (hct : c.val < t.val)
    (hpivot : Problem6ClosedNonnegativePivots (1 / 2) v t) :
    problem6ClosedValue (1 / 2) v t ≤
      problem6ClosedValue (1 / 2) v c := by
  exact problem6ClosedValue_le_of_succ_center_candidate_before
    hpos hsucc hct hpivot

/--
Appendix D, Lemma 10 selected-pivot bridge at `α = 1/2`, odd-center case:
an equalized optimal Problem 6 policy cannot select a pivot after an exact
center candidate.
-/
theorem paper_lemma10_half_optimal_lastActive_le_center
    {n : ℕ} [NeZero n]
    {v : Item n → ℝ} {ρ : TypePolicy 2 n} {ell : ℝ} {c : Item n}
    (hn : 2 < n)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter : c.val = (reverseItem c).val)
    (hitem_eq :
      ∀ l : Item n,
        pairShare (1 / 2) v l * (ρ 0 l).toReal +
          (1 - pairShare (1 / 2) v l) * (ρ 1 l).toReal = ell)
    (hopt : Problem6PolicyOptimal (1 / 2) v ρ ell)
    (hshared : TypePolicy.SharedItemsBound ρ) :
    (TypePolicy.lastActiveTypeZero ρ).val ≤ c.val := by
  exact lemma10_half_optimal_lastActive_le_center
    hn hpos hdec hcenter hitem_eq hopt hshared

/--
Appendix D, Lemma 10 selected-pivot bridge at `α = 1/2`, even-center case:
an equalized optimal Problem 6 policy cannot select a pivot after the candidate
immediately before its mirror.
-/
theorem paper_lemma10_half_optimal_lastActive_le_succ_center
    {n : ℕ} [NeZero n]
    {v : Item n → ℝ} {ρ : TypePolicy 2 n} {ell : ℝ} {c : Item n}
    (hn : 2 < n)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hsucc : c.val + 1 = (reverseItem c).val)
    (hitem_eq :
      ∀ l : Item n,
        pairShare (1 / 2) v l * (ρ 0 l).toReal +
          (1 - pairShare (1 / 2) v l) * (ρ 1 l).toReal = ell)
    (hopt : Problem6PolicyOptimal (1 / 2) v ρ ell)
    (hshared : TypePolicy.SharedItemsBound ρ) :
    (TypePolicy.lastActiveTypeZero ρ).val ≤ c.val := by
  exact lemma10_half_optimal_lastActive_le_succ_center
    hn hpos hdec hsucc hitem_eq hopt hshared

/--
Appendix D, Lemma 10 stitched with Lemma 7, odd-center case: for
`α ≤ 1/2`, the selected pivot is no later than the exact center, conditional on
a supplied equalized optimum at the midpoint.
-/
theorem paper_lemma10_alpha_le_half_optimal_lastActive_le_center
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ}
    {ρ ρhalf : TypePolicy 2 n} {ell ellHalf : ℝ} {c : Item n}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha_half : alpha ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter : c.val = (reverseItem c).val)
    (hitem_eq :
      ∀ l : Item n,
        pairShare alpha v l * (ρ 0 l).toReal +
          (1 - pairShare alpha v l) * (ρ 1 l).toReal = ell)
    (hitem_eq_half :
      ∀ l : Item n,
        pairShare (1 / 2) v l * (ρhalf 0 l).toReal +
          (1 - pairShare (1 / 2) v l) * (ρhalf 1 l).toReal = ellHalf)
    (hopt : Problem6PolicyOptimal alpha v ρ ell)
    (hopt_half : Problem6PolicyOptimal (1 / 2) v ρhalf ellHalf)
    (hshared : TypePolicy.SharedItemsBound ρ)
    (hshared_half : TypePolicy.SharedItemsBound ρhalf) :
    (TypePolicy.lastActiveTypeZero ρ).val ≤ c.val := by
  exact lemma10_alpha_le_half_optimal_lastActive_le_center
    hn halpha0 halpha1 halpha_half hpos hdec hcenter
    hitem_eq hitem_eq_half hopt hopt_half hshared hshared_half

/--
Appendix D, Lemma 10 stitched with Lemma 7, even-center case: for
`α ≤ 1/2`, the selected pivot is no later than the item immediately before its
mirror, conditional on a supplied equalized optimum at the midpoint.
-/
theorem paper_lemma10_alpha_le_half_optimal_lastActive_le_succ_center
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ}
    {ρ ρhalf : TypePolicy 2 n} {ell ellHalf : ℝ} {c : Item n}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha_half : alpha ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hsucc : c.val + 1 = (reverseItem c).val)
    (hitem_eq :
      ∀ l : Item n,
        pairShare alpha v l * (ρ 0 l).toReal +
          (1 - pairShare alpha v l) * (ρ 1 l).toReal = ell)
    (hitem_eq_half :
      ∀ l : Item n,
        pairShare (1 / 2) v l * (ρhalf 0 l).toReal +
          (1 - pairShare (1 / 2) v l) * (ρhalf 1 l).toReal = ellHalf)
    (hopt : Problem6PolicyOptimal alpha v ρ ell)
    (hopt_half : Problem6PolicyOptimal (1 / 2) v ρhalf ellHalf)
    (hshared : TypePolicy.SharedItemsBound ρ)
    (hshared_half : TypePolicy.SharedItemsBound ρhalf) :
    (TypePolicy.lastActiveTypeZero ρ).val ≤ c.val := by
  exact lemma10_alpha_le_half_optimal_lastActive_le_succ_center
    hn halpha0 halpha1 halpha_half hpos hdec hsucc
    hitem_eq hitem_eq_half hopt hopt_half hshared hshared_half

/--
Appendix D, Lemma 10 stitched with Lemma 7 for the paper's equality-form
optimal BFS package, odd-center case.
-/
theorem paper_lemma10_alpha_le_half_equalizedBasicOptimal_lastActive_le_center
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ}
    {ρ ρhalf : TypePolicy 2 n} {ell ellHalf : ℝ} {c : Item n}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha_half : alpha ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter : c.val = (reverseItem c).val)
    (h : Problem6EqualizedBasicOptimal alpha v ρ ell)
    (hhalf : Problem6EqualizedBasicOptimal (1 / 2) v ρhalf ellHalf) :
    (TypePolicy.lastActiveTypeZero ρ).val ≤ c.val := by
  exact lemma10_alpha_le_half_equalizedBasicOptimal_lastActive_le_center
    hn halpha0 halpha1 halpha_half hpos hdec hcenter h hhalf

/--
Appendix D, Lemma 10 stitched with Lemma 7 for the paper's equality-form
optimal BFS package, even-center case.
-/
theorem paper_lemma10_alpha_le_half_equalizedBasicOptimal_lastActive_le_succ_center
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ}
    {ρ ρhalf : TypePolicy 2 n} {ell ellHalf : ℝ} {c : Item n}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha_half : alpha ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hsucc : c.val + 1 = (reverseItem c).val)
    (h : Problem6EqualizedBasicOptimal alpha v ρ ell)
    (hhalf : Problem6EqualizedBasicOptimal (1 / 2) v ρhalf ellHalf) :
    (TypePolicy.lastActiveTypeZero ρ).val ≤ c.val := by
  exact lemma10_alpha_le_half_equalizedBasicOptimal_lastActive_le_succ_center
    hn halpha0 halpha1 halpha_half hpos hdec hsucc h hhalf

/--
Appendix D, Lemma 10 for the paper's equality-form optimal BFS package,
odd-center case, with the midpoint optimum supplied by the Lemma 5 closed form.
-/
theorem paper_lemma10_alpha_le_half_equalizedBasicOptimal_lastActive_le_center_of_closed_half
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ}
    {ρ : TypePolicy 2 n} {ell : ℝ} {c : Item n}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha_half : alpha ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter : c.val = (reverseItem c).val)
    (h : Problem6EqualizedBasicOptimal alpha v ρ ell) :
    (TypePolicy.lastActiveTypeZero ρ).val ≤ c.val := by
  exact lemma10_alpha_le_half_equalizedBasicOptimal_lastActive_le_center_of_closed_half
    hn halpha0 halpha1 halpha_half hpos hdec hcenter h

/--
Appendix D, Lemma 10 for the paper's equality-form optimal BFS package,
even-center case, with the midpoint optimum supplied by the Lemma 5 closed form.
-/
theorem paper_lemma10_alpha_le_half_equalizedBasicOptimal_lastActive_le_succ_center_of_closed_half
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ}
    {ρ : TypePolicy 2 n} {ell : ℝ} {c : Item n}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha_half : alpha ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hsucc : c.val + 1 = (reverseItem c).val)
    (h : Problem6EqualizedBasicOptimal alpha v ρ ell) :
    (TypePolicy.lastActiveTypeZero ρ).val ≤ c.val := by
  exact lemma10_alpha_le_half_equalizedBasicOptimal_lastActive_le_succ_center_of_closed_half
    hn halpha0 halpha1 halpha_half hpos hdec hsucc h

/--
Appendix D, Lemma 10 consequence, odd-center case: for `α ≤ 1/2`, the
selected pivot is at or before its mirror.
-/
theorem paper_lemma10_alpha_le_half_equalizedBasicOptimal_lastActive_le_reverse_center
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ}
    {ρ ρhalf : TypePolicy 2 n} {ell ellHalf : ℝ} {c : Item n}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha_half : alpha ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter : c.val = (reverseItem c).val)
    (h : Problem6EqualizedBasicOptimal alpha v ρ ell)
    (hhalf : Problem6EqualizedBasicOptimal (1 / 2) v ρhalf ellHalf) :
    (TypePolicy.lastActiveTypeZero ρ).val ≤
      (reverseItem (TypePolicy.lastActiveTypeZero ρ)).val := by
  exact lemma10_alpha_le_half_equalizedBasicOptimal_lastActive_le_reverse_center
    hn halpha0 halpha1 halpha_half hpos hdec hcenter h hhalf

/--
Appendix D, Lemma 10 consequence, even-center case: for `α ≤ 1/2`, the
selected pivot is at or before its mirror.
-/
theorem paper_lemma10_alpha_le_half_equalizedBasicOptimal_lastActive_le_reverse_succ_center
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ}
    {ρ ρhalf : TypePolicy 2 n} {ell ellHalf : ℝ} {c : Item n}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha_half : alpha ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hsucc : c.val + 1 = (reverseItem c).val)
    (h : Problem6EqualizedBasicOptimal alpha v ρ ell)
    (hhalf : Problem6EqualizedBasicOptimal (1 / 2) v ρhalf ellHalf) :
    (TypePolicy.lastActiveTypeZero ρ).val ≤
      (reverseItem (TypePolicy.lastActiveTypeZero ρ)).val := by
  exact lemma10_alpha_le_half_equalizedBasicOptimal_lastActive_le_reverse_succ_center
    hn halpha0 halpha1 halpha_half hpos hdec hsucc h hhalf

/--
Appendix D, Lemma 10 consequence, odd-center case, with the midpoint optimum
supplied by the Lemma 5 closed form.
-/
theorem paper_lemma10_alpha_le_half_equalizedBasicOptimal_lastActive_le_reverse_center_of_closed_half
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ}
    {ρ : TypePolicy 2 n} {ell : ℝ} {c : Item n}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha_half : alpha ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter : c.val = (reverseItem c).val)
    (h : Problem6EqualizedBasicOptimal alpha v ρ ell) :
    (TypePolicy.lastActiveTypeZero ρ).val ≤
      (reverseItem (TypePolicy.lastActiveTypeZero ρ)).val := by
  exact lemma10_alpha_le_half_equalizedBasicOptimal_lastActive_le_reverse_center_of_closed_half
    hn halpha0 halpha1 halpha_half hpos hdec hcenter h

/--
Appendix D, Lemma 10 consequence, even-center case, with the midpoint optimum
supplied by the Lemma 5 closed form.
-/
theorem paper_lemma10_alpha_le_half_equalizedBasicOptimal_lastActive_le_reverse_succ_center_of_closed_half
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ}
    {ρ : TypePolicy 2 n} {ell : ℝ} {c : Item n}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha_half : alpha ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hsucc : c.val + 1 = (reverseItem c).val)
    (h : Problem6EqualizedBasicOptimal alpha v ρ ell) :
    (TypePolicy.lastActiveTypeZero ρ).val ≤
      (reverseItem (TypePolicy.lastActiveTypeZero ρ)).val := by
  exact lemma10_alpha_le_half_equalizedBasicOptimal_lastActive_le_reverse_succ_center_of_closed_half
    hn halpha0 halpha1 halpha_half hpos hdec hsucc h

/--
Appendix D, Lemma 6/10 bridge: an exact midpoint candidate has zero pivot
mirror gap.
-/
theorem paper_lemma10_closedX_sub_closedY_reverse_half_center_eq_zero
    {n : ℕ} {v : Item n → ℝ} {t : Item n}
    (hpos : ∀ j : Item n, 0 < v j)
    (hcenter : t.val = (reverseItem t).val) :
    problem6ClosedX (1 / 2) v t t -
      problem6ClosedY (1 / 2) v t (reverseItem t) = 0 := by
  exact problem6ClosedX_sub_closedY_reverse_half_center_eq_zero
    hpos hcenter

/--
Appendix D, Lemma 6/10 bridge: an exact midpoint candidate satisfies the
nonnegative pivot-gap condition used by Lemma 6.
-/
theorem paper_lemma10_closedX_sub_closedY_reverse_half_center_nonneg
    {n : ℕ} {v : Item n → ℝ} {t : Item n}
    (hpos : ∀ j : Item n, 0 < v j)
    (hcenter : t.val = (reverseItem t).val) :
    0 ≤ problem6ClosedX (1 / 2) v t t -
      problem6ClosedY (1 / 2) v t (reverseItem t) := by
  exact problem6ClosedX_sub_closedY_reverse_half_center_nonneg
    hpos hcenter

/--
Appendix D, Lemma 6/10 bridge: an even midpoint candidate has zero pivot
mirror gap.
-/
theorem paper_lemma10_closedX_sub_closedY_reverse_half_succ_center_eq_zero
    {n : ℕ} {v : Item n → ℝ} {t : Item n}
    (hpos : ∀ j : Item n, 0 < v j)
    (hsucc : t.val + 1 = (reverseItem t).val) :
    problem6ClosedX (1 / 2) v t t -
      problem6ClosedY (1 / 2) v t (reverseItem t) = 0 := by
  exact problem6ClosedX_sub_closedY_reverse_half_succ_center_eq_zero
    hpos hsucc

/--
Appendix D, Lemma 6/10 bridge: an even midpoint candidate satisfies the
nonnegative pivot-gap condition used by Lemma 6.
-/
theorem paper_lemma10_closedX_sub_closedY_reverse_half_succ_center_nonneg
    {n : ℕ} {v : Item n → ℝ} {t : Item n}
    (hpos : ∀ j : Item n, 0 < v j)
    (hsucc : t.val + 1 = (reverseItem t).val) :
    0 ≤ problem6ClosedX (1 / 2) v t t -
      problem6ClosedY (1 / 2) v t (reverseItem t) := by
  exact problem6ClosedX_sub_closedY_reverse_half_succ_center_nonneg
    hpos hsucc

/--
Appendix D, Lemma 6/10 bridge: the exact midpoint closed policy has type
fairness equal to type `1`'s normalized utility.
-/
theorem paper_lemma10_closedPolicy_typeFairness_eq_one_half_center
    {n : ℕ} [NeZero n] {v : Item n → ℝ} {t : Item n}
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter : t.val = (reverseItem t).val) :
    let hpivot : Problem6ClosedNonnegativePivots (1 / 2) v t :=
      problem6ClosedNonnegativePivots_of_denominatorBounds
        (by norm_num : (0 : ℝ) < 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1) hpos
        (problem6ClosedPivotDenominatorBounds_half_center
          (v := v) (t := t) hpos hcenter)
    TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel (1 / 2) v)
        (problem6ClosedPolicy (1 / 2) v t
          (by norm_num : (0 : ℝ) < 1 / 2)
          (by norm_num : (1 / 2 : ℝ) < 1) hpos hpivot) =
      TypeWeightedRecommendationModel.normalizedTypeUtility
        (twoTypeReducedModel (1 / 2) v)
        (problem6ClosedPolicy (1 / 2) v t
          (by norm_num : (0 : ℝ) < 1 / 2)
          (by norm_num : (1 / 2 : ℝ) < 1) hpos hpivot) 1 := by
  exact problem6ClosedPolicy_typeFairness_eq_one_half_center
    hpos hdec hcenter

/--
Appendix D, Lemma 6/10 bridge: the even midpoint closed policy has type
fairness equal to type `1`'s normalized utility.
-/
theorem paper_lemma10_closedPolicy_typeFairness_eq_one_half_succ_center
    {n : ℕ} [NeZero n] {v : Item n → ℝ} {t : Item n}
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hsucc : t.val + 1 = (reverseItem t).val) :
    let hpivot : Problem6ClosedNonnegativePivots (1 / 2) v t :=
      problem6ClosedNonnegativePivots_of_denominatorBounds
        (by norm_num : (0 : ℝ) < 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1) hpos
        (problem6ClosedPivotDenominatorBounds_half_succ_center
          (v := v) (t := t) hpos hsucc)
    TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel (1 / 2) v)
        (problem6ClosedPolicy (1 / 2) v t
          (by norm_num : (0 : ℝ) < 1 / 2)
          (by norm_num : (1 / 2 : ℝ) < 1) hpos hpivot) =
      TypeWeightedRecommendationModel.normalizedTypeUtility
        (twoTypeReducedModel (1 / 2) v)
        (problem6ClosedPolicy (1 / 2) v t
          (by norm_num : (0 : ℝ) < 1 / 2)
          (by norm_num : (1 / 2 : ℝ) < 1) hpos hpivot) 1 := by
  exact problem6ClosedPolicy_typeFairness_eq_one_half_succ_center
    hpos hdec hsucc

/--
Appendix E / Theorem 4 true-model benchmark, odd midpoint case: without
misestimation, the maximal item-fairness reduced user optimum is strictly above
`1/n` at `α = 1/2`.
-/
theorem paper_theorem4_trueModel_optimalTypeFairnessAtLevel_one_gt_inv_card_half_center
    {n : ℕ} [NeZero n] {v : Item n → ℝ} {t : Item n}
    (hn : 1 < n)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter : t.val = (reverseItem t).val) :
    (n : ℝ)⁻¹ <
      TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel (1 / 2) v) 1 := by
  exact theorem4_trueModel_optimalTypeFairnessAtLevel_one_gt_inv_card_half_center
    hn hpos hdec hcenter

/--
Appendix E / Theorem 4 true-model benchmark, even midpoint case: without
misestimation, the maximal item-fairness reduced user optimum is strictly above
`1/n` at `α = 1/2`.
-/
theorem paper_theorem4_trueModel_optimalTypeFairnessAtLevel_one_gt_inv_card_half_succ_center
    {n : ℕ} [NeZero n] {v : Item n → ℝ} {t : Item n}
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hsucc : t.val + 1 = (reverseItem t).val) :
    (n : ℝ)⁻¹ <
      TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel (1 / 2) v) 1 := by
  exact theorem4_trueModel_optimalTypeFairnessAtLevel_one_gt_inv_card_half_succ_center
    hpos hdec hsucc

/--
Appendix E, Lemma 12: any estimated `γ = 1` optimum can be replaced by a
mirror-symmetric optimum in the paper's subspace `S'`.
-/
theorem paper_lemma12_theorem4_symmetrizedPolicy_isOptimalAtLevel
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
  exact OpposingTypes.theorem4_symmetrizedPolicy_isOptimalAtLevel
    hpos hopt

/--
Appendix E, Problem 11 translation: inside the mirror-symmetric subspace `S'`,
the estimated normalized item utilities are exactly the paper's linear
`x,z,λ` expressions.
-/
theorem paper_problem11_normalizedItemUtility_eq
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hpos : ∀ j : Item n, 0 < v j)
    {ρ : TypePolicy 3 n}
    (hsym : Theorem4MirrorSymmetricPolicy ρ)
    (j : Item n) :
    TypeWeightedRecommendationModel.normalizedItemUtility
        (theorem4EstimatedReducedModel beta v) ρ j =
      theorem4Problem11PolicyItemValue beta v ρ j := by
  exact theorem4EstimatedReducedModel_normalizedItemUtility_eq_problem11
    hpos hsym j

/--
Appendix E, Problem 11 optimality bridge: a mirror-symmetric estimated
`γ = 1` optimum solves the paper's Problem 11 epigraph LP.
-/
theorem paper_problem11_policyOptimal_of_isOptimalAtLevel
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
  exact theorem4Problem11PolicyOptimal_of_isOptimalAtLevel
    hbeta hcold hpos hsym hopt

/--
Appendix E, Problem 11 real-vector feasibility extracted from a
mirror-symmetric policy satisfying the paper's epigraph constraints.
-/
theorem paper_problem11_realLPFeasible_of_policy
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    {ρ : TypePolicy 3 n} {ell : ℝ}
    (hsym : Theorem4MirrorSymmetricPolicy ρ)
    (hfeas : theorem4Problem11LPFeasible beta v ρ ell) :
    Theorem4Problem11RealLPFeasible beta v
      (fun j : Item n => (ρ 0 j).toReal)
      (fun j : Item n => (ρ 2 j).toReal) ell := by
  exact theorem4Problem11RealLPFeasible_of_policy hsym hfeas

/--
Appendix E, Problem 11 weak-duality interface: finite symmetric item
multipliers upper-bound every feasible real `x,z,λ` solution.
-/
theorem paper_problem11_dualCertificate_upper_bound
    {n : ℕ} {beta : ℝ} {v : Item n → ℝ}
    (hpos : ∀ j : Item n, 0 < v j)
    {w : Item n → ℝ} {A B ell : ℝ}
    (cert : Theorem4Problem11DualCertificate beta v w A B ell)
    {x z : Item n → ℝ} {ell' : ℝ}
    (hfeas : Theorem4Problem11RealLPFeasible beta v x z ell') :
    ell' ≤ ell := by
  exact theorem4Problem11DualCertificate_upper_bound hpos cert hfeas

/--
Appendix E, Problem 11 closed-form dual certificate for any pivot on the
left half of the item line.
-/
theorem paper_problem11_closedDualCertificate
    {n : ℕ} {beta : ℝ} {v : Item n → ℝ} {t : Item n}
    (hbeta : 0 ≤ beta) (hcold : 0 ≤ 1 - 2 * beta)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hleft : t.val ≤ (reverseItem t).val) :
    Theorem4Problem11DualCertificate beta v
      (theorem4Problem11ClosedDualWeight v t)
      (theorem4Problem11ClosedKnownBudget beta v t)
      (theorem4Problem11ClosedColdBudget beta v t)
      (theorem4Problem11ClosedDualValue beta v t) := by
  exact theorem4Problem11ClosedDualCertificate
    hbeta hcold hpos hdec hleft

/--
Appendix E, Problem 11 closed-form dual upper bound: every feasible real
solution has `λ` at most the closed dual value for any left-half pivot.
-/
theorem paper_problem11_closedDual_upper_bound
    {n : ℕ} {beta : ℝ} {v : Item n → ℝ} {t : Item n}
    (hbeta : 0 ≤ beta) (hcold : 0 ≤ 1 - 2 * beta)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hleft : t.val ≤ (reverseItem t).val)
    {x z : Item n → ℝ} {ell : ℝ}
    (hfeas : Theorem4Problem11RealLPFeasible beta v x z ell) :
    ell ≤ theorem4Problem11ClosedDualValue beta v t := by
  exact theorem4Problem11ClosedDual_upper_bound
    hbeta hcold hpos hdec hleft hfeas

/--
Appendix E, Problem 11 closed-dual denominator identity in the paper's
full mirrored-policy convention.
-/
theorem paper_problem11_closedDualDenominator_eq
    {n : ℕ} {v : Item n → ℝ} {t : Item n}
    (hleft : t.val ≤ (reverseItem t).val) :
    theorem4Problem11ClosedDualDenominator v t =
      2 * pairShare (1 / 2) v t * theorem4Problem11LeftSum v t +
        ((n : ℝ) - 2 * (t.val : ℝ)) := by
  exact theorem4Problem11ClosedDualDenominator_eq hleft

/--
Appendix E, Problem 11 closed-dual value identity matching Lemma 15's
full-policy denominator.
-/
theorem paper_problem11_closedDualValue_eq_fullPolicy_formula
    {n : ℕ} {beta : ℝ} {v : Item n → ℝ} {t : Item n}
    (hleft : t.val ≤ (reverseItem t).val) :
    theorem4Problem11ClosedDualValue beta v t =
      (4 * beta * pairShare (1 / 2) v t + (1 - 2 * beta)) /
        (2 * pairShare (1 / 2) v t * theorem4Problem11LeftSum v t +
          ((n : ℝ) - 2 * (t.val : ℝ))) := by
  exact theorem4Problem11ClosedDualValue_eq_fullPolicy_formula hleft

/--
Appendix E, Problem 11 closed primal witness: the closed `x,z` coordinates
equalize every item at the closed dual value.
-/
theorem paper_problem11_closed_item_eq
    {n : ℕ} {beta : ℝ} {v : Item n → ℝ} {t : Item n}
    (hbeta_pos : 0 < beta)
    (hbeta_half : beta < 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hleft : t.val ≤ (reverseItem t).val) :
    ∀ j : Item n,
      theorem4Problem11ItemValue beta v
        (theorem4Problem11ClosedX beta v t)
        (theorem4Problem11ClosedZ beta v t) j =
          theorem4Problem11ClosedDualValue beta v t := by
  exact theorem4Problem11Closed_item_eq
    hbeta_pos hbeta_half hpos hleft

/--
Appendix E, Problem 11 closed primal witness feasibility, conditional only on
the two pivot nonnegativity inequalities.
-/
theorem paper_problem11_closed_realLPFeasible
    {n : ℕ} {beta : ℝ} {v : Item n → ℝ} {t : Item n}
    (hbeta_pos : 0 < beta)
    (hbeta_half : beta < 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hleft : t.val ≤ (reverseItem t).val)
    (hpivot : 0 ≤ theorem4Problem11ClosedX beta v t t)
    (hendpoint : 0 ≤ theorem4Problem11ClosedZEndpointMass beta v t) :
    Theorem4Problem11RealLPFeasible beta v
      (theorem4Problem11ClosedX beta v t)
      (theorem4Problem11ClosedZ beta v t)
      (theorem4Problem11ClosedDualValue beta v t) := by
  exact theorem4Problem11Closed_realLPFeasible
    hbeta_pos hbeta_half hpos hleft hpivot hendpoint

/--
Appendix E, Problem 11 closed policy pivot-support shape.
-/
theorem paper_problem11_closedPolicy_pivotSupport
    {n : ℕ} {beta : ℝ} {v : Item n → ℝ} {t : Item n}
    (hbeta_pos : 0 < beta)
    (hbeta_half : beta < 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hleft : t.val ≤ (reverseItem t).val)
    (hpivot : 0 ≤ theorem4Problem11ClosedX beta v t t)
    (hendpoint : 0 ≤ theorem4Problem11ClosedZEndpointMass beta v t) :
    Theorem4Problem11PivotSupport
      (theorem4Problem11ClosedPolicy beta v t
        hbeta_pos hbeta_half hpos hleft hpivot hendpoint) t := by
  exact theorem4Problem11ClosedPolicy_pivotSupport
    hbeta_pos hbeta_half hpos hleft hpivot hendpoint

/--
Appendix E, Problem 11 denominator-style pivot bounds imply the two
nonnegativity facts needed by the closed primal witness.
-/
theorem paper_problem11_closed_nonnegativePivots_of_bounds
    {n : ℕ} {beta : ℝ} {v : Item n → ℝ} {t : Item n}
    (hbeta_pos : 0 < beta)
    (hbeta_half : beta < 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hleft : t.val ≤ (reverseItem t).val)
    (hbounds : Theorem4Problem11ClosedPivotBounds beta v t) :
    0 ≤ theorem4Problem11ClosedX beta v t t ∧
      0 ≤ theorem4Problem11ClosedZEndpointMass beta v t := by
  exact theorem4Problem11Closed_nonnegativePivots_of_bounds
    hbeta_pos hbeta_half hpos hleft hbounds

/--
Appendix E, Problem 11 closed-policy support count: the explicit closed
policy is a basic-feasible support witness.
-/
theorem paper_problem11_closedPolicy_basicFeasibleSupportCertificate
    {n : ℕ} {beta : ℝ} {v : Item n → ℝ} {t : Item n}
    (hbeta_pos : 0 < beta)
    (hbeta_half : beta < 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hleft : t.val ≤ (reverseItem t).val)
    (hpivot : 0 ≤ theorem4Problem11ClosedX beta v t t)
    (hendpoint : 0 ≤ theorem4Problem11ClosedZEndpointMass beta v t) :
    TypePolicy.BasicFeasibleSupportCertificate
      (theorem4Problem11ClosedPolicy beta v t
        hbeta_pos hbeta_half hpos hleft hpivot hendpoint) := by
  exact theorem4Problem11ClosedPolicy_basicFeasibleSupportCertificate
    hbeta_pos hbeta_half hpos hleft hpivot hendpoint

/--
Appendix E, Problem 11 closed primal/dual tightness bridge from a bounded
pivot.  The closed policy supplies its own basic-support certificate.
-/
theorem paper_problem11_equalityFormOptimalBFS_of_closed_bounds
    {n : ℕ} {beta : ℝ} {v : Item n → ℝ} {t : Item n}
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
  exact theorem4Problem11EqualityFormOptimalBFS_of_closed_bounds
    hbeta_pos hbeta_half hpos hdec hleft hbounds

/--
Appendix E, Problem 11 finite crossing: in the odd-center case there exists a
closed-form equality-form optimal BFS witness.
-/
theorem paper_problem11_equalityFormOptimalBFS_exists_closed_of_center
    {n : ℕ} {beta : ℝ} {v : Item n → ℝ} {c : Item n}
    (hbeta_pos : 0 < beta)
    (hbeta_half : beta < 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter : c.val = (reverseItem c).val) :
    ∃ t : Item n,
      Theorem4Problem11EqualityFormOptimalBFS beta v
        (theorem4Problem11ClosedX beta v t)
        (theorem4Problem11ClosedZ beta v t)
        (theorem4Problem11ClosedDualValue beta v t) := by
  exact theorem4Problem11EqualityFormOptimalBFS_exists_closed_of_center
    hbeta_pos hbeta_half hpos hdec hcenter

/--
Appendix E, Problem 11 finite crossing: in the even-center case there exists a
closed-form equality-form optimal BFS witness.
-/
theorem paper_problem11_equalityFormOptimalBFS_exists_closed_of_succ_center
    {n : ℕ} {beta : ℝ} {v : Item n → ℝ} {c : Item n}
    (hbeta_pos : 0 < beta)
    (hbeta_half : beta < 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hsucc : c.val + 1 = (reverseItem c).val) :
    ∃ t : Item n,
      Theorem4Problem11EqualityFormOptimalBFS beta v
        (theorem4Problem11ClosedX beta v t)
        (theorem4Problem11ClosedZ beta v t)
        (theorem4Problem11ClosedDualValue beta v t) := by
  exact theorem4Problem11EqualityFormOptimalBFS_exists_closed_of_succ_center
    hbeta_pos hbeta_half hpos hdec hsucc

/--
Appendix E, Problem 11 closed primal/dual tightness bridge from a bounded
pivot and a basic-support certificate.
-/
theorem paper_problem11_equalityFormOptimalBFS_of_closed_witness
    {n : ℕ} {beta : ℝ} {v : Item n → ℝ} {t : Item n}
    (hbeta_pos : 0 < beta)
    (hbeta_half : beta < 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hleft : t.val ≤ (reverseItem t).val)
    (hpivot : 0 ≤ theorem4Problem11ClosedX beta v t t)
    (hendpoint : 0 ≤ theorem4Problem11ClosedZEndpointMass beta v t)
    (hbasic :
      TypePolicy.BasicFeasibleSupportCertificate
        (theorem4Problem11ClosedPolicy beta v t
          hbeta_pos hbeta_half hpos hleft hpivot hendpoint)) :
    Theorem4Problem11EqualityFormOptimalBFS beta v
      (theorem4Problem11ClosedX beta v t)
      (theorem4Problem11ClosedZ beta v t)
      (theorem4Problem11ClosedDualValue beta v t) := by
  exact theorem4Problem11EqualityFormOptimalBFS_of_closed_witness
    hbeta_pos hbeta_half hpos hdec hleft hpivot hendpoint hbasic

/--
Appendix E, Problem 11 closed-dual tightness bridge: a real feasible solution
that equalizes all items at the closed dual value supplies the paper's
equality-form optimal BFS package.
-/
theorem paper_problem11_equalityFormOptimalBFS_of_closedDual_tight
    {n : ℕ} {beta : ℝ} {v x z : Item n → ℝ} {t : Item n}
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
      (theorem4Problem11ClosedDualValue beta v t) := by
  exact theorem4Problem11EqualityFormOptimalBFS_of_closedDual_tight
    hbeta hcold hpos hdec hleft hfeas hitem_eq hbasic

/--
Appendix E, Problem 11 bridge: an epigraph-optimal mirror-symmetric policy has
objective value equal to its reduced estimated item-fairness.
-/
theorem paper_problem11_policyOptimal_itemFairness_eq
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hpos : ∀ j : Item n, 0 < v j)
    {ρ : TypePolicy 3 n} {ell : ℝ}
    (hopt : Theorem4Problem11PolicyOptimal beta v ρ ell) :
    TypeWeightedRecommendationModel.itemFairness
        (theorem4EstimatedReducedModel beta v) ρ = ell := by
  exact theorem4Problem11PolicyOptimal_itemFairness_eq hpos hopt

/--
Appendix E, Problem 11 / Problem 1 bridge: every Problem 11 epigraph optimum
is feasible for the reduced estimated model at maximal item-fairness level
`γ = 1`.
-/
theorem paper_problem11_policyOptimal_feasibleAtLevel_one
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hbeta : 0 ≤ beta) (hcold : 0 ≤ 1 - 2 * beta)
    (hpos : ∀ j : Item n, 0 < v j)
    {ρ : TypePolicy 3 n} {ell : ℝ}
    (hopt : Theorem4Problem11PolicyOptimal beta v ρ ell) :
    TypeWeightedRecommendationModel.feasibleAtLevel
      (theorem4EstimatedReducedModel beta v) 1 ρ := by
  exact theorem4Problem11PolicyOptimal_feasibleAtLevel_one
    hbeta hcold hpos hopt

/--
Appendix E, Problem 11 / Problem 1 bridge in the other direction: a
mirror-symmetric policy feasible at maximal estimated item fairness solves
Problem 11 with objective equal to its item-fairness value.
-/
theorem paper_problem11_policyOptimal_of_feasibleAtLevel_one
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
  exact theorem4Problem11PolicyOptimal_of_feasibleAtLevel_one
    hbeta hcold hpos hsym hfeas

/--
Appendix E, Lemma 12 / Problem 11 bridge: any reduced estimated policy
feasible at maximal item fairness has a mirror-symmetrization that solves
Problem 11.
-/
theorem paper_problem11_policyOptimal_symmetrized_of_feasibleAtLevel_one
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
  exact theorem4Problem11PolicyOptimal_symmetrized_of_feasibleAtLevel_one
    hbeta hcold hpos hfeas

/--
Appendix E, Problem 11 / Problem 1 bridge for the equality-form package used
by Lemmas 13--15.
-/
theorem paper_problem11_equalizedBasicOptimal_feasibleAtLevel_one
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hbeta : 0 ≤ beta) (hcold : 0 ≤ 1 - 2 * beta)
    (hpos : ∀ j : Item n, 0 < v j)
    {ρ : TypePolicy 3 n} {ell : ℝ}
    (h : Theorem4Problem11EqualizedBasicOptimal beta v ρ ell) :
    TypeWeightedRecommendationModel.feasibleAtLevel
      (theorem4EstimatedReducedModel beta v) 1 ρ := by
  exact theorem4Problem11EqualizedBasicOptimal_feasibleAtLevel_one
    hbeta hcold hpos h

/--
Appendix E, Problem 11 / Problem 1 bridge for the paper's real equality-form
optimal BFS data after rebuilding the three-type policy.
-/
theorem paper_problem11_equalityFormOptimalBFS_feasibleAtLevel_one
    {n : ℕ} [NeZero n] {beta : ℝ} {v x z : Item n → ℝ} {ell : ℝ}
    (hbeta : 0 ≤ beta) (hcold : 0 ≤ 1 - 2 * beta)
    (hpos : ∀ j : Item n, 0 < v j)
    (h : Theorem4Problem11EqualityFormOptimalBFS beta v x z ell) :
    TypeWeightedRecommendationModel.feasibleAtLevel
      (theorem4EstimatedReducedModel beta v) 1
      (theorem4Problem11PolicyOfRealVectors x z
        h.feasible.x_nonneg h.feasible.z_nonneg
        h.feasible.sum_x h.feasible.sum_z) := by
  exact theorem4Problem11EqualityFormOptimalBFS_feasibleAtLevel_one
    hbeta hcold hpos h

/--
Appendix E, Problem 11 / estimated Problem 1 bridge: if the selected
equality-form Problem 11 optimum is the unique epigraph-optimal
mirror-symmetric policy, then it solves the reduced estimated `γ = 1`
user-fairness problem.
-/
theorem paper_problem11_equalizedBasicOptimal_isOptimalAtLevel_of_policyOptimal_unique
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
  exact theorem4Problem11EqualizedBasicOptimal_isOptimalAtLevel_of_policyOptimal_unique
    hbeta hcold hpos h hunique

/--
Appendix E, Problem 11 / estimated Problem 1 bridge using Lemma 14: if every
epigraph-optimal mirror-symmetric policy is represented by an equality-form
basic optimum, then the selected equality-form optimum solves the reduced
estimated `γ = 1` user-fairness problem.
-/
theorem paper_problem11_equalizedBasicOptimal_isOptimalAtLevel_of_equalized_selection
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
  exact theorem4Problem11EqualizedBasicOptimal_isOptimalAtLevel_of_equalized_selection
    hn hbeta_pos hbeta_half hpos hdec h hselection

/--
Appendix E, Problem 11 / estimated Problem 1 bridge after rebuilding a policy
from the paper's real equality-form optimal BFS data.
-/
theorem paper_problem11_equalityFormOptimalBFS_isOptimalAtLevel_of_equalized_selection
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
  exact theorem4Problem11EqualityFormOptimalBFS_isOptimalAtLevel_of_equalized_selection
    hn hbeta_pos hbeta_half hpos hdec h hselection

/--
Appendix E, Problem 11 equality-form extraction: the paper's real optimal BFS
data rebuilds an optimal mirror-symmetric three-type policy for the epigraph
LP.
-/
theorem paper_problem11_policyOptimal_of_equalityFormOptimalBFS
    {n : ℕ} [NeZero n] {beta : ℝ} {v x z : Item n → ℝ} {ell : ℝ}
    (h : Theorem4Problem11EqualityFormOptimalBFS beta v x z ell) :
    Theorem4Problem11PolicyOptimal beta v
      (theorem4Problem11PolicyOfRealVectors x z
        h.feasible.x_nonneg h.feasible.z_nonneg
        h.feasible.sum_x h.feasible.sum_z) ell := by
  exact theorem4Problem11PolicyOptimal_of_equalityFormOptimalBFS h

/--
Appendix E, Problem 11 equality-form extraction: the paper's real optimal BFS
supplies the `Theorem4Problem11EqualizedBasicOptimal` package consumed by
Lemmas 13--15 and Theorem 4.
-/
theorem paper_problem11_equalizedBasicOptimal_of_equalityFormOptimalBFS
    {n : ℕ} [NeZero n] {beta : ℝ} {v x z : Item n → ℝ} {ell : ℝ}
    (h : Theorem4Problem11EqualityFormOptimalBFS beta v x z ell) :
    Theorem4Problem11EqualizedBasicOptimal beta v
      (theorem4Problem11PolicyOfRealVectors x z
        h.feasible.x_nonneg h.feasible.z_nonneg
        h.feasible.sum_x h.feasible.sum_z) ell := by
  exact theorem4Problem11EqualizedBasicOptimal_of_equalityFormOptimalBFS h

/--
Appendix E, Problem 11 epigraph fact: an optimal `λ` equals the minimum of the
paper's item-value expressions.
-/
theorem paper_problem11_policyOptimal_value_eq_finiteMin
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    {ρ : TypePolicy 3 n} {ell : ℝ}
    (hopt : Theorem4Problem11PolicyOptimal beta v ρ ell) :
    ell =
      AppliedModelingLib.finiteMin
        (fun j : Item n => theorem4Problem11PolicyItemValue beta v ρ j) := by
  exact theorem4Problem11PolicyOptimal_value_eq_finiteMin hopt

/--
Appendix E, Lemma 13 proof component: every optimal Problem 11 epigraph value
is strictly positive, witnessed by the uniform mirror-symmetric policy.
-/
theorem paper_problem11_policyOptimal_value_pos
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    {ρ : TypePolicy 3 n} {ell : ℝ}
    (hopt : Theorem4Problem11PolicyOptimal beta v ρ ell) :
    0 < ell := by
  exact theorem4Problem11PolicyOptimal_value_pos hopt

/--
Appendix E, Lemma 14 value-uniqueness component: two Problem 11 epigraph
optima have the same `λ`.
-/
theorem paper_lemma14_problem11_policyOptimal_value_unique
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    {ρ ρ' : TypePolicy 3 n} {ell ell' : ℝ}
    (hopt : Theorem4Problem11PolicyOptimal beta v ρ ell)
    (hopt' : Theorem4Problem11PolicyOptimal beta v ρ' ell') :
    ell = ell' := by
  exact theorem4Problem11PolicyOptimal_value_unique hopt hopt'

/--
Appendix E, Lemma 14 value-uniqueness component for the equality-form
basic-optimum packages used in Lemmas 13--15.
-/
theorem paper_lemma14_problem11_equalizedBasicOptimal_value_unique
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    {ρ ρ' : TypePolicy 3 n} {ell ell' : ℝ}
    (h : Theorem4Problem11EqualizedBasicOptimal beta v ρ ell)
    (h' : Theorem4Problem11EqualizedBasicOptimal beta v ρ' ell') :
    ell = ell' := by
  exact theorem4Problem11EqualizedBasicOptimal_value_unique h h'

/--
Appendix E, Lemma 13 proof component: an equality-form Problem 11 optimum
covers every item by one of the two known-type mirror rows or the cold-start
row.
-/
theorem paper_problem11_type_item_coverage_of_equalizedBasicOptimal
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    {ρ : TypePolicy 3 n} {ell : ℝ}
    (h : Theorem4Problem11EqualizedBasicOptimal beta v ρ ell) :
    ∀ j : Item n, ∃ k : UserType 3, ρ k j ≠ 0 := by
  exact theorem4Problem11_type_item_coverage_of_equalizedBasicOptimal h

/--
Appendix E, Lemma 13 proof component: the equality-form Problem 11
basic-feasible package has the Proposition 2 shared-item bound.
-/
theorem paper_problem11_sharedItemsBound_of_equalizedBasicOptimal
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    {ρ : TypePolicy 3 n} {ell : ℝ}
    (h : Theorem4Problem11EqualizedBasicOptimal beta v ρ ell) :
    TypePolicy.SharedItemsBound ρ := by
  exact theorem4Problem11_sharedItemsBound_of_equalizedBasicOptimal h

/--
Appendix E, Lemma 13 proof component: an equality-form optimal Problem 11
policy admits no mirror-symmetric policy that strictly improves all item values.
-/
theorem paper_problem11_noStrictPointwiseImprovement_of_equalizedBasicOptimal
    {n : ℕ} [NeZero n]
    {beta : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 3 n} {ell : ℝ}
    (h : Theorem4Problem11EqualizedBasicOptimal beta v ρ ell) :
    Theorem4Problem11PolicyNoStrictPointwiseImprovement beta v ρ := by
  exact theorem4Problem11_noStrictPointwiseImprovement_of_equalizedBasicOptimal h

/--
Appendix E, Lemma 17: in any locally optimal mirror-symmetric Problem 11
policy, the known-type row has no positive support strictly after its mirror.
-/
theorem paper_lemma17_problem11_typeZero_zero_after_mirror_of_noStrictPointwiseImprovement
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    {ρ : TypePolicy 3 n}
    (hn : 2 < n)
    (hbeta_pos : 0 < beta)
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hsym : Theorem4MirrorSymmetricPolicy ρ)
    (hno : Theorem4Problem11PolicyNoStrictPointwiseImprovement beta v ρ) :
    ∀ j : Item n, (reverseItem j).val < j.val → ρ 0 j = 0 := by
  exact theorem4Problem11_typeZero_zero_after_mirror_of_noStrictPointwiseImprovement
    hn hbeta_pos hpos hdec hsym hno

/--
Appendix E, Lemma 17 for the equality-form optimal BFS package used in
Problem 11.
-/
theorem paper_lemma17_problem11_typeZero_zero_after_mirror_of_equalizedBasicOptimal
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    {ρ : TypePolicy 3 n} {ell : ℝ}
    (hn : 2 < n)
    (hbeta_pos : 0 < beta)
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (h : Theorem4Problem11EqualizedBasicOptimal beta v ρ ell) :
    ∀ j : Item n, (reverseItem j).val < j.val → ρ 0 j = 0 := by
  exact theorem4Problem11_typeZero_zero_after_mirror_of_noStrictPointwiseImprovement
    hn hbeta_pos hpos hdec h.mirror
    (theorem4Problem11_noStrictPointwiseImprovement_of_equalizedBasicOptimal h)

/--
Appendix E, Lemma 13/14 support component: the selected last active
known-type coordinate of an equality-form Problem 11 optimum is in the left
half of the mirror order.
-/
theorem paper_lemma14_problem11_lastActive_le_reverse_of_equalizedBasicOptimal
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    {ρ : TypePolicy 3 n} {ell : ℝ}
    (hn : 2 < n)
    (hbeta_pos : 0 < beta)
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (h : Theorem4Problem11EqualizedBasicOptimal beta v ρ ell) :
    (theorem4Problem11LastActiveTypeZero ρ).val ≤
      (reverseItem (theorem4Problem11LastActiveTypeZero ρ)).val := by
  exact theorem4Problem11LastActiveTypeZero_le_reverse_of_equalizedBasicOptimal
    hn hbeta_pos hpos hdec h

/--
Appendix E, Lemma 14 pivot-uniqueness component: two equality-form Problem 11
optima select the same last active known-type coordinate.
-/
theorem paper_lemma14_problem11_lastActive_eq_of_equalizedBasicOptimal
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
  exact theorem4Problem11EqualizedBasicOptimal_lastActive_eq
    hn hbeta_pos hbeta_half hpos hdec h h'

/--
Appendix E, Lemma 14 sparse comparison component: before the last active
known-type coordinates of two equality-form Problem 11 optima, the known-row
coordinates agree.
-/
theorem paper_lemma14_problem11_typeZero_toReal_eq_of_before_both_lastActive
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
  exact theorem4Problem11EqualizedBasicOptimal_typeZero_toReal_eq_of_before_both_lastActive
    hn hbeta_pos hbeta_half hpos hdec h h' hj hj'

/--
Appendix E, Lemma 14 sparse comparison component: after the last active
known-type coordinates of two equality-form Problem 11 optima, on the left half
of the mirror order, the cold-start coordinates agree.
-/
theorem paper_lemma14_problem11_cold_toReal_eq_of_both_lastActive_before_left
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
  exact theorem4Problem11EqualizedBasicOptimal_cold_toReal_eq_of_both_lastActive_before_left
    hn hbeta_pos hbeta_half hpos hdec h h' hj hj' hjleft

/--
Appendix E, Lemma 14 coordinate-uniqueness component: after pivot uniqueness,
the known-type coordinates of two equality-form Problem 11 optima agree at
every item.
-/
theorem paper_lemma14_problem11_typeZero_toReal_eq
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
  exact theorem4Problem11EqualizedBasicOptimal_typeZero_toReal_eq
    hn hbeta_pos hbeta_half hpos hdec h h' j

/--
Appendix E, Lemma 14 coordinate-uniqueness component: item equalization and
known-row equality force the cold-start coordinates to agree.
-/
theorem paper_lemma14_problem11_cold_toReal_eq
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
  exact theorem4Problem11EqualizedBasicOptimal_cold_toReal_eq
    hn hbeta_pos hbeta_half hpos hdec h h' j

/--
Appendix E, Lemma 14: the equality-form Problem 11 optimum is unique inside
the mirror-symmetric basic-feasible package.
-/
theorem paper_lemma14_problem11_equalizedBasicOptimal_policy_eq
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
  exact theorem4Problem11EqualizedBasicOptimal_policy_eq
    hn hbeta_pos hbeta_half hpos hdec h h'

/--
Appendix E, Lemma 13 support-count bridge: once the paper's two no-gap
perturbation conclusions are available, Proposition 2's shared-item bound
forces the pivot-support form at the last active known-type item.
-/
theorem paper_lemma13_problem11_pivotSupport_of_lastActive_noGap_of_sharedBound
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
  exact theorem4Problem11PivotSupport_of_lastActive_noGap_of_sharedBound
    hmirror hx hz hshared hleft

/--
Appendix E, Lemma 13 for the equality-form optimal BFS package, conditional
only on the two remaining no-gap perturbation conclusions from the paper.
-/
theorem paper_lemma13_problem11_pivotSupport_of_equalizedBasicOptimal_noGap
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
  exact theorem4Problem11PivotSupport_of_equalizedBasicOptimal_noGap
    hn hbeta_pos hpos hdec h hx hz

/--
Appendix E, Lemma 13 final reduction seam: the two strict-improvement
perturbation certificates imply the no-gap predicates by optimality, and hence
give the pivot-support form.
-/
theorem paper_lemma13_problem11_pivotSupport_of_equalizedBasicOptimal_gapStrictImprovements
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
  exact theorem4Problem11PivotSupport_of_equalizedBasicOptimal_gapStrictImprovements
    hn hbeta_pos hpos hdec h hxgap hzgap

/--
Appendix E, Lemma 15 component: if the Problem 11 closed form is evaluated at
pivot `t = 1`, then the resulting `z₁` is negative whenever `β > 1/n` and the
cold-start type has positive mass.
-/
theorem paper_lemma15_problem11_pivotOneZ_neg
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hn : 2 < n)
    (hbeta : (n : ℝ)⁻¹ < beta)
    (hbeta_half : beta < 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v) :
    theorem4Problem11PivotOneZ beta v < 0 := by
  exact theorem4Problem11PivotOneZ_neg
    hn hbeta hbeta_half hpos hdec

/--
Appendix E, Lemma 15 notation: `L_t = ∑_{j<t} 1/q_j` for Problem 11.
-/
noncomputable def paper_lemma15_problem11_leftSum {n : ℕ}
    (v : Item n → ℝ) (t : Item n) : ℝ :=
  theorem4Problem11LeftSum v t

/-- Appendix E, Lemma 15 positivity side fact: `L_t` is nonnegative. -/
theorem paper_lemma15_problem11_leftSum_nonneg {n : ℕ}
    {v : Item n → ℝ}
    (hpos : ∀ j : Item n, 0 < v j) (t : Item n) :
    0 ≤ paper_lemma15_problem11_leftSum v t := by
  exact theorem4Problem11LeftSum_nonneg hpos t

/--
Appendix E, Lemma 15 coordinate formula: before the pivot,
`x_j = λ / (2β q_j)`.
-/
theorem paper_lemma15_problem11_typeZero_before_eq
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    {ρ : TypePolicy 3 n} {ell : ℝ} {t j : Item n}
    (hbeta_pos : 0 < beta)
    (hpos : ∀ l : Item n, 0 < v l)
    (h : Theorem4Problem11EqualizedBasicOptimal beta v ρ ell)
    (hpivot : Theorem4Problem11PivotSupport ρ t)
    (hleft : t.val ≤ (reverseItem t).val)
    (hj : j.val < t.val) :
    (ρ 0 j).toReal = ell / (2 * beta * pairShare (1 / 2) v j) := by
  exact theorem4Problem11Lemma15_typeZero_before_eq
    hbeta_pos hpos h hpivot hleft hj

/--
Appendix E, Lemma 15 coordinate formula: after the pivot, `x_j = 0`.
-/
theorem paper_lemma15_problem11_typeZero_after_eq_zero
    {n : ℕ} {ρ : TypePolicy 3 n} {t j : Item n}
    (hpivot : Theorem4Problem11PivotSupport ρ t)
    (hj : t.val < j.val) :
    (ρ 0 j).toReal = 0 := by
  exact theorem4Problem11Lemma15_typeZero_after_eq_zero hpivot hj

/--
Appendix E, Lemma 15 coordinate formula at the pivot:
`x_t = 1 - (λ / (2β)) L_t`.
-/
theorem paper_lemma15_problem11_typeZero_pivot_eq_one_sub_leftSum
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    {ρ : TypePolicy 3 n} {ell : ℝ} {t : Item n}
    (hbeta_pos : 0 < beta)
    (hpos : ∀ l : Item n, 0 < v l)
    (h : Theorem4Problem11EqualizedBasicOptimal beta v ρ ell)
    (hpivot : Theorem4Problem11PivotSupport ρ t)
    (hleft : t.val ≤ (reverseItem t).val) :
    (ρ 0 t).toReal =
      1 - (ell / (2 * beta)) * paper_lemma15_problem11_leftSum v t := by
  exact theorem4Problem11Lemma15_typeZero_pivot_eq_one_sub_leftSum
    hbeta_pos hpos h hpivot hleft

/--
Appendix E, Lemma 15 coordinate formula: before the pivot, `z_j = 0`.
-/
theorem paper_lemma15_problem11_cold_before_eq_zero
    {n : ℕ} {ρ : TypePolicy 3 n} {t j : Item n}
    (hpivot : Theorem4Problem11PivotSupport ρ t)
    (hj : j.val < t.val) :
    (ρ 2 j).toReal = 0 := by
  exact theorem4Problem11Lemma15_cold_before_eq_zero hpivot hj

/--
Appendix E, Lemma 15 coordinate formula: before the pivot, the mirrored
cold-start coordinate is also zero.
-/
theorem paper_lemma15_problem11_cold_reverse_before_eq_zero
    {n : ℕ} {ρ : TypePolicy 3 n} {t j : Item n}
    (hpivot : Theorem4Problem11PivotSupport ρ t)
    (hj : j.val < t.val) :
    (ρ 2 (reverseItem j)).toReal = 0 := by
  exact theorem4Problem11Lemma15_cold_reverse_before_eq_zero hpivot hj

/--
Appendix E, Lemma 15 coordinate formula: strictly between the pivot and its
mirror, `z_j = λ / (1 - 2β)`.
-/
theorem paper_lemma15_problem11_cold_between_pivot_and_mirror_eq
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    {ρ : TypePolicy 3 n} {ell : ℝ} {t j : Item n}
    (hbeta_half : beta < 1 / 2)
    (h : Theorem4Problem11EqualizedBasicOptimal beta v ρ ell)
    (hpivot : Theorem4Problem11PivotSupport ρ t)
    (hjt : t.val < j.val)
    (hjrev_t : j.val < (reverseItem t).val) :
    (ρ 2 j).toReal = ell / (1 - 2 * beta) := by
  exact theorem4Problem11Lemma15_cold_between_pivot_and_mirror_eq
    hbeta_half h hpivot hjt hjrev_t

/--
Appendix E, Lemma 15 sum identity: summing all Problem 11 item values leaves
only the weighted known-type row plus the cold-start row sum.
-/
theorem paper_lemma15_problem11_sum_policyItemValue_eq
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hpos : ∀ j : Item n, 0 < v j)
    (ρ : TypePolicy 3 n) :
    (∑ j : Item n, theorem4Problem11PolicyItemValue beta v ρ j) =
      4 * beta *
          (∑ j : Item n,
            pairShare (1 / 2) v j * (ρ 0 j).toReal) +
        (1 - 2 * beta) := by
  exact theorem4Problem11_sum_policyItemValue_eq hpos ρ

/--
Appendix E, Lemma 15 sum identity under pivot support.
-/
theorem paper_lemma15_problem11_sum_typeZero_q_of_pivot
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
          (1 - (ell / (2 * beta)) * paper_lemma15_problem11_leftSum v t) := by
  exact theorem4Problem11Lemma15_sum_typeZero_q_of_pivot
    hbeta_pos hpos h hpivot hleft

/--
Appendix E, Lemma 15 closed-value algebra: the equality-form `λ` satisfies the
paper's denominator equation.
-/
theorem paper_lemma15_problem11_lambda_mul_denominator_eq
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    {ρ : TypePolicy 3 n} {ell : ℝ} {t : Item n}
    (hbeta_pos : 0 < beta)
    (hpos : ∀ l : Item n, 0 < v l)
    (h : Theorem4Problem11EqualizedBasicOptimal beta v ρ ell)
    (hpivot : Theorem4Problem11PivotSupport ρ t)
    (hleft : t.val ≤ (reverseItem t).val) :
    ell *
        ((n : ℝ) - 2 * (t.val : ℝ) +
          2 * pairShare (1 / 2) v t * paper_lemma15_problem11_leftSum v t) =
      4 * beta * pairShare (1 / 2) v t + (1 - 2 * beta) := by
  exact theorem4Problem11Lemma15_lambda_mul_denominator_eq
    hbeta_pos hpos h hpivot hleft

/--
Appendix E, Lemma 15 non-center closed `λ` formula. Lean uses zero-based item
indices, so the paper's `n - 2t` appears as
`n - 2 * (t.val + 1)`.
-/
theorem paper_lemma15_problem11_lambda_eq_of_pivot_lt_mirror
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    {ρ : TypePolicy 3 n} {ell : ℝ} {t : Item n}
    (hbeta_pos : 0 < beta)
    (hpos : ∀ l : Item n, 0 < v l)
    (h : Theorem4Problem11EqualizedBasicOptimal beta v ρ ell)
    (hpivot : Theorem4Problem11PivotSupport ρ t)
    (ht_left : t.val < (reverseItem t).val) :
    ell =
      (2 * beta * pairShare (1 / 2) v t + (1 / 2) * (1 - 2 * beta)) /
        (1 + pairShare (1 / 2) v t * paper_lemma15_problem11_leftSum v t +
          (1 / 2) * ((n : ℝ) - 2 * ((t.val : ℝ) + 1))) := by
  exact theorem4Problem11Lemma15_lambda_eq_of_pivot_lt_mirror
    hbeta_pos hpos h hpivot ht_left

/--
Appendix E, Lemma 15 non-center coordinate formula at the pivot:
`z_t = (1/2) * (1 - (n - 2t)λ/(1 - 2β))`, with Lean's zero-based
`n - 2t` term written as `n - 2 * (t.val + 1)`.
-/
theorem paper_lemma15_problem11_cold_pivot_eq_of_pivot_lt_mirror
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
  exact theorem4Problem11Lemma15_cold_pivot_eq_of_pivot_lt_mirror
    hbeta_pos hbeta_half hpos h hpivot ht_left

/--
Appendix E, Lemma 15 non-center coordinate formula at the mirror pivot.
-/
theorem paper_lemma15_problem11_cold_mirror_pivot_eq_of_pivot_lt_mirror
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
  exact theorem4Problem11Lemma15_cold_mirror_pivot_eq_of_pivot_lt_mirror
    hbeta_pos hbeta_half hpos h hpivot ht_left

/--
Appendix E, Lemma 15 center-case cold-start coordinate: if the pivot is its
own mirror, `z_t = 1`.
-/
theorem paper_lemma15_problem11_cold_center_eq_one
    {n : ℕ} [NeZero n] {ρ : TypePolicy 3 n} {t : Item n}
    (hpivot : Theorem4Problem11PivotSupport ρ t)
    (ht_center : (reverseItem t).val = t.val) :
    (ρ 2 t).toReal = 1 := by
  exact theorem4Problem11Lemma15_cold_center_eq_one hpivot ht_center

/--
Auxiliary full-policy center-case value identity for Appendix E, Lemma 15.

This is intentionally not named as the verbatim paper formula: the paper writes
the center case in its half-LP convention, while the Lean equality-form Problem
11 interface uses the full mirrored policy. Under the full-policy convention the
center denominator equation simplifies to `λ = 1 / (1 + L_t)`.
-/
theorem paper_aux_lemma15_problem11_lambda_eq_of_center_fullPolicy
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    {ρ : TypePolicy 3 n} {ell : ℝ} {t : Item n}
    (hbeta_pos : 0 < beta)
    (hpos : ∀ l : Item n, 0 < v l)
    (h : Theorem4Problem11EqualizedBasicOptimal beta v ρ ell)
    (hpivot : Theorem4Problem11PivotSupport ρ t)
    (hcenter : t.val = (reverseItem t).val) :
    ell = 1 / (1 + paper_lemma15_problem11_leftSum v t) := by
  exact theorem4Problem11Lemma15_lambda_eq_of_center_fullPolicy
    hbeta_pos hpos h hpivot hcenter

/--
Appendix E, Lemma 15 center convention: the paper's displayed center case
uses a half-LP item equation where the known-type contribution is
`2β q_t x_t`.
-/
def paper_lemma15_problem11_centerHalfLPItemEquation {n : ℕ}
    (beta : ℝ) (v : Item n → ℝ) (ρ : TypePolicy 3 n)
    (ell : ℝ) (t : Item n) : Prop :=
  Theorem4Problem11CenterHalfLPItemEquation beta v ρ ell t

/--
Appendix E, Lemma 15 center closed `λ` formula in the paper's half-LP
convention:
`λ = (2β q_t + (1 - 2β)) / (1 + q_t L_t)`.

The full mirrored-policy formula used by the verified Problem 11 interface is
recorded separately in `paper_aux_lemma15_problem11_lambda_eq_of_center_fullPolicy`.
-/
theorem paper_lemma15_problem11_lambda_eq_of_center_halfLPConvention
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    {ρ : TypePolicy 3 n} {ell : ℝ} {t : Item n}
    (hbeta_pos : 0 < beta)
    (hpos : ∀ l : Item n, 0 < v l)
    (h : Theorem4Problem11EqualizedBasicOptimal beta v ρ ell)
    (hpivot : Theorem4Problem11PivotSupport ρ t)
    (hcenter : t.val = (reverseItem t).val)
    (hhalf :
      paper_lemma15_problem11_centerHalfLPItemEquation beta v ρ ell t) :
    ell =
      (2 * beta * pairShare (1 / 2) v t + (1 - 2 * beta)) /
        (1 + pairShare (1 / 2) v t * paper_lemma15_problem11_leftSum v t) := by
  exact theorem4Problem11Lemma15_lambda_eq_of_center_halfLPConvention
    hbeta_pos hpos h hpivot hcenter hhalf

/--
Appendix E, Lemma 15 consequence: a pivot-one closed-form coordinate cannot
be the cold-start row's PMF mass under the Theorem 4 assumptions.
-/
theorem paper_lemma15_problem11_pivotOne_closedZ_impossible
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
  exact theorem4Problem11PivotOne_closedZ_impossible
    hn hbeta hbeta_half hpos hdec ρ hz

/--
Appendix E, Lemma 13 support consequence: if the Problem 11 pivot is strictly
after item `1`, then the cold-start row gives zero mass to both extreme items.
-/
theorem paper_lemma13_problem11_pivotSupport_no_extremes_of_first_lt
    {n : ℕ} [NeZero n] {ρ : TypePolicy 3 n} {t : Item n}
    (hpivot : Theorem4Problem11PivotSupport ρ t)
    (hfirst_lt : (theorem4FirstItem : Item n).val < t.val) :
    ρ 2 theorem4FirstItem = 0 ∧ ρ 2 theorem4LastItem = 0 := by
  exact theorem4Problem11PivotSupport_no_extremes_of_first_lt
    hpivot hfirst_lt

/--
Appendix E Lemmas 13 and 15 combined: pivot support plus the pivot-one
closed-form coordinate certificate imply that the estimated optimum's
cold-start row avoids both extreme items.
-/
theorem paper_theorem4_problem11_no_extremes_of_pivotSupport_of_closedZ
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
  exact theorem4Problem11_no_extremes_of_pivotSupport_of_closedZ
    hn hbeta hbeta_half hpos hdec hpivot hclosed_first

/--
Appendix E, Lemma 15 pivot-one coordinate calculation: if an equality-form
Problem 11 optimum has Lemma 13 pivot support and the pivot is item `1`, then
the cold-start coordinate is exactly the paper's pivot-one closed-form `z_1`.
-/
theorem paper_lemma15_problem11_pivotOne_closedZ_of_equalized_pivotSupport
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
  exact theorem4Problem11PivotOne_closedZ_of_equalized_pivotSupport
    hn hbeta_half hpos h hpivot ht

/--
Appendix E Lemmas 13 and 15 combined for an equality-form Problem 11 optimum:
Lemma 15 now discharges the pivot-one closed-coordinate obligation internally.
-/
theorem paper_theorem4_problem11_no_extremes_of_equalized_pivotSupport
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
  exact theorem4Problem11_no_extremes_of_equalized_pivotSupport
    hn hbeta hbeta_half hpos hdec h hpivot

/--
Appendix E Lemmas 13 and 15 combined for an equality-form Problem 11 optimum,
with Lemma 13 reduced to the two no-gap perturbation conclusions.
-/
theorem paper_theorem4_problem11_no_extremes_of_equalized_noGap
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
  exact theorem4Problem11_no_extremes_of_equalized_noGap
    hn hbeta hbeta_half hpos hdec h hx hz

/--
Appendix E, Theorem 4 value-vector witness.

For every `eps > 0`, there is a positive strictly decreasing value vector whose
second item is small enough relative to the first item for the final
cold-start utility bound.
-/
theorem paper_theorem4_valueVector_exists_small_second
    {n : ℕ} [NeZero n] (hn : 1 < n) {eps : ℝ} (heps : 0 < eps) :
    ∃ v : Item n → ℝ,
      (∀ j : Item n, 0 < v j) ∧
      StrictlyDecreasingByIndex v ∧
      v (theorem4SecondItem hn) <
        eps / (n : ℝ) * v theorem4FirstItem := by
  exact theorem4_valueVector_exists_small_second hn heps

/--
Appendix E, Theorem 4 no-item-fairness construction, first possible true
cold-start type.

The policy chooses row maxima for the known types and an estimated-best mirror
pair oriented toward the first true cold-start row. It solves the estimated
`γ = 0` reduced problem.
-/
theorem paper_theorem4_noFairnessPolicy_typeZero_estimated_optimalAtLevel_zero
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hbeta : 0 ≤ beta) (hcold : 0 ≤ 1 - 2 * beta)
    (hpos : ∀ j, 0 < v j) (hdec : StrictlyDecreasingByIndex v) :
    TypeWeightedRecommendationModel.IsOptimalAtLevel
        (theorem4EstimatedReducedModel beta v) 0
        (theorem4NoFairnessPolicyTypeZero v) := by
  exact theorem4NoFairnessPolicyTypeZero_estimated_optimalAtLevel_zero
    hbeta hcold hpos hdec

/--
Appendix E, Theorem 4 no-item-fairness true-utility bound, first possible true
cold-start type.
-/
theorem paper_theorem4_noFairnessPolicy_typeZero_true_typeFairness_ge_half
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hpos : ∀ j, 0 < v j) (hdec : StrictlyDecreasingByIndex v) :
    (1 / 2 : ℝ) ≤
      TypeWeightedRecommendationModel.typeFairness
        (theorem4TrueReducedModelTypeZero beta v)
        (theorem4NoFairnessPolicyTypeZero v) := by
  exact theorem4NoFairnessPolicyTypeZero_true_typeFairness_ge_half
    hpos hdec

/--
Appendix E, Theorem 4 no-item-fairness construction, second possible true
cold-start type.
-/
theorem paper_theorem4_noFairnessPolicy_typeOne_estimated_optimalAtLevel_zero
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hbeta : 0 ≤ beta) (hcold : 0 ≤ 1 - 2 * beta)
    (hpos : ∀ j, 0 < v j) (hdec : StrictlyDecreasingByIndex v) :
    TypeWeightedRecommendationModel.IsOptimalAtLevel
        (theorem4EstimatedReducedModel beta v) 0
        (theorem4NoFairnessPolicyTypeOne v) := by
  exact theorem4NoFairnessPolicyTypeOne_estimated_optimalAtLevel_zero
    hbeta hcold hpos hdec

/--
Appendix E, Theorem 4 no-item-fairness true-utility bound, second possible true
cold-start type.
-/
theorem paper_theorem4_noFairnessPolicy_typeOne_true_typeFairness_ge_half
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hpos : ∀ j, 0 < v j) (hdec : StrictlyDecreasingByIndex v) :
    (1 / 2 : ℝ) ≤
      TypeWeightedRecommendationModel.typeFairness
        (theorem4TrueReducedModelTypeOne beta v)
        (theorem4NoFairnessPolicyTypeOne v) := by
  exact theorem4NoFairnessPolicyTypeOne_true_typeFairness_ge_half
    hpos hdec

/--
Appendix E, Theorem 4 cold-start bound, first true type.

If the estimated optimal policy gives the cold-start row no probability on the
first item and `v₂` is small relative to `v₁`, then that row's true normalized
utility is below `eps / n`.
-/
theorem paper_theorem4_coldStart_typeZero_normalizedUtility_lt_from_no_first
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
  exact paper_theorem4_coldStart_typeZero_normalizedUtility_lt
    hn hdec hfirst_pos hsmall ρ hno_first

/--
Appendix E, Theorem 4 cold-start bound, second true type.

If the estimated optimal policy gives the cold-start row no probability on the
last item and `v₂` is small relative to `v₁`, then that row's true normalized
utility is below `eps / n`.
-/
theorem paper_theorem4_coldStart_typeOne_normalizedUtility_lt_from_no_last
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
  exact paper_theorem4_coldStart_typeOne_normalizedUtility_lt
    hn hdec hfirst_pos hsmall ρ hno_last

/--
Appendix E, Theorem 4 cold-start minimum-user-utility consequence, first true
type.
-/
theorem paper_theorem4_coldStart_typeZero_typeFairness_lt_from_no_first
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
  exact paper_theorem4_coldStart_typeZero_typeFairness_lt
    hn hdec hfirst_pos hsmall ρ hno_first

/--
Appendix E, Theorem 4 cold-start minimum-user-utility consequence, second true
type.
-/
theorem paper_theorem4_coldStart_typeOne_typeFairness_lt_from_no_last
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
  exact paper_theorem4_coldStart_typeOne_typeFairness_lt
    hn hdec hfirst_pos hsmall ρ hno_last

end OpposingTypes

namespace EstimatedRecommendationModel

/--
Exact-estimation benchmark for the price of misestimation.

If the estimated utilities coincide with the true utilities, then any policy
that solves the estimated problem has zero price of misestimation when evaluated
against the true model.
-/
theorem paper_priceOfMisestimation_exact_estimation_eq_zero
    {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n) (γ : ℝ) (ρhat : Policy m n)
    (hutility : E.estimatedUtility = E.trueModel.utility)
    (hopt : E.SolvesEstimatedProblem γ ρhat) :
    E.priceOfMisestimation γ ρhat = 0 := by
  exact E.priceOfMisestimation_eq_zero_of_estimatedUtility_eq_true
    γ ρhat hutility hopt

/--
Estimated-problem lift bridge: if a reduced policy is optimal for a reduction
witness of the estimated model, then the lifted user-level policy solves the
paper's estimated problem.
-/
theorem paper_solvesEstimatedProblem_liftedPolicy_of_reduced
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
  exact E.solvesEstimatedProblem_liftedPolicy_of_reduced
    R reps hestimated hrow hopt

/--
Theorem 4 estimated-model packaging: an optimal reduced policy for the
Appendix E estimated three-type model solves the original estimated problem
after lifting.
-/
theorem paper_theorem4_solvesEstimatedProblem_from_estimated_reduction
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
  exact E.theorem4_solvesEstimatedProblem_from_estimated_reduction
    R reps hestimated hred hpos hopt

/--
Theorem 4 no-fairness policy, first true cold-start row: the displayed
estimated no-fairness policy solves the original estimated problem at `γ = 0`
after lifting through the estimated reduction.
-/
theorem paper_theorem4_noFairnessPolicyTypeZero_solvesEstimatedProblem_zero_from_reduction
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
  exact E.theorem4_noFairnessPolicyTypeZero_solvesEstimatedProblem_zero_from_reduction
    R reps hestimated hred hbeta hcold hpos hdec

/--
Theorem 4 no-fairness policy, second true cold-start row: the displayed
estimated no-fairness policy solves the original estimated problem at `γ = 0`
after lifting through the estimated reduction.
-/
theorem paper_theorem4_noFairnessPolicyTypeOne_solvesEstimatedProblem_zero_from_reduction
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
  exact E.theorem4_noFairnessPolicyTypeOne_solvesEstimatedProblem_zero_from_reduction
    R reps hestimated hred hbeta hcold hpos hdec

/--
Appendix E Problem 11 packaging: the selected equality-form Problem 11 optimum
solves the original estimated problem at `γ = 1` after lifting.
-/
theorem paper_theorem4_problem11EqualizedBasicOptimal_solvesEstimatedProblem_one_from_reduction
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
  exact E.theorem4_problem11EqualizedBasicOptimal_solvesEstimatedProblem_one_from_reduction
    R reps hn hestimated hred hbeta_pos hbeta_half hpos hdec h hselection

/--
Appendix E Problem 11 packaging after rebuilding the policy from real
equality-form BFS data.
-/
theorem paper_theorem4_problem11EqualityFormOptimalBFS_solvesEstimatedProblem_one_from_reduction
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
  exact E.theorem4_problem11EqualityFormOptimalBFS_solvesEstimatedProblem_one_from_reduction
    R reps hn hestimated hred hbeta_pos hbeta_half hpos hdec h hselection

/--
Appendix E Problem 11 estimated-problem packaging in Lemma 14 form: uniqueness
of the epigraph-optimal mirror-symmetric policy is enough to lift the selected
equality-form optimum to an original estimated-problem solution.
-/
theorem paper_theorem4_problem11EqualizedBasicOptimal_solvesEstimatedProblem_one_from_reduction_of_policyOptimal_unique
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
  exact E.theorem4_problem11EqualizedBasicOptimal_solvesEstimatedProblem_one_from_reduction_of_policyOptimal_unique
    R reps hestimated hred hbeta hcold hpos h hunique

/--
Appendix E Problem 11 estimated-problem packaging in Lemma 14 form, after
rebuilding the policy from real equality-form BFS data.
-/
theorem paper_theorem4_problem11EqualityFormOptimalBFS_solvesEstimatedProblem_one_from_reduction_of_policyOptimal_unique
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
  exact E.theorem4_problem11EqualityFormOptimalBFS_solvesEstimatedProblem_one_from_reduction_of_policyOptimal_unique
    R reps hestimated hred hbeta hcold hpos h hunique

/--
Appendix E / Theorem 4 true-model baseline, odd midpoint case: the two-type
half-population reduced lower bound lifts to the original true model.
-/
theorem paper_theorem4_trueModel_optimalUserFairnessAtLevel_one_gt_inv_card_half_center_from_reduction
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
  exact E.theorem4_trueModel_optimalUserFairnessAtLevel_one_gt_inv_card_half_center_from_reduction
    R reps hn htrue hred hpos hdec hcenter

/--
Appendix E / Theorem 4 true-model baseline, even midpoint case: the two-type
half-population reduced lower bound lifts to the original true model.
-/
theorem paper_theorem4_trueModel_optimalUserFairnessAtLevel_one_gt_inv_card_half_succ_center_from_reduction
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
  exact E.theorem4_trueModel_optimalUserFairnessAtLevel_one_gt_inv_card_half_succ_center_from_reduction
    R reps htrue hred hpos hdec hsucc

/--
Appendix E / Theorem 4 cold-start evaluation bridge, first true row: a user
whose true type is the first opposing row and whose estimated type is the
collapsed cold-start row receives exactly the reduced cold-start normalized
utility.
-/
theorem paper_theorem4_coldUser_typeZero_normalizedUserUtility_eq
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
  exact E.theorem4_coldUser_typeZero_normalizedUserUtility_eq
    Rtrue Rest u htrue hredTrue htrueType hestimatedType

/--
Appendix E / Theorem 4 cold-start evaluation bridge, second true row.
-/
theorem paper_theorem4_coldUser_typeOne_normalizedUserUtility_eq
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
  exact E.theorem4_coldUser_typeOne_normalizedUserUtility_eq
    Rtrue Rest u htrue hredTrue htrueType hestimatedType

/--
Appendix E / Theorem 4 large-misestimation bridge for a concrete cold-start
user whose true preferences are the first opposing row.
-/
theorem paper_theorem4_misestimation_with_fairness_large_from_trueHalf_coldUser_typeZero
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
  exact E.theorem4_misestimation_with_fairness_large_from_trueHalf_coldUser_typeZero
    (beta := beta) Rtrue Rest u hn htrue hredTrue htrueType
    hestimatedType heps hbase hdec hfirst_pos hsmall ρ hno_first

/--
Appendix E / Theorem 4 large-misestimation bridge for a concrete cold-start
user whose true preferences are the second opposing row.
-/
theorem paper_theorem4_misestimation_with_fairness_large_from_trueHalf_coldUser_typeOne
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
  exact E.theorem4_misestimation_with_fairness_large_from_trueHalf_coldUser_typeOne
    (beta := beta) Rtrue Rest u hn htrue hredTrue htrueType
    hestimatedType heps hbase hdec hfirst_pos hsmall ρ hno_last

/--
Appendix E / Theorem 4 strongest current fairness-side wrapper, odd midpoint
and first true cold-start row: the closed Problem 11 policy solves the original
estimated `γ = 1` problem and has price of misestimation above `1 - eps`.
-/
theorem paper_theorem4_misestimation_with_fairness_large_from_smallValueVector_closed_problem11_trueHalf_coldUser_typeZero_center
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
  exact E.theorem4_misestimation_with_fairness_large_from_smallValueVector_closed_problem11_trueHalf_coldUser_typeZero_center
    Rtrue Rest repsTrue repsEst u hn htrue hestimated hredTrue hredEst
    htrueType hestimatedType heps hbeta hbeta_half hcenter

/--
Appendix E / Theorem 4 strongest current fairness-side wrapper, odd midpoint
and second true cold-start row.
-/
theorem paper_theorem4_misestimation_with_fairness_large_from_smallValueVector_closed_problem11_trueHalf_coldUser_typeOne_center
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
  exact E.theorem4_misestimation_with_fairness_large_from_smallValueVector_closed_problem11_trueHalf_coldUser_typeOne_center
    Rtrue Rest repsTrue repsEst u hn htrue hestimated hredTrue hredEst
    htrueType hestimatedType heps hbeta hbeta_half hcenter

/--
Appendix E / Theorem 4 strongest current fairness-side wrapper, even midpoint
and first true cold-start row.
-/
theorem paper_theorem4_misestimation_with_fairness_large_from_smallValueVector_closed_problem11_trueHalf_coldUser_typeZero_succ_center
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
  exact E.theorem4_misestimation_with_fairness_large_from_smallValueVector_closed_problem11_trueHalf_coldUser_typeZero_succ_center
    Rtrue Rest repsTrue repsEst u hn htrue hestimated hredTrue hredEst
    htrueType hestimatedType heps hbeta hbeta_half hsucc

/--
Appendix E / Theorem 4 strongest current fairness-side wrapper, even midpoint
and second true cold-start row.
-/
theorem paper_theorem4_misestimation_with_fairness_large_from_smallValueVector_closed_problem11_trueHalf_coldUser_typeOne_succ_center
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
  exact E.theorem4_misestimation_with_fairness_large_from_smallValueVector_closed_problem11_trueHalf_coldUser_typeOne_succ_center
    Rtrue Rest repsTrue repsEst u hn htrue hestimated hredTrue hredEst
    htrueType hestimatedType heps hbeta hbeta_half hsucc

/--
Appendix E, Theorem 4 first-bullet algebra.

Without item-fairness constraints, if the true unconstrained optimum is `1`
and the chosen estimated-optimal policy gives true user fairness at least
`1/2`, then the price of misestimation is at most `1/2`.
-/
theorem paper_theorem4_misestimation_without_fairness_le_half_from_userFairness
    {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n) (ρhat : Policy m n)
    (hbase :
      RecommendationModel.optimalUserFairnessAtLevel E.trueModel 0 = 1)
    (huser :
      (1 / 2 : ℝ) ≤ RecommendationModel.userFairness E.trueModel ρhat) :
    E.priceOfMisestimation 0 ρhat ≤ (1 / 2 : ℝ) := by
  exact E.priceOfMisestimation_at_zero_le_half_of_userFairness_ge_half
    ρhat hbase huser

/--
Appendix E, Theorem 4 no-fairness price bound, first true cold-start row:
the reduced no-fairness policy lifted to the original model has price of
misestimation at most `1/2` at `γ = 0`.
-/
theorem paper_theorem4_misestimation_without_fairness_le_half_typeZero_from_reduction
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
  exact E.theorem4_misestimation_without_fairness_le_half_typeZero_from_reduction
    R reps htrue hred hpos hdec

/--
Appendix E, Theorem 4 no-fairness price bound, second true cold-start row:
the reduced no-fairness policy lifted to the original model has price of
misestimation at most `1/2` at `γ = 0`.
-/
theorem paper_theorem4_misestimation_without_fairness_le_half_typeOne_from_reduction
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
  exact E.theorem4_misestimation_without_fairness_le_half_typeOne_from_reduction
    R reps htrue hred hpos hdec

/--
Appendix E, Theorem 4 no-fairness price bound for the paper's source model:
the true model has the two opposing rows, the estimated model collapses
cold-start users into the averaged third row, and the no-fairness estimated
optimum mixes the cold-start row evenly across an estimated-best mirror pair.
-/
theorem paper_theorem4_misestimation_without_fairness_le_half_trueHalf_collapsed_from_reductions
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
  exact E.theorem4_misestimation_without_fairness_le_half_trueHalf_collapsed_from_reductions
    Rtrue Rest repsEst htrue hestimated hredTrue hredEst hknown0 hknown1
    hbeta hcold hpos hdec

/--
Appendix E, Theorem 4 two-bullet source wrapper: two-type true population,
collapsed estimated cold-start row, odd midpoint, and a cold-start user whose
true row is the first opposing row.
-/
theorem paper_theorem4_misestimation_tradeoff_trueHalf_collapsed_typeZero_center
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
    (hknown0 :
      ∀ u : User m, Rest.data.types.toType u = 0 →
        Rtrue.data.types.toType u = 0)
    (hknown1 :
      ∀ u : User m, Rest.data.types.toType u = 1 →
        Rtrue.data.types.toType u = 1)
    (htrueType : Rtrue.data.types.toType u = 0)
    (hestimatedType : Rest.data.types.toType u = 2)
    (heps : 0 < eps)
    (hbeta : (n : ℝ)⁻¹ < beta)
    (hbeta_half : beta < 1 / 2)
    (hcenter : c.val = (OpposingTypes.reverseItem c).val) :
    (let ρ0 : TypePolicy 3 n :=
        OpposingTypes.theorem4NoFairnessPolicyCollapsed
          (OpposingTypes.theorem4SmallValueVector (n := n) eps);
      E.SolvesEstimatedProblem 0 (Rest.liftedPolicy ρ0) ∧
        E.priceOfMisestimation 0 (Rest.liftedPolicy ρ0) ≤ (1 / 2 : ℝ)) ∧
      ∃ ρ1 : TypePolicy 3 n,
        E.SolvesEstimatedProblem 1 (Rest.liftedPolicy ρ1) ∧
          1 - eps < E.priceOfMisestimation 1 (Rest.liftedPolicy ρ1) := by
  let v : Item n → ℝ := OpposingTypes.theorem4SmallValueVector (n := n) eps
  have hpos : ∀ j : Item n, 0 < v j :=
    OpposingTypes.theorem4SmallValueVector_pos (n := n) (eps := eps) heps
  have hdec : OpposingTypes.StrictlyDecreasingByIndex v :=
    OpposingTypes.theorem4SmallValueVector_strictlyDecreasing
      (n := n) (eps := eps) heps
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hbeta_nonneg : 0 ≤ beta :=
    (lt_trans (inv_pos.mpr hnpos) hbeta).le
  have hcold : 0 ≤ 1 - 2 * beta := by
    nlinarith
  constructor
  · exact
      paper_theorem4_misestimation_without_fairness_le_half_trueHalf_collapsed_from_reductions
        E Rtrue Rest repsEst htrue hestimated hredTrue hredEst hknown0
        hknown1 hbeta_nonneg hcold hpos hdec
  · exact
      paper_theorem4_misestimation_with_fairness_large_from_smallValueVector_closed_problem11_trueHalf_coldUser_typeZero_center
        E Rtrue Rest repsTrue repsEst u hn htrue hestimated hredTrue hredEst
        htrueType hestimatedType heps hbeta hbeta_half hcenter

/--
Appendix E, Theorem 4 two-bullet source wrapper: odd midpoint and a cold-start
user whose true row is the second opposing row.
-/
theorem paper_theorem4_misestimation_tradeoff_trueHalf_collapsed_typeOne_center
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
    (hknown0 :
      ∀ u : User m, Rest.data.types.toType u = 0 →
        Rtrue.data.types.toType u = 0)
    (hknown1 :
      ∀ u : User m, Rest.data.types.toType u = 1 →
        Rtrue.data.types.toType u = 1)
    (htrueType : Rtrue.data.types.toType u = 1)
    (hestimatedType : Rest.data.types.toType u = 2)
    (heps : 0 < eps)
    (hbeta : (n : ℝ)⁻¹ < beta)
    (hbeta_half : beta < 1 / 2)
    (hcenter : c.val = (OpposingTypes.reverseItem c).val) :
    (let ρ0 : TypePolicy 3 n :=
        OpposingTypes.theorem4NoFairnessPolicyCollapsed
          (OpposingTypes.theorem4SmallValueVector (n := n) eps);
      E.SolvesEstimatedProblem 0 (Rest.liftedPolicy ρ0) ∧
        E.priceOfMisestimation 0 (Rest.liftedPolicy ρ0) ≤ (1 / 2 : ℝ)) ∧
      ∃ ρ1 : TypePolicy 3 n,
        E.SolvesEstimatedProblem 1 (Rest.liftedPolicy ρ1) ∧
          1 - eps < E.priceOfMisestimation 1 (Rest.liftedPolicy ρ1) := by
  let v : Item n → ℝ := OpposingTypes.theorem4SmallValueVector (n := n) eps
  have hpos : ∀ j : Item n, 0 < v j :=
    OpposingTypes.theorem4SmallValueVector_pos (n := n) (eps := eps) heps
  have hdec : OpposingTypes.StrictlyDecreasingByIndex v :=
    OpposingTypes.theorem4SmallValueVector_strictlyDecreasing
      (n := n) (eps := eps) heps
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hbeta_nonneg : 0 ≤ beta :=
    (lt_trans (inv_pos.mpr hnpos) hbeta).le
  have hcold : 0 ≤ 1 - 2 * beta := by
    nlinarith
  constructor
  · exact
      paper_theorem4_misestimation_without_fairness_le_half_trueHalf_collapsed_from_reductions
        E Rtrue Rest repsEst htrue hestimated hredTrue hredEst hknown0
        hknown1 hbeta_nonneg hcold hpos hdec
  · exact
      paper_theorem4_misestimation_with_fairness_large_from_smallValueVector_closed_problem11_trueHalf_coldUser_typeOne_center
        E Rtrue Rest repsTrue repsEst u hn htrue hestimated hredTrue hredEst
        htrueType hestimatedType heps hbeta hbeta_half hcenter

/--
Appendix E, Theorem 4 two-bullet source wrapper: even midpoint and a cold-start
user whose true row is the first opposing row.
-/
theorem paper_theorem4_misestimation_tradeoff_trueHalf_collapsed_typeZero_succ_center
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
    (hknown0 :
      ∀ u : User m, Rest.data.types.toType u = 0 →
        Rtrue.data.types.toType u = 0)
    (hknown1 :
      ∀ u : User m, Rest.data.types.toType u = 1 →
        Rtrue.data.types.toType u = 1)
    (htrueType : Rtrue.data.types.toType u = 0)
    (hestimatedType : Rest.data.types.toType u = 2)
    (heps : 0 < eps)
    (hbeta : (n : ℝ)⁻¹ < beta)
    (hbeta_half : beta < 1 / 2)
    (hsucc : c.val + 1 = (OpposingTypes.reverseItem c).val) :
    (let ρ0 : TypePolicy 3 n :=
        OpposingTypes.theorem4NoFairnessPolicyCollapsed
          (OpposingTypes.theorem4SmallValueVector (n := n) eps);
      E.SolvesEstimatedProblem 0 (Rest.liftedPolicy ρ0) ∧
        E.priceOfMisestimation 0 (Rest.liftedPolicy ρ0) ≤ (1 / 2 : ℝ)) ∧
      ∃ ρ1 : TypePolicy 3 n,
        E.SolvesEstimatedProblem 1 (Rest.liftedPolicy ρ1) ∧
          1 - eps < E.priceOfMisestimation 1 (Rest.liftedPolicy ρ1) := by
  let v : Item n → ℝ := OpposingTypes.theorem4SmallValueVector (n := n) eps
  have hpos : ∀ j : Item n, 0 < v j :=
    OpposingTypes.theorem4SmallValueVector_pos (n := n) (eps := eps) heps
  have hdec : OpposingTypes.StrictlyDecreasingByIndex v :=
    OpposingTypes.theorem4SmallValueVector_strictlyDecreasing
      (n := n) (eps := eps) heps
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hbeta_nonneg : 0 ≤ beta :=
    (lt_trans (inv_pos.mpr hnpos) hbeta).le
  have hcold : 0 ≤ 1 - 2 * beta := by
    nlinarith
  constructor
  · exact
      paper_theorem4_misestimation_without_fairness_le_half_trueHalf_collapsed_from_reductions
        E Rtrue Rest repsEst htrue hestimated hredTrue hredEst hknown0
        hknown1 hbeta_nonneg hcold hpos hdec
  · exact
      paper_theorem4_misestimation_with_fairness_large_from_smallValueVector_closed_problem11_trueHalf_coldUser_typeZero_succ_center
        E Rtrue Rest repsTrue repsEst u hn htrue hestimated hredTrue hredEst
        htrueType hestimatedType heps hbeta hbeta_half hsucc

/--
Appendix E, Theorem 4 two-bullet source wrapper: even midpoint and a cold-start
user whose true row is the second opposing row.
-/
theorem paper_theorem4_misestimation_tradeoff_trueHalf_collapsed_typeOne_succ_center
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
    (hknown0 :
      ∀ u : User m, Rest.data.types.toType u = 0 →
        Rtrue.data.types.toType u = 0)
    (hknown1 :
      ∀ u : User m, Rest.data.types.toType u = 1 →
        Rtrue.data.types.toType u = 1)
    (htrueType : Rtrue.data.types.toType u = 1)
    (hestimatedType : Rest.data.types.toType u = 2)
    (heps : 0 < eps)
    (hbeta : (n : ℝ)⁻¹ < beta)
    (hbeta_half : beta < 1 / 2)
    (hsucc : c.val + 1 = (OpposingTypes.reverseItem c).val) :
    (let ρ0 : TypePolicy 3 n :=
        OpposingTypes.theorem4NoFairnessPolicyCollapsed
          (OpposingTypes.theorem4SmallValueVector (n := n) eps);
      E.SolvesEstimatedProblem 0 (Rest.liftedPolicy ρ0) ∧
        E.priceOfMisestimation 0 (Rest.liftedPolicy ρ0) ≤ (1 / 2 : ℝ)) ∧
      ∃ ρ1 : TypePolicy 3 n,
        E.SolvesEstimatedProblem 1 (Rest.liftedPolicy ρ1) ∧
          1 - eps < E.priceOfMisestimation 1 (Rest.liftedPolicy ρ1) := by
  let v : Item n → ℝ := OpposingTypes.theorem4SmallValueVector (n := n) eps
  have hpos : ∀ j : Item n, 0 < v j :=
    OpposingTypes.theorem4SmallValueVector_pos (n := n) (eps := eps) heps
  have hdec : OpposingTypes.StrictlyDecreasingByIndex v :=
    OpposingTypes.theorem4SmallValueVector_strictlyDecreasing
      (n := n) (eps := eps) heps
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hbeta_nonneg : 0 ≤ beta :=
    (lt_trans (inv_pos.mpr hnpos) hbeta).le
  have hcold : 0 ≤ 1 - 2 * beta := by
    nlinarith
  constructor
  · exact
      paper_theorem4_misestimation_without_fairness_le_half_trueHalf_collapsed_from_reductions
        E Rtrue Rest repsEst htrue hestimated hredTrue hredEst hknown0
        hknown1 hbeta_nonneg hcold hpos hdec
  · exact
      paper_theorem4_misestimation_with_fairness_large_from_smallValueVector_closed_problem11_trueHalf_coldUser_typeOne_succ_center
        E Rtrue Rest repsTrue repsEst u hn htrue hestimated hredTrue hredEst
        htrueType hestimatedType heps hbeta hbeta_half hsucc

/--
Appendix E, Theorem 4 two-bullet source wrapper: two-type true population,
collapsed estimated cold-start row, and a cold-start user whose true row is the
first opposing row.  The odd/even midpoint split is discharged internally.
-/
theorem paper_theorem4_misestimation_tradeoff_trueHalf_collapsed_typeZero
    {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n)
    (Rtrue : ReductionWitness m n 2)
    (Rest : ReductionWitness m n 3)
    (repsTrue : UserTypeAssignment.TypeRepresentatives Rtrue.data.types)
    (repsEst : UserTypeAssignment.TypeRepresentatives Rest.data.types)
    {beta eps : ℝ}
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
    (hknown0 :
      ∀ u : User m, Rest.data.types.toType u = 0 →
        Rtrue.data.types.toType u = 0)
    (hknown1 :
      ∀ u : User m, Rest.data.types.toType u = 1 →
        Rtrue.data.types.toType u = 1)
    (htrueType : Rtrue.data.types.toType u = 0)
    (hestimatedType : Rest.data.types.toType u = 2)
    (heps : 0 < eps)
    (hbeta : (n : ℝ)⁻¹ < beta)
    (hbeta_half : beta < 1 / 2) :
    (let ρ0 : TypePolicy 3 n :=
        OpposingTypes.theorem4NoFairnessPolicyCollapsed
          (OpposingTypes.theorem4SmallValueVector (n := n) eps);
      E.SolvesEstimatedProblem 0 (Rest.liftedPolicy ρ0) ∧
        E.priceOfMisestimation 0 (Rest.liftedPolicy ρ0) ≤ (1 / 2 : ℝ)) ∧
      ∃ ρ1 : TypePolicy 3 n,
        E.SolvesEstimatedProblem 1 (Rest.liftedPolicy ρ1) ∧
          1 - eps < E.priceOfMisestimation 1 (Rest.liftedPolicy ρ1) := by
  rcases OpposingTypes.midpoint_center_or_succ_center (n := n) with
    hcenter | hsucc
  · rcases hcenter with ⟨c, hcenter⟩
    exact
      paper_theorem4_misestimation_tradeoff_trueHalf_collapsed_typeZero_center
        E Rtrue Rest repsTrue repsEst u hn htrue hestimated hredTrue hredEst
        hknown0 hknown1 htrueType hestimatedType heps hbeta hbeta_half
        hcenter
  · rcases hsucc with ⟨c, hsucc⟩
    exact
      paper_theorem4_misestimation_tradeoff_trueHalf_collapsed_typeZero_succ_center
        E Rtrue Rest repsTrue repsEst u hn htrue hestimated hredTrue hredEst
        hknown0 hknown1 htrueType hestimatedType heps hbeta hbeta_half
        hsucc

/--
Appendix E, Theorem 4 two-bullet source wrapper: two-type true population,
collapsed estimated cold-start row, and a cold-start user whose true row is the
second opposing row.  The odd/even midpoint split is discharged internally.
-/
theorem paper_theorem4_misestimation_tradeoff_trueHalf_collapsed_typeOne
    {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n)
    (Rtrue : ReductionWitness m n 2)
    (Rest : ReductionWitness m n 3)
    (repsTrue : UserTypeAssignment.TypeRepresentatives Rtrue.data.types)
    (repsEst : UserTypeAssignment.TypeRepresentatives Rest.data.types)
    {beta eps : ℝ}
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
    (hknown0 :
      ∀ u : User m, Rest.data.types.toType u = 0 →
        Rtrue.data.types.toType u = 0)
    (hknown1 :
      ∀ u : User m, Rest.data.types.toType u = 1 →
        Rtrue.data.types.toType u = 1)
    (htrueType : Rtrue.data.types.toType u = 1)
    (hestimatedType : Rest.data.types.toType u = 2)
    (heps : 0 < eps)
    (hbeta : (n : ℝ)⁻¹ < beta)
    (hbeta_half : beta < 1 / 2) :
    (let ρ0 : TypePolicy 3 n :=
        OpposingTypes.theorem4NoFairnessPolicyCollapsed
          (OpposingTypes.theorem4SmallValueVector (n := n) eps);
      E.SolvesEstimatedProblem 0 (Rest.liftedPolicy ρ0) ∧
        E.priceOfMisestimation 0 (Rest.liftedPolicy ρ0) ≤ (1 / 2 : ℝ)) ∧
      ∃ ρ1 : TypePolicy 3 n,
        E.SolvesEstimatedProblem 1 (Rest.liftedPolicy ρ1) ∧
          1 - eps < E.priceOfMisestimation 1 (Rest.liftedPolicy ρ1) := by
  rcases OpposingTypes.midpoint_center_or_succ_center (n := n) with
    hcenter | hsucc
  · rcases hcenter with ⟨c, hcenter⟩
    exact
      paper_theorem4_misestimation_tradeoff_trueHalf_collapsed_typeOne_center
        E Rtrue Rest repsTrue repsEst u hn htrue hestimated hredTrue hredEst
        hknown0 hknown1 htrueType hestimatedType heps hbeta hbeta_half
        hcenter
  · rcases hsucc with ⟨c, hsucc⟩
    exact
      paper_theorem4_misestimation_tradeoff_trueHalf_collapsed_typeOne_succ_center
        E Rtrue Rest repsTrue repsEst u hn htrue hestimated hredTrue hredEst
        hknown0 hknown1 htrueType hestimatedType heps hbeta hbeta_half
        hsucc

/--
Appendix E, Theorem 4 final algebraic step.

If the true maximal-fairness optimum is above `1/n` while the estimated
maximal-fairness solution gives true user fairness below `eps/n`, then the
price of misestimation with maximal item-fairness constraints is above
`1 - eps`.
-/
theorem paper_theorem4_misestimation_large_from_bounds
    {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n) (eps : ℝ) (ρhat : Policy m n)
    (heps : 0 < eps)
    (hbase :
      (n : ℝ)⁻¹ <
        RecommendationModel.optimalUserFairnessAtLevel E.trueModel 1)
    (huser :
      RecommendationModel.userFairness E.trueModel ρhat <
        eps / (n : ℝ)) :
    1 - eps < E.priceOfMisestimation 1 ρhat := by
  exact E.priceOfMisestimation_gt_one_sub_of_userFairness_lt_div_card
    eps ρhat heps hbase huser

/--
Appendix E, Theorem 4 fairness-constrained large-misestimation wrapper for a
cold-start user whose true preferences are the first opposing row.

The remaining construction hypothesis is the named Appendix E LP certificate
that the estimated optimum's cold-start row gives zero probability to item `1`.
-/
theorem paper_theorem4_misestimation_with_fairness_large_typeZero_from_reduction
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
  exact E.theorem4_misestimation_with_fairness_large_typeZero_from_reduction
    R reps hn htrue hred heps hbase hdec hfirst_pos hsmall ρ hno_first

/--
Appendix E, Theorem 4 fairness-constrained large-misestimation wrapper for a
cold-start user whose true preferences are the second opposing row.

The remaining construction hypothesis is the mirror Appendix E LP certificate
that the estimated optimum's cold-start row gives zero probability to item `n`.
-/
theorem paper_theorem4_misestimation_with_fairness_large_typeOne_from_reduction
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
  exact E.theorem4_misestimation_with_fairness_large_typeOne_from_reduction
    R reps hn htrue hred heps hbase hdec hfirst_pos hsmall ρ hno_last

/--
Appendix E, Theorem 4 fairness-constrained large-misestimation wrapper for a
cold-start user whose true preferences are the first opposing row, stated with
the Problem 11 pivot-support and closed-form certificates.
-/
theorem paper_theorem4_misestimation_with_fairness_large_typeZero_from_problem11_certificate
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
  exact E.theorem4_misestimation_with_fairness_large_typeZero_from_problem11_certificate
    R reps hn htrue hred heps hbase hbeta hbeta_half hdec hpos hsmall
    ρ t hpivot hclosed_first

/--
Appendix E, Theorem 4 fairness-constrained large-misestimation wrapper for a
cold-start user whose true preferences are the second opposing row, stated with
the Problem 11 pivot-support and closed-form certificates.
-/
theorem paper_theorem4_misestimation_with_fairness_large_typeOne_from_problem11_certificate
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
  exact E.theorem4_misestimation_with_fairness_large_typeOne_from_problem11_certificate
    R reps hn htrue hred heps hbase hbeta hbeta_half hdec hpos hsmall
    ρ t hpivot hclosed_first

/--
Appendix E, Theorem 4 fairness-constrained large-misestimation wrapper for a
cold-start user whose true preferences are the first opposing row, stated with
an equality-form Problem 11 optimum and Lemma 13 pivot support.
-/
theorem paper_theorem4_misestimation_with_fairness_large_typeZero_from_equalized_problem11
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
  exact E.theorem4_misestimation_with_fairness_large_typeZero_from_equalized_problem11
    R reps hn htrue hred heps hbase hbeta hbeta_half hdec hpos hsmall
    ρ ell t heq hpivot

/--
Appendix E, Theorem 4 fairness-constrained large-misestimation wrapper for a
cold-start user whose true preferences are the second opposing row, stated with
an equality-form Problem 11 optimum and Lemma 13 pivot support.
-/
theorem paper_theorem4_misestimation_with_fairness_large_typeOne_from_equalized_problem11
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
  exact E.theorem4_misestimation_with_fairness_large_typeOne_from_equalized_problem11
    R reps hn htrue hred heps hbase hbeta hbeta_half hdec hpos hsmall
    ρ ell t heq hpivot

/--
Appendix E, Theorem 4 fairness-constrained large-misestimation wrapper for a
cold-start user whose true preferences are the first opposing row, stated with
an equality-form Problem 11 optimum.  The Lemma 13 pivot-support certificate is
derived internally.
-/
theorem paper_theorem4_misestimation_with_fairness_large_typeZero_from_equalized_problem11_auto
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
  exact E.theorem4_misestimation_with_fairness_large_typeZero_from_equalized_problem11_auto
    R reps hn htrue hred heps hbase hbeta hbeta_half hdec hpos hsmall
    ρ ell heq

/--
Appendix E, Theorem 4 fairness-constrained large-misestimation wrapper for a
cold-start user whose true preferences are the second opposing row, stated with
an equality-form Problem 11 optimum.  The Lemma 13 pivot-support certificate is
derived internally.
-/
theorem paper_theorem4_misestimation_with_fairness_large_typeOne_from_equalized_problem11_auto
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
  exact E.theorem4_misestimation_with_fairness_large_typeOne_from_equalized_problem11_auto
    R reps hn htrue hred heps hbase hbeta hbeta_half hdec hpos hsmall
    ρ ell heq

/--
Appendix E, Theorem 4 fairness-constrained large-misestimation wrapper for a
cold-start user whose true preferences are the first opposing row, stated with
the paper's real equality-form Problem 11 optimal BFS data.
-/
theorem paper_theorem4_misestimation_with_fairness_large_typeZero_from_equalityFormOptimalBFS
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
  exact E.theorem4_misestimation_with_fairness_large_typeZero_from_equalityFormOptimalBFS
    R reps hn htrue hred heps hbase hbeta hbeta_half hdec hpos hsmall hbfs

/--
Appendix E, Theorem 4 fairness-constrained large-misestimation wrapper for a
cold-start user whose true preferences are the second opposing row, stated with
the paper's real equality-form Problem 11 optimal BFS data.
-/
theorem paper_theorem4_misestimation_with_fairness_large_typeOne_from_equalityFormOptimalBFS
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
  exact E.theorem4_misestimation_with_fairness_large_typeOne_from_equalityFormOptimalBFS
    R reps hn htrue hred heps hbase hbeta hbeta_half hdec hpos hsmall hbfs

/--
Appendix E, Theorem 4 fairness-constrained large-misestimation wrapper:
odd-center closed Problem 11 construction, first true cold-start row.
-/
theorem paper_theorem4_misestimation_with_fairness_large_typeZero_from_closed_problem11_center
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
  exact E.theorem4_misestimation_with_fairness_large_typeZero_from_closed_problem11_center
    R reps hn htrue hred heps hbase hbeta hbeta_half hdec hpos hsmall hcenter

/--
Appendix E, Theorem 4 fairness-constrained large-misestimation wrapper:
odd-center closed Problem 11 construction, second true cold-start row.
-/
theorem paper_theorem4_misestimation_with_fairness_large_typeOne_from_closed_problem11_center
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
  exact E.theorem4_misestimation_with_fairness_large_typeOne_from_closed_problem11_center
    R reps hn htrue hred heps hbase hbeta hbeta_half hdec hpos hsmall hcenter

/--
Appendix E, Theorem 4 fairness-constrained large-misestimation wrapper:
even-center closed Problem 11 construction, first true cold-start row.
-/
theorem paper_theorem4_misestimation_with_fairness_large_typeZero_from_closed_problem11_succ_center
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
  exact E.theorem4_misestimation_with_fairness_large_typeZero_from_closed_problem11_succ_center
    R reps hn htrue hred heps hbase hbeta hbeta_half hdec hpos hsmall hsucc

/--
Appendix E, Theorem 4 fairness-constrained large-misestimation wrapper:
even-center closed Problem 11 construction, second true cold-start row.
-/
theorem paper_theorem4_misestimation_with_fairness_large_typeOne_from_closed_problem11_succ_center
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
  exact E.theorem4_misestimation_with_fairness_large_typeOne_from_closed_problem11_succ_center
    R reps hn htrue hred heps hbase hbeta hbeta_half hdec hpos hsmall hsucc

/--
Appendix E, Theorem 4 fairness-constrained large-misestimation wrapper:
odd-center closed Problem 11 construction with the paper's geometric value
vector, first true cold-start row.
-/
theorem paper_theorem4_misestimation_with_fairness_large_typeZero_from_smallValueVector_closed_problem11_center
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
  exact E.theorem4_misestimation_with_fairness_large_typeZero_from_smallValueVector_closed_problem11_center
    R reps hn htrue hred heps hbase hbeta hbeta_half hcenter

/--
Appendix E, Theorem 4 fairness-constrained large-misestimation wrapper:
odd-center closed Problem 11 construction with the paper's geometric value
vector, second true cold-start row.
-/
theorem paper_theorem4_misestimation_with_fairness_large_typeOne_from_smallValueVector_closed_problem11_center
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
  exact E.theorem4_misestimation_with_fairness_large_typeOne_from_smallValueVector_closed_problem11_center
    R reps hn htrue hred heps hbase hbeta hbeta_half hcenter

/--
Appendix E, Theorem 4 fairness-constrained large-misestimation wrapper:
even-center closed Problem 11 construction with the paper's geometric value
vector, first true cold-start row.
-/
theorem paper_theorem4_misestimation_with_fairness_large_typeZero_from_smallValueVector_closed_problem11_succ_center
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
  exact E.theorem4_misestimation_with_fairness_large_typeZero_from_smallValueVector_closed_problem11_succ_center
    R reps hn htrue hred heps hbase hbeta hbeta_half hsucc

/--
Appendix E, Theorem 4 fairness-constrained large-misestimation wrapper:
even-center closed Problem 11 construction with the paper's geometric value
vector, second true cold-start row.
-/
theorem paper_theorem4_misestimation_with_fairness_large_typeOne_from_smallValueVector_closed_problem11_succ_center
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
  exact E.theorem4_misestimation_with_fairness_large_typeOne_from_smallValueVector_closed_problem11_succ_center
    R reps hn htrue hred heps hbase hbeta hbeta_half hsucc

/--
Appendix E, Theorem 4 two-bullet wrapper: for the constructed geometric value
vector and odd midpoint, the no-fairness price is at most `1/2` while the
fairness-constrained price can exceed `1 - eps`, first true cold-start row.
-/
theorem paper_theorem4_misestimation_tradeoff_typeZero_from_smallValueVector_closed_problem11_center
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
  exact E.theorem4_misestimation_tradeoff_typeZero_from_smallValueVector_closed_problem11_center
    R reps hn htrue hred heps hbase hbeta hbeta_half hcenter

/--
Appendix E, Theorem 4 two-bullet wrapper: constructed geometric value vector,
odd midpoint, second true cold-start row.
-/
theorem paper_theorem4_misestimation_tradeoff_typeOne_from_smallValueVector_closed_problem11_center
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
  exact E.theorem4_misestimation_tradeoff_typeOne_from_smallValueVector_closed_problem11_center
    R reps hn htrue hred heps hbase hbeta hbeta_half hcenter

/--
Appendix E, Theorem 4 two-bullet wrapper: constructed geometric value vector,
even midpoint, first true cold-start row.
-/
theorem paper_theorem4_misestimation_tradeoff_typeZero_from_smallValueVector_closed_problem11_succ_center
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
  exact E.theorem4_misestimation_tradeoff_typeZero_from_smallValueVector_closed_problem11_succ_center
    R reps hn htrue hred heps hbase hbeta hbeta_half hsucc

/--
Appendix E, Theorem 4 two-bullet wrapper: constructed geometric value vector,
even midpoint, second true cold-start row.
-/
theorem paper_theorem4_misestimation_tradeoff_typeOne_from_smallValueVector_closed_problem11_succ_center
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
  exact E.theorem4_misestimation_tradeoff_typeOne_from_smallValueVector_closed_problem11_succ_center
    R reps hn htrue hred heps hbase hbeta hbeta_half hsucc

/--
Appendix E, Theorem 4 fairness-constrained large-misestimation wrapper for a
cold-start user whose true preferences are the first opposing row, stated with
an equality-form Problem 11 optimum and the two no-gap conclusions completing
Lemma 13.
-/
theorem paper_theorem4_misestimation_with_fairness_large_typeZero_from_equalized_problem11_noGap
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
  exact E.theorem4_misestimation_with_fairness_large_typeZero_from_equalized_problem11_noGap
    R reps hn htrue hred heps hbase hbeta hbeta_half hdec hpos hsmall
    ρ ell heq hx hz

/--
Appendix E, Theorem 4 fairness-constrained large-misestimation wrapper for a
cold-start user whose true preferences are the second opposing row, stated with
an equality-form Problem 11 optimum and the two no-gap conclusions completing
Lemma 13.
-/
theorem paper_theorem4_misestimation_with_fairness_large_typeOne_from_equalized_problem11_noGap
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
  exact E.theorem4_misestimation_with_fairness_large_typeOne_from_equalized_problem11_noGap
    R reps hn htrue hred heps hbase hbeta hbeta_half hdec hpos hsmall
    ρ ell heq hx hz

end EstimatedRecommendationModel

namespace TypePolicy

/--
Appendix D, Lemma 4, Part 1: a two-type basic feasible solution has at most
`n + 1` positive `x_j,y_j` variables.
-/
theorem paper_lemma4_problem6_active_pairs_le_n_add_one
    {n : ℕ} [NeZero n]
    (ρ : TypePolicy 2 n) (hcert : BasicFeasibleSupportCertificate ρ) :
    activeTypeItemPairsCard ρ ≤ n + 1 := by
  exact activePairsCard_le_n_add_one_of_basicFeasibleSupportCertificate_two
    ρ hcert

/--
Appendix D, Lemma 4, Part 1: a two-type basic feasible solution has at least
`n - 1` zero `x_j,y_j` variables.
-/
theorem paper_lemma4_problem6_inactive_pairs_ge_n_sub_one
    {n : ℕ} [NeZero n]
    (ρ : TypePolicy 2 n) (hcert : BasicFeasibleSupportCertificate ρ) :
    n - 1 ≤ inactiveTypeItemPairsCard ρ := by
  exact inactivePairsCard_ge_n_sub_one_of_basicFeasibleSupportCertificate_two
    ρ hcert

/--
Appendix D threshold-support count: a two-type threshold-support policy has at
least `n - 1` zero `x_j,y_j` coordinates.
-/
theorem paper_lemma4_problem6_inactive_pairs_ge_n_sub_one_of_thresholdSupport
    {n : ℕ} (ρ : TypePolicy 2 n) (hthreshold : TwoTypeThresholdSupport ρ) :
    n - 1 ≤ inactiveTypeItemPairsCard ρ := by
  exact inactivePairsCard_ge_n_sub_one_of_twoTypeThresholdSupport
    ρ hthreshold

/--
Appendix D threshold-support count: in the two-type Problem 6 setting, the
threshold support shape itself supplies the paper's basic-feasible support
certificate.
-/
theorem paper_lemma4_problem6_basicFeasibleSupportCertificate_of_thresholdSupport
    {n : ℕ} (ρ : TypePolicy 2 n) (hthreshold : TwoTypeThresholdSupport ρ) :
    BasicFeasibleSupportCertificate ρ := by
  exact basicFeasibleSupportCertificate_of_twoTypeThresholdSupport
    ρ hthreshold

/--
Appendix D, Lemma 4, Part 2 threshold-support extraction: after the
perturbation argument has ruled out gaps in the `x` and `y` supports, the
shared-item sparsity bound forces a single pivot `t`.
-/
theorem paper_lemma4_problem6_thresholdSupport_of_zeroClosed_of_sharedBound
    {n : ℕ} [NeZero n] (ρ : TypePolicy 2 n)
    (hx : TwoTypeXZeroClosed ρ)
    (hy : TwoTypeYZeroClosed ρ)
    (hshared : SharedItemsBound ρ) :
    TwoTypeThresholdSupport ρ := by
  exact twoTypeThresholdSupport_of_zeroClosed_of_sharedBound
    ρ hx hy hshared

/--
Proposition 2 sparse shared-item consequence.

If a reduced type-level policy has at most `n + K - 1` active type-item pairs
and every item is recommended by at least one type, then at most `K - 1` items
are shared by multiple user types. This is the finite counting half of the
paper's sparse-support statement, separated from the LP basic-feasible-solution
theorem that supplies the active-pair bound.
-/
theorem paper_sparse_shared_items_of_active_pairs_bound
    {K n : ℕ} [NeZero K]
    (ρ : TypePolicy K n)
    (hactive : ActivePairsBound ρ)
    (hcover : ∀ j : Item n, ∃ k, ρ k j ≠ 0) :
    SharedItemsBound ρ := by
  exact sharedItemsBound_of_activePairsBound_of_item_coverage ρ hactive hcover

/--
Proposition 2 sparse-shape consequence from active-pair sparsity and item
coverage.
-/
theorem paper_sparse_shape_of_active_pairs_bound
    {K n : ℕ} [NeZero K]
    (ρ : TypePolicy K n)
    (hactive : ActivePairsBound ρ)
    (hcover : ∀ j : Item n, ∃ k, ρ k j ≠ 0) :
    SparseShape ρ := by
  exact sparseShape_of_activePairsBound_of_item_coverage ρ hactive hcover

/--
Proposition 2 sparse shared-item consequence with item coverage discharged from
positive reduced item fairness.

If the reduced type policy has positive minimum normalized item utility, then
every item is recommended by at least one type. Therefore the paper's
basic-feasible-solution active-pair bound implies that at most `K - 1` items
are shared by multiple user types.
-/
theorem paper_sparse_shared_items_of_active_pairs_bound_of_positive_item_fairness
    {K n : ℕ} [NeZero K] [NeZero n]
    (T : TypeWeightedRecommendationModel K n) (ρ : TypePolicy K n)
    (hactive : ActivePairsBound ρ)
    (hitem_pos : 0 < TypeWeightedRecommendationModel.itemFairness T ρ) :
    SharedItemsBound ρ := by
  exact sharedItemsBound_of_activePairsBound_of_item_coverage ρ hactive
    (TypeWeightedRecommendationModel.item_coverage_of_itemFairness_pos T ρ hitem_pos)

/--
Proposition 2 sparse-shape consequence with item coverage discharged from
positive reduced item fairness.
-/
theorem paper_sparse_shape_of_active_pairs_bound_of_positive_item_fairness
    {K n : ℕ} [NeZero K] [NeZero n]
    (T : TypeWeightedRecommendationModel K n) (ρ : TypePolicy K n)
    (hactive : ActivePairsBound ρ)
    (hitem_pos : 0 < TypeWeightedRecommendationModel.itemFairness T ρ) :
    SparseShape ρ := by
  exact sparseShape_of_activePairsBound_of_item_coverage ρ hactive
    (TypeWeightedRecommendationModel.item_coverage_of_itemFairness_pos T ρ hitem_pos)

/--
Lemma `IF* > 0` from the paper, in the reduced type-level model.

Strictly positive type weights and utility entries imply that the maximal
reduced item-fairness value is strictly positive; the proof is witnessed by the
uniform policy.
-/
theorem paper_reduced_optimal_item_fairness_positive
    {K n : ℕ} [NeZero K] [NeZero n]
    (T : TypeWeightedRecommendationModel K n)
    (hWeight : T.PositiveWeights) (hUtil : T.PositiveUtilities) :
    0 < TypeWeightedRecommendationModel.optimalItemFairness T := by
  exact TypeWeightedRecommendationModel.optimalItemFairness_pos_of_positive
    T hWeight hUtil

/--
Proposition 2 active-support bound from the LP basic-feasible-solution support
count.

This is the finite arithmetic part of the paper's BFS sparsity proof:
`nK + 1` variables, `n + K` equality constraints, and therefore at least
`nK + 1 - (n + K)` binding nonnegativity constraints imply at most
`n + K - 1` positive type-item pairs.
-/
theorem paper_active_pairs_bound_of_basic_feasible_support_certificate
    {K n : ℕ} [NeZero K] [NeZero n]
    (ρ : TypePolicy K n)
    (hcert : BasicFeasibleSupportCertificate ρ) :
    ActivePairsBound ρ := by
  exact activePairsBound_of_basicFeasibleSupportCertificate ρ hcert

/--
Proposition 2 active-support bound from an actual basic feasible solution of
the concrete reduced equality-form LP.  The binding-zero count is derived from
the active constraint basis rather than supplied as a premise.
-/
theorem paper_active_pairs_bound_of_equality_lp_basic_feasible
    {K n : ℕ} [NeZero K] [NeZero n]
    (T : TypeWeightedRecommendationModel K n)
    (ρ : TypePolicy K n) (ell : ℝ)
    (hbfs : T.IsEqualityLPBasicFeasible ρ ell) :
    ActivePairsBound ρ := by
  exact activePairsBound_of_basicFeasibleSupportCertificate ρ
    (ReducedEqualityLPBasicFeasible.basicFeasibleSupportCertificate hbfs)

/--
Proposition 2 sparse shared-item consequence for a maximal-item-fairness
reduced optimum.

The only remaining hypothesis is the paper's basic-feasible-solution
active-pair bound. Positivity of the item-fairness optimum is discharged from
strictly positive weights/utilities.
-/
theorem paper_sparse_shared_items_of_active_pairs_bound_of_maximal_optimum
    {K n : ℕ} [NeZero K] [NeZero n]
    (T : TypeWeightedRecommendationModel K n) (ρ : TypePolicy K n)
    (hWeight : T.PositiveWeights) (hUtil : T.PositiveUtilities)
    (hactive : ActivePairsBound ρ)
    (hitemOptimal :
      TypeWeightedRecommendationModel.itemFairness T ρ =
        TypeWeightedRecommendationModel.optimalItemFairness T) :
    SharedItemsBound ρ := by
  have hopt_pos :
      0 < TypeWeightedRecommendationModel.optimalItemFairness T :=
    TypeWeightedRecommendationModel.optimalItemFairness_pos_of_positive
      T hWeight hUtil
  have hitem_pos : 0 < TypeWeightedRecommendationModel.itemFairness T ρ := by
    rw [hitemOptimal]
    exact hopt_pos
  exact sharedItemsBound_of_activePairsBound_of_item_coverage ρ hactive
    (TypeWeightedRecommendationModel.item_coverage_of_itemFairness_pos T ρ hitem_pos)

/--
Proposition 2 sparse-shape consequence for a maximal-item-fairness reduced
optimum, with positivity discharged from strictly positive data.
-/
theorem paper_sparse_shape_of_active_pairs_bound_of_maximal_optimum
    {K n : ℕ} [NeZero K] [NeZero n]
    (T : TypeWeightedRecommendationModel K n) (ρ : TypePolicy K n)
    (hWeight : T.PositiveWeights) (hUtil : T.PositiveUtilities)
    (hactive : ActivePairsBound ρ)
    (hitemOptimal :
      TypeWeightedRecommendationModel.itemFairness T ρ =
        TypeWeightedRecommendationModel.optimalItemFairness T) :
    SparseShape ρ := by
  exact ⟨hactive,
    paper_sparse_shared_items_of_active_pairs_bound_of_maximal_optimum
      T ρ hWeight hUtil hactive hitemOptimal⟩

/--
Proposition 2 sparse shared-item consequence for a maximal-item-fairness
reduced optimum, using the paper's basic-feasible-solution support count
directly.
-/
theorem paper_sparse_shared_items_of_basic_feasible_maximal_optimum
    {K n : ℕ} [NeZero K] [NeZero n]
    (T : TypeWeightedRecommendationModel K n) (ρ : TypePolicy K n)
    (ell : ℝ)
    (hWeight : T.PositiveWeights) (hUtil : T.PositiveUtilities)
    (hbfs : T.IsEqualityLPBasicFeasible ρ ell)
    (hLPOptimal : ell = TypeWeightedRecommendationModel.optimalItemFairness T) :
    SharedItemsBound ρ := by
  exact paper_sparse_shared_items_of_active_pairs_bound_of_maximal_optimum
    T ρ hWeight hUtil
    (paper_active_pairs_bound_of_equality_lp_basic_feasible T ρ ell hbfs)
    ((T.itemFairness_eq_ell_of_equalityLPBasicFeasible
      hWeight hUtil ρ ell hbfs).trans hLPOptimal)

/--
Proposition 2 sparse-shape consequence for a maximal-item-fairness reduced
optimum, using the paper's basic-feasible-solution support count directly.
-/
theorem paper_sparse_shape_of_basic_feasible_maximal_optimum
    {K n : ℕ} [NeZero K] [NeZero n]
    (T : TypeWeightedRecommendationModel K n) (ρ : TypePolicy K n)
    (ell : ℝ)
    (hWeight : T.PositiveWeights) (hUtil : T.PositiveUtilities)
    (hbfs : T.IsEqualityLPBasicFeasible ρ ell)
    (hLPOptimal : ell = TypeWeightedRecommendationModel.optimalItemFairness T) :
    SparseShape ρ := by
  exact paper_sparse_shape_of_active_pairs_bound_of_maximal_optimum
    T ρ hWeight hUtil
    (paper_active_pairs_bound_of_equality_lp_basic_feasible T ρ ell hbfs)
    ((T.itemFairness_eq_ell_of_equalityLPBasicFeasible
      hWeight hUtil ρ ell hbfs).trans hLPOptimal)

end TypePolicy

/--
The Proposition 2 conclusions established for the explicit reduced equality
LP: a finite linear description of `S_symm`, existence of a symmetric optimum,
the reduced-LP BFS active-support bound, and the optimal reduced-LP BFS
shared-item bound.

The separate linear-equivalence theorem transporting basic feasible solutions
between Proposition 1's user-coordinate LP on `S_symm` and this reduced
type-coordinate LP has not yet been formalized.
-/
theorem paper_proposition2_reduced_lp_conclusions
    {m n K : ℕ} [NeZero m] [NeZero n] [NeZero K]
    (S : RecommendationModel.SymmetricData m n K)
    (reps : UserTypeAssignment.TypeRepresentatives S.types)
    (hPos : S.model.Positive) :
    ∃ _D : RecommendationModel.FiniteLinearPolicySetDescription
        (UserTypeAssignment.SymmetricPolicies (n := n) S.types),
      (∃ ρsym : Policy m n,
        UserTypeAssignment.IsTypeSymmetric S.types ρsym ∧
          RecommendationModel.IsOptimalAtLevel S.model 1 ρsym) ∧
      (∀ (ρ : TypePolicy K n) (ell : ℝ),
        (S.canonicalReduction reps).reduced.IsEqualityLPBasicFeasible ρ ell →
          TypePolicy.ActivePairsBound ρ) ∧
      (∀ (ρ : TypePolicy K n) (ell : ℝ),
        (S.canonicalReduction reps).reduced.IsEqualityLPBasicFeasible ρ ell →
        ell = TypeWeightedRecommendationModel.optimalItemFairness
            (S.canonicalReduction reps).reduced →
          TypePolicy.SharedItemsBound ρ) := by
  let R : ReductionWitness m n K := S.canonicalReduction reps
  have hWeight : R.reduced.PositiveWeights :=
    R.reduced_positiveWeights_of_representatives reps
  have hUtil : R.reduced.PositiveUtilities :=
    R.reduced_positiveUtilities_of_positive reps hPos
  refine ⟨UserTypeAssignment.symmetricPoliciesFiniteLinearDescription
      (n := n) S.types, ?_, ?_, ?_⟩
  · exact S.paper_proposition2_symmetric_optimum_exists_of_positive reps hPos
  · intro ρ ell hbfs
    exact TypePolicy.paper_active_pairs_bound_of_equality_lp_basic_feasible
      R.reduced ρ ell hbfs
  · intro ρ ell hbfs hLPOptimal
    exact TypePolicy.paper_sparse_shared_items_of_basic_feasible_maximal_optimum
      R.reduced ρ ell hWeight hUtil hbfs hLPOptimal

end GCG24UserItemFairness
