import GCG24UserItemFairness.MainTheorems
import GCG24UserItemFairness.Examples
import GCG24UserItemFairness.Assumptions
import Mathlib.Analysis.Convex.Extreme

/-!
# Paper Interface: User-Item Fairness Tradeoffs

This compact interface exposes the main paper definitions and direct named
result statements for the verified user-item fairness development.  The full
LP, symmetry, and misestimation proof layers remain in the sibling Lean files.
-/

namespace GCG24UserItemFairness
namespace ProofBridge

open scoped BigOperators

noncomputable section

/-! ## Paper Definitions -/

/-- Recommendation utility matrix `w_{ij}` for users and items. -/
def recommendationUtility {m n : ℕ} (W : RecommendationModel m n)
    (u : User m) (j : Item n) : ℝ :=
  W.utility u j

/-- Raw user utility `sum_j w_ij rho_ij`. -/
def rawUserUtility {m n : ℕ}
    (W : RecommendationModel m n) (ρ : Policy m n) (u : User m) : ℝ :=
  AppliedModelingLib.Policy.agentScore ρ W.utility u

/-- Normalized user utility `U_i(rho)`. -/
def normalizedUserUtility {m n : ℕ} [NeZero n]
    (W : RecommendationModel m n) (ρ : Policy m n) (u : User m) : ℝ :=
  rawUserUtility W ρ u / RecommendationModel.bestItemUtility W u

/--
Source status: direct source text
User fairness objective for a recommendation policy.
-/
def userFairness {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n) (ρ : Policy m n) : ℝ :=
  AppliedModelingLib.finiteMin (normalizedUserUtility W ρ)

/-- The direct paper-facing user objective is definitionally the library
objective; no policy or utility condition is introduced by this interface. -/
theorem userFairness_eq_library {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n) (ρ : Policy m n) :
    userFairness W ρ = RecommendationModel.userFairness W ρ :=
  rfl

/-- Raw item utility `sum_i w_ij rho_ij`. -/
def rawItemUtility {m n : ℕ}
    (W : RecommendationModel m n) (ρ : Policy m n) (j : Item n) : ℝ :=
  ∑ u, W.utility u j * (ρ u j).toReal

/-- Item normalizer `sum_i w_ij`. -/
def itemNormalizer {m n : ℕ}
    (W : RecommendationModel m n) (j : Item n) : ℝ :=
  ∑ u, W.utility u j

/-- Normalized item utility `I_j(rho)`. -/
def normalizedItemUtility {m n : ℕ}
    (W : RecommendationModel m n) (ρ : Policy m n) (j : Item n) : ℝ :=
  rawItemUtility W ρ j / itemNormalizer W j

/--
Source status: direct source text
Item fairness objective for a recommendation policy.
-/
def itemFairness {m n : ℕ} [NeZero n]
    (W : RecommendationModel m n) (ρ : Policy m n) : ℝ :=
  AppliedModelingLib.finiteMin (normalizedItemUtility W ρ)

/--
The paper-facing quotient agrees with the library definition on every Lean
model: Lean division already evaluates a zero denominator as zero, matching
the library's explicit totalization.  The source's strict positivity still
ensures this defensive branch is outside its intended ratio domain.
-/
theorem normalizedItemUtility_eq_library {m n : ℕ}
    (W : RecommendationModel m n) (ρ : Policy m n) (j : Item n) :
    normalizedItemUtility W ρ j = RecommendationModel.normalizedItemUtility W ρ j := by
  unfold normalizedItemUtility RecommendationModel.normalizedItemUtility
  dsimp only
  by_cases hden : RecommendationModel.itemNormalizer W j = 0
  · rw [dif_pos hden]
    change RecommendationModel.rawItemUtility W ρ j /
        RecommendationModel.itemNormalizer W j = 0
    simp [hden]
  · rw [dif_neg hden]
    rfl

/-- The direct paper-facing item objective agrees with the library objective. -/
theorem itemFairness_eq_library {m n : ℕ} [NeZero n]
    (W : RecommendationModel m n) (ρ : Policy m n) :
    itemFairness W ρ = RecommendationModel.itemFairness W ρ := by
  unfold itemFairness RecommendationModel.itemFairness
  apply congrArg AppliedModelingLib.finiteMin
  funext j
  exact normalizedItemUtility_eq_library W ρ j

/-- Price of fairness at item-fairness level `gamma`. -/
def priceOfFairnessAt {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n) (γ : ℝ) : ℝ :=
  (RecommendationModel.optimalUserFairnessAtLevel W 0 -
      RecommendationModel.optimalUserFairnessAtLevel W γ) /
    RecommendationModel.optimalUserFairnessAtLevel W 0

/--
The paper-facing quotient agrees with the library's explicit zero-baseline
totalization on every Lean model, because Lean division by zero is itself
zero.  The source's strict positivity remains the intended ordinary-ratio
domain.
-/
theorem priceOfFairnessAt_eq_library {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n) (γ : ℝ) :
    priceOfFairnessAt W γ = RecommendationModel.priceOfFairnessAt W γ := by
  unfold priceOfFairnessAt RecommendationModel.priceOfFairnessAt
  dsimp only
  by_cases hbase : RecommendationModel.optimalUserFairnessAtLevel W 0 = 0
  · rw [dif_pos hbase]
    simp [hbase]
  · rw [dif_neg hbase]

/-- Price of maximal item fairness. -/
def priceOfFairness {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n) : ℝ :=
  priceOfFairnessAt W 1

/-- The direct maximal-item-fairness price agrees with the library definition. -/
theorem priceOfFairness_eq_library {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n) :
    priceOfFairness W = RecommendationModel.priceOfFairness W := by
  unfold priceOfFairness RecommendationModel.priceOfFairness
  exact priceOfFairnessAt_eq_library W 1

/-- Problem 1 at item-fairness level `γ`: feasibility and attainment of the
gamma-constrained user-fairness optimum. -/
def solvesProblemOne {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n) (γ : ℝ) (ρ : Policy m n) : Prop :=
  RecommendationModel.IsOptimalAtLevel W γ ρ

/-- The source Problem 1 predicate is exactly the underlying constrained-optimum
predicate; this theorem makes the paper-facing definition auditable without
turning an arbitrary policy into a proved optimizer. -/
theorem solvesProblemOne_iff {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n) (γ : ℝ) (ρ : Policy m n) :
    solvesProblemOne W γ ρ ↔ RecommendationModel.IsOptimalAtLevel W γ ρ :=
  Iff.rfl

/-- Price of misestimation for an estimated-Problem-1 optimizer. -/
def priceOfMisestimation {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n) (γ : ℝ) (ρhat : Policy m n)
    (hEstimatedOptimal : solvesProblemOne E.estimatedModel γ ρhat) : ℝ :=
  (RecommendationModel.optimalUserFairnessAtLevel E.trueModel γ -
      RecommendationModel.userFairness E.trueModel ρhat) /
    RecommendationModel.optimalUserFairnessAtLevel E.trueModel γ

/--
The displayed source quotient agrees with the library's totalized expression.
The optimizer proof is retained because the source defines this quantity only
for a policy selected by the estimated optimization problem.
-/
theorem priceOfMisestimation_eq_library {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n) (γ : ℝ) (ρhat : Policy m n)
    (hEstimatedOptimal : solvesProblemOne E.estimatedModel γ ρhat) :
    priceOfMisestimation E γ ρhat hEstimatedOptimal =
      E.priceOfMisestimation γ ρhat := by
  unfold priceOfMisestimation EstimatedRecommendationModel.priceOfMisestimation
  dsimp only
  by_cases hbase : RecommendationModel.optimalUserFairnessAtLevel E.trueModel γ = 0
  · rw [dif_pos hbase]
    simp [hbase]
  · rw [dif_neg hbase]

/-! ## Named Results -/

/-! ### Example 1 -/

/--
Auxiliary fixed-2x2 calculation for the diverse-preferences illustration in
Example 1. This is not a proof of the source's general favorite-item
optimality assertion.
-/
theorem example1_diverse_favorite_policy_user_fairness :
    RecommendationModel.userFairness twoByTwoModel diagonalPolicy = 1 := by
  exact paper_example1_diagonal_userFairness_eq_one

/--
Auxiliary fixed-2x2 item-fairness calculation for Example 1. It receives no
source-claim proof credit for the source's general population model.
-/
theorem example1_diverse_favorite_policy_item_fairness :
    RecommendationModel.itemFairness twoByTwoModel diagonalPolicy = (10 : ℝ) / 11 := by
  exact paper_example1_diagonal_itemFairness_eq

/--
Auxiliary algebraic implication used to check the homogeneous-preferences
illustration in Example 1. The unnumbered example is outside normal
named-theory proof credit.
-/
theorem example1_homogeneous_tradeoff_bound
    {epsilon rho1 rho2 Umin Imin : ℝ}
    (hrho : rho2 = 1 - rho1)
    (hitem : Imin ≤ rho2)
    (huser : Umin ≤ rho1 + epsilon) :
    Umin + Imin ≤ 1 + epsilon := by
  exact paper_example1_homogeneous_tradeoff_bound hrho hitem huser

/-- Transparent specification for the auxiliary homogeneous-example implication. -/
def example1_homogeneous_tradeoff_boundSpec
    {epsilon rho1 rho2 Umin Imin : ℝ}
    (hrho : rho2 = 1 - rho1)
    (hitem : Imin ≤ rho2)
    (huser : Umin ≤ rho1 + epsilon) : Prop :=
  Umin + Imin ≤ 1 + epsilon

/-! ### Appendix lemma review rows -/

/-- Appendix C, Lemma 1: the optimal item-fairness value is positive. -/
theorem appendix_c_lemma1_item_fairness_positive
    {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n) (hPositive : W.Positive) :
    0 < W.optimalItemFairness :=
  RecommendationModel.paper_lemma1_optimal_item_fairness_positive W hPositive

/-- Transparent source-facing specification for Appendix C, Lemma 1. -/
def appendix_c_lemma1_item_fairness_positiveSpec
    {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n) (hPositive : W.Positive) : Prop :=
  0 < W.optimalItemFairness

/--
Appendix C, Lemma 2 proof component: the epigraph LP has the same objective
value as item fairness. The paper's named lemma additionally asserts equality
of optimizer sets; that complete result is exposed immediately below.
-/
theorem appendix_c_lemma2_item_fairness_lp_value
    {m n : ℕ} [NeZero n]
    (W : RecommendationModel m n) (hNonnegative : W.Nonnegative) :
    W.optimalItemFairnessLPValue = W.optimalItemFairness :=
  RecommendationModel.paper_lemma2_item_fairness_lp_value_eq W hNonnegative

/--
Appendix C, Lemma 2: the original max-min item-fairness optimizer set equals
the policy projection of the equality-form LP optimizer set. In particular,
the equality LP imposes `I_j(rho) = ell` for every item and no optimal policy
is omitted.

Source status: direct source result.
-/
theorem appendix_c_lemma2_item_fairness_equality_lp_solution_set
    {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n) (hPositive : W.Positive) (rho : Policy m n) :
    W.itemFairness rho = W.optimalItemFairness ↔
      ∃ ell : ℝ,
        W.itemFairnessEqualityLPFeasible rho ell ∧
          ∀ rho' : Policy m n, ∀ ell' : ℝ,
            W.itemFairnessEqualityLPFeasible rho' ell' → ell' ≤ ell :=
  RecommendationModel.paper_lemma2_item_fairness_equality_lp_solution_set_of_positive
    W hPositive rho

/-- Appendix D, Lemma 3: unconstrained user-fairness baseline. -/
theorem appendix_d_lemma3_unconstrained_baseline
    {n : ℕ} [NeZero n] {alpha : ℝ} {v : Item n → ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : OpposingTypes.StrictlyDecreasingByIndex v) :
    TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
      (OpposingTypes.twoTypeReducedModel alpha v) 0 = 1 :=
  RecommendationModel.paper_lemma3_unconstrained_user_fairness_eq_one
    alpha v halpha0 halpha1 hpos hdec

/--
Appendix D, Lemma 4: Problem 6 has a unique optimal equality-form solution,
and that solution has threshold support.  The optimizer, value, support, and
uniqueness conclusions are all visible; no basic-feasible or optimizer package
is a theorem premise.

Source status: direct source result.
-/
theorem appendix_d_lemma4_problem6_unique_sparse_solution
    {n : ℕ} [NeZero n] {alpha : ℝ} {v : Item n → ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : OpposingTypes.StrictlyDecreasingByIndex v) :
    ∃ (t : Item n) (ρstar : TypePolicy 2 n) (ellstar : ℝ),
      (∀ j : Item n,
        OpposingTypes.pairShare alpha v j * (ρstar 0 j).toReal +
          (1 - OpposingTypes.pairShare alpha v j) * (ρstar 1 j).toReal =
            ellstar) ∧
      (∀ (ρ : TypePolicy 2 n) (ell : ℝ),
        OpposingTypes.problem6LPFeasible alpha v ρ ell → ell ≤ ellstar) ∧
      (∀ {j : Item n}, t.val < j.val → (ρstar 0 j).toReal = 0) ∧
      (∀ {j : Item n}, j.val < t.val → (ρstar 1 j).toReal = 0) ∧
      ∀ (ρ : TypePolicy 2 n) (ell : ℝ),
        (∀ j : Item n,
          OpposingTypes.pairShare alpha v j * (ρ 0 j).toReal +
            (1 - OpposingTypes.pairShare alpha v j) * (ρ 1 j).toReal = ell) →
        (∀ (ρ' : TypePolicy 2 n) (ell' : ℝ),
          OpposingTypes.problem6LPFeasible alpha v ρ' ell' → ell' ≤ ell) →
        ρ = ρstar ∧ ell = ellstar := by
  let t : Item n :=
    OpposingTypes.problem6FirstClosedPivot alpha v halpha0 halpha1 hpos
  let ρstar : TypePolicy 2 n :=
    OpposingTypes.problem6FirstClosedPolicy alpha v halpha0 halpha1 hpos
  let ellstar : ℝ := OpposingTypes.problem6ClosedValue alpha v t
  have hstar :=
    OpposingTypes.problem6FirstClosedPolicy_item_eq_and_optimal
      halpha0 halpha1 hpos hdec
  let cert : OpposingTypes.Problem6ClosedOptimalityCertificate alpha v t :=
    OpposingTypes.problem6FirstClosedPivot_optimalityCertificate
      halpha0 halpha1 hpos hdec
  have hsupport :=
    OpposingTypes.problem6PolicyOptimal_equalized_thresholdSupport_of_closedCertificate
      halpha0 halpha1 hpos hdec cert hstar.1 hstar.2
  refine ⟨t, ρstar, ellstar, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [t, ρstar, ellstar] using hstar.1
  · intro ρ ell hfeas
    simpa [t, ellstar] using hstar.2.2 ρ ell hfeas
  · intro j hj
    exact congrArg ENNReal.toReal (hsupport.1 hj)
  · intro j hj
    exact congrArg ENNReal.toReal (hsupport.2 hj)
  · intro ρ ell hitem_eq hupper
    have hopt : OpposingTypes.Problem6PolicyOptimal alpha v ρ ell :=
      ⟨fun j => le_of_eq (hitem_eq j).symm, hupper⟩
    simpa [t, ρstar, ellstar] using
      OpposingTypes.problem6PolicyOptimal_equalized_eq_firstClosedPolicy
        halpha0 halpha1 hpos hdec hitem_eq hopt

/--
Appendix D, Lemma 5 proof component: an explicitly equalized threshold policy
has the displayed closed value.  This is not the source lemma's existence,
uniqueness, and coordinate formula.
-/
theorem appendix_d_lemma5_problem6_closed_form
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    {x y : Item n → ℝ} {ell : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hitem_eq : ∀ j : Item n,
      OpposingTypes.pairShare alpha v j * x j +
        (1 - OpposingTypes.pairShare alpha v j) * y j = ell)
    (hsum_x : (∑ j : Item n, x j) = 1)
    (hsum_y : (∑ j : Item n, y j) = 1)
    (hx_after : ∀ {j : Item n}, t.val < j.val → x j = 0)
    (hy_before : ∀ {j : Item n}, j.val < t.val → y j = 0) :
    ell = OpposingTypes.problem6ClosedValue alpha v t := by
  let hSparse : OpposingTypes.Problem6SparseEqualized alpha v t x y ell :=
    { item_eq := hitem_eq
      sum_x := hsum_x
      sum_y := hsum_y
      x_after_pivot_zero := hx_after
      y_before_pivot_zero := hy_before }
  exact OpposingTypes.paper_lemma5_problem6_closed_value
    halpha0 halpha1 hpos hSparse

/--
Appendix D, Lemma 5: the unique Problem 6 optimizer has the displayed value
and all threshold-coordinate formulas at its active pivot.

Source status: direct source result.
-/
theorem appendix_d_lemma5_problem6_active_optimizer_closed_form
    {n : ℕ} [NeZero n] {alpha : ℝ} {v : Item n → ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : OpposingTypes.StrictlyDecreasingByIndex v) :
    ∃ (ρstar : TypePolicy 2 n) (ellstar : ℝ),
      (∀ j : Item n,
        OpposingTypes.pairShare alpha v j * (ρstar 0 j).toReal +
          (1 - OpposingTypes.pairShare alpha v j) * (ρstar 1 j).toReal =
            ellstar) ∧
      (∀ (ρ : TypePolicy 2 n) (ell : ℝ),
        OpposingTypes.problem6LPFeasible alpha v ρ ell → ell ≤ ellstar) ∧
      (∀ (ρ : TypePolicy 2 n) (ell : ℝ),
        (∀ j : Item n,
          OpposingTypes.pairShare alpha v j * (ρ 0 j).toReal +
            (1 - OpposingTypes.pairShare alpha v j) * (ρ 1 j).toReal = ell) →
        (∀ (ρ' : TypePolicy 2 n) (ell' : ℝ),
          OpposingTypes.problem6LPFeasible alpha v ρ' ell' → ell' ≤ ell) →
        ρ = ρstar ∧ ell = ellstar) ∧
      let t : Item n := TypePolicy.lastActiveTypeZero ρstar
      ellstar = OpposingTypes.problem6ClosedValue alpha v t ∧
      (∀ {j : Item n}, j.val < t.val →
        (ρstar 0 j).toReal =
          ellstar / OpposingTypes.pairShare alpha v j) ∧
      (ρstar 0 t).toReal =
        1 - ellstar * OpposingTypes.problem6LeftSum alpha v t ∧
      (∀ {j : Item n}, t.val < j.val → (ρstar 0 j).toReal = 0) ∧
      (∀ {j : Item n}, j.val < t.val → (ρstar 1 j).toReal = 0) ∧
      (ρstar 1 t).toReal =
        1 - ellstar * OpposingTypes.problem6RightSum alpha v t ∧
      ∀ {j : Item n}, t.val < j.val →
        (ρstar 1 j).toReal =
          ellstar / (1 - OpposingTypes.pairShare alpha v j) := by
  let t0 : Item n :=
    OpposingTypes.problem6FirstClosedPivot alpha v halpha0 halpha1 hpos
  let ρstar : TypePolicy 2 n :=
    OpposingTypes.problem6FirstClosedPolicy alpha v halpha0 halpha1 hpos
  let ellstar : ℝ := OpposingTypes.problem6ClosedValue alpha v t0
  have hstar :=
    OpposingTypes.problem6FirstClosedPolicy_item_eq_and_optimal
      halpha0 halpha1 hpos hdec
  have hactive :=
    OpposingTypes.problem6PolicyOptimal_equalized_sparseActive
      halpha0 halpha1 hpos hdec hstar.1 hstar.2
  let t : Item n := TypePolicy.lastActiveTypeZero ρstar
  have hclosed :=
    OpposingTypes.problem6SparseEqualized_eq_closed
      halpha0 halpha1 hpos hactive.sparse
  refine ⟨ρstar, ellstar, ?_, ?_, ?_, ?_⟩
  · simpa [t0, ρstar, ellstar] using hstar.1
  · intro ρ ell hfeas
    simpa [t0, ellstar] using hstar.2.2 ρ ell hfeas
  · intro ρ ell hitem_eq hupper
    have hopt : OpposingTypes.Problem6PolicyOptimal alpha v ρ ell :=
      ⟨fun j => le_of_eq (hitem_eq j).symm, hupper⟩
    simpa [t0, ρstar, ellstar] using
      OpposingTypes.problem6PolicyOptimal_equalized_eq_firstClosedPolicy
        halpha0 halpha1 hpos hdec hitem_eq hopt
  · dsimp only
    refine ⟨by simpa [t0, ρstar, ellstar, t] using hclosed.1, ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro j hj
      exact OpposingTypes.problem6SparseEqualized_x_before_eq
        halpha0 halpha1 hpos hactive.sparse hj
    · exact OpposingTypes.problem6SparseEqualized_x_pivot_eq
        halpha0 halpha1 hpos hactive.sparse
    · intro j hj
      exact hactive.sparse.x_after_pivot_zero hj
    · intro j hj
      exact hactive.sparse.y_before_pivot_zero hj
    · exact OpposingTypes.problem6SparseEqualized_y_pivot_eq
        halpha0 halpha1 hpos hactive.sparse
    · intro j hj
      exact OpposingTypes.problem6SparseEqualized_y_after_eq
        halpha0 halpha1 hpos hactive.sparse hj

/--
Appendix D, Lemma 6 proof component: mirror inverse-gap algebra.  The source
lemma is an ordering statement about the optimal Problem 6 policy.
-/
theorem appendix_d_lemma6_mirror_inverse_gap
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} (j : Item n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j) :
    (OpposingTypes.pairShare alpha v j)⁻¹ -
        (1 - OpposingTypes.pairShare alpha v (OpposingTypes.reverseItem j))⁻¹ =
      v (OpposingTypes.reverseItem j) / v j * (1 - 2 * alpha) /
        (alpha * (1 - alpha)) :=
  OpposingTypes.paper_lemma6_pairShare_mirror_inverse_gap_eq
    j halpha0 halpha1 hpos

/--
Appendix D, Lemma 6: below one half, the unique Problem 6 optimizer gives
paper type 1 weakly greater normalized utility than paper type 2.

Source status: direct source result.
-/
theorem appendix_d_lemma6_optimal_policy_type_utility_order
    {n : ℕ} [NeZero n] {alpha : ℝ} {v : Item n → ℝ}
    (halpha0 : 0 < alpha) (halpha_half : alpha < 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : OpposingTypes.StrictlyDecreasingByIndex v) :
    TypeWeightedRecommendationModel.normalizedTypeUtility
        (OpposingTypes.twoTypeReducedModel alpha v)
        (OpposingTypes.problem6FirstClosedPolicy alpha v halpha0
          (halpha_half.trans (by norm_num)) hpos) 1 ≤
      TypeWeightedRecommendationModel.normalizedTypeUtility
        (OpposingTypes.twoTypeReducedModel alpha v)
        (OpposingTypes.problem6FirstClosedPolicy alpha v halpha0
          (halpha_half.trans (by norm_num)) hpos) 0 := by
  have halpha1 : alpha < 1 := halpha_half.trans (by norm_num)
  let t : Item n :=
    OpposingTypes.problem6FirstClosedPivot alpha v halpha0 halpha1 hpos
  let hbounds : OpposingTypes.Problem6ClosedPivotDenominatorBounds alpha v t :=
    OpposingTypes.problem6FirstClosedPivot_denominatorBounds
      halpha0 halpha1 hpos
  let hpivot : OpposingTypes.Problem6ClosedNonnegativePivots alpha v t :=
    OpposingTypes.problem6ClosedNonnegativePivots_of_denominatorBounds
      halpha0 halpha1 hpos hbounds
  have htcenter : t.val ≤ (OpposingTypes.reverseItem t).val := by
    rcases OpposingTypes.midpoint_center_or_succ_center (n := n) with
      ⟨c, hcenter⟩ | ⟨c, hsucc⟩
    · exact OpposingTypes.problem6FirstClosedPivot_le_reverse_of_alpha_le_half_center
        halpha0 halpha1 (le_of_lt halpha_half) hpos hcenter
    · exact OpposingTypes.problem6FirstClosedPivot_le_reverse_of_alpha_le_half_succ_center
        halpha0 halpha1 (le_of_lt halpha_half) hpos hsucc
  have hpolicy :
      OpposingTypes.problem6FirstClosedPolicy alpha v halpha0 halpha1 hpos =
        OpposingTypes.problem6ClosedPolicy alpha v t
          halpha0 halpha1 hpos hpivot := by
    dsimp [t, hpivot, hbounds]
    exact OpposingTypes.problem6FirstClosedPolicy_eq_closedPolicy_of_firstClosedPivot_eq
      halpha0 halpha1 hpos rfl
  rw [hpolicy]
  exact
    OpposingTypes.problem6ClosedPolicy_normalizedType_one_le_zero_of_alpha_le_half_auto_best_of_pivot_le_reverse
      halpha0 halpha1 (le_of_lt halpha_half) hpos hdec hpivot htcenter

/--
Appendix D, Lemma 7 proof component: the canonical first closed pivot is
monotone.  The source statement concerns the pivot of its unique optimizer.
-/
theorem appendix_d_lemma7_pivot_monotonicity
    {n : ℕ} [NeZero n] {alpha alpha' : ℝ} {v : Item n → ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha') (hpos : ∀ j : Item n, 0 < v j) :
    ↑(OpposingTypes.problem6FirstClosedPivot alpha v halpha0 halpha1 hpos) ≤
      ↑(OpposingTypes.problem6FirstClosedPivot alpha' v halpha0' halpha1' hpos) :=
  OpposingTypes.paper_lemma7_problem6FirstClosedPivot_mono_alpha
    halpha0 halpha1 halpha0' halpha1' halpha_le hpos

/--
Appendix D, Lemma 7: the active pivot of the unique Problem 6 optimizer is
weakly increasing in `alpha`.

Source status: direct source result.
-/
theorem appendix_d_lemma7_active_optimizer_pivot_monotonicity
    {n : ℕ} [NeZero n] {alpha alpha' : ℝ} {v : Item n → ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : OpposingTypes.StrictlyDecreasingByIndex v) :
    (TypePolicy.lastActiveTypeZero
        (OpposingTypes.problem6FirstClosedPolicy alpha v
          halpha0 halpha1 hpos)).val ≤
      (TypePolicy.lastActiveTypeZero
        (OpposingTypes.problem6FirstClosedPolicy alpha' v
          halpha0' halpha1' hpos)).val := by
  let ρ : TypePolicy 2 n :=
    OpposingTypes.problem6FirstClosedPolicy alpha v halpha0 halpha1 hpos
  let ρ' : TypePolicy 2 n :=
    OpposingTypes.problem6FirstClosedPolicy alpha' v halpha0' halpha1' hpos
  have hstar :=
    OpposingTypes.problem6FirstClosedPolicy_item_eq_and_optimal
      halpha0 halpha1 hpos hdec
  have hstar' :=
    OpposingTypes.problem6FirstClosedPolicy_item_eq_and_optimal
      halpha0' halpha1' hpos hdec
  have hactive :=
    OpposingTypes.problem6PolicyOptimal_equalized_sparseActive
      halpha0 halpha1 hpos hdec hstar.1 hstar.2
  have hactive' :=
    OpposingTypes.problem6PolicyOptimal_equalized_sparseActive
      halpha0' halpha1' hpos hdec hstar'.1 hstar'.2
  rcases lt_or_eq_of_le halpha_le with halpha_lt | halpha_eq
  · exact OpposingTypes.lemma7_sparseActive_pivot_mono_of_alpha_lt
      halpha0 halpha1 halpha0' halpha1' halpha_lt hpos hactive hactive'
  · subst alpha'
    rfl

/--
Appendix D, Lemma 8: optimal item fairness is increasing on the first half of
the alpha interval.  The parity split needed by the finite item index is
discharged internally.

Source status: direct source text.
-/
theorem appendix_d_lemma8_selected_pivot_stitching
    {n : ℕ} [NeZero n] {alpha alpha' : ℝ} {v : Item n → ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (halpha_half : alpha ≤ 1 / 2) (halpha_half' : alpha' ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : OpposingTypes.StrictlyDecreasingByIndex v) :
    (OpposingTypes.twoTypeReducedModel alpha v).optimalItemFairness ≤
      (OpposingTypes.twoTypeReducedModel alpha' v).optimalItemFairness := by
  rcases OpposingTypes.midpoint_center_or_succ_center (n := n) with
    hcenter | hsucc
  · rcases hcenter with ⟨c, hcenter⟩
    exact
      OpposingTypes.paper_lemma8_reducedOptimalItemFairness_mono_firstHalf_center_of_alpha_le
        halpha0 halpha1 halpha0' halpha1' halpha_le halpha_half halpha_half'
        hpos hdec hcenter
  · rcases hsucc with ⟨c, hsucc⟩
    exact
      OpposingTypes.paper_lemma8_reducedOptimalItemFairness_mono_firstHalf_succ_center_of_alpha_le
        halpha0 halpha1 halpha0' halpha1' halpha_le halpha_half halpha_half'
        hpos hdec hsucc


/--
Appendix D, Lemma 9: the `q_j`/pair-share algebra.

Source status: direct paper-facing Appendix D Lemma 9 algebra row.
-/
theorem appendix_d_lemma9_pair_share_algebra
    {n : ℕ} {alpha alpha' : ℝ} {v : Item n → ℝ} {i j : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_lt : alpha < alpha') (hpos : ∀ j : Item n, 0 < v j)
    (hdec : OpposingTypes.StrictlyDecreasingByIndex v)
    (hij : i.val < j.val) :
    OpposingTypes.pairShare alpha v j < OpposingTypes.pairShare alpha' v j ∧
      OpposingTypes.pairShare alpha v j < OpposingTypes.pairShare alpha v i := by
  constructor
  · exact OpposingTypes.paper_lemma9_pairShare_strictly_increases_in_alpha
      j halpha0 halpha1 halpha0' halpha1' halpha_lt hpos
  · exact OpposingTypes.paper_lemma9_pairShare_strictly_decreases_in_index
      halpha0 halpha1 hpos hdec hij

/--
Appendix D, Lemma 10 proof component: midpoint pair-share symmetry.  The
source lemma constrains the pivot of the source optimal policy.
-/
theorem appendix_d_lemma10_midpoint_candidate
    {n : ℕ} {v : Item n → ℝ} (j : Item n)
    (hpos : ∀ j : Item n, 0 < v j) :
    OpposingTypes.pairShare (1 / 2) v j +
        OpposingTypes.pairShare (1 / 2) v (OpposingTypes.reverseItem j) = 1 :=
  OpposingTypes.paper_lemma10_pairShare_half_add_reverse_eq_one j hpos

/--
Appendix D, Lemma 10: for `alpha ≤ 1/2`, the active pivot of the unique
Problem 6 optimizer is at or before the midpoint.

Source status: direct source result.
-/
theorem appendix_d_lemma10_active_optimizer_pivot_at_or_before_midpoint
    {n : ℕ} [NeZero n] {alpha : ℝ} {v : Item n → ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha_half : alpha ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : OpposingTypes.StrictlyDecreasingByIndex v) :
    let t := TypePolicy.lastActiveTypeZero
      (OpposingTypes.problem6FirstClosedPolicy alpha v halpha0 halpha1 hpos)
    t.val ≤ (OpposingTypes.reverseItem t).val := by
  dsimp
  let t0 : Item n :=
    OpposingTypes.problem6FirstClosedPivot alpha v halpha0 halpha1 hpos
  let ρ : TypePolicy 2 n :=
    OpposingTypes.problem6FirstClosedPolicy alpha v halpha0 halpha1 hpos
  let t : Item n := TypePolicy.lastActiveTypeZero ρ
  have hstar :=
    OpposingTypes.problem6FirstClosedPolicy_item_eq_and_optimal
      halpha0 halpha1 hpos hdec
  let cert : OpposingTypes.Problem6ClosedOptimalityCertificate alpha v t0 :=
    OpposingTypes.problem6FirstClosedPivot_optimalityCertificate
      halpha0 halpha1 hpos hdec
  have hsupport :=
    OpposingTypes.problem6PolicyOptimal_equalized_thresholdSupport_of_closedCertificate
      halpha0 halpha1 hpos hdec cert hstar.1 hstar.2
  have ht_le : t.val ≤ t0.val := by
    by_contra hnot
    have ht0t : t0.val < t.val := by omega
    exact TypePolicy.lastActiveTypeZero_active ρ (hsupport.1 ht0t)
  have ht0center : t0.val ≤ (OpposingTypes.reverseItem t0).val := by
    rcases OpposingTypes.midpoint_center_or_succ_center (n := n) with
      ⟨c, hcenter⟩ | ⟨c, hsucc⟩
    · exact OpposingTypes.problem6FirstClosedPivot_le_reverse_of_alpha_le_half_center
        halpha0 halpha1 halpha_half hpos hcenter
    · exact OpposingTypes.problem6FirstClosedPivot_le_reverse_of_alpha_le_half_succ_center
        halpha0 halpha1 halpha_half hpos hsucc
  change t.val ≤ (OpposingTypes.reverseItem t).val
  rw [OpposingTypes.val_le_reverseItem_iff]
  have ht0arith : 2 * t0.val + 1 ≤ n :=
    (OpposingTypes.val_le_reverseItem_iff t0).mp ht0center
  omega

/--
Appendix D, Lemma 11 proof component: a fixed-pivot denominator is monotone.
The source statement is item-fairness monotonicity on the selected-pivot
interval.
-/
theorem appendix_d_lemma11_denominator_monotonicity
    {n : ℕ} {alpha alpha' : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha') (hpos : ∀ j : Item n, 0 < v j)
    (hdec : OpposingTypes.StrictlyDecreasingByIndex v)
    (hpivot : ↑t ≤ ↑(OpposingTypes.reverseItem t)) :
    OpposingTypes.problem6ClosedDenominator alpha' v t ≤
      OpposingTypes.problem6ClosedDenominator alpha v t :=
  OpposingTypes.paper_lemma11_fixedPivotDenominator_antitone
    halpha0 halpha1 halpha0' halpha1' halpha_le hpos hdec hpivot

/--
Appendix D, Lemma 11: optimal item fairness increases on a selected-active-
pivot interval `A(t)` whose pivot is at or before the midpoint.

Source status: direct source result.
-/
theorem appendix_d_lemma11_optimal_item_fairness_mono_on_active_pivot_interval
    {n : ℕ} [NeZero n] {alpha alpha' : ℝ} {v : Item n → ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : OpposingTypes.StrictlyDecreasingByIndex v)
    (hpivot :
      TypePolicy.lastActiveTypeZero
          (OpposingTypes.problem6FirstClosedPolicy alpha v
            halpha0 halpha1 hpos) =
        TypePolicy.lastActiveTypeZero
          (OpposingTypes.problem6FirstClosedPolicy alpha' v
            halpha0' halpha1' hpos))
    (hcenter :
      let t := TypePolicy.lastActiveTypeZero
        (OpposingTypes.problem6FirstClosedPolicy alpha v
          halpha0 halpha1 hpos)
      t.val ≤ (OpposingTypes.reverseItem t).val) :
    (OpposingTypes.twoTypeReducedModel alpha v).optimalItemFairness ≤
      (OpposingTypes.twoTypeReducedModel alpha' v).optimalItemFairness := by
  let ρ : TypePolicy 2 n :=
    OpposingTypes.problem6FirstClosedPolicy alpha v halpha0 halpha1 hpos
  let ρ' : TypePolicy 2 n :=
    OpposingTypes.problem6FirstClosedPolicy alpha' v halpha0' halpha1' hpos
  let ell : ℝ := OpposingTypes.problem6ClosedValue alpha v
    (OpposingTypes.problem6FirstClosedPivot alpha v halpha0 halpha1 hpos)
  let ell' : ℝ := OpposingTypes.problem6ClosedValue alpha' v
    (OpposingTypes.problem6FirstClosedPivot alpha' v halpha0' halpha1' hpos)
  let t : Item n := TypePolicy.lastActiveTypeZero ρ
  have hstar :=
    OpposingTypes.problem6FirstClosedPolicy_item_eq_and_optimal
      halpha0 halpha1 hpos hdec
  have hstar' :=
    OpposingTypes.problem6FirstClosedPolicy_item_eq_and_optimal
      halpha0' halpha1' hpos hdec
  have hactive :=
    OpposingTypes.problem6PolicyOptimal_equalized_sparseActive
      halpha0 halpha1 hpos hdec hstar.1 hstar.2
  have hactive' :
      OpposingTypes.Problem6SparseEqualizedActive alpha' v
        (TypePolicy.lastActiveTypeZero ρ')
        (fun j : Item n => (ρ' 0 j).toReal)
        (fun j : Item n => (ρ' 1 j).toReal) ell' := by
    simpa [ρ', ell'] using
      OpposingTypes.problem6PolicyOptimal_equalized_sparseActive
        halpha0' halpha1' hpos hdec hstar'.1 hstar'.2
  have ht' : TypePolicy.lastActiveTypeZero ρ' = t := by
    simpa [t] using hpivot.symm
  have hactive'_same :
      OpposingTypes.Problem6SparseEqualizedActive alpha' v t
        (fun j : Item n => (ρ' 0 j).toReal)
        (fun j : Item n => (ρ' 1 j).toReal) ell' := by
    simpa [ht'] using hactive'
  have hell : ell = OpposingTypes.problem6ClosedValue alpha v t := by
    simpa [ρ, ell, t] using
      OpposingTypes.problem6SparseEqualized_value_eq_closed
        halpha0 halpha1 hpos hactive.sparse
  have hell' : ell' = OpposingTypes.problem6ClosedValue alpha' v t :=
    OpposingTypes.problem6SparseEqualized_value_eq_closed
      halpha0' halpha1' hpos hactive'_same.sparse
  have hitem :
      (OpposingTypes.twoTypeReducedModel alpha v).optimalItemFairness = ell := by
    calc
      _ = OpposingTypes.problem6LPOptimalValue alpha v :=
        (OpposingTypes.problem6LPOptimalValue_eq_optimalItemFairness
          alpha v halpha0 halpha1 hpos).symm
      _ = ell := by
        simpa [ell] using
          OpposingTypes.problem6LPOptimalValue_eq_of_policyOptimal
            halpha0 halpha1 hpos hstar.2
  have hitem' :
      (OpposingTypes.twoTypeReducedModel alpha' v).optimalItemFairness = ell' := by
    calc
      _ = OpposingTypes.problem6LPOptimalValue alpha' v :=
        (OpposingTypes.problem6LPOptimalValue_eq_optimalItemFairness
          alpha' v halpha0' halpha1' hpos).symm
      _ = ell' := by
        simpa [ell'] using
          OpposingTypes.problem6LPOptimalValue_eq_of_policyOptimal
            halpha0' halpha1' hpos hstar'.2
  rw [hitem, hitem', hell, hell']
  exact OpposingTypes.lemma11_fixedPivotClosedValue_monotone
    halpha0 halpha1 halpha0' halpha1' halpha_le hpos hdec
      (by simpa [ρ, t] using hcenter)

/-- Appendix E, Lemma 12: symmetrized estimated policy optimality. -/
theorem appendix_e_lemma12_symmetrized_policy
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hpos : ∀ j : Item n, 0 < v j) {ρ : TypePolicy 3 n}
    (hOptimal : (OpposingTypes.theorem4EstimatedReducedModel beta v).IsOptimalAtLevel 1 ρ) :
    (OpposingTypes.theorem4EstimatedReducedModel beta v).IsOptimalAtLevel 1
        (OpposingTypes.theorem4SymmetrizedPolicy ρ) ∧
      OpposingTypes.Theorem4MirrorSymmetricPolicy
        (OpposingTypes.theorem4SymmetrizedPolicy ρ) :=
  OpposingTypes.paper_lemma12_theorem4_symmetrizedPolicy_isOptimalAtLevel
    hpos hOptimal

/-- Coordinates of the mirror-restricted Problem 11 LP: `x`, `z`, and `lambda`. -/
abbrev Problem11Point (n : ℕ) :=
  ((Item n → ℝ) × (Item n → ℝ)) × ℝ

/--
The literal equality-feasible region of Problem 11 after the paper identifies
the mirror-restricted policy space `S'` with the two probability vectors
`x,z`.  The first two coordinates are the vectors and the final coordinate is
`lambda`.
-/
def problem11EqualityFeasibleSet {n : ℕ}
    (beta : ℝ) (v : Item n → ℝ) : Set (Problem11Point n) :=
  {p |
    (∀ j : Item n, 0 ≤ p.1.1 j) ∧
      (∀ j : Item n, 0 ≤ p.1.2 j) ∧
        (∑ j : Item n, p.1.1 j) = 1 ∧
          (∑ j : Item n, p.1.2 j) = 1 ∧
            (∀ j : Item n,
              p.1.2 (OpposingTypes.reverseItem j) = p.1.2 j) ∧
              ∀ j : Item n,
                OpposingTypes.theorem4Problem11ItemValue beta v p.1.1 p.1.2 j = p.2}

/-- The source Problem 11 coordinates represented by a mirror-symmetric policy. -/
def problem11PointOfPolicy {n : ℕ}
    (ρ : TypePolicy 3 n) (ell : ℝ) : Problem11Point n :=
  (((fun j : Item n => (ρ 0 j).toReal),
      (fun j : Item n => (ρ 2 j).toReal)), ell)

/--
The source's “basic feasible solution” condition for Problem 11.  For a
finite linear program, basic feasible points are exactly extreme points of
the equality-feasible polytope.  This definition therefore records the
actual mirror-restricted `x,z,lambda` LP, rather than a derived support count
or an active basis for a different three-row formulation.
-/
def problem11BasicFeasible {n : ℕ}
    (beta : ℝ) (v : Item n → ℝ) (ρ : TypePolicy 3 n) (ell : ℝ) : Prop :=
  problem11PointOfPolicy ρ ell ∈
    (problem11EqualityFeasibleSet beta v).extremePoints ℝ

/--
Appendix E, Lemma 13: every literal equality-LP optimal basic feasible
solution of Problem 11 has the complete pivot support asserted in the paper,
at a pivot no later than the midpoint, and that pivot is minimum among indices
with the full support shape.  `problem11BasicFeasible` is the actual
mirror-restricted equality-LP condition, not a support-count proxy.

The equality-program optimum is converted internally to epigraph optimality
by a closed primal-dual comparison witness; no epigraph-optimality premise is
inserted into the paper-facing statement.  The proof establishes the stated
support conclusion for every equality-program optimum, so the source's
basic-feasibility restriction is retained for literal correspondence rather
than used as a support-count shortcut.
-/
theorem appendix_e_lemma13_every_optimal_basic_solution_has_pivot_support
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    {ρ : TypePolicy 3 n} {ell : ℝ}
    (hn : 2 < n)
    (hbeta : (n : ℝ)⁻¹ < beta)
    (hbeta_half : beta < 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : OpposingTypes.StrictlyDecreasingByIndex v)
    (hmirror : OpposingTypes.Theorem4MirrorSymmetricPolicy ρ)
    (hitem_eq : ∀ j : Item n,
      OpposingTypes.theorem4Problem11PolicyItemValue beta v ρ j = ell)
    (hoptimal : ∀ (ρ' : TypePolicy 3 n) (ell' : ℝ),
      OpposingTypes.Theorem4MirrorSymmetricPolicy ρ' →
      (∀ j : Item n,
        OpposingTypes.theorem4Problem11PolicyItemValue beta v ρ' j = ell') →
      ell' ≤ ell)
    (hbasic : problem11BasicFeasible beta v ρ ell) :
    let t := OpposingTypes.theorem4Problem11LastActiveTypeZero ρ
    t.val ≤ (OpposingTypes.reverseItem t).val ∧
      (∀ j : Item n, t.val < j.val → ρ 0 j = 0) ∧
      (∀ j : Item n, j.val < t.val →
        ρ 2 j = 0 ∧ ρ 2 (OpposingTypes.reverseItem j) = 0) ∧
      ∀ s : Item n,
        (∀ j : Item n, s.val < j.val → ρ 0 j = 0) →
        (∀ j : Item n, j.val < s.val →
          ρ 2 j = 0 ∧ ρ 2 (OpposingTypes.reverseItem j) = 0) →
        t.val ≤ s.val := by
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hbeta0 : 0 < beta := lt_trans (inv_pos.mpr hnpos) hbeta
  let hEquality : OpposingTypes.Theorem4Problem11EqualityLPOptimal beta v ρ ell :=
    ⟨hmirror, hitem_eq, hoptimal⟩
  have hopt : OpposingTypes.Theorem4Problem11PolicyOptimal beta v ρ ell :=
    OpposingTypes.theorem4Problem11PolicyOptimal_of_equalityLPOptimal
      hbeta0 hbeta_half hpos hdec hEquality
  let t : Item n := OpposingTypes.theorem4Problem11LastActiveTypeZero ρ
  have hresult :
      t.val ≤ (OpposingTypes.reverseItem t).val ∧
        OpposingTypes.Theorem4Problem11PivotSupport ρ t ∧
        ∀ s : Item n,
          (∀ j : Item n, s.val < j.val → ρ 0 j = 0) → t.val ≤ s.val := by
    exact OpposingTypes.theorem4Problem11PolicyOptimal_lastActive_pivotSupport
      hn hbeta0 hbeta_half hpos hdec hitem_eq hopt
  rcases hresult with ⟨hleft, hpivot, hminimum⟩
  refine ⟨hleft, hpivot.1, hpivot.2, ?_⟩
  intro s hs _hsCold
  exact hminimum s hs

/--
Appendix E, Lemma 14: Problem 11 has a unique global optimizer.  Existence is
constructed from the closed primal/dual crossing, and uniqueness ranges over
all mirror-symmetric epigraph optima, not only basic feasible solutions.

Source status: direct source result.
-/
theorem appendix_e_lemma14_problem11_has_unique_optimal_solution
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hn : 2 < n)
    (hbeta : (n : ℝ)⁻¹ < beta)
    (hbeta_half : beta < 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : OpposingTypes.StrictlyDecreasingByIndex v) :
    ∃ (ρstar : TypePolicy 3 n) (ellstar : ℝ),
      OpposingTypes.Theorem4MirrorSymmetricPolicy ρstar ∧
      (∀ j : Item n,
        OpposingTypes.theorem4Problem11PolicyItemValue beta v ρstar j =
          ellstar) ∧
      (∀ (ρ : TypePolicy 3 n) (ell : ℝ),
        OpposingTypes.Theorem4MirrorSymmetricPolicy ρ →
        OpposingTypes.theorem4Problem11LPFeasible beta v ρ ell →
        ell ≤ ellstar) ∧
      ∀ (ρ : TypePolicy 3 n) (ell : ℝ),
        OpposingTypes.Theorem4MirrorSymmetricPolicy ρ →
        OpposingTypes.theorem4Problem11LPFeasible beta v ρ ell →
        (∀ (ρ' : TypePolicy 3 n) (ell' : ℝ),
          OpposingTypes.Theorem4MirrorSymmetricPolicy ρ' →
          OpposingTypes.theorem4Problem11LPFeasible beta v ρ' ell' →
          ell' ≤ ell) →
        ρ = ρstar ∧ ell = ellstar := by
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hbeta0 : 0 < beta := lt_trans (inv_pos.mpr hnpos) hbeta
  have hbuild :
      ∀ (t : Item n),
        t.val ≤ (OpposingTypes.reverseItem t).val →
        OpposingTypes.Theorem4Problem11ClosedPivotBounds beta v t →
        ∃ ρstar : TypePolicy 3 n,
          OpposingTypes.Theorem4Problem11PolicyOptimal beta v ρstar
              (OpposingTypes.theorem4Problem11ClosedDualValue beta v t) ∧
            ∀ j : Item n,
              OpposingTypes.theorem4Problem11PolicyItemValue beta v ρstar j =
                OpposingTypes.theorem4Problem11ClosedDualValue beta v t := by
    intro t hleft hbounds
    let hBFS : OpposingTypes.Theorem4Problem11EqualityFormOptimalBFS beta v
        (OpposingTypes.theorem4Problem11ClosedX beta v t)
        (OpposingTypes.theorem4Problem11ClosedZ beta v t)
        (OpposingTypes.theorem4Problem11ClosedDualValue beta v t) :=
      OpposingTypes.theorem4Problem11EqualityFormOptimalBFS_of_closed_bounds
        hbeta0 hbeta_half hpos hdec hleft hbounds
    let ρstar : TypePolicy 3 n :=
      OpposingTypes.theorem4Problem11PolicyOfRealVectors
        (OpposingTypes.theorem4Problem11ClosedX beta v t)
        (OpposingTypes.theorem4Problem11ClosedZ beta v t)
        hBFS.feasible.x_nonneg hBFS.feasible.z_nonneg
        hBFS.feasible.sum_x hBFS.feasible.sum_z
    have hopt : OpposingTypes.Theorem4Problem11PolicyOptimal beta v ρstar
        (OpposingTypes.theorem4Problem11ClosedDualValue beta v t) := by
      simpa [ρstar] using
        OpposingTypes.theorem4Problem11PolicyOptimal_of_equalityFormOptimalBFS
          hBFS
    have hequalized :=
      OpposingTypes.theorem4Problem11EqualizedBasicOptimal_of_equalityFormOptimalBFS
        hBFS
    exact ⟨ρstar, hopt, by simpa [ρstar] using hequalized.item_eq⟩
  have hclosed :
      ∃ (t : Item n) (ρstar : TypePolicy 3 n),
        t.val ≤ (OpposingTypes.reverseItem t).val ∧
          OpposingTypes.Theorem4Problem11PolicyOptimal beta v ρstar
              (OpposingTypes.theorem4Problem11ClosedDualValue beta v t) ∧
            ∀ j : Item n,
              OpposingTypes.theorem4Problem11PolicyItemValue beta v ρstar j =
                OpposingTypes.theorem4Problem11ClosedDualValue beta v t := by
    rcases OpposingTypes.midpoint_center_or_succ_center (n := n) with
      ⟨c, hcenter⟩ | ⟨c, hsucc⟩
    · rcases OpposingTypes.theorem4Problem11ClosedPivotBounds_exists_of_center
        hbeta0 hbeta_half hpos hcenter with ⟨t, hleft, hbounds⟩
      rcases hbuild t hleft hbounds with ⟨ρstar, hopt, hitem⟩
      exact ⟨t, ρstar, hleft, hopt, hitem⟩
    · rcases OpposingTypes.theorem4Problem11ClosedPivotBounds_exists_of_succ_center
        hbeta0 hbeta_half hpos hsucc with ⟨t, hleft, hbounds⟩
      rcases hbuild t hleft hbounds with ⟨ρstar, hopt, hitem⟩
      exact ⟨t, ρstar, hleft, hopt, hitem⟩
  rcases hclosed with ⟨t, ρstar, hleft, hstar, hstar_item⟩
  let ellstar := OpposingTypes.theorem4Problem11ClosedDualValue beta v t
  refine ⟨ρstar, ellstar, hstar.1, hstar_item, hstar.2.2, ?_⟩
  intro ρ ell hmirror hfeasible hoptimal
  have hopt : OpposingTypes.Theorem4Problem11PolicyOptimal beta v ρ ell :=
    ⟨hmirror, hfeasible, hoptimal⟩
  have hpolicy : ρ = ρstar :=
    OpposingTypes.theorem4Problem11PolicyOptimal_pairwise_unique_of_closed_policyOptimal
      hn hbeta0 hbeta_half hpos hdec hleft hstar
        ρ ρstar ell ellstar hopt hstar
  have hvalue : ell = ellstar :=
    OpposingTypes.theorem4Problem11PolicyOptimal_value_unique hopt hstar
  exact ⟨hpolicy, hvalue⟩


/--
Appendix E, Lemma 15: full closed form for an arbitrary global Problem 11
optimizer, at its active pivot.  The final disjunction separates the
non-center formula printed in the paper from the verified center formula for
Problem 11's full mirrored-policy item equation.

The paper's displayed center value drops the mirrored known-type contribution
at the self-mirror item.  Under the Problem 11 equation stated earlier in the
paper, the corrected center value is `1 / (1 + L_t)`, as exposed here.

Source status: repaired source result; the non-center display is direct and the
center display is corrected to agree with Problem 11.
-/
theorem appendix_e_lemma15_optimal_solution_full_closed_form
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    {ρ : TypePolicy 3 n} {ell : ℝ}
    (hn : 2 < n)
    (hbeta : (n : ℝ)⁻¹ < beta)
    (hbeta_half : beta < 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : OpposingTypes.StrictlyDecreasingByIndex v)
    (hmirror : OpposingTypes.Theorem4MirrorSymmetricPolicy ρ)
    (hitem_eq : ∀ j : Item n,
      OpposingTypes.theorem4Problem11PolicyItemValue beta v ρ j = ell)
    (hoptimal : ∀ (ρ' : TypePolicy 3 n) (ell' : ℝ),
      OpposingTypes.Theorem4MirrorSymmetricPolicy ρ' →
      OpposingTypes.theorem4Problem11LPFeasible beta v ρ' ell' →
      ell' ≤ ell) :
    let t := OpposingTypes.theorem4Problem11LastActiveTypeZero ρ
    t.val ≤ (OpposingTypes.reverseItem t).val ∧
      (∀ j : Item n, j.val < t.val →
        (ρ 0 j).toReal =
          ell / (2 * beta * OpposingTypes.pairShare (1 / 2) v j)) ∧
      (ρ 0 t).toReal =
        1 - (ell / (2 * beta)) *
          OpposingTypes.paper_lemma15_problem11_leftSum v t ∧
      (∀ j : Item n, t.val < j.val → (ρ 0 j).toReal = 0) ∧
      (∀ j : Item n, j.val < t.val →
        (ρ 2 j).toReal = 0 ∧
          (ρ 2 (OpposingTypes.reverseItem j)).toReal = 0) ∧
      (∀ j : Item n,
        t.val < j.val →
        j.val < (OpposingTypes.reverseItem t).val →
        (ρ 2 j).toReal = ell / (1 - 2 * beta)) ∧
      ((t.val < (OpposingTypes.reverseItem t).val ∧
          ell =
            (2 * beta * OpposingTypes.pairShare (1 / 2) v t +
                (1 / 2) * (1 - 2 * beta)) /
              (1 + OpposingTypes.pairShare (1 / 2) v t *
                  OpposingTypes.paper_lemma15_problem11_leftSum v t +
                (1 / 2) * ((n : ℝ) - 2 * ((t.val : ℝ) + 1))) ∧
          (ρ 2 t).toReal =
            (1 / 2) *
              (1 - (((n : ℝ) - 2 * ((t.val : ℝ) + 1)) * ell /
                (1 - 2 * beta))) ∧
          (ρ 2 (OpposingTypes.reverseItem t)).toReal =
            (1 / 2) *
              (1 - (((n : ℝ) - 2 * ((t.val : ℝ) + 1)) * ell /
                (1 - 2 * beta)))) ∨
        (t.val = (OpposingTypes.reverseItem t).val ∧
          (ρ 2 t).toReal = 1 ∧
          ell = 1 /
            (1 + OpposingTypes.paper_lemma15_problem11_leftSum v t))) := by
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hbeta0 : 0 < beta := lt_trans (inv_pos.mpr hnpos) hbeta
  have hclosed :
      ∃ (t0 : Item n) (ρclosed : TypePolicy 3 n),
        t0.val ≤ (OpposingTypes.reverseItem t0).val ∧
          OpposingTypes.Theorem4Problem11PolicyOptimal beta v ρclosed
            (OpposingTypes.theorem4Problem11ClosedDualValue beta v t0) := by
    rcases OpposingTypes.midpoint_center_or_succ_center (n := n) with
      ⟨c, hcenter⟩ | ⟨c, hsucc⟩
    · rcases OpposingTypes.theorem4Problem11ClosedPivotBounds_exists_of_center
        hbeta0 hbeta_half hpos hcenter with ⟨t0, hleft, hbounds⟩
      let hBFS : OpposingTypes.Theorem4Problem11EqualityFormOptimalBFS beta v
          (OpposingTypes.theorem4Problem11ClosedX beta v t0)
          (OpposingTypes.theorem4Problem11ClosedZ beta v t0)
          (OpposingTypes.theorem4Problem11ClosedDualValue beta v t0) :=
        OpposingTypes.theorem4Problem11EqualityFormOptimalBFS_of_closed_bounds
          hbeta0 hbeta_half hpos hdec hleft hbounds
      let ρclosed : TypePolicy 3 n :=
        OpposingTypes.theorem4Problem11PolicyOfRealVectors
          (OpposingTypes.theorem4Problem11ClosedX beta v t0)
          (OpposingTypes.theorem4Problem11ClosedZ beta v t0)
          hBFS.feasible.x_nonneg hBFS.feasible.z_nonneg
          hBFS.feasible.sum_x hBFS.feasible.sum_z
      refine ⟨t0, ρclosed, hleft, ?_⟩
      simpa [ρclosed] using
        OpposingTypes.theorem4Problem11PolicyOptimal_of_equalityFormOptimalBFS
          hBFS
    · rcases OpposingTypes.theorem4Problem11ClosedPivotBounds_exists_of_succ_center
        hbeta0 hbeta_half hpos hsucc with ⟨t0, hleft, hbounds⟩
      let hBFS : OpposingTypes.Theorem4Problem11EqualityFormOptimalBFS beta v
          (OpposingTypes.theorem4Problem11ClosedX beta v t0)
          (OpposingTypes.theorem4Problem11ClosedZ beta v t0)
          (OpposingTypes.theorem4Problem11ClosedDualValue beta v t0) :=
        OpposingTypes.theorem4Problem11EqualityFormOptimalBFS_of_closed_bounds
          hbeta0 hbeta_half hpos hdec hleft hbounds
      let ρclosed : TypePolicy 3 n :=
        OpposingTypes.theorem4Problem11PolicyOfRealVectors
          (OpposingTypes.theorem4Problem11ClosedX beta v t0)
          (OpposingTypes.theorem4Problem11ClosedZ beta v t0)
          hBFS.feasible.x_nonneg hBFS.feasible.z_nonneg
          hBFS.feasible.sum_x hBFS.feasible.sum_z
      refine ⟨t0, ρclosed, hleft, ?_⟩
      simpa [ρclosed] using
        OpposingTypes.theorem4Problem11PolicyOptimal_of_equalityFormOptimalBFS
          hBFS
  rcases hclosed with ⟨t0, ρclosed, hleft0, hclosed_opt⟩
  have hopt : OpposingTypes.Theorem4Problem11PolicyOptimal beta v ρ ell :=
    ⟨hmirror, (fun j => le_of_eq (hitem_eq j).symm), hoptimal⟩
  have hvalue :
      ell = OpposingTypes.theorem4Problem11ClosedDualValue beta v t0 :=
    OpposingTypes.theorem4Problem11PolicyOptimal_value_unique hopt hclosed_opt
  let hOptimal :
      OpposingTypes.Theorem4Problem11EqualizedBasicOptimal beta v ρ ell :=
    OpposingTypes.theorem4Problem11PolicyOptimal_equalizedBasicOptimal_of_closedDual_tight
      hbeta0 hbeta_half hpos hdec hleft0 hvalue hopt
  let t : Item n := OpposingTypes.theorem4Problem11LastActiveTypeZero ρ
  have hleft : t.val ≤ (OpposingTypes.reverseItem t).val := by
    exact
      OpposingTypes.theorem4Problem11LastActiveTypeZero_le_reverse_of_equalizedBasicOptimal
        hn hbeta0 hpos hdec hOptimal
  have hpivot : OpposingTypes.Theorem4Problem11PivotSupport ρ t := by
    exact OpposingTypes.theorem4Problem11PivotSupport_of_equalizedBasicOptimal
      hn hbeta0 hbeta_half hpos hdec hOptimal
  refine ⟨hleft, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    exact OpposingTypes.theorem4Problem11Lemma15_typeZero_before_eq
      hbeta0 hpos hOptimal hpivot hleft hj
  · exact
      OpposingTypes.theorem4Problem11Lemma15_typeZero_pivot_eq_one_sub_leftSum
        hbeta0 hpos hOptimal hpivot hleft
  · intro j hj
    exact OpposingTypes.theorem4Problem11Lemma15_typeZero_after_eq_zero
      hpivot hj
  · intro j hj
    exact
      ⟨OpposingTypes.theorem4Problem11Lemma15_cold_before_eq_zero hpivot hj,
        OpposingTypes.theorem4Problem11Lemma15_cold_reverse_before_eq_zero
          hpivot hj⟩
  · intro j hj_left hj_right
    exact OpposingTypes.theorem4Problem11Lemma15_cold_between_pivot_and_mirror_eq
      hbeta_half hOptimal hpivot hj_left hj_right
  · by_cases hcenter : t.val = (OpposingTypes.reverseItem t).val
    · right
      exact
        ⟨hcenter,
          OpposingTypes.theorem4Problem11Lemma15_cold_center_eq_one
            hpivot hcenter.symm,
          OpposingTypes.theorem4Problem11Lemma15_lambda_eq_of_center_fullPolicy
            hbeta0 hpos hOptimal hpivot hcenter⟩
    · have hstrict : t.val < (OpposingTypes.reverseItem t).val :=
        lt_of_le_of_ne hleft hcenter
      left
      exact
        ⟨hstrict,
          OpposingTypes.theorem4Problem11Lemma15_lambda_eq_of_pivot_lt_mirror
            hbeta0 hpos hOptimal hpivot hstrict,
          OpposingTypes.theorem4Problem11Lemma15_cold_pivot_eq_of_pivot_lt_mirror
            hbeta0 hbeta_half hpos hOptimal hpivot hstrict,
          OpposingTypes.theorem4Problem11Lemma15_cold_mirror_pivot_eq_of_pivot_lt_mirror
            hbeta0 hbeta_half hpos hOptimal hpivot hstrict⟩

/--
Appendix E, Lemma 15 source-defect witness.  For `n = 3`, `beta = 2/5`,
center share `q_t = 1/2`, and `L_t = 4/3` (realized, for example, by values
`3, 2, 1`), the value forced by the full Problem 11 equation differs from the
paper's printed center formula.

Source status: checked counterexample to the printed center display.
-/
theorem appendix_e_lemma15_printed_center_value_counterexample :
    (3 : ℝ)⁻¹ < 2 / 5 ∧
      (2 / 5 : ℝ) < 1 / 2 ∧
      (1 / (1 + 4 / 3) : ℝ) ≠
        (2 * (2 / 5 : ℝ) * (1 / 2) + (1 - 2 * (2 / 5 : ℝ))) /
          (1 + (1 / 2 : ℝ) * (4 / 3)) := by
  norm_num

/--
Appendix E, Lemma 16: the midpoint share is above, below, or equal to one half
according as the item lies before, after, or at its reversed index.

Source status: direct source text.
-/
theorem appendix_e_lemma16_midpoint_order_algebra
    {n : ℕ} {v : Item n → ℝ} (j : Item n)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : OpposingTypes.StrictlyDecreasingByIndex v) :
    (j.val < (OpposingTypes.reverseItem j).val →
      (1 / 2 : ℝ) < OpposingTypes.pairShare (1 / 2) v j) ∧
      ((OpposingTypes.reverseItem j).val < j.val →
        OpposingTypes.pairShare (1 / 2) v j < (1 / 2 : ℝ)) ∧
      (j.val = (OpposingTypes.reverseItem j).val →
        OpposingTypes.pairShare (1 / 2) v j = (1 / 2 : ℝ)) := by
  constructor
  · intro hbefore
    exact OpposingTypes.paper_lemma16_half_lt_pairShare_half_of_val_lt_reverse
      j hpos hdec hbefore
  constructor
  · intro hafter
    exact OpposingTypes.paper_lemma16_pairShare_half_lt_half_of_reverse_val_lt
      j hpos hdec hafter
  · intro hcenter
    exact OpposingTypes.paper_lemma16_pairShare_half_eq_half_of_val_eq_reverse
      j hpos hcenter

/--
Appendix E, Lemma 17: every equality-form global optimum of Problem 11 puts no
known-type mass strictly to the right of the midpoint.  Basic feasibility is
not assumed, matching the source's statement for an arbitrary optimum.

Source status: direct source result.
-/
theorem appendix_e_lemma17_every_optimal_solution_has_no_right_half_support
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    {ρ : TypePolicy 3 n} {ell : ℝ}
    (hn : 2 < n)
    (hbeta : (n : ℝ)⁻¹ < beta)
    (hbeta_half : beta < 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : OpposingTypes.StrictlyDecreasingByIndex v)
    (hmirror : OpposingTypes.Theorem4MirrorSymmetricPolicy ρ)
    (hitem_eq : ∀ j : Item n,
      OpposingTypes.theorem4Problem11PolicyItemValue beta v ρ j = ell)
    (hoptimal : ∀ (ρ' : TypePolicy 3 n) (ell' : ℝ),
      OpposingTypes.Theorem4MirrorSymmetricPolicy ρ' →
      OpposingTypes.theorem4Problem11LPFeasible beta v ρ' ell' →
      ell' ≤ ell) :
    ∀ j : Item n, (OpposingTypes.reverseItem j).val < j.val → ρ 0 j = 0 := by
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hbeta0 : 0 < beta := lt_trans (inv_pos.mpr hnpos) hbeta
  have hopt : OpposingTypes.Theorem4Problem11PolicyOptimal beta v ρ ell :=
    ⟨hmirror, (fun j => le_of_eq (hitem_eq j).symm), hoptimal⟩
  have hno :
      OpposingTypes.Theorem4Problem11PolicyNoStrictPointwiseImprovement
        beta v ρ :=
    OpposingTypes.theorem4Problem11_noStrictPointwiseImprovement_of_policyOptimal_equalized
      hitem_eq hopt
  exact
    OpposingTypes.theorem4Problem11_typeZero_zero_after_mirror_of_noStrictPointwiseImprovement
      hn hbeta0 hpos hdec hmirror hno

/--
Proposition 1: under source conditions (i)--(iii), the equality-form linear
program `L` has the Problem-(2) policy as its unique policy optimizer.

Source status: direct. NeurIPS 2024 conference PDF, Proposition 1 p. 4 and
Appendix C proof pp. 24--25.

The identifier is retained for dashboard compatibility; unlike the previous
wrapper, this statement quantifies over the source set `S` and concludes LP
optimality and uniqueness rather than only type-policy representability.
-/
theorem proposition1_symmetric_lp_reduction
    {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n)
    (hPos : assumption_positive_recommendation_utilities W)
    (S : Set (Policy m n))
    (D : RecommendationModel.FiniteLinearPolicySetDescription S)
    (ρstar : Policy m n)
    (hProblemTwo : RecommendationModel.IsOptimalAtLevel W 1 ρstar)
    (hStarMem : ρstar ∈ S)
    (hUniqueFeasible :
      ∀ ρ : Policy m n,
        ρ ∈ S →
          RecommendationModel.itemFairness W ρ =
            RecommendationModel.optimalItemFairness W →
          ρ = ρstar) :
    (RecommendationModel.PropositionOneLPFeasible W D ρstar
          (RecommendationModel.optimalItemFairness W) ∧
        ∀ ρ' : Policy m n, ∀ ell' : ℝ,
          RecommendationModel.PropositionOneLPFeasible W D ρ' ell' →
            ell' ≤ RecommendationModel.optimalItemFairness W) ∧
      ∀ ρ : Policy m n, ∀ ell : ℝ,
        (RecommendationModel.PropositionOneLPFeasible W D ρ ell ∧
          ∀ ρ' : Policy m n, ∀ ell' : ℝ,
            RecommendationModel.PropositionOneLPFeasible W D ρ' ell' →
              ell' ≤ ell) →
          ρ = ρstar ∧ ell = RecommendationModel.optimalItemFairness W := by
  exact RecommendationModel.propositionOne_unique_policy_optimizer_of_source_conditions
    W hPos S D ρstar hProblemTwo hStarMem hUniqueFeasible

/--
Problem (5) / Proposition 2 LP presentation: the source-shaped
user-coordinate equality LP on `S_symm` is the same Proposition 1 equality LP
obtained by instantiating condition (i) with the finite coordinate-linear
description of `S_symm`.

Source: NeurIPS 2024 conference PDF, Proposition 1 proof pp. 24--25 and
Proposition 2 proof pp. 25--26. This freezes the source LP presentation only;
it does not itself prove the active-basis transport from this user-coordinate
LP to the reduced type-coordinate LP. The separate source-facing Proposition 2
row immediately below proves that bridge.
-/
theorem proposition2_user_symmetric_lp_eq_source_problem5
    {m n K : ℕ}
    (S : RecommendationModel.SymmetricData m n K)
    (ρ : Policy m n) (ell : ℝ) :
    (RecommendationModel.UserSymmetricEqualityLP.ofSymmetricData S).Feasible ρ ell ↔
      RecommendationModel.PropositionOneLPFeasible S.model
        (UserTypeAssignment.symmetricPoliciesFiniteLinearDescription
          (n := n) S.types) ρ ell := by
  exact RecommendationModel.userSymmetricEqualityLP_eq_source_problem5 S ρ ell

/--
Proposition 2, source-facing form. The source defines `S_symm` by equality of
users' utility rows, rather than by an arbitrary declared label. The visible
`hRowsDetermineTypes` premise supplies that direction; `SymmetricData` already
supplies the converse direction for equal declared labels. Consequently the
displayed finite equality family describes the literal source policy set.

Source: NeurIPS 2024 conference PDF, Proposition 2 p. 4 and Appendix C proof
pp. 25--26.
-/
theorem proposition2_symmetric_optimum_exists
    {m n K : ℕ} [NeZero m] [NeZero n] [NeZero K]
    (S : RecommendationModel.SymmetricData m n K)
    (hTypes : Function.Surjective S.types.toType)
    (hPos : assumption_positive_recommendation_utilities S.model)
    (hRowsDetermineTypes :
      assumption_proposition2_utility_rows_determine_types S)
    (ρsrc : Policy m n) (ell : ℝ)
    (hsource : RecommendationModel.UserSymmetricEqualityLP.ActiveBasis
      (RecommendationModel.UserSymmetricEqualityLP.ofSymmetricData S) ρsrc ell) :
    (∀ ρ : Policy m n,
      RecommendationModel.UtilityRowSymmetric S.model ρ ↔
        ∀ c : UserTypeAssignment.TypeSymmetryLinearConstraintIndex m n,
          RecommendationModel.policyLinearConstraintHolds
            (UserTypeAssignment.typeSymmetryLinearCoefficient S.types c) 0
            RecommendationModel.PolicyLinearComparison.eq ρ) ∧
      (∃ ρsym : Policy m n,
        RecommendationModel.UtilityRowSymmetric S.model ρsym ∧
          RecommendationModel.IsOptimalAtLevel S.model 1 ρsym) ∧
      TypePolicy.ActivePairsBound
        (UserTypeAssignment.descendTypePolicy S.types
          (AppliedModelingLib.Policy.FiberRepresentatives.ofSurjective hTypes) ρsrc) ∧
      (
        ell = TypeWeightedRecommendationModel.optimalItemFairness
            (S.canonicalReductionOfSurjective hTypes).reduced →
          TypePolicy.SharedItemsBound
            (UserTypeAssignment.descendTypePolicy S.types
              (AppliedModelingLib.Policy.FiberRepresentatives.ofSurjective hTypes) ρsrc)) := by
  let reps : UserTypeAssignment.TypeRepresentatives S.types :=
    AppliedModelingLib.Policy.FiberRepresentatives.ofSurjective hTypes
  let R : ReductionWitness m n K := S.canonicalReductionOfSurjective hTypes
  let ρ : TypePolicy K n :=
    UserTypeAssignment.descendTypePolicy S.types reps ρsrc
  have hbfs :
      R.reduced.IsEqualityLPBasicFeasible ρ ell := by
    exact ReductionWitness.sourceActiveBasis_reducedBasicFeasible_descend
      (R := R) (reps := reps) hPos hsource
  obtain ⟨D, hsym, hactive, hshared⟩ :=
    paper_proposition2_reduced_lp_conclusions S reps hPos
  have hlinear : ∀ ρ : Policy m n,
      ρ ∈ UserTypeAssignment.SymmetricPolicies (n := n) S.types ↔
        ∀ c : UserTypeAssignment.TypeSymmetryLinearConstraintIndex m n,
          RecommendationModel.policyLinearConstraintHolds
            (UserTypeAssignment.typeSymmetryLinearCoefficient S.types c) 0
            RecommendationModel.PolicyLinearComparison.eq ρ := by
    intro ρ
    simpa [UserTypeAssignment.symmetricPoliciesFiniteLinearDescription] using
      (UserTypeAssignment.symmetricPoliciesFiniteLinearDescription
        (n := n) S.types).mem_iff ρ
  refine ⟨?_, ?_,
    by simpa [ρ, reps, R] using hactive ρ ell hbfs,
    by
      intro hLPOptimal
      simpa [ρ, reps, R] using hshared ρ ell hbfs hLPOptimal⟩
  · intro ρ
    calc
      RecommendationModel.UtilityRowSymmetric S.model ρ ↔
          ρ ∈ UserTypeAssignment.SymmetricPolicies (n := n) S.types := by
            simpa [UserTypeAssignment.SymmetricPolicies,
              UserTypeAssignment.IsTypeSymmetric] using
              (UserTypeAssignment.utilityRowSymmetric_iff_isTypeSymmetric
                S hRowsDetermineTypes ρ)
      _ ↔ ∀ c : UserTypeAssignment.TypeSymmetryLinearConstraintIndex m n,
          RecommendationModel.policyLinearConstraintHolds
            (UserTypeAssignment.typeSymmetryLinearCoefficient S.types c) 0
            RecommendationModel.PolicyLinearComparison.eq ρ := hlinear ρ
  · rcases hsym with ⟨ρsym, hsym, hopt⟩
    refine ⟨ρsym, ?_, hopt⟩
    exact (UserTypeAssignment.utilityRowSymmetric_iff_isTypeSymmetric
      S hRowsDetermineTypes ρsym).mpr hsym

/--
Theorem 3, first half: in the opposing two-type model, increasing `alpha`
toward `1 / 2` weakly decreases the price of fairness.

The two surjectivity premises say that both declared opposing types occur in
the corresponding populations; representative users are chosen internally.
-/
theorem theorem3_price_decreases_first_half
    {m n : ℕ} [NeZero m] [NeZero n]
    (S S' : RecommendationModel.SymmetricData m n 2)
    (hTypes : Function.Surjective S.types.toType)
    (hTypes' : Function.Surjective S'.types.toType)
    {alpha alpha' : ℝ} {v : Item n → ℝ}
    (hred : (S.canonicalReductionOfSurjective hTypes).reduced =
      OpposingTypes.twoTypeReducedModel alpha v)
    (hred' : (S'.canonicalReductionOfSurjective hTypes').reduced =
      OpposingTypes.twoTypeReducedModel alpha' v)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (halpha_half : alpha ≤ 1 / 2)
    (halpha_half' : alpha' ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : OpposingTypes.StrictlyDecreasingByIndex v) :
    RecommendationModel.priceOfFairness S'.model ≤
      RecommendationModel.priceOfFairness S.model := by
  let reps : UserTypeAssignment.TypeRepresentatives S.types :=
    AppliedModelingLib.Policy.FiberRepresentatives.ofSurjective hTypes
  let reps' : UserTypeAssignment.TypeRepresentatives S'.types :=
    AppliedModelingLib.Policy.FiberRepresentatives.ofSurjective hTypes'
  have hPos : assumption_positive_recommendation_utilities S.model := by
    intro u j
    change 0 < (S.canonicalReductionOfSurjective hTypes).data.model.utility u j
    rw [(S.canonicalReductionOfSurjective hTypes).utility_agrees u j, hred]
    exact OpposingTypes.twoTypeReducedModel_positiveUtilities alpha v hpos _ _
  have hPos' : assumption_positive_recommendation_utilities S'.model := by
    intro u j
    change 0 < (S'.canonicalReductionOfSurjective hTypes').data.model.utility u j
    rw [(S'.canonicalReductionOfSurjective hTypes').utility_agrees u j, hred']
    exact OpposingTypes.twoTypeReducedModel_positiveUtilities alpha' v hpos _ _
  have hNonneg : S.model.Nonnegative :=
    RecommendationModel.nonnegative_of_positive S.model hPos
  have hRow : S.model.RowHasPositiveItem :=
    RecommendationModel.rowHasPositiveItem_of_positive S.model hPos
  have hNonneg' : S'.model.Nonnegative :=
    RecommendationModel.nonnegative_of_positive S'.model hPos'
  have hRow' : S'.model.RowHasPositiveItem :=
    RecommendationModel.rowHasPositiveItem_of_positive S'.model hPos'
  exact OpposingTypes.paper_theorem3_price_decreases_firstHalf_of_reduction
    (S.canonicalReduction reps) (S'.canonicalReduction reps')
    reps reps' hred hred' halpha0 halpha1 halpha0' halpha1'
    halpha_le halpha_half halpha_half' hpos hdec hNonneg hRow hNonneg' hRow'

/--
Theorem 3, second half: in the opposing two-type model, increasing `alpha`
away from `1 / 2` weakly increases the price of fairness.
-/
theorem theorem3_price_increases_second_half
    {m n : ℕ} [NeZero m] [NeZero n]
    (S S' : RecommendationModel.SymmetricData m n 2)
    (hTypes : Function.Surjective S.types.toType)
    (hTypes' : Function.Surjective S'.types.toType)
    {alpha alpha' : ℝ} {v : Item n → ℝ}
    (hred : (S.canonicalReductionOfSurjective hTypes).reduced =
      OpposingTypes.twoTypeReducedModel alpha v)
    (hred' : (S'.canonicalReductionOfSurjective hTypes').reduced =
      OpposingTypes.twoTypeReducedModel alpha' v)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (halpha_half : 1 / 2 ≤ alpha)
    (halpha_half' : 1 / 2 ≤ alpha')
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : OpposingTypes.StrictlyDecreasingByIndex v) :
    RecommendationModel.priceOfFairness S.model ≤
      RecommendationModel.priceOfFairness S'.model := by
  let reps : UserTypeAssignment.TypeRepresentatives S.types :=
    AppliedModelingLib.Policy.FiberRepresentatives.ofSurjective hTypes
  let reps' : UserTypeAssignment.TypeRepresentatives S'.types :=
    AppliedModelingLib.Policy.FiberRepresentatives.ofSurjective hTypes'
  have hPos : assumption_positive_recommendation_utilities S.model := by
    intro u j
    change 0 < (S.canonicalReductionOfSurjective hTypes).data.model.utility u j
    rw [(S.canonicalReductionOfSurjective hTypes).utility_agrees u j, hred]
    exact OpposingTypes.twoTypeReducedModel_positiveUtilities alpha v hpos _ _
  have hPos' : assumption_positive_recommendation_utilities S'.model := by
    intro u j
    change 0 < (S'.canonicalReductionOfSurjective hTypes').data.model.utility u j
    rw [(S'.canonicalReductionOfSurjective hTypes').utility_agrees u j, hred']
    exact OpposingTypes.twoTypeReducedModel_positiveUtilities alpha' v hpos _ _
  have hNonneg : S.model.Nonnegative :=
    RecommendationModel.nonnegative_of_positive S.model hPos
  have hRow : S.model.RowHasPositiveItem :=
    RecommendationModel.rowHasPositiveItem_of_positive S.model hPos
  have hNonneg' : S'.model.Nonnegative :=
    RecommendationModel.nonnegative_of_positive S'.model hPos'
  have hRow' : S'.model.RowHasPositiveItem :=
    RecommendationModel.rowHasPositiveItem_of_positive S'.model hPos'
  exact OpposingTypes.paper_theorem3_price_increases_secondHalf_of_reduction
    (S.canonicalReduction reps) (S'.canonicalReduction reps')
    reps reps' hred hred' halpha0 halpha1 halpha0' halpha1'
    halpha_le halpha_half halpha_half' hpos hdec hNonneg hRow hNonneg' hRow'

/--
Theorem 4's first bullet: for every positive, strictly decreasing source value
vector, the displayed no-item-fairness estimated optimum has misestimation
price at most `1 / 2`.

The source's universal value-vector quantifier is deliberately separate from
the second bullet's existential construction.  The corrected estimated masses
are `beta`, `beta`, and `1 - 2 * beta`; see the source correction recorded in
the statement map.
-/
theorem theorem4_misestimation_without_fairness_universal
    {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n)
    (Strue : RecommendationModel.SymmetricData m n 2)
    (Sest : RecommendationModel.SymmetricData m n 3)
    (hTypesTrue : Function.Surjective Strue.types.toType)
    (hTypesEst : Function.Surjective Sest.types.toType)
    {beta : ℝ} {v : Item n → ℝ}
    (htrue : assumption_theorem4_true_model_reduction E Strue)
    (hestimated : assumption_theorem4_estimated_model_reduction E Sest)
    (hredTrue :
      (Strue.canonicalReductionOfSurjective hTypesTrue).reduced =
        OpposingTypes.twoTypeReducedModel (1 / 2 : ℝ) v)
    (hredEst :
      (Sest.canonicalReductionOfSurjective hTypesEst).reduced =
        OpposingTypes.theorem4EstimatedReducedModel beta v)
    (hknown0 :
      ∀ u : User m, Sest.types.toType u = 0 →
        Strue.types.toType u = 0)
    (hknown1 :
      ∀ u : User m, Sest.types.toType u = 1 →
        Strue.types.toType u = 1)
    (hbeta : (n : ℝ)⁻¹ < beta)
    (hvalue : assumption_theorem4_universal_value_vector v) :
    let ρ : TypePolicy 3 n := OpposingTypes.theorem4NoFairnessPolicyCollapsed v
    E.SolvesEstimatedProblem 0
        ((Sest.canonicalReductionOfSurjective hTypesEst).liftedPolicy ρ) ∧
      E.priceOfMisestimation 0
          ((Sest.canonicalReductionOfSurjective hTypesEst).liftedPolicy ρ) ≤
        (1 / 2 : ℝ) := by
  let repsTrue : UserTypeAssignment.TypeRepresentatives Strue.types :=
    AppliedModelingLib.Policy.FiberRepresentatives.ofSurjective hTypesTrue
  let repsEst : UserTypeAssignment.TypeRepresentatives Sest.types :=
    AppliedModelingLib.Policy.FiberRepresentatives.ofSurjective hTypesEst
  have hbeta_half : beta < 1 / 2 :=
    OpposingTypes.theorem4_beta_lt_half_of_estimated_reduction
      Sest hTypesEst hredEst
  have hbeta_nonneg : 0 ≤ beta := by
    have hinv_nonneg : 0 ≤ (n : ℝ)⁻¹ := by positivity
    exact hinv_nonneg.trans hbeta.le
  have hcold_nonneg : 0 ≤ 1 - 2 * beta := by
    nlinarith
  exact
    E.theorem4_misestimation_without_fairness_le_half_trueHalf_collapsed_from_reductions
      (Strue.canonicalReduction repsTrue) (Sest.canonicalReduction repsEst)
      repsEst htrue hestimated hredTrue hredEst hknown0 hknown1 hbeta_nonneg
      hcold_nonneg hvalue.1 hvalue.2

/--
Theorem 4's two-bullet tradeoff for a cold-start user whose true row is the
first opposing type.  For the displayed small-value construction, the
no-item-fairness optimum has price at most `1 / 2`, while an item-fairness
optimum has price above `1 - eps`.

Surjectivity of the true and estimated type maps makes the source's two and
three declared user types actual nonempty population types. The proof chooses
the representatives needed by the reduction internally.
-/
theorem theorem4_misestimation_tradeoff_typeZero
    {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n)
    (Strue : RecommendationModel.SymmetricData m n 2)
    (Sest : RecommendationModel.SymmetricData m n 3)
    (hTypesTrue : Function.Surjective Strue.types.toType)
    (hTypesEst : Function.Surjective Sest.types.toType)
    {beta eps : ℝ}
    (u : User m)
    (htrue : assumption_theorem4_true_model_reduction E Strue)
    (hestimated : assumption_theorem4_estimated_model_reduction E Sest)
    (hredTrue :
      (Strue.canonicalReductionOfSurjective hTypesTrue).reduced =
        OpposingTypes.twoTypeReducedModel (1 / 2 : ℝ)
        (OpposingTypes.theorem4SmallValueVector (n := n) eps))
    (hredEst :
      (Sest.canonicalReductionOfSurjective hTypesEst).reduced =
        OpposingTypes.theorem4EstimatedReducedModel beta
        (OpposingTypes.theorem4SmallValueVector (n := n) eps))
    (hknown0 :
      ∀ u : User m, Sest.types.toType u = 0 →
        Strue.types.toType u = 0)
    (hknown1 :
      ∀ u : User m, Sest.types.toType u = 1 →
        Strue.types.toType u = 1)
    (htrueType : Strue.types.toType u = 0)
    (hestimatedType : Sest.types.toType u = 2)
    (heps : 0 < eps)
    (hbeta : (n : ℝ)⁻¹ < beta) :
    (let ρ0 : TypePolicy 3 n :=
        OpposingTypes.theorem4NoFairnessPolicyCollapsed
          (OpposingTypes.theorem4SmallValueVector (n := n) eps);
      E.SolvesEstimatedProblem 0
          ((Sest.canonicalReductionOfSurjective hTypesEst).liftedPolicy ρ0) ∧
        E.priceOfMisestimation 0
          ((Sest.canonicalReductionOfSurjective hTypesEst).liftedPolicy ρ0) ≤
          (1 / 2 : ℝ)) ∧
      ∃ ρ1 : TypePolicy 3 n,
        E.SolvesEstimatedProblem 1
            ((Sest.canonicalReductionOfSurjective hTypesEst).liftedPolicy ρ1) ∧
          1 - eps < E.priceOfMisestimation 1
            ((Sest.canonicalReductionOfSurjective hTypesEst).liftedPolicy ρ1) := by
  let repsTrue : UserTypeAssignment.TypeRepresentatives Strue.types :=
    AppliedModelingLib.Policy.FiberRepresentatives.ofSurjective hTypesTrue
  let repsEst : UserTypeAssignment.TypeRepresentatives Sest.types :=
    AppliedModelingLib.Policy.FiberRepresentatives.ofSurjective hTypesEst
  have hbeta_half : beta < 1 / 2 :=
    OpposingTypes.theorem4_beta_lt_half_of_estimated_reduction
      Sest hTypesEst hredEst
  have hn : assumption_theorem4_at_least_three_items n :=
    OpposingTypes.theorem4_at_least_three_items_of_beta_domain hbeta hbeta_half
  exact
    EstimatedRecommendationModel.paper_theorem4_misestimation_tradeoff_trueHalf_collapsed_typeZero
      E (Strue.canonicalReduction repsTrue) (Sest.canonicalReduction repsEst)
      repsTrue repsEst u hn htrue hestimated hredTrue hredEst
      hknown0 hknown1 htrueType hestimatedType heps hbeta hbeta_half

/--
Theorem 4's two-bullet tradeoff for a cold-start user whose true row is the
second opposing type.
-/
theorem theorem4_misestimation_tradeoff_typeOne
    {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n)
    (Strue : RecommendationModel.SymmetricData m n 2)
    (Sest : RecommendationModel.SymmetricData m n 3)
    (hTypesTrue : Function.Surjective Strue.types.toType)
    (hTypesEst : Function.Surjective Sest.types.toType)
    {beta eps : ℝ}
    (u : User m)
    (htrue : assumption_theorem4_true_model_reduction E Strue)
    (hestimated : assumption_theorem4_estimated_model_reduction E Sest)
    (hredTrue :
      (Strue.canonicalReductionOfSurjective hTypesTrue).reduced =
        OpposingTypes.twoTypeReducedModel (1 / 2 : ℝ)
        (OpposingTypes.theorem4SmallValueVector (n := n) eps))
    (hredEst :
      (Sest.canonicalReductionOfSurjective hTypesEst).reduced =
        OpposingTypes.theorem4EstimatedReducedModel beta
        (OpposingTypes.theorem4SmallValueVector (n := n) eps))
    (hknown0 :
      ∀ u : User m, Sest.types.toType u = 0 →
        Strue.types.toType u = 0)
    (hknown1 :
      ∀ u : User m, Sest.types.toType u = 1 →
        Strue.types.toType u = 1)
    (htrueType : Strue.types.toType u = 1)
    (hestimatedType : Sest.types.toType u = 2)
    (heps : 0 < eps)
    (hbeta : (n : ℝ)⁻¹ < beta) :
    (let ρ0 : TypePolicy 3 n :=
        OpposingTypes.theorem4NoFairnessPolicyCollapsed
          (OpposingTypes.theorem4SmallValueVector (n := n) eps);
      E.SolvesEstimatedProblem 0
          ((Sest.canonicalReductionOfSurjective hTypesEst).liftedPolicy ρ0) ∧
        E.priceOfMisestimation 0
          ((Sest.canonicalReductionOfSurjective hTypesEst).liftedPolicy ρ0) ≤
          (1 / 2 : ℝ)) ∧
      ∃ ρ1 : TypePolicy 3 n,
        E.SolvesEstimatedProblem 1
            ((Sest.canonicalReductionOfSurjective hTypesEst).liftedPolicy ρ1) ∧
          1 - eps < E.priceOfMisestimation 1
            ((Sest.canonicalReductionOfSurjective hTypesEst).liftedPolicy ρ1) := by
  let repsTrue : UserTypeAssignment.TypeRepresentatives Strue.types :=
    AppliedModelingLib.Policy.FiberRepresentatives.ofSurjective hTypesTrue
  let repsEst : UserTypeAssignment.TypeRepresentatives Sest.types :=
    AppliedModelingLib.Policy.FiberRepresentatives.ofSurjective hTypesEst
  have hbeta_half : beta < 1 / 2 :=
    OpposingTypes.theorem4_beta_lt_half_of_estimated_reduction
      Sest hTypesEst hredEst
  have hn : assumption_theorem4_at_least_three_items n :=
    OpposingTypes.theorem4_at_least_three_items_of_beta_domain hbeta hbeta_half
  exact
    EstimatedRecommendationModel.paper_theorem4_misestimation_tradeoff_trueHalf_collapsed_typeOne
      E (Strue.canonicalReduction repsTrue) (Sest.canonicalReduction repsEst)
      repsTrue repsEst u hn htrue hestimated hredTrue hredEst
      hknown0 hknown1 htrueType hestimatedType heps hbeta hbeta_half

/--
Theorem 4's single high-item-fairness source bullet.  Surjectivity supplies a
cold-start user, and the finite two-type true population discharges the two
internal case lemmas without adding a user-level premise to the source result.
-/
theorem theorem4_misestimation_tradeoff
    {m n : ℕ} [NeZero m] [NeZero n]
    (E : EstimatedRecommendationModel m n)
    (Strue : RecommendationModel.SymmetricData m n 2)
    (Sest : RecommendationModel.SymmetricData m n 3)
    (hTypesTrue : Function.Surjective Strue.types.toType)
    (hTypesEst : Function.Surjective Sest.types.toType)
    {beta eps : ℝ}
    (htrue : assumption_theorem4_true_model_reduction E Strue)
    (hestimated : assumption_theorem4_estimated_model_reduction E Sest)
    (hredTrue :
      (Strue.canonicalReductionOfSurjective hTypesTrue).reduced =
        OpposingTypes.twoTypeReducedModel (1 / 2 : ℝ)
        (OpposingTypes.theorem4SmallValueVector (n := n) eps))
    (hredEst :
      (Sest.canonicalReductionOfSurjective hTypesEst).reduced =
        OpposingTypes.theorem4EstimatedReducedModel beta
        (OpposingTypes.theorem4SmallValueVector (n := n) eps))
    (hknown0 :
      ∀ u : User m, Sest.types.toType u = 0 →
        Strue.types.toType u = 0)
    (hknown1 :
      ∀ u : User m, Sest.types.toType u = 1 →
        Strue.types.toType u = 1)
    (heps : 0 < eps)
    (hbeta : (n : ℝ)⁻¹ < beta) :
    (let ρ0 : TypePolicy 3 n :=
        OpposingTypes.theorem4NoFairnessPolicyCollapsed
          (OpposingTypes.theorem4SmallValueVector (n := n) eps);
      E.SolvesEstimatedProblem 0
          ((Sest.canonicalReductionOfSurjective hTypesEst).liftedPolicy ρ0) ∧
        E.priceOfMisestimation 0
          ((Sest.canonicalReductionOfSurjective hTypesEst).liftedPolicy ρ0) ≤
          (1 / 2 : ℝ)) ∧
      ∃ ρ1 : TypePolicy 3 n,
        E.SolvesEstimatedProblem 1
            ((Sest.canonicalReductionOfSurjective hTypesEst).liftedPolicy ρ1) ∧
          1 - eps < E.priceOfMisestimation 1
            ((Sest.canonicalReductionOfSurjective hTypesEst).liftedPolicy ρ1) := by
  obtain ⟨u, hestimatedType⟩ := hTypesEst 2
  generalize htrueType : Strue.types.toType u = trueType
  fin_cases trueType
  · exact theorem4_misestimation_tradeoff_typeZero
      E Strue Sest hTypesTrue hTypesEst u htrue hestimated hredTrue hredEst
      hknown0 hknown1 htrueType hestimatedType heps hbeta
  · exact theorem4_misestimation_tradeoff_typeOne
      E Strue Sest hTypesTrue hTypesEst u htrue hestimated hredTrue hredEst
      hknown0 hknown1 htrueType hestimatedType heps hbeta

end

end ProofBridge
end GCG24UserItemFairness
