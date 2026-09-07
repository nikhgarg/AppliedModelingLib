import GCG24UserItemFairness.ProofBridge

namespace GCG24UserItemFairness

namespace PaperInterface

open scoped BigOperators
open GCG24UserItemFairness.ProofBridge
noncomputable section

/-! The model, utility, fairness, optimization, and misestimation definitions
are imported from `Basic`, `Optimization`, and `ProofBridge`. Their actual
declarations are the source-mapped semantic prerequisites of these results. -/

/-- Source-facing semantic target for `appendix_c_lemma1_item_fairness_positive`. -/
def appendix_c_lemma1_item_fairness_positiveSpec
    {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n) (hPositive : W.Positive) : Prop :=
  0 < W.optimalItemFairness

/-- Source-facing semantic target for `appendix_c_lemma2_item_fairness_equality_lp_solution_set`. -/
def appendix_c_lemma2_item_fairness_equality_lp_solution_setSpec
    {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n) (hPositive : W.Positive) (rho : Policy m n) : Prop :=
  W.itemFairness rho = W.optimalItemFairness ↔
    ∃ ell : ℝ,
      W.itemFairnessEqualityLPFeasible rho ell ∧
        ∀ rho' : Policy m n, ∀ ell' : ℝ,
          W.itemFairnessEqualityLPFeasible rho' ell' → ell' ≤ ell

/-- Source-facing semantic target for `appendix_d_lemma3_unconstrained_baseline`. -/
def appendix_d_lemma3_unconstrained_baselineSpec
    {n : ℕ} [NeZero n] {alpha : ℝ} {v : Item n → ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : OpposingTypes.StrictlyDecreasingByIndex v) : Prop :=
  TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
    (OpposingTypes.twoTypeReducedModel alpha v) 0 = 1

/-- Source-facing semantic target for `appendix_d_lemma4_problem6_unique_sparse_solution`. -/
def appendix_d_lemma4_problem6_unique_sparse_solutionSpec
    {n : ℕ} [NeZero n] {alpha : ℝ} {v : Item n → ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : OpposingTypes.StrictlyDecreasingByIndex v) : Prop :=
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
      ρ = ρstar ∧ ell = ellstar

/-- Source-facing semantic target for `appendix_d_lemma5_problem6_active_optimizer_closed_form`. -/
def appendix_d_lemma5_problem6_active_optimizer_closed_formSpec
    {n : ℕ} [NeZero n] {alpha : ℝ} {v : Item n → ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : OpposingTypes.StrictlyDecreasingByIndex v) : Prop :=
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
        ellstar / (1 - OpposingTypes.pairShare alpha v j)

/-- Source-facing semantic target for `appendix_d_lemma6_optimal_policy_type_utility_order`. -/
def appendix_d_lemma6_optimal_policy_type_utility_orderSpec
    {n : ℕ} [NeZero n] {alpha : ℝ} {v : Item n → ℝ}
    (halpha0 : 0 < alpha) (halpha_half : alpha < 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : OpposingTypes.StrictlyDecreasingByIndex v) : Prop :=
  TypeWeightedRecommendationModel.normalizedTypeUtility
      (OpposingTypes.twoTypeReducedModel alpha v)
      (OpposingTypes.problem6FirstClosedPolicy alpha v halpha0
        (halpha_half.trans (by norm_num)) hpos) 1 ≤
    TypeWeightedRecommendationModel.normalizedTypeUtility
      (OpposingTypes.twoTypeReducedModel alpha v)
      (OpposingTypes.problem6FirstClosedPolicy alpha v halpha0
        (halpha_half.trans (by norm_num)) hpos) 0

/-- Source-facing semantic target for `appendix_d_lemma7_active_optimizer_pivot_monotonicity`. -/
def appendix_d_lemma7_active_optimizer_pivot_monotonicitySpec
    {n : ℕ} [NeZero n] {alpha alpha' : ℝ} {v : Item n → ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : OpposingTypes.StrictlyDecreasingByIndex v) : Prop :=
  (TypePolicy.lastActiveTypeZero
      (OpposingTypes.problem6FirstClosedPolicy alpha v
        halpha0 halpha1 hpos)).val ≤
    (TypePolicy.lastActiveTypeZero
      (OpposingTypes.problem6FirstClosedPolicy alpha' v
        halpha0' halpha1' hpos)).val

/-- Source-facing semantic target for `appendix_d_lemma8_selected_pivot_stitching`. -/
def appendix_d_lemma8_selected_pivot_stitchingSpec
    {n : ℕ} [NeZero n] {alpha alpha' : ℝ} {v : Item n → ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (halpha_half : alpha ≤ 1 / 2) (halpha_half' : alpha' ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : OpposingTypes.StrictlyDecreasingByIndex v) : Prop :=
  (OpposingTypes.twoTypeReducedModel alpha v).optimalItemFairness ≤
    (OpposingTypes.twoTypeReducedModel alpha' v).optimalItemFairness

/-- Source-facing semantic target for `appendix_d_lemma9_pair_share_algebra`. -/
def appendix_d_lemma9_pair_share_algebraSpec
    {n : ℕ} {alpha alpha' : ℝ} {v : Item n → ℝ} {i j : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_lt : alpha < alpha') (hpos : ∀ j : Item n, 0 < v j)
    (hdec : OpposingTypes.StrictlyDecreasingByIndex v)
    (hij : i.val < j.val) : Prop :=
  OpposingTypes.pairShare alpha v j < OpposingTypes.pairShare alpha' v j ∧
    OpposingTypes.pairShare alpha v j < OpposingTypes.pairShare alpha v i

/-- Source-facing semantic target for `appendix_d_lemma10_active_optimizer_pivot_at_or_before_midpoint`. -/
def appendix_d_lemma10_active_optimizer_pivot_at_or_before_midpointSpec
    {n : ℕ} [NeZero n] {alpha : ℝ} {v : Item n → ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha_half : alpha ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : OpposingTypes.StrictlyDecreasingByIndex v) : Prop :=
  let t := TypePolicy.lastActiveTypeZero
    (OpposingTypes.problem6FirstClosedPolicy alpha v halpha0 halpha1 hpos)
  t.val ≤ (OpposingTypes.reverseItem t).val

/-- Source-facing semantic target for `appendix_d_lemma11_optimal_item_fairness_mono_on_active_pivot_interval`. -/
def appendix_d_lemma11_optimal_item_fairness_mono_on_active_pivot_intervalSpec
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
      t.val ≤ (OpposingTypes.reverseItem t).val) : Prop :=
  (OpposingTypes.twoTypeReducedModel alpha v).optimalItemFairness ≤
    (OpposingTypes.twoTypeReducedModel alpha' v).optimalItemFairness

/-- Source-facing semantic target for `appendix_e_lemma12_symmetrized_policy`. -/
def appendix_e_lemma12_symmetrized_policySpec
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hpos : ∀ j : Item n, 0 < v j) {ρ : TypePolicy 3 n}
    (hOptimal : (OpposingTypes.theorem4EstimatedReducedModel beta v).IsOptimalAtLevel 1 ρ) : Prop :=
  (OpposingTypes.theorem4EstimatedReducedModel beta v).IsOptimalAtLevel 1
      (OpposingTypes.theorem4SymmetrizedPolicy ρ) ∧
    OpposingTypes.Theorem4MirrorSymmetricPolicy
      (OpposingTypes.theorem4SymmetrizedPolicy ρ)

/-- Source-facing semantic target for `appendix_e_lemma13_every_optimal_basic_solution_has_pivot_support`. -/
def appendix_e_lemma13_every_optimal_basic_solution_has_pivot_supportSpec
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
    (hbasic : problem11BasicFeasible beta v ρ ell) : Prop :=
  let t := OpposingTypes.theorem4Problem11LastActiveTypeZero ρ
  t.val ≤ (OpposingTypes.reverseItem t).val ∧
    (∀ j : Item n, t.val < j.val → ρ 0 j = 0) ∧
    (∀ j : Item n, j.val < t.val →
      ρ 2 j = 0 ∧ ρ 2 (OpposingTypes.reverseItem j) = 0) ∧
    ∀ s : Item n,
      (∀ j : Item n, s.val < j.val → ρ 0 j = 0) →
      (∀ j : Item n, j.val < s.val →
        ρ 2 j = 0 ∧ ρ 2 (OpposingTypes.reverseItem j) = 0) →
      t.val ≤ s.val

/-- Source-facing semantic target for `appendix_e_lemma14_problem11_has_unique_optimal_solution`. -/
def appendix_e_lemma14_problem11_has_unique_optimal_solutionSpec
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hn : 2 < n)
    (hbeta : (n : ℝ)⁻¹ < beta)
    (hbeta_half : beta < 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : OpposingTypes.StrictlyDecreasingByIndex v) : Prop :=
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
      ρ = ρstar ∧ ell = ellstar

/-- Source-facing semantic target for `appendix_e_lemma15_optimal_solution_full_closed_form`. -/
def appendix_e_lemma15_optimal_solution_full_closed_formSpec
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
      ell' ≤ ell) : Prop :=
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
          (1 + OpposingTypes.paper_lemma15_problem11_leftSum v t)))

/-- Source-facing semantic target for `appendix_e_lemma16_midpoint_order_algebra`. -/
def appendix_e_lemma16_midpoint_order_algebraSpec
    {n : ℕ} {v : Item n → ℝ} (j : Item n)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : OpposingTypes.StrictlyDecreasingByIndex v) : Prop :=
  (j.val < (OpposingTypes.reverseItem j).val →
    (1 / 2 : ℝ) < OpposingTypes.pairShare (1 / 2) v j) ∧
    ((OpposingTypes.reverseItem j).val < j.val →
      OpposingTypes.pairShare (1 / 2) v j < (1 / 2 : ℝ)) ∧
    (j.val = (OpposingTypes.reverseItem j).val →
      OpposingTypes.pairShare (1 / 2) v j = (1 / 2 : ℝ))

/-- Source-facing semantic target for `appendix_e_lemma17_every_optimal_solution_has_no_right_half_support`. -/
def appendix_e_lemma17_every_optimal_solution_has_no_right_half_supportSpec
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
      ell' ≤ ell) : Prop :=
  ∀ j : Item n, (OpposingTypes.reverseItem j).val < j.val → ρ 0 j = 0

/-- Source-facing semantic target for `proposition1_symmetric_lp_reduction`. -/
def proposition1_symmetric_lp_reductionSpec
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
          ρ = ρstar) : Prop :=
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
        ρ = ρstar ∧ ell = RecommendationModel.optimalItemFairness W

/-- Source-facing semantic target for `proposition2_symmetric_optimum_exists`. -/
def proposition2_symmetric_optimum_existsSpec
    {m n K : ℕ} [NeZero m] [NeZero n] [NeZero K]
    (S : RecommendationModel.SymmetricData m n K)
    (hTypes : Function.Surjective S.types.toType)
    (hPos : assumption_positive_recommendation_utilities S.model)
    (hRowsDetermineTypes :
      assumption_proposition2_utility_rows_determine_types S)
    (ρsrc : Policy m n) (ell : ℝ)
    (hsource : RecommendationModel.UserSymmetricEqualityLP.ActiveBasis
      (RecommendationModel.UserSymmetricEqualityLP.ofSymmetricData S) ρsrc ell) : Prop :=
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
            (AppliedModelingLib.Policy.FiberRepresentatives.ofSurjective hTypes) ρsrc))

/-- Source-facing semantic target for `theorem3_price_decreases_first_half`. -/
def theorem3_price_decreases_first_halfSpec
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
    (hdec : OpposingTypes.StrictlyDecreasingByIndex v) : Prop :=
  RecommendationModel.priceOfFairness S'.model ≤
    RecommendationModel.priceOfFairness S.model

/-- Source-facing semantic target for `theorem3_price_increases_second_half`. -/
def theorem3_price_increases_second_halfSpec
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
    (hdec : OpposingTypes.StrictlyDecreasingByIndex v) : Prop :=
  RecommendationModel.priceOfFairness S.model ≤
    RecommendationModel.priceOfFairness S'.model

/-- Source-facing semantic target for `theorem4_misestimation_without_fairness_universal`. -/
def theorem4_misestimation_without_fairness_universalSpec
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
    (hvalue : assumption_theorem4_universal_value_vector v) : Prop :=
  ∃ ρ : Policy m n,
    E.SolvesEstimatedProblem 0 ρ ∧
      E.priceOfMisestimation 0 ρ ≤ (1 / 2 : ℝ)

/--
Source-facing semantic target for Theorem 4's single existential
high-item-fairness bullet.  The source does not select an individual user or
condition on that user's true type; the population model supplies those cases
internally.
-/
def theorem4_misestimation_tradeoffSpec
    {m n : ℕ} [NeZero m] [NeZero n]
    {beta eps : ℝ}
    (hparams : assumption_theorem4_parameter_domain n beta eps) : Prop :=
  ∃ v : Item n → ℝ,
    assumption_theorem4_universal_value_vector v ∧
      ∀ (E : EstimatedRecommendationModel m n)
        (Strue : RecommendationModel.SymmetricData m n 2)
        (Sest : RecommendationModel.SymmetricData m n 3)
        (hTypesTrue : Function.Surjective Strue.types.toType)
        (hTypesEst : Function.Surjective Sest.types.toType),
        assumption_theorem4_true_model_reduction E Strue →
          assumption_theorem4_estimated_model_reduction E Sest →
          (Strue.canonicalReductionOfSurjective hTypesTrue).reduced =
              OpposingTypes.twoTypeReducedModel (1 / 2 : ℝ) v →
          (Sest.canonicalReductionOfSurjective hTypesEst).reduced =
              OpposingTypes.theorem4EstimatedReducedModel beta v →
          (∀ u : User m, Sest.types.toType u = 0 →
              Strue.types.toType u = 0) →
          (∀ u : User m, Sest.types.toType u = 1 →
              Strue.types.toType u = 1) →
          ∃ ρ : Policy m n,
            E.SolvesEstimatedProblem 1 ρ ∧
              1 - eps < E.priceOfMisestimation 1 ρ

end

end PaperInterface
end GCG24UserItemFairness
