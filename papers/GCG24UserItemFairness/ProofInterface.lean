import GCG24UserItemFairness.PaperInterface

import GCG24UserItemFairness.ProofBridge



namespace GCG24UserItemFairness

namespace PaperInterface

open scoped BigOperators
open GCG24UserItemFairness.ProofBridge
noncomputable section


theorem appendix_c_lemma1_item_fairness_positive
    {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n) (hPositive : W.Positive) : appendix_c_lemma1_item_fairness_positiveSpec (m := m) (n := n) (W := W) (hPositive := hPositive) := by
  exact GCG24UserItemFairness.ProofBridge.appendix_c_lemma1_item_fairness_positive (m := m) (n := n) (W := W) (hPositive := hPositive)

theorem appendix_c_lemma2_item_fairness_equality_lp_solution_set
    {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n) (hPositive : W.Positive) (rho : Policy m n) : appendix_c_lemma2_item_fairness_equality_lp_solution_setSpec (m := m) (n := n) (W := W) (hPositive := hPositive) (rho := rho) := by
  exact GCG24UserItemFairness.ProofBridge.appendix_c_lemma2_item_fairness_equality_lp_solution_set (m := m) (n := n) (W := W) (hPositive := hPositive) (rho := rho)

theorem appendix_d_lemma3_unconstrained_baseline
    {n : ℕ} [NeZero n] {alpha : ℝ} {v : Item n → ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : OpposingTypes.StrictlyDecreasingByIndex v) :
    appendix_d_lemma3_unconstrained_baselineSpec
      (n := n) (alpha := alpha) (v := v) halpha0 halpha1 hpos hdec := by
  exact GCG24UserItemFairness.ProofBridge.appendix_d_lemma3_unconstrained_baseline
    (n := n) (alpha := alpha) (v := v) halpha0 halpha1 hpos hdec

theorem appendix_d_lemma4_problem6_unique_sparse_solution
    {n : ℕ} [NeZero n] {alpha : ℝ} {v : Item n → ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : OpposingTypes.StrictlyDecreasingByIndex v) : appendix_d_lemma4_problem6_unique_sparse_solutionSpec (n := n) (alpha := alpha) (v := v) (halpha0 := halpha0) (halpha1 := halpha1) (hpos := hpos) (hdec := hdec) := by
  exact GCG24UserItemFairness.ProofBridge.appendix_d_lemma4_problem6_unique_sparse_solution (n := n) (alpha := alpha) (v := v) (halpha0 := halpha0) (halpha1 := halpha1) (hpos := hpos) (hdec := hdec)

theorem appendix_d_lemma5_problem6_active_optimizer_closed_form
    {n : ℕ} [NeZero n] {alpha : ℝ} {v : Item n → ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : OpposingTypes.StrictlyDecreasingByIndex v) : appendix_d_lemma5_problem6_active_optimizer_closed_formSpec (n := n) (alpha := alpha) (v := v) (halpha0 := halpha0) (halpha1 := halpha1) (hpos := hpos) (hdec := hdec) := by
  exact GCG24UserItemFairness.ProofBridge.appendix_d_lemma5_problem6_active_optimizer_closed_form (n := n) (alpha := alpha) (v := v) (halpha0 := halpha0) (halpha1 := halpha1) (hpos := hpos) (hdec := hdec)

theorem appendix_d_lemma6_optimal_policy_type_utility_order
    {n : ℕ} [NeZero n] {alpha : ℝ} {v : Item n → ℝ}
    (halpha0 : 0 < alpha) (halpha_half : alpha < 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : OpposingTypes.StrictlyDecreasingByIndex v) : appendix_d_lemma6_optimal_policy_type_utility_orderSpec (n := n) (alpha := alpha) (v := v) (halpha0 := halpha0) (halpha_half := halpha_half) (hpos := hpos) (hdec := hdec) := by
  exact GCG24UserItemFairness.ProofBridge.appendix_d_lemma6_optimal_policy_type_utility_order (n := n) (alpha := alpha) (v := v) (halpha0 := halpha0) (halpha_half := halpha_half) (hpos := hpos) (hdec := hdec)

theorem appendix_d_lemma7_active_optimizer_pivot_monotonicity
    {n : ℕ} [NeZero n] {alpha alpha' : ℝ} {v : Item n → ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : OpposingTypes.StrictlyDecreasingByIndex v) : appendix_d_lemma7_active_optimizer_pivot_monotonicitySpec (n := n) (alpha := alpha) (alpha' := alpha') (v := v) (halpha0 := halpha0) (halpha1 := halpha1) (halpha0' := halpha0') (halpha1' := halpha1') (halpha_le := halpha_le) (hpos := hpos) (hdec := hdec) := by
  exact GCG24UserItemFairness.ProofBridge.appendix_d_lemma7_active_optimizer_pivot_monotonicity (n := n) (alpha := alpha) (alpha' := alpha') (v := v) (halpha0 := halpha0) (halpha1 := halpha1) (halpha0' := halpha0') (halpha1' := halpha1') (halpha_le := halpha_le) (hpos := hpos) (hdec := hdec)

theorem appendix_d_lemma8_selected_pivot_stitching
    {n : ℕ} [NeZero n] {alpha alpha' : ℝ} {v : Item n → ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (halpha_half : alpha ≤ 1 / 2) (halpha_half' : alpha' ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : OpposingTypes.StrictlyDecreasingByIndex v) : appendix_d_lemma8_selected_pivot_stitchingSpec (n := n) (alpha := alpha) (alpha' := alpha') (v := v) (halpha0 := halpha0) (halpha1 := halpha1) (halpha0' := halpha0') (halpha1' := halpha1') (halpha_le := halpha_le) (halpha_half := halpha_half) (halpha_half' := halpha_half') (hpos := hpos) (hdec := hdec) := by
  exact GCG24UserItemFairness.ProofBridge.appendix_d_lemma8_selected_pivot_stitching (n := n) (alpha := alpha) (alpha' := alpha') (v := v) (halpha0 := halpha0) (halpha1 := halpha1) (halpha0' := halpha0') (halpha1' := halpha1') (halpha_le := halpha_le) (halpha_half := halpha_half) (halpha_half' := halpha_half') (hpos := hpos) (hdec := hdec)

theorem appendix_d_lemma9_pair_share_algebra
    {n : ℕ} {alpha alpha' : ℝ} {v : Item n → ℝ} {i j : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_lt : alpha < alpha') (hpos : ∀ j : Item n, 0 < v j)
    (hdec : OpposingTypes.StrictlyDecreasingByIndex v)
    (hij : i.val < j.val) : appendix_d_lemma9_pair_share_algebraSpec (n := n) (alpha := alpha) (alpha' := alpha') (v := v) (i := i) (j := j) (halpha0 := halpha0) (halpha1 := halpha1) (halpha0' := halpha0') (halpha1' := halpha1') (halpha_lt := halpha_lt) (hpos := hpos) (hdec := hdec) (hij := hij) := by
  exact GCG24UserItemFairness.ProofBridge.appendix_d_lemma9_pair_share_algebra (n := n) (alpha := alpha) (alpha' := alpha') (v := v) (i := i) (j := j) (halpha0 := halpha0) (halpha1 := halpha1) (halpha0' := halpha0') (halpha1' := halpha1') (halpha_lt := halpha_lt) (hpos := hpos) (hdec := hdec) (hij := hij)

theorem appendix_d_lemma10_active_optimizer_pivot_at_or_before_midpoint
    {n : ℕ} [NeZero n] {alpha : ℝ} {v : Item n → ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha_half : alpha ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : OpposingTypes.StrictlyDecreasingByIndex v) : appendix_d_lemma10_active_optimizer_pivot_at_or_before_midpointSpec (n := n) (alpha := alpha) (v := v) (halpha0 := halpha0) (halpha1 := halpha1) (halpha_half := halpha_half) (hpos := hpos) (hdec := hdec) := by
  exact GCG24UserItemFairness.ProofBridge.appendix_d_lemma10_active_optimizer_pivot_at_or_before_midpoint (n := n) (alpha := alpha) (v := v) (halpha0 := halpha0) (halpha1 := halpha1) (halpha_half := halpha_half) (hpos := hpos) (hdec := hdec)

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
      t.val ≤ (OpposingTypes.reverseItem t).val) : appendix_d_lemma11_optimal_item_fairness_mono_on_active_pivot_intervalSpec (n := n) (alpha := alpha) (alpha' := alpha') (v := v) (halpha0 := halpha0) (halpha1 := halpha1) (halpha0' := halpha0') (halpha1' := halpha1') (halpha_le := halpha_le) (hpos := hpos) (hdec := hdec) (hpivot := hpivot) (hcenter := hcenter) := by
  exact GCG24UserItemFairness.ProofBridge.appendix_d_lemma11_optimal_item_fairness_mono_on_active_pivot_interval (n := n) (alpha := alpha) (alpha' := alpha') (v := v) (halpha0 := halpha0) (halpha1 := halpha1) (halpha0' := halpha0') (halpha1' := halpha1') (halpha_le := halpha_le) (hpos := hpos) (hdec := hdec) (hpivot := hpivot) (hcenter := hcenter)

theorem appendix_e_lemma12_symmetrized_policy
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hpos : ∀ j : Item n, 0 < v j) {ρ : TypePolicy 3 n}
    (hOptimal : (OpposingTypes.theorem4EstimatedReducedModel beta v).IsOptimalAtLevel 1 ρ) : appendix_e_lemma12_symmetrized_policySpec (n := n) (beta := beta) (v := v) (hpos := hpos) (ρ := ρ) (hOptimal := hOptimal) := by
  exact GCG24UserItemFairness.ProofBridge.appendix_e_lemma12_symmetrized_policy (n := n) (beta := beta) (v := v) (hpos := hpos) (ρ := ρ) (hOptimal := hOptimal)

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
    (hbasic : problem11BasicFeasible beta v ρ ell) : appendix_e_lemma13_every_optimal_basic_solution_has_pivot_supportSpec (n := n) (beta := beta) (v := v) (ρ := ρ) (ell := ell) (hn := hn) (hbeta := hbeta) (hbeta_half := hbeta_half) (hpos := hpos) (hdec := hdec) (hmirror := hmirror) (hitem_eq := hitem_eq) (hoptimal := hoptimal) (hbasic := hbasic) := by
  exact GCG24UserItemFairness.ProofBridge.appendix_e_lemma13_every_optimal_basic_solution_has_pivot_support (n := n) (beta := beta) (v := v) (ρ := ρ) (ell := ell) (hn := hn) (hbeta := hbeta) (hbeta_half := hbeta_half) (hpos := hpos) (hdec := hdec) (hmirror := hmirror) (hitem_eq := hitem_eq) (hoptimal := hoptimal) (hbasic := hbasic)

theorem appendix_e_lemma14_problem11_has_unique_optimal_solution
    {n : ℕ} [NeZero n] {beta : ℝ} {v : Item n → ℝ}
    (hn : 2 < n)
    (hbeta : (n : ℝ)⁻¹ < beta)
    (hbeta_half : beta < 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : OpposingTypes.StrictlyDecreasingByIndex v) : appendix_e_lemma14_problem11_has_unique_optimal_solutionSpec (n := n) (beta := beta) (v := v) (hn := hn) (hbeta := hbeta) (hbeta_half := hbeta_half) (hpos := hpos) (hdec := hdec) := by
  exact GCG24UserItemFairness.ProofBridge.appendix_e_lemma14_problem11_has_unique_optimal_solution (n := n) (beta := beta) (v := v) (hn := hn) (hbeta := hbeta) (hbeta_half := hbeta_half) (hpos := hpos) (hdec := hdec)

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
      ell' ≤ ell) : appendix_e_lemma15_optimal_solution_full_closed_formSpec (n := n) (beta := beta) (v := v) (ρ := ρ) (ell := ell) (hn := hn) (hbeta := hbeta) (hbeta_half := hbeta_half) (hpos := hpos) (hdec := hdec) (hmirror := hmirror) (hitem_eq := hitem_eq) (hoptimal := hoptimal) := by
  exact GCG24UserItemFairness.ProofBridge.appendix_e_lemma15_optimal_solution_full_closed_form (n := n) (beta := beta) (v := v) (ρ := ρ) (ell := ell) (hn := hn) (hbeta := hbeta) (hbeta_half := hbeta_half) (hpos := hpos) (hdec := hdec) (hmirror := hmirror) (hitem_eq := hitem_eq) (hoptimal := hoptimal)

theorem appendix_e_lemma16_midpoint_order_algebra
    {n : ℕ} {v : Item n → ℝ} (j : Item n)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : OpposingTypes.StrictlyDecreasingByIndex v) : appendix_e_lemma16_midpoint_order_algebraSpec (n := n) (v := v) (j := j) (hpos := hpos) (hdec := hdec) := by
  exact GCG24UserItemFairness.ProofBridge.appendix_e_lemma16_midpoint_order_algebra (n := n) (v := v) (j := j) (hpos := hpos) (hdec := hdec)

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
      ell' ≤ ell) : appendix_e_lemma17_every_optimal_solution_has_no_right_half_supportSpec (n := n) (beta := beta) (v := v) (ρ := ρ) (ell := ell) (hn := hn) (hbeta := hbeta) (hbeta_half := hbeta_half) (hpos := hpos) (hdec := hdec) (hmirror := hmirror) (hitem_eq := hitem_eq) (hoptimal := hoptimal) := by
  exact GCG24UserItemFairness.ProofBridge.appendix_e_lemma17_every_optimal_solution_has_no_right_half_support (n := n) (beta := beta) (v := v) (ρ := ρ) (ell := ell) (hn := hn) (hbeta := hbeta) (hbeta_half := hbeta_half) (hpos := hpos) (hdec := hdec) (hmirror := hmirror) (hitem_eq := hitem_eq) (hoptimal := hoptimal)

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
          ρ = ρstar) : proposition1_symmetric_lp_reductionSpec (m := m) (n := n) (W := W) (hPos := hPos) (S := S) (D := D) (ρstar := ρstar) (hProblemTwo := hProblemTwo) (hStarMem := hStarMem) (hUniqueFeasible := hUniqueFeasible) := by
  exact GCG24UserItemFairness.ProofBridge.proposition1_symmetric_lp_reduction (m := m) (n := n) (W := W) (hPos := hPos) (S := S) (D := D) (ρstar := ρstar) (hProblemTwo := hProblemTwo) (hStarMem := hStarMem) (hUniqueFeasible := hUniqueFeasible)

theorem proposition2_symmetric_optimum_exists
    {m n K : ℕ} [NeZero m] [NeZero n] [NeZero K]
    (S : RecommendationModel.SymmetricData m n K)
    (hTypes : Function.Surjective S.types.toType)
    (hPos : assumption_positive_recommendation_utilities S.model)
    (hRowsDetermineTypes :
      assumption_proposition2_utility_rows_determine_types S)
    (ρsrc : Policy m n) (ell : ℝ)
    (hsource : RecommendationModel.UserSymmetricEqualityLP.ActiveBasis
      (RecommendationModel.UserSymmetricEqualityLP.ofSymmetricData S) ρsrc ell) : proposition2_symmetric_optimum_existsSpec (m := m) (n := n) (K := K) (S := S) (hTypes := hTypes) (hPos := hPos) (hRowsDetermineTypes := hRowsDetermineTypes) (ρsrc := ρsrc) (ell := ell) (hsource := hsource) := by
  exact GCG24UserItemFairness.ProofBridge.proposition2_symmetric_optimum_exists (m := m) (n := n) (K := K) (S := S) (hTypes := hTypes) (hPos := hPos) (hRowsDetermineTypes := hRowsDetermineTypes) (ρsrc := ρsrc) (ell := ell) (hsource := hsource)

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
    (hdec : OpposingTypes.StrictlyDecreasingByIndex v) : theorem3_price_decreases_first_halfSpec (m := m) (n := n) (S := S) (S' := S') (hTypes := hTypes) (hTypes' := hTypes') (alpha := alpha) (alpha' := alpha') (v := v) (hred := hred) (hred' := hred') (halpha0 := halpha0) (halpha1 := halpha1) (halpha0' := halpha0') (halpha1' := halpha1') (halpha_le := halpha_le) (halpha_half := halpha_half) (halpha_half' := halpha_half') (hpos := hpos) (hdec := hdec) := by
  exact GCG24UserItemFairness.ProofBridge.theorem3_price_decreases_first_half (m := m) (n := n) (S := S) (S' := S') (hTypes := hTypes) (hTypes' := hTypes') (alpha := alpha) (alpha' := alpha') (v := v) (hred := hred) (hred' := hred') (halpha0 := halpha0) (halpha1 := halpha1) (halpha0' := halpha0') (halpha1' := halpha1') (halpha_le := halpha_le) (halpha_half := halpha_half) (halpha_half' := halpha_half') (hpos := hpos) (hdec := hdec)

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
    (hdec : OpposingTypes.StrictlyDecreasingByIndex v) : theorem3_price_increases_second_halfSpec (m := m) (n := n) (S := S) (S' := S') (hTypes := hTypes) (hTypes' := hTypes') (alpha := alpha) (alpha' := alpha') (v := v) (hred := hred) (hred' := hred') (halpha0 := halpha0) (halpha1 := halpha1) (halpha0' := halpha0') (halpha1' := halpha1') (halpha_le := halpha_le) (halpha_half := halpha_half) (halpha_half' := halpha_half') (hpos := hpos) (hdec := hdec) := by
  exact GCG24UserItemFairness.ProofBridge.theorem3_price_increases_second_half (m := m) (n := n) (S := S) (S' := S') (hTypes := hTypes) (hTypes' := hTypes') (alpha := alpha) (alpha' := alpha') (v := v) (hred := hred) (hred' := hred') (halpha0 := halpha0) (halpha1 := halpha1) (halpha0' := halpha0') (halpha1' := halpha1') (halpha_le := halpha_le) (halpha_half := halpha_half) (halpha_half' := halpha_half') (hpos := hpos) (hdec := hdec)

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
    (hvalue : assumption_theorem4_universal_value_vector v) : theorem4_misestimation_without_fairness_universalSpec (m := m) (n := n) (E := E) (Strue := Strue) (Sest := Sest) (hTypesTrue := hTypesTrue) (hTypesEst := hTypesEst) (beta := beta) (v := v) (htrue := htrue) (hestimated := hestimated) (hredTrue := hredTrue) (hredEst := hredEst) (hknown0 := hknown0) (hknown1 := hknown1) (hbeta := hbeta) (hvalue := hvalue) := by
  let ρ : TypePolicy 3 n := OpposingTypes.theorem4NoFairnessPolicyCollapsed v
  refine ⟨(Sest.canonicalReductionOfSurjective hTypesEst).liftedPolicy ρ, ?_⟩
  exact GCG24UserItemFairness.ProofBridge.theorem4_misestimation_without_fairness_universal
    (m := m) (n := n) (E := E) (Strue := Strue) (Sest := Sest)
    (hTypesTrue := hTypesTrue) (hTypesEst := hTypesEst) (beta := beta) (v := v)
    (htrue := htrue) (hestimated := hestimated) (hredTrue := hredTrue)
    (hredEst := hredEst) (hknown0 := hknown0) (hknown1 := hknown1)
    (hbeta := hbeta) (hvalue := hvalue)

/--
Theorem 4's single existential high-item-fairness source bullet.  The two
cold-user true-type cases are discharged inside `ProofBridge`; they are not
premises of the paper-facing statement.
-/
theorem theorem4_misestimation_tradeoff
    {m n : ℕ} [NeZero m] [NeZero n]
    {beta eps : ℝ}
    (hparams : assumption_theorem4_parameter_domain n beta eps) :
    theorem4_misestimation_tradeoffSpec
      (m := m) (n := n) (beta := beta) (eps := eps) hparams := by
  rcases hparams with ⟨heps, hbeta, _⟩
  refine ⟨OpposingTypes.theorem4SmallValueVector (n := n) eps, ?_, ?_⟩
  · exact ⟨OpposingTypes.theorem4SmallValueVector_pos (n := n) (eps := eps) heps,
      OpposingTypes.theorem4SmallValueVector_strictlyDecreasing
        (n := n) (eps := eps) heps⟩
  · intro E Strue Sest hTypesTrue hTypesEst htrue hestimated hredTrue hredEst
      hknown0 hknown1
    obtain ⟨_, ρ, hsolves, hlarge⟩ :=
      GCG24UserItemFairness.ProofBridge.theorem4_misestimation_tradeoff
        (m := m) (n := n) (E := E) (Strue := Strue) (Sest := Sest)
        (hTypesTrue := hTypesTrue) (hTypesEst := hTypesEst) (beta := beta)
        (eps := eps) (htrue := htrue) (hestimated := hestimated)
        (hredTrue := hredTrue) (hredEst := hredEst) (hknown0 := hknown0)
        (hknown1 := hknown1) (heps := heps) (hbeta := hbeta)
    exact ⟨(Sest.canonicalReductionOfSurjective hTypesEst).liftedPolicy ρ,
      hsolves, hlarge⟩

end

end PaperInterface
end GCG24UserItemFairness
