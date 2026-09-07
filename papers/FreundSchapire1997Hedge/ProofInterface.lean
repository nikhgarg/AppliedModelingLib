import FreundSchapire1997Hedge.PaperInterface
import FreundSchapire1997Hedge.MainTheorems

/-!
# Proof interface: Freund--Schapire (1997) Hedge

Each theorem below is exact-type proof evidence for one transparent semantic
specification in `PaperInterface.lean`.
-/

namespace FreundSchapire1997Hedge

/-- Checked proof endpoint for the finite source-facing Lemma 1 target. -/
theorem lemma1_finite_weight_potential :
    lemma1_finite_weight_potentialSpec := by
  classical
  exact lemma1_finite_weight_potential_core

/-- Checked proof endpoint for both comparator clauses printed in Theorem 2. -/
theorem theorem2_hedge_comparator_bounds :
    theorem2_hedge_comparator_boundsSpec := by
  classical
  intro Action _ _ discount hdiscount hdiscount_lt_one state hinitial losses hloss
  constructor
  · intro action
    simpa using
      (AppliedModelingLib.Learning.Online.hedgeWeightState_theorem2_subset_extendedReal
        discount hdiscount hdiscount_lt_one state hinitial losses hloss
        ({action} : Finset Action) (by simp))
  · intro selected hselected
    exact AppliedModelingLib.Learning.Online.hedgeWeightState_theorem2_subset_extendedReal
      discount hdiscount hdiscount_lt_one state hinitial losses hloss selected hselected

/-- Checked Vovk-dependent necessary-direction endpoint for source Theorem 3. -/
theorem theorem3_global_allocation_lower_tradeoff_checked :
    theorem3_global_allocation_lower_tradeoffSpec := by
  intro discount c a hdiscount hdiscount_lt_one hc_pos ha_pos hbounded
  exact theorem3_global_allocation_lower_tradeoff
    hdiscount hdiscount_lt_one hc_pos ha_pos hbounded

/-- Checked proof endpoint for source Lemma 4. -/
theorem lemma4_learning_rate_bound :
    lemma4_learning_rate_boundSpec := by
  intro loss lossBound regret regretBound hloss hlossBound hregret hregretBound
  exact AppliedModelingLib.Learning.Online.hedge_learning_rate_bound_closed
    hloss hlossBound hregret hregretBound

/-- Checked proof endpoint for the source-general Theorem 5 target. -/
theorem theorem5_decision_prediction_general :
    theorem5_decision_prediction_generalSpec := by
  classical
  exact theorem5_decision_prediction_general_core

/-- Checked proof endpoint for the finite source-facing AdaBoost Theorem 6 target. -/
theorem theorem6_adaBoost_finite :
    theorem6_adaBoost_finiteSpec := by
  classical
  exact theorem6_adaBoost_finite_core

/-- Checked proof endpoint for source Theorem 8's weighted-threshold VC bound. -/
theorem theorem8_weighted_threshold_vc :
    theorem8_weighted_threshold_vcSpec := by
  exact theorem8_weighted_threshold_vc_core

/-- Checked proof endpoint for source Theorem 9's soft AdaBoost error bound. -/
theorem theorem9_soft_adaBoost_error :
    theorem9_soft_adaBoost_errorSpec := by
  classical
  exact theorem9_soft_adaBoost_error_core

/-- Checked proof endpoint for source Eq. (21)'s binary-KL error bound. -/
theorem equation21_adaBoost_binaryKL :
    equation21_adaBoost_binaryKLSpec := by
  classical
  exact equation21_adaBoost_binaryKL_core

/-- Checked proof endpoint for source Eq. (22)'s uniform-edge bound. -/
theorem equation22_adaBoost_uniform_edge :
    equation22_adaBoost_uniform_edgeSpec := by
  classical
  exact equation22_adaBoost_uniform_edge_core

/-- Checked proof endpoint for source Eq. (23)'s sufficient iteration budget. -/
theorem equation23_adaBoost_quadratic_iterations :
    equation23_adaBoost_quadratic_iterationsSpec := by
  classical
  exact equation23_adaBoost_quadratic_iterations_core

/-- Checked proof endpoint for source Theorem 10's AdaBoost.M1 error bound. -/
theorem theorem10_adaBoostM1_error :
    theorem10_adaBoostM1_errorSpec := by
  classical
  intro Training Label _ _ _ _ state label hstate_total hypotheses hvalid hweak
  exact ⟨AppliedModelingLib.Learning.Online.adaBoostM1FinalHypothesis_score_le
      state label hypotheses hvalid,
    theorem10_adaBoostM1_error_core state label hstate_total hypotheses hvalid hweak⟩

/-- Checked proof endpoint for source Theorem 11's AdaBoost.M2 error bound. -/
theorem theorem11_adaBoostM2_error :
    theorem11_adaBoostM2_errorSpec := by
  classical
  intro Training Label _ _ _ _ label exampleWeight state hexample_nonneg
    hexample_total hlabels hinitial hstate_total hypotheses hhypothesis
  letI : Nonempty (AppliedModelingLib.Learning.Online.AdaBoostM2Instance
      Training Label label) :=
    AppliedModelingLib.Learning.Online.adaBoostM2Instance_nonempty label hlabels
  intro hvalid
  exact ⟨AppliedModelingLib.Learning.Online.adaBoostM2FinalHypothesis_score_le
      label state hypotheses hvalid,
    theorem11_adaBoostM2_error_core label exampleWeight state hexample_nonneg
      hexample_total hlabels hinitial hstate_total hypotheses hhypothesis hvalid⟩

/-- Checked proof endpoint for Figure 5's source-facing AdaBoost.R Theorem 12 bound. -/
theorem theorem12_adaBoostR_error :
    theorem12_adaBoostR_errorSpec := by
  classical
  exact theorem12_adaBoostR_error_core

end FreundSchapire1997Hedge
