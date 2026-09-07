import AppliedModelingLib.Learning.Online.Hedge
import AppliedModelingLib.Learning.Online.AdaBoost
import AppliedModelingLib.Learning.Online.AdaBoostMulticlass
import AppliedModelingLib.Learning.Online.AdaBoostMulticlassM2
import AppliedModelingLib.Learning.Online.AdaBoostRegression
import AppliedModelingLib.Learning.Online.DecisionTheoreticHedge
import AppliedModelingLib.Learning.Online.VovkLowerBound
import AppliedModelingLib.Learning.Online.AllocationDecisionReduction
import AppliedModelingLib.Learning.Online.UnitCoordinateGame
import AppliedModelingLib.Learning.Online.VovkGlobalGame
import AppliedModelingLib.Foundations.Math.FiniteOptimization
import AppliedModelingLib.Learning.Statistics

/-!
# Finite Hedge source theorem

This implementation realizes the finite weight-vector form of Lemma 1 in
Freund--Schapire (1997).
-/

namespace FreundSchapire1997Hedge

open AppliedModelingLib
open AppliedModelingLib.Learning.Online
open AppliedModelingLib.Statistics

/-- The finite source-weight conclusion of Freund--Schapire (1997), Lemma 1. -/
theorem lemma1_finite_weight_potential_core
    {Action : Type} [Fintype Action] [Nonempty Action]
    (discount : ℝ) (hdiscount : 0 < discount) (hdiscount_one : discount ≤ 1)
    (state : HedgeWeightState Action)
    (hinitial : (∑ action, state.weight action) = 1)
    (losses : List (Action → ℝ))
    (hloss : ∀ loss ∈ losses, ∀ action, 0 ≤ loss action ∧ loss action ≤ 1) :
    Real.log
        (∑ action,
          (hedgeWeightStateRun discount hdiscount state losses).weight action) ≤
      -(1 - discount) * hedgeWeightStateCumulativeLoss discount hdiscount state losses := by
  classical
  exact hedgeWeightState_lemma1_finite discount hdiscount hdiscount_one state hinitial losses hloss

/-- The finite real-valued single-comparator conclusion of source Theorem 2. -/
theorem theorem2_single_comparator_finite_core
    {Action : Type} [Fintype Action] [Nonempty Action]
    (discount : ℝ) (hdiscount : 0 < discount) (hdiscount_lt_one : discount < 1)
    (state : HedgeWeightState Action)
    (hinitial : (∑ action, state.weight action) = 1)
    (losses : List (Action → ℝ))
    (hloss : ∀ loss ∈ losses, ∀ action, 0 ≤ loss action ∧ loss action ≤ 1)
    (action : Action) (hweight : 0 < state.weight action) :
    hedgeWeightStateCumulativeLoss discount hdiscount state losses ≤
      (-Real.log (state.weight action) -
          (losses.map fun loss => loss action).sum * Real.log discount) /
        (1 - discount) := by
  classical
  exact hedgeWeightState_theorem2_single_finite discount hdiscount hdiscount_lt_one state
    hinitial losses hloss action hweight

/-- The finite real-valued subset-comparator conclusion of source Theorem 2, Eq. (8). -/
theorem theorem2_subset_comparator_finite_core
    {Action : Type} [Fintype Action] [Nonempty Action]
    (discount : ℝ) (hdiscount : 0 < discount) (hdiscount_lt_one : discount < 1)
    (state : HedgeWeightState Action)
    (hinitial : (∑ action, state.weight action) = 1)
    (losses : List (Action → ℝ))
    (hloss : ∀ loss ∈ losses, ∀ action, 0 ≤ loss action ∧ loss action ≤ 1)
    (selected : Finset Action) (hselected : selected.Nonempty)
    (hweight : 0 < ∑ action ∈ selected, state.weight action) :
    hedgeWeightStateCumulativeLoss discount hdiscount state losses ≤
      (-Real.log (∑ action ∈ selected, state.weight action) -
          (selected.sup' hselected (fun action =>
            (losses.map fun loss => loss action).sum)) * Real.log discount) /
        (1 - discount) := by
  classical
  exact hedgeWeightState_theorem2_subset_finite discount hdiscount hdiscount_lt_one state
    hinitial losses hloss selected hselected hweight

/-- The finite equal-prior conclusion of source Theorem 2, Eq. (9). -/
theorem theorem2_uniform_best_finite_core
    {Action : Type} [Fintype Action] [Nonempty Action]
    (discount : ℝ) (hdiscount : 0 < discount) (hdiscount_lt_one : discount < 1)
    (state : HedgeWeightState Action)
    (huniform : ∀ action, state.weight action = 1 / (Fintype.card Action : ℝ))
    (losses : List (Action → ℝ))
    (hloss : ∀ loss ∈ losses, ∀ action, 0 ≤ loss action ∧ loss action ≤ 1) :
    hedgeWeightStateCumulativeLoss discount hdiscount state losses ≤
      ((Finset.univ.inf' Finset.univ_nonempty
          (fun action => (losses.map fun loss => loss action).sum)) *
          Real.log (1 / discount) + Real.log (Fintype.card Action : ℝ)) /
        (1 - discount) := by
  classical
  exact hedgeWeightState_theorem2_uniform_best_finite discount hdiscount hdiscount_lt_one
    state huniform losses hloss

/-- The closed-boundary conclusion of source Lemma 4. -/
theorem lemma4_finite_learning_rate_core
    (loss lossBound regret regretBound : ℝ)
    (hloss_nonneg : 0 ≤ loss) (hloss_le : loss ≤ lossBound)
    (hregret_pos : 0 < regret) (hregret_le : regret ≤ regretBound) :
    (-loss * Real.log (hedgeDiscountFromBoundsClosed lossBound regretBound) + regret) /
        (1 - hedgeDiscountFromBoundsClosed lossBound regretBound) ≤
      loss + Real.sqrt (2 * lossBound * regretBound) + regret := by
  exact hedge_learning_rate_bound_closed hloss_nonneg hloss_le hregret_pos hregret_le

/--
The finite source-model conclusion of Theorem 5. At each round, the learner
uses the literal mixture `D_t = ∑_i p_{t,i} E_{t,i}` of the experts'
decision PMFs. `lossBound` is the paper's positive upper bound `L̄` on the
best fixed expert's cumulative expected loss.
-/
theorem theorem5_decision_prediction_finite_core
    {Expert Decision Outcome : Type}
    [Fintype Expert] [DecidableEq Expert] [Nonempty Expert]
    [Fintype Decision] [DecidableEq Decision]
    (state : HedgeWeightState Expert)
    (huniform : ∀ expert, state.weight expert = 1 / (Fintype.card Expert : ℝ))
    (rounds : List (FiniteDecisionHedgeRound Expert Decision Outcome))
    (lossBound : ℝ)
    (hbest_le_bound :
      Finset.univ.inf' Finset.univ_nonempty
        (fun expert => (rounds.map fun round => round.inducedLoss expert).sum) ≤ lossBound)
    (hlossBound_pos : 0 < lossBound)
    (hcard : 1 < Fintype.card Expert) :
    FiniteDecisionHedgeRound.hedgeCumulativeDecisionLoss
        (hedgeDiscountFromBounds lossBound (Real.log (Fintype.card Expert : ℝ)))
        (by
          unfold hedgeDiscountFromBounds
          apply one_div_pos.mpr
          have hcard_real : 1 < (Fintype.card Expert : ℝ) := by
            exact_mod_cast hcard
          have hlog_pos : 0 < Real.log (Fintype.card Expert : ℝ) :=
            Real.log_pos hcard_real
          have hratio_pos : 0 < 2 * Real.log (Fintype.card Expert : ℝ) / lossBound := by
            exact div_pos (mul_pos (by norm_num) hlog_pos) hlossBound_pos
          nlinarith [Real.sqrt_pos.mpr hratio_pos])
        state rounds ≤
      (Finset.univ.inf' Finset.univ_nonempty
          (fun expert => (rounds.map fun round => round.inducedLoss expert).sum)) +
        Real.sqrt (2 * lossBound * Real.log (Fintype.card Expert : ℝ)) +
          Real.log (Fintype.card Expert : ℝ) := by
  exact FiniteDecisionHedgeRound.hedgeCumulativeDecisionLoss_uniform_tuned_regret_bound
    state huniform rounds lossBound hbest_le_bound hlossBound_pos hcard

/--
The source-general conclusion of Theorem 5. `game.Distribution` is not
restricted to finite support; the game's checked mixture-expectation law is
the probabilistic content of the displayed equality
`L(D_t,y_t) = ∑_i p_{t,i} L(E_{t,i},y_t)`.
-/
theorem theorem5_decision_prediction_general_core
    {Expert Decision Outcome : Type*}
    [Fintype Expert] [DecidableEq Expert] [Nonempty Expert]
    [MeasurableSpace Decision]
    (game : GeneralDecisionHedgeGame Expert Decision Outcome)
    (state : HedgeWeightState Expert)
    (huniform : ∀ expert, state.weight expert = 1 / (Fintype.card Expert : ℝ))
    (rounds : List (GeneralDecisionHedgeRound game))
    (lossBound : ℝ)
    (hbest_le_bound :
      Finset.univ.inf' Finset.univ_nonempty
        (fun expert => (rounds.map fun round => round.inducedLoss expert).sum) ≤ lossBound)
    (_hlossBound_le_rounds : lossBound ≤ rounds.length)
    (hlossBound_pos : 0 < lossBound)
    (hcard : 1 < Fintype.card Expert) :
    GeneralDecisionHedgeRound.hedgeCumulativeDecisionLoss
        (hedgeDiscountFromBounds lossBound (Real.log (Fintype.card Expert : ℝ)))
        (by
          unfold hedgeDiscountFromBounds
          apply one_div_pos.mpr
          have hcard_real : 1 < (Fintype.card Expert : ℝ) := by
            exact_mod_cast hcard
          have hlog_pos : 0 < Real.log (Fintype.card Expert : ℝ) :=
            Real.log_pos hcard_real
          have hratio_pos : 0 < 2 * Real.log (Fintype.card Expert : ℝ) / lossBound := by
            exact div_pos (mul_pos (by norm_num) hlog_pos) hlossBound_pos
          nlinarith [Real.sqrt_pos.mpr hratio_pos])
        state rounds ≤
      (Finset.univ.inf' Finset.univ_nonempty
          (fun expert => (rounds.map fun round => round.inducedLoss expert).sum)) +
        Real.sqrt (2 * lossBound * Real.log (Fintype.card Expert : ℝ)) +
          Real.log (Fintype.card Expert : ℝ) := by
  exact GeneralDecisionHedgeRound.hedgeCumulativeDecisionLoss_uniform_tuned_regret_bound
    state huniform rounds lossBound hbest_le_bound hlossBound_pos hcard

/-- The finite source-model conclusion of Freund--Schapire (1997), Theorem 6. -/
theorem theorem6_adaBoost_finite_core
    {Training : Type} [Fintype Training] [DecidableEq Training] [Nonempty Training]
    (state : HedgeWeightState Training) (label : Training → ℝ)
    (hstate_total : ∑ sample, state.weight sample = 1)
    (hlabel_unit : ∀ sample, 0 ≤ label sample ∧ label sample ≤ 1)
    (hlabel_boolean : ∀ sample, label sample = 0 ∨ label sample = 1)
    (hypotheses : List (Training → ℝ))
    (hhypothesis : ∀ hypothesis ∈ hypotheses, ∀ sample,
      0 ≤ hypothesis sample ∧ hypothesis sample ≤ 1)
    (hvalid : AdaBoostAdmissible state label hypotheses) :
    adaBoostTrainingError state label hypotheses hvalid ≤
      adaBoostTheorem6Factor state label hypotheses hvalid := by
  exact adaBoost_training_error_le_theorem6Factor state label hstate_total hlabel_unit
    hlabel_boolean hypotheses hhypothesis hvalid

/-- Source Eq. (21): the Theorem-6 product is bounded by the binary-KL sum. -/
theorem equation21_adaBoost_binaryKL_core
    {Training : Type} [Fintype Training] [DecidableEq Training] [Nonempty Training]
    (state : HedgeWeightState Training) (label : Training → ℝ)
    (hstate_total : ∑ sample, state.weight sample = 1)
    (hlabel_unit : ∀ sample, 0 ≤ label sample ∧ label sample ≤ 1)
    (hlabel_boolean : ∀ sample, label sample = 0 ∨ label sample = 1)
    (hypotheses : List (Training → ℝ))
    (hhypothesis : ∀ hypothesis ∈ hypotheses, ∀ sample,
      0 ≤ hypothesis sample ∧ hypothesis sample ≤ 1)
    (hvalid : AdaBoostAdmissible state label hypotheses) :
    adaBoostTrainingError state label hypotheses hvalid ≤
        adaBoostTheorem6Factor state label hypotheses hvalid ∧
      adaBoostTheorem6Factor state label hypotheses hvalid =
        Real.exp (-((adaBoostErrors state label hypotheses hvalid).map fun error =>
          Probability.binaryKLDivergence (1 / 2) error).sum) ∧
      Real.exp (-((adaBoostErrors state label hypotheses hvalid).map fun error =>
          Probability.binaryKLDivergence (1 / 2) error).sum) ≤
        Real.exp (-2 * ((adaBoostErrors state label hypotheses hvalid).map fun error =>
          (1 / 2 - error) ^ 2).sum) := by
  exact ⟨adaBoost_training_error_le_theorem6Factor state label hstate_total hlabel_unit
      hlabel_boolean hypotheses hhypothesis hvalid,
    adaBoostTheorem6Factor_eq_exp_neg_binaryKLSum state label hypotheses hvalid,
    exp_neg_binaryKLSum_le_exp_neg_two_sum_squared_edges
      (adaBoostErrors state label hypotheses hvalid)
      (adaBoostErrors_mem_Ioo state label hypotheses hvalid)⟩

/-- Source Eq. (22): the equal-edge Theorem-6 factor has its closed rpow form. -/
theorem equation22_adaBoost_uniform_edge_core
    {Training : Type} [Fintype Training] [DecidableEq Training] [Nonempty Training]
    (state : HedgeWeightState Training) (label : Training → ℝ)
    (hstate_total : ∑ sample, state.weight sample = 1)
    (hlabel_unit : ∀ sample, 0 ≤ label sample ∧ label sample ≤ 1)
    (hlabel_boolean : ∀ sample, label sample = 0 ∨ label sample = 1)
    (hypotheses : List (Training → ℝ))
    (hhypothesis : ∀ hypothesis ∈ hypotheses, ∀ sample,
      0 ≤ hypothesis sample ∧ hypothesis sample ≤ 1)
    (hvalid : AdaBoostAdmissible state label hypotheses)
    (gamma : ℝ) (hgamma_lower : -(1 / 2 : ℝ) < gamma)
    (hgamma_upper : gamma < 1 / 2)
    (huniform : ∀ observed ∈ adaBoostErrors state label hypotheses hvalid,
      observed = 1 / 2 - gamma) :
    adaBoostTrainingError state label hypotheses hvalid ≤
        (1 - 4 * gamma ^ 2) ^ ((hypotheses.length : ℝ) / 2) ∧
      (1 - 4 * gamma ^ 2) ^ ((hypotheses.length : ℝ) / 2) =
        Real.exp (-(hypotheses.length : ℝ) *
          Probability.binaryKLDivergence (1 / 2) (1 / 2 - gamma)) ∧
      Real.exp (-(hypotheses.length : ℝ) *
          Probability.binaryKLDivergence (1 / 2) (1 / 2 - gamma)) ≤
        Real.exp (-2 * (hypotheses.length : ℝ) * gamma ^ 2) := by
  have htheorem6 := theorem6_adaBoost_finite_core state label hstate_total hlabel_unit
    hlabel_boolean hypotheses hhypothesis hvalid
  have hfactor_rpow := adaBoostTheorem6Factor_eq_uniform_edge_rpow
    state label hypotheses hvalid gamma hgamma_lower hgamma_upper huniform
  have hfactor_kl := adaBoostTheorem6Factor_eq_exp_neg_length_mul_binaryKL_of_uniform_error
    state label hypotheses hvalid (1 / 2 - gamma) (by constructor <;> linarith) huniform
  have hsum_edges := list_map_sum_eq_length_mul_of_forall_eq
    (adaBoostErrors state label hypotheses hvalid)
    (fun observed => (1 / 2 - observed) ^ 2) (1 / 2 - gamma) huniform
  have hkl_to_squared := exp_neg_binaryKLSum_le_exp_neg_two_sum_squared_edges
    (adaBoostErrors state label hypotheses hvalid)
    (adaBoostErrors_mem_Ioo state label hypotheses hvalid)
  have hkl_to_squared_uniform :
      Real.exp (-(hypotheses.length : ℝ) *
          Probability.binaryKLDivergence (1 / 2) (1 / 2 - gamma)) ≤
        Real.exp (-2 * (hypotheses.length : ℝ) * gamma ^ 2) := by
    calc
      Real.exp (-(hypotheses.length : ℝ) *
          Probability.binaryKLDivergence (1 / 2) (1 / 2 - gamma)) =
          Real.exp (-((adaBoostErrors state label hypotheses hvalid).map fun error =>
            Probability.binaryKLDivergence (1 / 2) error).sum) := by
            rw [list_map_sum_eq_length_mul_of_forall_eq
              (adaBoostErrors state label hypotheses hvalid)
              (fun observed => Probability.binaryKLDivergence (1 / 2) observed)
              (1 / 2 - gamma) huniform, adaBoostErrors_length]
            congr 1
            ring
      _ ≤ Real.exp (-2 * ((adaBoostErrors state label hypotheses hvalid).map fun error =>
            (1 / 2 - error) ^ 2).sum) := hkl_to_squared
      _ = Real.exp (-2 * (hypotheses.length : ℝ) * gamma ^ 2) := by
        rw [hsum_edges, adaBoostErrors_length]
        congr 1
        ring
  exact ⟨htheorem6.trans_eq hfactor_rpow,
    hfactor_rpow.symm.trans hfactor_kl,
    hkl_to_squared_uniform⟩

/-- Source Eq. (23): its quadratic iteration budget attains the target error. -/
theorem equation23_adaBoost_quadratic_iterations_core
    {Training : Type} [Fintype Training] [DecidableEq Training] [Nonempty Training]
    (state : HedgeWeightState Training) (label : Training → ℝ)
    (hstate_total : ∑ sample, state.weight sample = 1)
    (hlabel_unit : ∀ sample, 0 ≤ label sample ∧ label sample ≤ 1)
    (hlabel_boolean : ∀ sample, label sample = 0 ∨ label sample = 1)
    (hypotheses : List (Training → ℝ))
    (hhypothesis : ∀ hypothesis ∈ hypotheses, ∀ sample,
      0 ≤ hypothesis sample ∧ hypothesis sample ≤ 1)
    (hvalid : AdaBoostAdmissible state label hypotheses)
    (gamma target : ℝ) (hgamma_pos : 0 < gamma) (hgamma_upper : gamma < 1 / 2)
    (htarget_pos : 0 < target) (htarget_lt_one : target < 1)
    (huniform : ∀ observed ∈ adaBoostErrors state label hypotheses hvalid,
      observed = 1 / 2 - gamma)
    :
    Nat.ceil (Real.log (1 / target) /
        Probability.binaryKLDivergence (1 / 2) (1 / 2 - gamma)) ≤
        Nat.ceil (Real.log (1 / target) / (2 * gamma ^ 2)) ∧
      (Nat.ceil (Real.log (1 / target) /
          Probability.binaryKLDivergence (1 / 2) (1 / 2 - gamma)) ≤
          hypotheses.length →
        adaBoostTrainingError state label hypotheses hvalid ≤ target) := by
  have hthreshold := binaryKL_iteration_threshold_le_quadratic_threshold
    hgamma_pos hgamma_upper htarget_pos htarget_lt_one
  constructor
  · exact Nat.ceil_mono hthreshold
  · intro hcount_nat
    have hcount_cast :
        (Nat.ceil (Real.log (1 / target) /
            Probability.binaryKLDivergence (1 / 2) (1 / 2 - gamma)) : ℝ) ≤
          (hypotheses.length : ℝ) := by
      exact_mod_cast hcount_nat
    have hcount : Real.log (1 / target) /
        Probability.binaryKLDivergence (1 / 2) (1 / 2 - gamma) ≤
          (hypotheses.length : ℝ) :=
      (Nat.le_ceil _).trans hcount_cast
    have htheorem6 := theorem6_adaBoost_finite_core state label hstate_total hlabel_unit
      hlabel_boolean hypotheses hhypothesis hvalid
    have hfactor := adaBoostTheorem6Factor_eq_exp_neg_length_mul_binaryKL_of_uniform_error
      state label hypotheses hvalid (1 / 2 - gamma) (by constructor <;> linarith) huniform
    calc
      adaBoostTrainingError state label hypotheses hvalid ≤
          adaBoostTheorem6Factor state label hypotheses hvalid := htheorem6
      _ = Real.exp (-(hypotheses.length : ℝ) *
          Probability.binaryKLDivergence (1 / 2) (1 / 2 - gamma)) := hfactor
      _ ≤ target := exp_neg_nat_mul_binaryKL_le_target_of_iteration_count
        hgamma_pos hgamma_upper htarget_pos htarget_lt_one hypotheses.length hcount

/-- The uniform unit-expert discount calculation in the Appendix proof of Theorem 3 (Eq. (29)). -/
theorem theorem3_uniform_unit_expert_discount_average
    {Coordinate : Type} [Fintype Coordinate] [Nonempty Coordinate]
    (discount : ℝ) (outcome : Coordinate) :
    (∑ expert : Coordinate,
        discount ^ unitCoordinateLoss expert outcome *
          (Fintype.card Coordinate : ℝ)⁻¹) =
      discount * (Fintype.card Coordinate : ℝ)⁻¹ +
        ((Fintype.card Coordinate : ℝ) - 1) * (Fintype.card Coordinate : ℝ)⁻¹ := by
  exact uniform_average_rpow_unitCoordinateLoss discount outcome

/-- The Appendix Eq. (29) average is `1 - (1 - β) / K`. -/
theorem theorem3_uniform_unit_expert_discount_average_eq_one_sub
    {Coordinate : Type} [Fintype Coordinate] [Nonempty Coordinate]
    (discount : ℝ) (outcome : Coordinate) :
    (∑ expert : Coordinate,
        discount ^ unitCoordinateLoss expert outcome *
          (Fintype.card Coordinate : ℝ)⁻¹) =
      1 - (1 - discount) * (Fintype.card Coordinate : ℝ)⁻¹ := by
  rw [theorem3_uniform_unit_expert_discount_average]
  exact vovkUniformUnitExpertMixMass_eq_one_sub discount

/--
The lower logarithmic-denominator estimate used in the Appendix Eq. (31)
calculation for the uniform unit-expert mixture.
-/
theorem theorem3_vovk_denominator_lower
    {Coordinate : Type} [Fintype Coordinate] [Nonempty Coordinate]
    {discount : ℝ} (hdiscount : 0 < discount) (hdiscount_lt_one : discount < 1) :
    1 - discount ≤ (Fintype.card Coordinate : ℝ) *
      -Real.log (vovkUniformUnitExpertMixMass (Coordinate := Coordinate) discount) := by
  exact one_sub_le_card_mul_neg_log_vovkUniformUnitExpertMixMass hdiscount hdiscount_lt_one

/--
The upper logarithmic-denominator estimate used in the Appendix Eq. (31)
calculation for the uniform unit-expert mixture.
-/
theorem theorem3_vovk_denominator_upper
    {Coordinate : Type} [Fintype Coordinate] [Nonempty Coordinate]
    {discount : ℝ} (hdiscount : 0 < discount) (hdiscount_lt_one : discount < 1) :
    (Fintype.card Coordinate : ℝ) *
        -Real.log (vovkUniformUnitExpertMixMass (Coordinate := Coordinate) discount) ≤
      (1 - discount) /
        (1 - (1 - discount) * (Fintype.card Coordinate : ℝ)⁻¹) := by
  exact card_mul_neg_log_vovkUniformUnitExpertMixMass_le hdiscount hdiscount_lt_one

/--
The Appendix Eq. (31) coefficient lower bound.  This is Vovk's one-step
necessary condition specialized to the finite unit-coordinate decision game.
-/
theorem theorem3_vovk_coefficient_lower
    {Coordinate : Type} [Fintype Coordinate] [Nonempty Coordinate]
    {discount coefficient : ℝ} (hdiscount : 0 < discount)
    (hdiscount_lt_one : discount < 1)
    (hcondition : finiteUnitCoordinateVovkCondition (Coordinate := Coordinate)
      discount coefficient) :
    -Real.log discount /
        ((Fintype.card Coordinate : ℝ) *
          -Real.log (vovkUniformUnitExpertMixMass (Coordinate := Coordinate) discount)) ≤
      coefficient := by
  exact finiteUnitCoordinateVovkCondition_coefficient_lower hdiscount hdiscount_lt_one
    hcondition

/--
The finite-simplex calculation in the Appendix proof of Theorem 3 (Eq. (30)).
For the source decision space of probability vectors, some unit-vector outcome
always has loss at least the uniform coordinate mass; the uniform decision
attains that value exactly.

Together with Eq. (29), this provides the finite decision-game calculations
used by the subsequent lower-bound argument.
-/
theorem theorem3_simplex_coordinate_lower_core
    {Coordinate : Type} [Fintype Coordinate] [Nonempty Coordinate]
    (mass : Coordinate → ℝ) (hmass : FiniteProbabilitySimplex mass) :
    (Fintype.card Coordinate : ℝ)⁻¹ ≤ finiteMax mass ∧
      finiteMax (fun _coordinate : Coordinate => (Fintype.card Coordinate : ℝ)⁻¹) =
        (Fintype.card Coordinate : ℝ)⁻¹ := by
  exact ⟨finiteProbabilitySimplex_inv_card_le_finiteMax mass hmass,
    finiteMax_uniformProbabilityMass⟩

/--
The one-round allocation-to-decision-game bridge in the Appendix proof of
Theorem 3: mixing the expert decisions by the allocation gives a valid simplex
decision and preserves the mixture loss exactly.
-/
theorem theorem3_allocation_to_decision_round_core
    {Expert Coordinate : Type} [Fintype Expert] [Fintype Coordinate]
    (round : UnitCoordinateAllocationRound Expert Coordinate) :
    FiniteProbabilitySimplex round.learnerDecision ∧
      (∀ expert : Expert,
        0 ≤ unitCoordinateDecisionLoss (round.expertDecision expert) round.outcome ∧
          unitCoordinateDecisionLoss (round.expertDecision expert) round.outcome ≤ 1) ∧
      round.learnerLoss = round.allocationLoss := by
  exact ⟨round.learnerDecision_mem, round.expertLoss_mem_Icc,
    round.learnerLoss_eq_allocationLoss⟩

/-- The allocation-to-decision loss identity in the Appendix holds over every finite horizon. -/
theorem theorem3_allocation_to_decision_cumulative_core
    {Expert Coordinate : Type} [Fintype Expert] [Fintype Coordinate]
    (rounds : List (UnitCoordinateAllocationRound Expert Coordinate)) :
    unitCoordinateAllocationCumulativeLearnerLoss rounds =
      unitCoordinateAllocationCumulativeLoss rounds := by
  exact unitCoordinateAllocationCumulativeLearnerLoss_eq_allocation rounds

/--
The Appendix reduction transports an arbitrary history-dependent allocation
policy's source `(c,a)` guarantee to the finite unit-coordinate decision game.
-/
theorem theorem3_allocation_policy_to_decision_core
    {Expert Coordinate : Type} [Fintype Expert] [Fintype Coordinate] [Nonempty Expert]
    (policy : FiniteAllocationPolicy Expert) (hpolicy : FiniteAllocationPolicyAdmissible policy)
    (c a : ℝ) (hbound : FiniteAllocationPolicyBound policy c a) :
    AllocationPolicyUnitCoordinateDecisionBound (Coordinate := Coordinate) policy c a := by
  exact finiteAllocationPolicyBound_to_unitCoordinateDecisionBound policy hpolicy c a hbound

/--
The global allocation premise of Theorem 3 supplies the corresponding finite
unit-coordinate decision-game premise with the same two constants.
-/
theorem theorem3_global_allocation_to_decision_game_core
    {Coordinate : Type} [Fintype Coordinate] (c a : ℝ)
    (hbound : globalFiniteAllocationPolicyBounded c a) :
    finiteUnitCoordinateGameBounded Coordinate c a := by
  exact globalFiniteAllocationPolicyBounded_to_finiteUnitCoordinateGameBounded c a hbound

/--
The deterministic game-tree portion of Vovk's global necessary-direction
argument: below the Appendix Eq. (31) coefficient, the adaptive uniform
outcome selector forces its strict cumulative lower floor against any policy.
The separate iid expert-table construction remains the final Section-6 step.
-/
theorem theorem3_vovk_uniform_global_game_lower_core
    {Expert Coordinate : Type} [Fintype Expert] [Fintype Coordinate]
    [Nonempty Expert] [Nonempty Coordinate]
    {discount coefficient : ℝ} (hdiscount : 0 < discount)
    (hdiscount_lt_one : discount < 1)
    (hcoefficient_lt : coefficient < (-Real.log discount) /
      ((Fintype.card Coordinate : ℝ) *
        -Real.log (vovkUniformUnitExpertMixMass (Coordinate := Coordinate) discount)))
    (policy : UnitCoordinateDecisionPolicy Expert Coordinate)
    (hpolicy : UnitCoordinateDecisionPolicyAdmissible policy)
    (table : UnitCoordinatePureExpertTable Expert Coordinate)
    (horizon : ℕ) (hpositive : 0 < horizon) :
    (horizon : ℝ) *
        (coefficient *
          (Real.log (vovkUniformUnitExpertMixMass (Coordinate := Coordinate) discount) /
            Real.log discount)) <
      unitCoordinateDecisionPolicyCumulativeLoss policy
        (unitCoordinateVovkRounds policy
          (uniformUnitCoordinateVovkOutcomeSelector hdiscount hdiscount_lt_one hcoefficient_lt)
          table horizon) := by
  exact uniformUnitCoordinateVovkRounds_cumulativeLoss_gt hdiscount hdiscount_lt_one
    hcoefficient_lt policy hpolicy table horizon hpositive

/--
Freund--Schapire (1997), Theorem 3, necessary direction.  Any globally
available finite-expert allocation policy family satisfying the source
`(c,a)` regret template must meet Vovk's tradeoff for every `0 < β < 1`.

The proof uses the Appendix allocation-to-decision reduction, the finite
unit-coordinate Section-6 game contradiction, and then takes the number of
coordinates to infinity.  The finite construction begins at two coordinates,
which is the nontrivial case needed for the iid Cramer witness.
-/
theorem theorem3_global_allocation_lower_tradeoff
    {discount c a : ℝ} (hdiscount : 0 < discount) (hdiscount_lt_one : discount < 1)
    (hc_pos : 0 < c) (ha_pos : 0 < a)
    (hbounded : globalFiniteAllocationPolicyBounded c a) :
    (-Real.log discount) / (1 - discount) ≤ c ∨
      1 / (1 - discount) ≤ a := by
  apply vovkFiniteAlternative_limit_fin_succ_succ hdiscount hdiscount_lt_one
  intro n
  have hfinite := finiteUnitCoordinateGameBounded_vovk_alternative
    (Coordinate := Fin ((n + 1) + 1)) hdiscount hdiscount_lt_one hc_pos.le ha_pos
    (theorem3_global_allocation_to_decision_game_core
      (Coordinate := Fin ((n + 1) + 1)) c a hbounded)
  simpa using hfinite

/--
Source Theorem 8, proved through the finite-trace Baum--Haussler route.  The
reusable library theorem includes the direct affine-threshold VC proof, the
two-layer trace factorization, entropy compression, and the numerical
`2(d+1)(T+1) log₂(e(T+1))` calculation.
-/
theorem theorem8_weighted_threshold_vc_core
    {X : Type*} (width d : ℕ) (concepts : Set (BinaryClassifier X))
    (hd : 2 ≤ d)
    (hvc_exact : VCDimensionAtMost concepts d ∧
      ∃ sample : Finset X, binaryTraceVCDimension concepts sample = d) :
    ∀ sample : Finset X,
      (binaryTraceVCDimension
        (binaryThresholdCombinationClass concepts width) sample : ℝ) ≤
        sourceThresholdCombinationVCBound width d := by
  intro sample
  by_cases hwidth : 0 < width
  · exact vcDimension_thresholdCombinationClass_le_source_theorem8
      concepts hwidth hd hvc_exact.1 sample
  · have hzero : width = 0 := by omega
    subst width
    have hdim := binaryTraceVCDimension_thresholdCombinationClass_zero_le_one concepts sample
    have hdim_real :
        (binaryTraceVCDimension (binaryThresholdCombinationClass concepts 0) sample : ℝ) ≤ 1 := by
      exact_mod_cast hdim
    exact hdim_real.trans (sourceThresholdCombinationVCBound_zero_ge_one d hd)

/-- The finite source-model conclusion of Freund--Schapire Theorem 9. -/
theorem theorem9_soft_adaBoost_error_core
    {Training : Type} [Fintype Training] [DecidableEq Training] [Nonempty Training]
    (state : HedgeWeightState Training) (label : Training → ℝ)
    (hstate_total : ∑ sample, state.weight sample = 1)
    (hlabel_boolean : ∀ sample, label sample = 0 ∨ label sample = 1)
    (hypotheses : List (Training → ℝ))
    (hhypothesis : ∀ hypothesis ∈ hypotheses, ∀ sample,
      0 ≤ hypothesis sample ∧ hypothesis sample ≤ 1)
    (hvalid : AdaBoostAdmissible state label hypotheses)
    (hweight_ne : adaBoostVoteWeightSum state label hypotheses hvalid ≠ 0)
    (hnormalized : ∀ sample,
      0 ≤ adaBoostNormalizedVote state label hypotheses hvalid sample ∧
        adaBoostNormalizedVote state label hypotheses hvalid sample ≤ 1)
    (threshold : ℝ → ℝ)
    (hthreshold : AdaBoostSoftThreshold state label hypotheses hvalid threshold) :
    adaBoostSoftTrainingError state label hypotheses hvalid threshold ≤
      adaBoostTheorem9Factor state label hypotheses hvalid := by
  exact adaBoost_softTrainingError_le_theorem9Factor state label hstate_total hlabel_boolean
    hypotheses hhypothesis hvalid hweight_ne hnormalized threshold hthreshold

/-- The finite source-model conclusion of Freund--Schapire (1997), Theorem 10. -/
theorem theorem10_adaBoostM1_error_core
    {Training Label : Type}
    [Fintype Training] [DecidableEq Training] [Nonempty Training]
    [Fintype Label] [Nonempty Label] [DecidableEq Label]
    (state : HedgeWeightState Training) (label : Training → Label)
    (hstate_total : ∑ sample, state.weight sample = 1)
    (hypotheses : List (Training → Label))
    (hvalid : AdaBoostM1Admissible state label hypotheses)
    (hweak : ∀ error ∈ adaBoostM1Errors state label hypotheses hvalid, error ≤ 1 / 2) :
    adaBoostM1TrainingError state label hypotheses hvalid ≤
      adaBoostM1Theorem10Factor state label hypotheses hvalid := by
  exact adaBoostM1_training_error_le_theorem10Factor state label hstate_total hypotheses hvalid hweak

/-- The finite source-model conclusion of Freund--Schapire (1997), Theorem 11. -/
theorem theorem11_adaBoostM2_error_core
    {Training Label : Type}
    [Fintype Training] [DecidableEq Training] [Nonempty Training]
    [Fintype Label] [DecidableEq Label] [Nonempty Label]
    (label : Training → Label) (exampleWeight : Training → ℝ)
    (state : HedgeWeightState (AdaBoostM2Instance Training Label label))
    (hexample_nonneg : ∀ sample, 0 ≤ exampleWeight sample)
    (hexample_total : ∑ sample, exampleWeight sample = 1)
    (hlabels : 1 < Fintype.card Label)
    (hinitial : ∀ pair : AdaBoostM2Instance Training Label label,
      state.weight pair = exampleWeight pair.1.1 /
        ((Fintype.card Label - 1 : ℕ) : ℝ))
    (hstate_total : ∑ pair, state.weight pair = 1)
    (hypotheses : List (Training → Label → ℝ))
    (hhypothesis : ∀ hypothesis ∈ hypotheses, ∀ sample candidate,
      0 ≤ hypothesis sample candidate ∧ hypothesis sample candidate ≤ 1) :
    letI : Nonempty (AdaBoostM2Instance Training Label label) :=
      adaBoostM2Instance_nonempty label hlabels
    ∀ hvalid : AdaBoostM2Admissible label state hypotheses,
      adaBoostM2TrainingError label exampleWeight state hypotheses hvalid ≤
        adaBoostM2Theorem11Factor label state hypotheses hvalid := by
  classical
  letI : Nonempty (AdaBoostM2Instance Training Label label) :=
    adaBoostM2Instance_nonempty label hlabels
  intro hvalid
  exact adaBoostM2_training_error_le_theorem11Factor label exampleWeight state hstate_total
    hlabels hinitial hypotheses hhypothesis hvalid

/-- The finite source-model conclusion of Freund--Schapire (1997), Theorem 12. -/
theorem theorem12_adaBoostR_error_core
    {Training : Type} [Fintype Training]
    (exampleWeight : Training → ℝ) (label : Training → ℝ)
    (hexample_nonneg : ∀ sample, 0 ≤ exampleWeight sample)
    (hexample_total : ∑ sample, exampleWeight sample = 1)
    (hlabel : ∀ sample, 0 ≤ label sample ∧ label sample ≤ 1)
    (hypotheses : List (Training → ℝ))
    (hhypothesis : ∀ hypothesis ∈ hypotheses, ∀ sample,
      0 ≤ hypothesis sample ∧ hypothesis sample ≤ 1)
    (hvalid : AdaBoostRAdmissible (adaBoostRBaseState exampleWeight label
      hexample_nonneg hexample_total hlabel) label hypotheses) :
    adaBoostRMeanSquaredError exampleWeight label
      (adaBoostRFinalHypothesis
        (adaBoostRBaseState exampleWeight label hexample_nonneg hexample_total hlabel)
        label hypotheses hhypothesis hvalid) ≤
      adaBoostRTheorem12Factor
        (adaBoostRBaseState exampleWeight label hexample_nonneg hexample_total hlabel)
        label hypotheses hvalid := by
  classical
  exact adaBoostR_meanSquaredError_le_theorem12Factor exampleWeight label
    hexample_nonneg hexample_total hlabel hypotheses hhypothesis hvalid

end FreundSchapire1997Hedge
