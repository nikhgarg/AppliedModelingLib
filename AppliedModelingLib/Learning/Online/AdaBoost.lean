import AppliedModelingLib.Learning.Online.Hedge
import AppliedModelingLib.Foundations.Probability.BinaryKL

/-!
# Finite adaptive boosting updates

This module isolates the variable-discount multiplicative update in Figure 2
of Freund--Schapire (1997).  It is intentionally stated for finite training
sets and real-valued labels and weak hypotheses in `[0, 1]`: this is the
mathematical model used by the paper before its Boolean-classification,
multiclass, and regression reductions.

The source writes `β_t = ε_t / (1 - ε_t)`.  Consequently the literal update is
well-defined over the reals only in the interior regime `0 < ε_t < 1`; public
interfaces in this file expose that premise instead of silently assigning a
value at the endpoints.
-/

namespace AppliedModelingLib
namespace Learning
namespace Online

open scoped BigOperators

/-- A positive-discount multiplicative-update round, allowing the discount to vary by round. -/
structure AdaptiveHedgeRound (Action : Type*) where
  loss : Action → ℝ
  discount : ℝ
  discount_pos : 0 < discount

/-- Apply one variable-discount multiplicative update. -/
noncomputable def adaptiveHedgeWeightStateStep
    {Action : Type*} [Fintype Action] [Nonempty Action]
    (state : HedgeWeightState Action) (round : AdaptiveHedgeRound Action) :
    HedgeWeightState Action :=
  hedgeWeightStateStep state round.loss round.discount round.discount_pos

/-- Execute a finite list of variable-discount multiplicative updates. -/
noncomputable def adaptiveHedgeWeightStateRun
    {Action : Type*} [Fintype Action] [Nonempty Action]
    (state : HedgeWeightState Action) : List (AdaptiveHedgeRound Action) →
      HedgeWeightState Action
  | [] => state
  | round :: remaining =>
      adaptiveHedgeWeightStateRun (adaptiveHedgeWeightStateStep state round) remaining

/-- The exact normalized multiplicative factor accumulated by a variable-discount run. -/
noncomputable def adaptiveHedgePotential
    {Action : Type*} [Fintype Action] [Nonempty Action] :
    HedgeWeightState Action → List (AdaptiveHedgeRound Action) → ℝ
  | _, [] => 1
  | state, round :: remaining =>
      state.expectation (fun action => round.discount ^ (round.loss action)) *
        adaptiveHedgePotential (adaptiveHedgeWeightStateStep state round) remaining

/-- The source's linear chord upper factor, accumulated over an adaptive run. -/
noncomputable def adaptiveHedgeLinearPotential
    {Action : Type*} [Fintype Action] [Nonempty Action] :
    HedgeWeightState Action → List (AdaptiveHedgeRound Action) → ℝ
  | _, [] => 1
  | state, round :: remaining =>
      (1 - (1 - round.discount) * state.expectation round.loss) *
        adaptiveHedgeLinearPotential (adaptiveHedgeWeightStateStep state round) remaining

/-- Every exact normalized factor in a positive-discount adaptive run is positive. -/
theorem adaptiveHedgePotential_pos
    {Action : Type*} [Fintype Action] [DecidableEq Action] [Nonempty Action]
    (state : HedgeWeightState Action) (rounds : List (AdaptiveHedgeRound Action)) :
    0 < adaptiveHedgePotential state rounds := by
  induction rounds generalizing state with
  | nil => simp [adaptiveHedgePotential]
  | cons round remaining ih =>
      rw [adaptiveHedgePotential]
      exact mul_pos
        (by
          unfold HedgeWeightState.expectation
          exact pmfExp_pos_of_support_forall_pos state.policy _ fun action _ =>
            Real.rpow_pos_of_pos round.discount_pos _)
        (ih (adaptiveHedgeWeightStateStep state round))

/--
The total unnormalized weight after a variable-discount run equals its initial
mass times the product of the exact normalized one-step potentials.
-/
theorem adaptiveHedgeWeightStateRun_total
    {Action : Type*} [Fintype Action] [Nonempty Action]
    (state : HedgeWeightState Action) (rounds : List (AdaptiveHedgeRound Action)) :
    (∑ action, (adaptiveHedgeWeightStateRun state rounds).weight action) =
      (∑ action, state.weight action) * adaptiveHedgePotential state rounds := by
  induction rounds generalizing state with
  | nil => simp [adaptiveHedgeWeightStateRun, adaptiveHedgePotential]
  | cons round remaining ih =>
      rw [adaptiveHedgeWeightStateRun, ih]
      change
        (∑ action,
          (hedgeWeightStateStep state round.loss round.discount round.discount_pos).weight action) *
            adaptiveHedgePotential
              (hedgeWeightStateStep state round.loss round.discount round.discount_pos) remaining =
          (∑ action, state.weight action) *
            (state.expectation (fun action => round.discount ^ (round.loss action)) *
              adaptiveHedgePotential
                (hedgeWeightStateStep state round.loss round.discount round.discount_pos) remaining)
      rw [hedgeWeightStateStep_total]
      ring

/--
Each source weight after a variable-discount run is its initial weight times
the product of its per-round multiplicative factors.
-/
theorem adaptiveHedgeWeightStateRun_weight
    {Action : Type*} [Fintype Action] [Nonempty Action]
    (state : HedgeWeightState Action) (rounds : List (AdaptiveHedgeRound Action))
    (action : Action) :
    (adaptiveHedgeWeightStateRun state rounds).weight action =
      state.weight action *
        (rounds.map fun round => round.discount ^ (round.loss action)).prod := by
  induction rounds generalizing state with
  | nil => simp [adaptiveHedgeWeightStateRun]
  | cons round remaining ih =>
      rw [adaptiveHedgeWeightStateRun, ih]
      simp only [adaptiveHedgeWeightStateStep, hedgeWeightStateStep,
        List.map_cons, List.prod_cons]
      ring

/--
For source losses in `[0,1]`, the exact variable-discount potential is at
most the product of its linear chord factors.
-/
theorem adaptiveHedgePotential_le_linear
    {Action : Type*} [Fintype Action] [DecidableEq Action] [Nonempty Action]
    (state : HedgeWeightState Action) (rounds : List (AdaptiveHedgeRound Action))
    (hloss : ∀ round ∈ rounds, ∀ action,
      0 ≤ round.loss action ∧ round.loss action ≤ 1) :
    adaptiveHedgePotential state rounds ≤ adaptiveHedgeLinearPotential state rounds := by
  induction rounds generalizing state with
  | nil => simp [adaptiveHedgePotential, adaptiveHedgeLinearPotential]
  | cons round remaining ih =>
      have hround : ∀ action, 0 ≤ round.loss action ∧ round.loss action ≤ 1 :=
        hloss round (by simp)
      have hremaining : ∀ next ∈ remaining, ∀ action,
          0 ≤ next.loss action ∧ next.loss action ≤ 1 := by
        intro next hnext action
        exact hloss next (by simp [hnext]) action
      have hhead :
          state.expectation (fun action => round.discount ^ (round.loss action)) ≤
            1 - (1 - round.discount) * state.expectation round.loss :=
        hedge_one_step_potential_upper_of_pos state.policy round.loss round.discount
          round.discount_pos (fun action => (hround action).1)
          (fun action => (hround action).2)
      have htail := ih (adaptiveHedgeWeightStateStep state round) hremaining
      have htail_nonneg :
          0 ≤ adaptiveHedgePotential (adaptiveHedgeWeightStateStep state round) remaining :=
        (adaptiveHedgePotential_pos (adaptiveHedgeWeightStateStep state round) remaining).le
      have hhead_pos :
          0 < state.expectation (fun action => round.discount ^ (round.loss action)) := by
        unfold HedgeWeightState.expectation
        exact pmfExp_pos_of_support_forall_pos state.policy _ fun action _ =>
          Real.rpow_pos_of_pos round.discount_pos _
      have hlinear_nonneg :
          0 ≤ 1 - (1 - round.discount) * state.expectation round.loss :=
        hhead_pos.le.trans hhead
      change
        state.expectation (fun action => round.discount ^ (round.loss action)) *
            adaptiveHedgePotential (adaptiveHedgeWeightStateStep state round) remaining ≤
          (1 - (1 - round.discount) * state.expectation round.loss) *
            adaptiveHedgeLinearPotential (adaptiveHedgeWeightStateStep state round) remaining
      calc
        state.expectation (fun action => round.discount ^ (round.loss action)) *
            adaptiveHedgePotential (adaptiveHedgeWeightStateStep state round) remaining ≤
            (1 - (1 - round.discount) * state.expectation round.loss) *
              adaptiveHedgePotential (adaptiveHedgeWeightStateStep state round) remaining :=
          mul_le_mul_of_nonneg_right hhead htail_nonneg
        _ ≤ (1 - (1 - round.discount) * state.expectation round.loss) *
              adaptiveHedgeLinearPotential (adaptiveHedgeWeightStateStep state round) remaining :=
          mul_le_mul_of_nonneg_left htail hlinear_nonneg

/-- The finite variable-discount total-mass bound obtained by multiplying the chord factors. -/
theorem adaptiveHedgeWeightStateRun_total_le_linear
    {Action : Type*} [Fintype Action] [DecidableEq Action] [Nonempty Action]
    (state : HedgeWeightState Action) (rounds : List (AdaptiveHedgeRound Action))
    (hloss : ∀ round ∈ rounds, ∀ action,
      0 ≤ round.loss action ∧ round.loss action ≤ 1) :
    (∑ action, (adaptiveHedgeWeightStateRun state rounds).weight action) ≤
      (∑ action, state.weight action) * adaptiveHedgeLinearPotential state rounds := by
  rw [adaptiveHedgeWeightStateRun_total]
  exact mul_le_mul_of_nonneg_left
    (adaptiveHedgePotential_le_linear state rounds hloss)
    state.total_pos.le

/-- The reversed loss used in the AdaBoost weight update of Figure 2. -/
def adaBoostLoss {Training : Type*}
    (label hypothesis : Training → ℝ) : Training → ℝ :=
  fun sample => 1 - |hypothesis sample - label sample|

/-- The weighted absolute prediction error in Step 3 of Figure 2. -/
noncomputable def adaBoostError {Training : Type*} [Fintype Training]
    (state : HedgeWeightState Training) (label hypothesis : Training → ℝ) : ℝ :=
  state.expectation fun sample => |hypothesis sample - label sample|

/-- The adaptive source update factor `β = ε / (1 - ε)`. -/
noncomputable def adaBoostDiscount (error : ℝ) : ℝ :=
  error / (1 - error)

/--
An AdaBoost round's unnormalized update, exactly as in Step 5 of Figure 2.
The explicit interior-error hypothesis reflects the domain of the source's
displayed formula for `β`.
-/
noncomputable def adaBoostStep
    {Training : Type*} [Fintype Training] [Nonempty Training]
    (state : HedgeWeightState Training) (label hypothesis : Training → ℝ)
    (herror : 0 < adaBoostError state label hypothesis ∧
      adaBoostError state label hypothesis < 1) :
    HedgeWeightState Training :=
  hedgeWeightStateStep state (adaBoostLoss label hypothesis)
    (adaBoostDiscount (adaBoostError state label hypothesis))
    (by
      unfold adaBoostDiscount
      exact div_pos herror.1 (sub_pos.mpr herror.2))

/--
The recursively generated errors of a finite AdaBoost run are all in the
interior domain of Figure 2's displayed adaptive update.
-/
def AdaBoostAdmissible
    {Training : Type*} [Fintype Training] [Nonempty Training]
    (state : HedgeWeightState Training) (label : Training → ℝ) :
    List (Training → ℝ) → Prop
  | [] => True
  | hypothesis :: remaining =>
      ∃ herror : 0 < adaBoostError state label hypothesis ∧
          adaBoostError state label hypothesis < 1,
        AdaBoostAdmissible (adaBoostStep state label hypothesis herror) label remaining

/-- Execute Figure 2 on a finite list of weak hypotheses. -/
noncomputable def adaBoostRun
    {Training : Type*} [Fintype Training] [Nonempty Training]
    (state : HedgeWeightState Training) (label : Training → ℝ) :
    (hypotheses : List (Training → ℝ)) →
      AdaBoostAdmissible state label hypotheses → HedgeWeightState Training
  | [], _ => state
  | hypothesis :: remaining, hvalid =>
      adaBoostRun
        (adaBoostStep state label hypothesis (Classical.choose hvalid)) label remaining
        (Classical.choose_spec hvalid)

/-- Extract the Step-3 errors encountered along a finite certified AdaBoost run. -/
noncomputable def adaBoostErrors
    {Training : Type*} [Fintype Training] [Nonempty Training]
    (state : HedgeWeightState Training) (label : Training → ℝ) :
    (hypotheses : List (Training → ℝ)) →
      AdaBoostAdmissible state label hypotheses → List ℝ
  | [], _ => []
  | hypothesis :: remaining, hvalid =>
      adaBoostError state label hypothesis ::
        adaBoostErrors
          (adaBoostStep state label hypothesis (Classical.choose hvalid)) label remaining
          (Classical.choose_spec hvalid)

/-- The final-vote coefficient `α_t = log (1 / β_t)` in Figure 2. -/
noncomputable def adaBoostVoteWeight (error : ℝ) : ℝ :=
  Real.log (1 / adaBoostDiscount error)

/-- The unthresholded weighted vote of Figure 2. -/
noncomputable def adaBoostVote
    {Training : Type*} [Fintype Training] [Nonempty Training]
    (state : HedgeWeightState Training) (label : Training → ℝ) :
    (hypotheses : List (Training → ℝ)) →
      AdaBoostAdmissible state label hypotheses → Training → ℝ
  | [], _, _ => 0
  | hypothesis :: remaining, hvalid, sample =>
      adaBoostVoteWeight (adaBoostError state label hypothesis) * hypothesis sample +
        adaBoostVote
          (adaBoostStep state label hypothesis (Classical.choose hvalid)) label remaining
          (Classical.choose_spec hvalid) sample

/-- The sum of the final-vote coefficients in Figure 2. -/
noncomputable def adaBoostVoteWeightSum
    {Training : Type*} [Fintype Training] [Nonempty Training]
    (state : HedgeWeightState Training) (label : Training → ℝ) :
    (hypotheses : List (Training → ℝ)) →
      AdaBoostAdmissible state label hypotheses → ℝ
  | [], _ => 0
  | hypothesis :: remaining, hvalid =>
      adaBoostVoteWeight (adaBoostError state label hypothesis) +
        adaBoostVoteWeightSum
          (adaBoostStep state label hypothesis (Classical.choose hvalid)) label remaining
          (Classical.choose_spec hvalid)

/-- The final-vote weighted absolute error at one training sample. -/
noncomputable def adaBoostWeightedAbsoluteError
    {Training : Type*} [Fintype Training] [Nonempty Training]
    (state : HedgeWeightState Training) (label : Training → ℝ) :
    (hypotheses : List (Training → ℝ)) →
      AdaBoostAdmissible state label hypotheses → Training → ℝ
  | [], _, _ => 0
  | hypothesis :: remaining, hvalid, sample =>
      adaBoostVoteWeight (adaBoostError state label hypothesis) *
          |hypothesis sample - label sample| +
        adaBoostWeightedAbsoluteError
          (adaBoostStep state label hypothesis (Classical.choose hvalid)) label remaining
          (Classical.choose_spec hvalid) sample

/-- The Boolean final hypothesis output by Figure 2's weighted threshold. -/
noncomputable def adaBoostFinalHypothesis
    {Training : Type*} [Fintype Training] [Nonempty Training]
    (state : HedgeWeightState Training) (label : Training → ℝ)
    (hypotheses : List (Training → ℝ))
    (hvalid : AdaBoostAdmissible state label hypotheses) : Training → ℝ :=
  fun sample =>
    if adaBoostVoteWeightSum state label hypotheses hvalid / 2 ≤
        adaBoostVote state label hypotheses hvalid sample then 1 else 0

/-- The multiplicative factor accumulated by one training sample in a finite run. -/
noncomputable def adaBoostSampleWeightFactor
    {Training : Type*} [Fintype Training] [Nonempty Training]
    (state : HedgeWeightState Training) (label : Training → ℝ) :
    (hypotheses : List (Training → ℝ)) →
      AdaBoostAdmissible state label hypotheses → Training → ℝ
  | [], _, _ => 1
  | hypothesis :: remaining, hvalid, sample =>
      adaBoostDiscount (adaBoostError state label hypothesis) ^
          (1 - |hypothesis sample - label sample|) *
        adaBoostSampleWeightFactor
          (adaBoostStep state label hypothesis (Classical.choose hvalid)) label remaining
          (Classical.choose_spec hvalid) sample

/-- The logarithm of the sample's accumulated multiplicative factor. -/
noncomputable def adaBoostLogSampleWeightFactor
    {Training : Type*} [Fintype Training] [Nonempty Training]
    (state : HedgeWeightState Training) (label : Training → ℝ) :
    (hypotheses : List (Training → ℝ)) →
      AdaBoostAdmissible state label hypotheses → Training → ℝ
  | [], _, _ => 0
  | hypothesis :: remaining, hvalid, sample =>
      Real.log (adaBoostDiscount (adaBoostError state label hypothesis)) *
          (1 - |hypothesis sample - label sample|) +
        adaBoostLogSampleWeightFactor
          (adaBoostStep state label hypothesis (Classical.choose hvalid)) label remaining
          (Classical.choose_spec hvalid) sample

/-- The product of the source half-exponent factors `β_t^(1/2)`. -/
noncomputable def adaBoostHalfDiscountFactor
    {Training : Type*} [Fintype Training] [Nonempty Training]
    (state : HedgeWeightState Training) (label : Training → ℝ) :
    (hypotheses : List (Training → ℝ)) →
      AdaBoostAdmissible state label hypotheses → ℝ
  | [], _ => 1
  | hypothesis :: remaining, hvalid =>
      adaBoostDiscount (adaBoostError state label hypothesis) ^ ((1 : ℝ) / 2) *
        adaBoostHalfDiscountFactor
          (adaBoostStep state label hypothesis (Classical.choose hvalid)) label remaining
          (Classical.choose_spec hvalid)

/-- The exact per-sample product form of the Figure-2 weight update. -/
theorem adaBoostRun_weight
    {Training : Type*} [Fintype Training] [Nonempty Training]
    (state : HedgeWeightState Training) (label : Training → ℝ)
    (hypotheses : List (Training → ℝ))
    (hvalid : AdaBoostAdmissible state label hypotheses)
    (sample : Training) :
    (adaBoostRun state label hypotheses hvalid).weight sample =
      state.weight sample * adaBoostSampleWeightFactor state label hypotheses hvalid sample := by
  induction hypotheses generalizing state with
  | nil => simp [adaBoostRun, adaBoostSampleWeightFactor]
  | cons hypothesis remaining ih =>
      let herror := Classical.choose hvalid
      have hrest : AdaBoostAdmissible
          (adaBoostStep state label hypothesis herror) label remaining :=
        Classical.choose_spec hvalid
      have htail := ih (state := adaBoostStep state label hypothesis herror) hrest
      change
        (adaBoostRun (adaBoostStep state label hypothesis herror) label remaining hrest).weight sample =
          state.weight sample *
            (adaBoostDiscount (adaBoostError state label hypothesis) ^
              (1 - |hypothesis sample - label sample|) *
              adaBoostSampleWeightFactor
                (adaBoostStep state label hypothesis herror) label remaining hrest sample)
      rw [htail]
      simp only [adaBoostStep, hedgeWeightStateStep, adaBoostLoss]
      ring

/-- The sample weight factor is the exponential of its accumulated log factor. -/
theorem adaBoostSampleWeightFactor_eq_exp_log
    {Training : Type*} [Fintype Training] [Nonempty Training]
    (state : HedgeWeightState Training) (label : Training → ℝ)
    (hypotheses : List (Training → ℝ))
    (hvalid : AdaBoostAdmissible state label hypotheses)
    (sample : Training) :
    adaBoostSampleWeightFactor state label hypotheses hvalid sample =
      Real.exp (adaBoostLogSampleWeightFactor state label hypotheses hvalid sample) := by
  induction hypotheses generalizing state with
  | nil => simp [adaBoostSampleWeightFactor, adaBoostLogSampleWeightFactor]
  | cons hypothesis remaining ih =>
      let herror := Classical.choose hvalid
      have hrest : AdaBoostAdmissible
          (adaBoostStep state label hypothesis herror) label remaining :=
        Classical.choose_spec hvalid
      have hdiscount : 0 < adaBoostDiscount (adaBoostError state label hypothesis) := by
        unfold adaBoostDiscount
        exact div_pos herror.1 (sub_pos.mpr herror.2)
      have htail := ih (state := adaBoostStep state label hypothesis herror) hrest
      change
        adaBoostDiscount (adaBoostError state label hypothesis) ^
            (1 - |hypothesis sample - label sample|) *
            adaBoostSampleWeightFactor
              (adaBoostStep state label hypothesis herror) label remaining hrest sample =
          Real.exp
            (Real.log (adaBoostDiscount (adaBoostError state label hypothesis)) *
                (1 - |hypothesis sample - label sample|) +
              adaBoostLogSampleWeightFactor
                (adaBoostStep state label hypothesis herror) label remaining hrest sample)
      rw [Real.rpow_def_of_pos hdiscount, htail, ← Real.exp_add]

/--
The sample's accumulated log factor is weighted absolute error minus total
vote weight.  Together with Eq. (17), this is the logarithmic form of the
source proof's Eq. (18).
-/
theorem adaBoostLogSampleWeightFactor_eq_weightedAbsoluteError_sub_weightSum
    {Training : Type*} [Fintype Training] [Nonempty Training]
    (state : HedgeWeightState Training) (label : Training → ℝ)
    (hypotheses : List (Training → ℝ))
    (hvalid : AdaBoostAdmissible state label hypotheses)
    (sample : Training) :
    adaBoostLogSampleWeightFactor state label hypotheses hvalid sample =
      adaBoostWeightedAbsoluteError state label hypotheses hvalid sample -
        adaBoostVoteWeightSum state label hypotheses hvalid := by
  induction hypotheses generalizing state with
  | nil => simp [adaBoostLogSampleWeightFactor, adaBoostWeightedAbsoluteError,
      adaBoostVoteWeightSum]
  | cons hypothesis remaining ih =>
      let herror := Classical.choose hvalid
      have hrest : AdaBoostAdmissible
          (adaBoostStep state label hypothesis herror) label remaining :=
        Classical.choose_spec hvalid
      have htail := ih (state := adaBoostStep state label hypothesis herror) hrest
      change
        Real.log (adaBoostDiscount (adaBoostError state label hypothesis)) *
            (1 - |hypothesis sample - label sample|) +
            adaBoostLogSampleWeightFactor
              (adaBoostStep state label hypothesis herror) label remaining hrest sample =
          (adaBoostVoteWeight (adaBoostError state label hypothesis) *
              |hypothesis sample - label sample| +
            adaBoostWeightedAbsoluteError
              (adaBoostStep state label hypothesis herror) label remaining hrest sample) -
            (adaBoostVoteWeight (adaBoostError state label hypothesis) +
              adaBoostVoteWeightSum
                (adaBoostStep state label hypothesis herror) label remaining hrest)
      rw [htail]
      simp only [adaBoostVoteWeight, one_div, Real.log_inv]
      ring

/-- The product of `β_t^(1/2)` factors is the exponential of half the negative vote weight. -/
theorem adaBoostHalfDiscountFactor_eq_exp_neg_half_weightSum
    {Training : Type*} [Fintype Training] [Nonempty Training]
    (state : HedgeWeightState Training) (label : Training → ℝ)
    (hypotheses : List (Training → ℝ))
    (hvalid : AdaBoostAdmissible state label hypotheses) :
    adaBoostHalfDiscountFactor state label hypotheses hvalid =
      Real.exp (-(adaBoostVoteWeightSum state label hypotheses hvalid) / 2) := by
  induction hypotheses generalizing state with
  | nil => simp [adaBoostHalfDiscountFactor, adaBoostVoteWeightSum]
  | cons hypothesis remaining ih =>
      let herror := Classical.choose hvalid
      have hrest : AdaBoostAdmissible
          (adaBoostStep state label hypothesis herror) label remaining :=
        Classical.choose_spec hvalid
      have hdiscount : 0 < adaBoostDiscount (adaBoostError state label hypothesis) := by
        unfold adaBoostDiscount
        exact div_pos herror.1 (sub_pos.mpr herror.2)
      have htail := ih (state := adaBoostStep state label hypothesis herror) hrest
      change
        adaBoostDiscount (adaBoostError state label hypothesis) ^ ((1 : ℝ) / 2) *
            adaBoostHalfDiscountFactor
              (adaBoostStep state label hypothesis herror) label remaining hrest =
          Real.exp
            (-(adaBoostVoteWeight (adaBoostError state label hypothesis) +
                adaBoostVoteWeightSum
                  (adaBoostStep state label hypothesis herror) label remaining hrest) / 2)
      rw [Real.rpow_def_of_pos hdiscount, htail, ← Real.exp_add]
      congr 1
      simp only [adaBoostVoteWeight, one_div, Real.log_inv]
      ring

/-- The source's one-round simplification from Eq. (20) to Eq. (14). -/
theorem adaBoost_twice_error_div_half_discount_eq_source_factor
    {error : ℝ} (herror : 0 < error ∧ error < 1) :
    (2 * error) / adaBoostDiscount error ^ ((1 : ℝ) / 2) =
      2 * Real.sqrt (error * (1 - error)) := by
  have hcomplement_pos : 0 < 1 - error := sub_pos.mpr herror.2
  have hsqrt_error_pos : 0 < Real.sqrt error := Real.sqrt_pos.2 herror.1
  have hsqrt_error_ne : Real.sqrt error ≠ 0 := hsqrt_error_pos.ne'
  unfold adaBoostDiscount
  rw [Real.div_rpow herror.1.le hcomplement_pos.le,
    ← Real.sqrt_eq_rpow error, ← Real.sqrt_eq_rpow (1 - error),
    Real.sqrt_mul herror.1.le]
  field_simp [hsqrt_error_ne]
  nth_rewrite 1 [← Real.mul_self_sqrt herror.1.le]
  ring

/-- The product on the right-hand side of Freund--Schapire's Theorem 6. -/
noncomputable def adaBoostTheorem6Factor
    {Training : Type*} [Fintype Training] [Nonempty Training]
    (state : HedgeWeightState Training) (label : Training → ℝ) :
    (hypotheses : List (Training → ℝ)) →
      AdaBoostAdmissible state label hypotheses → ℝ
  | [], _ => 1
  | hypothesis :: remaining, hvalid =>
      2 * Real.sqrt
          (adaBoostError state label hypothesis *
            (1 - adaBoostError state label hypothesis)) *
        adaBoostTheorem6Factor
          (adaBoostStep state label hypothesis (Classical.choose hvalid)) label remaining
          (Classical.choose_spec hvalid)

/-- The common half-discount product is strictly positive. -/
theorem adaBoostHalfDiscountFactor_pos
    {Training : Type*} [Fintype Training] [Nonempty Training]
    (state : HedgeWeightState Training) (label : Training → ℝ)
    (hypotheses : List (Training → ℝ))
    (hvalid : AdaBoostAdmissible state label hypotheses) :
    0 < adaBoostHalfDiscountFactor state label hypotheses hvalid := by
  induction hypotheses generalizing state with
  | nil => simp [adaBoostHalfDiscountFactor]
  | cons hypothesis remaining ih =>
      let herror := Classical.choose hvalid
      have hrest : AdaBoostAdmissible
          (adaBoostStep state label hypothesis herror) label remaining :=
        Classical.choose_spec hvalid
      have hdiscount : 0 < adaBoostDiscount (adaBoostError state label hypothesis) := by
        unfold adaBoostDiscount
        exact div_pos herror.1 (sub_pos.mpr herror.2)
      change
        0 < adaBoostDiscount (adaBoostError state label hypothesis) ^ ((1 : ℝ) / 2) *
          adaBoostHalfDiscountFactor
            (adaBoostStep state label hypothesis herror) label remaining hrest
      exact mul_pos (Real.rpow_pos_of_pos hdiscount _)
        (ih (state := adaBoostStep state label hypothesis herror) hrest)

/--
Multiplying the per-round Eq. (20) factors and cancelling the common
half-discount product yields exactly the printed product in Theorem 6.
-/
theorem adaBoostErrorFactors_div_halfDiscountFactor_eq_theorem6Factor
    {Training : Type*} [Fintype Training] [Nonempty Training]
    (state : HedgeWeightState Training) (label : Training → ℝ)
    (hypotheses : List (Training → ℝ))
    (hvalid : AdaBoostAdmissible state label hypotheses) :
    ((adaBoostErrors state label hypotheses hvalid).map (fun error => 2 * error)).prod /
        adaBoostHalfDiscountFactor state label hypotheses hvalid =
      adaBoostTheorem6Factor state label hypotheses hvalid := by
  induction hypotheses generalizing state with
  | nil => simp [adaBoostErrors, adaBoostHalfDiscountFactor, adaBoostTheorem6Factor]
  | cons hypothesis remaining ih =>
      let herror := Classical.choose hvalid
      have hrest : AdaBoostAdmissible
          (adaBoostStep state label hypothesis herror) label remaining :=
        Classical.choose_spec hvalid
      have hdiscount : 0 < adaBoostDiscount (adaBoostError state label hypothesis) := by
        unfold adaBoostDiscount
        exact div_pos herror.1 (sub_pos.mpr herror.2)
      have hhead_half_pos :
          0 < adaBoostDiscount (adaBoostError state label hypothesis) ^ ((1 : ℝ) / 2) :=
        Real.rpow_pos_of_pos hdiscount _
      have htail_half_pos :
          0 < adaBoostHalfDiscountFactor
            (adaBoostStep state label hypothesis herror) label remaining hrest :=
        adaBoostHalfDiscountFactor_pos
          (adaBoostStep state label hypothesis herror) label remaining hrest
      have htail := ih (state := adaBoostStep state label hypothesis herror) hrest
      change
        ((2 * adaBoostError state label hypothesis) *
          ((adaBoostErrors (adaBoostStep state label hypothesis herror) label remaining hrest).map
            (fun error => 2 * error)).prod) /
          (adaBoostDiscount (adaBoostError state label hypothesis) ^ ((1 : ℝ) / 2) *
            adaBoostHalfDiscountFactor
              (adaBoostStep state label hypothesis herror) label remaining hrest) =
          2 * Real.sqrt
            (adaBoostError state label hypothesis *
              (1 - adaBoostError state label hypothesis)) *
            adaBoostTheorem6Factor
              (adaBoostStep state label hypothesis herror) label remaining hrest
      calc
        ((2 * adaBoostError state label hypothesis) *
          ((adaBoostErrors (adaBoostStep state label hypothesis herror) label remaining hrest).map
            (fun error => 2 * error)).prod) /
          (adaBoostDiscount (adaBoostError state label hypothesis) ^ ((1 : ℝ) / 2) *
            adaBoostHalfDiscountFactor
              (adaBoostStep state label hypothesis herror) label remaining hrest) =
            ((2 * adaBoostError state label hypothesis) /
              adaBoostDiscount (adaBoostError state label hypothesis) ^ ((1 : ℝ) / 2)) *
              (((adaBoostErrors (adaBoostStep state label hypothesis herror) label remaining hrest).map
                (fun error => 2 * error)).prod /
                adaBoostHalfDiscountFactor
                  (adaBoostStep state label hypothesis herror) label remaining hrest) := by
          field_simp [hhead_half_pos.ne', htail_half_pos.ne']
        _ = 2 * Real.sqrt
            (adaBoostError state label hypothesis *
              (1 - adaBoostError state label hypothesis)) *
            adaBoostTheorem6Factor
              (adaBoostStep state label hypothesis herror) label remaining hrest := by
          rw [adaBoost_twice_error_div_half_discount_eq_source_factor herror, htail]

/-- At a zero-labeled sample, the weighted absolute error equals the weighted vote. -/
theorem adaBoostWeightedAbsoluteError_eq_vote_of_label_eq_zero
    {Training : Type*} [Fintype Training] [Nonempty Training]
    (state : HedgeWeightState Training) (label : Training → ℝ)
    (hypotheses : List (Training → ℝ))
    (hhypothesis : ∀ hypothesis ∈ hypotheses, ∀ sample,
      0 ≤ hypothesis sample ∧ hypothesis sample ≤ 1)
    (hvalid : AdaBoostAdmissible state label hypotheses)
    (sample : Training) (hlabel : label sample = 0) :
    adaBoostWeightedAbsoluteError state label hypotheses hvalid sample =
      adaBoostVote state label hypotheses hvalid sample := by
  induction hypotheses generalizing state with
  | nil => simp [adaBoostWeightedAbsoluteError, adaBoostVote]
  | cons hypothesis remaining ih =>
      let herror := Classical.choose hvalid
      have hrest : AdaBoostAdmissible
          (adaBoostStep state label hypothesis herror) label remaining :=
        Classical.choose_spec hvalid
      have hhypothesis_head : ∀ sample,
          0 ≤ hypothesis sample ∧ hypothesis sample ≤ 1 :=
        hhypothesis hypothesis (by simp)
      have hhypothesis_rest : ∀ next ∈ remaining, ∀ sample,
          0 ≤ next sample ∧ next sample ≤ 1 := by
        intro next hnext other
        exact hhypothesis next (by simp [hnext]) other
      have htail := ih (state := adaBoostStep state label hypothesis herror)
        hhypothesis_rest hrest
      change
        adaBoostVoteWeight (adaBoostError state label hypothesis) *
            |hypothesis sample - label sample| +
            adaBoostWeightedAbsoluteError
              (adaBoostStep state label hypothesis herror) label remaining hrest sample =
          adaBoostVoteWeight (adaBoostError state label hypothesis) * hypothesis sample +
            adaBoostVote
              (adaBoostStep state label hypothesis herror) label remaining hrest sample
      rw [hlabel, sub_zero, abs_of_nonneg (hhypothesis_head sample).1, htail]

/-- At a one-labeled sample, the weighted absolute error is total vote weight minus vote. -/
theorem adaBoostWeightedAbsoluteError_eq_weightSum_sub_vote_of_label_eq_one
    {Training : Type*} [Fintype Training] [Nonempty Training]
    (state : HedgeWeightState Training) (label : Training → ℝ)
    (hypotheses : List (Training → ℝ))
    (hhypothesis : ∀ hypothesis ∈ hypotheses, ∀ sample,
      0 ≤ hypothesis sample ∧ hypothesis sample ≤ 1)
    (hvalid : AdaBoostAdmissible state label hypotheses)
    (sample : Training) (hlabel : label sample = 1) :
    adaBoostWeightedAbsoluteError state label hypotheses hvalid sample =
      adaBoostVoteWeightSum state label hypotheses hvalid -
        adaBoostVote state label hypotheses hvalid sample := by
  induction hypotheses generalizing state with
  | nil => simp [adaBoostWeightedAbsoluteError, adaBoostVoteWeightSum, adaBoostVote]
  | cons hypothesis remaining ih =>
      let herror := Classical.choose hvalid
      have hrest : AdaBoostAdmissible
          (adaBoostStep state label hypothesis herror) label remaining :=
        Classical.choose_spec hvalid
      have hhypothesis_head : ∀ sample,
          0 ≤ hypothesis sample ∧ hypothesis sample ≤ 1 :=
        hhypothesis hypothesis (by simp)
      have hhypothesis_rest : ∀ next ∈ remaining, ∀ sample,
          0 ≤ next sample ∧ next sample ≤ 1 := by
        intro next hnext other
        exact hhypothesis next (by simp [hnext]) other
      have htail := ih (state := adaBoostStep state label hypothesis herror)
        hhypothesis_rest hrest
      have habs : |hypothesis sample - label sample| = 1 - hypothesis sample := by
        rw [hlabel]
        calc
          |hypothesis sample - 1| = -(hypothesis sample - 1) :=
            abs_of_nonpos (sub_nonpos.mpr (hhypothesis_head sample).2)
          _ = 1 - hypothesis sample := by ring
      change
        adaBoostVoteWeight (adaBoostError state label hypothesis) *
            |hypothesis sample - label sample| +
            adaBoostWeightedAbsoluteError
              (adaBoostStep state label hypothesis herror) label remaining hrest sample =
          (adaBoostVoteWeight (adaBoostError state label hypothesis) +
            adaBoostVoteWeightSum
              (adaBoostStep state label hypothesis herror) label remaining hrest) -
            (adaBoostVoteWeight (adaBoostError state label hypothesis) * hypothesis sample +
              adaBoostVote
                (adaBoostStep state label hypothesis herror) label remaining hrest sample)
      rw [habs, htail]
      ring

/--
An incorrectly thresholded Boolean label has weighted absolute error at least
one half of the total vote weight.  This is Eq. (17) in the proof of
Freund--Schapire's Theorem 6.
-/
theorem adaBoostFinalHypothesis_mistake_implies_half_weight_le_weightedAbsoluteError
    {Training : Type*} [Fintype Training] [Nonempty Training]
    (state : HedgeWeightState Training) (label : Training → ℝ)
    (hypotheses : List (Training → ℝ))
    (hhypothesis : ∀ hypothesis ∈ hypotheses, ∀ sample,
      0 ≤ hypothesis sample ∧ hypothesis sample ≤ 1)
    (hvalid : AdaBoostAdmissible state label hypotheses)
    (sample : Training) (hlabel : label sample = 0 ∨ label sample = 1)
    (hmistake : adaBoostFinalHypothesis state label hypotheses hvalid sample ≠ label sample) :
    adaBoostVoteWeightSum state label hypotheses hvalid / 2 ≤
      adaBoostWeightedAbsoluteError state label hypotheses hvalid sample := by
  rcases hlabel with hzero | hone
  · have hthreshold : adaBoostVoteWeightSum state label hypotheses hvalid / 2 ≤
        adaBoostVote state label hypotheses hvalid sample := by
      by_contra hnotthreshold
      apply hmistake
      simp [adaBoostFinalHypothesis, hnotthreshold, hzero]
    rw [adaBoostWeightedAbsoluteError_eq_vote_of_label_eq_zero state label hypotheses
      hhypothesis hvalid sample hzero]
    exact hthreshold
  · have hnotthreshold : ¬ adaBoostVoteWeightSum state label hypotheses hvalid / 2 ≤
        adaBoostVote state label hypotheses hvalid sample := by
      intro hthreshold
      apply hmistake
      simp [adaBoostFinalHypothesis, hthreshold, hone]
    have hstrict : adaBoostVote state label hypotheses hvalid sample <
        adaBoostVoteWeightSum state label hypotheses hvalid / 2 :=
      lt_of_not_ge hnotthreshold
    rw [adaBoostWeightedAbsoluteError_eq_weightSum_sub_vote_of_label_eq_one
      state label hypotheses hhypothesis hvalid sample hone]
    linarith

/-- A misclassified Boolean sample receives at least the source half-discount factor. -/
theorem adaBoostFinalHypothesis_mistake_halfDiscountFactor_le_sampleWeightFactor
    {Training : Type*} [Fintype Training] [Nonempty Training]
    (state : HedgeWeightState Training) (label : Training → ℝ)
    (hypotheses : List (Training → ℝ))
    (hhypothesis : ∀ hypothesis ∈ hypotheses, ∀ sample,
      0 ≤ hypothesis sample ∧ hypothesis sample ≤ 1)
    (hvalid : AdaBoostAdmissible state label hypotheses)
    (sample : Training) (hlabel : label sample = 0 ∨ label sample = 1)
    (hmistake : adaBoostFinalHypothesis state label hypotheses hvalid sample ≠ label sample) :
    adaBoostHalfDiscountFactor state label hypotheses hvalid ≤
      adaBoostSampleWeightFactor state label hypotheses hvalid sample := by
  rw [adaBoostHalfDiscountFactor_eq_exp_neg_half_weightSum,
    adaBoostSampleWeightFactor_eq_exp_log]
  apply Real.exp_le_exp.mpr
  rw [adaBoostLogSampleWeightFactor_eq_weightedAbsoluteError_sub_weightSum]
  have hhalf := adaBoostFinalHypothesis_mistake_implies_half_weight_le_weightedAbsoluteError
    state label hypotheses hhypothesis hvalid sample hlabel hmistake
  linarith

/-- Eq. (18)'s per-sample lower bound on a final source weight after a mistake. -/
theorem adaBoostFinalHypothesis_mistake_initial_weight_mul_halfDiscountFactor_le_final_weight
    {Training : Type*} [Fintype Training] [Nonempty Training]
    (state : HedgeWeightState Training) (label : Training → ℝ)
    (hypotheses : List (Training → ℝ))
    (hhypothesis : ∀ hypothesis ∈ hypotheses, ∀ sample,
      0 ≤ hypothesis sample ∧ hypothesis sample ≤ 1)
    (hvalid : AdaBoostAdmissible state label hypotheses)
    (sample : Training) (hlabel : label sample = 0 ∨ label sample = 1)
    (hmistake : adaBoostFinalHypothesis state label hypotheses hvalid sample ≠ label sample) :
    state.weight sample * adaBoostHalfDiscountFactor state label hypotheses hvalid ≤
      (adaBoostRun state label hypotheses hvalid).weight sample := by
  rw [adaBoostRun_weight]
  exact mul_le_mul_of_nonneg_left
    (adaBoostFinalHypothesis_mistake_halfDiscountFactor_le_sampleWeightFactor
      state label hypotheses hhypothesis hvalid sample hlabel hmistake)
    (state.nonneg sample)

/-- The finite weighted training error of the Figure-2 final classifier. -/
noncomputable def adaBoostTrainingError
    {Training : Type*} [Fintype Training] [Nonempty Training]
    (state : HedgeWeightState Training) (label : Training → ℝ)
    (hypotheses : List (Training → ℝ))
    (hvalid : AdaBoostAdmissible state label hypotheses) : ℝ :=
  ∑ sample, state.weight sample *
    (if adaBoostFinalHypothesis state label hypotheses hvalid sample = label sample then 0 else 1)

/-- The weighted training error is the initial mass of the finite set of mistakes. -/
theorem adaBoostTrainingError_eq_mistake_weight_sum
    {Training : Type*} [Fintype Training] [Nonempty Training]
    (state : HedgeWeightState Training) (label : Training → ℝ)
    (hypotheses : List (Training → ℝ))
    (hvalid : AdaBoostAdmissible state label hypotheses) :
    adaBoostTrainingError state label hypotheses hvalid =
      ∑ sample ∈ (Finset.univ.filter fun sample =>
        adaBoostFinalHypothesis state label hypotheses hvalid sample ≠ label sample),
        state.weight sample := by
  classical
  rw [adaBoostTrainingError]
  symm
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun sample _ => ?_
  by_cases hmistake : adaBoostFinalHypothesis state label hypotheses hvalid sample ≠ label sample
  · simp [hmistake]
  · simp [not_not.mp hmistake]

/--
Eq. (19)'s finite lower bound: final total source mass dominates the final
training error times the common half-discount factor.
-/
theorem adaBoostTrainingError_mul_halfDiscountFactor_le_final_total
    {Training : Type*} [Fintype Training] [Nonempty Training]
    (state : HedgeWeightState Training) (label : Training → ℝ)
    (hypotheses : List (Training → ℝ))
    (hhypothesis : ∀ hypothesis ∈ hypotheses, ∀ sample,
      0 ≤ hypothesis sample ∧ hypothesis sample ≤ 1)
    (hlabel : ∀ sample, label sample = 0 ∨ label sample = 1)
    (hvalid : AdaBoostAdmissible state label hypotheses) :
    adaBoostTrainingError state label hypotheses hvalid *
        adaBoostHalfDiscountFactor state label hypotheses hvalid ≤
      ∑ sample, (adaBoostRun state label hypotheses hvalid).weight sample := by
  classical
  let mistakes : Finset Training := Finset.univ.filter fun sample =>
    adaBoostFinalHypothesis state label hypotheses hvalid sample ≠ label sample
  rw [adaBoostTrainingError_eq_mistake_weight_sum]
  change
    (∑ sample ∈ mistakes, state.weight sample) *
        adaBoostHalfDiscountFactor state label hypotheses hvalid ≤
      ∑ sample, (adaBoostRun state label hypotheses hvalid).weight sample
  rw [Finset.sum_mul]
  calc
    (∑ sample ∈ mistakes,
      state.weight sample * adaBoostHalfDiscountFactor state label hypotheses hvalid) ≤
        ∑ sample ∈ mistakes, (adaBoostRun state label hypotheses hvalid).weight sample :=
      Finset.sum_le_sum fun sample hsample =>
        adaBoostFinalHypothesis_mistake_initial_weight_mul_halfDiscountFactor_le_final_weight
          state label hypotheses hhypothesis hvalid sample (hlabel sample)
          ((Finset.mem_filter.mp hsample).2)
    _ ≤ ∑ sample, (adaBoostRun state label hypotheses hvalid).weight sample :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun sample _ _ => (adaBoostRun state label hypotheses hvalid).nonneg sample)

/-- The product of all `2 ε_t` factors in a certified finite AdaBoost run is nonnegative. -/
theorem adaBoostErrorFactors_nonneg
    {Training : Type*} [Fintype Training] [Nonempty Training]
    (state : HedgeWeightState Training) (label : Training → ℝ)
    (hypotheses : List (Training → ℝ))
    (hvalid : AdaBoostAdmissible state label hypotheses) :
    0 ≤ ((adaBoostErrors state label hypotheses hvalid).map (fun error => 2 * error)).prod := by
  induction hypotheses generalizing state with
  | nil => simp [adaBoostErrors]
  | cons hypothesis remaining ih =>
      let herror := Classical.choose hvalid
      have herror_pos : 0 < adaBoostError state label hypothesis := herror.1
      have hrest : AdaBoostAdmissible
          (adaBoostStep state label hypothesis herror) label remaining :=
        Classical.choose_spec hvalid
      change
        0 ≤ (2 * adaBoostError state label hypothesis) *
          ((adaBoostErrors (adaBoostStep state label hypothesis herror) label remaining hrest).map
            (fun error => 2 * error)).prod
      exact mul_nonneg (by linarith) (ih (adaBoostStep state label hypothesis herror) hrest)

/-- If labels and weak predictions lie in `[0,1]`, so does the source loss. -/
theorem adaBoostLoss_mem_Icc
    {Training : Type*} (label hypothesis : Training → ℝ)
    (hlabel : ∀ sample, 0 ≤ label sample ∧ label sample ≤ 1)
    (hhypothesis : ∀ sample, 0 ≤ hypothesis sample ∧ hypothesis sample ≤ 1)
    (sample : Training) :
    0 ≤ adaBoostLoss label hypothesis sample ∧ adaBoostLoss label hypothesis sample ≤ 1 := by
  unfold adaBoostLoss
  have hlabel_sample := hlabel sample
  have hhypothesis_sample := hhypothesis sample
  have habs_nonneg : 0 ≤ |hypothesis sample - label sample| := abs_nonneg _
  have habs_le_one : |hypothesis sample - label sample| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [hlabel_sample.1, hlabel_sample.2,
      hhypothesis_sample.1, hhypothesis_sample.2]
  constructor <;> linarith

/-- The weighted source loss is one minus the Step-3 weighted error. -/
theorem HedgeWeightState.expectation_adaBoostLoss
    {Training : Type*} [Fintype Training]
    (state : HedgeWeightState Training) (label hypothesis : Training → ℝ) :
    state.expectation (adaBoostLoss label hypothesis) =
      1 - adaBoostError state label hypothesis := by
  classical
  unfold HedgeWeightState.expectation adaBoostError adaBoostLoss
  change
    pmfExp state.policy (fun sample => 1 - |hypothesis sample - label sample|) =
      1 - pmfExp state.policy (fun sample => |hypothesis sample - label sample|)
  rw [pmfExp_sub, pmfExp_const]

/--
One source update contracts total unnormalized weight by its exact chord bound.
This is the finite real-valued form of the inequality in Eq. (15), before
substituting the adaptive choice of `β`.
-/
theorem hedgeWeightStateStep_total_le_linear
    {Training : Type*} [Fintype Training] [DecidableEq Training] [Nonempty Training]
    (state : HedgeWeightState Training) (loss : Training → ℝ) (discount : ℝ)
    (hdiscount : 0 < discount)
    (hloss_nonneg : ∀ sample, 0 ≤ loss sample)
    (hloss_one : ∀ sample, loss sample ≤ 1) :
    (∑ sample, (hedgeWeightStateStep state loss discount hdiscount).weight sample) ≤
      (∑ sample, state.weight sample) *
        (1 - (1 - discount) * state.expectation loss) := by
  rw [hedgeWeightStateStep_total]
  exact mul_le_mul_of_nonneg_left
    (hedge_one_step_potential_upper_of_pos state.policy loss discount hdiscount
      hloss_nonneg hloss_one)
    state.total_pos.le

/--
After substituting `β = ε/(1-ε)`, AdaBoost's one-round total weight is at most
twice the current weighted error times the old total weight.  This is exactly
the per-round factor in Freund--Schapire (1997), Eq. (15).
-/
theorem adaBoostStep_total_le_twice_error
    {Training : Type*} [Fintype Training] [DecidableEq Training] [Nonempty Training]
    (state : HedgeWeightState Training) (label hypothesis : Training → ℝ)
    (hlabel : ∀ sample, 0 ≤ label sample ∧ label sample ≤ 1)
    (hhypothesis : ∀ sample, 0 ≤ hypothesis sample ∧ hypothesis sample ≤ 1)
    (herror : 0 < adaBoostError state label hypothesis ∧
      adaBoostError state label hypothesis < 1) :
    (∑ sample, (adaBoostStep state label hypothesis herror).weight sample) ≤
      (∑ sample, state.weight sample) *
        (2 * adaBoostError state label hypothesis) := by
  let error := adaBoostError state label hypothesis
  have hdiscount : 0 < adaBoostDiscount error := by
    unfold adaBoostDiscount
    exact div_pos herror.1 (sub_pos.mpr herror.2)
  have hdenom : 1 - error ≠ 0 := by
    linarith [herror.2]
  have hfactor :
      1 - (1 - adaBoostDiscount error) * (1 - error) = 2 * error := by
    unfold adaBoostDiscount
    field_simp [hdenom]
    ring
  have hloss_nonneg : ∀ sample, 0 ≤ adaBoostLoss label hypothesis sample :=
    fun sample => (adaBoostLoss_mem_Icc label hypothesis hlabel hhypothesis sample).1
  have hloss_one : ∀ sample, adaBoostLoss label hypothesis sample ≤ 1 :=
    fun sample => (adaBoostLoss_mem_Icc label hypothesis hlabel hhypothesis sample).2
  change
    (∑ sample,
      (hedgeWeightStateStep state (adaBoostLoss label hypothesis)
        (adaBoostDiscount error) hdiscount).weight sample) ≤
      (∑ sample, state.weight sample) * (2 * error)
  calc
    (∑ sample,
      (hedgeWeightStateStep state (adaBoostLoss label hypothesis)
        (adaBoostDiscount error) hdiscount).weight sample) ≤
        (∑ sample, state.weight sample) *
          (1 - (1 - adaBoostDiscount error) *
            state.expectation (adaBoostLoss label hypothesis)) :=
      hedgeWeightStateStep_total_le_linear state (adaBoostLoss label hypothesis)
        (adaBoostDiscount error) hdiscount hloss_nonneg hloss_one
    _ = (∑ sample, state.weight sample) * (2 * error) := by
      rw [state.expectation_adaBoostLoss]
      change
        (∑ sample, state.weight sample) *
            (1 - (1 - adaBoostDiscount error) * (1 - error)) =
          (∑ sample, state.weight sample) * (2 * error)
      rw [hfactor]

/--
The finite product form of Eq. (15): the final total source weight is bounded
by the initial total weight times the product of the adaptive `2 ε_t` factors.
-/
theorem adaBoostRun_total_le_errorFactors
    {Training : Type*} [Fintype Training] [DecidableEq Training] [Nonempty Training]
    (state : HedgeWeightState Training) (label : Training → ℝ)
    (hlabel : ∀ sample, 0 ≤ label sample ∧ label sample ≤ 1)
    (hypotheses : List (Training → ℝ))
    (hhypothesis : ∀ hypothesis ∈ hypotheses, ∀ sample,
      0 ≤ hypothesis sample ∧ hypothesis sample ≤ 1)
    (hvalid : AdaBoostAdmissible state label hypotheses) :
    (∑ sample, (adaBoostRun state label hypotheses hvalid).weight sample) ≤
      (∑ sample, state.weight sample) *
        ((adaBoostErrors state label hypotheses hvalid).map (fun error => 2 * error)).prod := by
  induction hypotheses generalizing state with
  | nil => simp [adaBoostRun, adaBoostErrors]
  | cons hypothesis remaining ih =>
      let herror := Classical.choose hvalid
      have hrest : AdaBoostAdmissible
          (adaBoostStep state label hypothesis herror) label remaining :=
        Classical.choose_spec hvalid
      have hhypothesis_head : ∀ sample,
          0 ≤ hypothesis sample ∧ hypothesis sample ≤ 1 :=
        hhypothesis hypothesis (by simp)
      have hhypothesis_rest : ∀ next ∈ remaining, ∀ sample,
          0 ≤ next sample ∧ next sample ≤ 1 := by
        intro next hnext sample
        exact hhypothesis next (by simp [hnext]) sample
      have hstep := adaBoostStep_total_le_twice_error state label hypothesis
        hlabel hhypothesis_head herror
      have htail := ih (state := adaBoostStep state label hypothesis herror)
        hhypothesis_rest hrest
      have htail_nonneg :
          0 ≤ ((adaBoostErrors (adaBoostStep state label hypothesis herror) label remaining hrest).map
            (fun error => 2 * error)).prod :=
        adaBoostErrorFactors_nonneg (adaBoostStep state label hypothesis herror) label remaining hrest
      change
        (∑ sample,
          (adaBoostRun (adaBoostStep state label hypothesis herror) label remaining hrest).weight sample) ≤
          (∑ sample, state.weight sample) *
            ((2 * adaBoostError state label hypothesis) *
              ((adaBoostErrors (adaBoostStep state label hypothesis herror) label remaining hrest).map
                (fun error => 2 * error)).prod)
      calc
        (∑ sample,
          (adaBoostRun (adaBoostStep state label hypothesis herror) label remaining hrest).weight sample) ≤
            (∑ sample,
              (adaBoostStep state label hypothesis herror).weight sample) *
              ((adaBoostErrors (adaBoostStep state label hypothesis herror) label remaining hrest).map
                (fun error => 2 * error)).prod := htail
        _ ≤ ((∑ sample, state.weight sample) *
              (2 * adaBoostError state label hypothesis)) *
              ((adaBoostErrors (adaBoostStep state label hypothesis herror) label remaining hrest).map
                (fun error => 2 * error)).prod :=
          mul_le_mul_of_nonneg_right hstep htail_nonneg
        _ = (∑ sample, state.weight sample) *
            ((2 * adaBoostError state label hypothesis) *
              ((adaBoostErrors (adaBoostStep state label hypothesis herror) label remaining hrest).map
                (fun error => 2 * error)).prod) := by ring

/--
Freund--Schapire (1997), Theorem 6, in its finite source model: with a
normalized initial example distribution, Figure 2's final weighted-threshold
hypothesis has training error at most the printed product of per-round factors.
-/
theorem adaBoost_training_error_le_theorem6Factor
    {Training : Type*} [Fintype Training] [DecidableEq Training] [Nonempty Training]
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
  have hhalf_pos : 0 < adaBoostHalfDiscountFactor state label hypotheses hvalid :=
    adaBoostHalfDiscountFactor_pos state label hypotheses hvalid
  have hlower := adaBoostTrainingError_mul_halfDiscountFactor_le_final_total
    state label hypotheses hhypothesis hlabel_boolean hvalid
  have hupper := adaBoostRun_total_le_errorFactors state label hlabel_unit hypotheses
    hhypothesis hvalid
  have hcombined :
      adaBoostTrainingError state label hypotheses hvalid *
          adaBoostHalfDiscountFactor state label hypotheses hvalid ≤
        (∑ sample, state.weight sample) *
          ((adaBoostErrors state label hypotheses hvalid).map (fun error => 2 * error)).prod :=
    hlower.trans hupper
  calc
    adaBoostTrainingError state label hypotheses hvalid ≤
        ((∑ sample, state.weight sample) *
          ((adaBoostErrors state label hypotheses hvalid).map (fun error => 2 * error)).prod) /
          adaBoostHalfDiscountFactor state label hypotheses hvalid :=
      (le_div_iff₀ hhalf_pos).mpr hcombined
    _ = ((adaBoostErrors state label hypotheses hvalid).map (fun error => 2 * error)).prod /
          adaBoostHalfDiscountFactor state label hypotheses hvalid := by
      rw [hstate_total]
      ring
    _ = adaBoostTheorem6Factor state label hypotheses hvalid :=
      adaBoostErrorFactors_div_halfDiscountFactor_eq_theorem6Factor state label hypotheses hvalid

/-- Every Step-3 error appearing in a certified Figure-2 run is interior. -/
theorem adaBoostErrors_mem_Ioo
    {Training : Type*} [Fintype Training] [Nonempty Training]
    (state : HedgeWeightState Training) (label : Training → ℝ)
    (hypotheses : List (Training → ℝ))
    (hvalid : AdaBoostAdmissible state label hypotheses) :
    ∀ error ∈ adaBoostErrors state label hypotheses hvalid, 0 < error ∧ error < 1 := by
  induction hypotheses generalizing state with
  | nil => simp [adaBoostErrors]
  | cons hypothesis remaining ih =>
      let herror := Classical.choose hvalid
      have hrest : AdaBoostAdmissible
          (adaBoostStep state label hypothesis herror) label remaining :=
        Classical.choose_spec hvalid
      intro error hmem
      change error ∈ adaBoostError state label hypothesis ::
        adaBoostErrors (adaBoostStep state label hypothesis herror) label remaining hrest at hmem
      rcases List.mem_cons.mp hmem with hhead | htail
      · simpa [hhead] using herror
      · exact ih (state := adaBoostStep state label hypothesis herror) hrest error htail

/-- The recursive Theorem-6 factor is the product over the recorded errors. -/
theorem adaBoostTheorem6Factor_eq_errorFactorProduct
    {Training : Type*} [Fintype Training] [Nonempty Training]
    (state : HedgeWeightState Training) (label : Training → ℝ)
    (hypotheses : List (Training → ℝ))
    (hvalid : AdaBoostAdmissible state label hypotheses) :
    adaBoostTheorem6Factor state label hypotheses hvalid =
      ((adaBoostErrors state label hypotheses hvalid).map fun error =>
        2 * Real.sqrt (error * (1 - error))).prod := by
  induction hypotheses generalizing state with
  | nil => simp [adaBoostTheorem6Factor, adaBoostErrors]
  | cons hypothesis remaining ih =>
      let herror := Classical.choose hvalid
      have hrest : AdaBoostAdmissible
          (adaBoostStep state label hypothesis herror) label remaining :=
        Classical.choose_spec hvalid
      have htail := ih (state := adaBoostStep state label hypothesis herror) hrest
      change
        2 * Real.sqrt
            (adaBoostError state label hypothesis *
              (1 - adaBoostError state label hypothesis)) *
            adaBoostTheorem6Factor
              (adaBoostStep state label hypothesis herror) label remaining hrest =
          (2 * Real.sqrt
              (adaBoostError state label hypothesis *
                (1 - adaBoostError state label hypothesis)) ::
            (adaBoostErrors (adaBoostStep state label hypothesis herror) label remaining hrest).map
              (fun error => 2 * Real.sqrt (error * (1 - error)))).prod
      rw [htail]
      rfl

/--
The product of AdaBoost's per-round square-root factors is the exponential of
the negative binary-KL sum in Eq. (21).
-/
theorem adaBoostErrorFactorProduct_eq_exp_neg_binaryKLSum
    (errors : List ℝ) (herrors : ∀ error ∈ errors, 0 < error ∧ error < 1) :
    (errors.map fun error => 2 * Real.sqrt (error * (1 - error))).prod =
      Real.exp (-((errors.map fun error =>
        Probability.binaryKLDivergence (1 / 2) error).sum)) := by
  induction errors with
  | nil => simp
  | cons error remaining ih =>
      have herror := herrors error (by simp)
      have hremaining : ∀ later ∈ remaining, 0 < later ∧ later < 1 := by
        intro later hlater
        exact herrors later (by simp [hlater])
      simp only [List.map_cons, List.prod_cons, List.sum_cons]
      rw [Probability.two_mul_sqrt_error_mul_one_sub_eq_exp_neg_binaryKL_half herror,
        ih hremaining, ← Real.exp_add]
      congr 1
      ring

/-- Eq. (21)'s exact binary-KL expression for the Theorem-6 product. -/
theorem adaBoostTheorem6Factor_eq_exp_neg_binaryKLSum
    {Training : Type*} [Fintype Training] [Nonempty Training]
    (state : HedgeWeightState Training) (label : Training → ℝ)
    (hypotheses : List (Training → ℝ))
    (hvalid : AdaBoostAdmissible state label hypotheses) :
    adaBoostTheorem6Factor state label hypotheses hvalid =
      Real.exp (-((adaBoostErrors state label hypotheses hvalid).map fun error =>
        Probability.binaryKLDivergence (1 / 2) error).sum) := by
  rw [adaBoostTheorem6Factor_eq_errorFactorProduct]
  exact adaBoostErrorFactorProduct_eq_exp_neg_binaryKLSum
    (adaBoostErrors state label hypotheses hvalid)
    (adaBoostErrors_mem_Ioo state label hypotheses hvalid)

/-- Eq. (21)'s direct binary-KL upper bound on the training error. -/
theorem adaBoost_training_error_le_exp_neg_binaryKLSum
    {Training : Type*} [Fintype Training] [DecidableEq Training] [Nonempty Training]
    (state : HedgeWeightState Training) (label : Training → ℝ)
    (hstate_total : ∑ sample, state.weight sample = 1)
    (hlabel_unit : ∀ sample, 0 ≤ label sample ∧ label sample ≤ 1)
    (hlabel_boolean : ∀ sample, label sample = 0 ∨ label sample = 1)
    (hypotheses : List (Training → ℝ))
    (hhypothesis : ∀ hypothesis ∈ hypotheses, ∀ sample,
      0 ≤ hypothesis sample ∧ hypothesis sample ≤ 1)
    (hvalid : AdaBoostAdmissible state label hypotheses) :
    adaBoostTrainingError state label hypotheses hvalid ≤
      Real.exp (-((adaBoostErrors state label hypotheses hvalid).map fun error =>
        Probability.binaryKLDivergence (1 / 2) error).sum) := by
  calc
    adaBoostTrainingError state label hypotheses hvalid ≤
        adaBoostTheorem6Factor state label hypotheses hvalid :=
      adaBoost_training_error_le_theorem6Factor state label hstate_total hlabel_unit
        hlabel_boolean hypotheses hhypothesis hvalid
    _ = Real.exp (-((adaBoostErrors state label hypotheses hvalid).map fun error =>
        Probability.binaryKLDivergence (1 / 2) error).sum) :=
      adaBoostTheorem6Factor_eq_exp_neg_binaryKLSum state label hypotheses hvalid

/--
The sum form of the binary Pinsker bound for a finite path of AdaBoost errors.
-/
theorem two_mul_sum_squared_edges_le_binaryKLSum
    (errors : List ℝ) (herrors : ∀ error ∈ errors, 0 < error ∧ error < 1) :
    2 * (errors.map fun error => (1 / 2 - error) ^ 2).sum ≤
      (errors.map fun error => Probability.binaryKLDivergence (1 / 2) error).sum := by
  induction errors with
  | nil => simp
  | cons error remaining ih =>
      have herror := herrors error (by simp)
      have hremaining : ∀ later ∈ remaining, 0 < later ∧ later < 1 := by
        intro later hlater
        exact herrors later (by simp [hlater])
      have hhead : 2 * (1 / 2 - error) ^ 2 ≤
          Probability.binaryKLDivergence (1 / 2) error := by
        simpa using Probability.two_mul_sq_le_binaryKLDivergence_half_half_sub
          (gamma := 1 / 2 - error) (by linarith [herror.2]) (by linarith [herror.1])
      have htail := ih hremaining
      simp only [List.map_cons, List.sum_cons]
      nlinarith

/--
Exponentiating the finite-path binary Pinsker bound gives the middle-to-right
inequality displayed in Freund--Schapire (1997), Eq. (21).
-/
theorem exp_neg_binaryKLSum_le_exp_neg_two_sum_squared_edges
    (errors : List ℝ) (herrors : ∀ error ∈ errors, 0 < error ∧ error < 1) :
    Real.exp (-((errors.map fun error =>
        Probability.binaryKLDivergence (1 / 2) error).sum)) ≤
      Real.exp (-2 * (errors.map fun error => (1 / 2 - error) ^ 2).sum) := by
  apply Real.exp_le_exp.mpr
  have hsum := two_mul_sum_squared_edges_le_binaryKLSum errors herrors
  linarith

/--
Eq. (21)'s Chernoff/Pinsker consequence: training error is at most the
exponential of negative twice the sum of the squared edges
`gamma_t = 1/2 - epsilon_t`.
-/
theorem adaBoost_training_error_le_exp_neg_two_sum_squared_edges
    {Training : Type*} [Fintype Training] [DecidableEq Training] [Nonempty Training]
    (state : HedgeWeightState Training) (label : Training → ℝ)
    (hstate_total : ∑ sample, state.weight sample = 1)
    (hlabel_unit : ∀ sample, 0 ≤ label sample ∧ label sample ≤ 1)
    (hlabel_boolean : ∀ sample, label sample = 0 ∨ label sample = 1)
    (hypotheses : List (Training → ℝ))
    (hhypothesis : ∀ hypothesis ∈ hypotheses, ∀ sample,
      0 ≤ hypothesis sample ∧ hypothesis sample ≤ 1)
    (hvalid : AdaBoostAdmissible state label hypotheses) :
    adaBoostTrainingError state label hypotheses hvalid ≤
      Real.exp (-2 * ((adaBoostErrors state label hypotheses hvalid).map fun error =>
        (1 / 2 - error) ^ 2).sum) := by
  have htheorem6 := adaBoost_training_error_le_theorem6Factor state label hstate_total
    hlabel_unit hlabel_boolean hypotheses hhypothesis hvalid
  have hfactor := adaBoostTheorem6Factor_eq_exp_neg_binaryKLSum state label hypotheses hvalid
  have hsum := two_mul_sum_squared_edges_le_binaryKLSum
    (adaBoostErrors state label hypotheses hvalid)
    (adaBoostErrors_mem_Ioo state label hypotheses hvalid)
  calc
    adaBoostTrainingError state label hypotheses hvalid ≤
        adaBoostTheorem6Factor state label hypotheses hvalid := htheorem6
    _ = Real.exp (-((adaBoostErrors state label hypotheses hvalid).map fun error =>
        Probability.binaryKLDivergence (1 / 2) error).sum) := hfactor
    _ ≤ Real.exp (-2 * ((adaBoostErrors state label hypotheses hvalid).map fun error =>
        (1 / 2 - error) ^ 2).sum) := by
      apply Real.exp_le_exp.mpr
      linarith

/-- The recorded error list has one entry for every Figure-2 iteration. -/
theorem adaBoostErrors_length
    {Training : Type*} [Fintype Training] [Nonempty Training]
    (state : HedgeWeightState Training) (label : Training → ℝ)
    (hypotheses : List (Training → ℝ))
    (hvalid : AdaBoostAdmissible state label hypotheses) :
    (adaBoostErrors state label hypotheses hvalid).length = hypotheses.length := by
  induction hypotheses generalizing state with
  | nil => rfl
  | cons hypothesis remaining ih =>
      let herror := Classical.choose hvalid
      have hrest : AdaBoostAdmissible
          (adaBoostStep state label hypothesis herror) label remaining :=
        Classical.choose_spec hvalid
      change
        (adaBoostError state label hypothesis ::
          adaBoostErrors (adaBoostStep state label hypothesis herror) label remaining hrest).length =
          (hypothesis :: remaining).length
      simp only [List.length_cons]
      rw [ih (state := adaBoostStep state label hypothesis herror) hrest]

/-- A mapped finite-list sum is constant when every list entry has one value. -/
theorem list_map_sum_eq_length_mul_of_forall_eq
    {α : Type*} (values : List α) (f : α → ℝ) (value : α)
    (hvalue : ∀ current ∈ values, current = value) :
    (values.map f).sum = (values.length : ℝ) * f value := by
  induction values with
  | nil => simp
  | cons current remaining ih =>
      have hcurrent : current = value := hvalue current (by simp)
      have hremaining : ∀ later ∈ remaining, later = value := by
        intro later hlater
        exact hvalue later (by simp [hlater])
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
      rw [hcurrent, ih hremaining]
      ring

/--
Eq. (22)'s first equality: when every weak hypothesis has one common error,
the Theorem-6 product is an exponential with one repeated binary-KL term.
-/
theorem adaBoostTheorem6Factor_eq_exp_neg_length_mul_binaryKL_of_uniform_error
    {Training : Type*} [Fintype Training] [Nonempty Training]
    (state : HedgeWeightState Training) (label : Training → ℝ)
    (hypotheses : List (Training → ℝ))
    (hvalid : AdaBoostAdmissible state label hypotheses)
    (error : ℝ) (herror : 0 < error ∧ error < 1)
    (huniform : ∀ observed ∈ adaBoostErrors state label hypotheses hvalid, observed = error) :
    adaBoostTheorem6Factor state label hypotheses hvalid =
      Real.exp (-(hypotheses.length : ℝ) * Probability.binaryKLDivergence (1 / 2) error) := by
  rw [adaBoostTheorem6Factor_eq_exp_neg_binaryKLSum]
  have hsum := list_map_sum_eq_length_mul_of_forall_eq
    (adaBoostErrors state label hypotheses hvalid)
    (fun observed => Probability.binaryKLDivergence (1 / 2) observed) error huniform
  rw [hsum, adaBoostErrors_length]
  congr 1
  dsimp
  ring

/--
Eq. (22)'s closed factor when all errors are `1/2 - gamma`.
-/
theorem adaBoostTheorem6Factor_eq_uniform_edge_rpow
    {Training : Type*} [Fintype Training] [Nonempty Training]
    (state : HedgeWeightState Training) (label : Training → ℝ)
    (hypotheses : List (Training → ℝ))
    (hvalid : AdaBoostAdmissible state label hypotheses)
    (gamma : ℝ) (hgamma_lower : -(1 / 2 : ℝ) < gamma)
    (hgamma_upper : gamma < 1 / 2)
    (huniform : ∀ observed ∈ adaBoostErrors state label hypotheses hvalid,
      observed = 1 / 2 - gamma) :
    adaBoostTheorem6Factor state label hypotheses hvalid =
      (1 - 4 * gamma ^ 2) ^ ((hypotheses.length : ℝ) / 2) := by
  have herror : 0 < 1 / 2 - gamma ∧ 1 / 2 - gamma < 1 := by
    constructor <;> linarith
  calc
    adaBoostTheorem6Factor state label hypotheses hvalid =
        Real.exp (-(hypotheses.length : ℝ) *
          Probability.binaryKLDivergence (1 / 2) (1 / 2 - gamma)) :=
      adaBoostTheorem6Factor_eq_exp_neg_length_mul_binaryKL_of_uniform_error
        state label hypotheses hvalid (1 / 2 - gamma) herror huniform
    _ = (1 - 4 * gamma ^ 2) ^ ((hypotheses.length : ℝ) / 2) :=
      Probability.exp_neg_nat_mul_binaryKLDivergence_half_half_sub_eq_rpow
        hgamma_lower hgamma_upper hypotheses.length

/--
If an iteration count reaches the binary-KL threshold in Eq. (23), its
exponential error bound is at most the prescribed target error.
-/
theorem exp_neg_nat_mul_binaryKL_le_target_of_iteration_count
    {gamma target : ℝ} (hgamma_pos : 0 < gamma) (hgamma_upper : gamma < 1 / 2)
    (htarget_pos : 0 < target) (htarget_lt_one : target < 1)
    (rounds : ℕ)
    (hcount : Real.log (1 / target) /
      Probability.binaryKLDivergence (1 / 2) (1 / 2 - gamma) ≤ (rounds : ℝ)) :
    Real.exp (-(rounds : ℝ) *
      Probability.binaryKLDivergence (1 / 2) (1 / 2 - gamma)) ≤ target := by
  have hkl_lower := Probability.two_mul_sq_le_binaryKLDivergence_half_half_sub
    (gamma := gamma) (by linarith) hgamma_upper
  have hquadratic_pos : 0 < 2 * gamma ^ 2 := by positivity
  have hkl_pos : 0 < Probability.binaryKLDivergence (1 / 2) (1 / 2 - gamma) :=
    lt_of_lt_of_le hquadratic_pos hkl_lower
  have hlog_le : Real.log (1 / target) ≤
      (rounds : ℝ) * Probability.binaryKLDivergence (1 / 2) (1 / 2 - gamma) :=
    (div_le_iff₀ hkl_pos).mp hcount
  have hlog_target : Real.log target = -Real.log (1 / target) := by
    simp only [one_div, Real.log_inv]
    ring
  calc
    Real.exp (-(rounds : ℝ) *
        Probability.binaryKLDivergence (1 / 2) (1 / 2 - gamma)) ≤
        Real.exp (Real.log target) := by
          apply Real.exp_le_exp.mpr
          rw [hlog_target]
          linarith
    _ = target := Real.exp_log htarget_pos

/--
The KL iteration threshold in Eq. (23) is at most its familiar
`1 / (2 gamma^2)` upper bound.
-/
theorem binaryKL_iteration_threshold_le_quadratic_threshold
    {gamma target : ℝ} (hgamma_pos : 0 < gamma) (hgamma_upper : gamma < 1 / 2)
    (htarget_pos : 0 < target) (htarget_lt_one : target < 1) :
    Real.log (1 / target) /
        Probability.binaryKLDivergence (1 / 2) (1 / 2 - gamma) ≤
      Real.log (1 / target) / (2 * gamma ^ 2) := by
  have hkl_lower := Probability.two_mul_sq_le_binaryKLDivergence_half_half_sub
    (gamma := gamma) (by linarith) hgamma_upper
  have hquadratic_pos : 0 < 2 * gamma ^ 2 := by positivity
  have htarget_inv_gt_one : 1 < 1 / target := by
    apply (lt_div_iff₀ htarget_pos).mpr
    linarith
  have hlog_nonneg : 0 ≤ Real.log (1 / target) :=
    (Real.log_pos htarget_inv_gt_one).le
  exact div_le_div_of_nonneg_left hlog_nonneg hquadratic_pos hkl_lower

/--
The Eq. (23) quadratic iteration budget is sufficient for the finite
Theorem-6 training-error target when every weak learner has edge `gamma`.
-/
theorem adaBoost_training_error_le_target_of_uniform_edge_quadratic_iterations
    {Training : Type*} [Fintype Training] [DecidableEq Training] [Nonempty Training]
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
    (hquadratic_count : Real.log (1 / target) / (2 * gamma ^ 2) ≤
      (hypotheses.length : ℝ)) :
    adaBoostTrainingError state label hypotheses hvalid ≤ target := by
  have htheorem6 := adaBoost_training_error_le_theorem6Factor state label hstate_total
    hlabel_unit hlabel_boolean hypotheses hhypothesis hvalid
  have hfactor := adaBoostTheorem6Factor_eq_exp_neg_length_mul_binaryKL_of_uniform_error
    state label hypotheses hvalid (1 / 2 - gamma) (by constructor <;> linarith) huniform
  have hkl_count : Real.log (1 / target) /
      Probability.binaryKLDivergence (1 / 2) (1 / 2 - gamma) ≤
        (hypotheses.length : ℝ) :=
    (binaryKL_iteration_threshold_le_quadratic_threshold hgamma_pos hgamma_upper
      htarget_pos htarget_lt_one).trans hquadratic_count
  calc
    adaBoostTrainingError state label hypotheses hvalid ≤
        adaBoostTheorem6Factor state label hypotheses hvalid := htheorem6
    _ = Real.exp (-(hypotheses.length : ℝ) *
        Probability.binaryKLDivergence (1 / 2) (1 / 2 - gamma)) := hfactor
    _ ≤ target := exp_neg_nat_mul_binaryKL_le_target_of_iteration_count
      hgamma_pos hgamma_upper htarget_pos htarget_lt_one hypotheses.length hkl_count

/-- The normalized final vote `r(x)` used in Freund--Schapire Theorem 9. -/
noncomputable def adaBoostNormalizedVote
    {Training : Type*} [Fintype Training] [Nonempty Training]
    (state : HedgeWeightState Training) (label : Training → ℝ)
    (hypotheses : List (Training → ℝ))
    (hvalid : AdaBoostAdmissible state label hypotheses) : Training → ℝ :=
  fun sample =>
    adaBoostVote state label hypotheses hvalid sample /
      adaBoostVoteWeightSum state label hypotheses hvalid

/-- The source product `∏_t β_t^q` for a common real exponent `q`. -/
noncomputable def adaBoostDiscountPowerFactor
    {Training : Type*} [Fintype Training] [Nonempty Training]
    (state : HedgeWeightState Training) (label : Training → ℝ) :
    (hypotheses : List (Training → ℝ)) →
      AdaBoostAdmissible state label hypotheses → ℝ → ℝ
  | [], _, _ => 1
  | hypothesis :: remaining, hvalid, exponent =>
      adaBoostDiscount (adaBoostError state label hypothesis) ^ exponent *
        adaBoostDiscountPowerFactor
          (adaBoostStep state label hypothesis (Classical.choose hvalid)) label remaining
          (Classical.choose_spec hvalid) exponent

/-- A source-faithful soft threshold for Theorem 9, restricted to its `[0,1]` domain. -/
def AdaBoostSoftThreshold
    {Training : Type*} [Fintype Training] [Nonempty Training]
    (state : HedgeWeightState Training) (label : Training → ℝ)
    (hypotheses : List (Training → ℝ))
    (hvalid : AdaBoostAdmissible state label hypotheses) (threshold : ℝ → ℝ) : Prop :=
  (∀ r, 0 ≤ r → r ≤ 1 → 0 ≤ threshold r ∧ threshold r ≤ 1) ∧
  (∀ r, 0 ≤ r → r ≤ 1 → threshold (1 - r) = 1 - threshold r) ∧
  (∀ r, 0 ≤ r → r ≤ 1 →
    threshold r ≤ (1 / 2 : ℝ) *
      adaBoostDiscountPowerFactor state label hypotheses hvalid (1 / 2 - r))

/-- The randomized final predictor obtained by applying a Theorem-9 soft threshold. -/
noncomputable def adaBoostSoftFinalHypothesis
    {Training : Type*} [Fintype Training] [Nonempty Training]
    (state : HedgeWeightState Training) (label : Training → ℝ)
    (hypotheses : List (Training → ℝ))
    (hvalid : AdaBoostAdmissible state label hypotheses) (threshold : ℝ → ℝ) : Training → ℝ :=
  fun sample => threshold (adaBoostNormalizedVote state label hypotheses hvalid sample)

/-- The finite randomized-prediction error used by Freund--Schapire Theorem 9. -/
noncomputable def adaBoostSoftTrainingError
    {Training : Type*} [Fintype Training] [Nonempty Training]
    (state : HedgeWeightState Training) (label : Training → ℝ)
    (hypotheses : List (Training → ℝ))
    (hvalid : AdaBoostAdmissible state label hypotheses) (threshold : ℝ → ℝ) : ℝ :=
  ∑ sample, state.weight sample *
    |adaBoostSoftFinalHypothesis state label hypotheses hvalid threshold sample - label sample|

/-- A weak learner with error below one half has a strictly positive final-vote weight. -/
theorem adaBoostVoteWeight_pos_of_error_lt_half
    {error : ℝ} (herror : 0 < error ∧ error < 1 / 2) :
    0 < adaBoostVoteWeight error := by
  unfold adaBoostVoteWeight adaBoostDiscount
  have hcomplement_pos : 0 < 1 - error := by linarith
  have hone_lt_ratio : 1 < (1 - error) / error := by
    apply (lt_div_iff₀ herror.1).mpr
    linarith
  have hinv : 1 / (error / (1 - error)) = (1 - error) / error := by
    field_simp [herror.1.ne', hcomplement_pos.ne']
  rw [hinv]
  exact Real.log_pos hone_lt_ratio

/-- A weak learner with error at most one half has a nonnegative final-vote weight. -/
theorem adaBoostVoteWeight_nonneg_of_error_le_half
    {error : ℝ} (herror : 0 < error ∧ error ≤ 1 / 2) :
    0 ≤ adaBoostVoteWeight error := by
  rcases lt_or_eq_of_le herror.2 with hlt | heq
  · exact (adaBoostVoteWeight_pos_of_error_lt_half ⟨herror.1, hlt⟩).le
  · rw [heq]
    norm_num [adaBoostVoteWeight, adaBoostDiscount]

/-- Under nonpositive weak-learning loss, every final-vote coefficient is nonnegative. -/
theorem adaBoostVoteWeightSum_nonneg_of_errors_le_half
    {Training : Type*} [Fintype Training] [Nonempty Training]
    (state : HedgeWeightState Training) (label : Training → ℝ)
    (hypotheses : List (Training → ℝ))
    (hvalid : AdaBoostAdmissible state label hypotheses)
    (hweak : ∀ error ∈ adaBoostErrors state label hypotheses hvalid, error ≤ 1 / 2) :
    0 ≤ adaBoostVoteWeightSum state label hypotheses hvalid := by
  induction hypotheses generalizing state with
  | nil => simp [adaBoostVoteWeightSum]
  | cons hypothesis remaining ih =>
      let herror := Classical.choose hvalid
      have hrest : AdaBoostAdmissible
          (adaBoostStep state label hypothesis herror) label remaining :=
        Classical.choose_spec hvalid
      have hhead : adaBoostError state label hypothesis ≤ 1 / 2 := by
        apply hweak (adaBoostError state label hypothesis)
        simp [adaBoostErrors]
      have hweak_rest : ∀ error ∈
          adaBoostErrors (adaBoostStep state label hypothesis herror) label remaining hrest,
          error ≤ 1 / 2 := by
        intro error hmem
        apply hweak error
        simp [adaBoostErrors, hmem]
      change
        0 ≤ adaBoostVoteWeight (adaBoostError state label hypothesis) +
          adaBoostVoteWeightSum
            (adaBoostStep state label hypothesis herror) label remaining hrest
      exact add_nonneg
        (adaBoostVoteWeight_nonneg_of_error_le_half ⟨herror.1, hhead⟩)
        (ih (state := adaBoostStep state label hypothesis herror) hrest hweak_rest)

/-- A nonempty positive-edge run has a strictly positive total final-vote weight. -/
theorem adaBoostVoteWeightSum_pos_of_nonempty_errors_lt_half
    {Training : Type*} [Fintype Training] [Nonempty Training]
    (state : HedgeWeightState Training) (label : Training → ℝ)
    (hypotheses : List (Training → ℝ))
    (hvalid : AdaBoostAdmissible state label hypotheses)
    (hnonempty : hypotheses ≠ [])
    (hweak : ∀ error ∈ adaBoostErrors state label hypotheses hvalid, error < 1 / 2) :
    0 < adaBoostVoteWeightSum state label hypotheses hvalid := by
  cases hypotheses with
  | nil => exact False.elim (hnonempty rfl)
  | cons hypothesis remaining =>
      let herror := Classical.choose hvalid
      have hrest : AdaBoostAdmissible
          (adaBoostStep state label hypothesis herror) label remaining :=
        Classical.choose_spec hvalid
      have hhead : adaBoostError state label hypothesis < 1 / 2 := by
        apply hweak (adaBoostError state label hypothesis)
        simp [adaBoostErrors]
      have hweak_rest : ∀ error ∈
          adaBoostErrors (adaBoostStep state label hypothesis herror) label remaining hrest,
          error < 1 / 2 := by
        intro error hmem
        apply hweak error
        simp [adaBoostErrors, hmem]
      change
        0 < adaBoostVoteWeight (adaBoostError state label hypothesis) +
          adaBoostVoteWeightSum
            (adaBoostStep state label hypothesis herror) label remaining hrest
      exact add_pos_of_pos_of_nonneg
        (adaBoostVoteWeight_pos_of_error_lt_half ⟨herror.1, hhead⟩)
        (adaBoostVoteWeightSum_nonneg_of_errors_le_half
          (adaBoostStep state label hypothesis herror) label remaining hrest
          (fun error hmem => (hweak_rest error hmem).le))

/-- A weak-edge final vote is nonnegative on a unit-valued weak hypothesis class. -/
theorem adaBoostVote_nonneg_of_errors_le_half
    {Training : Type*} [Fintype Training] [Nonempty Training]
    (state : HedgeWeightState Training) (label : Training → ℝ)
    (hypotheses : List (Training → ℝ))
    (hhypothesis : ∀ hypothesis ∈ hypotheses, ∀ sample,
      0 ≤ hypothesis sample ∧ hypothesis sample ≤ 1)
    (hvalid : AdaBoostAdmissible state label hypotheses)
    (hweak : ∀ error ∈ adaBoostErrors state label hypotheses hvalid, error ≤ 1 / 2)
    (sample : Training) :
    0 ≤ adaBoostVote state label hypotheses hvalid sample := by
  induction hypotheses generalizing state with
  | nil => simp [adaBoostVote]
  | cons hypothesis remaining ih =>
      let herror := Classical.choose hvalid
      have hrest : AdaBoostAdmissible
          (adaBoostStep state label hypothesis herror) label remaining :=
        Classical.choose_spec hvalid
      have hhypothesis_head : ∀ sample,
          0 ≤ hypothesis sample ∧ hypothesis sample ≤ 1 :=
        hhypothesis hypothesis (by simp)
      have hhypothesis_rest : ∀ next ∈ remaining, ∀ other,
          0 ≤ next other ∧ next other ≤ 1 := by
        intro next hnext other
        exact hhypothesis next (by simp [hnext]) other
      have hhead : adaBoostError state label hypothesis ≤ 1 / 2 := by
        apply hweak (adaBoostError state label hypothesis)
        simp [adaBoostErrors]
      have hweak_rest : ∀ error ∈
          adaBoostErrors (adaBoostStep state label hypothesis herror) label remaining hrest,
          error ≤ 1 / 2 := by
        intro error hmem
        apply hweak error
        simp [adaBoostErrors, hmem]
      change
        0 ≤ adaBoostVoteWeight (adaBoostError state label hypothesis) * hypothesis sample +
          adaBoostVote (adaBoostStep state label hypothesis herror) label remaining hrest sample
      exact add_nonneg
        (mul_nonneg
          (adaBoostVoteWeight_nonneg_of_error_le_half ⟨herror.1, hhead⟩)
          (hhypothesis_head sample).1)
        (ih (state := adaBoostStep state label hypothesis herror)
          hhypothesis_rest hrest hweak_rest)

/-- A weak-edge final vote is at most its total coefficient weight. -/
theorem adaBoostVote_le_weightSum_of_errors_le_half
    {Training : Type*} [Fintype Training] [Nonempty Training]
    (state : HedgeWeightState Training) (label : Training → ℝ)
    (hypotheses : List (Training → ℝ))
    (hhypothesis : ∀ hypothesis ∈ hypotheses, ∀ sample,
      0 ≤ hypothesis sample ∧ hypothesis sample ≤ 1)
    (hvalid : AdaBoostAdmissible state label hypotheses)
    (hweak : ∀ error ∈ adaBoostErrors state label hypotheses hvalid, error ≤ 1 / 2)
    (sample : Training) :
    adaBoostVote state label hypotheses hvalid sample ≤
      adaBoostVoteWeightSum state label hypotheses hvalid := by
  induction hypotheses generalizing state with
  | nil => simp [adaBoostVote, adaBoostVoteWeightSum]
  | cons hypothesis remaining ih =>
      let herror := Classical.choose hvalid
      have hrest : AdaBoostAdmissible
          (adaBoostStep state label hypothesis herror) label remaining :=
        Classical.choose_spec hvalid
      have hhypothesis_head : ∀ sample,
          0 ≤ hypothesis sample ∧ hypothesis sample ≤ 1 :=
        hhypothesis hypothesis (by simp)
      have hhypothesis_rest : ∀ next ∈ remaining, ∀ other,
          0 ≤ next other ∧ next other ≤ 1 := by
        intro next hnext other
        exact hhypothesis next (by simp [hnext]) other
      have hhead : adaBoostError state label hypothesis ≤ 1 / 2 := by
        apply hweak (adaBoostError state label hypothesis)
        simp [adaBoostErrors]
      have hweak_rest : ∀ error ∈
          adaBoostErrors (adaBoostStep state label hypothesis herror) label remaining hrest,
          error ≤ 1 / 2 := by
        intro error hmem
        apply hweak error
        simp [adaBoostErrors, hmem]
      have hcoefficient_nonneg :
          0 ≤ adaBoostVoteWeight (adaBoostError state label hypothesis) :=
        adaBoostVoteWeight_nonneg_of_error_le_half ⟨herror.1, hhead⟩
      have hhead_le :
          adaBoostVoteWeight (adaBoostError state label hypothesis) * hypothesis sample ≤
            adaBoostVoteWeight (adaBoostError state label hypothesis) := by
        nlinarith [(hhypothesis_head sample).2]
      have htail := ih (state := adaBoostStep state label hypothesis herror)
        hhypothesis_rest hrest hweak_rest
      change
        adaBoostVoteWeight (adaBoostError state label hypothesis) * hypothesis sample +
            adaBoostVote (adaBoostStep state label hypothesis herror) label remaining hrest sample ≤
          adaBoostVoteWeight (adaBoostError state label hypothesis) +
            adaBoostVoteWeightSum
              (adaBoostStep state label hypothesis herror) label remaining hrest
      exact add_le_add hhead_le htail

/-- The Theorem-9 normalized vote lies in `[0,1]` whenever its total weight is positive. -/
theorem adaBoostNormalizedVote_mem_Icc_of_errors_le_half
    {Training : Type*} [Fintype Training] [Nonempty Training]
    (state : HedgeWeightState Training) (label : Training → ℝ)
    (hypotheses : List (Training → ℝ))
    (hhypothesis : ∀ hypothesis ∈ hypotheses, ∀ sample,
      0 ≤ hypothesis sample ∧ hypothesis sample ≤ 1)
    (hvalid : AdaBoostAdmissible state label hypotheses)
    (hweak : ∀ error ∈ adaBoostErrors state label hypotheses hvalid, error ≤ 1 / 2)
    (hweight_pos : 0 < adaBoostVoteWeightSum state label hypotheses hvalid)
    (sample : Training) :
    0 ≤ adaBoostNormalizedVote state label hypotheses hvalid sample ∧
      adaBoostNormalizedVote state label hypotheses hvalid sample ≤ 1 := by
  have hvote_nonneg : 0 ≤ adaBoostVote state label hypotheses hvalid sample :=
    adaBoostVote_nonneg_of_errors_le_half state label hypotheses hhypothesis hvalid hweak sample
  have hvote_le : adaBoostVote state label hypotheses hvalid sample ≤
      adaBoostVoteWeightSum state label hypotheses hvalid :=
    adaBoostVote_le_weightSum_of_errors_le_half state label hypotheses hhypothesis hvalid hweak sample
  constructor
  · exact div_nonneg hvote_nonneg hweight_pos.le
  · exact (div_le_iff₀ hweight_pos).mpr (by simpa using hvote_le)

/-- The source power product is the exponential of minus the common exponent times total vote weight. -/
theorem adaBoostDiscountPowerFactor_eq_exp_neg_mul_voteWeightSum
    {Training : Type*} [Fintype Training] [Nonempty Training]
    (state : HedgeWeightState Training) (label : Training → ℝ)
    (hypotheses : List (Training → ℝ))
    (hvalid : AdaBoostAdmissible state label hypotheses) (exponent : ℝ) :
    adaBoostDiscountPowerFactor state label hypotheses hvalid exponent =
      Real.exp (-exponent * adaBoostVoteWeightSum state label hypotheses hvalid) := by
  induction hypotheses generalizing state with
  | nil => simp [adaBoostDiscountPowerFactor, adaBoostVoteWeightSum]
  | cons hypothesis remaining ih =>
      let herror := Classical.choose hvalid
      have hrest : AdaBoostAdmissible
          (adaBoostStep state label hypothesis herror) label remaining :=
        Classical.choose_spec hvalid
      have hdiscount : 0 < adaBoostDiscount (adaBoostError state label hypothesis) := by
        unfold adaBoostDiscount
        exact div_pos herror.1 (sub_pos.mpr herror.2)
      have htail := ih (state := adaBoostStep state label hypothesis herror) hrest
      change
        adaBoostDiscount (adaBoostError state label hypothesis) ^ exponent *
            adaBoostDiscountPowerFactor
              (adaBoostStep state label hypothesis herror) label remaining hrest exponent =
          Real.exp (-exponent *
            (adaBoostVoteWeight (adaBoostError state label hypothesis) +
              adaBoostVoteWeightSum
                (adaBoostStep state label hypothesis herror) label remaining hrest))
      rw [Real.rpow_def_of_pos hdiscount, htail, ← Real.exp_add]
      congr 1
      simp only [adaBoostVoteWeight, one_div, Real.log_inv]
      ring

/-- The weighted absolute error is total vote weight times the normalized-vote distance to a Boolean label. -/
theorem adaBoostWeightedAbsoluteError_eq_weightSum_mul_abs_normalizedVote_sub_label
    {Training : Type*} [Fintype Training] [Nonempty Training]
    (state : HedgeWeightState Training) (label : Training → ℝ)
    (hypotheses : List (Training → ℝ))
    (hhypothesis : ∀ hypothesis ∈ hypotheses, ∀ sample,
      0 ≤ hypothesis sample ∧ hypothesis sample ≤ 1)
    (hvalid : AdaBoostAdmissible state label hypotheses)
    (sample : Training)
    (hnormalized : 0 ≤ adaBoostNormalizedVote state label hypotheses hvalid sample ∧
      adaBoostNormalizedVote state label hypotheses hvalid sample ≤ 1)
    (hweight_ne : adaBoostVoteWeightSum state label hypotheses hvalid ≠ 0)
    (hlabel : label sample = 0 ∨ label sample = 1) :
    adaBoostWeightedAbsoluteError state label hypotheses hvalid sample =
      adaBoostVoteWeightSum state label hypotheses hvalid *
        |adaBoostNormalizedVote state label hypotheses hvalid sample - label sample| := by
  rcases hlabel with hzero | hone
  · rw [hzero, sub_zero, abs_of_nonneg hnormalized.1,
      adaBoostWeightedAbsoluteError_eq_vote_of_label_eq_zero state label hypotheses
        hhypothesis hvalid sample hzero]
    unfold adaBoostNormalizedVote
    field_simp [hweight_ne]
  · rw [adaBoostWeightedAbsoluteError_eq_weightSum_sub_vote_of_label_eq_one
      state label hypotheses hhypothesis hvalid sample hone, hone]
    have habs : |adaBoostNormalizedVote state label hypotheses hvalid sample - 1| =
        1 - adaBoostNormalizedVote state label hypotheses hvalid sample := by
      rw [abs_of_nonpos (sub_nonpos.mpr hnormalized.2)]
      ring
    rw [habs]
    unfold adaBoostNormalizedVote
    field_simp [hweight_ne]

/-- The source's Theorem-9 power product equals its final sample-weight ratio. -/
theorem adaBoostDiscountPowerFactor_eq_sampleWeightFactor_div_halfDiscountFactor
    {Training : Type*} [Fintype Training] [Nonempty Training]
    (state : HedgeWeightState Training) (label : Training → ℝ)
    (hypotheses : List (Training → ℝ))
    (hhypothesis : ∀ hypothesis ∈ hypotheses, ∀ sample,
      0 ≤ hypothesis sample ∧ hypothesis sample ≤ 1)
    (hvalid : AdaBoostAdmissible state label hypotheses)
    (sample : Training)
    (hnormalized : 0 ≤ adaBoostNormalizedVote state label hypotheses hvalid sample ∧
      adaBoostNormalizedVote state label hypotheses hvalid sample ≤ 1)
    (hweight_ne : adaBoostVoteWeightSum state label hypotheses hvalid ≠ 0)
    (hlabel : label sample = 0 ∨ label sample = 1) :
    adaBoostDiscountPowerFactor state label hypotheses hvalid
        (1 / 2 - |adaBoostNormalizedVote state label hypotheses hvalid sample - label sample|) =
      adaBoostSampleWeightFactor state label hypotheses hvalid sample /
        adaBoostHalfDiscountFactor state label hypotheses hvalid := by
  have hdistance := adaBoostWeightedAbsoluteError_eq_weightSum_mul_abs_normalizedVote_sub_label
    state label hypotheses hhypothesis hvalid sample hnormalized hweight_ne hlabel
  rw [adaBoostDiscountPowerFactor_eq_exp_neg_mul_voteWeightSum,
    adaBoostSampleWeightFactor_eq_exp_log,
    adaBoostHalfDiscountFactor_eq_exp_neg_half_weightSum, ← Real.exp_sub]
  congr 1
  rw [adaBoostLogSampleWeightFactor_eq_weightedAbsoluteError_sub_weightSum, hdistance]
  ring

/-- The distance from a normalized vote to a Boolean label remains in `[0,1]`. -/
theorem abs_sub_boolean_mem_Icc
    {r y : ℝ} (hr : 0 ≤ r ∧ r ≤ 1) (hy : y = 0 ∨ y = 1) :
    0 ≤ |r - y| ∧ |r - y| ≤ 1 := by
  rcases hy with hzero | hone
  · rw [hzero, sub_zero, abs_of_nonneg hr.1]
    exact hr
  · rw [hone]
    have habs : |r - 1| = 1 - r := by
      rw [abs_of_nonpos (sub_nonpos.mpr hr.2)]
      ring
    rw [habs]
    constructor <;> linarith

/-- Soft-threshold symmetry converts randomized error into threshold mass at label distance. -/
theorem adaBoostSoftFinalHypothesis_abs_sub_label_eq_threshold_abs_normalizedVote_sub_label
    {Training : Type*} [Fintype Training] [Nonempty Training]
    (state : HedgeWeightState Training) (label : Training → ℝ)
    (hypotheses : List (Training → ℝ))
    (hvalid : AdaBoostAdmissible state label hypotheses)
    (sample : Training)
    (hnormalized : 0 ≤ adaBoostNormalizedVote state label hypotheses hvalid sample ∧
      adaBoostNormalizedVote state label hypotheses hvalid sample ≤ 1)
    (threshold : ℝ → ℝ)
    (hthreshold : AdaBoostSoftThreshold state label hypotheses hvalid threshold)
    (hlabel : label sample = 0 ∨ label sample = 1) :
    |adaBoostSoftFinalHypothesis state label hypotheses hvalid threshold sample - label sample| =
      threshold |adaBoostNormalizedVote state label hypotheses hvalid sample - label sample| := by
  change
    |threshold (adaBoostNormalizedVote state label hypotheses hvalid sample) - label sample| =
      threshold |adaBoostNormalizedVote state label hypotheses hvalid sample - label sample|
  rcases hlabel with hzero | hone
  · have habs : |adaBoostNormalizedVote state label hypotheses hvalid sample - 0| =
        adaBoostNormalizedVote state label hypotheses hvalid sample := by
      rw [sub_zero, abs_of_nonneg hnormalized.1]
    rw [hzero, habs, sub_zero,
      abs_of_nonneg (hthreshold.1 _ hnormalized.1 hnormalized.2).1]
  · rw [hone]
    have habs : |adaBoostNormalizedVote state label hypotheses hvalid sample - 1| =
        1 - adaBoostNormalizedVote state label hypotheses hvalid sample := by
      rw [abs_of_nonpos (sub_nonpos.mpr hnormalized.2)]
      ring
    calc
      |threshold (adaBoostNormalizedVote state label hypotheses hvalid sample) - 1| =
          -(threshold (adaBoostNormalizedVote state label hypotheses hvalid sample) - 1) :=
        abs_of_nonpos (sub_nonpos.mpr (hthreshold.1 _ hnormalized.1 hnormalized.2).2)
      _ = 1 - threshold (adaBoostNormalizedVote state label hypotheses hvalid sample) := by ring
      _ = threshold (1 - adaBoostNormalizedVote state label hypotheses hvalid sample) :=
        (hthreshold.2.1 _ hnormalized.1 hnormalized.2).symm
      _ = threshold |adaBoostNormalizedVote state label hypotheses hvalid sample - 1| := by
        rw [habs]

/--
Freund--Schapire (1997), Theorem 9, in the finite source model.  The vote-weight
sum is nonzero and every normalized vote lies in the source threshold's stated
domain `[0,1]`.  These exact domain conditions do not impose a weak-edge bound;
every source-admissible soft threshold improves the Theorem-6 product by a
factor of two.
-/
theorem adaBoost_softTrainingError_le_half_theorem6Factor
    {Training : Type*} [Fintype Training] [DecidableEq Training] [Nonempty Training]
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
      adaBoostTheorem6Factor state label hypotheses hvalid / 2 := by
  classical
  have hhalf_pos : 0 < adaBoostHalfDiscountFactor state label hypotheses hvalid :=
    adaBoostHalfDiscountFactor_pos state label hypotheses hvalid
  have hpointwise : ∀ sample,
      |adaBoostSoftFinalHypothesis state label hypotheses hvalid threshold sample - label sample| ≤
        (1 / 2 : ℝ) *
          (adaBoostSampleWeightFactor state label hypotheses hvalid sample /
            adaBoostHalfDiscountFactor state label hypotheses hvalid) := by
    intro sample
    have hdistance := abs_sub_boolean_mem_Icc (hnormalized sample) (hlabel_boolean sample)
    calc
      |adaBoostSoftFinalHypothesis state label hypotheses hvalid threshold sample - label sample| =
          threshold |adaBoostNormalizedVote state label hypotheses hvalid sample - label sample| :=
        adaBoostSoftFinalHypothesis_abs_sub_label_eq_threshold_abs_normalizedVote_sub_label
          state label hypotheses hvalid sample (hnormalized sample) threshold hthreshold
          (hlabel_boolean sample)
      _ ≤ (1 / 2 : ℝ) * adaBoostDiscountPowerFactor state label hypotheses hvalid
          (1 / 2 - |adaBoostNormalizedVote state label hypotheses hvalid sample - label sample|) :=
        hthreshold.2.2 _ hdistance.1 hdistance.2
      _ = (1 / 2 : ℝ) *
          (adaBoostSampleWeightFactor state label hypotheses hvalid sample /
            adaBoostHalfDiscountFactor state label hypotheses hvalid) := by
        rw [adaBoostDiscountPowerFactor_eq_sampleWeightFactor_div_halfDiscountFactor
          state label hypotheses hhypothesis hvalid sample (hnormalized sample) hweight_ne
          (hlabel_boolean sample)]
  have hfinal_total_eq :
      (∑ sample, (adaBoostRun state label hypotheses hvalid).weight sample) =
        ∑ sample, state.weight sample *
          adaBoostSampleWeightFactor state label hypotheses hvalid sample := by
    apply Finset.sum_congr rfl
    intro sample _
    exact adaBoostRun_weight state label hypotheses hvalid sample
  have hsum_eq :
      (∑ sample, state.weight sample *
        ((1 / 2 : ℝ) *
          (adaBoostSampleWeightFactor state label hypotheses hvalid sample /
            adaBoostHalfDiscountFactor state label hypotheses hvalid))) =
        (1 / 2 : ℝ) *
          ((∑ sample, (adaBoostRun state label hypotheses hvalid).weight sample) /
            adaBoostHalfDiscountFactor state label hypotheses hvalid) := by
    rw [hfinal_total_eq]
    calc
      (∑ sample, state.weight sample *
        ((1 / 2 : ℝ) *
          (adaBoostSampleWeightFactor state label hypotheses hvalid sample /
            adaBoostHalfDiscountFactor state label hypotheses hvalid))) =
          ∑ sample, ((1 / 2 : ℝ) /
            adaBoostHalfDiscountFactor state label hypotheses hvalid) *
              (state.weight sample * adaBoostSampleWeightFactor state label hypotheses hvalid sample) := by
            apply Finset.sum_congr rfl
            intro sample _
            field_simp [hhalf_pos.ne']
      _ = ((1 / 2 : ℝ) / adaBoostHalfDiscountFactor state label hypotheses hvalid) *
          ∑ sample, state.weight sample *
            adaBoostSampleWeightFactor state label hypotheses hvalid sample := by
            rw [Finset.mul_sum]
      _ = (1 / 2 : ℝ) *
          ((∑ sample, state.weight sample *
            adaBoostSampleWeightFactor state label hypotheses hvalid sample) /
              adaBoostHalfDiscountFactor state label hypotheses hvalid) := by
            field_simp [hhalf_pos.ne']
  have htotal_le := adaBoostRun_total_le_errorFactors state label
    (fun sample => by
      rcases hlabel_boolean sample with hzero | hone
      · rw [hzero]
        norm_num
      · rw [hone]
        norm_num)
    hypotheses hhypothesis hvalid
  have hfinal_le :
      (∑ sample, (adaBoostRun state label hypotheses hvalid).weight sample) ≤
        ((adaBoostErrors state label hypotheses hvalid).map (fun error => 2 * error)).prod := by
    simpa [hstate_total] using htotal_le
  have hdiv_le :
      (∑ sample, (adaBoostRun state label hypotheses hvalid).weight sample) /
          adaBoostHalfDiscountFactor state label hypotheses hvalid ≤
        ((adaBoostErrors state label hypotheses hvalid).map (fun error => 2 * error)).prod /
          adaBoostHalfDiscountFactor state label hypotheses hvalid :=
    (div_le_div_iff_of_pos_right hhalf_pos).mpr hfinal_le
  unfold adaBoostSoftTrainingError
  calc
    (∑ sample, state.weight sample *
      |adaBoostSoftFinalHypothesis state label hypotheses hvalid threshold sample - label sample|) ≤
        ∑ sample, state.weight sample *
          ((1 / 2 : ℝ) *
            (adaBoostSampleWeightFactor state label hypotheses hvalid sample /
              adaBoostHalfDiscountFactor state label hypotheses hvalid)) := by
      apply Finset.sum_le_sum
      intro sample _
      exact mul_le_mul_of_nonneg_left (hpointwise sample) (state.nonneg sample)
    _ = (1 / 2 : ℝ) *
        ((∑ sample, (adaBoostRun state label hypotheses hvalid).weight sample) /
          adaBoostHalfDiscountFactor state label hypotheses hvalid) := hsum_eq
    _ ≤ (1 / 2 : ℝ) *
        (((adaBoostErrors state label hypotheses hvalid).map (fun error => 2 * error)).prod /
          adaBoostHalfDiscountFactor state label hypotheses hvalid) :=
      mul_le_mul_of_nonneg_left hdiv_le (by norm_num)
    _ = adaBoostTheorem6Factor state label hypotheses hvalid / 2 := by
      rw [adaBoostErrorFactors_div_halfDiscountFactor_eq_theorem6Factor]
      ring

/-- The source's explicit Theorem-9 product, `2^(T-1) ∏ₜ √(εₜ(1-εₜ))`. -/
noncomputable def adaBoostTheorem9Factor
    {Training : Type*} [Fintype Training] [Nonempty Training]
    (state : HedgeWeightState Training) (label : Training → ℝ)
    (hypotheses : List (Training → ℝ))
    (hvalid : AdaBoostAdmissible state label hypotheses) : ℝ :=
  (2 : ℝ) ^ (hypotheses.length - 1) *
    ((adaBoostErrors state label hypotheses hvalid).map fun error =>
      Real.sqrt (error * (1 - error))).prod

/-- Factoring the roundwise twos from the Theorem-6 product. -/
theorem adaBoostErrorFactorProduct_eq_two_pow_mul_sqrtProduct (errors : List ℝ) :
    (errors.map fun error => 2 * Real.sqrt (error * (1 - error))).prod =
      (2 : ℝ) ^ errors.length *
        (errors.map fun error => Real.sqrt (error * (1 - error))).prod := by
  induction errors with
  | nil => norm_num
  | cons error remaining ih =>
      simp only [List.map_cons, List.prod_cons, List.length_cons]
      rw [ih]
      ring

/-- The half Theorem-6 factor is exactly the product printed in Theorem 9. -/
theorem adaBoostTheorem6Factor_div_two_eq_theorem9Factor
    {Training : Type*} [Fintype Training] [Nonempty Training]
    (state : HedgeWeightState Training) (label : Training → ℝ)
    (hypotheses : List (Training → ℝ))
    (hvalid : AdaBoostAdmissible state label hypotheses)
    (hnonempty : hypotheses ≠ []) :
    adaBoostTheorem6Factor state label hypotheses hvalid / 2 =
      adaBoostTheorem9Factor state label hypotheses hvalid := by
  rw [adaBoostTheorem6Factor_eq_errorFactorProduct,
    adaBoostErrorFactorProduct_eq_two_pow_mul_sqrtProduct]
  unfold adaBoostTheorem9Factor
  have hlength_pos : 0 < hypotheses.length := by
    cases hypotheses with
    | nil => exact False.elim (hnonempty rfl)
    | cons hypothesis remaining => simp
  have hlength : hypotheses.length = (hypotheses.length - 1) + 1 := by
    exact (Nat.sub_add_cancel (Nat.succ_le_iff.mpr hlength_pos)).symm
  rw [adaBoostErrors_length]
  conv_lhs => rw [hlength]
  rw [pow_succ]
  ring

/-- The exact source-product version of Freund--Schapire Theorem 9. -/
theorem adaBoost_softTrainingError_le_theorem9Factor
    {Training : Type*} [Fintype Training] [DecidableEq Training] [Nonempty Training]
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
  have hnonempty : hypotheses ≠ [] := by
    intro hnil
    subst hypotheses
    simp [adaBoostVoteWeightSum] at hweight_ne
  calc
    adaBoostSoftTrainingError state label hypotheses hvalid threshold ≤
        adaBoostTheorem6Factor state label hypotheses hvalid / 2 :=
      adaBoost_softTrainingError_le_half_theorem6Factor state label hstate_total hlabel_boolean
        hypotheses hhypothesis hvalid hweight_ne hnormalized threshold hthreshold
    _ = adaBoostTheorem9Factor state label hypotheses hvalid :=
      adaBoostTheorem6Factor_div_two_eq_theorem9Factor state label hypotheses hvalid hnonempty

end Online
end Learning
end AppliedModelingLib
