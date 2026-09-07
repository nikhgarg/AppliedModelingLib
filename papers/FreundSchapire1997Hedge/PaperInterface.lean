import AppliedModelingLib.Learning.Online.Hedge
import AppliedModelingLib.Learning.Online.AdaBoost
import AppliedModelingLib.Learning.Online.AdaBoostMulticlass
import AppliedModelingLib.Learning.Online.AdaBoostMulticlassM2
import AppliedModelingLib.Learning.Online.AdaBoostRegression
import AppliedModelingLib.Learning.Online.DecisionTheoreticHedge
import AppliedModelingLib.Learning.Online.VovkGlobalGame
import AppliedModelingLib.Learning.Statistics

/-!
# Paper interface: Freund--Schapire (1997) Hedge

The governing source is Freund and Schapire, *Journal of Computer and System
Sciences* 55(1):119--139 (1997). This interface records the selected online
allocation claims; its Theorem-3 endpoint uses the checked finite Vovk game
construction corresponding to the dependency cited in the paper's Appendix.
-/

namespace FreundSchapire1997Hedge

open AppliedModelingLib
open AppliedModelingLib.Learning.Online
open AppliedModelingLib.Statistics

/--
Finite source-facing specialization of Lemma 1.  `state.weight` is the
unnormalized vector `w¹`; `hedgeWeightStateRun` performs the source update
`wᵗ⁺¹_i = wᵗ_i β^(ℓᵗ_i)`, and the cumulative loss uses its normalized
allocation at every round.
-/
def lemma1_finite_weight_potentialSpec : Prop := by
  classical
  exact ∀ {Action : Type} [Fintype Action] [Nonempty Action]
    (discount : ℝ) (hdiscount : 0 < discount) (hdiscount_one : discount ≤ 1)
    (state : HedgeWeightState Action)
    (hinitial : (∑ action, state.weight action) = 1)
    (losses : List (Action → ℝ)),
    (∀ loss ∈ losses, ∀ action, 0 ≤ loss action ∧ loss action ≤ 1) →
      Real.log
          (∑ action,
            (hedgeWeightStateRun discount hdiscount state losses).weight action) ≤
        -(1 - discount) *
          hedgeWeightStateCumulativeLoss discount hdiscount state losses

/--
Full finite source reading of Theorem 2.  The first conjunct is the printed
single-strategy bound (7), and the second is the nonempty-subset bound (8).
The explicit extended-real branch represents the source convention
`-log 0 = +∞` without using Lean's totalized real logarithm at zero.
-/
def theorem2_hedge_comparator_boundsSpec : Prop := by
  classical
  exact ∀ {Action : Type} [Fintype Action] [Nonempty Action]
    (discount : ℝ) (hdiscount : 0 < discount) (hdiscount_lt_one : discount < 1)
    (state : HedgeWeightState Action)
    (hinitial : (∑ action, state.weight action) = 1)
    (losses : List (Action → ℝ)),
    (∀ loss ∈ losses, ∀ action, 0 ≤ loss action ∧ loss action ≤ 1) →
      (∀ action,
        (hedgeWeightStateCumulativeLoss discount hdiscount state losses : EReal) ≤
          hedgeWeightStateSubsetComparatorExtendedBound discount
            (state.weight action)
            ((losses.map fun loss => loss action).sum)) ∧
      (∀ (selected : Finset Action) (hselected : selected.Nonempty),
        (hedgeWeightStateCumulativeLoss discount hdiscount state losses : EReal) ≤
          hedgeWeightStateSubsetComparatorExtendedBound discount
            (∑ action ∈ selected, state.weight action)
            (selected.sup' hselected (fun action =>
              (losses.map fun loss => loss action).sum)))

/--
Source-facing necessary direction of Theorem 3.  A globally available family
of finite-expert allocation policies satisfying the source `(c,a)` template
must obey Vovk's two-constant tradeoff at every interior discount.
-/
def theorem3_global_allocation_lower_tradeoffSpec : Prop :=
  ∀ {discount c a : ℝ}, 0 < discount → discount < 1 → 0 < c → 0 < a →
    globalFiniteAllocationPolicyBounded c a →
      (-Real.log discount) / (1 - discount) ≤ c ∨
        1 / (1 - discount) ≤ a

/--
Freund--Schapire Lemma 4, including the `lossBound = 0` endpoint admitted by
the printed hypotheses. `hedgeDiscountFromBoundsClosed` uses the continuous
zero-loss-bound value of the displayed learning-rate choice.
-/
def lemma4_learning_rate_boundSpec : Prop :=
  ∀ (loss lossBound regret regretBound : ℝ),
    0 ≤ loss → loss ≤ lossBound → 0 < regret → regret ≤ regretBound →
      (-loss * Real.log (hedgeDiscountFromBoundsClosed lossBound regretBound) + regret) /
          (1 - hedgeDiscountFromBoundsClosed lossBound regretBound) ≤
        loss + Real.sqrt (2 * lossBound * regretBound) + regret

/--
Full source-facing Theorem-5 interface. `GeneralDecisionHedgeGame` leaves the
decision and outcome spaces unrestricted while requiring a proved finite
mixture/expected-loss identity. Thus the sole finite support in the theorem is
the paper's finite expert family, not the learners' or experts' decisions.
-/
def theorem5_decision_prediction_generalSpec : Prop := by
  classical
  exact ∀ {Expert Decision Outcome : Type*}
    [Fintype Expert] [Nonempty Expert] [MeasurableSpace Decision]
    (game : GeneralDecisionHedgeGame Expert Decision Outcome)
    (state : HedgeWeightState Expert)
    (huniform : ∀ expert, state.weight expert = 1 / (Fintype.card Expert : ℝ))
    (rounds : List (GeneralDecisionHedgeRound game))
    (lossBound : ℝ)
    (hbest_le_bound : Finset.univ.inf' Finset.univ_nonempty
      (fun expert => (rounds.map fun round => round.inducedLoss expert).sum) ≤ lossBound)
    (hlossBound_le_rounds : lossBound ≤ rounds.length)
    (hlossBound_pos : 0 < lossBound)
    (hcard : 1 < Fintype.card Expert),
    GeneralDecisionHedgeRound.hedgeCumulativeDecisionLoss
        (hedgeDiscountFromBounds lossBound (Real.log (Fintype.card Expert : ℝ)))
        (by
          unfold hedgeDiscountFromBounds
          apply one_div_pos.mpr
          have hcard_real : 1 < (Fintype.card Expert : ℝ) := by
            exact_mod_cast hcard
          have hlog_pos : 0 < Real.log (Fintype.card Expert : ℝ) :=
            Real.log_pos hcard_real
          have hratio_pos : 0 <
              2 * Real.log (Fintype.card Expert : ℝ) / lossBound := by
            exact div_pos (mul_pos (by norm_num) hlog_pos) hlossBound_pos
          nlinarith [Real.sqrt_pos.mpr hratio_pos])
        state rounds ≤
      (Finset.univ.inf' Finset.univ_nonempty
          (fun expert => (rounds.map fun round => round.inducedLoss expert).sum)) +
        Real.sqrt (2 * lossBound * Real.log (Fintype.card Expert : ℝ)) +
          Real.log (Fintype.card Expert : ℝ)

/--
Finite source-facing form of Theorem 6 on the domain where every displayed
Figure-2 update and logarithmic vote is defined. `AdaBoostAdmissible` records
`0 < ε_t < 1`; the source's separate endpoint assertion is addressed in the
source-definedness note.
-/
def theorem6_adaBoost_finiteSpec : Prop := by
  classical
  exact ∀ {Training : Type} [Fintype Training] [Nonempty Training]
    (state : HedgeWeightState Training) (label : Training → ℝ),
    (∑ sample, state.weight sample) = 1 →
      (∀ sample, 0 ≤ label sample ∧ label sample ≤ 1) →
      (∀ sample, label sample = 0 ∨ label sample = 1) →
        ∀ (hypotheses : List (Training → ℝ)),
          (∀ hypothesis ∈ hypotheses, ∀ sample,
            0 ≤ hypothesis sample ∧ hypothesis sample ≤ 1) →
            ∀ hvalid : AdaBoostAdmissible state label hypotheses,
              adaBoostTrainingError state label hypotheses hvalid ≤
                adaBoostTheorem6Factor state label hypotheses hvalid

/--
Freund--Schapire Theorem 8. `binaryThresholdCombinationClass concepts width`
is the paper's `C_T(H)`: choose `width = T` binary weak hypotheses, weight
their zero-one outputs, and take a closed affine threshold.  The source's
`d ≥ 2` hypothesis is explicit; the conjunction says that `d` is the class's
actual finite VC dimension.  The zero-term threshold class is included rather
than excluded by a proof-specific positivity premise.
-/
def theorem8_weighted_threshold_vcSpec : Prop := by
  classical
  exact ∀ {X : Type*} (width d : ℕ) (concepts : Set (BinaryClassifier X)),
    2 ≤ d →
      (VCDimensionAtMost concepts d ∧
        ∃ sample : Finset X, binaryTraceVCDimension concepts sample = d) →
      ∀ sample : Finset X,
          (binaryTraceVCDimension
          (binaryThresholdCombinationClass concepts width) sample : ℝ) ≤
          sourceThresholdCombinationVCBound width d

/--
Freund--Schapire Theorem 9 on the domain of its displayed normalized vote
`r(x)` and soft threshold `F : [0,1] → [0,1]`: the normalization denominator
is nonzero and each evaluated vote lies in `[0,1]`. Individual logarithmic
weights may be zero or negative; strict positive edges are not required.
-/
def theorem9_soft_adaBoost_errorSpec : Prop := by
  classical
  exact ∀ {Training : Type} [Fintype Training] [Nonempty Training]
    (state : HedgeWeightState Training) (label : Training → ℝ),
    (∑ sample, state.weight sample) = 1 →
      (∀ sample, label sample = 0 ∨ label sample = 1) →
        ∀ (hypotheses : List (Training → ℝ)),
          (∀ hypothesis ∈ hypotheses, ∀ sample,
            0 ≤ hypothesis sample ∧ hypothesis sample ≤ 1) →
            ∀ hvalid : AdaBoostAdmissible state label hypotheses,
              adaBoostVoteWeightSum state label hypotheses hvalid ≠ 0 →
                (∀ sample,
                  0 ≤ adaBoostNormalizedVote state label hypotheses hvalid sample ∧
                    adaBoostNormalizedVote state label hypotheses hvalid sample ≤ 1) →
                  ∀ threshold : ℝ → ℝ,
                    AdaBoostSoftThreshold state label hypotheses hvalid threshold →
                      adaBoostSoftTrainingError state label hypotheses hvalid threshold ≤
                        adaBoostTheorem9Factor state label hypotheses hvalid

/-!
Freund--Schapire Eq. (21): the Theorem-6 product is controlled by the
accumulated binary relative entropy of the observed weak-hypothesis errors.
-/
def equation21_adaBoost_binaryKLSpec : Prop := by
  classical
  exact ∀ {Training : Type} [Fintype Training] [Nonempty Training]
    (state : HedgeWeightState Training) (label : Training → ℝ),
    (∑ sample, state.weight sample) = 1 →
      (∀ sample, 0 ≤ label sample ∧ label sample ≤ 1) →
      (∀ sample, label sample = 0 ∨ label sample = 1) →
        ∀ (hypotheses : List (Training → ℝ)),
          (∀ hypothesis ∈ hypotheses, ∀ sample,
            0 ≤ hypothesis sample ∧ hypothesis sample ≤ 1) →
            ∀ hvalid : AdaBoostAdmissible state label hypotheses,
              adaBoostTrainingError state label hypotheses hvalid ≤
                  adaBoostTheorem6Factor state label hypotheses hvalid ∧
                adaBoostTheorem6Factor state label hypotheses hvalid =
                  Real.exp (-((adaBoostErrors state label hypotheses hvalid).map fun error =>
                    Probability.binaryKLDivergence (1 / 2) error).sum) ∧
                Real.exp (-((adaBoostErrors state label hypotheses hvalid).map fun error =>
                    Probability.binaryKLDivergence (1 / 2) error).sum) ≤
                  Real.exp (-2 *
                    ((adaBoostErrors state label hypotheses hvalid).map fun error =>
                      (1 / 2 - error) ^ 2).sum)

/-!
Freund--Schapire Eq. (22): when every observed weak-hypothesis error is
`1/2 - gamma`, the training error has the displayed uniform-edge power bound.
-/
def equation22_adaBoost_uniform_edgeSpec : Prop := by
  classical
  exact ∀ {Training : Type} [Fintype Training] [Nonempty Training]
    (state : HedgeWeightState Training) (label : Training → ℝ),
    (∑ sample, state.weight sample) = 1 →
      (∀ sample, 0 ≤ label sample ∧ label sample ≤ 1) →
      (∀ sample, label sample = 0 ∨ label sample = 1) →
        ∀ (hypotheses : List (Training → ℝ)),
          (∀ hypothesis ∈ hypotheses, ∀ sample,
            0 ≤ hypothesis sample ∧ hypothesis sample ≤ 1) →
            ∀ hvalid : AdaBoostAdmissible state label hypotheses,
              ∀ (gamma : ℝ), -(1 / 2 : ℝ) < gamma → gamma < 1 / 2 →
                (∀ observed ∈ adaBoostErrors state label hypotheses hvalid,
                  observed = 1 / 2 - gamma) →
                adaBoostTrainingError state label hypotheses hvalid ≤
                    (1 - 4 * gamma ^ 2) ^ ((hypotheses.length : ℝ) / 2) ∧
                  (1 - 4 * gamma ^ 2) ^ ((hypotheses.length : ℝ) / 2) =
                    Real.exp (-(hypotheses.length : ℝ) *
                      Probability.binaryKLDivergence (1 / 2) (1 / 2 - gamma)) ∧
                  Real.exp (-(hypotheses.length : ℝ) *
                      Probability.binaryKLDivergence (1 / 2) (1 / 2 - gamma)) ≤
                    Real.exp (-2 * (hypotheses.length : ℝ) * gamma ^ 2)

/-!
Freund--Schapire Eq. (23): the quadratic iteration budget is sufficient to
attain a target training error under a uniform positive edge.
-/
def equation23_adaBoost_quadratic_iterationsSpec : Prop := by
  classical
  exact ∀ {Training : Type} [Fintype Training] [Nonempty Training]
    (state : HedgeWeightState Training) (label : Training → ℝ),
    (∑ sample, state.weight sample) = 1 →
      (∀ sample, 0 ≤ label sample ∧ label sample ≤ 1) →
      (∀ sample, label sample = 0 ∨ label sample = 1) →
        ∀ (hypotheses : List (Training → ℝ)),
          (∀ hypothesis ∈ hypotheses, ∀ sample,
            0 ≤ hypothesis sample ∧ hypothesis sample ≤ 1) →
            ∀ hvalid : AdaBoostAdmissible state label hypotheses,
              ∀ (gamma target : ℝ), 0 < gamma → gamma < 1 / 2 →
                0 < target → target < 1 →
                (∀ observed ∈ adaBoostErrors state label hypotheses hvalid,
                  observed = 1 / 2 - gamma) →
                Nat.ceil (Real.log (1 / target) /
                    Probability.binaryKLDivergence (1 / 2) (1 / 2 - gamma)) ≤
                    Nat.ceil (Real.log (1 / target) / (2 * gamma ^ 2)) ∧
                  (Nat.ceil (Real.log (1 / target) /
                      Probability.binaryKLDivergence (1 / 2) (1 / 2 - gamma)) ≤
                      hypotheses.length →
                    adaBoostTrainingError state label hypotheses hvalid ≤ target)

/--
Freund--Schapire Theorem 10.  `AdaBoostM1Admissible` is the source's literal
binary mistake-indicator update, so its recorded errors and adaptive weights
are exactly those of Figure 3.  Its interior lower endpoint is explicit
because the source update divides by `1 - epsilon_t` and uses `beta_t` in the
next normalized distribution.
-/
def theorem10_adaBoostM1_errorSpec : Prop := by
  classical
  exact ∀ {Training Label : Type}
    [Fintype Training] [Nonempty Training]
    [Fintype Label] [Nonempty Label]
    (state : HedgeWeightState Training) (label : Training → Label),
    (∑ sample, state.weight sample) = 1 →
      ∀ (hypotheses : List (Training → Label)),
        ∀ hvalid : AdaBoostM1Admissible state label hypotheses,
          (∀ error ∈ adaBoostM1Errors state label hypotheses hvalid, error ≤ 1 / 2) →
            (∀ sample candidate,
              adaBoostM1LabelScore state label hypotheses hvalid sample candidate ≤
                adaBoostM1LabelScore state label hypotheses hvalid sample
                  (adaBoostM1FinalHypothesis state label hypotheses hvalid sample)) ∧
              adaBoostM1TrainingError state label hypotheses hvalid ≤
                adaBoostM1Theorem10Factor state label hypotheses hvalid

/--
Freund--Schapire Theorem 11.  The source's Figure-4 initialization is stated
as the exact weight identity on the finite product of examples and incorrect
labels.  The `letI` derives its nonempty product space from the source
condition `k ≥ 2`, rather than exposing it as an unrelated public typeclass.
-/
def theorem11_adaBoostM2_errorSpec : Prop := by
  classical
  exact ∀ {Training Label : Type}
    [Fintype Training] [Nonempty Training]
    [Fintype Label] [Nonempty Label]
    (label : Training → Label) (exampleWeight : Training → ℝ)
    (state : HedgeWeightState (AdaBoostM2Instance Training Label label)),
    (∀ sample, 0 ≤ exampleWeight sample) →
      (∑ sample, exampleWeight sample) = 1 →
        (hlabels : 1 < Fintype.card Label) →
          (∀ pair : AdaBoostM2Instance Training Label label,
            state.weight pair = exampleWeight pair.1.1 /
              ((Fintype.card Label - 1 : ℕ) : ℝ)) →
            (∑ pair, state.weight pair) = 1 →
              ∀ hypotheses : List (Training → Label → ℝ),
                (∀ hypothesis ∈ hypotheses, ∀ sample candidate,
                  0 ≤ hypothesis sample candidate ∧ hypothesis sample candidate ≤ 1) →
                  letI : Nonempty (AdaBoostM2Instance Training Label label) :=
                    adaBoostM2Instance_nonempty label hlabels
                  ∀ hvalid : AdaBoostM2Admissible label state hypotheses,
                    (∀ sample candidate,
                      adaBoostM2LabelScore label state hypotheses hvalid sample candidate ≤
                        adaBoostM2LabelScore label state hypotheses hvalid sample
                          (adaBoostM2FinalHypothesis label state hypotheses hvalid sample)) ∧
                      adaBoostM2TrainingError label exampleWeight state hypotheses hvalid ≤
                        adaBoostM2Theorem11Factor label state hypotheses hvalid

/--
Freund--Schapire Theorem 12 for Figure 5's AdaBoost.R reduction.  The source
initial density is the literal Eq. (25) `D(i)|y-y_i|/Z`; the final predictor
is the finite characterization of Figure 5's weighted-median infimum.  The
admissibility predicate records the displayed update domain
`0 < epsilon_t <= 1/2`.
-/
def theorem12_adaBoostR_errorSpec : Prop := by
  classical
  exact ∀ {Training : Type} [Fintype Training]
    (exampleWeight : Training → ℝ) (label : Training → ℝ),
    ∀ (hexample_nonneg : ∀ sample, 0 ≤ exampleWeight sample)
      (hexample_total : ∑ sample, exampleWeight sample = 1)
      (hlabel : ∀ sample, 0 ≤ label sample ∧ label sample ≤ 1),
          ∀ hypotheses : List (Training → ℝ),
            ∀ (hhypotheses : ∀ hypothesis ∈ hypotheses, ∀ sample,
              0 ≤ hypothesis sample ∧ hypothesis sample ≤ 1)
              (hvalid : AdaBoostRAdmissible
                (adaBoostRBaseState exampleWeight label
                  hexample_nonneg hexample_total hlabel) label hypotheses),
                adaBoostRMeanSquaredError exampleWeight label
                  (adaBoostRFinalHypothesis
                    (adaBoostRBaseState exampleWeight label
                      hexample_nonneg hexample_total hlabel)
                    label hypotheses hhypotheses hvalid) ≤
                  adaBoostRTheorem12Factor
                    (adaBoostRBaseState exampleWeight label
                      hexample_nonneg hexample_total hlabel)
                    label hypotheses hvalid

end FreundSchapire1997Hedge
