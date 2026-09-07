import DSWG24DiscretizationBias.MainTheorems
import DSWG24DiscretizationBias.Assumptions

/-!
# Paper Interface: DSWG24 Discretization Bias

This is the compact, human-facing Lean surface for the paper.  A reader should
be able to inspect this file alone and see the definitions and theorem
statements that correspond to the source paper.

The proofs are intentionally short calls into `MainTheorems.lean`, where the
implementation details and auxiliary lemmas live.
-/

namespace DSWG24DiscretizationBias
namespace ProofBridge

open scoped BigOperators ProbabilityTheory
open MeasureTheory

noncomputable section

/-! ## Paper Definitions -/

/--
Prior class probability `Pr(y)`.

Source status: direct source definition
Source note: The paper's bias definitions use the label prior as the reference distribution.
-/
def prior [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (μ : PMF (X × Y)) (y : Y) : ℝ :=
  ((Finite.labelMarginal μ) y).toReal

/--
Observed finite-sample accuracy
`acc(y₁:N, ŷ₁:N) = (1/N) ∑ᵢ 1[ŷᵢ = yᵢ]`.

Source status: direct source formula
Source note: Exact source text lines 171--173.
-/
def accuracy {N K : ℕ} (truth decision : Fin N → Fin K) : ℝ :=
  AppliedModelingLib.Decision.datasetAccuracy truth decision

/-- Marginal label share `\hat p_marg(y) = (1/N) sum_i 1[\hat y_i = y]`.

Source status: direct source formula
Source note: Source text lines 180--185 define this as the finite-sample average over predicted labels.
-/
def marginalLabelShare {N K : ℕ} (decision : Fin N → Fin K) (y : Fin K) : ℝ :=
  (∑ i : Fin N, if decision i = y then (1 : ℝ) else 0) / (N : ℝ)

/-- Aggregate posterior `p_agg^q(y) = (1/N) sum_i q(y,x_i)`.

Source status: direct source formula
Source note: Source text lines 198--206 define this as the finite-sample average of continuous classifier scores.
-/
def aggregatePosterior {N K : ℕ} (q : Fin N → Fin K → ℝ) (y : Fin K) : ℝ :=
  (∑ i : Fin N, q i y) / (N : ℝ)

/--
The source's consistent-order tie semantics for one argmax choice: the chosen
class maximizes `score`, and among tied maximizers it is first in the fixed
`Fin K` order.

Source status: direct source rule semantics
Source note: Exact source text lines 218--231.
-/
def isFirstArgmax {K : ℕ} (score : Fin K → ℝ) (chosen : Fin K) : Prop :=
  (∀ y, score y ≤ score chosen) ∧
    (∀ y, score y = score chosen → chosen.val ≤ y.val)

/-- Source formula for the fixed-order tie-broken argmax predicate. -/
theorem isFirstArgmax_formula {K : ℕ} (score : Fin K → ℝ) (chosen : Fin K) :
    isFirstArgmax score chosen ↔
      (∀ y, score y ≤ score chosen) ∧
        (∀ y, score y = score chosen → chosen.val ≤ y.val) :=
  Iff.rfl

/-- The source's fixed-order argmax predicate selects a unique class. -/
theorem isFirstArgmax_unique {K : ℕ} {score : Fin K → ℝ} {a b : Fin K}
    (ha : isFirstArgmax score a) (hb : isFirstArgmax score b) :
    a = b := by
  have hscore : score b = score a := le_antisymm (ha.1 b) (hb.1 a)
  apply Fin.ext
  exact Nat.le_antisymm (ha.2 b hscore) (hb.2 a hscore.symm)

/--
If every row has the same fixed-order argmax, that class is also the
fixed-order argmax of the aggregate posterior.
-/
theorem isFirstArgmax_aggregatePosterior_of_forall
    {N K : ℕ} (posterior : Fin N → Fin K → ℝ) (target : Fin K)
    (hNpos : 0 < N)
    (hrows : ∀ i, isFirstArgmax (posterior i) target) :
    isFirstArgmax (aggregatePosterior posterior) target := by
  have hNreal : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hNpos
  constructor
  · intro y
    unfold aggregatePosterior
    exact div_le_div_of_nonneg_right
      (Finset.sum_le_sum (fun i _ => (hrows i).1 y)) (le_of_lt hNreal)
  · intro y haggregateEq
    unfold aggregatePosterior at haggregateEq
    have hsumEq :
        (∑ i : Fin N, posterior i y) = ∑ i : Fin N, posterior i target :=
      (div_left_inj' (ne_of_gt hNreal)).mp haggregateEq
    let i0 : Fin N := ⟨0, hNpos⟩
    have hnotlt : ¬ posterior i0 y < posterior i0 target := by
      intro hlt
      have hsumLt :
          (∑ i : Fin N, posterior i y) < ∑ i : Fin N, posterior i target :=
        Finset.sum_lt_sum
          (fun i _ => (hrows i).1 y)
          ⟨i0, Finset.mem_univ i0, hlt⟩
      exact (ne_of_lt hsumLt) hsumEq
    have hrowEq : posterior i0 y = posterior i0 target :=
      le_antisymm ((hrows i0).1 y) (le_of_not_gt hnotlt)
    exact (hrows i0).2 y hrowEq

/-- Exact row-wise tie-broken argmax rule from Section 1.1.2. -/
def isTieBrokenArgmaxRule {N K : ℕ}
    (q : Fin N → Fin K → ℝ) (rule : Fin N → Fin K) : Prop :=
  ∀ i, isFirstArgmax (q i) (rule i)

/-- Source formula for row-wise fixed-order argmax decisions. -/
theorem isTieBrokenArgmaxRule_formula {N K : ℕ}
    (q : Fin N → Fin K → ℝ) (rule : Fin N → Fin K) :
    isTieBrokenArgmaxRule q rule ↔ ∀ i, isFirstArgmax (q i) (rule i) :=
  Iff.rfl

/--
Threshold-at-`t` semantics: emit the tie-broken argmax class when its score is
at least `t`, and otherwise leave the row uncoded.

Source status: direct source rule semantics
Source note: Exact source text lines 219--220.
-/
def thresholdRule {N K : ℕ} (t : ℝ) (q : Fin N → Fin K → ℝ)
    (argmaxRule : Fin N → Fin K) (i : Fin N) : Option (Fin K) :=
  if t ≤ q i (argmaxRule i) then some (argmaxRule i) else none

/--
Thompson sampling assigns row `i` to class `y` with probability `q i y`.

Source status: direct source randomized-rule semantics
Source note: Exact source text lines 222--223.
-/
def isThompsonSamplingRule {N K : ℕ} (q selectionProbability : Fin N → Fin K → ℝ) : Prop :=
  ∀ i y, selectionProbability i y = q i y

/-- Source formula for the row-wise Thompson sampling probabilities. -/
theorem isThompsonSamplingRule_formula {N K : ℕ}
    (q selectionProbability : Fin N → Fin K → ℝ) :
    isThompsonSamplingRule q selectionProbability ↔
      ∀ i y, selectionProbability i y = q i y :=
  Iff.rfl

/--
Deterministic independence: the decision at row `i` depends only on that row's
feature value, through one common row rule `d`.

Source status: direct source rule semantics
Source note: Exact source text lines 225--228 and 615--618.
-/
def isIndependentRule {X : Type*} {N K : ℕ}
    (rule : (Fin N → X) → Fin N → Fin K) : Prop :=
  ∃ d : X → Fin K, ∀ xs i, rule xs i = d (xs i)

/-- Source formula for deterministic row-wise independence. -/
theorem isIndependentRule_formula {X : Type*} {N K : ℕ}
    (rule : (Fin N → X) → Fin N → Fin K) :
    isIndependentRule rule ↔
      ∃ d : X → Fin K, ∀ xs i, rule xs i = d (xs i) :=
  Iff.rfl

/--
Randomized independence: conditional on the observed rows, a common
row-level probability kernel independently generates the decision vector.
-/
def isIndependentRandomizedRule {X : Type*} {N K : ℕ}
    (jointProbability : (Fin N → X) → (Fin N → Fin K) → ℝ) : Prop :=
  ∃ rowProbability : X → Fin K → ℝ,
    (∀ x y, 0 ≤ rowProbability x y) ∧
      (∀ x, (∑ y : Fin K, rowProbability x y) = 1) ∧
        ∀ xs decision,
          jointProbability xs decision =
            ∏ i : Fin N, rowProbability (xs i) (decision i)

/-- Source formula for randomized row-wise independence. -/
theorem isIndependentRandomizedRule_formula {X : Type*} {N K : ℕ}
    (jointProbability : (Fin N → X) → (Fin N → Fin K) → ℝ) :
    isIndependentRandomizedRule jointProbability ↔
      ∃ rowProbability : X → Fin K → ℝ,
        (∀ x y, 0 ≤ rowProbability x y) ∧
          (∀ x, (∑ y : Fin K, rowProbability x y) = 1) ∧
            ∀ xs decision,
              jointProbability xs decision =
                ∏ i : Fin N, rowProbability (xs i) (decision i) :=
  Iff.rfl

/--
Bias `bias(y, \hat y, p_ref) = \hat p_marg(y) - p_ref(y)`.

Source status: direct source formula
Source note: The source defines bias as marginal predicted-label share minus the chosen reference distribution.
-/
def bias {N K : ℕ} (decision : Fin N → Fin K) (pref : Fin K → ℝ) (y : Fin K) : ℝ :=
  marginalLabelShare decision y - pref y

/--
Distributional fidelity `fid(p_ref, \hat y) = -sum_y |bias(y,\hat y,p_ref)|`.

Source status: direct source formula
Source note: The source objective uses negative total absolute bias as the fidelity term.
-/
def fidelity {N K : ℕ} (decision : Fin N → Fin K) (pref : Fin K → ℝ) : ℝ :=
  -∑ y : Fin K, |bias decision pref y|

/--
Equation (1)'s per-dataset integer-program objective, with the source fidelity
specialized to the supplied dataset reference distribution.
-/
def equation1Objective {N K : ℕ} (γ : ℝ)
    (q : Fin N → Fin K → ℝ) (pref : Fin K → ℝ)
    (decision : Fin N → Fin K) : ℝ :=
  γ * AppliedModelingLib.Decision.averageScore q decision +
    (1 - γ) * fidelity decision pref

/-- A decision vector is a runner/argmax solution of Equation (1). -/
def maximizesEquation1 {N K : ℕ} (γ : ℝ)
    (q : Fin N → Fin K → ℝ) (pref : Fin K → ℝ)
    (decision : Fin N → Fin K) : Prop :=
  ∀ other : Fin N → Fin K,
    equation1Objective γ q pref other ≤ equation1Objective γ q pref decision

/-- Source formula for maximization of Equation (1). -/
theorem maximizesEquation1_formula {N K : ℕ} (γ : ℝ)
    (q : Fin N → Fin K → ℝ) (pref : Fin K → ℝ)
    (decision : Fin N → Fin K) :
    maximizesEquation1 γ q pref decision ↔
      ∀ other : Fin N → Fin K,
        equation1Objective γ q pref other ≤ equation1Objective γ q pref decision :=
  Iff.rfl

/-- Predictive MAE for Bayes posterior scores: `E_X sum_y q(y,x)(1-q(y,x))`. -/
def classifierMAE [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (μ : PMF (X × Y)) (q : X → Y → ℝ) : ℝ :=
  AppliedModelingLib.pmfExp (Finite.featureMarginal μ)
    (fun x => ∑ y : Y, q x y * (1 - q x y))

/--
Continuous marginal label share: `∫ x, 1[rule x = y] dμ(x)`.

Source status: continuous source analogue
Source note: This is the continuous-population version of the finite marginal label share.
-/
def continuousMarginalLabelShare {X Y : Type*} [MeasurableSpace X] [DecidableEq Y]
    (μ : Measure X) (rule : X → Y) (y : Y) : ℝ :=
  ∫ x, (if rule x = y then (1 : ℝ) else 0) ∂μ

/-- Continuous aggregate posterior reference: `∫ x, q x y dμ(x)`. -/
def continuousAggregatePosterior {X Y : Type*} [MeasurableSpace X]
    (μ : Measure X) (q : X → Y → ℝ) (y : Y) : ℝ :=
  ∫ x, q x y ∂μ

/-- Continuous bias relative to a supplied reference distribution. -/
def continuousBias {X Y : Type*} [MeasurableSpace X] [DecidableEq Y]
    (μ : Measure X) (rule : X → Y) (pref : Y → ℝ) (y : Y) : ℝ :=
  continuousMarginalLabelShare μ rule y - pref y

/-- Continuous aggregate-posterior bias. -/
def continuousAggregateBias {X Y : Type*} [MeasurableSpace X] [DecidableEq Y]
    (μ : Measure X) (q : X → Y → ℝ) (rule : X → Y) (y : Y) : ℝ :=
  continuousMarginalLabelShare μ rule y - continuousAggregatePosterior μ q y

/-- Continuous predictive MAE. -/
def continuousClassifierMAE {X Y : Type*} [MeasurableSpace X] [Fintype Y]
    (μ : Measure X) (q : X → Y → ℝ) : ℝ :=
  ∫ x, ∑ y : Y, q x y * (1 - q x y) ∂μ

/-- Joint prior-reference bias for Theorem 1's continuous statement. -/
def continuousJointPriorBias {X Y : Type*} [MeasurableSpace (X × Y)]
    [DecidableEq Y] (μ : Measure (X × Y)) (rule : X → Y) (y : Y) : ℝ :=
  (∫ xy, (if rule xy.1 = y then (1 : ℝ) else 0) ∂μ) -
    ∫ xy, (if xy.2 = y then (1 : ℝ) else 0) ∂μ

/-- Joint-distribution aggregate posterior, integrating the feature posterior over `F_{X,Y}`. -/
def continuousJointAggregatePosterior {X Y : Type*} [MeasurableSpace (X × Y)]
    (μ : Measure (X × Y)) (q : X → Y → ℝ) (y : Y) : ℝ :=
  ∫ xy, q xy.1 y ∂μ

/-- Joint aggregate-posterior bias for the source's aggregate reference choice. -/
def continuousJointAggregateBias {X Y : Type*} [MeasurableSpace (X × Y)]
    [DecidableEq Y] (μ : Measure (X × Y)) (q : X → Y → ℝ)
    (rule : X → Y) (y : Y) : ℝ :=
  (∫ xy, (if rule xy.1 = y then (1 : ℝ) else 0) ∂μ) -
    continuousJointAggregatePosterior μ q y

/-- Joint predictive MAE for Theorem 1's continuous statement. -/
def continuousJointClassifierMAE {X Y : Type*} [MeasurableSpace (X × Y)]
    [Fintype Y] (μ : Measure (X × Y)) (q : X → Y → ℝ) : ℝ :=
  ∫ xy, ∑ y : Y, q xy.1 y * (1 - q xy.1 y) ∂μ

/--
Posterior-simplex condition: each `q(x)` is a probability vector.

Source status: source model condition
Source note: The calibrated classifier is a posterior/probability vector over labels at each feature value.
-/
abbrev posteriorSimplex {X Y : Type*} [Fintype Y]
    (q : X → Y → ℝ) : Prop :=
  AppliedModelingLib.Learning.Prediction.IsSimplexValued q

/-- Source formula for the posterior-simplex condition. -/
theorem posteriorSimplex_formula {X Y : Type*} [Fintype Y]
    (q : X → Y → ℝ) :
    posteriorSimplex q ↔
      (∀ x, (∑ y : Y, q x y) = 1) ∧
        (∀ x y, 0 ≤ q x y) ∧
          (∀ x y, q x y ≤ 1) :=
  Iff.rfl

/-- Weak argmax support predicate; exact source tie ordering is `isFirstArgmax`. -/
abbrev isArgmaxRule {X Y : Type*}
    (q : X → Y → ℝ) (rule : X → Y) : Prop :=
  AppliedModelingLib.Learning.Prediction.IsArgmaxRule q rule

/-- Source formula for the weak argmax predicate used in Theorem 1. -/
theorem isArgmaxRule_formula {X Y : Type*}
    (q : X → Y → ℝ) (rule : X → Y) :
    isArgmaxRule q rule ↔ ∀ x y, q x y ≤ q x (rule x) :=
  Iff.rfl

/-- Exact tie-broken argmax implies the weak support predicate used internally. -/
theorem tieBrokenArgmaxRule_isArgmaxRule {N K : ℕ}
    (q : Fin N → Fin K → ℝ) (rule : Fin N → Fin K)
    (h : isTieBrokenArgmaxRule q rule) : isArgmaxRule q rule :=
  fun i y => (h i).1 y

/--
Finite atom-factorization form of Bayes optimality
`q*(y,x) = Pr(Y=y | X=x)`, avoiding undefined zero-mass conditionals.

Source status: direct source model definition
Source note: Exact source text lines 604--607 and 1600--1603.
-/
def bayesOptimal {Ω σ : Type*} [Fintype Ω] [DecidableEq Ω]
    [Fintype σ] [DecidableEq σ] {N K : ℕ}
    (μ : PMF Ω) (observedDataset : Ω → σ)
    (trueLabels : Ω → Fin N → Fin K)
    (posterior : σ → Fin N → Fin K → ℝ) : Prop :=
  ∀ xs i y,
    AppliedModelingLib.pmfProb μ
        (fun w => observedDataset w = xs ∧ trueLabels w i = y) =
      posterior xs i y *
        AppliedModelingLib.pmfProb μ (fun w => observedDataset w = xs)

/-- Finite-atom source formula for Bayes-optimal posterior scores. -/
theorem bayesOptimal_formula {Ω σ : Type*} [Fintype Ω] [DecidableEq Ω]
    [Fintype σ] [DecidableEq σ] {N K : ℕ}
    (μ : PMF Ω) (observedDataset : Ω → σ)
    (trueLabels : Ω → Fin N → Fin K)
    (posterior : σ → Fin N → Fin K → ℝ) :
    bayesOptimal μ observedDataset trueLabels posterior ↔
      ∀ xs i y,
        AppliedModelingLib.pmfProb μ
            (fun w => observedDataset w = xs ∧ trueLabels w i = y) =
          posterior xs i y *
            AppliedModelingLib.pmfProb μ (fun w => observedDataset w = xs) :=
  Iff.rfl

/--
Source-shaped perfect-classifier condition: on every positive-probability
joint atom, the induced decision is the true label and the posterior is the
corresponding one-hot vector.

The historical Theorem 1(ii) wrapper used a stronger all-product-pairs premise;
the exact support-sensitive endpoints below supersede it for source coverage.
-/
def perfectClassifierOnSupport
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (μ : PMF (X × Y)) (q : X → Y → ℝ) (rule : X → Y) : Prop :=
  ∀ x y, μ (x, y) ≠ 0 →
    rule x = y ∧ q x y = 1 ∧ ∀ a, a ≠ y → q x a = 0

/-- Exact source formula for perfect classification on the joint-law support. -/
theorem perfectClassifierOnSupport_formula
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (μ : PMF (X × Y)) (q : X → Y → ℝ) (rule : X → Y) :
    perfectClassifierOnSupport μ q rule ↔
      ∀ x y, μ (x, y) ≠ 0 →
        rule x = y ∧ q x y = 1 ∧ ∀ a, a ≠ y → q x a = 0 :=
  Iff.rfl

/--
Theorem 1(ii): a classifier that is one-hot and correct on every
positive-probability joint atom has zero bias under both reference choices in
the source theorem.

Source status: exact theorem endpoint
Source note: Zero-mass feature/label pairs are irrelevant; no all-product-pairs correctness premise is used.
-/
theorem theorem1ii_perfect_classifier_zero_bias_on_support
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (μ : PMF (X × Y)) (q : X → Y → ℝ) (rule : X → Y)
    (hperfect : perfectClassifierOnSupport μ q rule) (y : Y) :
    (Finite.paperBias μ rule (prior μ) y = 0) ∧
      (Finite.paperBias μ rule (Finite.paperAggregatePosterior μ q) y = 0) := by
  constructor
  · simpa [prior] using
      (Finite.paper_theorem1ii_perfect_classifier_prior_bias_zero_on_support
        μ q rule hperfect y)
  · simpa [Finite.paperAggregateBias] using
      (Finite.paper_theorem1ii_perfect_classifier_aggregate_bias_zero_on_support
        μ q rule hperfect y)

/-- Exact prior-reference source proposition in Theorem 1(ii). -/
def theorem1iiPriorReferenceZeroBiasSpec
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (μ : PMF (X × Y)) (q : X → Y → ℝ) (rule : X → Y) : Prop :=
  ∀ y : Y, perfectClassifierOnSupport μ q rule →
    Finite.paperBias μ rule (prior μ) y = 0

/-- Lean evidence for the exact prior-reference source proposition. -/
theorem theorem1ii_prior_reference_zero_bias_on_support_spec
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (μ : PMF (X × Y)) (q : X → Y → ℝ) (rule : X → Y) :
    theorem1iiPriorReferenceZeroBiasSpec μ q rule := by
  intro y hperfect
  exact (theorem1ii_perfect_classifier_zero_bias_on_support μ q rule hperfect y).1

/-- Exact aggregate-posterior-reference source proposition in Theorem 1(ii). -/
def theorem1iiAggregateReferenceZeroBiasSpec
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (μ : PMF (X × Y)) (q : X → Y → ℝ) (rule : X → Y) : Prop :=
  ∀ y : Y, perfectClassifierOnSupport μ q rule →
    Finite.paperBias μ rule (Finite.paperAggregatePosterior μ q) y = 0

/-- Lean evidence for the exact aggregate-reference source proposition. -/
theorem theorem1ii_aggregate_reference_zero_bias_on_support_spec
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (μ : PMF (X × Y)) (q : X → Y → ℝ) (rule : X → Y) :
    theorem1iiAggregateReferenceZeroBiasSpec μ q rule := by
  intro y hperfect
  exact (theorem1ii_perfect_classifier_zero_bias_on_support μ q rule hperfect y).2

/--
Calibration: for every label and every measurable score event, the true label
mass on that score event equals the aggregate posterior score mass on the same
event.  This is the paper's `Pr(Y=y | q(y,x)=c)=c` condition in
event-preimage form.

Source status: source model condition
Source note: The event-preimage form is the measurable version of the paper's calibration assumption.
-/
def calibrated {X Y : Type*} [MeasurableSpace (X × Y)] [DecidableEq Y]
    (μ : Measure (X × Y)) (q : X → Y → ℝ) : Prop := by
  classical
  exact
    ∀ (y : Y) (s : Set ℝ), MeasurableSet s →
      (∫ xy, (if q xy.1 y ∈ s then
          if xy.2 = y then (1 : ℝ) else 0
        else 0) ∂μ) =
            ∫ xy, (if q xy.1 y ∈ s then q xy.1 y else 0) ∂μ

/--
Calibration makes the source's two permitted Theorem 1 reference choices
coincide: the aggregate posterior equals the label prior.
-/
theorem continuousJointPrior_eq_jointAggregatePosterior_of_calibrated
    {X Y : Type*} [MeasurableSpace (X × Y)] [DecidableEq Y]
    (μ : Measure (X × Y)) (q : X → Y → ℝ) (y : Y)
    (hcal : calibrated μ q) :
    (∫ xy, (if xy.2 = y then (1 : ℝ) else 0) ∂μ) =
      continuousJointAggregatePosterior μ q y := by
  have hcal' : ContinuousTheorem1.ContinuousCalibration μ q := by
    simpa [calibrated, ContinuousTheorem1.ContinuousCalibration] using hcal
  simpa [continuousJointAggregatePosterior,
    ContinuousTheorem1.continuousJointPrior,
    ContinuousTheorem1.continuousJointAggregatePosterior] using
    (ContinuousTheorem1.continuousJointPrior_eq_jointAggregatePosterior_of_continuousCalibration
      μ q y hcal')

/-- Event-preimage source formula for calibration. -/
theorem calibrated_formula {X Y : Type*} [MeasurableSpace (X × Y)] [DecidableEq Y]
    (μ : Measure (X × Y)) (q : X → Y → ℝ) :
    calibrated μ q ↔ (by
      classical
      exact ∀ (y : Y) (s : Set ℝ), MeasurableSet s →
          (∫ xy, (if q xy.1 y ∈ s then
              if xy.2 = y then (1 : ℝ) else 0
            else 0) ∂μ) =
            ∫ xy, (if q xy.1 y ∈ s then q xy.1 y else 0) ∂μ) := by
  classical
  rfl

/--
Paper objective `O_N^gamma` for one observed dataset: `γ` times average
posterior score plus `(1 - γ)` times the fidelity term.
-/
def objective {N K : ℕ} {σ : Type*}
    (γ : ℝ) (posterior : σ → Fin N → Fin K → ℝ)
    (fidelityTerm : σ → (Fin N → Fin K) → ℝ)
    (xs : σ) (decision : Fin N → Fin K) : ℝ :=
  γ * AppliedModelingLib.Decision.averageScore (posterior xs) decision +
    (1 - γ) * fidelityTerm xs decision

/-- Expected paper objective using true-label accuracy plus expected fidelity. -/
def expectedObjective {ω σ : Type*} {N K : ℕ} [NeZero K]
    (expect : (ω → ℝ) → ℝ) (observedDataset : ω → σ)
    (trueLabels : ω → Fin N → Fin K)
    (γ : ℝ) (fidelityTerm : σ → (Fin N → Fin K) → ℝ)
    (rule : σ → Fin N → Fin K) : ℝ :=
  γ * AppliedModelingLib.Decision.expectedDecisionAccuracy
      expect observedDataset trueLabels rule +
    (1 - γ) * AppliedModelingLib.Decision.expectedObjective
      expect observedDataset fidelityTerm rule

/-- Equation (2): expected finite-sample true-label accuracy. -/
def equation2ExpectedAccuracy {ω σ : Type*} {N K : ℕ}
    (expect : (ω → ℝ) → ℝ) (observedDataset : ω → σ)
    (trueLabels : ω → Fin N → Fin K)
    (rule : σ → Fin N → Fin K) : ℝ :=
  AppliedModelingLib.Decision.expectedDecisionAccuracy
    expect observedDataset trueLabels rule

/-- Expected fidelity for a source-shaped dataset-dependent reference family. -/
def expectedFidelityAt {ω σ : Type*} {N K : ℕ}
    (expect : (ω → ℝ) → ℝ) (observedDataset : ω → σ)
    (prefAt : σ → Fin K → ℝ) (rule : σ → Fin N → Fin K) : ℝ :=
  AppliedModelingLib.Decision.expectedObjective expect observedDataset
    (fun xs decision => fidelity decision (prefAt xs)) rule

/-- Expected class bias for a source-shaped dataset-dependent reference family. -/
def expectedBiasAt {ω σ : Type*} {N K : ℕ}
    (expect : (ω → ℝ) → ℝ) (observedDataset : ω → σ)
    (prefAt : σ → Fin K → ℝ) (rule : σ → Fin N → Fin K)
    (y : Fin K) : ℝ :=
  expect (fun w => bias (rule (observedDataset w)) (prefAt (observedDataset w)) y)

/-- Equation (3): expected accuracy/fidelity objective `O_N^γ`. -/
def equation3ExpectedObjective {ω σ : Type*} {N K : ℕ}
    (expect : (ω → ℝ) → ℝ) (observedDataset : ω → σ)
    (trueLabels : ω → Fin N → Fin K)
    (γ : ℝ) (prefAt : σ → Fin K → ℝ)
    (rule : σ → Fin N → Fin K) : ℝ :=
  γ * equation2ExpectedAccuracy expect observedDataset trueLabels rule +
    (1 - γ) * expectedFidelityAt expect observedDataset prefAt rule

/-- Pareto optimality for the source's expected accuracy and fidelity metrics. -/
def paretoOptimal {Rule : Type*}
    (accuracyMetric fidelityMetric : Rule → ℝ) (rule : Rule) : Prop :=
  Pareto.ParetoOptimal accuracyMetric fidelityMetric rule

/-- Source formula for Pareto optimality in accuracy and fidelity. -/
theorem paretoOptimal_formula {Rule : Type*}
    (accuracyMetric fidelityMetric : Rule → ℝ) (rule : Rule) :
    paretoOptimal accuracyMetric fidelityMetric rule ↔
      Pareto.ParetoOptimal accuracyMetric fidelityMetric rule :=
  Iff.rfl

/-- A dataset-indexed reference family takes values in the label simplex. -/
def referenceSimplexAt {Sample : Type*} {K : ℕ}
    (prefAt : Sample → Fin K → ℝ) : Prop :=
  ∀ sample,
    (∀ y, 0 ≤ prefAt sample y) ∧
      (∑ y : Fin K, prefAt sample y) = 1

/-- Source formula for a dataset-indexed simplex-valued reference. -/
theorem referenceSimplexAt_formula {Sample : Type*} {K : ℕ}
    (prefAt : Sample → Fin K → ℝ) :
    referenceSimplexAt prefAt ↔
      ∀ sample,
        (∀ y, 0 ≤ prefAt sample y) ∧
          (∑ y : Fin K, prefAt sample y) = 1 :=
  Iff.rfl

/-- The tie-broken most likely class after aggregating scores in one dataset. -/
def isAggregateFirstArgmax {N K : ℕ}
    (posterior : Fin N → Fin K → ℝ) (target : Fin K) : Prop :=
  isFirstArgmax (aggregatePosterior posterior) target

/-- Source formula for the tie-broken aggregate-posterior maximizer. -/
theorem isAggregateFirstArgmax_formula {N K : ℕ}
    (posterior : Fin N → Fin K → ℝ) (target : Fin K) :
    isAggregateFirstArgmax posterior target ↔
      isFirstArgmax (aggregatePosterior posterior) target :=
  Iff.rfl

/--
The paper's exact non-trivial reference family `P_N^q`: `prefAt` is a
dataset-indexed simplex-valued reference, `aggregateArgmax sample` is the
tie-broken aggregate-max class of that dataset, and only that selected class
must receive mass at least `1/N`.

Source status: direct source definition
Source note: Exact source text lines 744--763 and proof lines 1651--1692.
-/
def sourcePNq {Sample : Type*} {N K : ℕ}
    (posterior : Sample → Fin N → Fin K → ℝ)
    (aggregateArgmax : Sample → Fin K)
    (prefAt : Sample → Fin K → ℝ) : Prop :=
  referenceSimplexAt prefAt ∧
    (∀ sample, isAggregateFirstArgmax (posterior sample) (aggregateArgmax sample)) ∧
      (∀ sample, 1 / (N : ℝ) ≤ prefAt sample (aggregateArgmax sample))

/-- Exact source formula for the dataset-dependent family `P_N^q`. -/
theorem sourcePNq_formula {Sample : Type*} {N K : ℕ}
    (posterior : Sample → Fin N → Fin K → ℝ)
    (aggregateArgmax : Sample → Fin K)
    (prefAt : Sample → Fin K → ℝ) :
    sourcePNq posterior aggregateArgmax prefAt ↔
      referenceSimplexAt prefAt ∧
        (∀ sample, isAggregateFirstArgmax (posterior sample) (aggregateArgmax sample)) ∧
          (∀ sample, 1 / (N : ℝ) ≤ prefAt sample (aggregateArgmax sample)) :=
  Iff.rfl

/-- Source proof region `S_a`: focal posterior is `1`. -/
def sourceSa {X Y : Type*} (q : X → Y → ℝ) (z : Y) : Set X :=
  {x | q x z = 1}

/-- Source formula for proof region `S_a`. -/
theorem sourceSa_formula {X Y : Type*} (q : X → Y → ℝ) (z : Y) :
    sourceSa q z = {x | q x z = 1} :=
  rfl

/-- Source proof region `S_b`: focal posterior is in `(1/K,1)`. -/
def sourceSb {X Y : Type*} [Fintype Y] (q : X → Y → ℝ) (z : Y) : Set X :=
  {x | (Fintype.card Y : ℝ)⁻¹ < q x z ∧ q x z < 1}

/-- Source formula for proof region `S_b`. -/
theorem sourceSb_formula {X Y : Type*} [Fintype Y]
    (q : X → Y → ℝ) (z : Y) :
    sourceSb q z = {x | (Fintype.card Y : ℝ)⁻¹ < q x z ∧ q x z < 1} :=
  rfl

/-- Source proof region `S_c`: focal posterior is exactly `1/K`. -/
def sourceSc {X Y : Type*} [Fintype Y] (q : X → Y → ℝ) (z : Y) : Set X :=
  {x | q x z = (Fintype.card Y : ℝ)⁻¹}

/-- Source formula for proof region `S_c`. -/
theorem sourceSc_formula {X Y : Type*} [Fintype Y]
    (q : X → Y → ℝ) (z : Y) :
    sourceSc q z = {x | q x z = (Fintype.card Y : ℝ)⁻¹} :=
  rfl

/-- Source proof region `S_d`: focal posterior is in `(0,1/K)`. -/
def sourceSd {X Y : Type*} [Fintype Y] (q : X → Y → ℝ) (z : Y) : Set X :=
  {x | 0 < q x z ∧ q x z < (Fintype.card Y : ℝ)⁻¹}

/-- Source formula for proof region `S_d`. -/
theorem sourceSd_formula {X Y : Type*} [Fintype Y]
    (q : X → Y → ℝ) (z : Y) :
    sourceSd q z = {x | 0 < q x z ∧ q x z < (Fintype.card Y : ℝ)⁻¹} :=
  rfl

/-- Source proof region `S_e`: focal posterior is `0`. -/
def sourceSe {X Y : Type*} (q : X → Y → ℝ) (z : Y) : Set X :=
  {x | q x z = 0}

/-- Source formula for proof region `S_e`. -/
theorem sourceSe_formula {X Y : Type*} (q : X → Y → ℝ) (z : Y) :
    sourceSe q z = {x | q x z = 0} :=
  rfl

/-! ## Theorem 1 -/

/--
Theorem 1(i): if features provide no information and all rows are assigned to
a plurality class `z`, then plurality-class bias is `1 - Pr(z)` and every other
class has bias `-Pr(y)`.  The same formula holds whether the reference is the
prior or the aggregate posterior.

Source status: direct theorem clause
Source note: This is the no-information/plurality case of Theorem 1.
-/
def theorem1iNoInformationBiasSpec
    [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype Y] [DecidableEq Y]
    (μ : PMF (X × Y)) (q : X → Y → ℝ) (z y : Y)
    (hnoInformation : ∀ x a, q x a = prior μ a)
    (hplurality : ∀ a, prior μ a ≤ prior μ z) : Prop :=
    (Finite.paperBias μ (fun _ : X => z) (prior μ) y =
        if z = y then 1 - prior μ y else -prior μ y) ∧
      (Finite.paperBias μ (fun _ : X => z) (Finite.paperAggregatePosterior μ q) y =
        if z = y then 1 - prior μ y else -prior μ y)

theorem theorem1i_no_information_bias
    [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype Y] [DecidableEq Y]
    (μ : PMF (X × Y)) (q : X → Y → ℝ) (z y : Y)
    (hnoInformation : ∀ x a, q x a = prior μ a)
    (hplurality : ∀ a, prior μ a ≤ prior μ z) :
    (Finite.paperBias μ (fun _ : X => z) (prior μ) y =
        if z = y then 1 - prior μ y else -prior μ y) ∧
      (Finite.paperBias μ (fun _ : X => z) (Finite.paperAggregatePosterior μ q) y =
        if z = y then 1 - prior μ y else -prior μ y) := by
  classical
  have hprior :
      Finite.paperBias μ (fun _ : X => z) (prior μ) y =
        if z = y then 1 - prior μ y else -prior μ y := by
    simpa [prior, Finite.paperBias, Finite.paperPrior,
      Finite.paperMarginalLabelShare] using
      (Finite.paper_theorem1i_no_information_prior_bias μ z y)
  have hagg : Finite.paperAggregatePosterior μ q y = prior μ y := by
    unfold Finite.paperAggregatePosterior
    have hfun : (fun x : X => q x y) = fun _ : X => prior μ y := by
      funext x
      exact hnoInformation x y
    rw [hfun]
    exact AppliedModelingLib.pmfExp_const (Finite.featureMarginal μ) (prior μ y)
  exact ⟨hprior, by simpa [Finite.paperBias, hagg] using hprior⟩

theorem theorem1i_no_information_bias_spec
    [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype Y] [DecidableEq Y]
    (μ : PMF (X × Y)) (q : X → Y → ℝ) (z y : Y)
    (hnoInformation : ∀ x a, q x a = prior μ a)
    (hplurality : ∀ a, prior μ a ≤ prior μ z) :
    theorem1iNoInformationBiasSpec μ q z y hnoInformation hplurality := by
  exact theorem1i_no_information_bias μ q z y hnoInformation hplurality

/--
Support theorem currently used for Theorem 1(ii): if the induced decision rule
agrees with the true label on every product pair, then prior-reference bias is
zero.

Source status: stronger-premise specialization
Source note: The paper quantifies over the data law/support.  The exact
`perfectClassifierOnSupport` endpoint remains open; this theorem must not be
used by itself to claim full Theorem 1(ii) coverage.
-/
theorem theorem1ii_perfect_classifier_zero_bias
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (μ : PMF (X × Y)) (rule : X → Y)
    (htruth : ∀ xy : X × Y, rule xy.1 = xy.2) (y : Y) :
    Finite.paperBias μ rule (prior μ) y = 0 := by
  simpa [prior, Finite.paperBias, Finite.paperPrior,
    Finite.paperMarginalLabelShare] using
    (Finite.paper_theorem1ii_perfect_classifier_prior_bias_zero μ rule htruth y)

/--
Theorem 1(iii): for a calibrated posterior classifier and a tie-broken argmax
rule, argmax bias is bounded above by predictive MAE.

The assumptions below are the formal versions of the paper's implicit
measurability, posterior-simplex, and calibration requirements.
-/
def theorem1iiiArgmaxBiasLeMaeSpec
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSingletonClass Y] [Fintype Y] [DecidableEq Y]
    (μ : Measure (X × Y)) [IsFiniteMeasure μ]
    (q : X → Y → ℝ) (argmaxRule : X → Y) (y : Y)
    (hrule : Measurable argmaxRule)
    (hargmax : isArgmaxRule q argmaxRule)
    (hsimplex : posteriorSimplex q)
    (hscore : ∀ y : Y, Measurable (fun xy : X × Y => q xy.1 y))
    (hcal : calibrated μ q) : Prop :=
    continuousJointPriorBias μ argmaxRule y ≤ continuousJointClassifierMAE μ q

theorem theorem1iii_argmax_bias_le_mae
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSingletonClass Y] [Fintype Y] [DecidableEq Y]
    (μ : Measure (X × Y)) [IsFiniteMeasure μ]
    (q : X → Y → ℝ) (argmaxRule : X → Y) (y : Y)
    (hrule : Measurable argmaxRule)
    (hargmax : isArgmaxRule q argmaxRule)
    (hsimplex : posteriorSimplex q)
    (hscore : ∀ y : Y, Measurable (fun xy : X × Y => q xy.1 y))
    (hcal : calibrated μ q) :
    continuousJointPriorBias μ argmaxRule y ≤
      continuousJointClassifierMAE μ q := by
  have hcal' : ContinuousTheorem1.ContinuousCalibration μ q := by
    simpa [calibrated, ContinuousTheorem1.ContinuousCalibration] using hcal
  simpa [continuousJointPriorBias, continuousJointClassifierMAE,
    isArgmaxRule, posteriorSimplex, calibrated,
    ContinuousTheorem1.ContinuousCalibration,
    ContinuousTheorem1.continuousJointPriorBias,
    ContinuousTheorem1.continuousJointClassifierMAE,
    Finite.paperConditionalMAE] using
    (ContinuousTheorem1.paper_theorem1iii_continuous_joint_prior_bias_le_mae_of_continuousCalibration_finite_simplex
      μ q argmaxRule y hrule hargmax hsimplex.1 hsimplex.2.1 hscore hcal')

theorem theorem1iii_argmax_bias_le_mae_spec
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSingletonClass Y] [Fintype Y] [DecidableEq Y]
    (μ : Measure (X × Y)) [IsFiniteMeasure μ]
    (q : X → Y → ℝ) (argmaxRule : X → Y) (y : Y)
    (hrule : Measurable argmaxRule)
    (hargmax : isArgmaxRule q argmaxRule)
    (hsimplex : posteriorSimplex q)
    (hscore : ∀ y : Y, Measurable (fun xy : X × Y => q xy.1 y))
    (hcal : calibrated μ q) :
    theorem1iiiArgmaxBiasLeMaeSpec μ q argmaxRule y hrule hargmax hsimplex hscore hcal := by
  exact theorem1iii_argmax_bias_le_mae μ q argmaxRule y hrule hargmax hsimplex hscore hcal

/--
Theorem 1(iii) tightness: there is a binary one-feature instance where
argmax bias equals predictive MAE.
-/
def theorem1iiiTightBinaryExampleSpec : Prop :=
  Finite.paperAggregateBias Finite.paperTheorem1TightMu
      Finite.paperTheorem1TightQ Finite.paperTheorem1TightArgmax 0 =
    classifierMAE Finite.paperTheorem1TightMu Finite.paperTheorem1TightQ

theorem theorem1iii_tight_binary_example :
    Finite.paperAggregateBias Finite.paperTheorem1TightMu
        Finite.paperTheorem1TightQ Finite.paperTheorem1TightArgmax 0 =
      classifierMAE Finite.paperTheorem1TightMu Finite.paperTheorem1TightQ := by
  change
    Finite.paperAggregateBias Finite.paperTheorem1TightMu
      Finite.paperTheorem1TightQ Finite.paperTheorem1TightArgmax 0 =
        Finite.paperClassifierMAE Finite.paperTheorem1TightMu
          Finite.paperTheorem1TightQ
  exact Finite.paper_theorem1iii_tight_binary_uniform_example

theorem theorem1iii_tight_binary_example_spec : theorem1iiiTightBinaryExampleSpec := by
  exact theorem1iii_tight_binary_example

/-! ## Theorem 2 -/

/--
Theorem 2(i): for Bayes-optimal scores, every `gamma` and fidelity/reference
term has a joint decision rule maximizing the expected objective `O_N^gamma`.

Source status: direct theorem clause
Source note: This is Theorem 2(i)'s joint-rule existence claim under the Bayes score identity.
-/
def theorem2iJointRuleExistsSpec
    {ω σ : Type*} {N K : ℕ} [NeZero K]
    (hK : 2 ≤ K) (hNK : K < N)
    (expect : (ω → ℝ) → ℝ)
    (hlin : AppliedModelingLib.Decision.FiniteLinearExpectation expect)
    (observedDataset : ω → σ)
    (trueLabels : ω → Fin N → Fin K)
    (γ : ℝ) (posterior : σ → Fin N → Fin K → ℝ)
    (fidelityTerm : σ → (Fin N → Fin K) → ℝ)
    (hbayesRow : ∀ i (choose : σ → Fin K),
      expect (fun x =>
          if choose (observedDataset x) = trueLabels x i then (1 : ℝ) else 0) =
        expect (fun x => posterior (observedDataset x) i (choose (observedDataset x)))) : Prop :=
    ∃ optRule : σ → Fin N → Fin K,
      ∀ rule : σ → Fin N → Fin K,
        expectedObjective expect observedDataset trueLabels γ fidelityTerm rule ≤
          expectedObjective expect observedDataset trueLabels γ fidelityTerm optRule

theorem theorem2i_joint_rule_exists
    {ω σ : Type*} {N K : ℕ} [NeZero K]
    (hK : 2 ≤ K) (hNK : K < N)
    (expect : (ω → ℝ) → ℝ)
    (hlin : AppliedModelingLib.Decision.FiniteLinearExpectation expect)
    (observedDataset : ω → σ)
    (trueLabels : ω → Fin N → Fin K)
    (γ : ℝ) (posterior : σ → Fin N → Fin K → ℝ)
    (fidelityTerm : σ → (Fin N → Fin K) → ℝ)
    (hbayesRow : ∀ i (choose : σ → Fin K),
      expect (fun x =>
          if choose (observedDataset x) = trueLabels x i then (1 : ℝ) else 0) =
        expect (fun x => posterior (observedDataset x) i (choose (observedDataset x)))) :
    ∃ optRule : σ → Fin N → Fin K,
      ∀ rule : σ → Fin N → Fin K,
        expectedObjective expect observedDataset trueLabels γ fidelityTerm rule ≤
          expectedObjective expect observedDataset trueLabels γ fidelityTerm optRule := by
  simpa [expectedObjective, paperExpectedONObjective] using
    (paper_theorem2i_joint_optimization_rule_exists
      hK hNK expect hlin observedDataset trueLabels γ posterior fidelityTerm hbayesRow)

theorem theorem2i_joint_rule_exists_spec
    {ω σ : Type*} {N K : ℕ} [NeZero K]
    (hK : 2 ≤ K) (hNK : K < N)
    (expect : (ω → ℝ) → ℝ)
    (hlin : AppliedModelingLib.Decision.FiniteLinearExpectation expect)
    (observedDataset : ω → σ)
    (trueLabels : ω → Fin N → Fin K)
    (γ : ℝ) (posterior : σ → Fin N → Fin K → ℝ)
    (fidelityTerm : σ → (Fin N → Fin K) → ℝ)
    (hbayesRow : ∀ i (choose : σ → Fin K),
      expect (fun x =>
          if choose (observedDataset x) = trueLabels x i then (1 : ℝ) else 0) =
        expect (fun x => posterior (observedDataset x) i (choose (observedDataset x)))) :
    theorem2iJointRuleExistsSpec hK hNK expect hlin observedDataset trueLabels γ posterior fidelityTerm hbayesRow := by
  exact theorem2i_joint_rule_exists hK hNK expect hlin observedDataset trueLabels γ posterior fidelityTerm hbayesRow

/--
Theorem 2(ii): for Bayes-optimal scores, a pointwise argmax rule maximizes
expected accuracy.
-/
def theorem2iiArgmaxAccuracyMaximizingSpec
    {ω σ : Type*} {N K : ℕ} [NeZero K]
    (hK : 2 ≤ K) (hNK : K < N)
    (expect : (ω → ℝ) → ℝ)
    (hlin : AppliedModelingLib.Decision.FiniteLinearExpectation expect)
    (observedDataset : ω → σ)
    (trueLabels : ω → Fin N → Fin K)
    (posterior : σ → Fin N → Fin K → ℝ)
    {decisionRule argmaxRule : σ → Fin N → Fin K}
    (hargmax :
      ∀ xs, AppliedModelingLib.Decision.IsPointwiseMax (posterior xs) (argmaxRule xs))
    (hbayesRow : ∀ i (choose : σ → Fin K),
      expect (fun x =>
          if choose (observedDataset x) = trueLabels x i then (1 : ℝ) else 0) =
        expect (fun x => posterior (observedDataset x) i (choose (observedDataset x)))) : Prop :=
    AppliedModelingLib.Decision.expectedDecisionAccuracy
        expect observedDataset trueLabels decisionRule ≤
      AppliedModelingLib.Decision.expectedDecisionAccuracy
        expect observedDataset trueLabels argmaxRule

theorem theorem2ii_argmax_accuracy_maximizing
    {ω σ : Type*} {N K : ℕ} [NeZero K]
    (hK : 2 ≤ K) (hNK : K < N)
    (expect : (ω → ℝ) → ℝ)
    (hlin : AppliedModelingLib.Decision.FiniteLinearExpectation expect)
    (observedDataset : ω → σ)
    (trueLabels : ω → Fin N → Fin K)
    (posterior : σ → Fin N → Fin K → ℝ)
    {decisionRule argmaxRule : σ → Fin N → Fin K}
    (hargmax :
      ∀ xs, AppliedModelingLib.Decision.IsPointwiseMax (posterior xs) (argmaxRule xs))
    (hbayesRow : ∀ i (choose : σ → Fin K),
      expect (fun x =>
          if choose (observedDataset x) = trueLabels x i then (1 : ℝ) else 0) =
        expect (fun x => posterior (observedDataset x) i (choose (observedDataset x)))) :
    AppliedModelingLib.Decision.expectedDecisionAccuracy
        expect observedDataset trueLabels decisionRule ≤
      AppliedModelingLib.Decision.expectedDecisionAccuracy
        expect observedDataset trueLabels argmaxRule := by
  exact paper_theorem2ii_argmax_expected_accuracy_maximizing
    hK hNK expect hlin observedDataset trueLabels posterior hargmax hbayesRow

theorem theorem2ii_argmax_accuracy_maximizing_spec
    {ω σ : Type*} {N K : ℕ} [NeZero K]
    (hK : 2 ≤ K) (hNK : K < N)
    (expect : (ω → ℝ) → ℝ)
    (hlin : AppliedModelingLib.Decision.FiniteLinearExpectation expect)
    (observedDataset : ω → σ)
    (trueLabels : ω → Fin N → Fin K)
    (posterior : σ → Fin N → Fin K → ℝ)
    {decisionRule argmaxRule : σ → Fin N → Fin K}
    (hargmax :
      ∀ xs, AppliedModelingLib.Decision.IsPointwiseMax (posterior xs) (argmaxRule xs))
    (hbayesRow : ∀ i (choose : σ → Fin K),
      expect (fun x =>
          if choose (observedDataset x) = trueLabels x i then (1 : ℝ) else 0) =
        expect (fun x => posterior (observedDataset x) i (choose (observedDataset x)))) :
    theorem2iiArgmaxAccuracyMaximizingSpec
      (decisionRule := decisionRule) (argmaxRule := argmaxRule)
      hK hNK expect hlin observedDataset trueLabels posterior hargmax hbayesRow := by
  exact paper_theorem2ii_argmax_expected_accuracy_maximizing
    hK hNK expect hlin observedDataset trueLabels posterior hargmax hbayesRow

/--
Source-shaped local bridge for Theorem 2(iii).  On a selected dataset where
every row has the same tie-broken argmax class and the independent decision
assigns no row to that class, the exact `P_N^q` lower bound for that one class
is sufficient for the existing one-row switch proof.
-/
theorem theorem2iii_source_dataset_reference_bridge
    {Sample : Type*} {N K : ℕ}
    (posterior : Sample → Fin N → Fin K → ℝ)
    (aggregateArgmax : Sample → Fin K)
    (prefAt : Sample → Fin K → ℝ)
    (hPNq : sourcePNq posterior aggregateArgmax prefAt)
    (sample : Sample) (decision : Fin N → Fin K)
    (hNpos : 0 < N)
    (hnone : ∀ i, decision i ≠ aggregateArgmax sample)
    (hsameArgmax :
      ∀ i, isFirstArgmax (posterior sample i) (aggregateArgmax sample)) :
    ¬ Pareto.ParetoOptimal
      (Theorem2iii.datasetAccuracyScore (posterior sample))
      (Theorem2iii.datasetFidelity (prefAt sample)) decision := by
  exact Theorem2iii.paper_theorem2iii_not_pareto_of_missing_argmax_class
    (posterior sample) (prefAt sample) decision (aggregateArgmax sample)
    hNpos hnone (hPNq.1 sample).1 (hPNq.1 sample).2 (hPNq.2.2 sample)
    (fun i => (hsameArgmax i).1 (decision i))

/--
The corresponding per-dataset weighted-objective bridge for `0 ≤ γ < 1`.
Only the selected aggregate-max class uses the `1/N` reference lower bound.
-/
theorem theorem2iii_source_dataset_weighted_bridge
    {Sample : Type*} {N K : ℕ}
    (posterior : Sample → Fin N → Fin K → ℝ)
    (aggregateArgmax : Sample → Fin K)
    (prefAt : Sample → Fin K → ℝ)
    (hPNq : sourcePNq posterior aggregateArgmax prefAt)
    (sample : Sample) (decision : Fin N → Fin K)
    {γ : ℝ} (hγnonneg : 0 ≤ γ) (hγlt : γ < 1)
    (hNpos : 0 < N)
    (hnone : ∀ i, decision i ≠ aggregateArgmax sample)
    (hsameArgmax :
      ∀ i, isFirstArgmax (posterior sample i) (aggregateArgmax sample)) :
    ¬ ∀ other : Fin N → Fin K,
        Pareto.weightedObjective γ
            (Theorem2iii.datasetAccuracyScore (posterior sample))
            (Theorem2iii.datasetFidelity (prefAt sample)) other ≤
          Pareto.weightedObjective γ
            (Theorem2iii.datasetAccuracyScore (posterior sample))
            (Theorem2iii.datasetFidelity (prefAt sample)) decision := by
  exact
    Theorem2iii.paper_theorem2iii_not_weightedObjective_maximizer_of_missing_argmax_class
      (posterior sample) (prefAt sample) decision (aggregateArgmax sample)
      hγnonneg hγlt hNpos hnone (hPNq.1 sample).1 (hPNq.1 sample).2
      (hPNq.2.2 sample) (fun i => (hsameArgmax i).1 (decision i))

/--
The source's positive-probability dataset selection step for Theorem 2(iii),
with the exact dataset-dependent `P_N^q` reference.  A positive-probability
disagreement between an independent rule and the fixed-order argmax rule
produces a positive-mass iid dataset and a one-row policy change that weakly
improves posterior accuracy and strictly improves that dataset's fidelity.
-/
theorem theorem2iii_source_exists_positive_mass_policy_improvement
    {X : Type*} [Fintype X] [DecidableEq X] {N K : ℕ}
    (μ : PMF X) (posterior : X → Fin K → ℝ)
    (rule argmaxRule : X → Fin K)
    (hargmax : ∀ x, isFirstArgmax (posterior x) (argmaxRule x))
    (hdisagree :
      0 < AppliedModelingLib.pmfProb μ (fun x : X => rule x ≠ argmaxRule x))
    (aggregateArgmax : (Fin N → X) → Fin K)
    (prefAt : (Fin N → X) → Fin K → ℝ)
    (hPNq : sourcePNq
      (fun sample : Fin N → X => Theorem2iii.sampledPosterior posterior sample)
      aggregateArgmax prefAt)
    (hNpos : 0 < N) :
    ∃ sample : Fin N → X, ∃ betterDecision : Fin N → Fin K,
      0 < ((Theorem2iii.iidSamplePMF μ N) sample).toReal ∧
        Theorem2iii.datasetAccuracyScore
            (Theorem2iii.sampledPosterior posterior sample)
            (Theorem2iii.sampledDecision rule sample) ≤
          Theorem2iii.datasetAccuracyScore
            (Theorem2iii.sampledPosterior posterior sample) betterDecision ∧
        Theorem2iii.datasetFidelity (prefAt sample)
            (Theorem2iii.sampledDecision rule sample) <
          Theorem2iii.datasetFidelity (prefAt sample) betterDecision := by
  classical
  rcases
      Theorem2iii.exists_target_allDisagreement_event_pos_of_disagreement_event_pos
        μ rule argmaxRule hdisagree with
    ⟨target, htargetPos⟩
  rcases Theorem2iii.exists_positive_mass_allDisagreement_sample_of_event_pos
      (N := N) μ rule argmaxRule target htargetPos with
    ⟨sample, hall, hsamplePos⟩
  have htargetAggregate :
      isAggregateFirstArgmax
        (Theorem2iii.sampledPosterior posterior sample) target := by
    apply isFirstArgmax_aggregatePosterior_of_forall
      (Theorem2iii.sampledPosterior posterior sample) target hNpos
    intro i
    simpa [Theorem2iii.sampledPosterior, (hall i).1] using
      hargmax (sample i)
  have haggregate : aggregateArgmax sample = target :=
    isFirstArgmax_unique (hPNq.2.1 sample) htargetAggregate
  have hnontrivial : 1 / (N : ℝ) ≤ prefAt sample target := by
    simpa [haggregate] using hPNq.2.2 sample
  rcases
      Theorem2iii.exists_weak_accuracy_strict_fidelity_switch_of_independent_all_disagreement_sample
        posterior (prefAt sample) rule argmaxRule sample target hNpos hall
        (hPNq.1 sample).1 (hPNq.1 sample).2 hnontrivial
        (fun x y => (hargmax x).1 y) with
    ⟨betterDecision, hacc, hfid⟩
  exact ⟨sample, betterDecision, hsamplePos, hacc, hfid⟩

/--
Theorem 2(iii), exact finite expected-policy Pareto endpoint for the source's
dataset-dependent reference family `P_N^q`.

Source status: exact theorem endpoint
Source note: The competing joint policy changes the independent rule only on the selected positive-mass iid dataset.
-/
theorem theorem2iii_source_non_argmax_not_expected_pareto
    {X : Type*} [Fintype X] [DecidableEq X] {N K : ℕ}
    (μ : PMF X) (posterior : X → Fin K → ℝ)
    (rule argmaxRule : X → Fin K)
    (hargmax : ∀ x, isFirstArgmax (posterior x) (argmaxRule x))
    (hdisagree :
      0 < AppliedModelingLib.pmfProb μ (fun x : X => rule x ≠ argmaxRule x))
    (aggregateArgmax : (Fin N → X) → Fin K)
    (prefAt : (Fin N → X) → Fin K → ℝ)
    (hPNq : sourcePNq
      (fun sample : Fin N → X => Theorem2iii.sampledPosterior posterior sample)
      aggregateArgmax prefAt)
    (hNpos : 0 < N) :
    ¬ Pareto.ParetoOptimal
      (Theorem2iii.expectedDatasetAccuracy (Theorem2iii.iidSamplePMF μ N)
        (fun sample => Theorem2iii.sampledPosterior posterior sample))
      (Theorem2iii.expectedDatasetFidelityAt
        (Theorem2iii.iidSamplePMF μ N) prefAt)
      (fun sample => Theorem2iii.sampledDecision rule sample) := by
  rcases theorem2iii_source_exists_positive_mass_policy_improvement
      μ posterior rule argmaxRule hargmax hdisagree aggregateArgmax prefAt hPNq
      hNpos with
    ⟨sample, betterDecision, hsamplePos, hacc, hfid⟩
  exact Theorem2iii.not_expectedDatasetAt_pareto_of_positive_mass_sample_dominated
    (Theorem2iii.iidSamplePMF μ N)
    (fun s => Theorem2iii.sampledPosterior posterior s) prefAt
    (fun s => Theorem2iii.sampledDecision rule s) sample betterDecision
    hsamplePos hacc hfid

/--
Equivalent uniqueness form of the exact Pareto endpoint: an independent rule
that is Pareto optimal among joint dataset policies agrees with the fixed-order
argmax rule almost surely.

Source status: exact theorem endpoint
Source note: This is the contrapositive form of `theorem2iii_source_non_argmax_not_expected_pareto` used in the paper's statement.
-/
theorem theorem2iii_source_pareto_optimal_agrees_argmax
    {X : Type*} [Fintype X] [DecidableEq X] {N K : ℕ}
    (μ : PMF X) (posterior : X → Fin K → ℝ)
    (rule argmaxRule : X → Fin K)
    (hargmax : ∀ x, isFirstArgmax (posterior x) (argmaxRule x))
    (aggregateArgmax : (Fin N → X) → Fin K)
    (prefAt : (Fin N → X) → Fin K → ℝ)
    (hPNq : sourcePNq
      (fun sample : Fin N → X => Theorem2iii.sampledPosterior posterior sample)
      aggregateArgmax prefAt)
    (hNpos : 0 < N)
    (hPareto : Pareto.ParetoOptimal
      (Theorem2iii.expectedDatasetAccuracy (Theorem2iii.iidSamplePMF μ N)
        (fun sample => Theorem2iii.sampledPosterior posterior sample))
      (Theorem2iii.expectedDatasetFidelityAt
        (Theorem2iii.iidSamplePMF μ N) prefAt)
      (fun sample => Theorem2iii.sampledDecision rule sample)) :
    AppliedModelingLib.pmfProb μ (fun x : X => rule x ≠ argmaxRule x) = 0 := by
  classical
  by_contra hne
  have hp_ne :
      AppliedModelingLib.pmfProb μ (fun x : X => rule x ≠ argmaxRule x) ≠ 0 := hne
  have hpos :
      0 < AppliedModelingLib.pmfProb μ (fun x : X => rule x ≠ argmaxRule x) :=
    lt_of_le_of_ne
      (AppliedModelingLib.pmfProb_nonneg μ (fun x : X => rule x ≠ argmaxRule x))
      hp_ne.symm
  exact
    (theorem2iii_source_non_argmax_not_expected_pareto
      μ posterior rule argmaxRule hargmax hpos aggregateArgmax prefAt hPNq hNpos)
      hPareto

/-- Exact source proposition for Theorem 2(iii)'s Pareto uniqueness clause. -/
def theorem2iiiParetoOptimalAgreesArgmaxSpec
    {X : Type*} [Fintype X] [DecidableEq X] {N K : ℕ}
    (μ : PMF X) (posterior : X → Fin K → ℝ)
    (rule argmaxRule : X → Fin K)
    (aggregateArgmax : (Fin N → X) → Fin K)
    (prefAt : (Fin N → X) → Fin K → ℝ) : Prop :=
  (∀ x, isFirstArgmax (posterior x) (argmaxRule x)) →
    sourcePNq
      (fun sample : Fin N → X => Theorem2iii.sampledPosterior posterior sample)
      aggregateArgmax prefAt →
    0 < N →
    Pareto.ParetoOptimal
      (Theorem2iii.expectedDatasetAccuracy (Theorem2iii.iidSamplePMF μ N)
        (fun sample => Theorem2iii.sampledPosterior posterior sample))
      (Theorem2iii.expectedDatasetFidelityAt
        (Theorem2iii.iidSamplePMF μ N) prefAt)
      (fun sample => Theorem2iii.sampledDecision rule sample) →
    AppliedModelingLib.pmfProb μ (fun x : X => rule x ≠ argmaxRule x) = 0

/-- Lean evidence for the exact source Pareto proposition. -/
theorem theorem2iii_source_pareto_optimal_agrees_argmax_spec
    {X : Type*} [Fintype X] [DecidableEq X] {N K : ℕ}
    (μ : PMF X) (posterior : X → Fin K → ℝ)
    (rule argmaxRule : X → Fin K)
    (aggregateArgmax : (Fin N → X) → Fin K)
    (prefAt : (Fin N → X) → Fin K → ℝ) :
    theorem2iiiParetoOptimalAgreesArgmaxSpec
      μ posterior rule argmaxRule aggregateArgmax prefAt := by
  intro hargmax hPNq hNpos hPareto
  exact theorem2iii_source_pareto_optimal_agrees_argmax
    μ posterior rule argmaxRule hargmax aggregateArgmax prefAt hPNq hNpos hPareto

/--
Theorem 2(iii), exact finite expected weighted-objective endpoint for
`0 ≤ γ < 1` and the source's dataset-dependent family `P_N^q`.

Source status: exact theorem endpoint
Source note: The strict fidelity gain has positive expectation because the selected iid dataset has positive mass.
-/
theorem theorem2iii_source_non_argmax_not_expected_weightedObjective_maximizer
    {X : Type*} [Fintype X] [DecidableEq X] {N K : ℕ}
    (μ : PMF X) (posterior : X → Fin K → ℝ)
    (rule argmaxRule : X → Fin K)
    (hargmax : ∀ x, isFirstArgmax (posterior x) (argmaxRule x))
    (hdisagree :
      0 < AppliedModelingLib.pmfProb μ (fun x : X => rule x ≠ argmaxRule x))
    (aggregateArgmax : (Fin N → X) → Fin K)
    (prefAt : (Fin N → X) → Fin K → ℝ)
    (hPNq : sourcePNq
      (fun sample : Fin N → X => Theorem2iii.sampledPosterior posterior sample)
      aggregateArgmax prefAt)
    {γ : ℝ} (hγnonneg : 0 ≤ γ) (hγlt : γ < 1)
    (hNpos : 0 < N) :
    ¬ ∀ other : (Fin N → X) → Fin N → Fin K,
        Pareto.weightedObjective γ
            (Theorem2iii.expectedDatasetAccuracy (Theorem2iii.iidSamplePMF μ N)
              (fun sample => Theorem2iii.sampledPosterior posterior sample))
            (Theorem2iii.expectedDatasetFidelityAt
              (Theorem2iii.iidSamplePMF μ N) prefAt) other ≤
          Pareto.weightedObjective γ
            (Theorem2iii.expectedDatasetAccuracy (Theorem2iii.iidSamplePMF μ N)
              (fun sample => Theorem2iii.sampledPosterior posterior sample))
            (Theorem2iii.expectedDatasetFidelityAt
              (Theorem2iii.iidSamplePMF μ N) prefAt)
            (fun sample => Theorem2iii.sampledDecision rule sample) := by
  rcases theorem2iii_source_exists_positive_mass_policy_improvement
      μ posterior rule argmaxRule hargmax hdisagree aggregateArgmax prefAt hPNq
      hNpos with
    ⟨sample, betterDecision, hsamplePos, hacc, hfid⟩
  exact
    Theorem2iii.not_expectedDatasetAt_weightedObjective_maximizer_of_positive_mass_sample_dominated
      (Theorem2iii.iidSamplePMF μ N)
      (fun s => Theorem2iii.sampledPosterior posterior s) prefAt
      (fun s => Theorem2iii.sampledDecision rule s) sample betterDecision
      hγnonneg hγlt hsamplePos hacc hfid

/--
Equivalent necessity form of the exact weighted endpoint: for `0 ≤ γ < 1`,
an independent expected-objective maximizer must agree with fixed-order argmax
almost surely.

Source status: exact theorem endpoint
Source note: The theorem keeps the source's dataset-dependent `P_N^q` reference and selected-label-only `1/N` premise.
-/
theorem theorem2iii_source_weighted_objective_maximizer_agrees_argmax
    {X : Type*} [Fintype X] [DecidableEq X] {N K : ℕ}
    (μ : PMF X) (posterior : X → Fin K → ℝ)
    (rule argmaxRule : X → Fin K)
    (hargmax : ∀ x, isFirstArgmax (posterior x) (argmaxRule x))
    (aggregateArgmax : (Fin N → X) → Fin K)
    (prefAt : (Fin N → X) → Fin K → ℝ)
    (hPNq : sourcePNq
      (fun sample : Fin N → X => Theorem2iii.sampledPosterior posterior sample)
      aggregateArgmax prefAt)
    {γ : ℝ} (hγnonneg : 0 ≤ γ) (hγlt : γ < 1)
    (hNpos : 0 < N)
    (hmax :
      ∀ other : (Fin N → X) → Fin N → Fin K,
        Pareto.weightedObjective γ
            (Theorem2iii.expectedDatasetAccuracy (Theorem2iii.iidSamplePMF μ N)
              (fun sample => Theorem2iii.sampledPosterior posterior sample))
            (Theorem2iii.expectedDatasetFidelityAt
              (Theorem2iii.iidSamplePMF μ N) prefAt) other ≤
          Pareto.weightedObjective γ
            (Theorem2iii.expectedDatasetAccuracy (Theorem2iii.iidSamplePMF μ N)
              (fun sample => Theorem2iii.sampledPosterior posterior sample))
            (Theorem2iii.expectedDatasetFidelityAt
              (Theorem2iii.iidSamplePMF μ N) prefAt)
            (fun sample => Theorem2iii.sampledDecision rule sample)) :
    AppliedModelingLib.pmfProb μ (fun x : X => rule x ≠ argmaxRule x) = 0 := by
  classical
  by_contra hne
  have hp_ne :
      AppliedModelingLib.pmfProb μ (fun x : X => rule x ≠ argmaxRule x) ≠ 0 := hne
  have hpos :
      0 < AppliedModelingLib.pmfProb μ (fun x : X => rule x ≠ argmaxRule x) :=
    lt_of_le_of_ne
      (AppliedModelingLib.pmfProb_nonneg μ (fun x : X => rule x ≠ argmaxRule x))
      hp_ne.symm
  exact
    (theorem2iii_source_non_argmax_not_expected_weightedObjective_maximizer
      μ posterior rule argmaxRule hargmax hpos aggregateArgmax prefAt hPNq
      hγnonneg hγlt hNpos) hmax

/-- Exact source proposition for Theorem 2(iii)'s weighted necessity clause. -/
def theorem2iiiWeightedObjectiveMaximizerAgreesArgmaxSpec
    {X : Type*} [Fintype X] [DecidableEq X] {N K : ℕ}
    (μ : PMF X) (posterior : X → Fin K → ℝ)
    (rule argmaxRule : X → Fin K)
    (aggregateArgmax : (Fin N → X) → Fin K)
    (prefAt : (Fin N → X) → Fin K → ℝ) (γ : ℝ) : Prop :=
  (∀ x, isFirstArgmax (posterior x) (argmaxRule x)) →
    sourcePNq
      (fun sample : Fin N → X => Theorem2iii.sampledPosterior posterior sample)
      aggregateArgmax prefAt →
    0 ≤ γ → γ < 1 → 0 < N →
    (∀ other : (Fin N → X) → Fin N → Fin K,
      Pareto.weightedObjective γ
          (Theorem2iii.expectedDatasetAccuracy (Theorem2iii.iidSamplePMF μ N)
            (fun sample => Theorem2iii.sampledPosterior posterior sample))
          (Theorem2iii.expectedDatasetFidelityAt
            (Theorem2iii.iidSamplePMF μ N) prefAt) other ≤
        Pareto.weightedObjective γ
          (Theorem2iii.expectedDatasetAccuracy (Theorem2iii.iidSamplePMF μ N)
            (fun sample => Theorem2iii.sampledPosterior posterior sample))
          (Theorem2iii.expectedDatasetFidelityAt
            (Theorem2iii.iidSamplePMF μ N) prefAt)
          (fun sample => Theorem2iii.sampledDecision rule sample)) →
    AppliedModelingLib.pmfProb μ (fun x : X => rule x ≠ argmaxRule x) = 0

/-- Lean evidence for the exact source weighted-objective proposition. -/
theorem theorem2iii_source_weighted_objective_maximizer_agrees_argmax_spec
    {X : Type*} [Fintype X] [DecidableEq X] {N K : ℕ}
    (μ : PMF X) (posterior : X → Fin K → ℝ)
    (rule argmaxRule : X → Fin K)
    (aggregateArgmax : (Fin N → X) → Fin K)
    (prefAt : (Fin N → X) → Fin K → ℝ) (γ : ℝ) :
    theorem2iiiWeightedObjectiveMaximizerAgreesArgmaxSpec
      μ posterior rule argmaxRule aggregateArgmax prefAt γ := by
  intro hargmax hPNq hγnonneg hγlt hNpos hmax
  exact theorem2iii_source_weighted_objective_maximizer_agrees_argmax
    μ posterior rule argmaxRule hargmax aggregateArgmax prefAt hPNq
    hγnonneg hγlt hNpos hmax

/--
Finite realized-randomness form of the exact Theorem 2(iii) endpoints.  The
atom type `Z` packages a feature with the randomness used by an independent
randomized rule; posterior scores, aggregate argmax, and `P_N^q` references
depend only on the projected feature dataset.

Source status: exact randomized-rule endpoint
Source note: This is the finite augmented-atom realization of the source's randomized independent rules.
-/
theorem theorem2iii_source_randomized_augmented_endpoints
    {Z X : Type*} [Fintype Z] [DecidableEq Z] {N K : ℕ}
    (ν : PMF Z) (feature : Z → X) (posterior : X → Fin K → ℝ)
    (rule : Z → Fin K) (argmaxRule : X → Fin K)
    (hargmax : ∀ x, isFirstArgmax (posterior x) (argmaxRule x))
    (hdisagree :
      0 < AppliedModelingLib.pmfProb ν
        (fun z : Z => rule z ≠ argmaxRule (feature z)))
    (aggregateArgmax : (Fin N → X) → Fin K)
    (prefAt : (Fin N → X) → Fin K → ℝ)
    (hPNq : sourcePNq
      (fun sample : Fin N → X => Theorem2iii.sampledPosterior posterior sample)
      aggregateArgmax prefAt)
    {γ : ℝ} (hγnonneg : 0 ≤ γ) (hγlt : γ < 1)
    (hNpos : 0 < N) :
    (¬ Pareto.ParetoOptimal
      (Theorem2iii.expectedDatasetAccuracy (Theorem2iii.iidSamplePMF ν N)
        (fun sample => Theorem2iii.sampledPosterior
          (fun z y => posterior (feature z) y) sample))
      (Theorem2iii.expectedDatasetFidelityAt (Theorem2iii.iidSamplePMF ν N)
        (fun sample => prefAt (fun i => feature (sample i))))
      (fun sample => Theorem2iii.sampledDecision rule sample)) ∧
    (¬ ∀ other : (Fin N → Z) → Fin N → Fin K,
      Pareto.weightedObjective γ
          (Theorem2iii.expectedDatasetAccuracy (Theorem2iii.iidSamplePMF ν N)
            (fun sample => Theorem2iii.sampledPosterior
              (fun z y => posterior (feature z) y) sample))
          (Theorem2iii.expectedDatasetFidelityAt (Theorem2iii.iidSamplePMF ν N)
            (fun sample => prefAt (fun i => feature (sample i)))) other ≤
        Pareto.weightedObjective γ
          (Theorem2iii.expectedDatasetAccuracy (Theorem2iii.iidSamplePMF ν N)
            (fun sample => Theorem2iii.sampledPosterior
              (fun z y => posterior (feature z) y) sample))
          (Theorem2iii.expectedDatasetFidelityAt (Theorem2iii.iidSamplePMF ν N)
            (fun sample => prefAt (fun i => feature (sample i))))
          (fun sample => Theorem2iii.sampledDecision rule sample)) := by
  have hPNqAugmented : sourcePNq
      (fun sample : Fin N → Z => Theorem2iii.sampledPosterior
        (fun z y => posterior (feature z) y) sample)
      (fun sample => aggregateArgmax (fun i => feature (sample i)))
      (fun sample => prefAt (fun i => feature (sample i))) := by
    constructor
    · intro sample
      exact hPNq.1 (fun i => feature (sample i))
    · constructor
      · intro sample
        simpa [Theorem2iii.sampledPosterior] using
          hPNq.2.1 (fun i => feature (sample i))
      · intro sample
        exact hPNq.2.2 (fun i => feature (sample i))
  constructor
  · exact theorem2iii_source_non_argmax_not_expected_pareto
      ν (fun z y => posterior (feature z) y) rule
      (fun z => argmaxRule (feature z)) (fun z => hargmax (feature z))
      hdisagree (fun sample => aggregateArgmax (fun i => feature (sample i)))
      (fun sample => prefAt (fun i => feature (sample i))) hPNqAugmented hNpos
  · exact theorem2iii_source_non_argmax_not_expected_weightedObjective_maximizer
      ν (fun z y => posterior (feature z) y) rule
      (fun z => argmaxRule (feature z)) (fun z => hargmax (feature z))
      hdisagree (fun sample => aggregateArgmax (fun i => feature (sample i)))
      (fun sample => prefAt (fun i => feature (sample i))) hPNqAugmented
      hγnonneg hγlt hNpos

/--
Fixed-reference support specialization for Theorem 2(iii): any independent
rule that disagrees with argmax with positive probability is not Pareto
optimal under a fixed reference satisfying a lower bound for every label.

Source status: stronger-premise specialization
Source note: The source uses a dataset-dependent reference family and requires
the `1/N` lower bound only for the selected aggregate-max class.  The exact
source endpoint is `theorem2iii_source_non_argmax_not_expected_pareto`.
-/
theorem theorem2iii_non_argmax_not_pareto
    {X : Type*} [Fintype X] [DecidableEq X] {N K : ℕ}
    (μ : PMF X) (posterior : X → Fin K → ℝ) (pref : Fin K → ℝ)
    (rule argmaxRule : X → Fin K)
    (hdisagree :
      0 < AppliedModelingLib.pmfProb μ (fun x : X => rule x ≠ argmaxRule x))
    (hNpos : 0 < N)
    (hpref_nonneg : ∀ y, 0 ≤ pref y)
    (hpref_sum : (∑ y : Fin K, pref y) = 1)
    (hnontrivial : ∀ y : Fin K, 1 / (N : ℝ) ≤ pref y)
    (hweak_argmax : ∀ x y, posterior x y ≤ posterior x (argmaxRule x)) :
    ¬ Pareto.ParetoOptimal
      (Theorem2iii.expectedDatasetAccuracy (Theorem2iii.iidSamplePMF μ N)
        (fun s => Theorem2iii.sampledPosterior posterior s))
      (Theorem2iii.expectedDatasetFidelity (Theorem2iii.iidSamplePMF μ N) pref)
      (fun s => Theorem2iii.sampledDecision rule s) := by
  exact
    Theorem2iii.paper_theorem2iii_not_expected_pareto_of_independent_rule_disagrees_pos
      μ posterior pref rule argmaxRule hdisagree hNpos hpref_nonneg hpref_sum
      hnontrivial hweak_argmax

/--
Fixed-reference support specialization of Theorem 2(iii)'s weighted-objective
claim for `gamma < 1`.

Source status: stronger-premise specialization
Source note: As above, this wrapper fixes `pref` and assumes the all-label
lower bound.  It is not the exact source endpoint.
-/
theorem theorem2iii_weighted_objective_maximizer_agrees_argmax
    {X : Type*} [Fintype X] [DecidableEq X] {N K : ℕ}
    (μ : PMF X) (posterior : X → Fin K → ℝ) (pref : Fin K → ℝ)
    (rule argmaxRule : X → Fin K)
    {γ : ℝ} (hγnonneg : 0 ≤ γ) (hγlt : γ < 1)
    (hNpos : 0 < N)
    (hpref_nonneg : ∀ y, 0 ≤ pref y)
    (hpref_sum : (∑ y : Fin K, pref y) = 1)
    (hnontrivial : ∀ y : Fin K, 1 / (N : ℝ) ≤ pref y)
    (hweak_argmax : ∀ x y, posterior x y ≤ posterior x (argmaxRule x))
    (hmax :
      ∀ other : (Fin N → X) → Fin N → Fin K,
        Pareto.weightedObjective γ
            (Theorem2iii.expectedDatasetAccuracy (Theorem2iii.iidSamplePMF μ N)
              (fun s => Theorem2iii.sampledPosterior posterior s))
            (Theorem2iii.expectedDatasetFidelity (Theorem2iii.iidSamplePMF μ N) pref) other ≤
          Pareto.weightedObjective γ
            (Theorem2iii.expectedDatasetAccuracy (Theorem2iii.iidSamplePMF μ N)
              (fun s => Theorem2iii.sampledPosterior posterior s))
            (Theorem2iii.expectedDatasetFidelity (Theorem2iii.iidSamplePMF μ N) pref)
            (fun s => Theorem2iii.sampledDecision rule s)) :
    AppliedModelingLib.pmfProb μ (fun x : X => rule x ≠ argmaxRule x) = 0 := by
  classical
  by_contra hzero
  have hp_ne : AppliedModelingLib.pmfProb μ (fun x : X => rule x ≠ argmaxRule x) ≠ 0 :=
    hzero
  have hnonneg :
      0 ≤ AppliedModelingLib.pmfProb μ (fun x : X => rule x ≠ argmaxRule x) :=
    AppliedModelingLib.pmfProb_nonneg μ (fun x : X => rule x ≠ argmaxRule x)
  have hpos : 0 < AppliedModelingLib.pmfProb μ (fun x : X => rule x ≠ argmaxRule x) :=
    lt_of_le_of_ne hnonneg hp_ne.symm
  exact
    (Theorem2iii.paper_theorem2iii_not_expected_weightedObjective_maximizer_of_independent_rule_disagrees_pos
      μ posterior pref rule argmaxRule hγnonneg hγlt hpos hNpos
      hpref_nonneg hpref_sum hnontrivial hweak_argmax) hmax

/--
Theorem 2(iii), `gamma = 1` boundary: if every positive-probability
disagreement is posterior-strict, then a disagreeing independent rule is not a
weighted-objective maximizer even at the accuracy-only boundary.

Source status: source-domain strengthening
Source note: This boundary row records the strict-disagreement case used to separate source-facing uniqueness behavior.
-/
theorem theorem2iii_strict_disagreement_not_weighted_objective_maximizer
    {X : Type*} [Fintype X] [DecidableEq X] {N K : ℕ}
    (μ : PMF X) (posterior : X → Fin K → ℝ) (pref : Fin K → ℝ)
    (rule argmaxRule : X → Fin K)
    {γ : ℝ} (hγpos : 0 < γ) (hγle : γ ≤ 1)
    (hdisagree :
      0 < AppliedModelingLib.pmfProb μ (fun x : X => rule x ≠ argmaxRule x))
    (hNpos : 0 < N)
    (hpref_nonneg : ∀ y, 0 ≤ pref y)
    (hpref_sum : (∑ y : Fin K, pref y) = 1)
    (hnontrivial : ∀ y : Fin K, 1 / (N : ℝ) ≤ pref y)
    (hstrict_argmax :
      ∀ x, rule x ≠ argmaxRule x →
        posterior x (rule x) < posterior x (argmaxRule x)) :
    ¬ ∀ other : (Fin N → X) → Fin N → Fin K,
        Pareto.weightedObjective γ
            (Theorem2iii.expectedDatasetAccuracy (Theorem2iii.iidSamplePMF μ N)
              (fun s => Theorem2iii.sampledPosterior posterior s))
            (Theorem2iii.expectedDatasetFidelity (Theorem2iii.iidSamplePMF μ N) pref) other ≤
          Pareto.weightedObjective γ
            (Theorem2iii.expectedDatasetAccuracy (Theorem2iii.iidSamplePMF μ N)
              (fun s => Theorem2iii.sampledPosterior posterior s))
            (Theorem2iii.expectedDatasetFidelity (Theorem2iii.iidSamplePMF μ N) pref)
            (fun s => Theorem2iii.sampledDecision rule s) := by
  exact
    Theorem2iii.paper_theorem2iii_not_expected_weightedObjective_maximizer_of_independent_rule_disagrees_pos_strict_argmax
      μ posterior pref rule argmaxRule hγpos hγle hdisagree hNpos hpref_nonneg
      hpref_sum hnontrivial hstrict_argmax

end

end ProofBridge
end DSWG24DiscretizationBias
