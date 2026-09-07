import AppliedModelingLib.Learning.Prediction.Calibration.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Bool.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Binary omniprediction primitives

Paper-independent finite-horizon objects for binary omniprediction.  The
definitions retain the source convention that losses are evaluated at a real
report, while hypotheses and forecasts carry their `[0,1]` range conditions
explicitly in theorem hypotheses.

The central algebraic theorem is
`omniPairRegret_le_calibration_add_multiaccuracy`.  It is the exact
one-loss/one-hypothesis form of the proper-calibration plus multiaccuracy
reduction used in omniprediction papers; finite maxima or suprema can be added
at the consumer layer.
-/

namespace AppliedModelingLib.Learning.Prediction

open scoped BigOperators

/-- A loss evaluated at a real-valued report and a binary outcome. -/
abbrev BinaryLoss := ℝ → Bool → ℝ

/-- The real encoding of a binary outcome. -/
def binaryOutcomeValue : Bool → ℝ
  | true => 1
  | false => 0

/-- A signed threshold on a finite ordered report grid.  This is the discrete
test family used to reduce bounded proper calibration to finitely many
coordinate payoffs. -/
def finiteGridThreshold {n : ℕ} (level report : Fin n) : ℝ :=
  if level ≤ report then 1 else -1

/-- Finite signed thresholds have unit magnitude. -/
@[simp] theorem abs_finiteGridThreshold {n : ℕ} (level report : Fin n) :
    |finiteGridThreshold level report| = 1 := by
  unfold finiteGridThreshold
  split <;> norm_num

/-- The expected loss of report `a` under a Bernoulli outcome with mean `q`. -/
def bernoulliRisk (loss : BinaryLoss) (q a : ℝ) : ℝ :=
  q * loss a true + (1 - q) * loss a false

/-- The source paper's discrete derivative `Δℓ(a) = ℓ(a,1)-ℓ(a,0)`. -/
def discreteDerivative (loss : BinaryLoss) (a : ℝ) : ℝ :=
  loss a true - loss a false

/-- View a curried binary loss as a function on report/outcome pairs. -/
def uncurryBinaryLoss (loss : BinaryLoss) : ℝ × Bool → ℝ :=
  fun pair => loss pair.1 pair.2

/-- The discrete derivative of an uncurried binary loss. -/
def uncurriedDiscreteDerivative (loss : ℝ × Bool → ℝ) (a : ℝ) : ℝ :=
  loss (a, true) - loss (a, false)

/-- A binary-loss class represented as a class of functions on report/outcome
pairs, convenient for uniform approximation statements. -/
def uncurriedBinaryLossClass (losses : Set BinaryLoss) : Set (ℝ × Bool → ℝ) :=
  { uncurried | ∃ loss ∈ losses, uncurried = uncurryBinaryLoss loss }

/-- Discrete derivatives of a class of uncurried binary losses. -/
def uncurriedDerivativeClass (losses : Set (ℝ × Bool → ℝ)) : Set (ℝ → ℝ) :=
  { derivative | ∃ loss ∈ losses, derivative = uncurriedDiscreteDerivative loss }

/-- Currying does not alter the discrete derivative. -/
@[simp] theorem uncurriedDiscreteDerivative_uncurryBinaryLoss
    (loss : BinaryLoss) (a : ℝ) :
    uncurriedDiscreteDerivative (uncurryBinaryLoss loss) a = discreteDerivative loss a := rfl

/-- A binary loss is proper on the report interval when truthful reporting is
a Bayes action for every Bernoulli mean in that interval. -/
def IsProperBinaryLoss (loss : BinaryLoss) : Prop :=
  ∀ ⦃q a : ℝ⦄, q ∈ Set.Icc (0 : ℝ) 1 → a ∈ Set.Icc (0 : ℝ) 1 →
    bernoulliRisk loss q q ≤ bernoulliRisk loss q a

/-- The paper's loss universe consists of losses bounded by one on the
probability-report domain.  The bound is part of the class, rather than a
consequence of properness. -/
def IsUnitBoundedBinaryLoss (loss : BinaryLoss) : Prop :=
  ∀ ⦃report : ℝ⦄, report ∈ Set.Icc (0 : ℝ) 1 → ∀ outcome : Bool,
    loss report outcome ∈ Set.Icc (-1 : ℝ) 1

/-- Properness makes the discrete derivative antitone on probability reports.
This is the finite-dimensional form of the scoring-rule monotonicity used in
the threshold decomposition of proper calibration. -/
theorem discreteDerivative_antitone_of_proper
    {loss : BinaryLoss} (hproper : IsProperBinaryLoss loss)
    {p q : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (hpq : p ≤ q) :
    discreteDerivative loss q ≤ discreteDerivative loss p := by
  have hpAtQ : bernoulliRisk loss p p ≤ bernoulliRisk loss p q :=
    hproper hp hq
  have hqAtP : bernoulliRisk loss q q ≤ bernoulliRisk loss q p :=
    hproper hq hp
  have hsum : 0 ≤
      (bernoulliRisk loss p q - bernoulliRisk loss p p) +
        (bernoulliRisk loss q p - bernoulliRisk loss q q) := by
    linarith
  have hidentity :
      (bernoulliRisk loss p q - bernoulliRisk loss p p) +
        (bernoulliRisk loss q p - bernoulliRisk loss q q) =
      (q - p) * (discreteDerivative loss p - discreteDerivative loss q) := by
    unfold bernoulliRisk discreteDerivative
    ring
  rw [hidentity] at hsum
  by_cases hpqEq : p = q
  · simpa [hpqEq]
  · have hpqLt : p < q := lt_of_le_of_ne hpq hpqEq
    have hpositive : 0 < q - p := sub_pos.mpr hpqLt
    nlinarith

/-- A bounded binary loss has discrete derivative in `[-2,2]`. -/
theorem discreteDerivative_abs_le_two_of_unitBounded
    {loss : BinaryLoss} (hloss : IsUnitBoundedBinaryLoss loss)
    {report : ℝ} (hreport : report ∈ Set.Icc (0 : ℝ) 1) :
    |discreteDerivative loss report| ≤ 2 := by
  have hzero := hloss hreport false
  have hone := hloss hreport true
  rcases hzero with ⟨hzeroLower, hzeroUpper⟩
  rcases hone with ⟨honeLower, honeUpper⟩
  unfold discreteDerivative
  rw [abs_le]
  constructor <;> linarith

/-- A postprocessor chooses a Bayes report for every valid Bernoulli mean. -/
def IsBayesPostprocessor (loss : BinaryLoss) (postprocess : ℝ → ℝ) : Prop :=
  (∀ ⦃q : ℝ⦄, q ∈ Set.Icc (0 : ℝ) 1 → postprocess q ∈ Set.Icc (0 : ℝ) 1) ∧
  ∀ ⦃q a : ℝ⦄, q ∈ Set.Icc (0 : ℝ) 1 → a ∈ Set.Icc (0 : ℝ) 1 →
    bernoulliRisk loss q (postprocess q) ≤ bernoulliRisk loss q a

/-- Compose a loss with a report postprocessor. -/
def postprocessedLoss (loss : BinaryLoss) (postprocess : ℝ → ℝ) : BinaryLoss :=
  fun q y => loss (postprocess q) y

/-- A Bayes postprocessor turns an arbitrary loss into a proper loss. -/
theorem postprocessedLoss_isProper
    {loss : BinaryLoss} {postprocess : ℝ → ℝ}
    (hpostprocess : IsBayesPostprocessor loss postprocess) :
    IsProperBinaryLoss (postprocessedLoss loss postprocess) := by
  intro q a hq ha
  exact hpostprocess.2 hq (hpostprocess.1 ha)

/-- Bayes postprocessing preserves the source loss bound because it maps the
unit interval back into itself. -/
theorem postprocessedLoss_isUnitBounded
    {loss : BinaryLoss} {postprocess : ℝ → ℝ}
    (hloss : IsUnitBoundedBinaryLoss loss)
    (hpostprocess : IsBayesPostprocessor loss postprocess) :
    IsUnitBoundedBinaryLoss (postprocessedLoss loss postprocess) := by
  intro report hreport outcome
  exact hloss (hpostprocess.1 hreport) outcome

/-- A finite-horizon forecaster, allowed to choose a feature-dependent report
on each round. -/
abbrev ForecastSequence (X : Type*) (horizon : ℕ) := Fin horizon → X → ℝ

/-- The real residual `y_t-p_t(x_t)` on one round. -/
def forecastResidual {X : Type*} {horizon : ℕ}
    (forecasts : ForecastSequence X horizon) (contexts : Fin horizon → X)
    (outcomes : Fin horizon → Bool) (round : Fin horizon) : ℝ :=
  binaryOutcomeValue (outcomes round) - forecasts round (contexts round)

/-- All reports issued along a finite realized path lie in the unit interval. -/
def ForecastsInUnitInterval {X : Type*} {horizon : ℕ}
    (forecasts : ForecastSequence X horizon) (contexts : Fin horizon → X) : Prop :=
  ∀ round, forecasts round (contexts round) ∈ Set.Icc (0 : ℝ) 1

/-- A binary outcome minus a realized unit-interval forecast has magnitude at
most one.  This elementary bound is the common residual hypothesis in the
finite approximate-basis and omniprediction reductions. -/
theorem forecastResidual_abs_le_one {X : Type*} {horizon : ℕ}
    (forecasts : ForecastSequence X horizon) (contexts : Fin horizon → X)
    (outcomes : Fin horizon → Bool)
    (hforecasts : ForecastsInUnitInterval forecasts contexts) (round : Fin horizon) :
    |forecastResidual forecasts contexts outcomes round| ≤ 1 := by
  have hreport := hforecasts round
  unfold forecastResidual
  cases outcomes round
  · simpa [binaryOutcomeValue, abs_of_nonneg hreport.1] using hreport.2
  · rw [binaryOutcomeValue, abs_le]
    constructor <;> linarith [hreport.1, hreport.2]

/-- A hypothesis takes only valid binary-probability reports. -/
def HypothesisInUnitInterval {X : Type*} (hypothesis : X → ℝ) : Prop :=
  ∀ x, hypothesis x ∈ Set.Icc (0 : ℝ) 1

/-- Residual correlation with a feature test. -/
def multiaccuracyCorrelation {X : Type*} {horizon : ℕ}
    (test : X → ℝ) (forecasts : ForecastSequence X horizon)
    (contexts : Fin horizon → X) (outcomes : Fin horizon → Bool) : ℝ :=
  ∑ round, test (contexts round) * forecastResidual forecasts contexts outcomes round

/-- Residual correlation with a report-dependent calibration weight. -/
def calibrationCorrelation {X : Type*} {horizon : ℕ}
    (weight : ℝ → ℝ) (forecasts : ForecastSequence X horizon)
    (contexts : Fin horizon → X) (outcomes : Fin horizon → Bool) : ℝ :=
  ∑ round, weight (forecasts round (contexts round)) *
    forecastResidual forecasts contexts outcomes round

/-- Residual correlation with a time-varying feature test, as produced by a
sequential weak-learning oracle. -/
def timeVaryingResidualCorrelation {X : Type*} {horizon : ℕ}
    (tests : Fin horizon → X → ℝ) (forecasts : ForecastSequence X horizon)
    (contexts : Fin horizon → X) (outcomes : Fin horizon → Bool) : ℝ :=
  ∑ round, tests round (contexts round) *
    forecastResidual forecasts contexts outcomes round

/-- The finite realized-path form of an online weak agnostic learner's
one-sided guarantee, specialized to the residual labels used in
omniprediction. -/
def ResidualWeakAgnosticGuarantee {X : Type*} {horizon : ℕ}
    (tests : Set (X → ℝ)) (oracleOutputs : Fin horizon → X → ℝ)
    (forecasts : ForecastSequence X horizon) (contexts : Fin horizon → X)
    (outcomes : Fin horizon → Bool) (regretBound : ℝ) : Prop :=
  ∀ test ∈ tests,
    multiaccuracyCorrelation test forecasts contexts outcomes ≤
      timeVaryingResidualCorrelation oracleOutputs forecasts contexts outcomes + regretBound

/-- Every calibration weight in a class has correlation at most `bound` in
absolute value. -/
def CalibrationBound {X : Type*} {horizon : ℕ} (weights : Set (ℝ → ℝ))
    (forecasts : ForecastSequence X horizon) (contexts : Fin horizon → X)
    (outcomes : Fin horizon → Bool) (bound : ℝ) : Prop :=
  ∀ weight ∈ weights,
    |calibrationCorrelation weight forecasts contexts outcomes| ≤ bound

/-- Every feature test in a class has residual correlation at most `bound` in
absolute value. -/
def MultiaccuracyBound {X : Type*} {horizon : ℕ} (tests : Set (X → ℝ))
    (forecasts : ForecastSequence X horizon) (contexts : Fin horizon → X)
    (outcomes : Fin horizon → Bool) (bound : ℝ) : Prop :=
  ∀ test ∈ tests,
    |multiaccuracyCorrelation test forecasts contexts outcomes| ≤ bound

/-- One-sided residual correlation control, the convention supplied directly
by an online weak agnostic learner. -/
def OneSidedMultiaccuracyBound {X : Type*} {horizon : ℕ} (tests : Set (X → ℝ))
    (forecasts : ForecastSequence X horizon) (contexts : Fin horizon → X)
    (outcomes : Fin horizon → Bool) (bound : ℝ) : Prop :=
  ∀ test ∈ tests,
    multiaccuracyCorrelation test forecasts contexts outcomes ≤ bound

/-- Add a positive and a negative copy of every test.  This is the source
class `{-1,+1}·C` used to turn one-sided OWAL control into absolute
multiaccuracy. -/
def signedTestClass {X : Type*} (tests : Set (X → ℝ)) : Set (X → ℝ) :=
  { signedTest | ∃ test ∈ tests,
    signedTest = test ∨ signedTest = fun x => -test x }

/-- Tie-breaking convention needed to identify fixed-selector Decision OI with
proper calibration: a proper loss is postprocessed by the identity.  Without
this convention, `argmin` in the paper is set-valued and the reverse
inequality is not determined. -/
def IsIdentityOnProperLosses (postprocess : BinaryLoss → ℝ → ℝ) : Prop :=
  ∀ ⦃loss : BinaryLoss⦄, IsProperBinaryLoss loss → ∀ ⦃q : ℝ⦄,
    q ∈ Set.Icc (0 : ℝ) 1 → postprocess loss q = q

/-- Discrete derivatives of bounded proper binary losses, the source paper's
proper-calibration test class.  Boundedness is essential: without it, a
positive rescaling of any proper loss would make the calibration supremum
infinite. -/
def properDerivativeClass : Set (ℝ → ℝ) :=
  { weight | ∃ loss : BinaryLoss, IsProperBinaryLoss loss ∧ IsUnitBoundedBinaryLoss loss ∧
    weight = discreteDerivative loss }

/-- The calibration-test class obtained by Bayes-postprocessing a family of
losses. -/
def postprocessedDerivativeClass (losses : Set BinaryLoss)
    (postprocess : BinaryLoss → ℝ → ℝ) : Set (ℝ → ℝ) :=
  { weight | ∃ loss ∈ losses,
    weight = discreteDerivative (postprocessedLoss loss (postprocess loss)) }

/-- The feature-test class `ΔL∘H` used by the omniprediction reduction. -/
def derivativeHypothesisClass {X : Type*} (losses : Set BinaryLoss)
    (hypotheses : Set (X → ℝ)) : Set (X → ℝ) :=
  { test | ∃ loss ∈ losses, ∃ hypothesis ∈ hypotheses,
    test = fun x => discreteDerivative loss (hypothesis x) }

/-- One loss's Decision-OI discrepancy on a finite realized sequence. -/
def decisionOIDiscrepancy {X : Type*} {horizon : ℕ}
    (loss : BinaryLoss) (postprocess : ℝ → ℝ)
    (forecasts : ForecastSequence X horizon) (contexts : Fin horizon → X)
    (outcomes : Fin horizon → Bool) : ℝ :=
  ∑ round : Fin horizon, (
    loss (postprocess (forecasts round (contexts round))) (outcomes round) -
      bernoulliRisk loss (forecasts round (contexts round))
        (postprocess (forecasts round (contexts round))))

/-- The sequential Decision-OI objective for the paper's bounded loss
universe, expressed as a family of absolute correlation bounds rather than an
ambient supremum. -/
def AllLossDecisionOIControlled {X : Type*} {horizon : ℕ}
    (postprocess : BinaryLoss → ℝ → ℝ)
    (forecasts : ForecastSequence X horizon) (contexts : Fin horizon → X)
  (outcomes : Fin horizon → Bool) (bound : ℝ) : Prop :=
  ∀ loss : BinaryLoss,
    IsUnitBoundedBinaryLoss loss →
    |decisionOIDiscrepancy loss (postprocess loss) forecasts contexts outcomes| ≤ bound

/-- One loss/hypothesis comparator's sequential omniprediction regret. -/
def omniPairRegret {X : Type*} {horizon : ℕ}
    (loss : BinaryLoss) (postprocess : ℝ → ℝ) (hypothesis : X → ℝ)
    (forecasts : ForecastSequence X horizon) (contexts : Fin horizon → X)
    (outcomes : Fin horizon → Bool) : ℝ :=
  ∑ round : Fin horizon, (
    loss (postprocess (forecasts round (contexts round))) (outcomes round) -
      loss (hypothesis (contexts round)) (outcomes round))

/-- The difference between realized and Bernoulli-expected loss is its
discrete derivative times the residual. -/
theorem realizedLoss_sub_bernoulliRisk_eq_residual_mul_derivative
    (loss : BinaryLoss) (q a : ℝ) (outcome : Bool) :
    loss a outcome - bernoulliRisk loss q a =
      (binaryOutcomeValue outcome - q) * discreteDerivative loss a := by
  cases outcome <;> simp [bernoulliRisk, binaryOutcomeValue, discreteDerivative] <;> ring

/-- The reverse realized/expected difference has the opposite residual sign. -/
theorem bernoulliRisk_sub_realizedLoss_eq_neg_residual_mul_derivative
    (loss : BinaryLoss) (q a : ℝ) (outcome : Bool) :
    bernoulliRisk loss q a - loss a outcome =
      -(binaryOutcomeValue outcome - q) * discreteDerivative loss a := by
  rw [← neg_sub]
  rw [realizedLoss_sub_bernoulliRisk_eq_residual_mul_derivative]
  ring

/-- Decision OI for a loss is exactly calibration correlation with the
discrete derivative of its postprocessed loss. -/
theorem decisionOIDiscrepancy_eq_calibrationCorrelation
    {X : Type*} {horizon : ℕ} (loss : BinaryLoss) (postprocess : ℝ → ℝ)
    (forecasts : ForecastSequence X horizon) (contexts : Fin horizon → X)
    (outcomes : Fin horizon → Bool) :
    decisionOIDiscrepancy loss postprocess forecasts contexts outcomes =
      calibrationCorrelation (discreteDerivative (postprocessedLoss loss postprocess))
        forecasts contexts outcomes := by
  unfold decisionOIDiscrepancy calibrationCorrelation forecastResidual postprocessedLoss
  apply Finset.sum_congr rfl
  intro round _
  rw [realizedLoss_sub_bernoulliRisk_eq_residual_mul_derivative]
  simp only [discreteDerivative]
  ring

/-- The source's decision-OI bound follows from proper calibration whenever
the selected postprocessor is Bayes-optimal. -/
theorem decisionOIDiscrepancy_abs_le_of_properCalibration
    {X : Type*} {horizon : ℕ} {loss : BinaryLoss} {postprocess : ℝ → ℝ}
    {forecasts : ForecastSequence X horizon} {contexts : Fin horizon → X}
    {outcomes : Fin horizon → Bool} {bound : ℝ}
    (hloss : IsUnitBoundedBinaryLoss loss)
    (hpostprocess : IsBayesPostprocessor loss postprocess)
    (hcalibration : CalibrationBound properDerivativeClass forecasts contexts outcomes bound) :
    |decisionOIDiscrepancy loss postprocess forecasts contexts outcomes| ≤ bound := by
  rw [decisionOIDiscrepancy_eq_calibrationCorrelation]
  apply hcalibration
  refine ⟨postprocessedLoss loss postprocess,
    postprocessedLoss_isProper hpostprocess,
    postprocessedLoss_isUnitBounded hloss hpostprocess, rfl⟩

/-- Proper calibration controls all-loss Decision OI when every source
postprocessor is Bayes-optimal. -/
theorem allLossDecisionOIControlled_of_properCalibration
    {X : Type*} {horizon : ℕ} {postprocess : BinaryLoss → ℝ → ℝ}
    {forecasts : ForecastSequence X horizon} {contexts : Fin horizon → X}
    {outcomes : Fin horizon → Bool} {bound : ℝ}
  (hbayes : ∀ loss : BinaryLoss, IsBayesPostprocessor loss (postprocess loss))
    (hcalibration : CalibrationBound properDerivativeClass forecasts contexts outcomes bound) :
    AllLossDecisionOIControlled postprocess forecasts contexts outcomes bound := by
  intro loss hloss
  exact decisionOIDiscrepancy_abs_le_of_properCalibration hloss (hbayes loss) hcalibration

/-- Calibration correlation is unchanged when two weights agree at every
realized forecast. -/
theorem calibrationCorrelation_congr_on_forecasts
    {X : Type*} {horizon : ℕ} {weight weight' : ℝ → ℝ}
    {forecasts : ForecastSequence X horizon} {contexts : Fin horizon → X}
    {outcomes : Fin horizon → Bool}
    (hweight : ∀ round, weight (forecasts round (contexts round)) =
      weight' (forecasts round (contexts round))) :
    calibrationCorrelation weight forecasts contexts outcomes =
      calibrationCorrelation weight' forecasts contexts outcomes := by
  unfold calibrationCorrelation
  apply Finset.sum_congr rfl
  intro round _
  rw [hweight round]

/-- Negating a feature test negates its finite-horizon residual correlation. -/
theorem multiaccuracyCorrelation_neg_test
    {X : Type*} {horizon : ℕ} (test : X → ℝ)
    (forecasts : ForecastSequence X horizon) (contexts : Fin horizon → X)
    (outcomes : Fin horizon → Bool) :
    multiaccuracyCorrelation (fun x => -test x) forecasts contexts outcomes =
      -multiaccuracyCorrelation test forecasts contexts outcomes := by
  unfold multiaccuracyCorrelation
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro round _
  ring

/-- One-sided control on the signed closure of a class is precisely absolute
multiaccuracy control on the original class. -/
theorem multiaccuracyBound_of_oneSided_signedTestClass
    {X : Type*} {horizon : ℕ} {tests : Set (X → ℝ)}
    {forecasts : ForecastSequence X horizon} {contexts : Fin horizon → X}
    {outcomes : Fin horizon → Bool} {bound : ℝ}
    (honeSided : OneSidedMultiaccuracyBound (signedTestClass tests)
      forecasts contexts outcomes bound) :
    MultiaccuracyBound tests forecasts contexts outcomes bound := by
  intro test htest
  have hupper : multiaccuracyCorrelation test forecasts contexts outcomes ≤ bound :=
    honeSided test ⟨test, htest, Or.inl rfl⟩
  have hnegative : multiaccuracyCorrelation (fun x => -test x)
      forecasts contexts outcomes ≤ bound :=
    honeSided (fun x => -test x) ⟨test, htest, Or.inr rfl⟩
  rw [multiaccuracyCorrelation_neg_test] at hnegative
  exact abs_le.mpr ⟨by linarith, hupper⟩

/-- Under identity tie-breaking for proper losses, all-loss Decision OI
controls proper calibration. -/
theorem properCalibration_of_allLossDecisionOIControlled
    {X : Type*} {horizon : ℕ} {postprocess : BinaryLoss → ℝ → ℝ}
    {forecasts : ForecastSequence X horizon} {contexts : Fin horizon → X}
    {outcomes : Fin horizon → Bool} {bound : ℝ}
    (hforecasts : ForecastsInUnitInterval forecasts contexts)
    (hidentity : IsIdentityOnProperLosses postprocess)
    (hdecision : AllLossDecisionOIControlled postprocess forecasts contexts outcomes bound) :
    CalibrationBound properDerivativeClass forecasts contexts outcomes bound := by
  intro weight hweight
  rcases hweight with ⟨loss, hlossProper, hlossBounded, rfl⟩
  have hsource := hdecision loss hlossBounded
  rw [decisionOIDiscrepancy_eq_calibrationCorrelation] at hsource
  rw [calibrationCorrelation_congr_on_forecasts
    (weight := discreteDerivative (postprocessedLoss loss (postprocess loss)))
    (weight' := discreteDerivative loss)
    (fun round => by
      simp only [discreteDerivative, postprocessedLoss]
      rw [hidentity hlossProper (hforecasts round)])] at hsource
  exact hsource

/-- The sequential form of the source's Decision-OI/proper-calibration
equivalence, with the necessary explicit tie-breaking convention. -/
theorem allLossDecisionOIControlled_iff_properCalibration
    {X : Type*} {horizon : ℕ} {postprocess : BinaryLoss → ℝ → ℝ}
    {forecasts : ForecastSequence X horizon} {contexts : Fin horizon → X}
    {outcomes : Fin horizon → Bool} {bound : ℝ}
    (hbayes : ∀ loss : BinaryLoss, IsBayesPostprocessor loss (postprocess loss))
    (hforecasts : ForecastsInUnitInterval forecasts contexts)
    (hidentity : IsIdentityOnProperLosses postprocess) :
    AllLossDecisionOIControlled postprocess forecasts contexts outcomes bound ↔
      CalibrationBound properDerivativeClass forecasts contexts outcomes bound := by
  constructor
  · exact properCalibration_of_allLossDecisionOIControlled hforecasts hidentity
  · exact allLossDecisionOIControlled_of_properCalibration hbayes

/-- A one-round Bayes-optimality decomposition of an omniprediction comparator
gap.  This is the local calculation behind OKK25 Lemma 3.2. -/
theorem omniPairRegret_le_residual_terms
    {X : Type*} {horizon : ℕ} {loss : BinaryLoss} {postprocess : ℝ → ℝ}
    {hypothesis : X → ℝ} {forecasts : ForecastSequence X horizon}
    {contexts : Fin horizon → X} {outcomes : Fin horizon → Bool}
    (hpostprocess : IsBayesPostprocessor loss postprocess)
    (hforecasts : ForecastsInUnitInterval forecasts contexts)
    (hhypothesis : HypothesisInUnitInterval hypothesis) :
    omniPairRegret loss postprocess hypothesis forecasts contexts outcomes ≤
      decisionOIDiscrepancy loss postprocess forecasts contexts outcomes -
        multiaccuracyCorrelation (fun x => discreteDerivative loss (hypothesis x))
          forecasts contexts outcomes := by
  unfold omniPairRegret decisionOIDiscrepancy multiaccuracyCorrelation
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro round _
  let q := forecasts round (contexts round)
  let a := hypothesis (contexts round)
  let r := postprocess q
  let y := outcomes round
  have hbayes : bernoulliRisk loss q r ≤ bernoulliRisk loss q a :=
    hpostprocess.2 (hforecasts round) (hhypothesis (contexts round))
  have hleft := realizedLoss_sub_bernoulliRisk_eq_residual_mul_derivative loss q r y
  have hright := bernoulliRisk_sub_realizedLoss_eq_neg_residual_mul_derivative loss q a y
  dsimp [q, a, r, y, forecastResidual] at hbayes hleft hright ⊢
  linarith

/-- Proper calibration plus multiaccuracy gives the source paper's
one-loss/one-hypothesis omniprediction bound.  Unlike a finite `max` wrapper,
this form works for arbitrary loss and hypothesis classes. -/
theorem omniPairRegret_le_calibration_add_multiaccuracy
    {X : Type*} {horizon : ℕ} {losses : Set BinaryLoss}
    {postprocess : BinaryLoss → ℝ → ℝ} {hypotheses : Set (X → ℝ)}
    {loss : BinaryLoss} {hypothesis : X → ℝ}
    {forecasts : ForecastSequence X horizon} {contexts : Fin horizon → X}
    {outcomes : Fin horizon → Bool} {calibrationBound multiaccuracyBound : ℝ}
    (hloss : loss ∈ losses) (hhypothesisClass : hypothesis ∈ hypotheses)
    (hpostprocess : IsBayesPostprocessor loss (postprocess loss))
    (hforecasts : ForecastsInUnitInterval forecasts contexts)
    (hhypothesis : HypothesisInUnitInterval hypothesis)
    (hcalibration :
      CalibrationBound (postprocessedDerivativeClass losses postprocess)
        forecasts contexts outcomes calibrationBound)
    (hmultiaccuracy :
      MultiaccuracyBound (derivativeHypothesisClass losses hypotheses)
        forecasts contexts outcomes multiaccuracyBound) :
    omniPairRegret loss (postprocess loss) hypothesis forecasts contexts outcomes ≤
      calibrationBound + multiaccuracyBound := by
  calc
    omniPairRegret loss (postprocess loss) hypothesis forecasts contexts outcomes ≤
        decisionOIDiscrepancy loss (postprocess loss) forecasts contexts outcomes -
          multiaccuracyCorrelation (fun x => discreteDerivative loss (hypothesis x))
            forecasts contexts outcomes :=
      omniPairRegret_le_residual_terms hpostprocess hforecasts hhypothesis
    _ ≤ |decisionOIDiscrepancy loss (postprocess loss) forecasts contexts outcomes| +
          |multiaccuracyCorrelation (fun x => discreteDerivative loss (hypothesis x))
            forecasts contexts outcomes| := by
      exact (le_abs_self _).trans (by
        simpa using (_root_.abs_sub_le
          (decisionOIDiscrepancy loss (postprocess loss) forecasts contexts outcomes)
          0
          (multiaccuracyCorrelation (fun x => discreteDerivative loss (hypothesis x))
            forecasts contexts outcomes)))
    _ ≤ calibrationBound + multiaccuracyBound := by
      gcongr
      · rw [decisionOIDiscrepancy_eq_calibrationCorrelation]
        apply hcalibration
        exact ⟨loss, hloss, rfl⟩
      · apply hmultiaccuracy
        exact ⟨loss, hloss, hypothesis, hhypothesisClass, rfl⟩

end AppliedModelingLib.Learning.Prediction
