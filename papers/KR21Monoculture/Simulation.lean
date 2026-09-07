import KR21Monoculture.Distributional
import AppliedModelingLib.Foundations.Probability.MeasureInequalities

open AppliedModelingLib MeasureTheory
open ProbabilityTheory

namespace KR21Monoculture

/-!
# The finite-sample test mentioned after Theorem 2

The source says that Definitions 2 and 3 can be tested efficiently when the
value and ranking laws are sampleable, but does not specify an estimator or a
confidence statement.  The definitions below give the natural unbiased score,
the empirical-mean sign test, an exact linear evaluation cost, and a Hoeffding
accuracy guarantee.

The guarantee is intentionally pointwise at a specified parameter pair (or can
be union-bounded over a finite grid).  Samples alone cannot certify the
source's universal quantifiers over every real accuracy parameter without
additional compactness, Lipschitz, and uniform-margin assumptions.
-/

/--
One Definition 2 observation: utility under an independent first ranking minus
utility under sharing the second mover's own ranking.
-/
def definition2SampleScore {n : ℕ} (value : Candidate n → ℝ)
    (own independentFirst : Ranking n) : ℝ :=
  value (bestRemainingAfter own (firstChoice independentFirst)) -
    value (secondChoice own)

/--
One Definition 3 observation: human utility against an independent human first
ranking minus human utility against an algorithmic first ranking.
-/
def definition3SampleScore {n : ℕ} (value : Candidate n → ℝ)
    (humanOwn humanFirst algorithmFirst : Ranking n) : ℝ :=
  value (bestRemainingAfter humanOwn (firstChoice humanFirst)) -
    value (bestRemainingAfter humanOwn (firstChoice algorithmFirst))

/--
The Definition 2 score is unbiased for the exact independent-minus-shared
payoff gap at a fixed value profile.
-/
theorem definition2SampleScore_expectation_eq_payoff_gap {n : ℕ}
    (ownLaw firstLaw : PMF (Ranking n)) (value : Candidate n → ℝ) :
    pmfPairExp ownLaw firstLaw
        (fun own independentFirst =>
          definition2SampleScore value own independentFirst) =
      expectedSecondMoverIndependent ownLaw firstLaw value -
        expectedSecondMoverShared ownLaw value := by
  unfold definition2SampleScore expectedSecondMoverIndependent
    expectedSecondMoverShared secondMoverUtility
  rw [pmfPairExp_sub]
  simp

/-- Expected Definition 3 score from the three independent ranking draws. -/
noncomputable def definition3SampleExpectation {n : ℕ}
    (humanLaw algorithmLaw : PMF (Ranking n))
    (value : Candidate n → ℝ) : ℝ :=
  pmfExp humanLaw fun humanOwn =>
    pmfPairExp humanLaw algorithmLaw fun humanFirst algorithmFirst =>
      definition3SampleScore value humanOwn humanFirst algorithmFirst

/--
The Definition 3 score is unbiased for human-against-human utility minus
human-against-algorithm utility at a fixed value profile.
-/
theorem definition3SampleExpectation_eq_payoff_gap {n : ℕ}
    (humanLaw algorithmLaw : PMF (Ranking n))
    (value : Candidate n → ℝ) :
    definition3SampleExpectation humanLaw algorithmLaw value =
      expectedSecondMoverIndependent humanLaw humanLaw value -
        expectedSecondMoverIndependent humanLaw algorithmLaw value := by
  unfold definition3SampleExpectation definition3SampleScore
    expectedSecondMoverIndependent secondMoverUtility pmfPairExp
  simp [pmfExp_sub]

/-- Definition 2 sample mean after also averaging the sampled value profile over `D`. -/
noncomputable def definition2OuterSampleMean {n : ℕ}
    (F : DistributionalAccuracyFamily n) (D : Measure (ValueProfile n))
    (theta : ℝ) : ℝ :=
  ∫ value,
    pmfPairExp (F.dist theta value) (F.dist theta value)
      (fun own independentFirst =>
        definition2SampleScore value own independentFirst) ∂D

/-- The outer Definition 2 estimator targets exactly the source's ex-ante payoff gap. -/
theorem definition2OuterSampleMean_eq_payoff_gap {n : ℕ}
    (F : DistributionalAccuracyFamily n) (D : Measure (ValueProfile n))
    (theta : ℝ)
    (hindependent : Integrable (fun value =>
      expectedSecondMoverIndependent
        (F.dist theta value) (F.dist theta value) value) D)
    (hshared : Integrable (fun value =>
      expectedSecondMoverShared (F.dist theta value) value) D) :
    definition2OuterSampleMean F D theta =
      DistributionalAccuracyFamily.outerExpected D (fun value =>
        expectedSecondMoverIndependent
          (F.dist theta value) (F.dist theta value) value) -
      DistributionalAccuracyFamily.outerExpected D (fun value =>
        expectedSecondMoverShared (F.dist theta value) value) := by
  unfold definition2OuterSampleMean DistributionalAccuracyFamily.outerExpected
  simp_rw [definition2SampleScore_expectation_eq_payoff_gap]
  exact integral_sub hindependent hshared

/-- Definition 3 sample mean after averaging the sampled value profile over `D`. -/
noncomputable def definition3OuterSampleMean {n : ℕ}
    (F : DistributionalAccuracyFamily n) (D : Measure (ValueProfile n))
    (thetaA thetaH : ℝ) : ℝ :=
  ∫ value,
    definition3SampleExpectation
      (F.dist thetaH value) (F.dist thetaA value) value ∂D

/-- The outer Definition 3 estimator targets exactly the source's ex-ante payoff gap. -/
theorem definition3OuterSampleMean_eq_payoff_gap {n : ℕ}
    (F : DistributionalAccuracyFamily n) (D : Measure (ValueProfile n))
    (thetaA thetaH : ℝ)
    (hworse : Integrable (fun value =>
      expectedSecondMoverIndependent
        (F.dist thetaH value) (F.dist thetaH value) value) D)
    (hbetter : Integrable (fun value =>
      expectedSecondMoverIndependent
        (F.dist thetaH value) (F.dist thetaA value) value) D) :
    definition3OuterSampleMean F D thetaA thetaH =
      DistributionalAccuracyFamily.outerExpected D (fun value =>
        expectedSecondMoverIndependent
          (F.dist thetaH value) (F.dist thetaH value) value) -
      DistributionalAccuracyFamily.outerExpected D (fun value =>
        expectedSecondMoverIndependent
          (F.dist thetaH value) (F.dist thetaA value) value) := by
  unfold definition3OuterSampleMean DistributionalAccuracyFamily.outerExpected
  simp_rw [definition3SampleExpectation_eq_payoff_gap]
  exact integral_sub hworse hbetter

/-- A uniform cardinal-value bound makes either source score lie in `[-2B,2B]`. -/
theorem definition2SampleScore_mem_Icc {n : ℕ}
    (value : Candidate n → ℝ) (B : ℝ)
    (hvalue : ∀ c, |value c| ≤ B) (own independentFirst : Ranking n) :
    definition2SampleScore value own independentFirst ∈ Set.Icc (-2 * B) (2 * B) := by
  have hown := hvalue (bestRemainingAfter own (firstChoice independentFirst))
  have hsecond := hvalue (secondChoice own)
  rcases abs_le.mp hown with ⟨hownLower, hownUpper⟩
  rcases abs_le.mp hsecond with ⟨hsecondLower, hsecondUpper⟩
  have hownLower' :
      -B ≤ value (bestRemainingAfter own (independentFirst 0)) := by
    simpa [firstChoice] using hownLower
  have hownUpper' :
      value (bestRemainingAfter own (independentFirst 0)) ≤ B := by
    simpa [firstChoice] using hownUpper
  have hsecondLower' : -B ≤ value (own 1) := by
    simpa [secondChoice] using hsecondLower
  have hsecondUpper' : value (own 1) ≤ B := by
    simpa [secondChoice] using hsecondUpper
  constructor <;> dsimp [definition2SampleScore] <;> linarith

/-- The same bound for a Definition 3 sample score. -/
theorem definition3SampleScore_mem_Icc {n : ℕ}
    (value : Candidate n → ℝ) (B : ℝ)
    (hvalue : ∀ c, |value c| ≤ B)
    (humanOwn humanFirst algorithmFirst : Ranking n) :
    definition3SampleScore value humanOwn humanFirst algorithmFirst ∈
      Set.Icc (-2 * B) (2 * B) := by
  have hhuman := hvalue (bestRemainingAfter humanOwn (firstChoice humanFirst))
  have halgorithm := hvalue (bestRemainingAfter humanOwn (firstChoice algorithmFirst))
  rcases abs_le.mp hhuman with ⟨hhumanLower, hhumanUpper⟩
  rcases abs_le.mp halgorithm with ⟨halgorithmLower, halgorithmUpper⟩
  have hhumanLower' :
      -B ≤ value (bestRemainingAfter humanOwn (humanFirst 0)) := by
    simpa [firstChoice] using hhumanLower
  have hhumanUpper' :
      value (bestRemainingAfter humanOwn (humanFirst 0)) ≤ B := by
    simpa [firstChoice] using hhumanUpper
  have halgorithmLower' :
      -B ≤ value (bestRemainingAfter humanOwn (algorithmFirst 0)) := by
    simpa [firstChoice] using halgorithmLower
  have halgorithmUpper' :
      value (bestRemainingAfter humanOwn (algorithmFirst 0)) ≤ B := by
    simpa [firstChoice] using halgorithmUpper
  constructor <;> dsimp [definition3SampleScore] <;>
    linarith

/-- Empirical mean of the observations indexed by a finite sample set. -/
noncomputable def empiricalMean {Omega I : Type*}
    (s : Finset I) (X : I → Omega → ℝ) (omega : Omega) : ℝ :=
  (∑ i ∈ s, X i omega) / s.card

/-- The concrete test accepts a strict source inequality exactly when the empirical mean is positive. -/
noncomputable def empiricalPositiveMarginTest {Omega I : Type*}
    (s : Finset I) (X : I → Omega → ℝ) (omega : Omega) : Prop :=
  0 < empiricalMean s X omega

/-- Each observation evaluates one constant-size score, so the score-evaluation cost is exactly linear. -/
def empiricalScoreEvaluationCost {I : Type*} (s : Finset I) : ℕ := s.card

theorem empiricalScoreEvaluationCost_eq_card {I : Type*} (s : Finset I) :
    empiricalScoreEvaluationCost s = s.card :=
  rfl

/--
Oracle-inclusive Definition 2 cost.  Each observation draws one value profile,
two independent rankings conditional on it, and evaluates one score.  The
caller supplies the implementation costs of those source sampling oracles.
-/
def definition2SimulationOracleCost {I : Type*} (s : Finset I)
    (valueDrawCost rankingDrawCost scoreCost : ℕ) : ℕ :=
  s.card * (valueDrawCost + 2 * rankingDrawCost + scoreCost)

theorem definition2SimulationOracleCost_eq {I : Type*} (s : Finset I)
    (valueDrawCost rankingDrawCost scoreCost : ℕ) :
    definition2SimulationOracleCost s valueDrawCost rankingDrawCost scoreCost =
      s.card * (valueDrawCost + 2 * rankingDrawCost + scoreCost) :=
  rfl

/--
Oracle-inclusive Definition 3 cost: one value draw, two independent human
ranking draws, one algorithmic ranking draw, and one score evaluation per
observation.
-/
def definition3SimulationOracleCost {I : Type*} (s : Finset I)
    (valueDrawCost humanDrawCost algorithmDrawCost scoreCost : ℕ) : ℕ :=
  s.card *
    (valueDrawCost + 2 * humanDrawCost + algorithmDrawCost + scoreCost)

theorem definition3SimulationOracleCost_eq {I : Type*} (s : Finset I)
    (valueDrawCost humanDrawCost algorithmDrawCost scoreCost : ℕ) :
    definition3SimulationOracleCost s valueDrawCost humanDrawCost
        algorithmDrawCost scoreCost =
      s.card *
        (valueDrawCost + 2 * humanDrawCost + algorithmDrawCost + scoreCost) :=
  rfl

/-- Deterministic margin guarantee underlying the statistical test. -/
theorem empiricalPositiveMarginTest_of_error_lt_margin
    {Omega I : Type*} (s : Finset I) (X : I → Omega → ℝ)
    (omega : Omega) (trueMean margin : ℝ)
    (hmean : margin ≤ trueMean) (hmargin : 0 < margin)
    (herror : |empiricalMean s X omega - trueMean| < margin) :
    empiricalPositiveMarginTest s X omega := by
  unfold empiricalPositiveMarginTest
  have hlower := (abs_lt.mp herror).1
  linarith

/--
Lower-tail Hoeffding inequality for independent bounded observations.  This is
the accuracy theorem used by the pointwise sign test: substitute
`epsilon = sampleCount * margin`.
-/
theorem measure_sum_expectation_sub_bounded_ge_le_exp_of_iIndepFun
    {Omega I : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {X : I → Omega → ℝ} (h_indep : iIndepFun X mu)
    {s : Finset I} {a b epsilon : ℝ}
    (h_meas : ∀ i ∈ s, AEMeasurable (X i) mu)
    (h_bound : ∀ i ∈ s, ∀ᵐ omega ∂mu, X i omega ∈ Set.Icc a b)
    (hepsilon : 0 ≤ epsilon) :
    mu.real
        {omega | epsilon ≤
          ∑ i ∈ s, ((∫ x, X i x ∂mu) - X i omega)} ≤
      Real.exp
        (-epsilon ^ 2 /
          (2 * ((∑ _ ∈ s, ((‖b - a‖₊ / 2) ^ 2 : NNReal)) : ℝ))) := by
  have hneg_indep : iIndepFun (fun i omega => -X i omega) mu :=
    h_indep.comp (fun _ x => -x) (fun _ => measurable_id.neg)
  have hneg_meas :
      ∀ i ∈ s, AEMeasurable (fun omega => -X i omega) mu := by
    intro i hi
    exact (h_meas i hi).neg
  have hneg_bound :
      ∀ i ∈ s, ∀ᵐ omega ∂mu,
        -X i omega ∈ Set.Icc (-b) (-a) := by
    intro i hi
    filter_upwards [h_bound i hi] with omega homega
    exact ⟨neg_le_neg homega.2, neg_le_neg homega.1⟩
  simpa [integral_neg, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
    (measure_sum_centered_bounded_ge_le_exp_of_iIndepFun
      mu hneg_indep (s := s) (a := -b) (b := -a)
      (ε := epsilon) hneg_meas hneg_bound hepsilon)

/--
At a source parameter where every observation has mean at least `margin`, a
nonpositive empirical sum can only occur after a downward deviation of at least
`sampleCount * margin`.
-/
theorem empirical_nonpositive_subset_lowerTail
    {Omega I : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (s : Finset I) (X : I → Omega → ℝ)
    (margin : ℝ)
    (hmean : ∀ i ∈ s, margin ≤ ∫ x, X i x ∂mu) :
    {omega | ∑ i ∈ s, X i omega ≤ 0} ⊆
      {omega | (s.card : ℝ) * margin ≤
        ∑ i ∈ s, ((∫ x, X i x ∂mu) - X i omega)} := by
  intro omega homega
  change (∑ i ∈ s, X i omega) ≤ 0 at homega
  have hsumMean :
      (s.card : ℝ) * margin ≤ ∑ i ∈ s, ∫ x, X i x ∂mu := by
    calc
      (s.card : ℝ) * margin = ∑ i ∈ s, margin := by simp [mul_comm]
      _ ≤ ∑ i ∈ s, ∫ x, X i x ∂mu :=
        Finset.sum_le_sum fun i hi => hmean i hi
  change (s.card : ℝ) * margin ≤
    ∑ i ∈ s, ((∫ x, X i x ∂mu) - X i omega)
  rw [Finset.sum_sub_distrib]
  linarith

/--
Concrete pointwise false-negative guarantee.  With `m` independent observations
in `[a,b]` and mean at least a positive `margin`, the probability that the
empirical sum has the wrong (nonpositive) sign is at most the displayed
Hoeffding exponential.  The exponent is quadratic in `m * margin` and the
score-evaluation cost is `m`.
-/
theorem empirical_nonpositive_probability_le_hoeffding
    {Omega I : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {X : I → Omega → ℝ} (h_indep : iIndepFun X mu)
    {s : Finset I} {a b margin : ℝ}
    (h_meas : ∀ i ∈ s, AEMeasurable (X i) mu)
    (h_bound : ∀ i ∈ s, ∀ᵐ omega ∂mu, X i omega ∈ Set.Icc a b)
    (hmargin : 0 < margin)
    (hmean : ∀ i ∈ s, margin ≤ ∫ x, X i x ∂mu) :
    mu.real {omega | ∑ i ∈ s, X i omega ≤ 0} ≤
      Real.exp
        (-((s.card : ℝ) * margin) ^ 2 /
          (2 * ((∑ _ ∈ s, ((‖b - a‖₊ / 2) ^ 2 : NNReal)) : ℝ))) := by
  calc
    mu.real {omega | ∑ i ∈ s, X i omega ≤ 0} ≤
        mu.real {omega | (s.card : ℝ) * margin ≤
          ∑ i ∈ s, ((∫ x, X i x ∂mu) - X i omega)} :=
      measureReal_mono
        (empirical_nonpositive_subset_lowerTail mu s X margin hmean)
        (measure_ne_top mu _)
    _ ≤ Real.exp
        (-((s.card : ℝ) * margin) ^ 2 /
          (2 * ((∑ _ ∈ s, ((‖b - a‖₊ / 2) ^ 2 : NNReal)) : ℝ))) :=
      measure_sum_expectation_sub_bounded_ge_le_exp_of_iIndepFun
        mu h_indep h_meas h_bound
          (mul_nonneg (Nat.cast_nonneg _) (le_of_lt hmargin))

end KR21Monoculture
