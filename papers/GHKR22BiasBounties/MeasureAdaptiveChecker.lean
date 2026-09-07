import GHKR22BiasBounties.MeasureCore
import GHKR22BiasBounties.AdaptiveChecker

/-!
# Adaptive certificate checking on arbitrary measurable populations

This file lifts Algorithm 2 and Theorem 11 from the executable finite-PMF
specialization to the paper's arbitrary-distribution domain.  The sample law
is Mathlib's finite iid product measure.  The only semantic prerequisites are
measurability of the bounded loss and of every submitted model and group.
-/

namespace GHKR22BiasBounties

noncomputable section

open scoped BigOperators
open MeasureTheory ProbabilityTheory
open AppliedModelingLib Probability

/-- All functions occurring in one adaptive submission are measurable. -/
def MeasureSubmissionMeasurable
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (submission : Submission X Y) : Prop :=
  MeasurableModel submission.current ∧
    MeasurableGroup submission.group ∧
    MeasurableModel submission.replacement

/-- The signed submission score is measurable under the source primitives. -/
theorem measurable_submissionScore
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {loss : BoundedLoss Y} (hloss : MeasurableBoundedLoss loss)
    {submission : Submission X Y}
    (hsubmission : MeasureSubmissionMeasurable submission) :
    Measurable (submissionScore loss submission) := by
  rcases hsubmission with ⟨hcurrent, hgroup, hreplacement⟩
  exact (measurable_groupIndicator_comp_fst hgroup).mul
    ((measurable_datumLoss hloss hcurrent).sub
      (measurable_datumLoss hloss hreplacement))

/-- The normalized `[0,1]` score is measurable. -/
theorem measurable_normalizedSubmissionScore
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {loss : BoundedLoss Y} (hloss : MeasurableBoundedLoss loss)
    {submission : Submission X Y}
    (hsubmission : MeasureSubmissionMeasurable submission) :
    Measurable (normalizedSubmissionScore loss submission) := by
  unfold normalizedSubmissionScore
  exact (measurable_submissionScore hloss hsubmission).add_const 1 |>.div_const 2

/-- The raw signed score is integrable. -/
theorem integrable_submissionScore
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) [IsProbabilityMeasure law]
    {loss : BoundedLoss Y} (hloss : MeasurableBoundedLoss loss)
    {submission : Submission X Y}
    (hsubmission : MeasureSubmissionMeasurable submission) :
    Integrable (submissionScore loss submission) law := by
  refine Integrable.of_bound
    (measurable_submissionScore hloss hsubmission).aestronglyMeasurable 1 ?_
  filter_upwards [] with datum
  rw [Real.norm_eq_abs]
  exact abs_le.2 (submissionScore_mem_Icc loss submission datum)

/-- The normalized score is integrable. -/
theorem integrable_normalizedSubmissionScore
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) [IsProbabilityMeasure law]
    {loss : BoundedLoss Y} (hloss : MeasurableBoundedLoss loss)
    {submission : Submission X Y}
    (hsubmission : MeasureSubmissionMeasurable submission) :
    Integrable (normalizedSubmissionScore loss submission) law := by
  refine Integrable.of_bound
    (measurable_normalizedSubmissionScore hloss hsubmission).aestronglyMeasurable 1 ?_
  filter_upwards [] with datum
  rw [Real.norm_eq_abs, abs_of_nonneg
    (normalizedSubmissionScore_mem_Icc loss submission datum).1]
  exact (normalizedSubmissionScore_mem_Icc loss submission datum).2

/-- The population integral of a submission is exactly its weighted
certificate-improvement score. -/
theorem integral_submissionScore_eq_measureCertificateImprovementScore
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) [IsProbabilityMeasure law]
    {loss : BoundedLoss Y} (hloss : MeasurableBoundedLoss loss)
    (submission : Submission X Y)
    (hsubmission : MeasureSubmissionMeasurable submission) :
    (∫ datum, submissionScore loss submission datum ∂law) =
      measureCertificateImprovementScore law loss submission.current
        submission.group submission.replacement := by
  rcases hsubmission with ⟨hcurrent, hgroup, hreplacement⟩
  rw [measureCertificateImprovementScore_eq_numerator_sub law hloss
    hcurrent hreplacement hgroup]
  unfold measureGroupLossNumerator
  rw [← integral_sub
    (integrable_groupWeightedDatumLoss law hloss hcurrent hgroup)
    (integrable_groupWeightedDatumLoss law hloss hreplacement hgroup)]
  apply integral_congr_ae
  filter_upwards [] with datum
  unfold submissionScore
  ring

/-- Population mean of the normalized score. -/
theorem integral_normalizedSubmissionScore
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) [IsProbabilityMeasure law]
    {loss : BoundedLoss Y} (hloss : MeasurableBoundedLoss loss)
    (submission : Submission X Y)
    (hsubmission : MeasureSubmissionMeasurable submission) :
    (∫ datum, normalizedSubmissionScore loss submission datum ∂law) =
      (measureCertificateImprovementScore law loss submission.current
        submission.group submission.replacement + 1) / 2 := by
  have hraw := integrable_submissionScore law hloss hsubmission
  unfold normalizedSubmissionScore
  rw [integral_div, integral_add hraw (integrable_const (1 : ℝ)),
    integral_submissionScore_eq_measureCertificateImprovementScore law hloss
      submission hsubmission]
  simp

/-- Uniform population/empirical accuracy for a finite adaptive query family. -/
def MeasureCheckerUniformlyAccurate
    {X Y Theta : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) (loss : BoundedLoss Y)
    (family : Theta → Submission X Y) (epsilon : ℝ) {n : ℕ}
    (sample : Fin n → X × Y) : Prop :=
  ∀ parameter,
    |empiricalSubmissionScore loss sample (family parameter) -
      measureCertificateImprovementScore law loss (family parameter).current
        (family parameter).group (family parameter).replacement| ≤ epsilon / 4

/-- Normalized empirical mean is the affine transform of the raw empirical score. -/
theorem finiteEmpiricalMean_normalizedSubmissionScore
    {X Y Theta : Type*} {n : ℕ} (hcount : 0 < n)
    (loss : BoundedLoss Y) (family : Theta → Submission X Y) (parameter : Theta)
    (sample : Fin n → X × Y) :
    finiteEmpiricalMean
        (fun (query : Theta) (index : Fin n) (outcome : Fin n → X × Y) =>
          normalizedSubmissionScore loss (family query) (outcome index))
        parameter sample =
      (empiricalSubmissionScore loss sample (family parameter) + 1) / 2 := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hcount
  have hsum :
      (∑ index : Fin n,
        normalizedSubmissionScore loss (family parameter) (sample index)) =
      ((∑ index : Fin n,
          submissionScore loss (family parameter) (sample index)) + (n : ℝ)) / 2 := by
    calc
      (∑ index : Fin n,
          normalizedSubmissionScore loss (family parameter) (sample index)) =
          ∑ index : Fin n,
            (submissionScore loss (family parameter) (sample index) + 1) / 2 := rfl
      _ = (∑ index : Fin n,
            (submissionScore loss (family parameter) (sample index) + 1)) / 2 := by
          rw [Finset.sum_div]
      _ = ((∑ index : Fin n,
            submissionScore loss (family parameter) (sample index)) + (n : ℝ)) / 2 := by
          rw [Finset.sum_add_distrib]
          simp
  unfold finiteEmpiricalMean empiricalSubmissionScore finiteIidScoreSum
  rw [hsum]
  rw [Fintype.card_fin]
  field_simp [hn]

/-- The normalized empirical/population discrepancy is half the raw one. -/
theorem normalized_measure_deviation_eq_half_raw
    {X Y Theta : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) [IsProbabilityMeasure law]
    {loss : BoundedLoss Y} (hloss : MeasurableBoundedLoss loss)
    {n : ℕ} (hcount : 0 < n) (family : Theta → Submission X Y)
    (parameter : Theta)
    (hsubmission : MeasureSubmissionMeasurable (family parameter))
    (sample : Fin n → X × Y) :
    finiteEmpiricalMean
        (fun (query : Theta) (index : Fin n) (outcome : Fin n → X × Y) =>
          normalizedSubmissionScore loss (family query) (outcome index))
        parameter sample -
        (∫ datum, normalizedSubmissionScore loss (family parameter) datum ∂law) =
      (empiricalSubmissionScore loss sample (family parameter) -
        measureCertificateImprovementScore law loss (family parameter).current
          (family parameter).group (family parameter).replacement) / 2 := by
  rw [finiteEmpiricalMean_normalizedSubmissionScore hcount loss
      family parameter,
    integral_normalizedSubmissionScore law hloss (family parameter) hsubmission]
  ring

/-- The finite-family normalized-score deviation event. -/
def measureAdaptiveCheckerDeviationEvent
    {X Y Theta : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) (loss : BoundedLoss Y)
    (family : Theta → Submission X Y) (epsilon : ℝ) {n : ℕ}
    (sample : Fin n → X × Y) : Prop :=
  ∃ parameter,
    epsilon / 8 <
      |finiteEmpiricalMean
          (fun (query : Theta) (index : Fin n) (outcome : Fin n → X × Y) =>
            normalizedSubmissionScore loss (family query) (outcome index))
          parameter sample -
        (∫ datum, normalizedSubmissionScore loss (family parameter) datum ∂law)|

/-- Probability of the arbitrary-population deviation event. -/
def measureAdaptiveCheckerDeviationFailure
    {X Y Theta : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) (loss : BoundedLoss Y)
    (family : Theta → Submission X Y) (epsilon : ℝ) (n : ℕ) : ℝ :=
  (finiteIIDSampleLaw law n).real
    {sample | measureAdaptiveCheckerDeviationEvent law loss family epsilon sample}

/-- Outside the normalized deviation event, every raw query score is accurate. -/
theorem measureCheckerUniformlyAccurate_of_not_deviationEvent
    {X Y Theta : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) [IsProbabilityMeasure law]
    {loss : BoundedLoss Y} (hloss : MeasurableBoundedLoss loss)
    (family : Theta → Submission X Y)
    (hfamily : ∀ parameter, MeasureSubmissionMeasurable (family parameter))
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    {n : ℕ} (hcount : 0 < n) (sample : Fin n → X × Y)
    (hgood : ¬ measureAdaptiveCheckerDeviationEvent law loss family epsilon sample) :
    MeasureCheckerUniformlyAccurate law loss family epsilon sample := by
  intro parameter
  have hnormalized :
      |finiteEmpiricalMean
          (fun (query : Theta) (index : Fin n) (outcome : Fin n → X × Y) =>
            normalizedSubmissionScore loss (family query) (outcome index))
          parameter sample -
        (∫ datum, normalizedSubmissionScore loss (family parameter) datum ∂law)| ≤
          epsilon / 8 := by
    by_contra hnot
    exact hgood ⟨parameter, lt_of_not_ge hnot⟩
  have hdeviation :
      finiteEmpiricalMean
          (fun (query : Theta) (index : Fin n) (outcome : Fin n → X × Y) =>
            normalizedSubmissionScore loss (family query) (outcome index))
          parameter sample -
          (∫ datum, normalizedSubmissionScore loss (family parameter) datum ∂law) =
        (empiricalSubmissionScore loss sample (family parameter) -
          measureCertificateImprovementScore law loss (family parameter).current
            (family parameter).group (family parameter).replacement) / 2 := by
    rw [finiteEmpiricalMean_normalizedSubmissionScore hcount loss family parameter,
      integral_normalizedSubmissionScore law hloss (family parameter)
        (hfamily parameter)]
    ring
  rw [hdeviation, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hnormalized
  linarith

/-- General finite-family Hoeffding bound for the checker. -/
theorem measureAdaptiveCheckerDeviationFailure_le_hoeffding
    {X Y Theta : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [Fintype Theta]
    (law : Measure (X × Y)) [IsProbabilityMeasure law]
    {loss : BoundedLoss Y} (hloss : MeasurableBoundedLoss loss)
    (family : Theta → Submission X Y)
    (hfamily : ∀ parameter, MeasureSubmissionMeasurable (family parameter))
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) (n : ℕ) (hcount : 0 < n) :
    measureAdaptiveCheckerDeviationFailure law loss family epsilon n ≤
      (Fintype.card Theta : ℝ) * 2 *
        Real.exp (-2 * (n : ℝ) * (epsilon / 8) ^ 2) := by
  let sampleLaw := finiteIIDSampleLaw law n
  let observation : Theta → Fin n → (Fin n → X × Y) → ℝ :=
    fun parameter index sample =>
      normalizedSubmissionScore loss (family parameter) (sample index)
  let mean : Theta → ℝ := fun parameter =>
    ∫ datum, normalizedSubmissionScore loss (family parameter) datum ∂law
  letI : IsProbabilityMeasure sampleLaw := by
    dsimp [sampleLaw, finiteIIDSampleLaw]
    infer_instance
  letI : Nonempty (Fin n) := ⟨⟨0, hcount⟩⟩
  have hindependent : ∀ parameter, iIndepFun (observation parameter) sampleLaw := by
    intro parameter
    simpa [observation, sampleLaw, finiteIIDSampleCoordinate, Function.comp_def] using
      (iIndepFun_finiteIIDSampleCoordinate law n).comp
        (fun _ datum => normalizedSubmissionScore loss (family parameter) datum)
        (fun _ => measurable_normalizedSubmissionScore hloss (hfamily parameter))
  have hmeasurable : ∀ parameter index, Measurable (observation parameter index) := by
    intro parameter index
    exact (measurable_normalizedSubmissionScore hloss (hfamily parameter)).comp
      (measurable_pi_apply index)
  have hbounded : ∀ parameter index, ∀ᵐ sample ∂sampleLaw,
      observation parameter index sample ∈ Set.Icc (0 : ℝ) 1 := by
    intro parameter index
    exact Filter.Eventually.of_forall fun sample =>
      normalizedSubmissionScore_mem_Icc loss (family parameter) (sample index)
  have hsameMean : ∀ parameter index,
      sampleLaw[observation parameter index] = mean parameter := by
    intro parameter index
    unfold mean observation
    calc
      (∫ sample, normalizedSubmissionScore loss (family parameter) (sample index)
          ∂sampleLaw) =
          ∫ datum, normalizedSubmissionScore loss (family parameter) datum
            ∂Measure.map (fun sample => sample index) sampleLaw := by
        symm
        apply integral_map
        · exact (measurable_pi_apply index).aemeasurable
        · exact (measurable_normalizedSubmissionScore hloss
            (hfamily parameter)).aestronglyMeasurable
      _ = ∫ datum, normalizedSubmissionScore loss (family parameter) datum ∂law := by
        change ∫ datum, normalizedSubmissionScore loss (family parameter) datum
            ∂Measure.map (finiteIIDSampleCoordinate index)
              (finiteIIDSampleLaw law n) = _
        rw [map_finiteIIDSampleCoordinate law n index]
  have htail := finite_uniform_finiteEmpiricalMean_abs_gt sampleLaw observation
    hindependent mean hsameMean hmeasurable hbounded (epsilon / 8)
    (div_nonneg hepsilon (by norm_num))
  simp only [Fintype.card_fin] at htail
  rw [boundedHoeffdingExponent_eq_neg_two_mul n hcount (epsilon / 8)] at htail
  simpa [measureAdaptiveCheckerDeviationFailure,
    measureAdaptiveCheckerDeviationEvent, sampleLaw, observation, mean] using htail

/-- The same bound in the paper's simplified exponent. -/
theorem measureAdaptiveCheckerDeviationFailure_le_explicit
    {X Y Theta : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [Fintype Theta]
    (law : Measure (X × Y)) [IsProbabilityMeasure law]
    {loss : BoundedLoss Y} (hloss : MeasurableBoundedLoss loss)
    (family : Theta → Submission X Y)
    (hfamily : ∀ parameter, MeasureSubmissionMeasurable (family parameter))
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) (n : ℕ) (hcount : 0 < n) :
    measureAdaptiveCheckerDeviationFailure law loss family epsilon n ≤
      (Fintype.card Theta : ℝ) * 2 *
        Real.exp (-(n : ℝ) * epsilon ^ 2 / 32) := by
  convert measureAdaptiveCheckerDeviationFailure_le_hoeffding law hloss family
    hfamily epsilon hepsilon n hcount using 1 <;> ring

/-- Source conclusions for one checker decision under an arbitrary population. -/
def MeasureCheckerDecisionGuaranteed
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) (loss : BoundedLoss Y) (epsilon : ℝ)
    (submission : Submission X Y) (decision : CertificateDecision) : Prop :=
  (decision = .rejected →
    ∀ mu Delta, epsilon ≤ mu * Delta →
      ¬ MeasureCertificateOfSuboptimality law loss submission.current
        submission.group submission.replacement mu Delta) ∧
  (decision = .accepted →
    ∃ mu Delta,
      MeasureCertificateOfSuboptimality law loss submission.current
        submission.group submission.replacement mu Delta ∧
      epsilon / 2 ≤ mu * Delta)

/-- Rejection soundness on the general population. -/
theorem measureCertificateChecker_rejected_sound
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {law : Measure (X × Y)} {loss : BoundedLoss Y}
    {epsilon : ℝ} {n : ℕ} {sample : Fin n → X × Y}
    {submission : Submission X Y}
    (haccurate :
      |empiricalSubmissionScore loss sample submission -
        measureCertificateImprovementScore law loss submission.current
          submission.group submission.replacement| ≤ epsilon / 4)
    (hdecision : certificateCheckerDecision epsilon loss sample submission = .rejected) :
    ∀ mu Delta, epsilon ≤ mu * Delta →
      ¬ MeasureCertificateOfSuboptimality law loss submission.current
        submission.group submission.replacement mu Delta := by
  intro mu Delta hlarge hcert
  have hempirical :=
    (certificateCheckerDecision_eq_rejected_iff epsilon loss sample submission).mp hdecision
  have hpopulation :
      measureCertificateImprovementScore law loss submission.current
        submission.group submission.replacement < epsilon := by
    rcases abs_le.mp haccurate with ⟨hlower, hupper⟩
    linarith
  have hcertScore := measureCertificate_mul_le_improvementScore hcert
  linarith

/-- Acceptance completeness on the general population. -/
theorem measureCertificateChecker_accepted_complete
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {law : Measure (X × Y)} [IsProbabilityMeasure law]
    {loss : BoundedLoss Y} {epsilon : ℝ} (hepsilon : 0 < epsilon)
    {n : ℕ} {sample : Fin n → X × Y} {submission : Submission X Y}
    (hsubmission : MeasureSubmissionMeasurable submission)
    (haccurate :
      |empiricalSubmissionScore loss sample submission -
        measureCertificateImprovementScore law loss submission.current
          submission.group submission.replacement| ≤ epsilon / 4)
    (hdecision : certificateCheckerDecision epsilon loss sample submission = .accepted) :
    ∃ mu Delta,
      MeasureCertificateOfSuboptimality law loss submission.current
        submission.group submission.replacement mu Delta ∧
      epsilon / 2 ≤ mu * Delta := by
  have hempirical :=
    (certificateCheckerDecision_eq_accepted_iff epsilon loss sample submission).mp hdecision
  have hpopulation : epsilon / 2 ≤
      measureCertificateImprovementScore law loss submission.current
        submission.group submission.replacement := by
    rcases abs_le.mp haccurate with ⟨hlower, hupper⟩
    linarith
  have hpositive : 0 < measureCertificateImprovementScore law loss submission.current
      submission.group submission.replacement :=
    lt_of_lt_of_le (half_pos hepsilon) hpopulation
  refine ⟨measureGroupMass law submission.group,
    measureGroupLoss law loss submission.current submission.group -
      measureGroupLoss law loss submission.replacement submission.group,
    measureCanonical_certificate_of_positive_score law hsubmission.2.1 hpositive, ?_⟩
  simpa [measureCertificateImprovementScore] using hpopulation

/-- Every query actually issued by Algorithm 2 has the source decision semantics. -/
def MeasureCheckerRunAuxGuaranteed
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) (loss : BoundedLoss Y) (epsilon : ℝ)
    {n : ℕ} (sample : Fin n → X × Y)
    (strategy : AdaptiveSubmissionStrategy X Y) :
    ℕ → List CertificateDecision → Prop
  | 0, _ => True
  | remaining + 1, reverseTranscript =>
      if (numberAccepted reverseTranscript : ℝ) ≤ 2 / epsilon then
        let publicTranscript := reverseTranscript.reverse
        let submission := strategy publicTranscript
        let decision := certificateCheckerDecision epsilon loss sample submission
        MeasureCheckerDecisionGuaranteed law loss epsilon submission decision ∧
          MeasureCheckerRunAuxGuaranteed law loss epsilon sample strategy remaining
            (decision :: reverseTranscript)
      else True

/-- Sparse-family accuracy gives the source semantics at every issued query. -/
theorem measureCheckerRunAuxGuaranteed_of_sparseFamilyAccuracy
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) [IsProbabilityMeasure law]
    {loss : BoundedLoss Y} (hloss : MeasurableBoundedLoss loss)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    {n : ℕ} (sample : Fin n → X × Y) (U : ℕ)
    (strategy : AdaptiveSubmissionStrategy X Y)
    (hstrategy : ∀ transcript, MeasureSubmissionMeasurable (strategy transcript))
    (haccurate : MeasureCheckerUniformlyAccurate law loss
      (sparseStrategyFamily U (checkerAcceptanceBudget epsilon) strategy)
      epsilon sample) :
    ∀ (remaining : ℕ) (reverseTranscript : List CertificateDecision),
      reverseTranscript.length + remaining ≤ U →
      MeasureCheckerRunAuxGuaranteed law loss epsilon sample strategy
        remaining reverseTranscript := by
  intro remaining
  induction remaining with
  | zero => intro reverseTranscript _; trivial
  | succ remaining ih =>
      intro reverseTranscript hlength
      simp only [MeasureCheckerRunAuxGuaranteed]
      split
      · rename_i hguard
        let publicTranscript := reverseTranscript.reverse
        let submission := strategy publicTranscript
        let decision := certificateCheckerDecision epsilon loss sample submission
        have hpublicLength : publicTranscript.length < U := by
          dsimp [publicTranscript]
          simp only [List.length_reverse]
          omega
        have hpublicCount :
            numberAccepted publicTranscript ≤ checkerAcceptanceBudget epsilon := by
          dsimp [publicTranscript]
          rw [numberAccepted_reverse]
          exact numberAccepted_le_checkerAcceptanceBudget epsilon reverseTranscript hguard
        rcases strategy_submission_mem_sparseFamily U
          (checkerAcceptanceBudget epsilon) strategy publicTranscript
          hpublicLength hpublicCount with ⟨query, hquery⟩
        have hqueryAccurate := haccurate query
        have hsubmission : MeasureSubmissionMeasurable submission := hstrategy publicTranscript
        simp only [sparseStrategyFamily, submission] at hquery ⊢
        have hqueryEq : sparseStrategyFamily U (checkerAcceptanceBudget epsilon)
            strategy query = submission := by simpa [submission] using hquery
        constructor
        · constructor
          · intro hdecision mu Delta hlarge
            exact measureCertificateChecker_rejected_sound
              (by simpa [hqueryEq] using hqueryAccurate) hdecision mu Delta hlarge
          · intro hdecision
            exact measureCertificateChecker_accepted_complete hepsilon hsubmission
              (by simpa [hqueryEq] using hqueryAccurate) hdecision
        · apply ih
          simp only [List.length_cons]
          omega
      · trivial

/-- Probability that the literal general-population Algorithm 2 run violates
one of its decision guarantees. -/
def measureCertificateCheckerRunGuaranteeFailure
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) (loss : BoundedLoss Y)
    (epsilon : ℝ) (n U : ℕ) (strategy : AdaptiveSubmissionStrategy X Y) : ℝ :=
  (finiteIIDSampleLaw law n).real {sample |
    ¬ MeasureCheckerRunAuxGuaranteed law loss epsilon sample strategy U []}

/-- Corrected Theorem 11 on an arbitrary measurable population. -/
theorem theorem11_measure_adaptive_certificateCheckerRun
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) [IsProbabilityMeasure law]
    {loss : BoundedLoss Y} (hloss : MeasurableBoundedLoss loss)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (n U : ℕ) (hcount : 0 < n)
    (strategy : AdaptiveSubmissionStrategy X Y)
    (hstrategy : ∀ transcript, MeasureSubmissionMeasurable (strategy transcript)) :
    measureCertificateCheckerRunGuaranteeFailure law loss epsilon n U strategy ≤
      (U * (U + 1) ^ checkerAcceptanceBudget epsilon : ℕ) * 2 *
        Real.exp (-(n : ℝ) * epsilon ^ 2 / 32) := by
  let family := sparseStrategyFamily U (checkerAcceptanceBudget epsilon) strategy
  letI : IsProbabilityMeasure (finiteIIDSampleLaw law n) := by
    dsimp [finiteIIDSampleLaw]
    infer_instance
  have hfamily : ∀ query, MeasureSubmissionMeasurable (family query) := by
    intro query
    exact hstrategy _
  calc
    measureCertificateCheckerRunGuaranteeFailure law loss epsilon n U strategy ≤
        measureAdaptiveCheckerDeviationFailure law loss family epsilon n := by
      refine measureReal_mono ?_ (measure_ne_top (finiteIIDSampleLaw law n) _)
      intro sample hbad
      by_contra hdeviation
      apply hbad
      exact measureCheckerRunAuxGuaranteed_of_sparseFamilyAccuracy law hloss epsilon
        hepsilon sample U strategy hstrategy
        (measureCheckerUniformlyAccurate_of_not_deviationEvent law hloss family
          hfamily epsilon hepsilon.le hcount sample hdeviation) U [] (by simp)
    _ ≤ (Fintype.card
          (AdaptiveQueryIndex U (checkerAcceptanceBudget epsilon)) : ℝ) * 2 *
          Real.exp (-(n : ℝ) * epsilon ^ 2 / 32) :=
      measureAdaptiveCheckerDeviationFailure_le_explicit law hloss family hfamily
        epsilon hepsilon.le n hcount
    _ = (U * (U + 1) ^ checkerAcceptanceBudget epsilon : ℕ) * 2 *
          Real.exp (-(n : ℝ) * epsilon ^ 2 / 32) := by
      rw [card_adaptiveQueryIndex]

/-- Remark 13 on an arbitrary measurable population. -/
theorem remark13_measure_sparse_adaptive_failure_bound
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (law : Measure (X × Y)) [IsProbabilityMeasure law]
    {loss : BoundedLoss Y} (hloss : MeasurableBoundedLoss loss)
    (U K : ℕ) (family : AdaptiveQueryIndex U K → Submission X Y)
    (hfamily : ∀ query, MeasureSubmissionMeasurable (family query))
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) (n : ℕ) (hcount : 0 < n) :
    measureAdaptiveCheckerDeviationFailure law loss family epsilon n ≤
      (U * (U + 1) ^ K : ℕ) * 2 *
        Real.exp (-(n : ℝ) * epsilon ^ 2 / 32) := by
  simpa [card_adaptiveQueryIndex] using
    (measureAdaptiveCheckerDeviationFailure_le_explicit law hloss family hfamily
      epsilon hepsilon n hcount)

end

end GHKR22BiasBounties
