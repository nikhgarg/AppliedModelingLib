import LBG24SpatialUnderreporting.KernelCausalResponseLaw

/-!
# Single-endpoint traces for causal LBG observation policies

Appendix Theorem 2 has one realized endpoint `E`, even when an agency updates
its prospective response after receiving another report.  This file gives the
canonical finite branch construction for that reading.  A policy supplies a
rate-free endpoint-response kernel at each *live* report prefix.  The internal
response draws are auxiliary policy randomization; after restricting to a
branch with `count` reports, the observable output has one absolute endpoint
time.

This is a source-model construction, not a derivation of an arbitrary endpoint
law from the printed Conditions 1--2 alone.  The source's prose says that endpoints depend on
reports only through information available up to their times
(`source.txt:254-258`, `1574-1579`) and later calls this a stopping-times
assumption (`source.txt:2086-2110`).  A source-carrier bridge still has to
establish the corresponding conditional transition law.  In particular, this
module does not turn the marginal Condition-2 density into that law.
-/

namespace LBG24SpatialUnderreporting

open MeasureTheory ProbabilityTheory
open AppliedModelingLib.Probability
open AppliedModelingLib.Probability.PoissonProcess
open scoped BigOperators ENNReal NNReal ProbabilityTheory

noncomputable section

namespace CollapsedFiniteStageEndpointKernelModel

variable {count : ℕ}

/-- Elapsed report time after a finite post-start gap block. -/
def elapsedTime (gaps : Fin count -> ℝ) : ℝ :=
  ∑ i : Fin count, gaps i

theorem measurable_elapsedTime :
    Measurable (elapsedTime (count := count)) := by
  unfold elapsedTime
  exact Finset.measurable_sum Finset.univ fun i _ => measurable_pi_apply i

/-- Forget the unobserved policy draws and retain the displayed report gaps
and the terminal remaining endpoint time. -/
def terminalEndpointCoordinate :
    ((Fin count -> ℝ) × ((Fin count -> ℝ) × (ℝ × ℝ))) ->
      ((Fin count -> ℝ) × ℝ) :=
  fun p => (p.1, p.2.2.1)

theorem measurable_terminalEndpointCoordinate :
    Measurable (terminalEndpointCoordinate (count := count)) := by
  exact measurable_fst.prodMk (by fun_prop)

/-- Convert a terminal remaining endpoint time into the one absolute endpoint
time measured from the selected start. -/
def absoluteEndpointTransform :
    ((Fin count -> ℝ) × ℝ) -> ((Fin count -> ℝ) × ℝ) :=
  fun p => (p.1, elapsedTime p.1 + p.2)

theorem measurable_absoluteEndpointTransform :
    Measurable (absoluteEndpointTransform (count := count)) := by
  exact measurable_fst.prodMk
    ((measurable_elapsedTime.comp measurable_fst).add measurable_snd)

/-- The branch's actual endpoint observation: one scalar endpoint time,
rather than the vector of provisional clocks used to implement the causal
policy. -/
def singleEndpointTraceFromLatent :
    ((Fin count -> ℝ) × ((Fin count -> ℝ) × (ℝ × ℝ))) ->
      ((Fin count -> ℝ) × ℝ) :=
  absoluteEndpointTransform ∘ terminalEndpointCoordinate

theorem measurable_singleEndpointTraceFromLatent :
    Measurable (singleEndpointTraceFromLatent (count := count)) :=
  measurable_absoluteEndpointTransform.comp measurable_terminalEndpointCoordinate

theorem singleEndpointTraceFromLatent_apply
    (p : (Fin count -> ℝ) × ((Fin count -> ℝ) × (ℝ × ℝ))) :
    singleEndpointTraceFromLatent p =
      (p.1, elapsedTime p.1 + p.2.2.1) := rfl

/-- Canonical finite latent law for a causal endpoint policy.  It is a
construction from the transition kernels, not a premise about an archived
source carrier. -/
def canonicalLatentLaw (M : CollapsedFiniteStageEndpointKernelModel count)
    (rate : ℝ) :
    Measure ((Fin count -> ℝ) × ((Fin count -> ℝ) × (ℝ × ℝ))) :=
  CollapsedFiniteStageEndpointModel.iidGapLaw count rate ⊗ₘ M.responseKernel rate

/-- The fixed-count branch law in relative endpoint coordinates. -/
def canonicalRelativeEndpointLaw
    (M : CollapsedFiniteStageEndpointKernelModel count) (rate : ℝ) :
    Measure ((Fin count -> ℝ) × ℝ) :=
  M.startWeight •
    Measure.map terminalEndpointCoordinate
      ((M.canonicalLatentLaw rate).restrict
        (acceptedGapResponseSet (count := count)))

/-- The fixed-count branch law carrying one absolute endpoint coordinate. -/
def canonicalSingleEndpointTraceLaw
    (M : CollapsedFiniteStageEndpointKernelModel count) (rate : ℝ) :
    Measure ((Fin count -> ℝ) × ℝ) :=
  M.startWeight •
    Measure.map singleEndpointTraceFromLatent
      ((M.canonicalLatentLaw rate).restrict
        (acceptedGapResponseSet (count := count)))

/-- The canonical relative-coordinate branch law is exactly the atom-safe
collapsed observation law.  This is a kernel construction theorem and does
not assume a mutually independent family of clocks on a source carrier. -/
theorem canonicalRelativeEndpointLaw_eq_collapsedObservationLaw
    (M : CollapsedFiniteStageEndpointKernelModel count)
    {rate : ℝ} (rate_pos : 0 < rate) :
    M.canonicalRelativeEndpointLaw rate = M.collapsedObservationLaw rate := by
  letI : IsProbabilityMeasure (expMeasure rate) :=
    isProbabilityMeasure_expMeasure rate_pos
  letI : ∀ _ : Fin count, IsProbabilityMeasure (expMeasure rate) :=
    fun _ => isProbabilityMeasure_expMeasure rate_pos
  letI : IsProbabilityMeasure
      (CollapsedFiniteStageEndpointModel.iidGapLaw count rate) := by
    unfold CollapsedFiniteStageEndpointModel.iidGapLaw
    infer_instance
  unfold canonicalRelativeEndpointLaw canonicalLatentLaw
  change M.startWeight •
      Measure.map
        (fun p : (Fin count -> ℝ) × ((Fin count -> ℝ) × (ℝ × ℝ)) =>
          (p.1, p.2.2.1))
        ((CollapsedFiniteStageEndpointModel.iidGapLaw count rate ⊗ₘ M.responseKernel rate).restrict
          (acceptedGapResponseSet (count := count))) =
      M.collapsedObservationLaw rate
  rw [M.map_restrict_responseLaw_eq_compProd_acceptedTail
    (CollapsedFiniteStageEndpointModel.iidGapLaw count rate) rate_pos]
  exact M.generatedObservationLaw_eq_collapsedObservationLaw rate_pos

/-- The same canonical construction has one coherent absolute endpoint on the
observed branch.  The proof integrates out provisional response draws before
the endpoint is exposed; no claim equates counterfactual stage clocks with the
single realized endpoint. -/
theorem canonicalSingleEndpointTraceLaw_eq_map_collapsedObservationLaw
    (M : CollapsedFiniteStageEndpointKernelModel count)
    {rate : ℝ} (rate_pos : 0 < rate) :
    M.canonicalSingleEndpointTraceLaw rate =
      Measure.map absoluteEndpointTransform (M.collapsedObservationLaw rate) := by
  calc
    M.canonicalSingleEndpointTraceLaw rate =
        Measure.map absoluteEndpointTransform
          (M.canonicalRelativeEndpointLaw rate) := by
      unfold canonicalSingleEndpointTraceLaw canonicalRelativeEndpointLaw
        canonicalLatentLaw
      rw [Measure.map_smul]
      rw [Measure.map_map measurable_absoluteEndpointTransform
        measurable_terminalEndpointCoordinate]
      rfl
    _ = Measure.map absoluteEndpointTransform (M.collapsedObservationLaw rate) := by
      rw [M.canonicalRelativeEndpointLaw_eq_collapsedObservationLaw rate_pos]

end CollapsedFiniteStageEndpointKernelModel

/-!
### Count-dependent competing clocks

The paper's simulator is a concrete source-supported instance of the causal
reading: after each report it races a new report clock against a death clock
whose rate may depend on the number of reports already received
(`source.txt:1897-1904`).  The following construction has one realized death
endpoint on every accepted finite branch.  The independently generated clock
coordinates are implementation noise for that sequential policy, not a claim
that the archived Conditions 1--2 imply a product law on an existing carrier.
-/

namespace CountDependentCompetingClock

variable {count : ℕ}

/-- The rate-free death-clock kernel after a visible report prefix. -/
noncomputable def endpointKernel
    (deathRate : Fin (count + 1) -> ℝ) (j : Fin (count + 1)) :
    Kernel (Fin j.1 -> ℝ) ℝ :=
  Kernel.const (Fin j.1 -> ℝ) (expMeasure (deathRate j))

theorem endpointKernel_isMarkov
    (deathRate : Fin (count + 1) -> ℝ)
    (deathRate_pos : ∀ j, 0 < deathRate j)
    (j : Fin (count + 1)) :
    IsMarkovKernel (endpointKernel deathRate j) := by
  letI : IsProbabilityMeasure (expMeasure (deathRate j)) :=
    isProbabilityMeasure_expMeasure (deathRate_pos j)
  unfold endpointKernel
  infer_instance

theorem endpointKernel_nonnegative_support
    (deathRate : Fin (count + 1) -> ℝ)
    (deathRate_pos : ∀ j, 0 < deathRate j)
    (j : Fin (count + 1)) (history : Fin j.1 -> ℝ) :
    endpointKernel deathRate j history (Set.Iio (0 : ℝ)) = 0 := by
  let D : AppliedModelingLib.Probability.Exponential.Model :=
    ⟨deathRate j, deathRate_pos j⟩
  change D.measure (Set.Iio (0 : ℝ)) = 0
  exact D.measure_Iio_zero

/-- A count-dependent competing-clock policy.  Its endpoint-response rule is
independent of the reporting rate; only the exponential report-gap law below
will contain that rate. -/
noncomputable def model
    (deathRate : Fin (count + 1) -> ℝ)
    (deathRate_pos : ∀ j, 0 < deathRate j)
    (startWeight : ℝ≥0∞) :
    CollapsedFiniteStageEndpointKernelModel count where
  startWeight := startWeight
  endKernel := endpointKernel deathRate
  endKernel_isMarkov := endpointKernel_isMarkov deathRate deathRate_pos
  endKernel_nonnegative_support :=
    endpointKernel_nonnegative_support deathRate deathRate_pos
  stageSurvival_measurable := by
    intro i
    letI : IsProbabilityMeasure (expMeasure (deathRate i.castSucc)) :=
      isProbabilityMeasure_expMeasure (deathRate_pos i.castSucc)
    simpa [endpointKernel, Kernel.const_apply] using
      ((measurable_measure_Ioi (expMeasure (deathRate i.castSucc))).comp
        (measurable_pi_apply i))

/-- The source simulator's fixed-count branch has one absolute death endpoint
after the final observed report. -/
def absoluteDeathEndpoint
    (p : (Fin count -> ℝ) × ((Fin count -> ℝ) × (ℝ × ℝ))) : ℝ :=
  CollapsedFiniteStageEndpointKernelModel.elapsedTime p.1 + p.2.2.1

theorem absoluteDeathEndpoint_eq_trace_endpoint
    (p : (Fin count -> ℝ) × ((Fin count -> ℝ) × (ℝ × ℝ))) :
    absoluteDeathEndpoint p =
      (CollapsedFiniteStageEndpointKernelModel.singleEndpointTraceFromLatent p).2 := rfl

/-- On an accepted branch each displayed report beats its current death clock
and the one terminal death endpoint beats the next report clock. -/
theorem accepted_branch_race_order
    (p : (Fin count -> ℝ) × ((Fin count -> ℝ) × (ℝ × ℝ)))
    (hp : p ∈ CollapsedFiniteStageEndpointKernelModel.acceptedGapResponseSet
      (count := count)) :
    (∀ i, p.1 i < p.2.1 i) ∧ p.2.2.1 < p.2.2.2 := by
  exact hp

/-- The canonical competing-clock branch law has a single absolute endpoint
coordinate and agrees with the atom-safe causal observation law after the
coordinate change. -/
theorem singleEndpointTraceLaw_eq_map_collapsedObservationLaw
    (deathRate : Fin (count + 1) -> ℝ)
    (deathRate_pos : ∀ j, 0 < deathRate j)
    (startWeight : ℝ≥0∞) {reportRate : ℝ} (reportRate_pos : 0 < reportRate) :
    (model deathRate deathRate_pos startWeight).canonicalSingleEndpointTraceLaw
        reportRate =
      Measure.map CollapsedFiniteStageEndpointKernelModel.absoluteEndpointTransform
        ((model deathRate deathRate_pos startWeight).collapsedObservationLaw
          reportRate) := by
  exact
    CollapsedFiniteStageEndpointKernelModel.canonicalSingleEndpointTraceLaw_eq_map_collapsedObservationLaw
      (model deathRate deathRate_pos startWeight) reportRate_pos

end CountDependentCompetingClock

end

end LBG24SpatialUnderreporting
