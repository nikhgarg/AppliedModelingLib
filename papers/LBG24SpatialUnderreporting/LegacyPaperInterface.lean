import LBG24SpatialUnderreporting.MainTheorems
import LBG24SpatialUnderreporting.Assumptions
import LBG24SpatialUnderreporting.CanonicalSelectedStart
import LBG24SpatialUnderreporting.CorrectedTheorem2Causal
import LBG24SpatialUnderreporting.CollapsedCausalObservationLaw
import LBG24SpatialUnderreporting.StationaryPalmCausalObservationLaw
import LBG24SpatialUnderreporting.KernelCausalEndpointBridge
import LBG24SpatialUnderreporting.BirthCohortFiniteHorizonBridge
import LBG24SpatialUnderreporting.DeterministicCapPalmBridge
import LBG24SpatialUnderreporting.CausalStoppingEndpointTrace
import LBG24SpatialUnderreporting.SourceTheoremModels
import LBG24SpatialUnderreporting.ObservationEndpointFormulas

/-!
# Audited Review Surface: Quantifying Spatial Under-reporting Disparities

This file is the compact Lean surface for the formalized theorem core of Liu,
Bhandaram, and Garg 2024.  It exposes the source formulas and named theoretical
claims represented in Lean, including the corrected causal reading of the
Appendix-Theorem-2 likelihood factorization.
-/

namespace LBG24SpatialUnderreporting

open Filter
open MeasureTheory
open AppliedModelingLib.Probability.PoissonProcess
open scoped Function ProbabilityTheory Topology NNReal

noncomputable section

universe u

local notation "durationMeasure" => volume.restrict (Set.Ici (0 : ℝ))

/-! ## Source Formulas -/

/--
Source-anchored observed-window representation convention: after conditioning
on reports before the selected start, the retained interval data are encoded as
exactly a zero-, one-, or multi-report window.  The one- and multi-report
branches carry ordered report-time data in `(s,e]`, not only a count.

Source status: shared source-model convention for source.txt:205-220;254-291.
This theorem exposes the encoding's exhaustive shape only; it does not
construct source variables `S`, `E`, or the conditioning history `H`.
-/
theorem theorem2_observed_window_data_definition
    (C : Theorem2ObservedWindowCase) :
    (∃ baseCount W,
      C = Theorem2ObservedWindowCase.zero baseCount W) ∨
    (∃ baseCount T h_exposure,
      C = Theorem2ObservedWindowCase.one baseCount T h_exposure) ∨
    (∃ baseCount T hcount h_exposure,
      C = Theorem2ObservedWindowCase.multi baseCount T hcount h_exposure) := by
  cases C with
  | zero baseCount W =>
      exact Or.inl ⟨baseCount, W, rfl⟩
  | one baseCount T h_exposure =>
      exact Or.inr <| Or.inl ⟨baseCount, T, h_exposure, rfl⟩
  | multi baseCount T hcount h_exposure =>
      exact Or.inr <| Or.inr ⟨baseCount, T, hcount, h_exposure, rfl⟩

/--
Poisson mean parameter used by the paper's count PMF.
Source status: Paper notation wrapper for Eq. (2); reviewed as auxiliary.
-/
abbrev poisson_count_mean (rate exposure : ℝ) : ℝ :=
  rate * exposure

/-- Eq. (2): the Poisson count probability mass used throughout the paper.
Source status: Lean-checked paper-facing row.
-/
theorem equation2_poisson_count_pmf_formula
    (rate exposure : ℝ) (count : ℕ) :
    sourcePoissonPMF rate exposure count =
      Real.exp (-(rate * exposure)) * (rate * exposure) ^ count /
        (count.factorial : ℝ) := by
  exact sourcePoissonPMF_eq_formula rate exposure count

/-- Homogeneous probability that an active incident receives at least one report.
Source status: Lean-checked paper-facing proof row for the fixed-duration conditional probability.
-/
theorem first_report_probability_formula
    (reportingRate duration : ℝ) :
    firstReportProbability reportingRate duration =
      1 - Real.exp (-(reportingRate * duration)) := by
  exact firstReportProbability_eq_one_sub_noReport reportingRate duration

/-- Lemma 1 continuous-duration homogeneous integral formula.
Source status: Lean-checked paper-facing row.
-/
theorem lemma1_continuous_duration_first_report_probability_integral
    (reportingRate : ℝ) (durationDensity : ℝ → ℝ)
    (h_density_mass : (∫ t, durationDensity t ∂durationMeasure) = 1)
    (h_density_integrable :
      Integrable durationDensity durationMeasure)
    (h_noReport_integrable :
      Integrable
        (fun t => durationDensity t * noArrivalProb reportingRate t)
        durationMeasure) :
    continuousDurationFirstReportProbability
        reportingRate durationDensity =
      ∫ t, durationDensity t * firstReportProbability reportingRate t
        ∂durationMeasure := by
  exact continuousDurationFirstReportProbability_eq_integral_firstReportProbability
    reportingRate durationDensity h_density_mass h_density_integrable
    h_noReport_integrable

/-- Lemma 1 continuous-duration observed unique-incident rate formula.
Source status: Lean-checked paper-facing row.
-/
theorem lemma1_continuous_duration_observed_rate_integral
    (incidentRate reportingRate : ℝ) (durationDensity : ℝ → ℝ)
    (h_density_mass : (∫ t, durationDensity t ∂durationMeasure) = 1)
    (h_density_integrable : Integrable durationDensity durationMeasure)
    (h_noReport_integrable :
      Integrable
        (fun t => durationDensity t * noArrivalProb reportingRate t) durationMeasure) :
    continuousDurationObservedIncidentRate
        incidentRate reportingRate durationDensity =
      incidentRate *
        ∫ t, durationDensity t * firstReportProbability reportingRate t
          ∂durationMeasure := by
  exact continuousDurationObservedIncidentRate_eq_integral_firstReportProbability
    incidentRate reportingRate durationDensity h_density_mass
    h_density_integrable h_noReport_integrable

/--
Lemma 1 nonhomogeneous continuous-duration first-report probability formula
through a cumulative reporting intensity.
-/
theorem
    lemma1_continuous_duration_cumulative_intensity_first_report_probability_integral
    (cumulativeIntensity durationDensity : ℝ → ℝ)
    (h_density_mass : (∫ t, durationDensity t ∂durationMeasure) = 1)
    (h_density_integrable : Integrable durationDensity durationMeasure)
    (h_noReport_integrable :
      Integrable
        (fun t => durationDensity t * Real.exp (-(cumulativeIntensity t)))
        durationMeasure) :
    continuousDurationFirstReportProbabilityOfCumulativeIntensity
        cumulativeIntensity durationDensity =
      ∫ t,
        durationDensity t *
          cumulativeIntensityFirstReportProbability cumulativeIntensity t
        ∂durationMeasure := by
  exact continuousDurationFirstReportProbabilityOfCumulativeIntensity_eq_integral
    cumulativeIntensity durationDensity h_density_mass h_density_integrable
    h_noReport_integrable

/--
Lemma 1 nonhomogeneous first-report formula in the source's literal notation,
with cumulative intensity `\int_0^t reportingRate(u) du`.
Source status: Lean-checked paper-facing row.
-/
theorem lemma1_nonhomogeneous_first_report_probability_integral
    (reportingRate durationDensity : ℝ → ℝ)
    (h_density_mass : (∫ t, durationDensity t ∂durationMeasure) = 1)
    (h_density_integrable : Integrable durationDensity durationMeasure)
    (h_noReport_integrable :
      Integrable
        (fun t => durationDensity t *
          Real.exp (-(∫ u in (0 : ℝ)..t, reportingRate u)))
        durationMeasure) :
    continuousDurationFirstReportProbabilityOfCumulativeIntensity
        (fun t => ∫ u in (0 : ℝ)..t, reportingRate u) durationDensity =
      ∫ t,
        durationDensity t *
          (1 - Real.exp (-(∫ u in (0 : ℝ)..t, reportingRate u)))
        ∂durationMeasure := by
  simpa [cumulativeIntensityFirstReportProbability] using
    lemma1_continuous_duration_cumulative_intensity_first_report_probability_integral
      (fun t => ∫ u in (0 : ℝ)..t, reportingRate u) durationDensity
      h_density_mass h_density_integrable h_noReport_integrable

/--
Lemma 1 nonhomogeneous continuous-duration observed unique-incident rate
formula through a cumulative reporting intensity.
Source status: Lean-checked paper-facing row.
-/
theorem lemma1_continuous_duration_cumulative_intensity_observed_rate_integral
    (incidentRate : ℝ) (cumulativeIntensity durationDensity : ℝ → ℝ)
    (h_density_mass : (∫ t, durationDensity t ∂durationMeasure) = 1)
    (h_density_integrable : Integrable durationDensity durationMeasure)
    (h_noReport_integrable :
      Integrable
        (fun t => durationDensity t * Real.exp (-(cumulativeIntensity t)))
        durationMeasure) :
    continuousDurationObservedIncidentRateOfCumulativeIntensity
        incidentRate cumulativeIntensity durationDensity =
      incidentRate *
        ∫ t,
          durationDensity t *
            cumulativeIntensityFirstReportProbability cumulativeIntensity t
          ∂durationMeasure := by
  exact continuousDurationObservedIncidentRateOfCumulativeIntensity_eq_integral
    incidentRate cumulativeIntensity durationDensity h_density_mass
    h_density_integrable h_noReport_integrable

/--
Lemma 1 nonhomogeneous observed-incident rate in the source's literal
cumulative-intensity notation.
Source status: Lean-checked paper-facing row.
-/
theorem lemma1_nonhomogeneous_observed_rate_integral
    (incidentRate : ℝ) (reportingRate durationDensity : ℝ → ℝ)
    (h_density_mass : (∫ t, durationDensity t ∂durationMeasure) = 1)
    (h_density_integrable : Integrable durationDensity durationMeasure)
    (h_noReport_integrable :
      Integrable
        (fun t => durationDensity t *
          Real.exp (-(∫ u in (0 : ℝ)..t, reportingRate u)))
        durationMeasure) :
    continuousDurationObservedIncidentRateOfCumulativeIntensity
        incidentRate (fun t => ∫ u in (0 : ℝ)..t, reportingRate u)
        durationDensity =
      incidentRate *
        ∫ t,
          durationDensity t *
            (1 - Real.exp (-(∫ u in (0 : ℝ)..t, reportingRate u)))
          ∂durationMeasure := by
  simpa [cumulativeIntensityFirstReportProbability] using
    lemma1_continuous_duration_cumulative_intensity_observed_rate_integral
      incidentRate (fun t => ∫ u in (0 : ℝ)..t, reportingRate u)
      durationDensity h_density_mass h_density_integrable
      h_noReport_integrable

/--
Lemma 1 finite-duration mixture form: normalized duration weights turn the
finite-duration first-report probability into the weighted average of
per-duration first-report probabilities.
Source status: Lean-checked paper-facing row.
-/
theorem lemma1_finite_duration_first_report_weighted_average
    {DurationType : Type*} [Fintype DurationType]
    (reportingRate : ℝ) (weight duration : DurationType → ℝ)
    (hsum_weight : (∑ d, weight d) = 1) :
    finiteDurationFirstReportProbability reportingRate weight duration =
      ∑ d, weight d * firstReportProbability reportingRate (duration d) := by
  exact
    finiteDurationFirstReportProbability_eq_weighted_firstReportProbability
      reportingRate weight duration hsum_weight

/--
Lemma 1 probability sanity check: the continuous-duration detection
probability is nonnegative under a normalized nonnegative duration density and
nonnegative reporting rate.
Source status: Lean-checked paper-facing row.
-/
theorem lemma1_continuous_duration_first_report_probability_nonnegative
    {reportingRate : ℝ} {durationDensity : ℝ → ℝ}
    (h_density_mass : (∫ t, durationDensity t ∂durationMeasure) = 1)
    (h_density_integrable : Integrable durationDensity durationMeasure)
    (h_noReport_integrable :
      Integrable
        (fun t => durationDensity t * noArrivalProb reportingRate t)
        durationMeasure)
    (h_density_nonneg : ∀ t, 0 ≤ durationDensity t)
    (h_rate_nonneg : 0 ≤ reportingRate) :
    0 ≤ continuousDurationFirstReportProbability
      reportingRate durationDensity := by
  exact continuousDurationFirstReportProbability_nonneg
    h_density_mass h_density_integrable h_noReport_integrable
    h_density_nonneg h_rate_nonneg

/--
Lemma 1 probability sanity check: the continuous-duration detection
probability is at most one under a nonnegative duration density.
Source status: Lean-checked paper-facing row.
-/
theorem lemma1_continuous_duration_first_report_probability_le_one
    (reportingRate : ℝ) {durationDensity : ℝ → ℝ}
    (h_density_nonneg : ∀ t, 0 ≤ durationDensity t) :
    continuousDurationFirstReportProbability reportingRate durationDensity ≤ 1 := by
  exact continuousDurationFirstReportProbability_le_one
    reportingRate h_density_nonneg

/--
Lemma 1 LLN step: IID observed unique-incident counts in unit intervals have
time-average limit equal to the one-period expected count.
Source status: Lean-checked paper-facing row.
-/
theorem lemma1_unit_interval_observed_counts_lln
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (observedCount : ℕ → Ω → ℝ)
    (hint : Integrable (observedCount 0) P)
    (hindep : Pairwise ((· ⟂ᵢ[P] ·) on observedCount))
    (hident :
      ∀ i, ProbabilityTheory.IdentDistrib
        (observedCount i) (observedCount 0) P P) :
    ∀ᵐ ω ∂P,
      Tendsto
        (fun T : ℕ =>
          (∑ τ ∈ Finset.range T, observedCount τ ω) / T)
        atTop (nhds (∫ ω, observedCount 0 ω ∂P)) := by
  exact LBG24SpatialUnderreporting.lemma1_unit_interval_observed_counts_lln_of_iid
    observedCount hint hindep hident

/--
Lemma 1 source-rate form: if the unit-interval mean is the continuous-duration
observed incident rate, the observed unit-count time average converges to that
rate.
Source status: Lean-checked paper-facing row.
-/
theorem lemma1_unit_interval_observed_counts_lln_to_continuous_duration_rate
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω}
    (observedCount : ℕ → Ω → ℝ)
    (incidentRate reportingRate : ℝ)
    (durationDensity : ℝ → ℝ)
    (hint : Integrable (observedCount 0) P)
    (hindep : Pairwise ((· ⟂ᵢ[P] ·) on observedCount))
    (hident :
      ∀ i, ProbabilityTheory.IdentDistrib
        (observedCount i) (observedCount 0) P P)
    (hmean :
      (∫ ω, observedCount 0 ω ∂P) =
        continuousDurationObservedIncidentRate
          incidentRate reportingRate durationDensity) :
    ∀ᵐ ω ∂P,
      Tendsto
        (fun T : ℕ =>
          (∑ τ ∈ Finset.range T, observedCount τ ω) / T)
        atTop
        (nhds
          (continuousDurationObservedIncidentRate
            incidentRate reportingRate durationDensity)) := by
  exact
    lemma1_unit_interval_observed_counts_lln_to_continuous_duration_rate_of_iid
      observedCount incidentRate reportingRate durationDensity
      hint hindep hident hmean

/--
Lemma 1 source-rate form for the nonhomogeneous cumulative-intensity
continuous-duration rate.
-/
theorem
    lemma1_unit_interval_observed_counts_lln_to_cumulative_intensity_duration_rate
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω}
    (observedCount : ℕ → Ω → ℝ)
    (incidentRate : ℝ)
    (cumulativeIntensity durationDensity : ℝ → ℝ)
    (hint : Integrable (observedCount 0) P)
    (hindep : Pairwise ((· ⟂ᵢ[P] ·) on observedCount))
    (hident :
      ∀ i, ProbabilityTheory.IdentDistrib
        (observedCount i) (observedCount 0) P P)
    (hmean :
      (∫ ω, observedCount 0 ω ∂P) =
        continuousDurationObservedIncidentRateOfCumulativeIntensity
          incidentRate cumulativeIntensity durationDensity) :
    ∀ᵐ ω ∂P,
      Tendsto
        (fun T : ℕ =>
          (∑ τ ∈ Finset.range T, observedCount τ ω) / T)
        atTop
        (nhds
          (continuousDurationObservedIncidentRateOfCumulativeIntensity
            incidentRate cumulativeIntensity durationDensity)) := by
  exact
    lemma1_unit_interval_observed_counts_lln_to_cumulative_intensity_duration_rate_of_iid
      observedCount incidentRate cumulativeIntensity durationDensity
      hint hindep hident hmean

/--
Lemma 1 continuous-duration thinning count law: a latent Poisson incident
count, thinned by the continuous-duration detection probability, has observed
count likelihood with mean equal to the continuous observed incident rate.
Source status: Lean-checked paper-facing row.
-/
theorem lemma1_continuous_duration_poisson_thinning_count_law
    (incidentMean reportingRate : ℝ)
    (durationDensity : ℝ → ℝ) (observedCount : ℕ) :
    (∑' originalCount : ℕ,
        countLikelihood 1 incidentMean originalCount *
          binomialThinningMass
            (continuousDurationFirstReportProbability
              reportingRate durationDensity)
            originalCount observedCount) =
      countLikelihood 1
        (continuousDurationObservedIncidentRate
          incidentMean reportingRate durationDensity)
        observedCount := by
  exact lemma1_continuous_duration_poisson_thinning_count_likelihood
    incidentMean reportingRate durationDensity observedCount

/--
Lemma 1 finite-duration thinning count law: a latent Poisson incident count,
thinned by the finite-duration detection probability, has observed count
likelihood with mean equal to the finite-duration observed incident rate.
Source status: Lean-checked paper-facing row.
-/
theorem lemma1_finite_duration_poisson_thinning_count_law
    {DurationType : Type*} [Fintype DurationType]
    (incidentMean reportingRate : ℝ)
    (weight duration : DurationType → ℝ) (observedCount : ℕ) :
    (∑' originalCount : ℕ,
        countLikelihood 1 incidentMean originalCount *
          binomialThinningMass
            (finiteDurationFirstReportProbability
              reportingRate weight duration)
            originalCount observedCount) =
      countLikelihood 1
        (finiteDurationObservedIncidentRate
          incidentMean reportingRate weight duration)
        observedCount := by
  exact lemma1_finite_duration_poisson_thinning_count_likelihood
    incidentMean reportingRate weight duration observedCount

/--
Lemma 1 nonhomogeneous cumulative-intensity thinning count law: a latent
Poisson incident count thinned by the cumulative-intensity detection
probability has observed count likelihood with the nonhomogeneous observed
incident rate.
-/
theorem
    lemma1_continuous_duration_cumulative_intensity_poisson_thinning_count_law
    (incidentMean : ℝ) (cumulativeIntensity durationDensity : ℝ → ℝ)
    (observedCount : ℕ) :
    (∑' originalCount : ℕ,
        countLikelihood 1 incidentMean originalCount *
          binomialThinningMass
            (continuousDurationFirstReportProbabilityOfCumulativeIntensity
              cumulativeIntensity durationDensity)
            originalCount observedCount) =
      countLikelihood 1
        (continuousDurationObservedIncidentRateOfCumulativeIntensity
          incidentMean cumulativeIntensity durationDensity)
        observedCount := by
  exact
    lemma1_continuous_duration_cumulative_intensity_poisson_thinning_count_likelihood
      incidentMean cumulativeIntensity durationDensity observedCount

/--
Lemma 1 nonhomogeneous Poisson-thinning conclusion in the source's literal
cumulative-intensity notation.
Source status: Lean-checked paper-facing row.
-/
theorem lemma1_nonhomogeneous_poisson_thinning_count_law
    (incidentMean : ℝ) (reportingRate durationDensity : ℝ → ℝ)
    (observedCount : ℕ) :
    (∑' originalCount : ℕ,
        countLikelihood 1 incidentMean originalCount *
          binomialThinningMass
            (continuousDurationFirstReportProbabilityOfCumulativeIntensity
              (fun t => ∫ u in (0 : ℝ)..t, reportingRate u)
              durationDensity)
            originalCount observedCount) =
      countLikelihood 1
        (continuousDurationObservedIncidentRateOfCumulativeIntensity
          incidentMean (fun t => ∫ u in (0 : ℝ)..t, reportingRate u)
          durationDensity)
        observedCount := by
  exact
    lemma1_continuous_duration_cumulative_intensity_poisson_thinning_count_law
      incidentMean (fun t => ∫ u in (0 : ℝ)..t, reportingRate u)
      durationDensity observedCount

/--
Lemma 1 process conclusion: independent reporting thins the latent homogeneous
Poisson incident process into a homogeneous Poisson observed-incident process
whose rate is the latent incident rate times the detection probability.
Source status: Lean-checked constructed-process support row under an explicit
exact joint Poisson/binomial law. It does not derive that law from the source's
duration/report-path model, first-report timestamps, or steady-state premise.
-/
theorem lemma1_observed_incidents_form_poisson_process
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (M : assumption_lemma1_independent_incident_reporting_process Ω P)
    (hdetection : 0 < M.detectionProbability) :
    ∃ observedProcess : ForwardHomogeneousPoissonCountingProcessByLaw Ω P,
      observedProcess.count = M.observedCount ∧
      observedProcess.rate =
        M.latentProcess.rate * M.detectionProbability := by
  exact M.observed_process_is_homogeneous_poisson hdetection

/--
Lemma 1, literal calendar-time reading: the observed incident is an actual
first report in the calendar window, obtained by displacing a stationary
marked birth process by its retained first-report delay. The source model
records the conditional duration/report survival bridge; Lean derives the
Poisson count laws, monotone path property, and independent increments from
the marked birth process.

Source status: Lean-checked paper-facing source-model theorem for
source.txt:1433-1520, with the calendar-time first-report clarification in
`docs/SOURCE_CLARIFICATIONS.md`.
-/
def lemma1CalendarTimeDurationSourceObservedProcessSpec
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    (M : Lemma1CalendarTimeDurationSourceModel Omega P) : Prop :=
    (∀ t : ℝ≥0, Measurable (M.calendarFirstReports.calendarCount t)) ∧
      (∀ᵐ omega ∂P, M.calendarFirstReports.calendarCount 0 omega = 0) ∧
      (∀ᵐ omega ∂P,
        Monotone fun t => M.calendarFirstReports.calendarCount t omega) ∧
      ProbabilityTheory.HasIndepIncrements M.calendarFirstReports.calendarCount P ∧
      ∀ {s t : ℝ≥0}, s ≤ t → ∀ observedCount : ℕ,
        P.real {omega : Omega |
          M.calendarFirstReports.calendarCount t omega -
            M.calendarFirstReports.calendarCount s omega = observedCount} =
          countLikelihood
            (continuousDurationObservedIncidentRateOfCumulativeIntensity
              M.calendarFirstReports.incidentRate
              (fun u => ∫ v in (0 : ℝ)..u, M.reportingIntensity v)
              M.durationDensity)
            ((t : ℝ) - (s : ℝ)) observedCount

theorem lemma1_calendar_time_duration_source_observed_process
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    (M : Lemma1CalendarTimeDurationSourceModel Omega P) :
    lemma1CalendarTimeDurationSourceObservedProcessSpec M := by
  exact M.observed_calendar_process_properties

/--
Proposition 1's homogeneous steady-state limit for calendar-time first
reports. The displayed rate is the source duration mixture at the chosen
reporting-rate parameter.

Source status: Lean-checked paper-facing source-model theorem for
source.txt:1433-1542, with the calendar-time first-report
clarification in `docs/SOURCE_CLARIFICATIONS.md`.
-/
theorem proposition1_calendar_time_homogeneous_source_count_lln
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    (M : Proposition1CalendarTimeDurationSourceModel Omega P)
    (observedRate_pos : 0 < M.observedIncidentRate) :
    ∀ᵐ omega ∂P,
      Tendsto (fun n : ℕ =>
        (M.observedUniqueIncidentCount n omega : ℝ) / n)
        atTop
          (nhds (continuousDurationObservedIncidentRate
            M.calendarFirstReports.incidentRate
            M.reportingRate M.durationDensity)) := by
  exact M.observedUniqueIncidentCount_real_strongLaw
    (M.incidentRate_pos_of_observedIncidentRate_pos observedRate_pos)
    (M.retentionProbability_pos_of_observedIncidentRate_pos observedRate_pos)

/--
Proposition 1's nonidentifiability implication on the literal calendar-time
reading: two source models can have different reporting-rate parameters while
their observed first-report Poisson processes have the same rate. The supplied
equal-rate premise is the compensation relation between the incident rates,
duration law, and reporting rates; Lean derives the two observed processes
from the common calendar-time model rather than treating either as a premise.

Source status: Lean-checked paper-facing source-model theorem for
source.txt:1433-1542, with the calendar-time first-report
clarification in `docs/SOURCE_CLARIFICATIONS.md`.
-/
def proposition1CalendarTimeHomogeneousSourceSpec
    {Omega1 Omega2 : Type*} [MeasurableSpace Omega1] [MeasurableSpace Omega2]
    {P1 : Measure Omega1} {P2 : Measure Omega2}
    (M1 : Proposition1CalendarTimeDurationSourceModel Omega1 P1)
    (M2 : Proposition1CalendarTimeDurationSourceModel Omega2 P2)
    (reporting_rates_ne : M1.reportingRate ≠ M2.reportingRate)
    (observed_rates_eq :
      continuousDurationObservedIncidentRate
        M1.calendarFirstReports.incidentRate M1.reportingRate M1.durationDensity =
      continuousDurationObservedIncidentRate
        M2.calendarFirstReports.incidentRate M2.reportingRate M2.durationDensity)
    (observedRate_pos : 0 < M1.observedIncidentRate) : Prop :=
    (∀ᵐ omega ∂P1,
      Tendsto (fun n : ℕ =>
        (M1.observedUniqueIncidentCount n omega : ℝ) / n)
        atTop
          (nhds (continuousDurationObservedIncidentRate
            M1.calendarFirstReports.incidentRate
            M1.reportingRate M1.durationDensity))) ∧
      M1.reportingRate ≠ M2.reportingRate ∧
        ∃ observedProcess1 : ForwardHomogeneousPoissonCountingProcessByLaw Omega1 P1,
          ∃ observedProcess2 : ForwardHomogeneousPoissonCountingProcessByLaw Omega2 P2,
            observedProcess1.count = M1.calendarFirstReports.calendarCount ∧
            observedProcess2.count = M2.calendarFirstReports.calendarCount ∧
            observedProcess1.rate = observedProcess2.rate

theorem proposition1_calendar_time_homogeneous_source_nonidentifiability
    {Omega1 Omega2 : Type*} [MeasurableSpace Omega1] [MeasurableSpace Omega2]
    {P1 : Measure Omega1} {P2 : Measure Omega2}
    (M1 : Proposition1CalendarTimeDurationSourceModel Omega1 P1)
    (M2 : Proposition1CalendarTimeDurationSourceModel Omega2 P2)
    (reporting_rates_ne : M1.reportingRate ≠ M2.reportingRate)
    (observed_rates_eq :
      continuousDurationObservedIncidentRate
        M1.calendarFirstReports.incidentRate M1.reportingRate M1.durationDensity =
      continuousDurationObservedIncidentRate
        M2.calendarFirstReports.incidentRate M2.reportingRate M2.durationDensity)
    (observedRate_pos : 0 < M1.observedIncidentRate) :
    proposition1CalendarTimeHomogeneousSourceSpec M1 M2 reporting_rates_ne
      observed_rates_eq observedRate_pos := by
  have observed_rates_eq' : M1.observedIncidentRate = M2.observedIncidentRate :=
    observed_rates_eq
  have observedRate2_pos : 0 < M2.observedIncidentRate := by
    rw [← observed_rates_eq']
    exact observedRate_pos
  exact ⟨M1.observedUniqueIncidentCount_real_strongLaw
      (M1.incidentRate_pos_of_observedIncidentRate_pos observedRate_pos)
      (M1.retentionProbability_pos_of_observedIncidentRate_pos observedRate_pos),
    M1.distinct_reporting_rates_same_observed_process_rate
      M2
      (M1.incidentRate_pos_of_observedIncidentRate_pos observedRate_pos)
      (M1.retentionProbability_pos_of_observedIncidentRate_pos observedRate_pos)
      (M2.incidentRate_pos_of_observedIncidentRate_pos observedRate2_pos)
      (M2.retentionProbability_pos_of_observedIncidentRate_pos observedRate2_pos)
      reporting_rates_ne observed_rates_eq'⟩

/--
Lemma 1's explicit birth-cohort proof reading: independently marked latent
Poisson incidents yield a homogeneous retained-birth count process at the
source's possibly nonhomogeneous cumulative-intensity duration-mixture rate.

The conclusion deliberately exposes the count-process laws themselves rather
than returning a packaged process certificate. Thus the source-facing theorem
does not hide measurability, path, independence, or interval-law assumptions
inside a Type-valued witness. The source model exposes the latent process,
independent marks, and the displayed cumulative-intensity probability of at
least one report before the duration ends; Lean derives every displayed
count-process property.  The source proof conditions this count on births in
the same window, so this theorem does not identify it with a calendar-window
count of first reports.
Source status: retired birth-cohort support route for source.txt:1433-1520;
the calendar-first-report route is the paper-facing formalization.
-/
theorem lemma1_steady_state_duration_cumulative_intensity_birth_cohort_process
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    (M : Lemma1CumulativeIntensitySteadyStateDurationSourceModel Omega P) :
    (∀ t : ℝ≥0, Measurable (M.markedProcess.observedCount t)) ∧
      (∀ᵐ omega ∂P, M.markedProcess.observedCount 0 omega = 0) ∧
      (∀ᵐ omega ∂P,
        Monotone fun t => M.markedProcess.observedCount t omega) ∧
      ProbabilityTheory.HasIndepIncrements M.markedProcess.observedCount P ∧
      ∀ {s t : ℝ≥0}, s ≤ t → ∀ observedCount : ℕ,
        P.real {omega : Omega |
          M.markedProcess.observedCount t omega -
            M.markedProcess.observedCount s omega = observedCount} =
          countLikelihood
            (continuousDurationObservedIncidentRateOfCumulativeIntensity
              M.incidentRate
              (fun u => ∫ v in (0 : ℝ)..u, M.reportingIntensity v)
              M.durationDensity)
            ((t : ℝ) - (s : ℝ)) observedCount := by
  refine ⟨M.markedProcess.observedCount_measurable,
    M.markedProcess.observedCount_zero_ae,
    M.markedProcess.observedCount_mono_ae,
    M.markedProcess.observedCount_hasIndepIncrements, ?_⟩
  intro s t hst observedCount
  simpa [continuousDurationObservedIncidentRateOfCumulativeIntensity,
    M.latent_rate_eq_incidentRate,
    M.retention_probability_eq_cumulative_firstReportProbability] using
    M.markedProcess.observedIntervalCount_mass_eq_countLikelihood hst observedCount

/--
Homogeneous specialization of Lemma 1 used by Proposition 1.  This remains a
checked source-model theorem, but it is not the review-surface endpoint for
the full Lemma 1 statement above.
-/
theorem lemma1_steady_state_duration_source_observed_process
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    (M : Lemma1SteadyStateDurationSourceModel Omega P) :
    (∀ t : ℝ≥0, Measurable (M.markedProcess.observedCount t)) ∧
      (∀ᵐ omega ∂P, M.markedProcess.observedCount 0 omega = 0) ∧
      (∀ᵐ omega ∂P,
        Monotone fun t => M.markedProcess.observedCount t omega) ∧
      ProbabilityTheory.HasIndepIncrements M.markedProcess.observedCount P ∧
      ∀ {s t : ℝ≥0}, s ≤ t → ∀ observedCount : ℕ,
        P.real {omega : Omega |
          M.markedProcess.observedCount t omega -
            M.markedProcess.observedCount s omega = observedCount} =
          countLikelihood
            (continuousDurationObservedIncidentRate
              M.incidentRate M.reportingRate M.durationDensity)
            ((t : ℝ) - (s : ℝ)) observedCount := by
  refine ⟨M.markedProcess.observedCount_measurable,
    M.markedProcess.observedCount_zero_ae,
    M.markedProcess.observedCount_mono_ae,
    M.markedProcess.observedCount_hasIndepIncrements, ?_⟩
  intro s t hst observedCount
  simpa [continuousDurationObservedIncidentRate,
    M.latent_rate_eq_incidentRate,
    M.retention_probability_eq_firstReportProbability] using
    M.markedProcess.observedIntervalCount_mass_eq_countLikelihood hst observedCount

/--
Proposition 1's large-time source conclusion: the paper's total observed
unique-incident count, written as the sum of consecutive unit-window counts,
converges almost surely to the same duration-mixture observed rate.

Source status: retired birth-cohort support route for source.txt:1433-1542.
-/
theorem proposition1_steady_state_duration_source_count_lln
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    (M : Lemma1SteadyStateDurationSourceModel Omega P)
    (hdetection : 0 < M.markedProcess.detectionProbability) :
    ∀ᵐ omega ∂P,
      Tendsto (fun n : ℕ =>
        (M.observedUniqueIncidentCount n omega : ℝ) / n)
        atTop
          (nhds (continuousDurationObservedIncidentRate
            M.incidentRate M.reportingRate M.durationDensity)) := by
  exact M.observedUniqueIncidentCount_real_strongLaw hdetection

/--
Proposition 1's observational-equivalence step: two source-steady-state
models with distinct reporting rates but the same observed incident rate induce
observed homogeneous Poisson processes with the same rate.

Source status: retired birth-cohort support route for source.txt:1433-1542.
-/
theorem proposition1_steady_state_duration_source_nonidentifiability
    {Omega1 Omega2 : Type*} [MeasurableSpace Omega1] [MeasurableSpace Omega2]
    {P1 : Measure Omega1} {P2 : Measure Omega2}
    (M1 : Lemma1SteadyStateDurationSourceModel Omega1 P1)
    (M2 : Lemma1SteadyStateDurationSourceModel Omega2 P2)
    (hdetection1 : 0 < M1.markedProcess.detectionProbability)
    (hdetection2 : 0 < M2.markedProcess.detectionProbability)
    (reporting_rates_ne : M1.reportingRate ≠ M2.reportingRate)
    (observed_rates_eq : M1.observedIncidentRate = M2.observedIncidentRate) :
    M1.reportingRate ≠ M2.reportingRate ∧
      ∃ observedProcess1 : ForwardHomogeneousPoissonCountingProcessByLaw Omega1 P1,
        ∃ observedProcess2 : ForwardHomogeneousPoissonCountingProcessByLaw Omega2 P2,
          observedProcess1.count = M1.markedProcess.observedCount ∧
          observedProcess2.count = M2.markedProcess.observedCount ∧
          observedProcess1.rate = observedProcess2.rate := by
  exact M1.compensating_models_have_equal_observed_process_rates M2
    hdetection1 hdetection2 reporting_rates_ne observed_rates_eq

/--
Proposition 1, constructive source-model form: any two distinct reporting
rates with positive duration-mixture detection probabilities admit compensating
positive incident rates and two steady-state source models whose derived
observed Poisson processes have the same rate.

Source status: retired birth-cohort support construction for source.txt:1433-1542.
-/
theorem proposition1_steady_state_duration_source_compensating_models
    (durationDensity : ℝ → ℝ)
    (durationDensity_source :
      ContinuousDurationDensitySourceCondition durationDensity)
    {observedRate reportingRate1 reportingRate2 : ℝ}
    (reporting_rates_ne : reportingRate1 ≠ reportingRate2)
    (observedRate_pos : 0 < observedRate)
    (retention1_pos :
      0 < continuousDurationFirstReportProbability reportingRate1 durationDensity)
    (retention1_le_one :
      continuousDurationFirstReportProbability reportingRate1 durationDensity ≤ 1)
    (retention2_pos :
      0 < continuousDurationFirstReportProbability reportingRate2 durationDensity)
    (retention2_le_one :
      continuousDurationFirstReportProbability reportingRate2 durationDensity ≤ 1) :
    reportingRate1 ≠ reportingRate2 ∧
      ∃ (Omega1 : Type) (mOmega1 : MeasurableSpace Omega1) (P1 : Measure Omega1)
          (M1 : @Lemma1SteadyStateDurationSourceModel Omega1 mOmega1 P1),
        ∃ (Omega2 : Type) (mOmega2 : MeasurableSpace Omega2) (P2 : Measure Omega2)
          (M2 : @Lemma1SteadyStateDurationSourceModel Omega2 mOmega2 P2),
          M1.reportingRate = reportingRate1 ∧
          M2.reportingRate = reportingRate2 ∧
          M1.observedIncidentRate = observedRate ∧
          M2.observedIncidentRate = observedRate ∧
          ∃ observedProcess1 :
              @ForwardHomogeneousPoissonCountingProcessByLaw Omega1 mOmega1 P1,
            ∃ observedProcess2 :
                @ForwardHomogeneousPoissonCountingProcessByLaw Omega2 mOmega2 P2,
              observedProcess1.count = M1.markedProcess.observedCount ∧
              observedProcess2.count = M2.markedProcess.observedCount ∧
              observedProcess1.rate = observedProcess2.rate := by
  exact Lemma1SteadyStateDurationSourceModel.exists_compensating_source_models
    durationDensity durationDensity_source reporting_rates_ne observedRate_pos retention1_pos
      retention1_le_one retention2_pos retention2_le_one

/--
Proposition 1, complete source-steady-state form: two distinct reporting
rates with positive duration-mixture retention probabilities admit
compensating incident rates.  The resulting source models derive the same
observed homogeneous-Poisson rate and each satisfies the displayed
large-time unique-incident-count limit.

The positive-retention branch is the identifiable-observation regime used by
the source's argument; the zero-retention convention is recorded separately
in the post-formalization audit rather than being hidden in this construction.
Source status: retired birth-cohort support route for source.txt:1433-1542.
-/
theorem proposition1_steady_state_duration_source
    (durationDensity : ℝ → ℝ)
    (durationDensity_source :
      ContinuousDurationDensitySourceCondition durationDensity)
    {observedRate reportingRate1 reportingRate2 : ℝ}
    (reporting_rates_ne : reportingRate1 ≠ reportingRate2)
    (observedRate_pos : 0 < observedRate)
    (retention1_pos :
      0 < continuousDurationFirstReportProbability reportingRate1 durationDensity)
    (retention1_le_one :
      continuousDurationFirstReportProbability reportingRate1 durationDensity ≤ 1)
    (retention2_pos :
      0 < continuousDurationFirstReportProbability reportingRate2 durationDensity)
    (retention2_le_one :
      continuousDurationFirstReportProbability reportingRate2 durationDensity ≤ 1) :
    reportingRate1 ≠ reportingRate2 ∧
      ∃ (Omega1 : Type) (mOmega1 : MeasurableSpace Omega1) (P1 : Measure Omega1)
          (M1 : @Lemma1SteadyStateDurationSourceModel Omega1 mOmega1 P1),
        ∃ (Omega2 : Type) (mOmega2 : MeasurableSpace Omega2) (P2 : Measure Omega2)
            (M2 : @Lemma1SteadyStateDurationSourceModel Omega2 mOmega2 P2),
          M1.reportingRate = reportingRate1 ∧
          M2.reportingRate = reportingRate2 ∧
          M1.observedIncidentRate = observedRate ∧
          M2.observedIncidentRate = observedRate ∧
          (∀ᵐ omega ∂P1,
            Tendsto (fun n : ℕ =>
              (M1.observedUniqueIncidentCount n omega : ℝ) / n)
              atTop (nhds observedRate)) ∧
          (∀ᵐ omega ∂P2,
            Tendsto (fun n : ℕ =>
              (M2.observedUniqueIncidentCount n omega : ℝ) / n)
              atTop (nhds observedRate)) ∧
          ∃ observedProcess1 :
              @ForwardHomogeneousPoissonCountingProcessByLaw Omega1 mOmega1 P1,
            ∃ observedProcess2 :
                @ForwardHomogeneousPoissonCountingProcessByLaw Omega2 mOmega2 P2,
              observedProcess1.count = M1.markedProcess.observedCount ∧
              observedProcess2.count = M2.markedProcess.observedCount ∧
              observedProcess1.rate = observedProcess2.rate := by
  rcases proposition1_steady_state_duration_source_compensating_models
      durationDensity durationDensity_source reporting_rates_ne observedRate_pos retention1_pos
        retention1_le_one retention2_pos retention2_le_one with
    ⟨hrates, Omega1, mOmega1, P1, M1, Omega2, mOmega2, P2, M2,
      hreporting1, hreporting2, hobserved1, hobserved2,
      observedProcess1, observedProcess2, hcount1, hcount2, hprocessRate⟩
  refine ⟨hrates, Omega1, mOmega1, P1, M1, Omega2, mOmega2, P2, M2,
    hreporting1, hreporting2, hobserved1, hobserved2, ?_, ?_,
    observedProcess1, observedProcess2, hcount1, hcount2, hprocessRate⟩
  · have hdetection1 : 0 < M1.markedProcess.detectionProbability := by
      apply pos_of_mul_pos_right _ M1.markedProcess.latentProcess.rate_pos.le
      calc
        0 < M1.observedIncidentRate := by simpa [hobserved1] using observedRate_pos
        _ = M1.markedProcess.latentProcess.rate *
              M1.markedProcess.detectionProbability := by
          rw [M1.latent_rate_eq_incidentRate,
            M1.retention_probability_eq_firstReportProbability]
          rfl
    simpa only [hobserved1] using
      M1.observedUniqueIncidentCount_real_strongLaw hdetection1
  · have hdetection2 : 0 < M2.markedProcess.detectionProbability := by
      apply pos_of_mul_pos_right _ M2.markedProcess.latentProcess.rate_pos.le
      calc
        0 < M2.observedIncidentRate := by simpa [hobserved2] using observedRate_pos
        _ = M2.markedProcess.latentProcess.rate *
              M2.markedProcess.detectionProbability := by
          rw [M2.latent_rate_eq_incidentRate,
            M2.retention_probability_eq_firstReportProbability]
          rfl
    simpa only [hobserved2] using
      M2.observedUniqueIncidentCount_real_strongLaw hdetection2

/--
Proposition 1, source-facing non-identifiability existence form.  A positive
observed rate and a duration law with positive retention at the two concrete
positive reporting rates `1` and `2` produce two distinct homogeneous
reporting models with the same direct observed-count process laws and the displayed
large-time limit.

The source treats the duration law as a genuine probability law.  Its
nonnegative density is used only to derive the probability upper bounds needed
by the marked-Poisson construction; positive retention at the selected rates
is the explicit positive-observation regularity of this existential branch.
Source status: retired birth-cohort support route for source.txt:1433-1542.
-/
theorem proposition1_steady_state_duration_source_exists_nonidentifiability
    (durationDensity : ℝ → ℝ)
    (durationDensity_source :
      ContinuousDurationDensitySourceCondition durationDensity)
    {observedRate : ℝ}
    (observedRate_pos : 0 < observedRate)
    (retention_one_pos :
      0 < continuousDurationFirstReportProbability 1 durationDensity)
    (retention_two_pos :
      0 < continuousDurationFirstReportProbability 2 durationDensity) :
    ∃ reportingRate1 reportingRate2 : ℝ,
      0 < reportingRate1 ∧
      0 < reportingRate2 ∧
      reportingRate1 ≠ reportingRate2 ∧
      ∃ (Omega1 : Type) (mOmega1 : MeasurableSpace Omega1) (P1 : Measure Omega1)
          (M1 : @Lemma1SteadyStateDurationSourceModel Omega1 mOmega1 P1),
        ∃ (Omega2 : Type) (mOmega2 : MeasurableSpace Omega2) (P2 : Measure Omega2)
            (M2 : @Lemma1SteadyStateDurationSourceModel Omega2 mOmega2 P2),
          M1.reportingRate = reportingRate1 ∧
          M2.reportingRate = reportingRate2 ∧
          M1.observedIncidentRate = observedRate ∧
          M2.observedIncidentRate = observedRate ∧
          (∀ᵐ omega ∂P1,
            Tendsto (fun n : ℕ =>
              (M1.observedUniqueIncidentCount n omega : ℝ) / n)
              atTop (nhds observedRate)) ∧
          (∀ᵐ omega ∂P2,
            Tendsto (fun n : ℕ =>
              (M2.observedUniqueIncidentCount n omega : ℝ) / n)
              atTop (nhds observedRate)) ∧
          ((∀ t : ℝ≥0, Measurable (M1.markedProcess.observedCount t)) ∧
            (∀ᵐ omega ∂P1, M1.markedProcess.observedCount 0 omega = 0) ∧
            (∀ᵐ omega ∂P1,
              Monotone fun t => M1.markedProcess.observedCount t omega) ∧
            ProbabilityTheory.HasIndepIncrements M1.markedProcess.observedCount P1 ∧
            ∀ {s t : ℝ≥0}, s ≤ t → ∀ observedCount : ℕ,
              P1.real {omega : Omega1 |
                M1.markedProcess.observedCount t omega -
                  M1.markedProcess.observedCount s omega = observedCount} =
                countLikelihood
                  (continuousDurationObservedIncidentRate
                    M1.incidentRate M1.reportingRate M1.durationDensity)
                  ((t : ℝ) - (s : ℝ)) observedCount) ∧
          ((∀ t : ℝ≥0, Measurable (M2.markedProcess.observedCount t)) ∧
            (∀ᵐ omega ∂P2, M2.markedProcess.observedCount 0 omega = 0) ∧
            (∀ᵐ omega ∂P2,
              Monotone fun t => M2.markedProcess.observedCount t omega) ∧
            ProbabilityTheory.HasIndepIncrements M2.markedProcess.observedCount P2 ∧
            ∀ {s t : ℝ≥0}, s ≤ t → ∀ observedCount : ℕ,
              P2.real {omega : Omega2 |
                M2.markedProcess.observedCount t omega -
                  M2.markedProcess.observedCount s omega = observedCount} =
                countLikelihood
                  (continuousDurationObservedIncidentRate
                    M2.incidentRate M2.reportingRate M2.durationDensity)
                  ((t : ℝ) - (s : ℝ)) observedCount) := by
  refine ⟨1, 2, by norm_num, by norm_num, ?_⟩
  rcases proposition1_steady_state_duration_source durationDensity
      durationDensity_source (by norm_num) observedRate_pos retention_one_pos
        (ContinuousDurationDensitySourceCondition.firstReportProbability_le_one
          durationDensity_source 1)
        retention_two_pos
        (ContinuousDurationDensitySourceCondition.firstReportProbability_le_one
          durationDensity_source 2) with
    ⟨hrates, Omega1, mOmega1, P1, M1, Omega2, mOmega2, P2, M2,
      hreporting1, hreporting2, hobserved1, hobserved2, hlln1, hlln2,
      observedProcess1, observedProcess2, hcount1, hcount2, hprocessRate⟩
  exact ⟨hrates, Omega1, mOmega1, P1, M1, Omega2, mOmega2, P2, M2,
    hreporting1, hreporting2, hobserved1, hobserved2, hlln1, hlln2,
    lemma1_steady_state_duration_source_observed_process M1,
    lemma1_steady_state_duration_source_observed_process M2⟩

/--
Combined continuous-duration Lemma 1 construction.  The reporting probability
is the paper's duration-mixture integral, and the marked-Poisson constructor
supplies both the latent process and the independently marked observed process.
Source status: Lean-checked restricted construction.  It does not yet derive
the full duration-law steady-state observed process asserted by source Lemma 1.
-/
theorem lemma1_continuous_duration_marked_poisson_process_construction
    (incidentRate reportingRate : ℝ) (durationDensity : ℝ → ℝ)
    (hincident : 0 < incidentRate)
    (hdetection :
      0 < continuousDurationFirstReportProbability reportingRate durationDensity)
    (hdetection_le :
      continuousDurationFirstReportProbability reportingRate durationDensity ≤ 1) :
    ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (P : Measure Ω)
        (M : @Lemma1MarkedPoissonThinning.MarkedPoissonReportingProcess Ω mΩ P),
      M.latentProcess.rate = incidentRate ∧
      M.detectionProbability =
        continuousDurationFirstReportProbability reportingRate durationDensity ∧
      ∃ observedProcess :
          @ForwardHomogeneousPoissonCountingProcessByLaw Ω mΩ P,
        observedProcess.count = M.observedCount ∧
        observedProcess.rate =
          continuousDurationObservedIncidentRate incidentRate reportingRate
            durationDensity := by
  let detectionProbability :=
    continuousDurationFirstReportProbability reportingRate durationDensity
  rcases
      Lemma1MarkedPoissonThinning.MarkedPoissonReportingProcess.exists_markedPoissonReportingProcess
        incidentRate detectionProbability
          hincident hdetection hdetection_le with
    ⟨Ω, mΩ, P, M, hlatent, hdetectionEq⟩
  have M_detection_pos : 0 < M.detectionProbability := by
    rw [hdetectionEq]
    exact hdetection
  rcases M.observed_process_is_homogeneous_poisson M_detection_pos with
    ⟨observedProcess, hcount, hrate⟩
  refine ⟨Ω, mΩ, P, M, hlatent, hdetectionEq, observedProcess, hcount, ?_⟩
  rw [hrate, hlatent, hdetectionEq]
  rfl

/--
Lemma 1 finite-duration observed-count construction: under the stated
nonnegativity side condition, there is a Poisson count model whose singleton
probabilities are the paper PMF with the finite-duration observed incident
rate.
Source status: Lean-checked paper-facing row.
-/
theorem lemma1_finite_duration_poisson_observed_count_construction
    {DurationType : Type*} [Fintype DurationType]
    (incidentMean reportingRate : ℝ)
    (weight duration : DurationType → ℝ)
    (h_observedRate :
      0 ≤ finiteDurationObservedIncidentRate
        incidentMean reportingRate weight duration) :
    ∃ Ω : Type, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω,
      ∃ X : Ω → ℕ,
        Measurable X ∧
        ProbabilityTheory.HasLaw X
          (ProbabilityTheory.poissonMeasure
            (rateExposureParam 1
              (finiteDurationObservedIncidentRate
                incidentMean reportingRate weight duration)
              (by simpa using h_observedRate))) P ∧
        IsProbabilityMeasure P ∧
        ∀ observedCount : ℕ,
          P.real {ω : Ω | X ω = observedCount} =
            sourcePoissonPMF 1
              (finiteDurationObservedIncidentRate
                incidentMean reportingRate weight duration)
              observedCount := by
  exact lemma1_exists_finite_duration_poisson_observed_count
    incidentMean reportingRate weight duration h_observedRate

/--
Lemma 1 continuous-duration observed-count construction: under the stated
nonnegativity side condition, there is a Poisson count model whose singleton
probabilities are the paper PMF with the continuous-duration observed incident
rate.
Source status: Lean-checked paper-facing row.
-/
theorem lemma1_continuous_duration_poisson_observed_count_construction
    (incidentMean reportingRate : ℝ)
    (durationDensity : ℝ → ℝ)
    (h_observedRate :
      0 ≤ continuousDurationObservedIncidentRate
        incidentMean reportingRate durationDensity) :
    ∃ Ω : Type, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω,
      ∃ X : Ω → ℕ,
        Measurable X ∧
        ProbabilityTheory.HasLaw X
          (ProbabilityTheory.poissonMeasure
            (rateExposureParam 1
              (continuousDurationObservedIncidentRate
                incidentMean reportingRate durationDensity)
              (by simpa using h_observedRate))) P ∧
        IsProbabilityMeasure P ∧
        ∀ observedCount : ℕ,
          P.real {ω : Ω | X ω = observedCount} =
            sourcePoissonPMF 1
              (continuousDurationObservedIncidentRate
                incidentMean reportingRate durationDensity)
              observedCount := by
  exact lemma1_exists_continuous_duration_poisson_observed_count
    incidentMean reportingRate durationDensity h_observedRate

/--
Lemma 1 nonhomogeneous continuous-duration observed-count construction:
under the stated nonnegativity side condition, there is a Poisson count model
whose singleton probabilities are the paper PMF with the cumulative-intensity
observed incident rate.
-/
theorem
    lemma1_continuous_duration_cumulative_intensity_poisson_observed_count_construction
    (incidentMean : ℝ)
    (cumulativeIntensity durationDensity : ℝ → ℝ)
    (h_observedRate :
      0 ≤ continuousDurationObservedIncidentRateOfCumulativeIntensity
        incidentMean cumulativeIntensity durationDensity) :
    ∃ Ω : Type, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω,
      ∃ X : Ω → ℕ,
        Measurable X ∧
        ProbabilityTheory.HasLaw X
          (ProbabilityTheory.poissonMeasure
            (rateExposureParam 1
              (continuousDurationObservedIncidentRateOfCumulativeIntensity
                incidentMean cumulativeIntensity durationDensity)
              (by simpa using h_observedRate))) P ∧
        IsProbabilityMeasure P ∧
        ∀ observedCount : ℕ,
          P.real {ω : Ω | X ω = observedCount} =
            sourcePoissonPMF 1
              (continuousDurationObservedIncidentRateOfCumulativeIntensity
                incidentMean cumulativeIntensity durationDensity)
              observedCount := by
  exact
    lemma1_exists_continuous_duration_cumulative_intensity_poisson_observed_count
      incidentMean cumulativeIntensity durationDensity h_observedRate

/--
Appendix Lemma 2 tail form after the source proof's sum/integral collapse:
integrating the independent no-arrival tail against the normalized start-time
density on `s >= lower`, with the shifted Poisson count mass inside the
integrand, gives the tail probability of an exponential waiting-time model.
Source status: Lean-checked paper-facing row.
-/
theorem lemma2_exponential_waiting_tail
    (rate : ℝ) (h_rate : 0 < rate)
    {epsilon lower : ℝ} (h_epsilon : 0 ≤ epsilon)
    {elapsed startDensity : ℝ → ℝ}
    (h_density_mass :
      ∫ s, startDensity s ∂(volume.restrict (Set.Ici lower)) = 1)
    (h_count_nonneg : ∀ s, 0 ≤ rate * elapsed s) :
    ∫ s,
        noArrivalProb rate epsilon *
          (∑' count : ℕ, countLikelihood rate (elapsed s) count) *
          startDensity s ∂(volume.restrict (Set.Ici lower)) =
      ((AppliedModelingLib.Probability.Exponential.Model.mk rate h_rate).measure
        (Set.Ioi epsilon)).toReal := by
  rw [lemma2_no_arrival_density_mixture_with_poisson_count_mass_on_Ici
    rate epsilon lower h_density_mass h_count_nonneg]
  exact lemma2_no_arrival_eq_exponential_tail rate h_rate h_epsilon

/--
Appendix Lemma 2 Eq. (16): after integrating the start-time density and
summing the Poisson count mass, the remaining tail is exponential.
Source status: Lean-checked paper-facing row.
-/
theorem equation16_lemma2_exponential_waiting_tail
    (rate : ℝ) (h_rate : 0 < rate)
    {epsilon lower : ℝ} (h_epsilon : 0 ≤ epsilon)
    {elapsed startDensity : ℝ → ℝ}
    (h_density_mass :
      ∫ s, startDensity s ∂(volume.restrict (Set.Ici lower)) = 1)
    (h_count_nonneg : ∀ s, 0 ≤ rate * elapsed s) :
    ∫ s,
        noArrivalProb rate epsilon *
          (∑' count : ℕ, countLikelihood rate (elapsed s) count) *
          startDensity s ∂(volume.restrict (Set.Ici lower)) =
      ((AppliedModelingLib.Probability.Exponential.Model.mk rate h_rate).measure
        (Set.Ioi epsilon)).toReal := by
  exact lemma2_exponential_waiting_tail
    rate h_rate h_epsilon h_density_mass h_count_nonneg

/--
Appendix Lemma 2 memoryless-tail form: after conditioning on survival through
an elapsed waiting time, the exponential tail ratio equals the tail probability
of the remaining future wait.
Source status: Lean-checked paper-facing row.
-/
theorem lemma2_exponential_waiting_tail_memoryless_ratio
    (rate : ℝ) (h_rate : 0 < rate)
    {elapsed future : ℝ}
    (h_elapsed : 0 ≤ elapsed) (h_future : 0 ≤ future) :
    ((AppliedModelingLib.Probability.Exponential.Model.mk rate h_rate).measure
        (Set.Ioi (elapsed + future))).toReal /
      ((AppliedModelingLib.Probability.Exponential.Model.mk rate h_rate).measure
        (Set.Ioi elapsed)).toReal =
    ((AppliedModelingLib.Probability.Exponential.Model.mk rate h_rate).measure
        (Set.Ioi future)).toReal := by
  exact lemma2_exponential_memoryless_tail_ratio
    rate h_rate h_elapsed h_future

namespace LegacyLemma2ForwardSourceModel

variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]

/-- Measurability of the post-selected-start count constructed from the
source interarrival path. -/
theorem measurable_postStartCount (M : Lemma2ForwardSourceModel Ω P)
    (u : ℝ≥0) :
    Measurable fun ω => forwardPostStopIntervalCount M.process
      M.selection.startTime u ω := by
  change Measurable fun ω =>
    canonicalRenewalCount
        ((M.selection.startTime ω : ℝ) + (u : ℝ))
        (M.interarrivalPath ω) -
      canonicalRenewalCount (M.selection.startTime ω : ℝ)
        (M.interarrivalPath ω)
  have hstart : Measurable fun ω => (M.selection.startTime ω : ℝ) :=
    M.selection.startTime_measurable.coe_nnreal_real
  exact
    (measurable_canonicalRenewalCount_joint.comp
      ((hstart.add measurable_const).prodMk M.interarrivalPath_measurable)).sub
    (measurable_canonicalRenewalCount_joint.comp
      (hstart.prodMk M.interarrivalPath_measurable))

/-- The actual pulled-back forward count and the canonical post-first-report
tail describe the same no-report event almost surely. -/
theorem ae_postStart_zero_iff_canonicalTailNoArrival
    (M : Lemma2ForwardSourceModel Ω P) (u : ℝ≥0) :
    ∀ᵐ ω ∂P,
      forwardPostStopIntervalCount M.process M.selection.startTime u ω = 0 ↔
        Theorem2ConditionOneSelection.canonicalTailNoArrival u
          (M.selection.firstReportTime ω, M.selection.startTime ω)
          (M.selection.postFirstReportTail ω) := by
  let μ : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure M.rate
  let hpath : MeasurePreserving M.interarrivalPath P μ :=
    M.interarrivalPath_hasLaw.measurePreserving M.interarrivalPath_measurable
  have hpos : ∀ᵐ ω ∂P, ∀ n, 0 < M.interarrivalPath ω n :=
    hpath.quasiMeasurePreserving.ae (ae_all_interarrival_positive M.rate_pos)
  have htailRaw : ∀ᵐ path ∂μ,
      Tendsto (fun m : ℕ => arrivalTime m (futureInterarrival 1 path))
        atTop atTop := by
    have hmap : ∀ᵐ tail ∂Measure.map (futureInterarrival 1) μ,
        Tendsto (fun m : ℕ => arrivalTime m tail) atTop atTop := by
      rw [(futureInterarrival_hasLaw_path M.rate_pos 1).map_eq]
      exact ae_arrivalTime_tendsto_atTop M.rate_pos
    exact Measure.tendsto_ae_map
      (futureInterarrival_hasLaw_path M.rate_pos 1).aemeasurable hmap
  have htailCanonical : ∀ᵐ path ∂μ,
      Tendsto (fun m : ℕ => futureArrivalTime 1 m path) atTop atTop := by
    filter_upwards [htailRaw] with path hpathTail
    simpa only [futureArrivalTime_eq_arrivalTime_tail,
      Function.comp_apply] using hpathTail
  have htail : ∀ᵐ ω ∂P,
      Tendsto (fun m : ℕ =>
        futureArrivalTime 1 m (M.interarrivalPath ω)) atTop atTop :=
    hpath.quasiMeasurePreserving.ae htailCanonical
  filter_upwards [hpos, htail] with ω hωpos hωtail
  have hstart :
      (canonicalFirstArrival (M.interarrivalPath ω)).toNNReal ≤
        M.selection.startTime ω := by
    simpa only [M.firstReportTime_eq] using
      M.selection.firstReport_le_start ω
  change canonicalRenewalCount
        ((M.selection.startTime ω : ℝ) + (u : ℝ))
        (M.interarrivalPath ω) -
      canonicalRenewalCount (M.selection.startTime ω : ℝ)
        (M.interarrivalPath ω) = 0 ↔ _
  simpa only [M.firstReportTime_eq, M.postFirstReportTail_eq] using
    canonicalRenewalCount_postStart_zero_iff_canonicalTailNoArrival_of_good
      (M.interarrivalPath ω) (M.selection.startTime ω) u hstart hωpos hωtail

/-- Source-carrier form of Lemma 2 before rewriting the Poisson zero-count
probability as an exponential survival tail. -/
theorem conditional_no_report_given_firstReport
    (M : Lemma2ForwardSourceModel Ω P) (u : ℝ≥0) :
    ∀ᵐ ω ∂P,
      (ProbabilityTheory.condExpKernel P
        (MeasurableSpace.comap M.selection.firstReportTime inferInstance) ω).real
          {ω' | forwardPostStopIntervalCount M.process
            M.selection.startTime u ω' = 0} =
        noArrivalProb M.rate (u : ℝ) := by
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure M.rate) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure M.rate_pos
  let A : Set Ω := {ω | forwardPostStopIntervalCount M.process
    M.selection.startTime u ω = 0}
  let B : Set Ω := {ω |
    Theorem2ConditionOneSelection.canonicalTailNoArrival u
      (M.selection.firstReportTime ω, M.selection.startTime ω)
      (M.selection.postFirstReportTail ω)}
  have hAB : ∀ᵐ ω ∂P, ω ∈ A ↔ ω ∈ B := by
    simpa only [A, B] using M.ae_postStart_zero_iff_canonicalTailNoArrival u
  have hAfun : Measurable fun ω => forwardPostStopIntervalCount M.process
      M.selection.startTime u ω := M.measurable_postStartCount u
  have hBfun : Measurable fun ω =>
      Theorem2ConditionOneSelection.canonicalTailNoArrival u
        (M.selection.firstReportTime ω, M.selection.startTime ω)
        (M.selection.postFirstReportTail ω) := by
    exact Theorem2ConditionOneSelection.measurable_canonicalTailNoArrival u |>.comp
      (M.selection.selection_measurable.prodMk
        M.selection.postFirstReportTail_measurable)
  have hA : MeasurableSet A := by
    simpa only [A, Set.preimage_setOf_eq] using
      hAfun (measurableSet_singleton 0)
  have hB : MeasurableSet B := by
    have hB_eq : B = (fun ω =>
        Theorem2ConditionOneSelection.canonicalTailNoArrival u
          (M.selection.firstReportTime ω, M.selection.startTime ω)
          (M.selection.postFirstReportTail ω)) ⁻¹' {True} := by
      ext ω
      simp [B]
    rw [hB_eq]
    exact hBfun (measurableSet_singleton True)
  have hle : MeasurableSpace.comap M.selection.firstReportTime inferInstance ≤
      (inferInstance : MeasurableSpace Ω) :=
    M.selection.firstReportTime_measurable.comap_le
  letI : IsFiniteMeasure (P.trim hle) :=
    MeasureTheory.isFiniteMeasure_trim hle
  have hkernelA := ProbabilityTheory.condExpKernel_ae_eq_condExp
    (μ := P) (m := MeasurableSpace.comap M.selection.firstReportTime
      inferInstance) hle hA
  have hkernelB := ProbabilityTheory.condExpKernel_ae_eq_condExp
    (μ := P) (m := MeasurableSpace.comap M.selection.firstReportTime
      inferInstance) hle hB
  have hindicator :
      A.indicator (fun _ : Ω => (1 : ℝ)) =ᵐ[P]
        B.indicator (fun _ : Ω => (1 : ℝ)) := by
    filter_upwards [hAB] with ω hω
    by_cases hAω : ω ∈ A
    · have hBω : ω ∈ B := hω.mp hAω
      simp [hAω, hBω]
    · have hBω : ω ∉ B := fun hb => hAω (hω.mpr hb)
      simp [hAω, hBω]
  have hcond := MeasureTheory.condExp_congr_ae
    (m := MeasurableSpace.comap M.selection.firstReportTime inferInstance)
    hindicator
  have hkernelEq : ∀ᵐ ω ∂P,
      (ProbabilityTheory.condExpKernel P
        (MeasurableSpace.comap M.selection.firstReportTime inferInstance) ω).real A =
      (ProbabilityTheory.condExpKernel P
        (MeasurableSpace.comap M.selection.firstReportTime inferInstance) ω).real B := by
    filter_upwards [hkernelA, hkernelB, hcond] with ω hAω hBω hcondω
    rw [hAω, hBω]
    exact hcondω
  have htailResult :=
    M.selection.conditional_canonicalTailNoArrival_real_given_firstReport_of_tailKernel
      M.rate_pos u (ProbabilityTheory.Kernel.const ℝ≥0
        (exponentialInterarrivalMeasure M.rate))
      M.postFirstReportTail_conditional_law (fun _ => rfl)
  filter_upwards [hkernelEq, htailResult] with ω hEq hTail
  change (ProbabilityTheory.condExpKernel P
    (MeasurableSpace.comap M.selection.firstReportTime inferInstance) ω).real A = _
  rw [hEq]
  exact hTail

end LegacyLemma2ForwardSourceModel

/--
Appendix Lemma 2 for a carrier-generic forward homogeneous Poisson source
model: conditional on the first report, the residual wait after any
Condition-1 selected start has the exponential survival tail at the report
rate.
Source status: Lean-checked paper-facing row under explicit path-complete Poisson source semantics.
-/
def lemma2ForwardSelectedStartExponentialTailSpec
    {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (M : Lemma2ForwardSourceModel Ω P)
    (u : ℝ≥0) : Prop :=
    ∀ᵐ ω ∂P,
      (ProbabilityTheory.condExpKernel P
        (MeasurableSpace.comap M.selection.firstReportTime inferInstance) ω).real
          {ω' | forwardPostStopIntervalCount M.process
            M.selection.startTime u ω' = 0} =
        ((AppliedModelingLib.Probability.Exponential.Model.mk
          M.rate M.rate_pos).measure
          (Set.Ioi (u : ℝ))).toReal

theorem lemma2_forward_selected_start_exponential_tail
    {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (M : Lemma2ForwardSourceModel Ω P)
    (u : ℝ≥0) :
    lemma2ForwardSelectedStartExponentialTailSpec M u := by
  filter_upwards [M.conditional_no_report_given_firstReport u] with ω hω
  rw [hω]
  exact noArrivalProb_eq_exponential_tail
    M.rate M.rate_pos (NNReal.coe_nonneg u)

/--
Appendix D.8.2 post-first-report shift result: conditional on the first report,
the complete future interarrival sequence has the iid exponential law at the
same report rate.
Source status: direct unnumbered appendix result.
-/
theorem appendix_shifted_poisson_after_first_jump
    {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (M : assumption_lemma2_forward_source_model Ω P) :
    ProbabilityTheory.condDistrib M.selection.postFirstReportTail
      M.selection.firstReportTime P =ᵐ[P.map M.selection.firstReportTime]
        ProbabilityTheory.Kernel.const ℝ≥0
          (exponentialInterarrivalMeasure M.rate) := by
  exact M.postFirstReportTail_conditional_law

/--
Appendix Lemma 2, concrete source-process form: for the canonical forward
Poisson report process, any Condition-1 selected start has a Poisson
post-start count conditional on the first report.  The selection record is
the paper's genuine conditional-independence assumption; the Poisson process
and its post-first-report tail are constructed rather than certified.
Source status: Lean-checked paper-facing row.
-/
theorem lemma2_canonical_forward_selected_start_conditional_count_law
    {rate : ℝ} (h_rate : 0 < rate) :
    letI : IsProbabilityMeasure (exponentialInterarrivalMeasure rate) :=
      isProbabilityMeasure_exponentialInterarrivalMeasure h_rate
    ∀ (C : assumption_lemma2_condition_one_selection (ℕ → ℝ)
      (exponentialInterarrivalMeasure rate) (ℕ → ℝ)),
      C.firstReportTime =
        (fun ω : ℕ → ℝ => (canonicalFirstArrival ω).toNNReal) →
      C.postFirstReportTail = futureInterarrival 1 →
      ∀ u : ℝ≥0, ∀ᵐ ω ∂exponentialInterarrivalMeasure rate,
      ProbabilityTheory.HasLaw
        (forwardPostStopIntervalCount
          (canonicalForwardHomogeneousPoissonCountingProcessByLaw h_rate)
          C.startTime u)
        (ProbabilityTheory.poissonMeasure
          (rateExposureParam rate (u : ℝ)
            (mul_nonneg h_rate.le (NNReal.coe_nonneg u))))
        (ProbabilityTheory.condExpKernel (exponentialInterarrivalMeasure rate)
          (MeasurableSpace.comap C.firstReportTime inferInstance) ω) := by
  exact lemma2_canonicalForward_selectedStart_conditional_count_hasLaw h_rate

/--
Appendix Lemma 2, concrete source-process survival-tail form.  This is the
paper's stated residual-waiting conclusion after conditioning on the first
report, expressed as an almost-everywhere equality of regular conditional
probabilities.
Source status: Lean-checked paper-facing row.
-/
theorem lemma2_canonical_forward_selected_start_exponential_tail
    {rate : ℝ} (h_rate : 0 < rate) :
    letI : IsProbabilityMeasure (exponentialInterarrivalMeasure rate) :=
      isProbabilityMeasure_exponentialInterarrivalMeasure h_rate
    ∀ (C : assumption_lemma2_condition_one_selection (ℕ → ℝ)
      (exponentialInterarrivalMeasure rate) (ℕ → ℝ)),
      C.firstReportTime =
        (fun ω : ℕ → ℝ => (canonicalFirstArrival ω).toNNReal) →
      C.postFirstReportTail = futureInterarrival 1 →
      ∀ (u : ℝ≥0), ∀ᵐ ω ∂exponentialInterarrivalMeasure rate,
      (ProbabilityTheory.condExpKernel (exponentialInterarrivalMeasure rate)
        (MeasurableSpace.comap C.firstReportTime inferInstance) ω).real
          {ω' | forwardPostStopIntervalCount
            (canonicalForwardHomogeneousPoissonCountingProcessByLaw h_rate)
            C.startTime u ω' = 0} =
        ((AppliedModelingLib.Probability.Exponential.Model.mk rate h_rate).measure
          (Set.Ioi (u : ℝ))).toReal := by
  exact lemma2_canonicalForward_selectedStart_conditional_exponential_tail h_rate

/--
Lemma 2 process-law normalization: one-jump ordered density integrates to the
one-count probability for the same observation window.
Source status: Lean-checked paper-facing row.
-/
theorem lemma2_one_jump_density_normalizes_to_count_probability
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : HomogeneousPoissonProcessLaw Ω P) (T : OrderedOneJumpWindow)
    (h_exposure : T.window.exposure ≠ 0) :
    H.arrivalLaw.oneJumpDensity T *
        (volume (orderedJumpRegion 1 T.window.exposure)).toReal =
      P.real {ω : Ω |
        H.countLaw.intervalCount T.window.startTime T.window.endTime ω = 1} := by
  exact lemma2_process_law_one_jump_density_ordered_region_volume_eq_count_prob
    H T h_exposure

/--
Lemma 2 process-law normalization with a positive-exposure window.
Source status: Lean-checked paper-facing row.
-/
theorem lemma2_one_jump_density_normalizes_to_count_probability_of_pos_exposure
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : HomogeneousPoissonProcessLaw Ω P) (T : OrderedOneJumpWindow)
    (h_exposure_pos : 0 < T.window.exposure) :
    H.arrivalLaw.oneJumpDensity T *
        (volume (orderedJumpRegion 1 T.window.exposure)).toReal =
      P.real {ω : Ω |
        H.countLaw.intervalCount T.window.startTime T.window.endTime ω = 1} := by
  exact lemma2_one_jump_density_normalizes_to_count_probability
    H T (ne_of_gt h_exposure_pos)

/--
Lemma 2 normalization from primitive homogeneous counting-process semantics:
the canonical one-jump ordered density induced by the count process integrates
to the matching one-count probability.
Source status: Lean-checked paper-facing row.
-/
theorem lemma2_one_jump_density_normalizes_to_count_probability_from_counting_process
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : HomogeneousPoissonCountingProcess Ω P) (T : OrderedOneJumpWindow)
    (h_exposure : T.window.exposure ≠ 0) :
    H.toHomogeneousPoissonProcessLaw.arrivalLaw.oneJumpDensity T *
        (volume (orderedJumpRegion 1 T.window.exposure)).toReal =
      P.real {ω : Ω |
        H.intervalCount T.window.startTime T.window.endTime ω = 1} := by
  simpa using
    H.oneJumpDensity_mul_orderedJumpRegionVolume_eq_windowCount_prob
      T h_exposure

/--
Lemma 2 normalization from primitive homogeneous counting-process semantics
with a positive-exposure window.
Source status: Lean-checked paper-facing row.
-/
theorem lemma2_one_jump_density_normalizes_to_count_probability_from_counting_process_of_pos_exposure
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : HomogeneousPoissonCountingProcess Ω P) (T : OrderedOneJumpWindow)
    (h_exposure_pos : 0 < T.window.exposure) :
    H.toHomogeneousPoissonProcessLaw.arrivalLaw.oneJumpDensity T *
        (volume (orderedJumpRegion 1 T.window.exposure)).toReal =
      P.real {ω : Ω |
        H.intervalCount T.window.startTime T.window.endTime ω = 1} := by
  exact
    lemma2_one_jump_density_normalizes_to_count_probability_from_counting_process
      H T (ne_of_gt h_exposure_pos)

/--
Lemma 2 normalization from mathlib Poisson increment laws: the canonical
one-jump ordered density induced by those laws integrates to the matching
one-count probability.
Source status: Lean-checked paper-facing row.
-/
theorem lemma2_one_jump_density_normalizes_to_count_probability_from_poisson_increment_laws
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : HomogeneousPoissonCountingProcessByLaw Ω P) (T : OrderedOneJumpWindow)
    (h_exposure : T.window.exposure ≠ 0) :
    H.toHomogeneousPoissonProcessLaw.arrivalLaw.oneJumpDensity T *
        (volume (orderedJumpRegion 1 T.window.exposure)).toReal =
      P.real {ω : Ω |
        H.intervalCount T.window.startTime T.window.endTime ω = 1} := by
  simpa using
    lemma2_one_jump_density_normalizes_to_count_probability
      H.toHomogeneousPoissonProcessLaw T h_exposure

/--
Lemma 2 normalization from mathlib Poisson increment laws with a
positive-exposure window.
Source status: Lean-checked paper-facing row.
-/
theorem lemma2_one_jump_density_normalizes_to_count_probability_from_poisson_increment_laws_of_pos_exposure
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : HomogeneousPoissonCountingProcessByLaw Ω P) (T : OrderedOneJumpWindow)
    (h_exposure_pos : 0 < T.window.exposure) :
    H.toHomogeneousPoissonProcessLaw.arrivalLaw.oneJumpDensity T *
        (volume (orderedJumpRegion 1 T.window.exposure)).toReal =
      P.real {ω : Ω |
        H.intervalCount T.window.startTime T.window.endTime ω = 1} := by
  exact
    lemma2_one_jump_density_normalizes_to_count_probability_from_poisson_increment_laws
      H T (ne_of_gt h_exposure_pos)

/--
Lemma 2 one-jump density from mathlib Poisson increment laws, written as the
one-count source Poisson PMF divided by ordered-region volume.
Source status: Lean-checked paper-facing row.
-/
theorem lemma2_one_jump_density_eq_pmf_div_volume_from_poisson_increment_laws
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : HomogeneousPoissonCountingProcessByLaw Ω P)
    (T : OrderedOneJumpWindow)
    (h_exposure_pos : 0 < T.window.exposure) :
    H.toHomogeneousPoissonProcessLaw.arrivalLaw.oneJumpDensity T =
      sourcePoissonPMF H.rate T.window.exposure 1 /
        (volume (orderedJumpRegion 1 T.window.exposure)).toReal := by
  simpa [sourcePoissonPMF] using
    H.oneJumpDensity_eq_countLikelihood_div_orderedJumpRegionVolume
      T h_exposure_pos

/--
Lemma 2 process-law normalization: finite ordered density times the ordered
region volume equals the matching count probability for the same observation
window.
Source status: Lean-checked paper-facing row.
-/
theorem lemma2_finite_jump_density_normalizes_to_count_probability
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : HomogeneousPoissonProcessLaw Ω P) (T : OrderedFiniteJumpTimeline)
    (h_exposure : T.window.exposure ≠ 0) :
    H.arrivalLaw.finiteJumpDensity T *
        (volume (orderedJumpRegion T.count T.window.exposure)).toReal =
      P.real {ω : Ω |
        H.countLaw.intervalCount T.window.startTime T.window.endTime ω =
          T.count} := by
  exact lemma2_process_law_finite_jump_density_ordered_region_volume_eq_count_prob
    H T h_exposure

/--
Lemma 2 finite-jump process-law normalization with a positive-exposure window.
Source status: Lean-checked paper-facing row.
-/
theorem lemma2_finite_jump_density_normalizes_to_count_probability_of_pos_exposure
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : HomogeneousPoissonProcessLaw Ω P) (T : OrderedFiniteJumpTimeline)
    (h_exposure_pos : 0 < T.window.exposure) :
    H.arrivalLaw.finiteJumpDensity T *
        (volume (orderedJumpRegion T.count T.window.exposure)).toReal =
      P.real {ω : Ω |
        H.countLaw.intervalCount T.window.startTime T.window.endTime ω =
          T.count} := by
  exact lemma2_finite_jump_density_normalizes_to_count_probability
    H T (ne_of_gt h_exposure_pos)

/--
Lemma 2 finite-jump normalization from primitive homogeneous counting-process
semantics: the canonical finite ordered density induced by the count process
integrates to the matching count probability.
Source status: Lean-checked paper-facing row.
-/
theorem lemma2_finite_jump_density_normalizes_to_count_probability_from_counting_process
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : HomogeneousPoissonCountingProcess Ω P) (T : OrderedFiniteJumpTimeline)
    (h_exposure : T.window.exposure ≠ 0) :
    H.toHomogeneousPoissonProcessLaw.arrivalLaw.finiteJumpDensity T *
        (volume (orderedJumpRegion T.count T.window.exposure)).toReal =
      P.real {ω : Ω |
        H.intervalCount T.window.startTime T.window.endTime ω =
          T.count} := by
  simpa using
    H.finiteJumpDensity_mul_orderedJumpRegionVolume_eq_windowCount_prob
      T h_exposure

/--
Lemma 2 finite-jump normalization from primitive homogeneous counting-process
semantics with a positive-exposure window.
Source status: Lean-checked paper-facing row.
-/
theorem lemma2_finite_jump_density_normalizes_to_count_probability_from_counting_process_of_pos_exposure
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : HomogeneousPoissonCountingProcess Ω P) (T : OrderedFiniteJumpTimeline)
    (h_exposure_pos : 0 < T.window.exposure) :
    H.toHomogeneousPoissonProcessLaw.arrivalLaw.finiteJumpDensity T *
        (volume (orderedJumpRegion T.count T.window.exposure)).toReal =
      P.real {ω : Ω |
        H.intervalCount T.window.startTime T.window.endTime ω =
          T.count} := by
  exact
    lemma2_finite_jump_density_normalizes_to_count_probability_from_counting_process
      H T (ne_of_gt h_exposure_pos)

/--
Lemma 2 finite-jump normalization from mathlib Poisson increment laws: the
canonical finite ordered density induced by those laws integrates to the
matching count probability.
Source status: Lean-checked paper-facing row.
-/
theorem lemma2_finite_jump_density_normalizes_to_count_probability_from_poisson_increment_laws
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : HomogeneousPoissonCountingProcessByLaw Ω P) (T : OrderedFiniteJumpTimeline)
    (h_exposure : T.window.exposure ≠ 0) :
    H.toHomogeneousPoissonProcessLaw.arrivalLaw.finiteJumpDensity T *
        (volume (orderedJumpRegion T.count T.window.exposure)).toReal =
      P.real {ω : Ω |
        H.intervalCount T.window.startTime T.window.endTime ω =
          T.count} := by
  simpa using
    lemma2_finite_jump_density_normalizes_to_count_probability
      H.toHomogeneousPoissonProcessLaw T h_exposure

/--
Lemma 2 finite-jump normalization from mathlib Poisson increment laws with a
positive-exposure window.
Source status: Lean-checked paper-facing row.
-/
theorem lemma2_finite_jump_density_normalizes_to_count_probability_from_poisson_increment_laws_of_pos_exposure
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : HomogeneousPoissonCountingProcessByLaw Ω P) (T : OrderedFiniteJumpTimeline)
    (h_exposure_pos : 0 < T.window.exposure) :
    H.toHomogeneousPoissonProcessLaw.arrivalLaw.finiteJumpDensity T *
        (volume (orderedJumpRegion T.count T.window.exposure)).toReal =
      P.real {ω : Ω |
        H.intervalCount T.window.startTime T.window.endTime ω =
          T.count} := by
  exact
    lemma2_finite_jump_density_normalizes_to_count_probability_from_poisson_increment_laws
      H T (ne_of_gt h_exposure_pos)

/--
Lemma 2 finite-jump density from mathlib Poisson increment laws, written as
the matching source Poisson PMF divided by ordered-region volume.
Source status: Lean-checked paper-facing row.
-/
theorem lemma2_finite_jump_density_eq_pmf_div_volume_from_poisson_increment_laws
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : HomogeneousPoissonCountingProcessByLaw Ω P)
    (T : OrderedFiniteJumpTimeline)
    (h_exposure_pos : 0 < T.window.exposure) :
    H.toHomogeneousPoissonProcessLaw.arrivalLaw.finiteJumpDensity T =
      sourcePoissonPMF H.rate T.window.exposure T.count /
        (volume (orderedJumpRegion T.count T.window.exposure)).toReal := by
  simpa [sourcePoissonPMF] using
    H.finiteJumpDensity_eq_countLikelihood_div_orderedJumpRegionVolume
      T h_exposure_pos

/-- Model formula: homogeneous exponential reporting delay has mean `1 / rate`.
Source status: Lean-checked paper-facing row.
-/
theorem homogeneous_reporting_delay_mean_formula
    (rate : ℝ) (h_rate : 0 < rate) :
    ∫ x, x ∂(AppliedModelingLib.Probability.Exponential.Model.mk rate h_rate).measure =
      1 / rate := by
  exact homogeneous_reporting_delay_mean rate h_rate

/-- Eq. (3): the displayed closed-form rate estimator.
Source status: Lean-checked paper-facing row.
-/
theorem equation3_mle_formula
    (totalCount : ℕ) (totalExposure : ℝ)
    (_hexposure : totalExposure ≠ 0) :
    mleRate totalCount totalExposure =
      (totalCount : ℝ) / totalExposure := by
  rfl

/-- Eq. (3) estimator satisfies the Poisson score equation away from zero.
Source status: Derived audit consequence; reviewed as auxiliary.
-/
theorem equation3_mle_score_equation
    {totalCount : ℕ} {totalExposure : ℝ}
    (hcount : totalCount ≠ 0) (hexposure : totalExposure ≠ 0) :
    poissonRateScore totalCount totalExposure
        (mleRate totalCount totalExposure) = 0 := by
  exact mleRate_score_eq_zero hcount hexposure

/-- Eq. (3): the displayed closed-form rate estimator with positive exposure.
Source status: Lean-checked paper-facing row.
-/
theorem equation3_mle_score_equation_of_pos_exposure
    {totalCount : ℕ} {totalExposure : ℝ}
    (hcount : totalCount ≠ 0) (hexposure : 0 < totalExposure) :
    poissonRateScore totalCount totalExposure
        (mleRate totalCount totalExposure) = 0 := by
  exact equation3_mle_score_equation hcount (ne_of_gt hexposure)

/--
Eq. (3): under the explicit positive-exposure and positive-rate convention,
the displayed estimator globally maximizes the rate-dependent Poisson
log-likelihood kernel.  The source leaves this domain convention implicit.
Source status: Lean-checked conditional formula result; the convention is an
additional-assumption note, not a separate source defect.
-/
theorem equation3_mle_global_logLikelihood_max
    {totalCount : ℕ} {totalExposure rate : ℝ}
    (hcount : totalCount ≠ 0) (hexposure : 0 < totalExposure)
    (hrate : 0 < rate) :
    poissonRateLogLikelihood totalCount totalExposure rate ≤
      poissonRateLogLikelihood totalCount totalExposure
        (mleRate totalCount totalExposure) := by
  exact mleRate_global_logLikelihood_max hcount hexposure hrate

/--
Eq. (3) zero-count boundary: over nonnegative rates and nonnegative exposure,
the displayed estimator `0` globally maximizes the rate-dependent Poisson
log-likelihood kernel.
Source status: Lean-checked paper-facing MLE boundary row.
-/
theorem equation3_mle_global_logLikelihood_max_zero_count
    {totalExposure rate : ℝ}
    (hexposure : 0 ≤ totalExposure) (hrate : 0 ≤ rate) :
    poissonRateLogLikelihood 0 totalExposure rate ≤
      poissonRateLogLikelihood 0 totalExposure
        (mleRate 0 totalExposure) := by
  simp [poissonRateLogLikelihood, poissonRateLogLikelihoodKernel, mleRate]
  exact mul_nonneg hrate hexposure

/--
Eq. (3) finite-product likelihood kernel: after multiplying the incident-level
Poisson factors, the only rate-dependent terms are the total-count power and
the exponential of total exposure.
Source status: Lean-checked paper-facing row.
-/
theorem equation3_product_likelihood_raw_shape
    {Incident : Type*} (s : Finset Incident)
    (rate : ℝ) (exposure : Incident → ℝ) (count : Incident → ℕ) :
    observedIncidentLikelihoodProduct s rate exposure count =
      observedIncidentLikelihoodProductResidual s exposure count *
        rate ^ totalObservedReportCount s count *
          Real.exp (-(rate * totalObservationExposure s exposure)) := by
  exact observedIncidentLikelihoodProduct_eq_raw_shape s rate exposure count

/--
Eq. (3) finite-product likelihood as a total-count Poisson PMF, up to a
rate-independent residual.
Source status: Lean-checked paper-facing row.
-/
theorem equation3_product_likelihood_total_pmf
    {Incident : Type*} (s : Finset Incident)
    (rate : ℝ) (exposure : Incident → ℝ) (count : Incident → ℕ)
    (h_totalExposure : totalObservationExposure s exposure ≠ 0) :
    observedIncidentLikelihoodProduct s rate exposure count =
      observedIncidentLikelihoodTotalPMFResidual s exposure count *
        sourcePoissonPMF rate
          (totalObservationExposure s exposure)
          (totalObservedReportCount s count) := by
  exact observedIncidentLikelihoodProduct_eq_total_pmf
    s rate exposure count h_totalExposure

/--
Eq. (3) finite-product likelihood as a total-count Poisson PMF, with nonzero
total exposure derived from nonnegative exposures and one positive exposure.
Source status: Lean-checked paper-facing row.
-/
theorem equation3_product_likelihood_total_pmf_of_exists_pos_exposure
    {Incident : Type*} (s : Finset Incident)
    (rate : ℝ) (exposure : Incident → ℝ) (count : Incident → ℕ)
    (h_exposure_nonneg : ∀ i ∈ s, 0 ≤ exposure i)
    (h_exists : ∃ i ∈ s, 0 < exposure i) :
    observedIncidentLikelihoodProduct s rate exposure count =
      observedIncidentLikelihoodTotalPMFResidual s exposure count *
        sourcePoissonPMF rate
          (totalObservationExposure s exposure)
          (totalObservedReportCount s count) := by
  exact observedIncidentLikelihoodProduct_eq_total_pmf_of_exists_pos_exposure
    s rate exposure count h_exposure_nonneg h_exists

/--
Eq. (3) stochastic finite-count construction: a finite incident-family Poisson
count certificate realizes the observed-incident product likelihood as a joint
count-event probability.
Source status: Lean-checked paper-facing row.
-/
theorem equation3_finite_poisson_count_event_probability_product
    {Ω Incident : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {rate : ℝ} {exposure : Incident → ℝ}
    (H : FinitePoissonCountFamily Ω P Incident rate exposure)
    (s : Finset Incident) (count : Incident → ℕ) :
    P.real (⋂ i ∈ s, {ω : Ω | H.count i ω = count i}) =
      observedIncidentLikelihoodProduct s rate exposure count := by
  exact finitePoissonCountFamily_observedIncident_event_prob_eq_product
    H s count

/--
Eq. (3) stochastic finite-count construction in total-PMF form: the same joint
count-event probability is a rate-independent residual times one source
Poisson PMF at total exposure and total count.
Source status: Lean-checked paper-facing row.
-/
theorem equation3_finite_poisson_count_event_probability_total_pmf
    {Ω Incident : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {rate : ℝ} {exposure : Incident → ℝ}
    (H : FinitePoissonCountFamily Ω P Incident rate exposure)
    (s : Finset Incident) (count : Incident → ℕ)
    (h_totalExposure : totalObservationExposure s exposure ≠ 0) :
    P.real (⋂ i ∈ s, {ω : Ω | H.count i ω = count i}) =
      observedIncidentLikelihoodTotalPMFResidual s exposure count *
        sourcePoissonPMF rate
          (totalObservationExposure s exposure)
          (totalObservedReportCount s count) := by
  exact finitePoissonCountFamily_observedIncident_event_prob_eq_total_pmf
    H s count h_totalExposure

/--
Eq. (3) stochastic finite-count construction in total-PMF form, with nonzero
total exposure derived from one positive finite-family exposure.
Source status: Lean-checked paper-facing row.
-/
theorem equation3_finite_poisson_count_event_probability_total_pmf_of_exists_pos_exposure
    {Ω Incident : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {rate : ℝ} {exposure : Incident → ℝ}
    (H : FinitePoissonCountFamily Ω P Incident rate exposure)
    (s : Finset Incident) (count : Incident → ℕ)
    (h_exists : ∃ i ∈ s, 0 < exposure i) :
    P.real (⋂ i ∈ s, {ω : Ω | H.count i ω = count i}) =
      observedIncidentLikelihoodTotalPMFResidual s exposure count *
        sourcePoissonPMF rate
          (totalObservationExposure s exposure)
          (totalObservedReportCount s count) := by
  exact
    finitePoissonCountFamily_observedIncident_event_prob_eq_total_pmf_of_exists_pos_exposure
      H s count h_exists

/--
Eq. (3) stochastic finite-count construction after summing over count vectors:
the total observed report count itself has the source Poisson PMF at total
exposure.
Source status: Lean-checked paper-facing row.
-/
theorem equation3_finite_poisson_total_count_event_probability_total_pmf
    {Ω Incident : Type*} [MeasurableSpace Ω] [Fintype Incident]
    [DecidableEq Incident] {P : Measure Ω}
    {rate : ℝ} {exposure : Incident → ℝ}
    (H : FinitePoissonCountFamily Ω P Incident rate exposure)
    (totalReportCount : ℕ) :
    P.real {ω : Ω | (∑ i : Incident, H.count i ω) = totalReportCount} =
      sourcePoissonPMF rate
        (totalObservationExposure (Finset.univ : Finset Incident) exposure)
        totalReportCount := by
  exact
    finitePoissonCountFamily_totalObservedReportCount_event_prob_eq_total_pmf
      H totalReportCount

/--
Eq. (3) stochastic finite-count construction after summing over count vectors
on an arbitrary finite incident set: the selected incidents' total observed
report count has the source Poisson PMF at selected total exposure.
Source status: Lean-checked paper-facing row.
-/
theorem equation3_finite_poisson_total_count_event_probability_total_pmf_finset
    {Ω Incident : Type*} [MeasurableSpace Ω] [DecidableEq Incident]
    {P : Measure Ω} {rate : ℝ} {exposure : Incident → ℝ}
    (H : FinitePoissonCountFamily Ω P Incident rate exposure)
    (s : Finset Incident) (totalReportCount : ℕ) :
    P.real {ω : Ω | (∑ i ∈ s, H.count i ω) = totalReportCount} =
      sourcePoissonPMF rate
        (totalObservationExposure s exposure)
        totalReportCount := by
  exact
    finitePoissonCountFamily_totalObservedReportCount_event_prob_eq_total_pmf_finset
      H s totalReportCount

/-- Eq. (4), main text: the Poisson regression log-link rate formula.
Source status: Lean-checked paper-facing row.
-/
theorem equation4_poisson_regression_rate_formula
    {Feature : Type*} [Fintype Feature]
    (alpha : ℝ) (beta theta : Feature → ℝ) :
    poissonRegressionRate alpha beta theta =
      Real.exp (alpha + ∑ j, beta j * theta j) := by
  exact poissonRegressionRate_eq_logLink alpha beta theta

/-- Eq. (5), supplementary numbering: the same Poisson regression log-link.
Source status: Lean-checked paper-facing row.
-/
theorem equation5_poisson_regression_rate_formula
    {Feature : Type*} [Fintype Feature]
    (alpha : ℝ) (beta theta : Feature → ℝ) :
    poissonRegressionRate alpha beta theta =
      Real.exp (alpha + ∑ j, beta j * theta j) := by
  exact equation4_poisson_regression_rate_formula alpha beta theta

/--
Eq. (6): substituting the log-link rate into the source-facing causal-stopping
Eq. (8) likelihood gives a rate-independent residual times the Poisson PMF.

The endpoint is the same visible-history causal policy and one-terminal-endpoint
density presentation used for the direct source Eq. (8) theorem.  Thus the
factorization is derived from the source model rather than from the older
synthetic condition-function wrapper.
Source status: Lean-checked paper-facing source-model formula for
source.txt:832-845;1567-1590.
-/
theorem equation6_poisson_regression_likelihood_formula
    {Feature : Type*} [Fintype Feature]
    (alpha : ℝ) (beta theta : Feature → ℝ)
    (T : OrderedFiniteJumpTimeline)
    (M : AppendixTheorem2CausalStoppingSourceModel T.count)
    (D : AppendixTheorem2CausalStoppingSourceModel.EndpointDensityPresentation M)
    (exposure_pos : 0 < T.window.exposure) :
    AppendixTheorem2CausalStoppingSourceModel.conditionalLikelihood T M D
        (poissonRegressionRate alpha beta theta) =
      AppendixTheorem2CausalStoppingSourceModel.rateFreeResidual T M D *
        sourcePoissonPMF
          (Real.exp (alpha + ∑ j, beta j * theta j))
          T.window.exposure T.count ∧
      RateIndependent (fun _rate : ℝ =>
        AppendixTheorem2CausalStoppingSourceModel.rateFreeResidual T M D) := by
  constructor
  · simpa only [poissonRegressionRate_eq_logLink] using
      (AppendixTheorem2CausalStoppingSourceModel.conditionalLikelihood_factorizes_eq8 M D
        (poissonRegressionRate_pos alpha beta theta) exposure_pos)
  · exact ⟨AppendixTheorem2CausalStoppingSourceModel.rateFreeResidual T M D,
      fun _ => rfl⟩

/-- Eq. (7), zero-count case: structural zero plus ordinary Poisson zero mass.
Source status: Lean-checked paper-facing count-mixture formula under the
source's explicitly stated independent structural-zero model.
-/
theorem equation7_zero_inflated_likelihood_zero
    (gamma rate exposure : ℝ) :
    zeroInflatedIncidentLikelihood gamma rate exposure 0 =
      gamma + (1 - gamma) * sourcePoissonPMF rate exposure 0 := by
  exact zeroInflatedIncidentLikelihood_zero gamma rate exposure

/-- Eq. (7), positive-count case: only the ordinary Poisson component contributes.
Source status: Lean-checked paper-facing count-mixture formula under the
source's explicitly stated independent structural-zero model.
-/
theorem equation7_zero_inflated_likelihood_positive_count
    {gamma rate exposure : ℝ} {count : ℕ} (hcount : 1 ≤ count) :
    zeroInflatedIncidentLikelihood gamma rate exposure count =
      (1 - gamma) * sourcePoissonPMF rate exposure count := by
  exact zeroInflatedIncidentLikelihood_of_positive_count (by omega)

/-- Eq. (7), zero-count case with the Poisson-regression rate substituted.
Source status: Lean-checked paper-facing row.
-/
theorem equation7_zero_inflated_regression_likelihood_zero
    {Feature : Type*} [Fintype Feature]
    (gamma alpha : ℝ) (beta theta : Feature → ℝ) (exposure : ℝ) :
    zeroInflatedRegressionIncidentLikelihood
        gamma alpha beta theta exposure 0 =
      gamma + (1 - gamma) *
        sourcePoissonPMF
          (Real.exp (alpha + ∑ j, beta j * theta j)) exposure 0 := by
  exact zeroInflatedRegressionIncidentLikelihood_zero
    gamma alpha beta theta exposure

/-- Eq. (7), positive-count case with the Poisson-regression rate substituted.
Source status: Lean-checked paper-facing row.
-/
theorem equation7_zero_inflated_regression_likelihood_positive_count
    {Feature : Type*} [Fintype Feature]
    {gamma alpha exposure : ℝ} {beta theta : Feature → ℝ} {count : ℕ}
    (hcount : count ≠ 0) :
    zeroInflatedRegressionIncidentLikelihood
        gamma alpha beta theta exposure count =
      (1 - gamma) *
        sourcePoissonPMF
          (Real.exp (alpha + ∑ j, beta j * theta j)) exposure count := by
  exact zeroInflatedRegressionIncidentLikelihood_of_positive_count hcount

/-! ## Named Theoretical Claims -/

/--
Proposition 1, homogeneous algebraic core: unique observed incident rates alone
do not identify the reporting rate, because occurrence rates can compensate for
different reporting probabilities and produce the same observed rate.
Source status: Lean-checked paper-facing row.
-/
theorem proposition1_homogeneous_nonidentifiability
    {observedRate rate₁ rate₂ duration : ℝ}
    (hrates : rate₁ ≠ rate₂)
    (hprob₁ : firstReportProbability rate₁ duration ≠ 0)
    (hprob₂ : firstReportProbability rate₂ duration ≠ 0) :
    rate₁ ≠ rate₂ ∧
      homogeneousObservedIncidentRate
          (observedRate / firstReportProbability rate₁ duration)
          rate₁ duration =
        homogeneousObservedIncidentRate
          (observedRate / firstReportProbability rate₂ duration)
          rate₂ duration := by
  exact proposition1_homogeneous_nonidentifiability_collision
    hrates hprob₁ hprob₂

/--
Proposition 1: two distinct reporting rates can be paired with compensating
latent incident rates so that the independently reported observed-incident
paths are homogeneous Poisson processes with the same rate.
Source status: Lean-checked paper-facing row under the process-level independent-reporting premise.
-/
theorem proposition1_continuous_duration_nonidentifiability
    {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂}
    (M₁ : assumption_lemma1_independent_incident_reporting_process Ω₁ P₁)
    (M₂ : assumption_lemma1_independent_incident_reporting_process Ω₂ P₂)
    (durationDensity : ℝ → ℝ)
    {observedRate rate₁ rate₂ : ℝ}
    (hrates : rate₁ ≠ rate₂)
    (hprob₁ :
      continuousDurationFirstReportProbability rate₁ durationDensity ≠ 0)
    (hprob₂ :
      continuousDurationFirstReportProbability rate₂ durationDensity ≠ 0)
    (hincident₁ : M₁.latentProcess.rate =
      observedRate /
        continuousDurationFirstReportProbability rate₁ durationDensity)
    (hincident₂ : M₂.latentProcess.rate =
      observedRate /
        continuousDurationFirstReportProbability rate₂ durationDensity)
    (hdetection₁ : M₁.detectionProbability =
      continuousDurationFirstReportProbability rate₁ durationDensity)
    (hdetection₂ : M₂.detectionProbability =
      continuousDurationFirstReportProbability rate₂ durationDensity) :
    rate₁ ≠ rate₂ ∧
      ∃ observedProcess₁ :
          ForwardHomogeneousPoissonCountingProcessByLaw Ω₁ P₁,
        ∃ observedProcess₂ :
          ForwardHomogeneousPoissonCountingProcessByLaw Ω₂ P₂,
          observedProcess₁.count = M₁.observedCount ∧
          observedProcess₂.count = M₂.observedCount ∧
          observedProcess₁.rate = observedProcess₂.rate := by
  refine ⟨hrates, ?_⟩
  have M₁_detection_ne : M₁.detectionProbability ≠ 0 := by
    rw [hdetection₁]
    exact hprob₁
  have M₂_detection_ne : M₂.detectionProbability ≠ 0 := by
    rw [hdetection₂]
    exact hprob₂
  have M₁_detection_pos : 0 < M₁.detectionProbability :=
    lt_of_le_of_ne M₁.detectionProbability_nonnegative (Ne.symm M₁_detection_ne)
  have M₂_detection_pos : 0 < M₂.detectionProbability :=
    lt_of_le_of_ne M₂.detectionProbability_nonnegative (Ne.symm M₂_detection_ne)
  rcases M₁.observed_process_is_homogeneous_poisson M₁_detection_pos with
    ⟨observedProcess₁, hcount₁, hrate₁⟩
  rcases M₂.observed_process_is_homogeneous_poisson M₂_detection_pos with
    ⟨observedProcess₂, hcount₂, hrate₂⟩
  refine ⟨observedProcess₁, observedProcess₂, hcount₁, hcount₂, ?_⟩
  rw [hrate₁, hrate₂, hincident₁, hincident₂, hdetection₁, hdetection₂]
  exact (proposition1_continuous_duration_nonidentifiability_collision
    durationDensity hrates hprob₁ hprob₂).2

/--
Proposition 1 with both observationally equivalent marked-Poisson models
constructed from the paper's two detection probabilities and compensating
latent incident rates.
Source status: Lean-checked paper-facing construction row.
-/
theorem proposition1_continuous_duration_nonidentifiability_construction
    (durationDensity : ℝ → ℝ)
    {observedRate rate₁ rate₂ : ℝ}
    (hrates : rate₁ ≠ rate₂)
    (hObservedRate : 0 < observedRate)
    (hdetection₁ :
      0 < continuousDurationFirstReportProbability rate₁ durationDensity)
    (hdetection₁_le :
      continuousDurationFirstReportProbability rate₁ durationDensity ≤ 1)
    (hdetection₂ :
      0 < continuousDurationFirstReportProbability rate₂ durationDensity)
    (hdetection₂_le :
      continuousDurationFirstReportProbability rate₂ durationDensity ≤ 1) :
    rate₁ ≠ rate₂ ∧
      ∃ (Ω₁ : Type) (mΩ₁ : MeasurableSpace Ω₁) (P₁ : Measure Ω₁)
          (M₁ : @Lemma1MarkedPoissonThinning.MarkedPoissonReportingProcess
            Ω₁ mΩ₁ P₁),
        ∃ (Ω₂ : Type) (mΩ₂ : MeasurableSpace Ω₂) (P₂ : Measure Ω₂)
            (M₂ : @Lemma1MarkedPoissonThinning.MarkedPoissonReportingProcess
              Ω₂ mΩ₂ P₂),
          M₁.latentProcess.rate =
              observedRate /
                continuousDurationFirstReportProbability rate₁ durationDensity ∧
          M₂.latentProcess.rate =
              observedRate /
                continuousDurationFirstReportProbability rate₂ durationDensity ∧
          M₁.detectionProbability =
              continuousDurationFirstReportProbability rate₁ durationDensity ∧
          M₂.detectionProbability =
              continuousDurationFirstReportProbability rate₂ durationDensity ∧
          ∃ observedProcess₁ :
              @ForwardHomogeneousPoissonCountingProcessByLaw Ω₁ mΩ₁ P₁,
            ∃ observedProcess₂ :
                @ForwardHomogeneousPoissonCountingProcessByLaw Ω₂ mΩ₂ P₂,
              observedProcess₁.count = M₁.observedCount ∧
              observedProcess₂.count = M₂.observedCount ∧
              observedProcess₁.rate = observedProcess₂.rate := by
  let detectionProbability₁ :=
    continuousDurationFirstReportProbability rate₁ durationDensity
  let detectionProbability₂ :=
    continuousDurationFirstReportProbability rate₂ durationDensity
  let incidentRate₁ := observedRate / detectionProbability₁
  let incidentRate₂ := observedRate / detectionProbability₂
  have hincident₁ : 0 < incidentRate₁ :=
    div_pos hObservedRate hdetection₁
  have hincident₂ : 0 < incidentRate₂ :=
    div_pos hObservedRate hdetection₂
  rcases
      Lemma1MarkedPoissonThinning.MarkedPoissonReportingProcess.exists_markedPoissonReportingProcess
        incidentRate₁ detectionProbability₁
          hincident₁ hdetection₁ hdetection₁_le with
    ⟨Ω₁, mΩ₁, P₁, M₁, hlatent₁, hdetectionEq₁⟩
  rcases
      Lemma1MarkedPoissonThinning.MarkedPoissonReportingProcess.exists_markedPoissonReportingProcess
        incidentRate₂ detectionProbability₂
          hincident₂ hdetection₂ hdetection₂_le with
    ⟨Ω₂, mΩ₂, P₂, M₂, hlatent₂, hdetectionEq₂⟩
  have M₁_detection_pos : 0 < M₁.detectionProbability := by
    rw [hdetectionEq₁]
    exact hdetection₁
  have M₂_detection_pos : 0 < M₂.detectionProbability := by
    rw [hdetectionEq₂]
    exact hdetection₂
  rcases M₁.observed_process_is_homogeneous_poisson M₁_detection_pos with
    ⟨observedProcess₁, hcount₁, hrate₁⟩
  rcases M₂.observed_process_is_homogeneous_poisson M₂_detection_pos with
    ⟨observedProcess₂, hcount₂, hrate₂⟩
  refine ⟨hrates, Ω₁, mΩ₁, P₁, M₁, Ω₂, mΩ₂, P₂, M₂,
    hlatent₁, hlatent₂, hdetectionEq₁, hdetectionEq₂,
    observedProcess₁, observedProcess₂, hcount₁, hcount₂, ?_⟩
  rw [hrate₁, hrate₂, hlatent₁, hlatent₂,
    hdetectionEq₁, hdetectionEq₂]
  simpa [incidentRate₁, incidentRate₂, detectionProbability₁,
    detectionProbability₂] using
    (proposition1_continuous_duration_nonidentifiability_collision
      durationDensity hrates (ne_of_gt hdetection₁)
        (ne_of_gt hdetection₂)).2

/--
Proposition 1 homogeneous non-identifiability with positive reporting rates
and positive duration replacing explicit nonzero detection-probability
premises.
Source status: Lean-checked paper-facing row.
-/
theorem proposition1_homogeneous_nonidentifiability_positive
    {observedRate rate₁ rate₂ duration : ℝ}
    (hrates : rate₁ ≠ rate₂)
    (hrate₁ : 0 < rate₁) (hrate₂ : 0 < rate₂)
    (hduration : 0 < duration) :
    rate₁ ≠ rate₂ ∧
      homogeneousObservedIncidentRate
          (observedRate / firstReportProbability rate₁ duration)
          rate₁ duration =
        homogeneousObservedIncidentRate
          (observedRate / firstReportProbability rate₂ duration)
          rate₂ duration := by
  exact proposition1_homogeneous_nonidentifiability_collision_of_pos
    hrates hrate₁ hrate₂ hduration

/--
Proposition 1 finite-duration non-identifiability with positive reporting
rates and a normalized nonnegative duration distribution that has positive
mass on a positive duration.
Source status: Lean-checked paper-facing row.
-/
theorem proposition1_finite_duration_nonidentifiability_positive
    {DurationType : Type*} [Fintype DurationType]
    (weight duration : DurationType → ℝ)
    {observedRate rate₁ rate₂ : ℝ}
    (hrates : rate₁ ≠ rate₂)
    (hrate₁ : 0 < rate₁) (hrate₂ : 0 < rate₂)
    (hweight_nonneg : ∀ d, 0 ≤ weight d)
    (hsum_weight : (∑ d, weight d) = 1)
    (hduration_nonneg : ∀ d, 0 ≤ duration d)
    (h_exists : ∃ d, 0 < weight d ∧ 0 < duration d) :
    rate₁ ≠ rate₂ ∧
      finiteDurationObservedIncidentRate
          (observedRate /
            finiteDurationFirstReportProbability rate₁ weight duration)
          rate₁ weight duration =
        finiteDurationObservedIncidentRate
          (observedRate /
            finiteDurationFirstReportProbability rate₂ weight duration)
          rate₂ weight duration := by
  exact proposition1_finite_duration_nonidentifiability_collision_of_pos
    weight duration hrates hrate₁ hrate₂
    hweight_nonneg hsum_weight hduration_nonneg h_exists

/--
Theorem 1 / Appendix Theorem 2, preferred source-assumption factorization
form: given a homogeneous Poisson process via mathlib Poisson increment laws
plus Condition 1/2 source assumptions, any observed zero/one/multi-report
window case has likelihood equal to a rate-independent residual times the
Poisson count PMF.
Source status: Lean-checked paper-facing row.
-/
theorem theorem1_likelihood_decomposition_from_poisson_increment_laws
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : HomogeneousPoissonCountingProcessByLaw Ω P)
    (K : Theorem2ConditionFunctions)
    (C : Theorem2ObservedWindowCase) :
    C.likelihoodFromPoissonIncrementLaws K H =
      C.residualWith K * sourcePoissonPMF H.rate
        (C.exposureWith K) (C.countWith K) := by
  exact C.factorizationFromPoissonIncrementLaws K H

/--
Theorem 1 / Appendix Theorem 2 in the source's density-kernel likelihood
semantics.  Conditions 1 and 2 are the explicit paper model input; the
rate-parametric observed-window likelihood then factors as a
rate-independent residual times the Poisson count PMF.  This row deliberately
does not invoke the obsolete all-real-time process interface.
Source status: Lean-checked paper-facing row.
-/
theorem theorem1_likelihood_decomposition_with_condition_density_source_model
    (M : assumption_theorem2_condition_density_source_model)
    (rate : ℝ) (C : Theorem2ObservedWindowCase) :
    C.rateLikelihoodWith M.toConditionFunctionSemantics.toConditionFunctions rate =
      C.residualWith M.toConditionFunctionSemantics.toConditionFunctions *
        sourcePoissonPMF rate
          (C.exposureWith M.toConditionFunctionSemantics.toConditionFunctions)
          (C.countWith M.toConditionFunctionSemantics.toConditionFunctions) := by
  exact C.rateLikelihoodWith_factorization
    M.toConditionFunctionSemantics.toConditionFunctions rate

/--
Eq. (1), process-free condition-function form: the likelihood contribution of
one observed window is the displayed Poisson count PMF times a factor
independent of the reporting rate.
Source status: Lean-checked paper-facing row.
-/
theorem equation1_likelihood_decomposition_with_condition_functions
    (K : Theorem2ConditionFunctions) (rate : ℝ)
    (C : Theorem2ObservedWindowCase) :
    C.rateLikelihoodWith K rate =
      sourcePoissonPMF rate (C.exposureWith K) (C.countWith K) *
        C.residualWith K := by
  rw [C.rateLikelihoodWith_factorization K rate]
  ring

/--
Eq. (1), Poisson-increment-law form: when the homogeneous Poisson process is
provided by mathlib increment laws, the observed-window likelihood is the
displayed Poisson count PMF times the rate-independent residual.
Source status: Lean-checked paper-facing row.
-/
theorem equation1_likelihood_decomposition_from_poisson_increment_laws
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : HomogeneousPoissonCountingProcessByLaw Ω P)
    (K : Theorem2ConditionFunctions)
    (C : Theorem2ObservedWindowCase) :
    C.likelihoodFromPoissonIncrementLaws K H =
      sourcePoissonPMF H.rate (C.exposureWith K) (C.countWith K) *
        C.residualWith K := by
  rw [theorem1_likelihood_decomposition_from_poisson_increment_laws H K C]
  ring

/--
Appendix Theorem 2 Eq. (8): the same likelihood decomposition written in the
stochastic-process notation of the supplement.
Source status: Lean-checked paper-facing row.
-/
theorem equation8_theorem2_likelihood_decomposition_from_poisson_increment_laws
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : HomogeneousPoissonCountingProcessByLaw Ω P)
    (K : Theorem2ConditionFunctions)
    (C : Theorem2ObservedWindowCase) :
    C.likelihoodFromPoissonIncrementLaws K H =
      sourcePoissonPMF H.rate (C.exposureWith K) (C.countWith K) *
        C.residualWith K := by
  exact equation1_likelihood_decomposition_from_poisson_increment_laws H K C

/--
Theorem 1 / Appendix Theorem 2 provenance bridge: the likelihood induced by
mathlib Poisson increment laws is exactly the process-free condition-function
likelihood kernel at the primitive process rate.
Source status: Lean-checked paper-facing row.
-/
theorem theorem1_likelihood_from_poisson_increment_laws_eq_condition_function_rate_likelihood
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : HomogeneousPoissonCountingProcessByLaw Ω P)
    (K : Theorem2ConditionFunctions)
    (C : Theorem2ObservedWindowCase) :
    C.likelihoodFromPoissonIncrementLaws K H =
      C.rateLikelihoodWith K H.rate := by
  exact C.likelihoodFromPoissonIncrementLaws_eq_rateLikelihoodWith K H

/--
Appendix B.2 zero-report row from mathlib Poisson increment laws and
rate-independent Condition 1/2 functions.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_zero_report_poisson_increment_law_factorization_row
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : HomogeneousPoissonCountingProcessByLaw Ω P)
    (K : Theorem2ConditionFunctions) (baseCount : ℕ)
    (W : ObservationWindow) :
    theorem2ZeroReportPoissonIncrementLawLikelihood P K baseCount H W =
      (K.zeroReportSourceDataFromWindow baseCount W).residual *
        sourcePoissonPMF H.rate
          (K.zeroReportSourceDataFromWindow baseCount W).exposure
          (K.zeroReportSourceDataFromWindow baseCount W).count := by
  exact theorem2_zero_report_poisson_increment_law_factorization
    P K baseCount H W

/--
Appendix B.2 zero-report row from a combined homogeneous Poisson process law
and rate-independent Condition 1/2 functions.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_zero_report_process_law_factorization_row
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : HomogeneousPoissonProcessLaw Ω P)
    (K : Theorem2ConditionFunctions) (baseCount : ℕ)
    (W : ObservationWindow) :
    theorem2ZeroReportProcessLawLikelihood P K baseCount H W =
      (K.zeroReportSourceDataFromWindow baseCount W).residual *
        sourcePoissonPMF H.rate
          (K.zeroReportSourceDataFromWindow baseCount W).exposure
          (K.zeroReportSourceDataFromWindow baseCount W).count := by
  exact theorem2_zero_report_process_law_factorization
    P K baseCount H W

/--
Appendix B.2 one-report row from a combined homogeneous Poisson process law
and rate-independent Condition 1/2 functions.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_one_report_process_law_factorization_row
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : HomogeneousPoissonProcessLaw Ω P)
    (K : Theorem2ConditionFunctions) (baseCount : ℕ)
    (T : OrderedOneJumpWindow) (h_exposure : T.window.exposure ≠ 0) :
    theorem2OneReportProcessLawLikelihood K baseCount H T =
      (K.oneReportSourceDataFromOrderedJumpWindow
          baseCount T h_exposure).residual *
        sourcePoissonPMF H.rate
          (K.oneReportSourceDataFromOrderedJumpWindow
            baseCount T h_exposure).exposure
          (K.oneReportSourceDataFromOrderedJumpWindow
            baseCount T h_exposure).count := by
  exact theorem2_one_report_process_law_factorization
    K baseCount H T h_exposure

/--
Appendix B.2 one-report row from a combined homogeneous Poisson process law,
with nonzero exposure derived from positive window exposure.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_one_report_process_law_factorization_row_of_pos_exposure
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : HomogeneousPoissonProcessLaw Ω P)
    (K : Theorem2ConditionFunctions) (baseCount : ℕ)
    (T : OrderedOneJumpWindow) (h_exposure_pos : 0 < T.window.exposure) :
    theorem2OneReportProcessLawLikelihood K baseCount H T =
      (K.oneReportSourceDataFromOrderedJumpWindow
          baseCount T (ne_of_gt h_exposure_pos)).residual *
        sourcePoissonPMF H.rate
          (K.oneReportSourceDataFromOrderedJumpWindow
            baseCount T (ne_of_gt h_exposure_pos)).exposure
          (K.oneReportSourceDataFromOrderedJumpWindow
            baseCount T (ne_of_gt h_exposure_pos)).count := by
  exact theorem2_one_report_process_law_factorization_of_pos_exposure
    K baseCount H T h_exposure_pos

/--
Appendix B.2 multi-report row from a combined homogeneous Poisson process law
and rate-independent Condition 1/2 functions.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_multi_report_process_law_factorization_row
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : HomogeneousPoissonProcessLaw Ω P)
    (K : Theorem2ConditionFunctions) (baseCount : ℕ)
    (T : OrderedFiniteJumpTimeline)
    (hcount : 1 < T.count) (h_exposure : T.window.exposure ≠ 0) :
    theorem2MultiReportProcessLawLikelihood K baseCount H T =
      (K.multiReportSourceDataFromOrderedTimeline
          baseCount T hcount h_exposure).residual *
        sourcePoissonPMF H.rate
          (K.multiReportSourceDataFromOrderedTimeline
            baseCount T hcount h_exposure).exposure
          (K.multiReportSourceDataFromOrderedTimeline
            baseCount T hcount h_exposure).count := by
  exact theorem2_multi_report_process_law_factorization
    K baseCount H T hcount h_exposure

/--
Appendix B.2 multi-report row from a combined homogeneous Poisson process law,
with nonzero exposure derived from positive window exposure.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_multi_report_process_law_factorization_row_of_pos_exposure
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : HomogeneousPoissonProcessLaw Ω P)
    (K : Theorem2ConditionFunctions) (baseCount : ℕ)
    (T : OrderedFiniteJumpTimeline)
    (hcount : 1 < T.count) (h_exposure_pos : 0 < T.window.exposure) :
    theorem2MultiReportProcessLawLikelihood K baseCount H T =
      (K.multiReportSourceDataFromOrderedTimeline
          baseCount T hcount (ne_of_gt h_exposure_pos)).residual *
        sourcePoissonPMF H.rate
          (K.multiReportSourceDataFromOrderedTimeline
            baseCount T hcount (ne_of_gt h_exposure_pos)).exposure
          (K.multiReportSourceDataFromOrderedTimeline
            baseCount T hcount (ne_of_gt h_exposure_pos)).count := by
  exact theorem2_multi_report_process_law_factorization_of_pos_exposure
    K baseCount H T hcount h_exposure_pos

/--
Appendix B.2 one-report row from mathlib Poisson increment laws, the
canonical ordered-arrival density at the same rate, and rate-independent
Condition 1/2 functions.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_one_report_poisson_increment_law_factorization_row
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : HomogeneousPoissonCountingProcessByLaw Ω P)
    (K : Theorem2ConditionFunctions) (baseCount : ℕ)
    (T : OrderedOneJumpWindow) (h_exposure : T.window.exposure ≠ 0) :
    theorem2OneReportPoissonIncrementLawLikelihood K baseCount H T =
      (K.oneReportSourceDataFromOrderedJumpWindow
          baseCount T h_exposure).residual *
        sourcePoissonPMF H.rate
          (K.oneReportSourceDataFromOrderedJumpWindow
            baseCount T h_exposure).exposure
          (K.oneReportSourceDataFromOrderedJumpWindow
            baseCount T h_exposure).count := by
  exact theorem2_one_report_poisson_increment_law_factorization
    K baseCount H T h_exposure

/--
Appendix B.2 one-report row from mathlib Poisson increment laws with the
nonzero-exposure premise derived from positive window exposure.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_one_report_poisson_increment_law_factorization_row_of_pos_exposure
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : HomogeneousPoissonCountingProcessByLaw Ω P)
    (K : Theorem2ConditionFunctions) (baseCount : ℕ)
    (T : OrderedOneJumpWindow) (h_exposure_pos : 0 < T.window.exposure) :
    theorem2OneReportPoissonIncrementLawLikelihood K baseCount H T =
      (K.oneReportSourceDataFromOrderedJumpWindow
          baseCount T (ne_of_gt h_exposure_pos)).residual *
        sourcePoissonPMF H.rate
          (K.oneReportSourceDataFromOrderedJumpWindow
            baseCount T (ne_of_gt h_exposure_pos)).exposure
          (K.oneReportSourceDataFromOrderedJumpWindow
            baseCount T (ne_of_gt h_exposure_pos)).count := by
  exact theorem2_one_report_poisson_increment_law_factorization_row
    H K baseCount T (ne_of_gt h_exposure_pos)

/--
Appendix B.2 multi-report row from mathlib Poisson increment laws, the
canonical ordered-arrival density at the same rate, and rate-independent
Condition 1/2 functions.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_multi_report_poisson_increment_law_factorization_row
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : HomogeneousPoissonCountingProcessByLaw Ω P)
    (K : Theorem2ConditionFunctions) (baseCount : ℕ)
    (T : OrderedFiniteJumpTimeline)
    (hcount : 1 < T.count) (h_exposure : T.window.exposure ≠ 0) :
    theorem2MultiReportPoissonIncrementLawLikelihood K baseCount H T =
      (K.multiReportSourceDataFromOrderedTimeline
          baseCount T hcount h_exposure).residual *
        sourcePoissonPMF H.rate
          (K.multiReportSourceDataFromOrderedTimeline
            baseCount T hcount h_exposure).exposure
          (K.multiReportSourceDataFromOrderedTimeline
            baseCount T hcount h_exposure).count := by
  exact theorem2_multi_report_poisson_increment_law_factorization
    K baseCount H T hcount h_exposure

/--
Appendix B.2 multi-report row from mathlib Poisson increment laws with the
nonzero-exposure premise derived from positive window exposure.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_multi_report_poisson_increment_law_factorization_row_of_pos_exposure
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : HomogeneousPoissonCountingProcessByLaw Ω P)
    (K : Theorem2ConditionFunctions) (baseCount : ℕ)
    (T : OrderedFiniteJumpTimeline)
    (hcount : 1 < T.count) (h_exposure_pos : 0 < T.window.exposure) :
    theorem2MultiReportPoissonIncrementLawLikelihood K baseCount H T =
      (K.multiReportSourceDataFromOrderedTimeline
          baseCount T hcount (ne_of_gt h_exposure_pos)).residual *
        sourcePoissonPMF H.rate
          (K.multiReportSourceDataFromOrderedTimeline
            baseCount T hcount (ne_of_gt h_exposure_pos)).exposure
          (K.multiReportSourceDataFromOrderedTimeline
            baseCount T hcount (ne_of_gt h_exposure_pos)).count := by
  exact theorem2_multi_report_poisson_increment_law_factorization_row
    H K baseCount T hcount (ne_of_gt h_exposure_pos)

/--
Appendix B.2 one-report row using the canonical homogeneous arrival-density
law, rather than an arbitrary arrival-density record.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_one_report_canonical_arrival_law_factorization_row
    (rate : ℝ) (h_rate : 0 < rate)
    (K : Theorem2ConditionFunctions) (baseCount : ℕ)
    (T : OrderedOneJumpWindow) (h_exposure : T.window.exposure ≠ 0) :
    theorem2OneReportArrivalLawLikelihood K baseCount
        (HomogeneousArrivalDensityLaw.canonical rate h_rate) T =
      (K.oneReportSourceDataFromOrderedJumpWindow
          baseCount T h_exposure).residual *
        sourcePoissonPMF rate
          (K.oneReportSourceDataFromOrderedJumpWindow
            baseCount T h_exposure).exposure
          (K.oneReportSourceDataFromOrderedJumpWindow
            baseCount T h_exposure).count := by
  simpa using
    theorem2_one_report_arrival_law_factorization
      K baseCount (HomogeneousArrivalDensityLaw.canonical rate h_rate)
      T h_exposure

/--
Appendix B.2 one-report row using the canonical homogeneous arrival-density
law, with the nonzero-exposure premise derived from positive window exposure.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_one_report_canonical_arrival_law_factorization_row_of_pos_exposure
    (rate : ℝ) (h_rate : 0 < rate)
    (K : Theorem2ConditionFunctions) (baseCount : ℕ)
    (T : OrderedOneJumpWindow) (h_exposure_pos : 0 < T.window.exposure) :
    theorem2OneReportArrivalLawLikelihood K baseCount
        (HomogeneousArrivalDensityLaw.canonical rate h_rate) T =
      (K.oneReportSourceDataFromOrderedJumpWindow
          baseCount T (ne_of_gt h_exposure_pos)).residual *
        sourcePoissonPMF rate
          (K.oneReportSourceDataFromOrderedJumpWindow
            baseCount T (ne_of_gt h_exposure_pos)).exposure
          (K.oneReportSourceDataFromOrderedJumpWindow
            baseCount T (ne_of_gt h_exposure_pos)).count := by
  exact theorem2_one_report_canonical_arrival_law_factorization_row
    rate h_rate K baseCount T (ne_of_gt h_exposure_pos)

/--
Appendix B.2 multi-report row using the canonical homogeneous arrival-density
law, rather than an arbitrary arrival-density record.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_multi_report_canonical_arrival_law_factorization_row
    (rate : ℝ) (h_rate : 0 < rate)
    (K : Theorem2ConditionFunctions) (baseCount : ℕ)
    (T : OrderedFiniteJumpTimeline)
    (hcount : 1 < T.count) (h_exposure : T.window.exposure ≠ 0) :
    theorem2MultiReportArrivalLawLikelihood K baseCount
        (HomogeneousArrivalDensityLaw.canonical rate h_rate) T =
      (K.multiReportSourceDataFromOrderedTimeline
          baseCount T hcount h_exposure).residual *
        sourcePoissonPMF rate
          (K.multiReportSourceDataFromOrderedTimeline
            baseCount T hcount h_exposure).exposure
          (K.multiReportSourceDataFromOrderedTimeline
            baseCount T hcount h_exposure).count := by
  simpa using
    theorem2_multi_report_arrival_law_factorization
      K baseCount (HomogeneousArrivalDensityLaw.canonical rate h_rate)
      T hcount h_exposure

/--
Appendix B.2 multi-report row using the canonical homogeneous arrival-density
law, with the nonzero-exposure premise derived from positive window exposure.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_multi_report_canonical_arrival_law_factorization_row_of_pos_exposure
    (rate : ℝ) (h_rate : 0 < rate)
    (K : Theorem2ConditionFunctions) (baseCount : ℕ)
    (T : OrderedFiniteJumpTimeline)
    (hcount : 1 < T.count) (h_exposure_pos : 0 < T.window.exposure) :
    theorem2MultiReportArrivalLawLikelihood K baseCount
        (HomogeneousArrivalDensityLaw.canonical rate h_rate) T =
      (K.multiReportSourceDataFromOrderedTimeline
          baseCount T hcount (ne_of_gt h_exposure_pos)).residual *
        sourcePoissonPMF rate
          (K.multiReportSourceDataFromOrderedTimeline
            baseCount T hcount (ne_of_gt h_exposure_pos)).exposure
          (K.multiReportSourceDataFromOrderedTimeline
            baseCount T hcount (ne_of_gt h_exposure_pos)).count := by
  exact theorem2_multi_report_canonical_arrival_law_factorization_row
    rate h_rate K baseCount T hcount (ne_of_gt h_exposure_pos)

/--
Unified Appendix B.2 zero/one/multi process-law case from mathlib Poisson
increment laws and the canonical ordered-arrival density at the same rate.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_process_law_case_from_poisson_increment_laws
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : HomogeneousPoissonCountingProcessByLaw Ω P)
    (C : Theorem2ProcessLawCase) :
    C.likelihoodFromPoissonIncrementLaws H =
      C.residual * sourcePoissonPMF H.rate C.exposure C.count := by
  exact C.factorizationFromPoissonIncrementLaws H

/--
Finite-product observed-arrival decomposition from mathlib Poisson increment
laws: the product of generic zero/one/finite-arrival likelihoods collapses to
one total-count source Poisson PMF with a rate-independent residual.
Source status: Lean-checked paper-facing row.
-/
theorem theorem1_observed_arrival_product_from_poisson_increment_laws
    {Ω Incident : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : HomogeneousPoissonCountingProcessByLaw Ω P)
    (s : Finset Incident) (C : Incident → ObservedArrivalCase)
    (h_totalExposure :
      totalExposure s (fun i => (C i).exposure) ≠ 0) :
    (∏ i ∈ s, H.observedArrivalCaseLikelihood (C i)) =
      ObservedArrivalCase.productResidual s C *
        sourcePoissonPMF H.rate
          (totalExposure s fun i => (C i).exposure)
          (totalCount s fun i => (C i).count) := by
  simpa [sourcePoissonPMF] using
    H.observedArrivalCaseLikelihood_product_decomposition
      s C h_totalExposure

/--
Finite-product observed-arrival decomposition from mathlib Poisson increment
laws with nonzero total exposure derived from one positive-exposure observed
case.
Source status: Lean-checked paper-facing row.
-/
theorem theorem1_observed_arrival_product_from_poisson_increment_laws_of_exists_pos_exposure
    {Ω Incident : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : HomogeneousPoissonCountingProcessByLaw Ω P)
    (s : Finset Incident) (C : Incident → ObservedArrivalCase)
    (h_exists : ∃ i ∈ s, 0 < (C i).exposure) :
    (∏ i ∈ s, H.observedArrivalCaseLikelihood (C i)) =
      ObservedArrivalCase.productResidual s C *
        sourcePoissonPMF H.rate
          (totalExposure s fun i => (C i).exposure)
          (totalCount s fun i => (C i).count) := by
  simpa [sourcePoissonPMF] using
    H.observedArrivalCaseLikelihood_product_decomposition_of_exists_pos_exposure
      s C h_exists

/--
Finite-product Theorem 1 decomposition for zero/one/multi process-law cases
induced directly by mathlib Poisson increment laws and the canonical
ordered-arrival density at the same rate.
Source status: Lean-checked paper-facing row.
-/
theorem theorem1_process_law_case_product_from_poisson_increment_laws
    {Ω Incident : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : HomogeneousPoissonCountingProcessByLaw Ω P)
    (s : Finset Incident) (C : Incident → Theorem2ProcessLawCase)
    (h_totalExposure :
      totalExposure s (fun i => (C i).exposure) ≠ 0) :
    (∏ i ∈ s, (C i).likelihoodFromPoissonIncrementLaws H) =
      theorem2ProcessLawCaseProductResidual s C *
        sourcePoissonPMF H.rate
          (totalExposure s fun i => (C i).exposure)
          (totalCount s fun i => (C i).count) := by
  exact
    theorem1_process_law_likelihood_product_decomposition_from_poisson_increment_laws
      s C H h_totalExposure

/--
Finite-product Theorem 1 decomposition for zero/one/multi process-law cases
from mathlib Poisson increment laws, deriving nonzero total exposure from one
positive-exposure observed case.
-/
theorem
    theorem1_process_law_case_product_from_poisson_increment_laws_of_exists_pos_exposure
    {Ω Incident : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : HomogeneousPoissonCountingProcessByLaw Ω P)
    (s : Finset Incident) (C : Incident → Theorem2ProcessLawCase)
    (h_exists : ∃ i ∈ s, 0 < (C i).exposure) :
    (∏ i ∈ s, (C i).likelihoodFromPoissonIncrementLaws H) =
      theorem2ProcessLawCaseProductResidual s C *
        sourcePoissonPMF H.rate
          (totalExposure s fun i => (C i).exposure)
          (totalCount s fun i => (C i).count) := by
  exact
    theorem1_process_law_likelihood_product_decomposition_from_poisson_increment_laws_of_exists_pos_exposure
      s C H h_exists

/--
Theorem 1 / Appendix Theorem 2 from primitive source semantics: the paper's
rate-indexed Condition 1/2 terms are first reduced to rate-independent
condition functions, then the homogeneous Poisson increment laws supply the
Poisson count PMF.
Source status: Lean-checked paper-facing row.
-/
theorem theorem1_likelihood_decomposition_from_source_semantics
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (S : theorem2_poisson_process_and_condition_semantics Ω P)
    (C : Theorem2ObservedWindowCase) :
    C.likelihoodFromSourceSemantics S =
      C.residualFromSourceSemantics S * sourcePoissonPMF S.rate
        (C.exposureFromSourceSemantics S)
        (C.countFromSourceSemantics S) := by
  exact C.factorizationFromSourceSemantics S

/--
Theorem 1 / Appendix Theorem 2 with primitive source semantics constructed
inside Lean from mathlib Poisson increment laws and rate-independent Condition
1/2 functions.
Source status: Lean-checked paper-facing row.
-/
theorem theorem1_likelihood_decomposition_from_constructed_source_semantics
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : HomogeneousPoissonCountingProcessByLaw Ω P)
    (K : Theorem2ConditionFunctions)
    (C : Theorem2ObservedWindowCase) :
    C.likelihoodFromSourceSemantics
        (theorem2_poisson_process_and_condition_semantics.fromPoissonIncrementLawsAndConditionFunctions
          H K) =
      C.residualWith K * sourcePoissonPMF H.rate
        (C.exposureWith K) (C.countWith K) := by
  exact C.factorizationFromConstructedSourceSemantics H K

/--
Theorem 1 / Appendix Theorem 2 with primitive source semantics constructed
inside Lean from mathlib Poisson increment laws and the paper's rate-indexed
Condition 1/2 source semantics.
Source status: Lean-checked paper-facing row.
-/
theorem theorem1_likelihood_decomposition_from_poisson_increment_laws_and_condition_semantics
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : HomogeneousPoissonCountingProcessByLaw Ω P)
    (G : Theorem2ConditionFunctionSemantics)
    (C : Theorem2ObservedWindowCase) :
    C.likelihoodFromSourceSemantics
        (theorem2_poisson_process_and_condition_semantics.fromPoissonIncrementLawsAndConditionSemantics
          H G) =
      C.residualWith G.toConditionFunctions * sourcePoissonPMF H.rate
        (C.exposureWith G.toConditionFunctions)
        (C.countWith G.toConditionFunctions) := by
  exact C.factorizationFromPoissonIncrementLawsAndConditionSemantics H G

/--
Theorem 1 / Appendix Theorem 2 with primitive source semantics constructed
inside Lean from mathlib Poisson increment laws and the paper's explicit
Condition 1/2 source model.
Source status: Lean-checked paper-facing row.
-/
theorem theorem1_likelihood_decomposition_from_poisson_increment_laws_and_condition_source_model
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : HomogeneousPoissonCountingProcessByLaw Ω P)
    (M : Theorem2ConditionSourceModel)
    (C : Theorem2ObservedWindowCase) :
    C.likelihoodFromSourceSemantics
        (theorem2_poisson_process_and_condition_semantics.fromPoissonIncrementLawsAndConditionSourceModel
          H M) =
      C.residualWith M.toConditionFunctionSemantics.toConditionFunctions *
        sourcePoissonPMF H.rate
          (C.exposureWith M.toConditionFunctionSemantics.toConditionFunctions)
          (C.countWith M.toConditionFunctionSemantics.toConditionFunctions) := by
  exact
    C.factorizationFromPoissonIncrementLawsAndConditionSemantics
      H M.toConditionFunctionSemantics

/--
Theorem 1 / Appendix Theorem 2 from mathlib Poisson increment laws and the
density-kernel Condition 1/2 source model.  In this route, `h_m(e)` is an
evaluation of the Condition 2 density kernel and the survival terms are
interval integrals of that same kernel.
Source status: Lean-checked paper-facing row.
-/
theorem theorem1_likelihood_decomposition_from_poisson_increment_laws_and_condition_density_source_model
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : HomogeneousPoissonCountingProcessByLaw Ω P)
    (M : Theorem2ConditionDensitySourceModel)
    (C : Theorem2ObservedWindowCase) :
    C.likelihoodFromSourceSemantics
        (theorem2_poisson_process_and_condition_semantics.fromPoissonIncrementLawsAndConditionDensitySourceModel
          H M) =
      C.residualWith M.toConditionFunctionSemantics.toConditionFunctions *
        sourcePoissonPMF H.rate
          (C.exposureWith M.toConditionFunctionSemantics.toConditionFunctions)
          (C.countWith M.toConditionFunctionSemantics.toConditionFunctions) := by
  exact
    C.factorizationFromPoissonIncrementLawsAndConditionSemantics
      H M.toConditionFunctionSemantics

/--
Theorem 1 / Appendix Theorem 2 from mathlib Poisson increment laws and fixed
paper Condition 1/2 functions.  Here `g(s)` and the `h_m(e)` kernels are
not rate-indexed inputs; the rate-indexed source model is constructed inside
Lean, with rate-independence proved by reflexivity.
Source status: Lean-checked paper-facing row.
-/
theorem theorem1_likelihood_decomposition_from_poisson_increment_laws_and_fixed_condition_density_source_model
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : HomogeneousPoissonCountingProcessByLaw Ω P)
    (M : Theorem2FixedConditionDensitySourceModel)
    (C : Theorem2ObservedWindowCase) :
    C.likelihoodFromSourceSemantics
        (theorem2_poisson_process_and_condition_semantics.fromPoissonIncrementLawsAndConditionDensitySourceModel
          H M.toConditionDensitySourceModel) =
      C.residualWith M.toConditionFunctionSemantics.toConditionFunctions *
        sourcePoissonPMF H.rate
          (C.exposureWith M.toConditionFunctionSemantics.toConditionFunctions)
          (C.countWith M.toConditionFunctionSemantics.toConditionFunctions) := by
  exact
    theorem1_likelihood_decomposition_from_poisson_increment_laws_and_condition_density_source_model
      H M.toConditionDensitySourceModel C

/--
Theorem 1 / Appendix Theorem 2 from the public-partial primitive source model.
This route derives the rate-indexed Condition 1/2 semantics from fixed paper
`g(s)` and `h_m(e)` data; the remaining process-side input is exactly the
homogeneous Poisson counting-process law carried by `M`.
Source status: Lean-checked paper-facing row.
-/
theorem theorem1_likelihood_decomposition_from_primitive_source_model
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (M : Theorem2PrimitiveSourceModel Ω P)
    (C : Theorem2ObservedWindowCase) :
    C.likelihoodFromSourceSemantics M.toSourceSemantics =
      C.residualWith M.conditionFunctions *
        sourcePoissonPMF M.rate
          (C.exposureWith M.conditionFunctions)
          (C.countWith M.conditionFunctions) := by
  exact
    theorem1_likelihood_decomposition_from_poisson_increment_laws_and_fixed_condition_density_source_model
      M.countProcess M.fixedConditionModel C

/--
Theorem 1 / Appendix Theorem 2 source-semantics route agrees with the
Appendix B.2 source-data route assembled from the same rate-indexed Condition
1/2 terms at the source process rate.
Source status: Lean-checked paper-facing row.
-/
theorem theorem1_likelihood_from_source_semantics_eq_source_data_at_rate
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (S : theorem2_poisson_process_and_condition_semantics Ω P)
    (C : Theorem2ObservedWindowCase) :
    C.likelihoodFromSourceSemantics S =
      C.sourceDataLikelihoodAtRate S := by
  exact C.likelihoodFromSourceSemantics_eq_sourceDataLikelihoodAtRate S

/--
The observed-window source-data object assembled at the primitive source rate
is exactly the source-data object carried by the corresponding process-law
case.  This exposes that Appendix B.2 source data are not an independent
assumption once the rate-indexed Condition 1/2 source semantics are supplied.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_observed_window_source_data_at_rate_eq_process_law_case_source_data
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (S : theorem2_poisson_process_and_condition_semantics Ω P)
    (C : Theorem2ObservedWindowCase) :
    C.toProcessSourceDataAtRate S =
      (C.toProcessLawCaseWith S.conditionFunctions).sourceData := by
  exact C.toProcessSourceDataAtRate_eq_processLawCase_sourceData S

/--
The residual term in the Appendix B.2 source-data object agrees with the
residual derived directly from primitive source semantics.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_source_data_residual_at_rate_eq_theorem1_residual
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (S : theorem2_poisson_process_and_condition_semantics Ω P)
    (C : Theorem2ObservedWindowCase) :
    C.sourceDataResidualAtRate S =
      C.residualFromSourceSemantics S := by
  exact C.sourceDataResidualAtRate_eq_residualFromSourceSemantics S

/--
The exposure term in the Appendix B.2 source-data object agrees with the
exposure derived directly from primitive source semantics.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_source_data_exposure_at_rate_eq_theorem1_exposure
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (S : theorem2_poisson_process_and_condition_semantics Ω P)
    (C : Theorem2ObservedWindowCase) :
    C.sourceDataExposureAtRate S =
      C.exposureFromSourceSemantics S := by
  exact C.sourceDataExposureAtRate_eq_exposureFromSourceSemantics S

/--
The count term in the Appendix B.2 source-data object agrees with the count
derived directly from primitive source semantics.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_source_data_count_at_rate_eq_theorem1_count
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (S : theorem2_poisson_process_and_condition_semantics Ω P)
    (C : Theorem2ObservedWindowCase) :
    C.sourceDataCountAtRate S =
      C.countFromSourceSemantics S := by
  exact C.sourceDataCountAtRate_eq_countFromSourceSemantics S

/--
Theorem 1 / Appendix Theorem 2 source semantics reduce directly to the
process-free condition-function likelihood kernel at the source process rate.
Source status: Lean-checked paper-facing row.
-/
theorem theorem1_likelihood_from_source_semantics_eq_condition_function_rate_likelihood
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (S : theorem2_poisson_process_and_condition_semantics Ω P)
    (C : Theorem2ObservedWindowCase) :
    C.likelihoodFromSourceSemantics S =
      C.rateLikelihoodWith S.conditionFunctions S.rate := by
  exact C.likelihoodFromSourceSemantics_eq_rateLikelihoodWith S

/--
The Appendix B.2 source-data likelihood assembled from rate-indexed Condition
1/2 source semantics is the same process-free likelihood kernel obtained from
the derived rate-independent condition functions.
Source status: Lean-checked paper-facing row.
-/
theorem theorem1_source_data_at_rate_eq_condition_function_rate_likelihood
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (S : theorem2_poisson_process_and_condition_semantics Ω P)
    (C : Theorem2ObservedWindowCase) :
    C.sourceDataLikelihoodAtRate S =
      C.rateLikelihoodWith S.conditionFunctions S.rate := by
  exact C.sourceDataLikelihoodAtRate_eq_rateLikelihoodWith S

/--
Theorem 1 / Appendix Theorem 2 source-semantics factorization written directly
through the Appendix B.2 source-data object produced at the source process rate.
Source status: Lean-checked paper-facing row.
-/
theorem theorem1_likelihood_decomposition_from_source_data_at_rate
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (S : theorem2_poisson_process_and_condition_semantics Ω P)
    (C : Theorem2ObservedWindowCase) :
    C.likelihoodFromSourceSemantics S =
      C.sourceDataResidualAtRate S *
        sourcePoissonPMF S.rate
          (C.sourceDataExposureAtRate S)
          (C.sourceDataCountAtRate S) := by
  exact C.factorizationFromSourceSemantics_via_sourceDataAtRate S

/--
Theorem 1 / Appendix Theorem 2 source-semantics factorization written directly
through the derived condition functions and source process rate.
Source status: Lean-checked paper-facing row.
-/
theorem theorem1_likelihood_decomposition_from_source_semantics_via_rate_likelihood
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (S : theorem2_poisson_process_and_condition_semantics Ω P)
    (C : Theorem2ObservedWindowCase) :
    C.likelihoodFromSourceSemantics S =
      C.residualWith S.conditionFunctions *
        sourcePoissonPMF S.rate
          (C.exposureWith S.conditionFunctions)
          (C.countWith S.conditionFunctions) := by
  exact C.factorizationFromSourceSemantics_via_rateLikelihoodWith S

/--
Appendix B.2 ordered one-jump density normalization from primitive source
semantics: the canonical one-jump density integrates over the ordered
one-jump region to the one-count window probability.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_one_jump_ordered_density_normalizes_from_source_semantics
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (S : theorem2_poisson_process_and_condition_semantics Ω P)
    (T : OrderedOneJumpWindow) (h_exposure : T.window.exposure ≠ 0) :
    S.processLaw.arrivalLaw.oneJumpDensity T *
        (volume (orderedJumpRegion 1 T.window.exposure)).toReal =
      P.real {ω : Ω |
        S.countProcess.intervalCount T.window.startTime T.window.endTime ω =
          1} := by
  exact
    theorem2_poisson_process_and_condition_semantics.one_jump_density_ordered_region_volume_eq_count_prob
      S T h_exposure

/--
Appendix B.2 ordered one-jump density normalization from primitive source
semantics, with nonzero exposure derived from positive window exposure.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_one_jump_ordered_density_normalizes_from_source_semantics_of_pos_exposure
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (S : theorem2_poisson_process_and_condition_semantics Ω P)
    (T : OrderedOneJumpWindow) (h_exposure_pos : 0 < T.window.exposure) :
    S.processLaw.arrivalLaw.oneJumpDensity T *
        (volume (orderedJumpRegion 1 T.window.exposure)).toReal =
      P.real {ω : Ω |
        S.countProcess.intervalCount T.window.startTime T.window.endTime ω =
          1} := by
  exact
    theorem2_poisson_process_and_condition_semantics.one_jump_density_ordered_region_volume_eq_count_prob_of_pos_exposure
      S T h_exposure_pos

/--
Appendix B.2 ordered one-jump density normalization from the theorem-facing
source assumption bundle, with nonzero exposure derived from positive window
exposure.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_one_jump_ordered_density_normalizes_from_assumption_bundle_of_pos_exposure
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (A : assumption_theorem2_poisson_process_and_conditions Ω P)
    (T : OrderedOneJumpWindow) (h_exposure_pos : 0 < T.window.exposure) :
    A.processLaw.arrivalLaw.oneJumpDensity T *
        (volume (orderedJumpRegion 1 T.window.exposure)).toReal =
      P.real {ω : Ω |
        A.countProcess.intervalCount T.window.startTime T.window.endTime ω =
          1} := by
  exact
    assumption_theorem2_poisson_process_and_conditions.one_jump_density_ordered_region_volume_eq_count_prob_of_pos_exposure
      A T h_exposure_pos

/--
Appendix B.2 one-jump ordered density from primitive source semantics, written
as one-count Poisson PMF divided by ordered-region volume.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_one_jump_ordered_density_eq_pmf_div_volume_from_source_semantics
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (S : theorem2_poisson_process_and_condition_semantics Ω P)
    (T : OrderedOneJumpWindow)
    (h_exposure_pos : 0 < T.window.exposure) :
    S.processLaw.arrivalLaw.oneJumpDensity T =
      sourcePoissonPMF S.rate T.window.exposure 1 /
        (volume (orderedJumpRegion 1 T.window.exposure)).toReal := by
  exact
    theorem2_poisson_process_and_condition_semantics.one_jump_density_eq_sourcePoissonPMF_div_ordered_region_volume
      S T h_exposure_pos

/--
Appendix B.2 one-jump ordered density from the theorem-facing source
assumption bundle, written as one-count Poisson PMF divided by ordered-region
volume.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_one_jump_ordered_density_eq_pmf_div_volume_from_assumption_bundle
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (A : assumption_theorem2_poisson_process_and_conditions Ω P)
    (T : OrderedOneJumpWindow)
    (h_exposure_pos : 0 < T.window.exposure) :
    A.processLaw.arrivalLaw.oneJumpDensity T =
      sourcePoissonPMF A.rate T.window.exposure 1 /
        (volume (orderedJumpRegion 1 T.window.exposure)).toReal := by
  exact
    assumption_theorem2_poisson_process_and_conditions.one_jump_density_eq_sourcePoissonPMF_div_ordered_region_volume
      A T h_exposure_pos

/--
Window-count probability from primitive source semantics: a deterministic
observation window has the source Poisson count likelihood at its exposure.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_window_count_probability_from_source_semantics
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (S : theorem2_poisson_process_and_condition_semantics Ω P)
    (W : ObservationWindow) (n : ℕ) :
    P.real {ω : Ω |
        S.countProcess.intervalCount W.startTime W.endTime ω = n} =
      sourcePoissonPMF S.rate W.exposure n := by
  simpa [sourcePoissonPMF] using
    theorem2_poisson_process_and_condition_semantics.windowCount_prob S W n

/--
Window-count distribution law from primitive source semantics: the deterministic
observation-window count has the mathlib Poisson law with parameter
`lambda * exposure`.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_window_count_has_poisson_law_from_source_semantics
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (S : theorem2_poisson_process_and_condition_semantics Ω P)
    (W : ObservationWindow) :
    ProbabilityTheory.HasLaw
      (fun ω : Ω =>
        S.countProcess.intervalCount W.startTime W.endTime ω)
      (ProbabilityTheory.poissonMeasure
        (rateExposureParam S.rate W.exposure
          (mul_nonneg (le_of_lt S.rate_pos) W.exposure_nonneg))) P := by
  exact theorem2_poisson_process_and_condition_semantics.windowCount_hasLaw
    S W

/--
Zero-report window-count probability from primitive source semantics: no
reports in the observation window have likelihood `exp (-lambda * exposure)`.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_window_no_arrival_probability_from_source_semantics
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (S : theorem2_poisson_process_and_condition_semantics Ω P)
    (W : ObservationWindow) :
    P.real {ω : Ω |
        S.countProcess.intervalCount W.startTime W.endTime ω = 0} =
      noArrivalProb S.rate W.exposure := by
  exact theorem2_poisson_process_and_condition_semantics.windowCount_zero_prob
    S W

/--
Zero-report window-count probability from primitive source semantics, written
as the exponential waiting-time tail over the observation exposure.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_window_no_arrival_exponential_tail_from_source_semantics
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (S : theorem2_poisson_process_and_condition_semantics Ω P)
    (W : ObservationWindow) :
    P.real {ω : Ω |
        S.countProcess.intervalCount W.startTime W.endTime ω = 0} =
      ((AppliedModelingLib.Probability.Exponential.Model.mk
          S.rate S.rate_pos).measure (Set.Ioi W.exposure)).toReal := by
  exact
    theorem2_poisson_process_and_condition_semantics.windowCount_zero_prob_eq_exponential_tail
      S W

/--
Appendix B.2 finite ordered-jump density normalization from primitive source
semantics: the canonical finite-jump density integrates over the ordered
jump-time region to the matching count-window probability.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_finite_jump_ordered_density_normalizes_from_source_semantics
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (S : theorem2_poisson_process_and_condition_semantics Ω P)
    (T : OrderedFiniteJumpTimeline) (h_exposure : T.window.exposure ≠ 0) :
    S.processLaw.arrivalLaw.finiteJumpDensity T *
        (volume (orderedJumpRegion T.count T.window.exposure)).toReal =
      P.real {ω : Ω |
        S.countProcess.intervalCount T.window.startTime T.window.endTime ω =
          T.count} := by
  exact
    theorem2_poisson_process_and_condition_semantics.finite_jump_density_ordered_region_volume_eq_count_prob
      S T h_exposure

/--
Appendix B.2 finite ordered-jump density normalization from primitive source
semantics, with nonzero exposure derived from positive window exposure.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_finite_jump_ordered_density_normalizes_from_source_semantics_of_pos_exposure
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (S : theorem2_poisson_process_and_condition_semantics Ω P)
    (T : OrderedFiniteJumpTimeline) (h_exposure_pos : 0 < T.window.exposure) :
    S.processLaw.arrivalLaw.finiteJumpDensity T *
        (volume (orderedJumpRegion T.count T.window.exposure)).toReal =
      P.real {ω : Ω |
        S.countProcess.intervalCount T.window.startTime T.window.endTime ω =
          T.count} := by
  exact
    theorem2_poisson_process_and_condition_semantics.finite_jump_density_ordered_region_volume_eq_count_prob_of_pos_exposure
      S T h_exposure_pos

/--
Appendix B.2 finite ordered-jump density normalization from the theorem-facing
source assumption bundle, with nonzero exposure derived from positive window
exposure.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_finite_jump_ordered_density_normalizes_from_assumption_bundle_of_pos_exposure
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (A : assumption_theorem2_poisson_process_and_conditions Ω P)
    (T : OrderedFiniteJumpTimeline) (h_exposure_pos : 0 < T.window.exposure) :
    A.processLaw.arrivalLaw.finiteJumpDensity T *
        (volume (orderedJumpRegion T.count T.window.exposure)).toReal =
      P.real {ω : Ω |
        A.countProcess.intervalCount T.window.startTime T.window.endTime ω =
          T.count} := by
  exact
    assumption_theorem2_poisson_process_and_conditions.finite_jump_density_ordered_region_volume_eq_count_prob_of_pos_exposure
      A T h_exposure_pos

/--
Appendix B.2 finite ordered-jump density from primitive source semantics,
written as count Poisson PMF divided by ordered-region volume.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_finite_jump_ordered_density_eq_pmf_div_volume_from_source_semantics
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (S : theorem2_poisson_process_and_condition_semantics Ω P)
    (T : OrderedFiniteJumpTimeline)
    (h_exposure_pos : 0 < T.window.exposure) :
    S.processLaw.arrivalLaw.finiteJumpDensity T =
      sourcePoissonPMF S.rate T.window.exposure T.count /
        (volume (orderedJumpRegion T.count T.window.exposure)).toReal := by
  exact
    theorem2_poisson_process_and_condition_semantics.finite_jump_density_eq_sourcePoissonPMF_div_ordered_region_volume
      S T h_exposure_pos

/--
Appendix B.2 finite ordered-jump density from the theorem-facing source
assumption bundle, written as count Poisson PMF divided by ordered-region
volume.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_finite_jump_ordered_density_eq_pmf_div_volume_from_assumption_bundle
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (A : assumption_theorem2_poisson_process_and_conditions Ω P)
    (T : OrderedFiniteJumpTimeline)
    (h_exposure_pos : 0 < T.window.exposure) :
    A.processLaw.arrivalLaw.finiteJumpDensity T =
      sourcePoissonPMF A.rate T.window.exposure T.count /
        (volume (orderedJumpRegion T.count T.window.exposure)).toReal := by
  exact
    assumption_theorem2_poisson_process_and_conditions.finite_jump_density_eq_sourcePoissonPMF_div_ordered_region_volume
      A T h_exposure_pos

/--
Finite-dimensional adjacent interval-count law from primitive source semantics:
adjacent count events on a monotone endpoint timeline factor into the product
of Poisson count likelihoods.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_adjacent_interval_counts_product_from_source_semantics
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    (S : theorem2_poisson_process_and_condition_semantics Ω P)
    {n : ℕ} {t : Fin (n + 1) → ℝ} (ht : Monotone t)
    (k : Fin n → ℕ) :
    P.real (⋂ i ∈ (Finset.univ : Finset (Fin n)),
        {ω : Ω |
          S.countProcess.intervalCount (t i.castSucc) (t i.succ) ω =
            k i}) =
      countLikelihoodProduct (Finset.univ : Finset (Fin n)) S.rate
        (fun i => t i.succ - t i.castSucc) k := by
  exact
    theorem2_poisson_process_and_condition_semantics.intervalCount_joint_real_eq_countLikelihoodProduct_fin
      S ht k

/--
Finite incident-family primitive construction: for any finite incident set with
nonnegative exposures and nonnegative Poisson rate, there is a probability
space carrying independent Poisson counts whose joint event likelihood over
that finite set is the product of the incident Poisson PMFs.
Source status: Lean-checked paper-facing row.
-/
theorem theorem1_exists_independent_poisson_count_family_product
    {Incident : Type u}
    (rate : ℝ) (h_rate : 0 ≤ rate)
    (exposure : Incident → ℝ)
    (h_exposure : ∀ i, 0 ≤ exposure i)
    (s : Finset Incident) :
    ∃ Ω : Type u, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω,
      ∃ X : Incident → Ω → ℕ,
        (∀ i, Measurable (X i)) ∧
        (∀ i,
          ProbabilityTheory.HasLaw
            (X i)
            (ProbabilityTheory.poissonMeasure
              (rateExposureParam rate (exposure i)
                (mul_nonneg h_rate (h_exposure i)))) P) ∧
        ProbabilityTheory.iIndepFun X P ∧ IsProbabilityMeasure P ∧
        ∀ k : Incident → ℕ,
          P.real (⋂ i ∈ s, {ω : Ω | X i ω = k i}) =
            countLikelihoodProduct s rate exposure k := by
  exact
    exists_iIndepFun_poisson_count_joint_real
      rate h_rate exposure h_exposure s

/--
Finite incident-family primitive construction in collapsed Theorem 1 form:
the joint count-event likelihood over the finite incident set is a
rate-independent residual times one total-count Poisson PMF.
Source status: Lean-checked paper-facing row.
-/
theorem theorem1_exists_independent_poisson_count_family_collapsed
    {Incident : Type u}
    (rate : ℝ) (h_rate : 0 ≤ rate)
    (exposure : Incident → ℝ)
    (h_exposure : ∀ i, 0 ≤ exposure i)
    (s : Finset Incident)
    (h_totalExposure : totalExposure s exposure ≠ 0) :
    ∃ Ω : Type u, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω,
      ∃ X : Incident → Ω → ℕ,
        (∀ i, Measurable (X i)) ∧
        (∀ i,
          ProbabilityTheory.HasLaw
            (X i)
            (ProbabilityTheory.poissonMeasure
              (rateExposureParam rate (exposure i)
                (mul_nonneg h_rate (h_exposure i)))) P) ∧
        ProbabilityTheory.iIndepFun X P ∧ IsProbabilityMeasure P ∧
        ∀ k : Incident → ℕ,
          P.real (⋂ i ∈ s, {ω : Ω | X i ω = k i}) =
            (countLikelihoodProductResidual s exposure k *
                ((totalCount s k).factorial : ℝ) /
                  (totalExposure s exposure) ^ totalCount s k) *
              countLikelihood rate (totalExposure s exposure)
                (totalCount s k) := by
  exact
    exists_iIndepFun_poisson_count_joint_residual_real
      rate h_rate exposure h_exposure s h_totalExposure

/--
Finite incident-family primitive construction in collapsed Theorem 1 form,
with nonzero total exposure derived from one positive selected exposure.
Source status: Lean-checked paper-facing row.
-/
theorem theorem1_exists_independent_poisson_count_family_collapsed_of_exists_pos_exposure
    {Incident : Type u}
    (rate : ℝ) (h_rate : 0 ≤ rate)
    (exposure : Incident → ℝ)
    (h_exposure : ∀ i, 0 ≤ exposure i)
    (s : Finset Incident)
    (h_exists : ∃ i ∈ s, 0 < exposure i) :
    ∃ Ω : Type u, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω,
      ∃ X : Incident → Ω → ℕ,
        (∀ i, Measurable (X i)) ∧
        (∀ i,
          ProbabilityTheory.HasLaw
            (X i)
            (ProbabilityTheory.poissonMeasure
              (rateExposureParam rate (exposure i)
                (mul_nonneg h_rate (h_exposure i)))) P) ∧
        ProbabilityTheory.iIndepFun X P ∧ IsProbabilityMeasure P ∧
        ∀ k : Incident → ℕ,
          P.real (⋂ i ∈ s, {ω : Ω | X i ω = k i}) =
            (countLikelihoodProductResidual s exposure k *
                ((totalCount s k).factorial : ℝ) /
                  (totalExposure s exposure) ^ totalCount s k) *
              sourcePoissonPMF rate (totalExposure s exposure)
                (totalCount s k) := by
  simpa [sourcePoissonPMF] using
    exists_iIndepFun_poisson_count_joint_residual_real_of_exists_pos_exposure
      rate h_rate exposure h_exposure s h_exists

/--
Finite incident-family primitive construction as a reusable certificate:
independent Poisson counts exist for the incident family, and their joint
likelihood over the finite incident set is the product of incident PMFs.
Source status: Lean-checked paper-facing row.
-/
theorem theorem1_exists_independent_poisson_count_family_certificate_product
    {Incident : Type u}
    (rate : ℝ) (h_rate : 0 ≤ rate)
    (exposure : Incident → ℝ)
    (h_exposure : ∀ i, 0 ≤ exposure i)
    (s : Finset Incident) :
    ∃ Ω : Type u, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω,
      ∃ H : FinitePoissonCountFamily Ω P Incident rate exposure,
        ∀ k : Incident → ℕ,
          P.real (⋂ i ∈ s, {ω : Ω | H.count i ω = k i}) =
            countLikelihoodProduct s rate exposure k := by
  exact
    exists_finitePoissonCountFamily_joint_real
      rate h_rate exposure h_exposure s

/--
Finite incident-family primitive construction as a reusable certificate in
the collapsed Theorem 1 form: the joint count-event likelihood is a
rate-independent residual times one total-count source Poisson PMF.
Source status: Lean-checked paper-facing row.
-/
theorem theorem1_exists_independent_poisson_count_family_certificate_collapsed
    {Incident : Type u}
    (rate : ℝ) (h_rate : 0 ≤ rate)
    (exposure : Incident → ℝ)
    (h_exposure : ∀ i, 0 ≤ exposure i)
    (s : Finset Incident)
    (h_totalExposure : totalExposure s exposure ≠ 0) :
    ∃ Ω : Type u, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω,
      ∃ H : FinitePoissonCountFamily Ω P Incident rate exposure,
        ∀ k : Incident → ℕ,
          P.real (⋂ i ∈ s, {ω : Ω | H.count i ω = k i}) =
            (countLikelihoodProductResidual s exposure k *
                ((totalCount s k).factorial : ℝ) /
                  (totalExposure s exposure) ^ totalCount s k) *
              sourcePoissonPMF rate (totalExposure s exposure)
                (totalCount s k) := by
  simpa [sourcePoissonPMF] using
    exists_finitePoissonCountFamily_joint_residual_real
      rate h_rate exposure h_exposure s h_totalExposure

/--
Finite incident-family primitive construction as a reusable certificate in the
collapsed Theorem 1 form, with nonzero total exposure derived from one
positive selected exposure.
Source status: Lean-checked paper-facing row.
-/
theorem theorem1_exists_independent_poisson_count_family_certificate_collapsed_of_exists_pos_exposure
    {Incident : Type u}
    (rate : ℝ) (h_rate : 0 ≤ rate)
    (exposure : Incident → ℝ)
    (h_exposure : ∀ i, 0 ≤ exposure i)
    (s : Finset Incident)
    (h_exists : ∃ i ∈ s, 0 < exposure i) :
    ∃ Ω : Type u, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω,
      ∃ H : FinitePoissonCountFamily Ω P Incident rate exposure,
        ∀ k : Incident → ℕ,
          P.real (⋂ i ∈ s, {ω : Ω | H.count i ω = k i}) =
            (countLikelihoodProductResidual s exposure k *
                ((totalCount s k).factorial : ℝ) /
                  (totalExposure s exposure) ^ totalCount s k) *
              sourcePoissonPMF rate (totalExposure s exposure)
                (totalCount s k) := by
  simpa [sourcePoissonPMF] using
    exists_finitePoissonCountFamily_joint_residual_real_of_exists_pos_exposure
      rate h_rate exposure h_exposure s h_exists

/--
Finite incident-family primitive construction in total-count form: independent
Poisson counts exist for the incident family, and the finite incident-set total
count has the source Poisson PMF at total exposure.
Source status: Lean-checked paper-facing row.
-/
theorem theorem1_exists_independent_poisson_count_family_certificate_total_count
    {Incident : Type u} [DecidableEq Incident]
    (rate : ℝ) (h_rate : 0 ≤ rate)
    (exposure : Incident → ℝ)
    (h_exposure : ∀ i, 0 ≤ exposure i)
    (s : Finset Incident) :
    ∃ Ω : Type u, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω,
      ∃ H : FinitePoissonCountFamily Ω P Incident rate exposure,
        ∀ n : ℕ,
          P.real {ω : Ω | (∑ i ∈ s, H.count i ω) = n} =
            sourcePoissonPMF rate (totalExposure s exposure) n := by
  simpa [sourcePoissonPMF] using
    exists_finitePoissonCountFamily_total_count_real
      rate h_rate exposure h_exposure s

/--
Finite exposure/count-family MLE score equation with the denominator justified
from nonnegative exposures and one positive selected exposure.
Source status: Lean-checked paper-facing row.
-/
theorem theorem1_finite_exposure_count_family_mle_score_equation_of_exists_pos_exposure
    {Incident : Type u}
    (exposure : Incident → ℝ) (count : Incident → ℕ)
    (h_exposure : ∀ i, 0 ≤ exposure i)
    (s : Finset Incident)
    (h_exists : ∃ i ∈ s, 0 < exposure i)
    (hcount : totalCount s count ≠ 0) :
    poissonRateScore (totalCount s count) (totalExposure s exposure)
        (mleRate (totalCount s count) (totalExposure s exposure)) = 0 := by
  exact
    equation3_mle_score_equation
      (totalCount := totalCount s count)
      (totalExposure := totalExposure s exposure)
      hcount
      (ne_of_gt
        (totalExposure_pos_of_exists_pos s exposure
          (fun i _hi => h_exposure i) h_exists))

/--
Finite-dimensional primitive existence for adjacent Poisson increments:
for any monotone finite endpoint timeline and nonnegative rate, there is a
probability space carrying independent Poisson increment counts whose joint
event likelihood is the product of the per-window Poisson PMFs.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_exists_adjacent_interval_count_product_schedule
    (rate : ℝ) (h_rate : 0 ≤ rate)
    {n : ℕ} (t : Fin (n + 1) → ℝ) (ht : Monotone t) :
    ∃ Ω : Type, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω,
      ∃ X : Fin n → Ω → ℕ,
        (∀ i, Measurable (X i)) ∧
        (∀ i,
          ProbabilityTheory.HasLaw
            (X i)
            (ProbabilityTheory.poissonMeasure
              (rateExposureParam rate (t i.succ - t i.castSucc)
                (mul_nonneg h_rate
                  (sub_nonneg.mpr (ht (Fin.castSucc_le_succ i)))))) P) ∧
        ProbabilityTheory.iIndepFun X P ∧ IsProbabilityMeasure P ∧
        ∀ k : Fin n → ℕ,
          P.real (⋂ i ∈ (Finset.univ : Finset (Fin n)),
              {ω : Ω | X i ω = k i}) =
            countLikelihoodProduct (Finset.univ : Finset (Fin n)) rate
              (fun i => t i.succ - t i.castSucc) k := by
  exact
    exists_iIndepFun_poisson_adjacent_interval_count_joint_real_fin
      rate h_rate t ht

/--
Finite-dimensional primitive counting-process construction: for any monotone
finite endpoint timeline and nonnegative rate, there is a probability space
carrying a cumulative endpoint count process that starts at zero, has monotone
sample paths, has independent Poisson adjacent increments, and satisfies the
product-PMF joint likelihood formula for those increments.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_exists_finite_schedule_counting_process
    (rate : ℝ) (h_rate : 0 ≤ rate)
    {n : ℕ} (t : Fin (n + 1) → ℝ) (ht : Monotone t) :
    ∃ Ω : Type, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω,
      ∃ N : Fin (n + 1) → Ω → ℕ,
        (∀ ω, N 0 ω = 0) ∧
        (∀ ω, Monotone fun j : Fin (n + 1) => N j ω) ∧
        (∀ i,
          ProbabilityTheory.HasLaw
            (fun ω => N i.succ ω - N i.castSucc ω)
            (ProbabilityTheory.poissonMeasure
              (rateExposureParam rate (t i.succ - t i.castSucc)
                (mul_nonneg h_rate
                  (sub_nonneg.mpr (ht (Fin.castSucc_le_succ i)))))) P) ∧
        ProbabilityTheory.iIndepFun
          (fun i : Fin n => fun ω => N i.succ ω - N i.castSucc ω) P ∧
        IsProbabilityMeasure P ∧
        ∀ k : Fin n → ℕ,
          P.real (⋂ i ∈ (Finset.univ : Finset (Fin n)),
              {ω : Ω | N i.succ ω - N i.castSucc ω = k i}) =
            countLikelihoodProduct (Finset.univ : Finset (Fin n)) rate
              (fun i => t i.succ - t i.castSucc) k := by
  exact exists_finiteSchedulePoissonCountingProcess_fin rate h_rate t ht

/--
One-window finite-schedule count law: in a two-endpoint schedule, the final
endpoint count has the Poisson PMF for the endpoint exposure. This is derived
from the adjacent increment law and zero-start path field.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_one_window_schedule_endpoint_count_pmf
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {rate : ℝ} {t : Fin 2 → ℝ}
    (H : FiniteSchedulePoissonCountingProcess Ω P 1 rate t)
    (k : ℕ) :
    P.real {ω : Ω | H.count (Fin.last 1) ω = k} =
      sourcePoissonPMF rate (t (Fin.last 1) - t 0) k := by
  simpa [sourcePoissonPMF] using H.count_last_prob_one k

/--
Two-window finite-schedule count law: in a three-endpoint schedule, the final
endpoint count has the Poisson PMF for the total endpoint exposure. This is
derived from the product joint law for the two adjacent increments and the
finite event partition over all split counts.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_two_window_schedule_endpoint_count_pmf
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {rate : ℝ} {t : Fin 3 → ℝ}
    (H : FiniteSchedulePoissonCountingProcess Ω P 2 rate t)
    (k : ℕ) :
    P.real {ω : Ω | H.count (Fin.last 2) ω = k} =
      sourcePoissonPMF rate (t (Fin.last 2) - t 0) k := by
  simpa [sourcePoissonPMF] using H.count_last_prob_two k

/--
Arbitrary finite-schedule count law: in any finite monotone endpoint schedule,
the final endpoint count has the Poisson PMF for the total endpoint exposure.
This is derived by summing the independent adjacent-increment joint law over
all finite count vectors with the requested total count.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_finite_schedule_final_endpoint_count_pmf
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {n : ℕ} {rate : ℝ} {t : Fin (n + 1) → ℝ}
    (H : FiniteSchedulePoissonCountingProcess Ω P n rate t)
    (k : ℕ) :
    P.real {ω : Ω | H.count (Fin.last n) ω = k} =
      sourcePoissonPMF rate (t (Fin.last n) - t 0) k := by
  simpa [sourcePoissonPMF] using H.count_last_prob k

/--
Observation-window finite-schedule construction: every deterministic
observation window and nonnegative rate admits a two-endpoint finite Poisson
counting-process certificate whose final endpoint count has the source
Poisson PMF for the window exposure.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_exists_observation_window_counting_process_endpoint_pmf
    (rate : ℝ) (h_rate : 0 ≤ rate) (W : ObservationWindow) :
    ∃ Ω : Type, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω,
      ∃ H : FiniteSchedulePoissonCountingProcess Ω P 1 rate
          (observationWindowEndpointTimeline W),
        ∀ k : ℕ,
          P.real {ω : Ω | H.count (Fin.last 1) ω = k} =
            sourcePoissonPMF rate W.exposure k := by
  simpa [sourcePoissonPMF] using
    exists_finiteSchedulePoissonCountingProcess_observationWindow
      rate h_rate W

/--
Two-window finite-schedule construction with endpoint PMF: every monotone
three-endpoint schedule and nonnegative rate admits a finite Poisson counting
process whose final endpoint count has the source Poisson PMF for the total
endpoint exposure.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_exists_two_window_counting_process_endpoint_pmf
    (rate : ℝ) (h_rate : 0 ≤ rate)
    (t : Fin 3 → ℝ) (ht : Monotone t) :
    ∃ Ω : Type, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω,
      ∃ H : FiniteSchedulePoissonCountingProcess Ω P 2 rate t,
        ∀ k : ℕ,
          P.real {ω : Ω | H.count (Fin.last 2) ω = k} =
            sourcePoissonPMF rate (t (Fin.last 2) - t 0) k := by
  rcases exists_finiteSchedulePoissonCountingProcess rate h_rate t ht with
    ⟨Ω, mΩ, P, H, _⟩
  exact ⟨Ω, mΩ, P, H,
    fun k => by simpa [sourcePoissonPMF] using H.count_last_prob_two k⟩

/--
Arbitrary finite-schedule construction with final endpoint PMF: every monotone
finite endpoint schedule and nonnegative rate admits a finite Poisson counting
process whose final endpoint count has the source Poisson PMF for the total
endpoint exposure.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_exists_finite_schedule_counting_process_final_endpoint_pmf
    (rate : ℝ) (h_rate : 0 ≤ rate)
    {n : ℕ} (t : Fin (n + 1) → ℝ) (ht : Monotone t) :
    ∃ Ω : Type, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω,
      ∃ H : FiniteSchedulePoissonCountingProcess Ω P n rate t,
        ∀ k : ℕ,
          P.real {ω : Ω | H.count (Fin.last n) ω = k} =
            sourcePoissonPMF rate (t (Fin.last n) - t 0) k := by
  rcases exists_finiteSchedulePoissonCountingProcess rate h_rate t ht with
    ⟨Ω, mΩ, P, H, _⟩
  exact ⟨Ω, mΩ, P, H,
    fun k => by simpa [sourcePoissonPMF] using H.count_last_prob k⟩

/--
Finite-schedule subset-total PMF: any finite subset of adjacent increments in
a finite schedule has the source Poisson PMF at the subset's total exposure.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_finite_schedule_adjacent_increment_subset_total_pmf
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {n : ℕ} {rate : ℝ} {t : Fin (n + 1) → ℝ}
    (H : FiniteSchedulePoissonCountingProcess Ω P n rate t)
    (s : Finset (Fin n)) (k : ℕ) :
    P.real {ω : Ω | (∑ i ∈ s, H.adjacentIncrement i ω) = k} =
      sourcePoissonPMF rate
        (totalExposure s (fun i => t i.succ - t i.castSucc)) k := by
  simpa [sourcePoissonPMF] using
    H.adjacentIncrement_total_real_eq_countLikelihood_finset s k

/--
Constructed finite-schedule subset-total PMF: every monotone finite endpoint
schedule and nonnegative rate admits a finite Poisson counting process whose
arbitrary adjacent-increment subset totals have the source Poisson PMF at the
corresponding subset exposure.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_exists_finite_schedule_counting_process_subset_total_pmf
    (rate : ℝ) (h_rate : 0 ≤ rate)
    {n : ℕ} (t : Fin (n + 1) → ℝ) (ht : Monotone t)
    (s : Finset (Fin n)) :
    ∃ Ω : Type, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω,
      ∃ H : FiniteSchedulePoissonCountingProcess Ω P n rate t,
        ∀ k : ℕ,
          P.real {ω : Ω | (∑ i ∈ s, H.adjacentIncrement i ω) = k} =
            sourcePoissonPMF rate
              (totalExposure s (fun i => t i.succ - t i.castSucc)) k := by
  rcases exists_finiteSchedulePoissonCountingProcess rate h_rate t ht with
    ⟨Ω, mΩ, P, H, _⟩
  exact ⟨Ω, mΩ, P, H,
    fun k =>
      theorem2_finite_schedule_adjacent_increment_subset_total_pmf H s k⟩

/--
Finite-dimensional primitive counting-process construction in collapsed
Theorem 1 form: if the endpoint timeline has positive total span, the
constructed finite count process satisfies the residual times total-count
Poisson PMF likelihood formula for adjacent increment events.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_exists_finite_schedule_counting_process_endpoint_pmf
    (rate : ℝ) (h_rate : 0 ≤ rate)
    {n : ℕ} (t : Fin (n + 1) → ℝ) (ht : Monotone t)
    (h_endpoint : t 0 < t (Fin.last n)) :
    ∃ Ω : Type, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω,
      ∃ N : Fin (n + 1) → Ω → ℕ,
        (∀ ω, N 0 ω = 0) ∧
        (∀ ω, Monotone fun j : Fin (n + 1) => N j ω) ∧
        (∀ i,
          ProbabilityTheory.HasLaw
            (fun ω => N i.succ ω - N i.castSucc ω)
            (ProbabilityTheory.poissonMeasure
              (rateExposureParam rate (t i.succ - t i.castSucc)
                (mul_nonneg h_rate
                  (sub_nonneg.mpr (ht (Fin.castSucc_le_succ i)))))) P) ∧
        ProbabilityTheory.iIndepFun
          (fun i : Fin n => fun ω => N i.succ ω - N i.castSucc ω) P ∧
        IsProbabilityMeasure P ∧
        ∀ k : Fin n → ℕ,
          P.real (⋂ i ∈ (Finset.univ : Finset (Fin n)),
              {ω : Ω | N i.succ ω - N i.castSucc ω = k i}) =
            (countLikelihoodProductResidual (Finset.univ : Finset (Fin n))
                (fun i => t i.succ - t i.castSucc) k *
                ((totalCount (Finset.univ : Finset (Fin n)) k).factorial : ℝ) /
                  (t (Fin.last n) - t 0) ^
                    totalCount (Finset.univ : Finset (Fin n)) k) *
              countLikelihood rate
                (t (Fin.last n) - t 0)
                (totalCount (Finset.univ : Finset (Fin n)) k) := by
  exact
    exists_finiteSchedulePoissonCountingProcess_endpoint_fin
      rate h_rate t ht h_endpoint

/--
Certificate version of the finite-dimensional primitive counting-process
construction in collapsed Theorem 1 form.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_exists_finite_schedule_counting_process_certificate_endpoint_pmf
    (rate : ℝ) (h_rate : 0 ≤ rate)
    {n : ℕ} (t : Fin (n + 1) → ℝ) (ht : Monotone t)
    (h_endpoint : t 0 < t (Fin.last n)) :
    ∃ Ω : Type, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω,
      ∃ H : FiniteSchedulePoissonCountingProcess Ω P n rate t,
        ∀ k : Fin n → ℕ,
          P.real (⋂ i ∈ (Finset.univ : Finset (Fin n)),
              {ω : Ω | H.adjacentIncrement i ω = k i}) =
            (countLikelihoodProductResidual (Finset.univ : Finset (Fin n))
                (fun i => t i.succ - t i.castSucc) k *
                ((totalCount (Finset.univ : Finset (Fin n)) k).factorial : ℝ) /
                  (t (Fin.last n) - t 0) ^
                    totalCount (Finset.univ : Finset (Fin n)) k) *
              countLikelihood rate
                (t (Fin.last n) - t 0)
                (totalCount (Finset.univ : Finset (Fin n)) k) := by
  exact
    exists_finiteSchedulePoissonCountingProcess_endpoint
      rate h_rate t ht h_endpoint

/--
Finite-dimensional primitive counting-process construction in collapsed
Theorem 1 form, deriving nonzero total exposure from one strictly positive
adjacent schedule interval.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_exists_finite_schedule_counting_process_total_pmf_of_exists_pos_exposure
    (rate : ℝ) (h_rate : 0 ≤ rate)
    {n : ℕ} (t : Fin (n + 1) → ℝ) (ht : Monotone t)
    (h_exists :
      ∃ i ∈ (Finset.univ : Finset (Fin n)),
        0 < t i.succ - t i.castSucc) :
    ∃ Ω : Type, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω,
      ∃ N : Fin (n + 1) → Ω → ℕ,
        (∀ ω, N 0 ω = 0) ∧
        (∀ ω, Monotone fun j : Fin (n + 1) => N j ω) ∧
        (∀ i,
          ProbabilityTheory.HasLaw
            (fun ω => N i.succ ω - N i.castSucc ω)
            (ProbabilityTheory.poissonMeasure
              (rateExposureParam rate (t i.succ - t i.castSucc)
                (mul_nonneg h_rate
                  (sub_nonneg.mpr (ht (Fin.castSucc_le_succ i)))))) P) ∧
        ProbabilityTheory.iIndepFun
          (fun i : Fin n => fun ω => N i.succ ω - N i.castSucc ω) P ∧
        IsProbabilityMeasure P ∧
        ∀ k : Fin n → ℕ,
          P.real (⋂ i ∈ (Finset.univ : Finset (Fin n)),
              {ω : Ω | N i.succ ω - N i.castSucc ω = k i}) =
            (countLikelihoodProductResidual (Finset.univ : Finset (Fin n))
                (fun i => t i.succ - t i.castSucc) k *
                ((totalCount (Finset.univ : Finset (Fin n)) k).factorial : ℝ) /
                  (totalExposure (Finset.univ : Finset (Fin n))
                    (fun i => t i.succ - t i.castSucc)) ^
                    totalCount (Finset.univ : Finset (Fin n)) k) *
              sourcePoissonPMF rate
                (totalExposure (Finset.univ : Finset (Fin n))
                  (fun i => t i.succ - t i.castSucc))
                (totalCount (Finset.univ : Finset (Fin n)) k) := by
  simpa [sourcePoissonPMF] using
    exists_finiteSchedulePoissonCountingProcess_total_fin_of_exists_pos_exposure
      rate h_rate t ht h_exists

/--
Certificate version of the finite-dimensional primitive counting-process
construction with one strictly positive adjacent schedule interval.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_exists_finite_schedule_counting_process_certificate_total_pmf_of_exists_pos_exposure
    (rate : ℝ) (h_rate : 0 ≤ rate)
    {n : ℕ} (t : Fin (n + 1) → ℝ) (ht : Monotone t)
    (h_exists :
      ∃ i ∈ (Finset.univ : Finset (Fin n)),
        0 < t i.succ - t i.castSucc) :
    ∃ Ω : Type, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω,
      ∃ H : FiniteSchedulePoissonCountingProcess Ω P n rate t,
        ∀ k : Fin n → ℕ,
          P.real (⋂ i ∈ (Finset.univ : Finset (Fin n)),
              {ω : Ω | H.adjacentIncrement i ω = k i}) =
            (countLikelihoodProductResidual (Finset.univ : Finset (Fin n))
                (fun i => t i.succ - t i.castSucc) k *
                ((totalCount (Finset.univ : Finset (Fin n)) k).factorial : ℝ) /
                  (totalExposure (Finset.univ : Finset (Fin n))
                    (fun i => t i.succ - t i.castSucc)) ^
                    totalCount (Finset.univ : Finset (Fin n)) k) *
              sourcePoissonPMF rate
                (totalExposure (Finset.univ : Finset (Fin n))
                  (fun i => t i.succ - t i.castSucc))
                (totalCount (Finset.univ : Finset (Fin n)) k) := by
  simpa [sourcePoissonPMF] using
    exists_finiteSchedulePoissonCountingProcess_total_of_exists_pos_exposure
      rate h_rate t ht h_exists

/--
Finite-schedule Theorem 1 shape: any finite endpoint count process whose
adjacent increment events have the product Poisson likelihood also has the
collapsed endpoint-exposure likelihood form, with a rate-independent residual
and one total-count Poisson PMF.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_finite_schedule_adjacent_count_endpoint_pmf
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {n : ℕ} (N : Fin (n + 1) → Ω → ℕ)
    (rate : ℝ) (t : Fin (n + 1) → ℝ)
    (hJoint : ∀ k : Fin n → ℕ,
      P.real (⋂ i ∈ (Finset.univ : Finset (Fin n)),
          {ω : Ω | N i.succ ω - N i.castSucc ω = k i}) =
        countLikelihoodProduct (Finset.univ : Finset (Fin n)) rate
          (fun i => t i.succ - t i.castSucc) k)
    (h_endpoint : t 0 < t (Fin.last n))
    (k : Fin n → ℕ) :
    P.real (⋂ i ∈ (Finset.univ : Finset (Fin n)),
        {ω : Ω | N i.succ ω - N i.castSucc ω = k i}) =
      (countLikelihoodProductResidual (Finset.univ : Finset (Fin n))
          (fun i => t i.succ - t i.castSucc) k *
          ((totalCount (Finset.univ : Finset (Fin n)) k).factorial : ℝ) /
            (t (Fin.last n) - t 0) ^
              totalCount (Finset.univ : Finset (Fin n)) k) *
        countLikelihood rate
          (t (Fin.last n) - t 0)
          (totalCount (Finset.univ : Finset (Fin n)) k) := by
  exact
    finiteScheduleAdjacentCount_joint_real_eq_residual_countLikelihood_endpoint
      N rate t hJoint h_endpoint k

/--
Finite-schedule Theorem 1 shape with nonzero total exposure derived from one
strictly positive adjacent schedule interval.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_finite_schedule_adjacent_count_total_pmf_of_exists_pos_exposure
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {n : ℕ} (N : Fin (n + 1) → Ω → ℕ)
    (rate : ℝ) (t : Fin (n + 1) → ℝ) (ht : Monotone t)
    (hJoint : ∀ k : Fin n → ℕ,
      P.real (⋂ i ∈ (Finset.univ : Finset (Fin n)),
          {ω : Ω | N i.succ ω - N i.castSucc ω = k i}) =
        countLikelihoodProduct (Finset.univ : Finset (Fin n)) rate
          (fun i => t i.succ - t i.castSucc) k)
    (h_exists :
      ∃ i ∈ (Finset.univ : Finset (Fin n)),
        0 < t i.succ - t i.castSucc)
    (k : Fin n → ℕ) :
    P.real (⋂ i ∈ (Finset.univ : Finset (Fin n)),
        {ω : Ω | N i.succ ω - N i.castSucc ω = k i}) =
      (countLikelihoodProductResidual (Finset.univ : Finset (Fin n))
          (fun i => t i.succ - t i.castSucc) k *
          ((totalCount (Finset.univ : Finset (Fin n)) k).factorial : ℝ) /
            (totalExposure (Finset.univ : Finset (Fin n))
              (fun i => t i.succ - t i.castSucc)) ^
                totalCount (Finset.univ : Finset (Fin n)) k) *
        sourcePoissonPMF rate
          (totalExposure (Finset.univ : Finset (Fin n))
            (fun i => t i.succ - t i.castSucc))
          (totalCount (Finset.univ : Finset (Fin n)) k) := by
  simpa [sourcePoissonPMF] using
    finiteScheduleAdjacentCount_joint_real_eq_residual_countLikelihood_total_of_exists_pos_exposure
      N rate t ht hJoint h_exists k

/--
Finite-dimensional adjacent interval-count law from primitive source semantics,
collapsed to the source Poisson PMF at the total endpoint exposure.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_adjacent_interval_counts_endpoint_pmf_from_source_semantics
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    (S : theorem2_poisson_process_and_condition_semantics Ω P)
    {n : ℕ} {t : Fin (n + 1) → ℝ} (ht : Monotone t)
    (k : Fin n → ℕ)
    (h_endpoint : t 0 < t (Fin.last n)) :
    P.real (⋂ i ∈ (Finset.univ : Finset (Fin n)),
        {ω : Ω |
          S.countProcess.intervalCount (t i.castSucc) (t i.succ) ω =
            k i}) =
      (countLikelihoodProductResidual (Finset.univ : Finset (Fin n))
          (fun i => t i.succ - t i.castSucc) k *
          ((totalCount (Finset.univ : Finset (Fin n)) k).factorial : ℝ) /
            (t (Fin.last n) - t 0) ^
              totalCount (Finset.univ : Finset (Fin n)) k) *
        sourcePoissonPMF S.rate
          (t (Fin.last n) - t 0)
          (totalCount (Finset.univ : Finset (Fin n)) k) := by
  exact
    theorem2_poisson_process_and_condition_semantics.intervalCount_joint_real_eq_residual_sourcePoissonPMF_endpoint_fin
      S ht k h_endpoint

/--
Finite-dimensional adjacent interval-count law from primitive source semantics,
collapsed to the source Poisson PMF at total exposure. The nonzero denominator
is derived from one strictly positive adjacent source window.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_adjacent_interval_counts_total_pmf_from_source_semantics_of_exists_pos_exposure
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    (S : theorem2_poisson_process_and_condition_semantics Ω P)
    {n : ℕ} {t : Fin (n + 1) → ℝ} (ht : Monotone t)
    (k : Fin n → ℕ)
    (h_exists :
      ∃ i ∈ (Finset.univ : Finset (Fin n)),
        0 < t i.succ - t i.castSucc) :
    P.real (⋂ i ∈ (Finset.univ : Finset (Fin n)),
        {ω : Ω |
          S.countProcess.intervalCount (t i.castSucc) (t i.succ) ω =
            k i}) =
      (countLikelihoodProductResidual (Finset.univ : Finset (Fin n))
          (fun i => t i.succ - t i.castSucc) k *
          ((totalCount (Finset.univ : Finset (Fin n)) k).factorial : ℝ) /
            (totalExposure (Finset.univ : Finset (Fin n))
              (fun i => t i.succ - t i.castSucc)) ^
                totalCount (Finset.univ : Finset (Fin n)) k) *
        sourcePoissonPMF S.rate
          (totalExposure (Finset.univ : Finset (Fin n))
            (fun i => t i.succ - t i.castSucc))
          (totalCount (Finset.univ : Finset (Fin n)) k) := by
  exact
    theorem2_poisson_process_and_condition_semantics.intervalCount_joint_real_eq_residual_sourcePoissonPMF_total_fin_of_exists_pos_exposure
      S ht k h_exists

/--
Finite-dimensional adjacent interval-count law constructed directly from
mathlib Poisson increment laws and the paper's rate-indexed Condition 1/2
source semantics, collapsed to the source Poisson PMF at endpoint exposure.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_adjacent_interval_counts_endpoint_pmf_from_poisson_increment_laws_and_condition_semantics
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    (H : HomogeneousPoissonCountingProcessByLaw Ω P)
    (G : Theorem2ConditionFunctionSemantics)
    {n : ℕ} {t : Fin (n + 1) → ℝ} (ht : Monotone t)
    (k : Fin n → ℕ)
    (h_endpoint : t 0 < t (Fin.last n)) :
    P.real (⋂ i ∈ (Finset.univ : Finset (Fin n)),
        {ω : Ω |
          H.intervalCount (t i.castSucc) (t i.succ) ω =
            k i}) =
      (countLikelihoodProductResidual (Finset.univ : Finset (Fin n))
          (fun i => t i.succ - t i.castSucc) k *
          ((totalCount (Finset.univ : Finset (Fin n)) k).factorial : ℝ) /
            (t (Fin.last n) - t 0) ^
              totalCount (Finset.univ : Finset (Fin n)) k) *
        sourcePoissonPMF H.rate
          (t (Fin.last n) - t 0)
          (totalCount (Finset.univ : Finset (Fin n)) k) := by
  simpa [theorem2_poisson_process_and_condition_semantics.rate] using
    theorem2_adjacent_interval_counts_endpoint_pmf_from_source_semantics
      (theorem2_poisson_process_and_condition_semantics.fromPoissonIncrementLawsAndConditionSemantics
        H G)
      ht k h_endpoint

/--
Finite-dimensional adjacent interval-count law constructed directly from
mathlib Poisson increment laws and the paper's rate-indexed Condition 1/2
source semantics, with nonzero total exposure derived from one positive
adjacent interval.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_adjacent_interval_counts_total_pmf_from_poisson_increment_laws_and_condition_semantics_of_exists_pos_exposure
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    (H : HomogeneousPoissonCountingProcessByLaw Ω P)
    (G : Theorem2ConditionFunctionSemantics)
    {n : ℕ} {t : Fin (n + 1) → ℝ} (ht : Monotone t)
    (k : Fin n → ℕ)
    (h_exists :
      ∃ i ∈ (Finset.univ : Finset (Fin n)),
        0 < t i.succ - t i.castSucc) :
    P.real (⋂ i ∈ (Finset.univ : Finset (Fin n)),
        {ω : Ω |
          H.intervalCount (t i.castSucc) (t i.succ) ω =
            k i}) =
      (countLikelihoodProductResidual (Finset.univ : Finset (Fin n))
          (fun i => t i.succ - t i.castSucc) k *
          ((totalCount (Finset.univ : Finset (Fin n)) k).factorial : ℝ) /
            (totalExposure (Finset.univ : Finset (Fin n))
              (fun i => t i.succ - t i.castSucc)) ^
                totalCount (Finset.univ : Finset (Fin n)) k) *
        sourcePoissonPMF H.rate
          (totalExposure (Finset.univ : Finset (Fin n))
            (fun i => t i.succ - t i.castSucc))
          (totalCount (Finset.univ : Finset (Fin n)) k) := by
  simpa [theorem2_poisson_process_and_condition_semantics.rate] using
    theorem2_adjacent_interval_counts_total_pmf_from_source_semantics_of_exists_pos_exposure
      (theorem2_poisson_process_and_condition_semantics.fromPoissonIncrementLawsAndConditionSemantics
        H G)
      ht k h_exists

/--
Bundled source-assumption version of the adjacent interval-count PMF row.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_adjacent_interval_counts_total_pmf_from_process_law_cases_of_exists_pos_exposure
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    (A : assumption_theorem2_poisson_process_and_conditions Ω P)
    {n : ℕ} {t : Fin (n + 1) → ℝ} (ht : Monotone t)
    (k : Fin n → ℕ)
    (h_exists :
      ∃ i ∈ (Finset.univ : Finset (Fin n)),
        0 < t i.succ - t i.castSucc) :
    P.real (⋂ i ∈ (Finset.univ : Finset (Fin n)),
        {ω : Ω |
          A.countProcess.intervalCount (t i.castSucc) (t i.succ) ω =
            k i}) =
      (countLikelihoodProductResidual (Finset.univ : Finset (Fin n))
          (fun i => t i.succ - t i.castSucc) k *
          ((totalCount (Finset.univ : Finset (Fin n)) k).factorial : ℝ) /
            (totalExposure (Finset.univ : Finset (Fin n))
              (fun i => t i.succ - t i.castSucc)) ^
                totalCount (Finset.univ : Finset (Fin n)) k) *
        sourcePoissonPMF A.rate
          (totalExposure (Finset.univ : Finset (Fin n))
            (fun i => t i.succ - t i.castSucc))
          (totalCount (Finset.univ : Finset (Fin n)) k) := by
  exact
    assumption_theorem2_poisson_process_and_conditions.intervalCount_joint_real_eq_residual_sourcePoissonPMF_total_fin_of_exists_pos_exposure
      A ht k h_exists

/--
Formula-facing primitive-process factorization form. Prefer
`theorem1_likelihood_decomposition_from_poisson_increment_laws` when the
homogeneous Poisson process is available as distribution laws.
Source status: Lean-checked paper-facing row.
-/
theorem theorem1_likelihood_decomposition_from_primitive_poisson_process
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : HomogeneousPoissonCountingProcess Ω P)
    (K : Theorem2ConditionFunctions)
    (C : Theorem2ObservedWindowCase) :
    C.likelihoodFromCountingProcess K H =
      C.residualWith K * sourcePoissonPMF H.rate
        (C.exposureWith K) (C.countWith K) := by
  exact C.factorizationFromCountingProcess K H

/--
Bundled source-assumption likelihood factorization form.
Source status: Lean-checked paper-facing row.
-/
theorem theorem1_likelihood_decomposition
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (A : assumption_theorem2_poisson_process_and_conditions Ω P)
    (C : Theorem2ObservedWindowCase) :
    C.likelihood A =
      C.residual A * sourcePoissonPMF A.rate (C.exposure A) (C.count A) := by
  exact C.factorization_via_toSourceSemantics A

/--
Theorem 1 / Appendix Theorem 2 from source data assembled out of reusable
Poisson no-arrival and interarrival-tail kernels.
Source status: Lean-checked paper-facing row.
-/
theorem theorem1_likelihood_decomposition_from_process_source_data
    (D : Theorem2ProcessSourceData) (rate : ℝ) :
    D.likelihood rate =
      D.residual * sourcePoissonPMF rate D.exposure D.count := by
  exact theorem2_process_source_data_factorization D rate

/--
Appendix B.2 zero-report case from the paper's condition functions `g` and
`h_m`: the resulting source data factors into the zero-count Poisson PMF.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_zero_report_condition_functions_factorization
    (K : Theorem2ConditionFunctions) (baseCount : ℕ)
    (W : ObservationWindow) (rate : ℝ) :
    (K.zeroReportSourceDataFromWindow baseCount W).likelihood rate =
      (K.zeroReportSourceDataFromWindow baseCount W).residual *
        sourcePoissonPMF rate
          (K.zeroReportSourceDataFromWindow baseCount W).exposure
          (K.zeroReportSourceDataFromWindow baseCount W).count := by
  exact theorem2_process_source_data_factorization
    (K.zeroReportSourceDataFromWindow baseCount W) rate

/--
Appendix B.2 zero-report case directly from the rate-indexed Condition 1/2
source semantics: at the source rate, the visible `g` and `h_m` terms factor
into the zero-count Poisson PMF.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_zero_report_condition_semantics_formula_factorization
    (S : Theorem2ConditionFunctionSemantics) (baseCount : ℕ)
    (W : ObservationWindow) (rate : ℝ) :
    theorem2ZeroReportLikelihood
        (S.startDensityOfRate rate) (S.endDensityOfRate baseCount rate)
        rate W.exposure =
      theorem2ZeroReportResidual
          (S.startDensityOfRate rate) (S.endDensityOfRate baseCount rate) *
        sourcePoissonPMF rate W.exposure 0 := by
  exact theorem2_zero_report_case_factorization
    (S.startDensityOfRate rate) (S.endDensityOfRate baseCount rate)
    rate W.exposure

/--
Appendix B.2 zero-report source-data row directly from rate-indexed Condition
1/2 semantics.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_zero_report_condition_semantics_source_data_factorization
    (S : Theorem2ConditionFunctionSemantics) (baseCount : ℕ)
    (W : ObservationWindow) (rate : ℝ) :
    (S.zeroReportSourceDataFromWindowAtRate baseCount W rate).likelihood rate =
      (S.zeroReportSourceDataFromWindowAtRate baseCount W rate).residual *
        sourcePoissonPMF rate
          (S.zeroReportSourceDataFromWindowAtRate baseCount W rate).exposure
          (S.zeroReportSourceDataFromWindowAtRate baseCount W rate).count := by
  exact
    Theorem2ConditionFunctionSemantics.zeroReportSourceDataFromWindowAtRate_self_factorization
      S baseCount W rate

/--
Appendix B.2 one-report case from the paper's condition functions plus one
interarrival/no-arrival kernel.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_one_report_condition_functions_factorization
    (K : Theorem2ConditionFunctions) (baseCount : ℕ)
    {gap tail exposure rate : ℝ}
    (h_gap : 0 ≤ gap) (h_tail : 0 ≤ tail)
    (hexposure : gap + tail = exposure)
    (h_exposure : exposure ≠ 0) :
    (K.oneReportSourceData baseCount gap tail exposure
        hexposure h_exposure).likelihood rate =
      (K.oneReportSourceData baseCount gap tail exposure
          hexposure h_exposure).residual *
        sourcePoissonPMF rate
          (K.oneReportSourceData baseCount gap tail exposure
            hexposure h_exposure).exposure
          (K.oneReportSourceData baseCount gap tail exposure
            hexposure h_exposure).count := by
  exact theorem2_process_source_data_factorization
    (K.oneReportSourceData baseCount gap tail exposure
      hexposure h_exposure) rate

/--
Appendix B.2 one-report case from condition functions, with positive exposure
instead of a raw nonzero denominator premise.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_one_report_condition_functions_factorization_of_pos_exposure
    (K : Theorem2ConditionFunctions) (baseCount : ℕ)
    {gap tail exposure rate : ℝ}
    (h_gap : 0 ≤ gap) (h_tail : 0 ≤ tail)
    (hexposure : gap + tail = exposure)
    (h_exposure_pos : 0 < exposure) :
    (K.oneReportSourceData baseCount gap tail exposure
        hexposure (ne_of_gt h_exposure_pos)).likelihood rate =
      (K.oneReportSourceData baseCount gap tail exposure
          hexposure (ne_of_gt h_exposure_pos)).residual *
        sourcePoissonPMF rate
          (K.oneReportSourceData baseCount gap tail exposure
            hexposure (ne_of_gt h_exposure_pos)).exposure
          (K.oneReportSourceData baseCount gap tail exposure
            hexposure (ne_of_gt h_exposure_pos)).count := by
  exact theorem2_one_report_condition_functions_factorization
    K baseCount h_gap h_tail hexposure (ne_of_gt h_exposure_pos)

/--
Appendix B.2 one-report case directly from the rate-indexed Condition 1/2
source semantics after collecting the single interarrival/no-arrival kernel.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_one_report_condition_semantics_formula_factorization
    (S : Theorem2ConditionFunctionSemantics) (baseCount : ℕ)
    {rate exposure : ℝ} (h_exposure : exposure ≠ 0) :
    theorem2OneReportLikelihood
        (S.startDensityOfRate rate)
        (S.endDensityOfRate (baseCount + 1) rate)
        (S.survivalIntegralOfRate baseCount rate)
        rate exposure =
      (theorem2OneReportKernelResidual
          (S.startDensityOfRate rate)
          (S.endDensityOfRate (baseCount + 1) rate)
          (S.survivalIntegralOfRate baseCount rate) / exposure) *
        sourcePoissonPMF rate exposure 1 := by
  exact theorem2_one_report_case_factorization h_exposure

/--
Appendix B.2 one-report source-semantics formula with positive exposure.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_one_report_condition_semantics_formula_factorization_of_pos_exposure
    (S : Theorem2ConditionFunctionSemantics) (baseCount : ℕ)
    {rate exposure : ℝ} (h_exposure_pos : 0 < exposure) :
    theorem2OneReportLikelihood
        (S.startDensityOfRate rate)
        (S.endDensityOfRate (baseCount + 1) rate)
        (S.survivalIntegralOfRate baseCount rate)
        rate exposure =
      (theorem2OneReportKernelResidual
          (S.startDensityOfRate rate)
          (S.endDensityOfRate (baseCount + 1) rate)
          (S.survivalIntegralOfRate baseCount rate) / exposure) *
        sourcePoissonPMF rate exposure 1 := by
  exact theorem2_one_report_case_factorization_of_pos_exposure
    h_exposure_pos

/--
Appendix B.2 one-report source-data row directly from rate-indexed Condition
1/2 semantics.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_one_report_condition_semantics_source_data_factorization
    (S : Theorem2ConditionFunctionSemantics) (baseCount : ℕ)
    {gap tail exposure rate : ℝ}
    (hexposure : gap + tail = exposure)
    (h_exposure : exposure ≠ 0) :
    (S.oneReportSourceDataAtRate baseCount gap tail exposure
        hexposure h_exposure rate).likelihood rate =
      (S.oneReportSourceDataAtRate baseCount gap tail exposure
          hexposure h_exposure rate).residual *
        sourcePoissonPMF rate
          (S.oneReportSourceDataAtRate baseCount gap tail exposure
            hexposure h_exposure rate).exposure
          (S.oneReportSourceDataAtRate baseCount gap tail exposure
            hexposure h_exposure rate).count := by
  exact
    Theorem2ConditionFunctionSemantics.oneReportSourceDataAtRate_self_factorization
      S baseCount hexposure h_exposure

/--
Appendix B.2 one-report source-data row directly from rate-indexed Condition
1/2 semantics, with positive exposure.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_one_report_condition_semantics_source_data_factorization_of_pos_exposure
    (S : Theorem2ConditionFunctionSemantics) (baseCount : ℕ)
    {gap tail exposure rate : ℝ}
    (hexposure : gap + tail = exposure)
    (h_exposure_pos : 0 < exposure) :
    (S.oneReportSourceDataAtRate baseCount gap tail exposure
        hexposure (ne_of_gt h_exposure_pos) rate).likelihood rate =
      (S.oneReportSourceDataAtRate baseCount gap tail exposure
          hexposure (ne_of_gt h_exposure_pos) rate).residual *
        sourcePoissonPMF rate
          (S.oneReportSourceDataAtRate baseCount gap tail exposure
            hexposure (ne_of_gt h_exposure_pos) rate).exposure
          (S.oneReportSourceDataAtRate baseCount gap tail exposure
            hexposure (ne_of_gt h_exposure_pos) rate).count := by
  exact theorem2_one_report_condition_semantics_source_data_factorization
    S baseCount hexposure (ne_of_gt h_exposure_pos)

/--
Appendix B.2 one-report ordered-window source-data row directly from
rate-indexed Condition 1/2 semantics.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_one_report_condition_semantics_ordered_window_source_data_factorization
    (S : Theorem2ConditionFunctionSemantics) (baseCount : ℕ)
    (T : OrderedOneJumpWindow) (h_exposure : T.window.exposure ≠ 0)
    (rate : ℝ) :
    (S.oneReportSourceDataFromOrderedJumpWindowAtRate
        baseCount T h_exposure rate).likelihood rate =
      (S.oneReportSourceDataFromOrderedJumpWindowAtRate
          baseCount T h_exposure rate).residual *
        sourcePoissonPMF rate
          (S.oneReportSourceDataFromOrderedJumpWindowAtRate
            baseCount T h_exposure rate).exposure
          (S.oneReportSourceDataFromOrderedJumpWindowAtRate
            baseCount T h_exposure rate).count := by
  exact
    Theorem2ConditionFunctionSemantics.oneReportSourceDataFromOrderedJumpWindowAtRate_self_factorization
      S baseCount T h_exposure rate

/--
Appendix B.2 one-report ordered-window source-data row from rate-indexed
Condition 1/2 semantics, aligned with the derived rate-independent
condition-function source-data object.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_one_report_condition_semantics_ordered_window_source_data_factorization_via_condition_functions
    (S : Theorem2ConditionFunctionSemantics) (baseCount : ℕ)
    (T : OrderedOneJumpWindow) (h_exposure : T.window.exposure ≠ 0)
    (rate : ℝ) :
    (S.oneReportSourceDataFromOrderedJumpWindowAtRate
        baseCount T h_exposure rate).likelihood rate =
      (S.toConditionFunctions.oneReportSourceDataFromOrderedJumpWindow
          baseCount T h_exposure).residual *
        sourcePoissonPMF rate
          (S.toConditionFunctions.oneReportSourceDataFromOrderedJumpWindow
            baseCount T h_exposure).exposure
          (S.toConditionFunctions.oneReportSourceDataFromOrderedJumpWindow
            baseCount T h_exposure).count := by
  exact
    Theorem2ConditionFunctionSemantics.oneReportSourceDataFromOrderedJumpWindowAtRate_factorization
      S baseCount T h_exposure rate

/--
Appendix B.2 one-report ordered-window source-data row from rate-indexed
Condition 1/2 semantics, with nonzero exposure derived from positive window
exposure.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_one_report_condition_semantics_ordered_window_source_data_factorization_of_pos_exposure
    (S : Theorem2ConditionFunctionSemantics) (baseCount : ℕ)
    (T : OrderedOneJumpWindow) (h_exposure_pos : 0 < T.window.exposure)
    (rate : ℝ) :
    (S.oneReportSourceDataFromOrderedJumpWindowAtRate
        baseCount T (ne_of_gt h_exposure_pos) rate).likelihood rate =
      (S.toConditionFunctions.oneReportSourceDataFromOrderedJumpWindow
          baseCount T (ne_of_gt h_exposure_pos)).residual *
        sourcePoissonPMF rate
          (S.toConditionFunctions.oneReportSourceDataFromOrderedJumpWindow
            baseCount T (ne_of_gt h_exposure_pos)).exposure
          (S.toConditionFunctions.oneReportSourceDataFromOrderedJumpWindow
            baseCount T (ne_of_gt h_exposure_pos)).count := by
  exact
    Theorem2ConditionFunctionSemantics.oneReportSourceDataFromOrderedJumpWindowAtRate_factorization_of_pos_exposure
      S baseCount T h_exposure_pos rate

/--
Appendix B.2 one-report case from actual start, end, and observed first jump
times; the exposure identity is proved by arithmetic.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_one_report_jump_time_factorization
    (K : Theorem2ConditionFunctions) (baseCount : ℕ)
    {startTime endTime firstJumpTime rate : ℝ}
    (h_start_le_jump : startTime ≤ firstJumpTime)
    (h_jump_le_end : firstJumpTime ≤ endTime)
    (h_exposure : observationExposure startTime endTime ≠ 0) :
    (K.oneReportSourceDataFromJumpTime baseCount
        startTime endTime firstJumpTime h_exposure).likelihood rate =
      (K.oneReportSourceDataFromJumpTime baseCount
          startTime endTime firstJumpTime h_exposure).residual *
        sourcePoissonPMF rate
          (K.oneReportSourceDataFromJumpTime baseCount
            startTime endTime firstJumpTime h_exposure).exposure
          (K.oneReportSourceDataFromJumpTime baseCount
            startTime endTime firstJumpTime h_exposure).count := by
  exact theorem2_process_source_data_factorization
    (K.oneReportSourceDataFromJumpTime baseCount
      startTime endTime firstJumpTime h_exposure) rate

/--
Appendix B.2 one-report jump-time factorization with positive observation
exposure.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_one_report_jump_time_factorization_of_pos_exposure
    (K : Theorem2ConditionFunctions) (baseCount : ℕ)
    {startTime endTime firstJumpTime rate : ℝ}
    (h_start_le_jump : startTime ≤ firstJumpTime)
    (h_jump_le_end : firstJumpTime ≤ endTime)
    (h_exposure_pos : 0 < observationExposure startTime endTime) :
    (K.oneReportSourceDataFromJumpTime baseCount
        startTime endTime firstJumpTime
        (ne_of_gt h_exposure_pos)).likelihood rate =
      (K.oneReportSourceDataFromJumpTime baseCount
          startTime endTime firstJumpTime
          (ne_of_gt h_exposure_pos)).residual *
        sourcePoissonPMF rate
          (K.oneReportSourceDataFromJumpTime baseCount
            startTime endTime firstJumpTime
            (ne_of_gt h_exposure_pos)).exposure
          (K.oneReportSourceDataFromJumpTime baseCount
            startTime endTime firstJumpTime
            (ne_of_gt h_exposure_pos)).count := by
  exact theorem2_one_report_jump_time_factorization
    K baseCount h_start_le_jump h_jump_le_end (ne_of_gt h_exposure_pos)

/--
Appendix B.2 multi-report case from the paper's condition functions plus a
finite interarrival/no-arrival kernel.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_multi_report_condition_functions_factorization
    (K : Theorem2ConditionFunctions) (baseCount count : ℕ)
    (hcount : 1 < count)
    (gap : Fin count → ℝ) {tail exposure rate : ℝ}
    (h_gap : ∀ j : Fin count, 0 ≤ gap j) (h_tail : 0 ≤ tail)
    (hexposure : (∑ j : Fin count, gap j) + tail = exposure)
    (h_exposure : exposure ≠ 0) :
    (K.multiReportSourceData baseCount count hcount gap tail exposure
        hexposure h_exposure).likelihood rate =
      (K.multiReportSourceData baseCount count hcount gap tail exposure
          hexposure h_exposure).residual *
        sourcePoissonPMF rate
          (K.multiReportSourceData baseCount count hcount gap tail exposure
            hexposure h_exposure).exposure
          (K.multiReportSourceData baseCount count hcount gap tail exposure
            hexposure h_exposure).count := by
  exact theorem2_process_source_data_factorization
    (K.multiReportSourceData baseCount count hcount gap tail exposure
      hexposure h_exposure) rate

/--
Appendix B.2 multi-report case from condition functions, with positive
exposure instead of a raw nonzero denominator premise.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_multi_report_condition_functions_factorization_of_pos_exposure
    (K : Theorem2ConditionFunctions) (baseCount count : ℕ)
    (hcount : 1 < count)
    (gap : Fin count → ℝ) {tail exposure rate : ℝ}
    (h_gap : ∀ j : Fin count, 0 ≤ gap j) (h_tail : 0 ≤ tail)
    (hexposure : (∑ j : Fin count, gap j) + tail = exposure)
    (h_exposure_pos : 0 < exposure) :
    (K.multiReportSourceData baseCount count hcount gap tail exposure
        hexposure (ne_of_gt h_exposure_pos)).likelihood rate =
      (K.multiReportSourceData baseCount count hcount gap tail exposure
          hexposure (ne_of_gt h_exposure_pos)).residual *
        sourcePoissonPMF rate
          (K.multiReportSourceData baseCount count hcount gap tail exposure
            hexposure (ne_of_gt h_exposure_pos)).exposure
          (K.multiReportSourceData baseCount count hcount gap tail exposure
            hexposure (ne_of_gt h_exposure_pos)).count := by
  exact theorem2_multi_report_condition_functions_factorization
    K baseCount count hcount gap h_gap h_tail hexposure
    (ne_of_gt h_exposure_pos)

/--
Appendix B.2 multi-report case directly from the rate-indexed Condition 1/2
source semantics after collecting all interarrival/no-arrival kernels.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_multi_report_condition_semantics_formula_factorization
    (S : Theorem2ConditionFunctionSemantics) (baseCount count : ℕ)
    (hcount : 1 < count) {rate exposure : ℝ}
    (h_exposure : exposure ≠ 0) :
    1 < count ∧
      theorem2MultiReportLikelihood
          (S.startDensityOfRate rate)
          (S.endDensityOfRate (baseCount + count) rate)
          (∏ j : Fin count,
            S.survivalIntegralOfRate (baseCount + j.val) rate)
          rate exposure count =
        theorem2CorrectedResidual
          (theorem2MultiReportKernelResidual
            (S.startDensityOfRate rate)
            (S.endDensityOfRate (baseCount + count) rate)
            (∏ j : Fin count,
              S.survivalIntegralOfRate (baseCount + j.val) rate))
          exposure count *
          sourcePoissonPMF rate exposure count := by
  exact theorem2_multi_report_case_factorization hcount h_exposure

/--
Appendix B.2 multi-report source-semantics formula with positive exposure.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_multi_report_condition_semantics_formula_factorization_of_pos_exposure
    (S : Theorem2ConditionFunctionSemantics) (baseCount count : ℕ)
    (hcount : 1 < count) {rate exposure : ℝ}
    (h_exposure_pos : 0 < exposure) :
    1 < count ∧
      theorem2MultiReportLikelihood
          (S.startDensityOfRate rate)
          (S.endDensityOfRate (baseCount + count) rate)
          (∏ j : Fin count,
            S.survivalIntegralOfRate (baseCount + j.val) rate)
          rate exposure count =
        theorem2CorrectedResidual
          (theorem2MultiReportKernelResidual
            (S.startDensityOfRate rate)
            (S.endDensityOfRate (baseCount + count) rate)
            (∏ j : Fin count,
              S.survivalIntegralOfRate (baseCount + j.val) rate))
          exposure count *
          sourcePoissonPMF rate exposure count := by
  exact theorem2_multi_report_case_factorization_of_pos_exposure
    hcount h_exposure_pos

/--
Appendix B.2 multi-report source-data row directly from rate-indexed Condition
1/2 semantics.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_multi_report_condition_semantics_source_data_factorization
    (S : Theorem2ConditionFunctionSemantics) (baseCount count : ℕ)
    (hcount : 1 < count)
    (gap : Fin count → ℝ) {tail exposure rate : ℝ}
    (hexposure : (∑ j : Fin count, gap j) + tail = exposure)
    (h_exposure : exposure ≠ 0) :
    (S.multiReportSourceDataAtRate baseCount count hcount gap tail exposure
        hexposure h_exposure rate).likelihood rate =
      (S.multiReportSourceDataAtRate baseCount count hcount gap tail exposure
          hexposure h_exposure rate).residual *
        sourcePoissonPMF rate
          (S.multiReportSourceDataAtRate baseCount count hcount gap tail exposure
            hexposure h_exposure rate).exposure
          (S.multiReportSourceDataAtRate baseCount count hcount gap tail exposure
            hexposure h_exposure rate).count := by
  exact
    Theorem2ConditionFunctionSemantics.multiReportSourceDataAtRate_self_factorization
      S baseCount count hcount gap hexposure h_exposure

/--
Appendix B.2 multi-report source-data row directly from rate-indexed Condition
1/2 semantics, with positive exposure.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_multi_report_condition_semantics_source_data_factorization_of_pos_exposure
    (S : Theorem2ConditionFunctionSemantics) (baseCount count : ℕ)
    (hcount : 1 < count)
    (gap : Fin count → ℝ) {tail exposure rate : ℝ}
    (hexposure : (∑ j : Fin count, gap j) + tail = exposure)
    (h_exposure_pos : 0 < exposure) :
    (S.multiReportSourceDataAtRate baseCount count hcount gap tail exposure
        hexposure (ne_of_gt h_exposure_pos) rate).likelihood rate =
      (S.multiReportSourceDataAtRate baseCount count hcount gap tail exposure
          hexposure (ne_of_gt h_exposure_pos) rate).residual *
        sourcePoissonPMF rate
          (S.multiReportSourceDataAtRate baseCount count hcount gap tail exposure
            hexposure (ne_of_gt h_exposure_pos) rate).exposure
          (S.multiReportSourceDataAtRate baseCount count hcount gap tail exposure
            hexposure (ne_of_gt h_exposure_pos) rate).count := by
  exact theorem2_multi_report_condition_semantics_source_data_factorization
    S baseCount count hcount gap hexposure (ne_of_gt h_exposure_pos)

/--
Appendix B.2 multi-report ordered-timeline source-data row directly from
rate-indexed Condition 1/2 semantics.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_multi_report_condition_semantics_ordered_timeline_source_data_factorization
    (S : Theorem2ConditionFunctionSemantics) (baseCount : ℕ)
    (T : OrderedFiniteJumpTimeline) (hcount : 1 < T.count)
    (h_exposure : T.window.exposure ≠ 0) (rate : ℝ) :
    (S.multiReportSourceDataFromOrderedTimelineAtRate
        baseCount T hcount h_exposure rate).likelihood rate =
      (S.multiReportSourceDataFromOrderedTimelineAtRate
          baseCount T hcount h_exposure rate).residual *
        sourcePoissonPMF rate
          (S.multiReportSourceDataFromOrderedTimelineAtRate
            baseCount T hcount h_exposure rate).exposure
          (S.multiReportSourceDataFromOrderedTimelineAtRate
            baseCount T hcount h_exposure rate).count := by
  exact
    Theorem2ConditionFunctionSemantics.multiReportSourceDataFromOrderedTimelineAtRate_self_factorization
      S baseCount T hcount h_exposure rate

/--
Appendix B.2 multi-report ordered-timeline source-data row from rate-indexed
Condition 1/2 semantics, aligned with the derived rate-independent
condition-function source-data object.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_multi_report_condition_semantics_ordered_timeline_source_data_factorization_via_condition_functions
    (S : Theorem2ConditionFunctionSemantics) (baseCount : ℕ)
    (T : OrderedFiniteJumpTimeline) (hcount : 1 < T.count)
    (h_exposure : T.window.exposure ≠ 0) (rate : ℝ) :
    (S.multiReportSourceDataFromOrderedTimelineAtRate
        baseCount T hcount h_exposure rate).likelihood rate =
      (S.toConditionFunctions.multiReportSourceDataFromOrderedTimeline
          baseCount T hcount h_exposure).residual *
        sourcePoissonPMF rate
          (S.toConditionFunctions.multiReportSourceDataFromOrderedTimeline
            baseCount T hcount h_exposure).exposure
          (S.toConditionFunctions.multiReportSourceDataFromOrderedTimeline
            baseCount T hcount h_exposure).count := by
  exact
    Theorem2ConditionFunctionSemantics.multiReportSourceDataFromOrderedTimelineAtRate_factorization
      S baseCount T hcount h_exposure rate

/--
Appendix B.2 multi-report ordered-timeline source-data row from rate-indexed
Condition 1/2 semantics, with nonzero exposure derived from positive window
exposure.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_multi_report_condition_semantics_ordered_timeline_source_data_factorization_of_pos_exposure
    (S : Theorem2ConditionFunctionSemantics) (baseCount : ℕ)
    (T : OrderedFiniteJumpTimeline) (hcount : 1 < T.count)
    (h_exposure_pos : 0 < T.window.exposure) (rate : ℝ) :
    (S.multiReportSourceDataFromOrderedTimelineAtRate
        baseCount T hcount (ne_of_gt h_exposure_pos) rate).likelihood rate =
      (S.toConditionFunctions.multiReportSourceDataFromOrderedTimeline
          baseCount T hcount (ne_of_gt h_exposure_pos)).residual *
        sourcePoissonPMF rate
          (S.toConditionFunctions.multiReportSourceDataFromOrderedTimeline
            baseCount T hcount (ne_of_gt h_exposure_pos)).exposure
          (S.toConditionFunctions.multiReportSourceDataFromOrderedTimeline
            baseCount T hcount (ne_of_gt h_exposure_pos)).count := by
  exact
    Theorem2ConditionFunctionSemantics.multiReportSourceDataFromOrderedTimelineAtRate_factorization_of_pos_exposure
      S baseCount T hcount h_exposure_pos rate

/--
Condition 2's start-realization independence, in the explicit Theorem 2
source model, agrees with the condition-semantics end-density term used by the
likelihood algebra.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_condition_source_model_end_density_independent_of_start
    (M : Theorem2ConditionSourceModel)
    (baseCount : ℕ) (startRealization rate : ℝ) :
    M.condition2.endDensityGivenStartOfRate
        baseCount startRealization rate =
      M.toConditionFunctionSemantics.endDensityOfRate baseCount rate := by
  exact
    M.endDensityGivenStart_eq_conditionSemantics_endDensity
      baseCount startRealization rate

/--
The start-conditioned Condition 2 density in the explicit source model is
rate-independent after applying the paper's independence of `S = s`.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_condition_source_model_end_density_given_start_rate_independent
    (M : Theorem2ConditionSourceModel)
    (baseCount : ℕ) (startRealization : ℝ) :
    RateIndependent
      (M.condition2.endDensityGivenStartOfRate
        baseCount startRealization) := by
  exact
    M.condition2.endDensityGivenStart_rateIndependent
      baseCount startRealization

/--
Appendix B.2 zero-report formula directly from the source-vocabulary
Condition 1/2 model.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_zero_report_condition_source_model_formula_factorization
    (M : Theorem2ConditionSourceModel) (baseCount : ℕ)
    (W : ObservationWindow) (rate : ℝ) :
    theorem2ZeroReportLikelihood
        (M.condition1.startDensityOfRate rate)
        (M.condition2.endDensityOfRate baseCount rate)
        rate W.exposure =
      theorem2ZeroReportResidual
          (M.condition1.startDensityOfRate rate)
          (M.condition2.endDensityOfRate baseCount rate) *
        sourcePoissonPMF rate W.exposure 0 := by
  simpa using
    theorem2_zero_report_condition_semantics_formula_factorization
      M.toConditionFunctionSemantics baseCount W rate

/--
Appendix B.2 zero-report source-data row built directly from the
source-vocabulary Condition 1/2 model.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_zero_report_condition_source_model_source_data_factorization
    (M : Theorem2ConditionSourceModel) (baseCount : ℕ)
    (W : ObservationWindow) (rate : ℝ) :
    (M.zeroReportSourceDataFromWindowAtRate baseCount W rate).likelihood rate =
      (M.zeroReportSourceDataFromWindowAtRate baseCount W rate).residual *
        sourcePoissonPMF rate
          (M.zeroReportSourceDataFromWindowAtRate baseCount W rate).exposure
          (M.zeroReportSourceDataFromWindowAtRate baseCount W rate).count := by
  exact theorem2_process_source_data_factorization
    (M.zeroReportSourceDataFromWindowAtRate baseCount W rate) rate

/--
Appendix B.2 one-report formula directly from the source-vocabulary Condition
1/2 model.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_one_report_condition_source_model_formula_factorization
    (M : Theorem2ConditionSourceModel) (baseCount : ℕ)
    {rate exposure : ℝ} (h_exposure : exposure ≠ 0) :
    theorem2OneReportLikelihood
        (M.condition1.startDensityOfRate rate)
        (M.condition2.endDensityOfRate (baseCount + 1) rate)
        (M.condition2.survivalIntegralOfRate baseCount rate)
        rate exposure =
      (theorem2OneReportKernelResidual
          (M.condition1.startDensityOfRate rate)
          (M.condition2.endDensityOfRate (baseCount + 1) rate)
          (M.condition2.survivalIntegralOfRate baseCount rate) / exposure) *
        sourcePoissonPMF rate exposure 1 := by
  simpa using
    theorem2_one_report_condition_semantics_formula_factorization
      M.toConditionFunctionSemantics baseCount h_exposure

/--
Appendix B.2 one-report formula directly from the source-vocabulary Condition
1/2 model, with positive exposure.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_one_report_condition_source_model_formula_factorization_of_pos_exposure
    (M : Theorem2ConditionSourceModel) (baseCount : ℕ)
    {rate exposure : ℝ} (h_exposure_pos : 0 < exposure) :
    theorem2OneReportLikelihood
        (M.condition1.startDensityOfRate rate)
        (M.condition2.endDensityOfRate (baseCount + 1) rate)
        (M.condition2.survivalIntegralOfRate baseCount rate)
        rate exposure =
      (theorem2OneReportKernelResidual
          (M.condition1.startDensityOfRate rate)
          (M.condition2.endDensityOfRate (baseCount + 1) rate)
          (M.condition2.survivalIntegralOfRate baseCount rate) / exposure) *
        sourcePoissonPMF rate exposure 1 := by
  exact
    theorem2_one_report_condition_source_model_formula_factorization
      M baseCount (ne_of_gt h_exposure_pos)

/--
Appendix B.2 one-report source-data row built directly from the
source-vocabulary Condition 1/2 model.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_one_report_condition_source_model_source_data_factorization
    (M : Theorem2ConditionSourceModel) (baseCount : ℕ)
    {gap tail exposure rate : ℝ}
    (hexposure : gap + tail = exposure)
    (h_exposure : exposure ≠ 0) :
    (M.oneReportSourceDataAtRate baseCount gap tail exposure
        hexposure h_exposure rate).likelihood rate =
      (M.oneReportSourceDataAtRate baseCount gap tail exposure
          hexposure h_exposure rate).residual *
        sourcePoissonPMF rate
          (M.oneReportSourceDataAtRate baseCount gap tail exposure
            hexposure h_exposure rate).exposure
          (M.oneReportSourceDataAtRate baseCount gap tail exposure
            hexposure h_exposure rate).count := by
  exact theorem2_process_source_data_factorization
    (M.oneReportSourceDataAtRate baseCount gap tail exposure
      hexposure h_exposure rate) rate

/--
Appendix B.2 one-report source-data row built directly from the
source-vocabulary Condition 1/2 model, with positive exposure.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_one_report_condition_source_model_source_data_factorization_of_pos_exposure
    (M : Theorem2ConditionSourceModel) (baseCount : ℕ)
    {gap tail exposure rate : ℝ}
    (hexposure : gap + tail = exposure)
    (h_exposure_pos : 0 < exposure) :
    (M.oneReportSourceDataAtRate baseCount gap tail exposure
        hexposure (ne_of_gt h_exposure_pos) rate).likelihood rate =
      (M.oneReportSourceDataAtRate baseCount gap tail exposure
          hexposure (ne_of_gt h_exposure_pos) rate).residual *
        sourcePoissonPMF rate
          (M.oneReportSourceDataAtRate baseCount gap tail exposure
            hexposure (ne_of_gt h_exposure_pos) rate).exposure
          (M.oneReportSourceDataAtRate baseCount gap tail exposure
            hexposure (ne_of_gt h_exposure_pos) rate).count := by
  exact
    theorem2_one_report_condition_source_model_source_data_factorization
      M baseCount hexposure (ne_of_gt h_exposure_pos)

/--
Appendix B.2 one-report ordered-window source-data row built directly from
the source-vocabulary Condition 1/2 model.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_one_report_condition_source_model_ordered_window_source_data_factorization
    (M : Theorem2ConditionSourceModel) (baseCount : ℕ)
    (T : OrderedOneJumpWindow) (h_exposure : T.window.exposure ≠ 0)
    (rate : ℝ) :
    (M.oneReportSourceDataFromOrderedJumpWindowAtRate
        baseCount T h_exposure rate).likelihood rate =
      (M.oneReportSourceDataFromOrderedJumpWindowAtRate
          baseCount T h_exposure rate).residual *
        sourcePoissonPMF rate
          (M.oneReportSourceDataFromOrderedJumpWindowAtRate
            baseCount T h_exposure rate).exposure
          (M.oneReportSourceDataFromOrderedJumpWindowAtRate
            baseCount T h_exposure rate).count := by
  exact theorem2_process_source_data_factorization
    (M.oneReportSourceDataFromOrderedJumpWindowAtRate
      baseCount T h_exposure rate) rate

/--
Appendix B.2 one-report ordered-window source-data row built directly from
the source-vocabulary Condition 1/2 model, with positive exposure.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_one_report_condition_source_model_ordered_window_source_data_factorization_of_pos_exposure
    (M : Theorem2ConditionSourceModel) (baseCount : ℕ)
    (T : OrderedOneJumpWindow) (h_exposure_pos : 0 < T.window.exposure)
    (rate : ℝ) :
    (M.oneReportSourceDataFromOrderedJumpWindowAtRate
        baseCount T (ne_of_gt h_exposure_pos) rate).likelihood rate =
      (M.oneReportSourceDataFromOrderedJumpWindowAtRate
          baseCount T (ne_of_gt h_exposure_pos) rate).residual *
        sourcePoissonPMF rate
          (M.oneReportSourceDataFromOrderedJumpWindowAtRate
            baseCount T (ne_of_gt h_exposure_pos) rate).exposure
          (M.oneReportSourceDataFromOrderedJumpWindowAtRate
            baseCount T (ne_of_gt h_exposure_pos) rate).count := by
  exact
    theorem2_one_report_condition_source_model_ordered_window_source_data_factorization
      M baseCount T (ne_of_gt h_exposure_pos) rate

/--
Appendix B.2 multi-report formula directly from the source-vocabulary
Condition 1/2 model.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_multi_report_condition_source_model_formula_factorization
    (M : Theorem2ConditionSourceModel) (baseCount count : ℕ)
    (hcount : 1 < count) {rate exposure : ℝ}
    (h_exposure : exposure ≠ 0) :
    1 < count ∧
      theorem2MultiReportLikelihood
          (M.condition1.startDensityOfRate rate)
          (M.condition2.endDensityOfRate (baseCount + count) rate)
          (∏ j : Fin count,
            M.condition2.survivalIntegralOfRate (baseCount + j.val) rate)
          rate exposure count =
        theorem2CorrectedResidual
          (theorem2MultiReportKernelResidual
            (M.condition1.startDensityOfRate rate)
            (M.condition2.endDensityOfRate (baseCount + count) rate)
            (∏ j : Fin count,
              M.condition2.survivalIntegralOfRate (baseCount + j.val) rate))
          exposure count *
          sourcePoissonPMF rate exposure count := by
  simpa using
    theorem2_multi_report_condition_semantics_formula_factorization
      M.toConditionFunctionSemantics baseCount count hcount h_exposure

/--
Appendix B.2 multi-report formula directly from the source-vocabulary
Condition 1/2 model, with positive exposure.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_multi_report_condition_source_model_formula_factorization_of_pos_exposure
    (M : Theorem2ConditionSourceModel) (baseCount count : ℕ)
    (hcount : 1 < count) {rate exposure : ℝ}
    (h_exposure_pos : 0 < exposure) :
    1 < count ∧
      theorem2MultiReportLikelihood
          (M.condition1.startDensityOfRate rate)
          (M.condition2.endDensityOfRate (baseCount + count) rate)
          (∏ j : Fin count,
            M.condition2.survivalIntegralOfRate (baseCount + j.val) rate)
          rate exposure count =
        theorem2CorrectedResidual
          (theorem2MultiReportKernelResidual
            (M.condition1.startDensityOfRate rate)
            (M.condition2.endDensityOfRate (baseCount + count) rate)
            (∏ j : Fin count,
              M.condition2.survivalIntegralOfRate (baseCount + j.val) rate))
          exposure count *
          sourcePoissonPMF rate exposure count := by
  exact
    theorem2_multi_report_condition_source_model_formula_factorization
      M baseCount count hcount (ne_of_gt h_exposure_pos)

/--
Appendix B.2 multi-report source-data row built directly from the
source-vocabulary Condition 1/2 model.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_multi_report_condition_source_model_source_data_factorization
    (M : Theorem2ConditionSourceModel) (baseCount count : ℕ)
    (hcount : 1 < count)
    (gap : Fin count → ℝ) {tail exposure rate : ℝ}
    (hexposure : (∑ j : Fin count, gap j) + tail = exposure)
    (h_exposure : exposure ≠ 0) :
    (M.multiReportSourceDataAtRate baseCount count hcount gap tail exposure
        hexposure h_exposure rate).likelihood rate =
      (M.multiReportSourceDataAtRate baseCount count hcount gap tail exposure
          hexposure h_exposure rate).residual *
        sourcePoissonPMF rate
          (M.multiReportSourceDataAtRate baseCount count hcount gap tail exposure
            hexposure h_exposure rate).exposure
          (M.multiReportSourceDataAtRate baseCount count hcount gap tail exposure
            hexposure h_exposure rate).count := by
  exact theorem2_process_source_data_factorization
    (M.multiReportSourceDataAtRate baseCount count hcount gap tail exposure
      hexposure h_exposure rate) rate

/--
Appendix B.2 multi-report source-data row built directly from the
source-vocabulary Condition 1/2 model, with positive exposure.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_multi_report_condition_source_model_source_data_factorization_of_pos_exposure
    (M : Theorem2ConditionSourceModel) (baseCount count : ℕ)
    (hcount : 1 < count)
    (gap : Fin count → ℝ) {tail exposure rate : ℝ}
    (hexposure : (∑ j : Fin count, gap j) + tail = exposure)
    (h_exposure_pos : 0 < exposure) :
    (M.multiReportSourceDataAtRate baseCount count hcount gap tail exposure
        hexposure (ne_of_gt h_exposure_pos) rate).likelihood rate =
      (M.multiReportSourceDataAtRate baseCount count hcount gap tail exposure
          hexposure (ne_of_gt h_exposure_pos) rate).residual *
        sourcePoissonPMF rate
          (M.multiReportSourceDataAtRate baseCount count hcount gap tail exposure
            hexposure (ne_of_gt h_exposure_pos) rate).exposure
          (M.multiReportSourceDataAtRate baseCount count hcount gap tail exposure
            hexposure (ne_of_gt h_exposure_pos) rate).count := by
  exact
    theorem2_multi_report_condition_source_model_source_data_factorization
      M baseCount count hcount gap hexposure (ne_of_gt h_exposure_pos)

/--
Appendix B.2 multi-report ordered-timeline source-data row built directly
from the source-vocabulary Condition 1/2 model.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_multi_report_condition_source_model_ordered_timeline_source_data_factorization
    (M : Theorem2ConditionSourceModel) (baseCount : ℕ)
    (T : OrderedFiniteJumpTimeline) (hcount : 1 < T.count)
    (h_exposure : T.window.exposure ≠ 0) (rate : ℝ) :
    (M.multiReportSourceDataFromOrderedTimelineAtRate
        baseCount T hcount h_exposure rate).likelihood rate =
      (M.multiReportSourceDataFromOrderedTimelineAtRate
          baseCount T hcount h_exposure rate).residual *
        sourcePoissonPMF rate
          (M.multiReportSourceDataFromOrderedTimelineAtRate
            baseCount T hcount h_exposure rate).exposure
          (M.multiReportSourceDataFromOrderedTimelineAtRate
            baseCount T hcount h_exposure rate).count := by
  exact theorem2_process_source_data_factorization
    (M.multiReportSourceDataFromOrderedTimelineAtRate
      baseCount T hcount h_exposure rate) rate

/--
Appendix B.2 multi-report ordered-timeline source-data row built directly
from the source-vocabulary Condition 1/2 model, with positive exposure.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_multi_report_condition_source_model_ordered_timeline_source_data_factorization_of_pos_exposure
    (M : Theorem2ConditionSourceModel) (baseCount : ℕ)
    (T : OrderedFiniteJumpTimeline) (hcount : 1 < T.count)
    (h_exposure_pos : 0 < T.window.exposure) (rate : ℝ) :
    (M.multiReportSourceDataFromOrderedTimelineAtRate
        baseCount T hcount (ne_of_gt h_exposure_pos) rate).likelihood rate =
      (M.multiReportSourceDataFromOrderedTimelineAtRate
          baseCount T hcount (ne_of_gt h_exposure_pos) rate).residual *
        sourcePoissonPMF rate
          (M.multiReportSourceDataFromOrderedTimelineAtRate
            baseCount T hcount (ne_of_gt h_exposure_pos) rate).exposure
          (M.multiReportSourceDataFromOrderedTimelineAtRate
            baseCount T hcount (ne_of_gt h_exposure_pos) rate).count := by
  exact
    theorem2_multi_report_condition_source_model_ordered_timeline_source_data_factorization
      M baseCount T hcount (ne_of_gt h_exposure_pos) rate

/--
In the density-kernel Condition 1/2 source model, the `h_m(e)` term used by
the likelihood algebra is the Condition 2 density kernel evaluated at the
observed end time for count state `m`.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_condition_density_source_model_end_density_eq_kernel_at_observed_end
    (M : Theorem2ConditionDensitySourceModel)
    (baseCount : ℕ) (rate : ℝ) :
    M.toConditionFunctionSemantics.endDensityOfRate baseCount rate =
      M.condition2.endDensityKernelOfRate
        baseCount (M.condition2.observedEndTime baseCount) rate := by
  rfl

/--
In the density-kernel Condition 1/2 source model, the survival term used by
the likelihood algebra is the interval integral `∫ h_m(t) dt`.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_condition_density_source_model_survival_integral_eq_interval_integral
    (M : Theorem2ConditionDensitySourceModel)
    (baseCount : ℕ) (rate : ℝ) :
    M.toConditionFunctionSemantics.survivalIntegralOfRate baseCount rate =
      ∫ endTime in M.condition2.survivalLower baseCount..M.condition2.survivalUpper,
        M.condition2.endDensityKernelOfRate baseCount endTime rate := by
  rfl

/--
The density-kernel Condition 2 model makes the interval-integral survival term
rate-independent from pointwise rate-invariance of `h_m(t)`.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_condition_density_source_model_survival_integral_rate_independent
    (M : Theorem2ConditionDensitySourceModel)
    (baseCount : ℕ) :
    RateIndependent
      (M.toConditionFunctionSemantics.survivalIntegralOfRate baseCount) := by
  exact M.condition2.survivalIntegral_rateIndependent baseCount

/--
Appendix B.2 zero-report formula directly from the density-kernel Condition
1/2 source model: the displayed `g(s)` and `h_m(e)` terms factor against the
zero-count source Poisson PMF.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_zero_report_condition_density_source_model_formula_factorization
    (M : Theorem2ConditionDensitySourceModel) (baseCount : ℕ)
    (W : ObservationWindow) (rate : ℝ) :
    theorem2ZeroReportLikelihood
        (M.condition1.startDensityOfRate rate)
        (M.condition2.endDensityKernelOfRate
          baseCount (M.condition2.observedEndTime baseCount) rate)
        rate W.exposure =
      theorem2ZeroReportResidual
          (M.condition1.startDensityOfRate rate)
          (M.condition2.endDensityKernelOfRate
            baseCount (M.condition2.observedEndTime baseCount) rate) *
        sourcePoissonPMF rate W.exposure 0 := by
  simpa using
    theorem2_zero_report_condition_semantics_formula_factorization
      M.toConditionFunctionSemantics baseCount W rate

/--
Appendix B.2 zero-report source-data row built directly from the
density-kernel Condition 1/2 source model.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_zero_report_condition_density_source_model_source_data_factorization
    (M : Theorem2ConditionDensitySourceModel) (baseCount : ℕ)
    (W : ObservationWindow) (rate : ℝ) :
    (M.zeroReportSourceDataFromWindowAtRate baseCount W rate).likelihood rate =
      (M.zeroReportSourceDataFromWindowAtRate baseCount W rate).residual *
        sourcePoissonPMF rate
          (M.zeroReportSourceDataFromWindowAtRate baseCount W rate).exposure
          (M.zeroReportSourceDataFromWindowAtRate baseCount W rate).count := by
  exact theorem2_process_source_data_factorization
    (M.zeroReportSourceDataFromWindowAtRate baseCount W rate) rate

/--
Appendix B.2 one-report formula directly from the density-kernel Condition
1/2 source model: the visible `g(s)`, `h_{m+1}(e)`, and
`∫ h_m(t) dt` terms factor against the one-count source Poisson PMF.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_one_report_condition_density_source_model_formula_factorization
    (M : Theorem2ConditionDensitySourceModel) (baseCount : ℕ)
    {rate exposure : ℝ} (h_exposure : exposure ≠ 0) :
    theorem2OneReportLikelihood
        (M.condition1.startDensityOfRate rate)
        (M.condition2.endDensityKernelOfRate
          (baseCount + 1) (M.condition2.observedEndTime (baseCount + 1)) rate)
        (M.condition2.survivalIntegralOfRate baseCount rate)
        rate exposure =
      (theorem2OneReportKernelResidual
          (M.condition1.startDensityOfRate rate)
          (M.condition2.endDensityKernelOfRate
            (baseCount + 1)
            (M.condition2.observedEndTime (baseCount + 1)) rate)
          (M.condition2.survivalIntegralOfRate baseCount rate) / exposure) *
        sourcePoissonPMF rate exposure 1 := by
  simpa using
    theorem2_one_report_condition_semantics_formula_factorization
      M.toConditionFunctionSemantics baseCount h_exposure

/--
Appendix B.2 one-report formula directly from the density-kernel Condition
1/2 source model, with positive exposure supplying the denominator side
condition.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_one_report_condition_density_source_model_formula_factorization_of_pos_exposure
    (M : Theorem2ConditionDensitySourceModel) (baseCount : ℕ)
    {rate exposure : ℝ} (h_exposure_pos : 0 < exposure) :
    theorem2OneReportLikelihood
        (M.condition1.startDensityOfRate rate)
        (M.condition2.endDensityKernelOfRate
          (baseCount + 1) (M.condition2.observedEndTime (baseCount + 1)) rate)
        (M.condition2.survivalIntegralOfRate baseCount rate)
        rate exposure =
      (theorem2OneReportKernelResidual
          (M.condition1.startDensityOfRate rate)
          (M.condition2.endDensityKernelOfRate
            (baseCount + 1)
            (M.condition2.observedEndTime (baseCount + 1)) rate)
          (M.condition2.survivalIntegralOfRate baseCount rate) / exposure) *
        sourcePoissonPMF rate exposure 1 := by
  exact
    theorem2_one_report_condition_density_source_model_formula_factorization
      M baseCount (ne_of_gt h_exposure_pos)

/--
Appendix B.2 one-report source-data row built directly from the
density-kernel Condition 1/2 source model.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_one_report_condition_density_source_model_source_data_factorization
    (M : Theorem2ConditionDensitySourceModel) (baseCount : ℕ)
    {gap tail exposure rate : ℝ}
    (hexposure : gap + tail = exposure)
    (h_exposure : exposure ≠ 0) :
    (M.oneReportSourceDataAtRate baseCount gap tail exposure
        hexposure h_exposure rate).likelihood rate =
      (M.oneReportSourceDataAtRate baseCount gap tail exposure
          hexposure h_exposure rate).residual *
        sourcePoissonPMF rate
          (M.oneReportSourceDataAtRate baseCount gap tail exposure
            hexposure h_exposure rate).exposure
          (M.oneReportSourceDataAtRate baseCount gap tail exposure
            hexposure h_exposure rate).count := by
  exact theorem2_process_source_data_factorization
    (M.oneReportSourceDataAtRate baseCount gap tail exposure
      hexposure h_exposure rate) rate

/--
Appendix B.2 one-report source-data row built directly from the
density-kernel Condition 1/2 source model, with positive exposure.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_one_report_condition_density_source_model_source_data_factorization_of_pos_exposure
    (M : Theorem2ConditionDensitySourceModel) (baseCount : ℕ)
    {gap tail exposure rate : ℝ}
    (hexposure : gap + tail = exposure)
    (h_exposure_pos : 0 < exposure) :
    (M.oneReportSourceDataAtRate baseCount gap tail exposure
        hexposure (ne_of_gt h_exposure_pos) rate).likelihood rate =
      (M.oneReportSourceDataAtRate baseCount gap tail exposure
          hexposure (ne_of_gt h_exposure_pos) rate).residual *
        sourcePoissonPMF rate
          (M.oneReportSourceDataAtRate baseCount gap tail exposure
            hexposure (ne_of_gt h_exposure_pos) rate).exposure
          (M.oneReportSourceDataAtRate baseCount gap tail exposure
            hexposure (ne_of_gt h_exposure_pos) rate).count := by
  exact
    theorem2_one_report_condition_density_source_model_source_data_factorization
      M baseCount hexposure (ne_of_gt h_exposure_pos)

/--
Appendix B.2 one-report ordered-window source-data row built directly from
the density-kernel Condition 1/2 source model.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_one_report_condition_density_source_model_ordered_window_source_data_factorization
    (M : Theorem2ConditionDensitySourceModel) (baseCount : ℕ)
    (T : OrderedOneJumpWindow) (h_exposure : T.window.exposure ≠ 0)
    (rate : ℝ) :
    (M.oneReportSourceDataFromOrderedJumpWindowAtRate
        baseCount T h_exposure rate).likelihood rate =
      (M.oneReportSourceDataFromOrderedJumpWindowAtRate
          baseCount T h_exposure rate).residual *
        sourcePoissonPMF rate
          (M.oneReportSourceDataFromOrderedJumpWindowAtRate
            baseCount T h_exposure rate).exposure
          (M.oneReportSourceDataFromOrderedJumpWindowAtRate
            baseCount T h_exposure rate).count := by
  exact theorem2_process_source_data_factorization
    (M.oneReportSourceDataFromOrderedJumpWindowAtRate
      baseCount T h_exposure rate) rate

/--
Appendix B.2 one-report ordered-window source-data row built directly from
the density-kernel Condition 1/2 source model, with positive exposure.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_one_report_condition_density_source_model_ordered_window_source_data_factorization_of_pos_exposure
    (M : Theorem2ConditionDensitySourceModel) (baseCount : ℕ)
    (T : OrderedOneJumpWindow) (h_exposure_pos : 0 < T.window.exposure)
    (rate : ℝ) :
    (M.oneReportSourceDataFromOrderedJumpWindowAtRate
        baseCount T (ne_of_gt h_exposure_pos) rate).likelihood rate =
      (M.oneReportSourceDataFromOrderedJumpWindowAtRate
          baseCount T (ne_of_gt h_exposure_pos) rate).residual *
        sourcePoissonPMF rate
          (M.oneReportSourceDataFromOrderedJumpWindowAtRate
            baseCount T (ne_of_gt h_exposure_pos) rate).exposure
          (M.oneReportSourceDataFromOrderedJumpWindowAtRate
            baseCount T (ne_of_gt h_exposure_pos) rate).count := by
  exact
    theorem2_one_report_condition_density_source_model_ordered_window_source_data_factorization
      M baseCount T (ne_of_gt h_exposure_pos) rate

/--
Appendix B.2 multi-report formula directly from the density-kernel Condition
1/2 source model: the visible `g(s)`, `h_{m+M}(e)`, and product of
survival-integral terms factor against the `M`-count source Poisson PMF.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_multi_report_condition_density_source_model_formula_factorization
    (M : Theorem2ConditionDensitySourceModel) (baseCount count : ℕ)
    (hcount : 1 < count) {rate exposure : ℝ}
    (h_exposure : exposure ≠ 0) :
    1 < count ∧
      theorem2MultiReportLikelihood
          (M.condition1.startDensityOfRate rate)
          (M.condition2.endDensityKernelOfRate
            (baseCount + count)
            (M.condition2.observedEndTime (baseCount + count)) rate)
          (∏ j : Fin count,
            M.condition2.survivalIntegralOfRate (baseCount + j.val) rate)
          rate exposure count =
        theorem2CorrectedResidual
          (theorem2MultiReportKernelResidual
            (M.condition1.startDensityOfRate rate)
            (M.condition2.endDensityKernelOfRate
              (baseCount + count)
              (M.condition2.observedEndTime (baseCount + count)) rate)
            (∏ j : Fin count,
              M.condition2.survivalIntegralOfRate (baseCount + j.val) rate))
          exposure count *
          sourcePoissonPMF rate exposure count := by
  simpa using
    theorem2_multi_report_condition_semantics_formula_factorization
      M.toConditionFunctionSemantics baseCount count hcount h_exposure

/--
Appendix B.2 multi-report formula directly from the density-kernel Condition
1/2 source model, with positive exposure supplying the denominator side
condition.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_multi_report_condition_density_source_model_formula_factorization_of_pos_exposure
    (M : Theorem2ConditionDensitySourceModel) (baseCount count : ℕ)
    (hcount : 1 < count) {rate exposure : ℝ}
    (h_exposure_pos : 0 < exposure) :
    1 < count ∧
      theorem2MultiReportLikelihood
          (M.condition1.startDensityOfRate rate)
          (M.condition2.endDensityKernelOfRate
            (baseCount + count)
            (M.condition2.observedEndTime (baseCount + count)) rate)
          (∏ j : Fin count,
            M.condition2.survivalIntegralOfRate (baseCount + j.val) rate)
          rate exposure count =
        theorem2CorrectedResidual
          (theorem2MultiReportKernelResidual
            (M.condition1.startDensityOfRate rate)
            (M.condition2.endDensityKernelOfRate
              (baseCount + count)
              (M.condition2.observedEndTime (baseCount + count)) rate)
            (∏ j : Fin count,
              M.condition2.survivalIntegralOfRate (baseCount + j.val) rate))
          exposure count *
          sourcePoissonPMF rate exposure count := by
  exact
    theorem2_multi_report_condition_density_source_model_formula_factorization
      M baseCount count hcount (ne_of_gt h_exposure_pos)

/--
Appendix B.2 multi-report source-data row built directly from the
density-kernel Condition 1/2 source model.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_multi_report_condition_density_source_model_source_data_factorization
    (M : Theorem2ConditionDensitySourceModel) (baseCount count : ℕ)
    (hcount : 1 < count)
    (gap : Fin count → ℝ) {tail exposure rate : ℝ}
    (hexposure : (∑ j : Fin count, gap j) + tail = exposure)
    (h_exposure : exposure ≠ 0) :
    (M.multiReportSourceDataAtRate baseCount count hcount gap tail exposure
        hexposure h_exposure rate).likelihood rate =
      (M.multiReportSourceDataAtRate baseCount count hcount gap tail exposure
          hexposure h_exposure rate).residual *
        sourcePoissonPMF rate
          (M.multiReportSourceDataAtRate baseCount count hcount gap tail exposure
            hexposure h_exposure rate).exposure
          (M.multiReportSourceDataAtRate baseCount count hcount gap tail exposure
            hexposure h_exposure rate).count := by
  exact theorem2_process_source_data_factorization
    (M.multiReportSourceDataAtRate baseCount count hcount gap tail exposure
      hexposure h_exposure rate) rate

/--
Appendix B.2 multi-report source-data row built directly from the
density-kernel Condition 1/2 source model, with positive exposure.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_multi_report_condition_density_source_model_source_data_factorization_of_pos_exposure
    (M : Theorem2ConditionDensitySourceModel) (baseCount count : ℕ)
    (hcount : 1 < count)
    (gap : Fin count → ℝ) {tail exposure rate : ℝ}
    (hexposure : (∑ j : Fin count, gap j) + tail = exposure)
    (h_exposure_pos : 0 < exposure) :
    (M.multiReportSourceDataAtRate baseCount count hcount gap tail exposure
        hexposure (ne_of_gt h_exposure_pos) rate).likelihood rate =
      (M.multiReportSourceDataAtRate baseCount count hcount gap tail exposure
          hexposure (ne_of_gt h_exposure_pos) rate).residual *
        sourcePoissonPMF rate
          (M.multiReportSourceDataAtRate baseCount count hcount gap tail exposure
            hexposure (ne_of_gt h_exposure_pos) rate).exposure
          (M.multiReportSourceDataAtRate baseCount count hcount gap tail exposure
            hexposure (ne_of_gt h_exposure_pos) rate).count := by
  exact
    theorem2_multi_report_condition_density_source_model_source_data_factorization
      M baseCount count hcount gap hexposure (ne_of_gt h_exposure_pos)

/--
Appendix B.2 multi-report ordered-timeline source-data row built directly
from the density-kernel Condition 1/2 source model.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_multi_report_condition_density_source_model_ordered_timeline_source_data_factorization
    (M : Theorem2ConditionDensitySourceModel) (baseCount : ℕ)
    (T : OrderedFiniteJumpTimeline) (hcount : 1 < T.count)
    (h_exposure : T.window.exposure ≠ 0) (rate : ℝ) :
    (M.multiReportSourceDataFromOrderedTimelineAtRate
        baseCount T hcount h_exposure rate).likelihood rate =
      (M.multiReportSourceDataFromOrderedTimelineAtRate
          baseCount T hcount h_exposure rate).residual *
        sourcePoissonPMF rate
          (M.multiReportSourceDataFromOrderedTimelineAtRate
            baseCount T hcount h_exposure rate).exposure
          (M.multiReportSourceDataFromOrderedTimelineAtRate
            baseCount T hcount h_exposure rate).count := by
  exact theorem2_process_source_data_factorization
    (M.multiReportSourceDataFromOrderedTimelineAtRate
      baseCount T hcount h_exposure rate) rate

/--
Appendix B.2 multi-report ordered-timeline source-data row built directly
from the density-kernel Condition 1/2 source model, with positive exposure.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_multi_report_condition_density_source_model_ordered_timeline_source_data_factorization_of_pos_exposure
    (M : Theorem2ConditionDensitySourceModel) (baseCount : ℕ)
    (T : OrderedFiniteJumpTimeline) (hcount : 1 < T.count)
    (h_exposure_pos : 0 < T.window.exposure) (rate : ℝ) :
    (M.multiReportSourceDataFromOrderedTimelineAtRate
        baseCount T hcount (ne_of_gt h_exposure_pos) rate).likelihood rate =
      (M.multiReportSourceDataFromOrderedTimelineAtRate
          baseCount T hcount (ne_of_gt h_exposure_pos) rate).residual *
        sourcePoissonPMF rate
          (M.multiReportSourceDataFromOrderedTimelineAtRate
            baseCount T hcount (ne_of_gt h_exposure_pos) rate).exposure
          (M.multiReportSourceDataFromOrderedTimelineAtRate
            baseCount T hcount (ne_of_gt h_exposure_pos) rate).count := by
  exact
    theorem2_multi_report_condition_density_source_model_ordered_timeline_source_data_factorization
      M baseCount T hcount (ne_of_gt h_exposure_pos) rate

/--
Unified Appendix B.2 observed-window source-data factorization constructed
directly from mathlib Poisson increment laws and the explicit Condition 1/2
source model.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_observed_window_source_data_factorization_from_poisson_increment_laws_and_condition_source_model
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : HomogeneousPoissonCountingProcessByLaw Ω P)
    (M : Theorem2ConditionSourceModel)
    (C : Theorem2ObservedWindowCase) :
    C.sourceDataLikelihoodAtRate
        (theorem2_poisson_process_and_condition_semantics.fromPoissonIncrementLawsAndConditionSourceModel
          H M) =
      C.residualWith M.toConditionFunctionSemantics.toConditionFunctions *
        sourcePoissonPMF H.rate
          (C.exposureWith M.toConditionFunctionSemantics.toConditionFunctions)
          (C.countWith M.toConditionFunctionSemantics.toConditionFunctions) := by
  exact
    C.sourceDataAtRate_factorizationFromPoissonIncrementLawsAndConditionSemantics
      H M.toConditionFunctionSemantics

/--
Unified Appendix B.2 observed-window source-data factorization constructed
directly from mathlib Poisson increment laws and the density-kernel Condition
1/2 source model.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_observed_window_source_data_factorization_from_poisson_increment_laws_and_condition_density_source_model
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : HomogeneousPoissonCountingProcessByLaw Ω P)
    (M : Theorem2ConditionDensitySourceModel)
    (C : Theorem2ObservedWindowCase) :
    C.sourceDataLikelihoodAtRate
        (theorem2_poisson_process_and_condition_semantics.fromPoissonIncrementLawsAndConditionDensitySourceModel
          H M) =
      C.residualWith M.toConditionFunctionSemantics.toConditionFunctions *
        sourcePoissonPMF H.rate
          (C.exposureWith M.toConditionFunctionSemantics.toConditionFunctions)
          (C.countWith M.toConditionFunctionSemantics.toConditionFunctions) := by
  exact
    C.sourceDataAtRate_factorizationFromPoissonIncrementLawsAndConditionSemantics
      H M.toConditionFunctionSemantics

/--
Unified Appendix B.2 observed-window source-data factorization from the
public-partial primitive source model.  The paper's fixed Condition 1/2 data
are converted inside Lean; the only process-side input is the homogeneous
counting-process law carried by `M`.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_observed_window_source_data_factorization_from_primitive_source_model
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (M : Theorem2PrimitiveSourceModel Ω P)
    (C : Theorem2ObservedWindowCase) :
    C.sourceDataLikelihoodAtRate M.toSourceSemantics =
      C.residualWith M.conditionFunctions *
        sourcePoissonPMF M.rate
          (C.exposureWith M.conditionFunctions)
          (C.countWith M.conditionFunctions) := by
  exact
    theorem2_observed_window_source_data_factorization_from_poisson_increment_laws_and_condition_density_source_model
      M.countProcess M.toConditionDensitySourceModel C

/--
Duration-censored stopping-certificate route to Appendix B.2 source-data
factorization from the public-partial primitive source model.  The certificate
supplies the realized deterministic observation window; the primitive source
model supplies the homogeneous count law and fixed paper Condition 1/2 kernels.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_duration_censored_certificate_source_data_factorization_from_primitive_source_model
    {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration (Ω := Ω) ℝ mΩ}
    (M : Theorem2PrimitiveSourceModel Ω P)
    (Cert : DurationCensoredFirstCountObservationCertificate 𝓕)
    (ω : Ω)
    (caseFromWindow : ObservationWindow → Theorem2ObservedWindowCase) :
    (caseFromWindow (Cert.observationWindow ω)).sourceDataLikelihoodAtRate
        M.toSourceSemantics =
      (caseFromWindow (Cert.observationWindow ω)).residualWith
          M.conditionFunctions *
        sourcePoissonPMF M.rate
          ((caseFromWindow (Cert.observationWindow ω)).exposureWith
            M.conditionFunctions)
          ((caseFromWindow (Cert.observationWindow ω)).countWith
            M.conditionFunctions) := by
  exact
    theorem2_observed_window_source_data_factorization_from_primitive_source_model
      M (caseFromWindow (Cert.observationWindow ω))

/--
Zero-report specialization of the duration-censored stopping-certificate route.
This exposes the common empirical-preprocessing case where the certified
window is attached directly to a zero-report Appendix B.2 row.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_zero_report_duration_censored_certificate_source_data_factorization_from_primitive_source_model
    {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration (Ω := Ω) ℝ mΩ}
    (M : Theorem2PrimitiveSourceModel Ω P)
    (Cert : DurationCensoredFirstCountObservationCertificate 𝓕)
    (ω : Ω) (baseCount : ℕ) :
    (Theorem2ObservedWindowCase.zero baseCount
        (Cert.observationWindow ω)).sourceDataLikelihoodAtRate
        M.toSourceSemantics =
      (Theorem2ObservedWindowCase.zero baseCount
          (Cert.observationWindow ω)).residualWith M.conditionFunctions *
        sourcePoissonPMF M.rate
          ((Theorem2ObservedWindowCase.zero baseCount
              (Cert.observationWindow ω)).exposureWith M.conditionFunctions)
          ((Theorem2ObservedWindowCase.zero baseCount
              (Cert.observationWindow ω)).countWith M.conditionFunctions) := by
  exact
    theorem2_duration_censored_certificate_source_data_factorization_from_primitive_source_model
      M Cert ω (fun W => Theorem2ObservedWindowCase.zero baseCount W)

/--
Unified Appendix B.2 observed-window source-data factorization from primitive
source semantics.  This packages the zero/one/multi observed-window cases
after attaching the rate-indexed Condition 1/2 source terms at the process
rate.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_observed_window_source_data_factorization_from_source_semantics
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (S : theorem2_poisson_process_and_condition_semantics Ω P)
    (C : Theorem2ObservedWindowCase) :
    C.sourceDataLikelihoodAtRate S =
      C.sourceDataResidualAtRate S *
        sourcePoissonPMF S.rate
          (C.sourceDataExposureAtRate S) (C.sourceDataCountAtRate S) := by
  exact C.sourceDataAtRate_factorization S

/--
Unified Appendix B.2 observed-window source-data factorization constructed
directly from mathlib Poisson increment laws and the paper's rate-indexed
Condition 1/2 source semantics.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_observed_window_source_data_factorization_from_poisson_increment_laws_and_condition_semantics
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : HomogeneousPoissonCountingProcessByLaw Ω P)
    (G : Theorem2ConditionFunctionSemantics)
    (C : Theorem2ObservedWindowCase) :
    C.sourceDataLikelihoodAtRate
        (theorem2_poisson_process_and_condition_semantics.fromPoissonIncrementLawsAndConditionSemantics
          H G) =
      C.residualWith G.toConditionFunctions *
        sourcePoissonPMF H.rate
          (C.exposureWith G.toConditionFunctions)
          (C.countWith G.toConditionFunctions) := by
  exact C.sourceDataAtRate_factorizationFromPoissonIncrementLawsAndConditionSemantics H G

/--
Appendix B.2 multi-report case from actual start/end times and indexed
observed jump times; the exposure identity is discharged by telescoping.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_multi_report_jump_times_factorization
    (K : Theorem2ConditionFunctions) (baseCount count : ℕ)
    (hcount : 1 < count)
    {startTime endTime rate : ℝ} (jumpTime : ℕ → ℝ)
    (hmono : Monotone (jumpTimelineEndpoint startTime jumpTime))
    (hlast : jumpTimelineEndpoint startTime jumpTime count ≤ endTime)
    (h_exposure : observationExposure startTime endTime ≠ 0) :
    (K.multiReportSourceDataFromJumpTimes baseCount count hcount
        startTime endTime jumpTime h_exposure).likelihood rate =
      (K.multiReportSourceDataFromJumpTimes baseCount count hcount
          startTime endTime jumpTime h_exposure).residual *
        sourcePoissonPMF rate
          (K.multiReportSourceDataFromJumpTimes baseCount count hcount
            startTime endTime jumpTime h_exposure).exposure
          (K.multiReportSourceDataFromJumpTimes baseCount count hcount
            startTime endTime jumpTime h_exposure).count := by
  exact theorem2_process_source_data_factorization
    (K.multiReportSourceDataFromJumpTimes baseCount count hcount
      startTime endTime jumpTime h_exposure) rate

/--
Appendix B.2 multi-report case from actual start/end times and indexed
observed jump times, with positive observation exposure.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_multi_report_jump_times_factorization_of_pos_exposure
    (K : Theorem2ConditionFunctions) (baseCount count : ℕ)
    (hcount : 1 < count)
    {startTime endTime rate : ℝ} (jumpTime : ℕ → ℝ)
    (hmono : Monotone (jumpTimelineEndpoint startTime jumpTime))
    (hlast : jumpTimelineEndpoint startTime jumpTime count ≤ endTime)
    (h_exposure_pos : 0 < observationExposure startTime endTime) :
    (K.multiReportSourceDataFromJumpTimes baseCount count hcount
        startTime endTime jumpTime
        (ne_of_gt h_exposure_pos)).likelihood rate =
      (K.multiReportSourceDataFromJumpTimes baseCount count hcount
          startTime endTime jumpTime
          (ne_of_gt h_exposure_pos)).residual *
        sourcePoissonPMF rate
          (K.multiReportSourceDataFromJumpTimes baseCount count hcount
            startTime endTime jumpTime
            (ne_of_gt h_exposure_pos)).exposure
          (K.multiReportSourceDataFromJumpTimes baseCount count hcount
            startTime endTime jumpTime
            (ne_of_gt h_exposure_pos)).count := by
  exact theorem2_multi_report_jump_times_factorization
    K baseCount count hcount jumpTime hmono hlast
    (ne_of_gt h_exposure_pos)

/--
Eq. (33) stopping-time condition: when the first-report, inspection, and
work-order times are stopping times, their 100-day min-censored endpoint is a
stopping time.
Source status: Lean-checked paper-facing row.
-/
theorem equation33_nyc_preprocessing_endpoint_is_stopping_time
    {Ω : Type u} {mΩ : MeasurableSpace Ω}
    (𝓕 : Filtration (Ω := Ω) ℝ mΩ)
    (startTime inspectionTime workOrderTime : Ω → ℝ)
    (h_start : IsStoppingTime 𝓕 startTime)
    (h_inspection : IsStoppingTime 𝓕 inspectionTime)
    (h_workOrder : IsStoppingTime 𝓕 workOrderTime) :
    AppliedModelingLib.Probability.PoissonProcess.IsStoppingTime 𝓕 (fun ω =>
      min (min (startTime ω + (100 : ℝ)) (inspectionTime ω))
        (workOrderTime ω)) := by
  exact (h_start.add_const_nonneg (show (0 : ℝ) ≤ 100 by norm_num)).min3
    h_inspection h_workOrder

/--
Eq. (33), NYC preprocessing stopping-time form: if the first-report time,
inspection time, and work-order time are stopping times, then the paper's
min-censored preprocessing rule defines a stopping observation window.
Source status: Lean-checked paper-facing row.
-/
theorem equation33_nyc_preprocessing_stopping_observation_window
    {Ω : Type u} {mΩ : MeasurableSpace Ω}
    (𝓕 : Filtration (Ω := Ω) ℝ mΩ)
    (startTime inspectionTime workOrderTime : Ω → ℝ)
    (h_start : IsStoppingTime 𝓕 startTime)
    (h_inspection_stopping : IsStoppingTime 𝓕 inspectionTime)
    (h_workOrder_stopping : IsStoppingTime 𝓕 workOrderTime)
    (h_inspection : ∀ ω, startTime ω ≤ inspectionTime ω)
    (h_workOrder : ∀ ω, startTime ω ≤ workOrderTime ω) :
    ∃ W : StoppingObservationWindow 𝓕,
      W.startTime = startTime ∧
        W.endTime =
          (fun ω =>
            min (min (startTime ω + (100 : ℝ)) (inspectionTime ω))
              (workOrderTime ω)) ∧
        ∀ ω, 0 ≤ W.exposure ω := by
  let W :=
    nycStoppingObservationWindow 𝓕 startTime inspectionTime workOrderTime
      h_start h_inspection_stopping h_workOrder_stopping
      h_inspection h_workOrder
  refine ⟨W, rfl, ?_, fun ω => W.exposure_nonneg ω⟩
  funext ω
  rfl

/--
Eq. (33), NYC preprocessing deterministic-endpoint stopping-time form: if the
first-report time is a stopping time and the fixed inspection/work-order
endpoints are after it pathwise, then the preprocessing rule defines a
stopping observation window.
Source status: Lean-checked paper-facing row.
-/
theorem equation33_nyc_preprocessing_stopping_observation_window_of_deterministic_endpoints
    {Ω : Type u} {mΩ : MeasurableSpace Ω}
    (𝓕 : Filtration (Ω := Ω) ℝ mΩ)
    (startTime : Ω → ℝ) (inspectionTime workOrderTime : ℝ)
    (h_start : IsStoppingTime 𝓕 startTime)
    (h_inspection : ∀ ω, startTime ω ≤ inspectionTime)
    (h_workOrder : ∀ ω, startTime ω ≤ workOrderTime) :
    ∃ W : StoppingObservationWindow 𝓕,
      W.startTime = startTime ∧
        W.endTime =
          (fun ω =>
            min (min (startTime ω + (100 : ℝ)) inspectionTime)
              workOrderTime) ∧
        ∀ ω, 0 ≤ W.exposure ω := by
  let W :=
    nycStoppingObservationWindowOfDeterministicEndpoints 𝓕 startTime
      inspectionTime workOrderTime h_start h_inspection h_workOrder
  refine ⟨W, rfl, ?_, fun ω => W.exposure_nonneg ω⟩
  funext ω
  rfl

/--
Eq. (33), NYC preprocessing first-count-arrival form: if the first-report time
has the same level sets as an adapted report-count threshold event and the
inspection/work-order endpoints are fixed times after it pathwise, then the
preprocessing rule defines a stopping observation window.
Source status: Lean-checked paper-facing row.
-/
theorem equation33_nyc_preprocessing_stopping_observation_window_of_first_count_arrival
    {Ω : Type u} {mΩ : MeasurableSpace Ω}
    (𝓕 : Filtration (Ω := Ω) ℝ mΩ)
    (reportCount : ℝ → Ω → ℕ) (startTime : Ω → ℝ)
    (inspectionTime workOrderTime : ℝ)
    (C : FirstCountArrivalCertificate 𝓕 reportCount startTime)
    (h_inspection : ∀ ω, startTime ω ≤ inspectionTime)
    (h_workOrder : ∀ ω, startTime ω ≤ workOrderTime) :
    ∃ W : StoppingObservationWindow 𝓕,
      W.startTime = startTime ∧
        W.endTime =
          (fun ω =>
            min (min (startTime ω + (100 : ℝ)) inspectionTime)
              workOrderTime) ∧
        ∀ ω, 0 ≤ W.exposure ω := by
  let W :=
    nycStoppingObservationWindowOfFirstReportCountCertificate 𝓕
      reportCount startTime inspectionTime workOrderTime C
      h_inspection h_workOrder
  refine ⟨W, rfl, ?_, fun ω => W.exposure_nonneg ω⟩
  funext ω
  rfl

/--
Eq. (33), NYC preprocessing local-count-process stopping-endpoint form: if
report counts are observable at each time, the first-report time has level
sets `{S <= t} = {1 <= N_t}`, and the inspection/work-order endpoint rules are
stopping times after the first report pathwise, then the preprocessing rule
defines a stopping observation window.  This is the finite/local
primitive-process route that avoids a full path-space Kolmogorov construction.
Source status: Lean-checked paper-facing row.
-/
theorem equation33_nyc_preprocessing_stopping_observation_window_of_local_count_process_stopping_endpoints
    {Ω : Type u} {mΩ : MeasurableSpace Ω}
    (𝓕 : Filtration (Ω := Ω) ℝ mΩ)
    (reportCount : ℝ → Ω → ℕ) (startTime : Ω → ℝ)
    (inspectionTime workOrderTime : Ω → ℝ)
    (h_count_measurable : ∀ t : ℝ, Measurable[𝓕 t] (reportCount t))
    (h_first_level_sets :
      ∀ t : ℝ, {ω | startTime ω ≤ t} = {ω | 1 ≤ reportCount t ω})
    (h_inspection_stopping : IsStoppingTime 𝓕 inspectionTime)
    (h_workOrder_stopping : IsStoppingTime 𝓕 workOrderTime)
    (h_inspection : ∀ ω, startTime ω ≤ inspectionTime ω)
    (h_workOrder : ∀ ω, startTime ω ≤ workOrderTime ω) :
    ∃ W : StoppingObservationWindow 𝓕,
      W.startTime = startTime ∧
        W.endTime =
          (fun ω =>
            min (min (startTime ω + (100 : ℝ)) (inspectionTime ω))
              (workOrderTime ω)) ∧
        ∀ ω, 0 ≤ W.exposure ω := by
  let W :=
    nycStoppingObservationWindowOfLocalCountProcess 𝓕 reportCount startTime
      inspectionTime workOrderTime h_count_measurable h_first_level_sets
      h_inspection_stopping h_workOrder_stopping h_inspection h_workOrder
  refine ⟨W, rfl, ?_, fun ω => W.exposure_nonneg ω⟩
  funext ω
  rfl

/--
Eq. (33), NYC preprocessing pathwise form from the local-count-process
stopping certificate: on every realized sample path, the certified stopping
window induces the deterministic observation window used by the finite
likelihood layer.
Source status: Lean-checked paper-facing row.
-/
theorem equation33_nyc_preprocessing_observation_window_of_local_count_process_at_sample
    {Ω : Type u} {mΩ : MeasurableSpace Ω}
    (𝓕 : Filtration (Ω := Ω) ℝ mΩ)
    (reportCount : ℝ → Ω → ℕ) (startTime : Ω → ℝ)
    (inspectionTime workOrderTime : Ω → ℝ)
    (h_count_measurable : ∀ t : ℝ, Measurable[𝓕 t] (reportCount t))
    (h_first_level_sets :
      ∀ t : ℝ, {ω | startTime ω ≤ t} = {ω | 1 ≤ reportCount t ω})
    (h_inspection_stopping : IsStoppingTime 𝓕 inspectionTime)
    (h_workOrder_stopping : IsStoppingTime 𝓕 workOrderTime)
    (h_inspection : ∀ ω, startTime ω ≤ inspectionTime ω)
    (h_workOrder : ∀ ω, startTime ω ≤ workOrderTime ω)
    (ω : Ω) :
    ∃ W : ObservationWindow,
      W.startTime = startTime ω ∧
        W.endTime =
          min (min (startTime ω + (100 : ℝ)) (inspectionTime ω))
            (workOrderTime ω) ∧
        0 ≤ W.exposure := by
  let Wstop :=
    nycStoppingObservationWindowOfLocalCountProcess 𝓕 reportCount startTime
      inspectionTime workOrderTime h_count_measurable h_first_level_sets
      h_inspection_stopping h_workOrder_stopping h_inspection h_workOrder
  let W := Wstop.toObservationWindow ω
  refine ⟨W, rfl, ?_, W.exposure_nonneg⟩
  rfl

/--
Eq. (33), NYC preprocessing zero-report likelihood bridge: the local-count
stopping certificate induces the pathwise observation window, and the
zero-report Appendix B.2 source-data row factors over that certified exposure.
Source status: Lean-checked paper-facing row.
-/
theorem equation33_nyc_zero_report_factorization_from_local_count_process_at_sample
    {Ω : Type u} {mΩ : MeasurableSpace Ω}
    (𝓕 : Filtration (Ω := Ω) ℝ mΩ)
    (K : Theorem2ConditionFunctions) (baseCount : ℕ)
    (reportCount : ℝ → Ω → ℕ) (startTime : Ω → ℝ)
    (inspectionTime workOrderTime : Ω → ℝ)
    (h_count_measurable : ∀ t : ℝ, Measurable[𝓕 t] (reportCount t))
    (h_first_level_sets :
      ∀ t : ℝ, {ω | startTime ω ≤ t} = {ω | 1 ≤ reportCount t ω})
    (h_inspection_stopping : IsStoppingTime 𝓕 inspectionTime)
    (h_workOrder_stopping : IsStoppingTime 𝓕 workOrderTime)
    (h_inspection : ∀ ω, startTime ω ≤ inspectionTime ω)
    (h_workOrder : ∀ ω, startTime ω ≤ workOrderTime ω)
    (ω : Ω) (rate : ℝ) :
    ∃ W : ObservationWindow,
      W.startTime = startTime ω ∧
        W.endTime =
          min (min (startTime ω + (100 : ℝ)) (inspectionTime ω))
            (workOrderTime ω) ∧
        (K.zeroReportSourceDataFromWindow baseCount W).likelihood rate =
          theorem2ZeroReportResidual K.startDensity (K.endDensity baseCount) *
            sourcePoissonPMF rate W.exposure 0 := by
  let Wstop :=
    nycStoppingObservationWindowOfLocalCountProcess 𝓕 reportCount startTime
      inspectionTime workOrderTime h_count_measurable h_first_level_sets
      h_inspection_stopping h_workOrder_stopping h_inspection h_workOrder
  let W := Wstop.toObservationWindow ω
  refine ⟨W, rfl, ?_, ?_⟩
  · rfl
  · exact theorem2_zero_report_stopping_window_at_sample_factorization_explicit
      K baseCount Wstop ω rate

/--
Eq. (33), NYC preprocessing one-report likelihood bridge: under explicit
observed-jump ordering in the certified pathwise preprocessing window, the
Appendix B.2 one-report source-data row factors over the certified exposure.
Source status: Lean-checked paper-facing row.
-/
theorem equation33_nyc_one_report_factorization_from_local_count_process_at_sample
    {Ω : Type u} {mΩ : MeasurableSpace Ω}
    (𝓕 : Filtration (Ω := Ω) ℝ mΩ)
    (K : Theorem2ConditionFunctions) (baseCount : ℕ)
    (reportCount : ℝ → Ω → ℕ) (startTime : Ω → ℝ)
    (inspectionTime workOrderTime : Ω → ℝ)
    (h_count_measurable : ∀ t : ℝ, Measurable[𝓕 t] (reportCount t))
    (h_first_level_sets :
      ∀ t : ℝ, {ω | startTime ω ≤ t} = {ω | 1 ≤ reportCount t ω})
    (h_inspection_stopping : IsStoppingTime 𝓕 inspectionTime)
    (h_workOrder_stopping : IsStoppingTime 𝓕 workOrderTime)
    (h_inspection : ∀ ω, startTime ω ≤ inspectionTime ω)
    (h_workOrder : ∀ ω, startTime ω ≤ workOrderTime ω)
    (ω : Ω) {firstJumpTime rate : ℝ}
    (h_window :
      startTime ω <
        min (min (startTime ω + (100 : ℝ)) (inspectionTime ω))
          (workOrderTime ω))
    (h_start_le_jump : startTime ω ≤ firstJumpTime)
    (h_jump_le_end :
      firstJumpTime ≤
        min (min (startTime ω + (100 : ℝ)) (inspectionTime ω))
          (workOrderTime ω)) :
    ∃ W : ObservationWindow,
      ∃ hW_window : W.startTime < W.endTime,
      ∃ hW_start_le_jump : W.startTime ≤ firstJumpTime,
      ∃ hW_jump_le_end : firstJumpTime ≤ W.endTime,
      W.startTime = startTime ω ∧
        W.endTime =
          min (min (startTime ω + (100 : ℝ)) (inspectionTime ω))
            (workOrderTime ω) ∧
        (K.oneReportSourceDataFromOrderedWindow baseCount
          W.startTime W.endTime firstJumpTime hW_window
          hW_start_le_jump hW_jump_le_end).likelihood rate =
          (K.oneReportSourceDataFromOrderedWindow baseCount
            W.startTime W.endTime firstJumpTime hW_window
            hW_start_le_jump hW_jump_le_end).residual *
            sourcePoissonPMF rate W.exposure 1 := by
  let Wstop :=
    nycStoppingObservationWindowOfLocalCountProcess 𝓕 reportCount startTime
      inspectionTime workOrderTime h_count_measurable h_first_level_sets
      h_inspection_stopping h_workOrder_stopping h_inspection h_workOrder
  let W := Wstop.toObservationWindow ω
  have hW_window : W.startTime < W.endTime := by
    change Wstop.startTime ω < Wstop.endTime ω
    change startTime ω <
      min (min (startTime ω + empiricalMaxObservationDurationDays)
        (inspectionTime ω)) (workOrderTime ω)
    simpa [empiricalMaxObservationDurationDays] using h_window
  have hW_start_le_jump : W.startTime ≤ firstJumpTime := by
    change Wstop.startTime ω ≤ firstJumpTime
    change startTime ω ≤ firstJumpTime
    exact h_start_le_jump
  have hW_jump_le_end : firstJumpTime ≤ W.endTime := by
    change firstJumpTime ≤ Wstop.endTime ω
    change firstJumpTime ≤
      min (min (startTime ω + empiricalMaxObservationDurationDays)
        (inspectionTime ω)) (workOrderTime ω)
    simpa [empiricalMaxObservationDurationDays] using h_jump_le_end
  refine ⟨W, hW_window, hW_start_le_jump, hW_jump_le_end, rfl, ?_, ?_⟩
  · rfl
  · exact theorem2_one_report_stopping_window_at_sample_factorization
      K baseCount Wstop ω
      hW_window hW_start_le_jump hW_jump_le_end

/--
Eq. (33), NYC preprocessing multi-report likelihood bridge: under explicit
ordered observed-jump timeline premises in the certified pathwise preprocessing
window, the Appendix B.2 multi-report source-data row factors over the
certified exposure.
Source status: Lean-checked paper-facing row.
-/
theorem equation33_nyc_multi_report_factorization_from_local_count_process_at_sample
    {Ω : Type u} {mΩ : MeasurableSpace Ω}
    (𝓕 : Filtration (Ω := Ω) ℝ mΩ)
    (K : Theorem2ConditionFunctions) (baseCount count : ℕ)
    (hcount : 1 < count)
    (reportCount : ℝ → Ω → ℕ) (startTime : Ω → ℝ)
    (inspectionTime workOrderTime : Ω → ℝ)
    (h_count_measurable : ∀ t : ℝ, Measurable[𝓕 t] (reportCount t))
    (h_first_level_sets :
      ∀ t : ℝ, {ω | startTime ω ≤ t} = {ω | 1 ≤ reportCount t ω})
    (h_inspection_stopping : IsStoppingTime 𝓕 inspectionTime)
    (h_workOrder_stopping : IsStoppingTime 𝓕 workOrderTime)
    (h_inspection : ∀ ω, startTime ω ≤ inspectionTime ω)
    (h_workOrder : ∀ ω, startTime ω ≤ workOrderTime ω)
    (ω : Ω) (jumpTime : ℕ → ℝ) {rate : ℝ}
    (h_window :
      startTime ω <
        min (min (startTime ω + (100 : ℝ)) (inspectionTime ω))
          (workOrderTime ω))
    (hmono : Monotone (jumpTimelineEndpoint (startTime ω) jumpTime))
    (hlast :
      jumpTimelineEndpoint (startTime ω) jumpTime count ≤
        min (min (startTime ω + (100 : ℝ)) (inspectionTime ω))
          (workOrderTime ω)) :
    ∃ W : ObservationWindow,
      ∃ hW_window : W.startTime < W.endTime,
      ∃ hWmono : Monotone (jumpTimelineEndpoint W.startTime jumpTime),
      ∃ hWlast : jumpTimelineEndpoint W.startTime jumpTime count ≤ W.endTime,
      W.startTime = startTime ω ∧
        W.endTime =
          min (min (startTime ω + (100 : ℝ)) (inspectionTime ω))
            (workOrderTime ω) ∧
        (K.multiReportSourceDataFromOrderedWindow baseCount count hcount
          W.startTime W.endTime jumpTime hW_window hWmono hWlast).likelihood rate =
          (K.multiReportSourceDataFromOrderedWindow baseCount count hcount
            W.startTime W.endTime jumpTime hW_window hWmono hWlast).residual *
            sourcePoissonPMF rate W.exposure count := by
  let Wstop :=
    nycStoppingObservationWindowOfLocalCountProcess 𝓕 reportCount startTime
      inspectionTime workOrderTime h_count_measurable h_first_level_sets
      h_inspection_stopping h_workOrder_stopping h_inspection h_workOrder
  let W := Wstop.toObservationWindow ω
  have hW_window : W.startTime < W.endTime := by
    change Wstop.startTime ω < Wstop.endTime ω
    change startTime ω <
      min (min (startTime ω + empiricalMaxObservationDurationDays)
        (inspectionTime ω)) (workOrderTime ω)
    simpa [empiricalMaxObservationDurationDays] using h_window
  have hWmono : Monotone (jumpTimelineEndpoint W.startTime jumpTime) := by
    change Monotone (jumpTimelineEndpoint (Wstop.startTime ω) jumpTime)
    change Monotone (jumpTimelineEndpoint (startTime ω) jumpTime)
    exact hmono
  have hWlast :
      jumpTimelineEndpoint W.startTime jumpTime count ≤ W.endTime := by
    change jumpTimelineEndpoint (Wstop.startTime ω) jumpTime count ≤
      Wstop.endTime ω
    change jumpTimelineEndpoint (startTime ω) jumpTime count ≤
      min (min (startTime ω + empiricalMaxObservationDurationDays)
        (inspectionTime ω)) (workOrderTime ω)
    simpa [empiricalMaxObservationDurationDays] using hlast
  refine ⟨W, hW_window, hWmono, hWlast, rfl, ?_, ?_⟩
  · rfl
  · exact theorem2_multi_report_stopping_window_at_sample_factorization
      K baseCount count hcount Wstop ω jumpTime
      hW_window hWmono hWlast

/--
Eq. (33), NYC preprocessing local-count-process deterministic-endpoint form:
if report counts are observable at each time, the first-report time has level
sets `{S <= t} = {1 <= N_t}`, and the fixed inspection/work-order endpoints
are after the first report pathwise, then the preprocessing rule defines a
stopping observation window.
Source status: Lean-checked paper-facing row.
-/
theorem equation33_nyc_preprocessing_stopping_observation_window_of_local_count_process
    {Ω : Type u} {mΩ : MeasurableSpace Ω}
    (𝓕 : Filtration (Ω := Ω) ℝ mΩ)
    (reportCount : ℝ → Ω → ℕ) (startTime : Ω → ℝ)
    (inspectionTime workOrderTime : ℝ)
    (h_count_measurable : ∀ t : ℝ, Measurable[𝓕 t] (reportCount t))
    (h_first_level_sets :
      ∀ t : ℝ, {ω | startTime ω ≤ t} = {ω | 1 ≤ reportCount t ω})
    (h_inspection : ∀ ω, startTime ω ≤ inspectionTime)
    (h_workOrder : ∀ ω, startTime ω ≤ workOrderTime) :
    ∃ W : StoppingObservationWindow 𝓕,
      W.startTime = startTime ∧
        W.endTime =
          (fun ω =>
            min (min (startTime ω + (100 : ℝ)) inspectionTime)
              workOrderTime) ∧
        ∀ ω, 0 ≤ W.exposure ω := by
  let W :=
    nycStoppingObservationWindowOfLocalCountProcess 𝓕 reportCount startTime
      (fun _ => inspectionTime) (fun _ => workOrderTime)
      h_count_measurable h_first_level_sets
      (IsStoppingTime.const inspectionTime) (IsStoppingTime.const workOrderTime)
      h_inspection h_workOrder
  refine ⟨W, rfl, ?_, fun ω => W.exposure_nonneg ω⟩
  funext ω
  rfl

/--
Eq. (33), NYC preprocessing: the constructed observation interval is capped at
100 days.
Source status: Lean-checked paper-facing row.
-/
theorem equation33_nyc_observation_exposure_le_100_days
    (startTime inspectionTime workOrderTime : ℝ)
    (h_inspection : startTime ≤ inspectionTime)
    (h_workOrder : startTime ≤ workOrderTime) :
    (nycObservationWindow startTime inspectionTime workOrderTime
      h_inspection h_workOrder).exposure ≤ (100 : ℝ) := by
  simpa [empiricalMaxObservationDurationDays] using
    nycObservationWindow_exposure_le_duration_cap
      startTime inspectionTime workOrderTime h_inspection h_workOrder

/--
Eq. (33), NYC preprocessing: if inspection and work-order times are strictly
after the start, the constructed observation interval has positive duration.
Source status: Lean-checked paper-facing row.
-/
theorem equation33_nyc_observation_exposure_pos
    (startTime inspectionTime workOrderTime : ℝ)
    (h_inspection : startTime < inspectionTime)
    (h_workOrder : startTime < workOrderTime) :
    0 <
      (nycObservationWindow startTime inspectionTime workOrderTime
        (le_of_lt h_inspection) (le_of_lt h_workOrder)).exposure :=
  nycObservationWindow_exposure_pos
    startTime inspectionTime workOrderTime h_inspection h_workOrder

/-- Eq. (33), NYC preprocessing: the observation end is before inspection.
Source status: Lean-checked paper-facing row.
-/
theorem equation33_nyc_observation_end_le_inspection
    (startTime inspectionTime workOrderTime : ℝ)
    (h_inspection : startTime ≤ inspectionTime)
    (h_workOrder : startTime ≤ workOrderTime) :
    (nycObservationWindow startTime inspectionTime workOrderTime
      h_inspection h_workOrder).endTime ≤ inspectionTime :=
  nycObservationWindow_endTime_le_inspection
    startTime inspectionTime workOrderTime h_inspection h_workOrder

/-- Eq. (33), NYC preprocessing: the observation end is before work order.
Source status: Lean-checked paper-facing row.
-/
theorem equation33_nyc_observation_end_le_work_order
    (startTime inspectionTime workOrderTime : ℝ)
    (h_inspection : startTime ≤ inspectionTime)
    (h_workOrder : startTime ≤ workOrderTime) :
    (nycObservationWindow startTime inspectionTime workOrderTime
      h_inspection h_workOrder).endTime ≤ workOrderTime :=
  nycObservationWindow_endTime_le_workOrder
    startTime inspectionTime workOrderTime h_inspection h_workOrder

/--
Eq. (33), NYC preprocessing: if inspection happens before the incident
lifetime endpoint, the constructed observation end lies inside the lifetime.
Source status: Lean-checked paper-facing row.
-/
theorem equation33_nyc_observation_end_le_lifetime_of_inspection_le
    (startTime inspectionTime workOrderTime lifetimeEnd : ℝ)
    (h_inspection : startTime ≤ inspectionTime)
    (h_workOrder : startTime ≤ workOrderTime)
    (h_inspection_lifetime : inspectionTime ≤ lifetimeEnd) :
    (nycObservationWindow startTime inspectionTime workOrderTime
      h_inspection h_workOrder).endTime ≤ lifetimeEnd :=
  nycObservationWindow_endTime_le_lifetime_of_inspection_le
    startTime inspectionTime workOrderTime lifetimeEnd
    h_inspection h_workOrder h_inspection_lifetime

/--
Eq. (33), NYC preprocessing: if the work-order time is before the incident
lifetime endpoint, the constructed observation end lies inside the lifetime.
Source status: Lean-checked paper-facing row.
-/
theorem equation33_nyc_observation_end_le_lifetime_of_work_order_le
    (startTime inspectionTime workOrderTime lifetimeEnd : ℝ)
    (h_inspection : startTime ≤ inspectionTime)
    (h_workOrder : startTime ≤ workOrderTime)
    (h_workOrder_lifetime : workOrderTime ≤ lifetimeEnd) :
    (nycObservationWindow startTime inspectionTime workOrderTime
      h_inspection h_workOrder).endTime ≤ lifetimeEnd :=
  nycObservationWindow_endTime_le_lifetime_of_workOrder_le
    startTime inspectionTime workOrderTime lifetimeEnd
    h_inspection h_workOrder h_workOrder_lifetime

/--
Eq. (33) finite-data count construction: for incidents whose exposures are
defined by the NYC preprocessing window, Lean constructs independent Poisson
counts and proves the collapsed total-count likelihood formula.
Source status: Lean-checked paper-facing row.
-/
theorem equation33_nyc_exists_finite_poisson_count_family_collapsed
    {Incident : Type u}
    (rate : ℝ) (h_rate : 0 ≤ rate)
    (startTime inspectionTime workOrderTime : Incident → ℝ)
    (h_inspection : ∀ i, startTime i ≤ inspectionTime i)
    (h_workOrder : ∀ i, startTime i ≤ workOrderTime i)
    (s : Finset Incident)
    (h_totalExposure :
      totalExposure s
        (fun i =>
          (nycObservationWindow (startTime i) (inspectionTime i)
            (workOrderTime i) (h_inspection i) (h_workOrder i)).exposure) ≠
          0) :
    ∃ Ω : Type u, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω,
      ∃ X : Incident → Ω → ℕ,
        (∀ i, Measurable (X i)) ∧
        (∀ i,
          ProbabilityTheory.HasLaw
            (X i)
            (ProbabilityTheory.poissonMeasure
              (rateExposureParam rate
                ((nycObservationWindow (startTime i) (inspectionTime i)
                  (workOrderTime i) (h_inspection i) (h_workOrder i)).exposure)
                (mul_nonneg h_rate
                  ((nycObservationWindow (startTime i) (inspectionTime i)
                    (workOrderTime i) (h_inspection i)
                    (h_workOrder i)).exposure_nonneg)))) P) ∧
        ProbabilityTheory.iIndepFun X P ∧ IsProbabilityMeasure P ∧
        ∀ k : Incident → ℕ,
          P.real (⋂ i ∈ s, {ω : Ω | X i ω = k i}) =
            (countLikelihoodProductResidual s
                (fun i =>
                  (nycObservationWindow (startTime i) (inspectionTime i)
                    (workOrderTime i) (h_inspection i)
                    (h_workOrder i)).exposure) k *
                ((totalCount s k).factorial : ℝ) /
                  (totalExposure s
                    (fun i =>
                      (nycObservationWindow (startTime i) (inspectionTime i)
                        (workOrderTime i) (h_inspection i)
                        (h_workOrder i)).exposure)) ^ totalCount s k) *
              countLikelihood rate
                (totalExposure s
                  (fun i =>
                    (nycObservationWindow (startTime i) (inspectionTime i)
                      (workOrderTime i) (h_inspection i)
                      (h_workOrder i)).exposure))
                (totalCount s k) := by
  exact
    theorem1_exists_independent_poisson_count_family_collapsed
      rate h_rate
      (fun i =>
        (nycObservationWindow (startTime i) (inspectionTime i)
          (workOrderTime i) (h_inspection i) (h_workOrder i)).exposure)
      (fun i =>
        (nycObservationWindow (startTime i) (inspectionTime i)
          (workOrderTime i) (h_inspection i)
          (h_workOrder i)).exposure_nonneg)
      s h_totalExposure

/--
Eq. (33) finite-data certificate form: the NYC preprocessing exposures admit
a reusable `FinitePoissonCountFamily` whose finite joint count likelihood
collapses to one total-count source Poisson PMF.
Source status: Lean-checked paper-facing row.
-/
theorem equation33_nyc_exists_finite_poisson_count_family_certificate_collapsed
    {Incident : Type u}
    (rate : ℝ) (h_rate : 0 ≤ rate)
    (startTime inspectionTime workOrderTime : Incident → ℝ)
    (h_inspection : ∀ i, startTime i ≤ inspectionTime i)
    (h_workOrder : ∀ i, startTime i ≤ workOrderTime i)
    (s : Finset Incident)
    (h_totalExposure :
      totalExposure s
        (fun i =>
          nycObservationExposure (startTime i) (inspectionTime i)
            (workOrderTime i) (h_inspection i) (h_workOrder i)) ≠ 0) :
    ∃ Ω : Type u, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω,
      ∃ H : FinitePoissonCountFamily Ω P Incident rate
          (fun i =>
            nycObservationExposure (startTime i) (inspectionTime i)
              (workOrderTime i) (h_inspection i) (h_workOrder i)),
        ∀ k : Incident → ℕ,
          P.real (⋂ i ∈ s, {ω : Ω | H.count i ω = k i}) =
            (countLikelihoodProductResidual s
                (fun i =>
                  nycObservationExposure (startTime i) (inspectionTime i)
                    (workOrderTime i) (h_inspection i) (h_workOrder i)) k *
                ((totalCount s k).factorial : ℝ) /
                  (totalExposure s
                    (fun i =>
                      nycObservationExposure (startTime i) (inspectionTime i)
                        (workOrderTime i) (h_inspection i)
                        (h_workOrder i))) ^ totalCount s k) *
              sourcePoissonPMF rate
                (totalExposure s
                  (fun i =>
                    nycObservationExposure (startTime i) (inspectionTime i)
                      (workOrderTime i) (h_inspection i)
                      (h_workOrder i)))
                (totalCount s k) := by
  simpa [sourcePoissonPMF, nycObservationExposure] using
    exists_finitePoissonCountFamily_joint_residual_real
      rate h_rate
      (fun i =>
        nycObservationExposure (startTime i) (inspectionTime i)
          (workOrderTime i) (h_inspection i) (h_workOrder i))
      (fun i =>
        nycObservationExposure_nonneg (startTime i) (inspectionTime i)
          (workOrderTime i) (h_inspection i) (h_workOrder i))
      s h_totalExposure

/--
Eq. (33) finite-data certificate form with the nonzero total exposure proved
from one strictly positive NYC observation window.
Source status: Lean-checked paper-facing row.
-/
theorem equation33_nyc_exists_finite_poisson_count_family_certificate_collapsed_of_exists_strict_window
    {Incident : Type u}
    (rate : ℝ) (h_rate : 0 ≤ rate)
    (startTime inspectionTime workOrderTime : Incident → ℝ)
    (h_inspection : ∀ i, startTime i ≤ inspectionTime i)
    (h_workOrder : ∀ i, startTime i ≤ workOrderTime i)
    (s : Finset Incident)
    (h_exists :
      ∃ i ∈ s, startTime i < inspectionTime i ∧
        startTime i < workOrderTime i) :
    ∃ Ω : Type u, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω,
      ∃ H : FinitePoissonCountFamily Ω P Incident rate
          (fun i =>
            nycObservationExposure (startTime i) (inspectionTime i)
              (workOrderTime i) (h_inspection i) (h_workOrder i)),
        ∀ k : Incident → ℕ,
          P.real (⋂ i ∈ s, {ω : Ω | H.count i ω = k i}) =
            (countLikelihoodProductResidual s
                (fun i =>
                  nycObservationExposure (startTime i) (inspectionTime i)
                    (workOrderTime i) (h_inspection i) (h_workOrder i)) k *
                ((totalCount s k).factorial : ℝ) /
                  (totalExposure s
                    (fun i =>
                      nycObservationExposure (startTime i) (inspectionTime i)
                        (workOrderTime i) (h_inspection i)
                        (h_workOrder i))) ^ totalCount s k) *
              sourcePoissonPMF rate
                (totalExposure s
                  (fun i =>
                    nycObservationExposure (startTime i) (inspectionTime i)
                      (workOrderTime i) (h_inspection i)
                      (h_workOrder i)))
                (totalCount s k) := by
  exact
    theorem1_exists_independent_poisson_count_family_certificate_collapsed_of_exists_pos_exposure
      rate h_rate
      (fun i =>
        nycObservationExposure (startTime i) (inspectionTime i)
          (workOrderTime i) (h_inspection i) (h_workOrder i))
      (fun i =>
        nycObservationExposure_nonneg (startTime i) (inspectionTime i)
          (workOrderTime i) (h_inspection i) (h_workOrder i))
      s
      (by
        rcases h_exists with ⟨i, hi, hstrict_inspection,
          hstrict_workOrder⟩
        refine ⟨i, hi, ?_⟩
        simpa [nycObservationExposure] using
          nycObservationExposure_pos
            (startTime i) (inspectionTime i) (workOrderTime i)
            hstrict_inspection hstrict_workOrder)

/--
Eq. (33) finite-data total-count construction: the total NYC observed report
count over any finite incident set has the source Poisson PMF at the total
preprocessed exposure.
Source status: Lean-checked paper-facing row.
-/
theorem equation33_nyc_exists_finite_poisson_total_count_pmf
    {Incident : Type u} [DecidableEq Incident]
    (rate : ℝ) (h_rate : 0 ≤ rate)
    (startTime inspectionTime workOrderTime : Incident → ℝ)
    (h_inspection : ∀ i, startTime i ≤ inspectionTime i)
    (h_workOrder : ∀ i, startTime i ≤ workOrderTime i)
    (s : Finset Incident) :
    ∃ Ω : Type u, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω,
      ∃ H : FinitePoissonCountFamily Ω P Incident rate
          (fun i =>
            nycObservationExposure (startTime i) (inspectionTime i)
              (workOrderTime i) (h_inspection i) (h_workOrder i)),
        ∀ totalReportCount : ℕ,
          P.real {ω : Ω |
              (∑ i ∈ s, H.count i ω) = totalReportCount} =
            sourcePoissonPMF rate
              (totalExposure s
                (fun i =>
                  nycObservationExposure (startTime i) (inspectionTime i)
                    (workOrderTime i) (h_inspection i) (h_workOrder i)))
              totalReportCount := by
  exact
    theorem1_exists_independent_poisson_count_family_certificate_total_count
      rate h_rate
      (fun i =>
        nycObservationExposure (startTime i) (inspectionTime i)
          (workOrderTime i) (h_inspection i) (h_workOrder i))
      (fun i =>
        nycObservationExposure_nonneg (startTime i) (inspectionTime i)
          (workOrderTime i) (h_inspection i) (h_workOrder i))
      s

/--
Eq. (33) MLE denominator check: if one NYC observation window is strictly
positive, the total preprocessed exposure is nonzero, so the displayed MLE
score equation applies to the total observed report count.
Source status: Lean-checked paper-facing row.
-/
theorem equation33_nyc_mle_score_equation_of_exists_strict_window
    {Incident : Type u}
    (totalReportCount : ℕ) (hcount : totalReportCount ≠ 0)
    (startTime inspectionTime workOrderTime : Incident → ℝ)
    (h_inspection : ∀ i, startTime i ≤ inspectionTime i)
    (h_workOrder : ∀ i, startTime i ≤ workOrderTime i)
    (s : Finset Incident)
    (h_exists :
      ∃ i ∈ s, startTime i < inspectionTime i ∧
        startTime i < workOrderTime i) :
    poissonRateScore totalReportCount
        (totalExposure s
          (fun i =>
            nycObservationExposure (startTime i) (inspectionTime i)
              (workOrderTime i) (h_inspection i) (h_workOrder i)))
        (mleRate totalReportCount
          (totalExposure s
            (fun i =>
              nycObservationExposure (startTime i) (inspectionTime i)
                (workOrderTime i) (h_inspection i) (h_workOrder i)))) = 0 := by
  exact
    equation3_mle_score_equation
      (totalCount := totalReportCount)
      (totalExposure := totalExposure s
        (fun i =>
          nycObservationExposure (startTime i) (inspectionTime i)
            (workOrderTime i) (h_inspection i) (h_workOrder i)))
      hcount
      (ne_of_gt
        (totalExposure_pos_of_exists_pos s
          (fun i =>
            nycObservationExposure (startTime i) (inspectionTime i)
              (workOrderTime i) (h_inspection i) (h_workOrder i))
          (fun i _hi =>
            nycObservationExposure_nonneg (startTime i) (inspectionTime i)
              (workOrderTime i) (h_inspection i) (h_workOrder i))
          (by
            rcases h_exists with ⟨i, hi, hstrict_inspection,
              hstrict_workOrder⟩
            refine ⟨i, hi, ?_⟩
            simpa [nycObservationExposure] using
              nycObservationExposure_pos
                (startTime i) (inspectionTime i) (workOrderTime i)
                hstrict_inspection hstrict_workOrder)))

/--
Eq. (33) MLE score equation for per-incident observed counts after NYC
preprocessing, with denominator positivity proved from one strictly positive
observation window.
Source status: Lean-checked paper-facing row.
-/
theorem equation33_nyc_observed_counts_mle_score_equation_of_exists_strict_window
    {Incident : Type u}
    (observedCount : Incident → ℕ)
    (startTime inspectionTime workOrderTime : Incident → ℝ)
    (h_inspection : ∀ i, startTime i ≤ inspectionTime i)
    (h_workOrder : ∀ i, startTime i ≤ workOrderTime i)
    (s : Finset Incident)
    (h_exists :
      ∃ i ∈ s, startTime i < inspectionTime i ∧
        startTime i < workOrderTime i)
    (hcount : totalCount s observedCount ≠ 0) :
    poissonRateScore (totalCount s observedCount)
        (totalExposure s
          (fun i =>
            nycObservationExposure (startTime i) (inspectionTime i)
              (workOrderTime i) (h_inspection i) (h_workOrder i)))
        (mleRate (totalCount s observedCount)
          (totalExposure s
            (fun i =>
              nycObservationExposure (startTime i) (inspectionTime i)
                (workOrderTime i) (h_inspection i) (h_workOrder i)))) = 0 := by
  exact
    theorem1_finite_exposure_count_family_mle_score_equation_of_exists_pos_exposure
      (fun i =>
        nycObservationExposure (startTime i) (inspectionTime i)
          (workOrderTime i) (h_inspection i) (h_workOrder i))
      observedCount
      (fun i =>
        nycObservationExposure_nonneg (startTime i) (inspectionTime i)
          (workOrderTime i) (h_inspection i) (h_workOrder i))
      s
      (by
        rcases h_exists with ⟨i, hi, hstrict_inspection,
          hstrict_workOrder⟩
        refine ⟨i, hi, ?_⟩
        simpa [nycObservationExposure] using
          nycObservationExposure_pos
            (startTime i) (inspectionTime i) (workOrderTime i)
            hstrict_inspection hstrict_workOrder)
      hcount

/--
Eq. (34), Chicago preprocessing stopping-time form: if the first-report time,
closed time, and dataset retrieval/update time are stopping times, then the
paper's min-censored preprocessing rule defines a stopping observation window.
Source status: Lean-checked paper-facing row.
-/
theorem equation34_chicago_preprocessing_stopping_observation_window
    {Ω : Type u} {mΩ : MeasurableSpace Ω}
    (𝓕 : Filtration (Ω := Ω) ℝ mΩ)
    (firstReportTime closedTime retrievalTime : Ω → ℝ)
    (h_firstReport : IsStoppingTime 𝓕 firstReportTime)
    (h_closed_stopping : IsStoppingTime 𝓕 closedTime)
    (h_retrieval_stopping : IsStoppingTime 𝓕 retrievalTime)
    (h_closed : ∀ ω, firstReportTime ω ≤ closedTime ω)
    (h_retrieval : ∀ ω, firstReportTime ω ≤ retrievalTime ω) :
    ∃ W : StoppingObservationWindow 𝓕,
      W.startTime = firstReportTime ∧
        W.endTime =
          (fun ω =>
            min (min (firstReportTime ω + (100 : ℝ)) (closedTime ω))
              (retrievalTime ω)) ∧
        ∀ ω, 0 ≤ W.exposure ω := by
  let W :=
    chicagoStoppingObservationWindow 𝓕 firstReportTime closedTime retrievalTime
      h_firstReport h_closed_stopping h_retrieval_stopping
      h_closed h_retrieval
  refine ⟨W, rfl, ?_, fun ω => W.exposure_nonneg ω⟩
  funext ω
  rfl

/--
Eq. (34), Chicago preprocessing deterministic-endpoint stopping-time form: if
the first-report time is a stopping time and the fixed closure/retrieval
endpoints are after it pathwise, then the preprocessing rule defines a
stopping observation window.
Source status: Lean-checked paper-facing row.
-/
theorem equation34_chicago_preprocessing_stopping_observation_window_of_deterministic_endpoints
    {Ω : Type u} {mΩ : MeasurableSpace Ω}
    (𝓕 : Filtration (Ω := Ω) ℝ mΩ)
    (firstReportTime : Ω → ℝ) (closedTime retrievalTime : ℝ)
    (h_firstReport : IsStoppingTime 𝓕 firstReportTime)
    (h_closed : ∀ ω, firstReportTime ω ≤ closedTime)
    (h_retrieval : ∀ ω, firstReportTime ω ≤ retrievalTime) :
    ∃ W : StoppingObservationWindow 𝓕,
      W.startTime = firstReportTime ∧
        W.endTime =
          (fun ω =>
            min (min (firstReportTime ω + (100 : ℝ)) closedTime)
              retrievalTime) ∧
        ∀ ω, 0 ≤ W.exposure ω := by
  let W :=
    chicagoStoppingObservationWindowOfDeterministicEndpoints 𝓕 firstReportTime
      closedTime retrievalTime h_firstReport h_closed h_retrieval
  refine ⟨W, rfl, ?_, fun ω => W.exposure_nonneg ω⟩
  funext ω
  rfl

/--
Eq. (34), Chicago preprocessing first-count-arrival form: if the first-report
time has the same level sets as an adapted report-count threshold event and
the fixed closure/retrieval endpoints are after it pathwise, then the
preprocessing rule defines a stopping observation window.
Source status: Lean-checked paper-facing row.
-/
theorem equation34_chicago_preprocessing_stopping_observation_window_of_first_count_arrival
    {Ω : Type u} {mΩ : MeasurableSpace Ω}
    (𝓕 : Filtration (Ω := Ω) ℝ mΩ)
    (reportCount : ℝ → Ω → ℕ) (firstReportTime : Ω → ℝ)
    (closedTime retrievalTime : ℝ)
    (C : FirstCountArrivalCertificate 𝓕 reportCount firstReportTime)
    (h_closed : ∀ ω, firstReportTime ω ≤ closedTime)
    (h_retrieval : ∀ ω, firstReportTime ω ≤ retrievalTime) :
    ∃ W : StoppingObservationWindow 𝓕,
      W.startTime = firstReportTime ∧
        W.endTime =
          (fun ω =>
            min (min (firstReportTime ω + (100 : ℝ)) closedTime)
              retrievalTime) ∧
        ∀ ω, 0 ≤ W.exposure ω := by
  let W :=
    chicagoStoppingObservationWindowOfFirstReportCountCertificate 𝓕
      reportCount firstReportTime closedTime retrievalTime C
      h_closed h_retrieval
  refine ⟨W, rfl, ?_, fun ω => W.exposure_nonneg ω⟩
  funext ω
  rfl

/--
Eq. (34), Chicago preprocessing local-count-process stopping-endpoint form: if
report counts are observable at each time, the first-report time has level sets
`{S <= t} = {1 <= N_t}`, and the closure/retrieval endpoint rules are stopping
times after the first report pathwise, then the preprocessing rule defines a
stopping observation window.
Source status: Lean-checked paper-facing row.
-/
theorem equation34_chicago_preprocessing_stopping_observation_window_of_local_count_process_stopping_endpoints
    {Ω : Type u} {mΩ : MeasurableSpace Ω}
    (𝓕 : Filtration (Ω := Ω) ℝ mΩ)
    (reportCount : ℝ → Ω → ℕ) (firstReportTime : Ω → ℝ)
    (closedTime retrievalTime : Ω → ℝ)
    (h_count_measurable : ∀ t : ℝ, Measurable[𝓕 t] (reportCount t))
    (h_first_level_sets :
      ∀ t : ℝ, {ω | firstReportTime ω ≤ t} = {ω | 1 ≤ reportCount t ω})
    (h_closed_stopping : IsStoppingTime 𝓕 closedTime)
    (h_retrieval_stopping : IsStoppingTime 𝓕 retrievalTime)
    (h_closed : ∀ ω, firstReportTime ω ≤ closedTime ω)
    (h_retrieval : ∀ ω, firstReportTime ω ≤ retrievalTime ω) :
    ∃ W : StoppingObservationWindow 𝓕,
      W.startTime = firstReportTime ∧
        W.endTime =
          (fun ω =>
            min (min (firstReportTime ω + (100 : ℝ)) (closedTime ω))
              (retrievalTime ω)) ∧
        ∀ ω, 0 ≤ W.exposure ω := by
  let W :=
    chicagoStoppingObservationWindowOfLocalCountProcess 𝓕 reportCount
      firstReportTime closedTime retrievalTime h_count_measurable
      h_first_level_sets h_closed_stopping h_retrieval_stopping h_closed
      h_retrieval
  refine ⟨W, rfl, ?_, fun ω => W.exposure_nonneg ω⟩
  funext ω
  rfl

/--
Eq. (34), Chicago preprocessing pathwise form from the local-count-process
stopping certificate: on every realized sample path, the certified stopping
window induces the deterministic observation window used by the finite
likelihood layer.
Source status: Lean-checked paper-facing row.
-/
theorem equation34_chicago_preprocessing_observation_window_of_local_count_process_at_sample
    {Ω : Type u} {mΩ : MeasurableSpace Ω}
    (𝓕 : Filtration (Ω := Ω) ℝ mΩ)
    (reportCount : ℝ → Ω → ℕ) (firstReportTime : Ω → ℝ)
    (closedTime retrievalTime : Ω → ℝ)
    (h_count_measurable : ∀ t : ℝ, Measurable[𝓕 t] (reportCount t))
    (h_first_level_sets :
      ∀ t : ℝ, {ω | firstReportTime ω ≤ t} = {ω | 1 ≤ reportCount t ω})
    (h_closed_stopping : IsStoppingTime 𝓕 closedTime)
    (h_retrieval_stopping : IsStoppingTime 𝓕 retrievalTime)
    (h_closed : ∀ ω, firstReportTime ω ≤ closedTime ω)
    (h_retrieval : ∀ ω, firstReportTime ω ≤ retrievalTime ω)
    (ω : Ω) :
    ∃ W : ObservationWindow,
      W.startTime = firstReportTime ω ∧
        W.endTime =
          min (min (firstReportTime ω + (100 : ℝ)) (closedTime ω))
            (retrievalTime ω) ∧
        0 ≤ W.exposure := by
  let Wstop :=
    chicagoStoppingObservationWindowOfLocalCountProcess 𝓕 reportCount
      firstReportTime closedTime retrievalTime h_count_measurable
      h_first_level_sets h_closed_stopping h_retrieval_stopping h_closed
      h_retrieval
  let W := Wstop.toObservationWindow ω
  refine ⟨W, rfl, ?_, W.exposure_nonneg⟩
  rfl

/--
Eq. (34), Chicago preprocessing zero-report likelihood bridge: the local-count
stopping certificate induces the pathwise observation window, and the
zero-report Appendix B.2 source-data row factors over that certified exposure.
Source status: Lean-checked paper-facing row.
-/
theorem equation34_chicago_zero_report_factorization_from_local_count_process_at_sample
    {Ω : Type u} {mΩ : MeasurableSpace Ω}
    (𝓕 : Filtration (Ω := Ω) ℝ mΩ)
    (K : Theorem2ConditionFunctions) (baseCount : ℕ)
    (reportCount : ℝ → Ω → ℕ) (firstReportTime : Ω → ℝ)
    (closedTime retrievalTime : Ω → ℝ)
    (h_count_measurable : ∀ t : ℝ, Measurable[𝓕 t] (reportCount t))
    (h_first_level_sets :
      ∀ t : ℝ, {ω | firstReportTime ω ≤ t} = {ω | 1 ≤ reportCount t ω})
    (h_closed_stopping : IsStoppingTime 𝓕 closedTime)
    (h_retrieval_stopping : IsStoppingTime 𝓕 retrievalTime)
    (h_closed : ∀ ω, firstReportTime ω ≤ closedTime ω)
    (h_retrieval : ∀ ω, firstReportTime ω ≤ retrievalTime ω)
    (ω : Ω) (rate : ℝ) :
    ∃ W : ObservationWindow,
      W.startTime = firstReportTime ω ∧
        W.endTime =
          min (min (firstReportTime ω + (100 : ℝ)) (closedTime ω))
            (retrievalTime ω) ∧
        (K.zeroReportSourceDataFromWindow baseCount W).likelihood rate =
          theorem2ZeroReportResidual K.startDensity (K.endDensity baseCount) *
            sourcePoissonPMF rate W.exposure 0 := by
  let Wstop :=
    chicagoStoppingObservationWindowOfLocalCountProcess 𝓕 reportCount
      firstReportTime closedTime retrievalTime h_count_measurable
      h_first_level_sets h_closed_stopping h_retrieval_stopping h_closed
      h_retrieval
  let W := Wstop.toObservationWindow ω
  refine ⟨W, rfl, ?_, ?_⟩
  · rfl
  · exact theorem2_zero_report_stopping_window_at_sample_factorization_explicit
      K baseCount Wstop ω rate

/--
Eq. (34), Chicago preprocessing one-report likelihood bridge: under explicit
observed-jump ordering in the certified pathwise preprocessing window, the
Appendix B.2 one-report source-data row factors over the certified exposure.
Source status: Lean-checked paper-facing row.
-/
theorem equation34_chicago_one_report_factorization_from_local_count_process_at_sample
    {Ω : Type u} {mΩ : MeasurableSpace Ω}
    (𝓕 : Filtration (Ω := Ω) ℝ mΩ)
    (K : Theorem2ConditionFunctions) (baseCount : ℕ)
    (reportCount : ℝ → Ω → ℕ) (firstReportTime : Ω → ℝ)
    (closedTime retrievalTime : Ω → ℝ)
    (h_count_measurable : ∀ t : ℝ, Measurable[𝓕 t] (reportCount t))
    (h_first_level_sets :
      ∀ t : ℝ, {ω | firstReportTime ω ≤ t} = {ω | 1 ≤ reportCount t ω})
    (h_closed_stopping : IsStoppingTime 𝓕 closedTime)
    (h_retrieval_stopping : IsStoppingTime 𝓕 retrievalTime)
    (h_closed : ∀ ω, firstReportTime ω ≤ closedTime ω)
    (h_retrieval : ∀ ω, firstReportTime ω ≤ retrievalTime ω)
    (ω : Ω) {firstJumpTime rate : ℝ}
    (h_window :
      firstReportTime ω <
        min (min (firstReportTime ω + (100 : ℝ)) (closedTime ω))
          (retrievalTime ω))
    (h_start_le_jump : firstReportTime ω ≤ firstJumpTime)
    (h_jump_le_end :
      firstJumpTime ≤
        min (min (firstReportTime ω + (100 : ℝ)) (closedTime ω))
          (retrievalTime ω)) :
    ∃ W : ObservationWindow,
      ∃ hW_window : W.startTime < W.endTime,
      ∃ hW_start_le_jump : W.startTime ≤ firstJumpTime,
      ∃ hW_jump_le_end : firstJumpTime ≤ W.endTime,
      W.startTime = firstReportTime ω ∧
        W.endTime =
          min (min (firstReportTime ω + (100 : ℝ)) (closedTime ω))
            (retrievalTime ω) ∧
        (K.oneReportSourceDataFromOrderedWindow baseCount
          W.startTime W.endTime firstJumpTime hW_window
          hW_start_le_jump hW_jump_le_end).likelihood rate =
          (K.oneReportSourceDataFromOrderedWindow baseCount
            W.startTime W.endTime firstJumpTime hW_window
            hW_start_le_jump hW_jump_le_end).residual *
            sourcePoissonPMF rate W.exposure 1 := by
  let Wstop :=
    chicagoStoppingObservationWindowOfLocalCountProcess 𝓕 reportCount
      firstReportTime closedTime retrievalTime h_count_measurable
      h_first_level_sets h_closed_stopping h_retrieval_stopping h_closed
      h_retrieval
  let W := Wstop.toObservationWindow ω
  have hW_window : W.startTime < W.endTime := by
    change Wstop.startTime ω < Wstop.endTime ω
    change firstReportTime ω <
      min (min (firstReportTime ω + empiricalMaxObservationDurationDays)
        (closedTime ω)) (retrievalTime ω)
    simpa [empiricalMaxObservationDurationDays] using h_window
  have hW_start_le_jump : W.startTime ≤ firstJumpTime := by
    change Wstop.startTime ω ≤ firstJumpTime
    change firstReportTime ω ≤ firstJumpTime
    exact h_start_le_jump
  have hW_jump_le_end : firstJumpTime ≤ W.endTime := by
    change firstJumpTime ≤ Wstop.endTime ω
    change firstJumpTime ≤
      min (min (firstReportTime ω + empiricalMaxObservationDurationDays)
        (closedTime ω)) (retrievalTime ω)
    simpa [empiricalMaxObservationDurationDays] using h_jump_le_end
  refine ⟨W, hW_window, hW_start_le_jump, hW_jump_le_end, rfl, ?_, ?_⟩
  · rfl
  · exact theorem2_one_report_stopping_window_at_sample_factorization
      K baseCount Wstop ω
      hW_window hW_start_le_jump hW_jump_le_end

/--
Eq. (34), Chicago preprocessing multi-report likelihood bridge: under explicit
ordered observed-jump timeline premises in the certified pathwise preprocessing
window, the Appendix B.2 multi-report source-data row factors over the
certified exposure.
Source status: Lean-checked paper-facing row.
-/
theorem equation34_chicago_multi_report_factorization_from_local_count_process_at_sample
    {Ω : Type u} {mΩ : MeasurableSpace Ω}
    (𝓕 : Filtration (Ω := Ω) ℝ mΩ)
    (K : Theorem2ConditionFunctions) (baseCount count : ℕ)
    (hcount : 1 < count)
    (reportCount : ℝ → Ω → ℕ) (firstReportTime : Ω → ℝ)
    (closedTime retrievalTime : Ω → ℝ)
    (h_count_measurable : ∀ t : ℝ, Measurable[𝓕 t] (reportCount t))
    (h_first_level_sets :
      ∀ t : ℝ, {ω | firstReportTime ω ≤ t} = {ω | 1 ≤ reportCount t ω})
    (h_closed_stopping : IsStoppingTime 𝓕 closedTime)
    (h_retrieval_stopping : IsStoppingTime 𝓕 retrievalTime)
    (h_closed : ∀ ω, firstReportTime ω ≤ closedTime ω)
    (h_retrieval : ∀ ω, firstReportTime ω ≤ retrievalTime ω)
    (ω : Ω) (jumpTime : ℕ → ℝ) {rate : ℝ}
    (h_window :
      firstReportTime ω <
        min (min (firstReportTime ω + (100 : ℝ)) (closedTime ω))
          (retrievalTime ω))
    (hmono : Monotone (jumpTimelineEndpoint (firstReportTime ω) jumpTime))
    (hlast :
      jumpTimelineEndpoint (firstReportTime ω) jumpTime count ≤
        min (min (firstReportTime ω + (100 : ℝ)) (closedTime ω))
          (retrievalTime ω)) :
    ∃ W : ObservationWindow,
      ∃ hW_window : W.startTime < W.endTime,
      ∃ hWmono : Monotone (jumpTimelineEndpoint W.startTime jumpTime),
      ∃ hWlast : jumpTimelineEndpoint W.startTime jumpTime count ≤ W.endTime,
      W.startTime = firstReportTime ω ∧
        W.endTime =
          min (min (firstReportTime ω + (100 : ℝ)) (closedTime ω))
            (retrievalTime ω) ∧
        (K.multiReportSourceDataFromOrderedWindow baseCount count hcount
          W.startTime W.endTime jumpTime hW_window hWmono hWlast).likelihood rate =
          (K.multiReportSourceDataFromOrderedWindow baseCount count hcount
            W.startTime W.endTime jumpTime hW_window hWmono hWlast).residual *
            sourcePoissonPMF rate W.exposure count := by
  let Wstop :=
    chicagoStoppingObservationWindowOfLocalCountProcess 𝓕 reportCount
      firstReportTime closedTime retrievalTime h_count_measurable
      h_first_level_sets h_closed_stopping h_retrieval_stopping h_closed
      h_retrieval
  let W := Wstop.toObservationWindow ω
  have hW_window : W.startTime < W.endTime := by
    change Wstop.startTime ω < Wstop.endTime ω
    change firstReportTime ω <
      min (min (firstReportTime ω + empiricalMaxObservationDurationDays)
        (closedTime ω)) (retrievalTime ω)
    simpa [empiricalMaxObservationDurationDays] using h_window
  have hWmono : Monotone (jumpTimelineEndpoint W.startTime jumpTime) := by
    change Monotone (jumpTimelineEndpoint (Wstop.startTime ω) jumpTime)
    change Monotone (jumpTimelineEndpoint (firstReportTime ω) jumpTime)
    exact hmono
  have hWlast :
      jumpTimelineEndpoint W.startTime jumpTime count ≤ W.endTime := by
    change jumpTimelineEndpoint (Wstop.startTime ω) jumpTime count ≤
      Wstop.endTime ω
    change jumpTimelineEndpoint (firstReportTime ω) jumpTime count ≤
      min (min (firstReportTime ω + empiricalMaxObservationDurationDays)
        (closedTime ω)) (retrievalTime ω)
    simpa [empiricalMaxObservationDurationDays] using hlast
  refine ⟨W, hW_window, hWmono, hWlast, rfl, ?_, ?_⟩
  · rfl
  · exact theorem2_multi_report_stopping_window_at_sample_factorization
      K baseCount count hcount Wstop ω jumpTime
      hW_window hWmono hWlast

/--
Eq. (34), Chicago preprocessing local-count-process deterministic-endpoint
form: if report counts are observable at each time, the first-report time has
level sets `{S <= t} = {1 <= N_t}`, and the fixed closure/retrieval endpoints
are after the first report pathwise, then the preprocessing rule defines a
stopping observation window.
Source status: Lean-checked paper-facing row.
-/
theorem equation34_chicago_preprocessing_stopping_observation_window_of_local_count_process
    {Ω : Type u} {mΩ : MeasurableSpace Ω}
    (𝓕 : Filtration (Ω := Ω) ℝ mΩ)
    (reportCount : ℝ → Ω → ℕ) (firstReportTime : Ω → ℝ)
    (closedTime retrievalTime : ℝ)
    (h_count_measurable : ∀ t : ℝ, Measurable[𝓕 t] (reportCount t))
    (h_first_level_sets :
      ∀ t : ℝ, {ω | firstReportTime ω ≤ t} = {ω | 1 ≤ reportCount t ω})
    (h_closed : ∀ ω, firstReportTime ω ≤ closedTime)
    (h_retrieval : ∀ ω, firstReportTime ω ≤ retrievalTime) :
    ∃ W : StoppingObservationWindow 𝓕,
      W.startTime = firstReportTime ∧
        W.endTime =
          (fun ω =>
            min (min (firstReportTime ω + (100 : ℝ)) closedTime)
              retrievalTime) ∧
        ∀ ω, 0 ≤ W.exposure ω := by
  let W :=
    chicagoStoppingObservationWindowOfLocalCountProcess 𝓕 reportCount
      firstReportTime (fun _ => closedTime) (fun _ => retrievalTime)
      h_count_measurable h_first_level_sets
      (IsStoppingTime.const closedTime) (IsStoppingTime.const retrievalTime)
      h_closed h_retrieval
  refine ⟨W, rfl, ?_, fun ω => W.exposure_nonneg ω⟩
  funext ω
  rfl

/--
Eq. (34), Chicago preprocessing: the constructed observation interval is
capped at 100 days.
Source status: Lean-checked paper-facing row.
-/
theorem equation34_chicago_observation_exposure_le_100_days
    (firstReportTime closedTime retrievalTime : ℝ)
    (h_closed : firstReportTime ≤ closedTime)
    (h_retrieval : firstReportTime ≤ retrievalTime) :
    (chicagoObservationWindow firstReportTime closedTime retrievalTime
      h_closed h_retrieval).exposure ≤ (100 : ℝ) := by
  simpa [empiricalMaxObservationDurationDays] using
    chicagoObservationWindow_exposure_le_duration_cap
      firstReportTime closedTime retrievalTime h_closed h_retrieval

/--
Eq. (34), Chicago preprocessing: if closing and retrieval/update times are
strictly after the first report, the constructed observation interval has
positive duration.
Source status: Lean-checked paper-facing row.
-/
theorem equation34_chicago_observation_exposure_pos
    (firstReportTime closedTime retrievalTime : ℝ)
    (h_closed : firstReportTime < closedTime)
    (h_retrieval : firstReportTime < retrievalTime) :
    0 <
      (chicagoObservationWindow firstReportTime closedTime retrievalTime
        (le_of_lt h_closed) (le_of_lt h_retrieval)).exposure :=
  chicagoObservationWindow_exposure_pos
    firstReportTime closedTime retrievalTime h_closed h_retrieval

/-- Eq. (34), Chicago preprocessing: the observation end is before closing.
Source status: Lean-checked paper-facing row.
-/
theorem equation34_chicago_observation_end_le_closed
    (firstReportTime closedTime retrievalTime : ℝ)
    (h_closed : firstReportTime ≤ closedTime)
    (h_retrieval : firstReportTime ≤ retrievalTime) :
    (chicagoObservationWindow firstReportTime closedTime retrievalTime
      h_closed h_retrieval).endTime ≤ closedTime :=
  chicagoObservationWindow_endTime_le_closed
    firstReportTime closedTime retrievalTime h_closed h_retrieval

/--
Eq. (34), Chicago preprocessing: the observation end is before the dataset
retrieval/update time.
Source status: Lean-checked paper-facing row.
-/
theorem equation34_chicago_observation_end_le_retrieval
    (firstReportTime closedTime retrievalTime : ℝ)
    (h_closed : firstReportTime ≤ closedTime)
    (h_retrieval : firstReportTime ≤ retrievalTime) :
    (chicagoObservationWindow firstReportTime closedTime retrievalTime
      h_closed h_retrieval).endTime ≤ retrievalTime :=
  chicagoObservationWindow_endTime_le_retrieval
    firstReportTime closedTime retrievalTime h_closed h_retrieval

/--
Eq. (34), Chicago preprocessing: if closing happens before the incident
lifetime endpoint, the constructed observation end lies inside the lifetime.
Source status: Lean-checked paper-facing row.
-/
theorem equation34_chicago_observation_end_le_lifetime_of_closed_le
    (firstReportTime closedTime retrievalTime lifetimeEnd : ℝ)
    (h_closed : firstReportTime ≤ closedTime)
    (h_retrieval : firstReportTime ≤ retrievalTime)
    (h_closed_lifetime : closedTime ≤ lifetimeEnd) :
    (chicagoObservationWindow firstReportTime closedTime retrievalTime
      h_closed h_retrieval).endTime ≤ lifetimeEnd :=
  chicagoObservationWindow_endTime_le_lifetime_of_closed_le
    firstReportTime closedTime retrievalTime lifetimeEnd
    h_closed h_retrieval h_closed_lifetime

/--
Eq. (34) finite-data count construction: for incidents whose exposures are
defined by the Chicago preprocessing window, Lean constructs independent
Poisson counts and proves the collapsed total-count likelihood formula.
Source status: Lean-checked paper-facing row.
-/
theorem equation34_chicago_exists_finite_poisson_count_family_collapsed
    {Incident : Type u}
    (rate : ℝ) (h_rate : 0 ≤ rate)
    (firstReportTime closedTime retrievalTime : Incident → ℝ)
    (h_closed : ∀ i, firstReportTime i ≤ closedTime i)
    (h_retrieval : ∀ i, firstReportTime i ≤ retrievalTime i)
    (s : Finset Incident)
    (h_totalExposure :
      totalExposure s
        (fun i =>
          (chicagoObservationWindow (firstReportTime i) (closedTime i)
            (retrievalTime i) (h_closed i) (h_retrieval i)).exposure) ≠
          0) :
    ∃ Ω : Type u, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω,
      ∃ X : Incident → Ω → ℕ,
        (∀ i, Measurable (X i)) ∧
        (∀ i,
          ProbabilityTheory.HasLaw
            (X i)
            (ProbabilityTheory.poissonMeasure
              (rateExposureParam rate
                ((chicagoObservationWindow (firstReportTime i)
                  (closedTime i) (retrievalTime i) (h_closed i)
                  (h_retrieval i)).exposure)
                (mul_nonneg h_rate
                  ((chicagoObservationWindow (firstReportTime i)
                    (closedTime i) (retrievalTime i) (h_closed i)
                    (h_retrieval i)).exposure_nonneg)))) P) ∧
        ProbabilityTheory.iIndepFun X P ∧ IsProbabilityMeasure P ∧
        ∀ k : Incident → ℕ,
          P.real (⋂ i ∈ s, {ω : Ω | X i ω = k i}) =
            (countLikelihoodProductResidual s
                (fun i =>
                  (chicagoObservationWindow (firstReportTime i)
                    (closedTime i) (retrievalTime i) (h_closed i)
                    (h_retrieval i)).exposure) k *
                ((totalCount s k).factorial : ℝ) /
                  (totalExposure s
                    (fun i =>
                      (chicagoObservationWindow (firstReportTime i)
                        (closedTime i) (retrievalTime i) (h_closed i)
                        (h_retrieval i)).exposure)) ^ totalCount s k) *
              countLikelihood rate
                (totalExposure s
                  (fun i =>
                    (chicagoObservationWindow (firstReportTime i)
                      (closedTime i) (retrievalTime i) (h_closed i)
                      (h_retrieval i)).exposure))
                (totalCount s k) := by
  exact
    theorem1_exists_independent_poisson_count_family_collapsed
      rate h_rate
      (fun i =>
        (chicagoObservationWindow (firstReportTime i) (closedTime i)
          (retrievalTime i) (h_closed i) (h_retrieval i)).exposure)
      (fun i =>
        (chicagoObservationWindow (firstReportTime i) (closedTime i)
          (retrievalTime i) (h_closed i) (h_retrieval i)).exposure_nonneg)
      s h_totalExposure

/--
Eq. (34) finite-data certificate form: the Chicago preprocessing exposures
admit a reusable `FinitePoissonCountFamily` whose finite joint count likelihood
collapses to one total-count source Poisson PMF.
Source status: Lean-checked paper-facing row.
-/
theorem equation34_chicago_exists_finite_poisson_count_family_certificate_collapsed
    {Incident : Type u}
    (rate : ℝ) (h_rate : 0 ≤ rate)
    (firstReportTime closedTime retrievalTime : Incident → ℝ)
    (h_closed : ∀ i, firstReportTime i ≤ closedTime i)
    (h_retrieval : ∀ i, firstReportTime i ≤ retrievalTime i)
    (s : Finset Incident)
    (h_totalExposure :
      totalExposure s
        (fun i =>
          chicagoObservationExposure (firstReportTime i) (closedTime i)
            (retrievalTime i) (h_closed i) (h_retrieval i)) ≠ 0) :
    ∃ Ω : Type u, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω,
      ∃ H : FinitePoissonCountFamily Ω P Incident rate
          (fun i =>
            chicagoObservationExposure (firstReportTime i) (closedTime i)
              (retrievalTime i) (h_closed i) (h_retrieval i)),
        ∀ k : Incident → ℕ,
          P.real (⋂ i ∈ s, {ω : Ω | H.count i ω = k i}) =
            (countLikelihoodProductResidual s
                (fun i =>
                  chicagoObservationExposure (firstReportTime i)
                    (closedTime i) (retrievalTime i) (h_closed i)
                    (h_retrieval i)) k *
                ((totalCount s k).factorial : ℝ) /
                  (totalExposure s
                    (fun i =>
                      chicagoObservationExposure (firstReportTime i)
                        (closedTime i) (retrievalTime i) (h_closed i)
                        (h_retrieval i))) ^ totalCount s k) *
              sourcePoissonPMF rate
                (totalExposure s
                  (fun i =>
                    chicagoObservationExposure (firstReportTime i)
                      (closedTime i) (retrievalTime i) (h_closed i)
                      (h_retrieval i)))
                (totalCount s k) := by
  simpa [sourcePoissonPMF, chicagoObservationExposure] using
    exists_finitePoissonCountFamily_joint_residual_real
      rate h_rate
      (fun i =>
        chicagoObservationExposure (firstReportTime i) (closedTime i)
          (retrievalTime i) (h_closed i) (h_retrieval i))
      (fun i =>
        chicagoObservationExposure_nonneg (firstReportTime i) (closedTime i)
          (retrievalTime i) (h_closed i) (h_retrieval i))
      s h_totalExposure

/--
Eq. (34) finite-data certificate form with the nonzero total exposure proved
from one strictly positive Chicago observation window.
Source status: Lean-checked paper-facing row.
-/
theorem equation34_chicago_exists_finite_poisson_count_family_certificate_collapsed_of_exists_strict_window
    {Incident : Type u}
    (rate : ℝ) (h_rate : 0 ≤ rate)
    (firstReportTime closedTime retrievalTime : Incident → ℝ)
    (h_closed : ∀ i, firstReportTime i ≤ closedTime i)
    (h_retrieval : ∀ i, firstReportTime i ≤ retrievalTime i)
    (s : Finset Incident)
    (h_exists :
      ∃ i ∈ s, firstReportTime i < closedTime i ∧
        firstReportTime i < retrievalTime i) :
    ∃ Ω : Type u, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω,
      ∃ H : FinitePoissonCountFamily Ω P Incident rate
          (fun i =>
            chicagoObservationExposure (firstReportTime i) (closedTime i)
              (retrievalTime i) (h_closed i) (h_retrieval i)),
        ∀ k : Incident → ℕ,
          P.real (⋂ i ∈ s, {ω : Ω | H.count i ω = k i}) =
            (countLikelihoodProductResidual s
                (fun i =>
                  chicagoObservationExposure (firstReportTime i)
                    (closedTime i) (retrievalTime i) (h_closed i)
                    (h_retrieval i)) k *
                ((totalCount s k).factorial : ℝ) /
                  (totalExposure s
                    (fun i =>
                      chicagoObservationExposure (firstReportTime i)
                        (closedTime i) (retrievalTime i) (h_closed i)
                        (h_retrieval i))) ^ totalCount s k) *
              sourcePoissonPMF rate
                (totalExposure s
                  (fun i =>
                    chicagoObservationExposure (firstReportTime i)
                      (closedTime i) (retrievalTime i) (h_closed i)
                      (h_retrieval i)))
                (totalCount s k) := by
  exact
    theorem1_exists_independent_poisson_count_family_certificate_collapsed_of_exists_pos_exposure
      rate h_rate
      (fun i =>
        chicagoObservationExposure (firstReportTime i) (closedTime i)
          (retrievalTime i) (h_closed i) (h_retrieval i))
      (fun i =>
        chicagoObservationExposure_nonneg (firstReportTime i) (closedTime i)
          (retrievalTime i) (h_closed i) (h_retrieval i))
      s
      (by
        rcases h_exists with ⟨i, hi, hstrict_closed,
          hstrict_retrieval⟩
        refine ⟨i, hi, ?_⟩
        simpa [chicagoObservationExposure] using
          chicagoObservationExposure_pos
            (firstReportTime i) (closedTime i) (retrievalTime i)
            hstrict_closed hstrict_retrieval)

/--
Eq. (34) finite-data total-count construction: the total Chicago observed
report count over any finite incident set has the source Poisson PMF at the
total preprocessed exposure.
Source status: Lean-checked paper-facing row.
-/
theorem equation34_chicago_exists_finite_poisson_total_count_pmf
    {Incident : Type u} [DecidableEq Incident]
    (rate : ℝ) (h_rate : 0 ≤ rate)
    (firstReportTime closedTime retrievalTime : Incident → ℝ)
    (h_closed : ∀ i, firstReportTime i ≤ closedTime i)
    (h_retrieval : ∀ i, firstReportTime i ≤ retrievalTime i)
    (s : Finset Incident) :
    ∃ Ω : Type u, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω,
      ∃ H : FinitePoissonCountFamily Ω P Incident rate
          (fun i =>
            chicagoObservationExposure (firstReportTime i) (closedTime i)
              (retrievalTime i) (h_closed i) (h_retrieval i)),
        ∀ totalReportCount : ℕ,
          P.real {ω : Ω |
              (∑ i ∈ s, H.count i ω) = totalReportCount} =
            sourcePoissonPMF rate
              (totalExposure s
                (fun i =>
                  chicagoObservationExposure (firstReportTime i)
                    (closedTime i) (retrievalTime i) (h_closed i)
                    (h_retrieval i)))
              totalReportCount := by
  exact
    theorem1_exists_independent_poisson_count_family_certificate_total_count
      rate h_rate
      (fun i =>
        chicagoObservationExposure (firstReportTime i) (closedTime i)
          (retrievalTime i) (h_closed i) (h_retrieval i))
      (fun i =>
        chicagoObservationExposure_nonneg (firstReportTime i) (closedTime i)
          (retrievalTime i) (h_closed i) (h_retrieval i))
      s

/--
Eq. (34) MLE denominator check: if one Chicago observation window is strictly
positive, the total preprocessed exposure is nonzero, so the displayed MLE
score equation applies to the total observed report count.
Source status: Lean-checked paper-facing row.
-/
theorem equation34_chicago_mle_score_equation_of_exists_strict_window
    {Incident : Type u}
    (totalReportCount : ℕ) (hcount : totalReportCount ≠ 0)
    (firstReportTime closedTime retrievalTime : Incident → ℝ)
    (h_closed : ∀ i, firstReportTime i ≤ closedTime i)
    (h_retrieval : ∀ i, firstReportTime i ≤ retrievalTime i)
    (s : Finset Incident)
    (h_exists :
      ∃ i ∈ s, firstReportTime i < closedTime i ∧
        firstReportTime i < retrievalTime i) :
    poissonRateScore totalReportCount
        (totalExposure s
          (fun i =>
            chicagoObservationExposure (firstReportTime i) (closedTime i)
              (retrievalTime i) (h_closed i) (h_retrieval i)))
        (mleRate totalReportCount
          (totalExposure s
            (fun i =>
              chicagoObservationExposure (firstReportTime i) (closedTime i)
                (retrievalTime i) (h_closed i) (h_retrieval i)))) = 0 := by
  exact
    equation3_mle_score_equation
      (totalCount := totalReportCount)
      (totalExposure := totalExposure s
        (fun i =>
          chicagoObservationExposure (firstReportTime i) (closedTime i)
            (retrievalTime i) (h_closed i) (h_retrieval i)))
      hcount
      (ne_of_gt
        (totalExposure_pos_of_exists_pos s
          (fun i =>
            chicagoObservationExposure (firstReportTime i) (closedTime i)
              (retrievalTime i) (h_closed i) (h_retrieval i))
          (fun i _hi =>
            chicagoObservationExposure_nonneg (firstReportTime i) (closedTime i)
              (retrievalTime i) (h_closed i) (h_retrieval i))
          (by
            rcases h_exists with ⟨i, hi, hstrict_closed,
              hstrict_retrieval⟩
            refine ⟨i, hi, ?_⟩
            simpa [chicagoObservationExposure] using
              chicagoObservationExposure_pos
                (firstReportTime i) (closedTime i) (retrievalTime i)
                hstrict_closed hstrict_retrieval)))

/--
Eq. (34) MLE score equation for per-incident observed counts after Chicago
preprocessing, with denominator positivity proved from one strictly positive
observation window.
Source status: Lean-checked paper-facing row.
-/
theorem equation34_chicago_observed_counts_mle_score_equation_of_exists_strict_window
    {Incident : Type u}
    (observedCount : Incident → ℕ)
    (firstReportTime closedTime retrievalTime : Incident → ℝ)
    (h_closed : ∀ i, firstReportTime i ≤ closedTime i)
    (h_retrieval : ∀ i, firstReportTime i ≤ retrievalTime i)
    (s : Finset Incident)
    (h_exists :
      ∃ i ∈ s, firstReportTime i < closedTime i ∧
        firstReportTime i < retrievalTime i)
    (hcount : totalCount s observedCount ≠ 0) :
    poissonRateScore (totalCount s observedCount)
        (totalExposure s
          (fun i =>
            chicagoObservationExposure (firstReportTime i) (closedTime i)
              (retrievalTime i) (h_closed i) (h_retrieval i)))
        (mleRate (totalCount s observedCount)
          (totalExposure s
            (fun i =>
              chicagoObservationExposure (firstReportTime i) (closedTime i)
                (retrievalTime i) (h_closed i) (h_retrieval i)))) = 0 := by
  exact
    theorem1_finite_exposure_count_family_mle_score_equation_of_exists_pos_exposure
      (fun i =>
        chicagoObservationExposure (firstReportTime i) (closedTime i)
          (retrievalTime i) (h_closed i) (h_retrieval i))
      observedCount
      (fun i =>
        chicagoObservationExposure_nonneg (firstReportTime i) (closedTime i)
          (retrievalTime i) (h_closed i) (h_retrieval i))
      s
      (by
        rcases h_exists with ⟨i, hi, hstrict_closed,
          hstrict_retrieval⟩
        refine ⟨i, hi, ?_⟩
        simpa [chicagoObservationExposure] using
          chicagoObservationExposure_pos
            (firstReportTime i) (closedTime i) (retrievalTime i)
            hstrict_closed hstrict_retrieval)
      hcount

/--
Zero-report Appendix B.2 source-data bookkeeping: constructing the source row
from an observation window preserves the window exposure and carries report
count zero.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_zero_report_window_source_data_exposure_count
    (K : Theorem2ConditionFunctions) (baseCount : ℕ)
    (W : ObservationWindow) :
    (K.zeroReportSourceDataFromWindow baseCount W).exposure = W.exposure ∧
      (K.zeroReportSourceDataFromWindow baseCount W).count = 0 := by
  exact ⟨
    Theorem2ConditionFunctions.zeroReportSourceDataFromWindow_exposure
      K baseCount W,
    Theorem2ConditionFunctions.zeroReportSourceDataFromWindow_count
      K baseCount W⟩

/--
One-report ordered-window Appendix B.2 source-data bookkeeping: the constructor
preserves the original observation exposure and carries report count one.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_one_report_ordered_window_source_data_exposure_count
    (K : Theorem2ConditionFunctions) (baseCount : ℕ)
    {startTime endTime firstJumpTime : ℝ}
    (h_window : startTime < endTime)
    (h_start_le_jump : startTime ≤ firstJumpTime)
    (h_jump_le_end : firstJumpTime ≤ endTime) :
    (K.oneReportSourceDataFromOrderedWindow baseCount
        startTime endTime firstJumpTime h_window
        h_start_le_jump h_jump_le_end).exposure =
        observationExposure startTime endTime ∧
      (K.oneReportSourceDataFromOrderedWindow baseCount
        startTime endTime firstJumpTime h_window
        h_start_le_jump h_jump_le_end).count = 1 := by
  exact ⟨
    Theorem2ConditionFunctions.oneReportSourceDataFromOrderedWindow_exposure
      K baseCount h_window h_start_le_jump h_jump_le_end,
    Theorem2ConditionFunctions.oneReportSourceDataFromOrderedWindow_count
      K baseCount h_window h_start_le_jump h_jump_le_end⟩

/--
Multi-report ordered-window Appendix B.2 source-data bookkeeping: the
constructor preserves the original observation exposure and supplied report
count.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_multi_report_ordered_window_source_data_exposure_count
    (K : Theorem2ConditionFunctions) (baseCount count : ℕ)
    (hcount : 1 < count)
    {startTime endTime : ℝ} (jumpTime : ℕ → ℝ)
    (h_window : startTime < endTime)
    (hmono : Monotone (jumpTimelineEndpoint startTime jumpTime))
    (hlast : jumpTimelineEndpoint startTime jumpTime count ≤ endTime) :
    (K.multiReportSourceDataFromOrderedWindow baseCount count hcount
        startTime endTime jumpTime h_window hmono hlast).exposure =
        observationExposure startTime endTime ∧
      (K.multiReportSourceDataFromOrderedWindow baseCount count hcount
        startTime endTime jumpTime h_window hmono hlast).count =
        count := by
  exact ⟨
    Theorem2ConditionFunctions.multiReportSourceDataFromOrderedWindow_exposure
      K baseCount count hcount jumpTime h_window hmono hlast,
    Theorem2ConditionFunctions.multiReportSourceDataFromOrderedWindow_count
      K baseCount count hcount jumpTime h_window hmono hlast⟩

/--
Appendix B.2 zero-report row with the count and exposure written explicitly:
the row contributes the zero-count source Poisson PMF over the observation
window exposure.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_zero_report_window_factorization_explicit_exposure_count
    (K : Theorem2ConditionFunctions) (baseCount : ℕ)
    (W : ObservationWindow) (rate : ℝ) :
    (K.zeroReportSourceDataFromWindow baseCount W).likelihood rate =
      (K.zeroReportSourceDataFromWindow baseCount W).residual *
        sourcePoissonPMF rate W.exposure 0 := by
  rw [theorem2_zero_report_condition_functions_factorization K baseCount W rate]
  rw [Theorem2ConditionFunctions.zeroReportSourceDataFromWindow_exposure]
  rw [Theorem2ConditionFunctions.zeroReportSourceDataFromWindow_count]

/--
Appendix B.2 zero-report row with the residual, exposure, and count all
written explicitly.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_zero_report_window_factorization_explicit
    (K : Theorem2ConditionFunctions) (baseCount : ℕ)
    (W : ObservationWindow) (rate : ℝ) :
    (K.zeroReportSourceDataFromWindow baseCount W).likelihood rate =
      theorem2ZeroReportResidual K.startDensity (K.endDensity baseCount) *
        sourcePoissonPMF rate W.exposure 0 := by
  rw [theorem2_zero_report_window_factorization_explicit_exposure_count]
  rw [Theorem2ConditionFunctions.zeroReportSourceDataFromWindow_residual]

/--
Appendix B.2 one-report ordered-window row with the count and exposure written
explicitly: the row contributes the one-count source Poisson PMF over
`endTime - startTime`.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_one_report_ordered_window_factorization_explicit_exposure_count
    (K : Theorem2ConditionFunctions) (baseCount : ℕ)
    {startTime endTime firstJumpTime rate : ℝ}
    (h_window : startTime < endTime)
    (h_start_le_jump : startTime ≤ firstJumpTime)
    (h_jump_le_end : firstJumpTime ≤ endTime) :
    (K.oneReportSourceDataFromOrderedWindow baseCount
        startTime endTime firstJumpTime h_window
        h_start_le_jump h_jump_le_end).likelihood rate =
      (K.oneReportSourceDataFromOrderedWindow baseCount
          startTime endTime firstJumpTime h_window
          h_start_le_jump h_jump_le_end).residual *
        sourcePoissonPMF rate (observationExposure startTime endTime) 1 := by
  rw [theorem2_one_report_proper_window_factorization
    K baseCount h_window h_start_le_jump h_jump_le_end]
  rw [Theorem2ConditionFunctions.oneReportSourceDataFromOrderedWindow_exposure]
  rw [Theorem2ConditionFunctions.oneReportSourceDataFromOrderedWindow_count]

/--
Appendix B.2 one-report ordered-window row with the corrected residual,
exposure, and count all written explicitly.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_one_report_ordered_window_factorization_explicit
    (K : Theorem2ConditionFunctions) (baseCount : ℕ)
    {startTime endTime firstJumpTime rate : ℝ}
    (h_window : startTime < endTime)
    (h_start_le_jump : startTime ≤ firstJumpTime)
    (h_jump_le_end : firstJumpTime ≤ endTime) :
    (K.oneReportSourceDataFromOrderedWindow baseCount
        startTime endTime firstJumpTime h_window
        h_start_le_jump h_jump_le_end).likelihood rate =
      (theorem2OneReportKernelResidual
          K.startDensity (K.endDensity (baseCount + 1))
          (K.survivalIntegral baseCount) /
        observationExposure startTime endTime) *
        sourcePoissonPMF rate (observationExposure startTime endTime) 1 := by
  rw [theorem2_one_report_ordered_window_factorization_explicit_exposure_count]
  rw [Theorem2ConditionFunctions.oneReportSourceDataFromOrderedWindow_residual]

/--
Appendix B.2 multi-report ordered-window row with the count and exposure
written explicitly: the row contributes the `M`-count source Poisson PMF over
`endTime - startTime`.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_multi_report_ordered_window_factorization_explicit_exposure_count
    (K : Theorem2ConditionFunctions) (baseCount count : ℕ)
    (hcount : 1 < count)
    {startTime endTime rate : ℝ} (jumpTime : ℕ → ℝ)
    (h_window : startTime < endTime)
    (hmono : Monotone (jumpTimelineEndpoint startTime jumpTime))
    (hlast : jumpTimelineEndpoint startTime jumpTime count ≤ endTime) :
    (K.multiReportSourceDataFromOrderedWindow baseCount count hcount
        startTime endTime jumpTime h_window hmono hlast).likelihood rate =
      (K.multiReportSourceDataFromOrderedWindow baseCount count hcount
          startTime endTime jumpTime h_window hmono hlast).residual *
        sourcePoissonPMF rate (observationExposure startTime endTime) count := by
  rw [theorem2_multi_report_proper_window_factorization
    K baseCount count hcount jumpTime h_window hmono hlast]
  rw [Theorem2ConditionFunctions.multiReportSourceDataFromOrderedWindow_exposure]
  rw [Theorem2ConditionFunctions.multiReportSourceDataFromOrderedWindow_count]

/--
Appendix B.2 multi-report ordered-window row with the corrected residual,
exposure, and count all written explicitly.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_multi_report_ordered_window_factorization_explicit
    (K : Theorem2ConditionFunctions) (baseCount count : ℕ)
    (hcount : 1 < count)
    {startTime endTime rate : ℝ} (jumpTime : ℕ → ℝ)
    (h_window : startTime < endTime)
    (hmono : Monotone (jumpTimelineEndpoint startTime jumpTime))
    (hlast : jumpTimelineEndpoint startTime jumpTime count ≤ endTime) :
    (K.multiReportSourceDataFromOrderedWindow baseCount count hcount
        startTime endTime jumpTime h_window hmono hlast).likelihood rate =
      theorem2CorrectedResidual
        (theorem2MultiReportKernelResidual
          K.startDensity (K.endDensity (baseCount + count))
          (K.survivalIntegralProduct baseCount count))
        (observationExposure startTime endTime) count *
        sourcePoissonPMF rate (observationExposure startTime endTime) count := by
  rw [theorem2_multi_report_ordered_window_factorization_explicit_exposure_count]
  rw [Theorem2ConditionFunctions.multiReportSourceDataFromOrderedWindow_residual]

/--
Appendix B.2 zero-report row over the deterministic observation window
realized by a certified stopping observation window on one sample path.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_zero_report_stopping_window_at_sample_factorization_row
    {Ω : Type u} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration (Ω := Ω) ℝ mΩ}
    (K : Theorem2ConditionFunctions) (baseCount : ℕ)
    (W : StoppingObservationWindow 𝓕) (ω : Ω) (rate : ℝ) :
    (K.zeroReportSourceDataFromWindow baseCount
        (W.toObservationWindow ω)).likelihood rate =
      theorem2ZeroReportResidual K.startDensity (K.endDensity baseCount) *
        sourcePoissonPMF rate (W.exposure ω) 0 :=
  theorem2_zero_report_stopping_window_at_sample_factorization_explicit
    K baseCount W ω rate

/--
Appendix B.2 one-report row over the deterministic observation window realized
by a certified stopping observation window on one sample path.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_one_report_stopping_window_at_sample_factorization_row
    {Ω : Type u} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration (Ω := Ω) ℝ mΩ}
    (K : Theorem2ConditionFunctions) (baseCount : ℕ)
    (W : StoppingObservationWindow 𝓕) (ω : Ω)
    {firstJumpTime rate : ℝ}
    (h_window : W.startTime ω < W.endTime ω)
    (h_start_le_jump : W.startTime ω ≤ firstJumpTime)
    (h_jump_le_end : firstJumpTime ≤ W.endTime ω) :
    (K.oneReportSourceDataFromOrderedWindow baseCount
        (W.startTime ω) (W.endTime ω) firstJumpTime h_window
        h_start_le_jump h_jump_le_end).likelihood rate =
      (K.oneReportSourceDataFromOrderedWindow baseCount
          (W.startTime ω) (W.endTime ω) firstJumpTime h_window
          h_start_le_jump h_jump_le_end).residual *
        sourcePoissonPMF rate (W.exposure ω) 1 :=
  theorem2_one_report_stopping_window_at_sample_factorization
    K baseCount W ω h_window h_start_le_jump h_jump_le_end

/--
Appendix B.2 multi-report row over the deterministic observation window
realized by a certified stopping observation window on one sample path.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_multi_report_stopping_window_at_sample_factorization_row
    {Ω : Type u} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration (Ω := Ω) ℝ mΩ}
    (K : Theorem2ConditionFunctions) (baseCount count : ℕ)
    (hcount : 1 < count)
    (W : StoppingObservationWindow 𝓕) (ω : Ω)
    (jumpTime : ℕ → ℝ) {rate : ℝ}
    (h_window : W.startTime ω < W.endTime ω)
    (hmono : Monotone (jumpTimelineEndpoint (W.startTime ω) jumpTime))
    (hlast : jumpTimelineEndpoint (W.startTime ω) jumpTime count ≤
      W.endTime ω) :
    (K.multiReportSourceDataFromOrderedWindow baseCount count hcount
        (W.startTime ω) (W.endTime ω) jumpTime h_window hmono hlast).likelihood rate =
      (K.multiReportSourceDataFromOrderedWindow baseCount count hcount
          (W.startTime ω) (W.endTime ω) jumpTime h_window hmono hlast).residual *
        sourcePoissonPMF rate (W.exposure ω) count :=
  theorem2_multi_report_stopping_window_at_sample_factorization
    K baseCount count hcount W ω jumpTime h_window hmono hlast

/--
Appendix B.2 one-report jump-time factorization under the paper-natural
ordered-window conditions: the window is proper and the observed first jump
lies inside it.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_one_report_proper_window_factorization_row
    (K : Theorem2ConditionFunctions) (baseCount : ℕ)
    {startTime endTime firstJumpTime rate : ℝ}
    (h_window : startTime < endTime)
    (h_start_le_jump : startTime ≤ firstJumpTime)
    (h_jump_le_end : firstJumpTime ≤ endTime) :
    (K.oneReportSourceDataFromOrderedWindow baseCount
        startTime endTime firstJumpTime h_window
        h_start_le_jump h_jump_le_end).likelihood rate =
      (K.oneReportSourceDataFromOrderedWindow baseCount
          startTime endTime firstJumpTime h_window
          h_start_le_jump h_jump_le_end).residual *
        sourcePoissonPMF rate
          (K.oneReportSourceDataFromOrderedWindow baseCount
            startTime endTime firstJumpTime h_window
            h_start_le_jump h_jump_le_end).exposure
          (K.oneReportSourceDataFromOrderedWindow baseCount
            startTime endTime firstJumpTime h_window
            h_start_le_jump h_jump_le_end).count := by
  exact theorem2_one_report_proper_window_factorization
    K baseCount h_window h_start_le_jump h_jump_le_end

/--
Appendix B.2 multi-report jump-time factorization under the paper-natural
ordered-window conditions: the window is proper, observed jump endpoints are
monotone, and the last observed endpoint lies before the window closes.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_multi_report_proper_window_factorization_row
    (K : Theorem2ConditionFunctions) (baseCount count : ℕ)
    (hcount : 1 < count)
    {startTime endTime rate : ℝ} (jumpTime : ℕ → ℝ)
    (h_window : startTime < endTime)
    (hmono : Monotone (jumpTimelineEndpoint startTime jumpTime))
    (hlast : jumpTimelineEndpoint startTime jumpTime count ≤ endTime) :
    (K.multiReportSourceDataFromOrderedWindow baseCount count hcount
        startTime endTime jumpTime h_window hmono hlast).likelihood rate =
      (K.multiReportSourceDataFromOrderedWindow baseCount count hcount
          startTime endTime jumpTime h_window hmono hlast).residual *
        sourcePoissonPMF rate
          (K.multiReportSourceDataFromOrderedWindow baseCount count hcount
            startTime endTime jumpTime h_window hmono hlast).exposure
          (K.multiReportSourceDataFromOrderedWindow baseCount count hcount
            startTime endTime jumpTime h_window hmono hlast).count := by
  exact theorem2_multi_report_proper_window_factorization
    K baseCount count hcount jumpTime h_window hmono hlast

/--
Theorem 1 finite-product form from mathlib Poisson increment laws: under the
paper's homogeneous Poisson process plus Condition 1/2 source assumptions, a
finite product of observed zero/one/multi-report window cases collapses to one
total-count Poisson PMF, up to a rate-independent residual.
Source status: Lean-checked paper-facing row.
-/
theorem theorem1_likelihood_product_decomposition_from_poisson_increment_laws
    {Ω Incident : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : HomogeneousPoissonCountingProcessByLaw Ω P)
    (K : Theorem2ConditionFunctions)
    (s : Finset Incident) (C : Incident → Theorem2ObservedWindowCase)
    (h_totalExposure :
      totalExposure s (fun i => (C i).exposureWith K) ≠ 0) :
    (∏ i ∈ s, (C i).likelihoodFromPoissonIncrementLaws K H) =
      Theorem2ObservedWindowCase.productResidualWith K s C *
        sourcePoissonPMF H.rate
          (totalExposure s fun i => (C i).exposureWith K)
          (totalCount s fun i => (C i).countWith K) := by
  exact Theorem2ObservedWindowCase.product_factorizationFromPoissonIncrementLaws
    K H s C h_totalExposure

/--
Finite-product provenance bridge: the product of likelihoods induced by
mathlib Poisson increment laws is termwise the process-free condition-function
rate likelihood product at the primitive process rate.
Source status: Lean-checked paper-facing row.
-/
theorem theorem1_likelihood_product_from_poisson_increment_laws_eq_condition_function_rate_likelihood_product
    {Ω Incident : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : HomogeneousPoissonCountingProcessByLaw Ω P)
    (K : Theorem2ConditionFunctions)
    (s : Finset Incident) (C : Incident → Theorem2ObservedWindowCase) :
    (∏ i ∈ s, (C i).likelihoodFromPoissonIncrementLaws K H) =
      ∏ i ∈ s, (C i).rateLikelihoodWith K H.rate := by
  exact
    Theorem2ObservedWindowCase.product_likelihoodFromPoissonIncrementLaws_eq_productRateLikelihoodWith
      K H s C

theorem theorem1_likelihood_product_decomposition_from_poisson_increment_laws_of_exists_pos_exposure
    {Ω Incident : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : HomogeneousPoissonCountingProcessByLaw Ω P)
    (K : Theorem2ConditionFunctions)
    (s : Finset Incident) (C : Incident → Theorem2ObservedWindowCase)
    (h_exists : ∃ i ∈ s, 0 < (C i).exposureWith K) :
    (∏ i ∈ s, (C i).likelihoodFromPoissonIncrementLaws K H) =
      Theorem2ObservedWindowCase.productResidualWith K s C *
        sourcePoissonPMF H.rate
          (totalExposure s fun i => (C i).exposureWith K)
          (totalCount s fun i => (C i).countWith K) := by
  exact
    Theorem2ObservedWindowCase.product_factorizationFromPoissonIncrementLaws_of_exists_pos_exposure
      K H s C h_exists

/--
Theorem 1 finite-product form without a continuous-time process object: after
Condition 1/2 functions are attached, the product of rate-parametric
zero/one/multi-report likelihood kernels collapses to one total-count source
Poisson PMF.
Source status: Lean-checked paper-facing row.
-/
theorem theorem1_rate_likelihood_product_decomposition_with_condition_functions
    {Incident : Type*}
    (K : Theorem2ConditionFunctions) (rate : ℝ)
    (s : Finset Incident) (C : Incident → Theorem2ObservedWindowCase)
    (h_totalExposure :
      totalExposure s (fun i => (C i).exposureWith K) ≠ 0) :
    (∏ i ∈ s, (C i).rateLikelihoodWith K rate) =
      Theorem2ObservedWindowCase.productResidualWith K s C *
        sourcePoissonPMF rate
          (totalExposure s fun i => (C i).exposureWith K)
          (totalCount s fun i => (C i).countWith K) := by
  exact Theorem2ObservedWindowCase.product_rateLikelihoodWith_factorization
    K rate s C h_totalExposure

/--
Theorem 1 process-free finite-product form, with nonzero total exposure
derived from one observed-window case with positive exposure.
Source status: Lean-checked paper-facing row.
-/
theorem theorem1_rate_likelihood_product_decomposition_with_condition_functions_of_exists_pos_exposure
    {Incident : Type*}
    (K : Theorem2ConditionFunctions) (rate : ℝ)
    (s : Finset Incident) (C : Incident → Theorem2ObservedWindowCase)
    (h_exists : ∃ i ∈ s, 0 < (C i).exposureWith K) :
    (∏ i ∈ s, (C i).rateLikelihoodWith K rate) =
      Theorem2ObservedWindowCase.productResidualWith K s C *
        sourcePoissonPMF rate
          (totalExposure s fun i => (C i).exposureWith K)
          (totalCount s fun i => (C i).countWith K) := by
  exact
    Theorem2ObservedWindowCase.product_rateLikelihoodWith_factorization_of_exists_pos_exposure
      K rate s C h_exists

/--
Theorem 1 finite-product form from a homogeneous Poisson process law and
rate-independent Condition 1/2 functions: the product of zero/one/multi-report
window likelihoods collapses to one total-count source Poisson PMF.
Source status: Lean-checked paper-facing row.
-/
theorem theorem1_likelihood_product_decomposition_from_process_law
    {Ω Incident : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : HomogeneousPoissonProcessLaw Ω P)
    (K : Theorem2ConditionFunctions)
    (s : Finset Incident) (C : Incident → Theorem2ObservedWindowCase)
    (h_totalExposure :
      totalExposure s (fun i => (C i).exposureWith K) ≠ 0) :
    (∏ i ∈ s, (C i).likelihoodWith K H) =
      Theorem2ObservedWindowCase.productResidualWith K s C *
        sourcePoissonPMF H.rate
          (totalExposure s fun i => (C i).exposureWith K)
          (totalCount s fun i => (C i).countWith K) := by
  exact Theorem2ObservedWindowCase.product_factorizationWith
    K H s C h_totalExposure

/--
Theorem 1 finite-product form from a homogeneous Poisson process law, with
nonzero total exposure derived from one observed-window case with positive
exposure.
Source status: Lean-checked paper-facing row.
-/
theorem theorem1_likelihood_product_decomposition_from_process_law_of_exists_pos_exposure
    {Ω Incident : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : HomogeneousPoissonProcessLaw Ω P)
    (K : Theorem2ConditionFunctions)
    (s : Finset Incident) (C : Incident → Theorem2ObservedWindowCase)
    (h_exists : ∃ i ∈ s, 0 < (C i).exposureWith K) :
    (∏ i ∈ s, (C i).likelihoodWith K H) =
      Theorem2ObservedWindowCase.productResidualWith K s C *
        sourcePoissonPMF H.rate
          (totalExposure s fun i => (C i).exposureWith K)
          (totalCount s fun i => (C i).countWith K) := by
  exact
    Theorem2ObservedWindowCase.product_factorizationWith_of_exists_pos_exposure
      K H s C h_exists

/--
Theorem 1 finite-count construction form: if the finite incident Poisson count
family is constructed with exposures matching the observed-window cases, then
the product likelihood is the product of individual non-Poisson residuals
times the joint observed count-event probability.
Source status: Lean-checked paper-facing row.
-/
theorem theorem1_rate_likelihood_product_from_finite_poisson_count_family
    {Ω Incident : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (K : Theorem2ConditionFunctions) {rate : ℝ}
    (s : Finset Incident) (C : Incident → Theorem2ObservedWindowCase)
    (H : FinitePoissonCountFamily Ω P Incident rate
      (fun i => (C i).exposureWith K)) :
    (∏ i ∈ s, (C i).rateLikelihoodWith K rate) =
      Theorem2ObservedWindowCase.productIndividualResidualWith K s C *
        P.real (⋂ i ∈ s, {ω : Ω | H.count i ω = (C i).countWith K}) := by
  exact
    Theorem2ObservedWindowCase.product_rateLikelihoodWith_eq_productIndividualResidual_mul_countEvent_prob
      K s C H

/--
Theorem 1 finite-count construction after collapsing count vectors: if the
finite incident Poisson count family is constructed with exposures matching
the observed-window cases, then the product likelihood is the collapsed paper
residual times the probability of the observed total count.
Source status: Lean-checked paper-facing row.
-/
theorem theorem1_rate_likelihood_product_from_finite_poisson_count_family_total_count
    {Ω Incident : Type*} [MeasurableSpace Ω] [DecidableEq Incident]
    {P : Measure Ω} (K : Theorem2ConditionFunctions) {rate : ℝ}
    (s : Finset Incident) (C : Incident → Theorem2ObservedWindowCase)
    (H : FinitePoissonCountFamily Ω P Incident rate
      (fun i => (C i).exposureWith K))
    (h_totalExposure :
      totalExposure s (fun i => (C i).exposureWith K) ≠ 0) :
    (∏ i ∈ s, (C i).rateLikelihoodWith K rate) =
      Theorem2ObservedWindowCase.productResidualWith K s C *
        P.real {ω : Ω |
          (∑ i ∈ s, H.count i ω) =
            totalCount s (fun i => (C i).countWith K)} := by
  exact
    Theorem2ObservedWindowCase.product_rateLikelihoodWith_eq_productResidual_mul_totalCountEvent_prob
      K s C H h_totalExposure

/--
Theorem 1 finite-count construction after collapsing count vectors, with
nonzero total exposure derived from one observed-window case with positive
exposure.
Source status: Lean-checked paper-facing row.
-/
theorem theorem1_rate_likelihood_product_from_finite_poisson_count_family_total_count_of_exists_pos_exposure
    {Ω Incident : Type*} [MeasurableSpace Ω] [DecidableEq Incident]
    {P : Measure Ω} (K : Theorem2ConditionFunctions) {rate : ℝ}
    (s : Finset Incident) (C : Incident → Theorem2ObservedWindowCase)
    (H : FinitePoissonCountFamily Ω P Incident rate
      (fun i => (C i).exposureWith K))
    (h_exists : ∃ i ∈ s, 0 < (C i).exposureWith K) :
    (∏ i ∈ s, (C i).rateLikelihoodWith K rate) =
      Theorem2ObservedWindowCase.productResidualWith K s C *
        P.real {ω : Ω |
          (∑ i ∈ s, H.count i ω) =
            totalCount s (fun i => (C i).countWith K)} := by
  exact
    Theorem2ObservedWindowCase.product_rateLikelihoodWith_eq_productResidual_mul_totalCountEvent_prob_of_exists_pos_exposure
      K s C H h_exists

/--
Theorem 1 finite-count construction exists for any finite observed-window
family and nonnegative reporting rate: the required independent Poisson count
family is built in Lean by the reusable product-space construction.
Source status: Lean-checked paper-facing row.
-/
theorem theorem1_exists_finite_poisson_count_family_for_observed_windows
    {Incident : Type u}
    (rate : ℝ) (h_rate : 0 ≤ rate)
    (K : Theorem2ConditionFunctions)
    (s : Finset Incident) (C : Incident → Theorem2ObservedWindowCase) :
    ∃ Ω : Type u, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω,
      ∃ H : FinitePoissonCountFamily Ω P Incident rate
          (fun i => (C i).exposureWith K),
        (∏ i ∈ s, (C i).rateLikelihoodWith K rate) =
          Theorem2ObservedWindowCase.productIndividualResidualWith K s C *
            P.real (⋂ i ∈ s,
              {ω : Ω | H.count i ω = (C i).countWith K}) := by
  rcases exists_finitePoissonCountFamily
      rate h_rate (fun i => (C i).exposureWith K)
      (fun i => (C i).exposureWith_nonneg K) with
    ⟨Ω, mΩ, P, H, _⟩
  exact ⟨Ω, mΩ, P, H,
    theorem1_rate_likelihood_product_from_finite_poisson_count_family
      K s C H⟩

/--
Theorem 1 finite-count construction exists in the collapsed total-count-event
form: Lean constructs the independent finite Poisson count family and proves
that the observed-window product likelihood is the collapsed paper residual
times the probability of the observed total count.
Source status: Lean-checked paper-facing row.
-/
theorem theorem1_exists_finite_poisson_count_family_for_observed_windows_total_count_event
    {Incident : Type u} [DecidableEq Incident]
    (rate : ℝ) (h_rate : 0 ≤ rate)
    (K : Theorem2ConditionFunctions)
    (s : Finset Incident) (C : Incident → Theorem2ObservedWindowCase)
    (h_totalExposure :
      totalExposure s (fun i => (C i).exposureWith K) ≠ 0) :
    ∃ Ω : Type u, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω,
      ∃ H : FinitePoissonCountFamily Ω P Incident rate
          (fun i => (C i).exposureWith K),
        (∏ i ∈ s, (C i).rateLikelihoodWith K rate) =
          Theorem2ObservedWindowCase.productResidualWith K s C *
            P.real {ω : Ω |
              (∑ i ∈ s, H.count i ω) =
                totalCount s (fun i => (C i).countWith K)} := by
  rcases exists_finitePoissonCountFamily
      rate h_rate (fun i => (C i).exposureWith K)
      (fun i => (C i).exposureWith_nonneg K) with
    ⟨Ω, mΩ, P, H, _⟩
  exact ⟨Ω, mΩ, P, H,
    theorem1_rate_likelihood_product_from_finite_poisson_count_family_total_count
      K s C H h_totalExposure⟩

/--
Theorem 1 finite-count construction exists in total-count-event form, deriving
nonzero total exposure from one observed-window case with positive exposure.
Source status: Lean-checked paper-facing row.
-/
theorem theorem1_exists_finite_poisson_count_family_for_observed_windows_total_count_event_of_exists_pos_exposure
    {Incident : Type u} [DecidableEq Incident]
    (rate : ℝ) (h_rate : 0 ≤ rate)
    (K : Theorem2ConditionFunctions)
    (s : Finset Incident) (C : Incident → Theorem2ObservedWindowCase)
    (h_exists : ∃ i ∈ s, 0 < (C i).exposureWith K) :
    ∃ Ω : Type u, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω,
      ∃ H : FinitePoissonCountFamily Ω P Incident rate
          (fun i => (C i).exposureWith K),
        (∏ i ∈ s, (C i).rateLikelihoodWith K rate) =
          Theorem2ObservedWindowCase.productResidualWith K s C *
            P.real {ω : Ω |
              (∑ i ∈ s, H.count i ω) =
                totalCount s (fun i => (C i).countWith K)} := by
  exact
    theorem1_exists_finite_poisson_count_family_for_observed_windows_total_count_event
      rate h_rate K s C
      (ne_of_gt
        (totalExposure_pos_of_exists_pos s
          (fun i => (C i).exposureWith K)
          (fun i _hi => (C i).exposureWith_nonneg K)
          h_exists))

/--
Consolidated finite-data Theorem 1 route: for a nonnegative reporting rate
and finite observed-window family, Lean constructs the independent finite
Poisson count family and proves both the joint count-event formula and the
collapsed total-count source-PMF likelihood formula.
Source status: Lean-checked paper-facing row.
-/
theorem theorem1_exists_finite_poisson_count_family_for_observed_windows_total_pmf
    {Incident : Type u}
    (rate : ℝ) (h_rate : 0 ≤ rate)
    (K : Theorem2ConditionFunctions)
    (s : Finset Incident) (C : Incident → Theorem2ObservedWindowCase)
    (h_totalExposure :
      totalExposure s (fun i => (C i).exposureWith K) ≠ 0) :
    ∃ Ω : Type u, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω,
      ∃ H : FinitePoissonCountFamily Ω P Incident rate
          (fun i => (C i).exposureWith K),
        P.real (⋂ i ∈ s, {ω : Ω | H.count i ω = (C i).countWith K}) =
            (countLikelihoodProductResidual s
                (fun i => (C i).exposureWith K)
                (fun i => (C i).countWith K) *
                ((totalCount s fun i => (C i).countWith K).factorial : ℝ) /
                  (totalExposure s fun i => (C i).exposureWith K) ^
                    totalCount s (fun i => (C i).countWith K)) *
              sourcePoissonPMF rate
                (totalExposure s fun i => (C i).exposureWith K)
                (totalCount s fun i => (C i).countWith K) ∧
          (∏ i ∈ s, (C i).rateLikelihoodWith K rate) =
            Theorem2ObservedWindowCase.productResidualWith K s C *
              sourcePoissonPMF rate
                (totalExposure s fun i => (C i).exposureWith K)
                (totalCount s fun i => (C i).countWith K) := by
  rcases exists_finitePoissonCountFamily
      rate h_rate (fun i => (C i).exposureWith K)
      (fun i => (C i).exposureWith_nonneg K) with
    ⟨Ω, mΩ, P, H, _⟩
  refine ⟨Ω, mΩ, P, H, ?_, ?_⟩
  · simpa [sourcePoissonPMF] using
      H.joint_real_eq_residual_countLikelihood_total
        s h_totalExposure (fun i => (C i).countWith K)
  · exact
      theorem1_rate_likelihood_product_decomposition_with_condition_functions
        K rate s C h_totalExposure

/--
Consolidated finite-data Theorem 1 route with nonzero total exposure derived
from one observed-window case with positive exposure.
Source status: Lean-checked paper-facing row.
-/
theorem theorem1_exists_finite_poisson_count_family_for_observed_windows_total_pmf_of_exists_pos_exposure
    {Incident : Type u}
    (rate : ℝ) (h_rate : 0 ≤ rate)
    (K : Theorem2ConditionFunctions)
    (s : Finset Incident) (C : Incident → Theorem2ObservedWindowCase)
    (h_exists : ∃ i ∈ s, 0 < (C i).exposureWith K) :
    ∃ Ω : Type u, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω,
      ∃ H : FinitePoissonCountFamily Ω P Incident rate
          (fun i => (C i).exposureWith K),
        P.real (⋂ i ∈ s, {ω : Ω | H.count i ω = (C i).countWith K}) =
            (countLikelihoodProductResidual s
                (fun i => (C i).exposureWith K)
                (fun i => (C i).countWith K) *
                ((totalCount s fun i => (C i).countWith K).factorial : ℝ) /
                  (totalExposure s fun i => (C i).exposureWith K) ^
                    totalCount s (fun i => (C i).countWith K)) *
              sourcePoissonPMF rate
                (totalExposure s fun i => (C i).exposureWith K)
                (totalCount s fun i => (C i).countWith K) ∧
          (∏ i ∈ s, (C i).rateLikelihoodWith K rate) =
            Theorem2ObservedWindowCase.productResidualWith K s C *
              sourcePoissonPMF rate
                (totalExposure s fun i => (C i).exposureWith K)
                (totalCount s fun i => (C i).countWith K) := by
  exact
    theorem1_exists_finite_poisson_count_family_for_observed_windows_total_pmf
      rate h_rate K s C
      (ne_of_gt
        (totalExposure_pos_of_exists_pos s
          (fun i => (C i).exposureWith K)
          (fun i _hi => (C i).exposureWith_nonneg K)
          h_exists))

/--
Theorem 1 finite-product form directly from the explicit source-vocabulary
Condition 1/2 model, with a raw nonzero total-exposure premise.
Source status: Lean-checked paper-facing row.
-/
theorem theorem1_rate_likelihood_product_decomposition_with_condition_source_model
    {Incident : Type*}
    (M : Theorem2ConditionSourceModel) (rate : ℝ)
    (s : Finset Incident) (C : Incident → Theorem2ObservedWindowCase)
    (h_totalExposure :
      totalExposure s (fun i =>
        (C i).exposureWith
          M.toConditionFunctionSemantics.toConditionFunctions) ≠ 0) :
    (∏ i ∈ s,
        (C i).rateLikelihoodWith
          M.toConditionFunctionSemantics.toConditionFunctions rate) =
      Theorem2ObservedWindowCase.productResidualWith
          M.toConditionFunctionSemantics.toConditionFunctions s C *
        sourcePoissonPMF rate
          (totalExposure s fun i =>
            (C i).exposureWith
              M.toConditionFunctionSemantics.toConditionFunctions)
          (totalCount s fun i =>
            (C i).countWith
              M.toConditionFunctionSemantics.toConditionFunctions) := by
  exact
    theorem1_rate_likelihood_product_decomposition_with_condition_functions
      M.toConditionFunctionSemantics.toConditionFunctions rate s C
      h_totalExposure

/--
Theorem 1 finite-product form directly from the explicit source-vocabulary
Condition 1/2 model, deriving nonzero total exposure from one positive
observed-window exposure.
Source status: Lean-checked paper-facing row.
-/
theorem theorem1_rate_likelihood_product_decomposition_with_condition_source_model_of_exists_pos_exposure
    {Incident : Type*}
    (M : Theorem2ConditionSourceModel) (rate : ℝ)
    (s : Finset Incident) (C : Incident → Theorem2ObservedWindowCase)
    (h_exists :
      ∃ i ∈ s,
        0 < (C i).exposureWith
          M.toConditionFunctionSemantics.toConditionFunctions) :
    (∏ i ∈ s,
        (C i).rateLikelihoodWith
          M.toConditionFunctionSemantics.toConditionFunctions rate) =
      Theorem2ObservedWindowCase.productResidualWith
          M.toConditionFunctionSemantics.toConditionFunctions s C *
        sourcePoissonPMF rate
          (totalExposure s fun i =>
            (C i).exposureWith
              M.toConditionFunctionSemantics.toConditionFunctions)
          (totalCount s fun i =>
            (C i).countWith
              M.toConditionFunctionSemantics.toConditionFunctions) := by
  exact
    theorem1_rate_likelihood_product_decomposition_with_condition_functions_of_exists_pos_exposure
      M.toConditionFunctionSemantics.toConditionFunctions rate s C h_exists

/--
Consolidated finite-data Theorem 1 route directly from the explicit
source-vocabulary Condition 1/2 model. Lean constructs the independent finite
Poisson count family and proves the collapsed source-PMF likelihood formula.
Source status: Lean-checked paper-facing row.
-/
theorem theorem1_exists_finite_poisson_count_family_for_condition_source_model_total_pmf
    {Incident : Type u}
    (rate : ℝ) (h_rate : 0 ≤ rate)
    (M : Theorem2ConditionSourceModel)
    (s : Finset Incident) (C : Incident → Theorem2ObservedWindowCase)
    (h_totalExposure :
      totalExposure s (fun i =>
        (C i).exposureWith
          M.toConditionFunctionSemantics.toConditionFunctions) ≠ 0) :
    ∃ Ω : Type u, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω,
      ∃ H : FinitePoissonCountFamily Ω P Incident rate
          (fun i =>
            (C i).exposureWith
              M.toConditionFunctionSemantics.toConditionFunctions),
        P.real (⋂ i ∈ s,
            {ω : Ω |
              H.count i ω =
                (C i).countWith
                  M.toConditionFunctionSemantics.toConditionFunctions}) =
            (countLikelihoodProductResidual s
                (fun i =>
                  (C i).exposureWith
                    M.toConditionFunctionSemantics.toConditionFunctions)
                (fun i =>
                  (C i).countWith
                    M.toConditionFunctionSemantics.toConditionFunctions) *
                ((totalCount s fun i =>
                    (C i).countWith
                      M.toConditionFunctionSemantics.toConditionFunctions).factorial : ℝ) /
                  (totalExposure s fun i =>
                    (C i).exposureWith
                      M.toConditionFunctionSemantics.toConditionFunctions) ^
                    totalCount s (fun i =>
                      (C i).countWith
                        M.toConditionFunctionSemantics.toConditionFunctions)) *
              sourcePoissonPMF rate
                (totalExposure s fun i =>
                  (C i).exposureWith
                    M.toConditionFunctionSemantics.toConditionFunctions)
                (totalCount s fun i =>
                  (C i).countWith
                    M.toConditionFunctionSemantics.toConditionFunctions) ∧
          (∏ i ∈ s,
              (C i).rateLikelihoodWith
                M.toConditionFunctionSemantics.toConditionFunctions rate) =
            Theorem2ObservedWindowCase.productResidualWith
                M.toConditionFunctionSemantics.toConditionFunctions s C *
              sourcePoissonPMF rate
                (totalExposure s fun i =>
                  (C i).exposureWith
                    M.toConditionFunctionSemantics.toConditionFunctions)
                (totalCount s fun i =>
                  (C i).countWith
                    M.toConditionFunctionSemantics.toConditionFunctions) := by
  exact
    theorem1_exists_finite_poisson_count_family_for_observed_windows_total_pmf
      rate h_rate M.toConditionFunctionSemantics.toConditionFunctions s C
      h_totalExposure

/--
Consolidated finite-data Theorem 1 route directly from the explicit
source-vocabulary Condition 1/2 model, deriving nonzero total exposure from
one positive observed-window exposure.
Source status: Lean-checked paper-facing row.
-/
theorem theorem1_exists_finite_poisson_count_family_for_condition_source_model_total_pmf_of_exists_pos_exposure
    {Incident : Type u}
    (rate : ℝ) (h_rate : 0 ≤ rate)
    (M : Theorem2ConditionSourceModel)
    (s : Finset Incident) (C : Incident → Theorem2ObservedWindowCase)
    (h_exists :
      ∃ i ∈ s,
        0 < (C i).exposureWith
          M.toConditionFunctionSemantics.toConditionFunctions) :
    ∃ Ω : Type u, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω,
      ∃ H : FinitePoissonCountFamily Ω P Incident rate
          (fun i =>
            (C i).exposureWith
              M.toConditionFunctionSemantics.toConditionFunctions),
        P.real (⋂ i ∈ s,
            {ω : Ω |
              H.count i ω =
                (C i).countWith
                  M.toConditionFunctionSemantics.toConditionFunctions}) =
            (countLikelihoodProductResidual s
                (fun i =>
                  (C i).exposureWith
                    M.toConditionFunctionSemantics.toConditionFunctions)
                (fun i =>
                  (C i).countWith
                    M.toConditionFunctionSemantics.toConditionFunctions) *
                ((totalCount s fun i =>
                    (C i).countWith
                      M.toConditionFunctionSemantics.toConditionFunctions).factorial : ℝ) /
                  (totalExposure s fun i =>
                    (C i).exposureWith
                      M.toConditionFunctionSemantics.toConditionFunctions) ^
                    totalCount s (fun i =>
                      (C i).countWith
                        M.toConditionFunctionSemantics.toConditionFunctions)) *
              sourcePoissonPMF rate
                (totalExposure s fun i =>
                  (C i).exposureWith
                    M.toConditionFunctionSemantics.toConditionFunctions)
                (totalCount s fun i =>
                  (C i).countWith
                    M.toConditionFunctionSemantics.toConditionFunctions) ∧
          (∏ i ∈ s,
              (C i).rateLikelihoodWith
                M.toConditionFunctionSemantics.toConditionFunctions rate) =
            Theorem2ObservedWindowCase.productResidualWith
                M.toConditionFunctionSemantics.toConditionFunctions s C *
              sourcePoissonPMF rate
                (totalExposure s fun i =>
                  (C i).exposureWith
                    M.toConditionFunctionSemantics.toConditionFunctions)
                (totalCount s fun i =>
                  (C i).countWith
                    M.toConditionFunctionSemantics.toConditionFunctions) := by
  exact
    theorem1_exists_finite_poisson_count_family_for_observed_windows_total_pmf_of_exists_pos_exposure
      rate h_rate M.toConditionFunctionSemantics.toConditionFunctions s C
      h_exists

/--
Theorem 1 finite-product form directly from the explicit density-kernel
Condition 1/2 source model, avoiding any continuous-time process object.
Source status: Lean-checked paper-facing row.
-/
theorem theorem1_rate_likelihood_product_decomposition_with_condition_density_source_model_of_exists_pos_exposure
    {Incident : Type*}
    (M : Theorem2ConditionDensitySourceModel) (rate : ℝ)
    (s : Finset Incident) (C : Incident → Theorem2ObservedWindowCase)
    (h_exists :
      ∃ i ∈ s,
        0 < (C i).exposureWith
          M.toConditionFunctionSemantics.toConditionFunctions) :
    (∏ i ∈ s,
        (C i).rateLikelihoodWith
          M.toConditionFunctionSemantics.toConditionFunctions rate) =
      Theorem2ObservedWindowCase.productResidualWith
          M.toConditionFunctionSemantics.toConditionFunctions s C *
        sourcePoissonPMF rate
          (totalExposure s fun i =>
            (C i).exposureWith
              M.toConditionFunctionSemantics.toConditionFunctions)
          (totalCount s fun i =>
            (C i).countWith
              M.toConditionFunctionSemantics.toConditionFunctions) := by
  exact
    theorem1_rate_likelihood_product_decomposition_with_condition_functions_of_exists_pos_exposure
      M.toConditionFunctionSemantics.toConditionFunctions rate s C h_exists

/--
Theorem 1 finite-product form directly from the explicit density-kernel
Condition 1/2 source model, with a raw nonzero total-exposure premise.
Source status: Lean-checked paper-facing row.
-/
theorem theorem1_rate_likelihood_product_decomposition_with_condition_density_source_model
    {Incident : Type*}
    (M : assumption_theorem2_condition_density_source_model) (rate : ℝ)
    (s : Finset Incident) (C : Incident → Theorem2ObservedWindowCase)
    (h_totalExposure :
      totalExposure s (fun i =>
        (C i).exposureWith
          M.toConditionFunctionSemantics.toConditionFunctions) ≠ 0) :
    (∏ i ∈ s,
        (C i).rateLikelihoodWith
          M.toConditionFunctionSemantics.toConditionFunctions rate) =
      Theorem2ObservedWindowCase.productResidualWith
          M.toConditionFunctionSemantics.toConditionFunctions s C *
        sourcePoissonPMF rate
          (totalExposure s fun i =>
            (C i).exposureWith
              M.toConditionFunctionSemantics.toConditionFunctions)
          (totalCount s fun i =>
            (C i).countWith
              M.toConditionFunctionSemantics.toConditionFunctions) := by
  exact
    theorem1_rate_likelihood_product_decomposition_with_condition_functions
      M.toConditionFunctionSemantics.toConditionFunctions rate s C
      h_totalExposure

/--
Theorem 1 finite-product form from fixed paper Condition 1/2 functions.
The rate-indexed density-source model is constructed from fixed `g(s)` and
`h_m(e)` data, so no separate rate-independence premises appear in this row.
Source status: Lean-checked paper-facing row.
-/
theorem theorem1_rate_likelihood_product_decomposition_with_fixed_condition_density_source_model
    {Incident : Type*}
    (M : Theorem2FixedConditionDensitySourceModel) (rate : ℝ)
    (s : Finset Incident) (C : Incident → Theorem2ObservedWindowCase)
    (h_totalExposure :
      totalExposure s (fun i =>
        (C i).exposureWith
          M.toConditionFunctionSemantics.toConditionFunctions) ≠ 0) :
    (∏ i ∈ s,
        (C i).rateLikelihoodWith
          M.toConditionFunctionSemantics.toConditionFunctions rate) =
      Theorem2ObservedWindowCase.productResidualWith
          M.toConditionFunctionSemantics.toConditionFunctions s C *
        sourcePoissonPMF rate
          (totalExposure s fun i =>
            (C i).exposureWith
              M.toConditionFunctionSemantics.toConditionFunctions)
          (totalCount s fun i =>
            (C i).countWith
              M.toConditionFunctionSemantics.toConditionFunctions) := by
  exact
    theorem1_rate_likelihood_product_decomposition_with_condition_density_source_model
      M.toConditionDensitySourceModel rate s C h_totalExposure

/--
Theorem 1 finite-product form from fixed paper Condition 1/2 functions,
deriving the nonzero-total-exposure premise from one positive observed-window
exposure.
Source status: Lean-checked paper-facing row.
-/
theorem theorem1_rate_likelihood_product_decomposition_with_fixed_condition_density_source_model_of_exists_pos_exposure
    {Incident : Type*}
    (M : Theorem2FixedConditionDensitySourceModel) (rate : ℝ)
    (s : Finset Incident) (C : Incident → Theorem2ObservedWindowCase)
    (h_exists :
      ∃ i ∈ s,
        0 < (C i).exposureWith
          M.toConditionFunctionSemantics.toConditionFunctions) :
    (∏ i ∈ s,
        (C i).rateLikelihoodWith
          M.toConditionFunctionSemantics.toConditionFunctions rate) =
      Theorem2ObservedWindowCase.productResidualWith
          M.toConditionFunctionSemantics.toConditionFunctions s C *
        sourcePoissonPMF rate
          (totalExposure s fun i =>
            (C i).exposureWith
              M.toConditionFunctionSemantics.toConditionFunctions)
          (totalCount s fun i =>
            (C i).countWith
              M.toConditionFunctionSemantics.toConditionFunctions) := by
  exact
    theorem1_rate_likelihood_product_decomposition_with_condition_density_source_model_of_exists_pos_exposure
      M.toConditionDensitySourceModel rate s C h_exists

/--
Consolidated finite-data Theorem 1 route directly from the explicit
density-kernel Condition 1/2 source model.  Lean constructs the independent
finite Poisson count family and proves the collapsed source-PMF likelihood
formula without assuming an all-times continuous-time process.
Source status: Lean-checked paper-facing row.
-/
theorem theorem1_exists_finite_poisson_count_family_for_condition_density_source_model_total_pmf_of_exists_pos_exposure
    {Incident : Type u}
    (rate : ℝ) (h_rate : 0 ≤ rate)
    (M : Theorem2ConditionDensitySourceModel)
    (s : Finset Incident) (C : Incident → Theorem2ObservedWindowCase)
    (h_exists :
      ∃ i ∈ s,
        0 < (C i).exposureWith
          M.toConditionFunctionSemantics.toConditionFunctions) :
    ∃ Ω : Type u, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω,
      ∃ H : FinitePoissonCountFamily Ω P Incident rate
          (fun i =>
            (C i).exposureWith
              M.toConditionFunctionSemantics.toConditionFunctions),
        P.real (⋂ i ∈ s,
            {ω : Ω |
              H.count i ω =
                (C i).countWith
                  M.toConditionFunctionSemantics.toConditionFunctions}) =
            (countLikelihoodProductResidual s
                (fun i =>
                  (C i).exposureWith
                    M.toConditionFunctionSemantics.toConditionFunctions)
                (fun i =>
                  (C i).countWith
                    M.toConditionFunctionSemantics.toConditionFunctions) *
                ((totalCount s fun i =>
                    (C i).countWith
                      M.toConditionFunctionSemantics.toConditionFunctions).factorial : ℝ) /
                  (totalExposure s fun i =>
                    (C i).exposureWith
                      M.toConditionFunctionSemantics.toConditionFunctions) ^
                    totalCount s (fun i =>
                      (C i).countWith
                        M.toConditionFunctionSemantics.toConditionFunctions)) *
              sourcePoissonPMF rate
                (totalExposure s fun i =>
                  (C i).exposureWith
                    M.toConditionFunctionSemantics.toConditionFunctions)
                (totalCount s fun i =>
                  (C i).countWith
                    M.toConditionFunctionSemantics.toConditionFunctions) ∧
          (∏ i ∈ s,
              (C i).rateLikelihoodWith
                M.toConditionFunctionSemantics.toConditionFunctions rate) =
            Theorem2ObservedWindowCase.productResidualWith
                M.toConditionFunctionSemantics.toConditionFunctions s C *
              sourcePoissonPMF rate
                (totalExposure s fun i =>
                  (C i).exposureWith
                    M.toConditionFunctionSemantics.toConditionFunctions)
                (totalCount s fun i =>
                  (C i).countWith
                    M.toConditionFunctionSemantics.toConditionFunctions) := by
  exact
    theorem1_exists_finite_poisson_count_family_for_observed_windows_total_pmf_of_exists_pos_exposure
      rate h_rate M.toConditionFunctionSemantics.toConditionFunctions s C h_exists

/--
Consolidated finite-data Theorem 1 route directly from the explicit
density-kernel Condition 1/2 source model, with a raw nonzero total-exposure
premise.
Source status: Lean-checked paper-facing row.
-/
theorem theorem1_exists_finite_poisson_count_family_for_condition_density_source_model_total_pmf
    {Incident : Type u}
    (rate : ℝ) (h_rate : 0 ≤ rate)
    (M : Theorem2ConditionDensitySourceModel)
    (s : Finset Incident) (C : Incident → Theorem2ObservedWindowCase)
    (h_totalExposure :
      totalExposure s (fun i =>
        (C i).exposureWith
          M.toConditionFunctionSemantics.toConditionFunctions) ≠ 0) :
    ∃ Ω : Type u, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω,
      ∃ H : FinitePoissonCountFamily Ω P Incident rate
          (fun i =>
            (C i).exposureWith
              M.toConditionFunctionSemantics.toConditionFunctions),
        P.real (⋂ i ∈ s,
            {ω : Ω |
              H.count i ω =
                (C i).countWith
                  M.toConditionFunctionSemantics.toConditionFunctions}) =
            (countLikelihoodProductResidual s
                (fun i =>
                  (C i).exposureWith
                    M.toConditionFunctionSemantics.toConditionFunctions)
                (fun i =>
                  (C i).countWith
                    M.toConditionFunctionSemantics.toConditionFunctions) *
                ((totalCount s fun i =>
                    (C i).countWith
                      M.toConditionFunctionSemantics.toConditionFunctions).factorial : ℝ) /
                  (totalExposure s fun i =>
                    (C i).exposureWith
                      M.toConditionFunctionSemantics.toConditionFunctions) ^
                    totalCount s (fun i =>
                      (C i).countWith
                        M.toConditionFunctionSemantics.toConditionFunctions)) *
              sourcePoissonPMF rate
                (totalExposure s fun i =>
                  (C i).exposureWith
                    M.toConditionFunctionSemantics.toConditionFunctions)
                (totalCount s fun i =>
                  (C i).countWith
                    M.toConditionFunctionSemantics.toConditionFunctions) ∧
          (∏ i ∈ s,
              (C i).rateLikelihoodWith
                M.toConditionFunctionSemantics.toConditionFunctions rate) =
            Theorem2ObservedWindowCase.productResidualWith
                M.toConditionFunctionSemantics.toConditionFunctions s C *
              sourcePoissonPMF rate
                (totalExposure s fun i =>
                  (C i).exposureWith
                    M.toConditionFunctionSemantics.toConditionFunctions)
                (totalCount s fun i =>
                  (C i).countWith
                    M.toConditionFunctionSemantics.toConditionFunctions) := by
  exact
    theorem1_exists_finite_poisson_count_family_for_observed_windows_total_pmf
      rate h_rate M.toConditionFunctionSemantics.toConditionFunctions s C
      h_totalExposure

/--
Theorem 1 finite-product form from primitive source semantics.  This is the
same product decomposition as the Poisson-increment-law row, but with the
Condition 1/2 terms supplied as rate-indexed source semantics and converted to
rate-independent condition functions inside Lean.
Source status: Lean-checked paper-facing row.
-/
theorem theorem1_likelihood_product_decomposition_from_source_semantics
    {Ω Incident : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (S : theorem2_poisson_process_and_condition_semantics Ω P)
    (s : Finset Incident) (C : Incident → Theorem2ObservedWindowCase)
    (h_totalExposure :
      totalExposure s (fun i => (C i).exposureFromSourceSemantics S) ≠ 0) :
    (∏ i ∈ s, (C i).likelihoodFromSourceSemantics S) =
      Theorem2ObservedWindowCase.productResidualFromSourceSemantics S s C *
        sourcePoissonPMF S.rate
          (totalExposure s fun i => (C i).exposureFromSourceSemantics S)
          (totalCount s fun i => (C i).countFromSourceSemantics S) := by
  exact Theorem2ObservedWindowCase.product_factorizationFromSourceSemantics
    S s C h_totalExposure

/--
Theorem 1 finite-product form with primitive source semantics constructed
inside Lean from mathlib Poisson increment laws and rate-independent Condition
1/2 functions.
Source status: Lean-checked paper-facing row.
-/
theorem theorem1_likelihood_product_decomposition_from_constructed_source_semantics
    {Ω Incident : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : HomogeneousPoissonCountingProcessByLaw Ω P)
    (K : Theorem2ConditionFunctions)
    (s : Finset Incident) (C : Incident → Theorem2ObservedWindowCase)
    (h_totalExposure :
      totalExposure s (fun i => (C i).exposureWith K) ≠ 0) :
    (∏ i ∈ s,
        (C i).likelihoodFromSourceSemantics
          (theorem2_poisson_process_and_condition_semantics.fromPoissonIncrementLawsAndConditionFunctions
            H K)) =
      Theorem2ObservedWindowCase.productResidualWith K s C *
        sourcePoissonPMF H.rate
          (totalExposure s fun i => (C i).exposureWith K)
          (totalCount s fun i => (C i).countWith K) := by
  exact
    Theorem2ObservedWindowCase.product_factorizationFromConstructedSourceSemantics
      H K s C h_totalExposure

/--
Theorem 1 finite-product form with primitive source semantics constructed
inside Lean, deriving nonzero total exposure from one positive observed
window.
Source status: Lean-checked paper-facing row.
-/
theorem theorem1_likelihood_product_decomposition_from_constructed_source_semantics_of_exists_pos_exposure
    {Ω Incident : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : HomogeneousPoissonCountingProcessByLaw Ω P)
    (K : Theorem2ConditionFunctions)
    (s : Finset Incident) (C : Incident → Theorem2ObservedWindowCase)
    (h_exists : ∃ i ∈ s, 0 < (C i).exposureWith K) :
    (∏ i ∈ s,
        (C i).likelihoodFromSourceSemantics
          (theorem2_poisson_process_and_condition_semantics.fromPoissonIncrementLawsAndConditionFunctions
            H K)) =
      Theorem2ObservedWindowCase.productResidualWith K s C *
        sourcePoissonPMF H.rate
          (totalExposure s fun i => (C i).exposureWith K)
          (totalCount s fun i => (C i).countWith K) := by
  exact
    Theorem2ObservedWindowCase.product_factorizationFromConstructedSourceSemantics_of_exists_pos_exposure
      H K s C h_exists

/--
Theorem 1 finite-product form with primitive source semantics constructed
inside Lean from mathlib Poisson increment laws and the paper's rate-indexed
Condition 1/2 source semantics.
Source status: Lean-checked paper-facing row.
-/
theorem theorem1_likelihood_product_decomposition_from_poisson_increment_laws_and_condition_semantics
    {Ω Incident : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : HomogeneousPoissonCountingProcessByLaw Ω P)
    (G : Theorem2ConditionFunctionSemantics)
    (s : Finset Incident) (C : Incident → Theorem2ObservedWindowCase)
    (h_totalExposure :
      totalExposure s (fun i => (C i).exposureWith G.toConditionFunctions) ≠
        0) :
    (∏ i ∈ s,
        (C i).likelihoodFromSourceSemantics
          (theorem2_poisson_process_and_condition_semantics.fromPoissonIncrementLawsAndConditionSemantics
            H G)) =
      Theorem2ObservedWindowCase.productResidualWith G.toConditionFunctions s C *
        sourcePoissonPMF H.rate
          (totalExposure s fun i => (C i).exposureWith G.toConditionFunctions)
          (totalCount s fun i => (C i).countWith G.toConditionFunctions) := by
  exact
    Theorem2ObservedWindowCase.product_factorizationFromPoissonIncrementLawsAndConditionSemantics
      H G s C h_totalExposure

theorem theorem1_likelihood_product_decomposition_from_poisson_increment_laws_and_condition_semantics_of_exists_pos_exposure
    {Ω Incident : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : HomogeneousPoissonCountingProcessByLaw Ω P)
    (G : Theorem2ConditionFunctionSemantics)
    (s : Finset Incident) (C : Incident → Theorem2ObservedWindowCase)
    (h_exists :
      ∃ i ∈ s, 0 < (C i).exposureWith G.toConditionFunctions) :
    (∏ i ∈ s,
        (C i).likelihoodFromSourceSemantics
          (theorem2_poisson_process_and_condition_semantics.fromPoissonIncrementLawsAndConditionSemantics
            H G)) =
      Theorem2ObservedWindowCase.productResidualWith G.toConditionFunctions s C *
        sourcePoissonPMF H.rate
          (totalExposure s fun i => (C i).exposureWith G.toConditionFunctions)
          (totalCount s fun i => (C i).countWith G.toConditionFunctions) := by
  exact
    Theorem2ObservedWindowCase.product_factorizationFromPoissonIncrementLawsAndConditionSemantics_of_exists_pos_exposure
      H G s C h_exists

/--
Finite-product Appendix B.2 source-data factorization constructed directly
from mathlib Poisson increment laws and the paper's rate-indexed Condition
1/2 source semantics.
Source status: Lean-checked paper-facing row.
-/
theorem theorem1_source_data_product_decomposition_from_poisson_increment_laws_and_condition_semantics
    {Ω Incident : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : HomogeneousPoissonCountingProcessByLaw Ω P)
    (G : Theorem2ConditionFunctionSemantics)
    (s : Finset Incident) (C : Incident → Theorem2ObservedWindowCase)
    (h_totalExposure :
      totalExposure s (fun i => (C i).exposureWith G.toConditionFunctions) ≠
        0) :
    (∏ i ∈ s,
        (C i).sourceDataLikelihoodAtRate
          (theorem2_poisson_process_and_condition_semantics.fromPoissonIncrementLawsAndConditionSemantics
            H G)) =
      Theorem2ObservedWindowCase.productResidualWith G.toConditionFunctions s C *
        sourcePoissonPMF H.rate
          (totalExposure s fun i => (C i).exposureWith G.toConditionFunctions)
          (totalCount s fun i => (C i).countWith G.toConditionFunctions) := by
  exact
    Theorem2ObservedWindowCase.product_sourceDataLikelihoodAtRate_factorizationFromPoissonIncrementLawsAndConditionSemantics
      H G s C h_totalExposure

theorem theorem1_source_data_product_decomposition_from_poisson_increment_laws_and_condition_semantics_of_exists_pos_exposure
    {Ω Incident : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : HomogeneousPoissonCountingProcessByLaw Ω P)
    (G : Theorem2ConditionFunctionSemantics)
    (s : Finset Incident) (C : Incident → Theorem2ObservedWindowCase)
    (h_exists :
      ∃ i ∈ s, 0 < (C i).exposureWith G.toConditionFunctions) :
    (∏ i ∈ s,
        (C i).sourceDataLikelihoodAtRate
          (theorem2_poisson_process_and_condition_semantics.fromPoissonIncrementLawsAndConditionSemantics
            H G)) =
      Theorem2ObservedWindowCase.productResidualWith G.toConditionFunctions s C *
        sourcePoissonPMF H.rate
          (totalExposure s fun i => (C i).exposureWith G.toConditionFunctions)
          (totalCount s fun i => (C i).countWith G.toConditionFunctions) := by
  exact
    Theorem2ObservedWindowCase.product_sourceDataLikelihoodAtRate_factorizationFromPoissonIncrementLawsAndConditionSemantics_of_exists_pos_exposure
      H G s C h_exists

/--
Finite-data realization of the primitive Theorem 1 route: from mathlib Poisson
increment laws and the paper's rate-indexed Condition 1/2 source semantics,
Lean constructs an independent finite Poisson count family whose observed
total-count event carries the same collapsed likelihood factor for both the
source-semantics and Appendix B.2 source-data products.
Source status: Lean-checked paper-facing row.
-/
theorem theorem1_exists_finite_poisson_count_family_for_poisson_increment_laws_and_condition_semantics_total_count_event_of_exists_pos_exposure
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Incident : Type u} [DecidableEq Incident]
    (H : HomogeneousPoissonCountingProcessByLaw Ω P)
    (G : Theorem2ConditionFunctionSemantics)
    (s : Finset Incident) (C : Incident → Theorem2ObservedWindowCase)
    (h_exists :
      ∃ i ∈ s, 0 < (C i).exposureWith G.toConditionFunctions) :
    ∃ Ωc : Type u, ∃ _ : MeasurableSpace Ωc, ∃ Pc : Measure Ωc,
      ∃ Hc : FinitePoissonCountFamily Ωc Pc Incident H.rate
          (fun i => (C i).exposureWith G.toConditionFunctions),
        (∏ i ∈ s,
            (C i).likelihoodFromSourceSemantics
              (theorem2_poisson_process_and_condition_semantics.fromPoissonIncrementLawsAndConditionSemantics
                H G)) =
            Theorem2ObservedWindowCase.productResidualWith G.toConditionFunctions s C *
              Pc.real {ω : Ωc |
                (∑ i ∈ s, Hc.count i ω) =
                  totalCount s (fun i => (C i).countWith G.toConditionFunctions)} ∧
        (∏ i ∈ s,
            (C i).sourceDataLikelihoodAtRate
              (theorem2_poisson_process_and_condition_semantics.fromPoissonIncrementLawsAndConditionSemantics
                H G)) =
            Theorem2ObservedWindowCase.productResidualWith G.toConditionFunctions s C *
              Pc.real {ω : Ωc |
                (∑ i ∈ s, Hc.count i ω) =
                  totalCount s (fun i => (C i).countWith G.toConditionFunctions)} := by
  rcases exists_finitePoissonCountFamily
      H.rate (le_of_lt H.rate_pos)
      (fun i => (C i).exposureWith G.toConditionFunctions)
      (fun i => (C i).exposureWith_nonneg G.toConditionFunctions) with
    ⟨Ωc, mΩc, Pc, Hc, _⟩
  exact
    ⟨Ωc, mΩc, Pc, Hc,
      Theorem2ObservedWindowCase.product_likelihoodFromPoissonIncrementLawsAndConditionSemantics_eq_productResidual_mul_totalCountEvent_prob_of_exists_pos_exposure
        H G s C Hc h_exists,
      Theorem2ObservedWindowCase.product_sourceDataLikelihoodAtRate_fromPoissonIncrementLawsAndConditionSemantics_eq_productResidual_mul_totalCountEvent_prob_of_exists_pos_exposure
        H G s C Hc h_exists⟩

/--
Theorem 1 finite-product form constructed from mathlib Poisson increment laws
and the explicit Condition 1/2 source model.
Source status: Lean-checked paper-facing row.
-/
theorem theorem1_likelihood_product_decomposition_from_poisson_increment_laws_and_condition_source_model_of_exists_pos_exposure
    {Ω Incident : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : HomogeneousPoissonCountingProcessByLaw Ω P)
    (M : Theorem2ConditionSourceModel)
    (s : Finset Incident) (C : Incident → Theorem2ObservedWindowCase)
    (h_exists :
      ∃ i ∈ s,
        0 < (C i).exposureWith
          M.toConditionFunctionSemantics.toConditionFunctions) :
    (∏ i ∈ s,
        (C i).likelihoodFromSourceSemantics
          (theorem2_poisson_process_and_condition_semantics.fromPoissonIncrementLawsAndConditionSourceModel
            H M)) =
      Theorem2ObservedWindowCase.productResidualWith
          M.toConditionFunctionSemantics.toConditionFunctions s C *
        sourcePoissonPMF H.rate
          (totalExposure s fun i =>
            (C i).exposureWith
              M.toConditionFunctionSemantics.toConditionFunctions)
          (totalCount s fun i =>
            (C i).countWith
              M.toConditionFunctionSemantics.toConditionFunctions) := by
  exact
    Theorem2ObservedWindowCase.product_factorizationFromPoissonIncrementLawsAndConditionSemantics_of_exists_pos_exposure
      H M.toConditionFunctionSemantics s C h_exists

/--
Finite-product Appendix B.2 source-data factorization constructed from
mathlib Poisson increment laws and the explicit Condition 1/2 source model.
Source status: Lean-checked paper-facing row.
-/
theorem theorem1_source_data_product_decomposition_from_poisson_increment_laws_and_condition_source_model_of_exists_pos_exposure
    {Ω Incident : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : HomogeneousPoissonCountingProcessByLaw Ω P)
    (M : Theorem2ConditionSourceModel)
    (s : Finset Incident) (C : Incident → Theorem2ObservedWindowCase)
    (h_exists :
      ∃ i ∈ s,
        0 < (C i).exposureWith
          M.toConditionFunctionSemantics.toConditionFunctions) :
    (∏ i ∈ s,
        (C i).sourceDataLikelihoodAtRate
          (theorem2_poisson_process_and_condition_semantics.fromPoissonIncrementLawsAndConditionSourceModel
            H M)) =
      Theorem2ObservedWindowCase.productResidualWith
          M.toConditionFunctionSemantics.toConditionFunctions s C *
        sourcePoissonPMF H.rate
          (totalExposure s fun i =>
            (C i).exposureWith
              M.toConditionFunctionSemantics.toConditionFunctions)
          (totalCount s fun i =>
            (C i).countWith
              M.toConditionFunctionSemantics.toConditionFunctions) := by
  exact
    Theorem2ObservedWindowCase.product_sourceDataLikelihoodAtRate_factorizationFromPoissonIncrementLawsAndConditionSemantics_of_exists_pos_exposure
      H M.toConditionFunctionSemantics s C h_exists

/--
Finite-data realization of the source-model route: Lean constructs an
independent finite Poisson count family whose total-count event carries the
same collapsed likelihood factor for both source-semantics and Appendix B.2
source-data products.
Source status: Lean-checked paper-facing row.
-/
theorem theorem1_exists_finite_poisson_count_family_for_poisson_increment_laws_and_condition_source_model_total_count_event_of_exists_pos_exposure
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Incident : Type u} [DecidableEq Incident]
    (H : HomogeneousPoissonCountingProcessByLaw Ω P)
    (M : Theorem2ConditionSourceModel)
    (s : Finset Incident) (C : Incident → Theorem2ObservedWindowCase)
    (h_exists :
      ∃ i ∈ s,
        0 < (C i).exposureWith
          M.toConditionFunctionSemantics.toConditionFunctions) :
    ∃ Ωc : Type u, ∃ _ : MeasurableSpace Ωc, ∃ Pc : Measure Ωc,
      ∃ Hc : FinitePoissonCountFamily Ωc Pc Incident H.rate
          (fun i => (C i).exposureWith
            M.toConditionFunctionSemantics.toConditionFunctions),
        (∏ i ∈ s,
            (C i).likelihoodFromSourceSemantics
              (theorem2_poisson_process_and_condition_semantics.fromPoissonIncrementLawsAndConditionSourceModel
                H M)) =
            Theorem2ObservedWindowCase.productResidualWith
                M.toConditionFunctionSemantics.toConditionFunctions s C *
              Pc.real {ω : Ωc |
                (∑ i ∈ s, Hc.count i ω) =
                  totalCount s (fun i =>
                    (C i).countWith
                      M.toConditionFunctionSemantics.toConditionFunctions)} ∧
        (∏ i ∈ s,
            (C i).sourceDataLikelihoodAtRate
              (theorem2_poisson_process_and_condition_semantics.fromPoissonIncrementLawsAndConditionSourceModel
                H M)) =
            Theorem2ObservedWindowCase.productResidualWith
                M.toConditionFunctionSemantics.toConditionFunctions s C *
              Pc.real {ω : Ωc |
                (∑ i ∈ s, Hc.count i ω) =
                  totalCount s (fun i =>
                    (C i).countWith
                      M.toConditionFunctionSemantics.toConditionFunctions)} := by
  exact
    theorem1_exists_finite_poisson_count_family_for_poisson_increment_laws_and_condition_semantics_total_count_event_of_exists_pos_exposure
      H M.toConditionFunctionSemantics s C h_exists

/--
Theorem 1 finite-product form constructed from mathlib Poisson increment laws
and the density-kernel Condition 1/2 source model.
Source status: Lean-checked paper-facing row.
-/
theorem theorem1_likelihood_product_decomposition_from_poisson_increment_laws_and_condition_density_source_model_of_exists_pos_exposure
    {Ω Incident : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : HomogeneousPoissonCountingProcessByLaw Ω P)
    (M : Theorem2ConditionDensitySourceModel)
    (s : Finset Incident) (C : Incident → Theorem2ObservedWindowCase)
    (h_exists :
      ∃ i ∈ s,
        0 < (C i).exposureWith
          M.toConditionFunctionSemantics.toConditionFunctions) :
    (∏ i ∈ s,
        (C i).likelihoodFromSourceSemantics
          (theorem2_poisson_process_and_condition_semantics.fromPoissonIncrementLawsAndConditionDensitySourceModel
            H M)) =
      Theorem2ObservedWindowCase.productResidualWith
          M.toConditionFunctionSemantics.toConditionFunctions s C *
        sourcePoissonPMF H.rate
          (totalExposure s fun i =>
            (C i).exposureWith
              M.toConditionFunctionSemantics.toConditionFunctions)
          (totalCount s fun i =>
            (C i).countWith
              M.toConditionFunctionSemantics.toConditionFunctions) := by
  exact
    Theorem2ObservedWindowCase.product_factorizationFromPoissonIncrementLawsAndConditionSemantics_of_exists_pos_exposure
      H M.toConditionFunctionSemantics s C h_exists

/--
Finite-product Appendix B.2 source-data factorization constructed from
mathlib Poisson increment laws and the density-kernel Condition 1/2 source
model.
Source status: Lean-checked paper-facing row.
-/
theorem theorem1_source_data_product_decomposition_from_poisson_increment_laws_and_condition_density_source_model_of_exists_pos_exposure
    {Ω Incident : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : HomogeneousPoissonCountingProcessByLaw Ω P)
    (M : Theorem2ConditionDensitySourceModel)
    (s : Finset Incident) (C : Incident → Theorem2ObservedWindowCase)
    (h_exists :
      ∃ i ∈ s,
        0 < (C i).exposureWith
          M.toConditionFunctionSemantics.toConditionFunctions) :
    (∏ i ∈ s,
        (C i).sourceDataLikelihoodAtRate
          (theorem2_poisson_process_and_condition_semantics.fromPoissonIncrementLawsAndConditionDensitySourceModel
            H M)) =
      Theorem2ObservedWindowCase.productResidualWith
          M.toConditionFunctionSemantics.toConditionFunctions s C *
        sourcePoissonPMF H.rate
          (totalExposure s fun i =>
            (C i).exposureWith
              M.toConditionFunctionSemantics.toConditionFunctions)
          (totalCount s fun i =>
            (C i).countWith
              M.toConditionFunctionSemantics.toConditionFunctions) := by
  exact
    Theorem2ObservedWindowCase.product_sourceDataLikelihoodAtRate_factorizationFromPoissonIncrementLawsAndConditionSemantics_of_exists_pos_exposure
      H M.toConditionFunctionSemantics s C h_exists

/--
Finite-data realization of the density-source route: Lean constructs an
independent finite Poisson count family whose total-count event carries the
same collapsed likelihood factor for both source-semantics and Appendix B.2
source-data products.
Source status: Lean-checked paper-facing row.
-/
theorem theorem1_exists_finite_poisson_count_family_for_poisson_increment_laws_and_condition_density_source_model_total_count_event_of_exists_pos_exposure
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Incident : Type u} [DecidableEq Incident]
    (H : HomogeneousPoissonCountingProcessByLaw Ω P)
    (M : Theorem2ConditionDensitySourceModel)
    (s : Finset Incident) (C : Incident → Theorem2ObservedWindowCase)
    (h_exists :
      ∃ i ∈ s,
        0 < (C i).exposureWith
          M.toConditionFunctionSemantics.toConditionFunctions) :
    ∃ Ωc : Type u, ∃ _ : MeasurableSpace Ωc, ∃ Pc : Measure Ωc,
      ∃ Hc : FinitePoissonCountFamily Ωc Pc Incident H.rate
          (fun i => (C i).exposureWith
            M.toConditionFunctionSemantics.toConditionFunctions),
        (∏ i ∈ s,
            (C i).likelihoodFromSourceSemantics
              (theorem2_poisson_process_and_condition_semantics.fromPoissonIncrementLawsAndConditionDensitySourceModel
                H M)) =
            Theorem2ObservedWindowCase.productResidualWith
                M.toConditionFunctionSemantics.toConditionFunctions s C *
              Pc.real {ω : Ωc |
                (∑ i ∈ s, Hc.count i ω) =
                  totalCount s (fun i =>
                    (C i).countWith
                      M.toConditionFunctionSemantics.toConditionFunctions)} ∧
        (∏ i ∈ s,
            (C i).sourceDataLikelihoodAtRate
              (theorem2_poisson_process_and_condition_semantics.fromPoissonIncrementLawsAndConditionDensitySourceModel
                H M)) =
            Theorem2ObservedWindowCase.productResidualWith
                M.toConditionFunctionSemantics.toConditionFunctions s C *
              Pc.real {ω : Ωc |
                (∑ i ∈ s, Hc.count i ω) =
                  totalCount s (fun i =>
                    (C i).countWith
                      M.toConditionFunctionSemantics.toConditionFunctions)} := by
  exact
    theorem1_exists_finite_poisson_count_family_for_poisson_increment_laws_and_condition_semantics_total_count_event_of_exists_pos_exposure
      H M.toConditionFunctionSemantics s C h_exists

/--
Theorem 1 finite-product form from the public-partial primitive source model.
All Condition 1/2 source terms are derived from the fixed paper kernels in
`M`; the only remaining process-side input is `M.countProcess`.
Source status: Lean-checked paper-facing row.
-/
theorem theorem1_likelihood_product_decomposition_from_primitive_source_model_of_exists_pos_exposure
    {Ω Incident : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (M : Theorem2PrimitiveSourceModel Ω P)
    (s : Finset Incident) (C : Incident → Theorem2ObservedWindowCase)
    (h_exists :
      ∃ i ∈ s,
        0 < (C i).exposureWith M.conditionFunctions) :
    (∏ i ∈ s,
        (C i).likelihoodFromSourceSemantics M.toSourceSemantics) =
      Theorem2ObservedWindowCase.productResidualWith
          M.conditionFunctions s C *
        sourcePoissonPMF M.rate
          (totalExposure s fun i =>
            (C i).exposureWith M.conditionFunctions)
          (totalCount s fun i =>
            (C i).countWith M.conditionFunctions) := by
  exact
    theorem1_likelihood_product_decomposition_from_poisson_increment_laws_and_condition_density_source_model_of_exists_pos_exposure
      M.countProcess M.toConditionDensitySourceModel s C h_exists

/--
Finite-product Appendix B.2 source-data factorization from the public-partial
primitive source model.  This is the product analogue of the single-window
primitive-wrapper row.
Source status: Lean-checked paper-facing row.
-/
theorem theorem1_source_data_product_decomposition_from_primitive_source_model_of_exists_pos_exposure
    {Ω Incident : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (M : Theorem2PrimitiveSourceModel Ω P)
    (s : Finset Incident) (C : Incident → Theorem2ObservedWindowCase)
    (h_exists :
      ∃ i ∈ s,
        0 < (C i).exposureWith M.conditionFunctions) :
    (∏ i ∈ s,
        (C i).sourceDataLikelihoodAtRate M.toSourceSemantics) =
      Theorem2ObservedWindowCase.productResidualWith
          M.conditionFunctions s C *
        sourcePoissonPMF M.rate
          (totalExposure s fun i =>
            (C i).exposureWith M.conditionFunctions)
          (totalCount s fun i =>
            (C i).countWith M.conditionFunctions) := by
  exact
    theorem1_source_data_product_decomposition_from_poisson_increment_laws_and_condition_density_source_model_of_exists_pos_exposure
      M.countProcess M.toConditionDensitySourceModel s C h_exists

/--
Finite-data realization from the public-partial primitive source model: Lean
constructs the independent finite Poisson count family and the collapsed
total-count event once the wrapper supplies the homogeneous count law and fixed
Condition 1/2 kernels.
Source status: Lean-checked paper-facing row.
-/
theorem theorem1_exists_finite_poisson_count_family_for_primitive_source_model_total_count_event_of_exists_pos_exposure
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Incident : Type u} [DecidableEq Incident]
    (M : Theorem2PrimitiveSourceModel Ω P)
    (s : Finset Incident) (C : Incident → Theorem2ObservedWindowCase)
    (h_exists :
      ∃ i ∈ s,
        0 < (C i).exposureWith M.conditionFunctions) :
    ∃ Ωc : Type u, ∃ _ : MeasurableSpace Ωc, ∃ Pc : Measure Ωc,
      ∃ Hc : FinitePoissonCountFamily Ωc Pc Incident M.rate
          (fun i => (C i).exposureWith M.conditionFunctions),
        (∏ i ∈ s,
            (C i).likelihoodFromSourceSemantics M.toSourceSemantics) =
            Theorem2ObservedWindowCase.productResidualWith
                M.conditionFunctions s C *
              Pc.real {ω : Ωc |
                (∑ i ∈ s, Hc.count i ω) =
                  totalCount s (fun i =>
                    (C i).countWith M.conditionFunctions)} ∧
        (∏ i ∈ s,
            (C i).sourceDataLikelihoodAtRate M.toSourceSemantics) =
            Theorem2ObservedWindowCase.productResidualWith
                M.conditionFunctions s C *
              Pc.real {ω : Ωc |
                (∑ i ∈ s, Hc.count i ω) =
                  totalCount s (fun i =>
                    (C i).countWith M.conditionFunctions)} := by
  exact
    theorem1_exists_finite_poisson_count_family_for_poisson_increment_laws_and_condition_density_source_model_total_count_event_of_exists_pos_exposure
      M.countProcess M.toConditionDensitySourceModel s C h_exists

/--
Finite-product Theorem 1 source-semantics route agrees term-by-term with the
Appendix B.2 source-data route assembled at the source process rate.
Source status: Lean-checked paper-facing row.
-/
theorem theorem1_likelihood_product_from_source_semantics_eq_source_data_at_rate
    {Ω Incident : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (S : theorem2_poisson_process_and_condition_semantics Ω P)
    (s : Finset Incident) (C : Incident → Theorem2ObservedWindowCase) :
    (∏ i ∈ s, (C i).likelihoodFromSourceSemantics S) =
      ∏ i ∈ s, (C i).sourceDataLikelihoodAtRate S := by
  exact
    Theorem2ObservedWindowCase.product_likelihoodFromSourceSemantics_eq_productSourceDataLikelihoodAtRate
      S s C

/--
Finite-product source semantics reduce termwise to the process-free
condition-function rate likelihoods at the source process rate.
Source status: Lean-checked paper-facing row.
-/
theorem theorem1_likelihood_product_from_source_semantics_eq_condition_function_rate_likelihood_product
    {Ω Incident : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (S : theorem2_poisson_process_and_condition_semantics Ω P)
    (s : Finset Incident) (C : Incident → Theorem2ObservedWindowCase) :
    (∏ i ∈ s, (C i).likelihoodFromSourceSemantics S) =
      ∏ i ∈ s, (C i).rateLikelihoodWith S.conditionFunctions S.rate := by
  exact
    Theorem2ObservedWindowCase.product_likelihoodFromSourceSemantics_eq_productRateLikelihoodWith
      S s C

/--
Finite-product version of the source-data/condition-function bridge: after
rate-independence is applied, the Appendix B.2 source-data product is the
process-free condition-function likelihood product at the source process rate.
Source status: Lean-checked paper-facing row.
-/
theorem theorem1_source_data_product_at_rate_eq_condition_function_rate_likelihood_product
    {Ω Incident : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (S : theorem2_poisson_process_and_condition_semantics Ω P)
    (s : Finset Incident) (C : Incident → Theorem2ObservedWindowCase) :
    (∏ i ∈ s, (C i).sourceDataLikelihoodAtRate S) =
      ∏ i ∈ s, (C i).rateLikelihoodWith S.conditionFunctions S.rate := by
  exact
    Theorem2ObservedWindowCase.product_sourceDataLikelihoodAtRate_eq_productRateLikelihoodWith
      S s C

/--
The finite-product source-data residual assembled at the source rate is the
same residual used by the source-semantics Theorem 1 product row.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_source_data_product_residual_at_rate_eq_theorem1_product_residual
    {Ω Incident : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (S : theorem2_poisson_process_and_condition_semantics Ω P)
    (s : Finset Incident) (C : Incident → Theorem2ObservedWindowCase) :
    Theorem2ObservedWindowCase.productSourceDataResidualAtRate S s C =
      Theorem2ObservedWindowCase.productResidualFromSourceSemantics S s C := by
  exact
    Theorem2ObservedWindowCase.productSourceDataResidualAtRate_eq_productResidualFromSourceSemantics
      S s C

/--
The finite-product source-data exposure sum equals the exposure sum derived
directly from primitive source semantics.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_source_data_total_exposure_at_rate_eq_theorem1_total_exposure
    {Ω Incident : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (S : theorem2_poisson_process_and_condition_semantics Ω P)
    (s : Finset Incident) (C : Incident → Theorem2ObservedWindowCase) :
    totalExposure s (fun i => (C i).sourceDataExposureAtRate S) =
      totalExposure s (fun i => (C i).exposureFromSourceSemantics S) := by
  classical
  unfold totalExposure
  refine Finset.sum_congr rfl ?_
  intro i _hi
  exact (C i).sourceDataExposureAtRate_eq_exposureFromSourceSemantics S

/--
The finite-product source-data count sum equals the count sum derived directly
from primitive source semantics.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_source_data_total_count_at_rate_eq_theorem1_total_count
    {Ω Incident : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (S : theorem2_poisson_process_and_condition_semantics Ω P)
    (s : Finset Incident) (C : Incident → Theorem2ObservedWindowCase) :
    totalCount s (fun i => (C i).sourceDataCountAtRate S) =
      totalCount s (fun i => (C i).countFromSourceSemantics S) := by
  classical
  unfold totalCount
  refine Finset.sum_congr rfl ?_
  intro i _hi
  exact (C i).sourceDataCountAtRate_eq_countFromSourceSemantics S

/--
Finite-product Appendix B.2 source-data factorization at the source process
rate, with the source-data residual kept explicit.
Source status: Lean-checked paper-facing row.
-/
theorem theorem1_source_data_product_decomposition_at_rate
    {Ω Incident : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (S : theorem2_poisson_process_and_condition_semantics Ω P)
    (s : Finset Incident) (C : Incident → Theorem2ObservedWindowCase)
    (h_totalExposure :
      totalExposure s (fun i => (C i).sourceDataExposureAtRate S) ≠ 0) :
    (∏ i ∈ s, (C i).sourceDataLikelihoodAtRate S) =
      Theorem2ObservedWindowCase.productSourceDataResidualAtRate S s C *
        sourcePoissonPMF S.rate
          (totalExposure s fun i => (C i).sourceDataExposureAtRate S)
          (totalCount s fun i => (C i).sourceDataCountAtRate S) := by
  exact
    Theorem2ObservedWindowCase.productSourceDataAtRate_factorization
      S s C h_totalExposure

/--
Finite-product Appendix B.2 source-data factorization at the source process
rate, rewritten with the same residual package used by the source-semantics
Theorem 1 row.
Source status: Lean-checked paper-facing row.
-/
theorem theorem1_source_data_product_decomposition_at_rate_same_residual
    {Ω Incident : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (S : theorem2_poisson_process_and_condition_semantics Ω P)
    (s : Finset Incident) (C : Incident → Theorem2ObservedWindowCase)
    (h_totalExposure :
      totalExposure s (fun i => (C i).sourceDataExposureAtRate S) ≠ 0) :
    (∏ i ∈ s, (C i).sourceDataLikelihoodAtRate S) =
      Theorem2ObservedWindowCase.productResidualFromSourceSemantics S s C *
        sourcePoissonPMF S.rate
          (totalExposure s fun i => (C i).sourceDataExposureAtRate S)
          (totalCount s fun i => (C i).sourceDataCountAtRate S) := by
  rw [theorem1_source_data_product_decomposition_at_rate S s C h_totalExposure]
  rw [Theorem2ObservedWindowCase.productSourceDataResidualAtRate_eq_productResidualFromSourceSemantics]

theorem theorem1_source_data_product_decomposition_at_rate_same_residual_of_exists_pos_exposure
    {Ω Incident : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (S : theorem2_poisson_process_and_condition_semantics Ω P)
    (s : Finset Incident) (C : Incident → Theorem2ObservedWindowCase)
    (h_exists : ∃ i ∈ s, 0 < (C i).sourceDataExposureAtRate S) :
    (∏ i ∈ s, (C i).sourceDataLikelihoodAtRate S) =
      Theorem2ObservedWindowCase.productResidualFromSourceSemantics S s C *
        sourcePoissonPMF S.rate
          (totalExposure s fun i => (C i).sourceDataExposureAtRate S)
          (totalCount s fun i => (C i).sourceDataCountAtRate S) := by
  exact
    theorem1_source_data_product_decomposition_at_rate_same_residual S s C
      (ne_of_gt
        (totalExposure_pos_of_exists_pos s
          (fun i => (C i).sourceDataExposureAtRate S)
          (fun i _hi => (C i).sourceDataExposureAtRate_nonneg S)
          h_exists))

/--
Finite-data realization of primitive source semantics: Lean constructs an
independent finite Poisson count family at the source process rate and proves
that both the source-semantics and Appendix B.2 source-data products collapse
to the same total-count event probability.
Source status: Lean-checked paper-facing row.
-/
theorem theorem1_exists_finite_poisson_count_family_for_source_semantics_total_count_event_of_exists_pos_exposure
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Incident : Type u} [DecidableEq Incident]
    (S : theorem2_poisson_process_and_condition_semantics Ω P)
    (s : Finset Incident) (C : Incident → Theorem2ObservedWindowCase)
    (h_exists :
      ∃ i ∈ s, 0 < (C i).exposureWith S.conditionFunctions) :
    ∃ Ωc : Type u, ∃ _ : MeasurableSpace Ωc, ∃ Pc : Measure Ωc,
      ∃ Hc : FinitePoissonCountFamily Ωc Pc Incident S.rate
          (fun i => (C i).exposureWith S.conditionFunctions),
        (∏ i ∈ s, (C i).likelihoodFromSourceSemantics S) =
            Theorem2ObservedWindowCase.productResidualWith S.conditionFunctions s C *
              Pc.real {ω : Ωc |
                (∑ i ∈ s, Hc.count i ω) =
                  totalCount s (fun i => (C i).countWith S.conditionFunctions)} ∧
        (∏ i ∈ s, (C i).sourceDataLikelihoodAtRate S) =
            Theorem2ObservedWindowCase.productResidualWith S.conditionFunctions s C *
              Pc.real {ω : Ωc |
                (∑ i ∈ s, Hc.count i ω) =
                  totalCount s (fun i => (C i).countWith S.conditionFunctions)} := by
  rcases exists_finitePoissonCountFamily
      S.rate (le_of_lt S.rate_pos)
      (fun i => (C i).exposureWith S.conditionFunctions)
      (fun i => (C i).exposureWith_nonneg S.conditionFunctions) with
    ⟨Ωc, mΩc, Pc, Hc, _⟩
  exact
    ⟨Ωc, mΩc, Pc, Hc,
      Theorem2ObservedWindowCase.product_likelihoodFromSourceSemantics_eq_productResidual_mul_totalCountEvent_prob_of_exists_pos_exposure
        S s C Hc h_exists,
      Theorem2ObservedWindowCase.product_sourceDataLikelihoodAtRate_eq_productResidual_mul_totalCountEvent_prob_of_exists_pos_exposure
        S s C Hc h_exists⟩

theorem theorem1_exists_finite_poisson_count_family_for_source_semantics_total_count_event_of_exists_pos_source_data_exposure
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Incident : Type u} [DecidableEq Incident]
    (S : theorem2_poisson_process_and_condition_semantics Ω P)
    (s : Finset Incident) (C : Incident → Theorem2ObservedWindowCase)
    (h_exists :
      ∃ i ∈ s, 0 < (C i).sourceDataExposureAtRate S) :
    ∃ Ωc : Type u, ∃ _ : MeasurableSpace Ωc, ∃ Pc : Measure Ωc,
      ∃ Hc : FinitePoissonCountFamily Ωc Pc Incident S.rate
          (fun i => (C i).exposureWith S.conditionFunctions),
        (∏ i ∈ s, (C i).likelihoodFromSourceSemantics S) =
            Theorem2ObservedWindowCase.productResidualWith S.conditionFunctions s C *
              Pc.real {ω : Ωc |
                (∑ i ∈ s, Hc.count i ω) =
                  totalCount s (fun i => (C i).countWith S.conditionFunctions)} ∧
        (∏ i ∈ s, (C i).sourceDataLikelihoodAtRate S) =
            Theorem2ObservedWindowCase.productResidualWith S.conditionFunctions s C *
              Pc.real {ω : Ωc |
                (∑ i ∈ s, Hc.count i ω) =
                  totalCount s (fun i => (C i).countWith S.conditionFunctions)} := by
  have h_exists_with :
      ∃ i ∈ s, 0 < (C i).exposureWith S.conditionFunctions := by
    rcases h_exists with ⟨i, hi, hpos⟩
    refine ⟨i, hi, ?_⟩
    rw [(C i).sourceDataExposureAtRate_eq_exposureFromSourceSemantics S] at hpos
    simpa [Theorem2ObservedWindowCase.exposureFromSourceSemantics] using hpos
  exact
    theorem1_exists_finite_poisson_count_family_for_source_semantics_total_count_event_of_exists_pos_exposure
      S s C h_exists_with

/--
Finite-product Theorem 1 factorization written directly through the Appendix
B.2 source-data objects produced at the source process rate.
Source status: Lean-checked paper-facing row.
-/
theorem theorem1_likelihood_product_decomposition_from_source_data_at_rate
    {Ω Incident : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (S : theorem2_poisson_process_and_condition_semantics Ω P)
    (s : Finset Incident) (C : Incident → Theorem2ObservedWindowCase)
    (h_totalExposure :
      totalExposure s (fun i => (C i).sourceDataExposureAtRate S) ≠ 0) :
    (∏ i ∈ s, (C i).likelihoodFromSourceSemantics S) =
      Theorem2ObservedWindowCase.productResidualFromSourceSemantics S s C *
        sourcePoissonPMF S.rate
          (totalExposure s fun i => (C i).sourceDataExposureAtRate S)
          (totalCount s fun i => (C i).sourceDataCountAtRate S) := by
  exact
    Theorem2ObservedWindowCase.product_factorizationFromSourceSemantics_via_sourceDataAtRate_sameResidual
      S s C h_totalExposure

/--
Finite-product source-semantics factorization written directly through the
derived rate-independent condition functions and source process rate.
Source status: Lean-checked paper-facing row.
-/
theorem theorem1_likelihood_product_decomposition_from_source_semantics_via_rate_likelihood
    {Ω Incident : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (S : theorem2_poisson_process_and_condition_semantics Ω P)
    (s : Finset Incident) (C : Incident → Theorem2ObservedWindowCase)
    (h_totalExposure :
      totalExposure s (fun i => (C i).exposureWith S.conditionFunctions) ≠
        0) :
    (∏ i ∈ s, (C i).likelihoodFromSourceSemantics S) =
      Theorem2ObservedWindowCase.productResidualWith S.conditionFunctions s C *
        sourcePoissonPMF S.rate
          (totalExposure s fun i => (C i).exposureWith S.conditionFunctions)
          (totalCount s fun i => (C i).countWith S.conditionFunctions) := by
  exact
    Theorem2ObservedWindowCase.product_factorizationFromSourceSemantics_via_rateLikelihoodWith
      S s C h_totalExposure

theorem theorem1_likelihood_product_decomposition_from_source_semantics_via_rate_likelihood_of_exists_pos_exposure
    {Ω Incident : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (S : theorem2_poisson_process_and_condition_semantics Ω P)
    (s : Finset Incident) (C : Incident → Theorem2ObservedWindowCase)
    (h_exists :
      ∃ i ∈ s, 0 < (C i).exposureWith S.conditionFunctions) :
    (∏ i ∈ s, (C i).likelihoodFromSourceSemantics S) =
      Theorem2ObservedWindowCase.productResidualWith S.conditionFunctions s C *
        sourcePoissonPMF S.rate
          (totalExposure s fun i => (C i).exposureWith S.conditionFunctions)
          (totalCount s fun i => (C i).countWith S.conditionFunctions) := by
  exact
    Theorem2ObservedWindowCase.product_factorizationFromSourceSemantics_via_rateLikelihoodWith_of_exists_pos_exposure
      S s C h_exists

theorem theorem1_likelihood_product_decomposition_from_source_data_at_rate_of_exists_pos_exposure
    {Ω Incident : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (S : theorem2_poisson_process_and_condition_semantics Ω P)
    (s : Finset Incident) (C : Incident → Theorem2ObservedWindowCase)
    (h_exists : ∃ i ∈ s, 0 < (C i).sourceDataExposureAtRate S) :
    (∏ i ∈ s, (C i).likelihoodFromSourceSemantics S) =
      Theorem2ObservedWindowCase.productResidualFromSourceSemantics S s C *
        sourcePoissonPMF S.rate
          (totalExposure s fun i => (C i).sourceDataExposureAtRate S)
          (totalCount s fun i => (C i).sourceDataCountAtRate S) := by
  exact
    Theorem2ObservedWindowCase.product_factorizationFromSourceSemantics_via_sourceDataAtRate_sameResidual_of_exists_pos_exposure
      S s C h_exists

theorem theorem1_likelihood_product_decomposition_from_source_semantics_of_exists_pos_exposure
    {Ω Incident : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (S : theorem2_poisson_process_and_condition_semantics Ω P)
    (s : Finset Incident) (C : Incident → Theorem2ObservedWindowCase)
    (h_exists :
      ∃ i ∈ s, 0 < (C i).exposureFromSourceSemantics S) :
    (∏ i ∈ s, (C i).likelihoodFromSourceSemantics S) =
      Theorem2ObservedWindowCase.productResidualFromSourceSemantics S s C *
        sourcePoissonPMF S.rate
          (totalExposure s fun i => (C i).exposureFromSourceSemantics S)
          (totalCount s fun i => (C i).countFromSourceSemantics S) := by
  exact
    Theorem2ObservedWindowCase.product_factorizationFromSourceSemantics_of_exists_pos_exposure
      S s C h_exists

/--
Formula-facing primitive-process finite-product form. Prefer the Poisson
increment-law statement above when the model primitives are available as
distribution laws.
Source status: Lean-checked paper-facing row.
-/
theorem theorem1_likelihood_product_decomposition_from_primitive_poisson_process
    {Ω Incident : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : HomogeneousPoissonCountingProcess Ω P)
    (K : Theorem2ConditionFunctions)
    (s : Finset Incident) (C : Incident → Theorem2ObservedWindowCase)
    (h_totalExposure :
      totalExposure s (fun i => (C i).exposureWith K) ≠ 0) :
    (∏ i ∈ s, (C i).likelihoodFromCountingProcess K H) =
      Theorem2ObservedWindowCase.productResidualWith K s C *
        sourcePoissonPMF H.rate
          (totalExposure s fun i => (C i).exposureWith K)
          (totalCount s fun i => (C i).countWith K) := by
  exact Theorem2ObservedWindowCase.product_factorizationFromCountingProcess
    K H s C h_totalExposure

theorem theorem1_likelihood_product_decomposition_from_primitive_poisson_process_of_exists_pos_exposure
    {Ω Incident : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : HomogeneousPoissonCountingProcess Ω P)
    (K : Theorem2ConditionFunctions)
    (s : Finset Incident) (C : Incident → Theorem2ObservedWindowCase)
    (h_exists : ∃ i ∈ s, 0 < (C i).exposureWith K) :
    (∏ i ∈ s, (C i).likelihoodFromCountingProcess K H) =
      Theorem2ObservedWindowCase.productResidualWith K s C *
        sourcePoissonPMF H.rate
          (totalExposure s fun i => (C i).exposureWith K)
          (totalCount s fun i => (C i).countWith K) := by
  exact
    Theorem2ObservedWindowCase.product_factorizationFromCountingProcess_of_exists_pos_exposure
      K H s C h_exists

/--
Bundled source-assumption finite-product form.
Source status: Lean-checked paper-facing row.
-/
theorem theorem1_likelihood_product_decomposition_from_process_law_cases
    {Ω Incident : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (A : assumption_theorem2_poisson_process_and_conditions Ω P)
    (s : Finset Incident) (C : Incident → Theorem2ObservedWindowCase)
    (h_totalExposure :
      totalExposure s (fun i => (C i).exposure A) ≠ 0) :
    (∏ i ∈ s, (C i).likelihood A) =
      Theorem2ObservedWindowCase.productResidual A s C *
        sourcePoissonPMF A.rate
          (totalExposure s fun i => (C i).exposure A)
          (totalCount s fun i => (C i).count A) := by
  exact Theorem2ObservedWindowCase.product_factorization_via_toSourceSemantics
    A s C h_totalExposure

/--
Theorem 1 finite-product form with the total-exposure premise derived from one
positive-exposure observed window.
Source status: Lean-checked paper-facing row.
-/
theorem theorem1_likelihood_product_decomposition_from_process_law_cases_of_exists_pos_exposure
    {Ω Incident : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (A : assumption_theorem2_poisson_process_and_conditions Ω P)
    (s : Finset Incident) (C : Incident → Theorem2ObservedWindowCase)
    (h_exists : ∃ i ∈ s, 0 < (C i).exposure A) :
    (∏ i ∈ s, (C i).likelihood A) =
      Theorem2ObservedWindowCase.productResidual A s C *
        sourcePoissonPMF A.rate
          (totalExposure s fun i => (C i).exposure A)
          (totalCount s fun i => (C i).count A) := by
  exact Theorem2ObservedWindowCase.product_factorization_of_exists_pos_exposure
    A s C h_exists

/--
Theorem 1 finite-product form from source data assembled out of reusable
Poisson no-arrival and interarrival-tail kernels.
Source status: Lean-checked paper-facing row.
-/
theorem theorem1_likelihood_product_decomposition_from_process_source_data
    {Incident : Type*} (s : Finset Incident)
    (D : Incident → Theorem2ProcessSourceData) (rate : ℝ)
    (h_totalExposure :
      totalExposure s (fun i => (D i).exposure) ≠ 0) :
    (∏ i ∈ s, (D i).likelihood rate) =
      theorem2ProcessSourceDataProductResidual s D *
        sourcePoissonPMF rate
          (totalExposure s fun i => (D i).exposure)
          (totalCount s fun i => (D i).count) := by
  exact theorem1_process_source_data_likelihood_product_decomposition
    s D rate h_totalExposure

/--
Theorem 1 finite-product form from source data assembled out of reusable
Poisson no-arrival and interarrival-tail kernels, deriving nonzero total
exposure from one positive row exposure.
Source status: Lean-checked paper-facing row.
-/
theorem theorem1_likelihood_product_decomposition_from_process_source_data_of_exists_pos_exposure
    {Incident : Type*} (s : Finset Incident)
    (D : Incident → Theorem2ProcessSourceData) (rate : ℝ)
    (h_nonneg : ∀ i ∈ s, 0 ≤ (D i).exposure)
    (h_exists : ∃ i ∈ s, 0 < (D i).exposure) :
    (∏ i ∈ s, (D i).likelihood rate) =
      theorem2ProcessSourceDataProductResidual s D *
        sourcePoissonPMF rate
          (totalExposure s fun i => (D i).exposure)
          (totalCount s fun i => (D i).count) := by
  exact
    theorem1_process_source_data_likelihood_product_decomposition_of_exists_pos_exposure
      s D rate h_nonneg h_exists

/-- Appendix B.2 Eq. (20), zero reports in `(s,e]`.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_zero_report_source_case
    (startDensity endDensity rate exposure : ℝ) :
    theorem2ZeroReportLikelihood startDensity endDensity rate exposure =
      theorem2ZeroReportResidual startDensity endDensity *
        sourcePoissonPMF rate exposure 0 := by
  exact theorem2_zero_report_case_factorization
    startDensity endDensity rate exposure

/-- Appendix B.2 Eq. (20), source-labeled zero-report factorization.
Source status: Lean-checked paper-facing row.
-/
theorem equation20_zero_report_source_case
    (startDensity endDensity rate exposure : ℝ) :
    theorem2ZeroReportLikelihood startDensity endDensity rate exposure =
      theorem2ZeroReportResidual startDensity endDensity *
        sourcePoissonPMF rate exposure 0 := by
  exact theorem2_zero_report_source_case
    startDensity endDensity rate exposure

/-- Appendix B.2 Eq. (26), one report in `(s,e]`.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_one_report_source_case
    {startDensity endDensityAfterJump endSurvivalIntegral rate exposure : ℝ}
    (h_exposure : exposure ≠ 0) :
    theorem2OneReportLikelihood
        startDensity endDensityAfterJump endSurvivalIntegral rate exposure =
      (theorem2OneReportKernelResidual
          startDensity endDensityAfterJump endSurvivalIntegral / exposure) *
        sourcePoissonPMF rate exposure 1 := by
  exact theorem2_one_report_case_factorization h_exposure

/-- Appendix B.2 Eq. (26), one report in `(s,e]`, with positive exposure.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_one_report_source_case_of_pos_exposure
    {startDensity endDensityAfterJump endSurvivalIntegral rate exposure : ℝ}
    (h_exposure_pos : 0 < exposure) :
    theorem2OneReportLikelihood
        startDensity endDensityAfterJump endSurvivalIntegral rate exposure =
      (theorem2OneReportKernelResidual
          startDensity endDensityAfterJump endSurvivalIntegral / exposure) *
        sourcePoissonPMF rate exposure 1 := by
  exact theorem2_one_report_case_factorization_of_pos_exposure
    h_exposure_pos

/-- Appendix B.2 Eq. (26), source-labeled one-report factorization.
Source status: Lean-checked paper-facing row.
-/
theorem equation26_one_report_source_case
    {startDensity endDensityAfterJump endSurvivalIntegral rate exposure : ℝ}
    (h_exposure : exposure ≠ 0) :
    theorem2OneReportLikelihood
        startDensity endDensityAfterJump endSurvivalIntegral rate exposure =
      (theorem2OneReportKernelResidual
          startDensity endDensityAfterJump endSurvivalIntegral / exposure) *
        sourcePoissonPMF rate exposure 1 := by
  exact theorem2_one_report_source_case h_exposure

/--
Appendix B.2 Eq. (26), source-labeled one-report factorization with positive
exposure.
Source status: Lean-checked paper-facing row.
-/
theorem equation26_one_report_source_case_of_pos_exposure
    {startDensity endDensityAfterJump endSurvivalIntegral rate exposure : ℝ}
    (h_exposure_pos : 0 < exposure) :
    theorem2OneReportLikelihood
        startDensity endDensityAfterJump endSurvivalIntegral rate exposure =
      (theorem2OneReportKernelResidual
          startDensity endDensityAfterJump endSurvivalIntegral / exposure) *
        sourcePoissonPMF rate exposure 1 := by
  exact theorem2_one_report_source_case_of_pos_exposure h_exposure_pos

/-- Appendix B.2 Eq. (32), two or more reports in `(s,e]`.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_multi_report_source_case
    {startDensity endDensityAfterLastJump survivalIntegralProduct rate exposure : ℝ}
    {count : ℕ} (hcount : 1 < count) (h_exposure : exposure ≠ 0) :
    1 < count ∧
      theorem2MultiReportLikelihood
          startDensity endDensityAfterLastJump survivalIntegralProduct
          rate exposure count =
        theorem2CorrectedResidual
          (theorem2MultiReportKernelResidual
            startDensity endDensityAfterLastJump survivalIntegralProduct)
          exposure count *
          sourcePoissonPMF rate exposure count := by
  exact theorem2_multi_report_case_factorization hcount h_exposure

/--
Appendix B.2 Eq. (32), two or more reports in `(s,e]`, with positive
exposure.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_multi_report_source_case_of_pos_exposure
    {startDensity endDensityAfterLastJump survivalIntegralProduct rate exposure : ℝ}
    {count : ℕ} (hcount : 1 < count) (h_exposure_pos : 0 < exposure) :
    1 < count ∧
      theorem2MultiReportLikelihood
          startDensity endDensityAfterLastJump survivalIntegralProduct
          rate exposure count =
        theorem2CorrectedResidual
          (theorem2MultiReportKernelResidual
            startDensity endDensityAfterLastJump survivalIntegralProduct)
          exposure count *
          sourcePoissonPMF rate exposure count := by
  exact theorem2_multi_report_case_factorization_of_pos_exposure
    hcount h_exposure_pos

/-- Appendix B.2 Eq. (32), source-labeled multi-report factorization.
Source status: Lean-checked paper-facing row.
-/
theorem equation32_multi_report_source_case
    {startDensity endDensityAfterLastJump survivalIntegralProduct rate exposure : ℝ}
    {count : ℕ} (hcount : 1 < count) (h_exposure : exposure ≠ 0) :
    1 < count ∧
      theorem2MultiReportLikelihood
          startDensity endDensityAfterLastJump survivalIntegralProduct
          rate exposure count =
        theorem2CorrectedResidual
          (theorem2MultiReportKernelResidual
            startDensity endDensityAfterLastJump survivalIntegralProduct)
          exposure count *
          sourcePoissonPMF rate exposure count := by
  exact theorem2_multi_report_source_case hcount h_exposure

/--
Appendix B.2 Eq. (32), source-labeled multi-report factorization with positive
exposure.
Source status: Lean-checked paper-facing row.
-/
theorem equation32_multi_report_source_case_of_pos_exposure
    {startDensity endDensityAfterLastJump survivalIntegralProduct rate exposure : ℝ}
    {count : ℕ} (hcount : 1 < count) (h_exposure_pos : 0 < exposure) :
    1 < count ∧
      theorem2MultiReportLikelihood
          startDensity endDensityAfterLastJump survivalIntegralProduct
          rate exposure count =
        theorem2CorrectedResidual
          (theorem2MultiReportKernelResidual
            startDensity endDensityAfterLastJump survivalIntegralProduct)
          exposure count *
          sourcePoissonPMF rate exposure count := by
  exact theorem2_multi_report_source_case_of_pos_exposure
    hcount h_exposure_pos

/--
Appendix B.2 Eq. (30) to Eq. (31): once the interarrival gaps and terminal
tail cover the observed exposure, the Poisson-process rate-dependent kernel
collects to `rate^M * exp(-rate * exposure)`.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_interarrival_kernel_collection
    {Jump : Type*} (jumps : Finset Jump)
    {rate exposure tail : ℝ} (gap : Jump → ℝ)
    (hexposure : (∑ j ∈ jumps, gap j) + tail = exposure) :
    theorem2InterarrivalTailLikelihood jumps rate gap tail =
      rate ^ jumps.card * Real.exp (-(rate * exposure)) := by
  exact theorem2_interarrival_tail_likelihood_eq_exposure_raw_shape
    jumps gap hexposure

/--
Appendix B.2 Eq. (30) to Eq. (31), source-labeled interarrival kernel
collection.
Source status: Lean-checked paper-facing row.
-/
theorem equation30_to_31_interarrival_kernel_collection
    {Jump : Type*} (jumps : Finset Jump)
    {rate exposure tail : ℝ} (gap : Jump → ℝ)
    (hexposure : (∑ j ∈ jumps, gap j) + tail = exposure) :
    theorem2InterarrivalTailLikelihood jumps rate gap tail =
      rate ^ jumps.card * Real.exp (-(rate * exposure)) := by
  exact theorem2_interarrival_kernel_collection jumps gap hexposure

/--
Appendix B.2 Eq. (24) to Eq. (25): the one-report density kernel collects to
the source-shaped `lambda * exp(-lambda * exposure)` likelihood factor.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_one_report_kernel_collection
    {startDensity endDensityAfterJump endSurvivalIntegral rate gap tail exposure : ℝ}
    (hexposure : gap + tail = exposure) :
    theorem2OneReportKernelResidual
        startDensity endDensityAfterJump endSurvivalIntegral *
        interarrivalDensityKernel rate gap * noArrivalProb rate tail =
      theorem2OneReportLikelihood
        startDensity endDensityAfterJump endSurvivalIntegral rate exposure := by
  exact theorem2_one_report_kernel_collects hexposure

/-- Appendix B.2 Eq. (25), source-labeled one-report kernel collection.
Source status: Lean-checked paper-facing row.
-/
theorem equation25_one_report_kernel_collection
    {startDensity endDensityAfterJump endSurvivalIntegral rate gap tail exposure : ℝ}
    (hexposure : gap + tail = exposure) :
    theorem2OneReportKernelResidual
        startDensity endDensityAfterJump endSurvivalIntegral *
        interarrivalDensityKernel rate gap * noArrivalProb rate tail =
      theorem2OneReportLikelihood
        startDensity endDensityAfterJump endSurvivalIntegral rate exposure := by
  exact theorem2_one_report_kernel_collection hexposure

/--
One-report ordered-volume normalization: the interarrival/no-arrival density
kernel times the one-dimensional ordered-jump volume is the one-count Poisson
PMF.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_one_report_ordered_volume_normalization
    {rate gap tail exposure : ℝ}
    (hexposure : gap + tail = exposure)
    (h_exposure : exposure ≠ 0) :
    interarrivalDensityKernel rate gap * noArrivalProb rate tail *
        orderedJumpNestedVolume 1 exposure =
      sourcePoissonPMF rate exposure 1 := by
  exact theorem2_one_report_density_mul_orderedJumpNestedVolume_eq_sourcePoissonPMF
    hexposure h_exposure

/--
One-report ordered-volume normalization with the usual positive exposure
premise.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_one_report_ordered_volume_normalization_of_pos_exposure
    {rate gap tail exposure : ℝ}
    (hexposure : gap + tail = exposure)
    (h_exposure_pos : 0 < exposure) :
    interarrivalDensityKernel rate gap * noArrivalProb rate tail *
        orderedJumpNestedVolume 1 exposure =
      sourcePoissonPMF rate exposure 1 := by
  exact
    theorem2_one_report_density_mul_orderedJumpNestedVolume_eq_sourcePoissonPMF_of_pos_exposure
      hexposure h_exposure_pos

/--
One-report ordered-region volume normalization: the interarrival/no-arrival
density kernel times the Lebesgue volume of the one-dimensional ordered
jump-time region is the one-count Poisson PMF.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_one_report_ordered_region_volume_normalization
    {rate gap tail exposure : ℝ}
    (hexposure : gap + tail = exposure)
    (h_exposure_nonneg : 0 ≤ exposure)
    (h_exposure : exposure ≠ 0) :
    interarrivalDensityKernel rate gap * noArrivalProb rate tail *
        (volume (orderedJumpRegion 1 exposure)).toReal =
      sourcePoissonPMF rate exposure 1 := by
  exact theorem2_one_report_density_mul_orderedJumpRegionVolume_eq_sourcePoissonPMF
    hexposure h_exposure_nonneg h_exposure

/--
One-report ordered-region volume normalization with the usual positive
exposure premise.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_one_report_ordered_region_volume_normalization_of_pos_exposure
    {rate gap tail exposure : ℝ}
    (hexposure : gap + tail = exposure)
    (h_exposure_pos : 0 < exposure) :
    interarrivalDensityKernel rate gap * noArrivalProb rate tail *
        (volume (orderedJumpRegion 1 exposure)).toReal =
      sourcePoissonPMF rate exposure 1 := by
  exact
    theorem2_one_report_density_mul_orderedJumpRegionVolume_eq_sourcePoissonPMF_of_pos_exposure
      hexposure h_exposure_pos

/--
Two-report ordered-region volume normalization: the interarrival/no-arrival
density kernel times the Lebesgue volume of the two-dimensional ordered
jump-time region is the two-count Poisson PMF.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_two_report_ordered_region_volume_normalization
    {rate exposure tail : ℝ} (gap : Fin 2 → ℝ)
    (hexposure : (∑ j : Fin 2, gap j) + tail = exposure)
    (h_exposure_nonneg : 0 ≤ exposure)
    (h_exposure : exposure ≠ 0) :
    theorem2InterarrivalTailLikelihood (Finset.univ : Finset (Fin 2))
        rate gap tail *
        (volume (orderedJumpRegion 2 exposure)).toReal =
      sourcePoissonPMF rate exposure 2 := by
  exact theorem2_two_report_density_mul_orderedJumpRegionVolume_eq_sourcePoissonPMF
    gap hexposure h_exposure_nonneg h_exposure

/--
Two-report ordered-region volume normalization with the usual positive
exposure premise.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_two_report_ordered_region_volume_normalization_of_pos_exposure
    {rate exposure tail : ℝ} (gap : Fin 2 → ℝ)
    (hexposure : (∑ j : Fin 2, gap j) + tail = exposure)
    (h_exposure_pos : 0 < exposure) :
    theorem2InterarrivalTailLikelihood (Finset.univ : Finset (Fin 2))
        rate gap tail *
        (volume (orderedJumpRegion 2 exposure)).toReal =
      sourcePoissonPMF rate exposure 2 := by
  exact theorem2_two_report_density_mul_orderedJumpRegionVolume_eq_sourcePoissonPMF_of_pos_exposure
    gap hexposure h_exposure_pos

/--
Multi-report ordered-region volume normalization: the interarrival/no-arrival
density kernel times the actual Lebesgue volume of the finite ordered
jump-time region is the matching Poisson count PMF.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_multi_report_ordered_region_volume_normalization
    {count : ℕ} {rate exposure tail : ℝ} (gap : Fin count → ℝ)
    (hexposure : (∑ j : Fin count, gap j) + tail = exposure)
    (h_exposure_nonneg : 0 ≤ exposure)
    (h_exposure : exposure ≠ 0) :
    theorem2InterarrivalTailLikelihood (Finset.univ : Finset (Fin count))
        rate gap tail *
        (volume (orderedJumpRegion count exposure)).toReal =
      sourcePoissonPMF rate exposure count := by
  exact theorem2_multi_report_density_mul_orderedJumpRegionVolume_eq_sourcePoissonPMF
    gap hexposure h_exposure_nonneg h_exposure

/--
Multi-report ordered-region volume normalization with the usual positive
exposure premise.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_multi_report_ordered_region_volume_normalization_of_pos_exposure
    {count : ℕ} {rate exposure tail : ℝ} (gap : Fin count → ℝ)
    (hexposure : (∑ j : Fin count, gap j) + tail = exposure)
    (h_exposure_pos : 0 < exposure) :
    theorem2InterarrivalTailLikelihood (Finset.univ : Finset (Fin count))
        rate gap tail *
        (volume (orderedJumpRegion count exposure)).toReal =
      sourcePoissonPMF rate exposure count := by
  exact theorem2_multi_report_density_mul_orderedJumpRegionVolume_eq_sourcePoissonPMF_of_pos_exposure
    gap hexposure h_exposure_pos

/--
Appendix B.2 Eq. (30) to Eq. (31): the multi-report interarrival-density
product and terminal no-arrival tail collect to the source-shaped
`lambda^M * exp(-lambda * exposure)` likelihood factor.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_multi_report_kernel_collection
    {Jump : Type*} (jumps : Finset Jump)
    {startDensity endDensityAfterLastJump survivalIntegralProduct rate exposure tail : ℝ}
    {count : ℕ} (gap : Jump → ℝ)
    (hcard : jumps.card = count)
    (hexposure : (∑ j ∈ jumps, gap j) + tail = exposure) :
    theorem2MultiReportKernelResidual
        startDensity endDensityAfterLastJump survivalIntegralProduct *
        theorem2InterarrivalTailLikelihood jumps rate gap tail =
      theorem2MultiReportLikelihood
        startDensity endDensityAfterLastJump survivalIntegralProduct
        rate exposure count := by
  exact theorem2_multi_report_kernel_collects jumps gap hcard hexposure

/-- Appendix B.2 Eq. (31), source-labeled multi-report kernel collection.
Source status: Lean-checked paper-facing row.
-/
theorem equation31_multi_report_kernel_collection
    {Jump : Type*} (jumps : Finset Jump)
    {startDensity endDensityAfterLastJump survivalIntegralProduct rate exposure tail : ℝ}
    {count : ℕ} (gap : Jump → ℝ)
    (hcard : jumps.card = count)
    (hexposure : (∑ j ∈ jumps, gap j) + tail = exposure) :
    theorem2MultiReportKernelResidual
        startDensity endDensityAfterLastJump survivalIntegralProduct *
        theorem2InterarrivalTailLikelihood jumps rate gap tail =
      theorem2MultiReportLikelihood
        startDensity endDensityAfterLastJump survivalIntegralProduct
        rate exposure count := by
  exact theorem2_multi_report_kernel_collection jumps gap hcard hexposure

/--
Explicit Appendix B.2 process-kernel cases agree with the corresponding
source-shaped cases after the no-arrival/interarrival kernels are collected.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_process_kernel_case_refines_source_case
    (C : Theorem2ProcessKernelCase) (rate : ℝ) :
    C.likelihood rate = C.toSourceCase.likelihood rate := by
  exact C.likelihood_eq_toSourceCase_likelihood rate

/--
Appendix B.2 process-kernel factorization routed through the collapsed
source-shaped case. This exposes the refinement relation between the explicit
kernel layer and the source-case algebra.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_process_kernel_case_factorization_via_source_case_row
    (C : Theorem2ProcessKernelCase) (rate : ℝ) :
    C.likelihood rate =
      C.residual * sourcePoissonPMF rate C.exposure C.count := by
  exact theorem2_process_kernel_case_factorization_via_source_case C rate

/--
Appendix B.2 Eq. (18) to Eq. (20): the zero-report process-kernel likelihood
factors into the source Poisson zero-count PMF and a rate-independent residual.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_zero_report_process_kernel_source_case
    (startDensity endDensity rate exposure : ℝ) :
    theorem2ZeroReportProcessKernelLikelihood
        startDensity endDensity rate exposure =
      theorem2ZeroReportResidual startDensity endDensity *
        sourcePoissonPMF rate exposure 0 := by
  exact theorem2_zero_report_process_kernel_factorization
    startDensity endDensity rate exposure

/--
Appendix B.2 Eq. (18) to Eq. (20), source-labeled zero-report process-kernel
factorization.
Source status: Lean-checked paper-facing row.
-/
theorem equation18_to_20_zero_report_process_kernel_source_case
    (startDensity endDensity rate exposure : ℝ) :
    theorem2ZeroReportProcessKernelLikelihood
        startDensity endDensity rate exposure =
      theorem2ZeroReportResidual startDensity endDensity *
        sourcePoissonPMF rate exposure 0 := by
  exact theorem2_zero_report_process_kernel_source_case
    startDensity endDensity rate exposure

/--
Appendix B.2 Eq. (23) to Eq. (26): the one-report process-kernel likelihood
factors into the source Poisson one-count PMF and a rate-independent residual.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_one_report_process_kernel_source_case
    {startDensity endDensityAfterJump endSurvivalIntegral rate gap tail exposure : ℝ}
    (hexposure : gap + tail = exposure) (h_exposure : exposure ≠ 0) :
    theorem2OneReportProcessKernelLikelihood
        startDensity endDensityAfterJump endSurvivalIntegral rate gap tail =
      (theorem2OneReportKernelResidual
          startDensity endDensityAfterJump endSurvivalIntegral / exposure) *
        sourcePoissonPMF rate exposure 1 := by
  exact theorem2_one_report_process_kernel_factorization
    hexposure h_exposure

/--
Appendix B.2 Eq. (23) to Eq. (26), one-report process-kernel factorization
with positive exposure.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_one_report_process_kernel_source_case_of_pos_exposure
    {startDensity endDensityAfterJump endSurvivalIntegral rate gap tail exposure : ℝ}
    (hexposure : gap + tail = exposure) (h_exposure_pos : 0 < exposure) :
    theorem2OneReportProcessKernelLikelihood
        startDensity endDensityAfterJump endSurvivalIntegral rate gap tail =
      (theorem2OneReportKernelResidual
          startDensity endDensityAfterJump endSurvivalIntegral / exposure) *
        sourcePoissonPMF rate exposure 1 := by
  exact theorem2_one_report_process_kernel_factorization_of_pos_exposure
    hexposure h_exposure_pos

/--
Appendix B.2 Eq. (23) to Eq. (26), source-labeled one-report process-kernel
factorization.
Source status: Lean-checked paper-facing row.
-/
theorem equation23_to_26_one_report_process_kernel_source_case
    {startDensity endDensityAfterJump endSurvivalIntegral rate gap tail exposure : ℝ}
    (hexposure : gap + tail = exposure) (h_exposure : exposure ≠ 0) :
    theorem2OneReportProcessKernelLikelihood
        startDensity endDensityAfterJump endSurvivalIntegral rate gap tail =
      (theorem2OneReportKernelResidual
          startDensity endDensityAfterJump endSurvivalIntegral / exposure) *
        sourcePoissonPMF rate exposure 1 := by
  exact theorem2_one_report_process_kernel_source_case
    hexposure h_exposure

/--
Appendix B.2 Eq. (23) to Eq. (26), source-labeled one-report process-kernel
factorization with positive exposure.
Source status: Lean-checked paper-facing row.
-/
theorem equation23_to_26_one_report_process_kernel_source_case_of_pos_exposure
    {startDensity endDensityAfterJump endSurvivalIntegral rate gap tail exposure : ℝ}
    (hexposure : gap + tail = exposure) (h_exposure_pos : 0 < exposure) :
    theorem2OneReportProcessKernelLikelihood
        startDensity endDensityAfterJump endSurvivalIntegral rate gap tail =
      (theorem2OneReportKernelResidual
          startDensity endDensityAfterJump endSurvivalIntegral / exposure) *
        sourcePoissonPMF rate exposure 1 := by
  exact theorem2_one_report_process_kernel_source_case_of_pos_exposure
    hexposure h_exposure_pos

/--
Appendix B.2 Eq. (29) to Eq. (32): the multi-report process-kernel likelihood
factors into the source Poisson count PMF and a rate-independent residual.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_multi_report_process_kernel_source_case
    {Jump : Type*} (jumps : Finset Jump)
    {startDensity endDensityAfterLastJump survivalIntegralProduct rate exposure tail : ℝ}
    {count : ℕ} (gap : Jump → ℝ)
    (hcard : jumps.card = count)
    (hexposure : (∑ j ∈ jumps, gap j) + tail = exposure)
    (hcount : 1 < count) (h_exposure : exposure ≠ 0) :
    1 < count ∧
      theorem2MultiReportProcessKernelLikelihood
          jumps startDensity endDensityAfterLastJump survivalIntegralProduct
          rate gap tail =
        theorem2CorrectedResidual
          (theorem2MultiReportKernelResidual
            startDensity endDensityAfterLastJump survivalIntegralProduct)
          exposure count *
          sourcePoissonPMF rate exposure count := by
  exact theorem2_multi_report_process_kernel_factorization
    jumps gap hcard hexposure hcount h_exposure

/--
Appendix B.2 Eq. (29) to Eq. (32), multi-report process-kernel factorization
with positive exposure.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_multi_report_process_kernel_source_case_of_pos_exposure
    {Jump : Type*} (jumps : Finset Jump)
    {startDensity endDensityAfterLastJump survivalIntegralProduct rate exposure tail : ℝ}
    {count : ℕ} (gap : Jump → ℝ)
    (hcard : jumps.card = count)
    (hexposure : (∑ j ∈ jumps, gap j) + tail = exposure)
    (hcount : 1 < count) (h_exposure_pos : 0 < exposure) :
    1 < count ∧
      theorem2MultiReportProcessKernelLikelihood
          jumps startDensity endDensityAfterLastJump survivalIntegralProduct
          rate gap tail =
        theorem2CorrectedResidual
          (theorem2MultiReportKernelResidual
            startDensity endDensityAfterLastJump survivalIntegralProduct)
          exposure count *
          sourcePoissonPMF rate exposure count := by
  exact theorem2_multi_report_process_kernel_factorization_of_pos_exposure
    jumps gap hcard hexposure hcount h_exposure_pos

/--
Appendix B.2 Eq. (29) to Eq. (32), source-labeled multi-report process-kernel
factorization.
Source status: Lean-checked paper-facing row.
-/
theorem equation29_to_32_multi_report_process_kernel_source_case
    {Jump : Type*} (jumps : Finset Jump)
    {startDensity endDensityAfterLastJump survivalIntegralProduct rate exposure tail : ℝ}
    {count : ℕ} (gap : Jump → ℝ)
    (hcard : jumps.card = count)
    (hexposure : (∑ j ∈ jumps, gap j) + tail = exposure)
    (hcount : 1 < count) (h_exposure : exposure ≠ 0) :
    1 < count ∧
      theorem2MultiReportProcessKernelLikelihood
          jumps startDensity endDensityAfterLastJump survivalIntegralProduct
          rate gap tail =
        theorem2CorrectedResidual
          (theorem2MultiReportKernelResidual
            startDensity endDensityAfterLastJump survivalIntegralProduct)
          exposure count *
          sourcePoissonPMF rate exposure count := by
  exact theorem2_multi_report_process_kernel_source_case
    jumps gap hcard hexposure hcount h_exposure

/--
Appendix B.2 Eq. (29) to Eq. (32), source-labeled multi-report process-kernel
factorization with positive exposure.
Source status: Lean-checked paper-facing row.
-/
theorem equation29_to_32_multi_report_process_kernel_source_case_of_pos_exposure
    {Jump : Type*} (jumps : Finset Jump)
    {startDensity endDensityAfterLastJump survivalIntegralProduct rate exposure tail : ℝ}
    {count : ℕ} (gap : Jump → ℝ)
    (hcard : jumps.card = count)
    (hexposure : (∑ j ∈ jumps, gap j) + tail = exposure)
    (hcount : 1 < count) (h_exposure_pos : 0 < exposure) :
    1 < count ∧
      theorem2MultiReportProcessKernelLikelihood
          jumps startDensity endDensityAfterLastJump survivalIntegralProduct
          rate gap tail =
        theorem2CorrectedResidual
          (theorem2MultiReportKernelResidual
            startDensity endDensityAfterLastJump survivalIntegralProduct)
          exposure count *
          sourcePoissonPMF rate exposure count := by
  exact theorem2_multi_report_process_kernel_source_case_of_pos_exposure
    jumps gap hcard hexposure hcount h_exposure_pos

/--
Appendix Theorem 2 proof algebra: a case likelihood whose rate dependence has
the raw density shape `rate^M * exp(-rate * exposure)` factors into the Poisson
count PMF after absorbing `M! / exposure^M` into the residual.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_corrected_case_factorization
    {kernelResidual rate exposure : ℝ} {count : ℕ}
    (h_exposure : exposure ≠ 0) :
    theorem2RawCaseLikelihood kernelResidual rate exposure count =
      theorem2CorrectedResidual kernelResidual exposure count *
        sourcePoissonPMF rate exposure count := by
  exact theorem2_raw_case_likelihood_factorizes h_exposure

/--
Appendix Theorem 2 proof algebra with positive exposure instead of a raw
nonzero denominator premise.
Source status: Lean-checked paper-facing row.
-/
theorem theorem2_corrected_case_factorization_of_pos_exposure
    {kernelResidual rate exposure : ℝ} {count : ℕ}
    (h_exposure_pos : 0 < exposure) :
    theorem2RawCaseLikelihood kernelResidual rate exposure count =
      theorem2CorrectedResidual kernelResidual exposure count *
        sourcePoissonPMF rate exposure count := by
  exact theorem2_corrected_case_factorization (ne_of_gt h_exposure_pos)

/--
Appendix Theorem 2 / Eq. (8), finite causal endpoint-clock form.  The exact
timeline density is a rate-free residual times the Poisson count PMF.  The
first gap is `t_{m+1}-s` and the residual multiplier is `M!/(e-s)^M`.

Source status: Lean-checked corrected finite causal density formulation.
-/
theorem theorem2_causal_endpoint_clock_eq8
    (T : OrderedFiniteJumpTimeline)
    (M : assumption_theorem2_causal_endpoint_model T.count)
    {rate : ℝ} (h_rate : 0 < rate) (h_exposure : 0 < T.window.exposure) :
    CollapsedFiniteStageEndpointModel.theorem2CausalConditionalLikelihood T M rate =
      M.toFiniteStageCausalEndpointProfile.correctedResidual *
        sourcePoissonPMF rate T.window.exposure T.count := by
  exact CollapsedFiniteStageEndpointModel.theorem2CausalConditionalLikelihood_factorizes_corrected_eq8
    T M h_rate h_exposure

/--
The finite causal density formulation of Theorem 1 is the corrected
Appendix-Theorem-2 factorization above.

Source status: Lean-checked corrected finite causal density formulation.
-/
theorem theorem1_causal_endpoint_clock_likelihood_decomposition
    (T : OrderedFiniteJumpTimeline)
    (M : assumption_theorem2_causal_endpoint_model T.count)
    {rate : ℝ} (h_rate : 0 < rate) (h_exposure : 0 < T.window.exposure) :
    CollapsedFiniteStageEndpointModel.theorem2CausalConditionalLikelihood T M rate =
      M.toFiniteStageCausalEndpointProfile.correctedResidual *
        sourcePoissonPMF rate T.window.exposure T.count :=
  theorem2_causal_endpoint_clock_eq8 T M h_rate h_exposure

/--
The causal endpoint model defines a finite fixed-history observation likelihood
measure.  Its density contains the exponential report-gap block, endpoint-clock
survival factors, terminal endpoint density, and terminal no-report tail.

Source status: Lean-checked causal density construction.
-/
theorem theorem2_causal_endpoint_observation_likelihood_measure
    {count : ℕ} (M : assumption_theorem2_causal_endpoint_model count)
    {rate : ℝ} (h_rate : 0 < rate) :
    M.collapsedObservationLaw rate =
      ((volume : Measure (Fin count → ℝ)).prod (volume : Measure ℝ)).withDensity
        (M.rawGapTailDensity rate) := by
  exact M.collapsedObservationLaw_eq_withDensity_rawGapTailDensity h_rate

/--
The density convention for the continuous likelihood notation in Appendix
Theorem 2: the finite causal model represents a fixed observed realization by
the density of its observation likelihood measure at that timeline.

Source status: Lean-checked model-density interpretation; this row does not identify the density with the source conditional likelihood.
-/
theorem theorem2_causal_endpoint_observation_density_representation
    (T : OrderedFiniteJumpTimeline)
    (M : assumption_theorem2_causal_endpoint_model T.count)
    (rate : ℝ) :
    CollapsedFiniteStageEndpointModel.theorem2CausalConditionalLikelihood T M rate =
      (M.rawGapTailDensity rate (T.gap, T.tail)).toReal := rfl

/-!
### Generated density construction

The legacy density-only model is
`assumption_theorem2_stationary_palm_causal_observation_model`: a stationary
report source with a Palm-tagged arrival, normalized causal endpoint kernels,
and a common selected-start density.  Its endpoint response is generated from
the Palm gap marginal; it is not an actual endpoint-variable pushforward on
the original source carrier.
-/

/--
The generated stationary/Palm density construction is the collapsed finite
causal observation law obtained by integrating an accepted endpoint-response
kernel against the Palm post-tag report-gap block.

This is a construction equality, not a source-carrier pushforward theorem and
not a separately numbered source statement.
-/
theorem theorem2_stationary_palm_source_observation_law_bridge
    {OmegaBase Omega : Type*}
    [MeasurableSpace OmegaBase] [MeasurableSpace Omega]
    {P : Measure Omega} {count : ℕ} {rate : ℝ}
    (M : assumption_theorem2_stationary_palm_causal_observation_model
      OmegaBase Omega P count rate) :
    M.sourceObservationLaw =
      M.endpointSource.toCollapsedFiniteStageEndpointModel.collapsedObservationLaw rate := by
  exact M.sourceObservationLaw_eq_collapsedObservationLaw

/--
The generated stationary/Palm density construction has the explicit density consisting
of the Poisson report-gap density, the product of causal endpoint-survival
factors, the terminal endpoint density, and the final response-tail factor.

This measure-theoretic density representation makes the source likelihood
construction explicit; it is not a separately numbered source statement.
Source status: Lean-checked generated-model proof-support row; it does not by
itself establish a source-carrier bridge.
-/
theorem theorem2_stationary_palm_source_observation_density
    {OmegaBase Omega : Type*}
    [MeasurableSpace OmegaBase] [MeasurableSpace Omega]
    {P : Measure Omega} {count : ℕ} {rate : ℝ}
    (M : assumption_theorem2_stationary_palm_causal_observation_model
      OmegaBase Omega P count rate) :
    M.sourceObservationLaw =
      ((volume : Measure (Fin count → ℝ)).prod (volume : Measure ℝ)).withDensity
        (M.endpointSource.toCollapsedFiniteStageEndpointModel.rawGapTailDensity rate) := by
  exact M.sourceObservationLaw_eq_withDensity_rawGapTailDensity

/--
Appendix Theorem 2 / Eq. (8), source-causal-stopping form.  At the conditioned
pre-start history, the selected-start contribution and the live endpoint policy
are rate-free.  At each visible report prefix, the policy has only that prefix
as input and chooses an immediate endpoint-response law before the next
Poisson gap.  In the source's continuous `h_m(e)` presentation this gives a
fixed-history likelihood density equal to a rate-free residual times the
Poisson count PMF.

The source wording used here is the main theorem's endpoint independence from
`S` conditional on reports observed up to the endpoint together with the
application's stopping-times reading (source.txt:254-300;2086-2110).  Appendix
B.2's final independence display is a terse restatement and must be read at
that history-conditioned level; marginal independence only after `T1` is not
sufficient.  The first-gap and reciprocal-residual clarifications are
source-proof notes, not additional model assumptions.

Source status: Lean-checked paper-facing source-model theorem for
source.txt:254-300;1567-1590;1675-1883;2086-2110.
-/
def appendixTheorem2Eq8CausalStoppingSourceSpec
    (T : OrderedFiniteJumpTimeline)
    (M : AppendixTheorem2CausalStoppingSourceModel T.count)
    (D : LBG24SpatialUnderreporting.AppendixTheorem2CausalStoppingSourceModel.EndpointDensityPresentation M)
    {rate : ℝ} (rate_pos : 0 < rate)
    (exposure_pos : 0 < T.window.exposure) : Prop :=
    AppendixTheorem2CausalStoppingSourceModel.conditionalLikelihood T M D rate =
      AppendixTheorem2CausalStoppingSourceModel.rateFreeResidual T M D *
        sourcePoissonPMF rate T.window.exposure T.count

theorem appendix_theorem2_eq8_causal_stopping_source_model
    (T : OrderedFiniteJumpTimeline)
    (M : AppendixTheorem2CausalStoppingSourceModel T.count)
    (D : LBG24SpatialUnderreporting.AppendixTheorem2CausalStoppingSourceModel.EndpointDensityPresentation M)
    {rate : ℝ} (rate_pos : 0 < rate)
    (exposure_pos : 0 < T.window.exposure) :
    AppendixTheorem2CausalStoppingSourceModel.conditionalLikelihood T M D rate =
      AppendixTheorem2CausalStoppingSourceModel.rateFreeResidual T M D *
        sourcePoissonPMF rate T.window.exposure T.count := by
  exact AppendixTheorem2CausalStoppingSourceModel.conditionalLikelihood_factorizes_eq8
    M D rate_pos exposure_pos

/-- Eq. (7) nonnegativity under the ordinary mixture and Poisson-mean bounds.
Source status: Lean-checked paper-facing row.
-/
theorem equation7_zero_inflated_likelihood_nonnegative
    {gamma rate exposure : ℝ} {count : ℕ}
    (hgamma_nonneg : 0 ≤ gamma) (hgamma_le_one : gamma ≤ 1)
    (hmean : 0 ≤ rate * exposure) :
    0 ≤ zeroInflatedIncidentLikelihood gamma rate exposure count := by
  exact zeroInflatedIncidentLikelihood_nonneg
    hgamma_nonneg hgamma_le_one hmean

end

end LBG24SpatialUnderreporting
