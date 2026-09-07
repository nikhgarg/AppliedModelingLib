import AppliedModelingLib.Foundations.Probability.PoissonStopping
import AppliedModelingLib.Foundations.Probability.RenewalReward
import Mathlib.Tactic

/-!
# Quantifying Spatial Under-reporting Disparities: Implementation Theorems

This file contains the Lean implementation layer for Liu, Bhandaram, and Garg
2024.  It keeps source-facing probability formulas in the paper namespace while
reusing the generic Poisson-count algebra in
`AppliedModelingLib.Foundations.Probability.PoissonProcess`.

The continuous-time process construction in Appendix B.2 is represented here by
explicit likelihood-factorization inputs.  Downstream algebra is proved in Lean;
the full measure-theoretic stopping-window/process-kernel construction is a
separate reusable-library seam.
-/

namespace LBG24SpatialUnderreporting

open Finset
open Filter
open MeasureTheory
open AppliedModelingLib.Probability.PoissonProcess
open scoped Function ProbabilityTheory Topology

noncomputable section

/-! ## Source Formulas -/

/-- Observation exposure `e - s` for an interval `(s,e]`. -/
def observationExposure (startTime endTime : ℝ) : ℝ :=
  endTime - startTime

/-- The paper's Poisson count mass `p(M; rate * exposure)`. -/
def sourcePoissonPMF (rate exposure : ℝ) (count : ℕ) : ℝ :=
  countLikelihood rate exposure count

/-- Equation (2)'s Poisson mass on its stated positive-parameter domain.

`sourcePoissonPMF` remains the total algebraic expression used by historical
proof infrastructure.  Paper-facing Specs carry the source's
`rate * exposure > 0` parameter condition as an ordinary premise; it is not a
proof-irrelevant argument to the displayed mass itself. -/
def sourcePoissonPMFOnSourceDomain (rate exposure : ℝ) (count : ℕ) : ℝ :=
  countLikelihood rate exposure count

/-- Probability that an active incident receives at least one report. -/
def firstReportProbability (reportingRate duration : ℝ) : ℝ :=
  atLeastOneArrivalProb reportingRate duration

/--
Homogeneous-duration observed unique-incident rate:
occurrence rate times the probability of at least one report.
-/
def homogeneousObservedIncidentRate
    (incidentRate reportingRate duration : ℝ) : ℝ :=
  incidentRate * firstReportProbability reportingRate duration

/--
Finite-support version of the no-report probability averaged over an incident
duration distribution.
-/
def finiteDurationNoReportProbability
    {DurationType : Type*} [Fintype DurationType]
    (reportingRate : ℝ) (weight duration : DurationType → ℝ) : ℝ :=
  ∑ d, weight d * noArrivalProb reportingRate (duration d)

/--
Finite-support version of the probability that an incident receives at least
one report before it dies.
-/
def finiteDurationFirstReportProbability
    {DurationType : Type*} [Fintype DurationType]
    (reportingRate : ℝ) (weight duration : DurationType → ℝ) : ℝ :=
  1 - finiteDurationNoReportProbability reportingRate weight duration

/--
Continuous-duration no-report probability over nonnegative incident lifetimes,
matching Lemma 1's integral over `[0,∞)` in the homogeneous-rate case.
-/
def continuousDurationNoReportProbability
    (reportingRate : ℝ) (durationDensity : ℝ → ℝ) : ℝ :=
  ∫ t, durationDensity t * noArrivalProb reportingRate t
    ∂(volume.restrict (Set.Ici (0 : ℝ)))

/--
Continuous-duration first-report probability over nonnegative incident
lifetimes in the homogeneous-rate case.
-/
def continuousDurationFirstReportProbability
    (reportingRate : ℝ) (durationDensity : ℝ → ℝ) : ℝ :=
  1 - continuousDurationNoReportProbability reportingRate durationDensity

/--
Continuous-duration observed unique-incident rate from Lemma 1 / Proposition 1:
occurrence rate times the average probability of at least one report.
-/
def continuousDurationObservedIncidentRate
    (incidentRate reportingRate : ℝ) (durationDensity : ℝ → ℝ) : ℝ :=
  incidentRate *
    continuousDurationFirstReportProbability reportingRate durationDensity

/--
Nonhomogeneous per-duration first-report probability from a cumulative
reporting intensity `∫₀ᵗ λ(u)du`.
-/
def cumulativeIntensityFirstReportProbability
    (cumulativeIntensity : ℝ → ℝ) (duration : ℝ) : ℝ :=
  1 - Real.exp (-(cumulativeIntensity duration))

/--
Continuous-duration no-report probability for Lemma 1's nonhomogeneous
reporting-rate formula, expressed through the cumulative reporting intensity.
-/
def continuousDurationNoReportProbabilityOfCumulativeIntensity
    (cumulativeIntensity durationDensity : ℝ → ℝ) : ℝ :=
  ∫ t, durationDensity t * Real.exp (-(cumulativeIntensity t))
    ∂(volume.restrict (Set.Ici (0 : ℝ)))

/-- Continuous-duration first-report probability for a cumulative intensity. -/
def continuousDurationFirstReportProbabilityOfCumulativeIntensity
    (cumulativeIntensity durationDensity : ℝ → ℝ) : ℝ :=
  1 -
    continuousDurationNoReportProbabilityOfCumulativeIntensity
      cumulativeIntensity durationDensity

/-- Continuous-duration observed incident rate for a cumulative intensity. -/
def continuousDurationObservedIncidentRateOfCumulativeIntensity
    (incidentRate : ℝ) (cumulativeIntensity durationDensity : ℝ → ℝ) : ℝ :=
  incidentRate *
    continuousDurationFirstReportProbabilityOfCumulativeIntensity
      cumulativeIntensity durationDensity

theorem continuousDurationNoReportProbabilityOfCumulativeIntensity_homogeneous
    (reportingRate : ℝ) (durationDensity : ℝ → ℝ) :
    continuousDurationNoReportProbabilityOfCumulativeIntensity
        (fun t => reportingRate * t) durationDensity =
      continuousDurationNoReportProbability reportingRate durationDensity := by
  simp [continuousDurationNoReportProbabilityOfCumulativeIntensity,
    continuousDurationNoReportProbability, noArrivalProb]

theorem continuousDurationFirstReportProbabilityOfCumulativeIntensity_homogeneous
    (reportingRate : ℝ) (durationDensity : ℝ → ℝ) :
    continuousDurationFirstReportProbabilityOfCumulativeIntensity
        (fun t => reportingRate * t) durationDensity =
      continuousDurationFirstReportProbability reportingRate durationDensity := by
  simp [continuousDurationFirstReportProbabilityOfCumulativeIntensity,
    continuousDurationFirstReportProbability,
    continuousDurationNoReportProbabilityOfCumulativeIntensity_homogeneous]

theorem continuousDurationObservedIncidentRateOfCumulativeIntensity_homogeneous
    (incidentRate reportingRate : ℝ) (durationDensity : ℝ → ℝ) :
    continuousDurationObservedIncidentRateOfCumulativeIntensity
        incidentRate (fun t => reportingRate * t) durationDensity =
      continuousDurationObservedIncidentRate
        incidentRate reportingRate durationDensity := by
  simp [continuousDurationObservedIncidentRateOfCumulativeIntensity,
    continuousDurationObservedIncidentRate,
    continuousDurationFirstReportProbabilityOfCumulativeIntensity_homogeneous]

/--
Finite-support observed unique-incident rate from Proposition 1 / Lemma 1:
occurrence rate times the average probability of at least one report.
-/
def finiteDurationObservedIncidentRate
    {DurationType : Type*} [Fintype DurationType]
    (incidentRate reportingRate : ℝ)
    (weight duration : DurationType → ℝ) : ℝ :=
  incidentRate *
    finiteDurationFirstReportProbability reportingRate weight duration

/--
The count likelihood factor in Theorem 1 / Appendix Theorem 2:
`p(M; rate * (e-s))`.
-/
def theorem1PoissonFactor
    (rate startTime endTime : ℝ) (count : ℕ) : ℝ :=
  sourcePoissonPMF rate (observationExposure startTime endTime) count

/--
Raw likelihood shape obtained in the Appendix B.2 case analysis after all
rate-independent density factors have been collected into `kernelResidual`.
-/
def theorem2RawCaseLikelihood
    (kernelResidual rate exposure : ℝ) (count : ℕ) : ℝ :=
  kernelResidual * rate ^ count * Real.exp (-(rate * exposure))

/--
Corrected rate-independent residual needed to rewrite the raw case likelihood
as a Poisson count likelihood.
-/
def theorem2CorrectedResidual
    (kernelResidual exposure : ℝ) (count : ℕ) : ℝ :=
  kernelResidual * (count.factorial : ℝ) / exposure ^ count

/--
The source-literal residual printed in the Appendix B.2 `M > 1` case.  This is
kept separate from `theorem2CorrectedResidual` because the printed formula has
the reciprocal factor relative to the displayed Poisson PMF.
-/
def theorem2PrintedMgtOneResidual
    (kernelResidual exposure : ℝ) (count : ℕ) : ℝ :=
  kernelResidual * exposure ^ count / (count.factorial : ℝ)

/-- Appendix B.2 zero-report case residual `g(s) h_m(e)`. -/
def theorem2ZeroReportResidual (startDensity endDensity : ℝ) : ℝ :=
  startDensity * endDensity

/--
Appendix B.2 zero-report case likelihood:
`g(s) h_m(e) exp (-rate * exposure)`.
-/
def theorem2ZeroReportLikelihood
    (startDensity endDensity rate exposure : ℝ) : ℝ :=
  theorem2ZeroReportResidual startDensity endDensity *
    Real.exp (-(rate * exposure))

/--
Appendix B.2 zero-report process-kernel likelihood before rewriting the
terminal no-arrival probability as an exponential.
-/
def theorem2ZeroReportProcessKernelLikelihood
    (startDensity endDensity rate exposure : ℝ) : ℝ :=
  theorem2ZeroReportResidual startDensity endDensity *
    noArrivalProb rate exposure

/--
Appendix B.2 one-report case residual before the Poisson-PMF rewrite:
`g(s) h_{m+1}(e) ∫_{t_{m+1}}^T h_m(t)dt`.
-/
def theorem2OneReportKernelResidual
    (startDensity endDensityAfterJump endSurvivalIntegral : ℝ) : ℝ :=
  startDensity * endDensityAfterJump * endSurvivalIntegral

/--
Appendix B.2 one-report case likelihood after collecting source kernel terms:
`A * rate * exp (-rate * exposure)`.
-/
def theorem2OneReportLikelihood
    (startDensity endDensityAfterJump endSurvivalIntegral rate exposure : ℝ) : ℝ :=
  theorem2OneReportKernelResidual
      startDensity endDensityAfterJump endSurvivalIntegral *
    rate * Real.exp (-(rate * exposure))

/--
Appendix B.2 one-report process-kernel likelihood before collecting the
interarrival density and terminal no-arrival factors.
-/
def theorem2OneReportProcessKernelLikelihood
    (startDensity endDensityAfterJump endSurvivalIntegral rate gap tail : ℝ) : ℝ :=
  theorem2OneReportKernelResidual
      startDensity endDensityAfterJump endSurvivalIntegral *
    interarrivalDensityKernel rate gap * noArrivalProb rate tail

/--
Appendix B.2 multi-report case residual before the Poisson-PMF rewrite:
`g(s) h_{m+M}(e) ∏ᵢ ∫_{t_{m+i}}^T h_{m+i-1}(t)dt`.
-/
def theorem2MultiReportKernelResidual
    (startDensity endDensityAfterLastJump survivalIntegralProduct : ℝ) : ℝ :=
  startDensity * endDensityAfterLastJump * survivalIntegralProduct

/--
Appendix B.2 multi-report case likelihood after collecting source kernel terms:
`A * rate^count * exp (-rate * exposure)`.
-/
def theorem2MultiReportLikelihood
    (startDensity endDensityAfterLastJump survivalIntegralProduct rate exposure : ℝ)
    (count : ℕ) : ℝ :=
  theorem2MultiReportKernelResidual
      startDensity endDensityAfterLastJump survivalIntegralProduct *
    rate ^ count * Real.exp (-(rate * exposure))

/--
Appendix B.2 interarrival-density kernel product with the terminal no-arrival
tail.  This is the rate-dependent Poisson-process part of Eq. (30).
-/
def theorem2InterarrivalTailLikelihood
    {Jump : Type*} (jumps : Finset Jump)
    (rate : ℝ) (gap : Jump → ℝ) (tail : ℝ) : ℝ :=
  interarrivalTailLikelihood jumps rate gap tail

/--
Appendix B.2 multi-report process-kernel likelihood before collecting the
interarrival-density product and terminal no-arrival tail.
-/
def theorem2MultiReportProcessKernelLikelihood
    {Jump : Type*} (jumps : Finset Jump)
    (startDensity endDensityAfterLastJump survivalIntegralProduct rate : ℝ)
    (gap : Jump → ℝ) (tail : ℝ) : ℝ :=
  theorem2MultiReportKernelResidual
      startDensity endDensityAfterLastJump survivalIntegralProduct *
    theorem2InterarrivalTailLikelihood jumps rate gap tail

/-- Closed-form estimator displayed as Eq. (3). -/
def mleRate (totalCount : ℕ) (totalExposure : ℝ) : ℝ :=
  (totalCount : ℝ) / totalExposure

/-- Score equation for the rate-dependent part of a Poisson likelihood product. -/
def poissonRateScore (totalCount : ℕ) (totalExposure rate : ℝ) : ℝ :=
  (totalCount : ℝ) / rate - totalExposure

/--
Rate-dependent log-likelihood kernel for Eq. (3), omitting constants
independent of the reporting rate.
-/
def poissonRateLogLikelihood
    (totalCount : ℕ) (totalExposure rate : ℝ) : ℝ :=
  poissonRateLogLikelihoodKernel totalCount totalExposure rate

/-- Total exposure over the observed incident rows used in Eq. (3). -/
def totalObservationExposure {Incident : Type*}
    (s : Finset Incident) (exposure : Incident → ℝ) : ℝ :=
  totalExposure s exposure

/-- Total observed report count over the incident rows used in Eq. (3). -/
def totalObservedReportCount {Incident : Type*}
    (s : Finset Incident) (count : Incident → ℕ) : ℕ :=
  totalCount s count

/-- Product of incident Poisson likelihood factors in Eq. (3)'s MLE derivation. -/
def observedIncidentLikelihoodProduct {Incident : Type*}
    (s : Finset Incident) (rate : ℝ)
    (exposure : Incident → ℝ) (count : Incident → ℕ) : ℝ :=
  countLikelihoodProduct s rate exposure count

/-- Rate-independent residual in the finite product likelihood. -/
def observedIncidentLikelihoodProductResidual {Incident : Type*}
    (s : Finset Incident) (exposure : Incident → ℝ) (count : Incident → ℕ) : ℝ :=
  countLikelihoodProductResidual s exposure count

/--
Rate-independent residual when the product likelihood is rewritten as one
Poisson count likelihood at total exposure and total count.
-/
def observedIncidentLikelihoodTotalPMFResidual {Incident : Type*}
    (s : Finset Incident) (exposure : Incident → ℝ) (count : Incident → ℕ) : ℝ :=
  observedIncidentLikelihoodProductResidual s exposure count *
    ((totalObservedReportCount s count).factorial : ℝ) /
      (totalObservationExposure s exposure) ^ totalObservedReportCount s count

/-- Log-link reporting-rate specification for Poisson regression. -/
def poissonRegressionRate
    {Feature : Type*} [Fintype Feature]
    (alpha : ℝ) (beta theta : Feature → ℝ) : ℝ :=
  Real.exp (alpha + ∑ j, beta j * theta j)

/-- Incident likelihood under the paper's non-zero-inflated Poisson regression. -/
def poissonRegressionIncidentLikelihood
    {Feature : Type*} [Fintype Feature]
    (alpha : ℝ) (beta theta : Feature → ℝ)
    (exposure : ℝ) (count : ℕ) : ℝ :=
  sourcePoissonPMF (poissonRegressionRate alpha beta theta) exposure count

/-- Zero-inflated incident likelihood displayed in Eq. (7). -/
def zeroInflatedIncidentLikelihood
    (gamma rate exposure : ℝ) (count : ℕ) : ℝ :=
  zeroInflatedCountLikelihood gamma rate exposure count

/--
Zero-inflated incident likelihood with the Poisson-regression log-link rate
substituted.
-/
def zeroInflatedRegressionIncidentLikelihood
    {Feature : Type*} [Fintype Feature]
    (gamma alpha : ℝ) (beta theta : Feature → ℝ)
    (exposure : ℝ) (count : ℕ) : ℝ :=
  zeroInflatedIncidentLikelihood gamma
    (poissonRegressionRate alpha beta theta) exposure count

/-! ## Closed Formula Lemmas -/

theorem sourcePoissonPMF_eq_formula
    (rate exposure : ℝ) (count : ℕ) :
    sourcePoissonPMF rate exposure count =
      Real.exp (-(rate * exposure)) * (rate * exposure) ^ count /
        (count.factorial : ℝ) := by
  rfl

theorem sourcePoissonPMF_eq_mathlib
    {rate exposure : ℝ} (h_mean : 0 ≤ rate * exposure) (count : ℕ) :
    sourcePoissonPMF rate exposure count =
      (ProbabilityTheory.poissonMeasure
        (rateExposureParam rate exposure h_mean)).real {count} := by
  exact countLikelihood_eq_poissonMeasure_real_singleton h_mean count

theorem observationExposure_nonneg
    {startTime endTime : ℝ} (hse : startTime ≤ endTime) :
    0 ≤ observationExposure startTime endTime := by
  exact sub_nonneg.mpr hse

theorem observationExposure_pos
    {startTime endTime : ℝ} (hse : startTime < endTime) :
    0 < observationExposure startTime endTime := by
  exact sub_pos.mpr hse

/-- The empirical maximum observation duration used in the NYC and Chicago rows. -/
def empiricalMaxObservationDurationDays : ℝ := 100

theorem empiricalMaxObservationDurationDays_nonneg :
    0 ≤ empiricalMaxObservationDurationDays := by
  norm_num [empiricalMaxObservationDurationDays]

theorem empiricalMaxObservationDurationDays_pos :
    0 < empiricalMaxObservationDurationDays := by
  norm_num [empiricalMaxObservationDurationDays]

/--
NYC preprocessing observation window from Eq. (33): start at the first report
and end at the earliest of 100 days after the start, inspection time, and work
order time.
-/
def nycObservationWindow
    (startTime inspectionTime workOrderTime : ℝ)
    (h_inspection : startTime ≤ inspectionTime)
    (h_workOrder : startTime ≤ workOrderTime) : ObservationWindow :=
  ObservationWindow.ofMinEnd3 startTime
    (startTime + empiricalMaxObservationDurationDays)
    inspectionTime workOrderTime
    (le_add_of_nonneg_right empiricalMaxObservationDurationDays_nonneg)
    h_inspection h_workOrder

/--
Stochastic Eq. (33) observation window: if the first report, inspection time,
and work-order time are stopping times, then the NYC preprocessing rule
`min (S + 100 days, inspection, work order)` is a stopping observation window.
-/
def nycStoppingObservationWindow
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (𝓕 : Filtration (Ω := Ω) ℝ mΩ)
    (startTime inspectionTime workOrderTime : Ω → ℝ)
    (h_start : IsStoppingTime 𝓕 startTime)
    (h_inspection_stopping : IsStoppingTime 𝓕 inspectionTime)
    (h_workOrder_stopping : IsStoppingTime 𝓕 workOrderTime)
    (h_inspection : ∀ ω, startTime ω ≤ inspectionTime ω)
    (h_workOrder : ∀ ω, startTime ω ≤ workOrderTime ω) :
    StoppingObservationWindow 𝓕 :=
  StoppingObservationWindow.ofDurationCensoredMinEnd3
    startTime inspectionTime workOrderTime
    empiricalMaxObservationDurationDays
    empiricalMaxObservationDurationDays_nonneg
    h_start h_inspection_stopping h_workOrder_stopping
    h_inspection h_workOrder

@[simp] theorem nycStoppingObservationWindow_endTime
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (𝓕 : Filtration (Ω := Ω) ℝ mΩ)
    (startTime inspectionTime workOrderTime : Ω → ℝ)
    (h_start : IsStoppingTime 𝓕 startTime)
    (h_inspection_stopping : IsStoppingTime 𝓕 inspectionTime)
    (h_workOrder_stopping : IsStoppingTime 𝓕 workOrderTime)
    (h_inspection : ∀ ω, startTime ω ≤ inspectionTime ω)
    (h_workOrder : ∀ ω, startTime ω ≤ workOrderTime ω) :
    (nycStoppingObservationWindow 𝓕 startTime inspectionTime workOrderTime
      h_start h_inspection_stopping h_workOrder_stopping
      h_inspection h_workOrder).endTime =
      fun ω =>
        min (min (startTime ω + empiricalMaxObservationDurationDays)
          (inspectionTime ω)) (workOrderTime ω) :=
  rfl

/--
Stochastic Eq. (33) observation window with deterministic inspection and
work-order endpoints. If the first report is a stopping time and the fixed
endpoints are after it pathwise, then the NYC preprocessing rule is a stopping
observation window.
-/
def nycStoppingObservationWindowOfDeterministicEndpoints
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (𝓕 : Filtration (Ω := Ω) ℝ mΩ)
    (startTime : Ω → ℝ) (inspectionTime workOrderTime : ℝ)
    (h_start : IsStoppingTime 𝓕 startTime)
    (h_inspection : ∀ ω, startTime ω ≤ inspectionTime)
    (h_workOrder : ∀ ω, startTime ω ≤ workOrderTime) :
    StoppingObservationWindow 𝓕 :=
  nycStoppingObservationWindow 𝓕 startTime
    (fun _ => inspectionTime) (fun _ => workOrderTime)
    h_start (IsStoppingTime.const inspectionTime)
    (IsStoppingTime.const workOrderTime)
    h_inspection h_workOrder

@[simp] theorem nycStoppingObservationWindowOfDeterministicEndpoints_endTime
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (𝓕 : Filtration (Ω := Ω) ℝ mΩ)
    (startTime : Ω → ℝ) (inspectionTime workOrderTime : ℝ)
    (h_start : IsStoppingTime 𝓕 startTime)
    (h_inspection : ∀ ω, startTime ω ≤ inspectionTime)
    (h_workOrder : ∀ ω, startTime ω ≤ workOrderTime) :
    (nycStoppingObservationWindowOfDeterministicEndpoints 𝓕 startTime
      inspectionTime workOrderTime h_start h_inspection h_workOrder).endTime =
      fun ω =>
        min (min (startTime ω + empiricalMaxObservationDurationDays)
          inspectionTime) workOrderTime :=
  rfl

/--
Stochastic Eq. (33) observation window where the first report is certified as
the first adapted count-arrival time and the inspection/work-order endpoints
are deterministic.
-/
def nycStoppingObservationWindowOfFirstReportCountCertificate
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (𝓕 : Filtration (Ω := Ω) ℝ mΩ)
    (reportCount : ℝ → Ω → ℕ) (startTime : Ω → ℝ)
    (inspectionTime workOrderTime : ℝ)
    (C : FirstCountArrivalCertificate 𝓕 reportCount startTime)
    (h_inspection : ∀ ω, startTime ω ≤ inspectionTime)
    (h_workOrder : ∀ ω, startTime ω ≤ workOrderTime) :
    StoppingObservationWindow 𝓕 :=
  nycStoppingObservationWindowOfDeterministicEndpoints 𝓕 startTime
    inspectionTime workOrderTime C.isStoppingTime
    h_inspection h_workOrder

@[simp] theorem nycStoppingObservationWindowOfFirstReportCountCertificate_endTime
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (𝓕 : Filtration (Ω := Ω) ℝ mΩ)
    (reportCount : ℝ → Ω → ℕ) (startTime : Ω → ℝ)
    (inspectionTime workOrderTime : ℝ)
    (C : FirstCountArrivalCertificate 𝓕 reportCount startTime)
    (h_inspection : ∀ ω, startTime ω ≤ inspectionTime)
    (h_workOrder : ∀ ω, startTime ω ≤ workOrderTime) :
    (nycStoppingObservationWindowOfFirstReportCountCertificate 𝓕
      reportCount startTime inspectionTime workOrderTime C
      h_inspection h_workOrder).endTime =
      fun ω =>
        min (min (startTime ω + empiricalMaxObservationDurationDays)
          inspectionTime) workOrderTime :=
  rfl

/--
Stochastic Eq. (33) observation window from the local finite-observation
certificate boundary.  The inputs are exactly count-coordinate observability,
first-count level sets, endpoint stopping-time facts, and pathwise endpoint
ordering; the first-report stopping-time theorem and min-censored window are
then supplied by the reusable Poisson library.
-/
def nycStoppingObservationWindowOfLocalCountProcess
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
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
    StoppingObservationWindow 𝓕 :=
  let C :=
    DurationCensoredFirstCountObservationCertificate.ofStoppingEndpoints
      (𝓕 := 𝓕) reportCount startTime inspectionTime workOrderTime
      empiricalMaxObservationDurationDays
      empiricalMaxObservationDurationDays_nonneg h_count_measurable
      h_first_level_sets h_inspection_stopping h_workOrder_stopping
      h_inspection h_workOrder
  C.stoppingObservationWindow

@[simp] theorem nycStoppingObservationWindowOfLocalCountProcess_endTime
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
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
    (nycStoppingObservationWindowOfLocalCountProcess 𝓕 reportCount startTime
      inspectionTime workOrderTime h_count_measurable h_first_level_sets
      h_inspection_stopping h_workOrder_stopping h_inspection h_workOrder).endTime =
      fun ω =>
        min (min (startTime ω + empiricalMaxObservationDurationDays)
          (inspectionTime ω)) (workOrderTime ω) :=
  rfl

/--
Filtered homogeneous-Poisson version of the stochastic NYC window.  Relative
to the local count-process route, adaptedness and stationary Poisson increment
laws are packaged in `H`; the remaining path-space premise is the first-report
sublevel identity.  This does not infer a random-window Poisson law.
-/
def nycStoppingObservationWindowOfFilteredHomogeneousPoisson
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : FilteredHomogeneousPoissonCountingProcessByLaw Ω P)
    (startTime inspectionTime workOrderTime : Ω → ℝ)
    (h_first_level_sets :
      ∀ t : ℝ, {ω | startTime ω ≤ t} = {ω | 1 ≤ H.process.count t ω})
    (h_inspection_stopping : IsStoppingTime H.filtration inspectionTime)
    (h_workOrder_stopping : IsStoppingTime H.filtration workOrderTime)
    (h_inspection : ∀ ω, startTime ω ≤ inspectionTime ω)
    (h_workOrder : ∀ ω, startTime ω ≤ workOrderTime ω) :
    StoppingObservationWindow H.filtration :=
  (DurationCensoredFirstCountObservationCertificate.ofFilteredHomogeneousPoisson
    H startTime inspectionTime workOrderTime empiricalMaxObservationDurationDays
    empiricalMaxObservationDurationDays_nonneg h_first_level_sets
    h_inspection_stopping h_workOrder_stopping h_inspection h_workOrder).stoppingObservationWindow

/-- The filtered-Poisson NYC first-report time is a native Mathlib stopping time. -/
theorem nycFirstReport_nativeStoppingOfFilteredHomogeneousPoisson
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : FilteredHomogeneousPoissonCountingProcessByLaw Ω P)
    (startTime : Ω → ℝ)
    (h_first_level_sets :
      ∀ t : ℝ, {ω | startTime ω ≤ t} = {ω | 1 ≤ H.process.count t ω}) :
    MeasureTheory.IsStoppingTime H.filtration (toNativeStoppingTime startTime) :=
  (H.firstCountArrivalCertificate startTime h_first_level_sets).isStoppingTime_native

@[simp] theorem nycObservationWindow_startTime
    (startTime inspectionTime workOrderTime : ℝ)
    (h_inspection : startTime ≤ inspectionTime)
    (h_workOrder : startTime ≤ workOrderTime) :
    (nycObservationWindow startTime inspectionTime workOrderTime
      h_inspection h_workOrder).startTime = startTime := rfl

@[simp] theorem nycObservationWindow_endTime
    (startTime inspectionTime workOrderTime : ℝ)
    (h_inspection : startTime ≤ inspectionTime)
    (h_workOrder : startTime ≤ workOrderTime) :
    (nycObservationWindow startTime inspectionTime workOrderTime
      h_inspection h_workOrder).endTime =
      min (min (startTime + empiricalMaxObservationDurationDays)
        inspectionTime) workOrderTime := rfl

theorem nycObservationWindow_endTime_le_duration_cap
    (startTime inspectionTime workOrderTime : ℝ)
    (h_inspection : startTime ≤ inspectionTime)
    (h_workOrder : startTime ≤ workOrderTime) :
    (nycObservationWindow startTime inspectionTime workOrderTime
      h_inspection h_workOrder).endTime ≤
      startTime + empiricalMaxObservationDurationDays := by
  exact ObservationWindow.ofMinEnd3_endTime_le_first
    startTime (startTime + empiricalMaxObservationDurationDays)
    inspectionTime workOrderTime
    (le_add_of_nonneg_right empiricalMaxObservationDurationDays_nonneg)
    h_inspection h_workOrder

theorem nycObservationWindow_endTime_le_inspection
    (startTime inspectionTime workOrderTime : ℝ)
    (h_inspection : startTime ≤ inspectionTime)
    (h_workOrder : startTime ≤ workOrderTime) :
    (nycObservationWindow startTime inspectionTime workOrderTime
      h_inspection h_workOrder).endTime ≤ inspectionTime := by
  exact ObservationWindow.ofMinEnd3_endTime_le_second
    startTime (startTime + empiricalMaxObservationDurationDays)
    inspectionTime workOrderTime
    (le_add_of_nonneg_right empiricalMaxObservationDurationDays_nonneg)
    h_inspection h_workOrder

theorem nycObservationWindow_endTime_le_workOrder
    (startTime inspectionTime workOrderTime : ℝ)
    (h_inspection : startTime ≤ inspectionTime)
    (h_workOrder : startTime ≤ workOrderTime) :
    (nycObservationWindow startTime inspectionTime workOrderTime
      h_inspection h_workOrder).endTime ≤ workOrderTime := by
  exact ObservationWindow.ofMinEnd3_endTime_le_third
    startTime (startTime + empiricalMaxObservationDurationDays)
    inspectionTime workOrderTime
    (le_add_of_nonneg_right empiricalMaxObservationDurationDays_nonneg)
    h_inspection h_workOrder

theorem nycObservationWindow_exposure_le_duration_cap
    (startTime inspectionTime workOrderTime : ℝ)
    (h_inspection : startTime ≤ inspectionTime)
    (h_workOrder : startTime ≤ workOrderTime) :
    (nycObservationWindow startTime inspectionTime workOrderTime
      h_inspection h_workOrder).exposure ≤
      empiricalMaxObservationDurationDays := by
  exact ObservationWindow.ofMinEnd3_exposure_le_duration_cap
    startTime empiricalMaxObservationDurationDays
    inspectionTime workOrderTime
    empiricalMaxObservationDurationDays_nonneg h_inspection h_workOrder

theorem nycObservationWindow_start_lt_end
    (startTime inspectionTime workOrderTime : ℝ)
    (h_inspection : startTime < inspectionTime)
    (h_workOrder : startTime < workOrderTime) :
    startTime <
      (nycObservationWindow startTime inspectionTime workOrderTime
        (le_of_lt h_inspection) (le_of_lt h_workOrder)).endTime := by
  exact ObservationWindow.ofMinEnd3_start_lt_end
    startTime (startTime + empiricalMaxObservationDurationDays)
    inspectionTime workOrderTime
    (lt_add_of_pos_right startTime empiricalMaxObservationDurationDays_pos)
    h_inspection h_workOrder

theorem nycObservationWindow_exposure_pos
    (startTime inspectionTime workOrderTime : ℝ)
    (h_inspection : startTime < inspectionTime)
    (h_workOrder : startTime < workOrderTime) :
    0 <
      (nycObservationWindow startTime inspectionTime workOrderTime
        (le_of_lt h_inspection) (le_of_lt h_workOrder)).exposure := by
  exact ObservationWindow.ofMinEnd3_exposure_pos
    startTime (startTime + empiricalMaxObservationDurationDays)
    inspectionTime workOrderTime
    (lt_add_of_pos_right startTime empiricalMaxObservationDurationDays_pos)
    h_inspection h_workOrder

/-- Exposure of the NYC Eq. (33) preprocessing observation window. -/
def nycObservationExposure
    (startTime inspectionTime workOrderTime : ℝ)
    (h_inspection : startTime ≤ inspectionTime)
    (h_workOrder : startTime ≤ workOrderTime) : ℝ :=
  (nycObservationWindow startTime inspectionTime workOrderTime
    h_inspection h_workOrder).exposure

theorem nycObservationExposure_nonneg
    (startTime inspectionTime workOrderTime : ℝ)
    (h_inspection : startTime ≤ inspectionTime)
    (h_workOrder : startTime ≤ workOrderTime) :
    0 ≤ nycObservationExposure startTime inspectionTime workOrderTime
      h_inspection h_workOrder :=
  (nycObservationWindow startTime inspectionTime workOrderTime
    h_inspection h_workOrder).exposure_nonneg

theorem nycObservationExposure_pos
    (startTime inspectionTime workOrderTime : ℝ)
    (h_inspection : startTime < inspectionTime)
    (h_workOrder : startTime < workOrderTime) :
    0 < nycObservationExposure startTime inspectionTime workOrderTime
      (le_of_lt h_inspection) (le_of_lt h_workOrder) :=
  nycObservationWindow_exposure_pos
    startTime inspectionTime workOrderTime h_inspection h_workOrder

theorem nycObservationWindow_endTime_le_lifetime_of_inspection_le
    (startTime inspectionTime workOrderTime lifetimeEnd : ℝ)
    (h_inspection : startTime ≤ inspectionTime)
    (h_workOrder : startTime ≤ workOrderTime)
    (h_inspection_lifetime : inspectionTime ≤ lifetimeEnd) :
    (nycObservationWindow startTime inspectionTime workOrderTime
      h_inspection h_workOrder).endTime ≤ lifetimeEnd :=
  le_trans
    (nycObservationWindow_endTime_le_inspection
      startTime inspectionTime workOrderTime h_inspection h_workOrder)
    h_inspection_lifetime

theorem nycObservationWindow_endTime_le_lifetime_of_workOrder_le
    (startTime inspectionTime workOrderTime lifetimeEnd : ℝ)
    (h_inspection : startTime ≤ inspectionTime)
    (h_workOrder : startTime ≤ workOrderTime)
    (h_workOrder_lifetime : workOrderTime ≤ lifetimeEnd) :
    (nycObservationWindow startTime inspectionTime workOrderTime
      h_inspection h_workOrder).endTime ≤ lifetimeEnd :=
  le_trans
    (nycObservationWindow_endTime_le_workOrder
      startTime inspectionTime workOrderTime h_inspection h_workOrder)
    h_workOrder_lifetime

/--
Chicago preprocessing observation window from Eq. (34): start at the first
report and end at the earliest of 100 days after the start, closed time, and
the dataset retrieval/update time.
-/
def chicagoObservationWindow
    (firstReportTime closedTime retrievalTime : ℝ)
    (h_closed : firstReportTime ≤ closedTime)
    (h_retrieval : firstReportTime ≤ retrievalTime) : ObservationWindow :=
  ObservationWindow.ofMinEnd3 firstReportTime
    (firstReportTime + empiricalMaxObservationDurationDays)
    closedTime retrievalTime
    (le_add_of_nonneg_right empiricalMaxObservationDurationDays_nonneg)
    h_closed h_retrieval

/--
Stochastic Eq. (34) observation window: if the first report, closure time, and
retrieval/update time are stopping times, then the Chicago preprocessing rule
`min (S + 100 days, closed, retrieval/update)` is a stopping observation
window.
-/
def chicagoStoppingObservationWindow
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (𝓕 : Filtration (Ω := Ω) ℝ mΩ)
    (firstReportTime closedTime retrievalTime : Ω → ℝ)
    (h_firstReport : IsStoppingTime 𝓕 firstReportTime)
    (h_closed_stopping : IsStoppingTime 𝓕 closedTime)
    (h_retrieval_stopping : IsStoppingTime 𝓕 retrievalTime)
    (h_closed : ∀ ω, firstReportTime ω ≤ closedTime ω)
    (h_retrieval : ∀ ω, firstReportTime ω ≤ retrievalTime ω) :
    StoppingObservationWindow 𝓕 :=
  StoppingObservationWindow.ofDurationCensoredMinEnd3
    firstReportTime closedTime retrievalTime
    empiricalMaxObservationDurationDays
    empiricalMaxObservationDurationDays_nonneg
    h_firstReport h_closed_stopping h_retrieval_stopping
    h_closed h_retrieval

@[simp] theorem chicagoStoppingObservationWindow_endTime
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (𝓕 : Filtration (Ω := Ω) ℝ mΩ)
    (firstReportTime closedTime retrievalTime : Ω → ℝ)
    (h_firstReport : IsStoppingTime 𝓕 firstReportTime)
    (h_closed_stopping : IsStoppingTime 𝓕 closedTime)
    (h_retrieval_stopping : IsStoppingTime 𝓕 retrievalTime)
    (h_closed : ∀ ω, firstReportTime ω ≤ closedTime ω)
    (h_retrieval : ∀ ω, firstReportTime ω ≤ retrievalTime ω) :
    (chicagoStoppingObservationWindow 𝓕 firstReportTime closedTime retrievalTime
      h_firstReport h_closed_stopping h_retrieval_stopping
      h_closed h_retrieval).endTime =
      fun ω =>
        min (min (firstReportTime ω + empiricalMaxObservationDurationDays)
          (closedTime ω)) (retrievalTime ω) :=
  rfl

/--
Stochastic Eq. (34) observation window with deterministic closure and
retrieval/update endpoints. If the first report is a stopping time and the
fixed endpoints are after it pathwise, then the Chicago preprocessing rule is
a stopping observation window.
-/
def chicagoStoppingObservationWindowOfDeterministicEndpoints
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (𝓕 : Filtration (Ω := Ω) ℝ mΩ)
    (firstReportTime : Ω → ℝ) (closedTime retrievalTime : ℝ)
    (h_firstReport : IsStoppingTime 𝓕 firstReportTime)
    (h_closed : ∀ ω, firstReportTime ω ≤ closedTime)
    (h_retrieval : ∀ ω, firstReportTime ω ≤ retrievalTime) :
    StoppingObservationWindow 𝓕 :=
  chicagoStoppingObservationWindow 𝓕 firstReportTime
    (fun _ => closedTime) (fun _ => retrievalTime)
    h_firstReport (IsStoppingTime.const closedTime)
    (IsStoppingTime.const retrievalTime)
    h_closed h_retrieval

@[simp] theorem chicagoStoppingObservationWindowOfDeterministicEndpoints_endTime
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (𝓕 : Filtration (Ω := Ω) ℝ mΩ)
    (firstReportTime : Ω → ℝ) (closedTime retrievalTime : ℝ)
    (h_firstReport : IsStoppingTime 𝓕 firstReportTime)
    (h_closed : ∀ ω, firstReportTime ω ≤ closedTime)
    (h_retrieval : ∀ ω, firstReportTime ω ≤ retrievalTime) :
    (chicagoStoppingObservationWindowOfDeterministicEndpoints 𝓕 firstReportTime
      closedTime retrievalTime h_firstReport h_closed h_retrieval).endTime =
      fun ω =>
        min (min (firstReportTime ω + empiricalMaxObservationDurationDays)
          closedTime) retrievalTime :=
  rfl

/--
Stochastic Eq. (34) observation window where the first report is certified as
the first adapted count-arrival time and the closure/retrieval endpoints are
deterministic.
-/
def chicagoStoppingObservationWindowOfFirstReportCountCertificate
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (𝓕 : Filtration (Ω := Ω) ℝ mΩ)
    (reportCount : ℝ → Ω → ℕ) (firstReportTime : Ω → ℝ)
    (closedTime retrievalTime : ℝ)
    (C : FirstCountArrivalCertificate 𝓕 reportCount firstReportTime)
    (h_closed : ∀ ω, firstReportTime ω ≤ closedTime)
    (h_retrieval : ∀ ω, firstReportTime ω ≤ retrievalTime) :
    StoppingObservationWindow 𝓕 :=
  chicagoStoppingObservationWindowOfDeterministicEndpoints 𝓕 firstReportTime
    closedTime retrievalTime C.isStoppingTime
    h_closed h_retrieval

@[simp] theorem chicagoStoppingObservationWindowOfFirstReportCountCertificate_endTime
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (𝓕 : Filtration (Ω := Ω) ℝ mΩ)
    (reportCount : ℝ → Ω → ℕ) (firstReportTime : Ω → ℝ)
    (closedTime retrievalTime : ℝ)
    (C : FirstCountArrivalCertificate 𝓕 reportCount firstReportTime)
    (h_closed : ∀ ω, firstReportTime ω ≤ closedTime)
    (h_retrieval : ∀ ω, firstReportTime ω ≤ retrievalTime) :
    (chicagoStoppingObservationWindowOfFirstReportCountCertificate 𝓕
      reportCount firstReportTime closedTime retrievalTime C
      h_closed h_retrieval).endTime =
      fun ω =>
        min (min (firstReportTime ω + empiricalMaxObservationDurationDays)
          closedTime) retrievalTime :=
  rfl

/--
Stochastic Eq. (34) observation window from the local finite-observation
certificate boundary.  The inputs are exactly count-coordinate observability,
first-count level sets, endpoint stopping-time facts, and pathwise endpoint
ordering; the first-report stopping-time theorem and min-censored window are
then supplied by the reusable Poisson library.
-/
def chicagoStoppingObservationWindowOfLocalCountProcess
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
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
    StoppingObservationWindow 𝓕 :=
  let C :=
    DurationCensoredFirstCountObservationCertificate.ofStoppingEndpoints
      (𝓕 := 𝓕) reportCount firstReportTime closedTime retrievalTime
      empiricalMaxObservationDurationDays
      empiricalMaxObservationDurationDays_nonneg h_count_measurable
      h_first_level_sets h_closed_stopping h_retrieval_stopping
      h_closed h_retrieval
  C.stoppingObservationWindow

@[simp] theorem chicagoStoppingObservationWindowOfLocalCountProcess_endTime
    {Ω : Type*} {mΩ : MeasurableSpace Ω}
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
    (chicagoStoppingObservationWindowOfLocalCountProcess 𝓕 reportCount
      firstReportTime closedTime retrievalTime h_count_measurable
      h_first_level_sets h_closed_stopping h_retrieval_stopping h_closed
      h_retrieval).endTime =
      fun ω =>
        min (min (firstReportTime ω + empiricalMaxObservationDurationDays)
          (closedTime ω)) (retrievalTime ω) :=
  rfl

/--
Filtered homogeneous-Poisson version of the stochastic Chicago window.  It
packages adapted count coordinates in `H` and leaves the genuine path-space
first-report identity explicit.
-/
def chicagoStoppingObservationWindowOfFilteredHomogeneousPoisson
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : FilteredHomogeneousPoissonCountingProcessByLaw Ω P)
    (firstReportTime closedTime retrievalTime : Ω → ℝ)
    (h_first_level_sets :
      ∀ t : ℝ, {ω | firstReportTime ω ≤ t} =
        {ω | 1 ≤ H.process.count t ω})
    (h_closed_stopping : IsStoppingTime H.filtration closedTime)
    (h_retrieval_stopping : IsStoppingTime H.filtration retrievalTime)
    (h_closed : ∀ ω, firstReportTime ω ≤ closedTime ω)
    (h_retrieval : ∀ ω, firstReportTime ω ≤ retrievalTime ω) :
    StoppingObservationWindow H.filtration :=
  (DurationCensoredFirstCountObservationCertificate.ofFilteredHomogeneousPoisson
    H firstReportTime closedTime retrievalTime empiricalMaxObservationDurationDays
    empiricalMaxObservationDurationDays_nonneg h_first_level_sets
    h_closed_stopping h_retrieval_stopping h_closed h_retrieval).stoppingObservationWindow

/-- The filtered-Poisson Chicago first-report time is a native Mathlib stopping time. -/
theorem chicagoFirstReport_nativeStoppingOfFilteredHomogeneousPoisson
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : FilteredHomogeneousPoissonCountingProcessByLaw Ω P)
    (firstReportTime : Ω → ℝ)
    (h_first_level_sets :
      ∀ t : ℝ, {ω | firstReportTime ω ≤ t} =
        {ω | 1 ≤ H.process.count t ω}) :
    MeasureTheory.IsStoppingTime H.filtration
      (toNativeStoppingTime firstReportTime) :=
  (H.firstCountArrivalCertificate firstReportTime h_first_level_sets).isStoppingTime_native

@[simp] theorem chicagoObservationWindow_startTime
    (firstReportTime closedTime retrievalTime : ℝ)
    (h_closed : firstReportTime ≤ closedTime)
    (h_retrieval : firstReportTime ≤ retrievalTime) :
    (chicagoObservationWindow firstReportTime closedTime retrievalTime
      h_closed h_retrieval).startTime = firstReportTime := rfl

@[simp] theorem chicagoObservationWindow_endTime
    (firstReportTime closedTime retrievalTime : ℝ)
    (h_closed : firstReportTime ≤ closedTime)
    (h_retrieval : firstReportTime ≤ retrievalTime) :
    (chicagoObservationWindow firstReportTime closedTime retrievalTime
      h_closed h_retrieval).endTime =
      min (min (firstReportTime + empiricalMaxObservationDurationDays)
        closedTime) retrievalTime := rfl

theorem chicagoObservationWindow_endTime_le_duration_cap
    (firstReportTime closedTime retrievalTime : ℝ)
    (h_closed : firstReportTime ≤ closedTime)
    (h_retrieval : firstReportTime ≤ retrievalTime) :
    (chicagoObservationWindow firstReportTime closedTime retrievalTime
      h_closed h_retrieval).endTime ≤
      firstReportTime + empiricalMaxObservationDurationDays := by
  exact ObservationWindow.ofMinEnd3_endTime_le_first
    firstReportTime (firstReportTime + empiricalMaxObservationDurationDays)
    closedTime retrievalTime
    (le_add_of_nonneg_right empiricalMaxObservationDurationDays_nonneg)
    h_closed h_retrieval

theorem chicagoObservationWindow_endTime_le_closed
    (firstReportTime closedTime retrievalTime : ℝ)
    (h_closed : firstReportTime ≤ closedTime)
    (h_retrieval : firstReportTime ≤ retrievalTime) :
    (chicagoObservationWindow firstReportTime closedTime retrievalTime
      h_closed h_retrieval).endTime ≤ closedTime := by
  exact ObservationWindow.ofMinEnd3_endTime_le_second
    firstReportTime (firstReportTime + empiricalMaxObservationDurationDays)
    closedTime retrievalTime
    (le_add_of_nonneg_right empiricalMaxObservationDurationDays_nonneg)
    h_closed h_retrieval

theorem chicagoObservationWindow_endTime_le_retrieval
    (firstReportTime closedTime retrievalTime : ℝ)
    (h_closed : firstReportTime ≤ closedTime)
    (h_retrieval : firstReportTime ≤ retrievalTime) :
    (chicagoObservationWindow firstReportTime closedTime retrievalTime
      h_closed h_retrieval).endTime ≤ retrievalTime := by
  exact ObservationWindow.ofMinEnd3_endTime_le_third
    firstReportTime (firstReportTime + empiricalMaxObservationDurationDays)
    closedTime retrievalTime
    (le_add_of_nonneg_right empiricalMaxObservationDurationDays_nonneg)
    h_closed h_retrieval

theorem chicagoObservationWindow_exposure_le_duration_cap
    (firstReportTime closedTime retrievalTime : ℝ)
    (h_closed : firstReportTime ≤ closedTime)
    (h_retrieval : firstReportTime ≤ retrievalTime) :
    (chicagoObservationWindow firstReportTime closedTime retrievalTime
      h_closed h_retrieval).exposure ≤
      empiricalMaxObservationDurationDays := by
  exact ObservationWindow.ofMinEnd3_exposure_le_duration_cap
    firstReportTime empiricalMaxObservationDurationDays
    closedTime retrievalTime
    empiricalMaxObservationDurationDays_nonneg h_closed h_retrieval

theorem chicagoObservationWindow_start_lt_end
    (firstReportTime closedTime retrievalTime : ℝ)
    (h_closed : firstReportTime < closedTime)
    (h_retrieval : firstReportTime < retrievalTime) :
    firstReportTime <
      (chicagoObservationWindow firstReportTime closedTime retrievalTime
        (le_of_lt h_closed) (le_of_lt h_retrieval)).endTime := by
  exact ObservationWindow.ofMinEnd3_start_lt_end
    firstReportTime
    (firstReportTime + empiricalMaxObservationDurationDays)
    closedTime retrievalTime
    (lt_add_of_pos_right firstReportTime
      empiricalMaxObservationDurationDays_pos)
    h_closed h_retrieval

theorem chicagoObservationWindow_exposure_pos
    (firstReportTime closedTime retrievalTime : ℝ)
    (h_closed : firstReportTime < closedTime)
    (h_retrieval : firstReportTime < retrievalTime) :
    0 <
      (chicagoObservationWindow firstReportTime closedTime retrievalTime
        (le_of_lt h_closed) (le_of_lt h_retrieval)).exposure := by
  exact ObservationWindow.ofMinEnd3_exposure_pos
    firstReportTime
    (firstReportTime + empiricalMaxObservationDurationDays)
    closedTime retrievalTime
    (lt_add_of_pos_right firstReportTime
      empiricalMaxObservationDurationDays_pos)
    h_closed h_retrieval

/-- Exposure of the Chicago Eq. (34) preprocessing observation window. -/
def chicagoObservationExposure
    (firstReportTime closedTime retrievalTime : ℝ)
    (h_closed : firstReportTime ≤ closedTime)
    (h_retrieval : firstReportTime ≤ retrievalTime) : ℝ :=
  (chicagoObservationWindow firstReportTime closedTime retrievalTime
    h_closed h_retrieval).exposure

theorem chicagoObservationExposure_nonneg
    (firstReportTime closedTime retrievalTime : ℝ)
    (h_closed : firstReportTime ≤ closedTime)
    (h_retrieval : firstReportTime ≤ retrievalTime) :
    0 ≤ chicagoObservationExposure firstReportTime closedTime retrievalTime
      h_closed h_retrieval :=
  (chicagoObservationWindow firstReportTime closedTime retrievalTime
    h_closed h_retrieval).exposure_nonneg

theorem chicagoObservationExposure_pos
    (firstReportTime closedTime retrievalTime : ℝ)
    (h_closed : firstReportTime < closedTime)
    (h_retrieval : firstReportTime < retrievalTime) :
    0 < chicagoObservationExposure firstReportTime closedTime retrievalTime
      (le_of_lt h_closed) (le_of_lt h_retrieval) :=
  chicagoObservationWindow_exposure_pos
    firstReportTime closedTime retrievalTime h_closed h_retrieval

theorem chicagoObservationWindow_endTime_le_lifetime_of_closed_le
    (firstReportTime closedTime retrievalTime lifetimeEnd : ℝ)
    (h_closed : firstReportTime ≤ closedTime)
    (h_retrieval : firstReportTime ≤ retrievalTime)
    (h_closed_lifetime : closedTime ≤ lifetimeEnd) :
    (chicagoObservationWindow firstReportTime closedTime retrievalTime
      h_closed h_retrieval).endTime ≤ lifetimeEnd :=
  le_trans
    (chicagoObservationWindow_endTime_le_closed
      firstReportTime closedTime retrievalTime h_closed h_retrieval)
    h_closed_lifetime

theorem firstReportProbability_eq_one_sub_noReport
    (reportingRate duration : ℝ) :
    firstReportProbability reportingRate duration =
      1 - Real.exp (-(reportingRate * duration)) := by
  rfl

theorem firstReportProbability_eq_of_rate_duration_product_eq
    {rate₁ duration₁ rate₂ duration₂ : ℝ}
    (hprod : rate₁ * duration₁ = rate₂ * duration₂) :
    firstReportProbability rate₁ duration₁ =
      firstReportProbability rate₂ duration₂ := by
  simp [firstReportProbability, atLeastOneArrivalProb, noArrivalProb, hprod]

theorem finiteDurationFirstReportProbability_eq_formula
    {DurationType : Type*} [Fintype DurationType]
    (reportingRate : ℝ) (weight duration : DurationType → ℝ) :
    finiteDurationFirstReportProbability reportingRate weight duration =
      1 - ∑ d, weight d * Real.exp (-(reportingRate * duration d)) := by
  simp [finiteDurationFirstReportProbability,
    finiteDurationNoReportProbability, noArrivalProb]

theorem finiteDurationFirstReportProbability_punit
    (reportingRate duration : ℝ) :
    finiteDurationFirstReportProbability
        (DurationType := PUnit) reportingRate
        (fun _ => 1) (fun _ => duration) =
      firstReportProbability reportingRate duration := by
  simp [finiteDurationFirstReportProbability,
    finiteDurationNoReportProbability, firstReportProbability,
    atLeastOneArrivalProb, noArrivalProb]

/--
Finite-duration detection probability as a weighted average of per-duration
first-report probabilities.  This is the finite-mixture algebra in Lemma 1 once
the duration weights are normalized.
-/
theorem finiteDurationFirstReportProbability_eq_weighted_firstReportProbability
    {DurationType : Type*} [Fintype DurationType]
    (reportingRate : ℝ) (weight duration : DurationType → ℝ)
    (hsum_weight : (∑ d, weight d) = 1) :
    finiteDurationFirstReportProbability reportingRate weight duration =
      ∑ d, weight d * firstReportProbability reportingRate (duration d) := by
  classical
  calc
    finiteDurationFirstReportProbability reportingRate weight duration
        = (∑ d, weight d) -
            ∑ d, weight d * noArrivalProb reportingRate (duration d) := by
          simp [finiteDurationFirstReportProbability,
            finiteDurationNoReportProbability, hsum_weight]
    _ = ∑ d,
          (weight d -
            weight d * noArrivalProb reportingRate (duration d)) := by
          rw [Finset.sum_sub_distrib]
    _ = ∑ d, weight d * firstReportProbability reportingRate (duration d) := by
          refine Finset.sum_congr rfl ?_
          intro d _hd
          simp [firstReportProbability, atLeastOneArrivalProb]
          ring

/--
Continuous-duration homogeneous Lemma 1 formula: if `durationDensity` is
normalized over nonnegative durations, then the source expression
`1 - ∫ exp(-λt) f(t) dt` is the integral of the per-duration first-report
probability.
-/
theorem continuousDurationFirstReportProbability_eq_integral_firstReportProbability
    (reportingRate : ℝ) (durationDensity : ℝ → ℝ)
    (h_density_mass :
      (∫ t, durationDensity t
        ∂(volume.restrict (Set.Ici (0 : ℝ)))) = 1)
    (h_density_integrable :
      Integrable durationDensity (volume.restrict (Set.Ici (0 : ℝ))))
    (h_noReport_integrable :
      Integrable
        (fun t => durationDensity t * noArrivalProb reportingRate t)
        (volume.restrict (Set.Ici (0 : ℝ)))) :
    continuousDurationFirstReportProbability
        reportingRate durationDensity =
      ∫ t, durationDensity t * firstReportProbability reportingRate t
        ∂(volume.restrict (Set.Ici (0 : ℝ))) := by
  let μ : Measure ℝ := volume.restrict (Set.Ici (0 : ℝ))
  calc
    continuousDurationFirstReportProbability
        reportingRate durationDensity
        = (∫ t, durationDensity t ∂μ) -
            ∫ t, durationDensity t * noArrivalProb reportingRate t ∂μ := by
          simp [continuousDurationFirstReportProbability,
            continuousDurationNoReportProbability, μ, h_density_mass]
    _ = ∫ t,
          (durationDensity t -
            durationDensity t * noArrivalProb reportingRate t) ∂μ := by
          rw [MeasureTheory.integral_sub h_density_integrable
            h_noReport_integrable]
    _ = ∫ t, durationDensity t * firstReportProbability reportingRate t ∂μ := by
          congr 1
          ext t
          simp [firstReportProbability, atLeastOneArrivalProb]
          ring

/--
Continuous-duration observed-rate version of Lemma 1 in the homogeneous case:
the observed unique-incident rate is the occurrence rate times the average
per-duration first-report probability.
-/
theorem continuousDurationObservedIncidentRate_eq_integral_firstReportProbability
    (incidentRate reportingRate : ℝ) (durationDensity : ℝ → ℝ)
    (h_density_mass :
      (∫ t, durationDensity t
        ∂(volume.restrict (Set.Ici (0 : ℝ)))) = 1)
    (h_density_integrable :
      Integrable durationDensity (volume.restrict (Set.Ici (0 : ℝ))))
    (h_noReport_integrable :
      Integrable
        (fun t => durationDensity t * noArrivalProb reportingRate t)
        (volume.restrict (Set.Ici (0 : ℝ)))) :
    continuousDurationObservedIncidentRate
        incidentRate reportingRate durationDensity =
      incidentRate *
        ∫ t, durationDensity t * firstReportProbability reportingRate t
          ∂(volume.restrict (Set.Ici (0 : ℝ))) := by
  simp [continuousDurationObservedIncidentRate,
    continuousDurationFirstReportProbability_eq_integral_firstReportProbability
      reportingRate durationDensity h_density_mass h_density_integrable
      h_noReport_integrable]

/--
Continuous-duration nonhomogeneous Lemma 1 formula: if `durationDensity` is
normalized over nonnegative durations, then
`1 - ∫ exp(-∫₀ᵗ λ(u)du) f(t) dt` is the integral of the per-duration
first-report probability induced by the cumulative intensity.
-/
theorem continuousDurationFirstReportProbabilityOfCumulativeIntensity_eq_integral
    (cumulativeIntensity durationDensity : ℝ → ℝ)
    (h_density_mass :
      (∫ t, durationDensity t
        ∂(volume.restrict (Set.Ici (0 : ℝ)))) = 1)
    (h_density_integrable :
      Integrable durationDensity (volume.restrict (Set.Ici (0 : ℝ))))
    (h_noReport_integrable :
      Integrable
        (fun t => durationDensity t * Real.exp (-(cumulativeIntensity t)))
        (volume.restrict (Set.Ici (0 : ℝ)))) :
    continuousDurationFirstReportProbabilityOfCumulativeIntensity
        cumulativeIntensity durationDensity =
      ∫ t,
        durationDensity t *
          cumulativeIntensityFirstReportProbability cumulativeIntensity t
        ∂(volume.restrict (Set.Ici (0 : ℝ))) := by
  let μ : Measure ℝ := volume.restrict (Set.Ici (0 : ℝ))
  calc
    continuousDurationFirstReportProbabilityOfCumulativeIntensity
        cumulativeIntensity durationDensity
        = (∫ t, durationDensity t ∂μ) -
            ∫ t, durationDensity t *
              Real.exp (-(cumulativeIntensity t)) ∂μ := by
          simp [continuousDurationFirstReportProbabilityOfCumulativeIntensity,
            continuousDurationNoReportProbabilityOfCumulativeIntensity,
            μ, h_density_mass]
    _ = ∫ t,
          (durationDensity t -
            durationDensity t * Real.exp (-(cumulativeIntensity t))) ∂μ := by
          rw [MeasureTheory.integral_sub h_density_integrable
            h_noReport_integrable]
    _ = ∫ t,
          durationDensity t *
            cumulativeIntensityFirstReportProbability cumulativeIntensity t
          ∂μ := by
          congr 1
          ext t
          simp [cumulativeIntensityFirstReportProbability]
          ring

/--
Continuous-duration observed-rate version of Lemma 1 for a nonhomogeneous
cumulative reporting intensity.
-/
theorem continuousDurationObservedIncidentRateOfCumulativeIntensity_eq_integral
    (incidentRate : ℝ) (cumulativeIntensity durationDensity : ℝ → ℝ)
    (h_density_mass :
      (∫ t, durationDensity t
        ∂(volume.restrict (Set.Ici (0 : ℝ)))) = 1)
    (h_density_integrable :
      Integrable durationDensity (volume.restrict (Set.Ici (0 : ℝ))))
    (h_noReport_integrable :
      Integrable
        (fun t => durationDensity t * Real.exp (-(cumulativeIntensity t)))
        (volume.restrict (Set.Ici (0 : ℝ)))) :
    continuousDurationObservedIncidentRateOfCumulativeIntensity
        incidentRate cumulativeIntensity durationDensity =
      incidentRate *
        ∫ t,
          durationDensity t *
            cumulativeIntensityFirstReportProbability cumulativeIntensity t
          ∂(volume.restrict (Set.Ici (0 : ℝ))) := by
  simp [continuousDurationObservedIncidentRateOfCumulativeIntensity,
    continuousDurationFirstReportProbabilityOfCumulativeIntensity_eq_integral
      cumulativeIntensity durationDensity h_density_mass h_density_integrable
      h_noReport_integrable]

theorem firstReportProbability_nonneg
    {reportingRate duration : ℝ}
    (h_mean : 0 ≤ reportingRate * duration) :
    0 ≤ firstReportProbability reportingRate duration := by
  exact atLeastOneArrivalProb_nonneg h_mean

theorem firstReportProbability_le_one
    (reportingRate duration : ℝ) :
    firstReportProbability reportingRate duration ≤ 1 :=
  atLeastOneArrivalProb_le_one reportingRate duration

theorem firstReportProbability_pos
    {reportingRate duration : ℝ}
    (h_rate : 0 < reportingRate) (h_duration : 0 < duration) :
    0 < firstReportProbability reportingRate duration := by
  exact atLeastOneArrivalProb_pos h_rate h_duration

/--
The continuous-duration first-report probability is nonnegative when the
duration density is nonnegative, normalized, and the reporting rate is
nonnegative over the nonnegative-duration support.
-/
theorem continuousDurationFirstReportProbability_nonneg
    {reportingRate : ℝ} {durationDensity : ℝ → ℝ}
    (h_density_mass :
      (∫ t, durationDensity t
        ∂(volume.restrict (Set.Ici (0 : ℝ)))) = 1)
    (h_density_integrable :
      Integrable durationDensity (volume.restrict (Set.Ici (0 : ℝ))))
    (h_noReport_integrable :
      Integrable
        (fun t => durationDensity t * noArrivalProb reportingRate t)
        (volume.restrict (Set.Ici (0 : ℝ))))
    (h_density_nonneg : ∀ t, 0 ≤ durationDensity t)
    (h_rate_nonneg : 0 ≤ reportingRate) :
    0 ≤ continuousDurationFirstReportProbability
      reportingRate durationDensity := by
  rw [continuousDurationFirstReportProbability_eq_integral_firstReportProbability
    reportingRate durationDensity h_density_mass h_density_integrable
    h_noReport_integrable]
  apply MeasureTheory.integral_nonneg_of_ae
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with t ht
  exact mul_nonneg (h_density_nonneg t)
    (firstReportProbability_nonneg
      (mul_nonneg h_rate_nonneg (by simpa using ht)))

/--
The continuous-duration first-report probability is at most one when the
duration density is nonnegative.
-/
theorem continuousDurationFirstReportProbability_le_one
    (reportingRate : ℝ) {durationDensity : ℝ → ℝ}
    (h_density_nonneg : ∀ t, 0 ≤ durationDensity t) :
    continuousDurationFirstReportProbability reportingRate durationDensity ≤ 1 := by
  let μ : Measure ℝ := volume.restrict (Set.Ici (0 : ℝ))
  have h_noReport_nonneg :
      0 ≤ ∫ t,
        durationDensity t * noArrivalProb reportingRate t ∂μ := by
    apply MeasureTheory.integral_nonneg_of_ae
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with t _ht
    exact mul_nonneg (h_density_nonneg t)
      (noArrivalProb_nonneg reportingRate t)
  dsimp [continuousDurationFirstReportProbability,
    continuousDurationNoReportProbability, μ]
  exact sub_le_self 1 h_noReport_nonneg

/--
The finite-duration first-report probability is nonnegative when the weights
are a probability vector and each rate-duration product is nonnegative.
-/
theorem finiteDurationFirstReportProbability_nonneg
    {DurationType : Type*} [Fintype DurationType]
    {reportingRate : ℝ} {weight duration : DurationType → ℝ}
    (hweight_nonneg : ∀ d, 0 ≤ weight d)
    (hsum_weight : (∑ d, weight d) = 1)
    (h_mean : ∀ d, 0 ≤ reportingRate * duration d) :
    0 ≤ finiteDurationFirstReportProbability reportingRate weight duration := by
  rw [finiteDurationFirstReportProbability_eq_weighted_firstReportProbability
    reportingRate weight duration hsum_weight]
  exact Finset.sum_nonneg fun d _hd =>
    mul_nonneg (hweight_nonneg d)
      (firstReportProbability_nonneg (h_mean d))

/--
The finite-duration first-report probability is at most one when the weights
are a probability vector.
-/
theorem finiteDurationFirstReportProbability_le_one
    {DurationType : Type*} [Fintype DurationType]
    {reportingRate : ℝ} {weight duration : DurationType → ℝ}
    (hweight_nonneg : ∀ d, 0 ≤ weight d)
    (hsum_weight : (∑ d, weight d) = 1) :
    finiteDurationFirstReportProbability reportingRate weight duration ≤ 1 := by
  rw [finiteDurationFirstReportProbability_eq_weighted_firstReportProbability
    reportingRate weight duration hsum_weight]
  calc
    ∑ d, weight d * firstReportProbability reportingRate (duration d)
        ≤ ∑ d, weight d * 1 := by
          refine Finset.sum_le_sum ?_
          intro d _hd
          exact mul_le_mul_of_nonneg_left
            (firstReportProbability_le_one reportingRate (duration d))
            (hweight_nonneg d)
    _ = 1 := by
          simpa using hsum_weight

/--
The finite-duration first-report probability is positive when the duration
weights are a probability vector with positive mass on at least one positive
duration and the reporting rate is positive.
-/
theorem finiteDurationFirstReportProbability_pos
    {DurationType : Type*} [Fintype DurationType]
    {reportingRate : ℝ} {weight duration : DurationType → ℝ}
    (h_rate : 0 < reportingRate)
    (hweight_nonneg : ∀ d, 0 ≤ weight d)
    (hsum_weight : (∑ d, weight d) = 1)
    (hduration_nonneg : ∀ d, 0 ≤ duration d)
    (h_exists : ∃ d, 0 < weight d ∧ 0 < duration d) :
    0 < finiteDurationFirstReportProbability
      reportingRate weight duration := by
  rw [finiteDurationFirstReportProbability_eq_weighted_firstReportProbability
    reportingRate weight duration hsum_weight]
  refine Finset.sum_pos' ?h_nonneg ?h_pos
  · intro d _hd
    exact mul_nonneg (hweight_nonneg d)
      (firstReportProbability_nonneg
        (mul_nonneg (le_of_lt h_rate) (hduration_nonneg d)))
  · rcases h_exists with ⟨d, hweight_pos, hduration_pos⟩
    refine ⟨d, Finset.mem_univ d, ?_⟩
    exact mul_pos hweight_pos
      (firstReportProbability_pos h_rate hduration_pos)

/--
Finite-duration observed incident rate as the occurrence rate times the
weighted first-report probability over possible durations.
-/
theorem finiteDurationObservedIncidentRate_eq_weighted_firstReportProbability
    {DurationType : Type*} [Fintype DurationType]
    (incidentRate reportingRate : ℝ)
    (weight duration : DurationType → ℝ)
    (hsum_weight : (∑ d, weight d) = 1) :
    finiteDurationObservedIncidentRate
        incidentRate reportingRate weight duration =
      incidentRate *
        ∑ d, weight d * firstReportProbability reportingRate (duration d) := by
  simp [finiteDurationObservedIncidentRate,
    finiteDurationFirstReportProbability_eq_weighted_firstReportProbability
      reportingRate weight duration hsum_weight]

/--
Lemma 1 LLN step for unit observation intervals: if observed unique-incident
counts in unit intervals are IID and integrable, then their time average
converges almost surely to the one-period expected count.
-/
theorem lemma1_unit_interval_observed_counts_lln_of_iid
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
        atTop (nhds (∫ ω, observedCount 0 ω ∂P)) :=
  AppliedModelingLib.ae_tendsto_empirical_mean_real_of_iid
    observedCount hint hindep hident

/--
Lemma 1 source-rate form: when the one-period mean equals the
finite-duration observed incident rate, the observed unit-count time average
converges almost surely to that rate.
-/
theorem lemma1_unit_interval_observed_counts_lln_to_finite_duration_rate_of_iid
    {Ω DurationType : Type*} [MeasurableSpace Ω] [Fintype DurationType]
    {P : Measure Ω}
    (observedCount : ℕ → Ω → ℝ)
    (incidentRate reportingRate : ℝ)
    (weight duration : DurationType → ℝ)
    (hint : Integrable (observedCount 0) P)
    (hindep : Pairwise ((· ⟂ᵢ[P] ·) on observedCount))
    (hident :
      ∀ i, ProbabilityTheory.IdentDistrib
        (observedCount i) (observedCount 0) P P)
    (hmean :
      (∫ ω, observedCount 0 ω ∂P) =
        finiteDurationObservedIncidentRate
          incidentRate reportingRate weight duration) :
    ∀ᵐ ω ∂P,
      Tendsto
        (fun T : ℕ =>
          (∑ τ ∈ Finset.range T, observedCount τ ω) / T)
        atTop
        (nhds
          (finiteDurationObservedIncidentRate
            incidentRate reportingRate weight duration)) := by
  simpa [hmean] using
    lemma1_unit_interval_observed_counts_lln_of_iid
      observedCount hint hindep hident

/--
Lemma 1 source-rate form for continuous durations: when the one-period mean
equals the continuous-duration observed incident rate, the observed unit-count
time average converges almost surely to that rate.
-/
theorem lemma1_unit_interval_observed_counts_lln_to_continuous_duration_rate_of_iid
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
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
  simpa [hmean] using
    lemma1_unit_interval_observed_counts_lln_of_iid
      observedCount hint hindep hident

/--
Lemma 1 source-rate form for the nonhomogeneous cumulative-intensity
continuous-duration rate.
-/
theorem
    lemma1_unit_interval_observed_counts_lln_to_cumulative_intensity_duration_rate_of_iid
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
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
  simpa [hmean] using
    lemma1_unit_interval_observed_counts_lln_of_iid
      observedCount hint hindep hident

/--
Lemma 1 thinning count law: if original incident counts in a unit interval have
Poisson mean `incidentMean` and each incident is retained independently with
detection probability `detectionProb`, summing over latent original counts gives
the Poisson count likelihood with thinned mean `incidentMean * detectionProb`.
-/
theorem lemma1_poisson_thinning_count_likelihood
    (incidentMean detectionProb : ℝ) (observedCount : ℕ) :
    (∑' originalCount : ℕ,
        countLikelihood 1 incidentMean originalCount *
          binomialThinningMass detectionProb originalCount observedCount) =
      countLikelihood 1 (incidentMean * detectionProb) observedCount :=
  tsum_countLikelihood_mul_binomialThinningMass
    incidentMean detectionProb observedCount

/--
Lemma 1 finite-duration thinning count law, with the detection probability
specialized to the finite-duration first-report probability.
-/
theorem lemma1_finite_duration_poisson_thinning_count_likelihood
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
  simpa [finiteDurationObservedIncidentRate] using
    lemma1_poisson_thinning_count_likelihood
      incidentMean
      (finiteDurationFirstReportProbability reportingRate weight duration)
      observedCount

/--
Lemma 1 continuous-duration thinning count law, with the detection probability
specialized to the homogeneous continuous-duration first-report probability
appearing in the source formula.
-/
theorem lemma1_continuous_duration_poisson_thinning_count_likelihood
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
  simpa [continuousDurationObservedIncidentRate] using
    lemma1_poisson_thinning_count_likelihood
      incidentMean
      (continuousDurationFirstReportProbability reportingRate durationDensity)
      observedCount

/--
Lemma 1 continuous-duration thinning count law for the nonhomogeneous
cumulative-intensity version of the source formula.
-/
theorem
    lemma1_continuous_duration_cumulative_intensity_poisson_thinning_count_likelihood
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
  simpa [continuousDurationObservedIncidentRateOfCumulativeIntensity] using
    lemma1_poisson_thinning_count_likelihood
      incidentMean
      (continuousDurationFirstReportProbabilityOfCumulativeIntensity
        cumulativeIntensity durationDensity)
      observedCount

/--
Lemma 1 finite-duration thinning as a reusable count-law certificate.  The
stochastic model supplies the latent Poisson count and binomial thinning
mixture; the reusable certificate proves the observed count is Poisson with
the thinned mean.
-/
def lemma1FiniteDurationPoissonThinningCountLaw
    {DurationType : Type*} [Fintype DurationType]
    (incidentMean reportingRate : ℝ)
    (weight duration : DurationType → ℝ) : PoissonThinningCountLaw :=
  PoissonThinningCountLaw.ofMixture incidentMean
    (finiteDurationFirstReportProbability reportingRate weight duration)

/--
Lemma 1 continuous-duration thinning as a reusable count-law certificate.  The
only specialization is the source continuous-duration detection probability;
the Poisson-thinning algebra remains paper-neutral.
-/
def lemma1ContinuousDurationPoissonThinningCountLaw
    (incidentMean reportingRate : ℝ)
    (durationDensity : ℝ → ℝ) : PoissonThinningCountLaw :=
  PoissonThinningCountLaw.ofMixture incidentMean
    (continuousDurationFirstReportProbability reportingRate durationDensity)

/--
Lemma 1 nonhomogeneous continuous-duration thinning as a reusable count-law
certificate, specialized to the cumulative-intensity detection probability.
-/
def lemma1ContinuousDurationCumulativeIntensityPoissonThinningCountLaw
    (incidentMean : ℝ) (cumulativeIntensity durationDensity : ℝ → ℝ) :
    PoissonThinningCountLaw :=
  PoissonThinningCountLaw.ofMixture incidentMean
    (continuousDurationFirstReportProbabilityOfCumulativeIntensity
      cumulativeIntensity durationDensity)

/--
Lemma 1 finite-duration thinning count law via the reusable count-law
certificate.
-/
theorem lemma1_finite_duration_poisson_thinning_count_law_from_certificate
    {DurationType : Type*} [Fintype DurationType]
    (incidentMean reportingRate : ℝ)
    (weight duration : DurationType → ℝ) (observedCount : ℕ) :
    (lemma1FiniteDurationPoissonThinningCountLaw
        incidentMean reportingRate weight duration).observedMass
        observedCount =
      countLikelihood 1
        (finiteDurationObservedIncidentRate
          incidentMean reportingRate weight duration)
        observedCount := by
  simpa [lemma1FiniteDurationPoissonThinningCountLaw,
    finiteDurationObservedIncidentRate] using
      (lemma1FiniteDurationPoissonThinningCountLaw
        incidentMean reportingRate weight duration).observedMass_eq_countLikelihood
          observedCount

/--
Lemma 1 continuous-duration thinning count law via the reusable count-law
certificate.
-/
theorem lemma1_continuous_duration_poisson_thinning_count_law_from_certificate
    (incidentMean reportingRate : ℝ)
    (durationDensity : ℝ → ℝ) (observedCount : ℕ) :
    (lemma1ContinuousDurationPoissonThinningCountLaw
        incidentMean reportingRate durationDensity).observedMass
        observedCount =
      countLikelihood 1
        (continuousDurationObservedIncidentRate
          incidentMean reportingRate durationDensity)
        observedCount := by
  simpa [lemma1ContinuousDurationPoissonThinningCountLaw,
    continuousDurationObservedIncidentRate] using
      (lemma1ContinuousDurationPoissonThinningCountLaw
        incidentMean reportingRate durationDensity).observedMass_eq_countLikelihood
          observedCount

/--
Lemma 1 nonhomogeneous continuous-duration thinning count law via the reusable
count-law certificate.
-/
theorem
    lemma1_continuous_duration_cumulative_intensity_poisson_thinning_count_law_from_certificate
    (incidentMean : ℝ) (cumulativeIntensity durationDensity : ℝ → ℝ)
    (observedCount : ℕ) :
    (lemma1ContinuousDurationCumulativeIntensityPoissonThinningCountLaw
        incidentMean cumulativeIntensity durationDensity).observedMass
        observedCount =
      countLikelihood 1
        (continuousDurationObservedIncidentRateOfCumulativeIntensity
          incidentMean cumulativeIntensity durationDensity)
        observedCount := by
  simpa [lemma1ContinuousDurationCumulativeIntensityPoissonThinningCountLaw,
    continuousDurationObservedIncidentRateOfCumulativeIntensity] using
      ((lemma1ContinuousDurationCumulativeIntensityPoissonThinningCountLaw
        incidentMean cumulativeIntensity durationDensity).observedMass_eq_countLikelihood
        observedCount)

/--
Lemma 1 observed-count construction: any nonnegative observed incident rate is
realized by a Poisson count whose singleton probabilities match the paper's
Poisson PMF.
-/
theorem lemma1_exists_poisson_observed_count_for_rate
    (observedRate : ℝ) (h_observedRate : 0 ≤ observedRate) :
    ∃ Ω : Type, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω,
      ∃ X : Ω → ℕ,
        Measurable X ∧
        ProbabilityTheory.HasLaw X
          (ProbabilityTheory.poissonMeasure
            (rateExposureParam 1 observedRate
              (by simpa using h_observedRate))) P ∧
        IsProbabilityMeasure P ∧
        ∀ observedCount : ℕ,
          P.real {ω : Ω | X ω = observedCount} =
            sourcePoissonPMF 1 observedRate observedCount := by
  rcases exists_poisson_count_real_eq_countLikelihood
      observedRate h_observedRate with
    ⟨Ω, mΩ, P, X, hmeas, hLaw, hprob, hpmf⟩
  exact ⟨Ω, mΩ, P, X, hmeas, hLaw, hprob,
    fun observedCount => by
      simpa [sourcePoissonPMF] using hpmf observedCount⟩

/--
Lemma 1 finite-duration observed-count construction, specialized to the
finite-support duration mixture observed incident rate.
-/
theorem lemma1_exists_finite_duration_poisson_observed_count
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
  exact lemma1_exists_poisson_observed_count_for_rate
    (finiteDurationObservedIncidentRate incidentMean reportingRate weight duration)
    h_observedRate

/--
Lemma 1 continuous-duration observed-count construction, specialized to the
homogeneous reporting-rate integral formula.
-/
theorem lemma1_exists_continuous_duration_poisson_observed_count
    (incidentMean reportingRate : ℝ) (durationDensity : ℝ → ℝ)
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
  exact lemma1_exists_poisson_observed_count_for_rate
    (continuousDurationObservedIncidentRate
      incidentMean reportingRate durationDensity)
    h_observedRate

/--
Lemma 1 nonhomogeneous continuous-duration observed-count construction,
specialized to the cumulative-intensity source formula.
-/
theorem
    lemma1_exists_continuous_duration_cumulative_intensity_poisson_observed_count
    (incidentMean : ℝ) (cumulativeIntensity durationDensity : ℝ → ℝ)
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
  exact lemma1_exists_poisson_observed_count_for_rate
    (continuousDurationObservedIncidentRateOfCumulativeIntensity
      incidentMean cumulativeIntensity durationDensity)
    h_observedRate

/--
The finite-duration detection probability used in Lemma 1 gives a nonnegative
binomial thinning mass under the usual duration-distribution side conditions.
-/
theorem lemma1_finite_duration_binomialThinningMass_nonneg
    {DurationType : Type*} [Fintype DurationType]
    {reportingRate : ℝ} {weight duration : DurationType → ℝ}
    (hweight_nonneg : ∀ d, 0 ≤ weight d)
    (hsum_weight : (∑ d, weight d) = 1)
    (h_mean : ∀ d, 0 ≤ reportingRate * duration d)
    (trials kept : ℕ) :
    0 ≤ binomialThinningMass
      (finiteDurationFirstReportProbability reportingRate weight duration)
      trials kept := by
  exact binomialThinningMass_nonneg
    (finiteDurationFirstReportProbability_nonneg
      hweight_nonneg hsum_weight h_mean)
    (finiteDurationFirstReportProbability_le_one
      hweight_nonneg hsum_weight)
    trials kept

/--
Each summand in the finite-duration Poisson thinning count law is nonnegative
under nonnegative incident mean and the usual duration-distribution side
conditions.
-/
theorem lemma1_finite_duration_poisson_thinning_summand_nonneg
    {DurationType : Type*} [Fintype DurationType]
    {incidentMean reportingRate : ℝ} {weight duration : DurationType → ℝ}
    (hincidentMean : 0 ≤ incidentMean)
    (hweight_nonneg : ∀ d, 0 ≤ weight d)
    (hsum_weight : (∑ d, weight d) = 1)
    (h_mean : ∀ d, 0 ≤ reportingRate * duration d)
    (originalCount observedCount : ℕ) :
    0 ≤ countLikelihood 1 incidentMean originalCount *
      binomialThinningMass
        (finiteDurationFirstReportProbability reportingRate weight duration)
        originalCount observedCount := by
  exact countLikelihood_mul_binomialThinningMass_nonneg
    (by simpa using hincidentMean)
    (finiteDurationFirstReportProbability_nonneg
      hweight_nonneg hsum_weight h_mean)
    (finiteDurationFirstReportProbability_le_one
      hweight_nonneg hsum_weight)
    originalCount observedCount

/--
Lemma 2 reusable tail form: a homogeneous no-arrival interval has the same
survival function as an exponential waiting time with the same rate.
-/
theorem lemma2_no_arrival_eq_exponential_tail
    (rate : ℝ) (h_rate : 0 < rate)
    {exposure : ℝ} (h_exposure : 0 ≤ exposure) :
    noArrivalProb rate exposure =
      ((AppliedModelingLib.Probability.Exponential.Model.mk rate h_rate).measure
        (Set.Ioi exposure)).toReal := by
  exact noArrivalProb_eq_exponential_tail rate h_rate h_exposure

/--
Lemma 2 memoryless-tail algebra: after no arrival through an elapsed interval,
the residual no-arrival probability over a future interval is unchanged.
-/
theorem lemma2_no_arrival_memoryless_tail_ratio
    (rate elapsed future : ℝ) :
    noArrivalProb rate (elapsed + future) / noArrivalProb rate elapsed =
      noArrivalProb rate future :=
  noArrivalProb_add_div_noArrivalProb_left rate elapsed future

/--
Lemma 2 exponential memoryless-tail form: the ratio of exponential tail
probabilities after an elapsed wait equals the tail probability for the
remaining future wait.
-/
theorem lemma2_exponential_memoryless_tail_ratio
    (rate : ℝ) (h_rate : 0 < rate)
    {elapsed future : ℝ}
    (h_elapsed : 0 ≤ elapsed) (h_future : 0 ≤ future) :
    ((AppliedModelingLib.Probability.Exponential.Model.mk rate h_rate).measure
        (Set.Ioi (elapsed + future))).toReal /
      ((AppliedModelingLib.Probability.Exponential.Model.mk rate h_rate).measure
        (Set.Ioi elapsed)).toReal =
    ((AppliedModelingLib.Probability.Exponential.Model.mk rate h_rate).measure
        (Set.Ioi future)).toReal := by
  exact
    (AppliedModelingLib.Probability.Exponential.Model.mk
      rate h_rate).measure_Ioi_add_div_measure_Ioi_toReal
        h_elapsed h_future

/--
Lemma 2 density-mixture step: after the Poisson memoryless property removes
dependence on the realized start time, integrating the remaining no-arrival
tail against the normalized `g(s)` density leaves the same exponential tail.
-/
theorem lemma2_no_arrival_density_mixture
    (rate epsilon : ℝ) {startDensity : ℝ → ℝ}
    (h_density_mass : ∫ s, startDensity s = 1) :
    ∫ s, noArrivalProb rate epsilon * startDensity s =
      noArrivalProb rate epsilon := by
  exact noArrivalProb_density_mixture_eq_self
    rate epsilon h_density_mass

/--
Lemma 2 restricted-start density-mixture step: the same source argument over
`s ≥ t1` when the start-time density is normalized on that support.
-/
theorem lemma2_no_arrival_density_mixture_on_Ici
    (rate epsilon lower : ℝ) {startDensity : ℝ → ℝ}
    (h_density_mass :
      ∫ s, startDensity s ∂(volume.restrict (Set.Ici lower)) = 1) :
    ∫ s, noArrivalProb rate epsilon * startDensity s
        ∂(volume.restrict (Set.Ici lower)) =
      noArrivalProb rate epsilon := by
  exact noArrivalProb_density_mixture_restrict_Ici_eq_self
    rate epsilon lower h_density_mass

/--
Lemma 2 Poisson-mass step: the shifted count sum in the source proof is the
total mass of a Poisson count likelihood, hence equals one for nonnegative
rate-exposure product.
-/
theorem lemma2_poisson_count_likelihood_tsum_one
    {rate exposure : ℝ} (h_nonneg : 0 ≤ rate * exposure) :
    (∑' count : ℕ, countLikelihood rate exposure count) = 1 :=
  tsum_countLikelihood h_nonneg

/--
Lemma 2 source-sum/integral collapse after the Tonelli/Fubini exchange used in
the paper: the shifted Poisson count mass contributes one inside the
restricted start-density integral.
-/
theorem lemma2_no_arrival_density_mixture_with_poisson_count_mass_on_Ici
    (rate epsilon lower : ℝ) {elapsed : ℝ → ℝ}
    {startDensity : ℝ → ℝ}
    (h_density_mass :
      ∫ s, startDensity s ∂(volume.restrict (Set.Ici lower)) = 1)
    (h_count_nonneg : ∀ s, 0 ≤ rate * elapsed s) :
    ∫ s,
        noArrivalProb rate epsilon *
          (∑' count : ℕ, countLikelihood rate (elapsed s) count) *
          startDensity s ∂(volume.restrict (Set.Ici lower)) =
      noArrivalProb rate epsilon := by
  calc
    ∫ s,
        noArrivalProb rate epsilon *
          (∑' count : ℕ, countLikelihood rate (elapsed s) count) *
          startDensity s ∂(volume.restrict (Set.Ici lower))
        = ∫ s, noArrivalProb rate epsilon * startDensity s
            ∂(volume.restrict (Set.Ici lower)) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with s
          rw [tsum_countLikelihood (h_count_nonneg s)]
          ring
    _ = noArrivalProb rate epsilon := by
          exact lemma2_no_arrival_density_mixture_on_Ici
            rate epsilon lower h_density_mass

/--
Lemma 2 process-law form: the no-arrival probability for a valid observation
window under a homogeneous Poisson process law is the exponential waiting-time
tail at the same shared rate.
-/
theorem lemma2_process_law_no_arrival_eq_exponential_tail
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : HomogeneousPoissonProcessLaw Ω P) (W : ObservationWindow) :
    P.real {ω : Ω |
        H.countLaw.intervalCount W.startTime W.endTime ω = 0} =
      ((AppliedModelingLib.Probability.Exponential.Model.mk
          H.rate H.rate_pos).measure (Set.Ioi W.exposure)).toReal := by
  exact H.windowCount_zero_prob_eq_exponential_tail W

/--
Lemma 2 ordered one-jump density form under the combined homogeneous Poisson
process law.
-/
theorem lemma2_process_law_one_jump_density_eq_exponential_pdf_tail
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : HomogeneousPoissonProcessLaw Ω P) (T : OrderedOneJumpWindow) :
    H.arrivalLaw.oneJumpDensity T =
      (AppliedModelingLib.Probability.Exponential.Model.mk
          H.rate H.rate_pos).pdfReal T.gap *
        ((AppliedModelingLib.Probability.Exponential.Model.mk
          H.rate H.rate_pos).measure (Set.Ioi T.tail)).toReal := by
  exact H.oneJumpDensity_eq_exponential_pdfReal_mul_tail T

/--
Lemma 2 ordered finite-jump density form under the combined homogeneous Poisson
process law.
-/
theorem lemma2_process_law_finite_jump_density_eq_exponential_pdf_tail
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : HomogeneousPoissonProcessLaw Ω P) (T : OrderedFiniteJumpTimeline) :
    H.arrivalLaw.finiteJumpDensity T =
      (∏ j : Fin T.count,
          (AppliedModelingLib.Probability.Exponential.Model.mk
            H.rate H.rate_pos).pdfReal (T.gap j)) *
        ((AppliedModelingLib.Probability.Exponential.Model.mk
          H.rate H.rate_pos).measure (Set.Ioi T.tail)).toReal := by
  exact H.finiteJumpDensity_eq_exponential_pdfReal_prod_mul_tail T

/--
Lemma 2 process-law normalization: integrating the one-jump density over the
one-dimensional ordered jump-time region agrees with the one-count probability
for the same observation window.
-/
theorem lemma2_process_law_one_jump_density_ordered_region_volume_eq_count_prob
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : HomogeneousPoissonProcessLaw Ω P) (T : OrderedOneJumpWindow)
    (h_exposure : T.window.exposure ≠ 0) :
    H.arrivalLaw.oneJumpDensity T *
        (volume (orderedJumpRegion 1 T.window.exposure)).toReal =
      P.real {ω : Ω |
        H.countLaw.intervalCount T.window.startTime T.window.endTime ω = 1} := by
  exact
    H.oneJumpDensity_mul_orderedJumpRegionVolume_eq_windowCount_prob
      T h_exposure

/--
Lemma 2 process-law normalization: the finite ordered-jump density, normalized
by the recursive ordered-volume factor, agrees with the matching count
probability for the same observation window.
-/
theorem lemma2_process_law_finite_jump_density_ordered_volume_eq_count_prob
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : HomogeneousPoissonProcessLaw Ω P) (T : OrderedFiniteJumpTimeline)
    (h_exposure : T.window.exposure ≠ 0) :
    H.arrivalLaw.finiteJumpDensity T *
        orderedJumpNestedVolume T.count T.window.exposure =
      P.real {ω : Ω |
        H.countLaw.intervalCount T.window.startTime T.window.endTime ω =
          T.count} := by
  exact
    H.finiteJumpDensity_mul_orderedJumpNestedVolume_eq_windowCount_prob
      T h_exposure

/--
Lemma 2 process-law normalization: the finite ordered-jump density, normalized
by the actual Lebesgue volume of the finite ordered jump-time region, agrees
with the matching count probability for the same observation window.
-/
theorem lemma2_process_law_finite_jump_density_ordered_region_volume_eq_count_prob
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (H : HomogeneousPoissonProcessLaw Ω P) (T : OrderedFiniteJumpTimeline)
    (h_exposure : T.window.exposure ≠ 0) :
    H.arrivalLaw.finiteJumpDensity T *
        (volume (orderedJumpRegion T.count T.window.exposure)).toReal =
      P.real {ω : Ω |
        H.countLaw.intervalCount T.window.startTime T.window.endTime ω =
          T.count} := by
  exact
    H.finiteJumpDensity_mul_orderedJumpRegionVolume_eq_windowCount_prob
      T h_exposure

/--
Homogeneous reporting-delay mean: the expected waiting time for one
rate-`rate` exponential reporting clock is `1 / rate`.
-/
theorem homogeneous_reporting_delay_mean
    (rate : ℝ) (h_rate : 0 < rate) :
    ∫ x, x ∂(AppliedModelingLib.Probability.Exponential.Model.mk rate h_rate).measure =
      1 / rate := by
  rw [AppliedModelingLib.Probability.Exponential.Model.integral_id_eq_expectedMaxValue_one]
  simp [AppliedModelingLib.Probability.Exponential.Model.expectedMaxValue,
    AppliedModelingLib.Probability.Exponential.expectedMaxValueOfRate_one]

/--
Proposition 1 algebraic core: if only the observed unique-incident rate is
available, different reporting rates can be paired with different occurrence
rates to produce exactly the same observed rate.
-/
theorem proposition1_homogeneous_nonidentifiability_collision
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
  refine ⟨hrates, ?_⟩
  unfold homogeneousObservedIncidentRate
  field_simp [hprob₁, hprob₂]

/--
Proposition 1 homogeneous non-identifiability with paper-natural positivity
premises instead of explicit nonzero first-report probabilities.
-/
theorem proposition1_homogeneous_nonidentifiability_collision_of_pos
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
  exact proposition1_homogeneous_nonidentifiability_collision
    hrates
    (ne_of_gt (firstReportProbability_pos hrate₁ hduration))
    (ne_of_gt (firstReportProbability_pos hrate₂ hduration))

/--
Finite-duration-mixture version of Proposition 1's algebraic core: even when
duration is averaged over a finite distribution, distinct reporting rates can
be paired with different occurrence rates to produce the same observed
unique-incident rate.
-/
theorem proposition1_finite_duration_nonidentifiability_collision
    {DurationType : Type*} [Fintype DurationType]
    (weight duration : DurationType → ℝ)
    {observedRate rate₁ rate₂ : ℝ}
    (hrates : rate₁ ≠ rate₂)
    (hprob₁ :
      finiteDurationFirstReportProbability rate₁ weight duration ≠ 0)
    (hprob₂ :
      finiteDurationFirstReportProbability rate₂ weight duration ≠ 0) :
    rate₁ ≠ rate₂ ∧
      finiteDurationObservedIncidentRate
          (observedRate /
            finiteDurationFirstReportProbability rate₁ weight duration)
          rate₁ weight duration =
        finiteDurationObservedIncidentRate
          (observedRate /
            finiteDurationFirstReportProbability rate₂ weight duration)
          rate₂ weight duration := by
  refine ⟨hrates, ?_⟩
  unfold finiteDurationObservedIncidentRate
  field_simp [hprob₁, hprob₂]

/--
Continuous-duration version of Proposition 1's algebraic core: distinct
homogeneous reporting rates can be paired with different occurrence rates to
produce the same observed unique-incident rate after averaging over a
continuous duration density.
-/
theorem proposition1_continuous_duration_nonidentifiability_collision
    (durationDensity : ℝ → ℝ)
    {observedRate rate₁ rate₂ : ℝ}
    (hrates : rate₁ ≠ rate₂)
    (hprob₁ :
      continuousDurationFirstReportProbability rate₁ durationDensity ≠ 0)
    (hprob₂ :
      continuousDurationFirstReportProbability rate₂ durationDensity ≠ 0) :
    rate₁ ≠ rate₂ ∧
      continuousDurationObservedIncidentRate
          (observedRate /
            continuousDurationFirstReportProbability rate₁ durationDensity)
          rate₁ durationDensity =
        continuousDurationObservedIncidentRate
          (observedRate /
            continuousDurationFirstReportProbability rate₂ durationDensity)
          rate₂ durationDensity := by
  refine ⟨hrates, ?_⟩
  unfold continuousDurationObservedIncidentRate
  field_simp [hprob₁, hprob₂]

/--
Finite-duration-mixture Proposition 1 with paper-natural positivity premises:
positive reporting rates and a duration distribution with positive mass on a
positive duration imply the nonzero detection probabilities used by the
algebraic collision theorem.
-/
theorem proposition1_finite_duration_nonidentifiability_collision_of_pos
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
  exact proposition1_finite_duration_nonidentifiability_collision
    weight duration hrates
    (ne_of_gt
      (finiteDurationFirstReportProbability_pos
        hrate₁ hweight_nonneg hsum_weight hduration_nonneg h_exists))
    (ne_of_gt
      (finiteDurationFirstReportProbability_pos
        hrate₂ hweight_nonneg hsum_weight hduration_nonneg h_exists))

/--
Theorem 1 / Theorem 2 algebraic core: once the Appendix B.2 process argument
has isolated all rate-independent density factors into `kernelResidual`, the
remaining rate dependence is exactly a Poisson count likelihood with the
corrected residual factor.
-/
theorem theorem2_raw_case_likelihood_factorizes
    {kernelResidual rate exposure : ℝ} {count : ℕ}
    (h_exposure : exposure ≠ 0) :
    theorem2RawCaseLikelihood kernelResidual rate exposure count =
      theorem2CorrectedResidual kernelResidual exposure count *
        sourcePoissonPMF rate exposure count := by
  simpa [theorem2RawCaseLikelihood, theorem2CorrectedResidual, sourcePoissonPMF]
    using
      ratePowerExp_factor_countLikelihood
        kernelResidual rate exposure count h_exposure

theorem theorem2_raw_case_likelihood_factorizes_of_pos
    {kernelResidual rate exposure : ℝ} {count : ℕ}
    (h_exposure : 0 < exposure) :
    theorem2RawCaseLikelihood kernelResidual rate exposure count =
      theorem2CorrectedResidual kernelResidual exposure count *
        sourcePoissonPMF rate exposure count :=
  theorem2_raw_case_likelihood_factorizes h_exposure.ne'

/-- Appendix B.2 Eq. (20), zero-report source case. -/
theorem theorem2_zero_report_case_factorization
    (startDensity endDensity rate exposure : ℝ) :
    theorem2ZeroReportLikelihood startDensity endDensity rate exposure =
      theorem2ZeroReportResidual startDensity endDensity *
        sourcePoissonPMF rate exposure 0 := by
  simp [theorem2ZeroReportLikelihood, theorem2ZeroReportResidual,
    sourcePoissonPMF]

/-- Appendix B.2 Eq. (26), one-report source case. -/
theorem theorem2_one_report_case_factorization
    {startDensity endDensityAfterJump endSurvivalIntegral rate exposure : ℝ}
    (h_exposure : exposure ≠ 0) :
    theorem2OneReportLikelihood
        startDensity endDensityAfterJump endSurvivalIntegral rate exposure =
      (theorem2OneReportKernelResidual
          startDensity endDensityAfterJump endSurvivalIntegral / exposure) *
        sourcePoissonPMF rate exposure 1 := by
  simpa [theorem2OneReportLikelihood, theorem2OneReportKernelResidual,
    theorem2RawCaseLikelihood, theorem2CorrectedResidual, sourcePoissonPMF] using
      theorem2_raw_case_likelihood_factorizes
        (kernelResidual := theorem2OneReportKernelResidual
          startDensity endDensityAfterJump endSurvivalIntegral)
        (rate := rate) (exposure := exposure) (count := 1) h_exposure

/-- Appendix B.2 Eq. (26), one-report source case with positive exposure. -/
theorem theorem2_one_report_case_factorization_of_pos_exposure
    {startDensity endDensityAfterJump endSurvivalIntegral rate exposure : ℝ}
    (h_exposure_pos : 0 < exposure) :
    theorem2OneReportLikelihood
        startDensity endDensityAfterJump endSurvivalIntegral rate exposure =
      (theorem2OneReportKernelResidual
          startDensity endDensityAfterJump endSurvivalIntegral / exposure) *
        sourcePoissonPMF rate exposure 1 := by
  exact theorem2_one_report_case_factorization (ne_of_gt h_exposure_pos)

/-- Appendix B.2 Eq. (32), multi-report source case with the corrected residual. -/
theorem theorem2_multi_report_case_factorization
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
  refine ⟨hcount, ?_⟩
  simpa [theorem2MultiReportLikelihood, theorem2MultiReportKernelResidual,
    theorem2CorrectedResidual, sourcePoissonPMF] using
      theorem2_raw_case_likelihood_factorizes
        (kernelResidual := theorem2MultiReportKernelResidual
          startDensity endDensityAfterLastJump survivalIntegralProduct)
        (rate := rate) (exposure := exposure) (count := count) h_exposure

/--
Appendix B.2 Eq. (32), multi-report source case with positive exposure.
-/
theorem theorem2_multi_report_case_factorization_of_pos_exposure
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
  exact theorem2_multi_report_case_factorization
    hcount (ne_of_gt h_exposure_pos)

/--
Appendix B.2 Eq. (30) to Eq. (31), reusable kernel collection form:
the product of homogeneous interarrival densities and the terminal no-arrival
tail collects to `rate^M * exp(-rate * totalExposure)`.
-/
theorem theorem2_interarrival_tail_likelihood_collects
    {Jump : Type*} (jumps : Finset Jump)
    (rate : ℝ) (gap : Jump → ℝ) (tail : ℝ) :
    theorem2InterarrivalTailLikelihood jumps rate gap tail =
      rate ^ jumps.card *
        Real.exp (-(rate * ((∑ j ∈ jumps, gap j) + tail))) := by
  exact interarrivalTailLikelihood_eq_rawShape
    jumps rate gap tail

/--
Appendix B.2 Eq. (31) exposure form: if the observed interarrival gaps plus
the terminal tail cover the whole observation exposure, the rate-dependent
kernel has the source shape `rate^M * exp(-rate * exposure)`.
-/
theorem theorem2_interarrival_tail_likelihood_eq_exposure_raw_shape
    {Jump : Type*} (jumps : Finset Jump)
    {rate exposure tail : ℝ} (gap : Jump → ℝ)
    (hexposure : (∑ j ∈ jumps, gap j) + tail = exposure) :
    theorem2InterarrivalTailLikelihood jumps rate gap tail =
      rate ^ jumps.card * Real.exp (-(rate * exposure)) := by
  exact interarrivalTailLikelihood_eq_exposure_rawShape jumps gap hexposure

/--
Corrected Appendix B.2 multi-report Poisson kernel on an ordered timeline.
The first stored gap is `t_{m+1} - s`, not `t_{m+1} - t_m`; consequently all
gaps plus the terminal tail telescope to the observation exposure `e - s`.
-/
theorem theorem2_orderedTimeline_interarrival_tail_collects
    (T : OrderedFiniteJumpTimeline) (rate : ℝ) :
    theorem2InterarrivalTailLikelihood (Finset.univ : Finset (Fin T.count))
        rate T.gap T.tail =
      rate ^ T.count * Real.exp (-(rate * T.window.exposure)) := by
  rw [theorem2_interarrival_tail_likelihood_eq_exposure_raw_shape
    (jumps := (Finset.univ : Finset (Fin T.count)))
    (rate := rate) (exposure := T.window.exposure) (tail := T.tail)
    T.gap (by simpa using T.exposure_eq)]
  simp

/--
The corrected ordered-timeline kernel factors into the Poisson count PMF and
the ordered-simplex reciprocal-volume residual.  This is the direct finite
Poisson correction behind the source's multi-report Eq. (30)--(32) algebra.
-/
theorem theorem2_orderedTimeline_interarrival_tail_factorizes
    (T : OrderedFiniteJumpTimeline) (rate : ℝ)
    (h_exposure : T.window.exposure ≠ 0) :
    theorem2InterarrivalTailLikelihood (Finset.univ : Finset (Fin T.count))
        rate T.gap T.tail =
      ((T.count.factorial : ℝ) / T.window.exposure ^ T.count) *
        sourcePoissonPMF rate T.window.exposure T.count := by
  rw [theorem2_orderedTimeline_interarrival_tail_collects]
  simpa [sourcePoissonPMF] using
    (ratePowerExp_factor_countLikelihood 1 rate T.window.exposure T.count h_exposure)

/--
Appendix B.2 Eq. (24) to Eq. (25): the one-report interarrival density and
terminal no-arrival tail collect to the source-shaped one-report likelihood.
-/
theorem theorem2_one_report_kernel_collects
    {startDensity endDensityAfterJump endSurvivalIntegral rate gap tail exposure : ℝ}
    (hexposure : gap + tail = exposure) :
    theorem2OneReportKernelResidual
        startDensity endDensityAfterJump endSurvivalIntegral *
        interarrivalDensityKernel rate gap * noArrivalProb rate tail =
      theorem2OneReportLikelihood
        startDensity endDensityAfterJump endSurvivalIntegral rate exposure := by
  rw [theorem2OneReportLikelihood, interarrivalDensityKernel, noArrivalProb]
  rw [show -(rate * exposure) = -(rate * gap) + -(rate * tail) by
    rw [← hexposure]
    ring, Real.exp_add]
  ring_nf

/--
The one-report density kernel over a deterministic observation window
normalizes to the one-count Poisson likelihood.
-/
theorem theorem2_one_report_window_density_integral_eq_sourcePoissonPMF
    {startTime endTime rate : ℝ} (h_window : startTime ≤ endTime) :
    (∫ x in startTime..endTime,
        interarrivalDensityKernel rate (x - startTime) *
          noArrivalProb rate (endTime - x)) =
      sourcePoissonPMF rate (observationExposure startTime endTime) 1 := by
  let W : ObservationWindow :=
    { startTime := startTime
      endTime := endTime
      start_le_end := h_window }
  simpa [W, sourcePoissonPMF, observationExposure,
    ObservationWindow.exposure] using
      oneJumpWindowDensityKernel_integral_eq_countLikelihood_one W rate

/--
The one-report process kernel with the paper's condition residual integrated
over the jump time equals that residual times the one-count Poisson likelihood.
-/
theorem theorem2_one_report_process_kernel_integral_eq_residual_mul_sourcePoissonPMF
    {startDensity endDensityAfterJump endSurvivalIntegral
      startTime endTime rate : ℝ}
    (h_window : startTime ≤ endTime) :
    (∫ x in startTime..endTime,
        theorem2OneReportKernelResidual
            startDensity endDensityAfterJump endSurvivalIntegral *
          interarrivalDensityKernel rate (x - startTime) *
          noArrivalProb rate (endTime - x)) =
      theorem2OneReportKernelResidual
          startDensity endDensityAfterJump endSurvivalIntegral *
        sourcePoissonPMF rate (observationExposure startTime endTime) 1 := by
  have hcongr :
    (∫ x in startTime..endTime,
        theorem2OneReportKernelResidual
            startDensity endDensityAfterJump endSurvivalIntegral *
            interarrivalDensityKernel rate (x - startTime) *
          noArrivalProb rate (endTime - x)) =
      (∫ x in startTime..endTime,
        theorem2OneReportKernelResidual
            startDensity endDensityAfterJump endSurvivalIntegral *
          (interarrivalDensityKernel rate (x - startTime) *
            noArrivalProb rate (endTime - x))) := by
    refine intervalIntegral.integral_congr ?_
    intro x _hx
    ring
  rw [hcongr]
  rw [intervalIntegral.integral_const_mul]
  rw [theorem2_one_report_window_density_integral_eq_sourcePoissonPMF h_window]

/--
The one-report interarrival density kernel, normalized by the one-dimensional
ordered-jump volume factor, recovers the one-count Poisson likelihood.
-/
theorem theorem2_one_report_density_mul_orderedJumpNestedVolume_eq_sourcePoissonPMF
    {rate gap tail exposure : ℝ}
    (hexposure : gap + tail = exposure)
    (h_exposure : exposure ≠ 0) :
    interarrivalDensityKernel rate gap * noArrivalProb rate tail *
        orderedJumpNestedVolume 1 exposure =
      sourcePoissonPMF rate exposure 1 := by
  let K : OneInterarrivalTailKernel :=
    { gap := gap
      tail := tail
      exposure := exposure
      exposure_eq := hexposure
      exposure_ne_zero := h_exposure }
  simpa [K, OneInterarrivalTailKernel.likelihood,
    sourcePoissonPMF] using
      K.likelihood_mul_orderedJumpNestedVolume_eq_countLikelihood rate

/--
Positive-exposure form of the one-report nested-volume normalization.
-/
theorem theorem2_one_report_density_mul_orderedJumpNestedVolume_eq_sourcePoissonPMF_of_pos_exposure
    {rate gap tail exposure : ℝ}
    (hexposure : gap + tail = exposure)
    (h_exposure_pos : 0 < exposure) :
    interarrivalDensityKernel rate gap * noArrivalProb rate tail *
        orderedJumpNestedVolume 1 exposure =
      sourcePoissonPMF rate exposure 1 := by
  exact theorem2_one_report_density_mul_orderedJumpNestedVolume_eq_sourcePoissonPMF
    hexposure (ne_of_gt h_exposure_pos)

/--
The one-report interarrival density kernel, normalized by the Lebesgue volume
of the one-dimensional ordered jump-time region, recovers the one-count
Poisson likelihood.
-/
theorem theorem2_one_report_density_mul_orderedJumpRegionVolume_eq_sourcePoissonPMF
    {rate gap tail exposure : ℝ}
    (hexposure : gap + tail = exposure)
    (h_exposure_nonneg : 0 ≤ exposure)
    (h_exposure : exposure ≠ 0) :
    interarrivalDensityKernel rate gap * noArrivalProb rate tail *
        (volume (orderedJumpRegion 1 exposure)).toReal =
      sourcePoissonPMF rate exposure 1 := by
  rw [orderedJumpRegion_one_volume_toReal h_exposure_nonneg]
  exact theorem2_one_report_density_mul_orderedJumpNestedVolume_eq_sourcePoissonPMF
    hexposure h_exposure

/--
Positive-exposure form of the one-report ordered-region normalization.
-/
theorem theorem2_one_report_density_mul_orderedJumpRegionVolume_eq_sourcePoissonPMF_of_pos_exposure
    {rate gap tail exposure : ℝ}
    (hexposure : gap + tail = exposure)
    (h_exposure_pos : 0 < exposure) :
    interarrivalDensityKernel rate gap * noArrivalProb rate tail *
        (volume (orderedJumpRegion 1 exposure)).toReal =
      sourcePoissonPMF rate exposure 1 := by
  exact
    theorem2_one_report_density_mul_orderedJumpRegionVolume_eq_sourcePoissonPMF
      hexposure (le_of_lt h_exposure_pos) (ne_of_gt h_exposure_pos)

/--
The one-report process kernel with the paper's condition residual, normalized
by the one-dimensional ordered-jump volume factor, equals that residual times
the one-count Poisson likelihood.
-/
theorem theorem2_one_report_process_kernel_density_mul_orderedJumpNestedVolume_eq_residual_mul_sourcePoissonPMF
    {startDensity endDensityAfterJump endSurvivalIntegral
      rate gap tail exposure : ℝ}
    (hexposure : gap + tail = exposure)
    (h_exposure : exposure ≠ 0) :
    theorem2OneReportKernelResidual
        startDensity endDensityAfterJump endSurvivalIntegral *
        interarrivalDensityKernel rate gap * noArrivalProb rate tail *
        orderedJumpNestedVolume 1 exposure =
    theorem2OneReportKernelResidual
        startDensity endDensityAfterJump endSurvivalIntegral *
        sourcePoissonPMF rate exposure 1 := by
  calc
    theorem2OneReportKernelResidual
        startDensity endDensityAfterJump endSurvivalIntegral *
        interarrivalDensityKernel rate gap * noArrivalProb rate tail *
        orderedJumpNestedVolume 1 exposure =
      theorem2OneReportKernelResidual
        startDensity endDensityAfterJump endSurvivalIntegral *
        (interarrivalDensityKernel rate gap * noArrivalProb rate tail *
          orderedJumpNestedVolume 1 exposure) := by
        ring
    _ =
      theorem2OneReportKernelResidual
        startDensity endDensityAfterJump endSurvivalIntegral *
        sourcePoissonPMF rate exposure 1 := by
        rw [theorem2_one_report_density_mul_orderedJumpNestedVolume_eq_sourcePoissonPMF
          hexposure h_exposure]

/--
Positive-exposure form of the one-report process-kernel nested-volume
normalization.
-/
theorem theorem2_one_report_process_kernel_density_mul_orderedJumpNestedVolume_eq_residual_mul_sourcePoissonPMF_of_pos_exposure
    {startDensity endDensityAfterJump endSurvivalIntegral
      rate gap tail exposure : ℝ}
    (hexposure : gap + tail = exposure)
    (h_exposure_pos : 0 < exposure) :
    theorem2OneReportKernelResidual
        startDensity endDensityAfterJump endSurvivalIntegral *
        interarrivalDensityKernel rate gap * noArrivalProb rate tail *
        orderedJumpNestedVolume 1 exposure =
    theorem2OneReportKernelResidual
        startDensity endDensityAfterJump endSurvivalIntegral *
        sourcePoissonPMF rate exposure 1 := by
  exact
    theorem2_one_report_process_kernel_density_mul_orderedJumpNestedVolume_eq_residual_mul_sourcePoissonPMF
      hexposure (ne_of_gt h_exposure_pos)

/--
The one-report process kernel with the paper's condition residual, normalized
by the Lebesgue volume of the one-dimensional ordered jump-time region, equals
that residual times the one-count Poisson likelihood.
-/
theorem theorem2_one_report_process_kernel_density_mul_orderedJumpRegionVolume_eq_residual_mul_sourcePoissonPMF
    {startDensity endDensityAfterJump endSurvivalIntegral
      rate gap tail exposure : ℝ}
    (hexposure : gap + tail = exposure)
    (h_exposure_nonneg : 0 ≤ exposure)
    (h_exposure : exposure ≠ 0) :
    theorem2OneReportKernelResidual
        startDensity endDensityAfterJump endSurvivalIntegral *
        interarrivalDensityKernel rate gap * noArrivalProb rate tail *
        (volume (orderedJumpRegion 1 exposure)).toReal =
    theorem2OneReportKernelResidual
        startDensity endDensityAfterJump endSurvivalIntegral *
        sourcePoissonPMF rate exposure 1 := by
  rw [orderedJumpRegion_one_volume_toReal h_exposure_nonneg]
  exact
    theorem2_one_report_process_kernel_density_mul_orderedJumpNestedVolume_eq_residual_mul_sourcePoissonPMF
      hexposure h_exposure

/--
Positive-exposure form of the one-report process-kernel ordered-region
normalization.
-/
theorem theorem2_one_report_process_kernel_density_mul_orderedJumpRegionVolume_eq_residual_mul_sourcePoissonPMF_of_pos_exposure
    {startDensity endDensityAfterJump endSurvivalIntegral
      rate gap tail exposure : ℝ}
    (hexposure : gap + tail = exposure)
    (h_exposure_pos : 0 < exposure) :
    theorem2OneReportKernelResidual
        startDensity endDensityAfterJump endSurvivalIntegral *
        interarrivalDensityKernel rate gap * noArrivalProb rate tail *
        (volume (orderedJumpRegion 1 exposure)).toReal =
    theorem2OneReportKernelResidual
        startDensity endDensityAfterJump endSurvivalIntegral *
        sourcePoissonPMF rate exposure 1 := by
  exact
    theorem2_one_report_process_kernel_density_mul_orderedJumpRegionVolume_eq_residual_mul_sourcePoissonPMF
      hexposure (le_of_lt h_exposure_pos) (ne_of_gt h_exposure_pos)

/--
Appendix B.2 Eq. (30) to Eq. (31): the multi-report interarrival-density
product and terminal no-arrival tail collect to the source-shaped multi-report
likelihood.
-/
theorem theorem2_multi_report_kernel_collects
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
  rw [theorem2_interarrival_tail_likelihood_eq_exposure_raw_shape
    jumps gap hexposure]
  rw [hcard]
  simp [theorem2MultiReportLikelihood]
  ring

/--
The multi-report interarrival density kernel, normalized by the ordered-jump
simplex volume factor, recovers the `M`-count Poisson likelihood.
-/
theorem theorem2_multi_report_density_mul_orderedJumpSimplexVolume_eq_sourcePoissonPMF
    {count : ℕ} {rate exposure tail : ℝ} (gap : Fin count → ℝ)
    (hexposure : (∑ j : Fin count, gap j) + tail = exposure)
    (h_exposure : exposure ≠ 0) :
    theorem2InterarrivalTailLikelihood (Finset.univ : Finset (Fin count))
        rate gap tail *
        orderedJumpSimplexVolume exposure count =
      sourcePoissonPMF rate exposure count := by
  let K : FinInterarrivalTailKernel :=
    { count := count
      gap := gap
      tail := tail
      exposure := exposure
      exposure_eq := hexposure
      exposure_ne_zero := h_exposure }
  simpa [K, FinInterarrivalTailKernel.likelihood,
    sourcePoissonPMF] using
      K.likelihood_mul_orderedJumpSimplexVolume_eq_countLikelihood rate

/--
The multi-report interarrival density kernel, normalized by the recursive
nested ordered-jump volume, recovers the `M`-count Poisson likelihood.
-/
theorem theorem2_multi_report_density_mul_orderedJumpNestedVolume_eq_sourcePoissonPMF
    {count : ℕ} {rate exposure tail : ℝ} (gap : Fin count → ℝ)
    (hexposure : (∑ j : Fin count, gap j) + tail = exposure)
    (h_exposure : exposure ≠ 0) :
    theorem2InterarrivalTailLikelihood (Finset.univ : Finset (Fin count))
        rate gap tail *
        orderedJumpNestedVolume count exposure =
      sourcePoissonPMF rate exposure count := by
  rw [orderedJumpNestedVolume_eq_orderedJumpSimplexVolume]
  exact theorem2_multi_report_density_mul_orderedJumpSimplexVolume_eq_sourcePoissonPMF
    gap hexposure h_exposure

/--
Positive-exposure form of the multi-report nested-volume normalization.
-/
theorem theorem2_multi_report_density_mul_orderedJumpNestedVolume_eq_sourcePoissonPMF_of_pos_exposure
    {count : ℕ} {rate exposure tail : ℝ} (gap : Fin count → ℝ)
    (hexposure : (∑ j : Fin count, gap j) + tail = exposure)
    (h_exposure_pos : 0 < exposure) :
    theorem2InterarrivalTailLikelihood (Finset.univ : Finset (Fin count))
        rate gap tail *
        orderedJumpNestedVolume count exposure =
      sourcePoissonPMF rate exposure count := by
  exact theorem2_multi_report_density_mul_orderedJumpNestedVolume_eq_sourcePoissonPMF
    gap hexposure (ne_of_gt h_exposure_pos)

/--
The multi-report interarrival density kernel, normalized by the actual
Lebesgue volume of the finite ordered jump-time region, recovers the
`M`-count Poisson likelihood.
-/
theorem theorem2_multi_report_density_mul_orderedJumpRegionVolume_eq_sourcePoissonPMF
    {count : ℕ} {rate exposure tail : ℝ} (gap : Fin count → ℝ)
    (hexposure : (∑ j : Fin count, gap j) + tail = exposure)
    (h_exposure_nonneg : 0 ≤ exposure)
    (h_exposure : exposure ≠ 0) :
    theorem2InterarrivalTailLikelihood (Finset.univ : Finset (Fin count))
        rate gap tail *
        (volume (orderedJumpRegion count exposure)).toReal =
      sourcePoissonPMF rate exposure count := by
  rw [orderedJumpRegion_volume_toReal h_exposure_nonneg]
  exact theorem2_multi_report_density_mul_orderedJumpNestedVolume_eq_sourcePoissonPMF
    gap hexposure h_exposure

/--
Positive-exposure form of the multi-report ordered-region normalization.
-/
theorem theorem2_multi_report_density_mul_orderedJumpRegionVolume_eq_sourcePoissonPMF_of_pos_exposure
    {count : ℕ} {rate exposure tail : ℝ} (gap : Fin count → ℝ)
    (hexposure : (∑ j : Fin count, gap j) + tail = exposure)
    (h_exposure_pos : 0 < exposure) :
    theorem2InterarrivalTailLikelihood (Finset.univ : Finset (Fin count))
        rate gap tail *
        (volume (orderedJumpRegion count exposure)).toReal =
      sourcePoissonPMF rate exposure count := by
  exact
    theorem2_multi_report_density_mul_orderedJumpRegionVolume_eq_sourcePoissonPMF
      gap hexposure (le_of_lt h_exposure_pos) (ne_of_gt h_exposure_pos)

/--
The multi-report process kernel with the paper's condition residual,
normalized by the ordered-jump simplex volume factor, equals that residual
times the `M`-count Poisson likelihood.
-/
theorem theorem2_multi_report_process_kernel_density_mul_orderedJumpSimplexVolume_eq_residual_mul_sourcePoissonPMF
    {count : ℕ}
    {startDensity endDensityAfterLastJump survivalIntegralProduct
      rate exposure tail : ℝ} (gap : Fin count → ℝ)
    (hexposure : (∑ j : Fin count, gap j) + tail = exposure)
    (h_exposure : exposure ≠ 0) :
    theorem2MultiReportKernelResidual
        startDensity endDensityAfterLastJump survivalIntegralProduct *
        theorem2InterarrivalTailLikelihood
          (Finset.univ : Finset (Fin count)) rate gap tail *
        orderedJumpSimplexVolume exposure count =
      theorem2MultiReportKernelResidual
        startDensity endDensityAfterLastJump survivalIntegralProduct *
        sourcePoissonPMF rate exposure count := by
  rw [mul_assoc]
  rw [theorem2_multi_report_density_mul_orderedJumpSimplexVolume_eq_sourcePoissonPMF
    gap hexposure h_exposure]

/--
The multi-report process kernel with the paper's condition residual,
normalized by the recursive nested ordered-jump volume integral, equals that
residual times the `M`-count Poisson likelihood.
-/
theorem theorem2_multi_report_process_kernel_density_mul_orderedJumpNestedVolume_eq_residual_mul_sourcePoissonPMF
    {count : ℕ}
    {startDensity endDensityAfterLastJump survivalIntegralProduct
      rate exposure tail : ℝ} (gap : Fin count → ℝ)
    (hexposure : (∑ j : Fin count, gap j) + tail = exposure)
    (h_exposure : exposure ≠ 0) :
    theorem2MultiReportKernelResidual
        startDensity endDensityAfterLastJump survivalIntegralProduct *
        theorem2InterarrivalTailLikelihood
          (Finset.univ : Finset (Fin count)) rate gap tail *
        orderedJumpNestedVolume count exposure =
      theorem2MultiReportKernelResidual
        startDensity endDensityAfterLastJump survivalIntegralProduct *
        sourcePoissonPMF rate exposure count := by
  let K : FinInterarrivalTailKernel :=
    { count := count
      gap := gap
      tail := tail
      exposure := exposure
      exposure_eq := hexposure
      exposure_ne_zero := h_exposure }
  rw [mul_assoc]
  simpa [K, FinInterarrivalTailKernel.likelihood, sourcePoissonPMF] using
    congrArg
      (fun x =>
        theorem2MultiReportKernelResidual
          startDensity endDensityAfterLastJump survivalIntegralProduct * x)
      (K.likelihood_mul_orderedJumpNestedVolume_eq_countLikelihood rate)

/--
Positive-exposure form of the multi-report process-kernel nested-volume
normalization.
-/
theorem theorem2_multi_report_process_kernel_density_mul_orderedJumpNestedVolume_eq_residual_mul_sourcePoissonPMF_of_pos_exposure
    {count : ℕ}
    {startDensity endDensityAfterLastJump survivalIntegralProduct
      rate exposure tail : ℝ} (gap : Fin count → ℝ)
    (hexposure : (∑ j : Fin count, gap j) + tail = exposure)
    (h_exposure_pos : 0 < exposure) :
    theorem2MultiReportKernelResidual
        startDensity endDensityAfterLastJump survivalIntegralProduct *
        theorem2InterarrivalTailLikelihood
          (Finset.univ : Finset (Fin count)) rate gap tail *
        orderedJumpNestedVolume count exposure =
      theorem2MultiReportKernelResidual
        startDensity endDensityAfterLastJump survivalIntegralProduct *
        sourcePoissonPMF rate exposure count := by
  exact
    theorem2_multi_report_process_kernel_density_mul_orderedJumpNestedVolume_eq_residual_mul_sourcePoissonPMF
      gap hexposure (ne_of_gt h_exposure_pos)

/--
The multi-report process kernel with the paper's condition residual,
normalized by the actual Lebesgue volume of the finite ordered jump-time
region, equals that residual times the `M`-count Poisson likelihood.
-/
theorem theorem2_multi_report_process_kernel_density_mul_orderedJumpRegionVolume_eq_residual_mul_sourcePoissonPMF
    {count : ℕ}
    {startDensity endDensityAfterLastJump survivalIntegralProduct
      rate exposure tail : ℝ} (gap : Fin count → ℝ)
    (hexposure : (∑ j : Fin count, gap j) + tail = exposure)
    (h_exposure_nonneg : 0 ≤ exposure)
    (h_exposure : exposure ≠ 0) :
    theorem2MultiReportKernelResidual
        startDensity endDensityAfterLastJump survivalIntegralProduct *
        theorem2InterarrivalTailLikelihood
          (Finset.univ : Finset (Fin count)) rate gap tail *
        (volume (orderedJumpRegion count exposure)).toReal =
      theorem2MultiReportKernelResidual
        startDensity endDensityAfterLastJump survivalIntegralProduct *
        sourcePoissonPMF rate exposure count := by
  rw [orderedJumpRegion_volume_toReal h_exposure_nonneg]
  exact
    theorem2_multi_report_process_kernel_density_mul_orderedJumpNestedVolume_eq_residual_mul_sourcePoissonPMF
      gap hexposure h_exposure

/--
Positive-exposure form of the multi-report process-kernel ordered-region
normalization.
-/
theorem theorem2_multi_report_process_kernel_density_mul_orderedJumpRegionVolume_eq_residual_mul_sourcePoissonPMF_of_pos_exposure
    {count : ℕ}
    {startDensity endDensityAfterLastJump survivalIntegralProduct
      rate exposure tail : ℝ} (gap : Fin count → ℝ)
    (hexposure : (∑ j : Fin count, gap j) + tail = exposure)
    (h_exposure_pos : 0 < exposure) :
    theorem2MultiReportKernelResidual
        startDensity endDensityAfterLastJump survivalIntegralProduct *
        theorem2InterarrivalTailLikelihood
          (Finset.univ : Finset (Fin count)) rate gap tail *
        (volume (orderedJumpRegion count exposure)).toReal =
      theorem2MultiReportKernelResidual
        startDensity endDensityAfterLastJump survivalIntegralProduct *
        sourcePoissonPMF rate exposure count := by
  exact
    theorem2_multi_report_process_kernel_density_mul_orderedJumpRegionVolume_eq_residual_mul_sourcePoissonPMF
      gap hexposure (le_of_lt h_exposure_pos) (ne_of_gt h_exposure_pos)

/--
The two-report interarrival density kernel, normalized by the Lebesgue volume
of the two-dimensional ordered jump-time region, recovers the two-count
Poisson likelihood.
-/
theorem theorem2_two_report_density_mul_orderedJumpRegionVolume_eq_sourcePoissonPMF
    {rate exposure tail : ℝ} (gap : Fin 2 → ℝ)
    (hexposure : (∑ j : Fin 2, gap j) + tail = exposure)
    (h_exposure_nonneg : 0 ≤ exposure)
    (h_exposure : exposure ≠ 0) :
    theorem2InterarrivalTailLikelihood (Finset.univ : Finset (Fin 2))
        rate gap tail *
        (volume (orderedJumpRegion 2 exposure)).toReal =
      sourcePoissonPMF rate exposure 2 := by
  exact theorem2_multi_report_density_mul_orderedJumpRegionVolume_eq_sourcePoissonPMF
    gap hexposure h_exposure_nonneg h_exposure

/--
Positive-exposure form of the two-report ordered-region normalization.
-/
theorem theorem2_two_report_density_mul_orderedJumpRegionVolume_eq_sourcePoissonPMF_of_pos_exposure
    {rate exposure tail : ℝ} (gap : Fin 2 → ℝ)
    (hexposure : (∑ j : Fin 2, gap j) + tail = exposure)
    (h_exposure_pos : 0 < exposure) :
    theorem2InterarrivalTailLikelihood (Finset.univ : Finset (Fin 2))
        rate gap tail *
        (volume (orderedJumpRegion 2 exposure)).toReal =
      sourcePoissonPMF rate exposure 2 := by
  exact theorem2_two_report_density_mul_orderedJumpRegionVolume_eq_sourcePoissonPMF
    gap hexposure (le_of_lt h_exposure_pos) (ne_of_gt h_exposure_pos)

/--
The two-report process kernel with the paper's condition residual, normalized
by the Lebesgue volume of the two-dimensional ordered jump-time region, equals
that residual times the two-count Poisson likelihood.
-/
theorem theorem2_two_report_process_kernel_density_mul_orderedJumpRegionVolume_eq_residual_mul_sourcePoissonPMF
    {startDensity endDensityAfterLastJump survivalIntegralProduct
      rate exposure tail : ℝ} (gap : Fin 2 → ℝ)
    (hexposure : (∑ j : Fin 2, gap j) + tail = exposure)
    (h_exposure_nonneg : 0 ≤ exposure)
    (h_exposure : exposure ≠ 0) :
    theorem2MultiReportKernelResidual
        startDensity endDensityAfterLastJump survivalIntegralProduct *
        theorem2InterarrivalTailLikelihood
          (Finset.univ : Finset (Fin 2)) rate gap tail *
        (volume (orderedJumpRegion 2 exposure)).toReal =
      theorem2MultiReportKernelResidual
        startDensity endDensityAfterLastJump survivalIntegralProduct *
        sourcePoissonPMF rate exposure 2 := by
  exact
    theorem2_multi_report_process_kernel_density_mul_orderedJumpRegionVolume_eq_residual_mul_sourcePoissonPMF
      gap hexposure h_exposure_nonneg h_exposure

/--
Positive-exposure form of the two-report process-kernel ordered-region
normalization.
-/
theorem theorem2_two_report_process_kernel_density_mul_orderedJumpRegionVolume_eq_residual_mul_sourcePoissonPMF_of_pos_exposure
    {startDensity endDensityAfterLastJump survivalIntegralProduct
      rate exposure tail : ℝ} (gap : Fin 2 → ℝ)
    (hexposure : (∑ j : Fin 2, gap j) + tail = exposure)
    (h_exposure_pos : 0 < exposure) :
    theorem2MultiReportKernelResidual
        startDensity endDensityAfterLastJump survivalIntegralProduct *
        theorem2InterarrivalTailLikelihood
          (Finset.univ : Finset (Fin 2)) rate gap tail *
        (volume (orderedJumpRegion 2 exposure)).toReal =
      theorem2MultiReportKernelResidual
        startDensity endDensityAfterLastJump survivalIntegralProduct *
        sourcePoissonPMF rate exposure 2 := by
  exact
    theorem2_two_report_process_kernel_density_mul_orderedJumpRegionVolume_eq_residual_mul_sourcePoissonPMF
      gap hexposure (le_of_lt h_exposure_pos) (ne_of_gt h_exposure_pos)

/--
Appendix B.2 zero-report process-kernel factorization from the no-arrival
source factor directly to the Poisson count PMF.
-/
theorem theorem2_zero_report_process_kernel_factorization
    (startDensity endDensity rate exposure : ℝ) :
    theorem2ZeroReportProcessKernelLikelihood
        startDensity endDensity rate exposure =
      theorem2ZeroReportResidual startDensity endDensity *
        sourcePoissonPMF rate exposure 0 := by
  simp [theorem2ZeroReportProcessKernelLikelihood, sourcePoissonPMF,
    noArrivalProb]

/--
Appendix B.2 one-report process-kernel factorization from the interarrival
density/no-arrival source factors directly to the Poisson count PMF.
-/
theorem theorem2_one_report_process_kernel_factorization
    {startDensity endDensityAfterJump endSurvivalIntegral rate gap tail exposure : ℝ}
    (hexposure : gap + tail = exposure) (h_exposure : exposure ≠ 0) :
    theorem2OneReportProcessKernelLikelihood
        startDensity endDensityAfterJump endSurvivalIntegral rate gap tail =
      (theorem2OneReportKernelResidual
          startDensity endDensityAfterJump endSurvivalIntegral / exposure) *
        sourcePoissonPMF rate exposure 1 := by
  rw [theorem2OneReportProcessKernelLikelihood]
  rw [theorem2_one_report_kernel_collects hexposure]
  exact theorem2_one_report_case_factorization h_exposure

/--
Appendix B.2 one-report process-kernel factorization with positive exposure.
-/
theorem theorem2_one_report_process_kernel_factorization_of_pos_exposure
    {startDensity endDensityAfterJump endSurvivalIntegral rate gap tail exposure : ℝ}
    (hexposure : gap + tail = exposure) (h_exposure_pos : 0 < exposure) :
    theorem2OneReportProcessKernelLikelihood
        startDensity endDensityAfterJump endSurvivalIntegral rate gap tail =
      (theorem2OneReportKernelResidual
          startDensity endDensityAfterJump endSurvivalIntegral / exposure) *
        sourcePoissonPMF rate exposure 1 := by
  exact theorem2_one_report_process_kernel_factorization
    hexposure (ne_of_gt h_exposure_pos)

/--
Appendix B.2 multi-report process-kernel factorization from the
interarrival-density product/no-arrival source factors directly to the Poisson
count PMF.
-/
theorem theorem2_multi_report_process_kernel_factorization
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
  refine ⟨hcount, ?_⟩
  rw [theorem2MultiReportProcessKernelLikelihood]
  rw [theorem2_multi_report_kernel_collects jumps gap hcard hexposure]
  exact (theorem2_multi_report_case_factorization
    (startDensity := startDensity)
    (endDensityAfterLastJump := endDensityAfterLastJump)
    (survivalIntegralProduct := survivalIntegralProduct)
    (rate := rate) (exposure := exposure) (count := count)
    hcount h_exposure).2

/--
Appendix B.2 multi-report process-kernel factorization with positive exposure.
-/
theorem theorem2_multi_report_process_kernel_factorization_of_pos_exposure
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
  exact theorem2_multi_report_process_kernel_factorization
    jumps gap hcard hexposure hcount (ne_of_gt h_exposure_pos)

/--
Source-shaped Appendix B.2 process-kernel case.

Unlike `Theorem2SourceCase`, this keeps the no-arrival and interarrival
density kernels visible.  The remaining stochastic-process work is to derive
one of these cases from the conditional-probability semantics of Conditions
1/2; the likelihood algebra from these source kernels is checked below.
-/
inductive Theorem2ProcessKernelCase where
  | zero (startDensity endDensity exposure : ℝ)
  | one
      (startDensity endDensityAfterJump endSurvivalIntegral gap tail exposure : ℝ)
      (exposure_eq : gap + tail = exposure)
      (exposure_ne_zero : exposure ≠ 0)
  | multi
      (startDensity endDensityAfterLastJump survivalIntegralProduct exposure tail : ℝ)
      (count : ℕ) (count_gt_one : 1 < count)
      (gap : Fin count → ℝ)
      (exposure_eq : (∑ j : Fin count, gap j) + tail = exposure)
      (exposure_ne_zero : exposure ≠ 0)

namespace Theorem2ProcessKernelCase

/-- Exposure length `e-s` for a source-shaped process-kernel case. -/
def exposure : Theorem2ProcessKernelCase → ℝ
  | zero _ _ exposure => exposure
  | one _ _ _ _ _ exposure _ _ => exposure
  | multi _ _ _ exposure _ _ _ _ _ _ => exposure

/-- Report count `M` for a source-shaped process-kernel case. -/
def count : Theorem2ProcessKernelCase → ℕ
  | zero _ _ _ => 0
  | one _ _ _ _ _ _ _ _ => 1
  | multi _ _ _ _ _ count _ _ _ _ => count

/-- One-report process-kernel case built from a positive exposure premise. -/
def oneOfPos
    (startDensity endDensityAfterJump endSurvivalIntegral gap tail exposure : ℝ)
    (exposure_eq : gap + tail = exposure)
    (exposure_pos : 0 < exposure) : Theorem2ProcessKernelCase :=
  one startDensity endDensityAfterJump endSurvivalIntegral gap tail exposure
    exposure_eq (ne_of_gt exposure_pos)

/-- Multi-report process-kernel case built from a positive exposure premise. -/
def multiOfPos
    (startDensity endDensityAfterLastJump survivalIntegralProduct
      exposure tail : ℝ)
    (count : ℕ) (count_gt_one : 1 < count)
    (gap : Fin count → ℝ)
    (exposure_eq : (∑ j : Fin count, gap j) + tail = exposure)
    (exposure_pos : 0 < exposure) : Theorem2ProcessKernelCase :=
  multi startDensity endDensityAfterLastJump survivalIntegralProduct
    exposure tail count count_gt_one gap exposure_eq (ne_of_gt exposure_pos)

/-- Process-kernel likelihood expression for a source-shaped Appendix B.2 case. -/
def likelihood (C : Theorem2ProcessKernelCase) (rate : ℝ) : ℝ :=
  match C with
  | zero startDensity endDensity exposure =>
      theorem2ZeroReportProcessKernelLikelihood
        startDensity endDensity rate exposure
  | one startDensity endDensityAfterJump endSurvivalIntegral gap tail _ _ _ =>
      theorem2OneReportProcessKernelLikelihood
        startDensity endDensityAfterJump endSurvivalIntegral rate gap tail
  | multi startDensity endDensityAfterLastJump survivalIntegralProduct _ tail
      count _ gap _ _ =>
      theorem2MultiReportProcessKernelLikelihood
        (Finset.univ : Finset (Fin count))
        startDensity endDensityAfterLastJump survivalIntegralProduct
        rate gap tail

/-- Corrected rate-independent residual for a process-kernel case. -/
def residual : Theorem2ProcessKernelCase → ℝ
  | zero startDensity endDensity _ =>
      theorem2ZeroReportResidual startDensity endDensity
  | one startDensity endDensityAfterJump endSurvivalIntegral _ _ exposure _ _ =>
      theorem2OneReportKernelResidual
        startDensity endDensityAfterJump endSurvivalIntegral / exposure
  | multi startDensity endDensityAfterLastJump survivalIntegralProduct
      exposure _ count _ _ _ _ =>
      theorem2CorrectedResidual
        (theorem2MultiReportKernelResidual
          startDensity endDensityAfterLastJump survivalIntegralProduct)
        exposure count

end Theorem2ProcessKernelCase

/-! ## Source-Kernel Constructors For Appendix B.2 -/

/--
Zero-report source data for Appendix B.2, Eq. (18)--(20), using the reusable
Poisson no-arrival kernel for the rate-dependent part.
-/
structure Theorem2ZeroReportProcessData where
  startDensity : ℝ
  endDensity : ℝ
  noArrival : NoArrivalKernel

/--
One-report source data for Appendix B.2, Eq. (23)--(26), using the reusable
one-interarrival-plus-tail kernel for the rate-dependent part.
-/
structure Theorem2OneReportProcessData where
  startDensity : ℝ
  endDensityAfterJump : ℝ
  endSurvivalIntegral : ℝ
  arrival : OneInterarrivalTailKernel

/--
Multi-report source data for Appendix B.2, Eq. (29)--(32), using the reusable
finite interarrival-product-plus-tail kernel for the rate-dependent part.
-/
structure Theorem2MultiReportProcessData where
  startDensity : ℝ
  endDensityAfterLastJump : ℝ
  survivalIntegralProduct : ℝ
  arrival : FinInterarrivalTailKernel
  count_gt_one : 1 < arrival.count

namespace Theorem2ZeroReportProcessData

def exposure (D : Theorem2ZeroReportProcessData) : ℝ :=
  D.noArrival.exposure

def toProcessKernelCase
    (D : Theorem2ZeroReportProcessData) : Theorem2ProcessKernelCase :=
  Theorem2ProcessKernelCase.zero D.startDensity D.endDensity D.exposure

end Theorem2ZeroReportProcessData

namespace Theorem2OneReportProcessData

def exposure (D : Theorem2OneReportProcessData) : ℝ :=
  D.arrival.exposure

def toProcessKernelCase
    (D : Theorem2OneReportProcessData) : Theorem2ProcessKernelCase :=
  Theorem2ProcessKernelCase.one
    D.startDensity D.endDensityAfterJump D.endSurvivalIntegral
    D.arrival.gap D.arrival.tail D.exposure
    D.arrival.exposure_eq D.arrival.exposure_ne_zero

end Theorem2OneReportProcessData

namespace Theorem2MultiReportProcessData

def exposure (D : Theorem2MultiReportProcessData) : ℝ :=
  D.arrival.exposure

def toProcessKernelCase
    (D : Theorem2MultiReportProcessData) : Theorem2ProcessKernelCase :=
  Theorem2ProcessKernelCase.multi
    D.startDensity D.endDensityAfterLastJump D.survivalIntegralProduct
    D.exposure D.arrival.tail D.arrival.count D.count_gt_one D.arrival.gap
    D.arrival.exposure_eq D.arrival.exposure_ne_zero

end Theorem2MultiReportProcessData

/--
Source-data union for the zero/one/multi-report cases in Appendix B.2.

This is the narrower paper-facing bridge: a future full stochastic-process
theorem should construct one of these records from Conditions 1/2 and the
homogeneous Poisson process law, rather than supplying an arbitrary likelihood.
-/
inductive Theorem2ProcessSourceData where
  | zero (D : Theorem2ZeroReportProcessData)
  | one (D : Theorem2OneReportProcessData)
  | multi (D : Theorem2MultiReportProcessData)

namespace Theorem2ProcessSourceData

def toProcessKernelCase : Theorem2ProcessSourceData → Theorem2ProcessKernelCase
  | zero D => D.toProcessKernelCase
  | one D => D.toProcessKernelCase
  | multi D => D.toProcessKernelCase

def exposure (D : Theorem2ProcessSourceData) : ℝ :=
  D.toProcessKernelCase.exposure

def count (D : Theorem2ProcessSourceData) : ℕ :=
  D.toProcessKernelCase.count

def likelihood (D : Theorem2ProcessSourceData) (rate : ℝ) : ℝ :=
  D.toProcessKernelCase.likelihood rate

def residual (D : Theorem2ProcessSourceData) : ℝ :=
  D.toProcessKernelCase.residual

/-- Generic Poisson arrival-kernel case carried by the source-data row. -/
def arrivalKernelCase : Theorem2ProcessSourceData → ArrivalKernelCase
  | zero D => ArrivalKernelCase.zero D.noArrival
  | one D => ArrivalKernelCase.one D.arrival
  | multi D => ArrivalKernelCase.finite D.arrival

/--
The rate-independent condition-function residual multiplying the generic
Poisson arrival kernel.
-/
def conditionResidual : Theorem2ProcessSourceData → ℝ
  | zero D => theorem2ZeroReportResidual D.startDensity D.endDensity
  | one D =>
      theorem2OneReportKernelResidual
        D.startDensity D.endDensityAfterJump D.endSurvivalIntegral
  | multi D =>
      theorem2MultiReportKernelResidual
        D.startDensity D.endDensityAfterLastJump
        D.survivalIntegralProduct

theorem exposure_eq_arrivalKernelCase_exposure
    (D : Theorem2ProcessSourceData) :
    D.exposure = D.arrivalKernelCase.exposure := by
  cases D <;> rfl

theorem count_eq_arrivalKernelCase_count
    (D : Theorem2ProcessSourceData) :
    D.count = D.arrivalKernelCase.count := by
  cases D <;> rfl

/--
Source-data likelihoods split into condition-function residuals and reusable
arrival-kernel likelihoods before any Poisson PMF rewrite.
-/
theorem likelihood_eq_conditionResidual_mul_arrivalKernelCase_likelihood
    (D : Theorem2ProcessSourceData) (rate : ℝ) :
    D.likelihood rate =
      D.conditionResidual * D.arrivalKernelCase.likelihood rate := by
  cases D with
  | zero D =>
      simp [likelihood, toProcessKernelCase, conditionResidual,
        arrivalKernelCase, Theorem2ZeroReportProcessData.toProcessKernelCase,
        Theorem2ZeroReportProcessData.exposure,
        Theorem2ProcessKernelCase.likelihood,
        theorem2ZeroReportProcessKernelLikelihood,
        ArrivalKernelCase.likelihood, NoArrivalKernel.likelihood]
  | one D =>
      simp [likelihood, toProcessKernelCase, conditionResidual,
        arrivalKernelCase, Theorem2OneReportProcessData.toProcessKernelCase,
        Theorem2ProcessKernelCase.likelihood,
        theorem2OneReportProcessKernelLikelihood,
        ArrivalKernelCase.likelihood, OneInterarrivalTailKernel.likelihood]
      ring
  | multi D =>
      simp [likelihood, toProcessKernelCase, conditionResidual,
        arrivalKernelCase, Theorem2MultiReportProcessData.toProcessKernelCase,
        Theorem2ProcessKernelCase.likelihood,
        theorem2MultiReportProcessKernelLikelihood,
        theorem2InterarrivalTailLikelihood,
        ArrivalKernelCase.likelihood, FinInterarrivalTailKernel.likelihood]

/--
The source-data residual is exactly the condition residual times the generic
arrival-kernel residual.
-/
theorem residual_eq_conditionResidual_mul_arrivalKernelCase_residual
    (D : Theorem2ProcessSourceData) :
    D.residual =
      D.conditionResidual * D.arrivalKernelCase.residual := by
  cases D with
  | zero D =>
      simp [residual, toProcessKernelCase, conditionResidual,
        arrivalKernelCase, Theorem2ZeroReportProcessData.toProcessKernelCase,
        Theorem2ZeroReportProcessData.exposure,
        Theorem2ProcessKernelCase.residual,
        ArrivalKernelCase.residual]
  | one D =>
      simp [residual, toProcessKernelCase, conditionResidual,
        arrivalKernelCase, Theorem2OneReportProcessData.toProcessKernelCase,
        Theorem2OneReportProcessData.exposure,
        Theorem2ProcessKernelCase.residual,
        ArrivalKernelCase.residual]
      ring
  | multi D =>
      simp [residual, toProcessKernelCase, conditionResidual,
        arrivalKernelCase, Theorem2MultiReportProcessData.toProcessKernelCase,
        Theorem2MultiReportProcessData.exposure,
        Theorem2ProcessKernelCase.residual,
        theorem2CorrectedResidual, ArrivalKernelCase.residual]
      ring

/--
The source-data arrival kernel has the reusable Poisson count-PMF
factorization.
-/
theorem arrivalKernelCase_factorization
    (D : Theorem2ProcessSourceData) (rate : ℝ) :
    D.arrivalKernelCase.likelihood rate =
      D.arrivalKernelCase.residual *
        countLikelihood rate
          D.arrivalKernelCase.exposure D.arrivalKernelCase.count :=
  D.arrivalKernelCase.factorization rate

/--
Source-data factorization proved through the generic arrival-kernel case.  This
keeps the rate-dependent Poisson-process algebra separate from the paper's
condition-function residuals.
-/
theorem factorization_via_arrivalKernelCase
    (D : Theorem2ProcessSourceData) (rate : ℝ) :
    D.likelihood rate =
      D.residual * sourcePoissonPMF rate D.exposure D.count := by
  rw [D.likelihood_eq_conditionResidual_mul_arrivalKernelCase_likelihood rate]
  rw [D.arrivalKernelCase_factorization rate]
  rw [D.residual_eq_conditionResidual_mul_arrivalKernelCase_residual]
  rw [D.exposure_eq_arrivalKernelCase_exposure,
    D.count_eq_arrivalKernelCase_count]
  simp [sourcePoissonPMF]
  ring

/--
The source-data residual in the Appendix B.2 factorization is independent of
the Poisson rate.
-/
theorem residual_rateIndependent
    (D : Theorem2ProcessSourceData) :
    RateIndependent (fun _rate : ℝ => D.residual) := by
  exact ⟨D.residual, fun _ => rfl⟩

end Theorem2ProcessSourceData

/-! ## Condition-Function Bookkeeping For Theorem 2 -/

/--
The paper's rate-independent condition functions at a fixed observed history.

`startDensity` represents `g(s)`.  `endDensity m` represents `h_m(e)`.
`survivalIntegral m` represents the source term
`∫_{t_{m+1}}^T h_m(t) dt` attached to the next observed jump.  The actual
measurability and conditional-density construction from Conditions 1/2 is the
remaining stochastic-process theorem; this record only stores the
rate-independent functions after that construction has been obtained.
-/
structure Theorem2ConditionFunctions where
  startDensity : ℝ
  endDensity : ℕ → ℝ
  survivalIntegral : ℕ → ℝ

namespace Theorem2ConditionFunctions

/-- Product of the survival-integral terms in Appendix B.2 Eq. (30). -/
def survivalIntegralProduct
    (K : Theorem2ConditionFunctions) (baseCount count : ℕ) : ℝ :=
  ∏ j : Fin count, K.survivalIntegral (baseCount + j.val)

/-- Source data for the zero-report Appendix B.2 case from condition functions. -/
def zeroReportSourceData
    (K : Theorem2ConditionFunctions) (baseCount : ℕ)
    (exposure : ℝ) : Theorem2ProcessSourceData :=
  Theorem2ProcessSourceData.zero
    { startDensity := K.startDensity
      endDensity := K.endDensity baseCount
      noArrival := { exposure := exposure } }

/-- Source data for the zero-report Appendix B.2 case from an observation window. -/
def zeroReportSourceDataFromWindow
    (K : Theorem2ConditionFunctions) (baseCount : ℕ)
    (W : ObservationWindow) : Theorem2ProcessSourceData :=
  Theorem2ProcessSourceData.zero
    { startDensity := K.startDensity
      endDensity := K.endDensity baseCount
      noArrival := NoArrivalKernel.fromWindow W }

/-- Source data for the one-report Appendix B.2 case from condition functions. -/
def oneReportSourceData
    (K : Theorem2ConditionFunctions) (baseCount : ℕ)
    (gap tail exposure : ℝ)
    (hexposure : gap + tail = exposure)
    (h_exposure : exposure ≠ 0) : Theorem2ProcessSourceData :=
  Theorem2ProcessSourceData.one
    { startDensity := K.startDensity
      endDensityAfterJump := K.endDensity (baseCount + 1)
      endSurvivalIntegral := K.survivalIntegral baseCount
      arrival :=
        { gap := gap
          tail := tail
          exposure := exposure
          exposure_eq := hexposure
          exposure_ne_zero := h_exposure } }

/--
One-report source data from actual start, end, and observed first jump time.
The exposure identity is proved by arithmetic.
-/
def oneReportSourceDataFromJumpTime
    (K : Theorem2ConditionFunctions) (baseCount : ℕ)
    (startTime endTime firstJumpTime : ℝ)
    (h_exposure : observationExposure startTime endTime ≠ 0) :
    Theorem2ProcessSourceData :=
  K.oneReportSourceData baseCount
    (firstJumpTime - startTime) (endTime - firstJumpTime)
    (observationExposure startTime endTime)
    (by
      unfold observationExposure
      ring)
    h_exposure

/--
One-report source data from a proper observation window.  The nonzero exposure
side condition follows from `startTime < endTime`.
-/
def oneReportSourceDataFromProperWindow
    (K : Theorem2ConditionFunctions) (baseCount : ℕ)
    (startTime endTime firstJumpTime : ℝ)
    (h_window : startTime < endTime) :
    Theorem2ProcessSourceData :=
  K.oneReportSourceDataFromJumpTime baseCount
    startTime endTime firstJumpTime
    (observationExposure_pos h_window).ne'

/-- One-report process data from a reusable ordered one-jump window. -/
def oneReportProcessDataFromOrderedJumpWindow
    (K : Theorem2ConditionFunctions) (baseCount : ℕ)
    (T : OrderedOneJumpWindow) (h_exposure : T.window.exposure ≠ 0) :
    Theorem2OneReportProcessData :=
  { startDensity := K.startDensity
    endDensityAfterJump := K.endDensity (baseCount + 1)
    endSurvivalIntegral := K.survivalIntegral baseCount
    arrival := OneInterarrivalTailKernel.fromOrderedWindow T h_exposure }

/-- Source data for the one-report Appendix B.2 case from an ordered window. -/
def oneReportSourceDataFromOrderedJumpWindow
    (K : Theorem2ConditionFunctions) (baseCount : ℕ)
    (T : OrderedOneJumpWindow) (h_exposure : T.window.exposure ≠ 0) :
    Theorem2ProcessSourceData :=
  Theorem2ProcessSourceData.one
    (K.oneReportProcessDataFromOrderedJumpWindow baseCount T h_exposure)

/--
One-report source data from an ordered observation window: the first observed
jump is explicitly inside the window.  The ordering premises are source
semantics for the interarrival gap and terminal no-arrival tail; the exposure
identity itself is still arithmetic.
-/
def oneReportSourceDataFromOrderedWindow
    (K : Theorem2ConditionFunctions) (baseCount : ℕ)
    (startTime endTime firstJumpTime : ℝ)
    (h_window : startTime < endTime)
    (h_start_le_jump : startTime ≤ firstJumpTime)
    (h_jump_le_end : firstJumpTime ≤ endTime) :
    Theorem2ProcessSourceData :=
  let W : ObservationWindow :=
    { startTime := startTime
      endTime := endTime
      start_le_end := le_of_lt h_window }
  let T : OrderedOneJumpWindow :=
    { window := W
      firstJumpTime := firstJumpTime
      start_le_jump := h_start_le_jump
      jump_le_end := h_jump_le_end }
  K.oneReportSourceDataFromOrderedJumpWindow baseCount T
    (W.exposure_pos_of_lt h_window).ne'

/--
The one-report ordered-window premises imply nonnegative interarrival and
terminal-tail lengths.
-/
theorem oneReportOrderedWindowGaps_nonneg
    {startTime endTime firstJumpTime : ℝ}
    (h_start_le_jump : startTime ≤ firstJumpTime)
    (h_jump_le_end : firstJumpTime ≤ endTime) :
    0 ≤ firstJumpTime - startTime ∧
      0 ≤ endTime - firstJumpTime := by
  exact ⟨sub_nonneg.mpr h_start_le_jump,
    sub_nonneg.mpr h_jump_le_end⟩

/-- Source data for the multi-report Appendix B.2 case from condition functions. -/
def multiReportSourceData
    (K : Theorem2ConditionFunctions) (baseCount count : ℕ)
    (hcount : 1 < count)
    (gap : Fin count → ℝ) (tail exposure : ℝ)
    (hexposure : (∑ j : Fin count, gap j) + tail = exposure)
    (h_exposure : exposure ≠ 0) : Theorem2ProcessSourceData :=
  Theorem2ProcessSourceData.multi
    { startDensity := K.startDensity
      endDensityAfterLastJump := K.endDensity (baseCount + count)
      survivalIntegralProduct := K.survivalIntegralProduct baseCount count
      arrival :=
        { count := count
          gap := gap
          tail := tail
          exposure := exposure
          exposure_eq := hexposure
          exposure_ne_zero := h_exposure }
      count_gt_one := hcount }

/--
Multi-report source data from actual start/end times and an indexed family of
observed jump times.  The interarrival-gap-plus-tail exposure identity is
discharged by the reusable telescoping lemma.
-/
def multiReportSourceDataFromJumpTimes
    (K : Theorem2ConditionFunctions) (baseCount count : ℕ)
    (hcount : 1 < count)
    (startTime endTime : ℝ) (jumpTime : ℕ → ℝ)
    (h_exposure : observationExposure startTime endTime ≠ 0) :
    Theorem2ProcessSourceData :=
  K.multiReportSourceData baseCount count hcount
    (fun j : Fin count =>
      interarrivalGapFromJumpTimes startTime jumpTime j.val)
    (terminalTailFromJumpTimes startTime endTime jumpTime count)
    (observationExposure startTime endTime)
    (by
      unfold observationExposure
      exact sum_fin_interarrivalGapFromJumpTimes_add_terminalTail
        startTime endTime jumpTime count)
    h_exposure

/--
Multi-report source data from a proper observation window and indexed observed
jump times.  The nonzero exposure side condition follows from
`startTime < endTime`.
-/
def multiReportSourceDataFromProperWindow
    (K : Theorem2ConditionFunctions) (baseCount count : ℕ)
    (hcount : 1 < count)
    (startTime endTime : ℝ) (jumpTime : ℕ → ℝ)
    (h_window : startTime < endTime) :
    Theorem2ProcessSourceData :=
  K.multiReportSourceDataFromJumpTimes baseCount count hcount
    startTime endTime jumpTime (observationExposure_pos h_window).ne'

/-- Multi-report process data from a reusable ordered finite-jump timeline. -/
def multiReportProcessDataFromOrderedTimeline
    (K : Theorem2ConditionFunctions) (baseCount : ℕ)
    (T : OrderedFiniteJumpTimeline) (hcount : 1 < T.count)
    (h_exposure : T.window.exposure ≠ 0) :
    Theorem2MultiReportProcessData :=
  { startDensity := K.startDensity
    endDensityAfterLastJump := K.endDensity (baseCount + T.count)
    survivalIntegralProduct := K.survivalIntegralProduct baseCount T.count
    arrival := FinInterarrivalTailKernel.fromOrderedTimeline T h_exposure
    count_gt_one := hcount }

/-- Source data for the multi-report Appendix B.2 case from an ordered timeline. -/
def multiReportSourceDataFromOrderedTimeline
    (K : Theorem2ConditionFunctions) (baseCount : ℕ)
    (T : OrderedFiniteJumpTimeline) (hcount : 1 < T.count)
    (h_exposure : T.window.exposure ≠ 0) :
    Theorem2ProcessSourceData :=
  Theorem2ProcessSourceData.multi
    (K.multiReportProcessDataFromOrderedTimeline baseCount T hcount h_exposure)

/--
Multi-report source data from an ordered observation window: the observed jump
timeline is monotone and the final observed endpoint lies before the window
end.  These are the paper-natural ordering conditions behind the nonnegative
interarrival gaps and terminal no-arrival tail.
-/
def multiReportSourceDataFromOrderedWindow
    (K : Theorem2ConditionFunctions) (baseCount count : ℕ)
    (hcount : 1 < count)
    (startTime endTime : ℝ) (jumpTime : ℕ → ℝ)
    (h_window : startTime < endTime)
    (hmono : Monotone (jumpTimelineEndpoint startTime jumpTime))
    (hlast :
      jumpTimelineEndpoint startTime jumpTime count ≤ endTime) :
    Theorem2ProcessSourceData :=
  let W : ObservationWindow :=
    { startTime := startTime
      endTime := endTime
      start_le_end := le_of_lt h_window }
  let T : OrderedFiniteJumpTimeline :=
    { window := W
      count := count
      jumpTime := jumpTime
      endpoint_mono := hmono
      last_le_end := hlast }
  K.multiReportSourceDataFromOrderedTimeline baseCount T hcount
    (W.exposure_pos_of_lt h_window).ne'

/--
The multi-report ordered-window premises imply all interarrival gaps and the
terminal tail are nonnegative.
-/
theorem multiReportOrderedWindowGaps_nonneg
    {count : ℕ} {startTime endTime : ℝ} {jumpTime : ℕ → ℝ}
    (hmono : Monotone (jumpTimelineEndpoint startTime jumpTime))
    (hlast : jumpTimelineEndpoint startTime jumpTime count ≤ endTime) :
    (∀ j : Fin count,
      0 ≤ interarrivalGapFromJumpTimes startTime jumpTime j.val) ∧
      0 ≤ terminalTailFromJumpTimes startTime endTime jumpTime count := by
  exact ⟨fun j => interarrivalGapFromJumpTimes_fin_nonneg_of_monotone hmono j,
    terminalTailFromJumpTimes_nonneg hlast⟩

/-- The zero-report window constructor carries exactly the window exposure. -/
theorem zeroReportSourceDataFromWindow_exposure
    (K : Theorem2ConditionFunctions) (baseCount : ℕ)
    (W : ObservationWindow) :
    (K.zeroReportSourceDataFromWindow baseCount W).exposure =
      W.exposure := by
  simp [zeroReportSourceDataFromWindow,
    Theorem2ProcessSourceData.exposure,
    Theorem2ProcessSourceData.toProcessKernelCase,
    Theorem2ZeroReportProcessData.toProcessKernelCase,
    Theorem2ZeroReportProcessData.exposure,
    Theorem2ProcessKernelCase.exposure,
    NoArrivalKernel.fromWindow]

/-- The zero-report window constructor carries count zero. -/
theorem zeroReportSourceDataFromWindow_count
    (K : Theorem2ConditionFunctions) (baseCount : ℕ)
    (W : ObservationWindow) :
    (K.zeroReportSourceDataFromWindow baseCount W).count = 0 := by
  simp [zeroReportSourceDataFromWindow,
    Theorem2ProcessSourceData.count,
    Theorem2ProcessSourceData.toProcessKernelCase,
    Theorem2ZeroReportProcessData.toProcessKernelCase,
    Theorem2ProcessKernelCase.count]

/-- The zero-report window constructor carries the zero-report residual. -/
theorem zeroReportSourceDataFromWindow_residual
    (K : Theorem2ConditionFunctions) (baseCount : ℕ)
    (W : ObservationWindow) :
    (K.zeroReportSourceDataFromWindow baseCount W).residual =
      theorem2ZeroReportResidual K.startDensity (K.endDensity baseCount) := by
  simp [zeroReportSourceDataFromWindow,
    Theorem2ProcessSourceData.residual,
    Theorem2ProcessSourceData.toProcessKernelCase,
    Theorem2ZeroReportProcessData.toProcessKernelCase,
    Theorem2ZeroReportProcessData.exposure,
    Theorem2ProcessKernelCase.residual]

/--
The ordered one-report window constructor carries exactly the original window
exposure.
-/
theorem oneReportSourceDataFromOrderedWindow_exposure
    (K : Theorem2ConditionFunctions) (baseCount : ℕ)
    {startTime endTime firstJumpTime : ℝ}
    (h_window : startTime < endTime)
    (h_start_le_jump : startTime ≤ firstJumpTime)
    (h_jump_le_end : firstJumpTime ≤ endTime) :
    (K.oneReportSourceDataFromOrderedWindow baseCount
        startTime endTime firstJumpTime h_window
        h_start_le_jump h_jump_le_end).exposure =
      observationExposure startTime endTime := by
  simp [oneReportSourceDataFromOrderedWindow,
    oneReportSourceDataFromOrderedJumpWindow,
    oneReportProcessDataFromOrderedJumpWindow,
    Theorem2ProcessSourceData.exposure,
    Theorem2ProcessSourceData.toProcessKernelCase,
    Theorem2OneReportProcessData.toProcessKernelCase,
    Theorem2OneReportProcessData.exposure,
    Theorem2ProcessKernelCase.exposure,
    OneInterarrivalTailKernel.fromOrderedWindow,
    ObservationWindow.exposure, observationExposure]

/-- The ordered one-report window constructor carries count one. -/
theorem oneReportSourceDataFromOrderedWindow_count
    (K : Theorem2ConditionFunctions) (baseCount : ℕ)
    {startTime endTime firstJumpTime : ℝ}
    (h_window : startTime < endTime)
    (h_start_le_jump : startTime ≤ firstJumpTime)
    (h_jump_le_end : firstJumpTime ≤ endTime) :
    (K.oneReportSourceDataFromOrderedWindow baseCount
        startTime endTime firstJumpTime h_window
        h_start_le_jump h_jump_le_end).count = 1 := by
  simp [oneReportSourceDataFromOrderedWindow,
    oneReportSourceDataFromOrderedJumpWindow,
    oneReportProcessDataFromOrderedJumpWindow,
    Theorem2ProcessSourceData.count,
    Theorem2ProcessSourceData.toProcessKernelCase,
    Theorem2OneReportProcessData.toProcessKernelCase,
    Theorem2ProcessKernelCase.count]

/--
The ordered one-report window constructor carries the corrected one-report
residual, with the observation exposure in the denominator.
-/
theorem oneReportSourceDataFromOrderedWindow_residual
    (K : Theorem2ConditionFunctions) (baseCount : ℕ)
    {startTime endTime firstJumpTime : ℝ}
    (h_window : startTime < endTime)
    (h_start_le_jump : startTime ≤ firstJumpTime)
    (h_jump_le_end : firstJumpTime ≤ endTime) :
    (K.oneReportSourceDataFromOrderedWindow baseCount
        startTime endTime firstJumpTime h_window
        h_start_le_jump h_jump_le_end).residual =
      theorem2OneReportKernelResidual
          K.startDensity (K.endDensity (baseCount + 1))
          (K.survivalIntegral baseCount) /
        observationExposure startTime endTime := by
  simp [oneReportSourceDataFromOrderedWindow,
    oneReportSourceDataFromOrderedJumpWindow,
    oneReportProcessDataFromOrderedJumpWindow,
    Theorem2ProcessSourceData.residual,
    Theorem2ProcessSourceData.toProcessKernelCase,
    Theorem2OneReportProcessData.toProcessKernelCase,
    Theorem2OneReportProcessData.exposure,
    Theorem2ProcessKernelCase.residual,
    OneInterarrivalTailKernel.fromOrderedWindow,
    ObservationWindow.exposure, observationExposure]

/--
The ordered multi-report window constructor carries exactly the original
window exposure.
-/
theorem multiReportSourceDataFromOrderedWindow_exposure
    (K : Theorem2ConditionFunctions) (baseCount count : ℕ)
    (hcount : 1 < count)
    {startTime endTime : ℝ} (jumpTime : ℕ → ℝ)
    (h_window : startTime < endTime)
    (hmono : Monotone (jumpTimelineEndpoint startTime jumpTime))
    (hlast : jumpTimelineEndpoint startTime jumpTime count ≤ endTime) :
    (K.multiReportSourceDataFromOrderedWindow baseCount count hcount
        startTime endTime jumpTime h_window hmono hlast).exposure =
      observationExposure startTime endTime := by
  simp [multiReportSourceDataFromOrderedWindow,
    multiReportSourceDataFromOrderedTimeline,
    multiReportProcessDataFromOrderedTimeline,
    Theorem2ProcessSourceData.exposure,
    Theorem2ProcessSourceData.toProcessKernelCase,
    Theorem2MultiReportProcessData.toProcessKernelCase,
    Theorem2MultiReportProcessData.exposure,
    Theorem2ProcessKernelCase.exposure,
    FinInterarrivalTailKernel.fromOrderedTimeline,
    ObservationWindow.exposure, observationExposure]

/-- The ordered multi-report window constructor carries the supplied count. -/
theorem multiReportSourceDataFromOrderedWindow_count
    (K : Theorem2ConditionFunctions) (baseCount count : ℕ)
    (hcount : 1 < count)
    {startTime endTime : ℝ} (jumpTime : ℕ → ℝ)
    (h_window : startTime < endTime)
    (hmono : Monotone (jumpTimelineEndpoint startTime jumpTime))
    (hlast : jumpTimelineEndpoint startTime jumpTime count ≤ endTime) :
    (K.multiReportSourceDataFromOrderedWindow baseCount count hcount
        startTime endTime jumpTime h_window hmono hlast).count =
      count := by
  simp [multiReportSourceDataFromOrderedWindow,
    multiReportSourceDataFromOrderedTimeline,
    multiReportProcessDataFromOrderedTimeline,
    Theorem2ProcessSourceData.count,
    Theorem2ProcessSourceData.toProcessKernelCase,
    Theorem2MultiReportProcessData.toProcessKernelCase,
    Theorem2ProcessKernelCase.count,
    FinInterarrivalTailKernel.fromOrderedTimeline]

/--
The ordered multi-report window constructor carries the corrected multi-report
residual at the supplied report count and observation exposure.
-/
theorem multiReportSourceDataFromOrderedWindow_residual
    (K : Theorem2ConditionFunctions) (baseCount count : ℕ)
    (hcount : 1 < count)
    {startTime endTime : ℝ} (jumpTime : ℕ → ℝ)
    (h_window : startTime < endTime)
    (hmono : Monotone (jumpTimelineEndpoint startTime jumpTime))
    (hlast : jumpTimelineEndpoint startTime jumpTime count ≤ endTime) :
    (K.multiReportSourceDataFromOrderedWindow baseCount count hcount
        startTime endTime jumpTime h_window hmono hlast).residual =
      theorem2CorrectedResidual
        (theorem2MultiReportKernelResidual
          K.startDensity (K.endDensity (baseCount + count))
          (K.survivalIntegralProduct baseCount count))
        (observationExposure startTime endTime) count := by
  simp [multiReportSourceDataFromOrderedWindow,
    multiReportSourceDataFromOrderedTimeline,
    multiReportProcessDataFromOrderedTimeline,
    Theorem2ProcessSourceData.residual,
    Theorem2ProcessSourceData.toProcessKernelCase,
    Theorem2MultiReportProcessData.toProcessKernelCase,
    Theorem2MultiReportProcessData.exposure,
    Theorem2ProcessKernelCase.residual,
    FinInterarrivalTailKernel.fromOrderedTimeline,
    ObservationWindow.exposure, observationExposure]

end Theorem2ConditionFunctions

/-! ## Rate-Indexed Condition Semantics -/

/--
Rate-indexed source semantics for the Condition 1/2 terms in Appendix B.2.

The paper's stochastic source assumptions say that the conditional start/end
density terms and the survival-integral terms do not depend on the homogeneous
Poisson rate.  This record keeps the rate-indexed source objects visible, with
explicit rate-independence proofs.  The constant `Theorem2ConditionFunctions`
used by the algebraic theorem layer is derived from these fields below.
-/
structure Theorem2ConditionFunctionSemantics where
  startDensityOfRate : ℝ → ℝ
  endDensityOfRate : ℕ → ℝ → ℝ
  survivalIntegralOfRate : ℕ → ℝ → ℝ
  startDensity_rateIndependent :
    RateIndependent startDensityOfRate
  endDensity_rateIndependent :
    ∀ baseCount : ℕ, RateIndependent (endDensityOfRate baseCount)
  survivalIntegral_rateIndependent :
    ∀ baseCount : ℕ, RateIndependent (survivalIntegralOfRate baseCount)

/--
Algebraic fixed-history form of Theorem 2 Condition 1.  It records only the
rate-independence of the evaluated start-density contribution `g(s)`.  A
missing future-path argument cannot itself express independence of the random
start from the post-first-report sample path; that stochastic source premise
is formalized separately in `ConditionOneTail.lean`.
-/
structure Theorem2ConditionOneSource where
  startDensityOfRate : ℝ → ℝ
  startDensity_rateIndependent :
    RateIndependent startDensityOfRate

namespace Theorem2ConditionOneSource

/-- Condition 1 as the rate-indexed condition-semantics start term. -/
def toStartDensityOfRate
    (C : Theorem2ConditionOneSource) : ℝ → ℝ :=
  C.startDensityOfRate

theorem startDensityOfRate_rateIndependent
    (C : Theorem2ConditionOneSource) :
    RateIndependent C.toStartDensityOfRate :=
  C.startDensity_rateIndependent

end Theorem2ConditionOneSource

/--
Source-vocabulary form of Theorem 2 Condition 2 at fixed observed end/jump
realizations.  The paper gives a family `h_m(e)` independent of the Poisson
rate, and additionally states that the end distribution is independent of the
realized start `S = s` given the first jump.  The `endDensityGivenStartOfRate`
field records the start-conditioned version, and
`endDensity_independentOfStart` proves it reduces to the `h_m(e)` term used by
the likelihood algebra.
-/
structure Theorem2ConditionTwoSource where
  endDensityOfRate : ℕ → ℝ → ℝ
  endDensityGivenStartOfRate : ℕ → ℝ → ℝ → ℝ
  survivalIntegralOfRate : ℕ → ℝ → ℝ
  endDensity_independentOfStart :
    ∀ baseCount : ℕ, ∀ startRealization rate : ℝ,
      endDensityGivenStartOfRate baseCount startRealization rate =
        endDensityOfRate baseCount rate
  endDensity_rateIndependent :
    ∀ baseCount : ℕ, RateIndependent (endDensityOfRate baseCount)
  survivalIntegral_rateIndependent :
    ∀ baseCount : ℕ, RateIndependent (survivalIntegralOfRate baseCount)

namespace Theorem2ConditionTwoSource

theorem endDensityGivenStart_rateIndependent
    (C : Theorem2ConditionTwoSource)
    (baseCount : ℕ) (startRealization : ℝ) :
    RateIndependent
      (C.endDensityGivenStartOfRate baseCount startRealization) := by
  rcases C.endDensity_rateIndependent baseCount with ⟨c, hc⟩
  exact
    ⟨c, fun rate => by
      rw [C.endDensity_independentOfStart baseCount startRealization rate]
      exact hc rate⟩

end Theorem2ConditionTwoSource

/--
More concrete Condition 2 source model: a rate-indexed density kernel
`h_m(t)` over possible end times, together with the observed end-time
evaluation and the lower limits used in the paper's survival-integral factors
`∫ h_m(t) dt`.  The scalar Condition 2 source record is derived from this
kernel, which determines the survival terms from the same endpoint-density
family.
-/
structure Theorem2ConditionTwoDensitySource where
  endDensityKernelOfRate : ℕ → ℝ → ℝ → ℝ
  endDensityGivenStartKernelOfRate : ℕ → ℝ → ℝ → ℝ → ℝ
  observedEndTime : ℕ → ℝ
  survivalLower : ℕ → ℝ
  survivalUpper : ℝ
  endDensityKernel_rateInvariant :
    ∀ baseCount : ℕ, ∀ endTime rate : ℝ,
      endDensityKernelOfRate baseCount endTime rate =
        endDensityKernelOfRate baseCount endTime 0
  endDensityGivenStart_independentOfStart :
    ∀ baseCount : ℕ, ∀ startRealization endTime rate : ℝ,
      endDensityGivenStartKernelOfRate
          baseCount startRealization endTime rate =
        endDensityKernelOfRate baseCount endTime rate

namespace Theorem2ConditionTwoDensitySource

/-- The paper's `∫ h_m(t) dt` survival term from the Condition 2 density. -/
noncomputable def survivalIntegralOfRate
    (C : Theorem2ConditionTwoDensitySource)
    (baseCount : ℕ) (rate : ℝ) : ℝ :=
  ∫ endTime in C.survivalLower baseCount..C.survivalUpper,
    C.endDensityKernelOfRate baseCount endTime rate

theorem endDensityKernel_rateIndependent
    (C : Theorem2ConditionTwoDensitySource)
    (baseCount : ℕ) (endTime : ℝ) :
    RateIndependent (C.endDensityKernelOfRate baseCount endTime) := by
  exact
    ⟨C.endDensityKernelOfRate baseCount endTime 0,
      fun rate => C.endDensityKernel_rateInvariant baseCount endTime rate⟩

theorem survivalIntegral_rateIndependent
    (C : Theorem2ConditionTwoDensitySource)
    (baseCount : ℕ) :
    RateIndependent (C.survivalIntegralOfRate baseCount) := by
  refine
    ⟨(∫ endTime in C.survivalLower baseCount..C.survivalUpper,
        C.endDensityKernelOfRate baseCount endTime 0), ?_⟩
  intro rate
  unfold survivalIntegralOfRate
  have hfun :
      (fun endTime : ℝ =>
          C.endDensityKernelOfRate baseCount endTime rate) =
        (fun endTime : ℝ =>
          C.endDensityKernelOfRate baseCount endTime 0) := by
    funext endTime
    exact C.endDensityKernel_rateInvariant baseCount endTime rate
  rw [hfun]

/--
Collapse the density-kernel Condition 2 model to the scalar source model used
by the likelihood factorization layer.
-/
noncomputable def toConditionTwoSource
    (C : Theorem2ConditionTwoDensitySource) :
    Theorem2ConditionTwoSource where
  endDensityOfRate := fun baseCount rate =>
    C.endDensityKernelOfRate baseCount (C.observedEndTime baseCount) rate
  endDensityGivenStartOfRate := fun baseCount startRealization rate =>
    C.endDensityGivenStartKernelOfRate
      baseCount startRealization (C.observedEndTime baseCount) rate
  survivalIntegralOfRate := C.survivalIntegralOfRate
  endDensity_independentOfStart := by
    intro baseCount startRealization rate
    exact
      C.endDensityGivenStart_independentOfStart
        baseCount startRealization (C.observedEndTime baseCount) rate
  endDensity_rateIndependent := by
    intro baseCount
    exact
      C.endDensityKernel_rateIndependent
        baseCount (C.observedEndTime baseCount)
  survivalIntegral_rateIndependent :=
    C.survivalIntegral_rateIndependent

@[simp] theorem toConditionTwoSource_endDensityOfRate
    (C : Theorem2ConditionTwoDensitySource) :
    C.toConditionTwoSource.endDensityOfRate =
      (fun baseCount rate =>
        C.endDensityKernelOfRate baseCount
          (C.observedEndTime baseCount) rate) := rfl

@[simp] theorem toConditionTwoSource_survivalIntegralOfRate
    (C : Theorem2ConditionTwoDensitySource) :
    C.toConditionTwoSource.survivalIntegralOfRate =
      C.survivalIntegralOfRate := rfl

end Theorem2ConditionTwoDensitySource

/--
Paper-source model for the two conditional-distribution assumptions in
Theorem 2.  It is deliberately source-shaped: Condition 1 and Condition 2 are
separate records, and the existing condition-function semantics are derived
from them instead of being passed as unrelated scalars.
-/
structure Theorem2ConditionSourceModel where
  condition1 : Theorem2ConditionOneSource
  condition2 : Theorem2ConditionTwoSource

namespace Theorem2ConditionSourceModel

/--
The rate-indexed condition semantics induced by the source-vocabulary
Condition 1/2 model.
-/
def toConditionFunctionSemantics
    (C : Theorem2ConditionSourceModel) :
    Theorem2ConditionFunctionSemantics where
  startDensityOfRate := C.condition1.startDensityOfRate
  endDensityOfRate := C.condition2.endDensityOfRate
  survivalIntegralOfRate := C.condition2.survivalIntegralOfRate
  startDensity_rateIndependent :=
    C.condition1.startDensity_rateIndependent
  endDensity_rateIndependent :=
    C.condition2.endDensity_rateIndependent
  survivalIntegral_rateIndependent :=
    C.condition2.survivalIntegral_rateIndependent

@[simp] theorem toConditionFunctionSemantics_startDensityOfRate
    (C : Theorem2ConditionSourceModel) :
    C.toConditionFunctionSemantics.startDensityOfRate =
      C.condition1.startDensityOfRate := rfl

@[simp] theorem toConditionFunctionSemantics_endDensityOfRate
    (C : Theorem2ConditionSourceModel) :
    C.toConditionFunctionSemantics.endDensityOfRate =
      C.condition2.endDensityOfRate := rfl

@[simp] theorem toConditionFunctionSemantics_survivalIntegralOfRate
    (C : Theorem2ConditionSourceModel) :
    C.toConditionFunctionSemantics.survivalIntegralOfRate =
      C.condition2.survivalIntegralOfRate := rfl

theorem endDensityGivenStart_eq_conditionSemantics_endDensity
    (C : Theorem2ConditionSourceModel)
    (baseCount : ℕ) (startRealization rate : ℝ) :
    C.condition2.endDensityGivenStartOfRate
        baseCount startRealization rate =
      C.toConditionFunctionSemantics.endDensityOfRate baseCount rate := by
  exact
    C.condition2.endDensity_independentOfStart
      baseCount startRealization rate

/--
Zero-report source data built directly from the source-vocabulary Condition
1/2 model, without passing an abstract condition-function record.
-/
def zeroReportSourceDataFromWindowAtRate
    (C : Theorem2ConditionSourceModel) (baseCount : ℕ)
    (W : ObservationWindow) (rate : ℝ) :
    Theorem2ProcessSourceData :=
  Theorem2ProcessSourceData.zero
    { startDensity := C.condition1.startDensityOfRate rate
      endDensity := C.condition2.endDensityOfRate baseCount rate
      noArrival := NoArrivalKernel.fromWindow W }

/--
One-report source data built directly from the source-vocabulary Condition
1/2 model.
-/
def oneReportSourceDataAtRate
    (C : Theorem2ConditionSourceModel) (baseCount : ℕ)
    (gap tail exposure : ℝ)
    (hexposure : gap + tail = exposure)
    (h_exposure : exposure ≠ 0) (rate : ℝ) :
    Theorem2ProcessSourceData :=
  Theorem2ProcessSourceData.one
    { startDensity := C.condition1.startDensityOfRate rate
      endDensityAfterJump := C.condition2.endDensityOfRate (baseCount + 1) rate
      endSurvivalIntegral := C.condition2.survivalIntegralOfRate baseCount rate
      arrival :=
        { gap := gap
          tail := tail
          exposure := exposure
          exposure_eq := hexposure
          exposure_ne_zero := h_exposure } }

/--
One-report source data from a reusable ordered one-jump window, built
directly from the source-vocabulary Condition 1/2 model.
-/
def oneReportSourceDataFromOrderedJumpWindowAtRate
    (C : Theorem2ConditionSourceModel) (baseCount : ℕ)
    (T : OrderedOneJumpWindow) (h_exposure : T.window.exposure ≠ 0)
    (rate : ℝ) : Theorem2ProcessSourceData :=
  C.oneReportSourceDataAtRate baseCount T.gap T.tail T.window.exposure
    T.exposure_eq h_exposure rate

/--
Multi-report source data built directly from the source-vocabulary Condition
1/2 model.
-/
def multiReportSourceDataAtRate
    (C : Theorem2ConditionSourceModel) (baseCount count : ℕ)
    (hcount : 1 < count)
    (gap : Fin count → ℝ) (tail exposure : ℝ)
    (hexposure : (∑ j : Fin count, gap j) + tail = exposure)
    (h_exposure : exposure ≠ 0) (rate : ℝ) :
    Theorem2ProcessSourceData :=
  Theorem2ProcessSourceData.multi
    { startDensity := C.condition1.startDensityOfRate rate
      endDensityAfterLastJump :=
        C.condition2.endDensityOfRate (baseCount + count) rate
      survivalIntegralProduct :=
        ∏ j : Fin count,
          C.condition2.survivalIntegralOfRate (baseCount + j.val) rate
      arrival :=
        { count := count
          gap := gap
          tail := tail
          exposure := exposure
          exposure_eq := hexposure
          exposure_ne_zero := h_exposure }
      count_gt_one := hcount }

/--
Multi-report source data from a reusable ordered finite-jump timeline, built
directly from the source-vocabulary Condition 1/2 model.
-/
def multiReportSourceDataFromOrderedTimelineAtRate
    (C : Theorem2ConditionSourceModel) (baseCount : ℕ)
    (T : OrderedFiniteJumpTimeline) (hcount : 1 < T.count)
    (h_exposure : T.window.exposure ≠ 0) (rate : ℝ) :
    Theorem2ProcessSourceData :=
  C.multiReportSourceDataAtRate baseCount T.count hcount
    T.gap T.tail T.window.exposure T.exposure_eq h_exposure rate

end Theorem2ConditionSourceModel

/--
Fully source-shaped Condition 1/2 model with Condition 2 represented by an
end-time density kernel.  This is the most explicit source-provenance layer
currently used by the LBG proof: `g(s)` comes from Condition 1, `h_m(e)` is an
evaluation of the Condition 2 density kernel, and each survival term is an
interval integral of that same kernel.
-/
structure Theorem2ConditionDensitySourceModel where
  condition1 : Theorem2ConditionOneSource
  condition2 : Theorem2ConditionTwoDensitySource

namespace Theorem2ConditionDensitySourceModel

/-- Forget only the explicit integral-kernel layer, retaining source semantics. -/
noncomputable def toConditionSourceModel
    (C : Theorem2ConditionDensitySourceModel) :
    Theorem2ConditionSourceModel where
  condition1 := C.condition1
  condition2 := C.condition2.toConditionTwoSource

/-- The rate-indexed condition semantics induced by the density source model. -/
noncomputable def toConditionFunctionSemantics
    (C : Theorem2ConditionDensitySourceModel) :
    Theorem2ConditionFunctionSemantics :=
  C.toConditionSourceModel.toConditionFunctionSemantics

@[simp] theorem toConditionFunctionSemantics_startDensityOfRate
    (C : Theorem2ConditionDensitySourceModel) :
    C.toConditionFunctionSemantics.startDensityOfRate =
      C.condition1.startDensityOfRate := rfl

@[simp] theorem toConditionFunctionSemantics_endDensityOfRate
    (C : Theorem2ConditionDensitySourceModel) :
    C.toConditionFunctionSemantics.endDensityOfRate =
      (fun baseCount rate =>
        C.condition2.endDensityKernelOfRate baseCount
          (C.condition2.observedEndTime baseCount) rate) := rfl

@[simp] theorem toConditionFunctionSemantics_survivalIntegralOfRate
    (C : Theorem2ConditionDensitySourceModel) :
    C.toConditionFunctionSemantics.survivalIntegralOfRate =
      C.condition2.survivalIntegralOfRate := rfl

/--
Zero-report source data built directly from the density-kernel Condition 1/2
source model, with no intermediate abstract condition-function record.
-/
def zeroReportSourceDataFromWindowAtRate
    (C : Theorem2ConditionDensitySourceModel) (baseCount : ℕ)
    (W : ObservationWindow) (rate : ℝ) :
    Theorem2ProcessSourceData :=
  Theorem2ProcessSourceData.zero
    { startDensity := C.condition1.startDensityOfRate rate
      endDensity :=
        C.condition2.endDensityKernelOfRate
          baseCount (C.condition2.observedEndTime baseCount) rate
      noArrival := NoArrivalKernel.fromWindow W }

/--
One-report source data built directly from the density-kernel Condition 1/2
source model.
-/
def oneReportSourceDataAtRate
    (C : Theorem2ConditionDensitySourceModel) (baseCount : ℕ)
    (gap tail exposure : ℝ)
    (hexposure : gap + tail = exposure)
    (h_exposure : exposure ≠ 0) (rate : ℝ) :
    Theorem2ProcessSourceData :=
  Theorem2ProcessSourceData.one
    { startDensity := C.condition1.startDensityOfRate rate
      endDensityAfterJump :=
        C.condition2.endDensityKernelOfRate
          (baseCount + 1) (C.condition2.observedEndTime (baseCount + 1)) rate
      endSurvivalIntegral :=
        C.condition2.survivalIntegralOfRate baseCount rate
      arrival :=
        { gap := gap
          tail := tail
          exposure := exposure
          exposure_eq := hexposure
          exposure_ne_zero := h_exposure } }

/--
One-report source data from a reusable ordered one-jump window, built
directly from the density-kernel Condition 1/2 source model.
-/
def oneReportSourceDataFromOrderedJumpWindowAtRate
    (C : Theorem2ConditionDensitySourceModel) (baseCount : ℕ)
    (T : OrderedOneJumpWindow) (h_exposure : T.window.exposure ≠ 0)
    (rate : ℝ) : Theorem2ProcessSourceData :=
  C.oneReportSourceDataAtRate baseCount T.gap T.tail T.window.exposure
    T.exposure_eq h_exposure rate

/--
Multi-report source data built directly from the density-kernel Condition 1/2
source model.
-/
def multiReportSourceDataAtRate
    (C : Theorem2ConditionDensitySourceModel) (baseCount count : ℕ)
    (hcount : 1 < count)
    (gap : Fin count → ℝ) (tail exposure : ℝ)
    (hexposure : (∑ j : Fin count, gap j) + tail = exposure)
    (h_exposure : exposure ≠ 0) (rate : ℝ) :
    Theorem2ProcessSourceData :=
  Theorem2ProcessSourceData.multi
    { startDensity := C.condition1.startDensityOfRate rate
      endDensityAfterLastJump :=
        C.condition2.endDensityKernelOfRate
          (baseCount + count)
          (C.condition2.observedEndTime (baseCount + count)) rate
      survivalIntegralProduct :=
        ∏ j : Fin count,
          C.condition2.survivalIntegralOfRate (baseCount + j.val) rate
      arrival :=
        { count := count
          gap := gap
          tail := tail
          exposure := exposure
          exposure_eq := hexposure
          exposure_ne_zero := h_exposure }
      count_gt_one := hcount }

/--
Multi-report source data from a reusable ordered finite-jump timeline, built
directly from the density-kernel Condition 1/2 source model.
-/
def multiReportSourceDataFromOrderedTimelineAtRate
    (C : Theorem2ConditionDensitySourceModel) (baseCount : ℕ)
    (T : OrderedFiniteJumpTimeline) (hcount : 1 < T.count)
    (h_exposure : T.window.exposure ≠ 0) (rate : ℝ) :
    Theorem2ProcessSourceData :=
  C.multiReportSourceDataAtRate baseCount T.count hcount
    T.gap T.tail T.window.exposure T.exposure_eq h_exposure rate

end Theorem2ConditionDensitySourceModel

/--
Concrete Condition 1 source term when the paper has already supplied the
fixed `g(s)` value.  The rate-indexed Condition 1 record is derived from this
constant, so rate-independence is checked by reflexivity.
-/
structure Theorem2FixedConditionOneSource where
  startDensity : ℝ

namespace Theorem2FixedConditionOneSource

/-- The fixed Condition 1 value as a rate-indexed source record. -/
def toConditionOneSource
    (C : Theorem2FixedConditionOneSource) :
    Theorem2ConditionOneSource where
  startDensityOfRate := fun _rate => C.startDensity
  startDensity_rateIndependent :=
    ⟨C.startDensity, fun _rate => rfl⟩

@[simp] theorem toConditionOneSource_startDensityOfRate
    (C : Theorem2FixedConditionOneSource) :
    C.toConditionOneSource.startDensityOfRate =
      fun _rate => C.startDensity := rfl

end Theorem2FixedConditionOneSource

/--
Concrete Condition 2 density source when the paper has supplied fixed
`h_m(e)` kernels and the relevant observed/survival integration endpoints.
The rate-indexed density-source record is derived from these kernels, so both
rate-independence and independence from the realized start are checked by
reflexivity.
-/
structure Theorem2FixedConditionTwoDensitySource where
  endDensityKernel : ℕ → ℝ → ℝ
  observedEndTime : ℕ → ℝ
  survivalLower : ℕ → ℝ
  survivalUpper : ℝ

namespace Theorem2FixedConditionTwoDensitySource

/-- The fixed Condition 2 density kernel as a rate-indexed density-source record. -/
noncomputable def toConditionTwoDensitySource
    (C : Theorem2FixedConditionTwoDensitySource) :
    Theorem2ConditionTwoDensitySource where
  endDensityKernelOfRate := fun baseCount endTime _rate =>
    C.endDensityKernel baseCount endTime
  endDensityGivenStartKernelOfRate := fun baseCount _startRealization endTime _rate =>
    C.endDensityKernel baseCount endTime
  observedEndTime := C.observedEndTime
  survivalLower := C.survivalLower
  survivalUpper := C.survivalUpper
  endDensityKernel_rateInvariant := by
    intro baseCount endTime rate
    rfl
  endDensityGivenStart_independentOfStart := by
    intro baseCount startRealization endTime rate
    rfl

@[simp] theorem toConditionTwoDensitySource_endDensityKernelOfRate
    (C : Theorem2FixedConditionTwoDensitySource) :
    C.toConditionTwoDensitySource.endDensityKernelOfRate =
      fun baseCount endTime _rate => C.endDensityKernel baseCount endTime := rfl

@[simp] theorem toConditionTwoDensitySource_observedEndTime
    (C : Theorem2FixedConditionTwoDensitySource) :
    C.toConditionTwoDensitySource.observedEndTime = C.observedEndTime := rfl

@[simp] theorem toConditionTwoDensitySource_survivalLower
    (C : Theorem2FixedConditionTwoDensitySource) :
    C.toConditionTwoDensitySource.survivalLower = C.survivalLower := rfl

@[simp] theorem toConditionTwoDensitySource_survivalUpper
    (C : Theorem2FixedConditionTwoDensitySource) :
    C.toConditionTwoDensitySource.survivalUpper = C.survivalUpper := rfl

end Theorem2FixedConditionTwoDensitySource

/--
Most concrete current source model for the paper's Condition 1/2 terms:
Condition 1 is a fixed `g(s)` value and Condition 2 is a fixed `h_m(e)`
density kernel with observed/integration endpoints.  It constructs the
rate-indexed density-source model used by the theorem layer.
-/
structure Theorem2FixedConditionDensitySourceModel where
  condition1 : Theorem2FixedConditionOneSource
  condition2 : Theorem2FixedConditionTwoDensitySource

namespace Theorem2FixedConditionDensitySourceModel

/-- Convert fixed paper Condition 1/2 functions to the density-source model. -/
noncomputable def toConditionDensitySourceModel
    (C : Theorem2FixedConditionDensitySourceModel) :
    Theorem2ConditionDensitySourceModel where
  condition1 := C.condition1.toConditionOneSource
  condition2 := C.condition2.toConditionTwoDensitySource

/-- The induced rate-indexed condition semantics. -/
noncomputable def toConditionFunctionSemantics
    (C : Theorem2FixedConditionDensitySourceModel) :
    Theorem2ConditionFunctionSemantics :=
  C.toConditionDensitySourceModel.toConditionFunctionSemantics

@[simp] theorem toConditionDensitySourceModel_condition1
    (C : Theorem2FixedConditionDensitySourceModel) :
    C.toConditionDensitySourceModel.condition1 =
      C.condition1.toConditionOneSource := rfl

@[simp] theorem toConditionDensitySourceModel_condition2
    (C : Theorem2FixedConditionDensitySourceModel) :
    C.toConditionDensitySourceModel.condition2 =
      C.condition2.toConditionTwoDensitySource := rfl

@[simp] theorem toConditionFunctionSemantics_startDensityOfRate
    (C : Theorem2FixedConditionDensitySourceModel) :
    C.toConditionFunctionSemantics.startDensityOfRate =
      fun _rate => C.condition1.startDensity := rfl

@[simp] theorem toConditionFunctionSemantics_endDensityOfRate
    (C : Theorem2FixedConditionDensitySourceModel) :
    C.toConditionFunctionSemantics.endDensityOfRate =
      fun baseCount _rate =>
        C.condition2.endDensityKernel baseCount
          (C.condition2.observedEndTime baseCount) := rfl

@[simp] theorem toConditionFunctionSemantics_survivalIntegralOfRate
    (C : Theorem2FixedConditionDensitySourceModel) :
    C.toConditionFunctionSemantics.survivalIntegralOfRate =
      fun baseCount rate =>
        C.condition2.toConditionTwoDensitySource.survivalIntegralOfRate
          baseCount rate := rfl

end Theorem2FixedConditionDensitySourceModel

namespace Theorem2ConditionFunctionSemantics

/--
Condition functions obtained by choosing the rate-independent constants from
the rate-indexed source semantics.
-/
noncomputable def toConditionFunctions
    (S : Theorem2ConditionFunctionSemantics) :
    Theorem2ConditionFunctions :=
  { startDensity :=
      Classical.choose S.startDensity_rateIndependent
    endDensity := fun baseCount =>
      Classical.choose (S.endDensity_rateIndependent baseCount)
    survivalIntegral := fun baseCount =>
      Classical.choose (S.survivalIntegral_rateIndependent baseCount) }

theorem startDensityOfRate_eq
    (S : Theorem2ConditionFunctionSemantics) (rate : ℝ) :
    S.startDensityOfRate rate = S.toConditionFunctions.startDensity :=
  Classical.choose_spec S.startDensity_rateIndependent rate

theorem endDensityOfRate_eq
    (S : Theorem2ConditionFunctionSemantics)
    (baseCount : ℕ) (rate : ℝ) :
    S.endDensityOfRate baseCount rate =
      S.toConditionFunctions.endDensity baseCount :=
  Classical.choose_spec (S.endDensity_rateIndependent baseCount) rate

theorem survivalIntegralOfRate_eq
    (S : Theorem2ConditionFunctionSemantics)
    (baseCount : ℕ) (rate : ℝ) :
    S.survivalIntegralOfRate baseCount rate =
      S.toConditionFunctions.survivalIntegral baseCount :=
  Classical.choose_spec (S.survivalIntegral_rateIndependent baseCount) rate

theorem toConditionFunctions_startDensity_rateIndependent
    (S : Theorem2ConditionFunctionSemantics) :
    RateIndependent (fun _rate : ℝ =>
      S.toConditionFunctions.startDensity) := by
  exact ⟨S.toConditionFunctions.startDensity, fun _ => rfl⟩

theorem toConditionFunctions_endDensity_rateIndependent
    (S : Theorem2ConditionFunctionSemantics) (baseCount : ℕ) :
    RateIndependent (fun _rate : ℝ =>
      S.toConditionFunctions.endDensity baseCount) := by
  exact ⟨S.toConditionFunctions.endDensity baseCount, fun _ => rfl⟩

theorem toConditionFunctions_survivalIntegral_rateIndependent
    (S : Theorem2ConditionFunctionSemantics) (baseCount : ℕ) :
    RateIndependent (fun _rate : ℝ =>
      S.toConditionFunctions.survivalIntegral baseCount) := by
  exact ⟨S.toConditionFunctions.survivalIntegral baseCount, fun _ => rfl⟩

/--
Zero-report source data using the rate-indexed Condition 1/2 terms at a
specific Poisson rate.
-/
def zeroReportSourceDataFromWindowAtRate
    (S : Theorem2ConditionFunctionSemantics) (baseCount : ℕ)
    (W : ObservationWindow) (rate : ℝ) :
    Theorem2ProcessSourceData :=
  Theorem2ProcessSourceData.zero
    { startDensity := S.startDensityOfRate rate
      endDensity := S.endDensityOfRate baseCount rate
      noArrival := NoArrivalKernel.fromWindow W }

theorem zeroReportSourceDataFromWindowAtRate_eq
    (S : Theorem2ConditionFunctionSemantics) (baseCount : ℕ)
    (W : ObservationWindow) (rate : ℝ) :
    S.zeroReportSourceDataFromWindowAtRate baseCount W rate =
      S.toConditionFunctions.zeroReportSourceDataFromWindow baseCount W := by
  simp [zeroReportSourceDataFromWindowAtRate,
    Theorem2ConditionFunctions.zeroReportSourceDataFromWindow,
    S.startDensityOfRate_eq rate,
    S.endDensityOfRate_eq baseCount rate]

/--
One-report source data using the rate-indexed Condition 1/2 terms at a
specific Poisson rate.
-/
def oneReportSourceDataAtRate
    (S : Theorem2ConditionFunctionSemantics) (baseCount : ℕ)
    (gap tail exposure : ℝ)
    (hexposure : gap + tail = exposure)
    (h_exposure : exposure ≠ 0) (rate : ℝ) :
    Theorem2ProcessSourceData :=
  Theorem2ProcessSourceData.one
    { startDensity := S.startDensityOfRate rate
      endDensityAfterJump := S.endDensityOfRate (baseCount + 1) rate
      endSurvivalIntegral := S.survivalIntegralOfRate baseCount rate
      arrival :=
        { gap := gap
          tail := tail
          exposure := exposure
          exposure_eq := hexposure
          exposure_ne_zero := h_exposure } }

theorem oneReportSourceDataAtRate_eq
    (S : Theorem2ConditionFunctionSemantics) (baseCount : ℕ)
    (gap tail exposure : ℝ)
    (hexposure : gap + tail = exposure)
    (h_exposure : exposure ≠ 0) (rate : ℝ) :
    S.oneReportSourceDataAtRate baseCount gap tail exposure
        hexposure h_exposure rate =
      S.toConditionFunctions.oneReportSourceData baseCount
        gap tail exposure hexposure h_exposure := by
  simp [oneReportSourceDataAtRate,
    Theorem2ConditionFunctions.oneReportSourceData,
    S.startDensityOfRate_eq rate,
    S.endDensityOfRate_eq (baseCount + 1) rate,
    S.survivalIntegralOfRate_eq baseCount rate]

/--
One-report source data from a reusable ordered one-jump window, using the
rate-indexed Condition 1/2 terms at a specific Poisson rate.
-/
def oneReportSourceDataFromOrderedJumpWindowAtRate
    (S : Theorem2ConditionFunctionSemantics) (baseCount : ℕ)
    (T : OrderedOneJumpWindow) (h_exposure : T.window.exposure ≠ 0)
    (rate : ℝ) : Theorem2ProcessSourceData :=
  S.oneReportSourceDataAtRate baseCount T.gap T.tail T.window.exposure
    T.exposure_eq h_exposure rate

theorem oneReportSourceDataFromOrderedJumpWindowAtRate_eq
    (S : Theorem2ConditionFunctionSemantics) (baseCount : ℕ)
    (T : OrderedOneJumpWindow) (h_exposure : T.window.exposure ≠ 0)
    (rate : ℝ) :
    S.oneReportSourceDataFromOrderedJumpWindowAtRate
        baseCount T h_exposure rate =
      S.toConditionFunctions.oneReportSourceDataFromOrderedJumpWindow
        baseCount T h_exposure := by
  simpa [oneReportSourceDataFromOrderedJumpWindowAtRate,
    Theorem2ConditionFunctions.oneReportSourceDataFromOrderedJumpWindow,
    Theorem2ConditionFunctions.oneReportProcessDataFromOrderedJumpWindow,
    Theorem2ConditionFunctions.oneReportSourceData,
    OneInterarrivalTailKernel.fromOrderedWindow] using
      S.oneReportSourceDataAtRate_eq
        baseCount T.gap T.tail T.window.exposure
        T.exposure_eq h_exposure rate

/--
Multi-report source data using the rate-indexed Condition 1/2 terms at a
specific Poisson rate.
-/
def multiReportSourceDataAtRate
    (S : Theorem2ConditionFunctionSemantics) (baseCount count : ℕ)
    (hcount : 1 < count)
    (gap : Fin count → ℝ) (tail exposure : ℝ)
    (hexposure : (∑ j : Fin count, gap j) + tail = exposure)
    (h_exposure : exposure ≠ 0) (rate : ℝ) :
    Theorem2ProcessSourceData :=
  Theorem2ProcessSourceData.multi
    { startDensity := S.startDensityOfRate rate
      endDensityAfterLastJump := S.endDensityOfRate (baseCount + count) rate
      survivalIntegralProduct :=
        ∏ j : Fin count,
          S.survivalIntegralOfRate (baseCount + j.val) rate
      arrival :=
        { count := count
          gap := gap
          tail := tail
          exposure := exposure
          exposure_eq := hexposure
          exposure_ne_zero := h_exposure }
      count_gt_one := hcount }

theorem survivalIntegralProduct_atRate_eq
    (S : Theorem2ConditionFunctionSemantics)
    (baseCount count : ℕ) (rate : ℝ) :
    (∏ j : Fin count,
        S.survivalIntegralOfRate (baseCount + j.val) rate) =
      S.toConditionFunctions.survivalIntegralProduct
        baseCount count := by
  simp [Theorem2ConditionFunctions.survivalIntegralProduct,
    S.survivalIntegralOfRate_eq]

theorem multiReportSourceDataAtRate_eq
    (S : Theorem2ConditionFunctionSemantics) (baseCount count : ℕ)
    (hcount : 1 < count)
    (gap : Fin count → ℝ) (tail exposure : ℝ)
    (hexposure : (∑ j : Fin count, gap j) + tail = exposure)
    (h_exposure : exposure ≠ 0) (rate : ℝ) :
    S.multiReportSourceDataAtRate baseCount count hcount gap tail exposure
        hexposure h_exposure rate =
      S.toConditionFunctions.multiReportSourceData baseCount count hcount
        gap tail exposure hexposure h_exposure := by
  simp [multiReportSourceDataAtRate,
    Theorem2ConditionFunctions.multiReportSourceData,
    survivalIntegralProduct_atRate_eq,
    S.startDensityOfRate_eq rate,
    S.endDensityOfRate_eq (baseCount + count) rate]

/--
Multi-report source data from a reusable ordered finite-jump timeline, using
the rate-indexed Condition 1/2 terms at a specific Poisson rate.
-/
def multiReportSourceDataFromOrderedTimelineAtRate
    (S : Theorem2ConditionFunctionSemantics) (baseCount : ℕ)
    (T : OrderedFiniteJumpTimeline) (hcount : 1 < T.count)
    (h_exposure : T.window.exposure ≠ 0) (rate : ℝ) :
    Theorem2ProcessSourceData :=
  S.multiReportSourceDataAtRate baseCount T.count hcount
    T.gap T.tail T.window.exposure T.exposure_eq h_exposure rate

theorem multiReportSourceDataFromOrderedTimelineAtRate_eq
    (S : Theorem2ConditionFunctionSemantics) (baseCount : ℕ)
    (T : OrderedFiniteJumpTimeline) (hcount : 1 < T.count)
    (h_exposure : T.window.exposure ≠ 0) (rate : ℝ) :
    S.multiReportSourceDataFromOrderedTimelineAtRate
        baseCount T hcount h_exposure rate =
      S.toConditionFunctions.multiReportSourceDataFromOrderedTimeline
        baseCount T hcount h_exposure := by
  simpa [multiReportSourceDataFromOrderedTimelineAtRate,
    Theorem2ConditionFunctions.multiReportSourceDataFromOrderedTimeline,
    Theorem2ConditionFunctions.multiReportProcessDataFromOrderedTimeline,
    Theorem2ConditionFunctions.multiReportSourceData,
    FinInterarrivalTailKernel.fromOrderedTimeline] using
      S.multiReportSourceDataAtRate_eq
        baseCount T.count hcount T.gap T.tail T.window.exposure
        T.exposure_eq h_exposure rate

end Theorem2ConditionFunctionSemantics

namespace Theorem2ConditionSourceModel

@[simp] theorem zeroReportSourceDataFromWindowAtRate_eq_conditionSemantics
    (C : Theorem2ConditionSourceModel) (baseCount : ℕ)
    (W : ObservationWindow) (rate : ℝ) :
    C.zeroReportSourceDataFromWindowAtRate baseCount W rate =
      C.toConditionFunctionSemantics.zeroReportSourceDataFromWindowAtRate
        baseCount W rate := rfl

@[simp] theorem oneReportSourceDataAtRate_eq_conditionSemantics
    (C : Theorem2ConditionSourceModel) (baseCount : ℕ)
    (gap tail exposure : ℝ)
    (hexposure : gap + tail = exposure)
    (h_exposure : exposure ≠ 0) (rate : ℝ) :
    C.oneReportSourceDataAtRate baseCount gap tail exposure
        hexposure h_exposure rate =
      C.toConditionFunctionSemantics.oneReportSourceDataAtRate
        baseCount gap tail exposure hexposure h_exposure rate := rfl

@[simp] theorem oneReportSourceDataFromOrderedJumpWindowAtRate_eq_conditionSemantics
    (C : Theorem2ConditionSourceModel) (baseCount : ℕ)
    (T : OrderedOneJumpWindow) (h_exposure : T.window.exposure ≠ 0)
    (rate : ℝ) :
    C.oneReportSourceDataFromOrderedJumpWindowAtRate
        baseCount T h_exposure rate =
      C.toConditionFunctionSemantics.oneReportSourceDataFromOrderedJumpWindowAtRate
        baseCount T h_exposure rate := rfl

@[simp] theorem multiReportSourceDataAtRate_eq_conditionSemantics
    (C : Theorem2ConditionSourceModel) (baseCount count : ℕ)
    (hcount : 1 < count)
    (gap : Fin count → ℝ) (tail exposure : ℝ)
    (hexposure : (∑ j : Fin count, gap j) + tail = exposure)
    (h_exposure : exposure ≠ 0) (rate : ℝ) :
    C.multiReportSourceDataAtRate baseCount count hcount gap tail exposure
        hexposure h_exposure rate =
      C.toConditionFunctionSemantics.multiReportSourceDataAtRate
        baseCount count hcount gap tail exposure hexposure h_exposure rate := rfl

@[simp] theorem multiReportSourceDataFromOrderedTimelineAtRate_eq_conditionSemantics
    (C : Theorem2ConditionSourceModel) (baseCount : ℕ)
    (T : OrderedFiniteJumpTimeline) (hcount : 1 < T.count)
    (h_exposure : T.window.exposure ≠ 0) (rate : ℝ) :
    C.multiReportSourceDataFromOrderedTimelineAtRate
        baseCount T hcount h_exposure rate =
      C.toConditionFunctionSemantics.multiReportSourceDataFromOrderedTimelineAtRate
        baseCount T hcount h_exposure rate := rfl

end Theorem2ConditionSourceModel

namespace Theorem2ConditionDensitySourceModel

@[simp] theorem zeroReportSourceDataFromWindowAtRate_eq_conditionSemantics
    (C : Theorem2ConditionDensitySourceModel) (baseCount : ℕ)
    (W : ObservationWindow) (rate : ℝ) :
    C.zeroReportSourceDataFromWindowAtRate baseCount W rate =
      C.toConditionFunctionSemantics.zeroReportSourceDataFromWindowAtRate
        baseCount W rate := rfl

@[simp] theorem oneReportSourceDataAtRate_eq_conditionSemantics
    (C : Theorem2ConditionDensitySourceModel) (baseCount : ℕ)
    (gap tail exposure : ℝ)
    (hexposure : gap + tail = exposure)
    (h_exposure : exposure ≠ 0) (rate : ℝ) :
    C.oneReportSourceDataAtRate baseCount gap tail exposure
        hexposure h_exposure rate =
      C.toConditionFunctionSemantics.oneReportSourceDataAtRate
        baseCount gap tail exposure hexposure h_exposure rate := rfl

@[simp] theorem oneReportSourceDataFromOrderedJumpWindowAtRate_eq_conditionSemantics
    (C : Theorem2ConditionDensitySourceModel) (baseCount : ℕ)
    (T : OrderedOneJumpWindow) (h_exposure : T.window.exposure ≠ 0)
    (rate : ℝ) :
    C.oneReportSourceDataFromOrderedJumpWindowAtRate
        baseCount T h_exposure rate =
      C.toConditionFunctionSemantics.oneReportSourceDataFromOrderedJumpWindowAtRate
        baseCount T h_exposure rate := rfl

@[simp] theorem multiReportSourceDataAtRate_eq_conditionSemantics
    (C : Theorem2ConditionDensitySourceModel) (baseCount count : ℕ)
    (hcount : 1 < count)
    (gap : Fin count → ℝ) (tail exposure : ℝ)
    (hexposure : (∑ j : Fin count, gap j) + tail = exposure)
    (h_exposure : exposure ≠ 0) (rate : ℝ) :
    C.multiReportSourceDataAtRate baseCount count hcount gap tail exposure
        hexposure h_exposure rate =
      C.toConditionFunctionSemantics.multiReportSourceDataAtRate
        baseCount count hcount gap tail exposure hexposure h_exposure rate := rfl

@[simp] theorem multiReportSourceDataFromOrderedTimelineAtRate_eq_conditionSemantics
    (C : Theorem2ConditionDensitySourceModel) (baseCount : ℕ)
    (T : OrderedFiniteJumpTimeline) (hcount : 1 < T.count)
    (h_exposure : T.window.exposure ≠ 0) (rate : ℝ) :
    C.multiReportSourceDataFromOrderedTimelineAtRate
        baseCount T hcount h_exposure rate =
      C.toConditionFunctionSemantics.multiReportSourceDataFromOrderedTimelineAtRate
        baseCount T hcount h_exposure rate := rfl

end Theorem2ConditionDensitySourceModel

namespace Theorem2ConditionFunctions

/--
Rate-indexed condition semantics generated by rate-independent condition
functions.  This is the canonical way to view the paper's `g`, `h_m`, and
survival-integral terms as source semantics when those terms have already been
proved or assumed independent of the Poisson rate.
-/
def toConditionFunctionSemantics
    (K : Theorem2ConditionFunctions) :
    Theorem2ConditionFunctionSemantics where
  startDensityOfRate := fun _rate => K.startDensity
  endDensityOfRate := fun baseCount _rate => K.endDensity baseCount
  survivalIntegralOfRate := fun baseCount _rate =>
    K.survivalIntegral baseCount
  startDensity_rateIndependent :=
    ⟨K.startDensity, fun _ => rfl⟩
  endDensity_rateIndependent := fun baseCount =>
    ⟨K.endDensity baseCount, fun _ => rfl⟩
  survivalIntegral_rateIndependent := fun baseCount =>
    ⟨K.survivalIntegral baseCount, fun _ => rfl⟩

theorem toConditionFunctionSemantics_toConditionFunctions
    (K : Theorem2ConditionFunctions) :
    K.toConditionFunctionSemantics.toConditionFunctions = K := by
  cases K
  simp [toConditionFunctionSemantics,
    Theorem2ConditionFunctionSemantics.toConditionFunctions]

end Theorem2ConditionFunctions

/-! ## Source-Data Likelihood Decomposition Before Poisson-PMF Collection -/

theorem theorem2_one_report_process_data_likelihood_eq_arrival_kernel
    (D : Theorem2OneReportProcessData) (rate : ℝ) :
    (Theorem2ProcessSourceData.one D).likelihood rate =
      theorem2OneReportKernelResidual
          D.startDensity D.endDensityAfterJump D.endSurvivalIntegral *
        D.arrival.likelihood rate := by
  simp [Theorem2ProcessSourceData.likelihood,
    Theorem2ProcessSourceData.toProcessKernelCase,
    Theorem2OneReportProcessData.toProcessKernelCase,
    Theorem2ProcessKernelCase.likelihood,
    theorem2OneReportProcessKernelLikelihood,
    OneInterarrivalTailKernel.likelihood]
  ring

theorem theorem2_one_report_process_data_likelihood_eq_exponential_pdf_tail
    (D : Theorem2OneReportProcessData) (rate : ℝ) (h_rate : 0 < rate)
    (h_gap : 0 ≤ D.arrival.gap) (h_tail : 0 ≤ D.arrival.tail) :
    (Theorem2ProcessSourceData.one D).likelihood rate =
      theorem2OneReportKernelResidual
          D.startDensity D.endDensityAfterJump D.endSurvivalIntegral *
        ((AppliedModelingLib.Probability.Exponential.Model.mk rate h_rate).pdfReal
            D.arrival.gap *
          ((AppliedModelingLib.Probability.Exponential.Model.mk rate h_rate).measure
            (Set.Ioi D.arrival.tail)).toReal) := by
  rw [theorem2_one_report_process_data_likelihood_eq_arrival_kernel]
  rw [D.arrival.likelihood_eq_exponential_pdfReal_mul_tail
    rate h_rate h_gap h_tail]

theorem theorem2_multi_report_process_data_likelihood_eq_arrival_kernel
    (D : Theorem2MultiReportProcessData) (rate : ℝ) :
    (Theorem2ProcessSourceData.multi D).likelihood rate =
      theorem2MultiReportKernelResidual
          D.startDensity D.endDensityAfterLastJump
          D.survivalIntegralProduct *
        D.arrival.likelihood rate := by
  simp [Theorem2ProcessSourceData.likelihood,
    Theorem2ProcessSourceData.toProcessKernelCase,
    Theorem2MultiReportProcessData.toProcessKernelCase,
    Theorem2ProcessKernelCase.likelihood,
    theorem2MultiReportProcessKernelLikelihood,
    theorem2InterarrivalTailLikelihood,
    FinInterarrivalTailKernel.likelihood]

theorem theorem2_multi_report_process_data_likelihood_eq_exponential_pdf_tail
    (D : Theorem2MultiReportProcessData) (rate : ℝ) (h_rate : 0 < rate)
    (h_gap : ∀ j : Fin D.arrival.count, 0 ≤ D.arrival.gap j)
    (h_tail : 0 ≤ D.arrival.tail) :
    (Theorem2ProcessSourceData.multi D).likelihood rate =
      theorem2MultiReportKernelResidual
          D.startDensity D.endDensityAfterLastJump
          D.survivalIntegralProduct *
        ((∏ j : Fin D.arrival.count,
            (AppliedModelingLib.Probability.Exponential.Model.mk rate h_rate).pdfReal
              (D.arrival.gap j)) *
          ((AppliedModelingLib.Probability.Exponential.Model.mk rate h_rate).measure
            (Set.Ioi D.arrival.tail)).toReal) := by
  rw [theorem2_multi_report_process_data_likelihood_eq_arrival_kernel]
  rw [D.arrival.likelihood_eq_exponential_pdfReal_prod_mul_tail
    rate h_rate h_gap h_tail]

/--
Unified Appendix B.2 process-kernel factorization.  This starts from the
source-shaped no-arrival/interarrival density kernels and proves the Poisson
count-PMF factorization with the corrected residual.
-/
theorem theorem2_process_kernel_case_factorization
    (C : Theorem2ProcessKernelCase) (rate : ℝ) :
    C.likelihood rate =
      C.residual * sourcePoissonPMF rate C.exposure C.count := by
  cases C with
  | zero startDensity endDensity exposure =>
      simpa [Theorem2ProcessKernelCase.likelihood,
        Theorem2ProcessKernelCase.residual,
        Theorem2ProcessKernelCase.exposure,
        Theorem2ProcessKernelCase.count] using
          theorem2_zero_report_process_kernel_factorization
            startDensity endDensity rate exposure
  | one startDensity endDensityAfterJump endSurvivalIntegral gap tail exposure
      hexposure h_exposure =>
      simpa [Theorem2ProcessKernelCase.likelihood,
        Theorem2ProcessKernelCase.residual,
        Theorem2ProcessKernelCase.exposure,
        Theorem2ProcessKernelCase.count] using
          theorem2_one_report_process_kernel_factorization
            (startDensity := startDensity)
            (endDensityAfterJump := endDensityAfterJump)
            (endSurvivalIntegral := endSurvivalIntegral)
            (rate := rate) (gap := gap) (tail := tail)
            (exposure := exposure) hexposure h_exposure
  | multi startDensity endDensityAfterLastJump survivalIntegralProduct
      exposure tail reportCount hcount gap hexposure h_exposure =>
      have hcard : (Finset.univ : Finset (Fin reportCount)).card = reportCount := by
        simp
      have hexposure' :
          (∑ j ∈ (Finset.univ : Finset (Fin reportCount)), gap j) + tail =
            exposure := by
        simpa using hexposure
      have hcase := theorem2_multi_report_process_kernel_factorization
        (jumps := (Finset.univ : Finset (Fin reportCount)))
        (startDensity := startDensity)
        (endDensityAfterLastJump := endDensityAfterLastJump)
        (survivalIntegralProduct := survivalIntegralProduct)
        (rate := rate) (exposure := exposure) (tail := tail)
        (count := reportCount) gap hcard hexposure' hcount h_exposure
      simpa [Theorem2ProcessKernelCase.likelihood,
        Theorem2ProcessKernelCase.residual,
        Theorem2ProcessKernelCase.exposure,
        Theorem2ProcessKernelCase.count] using hcase.2

/-- Convert a checked process-kernel case into the reusable likelihood certificate. -/
def theorem2ProcessKernelCasePoissonFactorization
    (C : Theorem2ProcessKernelCase) : PoissonLikelihoodFactorization where
  likelihood := C.likelihood
  residual := C.residual
  exposure := C.exposure
  count := C.count
  factorized := theorem2_process_kernel_case_factorization C

/--
Unified Appendix B.2 factorization from source-kernel data built out of the
reusable Poisson no-arrival and interarrival-tail kernels.
-/
theorem theorem2_process_source_data_factorization
    (D : Theorem2ProcessSourceData) (rate : ℝ) :
    D.likelihood rate =
      D.residual * sourcePoissonPMF rate D.exposure D.count := by
  exact D.factorization_via_arrivalKernelCase rate

namespace Theorem2ConditionFunctionSemantics

/--
Zero-report source data built from rate-indexed Condition 1/2 terms factors
directly into its own residual and zero-count Poisson PMF.
-/
theorem zeroReportSourceDataFromWindowAtRate_self_factorization
    (S : Theorem2ConditionFunctionSemantics) (baseCount : ℕ)
    (W : ObservationWindow) (rate : ℝ) :
    (S.zeroReportSourceDataFromWindowAtRate baseCount W rate).likelihood rate =
      (S.zeroReportSourceDataFromWindowAtRate baseCount W rate).residual *
        sourcePoissonPMF rate
          (S.zeroReportSourceDataFromWindowAtRate baseCount W rate).exposure
          (S.zeroReportSourceDataFromWindowAtRate baseCount W rate).count := by
  exact theorem2_process_source_data_factorization
    (S.zeroReportSourceDataFromWindowAtRate baseCount W rate) rate

theorem zeroReportSourceDataFromWindowAtRate_factorization
    (S : Theorem2ConditionFunctionSemantics) (baseCount : ℕ)
    (W : ObservationWindow) (rate : ℝ) :
    (S.zeroReportSourceDataFromWindowAtRate baseCount W rate).likelihood rate =
      (S.toConditionFunctions.zeroReportSourceDataFromWindow
          baseCount W).residual *
        sourcePoissonPMF rate
          (S.toConditionFunctions.zeroReportSourceDataFromWindow
            baseCount W).exposure
          (S.toConditionFunctions.zeroReportSourceDataFromWindow
            baseCount W).count := by
  rw [S.zeroReportSourceDataFromWindowAtRate_eq baseCount W rate]
  exact theorem2_process_source_data_factorization
    (S.toConditionFunctions.zeroReportSourceDataFromWindow baseCount W) rate

/--
One-report source data built from rate-indexed Condition 1/2 terms factors
directly into its own residual and one-count Poisson PMF.
-/
theorem oneReportSourceDataAtRate_self_factorization
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
  exact theorem2_process_source_data_factorization
    (S.oneReportSourceDataAtRate baseCount gap tail exposure
      hexposure h_exposure rate) rate

/--
One-report at-rate source-data self-factorization with nonzero exposure
derived from positive exposure.
-/
theorem oneReportSourceDataAtRate_self_factorization_of_pos_exposure
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
  exact oneReportSourceDataAtRate_self_factorization
    S baseCount hexposure (ne_of_gt h_exposure_pos)

theorem oneReportSourceDataAtRate_factorization
    (S : Theorem2ConditionFunctionSemantics) (baseCount : ℕ)
    {gap tail exposure rate : ℝ}
    (hexposure : gap + tail = exposure)
    (h_exposure : exposure ≠ 0) :
    (S.oneReportSourceDataAtRate baseCount gap tail exposure
        hexposure h_exposure rate).likelihood rate =
      (S.toConditionFunctions.oneReportSourceData baseCount
          gap tail exposure hexposure h_exposure).residual *
        sourcePoissonPMF rate
          (S.toConditionFunctions.oneReportSourceData baseCount
            gap tail exposure hexposure h_exposure).exposure
          (S.toConditionFunctions.oneReportSourceData baseCount
            gap tail exposure hexposure h_exposure).count := by
  rw [S.oneReportSourceDataAtRate_eq
    baseCount gap tail exposure hexposure h_exposure rate]
  exact theorem2_process_source_data_factorization
    (S.toConditionFunctions.oneReportSourceData baseCount
      gap tail exposure hexposure h_exposure) rate

/--
One-report at-rate source-data factorization through the derived
rate-independent condition functions, with nonzero exposure derived from
positive exposure.
-/
theorem oneReportSourceDataAtRate_factorization_of_pos_exposure
    (S : Theorem2ConditionFunctionSemantics) (baseCount : ℕ)
    {gap tail exposure rate : ℝ}
    (hexposure : gap + tail = exposure)
    (h_exposure_pos : 0 < exposure) :
    (S.oneReportSourceDataAtRate baseCount gap tail exposure
        hexposure (ne_of_gt h_exposure_pos) rate).likelihood rate =
      (S.toConditionFunctions.oneReportSourceData baseCount
          gap tail exposure hexposure (ne_of_gt h_exposure_pos)).residual *
        sourcePoissonPMF rate
          (S.toConditionFunctions.oneReportSourceData baseCount
            gap tail exposure hexposure (ne_of_gt h_exposure_pos)).exposure
          (S.toConditionFunctions.oneReportSourceData baseCount
            gap tail exposure hexposure (ne_of_gt h_exposure_pos)).count := by
  exact oneReportSourceDataAtRate_factorization
    S baseCount hexposure (ne_of_gt h_exposure_pos)

/--
One-report ordered-window source data built from rate-indexed Condition 1/2
terms factors directly into its own residual and one-count Poisson PMF.
-/
theorem oneReportSourceDataFromOrderedJumpWindowAtRate_self_factorization
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
  exact theorem2_process_source_data_factorization
    (S.oneReportSourceDataFromOrderedJumpWindowAtRate
      baseCount T h_exposure rate) rate

/--
One-report ordered-window source data built from rate-indexed Condition 1/2
terms agrees with the derived rate-independent condition-function source data
and therefore has the same factorization.
-/
theorem oneReportSourceDataFromOrderedJumpWindowAtRate_factorization
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
  rw [S.oneReportSourceDataFromOrderedJumpWindowAtRate_eq
    baseCount T h_exposure rate]
  exact theorem2_process_source_data_factorization
    (S.toConditionFunctions.oneReportSourceDataFromOrderedJumpWindow
      baseCount T h_exposure) rate

/--
One-report ordered-window source-data factorization with nonzero exposure
derived from positive window exposure.
-/
theorem oneReportSourceDataFromOrderedJumpWindowAtRate_factorization_of_pos_exposure
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
  exact S.oneReportSourceDataFromOrderedJumpWindowAtRate_factorization
    baseCount T (ne_of_gt h_exposure_pos) rate

/--
Multi-report source data built from rate-indexed Condition 1/2 terms factors
directly into its own residual and count Poisson PMF.
-/
theorem multiReportSourceDataAtRate_self_factorization
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
  exact theorem2_process_source_data_factorization
    (S.multiReportSourceDataAtRate baseCount count hcount gap tail exposure
      hexposure h_exposure rate) rate

/--
Multi-report at-rate source-data self-factorization with nonzero exposure
derived from positive exposure.
-/
theorem multiReportSourceDataAtRate_self_factorization_of_pos_exposure
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
  exact multiReportSourceDataAtRate_self_factorization
    S baseCount count hcount gap hexposure (ne_of_gt h_exposure_pos)

theorem multiReportSourceDataAtRate_factorization
    (S : Theorem2ConditionFunctionSemantics) (baseCount count : ℕ)
    (hcount : 1 < count)
    (gap : Fin count → ℝ) {tail exposure rate : ℝ}
    (hexposure : (∑ j : Fin count, gap j) + tail = exposure)
    (h_exposure : exposure ≠ 0) :
    (S.multiReportSourceDataAtRate baseCount count hcount gap tail exposure
        hexposure h_exposure rate).likelihood rate =
      (S.toConditionFunctions.multiReportSourceData baseCount count hcount
          gap tail exposure hexposure h_exposure).residual *
        sourcePoissonPMF rate
          (S.toConditionFunctions.multiReportSourceData baseCount count hcount
            gap tail exposure hexposure h_exposure).exposure
          (S.toConditionFunctions.multiReportSourceData baseCount count hcount
            gap tail exposure hexposure h_exposure).count := by
  rw [S.multiReportSourceDataAtRate_eq
    baseCount count hcount gap tail exposure hexposure h_exposure rate]
  exact theorem2_process_source_data_factorization
    (S.toConditionFunctions.multiReportSourceData baseCount count hcount
      gap tail exposure hexposure h_exposure) rate

/--
Multi-report at-rate source-data factorization through the derived
rate-independent condition functions, with nonzero exposure derived from
positive exposure.
-/
theorem multiReportSourceDataAtRate_factorization_of_pos_exposure
    (S : Theorem2ConditionFunctionSemantics) (baseCount count : ℕ)
    (hcount : 1 < count)
    (gap : Fin count → ℝ) {tail exposure rate : ℝ}
    (hexposure : (∑ j : Fin count, gap j) + tail = exposure)
    (h_exposure_pos : 0 < exposure) :
    (S.multiReportSourceDataAtRate baseCount count hcount gap tail exposure
        hexposure (ne_of_gt h_exposure_pos) rate).likelihood rate =
      (S.toConditionFunctions.multiReportSourceData baseCount count hcount
          gap tail exposure hexposure (ne_of_gt h_exposure_pos)).residual *
        sourcePoissonPMF rate
          (S.toConditionFunctions.multiReportSourceData baseCount count hcount
            gap tail exposure hexposure (ne_of_gt h_exposure_pos)).exposure
          (S.toConditionFunctions.multiReportSourceData baseCount count hcount
            gap tail exposure hexposure (ne_of_gt h_exposure_pos)).count := by
  exact multiReportSourceDataAtRate_factorization
    S baseCount count hcount gap hexposure (ne_of_gt h_exposure_pos)

/--
Multi-report ordered-timeline source data built from rate-indexed Condition
1/2 terms factors directly into its own residual and count Poisson PMF.
-/
theorem multiReportSourceDataFromOrderedTimelineAtRate_self_factorization
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
  exact theorem2_process_source_data_factorization
    (S.multiReportSourceDataFromOrderedTimelineAtRate
      baseCount T hcount h_exposure rate) rate

/--
Multi-report ordered-timeline source data built from rate-indexed Condition
1/2 terms agrees with the derived rate-independent condition-function source
data and therefore has the same factorization.
-/
theorem multiReportSourceDataFromOrderedTimelineAtRate_factorization
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
  rw [S.multiReportSourceDataFromOrderedTimelineAtRate_eq
    baseCount T hcount h_exposure rate]
  exact theorem2_process_source_data_factorization
    (S.toConditionFunctions.multiReportSourceDataFromOrderedTimeline
      baseCount T hcount h_exposure) rate

/--
Multi-report ordered-timeline source-data factorization with nonzero exposure
derived from positive window exposure.
-/
theorem multiReportSourceDataFromOrderedTimelineAtRate_factorization_of_pos_exposure
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
  exact S.multiReportSourceDataFromOrderedTimelineAtRate_factorization
    baseCount T hcount (ne_of_gt h_exposure_pos) rate

end Theorem2ConditionFunctionSemantics

/-! ## Process-Law Bridges For Appendix B.2 Source Data -/

/--
Zero-report likelihood using a homogeneous count-process law.  This is the
process-facing version of Appendix B.2 Eq. (18): the rate-dependent part is
the probability of zero interval counts in the observation window.
-/
def theorem2ZeroReportCountLawLikelihood
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (K : Theorem2ConditionFunctions) (baseCount : ℕ)
    (H : HomogeneousCountProcessLaw Ω P) (W : ObservationWindow) : ℝ :=
  theorem2ZeroReportResidual K.startDensity (K.endDensity baseCount) *
    P.real {ω : Ω | H.intervalCount W.startTime W.endTime ω = 0}

/--
The zero-report process-law likelihood is exactly the zero-report source-data
likelihood at the process rate.
-/
theorem theorem2_zero_report_count_law_likelihood_eq_source_data
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (K : Theorem2ConditionFunctions) (baseCount : ℕ)
    (H : HomogeneousCountProcessLaw Ω P) (W : ObservationWindow) :
    theorem2ZeroReportCountLawLikelihood P K baseCount H W =
      (K.zeroReportSourceDataFromWindow baseCount W).likelihood H.rate := by
  rw [theorem2ZeroReportCountLawLikelihood]
  rw [← H.windowNoArrivalKernel_likelihood_eq_prob W]
  simp [Theorem2ConditionFunctions.zeroReportSourceDataFromWindow,
    Theorem2ProcessSourceData.likelihood,
    Theorem2ProcessSourceData.toProcessKernelCase,
    Theorem2ZeroReportProcessData.toProcessKernelCase,
    Theorem2ZeroReportProcessData.exposure,
    Theorem2ProcessKernelCase.likelihood,
    theorem2ZeroReportProcessKernelLikelihood,
    NoArrivalKernel.fromWindow, NoArrivalKernel.likelihood]

/--
Zero-report factorization obtained from a homogeneous count-process law rather
than an abstract source-data record.
-/
theorem theorem2_zero_report_count_law_factorization
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (K : Theorem2ConditionFunctions) (baseCount : ℕ)
    (H : HomogeneousCountProcessLaw Ω P) (W : ObservationWindow) :
    theorem2ZeroReportCountLawLikelihood P K baseCount H W =
      (K.zeroReportSourceDataFromWindow baseCount W).residual *
        sourcePoissonPMF H.rate
          (K.zeroReportSourceDataFromWindow baseCount W).exposure
          (K.zeroReportSourceDataFromWindow baseCount W).count := by
  rw [theorem2_zero_report_count_law_likelihood_eq_source_data P K baseCount H W]
  exact theorem2_process_source_data_factorization
    (K.zeroReportSourceDataFromWindow baseCount W) H.rate

/--
One-report process-law likelihood from Appendix B.2 Eq. (23): condition
function terms times the ordered one-jump density supplied by the homogeneous
arrival-density law.
-/
def theorem2OneReportArrivalLawLikelihood
    (K : Theorem2ConditionFunctions) (baseCount : ℕ)
    (H : HomogeneousArrivalDensityLaw) (T : OrderedOneJumpWindow) : ℝ :=
  theorem2OneReportKernelResidual
      K.startDensity (K.endDensity (baseCount + 1))
      (K.survivalIntegral baseCount) *
    H.oneJumpDensity T

/--
The one-report arrival-density-law likelihood is exactly the one-report
source-data likelihood at the process rate.
-/
theorem theorem2_one_report_arrival_law_likelihood_eq_source_data
    (K : Theorem2ConditionFunctions) (baseCount : ℕ)
    (H : HomogeneousArrivalDensityLaw) (T : OrderedOneJumpWindow)
    (h_exposure : T.window.exposure ≠ 0) :
    theorem2OneReportArrivalLawLikelihood K baseCount H T =
      (K.oneReportSourceDataFromOrderedJumpWindow
        baseCount T h_exposure).likelihood H.rate := by
  change theorem2OneReportArrivalLawLikelihood K baseCount H T =
    (Theorem2ProcessSourceData.one
      (K.oneReportProcessDataFromOrderedJumpWindow
        baseCount T h_exposure)).likelihood H.rate
  rw [theorem2OneReportArrivalLawLikelihood]
  rw [theorem2_one_report_process_data_likelihood_eq_arrival_kernel]
  rw [H.oneJumpDensity_eq_kernel_likelihood T h_exposure]
  simp [Theorem2ConditionFunctions.oneReportProcessDataFromOrderedJumpWindow]

/--
One-report factorization obtained from the reusable homogeneous
arrival-density law.
-/
theorem theorem2_one_report_arrival_law_factorization
    (K : Theorem2ConditionFunctions) (baseCount : ℕ)
    (H : HomogeneousArrivalDensityLaw) (T : OrderedOneJumpWindow)
    (h_exposure : T.window.exposure ≠ 0) :
    theorem2OneReportArrivalLawLikelihood K baseCount H T =
      (K.oneReportSourceDataFromOrderedJumpWindow
          baseCount T h_exposure).residual *
        sourcePoissonPMF H.rate
          (K.oneReportSourceDataFromOrderedJumpWindow
            baseCount T h_exposure).exposure
          (K.oneReportSourceDataFromOrderedJumpWindow
            baseCount T h_exposure).count := by
  rw [theorem2_one_report_arrival_law_likelihood_eq_source_data
    K baseCount H T h_exposure]
  exact theorem2_process_source_data_factorization
    (K.oneReportSourceDataFromOrderedJumpWindow
      baseCount T h_exposure) H.rate

/--
One-report factorization from the reusable homogeneous arrival-density law,
with nonzero exposure derived from positive window exposure.
-/
theorem theorem2_one_report_arrival_law_factorization_of_pos_exposure
    (K : Theorem2ConditionFunctions) (baseCount : ℕ)
    (H : HomogeneousArrivalDensityLaw) (T : OrderedOneJumpWindow)
    (h_exposure_pos : 0 < T.window.exposure) :
    theorem2OneReportArrivalLawLikelihood K baseCount H T =
      (K.oneReportSourceDataFromOrderedJumpWindow
          baseCount T (ne_of_gt h_exposure_pos)).residual *
        sourcePoissonPMF H.rate
          (K.oneReportSourceDataFromOrderedJumpWindow
            baseCount T (ne_of_gt h_exposure_pos)).exposure
          (K.oneReportSourceDataFromOrderedJumpWindow
            baseCount T (ne_of_gt h_exposure_pos)).count := by
  exact theorem2_one_report_arrival_law_factorization
    K baseCount H T (ne_of_gt h_exposure_pos)

/--
Multi-report process-law likelihood from Appendix B.2 Eq. (29): condition
function terms times the ordered finite-jump density supplied by the
homogeneous arrival-density law.
-/
def theorem2MultiReportArrivalLawLikelihood
    (K : Theorem2ConditionFunctions) (baseCount : ℕ)
    (H : HomogeneousArrivalDensityLaw) (T : OrderedFiniteJumpTimeline) : ℝ :=
  theorem2MultiReportKernelResidual
      K.startDensity (K.endDensity (baseCount + T.count))
      (K.survivalIntegralProduct baseCount T.count) *
    H.finiteJumpDensity T

/--
The multi-report arrival-density-law likelihood is exactly the multi-report
source-data likelihood at the process rate.
-/
theorem theorem2_multi_report_arrival_law_likelihood_eq_source_data
    (K : Theorem2ConditionFunctions) (baseCount : ℕ)
    (H : HomogeneousArrivalDensityLaw) (T : OrderedFiniteJumpTimeline)
    (hcount : 1 < T.count) (h_exposure : T.window.exposure ≠ 0) :
    theorem2MultiReportArrivalLawLikelihood K baseCount H T =
      (K.multiReportSourceDataFromOrderedTimeline
        baseCount T hcount h_exposure).likelihood H.rate := by
  change theorem2MultiReportArrivalLawLikelihood K baseCount H T =
    (Theorem2ProcessSourceData.multi
      (K.multiReportProcessDataFromOrderedTimeline
        baseCount T hcount h_exposure)).likelihood H.rate
  rw [theorem2MultiReportArrivalLawLikelihood]
  rw [theorem2_multi_report_process_data_likelihood_eq_arrival_kernel]
  rw [H.finiteJumpDensity_eq_kernel_likelihood T h_exposure]
  simp [Theorem2ConditionFunctions.multiReportProcessDataFromOrderedTimeline]

/--
Multi-report factorization obtained from the reusable homogeneous
arrival-density law.
-/
theorem theorem2_multi_report_arrival_law_factorization
    (K : Theorem2ConditionFunctions) (baseCount : ℕ)
    (H : HomogeneousArrivalDensityLaw) (T : OrderedFiniteJumpTimeline)
    (hcount : 1 < T.count) (h_exposure : T.window.exposure ≠ 0) :
    theorem2MultiReportArrivalLawLikelihood K baseCount H T =
      (K.multiReportSourceDataFromOrderedTimeline
          baseCount T hcount h_exposure).residual *
        sourcePoissonPMF H.rate
          (K.multiReportSourceDataFromOrderedTimeline
            baseCount T hcount h_exposure).exposure
          (K.multiReportSourceDataFromOrderedTimeline
            baseCount T hcount h_exposure).count := by
  rw [theorem2_multi_report_arrival_law_likelihood_eq_source_data
    K baseCount H T hcount h_exposure]
  exact theorem2_process_source_data_factorization
    (K.multiReportSourceDataFromOrderedTimeline
      baseCount T hcount h_exposure) H.rate

/--
Multi-report factorization from the reusable homogeneous arrival-density law,
with nonzero exposure derived from positive window exposure.
-/
theorem theorem2_multi_report_arrival_law_factorization_of_pos_exposure
    (K : Theorem2ConditionFunctions) (baseCount : ℕ)
    (H : HomogeneousArrivalDensityLaw) (T : OrderedFiniteJumpTimeline)
    (hcount : 1 < T.count) (h_exposure_pos : 0 < T.window.exposure) :
    theorem2MultiReportArrivalLawLikelihood K baseCount H T =
      (K.multiReportSourceDataFromOrderedTimeline
          baseCount T hcount (ne_of_gt h_exposure_pos)).residual *
        sourcePoissonPMF H.rate
          (K.multiReportSourceDataFromOrderedTimeline
            baseCount T hcount (ne_of_gt h_exposure_pos)).exposure
          (K.multiReportSourceDataFromOrderedTimeline
            baseCount T hcount (ne_of_gt h_exposure_pos)).count := by
  exact theorem2_multi_report_arrival_law_factorization
    K baseCount H T hcount (ne_of_gt h_exposure_pos)

/--
Zero-report likelihood from the combined homogeneous Poisson process law.
-/
def theorem2ZeroReportProcessLawLikelihood
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (K : Theorem2ConditionFunctions) (baseCount : ℕ)
    (H : HomogeneousPoissonProcessLaw Ω P) (W : ObservationWindow) : ℝ :=
  theorem2ZeroReportCountLawLikelihood P K baseCount H.countLaw W

/--
Zero-report factorization from the combined process law, with the shared
process rate on the Poisson PMF.
-/
theorem theorem2_zero_report_process_law_factorization
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (K : Theorem2ConditionFunctions) (baseCount : ℕ)
    (H : HomogeneousPoissonProcessLaw Ω P) (W : ObservationWindow) :
    theorem2ZeroReportProcessLawLikelihood P K baseCount H W =
      (K.zeroReportSourceDataFromWindow baseCount W).residual *
        sourcePoissonPMF H.rate
          (K.zeroReportSourceDataFromWindow baseCount W).exposure
          (K.zeroReportSourceDataFromWindow baseCount W).count := by
  simpa [theorem2ZeroReportProcessLawLikelihood,
    HomogeneousPoissonProcessLaw.rate] using
    theorem2_zero_report_count_law_factorization
      P K baseCount H.countLaw W

/--
One-report likelihood from the combined homogeneous Poisson process law.
-/
def theorem2OneReportProcessLawLikelihood
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (K : Theorem2ConditionFunctions) (baseCount : ℕ)
    (H : HomogeneousPoissonProcessLaw Ω P) (T : OrderedOneJumpWindow) : ℝ :=
  theorem2OneReportArrivalLawLikelihood K baseCount H.arrivalLaw T

/--
One-report factorization from the combined process law, with the shared process
rate on the Poisson PMF.
-/
theorem theorem2_one_report_process_law_factorization
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (K : Theorem2ConditionFunctions) (baseCount : ℕ)
    (H : HomogeneousPoissonProcessLaw Ω P) (T : OrderedOneJumpWindow)
    (h_exposure : T.window.exposure ≠ 0) :
    theorem2OneReportProcessLawLikelihood K baseCount H T =
      (K.oneReportSourceDataFromOrderedJumpWindow
          baseCount T h_exposure).residual *
        sourcePoissonPMF H.rate
          (K.oneReportSourceDataFromOrderedJumpWindow
            baseCount T h_exposure).exposure
          (K.oneReportSourceDataFromOrderedJumpWindow
            baseCount T h_exposure).count := by
  simpa [theorem2OneReportProcessLawLikelihood,
    HomogeneousPoissonProcessLaw.rate, H.arrival_rate_eq_count_rate] using
    theorem2_one_report_arrival_law_factorization
      K baseCount H.arrivalLaw T h_exposure

/--
One-report factorization from the combined process law, with nonzero exposure
derived from positive window exposure.
-/
theorem theorem2_one_report_process_law_factorization_of_pos_exposure
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (K : Theorem2ConditionFunctions) (baseCount : ℕ)
    (H : HomogeneousPoissonProcessLaw Ω P) (T : OrderedOneJumpWindow)
    (h_exposure_pos : 0 < T.window.exposure) :
    theorem2OneReportProcessLawLikelihood K baseCount H T =
      (K.oneReportSourceDataFromOrderedJumpWindow
          baseCount T (ne_of_gt h_exposure_pos)).residual *
        sourcePoissonPMF H.rate
          (K.oneReportSourceDataFromOrderedJumpWindow
            baseCount T (ne_of_gt h_exposure_pos)).exposure
          (K.oneReportSourceDataFromOrderedJumpWindow
            baseCount T (ne_of_gt h_exposure_pos)).count := by
  exact theorem2_one_report_process_law_factorization
    K baseCount H T (ne_of_gt h_exposure_pos)

/--
Multi-report likelihood from the combined homogeneous Poisson process law.
-/
def theorem2MultiReportProcessLawLikelihood
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (K : Theorem2ConditionFunctions) (baseCount : ℕ)
    (H : HomogeneousPoissonProcessLaw Ω P)
    (T : OrderedFiniteJumpTimeline) : ℝ :=
  theorem2MultiReportArrivalLawLikelihood K baseCount H.arrivalLaw T

/--
Multi-report factorization from the combined process law, with the shared
process rate on the Poisson PMF.
-/
theorem theorem2_multi_report_process_law_factorization
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (K : Theorem2ConditionFunctions) (baseCount : ℕ)
    (H : HomogeneousPoissonProcessLaw Ω P)
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
  simpa [theorem2MultiReportProcessLawLikelihood,
    HomogeneousPoissonProcessLaw.rate, H.arrival_rate_eq_count_rate] using
    theorem2_multi_report_arrival_law_factorization
      K baseCount H.arrivalLaw T hcount h_exposure

/--
Multi-report factorization from the combined process law, with nonzero
exposure derived from positive window exposure.
-/
theorem theorem2_multi_report_process_law_factorization_of_pos_exposure
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (K : Theorem2ConditionFunctions) (baseCount : ℕ)
    (H : HomogeneousPoissonProcessLaw Ω P)
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
  exact theorem2_multi_report_process_law_factorization
    K baseCount H T hcount (ne_of_gt h_exposure_pos)

/--
Zero-report likelihood induced directly by mathlib Poisson increment laws.
-/
def theorem2ZeroReportPoissonIncrementLawLikelihood
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (K : Theorem2ConditionFunctions) (baseCount : ℕ)
    (H : HomogeneousPoissonCountingProcessByLaw Ω P)
    (W : ObservationWindow) : ℝ :=
  theorem2ZeroReportProcessLawLikelihood P K baseCount
    H.toHomogeneousPoissonProcessLaw W

/--
Zero-report factorization induced directly by mathlib Poisson increment laws.
-/
theorem theorem2_zero_report_poisson_increment_law_factorization
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (K : Theorem2ConditionFunctions) (baseCount : ℕ)
    (H : HomogeneousPoissonCountingProcessByLaw Ω P)
    (W : ObservationWindow) :
    theorem2ZeroReportPoissonIncrementLawLikelihood P K baseCount H W =
      (K.zeroReportSourceDataFromWindow baseCount W).residual *
        sourcePoissonPMF H.rate
          (K.zeroReportSourceDataFromWindow baseCount W).exposure
          (K.zeroReportSourceDataFromWindow baseCount W).count := by
  simpa [theorem2ZeroReportPoissonIncrementLawLikelihood] using
    theorem2_zero_report_process_law_factorization
      P K baseCount H.toHomogeneousPoissonProcessLaw W

/--
One-report likelihood induced directly by mathlib Poisson increment laws and
the canonical ordered-arrival density at the same rate.
-/
def theorem2OneReportPoissonIncrementLawLikelihood
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (K : Theorem2ConditionFunctions) (baseCount : ℕ)
    (H : HomogeneousPoissonCountingProcessByLaw Ω P)
    (T : OrderedOneJumpWindow) : ℝ :=
  theorem2OneReportProcessLawLikelihood K baseCount
    H.toHomogeneousPoissonProcessLaw T

/--
One-report factorization induced directly by mathlib Poisson increment laws
and the canonical ordered-arrival density at the same rate.
-/
theorem theorem2_one_report_poisson_increment_law_factorization
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (K : Theorem2ConditionFunctions) (baseCount : ℕ)
    (H : HomogeneousPoissonCountingProcessByLaw Ω P)
    (T : OrderedOneJumpWindow) (h_exposure : T.window.exposure ≠ 0) :
    theorem2OneReportPoissonIncrementLawLikelihood K baseCount H T =
      (K.oneReportSourceDataFromOrderedJumpWindow
          baseCount T h_exposure).residual *
        sourcePoissonPMF H.rate
          (K.oneReportSourceDataFromOrderedJumpWindow
            baseCount T h_exposure).exposure
          (K.oneReportSourceDataFromOrderedJumpWindow
            baseCount T h_exposure).count := by
  simpa [theorem2OneReportPoissonIncrementLawLikelihood] using
    theorem2_one_report_process_law_factorization
      K baseCount H.toHomogeneousPoissonProcessLaw T h_exposure

/--
One-report factorization induced directly by mathlib Poisson increment laws,
with nonzero exposure derived from positive window exposure.
-/
theorem theorem2_one_report_poisson_increment_law_factorization_of_pos_exposure
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (K : Theorem2ConditionFunctions) (baseCount : ℕ)
    (H : HomogeneousPoissonCountingProcessByLaw Ω P)
    (T : OrderedOneJumpWindow) (h_exposure_pos : 0 < T.window.exposure) :
    theorem2OneReportPoissonIncrementLawLikelihood K baseCount H T =
      (K.oneReportSourceDataFromOrderedJumpWindow
          baseCount T (ne_of_gt h_exposure_pos)).residual *
        sourcePoissonPMF H.rate
          (K.oneReportSourceDataFromOrderedJumpWindow
            baseCount T (ne_of_gt h_exposure_pos)).exposure
          (K.oneReportSourceDataFromOrderedJumpWindow
            baseCount T (ne_of_gt h_exposure_pos)).count := by
  exact theorem2_one_report_poisson_increment_law_factorization
    K baseCount H T (ne_of_gt h_exposure_pos)

/--
Multi-report likelihood induced directly by mathlib Poisson increment laws and
the canonical ordered-arrival density at the same rate.
-/
def theorem2MultiReportPoissonIncrementLawLikelihood
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (K : Theorem2ConditionFunctions) (baseCount : ℕ)
    (H : HomogeneousPoissonCountingProcessByLaw Ω P)
    (T : OrderedFiniteJumpTimeline) : ℝ :=
  theorem2MultiReportProcessLawLikelihood K baseCount
    H.toHomogeneousPoissonProcessLaw T

/--
Multi-report factorization induced directly by mathlib Poisson increment laws
and the canonical ordered-arrival density at the same rate.
-/
theorem theorem2_multi_report_poisson_increment_law_factorization
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (K : Theorem2ConditionFunctions) (baseCount : ℕ)
    (H : HomogeneousPoissonCountingProcessByLaw Ω P)
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
  simpa [theorem2MultiReportPoissonIncrementLawLikelihood] using
    theorem2_multi_report_process_law_factorization
      K baseCount H.toHomogeneousPoissonProcessLaw T hcount h_exposure

/--
Multi-report factorization induced directly by mathlib Poisson increment laws,
with nonzero exposure derived from positive window exposure.
-/
theorem theorem2_multi_report_poisson_increment_law_factorization_of_pos_exposure
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (K : Theorem2ConditionFunctions) (baseCount : ℕ)
    (H : HomogeneousPoissonCountingProcessByLaw Ω P)
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
  exact theorem2_multi_report_poisson_increment_law_factorization
    K baseCount H T hcount (ne_of_gt h_exposure_pos)

/-! ## Unified Process-Law Cases For Appendix B.2 -/

/--
Observed Appendix B.2 cases whose rate-dependent factors are supplied by a
combined homogeneous Poisson process law.

This is the narrow process-facing case object: it stores the paper's
rate-independent condition functions and the ordered observation window/timeline
data, while `HomogeneousPoissonProcessLaw` supplies the actual count and
arrival-density laws.
-/
inductive Theorem2ProcessLawCase where
  | zero
      (K : Theorem2ConditionFunctions) (baseCount : ℕ)
      (W : ObservationWindow)
  | one
      (K : Theorem2ConditionFunctions) (baseCount : ℕ)
      (T : OrderedOneJumpWindow)
      (exposure_ne_zero : T.window.exposure ≠ 0)
  | multi
      (K : Theorem2ConditionFunctions) (baseCount : ℕ)
      (T : OrderedFiniteJumpTimeline)
      (count_gt_one : 1 < T.count)
      (exposure_ne_zero : T.window.exposure ≠ 0)

namespace Theorem2ProcessLawCase

/-- The source-data record induced by a process-law case. -/
def sourceData : Theorem2ProcessLawCase → Theorem2ProcessSourceData
  | zero K baseCount W =>
      K.zeroReportSourceDataFromWindow baseCount W
  | one K baseCount T h_exposure =>
      K.oneReportSourceDataFromOrderedJumpWindow baseCount T h_exposure
  | multi K baseCount T hcount h_exposure =>
      K.multiReportSourceDataFromOrderedTimeline
        baseCount T hcount h_exposure

def exposure (C : Theorem2ProcessLawCase) : ℝ :=
  C.sourceData.exposure

def count (C : Theorem2ProcessLawCase) : ℕ :=
  C.sourceData.count

def residual (C : Theorem2ProcessLawCase) : ℝ :=
  C.sourceData.residual

/-- Process-law cases always carry nonnegative observation exposure. -/
theorem exposure_nonneg (C : Theorem2ProcessLawCase) :
    0 ≤ C.exposure := by
  cases C with
  | zero _ _ W =>
      exact W.exposure_nonneg
  | one _ _ T _ =>
      exact T.window.exposure_nonneg
  | multi _ _ T _ _ =>
      exact T.window.exposure_nonneg

/-- Generic observed-arrival case underlying a Theorem 2 process-law case. -/
def observedArrivalCase : Theorem2ProcessLawCase → ObservedArrivalCase
  | zero _ _ W => ObservedArrivalCase.zero W
  | one _ _ T h_exposure => ObservedArrivalCase.one T h_exposure
  | multi _ _ T _ h_exposure => ObservedArrivalCase.finite T h_exposure

/--
The paper-specific condition-function residual before the generic arrival
kernel is rewritten as a Poisson count PMF.
-/
def conditionResidual : Theorem2ProcessLawCase → ℝ
  | zero K baseCount _ =>
      theorem2ZeroReportResidual K.startDensity (K.endDensity baseCount)
  | one K baseCount _ _ =>
      theorem2OneReportKernelResidual
        K.startDensity (K.endDensity (baseCount + 1))
        (K.survivalIntegral baseCount)
  | multi K baseCount T _ _ =>
      theorem2MultiReportKernelResidual
        K.startDensity (K.endDensity (baseCount + T.count))
        (K.survivalIntegralProduct baseCount T.count)

/-- Process-law likelihood for a case at the law's shared rate. -/
def likelihood
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (C : Theorem2ProcessLawCase)
    (H : HomogeneousPoissonProcessLaw Ω P) : ℝ :=
  match C with
  | zero K baseCount W =>
      theorem2ZeroReportProcessLawLikelihood P K baseCount H W
  | one K baseCount T _ =>
      theorem2OneReportProcessLawLikelihood K baseCount H T
  | multi K baseCount T _ _ =>
      theorem2MultiReportProcessLawLikelihood K baseCount H T

/--
The process-law likelihood splits into the paper-specific condition residual
times the observed-arrival probability/density supplied by the combined
homogeneous Poisson process law.
-/
theorem likelihood_eq_conditionResidual_mul_processObservedArrivalCaseLikelihood
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (C : Theorem2ProcessLawCase)
    (H : HomogeneousPoissonProcessLaw Ω P) :
    C.likelihood H =
      C.conditionResidual *
        H.observedArrivalCaseLikelihood C.observedArrivalCase := by
  cases C with
  | zero K baseCount W =>
      rfl
  | one K baseCount T h_exposure =>
      rfl
  | multi K baseCount T hcount h_exposure =>
      rfl

/--
The process-law likelihood splits into the paper-specific condition residual
times the generic observed-arrival likelihood supplied by the reusable
Poisson-process library.
-/
theorem likelihood_eq_conditionResidual_mul_observedArrivalCase_likelihood
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (C : Theorem2ProcessLawCase)
    (H : HomogeneousPoissonProcessLaw Ω P) :
    C.likelihood H =
      C.conditionResidual * C.observedArrivalCase.likelihood H.rate := by
  rw [C.likelihood_eq_conditionResidual_mul_processObservedArrivalCaseLikelihood H]
  rw [H.observedArrivalCaseLikelihood_eq_kernel_likelihood C.observedArrivalCase]

/--
The generic observed-arrival part of a process-law case has the reusable
Poisson count-PMF factorization.
-/
theorem observedArrivalCase_factorization
    (C : Theorem2ProcessLawCase) (rate : ℝ) :
    C.observedArrivalCase.likelihood rate =
      C.observedArrivalCase.residual *
        countLikelihood rate
          C.observedArrivalCase.exposure C.observedArrivalCase.count :=
  C.observedArrivalCase.factorization rate

theorem exposure_eq_observedArrivalCase_exposure
    (C : Theorem2ProcessLawCase) :
    C.exposure = C.observedArrivalCase.exposure := by
  cases C <;> rfl

theorem count_eq_observedArrivalCase_count
    (C : Theorem2ProcessLawCase) :
    C.count = C.observedArrivalCase.count := by
  cases C <;> rfl

theorem residual_eq_conditionResidual_mul_observedArrivalCase_residual
    (C : Theorem2ProcessLawCase) :
    C.residual =
      C.conditionResidual * C.observedArrivalCase.residual := by
  cases C with
  | zero K baseCount W =>
      simpa [residual, sourceData, conditionResidual, observedArrivalCase,
        Theorem2ProcessSourceData.conditionResidual,
        Theorem2ProcessSourceData.arrivalKernelCase,
        Theorem2ConditionFunctions.zeroReportSourceDataFromWindow,
        ArrivalKernelCase.residual, ObservedArrivalCase.residual] using
          (K.zeroReportSourceDataFromWindow baseCount W).residual_eq_conditionResidual_mul_arrivalKernelCase_residual
  | one K baseCount T h_exposure =>
      simpa [residual, sourceData, conditionResidual, observedArrivalCase,
        Theorem2ProcessSourceData.conditionResidual,
        Theorem2ProcessSourceData.arrivalKernelCase,
        Theorem2ConditionFunctions.oneReportSourceDataFromOrderedJumpWindow,
        Theorem2ConditionFunctions.oneReportProcessDataFromOrderedJumpWindow,
        OneInterarrivalTailKernel.fromOrderedWindow,
        ArrivalKernelCase.residual, ObservedArrivalCase.residual,
        Nat.add_comm] using
          (K.oneReportSourceDataFromOrderedJumpWindow
            baseCount T h_exposure).residual_eq_conditionResidual_mul_arrivalKernelCase_residual
  | multi K baseCount T hcount h_exposure =>
      simpa [residual, sourceData, conditionResidual, observedArrivalCase,
        Theorem2ProcessSourceData.conditionResidual,
        Theorem2ProcessSourceData.arrivalKernelCase,
        Theorem2ConditionFunctions.multiReportSourceDataFromOrderedTimeline,
        Theorem2ConditionFunctions.multiReportProcessDataFromOrderedTimeline,
        FinInterarrivalTailKernel.fromOrderedTimeline,
        ArrivalKernelCase.residual, ObservedArrivalCase.residual] using
          (K.multiReportSourceDataFromOrderedTimeline
            baseCount T hcount h_exposure).residual_eq_conditionResidual_mul_arrivalKernelCase_residual

/--
Rate-parametric likelihood kernel associated with a process-law case after the
process law has supplied the observed-arrival density/probability.
-/
def rateLikelihood (C : Theorem2ProcessLawCase) (rate : ℝ) : ℝ :=
  C.conditionResidual * C.observedArrivalCase.likelihood rate

/--
The combined-process likelihood is the rate-parametric condition-function
kernel evaluated at the process law's shared rate.
-/
theorem likelihood_eq_rateLikelihood
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (C : Theorem2ProcessLawCase)
    (H : HomogeneousPoissonProcessLaw Ω P) :
    C.likelihood H = C.rateLikelihood H.rate := by
  simpa [rateLikelihood] using
    C.likelihood_eq_conditionResidual_mul_observedArrivalCase_likelihood H

def rateResidual (C : Theorem2ProcessLawCase) : ℝ :=
  C.conditionResidual * C.observedArrivalCase.residual

theorem residual_eq_rateResidual (C : Theorem2ProcessLawCase) :
    C.residual = C.rateResidual :=
  C.residual_eq_conditionResidual_mul_observedArrivalCase_residual

/--
The rate-parametric process-law kernel factors through the Poisson count PMF
using only generic observed-arrival algebra.
-/
theorem rateLikelihood_factorization
    (C : Theorem2ProcessLawCase) (rate : ℝ) :
    C.rateLikelihood rate =
      C.residual * sourcePoissonPMF rate C.exposure C.count := by
  rw [rateLikelihood]
  rw [C.observedArrivalCase_factorization rate]
  rw [C.residual_eq_rateResidual]
  rw [C.exposure_eq_observedArrivalCase_exposure,
    C.count_eq_observedArrivalCase_count]
  simp [rateResidual, sourcePoissonPMF]
  ring

/-- Direct reusable likelihood-factorization certificate for a process-law case. -/
def poissonFactorization
    (C : Theorem2ProcessLawCase) : PoissonLikelihoodFactorization where
  likelihood := C.rateLikelihood
  residual := C.residual
  exposure := C.exposure
  count := C.count
  factorized := C.rateLikelihood_factorization

/--
The process-law case residual in the Theorem 1 / Appendix B.2 factorization is
independent of the Poisson rate.
-/
theorem residual_rateIndependent
    (C : Theorem2ProcessLawCase) :
    RateIndependent (fun _rate : ℝ => C.residual) := by
  exact C.poissonFactorization.residual_factor_rateIndependent

/--
The process-law likelihood agrees with the source-data likelihood at the
combined process rate.
-/
theorem likelihood_eq_sourceData_likelihood
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (C : Theorem2ProcessLawCase)
    (H : HomogeneousPoissonProcessLaw Ω P) :
    C.likelihood H = C.sourceData.likelihood H.rate := by
  cases C with
  | zero K baseCount W =>
      simpa [likelihood, sourceData, HomogeneousPoissonProcessLaw.rate] using
        theorem2_zero_report_count_law_likelihood_eq_source_data
          P K baseCount H.countLaw W
  | one K baseCount T h_exposure =>
      simpa [likelihood, sourceData, theorem2OneReportProcessLawLikelihood,
        HomogeneousPoissonProcessLaw.rate, H.arrival_rate_eq_count_rate] using
          theorem2_one_report_arrival_law_likelihood_eq_source_data
            K baseCount H.arrivalLaw T h_exposure
  | multi K baseCount T hcount h_exposure =>
      simpa [likelihood, sourceData, theorem2MultiReportProcessLawLikelihood,
        HomogeneousPoissonProcessLaw.rate, H.arrival_rate_eq_count_rate] using
          theorem2_multi_report_arrival_law_likelihood_eq_source_data
            K baseCount H.arrivalLaw T hcount h_exposure

/--
Unified zero/one/multi factorization from a combined homogeneous process law.
-/
theorem factorization
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (C : Theorem2ProcessLawCase)
    (H : HomogeneousPoissonProcessLaw Ω P) :
    C.likelihood H =
      C.residual * sourcePoissonPMF H.rate C.exposure C.count := by
  rw [C.likelihood_eq_conditionResidual_mul_observedArrivalCase_likelihood H]
  exact C.rateLikelihood_factorization H.rate

/--
Unified zero/one/multi likelihood induced directly by mathlib Poisson
increment laws and the canonical ordered-arrival density at the same rate.
-/
def likelihoodFromPoissonIncrementLaws
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (C : Theorem2ProcessLawCase)
    (H : HomogeneousPoissonCountingProcessByLaw Ω P) : ℝ :=
  C.likelihood H.toHomogeneousPoissonProcessLaw

/--
The likelihood induced directly by mathlib Poisson-increment laws is the
rate-parametric condition-function kernel evaluated at the primitive rate.
-/
theorem likelihoodFromPoissonIncrementLaws_eq_rateLikelihood
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (C : Theorem2ProcessLawCase)
    (H : HomogeneousPoissonCountingProcessByLaw Ω P) :
    C.likelihoodFromPoissonIncrementLaws H = C.rateLikelihood H.rate := by
  simpa [likelihoodFromPoissonIncrementLaws] using
    C.likelihood_eq_rateLikelihood H.toHomogeneousPoissonProcessLaw

/--
Unified zero/one/multi factorization induced directly by mathlib Poisson
increment laws and the canonical ordered-arrival density at the same rate.
-/
theorem factorizationFromPoissonIncrementLaws
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (C : Theorem2ProcessLawCase)
    (H : HomogeneousPoissonCountingProcessByLaw Ω P) :
    C.likelihoodFromPoissonIncrementLaws H =
      C.residual * sourcePoissonPMF H.rate C.exposure C.count := by
  simpa [likelihoodFromPoissonIncrementLaws] using
    C.factorization H.toHomogeneousPoissonProcessLaw

end Theorem2ProcessLawCase

/-- Residual for a finite product of source-shaped process-kernel cases. -/
def theorem2ProcessKernelCaseProductResidual {Incident : Type*}
    (s : Finset Incident) (C : Incident → Theorem2ProcessKernelCase) : ℝ :=
  poissonLikelihoodFactorizationProductResidual s
    (fun i => theorem2ProcessKernelCasePoissonFactorization (C i))

/--
Finite-product Theorem 1 decomposition for source-shaped process-kernel cases:
the product of full case likelihoods collapses to one total-count Poisson PMF,
up to a rate-independent residual.
-/
theorem theorem1_process_kernel_likelihood_product_decomposition
    {Incident : Type*} (s : Finset Incident)
    (C : Incident → Theorem2ProcessKernelCase) (rate : ℝ)
    (h_totalExposure :
      totalExposure s (fun i => (C i).exposure) ≠ 0) :
    (∏ i ∈ s, (C i).likelihood rate) =
      theorem2ProcessKernelCaseProductResidual s C *
        sourcePoissonPMF rate
          (totalExposure s fun i => (C i).exposure)
          (totalCount s fun i => (C i).count) := by
  simpa [theorem2ProcessKernelCaseProductResidual,
    theorem2ProcessKernelCasePoissonFactorization, sourcePoissonPMF] using
      prod_poissonLikelihoodFactorization_eq_collapsed_countLikelihood
        s (fun i => theorem2ProcessKernelCasePoissonFactorization (C i))
        rate h_totalExposure

/--
Finite-product Theorem 1 decomposition for source-shaped process-kernel cases,
with nonzero total exposure derived from one positive row exposure and
nonnegativity of all included row exposures.
-/
theorem theorem1_process_kernel_likelihood_product_decomposition_of_exists_pos_exposure
    {Incident : Type*} (s : Finset Incident)
    (C : Incident → Theorem2ProcessKernelCase) (rate : ℝ)
    (h_nonneg : ∀ i ∈ s, 0 ≤ (C i).exposure)
    (h_exists : ∃ i ∈ s, 0 < (C i).exposure) :
    (∏ i ∈ s, (C i).likelihood rate) =
      theorem2ProcessKernelCaseProductResidual s C *
        sourcePoissonPMF rate
          (totalExposure s fun i => (C i).exposure)
          (totalCount s fun i => (C i).count) := by
  simpa [theorem2ProcessKernelCaseProductResidual,
    theorem2ProcessKernelCasePoissonFactorization, sourcePoissonPMF] using
      prod_poissonLikelihoodFactorization_eq_collapsed_countLikelihood_of_exists_pos_exposure
        s (fun i => theorem2ProcessKernelCasePoissonFactorization (C i))
        rate h_nonneg h_exists

def theorem2ProcessSourceDataPoissonFactorization
    (D : Theorem2ProcessSourceData) : PoissonLikelihoodFactorization :=
  theorem2ProcessKernelCasePoissonFactorization D.toProcessKernelCase

/-- Residual for a finite product of source-data process cases. -/
def theorem2ProcessSourceDataProductResidual {Incident : Type*}
    (s : Finset Incident) (D : Incident → Theorem2ProcessSourceData) : ℝ :=
  theorem2ProcessKernelCaseProductResidual s
    (fun i => (D i).toProcessKernelCase)

/--
Finite-product Theorem 1 decomposition for source data built from reusable
Poisson process kernels.
-/
theorem theorem1_process_source_data_likelihood_product_decomposition
    {Incident : Type*} (s : Finset Incident)
    (D : Incident → Theorem2ProcessSourceData) (rate : ℝ)
    (h_totalExposure :
      totalExposure s (fun i => (D i).exposure) ≠ 0) :
    (∏ i ∈ s, (D i).likelihood rate) =
      theorem2ProcessSourceDataProductResidual s D *
        sourcePoissonPMF rate
          (totalExposure s fun i => (D i).exposure)
          (totalCount s fun i => (D i).count) := by
  simpa [Theorem2ProcessSourceData.likelihood,
    Theorem2ProcessSourceData.exposure, Theorem2ProcessSourceData.count,
    theorem2ProcessSourceDataProductResidual] using
      theorem1_process_kernel_likelihood_product_decomposition
        s (fun i => (D i).toProcessKernelCase) rate h_totalExposure

/--
Finite-product Theorem 1 decomposition for source data built from reusable
Poisson process kernels, with nonzero total exposure derived from one positive
row exposure and nonnegativity of all included row exposures.
-/
theorem theorem1_process_source_data_likelihood_product_decomposition_of_exists_pos_exposure
    {Incident : Type*} (s : Finset Incident)
    (D : Incident → Theorem2ProcessSourceData) (rate : ℝ)
    (h_nonneg : ∀ i ∈ s, 0 ≤ (D i).exposure)
    (h_exists : ∃ i ∈ s, 0 < (D i).exposure) :
    (∏ i ∈ s, (D i).likelihood rate) =
      theorem2ProcessSourceDataProductResidual s D *
        sourcePoissonPMF rate
          (totalExposure s fun i => (D i).exposure)
          (totalCount s fun i => (D i).count) := by
  simpa [Theorem2ProcessSourceData.likelihood,
    Theorem2ProcessSourceData.exposure, Theorem2ProcessSourceData.count,
    theorem2ProcessSourceDataProductResidual] using
      theorem1_process_kernel_likelihood_product_decomposition_of_exists_pos_exposure
        s (fun i => (D i).toProcessKernelCase) rate h_nonneg h_exists

/-- Residual for a finite product of combined-process-law cases. -/
def theorem2ProcessLawCaseProductResidual {Incident : Type*}
    (s : Finset Incident) (C : Incident → Theorem2ProcessLawCase) : ℝ :=
  poissonLikelihoodFactorizationProductResidual s
    (fun i => (C i).poissonFactorization)

/--
Reusable observed-arrival residual underlying a finite product of
process-law cases.
-/
def theorem2ProcessLawCaseObservedArrivalProductResidual {Incident : Type*}
    (s : Finset Incident) (C : Incident → Theorem2ProcessLawCase) : ℝ :=
  ObservedArrivalCase.productResidual s
    fun i => (C i).observedArrivalCase

/--
The process-law product residual is exactly the product of paper-specific
condition residuals times the reusable observed-arrival product residual.
-/
theorem theorem2ProcessLawCaseProductResidual_eq_condition_mul_observedArrivalResidual
    {Incident : Type*} (s : Finset Incident)
    (C : Incident → Theorem2ProcessLawCase) :
    theorem2ProcessLawCaseProductResidual s C =
      (∏ i ∈ s, (C i).conditionResidual) *
        theorem2ProcessLawCaseObservedArrivalProductResidual s C := by
  classical
  simp [theorem2ProcessLawCaseProductResidual,
    theorem2ProcessLawCaseObservedArrivalProductResidual,
    ObservedArrivalCase.productResidual,
    poissonLikelihoodFactorizationProductResidual,
    Theorem2ProcessLawCase.poissonFactorization,
    ObservedArrivalCase.toPoissonLikelihoodFactorization]
  rw [show
      (∏ i ∈ s, (C i).residual) =
        ∏ i ∈ s,
          ((C i).conditionResidual * (C i).observedArrivalCase.residual) by
        refine Finset.prod_congr rfl ?_
        intro i _hi
        exact (C i).residual_eq_conditionResidual_mul_observedArrivalCase_residual]
  rw [Finset.prod_mul_distrib]
  simp [Theorem2ProcessLawCase.exposure_eq_observedArrivalCase_exposure,
    Theorem2ProcessLawCase.count_eq_observedArrivalCase_count]
  ring

/--
The finite-product residual for process-law cases is the same object as the
finite-product residual for the induced Appendix B.2 source-data rows.
-/
theorem theorem2ProcessLawCaseProductResidual_eq_sourceDataProductResidual
    {Incident : Type*} (s : Finset Incident)
    (C : Incident → Theorem2ProcessLawCase) :
    theorem2ProcessLawCaseProductResidual s C =
      theorem2ProcessSourceDataProductResidual s
        (fun i => (C i).sourceData) := by
  simp [theorem2ProcessLawCaseProductResidual,
    theorem2ProcessSourceDataProductResidual,
    theorem2ProcessKernelCaseProductResidual,
    poissonLikelihoodFactorizationProductResidual,
    theorem2ProcessKernelCasePoissonFactorization,
    Theorem2ProcessLawCase.poissonFactorization,
    Theorem2ProcessLawCase.residual,
    Theorem2ProcessLawCase.exposure,
    Theorem2ProcessLawCase.count,
    Theorem2ProcessSourceData.residual,
    Theorem2ProcessSourceData.exposure,
    Theorem2ProcessSourceData.count]

/--
Finite-product decomposition for process-law cases at an explicit Poisson
rate, without requiring a continuous-time process-law object.
-/
theorem theorem1_process_law_rateLikelihood_product_decomposition
    {Incident : Type*} (s : Finset Incident)
    (C : Incident → Theorem2ProcessLawCase) (rate : ℝ)
    (h_totalExposure :
      totalExposure s (fun i => (C i).exposure) ≠ 0) :
    (∏ i ∈ s, (C i).rateLikelihood rate) =
      theorem2ProcessLawCaseProductResidual s C *
        sourcePoissonPMF rate
          (totalExposure s fun i => (C i).exposure)
          (totalCount s fun i => (C i).count) := by
  simpa [theorem2ProcessLawCaseProductResidual,
    Theorem2ProcessLawCase.poissonFactorization, sourcePoissonPMF] using
      prod_poissonLikelihoodFactorization_eq_collapsed_countLikelihood
        s (fun i => (C i).poissonFactorization) rate h_totalExposure

/--
Finite-product decomposition for process-law cases at an explicit Poisson
rate, deriving nonzero total exposure from one positive observed exposure.
-/
theorem theorem1_process_law_rateLikelihood_product_decomposition_of_exists_pos_exposure
    {Incident : Type*} (s : Finset Incident)
    (C : Incident → Theorem2ProcessLawCase) (rate : ℝ)
    (h_exists : ∃ i ∈ s, 0 < (C i).exposure) :
    (∏ i ∈ s, (C i).rateLikelihood rate) =
      theorem2ProcessLawCaseProductResidual s C *
        sourcePoissonPMF rate
          (totalExposure s fun i => (C i).exposure)
          (totalCount s fun i => (C i).count) := by
  simpa [theorem2ProcessLawCaseProductResidual,
    Theorem2ProcessLawCase.poissonFactorization, sourcePoissonPMF] using
      prod_poissonLikelihoodFactorization_eq_collapsed_countLikelihood_of_exists_pos_exposure
        s (fun i => (C i).poissonFactorization) rate
        (fun i _hi => (C i).exposure_nonneg) h_exists

/--
Finite-product decomposition for process-law cases routed through the reusable
observed-arrival product theorem.  This keeps the paper-specific condition
residuals separate from the homogeneous Poisson arrival algebra.
-/
theorem theorem1_process_law_likelihood_product_decomposition_via_observed_arrivals
    {Ω Incident : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (s : Finset Incident) (C : Incident → Theorem2ProcessLawCase)
    (H : HomogeneousPoissonProcessLaw Ω P)
    (h_totalExposure :
      totalExposure s (fun i => (C i).exposure) ≠ 0) :
    (∏ i ∈ s, (C i).likelihood H) =
      ((∏ i ∈ s, (C i).conditionResidual) *
          theorem2ProcessLawCaseObservedArrivalProductResidual s C) *
        sourcePoissonPMF H.rate
          (totalExposure s fun i => (C i).exposure)
          (totalCount s fun i => (C i).count) := by
  classical
  have h_totalObserved :
      totalExposure s (fun i => (C i).observedArrivalCase.exposure) ≠ 0 := by
    simpa [totalExposure,
      Theorem2ProcessLawCase.exposure_eq_observedArrivalCase_exposure] using
      h_totalExposure
  calc
    (∏ i ∈ s, (C i).likelihood H)
        = ∏ i ∈ s,
            ((C i).conditionResidual *
              H.observedArrivalCaseLikelihood (C i).observedArrivalCase) := by
            refine Finset.prod_congr rfl ?_
            intro i _hi
            rw [(C i).likelihood_eq_conditionResidual_mul_processObservedArrivalCaseLikelihood H]
    _ = (∏ i ∈ s, (C i).conditionResidual) *
          (∏ i ∈ s, H.observedArrivalCaseLikelihood (C i).observedArrivalCase) := by
            rw [Finset.prod_mul_distrib]
    _ = (∏ i ∈ s, (C i).conditionResidual) *
          (ObservedArrivalCase.productResidual s
              (fun i => (C i).observedArrivalCase) *
            countLikelihood H.rate
              (totalExposure s fun i => (C i).observedArrivalCase.exposure)
              (totalCount s fun i => (C i).observedArrivalCase.count)) := by
            rw [H.observedArrivalCaseLikelihood_product_decomposition
              s (fun i => (C i).observedArrivalCase) h_totalObserved]
    _ = ((∏ i ∈ s, (C i).conditionResidual) *
          theorem2ProcessLawCaseObservedArrivalProductResidual s C) *
        sourcePoissonPMF H.rate
          (totalExposure s fun i => (C i).exposure)
          (totalCount s fun i => (C i).count) := by
            simp [theorem2ProcessLawCaseObservedArrivalProductResidual,
              sourcePoissonPMF, totalExposure, totalCount,
              Theorem2ProcessLawCase.exposure_eq_observedArrivalCase_exposure,
              Theorem2ProcessLawCase.count_eq_observedArrivalCase_count]
            ring

/--
Finite-product Theorem 1 decomposition for cases supplied by one combined
homogeneous Poisson process law.
-/
theorem theorem1_process_law_likelihood_product_decomposition
    {Ω Incident : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (s : Finset Incident) (C : Incident → Theorem2ProcessLawCase)
    (H : HomogeneousPoissonProcessLaw Ω P)
    (h_totalExposure :
      totalExposure s (fun i => (C i).exposure) ≠ 0) :
    (∏ i ∈ s, (C i).likelihood H) =
      theorem2ProcessLawCaseProductResidual s C *
        sourcePoissonPMF H.rate
          (totalExposure s fun i => (C i).exposure)
          (totalCount s fun i => (C i).count) := by
  calc
    (∏ i ∈ s, (C i).likelihood H)
        = ∏ i ∈ s, (C i).rateLikelihood H.rate := by
            refine Finset.prod_congr rfl ?_
            intro i _hi
            rw [(C i).likelihood_eq_conditionResidual_mul_observedArrivalCase_likelihood H]
            rfl
    _ = theorem2ProcessLawCaseProductResidual s C *
          sourcePoissonPMF H.rate
            (totalExposure s fun i => (C i).exposure)
            (totalCount s fun i => (C i).count) := by
          exact theorem1_process_law_rateLikelihood_product_decomposition
            s C H.rate h_totalExposure

/--
Finite-product decomposition for process-law cases induced directly by mathlib
Poisson increment laws and the canonical ordered-arrival density at the same
rate.
-/
theorem
    theorem1_process_law_likelihood_product_decomposition_from_poisson_increment_laws
    {Ω Incident : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (s : Finset Incident) (C : Incident → Theorem2ProcessLawCase)
    (H : HomogeneousPoissonCountingProcessByLaw Ω P)
    (h_totalExposure :
      totalExposure s (fun i => (C i).exposure) ≠ 0) :
    (∏ i ∈ s, (C i).likelihoodFromPoissonIncrementLaws H) =
      theorem2ProcessLawCaseProductResidual s C *
        sourcePoissonPMF H.rate
          (totalExposure s fun i => (C i).exposure)
          (totalCount s fun i => (C i).count) := by
  simpa [Theorem2ProcessLawCase.likelihoodFromPoissonIncrementLaws] using
    theorem1_process_law_likelihood_product_decomposition
      s C H.toHomogeneousPoissonProcessLaw h_totalExposure

/--
Finite-product decomposition for process-law cases induced directly by mathlib
Poisson increment laws, deriving nonzero total exposure from a positive
exposure witness.
-/
theorem
    theorem1_process_law_likelihood_product_decomposition_from_poisson_increment_laws_of_exists_pos_exposure
    {Ω Incident : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (s : Finset Incident) (C : Incident → Theorem2ProcessLawCase)
    (H : HomogeneousPoissonCountingProcessByLaw Ω P)
    (h_exists : ∃ i ∈ s, 0 < (C i).exposure) :
    (∏ i ∈ s, (C i).likelihoodFromPoissonIncrementLaws H) =
      theorem2ProcessLawCaseProductResidual s C *
        sourcePoissonPMF H.rate
          (totalExposure s fun i => (C i).exposure)
          (totalCount s fun i => (C i).count) := by
  calc
    (∏ i ∈ s, (C i).likelihoodFromPoissonIncrementLaws H)
        = ∏ i ∈ s, (C i).rateLikelihood H.rate := by
            refine Finset.prod_congr rfl ?_
            intro i _hi
            rw [(C i).likelihoodFromPoissonIncrementLaws_eq_rateLikelihood H]
    _ = theorem2ProcessLawCaseProductResidual s C *
          sourcePoissonPMF H.rate
            (totalExposure s fun i => (C i).exposure)
            (totalCount s fun i => (C i).count) := by
          exact theorem1_process_law_rateLikelihood_product_decomposition_of_exists_pos_exposure
            s C H.rate h_exists

/--
Finite-product decomposition for process-law cases, deriving the nonzero
total-exposure premise from a positive-exposure witness.
-/
theorem theorem1_process_law_likelihood_product_decomposition_of_exists_pos_exposure
    {Ω Incident : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (s : Finset Incident) (C : Incident → Theorem2ProcessLawCase)
    (H : HomogeneousPoissonProcessLaw Ω P)
    (h_exists : ∃ i ∈ s, 0 < (C i).exposure) :
    (∏ i ∈ s, (C i).likelihood H) =
      theorem2ProcessLawCaseProductResidual s C *
        sourcePoissonPMF H.rate
          (totalExposure s fun i => (C i).exposure)
          (totalCount s fun i => (C i).count) := by
  calc
    (∏ i ∈ s, (C i).likelihood H)
        = ∏ i ∈ s, (C i).rateLikelihood H.rate := by
            refine Finset.prod_congr rfl ?_
            intro i _hi
            rw [(C i).likelihood_eq_conditionResidual_mul_observedArrivalCase_likelihood H]
            rfl
    _ = theorem2ProcessLawCaseProductResidual s C *
          sourcePoissonPMF H.rate
            (totalExposure s fun i => (C i).exposure)
            (totalCount s fun i => (C i).count) := by
          exact theorem1_process_law_rateLikelihood_product_decomposition_of_exists_pos_exposure
            s C H.rate h_exists

/--
Appendix B.2 one-report jump-time factorization for a proper observation
window.  This removes the explicit nonzero-exposure premise from the
paper-facing jump-time route.
-/
theorem theorem2_one_report_proper_window_factorization
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
  exact theorem2_process_source_data_factorization
    (K.oneReportSourceDataFromOrderedWindow baseCount
      startTime endTime firstJumpTime h_window
      h_start_le_jump h_jump_le_end) rate

/--
Appendix B.2 multi-report jump-time factorization for a proper observation
window.  This removes the explicit nonzero-exposure premise from the
paper-facing jump-time route.
-/
theorem theorem2_multi_report_proper_window_factorization
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
  exact theorem2_process_source_data_factorization
    (K.multiReportSourceDataFromOrderedWindow baseCount count hcount
      startTime endTime jumpTime h_window hmono hlast) rate

/--
Zero-report Appendix B.2 row over the deterministic observation window realized
by a stopping observation window on one sample path.
-/
theorem theorem2_zero_report_stopping_window_at_sample_factorization
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration (Ω := Ω) ℝ mΩ}
    (K : Theorem2ConditionFunctions) (baseCount : ℕ)
    (W : StoppingObservationWindow 𝓕) (ω : Ω) (rate : ℝ) :
    (K.zeroReportSourceDataFromWindow baseCount
        (W.toObservationWindow ω)).likelihood rate =
      (K.zeroReportSourceDataFromWindow baseCount
        (W.toObservationWindow ω)).residual *
        sourcePoissonPMF rate (W.exposure ω) 0 := by
  rw [theorem2_process_source_data_factorization]
  rw [Theorem2ConditionFunctions.zeroReportSourceDataFromWindow_exposure]
  rw [Theorem2ConditionFunctions.zeroReportSourceDataFromWindow_count]
  rw [StoppingObservationWindow.toObservationWindow_exposure]

/--
Zero-report Appendix B.2 row over a realized stopping observation window, with
the residual written as the paper's `g(s) h_m(e)` term.
-/
theorem theorem2_zero_report_stopping_window_at_sample_factorization_explicit
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration (Ω := Ω) ℝ mΩ}
    (K : Theorem2ConditionFunctions) (baseCount : ℕ)
    (W : StoppingObservationWindow 𝓕) (ω : Ω) (rate : ℝ) :
    (K.zeroReportSourceDataFromWindow baseCount
        (W.toObservationWindow ω)).likelihood rate =
      theorem2ZeroReportResidual K.startDensity (K.endDensity baseCount) *
        sourcePoissonPMF rate (W.exposure ω) 0 := by
  rw [theorem2_zero_report_stopping_window_at_sample_factorization]
  rw [Theorem2ConditionFunctions.zeroReportSourceDataFromWindow_residual]

/--
One-report Appendix B.2 ordered-window row over the deterministic observation
window realized by a stopping observation window on one sample path.
-/
theorem theorem2_one_report_stopping_window_at_sample_factorization
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration (Ω := Ω) ℝ mΩ}
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
        sourcePoissonPMF rate (W.exposure ω) 1 := by
  rw [theorem2_process_source_data_factorization]
  rw [Theorem2ConditionFunctions.oneReportSourceDataFromOrderedWindow_exposure]
  rw [Theorem2ConditionFunctions.oneReportSourceDataFromOrderedWindow_count]
  rfl

/--
Multi-report Appendix B.2 ordered-window row over the deterministic observation
window realized by a stopping observation window on one sample path.
-/
theorem theorem2_multi_report_stopping_window_at_sample_factorization
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration (Ω := Ω) ℝ mΩ}
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
        sourcePoissonPMF rate (W.exposure ω) count := by
  rw [theorem2_process_source_data_factorization]
  rw [Theorem2ConditionFunctions.multiReportSourceDataFromOrderedWindow_exposure]
  rw [Theorem2ConditionFunctions.multiReportSourceDataFromOrderedWindow_count]
  rfl

/--
Source-shaped Appendix B.2 likelihood case.

This records the three cases used in the paper's proof after the conditional
kernel factors have been derived from Conditions 1/2 and Lemma 2.
-/
inductive Theorem2SourceCase where
  | zero (startDensity endDensity exposure : ℝ)
  | one
      (startDensity endDensityAfterJump endSurvivalIntegral exposure : ℝ)
      (exposure_ne_zero : exposure ≠ 0)
  | multi
      (startDensity endDensityAfterLastJump survivalIntegralProduct exposure : ℝ)
      (count : ℕ) (count_gt_one : 1 < count)
      (exposure_ne_zero : exposure ≠ 0)

namespace Theorem2SourceCase

/-- Exposure length `e-s` for a source-shaped Appendix B.2 case. -/
def exposure : Theorem2SourceCase → ℝ
  | zero _ _ exposure => exposure
  | one _ _ _ exposure _ => exposure
  | multi _ _ _ exposure _ _ _ => exposure

/-- Report count `M` for a source-shaped Appendix B.2 case. -/
def count : Theorem2SourceCase → ℕ
  | zero _ _ _ => 0
  | one _ _ _ _ _ => 1
  | multi _ _ _ _ count _ _ => count

/-- One-report source case built from a positive exposure premise. -/
def oneOfPos
    (startDensity endDensityAfterJump endSurvivalIntegral exposure : ℝ)
    (exposure_pos : 0 < exposure) : Theorem2SourceCase :=
  one startDensity endDensityAfterJump endSurvivalIntegral exposure
    (ne_of_gt exposure_pos)

/-- Multi-report source case built from a positive exposure premise. -/
def multiOfPos
    (startDensity endDensityAfterLastJump survivalIntegralProduct exposure : ℝ)
    (count : ℕ) (count_gt_one : 1 < count)
    (exposure_pos : 0 < exposure) : Theorem2SourceCase :=
  multi startDensity endDensityAfterLastJump survivalIntegralProduct
    exposure count count_gt_one (ne_of_gt exposure_pos)

/-- Likelihood expression for a source-shaped Appendix B.2 case. -/
def likelihood (C : Theorem2SourceCase) (rate : ℝ) : ℝ :=
  match C with
  | zero startDensity endDensity exposure =>
      theorem2ZeroReportLikelihood startDensity endDensity rate exposure
  | one startDensity endDensityAfterJump endSurvivalIntegral exposure _ =>
      theorem2OneReportLikelihood
        startDensity endDensityAfterJump endSurvivalIntegral rate exposure
  | multi startDensity endDensityAfterLastJump survivalIntegralProduct
      exposure count _ _ =>
      theorem2MultiReportLikelihood
        startDensity endDensityAfterLastJump survivalIntegralProduct
        rate exposure count

/-- Corrected rate-independent residual for a source-shaped Appendix B.2 case. -/
def residual : Theorem2SourceCase → ℝ
  | zero startDensity endDensity _ =>
      theorem2ZeroReportResidual startDensity endDensity
  | one startDensity endDensityAfterJump endSurvivalIntegral exposure _ =>
      theorem2OneReportKernelResidual
        startDensity endDensityAfterJump endSurvivalIntegral / exposure
  | multi startDensity endDensityAfterLastJump survivalIntegralProduct
      exposure count _ _ =>
      theorem2CorrectedResidual
        (theorem2MultiReportKernelResidual
          startDensity endDensityAfterLastJump survivalIntegralProduct)
        exposure count

end Theorem2SourceCase

namespace Theorem2ProcessKernelCase

/--
Collapse an explicit no-arrival/interarrival process-kernel case to the
source-shaped Appendix B.2 case after collecting the rate-dependent kernels.
-/
def toSourceCase : Theorem2ProcessKernelCase → Theorem2SourceCase
  | zero startDensity endDensity exposure =>
      Theorem2SourceCase.zero startDensity endDensity exposure
  | one startDensity endDensityAfterJump endSurvivalIntegral _ _ exposure
      _ h_exposure =>
      Theorem2SourceCase.one
        startDensity endDensityAfterJump endSurvivalIntegral exposure
        h_exposure
  | multi startDensity endDensityAfterLastJump survivalIntegralProduct
      exposure _ count hcount _ _ h_exposure =>
      Theorem2SourceCase.multi
        startDensity endDensityAfterLastJump survivalIntegralProduct
        exposure count hcount h_exposure

theorem toSourceCase_exposure
    (C : Theorem2ProcessKernelCase) :
    C.toSourceCase.exposure = C.exposure := by
  cases C <;> rfl

theorem toSourceCase_count
    (C : Theorem2ProcessKernelCase) :
    C.toSourceCase.count = C.count := by
  cases C <;> rfl

theorem toSourceCase_residual
    (C : Theorem2ProcessKernelCase) :
    C.toSourceCase.residual = C.residual := by
  cases C <;> rfl

/--
The explicit process-kernel likelihood is the collapsed source-case likelihood
after collecting the no-arrival/interarrival rate-dependent factors.
-/
theorem likelihood_eq_toSourceCase_likelihood
    (C : Theorem2ProcessKernelCase) (rate : ℝ) :
    C.likelihood rate = C.toSourceCase.likelihood rate := by
  cases C with
  | zero startDensity endDensity exposure =>
      simp [likelihood, toSourceCase, Theorem2SourceCase.likelihood,
        theorem2ZeroReportProcessKernelLikelihood,
        theorem2ZeroReportLikelihood, noArrivalProb]
  | one startDensity endDensityAfterJump endSurvivalIntegral gap tail exposure
      hexposure h_exposure =>
      simpa [likelihood, toSourceCase, Theorem2SourceCase.likelihood] using
        theorem2_one_report_kernel_collects
          (startDensity := startDensity)
          (endDensityAfterJump := endDensityAfterJump)
          (endSurvivalIntegral := endSurvivalIntegral)
          (rate := rate) (gap := gap) (tail := tail)
          (exposure := exposure) hexposure
  | multi startDensity endDensityAfterLastJump survivalIntegralProduct
      exposure tail count hcount gap hexposure h_exposure =>
      have hcard :
          (Finset.univ : Finset (Fin count)).card = count := by
        simp
      simpa [likelihood, toSourceCase, Theorem2SourceCase.likelihood] using
        theorem2_multi_report_kernel_collects
          (jumps := (Finset.univ : Finset (Fin count)))
          (startDensity := startDensity)
          (endDensityAfterLastJump := endDensityAfterLastJump)
          (survivalIntegralProduct := survivalIntegralProduct)
          (rate := rate) (exposure := exposure) (tail := tail)
          (count := count) gap hcard (by simpa using hexposure)

end Theorem2ProcessKernelCase

/-- Unified Appendix B.2 source-case factorization. -/
theorem theorem2_source_case_factorization
    (C : Theorem2SourceCase) (rate : ℝ) :
    C.likelihood rate =
      C.residual * sourcePoissonPMF rate C.exposure C.count := by
  cases C with
  | zero startDensity endDensity exposure =>
      simpa [Theorem2SourceCase.likelihood, Theorem2SourceCase.residual,
        Theorem2SourceCase.exposure, Theorem2SourceCase.count] using
          theorem2_zero_report_case_factorization
            startDensity endDensity rate exposure
  | one startDensity endDensityAfterJump endSurvivalIntegral exposure h_exposure =>
      simpa [Theorem2SourceCase.likelihood, Theorem2SourceCase.residual,
        Theorem2SourceCase.exposure, Theorem2SourceCase.count] using
          theorem2_one_report_case_factorization
            (startDensity := startDensity)
            (endDensityAfterJump := endDensityAfterJump)
            (endSurvivalIntegral := endSurvivalIntegral)
            (rate := rate) (exposure := exposure) h_exposure
  | multi startDensity endDensityAfterLastJump survivalIntegralProduct
      exposure count hcount h_exposure =>
      have hcase := theorem2_multi_report_case_factorization
        (startDensity := startDensity)
        (endDensityAfterLastJump := endDensityAfterLastJump)
        (survivalIntegralProduct := survivalIntegralProduct)
        (rate := rate) (exposure := exposure) (count := count)
        hcount h_exposure
      simpa [Theorem2SourceCase.likelihood, Theorem2SourceCase.residual,
        Theorem2SourceCase.exposure, Theorem2SourceCase.count] using hcase.2

/--
Explicit process-kernel cases factor through their collapsed source cases.
Thus the no-arrival/interarrival-kernel layer refines the source-shaped
algebraic layer.
-/
theorem theorem2_process_kernel_case_factorization_via_source_case
    (C : Theorem2ProcessKernelCase) (rate : ℝ) :
    C.likelihood rate =
      C.residual * sourcePoissonPMF rate C.exposure C.count := by
  calc
    C.likelihood rate = C.toSourceCase.likelihood rate := by
      exact C.likelihood_eq_toSourceCase_likelihood rate
    _ = C.toSourceCase.residual *
          sourcePoissonPMF rate C.toSourceCase.exposure
            C.toSourceCase.count := by
      exact theorem2_source_case_factorization C.toSourceCase rate
    _ = C.residual * sourcePoissonPMF rate C.exposure C.count := by
      rw [C.toSourceCase_residual, C.toSourceCase_exposure,
        C.toSourceCase_count]

/--
The printed `M > 1` residual equals the corrected residual only under this
explicit algebraic condition.  This isolates the proof-formula discrepancy
without changing the paper's main factorization theorem.
-/
theorem theorem2_printed_residual_eq_corrected_iff
    {kernelResidual exposure : ℝ} {count : ℕ} :
    theorem2PrintedMgtOneResidual kernelResidual exposure count =
        theorem2CorrectedResidual kernelResidual exposure count ↔
      kernelResidual * exposure ^ count / (count.factorial : ℝ) =
        kernelResidual * (count.factorial : ℝ) / exposure ^ count := by
  simp [theorem2PrintedMgtOneResidual, theorem2CorrectedResidual]

theorem theorem1_likelihood_factorization
    (F : PoissonLikelihoodFactorization) (rate : ℝ) :
    F.likelihood rate =
      F.residual * sourcePoissonPMF rate F.exposure F.count := by
  simpa [sourcePoissonPMF] using F.likelihood_eq rate

theorem theorem1_likelihood_factorization_commuted
    (F : PoissonLikelihoodFactorization) (rate : ℝ) :
    F.likelihood rate =
      sourcePoissonPMF rate F.exposure F.count * F.residual := by
  simpa [sourcePoissonPMF] using F.likelihood_eq_commuted rate

theorem theorem1_likelihood_factorization_from_raw_arrival
    (R : RawPoissonArrivalLikelihood) (rate : ℝ) :
    R.likelihood rate =
      R.correctedResidual * sourcePoissonPMF rate R.exposure R.count := by
  simpa [sourcePoissonPMF] using R.likelihood_eq_countLikelihood rate

/--
Finite-product version of Theorem 1's likelihood decomposition for incident
rows that already have individual Poisson likelihood-factorization
certificates.
-/
theorem theorem1_likelihood_product_decomposition
    {Incident : Type*} (s : Finset Incident)
    (F : Incident → PoissonLikelihoodFactorization) (rate : ℝ)
    (h_totalExposure :
      totalExposure s (fun i => (F i).exposure) ≠ 0) :
    (∏ i ∈ s, (F i).likelihood rate) =
      poissonLikelihoodFactorizationProductResidual s F *
        sourcePoissonPMF rate
          (totalExposure s fun i => (F i).exposure)
          (totalCount s fun i => (F i).count) := by
  simpa [sourcePoissonPMF] using
    prod_poissonLikelihoodFactorization_eq_collapsed_countLikelihood
      s F rate h_totalExposure

/--
Finite-product version of Theorem 1's likelihood decomposition for incident
rows with nonnegative exposures, deriving the denominator premise from one
positive exposure.
-/
theorem theorem1_likelihood_product_decomposition_of_exists_pos_exposure
    {Incident : Type*} (s : Finset Incident)
    (F : Incident → PoissonLikelihoodFactorization) (rate : ℝ)
    (h_exposure_nonneg : ∀ i ∈ s, 0 ≤ (F i).exposure)
    (h_exists : ∃ i ∈ s, 0 < (F i).exposure) :
    (∏ i ∈ s, (F i).likelihood rate) =
      poissonLikelihoodFactorizationProductResidual s F *
        sourcePoissonPMF rate
          (totalExposure s fun i => (F i).exposure)
          (totalCount s fun i => (F i).count) := by
  simpa [sourcePoissonPMF] using
    prod_poissonLikelihoodFactorization_eq_collapsed_countLikelihood_of_exists_pos_exposure
      s F rate h_exposure_nonneg h_exists

theorem mleRate_score_eq_zero
    {totalCount : ℕ} {totalExposure : ℝ}
    (hcount : totalCount ≠ 0) (hexposure : totalExposure ≠ 0) :
    poissonRateScore totalCount totalExposure
        (mleRate totalCount totalExposure) = 0 := by
  have hcount_real : (totalCount : ℝ) ≠ 0 := by
    exact_mod_cast hcount
  unfold poissonRateScore mleRate
  field_simp [hcount_real, hexposure]
  ring

/--
Eq. (3) global log-likelihood optimality over positive reporting rates, for
positive total exposure and nonzero total count.
-/
theorem mleRate_global_logLikelihood_max
    {totalCount : ℕ} {totalExposure rate : ℝ}
    (hcount : totalCount ≠ 0) (hexposure : 0 < totalExposure)
    (hrate : 0 < rate) :
    poissonRateLogLikelihood totalCount totalExposure rate ≤
      poissonRateLogLikelihood totalCount totalExposure
        (mleRate totalCount totalExposure) := by
  simpa [poissonRateLogLikelihood, mleRate] using
    poissonRateLogLikelihoodKernel_le_at_mle
      (count := totalCount) (exposure := totalExposure) (rate := rate)
      hcount hexposure hrate

/--
Finite-product likelihood shape behind Eq. (3): multiplying the incident
Poisson count factors leaves a rate-independent residual times
`rate^(sum counts) * exp(-rate * sum exposure)`.
-/
theorem observedIncidentLikelihoodProduct_eq_raw_shape
    {Incident : Type*} (s : Finset Incident)
    (rate : ℝ) (exposure : Incident → ℝ) (count : Incident → ℕ) :
    observedIncidentLikelihoodProduct s rate exposure count =
      observedIncidentLikelihoodProductResidual s exposure count *
        rate ^ totalObservedReportCount s count *
          Real.exp (-(rate * totalObservationExposure s exposure)) := by
  exact countLikelihoodProduct_eq_residual_rawShape s rate exposure count

/--
Finite-product likelihood as a single total-count Poisson PMF, up to a
rate-independent residual.
-/
theorem observedIncidentLikelihoodProduct_eq_total_pmf
    {Incident : Type*} (s : Finset Incident)
    (rate : ℝ) (exposure : Incident → ℝ) (count : Incident → ℕ)
    (h_totalExposure : totalObservationExposure s exposure ≠ 0) :
    observedIncidentLikelihoodProduct s rate exposure count =
      observedIncidentLikelihoodTotalPMFResidual s exposure count *
        sourcePoissonPMF rate
          (totalObservationExposure s exposure)
          (totalObservedReportCount s count) := by
  simpa [observedIncidentLikelihoodProduct, observedIncidentLikelihoodProductResidual,
    observedIncidentLikelihoodTotalPMFResidual, sourcePoissonPMF,
    totalObservationExposure, totalObservedReportCount] using
      countLikelihoodProduct_eq_residual_countLikelihood_total
        s rate exposure count h_totalExposure

/--
Finite-product likelihood as a single total-count Poisson PMF, deriving the
nonzero denominator from nonnegative incident exposures and one positive
incident exposure.
-/
theorem observedIncidentLikelihoodProduct_eq_total_pmf_of_exists_pos_exposure
    {Incident : Type*} (s : Finset Incident)
    (rate : ℝ) (exposure : Incident → ℝ) (count : Incident → ℕ)
    (h_exposure_nonneg : ∀ i ∈ s, 0 ≤ exposure i)
    (h_exists : ∃ i ∈ s, 0 < exposure i) :
    observedIncidentLikelihoodProduct s rate exposure count =
      observedIncidentLikelihoodTotalPMFResidual s exposure count *
        sourcePoissonPMF rate
          (totalObservationExposure s exposure)
          (totalObservedReportCount s count) := by
  simpa [observedIncidentLikelihoodProduct,
    observedIncidentLikelihoodTotalPMFResidual, sourcePoissonPMF,
    totalObservationExposure, totalObservedReportCount] using
      countLikelihoodProduct_eq_residual_countLikelihood_total_of_exists_pos_exposure
        s rate exposure count h_exposure_nonneg h_exists

/--
Finite stochastic construction behind Eq. (3): a finite incident-family
Poisson count certificate gives the paper's observed-incident product
likelihood as the joint count-event probability.
-/
theorem finitePoissonCountFamily_observedIncident_event_prob_eq_product
    {Ω Incident : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {rate : ℝ} {exposure : Incident → ℝ}
    (H : FinitePoissonCountFamily Ω P Incident rate exposure)
    (s : Finset Incident) (count : Incident → ℕ) :
    P.real (⋂ i ∈ s, {ω : Ω | H.count i ω = count i}) =
      observedIncidentLikelihoodProduct s rate exposure count := by
  simpa [observedIncidentLikelihoodProduct] using
    H.joint_real_eq_countLikelihoodProduct s count

/--
Finite stochastic construction behind Eq. (3), in the total-count PMF form:
the joint observed incident-count event has probability equal to the
rate-independent residual times one source Poisson PMF at total exposure and
total count.
-/
theorem finitePoissonCountFamily_observedIncident_event_prob_eq_total_pmf
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
  simpa [observedIncidentLikelihoodTotalPMFResidual,
    observedIncidentLikelihoodProductResidual, sourcePoissonPMF,
    totalObservationExposure, totalObservedReportCount] using
      H.joint_real_eq_residual_countLikelihood_total
        s h_totalExposure count

/--
Finite stochastic construction behind Eq. (3), in total-PMF form, deriving the
nonzero denominator from one positive finite-family exposure.
-/
theorem finitePoissonCountFamily_observedIncident_event_prob_eq_total_pmf_of_exists_pos_exposure
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
  simpa [observedIncidentLikelihoodTotalPMFResidual,
    observedIncidentLikelihoodProductResidual, sourcePoissonPMF,
    totalObservationExposure, totalObservedReportCount] using
      H.joint_real_eq_residual_countLikelihood_total_of_exists_pos_exposure
        s h_exists count

/--
Finite stochastic construction behind Eq. (3), summed over all incident count
vectors: for a finite incident family, the total observed report count has the
source Poisson PMF at total exposure.
-/
theorem finitePoissonCountFamily_totalObservedReportCount_event_prob_eq_total_pmf
    {Ω Incident : Type*} [MeasurableSpace Ω] [Fintype Incident]
    [DecidableEq Incident] {P : Measure Ω}
    {rate : ℝ} {exposure : Incident → ℝ}
    (H : FinitePoissonCountFamily Ω P Incident rate exposure)
    (totalReportCount : ℕ) :
    P.real {ω : Ω | (∑ i : Incident, H.count i ω) = totalReportCount} =
      sourcePoissonPMF rate
        (totalObservationExposure (Finset.univ : Finset Incident) exposure)
        totalReportCount := by
  simpa [sourcePoissonPMF, totalObservationExposure] using
    H.total_count_real_eq_countLikelihood totalReportCount

/--
Finite stochastic construction behind Eq. (3), summed over all count vectors in
an arbitrary finite incident set: the subfamily total observed report count has
the source Poisson PMF at subfamily total exposure.
-/
theorem finitePoissonCountFamily_totalObservedReportCount_event_prob_eq_total_pmf_finset
    {Ω Incident : Type*} [MeasurableSpace Ω] [DecidableEq Incident]
    {P : Measure Ω} {rate : ℝ} {exposure : Incident → ℝ}
    (H : FinitePoissonCountFamily Ω P Incident rate exposure)
    (s : Finset Incident) (totalReportCount : ℕ) :
    P.real {ω : Ω | (∑ i ∈ s, H.count i ω) = totalReportCount} =
      sourcePoissonPMF rate
        (totalObservationExposure s exposure)
        totalReportCount := by
  simpa [sourcePoissonPMF, totalObservationExposure] using
    H.total_count_real_eq_countLikelihood_finset s totalReportCount

theorem poissonRegressionRate_pos
    {Feature : Type*} [Fintype Feature]
    (alpha : ℝ) (beta theta : Feature → ℝ) :
    0 < poissonRegressionRate alpha beta theta := by
  exact Real.exp_pos _

theorem poissonRegressionRate_eq_logLink
    {Feature : Type*} [Fintype Feature]
    (alpha : ℝ) (beta theta : Feature → ℝ) :
    poissonRegressionRate alpha beta theta =
      Real.exp (alpha + ∑ j, beta j * theta j) := by
  rfl

theorem poissonRegressionIncidentLikelihood_eq_source
    {Feature : Type*} [Fintype Feature]
    (alpha : ℝ) (beta theta : Feature → ℝ)
    (exposure : ℝ) (count : ℕ) :
    poissonRegressionIncidentLikelihood alpha beta theta exposure count =
      sourcePoissonPMF
        (Real.exp (alpha + ∑ j, beta j * theta j)) exposure count := by
  rfl

theorem zeroInflatedIncidentLikelihood_zero
    (gamma rate exposure : ℝ) :
    zeroInflatedIncidentLikelihood gamma rate exposure 0 =
      gamma + (1 - gamma) * sourcePoissonPMF rate exposure 0 := by
  simp [zeroInflatedIncidentLikelihood, sourcePoissonPMF]

theorem zeroInflatedIncidentLikelihood_of_positive_count
    {gamma rate exposure : ℝ} {count : ℕ} (hcount : count ≠ 0) :
    zeroInflatedIncidentLikelihood gamma rate exposure count =
      (1 - gamma) * sourcePoissonPMF rate exposure count := by
  simpa [zeroInflatedIncidentLikelihood, sourcePoissonPMF] using
    zeroInflatedCountLikelihood_of_ne_zero
      (γ := gamma) (rate := rate) (exposure := exposure) hcount

theorem zeroInflatedRegressionIncidentLikelihood_zero
    {Feature : Type*} [Fintype Feature]
    (gamma alpha : ℝ) (beta theta : Feature → ℝ) (exposure : ℝ) :
    zeroInflatedRegressionIncidentLikelihood
        gamma alpha beta theta exposure 0 =
      gamma + (1 - gamma) *
        sourcePoissonPMF
          (Real.exp (alpha + ∑ j, beta j * theta j)) exposure 0 := by
  simp [zeroInflatedRegressionIncidentLikelihood,
    zeroInflatedIncidentLikelihood_zero, poissonRegressionRate]

theorem zeroInflatedRegressionIncidentLikelihood_of_positive_count
    {Feature : Type*} [Fintype Feature]
    {gamma alpha exposure : ℝ} {beta theta : Feature → ℝ} {count : ℕ}
    (hcount : count ≠ 0) :
    zeroInflatedRegressionIncidentLikelihood
        gamma alpha beta theta exposure count =
      (1 - gamma) *
        sourcePoissonPMF
          (Real.exp (alpha + ∑ j, beta j * theta j)) exposure count := by
  simp [zeroInflatedRegressionIncidentLikelihood,
    zeroInflatedIncidentLikelihood_of_positive_count hcount,
    poissonRegressionRate]

theorem zeroInflatedIncidentLikelihood_nonneg
    {gamma rate exposure : ℝ} {count : ℕ}
    (hgamma_nonneg : 0 ≤ gamma) (hgamma_le_one : gamma ≤ 1)
    (hmean : 0 ≤ rate * exposure) :
    0 ≤ zeroInflatedIncidentLikelihood gamma rate exposure count := by
  simpa [zeroInflatedIncidentLikelihood] using
    zeroInflatedCountLikelihood_nonneg
      (γ := gamma) (rate := rate) (exposure := exposure) (count := count)
      hgamma_nonneg hgamma_le_one hmean

end

end LBG24SpatialUnderreporting
