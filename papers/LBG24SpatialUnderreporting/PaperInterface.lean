import LBG24SpatialUnderreporting.SourceTheoremModels
import LBG24SpatialUnderreporting.Assumptions
import LBG24SpatialUnderreporting.ObservationEndpointFormulas

/-!
# Source-facing interface: Quantifying Spatial Under-reporting Disparities

Each declaration below is one transparent semantic target for an independently
presented source result.  Proof endpoints live in `ProofInterface.lean`.
-/

namespace LBG24SpatialUnderreporting

open Filter MeasureTheory
open AppliedModelingLib.Probability.PoissonProcess
open scoped Function ProbabilityTheory Topology NNReal

noncomputable section

/-- Equation (2): on the source's positive Poisson-parameter domain, the
count mass has the displayed exponential/factorial form. -/
def sourceEquation2PoissonCountPMFSpec : Prop :=
  ∀ (rate exposure : ℝ) (count : ℕ), 0 < rate * exposure →
    sourcePoissonPMFOnSourceDomain rate exposure count =
      Real.exp (-(rate * exposure)) * (rate * exposure) ^ count /
        (count.factorial : ℝ)

/-- Source Lemma 1: the source's time-indexed incident and independent
first-report model induces a calendar-time observed-count process at the
displayed duration-mixture rate, including the zero-reporting boundary. -/
def sourceLemma1CalendarTimeDurationObservedProcessSpec
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

/-- Source Proposition 1: distinct reporting rates can induce the same
observable calendar-time first-report process rate.  The two supplied source
models make the paper's stationary-process premises explicit; their actual
calendar-window counts have the same Poisson rate and the stated large-time
limit. -/
def sourceProposition1CalendarTimeNonidentifiabilitySpec : Prop :=
  ∀ {Omega1 Omega2 : Type*}
      [MeasurableSpace Omega1] [MeasurableSpace Omega2]
      {P1 : Measure Omega1} {P2 : Measure Omega2}
      (M1 : Proposition1CalendarTimeDurationSourceModel Omega1 P1)
      (M2 : Proposition1CalendarTimeDurationSourceModel Omega2 P2)
      (observedRate : ℝ),
    0 < observedRate →
    M1.reportingRate ≠ M2.reportingRate →
    M1.durationDensity = M2.durationDensity →
    0 < continuousDurationFirstReportProbability
      M1.reportingRate M1.durationDensity →
    0 < continuousDurationFirstReportProbability
      M2.reportingRate M2.durationDensity →
    M1.calendarFirstReports.incidentRate =
      observedRate /
        continuousDurationFirstReportProbability
          M1.reportingRate M1.durationDensity →
    M2.calendarFirstReports.incidentRate =
      observedRate /
        continuousDurationFirstReportProbability
          M2.reportingRate M2.durationDensity →
      (∀ᵐ omega ∂P1,
        Tendsto (fun n : ℕ =>
          (M1.observedUniqueIncidentCount n omega : ℝ) / n)
          atTop (nhds observedRate)) ∧
      (∀ᵐ omega ∂P2,
        Tendsto (fun n : ℕ =>
          (M2.observedUniqueIncidentCount n omega : ℝ) / n)
          atTop (nhds observedRate)) ∧
      M1.reportingRate ≠ M2.reportingRate ∧
      ∃ observedProcess1 :
          ForwardHomogeneousPoissonCountingProcessByLaw Omega1 P1,
        ∃ observedProcess2 :
            ForwardHomogeneousPoissonCountingProcessByLaw Omega2 P2,
          observedProcess1.count = M1.calendarFirstReports.calendarCount ∧
          observedProcess2.count = M2.calendarFirstReports.calendarCount ∧
          observedProcess1.rate = observedRate ∧
          observedProcess2.rate = observedRate

/-- Source Lemma 2: after any Condition-1 selected start, the residual wait to
the next report has the exponential tail at the original reporting rate. -/
def sourceLemma2SelectedStartExponentialTailSpec
    {Omega : Type*} [MeasurableSpace Omega] [StandardBorelSpace Omega]
    {P : Measure Omega} [IsProbabilityMeasure P]
    (M : Lemma2ForwardSourceModel Omega P) : Prop :=
    ∀ u : ℝ≥0, ∀ᵐ omega ∂P,
        (ProbabilityTheory.condExpKernel P
          (MeasurableSpace.comap M.selection.firstReportTime inferInstance) omega).real
            {omega' | forwardPostStopIntervalCount M.process
              M.selection.startTime u omega' = 0} =
          ((AppliedModelingLib.Probability.Exponential.Model.mk
            M.rate M.rate_pos).measure
            (Set.Ioi (u : ℝ))).toReal

/-- Main Theorem 1 / Appendix Theorem 2: the fixed-history observation
likelihood factors into a rate-free residual and the Poisson count mass. -/
def sourceTheorem1LikelihoodDecompositionSpec
    (T : OrderedFiniteJumpTimeline)
    (M : AppendixTheorem2CausalStoppingSourceModel T.count)
    (D : AppendixTheorem2CausalStoppingSourceModel.EndpointDensityPresentation M)
    {rate : ℝ} (rate_pos : 0 < rate)
    (exposure_pos : 0 < T.window.exposure) : Prop :=
    AppendixTheorem2CausalStoppingSourceModel.conditionalLikelihood T M D rate =
        AppendixTheorem2CausalStoppingSourceModel.rateFreeResidual T M D *
          sourcePoissonPMFOnSourceDomain rate T.window.exposure T.count ∧
      RateIndependent (fun _rate : ℝ =>
        AppendixTheorem2CausalStoppingSourceModel.rateFreeResidual T M D)

/-- The homogeneous Poisson first-report delay has mean `1 / rate`. -/
def sourceHomogeneousReportingDelayMeanSpec : Prop :=
  ∀ (rate : ℝ) (rate_pos : 0 < rate),
    ∫ x, x ∂(AppliedModelingLib.Probability.Exponential.Model.mk
      rate rate_pos).measure = 1 / rate

/-- Equation (3), including the ordinary positive-exposure parameter-domain
clarification needed to interpret the displayed formula as an MLE. -/
def sourceEquation3MaximumLikelihoodEstimateSpec : Prop :=
  ∀ (totalCount : ℕ) (totalExposure : ℝ), 0 < totalExposure →
    mleRate totalCount totalExposure = (totalCount : ℝ) / totalExposure ∧
    (totalCount = 0 → ∀ rate : ℝ, 0 ≤ rate →
      poissonRateLogLikelihood totalCount totalExposure rate ≤
        poissonRateLogLikelihood totalCount totalExposure
          (mleRate totalCount totalExposure)) ∧
    (totalCount ≠ 0 → ∀ rate : ℝ, 0 < rate →
      poissonRateLogLikelihood totalCount totalExposure rate ≤
        poissonRateLogLikelihood totalCount totalExposure
          (mleRate totalCount totalExposure))

/-- Equation (6): substituting the paper's log-link rate into the causal
observation likelihood leaves a rate-free residual times the displayed
Poisson count mass. -/
def sourceEquation6PoissonRegressionLikelihoodSpec : Prop :=
  ∀ {Feature : Type*} [Fintype Feature]
      (alpha : ℝ) (beta theta : Feature → ℝ)
      (T : OrderedFiniteJumpTimeline)
      (M : AppendixTheorem2CausalStoppingSourceModel T.count)
      (D : AppendixTheorem2CausalStoppingSourceModel.EndpointDensityPresentation M)
      (exposure_pos : 0 < T.window.exposure),
      AppendixTheorem2CausalStoppingSourceModel.conditionalLikelihood T M D
          (poissonRegressionRate alpha beta theta) =
        AppendixTheorem2CausalStoppingSourceModel.rateFreeResidual T M D *
          sourcePoissonPMFOnSourceDomain
            (Real.exp (alpha + ∑ j, beta j * theta j))
            T.window.exposure T.count ∧
      RateIndependent (fun _rate : ℝ ↦
        AppendixTheorem2CausalStoppingSourceModel.rateFreeResidual T M D)

/-- Valid parameters for one incident in the source's zero-inflated model. -/
structure ZeroInflatedIncidentSourceModel where
  /-- Probability that this incident is in the one-report structural class. -/
  gamma : ℝ
  gamma_nonnegative : 0 ≤ gamma
  gamma_le_one : gamma ≤ 1
  /-- Positive duplicate-reporting rate in the ordinary Poisson class. -/
  rate : ℝ
  rate_pos : 0 < rate
  /-- Positive length of the observed interval, as required by the paper's
  Poisson-PMF parameter convention. -/
  exposure : ℝ
  exposure_pos : 0 < exposure

/-- The source's independence assumption across incidents is the product of
their observed duplicate-count mixture likelihoods. -/
def zeroInflatedIndependentIncidentFamilyLikelihood
    {Incident : Type*} (incidents : Finset Incident)
    (model : Incident → ZeroInflatedIncidentSourceModel)
    (count : Incident → ℕ) : ℝ :=
  ∏ i ∈ incidents,
    zeroInflatedIncidentLikelihood (model i).gamma (model i).rate
      (model i).exposure (count i)

/-- The source's zero-inflated extension, with probability, rate, and exposure
domains and the incident-level structural-zero semantics made explicit. -/
def sourceZeroInflatedLikelihoodExtensionSpec : Prop :=
  ∀ M : ZeroInflatedIncidentSourceModel,
    zeroInflatedIncidentLikelihood M.gamma M.rate M.exposure 0 =
      M.gamma + (1 - M.gamma) *
        sourcePoissonPMFOnSourceDomain M.rate M.exposure 0 ∧
    (∀ count : ℕ, 1 ≤ count →
      zeroInflatedIncidentLikelihood M.gamma M.rate M.exposure count =
        (1 - M.gamma) *
          sourcePoissonPMFOnSourceDomain M.rate M.exposure count) ∧
    (∀ {Incident : Type*} (incidents : Finset Incident)
        (model : Incident → ZeroInflatedIncidentSourceModel)
        (count : Incident → ℕ),
      zeroInflatedIndependentIncidentFamilyLikelihood incidents model count =
        ∏ i ∈ incidents,
          zeroInflatedIncidentLikelihood (model i).gamma (model i).rate
            (model i).exposure (count i))

/-- Appendix D.8.2: conditional on the first jump, the complete future
interarrival sequence retains the iid exponential law at the same rate. -/
def sourcePostFirstJumpPoissonShiftSpec : Prop :=
  ∀ {Omega : Type*} [MeasurableSpace Omega] [StandardBorelSpace Omega]
      {P : Measure Omega} [IsProbabilityMeasure P]
      (M : Lemma2ForwardSourceModel Omega P),
    ProbabilityTheory.condDistrib M.selection.postFirstReportTail
      M.selection.firstReportTime P =ᵐ[P.map M.selection.firstReportTime]
        ProbabilityTheory.Kernel.const ℝ≥0
          (exponentialInterarrivalMeasure M.rate)

end

end LBG24SpatialUnderreporting
