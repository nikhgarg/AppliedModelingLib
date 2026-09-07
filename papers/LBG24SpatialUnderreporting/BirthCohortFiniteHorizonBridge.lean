import AppliedModelingLib.Foundations.Probability.PoissonFiniteHorizonMarkedThinning

/-!
# Finite birth-cohort retention bridge for Lemma 1

The Appendix calculation for Lemma 1 can be read as a statement about a
*birth cohort*: count the incidents born in one fixed interval and retain an
incident exactly when its eventual report path contains at least one report
before the incident ends.  This module gives the finite-horizon consequence of
that reading using an actual finite vector of Boolean retention marks.

The model deliberately stops at a fixed cohort.  It does not identify a
retained incident with a first-report timestamp, construct a retained counting
process, assert consistency between different horizons, or assert steady-state
stationarity.  Those are separate obligations for the alternate temporal
reading of the paper.

The `iidRetentionLaw` field is the precise finite-horizon obligation that a
duration/report-path source model must discharge: conditional on the latent
birth count, the eventual-report indicators are iid Bernoulli with the stated
retention probability.  It is not inferred merely from the name of a reporting
process.
-/

namespace LBG24SpatialUnderreporting

open MeasureTheory ProbabilityTheory
open AppliedModelingLib.Probability.PoissonProcess
open AppliedModelingLib.Probability.FiniteHorizonMarkedPoisson
open scoped ENNReal NNReal ProbabilityTheory

noncomputable section

namespace BirthCohortFiniteHorizonBridge

/--
A fixed-window birth-cohort source model.  `latentBirthCount` counts births in
the window.  `retainedBirthCount` counts only those births whose own future
report history contains a report before that incident ends.  The latter is a
cohort label, not a count of reports whose timestamps fall in the window.
-/
structure BirthCohortRetentionSource
    (Omega : Type*) [MeasurableSpace Omega] (P : Measure Omega) where
  /-- Incident-birth rate for the fixed observation window. -/
  incidentRate : ℝ
  incidentRate_nonneg : 0 ≤ incidentRate
  /-- Length of the fixed birth-cohort window. -/
  exposure : ℝ
  exposure_nonneg : 0 ≤ exposure
  /-- Probability that one incident is eventually reported before it ends. -/
  retentionProbability : ℝ≥0
  retentionProbability_le_one : retentionProbability ≤ 1
  /-- The latent births and their actual eventual-report retention indicators. -/
  cohortSample : Omega → Sample
  /--
  Conditional iid retention obligation.  The sample's Boolean mark is `true`
  exactly for a birth retained by the source's duration/report criterion.
  -/
  iidRetentionLaw : HasLaw cohortSample
    (ofRateExposure incidentRate exposure
      (mul_nonneg incidentRate_nonneg exposure_nonneg)
      retentionProbability retentionProbability_le_one).toMeasure P
  /-- Source count of all births in the fixed window. -/
  latentBirthCount : Omega → ℕ
  /-- Source count of births eventually reported before their own endpoints. -/
  retainedBirthCount : Omega → ℕ
  latentBirthCount_eq_total : ∀ omega,
    latentBirthCount omega = total (cohortSample omega)
  retainedBirthCount_eq_kept : ∀ omega,
    retainedBirthCount omega = kept (cohortSample omega)

namespace BirthCohortRetentionSource

variable {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}

/-- The finite source's latent birth count has the advertised Poisson law. -/
theorem latentBirthCount_hasLaw
    (M : BirthCohortRetentionSource Omega P) :
    HasLaw M.latentBirthCount
      (poissonMeasure
        (rateExposureParam M.incidentRate M.exposure
          (mul_nonneg M.incidentRate_nonneg M.exposure_nonneg))) P := by
  have htotal : HasLaw (total ∘ M.cohortSample)
      (poissonMeasure
        (rateExposureParam M.incidentRate M.exposure
          (mul_nonneg M.incidentRate_nonneg M.exposure_nonneg))) P := by
    exact (ofRateExposure_total_hasLaw M.incidentRate M.exposure
      (mul_nonneg M.incidentRate_nonneg M.exposure_nonneg)
      M.retentionProbability M.retentionProbability_le_one).comp
        M.iidRetentionLaw
  apply htotal.congr
  filter_upwards [] with omega
  simpa [Function.comp_def] using M.latentBirthCount_eq_total omega

/--
The exact finite-horizon thinning conclusion for birth cohorts.  This is not a
claim about the time at which retained incidents first report.
-/
theorem retainedBirthCount_hasLaw
    (M : BirthCohortRetentionSource Omega P) :
    HasLaw M.retainedBirthCount
      (poissonMeasure
        (rateExposureParam M.incidentRate M.exposure
          (mul_nonneg M.incidentRate_nonneg M.exposure_nonneg) *
          M.retentionProbability)) P := by
  have hkept : HasLaw (kept ∘ M.cohortSample)
      (poissonMeasure
        (rateExposureParam M.incidentRate M.exposure
          (mul_nonneg M.incidentRate_nonneg M.exposure_nonneg) *
          M.retentionProbability)) P := by
    exact (ofRateExposure_kept_hasLaw M.incidentRate M.exposure
      (mul_nonneg M.incidentRate_nonneg M.exposure_nonneg)
      M.retentionProbability M.retentionProbability_le_one).comp
        M.iidRetentionLaw
  apply hkept.congr
  filter_upwards [] with omega
  simpa [Function.comp_def] using M.retainedBirthCount_eq_kept omega

/-- The finite cohort's retained-count probability mass in the Poisson form. -/
theorem retainedBirthCount_probability
    (M : BirthCohortRetentionSource Omega P) (n : ℕ) :
    P.real {omega : Omega | M.retainedBirthCount omega = n} =
      (poissonMeasure
        (rateExposureParam M.incidentRate M.exposure
          (mul_nonneg M.incidentRate_nonneg M.exposure_nonneg) *
          M.retentionProbability)).real {n} := by
  change (P (M.retainedBirthCount ⁻¹' ({n} : Set ℕ))).toReal =
    ((poissonMeasure
      (rateExposureParam M.incidentRate M.exposure
        (mul_nonneg M.incidentRate_nonneg M.exposure_nonneg) *
        M.retentionProbability)) {n}).toReal
  rw [← Measure.map_apply_of_aemeasurable
    (M.retainedBirthCount_hasLaw).aemeasurable (measurableSet_singleton n),
    M.retainedBirthCount_hasLaw.map_eq]

/-- A retained birth is a subset of the latent birth cohort, pointwise. -/
theorem retainedBirthCount_le_latentBirthCount
    (M : BirthCohortRetentionSource Omega P) (omega : Omega) :
    M.retainedBirthCount omega ≤ M.latentBirthCount omega := by
  rw [M.retainedBirthCount_eq_kept, M.latentBirthCount_eq_total]
  simpa [kept, keptInMarks, total] using Finset.card_le_card
    (Finset.subset_univ
      (AppliedModelingLib.successIndexSet (fun b : Bool => b = true)
        (M.cohortSample omega).marks))

end BirthCohortRetentionSource

end BirthCohortFiniteHorizonBridge

end

end LBG24SpatialUnderreporting
