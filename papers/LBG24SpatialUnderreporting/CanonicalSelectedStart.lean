import LBG24SpatialUnderreporting.ConditionOneTail
import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalForwardPoisson

/-!
# Canonical selected-start Poisson tail for LBG24

This module connects the source-faithful Condition 1 selection assumption to
the *actual* count of the canonical forward Poisson process.  The selection
can depend on the first report and is conditionally independent of the whole
post-first-report tail, exactly as encoded by
`Theorem2ConditionOneSelection`.

The pathwise renewal identity holds on the full-measure set of positive,
nonexplosive interarrival paths.  We therefore transfer the event equality
through conditional expectation almost everywhere instead of pretending that
the identity holds on malformed null paths.

This is a paper-specific selected-start result, not a claim of the general
strong Markov property at an arbitrary stopped filtration.
-/

namespace LBG24SpatialUnderreporting

open MeasureTheory Filter ProbabilityTheory
open AppliedModelingLib.Probability.PoissonProcess
open scoped ENNReal NNReal

noncomputable section

/-- The canonical exponential-interarrival path space has its product Borel
sigma-algebra. -/
local instance : MeasurableSpace (ℕ → ℝ) := MeasurableSpace.pi

/-- The count in a duration `u` of a fresh post-first-report tail, starting
at the deterministic offset `s - t`. -/
def canonicalTailCount
    (u : ℝ≥0) (p : ℝ≥0 × ℝ≥0) (tail : ℕ → ℝ) : ℕ :=
  canonicalRenewalCount (((p.2 : ℝ) - (p.1 : ℝ)) + (u : ℝ)) tail -
    canonicalRenewalCount ((p.2 : ℝ) - (p.1 : ℝ)) tail

/-- Measurability of the deterministic-offset count in a canonical tail. -/
theorem measurable_canonicalTailCount (u : ℝ≥0) :
    Measurable fun x : (ℝ≥0 × ℝ≥0) × (ℕ → ℝ) =>
      canonicalTailCount u x.1 x.2 := by
  let d : (ℝ≥0 × ℝ≥0) × (ℕ → ℝ) → ℝ :=
    fun x => (x.1.2 : ℝ) - (x.1.1 : ℝ)
  have hd : Measurable d := by
    exact (measurable_fst.snd.coe_nnreal_real).sub
      (measurable_fst.fst.coe_nnreal_real)
  exact
    (measurable_canonicalRenewalCount_joint.comp
      ((hd.add measurable_const).prodMk measurable_snd)).sub
    (measurable_canonicalRenewalCount_joint.comp
      (hd.prodMk measurable_snd))

/-- A fresh canonical tail has the Poisson count law over every deterministic
nonnegative offset interval. -/
theorem canonicalTailCount_hasLaw_poisson
    {rate : ℝ} (hrate : 0 < rate) (u t s : ℝ≥0) (hts : t ≤ s) :
    ProbabilityTheory.HasLaw
      (canonicalTailCount u (t, s))
      (ProbabilityTheory.poissonMeasure
        (rateExposureParam rate (u : ℝ)
          (mul_nonneg hrate.le (NNReal.coe_nonneg u))))
      (exponentialInterarrivalMeasure rate) := by
  have hd : 0 ≤ (s : ℝ) - (t : ℝ) :=
    sub_nonneg.mpr (NNReal.coe_le_coe.mpr hts)
  simpa [canonicalTailCount, rateExposureParam] using
    canonicalRenewalCount_increment_hasLaw_poisson
      (s := (s : ℝ) - (t : ℝ)) (h := (u : ℝ)) hrate hd (NNReal.coe_nonneg u)

/-- Pathwise renewal identity behind the selected-start event representation.
It applies to any well-formed interarrival path and any scalar start after its
first arrival, so it can also be pulled back to a source carrier containing
auxiliary selection randomness. -/
theorem canonicalRenewalCount_postStart_zero_iff_canonicalTailNoArrival_of_good
    (path : ℕ → ℝ) (start u : ℝ≥0)
    (hstart : (canonicalFirstArrival path).toNNReal ≤ start)
    (hpos : ∀ n, 0 < path n)
    (htail : Tendsto (fun m : ℕ => futureArrivalTime 1 m path) atTop atTop) :
    canonicalRenewalCount ((start : ℝ) + (u : ℝ)) path -
        canonicalRenewalCount (start : ℝ) path = 0 ↔
      Theorem2ConditionOneSelection.canonicalTailNoArrival u
        ((canonicalFirstArrival path).toNNReal, start)
        (futureInterarrival 1 path) := by
  have hfirst_pos : 0 < canonicalFirstArrival path := by
    simpa [canonicalFirstArrival] using hpos 0
  have hfirstMax : max (canonicalFirstArrival path) 0 =
      arrivalPrefix 1 path := by
    rw [max_eq_left hfirst_pos.le]
    simp [canonicalFirstArrival, arrivalPrefix]
  let d : ℝ := (start : ℝ) - (canonicalFirstArrival path).toNNReal
  have hd : 0 ≤ d := by
    dsimp [d]
    exact sub_nonneg.mpr (NNReal.coe_le_coe.mpr hstart)
  have hdu : 0 ≤ d + (u : ℝ) := add_nonneg hd (NNReal.coe_nonneg u)
  have hstart_eq : (start : ℝ) = arrivalPrefix 1 path + d := by
    calc
      (start : ℝ) = ((canonicalFirstArrival path).toNNReal : ℝ) +
          ((start : ℝ) - ((canonicalFirstArrival path).toNNReal : ℝ)) := by ring
      _ = arrivalPrefix 1 path + d := by
        dsimp [d]
        rw [hfirstMax]
  have hcount_start := canonicalRenewalCount_arrivalPrefix_add
    1 d hd path hpos htail
  have hcount_startu := canonicalRenewalCount_arrivalPrefix_add
    1 (d + (u : ℝ)) hdu path hpos htail
  rw [hstart_eq]
  rw [add_assoc]
  rw [hcount_start, hcount_startu]
  simp only [Nat.add_sub_add_left]
  change canonicalRenewalCount (d + (u : ℝ)) (futureInterarrival 1 path) -
      canonicalRenewalCount d (futureInterarrival 1 path) = 0 ↔
    canonicalRenewalCount (d + (u : ℝ)) (futureInterarrival 1 path) =
      canonicalRenewalCount d (futureInterarrival 1 path)
  constructor
  · intro hzero
    have hle :
        canonicalRenewalCount (d + (u : ℝ)) (futureInterarrival 1 path) ≤
          canonicalRenewalCount d (futureInterarrival 1 path) :=
      Nat.sub_eq_zero_iff_le.mp hzero
    have hge :
        canonicalRenewalCount d (futureInterarrival 1 path) ≤
          canonicalRenewalCount (d + (u : ℝ))
            (futureInterarrival 1 path) := by
      have htailTail : Tendsto (fun m : ℕ =>
          arrivalTime m (futureInterarrival 1 path)) atTop atTop := by
        simpa only [futureArrivalTime_eq_arrivalTime_tail,
          Function.comp_apply] using htail
      have hmonoTail : Monotone fun t : ℝ =>
          canonicalRenewalCount t (futureInterarrival 1 path) :=
        canonicalRenewalCount_monotone_of_tendsto
          (futureInterarrival 1 path) htailTail
      exact hmonoTail (by linarith)
    exact Nat.le_antisymm hle hge
  · intro heq
    simp [heq]

/--
On the full-measure set of well-formed canonical renewal paths, the event of
no report in the actual forward Poisson count from a selected start is exactly
the no-arrival event in the post-first-report tail at the corresponding
offset.  The only pathwise premise on the selected start is the source
condition `T₁ ≤ S`.
-/
theorem ae_canonicalForward_postStart_zero_iff_canonicalTailNoArrival
    {rate : ℝ} (hrate : 0 < rate)
    (start : (ℕ → ℝ) → ℝ≥0)
    (hstart : ∀ ω, (canonicalFirstArrival ω).toNNReal ≤ start ω)
    (u : ℝ≥0) :
    ∀ᵐ ω ∂exponentialInterarrivalMeasure rate,
      forwardPostStopIntervalCount
          (canonicalForwardHomogeneousPoissonCountingProcessByLaw hrate)
          start u ω = 0 ↔
        Theorem2ConditionOneSelection.canonicalTailNoArrival u
          ((canonicalFirstArrival ω).toNNReal, start ω)
          (futureInterarrival 1 ω) := by
  have htailRaw : ∀ᵐ ω ∂exponentialInterarrivalMeasure rate,
      Tendsto (fun m : ℕ => arrivalTime m (futureInterarrival 1 ω)) atTop atTop := by
    have hmap : ∀ᵐ ξ ∂Measure.map (futureInterarrival 1)
        (exponentialInterarrivalMeasure rate),
        Tendsto (fun m : ℕ => arrivalTime m ξ) atTop atTop := by
      rw [(futureInterarrival_hasLaw_path hrate 1).map_eq]
      exact ae_arrivalTime_tendsto_atTop hrate
    exact (Measure.tendsto_ae_map
      (futureInterarrival_hasLaw_path hrate 1).aemeasurable) hmap
  have htail : ∀ᵐ ω ∂exponentialInterarrivalMeasure rate,
      Tendsto (fun m : ℕ => futureArrivalTime 1 m ω) atTop atTop := by
    filter_upwards [htailRaw] with ω hω
    simpa only [futureArrivalTime_eq_arrivalTime_tail, Function.comp_apply] using hω
  filter_upwards [ae_all_interarrival_positive hrate, htail] with ω hpos htail
  change canonicalRenewalCount ((start ω : ℝ) + (u : ℝ)) ω -
      canonicalRenewalCount (start ω : ℝ) ω = 0 ↔ _
  exact
    canonicalRenewalCount_postStart_zero_iff_canonicalTailNoArrival_of_good
      ω (start ω) u (hstart ω) hpos htail

/--
Concrete Appendix Lemma 2 for a canonical forward Poisson report process and
any source-valid Condition 1 selected start.  Conditional on the first report,
the actual interval count from that selected start has no report over `u` with
the Poisson zero-count probability.

The hypotheses identify the paper's first report and post-first-report path
with the canonical renewal representations.  All other selection assumptions
come from `Theorem2ConditionOneSelection` itself.
-/
theorem lemma2_canonicalForward_selectedStart_conditional_no_report
    {rate : ℝ} (hrate : 0 < rate) :
    letI : IsProbabilityMeasure (exponentialInterarrivalMeasure rate) :=
      isProbabilityMeasure_exponentialInterarrivalMeasure hrate
    ∀ (C : Theorem2ConditionOneSelection (ℕ → ℝ)
      (exponentialInterarrivalMeasure rate) (ℕ → ℝ)),
      C.firstReportTime =
        (fun ω : ℕ → ℝ => (canonicalFirstArrival ω).toNNReal) →
      C.postFirstReportTail = futureInterarrival 1 →
      ∀ (u : ℝ≥0), ∀ᵐ ω ∂exponentialInterarrivalMeasure rate,
      (ProbabilityTheory.condExpKernel (exponentialInterarrivalMeasure rate)
        (MeasurableSpace.comap C.firstReportTime inferInstance) ω).real
          {ω' | forwardPostStopIntervalCount
            (canonicalForwardHomogeneousPoissonCountingProcessByLaw hrate)
            C.startTime u ω' = 0} =
        noArrivalProb rate (u : ℝ) := by
  intro C hfirst htail u
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure rate) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  let H := canonicalForwardHomogeneousPoissonCountingProcessByLaw hrate
  let A : Set (ℕ → ℝ) := {ω | forwardPostStopIntervalCount H C.startTime u ω = 0}
  let B : Set (ℕ → ℝ) := {ω |
    Theorem2ConditionOneSelection.canonicalTailNoArrival u
      (C.firstReportTime ω, C.startTime ω) (C.postFirstReportTail ω)}
  have hstart : ∀ ω, (canonicalFirstArrival ω).toNNReal ≤ C.startTime ω := by
    intro ω
    simpa only [hfirst] using C.firstReport_le_start ω
  have hAB : ∀ᵐ ω ∂exponentialInterarrivalMeasure rate, ω ∈ A ↔ ω ∈ B := by
    simpa only [A, B, H, hfirst, htail] using
      ae_canonicalForward_postStart_zero_iff_canonicalTailNoArrival
        hrate C.startTime hstart u
  have hAfun : Measurable fun ω : ℕ → ℝ =>
      forwardPostStopIntervalCount H C.startTime u ω := by
    change Measurable (fun ω : ℕ → ℝ =>
      canonicalRenewalCount ((C.startTime ω : ℝ) + (u : ℝ)) ω -
        canonicalRenewalCount (C.startTime ω : ℝ) ω)
    have hstartReal : Measurable fun ω : ℕ → ℝ => (C.startTime ω : ℝ) :=
      C.startTime_measurable.coe_nnreal_real
    exact
      (measurable_canonicalRenewalCount_joint.comp
        ((hstartReal.add measurable_const).prodMk measurable_id)).sub
      (measurable_canonicalRenewalCount_joint.comp
        (hstartReal.prodMk measurable_id))
  have hBfun : Measurable fun ω : ℕ → ℝ =>
      Theorem2ConditionOneSelection.canonicalTailNoArrival u
        (C.firstReportTime ω, C.startTime ω) (C.postFirstReportTail ω) := by
    exact Theorem2ConditionOneSelection.measurable_canonicalTailNoArrival u |>.comp
      (C.selection_measurable.prodMk C.postFirstReportTail_measurable)
  have hA : MeasurableSet A := by
    simpa only [A, Set.preimage_setOf_eq] using hAfun (measurableSet_singleton 0)
  have hB : MeasurableSet B := by
    have hB_eq : B = (fun ω : ℕ → ℝ =>
        Theorem2ConditionOneSelection.canonicalTailNoArrival u
          (C.firstReportTime ω, C.startTime ω) (C.postFirstReportTail ω)) ⁻¹' {True} := by
      ext ω
      simp [B]
    rw [hB_eq]
    exact hBfun (measurableSet_singleton True)
  have hle : MeasurableSpace.comap C.firstReportTime inferInstance ≤
      (inferInstance : MeasurableSpace (ℕ → ℝ)) :=
    C.firstReportTime_measurable.comap_le
  letI : IsFiniteMeasure ((exponentialInterarrivalMeasure rate).trim hle) :=
    MeasureTheory.isFiniteMeasure_trim hle
  have hkernelA := ProbabilityTheory.condExpKernel_ae_eq_condExp
    (μ := exponentialInterarrivalMeasure rate)
    (m := MeasurableSpace.comap C.firstReportTime inferInstance) hle hA
  have hkernelB := ProbabilityTheory.condExpKernel_ae_eq_condExp
    (μ := exponentialInterarrivalMeasure rate)
    (m := MeasurableSpace.comap C.firstReportTime inferInstance) hle hB
  have hindicator :
      A.indicator (fun _ : ℕ → ℝ => (1 : ℝ)) =ᵐ[exponentialInterarrivalMeasure rate]
        B.indicator (fun _ : ℕ → ℝ => (1 : ℝ)) := by
    filter_upwards [hAB] with ω hω
    by_cases hAω : ω ∈ A
    · have hBω : ω ∈ B := hω.mp hAω
      simp [hAω, hBω]
    · have hBω : ω ∉ B := fun hb => hAω (hω.mpr hb)
      simp [hAω, hBω]
  have hcond := MeasureTheory.condExp_congr_ae
    (m := MeasurableSpace.comap C.firstReportTime inferInstance) hindicator
  have hkernelEq : ∀ᵐ ω ∂exponentialInterarrivalMeasure rate,
      (ProbabilityTheory.condExpKernel (exponentialInterarrivalMeasure rate)
        (MeasurableSpace.comap C.firstReportTime inferInstance) ω).real A =
      (ProbabilityTheory.condExpKernel (exponentialInterarrivalMeasure rate)
        (MeasurableSpace.comap C.firstReportTime inferInstance) ω).real B := by
    filter_upwards [hkernelA, hkernelB, hcond] with ω hAω hBω hcondω
    rw [hAω, hBω]
    exact hcondω
  have htailResult :=
    C.conditional_canonicalTailNoArrival_real_given_firstReport_of_canonicalFirstArrival
      hrate hfirst htail u
  filter_upwards [hkernelEq, htailResult] with ω hEq hTail
  change (ProbabilityTheory.condExpKernel (exponentialInterarrivalMeasure rate)
    (MeasurableSpace.comap C.firstReportTime inferInstance) ω).real A = _
  rw [hEq]
  exact hTail

/-- The same selected-start conclusion in the exponential survival-tail form
used in the paper's residual-waiting discussion. -/
theorem lemma2_canonicalForward_selectedStart_conditional_exponential_tail
    {rate : ℝ} (hrate : 0 < rate) :
    letI : IsProbabilityMeasure (exponentialInterarrivalMeasure rate) :=
      isProbabilityMeasure_exponentialInterarrivalMeasure hrate
    ∀ (C : Theorem2ConditionOneSelection (ℕ → ℝ)
      (exponentialInterarrivalMeasure rate) (ℕ → ℝ)),
      C.firstReportTime =
        (fun ω : ℕ → ℝ => (canonicalFirstArrival ω).toNNReal) →
      C.postFirstReportTail = futureInterarrival 1 →
      ∀ (u : ℝ≥0), ∀ᵐ ω ∂exponentialInterarrivalMeasure rate,
      (ProbabilityTheory.condExpKernel (exponentialInterarrivalMeasure rate)
        (MeasurableSpace.comap C.firstReportTime inferInstance) ω).real
          {ω' | forwardPostStopIntervalCount
            (canonicalForwardHomogeneousPoissonCountingProcessByLaw hrate)
            C.startTime u ω' = 0} =
        ((AppliedModelingLib.Probability.Exponential.Model.mk rate hrate).measure
          (Set.Ioi (u : ℝ))).toReal := by
  intro C hfirst htail u
  filter_upwards [lemma2_canonicalForward_selectedStart_conditional_no_report
    hrate C hfirst htail u] with ω hω
  rw [hω]
  exact noArrivalProb_eq_exponential_tail rate hrate (NNReal.coe_nonneg u)

/-- On the full-measure set of well-formed renewal paths, the actual forward
post-start count equals the corresponding deterministic-offset tail count. -/
theorem ae_canonicalForward_postStart_eq_canonicalTailCount
    {rate : ℝ} (hrate : 0 < rate)
    (start : (ℕ → ℝ) → ℝ≥0)
    (hstart : ∀ ω, (canonicalFirstArrival ω).toNNReal ≤ start ω)
    (u : ℝ≥0) :
    ∀ᵐ ω ∂exponentialInterarrivalMeasure rate,
      forwardPostStopIntervalCount
          (canonicalForwardHomogeneousPoissonCountingProcessByLaw hrate)
          start u ω =
        canonicalTailCount u
          ((canonicalFirstArrival ω).toNNReal, start ω)
          (futureInterarrival 1 ω) := by
  have htailRaw : ∀ᵐ ω ∂exponentialInterarrivalMeasure rate,
      Tendsto (fun m : ℕ => arrivalTime m (futureInterarrival 1 ω)) atTop atTop := by
    have hmap : ∀ᵐ ξ ∂Measure.map (futureInterarrival 1)
        (exponentialInterarrivalMeasure rate),
        Tendsto (fun m : ℕ => arrivalTime m ξ) atTop atTop := by
      rw [(futureInterarrival_hasLaw_path hrate 1).map_eq]
      exact ae_arrivalTime_tendsto_atTop hrate
    exact (Measure.tendsto_ae_map
      (futureInterarrival_hasLaw_path hrate 1).aemeasurable) hmap
  have htail : ∀ᵐ ω ∂exponentialInterarrivalMeasure rate,
      Tendsto (fun m : ℕ => futureArrivalTime 1 m ω) atTop atTop := by
    filter_upwards [htailRaw] with ω hω
    simpa only [futureArrivalTime_eq_arrivalTime_tail, Function.comp_apply] using hω
  filter_upwards [ae_all_interarrival_positive hrate, htail] with ω hpos htail
  have hfirst_pos : 0 < canonicalFirstArrival ω := by
    simpa [canonicalFirstArrival] using hpos 0
  have hfirstMax : max (canonicalFirstArrival ω) 0 = arrivalPrefix 1 ω := by
    rw [max_eq_left hfirst_pos.le]
    simp [canonicalFirstArrival, arrivalPrefix]
  let d : ℝ := (start ω : ℝ) - (canonicalFirstArrival ω).toNNReal
  have hd : 0 ≤ d := by
    dsimp [d]
    exact sub_nonneg.mpr (NNReal.coe_le_coe.mpr (hstart ω))
  have hdu : 0 ≤ d + (u : ℝ) := add_nonneg hd (NNReal.coe_nonneg u)
  have hstart_eq : (start ω : ℝ) = arrivalPrefix 1 ω + d := by
    calc
      (start ω : ℝ) = ((canonicalFirstArrival ω).toNNReal : ℝ) +
          ((start ω : ℝ) - ((canonicalFirstArrival ω).toNNReal : ℝ)) := by ring
      _ = arrivalPrefix 1 ω + d := by
        dsimp [d]
        rw [hfirstMax]
  have hcount_start := canonicalRenewalCount_arrivalPrefix_add
    1 d hd ω hpos htail
  have hcount_startu := canonicalRenewalCount_arrivalPrefix_add
    1 (d + (u : ℝ)) hdu ω hpos htail
  change canonicalRenewalCount ((start ω : ℝ) + (u : ℝ)) ω -
      canonicalRenewalCount (start ω : ℝ) ω = _
  rw [hstart_eq]
  rw [add_assoc]
  rw [hcount_start, hcount_startu]
  simp only [Nat.add_sub_add_left]
  rfl

/-- Atomwise fresh-tail Poisson law after conditioning on the canonical first
report.  This is the full-count strengthening of the zero-tail bridge. -/
theorem canonicalTailCount_conditional_atom_given_firstReport
    {rate : ℝ} (hrate : 0 < rate) :
    letI : IsProbabilityMeasure (exponentialInterarrivalMeasure rate) :=
      isProbabilityMeasure_exponentialInterarrivalMeasure hrate
    ∀ (C : Theorem2ConditionOneSelection (ℕ → ℝ)
      (exponentialInterarrivalMeasure rate) (ℕ → ℝ)),
      C.firstReportTime =
        (fun ω : ℕ → ℝ => (canonicalFirstArrival ω).toNNReal) →
      C.postFirstReportTail = futureInterarrival 1 →
      ∀ (u : ℝ≥0) (k : ℕ), ∀ᵐ ω ∂exponentialInterarrivalMeasure rate,
      (ProbabilityTheory.condExpKernel (exponentialInterarrivalMeasure rate)
        (MeasurableSpace.comap C.firstReportTime inferInstance) ω).real
          {ω' | canonicalTailCount u
            (C.firstReportTime ω', C.startTime ω')
            (C.postFirstReportTail ω') = k} =
        (ProbabilityTheory.poissonMeasure
          (rateExposureParam rate (u : ℝ)
            (mul_nonneg hrate.le (NNReal.coe_nonneg u)))).real {k} := by
  intro C hfirst htail u k
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure rate) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  apply C.conditional_postTailCount_atom_given_firstReport_of_tailKernel
    (postCount := canonicalTailCount u)
    (measurable_canonicalTailCount u)
    (Kernel.const ℝ≥0 (exponentialInterarrivalMeasure rate))
    (C.canonicalFirstArrivalSelection_tailKernel hrate hfirst htail)
    (ProbabilityTheory.poissonMeasure
      (rateExposureParam rate (u : ℝ)
        (mul_nonneg hrate.le (NNReal.coe_nonneg u))))
  intro t s k hts
  exact
    (hasLaw_poissonMeasure_real_singleton_eq_countLikelihood
      (mul_nonneg hrate.le (NNReal.coe_nonneg u))
      (canonicalTailCount_hasLaw_poisson hrate u t s hts) k).trans
    (countLikelihood_eq_poissonMeasure_real_singleton
      (mul_nonneg hrate.le (NNReal.coe_nonneg u)) k)

/--
Full count-law form of the canonical selected-start Lemma 2 bridge.  Given the
first report, the actual number of reports over the subsequent horizon has the
Poisson law of mean `rate * u`.  This is the post-start count law for the
concrete canonical source model; it does not assert a generic
stopped-filtration theorem.
-/
theorem lemma2_canonicalForward_selectedStart_conditional_count_hasLaw
    {rate : ℝ} (hrate : 0 < rate) :
    letI : IsProbabilityMeasure (exponentialInterarrivalMeasure rate) :=
      isProbabilityMeasure_exponentialInterarrivalMeasure hrate
    ∀ (C : Theorem2ConditionOneSelection (ℕ → ℝ)
      (exponentialInterarrivalMeasure rate) (ℕ → ℝ)),
      C.firstReportTime =
        (fun ω : ℕ → ℝ => (canonicalFirstArrival ω).toNNReal) →
      C.postFirstReportTail = futureInterarrival 1 →
      ∀ u : ℝ≥0, ∀ᵐ ω ∂exponentialInterarrivalMeasure rate,
      ProbabilityTheory.HasLaw
        (forwardPostStopIntervalCount
          (canonicalForwardHomogeneousPoissonCountingProcessByLaw hrate)
          C.startTime u)
        (ProbabilityTheory.poissonMeasure
          (rateExposureParam rate (u : ℝ)
            (mul_nonneg hrate.le (NNReal.coe_nonneg u))))
        (ProbabilityTheory.condExpKernel (exponentialInterarrivalMeasure rate)
          (MeasurableSpace.comap C.firstReportTime inferInstance) ω) := by
  intro C hfirst htail u
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure rate) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  let H := canonicalForwardHomogeneousPoissonCountingProcessByLaw hrate
  let Y : (ℕ → ℝ) → ℕ := forwardPostStopIntervalCount H C.startTime u
  let Z : (ℕ → ℝ) → ℕ := fun ω => canonicalTailCount u
    (C.firstReportTime ω, C.startTime ω) (C.postFirstReportTail ω)
  let ν : Measure ℕ := ProbabilityTheory.poissonMeasure
    (rateExposureParam rate (u : ℝ)
      (mul_nonneg hrate.le (NNReal.coe_nonneg u)))
  have hY : Measurable Y := by
    change Measurable (fun ω : ℕ → ℝ =>
      canonicalRenewalCount ((C.startTime ω : ℝ) + (u : ℝ)) ω -
        canonicalRenewalCount (C.startTime ω : ℝ) ω)
    have hstartReal : Measurable fun ω : ℕ → ℝ => (C.startTime ω : ℝ) :=
      C.startTime_measurable.coe_nnreal_real
    exact
      (measurable_canonicalRenewalCount_joint.comp
        ((hstartReal.add measurable_const).prodMk measurable_id)).sub
      (measurable_canonicalRenewalCount_joint.comp
        (hstartReal.prodMk measurable_id))
  have hZ : Measurable Z := by
    exact measurable_canonicalTailCount u |>.comp
      (C.selection_measurable.prodMk C.postFirstReportTail_measurable)
  have hYZ : Y =ᵐ[exponentialInterarrivalMeasure rate] Z := by
    simpa only [Y, Z, H, hfirst, htail] using
      ae_canonicalForward_postStart_eq_canonicalTailCount hrate C.startTime
        (by intro ω; simpa only [hfirst] using C.firstReport_le_start ω) u
  have hle : MeasurableSpace.comap C.firstReportTime inferInstance ≤
      (inferInstance : MeasurableSpace (ℕ → ℝ)) :=
    C.firstReportTime_measurable.comap_le
  letI : IsFiniteMeasure ((exponentialInterarrivalMeasure rate).trim hle) :=
    MeasureTheory.isFiniteMeasure_trim hle
  have htransfer : ∀ k : ℕ, ∀ᵐ ω ∂exponentialInterarrivalMeasure rate,
      (ProbabilityTheory.condExpKernel (exponentialInterarrivalMeasure rate)
        (MeasurableSpace.comap C.firstReportTime inferInstance) ω).real
          {ω' | Y ω' = k} =
      (ProbabilityTheory.condExpKernel (exponentialInterarrivalMeasure rate)
        (MeasurableSpace.comap C.firstReportTime inferInstance) ω).real
          {ω' | Z ω' = k} := by
    intro k
    let A : Set (ℕ → ℝ) := {ω | Y ω = k}
    let B : Set (ℕ → ℝ) := {ω | Z ω = k}
    have hA : MeasurableSet A := by
      simpa only [A, Set.preimage_setOf_eq] using hY (measurableSet_singleton k)
    have hB : MeasurableSet B := by
      simpa only [B, Set.preimage_setOf_eq] using hZ (measurableSet_singleton k)
    have hAB : ∀ᵐ ω ∂exponentialInterarrivalMeasure rate, ω ∈ A ↔ ω ∈ B := by
      filter_upwards [hYZ] with ω hω
      simp only [A, B, Set.mem_setOf_eq]
      exact hω ▸ Iff.rfl
    have hindicator :
        A.indicator (fun _ : ℕ → ℝ => (1 : ℝ)) =ᵐ[exponentialInterarrivalMeasure rate]
          B.indicator (fun _ : ℕ → ℝ => (1 : ℝ)) := by
      filter_upwards [hAB] with ω hω
      by_cases hAω : ω ∈ A
      · have hBω : ω ∈ B := hω.mp hAω
        simp [hAω, hBω]
      · have hBω : ω ∉ B := fun hb => hAω (hω.mpr hb)
        simp [hAω, hBω]
    have hkernelA := ProbabilityTheory.condExpKernel_ae_eq_condExp
      (μ := exponentialInterarrivalMeasure rate)
      (m := MeasurableSpace.comap C.firstReportTime inferInstance) hle hA
    have hkernelB := ProbabilityTheory.condExpKernel_ae_eq_condExp
      (μ := exponentialInterarrivalMeasure rate)
      (m := MeasurableSpace.comap C.firstReportTime inferInstance) hle hB
    have hcond := MeasureTheory.condExp_congr_ae
      (m := MeasurableSpace.comap C.firstReportTime inferInstance) hindicator
    filter_upwards [hkernelA, hkernelB, hcond] with ω hAω hBω hcondω
    rw [hAω, hBω]
    exact hcondω
  have hatoms : ∀ᵐ ω ∂exponentialInterarrivalMeasure rate, ∀ k : ℕ,
      (ProbabilityTheory.condExpKernel (exponentialInterarrivalMeasure rate)
        (MeasurableSpace.comap C.firstReportTime inferInstance) ω).real
          {ω' | Y ω' = k} = ν.real {k} := by
    rw [ae_all_iff]
    intro k
    filter_upwards [htransfer k,
      canonicalTailCount_conditional_atom_given_firstReport hrate C hfirst htail u k]
      with ω htransferω htailω
    exact htransferω.trans (by simpa only [ν] using htailω)
  filter_upwards [hatoms] with ω hω
  refine ⟨hY.aemeasurable, ?_⟩
  rw [MeasureTheory.ext_iff_measureReal_singleton]
  intro k
  rw [MeasureTheory.measureReal_def, MeasureTheory.measureReal_def,
    Measure.map_apply hY (measurableSet_singleton k)]
  exact hω k

end
end LBG24SpatialUnderreporting
