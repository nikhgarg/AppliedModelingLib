import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalFiniteDensity
import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalBoundedStoppingBlock
import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalUnboundedStopping
import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalRenewalCount

/-!
# Actual one-arrival density for the forward canonical Poisson construction

This module proves a genuine subprobability-measure equality for one observed
arrival before a deterministic horizon.  It bridges the canonical iid
exponential renewal path to the density `rate * exp (-rate * horizon)` on the
one-dimensional ordered arrival region.  The arbitrary finite ordered-arrival
version remains a separate induction over terminal survival slices.
-/

namespace LBG24SpatialUnderreporting

open MeasureTheory Filter ProbabilityTheory
open AppliedModelingLib.Probability.PoissonProcess
open scoped ENNReal NNReal ProbabilityTheory

noncomputable section

/-- The two-gap event that a deterministic horizon contains exactly one arrival. -/
def oneArrivalPairEvent (horizon : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ≤ horizon ∧ horizon < p.1 + p.2}

/-- The Lebesgue density of one arrival before a deterministic horizon. -/
noncomputable def oneArrivalDensity (rate horizon : ℝ) : ℝ → ℝ≥0∞ :=
  (Set.Icc (0 : ℝ) horizon).indicator
    (fun _ => ENNReal.ofReal (rate * Real.exp (-(rate * horizon))))

theorem measurable_oneArrivalDensity (rate horizon : ℝ) :
    Measurable (oneArrivalDensity rate horizon) := by
  exact measurable_const.indicator measurableSet_Icc

/-- The first two canonical interarrival coordinates in pair form. -/
def firstTwoGaps : (ℕ → ℝ) → ℝ × ℝ :=
  fun ω => (interarrival 0 ω, interarrival 1 ω)

theorem measurable_firstTwoGaps : Measurable firstTwoGaps := by
  exact (measurable_interarrival 0).prodMk (measurable_interarrival 1)

theorem canonicalRenewalCount_one_iff_firstTwoGaps_event
    (horizon : ℝ) (ω : ℕ → ℝ) :
    canonicalRenewalCount horizon ω = 1 ↔ firstTwoGaps ω ∈ oneArrivalPairEvent horizon := by
  have hzero : arrivalTime 0 ω = interarrival 0 ω := by
    simp [arrivalTime]
  have hone : arrivalTime 1 ω = interarrival 0 ω + interarrival 1 ω := by
    norm_num [arrivalTime, Finset.sum_range_succ]
  simpa [hzero, hone, firstTwoGaps, oneArrivalPairEvent, and_comm] using
    (canonicalRenewalCount_eq_succ_iff horizon ω 0)

theorem firstTwoGaps_hasLaw_prod_expMeasure
    {rate : ℝ} (hrate : 0 < rate) :
    HasLaw firstTwoGaps
      ((expMeasure rate).prod (expMeasure rate))
      (exponentialInterarrivalMeasure rate) := by
  let μ : Measure ℝ := expMeasure rate
  letI : IsProbabilityMeasure μ := by
    simpa [μ] using isProbabilityMeasure_expMeasure hrate
  have hpair : HasLaw
      (MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) → ℝ × ℝ)
      (μ.prod μ) (Measure.pi fun _ : Fin 2 => μ) :=
    ⟨MeasurableEquiv.finTwoArrow.measurable.aemeasurable,
      (MeasureTheory.measurePreserving_finTwoArrow μ).map_eq⟩
  have hcomp := hpair.comp (interarrivalBlock_hasLaw hrate 0 2)
  apply hcomp.congr
  filter_upwards [] with ω
  change (interarrival 0 ω, interarrival 1 ω) =
    MeasurableEquiv.finTwoArrow (interarrivalBlock 0 2 ω)
  rw [MeasurableEquiv.finTwoArrow_apply]
  simp [interarrivalBlock]

/-- The first two uninspected gaps after a prefix stopping index, in pair form. -/
def postStopFirstTwoGaps (τ : PrefixStoppingIndex) :
    (ℕ → ℝ) → ℝ × ℝ :=
  MeasurableEquiv.finTwoArrow ∘ τ.postInterarrivalBlock 2

/-- The first uninspected gap after a prefix stopping index. -/
def postStopFirstGap (τ : PrefixStoppingIndex) : (ℕ → ℝ) → ℝ :=
  fun ω => τ.postInterarrivalBlock 2 ω 0

/-- The event that the first two post-stop gaps contain exactly one arrival. -/
def postStopOneArrivalEvent (τ : PrefixStoppingIndex) (horizon : ℝ) :
    Set (ℕ → ℝ) :=
  postStopFirstTwoGaps τ ⁻¹' oneArrivalPairEvent horizon

theorem measurable_postStopFirstTwoGaps (τ : PrefixStoppingIndex) :
    Measurable (postStopFirstTwoGaps τ) := by
  exact MeasurableEquiv.finTwoArrow.measurable.comp
    (τ.measurable_postInterarrivalBlock 2)

theorem measurable_postStopFirstGap (τ : PrefixStoppingIndex) :
    Measurable (postStopFirstGap τ) := by
  exact (measurable_pi_apply (0 : Fin 2)).comp
    (τ.measurable_postInterarrivalBlock 2)

theorem postStopFirstGap_eq_fst_comp_firstTwoGaps (τ : PrefixStoppingIndex) :
    postStopFirstGap τ = Prod.fst ∘ postStopFirstTwoGaps τ := by
  funext ω
  simp [postStopFirstGap, postStopFirstTwoGaps, Function.comp_def,
    MeasurableEquiv.finTwoArrow_apply]

theorem postStopFirstTwoGaps_hasLaw_prod_expMeasure
    {rate : ℝ} (hrate : 0 < rate) (τ : PrefixStoppingIndex) :
    HasLaw (postStopFirstTwoGaps τ)
      ((expMeasure rate).prod (expMeasure rate))
      (exponentialInterarrivalMeasure rate) := by
  let μ : Measure ℝ := expMeasure rate
  letI : IsProbabilityMeasure μ := by
    simpa [μ] using isProbabilityMeasure_expMeasure hrate
  have hpair : HasLaw
      (MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) → ℝ × ℝ)
      (μ.prod μ) (Measure.pi fun _ : Fin 2 => μ) :=
    ⟨MeasurableEquiv.finTwoArrow.measurable.aemeasurable,
      (MeasureTheory.measurePreserving_finTwoArrow μ).map_eq⟩
  simpa [postStopFirstTwoGaps] using
    hpair.comp (τ.postInterarrivalBlock_hasLaw hrate 2)

theorem measurableSet_oneArrivalPairEvent (horizon : ℝ) :
    MeasurableSet (oneArrivalPairEvent horizon) := by
  exact (measurableSet_le measurable_fst measurable_const).inter
    (measurableSet_lt measurable_const (measurable_fst.add measurable_snd))

private theorem expMeasure_Ioi_eq_ofReal_exp
    {rate threshold : ℝ} (hrate : 0 < rate) (hthreshold : 0 ≤ threshold) :
    expMeasure rate (Set.Ioi threshold) =
      ENNReal.ofReal (Real.exp (-(rate * threshold))) := by
  let model : AppliedModelingLib.Probability.Exponential.Model := ⟨rate, hrate⟩
  letI : IsProbabilityMeasure (expMeasure rate) :=
    isProbabilityMeasure_expMeasure hrate
  apply (ENNReal.toReal_eq_toReal_iff'
    (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
  change (model.measure (Set.Ioi threshold)).toReal =
    (ENNReal.ofReal (Real.exp (-(rate * threshold)))).toReal
  rw [model.measure_Ioi_toReal hthreshold]
  exact (ENNReal.toReal_ofReal (le_of_lt (Real.exp_pos _))).symm

private theorem measurable_terminalTailDensity (rate horizon : ℝ) :
    Measurable (fun x : ℝ =>
      ENNReal.ofReal (Real.exp (-(rate * (horizon - x))))) := by
  fun_prop

private theorem exponentialPDF_mul_terminalTail_eq_oneArrivalDensity
    {rate horizon x : ℝ} (hrate : 0 < rate) (hx0 : 0 ≤ x) (hxh : x ≤ horizon) :
    exponentialPDF rate x * ENNReal.ofReal (Real.exp (-(rate * (horizon - x)))) =
      oneArrivalDensity rate horizon x := by
  have hmem : x ∈ Set.Icc (0 : ℝ) horizon := ⟨hx0, hxh⟩
  simp only [oneArrivalDensity, Set.indicator_of_mem hmem]
  rw [exponentialPDF_of_nonneg hx0]
  rw [← ENNReal.ofReal_mul
    (mul_nonneg (le_of_lt hrate) (le_of_lt (Real.exp_pos _)))]
  congr 1
  calc
    rate * Real.exp (-(rate * x)) * Real.exp (-(rate * (horizon - x))) =
        rate * (Real.exp (-(rate * x)) * Real.exp (-(rate * (horizon - x)))) := by
      ring
    _ = rate * Real.exp (-(rate * x) + -(rate * (horizon - x))) := by
      rw [Real.exp_add]
    _ = rate * Real.exp (-(rate * horizon)) := by
      congr 2
      ring

private theorem exponentialPDF_mul_terminalTail_eq_zero_of_neg
    {rate horizon x : ℝ} (hx : x < 0) :
    exponentialPDF rate x * ENNReal.ofReal (Real.exp (-(rate * (horizon - x)))) =
      oneArrivalDensity rate horizon x := by
  have hxnot : x ∉ Set.Icc (0 : ℝ) horizon := by
    intro hxmem
    exact (not_le_of_gt hx) hxmem.1
  rw [exponentialPDF_of_neg hx, oneArrivalDensity,
    Set.indicator_of_notMem hxnot _]
  simp

theorem oneArrivalPair_projection_apply
    {rate horizon : ℝ} (hrate : 0 < rate) (B : Set ℝ) (hB : MeasurableSet B) :
    Measure.map Prod.fst (((expMeasure rate).prod (expMeasure rate)).restrict
      (oneArrivalPairEvent horizon)) B =
      ∫⁻ x, expMeasure rate
        (Prod.mk x ⁻¹' (Prod.fst ⁻¹' B ∩ oneArrivalPairEvent horizon)) ∂expMeasure rate := by
  letI : IsProbabilityMeasure (expMeasure rate) :=
    isProbabilityMeasure_expMeasure hrate
  rw [Measure.map_apply measurable_fst hB]
  rw [Measure.restrict_apply (measurable_fst hB)]
  rw [Measure.prod_apply ((measurable_fst hB).inter
    (measurableSet_oneArrivalPairEvent horizon))]

private theorem preimage_fst_inter_oneArrivalPairEvent
    (B : Set ℝ) (horizon x : ℝ) [Decidable (x ∈ B ∩ Set.Iic horizon)] :
    Prod.mk x ⁻¹' (Prod.fst ⁻¹' B ∩ oneArrivalPairEvent horizon) =
      if x ∈ B ∩ Set.Iic horizon then Set.Ioi (horizon - x) else ∅ := by
  classical
  by_cases hx : x ∈ B ∩ Set.Iic horizon
  · ext y
    rw [if_pos hx]
    change (x ∈ B ∧ x ≤ horizon ∧ horizon < x + y) ↔ horizon - x < y
    constructor
    · rintro ⟨hxB, hxle, hxy⟩
      exact by linarith
    · intro hy
      exact ⟨hx.1, hx.2, by linarith⟩
  · ext y
    rw [if_neg hx]
    change (x ∈ B ∧ x ≤ horizon ∧ horizon < x + y) ↔ False
    constructor
    · rintro ⟨hxB, hxle, _⟩
      exact False.elim (hx ⟨hxB, hxle⟩)
    · exact False.elim

theorem oneArrivalPair_projection_apply_slice
    {rate horizon : ℝ} (hrate : 0 < rate) (B : Set ℝ) (hB : MeasurableSet B) :
    Measure.map Prod.fst (((expMeasure rate).prod (expMeasure rate)).restrict
      (oneArrivalPairEvent horizon)) B =
      ∫⁻ x in B ∩ Set.Iic horizon,
        expMeasure rate (Set.Ioi (horizon - x)) ∂expMeasure rate := by
  classical
  rw [oneArrivalPair_projection_apply hrate B hB]
  calc
    ∫⁻ x, expMeasure rate
        (Prod.mk x ⁻¹' (Prod.fst ⁻¹' B ∩ oneArrivalPairEvent horizon)) ∂expMeasure rate =
        ∫⁻ x, (B ∩ Set.Iic horizon).indicator
          (fun x => expMeasure rate (Set.Ioi (horizon - x))) x ∂expMeasure rate := by
      apply lintegral_congr
      intro x
      rw [preimage_fst_inter_oneArrivalPairEvent B horizon x]
      by_cases hx : x ∈ B ∩ Set.Iic horizon <;> simp [hx]
    _ = ∫⁻ x in B ∩ Set.Iic horizon,
        expMeasure rate (Set.Ioi (horizon - x)) ∂expMeasure rate := by
      rw [MeasureTheory.lintegral_indicator (hB.inter measurableSet_Iic)]

private theorem setLIntegral_oneArrivalDensity_inter_Iic
    (rate horizon : ℝ) (B : Set ℝ) (hB : MeasurableSet B) :
    ∫⁻ x in B ∩ Set.Iic horizon, oneArrivalDensity rate horizon x ∂volume =
      ∫⁻ x in B, oneArrivalDensity rate horizon x ∂volume := by
  classical
  rw [← MeasureTheory.lintegral_indicator (hB.inter measurableSet_Iic),
    ← MeasureTheory.lintegral_indicator hB]
  apply lintegral_congr
  intro x
  by_cases hxB : x ∈ B
  · by_cases hxh : x ≤ horizon
    · have hleft : x ∈ B ∩ Set.Iic horizon := ⟨hxB, hxh⟩
      rw [Set.indicator_of_mem hleft _, Set.indicator_of_mem hxB _]
    · have hleft : x ∉ B ∩ Set.Iic horizon := by
        intro hmem
        exact hxh hmem.2
      have hdensity : oneArrivalDensity rate horizon x = 0 := by
        have hnot : x ∉ Set.Icc (0 : ℝ) horizon := by
          intro hmem
          exact hxh hmem.2
        rw [oneArrivalDensity, Set.indicator_of_notMem hnot _]
      rw [Set.indicator_of_notMem hleft _, Set.indicator_of_mem hxB _, hdensity]
  · have hleft : x ∉ B ∩ Set.Iic horizon := by
      intro hmem
      exact hxB hmem.1
    rw [Set.indicator_of_notMem hleft _, Set.indicator_of_notMem hxB _]

/--
The first post-start gap, restricted to exactly one arrival before a fixed
horizon, has density `rate * exp (-rate * horizon)` on `[0, horizon]`.
-/
theorem oneArrivalPair_projection_eq_withDensity
    {rate horizon : ℝ} (hrate : 0 < rate) :
    Measure.map Prod.fst (((expMeasure rate).prod (expMeasure rate)).restrict
      (oneArrivalPairEvent horizon)) =
      volume.withDensity (oneArrivalDensity rate horizon) := by
  apply Measure.ext
  intro B hB
  calc
    Measure.map Prod.fst (((expMeasure rate).prod (expMeasure rate)).restrict
        (oneArrivalPairEvent horizon)) B =
        ∫⁻ x in B ∩ Set.Iic horizon,
          expMeasure rate (Set.Ioi (horizon - x)) ∂expMeasure rate := by
      exact oneArrivalPair_projection_apply_slice hrate B hB
    _ = ∫⁻ x in B ∩ Set.Iic horizon,
        ENNReal.ofReal (Real.exp (-(rate * (horizon - x)))) ∂expMeasure rate := by
      apply MeasureTheory.setLIntegral_congr_fun (hB.inter measurableSet_Iic)
      intro x hx
      exact expMeasure_Ioi_eq_ofReal_exp hrate (sub_nonneg.mpr hx.2)
    _ = ∫⁻ x in B ∩ Set.Iic horizon,
        exponentialPDF rate x *
          ENNReal.ofReal (Real.exp (-(rate * (horizon - x)))) ∂volume := by
      rw [show expMeasure rate = volume.withDensity (exponentialPDF rate) by rfl]
      exact MeasureTheory.setLIntegral_withDensity_eq_setLIntegral_mul volume
        (AppliedModelingLib.Probability.PoissonProcess.measurable_exponentialPDF rate)
        (measurable_terminalTailDensity rate horizon)
        (hB.inter measurableSet_Iic)
    _ = ∫⁻ x in B ∩ Set.Iic horizon,
        oneArrivalDensity rate horizon x ∂volume := by
      apply MeasureTheory.setLIntegral_congr_fun (hB.inter measurableSet_Iic)
      intro x hx
      change exponentialPDF rate x *
        ENNReal.ofReal (Real.exp (-(rate * (horizon - x)))) =
          oneArrivalDensity rate horizon x
      by_cases hx0 : 0 ≤ x
      · exact exponentialPDF_mul_terminalTail_eq_oneArrivalDensity hrate hx0 hx.2
      · exact exponentialPDF_mul_terminalTail_eq_zero_of_neg (lt_of_not_ge hx0)
    _ = ∫⁻ x in B, oneArrivalDensity rate horizon x ∂volume := by
      exact setLIntegral_oneArrivalDensity_inter_Iic rate horizon B hB
    _ = (volume.withDensity (oneArrivalDensity rate horizon)) B := by
      exact (MeasureTheory.withDensity_apply _ hB).symm

/--
Canonical renewal-path form of the one-arrival ordered-density theorem.
It establishes a measure equality for the actual first arrival epoch, not a
normalization identity for a proposed likelihood.
-/
theorem canonical_firstGap_restrict_countOne_eq_withDensity
    {rate horizon : ℝ} (hrate : 0 < rate) :
    Measure.map (interarrival 0)
        ((exponentialInterarrivalMeasure rate).restrict
          {ω | canonicalRenewalCount horizon ω = 1}) =
      volume.withDensity (oneArrivalDensity rate horizon) := by
  apply Measure.ext
  intro B hB
  have hEvent : {ω : ℕ → ℝ | canonicalRenewalCount horizon ω = 1} =
      firstTwoGaps ⁻¹' oneArrivalPairEvent horizon := by
    ext ω
    exact canonicalRenewalCount_one_iff_firstTwoGaps_event horizon ω
  have hPairSet : MeasurableSet (Prod.fst ⁻¹' B ∩ oneArrivalPairEvent horizon) :=
    (measurable_fst hB).inter (measurableSet_oneArrivalPairEvent horizon)
  calc
    Measure.map (interarrival 0) ((exponentialInterarrivalMeasure rate).restrict
        {ω | canonicalRenewalCount horizon ω = 1}) B =
        exponentialInterarrivalMeasure rate
          ((interarrival 0) ⁻¹' B ∩ {ω | canonicalRenewalCount horizon ω = 1}) := by
      rw [Measure.map_apply (measurable_interarrival 0) hB,
        Measure.restrict_apply ((measurable_interarrival 0) hB)]
    _ = exponentialInterarrivalMeasure rate
          ((interarrival 0) ⁻¹' B ∩ firstTwoGaps ⁻¹' oneArrivalPairEvent horizon) := by
      rw [hEvent]
    _ = exponentialInterarrivalMeasure rate
          (firstTwoGaps ⁻¹' (Prod.fst ⁻¹' B ∩ oneArrivalPairEvent horizon)) := by
      rfl
    _ = (Measure.map firstTwoGaps (exponentialInterarrivalMeasure rate))
          (Prod.fst ⁻¹' B ∩ oneArrivalPairEvent horizon) := by
      exact (Measure.map_apply measurable_firstTwoGaps hPairSet).symm
    _ = ((expMeasure rate).prod (expMeasure rate))
          (Prod.fst ⁻¹' B ∩ oneArrivalPairEvent horizon) := by
      rw [(firstTwoGaps_hasLaw_prod_expMeasure hrate).map_eq]
    _ = (((expMeasure rate).prod (expMeasure rate)).restrict
          (oneArrivalPairEvent horizon)) (Prod.fst ⁻¹' B) := by
      exact (Measure.restrict_apply (measurable_fst hB)).symm
    _ = Measure.map Prod.fst (((expMeasure rate).prod (expMeasure rate)).restrict
          (oneArrivalPairEvent horizon)) B := by
      exact (Measure.map_apply measurable_fst hB).symm
    _ = (volume.withDensity (oneArrivalDensity rate horizon)) B := by
      rw [oneArrivalPair_projection_eq_withDensity hrate]

/--
After any total prefix stopping index, the first uninspected gap restricted to
one new arrival in its next two gaps has the same exact density.  This is a
finite-block renewal statement; it does not assert a continuous-time
strong-Markov theorem for an arbitrary clock-time stopping rule.
-/
theorem postStop_firstGap_restrict_oneArrival_eq_withDensity
    {rate horizon : ℝ} (hrate : 0 < rate) (τ : PrefixStoppingIndex) :
    Measure.map (postStopFirstGap τ)
        ((exponentialInterarrivalMeasure rate).restrict
          (postStopOneArrivalEvent τ horizon)) =
      volume.withDensity (oneArrivalDensity rate horizon) := by
  apply Measure.ext
  intro B hB
  have hPairSet : MeasurableSet (Prod.fst ⁻¹' B ∩ oneArrivalPairEvent horizon) :=
    (measurable_fst hB).inter (measurableSet_oneArrivalPairEvent horizon)
  calc
    Measure.map (postStopFirstGap τ) ((exponentialInterarrivalMeasure rate).restrict
        (postStopOneArrivalEvent τ horizon)) B =
        exponentialInterarrivalMeasure rate
          ((postStopFirstGap τ) ⁻¹' B ∩ postStopOneArrivalEvent τ horizon) := by
      rw [Measure.map_apply (measurable_postStopFirstGap τ) hB,
        Measure.restrict_apply ((measurable_postStopFirstGap τ) hB)]
    _ = exponentialInterarrivalMeasure rate
          (postStopFirstTwoGaps τ ⁻¹'
            (Prod.fst ⁻¹' B ∩ oneArrivalPairEvent horizon)) := by
      rfl
    _ = (Measure.map (postStopFirstTwoGaps τ)
          (exponentialInterarrivalMeasure rate))
          (Prod.fst ⁻¹' B ∩ oneArrivalPairEvent horizon) := by
      exact (Measure.map_apply (measurable_postStopFirstTwoGaps τ) hPairSet).symm
    _ = ((expMeasure rate).prod (expMeasure rate))
          (Prod.fst ⁻¹' B ∩ oneArrivalPairEvent horizon) := by
      rw [(postStopFirstTwoGaps_hasLaw_prod_expMeasure hrate τ).map_eq]
    _ = (((expMeasure rate).prod (expMeasure rate)).restrict
          (oneArrivalPairEvent horizon)) (Prod.fst ⁻¹' B) := by
      exact (Measure.restrict_apply (measurable_fst hB)).symm
    _ = Measure.map Prod.fst (((expMeasure rate).prod (expMeasure rate)).restrict
          (oneArrivalPairEvent horizon)) B := by
      exact (Measure.map_apply measurable_fst hB).symm
    _ = (volume.withDensity (oneArrivalDensity rate horizon)) B := by
      rw [oneArrivalPair_projection_eq_withDensity hrate]

end

end LBG24SpatialUnderreporting
