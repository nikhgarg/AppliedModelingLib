import AppliedModelingLib.Foundations.Probability.PalmProductTaggedArrival
import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalFiniteDensity

/-!
# Finite future blocks from a tagged Poisson arrival

This module identifies every finite block of post-tag gaps in the canonical
two-sided tagged-arrival construction with the corresponding iid exponential
product law.
-/

namespace AppliedModelingLib.Probability.PoissonProcess

open MeasureTheory ProbabilityTheory

noncomputable section

/-- The first `count` gaps strictly after the tagged arrival at time zero. -/
def taggedFutureGapBlock (count : ℕ) : (ℤ → ℝ) → Fin count → ℝ :=
  fun gaps i => twoSidedGap (Int.ofNat i) gaps

theorem measurable_taggedFutureGapBlock (count : ℕ) :
    Measurable (taggedFutureGapBlock count) := by
  exact measurable_pi_iff.2 fun i => measurable_twoSidedGap (Int.ofNat i)

/-- A finite post-tag gap block has the iid exponential product law. -/
theorem map_taggedFutureGapBlock_twoSidedInterarrivalMeasure
    {rate : ℝ} (hrate : 0 < rate) (count : ℕ) :
    Measure.map (taggedFutureGapBlock count) (twoSidedInterarrivalMeasure rate) =
      Measure.pi (fun _ : Fin count => expMeasure rate) := by
  letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure rate) :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure hrate
  have hindex : Function.Injective (fun i : Fin count => Int.ofNat i.1) := by
    intro i j hij
    apply Fin.ext
    exact Int.ofNat_inj.mp hij
  have hindep :
      iIndepFun (fun i : Fin count => twoSidedGap (Int.ofNat i.1))
        (twoSidedInterarrivalMeasure rate) :=
    (iIndepFun_twoSidedGap hrate).precomp hindex
  have hmap :=
    (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
      (fun i : Fin count => (measurable_twoSidedGap (Int.ofNat i.1)).aemeasurable)).mp
      hindep
  rw [show taggedFutureGapBlock count =
      (fun ω i => twoSidedGap (Int.ofNat i.1) ω) by rfl]
  rw [hmap]
  congr 1
  funext i
  exact (twoSidedGap_hasLaw hrate (Int.ofNat i.1)).map_eq

/-- A finite post-tag gap block and its next gap have the corresponding
independent exponential product law. -/
theorem map_taggedFutureGapBlock_nextGap_twoSidedInterarrivalMeasure
    {rate : ℝ} (hrate : 0 < rate) (count : ℕ) :
    Measure.map
        (fun gaps : (ℤ → ℝ) =>
          (taggedFutureGapBlock count gaps, twoSidedGap (Int.ofNat count) gaps))
        (twoSidedInterarrivalMeasure rate) =
      (Measure.pi (fun _ : Fin count => expMeasure rate)).prod (expMeasure rate) := by
  letI : IsProbabilityMeasure (expMeasure rate) :=
    isProbabilityMeasure_expMeasure hrate
  let μ : Measure (Fin (count + 1) → ℝ) :=
    Measure.pi (fun _ : Fin (count + 1) => expMeasure rate)
  let lead : (Fin (count + 1) → ℝ) → ℝ × (Fin count → ℝ) :=
    fun v => (v (Fin.last count), fun i => v i.castSucc)
  let split : (Fin (count + 1) → ℝ) → (Fin count → ℝ) × ℝ :=
    fun v => ((fun i => v i.castSucc), v (Fin.last count))
  have hlead : Measurable lead :=
    (measurable_pi_apply (Fin.last count)).prodMk
      (measurable_pi_iff.2 fun i => measurable_pi_apply i.castSucc)
  have hsplit : Measurable split :=
    (measurable_pi_iff.2 fun i => measurable_pi_apply i.castSucc).prodMk
      (measurable_pi_apply (Fin.last count))
  have hleadfun :
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (count + 1) => ℝ)
        (Fin.last count) : (Fin (count + 1) → ℝ) → ℝ × (Fin count → ℝ)) =
        lead := by
    funext v
    apply Prod.ext
    · rfl
    · funext i
      change v ((Fin.last count).succAbove i) = v i.castSucc
      rw [Fin.succAbove_last]
  have hleadLaw :
      Measure.map lead μ =
        (expMeasure rate).prod (Measure.pi (fun _ : Fin count => expMeasure rate)) := by
    have h :=
      (measurePreserving_piFinSuccAbove
        (fun _ : Fin (count + 1) => expMeasure rate) (Fin.last count)).map_eq
    rw [hleadfun] at h
    simpa [μ, Fin.succAbove_last] using h
  have hsplitLaw :
      Measure.map split μ =
        (Measure.pi (fun _ : Fin count => expMeasure rate)).prod (expMeasure rate) := by
    calc
      Measure.map split μ = Measure.map Prod.swap (Measure.map lead μ) := by
        rw [Measure.map_map measurable_swap hlead]
        congr 1
      _ = Measure.map Prod.swap
          ((expMeasure rate).prod (Measure.pi (fun _ : Fin count => expMeasure rate))) := by
        rw [hleadLaw]
      _ = (Measure.pi (fun _ : Fin count => expMeasure rate)).prod (expMeasure rate) :=
        Measure.prod_swap
  have hfull :=
    map_taggedFutureGapBlock_twoSidedInterarrivalMeasure hrate (count + 1)
  calc
    Measure.map
        (fun gaps : (ℤ → ℝ) =>
          (taggedFutureGapBlock count gaps, twoSidedGap (Int.ofNat count) gaps))
        (twoSidedInterarrivalMeasure rate) =
        Measure.map split
          (Measure.map (taggedFutureGapBlock (count + 1))
            (twoSidedInterarrivalMeasure rate)) := by
      rw [Measure.map_map hsplit (measurable_taggedFutureGapBlock (count + 1))]
      congr 1
    _ = Measure.map split μ := by rw [hfull]
    _ = (Measure.pi (fun _ : Fin count => expMeasure rate)).prod (expMeasure rate) :=
      hsplitLaw

/-- The same finite gap law under an independently adjoined stationary state. -/
theorem map_taggedFutureGapBlock_independentProductTaggedArrivalAtZero
    {Ω : Type*} [MeasurableSpace Ω]
    (Pstate : Measure Ω) [IsProbabilityMeasure Pstate]
    {rate : ℝ} (hrate : 0 < rate) (count : ℕ) :
    Measure.map (fun x : Ω × (ℤ → ℝ) => taggedFutureGapBlock count x.2)
        (independentProductTaggedArrivalAtZero Pstate rate hrate).Ptag =
      Measure.pi (fun _ : Fin count => expMeasure rate) := by
  letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure rate) :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure hrate
  change Measure.map (fun x : Ω × (ℤ → ℝ) => taggedFutureGapBlock count x.2)
      (Pstate.prod (twoSidedInterarrivalMeasure rate)) = _
  calc
    Measure.map (fun x : Ω × (ℤ → ℝ) => taggedFutureGapBlock count x.2)
        (Pstate.prod (twoSidedInterarrivalMeasure rate)) =
        Measure.map (taggedFutureGapBlock count)
          (Measure.map Prod.snd (Pstate.prod (twoSidedInterarrivalMeasure rate))) := by
      rw [Measure.map_map (measurable_taggedFutureGapBlock count) measurable_snd]
      rfl
    _ = Measure.map (taggedFutureGapBlock count)
        (twoSidedInterarrivalMeasure rate) := by
      rw [Measure.map_snd_prod, measure_univ, one_smul]
    _ = Measure.pi (fun _ : Fin count => expMeasure rate) :=
      map_taggedFutureGapBlock_twoSidedInterarrivalMeasure hrate count

/-- Adjoining an independent stationary state preserves the joint law of a
finite post-tag gap block and its next gap. -/
theorem map_taggedFutureGapBlock_nextGap_independentProductTaggedArrivalAtZero
    {Ω : Type*} [MeasurableSpace Ω]
    (Pstate : Measure Ω) [IsProbabilityMeasure Pstate]
    {rate : ℝ} (hrate : 0 < rate) (count : ℕ) :
    Measure.map
        (fun x : Ω × (ℤ → ℝ) =>
          (taggedFutureGapBlock count x.2,
            twoSidedGap (Int.ofNat count) x.2))
        (independentProductTaggedArrivalAtZero Pstate rate hrate).Ptag =
      (Measure.pi (fun _ : Fin count => expMeasure rate)).prod (expMeasure rate) := by
  letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure rate) :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure hrate
  let blockNext : (ℤ → ℝ) → (Fin count → ℝ) × ℝ :=
    fun gaps =>
      (taggedFutureGapBlock count gaps, twoSidedGap (Int.ofNat count) gaps)
  have hblockNext : Measurable blockNext :=
    (measurable_taggedFutureGapBlock count).prodMk
      (measurable_twoSidedGap (Int.ofNat count))
  change Measure.map (fun x : Ω × (ℤ → ℝ) => blockNext x.2)
      (Pstate.prod (twoSidedInterarrivalMeasure rate)) = _
  calc
    Measure.map (fun x : Ω × (ℤ → ℝ) => blockNext x.2)
        (Pstate.prod (twoSidedInterarrivalMeasure rate)) =
        Measure.map blockNext
          (Measure.map Prod.snd (Pstate.prod (twoSidedInterarrivalMeasure rate))) := by
      rw [Measure.map_map hblockNext measurable_snd]
      rfl
    _ = Measure.map blockNext (twoSidedInterarrivalMeasure rate) := by
      rw [Measure.map_snd_prod, measure_univ, one_smul]
    _ = (Measure.pi (fun _ : Fin count => expMeasure rate)).prod (expMeasure rate) :=
      map_taggedFutureGapBlock_nextGap_twoSidedInterarrivalMeasure hrate count

/-- The cumulative post-tag arrival epochs inherit the finite-arrival density. -/
theorem map_taggedFutureArrivalBlock_independentProductTaggedArrivalAtZero
    {Ω : Type*} [MeasurableSpace Ω]
    (Pstate : Measure Ω) [IsProbabilityMeasure Pstate]
    {rate : ℝ} (hrate : 0 < rate) (count : ℕ) :
    Measure.map
        (fun x : Ω × (ℤ → ℝ) =>
          cumulativeArrivalVector count (taggedFutureGapBlock count x.2))
        (independentProductTaggedArrivalAtZero Pstate rate hrate).Ptag =
      (volume : Measure (Fin count → ℝ)).withDensity
        (exponentialBlockDensity rate count ∘
          (cumulativeArrivalLinearEquiv count).symm) := by
  rw [← map_cumulativeArrivalVector_pi_expMeasure_eq_withDensity hrate count]
  rw [← map_taggedFutureGapBlock_independentProductTaggedArrivalAtZero
    Pstate hrate count]
  have hcum : Measurable (cumulativeArrivalVector count) := by
    rw [show cumulativeArrivalVector count = cumulativeArrivalLinearMap count by
      funext gaps
      exact (cumulativeArrivalLinearMap_apply count gaps).symm]
    exact (cumulativeArrivalLinearMap_volume_preserving count).measurable
  simpa [Function.comp_def] using
    (Measure.map_map hcum
      ((measurable_taggedFutureGapBlock count).comp measurable_snd)
      (μ := (independentProductTaggedArrivalAtZero Pstate rate hrate).Ptag)).symm

end

end AppliedModelingLib.Probability.PoissonProcess
