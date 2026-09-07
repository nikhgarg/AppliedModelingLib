import AppliedModelingLib.Foundations.Probability.MeasureInequalities
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.BorelCantelli
import Mathlib.Probability.Independence.InfinitePi

/-!
# Iid Sequence Conditioning

Reusable facts for a canonical countable iid product space.  The step indexed
by `n` uses coordinate `n + 1`, leaving the finite prefix through `n` as its
natural past.  The main result identifies the conditional expectation of an
integrable statistic of that prefix and the fresh draw with its population
integral.
-/

open MeasureTheory ProbabilityTheory

namespace AppliedModelingLib

variable {α : Type*} [MetricSpace α] [SecondCountableTopology α]
  [MeasurableSpace α] [BorelSpace α] [StandardBorelSpace α] [Nonempty α]

/-- The canonical countable iid product measure with marginal law `ν`. -/
noncomputable def iidSequenceMeasure (ν : Measure α) : Measure (ℕ → α) :=
  Measure.infinitePi fun _ : ℕ => ν

/-- The canonical iid sequence measure is a probability measure. -/
theorem iidSequenceMeasure_isProbabilityMeasure (ν : Measure α)
    [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (iidSequenceMeasure ν) := by
  let P : ℕ → Measure α := fun _ => ν
  let hP : ∀ n : ℕ, IsProbabilityMeasure (P n) := fun _ => inferInstance
  simpa [iidSequenceMeasure, P] using
    @MeasureTheory.Measure.instIsProbabilityMeasureForallInfinitePi
      (ι := ℕ) (X := fun _ : ℕ => α)
      (mX := fun _ => inferInstance) (μ := P) hP

/-- The fresh iid draw used at step `n`. -/
def iidSequenceSample (n : ℕ) (omega : ℕ → α) : α := omega (n + 1)

/-- Each fresh iid draw has the designated marginal law. -/
theorem iidSequenceSample_law (ν : Measure α) [IsProbabilityMeasure ν] (n : ℕ) :
    Measure.map (iidSequenceSample (α := α) n) (iidSequenceMeasure ν) = ν := by
  let P : ℕ → Measure α := fun _ => ν
  let hP : ∀ k : ℕ, IsProbabilityMeasure (P k) := fun _ => inferInstance
  simpa [iidSequenceSample, iidSequenceMeasure, P] using
    (@MeasureTheory.Measure.infinitePi_map_eval
      (ι := ℕ) (X := fun _ : ℕ => α)
      (mX := fun _ => inferInstance) (μ := P) hP (n + 1))

/-- Every fresh iid draw preserves the designated marginal law. -/
theorem iidSequenceSample_measurePreserving (ν : Measure α) [IsProbabilityMeasure ν]
    (n : ℕ) :
    MeasurePreserving (iidSequenceSample (α := α) n) (iidSequenceMeasure ν) ν := by
  refine ⟨?_, iidSequenceSample_law ν n⟩
  simpa [iidSequenceSample] using
    (measurable_pi_apply (n + 1) : Measurable (fun omega : ℕ → α => omega (n + 1)))

/-- Integrability is preserved when an integrable reward is evaluated at a
fresh canonical iid draw. -/
theorem integrable_iidSequenceSample_reward (ν : Measure α) [IsProbabilityMeasure ν]
    (reward : α → ℝ) (hreward : Integrable reward ν) (n : ℕ) :
    Integrable (fun omega => reward (iidSequenceSample (α := α) n omega))
      (iidSequenceMeasure ν) := by
  exact (iidSequenceSample_measurePreserving ν n).integrable_comp_of_integrable hreward

/-- The raw coordinates of a canonical iid sequence are mutually independent. -/
theorem iidSequence_iIndepFun (ν : Measure α) [IsProbabilityMeasure ν] :
    ProbabilityTheory.iIndepFun (fun n (omega : ℕ → α) => omega n)
      (iidSequenceMeasure ν) := by
  let P : ℕ → Measure α := fun _ => ν
  let hP : ∀ n : ℕ, IsProbabilityMeasure (P n) := fun _ => inferInstance
  simpa [iidSequenceMeasure, P] using
    (@ProbabilityTheory.iIndepFun_infinitePi
      (ι := ℕ) (𝓧 := fun _ : ℕ => α)
      (m𝓧 := fun _ => inferInstance) (Ω := fun _ : ℕ => α)
      (mΩ := fun _ => inferInstance) (P := P) hP
      (X := fun _ : ℕ => id) (mX := fun _ => measurable_id))

/-- The shifted fresh draws of a canonical iid sequence are mutually independent. -/
theorem iidSequenceSample_iIndepFun (ν : Measure α) [IsProbabilityMeasure ν] :
    ProbabilityTheory.iIndepFun (fun n (omega : ℕ → α) => iidSequenceSample n omega)
      (iidSequenceMeasure ν) := by
  simpa [iidSequenceSample, Function.comp_def] using
    (iidSequence_iIndepFun ν).precomp Nat.succ_injective

/-- Every fresh iid draw is measurable on the canonical product space. -/
theorem measurable_iidSequenceSample (n : ℕ) :
    Measurable (iidSequenceSample (α := α) n) := by
  simpa [iidSequenceSample] using
    (measurable_pi_apply (n + 1) : Measurable (fun omega : ℕ → α => omega (n + 1)))

/-- The natural filtration of the raw iid coordinate sequence. -/
noncomputable def iidSequenceNaturalFiltration :
    Filtration (Ω := ℕ → α) ℕ inferInstance :=
  Filtration.natural (fun n (omega : ℕ → α) => omega n)
    (fun n => (measurable_pi_apply n).stronglyMeasurable)

/-- The finite raw history available before the step-`n` iid draw. -/
def iidSequencePastPrefix (n : ℕ) (omega : ℕ → α) : Fin (n + 1) → α :=
  fun j => omega j

/-- The finite raw history is measurable on the canonical sequence space. -/
theorem measurable_iidSequencePastPrefix (n : ℕ) :
    Measurable (iidSequencePastPrefix (α := α) n) := by
  change Measurable (fun omega : ℕ → α => fun j : Fin (n + 1) => omega j)
  exact measurable_pi_iff.mpr (fun j =>
    (measurable_pi_apply (j : ℕ) : Measurable (fun omega : ℕ → α => omega (j : ℕ))))

/--
The natural filtration through time `n` is exactly the pullback of the finite
raw prefix through coordinate `n`.
-/
theorem iidSequenceNaturalFiltration_eq_comap_pastPrefix (n : ℕ) :
    iidSequenceNaturalFiltration (α := α) n =
      MeasurableSpace.comap (iidSequencePastPrefix (α := α) n) inferInstance := by
  unfold iidSequenceNaturalFiltration
  apply le_antisymm
  · change (⨆ j ≤ n, MeasurableSpace.comap
      (fun omega : ℕ → α => omega j) inferInstance) ≤ _
    refine iSup_le fun j => iSup_le fun hj => ?_
    change MeasurableSpace.comap (fun omega : ℕ → α => omega j) inferInstance ≤
      MeasurableSpace.comap (iidSequencePastPrefix (α := α) n) inferInstance
    rw [show (fun omega : ℕ → α => omega j) =
        (fun h : Fin (n + 1) → α => h ⟨j, Nat.lt_succ_of_le hj⟩) ∘
          iidSequencePastPrefix (α := α) n by rfl,
      ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono
      (measurable_pi_apply (⟨j, Nat.lt_succ_of_le hj⟩ : Fin (n + 1))).comap_le
  · change MeasurableSpace.comap (iidSequencePastPrefix (α := α) n)
      inferInstance ≤
      (⨆ j ≤ n, MeasurableSpace.comap (fun omega : ℕ → α => omega j) inferInstance)
    rw [show (inferInstance : MeasurableSpace (Fin (n + 1) → α)) =
      ⨆ j : Fin (n + 1), MeasurableSpace.comap (fun h : Fin (n + 1) → α => h j)
        inferInstance by rfl,
      MeasurableSpace.comap_iSup]
    refine iSup_le fun j => ?_
    rw [MeasurableSpace.comap_comp]
    exact le_iSup_of_le (j : ℕ)
      (le_iSup_of_le (Nat.le_of_lt_succ j.isLt) le_rfl)

/-- The finite iid past is independent of the fresh draw at step `n`. -/
theorem iidSequencePastPrefix_indep_sample (ν : Measure α) [IsProbabilityMeasure ν]
    (n : ℕ) :
    IndepFun (iidSequencePastPrefix (α := α) n)
      (iidSequenceSample (α := α) n) (iidSequenceMeasure ν) := by
  letI : IsProbabilityMeasure (iidSequenceMeasure ν) :=
    iidSequenceMeasure_isProbabilityMeasure ν
  rw [IndepFun_iff_Indep]
  have hpast : MeasurableSpace.comap (iidSequencePastPrefix (α := α) n)
      inferInstance ≤ iidSequenceNaturalFiltration (α := α) n := by
    rw [iidSequenceNaturalFiltration_eq_comap_pastPrefix]
  have hraw_indep :
      Indep (MeasurableSpace.comap (fun omega : ℕ → α => omega (n + 1)) inferInstance)
        (⨆ k ∈ {k : ℕ | k ≤ n},
          MeasurableSpace.comap (fun omega : ℕ → α => omega k) inferInstance)
        (iidSequenceMeasure ν) := by
    suffices
        Indep (⨆ k ∈ ({n + 1} : Set ℕ),
          MeasurableSpace.comap (fun omega : ℕ → α => omega k) inferInstance)
          (⨆ k ∈ {k : ℕ | k ≤ n},
            MeasurableSpace.comap (fun omega : ℕ → α => omega k) inferInstance)
          (iidSequenceMeasure ν) by
      simpa only [iSup_singleton] using this
    exact indep_iSup_of_disjoint
      (fun k => (measurable_pi_apply k).comap_le)
      (iidSequence_iIndepFun ν) (by simpa)
  have hraw_indep' :
      Indep (MeasurableSpace.comap (fun omega : ℕ → α => omega (n + 1)) inferInstance)
        (iidSequenceNaturalFiltration (α := α) n) (iidSequenceMeasure ν) := by
    simpa [iidSequenceNaturalFiltration] using hraw_indep
  simpa [iidSequenceSample] using
    (indep_of_indep_of_le_right hraw_indep' hpast).symm

/-- The iid past prefix and fresh draw have their product law. -/
theorem iidSequencePastPrefix_sample_pair_law (ν : Measure α) [IsProbabilityMeasure ν]
    (n : ℕ) :
    Measure.map (fun omega =>
      (iidSequencePastPrefix (α := α) n omega, iidSequenceSample (α := α) n omega))
      (iidSequenceMeasure ν) =
        (Measure.map (iidSequencePastPrefix (α := α) n) (iidSequenceMeasure ν)).prod ν := by
  letI : IsProbabilityMeasure (iidSequenceMeasure ν) :=
    iidSequenceMeasure_isProbabilityMeasure ν
  calc
    Measure.map (fun omega =>
        (iidSequencePastPrefix (α := α) n omega,
          iidSequenceSample (α := α) n omega))
        (iidSequenceMeasure ν) =
        (Measure.map (iidSequencePastPrefix (α := α) n)
          (iidSequenceMeasure ν)).prod
          (Measure.map (iidSequenceSample (α := α) n) (iidSequenceMeasure ν)) :=
      (indepFun_iff_map_prod_eq_prod_map_map
        (measurable_iidSequencePastPrefix n).aemeasurable
        (measurable_iidSequenceSample n).aemeasurable).mp
        (iidSequencePastPrefix_indep_sample ν n)
    _ = (Measure.map (iidSequencePastPrefix (α := α) n)
          (iidSequenceMeasure ν)).prod ν := by
      rw [iidSequenceSample_law ν n]

/--
Conditioning an integrable statistic of a finite iid past and its fresh draw
on the natural past filtration gives the population integral over that draw.
-/
theorem iidSequencePastPrefix_condExp_ae_eq_integral
    (ν : Measure α) [IsProbabilityMeasure ν] (n : ℕ)
    (test : (Fin (n + 1) → α) → α → ℝ)
    (htest : Integrable (fun z : (Fin (n + 1) → α) × α => test z.1 z.2)
      (Measure.map (fun omega =>
        (iidSequencePastPrefix (α := α) n omega, iidSequenceSample (α := α) n omega))
        (iidSequenceMeasure ν))) :
    (iidSequenceMeasure ν)[
      fun omega => test (iidSequencePastPrefix n omega) (iidSequenceSample n omega) |
        iidSequenceNaturalFiltration (α := α) n] =ᵐ[iidSequenceMeasure ν]
      fun omega => ∫ sample, test (iidSequencePastPrefix n omega) sample ∂ν := by
  letI : IsProbabilityMeasure (iidSequenceMeasure ν) :=
    iidSequenceMeasure_isProbabilityMeasure ν
  have hkernel : condDistrib (iidSequenceSample (α := α) n)
      (iidSequencePastPrefix (α := α) n) (iidSequenceMeasure ν) =ᵐ[
        Measure.map (iidSequencePastPrefix (α := α) n) (iidSequenceMeasure ν)]
      Kernel.const (Fin (n + 1) → α) ν := by
    apply condDistrib_ae_eq_of_measure_eq_compProd
      (iidSequencePastPrefix (α := α) n)
      (measurable_iidSequenceSample n).aemeasurable
    rw [Measure.compProd_const]
    exact iidSequencePastPrefix_sample_pair_law ν n
  have hkernel_lift : ∀ᵐ omega ∂iidSequenceMeasure ν,
      condDistrib (iidSequenceSample (α := α) n)
        (iidSequencePastPrefix (α := α) n) (iidSequenceMeasure ν)
          (iidSequencePastPrefix n omega) =
        (Kernel.const (Fin (n + 1) → α) ν) (iidSequencePastPrefix n omega) :=
    ae_of_ae_map (measurable_iidSequencePastPrefix n).aemeasurable hkernel
  have hcond := condExp_prod_ae_eq_integral_condDistrib'
    (μ := iidSequenceMeasure ν)
    (X := iidSequencePastPrefix (α := α) n)
    (Y := iidSequenceSample (α := α) n)
    (f := fun z : (Fin (n + 1) → α) × α => test z.1 z.2)
    (measurable_iidSequencePastPrefix n)
    (measurable_iidSequenceSample n).aemeasurable htest
  rw [← iidSequenceNaturalFiltration_eq_comap_pastPrefix] at hcond
  filter_upwards [hcond, hkernel_lift] with omega hcond hkernel_eq
  rw [hkernel_eq] at hcond
  simpa [Kernel.const_apply] using hcond

/--
If every realized finite history gives a population bound for an integrable
statistic of the next iid draw, then the corresponding conditional expectation
given that history obeys the same bound almost surely.  This is the reusable
history-to-fresh-draw step behind conditional rare-event estimates.
-/
theorem iidSequencePastPrefix_condExp_ae_le_of_integral_le
    (ν : Measure α) [IsProbabilityMeasure ν] (n : ℕ)
    (test : (Fin (n + 1) → α) → α → ℝ)
    (htest : Integrable (fun z : (Fin (n + 1) → α) × α => test z.1 z.2)
      (Measure.map (fun omega =>
        (iidSequencePastPrefix (α := α) n omega, iidSequenceSample (α := α) n omega))
        (iidSequenceMeasure ν)))
    (bound : (Fin (n + 1) → α) → ℝ)
    (hbound : ∀ history, ∫ sample, test history sample ∂ν ≤ bound history) :
    (iidSequenceMeasure ν)[
      fun omega => test (iidSequencePastPrefix n omega) (iidSequenceSample n omega) |
        iidSequenceNaturalFiltration (α := α) n] ≤ᵐ[iidSequenceMeasure ν]
      fun omega => bound (iidSequencePastPrefix n omega) := by
  filter_upwards [iidSequencePastPrefix_condExp_ae_eq_integral ν n test htest] with
    omega hcond
  rw [hcond]
  exact hbound _

/-- The conditional mean of an integrable statistic of the fresh iid draw,
given the preceding raw-coordinate filtration, is its population mean. -/
theorem condExp_iidSequenceSample_ae_eq_integral
    (ν : Measure α) [IsProbabilityMeasure ν] (reward : α → ℝ)
    (hreward : Measurable reward) (n : ℕ) :
    (iidSequenceMeasure ν)[fun omega => reward (iidSequenceSample n omega) |
      iidSequenceNaturalFiltration (α := α) n] =ᵐ[iidSequenceMeasure ν]
      fun _ => ∫ sample, reward sample ∂ν := by
  let μ : Measure (ℕ → α) := iidSequenceMeasure ν
  let raw : ℕ → (ℕ → α) → α := fun index omega => omega index
  let f : (ℕ → α) → ℝ := fun omega => reward (omega (n + 1))
  letI : IsProbabilityMeasure μ := by
    simpa [μ] using iidSequenceMeasure_isProbabilityMeasure ν
  have hraw_meas : ∀ index, StronglyMeasurable (raw index) := by
    intro index
    exact (measurable_pi_apply index).stronglyMeasurable
  have hf_meas : Measurable[MeasurableSpace.comap (raw (n + 1)) inferInstance] f := by
    exact hreward.comp (comap_measurable (raw (n + 1)))
  have hindep_raw :
      Indep (MeasurableSpace.comap (raw (n + 1)) inferInstance)
        (⨆ k ∈ {k : ℕ | k ≤ n}, MeasurableSpace.comap (raw k) inferInstance) μ := by
    have hbase :
        Indep (⨆ k ∈ ({n + 1} : Set ℕ),
          MeasurableSpace.comap (fun omega : ℕ → α => omega k) inferInstance)
          (⨆ k ∈ {k : ℕ | k ≤ n},
            MeasurableSpace.comap (fun omega : ℕ → α => omega k) inferInstance)
          (iidSequenceMeasure ν) := by
      exact indep_iSup_of_disjoint
        (fun k => (measurable_pi_apply k).comap_le)
        (iidSequence_iIndepFun ν) (by simpa)
    suffices
        Indep (⨆ k ∈ ({n + 1} : Set ℕ), MeasurableSpace.comap (raw k) inferInstance)
          (⨆ k ∈ {k : ℕ | k ≤ n}, MeasurableSpace.comap (raw k) inferInstance) μ by
      simpa only [iSup_singleton] using this
    simpa [raw, μ] using hbase
  have hindep : Indep (MeasurableSpace.comap (raw (n + 1)) inferInstance)
      (iidSequenceNaturalFiltration (α := α) n) μ := by
    simpa [iidSequenceNaturalFiltration, raw, μ] using hindep_raw
  have hfiltration_le : iidSequenceNaturalFiltration (α := α) n ≤
      (inferInstance : MeasurableSpace (ℕ → α)) :=
    (iidSequenceNaturalFiltration (α := α)).le n
  have hcond : μ[f | iidSequenceNaturalFiltration (α := α) n] =ᵐ[μ]
      fun _ => ∫ omega, f omega ∂μ := by
    exact condExp_indep_eq
      (m₁ := MeasurableSpace.comap (raw (n + 1)) inferInstance)
      (m₂ := iidSequenceNaturalFiltration (α := α) n) (m := inferInstance)
      (measurable_pi_apply (n + 1)).comap_le
      hfiltration_le
      hf_meas.stronglyMeasurable hindep
  have hintegral : (∫ omega, f omega ∂μ) = ∫ sample, reward sample ∂ν := by
    calc
      (∫ omega, f omega ∂μ) =
          ∫ sample, reward sample ∂Measure.map (iidSequenceSample n) (iidSequenceMeasure ν) := by
        symm
        simpa [μ, f, iidSequenceSample] using
          integral_map (iidSequenceSample_law ν n |>.symm ▸
            (measurable_iidSequenceSample n).aemeasurable) hreward.aestronglyMeasurable
      _ = ∫ sample, reward sample ∂ν := by rw [iidSequenceSample_law ν n]
  rw [hintegral] at hcond
  simpa [μ, f, iidSequenceSample] using hcond

/-- Centered partial sums of the fresh coordinates of a canonical iid stream.
The `n`th sum contains the first `n` samples and is measurable with respect
to the raw coordinate filtration through `n`; this one-step offset leaves the
next coordinate independent of the past. -/
def iidSequenceCenteredPartialSum
    (reward : α → ℝ) (mean : ℝ) (steps : ℕ) (omega : ℕ → α) : ℝ :=
  ∑ index ∈ Finset.range steps, (reward (iidSequenceSample index omega) - mean)

/-- These shifted iid partial sums are strongly adapted to the raw-coordinate
natural filtration. -/
theorem stronglyAdapted_iidSequenceCenteredPartialSum
    (ν : Measure α) [IsProbabilityMeasure ν] (reward : α → ℝ) (mean : ℝ)
    (hreward : Measurable reward) :
    StronglyAdapted (iidSequenceNaturalFiltration (α := α))
      (iidSequenceCenteredPartialSum reward mean) := by
  have hraw : StronglyAdapted (iidSequenceNaturalFiltration (α := α))
      (fun index (omega : ℕ → α) => omega index) := by
    exact Filtration.stronglyAdapted_natural
      (fun index => (measurable_pi_apply index).stronglyMeasurable)
  intro steps
  unfold iidSequenceCenteredPartialSum
  have hsum : StronglyMeasurable[iidSequenceNaturalFiltration (α := α) steps]
      (∑ index ∈ Finset.range steps,
        (fun omega : ℕ → α => reward (iidSequenceSample index omega) - mean)) := by
    refine Finset.stronglyMeasurable_sum (Finset.range steps) ?_
    intro index hindex
    have hindex_lt : index < steps := Finset.mem_range.mp hindex
    have hindex_le : index + 1 ≤ steps := Nat.succ_le_of_lt hindex_lt
    have hsample : StronglyMeasurable[iidSequenceNaturalFiltration (α := α) steps]
        (fun omega : ℕ → α => omega (index + 1)) :=
      hraw.stronglyMeasurable_le hindex_le
    exact ((hreward.comp hsample.measurable).stronglyMeasurable).sub stronglyMeasurable_const
  have hsum_eq : (fun omega : ℕ → α =>
      ∑ index ∈ Finset.range steps, (reward (iidSequenceSample index omega) - mean)) =
      ∑ index ∈ Finset.range steps,
        (fun omega : ℕ → α => reward (iidSequenceSample index omega) - mean) := by
    funext omega
    simp
  rw [hsum_eq]
  exact hsum

/-- An integrable iid reward gives integrable centered finite partial sums. -/
theorem integrable_iidSequenceCenteredPartialSum
    (ν : Measure α) [IsProbabilityMeasure ν] (reward : α → ℝ) (mean : ℝ)
    (hreward : Integrable reward ν) (steps : ℕ) :
    Integrable (iidSequenceCenteredPartialSum reward mean steps)
      (iidSequenceMeasure ν) := by
  letI : IsProbabilityMeasure (iidSequenceMeasure ν) :=
    iidSequenceMeasure_isProbabilityMeasure ν
  letI : IsFiniteMeasure (iidSequenceMeasure ν) := by infer_instance
  unfold iidSequenceCenteredPartialSum
  apply integrable_finset_sum
  intro index _
  have hsample : Integrable (fun omega : ℕ → α =>
      reward (iidSequenceSample index omega)) (iidSequenceMeasure ν) := by
    exact integrable_iidSequenceSample_reward ν reward hreward index
  exact hsample.sub (integrable_const _)

/-- Centered partial sums of an integrable iid reward are a martingale for
the raw-coordinate filtration.  This reusable finite-prefix result is the
discrete maximal-inequality input for queueing and renewal-process paths. -/
theorem iidSequenceCenteredPartialSum_martingale
    (ν : Measure α) [IsProbabilityMeasure ν] (reward : α → ℝ) (mean : ℝ)
    (hreward_meas : Measurable reward) (hreward_int : Integrable reward ν)
    (hmean : mean = ∫ sample, reward sample ∂ν) :
    Martingale (iidSequenceCenteredPartialSum reward mean)
      (iidSequenceNaturalFiltration (α := α)) (iidSequenceMeasure ν) := by
  let μ : Measure (ℕ → α) := iidSequenceMeasure ν
  letI : IsProbabilityMeasure μ := by
    simpa [μ] using iidSequenceMeasure_isProbabilityMeasure ν
  letI : IsFiniteMeasure μ := by infer_instance
  refine AppliedModelingLib.martingale_partial_sum_of_condExp_eq_zero
    (Y := fun index (omega : ℕ → α) => reward (iidSequenceSample index omega) - mean)
    (ℱ := iidSequenceNaturalFiltration (α := α)) ?_ ?_ ?_
  · exact stronglyAdapted_iidSequenceCenteredPartialSum ν reward mean hreward_meas
  · intro steps
    change Integrable (iidSequenceCenteredPartialSum reward mean steps) μ
    simpa only [μ] using
      integrable_iidSequenceCenteredPartialSum ν reward mean hreward_int steps
  · intro index
    have hsample_int : Integrable (fun omega : ℕ → α =>
        reward (iidSequenceSample index omega)) μ := by
      simpa only [μ] using
        integrable_iidSequenceSample_reward ν reward hreward_int index
    have hcond := condExp_iidSequenceSample_ae_eq_integral
      ν reward hreward_meas index
    have hcond_mean : μ[fun omega => reward (iidSequenceSample index omega) |
        iidSequenceNaturalFiltration (α := α) index] =ᵐ[μ] fun _ => mean := by
      simpa [μ, hmean] using hcond
    have hconst : μ[fun _ : ℕ → α => mean |
        iidSequenceNaturalFiltration (α := α) index] = fun _ => mean := by
      exact condExp_const (μ := μ)
        ((iidSequenceNaturalFiltration (α := α)).le index) mean
    have hconst_ae : μ[fun _ : ℕ → α => mean |
        iidSequenceNaturalFiltration (α := α) index] =ᵐ[μ] fun _ => mean :=
      Filter.Eventually.of_forall fun omega => congrFun hconst omega
    calc
      μ[(fun omega : ℕ → α => reward (iidSequenceSample index omega) - mean) |
          iidSequenceNaturalFiltration (α := α) index] =ᵐ[μ]
          μ[fun omega => reward (iidSequenceSample index omega) |
            iidSequenceNaturalFiltration (α := α) index] -
            μ[fun _ : ℕ → α => mean |
              iidSequenceNaturalFiltration (α := α) index] :=
        condExp_sub hsample_int (integrable_const _) _
      _ =ᵐ[μ] (fun _ => mean) - (fun _ => mean) :=
        hcond_mean.sub hconst_ae
      _ =ᵐ[μ] 0 := Filter.Eventually.of_forall fun _ => sub_self _

end AppliedModelingLib
