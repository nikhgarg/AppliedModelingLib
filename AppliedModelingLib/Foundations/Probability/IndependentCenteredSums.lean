import AppliedModelingLib.Foundations.Probability.MeasureInequalities
import Mathlib.Probability.BorelCantelli

/-!
# Centered partial sums of independent sequences

This module packages the shifted-past convention needed to make a discrete
independent sequence into a martingale.  At filtration time `n`, the partial
sum contains coordinates `1, …, n`; coordinate `n + 1` is still fresh.
The offset is intentional and makes the result directly usable for fixed
meshes of a process with independent increments.
-/

namespace AppliedModelingLib.Probability

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The centered sum of the coordinates strictly after the origin and through
`steps`.  The first coordinate is retained outside this sum so the process is
adapted to the ordinary natural filtration of the unshifted sequence. -/
def shiftedCenteredPartialSum
    (Y : ℕ → Ω → ℝ) (means : ℕ → ℝ) (steps : ℕ) (omega : Ω) : ℝ :=
  ∑ index ∈ Finset.range steps, (Y (index + 1) omega - means index)

/-- Shifted centered partial sums are strongly adapted to the natural
filtration of their underlying sequence. -/
theorem stronglyAdapted_shiftedCenteredPartialSum
    {Y : ℕ → Ω → ℝ} (hY : ∀ index, StronglyMeasurable (Y index))
    (means : ℕ → ℝ) :
    StronglyAdapted (Filtration.natural Y hY) (shiftedCenteredPartialSum Y means) := by
  have hadapted : StronglyAdapted (Filtration.natural Y hY) Y :=
    Filtration.stronglyAdapted_natural hY
  intro steps
  unfold shiftedCenteredPartialSum
  have hsum : StronglyMeasurable[Filtration.natural Y hY steps]
      (∑ index ∈ Finset.range steps,
        (fun omega : Ω => Y (index + 1) omega - means index)) := by
    refine Finset.stronglyMeasurable_sum (Finset.range steps) ?_
    intro index hindex
    have hindex_lt : index < steps := Finset.mem_range.mp hindex
    have hindex_le : index + 1 ≤ steps := Nat.succ_le_of_lt hindex_lt
    exact (hadapted.stronglyMeasurable_le hindex_le).sub stronglyMeasurable_const
  have hsum_eq : (fun omega : Ω =>
      ∑ index ∈ Finset.range steps, (Y (index + 1) omega - means index)) =
      ∑ index ∈ Finset.range steps,
        (fun omega : Ω => Y (index + 1) omega - means index) := by
    funext omega
    simp
  rw [hsum_eq]
  exact hsum

/-- Integrability of all coordinates gives integrability of every finite
shifted centered partial sum. -/
theorem integrable_shiftedCenteredPartialSum
    {Y : ℕ → Ω → ℝ} [IsFiniteMeasure μ]
    (hY : ∀ index, Integrable (Y index) μ) (means : ℕ → ℝ) (steps : ℕ) :
    Integrable (shiftedCenteredPartialSum Y means steps) μ := by
  unfold shiftedCenteredPartialSum
  apply integrable_finset_sum
  intro index _
  exact (hY (index + 1)).sub (integrable_const _)

/-- Pointwise expansion of a shifted centered partial sum. -/
theorem shiftedCenteredPartialSum_eq_sum
    (Y : ℕ → Ω → ℝ) (means : ℕ → ℝ) (steps : ℕ) :
    shiftedCenteredPartialSum Y means steps =
      fun omega => ∑ index ∈ Finset.range steps,
        (Y (index + 1) omega - means index) := by
  rfl

/-- Square integrability is preserved by finite shifted centered sums. -/
theorem memLp_two_shiftedCenteredPartialSum
    {Y : ℕ → Ω → ℝ} [IsFiniteMeasure μ]
    (hY : ∀ index, MemLp (Y index) 2 μ)
    (means : ℕ → ℝ) (steps : ℕ) :
    MemLp (shiftedCenteredPartialSum Y means steps) 2 μ := by
  rw [shiftedCenteredPartialSum_eq_sum]
  exact MeasureTheory.memLp_finset_sum (Finset.range steps) fun index _ =>
    (hY (index + 1)).sub (memLp_const (means index))

/-- Fourth-power integrability is preserved by finite shifted centered sums. -/
theorem memLp_four_shiftedCenteredPartialSum
    {Y : ℕ → Ω → ℝ} [IsFiniteMeasure μ]
    (hY : ∀ index, MemLp (Y index) 4 μ)
    (means : ℕ → ℝ) (steps : ℕ) :
    MemLp (shiftedCenteredPartialSum Y means steps) 4 μ := by
  rw [shiftedCenteredPartialSum_eq_sum]
  exact MeasureTheory.memLp_finset_sum (Finset.range steps) fun index _ =>
    (hY (index + 1)).sub (memLp_const (means index))

/-- Centering by the literal coordinate means makes every shifted finite sum
have mean zero. -/
theorem integral_shiftedCenteredPartialSum
    {Y : ℕ → Ω → ℝ} [IsProbabilityMeasure μ]
    (hY : ∀ index, Integrable (Y index) μ) (means : ℕ → ℝ)
    (hmeans : ∀ index, means index = ∫ omega, Y (index + 1) omega ∂μ)
    (steps : ℕ) :
    ∫ omega, shiftedCenteredPartialSum Y means steps omega ∂μ = 0 := by
  rw [shiftedCenteredPartialSum_eq_sum]
  rw [MeasureTheory.integral_finset_sum]
  · apply Finset.sum_eq_zero
    intro index _
    rw [integral_sub (hY (index + 1)) (integrable_const _), integral_const,
      ← hmeans index]
    simp
  · intro index _
    exact (hY (index + 1)).sub (integrable_const _)

/-- Centered shifted partial sums of an integrable independent real sequence
are a martingale.  The hypothesis on `means` records the literal coordinate
means, so the result also handles non-identically distributed increments. -/
theorem shiftedCenteredPartialSum_martingale
    {Y : ℕ → Ω → ℝ} [IsFiniteMeasure μ]
    (hY_meas : ∀ index, StronglyMeasurable (Y index))
    (hY_int : ∀ index, Integrable (Y index) μ)
    (hY_indep : iIndepFun Y μ) (means : ℕ → ℝ)
    (hmeans : ∀ index, means index = ∫ omega, Y (index + 1) omega ∂μ) :
    Martingale (shiftedCenteredPartialSum Y means) (Filtration.natural Y hY_meas) μ := by
  letI : IsProbabilityMeasure μ := hY_indep.isProbabilityMeasure
  refine AppliedModelingLib.martingale_partial_sum_of_condExp_eq_zero
    (Y := fun index omega => Y (index + 1) omega - means index)
    (ℱ := Filtration.natural Y hY_meas) ?_ ?_ ?_
  · exact stronglyAdapted_shiftedCenteredPartialSum hY_meas means
  · intro steps
    exact integrable_shiftedCenteredPartialSum hY_int means steps
  · intro index
    have hcond := hY_indep.condExp_natural_ae_eq_of_lt hY_meas index.lt_succ_self
    have hcond_mean : μ[Y (index + 1) | Filtration.natural Y hY_meas index] =ᵐ[μ]
        fun _ => means index := by
      simpa [hmeans index] using hcond
    have hconst : μ[fun _ : Ω => means index | Filtration.natural Y hY_meas index] =
        fun _ => means index := by
      exact condExp_const (μ := μ) ((Filtration.natural Y hY_meas).le index) _
    have hconst_ae : μ[fun _ : Ω => means index |
        Filtration.natural Y hY_meas index] =ᵐ[μ] fun _ => means index :=
      Filter.Eventually.of_forall fun omega => congrFun hconst omega
    calc
      μ[(fun omega => Y (index + 1) omega - means index) |
          Filtration.natural Y hY_meas index] =ᵐ[μ]
          μ[Y (index + 1) | Filtration.natural Y hY_meas index] -
            μ[fun _ : Ω => means index | Filtration.natural Y hY_meas index] :=
        condExp_sub (hY_int (index + 1)) (integrable_const _) _
      _ =ᵐ[μ] (fun _ => means index) - (fun _ => means index) :=
        hcond_mean.sub hconst_ae
      _ =ᵐ[μ] 0 := Filter.Eventually.of_forall fun _ => sub_self _

/-- The terminal second moment of an independent centered partial sum is the
sum of the individual centered second moments. -/
theorem integral_sq_shiftedCenteredPartialSum
    {Y : ℕ → Ω → ℝ} [IsFiniteMeasure μ]
    (hY_memLp : ∀ index, MemLp (Y index) 2 μ)
    (hY_indep : iIndepFun Y μ) (means : ℕ → ℝ)
    (hmeans : ∀ index, means index = ∫ omega, Y (index + 1) omega ∂μ)
    (steps : ℕ) :
    ∫ omega, (shiftedCenteredPartialSum Y means steps omega) ^ 2 ∂μ =
      ∑ index ∈ Finset.range steps,
        ∫ omega, (Y (index + 1) omega - means index) ^ 2 ∂μ := by
  letI : IsProbabilityMeasure μ := hY_indep.isProbabilityMeasure
  let Z : ℕ → Ω → ℝ := fun index omega => Y (index + 1) omega - means index
  have hZ_memLp : ∀ index, MemLp (Z index) 2 μ := by
    intro index
    exact (hY_memLp (index + 1)).sub (memLp_const (means index))
  have hZ_indep : iIndepFun Z μ := by
    simpa only [Z, Function.comp_apply] using
      (hY_indep.precomp Nat.succ_injective).comp
        (fun index => fun value : ℝ => value - means index)
        (fun _ => measurable_id.sub measurable_const)
  have hZ_mean : ∀ index, ∫ omega, Z index omega ∂μ = 0 := by
    intro index
    have hint : Integrable (Y (index + 1)) μ :=
      (hY_memLp (index + 1)).integrable one_le_two
    rw [integral_sub hint (integrable_const _), integral_const, ← hmeans index]
    simp
  have hsum_mean : ∫ omega, shiftedCenteredPartialSum Y means steps omega ∂μ = 0 :=
    integral_shiftedCenteredPartialSum
      (fun index => (hY_memLp index).integrable one_le_two) means hmeans steps
  calc
    ∫ omega, (shiftedCenteredPartialSum Y means steps omega) ^ 2 ∂μ =
        ProbabilityTheory.variance (shiftedCenteredPartialSum Y means steps) μ := by
      rw [ProbabilityTheory.variance_of_integral_eq_zero
        (memLp_two_shiftedCenteredPartialSum hY_memLp means steps).aemeasurable hsum_mean]
    _ = ∑ index ∈ Finset.range steps, ProbabilityTheory.variance (Z index) μ := by
      rw [shiftedCenteredPartialSum_eq_sum]
      have hsum : (fun omega => ∑ index ∈ Finset.range steps, Z index omega) =
          ∑ index ∈ Finset.range steps, Z index := by
        ext omega
        simp
      rw [hsum]
      exact ProbabilityTheory.IndepFun.variance_sum
        (fun index _ => hZ_memLp index)
        (fun i hi j hj hij => hZ_indep.indepFun hij)
    _ = ∑ index ∈ Finset.range steps,
        ∫ omega, (Y (index + 1) omega - means index) ^ 2 ∂μ := by
      apply Finset.sum_congr rfl
      intro index _
      rw [ProbabilityTheory.variance_of_integral_eq_zero
        (hZ_memLp index).aemeasurable (hZ_mean index)]

/-- Doob's inequality for an independent centered partial sum, with its
terminal second moment expanded into the sum of coordinate second moments. -/
theorem ennreal_mul_measure_range_sup_sq_le_sum_integral_sq_shiftedCenteredPartialSum
    {Y : ℕ → Ω → ℝ} [IsFiniteMeasure μ]
    (hY_memLp : ∀ index, MemLp (Y index) 2 μ)
    (hY_meas : ∀ index, StronglyMeasurable (Y index))
    (hY_indep : iIndepFun Y μ) (means : ℕ → ℝ)
    (hmeans : ∀ index, means index = ∫ omega, Y (index + 1) omega ∂μ)
    (threshold : ℝ≥0) (steps : ℕ) :
    threshold * μ {omega | (threshold : ℝ) ≤
      (Finset.range (steps + 1)).sup' Finset.nonempty_range_add_one
        (fun index => (shiftedCenteredPartialSum Y means index omega) ^ 2)} ≤
      ENNReal.ofReal (∑ index ∈ Finset.range steps,
        ∫ omega, (Y (index + 1) omega - means index) ^ 2 ∂μ) := by
  calc
    threshold * μ {omega | (threshold : ℝ) ≤
        (Finset.range (steps + 1)).sup' Finset.nonempty_range_add_one
          (fun index => (shiftedCenteredPartialSum Y means index omega) ^ 2)} ≤
        ENNReal.ofReal (∫ omega,
          (shiftedCenteredPartialSum Y means steps omega) ^ 2 ∂μ) :=
      AppliedModelingLib.ennreal_mul_measure_range_sup_sq_le_integral_sq
        (shiftedCenteredPartialSum_martingale
          hY_meas
          (fun index => (hY_memLp index).integrable one_le_two)
          hY_indep means hmeans)
        (memLp_two_shiftedCenteredPartialSum hY_memLp means) threshold steps
    _ = ENNReal.ofReal (∑ index ∈ Finset.range steps,
        ∫ omega, (Y (index + 1) omega - means index) ^ 2 ∂μ) := by
      rw [integral_sq_shiftedCenteredPartialSum hY_memLp hY_indep means hmeans steps]

/-- Doob's fourth-moment maximal inequality for an independent centered
partial sum.  The terminal fourth moment is intentionally left explicit: a
caller can supply the sharp model-specific fourth-moment calculation needed
for a modulus-of-continuity estimate. -/
theorem ennreal_mul_measure_range_sup_fourth_le_integral_fourth_shiftedCenteredPartialSum
    {Y : ℕ → Ω → ℝ} [IsFiniteMeasure μ]
    (hY_memLp : ∀ index, MemLp (Y index) 4 μ)
    (hY_meas : ∀ index, StronglyMeasurable (Y index))
    (hY_indep : iIndepFun Y μ) (means : ℕ → ℝ)
    (hmeans : ∀ index, means index = ∫ omega, Y (index + 1) omega ∂μ)
    (threshold : ℝ≥0) (steps : ℕ) :
    threshold * μ {omega | (threshold : ℝ) ≤
      (Finset.range (steps + 1)).sup' Finset.nonempty_range_add_one
        (fun index => (shiftedCenteredPartialSum Y means index omega) ^ 4)} ≤
      ENNReal.ofReal (∫ omega,
        (shiftedCenteredPartialSum Y means steps omega) ^ 4 ∂μ) := by
  calc
    threshold * μ {omega | (threshold : ℝ) ≤
        (Finset.range (steps + 1)).sup' Finset.nonempty_range_add_one
          (fun index => (shiftedCenteredPartialSum Y means index omega) ^ 4)} ≤
        ENNReal.ofReal (∫ omega,
          (shiftedCenteredPartialSum Y means steps omega) ^ 4 ∂μ) :=
      AppliedModelingLib.ennreal_mul_measure_range_sup_fourth_le_integral_fourth
        (shiftedCenteredPartialSum_martingale
          hY_meas
          (fun index => (hY_memLp index).integrable (by norm_num))
          hY_indep means hmeans)
        (fun index => memLp_four_shiftedCenteredPartialSum hY_memLp means index)
        threshold steps

end AppliedModelingLib.Probability
