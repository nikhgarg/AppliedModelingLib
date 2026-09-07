import AppliedModelingLib.Foundations.Probability.FiniteIID
import AppliedModelingLib.Foundations.Probability.IidPrefixStopping
import AppliedModelingLib.Foundations.Probability.IndependentCenteredSums

/-!
# Maximal bounds for finite iid samples

This module transfers the discrete-time maximal inequality for an infinite
iid stream to the finite product law of a fixed iid sample.  The result is
stated in terms of literal finite prefixes, so callers with a checked finite
product law can use it without choosing an auxiliary infinite realization.
-/

namespace AppliedModelingLib.Probability

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

/-- The sum of a finite real sample through the first `steps` coordinates;
when `steps` exceeds the sample size, the full sample is used. -/
def finiteIIDPrefixSum (count : ℕ) (sample : Fin count → ℝ) (steps : ℕ) : ℝ :=
  if hsteps : steps ≤ count then
    ∑ index : Fin steps, sample (Fin.castLE hsteps index)
  else
    ∑ index : Fin count, sample index

/-- The whole finite prefix-sum trajectory of a real sample, including the
zero prefix.  Unlike the maximal-event wrappers below, this is a reusable
finite-dimensional linear transform and is therefore suitable for transport
through weak convergence. -/
noncomputable def finiteIIDPrefixSumVector (count : ℕ) (sample : Fin count → ℝ) :
    Fin (count + 1) → ℝ :=
  fun steps => finiteIIDPrefixSum count sample steps.val

@[simp]
theorem finiteIIDPrefixSumVector_apply (count : ℕ) (sample : Fin count → ℝ)
    (steps : Fin (count + 1)) :
    finiteIIDPrefixSumVector count sample steps = finiteIIDPrefixSum count sample steps.val := rfl

/-- Taking all finite prefix sums is continuous in the input finite vector. -/
theorem continuous_finiteIIDPrefixSumVector (count : ℕ) :
    Continuous (finiteIIDPrefixSumVector count) := by
  rw [continuous_pi_iff]
  intro steps
  have hsteps : steps.val ≤ count := Nat.le_of_lt_succ steps.isLt
  change Continuous (fun sample : Fin count → ℝ =>
    finiteIIDPrefixSum count sample steps.val)
  simp only [finiteIIDPrefixSum, dif_pos hsteps]
  exact continuous_finset_sum Finset.univ
    (fun index _ => continuous_apply (Fin.castLE hsteps index))

/-- If a finite vector records consecutive differences of another vector,
its prefix-sum vector recovers the latter relative to its initial value. -/
theorem finiteIIDPrefixSumVector_eq_sub_of_increment_eq
    (count : ℕ) (increments : Fin count → ℝ) (values : Fin (count + 1) → ℝ)
    (hincrement : ∀ index : Fin count,
      increments index = values index.succ - values index.castSucc) :
    finiteIIDPrefixSumVector count increments = fun index => values index - values 0 := by
  funext steps
  have hsteps : steps.val ≤ count := Nat.le_of_lt_succ steps.isLt
  let valueAt : ℕ → ℝ := fun index =>
    if hindex : index ≤ count then values ⟨index, Nat.lt_succ_of_le hindex⟩ else values 0
  have hcoordinate : ∀ index : Fin count,
      increments index = valueAt (index.val + 1) - valueAt index.val := by
    intro index
    rw [hincrement index]
    simp only [valueAt, dif_pos (Nat.succ_le_of_lt index.isLt), dif_pos index.isLt.le]
    congr 1
  change finiteIIDPrefixSum count increments steps.val = values steps - values 0
  simp only [finiteIIDPrefixSum, dif_pos hsteps]
  calc
    ∑ index : Fin steps.val, increments (Fin.castLE hsteps index) =
        ∑ index : Fin steps.val,
          (valueAt (index.val + 1) - valueAt index.val) := by
            apply Finset.sum_congr rfl
            intro index _
            simpa using hcoordinate (Fin.castLE hsteps index)
    _ = ∑ index ∈ Finset.range steps.val,
        (valueAt (index + 1) - valueAt index) := by
          simpa using (Fin.sum_univ_eq_sum_range
            (fun index => valueAt (index + 1) - valueAt index) steps.val)
    _ = valueAt steps.val - valueAt 0 := by
          exact Finset.sum_range_sub valueAt steps.val
    _ = values steps - values 0 := by
          simp only [valueAt, dif_pos hsteps, dif_pos (Nat.zero_le count)]
          congr 1

/-- Finite iid prefix sums are measurable. -/
theorem measurable_finiteIIDPrefixSum (count steps : ℕ) :
    Measurable (fun sample : Fin count → ℝ => finiteIIDPrefixSum count sample steps) := by
  by_cases hsteps : steps ≤ count
  · simp only [finiteIIDPrefixSum, dif_pos hsteps]
    apply Finset.measurable_sum
    intro index _
    exact measurable_pi_apply (Fin.castLE hsteps index)
  · simp only [finiteIIDPrefixSum, dif_neg hsteps]
    apply Finset.measurable_sum
    intro index _
    exact measurable_pi_apply index

/-- The finite iid maximal-square event through a full sample. -/
def finiteIIDPrefixMaximumSqEvent (count : ℕ) (threshold : ℝ≥0) :
    Set (Fin count → ℝ) :=
  {sample | (threshold : ℝ) ≤
    (Finset.range (count + 1)).sup' Finset.nonempty_range_add_one
      (fun steps => (finiteIIDPrefixSum count sample steps) ^ 2)}

/-- The finite iid maximal-fourth-power event through a full sample. -/
def finiteIIDPrefixMaximumFourthEvent (count : ℕ) (threshold : ℝ≥0) :
    Set (Fin count → ℝ) :=
  {sample | (threshold : ℝ) ≤
    (Finset.range (count + 1)).sup' Finset.nonempty_range_add_one
      (fun steps => (finiteIIDPrefixSum count sample steps) ^ 4)}

/-- The finite iid maximal-square event is measurable. -/
theorem measurableSet_finiteIIDPrefixMaximumSqEvent (count : ℕ) (threshold : ℝ≥0) :
    MeasurableSet (finiteIIDPrefixMaximumSqEvent count threshold) := by
  change MeasurableSet {sample | (threshold : ℝ) ≤
    (Finset.range (count + 1)).sup' Finset.nonempty_range_add_one
      (fun steps => (finiteIIDPrefixSum count sample steps) ^ 2)}
  exact measurableSet_le measurable_const (by
    simpa [pow_two] using Finset.measurable_range_sup'' fun steps _ =>
        (measurable_finiteIIDPrefixSum count steps).mul
        (measurable_finiteIIDPrefixSum count steps))

/-- The finite iid maximal-fourth-power event is measurable. -/
theorem measurableSet_finiteIIDPrefixMaximumFourthEvent (count : ℕ) (threshold : ℝ≥0) :
    MeasurableSet (finiteIIDPrefixMaximumFourthEvent count threshold) := by
  change MeasurableSet {sample | (threshold : ℝ) ≤
    (Finset.range (count + 1)).sup' Finset.nonempty_range_add_one
      (fun steps => (finiteIIDPrefixSum count sample steps) ^ 4)}
  exact measurableSet_le measurable_const (by
    simpa [pow_succ] using Finset.measurable_range_sup'' fun steps _ =>
      (((measurable_finiteIIDPrefixSum count steps).mul
        (measurable_finiteIIDPrefixSum count steps)).mul
        (measurable_finiteIIDPrefixSum count steps)).mul
        (measurable_finiteIIDPrefixSum count steps))

/-- A finite iid sample inherits the L² maximal inequality from an iid stream.
The common coordinate law is assumed centered, and the conclusion keeps the
literal finite-product measure. -/
theorem ennreal_mul_measure_finiteIIDPrefixMaximumSqEvent_le
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hmean : ∫ value, value ∂ν = 0) (hmem : MemLp id 2 ν)
    (count : ℕ) (threshold : ℝ≥0) :
    threshold * finiteIIDSampleLaw ν count
      (finiteIIDPrefixMaximumSqEvent count threshold) ≤
      ENNReal.ofReal (count * ∫ value, value ^ 2 ∂ν) := by
  let streamLaw : Measure (ℕ → ℝ) := IIDStream.measure ν
  let raw : ℕ → (ℕ → ℝ) → ℝ := IIDStream.coordinate
  let block : (ℕ → ℝ) → Fin count → ℝ := IIDStream.block 1 count
  letI : IsProbabilityMeasure streamLaw := by
    dsimp [streamLaw, IIDStream.measure]
    infer_instance
  have hraw_memLp : ∀ index, MemLp (raw index) 2 streamLaw := by
    intro index
    simpa [raw, Function.comp_def, streamLaw] using
      hmem.comp_measurePreserving (IIDStream.coordinate_measurePreserving ν index)
  have hraw_meas : ∀ index, StronglyMeasurable (raw index) := by
    intro index
    exact (IIDStream.measurable_coordinate index).stronglyMeasurable
  have hraw_indep : iIndepFun raw streamLaw := by
    simpa [raw, streamLaw] using IIDStream.iIndepFun_coordinate ν
  have hraw_mean : ∀ index, (0 : ℝ) = ∫ omega, raw (index + 1) omega ∂streamLaw := by
    intro index
    symm
    calc
      ∫ omega, raw (index + 1) omega ∂streamLaw = ∫ value, value ∂ν := by
        simpa [raw, streamLaw] using
          (IIDStream.coordinate_hasLaw ν (index + 1)).integral_comp
            (f := id) (hmem.integrable one_le_two).aestronglyMeasurable
      _ = 0 := hmean
  have hraw_sq : ∀ index, ∫ omega,
      (raw (index + 1) omega - 0) ^ 2 ∂streamLaw = ∫ value, value ^ 2 ∂ν := by
    intro index
    simpa [raw, streamLaw] using
      (IIDStream.coordinate_hasLaw ν (index + 1)).integral_comp
        (f := fun value : ℝ => value ^ 2) hmem.integrable_sq.aestronglyMeasurable
  have hblock : HasLaw block (finiteIIDSampleLaw ν count) streamLaw := by
    simpa [block, streamLaw, finiteIIDSampleLaw] using
      IIDStream.block_hasLaw ν 1 count
  have hblock_meas : Measurable block := by
    simpa [block] using IIDStream.measurable_block (α := ℝ) 1 count
  let event : Set (ℕ → ℝ) := {omega | (threshold : ℝ) ≤
    (Finset.range (count + 1)).sup' Finset.nonempty_range_add_one
      (fun steps => (shiftedCenteredPartialSum raw (fun _ => 0) steps omega) ^ 2)}
  have hevent : block ⁻¹' finiteIIDPrefixMaximumSqEvent count threshold = event := by
    ext omega
    simp only [Set.mem_preimage, finiteIIDPrefixMaximumSqEvent, Set.mem_setOf_eq, event]
    have hsup :
        (Finset.range (count + 1)).sup' Finset.nonempty_range_add_one
            (fun steps => (finiteIIDPrefixSum count (block omega) steps) ^ 2) =
          (Finset.range (count + 1)).sup' Finset.nonempty_range_add_one
            (fun steps => (shiftedCenteredPartialSum raw (fun _ => 0) steps omega) ^ 2) := by
      apply Finset.sup'_congr Finset.nonempty_range_add_one rfl
      intro steps hsteps
      have hsteps_le : steps ≤ count := Nat.le_of_lt_succ (Finset.mem_range.mp hsteps)
      congr 1
      unfold shiftedCenteredPartialSum block raw IIDStream.block
      simp only [finiteIIDPrefixSum, dif_pos hsteps_le, IIDStream.coordinate, sub_zero]
      simpa [Nat.add_comm] using
        (Fin.sum_univ_eq_sum_range (fun index => omega (1 + index)) steps)
    rw [hsup]
  have hmeasure : streamLaw (block ⁻¹' finiteIIDPrefixMaximumSqEvent count threshold) =
      finiteIIDSampleLaw ν count (finiteIIDPrefixMaximumSqEvent count threshold) := by
    rw [← Measure.map_apply hblock_meas
      (measurableSet_finiteIIDPrefixMaximumSqEvent count threshold), hblock.map_eq]
  have hmax := ennreal_mul_measure_range_sup_sq_le_sum_integral_sq_shiftedCenteredPartialSum
    hraw_memLp hraw_meas hraw_indep (fun _ => 0) hraw_mean threshold count
  have hsum_sq : (∑ index ∈ Finset.range count, ∫ omega,
      (raw (index + 1) omega - 0) ^ 2 ∂streamLaw) =
      count * ∫ value, value ^ 2 ∂ν := by
    simp_rw [hraw_sq]
    simp
  calc
    threshold * finiteIIDSampleLaw ν count
        (finiteIIDPrefixMaximumSqEvent count threshold) =
        threshold * streamLaw (block ⁻¹' finiteIIDPrefixMaximumSqEvent count threshold) := by
      rw [hmeasure]
    _ = threshold * streamLaw event := by rw [hevent]
    _ ≤ ENNReal.ofReal (∑ index ∈ Finset.range count, ∫ omega,
        (raw (index + 1) omega - 0) ^ 2 ∂streamLaw) := hmax
    _ = ENNReal.ofReal (count * ∫ value, value ^ 2 ∂ν) := by rw [hsum_sq]

/-- A finite iid sample inherits fourth-moment Doob control from an iid
stream.  The terminal fourth moment stays explicit so model-specific users
can apply their sharp endpoint calculation without weakening the maximal
estimate. -/
theorem ennreal_mul_measure_finiteIIDPrefixMaximumFourthEvent_le_integral_fourth
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hmean : ∫ value, value ∂ν = 0) (hmem : MemLp id 4 ν)
    (count : ℕ) (threshold : ℝ≥0) :
    threshold * finiteIIDSampleLaw ν count
      (finiteIIDPrefixMaximumFourthEvent count threshold) ≤
      ENNReal.ofReal (∫ sample,
        (finiteIIDPrefixSum count sample count) ^ 4 ∂finiteIIDSampleLaw ν count) := by
  let streamLaw : Measure (ℕ → ℝ) := IIDStream.measure ν
  let raw : ℕ → (ℕ → ℝ) → ℝ := IIDStream.coordinate
  let block : (ℕ → ℝ) → Fin count → ℝ := IIDStream.block 1 count
  letI : IsProbabilityMeasure streamLaw := by
    dsimp [streamLaw, IIDStream.measure]
    infer_instance
  have hraw_memLp : ∀ index, MemLp (raw index) 4 streamLaw := by
    intro index
    simpa [raw, Function.comp_def, streamLaw] using
      hmem.comp_measurePreserving (IIDStream.coordinate_measurePreserving ν index)
  have hraw_meas : ∀ index, StronglyMeasurable (raw index) := by
    intro index
    exact (IIDStream.measurable_coordinate index).stronglyMeasurable
  have hraw_indep : iIndepFun raw streamLaw := by
    simpa [raw, streamLaw] using IIDStream.iIndepFun_coordinate ν
  have hraw_mean : ∀ index, (0 : ℝ) = ∫ omega, raw (index + 1) omega ∂streamLaw := by
    intro index
    symm
    calc
      ∫ omega, raw (index + 1) omega ∂streamLaw = ∫ value, value ∂ν := by
        simpa [raw, streamLaw] using
          (IIDStream.coordinate_hasLaw ν (index + 1)).integral_comp
            (f := id) (hmem.integrable (by norm_num)).aestronglyMeasurable
      _ = 0 := hmean
  have hblock : HasLaw block (finiteIIDSampleLaw ν count) streamLaw := by
    simpa [block, streamLaw, finiteIIDSampleLaw] using
      IIDStream.block_hasLaw ν 1 count
  have hblock_meas : Measurable block := by
    simpa [block] using IIDStream.measurable_block (α := ℝ) 1 count
  let event : Set (ℕ → ℝ) := {omega | (threshold : ℝ) ≤
    (Finset.range (count + 1)).sup' Finset.nonempty_range_add_one
      (fun steps => (shiftedCenteredPartialSum raw (fun _ => 0) steps omega) ^ 4)}
  have hprefix : ∀ omega steps, steps ≤ count →
      finiteIIDPrefixSum count (block omega) steps =
        shiftedCenteredPartialSum raw (fun _ => 0) steps omega := by
    intro omega steps hsteps
    unfold shiftedCenteredPartialSum block raw IIDStream.block
    simp only [finiteIIDPrefixSum, dif_pos hsteps, IIDStream.coordinate, sub_zero]
    simpa [Nat.add_comm] using
      (Fin.sum_univ_eq_sum_range (fun index => omega (1 + index)) steps)
  have hevent : block ⁻¹' finiteIIDPrefixMaximumFourthEvent count threshold = event := by
    ext omega
    simp only [Set.mem_preimage, finiteIIDPrefixMaximumFourthEvent, Set.mem_setOf_eq, event]
    have hsup :
        (Finset.range (count + 1)).sup' Finset.nonempty_range_add_one
            (fun steps => (finiteIIDPrefixSum count (block omega) steps) ^ 4) =
          (Finset.range (count + 1)).sup' Finset.nonempty_range_add_one
            (fun steps => (shiftedCenteredPartialSum raw (fun _ => 0) steps omega) ^ 4) := by
      apply Finset.sup'_congr Finset.nonempty_range_add_one rfl
      intro steps hsteps
      exact congrArg (fun value : ℝ => value ^ 4)
        (hprefix omega steps (Nat.le_of_lt_succ (Finset.mem_range.mp hsteps)))
    rw [hsup]
  have hmeasure : streamLaw (block ⁻¹' finiteIIDPrefixMaximumFourthEvent count threshold) =
      finiteIIDSampleLaw ν count (finiteIIDPrefixMaximumFourthEvent count threshold) := by
    rw [← Measure.map_apply hblock_meas
      (measurableSet_finiteIIDPrefixMaximumFourthEvent count threshold), hblock.map_eq]
  have hterminal : (∫ omega,
      (shiftedCenteredPartialSum raw (fun _ => 0) count omega) ^ 4 ∂streamLaw) =
      ∫ sample, (finiteIIDPrefixSum count sample count) ^ 4 ∂finiteIIDSampleLaw ν count := by
    have hfourth_meas : AEStronglyMeasurable
        (fun sample : Fin count → ℝ => (finiteIIDPrefixSum count sample count) ^ 4)
        (finiteIIDSampleLaw ν count) := by
      simpa [pow_succ] using
        ((((measurable_finiteIIDPrefixSum count count).mul
          (measurable_finiteIIDPrefixSum count count)).mul
          (measurable_finiteIIDPrefixSum count count)).mul
          (measurable_finiteIIDPrefixSum count count)).aestronglyMeasurable
    rw [← show (fun omega => finiteIIDPrefixSum count (block omega) count) =
        shiftedCenteredPartialSum raw (fun _ => 0) count by
      funext omega
      exact hprefix omega count le_rfl]
    simpa only [Function.comp_apply] using
      hblock.integral_comp (f := fun sample => (finiteIIDPrefixSum count sample count) ^ 4)
        hfourth_meas
  have hmax :=
    ennreal_mul_measure_range_sup_fourth_le_integral_fourth_shiftedCenteredPartialSum
      hraw_memLp hraw_meas hraw_indep (fun _ => 0) hraw_mean threshold count
  calc
    threshold * finiteIIDSampleLaw ν count
        (finiteIIDPrefixMaximumFourthEvent count threshold) =
        threshold * streamLaw (block ⁻¹' finiteIIDPrefixMaximumFourthEvent count threshold) := by
      rw [hmeasure]
    _ = threshold * streamLaw event := by rw [hevent]
    _ ≤ ENNReal.ofReal (∫ omega,
        (shiftedCenteredPartialSum raw (fun _ => 0) count omega) ^ 4 ∂streamLaw) := hmax
    _ = ENNReal.ofReal (∫ sample,
        (finiteIIDPrefixSum count sample count) ^ 4 ∂finiteIIDSampleLaw ν count) := by
      rw [hterminal]

end

end AppliedModelingLib.Probability
