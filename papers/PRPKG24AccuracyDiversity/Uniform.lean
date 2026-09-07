import PRPKG24AccuracyDiversity.Exchange
import PRPKG24AccuracyDiversity.TopKOracle
import AppliedModelingLib.Foundations.Math.BinomialBounds
import AppliedModelingLib.Foundations.Math.GammaAsymptotics
import AppliedModelingLib.Foundations.Probability.RealDistribution
import AppliedModelingLib.Foundations.Math.FiniteRounding
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Probability.ConditionalProbability
import Mathlib.Tactic.Linarith

open scoped BigOperators
open MeasureTheory Set

namespace PRPKG24AccuracyDiversity

/-- The continuous uniform probability measure on `[0,1]`. -/
noncomputable def uniform01Measure : Measure ℝ := ProbabilityTheory.cond volume (Set.Icc (0 : ℝ) 1)

instance uniform01Measure_isProbabilityMeasure :
    IsProbabilityMeasure uniform01Measure := by
  unfold uniform01Measure
  exact ProbabilityTheory.cond_isProbabilityMeasure_of_finite
    (μ := volume) (s := Set.Icc (0 : ℝ) 1)
    (by simp) (by simp)

theorem uniform01Measure_ae_bounds :
    ∀ᵐ y ∂uniform01Measure, 0 ≤ y ∧ y ≤ 1 := by
  simpa [uniform01Measure] using
    (ProbabilityTheory.ae_cond_mem
      (μ := volume) (s := Set.Icc (0 : ℝ) 1) measurableSet_Icc)

theorem uniform01Measure_real_eq_volume_real_inter
    (t : Set ℝ) :
    uniform01Measure.real t =
      volume.real (t ∩ Set.Icc (0 : ℝ) 1) := by
  unfold uniform01Measure ProbabilityTheory.cond
  simp [Real.volume_Icc]

theorem uniform01_reflectedCDFMass_eq {x : ℝ}
    (hx_pos : 0 < x) (hx_lt_one : x < 1) :
    AppliedModelingLib.Probability.reflectedCDFMass uniform01Measure 1 x = x := by
  let t : Set ℝ := {y : ℝ | (1 : ℝ) ≤ x + y}
  have ht_inter :
      t ∩ Set.Icc (0 : ℝ) 1 = Set.Icc (1 - x) 1 := by
    ext y
    constructor
    · intro hy
      have hyt : 1 ≤ x + y := by simpa [t] using hy.1
      exact ⟨by linarith [hyt], hy.2.2⟩
    · intro hy
      constructor
      · change 1 ≤ x + y
        linarith [hy.1]
      · exact ⟨by linarith [hy.1, hx_lt_one], hy.2⟩
  have hle : 1 - x ≤ (1 : ℝ) := by linarith
  calc
    AppliedModelingLib.Probability.reflectedCDFMass uniform01Measure 1 x =
        uniform01Measure.real t := by rfl
    _ = volume.real (t ∩ Set.Icc (0 : ℝ) 1) :=
        uniform01Measure_real_eq_volume_real_inter t
    _ = volume.real (Set.Icc (1 - x) 1) := by rw [ht_inter]
    _ = x := by
      rw [Real.volume_real_Icc_of_le hle]
      ring

theorem uniform01_reflectedCDFMass_eventually_eq_power :
    ∀ᶠ x in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
      AppliedModelingLib.Probability.reflectedCDFMass uniform01Measure 1 x =
        (1 / 1 : ℝ) * x ^ (1 : ℝ) := by
  filter_upwards
    [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))]
    with x hx_pos hx_lt_one
  rw [uniform01_reflectedCDFMass_eq hx_pos hx_lt_one]
  simp

theorem uniform01Measure_real_Ioi_eq {x : ℝ}
    (hx_nonneg : 0 ≤ x) (hx_le_one : x ≤ 1) :
    uniform01Measure.real (Set.Ioi x) = 1 - x := by
  have hinter :
      Set.Ioi x ∩ Set.Icc (0 : ℝ) 1 = Set.Ioc x 1 := by
    ext y
    constructor
    · intro hy
      exact ⟨hy.1, hy.2.2⟩
    · intro hy
      exact ⟨hy.1, ⟨le_trans hx_nonneg (le_of_lt hy.1), hy.2⟩⟩
  calc
    uniform01Measure.real (Set.Ioi x) =
        volume.real (Set.Ioi x ∩ Set.Icc (0 : ℝ) 1) :=
          uniform01Measure_real_eq_volume_real_inter (Set.Ioi x)
    _ = volume.real (Set.Ioc x 1) := by rw [hinter]
    _ = 1 - x := Real.volume_real_Ioc_of_le hx_le_one

theorem uniform01Measure_real_Iic_eq {x : ℝ}
    (hx_nonneg : 0 ≤ x) (hx_le_one : x ≤ 1) :
    uniform01Measure.real (Set.Iic x) = x := by
  have hinter :
      Set.Iic x ∩ Set.Icc (0 : ℝ) 1 = Set.Icc 0 x := by
    ext y
    constructor
    · intro hy
      exact ⟨hy.2.1, hy.1⟩
    · intro hy
      exact ⟨hy.2, ⟨hy.1, le_trans hy.2 hx_le_one⟩⟩
  calc
    uniform01Measure.real (Set.Iic x) =
        volume.real (Set.Iic x ∩ Set.Icc (0 : ℝ) 1) :=
          uniform01Measure_real_eq_volume_real_inter (Set.Iic x)
    _ = volume.real (Set.Icc 0 x) := by rw [hinter]
    _ = x := by
      rw [Real.volume_real_Icc_of_le hx_nonneg]
      ring

/--
The reflected-power source map used for the bounded-support power-tail
examples: if `U` is uniform on `[0,1]`, then `1 - U^(1 / beta)` has upper-tail
mass `x ^ beta` at distance `x` from the endpoint `1`.
-/
noncomputable def boundedReflectedPowerSourceMap (beta : ℝ) (u : ℝ) : ℝ :=
  1 - u ^ (1 / beta)

/-- The bounded reflected-power source law as a pushforward of `uniform01Measure`. -/
noncomputable def boundedReflectedPowerSourceMeasure (beta : ℝ) : Measure ℝ :=
  Measure.map (boundedReflectedPowerSourceMap beta) uniform01Measure

instance boundedReflectedPowerSourceMeasure_isProbabilityMeasure (beta : ℝ) :
    IsProbabilityMeasure (boundedReflectedPowerSourceMeasure beta) := by
  unfold boundedReflectedPowerSourceMeasure
  exact Measure.isProbabilityMeasure_map
    ((by
      fun_prop : Measurable (fun u : ℝ => 1 - u ^ (1 / beta))).aemeasurable)

theorem boundedReflectedPowerSourceMeasure_ae_bounds {beta : ℝ}
    (hbeta_pos : 0 < beta) :
    ∀ᵐ y ∂boundedReflectedPowerSourceMeasure beta, 0 ≤ y ∧ y ≤ 1 := by
  let f : ℝ → ℝ := boundedReflectedPowerSourceMap beta
  have hf : Measurable f := by
    change Measurable (fun u : ℝ => 1 - u ^ (1 / beta))
    fun_prop
  rw [boundedReflectedPowerSourceMeasure,
    MeasureTheory.ae_map_iff hf.aemeasurable measurableSet_Icc]
  filter_upwards [uniform01Measure_ae_bounds] with u hu
  have hinv_nonneg : 0 ≤ 1 / beta := (one_div_pos.mpr hbeta_pos).le
  have hpow_nonneg : 0 ≤ u ^ (1 / beta) :=
    Real.rpow_nonneg hu.1 _
  have hpow_le_one : u ^ (1 / beta) ≤ 1 := by
    have hle := Real.rpow_le_rpow hu.1 hu.2 hinv_nonneg
    simpa using hle
  dsimp [f, boundedReflectedPowerSourceMap]
  exact ⟨by linarith, by linarith⟩

theorem boundedReflectedPowerSourceMeasure_real_upper_endpoint_eq_power
    {beta x : ℝ} (hbeta_pos : 0 < beta)
    (hx_pos : 0 < x) (hx_lt_one : x < 1) :
    (boundedReflectedPowerSourceMeasure beta).real (Set.Ici (1 - x)) =
      x ^ beta := by
  let f : ℝ → ℝ := boundedReflectedPowerSourceMap beta
  have hf : Measurable f := by
    change Measurable (fun u : ℝ => 1 - u ^ (1 / beta))
    fun_prop
  have hinv_pos : 0 < 1 / beta := one_div_pos.mpr hbeta_pos
  have hxpow_nonneg : 0 ≤ x ^ beta := Real.rpow_nonneg hx_pos.le beta
  have hxpow_lt_one : x ^ beta < 1 := by
    rw [Real.rpow_lt_one_iff hx_pos.le]
    exact Or.inr (Or.inr ⟨hx_lt_one, hbeta_pos⟩)
  have hxpow_le_one : x ^ beta ≤ 1 := le_of_lt hxpow_lt_one
  have hxpow_inv : (x ^ beta) ^ (1 / beta) = x := by
    simpa [one_div] using
      Real.rpow_rpow_inv hx_pos.le hbeta_pos.ne'
  have hpre_inter :
      f ⁻¹' Set.Ici (1 - x) ∩ Set.Icc (0 : ℝ) 1 =
        Set.Icc 0 (x ^ beta) := by
    ext u
    constructor
    · intro hu
      have hu_nonneg : 0 ≤ u := hu.2.1
      have hpre : 1 - x ≤ 1 - u ^ (1 / beta) := by
        simpa [f, boundedReflectedPowerSourceMap] using hu.1
      have hpow_le_x : u ^ (1 / beta) ≤ x := by linarith
      have hle_pow :
          (u ^ (1 / beta)) ^ beta ≤ x ^ beta :=
        Real.rpow_le_rpow (Real.rpow_nonneg hu_nonneg _) hpow_le_x hbeta_pos.le
      have hpow_eq_u : (u ^ beta⁻¹) ^ beta = u := by
        simpa [one_div] using
          Real.rpow_inv_rpow hu_nonneg hbeta_pos.ne'
      have hle_u : u ≤ x ^ beta := by
        simpa [one_div, hpow_eq_u] using hle_pow
      exact ⟨hu_nonneg, hle_u⟩
    · intro hu
      have hu_nonneg : 0 ≤ u := hu.1
      have hpow_le_x : u ^ (1 / beta) ≤ x := by
        have hle_pow :
            u ^ (1 / beta) ≤ (x ^ beta) ^ (1 / beta) :=
          Real.rpow_le_rpow hu_nonneg hu.2 hinv_pos.le
        have hxpow_inv' : (x ^ beta) ^ beta⁻¹ = x := by
          simpa [one_div] using hxpow_inv
        simpa [one_div, hxpow_inv'] using hle_pow
      have hpre : 1 - x ≤ 1 - u ^ (1 / beta) := by linarith
      exact
        ⟨by
          simpa [f, boundedReflectedPowerSourceMap] using hpre,
         ⟨hu_nonneg, le_trans hu.2 hxpow_le_one⟩⟩
  calc
    (boundedReflectedPowerSourceMeasure beta).real (Set.Ici (1 - x)) =
        uniform01Measure.real (f ⁻¹' Set.Ici (1 - x)) := by
          rw [boundedReflectedPowerSourceMeasure, Measure.real,
            Measure.map_apply hf measurableSet_Ici]
          rfl
    _ = volume.real
        (f ⁻¹' Set.Ici (1 - x) ∩ Set.Icc (0 : ℝ) 1) :=
          uniform01Measure_real_eq_volume_real_inter
            (f ⁻¹' Set.Ici (1 - x))
    _ = volume.real (Set.Icc 0 (x ^ beta)) := by rw [hpre_inter]
    _ = x ^ beta := by
      rw [Real.volume_real_Icc_of_le hxpow_nonneg]
      ring

theorem boundedReflectedPowerSourceMeasure_real_upper_endpoint_eventually_eq_power
    {beta : ℝ} (hbeta_pos : 0 < beta) :
    ∀ᶠ x in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
      (boundedReflectedPowerSourceMeasure beta).real (Set.Ici (1 - x)) =
        x ^ beta := by
  filter_upwards
    [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds
        (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))]
    with x hx_pos hx_lt_one
  exact boundedReflectedPowerSourceMeasure_real_upper_endpoint_eq_power
    hbeta_pos hx_pos hx_lt_one

theorem boundedReflectedPowerProductMeasure_all_bounds_ae {beta : ℝ}
    (hbeta_pos : 0 < beta) (q : ℕ) :
    ∀ᵐ sample ∂MeasureTheory.Measure.pi
        (fun _ : Fin q => boundedReflectedPowerSourceMeasure beta),
      ∀ i : Fin q, 0 ≤ sample i ∧ sample i ≤ 1 := by
  simpa using
    AppliedModelingLib.Probability.iidProductMeasure_forall_bounds_ae
      (n := q) (boundedReflectedPowerSourceMeasure beta)
      (boundedReflectedPowerSourceMeasure_ae_bounds hbeta_pos)

theorem
    boundedReflectedPowerProductMeasure_reflectedAscendingOrderStatistic_nonnegative_ae
    {beta : ℝ} (hbeta_pos : 0 < beta) {q : ℕ} (rank : Fin q) :
    (fun _sample : Fin q → ℝ => (0 : ℝ)) ≤ᵐ[
      MeasureTheory.Measure.pi
        (fun _ : Fin q => boundedReflectedPowerSourceMeasure beta)]
      fun sample =>
        AppliedModelingLib.Probability.ascendingOrderStatistic
          (AppliedModelingLib.Probability.reflectedSample 1 sample) rank := by
  filter_upwards [boundedReflectedPowerProductMeasure_all_bounds_ae
    hbeta_pos q] with sample hsample
  exact
    AppliedModelingLib.Probability.le_ascendingOrderStatistic_of_forall_le
      (AppliedModelingLib.Probability.reflectedSample_nonneg_of_forall_le
        1 (fun i => (hsample i).2)) rank

theorem
    boundedReflectedPowerProductMeasure_reflectedAscendingOrderStatistic_integrable
    {beta : ℝ} (hbeta_pos : 0 < beta) {q : ℕ} (rank : Fin q) :
    MeasureTheory.Integrable
      (fun sample : Fin q → ℝ =>
        AppliedModelingLib.Probability.ascendingOrderStatistic
          (AppliedModelingLib.Probability.reflectedSample 1 sample) rank)
      (MeasureTheory.Measure.pi
        (fun _ : Fin q => boundedReflectedPowerSourceMeasure beta)) :=
  AppliedModelingLib.Probability.reflectedAscendingOrderStatistic_integrable_of_ae_bounds
    1 0
    (MeasureTheory.Measure.pi
      (fun _ : Fin q => boundedReflectedPowerSourceMeasure beta))
    rank (boundedReflectedPowerProductMeasure_all_bounds_ae hbeta_pos q)

theorem
    boundedReflectedPowerProductMeasure_reflectedAscendingOrderStatistic_gt_real
    {beta x : ℝ} (hbeta_pos : 0 < beta)
    (hx_pos : 0 < x) (hx_lt_one : x < 1)
    {q : ℕ} (rank : Fin q) :
    (MeasureTheory.Measure.pi
        (fun _ : Fin q => boundedReflectedPowerSourceMeasure beta)).real
        {sample : Fin q → ℝ |
          x < AppliedModelingLib.Probability.ascendingOrderStatistic
            (AppliedModelingLib.Probability.reflectedSample 1 sample) rank} =
      ∑ j ∈ Finset.Icc 0 rank.val,
        (Nat.choose q j : ℝ) *
          (x ^ beta) ^ j * (1 - x ^ beta) ^ (q - j) := by
  classical
  let μ : MeasureTheory.Measure (Fin q → ℝ) :=
    MeasureTheory.Measure.pi
      (fun _ : Fin q => boundedReflectedPowerSourceMeasure beta)
  haveI : MeasureTheory.IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  let successSet : Set ℝ := Set.Ici (1 - x)
  have hset :
      {sample : Fin q → ℝ |
          x < AppliedModelingLib.Probability.ascendingOrderStatistic
            (AppliedModelingLib.Probability.reflectedSample 1 sample) rank} =
        {sample : Fin q → ℝ |
          AppliedModelingLib.Probability.iidSuccessCount successSet sample ≤
            rank.val} := by
    ext sample
    have hcount :
        (Finset.univ.filter
            (fun i : Fin q =>
              AppliedModelingLib.Probability.reflectedSample 1 sample i ≤ x)).card =
          AppliedModelingLib.Probability.iidSuccessCount successSet sample := by
      unfold AppliedModelingLib.Probability.iidSuccessCount
        AppliedModelingLib.Probability.iidSuccessIndexSet successSet
      congr 1
      ext i
      constructor
      · intro hi
        have hle : 1 - sample i ≤ x := by
          simpa [AppliedModelingLib.Probability.reflectedSample] using
            (Finset.mem_filter.mp hi).2
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ i, by
            change 1 - x ≤ sample i
            linarith⟩
      · intro hi
        have hle : 1 - x ≤ sample i := (Finset.mem_filter.mp hi).2
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ i, by
            change 1 - sample i ≤ x
            linarith⟩
    have hiff :=
      AppliedModelingLib.Probability.ascendingOrderStatistic_rank_count_le_iff
        (AppliedModelingLib.Probability.reflectedSample 1 sample) rank x
    change
      x < AppliedModelingLib.Probability.ascendingOrderStatistic
          (AppliedModelingLib.Probability.reflectedSample 1 sample) rank ↔
        AppliedModelingLib.Probability.iidSuccessCount successSet sample ≤ rank.val
    rw [← hcount]
    exact hiff.symm
  have htail :
      (boundedReflectedPowerSourceMeasure beta).real successSet = x ^ beta := by
    simpa [successSet] using
      boundedReflectedPowerSourceMeasure_real_upper_endpoint_eq_power
        hbeta_pos hx_pos hx_lt_one
  have hmin : min rank.val q = rank.val :=
    min_eq_left (Nat.le_of_lt rank.isLt)
  rw [hset,
    AppliedModelingLib.Probability.iidProductMeasure_successCount_le_real
      (boundedReflectedPowerSourceMeasure beta) measurableSet_Ici rank.val]
  rw [hmin, htail]

theorem
    boundedReflectedPowerProductMeasure_reflectedAscendingOrderStatistic_gt_real_of_one_lt
    {beta x : ℝ} (hbeta_pos : 0 < beta) (hx : 1 < x)
    {q : ℕ} (rank : Fin q) :
    (MeasureTheory.Measure.pi
        (fun _ : Fin q => boundedReflectedPowerSourceMeasure beta)).real
        {sample : Fin q → ℝ |
          x < AppliedModelingLib.Probability.ascendingOrderStatistic
            (AppliedModelingLib.Probability.reflectedSample 1 sample) rank} =
      0 := by
  let μ : MeasureTheory.Measure (Fin q → ℝ) :=
    MeasureTheory.Measure.pi
      (fun _ : Fin q => boundedReflectedPowerSourceMeasure beta)
  have hset :
      {sample : Fin q → ℝ |
          x < AppliedModelingLib.Probability.ascendingOrderStatistic
            (AppliedModelingLib.Probability.reflectedSample 1 sample) rank}
        =ᵐ[μ] (∅ : Set (Fin q → ℝ)) := by
    filter_upwards [boundedReflectedPowerProductMeasure_all_bounds_ae
      hbeta_pos q] with sample hsample
    have hupper :
        AppliedModelingLib.Probability.ascendingOrderStatistic
            (AppliedModelingLib.Probability.reflectedSample 1 sample) rank ≤ 1 :=
      by
        simpa using
          AppliedModelingLib.Probability.ascendingOrderStatistic_le_of_forall_le
            (AppliedModelingLib.Probability.reflectedSample_le_of_forall_lower
              1 0 (fun i => (hsample i).1)) rank
    exact propext
      ⟨fun hmem =>
        (not_lt_of_ge (le_trans hupper (le_of_lt hx)) hmem).elim,
        fun hmem => False.elim hmem⟩
  calc
    (MeasureTheory.Measure.pi
        (fun _ : Fin q => boundedReflectedPowerSourceMeasure beta)).real
        {sample : Fin q → ℝ |
          x < AppliedModelingLib.Probability.ascendingOrderStatistic
            (AppliedModelingLib.Probability.reflectedSample 1 sample) rank}
        =
        μ.real (∅ : Set (Fin q → ℝ)) := by
          simpa [μ] using MeasureTheory.measureReal_congr (μ := μ) hset
    _ = 0 := by simp

theorem
    boundedReflectedPowerProductMeasure_reflectedAscendingOrderStatistic_tail_integrableOn_Ioo_zero_one
    {beta : ℝ} (hbeta_pos : 0 < beta)
    {q : ℕ} (rank : Fin q) :
    MeasureTheory.IntegrableOn
      (fun x : ℝ =>
        (MeasureTheory.Measure.pi
          (fun _ : Fin q => boundedReflectedPowerSourceMeasure beta)).real
          {sample : Fin q → ℝ |
            x < AppliedModelingLib.Probability.ascendingOrderStatistic
              (AppliedModelingLib.Probability.reflectedSample 1 sample) rank})
      (Set.Ioo (0 : ℝ) 1) := by
  classical
  let tail : ℝ → ℝ := fun x =>
    (MeasureTheory.Measure.pi
      (fun _ : Fin q => boundedReflectedPowerSourceMeasure beta)).real
      {sample : Fin q → ℝ |
        x < AppliedModelingLib.Probability.ascendingOrderStatistic
          (AppliedModelingLib.Probability.reflectedSample 1 sample) rank}
  let kernel : ℝ → ℝ := fun x =>
    ∑ j ∈ Finset.Icc 0 rank.val,
      (Nat.choose q j : ℝ) *
        (x ^ beta) ^ j * (1 - x ^ beta) ^ (q - j)
  have hkernel : MeasureTheory.IntegrableOn kernel (Set.Ioo (0 : ℝ) 1) := by
    dsimp [kernel]
    exact MeasureTheory.integrable_finset_sum
      (Finset.Icc 0 rank.val)
      (fun j _hj => by
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          (AppliedModelingLib.Math.integrableOn_Ioo_zero_one_rpow_power_kernel
            hbeta_pos j (q - j)).const_mul (Nat.choose q j : ℝ))
  refine hkernel.congr_fun ?_ measurableSet_Ioo
  intro x hx
  dsimp [tail, kernel]
  exact
    (boundedReflectedPowerProductMeasure_reflectedAscendingOrderStatistic_gt_real
      hbeta_pos hx.1 hx.2 rank).symm

theorem
    boundedReflectedPowerProductMeasure_reflectedAscendingOrderStatistic_tail_integrableOn_Ioi_one
    {beta : ℝ} (hbeta_pos : 0 < beta)
    {q : ℕ} (rank : Fin q) :
    MeasureTheory.IntegrableOn
      (fun x : ℝ =>
        (MeasureTheory.Measure.pi
          (fun _ : Fin q => boundedReflectedPowerSourceMeasure beta)).real
          {sample : Fin q → ℝ |
            x < AppliedModelingLib.Probability.ascendingOrderStatistic
              (AppliedModelingLib.Probability.reflectedSample 1 sample) rank})
      (Set.Ioi (1 : ℝ)) := by
  have hzero :
      MeasureTheory.IntegrableOn (fun _x : ℝ => (0 : ℝ)) (Set.Ioi (1 : ℝ)) :=
    by simp
  refine hzero.congr_fun ?_ measurableSet_Ioi
  intro x hx
  exact
    (boundedReflectedPowerProductMeasure_reflectedAscendingOrderStatistic_gt_real_of_one_lt
      hbeta_pos hx rank).symm

theorem
    boundedReflectedPowerProductMeasure_reflectedAscendingOrderStatistic_tail_integral_Ioo_zero_one
    {beta : ℝ} (hbeta_pos : 0 < beta)
    {q : ℕ} (rank : Fin q) :
    ∫ x in Set.Ioo (0 : ℝ) 1,
        (MeasureTheory.Measure.pi
          (fun _ : Fin q => boundedReflectedPowerSourceMeasure beta)).real
          {sample : Fin q → ℝ |
            x < AppliedModelingLib.Probability.ascendingOrderStatistic
              (AppliedModelingLib.Probability.reflectedSample 1 sample) rank}
      =
      ∑ j ∈ Finset.Icc 0 rank.val,
        (Nat.choose q j : ℝ) *
          ((1 / beta) *
            ProbabilityTheory.beta
              ((j : ℝ) + 1 / beta)
              (((q - j : ℕ) : ℝ) + 1)) := by
  classical
  let lowerTail : Finset ℕ := Finset.Icc 0 rank.val
  have hinv_pos : 0 < 1 / beta := one_div_pos.mpr hbeta_pos
  have hinv_mul : (1 / beta) * beta = 1 := by
    field_simp [hbeta_pos.ne']
  calc
    ∫ x in Set.Ioo (0 : ℝ) 1,
        (MeasureTheory.Measure.pi
          (fun _ : Fin q => boundedReflectedPowerSourceMeasure beta)).real
          {sample : Fin q → ℝ |
            x < AppliedModelingLib.Probability.ascendingOrderStatistic
              (AppliedModelingLib.Probability.reflectedSample 1 sample) rank}
        =
        ∫ x in Set.Ioo (0 : ℝ) 1,
          ∑ j ∈ lowerTail,
            (Nat.choose q j : ℝ) *
              (x ^ beta) ^ j * (1 - x ^ beta) ^ (q - j) := by
          refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo ?_
          intro x hx
          dsimp [lowerTail]
          exact
            boundedReflectedPowerProductMeasure_reflectedAscendingOrderStatistic_gt_real
              hbeta_pos hx.1 hx.2 rank
    _ =
        ∑ j ∈ lowerTail,
          ∫ x in Set.Ioo (0 : ℝ) 1,
            (Nat.choose q j : ℝ) *
              (x ^ beta) ^ j * (1 - x ^ beta) ^ (q - j) := by
          exact MeasureTheory.integral_finset_sum lowerTail
            (fun j _hj => by
              simpa [mul_assoc, mul_left_comm, mul_comm] using
                (AppliedModelingLib.Math.integrableOn_Ioo_zero_one_rpow_power_kernel
                  hbeta_pos j (q - j)).const_mul (Nat.choose q j : ℝ))
    _ =
        ∑ j ∈ lowerTail,
          (Nat.choose q j : ℝ) *
            ((1 / beta) *
              ProbabilityTheory.beta
                ((j : ℝ) + 1 / beta)
                (((q - j : ℕ) : ℝ) + 1)) := by
          refine Finset.sum_congr rfl ?_
          intro j _hj
          calc
            ∫ x in Set.Ioo (0 : ℝ) 1,
                (Nat.choose q j : ℝ) *
                  (x ^ beta) ^ j * (1 - x ^ beta) ^ (q - j)
                =
                ∫ x in Set.Ioo (0 : ℝ) 1,
                  (Nat.choose q j : ℝ) *
                    ((x ^ beta) ^ j * (1 - x ^ beta) ^ (q - j)) := by
                  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo ?_
                  intro x hx
                  ring
            _ =
                (Nat.choose q j : ℝ) *
                  ∫ x in Set.Ioo (0 : ℝ) 1,
                    (x ^ beta) ^ j * (1 - x ^ beta) ^ (q - j) := by
                  rw [MeasureTheory.integral_const_mul]
            _ =
                (Nat.choose q j : ℝ) *
                  ((1 / beta) *
                    ProbabilityTheory.beta
                      ((j : ℝ) + 1 / beta)
                      (((q - j : ℕ) : ℝ) + 1)) := by
                  rw [AppliedModelingLib.Math.integral_Ioo_zero_one_rpow_power_kernel_eq_s_mul_beta
                    (s := 1 / beta) (beta := beta) hinv_pos hbeta_pos hinv_mul
                    j (q - j)]

theorem uniform01ProductMeasure_all_bounds_ae (q : ℕ) :
    ∀ᵐ sample ∂MeasureTheory.Measure.pi (fun _ : Fin q => uniform01Measure),
      ∀ i : Fin q, 0 ≤ sample i ∧ sample i ≤ 1 := by
  simpa using
    AppliedModelingLib.Probability.iidProductMeasure_forall_bounds_ae
      (n := q) uniform01Measure uniform01Measure_ae_bounds

theorem uniform01ProductMeasure_upperOrderStatistic_nonnegative_ae
    {q : ℕ} (rankFromTop : Fin q) :
    (fun _sample : Fin q → ℝ => (0 : ℝ)) ≤ᵐ[
      MeasureTheory.Measure.pi (fun _ : Fin q => uniform01Measure)]
      fun sample =>
        AppliedModelingLib.Probability.upperOrderStatistic sample rankFromTop := by
  filter_upwards [uniform01ProductMeasure_all_bounds_ae q] with sample hsample
  exact
    AppliedModelingLib.Probability.le_upperOrderStatistic_of_forall_le
      (fun i => (hsample i).1) rankFromTop

theorem uniform01ProductMeasure_upperOrderStatistic_integrable
    {q : ℕ} (rankFromTop : Fin q) :
    MeasureTheory.Integrable
      (fun sample : Fin q → ℝ =>
        AppliedModelingLib.Probability.upperOrderStatistic sample rankFromTop)
      (MeasureTheory.Measure.pi (fun _ : Fin q => uniform01Measure)) :=
  AppliedModelingLib.Probability.upperOrderStatistic_integrable_of_ae_bounds
    0 1 (MeasureTheory.Measure.pi (fun _ : Fin q => uniform01Measure))
    rankFromTop (uniform01ProductMeasure_all_bounds_ae q)

theorem uniform01ProductMeasure_upperOrderStatistic_gt_real
    {x : ℝ} (hx_pos : 0 < x) (hx_lt_one : x < 1)
    {q : ℕ} (rankFromTop : Fin q) :
    (MeasureTheory.Measure.pi (fun _ : Fin q => uniform01Measure)).real
        {sample : Fin q → ℝ |
          x < AppliedModelingLib.Probability.upperOrderStatistic sample rankFromTop} =
      ∑ j ∈ Finset.Icc (rankFromTop.val + 1) q,
        (Nat.choose q j : ℝ) *
          (1 - x) ^ j * x ^ (q - j) := by
  classical
  let μ : MeasureTheory.Measure (Fin q → ℝ) :=
    MeasureTheory.Measure.pi (fun _ : Fin q => uniform01Measure)
  haveI : MeasureTheory.IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  have hset :
      {sample : Fin q → ℝ |
          x < AppliedModelingLib.Probability.upperOrderStatistic sample rankFromTop} =
        {sample : Fin q → ℝ |
          AppliedModelingLib.Probability.iidSuccessCount (Set.Ioi x) sample ≤
            rankFromTop.val}ᶜ := by
    ext sample
    simp [AppliedModelingLib.Probability.upperOrderStatistic_lt_iff_rank_lt_iidSuccessCount_Ioi]
  have htail : uniform01Measure.real (Set.Ioi x) = 1 - x :=
    uniform01Measure_real_Ioi_eq hx_pos.le hx_lt_one.le
  have hcomp : 1 - (1 - x) = x := by ring
  have hmin : min rankFromTop.val q = rankFromTop.val :=
    min_eq_left (Nat.le_of_lt rankFromTop.isLt)
  rw [hset,
    MeasureTheory.measureReal_compl
      (AppliedModelingLib.Probability.iidSuccessCount_le_measurableSet
        (n := q) measurableSet_Ioi rankFromTop.val),
    MeasureTheory.probReal_univ,
    AppliedModelingLib.Probability.iidProductMeasure_successCount_le_real
      uniform01Measure measurableSet_Ioi rankFromTop.val]
  rw [hmin, htail, hcomp]
  simpa [μ, mul_assoc] using
    AppliedModelingLib.FiniteSum.binomial_lower_tail_complement_eq_upper_tail
      rankFromTop.isLt (1 - x)

theorem uniform01ProductMeasure_upperOrderStatistic_gt_real_of_one_lt
    {x : ℝ} (hx : 1 < x) {q : ℕ} (rankFromTop : Fin q) :
    (MeasureTheory.Measure.pi (fun _ : Fin q => uniform01Measure)).real
        {sample : Fin q → ℝ |
          x < AppliedModelingLib.Probability.upperOrderStatistic sample rankFromTop} =
      0 := by
  let μ : MeasureTheory.Measure (Fin q → ℝ) :=
    MeasureTheory.Measure.pi (fun _ : Fin q => uniform01Measure)
  have hset :
      {sample : Fin q → ℝ |
          x < AppliedModelingLib.Probability.upperOrderStatistic sample rankFromTop}
        =ᵐ[μ] (∅ : Set (Fin q → ℝ)) := by
    filter_upwards [uniform01ProductMeasure_all_bounds_ae q] with sample hsample
    have hupper :
        AppliedModelingLib.Probability.upperOrderStatistic sample rankFromTop ≤ 1 :=
      AppliedModelingLib.Probability.upperOrderStatistic_le_of_forall_le
        (fun i => (hsample i).2) rankFromTop
    exact propext
      ⟨fun hmem =>
        (not_lt_of_ge (le_trans hupper (le_of_lt hx)) hmem).elim,
        fun hmem => False.elim hmem⟩
  calc
    (MeasureTheory.Measure.pi (fun _ : Fin q => uniform01Measure)).real
        {sample : Fin q → ℝ |
          x < AppliedModelingLib.Probability.upperOrderStatistic sample rankFromTop}
        =
        μ.real (∅ : Set (Fin q → ℝ)) := by
          simpa [μ] using MeasureTheory.measureReal_congr (μ := μ) hset
    _ = 0 := by simp

theorem uniform01ProductMeasure_upperOrderStatistic_tail_integrableOn_Ioo_zero_one
    {q : ℕ} (rankFromTop : Fin q) :
    MeasureTheory.IntegrableOn
      (fun x : ℝ =>
        (MeasureTheory.Measure.pi (fun _ : Fin q => uniform01Measure)).real
          {sample : Fin q → ℝ |
            x < AppliedModelingLib.Probability.upperOrderStatistic sample rankFromTop})
      (Set.Ioo (0 : ℝ) 1) := by
  classical
  let tail : ℝ → ℝ := fun x =>
    (MeasureTheory.Measure.pi (fun _ : Fin q => uniform01Measure)).real
      {sample : Fin q → ℝ |
        x < AppliedModelingLib.Probability.upperOrderStatistic sample rankFromTop}
  let kernel : ℝ → ℝ := fun x =>
    ∑ j ∈ Finset.Icc (rankFromTop.val + 1) q,
      (Nat.choose q j : ℝ) * (1 - x) ^ j * x ^ (q - j)
  have hkernel : MeasureTheory.IntegrableOn kernel (Set.Ioo (0 : ℝ) 1) := by
    dsimp [kernel]
    exact MeasureTheory.integrable_finset_sum
      (Finset.Icc (rankFromTop.val + 1) q)
      (fun j _hj => by
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          (AppliedModelingLib.Math.integrableOn_Ioo_zero_one_pow_mul_one_sub_pow
            (q - j) j).const_mul (Nat.choose q j : ℝ))
  refine hkernel.congr_fun ?_ measurableSet_Ioo
  intro x hx
  dsimp [tail, kernel]
  exact (uniform01ProductMeasure_upperOrderStatistic_gt_real hx.1 hx.2 rankFromTop).symm

theorem uniform01ProductMeasure_upperOrderStatistic_tail_integrableOn_Ioi_one
    {q : ℕ} (rankFromTop : Fin q) :
    MeasureTheory.IntegrableOn
      (fun x : ℝ =>
        (MeasureTheory.Measure.pi (fun _ : Fin q => uniform01Measure)).real
          {sample : Fin q → ℝ |
            x < AppliedModelingLib.Probability.upperOrderStatistic sample rankFromTop})
      (Set.Ioi (1 : ℝ)) := by
  have hzero :
      MeasureTheory.IntegrableOn (fun _x : ℝ => (0 : ℝ)) (Set.Ioi (1 : ℝ)) :=
    by simp
  refine hzero.congr_fun ?_ measurableSet_Ioi
  intro x hx
  exact (uniform01ProductMeasure_upperOrderStatistic_gt_real_of_one_lt hx rankFromTop).symm

theorem uniform01ProductMeasure_upperOrderStatistic_tail_integral_Ioo_zero_one
    {q : ℕ} (rankFromTop : Fin q) :
    ∫ x in Set.Ioo (0 : ℝ) 1,
        (MeasureTheory.Measure.pi (fun _ : Fin q => uniform01Measure)).real
          {sample : Fin q → ℝ |
            x < AppliedModelingLib.Probability.upperOrderStatistic sample rankFromTop}
      =
      (q - rankFromTop.val : ℝ) / ((q : ℝ) + 1) := by
  classical
  let upperTail : Finset ℕ := Finset.Icc (rankFromTop.val + 1) q
  calc
    ∫ x in Set.Ioo (0 : ℝ) 1,
        (MeasureTheory.Measure.pi (fun _ : Fin q => uniform01Measure)).real
          {sample : Fin q → ℝ |
            x < AppliedModelingLib.Probability.upperOrderStatistic sample rankFromTop}
        =
        ∫ x in Set.Ioo (0 : ℝ) 1,
          ∑ j ∈ upperTail,
            (Nat.choose q j : ℝ) * (1 - x) ^ j * x ^ (q - j) := by
          refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo ?_
          intro x hx
          dsimp [upperTail]
          exact uniform01ProductMeasure_upperOrderStatistic_gt_real
            hx.1 hx.2 rankFromTop
    _ =
        ∑ j ∈ upperTail,
          (Nat.choose q j : ℝ) *
            ProbabilityTheory.beta
              (((q - j : ℕ) : ℝ) + 1)
              (((j : ℕ) : ℝ) + 1) := by
          calc
            ∫ x in Set.Ioo (0 : ℝ) 1,
              ∑ j ∈ upperTail,
                (Nat.choose q j : ℝ) * (1 - x) ^ j * x ^ (q - j)
              =
              ∑ j ∈ upperTail,
                ∫ x in Set.Ioo (0 : ℝ) 1,
                  (Nat.choose q j : ℝ) * (1 - x) ^ j * x ^ (q - j) := by
                exact MeasureTheory.integral_finset_sum upperTail
                  (fun j _hj => by
                    simpa [mul_assoc, mul_left_comm, mul_comm] using
                      (AppliedModelingLib.Math.integrableOn_Ioo_zero_one_pow_mul_one_sub_pow
                        (q - j) j).const_mul (Nat.choose q j : ℝ))
            _ =
              ∑ j ∈ upperTail,
                (Nat.choose q j : ℝ) *
                  ProbabilityTheory.beta
                    (((q - j : ℕ) : ℝ) + 1)
                    (((j : ℕ) : ℝ) + 1) := by
                refine Finset.sum_congr rfl ?_
                intro j _hj
                calc
                  ∫ x in Set.Ioo (0 : ℝ) 1,
                      (Nat.choose q j : ℝ) * (1 - x) ^ j * x ^ (q - j)
                      =
                      ∫ x in Set.Ioo (0 : ℝ) 1,
                        (Nat.choose q j : ℝ) *
                          (x ^ (q - j) * (1 - x) ^ j) := by
                        refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo ?_
                        intro x hx
                        ring
                  _ =
                      (Nat.choose q j : ℝ) *
                        ∫ x in Set.Ioo (0 : ℝ) 1,
                          x ^ (q - j) * (1 - x) ^ j := by
                        rw [MeasureTheory.integral_const_mul]
                  _ =
                      (Nat.choose q j : ℝ) *
                        ProbabilityTheory.beta
                          (((q - j : ℕ) : ℝ) + 1)
                          (((j : ℕ) : ℝ) + 1) := by
                        rw [AppliedModelingLib.Math.integral_Ioo_zero_one_pow_mul_one_sub_pow_eq_beta_nat]
    _ =
        ∑ _j ∈ upperTail, (1 / (((q : ℕ) : ℝ) + 1) : ℝ) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          have hjq : j ≤ q := (Finset.mem_Icc.mp hj).2
          exact AppliedModelingLib.Math.nat_choose_mul_beta_nat_sub_add_one_eq_inv_succ hjq
    _ = (q - rankFromTop.val : ℝ) / ((q : ℝ) + 1) := by
          have hcard : upperTail.card = q - rankFromTop.val := by
            dsimp [upperTail]
            rw [Nat.card_Icc]
            omega
          rw [Finset.sum_const, hcard]
          simp [nsmul_eq_mul]
          ring

theorem uniform01ProductMeasure_expectedUpperOrderStatistic_eq
    {q : ℕ} (rankFromTop : Fin q) :
    AppliedModelingLib.Probability.expectedUpperOrderStatistic
        (MeasureTheory.Measure.pi (fun _ : Fin q => uniform01Measure))
        rankFromTop =
      (q - rankFromTop.val : ℝ) / ((q : ℝ) + 1) := by
  let tail : ℝ → ℝ := fun x =>
    (MeasureTheory.Measure.pi (fun _ : Fin q => uniform01Measure)).real
      {sample : Fin q → ℝ |
        x < AppliedModelingLib.Probability.upperOrderStatistic sample rankFromTop}
  have h_nonneg :=
    uniform01ProductMeasure_upperOrderStatistic_nonnegative_ae rankFromTop
  have h_int :=
    uniform01ProductMeasure_upperOrderStatistic_integrable rankFromTop
  rw [AppliedModelingLib.Probability.expectedUpperOrderStatistic_eq_integral_tail_probability_of_nonneg
    (μ := MeasureTheory.Measure.pi (fun _ : Fin q => uniform01Measure))
    rankFromTop h_nonneg h_int]
  have hbelow_Ioo : MeasureTheory.IntegrableOn tail (Set.Ioo (0 : ℝ) 1) :=
    uniform01ProductMeasure_upperOrderStatistic_tail_integrableOn_Ioo_zero_one
      rankFromTop
  have hbelow_Ioc : MeasureTheory.IntegrableOn tail (Set.Ioc (0 : ℝ) 1) :=
    (integrableOn_Ioc_iff_integrableOn_Ioo
      (μ := MeasureTheory.volume) (f := tail) (a := 0) (b := 1)).2
      hbelow_Ioo
  have habove_Ioi : MeasureTheory.IntegrableOn tail (Set.Ioi (1 : ℝ)) :=
    uniform01ProductMeasure_upperOrderStatistic_tail_integrableOn_Ioi_one
      rankFromTop
  have hsplit :
      ∫ x in (Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ)), tail x =
        (∫ x in Set.Ioc (0 : ℝ) 1, tail x) +
          ∫ x in Set.Ioi (1 : ℝ), tail x := by
    exact MeasureTheory.setIntegral_union
      Set.Ioc_disjoint_Ioi_same measurableSet_Ioi hbelow_Ioc habove_Ioi
  rw [Set.Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1)] at hsplit
  rw [hsplit]
  have hbelow_eq :
      ∫ x in Set.Ioc (0 : ℝ) 1, tail x =
        (q - rankFromTop.val : ℝ) / ((q : ℝ) + 1) := by
    rw [MeasureTheory.integral_Ioc_eq_integral_Ioo]
    dsimp [tail]
    exact uniform01ProductMeasure_upperOrderStatistic_tail_integral_Ioo_zero_one
      rankFromTop
  have habove_eq :
      ∫ x in Set.Ioi (1 : ℝ), tail x = 0 := by
    calc
      ∫ x in Set.Ioi (1 : ℝ), tail x =
          ∫ _x in Set.Ioi (1 : ℝ), (0 : ℝ) := by
            refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
            intro x hx
            dsimp [tail]
            exact uniform01ProductMeasure_upperOrderStatistic_gt_real_of_one_lt
              hx rankFromTop
      _ = 0 := by simp
  rw [hbelow_eq, habove_eq, add_zero]

noncomputable def uniformTopOneValue (q : ℕ) : ℝ := 1 - 1 / (q + 1 : ℝ)

@[simp] theorem uniformTopOneValue_zero :
    uniformTopOneValue 0 = 0 := by
  norm_num [uniformTopOneValue]

theorem uniformTopOneValue_succ_sub (q : ℕ) :
    uniformTopOneValue (q + 1) - uniformTopOneValue q =
      1 / ((q + 1 : ℝ) * (q + 2 : ℝ)) := by
  unfold uniformTopOneValue
  have h_cast : ((q + 1 : ℕ) : ℝ) = (q : ℝ) + 1 := by push_cast; rfl
  rw [h_cast]
  have h1 : (q : ℝ) + 1 + 1 = (q : ℝ) + 2 := by ring
  rw [h1]
  have hd1 : (q : ℝ) + 1 ≠ 0 := by positivity
  have hd2 : (q : ℝ) + 2 ≠ 0 := by positivity
  have h_diff : 1 - 1 / ((q : ℝ) + 2) - (1 - 1 / ((q : ℝ) + 1)) = 1 / ((q : ℝ) + 1) - 1 / ((q : ℝ) + 2) := by ring
  rw [h_diff]
  have h_frac : 1 / ((q : ℝ) + 1) - 1 / ((q : ℝ) + 2) = (1 * ((q : ℝ) + 2) - ((q : ℝ) + 1) * 1) / (((q : ℝ) + 1) * ((q : ℝ) + 2)) :=
  by
    exact div_sub_div 1 1 hd1 hd2
  rw [h_frac]
  have h_num : 1 * ((q : ℝ) + 2) - ((q : ℝ) + 1) * 1 = 1 := by ring
  rw [h_num]

theorem uniformTopOneValue_sub_pred {q : ℕ} (hq : 0 < q) :
    uniformTopOneValue q - uniformTopOneValue (q - 1) =
      1 / ((q : ℝ) * (q + 1 : ℝ)) := by
  unfold uniformTopOneValue
  have h_cast1 : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
    rw [Nat.cast_sub hq]
    push_cast
    rfl
  rw [h_cast1]
  have h1 : (q : ℝ) - 1 + 1 = (q : ℝ) := by ring
  rw [h1]
  have hd1 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hd2 : (q : ℝ) + 1 ≠ 0 := by positivity
  have h_diff : 1 - 1 / ((q : ℝ) + 1) - (1 - 1 / (q : ℝ)) = 1 / (q : ℝ) - 1 / ((q : ℝ) + 1) := by ring
  rw [h_diff]
  have h_frac : 1 / (q : ℝ) - 1 / ((q : ℝ) + 1) = (1 * ((q : ℝ) + 1) - (q : ℝ) * 1) / ((q : ℝ) * ((q : ℝ) + 1)) :=
    div_sub_div 1 1 hd1 hd2
  rw [h_frac]
  have h_num : 1 * ((q : ℝ) + 1) - (q : ℝ) * 1 = 1 := by ring
  rw [h_num]

noncomputable def uniformTopKFactor (k : ℕ) : ℝ := (k : ℝ) * (k + 1 : ℝ) / 2

noncomputable def uniformTopKValue (k q : ℕ) : ℝ :=
  if q ≤ k then (q : ℝ) / 2
  else (k : ℝ) - uniformTopKFactor k / (q + 1 : ℝ)

noncomputable def uniformOrderStatisticMean (i q : ℕ) : ℝ := 1 - (i : ℝ) / (q + 1 : ℝ)

/--
Uniform `[0,1]` order-statistic mean in the paper's Definition 3 convention:
`i` is the `i`-th smallest draw among `q` samples.
-/
noncomputable def uniformAscendingOrderStatisticMean (i q : ℕ) : ℝ := (i : ℝ) / (q + 1 : ℝ)

/--
Concrete Definition 3 mean table induced by iid uniform `[0,1]` samples.
-/
noncomputable def uniform01IidOrderStatisticMeanSeq (rank sampleSize : ℕ) : ℝ :=
  expectedOrderStatisticMeanSeq
    (fun a => MeasureTheory.Measure.pi (fun _ : Fin a => uniform01Measure))
    rank sampleSize

theorem uniform01_expectedOrderStatisticMeanSeq_eq_uniformAscendingOrderStatisticMean
    {q r : ℕ} (hrq : r < q) :
    uniform01IidOrderStatisticMeanSeq (q - r) q =
      uniformAscendingOrderStatisticMean (q - r) q := by
  calc
    uniform01IidOrderStatisticMeanSeq (q - r) q
        =
        AppliedModelingLib.Probability.expectedUpperOrderStatistic
          (MeasureTheory.Measure.pi (fun _ : Fin q => uniform01Measure))
          ⟨r, hrq⟩ := by
          simpa [uniform01IidOrderStatisticMeanSeq, expectedOrderStatisticMeanSeq] using
            AppliedModelingLib.Probability.expectedSampleOrderStatisticMean_eq_expectedUpperOrderStatistic_of_rank_from_top
              (μ := MeasureTheory.Measure.pi (fun _ : Fin q => uniform01Measure))
              (a := q) (r := r) hrq
    _ = (q - r : ℝ) / ((q : ℝ) + 1) :=
        uniform01ProductMeasure_expectedUpperOrderStatistic_eq ⟨r, hrq⟩
    _ = uniformAscendingOrderStatisticMean (q - r) q := by
        unfold uniformAscendingOrderStatisticMean
        rw [Nat.cast_sub (le_of_lt hrq)]

noncomputable def uniformTopKOrderStatisticSum (k q : ℕ) : ℝ := ∑ i ∈ Finset.range (min k q), uniformOrderStatisticMean (i + 1) q

theorem uniformTopKFactor_pos {k : ℕ} (hk : 0 < k) :
    0 < uniformTopKFactor k := by
  unfold uniformTopKFactor
  positivity

theorem uniformTopKFactor_nonneg (k : ℕ) :
    0 ≤ uniformTopKFactor k := by
  unfold uniformTopKFactor
  positivity

@[simp] theorem uniformTopKValue_zero (k : ℕ) :
    uniformTopKValue k 0 = 0 := by
  simp [uniformTopKValue]

theorem sum_range_cast_succ (n : ℕ) :
    (∑ i ∈ Finset.range n, ((i + 1 : ℕ) : ℝ)) =
      (n : ℝ) * ((n : ℝ) + 1) / 2 := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      norm_num
      ring

theorem uniformTopKOrderStatisticSum_eq_value (k q : ℕ) :
    uniformTopKOrderStatisticSum k q = uniformTopKValue k q := by
  by_cases hqk : q ≤ k
  · have hmin : min k q = q := min_eq_right hqk
    unfold uniformTopKOrderStatisticSum uniformOrderStatisticMean uniformTopKValue
    simp [hqk]
    have hsum :
        (∑ i ∈ Finset.range q, ((i : ℝ) + 1)) =
          (q : ℝ) * ((q : ℝ) + 1) / 2 := by
      simpa only [Nat.cast_add, Nat.cast_one] using sum_range_cast_succ q
    rw [← Finset.sum_div, hsum]
    have hden : (q : ℝ) + 1 ≠ 0 := by positivity
    field_simp [hden]
    ring
  · have hkq : k < q := not_le.mp hqk
    have hmin : min k q = k := min_eq_left (le_of_lt hkq)
    unfold uniformTopKOrderStatisticSum uniformOrderStatisticMean uniformTopKValue
    simp [hqk, hmin]
    have hsum :
        (∑ i ∈ Finset.range k, ((i : ℝ) + 1)) =
          (k : ℝ) * ((k : ℝ) + 1) / 2 := by
      simpa only [Nat.cast_add, Nat.cast_one] using sum_range_cast_succ k
    rw [← Finset.sum_div, hsum]
    unfold uniformTopKFactor
    have hden : (q : ℝ) + 1 ≠ 0 := by positivity
    field_simp [hden]

/--
Proposition 5 specialized to the uniform `[0,1]` order-statistic means in the
paper's bottom-indexed convention.
-/
theorem uniform_orderStatisticTopKSumFromMean_eq_topKOrderStatisticSum
    (k q : ℕ) :
    orderStatisticTopKSumFromMean uniformAscendingOrderStatisticMean k q =
      uniformTopKOrderStatisticSum k q := by
  unfold orderStatisticTopKSumFromMean uniformAscendingOrderStatisticMean
    uniformTopKOrderStatisticSum uniformOrderStatisticMean
  apply Finset.sum_congr rfl
  intro i hi
  have hi_lt : i < min k q := Finset.mem_range.mp hi
  have hi_le_q : i ≤ q :=
    le_trans (Nat.le_of_lt hi_lt) (min_le_right k q)
  have hden : (q : ℝ) + 1 ≠ 0 := by positivity
  change ((q - i : ℕ) : ℝ) / ((q : ℝ) + 1) =
    1 - ((i + 1 : ℕ) : ℝ) / ((q : ℝ) + 1)
  rw [Nat.cast_sub hi_le_q]
  field_simp [hden]
  norm_num only [Nat.cast_add, Nat.cast_one]
  ring

theorem uniform_orderStatisticTopKSumFromMean_eq_value (k q : ℕ) :
    orderStatisticTopKSumFromMean uniformAscendingOrderStatisticMean k q =
      uniformTopKValue k q := by
  rw [uniform_orderStatisticTopKSumFromMean_eq_topKOrderStatisticSum,
    uniformTopKOrderStatisticSum_eq_value]

theorem uniform01_expectedOrderStatisticTopKSum_eq_uniformOrderStatisticTopKSum
    (k q : ℕ) :
    orderStatisticTopKSumFromMean uniform01IidOrderStatisticMeanSeq k q =
      orderStatisticTopKSumFromMean uniformAscendingOrderStatisticMean k q := by
  rw [orderStatisticTopKSumFromMean_eq_bottomIndexed_sum,
    orderStatisticTopKSumFromMean_eq_bottomIndexed_sum]
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hiq : i < q :=
    lt_of_lt_of_le (Finset.mem_range.mp hi) (min_le_right k q)
  exact uniform01_expectedOrderStatisticMeanSeq_eq_uniformAscendingOrderStatisticMean hiq

theorem uniform01_expectedOrderStatisticTopKSum_eq_uniformTopKValue
    (k q : ℕ) :
    orderStatisticTopKSumFromMean uniform01IidOrderStatisticMeanSeq k q =
      uniformTopKValue k q := by
  rw [uniform01_expectedOrderStatisticTopKSum_eq_uniformOrderStatisticTopKSum,
    uniform_orderStatisticTopKSumFromMean_eq_value]

theorem uniformTopKValue_succ_sub_of_le {k q : ℕ} (hkq : k ≤ q) :
    uniformTopKValue k (q + 1) - uniformTopKValue k q =
      uniformTopKFactor k / ((q + 1 : ℝ) * (q + 2 : ℝ)) := by
  by_cases hqk : q = k
  · subst q
    unfold uniformTopKValue uniformTopKFactor
    have hnot : ¬ k + 1 ≤ k := by omega
    simp [hnot]
    field_simp
    ring
  · have hklt : k < q := lt_of_le_of_ne hkq (Ne.symm hqk)
    have hnot_q : ¬ q ≤ k := not_le_of_gt hklt
    have hnot_succ : ¬ q + 1 ≤ k := by omega
    unfold uniformTopKValue
    simp [hnot_q, hnot_succ]
    have hd1 : (q : ℝ) + 1 ≠ 0 := by positivity
    have hd2 : (q : ℝ) + 2 ≠ 0 := by positivity
    unfold uniformTopKFactor
    field_simp [hd1, hd2]
    ring

theorem uniformTopKValue_succ_sub_of_lt {k q : ℕ} (hq : q < k) :
    uniformTopKValue k (q + 1) - uniformTopKValue k q = 1 / 2 := by
  have hqle : q ≤ k := le_of_lt hq
  have hsuccle : q + 1 ≤ k := Nat.succ_le_of_lt hq
  unfold uniformTopKValue
  simp [hqle, hsuccle]
  ring

theorem uniformTopKValue_sub_pred_of_le {k q : ℕ}
    (hkq : k ≤ q) (hq : 0 < q) :
    uniformTopKValue k q - uniformTopKValue k (q - 1) =
      uniformTopKFactor k / ((q : ℝ) * (q + 1 : ℝ)) := by
  by_cases hqk : q = k
  · subst q
    have hk : 0 < k := hq
    unfold uniformTopKValue uniformTopKFactor
    have hsub : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub (Nat.succ_le_of_lt hk)]
      norm_num
    simp [hsub]
    have hk_ne : (k : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hk
    have hk_succ_ne : (k : ℝ) + 1 ≠ 0 := by positivity
    field_simp [hk_ne, hk_succ_ne]
    ring_nf
  · have hpred : k ≤ q - 1 := by omega
    have hsucc := uniformTopKValue_succ_sub_of_le (k := k) (q := q - 1) hpred
    have hcancel : q - 1 + 1 = q := Nat.sub_add_cancel (Nat.succ_le_of_lt hq)
    have hden1 : ((q - 1 : ℕ) : ℝ) + 1 = (q : ℝ) := by
      rw [Nat.cast_sub (Nat.succ_le_of_lt hq)]
      norm_num
    have hden2 : ((q - 1 : ℕ) : ℝ) + 2 = (q : ℝ) + 1 := by
      linarith
    simpa [hcancel, hden1, hden2] using hsucc

theorem uniformTopKValue_marginal_antitone_step (k q : ℕ) :
    uniformTopKValue k (q + 2) - uniformTopKValue k (q + 1) ≤
      uniformTopKValue k (q + 1) - uniformTopKValue k q := by
  by_cases hlt : q + 1 < k
  · have hq : q < k := by omega
    rw [uniformTopKValue_succ_sub_of_lt hlt,
      uniformTopKValue_succ_sub_of_lt hq]
  · have hge : k ≤ q + 1 := le_of_not_gt hlt
    by_cases heq : q + 1 = k
    · rw [uniformTopKValue_succ_sub_of_le hge,
        uniformTopKValue_succ_sub_of_lt (by omega : q < k)]
      norm_num only [Nat.cast_add, Nat.cast_one]
      subst k
      unfold uniformTopKFactor
      norm_num only [Nat.cast_add, Nat.cast_one]
      have hdenpos :
          0 < (((q : ℝ) + 1 + 1) * ((q : ℝ) + 1 + 2)) := by
        positivity
      rw [div_le_iff₀ hdenpos]
      ring_nf
      norm_num only [Nat.cast_add, Nat.cast_one] at *
      nlinarith [show (0 : ℝ) ≤ q by positivity]
    · have hkq : k ≤ q := by omega
      rw [uniformTopKValue_succ_sub_of_le (k := k) (q := q + 1) hge,
        uniformTopKValue_succ_sub_of_le (k := k) (q := q) hkq]
      have hfactor_nonneg := uniformTopKFactor_nonneg k
      have hden :
          ((q + 1 : ℝ) * (q + 2 : ℝ)) ≤
            ((((q + 1 : ℕ) : ℝ) + 1) * (((q + 1 : ℕ) : ℝ) + 2)) := by
        norm_num only [Nat.cast_add, Nat.cast_one]
        nlinarith [show (0 : ℝ) ≤ q + 2 by positivity]
      have hrec :
          1 / ((((q + 1 : ℕ) : ℝ) + 1) * (((q + 1 : ℕ) : ℝ) + 2)) ≤
            1 / ((q + 1 : ℝ) * (q + 2 : ℝ)) := by
        gcongr
      calc
        uniformTopKFactor k /
            ((((q + 1 : ℕ) : ℝ) + 1) * (((q + 1 : ℕ) : ℝ) + 2))
            = uniformTopKFactor k *
                (1 / ((((q + 1 : ℕ) : ℝ) + 1) *
                  (((q + 1 : ℕ) : ℝ) + 2))) := by ring
        _ ≤ uniformTopKFactor k *
                (1 / ((q + 1 : ℝ) * (q + 2 : ℝ))) :=
              mul_le_mul_of_nonneg_left hrec hfactor_nonneg
        _ = uniformTopKFactor k / ((q + 1 : ℝ) * (q + 2 : ℝ)) := by ring

noncomputable def uniformTopOneConsumptionModel {T : ℕ}
    (likelihood : ItemType T → ℝ) : ConsumptionModel T where
  likelihood := likelihood
  valueOfCount := fun _ q => uniformTopOneValue q

noncomputable def uniformTopKConsumptionModel {T : ℕ}
    (likelihood : ItemType T → ℝ) (k : ℕ) : ConsumptionModel T where
  likelihood := likelihood
  valueOfCount := fun _ q => uniformTopKValue k q

theorem uniformTopKConsumptionModel_has_diminishing_returns {T : ℕ}
    (likelihood : ItemType T → ℝ) (k : ℕ) :
    (uniformTopKConsumptionModel likelihood k).HasDiminishingReturns := by
  intro t q
  exact uniformTopKValue_marginal_antitone_step k q

theorem uniformTopOneConsumptionModel_has_diminishing_returns {T : ℕ}
    (likelihood : ItemType T → ℝ) :
    (uniformTopOneConsumptionModel likelihood).HasDiminishingReturns := by
  intro t q
  change uniformTopOneValue (q + 2) - uniformTopOneValue (q + 1) ≤
    uniformTopOneValue (q + 1) - uniformTopOneValue q
  rw [uniformTopOneValue_succ_sub (q + 1), uniformTopOneValue_succ_sub q]
  norm_num only [Nat.cast_add, Nat.cast_one]
  exact one_div_le_one_div_of_le (by positivity)
    (by nlinarith [show (0 : ℝ) ≤ q by positivity])

noncomputable def uniformSqrtTarget {T : ℕ}
    (likelihood : ItemType T → ℝ) (N : ℕ) (t : ItemType T) : ℝ := (N : ℝ) * (Real.sqrt (likelihood t) / ∑ i, Real.sqrt (likelihood i))

noncomputable def uniformSqrtShiftedTarget {T : ℕ}
    (likelihood : ItemType T → ℝ) (N : ℕ) (t : ItemType T) : ℝ := (N + T : ℝ) * (Real.sqrt (likelihood t) / ∑ i, Real.sqrt (likelihood i))

noncomputable def uniformSqrtRealOptTarget {T : ℕ}
    (likelihood : ItemType T → ℝ) (N : ℕ) (t : ItemType T) : ℝ := uniformSqrtShiftedTarget likelihood N t - 1

noncomputable def uniformSqrtPrintedOptTarget {T : ℕ}
    (likelihood : ItemType T → ℝ) (N : ℕ) (t : ItemType T) : ℝ := uniformSqrtTarget likelihood N t - 1

noncomputable def uniformSqrtScale {T : ℕ}
    (likelihood : ItemType T → ℝ) (N : ℕ) : ℝ := (∑ i, Real.sqrt (likelihood i)) ^ 2 / (N + T : ℝ) ^ 2

theorem likelihood_eq_scale_mul_shiftedTarget_sq {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (N : ℕ) (t : ItemType T)
    (hlike_nonneg : ∀ i, 0 ≤ likelihood i)
    (hnorm : ∑ i, Real.sqrt (likelihood i) ≠ 0) :
    likelihood t =
      uniformSqrtScale likelihood N *
        (uniformSqrtShiftedTarget likelihood N t) ^ 2 := by
  unfold uniformSqrtScale uniformSqrtShiftedTarget
  have hT_pos : 0 < (T : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne T)
  have hden : (N + T : ℝ) ≠ 0 := by positivity
  have hden2 : (N + T : ℝ) ^ 2 ≠ 0 := by positivity
  have hnorm2 : (∑ i, Real.sqrt (likelihood i)) ^ 2 ≠ 0 := by
    have h : (∑ i, Real.sqrt (likelihood i)) ^ 2 = (∑ i, Real.sqrt (likelihood i)) * (∑ i, Real.sqrt (likelihood i)) := by ring
    rw [h]
    exact mul_ne_zero hnorm hnorm
  have hsq1 : (Real.sqrt (likelihood t) / ∑ i, Real.sqrt (likelihood i)) ^ 2 =
      (Real.sqrt (likelihood t)) ^ 2 / (∑ i, Real.sqrt (likelihood i)) ^ 2 := by ring
  have hsq2 : ((N + T : ℝ) * (Real.sqrt (likelihood t) / ∑ i, Real.sqrt (likelihood i))) ^ 2 =
      (N + T : ℝ) ^ 2 * (Real.sqrt (likelihood t) / ∑ i, Real.sqrt (likelihood i)) ^ 2 := by ring
  rw [hsq2, hsq1]
  have h_mul : ((∑ i, Real.sqrt (likelihood i)) ^ 2 / (N + T : ℝ) ^ 2) *
        ((N + T : ℝ) ^ 2 * ((Real.sqrt (likelihood t)) ^ 2 / (∑ i, Real.sqrt (likelihood i)) ^ 2)) =
      (Real.sqrt (likelihood t)) ^ 2 := by
    calc
      ((∑ i, Real.sqrt (likelihood i)) ^ 2 / (N + T : ℝ) ^ 2) *
          ((N + T : ℝ) ^ 2 * ((Real.sqrt (likelihood t)) ^ 2 / (∑ i, Real.sqrt (likelihood i)) ^ 2))
        = (((∑ i, Real.sqrt (likelihood i)) ^ 2) / (∑ i, Real.sqrt (likelihood i)) ^ 2) *
            (((N + T : ℝ) ^ 2) / (N + T : ℝ) ^ 2) * (Real.sqrt (likelihood t)) ^ 2 := by ring
      _ = 1 * 1 * (Real.sqrt (likelihood t)) ^ 2 := by
          rw [div_self hnorm2, div_self hden2]
      _ = (Real.sqrt (likelihood t)) ^ 2 := by ring
  rw [h_mul]
  exact (Real.sq_sqrt (hlike_nonneg t)).symm

theorem uniformSqrtShiftedTarget_nonneg {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (N : ℕ) (t : ItemType T) :
    0 ≤ uniformSqrtShiftedTarget likelihood N t := by
  unfold uniformSqrtShiftedTarget
  have hT_pos : 0 < (T : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne T)
  have hsqrt_nonneg : 0 ≤ Real.sqrt (likelihood t) := Real.sqrt_nonneg _
  have hsum_nonneg : 0 ≤ ∑ i, Real.sqrt (likelihood i) := Finset.sum_nonneg (fun i _ => Real.sqrt_nonneg _)
  positivity

theorem sum_uniformSqrtShiftedTarget {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (N : ℕ)
    (hnorm : ∑ i, Real.sqrt (likelihood i) ≠ 0) :
    ∑ t, uniformSqrtShiftedTarget likelihood N t = N + T := by
  unfold uniformSqrtShiftedTarget
  have hrewrite : ∀ t, (N + T : ℝ) * (Real.sqrt (likelihood t) / ∑ i, Real.sqrt (likelihood i)) =
      ((N + T : ℝ) / ∑ i, Real.sqrt (likelihood i)) * Real.sqrt (likelihood t) := by
    intro t
    ring
  have hsum_rewrite : (∑ t, (N + T : ℝ) * (Real.sqrt (likelihood t) / ∑ i, Real.sqrt (likelihood i))) =
      ∑ t, ((N + T : ℝ) / ∑ i, Real.sqrt (likelihood i)) * Real.sqrt (likelihood t) :=
    Finset.sum_congr rfl (fun t _ => hrewrite t)
  rw [hsum_rewrite, ← Finset.mul_sum]
  have hden : (∑ i, Real.sqrt (likelihood i)) ≠ 0 := hnorm
  exact div_mul_cancel₀ (N + T : ℝ) hden

theorem sum_uniformSqrtRealOptTarget {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (N : ℕ)
    (hnorm : ∑ i, Real.sqrt (likelihood i) ≠ 0) :
    ∑ t, uniformSqrtRealOptTarget likelihood N t = N := by
  unfold uniformSqrtRealOptTarget
  rw [Finset.sum_sub_distrib, sum_uniformSqrtShiftedTarget likelihood N hnorm]
  simp [Fintype.card_fin]

theorem uniformSqrtRealOptTarget_add_one {T : ℕ}
    (likelihood : ItemType T → ℝ) (N : ℕ) (t : ItemType T) :
    uniformSqrtRealOptTarget likelihood N t + 1 =
      uniformSqrtShiftedTarget likelihood N t := by
  unfold uniformSqrtRealOptTarget
  ring

theorem sum_uniformSqrtPrintedOptTarget {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (N : ℕ)
    (hnorm : ∑ i, Real.sqrt (likelihood i) ≠ 0) :
    ∑ t, uniformSqrtPrintedOptTarget likelihood N t = (N : ℝ) - T := by
  unfold uniformSqrtPrintedOptTarget uniformSqrtTarget
  rw [Finset.sum_sub_distrib]
  have hrewrite :
      (∑ t : ItemType T,
          (N : ℝ) * (Real.sqrt (likelihood t) /
            ∑ i : ItemType T, Real.sqrt (likelihood i))) =
        (N : ℝ) := by
    have hpoint : ∀ t,
        (N : ℝ) * (Real.sqrt (likelihood t) /
          ∑ i : ItemType T, Real.sqrt (likelihood i)) =
        ((N : ℝ) / ∑ i : ItemType T, Real.sqrt (likelihood i)) *
          Real.sqrt (likelihood t) := by
      intro t
      ring
    calc
      (∑ t : ItemType T,
          (N : ℝ) * (Real.sqrt (likelihood t) /
            ∑ i : ItemType T, Real.sqrt (likelihood i)))
          = ∑ t : ItemType T,
              ((N : ℝ) / ∑ i : ItemType T, Real.sqrt (likelihood i)) *
                Real.sqrt (likelihood t) :=
              Finset.sum_congr rfl (fun t _ => hpoint t)
      _ = ((N : ℝ) / ∑ i : ItemType T, Real.sqrt (likelihood i)) *
            ∑ t : ItemType T, Real.sqrt (likelihood t) := by
              rw [Finset.mul_sum]
      _ = (N : ℝ) := div_mul_cancel₀ (N : ℝ) hnorm
  rw [hrewrite]
  simp [Fintype.card_fin]

theorem sum_uniformSqrtShiftedTarget_nonneg {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (N : ℕ) :
    0 ≤ ∑ t, uniformSqrtShiftedTarget likelihood N t := Finset.sum_nonneg (fun t _ => uniformSqrtShiftedTarget_nonneg _ _ _)

theorem sqrtLikelihoodProfile_normalizer_ne_zero {T : ℕ}
    (likelihood : ItemType T → ℝ)
    (hsum : 0 < ∑ i, likelihood i) (hnonneg : ∀ i, 0 ≤ likelihood i) :
    ∑ i : ItemType T, Real.sqrt (likelihood i) ≠ 0 := by
  intro h
  have hwnonneg : ∀ i ∈ (Finset.univ : Finset (ItemType T)), 0 ≤ Real.sqrt (likelihood i) := fun i _ => Real.sqrt_nonneg _
  have h0 : ∀ i, Real.sqrt (likelihood i) = 0 := by
    intro i
    exact (Finset.sum_eq_zero_iff_of_nonneg hwnonneg).mp h i (Finset.mem_univ i)
  have hw0 : ∀ i, likelihood i = 0 := by
    intro i
    have hi := h0 i
    rwa [Real.sqrt_eq_zero (hnonneg i)] at hi
  have hsum0 : (∑ i, likelihood i) = 0 := Finset.sum_eq_zero (fun i _ => hw0 i)
  linarith

noncomputable def floorCountAnchor {T : ℕ}
    (target : ItemType T → ℝ) : CountAllocation T where
  count := fun t => ⌊target t⌋₊

noncomputable def uniformSqrtUpperAnchor {T : ℕ}
    (likelihood : ItemType T → ℝ) (N : ℕ) : CountAllocation T := floorCountAnchor (uniformSqrtShiftedTarget likelihood N)

noncomputable def uniformSqrtLowerAnchor {T : ℕ}
    (likelihood : ItemType T → ℝ) (N : ℕ) : CountAllocation T where
  count := fun t => ⌊uniformSqrtShiftedTarget likelihood N t⌋₊ - 1

theorem total_uniformSqrtUpperAnchor_le {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (N : ℕ)
    (hnorm : ∑ i, Real.sqrt (likelihood i) ≠ 0) :
    (AppliedModelingLib.Allocation.total (uniformSqrtUpperAnchor likelihood N) : ℝ) ≤ N + T := by
  unfold uniformSqrtUpperAnchor floorCountAnchor AppliedModelingLib.Allocation.total
  dsimp only
  have h_le : ∀ t, (⌊uniformSqrtShiftedTarget likelihood N t⌋₊ : ℝ) ≤ uniformSqrtShiftedTarget likelihood N t := by
    intro t
    exact Nat.floor_le (uniformSqrtShiftedTarget_nonneg likelihood N t)
  calc
    ((∑ t, ⌊uniformSqrtShiftedTarget likelihood N t⌋₊ : ℕ) : ℝ)
        = ∑ t, (⌊uniformSqrtShiftedTarget likelihood N t⌋₊ : ℝ) := by push_cast; rfl
    _ ≤ ∑ t, uniformSqrtShiftedTarget likelihood N t := Finset.sum_le_sum (fun t _ => h_le t)
    _ = N + T := sum_uniformSqrtShiftedTarget likelihood N hnorm

theorem total_uniformSqrtLowerAnchor_le_N {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (N : ℕ)
    (hnorm : ∑ i, Real.sqrt (likelihood i) ≠ 0)
    (h_interior : ∀ t, 1 ≤ uniformSqrtShiftedTarget likelihood N t) :
    (AppliedModelingLib.Allocation.total (uniformSqrtLowerAnchor likelihood N) : ℝ) ≤ N := by
  unfold uniformSqrtLowerAnchor AppliedModelingLib.Allocation.total
  dsimp only
  have h_ge1 : ∀ t, 1 ≤ ⌊uniformSqrtShiftedTarget likelihood N t⌋₊ := by
    intro t
    exact Nat.succ_le_of_lt (Nat.floor_pos.mpr (h_interior t))
  have h_le : ∀ t, ((⌊uniformSqrtShiftedTarget likelihood N t⌋₊ - 1 : ℕ) : ℝ) ≤ uniformSqrtShiftedTarget likelihood N t - 1 :=
  by
    intro t
    rw [Nat.cast_sub (h_ge1 t), Nat.cast_one]
    exact sub_le_sub_right (Nat.floor_le (uniformSqrtShiftedTarget_nonneg likelihood N t)) 1
  calc
    ((∑ t, (⌊uniformSqrtShiftedTarget likelihood N t⌋₊ - 1) : ℕ) : ℝ)
        = ∑ t, ((⌊uniformSqrtShiftedTarget likelihood N t⌋₊ - 1 : ℕ) : ℝ) := by push_cast; rfl
    _ ≤ ∑ t, (uniformSqrtShiftedTarget likelihood N t - 1) := Finset.sum_le_sum (fun t _ => h_le t)
    _ = (∑ t, uniformSqrtShiftedTarget likelihood N t) - T := by
          rw [Finset.sum_sub_distrib]
          simp
    _ = N := by
          rw [sum_uniformSqrtShiftedTarget likelihood N hnorm]
          ring

theorem total_uniformSqrtLowerAnchor_eq_N_of_integers {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (N : ℕ)
    (hnorm : ∑ i, Real.sqrt (likelihood i) ≠ 0)
    (h_interior : ∀ t, 1 ≤ uniformSqrtShiftedTarget likelihood N t)
    (hintegers : ∀ t, uniformSqrtShiftedTarget likelihood N t = ⌊uniformSqrtShiftedTarget likelihood N t⌋₊) :
    (AppliedModelingLib.Allocation.total (uniformSqrtLowerAnchor likelihood N) : ℝ) = N := by
  unfold uniformSqrtLowerAnchor AppliedModelingLib.Allocation.total
  dsimp only
  have h_ge1 : ∀ t, 1 ≤ ⌊uniformSqrtShiftedTarget likelihood N t⌋₊ := by
    intro t
    exact Nat.succ_le_of_lt (Nat.floor_pos.mpr (h_interior t))
  have h_eq : ∀ t, ((⌊uniformSqrtShiftedTarget likelihood N t⌋₊ - 1 : ℕ) : ℝ) = uniformSqrtShiftedTarget likelihood N t - 1 :=
  by
    intro t
    rw [Nat.cast_sub (h_ge1 t), Nat.cast_one]
    rw [← hintegers t]
  calc
    ((∑ t, (⌊uniformSqrtShiftedTarget likelihood N t⌋₊ - 1) : ℕ) : ℝ)
        = ∑ t, ((⌊uniformSqrtShiftedTarget likelihood N t⌋₊ - 1 : ℕ) : ℝ) := by push_cast; rfl
    _ = ∑ t, (uniformSqrtShiftedTarget likelihood N t - 1) := Finset.sum_congr rfl (fun t _ => h_eq t)
    _ = (∑ t, uniformSqrtShiftedTarget likelihood N t) - T := by
          rw [Finset.sum_sub_distrib]
          simp
    _ = N := by
          rw [sum_uniformSqrtShiftedTarget likelihood N hnorm]
          ring

theorem total_uniformSqrtLowerAnchor_gt_N_sub_T_refined {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (N : ℕ)
    (hnorm : ∑ i, Real.sqrt (likelihood i) ≠ 0)
    (h_interior : ∀ t, 1 ≤ uniformSqrtShiftedTarget likelihood N t)
    (hnot_integers : ∃ t, uniformSqrtShiftedTarget likelihood N t ≠ ⌊uniformSqrtShiftedTarget likelihood N t⌋₊) :
    (N : ℝ) - T < (AppliedModelingLib.Allocation.total (uniformSqrtLowerAnchor likelihood N) : ℝ) := by
  unfold uniformSqrtLowerAnchor AppliedModelingLib.Allocation.total
  dsimp only
  have h_ge1 : ∀ t, 1 ≤ ⌊uniformSqrtShiftedTarget likelihood N t⌋₊ := by
    intro t
    exact Nat.succ_le_of_lt (Nat.floor_pos.mpr (h_interior t))
  have h_eq : ∀ t, ((⌊uniformSqrtShiftedTarget likelihood N t⌋₊ - 1 : ℕ) : ℝ) = (⌊uniformSqrtShiftedTarget likelihood N t⌋₊ : ℝ) - 1 :=
  by
    intro t
    rw [Nat.cast_sub (h_ge1 t), Nat.cast_one]
  have h_sum_rewrite : ((∑ t, (⌊uniformSqrtShiftedTarget likelihood N t⌋₊ - 1) : ℕ) : ℝ) = ∑ t, ((⌊uniformSqrtShiftedTarget likelihood N t⌋₊ : ℝ) - 1) :=
  by
    calc
      ((∑ t, (⌊uniformSqrtShiftedTarget likelihood N t⌋₊ - 1) : ℕ) : ℝ)
          = ∑ t, ((⌊uniformSqrtShiftedTarget likelihood N t⌋₊ - 1 : ℕ) : ℝ) := by push_cast; rfl
      _ = ∑ t, ((⌊uniformSqrtShiftedTarget likelihood N t⌋₊ : ℝ) - 1) := Finset.sum_congr rfl (fun t _ => h_eq t)
  rw [h_sum_rewrite]
  rw [Finset.sum_sub_distrib]
  simp
  have h_lt : ∑ t, (⌊uniformSqrtShiftedTarget likelihood N t⌋₊ : ℝ) > (∑ t, uniformSqrtShiftedTarget likelihood N t) - T := by
    have h_diff : (∑ t, uniformSqrtShiftedTarget likelihood N t) - ∑ t, (⌊uniformSqrtShiftedTarget likelihood N t⌋₊ : ℝ) = ∑ t, (uniformSqrtShiftedTarget likelihood N t - ⌊uniformSqrtShiftedTarget likelihood N t⌋₊) :=
  by
      rw [Finset.sum_sub_distrib]
    have h_sum_lt_T : ∑ t, (uniformSqrtShiftedTarget likelihood N t - ⌊uniformSqrtShiftedTarget likelihood N t⌋₊) < T := by
      have h_lt_one : ∀ t, uniformSqrtShiftedTarget likelihood N t - ⌊uniformSqrtShiftedTarget likelihood N t⌋₊ < 1 := by
        intro t
        have ht := Nat.lt_floor_add_one (uniformSqrtShiftedTarget likelihood N t)
        linarith
      calc
        ∑ t, (uniformSqrtShiftedTarget likelihood N t - ⌊uniformSqrtShiftedTarget likelihood N t⌋₊)
            < ∑ t : ItemType T, (1 : ℝ) := Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty) (fun t _ => h_lt_one t)
        _ = T := by simp
    linarith
  have hsum_target := sum_uniformSqrtShiftedTarget likelihood N hnorm
  linarith

theorem uniformSqrtUpperAnchor_shift_le {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (N : ℕ) (t : ItemType T) :
    uniformSqrtShiftedTarget likelihood N t ≤
      ((uniformSqrtUpperAnchor likelihood N).count t : ℝ) + 1 := by
  unfold uniformSqrtUpperAnchor floorCountAnchor
  dsimp only
  exact le_of_lt (Nat.lt_floor_add_one (uniformSqrtShiftedTarget likelihood N t))

theorem uniformSqrtLowerAnchor_le_shift {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (N : ℕ) (t : ItemType T)
    (h_interior : ∀ t, 1 ≤ uniformSqrtShiftedTarget likelihood N t) :
    ((uniformSqrtLowerAnchor likelihood N).count t : ℝ) + 1 ≤
      uniformSqrtShiftedTarget likelihood N t := by
  unfold uniformSqrtLowerAnchor
  dsimp only
  have hge1 : 1 ≤ ⌊uniformSqrtShiftedTarget likelihood N t⌋₊ :=
    Nat.succ_le_of_lt (Nat.floor_pos.mpr (h_interior t))
  rw [Nat.cast_sub hge1]
  push_cast
  have hfloor := Nat.floor_le (uniformSqrtShiftedTarget_nonneg likelihood N t)
  linarith

theorem uniformSqrtUpperAnchor_abs_close {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (N : ℕ) (t : ItemType T)
    (hnorm : ∑ i, Real.sqrt (likelihood i) ≠ 0) :
    |((uniformSqrtUpperAnchor likelihood N).count t : ℝ) -
      uniformSqrtTarget likelihood N t| < (T : ℝ) + 1 := by
  unfold uniformSqrtUpperAnchor floorCountAnchor uniformSqrtShiftedTarget uniformSqrtTarget
  dsimp only
  have h_frac_nonneg : 0 ≤ Real.sqrt (likelihood t) / ∑ i, Real.sqrt (likelihood i) := by
    have h1 : 0 ≤ Real.sqrt (likelihood t) := Real.sqrt_nonneg _
    have h2 : 0 ≤ ∑ i, Real.sqrt (likelihood i) := Finset.sum_nonneg (fun i _ => Real.sqrt_nonneg _)
    positivity
  have h_den_pos : 0 < ∑ i, Real.sqrt (likelihood i) := by
    have h2 : 0 ≤ ∑ i, Real.sqrt (likelihood i) := Finset.sum_nonneg (fun i _ => Real.sqrt_nonneg _)
    exact lt_of_le_of_ne h2 hnorm.symm
  have h_frac_le_one : Real.sqrt (likelihood t) / ∑ i, Real.sqrt (likelihood i) ≤ 1 := by
    have hsum : Real.sqrt (likelihood t) ≤ ∑ i, Real.sqrt (likelihood i) :=
      Finset.single_le_sum (fun i _ => Real.sqrt_nonneg _) (Finset.mem_univ t)
    exact (div_le_one₀ h_den_pos).mpr hsum
  have h_shift : ((N : ℝ) + T) * (Real.sqrt (likelihood t) / ∑ i, Real.sqrt (likelihood i)) =
      (N : ℝ) * (Real.sqrt (likelihood t) / ∑ i, Real.sqrt (likelihood i)) + (T : ℝ) * (Real.sqrt (likelihood t) / ∑ i, Real.sqrt (likelihood i)) :=
  by ring
  have h_floor_le := Nat.floor_le (uniformSqrtShiftedTarget_nonneg likelihood N t)
  have h_le_floor_add_one := Nat.lt_floor_add_one (uniformSqrtShiftedTarget likelihood N t)
  have h_T_frac_le_T : (T : ℝ) * (Real.sqrt (likelihood t) / ∑ i, Real.sqrt (likelihood i)) ≤ T := by
    calc
      (T : ℝ) * (Real.sqrt (likelihood t) / ∑ i, Real.sqrt (likelihood i))
          ≤ (T : ℝ) * 1 := mul_le_mul_of_nonneg_left h_frac_le_one (by positivity)
      _ = T := mul_one _
  have h_pos_T : 0 ≤ (T : ℝ) * (Real.sqrt (likelihood t) / ∑ i, Real.sqrt (likelihood i)) := mul_nonneg (by positivity) h_frac_nonneg
  have h_pos_T_num : 0 ≤ (T : ℝ) := by positivity
  rw [abs_lt]
  constructor
  · unfold uniformSqrtShiftedTarget at h_floor_le h_le_floor_add_one
    linarith
  · unfold uniformSqrtShiftedTarget at h_floor_le h_le_floor_add_one
    linarith

theorem uniformSqrtLowerAnchor_abs_close {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (N : ℕ) (t : ItemType T)
    (hnorm : ∑ i, Real.sqrt (likelihood i) ≠ 0)
    (h_interior : ∀ t, 1 ≤ uniformSqrtShiftedTarget likelihood N t) :
    |((uniformSqrtLowerAnchor likelihood N).count t : ℝ) -
      uniformSqrtTarget likelihood N t| < (T : ℝ) + 1 := by
  unfold uniformSqrtLowerAnchor uniformSqrtShiftedTarget uniformSqrtTarget
  dsimp only
  have h_frac_nonneg : 0 ≤ Real.sqrt (likelihood t) / ∑ i, Real.sqrt (likelihood i) := by
    have h1 : 0 ≤ Real.sqrt (likelihood t) := Real.sqrt_nonneg _
    have h2 : 0 ≤ ∑ i, Real.sqrt (likelihood i) := Finset.sum_nonneg (fun i _ => Real.sqrt_nonneg _)
    positivity
  have h_den_pos : 0 < ∑ i, Real.sqrt (likelihood i) := by
    have h2 : 0 ≤ ∑ i, Real.sqrt (likelihood i) := Finset.sum_nonneg (fun i _ => Real.sqrt_nonneg _)
    exact lt_of_le_of_ne h2 hnorm.symm
  have h_frac_le_one : Real.sqrt (likelihood t) / ∑ i, Real.sqrt (likelihood i) ≤ 1 := by
    have hsum : Real.sqrt (likelihood t) ≤ ∑ i, Real.sqrt (likelihood i) :=
      Finset.single_le_sum (fun i _ => Real.sqrt_nonneg _) (Finset.mem_univ t)
    exact (div_le_one₀ h_den_pos).mpr hsum
  have h_shift : ((N : ℝ) + T) * (Real.sqrt (likelihood t) / ∑ i, Real.sqrt (likelihood i)) =
      (N : ℝ) * (Real.sqrt (likelihood t) / ∑ i, Real.sqrt (likelihood i)) + (T : ℝ) * (Real.sqrt (likelihood t) / ∑ i, Real.sqrt (likelihood i)) :=
  by ring
  have h_floor_le := Nat.floor_le (uniformSqrtShiftedTarget_nonneg likelihood N t)
  have h_le_floor_add_one := Nat.lt_floor_add_one (uniformSqrtShiftedTarget likelihood N t)
  have h_T_frac_le_T : (T : ℝ) * (Real.sqrt (likelihood t) / ∑ i, Real.sqrt (likelihood i)) ≤ T := by
    calc
      (T : ℝ) * (Real.sqrt (likelihood t) / ∑ i, Real.sqrt (likelihood i))
          ≤ (T : ℝ) * 1 := mul_le_mul_of_nonneg_left h_frac_le_one (by positivity)
      _ = T := mul_one _
  have h_pos_T : 0 ≤ (T : ℝ) * (Real.sqrt (likelihood t) / ∑ i, Real.sqrt (likelihood i)) := mul_nonneg (by positivity) h_frac_nonneg
  have hT_ge_1 : 1 ≤ (T : ℝ) := by exact_mod_cast NeZero.one_le
  have h_sub : ((⌊((N : ℝ) + T) * (Real.sqrt (likelihood t) / ∑ i, Real.sqrt (likelihood i))⌋₊ - 1 : ℕ) : ℝ) ≤
      (⌊((N : ℝ) + T) * (Real.sqrt (likelihood t) / ∑ i, Real.sqrt (likelihood i))⌋₊ : ℝ) := by
    exact_mod_cast Nat.sub_le _ _
  have h_sub_lower : (⌊((N : ℝ) + T) * (Real.sqrt (likelihood t) / ∑ i, Real.sqrt (likelihood i))⌋₊ : ℝ) - 1 ≤
      ((⌊((N : ℝ) + T) * (Real.sqrt (likelihood t) / ∑ i, Real.sqrt (likelihood i))⌋₊ - 1 : ℕ) : ℝ) := by
    have hge1 : 1 ≤ ⌊((N : ℝ) + T) * (Real.sqrt (likelihood t) / ∑ i, Real.sqrt (likelihood i))⌋₊ :=
  Nat.succ_le_of_lt (Nat.floor_pos.mpr (h_interior t))
    rw [Nat.cast_sub hge1, Nat.cast_one]
  rw [abs_lt]
  constructor
  · unfold uniformSqrtShiftedTarget at h_floor_le h_le_floor_add_one
    linarith
  · unfold uniformSqrtShiftedTarget at h_floor_le h_le_floor_add_one
    linarith

noncomputable def sqrtLikelihoodProfile {T : ℕ}
    (likelihood : ItemType T → ℝ) : GammaHomogeneityProfile T where
  gamma := 1 / 2
  targetWeight := fun t => Real.sqrt (likelihood t)

noncomputable def uniformSqrtMinShare {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) : ℝ :=
  AppliedModelingLib.finiteMin
    (fun t : ItemType T =>
      Real.sqrt (likelihood t) / ∑ i : ItemType T, Real.sqrt (likelihood i))

theorem uniformSqrtMinShare_le_share {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (t : ItemType T) :
    uniformSqrtMinShare likelihood ≤
      Real.sqrt (likelihood t) / ∑ i : ItemType T, Real.sqrt (likelihood i) := by
  unfold uniformSqrtMinShare
  exact AppliedModelingLib.finiteMin_le
    (fun t : ItemType T =>
      Real.sqrt (likelihood t) / ∑ i : ItemType T, Real.sqrt (likelihood i)) t

theorem uniformSqrtTarget_le_shiftedTarget {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (N : ℕ) (t : ItemType T)
    (hnorm : ∑ i : ItemType T, Real.sqrt (likelihood i) ≠ 0) :
    uniformSqrtTarget likelihood N t ≤ uniformSqrtShiftedTarget likelihood N t := by
  unfold uniformSqrtTarget uniformSqrtShiftedTarget
  have hden_nonneg : 0 ≤ ∑ i : ItemType T, Real.sqrt (likelihood i) :=
    Finset.sum_nonneg (fun i _ => Real.sqrt_nonneg _)
  have hden_pos : 0 < ∑ i : ItemType T, Real.sqrt (likelihood i) :=
    lt_of_le_of_ne hden_nonneg hnorm.symm
  have hfrac_nonneg :
      0 ≤ Real.sqrt (likelihood t) / ∑ i : ItemType T, Real.sqrt (likelihood i) :=
    div_nonneg (Real.sqrt_nonneg _) (le_of_lt hden_pos)
  nlinarith [show (0 : ℝ) ≤ T by positivity]

theorem uniformTopK_eligible_of_paper_min_share_bound {T : ℕ} [NeZero T]
    (likelihood : ItemType T → ℝ) (N k : ℕ)
    (hnorm : ∑ i : ItemType T, Real.sqrt (likelihood i) ≠ 0)
    (hbound :
      (k : ℝ) + 1 ≤ (N : ℝ) * uniformSqrtMinShare likelihood - T) :
    ∀ t, (k : ℝ) + 1 ≤ uniformSqrtShiftedTarget likelihood N t := by
  intro t
  have hmin_le := uniformSqrtMinShare_le_share likelihood t
  have hN_nonneg : 0 ≤ (N : ℝ) := by positivity
  have htarget_bound :
      (k : ℝ) + 1 ≤ uniformSqrtTarget likelihood N t := by
    unfold uniformSqrtTarget
    nlinarith [mul_le_mul_of_nonneg_left hmin_le hN_nonneg,
      show (0 : ℝ) ≤ T by positivity]
  exact le_trans htarget_bound
    (uniformSqrtTarget_le_shiftedTarget likelihood N t hnorm)

namespace sqrtLikelihoodProfile

@[simp] theorem normalizer_eq {T : ℕ}
    (likelihood : ItemType T → ℝ) :
    (sqrtLikelihoodProfile likelihood).normalizer =
      ∑ t : ItemType T, Real.sqrt (likelihood t) := by
  rfl

theorem targetShare_eq {T : ℕ}
    (likelihood : ItemType T → ℝ) (t : ItemType T)
    (hnorm : (∑ i : ItemType T, Real.sqrt (likelihood i)) ≠ 0) :
    (sqrtLikelihoodProfile likelihood).targetShare t =
      Real.sqrt (likelihood t) /
        ∑ i : ItemType T, Real.sqrt (likelihood i) :=
   GammaHomogeneityProfile.targetShare_eq_div_of_normalizer_ne_zero
    (G := sqrtLikelihoodProfile likelihood) (t := t) (by simpa using hnorm)

theorem approx_of_count_abs_error {T : ℕ}
    (likelihood : ItemType T → ℝ) (a : CountAllocation T) {N : ℕ} {C : ℝ}
    (hN : AppliedModelingLib.Allocation.total a = N) (hNpos : 0 < N)
    (hclose :
      ∀ t,
        |(a.count t : ℝ) -
          (N : ℝ) * (sqrtLikelihoodProfile likelihood).targetShare t| ≤ C) :
    (sqrtLikelihoodProfile likelihood).Approx a (C / (N : ℝ)) :=
   GammaHomogeneityProfile.approx_of_count_abs_error
    (sqrtLikelihoodProfile likelihood) a hN hNpos hclose

end sqrtLikelihoodProfile

namespace UniformTopOne

def StrictRoundingExchangeCertificateBetween {T : ℕ}
    (likelihood : ItemType T → ℝ)
    (lower upper : CountAllocation T) : Prop :=
  ∀ high low,
    0 < lower.count low →
      (likelihood high * (1 / ((upper.count high + 1 : ℝ) * (upper.count high + 2 : ℝ)))) <
        (likelihood low * (1 / ((lower.count low : ℝ) * (lower.count low + 1 : ℝ))))

theorem forwardMarginal_le_backwardMarginal_of_optimum {T : ℕ}
    (likelihood : ItemType T → ℝ) (N : ℕ)
    {a : CountAllocation T} {src dst : ItemType T}
    (hopt : (uniformTopOneConsumptionModel likelihood).IsOptimalAtTotal N a)
    (hne : src ≠ dst)
    (hcan : AppliedModelingLib.Allocation.CanMoveOne a src) :
    likelihood dst *
        (1 / ((a.count dst + 1 : ℝ) * (a.count dst + 2 : ℝ))) ≤
      likelihood src *
        (1 / ((a.count src : ℝ) * (a.count src + 1 : ℝ))) := by
  have h :=
  ConsumptionModel.weightedForwardMarginal_le_weightedBackwardMarginal_of_optimum (uniformTopOneConsumptionModel likelihood) N hopt hne hcan
  unfold ConsumptionModel.weightedForwardMarginal ConsumptionModel.weightedBackwardMarginal at h
  unfold ConsumptionModel.marginalValue at h
  unfold AppliedModelingLib.Allocation.marginal at h
  unfold uniformTopOneConsumptionModel at h
  dsimp only at h
  have hq : 0 < a.count src := hcan
  have hne0 : a.count src ≠ 0 := ne_of_gt hcan
  rw [dif_neg hne0] at h
  rw [uniformTopOneValue_succ_sub] at h
  rw [uniformTopOneValue_sub_pred hq] at h
  exact h

theorem noRoundingCrossingBetween_of_strictExchangeCertificate {T : ℕ}
    (likelihood : ItemType T → ℝ) (N : ℕ)
    {a lower upper : CountAllocation T}
    (hopt : (uniformTopOneConsumptionModel likelihood).IsOptimalAtTotal N a)
    (hlike_nonneg : ∀ t, 0 ≤ likelihood t)
    (horder : ∀ t, lower.count t ≤ upper.count t)
    (hcert : StrictRoundingExchangeCertificateBetween likelihood lower upper) :
    AppliedModelingLib.FiniteRounding.NoRoundingCrossingBetween
      (fun t : ItemType T => a.count t)
      (fun t : ItemType T => lower.count t)
      (fun t : ItemType T => upper.count t) := by
  have hcert' :
      (uniformTopOneConsumptionModel likelihood).StrictRoundingExchangeCertificateBetween
        lower upper := by
    intro high low hlow
    have hlow_ne : lower.count low ≠ 0 := ne_of_gt hlow
    simpa [ConsumptionModel.StrictRoundingExchangeCertificateBetween,
      ConsumptionModel.weightedForwardMarginal, ConsumptionModel.weightedBackwardMarginal,
      ConsumptionModel.marginalValue, uniformTopOneConsumptionModel,
      AppliedModelingLib.Allocation.marginal, hlow_ne, uniformTopOneValue_succ_sub,
      uniformTopOneValue_sub_pred hlow] using hcert high low hlow
  exact
    ConsumptionModel.noRoundingCrossingBetween_of_strictExchangeCertificate
      (uniformTopOneConsumptionModel likelihood) N hopt
      (uniformTopOneConsumptionModel_has_diminishing_returns likelihood)
      hlike_nonneg horder hcert'

theorem strictRoundingExchangeCertificateBetween_of_shifted_target {T : ℕ}
    (likelihood : ItemType T → ℝ)
    (lower upper : CountAllocation T)
    (scale : ℝ) (shift : ItemType T → ℝ)
    (hscale_pos : 0 < scale)
    (hlike : ∀ t, likelihood t = scale * (shift t) ^ 2)
    (hshift_nonneg : ∀ t, 0 ≤ shift t)
    (hupper : ∀ t, shift t ≤ (upper.count t : ℝ) + 1)
    (hlower : ∀ t, 0 < lower.count t → (lower.count t : ℝ) + 1 ≤ shift t) :
    StrictRoundingExchangeCertificateBetween likelihood lower upper := by
  intro high low h_low_pos
  have hu : shift high ≤ (upper.count high : ℝ) + 1 := hupper high
  have hl : (lower.count low : ℝ) + 1 ≤ shift low := hlower low h_low_pos
  have h_sh_pos : 0 ≤ shift high := hshift_nonneg high
  have h_u_pos : 0 ≤ (upper.count high : ℝ) + 1 := by positivity
  have hs_h_sq_le : (shift high) ^ 2 ≤ ((upper.count high : ℝ) + 1) ^ 2 := by nlinarith
  have hs_h_lt : (shift high) ^ 2 / (((upper.count high : ℝ) + 1) * ((upper.count high : ℝ) + 2)) < 1 := by
    rw [div_lt_iff₀ (by positivity)]
    calc
      (shift high) ^ 2 ≤ ((upper.count high : ℝ) + 1) ^ 2 := hs_h_sq_le
      _ = ((upper.count high : ℝ) + 1) * ((upper.count high : ℝ) + 1) := by ring
      _ < ((upper.count high : ℝ) + 1) * ((upper.count high : ℝ) + 2) := by nlinarith
      _ = 1 * (((upper.count high : ℝ) + 1) * ((upper.count high : ℝ) + 2)) := by ring
  have h_l_pos : 0 ≤ (lower.count low : ℝ) + 1 := by positivity
  have h_sl_pos : 0 ≤ shift low := hshift_nonneg low
  have hs_l_sq_ge : ((lower.count low : ℝ) + 1) ^ 2 ≤ (shift low) ^ 2 := by nlinarith
  have hs_l_gt : 1 < (shift low) ^ 2 / ((lower.count low : ℝ) * ((lower.count low : ℝ) + 1)) := by
    rw [lt_div_iff₀ (by positivity)]
    calc
      1 * ((lower.count low : ℝ) * ((lower.count low : ℝ) + 1)) = (lower.count low : ℝ) * ((lower.count low : ℝ) + 1) := by ring
      _ < ((lower.count low : ℝ) + 1) * ((lower.count low : ℝ) + 1) := by nlinarith
      _ = ((lower.count low : ℝ) + 1) ^ 2 := by ring
      _ ≤ (shift low) ^ 2 := hs_l_sq_ge
  rw [hlike high, hlike low]
  calc
    scale * (shift high) ^ 2 * (1 / (((upper.count high : ℝ) + 1) * ((upper.count high : ℝ) + 2)))
        = scale * ((shift high) ^ 2 / (((upper.count high : ℝ) + 1) * ((upper.count high : ℝ) + 2))) := by ring
    _ < scale * 1 := mul_lt_mul_of_pos_left hs_h_lt hscale_pos
    _ = scale * 1 := by rfl
    _ < scale * ((shift low) ^ 2 / ((lower.count low : ℝ) * ((lower.count low : ℝ) + 1))) :=
      mul_lt_mul_of_pos_left hs_l_gt hscale_pos
    _ = scale * (shift low) ^ 2 * (1 / ((lower.count low : ℝ) * ((lower.count low : ℝ) + 1))) := by ring

end UniformTopOne

namespace UniformTopK

theorem weightedForwardMarginal_eq_of_le {T : ℕ}
    (likelihood : ItemType T → ℝ) (k : ℕ) (t : ItemType T) {q : ℕ}
    (hkq : k ≤ q) :
    (uniformTopKConsumptionModel likelihood k).weightedForwardMarginal t q =
      likelihood t *
        (uniformTopKFactor k / ((q + 1 : ℝ) * (q + 2 : ℝ))) := by
  unfold ConsumptionModel.weightedForwardMarginal ConsumptionModel.marginalValue
    AppliedModelingLib.Allocation.marginal uniformTopKConsumptionModel
  dsimp only
  rw [uniformTopKValue_succ_sub_of_le hkq]

theorem weightedBackwardMarginal_eq_of_le {T : ℕ}
    (likelihood : ItemType T → ℝ) (k : ℕ) (t : ItemType T) {q : ℕ}
    (hkq : k ≤ q) (hq : 0 < q) :
    (uniformTopKConsumptionModel likelihood k).weightedBackwardMarginal t q =
      likelihood t *
        (uniformTopKFactor k / ((q : ℝ) * (q + 1 : ℝ))) := by
  unfold ConsumptionModel.weightedBackwardMarginal uniformTopKConsumptionModel
  dsimp only
  have hq_ne : ¬ q = 0 := ne_of_gt hq
  simp [hq_ne, uniformTopKValue_sub_pred_of_le hkq hq]

theorem strictRoundingExchangeCertificateBetween_of_shifted_target {T : ℕ}
    (likelihood : ItemType T → ℝ) (k : ℕ)
    (lower upper : CountAllocation T)
    (scale : ℝ) (shift : ItemType T → ℝ)
    (hk_pos : 0 < k)
    (hscale_pos : 0 < scale)
    (hlike : ∀ t, likelihood t = scale * (shift t) ^ 2)
    (hshift_nonneg : ∀ t, 0 ≤ shift t)
    (hupper_tail : ∀ t, k ≤ upper.count t)
    (hlower_tail : ∀ t, k ≤ lower.count t)
    (hupper : ∀ t, shift t ≤ (upper.count t : ℝ) + 1)
    (hlower : ∀ t, 0 < lower.count t → (lower.count t : ℝ) + 1 ≤ shift t) :
    (uniformTopKConsumptionModel likelihood k).StrictRoundingExchangeCertificateBetween
      lower upper := by
  intro high low h_low_pos
  rw [weightedForwardMarginal_eq_of_le likelihood k high (hupper_tail high),
    weightedBackwardMarginal_eq_of_le likelihood k low (hlower_tail low) h_low_pos,
    hlike high, hlike low]
  have hcoef_pos : 0 < scale * uniformTopKFactor k :=
    mul_pos hscale_pos (uniformTopKFactor_pos hk_pos)
  have hu : shift high ≤ (upper.count high : ℝ) + 1 := hupper high
  have hl : (lower.count low : ℝ) + 1 ≤ shift low := hlower low h_low_pos
  have h_sh_pos : 0 ≤ shift high := hshift_nonneg high
  have hs_h_sq_le : (shift high) ^ 2 ≤ ((upper.count high : ℝ) + 1) ^ 2 := by
    nlinarith
  have hs_h_lt :
      (shift high) ^ 2 /
          (((upper.count high : ℝ) + 1) * ((upper.count high : ℝ) + 2)) < 1 := by
    rw [div_lt_iff₀ (by positivity)]
    calc
      (shift high) ^ 2 ≤ ((upper.count high : ℝ) + 1) ^ 2 := hs_h_sq_le
      _ = ((upper.count high : ℝ) + 1) * ((upper.count high : ℝ) + 1) := by ring
      _ < ((upper.count high : ℝ) + 1) * ((upper.count high : ℝ) + 2) := by nlinarith
      _ = 1 * (((upper.count high : ℝ) + 1) * ((upper.count high : ℝ) + 2)) := by ring
  have h_sl_pos : 0 ≤ shift low := hshift_nonneg low
  have hs_l_sq_ge : ((lower.count low : ℝ) + 1) ^ 2 ≤ (shift low) ^ 2 := by
    nlinarith
  have hs_l_gt :
      1 < (shift low) ^ 2 /
          ((lower.count low : ℝ) * ((lower.count low : ℝ) + 1)) := by
    rw [lt_div_iff₀ (by positivity)]
    calc
      1 * ((lower.count low : ℝ) * ((lower.count low : ℝ) + 1)) =
          (lower.count low : ℝ) * ((lower.count low : ℝ) + 1) := by ring
      _ < ((lower.count low : ℝ) + 1) * ((lower.count low : ℝ) + 1) := by nlinarith
      _ = ((lower.count low : ℝ) + 1) ^ 2 := by ring
      _ ≤ (shift low) ^ 2 := hs_l_sq_ge
  calc
    scale * (shift high) ^ 2 *
        (uniformTopKFactor k /
          (((upper.count high : ℝ) + 1) * ((upper.count high : ℝ) + 2)))
        = (scale * uniformTopKFactor k) *
            ((shift high) ^ 2 /
              (((upper.count high : ℝ) + 1) * ((upper.count high : ℝ) + 2))) := by ring
    _ < (scale * uniformTopKFactor k) * 1 :=
          mul_lt_mul_of_pos_left hs_h_lt hcoef_pos
    _ < (scale * uniformTopKFactor k) *
            ((shift low) ^ 2 /
              ((lower.count low : ℝ) * ((lower.count low : ℝ) + 1))) :=
          mul_lt_mul_of_pos_left hs_l_gt hcoef_pos
    _ = scale * (shift low) ^ 2 *
        (uniformTopKFactor k /
          ((lower.count low : ℝ) * ((lower.count low : ℝ) + 1))) := by ring

end UniformTopK

namespace UniformRounding

theorem count_close_of_no_rounding_crossing_between {T : ℕ}
    (a lower upper : CountAllocation T) {N L U : ℕ}
    (ha : AppliedModelingLib.Allocation.total a = N)
    (hlower : AppliedModelingLib.Allocation.total lower = L)
    (hupper : AppliedModelingLib.Allocation.total upper = U)
    (hNlt : N < L + Fintype.card (ItemType T) + 1)
    (hUlt : U < N + Fintype.card (ItemType T) + 1)
    (horder : ∀ t, lower.count t ≤ upper.count t)
    (hno :
      AppliedModelingLib.FiniteRounding.NoRoundingCrossingBetween
        (fun t : ItemType T => a.count t)
        (fun t : ItemType T => lower.count t)
        (fun t : ItemType T => upper.count t)) :
    ∀ t : ItemType T,
      lower.count t < a.count t + Fintype.card (ItemType T) + 1 ∧
        a.count t < upper.count t + Fintype.card (ItemType T) + 1 := by
  exact
    AppliedModelingLib.FiniteRounding.NoRoundingCrossingBetween.count_close
      (fun t : ItemType T => a.count t)
      (fun t : ItemType T => lower.count t)
      (fun t : ItemType T => upper.count t)
      ha hlower hupper hNlt hUlt horder hno

theorem count_le_card_of_no_rounding_crossing_between {T : ℕ}
    (a lower upper : CountAllocation T) {N L U : ℕ}
    (ha : AppliedModelingLib.Allocation.total a = N)
    (hlower : AppliedModelingLib.Allocation.total lower = L)
    (hupper : AppliedModelingLib.Allocation.total upper = U)
    (hNlt : N < L + Fintype.card (ItemType T) + 1)
    (hUlt : U < N + Fintype.card (ItemType T) + 1)
    (horder : ∀ t, lower.count t ≤ upper.count t)
    (hno :
      AppliedModelingLib.FiniteRounding.NoRoundingCrossingBetween
        (fun t : ItemType T => a.count t)
        (fun t : ItemType T => lower.count t)
        (fun t : ItemType T => upper.count t)) :
    ∀ t : ItemType T,
      lower.count t ≤ a.count t + Fintype.card (ItemType T) ∧
        a.count t ≤ upper.count t + Fintype.card (ItemType T) := by
  intro t
  exact
    AppliedModelingLib.FiniteRounding.NoRoundingCrossingBetween.count_le_close
      (fun t : ItemType T => a.count t)
      (fun t : ItemType T => lower.count t)
      (fun t : ItemType T => upper.count t)
      ha hlower hupper hNlt hUlt horder hno t

/--
Square-root profile approximation from the finite two-anchor rounding layer.

This is the reusable endpoint used by Proposition 2: once finite optimality
rules out a high/low rounding crossing and both integer anchors are uniformly
close to the square-root target, every optimum is close to that target with the
anchor error plus one cardinality error.
-/
theorem sqrt_profile_approx_of_no_rounding_crossing_between {T : ℕ}
    (likelihood : ItemType T → ℝ) (N : ℕ) {C : ℝ}
    (hNpos : 0 < N)
    (a lower upper : CountAllocation T) {L U : ℕ}
    (hnorm : (∑ i : ItemType T, Real.sqrt (likelihood i)) ≠ 0)
    (ha : AppliedModelingLib.Allocation.total a = N)
    (hlower : AppliedModelingLib.Allocation.total lower = L)
    (hupper : AppliedModelingLib.Allocation.total upper = U)
    (hNlt : N < L + Fintype.card (ItemType T) + 1)
    (hUlt : U < N + Fintype.card (ItemType T) + 1)
    (horder : ∀ t, lower.count t ≤ upper.count t)
    (hno :
      AppliedModelingLib.FiniteRounding.NoRoundingCrossingBetween
        (fun t : ItemType T => a.count t)
        (fun t : ItemType T => lower.count t)
        (fun t : ItemType T => upper.count t))
    (hlower_close :
      ∀ t,
        |((lower.count t : ℕ) : ℝ) - uniformSqrtTarget likelihood N t| < C)
    (hupper_close :
      ∀ t,
        |((upper.count t : ℕ) : ℝ) - uniformSqrtTarget likelihood N t| < C) :
    (sqrtLikelihoodProfile likelihood).Approx a
      ((C + (Fintype.card (ItemType T) : ℝ)) / (N : ℝ)) := by
  refine sqrtLikelihoodProfile.approx_of_count_abs_error
    likelihood a ha hNpos ?_
  intro t
  have hshare :=
    sqrtLikelihoodProfile.targetShare_eq likelihood t hnorm
  have htarget :
      (N : ℝ) * (sqrtLikelihoodProfile likelihood).targetShare t =
        uniformSqrtTarget likelihood N t := by
    unfold uniformSqrtTarget
    rw [hshare]
  rw [htarget]
  have hround :=
    count_le_card_of_no_rounding_crossing_between
      a lower upper ha hlower hupper hNlt hUlt horder hno t
  have hlower_t := hlower_close t
  have hupper_t := hupper_close t
  rw [abs_lt] at hlower_t hupper_t
  have hlower_bound :
      ((lower.count t : ℕ) : ℝ) ≤
        (a.count t : ℝ) + (Fintype.card (ItemType T) : ℝ) := by
    exact_mod_cast hround.1
  have hupper_bound :
      (a.count t : ℝ) ≤
        ((upper.count t : ℕ) : ℝ) + (Fintype.card (ItemType T) : ℝ) := by
    exact_mod_cast hround.2
  rw [abs_le]
  constructor <;> linarith
end UniformRounding

end PRPKG24AccuracyDiversity
