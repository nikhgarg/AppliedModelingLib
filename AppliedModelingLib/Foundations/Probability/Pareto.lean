import AppliedModelingLib.Foundations.Math.GammaAsymptotics
import AppliedModelingLib.Foundations.Math.BinomialBounds
import AppliedModelingLib.Foundations.Probability.OrderStatistics
import AppliedModelingLib.Foundations.Probability.RealDistribution
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Probability.Distributions.Pareto

/-!
# Pareto Distribution Helpers

Reusable wrappers around mathlib's Pareto distribution for finite iid samples.
-/

namespace AppliedModelingLib
namespace Probability
namespace Pareto

open MeasureTheory Set
open scoped ENNReal

/-- I.i.d. product measure for `q` draws from a Pareto distribution. -/
noncomputable def iidProductMeasure (t r : ℝ) (q : ℕ) :
    MeasureTheory.Measure (Fin q → ℝ) :=
  MeasureTheory.Measure.pi
    (fun _ : Fin q => ProbabilityTheory.paretoMeasure t r)

theorem isProbabilityMeasure_iidProductMeasure
    {t r : ℝ} (ht : 0 < t) (hr : 0 < r) (q : ℕ) :
    MeasureTheory.IsProbabilityMeasure (iidProductMeasure t r q) := by
  haveI : MeasureTheory.IsProbabilityMeasure
      (ProbabilityTheory.paretoMeasure t r) :=
    ProbabilityTheory.isProbabilityMeasure_paretoMeasure ht hr
  unfold iidProductMeasure
  infer_instance

/--
Closed-form upper-tail mass for mathlib's Pareto measure.

For scale `t` and shape `r`, the survival probability above any `x ≥ t` is
`t^r * x^(-r)`.
-/
theorem paretoMeasure_real_Ici_eq
    {t r x : ℝ} (ht : 0 < t) (hr : 0 < r) (hx : t ≤ x) :
    (ProbabilityTheory.paretoMeasure t r).real (Set.Ici x) =
      t ^ r * x ^ (-r) := by
  have hx_pos : 0 < x := lt_of_lt_of_le ht hx
  have hpdf :
      ∫⁻ y in Set.Ici x, ProbabilityTheory.paretoPDF t r y =
        ∫⁻ y in Set.Ici x,
          ENNReal.ofReal (r * t ^ r * y ^ (-(r + 1))) :=
    setLIntegral_congr_fun measurableSet_Ici
      (fun y hy => ProbabilityTheory.paretoPDF_of_le (le_trans hx hy))
  rw [ProbabilityTheory.paretoMeasure, measureReal_def,
    withDensity_apply _ measurableSet_Ici, hpdf,
    ← integral_eq_lintegral_of_nonneg_ae]
  · rw [integral_Ici_eq_integral_Ioi, integral_const_mul,
      integral_Ioi_rpow_of_lt (by linarith) hx_pos]
    have hden : -(r + 1) + 1 = -r := by ring
    rw [hden]
    field_simp [ne_of_gt hr]
  · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ici]
    filter_upwards with y hy
    positivity [lt_of_lt_of_le hx_pos hy]
  · fun_prop

/-- Scale-one specialization of `paretoMeasure_real_Ici_eq`. -/
theorem paretoMeasure_one_real_Ici_eq
    {r x : ℝ} (hr : 0 < r) (hx : 1 ≤ x) :
    (ProbabilityTheory.paretoMeasure 1 r).real (Set.Ici x) =
      x ^ (-r) := by
  simpa using
    paretoMeasure_real_Ici_eq (t := 1) (r := r) (x := x)
      (by norm_num) hr hx

/-- Closed-form strict upper-tail mass for mathlib's Pareto measure. -/
theorem paretoMeasure_real_Ioi_eq
    {t r x : ℝ} (ht : 0 < t) (hr : 0 < r) (hx : t ≤ x) :
    (ProbabilityTheory.paretoMeasure t r).real (Set.Ioi x) =
      t ^ r * x ^ (-r) := by
  have hx_pos : 0 < x := lt_of_lt_of_le ht hx
  have hpdf :
      ∫⁻ y in Set.Ioi x, ProbabilityTheory.paretoPDF t r y =
        ∫⁻ y in Set.Ioi x,
          ENNReal.ofReal (r * t ^ r * y ^ (-(r + 1))) :=
    setLIntegral_congr_fun measurableSet_Ioi
      (fun y hy => ProbabilityTheory.paretoPDF_of_le
        (le_trans hx (le_of_lt hy)))
  rw [ProbabilityTheory.paretoMeasure, measureReal_def,
    withDensity_apply _ measurableSet_Ioi, hpdf,
    ← integral_eq_lintegral_of_nonneg_ae]
  · rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hx_pos]
    have hden : -(r + 1) + 1 = -r := by ring
    rw [hden]
    field_simp [ne_of_gt hr]
  · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with y hy
    positivity [lt_trans hx_pos hy]
  · fun_prop

/-- Scale-one specialization of `paretoMeasure_real_Ioi_eq`. -/
theorem paretoMeasure_one_real_Ioi_eq
    {r x : ℝ} (hr : 0 < r) (hx : 1 ≤ x) :
    (ProbabilityTheory.paretoMeasure 1 r).real (Set.Ioi x) =
      x ^ (-r) := by
  simpa using
    paretoMeasure_real_Ioi_eq (t := 1) (r := r) (x := x)
      (by norm_num) hr hx

/--
Closed-form lower CDF mass for mathlib's Pareto measure, above the scale
parameter.
-/
theorem paretoMeasure_real_Iic_eq
    {t r x : ℝ} (ht : 0 < t) (hr : 0 < r) (hx : t ≤ x) :
    (ProbabilityTheory.paretoMeasure t r).real (Set.Iic x) =
      1 - t ^ r * x ^ (-r) := by
  haveI : MeasureTheory.IsProbabilityMeasure
      (ProbabilityTheory.paretoMeasure t r) :=
    ProbabilityTheory.isProbabilityMeasure_paretoMeasure ht hr
  have hcompl :=
    MeasureTheory.measureReal_compl
      (μ := ProbabilityTheory.paretoMeasure t r) (s := Set.Iic x)
      measurableSet_Iic
  have htail := paretoMeasure_real_Ioi_eq ht hr hx
  rw [compl_Iic, htail] at hcompl
  have huniv :
      (ProbabilityTheory.paretoMeasure t r).real Set.univ = 1 := by
    simp [Measure.real]
  rw [huniv] at hcompl
  linarith

/-- Scale-one specialization of `paretoMeasure_real_Iic_eq`. -/
theorem paretoMeasure_one_real_Iic_eq
    {r x : ℝ} (hr : 0 < r) (hx : 1 ≤ x) :
    (ProbabilityTheory.paretoMeasure 1 r).real (Set.Iic x) =
      1 - x ^ (-r) := by
  simpa using
    paretoMeasure_real_Iic_eq (t := 1) (r := r) (x := x)
      (by norm_num) hr hx

/-- Pareto mass below a threshold strictly below the scale is zero. -/
theorem paretoMeasure_real_Iic_eq_zero_of_lt
    {t r x : ℝ} (hx : x < t) :
    (ProbabilityTheory.paretoMeasure t r).real (Set.Iic x) = 0 := by
  have hbelow :
      ProbabilityTheory.paretoMeasure t r (Set.Iio t) = 0 := by
    rw [ProbabilityTheory.paretoMeasure,
      MeasureTheory.withDensity_apply _ measurableSet_Iio]
    exact ProbabilityTheory.lintegral_paretoPDF_of_le
      (t := t) (r := r) (x := t) (le_refl t)
  have hsubset : Set.Iic x ⊆ Set.Iio t := by
    intro y hy
    exact lt_of_le_of_lt hy hx
  have hzero :
      ProbabilityTheory.paretoMeasure t r (Set.Iic x) = 0 :=
    measure_mono_null hsubset hbelow
  simp [MeasureTheory.Measure.real, hzero]

/-- Scale-one specialization of `paretoMeasure_real_Iic_eq_zero_of_lt`. -/
theorem paretoMeasure_one_real_Iic_eq_zero_of_lt
    {r x : ℝ} (hx : x < 1) :
    (ProbabilityTheory.paretoMeasure 1 r).real (Set.Iic x) = 0 :=
  paretoMeasure_real_Iic_eq_zero_of_lt (t := 1) (r := r) (x := x) hx

/-- Pareto strict upper-tail mass is one below the scale parameter. -/
theorem paretoMeasure_real_Ioi_eq_one_of_lt
    {t r x : ℝ} (ht : 0 < t) (hr : 0 < r) (hx : x < t) :
    (ProbabilityTheory.paretoMeasure t r).real (Set.Ioi x) = 1 := by
  haveI : MeasureTheory.IsProbabilityMeasure
      (ProbabilityTheory.paretoMeasure t r) :=
    ProbabilityTheory.isProbabilityMeasure_paretoMeasure ht hr
  have hzero := paretoMeasure_real_Iic_eq_zero_of_lt
    (t := t) (r := r) (x := x) hx
  have hcompl :=
    MeasureTheory.measureReal_compl
      (μ := ProbabilityTheory.paretoMeasure t r) (s := Set.Iic x)
      measurableSet_Iic
  rw [compl_Iic, hzero, MeasureTheory.probReal_univ] at hcompl
  simpa using hcompl

/-- Scale-one specialization of `paretoMeasure_real_Ioi_eq_one_of_lt`. -/
theorem paretoMeasure_one_real_Ioi_eq_one_of_lt
    {r x : ℝ} (hr : 0 < r) (hx : x < 1) :
    (ProbabilityTheory.paretoMeasure 1 r).real (Set.Ioi x) = 1 :=
  paretoMeasure_real_Ioi_eq_one_of_lt
    (t := 1) (r := r) (x := x) (by norm_num) hr hx

/--
For iid Pareto samples, the number of coordinates strictly above a threshold
has the corresponding binomial mass.
-/
theorem iidProductMeasure_successCount_Ioi_eq_real
    {t r x : ℝ} (ht : 0 < t) (hr : 0 < r) (hx : t ≤ x)
    (q j : ℕ) :
    (iidProductMeasure t r q).real
        {sample : Fin q → ℝ | iidSuccessCount (Set.Ioi x) sample = j} =
      (Nat.choose q j : ℝ) *
        (t ^ r * x ^ (-r)) ^ j *
          (1 - t ^ r * x ^ (-r)) ^ (q - j) := by
  haveI : MeasureTheory.IsProbabilityMeasure
      (ProbabilityTheory.paretoMeasure t r) :=
    ProbabilityTheory.isProbabilityMeasure_paretoMeasure ht hr
  simpa [iidProductMeasure, paretoMeasure_real_Ioi_eq ht hr hx] using
    (iidProductMeasure_successCount_eq_real
      (μ := ProbabilityTheory.paretoMeasure t r)
      (n := q) (s := Set.Ioi x) measurableSet_Ioi j)

/--
For iid Pareto samples, the probability that at most `m` coordinates are
strictly above a threshold is the corresponding binomial tail sum.
-/
theorem iidProductMeasure_successCount_Ioi_le_real
    {t r x : ℝ} (ht : 0 < t) (hr : 0 < r) (hx : t ≤ x)
    (q m : ℕ) :
    (iidProductMeasure t r q).real
        {sample : Fin q → ℝ | iidSuccessCount (Set.Ioi x) sample ≤ m} =
      ∑ j ∈ Finset.Icc 0 (min m q),
        (Nat.choose q j : ℝ) *
          (t ^ r * x ^ (-r)) ^ j *
            (1 - t ^ r * x ^ (-r)) ^ (q - j) := by
  haveI : MeasureTheory.IsProbabilityMeasure
      (ProbabilityTheory.paretoMeasure t r) :=
    ProbabilityTheory.isProbabilityMeasure_paretoMeasure ht hr
  simpa [iidProductMeasure, paretoMeasure_real_Ioi_eq ht hr hx] using
    (iidProductMeasure_successCount_le_real
      (μ := ProbabilityTheory.paretoMeasure t r)
      (n := q) (s := Set.Ioi x) measurableSet_Ioi m)

/--
For iid Pareto samples, the survival probability of an upper order statistic is
the complement of the binomial lower tail for coordinates strictly above the
threshold.
-/
theorem iidProductMeasure_upperOrderStatistic_gt_real
    {t r x : ℝ} (ht : 0 < t) (hr : 0 < r) (hx : t ≤ x)
    {q : ℕ} (rankFromTop : Fin q) :
    (iidProductMeasure t r q).real
        {sample : Fin q → ℝ | x < upperOrderStatistic sample rankFromTop} =
      1 - ∑ j ∈ Finset.Icc 0 (min rankFromTop.val q),
        (Nat.choose q j : ℝ) *
          (t ^ r * x ^ (-r)) ^ j *
            (1 - t ^ r * x ^ (-r)) ^ (q - j) := by
  haveI : MeasureTheory.IsProbabilityMeasure (iidProductMeasure t r q) :=
    isProbabilityMeasure_iidProductMeasure ht hr q
  have hset :
      {sample : Fin q → ℝ | x < upperOrderStatistic sample rankFromTop} =
        {sample : Fin q → ℝ |
          iidSuccessCount (Set.Ioi x) sample ≤ rankFromTop.val}ᶜ := by
    ext sample
    simp [upperOrderStatistic_lt_iff_rank_lt_iidSuccessCount_Ioi]
  rw [hset,
    MeasureTheory.measureReal_compl
      (AppliedModelingLib.Probability.iidSuccessCount_le_measurableSet
        (n := q) measurableSet_Ioi rankFromTop.val),
    MeasureTheory.probReal_univ,
    iidProductMeasure_successCount_Ioi_le_real ht hr hx q rankFromTop.val]

/-- Scale-one specialization of `iidProductMeasure_upperOrderStatistic_gt_real`. -/
theorem iidProductMeasure_one_upperOrderStatistic_gt_real
    {r x : ℝ} (hr : 0 < r) (hx : 1 ≤ x)
    {q : ℕ} (rankFromTop : Fin q) :
    (iidProductMeasure 1 r q).real
        {sample : Fin q → ℝ | x < upperOrderStatistic sample rankFromTop} =
      1 - ∑ j ∈ Finset.Icc 0 (min rankFromTop.val q),
        (Nat.choose q j : ℝ) *
          (x ^ (-r)) ^ j *
            (1 - x ^ (-r)) ^ (q - j) := by
  simpa using
    iidProductMeasure_upperOrderStatistic_gt_real
      (t := 1) (r := r) (x := x) (by norm_num) hr hx rankFromTop

/--
Below the Pareto scale, every draw is strictly above the threshold almost
surely, hence every upper order statistic is above that threshold with
probability one.
-/
theorem iidProductMeasure_upperOrderStatistic_gt_real_of_lt_scale
    {t r x : ℝ} (ht : 0 < t) (hr : 0 < r) (hx : x < t)
    {q : ℕ} (rankFromTop : Fin q) :
    (iidProductMeasure t r q).real
        {sample : Fin q → ℝ | x < upperOrderStatistic sample rankFromTop} =
      1 := by
  haveI : MeasureTheory.IsProbabilityMeasure
      (ProbabilityTheory.paretoMeasure t r) :=
    ProbabilityTheory.isProbabilityMeasure_paretoMeasure ht hr
  haveI : MeasureTheory.IsProbabilityMeasure (iidProductMeasure t r q) :=
    isProbabilityMeasure_iidProductMeasure ht hr q
  let allAbove : Set (Fin q → ℝ) :=
    Set.pi Set.univ (fun _ : Fin q => Set.Ioi x)
  have hbase :
      (ProbabilityTheory.paretoMeasure t r).real (Set.Ioi x) = 1 :=
    paretoMeasure_real_Ioi_eq_one_of_lt ht hr hx
  have hall_real :
      (iidProductMeasure t r q).real allAbove = 1 := by
    have hall :
        iidProductMeasure t r q allAbove =
          ∏ _i : Fin q, ProbabilityTheory.paretoMeasure t r (Set.Ioi x) := by
      dsimp [iidProductMeasure, allAbove]
      rw [MeasureTheory.Measure.pi_pi]
    rw [MeasureTheory.Measure.real, hall, ENNReal.toReal_prod]
    calc
      ∏ _i : Fin q,
          (ProbabilityTheory.paretoMeasure t r (Set.Ioi x)).toReal =
          ∏ _i : Fin q, (1 : ℝ) := by
            refine Finset.prod_congr rfl ?_
            intro i _hi
            simpa [MeasureTheory.Measure.real] using hbase
      _ = 1 := by simp
  have hsubset :
      allAbove ⊆
        {sample : Fin q → ℝ | x < upperOrderStatistic sample rankFromTop} := by
    intro sample hsample
    have hcount :
        rankFromTop.val < iidSuccessCount (Set.Ioi x) sample := by
      have hindex :
          iidSuccessIndexSet (Set.Ioi x) sample = Finset.univ := by
        ext i
        simp [iidSuccessIndexSet, allAbove] at hsample ⊢
        exact hsample i
      simp [iidSuccessCount, hindex, rankFromTop.isLt]
    exact
      (upperOrderStatistic_lt_iff_rank_lt_iidSuccessCount_Ioi
        sample rankFromTop x).2 hcount
  have hlower :
      1 ≤ (iidProductMeasure t r q).real
          {sample : Fin q → ℝ | x < upperOrderStatistic sample rankFromTop} := by
    rw [← hall_real]
    exact MeasureTheory.measureReal_mono (μ := iidProductMeasure t r q) hsubset
  have hupper :
      (iidProductMeasure t r q).real
          {sample : Fin q → ℝ | x < upperOrderStatistic sample rankFromTop} ≤ 1 := by
    rw [← MeasureTheory.probReal_univ (μ := iidProductMeasure t r q)]
    exact MeasureTheory.measureReal_mono
      (μ := iidProductMeasure t r q) (Set.subset_univ _)
  exact le_antisymm hupper hlower

/-- Scale-one specialization of `iidProductMeasure_upperOrderStatistic_gt_real_of_lt_scale`. -/
theorem iidProductMeasure_one_upperOrderStatistic_gt_real_of_lt_one
    {r x : ℝ} (hr : 0 < r) (hx : x < 1)
    {q : ℕ} (rankFromTop : Fin q) :
    (iidProductMeasure 1 r q).real
        {sample : Fin q → ℝ | x < upperOrderStatistic sample rankFromTop} =
      1 :=
  iidProductMeasure_upperOrderStatistic_gt_real_of_lt_scale
    (t := 1) (r := r) (x := x) (by norm_num) hr hx rankFromTop

/--
Below the scale-one Pareto support, the upper-order-statistic tail integrand is
identically one, so its contribution over `(0, 1)` is exactly one.
-/
theorem iidProductMeasure_one_upperOrderStatistic_tail_integral_Ioo_zero_one
    {r : ℝ} (hr : 0 < r) {q : ℕ} (rankFromTop : Fin q) :
    ∫ x in Set.Ioo (0 : ℝ) 1,
        (iidProductMeasure 1 r q).real
          {sample : Fin q → ℝ | x < upperOrderStatistic sample rankFromTop} =
      1 := by
  calc
    ∫ x in Set.Ioo (0 : ℝ) 1,
        (iidProductMeasure 1 r q).real
          {sample : Fin q → ℝ | x < upperOrderStatistic sample rankFromTop}
        = ∫ _x in Set.Ioo (0 : ℝ) 1, (1 : ℝ) := by
          refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo ?_
          intro x hx
          exact iidProductMeasure_one_upperOrderStatistic_gt_real_of_lt_one
            hr hx.2 rankFromTop
    _ = 1 := by
          rw [MeasureTheory.setIntegral_const]
          simp

/--
Above the scale-one Pareto support, the upper-order-statistic survival integral
reduces pointwise to the binomial tail formula.
-/
theorem iidProductMeasure_one_upperOrderStatistic_tail_integral_Ioi_one
    {r : ℝ} (hr : 0 < r) {q : ℕ} (rankFromTop : Fin q) :
    ∫ x in Set.Ioi (1 : ℝ),
        (iidProductMeasure 1 r q).real
          {sample : Fin q → ℝ | x < upperOrderStatistic sample rankFromTop} =
      ∫ x in Set.Ioi (1 : ℝ),
        1 - ∑ j ∈ Finset.Icc 0 (min rankFromTop.val q),
          (Nat.choose q j : ℝ) *
            (x ^ (-r)) ^ j *
              (1 - x ^ (-r)) ^ (q - j) := by
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
  intro x hx
  exact iidProductMeasure_one_upperOrderStatistic_gt_real
    hr (le_of_lt hx) rankFromTop

/--
Scale-one iid Pareto upper-order-statistic survival as an upper binomial tail.

This is the integrable form of the tail probability over `(1,∞)`.
-/
theorem iidProductMeasure_one_upperOrderStatistic_gt_real_upper_tail
    {r x : ℝ} (hr : 0 < r) (hx : 1 ≤ x)
    {q : ℕ} (rankFromTop : Fin q) :
    (iidProductMeasure 1 r q).real
        {sample : Fin q → ℝ | x < upperOrderStatistic sample rankFromTop} =
      ∑ j ∈ Finset.Icc (rankFromTop.val + 1) q,
        (Nat.choose q j : ℝ) *
          (x ^ (-r)) ^ j *
            (1 - x ^ (-r)) ^ (q - j) := by
  rw [iidProductMeasure_one_upperOrderStatistic_gt_real hr hx rankFromTop]
  have hmin : min rankFromTop.val q = rankFromTop.val :=
    min_eq_left (Nat.le_of_lt rankFromTop.isLt)
  simpa [hmin] using
    AppliedModelingLib.FiniteSum.binomial_lower_tail_complement_eq_upper_tail
      rankFromTop.isLt (x ^ (-r))

/--
Above the scale-one Pareto support, the upper-order-statistic survival integral
is the integral of the upper binomial tail.
-/
theorem iidProductMeasure_one_upperOrderStatistic_tail_integral_Ioi_one_upper_tail
    {r : ℝ} (hr : 0 < r) {q : ℕ} (rankFromTop : Fin q) :
    ∫ x in Set.Ioi (1 : ℝ),
        (iidProductMeasure 1 r q).real
          {sample : Fin q → ℝ | x < upperOrderStatistic sample rankFromTop} =
      ∫ x in Set.Ioi (1 : ℝ),
        ∑ j ∈ Finset.Icc (rankFromTop.val + 1) q,
          (Nat.choose q j : ℝ) *
            (x ^ (-r)) ^ j *
              (1 - x ^ (-r)) ^ (q - j) := by
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
  intro x hx
  exact iidProductMeasure_one_upperOrderStatistic_gt_real_upper_tail
    hr (le_of_lt hx) rankFromTop

/-- The map `x ↦ x ^ (-α)` sends the Pareto tail `(1, ∞)` onto `(0, 1)`. -/
theorem rpow_neg_image_Ioi_one
    {α : ℝ} (hα : 0 < α) :
    (fun x : ℝ => x ^ (-α)) '' Set.Ioi (1 : ℝ) = Set.Ioo (0 : ℝ) 1 := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨Real.rpow_pos_of_pos (lt_trans zero_lt_one hx) (-α),
      Real.rpow_lt_one_of_one_lt_of_neg hx (neg_neg_of_pos hα)⟩
  · intro hy
    refine ⟨y ^ ((-α)⁻¹), ?_, ?_⟩
    · exact Real.one_lt_rpow_of_pos_of_lt_one_of_neg hy.1 hy.2
        (inv_lt_zero.mpr (neg_neg_of_pos hα))
    · change (y ^ ((-α)⁻¹)) ^ (-α) = y
      exact Real.rpow_inv_rpow (le_of_lt hy.1) (by linarith)

/--
Pareto kernel integral as a beta integral under the substitution
`y = x ^ (-α)`.

This is the reusable analytic checkpoint behind fixed-rank Pareto
order-statistic expectations.
-/
theorem paretoKernelIntegral_eq_beta
    {α : ℝ} (hα : 1 < α) {q j : ℕ} (hj : 1 ≤ j) :
    ∫ x in Set.Ioi (1 : ℝ),
        (x ^ (-α)) ^ j * (1 - x ^ (-α)) ^ (q - j)
      =
      (1 / α) *
        ProbabilityTheory.beta
          ((j : ℝ) - 1 / α)
          (((q - j : ℕ) : ℝ) + 1) := by
  let a : ℝ := (j : ℝ) - 1 / α
  let b : ℝ := (((q - j : ℕ) : ℝ) + 1)
  let g : ℝ → ℝ := fun y => (1 / α) * y ^ (a - 1) * (1 - y) ^ (b - 1)
  have hα_pos : 0 < α := lt_trans zero_lt_one hα
  have ha : 0 < a := by
    have hinv_lt_one : 1 / α < 1 := by
      rw [div_lt_one hα_pos]
      exact hα
    have hj_real : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    dsimp [a]
    linarith
  have hb : 0 < b := by
    dsimp [b]
    positivity
  have hderiv :
      ∀ x ∈ Set.Ioi (1 : ℝ),
        HasDerivWithinAt
          (fun t : ℝ => t ^ (-α))
          ((-α) * x ^ (-α - 1))
          (Set.Ioi (1 : ℝ)) x := by
    intro x hx
    exact (Real.hasDerivAt_rpow_const
      (Or.inl (ne_of_gt (lt_trans zero_lt_one hx)))).hasDerivWithinAt
  have hanti :
      AntitoneOn (fun x : ℝ => x ^ (-α)) (Set.Ioi (1 : ℝ)) := by
    exact (Real.strictAntiOn_rpow_Ioi_of_exponent_neg
      (neg_neg_of_pos hα_pos)).antitoneOn.mono
        (fun x hx => by simpa using lt_trans zero_lt_one hx)
  have hsubst :=
    MeasureTheory.integral_image_eq_integral_deriv_smul_of_antitoneOn
      (s := Set.Ioi (1 : ℝ)) (f := fun x : ℝ => x ^ (-α))
      (f' := fun x : ℝ => (-α) * x ^ (-α - 1))
      measurableSet_Ioi hderiv hanti g
  have hbeta :
      ∫ y in Set.Ioo (0 : ℝ) 1, y ^ (a - 1) * (1 - y) ^ (b - 1) =
        ProbabilityTheory.beta a b :=
    AppliedModelingLib.Math.integral_Ioo_zero_one_rpow_mul_one_sub_rpow_eq_beta ha hb
  have hleft :
      ∫ y in Set.Ioo (0 : ℝ) 1, g y =
        (1 / α) * ProbabilityTheory.beta a b := by
    simp [g, MeasureTheory.integral_const_mul, hbeta, mul_assoc]
  have hsubst' :
      ∫ y in Set.Ioo (0 : ℝ) 1, g y =
        ∫ x in Set.Ioi (1 : ℝ),
          (-((-α) * x ^ (-α - 1))) • g (x ^ (-α)) := by
    simpa [rpow_neg_image_Ioi_one hα_pos] using hsubst
  rw [hleft] at hsubst'
  rw [hsubst']
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
  intro x hx
  have hx_pos : 0 < x := lt_trans zero_lt_one hx
  have hx_nonneg : 0 ≤ x := le_of_lt hx_pos
  have hxpow_pos : 0 < x ^ (-α) := Real.rpow_pos_of_pos hx_pos (-α)
  have hpow :
      ((x ^ (-α)) ^ (a - 1)) =
        x ^ (α + 1 - α * (j : ℝ)) := by
    rw [← Real.rpow_mul hx_nonneg]
    dsimp [a]
    congr 1
    field_simp [ne_of_gt hα_pos]
    ring
  have hjac :
      α * (x ^ (-α - 1) * (α⁻¹ * (x ^ (-α)) ^ (a - 1))) =
        (x ^ (-α)) ^ j := by
    rw [hpow]
    calc
      α * (x ^ (-α - 1) * (α⁻¹ * x ^ (α + 1 - α * (j : ℝ))))
          = x ^ (-α - 1) * x ^ (α + 1 - α * (j : ℝ)) := by
              field_simp [ne_of_gt hα_pos]
      _ = x ^ ((-α - 1) + (α + 1 - α * (j : ℝ))) := by
              rw [← Real.rpow_add hx_pos]
      _ = x ^ ((-α) * (j : ℝ)) := by
              congr 1
              ring
      _ = (x ^ (-α)) ^ (j : ℝ) := by
              rw [Real.rpow_mul hx_nonneg]
      _ = (x ^ (-α)) ^ j := by
              rw [Real.rpow_natCast]
  dsimp [g]
  simp [b, one_div]
  calc
    (x ^ (-α)) ^ j * (1 - x ^ (-α)) ^ (q - j)
        =
        (α * (x ^ (-α - 1) *
          (α⁻¹ * (x ^ (-α)) ^ (a - 1)))) *
            (1 - x ^ (-α)) ^ (q - j) := by
          rw [hjac]
    _ = α * x ^ (-α - 1) *
        (α⁻¹ * (x ^ (-α)) ^ (a - 1) *
          (1 - x ^ (-α)) ^ (q - j)) := by
          ring

/--
The Pareto beta-kernel is integrable on the scale-one tail `(1, ∞)`.

This is the integrability side of `paretoKernelIntegral_eq_beta`, exposed so
finite upper-tail sums can be exchanged with integrals.
-/
theorem paretoKernelIntegrableOn_Ioi_one
    {α : ℝ} (hα : 1 < α) {q j : ℕ} (hj : 1 ≤ j) :
    IntegrableOn
      (fun x : ℝ => (x ^ (-α)) ^ j * (1 - x ^ (-α)) ^ (q - j))
      (Set.Ioi (1 : ℝ)) := by
  let a : ℝ := (j : ℝ) - 1 / α
  let b : ℝ := (((q - j : ℕ) : ℝ) + 1)
  let g : ℝ → ℝ := fun y => (1 / α) * y ^ (a - 1) * (1 - y) ^ (b - 1)
  have hα_pos : 0 < α := lt_trans zero_lt_one hα
  have ha : 0 < a := by
    have hinv_lt_one : 1 / α < 1 := by
      rw [div_lt_one hα_pos]
      exact hα
    have hj_real : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    dsimp [a]
    linarith
  have hb : 0 < b := by
    dsimp [b]
    positivity
  have hderiv :
      ∀ x ∈ Set.Ioi (1 : ℝ),
        HasDerivWithinAt
          (fun t : ℝ => t ^ (-α))
          ((-α) * x ^ (-α - 1))
          (Set.Ioi (1 : ℝ)) x := by
    intro x hx
    exact (Real.hasDerivAt_rpow_const
      (Or.inl (ne_of_gt (lt_trans zero_lt_one hx)))).hasDerivWithinAt
  have hanti :
      AntitoneOn (fun x : ℝ => x ^ (-α)) (Set.Ioi (1 : ℝ)) := by
    exact (Real.strictAntiOn_rpow_Ioi_of_exponent_neg
      (neg_neg_of_pos hα_pos)).antitoneOn.mono
        (fun x hx => by simpa using lt_trans zero_lt_one hx)
  have hbeta_int :
      IntegrableOn
        (fun y : ℝ => y ^ (a - 1) * (1 - y) ^ (b - 1))
        (Set.Ioo (0 : ℝ) 1) :=
    AppliedModelingLib.Math.integrableOn_Ioo_zero_one_rpow_mul_one_sub_rpow ha hb
  have hg :
      IntegrableOn g (Set.Ioo (0 : ℝ) 1) := by
    simpa [g, mul_assoc] using hbeta_int.const_mul (1 / α)
  have hg_image :
      IntegrableOn g
        ((fun x : ℝ => x ^ (-α)) '' Set.Ioi (1 : ℝ)) := by
    simpa [rpow_neg_image_Ioi_one hα_pos] using hg
  have hpull :
      IntegrableOn
        (fun x : ℝ =>
          (-((-α) * x ^ (-α - 1))) • g (x ^ (-α)))
        (Set.Ioi (1 : ℝ)) :=
    (MeasureTheory.integrableOn_image_iff_integrableOn_deriv_smul_of_antitoneOn
      (s := Set.Ioi (1 : ℝ)) (f := fun x : ℝ => x ^ (-α))
      (f' := fun x : ℝ => (-α) * x ^ (-α - 1))
      measurableSet_Ioi hderiv hanti g).1 hg_image
  refine hpull.congr_fun ?_ measurableSet_Ioi
  intro x hx
  have hx_pos : 0 < x := lt_trans zero_lt_one hx
  have hx_nonneg : 0 ≤ x := le_of_lt hx_pos
  have hpow :
      ((x ^ (-α)) ^ (a - 1)) =
        x ^ (α + 1 - α * (j : ℝ)) := by
    rw [← Real.rpow_mul hx_nonneg]
    dsimp [a]
    congr 1
    field_simp [ne_of_gt hα_pos]
    ring
  have hjac :
      α * (x ^ (-α - 1) * (α⁻¹ * (x ^ (-α)) ^ (a - 1))) =
        (x ^ (-α)) ^ j := by
    rw [hpow]
    calc
      α * (x ^ (-α - 1) * (α⁻¹ * x ^ (α + 1 - α * (j : ℝ))))
          = x ^ (-α - 1) * x ^ (α + 1 - α * (j : ℝ)) := by
              field_simp [ne_of_gt hα_pos]
      _ = x ^ ((-α - 1) + (α + 1 - α * (j : ℝ))) := by
              rw [← Real.rpow_add hx_pos]
      _ = x ^ ((-α) * (j : ℝ)) := by
              congr 1
              ring
      _ = (x ^ (-α)) ^ (j : ℝ) := by
              rw [Real.rpow_mul hx_nonneg]
      _ = (x ^ (-α)) ^ j := by
              rw [Real.rpow_natCast]
  dsimp [g]
  simp [b, one_div]
  calc
    α * x ^ (-α - 1) *
        (α⁻¹ * (x ^ (-α)) ^ (a - 1) *
          (1 - x ^ (-α)) ^ (q - j))
        =
        (α * (x ^ (-α - 1) *
          (α⁻¹ * (x ^ (-α)) ^ (a - 1)))) *
            (1 - x ^ (-α)) ^ (q - j) := by
          ring
    _ = (x ^ (-α)) ^ j * (1 - x ^ (-α)) ^ (q - j) := by
          rw [hjac]

/--
Finite-product form of the Pareto beta-kernel integral when the second beta
parameter is a natural shift.
-/
theorem paretoKernelIntegral_eq_beta_product
    {α : ℝ} (hα : 1 < α) {q j : ℕ} (hj : 1 ≤ j) :
    ∫ x in Set.Ioi (1 : ℝ),
        (x ^ (-α)) ^ j * (1 - x ^ (-α)) ^ (q - j)
      =
      (1 / α) *
        ((Nat.factorial (q - j) : ℝ) /
          ∏ m ∈ Finset.range (q - j + 1),
            ((j : ℝ) - 1 / α + m)) := by
  have hα_pos : 0 < α := lt_trans zero_lt_one hα
  have ha : 0 < (j : ℝ) - 1 / α := by
    have hinv_lt_one : 1 / α < 1 := by
      rw [div_lt_one hα_pos]
      exact hα
    have hj_real : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    linarith
  rw [paretoKernelIntegral_eq_beta hα hj,
    AppliedModelingLib.Math.beta_nat_add_one_right_real ha (q - j)]

/--
Exchange the finite upper binomial-tail sum with the Pareto tail integral.
-/
theorem paretoUpperTailIntegral_eq_sum_kernel_integrals
    {α : ℝ} (hα : 1 < α) {q : ℕ} (rankFromTop : Fin q) :
    ∫ x in Set.Ioi (1 : ℝ),
        ∑ j ∈ Finset.Icc (rankFromTop.val + 1) q,
          (Nat.choose q j : ℝ) *
            (x ^ (-α)) ^ j *
              (1 - x ^ (-α)) ^ (q - j)
      =
      ∑ j ∈ Finset.Icc (rankFromTop.val + 1) q,
        (Nat.choose q j : ℝ) *
          ∫ x in Set.Ioi (1 : ℝ),
            (x ^ (-α)) ^ j * (1 - x ^ (-α)) ^ (q - j) := by
  calc
    ∫ x in Set.Ioi (1 : ℝ),
        ∑ j ∈ Finset.Icc (rankFromTop.val + 1) q,
          (Nat.choose q j : ℝ) *
            (x ^ (-α)) ^ j *
              (1 - x ^ (-α)) ^ (q - j)
        =
        ∫ x in Set.Ioi (1 : ℝ),
          ∑ j ∈ Finset.Icc (rankFromTop.val + 1) q,
            (Nat.choose q j : ℝ) *
              ((x ^ (-α)) ^ j *
                (1 - x ^ (-α)) ^ (q - j)) := by
          refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
          intro x hx
          refine Finset.sum_congr rfl ?_
          intro j hj
          ring
    _ =
        ∑ j ∈ Finset.Icc (rankFromTop.val + 1) q,
          ∫ x in Set.Ioi (1 : ℝ),
            (Nat.choose q j : ℝ) *
              ((x ^ (-α)) ^ j *
                (1 - x ^ (-α)) ^ (q - j)) := by
          exact MeasureTheory.integral_finset_sum
            (Finset.Icc (rankFromTop.val + 1) q)
            (fun j hj =>
              (paretoKernelIntegrableOn_Ioi_one
                (α := α) (q := q) (j := j) hα
                (by
                  have hj_lower := (Finset.mem_Icc.mp hj).1
                  omega : 1 ≤ j)).const_mul (Nat.choose q j : ℝ))
    _ =
        ∑ j ∈ Finset.Icc (rankFromTop.val + 1) q,
          ∫ x in Set.Ioi (1 : ℝ),
            (Nat.choose q j : ℝ) *
              (x ^ (-α)) ^ j *
                (1 - x ^ (-α)) ^ (q - j) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
          intro x hx
          ring
    _ =
        ∑ j ∈ Finset.Icc (rankFromTop.val + 1) q,
          (Nat.choose q j : ℝ) *
            ∫ x in Set.Ioi (1 : ℝ),
              (x ^ (-α)) ^ j * (1 - x ^ (-α)) ^ (q - j) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          calc
            ∫ x in Set.Ioi (1 : ℝ),
              (Nat.choose q j : ℝ) *
                (x ^ (-α)) ^ j *
                  (1 - x ^ (-α)) ^ (q - j)
                =
                ∫ x in Set.Ioi (1 : ℝ),
                  (Nat.choose q j : ℝ) *
                    ((x ^ (-α)) ^ j *
                      (1 - x ^ (-α)) ^ (q - j)) := by
                  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
                  intro x hx
                  ring
            _ =
                (Nat.choose q j : ℝ) *
                  ∫ x in Set.Ioi (1 : ℝ),
                    (x ^ (-α)) ^ j *
                      (1 - x ^ (-α)) ^ (q - j) := by
                  rw [MeasureTheory.integral_const_mul]

/--
Closed beta-sum form of the scale-one Pareto upper-order-statistic tail
integral over `(1, ∞)`.
-/
theorem iidProductMeasure_one_upperOrderStatistic_tail_integral_Ioi_one_eq_beta_sum
    {α : ℝ} (hα : 1 < α) {q : ℕ} (rankFromTop : Fin q) :
    ∫ x in Set.Ioi (1 : ℝ),
        (iidProductMeasure 1 α q).real
          {sample : Fin q → ℝ | x < upperOrderStatistic sample rankFromTop} =
      ∑ j ∈ Finset.Icc (rankFromTop.val + 1) q,
        (Nat.choose q j : ℝ) *
          ((1 / α) *
            ProbabilityTheory.beta
              ((j : ℝ) - 1 / α)
              (((q - j : ℕ) : ℝ) + 1)) := by
  rw [iidProductMeasure_one_upperOrderStatistic_tail_integral_Ioi_one_upper_tail
      (lt_trans zero_lt_one hα) rankFromTop,
    paretoUpperTailIntegral_eq_sum_kernel_integrals hα rankFromTop]
  refine Finset.sum_congr rfl ?_
  intro j hj
  rw [paretoKernelIntegral_eq_beta hα
    (by
      have hj_lower := (Finset.mem_Icc.mp hj).1
      omega : 1 ≤ j)]

/-- Scale-one Pareto samples are nonnegative almost surely. -/
theorem paretoMeasure_one_nonnegative_ae
    {α : ℝ} (hα : 0 < α) :
    (fun _ : ℝ => (0 : ℝ)) ≤ᵐ[
      ProbabilityTheory.paretoMeasure 1 α] fun x => x := by
  haveI : MeasureTheory.IsProbabilityMeasure
      (ProbabilityTheory.paretoMeasure 1 α) :=
    ProbabilityTheory.isProbabilityMeasure_paretoMeasure
      (by norm_num) hα
  have hzero_real :
      (ProbabilityTheory.paretoMeasure 1 α).real (Set.Iic (0 : ℝ)) = 0 :=
    paretoMeasure_one_real_Iic_eq_zero_of_lt (r := α) (x := 0)
      (by norm_num)
  have hzero :
      ProbabilityTheory.paretoMeasure 1 α (Set.Iic (0 : ℝ)) = 0 :=
    (MeasureTheory.measureReal_eq_zero_iff
      (μ := ProbabilityTheory.paretoMeasure 1 α)
      (s := Set.Iic (0 : ℝ))).1 hzero_real
  rw [Filter.EventuallyLE, ae_iff]
  refine measure_mono_null ?_ hzero
  intro x hx
  exact le_of_lt (lt_of_not_ge hx)

/-- Every coordinate in a scale-one iid Pareto sample is nonnegative a.s. -/
theorem iidProductMeasure_one_all_nonnegative_ae
    {α : ℝ} (hα : 0 < α) (q : ℕ) :
    ∀ᵐ sample ∂iidProductMeasure 1 α q,
      ∀ i : Fin q, 0 ≤ sample i := by
  haveI : MeasureTheory.IsProbabilityMeasure
      (ProbabilityTheory.paretoMeasure 1 α) :=
    ProbabilityTheory.isProbabilityMeasure_paretoMeasure
      (by norm_num) hα
  have hbase :
      ∀ i : Fin q,
        (fun _ : ℝ => (0 : ℝ)) ≤ᵐ[
          ProbabilityTheory.paretoMeasure 1 α] fun x => x :=
    fun _ => paretoMeasure_one_nonnegative_ae hα
  have hpi :
      (fun _sample : Fin q → ℝ => fun _i : Fin q => (0 : ℝ)) ≤ᵐ[
        iidProductMeasure 1 α q] fun sample => sample := by
    simpa [iidProductMeasure] using
      MeasureTheory.Measure.ae_le_pi
        (μ := fun _ : Fin q => ProbabilityTheory.paretoMeasure 1 α)
        hbase
  filter_upwards [hpi] with sample hsample i
  exact hsample i

/-- Scale-one iid Pareto upper order statistics are nonnegative a.s. -/
theorem iidProductMeasure_one_upperOrderStatistic_nonnegative_ae
    {α : ℝ} (hα : 0 < α) {q : ℕ} (rankFromTop : Fin q) :
    (fun _sample : Fin q → ℝ => (0 : ℝ)) ≤ᵐ[
      iidProductMeasure 1 α q]
      fun sample => upperOrderStatistic sample rankFromTop := by
  filter_upwards [iidProductMeasure_one_all_nonnegative_ae hα q]
    with sample hsample
  exact le_upperOrderStatistic_of_forall_le hsample rankFromTop

/--
The Pareto upper-order-statistic survival function is integrable over the
scale-one tail `(1, ∞)`.
-/
theorem iidProductMeasure_one_upperOrderStatistic_tail_integrableOn_Ioi_one
    {α : ℝ} (hα : 1 < α) {q : ℕ} (rankFromTop : Fin q) :
    IntegrableOn
      (fun x : ℝ =>
        (iidProductMeasure 1 α q).real
          {sample : Fin q → ℝ | x < upperOrderStatistic sample rankFromTop})
      (Set.Ioi (1 : ℝ)) := by
  have hsum_int :
      IntegrableOn
        (fun x : ℝ =>
          ∑ j ∈ Finset.Icc (rankFromTop.val + 1) q,
            (Nat.choose q j : ℝ) *
              ((x ^ (-α)) ^ j *
                (1 - x ^ (-α)) ^ (q - j)))
        (Set.Ioi (1 : ℝ)) := by
    exact MeasureTheory.integrable_finset_sum
      (Finset.Icc (rankFromTop.val + 1) q)
      (fun j hj =>
        (paretoKernelIntegrableOn_Ioi_one
          (α := α) (q := q) (j := j) hα
          (by
            have hj_lower := (Finset.mem_Icc.mp hj).1
            omega : 1 ≤ j)).const_mul (Nat.choose q j : ℝ))
  refine hsum_int.congr_fun ?_ measurableSet_Ioi
  intro x hx
  calc
    (∑ j ∈ Finset.Icc (rankFromTop.val + 1) q,
      (Nat.choose q j : ℝ) *
        ((x ^ (-α)) ^ j * (1 - x ^ (-α)) ^ (q - j)))
        =
        ∑ j ∈ Finset.Icc (rankFromTop.val + 1) q,
          (Nat.choose q j : ℝ) *
            (x ^ (-α)) ^ j *
              (1 - x ^ (-α)) ^ (q - j) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          ring
    _ =
        (iidProductMeasure 1 α q).real
          {sample : Fin q → ℝ | x < upperOrderStatistic sample rankFromTop} :=
      (iidProductMeasure_one_upperOrderStatistic_gt_real_upper_tail
        (lt_trans zero_lt_one hα) (le_of_lt hx) rankFromTop).symm

/--
The Pareto upper-order-statistic survival function is integrable over
`(0, ∞)`.
-/
theorem iidProductMeasure_one_upperOrderStatistic_tail_integrableOn_Ioi_zero
    {α : ℝ} (hα : 1 < α) {q : ℕ} (rankFromTop : Fin q) :
    IntegrableOn
      (fun x : ℝ =>
        (iidProductMeasure 1 α q).real
          {sample : Fin q → ℝ | x < upperOrderStatistic sample rankFromTop})
      (Set.Ioi (0 : ℝ)) := by
  let tail : ℝ → ℝ := fun x =>
    (iidProductMeasure 1 α q).real
      {sample : Fin q → ℝ | x < upperOrderStatistic sample rankFromTop}
  have hbelow_Ioo : IntegrableOn tail (Set.Ioo (0 : ℝ) 1) := by
    have hconst : IntegrableOn (fun _x : ℝ => (1 : ℝ))
        (Set.Ioo (0 : ℝ) 1) :=
      integrableOn_const (by simp)
    refine hconst.congr_fun ?_ measurableSet_Ioo
    intro x hx
    dsimp [tail]
    exact (iidProductMeasure_one_upperOrderStatistic_gt_real_of_lt_one
      (lt_trans zero_lt_one hα) hx.2 rankFromTop).symm
  have hbelow_Ioc : IntegrableOn tail (Set.Ioc (0 : ℝ) 1) :=
    (integrableOn_Ioc_iff_integrableOn_Ioo
      (μ := MeasureTheory.volume) (f := tail) (a := 0) (b := 1)).2
      hbelow_Ioo
  have habove_Ioi : IntegrableOn tail (Set.Ioi (1 : ℝ)) :=
    iidProductMeasure_one_upperOrderStatistic_tail_integrableOn_Ioi_one
      hα rankFromTop
  have hunion : IntegrableOn tail (Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ)) :=
    hbelow_Ioc.union habove_Ioi
  simpa [tail, Set.Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1)]
    using hunion

/-- Scale-one iid Pareto upper order statistics are integrable for `α > 1`. -/
theorem iidProductMeasure_one_upperOrderStatistic_integrable
    {α : ℝ} (hα : 1 < α) {q : ℕ} (rankFromTop : Fin q) :
    MeasureTheory.Integrable
      (fun sample : Fin q → ℝ => upperOrderStatistic sample rankFromTop)
      (iidProductMeasure 1 α q) := by
  let μ := iidProductMeasure 1 α q
  haveI : MeasureTheory.IsProbabilityMeasure μ := by
    simpa [μ] using
      isProbabilityMeasure_iidProductMeasure
        (t := 1) (r := α) (by norm_num) (lt_trans zero_lt_one hα) q
  have h_nonneg :
      (fun _sample : Fin q → ℝ => (0 : ℝ)) ≤ᵐ[μ]
        fun sample => upperOrderStatistic sample rankFromTop := by
    simpa [μ] using
      iidProductMeasure_one_upperOrderStatistic_nonnegative_ae
        (lt_trans zero_lt_one hα) rankFromTop
  have h_layer :=
    MeasureTheory.lintegral_eq_lintegral_meas_lt (μ := μ)
      h_nonneg (upperOrderStatistic_measurable rankFromTop).aemeasurable
  let tailSet : ℝ → Set (Fin q → ℝ) :=
    fun x => {sample : Fin q → ℝ | x < upperOrderStatistic sample rankFromTop}
  have h_tail_int : MeasureTheory.Integrable
      (fun x : ℝ => μ.real (tailSet x))
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    simpa [μ, tailSet, IntegrableOn] using
      iidProductMeasure_one_upperOrderStatistic_tail_integrableOn_Ioi_zero
        hα rankFromTop
  have h_tail_lintegral :
      (∫⁻ x, (μ (tailSet x))
        ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))) < ∞ := by
    calc
      ∫⁻ x, (μ (tailSet x))
          ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
        = ∫⁻ x, ENNReal.ofReal (μ.real (tailSet x))
            ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
            refine MeasureTheory.lintegral_congr_ae ?_
            filter_upwards with x
            rw [MeasureTheory.ofReal_measureReal
              (μ := μ) (s := tailSet x) (h := measure_ne_top μ (tailSet x))]
      _ < ∞ := MeasureTheory.Integrable.lintegral_lt_top h_tail_int
  have h_lintegral :
      (∫⁻ sample, ENNReal.ofReal (upperOrderStatistic sample rankFromTop) ∂μ) < ∞ := by
    simpa [μ, tailSet] using h_layer.trans_lt h_tail_lintegral
  exact (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
    (upperOrderStatistic_measurable rankFromTop).aestronglyMeasurable
    h_nonneg).1 h_lintegral.ne

/--
Expected scale-one iid Pareto upper order statistic in gamma-ratio form.
-/
theorem iidProductMeasure_one_expectedUpperOrderStatistic_eq_gamma_ratio
    {α : ℝ} (hα : 1 < α) {q : ℕ} (rankFromTop : Fin q) :
    expectedUpperOrderStatistic (iidProductMeasure 1 α q) rankFromTop =
      (Real.Gamma ((rankFromTop.val : ℝ) + 1 - 1 / α) /
          Real.Gamma ((rankFromTop.val : ℝ) + 1)) *
        (Real.Gamma ((q : ℝ) + 1) /
          Real.Gamma ((q : ℝ) + 1 - 1 / α)) := by
  let tail : ℝ → ℝ := fun x =>
    (iidProductMeasure 1 α q).real
      {sample : Fin q → ℝ | x < upperOrderStatistic sample rankFromTop}
  have h_nonneg :=
    iidProductMeasure_one_upperOrderStatistic_nonnegative_ae
      (lt_trans zero_lt_one hα) rankFromTop
  have h_int :=
    iidProductMeasure_one_upperOrderStatistic_integrable hα rankFromTop
  rw [expectedUpperOrderStatistic_eq_integral_tail_probability_of_nonneg
    (μ := iidProductMeasure 1 α q) rankFromTop h_nonneg h_int]
  have hbelow_Ioo :
      ∫ x in Set.Ioo (0 : ℝ) 1, tail x = 1 := by
    dsimp [tail]
    exact iidProductMeasure_one_upperOrderStatistic_tail_integral_Ioo_zero_one
      (lt_trans zero_lt_one hα) rankFromTop
  have hbelow_Ioc : IntegrableOn tail (Set.Ioc (0 : ℝ) 1) := by
    have hbelow_Ioo_int : IntegrableOn tail (Set.Ioo (0 : ℝ) 1) := by
      have hconst : IntegrableOn (fun _x : ℝ => (1 : ℝ))
          (Set.Ioo (0 : ℝ) 1) :=
        integrableOn_const (by simp)
      refine hconst.congr_fun ?_ measurableSet_Ioo
      intro x hx
      dsimp [tail]
      exact (iidProductMeasure_one_upperOrderStatistic_gt_real_of_lt_one
        (lt_trans zero_lt_one hα) hx.2 rankFromTop).symm
    exact
      (integrableOn_Ioc_iff_integrableOn_Ioo
        (μ := MeasureTheory.volume) (f := tail) (a := 0) (b := 1)).2
        hbelow_Ioo_int
  have habove_Ioi : IntegrableOn tail (Set.Ioi (1 : ℝ)) :=
    iidProductMeasure_one_upperOrderStatistic_tail_integrableOn_Ioi_one
      hα rankFromTop
  have hsplit :
      ∫ x in (Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ)), tail x =
        (∫ x in Set.Ioc (0 : ℝ) 1, tail x) +
          ∫ x in Set.Ioi (1 : ℝ), tail x := by
    exact MeasureTheory.setIntegral_union
      (Set.Ioc_disjoint_Ioi_same) measurableSet_Ioi
      hbelow_Ioc habove_Ioi
  rw [Set.Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1)] at hsplit
  rw [hsplit]
  have hbelow_Ioc_eq :
      ∫ x in Set.Ioc (0 : ℝ) 1, tail x = 1 := by
    rw [MeasureTheory.integral_Ioc_eq_integral_Ioo]
    exact hbelow_Ioo
  rw [hbelow_Ioc_eq]
  rw [iidProductMeasure_one_upperOrderStatistic_tail_integral_Ioi_one_eq_beta_sum
    hα rankFromTop]
  have hα_pos : 0 < α := lt_trans zero_lt_one hα
  have hδ_pos : 0 < 1 / α := one_div_pos.mpr hα_pos
  have hδ_lt_one : 1 / α < 1 := by
    rw [div_lt_one hα_pos]
    exact hα
  simpa [tail] using
    AppliedModelingLib.Math.one_add_sum_choose_mul_delta_mul_beta_eq_gamma_ratio
      (δ := 1 / α) hδ_pos hδ_lt_one
      (r := rankFromTop.val) (q := q) (Nat.le_of_lt rankFromTop.isLt)

end Pareto
end Probability
end AppliedModelingLib
