import Mathlib.Tactic.Linarith
import Mathlib.Topology.Algebra.Ring.Real
import AppliedModelingLib.Foundations.Probability.Gaussian

/-!
# Standard Gaussian Quantile Interface

Small analytic interface for papers that use the inverse standard-normal CDF.

## Main declarations

- `StandardGaussianQuantileAPI`
- `StandardGaussianQuantileAPI.quantile_pos_of_two_mul_capacity_lt_mass`
-/

namespace AppliedModelingLib
namespace Probability

/--
Analytic API for the inverse standard-normal CDF.

The mathematically faithful continuity domain for `Φ⁻¹` is the probability
interval `(0,1)`.  Paper proofs should prove their displayed quantile
arguments lie in this interval, then use this narrow interface for monotonicity,
continuity, and positivity above the median.
-/
structure StandardGaussianQuantileAPI where
  cdfAPI : StandardGaussianCDFAPI
  quantile : ℝ → ℝ
  cdf_quantile :
    ∀ {p : ℝ}, p ∈ Set.Ioo (0 : ℝ) 1 → cdfAPI.cdf (quantile p) = p
  quantile_mono : MonotoneOn quantile (Set.Ioo (0 : ℝ) 1)
  quantile_continuous : ContinuousOn quantile (Set.Ioo (0 : ℝ) 1)
  quantile_pos_of_half_lt :
    ∀ {p : ℝ}, p ∈ Set.Ioo (1 / 2 : ℝ) 1 → 0 < quantile p

namespace StandardGaussianQuantileAPI

/--
The quantile converts CDF upper sets into probability upper sets on `(0,1)`.
This is the reusable inverse-CDF bridge used by threshold-strategy proofs.
-/
theorem cdf_le_iff_le_quantile
    (Q : StandardGaussianQuantileAPI)
    {z p : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    Q.cdfAPI.cdf z ≤ p ↔ z ≤ Q.quantile p := by
  have hquantile : Q.cdfAPI.cdf (Q.quantile p) = p :=
    Q.cdf_quantile hp
  constructor
  · intro h
    have hcdf : Q.cdfAPI.cdf z ≤ Q.cdfAPI.cdf (Q.quantile p) := by
      simpa [hquantile] using h
    exact Q.cdfAPI.cdf_strictMono.le_iff_le.mp hcdf
  · intro h
    have hcdf : Q.cdfAPI.cdf z ≤ Q.cdfAPI.cdf (Q.quantile p) :=
      Q.cdfAPI.cdf_strictMono.le_iff_le.mpr h
    simpa [hquantile] using hcdf

/-- The inverse CDF is strictly increasing on `(0,1)`. -/
theorem quantile_strictMonoOn
    (Q : StandardGaussianQuantileAPI) :
    StrictMonoOn Q.quantile (Set.Ioo (0 : ℝ) 1) := by
  intro p hp q hq hpq
  by_contra hnot
  have hle : Q.quantile q ≤ Q.quantile p := le_of_not_gt hnot
  have hcdf_le :
      Q.cdfAPI.cdf (Q.quantile q) ≤ Q.cdfAPI.cdf (Q.quantile p) :=
    Q.cdfAPI.cdf_mono hle
  rw [Q.cdf_quantile hq, Q.cdf_quantile hp] at hcdf_le
  linarith

/--
Equivalently, a standard-normal upper-tail probability is at least `α` iff the
standardized cutoff lies below `Φ⁻¹(1 - α)`.
-/
theorem le_standardTail_iff_le_quantile_one_sub
    (Q : StandardGaussianQuantileAPI)
    {alpha z : ℝ} (halpha : alpha ∈ Set.Ioo (0 : ℝ) 1) :
    alpha ≤ 1 - Q.cdfAPI.cdf z ↔ z ≤ Q.quantile (1 - alpha) := by
  have halpha_pos : 0 < alpha := halpha.1
  have halpha_lt_one : alpha < 1 := halpha.2
  have hone_sub_mem : 1 - alpha ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨by linarith, by linarith⟩
  calc
    alpha ≤ 1 - Q.cdfAPI.cdf z ↔ Q.cdfAPI.cdf z ≤ 1 - alpha := by
      constructor <;> intro h <;> linarith
    _ ↔ z ≤ Q.quantile (1 - alpha) :=
      Q.cdf_le_iff_le_quantile hone_sub_mem

/--
Strict upper-tail inverse-CDF form: an upper-tail probability is strictly above
`α` iff the standardized cutoff lies strictly below `Φ⁻¹(1 - α)`.
-/
theorem lt_standardTail_iff_lt_quantile_one_sub
    (Q : StandardGaussianQuantileAPI)
    {alpha z : ℝ} (halpha : alpha ∈ Set.Ioo (0 : ℝ) 1) :
    alpha < 1 - Q.cdfAPI.cdf z ↔ z < Q.quantile (1 - alpha) := by
  have halpha_pos : 0 < alpha := halpha.1
  have halpha_lt_one : alpha < 1 := halpha.2
  have hone_sub_mem : 1 - alpha ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨by linarith, by linarith⟩
  have hquantile : Q.cdfAPI.cdf (Q.quantile (1 - alpha)) = 1 - alpha :=
    Q.cdf_quantile hone_sub_mem
  calc
    alpha < 1 - Q.cdfAPI.cdf z ↔
        Q.cdfAPI.cdf z < 1 - alpha := by
      constructor <;> intro h <;> linarith
    _ ↔ Q.cdfAPI.cdf z < Q.cdfAPI.cdf (Q.quantile (1 - alpha)) := by
      rw [hquantile]
    _ ↔ z < Q.quantile (1 - alpha) :=
      Q.cdfAPI.cdf_strictMono.lt_iff_lt

/--
Strict lower-tail counterpart: an upper-tail probability is strictly below
`α` iff `Φ⁻¹(1 - α)` lies strictly below the standardized cutoff.
-/
theorem standardTail_lt_iff_quantile_one_sub_lt
    (Q : StandardGaussianQuantileAPI)
    {alpha z : ℝ} (halpha : alpha ∈ Set.Ioo (0 : ℝ) 1) :
    1 - Q.cdfAPI.cdf z < alpha ↔ Q.quantile (1 - alpha) < z := by
  have halpha_pos : 0 < alpha := halpha.1
  have halpha_lt_one : alpha < 1 := halpha.2
  have hone_sub_mem : 1 - alpha ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨by linarith, by linarith⟩
  have hquantile : Q.cdfAPI.cdf (Q.quantile (1 - alpha)) = 1 - alpha :=
    Q.cdf_quantile hone_sub_mem
  calc
    1 - Q.cdfAPI.cdf z < alpha ↔
        1 - alpha < Q.cdfAPI.cdf z := by
      constructor <;> intro h <;> linarith
    _ ↔ Q.cdfAPI.cdf (Q.quantile (1 - alpha)) < Q.cdfAPI.cdf z := by
      rw [hquantile]
    _ ↔ Q.quantile (1 - alpha) < z :=
      Q.cdfAPI.cdf_strictMono.lt_iff_lt

/--
The selectivity condition relative to an eligible mass, `2 * capacity < mass`,
makes the upper-tail quantile `Φ⁻¹(1 - capacity / mass)` positive.
-/
theorem quantile_pos_of_two_mul_capacity_lt_mass
    (Q : StandardGaussianQuantileAPI)
    {capacity mass : ℝ}
    (hcapacity_pos : 0 < capacity)
    (hmass_pos : 0 < mass) (hselective : 2 * capacity < mass) :
    0 < Q.quantile (1 - capacity / mass) := by
  have hdiv_lt_half : capacity / mass < (1 / 2 : ℝ) := by
    rw [div_lt_iff₀ hmass_pos]
    linarith
  have hdiv_pos : 0 < capacity / mass := div_pos hcapacity_pos hmass_pos
  exact Q.quantile_pos_of_half_lt ⟨by linarith, by linarith⟩

end StandardGaussianQuantileAPI

end Probability
end AppliedModelingLib
