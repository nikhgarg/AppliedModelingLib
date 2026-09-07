import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import AppliedModelingLib.Foundations.Optimization.Certificate

namespace AppliedModelingLib
namespace Statistics

/-!
# Binary Prior-Weighted Rating Algebra

Reusable algebra for binary-review Bayesian/prior-weighted rating systems.
-/

/-- Jensen convexity for real functions, stated in the finite-dimensional form
used by EC paper theorem wrappers. -/
def JensenConvex (f : ℝ → ℝ) : Prop :=
  ∀ x y lam, 0 ≤ lam → lam ≤ 1 →
    f (lam * x + (1 - lam) * y) ≤ lam * f x + (1 - lam) * f y

/-- Jensen concavity for real functions, stated in the finite-dimensional form
used by EC paper theorem wrappers. -/
def JensenConcave (f : ℝ → ℝ) : Prop :=
  ∀ x y lam, 0 ≤ lam → lam ≤ 1 →
    lam * f x + (1 - lam) * f y ≤ f (lam * x + (1 - lam) * y)

/-- A point is a global minimizer of a real-valued function. -/
abbrev GlobalMinAt (f : ℝ → ℝ) (x₀ : ℝ) : Prop :=
  Optimization.IsGlobalMinimizer f x₀

/-- A point is a global maximizer of a real-valued function. -/
abbrev GlobalMaxAt (f : ℝ → ℝ) (x₀ : ℝ) : Prop :=
  Optimization.IsGlobalMaximizer f x₀

/--
Variance term for the prior-weighted posterior mean estimator in the fixed
binary-rating model.

The parameters are real-valued here to keep this lemma reusable for paper
wrappers. In paper notation, `alpha` and `beta` are prior-shape parameters,
`eta` is prior strength, `t` is the number of reviews, and `q` is true quality.
-/
noncomputable def priorWeightedVariance
    (alpha beta eta t q : ℝ) : ℝ :=
  t * q * (1 - q) / (eta * alpha + eta * beta + t) ^ 2

/--
Posterior mean of the Beta-Bernoulli prior-weighted estimator in the fixed
binary-rating model, conditional on true quality `q`.
-/
noncomputable def priorWeightedPosteriorMean
    (alpha beta eta t q : ℝ) : ℝ :=
  (eta * alpha + t * q) / (eta * alpha + eta * beta + t)

/-- Bias of the prior-weighted posterior mean estimator. -/
noncomputable def priorWeightedBias
    (alpha beta eta t q : ℝ) : ℝ :=
  priorWeightedPosteriorMean alpha beta eta t q - q

/-- Squared bias term in the fixed binary-rating model. -/
noncomputable def priorWeightedSquaredBias
    (alpha beta eta t q : ℝ) : ℝ :=
  (priorWeightedBias alpha beta eta t q) ^ 2

theorem priorWeightedBias_eq_scaled_priorShare
    {alpha beta eta t q : ℝ}
    (hden : eta * alpha + eta * beta + t ≠ 0) :
    priorWeightedBias alpha beta eta t q =
      (alpha - (alpha + beta) * q) *
        (eta / (eta * (alpha + beta) + t)) := by
  unfold priorWeightedBias priorWeightedPosteriorMean
  have hden' : eta * (alpha + beta) + t ≠ 0 := by
    intro h
    apply hden
    calc
      eta * alpha + eta * beta + t = eta * (alpha + beta) + t := by ring
      _ = 0 := h
  field_simp [hden, hden']
  ring

theorem priorWeightedSquaredBias_eq_scaled_priorShare_sq
    {alpha beta eta t q : ℝ}
    (hden : eta * alpha + eta * beta + t ≠ 0) :
    priorWeightedSquaredBias alpha beta eta t q =
      (alpha - (alpha + beta) * q) ^ 2 *
        (eta / (eta * (alpha + beta) + t)) ^ 2 := by
  unfold priorWeightedSquaredBias
  rw [priorWeightedBias_eq_scaled_priorShare (hden := hden)]
  ring

theorem priorShare_mono
    {s t etaLow etaHigh : ℝ}
    (hs : 0 < s)
    (ht : 0 < t)
    (hetaLow_nonneg : 0 ≤ etaLow)
    (heta_le : etaLow ≤ etaHigh) :
    etaLow / (etaLow * s + t) ≤
      etaHigh / (etaHigh * s + t) := by
  have hetaHigh_nonneg : 0 ≤ etaHigh := le_trans hetaLow_nonneg heta_le
  have hden_low_pos : 0 < etaLow * s + t :=
    add_pos_of_nonneg_of_pos (mul_nonneg hetaLow_nonneg hs.le) ht
  have hden_high_pos : 0 < etaHigh * s + t :=
    add_pos_of_nonneg_of_pos (mul_nonneg hetaHigh_nonneg hs.le) ht
  rw [div_le_div_iff₀ hden_low_pos hden_high_pos]
  have hmul : etaLow * t ≤ etaHigh * t :=
    mul_le_mul_of_nonneg_right heta_le ht.le
  nlinarith

theorem priorWeightedSquaredBias_mono
    {alpha beta t q etaLow etaHigh : ℝ}
    (hshape : 0 < alpha + beta)
    (ht : 0 < t)
    (hetaLow_nonneg : 0 ≤ etaLow)
    (heta_le : etaLow ≤ etaHigh) :
    priorWeightedSquaredBias alpha beta etaLow t q ≤
      priorWeightedSquaredBias alpha beta etaHigh t q := by
  let s := alpha + beta
  have hs : 0 < s := hshape
  have hetaHigh_nonneg : 0 ≤ etaHigh := le_trans hetaLow_nonneg heta_le
  have hden_low_pos : 0 < etaLow * alpha + etaLow * beta + t := by
    calc
      0 < etaLow * (alpha + beta) + t :=
        add_pos_of_nonneg_of_pos
          (mul_nonneg hetaLow_nonneg hshape.le) ht
      _ = etaLow * alpha + etaLow * beta + t := by ring
  have hden_high_pos : 0 < etaHigh * alpha + etaHigh * beta + t := by
    calc
      0 < etaHigh * (alpha + beta) + t :=
        add_pos_of_nonneg_of_pos
          (mul_nonneg hetaHigh_nonneg hshape.le) ht
      _ = etaHigh * alpha + etaHigh * beta + t := by ring
  have hshare_le :
      etaLow / (etaLow * (alpha + beta) + t) ≤
        etaHigh / (etaHigh * (alpha + beta) + t) :=
    priorShare_mono hshape ht hetaLow_nonneg heta_le
  have hshare_low_nonneg :
      0 ≤ etaLow / (etaLow * (alpha + beta) + t) := by
    exact div_nonneg hetaLow_nonneg
      (add_pos_of_nonneg_of_pos
        (mul_nonneg hetaLow_nonneg hshape.le) ht).le
  have hshare_sq_le :
      (etaLow / (etaLow * (alpha + beta) + t)) ^ 2 ≤
        (etaHigh / (etaHigh * (alpha + beta) + t)) ^ 2 := by
    rw [sq, sq]
    exact mul_self_le_mul_self hshare_low_nonneg hshare_le
  have hscale_nonneg : 0 ≤ (alpha - (alpha + beta) * q) ^ 2 :=
    sq_nonneg _
  calc
    priorWeightedSquaredBias alpha beta etaLow t q
        = (alpha - (alpha + beta) * q) ^ 2 *
            (etaLow / (etaLow * (alpha + beta) + t)) ^ 2 := by
          exact priorWeightedSquaredBias_eq_scaled_priorShare_sq
            (hden := ne_of_gt hden_low_pos)
    _ ≤ (alpha - (alpha + beta) * q) ^ 2 *
            (etaHigh / (etaHigh * (alpha + beta) + t)) ^ 2 :=
          mul_le_mul_of_nonneg_left hshare_sq_le hscale_nonneg
    _ = priorWeightedSquaredBias alpha beta etaHigh t q := by
          exact (priorWeightedSquaredBias_eq_scaled_priorShare_sq
            (hden := ne_of_gt hden_high_pos)).symm

theorem priorWeightedSquaredBias_nonneg
    (alpha beta eta t q : ℝ) :
    0 ≤ priorWeightedSquaredBias alpha beta eta t q := by
  unfold priorWeightedSquaredBias
  exact sq_nonneg _

@[simp] theorem priorWeightedSquaredBias_priorMean_eq_zero
    {alpha beta eta t : ℝ}
    (hshape : alpha + beta ≠ 0)
    (hden : eta * alpha + eta * beta + t ≠ 0) :
    priorWeightedSquaredBias alpha beta eta t (alpha / (alpha + beta)) = 0 := by
  rw [priorWeightedSquaredBias_eq_scaled_priorShare_sq (hden := hden)]
  have hzero : alpha - (alpha + beta) * (alpha / (alpha + beta)) = 0 := by
    field_simp [hshape]
    ring
  rw [hzero]
  ring

theorem priorWeightedSquaredBias_globalMin_priorMean
    {alpha beta eta t : ℝ}
    (hshape : alpha + beta ≠ 0)
    (hden : eta * alpha + eta * beta + t ≠ 0) :
    GlobalMinAt
      (fun q => priorWeightedSquaredBias alpha beta eta t q)
      (alpha / (alpha + beta)) := by
  intro q
  change priorWeightedSquaredBias alpha beta eta t (alpha / (alpha + beta)) ≤
    priorWeightedSquaredBias alpha beta eta t q
  rw [priorWeightedSquaredBias_priorMean_eq_zero
    (hshape := hshape) (hden := hden)]
  exact priorWeightedSquaredBias_nonneg alpha beta eta t q

theorem priorWeightedSquaredBias_jensenConvex_quality
    {alpha beta eta t : ℝ}
    (hden : eta * alpha + eta * beta + t ≠ 0) :
    JensenConvex (fun q => priorWeightedSquaredBias alpha beta eta t q) := by
  intro x y lam hlam0 hlam1
  let scale := (eta / (eta * (alpha + beta) + t)) ^ 2
  have hden' : eta * (alpha + beta) + t ≠ 0 := by
    intro h
    apply hden
    calc
      eta * alpha + eta * beta + t = eta * (alpha + beta) + t := by ring
      _ = 0 := h
  have hscale_nonneg : 0 ≤ scale := by
    unfold scale
    exact sq_nonneg _
  have h1lam : 0 ≤ 1 - lam := sub_nonneg.mpr hlam1
  have hsquare :
      (alpha - (alpha + beta) * (lam * x + (1 - lam) * y)) ^ 2 ≤
        lam * (alpha - (alpha + beta) * x) ^ 2 +
          (1 - lam) * (alpha - (alpha + beta) * y) ^ 2 := by
    nlinarith [mul_nonneg hlam0 h1lam,
      sq_nonneg ((alpha - (alpha + beta) * x) -
        (alpha - (alpha + beta) * y))]
  calc
    priorWeightedSquaredBias alpha beta eta t (lam * x + (1 - lam) * y)
        = scale *
            (alpha - (alpha + beta) * (lam * x + (1 - lam) * y)) ^ 2 := by
          rw [priorWeightedSquaredBias_eq_scaled_priorShare_sq (hden := hden)]
          ring
    _ ≤ scale *
          (lam * (alpha - (alpha + beta) * x) ^ 2 +
            (1 - lam) * (alpha - (alpha + beta) * y) ^ 2) :=
          mul_le_mul_of_nonneg_left hsquare hscale_nonneg
    _ = lam * priorWeightedSquaredBias alpha beta eta t x +
          (1 - lam) * priorWeightedSquaredBias alpha beta eta t y := by
          rw [priorWeightedSquaredBias_eq_scaled_priorShare_sq (hden := hden)]
          rw [priorWeightedSquaredBias_eq_scaled_priorShare_sq (hden := hden)]
          ring

@[simp] theorem priorWeightedVariance_quality_zero
    (alpha beta eta t : ℝ) :
    priorWeightedVariance alpha beta eta t 0 = 0 := by
  simp [priorWeightedVariance]

@[simp] theorem priorWeightedVariance_quality_one
    (alpha beta eta t : ℝ) :
    priorWeightedVariance alpha beta eta t 1 = 0 := by
  simp [priorWeightedVariance]

theorem priorWeightedVariance_eq_scaled_qualityQuadratic
    (alpha beta eta t q : ℝ) :
    priorWeightedVariance alpha beta eta t q =
      (t / (eta * (alpha + beta) + t) ^ 2) * (q * (1 - q)) := by
  unfold priorWeightedVariance
  ring

theorem priorWeightedVariance_globalMax_half
    {alpha beta eta t : ℝ}
    (ht : 0 ≤ t) :
    GlobalMaxAt
      (fun q => priorWeightedVariance alpha beta eta t q)
      (1 / 2) := by
  intro q
  let scale := t / (eta * (alpha + beta) + t) ^ 2
  have hscale_nonneg : 0 ≤ scale := by
    unfold scale
    exact div_nonneg ht (sq_nonneg _)
  have hquad : q * (1 - q) ≤ (1 / 2 : ℝ) * (1 - (1 / 2 : ℝ)) := by
    nlinarith [sq_nonneg (q - (1 / 2 : ℝ))]
  change priorWeightedVariance alpha beta eta t q ≤
    priorWeightedVariance alpha beta eta t (1 / 2)
  calc
    priorWeightedVariance alpha beta eta t q
        = scale * (q * (1 - q)) := by
          unfold scale
          exact priorWeightedVariance_eq_scaled_qualityQuadratic
            alpha beta eta t q
    _ ≤ scale * ((1 / 2 : ℝ) * (1 - (1 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left hquad hscale_nonneg
    _ = priorWeightedVariance alpha beta eta t (1 / 2) := by
          unfold scale
          exact (priorWeightedVariance_eq_scaled_qualityQuadratic
            alpha beta eta t (1 / 2)).symm

theorem priorWeightedVariance_jensenConcave_quality
    {alpha beta eta t : ℝ}
    (ht : 0 ≤ t) :
    JensenConcave (fun q => priorWeightedVariance alpha beta eta t q) := by
  intro x y lam hlam0 hlam1
  let scale := t / (eta * (alpha + beta) + t) ^ 2
  have hscale_nonneg : 0 ≤ scale := by
    unfold scale
    exact div_nonneg ht (sq_nonneg _)
  have h1lam : 0 ≤ 1 - lam := sub_nonneg.mpr hlam1
  have hquad :
      lam * (x * (1 - x)) + (1 - lam) * (y * (1 - y)) ≤
        (lam * x + (1 - lam) * y) *
          (1 - (lam * x + (1 - lam) * y)) := by
    nlinarith [mul_nonneg hlam0 h1lam, sq_nonneg (x - y)]
  calc
    lam * priorWeightedVariance alpha beta eta t x +
        (1 - lam) * priorWeightedVariance alpha beta eta t y
        = scale *
            (lam * (x * (1 - x)) + (1 - lam) * (y * (1 - y))) := by
          rw [priorWeightedVariance_eq_scaled_qualityQuadratic
            alpha beta eta t x]
          rw [priorWeightedVariance_eq_scaled_qualityQuadratic
            alpha beta eta t y]
          unfold scale
          ring
    _ ≤ scale *
          ((lam * x + (1 - lam) * y) *
            (1 - (lam * x + (1 - lam) * y))) :=
          mul_le_mul_of_nonneg_left hquad hscale_nonneg
    _ = priorWeightedVariance alpha beta eta t
          (lam * x + (1 - lam) * y) := by
          unfold scale
          exact (priorWeightedVariance_eq_scaled_qualityQuadratic
            alpha beta eta t (lam * x + (1 - lam) * y)).symm

/--
At boundary quality `q = 0`, the variance term cannot be strictly decreasing in
prior strength, since it is identically zero.
-/
theorem not_strictly_decreasing_priorWeightedVariance_quality_zero
    (alpha beta t etaLow etaHigh : ℝ) :
    ¬ priorWeightedVariance alpha beta etaHigh t 0 <
      priorWeightedVariance alpha beta etaLow t 0 := by
  simp

/--
At boundary quality `q = 1`, the variance term cannot be strictly decreasing in
prior strength, since it is identically zero.
-/
theorem not_strictly_decreasing_priorWeightedVariance_quality_one
    (alpha beta t etaLow etaHigh : ℝ) :
    ¬ priorWeightedVariance alpha beta etaHigh t 1 <
      priorWeightedVariance alpha beta etaLow t 1 := by
  simp

/--
Weak variance decrease for all Bernoulli qualities in `[0, 1]`.

The strict version fails at the boundary, but the weak monotonicity statement is
valid throughout the closed quality interval.
-/
theorem priorWeightedVariance_weak_decrease
    {alpha beta t q etaLow etaHigh : ℝ}
    (hshape : 0 < alpha + beta)
    (ht : 0 < t)
    (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1)
    (hetaLow_nonneg : 0 ≤ etaLow)
    (heta_le : etaLow ≤ etaHigh) :
    priorWeightedVariance alpha beta etaHigh t q ≤
      priorWeightedVariance alpha beta etaLow t q := by
  have hetaHigh_nonneg : 0 ≤ etaHigh := le_trans hetaLow_nonneg heta_le
  have hq_gap : 0 ≤ 1 - q := sub_nonneg.mpr hq1
  have hnum_nonneg : 0 ≤ t * q * (1 - q) := by
    exact mul_nonneg (mul_nonneg ht.le hq0) hq_gap
  have hden_low_pos : 0 < etaLow * alpha + etaLow * beta + t := by
    calc
      0 < etaLow * (alpha + beta) + t :=
        add_pos_of_nonneg_of_pos
          (mul_nonneg hetaLow_nonneg hshape.le) ht
      _ = etaLow * alpha + etaLow * beta + t := by ring
  have hden_high_pos : 0 < etaHigh * alpha + etaHigh * beta + t := by
    calc
      0 < etaHigh * (alpha + beta) + t :=
        add_pos_of_nonneg_of_pos
          (mul_nonneg hetaHigh_nonneg hshape.le) ht
      _ = etaHigh * alpha + etaHigh * beta + t := by ring
  have hden_le :
      etaLow * alpha + etaLow * beta + t ≤
        etaHigh * alpha + etaHigh * beta + t := by
    calc
      etaLow * alpha + etaLow * beta + t
          = etaLow * (alpha + beta) + t := by ring
      _ ≤ etaHigh * (alpha + beta) + t := by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_right
              (mul_le_mul_of_nonneg_right heta_le hshape.le) t
      _ = etaHigh * alpha + etaHigh * beta + t := by ring
  have hsq_le :
      (etaLow * alpha + etaLow * beta + t) ^ 2 ≤
        (etaHigh * alpha + etaHigh * beta + t) ^ 2 := by
    exact pow_le_pow_left₀ hden_low_pos.le hden_le 2
  unfold priorWeightedVariance
  exact div_le_div_of_nonneg_left hnum_nonneg
    (sq_pos_of_pos hden_low_pos) hsq_le

/--
Interior-quality corrected strict variance decrease for the fixed binary-rating
model.

If prior shape has positive total mass, the number of reviews is positive, and
true quality is not at a Bernoulli boundary, then increasing prior strength
strictly decreases the variance term from the variance decomposition.
-/
theorem priorWeightedVariance_strict_decrease_of_interior_quality
    {alpha beta t q etaLow etaHigh : ℝ}
    (hshape : 0 < alpha + beta)
    (ht : 0 < t)
    (hq0 : 0 < q)
    (hq1 : q < 1)
    (hetaLow_nonneg : 0 ≤ etaLow)
    (heta_lt : etaLow < etaHigh) :
    priorWeightedVariance alpha beta etaHigh t q <
      priorWeightedVariance alpha beta etaLow t q := by
  have hq_gap : 0 < 1 - q := sub_pos.mpr hq1
  have hnum_pos : 0 < t * q * (1 - q) := by
    exact mul_pos (mul_pos ht hq0) hq_gap
  have hden_low_pos : 0 < etaLow * alpha + etaLow * beta + t := by
    calc
      0 < etaLow * (alpha + beta) + t :=
        add_pos_of_nonneg_of_pos
          (mul_nonneg hetaLow_nonneg hshape.le) ht
      _ = etaLow * alpha + etaLow * beta + t := by ring
  have hden_lt :
      etaLow * alpha + etaLow * beta + t <
        etaHigh * alpha + etaHigh * beta + t := by
    calc
      etaLow * alpha + etaLow * beta + t
          = etaLow * (alpha + beta) + t := by ring
      _ < etaHigh * (alpha + beta) + t := by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_lt_add_right
              (mul_lt_mul_of_pos_right heta_lt hshape) t
      _ = etaHigh * alpha + etaHigh * beta + t := by ring
  have hsq_lt :
      (etaLow * alpha + etaLow * beta + t) ^ 2 <
        (etaHigh * alpha + etaHigh * beta + t) ^ 2 :=
    pow_lt_pow_left₀ hden_lt hden_low_pos.le (by decide : (2 : ℕ) ≠ 0)
  unfold priorWeightedVariance
  exact div_lt_div_of_pos_left hnum_pos
    (sq_pos_of_pos hden_low_pos) hsq_lt

end Statistics
end AppliedModelingLib
