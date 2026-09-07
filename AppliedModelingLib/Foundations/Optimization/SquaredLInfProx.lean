import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Data.Real.Sign
import Mathlib.Tactic

/-!
# Proximal map of a squared finite sup norm

This module proves the finite-dimensional clipping formula for the proximal
map of `x ↦ (κ / 2) * ‖x‖_∞²`.  Its mathematical core is the scalar threshold
equation

`∑ i, max (|w i| - β) 0 = κ * β`.

The repository's pinned Mathlib checkout and public Lean repositories were
searched for a proximal/Moreau or squared-`ℓ¹` threshold theorem before this
module was written.  None compatible with the pinned revision was found.  The
proof below is original to this repository; it uses Mathlib's finite sup norm,
finite sums, real sign, and elementary ordered-ring lemmas.  Mathlib is
Apache-2.0 and is pinned by this repository's `lake-manifest.json`.
-/

namespace AppliedModelingLib
namespace SquaredLInfProx

/-- The positive part of a real number. -/
def positivePart (x : ℝ) : ℝ := max x 0

/-- Coordinatewise clipping at absolute level `β`, in the paper's residual form. -/
noncomputable def clipCoordinate (β w : ℝ) : ℝ :=
  w - positivePart (|w| - β) * Real.sign w

/-- Coordinatewise clipping of a finite real vector. -/
noncomputable def clip {ι : Type*} (β : ℝ) (w : ι → ℝ) : ι → ℝ :=
  fun i => clipCoordinate β (w i)

/-- The scalar equation determining the clipping threshold. -/
def ThresholdEquation {ι : Type*} [Fintype ι]
    (κ β : ℝ) (w : ι → ℝ) : Prop :=
  ∑ i, positivePart (|w i| - β) = κ * β

/-- The standard proximal objective for `(κ / 2) * ‖·‖_∞²`. -/
noncomputable def objective {ι : Type*} [Fintype ι]
    (κ : ℝ) (w x : ι → ℝ) : ℝ :=
  κ / 2 * ‖x‖ ^ 2 + (1 / 2 : ℝ) * ∑ i, (x i - w i) ^ 2

lemma positivePart_nonneg (x : ℝ) : 0 ≤ positivePart x := by
  simp [positivePart]

lemma positivePart_eq_zero_of_le {x : ℝ} (hx : x ≤ 0) : positivePart x = 0 := by
  simp [positivePart, hx]

lemma positivePart_eq_self_of_nonneg {x : ℝ} (hx : 0 ≤ x) : positivePart x = x := by
  simp [positivePart, hx]

/-- Increasing the clipping threshold weakly decreases every residual positive part. -/
lemma positivePart_sub_antitone_right {value first second : ℝ} (h : first ≤ second) :
    positivePart (value - second) ≤ positivePart (value - first) := by
  unfold positivePart
  exact max_le_max (sub_le_sub_left h value) le_rfl

/--
For a positive quadratic coefficient, the scalar clipping-threshold equation
has at most one solution.  No ordering or sign condition on the vector is
needed for uniqueness.
-/
theorem thresholdEquation_unique {ι : Type*} [Fintype ι]
    {κ first second : ℝ} {w : ι → ℝ} (hκ : 0 < κ)
    (hfirst : ThresholdEquation κ first w)
    (hsecond : ThresholdEquation κ second w) :
    first = second := by
  rcases lt_trichotomy first second with hlt | heq | hgt
  · have hsum :
        ∑ i, positivePart (|w i| - second) ≤
          ∑ i, positivePart (|w i| - first) := by
      exact Finset.sum_le_sum fun i _ => positivePart_sub_antitone_right hlt.le
    rw [hsecond, hfirst] at hsum
    exact (not_lt_of_ge hsum (mul_lt_mul_of_pos_left hlt hκ)).elim
  · exact heq
  · have hsum :
        ∑ i, positivePart (|w i| - first) ≤
          ∑ i, positivePart (|w i| - second) := by
      exact Finset.sum_le_sum fun i _ => positivePart_sub_antitone_right hgt.le
    rw [hfirst, hsecond] at hsum
    exact (not_lt_of_ge hsum (mul_lt_mul_of_pos_left hgt hκ)).elim

lemma abs_mul_realSign (w : ℝ) : |w| * Real.sign w = w := by
  rcases lt_trichotomy w 0 with hw | rfl | hw
  · rw [abs_of_neg hw, Real.sign_of_neg hw]
    ring
  · simp
  · rw [abs_of_pos hw, Real.sign_of_pos hw]
    ring

lemma realSign_sq_of_ne_zero {w : ℝ} (hw : w ≠ 0) : Real.sign w ^ 2 = 1 := by
  rcases hw.lt_or_gt with hw | hw
  · rw [Real.sign_of_neg hw]
    norm_num
  · rw [Real.sign_of_pos hw]
    norm_num

lemma clipCoordinate_eq_self_of_abs_le {β w : ℝ} (hw : |w| ≤ β) :
    clipCoordinate β w = w := by
  simp [clipCoordinate, positivePart, sub_nonpos.mpr hw]

lemma clipCoordinate_eq_sign_mul_of_le_abs {β w : ℝ} (hw : β ≤ |w|) :
    clipCoordinate β w = β * Real.sign w := by
  have hpart : positivePart (|w| - β) = |w| - β :=
    positivePart_eq_self_of_nonneg (sub_nonneg.mpr hw)
  rw [clipCoordinate, hpart]
  rw [sub_mul, abs_mul_realSign]
  ring

lemma abs_clipCoordinate_le {β w : ℝ} (hβ : 0 ≤ β) :
    |clipCoordinate β w| ≤ β := by
  rcases le_total |w| β with hw | hw
  · rw [clipCoordinate_eq_self_of_abs_le hw]
    exact hw
  · rw [clipCoordinate_eq_sign_mul_of_le_abs hw]
    by_cases hzero : w = 0
    · subst w
      simp [hβ]
    · have hsign : |Real.sign w| = 1 := by
        rcases Real.sign_apply_eq_of_ne_zero w hzero with hsign | hsign <;>
          rw [hsign] <;> norm_num
      rw [abs_mul, abs_of_nonneg hβ, hsign, mul_one]

lemma clipCoordinate_sub_sq {β w : ℝ} (hβ : 0 ≤ β) :
    (clipCoordinate β w - w) ^ 2 = positivePart (|w| - β) ^ 2 := by
  rw [clipCoordinate]
  ring_nf
  by_cases hpart : positivePart (|w| - β) = 0
  · simp [hpart]
  · have hw : w ≠ 0 := by
      intro hw
      subst w
      simp [positivePart, hβ] at hpart
    rw [realSign_sq_of_ne_zero hw, mul_one]

/-- A coordinate outside a radius incurs at least its clipped residual distance. -/
lemma positivePart_sq_le_sub_sq {r x w : ℝ} (hx : |x| ≤ r) :
    positivePart (|w| - r) ^ 2 ≤ (x - w) ^ 2 := by
  have hresidual_nonneg : 0 ≤ positivePart (|w| - r) := positivePart_nonneg _
  have hresidual_le : positivePart (|w| - r) ≤ |x - w| := by
    rw [positivePart]
    apply max_le
    · calc
        |w| - r ≤ |w| - |x| := sub_le_sub_left hx _
        _ ≤ |w - x| := abs_sub_abs_le_abs_sub _ _
        _ = |x - w| := abs_sub_comm _ _
    · exact abs_nonneg _
  simpa [pow_two] using mul_self_le_mul_self hresidual_nonneg hresidual_le

/-- Supporting-line inequality for a squared positive-part residual. -/
lemma positivePart_sq_support (v β r : ℝ) :
    (1 / 2 : ℝ) * positivePart (v - r) ^ 2 ≥
      (1 / 2 : ℝ) * positivePart (v - β) ^ 2 -
        positivePart (v - β) * (r - β) := by
  by_cases hvβ : v ≤ β
  · have hzero : positivePart (v - β) = 0 :=
      positivePart_eq_zero_of_le (sub_nonpos.mpr hvβ)
    rw [hzero]
    have hsquare : 0 ≤ positivePart (v - r) ^ 2 := sq_nonneg _
    nlinarith
  · have hβv : β < v := lt_of_not_ge hvβ
    have hβpart : positivePart (v - β) = v - β :=
      positivePart_eq_self_of_nonneg (sub_nonneg.mpr hβv.le)
    by_cases hvr : v ≤ r
    · have hrpart : positivePart (v - r) = 0 :=
        positivePart_eq_zero_of_le (sub_nonpos.mpr hvr)
      rw [hrpart, hβpart]
      ring_nf
      nlinarith [sq_nonneg (r - β)]
    · have hrv : r < v := lt_of_not_ge hvr
      have hrpart : positivePart (v - r) = v - r :=
        positivePart_eq_self_of_nonneg (sub_nonneg.mpr hrv.le)
      rw [hrpart, hβpart]
      ring_nf
      nlinarith [sq_nonneg (r - β)]

/-- The clipping vector has sup norm at most its nonnegative threshold. -/
lemma norm_clip_le {ι : Type*} [Fintype ι] [Nonempty ι]
    {β : ℝ} (hβ : 0 ≤ β) (w : ι → ℝ) :
    ‖clip β w‖ ≤ β := by
  rw [pi_norm_le_iff_of_nonneg hβ]
  intro i
  simpa [Real.norm_eq_abs, clip] using abs_clipCoordinate_le (β := β) (w := w i) hβ

/--
Any nonnegative solution of the threshold equation gives the global minimizer
of the squared-sup-norm proximal objective.
-/
theorem clip_minimizes_objective {ι : Type*} [Fintype ι] [Nonempty ι]
    {κ β : ℝ} (hκ : 0 < κ) (hβ : 0 ≤ β) (w x : ι → ℝ)
    (hequation : ThresholdEquation κ β w) :
    objective κ w (clip β w) ≤ objective κ w x := by
  let r : ℝ := ‖x‖
  have hr : 0 ≤ r := norm_nonneg _
  have hcoordinate (i : ι) : |x i| ≤ r := by
    simpa [r, Real.norm_eq_abs] using norm_le_pi_norm x i
  have hlower_distance :
      ∑ i, positivePart (|w i| - r) ^ 2 ≤ ∑ i, (x i - w i) ^ 2 := by
    exact Finset.sum_le_sum fun i _ => positivePart_sq_le_sub_sq (hcoordinate i)
  have hsupport_each (i : ι) :
      (1 / 2 : ℝ) * positivePart (|w i| - r) ^ 2 ≥
        (1 / 2 : ℝ) * positivePart (|w i| - β) ^ 2 -
          positivePart (|w i| - β) * (r - β) :=
    positivePart_sq_support _ _ _
  have hsupport_sum :
      (1 / 2 : ℝ) * ∑ i, positivePart (|w i| - r) ^ 2 ≥
        (1 / 2 : ℝ) * ∑ i, positivePart (|w i| - β) ^ 2 -
          (∑ i, positivePart (|w i| - β)) * (r - β) := by
    calc
      (1 / 2 : ℝ) * ∑ i, positivePart (|w i| - r) ^ 2 =
          ∑ i, (1 / 2 : ℝ) * positivePart (|w i| - r) ^ 2 := by
            rw [Finset.mul_sum]
      _ ≥ ∑ i, ((1 / 2 : ℝ) * positivePart (|w i| - β) ^ 2 -
          positivePart (|w i| - β) * (r - β)) :=
            Finset.sum_le_sum fun i _ => hsupport_each i
      _ = (1 / 2 : ℝ) * ∑ i, positivePart (|w i| - β) ^ 2 -
          (∑ i, positivePart (|w i| - β)) * (r - β) := by
            rw [Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul]
  have hclip_distance :
      ∑ i, (clip β w i - w i) ^ 2 =
        ∑ i, positivePart (|w i| - β) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    exact clipCoordinate_sub_sq hβ
  have hnorm_clip : ‖clip β w‖ ≤ β := norm_clip_le hβ w
  have hnorm_clip_sq : ‖clip β w‖ ^ 2 ≤ β ^ 2 := by
    exact (sq_le_sq₀ (norm_nonneg _) hβ).2 hnorm_clip
  have hdistance_scaled :
      (1 / 2 : ℝ) * ∑ i, positivePart (|w i| - r) ^ 2 ≤
        (1 / 2 : ℝ) * ∑ i, (x i - w i) ^ 2 := by
    exact mul_le_mul_of_nonneg_left hlower_distance (by norm_num)
  rw [ThresholdEquation] at hequation
  rw [objective, hclip_distance]
  have hκnonneg : 0 ≤ κ := hκ.le
  have hclip_norm_scaled : κ / 2 * ‖clip β w‖ ^ 2 ≤ κ / 2 * β ^ 2 :=
    mul_le_mul_of_nonneg_left hnorm_clip_sq (by positivity)
  calc
    κ / 2 * ‖clip β w‖ ^ 2 + (1 / 2 : ℝ) * ∑ i, positivePart (|w i| - β) ^ 2
        ≤ κ / 2 * β ^ 2 + (1 / 2 : ℝ) * ∑ i, positivePart (|w i| - β) ^ 2 :=
          add_le_add hclip_norm_scaled le_rfl
    _ ≤ κ / 2 * r ^ 2 + (1 / 2 : ℝ) * ∑ i, positivePart (|w i| - r) ^ 2 := by
      rw [hequation] at hsupport_sum
      calc
        κ / 2 * β ^ 2 + (1 / 2 : ℝ) * ∑ i, positivePart (|w i| - β) ^ 2
            ≤ (κ / 2 * β ^ 2 + (1 / 2 : ℝ) * ∑ i, positivePart (|w i| - β) ^ 2) +
                κ / 2 * (r - β) ^ 2 := by
              exact le_add_of_nonneg_right (mul_nonneg (by positivity) (sq_nonneg _))
        _ = κ / 2 * r ^ 2 +
              ((1 / 2 : ℝ) * ∑ i, positivePart (|w i| - β) ^ 2 -
                κ * β * (r - β)) := by ring
        _ ≤ κ / 2 * r ^ 2 + (1 / 2 : ℝ) * ∑ i, positivePart (|w i| - r) ^ 2 :=
              add_le_add le_rfl hsupport_sum
    _ ≤ κ / 2 * ‖x‖ ^ 2 + (1 / 2 : ℝ) * ∑ i, (x i - w i) ^ 2 := by
      dsimp [r]
      exact add_le_add le_rfl hdistance_scaled

/-! ## The decreasing-sort formula for the threshold -/

/-- Sum of the coordinates strictly before an index in a decreasing vector. -/
def priorSum {m : ℕ} (v : Fin (m + 1) → ℝ) (j : Fin (m + 1)) : ℝ :=
  ∑ i ∈ Finset.Iio j, v i

/-- Sum of the coordinates through an index in a decreasing vector. -/
def prefixSum {m : ℕ} (v : Fin (m + 1) → ℝ) (j : Fin (m + 1)) : ℝ :=
  ∑ i ∈ Finset.Iic j, v i

/-- The corrected active-index test, with the coefficient `κ + (j - 1)`. -/
def IsAdmissibleIndex {m : ℕ} (κ : ℝ) (v : Fin (m + 1) → ℝ)
    (j : Fin (m + 1)) : Prop :=
  priorSum v j < (κ + (j : ℕ)) * v j

/-- An admissible index after which no later index is admissible. -/
def IsGreatestAdmissibleIndex {m : ℕ} (κ : ℝ) (v : Fin (m + 1) → ℝ)
    (j : Fin (m + 1)) : Prop :=
  IsAdmissibleIndex κ v j ∧
    ∀ k, IsAdmissibleIndex κ v k → k ≤ j

/-- The corrected threshold attached to an active index. -/
noncomputable def sortedThreshold {m : ℕ} (κ : ℝ) (v : Fin (m + 1) → ℝ)
    (j : Fin (m + 1)) : ℝ :=
  prefixSum v j / (κ + ((j : ℕ) + 1))

lemma prefixSum_eq_priorSum_add {m : ℕ} (v : Fin (m + 1) → ℝ)
    (j : Fin (m + 1)) :
    prefixSum v j = priorSum v j + v j := by
  classical
  rw [prefixSum, priorSum, ← Finset.Iio_insert j,
    Finset.sum_insert (by simp)]
  ring

lemma first_pos_of_antitone_nonnegative_ne_zero {m : ℕ}
    {v : Fin (m + 1) → ℝ} (hvmono : Antitone v)
    (hvnonneg : ∀ i, 0 ≤ v i) (hvzero : v ≠ 0) :
    0 < v 0 := by
  have hv0nonneg := hvnonneg 0
  apply lt_of_le_of_ne hv0nonneg
  intro hv0
  apply hvzero
  funext i
  apply le_antisymm
  · calc
      v i ≤ v 0 := hvmono (Fin.zero_le i)
      _ = 0 := hv0.symm
  · exact hvnonneg i

lemma zero_isAdmissibleIndex {m : ℕ} {κ : ℝ} {v : Fin (m + 1) → ℝ}
    (hκ : 0 < κ) (hv0 : 0 < v 0) :
    IsAdmissibleIndex κ v 0 := by
  simp [IsAdmissibleIndex, priorSum]
  positivity

/-- Every nonempty finite active-index set has its source-defined maximum. -/
theorem exists_greatestAdmissibleIndex {m : ℕ} {κ : ℝ}
    {v : Fin (m + 1) → ℝ} (hzero : IsAdmissibleIndex κ v 0) :
    ∃ j, IsGreatestAdmissibleIndex κ v j := by
  classical
  let active : Finset (Fin (m + 1)) :=
    Finset.univ.filter (IsAdmissibleIndex κ v)
  have hactive : active.Nonempty := by
    refine ⟨0, ?_⟩
    simp [active, hzero]
  let j := active.max' hactive
  refine ⟨j, ?_, ?_⟩
  · have hjmem := Finset.max'_mem active hactive
    simpa [active] using hjmem
  · intro k hk
    apply Finset.le_max' active k
    simp [active, hk]

/--
The maximal corrected active index gives a positive threshold, separates the
active and inactive sorted coordinates, and solves the threshold equation.
-/
theorem sortedThreshold_spec {m : ℕ} {κ : ℝ} {v : Fin (m + 1) → ℝ}
    (hκ : 0 < κ) (hvmono : Antitone v) (hvnonneg : ∀ i, 0 ≤ v i)
    {j : Fin (m + 1)} (hj : IsGreatestAdmissibleIndex κ v j) :
    let β := sortedThreshold κ v j
    0 < β ∧
      (∀ i, i ≤ j → β < v i) ∧
      (∀ i, j < i → v i ≤ β) ∧
      ThresholdEquation κ β v := by
  classical
  let β := sortedThreshold κ v j
  let denominator : ℝ := κ + ((j : ℕ) + 1)
  have hdenominator : 0 < denominator := by
    dsimp [denominator]
    positivity
  have hprior_nonneg : 0 ≤ priorSum v j := by
    exact Finset.sum_nonneg fun i _ => hvnonneg i
  have hcoefficient_pos : 0 < κ + (j : ℕ) := by positivity
  have hvj_pos : 0 < v j := by
    have hproduct_pos : 0 < (κ + (j : ℕ)) * v j :=
      lt_of_le_of_lt hprior_nonneg hj.1
    rcases mul_pos_iff.mp hproduct_pos with hpositive | hnegative
    · exact hpositive.2
    · exact (not_lt_of_ge hcoefficient_pos.le hnegative.1).elim
  have hprefix_pos : 0 < prefixSum v j := by
    rw [prefixSum_eq_priorSum_add]
    positivity
  have hβ_pos : 0 < β := by
    exact div_pos hprefix_pos hdenominator
  have hprefix_lt : prefixSum v j < denominator * v j := by
    rw [prefixSum_eq_priorSum_add]
    dsimp [denominator]
    have hjadm := hj.1
    rw [IsAdmissibleIndex] at hjadm
    nlinarith
  have hβ_lt_vj : β < v j := by
    rw [show β = prefixSum v j / denominator by rfl]
    exact (div_lt_iff₀ hdenominator).2 (by simpa [mul_comm] using hprefix_lt)
  have hactive : ∀ i, i ≤ j → β < v i := by
    intro i hi
    exact hβ_lt_vj.trans_le (hvmono hi)
  have hinactive : ∀ i, j < i → v i ≤ β := by
    intro i hji
    have hnextBound : j.val + 1 < m + 1 := by omega
    let next : Fin (m + 1) := ⟨j.val + 1, hnextBound⟩
    have hjnext : j < next := by
      change j.val < j.val + 1
      omega
    have hnextNot : ¬ IsAdmissibleIndex κ v next := by
      intro hnext
      have hnext_le := hj.2 next hnext
      exact (not_le_of_gt hjnext) hnext_le
    have hprior_next : priorSum v next = prefixSum v j := by
      dsimp [priorSum, prefixSum]
      apply Finset.sum_congr
      · ext k
        simp only [Finset.mem_Iio, Finset.mem_Iic]
        change k.val < j.val + 1 ↔ k.val ≤ j.val
        omega
      · intro k _
        rfl
    have hnext_product : denominator * v next ≤ prefixSum v j := by
      rw [IsAdmissibleIndex, hprior_next] at hnextNot
      have hnotlt := not_lt.mp hnextNot
      simpa [denominator, next, mul_comm] using hnotlt
    have hnext_le_beta : v next ≤ β := by
      rw [show β = prefixSum v j / denominator by rfl]
      exact (le_div_iff₀ hdenominator).2 (by simpa [mul_comm] using hnext_product)
    have hnext_le_i : next ≤ i := by
      change j.val + 1 ≤ i.val
      omega
    exact (hvmono hnext_le_i).trans hnext_le_beta
  have hsum_support :
      ∑ i, positivePart (|v i| - β) =
        ∑ i ∈ Finset.Iic j, positivePart (|v i| - β) := by
    symm
    apply Finset.sum_subset (by simp)
    intro i _ hi
    have hji : j < i := lt_of_not_ge (by simpa using hi)
    have hvi := hinactive i hji
    have habs : |v i| = v i := abs_of_nonneg (hvnonneg i)
    rw [habs, positivePart_eq_zero_of_le (sub_nonpos.mpr hvi)]
  have hsum_active :
      ∑ i ∈ Finset.Iic j, positivePart (|v i| - β) =
        prefixSum v j - (((j : ℕ) : ℝ) + 1) * β := by
    calc
      ∑ i ∈ Finset.Iic j, positivePart (|v i| - β) =
          ∑ i ∈ Finset.Iic j, (v i - β) := by
            apply Finset.sum_congr rfl
            intro i hi
            have hi_le : i ≤ j := Finset.mem_Iic.mp hi
            rw [abs_of_nonneg (hvnonneg i)]
            exact positivePart_eq_self_of_nonneg (sub_nonneg.mpr (hactive i hi_le).le)
      _ = prefixSum v j - (((j : ℕ) : ℝ) + 1) * β := by
        rw [Finset.sum_sub_distrib, prefixSum]
        simp [Fin.card_Iic, nsmul_eq_mul]
  have hdenominator_mul : denominator * β = prefixSum v j := by
    rw [show β = prefixSum v j / denominator by rfl]
    calc
      denominator * (prefixSum v j / denominator) =
          (prefixSum v j / denominator) * denominator := mul_comm _ _
      _ = prefixSum v j := div_mul_cancel₀ _ hdenominator.ne'
  have hequation : ThresholdEquation κ β v := by
    rw [ThresholdEquation, hsum_support, hsum_active]
    dsimp [denominator] at hdenominator_mul
    calc
      prefixSum v j - ((↑j : ℝ) + 1) * β =
          (κ + ((↑j : ℝ) + 1)) * β - ((↑j : ℝ) + 1) * β := by
            rw [hdenominator_mul]
      _ = κ * β := by ring
  exact ⟨hβ_pos, hactive, hinactive, hequation⟩

/-- The corrected sorted threshold exists for every nonzero decreasing nonnegative vector. -/
theorem exists_sortedThreshold {m : ℕ} {κ : ℝ} {v : Fin (m + 1) → ℝ}
    (hκ : 0 < κ) (hvmono : Antitone v) (hvnonneg : ∀ i, 0 ≤ v i)
    (hvzero : v ≠ 0) :
    ∃ j, IsGreatestAdmissibleIndex κ v j ∧
      let β := sortedThreshold κ v j
      0 < β ∧ ThresholdEquation κ β v := by
  have hv0 := first_pos_of_antitone_nonnegative_ne_zero hvmono hvnonneg hvzero
  obtain ⟨j, hj⟩ := exists_greatestAdmissibleIndex (zero_isAdmissibleIndex hκ hv0)
  refine ⟨j, hj, ?_⟩
  have hspec := sortedThreshold_spec hκ hvmono hvnonneg hj
  exact ⟨hspec.1, hspec.2.2.2⟩

/-- A sorting permutation transports the threshold equation back to the unsorted vector. -/
lemma thresholdEquation_of_sortedPermutation {m : ℕ} {κ β : ℝ}
    {w v : Fin (m + 1) → ℝ} (permutation : Equiv.Perm (Fin (m + 1)))
    (hv : ∀ i, v i = |w (permutation i)|)
    (hequation : ThresholdEquation κ β v) :
    ThresholdEquation κ β w := by
  rw [ThresholdEquation] at hequation ⊢
  calc
    ∑ i, positivePart (|w i| - β) =
        ∑ i, positivePart (|w (permutation i)| - β) := by
          exact (Equiv.sum_comp permutation (fun i => positivePart (|w i| - β))).symm
    _ = ∑ i, positivePart (|v i| - β) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hv, abs_abs]
    _ = κ * β := hequation

/--
Corrected sorting-and-clipping formula for the proximal minimizer of a squared
finite sup norm.
-/
theorem exists_sorted_clip_minimizer {m : ℕ} {κ : ℝ}
    {w v : Fin (m + 1) → ℝ} (hκ : 0 < κ)
    (hvmono : Antitone v) (hvnonneg : ∀ i, 0 ≤ v i) (hvzero : v ≠ 0)
    (permutation : Equiv.Perm (Fin (m + 1)))
    (hv : ∀ i, v i = |w (permutation i)|) :
    ∃ j, IsGreatestAdmissibleIndex κ v j ∧
      let β := sortedThreshold κ v j
      0 < β ∧ ∀ x, objective κ w (clip β w) ≤ objective κ w x := by
  obtain ⟨j, hj, hβ, hequation⟩ :=
    exists_sortedThreshold hκ hvmono hvnonneg hvzero
  refine ⟨j, hj, hβ, ?_⟩
  have hequationW := thresholdEquation_of_sortedPermutation permutation hv hequation
  intro x
  exact clip_minimizes_objective hκ hβ.le w x hequationW

end SquaredLInfProx
end AppliedModelingLib
