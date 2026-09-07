import Mathlib.Topology.Order.IntermediateValue
import GCG24UserItemFairness.Symmetrization

namespace GCG24UserItemFairness

/-!
Scalar algebra for the two-opposing-type models used in Theorems 3 and 4.

The paper writes this quantity as
`q_j(α) = α v_j / (α v_j + (1 - α) v_{n-j+1})`.
-/
namespace OpposingTypes

/-- The normalized contribution share of the first type for one item pair. -/
noncomputable def typeOneShare (alpha left right : ℝ) : ℝ :=
  alpha * left / (alpha * left + (1 - alpha) * right)

/-- The denominator in `q_j(α)` is positive for interior `α` and positive utilities. -/
theorem typeOneShare_denom_pos
    {alpha left right : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hleft : 0 < left) (hright : 0 < right) :
    0 < alpha * left + (1 - alpha) * right := by
  exact add_pos (mul_pos halpha0 hleft)
    (mul_pos (sub_pos.mpr halpha1) hright)

/-- `q_j(α)` is positive for interior `α` and positive utilities. -/
theorem typeOneShare_pos
    {alpha left right : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hleft : 0 < left) (hright : 0 < right) :
    0 < typeOneShare alpha left right := by
  unfold typeOneShare
  exact div_pos (mul_pos halpha0 hleft)
    (typeOneShare_denom_pos halpha0 halpha1 hleft hright)

/-- `q_j(α)` is less than one for interior `α` and positive utilities. -/
theorem typeOneShare_lt_one
    {alpha left right : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hleft : 0 < left) (hright : 0 < right) :
    typeOneShare alpha left right < 1 := by
  unfold typeOneShare
  have hden := typeOneShare_denom_pos halpha0 halpha1 hleft hright
  rw [div_lt_one hden]
  nlinarith [mul_pos (sub_pos.mpr halpha1) hright]

/-- The complementary share `1 - q_j(α)` is positive. -/
theorem one_sub_typeOneShare_pos
    {alpha left right : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hleft : 0 < left) (hright : 0 < right) :
    0 < 1 - typeOneShare alpha left right := by
  have hlt := typeOneShare_lt_one halpha0 halpha1 hleft hright
  linarith

/-- On `(0,1)`, `q/(1-q)` is monotone increasing in `q`. -/
theorem ratio_self_one_sub_mono_of_le
    {q q' : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hq0' : 0 < q') (hq1' : q' < 1) (hle : q ≤ q') :
    q / (1 - q) ≤ q' / (1 - q') := by
  have hden : 0 < 1 - q := sub_pos.mpr hq1
  have hden' : 0 < 1 - q' := sub_pos.mpr hq1'
  rw [div_le_div_iff₀ hden hden']
  nlinarith

/-- On `(0,1)`, `(1-q)/q` is monotone decreasing in `q`. -/
theorem ratio_one_sub_self_antitone_of_le
    {q q' : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hq0' : 0 < q') (hq1' : q' < 1) (hle : q ≤ q') :
    (1 - q') / q' ≤ (1 - q) / q := by
  rw [div_le_div_iff₀ hq0' hq0]
  nlinarith

/-- Algebraic complement form: `1 - q = (1-α) right / denominator`. -/
theorem one_sub_typeOneShare_eq
    {alpha left right : ℝ}
    (hden : alpha * left + (1 - alpha) * right ≠ 0) :
    1 - typeOneShare alpha left right =
      (1 - alpha) * right /
        (alpha * left + (1 - alpha) * right) := by
  unfold typeOneShare
  field_simp [hden]
  ring

/--
Appendix D, Lemma 11 scalar monotonicity template.  This is the derivative-sign
calculation in two-point form: if `B*X ≤ A*C`, then
`(C + α(X-C))/(B + α(A-B))` decreases as `α` increases.
-/
theorem lemma11_affine_ratio_antitone_of_cross
    {A B C X alpha alpha' : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (hA : 0 < A) (hB : 0 < B)
    (hcross : B * X ≤ A * C) :
    (C + alpha' * (X - C)) / (B + alpha' * (A - B)) ≤
      (C + alpha * (X - C)) / (B + alpha * (A - B)) := by
  have hD : 0 < B + alpha * (A - B) := by
    have h :=
      typeOneShare_denom_pos halpha0 halpha1 hA hB
    convert h using 1
    ring
  have hD' : 0 < B + alpha' * (A - B) := by
    have h :=
      typeOneShare_denom_pos halpha0' halpha1' hA hB
    convert h using 1
    ring
  rw [div_le_div_iff₀ hD' hD]
  have hprod :
      (alpha' - alpha) * (B * X - A * C) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos
      (sub_nonneg.mpr halpha_le) (sub_nonpos.mpr hcross)
  nlinarith

/--
Appendix D, Lemma 11 scalar algebra for a mirror-paired pre-pivot term.
-/
theorem lemma11_paired_ratio_sum_scalar_eq
    {A B X Y alpha : ℝ}
    (hX : X ≠ 0)
    (hD : alpha * A + (1 - alpha) * B ≠ 0) :
    A / X * ((alpha * X + (1 - alpha) * Y) /
        (alpha * A + (1 - alpha) * B)) +
      B / X * ((alpha * Y + (1 - alpha) * X) /
        (alpha * A + (1 - alpha) * B)) =
      1 + Y / X * (((1 - alpha) * A + alpha * B) /
        (alpha * A + (1 - alpha) * B)) := by
  let D : ℝ := alpha * A + (1 - alpha) * B
  have hDnz : D ≠ 0 := by
    simpa [D] using hD
  change A / X * ((alpha * X + (1 - alpha) * Y) / D) +
      B / X * ((alpha * Y + (1 - alpha) * X) / D) =
    1 + Y / X * (((1 - alpha) * A + alpha * B) / D)
  field_simp [hX, hDnz]
  ring

/--
Lemma 6 scalar algebra: the inverse share gap for mirror items expands to the
paper's denominator-cleared expression.
-/
theorem typeOneShare_inv_sub_inv_one_sub_reverse_eq
    {alpha left right : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hleft : 0 < left) (hright : 0 < right) :
    (typeOneShare alpha left right)⁻¹ -
        (1 - typeOneShare alpha right left)⁻¹ =
      right / left * (1 - 2 * alpha) / (alpha * (1 - alpha)) := by
  have hden₁ :=
    typeOneShare_denom_pos halpha0 halpha1 hleft hright
  have hden₂ :=
    typeOneShare_denom_pos halpha0 halpha1 hright hleft
  have hq₁ :
      typeOneShare alpha left right ≠ 0 :=
    ne_of_gt (typeOneShare_pos halpha0 halpha1 hleft hright)
  have hq₂ :
      1 - typeOneShare alpha right left ≠ 0 :=
    ne_of_gt (one_sub_typeOneShare_pos halpha0 halpha1 hright hleft)
  have halpha_ne : alpha ≠ 0 := ne_of_gt halpha0
  have hone_sub_ne : 1 - alpha ≠ 0 := ne_of_gt (sub_pos.mpr halpha1)
  have hleft_ne : left ≠ 0 := ne_of_gt hleft
  have halpha_left_ne : alpha * left ≠ 0 :=
    mul_ne_zero halpha_ne hleft_ne
  have honesub_left_ne : (1 - alpha) * left ≠ 0 :=
    mul_ne_zero hone_sub_ne hleft_ne
  have hinv_left :
      (typeOneShare alpha left right)⁻¹ =
        (alpha * left + (1 - alpha) * right) / (alpha * left) := by
    unfold typeOneShare
    field_simp [hden₁.ne', halpha_left_ne]
  have hinv_right :
      (1 - typeOneShare alpha right left)⁻¹ =
        (alpha * right + (1 - alpha) * left) / ((1 - alpha) * left) := by
    unfold typeOneShare
    field_simp [hden₂.ne', honesub_left_ne]
    ring
  rw [hinv_left, hinv_right]
  field_simp [halpha_ne, hone_sub_ne, hleft_ne]
  ring_nf

/--
Appendix D, Lemma 9, scalar alpha-monotonicity component:
`q_j(α)` strictly increases as `α` increases.
-/
theorem typeOneShare_strictMono_alpha
    {alpha alpha' left right : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (hlt : alpha < alpha')
    (hleft : 0 < left) (hright : 0 < right) :
    typeOneShare alpha left right <
      typeOneShare alpha' left right := by
  unfold typeOneShare
  have hden :=
    typeOneShare_denom_pos halpha0 halpha1 hleft hright
  have hden' :=
    typeOneShare_denom_pos halpha0' halpha1' hleft hright
  rw [div_lt_div_iff₀ hden hden']
  ring_nf
  have hprod : 0 < left * right := mul_pos hleft hright
  nlinarith [hprod, hlt]

/--
For fixed `α`, the share decreases when the opposing-value ratio
`right / left` increases, stated in denominator-cleared form.
-/
theorem typeOneShare_lt_of_cross_mul_lt
    {alpha left right left' right' : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hleft : 0 < left) (hright : 0 < right)
    (hleft' : 0 < left') (hright' : 0 < right')
    (hcross : right * left' < right' * left) :
    typeOneShare alpha left' right' <
      typeOneShare alpha left right := by
  unfold typeOneShare
  have hden :=
    typeOneShare_denom_pos halpha0 halpha1 hleft hright
  have hden' :=
    typeOneShare_denom_pos halpha0 halpha1 hleft' hright'
  rw [div_lt_div_iff₀ hden' hden]
  ring_nf
  have hscale : 0 < alpha * (1 - alpha) :=
    mul_pos halpha0 (sub_pos.mpr halpha1)
  nlinarith [hscale, hcross]

/--
Appendix E, Lemma 16, scalar midpoint component: at `α = 1/2`, the share is
above `1/2` when the left utility exceeds the right utility.
-/
theorem half_lt_typeOneShare_half_of_right_lt_left
    {left right : ℝ}
    (hleft : 0 < left) (hright : 0 < right) (hlt : right < left) :
    (1 / 2 : ℝ) < typeOneShare (1 / 2) left right := by
  unfold typeOneShare
  have hden : 0 < (1 / 2 : ℝ) * left + (1 - (1 / 2 : ℝ)) * right := by
    norm_num
    nlinarith [hleft, hright]
  rw [lt_div_iff₀ hden]
  nlinarith

/--
Appendix E, Lemma 16, scalar midpoint component: at `α = 1/2`, the share is
below `1/2` when the left utility is below the right utility.
-/
theorem typeOneShare_half_lt_half_of_left_lt_right
    {left right : ℝ}
    (hleft : 0 < left) (hright : 0 < right) (hlt : left < right) :
    typeOneShare (1 / 2) left right < (1 / 2 : ℝ) := by
  unfold typeOneShare
  have hden : 0 < (1 / 2 : ℝ) * left + (1 - (1 / 2 : ℝ)) * right := by
    norm_num
    nlinarith [hleft, hright]
  rw [div_lt_iff₀ hden]
  nlinarith

/--
Appendix E, Lemma 16, scalar midpoint component: at `α = 1/2`, equal opposing
utilities give share exactly `1/2`.
-/
theorem typeOneShare_half_eq_half_of_eq
    {left right : ℝ}
    (hleft : 0 < left) (heq : left = right) :
    typeOneShare (1 / 2) left right = (1 / 2 : ℝ) := by
  subst right
  unfold typeOneShare
  have hden : (1 / 2 : ℝ) * left + (1 - (1 / 2 : ℝ)) * left ≠ 0 := by
    norm_num
    exact ne_of_gt hleft
  field_simp [hden]
  ring

/--
At `α = 1/2`, mirror shares are complementary:
`q(left,right) + q(right,left) = 1`.
-/
theorem typeOneShare_half_add_reverse_eq_one
    {left right : ℝ}
    (hleft : 0 < left) (hright : 0 < right) :
    typeOneShare (1 / 2) left right +
        typeOneShare (1 / 2) right left = 1 := by
  unfold typeOneShare
  have hden₁ :
      (1 / 2 : ℝ) * left + (1 - (1 / 2 : ℝ)) * right ≠ 0 := by
    have hpos : 0 <
        (1 / 2 : ℝ) * left + (1 - (1 / 2 : ℝ)) * right := by
      nlinarith
    exact ne_of_gt hpos
  have hden₂ :
      (1 / 2 : ℝ) * right + (1 - (1 / 2 : ℝ)) * left ≠ 0 := by
    have hpos : 0 <
        (1 / 2 : ℝ) * right + (1 - (1 / 2 : ℝ)) * left := by
      nlinarith
    exact ne_of_gt hpos
  field_simp [hden₁, hden₂]
  ring

/-- The opposite item index `n - j + 1` in zero-based `Fin n` notation. -/
def reverseItem {n : ℕ} (j : Item n) : Item n :=
  ⟨n - 1 - j.val, by omega⟩

/-- Reversing the opposite item index returns the original item. -/
theorem reverseItem_reverseItem {n : ℕ} (j : Item n) :
    reverseItem (reverseItem j) = j := by
  ext
  simp [reverseItem]
  omega

/-- The first item in zero-based Lean notation, corresponding to paper index `1`. -/
def firstItem {n : ℕ} [NeZero n] : Item n :=
  ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩

/-- The last item in zero-based Lean notation, corresponding to paper index `n`. -/
def lastItem {n : ℕ} [NeZero n] : Item n :=
  reverseItem firstItem

@[simp] theorem firstItem_val {n : ℕ} [NeZero n] :
    (firstItem : Item n).val = 0 := rfl

@[simp] theorem lastItem_val {n : ℕ} [NeZero n] :
    (lastItem : Item n).val = n - 1 := by
  simp [lastItem, firstItem, reverseItem]

@[simp] theorem reverseItem_lastItem {n : ℕ} [NeZero n] :
    reverseItem (lastItem : Item n) = firstItem := by
  simp [lastItem, reverseItem_reverseItem]

/-- Reversal as a finite equivalence on item indices. -/
def reverseItemEquiv (n : ℕ) : Item n ≃ Item n where
  toFun := reverseItem
  invFun := reverseItem
  left_inv := reverseItem_reverseItem
  right_inv := reverseItem_reverseItem

/-- Reindex a finite sum by item reversal. -/
theorem sum_reverseItem {n : ℕ} (f : Item n → ℝ) :
    (∑ j : Item n, f (reverseItem j)) = ∑ j : Item n, f j := by
  simpa [reverseItemEquiv] using
    (Equiv.sum_comp (reverseItemEquiv n) f)

/-- Reindexing by item reversal preserves finite maxima. -/
theorem finiteMax_reverseItem {n : ℕ} [NeZero n] (v : Item n → ℝ) :
    AppliedModelingLib.finiteMax (fun j : Item n => v (reverseItem j)) =
      AppliedModelingLib.finiteMax v := by
  apply le_antisymm
  · obtain ⟨j, hj⟩ :=
      AppliedModelingLib.exists_finiteMax_eq
        (fun j : Item n => v (reverseItem j))
    rw [hj]
    exact AppliedModelingLib.le_finiteMax v (reverseItem j)
  · obtain ⟨j, hj⟩ := AppliedModelingLib.exists_finiteMax_eq v
    rw [hj]
    have hle :=
      AppliedModelingLib.le_finiteMax
        (fun j : Item n => v (reverseItem j)) (reverseItem j)
    simpa [reverseItem_reverseItem] using hle

/-- Reindexing by item reversal preserves finite minima. -/
theorem finiteMin_reverseItem {n : ℕ} [NeZero n] (v : Item n → ℝ) :
    AppliedModelingLib.finiteMin (fun j : Item n => v (reverseItem j)) =
      AppliedModelingLib.finiteMin v := by
  apply le_antisymm
  · refine AppliedModelingLib.le_finiteMin v ?_
    intro j
    have hle :=
      AppliedModelingLib.finiteMin_le
        (fun j : Item n => v (reverseItem j)) (reverseItem j)
    simpa [reverseItem_reverseItem] using hle
  · refine AppliedModelingLib.le_finiteMin (fun j : Item n => v (reverseItem j)) ?_
    intro j
    exact AppliedModelingLib.finiteMin_le v (reverseItem j)

/-- The indexed `q_j(α)` used in the opposing-preference proofs. -/
noncomputable def pairShare {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) (j : Item n) : ℝ :=
  typeOneShare alpha (v j) (v (reverseItem j))

/--
Appendix D, Lemma 6, indexed mirror-pair algebra:
`1/q_j - 1/(1-q_{n-j+1})` has the paper's closed form.
-/
theorem pairShare_inv_sub_inv_one_sub_reverse_eq
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} (j : Item n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j) :
    (pairShare alpha v j)⁻¹ -
        (1 - pairShare alpha v (reverseItem j))⁻¹ =
      v (reverseItem j) / v j * (1 - 2 * alpha) /
        (alpha * (1 - alpha)) := by
  unfold pairShare
  rw [reverseItem_reverseItem]
  exact typeOneShare_inv_sub_inv_one_sub_reverse_eq
    halpha0 halpha1 (hpos j) (hpos (reverseItem j))

/--
Appendix D, Lemma 6, indexed mirror-pair inequality for `α ≤ 1/2`.
-/
theorem pairShare_inv_sub_inv_one_sub_reverse_nonneg_of_alpha_le_half
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} (j : Item n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha_half : alpha ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j) :
    0 ≤ (pairShare alpha v j)⁻¹ -
        (1 - pairShare alpha v (reverseItem j))⁻¹ := by
  rw [pairShare_inv_sub_inv_one_sub_reverse_eq
    j halpha0 halpha1 hpos]
  have hratio : 0 ≤ v (reverseItem j) / v j :=
    div_nonneg (hpos (reverseItem j)).le (hpos j).le
  have hnum : 0 ≤ 1 - 2 * alpha := by
    nlinarith
  have hden : 0 ≤ alpha * (1 - alpha) :=
    (mul_pos halpha0 (sub_pos.mpr halpha1)).le
  exact div_nonneg (mul_nonneg hratio hnum) hden

/--
Appendix D, Lemma 11 algebra: ratio of two indexed `q` terms after expanding
their denominators.
-/
theorem pairShare_div_pairShare_eq
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} (t j : Item n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j) :
    pairShare alpha v t / pairShare alpha v j =
      (v t / v j) *
        ((alpha * v j + (1 - alpha) * v (reverseItem j)) /
          (alpha * v t + (1 - alpha) * v (reverseItem t))) := by
  unfold pairShare typeOneShare
  have hDt :
      alpha * v t + (1 - alpha) * v (reverseItem t) ≠ 0 :=
    ne_of_gt (typeOneShare_denom_pos halpha0 halpha1
      (hpos t) (hpos (reverseItem t)))
  have hDj :
      alpha * v j + (1 - alpha) * v (reverseItem j) ≠ 0 :=
    ne_of_gt (typeOneShare_denom_pos halpha0 halpha1
      (hpos j) (hpos (reverseItem j)))
  have halpha_ne : alpha ≠ 0 := ne_of_gt halpha0
  have hvj_ne : v j ≠ 0 := ne_of_gt (hpos j)
  field_simp [hDt, hDj, halpha_ne, hvj_ne]

/--
Appendix D, Lemma 11 algebra: ratio of two indexed complement terms
`1-q`.
-/
theorem one_sub_pairShare_div_one_sub_pairShare_eq
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} (t j : Item n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j) :
    (1 - pairShare alpha v t) / (1 - pairShare alpha v j) =
      (v (reverseItem t) / v (reverseItem j)) *
        ((alpha * v j + (1 - alpha) * v (reverseItem j)) /
          (alpha * v t + (1 - alpha) * v (reverseItem t))) := by
  unfold pairShare
  have hDt :
      alpha * v t + (1 - alpha) * v (reverseItem t) ≠ 0 :=
    ne_of_gt (typeOneShare_denom_pos halpha0 halpha1
      (hpos t) (hpos (reverseItem t)))
  have hDj :
      alpha * v j + (1 - alpha) * v (reverseItem j) ≠ 0 :=
    ne_of_gt (typeOneShare_denom_pos halpha0 halpha1
      (hpos j) (hpos (reverseItem j)))
  rw [one_sub_typeOneShare_eq hDt, one_sub_typeOneShare_eq hDj]
  have hone_sub_ne : 1 - alpha ≠ 0 := ne_of_gt (sub_pos.mpr halpha1)
  have hvrevj_ne : v (reverseItem j) ≠ 0 :=
    ne_of_gt (hpos (reverseItem j))
  field_simp [hDt, hDj, hone_sub_ne, hvrevj_ne]

/--
Appendix D, Lemma 11 mirror-paired pre-pivot algebra:
`q_t/q_j + (1-q_t)/(1-q_{n-j+1})` equals the paper's `h_t(α)` expression.
-/
theorem lemma11_paired_q_term_eq
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} (t j : Item n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j) :
    pairShare alpha v t / pairShare alpha v j +
        (1 - pairShare alpha v t) /
          (1 - pairShare alpha v (reverseItem j)) =
      1 + (v (reverseItem j) / v j) *
        (((1 - alpha) * v t + alpha * v (reverseItem t)) /
          (alpha * v t + (1 - alpha) * v (reverseItem t))) := by
  rw [pairShare_div_pairShare_eq t j halpha0 halpha1 hpos,
    one_sub_pairShare_div_one_sub_pairShare_eq
      t (reverseItem j) halpha0 halpha1 hpos]
  simp [reverseItem_reverseItem]
  exact lemma11_paired_ratio_sum_scalar_eq
    (A := v t) (B := v (reverseItem t)) (X := v j)
    (Y := v (reverseItem j)) (alpha := alpha)
    (ne_of_gt (hpos j))
    (ne_of_gt (typeOneShare_denom_pos halpha0 halpha1
      (hpos t) (hpos (reverseItem t))))

/--
Appendix D, Lemma 10 setup: at `α = 1/2`, opposite items have complementary
shares.
-/
theorem pairShare_half_add_reverse_eq_one
    {n : ℕ} {v : Item n → ℝ} (j : Item n)
    (hpos : ∀ j : Item n, 0 < v j) :
    pairShare (1 / 2) v j +
        pairShare (1 / 2) v (reverseItem j) = 1 := by
  unfold pairShare
  rw [reverseItem_reverseItem]
  exact typeOneShare_half_add_reverse_eq_one
    (hpos j) (hpos (reverseItem j))

/--
Appendix D, Lemma 10 setup: `q_j(1/2) = 1 - q_{n-j+1}(1/2)`.
-/
theorem pairShare_half_eq_one_sub_reverse
    {n : ℕ} {v : Item n → ℝ} (j : Item n)
    (hpos : ∀ j : Item n, 0 < v j) :
    pairShare (1 / 2) v j =
      1 - pairShare (1 / 2) v (reverseItem j) := by
  have hsum := pairShare_half_add_reverse_eq_one j hpos
  linarith

/-- Values are strictly decreasing in the item index, matching `v₁ > ... > vₙ`. -/
def StrictlyDecreasingByIndex {n : ℕ} (v : Item n → ℝ) : Prop :=
  ∀ ⦃i j : Item n⦄, i.val < j.val → v j < v i

/-- Non-strict form of `StrictlyDecreasingByIndex`. -/
theorem value_antitone_of_val_le {n : ℕ} {v : Item n → ℝ}
    (hdec : StrictlyDecreasingByIndex v) {i j : Item n}
    (hij : i.val ≤ j.val) :
    v j ≤ v i := by
  rcases lt_or_eq_of_le hij with hlt | heq
  · exact (hdec hlt).le
  · have hji : j = i := Fin.ext heq.symm
    subst j
    rfl

/-- A strictly decreasing value vector attains its finite maximum at item `1`. -/
theorem finiteMax_eq_firstItem {n : ℕ} [NeZero n] {v : Item n → ℝ}
    (hdec : StrictlyDecreasingByIndex v) :
    AppliedModelingLib.finiteMax v = v firstItem := by
  apply le_antisymm
  · obtain ⟨j, hj⟩ := AppliedModelingLib.exists_finiteMax_eq v
    rw [hj]
    have hle : (firstItem : Item n).val ≤ j.val := by
      simp
    exact value_antitone_of_val_le hdec hle
  · exact AppliedModelingLib.le_finiteMax v firstItem

/--
Appendix D, Lemma 9, indexed alpha-monotonicity component:
for each item `j`, `q_j(α)` strictly increases with `α`.
-/
theorem pairShare_strictMono_alpha
    {n : ℕ} {alpha alpha' : ℝ} {v : Item n → ℝ} (j : Item n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (hlt : alpha < alpha')
    (hpos : ∀ j : Item n, 0 < v j) :
    pairShare alpha v j < pairShare alpha' v j := by
  exact typeOneShare_strictMono_alpha
    halpha0 halpha1 halpha0' halpha1' hlt (hpos j) (hpos (reverseItem j))

/--
Appendix D, Lemma 9, non-strict indexed alpha-monotonicity:
`q_j(α)` is weakly increasing in `α`.
-/
theorem pairShare_mono_alpha
    {n : ℕ} {alpha alpha' : ℝ} {v : Item n → ℝ} (j : Item n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (hpos : ∀ j : Item n, 0 < v j) :
    pairShare alpha v j ≤ pairShare alpha' v j := by
  rcases lt_or_eq_of_le halpha_le with hlt | heq
  · exact (pairShare_strictMono_alpha j
      halpha0 halpha1 halpha0' halpha1' hlt hpos).le
  · subst alpha'
    exact le_rfl

/-- The indexed share `q_j(α)` is positive. -/
theorem pairShare_pos
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} (j : Item n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j) :
    0 < pairShare alpha v j := by
  exact typeOneShare_pos halpha0 halpha1 (hpos j) (hpos (reverseItem j))

/-- The indexed share `q_j(α)` is less than one. -/
theorem pairShare_lt_one
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} (j : Item n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j) :
    pairShare alpha v j < 1 := by
  exact typeOneShare_lt_one halpha0 halpha1 (hpos j) (hpos (reverseItem j))

/-- The reciprocal `q_j(α)⁻¹` is weakly decreasing in `α`. -/
theorem pairShare_inv_antitone_alpha
    {n : ℕ} {alpha alpha' : ℝ} {v : Item n → ℝ} (j : Item n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (hpos : ∀ j : Item n, 0 < v j) :
    (pairShare alpha' v j)⁻¹ ≤ (pairShare alpha v j)⁻¹ := by
  have hq_le :
      pairShare alpha v j ≤ pairShare alpha' v j :=
    pairShare_mono_alpha j
      halpha0 halpha1 halpha0' halpha1' halpha_le hpos
  have h :=
    one_div_le_one_div_of_le
      (pairShare_pos j halpha0 halpha1 hpos) hq_le
  simpa [one_div] using h

/-- The indexed complementary share `1 - q_j(α)` is positive. -/
theorem one_sub_pairShare_pos
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} (j : Item n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j) :
    0 < 1 - pairShare alpha v j := by
  exact one_sub_typeOneShare_pos halpha0 halpha1 (hpos j) (hpos (reverseItem j))

/-- The scalar share `q_j(α)` is continuous on every compact subinterval of `(0,1)`. -/
theorem typeOneShare_continuousOn_Icc
    {alphaLeft alphaRight left right : ℝ}
    (halphaLeft0 : 0 < alphaLeft) (halphaRight1 : alphaRight < 1)
    (hleft : 0 < left) (hright : 0 < right) :
    ContinuousOn (fun alpha => typeOneShare alpha left right)
      (Set.Icc alphaLeft alphaRight) := by
  have hnum :
      ContinuousOn (fun alpha : ℝ => alpha * left)
        (Set.Icc alphaLeft alphaRight) :=
    continuousOn_id.mul continuousOn_const
  have hden :
      ContinuousOn
        (fun alpha : ℝ => alpha * left + (1 - alpha) * right)
        (Set.Icc alphaLeft alphaRight) :=
    hnum.add ((continuousOn_const.sub continuousOn_id).mul continuousOn_const)
  have hden_ne :
      ∀ alpha ∈ Set.Icc alphaLeft alphaRight,
        alpha * left + (1 - alpha) * right ≠ 0 := by
    intro alpha halpha
    exact ne_of_gt
      (typeOneShare_denom_pos
        (lt_of_lt_of_le halphaLeft0 halpha.1)
        (lt_of_le_of_lt halpha.2 halphaRight1)
        hleft hright)
  simpa [typeOneShare, div_eq_mul_inv] using hnum.mul (hden.inv₀ hden_ne)

/-- The indexed share `q_j(α)` is continuous on compact subintervals of `(0,1)`. -/
theorem pairShare_continuousOn_Icc
    {n : ℕ} {alphaLeft alphaRight : ℝ} {v : Item n → ℝ} (j : Item n)
    (halphaLeft0 : 0 < alphaLeft) (halphaRight1 : alphaRight < 1)
    (hpos : ∀ j : Item n, 0 < v j) :
    ContinuousOn (fun alpha => pairShare alpha v j)
      (Set.Icc alphaLeft alphaRight) := by
  exact typeOneShare_continuousOn_Icc
    halphaLeft0 halphaRight1 (hpos j) (hpos (reverseItem j))

/-- The complementary indexed share `1-q_j(α)` is continuous on compact subintervals. -/
theorem one_sub_pairShare_continuousOn_Icc
    {n : ℕ} {alphaLeft alphaRight : ℝ} {v : Item n → ℝ} (j : Item n)
    (halphaLeft0 : 0 < alphaLeft) (halphaRight1 : alphaRight < 1)
    (hpos : ∀ j : Item n, 0 < v j) :
    ContinuousOn (fun alpha => 1 - pairShare alpha v j)
      (Set.Icc alphaLeft alphaRight) := by
  exact continuousOn_const.sub
    (pairShare_continuousOn_Icc j halphaLeft0 halphaRight1 hpos)

/-- Reversing item indices flips strict order. -/
theorem reverseItem_val_lt_of_val_lt {n : ℕ} {i j : Item n}
    (hij : i.val < j.val) :
    (reverseItem j).val < (reverseItem i).val := by
  simp [reverseItem]
  omega

/--
Appendix D, Lemma 9, indexed item-monotonicity component:
for a strictly decreasing value vector, `q_j(α)` strictly decreases as the item
index `j` increases.
-/
theorem pairShare_strictAnti_index
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {i j : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hij : i.val < j.val) :
    pairShare alpha v j < pairShare alpha v i := by
  have hleft : 0 < v i := hpos i
  have hright : 0 < v (reverseItem i) := hpos (reverseItem i)
  have hleft' : 0 < v j := hpos j
  have hright' : 0 < v (reverseItem j) := hpos (reverseItem j)
  have hleft_lt : v j < v i := hdec hij
  have hrev_val : (reverseItem j).val < (reverseItem i).val :=
    reverseItem_val_lt_of_val_lt hij
  have hrev_lt : v (reverseItem i) < v (reverseItem j) :=
    hdec hrev_val
  have hcross :
      v (reverseItem i) * v j < v (reverseItem j) * v i := by
    have h1 :
        v (reverseItem i) * v j <
          v (reverseItem j) * v j := by
      exact mul_lt_mul_of_pos_right hrev_lt hleft'
    have h2 :
        v (reverseItem j) * v j <
          v (reverseItem j) * v i := by
      exact mul_lt_mul_of_pos_left hleft_lt hright'
    exact lt_trans h1 h2
  exact typeOneShare_lt_of_cross_mul_lt
    halpha0 halpha1 hleft hright hleft' hright' hcross

/--
Appendix D, Lemma 4 exchange algebra: if `q_i < q_j < 1`, then the coefficient
left in the item-`j` perturbation is strictly positive.
-/
theorem lemma4_exchange_margin_pos
    {qi qj : ℝ}
    (hqi1 : qi < 1) (hqij : qi < qj) :
    0 < qj - qi * ((1 - qj) / (1 - qi)) := by
  have hden : 0 < 1 - qi := sub_pos.mpr hqi1
  rw [sub_pos]
  have hmul :
      qi * ((1 - qj) / (1 - qi)) =
        qi * (1 - qj) / (1 - qi) := by
    ring
  rw [hmul]
  rw [div_lt_iff₀ hden]
  nlinarith

/--
Appendix D, Lemma 4 exchange algebra: the transfer from item `j` to item `i`
keeps `y_j` positive under the paper's equality relation.
-/
theorem lemma4_exchange_transfer_lt
    {qi qj c yi yj : ℝ}
    (hqi0 : 0 < qi) (hqi1 : qi < 1) (hqj1 : qj < 1)
    (hqij : qi < qj) (hc : 0 < c) (hyi : 0 ≤ yi)
    (heq : qi * c + (1 - qi) * yi = (1 - qj) * yj) :
    yi + qi * c / (1 - qi) < yj := by
  have hden_i : 0 < 1 - qi := sub_pos.mpr hqi1
  have hden_j : 0 < 1 - qj := sub_pos.mpr hqj1
  have hyj_pos : 0 < yj := by
    have hleft : 0 < qi * c + (1 - qi) * yi :=
      add_pos_of_pos_of_nonneg (mul_pos hqi0 hc)
        (mul_nonneg hden_i.le hyi)
    nlinarith
  have hrewrite :
      yi + qi * c / (1 - qi) =
        ((1 - qj) / (1 - qi)) * yj := by
    field_simp [ne_of_gt hden_i]
    nlinarith
  have hratio : (1 - qj) / (1 - qi) < 1 := by
    rw [div_lt_one hden_i]
    nlinarith
  calc
    yi + qi * c / (1 - qi)
        = ((1 - qj) / (1 - qi)) * yj := hrewrite
    _ < 1 * yj := mul_lt_mul_of_pos_right hratio hyj_pos
    _ = yj := by ring

/--
Appendix D, Lemma 4 exchange algebra: after the transfer, item `j` keeps more
than the original `y_i` mass.
-/
theorem lemma4_exchange_yj_sub_transfer_gt_yi
    {qi qj c yi yj : ℝ}
    (hqi0 : 0 < qi) (hqi1 : qi < 1) (hqj1 : qj < 1)
    (hqij : qi < qj) (hc : 0 < c) (hyi : 0 ≤ yi)
    (heq : qi * c + (1 - qi) * yi = (1 - qj) * yj) :
    yi < yj - qi * c / (1 - qi) := by
  have hlt :=
    lemma4_exchange_transfer_lt hqi0 hqi1 hqj1 hqij hc hyi heq
  nlinarith

/--
Appendix D, Lemma 4 exchange algebra: the exact transfer preserves item `i`'s
item-fairness value before the small positive `ε₂` perturbation.
-/
theorem lemma4_exchange_i_value_eq
    {qi c yi : ℝ} (hqi1 : qi < 1) :
    (1 - qi) * (yi + qi * c / (1 - qi)) =
      qi * c + (1 - qi) * yi := by
  have hden : 1 - qi ≠ 0 := ne_of_gt (sub_pos.mpr hqi1)
  field_simp [hden]
  ring

/--
Appendix D, Lemma 4 exchange algebra: moving the `x_i` mass to the earlier
zero coordinate `j` strictly improves item `j` before the small `ε` terms.
-/
theorem lemma4_exchange_j_value_gt
    {qi qj c yj : ℝ}
    (hqi1 : qi < 1) (hqij : qi < qj) (hc : 0 < c) :
    qj * c + (1 - qj) * (yj - qi * c / (1 - qi)) >
      (1 - qj) * yj := by
  have hmargin :
      0 < qj - qi * ((1 - qj) / (1 - qi)) :=
    lemma4_exchange_margin_pos hqi1 hqij
  have hden : 1 - qi ≠ 0 := ne_of_gt (sub_pos.mpr hqi1)
  have hrewrite :
      qj * c + (1 - qj) * (yj - qi * c / (1 - qi)) -
          (1 - qj) * yj =
        c * (qj - qi * ((1 - qj) / (1 - qi))) := by
    field_simp [hden]
    ring
  have hpos :
      0 < c * (qj - qi * ((1 - qj) / (1 - qi))) :=
    mul_pos hc hmargin
  nlinarith

/--
Appendix D, Lemma 4 exchange algebra: there are small positive `ε₁, ε₂`
making both affected item values strictly larger after the paper's perturbation.
-/
theorem lemma4_exchange_exists_pos_eps_i_j_value_gt
    {qi qj c yi yj : ℝ}
    (hqi1 : qi < 1) (hqij : qi < qj) (hc : 0 < c) :
    ∃ eps1 eps2 : ℝ,
      0 < eps1 ∧ 0 < eps2 ∧
      (1 - qi) * (yi + qi * c / (1 - qi) + eps2) >
        qi * c + (1 - qi) * yi ∧
      qj * (c - eps1) +
          (1 - qj) * (yj - qi * c / (1 - qi) - eps2) >
        (1 - qj) * yj := by
  let margin : ℝ := qj - qi * ((1 - qj) / (1 - qi))
  let eps : ℝ := c * margin / 4
  have hmargin : 0 < margin := by
    simpa [margin] using lemma4_exchange_margin_pos hqi1 hqij
  have hMpos : 0 < c * margin := mul_pos hc hmargin
  have heps_pos : 0 < eps := by
    dsimp [eps]
    positivity
  have hden : 1 - qi ≠ 0 := ne_of_gt (sub_pos.mpr hqi1)
  refine ⟨eps, eps, heps_pos, heps_pos, ?_, ?_⟩
  · have hdiff :
        (1 - qi) * (yi + qi * c / (1 - qi) + eps) -
            (qi * c + (1 - qi) * yi) =
          (1 - qi) * eps := by
        field_simp [hden]
        ring
    have hpos : 0 < (1 - qi) * eps :=
      mul_pos (sub_pos.mpr hqi1) heps_pos
    nlinarith
  · have hdiff :
        qj * (c - eps) +
            (1 - qj) * (yj - qi * c / (1 - qi) - eps) -
            (1 - qj) * yj =
          c * margin - eps := by
        dsimp [margin]
        field_simp [hden]
        ring
    have hpositive : 0 < c * margin - eps := by
      dsimp [eps]
      nlinarith
    nlinarith

/--
Appendix D, Lemma 4 exchange algebra with validity bounds: the small positive
`ε₁, ε₂` can also be chosen below arbitrary positive caps.
-/
theorem lemma4_exchange_exists_bounded_pos_eps_i_j_value_gt
    {qi qj c yi yj b1 b2 : ℝ}
    (hqi1 : qi < 1) (hqij : qi < qj) (hc : 0 < c)
    (hb1 : 0 < b1) (hb2 : 0 < b2) :
    ∃ eps1 eps2 : ℝ,
      0 < eps1 ∧ eps1 < b1 ∧
      0 < eps2 ∧ eps2 < b2 ∧
      (1 - qi) * (yi + qi * c / (1 - qi) + eps2) >
        qi * c + (1 - qi) * yi ∧
      qj * (c - eps1) +
          (1 - qj) * (yj - qi * c / (1 - qi) - eps2) >
        (1 - qj) * yj := by
  let margin : ℝ := qj - qi * ((1 - qj) / (1 - qi))
  let totalMargin : ℝ := c * margin
  let cap : ℝ := min (min b1 b2) totalMargin
  let eps : ℝ := cap / 4
  have hmargin : 0 < margin := by
    simpa [margin] using lemma4_exchange_margin_pos hqi1 hqij
  have hMpos : 0 < totalMargin := by
    dsimp [totalMargin]
    exact mul_pos hc hmargin
  have hcap_pos : 0 < cap := by
    dsimp [cap]
    exact lt_min (lt_min hb1 hb2) hMpos
  have heps_pos : 0 < eps := by
    dsimp [eps]
    positivity
  have heps_lt_cap : eps < cap := by
    dsimp [eps]
    nlinarith
  have hcap_le_b1 : cap ≤ b1 := by
    dsimp [cap]
    exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hcap_le_b2 : cap ≤ b2 := by
    dsimp [cap]
    exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hcap_le_margin : cap ≤ totalMargin := by
    dsimp [cap]
    exact min_le_right _ _
  have heps_lt_b1 : eps < b1 := lt_of_lt_of_le heps_lt_cap hcap_le_b1
  have heps_lt_b2 : eps < b2 := lt_of_lt_of_le heps_lt_cap hcap_le_b2
  have heps_lt_margin : eps < totalMargin :=
    lt_of_lt_of_le heps_lt_cap hcap_le_margin
  have hden : 1 - qi ≠ 0 := ne_of_gt (sub_pos.mpr hqi1)
  refine ⟨eps, eps, heps_pos, heps_lt_b1,
    heps_pos, heps_lt_b2, ?_, ?_⟩
  · have hdiff :
        (1 - qi) * (yi + qi * c / (1 - qi) + eps) -
            (qi * c + (1 - qi) * yi) =
          (1 - qi) * eps := by
        field_simp [hden]
        ring
    have hpos : 0 < (1 - qi) * eps :=
      mul_pos (sub_pos.mpr hqi1) heps_pos
    nlinarith
  · have hdiff :
        qj * (c - eps) +
            (1 - qj) * (yj - qi * c / (1 - qi) - eps) -
            (1 - qj) * yj =
          totalMargin - eps := by
        dsimp [totalMargin, margin]
        field_simp [hden]
        ring
    nlinarith

/--
Appendix D, Lemma 4 exchange algebra: after the exact transfer, the donor
coordinate `y_j` remains nonnegative.
-/
theorem lemma4_exchange_yj_after_nonneg
    {qi qj c yi yj : ℝ}
    (hqi0 : 0 < qi) (hqi1 : qi < 1) (hqj1 : qj < 1)
    (hqij : qi < qj) (hc : 0 < c) (hyi : 0 ≤ yi)
    (heq : qi * c + (1 - qi) * yi = (1 - qj) * yj) :
    0 ≤ yj - qi * c / (1 - qi) := by
  have hlt :=
    lemma4_exchange_yj_sub_transfer_gt_yi
      hqi0 hqi1 hqj1 hqij hc hyi heq
  linarith

/--
Appendix D, Lemma 4 exchange algebra: after the exact transfer, the receiver
coordinate `y_i` remains below one whenever the original donor coordinate did.
-/
theorem lemma4_exchange_yi_after_lt_one
    {qi qj c yi yj : ℝ}
    (hqi0 : 0 < qi) (hqi1 : qi < 1) (hqj1 : qj < 1)
    (hqij : qi < qj) (hc : 0 < c) (hyi : 0 ≤ yi)
    (hyj_le_one : yj ≤ 1)
    (heq : qi * c + (1 - qi) * yi = (1 - qj) * yj) :
    yi + qi * c / (1 - qi) < 1 := by
  have hlt :=
    lemma4_exchange_transfer_lt
      hqi0 hqi1 hqj1 hqij hc hyi heq
  exact lt_of_lt_of_le hlt hyj_le_one

/--
Problem 6 dual algebra: if `q_t ≤ q_j`, the left-side dual coefficient also
respects the `y` budget.
-/
theorem problem6Dual_left_coeff_le
    {qt qj : ℝ}
    (hqj0 : 0 < qj) (hqj1 : qj < 1) (hqt_le : qt ≤ qj) :
    (qt / qj) * (1 - qj) ≤ 1 - qt := by
  have hqj_ne : qj ≠ 0 := ne_of_gt hqj0
  rw [div_mul_eq_mul_div]
  rw [div_le_iff₀ hqj0]
  nlinarith

/-- Strict left-side dual slack when `q_t < q_j`. -/
theorem problem6Dual_left_coeff_lt
    {qt qj : ℝ}
    (hqj0 : 0 < qj) (hqj1 : qj < 1) (hqt_lt : qt < qj) :
    (qt / qj) * (1 - qj) < 1 - qt := by
  rw [div_mul_eq_mul_div]
  rw [div_lt_iff₀ hqj0]
  nlinarith

/--
Problem 6 dual algebra: if `q_j ≤ q_t`, the right-side dual coefficient also
respects the `x` budget.
-/
theorem problem6Dual_right_coeff_le
    {qt qj : ℝ}
    (hqj1 : qj < 1) (hqt_le : qj ≤ qt) :
    ((1 - qt) / (1 - qj)) * qj ≤ qt := by
  have hden : 0 < 1 - qj := sub_pos.mpr hqj1
  rw [div_mul_eq_mul_div]
  rw [div_le_iff₀ hden]
  nlinarith

/-- Strict right-side dual slack when `q_j < q_t`. -/
theorem problem6Dual_right_coeff_lt
    {qt qj : ℝ}
    (hqj1 : qj < 1) (hjt_lt : qj < qt) :
    ((1 - qt) / (1 - qj)) * qj < qt := by
  have hden : 0 < 1 - qj := sub_pos.mpr hqj1
  rw [div_mul_eq_mul_div]
  rw [div_lt_iff₀ hden]
  nlinarith

/--
Appendix D, Lemma 4 indexed exchange margin: if `j` is before `i`, then
`q_j > q_i`, so the item-`j` perturbation has positive slack.
-/
theorem lemma4_pairShare_exchange_margin_pos
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {i j : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hji : j.val < i.val) :
    0 < pairShare alpha v j -
      pairShare alpha v i *
        ((1 - pairShare alpha v j) / (1 - pairShare alpha v i)) := by
  have hqij :
      pairShare alpha v i < pairShare alpha v j :=
    pairShare_strictAnti_index
      halpha0 halpha1 hpos hdec hji
  exact lemma4_exchange_margin_pos
    (pairShare_lt_one i halpha0 halpha1 hpos) hqij

/--
Appendix D, Lemma 4 indexed exchange transfer bound. This is the paper's
`y_i + q_i c/(1-q_i) < y_j` inequality.
-/
theorem lemma4_pairShare_exchange_transfer_lt
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {i j : Item n}
    {c yi yj : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hji : j.val < i.val)
    (hc : 0 < c) (hyi : 0 ≤ yi)
    (heq :
      pairShare alpha v i * c +
        (1 - pairShare alpha v i) * yi =
          (1 - pairShare alpha v j) * yj) :
    yi + pairShare alpha v i * c /
        (1 - pairShare alpha v i) < yj := by
  have hqij :
      pairShare alpha v i < pairShare alpha v j :=
    pairShare_strictAnti_index
      halpha0 halpha1 hpos hdec hji
  exact lemma4_exchange_transfer_lt
    (pairShare_pos i halpha0 halpha1 hpos)
    (pairShare_lt_one i halpha0 halpha1 hpos)
    (pairShare_lt_one j halpha0 halpha1 hpos)
    hqij hc hyi heq

/--
Appendix D, Lemma 4 indexed exchange transfer bound. This is the paper's
`y_j - q_i c/(1-q_i) > y_i` inequality.
-/
theorem lemma4_pairShare_exchange_yj_sub_transfer_gt_yi
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {i j : Item n}
    {c yi yj : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hji : j.val < i.val)
    (hc : 0 < c) (hyi : 0 ≤ yi)
    (heq :
      pairShare alpha v i * c +
        (1 - pairShare alpha v i) * yi =
          (1 - pairShare alpha v j) * yj) :
    yi < yj - pairShare alpha v i * c /
        (1 - pairShare alpha v i) := by
  have hlt :=
    lemma4_pairShare_exchange_transfer_lt
      halpha0 halpha1 hpos hdec hji hc hyi heq
  nlinarith

/--
Appendix D, Lemma 4 indexed exchange algebra: the exact transfer preserves
item `i`'s value before the small positive `ε₂` perturbation.
-/
theorem lemma4_pairShare_exchange_i_value_eq
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {i : Item n}
    {c yi : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j) :
    (1 - pairShare alpha v i) *
        (yi + pairShare alpha v i * c /
          (1 - pairShare alpha v i)) =
      pairShare alpha v i * c +
        (1 - pairShare alpha v i) * yi := by
  exact lemma4_exchange_i_value_eq
    (pairShare_lt_one i halpha0 halpha1 hpos)

/--
Appendix D, Lemma 4 indexed exchange algebra: moving positive `x_i` mass to
an earlier zero coordinate `j` strictly improves item `j`.
-/
theorem lemma4_pairShare_exchange_j_value_gt
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {i j : Item n}
    {c yj : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hji : j.val < i.val)
    (hc : 0 < c) :
    pairShare alpha v j * c +
        (1 - pairShare alpha v j) *
          (yj - pairShare alpha v i * c /
            (1 - pairShare alpha v i)) >
      (1 - pairShare alpha v j) * yj := by
  have hqij :
      pairShare alpha v i < pairShare alpha v j :=
    pairShare_strictAnti_index
      halpha0 halpha1 hpos hdec hji
  exact lemma4_exchange_j_value_gt
    (pairShare_lt_one i halpha0 halpha1 hpos) hqij hc

/--
Appendix D, Lemma 4 indexed exchange algebra: small positive `ε₁, ε₂` can be
chosen so both affected item values strictly increase.
-/
theorem lemma4_pairShare_exchange_exists_pos_eps_i_j_value_gt
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {i j : Item n}
    {c yi yj : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hji : j.val < i.val)
    (hc : 0 < c) :
    ∃ eps1 eps2 : ℝ,
      0 < eps1 ∧ 0 < eps2 ∧
      (1 - pairShare alpha v i) *
          (yi + pairShare alpha v i * c /
            (1 - pairShare alpha v i) + eps2) >
        pairShare alpha v i * c +
          (1 - pairShare alpha v i) * yi ∧
      pairShare alpha v j * (c - eps1) +
          (1 - pairShare alpha v j) *
            (yj - pairShare alpha v i * c /
              (1 - pairShare alpha v i) - eps2) >
        (1 - pairShare alpha v j) * yj := by
  have hqij :
      pairShare alpha v i < pairShare alpha v j :=
    pairShare_strictAnti_index
      halpha0 halpha1 hpos hdec hji
  exact lemma4_exchange_exists_pos_eps_i_j_value_gt
    (pairShare_lt_one i halpha0 halpha1 hpos) hqij hc

/--
Appendix D, Lemma 4 indexed exchange algebra with validity bounds: the small
positive `ε₁, ε₂` can also be chosen below arbitrary positive caps.
-/
theorem lemma4_pairShare_exchange_exists_bounded_pos_eps_i_j_value_gt
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {i j : Item n}
    {c yi yj b1 b2 : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hji : j.val < i.val)
    (hc : 0 < c) (hb1 : 0 < b1) (hb2 : 0 < b2) :
    ∃ eps1 eps2 : ℝ,
      0 < eps1 ∧ eps1 < b1 ∧
      0 < eps2 ∧ eps2 < b2 ∧
      (1 - pairShare alpha v i) *
          (yi + pairShare alpha v i * c /
            (1 - pairShare alpha v i) + eps2) >
        pairShare alpha v i * c +
          (1 - pairShare alpha v i) * yi ∧
      pairShare alpha v j * (c - eps1) +
          (1 - pairShare alpha v j) *
            (yj - pairShare alpha v i * c /
              (1 - pairShare alpha v i) - eps2) >
        (1 - pairShare alpha v j) * yj := by
  have hqij :
      pairShare alpha v i < pairShare alpha v j :=
    pairShare_strictAnti_index
      halpha0 halpha1 hpos hdec hji
  exact lemma4_exchange_exists_bounded_pos_eps_i_j_value_gt
    (pairShare_lt_one i halpha0 halpha1 hpos) hqij hc hb1 hb2

/--
Appendix D, Lemma 4 indexed exchange algebra: after the exact transfer, the
donor coordinate `y_j` remains nonnegative.
-/
theorem lemma4_pairShare_exchange_yj_after_nonneg
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {i j : Item n}
    {c yi yj : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hji : j.val < i.val)
    (hc : 0 < c) (hyi : 0 ≤ yi)
    (heq :
      pairShare alpha v i * c +
        (1 - pairShare alpha v i) * yi =
          (1 - pairShare alpha v j) * yj) :
    0 ≤ yj - pairShare alpha v i * c /
        (1 - pairShare alpha v i) := by
  have hqij :
      pairShare alpha v i < pairShare alpha v j :=
    pairShare_strictAnti_index
      halpha0 halpha1 hpos hdec hji
  exact lemma4_exchange_yj_after_nonneg
    (pairShare_pos i halpha0 halpha1 hpos)
    (pairShare_lt_one i halpha0 halpha1 hpos)
    (pairShare_lt_one j halpha0 halpha1 hpos)
    hqij hc hyi heq

/--
Appendix D, Lemma 4 indexed exchange algebra: after the exact transfer, the
receiver coordinate `y_i` remains below one whenever the original donor
coordinate did.
-/
theorem lemma4_pairShare_exchange_yi_after_lt_one
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {i j : Item n}
    {c yi yj : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hji : j.val < i.val)
    (hc : 0 < c) (hyi : 0 ≤ yi) (hyj_le_one : yj ≤ 1)
    (heq :
      pairShare alpha v i * c +
        (1 - pairShare alpha v i) * yi =
          (1 - pairShare alpha v j) * yj) :
    yi + pairShare alpha v i * c /
        (1 - pairShare alpha v i) < 1 := by
  have hqij :
      pairShare alpha v i < pairShare alpha v j :=
    pairShare_strictAnti_index
      halpha0 halpha1 hpos hdec hji
  exact lemma4_exchange_yi_after_lt_one
    (pairShare_pos i halpha0 halpha1 hpos)
    (pairShare_lt_one i halpha0 halpha1 hpos)
    (pairShare_lt_one j halpha0 halpha1 hpos)
    hqij hc hyi hyj_le_one heq

/--
Appendix D, Lemma 4 perturbation of the first row `x`.

The paper moves all mass `c = x_i` from the later positive coordinate `i` to
the earlier zero coordinate `j`, except for a small `ε₁` that is redistributed
to the other items through `r`.
-/
noncomputable def lemma4GapExchangeX {n : ℕ}
    (x : Item n → ℝ) (i j : Item n) (c eps1 : ℝ)
    (r : Item n → ℝ) (l : Item n) : ℝ :=
  x l + (if l = i then -c else 0) +
    (if l = j then c - eps1 else 0) + eps1 * r l

/--
Appendix D, Lemma 4 perturbation of the second row `y`.

The transfer `q_i c/(1-q_i)` offsets the loss at item `i`; the small `ε₂`
strictly improves item `i` and is taken from item `j`.
-/
noncomputable def lemma4GapExchangeY {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) (y : Item n → ℝ)
    (i j : Item n) (c eps2 : ℝ) (l : Item n) : ℝ :=
  y l +
    (if l = i then
      pairShare alpha v i * c / (1 - pairShare alpha v i) + eps2
    else 0) +
    (if l = j then
      -(pairShare alpha v i * c / (1 - pairShare alpha v i) + eps2)
    else 0)

/-- Lemma 4's `x` perturbation preserves the row sum. -/
theorem lemma4GapExchangeX_sum_eq {n : ℕ}
    (x : Item n → ℝ) (i j : Item n) (c eps1 : ℝ)
    (r : Item n → ℝ)
    (hrsum : (∑ l : Item n, r l) = 1) :
    (∑ l : Item n, lemma4GapExchangeX x i j c eps1 r l) =
      ∑ l : Item n, x l := by
  unfold lemma4GapExchangeX
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum]
  simp [hrsum]
  ring

/-- Lemma 4's `y` perturbation preserves the row sum. -/
theorem lemma4GapExchangeY_sum_eq {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) (y : Item n → ℝ)
    (i j : Item n) (c eps2 : ℝ) :
    (∑ l : Item n, lemma4GapExchangeY alpha v y i j c eps2 l) =
      ∑ l : Item n, y l := by
  unfold lemma4GapExchangeY
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp
  ring

/-- Lemma 4's `x` perturbation remains nonnegative under the paper's bounds. -/
theorem lemma4GapExchangeX_nonneg {n : ℕ}
    {x r : Item n → ℝ} {i j : Item n} {c eps1 : ℝ}
    (hnonneg : ∀ l : Item n, 0 ≤ x l)
    (hxi : x i = c) (hxj : x j = 0) (hij : i ≠ j)
    (hrnonneg : ∀ l : Item n, 0 ≤ r l)
    (hri : r i = 0) (hrj : r j = 0)
    (heps1_pos : 0 < eps1) (heps1_lt_c : eps1 < c) :
    ∀ l : Item n, 0 ≤ lemma4GapExchangeX x i j c eps1 r l := by
  intro l
  by_cases hli : l = i
  · subst l
    simp [lemma4GapExchangeX, hxi, hri, hij]
  · by_cases hlj : l = j
    · subst l
      have hji : j ≠ i := hij.symm
      simp [lemma4GapExchangeX, hxj, hrj, hji]
      linarith
    · have hdist_i : l ≠ i := hli
      have hdist_j : l ≠ j := hlj
      have hredistrib : 0 ≤ eps1 * r l :=
        mul_nonneg heps1_pos.le (hrnonneg l)
      simpa [lemma4GapExchangeX, hdist_i, hdist_j] using
        add_nonneg (hnonneg l) hredistrib

/-- Lemma 4's `y` perturbation remains nonnegative under the paper's bounds. -/
theorem lemma4GapExchangeY_nonneg {n : ℕ}
    {alpha : ℝ} {v y : Item n → ℝ} {i j : Item n} {c eps2 : ℝ}
    (hnonneg : ∀ l : Item n, 0 ≤ y l) (hij : i ≠ j)
    (htransfer_nonneg :
      0 ≤ pairShare alpha v i * c / (1 - pairShare alpha v i))
    (heps2_pos : 0 < eps2)
    (heps2_lt_gap :
      eps2 < y j - pairShare alpha v i * c /
        (1 - pairShare alpha v i)) :
    ∀ l : Item n, 0 ≤ lemma4GapExchangeY alpha v y i j c eps2 l := by
  intro l
  by_cases hli : l = i
  · subst l
    simp [lemma4GapExchangeY, hij]
    nlinarith [hnonneg i, htransfer_nonneg, heps2_pos]
  · by_cases hlj : l = j
    · subst l
      have hji : j ≠ i := hij.symm
      simp [lemma4GapExchangeY, hji]
      linarith
    · simpa [lemma4GapExchangeY, hli, hlj] using hnonneg l

/--
Appendix D, Lemma 4 perturbation construction.

If an optimal equalized solution had an earlier zero `x_j` and a later positive
`x_i = c`, then the paper's exchange produces nonnegative row vectors with the
same row sums and strictly larger item value at every item.  The redistribution
vector `r` is an abstract version of the paper's uniform `ε₁/(n-2)` spread over
the unaffected items.
-/
theorem lemma4_pairShare_gap_exchange_exists_strictly_improves
    {n : ℕ} {alpha : ℝ} {v x y r : Item n → ℝ} {i j : Item n}
    {c ell : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hji : j.val < i.val)
    (hx_nonneg : ∀ l : Item n, 0 ≤ x l)
    (hy_nonneg : ∀ l : Item n, 0 ≤ y l)
    (hxi : x i = c) (hxj : x j = 0) (hc : 0 < c)
    (hsumx : (∑ l : Item n, x l) = 1)
    (hsumy : (∑ l : Item n, y l) = 1)
    (hr_nonneg : ∀ l : Item n, 0 ≤ r l)
    (hr_pos : ∀ {l : Item n}, l ≠ i → l ≠ j → 0 < r l)
    (hri : r i = 0) (hrj : r j = 0)
    (hrsum : (∑ l : Item n, r l) = 1)
    (hi_eq :
      pairShare alpha v i * x i +
        (1 - pairShare alpha v i) * y i = ell)
    (hj_eq :
      pairShare alpha v j * x j +
        (1 - pairShare alpha v j) * y j = ell) :
    ∃ eps1 eps2 : ℝ, ∃ x' y' : Item n → ℝ,
      0 < eps1 ∧ eps1 < c ∧ 0 < eps2 ∧
      (eps2 < y j - pairShare alpha v i * c /
        (1 - pairShare alpha v i)) ∧
      (∀ l : Item n, 0 ≤ x' l) ∧
      (∀ l : Item n, 0 ≤ y' l) ∧
      (∑ l : Item n, x' l) = 1 ∧
      (∑ l : Item n, y' l) = 1 ∧
      (∀ l : Item n,
        pairShare alpha v l * x l +
          (1 - pairShare alpha v l) * y l <
        pairShare alpha v l * x' l +
          (1 - pairShare alpha v l) * y' l) := by
  classical
  have hij_ne : i ≠ j := by
    intro hij
    subst i
    omega
  have hqij :
      pairShare alpha v i < pairShare alpha v j :=
    pairShare_strictAnti_index halpha0 halpha1 hpos hdec hji
  have heq_transfer :
      pairShare alpha v i * c +
        (1 - pairShare alpha v i) * y i =
          (1 - pairShare alpha v j) * y j := by
    have hi :
        pairShare alpha v i * c +
          (1 - pairShare alpha v i) * y i = ell := by
      simpa [hxi] using hi_eq
    have hj :
        (1 - pairShare alpha v j) * y j = ell := by
      simpa [hxj] using hj_eq
    exact hi.trans hj.symm
  have hy_gap_pos :
      0 < y j - pairShare alpha v i * c /
        (1 - pairShare alpha v i) := by
    have hlt :=
      lemma4_pairShare_exchange_yj_sub_transfer_gt_yi
        halpha0 halpha1 hpos hdec hji hc (hy_nonneg i) heq_transfer
    exact lt_of_le_of_lt (hy_nonneg i) hlt
  obtain ⟨eps1, eps2, heps1_pos, heps1_lt_c,
      heps2_pos, heps2_lt_gap, hi_gt, hj_gt⟩ :=
    lemma4_pairShare_exchange_exists_bounded_pos_eps_i_j_value_gt
      halpha0 halpha1 hpos hdec hji hc hc hy_gap_pos
      (yi := y i) (yj := y j)
  let x' : Item n → ℝ := lemma4GapExchangeX x i j c eps1 r
  let y' : Item n → ℝ := lemma4GapExchangeY alpha v y i j c eps2
  have hx'_nonneg : ∀ l : Item n, 0 ≤ x' l := by
    intro l
    exact lemma4GapExchangeX_nonneg hx_nonneg hxi hxj hij_ne
      hr_nonneg hri hrj heps1_pos heps1_lt_c l
  have htransfer_nonneg :
      0 ≤ pairShare alpha v i * c / (1 - pairShare alpha v i) := by
    exact div_nonneg
      (mul_nonneg (pairShare_pos i halpha0 halpha1 hpos).le hc.le)
      (one_sub_pairShare_pos i halpha0 halpha1 hpos).le
  have hy'_nonneg : ∀ l : Item n, 0 ≤ y' l := by
    intro l
    exact lemma4GapExchangeY_nonneg hy_nonneg hij_ne htransfer_nonneg
      heps2_pos heps2_lt_gap l
  have hx'_sum : (∑ l : Item n, x' l) = 1 := by
    dsimp [x']
    rw [lemma4GapExchangeX_sum_eq x i j c eps1 r hrsum, hsumx]
  have hy'_sum : (∑ l : Item n, y' l) = 1 := by
    dsimp [y']
    rw [lemma4GapExchangeY_sum_eq alpha v y i j c eps2, hsumy]
  refine ⟨eps1, eps2, x', y', heps1_pos, heps1_lt_c,
    heps2_pos, heps2_lt_gap, hx'_nonneg, hy'_nonneg,
    hx'_sum, hy'_sum, ?_⟩
  intro l
  by_cases hli : l = i
  · subst l
    have hx'i : x' i = 0 := by
      dsimp [x']
      simp [lemma4GapExchangeX, hxi, hri, hij_ne]
    have hy'i :
        y' i =
          y i + pairShare alpha v i * c /
            (1 - pairShare alpha v i) + eps2 := by
      dsimp [y']
      simp [lemma4GapExchangeY, hij_ne]
      ring
    rw [hx'i, hy'i, hxi]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hi_gt
  · by_cases hlj : l = j
    · subst l
      have hji_ne : j ≠ i := hij_ne.symm
      have hx'j : x' j = c - eps1 := by
        dsimp [x']
        simp [lemma4GapExchangeX, hxj, hrj, hji_ne]
      have hy'j :
          y' j =
            y j - pairShare alpha v i * c /
              (1 - pairShare alpha v i) - eps2 := by
        dsimp [y']
        simp [lemma4GapExchangeY, hji_ne]
        ring
      rw [hx'j, hy'j, hxj]
      simpa [mul_comm, mul_left_comm, mul_assoc] using hj_gt
    · have hx'l : x' l = x l + eps1 * r l := by
        dsimp [x']
        simp [lemma4GapExchangeX, hli, hlj]
      have hy'l : y' l = y l := by
        dsimp [y']
        simp [lemma4GapExchangeY, hli, hlj]
      rw [hx'l, hy'l]
      have hq_pos : 0 < pairShare alpha v l :=
        pairShare_pos l halpha0 halpha1 hpos
      have hdelta_pos : 0 < pairShare alpha v l * (eps1 * r l) :=
        mul_pos hq_pos (mul_pos heps1_pos (hr_pos hli hlj))
      nlinarith

/--
Appendix D, Lemma 4 symmetric perturbation of the first row `x` when the gap is
in the second row `y`.
-/
noncomputable def lemma4GapExchangeXFromY {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) (x : Item n → ℝ)
    (i j : Item n) (c eps2 : ℝ) (l : Item n) : ℝ :=
  x l +
    (if l = i then
      (1 - pairShare alpha v i) * c / pairShare alpha v i + eps2
    else 0) +
    (if l = j then
      -((1 - pairShare alpha v i) * c / pairShare alpha v i + eps2)
    else 0)

/-- The symmetric Lemma 4 `x` compensation preserves the row sum. -/
theorem lemma4GapExchangeXFromY_sum_eq {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) (x : Item n → ℝ)
    (i j : Item n) (c eps2 : ℝ) :
    (∑ l : Item n, lemma4GapExchangeXFromY alpha v x i j c eps2 l) =
      ∑ l : Item n, x l := by
  unfold lemma4GapExchangeXFromY
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp
  ring

/-- The symmetric Lemma 4 `x` compensation remains nonnegative. -/
theorem lemma4GapExchangeXFromY_nonneg {n : ℕ}
    {alpha : ℝ} {v x : Item n → ℝ} {i j : Item n} {c eps2 : ℝ}
    (hnonneg : ∀ l : Item n, 0 ≤ x l) (hij : i ≠ j)
    (htransfer_nonneg :
      0 ≤ (1 - pairShare alpha v i) * c / pairShare alpha v i)
    (heps2_pos : 0 < eps2)
    (heps2_lt_gap :
      eps2 < x j - (1 - pairShare alpha v i) * c /
        pairShare alpha v i) :
    ∀ l : Item n, 0 ≤ lemma4GapExchangeXFromY alpha v x i j c eps2 l := by
  intro l
  by_cases hli : l = i
  · subst l
    simp [lemma4GapExchangeXFromY, hij]
    nlinarith [hnonneg i, htransfer_nonneg, heps2_pos]
  · by_cases hlj : l = j
    · subst l
      have hji : j ≠ i := hij.symm
      simp [lemma4GapExchangeXFromY, hji]
      linarith
    · simpa [lemma4GapExchangeXFromY, hli, hlj] using hnonneg l

/--
Appendix D, Lemma 4 symmetric perturbation construction.

If an equalized locally optimal solution had an earlier positive `y_i = c` and
a later zero `y_j`, the symmetric exchange strictly improves every item value.
-/
theorem lemma4_pairShare_y_gap_exchange_exists_strictly_improves
    {n : ℕ} {alpha : ℝ} {v x y r : Item n → ℝ} {i j : Item n}
    {c ell : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hij : i.val < j.val)
    (hx_nonneg : ∀ l : Item n, 0 ≤ x l)
    (hy_nonneg : ∀ l : Item n, 0 ≤ y l)
    (hyi : y i = c) (hyj : y j = 0) (hc : 0 < c)
    (hsumx : (∑ l : Item n, x l) = 1)
    (hsumy : (∑ l : Item n, y l) = 1)
    (hr_nonneg : ∀ l : Item n, 0 ≤ r l)
    (hr_pos : ∀ {l : Item n}, l ≠ i → l ≠ j → 0 < r l)
    (hri : r i = 0) (hrj : r j = 0)
    (hrsum : (∑ l : Item n, r l) = 1)
    (hi_eq :
      pairShare alpha v i * x i +
        (1 - pairShare alpha v i) * y i = ell)
    (hj_eq :
      pairShare alpha v j * x j +
        (1 - pairShare alpha v j) * y j = ell) :
    ∃ eps1 eps2 : ℝ, ∃ x' y' : Item n → ℝ,
      0 < eps1 ∧ eps1 < c ∧ 0 < eps2 ∧
      (eps2 < x j - (1 - pairShare alpha v i) * c /
        pairShare alpha v i) ∧
      (∀ l : Item n, 0 ≤ x' l) ∧
      (∀ l : Item n, 0 ≤ y' l) ∧
      (∑ l : Item n, x' l) = 1 ∧
      (∑ l : Item n, y' l) = 1 ∧
      (∀ l : Item n,
        pairShare alpha v l * x l +
          (1 - pairShare alpha v l) * y l <
        pairShare alpha v l * x' l +
          (1 - pairShare alpha v l) * y' l) := by
  classical
  have hij_ne : i ≠ j := by
    intro h
    subst j
    omega
  have hqji :
      pairShare alpha v j < pairShare alpha v i :=
    pairShare_strictAnti_index halpha0 halpha1 hpos hdec hij
  have hpij :
      1 - pairShare alpha v i < 1 - pairShare alpha v j := by
    linarith
  have heq_transfer :
      (1 - pairShare alpha v i) * c +
        pairShare alpha v i * x i =
          pairShare alpha v j * x j := by
    have hi :
        pairShare alpha v i * x i +
          (1 - pairShare alpha v i) * c = ell := by
      simpa [hyi] using hi_eq
    have hj :
        pairShare alpha v j * x j = ell := by
      simpa [hyj] using hj_eq
    nlinarith
  have hx_gap_pos :
      0 < x j - (1 - pairShare alpha v i) * c /
        pairShare alpha v i := by
    have heq_transfer_scalar :
        (1 - pairShare alpha v i) * c +
          (1 - (1 - pairShare alpha v i)) * x i =
            (1 - (1 - pairShare alpha v j)) * x j := by
      nlinarith [heq_transfer]
    have hlt :=
      lemma4_exchange_yj_sub_transfer_gt_yi
        (one_sub_pairShare_pos i halpha0 halpha1 hpos)
        (by
          have hqpos := pairShare_pos i halpha0 halpha1 hpos
          linarith)
        (by
          have hqpos := pairShare_pos j halpha0 halpha1 hpos
          linarith)
        hpij hc (hx_nonneg i) heq_transfer_scalar
    have hlt' :
        x i < x j - (1 - pairShare alpha v i) * c /
          pairShare alpha v i := by
      convert hlt using 1
      ring
    exact lt_of_le_of_lt (hx_nonneg i) hlt'
  obtain ⟨eps1, eps2, heps1_pos, heps1_lt_c,
      heps2_pos, heps2_lt_gap, hi_gt, hj_gt⟩ :=
    lemma4_exchange_exists_bounded_pos_eps_i_j_value_gt
      (by
        have hqpos := pairShare_pos i halpha0 halpha1 hpos
        linarith)
      hpij hc hc hx_gap_pos
      (qi := 1 - pairShare alpha v i)
      (qj := 1 - pairShare alpha v j)
      (yi := x i) (yj := x j)
  have hi_gt_pair :
      pairShare alpha v i *
          (x i + (1 - pairShare alpha v i) * c /
            pairShare alpha v i + eps2) >
        (1 - pairShare alpha v i) * c +
          pairShare alpha v i * x i := by
    convert hi_gt using 1 <;> ring
  have hj_gt_pair :
      (1 - pairShare alpha v j) * (c - eps1) +
          pairShare alpha v j *
            (x j - (1 - pairShare alpha v i) * c /
              pairShare alpha v i - eps2) >
        pairShare alpha v j * x j := by
    convert hj_gt using 1 <;> ring
  let y' : Item n → ℝ := lemma4GapExchangeX y i j c eps1 r
  let x' : Item n → ℝ := lemma4GapExchangeXFromY alpha v x i j c eps2
  have hy'_nonneg : ∀ l : Item n, 0 ≤ y' l := by
    intro l
    exact lemma4GapExchangeX_nonneg hy_nonneg hyi hyj hij_ne
      hr_nonneg hri hrj heps1_pos heps1_lt_c l
  have htransfer_nonneg :
      0 ≤ (1 - pairShare alpha v i) * c / pairShare alpha v i := by
    exact div_nonneg
      (mul_nonneg (one_sub_pairShare_pos i halpha0 halpha1 hpos).le hc.le)
      (pairShare_pos i halpha0 halpha1 hpos).le
  have hx'_nonneg : ∀ l : Item n, 0 ≤ x' l := by
    intro l
    exact lemma4GapExchangeXFromY_nonneg hx_nonneg hij_ne htransfer_nonneg
      heps2_pos heps2_lt_gap l
  have hy'_sum : (∑ l : Item n, y' l) = 1 := by
    dsimp [y']
    rw [lemma4GapExchangeX_sum_eq y i j c eps1 r hrsum, hsumy]
  have hx'_sum : (∑ l : Item n, x' l) = 1 := by
    dsimp [x']
    rw [lemma4GapExchangeXFromY_sum_eq alpha v x i j c eps2, hsumx]
  refine ⟨eps1, eps2, x', y', heps1_pos, heps1_lt_c,
    heps2_pos, heps2_lt_gap, hx'_nonneg, hy'_nonneg,
    hx'_sum, hy'_sum, ?_⟩
  intro l
  by_cases hli : l = i
  · subst l
    have hy'i : y' i = 0 := by
      dsimp [y']
      simp [lemma4GapExchangeX, hyi, hri, hij_ne]
    have hx'i :
        x' i =
          x i + (1 - pairShare alpha v i) * c /
            pairShare alpha v i + eps2 := by
      dsimp [x']
      simp [lemma4GapExchangeXFromY, hij_ne]
      ring
    rw [hy'i, hx'i, hyi]
    nlinarith [hi_gt_pair]
  · by_cases hlj : l = j
    · subst l
      have hji_ne : j ≠ i := hij_ne.symm
      have hy'j : y' j = c - eps1 := by
        dsimp [y']
        simp [lemma4GapExchangeX, hyj, hrj, hji_ne]
      have hx'j :
          x' j =
            x j - (1 - pairShare alpha v i) * c /
              pairShare alpha v i - eps2 := by
        dsimp [x']
        simp [lemma4GapExchangeXFromY, hji_ne]
        ring
      rw [hy'j, hx'j, hyj]
      nlinarith [hj_gt_pair]
    · have hy'l : y' l = y l + eps1 * r l := by
        dsimp [y']
        simp [lemma4GapExchangeX, hli, hlj]
      have hx'l : x' l = x l := by
        dsimp [x']
        simp [lemma4GapExchangeXFromY, hli, hlj]
      rw [hy'l, hx'l]
      have hone_sub_pos : 0 < 1 - pairShare alpha v l :=
        one_sub_pairShare_pos l halpha0 halpha1 hpos
      have hdelta_pos : 0 < (1 - pairShare alpha v l) * (eps1 * r l) :=
        mul_pos hone_sub_pos (mul_pos heps1_pos (hr_pos hli hlj))
      nlinarith

/--
Appendix E, Lemma 16, indexed midpoint component: if item `j` has higher value
than its opposite item, then `q_j(1/2) > 1/2`.
-/
theorem half_lt_pairShare_half_of_reverse_lt
    {n : ℕ} {v : Item n → ℝ} (j : Item n)
    (hpos : ∀ j : Item n, 0 < v j)
    (hlt : v (reverseItem j) < v j) :
    (1 / 2 : ℝ) < pairShare (1 / 2) v j := by
  exact half_lt_typeOneShare_half_of_right_lt_left
    (hpos j) (hpos (reverseItem j)) hlt

/--
Appendix E, Lemma 16, indexed midpoint component: if item `j` has lower value
than its opposite item, then `q_j(1/2) < 1/2`.
-/
theorem pairShare_half_lt_half_of_lt_reverse
    {n : ℕ} {v : Item n → ℝ} (j : Item n)
    (hpos : ∀ j : Item n, 0 < v j)
    (hlt : v j < v (reverseItem j)) :
    pairShare (1 / 2) v j < (1 / 2 : ℝ) := by
  exact typeOneShare_half_lt_half_of_left_lt_right
    (hpos j) (hpos (reverseItem j)) hlt

/--
Appendix E, Lemma 16, indexed midpoint component: equal opposite item values
give `q_j(1/2) = 1/2`.
-/
theorem pairShare_half_eq_half_of_eq_reverse
    {n : ℕ} {v : Item n → ℝ} (j : Item n)
    (hpos : ∀ j : Item n, 0 < v j)
    (heq : v j = v (reverseItem j)) :
    pairShare (1 / 2) v j = (1 / 2 : ℝ) := by
  exact typeOneShare_half_eq_half_of_eq (hpos j) heq

/-- If `j` is before its reverse partner, strict index-decrease gives `v_rev < v_j`. -/
theorem reverse_value_lt_of_val_lt_reverse
    {n : ℕ} {v : Item n → ℝ} (j : Item n)
    (hdec : StrictlyDecreasingByIndex v)
    (hval : j.val < (reverseItem j).val) :
    v (reverseItem j) < v j := by
  exact hdec hval

/-- If `j` is after its reverse partner, strict index-decrease gives `v_j < v_rev`. -/
theorem value_lt_reverse_value_of_reverse_val_lt
    {n : ℕ} {v : Item n → ℝ} (j : Item n)
    (hdec : StrictlyDecreasingByIndex v)
    (hval : (reverseItem j).val < j.val) :
    v j < v (reverseItem j) := by
  exact hdec hval

/--
Appendix E, Lemma 16, indexed order form: an item before its reverse partner
has `q_j(1/2) > 1/2`.
-/
theorem half_lt_pairShare_half_of_val_lt_reverse
    {n : ℕ} {v : Item n → ℝ} (j : Item n)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hval : j.val < (reverseItem j).val) :
    (1 / 2 : ℝ) < pairShare (1 / 2) v j := by
  exact half_lt_pairShare_half_of_reverse_lt j hpos
    (reverse_value_lt_of_val_lt_reverse j hdec hval)

/--
Appendix E, Lemma 16, indexed order form: an item after its reverse partner
has `q_j(1/2) < 1/2`.
-/
theorem pairShare_half_lt_half_of_reverse_val_lt
    {n : ℕ} {v : Item n → ℝ} (j : Item n)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hval : (reverseItem j).val < j.val) :
    pairShare (1 / 2) v j < (1 / 2 : ℝ) := by
  exact pairShare_half_lt_half_of_lt_reverse j hpos
    (value_lt_reverse_value_of_reverse_val_lt j hdec hval)

/--
Appendix E, Lemma 16, indexed order form: an item equal to its reverse partner
has `q_j(1/2) = 1/2`.
-/
theorem pairShare_half_eq_half_of_val_eq_reverse
    {n : ℕ} {v : Item n → ℝ} (j : Item n)
    (hpos : ∀ j : Item n, 0 < v j)
    (hval : j.val = (reverseItem j).val) :
    pairShare (1 / 2) v j = (1 / 2 : ℝ) := by
  have heq_item : j = reverseItem j := by
    exact Fin.ext hval
  exact pairShare_half_eq_half_of_eq_reverse j hpos (congrArg v heq_item)

/-- Zero-based arithmetic form of being before the reverse item. -/
theorem val_lt_reverseItem_iff {n : ℕ} (j : Item n) :
    j.val < (reverseItem j).val ↔ 2 * j.val + 1 < n := by
  simp [reverseItem]
  omega

/-- Zero-based arithmetic form of being after the reverse item. -/
theorem reverseItem_val_lt_iff {n : ℕ} (j : Item n) :
    (reverseItem j).val < j.val ↔ n < 2 * j.val + 1 := by
  simp [reverseItem]
  omega

/-- Zero-based arithmetic form of being the middle item. -/
theorem val_eq_reverseItem_iff {n : ℕ} (j : Item n) :
    j.val = (reverseItem j).val ↔ 2 * j.val + 1 = n := by
  simp [reverseItem]
  omega

/-- Zero-based arithmetic form of being at or before the reverse item. -/
theorem val_le_reverseItem_iff {n : ℕ} (j : Item n) :
    j.val ≤ (reverseItem j).val ↔ 2 * j.val + 1 ≤ n := by
  simp [reverseItem]
  omega

/--
Every item line has either an exact middle item or an item immediately before
the middle mirror pair.  This removes the odd/even midpoint case split from
paper-level theorem statements.
-/
theorem midpoint_center_or_succ_center {n : ℕ} [NeZero n] :
    (∃ c : Item n, c.val = (reverseItem c).val) ∨
      (∃ c : Item n, c.val + 1 = (reverseItem c).val) := by
  have hn0 : n ≠ 0 := NeZero.ne n
  rcases Nat.mod_two_eq_zero_or_one n with hmod | hmod
  · right
    let c : Item n := ⟨n / 2 - 1, by omega⟩
    refine ⟨c, ?_⟩
    have hdiv : 2 * (n / 2) = n := by
      have h := Nat.div_add_mod n 2
      omega
    simp [c, reverseItem]
    omega
  · left
    let c : Item n := ⟨n / 2, by omega⟩
    refine ⟨c, ?_⟩
    have hdiv : 2 * (n / 2) + 1 = n := by
      have h := Nat.div_add_mod n 2
      omega
    simp [c, reverseItem]
    omega

/-- Any item weakly before an exact center is weakly before its own mirror. -/
theorem val_le_reverseItem_of_val_le_center_eq_reverse
    {n : ℕ} {j c : Item n}
    (hj : j.val ≤ c.val)
    (hcenter : c.val = (reverseItem c).val) :
    j.val ≤ (reverseItem j).val := by
  rw [val_le_reverseItem_iff]
  have hc : 2 * c.val + 1 = n := by
    exact (val_eq_reverseItem_iff c).mp hcenter
  omega

/--
Any item weakly before the item immediately before the even midpoint is weakly
before its own mirror.
-/
theorem val_le_reverseItem_of_val_le_succ_center
    {n : ℕ} {j c : Item n}
    (hj : j.val ≤ c.val)
    (hsucc : c.val + 1 = (reverseItem c).val) :
    j.val ≤ (reverseItem j).val := by
  rw [val_le_reverseItem_iff]
  have hc : 2 * c.val + 2 = n := by
    simp [reverseItem] at hsucc
    omega
  omega

/--
If the pivot is at or before its mirror, then every item before the pivot has
its mirror after the pivot.
-/
theorem reverseItem_after_pivot_of_before_pivot_of_pivot_le_reverse
    {n : ℕ} {t j : Item n}
    (hcenter : t.val ≤ (reverseItem t).val)
    (hj : j.val < t.val) :
    t.val < (reverseItem j).val := by
  exact lt_of_le_of_lt hcenter (reverseItem_val_lt_of_val_lt hj)

/-- For an exact center pivot, mirroring identifies post-pivot and pre-pivot items. -/
theorem pivot_lt_reverseItem_iff_val_lt_pivot_of_pivot_eq_reverse
    {n : ℕ} {t j : Item n}
    (hcenter : t.val = (reverseItem t).val) :
    t.val < (reverseItem j).val ↔ j.val < t.val := by
  simp [reverseItem] at hcenter ⊢
  omega

/--
For an even midpoint pivot immediately before its mirror, post-pivot mirrors
are exactly the pivot and pre-pivot items.
-/
theorem pivot_lt_reverseItem_iff_val_le_pivot_of_pivot_succ_reverse
    {n : ℕ} {t j : Item n}
    (hsucc : t.val + 1 = (reverseItem t).val) :
    t.val < (reverseItem j).val ↔ j.val ≤ t.val := by
  simp [reverseItem] at hsucc ⊢
  omega

/--
Appendix D, Lemma 11 middle-term monotonicity: the denominator ratio appearing
in `(1-q_t)/(1-q_j)` decreases with `α` when `j` is after `t`.
-/
theorem lemma11_middle_denominator_ratio_antitone
    {n : ℕ} {alpha alpha' : ℝ} {v : Item n → ℝ} {t j : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (htj : t.val < j.val) :
    (alpha' * v j + (1 - alpha') * v (reverseItem j)) /
        (alpha' * v t + (1 - alpha') * v (reverseItem t)) ≤
      (alpha * v j + (1 - alpha) * v (reverseItem j)) /
        (alpha * v t + (1 - alpha) * v (reverseItem t)) := by
  have hXleA : v j ≤ v t := (hdec htj).le
  have hrev_lt : (reverseItem j).val < (reverseItem t).val :=
    reverseItem_val_lt_of_val_lt htj
  have hB_le_C : v (reverseItem t) ≤ v (reverseItem j) :=
    (hdec hrev_lt).le
  have hcross : v (reverseItem t) * v j ≤ v t * v (reverseItem j) := by
    have hmul :=
      mul_le_mul hB_le_C hXleA (hpos j).le (hpos (reverseItem j)).le
    nlinarith
  have h :=
    lemma11_affine_ratio_antitone_of_cross
      halpha0 halpha1 halpha0' halpha1' halpha_le
      (hpos t) (hpos (reverseItem t)) hcross
      (A := v t) (B := v (reverseItem t))
      (C := v (reverseItem j)) (X := v j)
  convert h using 1
  · ring
  · ring

/--
Appendix D, Lemma 11 right-side term monotonicity:
`(1-q_t(α))/(1-q_j(α))` decreases with `α` for each `j > t`.
-/
theorem lemma11_right_term_antitone
    {n : ℕ} {alpha alpha' : ℝ} {v : Item n → ℝ} {t j : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (htj : t.val < j.val) :
    (1 - pairShare alpha' v t) / (1 - pairShare alpha' v j) ≤
      (1 - pairShare alpha v t) / (1 - pairShare alpha v j) := by
  rw [one_sub_pairShare_div_one_sub_pairShare_eq
      t j halpha0' halpha1' hpos,
    one_sub_pairShare_div_one_sub_pairShare_eq
      t j halpha0 halpha1 hpos]
  have hratio :=
    lemma11_middle_denominator_ratio_antitone
      halpha0 halpha1 halpha0' halpha1' halpha_le hpos hdec htj
  have hconst_nonneg :
      0 ≤ v (reverseItem t) / v (reverseItem j) :=
    div_nonneg (hpos (reverseItem t)).le (hpos (reverseItem j)).le
  exact mul_le_mul_of_nonneg_left hratio hconst_nonneg

/--
Appendix D, Lemma 11 paired-term monotonicity: the mirror-paired ratio
`((1-α)v_t + αv_rev(t))/(αv_t + (1-α)v_rev(t))` decreases with `α` for pivots
at or before their mirror.
-/
theorem lemma11_paired_denominator_ratio_antitone
    {n : ℕ} {alpha alpha' : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter : t.val ≤ (reverseItem t).val) :
    ((1 - alpha') * v t + alpha' * v (reverseItem t)) /
        (alpha' * v t + (1 - alpha') * v (reverseItem t)) ≤
      ((1 - alpha) * v t + alpha * v (reverseItem t)) /
        (alpha * v t + (1 - alpha) * v (reverseItem t)) := by
  have hB_le_A : v (reverseItem t) ≤ v t := by
    by_cases heq : t.val = (reverseItem t).val
    · have ht_eq_rev : t = reverseItem t := Fin.ext heq
      rw [← ht_eq_rev]
    · have hlt : t.val < (reverseItem t).val := lt_of_le_of_ne hcenter heq
      exact (hdec hlt).le
  have hcross : v (reverseItem t) * v (reverseItem t) ≤ v t * v t := by
    have hmul :=
      mul_le_mul hB_le_A hB_le_A (hpos (reverseItem t)).le (hpos t).le
    nlinarith
  have h :=
    lemma11_affine_ratio_antitone_of_cross
      halpha0 halpha1 halpha0' halpha1' halpha_le
      (hpos t) (hpos (reverseItem t)) hcross
      (A := v t) (B := v (reverseItem t))
      (C := v t) (X := v (reverseItem t))
  convert h using 1
  · ring
  · ring

/--
Appendix D, Lemma 11 paired `h_t(α)` expression monotonicity after the paper's
mirror-pair expansion.
-/
theorem lemma11_pairedExpression_antitone
    {n : ℕ} {alpha alpha' : ℝ} {v : Item n → ℝ} {t j : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter : t.val ≤ (reverseItem t).val) :
    1 + (v (reverseItem j) / v j) *
        (((1 - alpha') * v t + alpha' * v (reverseItem t)) /
          (alpha' * v t + (1 - alpha') * v (reverseItem t))) ≤
      1 + (v (reverseItem j) / v j) *
        (((1 - alpha) * v t + alpha * v (reverseItem t)) /
          (alpha * v t + (1 - alpha) * v (reverseItem t))) := by
  have hratio :=
    lemma11_paired_denominator_ratio_antitone
      halpha0 halpha1 halpha0' halpha1' halpha_le hpos hdec hcenter
  have hconst_nonneg : 0 ≤ v (reverseItem j) / v j :=
    div_nonneg (hpos (reverseItem j)).le (hpos j).le
  have hmul := mul_le_mul_of_nonneg_left hratio hconst_nonneg
  nlinarith

/--
Appendix D, Lemma 11 mirror-paired term monotonicity:
`q_t/q_j + (1-q_t)/(1-q_{n-j+1})` decreases with `α` after the paper's
mirror-pair expansion.
-/
theorem lemma11_paired_q_term_antitone
    {n : ℕ} {alpha alpha' : ℝ} {v : Item n → ℝ} {t j : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter : t.val ≤ (reverseItem t).val) :
    pairShare alpha' v t / pairShare alpha' v j +
        (1 - pairShare alpha' v t) /
          (1 - pairShare alpha' v (reverseItem j)) ≤
      pairShare alpha v t / pairShare alpha v j +
        (1 - pairShare alpha v t) /
          (1 - pairShare alpha v (reverseItem j)) := by
  rw [lemma11_paired_q_term_eq t j halpha0' halpha1' hpos,
    lemma11_paired_q_term_eq t j halpha0 halpha1 hpos]
  exact lemma11_pairedExpression_antitone
    halpha0 halpha1 halpha0' halpha1' halpha_le hpos hdec hcenter

/--
The reduced two-type model for the opposing-preference setting in Theorem 3.
Type `0` has values `v_j`; type `1` has reversed values `v_{n-j+1}`.
-/
noncomputable def twoTypeReducedModel {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) :
    TypeWeightedRecommendationModel 2 n where
  utility := fun k j => if k = 0 then v j else v (reverseItem j)
  weight := fun k => if k = 0 then alpha else 1 - alpha

@[simp] theorem twoTypeReducedModel_utility_zero {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) (j : Item n) :
    (twoTypeReducedModel alpha v).utility 0 j = v j := by
  simp [twoTypeReducedModel]

@[simp] theorem twoTypeReducedModel_utility_one {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) (j : Item n) :
    (twoTypeReducedModel alpha v).utility 1 j = v (reverseItem j) := by
  simp [twoTypeReducedModel]

@[simp] theorem twoTypeReducedModel_weight_zero {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) :
    (twoTypeReducedModel alpha v).weight 0 = alpha := by
  simp [twoTypeReducedModel]

@[simp] theorem twoTypeReducedModel_weight_one {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) :
    (twoTypeReducedModel alpha v).weight 1 = 1 - alpha := by
  simp [twoTypeReducedModel]

/-- Interior type shares give strictly positive type weights. -/
theorem twoTypeReducedModel_positiveWeights {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1) :
    (twoTypeReducedModel alpha v).PositiveWeights := by
  intro k
  fin_cases k <;> simp [halpha0, sub_pos.mpr halpha1]

/-- Positive base values give strictly positive reduced utilities. -/
theorem twoTypeReducedModel_positiveUtilities {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ)
    (hpos : ∀ j : Item n, 0 < v j) :
    (twoTypeReducedModel alpha v).PositiveUtilities := by
  intro k j
  fin_cases k <;> simp [hpos]

/-- Positive base values give every opposing type a positive item. -/
theorem twoTypeReducedModel_rowHasPositiveItem {n : ℕ} [NeZero n]
    (alpha : ℝ) (v : Item n → ℝ)
    (hpos : ∀ j : Item n, 0 < v j) :
    (twoTypeReducedModel alpha v).RowHasPositiveItem := by
  intro k
  let j0 : Item n := Classical.choice inferInstance
  exact ⟨j0, twoTypeReducedModel_positiveUtilities alpha v hpos k j0⟩

/--
Mirror a two-type policy by swapping the two opposing types and reversing item
indices. This is the policy-level symmetry behind the second half of Theorem 3.
-/
noncomputable def mirrorTypePolicy {n : ℕ} (ρ : TypePolicy 2 n) :
    TypePolicy 2 n :=
  TypeWeightedRecommendationModel.typePolicyOfSimplexVector (fun k : UserType 2 =>
    ⟨fun j : Item n =>
        if k = 0 then (ρ 1 (reverseItem j)).toReal
        else (ρ 0 (reverseItem j)).toReal,
      ⟨by
        intro j
        by_cases hk : k = 0 <;> simp [hk, ENNReal.toReal_nonneg],
      by
        by_cases hk : k = 0
        · simp only [hk, ↓reduceIte]
          calc
            ∑ x : Item n, ((ρ 1) (reverseItem x)).toReal =
                ∑ x : Item n, ((ρ 1) x).toReal := by
                  simpa using
                    (sum_reverseItem (fun x : Item n => ((ρ 1) x).toReal))
            _ = 1 := AppliedModelingLib.pmfToRealSum (ρ 1)
        · have hk1 : k = 1 := by
            fin_cases k
            · exact (hk rfl).elim
            · rfl
          have hne : ¬ (1 : UserType 2) = 0 := by decide
          simp only [hk1, hne, ↓reduceIte]
          calc
            ∑ x : Item n, ((ρ 0) (reverseItem x)).toReal =
                ∑ x : Item n, ((ρ 0) x).toReal := by
                  simpa using
                    (sum_reverseItem (fun x : Item n => ((ρ 0) x).toReal))
            _ = 1 := AppliedModelingLib.pmfToRealSum (ρ 0)⟩⟩)

@[simp] theorem mirrorTypePolicy_zero_toReal {n : ℕ}
    (ρ : TypePolicy 2 n) (j : Item n) :
    ((mirrorTypePolicy ρ 0) j).toReal =
      (ρ 1 (reverseItem j)).toReal := by
  simp only [mirrorTypePolicy,
    TypeWeightedRecommendationModel.typePolicyOfSimplexVector_apply_toReal]
  rfl

@[simp] theorem mirrorTypePolicy_one_toReal {n : ℕ}
    (ρ : TypePolicy 2 n) (j : Item n) :
    ((mirrorTypePolicy ρ 1) j).toReal =
      (ρ 0 (reverseItem j)).toReal := by
  simp only [mirrorTypePolicy,
    TypeWeightedRecommendationModel.typePolicyOfSimplexVector_apply_toReal]
  rfl

/-- The two opposing types have the same best-item utility. -/
theorem twoTypeReducedModel_bestItemUtility_one_eq_zero {n : ℕ} [NeZero n]
    (alpha : ℝ) (v : Item n → ℝ) :
    TypeWeightedRecommendationModel.bestItemUtility
        (twoTypeReducedModel alpha v) 1 =
      TypeWeightedRecommendationModel.bestItemUtility
        (twoTypeReducedModel alpha v) 0 := by
  unfold TypeWeightedRecommendationModel.bestItemUtility
  change AppliedModelingLib.finiteMax (fun j : Item n => v (reverseItem j)) =
    AppliedModelingLib.finiteMax v
  exact finiteMax_reverseItem v

/-- Mirroring swaps type `0` raw utility with type `1` raw utility. -/
theorem twoTypeReducedModel_rawTypeUtility_mirror_zero_eq_one {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) (ρ : TypePolicy 2 n) :
    TypeWeightedRecommendationModel.rawTypeUtility
        (twoTypeReducedModel (1 - alpha) v) (mirrorTypePolicy ρ) 0 =
      TypeWeightedRecommendationModel.rawTypeUtility
        (twoTypeReducedModel alpha v) ρ 1 := by
  unfold TypeWeightedRecommendationModel.rawTypeUtility
    AppliedModelingLib.Policy.agentScore AppliedModelingLib.pmfExp
  change
    (∑ j : Item n, ((mirrorTypePolicy ρ 0) j).toReal * v j) =
      ∑ j : Item n, ((ρ 1) j).toReal * v (reverseItem j)
  simp
  simpa [reverseItem_reverseItem] using
    (sum_reverseItem (fun j : Item n =>
      ((ρ 1) j).toReal * v (reverseItem j)))

/-- Mirroring swaps type `1` raw utility with type `0` raw utility. -/
theorem twoTypeReducedModel_rawTypeUtility_mirror_one_eq_zero {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) (ρ : TypePolicy 2 n) :
    TypeWeightedRecommendationModel.rawTypeUtility
        (twoTypeReducedModel (1 - alpha) v) (mirrorTypePolicy ρ) 1 =
      TypeWeightedRecommendationModel.rawTypeUtility
        (twoTypeReducedModel alpha v) ρ 0 := by
  unfold TypeWeightedRecommendationModel.rawTypeUtility
    AppliedModelingLib.Policy.agentScore AppliedModelingLib.pmfExp
  change
    (∑ j : Item n,
      ((mirrorTypePolicy ρ 1) j).toReal * v (reverseItem j)) =
      ∑ j : Item n, ((ρ 0) j).toReal * v j
  simp
  simpa [reverseItem_reverseItem] using
    (sum_reverseItem (fun j : Item n => ((ρ 0) j).toReal * v j))

/-- Mirroring swaps the type `0` best-item denominator with type `1`. -/
theorem twoTypeReducedModel_bestItemUtility_mirror_zero_eq_one
    {n : ℕ} [NeZero n] (alpha : ℝ) (v : Item n → ℝ) :
    TypeWeightedRecommendationModel.bestItemUtility
        (twoTypeReducedModel (1 - alpha) v) 0 =
      TypeWeightedRecommendationModel.bestItemUtility
        (twoTypeReducedModel alpha v) 1 := by
  unfold TypeWeightedRecommendationModel.bestItemUtility
  change AppliedModelingLib.finiteMax v =
    AppliedModelingLib.finiteMax (fun j : Item n => v (reverseItem j))
  rw [finiteMax_reverseItem]

/-- Mirroring swaps the type `1` best-item denominator with type `0`. -/
theorem twoTypeReducedModel_bestItemUtility_mirror_one_eq_zero
    {n : ℕ} [NeZero n] (alpha : ℝ) (v : Item n → ℝ) :
    TypeWeightedRecommendationModel.bestItemUtility
        (twoTypeReducedModel (1 - alpha) v) 1 =
      TypeWeightedRecommendationModel.bestItemUtility
        (twoTypeReducedModel alpha v) 0 := by
  unfold TypeWeightedRecommendationModel.bestItemUtility
  change AppliedModelingLib.finiteMax (fun j : Item n => v (reverseItem j)) =
    AppliedModelingLib.finiteMax v
  exact finiteMax_reverseItem v

/-- Mirroring swaps normalized type utility from type `0` to type `1`. -/
theorem twoTypeReducedModel_normalizedTypeUtility_mirror_zero_eq_one
    {n : ℕ} [NeZero n]
    (alpha : ℝ) (v : Item n → ℝ) (ρ : TypePolicy 2 n) :
    TypeWeightedRecommendationModel.normalizedTypeUtility
        (twoTypeReducedModel (1 - alpha) v) (mirrorTypePolicy ρ) 0 =
      TypeWeightedRecommendationModel.normalizedTypeUtility
        (twoTypeReducedModel alpha v) ρ 1 := by
  unfold TypeWeightedRecommendationModel.normalizedTypeUtility
  rw [twoTypeReducedModel_rawTypeUtility_mirror_zero_eq_one,
    twoTypeReducedModel_bestItemUtility_mirror_zero_eq_one]

/-- Mirroring swaps normalized type utility from type `1` to type `0`. -/
theorem twoTypeReducedModel_normalizedTypeUtility_mirror_one_eq_zero
    {n : ℕ} [NeZero n]
    (alpha : ℝ) (v : Item n → ℝ) (ρ : TypePolicy 2 n) :
    TypeWeightedRecommendationModel.normalizedTypeUtility
        (twoTypeReducedModel (1 - alpha) v) (mirrorTypePolicy ρ) 1 =
      TypeWeightedRecommendationModel.normalizedTypeUtility
        (twoTypeReducedModel alpha v) ρ 0 := by
  unfold TypeWeightedRecommendationModel.normalizedTypeUtility
  rw [twoTypeReducedModel_rawTypeUtility_mirror_one_eq_zero,
    twoTypeReducedModel_bestItemUtility_mirror_one_eq_zero]

/-- Mirroring preserves the minimum normalized type utility. -/
theorem twoTypeReducedModel_typeFairness_mirror_eq
    {n : ℕ} [NeZero n]
    (alpha : ℝ) (v : Item n → ℝ) (ρ : TypePolicy 2 n) :
    TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel (1 - alpha) v) (mirrorTypePolicy ρ) =
      TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel alpha v) ρ := by
  apply le_antisymm
  · unfold TypeWeightedRecommendationModel.typeFairness
    refine AppliedModelingLib.le_finiteMin
      (TypeWeightedRecommendationModel.normalizedTypeUtility
        (twoTypeReducedModel alpha v) ρ) ?_
    intro k
    fin_cases k
    · have hle :=
        AppliedModelingLib.finiteMin_le
          (TypeWeightedRecommendationModel.normalizedTypeUtility
            (twoTypeReducedModel (1 - alpha) v) (mirrorTypePolicy ρ))
          (1 : UserType 2)
      simpa [twoTypeReducedModel_normalizedTypeUtility_mirror_one_eq_zero]
        using hle
    · have hle :=
        AppliedModelingLib.finiteMin_le
          (TypeWeightedRecommendationModel.normalizedTypeUtility
            (twoTypeReducedModel (1 - alpha) v) (mirrorTypePolicy ρ))
          (0 : UserType 2)
      simpa [twoTypeReducedModel_normalizedTypeUtility_mirror_zero_eq_one]
        using hle
  · unfold TypeWeightedRecommendationModel.typeFairness
    refine AppliedModelingLib.le_finiteMin
      (TypeWeightedRecommendationModel.normalizedTypeUtility
        (twoTypeReducedModel (1 - alpha) v) (mirrorTypePolicy ρ)) ?_
    intro k
    fin_cases k
    · have hle :=
        AppliedModelingLib.finiteMin_le
          (TypeWeightedRecommendationModel.normalizedTypeUtility
            (twoTypeReducedModel alpha v) ρ)
          (1 : UserType 2)
      simpa [twoTypeReducedModel_normalizedTypeUtility_mirror_zero_eq_one]
        using hle
    · have hle :=
        AppliedModelingLib.finiteMin_le
          (TypeWeightedRecommendationModel.normalizedTypeUtility
            (twoTypeReducedModel alpha v) ρ)
          (0 : UserType 2)
      simpa [twoTypeReducedModel_normalizedTypeUtility_mirror_one_eq_zero]
        using hle

/--
The inverse direction of mirror preservation for type fairness, useful when a
policy starts in the `1 - α` model and is mirrored back to the `α` model.
-/
theorem twoTypeReducedModel_typeFairness_mirror_eq_symm
    {n : ℕ} [NeZero n]
    (alpha : ℝ) (v : Item n → ℝ) (ρ : TypePolicy 2 n) :
    TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel alpha v) (mirrorTypePolicy ρ) =
      TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel (1 - alpha) v) ρ := by
  have h :=
    twoTypeReducedModel_typeFairness_mirror_eq (1 - alpha) v ρ
  have hsub : 1 - (1 - alpha) = alpha := by ring
  simpa [hsub] using h

/-- Positive base values give a positive common best-item denominator. -/
theorem twoTypeReducedModel_bestItemUtility_zero_pos {n : ℕ} [NeZero n]
    (alpha : ℝ) (v : Item n → ℝ)
    (hpos : ∀ j : Item n, 0 < v j) :
    0 < TypeWeightedRecommendationModel.bestItemUtility
      (twoTypeReducedModel alpha v) 0 := by
  let j0 : Item n := Classical.choice inferInstance
  unfold TypeWeightedRecommendationModel.bestItemUtility
  change 0 < AppliedModelingLib.finiteMax v
  exact lt_of_lt_of_le (hpos j0) (AppliedModelingLib.le_finiteMax v j0)

/-- Item normalizers in the two-type model are the denominators of `q_j(α)`. -/
theorem twoTypeReducedModel_itemNormalizer_eq {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) (j : Item n) :
    TypeWeightedRecommendationModel.itemNormalizer
      (twoTypeReducedModel alpha v) j =
      alpha * v j + (1 - alpha) * v (reverseItem j) := by
  unfold TypeWeightedRecommendationModel.itemNormalizer
  have huniv : (Finset.univ : Finset (UserType 2)) = {0, 1} := by
    decide
  rw [huniv]
  simp

/-- Raw item utility in the two-type model expanded by type policies. -/
theorem twoTypeReducedModel_rawItemUtility_eq {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) (ρ : TypePolicy 2 n) (j : Item n) :
    TypeWeightedRecommendationModel.rawItemUtility
      (twoTypeReducedModel alpha v) ρ j =
      alpha * v j * (ρ 0 j).toReal +
        (1 - alpha) * v (reverseItem j) * (ρ 1 j).toReal := by
  unfold TypeWeightedRecommendationModel.rawItemUtility
  have huniv : (Finset.univ : Finset (UserType 2)) = {0, 1} := by
    decide
  rw [huniv]
  simp

/-- Mirroring sends the item normalizer at `j` to the original one at `n-j+1`. -/
theorem twoTypeReducedModel_itemNormalizer_mirror_eq_reverse {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) (j : Item n) :
    TypeWeightedRecommendationModel.itemNormalizer
        (twoTypeReducedModel (1 - alpha) v) j =
      TypeWeightedRecommendationModel.itemNormalizer
        (twoTypeReducedModel alpha v) (reverseItem j) := by
  rw [twoTypeReducedModel_itemNormalizer_eq,
    twoTypeReducedModel_itemNormalizer_eq, reverseItem_reverseItem]
  ring

/-- Mirroring sends raw item utility at `j` to the original one at `n-j+1`. -/
theorem twoTypeReducedModel_rawItemUtility_mirror_eq_reverse {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) (ρ : TypePolicy 2 n) (j : Item n) :
    TypeWeightedRecommendationModel.rawItemUtility
        (twoTypeReducedModel (1 - alpha) v) (mirrorTypePolicy ρ) j =
      TypeWeightedRecommendationModel.rawItemUtility
        (twoTypeReducedModel alpha v) ρ (reverseItem j) := by
  rw [twoTypeReducedModel_rawItemUtility_eq,
    twoTypeReducedModel_rawItemUtility_eq, reverseItem_reverseItem]
  simp
  ring

/-- Mirroring sends normalized item utility at `j` to the original one at `n-j+1`. -/
theorem twoTypeReducedModel_normalizedItemUtility_mirror_eq_reverse {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) (ρ : TypePolicy 2 n) (j : Item n) :
    TypeWeightedRecommendationModel.normalizedItemUtility
        (twoTypeReducedModel (1 - alpha) v) (mirrorTypePolicy ρ) j =
      TypeWeightedRecommendationModel.normalizedItemUtility
        (twoTypeReducedModel alpha v) ρ (reverseItem j) := by
  unfold TypeWeightedRecommendationModel.normalizedItemUtility
  rw [twoTypeReducedModel_itemNormalizer_mirror_eq_reverse,
    twoTypeReducedModel_rawItemUtility_mirror_eq_reverse]

/-- Mirroring preserves item fairness. -/
theorem twoTypeReducedModel_itemFairness_mirror_eq {n : ℕ} [NeZero n]
    (alpha : ℝ) (v : Item n → ℝ) (ρ : TypePolicy 2 n) :
    TypeWeightedRecommendationModel.itemFairness
        (twoTypeReducedModel (1 - alpha) v) (mirrorTypePolicy ρ) =
      TypeWeightedRecommendationModel.itemFairness
        (twoTypeReducedModel alpha v) ρ := by
  unfold TypeWeightedRecommendationModel.itemFairness
  rw [← finiteMin_reverseItem
    (fun j : Item n =>
      TypeWeightedRecommendationModel.normalizedItemUtility
        (twoTypeReducedModel alpha v) ρ j)]
  apply congrArg AppliedModelingLib.finiteMin
  funext j
  exact twoTypeReducedModel_normalizedItemUtility_mirror_eq_reverse
    alpha v ρ j

/--
The inverse direction of mirror preservation for item fairness, useful when a
policy starts in the `1 - α` model and is mirrored back to the `α` model.
-/
theorem twoTypeReducedModel_itemFairness_mirror_eq_symm
    {n : ℕ} [NeZero n]
    (alpha : ℝ) (v : Item n → ℝ) (ρ : TypePolicy 2 n) :
    TypeWeightedRecommendationModel.itemFairness
        (twoTypeReducedModel alpha v) (mirrorTypePolicy ρ) =
      TypeWeightedRecommendationModel.itemFairness
        (twoTypeReducedModel (1 - alpha) v) ρ := by
  have h :=
    twoTypeReducedModel_itemFairness_mirror_eq (1 - alpha) v ρ
  have hsub : 1 - (1 - alpha) = alpha := by ring
  simpa [hsub] using h

/-- Mirroring preserves the attainable item-fairness set. -/
theorem twoTypeReducedModel_attainableItemFairnessSet_mirror_eq
    {n : ℕ} [NeZero n] (alpha : ℝ) (v : Item n → ℝ) :
    TypeWeightedRecommendationModel.attainableItemFairnessSet
        (twoTypeReducedModel (1 - alpha) v) =
      TypeWeightedRecommendationModel.attainableItemFairnessSet
        (twoTypeReducedModel alpha v) := by
  ext r
  constructor
  · rintro ⟨ρ, rfl⟩
    exact ⟨mirrorTypePolicy ρ,
      (twoTypeReducedModel_itemFairness_mirror_eq_symm alpha v ρ).symm⟩
  · rintro ⟨ρ, rfl⟩
    exact ⟨mirrorTypePolicy ρ,
      (twoTypeReducedModel_itemFairness_mirror_eq alpha v ρ).symm⟩

/-- Mirroring preserves the optimal item-fairness value. -/
theorem twoTypeReducedModel_optimalItemFairness_mirror_eq
    {n : ℕ} [NeZero n] (alpha : ℝ) (v : Item n → ℝ) :
    TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel (1 - alpha) v) =
      TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel alpha v) := by
  unfold TypeWeightedRecommendationModel.optimalItemFairness
  rw [twoTypeReducedModel_attainableItemFairnessSet_mirror_eq]

/-- Mirroring preserves the attainable type-fairness set at `γ = 1`. -/
theorem twoTypeReducedModel_attainableTypeFairnessAtLevel_one_mirror_eq
    {n : ℕ} [NeZero n] (alpha : ℝ) (v : Item n → ℝ) :
    TypeWeightedRecommendationModel.attainableTypeFairnessAtLevel
        (twoTypeReducedModel (1 - alpha) v) 1 =
      TypeWeightedRecommendationModel.attainableTypeFairnessAtLevel
        (twoTypeReducedModel alpha v) 1 := by
  ext r
  constructor
  · rintro ⟨ρ, hfeas, rfl⟩
    refine ⟨mirrorTypePolicy ρ, ?_, ?_⟩
    · unfold TypeWeightedRecommendationModel.feasibleAtLevel at hfeas ⊢
      rw [← twoTypeReducedModel_optimalItemFairness_mirror_eq alpha v,
        twoTypeReducedModel_itemFairness_mirror_eq_symm]
      exact hfeas
    · exact (twoTypeReducedModel_typeFairness_mirror_eq_symm alpha v ρ).symm
  · rintro ⟨ρ, hfeas, rfl⟩
    refine ⟨mirrorTypePolicy ρ, ?_, ?_⟩
    · unfold TypeWeightedRecommendationModel.feasibleAtLevel at hfeas ⊢
      rw [twoTypeReducedModel_optimalItemFairness_mirror_eq alpha v,
        twoTypeReducedModel_itemFairness_mirror_eq]
      exact hfeas
    · exact (twoTypeReducedModel_typeFairness_mirror_eq alpha v ρ).symm

/-- Mirroring preserves the optimal type-fairness value at `γ = 1`. -/
theorem twoTypeReducedModel_optimalTypeFairnessAtLevel_one_mirror_eq
    {n : ℕ} [NeZero n] (alpha : ℝ) (v : Item n → ℝ) :
    TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel (1 - alpha) v) 1 =
      TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel alpha v) 1 := by
  unfold TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
  rw [twoTypeReducedModel_attainableTypeFairnessAtLevel_one_mirror_eq]

/--
Problem 6 item-utility expansion: normalized item utility is the convex
combination `q_j(α) x_j + (1-q_j(α)) y_j`.
-/
theorem twoTypeReducedModel_normalizedItemUtility_eq_pairShare
    {n : ℕ} (alpha : ℝ) (v : Item n → ℝ) (ρ : TypePolicy 2 n) (j : Item n)
    (hden : 0 < alpha * v j + (1 - alpha) * v (reverseItem j)) :
    TypeWeightedRecommendationModel.normalizedItemUtility
      (twoTypeReducedModel alpha v) ρ j =
      pairShare alpha v j * (ρ 0 j).toReal +
        (1 - pairShare alpha v j) * (ρ 1 j).toReal := by
  unfold TypeWeightedRecommendationModel.normalizedItemUtility
  rw [twoTypeReducedModel_itemNormalizer_eq]
  simp [hden.ne']
  rw [twoTypeReducedModel_rawItemUtility_eq]
  unfold pairShare typeOneShare
  field_simp [hden.ne']
  ring

/--
Problem 6 LP feasibility in the paper's `x_j`, `y_j`, `q_j(α)`, `λ` notation.
For a type policy `ρ`, `x_j` is `ρ 0 j` and `y_j` is `ρ 1 j`.
-/
def problem6LPFeasible {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) (ρ : TypePolicy 2 n) (ell : ℝ) : Prop :=
  ∀ j : Item n,
    ell ≤ pairShare alpha v j * (ρ 0 j).toReal +
      (1 - pairShare alpha v j) * (ρ 1 j).toReal

/-- Problem 6 variable nonnegativity for `x_j = ρ_{0j}`. -/
theorem problem6_typeZero_prob_nonneg {n : ℕ}
    (ρ : TypePolicy 2 n) (j : Item n) :
    0 ≤ (ρ 0 j).toReal := by
  exact ENNReal.toReal_nonneg

/-- Problem 6 variable nonnegativity for `y_j = ρ_{1j}`. -/
theorem problem6_typeOne_prob_nonneg {n : ℕ}
    (ρ : TypePolicy 2 n) (j : Item n) :
    0 ≤ (ρ 1 j).toReal := by
  exact ENNReal.toReal_nonneg

/-- Problem 6 row constraint `∑_j x_j = 1`. -/
theorem problem6_typeZero_sum_eq_one {n : ℕ}
    (ρ : TypePolicy 2 n) :
    (∑ j : Item n, (ρ 0 j).toReal) = 1 := by
  exact AppliedModelingLib.pmfToRealSum (ρ 0)

/-- Problem 6 row constraint `∑_j y_j = 1`. -/
theorem problem6_typeOne_sum_eq_one {n : ℕ}
    (ρ : TypePolicy 2 n) :
    (∑ j : Item n, (ρ 1 j).toReal) = 1 := by
  exact AppliedModelingLib.pmfToRealSum (ρ 1)

/-- Lemma 5's left-side sum `L_t = ∑_{j<t} 1 / q_j`. -/
noncomputable def problem6LeftSum {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) (t : Item n) : ℝ :=
  ∑ j : Item n, if j.val < t.val then (pairShare alpha v j)⁻¹ else 0

/-- Lemma 5's right-side sum `R_t = ∑_{j>t} 1 / (1 - q_j)`. -/
noncomputable def problem6RightSum {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) (t : Item n) : ℝ :=
  ∑ j : Item n, if t.val < j.val then (1 - pairShare alpha v j)⁻¹ else 0

/-- Lemma 5's denominator `1 + q_t L_t + (1 - q_t) R_t`. -/
noncomputable def problem6ClosedDenominator {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) (t : Item n) : ℝ :=
  1 + pairShare alpha v t * problem6LeftSum alpha v t +
    (1 - pairShare alpha v t) * problem6RightSum alpha v t

/-- Lemma 5's closed-form value `I^*_min = 1 / (1 + q_t L_t + (1-q_t)R_t)`. -/
noncomputable def problem6ClosedValue {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) (t : Item n) : ℝ :=
  1 / problem6ClosedDenominator alpha v t

/-- Lemma 5's closed-form `x_j` coordinates for a fixed pivot `t`. -/
noncomputable def problem6ClosedX {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) (t j : Item n) : ℝ :=
  if j.val < t.val then
    problem6ClosedValue alpha v t / pairShare alpha v j
  else if j = t then
    1 - problem6ClosedValue alpha v t * problem6LeftSum alpha v t
  else
    0

/-- Lemma 5's closed-form `y_j` coordinates for a fixed pivot `t`. -/
noncomputable def problem6ClosedY {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) (t j : Item n) : ℝ :=
  if j.val < t.val then
    0
  else if j = t then
    1 - problem6ClosedValue alpha v t * problem6RightSum alpha v t
  else
    problem6ClosedValue alpha v t / (1 - pairShare alpha v j)

/--
The sparse, equalized solution shape produced by Lemma 4 and used in Lemma 5.
The real variables `x` and `y` correspond to the two type policies.
-/
structure Problem6SparseEqualized {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) (t : Item n)
    (x y : Item n → ℝ) (ell : ℝ) : Prop where
  item_eq :
    ∀ j : Item n,
      pairShare alpha v j * x j + (1 - pairShare alpha v j) * y j = ell
  sum_x : (∑ j : Item n, x j) = 1
  sum_y : (∑ j : Item n, y j) = 1
  x_after_pivot_zero : ∀ {j : Item n}, t.val < j.val → x j = 0
  y_before_pivot_zero : ∀ {j : Item n}, j.val < t.val → y j = 0

/--
The sparse equalized shape with the extra facts carried by the paper's pivot
choice `t = max {j : x_j > 0}`: nonnegative coordinates and positive `x_t`.
-/
structure Problem6SparseEqualizedActive {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) (t : Item n)
    (x y : Item n → ℝ) (ell : ℝ) : Prop where
  sparse : Problem6SparseEqualized alpha v t x y ell
  x_nonneg : ∀ j : Item n, 0 ≤ x j
  y_nonneg : ∀ j : Item n, 0 ≤ y j
  x_pivot_pos : 0 < x t

theorem problem6LeftSum_nonneg {n : ℕ}
    {alpha : ℝ} {v : Item n → ℝ} (t : Item n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j) :
    0 ≤ problem6LeftSum alpha v t := by
  unfold problem6LeftSum
  refine Finset.sum_nonneg ?_
  intro j _hj
  by_cases hlt : j.val < t.val
  · simp [hlt, inv_nonneg.mpr (pairShare_pos j halpha0 halpha1 hpos).le]
  · simp [hlt]

theorem problem6RightSum_nonneg {n : ℕ}
    {alpha : ℝ} {v : Item n → ℝ} (t : Item n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j) :
    0 ≤ problem6RightSum alpha v t := by
  unfold problem6RightSum
  refine Finset.sum_nonneg ?_
  intro j _hj
  by_cases hlt : t.val < j.val
  · simp [hlt, inv_nonneg.mpr (one_sub_pairShare_pos j halpha0 halpha1 hpos).le]
  · simp [hlt]

/--
Appendix D, Lemma 11 right-side sum monotonicity:
`(1-q_t)R_t` decreases with `α` for a fixed pivot.
-/
theorem lemma11_rightWeightedSum_antitone
    {n : ℕ} {alpha alpha' : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v) :
    (1 - pairShare alpha' v t) * problem6RightSum alpha' v t ≤
      (1 - pairShare alpha v t) * problem6RightSum alpha v t := by
  unfold problem6RightSum
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum ?_
  intro j _hj
  by_cases htj : t.val < j.val
  · have hterm :=
      lemma11_right_term_antitone
        halpha0 halpha1 halpha0' halpha1' halpha_le hpos hdec htj
    simpa [htj, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hterm
  · simp [htj]

/--
Appendix D, Lemma 11 paired-sum monotonicity: summing the paper's mirror-paired
pre-pivot terms preserves the antitonicity in `α`.
-/
theorem lemma11_pairedWeightedSum_antitone
    {n : ℕ} {alpha alpha' : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter : t.val ≤ (reverseItem t).val) :
    (∑ j : Item n, if j.val < t.val then
        pairShare alpha' v t / pairShare alpha' v j +
          (1 - pairShare alpha' v t) /
            (1 - pairShare alpha' v (reverseItem j)) else 0) ≤
      (∑ j : Item n, if j.val < t.val then
        pairShare alpha v t / pairShare alpha v j +
          (1 - pairShare alpha v t) /
            (1 - pairShare alpha v (reverseItem j)) else 0) := by
  refine Finset.sum_le_sum ?_
  intro j _hj
  by_cases hjt : j.val < t.val
  · simpa [hjt] using
      lemma11_paired_q_term_antitone
        halpha0 halpha1 halpha0' halpha1' halpha_le
        hpos hdec hcenter
  · simp [hjt]

/-- Expand the left part `q_t L_t` as the sum of ratios `q_t/q_j`. -/
theorem lemma11_leftWeightedSum_eq_leftRatioSum
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} (t : Item n) :
    pairShare alpha v t * problem6LeftSum alpha v t =
      ∑ j : Item n, if j.val < t.val then
        pairShare alpha v t / pairShare alpha v j else 0 := by
  unfold problem6LeftSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro j _hj
  by_cases hjt : j.val < t.val
  · simp [hjt, div_eq_mul_inv]
  · simp [hjt]

/-- Expand the right part `(1-q_t)R_t` as the sum of complement ratios. -/
theorem lemma11_rightWeightedSum_eq_rightRatioSum
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} (t : Item n) :
    (1 - pairShare alpha v t) * problem6RightSum alpha v t =
      ∑ j : Item n, if t.val < j.val then
        (1 - pairShare alpha v t) / (1 - pairShare alpha v j) else 0 := by
  unfold problem6RightSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro j _hj
  by_cases htj : t.val < j.val
  · simp [htj, div_eq_mul_inv]
  · simp [htj]

/--
Reindex the mirror-paired right terms by item reversal.  This is the finite-sum
form of replacing the paper's item `n-j+1` by its pre-pivot mate `j`.
-/
theorem lemma11_mirrorRightRatioSum_eq_prePivot
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} (t : Item n) :
    (∑ j : Item n, if j.val < t.val then
        (1 - pairShare alpha v t) /
          (1 - pairShare alpha v (reverseItem j)) else 0) =
      ∑ j : Item n, if (reverseItem j).val < t.val then
        (1 - pairShare alpha v t) / (1 - pairShare alpha v j) else 0 := by
  rw [← sum_reverseItem
    (fun j : Item n => if (reverseItem j).val < t.val then
      (1 - pairShare alpha v t) / (1 - pairShare alpha v j) else 0)]
  refine Finset.sum_congr rfl ?_
  intro j _hj
  simp [reverseItem_reverseItem]

/--
For a pivot at or before its mirror, the post-pivot right-side ratios split
into mirror-paired pre-pivot terms and the remaining middle/right residual.
-/
theorem lemma11_rightRatioSum_split_mirror_residual
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (hcenter : t.val ≤ (reverseItem t).val) :
    (∑ j : Item n, if t.val < j.val then
        (1 - pairShare alpha v t) / (1 - pairShare alpha v j) else 0) =
      (∑ j : Item n, if (reverseItem j).val < t.val then
        (1 - pairShare alpha v t) / (1 - pairShare alpha v j) else 0) +
      (∑ j : Item n, if t.val < j.val ∧
          t.val ≤ (reverseItem j).val then
        (1 - pairShare alpha v t) / (1 - pairShare alpha v j) else 0) := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro j _hj
  by_cases hrev : (reverseItem j).val < t.val
  · have htj : t.val < j.val := by
      have h :=
        reverseItem_after_pivot_of_before_pivot_of_pivot_le_reverse
          (t := t) (j := reverseItem j) hcenter hrev
      simpa [reverseItem_reverseItem] using h
    have hnle : ¬ t.val ≤ (reverseItem j).val := by omega
    simp [htj, hrev, hnle]
  · by_cases htj : t.val < j.val
    · have hle : t.val ≤ (reverseItem j).val := by omega
      simp [htj, hrev, hle]
    · simp [htj, hrev]

/--
Appendix D, Lemma 11 denominator decomposition: `q_t L_t + (1-q_t)R_t`
is the sum of the paper's mirror-paired pre-pivot terms plus the residual
post-pivot complement-ratio terms.
-/
theorem lemma11_weightedCore_eq_paired_add_residual
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (hcenter : t.val ≤ (reverseItem t).val) :
    pairShare alpha v t * problem6LeftSum alpha v t +
        (1 - pairShare alpha v t) * problem6RightSum alpha v t =
      (∑ j : Item n, if j.val < t.val then
        pairShare alpha v t / pairShare alpha v j +
          (1 - pairShare alpha v t) /
            (1 - pairShare alpha v (reverseItem j)) else 0) +
      (∑ j : Item n, if t.val < j.val ∧
          t.val ≤ (reverseItem j).val then
        (1 - pairShare alpha v t) / (1 - pairShare alpha v j) else 0) := by
  have hleft := lemma11_leftWeightedSum_eq_leftRatioSum
    (alpha := alpha) (v := v) t
  have hright := lemma11_rightWeightedSum_eq_rightRatioSum
    (alpha := alpha) (v := v) t
  have hmirror := lemma11_mirrorRightRatioSum_eq_prePivot
    (alpha := alpha) (v := v) t
  have hsplit := lemma11_rightRatioSum_split_mirror_residual
    (alpha := alpha) (v := v) (t := t) hcenter
  have hpaired :
      (∑ j : Item n, if j.val < t.val then
        pairShare alpha v t / pairShare alpha v j else 0) +
      (∑ j : Item n, if j.val < t.val then
        (1 - pairShare alpha v t) /
          (1 - pairShare alpha v (reverseItem j)) else 0) =
      ∑ j : Item n, if j.val < t.val then
        pairShare alpha v t / pairShare alpha v j +
          (1 - pairShare alpha v t) /
            (1 - pairShare alpha v (reverseItem j)) else 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro j _hj
    by_cases hjt : j.val < t.val
    · simp [hjt]
    · simp [hjt]
  calc
    pairShare alpha v t * problem6LeftSum alpha v t +
        (1 - pairShare alpha v t) * problem6RightSum alpha v t
        =
      (∑ j : Item n, if j.val < t.val then
        pairShare alpha v t / pairShare alpha v j else 0) +
      (∑ j : Item n, if t.val < j.val then
        (1 - pairShare alpha v t) / (1 - pairShare alpha v j) else 0) := by
          rw [hleft, hright]
    _ =
      (∑ j : Item n, if j.val < t.val then
        pairShare alpha v t / pairShare alpha v j else 0) +
      ((∑ j : Item n, if (reverseItem j).val < t.val then
        (1 - pairShare alpha v t) / (1 - pairShare alpha v j) else 0) +
      (∑ j : Item n, if t.val < j.val ∧
          t.val ≤ (reverseItem j).val then
        (1 - pairShare alpha v t) / (1 - pairShare alpha v j) else 0)) := by
          rw [hsplit]
    _ =
      (∑ j : Item n, if j.val < t.val then
        pairShare alpha v t / pairShare alpha v j else 0) +
      ((∑ j : Item n, if j.val < t.val then
        (1 - pairShare alpha v t) /
          (1 - pairShare alpha v (reverseItem j)) else 0) +
      (∑ j : Item n, if t.val < j.val ∧
          t.val ≤ (reverseItem j).val then
        (1 - pairShare alpha v t) / (1 - pairShare alpha v j) else 0)) := by
          rw [← hmirror]
    _ =
      (∑ j : Item n, if j.val < t.val then
        pairShare alpha v t / pairShare alpha v j +
          (1 - pairShare alpha v t) /
            (1 - pairShare alpha v (reverseItem j)) else 0) +
      (∑ j : Item n, if t.val < j.val ∧
          t.val ≤ (reverseItem j).val then
        (1 - pairShare alpha v t) / (1 - pairShare alpha v j) else 0) := by
          rw [← hpaired]
          ring

/--
Appendix D, Lemma 11 residual right-sum monotonicity: the unpaired residual
post-pivot complement-ratio terms decrease with `α`.
-/
theorem lemma11_residualRightSum_antitone
    {n : ℕ} {alpha alpha' : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v) :
    (∑ j : Item n, if t.val < j.val ∧
          t.val ≤ (reverseItem j).val then
        (1 - pairShare alpha' v t) / (1 - pairShare alpha' v j) else 0) ≤
      (∑ j : Item n, if t.val < j.val ∧
          t.val ≤ (reverseItem j).val then
        (1 - pairShare alpha v t) / (1 - pairShare alpha v j) else 0) := by
  refine Finset.sum_le_sum ?_
  intro j _hj
  by_cases hcond : t < j ∧ t ≤ reverseItem j
  · have hterm :=
      lemma11_right_term_antitone
        halpha0 halpha1 halpha0' halpha1' halpha_le
        hpos hdec hcond.1
    simpa [hcond] using hterm
  · simp [hcond]

/--
Appendix D, Lemma 11 fixed-pivot denominator-core monotonicity:
`q_t L_t + (1-q_t)R_t` decreases with `α` when the pivot is at or before its
mirror.
-/
theorem lemma11_fixedPivotWeightedCore_antitone
    {n : ℕ} {alpha alpha' : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter : t.val ≤ (reverseItem t).val) :
    pairShare alpha' v t * problem6LeftSum alpha' v t +
        (1 - pairShare alpha' v t) * problem6RightSum alpha' v t ≤
      pairShare alpha v t * problem6LeftSum alpha v t +
        (1 - pairShare alpha v t) * problem6RightSum alpha v t := by
  rw [lemma11_weightedCore_eq_paired_add_residual
      (alpha := alpha') (v := v) (t := t) hcenter,
    lemma11_weightedCore_eq_paired_add_residual
      (alpha := alpha) (v := v) (t := t) hcenter]
  exact add_le_add
    (lemma11_pairedWeightedSum_antitone
      halpha0 halpha1 halpha0' halpha1' halpha_le
      hpos hdec hcenter)
    (lemma11_residualRightSum_antitone
      halpha0 halpha1 halpha0' halpha1' halpha_le hpos hdec)

/--
Appendix D, Lemma 11 fixed-pivot denominator monotonicity: the full Lemma 5
denominator decreases with `α` for a pivot at or before its mirror.
-/
theorem lemma11_fixedPivotDenominator_antitone
    {n : ℕ} {alpha alpha' : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter : t.val ≤ (reverseItem t).val) :
    problem6ClosedDenominator alpha' v t ≤
      problem6ClosedDenominator alpha v t := by
  unfold problem6ClosedDenominator
  have hcore :=
    lemma11_fixedPivotWeightedCore_antitone
      halpha0 halpha1 halpha0' halpha1' halpha_le hpos hdec hcenter
  nlinarith

/--
Appendix D, Lemma 10 exact-center case: at `α = 1/2`, an exact center pivot
has identical left and right inverse-share sums after mirror reindexing.
-/
theorem problem6LeftSum_half_eq_rightSum_half_of_pivot_eq_reverse {n : ℕ}
    {v : Item n → ℝ} {t : Item n}
    (hpos : ∀ j : Item n, 0 < v j)
    (hcenter : t.val = (reverseItem t).val) :
    problem6LeftSum (1 / 2) v t = problem6RightSum (1 / 2) v t := by
  unfold problem6LeftSum problem6RightSum
  rw [← sum_reverseItem
    (fun j : Item n =>
      if t.val < j.val then (1 - pairShare (1 / 2) v j)⁻¹ else 0)]
  refine Finset.sum_congr rfl ?_
  intro j _hj
  have hiff :=
    pivot_lt_reverseItem_iff_val_lt_pivot_of_pivot_eq_reverse
      (t := t) (j := j) hcenter
  by_cases hj : j.val < t.val
  · have hmirror : t.val < (reverseItem j).val := hiff.mpr hj
    have hshare := pairShare_half_eq_one_sub_reverse j hpos
    simpa [hj, hmirror, one_div] using hshare
  · have hmirror : ¬ t.val < (reverseItem j).val := by
      intro hlt
      exact hj (hiff.mp hlt)
    simp [hj, hmirror]

/--
Appendix D, Lemma 10 exact-center denominator simplification:
at `α = 1/2` and an exact center pivot, Lemma 5's denominator is `1 + L_t`.
-/
theorem problem6ClosedDenominator_half_center_eq_one_add_leftSum {n : ℕ}
    {v : Item n → ℝ} {t : Item n}
    (hpos : ∀ j : Item n, 0 < v j)
    (hcenter : t.val = (reverseItem t).val) :
    problem6ClosedDenominator (1 / 2) v t =
      1 + problem6LeftSum (1 / 2) v t := by
  have hsum :=
    problem6LeftSum_half_eq_rightSum_half_of_pivot_eq_reverse
      (v := v) (t := t) hpos hcenter
  have hshare := pairShare_half_eq_half_of_val_eq_reverse t hpos hcenter
  unfold problem6ClosedDenominator
  rw [hshare, ← hsum]
  ring

/-- The Lemma 5 denominator is strictly positive. -/
theorem problem6ClosedDenominator_pos {n : ℕ}
    {alpha : ℝ} {v : Item n → ℝ} (t : Item n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j) :
    0 < problem6ClosedDenominator alpha v t := by
  have hL := problem6LeftSum_nonneg t halpha0 halpha1 hpos
  have hR := problem6RightSum_nonneg t halpha0 halpha1 hpos
  have hq := (pairShare_pos t halpha0 halpha1 hpos).le
  have hqc := (one_sub_pairShare_pos t halpha0 halpha1 hpos).le
  unfold problem6ClosedDenominator
  nlinarith

/-- Lemma 5's closed-form value is positive. -/
theorem problem6ClosedValue_pos {n : ℕ}
    {alpha : ℝ} {v : Item n → ℝ} (t : Item n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j) :
    0 < problem6ClosedValue alpha v t := by
  unfold problem6ClosedValue
  exact one_div_pos.mpr
    (problem6ClosedDenominator_pos t halpha0 halpha1 hpos)

/--
Appendix D, Lemma 11 fixed-pivot value monotonicity: once the selected pivot
is held fixed, the closed-form `I^*_{min}` value increases with `α`.
-/
theorem lemma11_fixedPivotClosedValue_monotone
    {n : ℕ} {alpha alpha' : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter : t.val ≤ (reverseItem t).val) :
    problem6ClosedValue alpha v t ≤ problem6ClosedValue alpha' v t := by
  unfold problem6ClosedValue
  exact one_div_le_one_div_of_le
    (problem6ClosedDenominator_pos t halpha0' halpha1' hpos)
    (lemma11_fixedPivotDenominator_antitone
      halpha0 halpha1 halpha0' halpha1' halpha_le hpos hdec hcenter)

theorem problem6ClosedX_before {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) {t j : Item n}
    (hj : j.val < t.val) :
    problem6ClosedX alpha v t j =
      problem6ClosedValue alpha v t / pairShare alpha v j := by
  simp [problem6ClosedX, hj]

theorem problem6ClosedX_at {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) (t : Item n) :
    problem6ClosedX alpha v t t =
      1 - problem6ClosedValue alpha v t * problem6LeftSum alpha v t := by
  simp [problem6ClosedX]

theorem problem6ClosedX_after {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) {t j : Item n}
    (hj : t.val < j.val) :
    problem6ClosedX alpha v t j = 0 := by
  have hnlt : ¬ j.val < t.val := by omega
  have hne : j ≠ t := by
    intro h
    subst h
    omega
  simp [problem6ClosedX, hnlt, hne]

theorem problem6ClosedY_before {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) {t j : Item n}
    (hj : j.val < t.val) :
    problem6ClosedY alpha v t j = 0 := by
  simp [problem6ClosedY, hj]

theorem problem6ClosedY_at {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) (t : Item n) :
    problem6ClosedY alpha v t t =
      1 - problem6ClosedValue alpha v t * problem6RightSum alpha v t := by
  simp [problem6ClosedY]

theorem problem6ClosedY_after {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) {t j : Item n}
    (hj : t.val < j.val) :
    problem6ClosedY alpha v t j =
      problem6ClosedValue alpha v t / (1 - pairShare alpha v j) := by
  have hnlt : ¬ j.val < t.val := by omega
  have hne : j ≠ t := by
    intro h
    subst h
    omega
  simp [problem6ClosedY, hnlt, hne]

private theorem problem6_sum_eq_left_part_add_pivot_of_after_zero {n : ℕ}
    (x : Item n → ℝ) (t : Item n)
    (hzero : ∀ {j : Item n}, t.val < j.val → x j = 0) :
    (∑ j : Item n, x j) =
      (∑ j : Item n, if j.val < t.val then x j else 0) + x t := by
  classical
  calc
    (∑ j : Item n, x j)
        = ∑ j : Item n,
            ((if j.val < t.val then x j else 0) +
              (if j = t then x t else 0)) := by
          refine Finset.sum_congr rfl ?_
          intro j _hj
          by_cases hlt : j.val < t.val
          · have hne : j ≠ t := by
              intro h
              subst h
              omega
            simp [hlt, hne]
          · by_cases heq : j = t
            · subst heq
              simp
            · have hgt : t.val < j.val := by
                have hne_val : j.val ≠ t.val := by
                  intro hval
                  exact heq (Fin.ext hval)
                omega
              simp [hlt, heq, hzero hgt]
    _ = (∑ j : Item n, if j.val < t.val then x j else 0) +
          (∑ j : Item n, if j = t then x t else 0) := by
          rw [Finset.sum_add_distrib]
    _ = (∑ j : Item n, if j.val < t.val then x j else 0) + x t := by
          simp

private theorem problem6_sum_eq_pivot_add_right_part_of_before_zero {n : ℕ}
    (y : Item n → ℝ) (t : Item n)
    (hzero : ∀ {j : Item n}, j.val < t.val → y j = 0) :
    (∑ j : Item n, y j) =
      y t + (∑ j : Item n, if t.val < j.val then y j else 0) := by
  classical
  calc
    (∑ j : Item n, y j)
        = ∑ j : Item n,
            ((if j = t then y t else 0) +
              (if t.val < j.val then y j else 0)) := by
          refine Finset.sum_congr rfl ?_
          intro j _hj
          by_cases heq : j = t
          · subst heq
            simp
          · by_cases hgt : t.val < j.val
            · simp [heq, hgt]
            · have hlt : j.val < t.val := by
                have hne_val : j.val ≠ t.val := by
                  intro hval
                  exact heq (Fin.ext hval)
                omega
              simp [heq, hgt, hzero hlt]
    _ = (∑ j : Item n, if j = t then y t else 0) +
          (∑ j : Item n, if t.val < j.val then y j else 0) := by
          rw [Finset.sum_add_distrib]
    _ = y t + (∑ j : Item n, if t.val < j.val then y j else 0) := by
          simp

private theorem problem6_sum_eq_left_part_add_pivot_add_right_part {n : ℕ}
    (x : Item n → ℝ) (t : Item n) :
    (∑ j : Item n, x j) =
      (∑ j : Item n, if j.val < t.val then x j else 0) + x t +
        (∑ j : Item n, if t.val < j.val then x j else 0) := by
  classical
  calc
    (∑ j : Item n, x j)
        = ∑ j : Item n,
            ((if j.val < t.val then x j else 0) +
              (if j = t then x t else 0) +
              (if t.val < j.val then x j else 0)) := by
          refine Finset.sum_congr rfl ?_
          intro j _hj
          by_cases hlt : j.val < t.val
          · have hne : j ≠ t := by
              intro h
              subst h
              omega
            have hnlt : ¬ t.val < j.val := by omega
            simp [hlt, hne, hnlt]
          · by_cases heq : j = t
            · subst heq
              simp
            · have hgt : t.val < j.val := by
                have hne_val : j.val ≠ t.val := by
                  intro hval
                  exact heq (Fin.ext hval)
                omega
              simp [hlt, heq, hgt]
    _ =
        ((∑ j : Item n, if j.val < t.val then x j else 0) +
          (∑ j : Item n, if j = t then x t else 0)) +
          (∑ j : Item n, if t.val < j.val then x j else 0) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ = (∑ j : Item n, if j.val < t.val then x j else 0) + x t +
        (∑ j : Item n, if t.val < j.val then x j else 0) := by
          simp [add_assoc]

/--
Moving the closed-form pivot one item to the right adds the old pivot's
inverse `q` contribution to the left sum.
-/
theorem problem6LeftSum_next_eq {n : ℕ}
    {alpha : ℝ} {v : Item n → ℝ} {t u : Item n}
    (hnext : u.val = t.val + 1) :
    problem6LeftSum alpha v u =
      problem6LeftSum alpha v t + (pairShare alpha v t)⁻¹ := by
  let x : Item n → ℝ :=
    fun j => if j.val < u.val then (pairShare alpha v j)⁻¹ else 0
  have hzero : ∀ {j : Item n}, t.val < j.val → x j = 0 := by
    intro j hj
    have hnlt : ¬ j.val < u.val := by omega
    change (if j.val < u.val then (pairShare alpha v j)⁻¹ else 0) = 0
    simp [hnlt]
  have hsplit := problem6_sum_eq_left_part_add_pivot_of_after_zero x t hzero
  have hleft :
      (∑ j : Item n, if j.val < t.val then x j else 0) =
        problem6LeftSum alpha v t := by
    unfold problem6LeftSum
    refine Finset.sum_congr rfl ?_
    intro j _hj
    by_cases hjt : j.val < t.val
    · have hju : j.val < u.val := by omega
      rw [if_pos hjt, if_pos hjt]
      change (if j.val < u.val then (pairShare alpha v j)⁻¹ else 0) =
        (pairShare alpha v j)⁻¹
      rw [if_pos hju]
    · rw [if_neg hjt, if_neg hjt]
  have hpivot :
      x t = (pairShare alpha v t)⁻¹ := by
    have htu : t.val < u.val := by omega
    change (if t.val < u.val then (pairShare alpha v t)⁻¹ else 0) =
      (pairShare alpha v t)⁻¹
    simp [htu]
  calc
    problem6LeftSum alpha v u = ∑ j : Item n, x j := by
      unfold problem6LeftSum
      rfl
    _ = (∑ j : Item n, if j.val < t.val then x j else 0) + x t := hsplit
    _ = problem6LeftSum alpha v t + (pairShare alpha v t)⁻¹ := by
      rw [hleft, hpivot]

/--
Moving the closed-form pivot one item to the right removes the new pivot's
inverse `(1-q)` contribution from the right sum.
-/
theorem problem6RightSum_next_eq {n : ℕ}
    {alpha : ℝ} {v : Item n → ℝ} {t u : Item n}
    (hnext : u.val = t.val + 1) :
    problem6RightSum alpha v t =
      (1 - pairShare alpha v u)⁻¹ + problem6RightSum alpha v u := by
  let y : Item n → ℝ :=
    fun j => if t.val < j.val then (1 - pairShare alpha v j)⁻¹ else 0
  have hzero : ∀ {j : Item n}, j.val < u.val → y j = 0 := by
    intro j hj
    have hnlt : ¬ t.val < j.val := by omega
    change (if t.val < j.val then (1 - pairShare alpha v j)⁻¹ else 0) = 0
    simp [hnlt]
  have hsplit := problem6_sum_eq_pivot_add_right_part_of_before_zero y u hzero
  have hright :
      (∑ j : Item n, if u.val < j.val then y j else 0) =
        problem6RightSum alpha v u := by
    unfold problem6RightSum
    refine Finset.sum_congr rfl ?_
    intro j _hj
    by_cases huj : u.val < j.val
    · have htj : t.val < j.val := by omega
      rw [if_pos huj, if_pos huj]
      change (if t.val < j.val then (1 - pairShare alpha v j)⁻¹ else 0) =
        (1 - pairShare alpha v j)⁻¹
      rw [if_pos htj]
    · rw [if_neg huj, if_neg huj]
  have hpivot :
      y u = (1 - pairShare alpha v u)⁻¹ := by
    have htu : t.val < u.val := by omega
    change (if t.val < u.val then (1 - pairShare alpha v u)⁻¹ else 0) =
      (1 - pairShare alpha v u)⁻¹
    simp [htu]
  calc
    problem6RightSum alpha v t = ∑ j : Item n, y j := by
      unfold problem6RightSum
      rfl
    _ = y u + (∑ j : Item n, if u.val < j.val then y j else 0) := hsplit
    _ = (1 - pairShare alpha v u)⁻¹ + problem6RightSum alpha v u := by
      rw [hpivot, hright]

/-- The closed-form pivot-crossing gap `L_t - R_t`. -/
noncomputable def problem6PivotGap {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) (t : Item n) : ℝ :=
  problem6LeftSum alpha v t - problem6RightSum alpha v t

/--
Adjacent-pivot update for the closed-form crossing gap.  This is the discrete
intermediate-value arithmetic behind choosing the valid Lemma 5 pivot.
-/
theorem problem6PivotGap_next_eq {n : ℕ}
    {alpha : ℝ} {v : Item n → ℝ} {t u : Item n}
    (hnext : u.val = t.val + 1) :
    problem6PivotGap alpha v u =
      problem6PivotGap alpha v t + (pairShare alpha v t)⁻¹ +
        (1 - pairShare alpha v u)⁻¹ := by
  unfold problem6PivotGap
  rw [problem6LeftSum_next_eq (alpha := alpha) (v := v) hnext,
    problem6RightSum_next_eq (alpha := alpha) (v := v) hnext]
  ring

/-- The lower-crossing boundary gap `L_t - R_t + 1/q_t`. -/
noncomputable def problem6BoundaryGap {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) (t : Item n) : ℝ :=
  problem6PivotGap alpha v t + (pairShare alpha v t)⁻¹

/-- Vanishing boundary gap is the tight lower-crossing equation. -/
theorem problem6BoundaryGap_eq_zero_iff {n : ℕ}
    {alpha : ℝ} {v : Item n → ℝ} {t : Item n} :
    problem6BoundaryGap alpha v t = 0 ↔
      problem6PivotGap alpha v t = - (pairShare alpha v t)⁻¹ := by
  unfold problem6BoundaryGap
  constructor <;> intro h <;> linarith

/-- Nonnegative boundary gap is exactly the lower crossing inequality. -/
theorem problem6BoundaryGap_nonneg_iff_lower_crossing {n : ℕ}
    {alpha : ℝ} {v : Item n → ℝ} {t : Item n} :
    0 ≤ problem6BoundaryGap alpha v t ↔
      - (pairShare alpha v t)⁻¹ ≤ problem6PivotGap alpha v t := by
  unfold problem6BoundaryGap
  constructor <;> intro h <;> linarith

/-- Adjacent-pivot update for the lower-crossing boundary gap. -/
theorem problem6BoundaryGap_next_eq {n : ℕ}
    {alpha : ℝ} {v : Item n → ℝ} {t u : Item n}
    (hnext : u.val = t.val + 1) :
    problem6BoundaryGap alpha v u =
      problem6BoundaryGap alpha v t +
        (1 - pairShare alpha v u)⁻¹ + (pairShare alpha v u)⁻¹ := by
  unfold problem6BoundaryGap
  rw [problem6PivotGap_next_eq (alpha := alpha) (v := v) hnext]

/--
At a tight lower boundary for pivot `t`, the next pivot's lower-crossing
boundary gap is strictly positive.
-/
theorem problem6BoundaryGap_next_pos_of_boundary {n : ℕ}
    {alpha : ℝ} {v : Item n → ℝ} {t u : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hnext : u.val = t.val + 1)
    (hboundary :
      problem6PivotGap alpha v t = - (pairShare alpha v t)⁻¹) :
    0 < problem6BoundaryGap alpha v u := by
  have hzero : problem6BoundaryGap alpha v t = 0 :=
    problem6BoundaryGap_eq_zero_iff.mpr hboundary
  have hcomp_pos :
      0 < (1 - pairShare alpha v u)⁻¹ :=
    inv_pos.mpr (one_sub_pairShare_pos u halpha0 halpha1 hpos)
  have hq_pos :
      0 < (pairShare alpha v u)⁻¹ :=
    inv_pos.mpr (pairShare_pos u halpha0 halpha1 hpos)
  rw [problem6BoundaryGap_next_eq (alpha := alpha) (v := v) hnext,
    hzero]
  linarith

/-- The boundary gap is continuous on every compact subinterval of `(0,1)`. -/
theorem problem6BoundaryGap_continuousOn_Icc {n : ℕ}
    {alphaLeft alphaRight : ℝ} {v : Item n → ℝ} {t : Item n}
    (halphaLeft0 : 0 < alphaLeft) (halphaRight1 : alphaRight < 1)
    (hpos : ∀ j : Item n, 0 < v j) :
    ContinuousOn (fun alpha => problem6BoundaryGap alpha v t)
      (Set.Icc alphaLeft alphaRight) := by
  have hleft :
      ContinuousOn (fun alpha => problem6LeftSum alpha v t)
        (Set.Icc alphaLeft alphaRight) := by
    unfold problem6LeftSum
    refine continuousOn_finset_sum Finset.univ ?_
    intro j _hj
    by_cases hjt : j.val < t.val
    · have hq :=
        pairShare_continuousOn_Icc j halphaLeft0 halphaRight1 hpos
      have hq_ne :
          ∀ alpha ∈ Set.Icc alphaLeft alphaRight,
            pairShare alpha v j ≠ 0 := by
        intro alpha halpha
        exact ne_of_gt
          (pairShare_pos j
            (lt_of_lt_of_le halphaLeft0 halpha.1)
            (lt_of_le_of_lt halpha.2 halphaRight1)
            hpos)
      simpa [hjt] using hq.inv₀ hq_ne
    · simpa [hjt] using
        (continuousOn_const :
          ContinuousOn (fun _ : ℝ => (0 : ℝ))
            (Set.Icc alphaLeft alphaRight))
  have hright :
      ContinuousOn (fun alpha => problem6RightSum alpha v t)
        (Set.Icc alphaLeft alphaRight) := by
    unfold problem6RightSum
    refine continuousOn_finset_sum Finset.univ ?_
    intro j _hj
    by_cases htj : t.val < j.val
    · have hq :=
        one_sub_pairShare_continuousOn_Icc j
          halphaLeft0 halphaRight1 hpos
      have hq_ne :
          ∀ alpha ∈ Set.Icc alphaLeft alphaRight,
            1 - pairShare alpha v j ≠ 0 := by
        intro alpha halpha
        exact ne_of_gt
          (one_sub_pairShare_pos j
            (lt_of_lt_of_le halphaLeft0 halpha.1)
            (lt_of_le_of_lt halpha.2 halphaRight1)
            hpos)
      simpa [htj] using hq.inv₀ hq_ne
    · simpa [htj] using
        (continuousOn_const :
          ContinuousOn (fun _ : ℝ => (0 : ℝ))
            (Set.Icc alphaLeft alphaRight))
  have hpivot :
      ContinuousOn (fun alpha => pairShare alpha v t)
        (Set.Icc alphaLeft alphaRight) :=
    pairShare_continuousOn_Icc t halphaLeft0 halphaRight1 hpos
  have hpivot_ne :
      ∀ alpha ∈ Set.Icc alphaLeft alphaRight,
        pairShare alpha v t ≠ 0 := by
    intro alpha halpha
    exact ne_of_gt
      (pairShare_pos t
        (lt_of_lt_of_le halphaLeft0 halpha.1)
        (lt_of_le_of_lt halpha.2 halphaRight1)
        hpos)
  unfold problem6BoundaryGap problem6PivotGap
  exact (hleft.sub hright).add (hpivot.inv₀ hpivot_ne)

/--
If the lower crossing inequality for a pivot holds at the left endpoint and
fails at the right endpoint, then the tight crossing equation holds somewhere
between them.  This is the scalar IVT step used to construct Lemma 8 boundary
points.
-/
theorem problem6BoundaryGap_exists_zero_of_lower_crossing_changes {n : ℕ}
    {alphaLeft alphaRight : ℝ} {v : Item n → ℝ} {t : Item n}
    (halphaLeft0 : 0 < alphaLeft) (halphaRight1 : alphaRight < 1)
    (hleft_le_right : alphaLeft ≤ alphaRight)
    (hpos : ∀ j : Item n, 0 < v j)
    (hcross_left :
      - (pairShare alphaLeft v t)⁻¹ ≤ problem6PivotGap alphaLeft v t)
    (hnot_cross_right :
      ¬ - (pairShare alphaRight v t)⁻¹ ≤
        problem6PivotGap alphaRight v t) :
    ∃ alphaBoundary : ℝ,
      alphaLeft ≤ alphaBoundary ∧ alphaBoundary ≤ alphaRight ∧
      0 < alphaBoundary ∧ alphaBoundary < 1 ∧
      problem6PivotGap alphaBoundary v t =
        - (pairShare alphaBoundary v t)⁻¹ := by
  let F : ℝ → ℝ := fun alpha => problem6BoundaryGap alpha v t
  have hcont :
      ContinuousOn F (Set.Icc alphaLeft alphaRight) := by
    dsimp [F]
    exact problem6BoundaryGap_continuousOn_Icc
      halphaLeft0 halphaRight1 hpos
  have hleft_nonneg : 0 ≤ F alphaLeft := by
    dsimp [F]
    exact problem6BoundaryGap_nonneg_iff_lower_crossing.mpr hcross_left
  have hright_neg : F alphaRight < 0 := by
    have hnot_nonneg : ¬ 0 ≤ F alphaRight := by
      intro hnonneg
      exact hnot_cross_right
        (by
          dsimp [F] at hnonneg
          exact problem6BoundaryGap_nonneg_iff_lower_crossing.mp hnonneg)
    exact not_le.mp hnot_nonneg
  have hzero_between : 0 ∈ Set.Icc (F alphaRight) (F alphaLeft) :=
    ⟨le_of_lt hright_neg, hleft_nonneg⟩
  rcases intermediate_value_Icc' hleft_le_right hcont hzero_between with
    ⟨alphaBoundary, halphaBoundary, hzero⟩
  refine ⟨alphaBoundary, halphaBoundary.1, halphaBoundary.2,
    lt_of_lt_of_le halphaLeft0 halphaBoundary.1,
    lt_of_le_of_lt halphaBoundary.2 halphaRight1, ?_⟩
  dsimp [F] at hzero
  exact problem6BoundaryGap_eq_zero_iff.mp hzero

/--
Appendix D, Lemma 10 even-center case: when the midpoint candidate is
immediately before its mirror, the right inverse-share sum is the left sum plus
the pivot's inverse share.
-/
theorem problem6RightSum_half_eq_leftSum_half_add_inv_pairShare_of_pivot_succ_reverse
    {n : ℕ} {v : Item n → ℝ} {t : Item n}
    (hpos : ∀ j : Item n, 0 < v j)
    (hsucc : t.val + 1 = (reverseItem t).val) :
    problem6RightSum (1 / 2) v t =
      problem6LeftSum (1 / 2) v t + (pairShare (1 / 2) v t)⁻¹ := by
  unfold problem6LeftSum problem6RightSum
  rw [← sum_reverseItem
    (fun j : Item n =>
      if t.val < j.val then (1 - pairShare (1 / 2) v j)⁻¹ else 0)]
  have hreindex :
      (∑ j : Item n,
        if t.val < (reverseItem j).val then
          (1 - pairShare (1 / 2) v (reverseItem j))⁻¹
        else 0) =
        ∑ j : Item n,
          if j.val ≤ t.val then (pairShare (1 / 2) v j)⁻¹ else 0 := by
    refine Finset.sum_congr rfl ?_
    intro j _hj
    have hiff :=
      pivot_lt_reverseItem_iff_val_le_pivot_of_pivot_succ_reverse
        (t := t) (j := j) hsucc
    by_cases hj : j.val ≤ t.val
    · have hmirror : t.val < (reverseItem j).val := hiff.mpr hj
      have hshare := pairShare_half_eq_one_sub_reverse j hpos
      simpa [hj, hmirror, one_div] using hshare.symm
    · have hmirror : ¬ t.val < (reverseItem j).val := by
        intro hlt
        exact hj (hiff.mp hlt)
      simp [hj, hmirror]
  rw [hreindex]
  let x : Item n → ℝ :=
    fun j => if j.val ≤ t.val then (pairShare (1 / 2) v j)⁻¹ else 0
  have hzero : ∀ {j : Item n}, t.val < j.val → x j = 0 := by
    intro j hj
    have hnle_fin : ¬ j ≤ t := not_le.mpr hj
    simp [x, hnle_fin]
  have hsplit :=
    problem6_sum_eq_left_part_add_pivot_of_after_zero x t hzero
  have hleft :
      (∑ j : Item n, if j.val < t.val then x j else 0) =
        ∑ j : Item n,
          if j.val < t.val then (pairShare (1 / 2) v j)⁻¹ else 0 := by
    refine Finset.sum_congr rfl ?_
    intro j _hj
    by_cases hlt : j.val < t.val
    · have hle_fin : j ≤ t := le_of_lt hlt
      simp [x, hlt, hle_fin]
    · simp [x, hlt]
  calc
    (∑ j : Item n, if j.val ≤ t.val then
        (pairShare (1 / 2) v j)⁻¹ else 0)
        = (∑ j : Item n, if j.val < t.val then x j else 0) + x t := by
          simpa [x] using hsplit
    _ = (∑ j : Item n,
          if j.val < t.val then (pairShare (1 / 2) v j)⁻¹ else 0) +
          (pairShare (1 / 2) v t)⁻¹ := by
          rw [hleft]
          simp [x]

/--
Appendix D, Lemma 10 even-center case: for the midpoint pivot immediately
before its mirror, Lemma 5's denominator equals the right inverse-share sum.
-/
theorem problem6ClosedDenominator_half_succ_center_eq_rightSum {n : ℕ}
    {v : Item n → ℝ} {t : Item n}
    (hpos : ∀ j : Item n, 0 < v j)
    (hsucc : t.val + 1 = (reverseItem t).val) :
    problem6ClosedDenominator (1 / 2) v t =
      problem6RightSum (1 / 2) v t := by
  have hright :=
    problem6RightSum_half_eq_leftSum_half_add_inv_pairShare_of_pivot_succ_reverse
      (v := v) (t := t) hpos hsucc
  set q := pairShare (1 / 2) v t
  set L := problem6LeftSum (1 / 2) v t
  have hqpos : 0 < q := by
    simpa [q] using
      pairShare_pos t (by norm_num : (0 : ℝ) < 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1) hpos
  have hqne : q ≠ 0 := ne_of_gt hqpos
  unfold problem6ClosedDenominator
  rw [hright]
  change 1 + q * L + (1 - q) * (L + q⁻¹) = L + q⁻¹
  field_simp [hqne]
  ring

/-- The number of item indices strictly before `t`, packaged as a real sum. -/
theorem problem6_sum_left_const_eq {n : ℕ} (t : Item n) (c : ℝ) :
    (∑ j : Item n, if j.val < t.val then c else 0) =
      (t.val : ℝ) * c := by
  classical
  let s : Finset ℕ := Finset.range t.val
  let hs : ∀ m ∈ s, m < n := by
    intro m hm
    exact lt_trans (Finset.mem_range.mp hm) t.isLt
  have hfilter :
      (Finset.univ.filter fun j : Item n => j.val < t.val) =
        s.attachFin hs := by
    ext j
    simp [s]
  calc
    (∑ j : Item n, if j.val < t.val then c else 0) =
        ∑ j ∈ (Finset.univ.filter (fun j : Item n => j.val < t.val)), c := by
          rw [Finset.sum_filter]
    _ = ∑ j ∈ s.attachFin hs, c := by
          rw [hfilter]
    _ = (t.val : ℝ) * c := by
          simp [s, Finset.sum_const, nsmul_eq_mul]

/-- The number of item indices strictly after `t`, packaged as a real sum. -/
theorem problem6_sum_right_const_eq {n : ℕ} (t : Item n) (c : ℝ) :
    (∑ j : Item n, if t.val < j.val then c else 0) =
      ((n : ℝ) - (t.val : ℝ) - 1) * c := by
  have hsplit :=
    problem6_sum_eq_left_part_add_pivot_add_right_part
      (fun _ : Item n => c) t
  have hleft := problem6_sum_left_const_eq t c
  have htotal : (∑ _j : Item n, c) = (n : ℝ) * c := by
    simp [Finset.sum_const, nsmul_eq_mul, Item]
  nlinarith

/--
Appendix E true-model lower-bound denominator estimate, odd midpoint case:
the Lemma 5 closed value at the exact center is strictly above `1/n`.
-/
theorem problem6ClosedValue_half_center_gt_inv_card {n : ℕ} [NeZero n]
    {v : Item n → ℝ} {t : Item n}
    (hn : 1 < n)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter : t.val = (reverseItem t).val) :
    (n : ℝ)⁻¹ < problem6ClosedValue (1 / 2) v t := by
  have hcenter_arith : 2 * t.val + 1 = n := by
    exact (val_eq_reverseItem_iff t).mp hcenter
  have hcenter_real : (2 : ℝ) * (t.val : ℝ) + 1 = (n : ℝ) := by
    exact_mod_cast hcenter_arith
  have hleft_lt :
      problem6LeftSum (1 / 2) v t <
        ∑ j : Item n, if j.val < t.val then (2 : ℝ) else 0 := by
    unfold problem6LeftSum
    refine Finset.sum_lt_sum ?_ ?_
    · intro j _hj
      by_cases hjt : j.val < t.val
      · have hbefore : j.val < (reverseItem j).val := by
          rw [val_lt_reverseItem_iff]
          omega
        have hq_half :
            (1 / 2 : ℝ) < pairShare (1 / 2) v j :=
          half_lt_pairShare_half_of_val_lt_reverse j hpos hdec hbefore
        have hqpos :
            0 < pairShare (1 / 2) v j :=
          pairShare_pos j (by norm_num : (0 : ℝ) < 1 / 2)
            (by norm_num : (1 / 2 : ℝ) < 1) hpos
        have hinv_lt :
            (pairShare (1 / 2) v j)⁻¹ < (2 : ℝ) := by
          have h :=
            (inv_lt_inv₀ hqpos (by norm_num : (0 : ℝ) < 1 / 2)).2 hq_half
          norm_num at h
          exact h
        exact le_of_lt (by simpa [hjt] using hinv_lt)
      · simp [hjt]
    · refine ⟨firstItem, by simp, ?_⟩
      have hfirst_lt : (firstItem : Item n).val < t.val := by
        have htpos : 0 < t.val := by omega
        simpa using htpos
      have hbefore : (firstItem : Item n).val <
          (reverseItem (firstItem : Item n)).val := by
        rw [val_lt_reverseItem_iff]
        simp
        omega
      have hq_half :
          (1 / 2 : ℝ) < pairShare (1 / 2) v firstItem :=
        half_lt_pairShare_half_of_val_lt_reverse firstItem hpos hdec hbefore
      have hqpos :
          0 < pairShare (1 / 2) v firstItem :=
        pairShare_pos firstItem (by norm_num : (0 : ℝ) < 1 / 2)
          (by norm_num : (1 / 2 : ℝ) < 1) hpos
      have hinv_lt :
          (pairShare (1 / 2) v firstItem)⁻¹ < (2 : ℝ) := by
        have h :=
          (inv_lt_inv₀ hqpos (by norm_num : (0 : ℝ) < 1 / 2)).2 hq_half
        norm_num at h
        exact h
      change
        (if (firstItem : Item n).val < t.val then
            (pairShare (1 / 2) v firstItem)⁻¹ else 0) <
          if (firstItem : Item n).val < t.val then (2 : ℝ) else 0
      have hfirst_lt0 : 0 < t.val := by
        simpa using hfirst_lt
      simpa [firstItem, hfirst_lt0] using hinv_lt
  have hleft_count :
      (∑ j : Item n, if j.val < t.val then (2 : ℝ) else 0) =
        (t.val : ℝ) * 2 :=
    problem6_sum_left_const_eq t 2
  have hD_lt :
      problem6ClosedDenominator (1 / 2) v t < (n : ℝ) := by
    rw [problem6ClosedDenominator_half_center_eq_one_add_leftSum
      (v := v) (t := t) hpos hcenter]
    nlinarith [hleft_lt, hleft_count, hcenter_real]
  have hDpos :
      0 < problem6ClosedDenominator (1 / 2) v t :=
    problem6ClosedDenominator_pos t
      (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) hpos
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt hn)
  unfold problem6ClosedValue
  simpa [one_div] using (inv_lt_inv₀ hnpos hDpos).2 hD_lt

/--
Appendix E true-model lower-bound denominator estimate, even midpoint case:
the Lemma 5 closed value at the item immediately before its mirror is
strictly above `1/n`.
-/
theorem problem6ClosedValue_half_succ_center_gt_inv_card {n : ℕ} [NeZero n]
    {v : Item n → ℝ} {t : Item n}
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hsucc : t.val + 1 = (reverseItem t).val) :
    (n : ℝ)⁻¹ < problem6ClosedValue (1 / 2) v t := by
  have hsucc_arith : 2 * t.val + 2 = n := by
    simp [reverseItem] at hsucc
    omega
  have hsucc_real : (2 : ℝ) * (t.val : ℝ) + 2 = (n : ℝ) := by
    exact_mod_cast hsucc_arith
  have hright_lt :
      problem6RightSum (1 / 2) v t <
        ∑ j : Item n, if t.val < j.val then (2 : ℝ) else 0 := by
    unfold problem6RightSum
    refine Finset.sum_lt_sum ?_ ?_
    · intro j _hj
      by_cases htj : t.val < j.val
      · have hafter : (reverseItem j).val < j.val := by
          rw [reverseItem_val_lt_iff]
          omega
        have hq_half :
            pairShare (1 / 2) v j < (1 / 2 : ℝ) :=
          pairShare_half_lt_half_of_reverse_val_lt j hpos hdec hafter
        have hcomp_pos :
            0 < 1 - pairShare (1 / 2) v j :=
          one_sub_pairShare_pos j (by norm_num : (0 : ℝ) < 1 / 2)
            (by norm_num : (1 / 2 : ℝ) < 1) hpos
        have hcomp_half :
            (1 / 2 : ℝ) < 1 - pairShare (1 / 2) v j := by
          linarith
        have hinv_lt :
            (1 - pairShare (1 / 2) v j)⁻¹ < (2 : ℝ) := by
          have h :=
            (inv_lt_inv₀ hcomp_pos (by norm_num : (0 : ℝ) < 1 / 2)).2
              hcomp_half
          norm_num at h
          exact h
        exact le_of_lt (by simpa [htj] using hinv_lt)
      · simp [htj]
    · refine ⟨lastItem, by simp, ?_⟩
      have htlast : t.val < (lastItem : Item n).val := by
        simp
        omega
      have hafter : (reverseItem (lastItem : Item n)).val <
          (lastItem : Item n).val := by
        rw [reverseItem_val_lt_iff]
        simp
        omega
      have hq_half :
          pairShare (1 / 2) v lastItem < (1 / 2 : ℝ) :=
        pairShare_half_lt_half_of_reverse_val_lt lastItem hpos hdec hafter
      have hcomp_pos :
          0 < 1 - pairShare (1 / 2) v lastItem :=
        one_sub_pairShare_pos lastItem (by norm_num : (0 : ℝ) < 1 / 2)
          (by norm_num : (1 / 2 : ℝ) < 1) hpos
      have hcomp_half :
          (1 / 2 : ℝ) < 1 - pairShare (1 / 2) v lastItem := by
        linarith
      have hinv_lt :
          (1 - pairShare (1 / 2) v lastItem)⁻¹ < (2 : ℝ) := by
        have h :=
          (inv_lt_inv₀ hcomp_pos (by norm_num : (0 : ℝ) < 1 / 2)).2
            hcomp_half
        norm_num at h
        exact h
      change
        (if t < (lastItem : Item n) then
            (1 - pairShare (1 / 2) v lastItem)⁻¹ else 0) <
          if t < (lastItem : Item n) then (2 : ℝ) else 0
      have htlast_fin : t < (lastItem : Item n) := by
        simpa using htlast
      simpa [htlast_fin] using hinv_lt
  have hright_count :
      (∑ j : Item n, if t.val < j.val then (2 : ℝ) else 0) =
        ((n : ℝ) - (t.val : ℝ) - 1) * 2 :=
    problem6_sum_right_const_eq t 2
  have hD_lt :
      problem6ClosedDenominator (1 / 2) v t < (n : ℝ) := by
    rw [problem6ClosedDenominator_half_succ_center_eq_rightSum
      (v := v) (t := t) hpos hsucc]
    nlinarith [hright_lt, hright_count, hsucc_real]
  have hDpos :
      0 < problem6ClosedDenominator (1 / 2) v t :=
    problem6ClosedDenominator_pos t
      (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) hpos
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  unfold problem6ClosedValue
  simpa [one_div] using (inv_lt_inv₀ hnpos hDpos).2 hD_lt

/-- Lemma 5: before the pivot, `x_j = λ / q_j`. -/
theorem problem6SparseEqualized_x_before_eq
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {t j : Item n}
    {x y : Item n → ℝ} {ell : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (h : Problem6SparseEqualized alpha v t x y ell)
    (hj : j.val < t.val) :
    x j = ell / pairShare alpha v j := by
  have hqne : pairShare alpha v j ≠ 0 :=
    ne_of_gt (pairShare_pos j halpha0 halpha1 hpos)
  have hmul : pairShare alpha v j * x j = ell := by
    have heq := h.item_eq j
    rw [h.y_before_pivot_zero hj] at heq
    simpa using heq
  calc
    x j = (pairShare alpha v j * x j) / pairShare alpha v j := by
      field_simp [hqne]
    _ = ell / pairShare alpha v j := by
      rw [hmul]

/-- Lemma 5: after the pivot, `y_j = λ / (1 - q_j)`. -/
theorem problem6SparseEqualized_y_after_eq
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {t j : Item n}
    {x y : Item n → ℝ} {ell : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (h : Problem6SparseEqualized alpha v t x y ell)
    (hj : t.val < j.val) :
    y j = ell / (1 - pairShare alpha v j) := by
  have hqne : 1 - pairShare alpha v j ≠ 0 :=
    ne_of_gt (one_sub_pairShare_pos j halpha0 halpha1 hpos)
  have hmul : (1 - pairShare alpha v j) * y j = ell := by
    have heq := h.item_eq j
    rw [h.x_after_pivot_zero hj] at heq
    simpa using heq
  calc
    y j = ((1 - pairShare alpha v j) * y j) /
        (1 - pairShare alpha v j) := by
      field_simp [hqne]
    _ = ell / (1 - pairShare alpha v j) := by
      rw [hmul]

/--
Appendix D, Lemma 4 comparison core.  A sparse equalized solution whose pivot
is to the right of another sparse equalized candidate cannot have a strictly
larger value, provided the later solution's `x` masses and the candidate's
pivot `y` mass are nonnegative.
-/
theorem problem6SparseEqualized_value_le_of_candidate_before_general
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {c t : Item n}
    {x y x' y' : Item n → ℝ} {ell ell' : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hct : c.val < t.val)
    (h : Problem6SparseEqualized alpha v t x y ell)
    (hcand : Problem6SparseEqualized alpha v c x' y' ell')
    (hx_nonneg : ∀ j : Item n, 0 ≤ x j)
    (hy'_pivot_nonneg : 0 ≤ y' c) :
    ell ≤ ell' := by
  by_contra hnot
  have hell_lt : ell' < ell := lt_of_not_ge hnot
  let q : ℝ := pairShare alpha v c
  have hqpos : 0 < q := by
    simpa [q] using
      pairShare_pos c halpha0 halpha1 hpos
  have hqnonneg : 0 ≤ q := hqpos.le
  have hqcomp_nonneg : 0 ≤ 1 - q := by
    have hqcomp_pos :
        0 < 1 - pairShare alpha v c :=
      one_sub_pairShare_pos c halpha0 halpha1 hpos
    simpa [q] using hqcomp_pos.le
  have hitem_later : q * x c = ell := by
    have heq := h.item_eq c
    rw [h.y_before_pivot_zero hct] at heq
    simpa [q] using heq
  have hitem_candidate : q * x' c + (1 - q) * y' c = ell' := by
    have heq := hcand.item_eq c
    simpa [q] using heq
  have hstrict :
      q * x c > q * x' c + (1 - q) * y' c := by
    nlinarith
  let leftx : ℝ :=
    ∑ j : Item n, if j.val < c.val then x j else 0
  let leftx' : ℝ :=
    ∑ j : Item n, if j.val < c.val then x' j else 0
  have hleft_le : leftx' ≤ leftx := by
    unfold leftx leftx'
    refine Finset.sum_le_sum ?_
    intro j _hj
    by_cases hjc : j.val < c.val
    · have hjt : j.val < t.val := lt_trans hjc hct
      have hqj_nonneg :
          0 ≤ pairShare alpha v j :=
        (pairShare_pos j halpha0 halpha1 hpos).le
      simp [hjc]
      rw [problem6SparseEqualized_x_before_eq
          halpha0 halpha1 hpos hcand hjc,
        problem6SparseEqualized_x_before_eq
          halpha0 halpha1 hpos h hjt]
      exact div_le_div_of_nonneg_right hell_lt.le hqj_nonneg
    · simp [hjc]
  have hsplit_candidate :=
    problem6_sum_eq_left_part_add_pivot_of_after_zero
      x' c hcand.x_after_pivot_zero
  have hx'_pivot : x' c = 1 - leftx' := by
    have hsum :
        (∑ j : Item n, x' j) = leftx' + x' c := by
      simpa [leftx'] using hsplit_candidate
    nlinarith [hcand.sum_x, hsum]
  let rightx : ℝ :=
    ∑ j : Item n, if c.val < j.val then x j else 0
  have hright_nonneg : 0 ≤ rightx := by
    unfold rightx
    refine Finset.sum_nonneg ?_
    intro j _hj
    by_cases hj : c.val < j.val
    · simp [hj, hx_nonneg j]
    · simp [hj]
  have hsplit_later :=
    problem6_sum_eq_left_part_add_pivot_add_right_part x c
  have hxc_le : x c ≤ 1 - leftx := by
    have hsum :
        (∑ j : Item n, x j) = leftx + x c + rightx := by
      simpa [leftx, rightx] using hsplit_later
    nlinarith [h.sum_x, hsum, hright_nonneg]
  have hx'_ge : 1 - leftx ≤ x' c := by
    nlinarith [hx'_pivot, hleft_le]
  have hcandidate_ge :
      q * (1 - leftx) ≤ q * x' c + (1 - q) * y' c := by
    have hq_part : q * (1 - leftx) ≤ q * x' c :=
      mul_le_mul_of_nonneg_left hx'_ge hqnonneg
    have hy_part : 0 ≤ (1 - q) * y' c :=
      mul_nonneg hqcomp_nonneg hy'_pivot_nonneg
    nlinarith
  have hlater_le : q * x c ≤ q * (1 - leftx) :=
    mul_le_mul_of_nonneg_left hxc_le hqnonneg
  nlinarith

/--
Appendix D, Lemma 10 comparison core at the midpoint.  This is the `α = 1/2`
specialization used by the midpoint candidate construction.
-/
theorem problem6SparseEqualized_value_le_of_candidate_before
    {n : ℕ} {v : Item n → ℝ} {c t : Item n}
    {x y x' y' : Item n → ℝ} {ell ell' : ℝ}
    (hpos : ∀ j : Item n, 0 < v j)
    (hct : c.val < t.val)
    (h : Problem6SparseEqualized (1 / 2) v t x y ell)
    (hcand : Problem6SparseEqualized (1 / 2) v c x' y' ell')
    (hx_nonneg : ∀ j : Item n, 0 ≤ x j)
    (hy'_pivot_nonneg : 0 ≤ y' c) :
    ell ≤ ell' := by
  exact problem6SparseEqualized_value_le_of_candidate_before_general
    (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
    hpos hct h hcand hx_nonneg hy'_pivot_nonneg

private theorem problem6SparseEqualized_left_part_sum_eq
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    {x y : Item n → ℝ} {ell : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (h : Problem6SparseEqualized alpha v t x y ell) :
    (∑ j : Item n, if j.val < t.val then x j else 0) =
      ell * problem6LeftSum alpha v t := by
  unfold problem6LeftSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro j _hj
  by_cases hj : j.val < t.val
  · simp [hj, problem6SparseEqualized_x_before_eq
      halpha0 halpha1 hpos h hj, div_eq_mul_inv]
  · simp [hj]

private theorem problem6SparseEqualized_right_part_sum_eq
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    {x y : Item n → ℝ} {ell : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (h : Problem6SparseEqualized alpha v t x y ell) :
    (∑ j : Item n, if t.val < j.val then y j else 0) =
      ell * problem6RightSum alpha v t := by
  unfold problem6RightSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro j _hj
  by_cases hj : t.val < j.val
  · simp [hj, problem6SparseEqualized_y_after_eq
      halpha0 halpha1 hpos h hj, div_eq_mul_inv]
  · simp [hj]

private theorem problem6ClosedX_left_part_sum_eq
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {t : Item n} :
    (∑ j : Item n,
        if j.val < t.val then problem6ClosedX alpha v t j else 0) =
      problem6ClosedValue alpha v t * problem6LeftSum alpha v t := by
  unfold problem6LeftSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro j _hj
  by_cases hj : j.val < t.val
  · simp [hj, problem6ClosedX_before alpha v hj, div_eq_mul_inv]
  · simp [hj]

private theorem problem6ClosedY_right_part_sum_eq
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {t : Item n} :
    (∑ j : Item n,
        if t.val < j.val then problem6ClosedY alpha v t j else 0) =
      problem6ClosedValue alpha v t * problem6RightSum alpha v t := by
  unfold problem6RightSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro j _hj
  by_cases hj : t.val < j.val
  · simp [hj, problem6ClosedY_after alpha v hj, div_eq_mul_inv]
  · simp [hj]

/-- The closed-form `x_j` coordinates sum to one. -/
theorem problem6ClosedX_sum_eq_one {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) (t : Item n) :
    (∑ j : Item n, problem6ClosedX alpha v t j) = 1 := by
  have hsplit :=
    problem6_sum_eq_left_part_add_pivot_of_after_zero
      (problem6ClosedX alpha v t) t
      (fun {j} hj => problem6ClosedX_after alpha v hj)
  have hleft : (∑ j : Item n,
        if j.val < t.val then problem6ClosedX alpha v t j else 0) =
      problem6ClosedValue alpha v t * problem6LeftSum alpha v t :=
    problem6ClosedX_left_part_sum_eq
  rw [hsplit, hleft, problem6ClosedX_at]
  ring

/-- The closed-form `y_j` coordinates sum to one. -/
theorem problem6ClosedY_sum_eq_one {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) (t : Item n) :
    (∑ j : Item n, problem6ClosedY alpha v t j) = 1 := by
  have hsplit :=
    problem6_sum_eq_pivot_add_right_part_of_before_zero
      (problem6ClosedY alpha v t) t
      (fun {j} hj => problem6ClosedY_before alpha v hj)
  have hright : (∑ j : Item n,
        if t.val < j.val then problem6ClosedY alpha v t j else 0) =
      problem6ClosedValue alpha v t * problem6RightSum alpha v t :=
    problem6ClosedY_right_part_sum_eq
  rw [hsplit, hright, problem6ClosedY_at]
  ring

/-- The closed-form coordinates equalize every Problem 6 item constraint. -/
theorem problem6Closed_item_eq {n : ℕ}
    {alpha : ℝ} {v : Item n → ℝ} (t j : Item n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j) :
    pairShare alpha v j * problem6ClosedX alpha v t j +
        (1 - pairShare alpha v j) * problem6ClosedY alpha v t j =
      problem6ClosedValue alpha v t := by
  by_cases hlt : j.val < t.val
  · rw [problem6ClosedX_before alpha v hlt,
      problem6ClosedY_before alpha v hlt]
    have hqne : pairShare alpha v j ≠ 0 :=
      ne_of_gt (pairShare_pos j halpha0 halpha1 hpos)
    field_simp [hqne]
    ring
  · by_cases heq : j = t
    · subst j
      rw [problem6ClosedX_at, problem6ClosedY_at]
      have hmul :
          problem6ClosedValue alpha v t *
              problem6ClosedDenominator alpha v t = 1 := by
        unfold problem6ClosedValue
        field_simp [ne_of_gt
          (problem6ClosedDenominator_pos t halpha0 halpha1 hpos)]
      unfold problem6ClosedDenominator at hmul
      nlinarith
    · have hgt : t.val < j.val := by
        have hne_val : j.val ≠ t.val := by
          intro hval
          exact heq (Fin.ext hval)
        omega
      rw [problem6ClosedX_after alpha v hgt,
        problem6ClosedY_after alpha v hgt]
      have hqne : 1 - pairShare alpha v j ≠ 0 :=
        ne_of_gt (one_sub_pairShare_pos j halpha0 halpha1 hpos)
      field_simp [hqne]
      ring

/--
The Lemma 5 closed-form coordinates satisfy the sparse, equalized real LP
shape for every pivot. Nonnegativity of the pivot coordinates is the remaining
condition needed to turn this real certificate into a probability policy.
-/
theorem problem6Closed_sparseEqualized {n : ℕ}
    {alpha : ℝ} {v : Item n → ℝ} (t : Item n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j) :
    Problem6SparseEqualized alpha v t
      (problem6ClosedX alpha v t) (problem6ClosedY alpha v t)
      (problem6ClosedValue alpha v t) where
  item_eq := fun j => problem6Closed_item_eq t j halpha0 halpha1 hpos
  sum_x := problem6ClosedX_sum_eq_one alpha v t
  sum_y := problem6ClosedY_sum_eq_one alpha v t
  x_after_pivot_zero := fun {j} hj => problem6ClosedX_after alpha v hj
  y_before_pivot_zero := fun {j} hj => problem6ClosedY_before alpha v hj

/--
The only coordinate-level nonnegativity conditions not automatic from the
closed form: the two pivot masses.
-/
structure Problem6ClosedNonnegativePivots {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) (t : Item n) : Prop where
  x_pivot_nonneg : 0 ≤ problem6ClosedX alpha v t t
  y_pivot_nonneg : 0 ≤ problem6ClosedY alpha v t t

/--
A denominator-bound certificate implying the two closed-form pivot masses are
nonnegative.
-/
structure Problem6ClosedPivotDenominatorBounds {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) (t : Item n) : Prop where
  left_le_denominator :
    problem6LeftSum alpha v t ≤ problem6ClosedDenominator alpha v t
  right_le_denominator :
    problem6RightSum alpha v t ≤ problem6ClosedDenominator alpha v t

/-- Left pivot-mass denominator slack written in terms of the gap `L_t - R_t`. -/
theorem problem6ClosedDenominator_sub_leftSum_eq {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) (t : Item n) :
    problem6ClosedDenominator alpha v t -
        problem6LeftSum alpha v t =
      1 - (1 - pairShare alpha v t) * problem6PivotGap alpha v t := by
  unfold problem6ClosedDenominator problem6PivotGap
  ring

/-- Right pivot-mass denominator slack written in terms of the gap `L_t - R_t`. -/
theorem problem6ClosedDenominator_sub_rightSum_eq {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) (t : Item n) :
    problem6ClosedDenominator alpha v t -
        problem6RightSum alpha v t =
      1 + pairShare alpha v t * problem6PivotGap alpha v t := by
  unfold problem6ClosedDenominator problem6PivotGap
  ring

/--
Gap bounds imply the two denominator inequalities needed for Lemma 5's
closed-form pivot masses to be nonnegative.
-/
theorem problem6ClosedPivotDenominatorBounds_of_pivotGap_bounds {n : ℕ}
    {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hlower : - (pairShare alpha v t)⁻¹ ≤ problem6PivotGap alpha v t)
    (hupper : problem6PivotGap alpha v t ≤
      (1 - pairShare alpha v t)⁻¹) :
    Problem6ClosedPivotDenominatorBounds alpha v t := by
  have hqpos := pairShare_pos t halpha0 halpha1 hpos
  have hcomp_pos := one_sub_pairShare_pos t halpha0 halpha1 hpos
  constructor
  · rw [← sub_nonneg,
      problem6ClosedDenominator_sub_leftSum_eq]
    have hmul :=
      mul_le_mul_of_nonneg_left hupper hcomp_pos.le
    have hcancel :
        (1 - pairShare alpha v t) *
            (1 - pairShare alpha v t)⁻¹ = 1 := by
      exact mul_inv_cancel₀ (ne_of_gt hcomp_pos)
    nlinarith
  · rw [← sub_nonneg,
      problem6ClosedDenominator_sub_rightSum_eq]
    have hmul :=
      mul_le_mul_of_nonneg_left hlower hqpos.le
    have hcancel :
        pairShare alpha v t * (-(pairShare alpha v t)⁻¹) = -1 := by
      rw [mul_neg, mul_inv_cancel₀ (ne_of_gt hqpos)]
    nlinarith

/--
The right denominator inequality is equivalent to the lower crossing bound
used to define the first Lemma 5 pivot.
-/
theorem problem6PivotGap_lower_bound_of_closedPivotDenominatorBounds {n : ℕ}
    {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hbounds : Problem6ClosedPivotDenominatorBounds alpha v t) :
    - (pairShare alpha v t)⁻¹ ≤ problem6PivotGap alpha v t := by
  have hqpos := pairShare_pos t halpha0 halpha1 hpos
  have hslack :
      0 ≤ problem6ClosedDenominator alpha v t -
          problem6RightSum alpha v t := by
    exact sub_nonneg.mpr hbounds.right_le_denominator
  rw [problem6ClosedDenominator_sub_rightSum_eq] at hslack
  have hmul : -1 ≤ pairShare alpha v t * problem6PivotGap alpha v t := by
    nlinarith
  calc
    - (pairShare alpha v t)⁻¹ =
        (pairShare alpha v t)⁻¹ * (-1) := by ring
    _ ≤
        (pairShare alpha v t)⁻¹ *
          (pairShare alpha v t * problem6PivotGap alpha v t) := by
        exact mul_le_mul_of_nonneg_left hmul
          (inv_nonneg.mpr hqpos.le)
    _ = problem6PivotGap alpha v t := by
        field_simp [ne_of_gt hqpos]

/--
The left denominator inequality is equivalent to the upper crossing bound for
the Lemma 5 pivot.
-/
theorem problem6PivotGap_upper_bound_of_closedPivotDenominatorBounds {n : ℕ}
    {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hbounds : Problem6ClosedPivotDenominatorBounds alpha v t) :
    problem6PivotGap alpha v t ≤ (1 - pairShare alpha v t)⁻¹ := by
  have hcomp_pos := one_sub_pairShare_pos t halpha0 halpha1 hpos
  have hslack :
      0 ≤ problem6ClosedDenominator alpha v t -
          problem6LeftSum alpha v t := by
    exact sub_nonneg.mpr hbounds.left_le_denominator
  rw [problem6ClosedDenominator_sub_leftSum_eq] at hslack
  have hmul :
      (1 - pairShare alpha v t) * problem6PivotGap alpha v t ≤ 1 := by
    nlinarith
  calc
    problem6PivotGap alpha v t =
        (1 - pairShare alpha v t)⁻¹ *
          ((1 - pairShare alpha v t) * problem6PivotGap alpha v t) := by
        field_simp [ne_of_gt hcomp_pos]
    _ ≤ (1 - pairShare alpha v t)⁻¹ * 1 := by
        exact mul_le_mul_of_nonneg_left hmul
          (inv_nonneg.mpr hcomp_pos.le)
    _ = (1 - pairShare alpha v t)⁻¹ := by ring

/--
Adjacent-boundary denominator bridge for Lemma 8: if `u` is the item after
`t` and the lower crossing inequality for `t` is tight, then both adjacent
pivots satisfy the Lemma 5 denominator bounds.  This is the local algebraic
form of the paper's continuity stitch between consecutive `A(t)` intervals.
-/
theorem problem6ClosedPivotDenominatorBounds_adjacent_of_boundary
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {t u : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hnext : u.val = t.val + 1)
    (hboundary :
      problem6PivotGap alpha v t = - (pairShare alpha v t)⁻¹) :
    Problem6ClosedPivotDenominatorBounds alpha v t ∧
      Problem6ClosedPivotDenominatorBounds alpha v u := by
  have hqpos_t := pairShare_pos t halpha0 halpha1 hpos
  have hcomp_pos_t := one_sub_pairShare_pos t halpha0 halpha1 hpos
  have hqpos_u := pairShare_pos u halpha0 halpha1 hpos
  have hcomp_pos_u := one_sub_pairShare_pos u halpha0 halpha1 hpos
  have hneg_inv_t_nonpos :
      - (pairShare alpha v t)⁻¹ ≤ 0 :=
    neg_nonpos.mpr (inv_nonneg.mpr hqpos_t.le)
  have hcomp_inv_t_nonneg :
      0 ≤ (1 - pairShare alpha v t)⁻¹ :=
    inv_nonneg.mpr hcomp_pos_t.le
  have hgap_u :
      problem6PivotGap alpha v u =
        (1 - pairShare alpha v u)⁻¹ := by
    rw [problem6PivotGap_next_eq
      (alpha := alpha) (v := v) (t := t) (u := u) hnext,
      hboundary]
    ring
  have hneg_inv_u_nonpos :
      - (pairShare alpha v u)⁻¹ ≤ 0 :=
    neg_nonpos.mpr (inv_nonneg.mpr hqpos_u.le)
  have hcomp_inv_u_nonneg :
      0 ≤ (1 - pairShare alpha v u)⁻¹ :=
    inv_nonneg.mpr hcomp_pos_u.le
  constructor
  · exact
      problem6ClosedPivotDenominatorBounds_of_pivotGap_bounds
        halpha0 halpha1 hpos
        (by rw [hboundary])
        (by rw [hboundary]; linarith)
  · exact
      problem6ClosedPivotDenominatorBounds_of_pivotGap_bounds
        halpha0 halpha1 hpos
        (by rw [hgap_u]; linarith)
        (by rw [hgap_u])

/--
Lemma 5 finite pivot choice: some closed-form pivot satisfies the denominator
bounds, without appealing to an external LP existence theorem.
-/
theorem problem6ClosedPivotDenominatorBounds_exists {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j) :
    ∃ t : Item n, Problem6ClosedPivotDenominatorBounds alpha v t := by
  classical
  have hnpos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  let last : Item n := ⟨n - 1, by omega⟩
  have hlast_lower :
      - (pairShare alpha v last)⁻¹ ≤ problem6PivotGap alpha v last := by
    have hRzero : problem6RightSum alpha v last = 0 := by
      unfold problem6RightSum
      refine Finset.sum_eq_zero ?_
      intro j _hj
      have hnlt : ¬ last.val < j.val := by
        change ¬ n - 1 < j.val
        omega
      simp [hnlt]
    have hLnonneg :
        0 ≤ problem6LeftSum alpha v last :=
      problem6LeftSum_nonneg last halpha0 halpha1 hpos
    have hqinv_nonneg :
        0 ≤ (pairShare alpha v last)⁻¹ :=
      inv_nonneg.mpr (pairShare_pos last halpha0 halpha1 hpos).le
    unfold problem6PivotGap
    rw [hRzero]
    nlinarith
  let crossingSet : Finset (Item n) :=
    Finset.univ.filter
      (fun t : Item n =>
        - (pairShare alpha v t)⁻¹ ≤ problem6PivotGap alpha v t)
  have hlast_mem : last ∈ crossingSet := by
    simp [crossingSet, hlast_lower]
  obtain ⟨t, htmem, hmin⟩ :=
    Finset.exists_min_image crossingSet (fun t : Item n => t.val)
      ⟨last, hlast_mem⟩
  have hlower :
      - (pairShare alpha v t)⁻¹ ≤ problem6PivotGap alpha v t := by
    have htmem_filter :
        t ∈ Finset.univ.filter
          (fun t : Item n =>
            - (pairShare alpha v t)⁻¹ ≤
              problem6PivotGap alpha v t) := by
      simpa [crossingSet] using htmem
    exact (Finset.mem_filter.mp htmem_filter).2
  have hupper :
      problem6PivotGap alpha v t ≤
        (1 - pairShare alpha v t)⁻¹ := by
    by_cases ht0 : t.val = 0
    · have hLzero : problem6LeftSum alpha v t = 0 := by
        unfold problem6LeftSum
        refine Finset.sum_eq_zero ?_
        intro j _hj
        have hnlt : ¬ j.val < t.val := by omega
        simp [hnlt]
      have hRnonneg :
          0 ≤ problem6RightSum alpha v t :=
        problem6RightSum_nonneg t halpha0 halpha1 hpos
      have hcomp_inv_nonneg :
          0 ≤ (1 - pairShare alpha v t)⁻¹ :=
        inv_nonneg.mpr
          (one_sub_pairShare_pos t halpha0 halpha1 hpos).le
      unfold problem6PivotGap
      rw [hLzero]
      nlinarith
    · have htpos : 0 < t.val := Nat.pos_of_ne_zero ht0
      let p : Item n := ⟨t.val - 1, by omega⟩
      have hpnext : t.val = p.val + 1 := by
        dsimp [p]
        omega
      have hp_not :
          ¬ (- (pairShare alpha v p)⁻¹ ≤
              problem6PivotGap alpha v p) := by
        intro hp
        have hp_mem : p ∈ crossingSet := by
          simp [crossingSet, hp]
        have hminp := hmin p hp_mem
        dsimp [p] at hminp
        omega
      have hp_lt :
          problem6PivotGap alpha v p <
            - (pairShare alpha v p)⁻¹ :=
        not_le.mp hp_not
      have hgap_eq :=
        problem6PivotGap_next_eq
          (alpha := alpha) (v := v) (t := p) (u := t) hpnext
      have hupper_lt :
          problem6PivotGap alpha v t <
            (1 - pairShare alpha v t)⁻¹ := by
        rw [hgap_eq]
        nlinarith
      exact le_of_lt hupper_lt
  exact ⟨t,
    problem6ClosedPivotDenominatorBounds_of_pivotGap_bounds
      halpha0 halpha1 hpos hlower hupper⟩

/--
Appendix D, Lemma 10 exact-center feasibility certificate: the closed-form
Lemma 5 midpoint construction has nonnegative pivot masses.
-/
theorem problem6ClosedPivotDenominatorBounds_half_center {n : ℕ}
    {v : Item n → ℝ} {t : Item n}
    (hpos : ∀ j : Item n, 0 < v j)
    (hcenter : t.val = (reverseItem t).val) :
    Problem6ClosedPivotDenominatorBounds (1 / 2) v t := by
  have hsum :=
    problem6LeftSum_half_eq_rightSum_half_of_pivot_eq_reverse
      (v := v) (t := t) hpos hcenter
  have hden :=
    problem6ClosedDenominator_half_center_eq_one_add_leftSum
      (v := v) (t := t) hpos hcenter
  have hleft_nonneg :
      0 ≤ problem6LeftSum (1 / 2) v t :=
    problem6LeftSum_nonneg t (by norm_num) (by norm_num) hpos
  constructor
  · rw [hden]
    linarith
  · rw [← hsum, hden]
    linarith

/--
Appendix D, Lemma 10 even-center feasibility certificate: the midpoint
candidate immediately before its mirror has nonnegative closed-form pivot masses.
-/
theorem problem6ClosedPivotDenominatorBounds_half_succ_center {n : ℕ}
    {v : Item n → ℝ} {t : Item n}
    (hpos : ∀ j : Item n, 0 < v j)
    (hsucc : t.val + 1 = (reverseItem t).val) :
    Problem6ClosedPivotDenominatorBounds (1 / 2) v t := by
  have hright :=
    problem6RightSum_half_eq_leftSum_half_add_inv_pairShare_of_pivot_succ_reverse
      (v := v) (t := t) hpos hsucc
  have hden :=
    problem6ClosedDenominator_half_succ_center_eq_rightSum
      (v := v) (t := t) hpos hsucc
  have hq_nonneg :
      0 ≤ (pairShare (1 / 2) v t)⁻¹ :=
    inv_nonneg.mpr
      (pairShare_pos t (by norm_num : (0 : ℝ) < 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1) hpos).le
  constructor
  · rw [hden, hright]
    exact le_add_of_nonneg_right hq_nonneg
  · rw [hden]

/-- Denominator bounds imply nonnegative pivot coordinates. -/
theorem problem6ClosedNonnegativePivots_of_denominatorBounds {n : ℕ}
    {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hbounds : Problem6ClosedPivotDenominatorBounds alpha v t) :
    Problem6ClosedNonnegativePivots alpha v t := by
  have hDpos := problem6ClosedDenominator_pos t halpha0 halpha1 hpos
  constructor
  · rw [problem6ClosedX_at]
    rw [sub_nonneg]
    unfold problem6ClosedValue
    have hdiv :
        problem6LeftSum alpha v t /
            problem6ClosedDenominator alpha v t ≤ 1 := by
      rw [div_le_iff₀ hDpos]
      simpa using hbounds.left_le_denominator
    have heq :
        1 / problem6ClosedDenominator alpha v t *
            problem6LeftSum alpha v t =
          problem6LeftSum alpha v t /
            problem6ClosedDenominator alpha v t := by
      ring
    rw [heq]
    exact hdiv
  · rw [problem6ClosedY_at]
    rw [sub_nonneg]
    unfold problem6ClosedValue
    have hdiv :
        problem6RightSum alpha v t /
            problem6ClosedDenominator alpha v t ≤ 1 := by
      rw [div_le_iff₀ hDpos]
      simpa using hbounds.right_le_denominator
    have heq :
        1 / problem6ClosedDenominator alpha v t *
            problem6RightSum alpha v t =
          problem6RightSum alpha v t /
            problem6ClosedDenominator alpha v t := by
      ring
    rw [heq]
    exact hdiv

/-- Nonnegative closed-form pivot coordinates imply the denominator bounds. -/
theorem problem6ClosedPivotDenominatorBounds_of_nonnegativePivots {n : ℕ}
    {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hpivot : Problem6ClosedNonnegativePivots alpha v t) :
    Problem6ClosedPivotDenominatorBounds alpha v t := by
  have hDpos := problem6ClosedDenominator_pos t halpha0 halpha1 hpos
  constructor
  · have hx := hpivot.x_pivot_nonneg
    rw [problem6ClosedX_at] at hx
    unfold problem6ClosedValue at hx
    have hmul :
        1 / problem6ClosedDenominator alpha v t *
            problem6LeftSum alpha v t ≤ 1 := by
      linarith
    have hdiv :
        problem6LeftSum alpha v t /
            problem6ClosedDenominator alpha v t ≤ 1 := by
      calc
        problem6LeftSum alpha v t /
            problem6ClosedDenominator alpha v t =
              (problem6ClosedDenominator alpha v t)⁻¹ *
                problem6LeftSum alpha v t := by
                ring
        _ ≤ 1 := by simpa [one_div] using hmul
    rw [div_le_iff₀ hDpos] at hdiv
    simpa using hdiv
  · have hy := hpivot.y_pivot_nonneg
    rw [problem6ClosedY_at] at hy
    unfold problem6ClosedValue at hy
    have hmul :
        1 / problem6ClosedDenominator alpha v t *
            problem6RightSum alpha v t ≤ 1 := by
      linarith
    have hdiv :
        problem6RightSum alpha v t /
            problem6ClosedDenominator alpha v t ≤ 1 := by
      calc
        problem6RightSum alpha v t /
            problem6ClosedDenominator alpha v t =
              (problem6ClosedDenominator alpha v t)⁻¹ *
                problem6RightSum alpha v t := by
                ring
        _ ≤ 1 := by simpa [one_div] using hmul
    rw [div_le_iff₀ hDpos] at hdiv
    simpa using hdiv

/-- Under pivot nonnegativity, all closed-form `x_j` coordinates are nonnegative. -/
theorem problem6ClosedX_nonneg {n : ℕ}
    {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hpivot : Problem6ClosedNonnegativePivots alpha v t)
    (j : Item n) :
    0 ≤ problem6ClosedX alpha v t j := by
  by_cases hlt : j.val < t.val
  · rw [problem6ClosedX_before alpha v hlt]
    exact div_nonneg
      (problem6ClosedValue_pos t halpha0 halpha1 hpos).le
      (pairShare_pos j halpha0 halpha1 hpos).le
  · by_cases heq : j = t
    · subst j
      exact hpivot.x_pivot_nonneg
    · have hgt : t.val < j.val := by
        have hne_val : j.val ≠ t.val := by
          intro hval
          exact heq (Fin.ext hval)
        omega
      rw [problem6ClosedX_after alpha v hgt]

/-- Under pivot nonnegativity, all closed-form `y_j` coordinates are nonnegative. -/
theorem problem6ClosedY_nonneg {n : ℕ}
    {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hpivot : Problem6ClosedNonnegativePivots alpha v t)
    (j : Item n) :
    0 ≤ problem6ClosedY alpha v t j := by
  by_cases hlt : j.val < t.val
  · rw [problem6ClosedY_before alpha v hlt]
  · by_cases heq : j = t
    · subst j
      exact hpivot.y_pivot_nonneg
    · have hgt : t.val < j.val := by
        have hne_val : j.val ≠ t.val := by
          intro hval
          exact heq (Fin.ext hval)
        omega
      rw [problem6ClosedY_after alpha v hgt]
      exact div_nonneg
        (problem6ClosedValue_pos t halpha0 halpha1 hpos).le
        (one_sub_pairShare_pos j halpha0 halpha1 hpos).le

/--
Appendix D, Lemma 4 comparison specialized to Lemma 5's closed form:
a closed-form pivot to the right of a nonnegative closed-form candidate cannot
have a larger `I^*_min` value.
-/
theorem problem6ClosedValue_le_of_closed_candidate_before_general {n : ℕ}
    {alpha : ℝ} {v : Item n → ℝ} {c t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hct : c.val < t.val)
    (hpivot : Problem6ClosedNonnegativePivots alpha v t)
    (hcandidate : Problem6ClosedNonnegativePivots alpha v c) :
    problem6ClosedValue alpha v t ≤
      problem6ClosedValue alpha v c := by
  exact problem6SparseEqualized_value_le_of_candidate_before_general
    halpha0 halpha1
    hpos hct
    (problem6Closed_sparseEqualized t halpha0 halpha1 hpos)
    (problem6Closed_sparseEqualized c halpha0 halpha1 hpos)
    (fun j =>
      problem6ClosedX_nonneg
        halpha0 halpha1 hpos hpivot j)
    (problem6ClosedY_nonneg
      halpha0 halpha1 hpos hcandidate c)

/--
Appendix D, Lemma 10 comparison specialized to Lemma 5's closed form at the
midpoint.
-/
theorem problem6ClosedValue_le_of_closed_candidate_before {n : ℕ}
    {v : Item n → ℝ} {c t : Item n}
    (hpos : ∀ j : Item n, 0 < v j)
    (hct : c.val < t.val)
    (hpivot : Problem6ClosedNonnegativePivots (1 / 2) v t)
    (hcandidate : Problem6ClosedNonnegativePivots (1 / 2) v c) :
    problem6ClosedValue (1 / 2) v t ≤
      problem6ClosedValue (1 / 2) v c := by
  exact problem6ClosedValue_le_of_closed_candidate_before_general
      (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)
      hpos hct hpivot hcandidate

/--
Appendix D, Lemma 10 exact-center candidate comparison: any nonnegative
closed-form pivot strictly after an exact center candidate has value no larger
than that candidate.
-/
theorem problem6ClosedValue_le_of_center_candidate_before {n : ℕ}
    {v : Item n → ℝ} {c t : Item n}
    (hpos : ∀ j : Item n, 0 < v j)
    (hcenter : c.val = (reverseItem c).val)
    (hct : c.val < t.val)
    (hpivot : Problem6ClosedNonnegativePivots (1 / 2) v t) :
    problem6ClosedValue (1 / 2) v t ≤
      problem6ClosedValue (1 / 2) v c := by
  exact problem6ClosedValue_le_of_closed_candidate_before
    hpos hct hpivot
    (problem6ClosedNonnegativePivots_of_denominatorBounds
      (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) hpos
      (problem6ClosedPivotDenominatorBounds_half_center
        (v := v) (t := c) hpos hcenter))

/--
Appendix D, Lemma 10 even-center candidate comparison: any nonnegative
closed-form pivot strictly after the candidate immediately before its mirror has
value no larger than that candidate.
-/
theorem problem6ClosedValue_le_of_succ_center_candidate_before {n : ℕ}
    {v : Item n → ℝ} {c t : Item n}
    (hpos : ∀ j : Item n, 0 < v j)
    (hsucc : c.val + 1 = (reverseItem c).val)
    (hct : c.val < t.val)
    (hpivot : Problem6ClosedNonnegativePivots (1 / 2) v t) :
    problem6ClosedValue (1 / 2) v t ≤
      problem6ClosedValue (1 / 2) v c := by
  exact problem6ClosedValue_le_of_closed_candidate_before
    hpos hct hpivot
    (problem6ClosedNonnegativePivots_of_denominatorBounds
      (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) hpos
      (problem6ClosedPivotDenominatorBounds_half_succ_center
        (v := v) (t := c) hpos hsucc))

/--
Appendix D, Lemma 6 pivot-gap side condition for an exact midpoint candidate:
the pivot and its mirror are the same coordinate, so the closed-form gap is zero.
-/
theorem problem6ClosedX_sub_closedY_reverse_half_center_eq_zero {n : ℕ}
    {v : Item n → ℝ} {t : Item n}
    (hpos : ∀ j : Item n, 0 < v j)
    (hcenter : t.val = (reverseItem t).val) :
    problem6ClosedX (1 / 2) v t t -
      problem6ClosedY (1 / 2) v t (reverseItem t) = 0 := by
  have hrev : reverseItem t = t := Fin.ext hcenter.symm
  have hsum :=
    problem6LeftSum_half_eq_rightSum_half_of_pivot_eq_reverse
      (v := v) (t := t) hpos hcenter
  rw [hrev, problem6ClosedX_at, problem6ClosedY_at]
  rw [← hsum]
  ring

/--
Appendix D, Lemma 6 pivot-gap side condition for an exact midpoint candidate,
as a nonnegativity fact.
-/
theorem problem6ClosedX_sub_closedY_reverse_half_center_nonneg {n : ℕ}
    {v : Item n → ℝ} {t : Item n}
    (hpos : ∀ j : Item n, 0 < v j)
    (hcenter : t.val = (reverseItem t).val) :
    0 ≤ problem6ClosedX (1 / 2) v t t -
      problem6ClosedY (1 / 2) v t (reverseItem t) := by
  rw [problem6ClosedX_sub_closedY_reverse_half_center_eq_zero hpos hcenter]

/--
Appendix D, Lemma 6 pivot-gap side condition for the even midpoint candidate:
the pivot `x` mass equals the mirrored `y` mass.
-/
theorem problem6ClosedX_sub_closedY_reverse_half_succ_center_eq_zero {n : ℕ}
    {v : Item n → ℝ} {t : Item n}
    (hpos : ∀ j : Item n, 0 < v j)
    (hsucc : t.val + 1 = (reverseItem t).val) :
    problem6ClosedX (1 / 2) v t t -
      problem6ClosedY (1 / 2) v t (reverseItem t) = 0 := by
  have hright :=
    problem6RightSum_half_eq_leftSum_half_add_inv_pairShare_of_pivot_succ_reverse
      (v := v) (t := t) hpos hsucc
  have hden_right :=
    problem6ClosedDenominator_half_succ_center_eq_rightSum
      (v := v) (t := t) hpos hsucc
  let q : ℝ := pairShare (1 / 2) v t
  let L : ℝ := problem6LeftSum (1 / 2) v t
  let D : ℝ := problem6ClosedDenominator (1 / 2) v t
  have hD_eq : D = L + q⁻¹ := by
    dsimp [D, L, q]
    rw [hden_right, hright]
  have hqpos : 0 < q := by
    simpa [q] using
      pairShare_pos t (by norm_num : (0 : ℝ) < 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1) hpos
  have hqne : q ≠ 0 := ne_of_gt hqpos
  have hDpos : 0 < D := by
    simpa [D] using
      problem6ClosedDenominator_pos t
        (by norm_num : (0 : ℝ) < 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1) hpos
  have hDne : D ≠ 0 := ne_of_gt hDpos
  have hmirror_gt : t.val < (reverseItem t).val := by
    omega
  have hshare := pairShare_half_eq_one_sub_reverse t hpos
  rw [problem6ClosedX_at, problem6ClosedY_after (1 / 2) v hmirror_gt]
  unfold problem6ClosedValue
  rw [← hshare]
  change 1 - 1 / D * L - (1 / D / q) = 0
  have hmul : 1 / D * (L + q⁻¹) = 1 := by
    rw [← hD_eq]
    field_simp [hDne]
  have hdiv_eq : 1 / D / q = 1 / D * q⁻¹ := by
    ring
  rw [hdiv_eq]
  nlinarith

/--
Appendix D, Lemma 6 pivot-gap side condition for the even midpoint candidate,
as a nonnegativity fact.
-/
theorem problem6ClosedX_sub_closedY_reverse_half_succ_center_nonneg {n : ℕ}
    {v : Item n → ℝ} {t : Item n}
    (hpos : ∀ j : Item n, 0 < v j)
    (hsucc : t.val + 1 = (reverseItem t).val) :
    0 ≤ problem6ClosedX (1 / 2) v t t -
      problem6ClosedY (1 / 2) v t (reverseItem t) := by
  rw [problem6ClosedX_sub_closedY_reverse_half_succ_center_eq_zero hpos hsucc]

/-- Build a finite PMF from a nonnegative real vector with total mass one. -/
noncomputable def pmfOfRealVector {n : ℕ}
    (x : Item n → ℝ)
    (hnonneg : ∀ j : Item n, 0 ≤ x j)
    (hsum : (∑ j : Item n, x j) = 1) : PMF (Item n) :=
  PMF.ofFintype (fun j : Item n => ENNReal.ofReal (x j)) (by
    calc
      (∑ j : Item n, ENNReal.ofReal (x j))
          = ENNReal.ofReal (∑ j : Item n, x j) := by
            rw [← ENNReal.ofReal_sum_of_nonneg
              (s := Finset.univ) (f := x)]
            simp [hnonneg]
      _ = 1 := by
            simp [hsum])

@[simp] theorem pmfOfRealVector_apply_toReal {n : ℕ}
    (x : Item n → ℝ)
    (hnonneg : ∀ j : Item n, 0 ≤ x j)
    (hsum : (∑ j : Item n, x j) = 1)
    (j : Item n) :
    ((pmfOfRealVector x hnonneg hsum) j).toReal = x j := by
  unfold pmfOfRealVector
  rw [PMF.ofFintype_apply]
  exact ENNReal.toReal_ofReal (hnonneg j)

/-- Finite PMFs are extensional through their real coordinate values. -/
theorem pmf_eq_of_forall_toReal_eq {n : ℕ}
    {μ ν : PMF (Item n)}
    (h : ∀ j : Item n, (μ j).toReal = (ν j).toReal) :
    μ = ν := by
  apply PMF.ext
  intro j
  exact (ENNReal.toReal_eq_toReal_iff'
    (μ.apply_ne_top j) (ν.apply_ne_top j)).mp (h j)

/-- A finite PMF coordinate with zero real value is zero as an `ENNReal`. -/
theorem pmf_apply_eq_zero_of_toReal_eq_zero {n : ℕ}
    {μ : PMF (Item n)} {j : Item n}
    (h : (μ j).toReal = 0) :
    μ j = 0 := by
  rcases (ENNReal.toReal_eq_zero_iff (μ j)).mp h with hzero | htop
  · exact hzero
  · exact False.elim ((μ.apply_ne_top j) htop)

/-- Problem 6's real-vector epigraph feasibility in the paper's variables. -/
structure Problem6RealLPFeasible {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ)
    (x y : Item n → ℝ) (ell : ℝ) : Prop where
  x_nonneg : ∀ j : Item n, 0 ≤ x j
  y_nonneg : ∀ j : Item n, 0 ≤ y j
  sum_x : (∑ j : Item n, x j) = 1
  sum_y : (∑ j : Item n, y j) = 1
  item_le :
    ∀ j : Item n,
      ell ≤ pairShare alpha v j * x j + (1 - pairShare alpha v j) * y j

/-- Rebuild a two-type policy from feasible real `x` and `y` rows. -/
noncomputable def problem6PolicyOfRealVectors {n : ℕ}
    (x y : Item n → ℝ)
    (hx : ∀ j : Item n, 0 ≤ x j)
    (hy : ∀ j : Item n, 0 ≤ y j)
    (hsx : (∑ j : Item n, x j) = 1)
    (hsy : (∑ j : Item n, y j) = 1) :
    TypePolicy 2 n :=
  fun k =>
    if k = 0 then
      pmfOfRealVector x hx hsx
    else
      pmfOfRealVector y hy hsy

@[simp] theorem problem6PolicyOfRealVectors_zero_toReal {n : ℕ}
    (x y : Item n → ℝ)
    (hx : ∀ j : Item n, 0 ≤ x j)
    (hy : ∀ j : Item n, 0 ≤ y j)
    (hsx : (∑ j : Item n, x j) = 1)
    (hsy : (∑ j : Item n, y j) = 1)
    (j : Item n) :
    ((problem6PolicyOfRealVectors x y hx hy hsx hsy 0) j).toReal = x j := by
  simp [problem6PolicyOfRealVectors]

@[simp] theorem problem6PolicyOfRealVectors_one_toReal {n : ℕ}
    (x y : Item n → ℝ)
    (hx : ∀ j : Item n, 0 ≤ x j)
    (hy : ∀ j : Item n, 0 ≤ y j)
    (hsx : (∑ j : Item n, x j) = 1)
    (hsy : (∑ j : Item n, y j) = 1)
    (j : Item n) :
    ((problem6PolicyOfRealVectors x y hx hy hsx hsy 1) j).toReal = y j := by
  simp [problem6PolicyOfRealVectors]

/-- A policy satisfying the epigraph constraints gives a feasible real-vector LP point. -/
theorem problem6RealLPFeasible_of_policy {n : ℕ}
    {alpha : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 2 n} {ell : ℝ}
    (hfeas : problem6LPFeasible alpha v ρ ell) :
    Problem6RealLPFeasible alpha v
      (fun j : Item n => (ρ 0 j).toReal)
      (fun j : Item n => (ρ 1 j).toReal) ell := by
  exact
    { x_nonneg := fun j => ENNReal.toReal_nonneg
      y_nonneg := fun j => ENNReal.toReal_nonneg
      sum_x := problem6_typeZero_sum_eq_one ρ
      sum_y := problem6_typeOne_sum_eq_one ρ
      item_le := hfeas }

/-- A nonzero PMF coordinate has strictly positive real value. -/
theorem typePolicy_toReal_pos_of_ne_zero {K n : ℕ}
    (ρ : TypePolicy K n) {k : UserType K} {j : Item n}
    (h : ρ k j ≠ 0) :
    0 < (ρ k j).toReal := by
  have htoReal_ne : (ρ k j).toReal ≠ 0 := by
    intro hzero
    have hzero_or_top :=
      (ENNReal.toReal_eq_zero_iff (ρ k j)).mp hzero
    rcases hzero_or_top with hzero_enn | htop
    · exact h hzero_enn
    · exact (ρ k).apply_ne_top j htop
  exact lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm htoReal_ne)

/--
Problem 6 local optimality condition used in Appendix D, Lemma 4:
there is no other two-type policy that strictly improves every item value.
-/
def Problem6PolicyNoStrictPointwiseImprovement {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) (ρ : TypePolicy 2 n) : Prop :=
  ¬ ∃ ρ' : TypePolicy 2 n,
    ∀ j : Item n,
      pairShare alpha v j * (ρ 0 j).toReal +
        (1 - pairShare alpha v j) * (ρ 1 j).toReal <
      pairShare alpha v j * (ρ' 0 j).toReal +
        (1 - pairShare alpha v j) * (ρ' 1 j).toReal

/-- A policy/value pair is optimal for the Problem 6 epigraph LP. -/
def Problem6PolicyOptimal {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) (ρ : TypePolicy 2 n) (ell : ℝ) : Prop :=
  problem6LPFeasible alpha v ρ ell ∧
    ∀ (ρ' : TypePolicy 2 n) (ell' : ℝ),
      problem6LPFeasible alpha v ρ' ell' → ell' ≤ ell

/--
Finite dual certificate for upper-bounding type `1` raw utility over the
Problem 6 feasible face at item value `ell`.

The fields are the two row-sum dual variables and nonnegative item-constraint
dual weights. The coefficient inequalities are exactly the finite weak-duality
conditions for the LP that maximizes type-`1` utility subject to the Problem 6
item lower bounds and row-simplex constraints.
-/
structure Problem6TypeOneRawUtilityDualCertificate {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) (ell upper rowZero rowOne : ℝ)
    (itemWeight : Item n → ℝ) : Prop where
  itemWeight_nonneg : ∀ j : Item n, 0 ≤ itemWeight j
  typeZero_coeff_nonneg :
    ∀ j : Item n, 0 ≤ rowZero - itemWeight j * pairShare alpha v j
  typeOne_coeff_upper :
    ∀ j : Item n,
      v (reverseItem j) ≤
        rowOne - itemWeight j * (1 - pairShare alpha v j)
  objective_bound :
    rowZero + rowOne - ell * (∑ j : Item n, itemWeight j) ≤ upper

/--
Problem 6 finite weak duality for the auxiliary LP that maximizes type `1`
raw utility over policies satisfying item lower bound `ell`.
-/
theorem problem6_typeOneRawUtility_le_of_dualCertificate {n : ℕ}
    {alpha : ℝ} {v : Item n → ℝ} {ell upper rowZero rowOne : ℝ}
    {itemWeight : Item n → ℝ}
    (ρ : TypePolicy 2 n)
    (hfeas : problem6LPFeasible alpha v ρ ell)
    (cert :
      Problem6TypeOneRawUtilityDualCertificate
        alpha v ell upper rowZero rowOne itemWeight) :
    TypeWeightedRecommendationModel.rawTypeUtility
        (twoTypeReducedModel alpha v) ρ 1 ≤ upper := by
  let x : Item n → ℝ := fun j => (ρ 0 j).toReal
  let y : Item n → ℝ := fun j => (ρ 1 j).toReal
  let q : Item n → ℝ := fun j => pairShare alpha v j
  let β : Item n → ℝ := itemWeight
  have hy_nonneg : ∀ j : Item n, 0 ≤ y j := by
    intro j
    exact ENNReal.toReal_nonneg
  have hx_nonneg : ∀ j : Item n, 0 ≤ x j := by
    intro j
    exact ENNReal.toReal_nonneg
  have hy_bound :
      (∑ j : Item n, v (reverseItem j) * y j) ≤
        ∑ j : Item n, (rowOne - β j * (1 - q j)) * y j := by
    refine Finset.sum_le_sum ?_
    intro j _hj
    exact mul_le_mul_of_nonneg_right
      (by simpa [q, β] using cert.typeOne_coeff_upper j)
      (hy_nonneg j)
  have hy_sum :
      (∑ j : Item n, (rowOne - β j * (1 - q j)) * y j) =
        rowOne - ∑ j : Item n, β j * (1 - q j) * y j := by
    calc
      (∑ j : Item n, (rowOne - β j * (1 - q j)) * y j)
          = (∑ j : Item n, rowOne * y j) -
              ∑ j : Item n, β j * (1 - q j) * y j := by
              rw [← Finset.sum_sub_distrib]
              refine Finset.sum_congr rfl ?_
              intro j _hj
              ring
      _ = rowOne - ∑ j : Item n, β j * (1 - q j) * y j := by
              rw [← Finset.mul_sum]
              have hsumy : (∑ j : Item n, y j) = 1 := by
                dsimp [y]
                exact problem6_typeOne_sum_eq_one ρ
              rw [hsumy]
              ring
  have hconstraint :
      ell * (∑ j : Item n, β j) ≤
        (∑ j : Item n, β j * q j * x j) +
          ∑ j : Item n, β j * (1 - q j) * y j := by
    calc
      ell * (∑ j : Item n, β j)
          = ∑ j : Item n, β j * ell := by
              rw [mul_comm ell]
              rw [Finset.sum_mul]
      _ ≤ ∑ j : Item n, β j * (q j * x j + (1 - q j) * y j) := by
              refine Finset.sum_le_sum ?_
              intro j _hj
              exact mul_le_mul_of_nonneg_left
                (by simpa [q, x, y] using hfeas j)
                (by simpa [β] using cert.itemWeight_nonneg j)
      _ =
        (∑ j : Item n, β j * q j * x j) +
          ∑ j : Item n, β j * (1 - q j) * y j := by
              rw [← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl ?_
              intro j _hj
              ring
  have hx_bound :
      (∑ j : Item n, β j * q j * x j) ≤ rowZero := by
    calc
      (∑ j : Item n, β j * q j * x j)
          ≤ ∑ j : Item n, rowZero * x j := by
              refine Finset.sum_le_sum ?_
              intro j _hj
              have hcoeff : β j * q j ≤ rowZero := by
                have h := cert.typeZero_coeff_nonneg j
                linarith
              exact mul_le_mul_of_nonneg_right hcoeff (hx_nonneg j)
      _ = rowZero := by
              rw [← Finset.mul_sum]
              have hsumx : (∑ j : Item n, x j) = 1 := by
                dsimp [x]
                exact problem6_typeZero_sum_eq_one ρ
              rw [hsumx]
              ring
  have hraw_eq :
      TypeWeightedRecommendationModel.rawTypeUtility
          (twoTypeReducedModel alpha v) ρ 1 =
        ∑ j : Item n, v (reverseItem j) * y j := by
    unfold TypeWeightedRecommendationModel.rawTypeUtility
      AppliedModelingLib.Policy.agentScore AppliedModelingLib.pmfExp
    refine Finset.sum_congr rfl ?_
    intro j _hj
    simp [twoTypeReducedModel, y, mul_comm]
  calc
    TypeWeightedRecommendationModel.rawTypeUtility
        (twoTypeReducedModel alpha v) ρ 1
        = ∑ j : Item n, v (reverseItem j) * y j := hraw_eq
    _ ≤ ∑ j : Item n, (rowOne - β j * (1 - q j)) * y j := hy_bound
    _ = rowOne - ∑ j : Item n, β j * (1 - q j) * y j := hy_sum
    _ ≤ rowOne +
        ((∑ j : Item n, β j * q j * x j) -
          ell * (∑ j : Item n, β j)) := by
          linarith
    _ ≤ rowOne + (rowZero -
          ell * (∑ j : Item n, β j)) := by
          linarith
    _ = rowZero + rowOne -
          ell * (∑ j : Item n, β j) := by ring
    _ ≤ upper := cert.objective_bound

/-- The type-`1` utility dual uses the common opposing-model best-item value. -/
noncomputable def problem6TypeOneDualRowOne {n : ℕ} [NeZero n]
    (alpha : ℝ) (v : Item n → ℝ) : ℝ :=
  TypeWeightedRecommendationModel.bestItemUtility
    (twoTypeReducedModel alpha v) 1

/--
The type-`0` row-sum dual variable for the Lemma 5 pivot in the auxiliary
type-`1` utility maximization LP.
-/
noncomputable def problem6TypeOneDualRowZero {n : ℕ} [NeZero n]
    (alpha : ℝ) (v : Item n → ℝ) (t : Item n) : ℝ :=
  pairShare alpha v t *
    (problem6TypeOneDualRowOne alpha v - v (reverseItem t)) /
      (1 - pairShare alpha v t)

/--
Item-constraint dual weights for the auxiliary type-`1` utility LP. At and
before the pivot the `x`-coefficient is tight; after the pivot the
`y`-coefficient is tight.
-/
noncomputable def problem6TypeOneDualWeight {n : ℕ} [NeZero n]
    (alpha : ℝ) (v : Item n → ℝ) (t j : Item n) : ℝ :=
  if j.val ≤ t.val then
    problem6TypeOneDualRowZero alpha v t / pairShare alpha v j
  else
    (problem6TypeOneDualRowOne alpha v - v (reverseItem j)) /
      (1 - pairShare alpha v j)

theorem problem6TypeOneDualRowOne_ge_reverse {n : ℕ} [NeZero n]
    (alpha : ℝ) (v : Item n → ℝ) (j : Item n) :
    v (reverseItem j) ≤ problem6TypeOneDualRowOne alpha v := by
  unfold problem6TypeOneDualRowOne
  unfold TypeWeightedRecommendationModel.bestItemUtility
  change v (reverseItem j) ≤
    AppliedModelingLib.finiteMax (fun l : Item n => v (reverseItem l))
  exact AppliedModelingLib.le_finiteMax (fun l : Item n => v (reverseItem l)) j

theorem problem6TypeOneDualRowOne_sub_reverse_nonneg {n : ℕ} [NeZero n]
    (alpha : ℝ) (v : Item n → ℝ) (j : Item n) :
    0 ≤ problem6TypeOneDualRowOne alpha v - v (reverseItem j) := by
  have h := problem6TypeOneDualRowOne_ge_reverse alpha v j
  linarith

theorem problem6TypeOneDualRowZero_nonneg {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j) :
    0 ≤ problem6TypeOneDualRowZero alpha v t := by
  unfold problem6TypeOneDualRowZero
  exact div_nonneg
    (mul_nonneg (pairShare_pos t halpha0 halpha1 hpos).le
      (problem6TypeOneDualRowOne_sub_reverse_nonneg alpha v t))
    (one_sub_pairShare_pos t halpha0 halpha1 hpos).le

theorem problem6_pairShare_le_of_val_le {n : ℕ}
    {alpha : ℝ} {v : Item n → ℝ} {i j : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hij : i.val ≤ j.val) :
    pairShare alpha v j ≤ pairShare alpha v i := by
  rcases lt_or_eq_of_le hij with hlt | heq
  · exact (pairShare_strictAnti_index
      halpha0 halpha1 hpos hdec hlt).le
  · have hji : j = i := Fin.ext heq.symm
    subst j
    rfl

theorem problem6TypeOneDualWeight_nonneg {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j) :
    ∀ j : Item n, 0 ≤ problem6TypeOneDualWeight alpha v t j := by
  intro j
  unfold problem6TypeOneDualWeight
  by_cases hjt : j.val ≤ t.val
  · rw [if_pos hjt]
    exact div_nonneg
      (problem6TypeOneDualRowZero_nonneg halpha0 halpha1 hpos)
      (pairShare_pos j halpha0 halpha1 hpos).le
  · rw [if_neg hjt]
    exact div_nonneg
      (problem6TypeOneDualRowOne_sub_reverse_nonneg alpha v j)
      (one_sub_pairShare_pos j halpha0 halpha1 hpos).le

theorem problem6TypeOneDual_typeZero_coeff_nonneg {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v) :
    ∀ j : Item n,
      0 ≤ problem6TypeOneDualRowZero alpha v t -
        problem6TypeOneDualWeight alpha v t j * pairShare alpha v j := by
  intro j
  unfold problem6TypeOneDualWeight
  by_cases hjt : j.val ≤ t.val
  · rw [if_pos hjt]
    have hq_ne : pairShare alpha v j ≠ 0 :=
      ne_of_gt (pairShare_pos j halpha0 halpha1 hpos)
    field_simp [hq_ne]
    ring_nf
    norm_num
  · rw [if_neg hjt]
    have htj : t.val < j.val := lt_of_not_ge hjt
    have hq_le :
        pairShare alpha v j ≤ pairShare alpha v t :=
      problem6_pairShare_le_of_val_le
        halpha0 halpha1 hpos hdec htj.le
    have hratio :
        pairShare alpha v j / (1 - pairShare alpha v j) ≤
          pairShare alpha v t / (1 - pairShare alpha v t) :=
      ratio_self_one_sub_mono_of_le
        (pairShare_pos j halpha0 halpha1 hpos)
        (pairShare_lt_one j halpha0 halpha1 hpos)
        (pairShare_pos t halpha0 halpha1 hpos)
        (pairShare_lt_one t halpha0 halpha1 hpos)
        hq_le
    have hBjt :
        problem6TypeOneDualRowOne alpha v - v (reverseItem j) ≤
          problem6TypeOneDualRowOne alpha v - v (reverseItem t) := by
      have hrev : (reverseItem j).val ≤ (reverseItem t).val :=
        (reverseItem_val_lt_of_val_lt htj).le
      have hv : v (reverseItem t) ≤ v (reverseItem j) :=
        value_antitone_of_val_le hdec hrev
      linarith
    have hBjt_nonneg :
        0 ≤ problem6TypeOneDualRowOne alpha v - v (reverseItem j) :=
      problem6TypeOneDualRowOne_sub_reverse_nonneg alpha v j
    have hBt_nonneg :
        0 ≤ problem6TypeOneDualRowOne alpha v - v (reverseItem t) :=
      problem6TypeOneDualRowOne_sub_reverse_nonneg alpha v t
    have htarget :
        (problem6TypeOneDualRowOne alpha v - v (reverseItem j)) *
            (pairShare alpha v j / (1 - pairShare alpha v j)) ≤
          (problem6TypeOneDualRowOne alpha v - v (reverseItem t)) *
            (pairShare alpha v t / (1 - pairShare alpha v t)) := by
      exact mul_le_mul hBjt hratio
        (div_nonneg
          (pairShare_pos j halpha0 halpha1 hpos).le
          (one_sub_pairShare_pos j halpha0 halpha1 hpos).le)
        hBt_nonneg
    have hweight :
        (problem6TypeOneDualRowOne alpha v - v (reverseItem j)) /
            (1 - pairShare alpha v j) * pairShare alpha v j ≤
          problem6TypeOneDualRowZero alpha v t := by
      unfold problem6TypeOneDualRowZero
      have hdenj : 1 - pairShare alpha v j ≠ 0 :=
        ne_of_gt (one_sub_pairShare_pos j halpha0 halpha1 hpos)
      have hdent : 1 - pairShare alpha v t ≠ 0 :=
        ne_of_gt (one_sub_pairShare_pos t halpha0 halpha1 hpos)
      calc
        (problem6TypeOneDualRowOne alpha v - v (reverseItem j)) /
              (1 - pairShare alpha v j) * pairShare alpha v j =
            (problem6TypeOneDualRowOne alpha v - v (reverseItem j)) *
              (pairShare alpha v j / (1 - pairShare alpha v j)) := by
              field_simp [hdenj]
        _ ≤
            (problem6TypeOneDualRowOne alpha v - v (reverseItem t)) *
              (pairShare alpha v t / (1 - pairShare alpha v t)) := htarget
        _ =
            pairShare alpha v t *
              (problem6TypeOneDualRowOne alpha v - v (reverseItem t)) /
                (1 - pairShare alpha v t) := by
              field_simp [hdent]
    exact sub_nonneg.mpr hweight

theorem problem6TypeOneDual_typeOne_coeff_upper {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v) :
    ∀ j : Item n,
      v (reverseItem j) ≤
        problem6TypeOneDualRowOne alpha v -
          problem6TypeOneDualWeight alpha v t j *
            (1 - pairShare alpha v j) := by
  intro j
  unfold problem6TypeOneDualWeight
  by_cases hjt : j.val ≤ t.val
  · rw [if_pos hjt]
    have hq_le :
        pairShare alpha v t ≤ pairShare alpha v j :=
      problem6_pairShare_le_of_val_le
        halpha0 halpha1 hpos hdec hjt
    have hratio :
        (1 - pairShare alpha v j) / pairShare alpha v j ≤
          (1 - pairShare alpha v t) / pairShare alpha v t :=
      ratio_one_sub_self_antitone_of_le
        (pairShare_pos t halpha0 halpha1 hpos)
        (pairShare_lt_one t halpha0 halpha1 hpos)
        (pairShare_pos j halpha0 halpha1 hpos)
        (pairShare_lt_one j halpha0 halpha1 hpos)
        hq_le
    have hBjt :
        problem6TypeOneDualRowOne alpha v - v (reverseItem t) ≤
          problem6TypeOneDualRowOne alpha v - v (reverseItem j) := by
      have hrev : (reverseItem t).val ≤ (reverseItem j).val := by
        simp [reverseItem]
        omega
      have hv : v (reverseItem j) ≤ v (reverseItem t) :=
        value_antitone_of_val_le hdec hrev
      linarith
    have hBjt_nonneg :
        0 ≤ problem6TypeOneDualRowOne alpha v - v (reverseItem t) :=
      problem6TypeOneDualRowOne_sub_reverse_nonneg alpha v t
    have htarget :
        problem6TypeOneDualRowZero alpha v t / pairShare alpha v j *
            (1 - pairShare alpha v j) ≤
          problem6TypeOneDualRowOne alpha v - v (reverseItem j) := by
      have hfactor_nonneg :
          0 ≤ pairShare alpha v t / (1 - pairShare alpha v t) :=
        div_nonneg
          (pairShare_pos t halpha0 halpha1 hpos).le
          (one_sub_pairShare_pos t halpha0 halpha1 hpos).le
      have hfactor :
          (pairShare alpha v t / (1 - pairShare alpha v t)) *
              ((1 - pairShare alpha v j) / pairShare alpha v j) ≤ 1 := by
        have hmul :=
          mul_le_mul_of_nonneg_left hratio hfactor_nonneg
        have hright :
            (pairShare alpha v t / (1 - pairShare alpha v t)) *
                ((1 - pairShare alpha v t) / pairShare alpha v t) = 1 := by
          field_simp
            [ne_of_gt (pairShare_pos t halpha0 halpha1 hpos),
              ne_of_gt (one_sub_pairShare_pos t halpha0 halpha1 hpos)]
        exact hmul.trans_eq hright
      unfold problem6TypeOneDualRowZero
      have hqj : pairShare alpha v j ≠ 0 :=
        ne_of_gt (pairShare_pos j halpha0 halpha1 hpos)
      have hct : 1 - pairShare alpha v t ≠ 0 :=
        ne_of_gt (one_sub_pairShare_pos t halpha0 halpha1 hpos)
      calc
        pairShare alpha v t *
              (problem6TypeOneDualRowOne alpha v - v (reverseItem t)) /
              (1 - pairShare alpha v t) /
            pairShare alpha v j * (1 - pairShare alpha v j)
            =
          (problem6TypeOneDualRowOne alpha v - v (reverseItem t)) *
            ((pairShare alpha v t / (1 - pairShare alpha v t)) *
              ((1 - pairShare alpha v j) / pairShare alpha v j)) := by
              field_simp [hqj, hct]
        _ ≤ (problem6TypeOneDualRowOne alpha v - v (reverseItem t)) * 1 := by
              exact mul_le_mul_of_nonneg_left hfactor hBjt_nonneg
        _ ≤ problem6TypeOneDualRowOne alpha v - v (reverseItem j) := by
              simpa using hBjt
    linarith
  · rw [if_neg hjt]
    have hden : 1 - pairShare alpha v j ≠ 0 :=
      ne_of_gt (one_sub_pairShare_pos j halpha0 halpha1 hpos)
    field_simp [hden]
    ring_nf
    exact le_rfl

private theorem problem6TypeOneDualWeight_left_part_sum_eq {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {t : Item n} :
    (∑ j : Item n, if j.val < t.val then
        problem6TypeOneDualWeight alpha v t j else 0) =
      problem6TypeOneDualRowZero alpha v t *
        problem6LeftSum alpha v t := by
  unfold problem6LeftSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro j _hj
  by_cases hjt : j.val < t.val
  · have hjle : j.val ≤ t.val := hjt.le
    simp [hjt, problem6TypeOneDualWeight, hjle, div_eq_mul_inv]
  · simp [hjt]

private theorem problem6TypeOneDualWeight_right_part_sum_eq {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {t : Item n} :
    (∑ j : Item n, if t.val < j.val then
        problem6TypeOneDualWeight alpha v t j else 0) =
      ∑ j : Item n, if t.val < j.val then
        (problem6TypeOneDualRowOne alpha v - v (reverseItem j)) /
          (1 - pairShare alpha v j) else 0 := by
  refine Finset.sum_congr rfl ?_
  intro j _hj
  by_cases htj : t.val < j.val
  · have hnle : ¬ j.val ≤ t.val := by omega
    simp [htj, problem6TypeOneDualWeight, hnle]
  · simp [htj]

theorem problem6TypeOneDualWeight_sum_eq {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {t : Item n} :
    (∑ j : Item n, problem6TypeOneDualWeight alpha v t j) =
      problem6TypeOneDualRowZero alpha v t *
          problem6LeftSum alpha v t +
        problem6TypeOneDualRowZero alpha v t / pairShare alpha v t +
        ∑ j : Item n, if t.val < j.val then
          (problem6TypeOneDualRowOne alpha v - v (reverseItem j)) /
            (1 - pairShare alpha v j) else 0 := by
  have hsplit :=
    problem6_sum_eq_left_part_add_pivot_add_right_part
      (problem6TypeOneDualWeight alpha v t) t
  have hleft :
      (∑ j : Item n, if j.val < t.val then
          problem6TypeOneDualWeight alpha v t j else 0) =
        problem6TypeOneDualRowZero alpha v t *
          problem6LeftSum alpha v t :=
    problem6TypeOneDualWeight_left_part_sum_eq
  have hright :
      (∑ j : Item n, if t.val < j.val then
          problem6TypeOneDualWeight alpha v t j else 0) =
        ∑ j : Item n, if t.val < j.val then
          (problem6TypeOneDualRowOne alpha v - v (reverseItem j)) /
            (1 - pairShare alpha v j) else 0 :=
    problem6TypeOneDualWeight_right_part_sum_eq
  rw [hsplit, hleft, hright]
  simp [problem6TypeOneDualWeight]

private theorem problem6TypeOneDual_tail_sum_add_closed_gap_sum_eq {n : ℕ}
    [NeZero n] {alpha : ℝ} {v : Item n → ℝ} {t : Item n} :
    (∑ j : Item n, if t.val < j.val then
        (problem6TypeOneDualRowOne alpha v - v (reverseItem j)) /
          (1 - pairShare alpha v j) else 0) +
      (∑ j : Item n, if t.val < j.val then
        (v (reverseItem j) - v (reverseItem t)) /
          (1 - pairShare alpha v j) else 0) =
      (problem6TypeOneDualRowOne alpha v - v (reverseItem t)) *
        problem6RightSum alpha v t := by
  unfold problem6RightSum
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro j _hj
  by_cases htj : t.val < j.val
  · simp [htj, div_eq_mul_inv]
    ring
  · simp [htj]

/--
The paper's equality-form Problem 6 data before rebuilding the PMF policy.
The feasibility field carries the simplex/nonnegativity constraints, `item_eq`
is the equality-form constraint, `optimal` is optimality against all real
epigraph-feasible points, and `basic_feasible` is the support-count certificate
for the rebuilt policy.
-/
structure Problem6EqualityFormOptimalBFS {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ)
    (x y : Item n → ℝ) (ell : ℝ) : Prop where
  feasible : Problem6RealLPFeasible alpha v x y ell
  item_eq :
    ∀ j : Item n,
      pairShare alpha v j * x j + (1 - pairShare alpha v j) * y j = ell
  optimal :
    ∀ {x' y' : Item n → ℝ} {ell' : ℝ},
      Problem6RealLPFeasible alpha v x' y' ell' → ell' ≤ ell
  basic_feasible :
    TypePolicy.BasicFeasibleSupportCertificate
      (problem6PolicyOfRealVectors x y
        feasible.x_nonneg feasible.y_nonneg feasible.sum_x feasible.sum_y)

/--
The paper's equality-form optimal basic feasible solution package for Problem
6.  The equality field is the constraint
`q_j x_j + (1-q_j)y_j = λ` for every item, `optimal` records optimality for
the epigraph LP formulation used in the formalization, and `basic_feasible`
is the support-count consequence supplied by the basic-feasible-solution
theorem.
-/
structure Problem6EqualizedBasicOptimal {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) (ρ : TypePolicy 2 n) (ell : ℝ) :
    Prop where
  item_eq :
    ∀ l : Item n,
      pairShare alpha v l * (ρ 0 l).toReal +
        (1 - pairShare alpha v l) * (ρ 1 l).toReal = ell
  optimal : Problem6PolicyOptimal alpha v ρ ell
  basic_feasible : TypePolicy.BasicFeasibleSupportCertificate ρ

/--
The paper's real equality-form optimal BFS gives an optimal policy after
rebuilding the two PMF rows from `x` and `y`.
-/
theorem problem6PolicyOptimal_of_equalityFormOptimalBFS {n : ℕ}
    {alpha : ℝ} {v : Item n → ℝ}
    {x y : Item n → ℝ} {ell : ℝ}
    (h : Problem6EqualityFormOptimalBFS alpha v x y ell) :
    Problem6PolicyOptimal alpha v
      (problem6PolicyOfRealVectors x y
        h.feasible.x_nonneg h.feasible.y_nonneg
        h.feasible.sum_x h.feasible.sum_y) ell := by
  refine ⟨?_, ?_⟩
  · intro j
    simpa using le_of_eq (h.item_eq j).symm
  · intro ρ' ell' hfeas'
    exact h.optimal (problem6RealLPFeasible_of_policy hfeas')

/--
Extraction bridge from the paper's real equality-form optimal BFS to the
`Problem6EqualizedBasicOptimal` package consumed by Lemmas 4-11.
-/
theorem problem6EqualizedBasicOptimal_of_equalityFormOptimalBFS {n : ℕ}
    {alpha : ℝ} {v : Item n → ℝ}
    {x y : Item n → ℝ} {ell : ℝ}
    (h : Problem6EqualityFormOptimalBFS alpha v x y ell) :
    Problem6EqualizedBasicOptimal alpha v
      (problem6PolicyOfRealVectors x y
        h.feasible.x_nonneg h.feasible.y_nonneg
        h.feasible.sum_x h.feasible.sum_y) ell := by
  refine
    { item_eq := ?_
      optimal := problem6PolicyOptimal_of_equalityFormOptimalBFS h
      basic_feasible := h.basic_feasible }
  intro j
  simpa using h.item_eq j

/-- A Problem 6 optimal epigraph value is the minimum item value of its policy. -/
theorem problem6PolicyOptimal_value_eq_finiteMin {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 2 n} {ell : ℝ}
    (hopt : Problem6PolicyOptimal alpha v ρ ell) :
    ell =
      AppliedModelingLib.finiteMin (fun l : Item n =>
        pairShare alpha v l * (ρ 0 l).toReal +
          (1 - pairShare alpha v l) * (ρ 1 l).toReal) := by
  let value : Item n → ℝ := fun l =>
    pairShare alpha v l * (ρ 0 l).toReal +
      (1 - pairShare alpha v l) * (ρ 1 l).toReal
  have hell_le_min : ell ≤ AppliedModelingLib.finiteMin value := by
    dsimp [AppliedModelingLib.finiteMin]
    apply Finset.le_inf'
    intro l _hl
    exact hopt.1 l
  have hmin_feas : problem6LPFeasible alpha v ρ
      (AppliedModelingLib.finiteMin value) := by
    intro l
    dsimp [value]
    exact AppliedModelingLib.finiteMin_le value l
  have hmin_le_ell : AppliedModelingLib.finiteMin value ≤ ell :=
    hopt.2 ρ (AppliedModelingLib.finiteMin value) hmin_feas
  exact le_antisymm hell_le_min hmin_le_ell

/--
An optimal Problem 6 policy admits no feasible policy that strictly improves
every item value.  This uses optimality to identify `ell` with the minimum item
value of the current policy.
-/
theorem problem6_noStrictPointwiseImprovement_of_policyOptimal
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 2 n} {ell : ℝ}
    (hopt : Problem6PolicyOptimal alpha v ρ ell) :
    Problem6PolicyNoStrictPointwiseImprovement alpha v ρ := by
  classical
  intro hbad
  rcases hbad with ⟨ρ', hstrict⟩
  let value : Item n → ℝ := fun l =>
    pairShare alpha v l * (ρ 0 l).toReal +
      (1 - pairShare alpha v l) * (ρ 1 l).toReal
  let value' : Item n → ℝ := fun l =>
    pairShare alpha v l * (ρ' 0 l).toReal +
      (1 - pairShare alpha v l) * (ρ' 1 l).toReal
  let delta : ℝ := AppliedModelingLib.finiteMin (fun l : Item n => value' l - value l)
  have hdelta_pos : 0 < delta := by
    dsimp [delta]
    apply AppliedModelingLib.finiteMin_pos
    intro l
    exact sub_pos.mpr (hstrict l)
  let ell' : ℝ := ell + delta
  have hfeas' : problem6LPFeasible alpha v ρ' ell' := by
    intro l
    have hdelta_le :
        delta ≤ value' l - value l := by
      dsimp [delta]
      exact AppliedModelingLib.finiteMin_le
        (fun l : Item n => value' l - value l) l
    have hell_le_value : ell ≤ value l := by
      dsimp [value]
      exact hopt.1 l
    dsimp [ell', value, value'] at hdelta_le hell_le_value ⊢
    linarith
  have hle := hopt.2 ρ' ell' hfeas'
  dsimp [ell'] at hle
  linarith

/-- An optimal Problem 6 epigraph policy has strictly positive value. -/
theorem problem6PolicyOptimal_value_pos {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 2 n} {ell : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hopt : Problem6PolicyOptimal alpha v ρ ell) :
    0 < ell := by
  let ρu : TypePolicy 2 n :=
    TypeWeightedRecommendationModel.uniformTypePolicy (K := 2) (n := n)
  let value : Item n → ℝ := fun j =>
    pairShare alpha v j * (ρu 0 j).toReal +
      (1 - pairShare alpha v j) * (ρu 1 j).toReal
  let ell0 : ℝ := AppliedModelingLib.finiteMin value
  have hvalue_pos : ∀ j : Item n, 0 < value j := by
    intro j
    have hqpos : 0 < pairShare alpha v j :=
      pairShare_pos j halpha0 halpha1 hpos
    have hqcomp_pos : 0 < 1 - pairShare alpha v j :=
      one_sub_pairShare_pos j halpha0 halpha1 hpos
    have hxpos : 0 < (ρu 0 j).toReal := by
      simpa [ρu] using
        TypeWeightedRecommendationModel.uniformTypePolicy_apply_toReal_pos
          (K := 2) (n := n) (0 : UserType 2) j
    have hypos : 0 < (ρu 1 j).toReal := by
      simpa [ρu] using
        TypeWeightedRecommendationModel.uniformTypePolicy_apply_toReal_pos
          (K := 2) (n := n) (1 : UserType 2) j
    have hleft : 0 < pairShare alpha v j * (ρu 0 j).toReal :=
      mul_pos hqpos hxpos
    have hright : 0 < (1 - pairShare alpha v j) * (ρu 1 j).toReal :=
      mul_pos hqcomp_pos hypos
    dsimp [value]
    linarith
  have hell0_pos : 0 < ell0 := by
    dsimp [ell0]
    exact AppliedModelingLib.finiteMin_pos value hvalue_pos
  have hfeas0 : problem6LPFeasible alpha v ρu ell0 := by
    intro j
    dsimp [ell0, value]
    exact AppliedModelingLib.finiteMin_le value j
  have hell0_le : ell0 ≤ ell :=
    hopt.2 ρu ell0 hfeas0
  exact lt_of_lt_of_le hell0_pos hell0_le

/--
An equalized optimal Problem 6 policy covers every item: if no type
recommended an item, its equalized item value would be zero, contradicting the
strictly positive optimum value.
-/
theorem problem6_item_coverage_of_equalized_policyOptimal {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 2 n} {ell : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hitem_eq :
      ∀ l : Item n,
        pairShare alpha v l * (ρ 0 l).toReal +
          (1 - pairShare alpha v l) * (ρ 1 l).toReal = ell)
    (hopt : Problem6PolicyOptimal alpha v ρ ell) :
  ∀ j : Item n, ∃ k : UserType 2, ρ k j ≠ 0 := by
  intro j
  by_contra hnone
  push Not at hnone
  have h0 : ρ 0 j = 0 := hnone 0
  have h1 : ρ 1 j = 0 := hnone 1
  have hell_zero : ell = 0 := by
    have h := hitem_eq j
    simp [h0, h1] at h
    exact h.symm
  have hell_pos :
      0 < ell :=
    problem6PolicyOptimal_value_pos halpha0 halpha1 hpos hopt
  linarith

/--
For the paper's equality-form optimal BFS package, the basic-feasible support
count and positive equalized item values imply the Proposition 2 shared-item
bound.
-/
theorem problem6_sharedItemsBound_of_equalizedBasicOptimal {n : ℕ}
    [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 2 n} {ell : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (h : Problem6EqualizedBasicOptimal alpha v ρ ell) :
    TypePolicy.SharedItemsBound ρ := by
  have hactive : TypePolicy.ActivePairsBound ρ :=
    TypePolicy.activePairsBound_of_basicFeasibleSupportCertificate
      ρ h.basic_feasible
  exact TypePolicy.sharedItemsBound_of_activePairsBound_of_item_coverage
    ρ hactive
    (problem6_item_coverage_of_equalized_policyOptimal
      halpha0 halpha1 hpos h.item_eq h.optimal)

/--
An equalized optimal Problem 6 policy admits no feasible policy that strictly
improves every item value.
-/
theorem problem6_noStrictPointwiseImprovement_of_policyOptimal_equalized
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 2 n} {ell : ℝ}
    (hitem_eq :
      ∀ l : Item n,
        pairShare alpha v l * (ρ 0 l).toReal +
          (1 - pairShare alpha v l) * (ρ 1 l).toReal = ell)
    (hopt : Problem6PolicyOptimal alpha v ρ ell) :
    Problem6PolicyNoStrictPointwiseImprovement alpha v ρ := by
  exact problem6_noStrictPointwiseImprovement_of_policyOptimal hopt

/--
Appendix D, Lemma 4 no-gap consequence for the first row.

Under the equalized Problem 6 constraints and the local optimality condition
that no feasible policy strictly improves every item value, an earlier zero
`x_j` rules out any later positive `x_i`.
-/
theorem lemma4_twoTypeXZeroClosed_of_noStrictPointwiseImprovement {n : ℕ}
    {alpha : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 2 n} {ell : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hredistrib :
      ∀ {i j : Item n}, j.val < i.val →
        ∃ r : Item n → ℝ,
          (∀ l : Item n, 0 ≤ r l) ∧
          (∀ {l : Item n}, l ≠ i → l ≠ j → 0 < r l) ∧
          r i = 0 ∧ r j = 0 ∧
          (∑ l : Item n, r l) = 1)
    (hitem_eq :
      ∀ l : Item n,
        pairShare alpha v l * (ρ 0 l).toReal +
          (1 - pairShare alpha v l) * (ρ 1 l).toReal = ell)
    (hno : Problem6PolicyNoStrictPointwiseImprovement alpha v ρ) :
    TypePolicy.TwoTypeXZeroClosed ρ := by
  classical
  intro j i hji hxj_zero
  by_contra hxi_not_zero
  let x : Item n → ℝ := fun l => (ρ 0 l).toReal
  let y : Item n → ℝ := fun l => (ρ 1 l).toReal
  let c : ℝ := x i
  have hx_nonneg : ∀ l : Item n, 0 ≤ x l := by
    intro l
    exact ENNReal.toReal_nonneg
  have hy_nonneg : ∀ l : Item n, 0 ≤ y l := by
    intro l
    exact ENNReal.toReal_nonneg
  have hxi : x i = c := rfl
  have hxj : x j = 0 := by
    dsimp [x]
    simp [hxj_zero]
  have hc : 0 < c := by
    have htoReal_ne : (ρ 0 i).toReal ≠ 0 := by
      intro hzero
      have hzero_or_top :=
        (ENNReal.toReal_eq_zero_iff (ρ 0 i)).mp hzero
      rcases hzero_or_top with hzero_enn | htop
      · exact hxi_not_zero hzero_enn
      · exact (ρ 0).apply_ne_top i htop
    exact lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm htoReal_ne)
  have hsumx : (∑ l : Item n, x l) = 1 := by
    dsimp [x]
    exact problem6_typeZero_sum_eq_one ρ
  have hsumy : (∑ l : Item n, y l) = 1 := by
    dsimp [y]
    exact problem6_typeOne_sum_eq_one ρ
  obtain ⟨r, hr_nonneg, hr_pos, hri, hrj, hrsum⟩ := hredistrib hji
  have hi_eq :
      pairShare alpha v i * x i +
        (1 - pairShare alpha v i) * y i = ell := by
    simpa [x, y] using hitem_eq i
  have hj_eq :
      pairShare alpha v j * x j +
        (1 - pairShare alpha v j) * y j = ell := by
    simpa [x, y] using hitem_eq j
  obtain ⟨eps1, eps2, x', y', _heps1_pos, _heps1_lt_c,
      _heps2_pos, _heps2_lt_gap, hx'_nonneg, hy'_nonneg,
      hx'_sum, hy'_sum, hstrict⟩ :=
    lemma4_pairShare_gap_exchange_exists_strictly_improves
      halpha0 halpha1 hpos hdec hji hx_nonneg hy_nonneg hxi hxj hc
      hsumx hsumy hr_nonneg hr_pos hri hrj hrsum hi_eq hj_eq
  let ρ' : TypePolicy 2 n := fun k =>
    if k = 0 then
      pmfOfRealVector x' hx'_nonneg hx'_sum
    else
      pmfOfRealVector y' hy'_nonneg hy'_sum
  apply hno
  refine ⟨ρ', ?_⟩
  intro l
  have h := hstrict l
  simpa [ρ', x, y] using h

/--
Appendix D, Lemma 4 no-gap consequence for the second row.

This is the symmetric argument in the paper: under the equalized Problem 6
constraints and the same local optimality condition, a later zero `y_j` rules
out any earlier positive `y_i`.
-/
theorem lemma4_twoTypeYZeroClosed_of_noStrictPointwiseImprovement {n : ℕ}
    {alpha : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 2 n} {ell : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hredistrib :
      ∀ {i j : Item n}, i.val < j.val →
        ∃ r : Item n → ℝ,
          (∀ l : Item n, 0 ≤ r l) ∧
          (∀ {l : Item n}, l ≠ i → l ≠ j → 0 < r l) ∧
          r i = 0 ∧ r j = 0 ∧
          (∑ l : Item n, r l) = 1)
    (hitem_eq :
      ∀ l : Item n,
        pairShare alpha v l * (ρ 0 l).toReal +
          (1 - pairShare alpha v l) * (ρ 1 l).toReal = ell)
    (hno : Problem6PolicyNoStrictPointwiseImprovement alpha v ρ) :
    TypePolicy.TwoTypeYZeroClosed ρ := by
  classical
  intro i j hij hyj_zero
  by_contra hyi_not_zero
  let x : Item n → ℝ := fun l => (ρ 0 l).toReal
  let y : Item n → ℝ := fun l => (ρ 1 l).toReal
  let c : ℝ := y i
  have hx_nonneg : ∀ l : Item n, 0 ≤ x l := by
    intro l
    exact ENNReal.toReal_nonneg
  have hy_nonneg : ∀ l : Item n, 0 ≤ y l := by
    intro l
    exact ENNReal.toReal_nonneg
  have hyi : y i = c := rfl
  have hyj : y j = 0 := by
    dsimp [y]
    simp [hyj_zero]
  have hc : 0 < c := by
    have htoReal_ne : (ρ 1 i).toReal ≠ 0 := by
      intro hzero
      have hzero_or_top :=
        (ENNReal.toReal_eq_zero_iff (ρ 1 i)).mp hzero
      rcases hzero_or_top with hzero_enn | htop
      · exact hyi_not_zero hzero_enn
      · exact (ρ 1).apply_ne_top i htop
    exact lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm htoReal_ne)
  have hsumx : (∑ l : Item n, x l) = 1 := by
    dsimp [x]
    exact problem6_typeZero_sum_eq_one ρ
  have hsumy : (∑ l : Item n, y l) = 1 := by
    dsimp [y]
    exact problem6_typeOne_sum_eq_one ρ
  obtain ⟨r, hr_nonneg, hr_pos, hri, hrj, hrsum⟩ := hredistrib hij
  have hi_eq :
      pairShare alpha v i * x i +
        (1 - pairShare alpha v i) * y i = ell := by
    simpa [x, y] using hitem_eq i
  have hj_eq :
      pairShare alpha v j * x j +
        (1 - pairShare alpha v j) * y j = ell := by
    simpa [x, y] using hitem_eq j
  obtain ⟨eps1, eps2, x', y', _heps1_pos, _heps1_lt_c,
      _heps2_pos, _heps2_lt_gap, hx'_nonneg, hy'_nonneg,
      hx'_sum, hy'_sum, hstrict⟩ :=
    lemma4_pairShare_y_gap_exchange_exists_strictly_improves
      halpha0 halpha1 hpos hdec hij hx_nonneg hy_nonneg hyi hyj hc
      hsumx hsumy hr_nonneg hr_pos hri hrj hrsum hi_eq hj_eq
  let ρ' : TypePolicy 2 n := fun k =>
    if k = 0 then
      pmfOfRealVector x' hx'_nonneg hx'_sum
    else
      pmfOfRealVector y' hy'_nonneg hy'_sum
  apply hno
  refine ⟨ρ', ?_⟩
  intro l
  have h := hstrict l
  simpa [ρ', x, y] using h

/--
The redistribution vector used in Appendix D, Lemma 4 exists whenever there is
at least one item other than the exchanged pair.  It is the paper's uniform
`1/(n-2)` distribution over all unaffected items.
-/
theorem lemma4_redistribution_exists_of_two_lt {n : ℕ}
    (hn : 2 < n) {i j : Item n} (hij : i ≠ j) :
    ∃ r : Item n → ℝ,
      (∀ l : Item n, 0 ≤ r l) ∧
      (∀ {l : Item n}, l ≠ i → l ≠ j → 0 < r l) ∧
      r i = 0 ∧ r j = 0 ∧
      (∑ l : Item n, r l) = 1 := by
  classical
  let s : Finset (Item n) := (Finset.univ.erase i).erase j
  have hi_mem : i ∈ (Finset.univ : Finset (Item n)) := by
    simp
  have hj_mem : j ∈ (Finset.univ.erase i : Finset (Item n)) := by
    simp [hij.symm]
  have hcard_s : s.card = n - 2 := by
    dsimp [s]
    rw [Finset.card_erase_of_mem hj_mem]
    rw [Finset.card_erase_of_mem hi_mem]
    simp [Item]
    omega
  have hcard_pos_nat : 0 < s.card := by
    rw [hcard_s]
    omega
  have hcard_pos_real : 0 < (s.card : ℝ) := by
    exact_mod_cast hcard_pos_nat
  let r : Item n → ℝ := fun l =>
    if l ∈ s then ((s.card : ℝ)⁻¹) else 0
  refine ⟨r, ?_, ?_, ?_, ?_, ?_⟩
  · intro l
    by_cases hls : l ∈ s
    · simp [r, hls, inv_nonneg.mpr hcard_pos_real.le]
    · simp [r, hls]
  · intro l hli hlj
    have hls : l ∈ s := by
      simp [s, hli, hlj]
    simpa [r, hls] using inv_pos.mpr hcard_pos_real
  · simp [r, s]
  · simp [r, s]
  · calc
      (∑ l : Item n, r l)
          = ∑ l : Item n, if l ∈ s then ((s.card : ℝ)⁻¹) else 0 := by
              rfl
      _ = ∑ l ∈ s, ((s.card : ℝ)⁻¹) := by
              simp [Finset.sum_ite_mem]
      _ = (s.card : ℝ) * ((s.card : ℝ)⁻¹) := by
              simp [Finset.sum_const, nsmul_eq_mul]
      _ = 1 := by
              exact mul_inv_cancel₀ (ne_of_gt hcard_pos_real)

/--
Appendix D, Lemma 4 threshold-support conclusion from the perturbation
argument and the Proposition 2 shared-item bound.
-/
theorem lemma4_twoTypeThresholdSupport_of_noStrictPointwiseImprovement {n : ℕ}
    [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 2 n} {ell : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hredistrib :
      ∀ {i j : Item n}, i ≠ j →
        ∃ r : Item n → ℝ,
          (∀ l : Item n, 0 ≤ r l) ∧
          (∀ {l : Item n}, l ≠ i → l ≠ j → 0 < r l) ∧
          r i = 0 ∧ r j = 0 ∧
          (∑ l : Item n, r l) = 1)
    (hitem_eq :
      ∀ l : Item n,
        pairShare alpha v l * (ρ 0 l).toReal +
          (1 - pairShare alpha v l) * (ρ 1 l).toReal = ell)
    (hno : Problem6PolicyNoStrictPointwiseImprovement alpha v ρ)
    (hshared : TypePolicy.SharedItemsBound ρ) :
    TypePolicy.TwoTypeThresholdSupport ρ := by
  have hx : TypePolicy.TwoTypeXZeroClosed ρ :=
    lemma4_twoTypeXZeroClosed_of_noStrictPointwiseImprovement
      halpha0 halpha1 hpos hdec
      (fun {i j} hji =>
        hredistrib (by
          intro hij
          subst i
          omega))
      hitem_eq hno
  have hy : TypePolicy.TwoTypeYZeroClosed ρ :=
    lemma4_twoTypeYZeroClosed_of_noStrictPointwiseImprovement
      halpha0 halpha1 hpos hdec
      (fun {i j} hij =>
        hredistrib (by
          intro h
          subst j
          omega))
      hitem_eq hno
  exact TypePolicy.twoTypeThresholdSupport_of_zeroClosed_of_sharedBound
    ρ hx hy hshared

/--
Appendix D, Lemma 4 threshold-support conclusion with the paper's uniform
redistribution vector discharged by `2 < n`.
-/
theorem lemma4_twoTypeThresholdSupport_of_noStrictPointwiseImprovement_of_two_lt
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 2 n} {ell : ℝ}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hitem_eq :
      ∀ l : Item n,
        pairShare alpha v l * (ρ 0 l).toReal +
          (1 - pairShare alpha v l) * (ρ 1 l).toReal = ell)
    (hno : Problem6PolicyNoStrictPointwiseImprovement alpha v ρ)
    (hshared : TypePolicy.SharedItemsBound ρ) :
    TypePolicy.TwoTypeThresholdSupport ρ := by
  exact lemma4_twoTypeThresholdSupport_of_noStrictPointwiseImprovement
    halpha0 halpha1 hpos hdec
    (fun hij => lemma4_redistribution_exists_of_two_lt hn hij)
    hitem_eq hno hshared

/--
Appendix D, Lemma 4 threshold-support conclusion for an equalized optimal
Problem 6 policy, with the paper's redistribution vector discharged by `2 < n`.
-/
theorem lemma4_twoTypeThresholdSupport_of_policyOptimal_equalized_of_two_lt
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 2 n} {ell : ℝ}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hitem_eq :
      ∀ l : Item n,
        pairShare alpha v l * (ρ 0 l).toReal +
          (1 - pairShare alpha v l) * (ρ 1 l).toReal = ell)
    (hopt : Problem6PolicyOptimal alpha v ρ ell)
    (hshared : TypePolicy.SharedItemsBound ρ) :
    TypePolicy.TwoTypeThresholdSupport ρ := by
  have hno :
      Problem6PolicyNoStrictPointwiseImprovement alpha v ρ :=
    problem6_noStrictPointwiseImprovement_of_policyOptimal_equalized
      hitem_eq hopt
  exact lemma4_twoTypeThresholdSupport_of_noStrictPointwiseImprovement_of_two_lt
    hn halpha0 halpha1 hpos hdec hitem_eq hno hshared

/--
Lemma 4 to Lemma 5 bridge: once the paper's perturbation argument has produced
threshold support, the policy is exactly a sparse equalized real solution with
the threshold pivot.
-/
theorem problem6SparseEqualized_of_twoTypeThresholdSupport {n : ℕ}
    {alpha : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 2 n} {ell : ℝ}
    (hitem_eq :
      ∀ l : Item n,
        pairShare alpha v l * (ρ 0 l).toReal +
          (1 - pairShare alpha v l) * (ρ 1 l).toReal = ell)
    (hthreshold : TypePolicy.TwoTypeThresholdSupport ρ) :
    ∃ t : Item n,
      Problem6SparseEqualized alpha v t
        (fun l : Item n => (ρ 0 l).toReal)
        (fun l : Item n => (ρ 1 l).toReal) ell := by
  rcases hthreshold with ⟨t, hx_after, hy_before⟩
  refine ⟨t, ?_⟩
  refine
    { item_eq := ?_
      sum_x := ?_
      sum_y := ?_
      x_after_pivot_zero := ?_
      y_before_pivot_zero := ?_ }
  · intro j
    exact hitem_eq j
  · exact problem6_typeZero_sum_eq_one ρ
  · exact problem6_typeOne_sum_eq_one ρ
  · intro j hj
    have hzero : ρ 0 j = 0 := hx_after hj
    simpa [hzero]
  · intro j hj
    have hzero : ρ 1 j = 0 := hy_before hj
    simpa [hzero]

/--
Appendix D, Lemma 4 to Lemma 5 bridge for an equalized optimal Problem 6
policy: the threshold-support conclusion supplies a sparse equalized real
solution for some pivot.
-/
theorem problem6SparseEqualized_of_policyOptimal_equalized_of_two_lt
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 2 n} {ell : ℝ}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hitem_eq :
      ∀ l : Item n,
        pairShare alpha v l * (ρ 0 l).toReal +
          (1 - pairShare alpha v l) * (ρ 1 l).toReal = ell)
    (hopt : Problem6PolicyOptimal alpha v ρ ell)
    (hshared : TypePolicy.SharedItemsBound ρ) :
    ∃ t : Item n,
      Problem6SparseEqualized alpha v t
        (fun l : Item n => (ρ 0 l).toReal)
        (fun l : Item n => (ρ 1 l).toReal) ell := by
  have hthreshold :
      TypePolicy.TwoTypeThresholdSupport ρ :=
    lemma4_twoTypeThresholdSupport_of_policyOptimal_equalized_of_two_lt
      hn halpha0 halpha1 hpos hdec hitem_eq hopt hshared
  exact problem6SparseEqualized_of_twoTypeThresholdSupport
    hitem_eq hthreshold

/--
Lemma 4 to Lemma 5 bridge retaining the paper's pivot choice
`t = max {j : x_j > 0}`.  From the no-gap support shape and shared-item bound,
the last active type-`0` item yields a sparse equalized solution with
nonnegative coordinates and positive pivot `x_t`.
-/
theorem problem6SparseEqualizedActive_of_zeroClosed_sharedBound
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 2 n} {ell : ℝ}
    (hitem_eq :
      ∀ l : Item n,
        pairShare alpha v l * (ρ 0 l).toReal +
          (1 - pairShare alpha v l) * (ρ 1 l).toReal = ell)
    (hx : TypePolicy.TwoTypeXZeroClosed ρ)
    (hy : TypePolicy.TwoTypeYZeroClosed ρ)
    (hshared : TypePolicy.SharedItemsBound ρ) :
    Problem6SparseEqualizedActive alpha v (TypePolicy.lastActiveTypeZero ρ)
      (fun l : Item n => (ρ 0 l).toReal)
      (fun l : Item n => (ρ 1 l).toReal) ell := by
  refine
    { sparse := ?_
      x_nonneg := ?_
      y_nonneg := ?_
      x_pivot_pos := ?_ }
  · refine
      { item_eq := ?_
        sum_x := ?_
        sum_y := ?_
        x_after_pivot_zero := ?_
        y_before_pivot_zero := ?_ }
    · intro j
      exact hitem_eq j
    · exact problem6_typeZero_sum_eq_one ρ
    · exact problem6_typeOne_sum_eq_one ρ
    · intro j hj
      have hzero : ρ 0 j = 0 :=
        TypePolicy.typeZero_zero_after_lastActive ρ hj
      simpa [hzero]
    · intro j hj
      have hzero : ρ 1 j = 0 :=
        TypePolicy.typeOne_zero_before_lastActive_of_zeroClosed_of_sharedBound
          ρ hx hy hshared hj
      simpa [hzero]
  · intro j
    exact ENNReal.toReal_nonneg
  · intro j
    exact ENNReal.toReal_nonneg
  · exact typePolicy_toReal_pos_of_ne_zero ρ
      (TypePolicy.lastActiveTypeZero_active ρ)

/--
Appendix D, Lemma 4 active sparse bridge under the local optimality condition:
the perturbation argument gives the no-gap support shape, and the paper pivot
is the last active type-`0` item.
-/
theorem problem6SparseEqualizedActive_of_noStrictPointwiseImprovement_of_two_lt
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 2 n} {ell : ℝ}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hitem_eq :
      ∀ l : Item n,
        pairShare alpha v l * (ρ 0 l).toReal +
          (1 - pairShare alpha v l) * (ρ 1 l).toReal = ell)
    (hno : Problem6PolicyNoStrictPointwiseImprovement alpha v ρ)
    (hshared : TypePolicy.SharedItemsBound ρ) :
    Problem6SparseEqualizedActive alpha v (TypePolicy.lastActiveTypeZero ρ)
      (fun l : Item n => (ρ 0 l).toReal)
      (fun l : Item n => (ρ 1 l).toReal) ell := by
  have hx : TypePolicy.TwoTypeXZeroClosed ρ :=
    lemma4_twoTypeXZeroClosed_of_noStrictPointwiseImprovement
      halpha0 halpha1 hpos hdec
      (fun {i j} hji =>
        lemma4_redistribution_exists_of_two_lt hn (by
          intro hij
          subst i
          omega))
      hitem_eq hno
  have hy : TypePolicy.TwoTypeYZeroClosed ρ :=
    lemma4_twoTypeYZeroClosed_of_noStrictPointwiseImprovement
      halpha0 halpha1 hpos hdec
      (fun {i j} hij =>
        lemma4_redistribution_exists_of_two_lt hn (by
          intro h
          subst j
          omega))
      hitem_eq hno
  exact problem6SparseEqualizedActive_of_zeroClosed_sharedBound
    hitem_eq hx hy hshared

/--
Appendix D, Lemma 4 active sparse bridge for an equalized optimal Problem 6
policy.
-/
theorem problem6SparseEqualizedActive_of_policyOptimal_equalized_of_two_lt
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 2 n} {ell : ℝ}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hitem_eq :
      ∀ l : Item n,
        pairShare alpha v l * (ρ 0 l).toReal +
          (1 - pairShare alpha v l) * (ρ 1 l).toReal = ell)
    (hopt : Problem6PolicyOptimal alpha v ρ ell)
    (hshared : TypePolicy.SharedItemsBound ρ) :
    Problem6SparseEqualizedActive alpha v (TypePolicy.lastActiveTypeZero ρ)
      (fun l : Item n => (ρ 0 l).toReal)
      (fun l : Item n => (ρ 1 l).toReal) ell := by
  have hno :
      Problem6PolicyNoStrictPointwiseImprovement alpha v ρ :=
    problem6_noStrictPointwiseImprovement_of_policyOptimal_equalized
      hitem_eq hopt
  exact problem6SparseEqualizedActive_of_noStrictPointwiseImprovement_of_two_lt
    hn halpha0 halpha1 hpos hdec hitem_eq hno hshared

/--
Appendix D, Lemma 4 active sparse bridge for the paper's equality-form optimal
BFS package.  The shared-item bound is derived from the basic-feasible support
count and positive equalized item values.
-/
theorem problem6SparseEqualizedActive_of_equalizedBasicOptimal_of_two_lt
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 2 n} {ell : ℝ}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (h : Problem6EqualizedBasicOptimal alpha v ρ ell) :
    Problem6SparseEqualizedActive alpha v (TypePolicy.lastActiveTypeZero ρ)
      (fun l : Item n => (ρ 0 l).toReal)
      (fun l : Item n => (ρ 1 l).toReal) ell := by
  exact problem6SparseEqualizedActive_of_policyOptimal_equalized_of_two_lt
    hn halpha0 halpha1 hpos hdec h.item_eq h.optimal
    (problem6_sharedItemsBound_of_equalizedBasicOptimal
      halpha0 halpha1 hpos h)

/-- The Problem 6 closed-form real solution as a two-type policy. -/
noncomputable def problem6ClosedPolicy {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) (t : Item n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hpivot : Problem6ClosedNonnegativePivots alpha v t) :
    TypePolicy 2 n :=
  fun k =>
    if k = 0 then
      pmfOfRealVector (problem6ClosedX alpha v t)
        (problem6ClosedX_nonneg halpha0 halpha1 hpos hpivot)
        (problem6ClosedX_sum_eq_one alpha v t)
    else
      pmfOfRealVector (problem6ClosedY alpha v t)
        (problem6ClosedY_nonneg halpha0 halpha1 hpos hpivot)
        (problem6ClosedY_sum_eq_one alpha v t)

@[simp] theorem problem6ClosedPolicy_zero_toReal {n : ℕ}
    {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hpivot : Problem6ClosedNonnegativePivots alpha v t)
    (j : Item n) :
    ((problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot 0) j).toReal =
      problem6ClosedX alpha v t j := by
  simp [problem6ClosedPolicy]

@[simp] theorem problem6ClosedPolicy_one_toReal {n : ℕ}
    {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hpivot : Problem6ClosedNonnegativePivots alpha v t)
    (j : Item n) :
    ((problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot 1) j).toReal =
      problem6ClosedY alpha v t j := by
  simp [problem6ClosedPolicy]

/-- The closed-form policy satisfies Problem 6's LP epigraph constraints. -/
theorem problem6ClosedPolicy_feasible {n : ℕ}
    {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hpivot : Problem6ClosedNonnegativePivots alpha v t) :
    problem6LPFeasible alpha v
      (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot)
      (problem6ClosedValue alpha v t) := by
  intro j
  rw [problem6ClosedPolicy_zero_toReal halpha0 halpha1 hpos hpivot,
    problem6ClosedPolicy_one_toReal halpha0 halpha1 hpos hpivot]
  exact le_of_eq (problem6Closed_item_eq t j halpha0 halpha1 hpos).symm

/--
Denominator bounds are enough to build a feasible closed-form Problem 6 policy.
-/
theorem problem6ClosedPolicy_feasible_of_denominatorBounds {n : ℕ}
    {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hbounds : Problem6ClosedPivotDenominatorBounds alpha v t) :
    problem6LPFeasible alpha v
      (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos
        (problem6ClosedNonnegativePivots_of_denominatorBounds
          halpha0 halpha1 hpos hbounds))
      (problem6ClosedValue alpha v t) := by
  exact problem6ClosedPolicy_feasible halpha0 halpha1 hpos
    (problem6ClosedNonnegativePivots_of_denominatorBounds
      halpha0 halpha1 hpos hbounds)

/--
The Lemma 5 closed-form policy has the threshold support shape used in
Appendix D, Lemma 4: type `0` is zero after the pivot and type `1` is zero
before it.
-/
theorem problem6ClosedPolicy_twoTypeThresholdSupport {n : ℕ}
    {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hpivot : Problem6ClosedNonnegativePivots alpha v t) :
    TypePolicy.TwoTypeThresholdSupport
      (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot) := by
  refine ⟨t, ?_, ?_⟩
  · intro j hj
    apply pmf_apply_eq_zero_of_toReal_eq_zero
    rw [problem6ClosedPolicy_zero_toReal halpha0 halpha1 hpos hpivot,
      problem6ClosedX_after alpha v hj]
  · intro j hj
    apply pmf_apply_eq_zero_of_toReal_eq_zero
    rw [problem6ClosedPolicy_one_toReal halpha0 halpha1 hpos hpivot,
      problem6ClosedY_before alpha v hj]

/--
Closed-form Problem 6 policies satisfy the paper's two-type basic-feasible
support-count certificate directly from their threshold support.
-/
theorem problem6ClosedPolicy_basicFeasibleSupportCertificate {n : ℕ}
    {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hpivot : Problem6ClosedNonnegativePivots alpha v t) :
    TypePolicy.BasicFeasibleSupportCertificate
      (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot) := by
  exact TypePolicy.basicFeasibleSupportCertificate_of_twoTypeThresholdSupport
    (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot)
    (problem6ClosedPolicy_twoTypeThresholdSupport
      halpha0 halpha1 hpos hpivot)

/-- Raw type-0 utility of the closed-form Problem 6 policy. -/
noncomputable def problem6ClosedTypeZeroRawUtility {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) (t : Item n) : ℝ :=
  ∑ j : Item n, v j * problem6ClosedX alpha v t j

/-- Raw type-1 utility of the closed-form Problem 6 policy. -/
noncomputable def problem6ClosedTypeOneRawUtility {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) (t : Item n) : ℝ :=
  ∑ j : Item n, v (reverseItem j) * problem6ClosedY alpha v t j

/--
Mirror-reindexing form of the closed type-1 raw utility, matching the summation
used in Lemma 6.
-/
theorem problem6ClosedTypeOneRawUtility_eq_mirror_sum {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) (t : Item n) :
    problem6ClosedTypeOneRawUtility alpha v t =
      ∑ j : Item n, v j * problem6ClosedY alpha v t (reverseItem j) := by
  unfold problem6ClosedTypeOneRawUtility
  simpa [reverseItem_reverseItem] using
    (sum_reverseItem
      (fun j : Item n => v j * problem6ClosedY alpha v t (reverseItem j)))

/-- Mirrored closed-form `y` coordinates still have total mass one. -/
theorem problem6ClosedY_reverse_sum_eq_one {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) (t : Item n) :
    (∑ j : Item n, problem6ClosedY alpha v t (reverseItem j)) = 1 := by
  rw [sum_reverseItem]
  exact problem6ClosedY_sum_eq_one alpha v t

/--
Appendix D, Lemma 6 summation identity: the raw utility gap is the weighted
sum of mirror-coordinate gaps.
-/
theorem problem6ClosedRawUtility_sub_eq_mirror_gap_sum {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) (t : Item n) :
    problem6ClosedTypeZeroRawUtility alpha v t -
        problem6ClosedTypeOneRawUtility alpha v t =
      ∑ j : Item n,
        v j * (problem6ClosedX alpha v t j -
          problem6ClosedY alpha v t (reverseItem j)) := by
  unfold problem6ClosedTypeZeroRawUtility
  rw [problem6ClosedTypeOneRawUtility_eq_mirror_sum]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro j _hj
  ring

/--
Appendix D, Lemma 6 coordinate dominance: for `α ≤ 1/2`, a pre-pivot
closed-form `x_j` coordinate dominates the mirrored `y_{n-j+1}` coordinate
whenever the mirror item lies after the pivot.
-/
theorem problem6ClosedX_sub_closedY_reverse_nonneg_of_alpha_le_half
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {t j : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha_half : alpha ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hj : j.val < t.val)
    (hrev : t.val < (reverseItem j).val) :
    0 ≤ problem6ClosedX alpha v t j -
      problem6ClosedY alpha v t (reverseItem j) := by
  rw [problem6ClosedX_before alpha v hj,
    problem6ClosedY_after alpha v hrev]
  have hcv : 0 ≤ problem6ClosedValue alpha v t :=
    (problem6ClosedValue_pos t halpha0 halpha1 hpos).le
  have hgap :
      0 ≤ (pairShare alpha v j)⁻¹ -
        (1 - pairShare alpha v (reverseItem j))⁻¹ :=
    pairShare_inv_sub_inv_one_sub_reverse_nonneg_of_alpha_le_half
      j halpha0 halpha1 halpha_half hpos
  have heq :
      problem6ClosedValue alpha v t / pairShare alpha v j -
          problem6ClosedValue alpha v t /
            (1 - pairShare alpha v (reverseItem j)) =
        problem6ClosedValue alpha v t *
          ((pairShare alpha v j)⁻¹ -
            (1 - pairShare alpha v (reverseItem j))⁻¹) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    ring
  rw [heq]
  exact mul_nonneg hcv hgap

/--
Appendix D, Lemma 6 finite-sum comparison: if all mirror gaps up to the pivot
are nonnegative, and all mirrored `y` masses are nonnegative, then the closed
type-0 raw utility dominates the closed type-1 raw utility.
-/
theorem problem6ClosedTypeOneRawUtility_le_typeZeroRawUtility_of_left_gaps
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (hdec : StrictlyDecreasingByIndex v)
    (hleft :
      ∀ j : Item n, j.val ≤ t.val →
        0 ≤ problem6ClosedX alpha v t j -
          problem6ClosedY alpha v t (reverseItem j))
    (hy_nonneg :
      ∀ j : Item n, 0 ≤ problem6ClosedY alpha v t (reverseItem j)) :
    problem6ClosedTypeOneRawUtility alpha v t ≤
      problem6ClosedTypeZeroRawUtility alpha v t := by
  let gap : Item n → ℝ :=
    fun j => problem6ClosedX alpha v t j -
      problem6ClosedY alpha v t (reverseItem j)
  have hgap_sum : (∑ j : Item n, gap j) = 0 := by
    unfold gap
    rw [Finset.sum_sub_distrib]
    rw [problem6ClosedX_sum_eq_one, problem6ClosedY_reverse_sum_eq_one]
    ring
  have hterm :
      (∑ j : Item n, v t * gap j) ≤
        ∑ j : Item n, v j * gap j := by
    refine Finset.sum_le_sum ?_
    intro j _hj
    by_cases hjle : j.val ≤ t.val
    · have hv : v t ≤ v j := by
        by_cases heq : j = t
        · subst j
          rfl
        · have hlt : j.val < t.val := by
            have hne_val : j.val ≠ t.val := by
              intro hval
              exact heq (Fin.ext hval)
            omega
          exact (hdec hlt).le
      exact mul_le_mul_of_nonneg_right hv (hleft j hjle)
    · have hgt : t.val < j.val := by omega
      have hv : v j ≤ v t := (hdec hgt).le
      have hgap_nonpos : gap j ≤ 0 := by
        unfold gap
        rw [problem6ClosedX_after alpha v hgt]
        linarith [hy_nonneg j]
      exact mul_le_mul_of_nonpos_right hv hgap_nonpos
  have hweighted_nonneg :
      0 ≤ ∑ j : Item n, v j * gap j := by
    have hconst :
        (∑ j : Item n, v t * gap j) = 0 := by
      rw [← Finset.mul_sum, hgap_sum, mul_zero]
    linarith
  have hraw :=
    problem6ClosedRawUtility_sub_eq_mirror_gap_sum alpha v t
  unfold gap at hweighted_nonneg
  linarith

/--
Appendix D, Lemma 6 finite-sum comparison in the paper's sharper form: only
the strict pre-pivot mirror gaps need to be nonnegative.  The pivot gap has
coefficient `v_t` in the constant-weight decomposition and cancels out.
-/
theorem problem6ClosedTypeOneRawUtility_le_typeZeroRawUtility_of_strict_left_gaps
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (hdec : StrictlyDecreasingByIndex v)
    (hleft :
      ∀ j : Item n, j.val < t.val →
        0 ≤ problem6ClosedX alpha v t j -
          problem6ClosedY alpha v t (reverseItem j))
    (hy_nonneg :
      ∀ j : Item n, 0 ≤ problem6ClosedY alpha v t (reverseItem j)) :
    problem6ClosedTypeOneRawUtility alpha v t ≤
      problem6ClosedTypeZeroRawUtility alpha v t := by
  let gap : Item n → ℝ :=
    fun j => problem6ClosedX alpha v t j -
      problem6ClosedY alpha v t (reverseItem j)
  have hgap_sum : (∑ j : Item n, gap j) = 0 := by
    unfold gap
    rw [Finset.sum_sub_distrib]
    rw [problem6ClosedX_sum_eq_one, problem6ClosedY_reverse_sum_eq_one]
    ring
  have hterm :
      (∑ j : Item n, v t * gap j) ≤
        ∑ j : Item n, v j * gap j := by
    refine Finset.sum_le_sum ?_
    intro j _hj
    by_cases hjlt : j.val < t.val
    · have hv : v t ≤ v j := (hdec hjlt).le
      exact mul_le_mul_of_nonneg_right hv (hleft j hjlt)
    · by_cases heq : j = t
      · subst j
        exact le_rfl
      · have hgt : t.val < j.val := by
          have hne_val : j.val ≠ t.val := by
            intro hval
            exact heq (Fin.ext hval)
          omega
        have hv : v j ≤ v t := (hdec hgt).le
        have hgap_nonpos : gap j ≤ 0 := by
          unfold gap
          rw [problem6ClosedX_after alpha v hgt]
          linarith [hy_nonneg j]
        exact mul_le_mul_of_nonpos_right hv hgap_nonpos
  have hweighted_nonneg :
      0 ≤ ∑ j : Item n, v j * gap j := by
    have hconst :
        (∑ j : Item n, v t * gap j) = 0 := by
      rw [← Finset.mul_sum, hgap_sum, mul_zero]
    linarith
  have hraw :=
    problem6ClosedRawUtility_sub_eq_mirror_gap_sum alpha v t
  unfold gap at hweighted_nonneg
  linarith

/--
Appendix D, Lemma 6 comparison specialized to `α ≤ 1/2`: the scalar
mirror-gap algebra supplies all pre-pivot gaps; the pivot gap is left explicit.
-/
theorem problem6ClosedTypeOneRawUtility_le_typeZeroRawUtility_of_alpha_le_half
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha_half : alpha ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hpivot : Problem6ClosedNonnegativePivots alpha v t)
    (hmirror :
      ∀ j : Item n, j.val < t.val → t.val < (reverseItem j).val)
    (hpivot_gap :
      0 ≤ problem6ClosedX alpha v t t -
        problem6ClosedY alpha v t (reverseItem t)) :
    problem6ClosedTypeOneRawUtility alpha v t ≤
      problem6ClosedTypeZeroRawUtility alpha v t := by
  refine problem6ClosedTypeOneRawUtility_le_typeZeroRawUtility_of_left_gaps
    hdec ?_ ?_
  · intro j hjle
    by_cases hj : j = t
    · subst j
      exact hpivot_gap
    · have hjlt : j.val < t.val := by
        have hne_val : j.val ≠ t.val := by
          intro hval
          exact hj (Fin.ext hval)
        omega
      exact problem6ClosedX_sub_closedY_reverse_nonneg_of_alpha_le_half
        halpha0 halpha1 halpha_half hpos hjlt (hmirror j hjlt)
  · intro j
    exact problem6ClosedY_nonneg halpha0 halpha1 hpos hpivot (reverseItem j)

/--
Appendix D, Lemma 6 comparison specialized to `α ≤ 1/2`, following the
paper's strict pre-pivot summation argument.  Once the pivot is at or before
its mirror, no separate pivot-gap obligation is needed.
-/
theorem problem6ClosedTypeOneRawUtility_le_typeZeroRawUtility_of_alpha_le_half_of_pivot_le_reverse
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha_half : alpha ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hpivot : Problem6ClosedNonnegativePivots alpha v t)
    (hcenter : t.val ≤ (reverseItem t).val) :
    problem6ClosedTypeOneRawUtility alpha v t ≤
      problem6ClosedTypeZeroRawUtility alpha v t := by
  refine problem6ClosedTypeOneRawUtility_le_typeZeroRawUtility_of_strict_left_gaps
    hdec ?_ ?_
  · intro j hj
    exact problem6ClosedX_sub_closedY_reverse_nonneg_of_alpha_le_half
      halpha0 halpha1 halpha_half hpos hj
      (reverseItem_after_pivot_of_before_pivot_of_pivot_le_reverse
        hcenter hj)
  · intro j
    exact problem6ClosedY_nonneg halpha0 halpha1 hpos hpivot (reverseItem j)

/-- Closed-form policy type-0 raw utility equals the closed `x` raw utility. -/
theorem problem6ClosedPolicy_rawTypeUtility_zero_eq {n : ℕ}
    {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hpivot : Problem6ClosedNonnegativePivots alpha v t) :
    TypeWeightedRecommendationModel.rawTypeUtility
      (twoTypeReducedModel alpha v)
      (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot) 0 =
      problem6ClosedTypeZeroRawUtility alpha v t := by
  unfold TypeWeightedRecommendationModel.rawTypeUtility
    AppliedModelingLib.Policy.agentScore AppliedModelingLib.pmfExp
    problem6ClosedTypeZeroRawUtility
  refine Finset.sum_congr rfl ?_
  intro j _hj
  rw [problem6ClosedPolicy_zero_toReal halpha0 halpha1 hpos hpivot]
  simp
  ring

/-- Closed-form policy type-1 raw utility equals the closed `y` raw utility. -/
theorem problem6ClosedPolicy_rawTypeUtility_one_eq {n : ℕ}
    {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hpivot : Problem6ClosedNonnegativePivots alpha v t) :
    TypeWeightedRecommendationModel.rawTypeUtility
      (twoTypeReducedModel alpha v)
      (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot) 1 =
      problem6ClosedTypeOneRawUtility alpha v t := by
  unfold TypeWeightedRecommendationModel.rawTypeUtility
    AppliedModelingLib.Policy.agentScore AppliedModelingLib.pmfExp
    problem6ClosedTypeOneRawUtility
  refine Finset.sum_congr rfl ?_
  intro j _hj
  rw [problem6ClosedPolicy_one_toReal halpha0 halpha1 hpos hpivot]
  simp
  ring

/--
The closed-form type-1 raw utility expansion used in Theorem 3:
the tail is written as a positive correction above the pivot mirror value.
-/
theorem problem6ClosedTypeOneRawUtility_eq_pivot_add_tail {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) (t : Item n) :
    problem6ClosedTypeOneRawUtility alpha v t =
      v (reverseItem t) +
        ∑ j : Item n,
          if t.val < j.val then
            problem6ClosedValue alpha v t / (1 - pairShare alpha v j) *
              (v (reverseItem j) - v (reverseItem t))
          else 0 := by
  unfold problem6ClosedTypeOneRawUtility
  have hdecomp :
      (∑ j : Item n, v (reverseItem j) * problem6ClosedY alpha v t j) =
        (∑ j : Item n,
          v (reverseItem t) * problem6ClosedY alpha v t j) +
        (∑ j : Item n,
          (v (reverseItem j) - v (reverseItem t)) *
            problem6ClosedY alpha v t j) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro j _hj
    ring
  rw [hdecomp]
  have hfirst :
      (∑ j : Item n,
          v (reverseItem t) * problem6ClosedY alpha v t j) =
        v (reverseItem t) := by
    rw [← Finset.mul_sum, problem6ClosedY_sum_eq_one]
    ring
  rw [hfirst]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro j _hj
  by_cases htj : t.val < j.val
  · rw [if_pos htj, problem6ClosedY_after alpha v htj]
    ring
  · rw [if_neg htj]
    by_cases hjt : j.val < t.val
    · rw [problem6ClosedY_before alpha v hjt]
      ring
    · have hval : j.val = t.val := by omega
      have hjeq : j = t := Fin.ext hval
      subst j
      ring

theorem problem6ClosedTypeOneRawUtility_eq_pivot_add_value_mul_gap_sum {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) (t : Item n) :
    problem6ClosedTypeOneRawUtility alpha v t =
      v (reverseItem t) +
        problem6ClosedValue alpha v t *
          (∑ j : Item n, if t.val < j.val then
            (v (reverseItem j) - v (reverseItem t)) /
              (1 - pairShare alpha v j) else 0) := by
  rw [problem6ClosedTypeOneRawUtility_eq_pivot_add_tail]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro j _hj
  by_cases htj : t.val < j.val
  · simp [htj, div_eq_mul_inv]
    ring
  · simp [htj]

theorem problem6TypeOneDual_objective_eq_closedTypeOneRawUtility {n : ℕ}
    [NeZero n] {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j) :
    problem6TypeOneDualRowZero alpha v t +
        problem6TypeOneDualRowOne alpha v -
      problem6ClosedValue alpha v t *
        (∑ j : Item n, problem6TypeOneDualWeight alpha v t j) =
      problem6ClosedTypeOneRawUtility alpha v t := by
  let A : ℝ := problem6TypeOneDualRowZero alpha v t
  let B : ℝ := problem6TypeOneDualRowOne alpha v
  let b : ℝ := v (reverseItem t)
  let q : ℝ := pairShare alpha v t
  let lam : ℝ := problem6ClosedValue alpha v t
  let L : ℝ := problem6LeftSum alpha v t
  let R : ℝ := problem6RightSum alpha v t
  let T : ℝ :=
    ∑ j : Item n, if t.val < j.val then
      (problem6TypeOneDualRowOne alpha v - v (reverseItem j)) /
        (1 - pairShare alpha v j) else 0
  let G : ℝ :=
    ∑ j : Item n, if t.val < j.val then
      (v (reverseItem j) - v (reverseItem t)) /
        (1 - pairShare alpha v j) else 0
  have hsum :
      (∑ j : Item n, problem6TypeOneDualWeight alpha v t j) =
        A * L + A / q + T := by
    simpa [A, q, L, T, add_assoc] using
      (problem6TypeOneDualWeight_sum_eq (alpha := alpha) (v := v) (t := t))
  have hraw :
      problem6ClosedTypeOneRawUtility alpha v t = b + lam * G := by
    simpa [b, lam, G] using
      (problem6ClosedTypeOneRawUtility_eq_pivot_add_value_mul_gap_sum
        alpha v t)
  have htail : T + G = (B - b) * R := by
    simpa [B, b, R, T, G] using
      (problem6TypeOneDual_tail_sum_add_closed_gap_sum_eq
        (alpha := alpha) (v := v) (t := t))
  have hA : A = q * (B - b) / (1 - q) := by
    rfl
  have hDpos : 0 < problem6ClosedDenominator alpha v t :=
    problem6ClosedDenominator_pos t halpha0 halpha1 hpos
  have hDmul :
      lam * (1 + q * L + (1 - q) * R) = 1 := by
    have hDmul0 :
        problem6ClosedValue alpha v t *
            problem6ClosedDenominator alpha v t = 1 := by
      unfold problem6ClosedValue
      field_simp [ne_of_gt hDpos]
    simpa [lam, q, L, R, problem6ClosedDenominator] using hDmul0
  have hq_ne : q ≠ 0 := by
    exact ne_of_gt (by simpa [q] using pairShare_pos t halpha0 halpha1 hpos)
  have h1q_ne : 1 - q ≠ 0 := by
    exact ne_of_gt
      (by simpa [q] using one_sub_pairShare_pos t halpha0 halpha1 hpos)
  rw [hsum, hraw]
  change A + B - lam * (A * L + A / q + T) = b + lam * G
  have htail_sub : T = (B - b) * R - G := by
    linarith
  rw [hA, htail_sub]
  have hfactor :
      lam * (q * L / (1 - q) + 1 / (1 - q) + R) =
        1 / (1 - q) := by
    field_simp [h1q_ne]
    ring_nf at hDmul ⊢
    nlinarith
  have hqcancel :
      q * (B - b) / (1 - q) / q = (B - b) / (1 - q) := by
    field_simp [hq_ne]
  rw [hqcancel]
  calc
    q * (B - b) / (1 - q) + B -
        lam * (q * (B - b) / (1 - q) * L +
          (B - b) / (1 - q) + ((B - b) * R - G)) =
      b + lam * G + (B - b) *
        (1 / (1 - q) -
          lam * (q * L / (1 - q) + 1 / (1 - q) + R)) := by
        field_simp [h1q_ne]
        ring
    _ = b + lam * G := by
        rw [hfactor]
        ring

theorem problem6TypeOneRawUtilityDualCertificate_closedTypeOneRawUtility
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v) :
    Problem6TypeOneRawUtilityDualCertificate
      alpha v (problem6ClosedValue alpha v t)
      (problem6ClosedTypeOneRawUtility alpha v t)
      (problem6TypeOneDualRowZero alpha v t)
      (problem6TypeOneDualRowOne alpha v)
      (problem6TypeOneDualWeight alpha v t) where
  itemWeight_nonneg :=
    problem6TypeOneDualWeight_nonneg halpha0 halpha1 hpos
  typeZero_coeff_nonneg :=
    problem6TypeOneDual_typeZero_coeff_nonneg
      halpha0 halpha1 hpos hdec
  typeOne_coeff_upper :=
    problem6TypeOneDual_typeOne_coeff_upper
      halpha0 halpha1 hpos hdec
  objective_bound := by
    rw [problem6TypeOneDual_objective_eq_closedTypeOneRawUtility
      halpha0 halpha1 hpos]

theorem problem6_typeOneRawUtility_le_closedTypeOneRawUtility_of_closedValue_feasible
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (ρ : TypePolicy 2 n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hfeas :
      problem6LPFeasible alpha v ρ (problem6ClosedValue alpha v t)) :
    TypeWeightedRecommendationModel.rawTypeUtility
        (twoTypeReducedModel alpha v) ρ 1 ≤
      problem6ClosedTypeOneRawUtility alpha v t := by
  exact problem6_typeOneRawUtility_le_of_dualCertificate ρ hfeas
    (problem6TypeOneRawUtilityDualCertificate_closedTypeOneRawUtility
      halpha0 halpha1 hpos hdec)

/--
The normalized type-1 utility of the closed policy in the displayed Theorem 3
form, with the common best-item denominator left explicit.
-/
theorem problem6ClosedPolicy_normalizedTypeUtility_one_eq_pivot_add_tail
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hpivot : Problem6ClosedNonnegativePivots alpha v t) :
    TypeWeightedRecommendationModel.normalizedTypeUtility
        (twoTypeReducedModel alpha v)
        (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot) 1 =
      (v (reverseItem t) +
        ∑ j : Item n,
          if t.val < j.val then
            problem6ClosedValue alpha v t / (1 - pairShare alpha v j) *
              (v (reverseItem j) - v (reverseItem t))
          else 0) /
        TypeWeightedRecommendationModel.bestItemUtility
          (twoTypeReducedModel alpha v) 1 := by
  unfold TypeWeightedRecommendationModel.normalizedTypeUtility
  rw [problem6ClosedPolicy_rawTypeUtility_one_eq halpha0 halpha1 hpos hpivot,
    problem6ClosedTypeOneRawUtility_eq_pivot_add_tail]

/--
Theorem 3 tail-gap positivity: if `j` is after the selected pivot, then the
mirror value of `j` is strictly above the mirror value of the pivot.
-/
theorem theorem3_tailGap_pos_of_pivot_lt
    {n : ℕ} {v : Item n → ℝ} {t j : Item n}
    (hdec : StrictlyDecreasingByIndex v)
    (htj : t.val < j.val) :
    0 < v (reverseItem j) - v (reverseItem t) := by
  have hrev : (reverseItem j).val < (reverseItem t).val :=
    reverseItem_val_lt_of_val_lt htj
  have hv : v (reverseItem t) < v (reverseItem j) :=
    hdec hrev
  linarith

/--
The reciprocal tail factor `1 / (1-q_j(α))` is increasing in `α`.
-/
theorem one_sub_pairShare_inv_mono_alpha
    {n : ℕ} {alpha alpha' : ℝ} {v : Item n → ℝ} (j : Item n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (hpos : ∀ l : Item n, 0 < v l) :
    (1 - pairShare alpha v j)⁻¹ ≤
      (1 - pairShare alpha' v j)⁻¹ := by
  have hq_le : pairShare alpha v j ≤ pairShare alpha' v j := by
    rcases lt_or_eq_of_le halpha_le with hlt | heq
    · exact (pairShare_strictMono_alpha j
        halpha0 halpha1 halpha0' halpha1' hlt hpos).le
    · subst alpha'
      exact le_rfl
  have hden_le :
      1 - pairShare alpha' v j ≤ 1 - pairShare alpha v j := by
    linarith
  have h :=
    one_div_le_one_div_of_le
      (one_sub_pairShare_pos j halpha0' halpha1' hpos)
      hden_le
  simpa [one_div] using h

/-- The reciprocal `q_j(α)⁻¹` is strictly decreasing in `α`. -/
theorem pairShare_inv_strictAnti_alpha
    {n : ℕ} {alpha alpha' : ℝ} {v : Item n → ℝ} (j : Item n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_lt : alpha < alpha')
    (hpos : ∀ l : Item n, 0 < v l) :
    (pairShare alpha' v j)⁻¹ < (pairShare alpha v j)⁻¹ := by
  have hq_lt :
      pairShare alpha v j < pairShare alpha' v j :=
    pairShare_strictMono_alpha j
      halpha0 halpha1 halpha0' halpha1' halpha_lt hpos
  exact inv_strictAnti₀ (pairShare_pos j halpha0 halpha1 hpos) hq_lt

/-- The reciprocal tail factor `1/(1-q_j(α))` is strictly increasing in `α`. -/
theorem one_sub_pairShare_inv_strictMono_alpha
    {n : ℕ} {alpha alpha' : ℝ} {v : Item n → ℝ} (j : Item n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_lt : alpha < alpha')
    (hpos : ∀ l : Item n, 0 < v l) :
    (1 - pairShare alpha v j)⁻¹ <
      (1 - pairShare alpha' v j)⁻¹ := by
  have hq_lt :
      pairShare alpha v j < pairShare alpha' v j :=
    pairShare_strictMono_alpha j
      halpha0 halpha1 halpha0' halpha1' halpha_lt hpos
  have hden_lt :
      1 - pairShare alpha' v j < 1 - pairShare alpha v j := by
    linarith
  exact inv_strictAnti₀
    (one_sub_pairShare_pos j halpha0' halpha1' hpos) hden_lt

/-- Fixed-pivot left inverse sum is weakly decreasing in `α`. -/
theorem problem6LeftSum_antitone_alpha
    {n : ℕ} {alpha alpha' : ℝ} {v : Item n → ℝ} (t : Item n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (hpos : ∀ j : Item n, 0 < v j) :
    problem6LeftSum alpha' v t ≤ problem6LeftSum alpha v t := by
  unfold problem6LeftSum
  refine Finset.sum_le_sum ?_
  intro j _hj
  by_cases hlt : j.val < t.val
  · simp [hlt, pairShare_inv_antitone_alpha j
      halpha0 halpha1 halpha0' halpha1' halpha_le hpos]
  · simp [hlt]

/-- Fixed-pivot right inverse-complement sum is weakly increasing in `α`. -/
theorem problem6RightSum_mono_alpha
    {n : ℕ} {alpha alpha' : ℝ} {v : Item n → ℝ} (t : Item n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (hpos : ∀ j : Item n, 0 < v j) :
    problem6RightSum alpha v t ≤ problem6RightSum alpha' v t := by
  unfold problem6RightSum
  refine Finset.sum_le_sum ?_
  intro j _hj
  by_cases hlt : t.val < j.val
  · simp [hlt, one_sub_pairShare_inv_mono_alpha j
      halpha0 halpha1 halpha0' halpha1' halpha_le hpos]
  · simp [hlt]

/-- The fixed-pivot crossing gap `L_t - R_t` is weakly decreasing in `α`. -/
theorem problem6PivotGap_antitone_alpha
    {n : ℕ} {alpha alpha' : ℝ} {v : Item n → ℝ} (t : Item n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (hpos : ∀ j : Item n, 0 < v j) :
    problem6PivotGap alpha' v t ≤ problem6PivotGap alpha v t := by
  have hL :=
    problem6LeftSum_antitone_alpha t
      halpha0 halpha1 halpha0' halpha1' halpha_le hpos
  have hR :=
    problem6RightSum_mono_alpha t
      halpha0 halpha1 halpha0' halpha1' halpha_le hpos
  unfold problem6PivotGap
  linarith

/-- The lower-crossing boundary gap is strictly decreasing in `α`. -/
theorem problem6BoundaryGap_strictAnti_alpha
    {n : ℕ} {alpha alpha' : ℝ} {v : Item n → ℝ} (t : Item n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_lt : alpha < alpha')
    (hpos : ∀ j : Item n, 0 < v j) :
    problem6BoundaryGap alpha' v t <
      problem6BoundaryGap alpha v t := by
  have halpha_le : alpha ≤ alpha' := le_of_lt halpha_lt
  have hL :=
    problem6LeftSum_antitone_alpha t
      halpha0 halpha1 halpha0' halpha1' halpha_le hpos
  have hR :=
    problem6RightSum_mono_alpha t
      halpha0 halpha1 halpha0' halpha1' halpha_le hpos
  have hinv :=
    pairShare_inv_strictAnti_alpha t
      halpha0 halpha1 halpha0' halpha1' halpha_lt hpos
  unfold problem6BoundaryGap problem6PivotGap
  linarith

/-- The lower crossing threshold `-q_t(α)⁻¹` is weakly increasing in `α`. -/
theorem problem6PivotGap_lowerThreshold_mono_alpha
    {n : ℕ} {alpha alpha' : ℝ} {v : Item n → ℝ} (t : Item n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (hpos : ∀ j : Item n, 0 < v j) :
    - (pairShare alpha v t)⁻¹ ≤ - (pairShare alpha' v t)⁻¹ := by
  have hinv :=
    pairShare_inv_antitone_alpha t
      halpha0 halpha1 halpha0' halpha1' halpha_le hpos
  linarith

/--
Fixed-pivot crossing persistence backward in `α`: if pivot `t` has crossed the
lower gap threshold at the larger `α'`, then it has also crossed at the smaller
`α`.
-/
theorem problem6PivotGap_lower_crossing_of_alpha_le
    {n : ℕ} {alpha alpha' : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (hpos : ∀ j : Item n, 0 < v j)
    (hcross' :
      - (pairShare alpha' v t)⁻¹ ≤ problem6PivotGap alpha' v t) :
    - (pairShare alpha v t)⁻¹ ≤ problem6PivotGap alpha v t := by
  have hlower :=
    problem6PivotGap_lowerThreshold_mono_alpha t
      halpha0 halpha1 halpha0' halpha1' halpha_le hpos
  have hgap :=
    problem6PivotGap_antitone_alpha t
      halpha0 halpha1 halpha0' halpha1' halpha_le hpos
  linarith

/-- The finite set of pivots whose lower crossing inequality holds. -/
noncomputable def problem6PivotCrossingSet {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) : Finset (Item n) :=
  Finset.univ.filter
    (fun t : Item n =>
      - (pairShare alpha v t)⁻¹ ≤ problem6PivotGap alpha v t)

/-- The lower crossing set is nonempty: the last item always belongs to it. -/
theorem problem6PivotCrossingSet_nonempty {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j) :
    (problem6PivotCrossingSet alpha v).Nonempty := by
  classical
  have hnpos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  let last : Item n := ⟨n - 1, by omega⟩
  have hlast_lower :
      - (pairShare alpha v last)⁻¹ ≤ problem6PivotGap alpha v last := by
    have hRzero : problem6RightSum alpha v last = 0 := by
      unfold problem6RightSum
      refine Finset.sum_eq_zero ?_
      intro j _hj
      have hnlt : ¬ last.val < j.val := by
        change ¬ n - 1 < j.val
        omega
      simp [hnlt]
    have hLnonneg :
        0 ≤ problem6LeftSum alpha v last :=
      problem6LeftSum_nonneg last halpha0 halpha1 hpos
    have hqinv_nonneg :
        0 ≤ (pairShare alpha v last)⁻¹ :=
      inv_nonneg.mpr (pairShare_pos last halpha0 halpha1 hpos).le
    unfold problem6PivotGap
    rw [hRzero]
    nlinarith
  exact ⟨last, by simp [problem6PivotCrossingSet, hlast_lower]⟩

/-- The canonical Lemma 5 pivot: the first item satisfying the lower crossing inequality. -/
noncomputable def problem6FirstClosedPivot {n : ℕ} [NeZero n]
    (alpha : ℝ) (v : Item n → ℝ)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j) : Item n :=
  Classical.choose
    (Finset.exists_min_image (problem6PivotCrossingSet alpha v)
      (fun t : Item n => t.val)
      (problem6PivotCrossingSet_nonempty
        (alpha := alpha) (v := v) halpha0 halpha1 hpos))

theorem problem6FirstClosedPivot_mem_crossingSet {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j) :
    problem6FirstClosedPivot alpha v halpha0 halpha1 hpos ∈
      problem6PivotCrossingSet alpha v := by
  exact (Classical.choose_spec
    (Finset.exists_min_image (problem6PivotCrossingSet alpha v)
      (fun t : Item n => t.val)
      (problem6PivotCrossingSet_nonempty
        (alpha := alpha) (v := v) halpha0 halpha1 hpos))).1

theorem problem6FirstClosedPivot_lower_crossing {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j) :
    - (pairShare alpha v
        (problem6FirstClosedPivot alpha v halpha0 halpha1 hpos))⁻¹ ≤
      problem6PivotGap alpha v
        (problem6FirstClosedPivot alpha v halpha0 halpha1 hpos) := by
  have hmem :=
    problem6FirstClosedPivot_mem_crossingSet
      (alpha := alpha) (v := v) halpha0 halpha1 hpos
  simpa [problem6PivotCrossingSet] using hmem

theorem problem6FirstClosedPivot_min {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    {u : Item n} (hu : u ∈ problem6PivotCrossingSet alpha v) :
    (problem6FirstClosedPivot alpha v halpha0 halpha1 hpos).val ≤ u.val := by
  exact (Classical.choose_spec
    (Finset.exists_min_image (problem6PivotCrossingSet alpha v)
      (fun t : Item n => t.val)
      (problem6PivotCrossingSet_nonempty
        (alpha := alpha) (v := v) halpha0 halpha1 hpos))).2 u hu

/--
Any pivot satisfying Lemma 5's denominator bounds lies weakly after the
canonical first crossing pivot.
-/
theorem problem6FirstClosedPivot_le_of_closedPivotDenominatorBounds
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hbounds : Problem6ClosedPivotDenominatorBounds alpha v t) :
    (problem6FirstClosedPivot alpha v halpha0 halpha1 hpos).val ≤ t.val := by
  have hlower :
      - (pairShare alpha v t)⁻¹ ≤ problem6PivotGap alpha v t :=
    problem6PivotGap_lower_bound_of_closedPivotDenominatorBounds
      halpha0 halpha1 hpos hbounds
  have hmem : t ∈ problem6PivotCrossingSet alpha v := by
    simp [problem6PivotCrossingSet, hlower]
  exact problem6FirstClosedPivot_min
    (alpha := alpha) (v := v) halpha0 halpha1 hpos hmem

/--
The first closed pivot satisfies Lemma 5's denominator bounds.
-/
theorem problem6FirstClosedPivot_denominatorBounds {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j) :
    Problem6ClosedPivotDenominatorBounds alpha v
      (problem6FirstClosedPivot alpha v halpha0 halpha1 hpos) := by
  let t : Item n := problem6FirstClosedPivot alpha v halpha0 halpha1 hpos
  have hlower :
      - (pairShare alpha v t)⁻¹ ≤ problem6PivotGap alpha v t := by
    dsimp [t]
    exact problem6FirstClosedPivot_lower_crossing
      (alpha := alpha) (v := v) halpha0 halpha1 hpos
  have hupper :
      problem6PivotGap alpha v t ≤
        (1 - pairShare alpha v t)⁻¹ := by
    by_cases ht0 : t.val = 0
    · have hLzero : problem6LeftSum alpha v t = 0 := by
        unfold problem6LeftSum
        refine Finset.sum_eq_zero ?_
        intro j _hj
        have hnlt : ¬ j.val < t.val := by omega
        simp [hnlt]
      have hRnonneg :
          0 ≤ problem6RightSum alpha v t :=
        problem6RightSum_nonneg t halpha0 halpha1 hpos
      have hcomp_inv_nonneg :
          0 ≤ (1 - pairShare alpha v t)⁻¹ :=
        inv_nonneg.mpr
          (one_sub_pairShare_pos t halpha0 halpha1 hpos).le
      unfold problem6PivotGap
      rw [hLzero]
      nlinarith
    · have htpos : 0 < t.val := Nat.pos_of_ne_zero ht0
      let p : Item n := ⟨t.val - 1, by omega⟩
      have hpnext : t.val = p.val + 1 := by
        dsimp [p]
        omega
      have hp_not :
          ¬ (- (pairShare alpha v p)⁻¹ ≤
              problem6PivotGap alpha v p) := by
        intro hp
        have hp_mem : p ∈ problem6PivotCrossingSet alpha v := by
          simp [problem6PivotCrossingSet, hp]
        have hmin :=
          problem6FirstClosedPivot_min
            (alpha := alpha) (v := v)
            halpha0 halpha1 hpos hp_mem
        dsimp [t, p] at hmin
        omega
      have hp_lt :
          problem6PivotGap alpha v p <
            - (pairShare alpha v p)⁻¹ :=
        not_le.mp hp_not
      have hgap_eq :=
        problem6PivotGap_next_eq
          (alpha := alpha) (v := v) (t := p) (u := t) hpnext
      have hupper_lt :
          problem6PivotGap alpha v t <
            (1 - pairShare alpha v t)⁻¹ := by
        rw [hgap_eq]
        nlinarith
      exact le_of_lt hupper_lt
  exact problem6ClosedPivotDenominatorBounds_of_pivotGap_bounds
    halpha0 halpha1 hpos hlower hupper

/--
Canonical Lemma 5 closed-form policy using the first closed pivot.  This
convenience definition keeps paper-facing Theorem 3 statements from exposing
the denominator-bound proof object.
-/
noncomputable def problem6FirstClosedPolicy {n : ℕ} [NeZero n]
    (alpha : ℝ) (v : Item n → ℝ)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j) : TypePolicy 2 n :=
  let t : Item n := problem6FirstClosedPivot alpha v halpha0 halpha1 hpos
  let hpivot : Problem6ClosedNonnegativePivots alpha v t :=
    problem6ClosedNonnegativePivots_of_denominatorBounds
      halpha0 halpha1 hpos
      (problem6FirstClosedPivot_denominatorBounds
        (alpha := alpha) (v := v) halpha0 halpha1 hpos)
  problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot

/--
Unfold the canonical first-closed policy at a supplied proof of the first
closed pivot.  The proof is extensional because the policy coordinates do not
depend on the particular denominator-bound certificate.
-/
theorem problem6FirstClosedPolicy_eq_closedPolicy_of_firstClosedPivot_eq
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hpivot_eq :
      problem6FirstClosedPivot alpha v halpha0 halpha1 hpos = t) :
    problem6FirstClosedPolicy alpha v halpha0 halpha1 hpos =
      problem6ClosedPolicy alpha v t halpha0 halpha1 hpos
        (problem6ClosedNonnegativePivots_of_denominatorBounds
          halpha0 halpha1 hpos
          (by
            simpa [hpivot_eq] using
              problem6FirstClosedPivot_denominatorBounds
                (alpha := alpha) (v := v) halpha0 halpha1 hpos)) := by
  unfold problem6FirstClosedPolicy
  funext k
  fin_cases k
  · apply pmf_eq_of_forall_toReal_eq
    intro j
    simp [hpivot_eq]
  · apply pmf_eq_of_forall_toReal_eq
    intro j
    simp [hpivot_eq]

/--
The canonical first closed pivot is monotone in `α`: as the first type's
weight increases, the first crossing index can only move to the right.
-/
theorem problem6FirstClosedPivot_mono_alpha {n : ℕ} [NeZero n]
    {alpha alpha' : ℝ} {v : Item n → ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (hpos : ∀ j : Item n, 0 < v j) :
    (problem6FirstClosedPivot alpha v halpha0 halpha1 hpos).val ≤
      (problem6FirstClosedPivot alpha' v halpha0' halpha1' hpos).val := by
  let t' : Item n :=
    problem6FirstClosedPivot alpha' v halpha0' halpha1' hpos
  have hcross' :
      - (pairShare alpha' v t')⁻¹ ≤ problem6PivotGap alpha' v t' := by
    dsimp [t']
    exact problem6FirstClosedPivot_lower_crossing
      (alpha := alpha') (v := v) halpha0' halpha1' hpos
  have hcross :
      - (pairShare alpha v t')⁻¹ ≤ problem6PivotGap alpha v t' :=
    problem6PivotGap_lower_crossing_of_alpha_le
      halpha0 halpha1 halpha0' halpha1' halpha_le hpos hcross'
  have ht'_mem : t' ∈ problem6PivotCrossingSet alpha v := by
    simp [problem6PivotCrossingSet, hcross]
  exact problem6FirstClosedPivot_min
    (alpha := alpha) (v := v) halpha0 halpha1 hpos ht'_mem

/--
Appendix D, Lemma 8 interval step for the canonical first pivot: if the
canonical first closed pivot agrees at two endpoint parameters, then it agrees
at every intermediate parameter.  This is the formal `A(t)`-is-an-interval
statement following from Lemma 7-style monotonicity.
-/
theorem lemma8_firstClosedPivot_eq_of_between_endpoints
    {n : ℕ} [NeZero n]
    {alphaLeft alpha alphaRight : ℝ} {v : Item n → ℝ}
    (halphaLeft0 : 0 < alphaLeft) (halphaLeft1 : alphaLeft < 1)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halphaRight0 : 0 < alphaRight) (halphaRight1 : alphaRight < 1)
    (hleft : alphaLeft ≤ alpha)
    (hright : alpha ≤ alphaRight)
    (hpos : ∀ j : Item n, 0 < v j)
    (hpivot :
      problem6FirstClosedPivot alphaLeft v halphaLeft0 halphaLeft1 hpos =
        problem6FirstClosedPivot alphaRight v
          halphaRight0 halphaRight1 hpos) :
    problem6FirstClosedPivot alpha v halpha0 halpha1 hpos =
      problem6FirstClosedPivot alphaLeft v halphaLeft0 halphaLeft1 hpos := by
  have hleft_mono :
      (problem6FirstClosedPivot alphaLeft v
          halphaLeft0 halphaLeft1 hpos).val ≤
        (problem6FirstClosedPivot alpha v halpha0 halpha1 hpos).val :=
    problem6FirstClosedPivot_mono_alpha
      halphaLeft0 halphaLeft1 halpha0 halpha1 hleft hpos
  have hright_mono :
      (problem6FirstClosedPivot alpha v halpha0 halpha1 hpos).val ≤
        (problem6FirstClosedPivot alphaLeft v
          halphaLeft0 halphaLeft1 hpos).val := by
    have hraw :
        (problem6FirstClosedPivot alpha v halpha0 halpha1 hpos).val ≤
          (problem6FirstClosedPivot alphaRight v
            halphaRight0 halphaRight1 hpos).val :=
      problem6FirstClosedPivot_mono_alpha
        halpha0 halpha1 halphaRight0 halphaRight1 hright hpos
    simpa [hpivot] using hraw
  exact Fin.ext (le_antisymm hright_mono hleft_mono)

/--
The canonical `A(t)` set from Appendix D, Lemma 8: parameters whose canonical
first closed pivot is `t`.
-/
def problem6FirstClosedPivotRegion {n : ℕ} [NeZero n]
    (v : Item n → ℝ) (hpos : ∀ j : Item n, 0 < v j)
    (t : Item n) : Set ℝ :=
  { alpha | ∃ (halpha0 : 0 < alpha) (halpha1 : alpha < 1),
      problem6FirstClosedPivot alpha v halpha0 halpha1 hpos = t }

/-- Every interior parameter belongs to the region of its canonical first pivot. -/
theorem problem6FirstClosedPivotRegion_mem {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j) :
    alpha ∈
      problem6FirstClosedPivotRegion v hpos
        (problem6FirstClosedPivot alpha v halpha0 halpha1 hpos) := by
  exact ⟨halpha0, halpha1, rfl⟩

/-- The canonical regions cover the open interval `(0,1)`. -/
theorem problem6FirstClosedPivotRegion_cover {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j) :
    ∃ t : Item n, alpha ∈ problem6FirstClosedPivotRegion v hpos t := by
  exact ⟨problem6FirstClosedPivot alpha v halpha0 halpha1 hpos,
    problem6FirstClosedPivotRegion_mem halpha0 halpha1 hpos⟩

/-- A parameter belongs to at most one canonical first-pivot region. -/
theorem problem6FirstClosedPivotRegion_unique {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {t u : Item n}
    (hpos : ∀ j : Item n, 0 < v j)
    (ht : alpha ∈ problem6FirstClosedPivotRegion v hpos t)
    (hu : alpha ∈ problem6FirstClosedPivotRegion v hpos u) :
    t = u := by
  rcases ht with ⟨halpha0, halpha1, ht⟩
  rcases hu with ⟨halpha0', halpha1', hu⟩
  have hsame :
      problem6FirstClosedPivot alpha v halpha0 halpha1 hpos =
        problem6FirstClosedPivot alpha v halpha0' halpha1' hpos := by
    congr
  exact ht.symm.trans (hsame.trans hu)

/--
The canonical `A(t)` sets are intervals: if two endpoints have canonical first
pivot `t`, then every intermediate parameter has canonical first pivot `t`.
-/
theorem problem6FirstClosedPivotRegion_interval {n : ℕ} [NeZero n]
    {alphaLeft alpha alphaRight : ℝ} {v : Item n → ℝ} {t : Item n}
    (hpos : ∀ j : Item n, 0 < v j)
    (hLeft : alphaLeft ∈ problem6FirstClosedPivotRegion v hpos t)
    (hRight : alphaRight ∈ problem6FirstClosedPivotRegion v hpos t)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hleft : alphaLeft ≤ alpha)
    (hright : alpha ≤ alphaRight) :
    alpha ∈ problem6FirstClosedPivotRegion v hpos t := by
  rcases hLeft with ⟨halphaLeft0, halphaLeft1, hpivotLeft⟩
  rcases hRight with ⟨halphaRight0, halphaRight1, hpivotRight⟩
  have hpivot_end :
      problem6FirstClosedPivot alphaLeft v
          halphaLeft0 halphaLeft1 hpos =
        problem6FirstClosedPivot alphaRight v
          halphaRight0 halphaRight1 hpos :=
    hpivotLeft.trans hpivotRight.symm
  have hpivot_mid :=
    lemma8_firstClosedPivot_eq_of_between_endpoints
      halphaLeft0 halphaLeft1 halpha0 halpha1
      halphaRight0 halphaRight1 hleft hright hpos hpivot_end
  exact ⟨halpha0, halpha1, hpivot_mid.trans hpivotLeft⟩

/--
The canonical first-pivot regions are consecutive in item order: moving to a
larger `α` can only move to the same or a later region.
-/
theorem problem6FirstClosedPivotRegion_order {n : ℕ} [NeZero n]
    {alpha beta : ℝ} {v : Item n → ℝ} {t u : Item n}
    (hpos : ∀ j : Item n, 0 < v j)
    (halpha : alpha ∈ problem6FirstClosedPivotRegion v hpos t)
    (hbeta : beta ∈ problem6FirstClosedPivotRegion v hpos u)
    (hle : alpha ≤ beta) :
    t.val ≤ u.val := by
  rcases halpha with ⟨halpha0, halpha1, ht⟩
  rcases hbeta with ⟨hbeta0, hbeta1, hu⟩
  have hmono :=
    problem6FirstClosedPivot_mono_alpha
      halpha0 halpha1 hbeta0 hbeta1 hle hpos
  simpa [ht, hu] using hmono

/--
Appendix D, Lemma 8 boundary-point existence for adjacent canonical
first-pivot intervals: if the canonical first closed pivot is `t` at the left
endpoint and the adjacent item `u = t+1` at the right endpoint, then the tight
lower-crossing boundary for `t` occurs between the two parameters.
-/
theorem problem6FirstClosedPivot_adjacentBoundary_exists
    {n : ℕ} [NeZero n]
    {alphaLeft alphaRight : ℝ} {v : Item n → ℝ} {t u : Item n}
    (halphaLeft0 : 0 < alphaLeft) (halphaLeft1 : alphaLeft < 1)
    (halphaRight0 : 0 < alphaRight) (halphaRight1 : alphaRight < 1)
    (hleft_le_right : alphaLeft ≤ alphaRight)
    (hpos : ∀ j : Item n, 0 < v j)
    (hleft_pivot :
      problem6FirstClosedPivot alphaLeft v
        halphaLeft0 halphaLeft1 hpos = t)
    (hright_pivot :
      problem6FirstClosedPivot alphaRight v
        halphaRight0 halphaRight1 hpos = u)
    (hnext : u.val = t.val + 1) :
    ∃ alphaBoundary : ℝ,
      alphaLeft ≤ alphaBoundary ∧ alphaBoundary ≤ alphaRight ∧
      0 < alphaBoundary ∧ alphaBoundary < 1 ∧
      problem6PivotGap alphaBoundary v t =
        - (pairShare alphaBoundary v t)⁻¹ := by
  have hcross_left :
      - (pairShare alphaLeft v t)⁻¹ ≤
        problem6PivotGap alphaLeft v t := by
    have h :=
      problem6FirstClosedPivot_lower_crossing
        (alpha := alphaLeft) (v := v)
        halphaLeft0 halphaLeft1 hpos
    simpa [hleft_pivot] using h
  have hnot_cross_right :
      ¬ - (pairShare alphaRight v t)⁻¹ ≤
        problem6PivotGap alphaRight v t := by
    intro hcross_right
    have ht_mem : t ∈ problem6PivotCrossingSet alphaRight v := by
      simp [problem6PivotCrossingSet, hcross_right]
    have hmin :=
      problem6FirstClosedPivot_min
        (alpha := alphaRight) (v := v)
        halphaRight0 halphaRight1 hpos ht_mem
    have hu_le_t : u.val ≤ t.val := by
      simpa [hright_pivot] using hmin
    omega
  exact
    problem6BoundaryGap_exists_zero_of_lower_crossing_changes
      halphaLeft0 halphaRight1 hleft_le_right hpos
      hcross_left hnot_cross_right

/--
If the first closed pivot is `t` at a left endpoint and the tight lower
boundary for `t` occurs later, then the canonical first closed pivot at the
boundary is still `t`.
-/
theorem problem6FirstClosedPivot_eq_of_left_pivot_and_boundary
    {n : ℕ} [NeZero n]
    {alphaLeft alphaBoundary : ℝ} {v : Item n → ℝ} {t : Item n}
    (halphaLeft0 : 0 < alphaLeft) (halphaLeft1 : alphaLeft < 1)
    (halphaBoundary0 : 0 < alphaBoundary)
    (halphaBoundary1 : alphaBoundary < 1)
    (hleft_le_boundary : alphaLeft ≤ alphaBoundary)
    (hpos : ∀ j : Item n, 0 < v j)
    (hleft_pivot :
      problem6FirstClosedPivot alphaLeft v
        halphaLeft0 halphaLeft1 hpos = t)
    (hboundary :
      problem6PivotGap alphaBoundary v t =
        - (pairShare alphaBoundary v t)⁻¹) :
    problem6FirstClosedPivot alphaBoundary v
      halphaBoundary0 halphaBoundary1 hpos = t := by
  have hmono :
      t.val ≤
        (problem6FirstClosedPivot alphaBoundary v
          halphaBoundary0 halphaBoundary1 hpos).val := by
    have h :=
      problem6FirstClosedPivot_mono_alpha
        halphaLeft0 halphaLeft1
        halphaBoundary0 halphaBoundary1
        hleft_le_boundary hpos
    simpa [hleft_pivot] using h
  have hcross_boundary :
      - (pairShare alphaBoundary v t)⁻¹ ≤
        problem6PivotGap alphaBoundary v t := by
    rw [hboundary]
  have ht_mem : t ∈ problem6PivotCrossingSet alphaBoundary v := by
    simp [problem6PivotCrossingSet, hcross_boundary]
  have hmin :
      (problem6FirstClosedPivot alphaBoundary v
        halphaBoundary0 halphaBoundary1 hpos).val ≤ t.val :=
    problem6FirstClosedPivot_min
      (alpha := alphaBoundary) (v := v)
      halphaBoundary0 halphaBoundary1 hpos ht_mem
  exact Fin.ext (le_antisymm hmin hmono)

/--
No-skip bridge for the canonical first closed pivot: if the canonical first
pivot moves from `t` to a later pivot beyond `t+1`, then some intermediate
parameter has canonical first pivot exactly `t+1`.
-/
theorem problem6FirstClosedPivot_successor_exists_of_pivot_jump
    {n : ℕ} [NeZero n]
    {alphaLeft alphaRight : ℝ} {v : Item n → ℝ} {t u : Item n}
    (halphaLeft0 : 0 < alphaLeft) (halphaLeft1 : alphaLeft < 1)
    (halphaRight0 : 0 < alphaRight) (halphaRight1 : alphaRight < 1)
    (hleft_le_right : alphaLeft ≤ alphaRight)
    (hpos : ∀ j : Item n, 0 < v j)
    (hleft_pivot :
      problem6FirstClosedPivot alphaLeft v
        halphaLeft0 halphaLeft1 hpos = t)
    (hright_pivot :
      problem6FirstClosedPivot alphaRight v
        halphaRight0 halphaRight1 hpos = u)
    (hskip : t.val + 1 < u.val) :
    ∃ (alphaMid : ℝ) (halphaMid0 : 0 < alphaMid)
      (halphaMid1 : alphaMid < 1) (s : Item n),
      alphaLeft ≤ alphaMid ∧ alphaMid ≤ alphaRight ∧
      s.val = t.val + 1 ∧
      problem6FirstClosedPivot alphaMid v
        halphaMid0 halphaMid1 hpos = s := by
  have hcross_left_t :
      - (pairShare alphaLeft v t)⁻¹ ≤
        problem6PivotGap alphaLeft v t := by
    have h :=
      problem6FirstClosedPivot_lower_crossing
        (alpha := alphaLeft) (v := v)
        halphaLeft0 halphaLeft1 hpos
    simpa [hleft_pivot] using h
  have hnot_cross_right_t :
      ¬ - (pairShare alphaRight v t)⁻¹ ≤
        problem6PivotGap alphaRight v t := by
    intro hcross_right
    have ht_mem : t ∈ problem6PivotCrossingSet alphaRight v := by
      simp [problem6PivotCrossingSet, hcross_right]
    have hmin :=
      problem6FirstClosedPivot_min
        (alpha := alphaRight) (v := v)
        halphaRight0 halphaRight1 hpos ht_mem
    have hu_le_t : u.val ≤ t.val := by
      simpa [hright_pivot] using hmin
    omega
  rcases problem6BoundaryGap_exists_zero_of_lower_crossing_changes
      halphaLeft0 halphaRight1 hleft_le_right hpos
      hcross_left_t hnot_cross_right_t with
    ⟨alphaBoundary, hleft_le_boundary, hboundary_le_right,
      halphaBoundary0, halphaBoundary1, hboundary_t⟩
  have hfirst_boundary_t :
      problem6FirstClosedPivot alphaBoundary v
        halphaBoundary0 halphaBoundary1 hpos = t :=
    problem6FirstClosedPivot_eq_of_left_pivot_and_boundary
      halphaLeft0 halphaLeft1
      halphaBoundary0 halphaBoundary1
      hleft_le_boundary hpos hleft_pivot hboundary_t
  let s : Item n := ⟨t.val + 1, by omega⟩
  have hs_val : s.val = t.val + 1 := rfl
  have hnext_s : s.val = t.val + 1 := rfl
  have hBs_boundary_pos :
      0 < problem6BoundaryGap alphaBoundary v s :=
    problem6BoundaryGap_next_pos_of_boundary
      halphaBoundary0 halphaBoundary1 hpos hnext_s hboundary_t
  have hcross_boundary_s :
      - (pairShare alphaBoundary v s)⁻¹ ≤
        problem6PivotGap alphaBoundary v s :=
    problem6BoundaryGap_nonneg_iff_lower_crossing.mp
      hBs_boundary_pos.le
  have hnot_cross_right_s :
      ¬ - (pairShare alphaRight v s)⁻¹ ≤
        problem6PivotGap alphaRight v s := by
    intro hcross_right
    have hs_mem : s ∈ problem6PivotCrossingSet alphaRight v := by
      simp [problem6PivotCrossingSet, hcross_right]
    have hmin :=
      problem6FirstClosedPivot_min
        (alpha := alphaRight) (v := v)
        halphaRight0 halphaRight1 hpos hs_mem
    have hu_le_s : u.val ≤ s.val := by
      simpa [hright_pivot] using hmin
    dsimp [s] at hu_le_s
    omega
  rcases problem6BoundaryGap_exists_zero_of_lower_crossing_changes
      halphaBoundary0 halphaRight1 hboundary_le_right hpos
      hcross_boundary_s hnot_cross_right_s with
    ⟨alphaStop, hboundary_le_stop, hstop_le_right,
      halphaStop0, halphaStop1, hboundary_s⟩
  have hBs_stop_zero : problem6BoundaryGap alphaStop v s = 0 :=
    problem6BoundaryGap_eq_zero_iff.mpr hboundary_s
  have hboundary_lt_stop : alphaBoundary < alphaStop := by
    have hne : alphaBoundary ≠ alphaStop := by
      intro hEq
      have hzero_at_boundary :
          problem6BoundaryGap alphaBoundary v s = 0 := by
        simpa [hEq] using hBs_stop_zero
      linarith
    exact lt_of_le_of_ne hboundary_le_stop hne
  let alphaMid : ℝ := (alphaBoundary + alphaStop) / 2
  have hboundary_lt_mid : alphaBoundary < alphaMid := by
    dsimp [alphaMid]
    linarith
  have hmid_lt_stop : alphaMid < alphaStop := by
    dsimp [alphaMid]
    linarith
  have halphaMid0 : 0 < alphaMid :=
    lt_trans halphaBoundary0 hboundary_lt_mid
  have halphaMid1 : alphaMid < 1 :=
    lt_trans hmid_lt_stop halphaStop1
  have hleft_le_mid : alphaLeft ≤ alphaMid :=
    hleft_le_boundary.trans hboundary_lt_mid.le
  have hmid_le_right : alphaMid ≤ alphaRight :=
    hmid_lt_stop.le.trans hstop_le_right
  have hBs_mid_pos :
      0 < problem6BoundaryGap alphaMid v s := by
    have hstrict :=
      problem6BoundaryGap_strictAnti_alpha s
        halphaMid0 halphaMid1 halphaStop0 halphaStop1
        hmid_lt_stop hpos
    linarith
  have hcross_mid_s :
      - (pairShare alphaMid v s)⁻¹ ≤ problem6PivotGap alphaMid v s :=
    problem6BoundaryGap_nonneg_iff_lower_crossing.mp hBs_mid_pos.le
  let p : Item n :=
    problem6FirstClosedPivot alphaMid v halphaMid0 halphaMid1 hpos
  have hp_cross :
      - (pairShare alphaMid v p)⁻¹ ≤ problem6PivotGap alphaMid v p := by
    dsimp [p]
    exact problem6FirstClosedPivot_lower_crossing
      (alpha := alphaMid) (v := v)
      halphaMid0 halphaMid1 hpos
  have hs_mem_mid : s ∈ problem6PivotCrossingSet alphaMid v := by
    simp [problem6PivotCrossingSet, hcross_mid_s]
  have hp_le_s : p.val ≤ s.val := by
    dsimp [p]
    exact problem6FirstClosedPivot_min
      (alpha := alphaMid) (v := v)
      halphaMid0 halphaMid1 hpos hs_mem_mid
  have hnot_p_lt_s : ¬ p.val < s.val := by
    intro hp_lt_s
    have hp_boundary_nonneg :
        0 ≤ problem6BoundaryGap alphaMid v p :=
      problem6BoundaryGap_nonneg_iff_lower_crossing.mpr hp_cross
    have hp_le_t : p.val ≤ t.val := by
      dsimp [s] at hp_lt_s
      omega
    by_cases hp_eq_t_val : p.val = t.val
    · have hp_eq_t : p = t := Fin.ext hp_eq_t_val
      have hBt_boundary_zero :
          problem6BoundaryGap alphaBoundary v t = 0 :=
        problem6BoundaryGap_eq_zero_iff.mpr hboundary_t
      have hBt_mid_lt_boundary :
          problem6BoundaryGap alphaMid v t <
            problem6BoundaryGap alphaBoundary v t :=
        problem6BoundaryGap_strictAnti_alpha t
          halphaBoundary0 halphaBoundary1 halphaMid0 halphaMid1
          hboundary_lt_mid hpos
      have hBt_mid_nonneg :
          0 ≤ problem6BoundaryGap alphaMid v t := by
        simpa [hp_eq_t] using hp_boundary_nonneg
      linarith
    · have hp_lt_t : p.val < t.val := lt_of_le_of_ne hp_le_t hp_eq_t_val
      have hp_not_boundary :
          ¬ - (pairShare alphaBoundary v p)⁻¹ ≤
            problem6PivotGap alphaBoundary v p := by
        intro hp_cross_boundary
        have hp_mem_boundary :
            p ∈ problem6PivotCrossingSet alphaBoundary v := by
          simp [problem6PivotCrossingSet, hp_cross_boundary]
        have hmin_boundary :=
          problem6FirstClosedPivot_min
            (alpha := alphaBoundary) (v := v)
            halphaBoundary0 halphaBoundary1 hpos hp_mem_boundary
        have ht_le_p : t.val ≤ p.val := by
          simpa [hfirst_boundary_t] using hmin_boundary
        omega
      have hp_boundary_neg :
          problem6BoundaryGap alphaBoundary v p < 0 := by
        have hnot_nonneg :
            ¬ 0 ≤ problem6BoundaryGap alphaBoundary v p := by
          intro hnonneg
          exact hp_not_boundary
            (problem6BoundaryGap_nonneg_iff_lower_crossing.mp hnonneg)
        exact not_le.mp hnot_nonneg
      have hp_mid_lt_boundary :
          problem6BoundaryGap alphaMid v p <
            problem6BoundaryGap alphaBoundary v p :=
        problem6BoundaryGap_strictAnti_alpha p
          halphaBoundary0 halphaBoundary1 halphaMid0 halphaMid1
          hboundary_lt_mid hpos
      linarith
  have hs_le_p : s.val ≤ p.val := le_of_not_gt hnot_p_lt_s
  have hp_eq_s : p = s := Fin.ext (le_antisymm hp_le_s hs_le_p)
  refine ⟨alphaMid, halphaMid0, halphaMid1, s,
    hleft_le_mid, hmid_le_right, hs_val, ?_⟩
  simpa [p] using hp_eq_s

/--
At `α = 1/2`, the exact-center Lemma 10 candidate lies weakly after the
canonical first closed pivot.
-/
theorem problem6FirstClosedPivot_half_le_center {n : ℕ} [NeZero n]
    {v : Item n → ℝ} {c : Item n}
    (hpos : ∀ j : Item n, 0 < v j)
    (hcenter : c.val = (reverseItem c).val) :
    (problem6FirstClosedPivot (1 / 2) v
      (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) hpos).val ≤ c.val := by
  exact problem6FirstClosedPivot_le_of_closedPivotDenominatorBounds
    (alpha := (1 / 2 : ℝ)) (v := v) (t := c)
    (by norm_num) (by norm_num) hpos
    (problem6ClosedPivotDenominatorBounds_half_center
      hpos hcenter)

/--
At `α = 1/2`, the even-center Lemma 10 candidate lies weakly after the
canonical first closed pivot.
-/
theorem problem6FirstClosedPivot_half_le_succ_center {n : ℕ} [NeZero n]
    {v : Item n → ℝ} {c : Item n}
    (hpos : ∀ j : Item n, 0 < v j)
    (hsucc : c.val + 1 = (reverseItem c).val) :
    (problem6FirstClosedPivot (1 / 2) v
      (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) hpos).val ≤ c.val := by
  exact problem6FirstClosedPivot_le_of_closedPivotDenominatorBounds
    (alpha := (1 / 2 : ℝ)) (v := v) (t := c)
    (by norm_num) (by norm_num) hpos
    (problem6ClosedPivotDenominatorBounds_half_succ_center
      hpos hsucc)

/--
For `α ≤ 1/2`, the canonical first closed pivot lies weakly before its mirror
in the exact-center case.
-/
theorem problem6FirstClosedPivot_le_reverse_of_alpha_le_half_center
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {c : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha_half : alpha ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hcenter : c.val = (reverseItem c).val) :
    (problem6FirstClosedPivot alpha v halpha0 halpha1 hpos).val ≤
      (reverseItem
        (problem6FirstClosedPivot alpha v halpha0 halpha1 hpos)).val := by
  have hmono :
      (problem6FirstClosedPivot alpha v halpha0 halpha1 hpos).val ≤
        (problem6FirstClosedPivot (1 / 2) v
          (by norm_num : (0 : ℝ) < 1 / 2)
          (by norm_num : (1 / 2 : ℝ) < 1) hpos).val :=
    problem6FirstClosedPivot_mono_alpha
      halpha0 halpha1
      (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)
      halpha_half hpos
  have hhalf_le :=
    problem6FirstClosedPivot_half_le_center
      (v := v) (c := c) hpos hcenter
  exact val_le_reverseItem_of_val_le_center_eq_reverse
    (hmono.trans hhalf_le) hcenter

/--
For `α ≤ 1/2`, the canonical first closed pivot lies weakly before its mirror
in the even-center case.
-/
theorem problem6FirstClosedPivot_le_reverse_of_alpha_le_half_succ_center
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {c : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha_half : alpha ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hsucc : c.val + 1 = (reverseItem c).val) :
    (problem6FirstClosedPivot alpha v halpha0 halpha1 hpos).val ≤
      (reverseItem
        (problem6FirstClosedPivot alpha v halpha0 halpha1 hpos)).val := by
  have hmono :
      (problem6FirstClosedPivot alpha v halpha0 halpha1 hpos).val ≤
        (problem6FirstClosedPivot (1 / 2) v
          (by norm_num : (0 : ℝ) < 1 / 2)
          (by norm_num : (1 / 2 : ℝ) < 1) hpos).val :=
    problem6FirstClosedPivot_mono_alpha
      halpha0 halpha1
      (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)
      halpha_half hpos
  have hhalf_le :=
    problem6FirstClosedPivot_half_le_succ_center
      (v := v) (c := c) hpos hsucc
  exact val_le_reverseItem_of_val_le_succ_center
    (hmono.trans hhalf_le) hsucc

/--
Theorem 3 fixed-pivot multiplier monotonicity: on a fixed-pivot first-half
interval, Lemma 8/11 monotonicity of `I^*_{min}` and Lemma 9 monotonicity of
`q_j` imply monotonicity of `I^*_{min}/(1-q_j)`.
-/
theorem theorem3_fixedPivot_tailMultiplier_mono
    {n : ℕ} {alpha alpha' : ℝ} {v : Item n → ℝ} {t j : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter : t.val ≤ (reverseItem t).val) :
    problem6ClosedValue alpha v t / (1 - pairShare alpha v j) ≤
      problem6ClosedValue alpha' v t / (1 - pairShare alpha' v j) := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  have hvalue :
      problem6ClosedValue alpha v t ≤
        problem6ClosedValue alpha' v t :=
    lemma11_fixedPivotClosedValue_monotone
      halpha0 halpha1 halpha0' halpha1' halpha_le hpos hdec hcenter
  have hinv :
      (1 - pairShare alpha v j)⁻¹ ≤
        (1 - pairShare alpha' v j)⁻¹ :=
    one_sub_pairShare_inv_mono_alpha j
      halpha0 halpha1 halpha0' halpha1' halpha_le hpos
  exact mul_le_mul hvalue hinv
    (inv_nonneg.mpr (one_sub_pairShare_pos j halpha0 halpha1 hpos).le)
    (problem6ClosedValue_pos t halpha0' halpha1' hpos).le

/-- Type-1's best-item denominator in the opposing model does not depend on `α`. -/
theorem twoTypeReducedModel_bestItemUtility_one_eq_of_alpha
    {n : ℕ} [NeZero n] (alpha alpha' : ℝ) (v : Item n → ℝ) :
    TypeWeightedRecommendationModel.bestItemUtility
        (twoTypeReducedModel alpha v) 1 =
      TypeWeightedRecommendationModel.bestItemUtility
        (twoTypeReducedModel alpha' v) 1 := by
  simp [TypeWeightedRecommendationModel.bestItemUtility, twoTypeReducedModel]

/--
Theorem 3 fixed-pivot raw utility monotonicity for type `1`.
-/
theorem theorem3_fixedPivot_closedTypeOneRawUtility_mono
    {n : ℕ} {alpha alpha' : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter : t.val ≤ (reverseItem t).val) :
    problem6ClosedTypeOneRawUtility alpha v t ≤
      problem6ClosedTypeOneRawUtility alpha' v t := by
  rw [problem6ClosedTypeOneRawUtility_eq_pivot_add_tail alpha v t,
    problem6ClosedTypeOneRawUtility_eq_pivot_add_tail alpha' v t]
  have hsum :
      (∑ j : Item n,
          if t.val < j.val then
            problem6ClosedValue alpha v t / (1 - pairShare alpha v j) *
              (v (reverseItem j) - v (reverseItem t))
          else 0) ≤
        ∑ j : Item n,
          if t.val < j.val then
            problem6ClosedValue alpha' v t / (1 - pairShare alpha' v j) *
              (v (reverseItem j) - v (reverseItem t))
          else 0 := by
    refine Finset.sum_le_sum ?_
    intro j _hj
    by_cases htj : t.val < j.val
    · rw [if_pos htj, if_pos htj]
      exact mul_le_mul_of_nonneg_right
        (theorem3_fixedPivot_tailMultiplier_mono
          halpha0 halpha1 halpha0' halpha1' halpha_le hpos hdec hcenter)
        (theorem3_tailGap_pos_of_pivot_lt hdec htj).le
    · rw [if_neg htj, if_neg htj]
  simpa [add_comm] using add_le_add_left hsum (v (reverseItem t))

/--
Theorem 3 fixed-pivot normalized utility monotonicity for type `1`.
-/
theorem theorem3_fixedPivot_closedPolicy_normalizedTypeUtility_one_mono
    {n : ℕ} [NeZero n]
    {alpha alpha' : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter : t.val ≤ (reverseItem t).val)
    (hpivot : Problem6ClosedNonnegativePivots alpha v t)
    (hpivot' : Problem6ClosedNonnegativePivots alpha' v t) :
    TypeWeightedRecommendationModel.normalizedTypeUtility
        (twoTypeReducedModel alpha v)
        (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot) 1 ≤
      TypeWeightedRecommendationModel.normalizedTypeUtility
        (twoTypeReducedModel alpha' v)
        (problem6ClosedPolicy alpha' v t halpha0' halpha1' hpos hpivot') 1 := by
  unfold TypeWeightedRecommendationModel.normalizedTypeUtility
  rw [problem6ClosedPolicy_rawTypeUtility_one_eq halpha0 halpha1 hpos hpivot,
    problem6ClosedPolicy_rawTypeUtility_one_eq halpha0' halpha1' hpos hpivot']
  rw [twoTypeReducedModel_bestItemUtility_one_eq_of_alpha alpha' alpha v]
  exact div_le_div_of_nonneg_right
    (theorem3_fixedPivot_closedTypeOneRawUtility_mono
      halpha0 halpha1 halpha0' halpha1' halpha_le hpos hdec hcenter)
    (by
      rw [twoTypeReducedModel_bestItemUtility_one_eq_zero alpha v]
      exact (twoTypeReducedModel_bestItemUtility_zero_pos alpha v hpos).le)

/--
Lemma 6 normalization bridge: once the raw closed-form utility of type `0`
dominates type `1` and their best-item normalizers coincide, the normalized
type utility comparison follows.
-/
theorem problem6ClosedPolicy_normalizedType_one_le_zero_of_raw
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hpivot : Problem6ClosedNonnegativePivots alpha v t)
    (hbest :
      TypeWeightedRecommendationModel.bestItemUtility
          (twoTypeReducedModel alpha v) 1 =
        TypeWeightedRecommendationModel.bestItemUtility
          (twoTypeReducedModel alpha v) 0)
    (hbest_pos :
      0 < TypeWeightedRecommendationModel.bestItemUtility
        (twoTypeReducedModel alpha v) 0)
    (hraw :
      problem6ClosedTypeOneRawUtility alpha v t ≤
        problem6ClosedTypeZeroRawUtility alpha v t) :
    TypeWeightedRecommendationModel.normalizedTypeUtility
        (twoTypeReducedModel alpha v)
        (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot) 1 ≤
      TypeWeightedRecommendationModel.normalizedTypeUtility
        (twoTypeReducedModel alpha v)
        (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot) 0 := by
  unfold TypeWeightedRecommendationModel.normalizedTypeUtility
  rw [problem6ClosedPolicy_rawTypeUtility_one_eq halpha0 halpha1 hpos hpivot,
    problem6ClosedPolicy_rawTypeUtility_zero_eq halpha0 halpha1 hpos hpivot,
    hbest]
  exact div_le_div_of_nonneg_right hraw hbest_pos.le

/--
Lemma 6 normalized-utility comparison under the remaining paper-specific
pivot-gap and center-position obligations.
-/
theorem problem6ClosedPolicy_normalizedType_one_le_zero_of_alpha_le_half
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha_half : alpha ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hpivot : Problem6ClosedNonnegativePivots alpha v t)
    (hcenter : t.val ≤ (reverseItem t).val)
    (hpivot_gap :
      0 ≤ problem6ClosedX alpha v t t -
        problem6ClosedY alpha v t (reverseItem t))
    (hbest :
      TypeWeightedRecommendationModel.bestItemUtility
          (twoTypeReducedModel alpha v) 1 =
        TypeWeightedRecommendationModel.bestItemUtility
          (twoTypeReducedModel alpha v) 0)
    (hbest_pos :
      0 < TypeWeightedRecommendationModel.bestItemUtility
        (twoTypeReducedModel alpha v) 0) :
    TypeWeightedRecommendationModel.normalizedTypeUtility
        (twoTypeReducedModel alpha v)
        (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot) 1 ≤
      TypeWeightedRecommendationModel.normalizedTypeUtility
        (twoTypeReducedModel alpha v)
        (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot) 0 := by
  have hraw :
      problem6ClosedTypeOneRawUtility alpha v t ≤
        problem6ClosedTypeZeroRawUtility alpha v t :=
    problem6ClosedTypeOneRawUtility_le_typeZeroRawUtility_of_alpha_le_half
      halpha0 halpha1 halpha_half hpos hdec hpivot
      (fun j hj =>
        reverseItem_after_pivot_of_before_pivot_of_pivot_le_reverse
          hcenter hj)
      hpivot_gap
  exact problem6ClosedPolicy_normalizedType_one_le_zero_of_raw
    halpha0 halpha1 hpos hpivot hbest hbest_pos hraw

/--
Lemma 6 normalized-utility comparison under `α ≤ 1/2`, with the pivot-gap
obligation removed by the paper's strict pre-pivot summation argument.
-/
theorem problem6ClosedPolicy_normalizedType_one_le_zero_of_alpha_le_half_of_pivot_le_reverse
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha_half : alpha ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hpivot : Problem6ClosedNonnegativePivots alpha v t)
    (hcenter : t.val ≤ (reverseItem t).val)
    (hbest :
      TypeWeightedRecommendationModel.bestItemUtility
          (twoTypeReducedModel alpha v) 1 =
        TypeWeightedRecommendationModel.bestItemUtility
          (twoTypeReducedModel alpha v) 0)
    (hbest_pos :
      0 < TypeWeightedRecommendationModel.bestItemUtility
        (twoTypeReducedModel alpha v) 0) :
    TypeWeightedRecommendationModel.normalizedTypeUtility
        (twoTypeReducedModel alpha v)
        (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot) 1 ≤
      TypeWeightedRecommendationModel.normalizedTypeUtility
        (twoTypeReducedModel alpha v)
        (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot) 0 := by
  have hraw :
      problem6ClosedTypeOneRawUtility alpha v t ≤
        problem6ClosedTypeZeroRawUtility alpha v t :=
    problem6ClosedTypeOneRawUtility_le_typeZeroRawUtility_of_alpha_le_half_of_pivot_le_reverse
      halpha0 halpha1 halpha_half hpos hdec hpivot hcenter
  exact problem6ClosedPolicy_normalizedType_one_le_zero_of_raw
    halpha0 halpha1 hpos hpivot hbest hbest_pos hraw

/--
Lemma 6 normalized-utility comparison under `α ≤ 1/2`, with the common
best-item denominator discharged by the opposing-preference model.
-/
theorem problem6ClosedPolicy_normalizedType_one_le_zero_of_alpha_le_half_auto_best
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha_half : alpha ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hpivot : Problem6ClosedNonnegativePivots alpha v t)
    (hcenter : t.val ≤ (reverseItem t).val)
    (hpivot_gap :
      0 ≤ problem6ClosedX alpha v t t -
        problem6ClosedY alpha v t (reverseItem t)) :
    TypeWeightedRecommendationModel.normalizedTypeUtility
        (twoTypeReducedModel alpha v)
        (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot) 1 ≤
      TypeWeightedRecommendationModel.normalizedTypeUtility
        (twoTypeReducedModel alpha v)
        (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot) 0 := by
  exact problem6ClosedPolicy_normalizedType_one_le_zero_of_alpha_le_half
    halpha0 halpha1 halpha_half hpos hdec hpivot hcenter hpivot_gap
    (twoTypeReducedModel_bestItemUtility_one_eq_zero alpha v)
    (twoTypeReducedModel_bestItemUtility_zero_pos alpha v hpos)

/--
Lemma 6 normalized-utility comparison under `α ≤ 1/2`, with the common
best-item denominator discharged and no pivot-gap side condition.
-/
theorem problem6ClosedPolicy_normalizedType_one_le_zero_of_alpha_le_half_auto_best_of_pivot_le_reverse
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha_half : alpha ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hpivot : Problem6ClosedNonnegativePivots alpha v t)
    (hcenter : t.val ≤ (reverseItem t).val) :
    TypeWeightedRecommendationModel.normalizedTypeUtility
        (twoTypeReducedModel alpha v)
        (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot) 1 ≤
      TypeWeightedRecommendationModel.normalizedTypeUtility
        (twoTypeReducedModel alpha v)
        (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot) 0 := by
  exact problem6ClosedPolicy_normalizedType_one_le_zero_of_alpha_le_half_of_pivot_le_reverse
    halpha0 halpha1 halpha_half hpos hdec hpivot hcenter
    (twoTypeReducedModel_bestItemUtility_one_eq_zero alpha v)
    (twoTypeReducedModel_bestItemUtility_zero_pos alpha v hpos)

/-- In a two-type model, if type `1` is no better than type `0`, it is the minimum. -/
theorem twoType_typeFairness_eq_one_of_one_le_zero {n : ℕ} [NeZero n]
    (T : TypeWeightedRecommendationModel 2 n) (ρ : TypePolicy 2 n)
    (hle :
      TypeWeightedRecommendationModel.normalizedTypeUtility T ρ 1 ≤
        TypeWeightedRecommendationModel.normalizedTypeUtility T ρ 0) :
    TypeWeightedRecommendationModel.typeFairness T ρ =
      TypeWeightedRecommendationModel.normalizedTypeUtility T ρ 1 := by
  unfold TypeWeightedRecommendationModel.typeFairness AppliedModelingLib.finiteMin
  apply le_antisymm
  · exact Finset.inf'_le
      (s := (Finset.univ : Finset (UserType 2)))
      (f := TypeWeightedRecommendationModel.normalizedTypeUtility T ρ)
      (by simp : (1 : UserType 2) ∈ Finset.univ)
  · apply Finset.le_inf'
    intro k _hk
    fin_cases k
    · exact hle
    · rfl

/--
Lemma 6 consequence: under the remaining pivot-gap and center-position
obligations, the closed policy's type fairness is exactly type `1`'s
normalized utility.
-/
theorem problem6ClosedPolicy_typeFairness_eq_one_of_alpha_le_half
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha_half : alpha ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hpivot : Problem6ClosedNonnegativePivots alpha v t)
    (hcenter : t.val ≤ (reverseItem t).val)
    (hpivot_gap :
      0 ≤ problem6ClosedX alpha v t t -
        problem6ClosedY alpha v t (reverseItem t)) :
    TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel alpha v)
        (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot) =
      TypeWeightedRecommendationModel.normalizedTypeUtility
        (twoTypeReducedModel alpha v)
        (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot) 1 := by
  exact twoType_typeFairness_eq_one_of_one_le_zero
    (twoTypeReducedModel alpha v)
    (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot)
    (problem6ClosedPolicy_normalizedType_one_le_zero_of_alpha_le_half_auto_best
      halpha0 halpha1 halpha_half hpos hdec hpivot hcenter hpivot_gap)

/--
Lemma 6 consequence with the pivot-gap side condition removed: if `α ≤ 1/2`
and the closed-form pivot is at or before its mirror, the closed policy's type
fairness is exactly type `1`'s normalized utility.
-/
theorem problem6ClosedPolicy_typeFairness_eq_one_of_alpha_le_half_of_pivot_le_reverse
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha_half : alpha ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hpivot : Problem6ClosedNonnegativePivots alpha v t)
    (hcenter : t.val ≤ (reverseItem t).val) :
    TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel alpha v)
        (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot) =
      TypeWeightedRecommendationModel.normalizedTypeUtility
        (twoTypeReducedModel alpha v)
        (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot) 1 := by
  exact twoType_typeFairness_eq_one_of_one_le_zero
    (twoTypeReducedModel alpha v)
    (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot)
    (problem6ClosedPolicy_normalizedType_one_le_zero_of_alpha_le_half_auto_best_of_pivot_le_reverse
      halpha0 halpha1 halpha_half hpos hdec hpivot hcenter)

/--
Appendix D, Lemma 6 specialized to the exact midpoint candidate: its closed
policy's type fairness is type `1`'s normalized utility.
-/
theorem problem6ClosedPolicy_typeFairness_eq_one_half_center
    {n : ℕ} [NeZero n] {v : Item n → ℝ} {t : Item n}
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter : t.val = (reverseItem t).val) :
    let hpivot : Problem6ClosedNonnegativePivots (1 / 2) v t :=
      problem6ClosedNonnegativePivots_of_denominatorBounds
        (by norm_num : (0 : ℝ) < 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1) hpos
        (problem6ClosedPivotDenominatorBounds_half_center
          (v := v) (t := t) hpos hcenter)
    TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel (1 / 2) v)
        (problem6ClosedPolicy (1 / 2) v t
          (by norm_num : (0 : ℝ) < 1 / 2)
          (by norm_num : (1 / 2 : ℝ) < 1) hpos hpivot) =
      TypeWeightedRecommendationModel.normalizedTypeUtility
        (twoTypeReducedModel (1 / 2) v)
        (problem6ClosedPolicy (1 / 2) v t
          (by norm_num : (0 : ℝ) < 1 / 2)
          (by norm_num : (1 / 2 : ℝ) < 1) hpos hpivot) 1 := by
  dsimp
  exact problem6ClosedPolicy_typeFairness_eq_one_of_alpha_le_half
    (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
    (by norm_num : (1 / 2 : ℝ) ≤ 1 / 2)
    hpos hdec
    (problem6ClosedNonnegativePivots_of_denominatorBounds
      (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) hpos
      (problem6ClosedPivotDenominatorBounds_half_center
        (v := v) (t := t) hpos hcenter))
    hcenter.le
    (problem6ClosedX_sub_closedY_reverse_half_center_nonneg
      hpos hcenter)

/--
Appendix D, Lemma 6 specialized to the even midpoint candidate: its closed
policy's type fairness is type `1`'s normalized utility.
-/
theorem problem6ClosedPolicy_typeFairness_eq_one_half_succ_center
    {n : ℕ} [NeZero n] {v : Item n → ℝ} {t : Item n}
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hsucc : t.val + 1 = (reverseItem t).val) :
    let hpivot : Problem6ClosedNonnegativePivots (1 / 2) v t :=
      problem6ClosedNonnegativePivots_of_denominatorBounds
        (by norm_num : (0 : ℝ) < 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1) hpos
        (problem6ClosedPivotDenominatorBounds_half_succ_center
          (v := v) (t := t) hpos hsucc)
    TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel (1 / 2) v)
        (problem6ClosedPolicy (1 / 2) v t
          (by norm_num : (0 : ℝ) < 1 / 2)
          (by norm_num : (1 / 2 : ℝ) < 1) hpos hpivot) =
      TypeWeightedRecommendationModel.normalizedTypeUtility
        (twoTypeReducedModel (1 / 2) v)
        (problem6ClosedPolicy (1 / 2) v t
          (by norm_num : (0 : ℝ) < 1 / 2)
          (by norm_num : (1 / 2 : ℝ) < 1) hpos hpivot) 1 := by
  dsimp
  have hcenter : t.val ≤ (reverseItem t).val := by
    omega
  exact problem6ClosedPolicy_typeFairness_eq_one_of_alpha_le_half
    (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
    (by norm_num : (1 / 2 : ℝ) ≤ 1 / 2)
    hpos hdec
    (problem6ClosedNonnegativePivots_of_denominatorBounds
      (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) hpos
      (problem6ClosedPivotDenominatorBounds_half_succ_center
        (v := v) (t := t) hpos hsucc))
    hcenter
    (problem6ClosedX_sub_closedY_reverse_half_succ_center_nonneg
      hpos hsucc)

/-- Lemma 5 pivot equation: `x_t = 1 - λ L_t`. -/
theorem problem6SparseEqualized_x_pivot_eq
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    {x y : Item n → ℝ} {ell : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (h : Problem6SparseEqualized alpha v t x y ell) :
    x t = 1 - ell * problem6LeftSum alpha v t := by
  have hsplit :=
    problem6_sum_eq_left_part_add_pivot_of_after_zero x t
      h.x_after_pivot_zero
  have hleft :=
    problem6SparseEqualized_left_part_sum_eq halpha0 halpha1 hpos h
  nlinarith [h.sum_x, hsplit, hleft]

/-- Lemma 5 pivot equation: `y_t = 1 - λ R_t`. -/
theorem problem6SparseEqualized_y_pivot_eq
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    {x y : Item n → ℝ} {ell : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (h : Problem6SparseEqualized alpha v t x y ell) :
    y t = 1 - ell * problem6RightSum alpha v t := by
  have hsplit :=
    problem6_sum_eq_pivot_add_right_part_of_before_zero y t
      h.y_before_pivot_zero
  have hright :=
    problem6SparseEqualized_right_part_sum_eq halpha0 halpha1 hpos h
  nlinarith [h.sum_y, hsplit, hright]

/-- Lemma 5 closed value: `λ = 1 / (1 + q_t L_t + (1-q_t)R_t)`. -/
theorem problem6SparseEqualized_value_eq_closed
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    {x y : Item n → ℝ} {ell : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (h : Problem6SparseEqualized alpha v t x y ell) :
    ell = problem6ClosedValue alpha v t := by
  have hx :=
    problem6SparseEqualized_x_pivot_eq halpha0 halpha1 hpos h
  have hy :=
    problem6SparseEqualized_y_pivot_eq halpha0 halpha1 hpos h
  have ht := h.item_eq t
  rw [hx, hy] at ht
  have hmul : ell * problem6ClosedDenominator alpha v t = 1 := by
    unfold problem6ClosedDenominator
    nlinarith
  have hDpos :=
    problem6ClosedDenominator_pos t halpha0 halpha1 hpos
  unfold problem6ClosedValue
  rw [eq_div_iff (ne_of_gt hDpos)]
  exact hmul

/-- Lemma 5 closed form: before the pivot, `x_j = I^*_min / q_j`. -/
theorem problem6SparseEqualized_x_before_eq_closed
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {t j : Item n}
    {x y : Item n → ℝ} {ell : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (h : Problem6SparseEqualized alpha v t x y ell)
    (hj : j.val < t.val) :
    x j = problem6ClosedValue alpha v t / pairShare alpha v j := by
  rw [problem6SparseEqualized_x_before_eq halpha0 halpha1 hpos h hj,
    problem6SparseEqualized_value_eq_closed halpha0 halpha1 hpos h]

/-- Lemma 5 closed form: after the pivot, `y_j = I^*_min / (1 - q_j)`. -/
theorem problem6SparseEqualized_y_after_eq_closed
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {t j : Item n}
    {x y : Item n → ℝ} {ell : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (h : Problem6SparseEqualized alpha v t x y ell)
    (hj : t.val < j.val) :
    y j = problem6ClosedValue alpha v t / (1 - pairShare alpha v j) := by
  rw [problem6SparseEqualized_y_after_eq halpha0 halpha1 hpos h hj,
    problem6SparseEqualized_value_eq_closed halpha0 halpha1 hpos h]

/-- Lemma 5 closed form for the pivot `x_t`. -/
theorem problem6SparseEqualized_x_pivot_eq_closed
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    {x y : Item n → ℝ} {ell : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (h : Problem6SparseEqualized alpha v t x y ell) :
    x t = 1 - problem6ClosedValue alpha v t *
      problem6LeftSum alpha v t := by
  rw [problem6SparseEqualized_x_pivot_eq halpha0 halpha1 hpos h,
    problem6SparseEqualized_value_eq_closed halpha0 halpha1 hpos h]

/-- Lemma 5 closed form for the pivot `y_t`. -/
theorem problem6SparseEqualized_y_pivot_eq_closed
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    {x y : Item n → ℝ} {ell : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (h : Problem6SparseEqualized alpha v t x y ell) :
    y t = 1 - problem6ClosedValue alpha v t *
      problem6RightSum alpha v t := by
  rw [problem6SparseEqualized_y_pivot_eq halpha0 halpha1 hpos h,
    problem6SparseEqualized_value_eq_closed halpha0 halpha1 hpos h]

/--
Appendix D, Lemma 4 uniqueness, same-pivot case: two sparse equalized
solutions with the same pivot have identical value and coordinates.
-/
theorem problem6SparseEqualized_eq_of_same_pivot
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    {x y x' y' : Item n → ℝ} {ell ell' : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (h : Problem6SparseEqualized alpha v t x y ell)
    (h' : Problem6SparseEqualized alpha v t x' y' ell') :
    ell = ell' ∧ x = x' ∧ y = y' := by
  have hell :
      ell = problem6ClosedValue alpha v t :=
    problem6SparseEqualized_value_eq_closed halpha0 halpha1 hpos h
  have hell' :
      ell' = problem6ClosedValue alpha v t :=
    problem6SparseEqualized_value_eq_closed halpha0 halpha1 hpos h'
  have hx : x = x' := by
    funext j
    by_cases hjlt : j.val < t.val
    · rw [problem6SparseEqualized_x_before_eq_closed
        halpha0 halpha1 hpos h hjlt,
        problem6SparseEqualized_x_before_eq_closed
          halpha0 halpha1 hpos h' hjlt]
    · by_cases hjeq : j = t
      · subst j
        rw [problem6SparseEqualized_x_pivot_eq_closed
          halpha0 halpha1 hpos h,
          problem6SparseEqualized_x_pivot_eq_closed
            halpha0 halpha1 hpos h']
      · have hjgt : t.val < j.val := by
          have hne_val : j.val ≠ t.val := by
            intro hval
            exact hjeq (Fin.ext hval)
          omega
        rw [h.x_after_pivot_zero hjgt, h'.x_after_pivot_zero hjgt]
  have hy : y = y' := by
    funext j
    by_cases hjlt : j.val < t.val
    · rw [h.y_before_pivot_zero hjlt, h'.y_before_pivot_zero hjlt]
    · by_cases hjeq : j = t
      · subst j
        rw [problem6SparseEqualized_y_pivot_eq_closed
          halpha0 halpha1 hpos h,
          problem6SparseEqualized_y_pivot_eq_closed
            halpha0 halpha1 hpos h']
      · have hjgt : t.val < j.val := by
          have hne_val : j.val ≠ t.val := by
            intro hval
            exact hjeq (Fin.ext hval)
          omega
        rw [problem6SparseEqualized_y_after_eq_closed
          halpha0 halpha1 hpos h hjgt,
          problem6SparseEqualized_y_after_eq_closed
            halpha0 halpha1 hpos h' hjgt]
  exact ⟨hell.trans hell'.symm, hx, hy⟩

/--
Lemma 5 closed-form uniqueness: any sparse equalized solution with pivot `t`
has exactly the closed-form value and coordinates for that pivot.
-/
theorem problem6SparseEqualized_eq_closed
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    {x y : Item n → ℝ} {ell : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (h : Problem6SparseEqualized alpha v t x y ell) :
    ell = problem6ClosedValue alpha v t ∧
      x = problem6ClosedX alpha v t ∧
      y = problem6ClosedY alpha v t := by
  exact problem6SparseEqualized_eq_of_same_pivot
    halpha0 halpha1 hpos h
    (problem6Closed_sparseEqualized t halpha0 halpha1 hpos)

/--
Appendix D, Lemma 4 cross-pivot contradiction.  If two sparse equalized
solutions have the same value and the second pivot is strictly to the right,
then the later pivot cannot carry positive `x` mass.

This is the paper's final uniqueness argument with the active-pivot positivity
assumption made explicit.
-/
theorem problem6SparseEqualized_cross_pivot_contradiction_of_right_pivot_active
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {t t' : Item n}
    {x y x' y' : Item n → ℝ} {ell ell' : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (htt' : t.val < t'.val)
    (h : Problem6SparseEqualized alpha v t x y ell)
    (h' : Problem6SparseEqualized alpha v t' x' y' ell')
    (hell : ell = ell')
    (hy_pivot_nonneg : 0 ≤ y t)
    (hx'_nonneg : ∀ j : Item n, 0 ≤ x' j)
    (hx'_pivot_pos : 0 < x' t') :
    False := by
  classical
  let leftx : ℝ :=
    ∑ j : Item n, if j.val < t.val then x j else 0
  let leftx' : ℝ :=
    ∑ j : Item n, if j.val < t.val then x' j else 0
  have hleft_eq : leftx = leftx' := by
    unfold leftx leftx'
    refine Finset.sum_congr rfl ?_
    intro j _hj
    by_cases hjt : j.val < t.val
    · have hjt' : j.val < t'.val := lt_trans hjt htt'
      have hqne : pairShare alpha v j ≠ 0 :=
        ne_of_gt (pairShare_pos j halpha0 halpha1 hpos)
      have hitem :
          pairShare alpha v j * x j = ell := by
        have heq := h.item_eq j
        rw [h.y_before_pivot_zero hjt] at heq
        simpa using heq
      have hitem' :
          pairShare alpha v j * x' j = ell' := by
        have heq := h'.item_eq j
        rw [h'.y_before_pivot_zero hjt'] at heq
        simpa using heq
      have hmul :
          pairShare alpha v j * x j =
            pairShare alpha v j * x' j := by
        calc
          pairShare alpha v j * x j = ell := hitem
          _ = ell' := hell
          _ = pairShare alpha v j * x' j := hitem'.symm
      have hxj_eq : x j = x' j := by
        calc
          x j =
              (pairShare alpha v j * x j) /
                pairShare alpha v j := by
                field_simp [hqne]
          _ =
              (pairShare alpha v j * x' j) /
                pairShare alpha v j := by
                rw [hmul]
          _ = x' j := by
                field_simp [hqne]
      simp [hjt, hxj_eq]
    · simp [hjt]
  have hsplit :=
    problem6_sum_eq_left_part_add_pivot_of_after_zero
      x t h.x_after_pivot_zero
  have hxt_eq : x t = 1 - leftx := by
    have hsum :
        (∑ j : Item n, x j) = leftx + x t := by
      simpa [leftx] using hsplit
    nlinarith [h.sum_x, hsum]
  let rightx' : ℝ :=
    ∑ j : Item n, if t.val < j.val then x' j else 0
  have hrightx'_nonneg : 0 ≤ rightx' := by
    unfold rightx'
    refine Finset.sum_nonneg ?_
    intro j _hj
    by_cases hj : t.val < j.val
    · simp [hj, hx'_nonneg j]
    · simp [hj]
  have hrightx'_pos : 0 < rightx' := by
    have hle : x' t' ≤ rightx' := by
      unfold rightx'
      simpa [htt'] using
        Finset.single_le_sum
          (s := (Finset.univ : Finset (Item n)))
          (f := fun j : Item n => if t.val < j.val then x' j else 0)
          (fun j _hj => by
            by_cases hj : t.val < j.val
            · simp [hj, hx'_nonneg j]
            · simp [hj])
          (by simp : t' ∈ (Finset.univ : Finset (Item n)))
    exact lt_of_lt_of_le hx'_pivot_pos hle
  have hsplit' :=
    problem6_sum_eq_left_part_add_pivot_add_right_part x' t
  have hprefix_lt : leftx' + x' t < 1 := by
    have hsum :
        (∑ j : Item n, x' j) = leftx' + x' t + rightx' := by
      simpa [leftx', rightx'] using hsplit'
    nlinarith [h'.sum_x, hsum, hrightx'_pos]
  let q : ℝ := pairShare alpha v t
  have hqpos : 0 < q := by
    simpa [q] using pairShare_pos t halpha0 halpha1 hpos
  have hqcomp_pos : 0 < 1 - q := by
    simpa [q] using one_sub_pairShare_pos t halpha0 halpha1 hpos
  have hitem_t :
      q * x t + (1 - q) * y t = ell := by
    simpa [q] using h.item_eq t
  have hitem_t' :
      q * x' t = ell' := by
    have heq := h'.item_eq t
    rw [h'.y_before_pivot_zero htt'] at heq
    simpa [q] using heq
  have hsame_item :
      q * x t + (1 - q) * y t = q * x' t := by
    calc
      q * x t + (1 - q) * y t = ell := hitem_t
      _ = ell' := hell
      _ = q * x' t := hitem_t'.symm
  have hdelta_eq :
      (1 - q) * y t = q * (x' t - (1 - leftx)) := by
    rw [hxt_eq] at hsame_item
    nlinarith
  have hxprime_minus_neg : x' t - (1 - leftx) < 0 := by
    nlinarith [hprefix_lt, hleft_eq]
  have hright_neg : q * (x' t - (1 - leftx)) < 0 :=
    mul_neg_of_pos_of_neg hqpos hxprime_minus_neg
  have hleft_nonneg : 0 ≤ (1 - q) * y t :=
    mul_nonneg hqcomp_pos.le hy_pivot_nonneg
  linarith

/--
Appendix D, Lemma 4 cross-pivot uniqueness under the active-pivot side
condition: two sparse equalized solutions with the same value, nonnegative
coordinates, and positive active `x` mass at both pivots must use the same
pivot.
-/
theorem problem6SparseEqualized_pivot_eq_of_equal_value_and_active_pivots
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {t t' : Item n}
    {x y x' y' : Item n → ℝ} {ell ell' : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (h : Problem6SparseEqualized alpha v t x y ell)
    (h' : Problem6SparseEqualized alpha v t' x' y' ell')
    (hell : ell = ell')
    (hx_nonneg : ∀ j : Item n, 0 ≤ x j)
    (hy_nonneg : ∀ j : Item n, 0 ≤ y j)
    (hx'_nonneg : ∀ j : Item n, 0 ≤ x' j)
    (hy'_nonneg : ∀ j : Item n, 0 ≤ y' j)
    (hxt_pos : 0 < x t)
    (hxt'_pos : 0 < x' t') :
    t = t' := by
  rcases lt_trichotomy t.val t'.val with htt' | hval_eq | ht't
  · exact False.elim
      (problem6SparseEqualized_cross_pivot_contradiction_of_right_pivot_active
        halpha0 halpha1 hpos htt' h h' hell (hy_nonneg t)
        hx'_nonneg hxt'_pos)
  · exact Fin.ext hval_eq
  · exact False.elim
      (problem6SparseEqualized_cross_pivot_contradiction_of_right_pivot_active
        halpha0 halpha1 hpos ht't h' h hell.symm (hy'_nonneg t')
        hx_nonneg hxt_pos)

/--
Appendix D, Lemma 4 uniqueness under the active-pivot side condition: once
cross-pivot cases are ruled out, the same-pivot closed-form argument identifies
the value and all coordinates.
-/
theorem problem6SparseEqualized_eq_of_equal_value_and_active_pivots
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {t t' : Item n}
    {x y x' y' : Item n → ℝ} {ell ell' : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (h : Problem6SparseEqualized alpha v t x y ell)
    (h' : Problem6SparseEqualized alpha v t' x' y' ell')
    (hell : ell = ell')
    (hx_nonneg : ∀ j : Item n, 0 ≤ x j)
    (hy_nonneg : ∀ j : Item n, 0 ≤ y j)
    (hx'_nonneg : ∀ j : Item n, 0 ≤ x' j)
    (hy'_nonneg : ∀ j : Item n, 0 ≤ y' j)
    (hxt_pos : 0 < x t)
    (hxt'_pos : 0 < x' t') :
    t = t' ∧ ell = ell' ∧ x = x' ∧ y = y' := by
  have hpivot :
      t = t' :=
    problem6SparseEqualized_pivot_eq_of_equal_value_and_active_pivots
      halpha0 halpha1 hpos h h' hell hx_nonneg hy_nonneg
      hx'_nonneg hy'_nonneg hxt_pos hxt'_pos
  subst t'
  have hsame :=
    problem6SparseEqualized_eq_of_same_pivot
      halpha0 halpha1 hpos h h'
  exact ⟨rfl, hsame⟩

/--
Appendix D, Lemma 4 uniqueness for active sparse equalized solutions: if two
active-pivot sparse solutions have the same value, then the pivots, value, and
all coordinates agree.
-/
theorem problem6SparseEqualizedActive_eq_of_equal_value
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {t t' : Item n}
    {x y x' y' : Item n → ℝ} {ell ell' : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (h : Problem6SparseEqualizedActive alpha v t x y ell)
    (h' : Problem6SparseEqualizedActive alpha v t' x' y' ell')
    (hell : ell = ell') :
    t = t' ∧ ell = ell' ∧ x = x' ∧ y = y' := by
  exact problem6SparseEqualized_eq_of_equal_value_and_active_pivots
    halpha0 halpha1 hpos h.sparse h'.sparse hell h.x_nonneg h.y_nonneg
    h'.x_nonneg h'.y_nonneg h.x_pivot_pos h'.x_pivot_pos

/--
Lemma 5 feasibility bridge: an active sparse equalized solution makes the
closed-form pivot coordinates nonnegative at the same pivot.
-/
theorem problem6ClosedNonnegativePivots_of_sparseEqualizedActive
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    {x y : Item n → ℝ} {ell : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (h : Problem6SparseEqualizedActive alpha v t x y ell) :
    Problem6ClosedNonnegativePivots alpha v t := by
  constructor
  · rw [problem6ClosedX_at]
    rw [← problem6SparseEqualized_x_pivot_eq_closed
      halpha0 halpha1 hpos h.sparse]
    exact h.x_nonneg t
  · rw [problem6ClosedY_at]
    rw [← problem6SparseEqualized_y_pivot_eq_closed
      halpha0 halpha1 hpos h.sparse]
    exact h.y_nonneg t

/--
Lemma 5 denominator-bound bridge: for the active sparse pivot of Lemma 4, the
closed-form denominator bounds follow from the nonnegative pivot coordinates.
-/
theorem problem6ClosedPivotDenominatorBounds_of_sparseEqualizedActive
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    {x y : Item n → ℝ} {ell : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (h : Problem6SparseEqualizedActive alpha v t x y ell) :
    Problem6ClosedPivotDenominatorBounds alpha v t := by
  exact problem6ClosedPivotDenominatorBounds_of_nonnegativePivots
    halpha0 halpha1 hpos
    (problem6ClosedNonnegativePivots_of_sparseEqualizedActive
      halpha0 halpha1 hpos h)

/-- Active sparse equalized solutions have strictly positive equalized value. -/
theorem problem6SparseEqualizedActive_value_pos
    {n : ℕ} {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    {x y : Item n → ℝ} {ell : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (h : Problem6SparseEqualizedActive alpha v t x y ell) :
    0 < ell := by
  let q : ℝ := pairShare alpha v t
  have hqpos : 0 < q := by
    simpa [q] using pairShare_pos t halpha0 halpha1 hpos
  have hqcomp_nonneg : 0 ≤ 1 - q := by
    exact (one_sub_pairShare_pos t halpha0 halpha1 hpos).le
  have hmain :
      0 < q * x t + (1 - q) * y t := by
    have hleft : 0 < q * x t := mul_pos hqpos h.x_pivot_pos
    have hright : 0 ≤ (1 - q) * y t :=
      mul_nonneg hqcomp_nonneg (h.y_nonneg t)
    exact lt_of_lt_of_le hleft (by nlinarith)
  simpa [q, h.sparse.item_eq t] using hmain

set_option maxHeartbeats 800000 in
-- This large paper proof compares two finite equalized policies and otherwise
-- times out in the final contradiction branch under the default budget.
/--
Appendix D, Lemma 7 in sparse-solution form: as `α` increases, the active
pivot `t = max {j : x_j > 0}` cannot move left.

This follows the paper's two-case proof comparing the equalized values
`I^*_{min}(α)` and `I^*_{min}(α')`.
-/
theorem lemma7_sparseActive_pivot_mono_of_alpha_lt
    {n : ℕ} {alpha alpha' : ℝ} {v : Item n → ℝ}
    {t t' : Item n} {x y x' y' : Item n → ℝ} {ell ell' : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_lt : alpha < alpha')
    (hpos : ∀ j : Item n, 0 < v j)
    (h : Problem6SparseEqualizedActive alpha v t x y ell)
    (h' : Problem6SparseEqualizedActive alpha' v t' x' y' ell') :
    t.val ≤ t'.val := by
  classical
  by_contra hnot
  have ht't : t'.val < t.val := by omega
  have hell_pos : 0 < ell :=
    problem6SparseEqualizedActive_value_pos halpha0 halpha1 hpos h
  have hell'_pos : 0 < ell' :=
    problem6SparseEqualizedActive_value_pos halpha0' halpha1' hpos h'
  rcases lt_or_ge ell ell' with hell_lt | hell_ge
  · let q : ℝ := pairShare alpha v t
    let q' : ℝ := pairShare alpha' v t
    have hqpos : 0 < q := by
      simpa [q] using pairShare_pos t halpha0 halpha1 hpos
    have hq'comp_pos : 0 < 1 - q' := by
      simpa [q'] using one_sub_pairShare_pos t halpha0' halpha1' hpos
    have hq_lt : q < q' := by
      simpa [q, q'] using
        pairShare_strictMono_alpha t halpha0 halpha1
          halpha0' halpha1' halpha_lt hpos
    have hx'_t_zero : x' t = 0 :=
      h'.sparse.x_after_pivot_zero ht't
    have hitem_t :
        q * x t + (1 - q) * y t = ell := by
      simpa [q] using h.sparse.item_eq t
    have hitem_t' :
        (1 - q') * y' t = ell' := by
      have heq := h'.sparse.item_eq t
      rw [hx'_t_zero] at heq
      simpa [q'] using heq
    by_cases hright_exists : ∃ j : Item n, t.val < j.val
    · have hy_after_lt :
          ∀ {j : Item n}, t.val < j.val → y j < y' j := by
        intro j hj
        have hj' : t'.val < j.val := lt_trans ht't hj
        let qj : ℝ := pairShare alpha v j
        let qj' : ℝ := pairShare alpha' v j
        have hqj_lt : qj < qj' := by
          simpa [qj, qj'] using
            pairShare_strictMono_alpha j halpha0 halpha1
              halpha0' halpha1' halpha_lt hpos
        have hden : 0 < 1 - qj := by
          simpa [qj] using one_sub_pairShare_pos j halpha0 halpha1 hpos
        have hden' : 0 < 1 - qj' := by
          simpa [qj'] using one_sub_pairShare_pos j halpha0' halpha1' hpos
        have hval_lt_same_denom :
            ell / (1 - qj) < ell' / (1 - qj) :=
          div_lt_div_of_pos_right hell_lt hden
        have hsame_val_lt :
            ell' / (1 - qj) < ell' / (1 - qj') := by
          rw [div_lt_div_iff₀ hden hden']
          nlinarith [hell'_pos, hqj_lt]
        rw [problem6SparseEqualized_y_after_eq
            halpha0 halpha1 hpos h.sparse hj,
          problem6SparseEqualized_y_after_eq
            halpha0' halpha1' hpos h'.sparse hj']
        exact lt_trans hval_lt_same_denom hsame_val_lt
      let rightY : ℝ :=
        ∑ j : Item n, if t.val < j.val then y j else 0
      let rightY' : ℝ :=
        ∑ j : Item n, if t.val < j.val then y' j else 0
      have hright_lt : rightY < rightY' := by
        unfold rightY rightY'
        refine Finset.sum_lt_sum ?_ ?_
        · intro j _hj
          by_cases hj : t.val < j.val
          · exact le_of_lt (by simpa [hj] using hy_after_lt hj)
          · simp [hj]
        · rcases hright_exists with ⟨j, hj⟩
          exact ⟨j, by simp, by simpa [hj] using hy_after_lt hj⟩
      have hsplit_y :=
        problem6_sum_eq_pivot_add_right_part_of_before_zero
          y t h.sparse.y_before_pivot_zero
      have hy_t_eq : y t = 1 - rightY := by
        have hsum :
            (∑ j : Item n, y j) = y t + rightY := by
          simpa [rightY] using hsplit_y
        nlinarith [h.sparse.sum_y, hsum]
      let leftY' : ℝ :=
        ∑ j : Item n, if j.val < t.val then y' j else 0
      have hleftY'_nonneg : 0 ≤ leftY' := by
        unfold leftY'
        refine Finset.sum_nonneg ?_
        intro j _hj
        by_cases hj : j.val < t.val
        · simp [hj, h'.y_nonneg j]
        · simp [hj]
      have hsplit_y' :=
        problem6_sum_eq_left_part_add_pivot_add_right_part y' t
      have hy'_plus_right_le : y' t + rightY' ≤ 1 := by
        have hsum :
            (∑ j : Item n, y' j) =
              leftY' + y' t + rightY' := by
          simpa [leftY', rightY'] using hsplit_y'
        nlinarith [h'.sparse.sum_y, hsum, hleftY'_nonneg]
      have hy'_t_lt_y_t : y' t < y t := by
        nlinarith [hright_lt, hy_t_eq, hy'_plus_right_le]
      have hfirst :
          q * x t + (1 - q) * y t < (1 - q') * y' t := by
        rw [hitem_t, hitem_t']
        exact hell_lt
      have hsecond :
          (1 - q') * y' t < (1 - q') * y t :=
        mul_lt_mul_of_pos_left hy'_t_lt_y_t hq'comp_pos
      have hbad :
          q * x t + (1 - q) * y t < (1 - q') * y t :=
        lt_trans hfirst hsecond
      have hleft_nonneg : 0 ≤ q * x t :=
        mul_nonneg hqpos.le (h.x_nonneg t)
      have hright_nonpos : (q - q') * y t ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg
          (sub_nonpos.mpr hq_lt.le) (h.y_nonneg t)
      have hlt_right : q * x t < (q - q') * y t := by
        nlinarith
      exact (not_lt_of_ge hleft_nonneg)
        (lt_of_lt_of_le hlt_right hright_nonpos)
    · let rightY : ℝ :=
        ∑ j : Item n, if t.val < j.val then y j else 0
      have hright_zero : rightY = 0 := by
        unfold rightY
        refine Finset.sum_eq_zero ?_
        intro j _hj
        have hj : ¬ t.val < j.val := by
          intro htj
          exact hright_exists ⟨j, htj⟩
        simp [hj]
      have hsplit_y :=
        problem6_sum_eq_pivot_add_right_part_of_before_zero
          y t h.sparse.y_before_pivot_zero
      have hy_t_eq : y t = 1 := by
        have hsum :
            (∑ j : Item n, y j) = y t + rightY := by
          simpa [rightY] using hsplit_y
        nlinarith [h.sparse.sum_y, hsum, hright_zero]
      let leftY' : ℝ :=
        ∑ j : Item n, if j.val < t.val then y' j else 0
      let rightY' : ℝ :=
        ∑ j : Item n, if t.val < j.val then y' j else 0
      have hleftY'_nonneg : 0 ≤ leftY' := by
        unfold leftY'
        refine Finset.sum_nonneg ?_
        intro j _hj
        by_cases hj : j.val < t.val
        · simp [hj, h'.y_nonneg j]
        · simp [hj]
      have hrightY'_nonneg : 0 ≤ rightY' := by
        unfold rightY'
        refine Finset.sum_nonneg ?_
        intro j _hj
        by_cases hj : t.val < j.val
        · simp [hj, h'.y_nonneg j]
        · simp [hj]
      have hsplit_y' :=
        problem6_sum_eq_left_part_add_pivot_add_right_part y' t
      have hy'_t_le_one : y' t ≤ 1 := by
        have hsum :
            (∑ j : Item n, y' j) =
              leftY' + y' t + rightY' := by
          simpa [leftY', rightY'] using hsplit_y'
        nlinarith [h'.sparse.sum_y, hsum, hleftY'_nonneg, hrightY'_nonneg]
      have hell_ge_comp : 1 - q ≤ ell := by
        have hleft_nonneg : 0 ≤ q * x t :=
          mul_nonneg hqpos.le (h.x_nonneg t)
        nlinarith [hitem_t, hy_t_eq, hleft_nonneg]
      have hell'_le_comp : ell' ≤ 1 - q' := by
        have hmul_le : (1 - q') * y' t ≤ (1 - q') * 1 :=
          mul_le_mul_of_nonneg_left hy'_t_le_one hq'comp_pos.le
        nlinarith [hitem_t', hmul_le]
      have hcomp_lt : 1 - q' < 1 - q := by
        nlinarith [hq_lt]
      linarith
  · let q : ℝ := pairShare alpha v t'
    let q' : ℝ := pairShare alpha' v t'
    have hqpos : 0 < q := by
      simpa [q] using pairShare_pos t' halpha0 halpha1 hpos
    have hq'pos : 0 < q' := by
      simpa [q'] using pairShare_pos t' halpha0' halpha1' hpos
    have hq'comp_nonneg : 0 ≤ 1 - q' := by
      exact (one_sub_pairShare_pos t' halpha0' halpha1' hpos).le
    have hq_lt : q < q' := by
      simpa [q, q'] using
        pairShare_strictMono_alpha t' halpha0 halpha1
          halpha0' halpha1' halpha_lt hpos
    have hy_t'_zero : y t' = 0 :=
      h.sparse.y_before_pivot_zero ht't
    have hitem_t' :
        q * x t' = ell := by
      have heq := h.sparse.item_eq t'
      rw [hy_t'_zero] at heq
      simpa [q] using heq
    have hitem_t'' :
        q' * x' t' + (1 - q') * y' t' = ell' := by
      simpa [q'] using h'.sparse.item_eq t'
    by_cases hleft_exists : ∃ j : Item n, j.val < t'.val
    · have hx_before_lt :
          ∀ {j : Item n}, j.val < t'.val → x' j < x j := by
        intro j hj
        have hjt : j.val < t.val := lt_trans hj ht't
        let qj : ℝ := pairShare alpha v j
        let qj' : ℝ := pairShare alpha' v j
        have hqj_lt : qj < qj' := by
          simpa [qj, qj'] using
            pairShare_strictMono_alpha j halpha0 halpha1
              halpha0' halpha1' halpha_lt hpos
        have hqj_pos : 0 < qj := by
          simpa [qj] using pairShare_pos j halpha0 halpha1 hpos
        have hqj'_pos : 0 < qj' := by
          simpa [qj'] using pairShare_pos j halpha0' halpha1' hpos
        have hsame_val_lt :
            ell' / qj' < ell' / qj := by
          rw [div_lt_div_iff₀ hqj'_pos hqj_pos]
          nlinarith [hell'_pos, hqj_lt]
        have hval_le_same_denom :
            ell' / qj ≤ ell / qj :=
          div_le_div_of_nonneg_right hell_ge hqj_pos.le
        rw [problem6SparseEqualized_x_before_eq
            halpha0' halpha1' hpos h'.sparse hj,
          problem6SparseEqualized_x_before_eq
            halpha0 halpha1 hpos h.sparse hjt]
        exact lt_of_lt_of_le hsame_val_lt hval_le_same_denom
      let leftX : ℝ :=
        ∑ j : Item n, if j.val < t'.val then x j else 0
      let leftX' : ℝ :=
        ∑ j : Item n, if j.val < t'.val then x' j else 0
      have hleft_lt : leftX' < leftX := by
        unfold leftX leftX'
        refine Finset.sum_lt_sum ?_ ?_
        · intro j _hj
          by_cases hj : j.val < t'.val
          · exact le_of_lt (by simpa [hj] using hx_before_lt hj)
          · simp [hj]
        · rcases hleft_exists with ⟨j, hj⟩
          exact ⟨j, by simp, by simpa [hj] using hx_before_lt hj⟩
      have hsplit_x' :=
        problem6_sum_eq_left_part_add_pivot_of_after_zero
          x' t' h'.sparse.x_after_pivot_zero
      have hx'_t_eq : x' t' = 1 - leftX' := by
        have hsum :
            (∑ j : Item n, x' j) = leftX' + x' t' := by
          simpa [leftX'] using hsplit_x'
        nlinarith [h'.sparse.sum_x, hsum]
      let rightX : ℝ :=
        ∑ j : Item n, if t'.val < j.val then x j else 0
      have hrightX_nonneg : 0 ≤ rightX := by
        unfold rightX
        refine Finset.sum_nonneg ?_
        intro j _hj
        by_cases hj : t'.val < j.val
        · simp [hj, h.x_nonneg j]
        · simp [hj]
      have hsplit_x :=
        problem6_sum_eq_left_part_add_pivot_add_right_part x t'
      have hprefix_le : leftX + x t' ≤ 1 := by
        have hsum :
            (∑ j : Item n, x j) =
              leftX + x t' + rightX := by
          simpa [leftX, rightX] using hsplit_x
        nlinarith [h.sparse.sum_x, hsum, hrightX_nonneg]
      have hx_t'_lt_x'_t' : x t' < x' t' := by
        nlinarith [hleft_lt, hx'_t_eq, hprefix_le]
      have hopt_ineq : q' * x' t' ≤ q * x t' := by
        have hright_nonneg : 0 ≤ (1 - q') * y' t' :=
          mul_nonneg hq'comp_nonneg (h'.y_nonneg t')
        have hx_le_ell' : q' * x' t' ≤ ell' := by
          calc
            q' * x' t' ≤ q' * x' t' + (1 - q') * y' t' :=
              le_add_of_nonneg_right hright_nonneg
            _ = ell' := hitem_t''
        calc
          q' * x' t' ≤ ell' := hx_le_ell'
          _ ≤ ell := hell_ge
          _ = q * x t' := hitem_t'.symm
      have hstrict_mul : q * x t' < q' * x' t' := by
        have hfirst : q * x t' < q * x' t' :=
          mul_lt_mul_of_pos_left hx_t'_lt_x'_t' hqpos
        have hsecond : q * x' t' < q' * x' t' :=
          mul_lt_mul_of_pos_right hq_lt h'.x_pivot_pos
        exact lt_trans hfirst hsecond
      exact (not_lt_of_ge hopt_ineq) hstrict_mul
    · let leftX' : ℝ :=
        ∑ j : Item n, if j.val < t'.val then x' j else 0
      have hleft_zero : leftX' = 0 := by
        unfold leftX'
        refine Finset.sum_eq_zero ?_
        intro j _hj
        have hj : ¬ j.val < t'.val := by
          intro hj
          exact hleft_exists ⟨j, hj⟩
        simp [hj]
      have hsplit_x' :=
        problem6_sum_eq_left_part_add_pivot_of_after_zero
          x' t' h'.sparse.x_after_pivot_zero
      have hx'_t_eq : x' t' = 1 := by
        have hsum :
            (∑ j : Item n, x' j) = leftX' + x' t' := by
          simpa [leftX'] using hsplit_x'
        linarith [h'.sparse.sum_x, hsum, hleft_zero]
      let leftX : ℝ :=
        ∑ j : Item n, if j.val < t'.val then x j else 0
      let rightX : ℝ :=
        ∑ j : Item n, if t'.val < j.val then x j else 0
      have hleftX_nonneg : 0 ≤ leftX := by
        unfold leftX
        refine Finset.sum_nonneg ?_
        intro j _hj
        by_cases hj : j.val < t'.val
        · simp [hj, h.x_nonneg j]
        · simp [hj]
      have hrightX_nonneg : 0 ≤ rightX := by
        unfold rightX
        refine Finset.sum_nonneg ?_
        intro j _hj
        by_cases hj : t'.val < j.val
        · simp [hj, h.x_nonneg j]
        · simp [hj]
      have hsplit_x :=
        problem6_sum_eq_left_part_add_pivot_add_right_part x t'
      have hx_t'_le_one : x t' ≤ 1 := by
        have hsum :
            (∑ j : Item n, x j) =
              leftX + x t' + rightX := by
          simpa [leftX, rightX] using hsplit_x
        linarith [h.sparse.sum_x, hsum, hleftX_nonneg, hrightX_nonneg]
      have hell_le_q : ell ≤ q := by
        have hmul_le : q * x t' ≤ q :=
          calc
            q * x t' ≤ q * 1 :=
              mul_le_mul_of_nonneg_left hx_t'_le_one hqpos.le
            _ = q := by norm_num
        calc
          ell = q * x t' := hitem_t'.symm
          _ ≤ q := hmul_le
      have hell'_ge_q' : q' ≤ ell' := by
        have hright_nonneg : 0 ≤ (1 - q') * y' t' :=
          mul_nonneg hq'comp_nonneg (h'.y_nonneg t')
        have hq'_eq_mul : q' = q' * x' t' := by
          rw [hx'_t_eq]
          norm_num
        have hmul_le_ell : q' * x' t' ≤ ell' := by
          rw [← hitem_t'']
          exact le_add_of_nonneg_right hright_nonneg
        exact hq'_eq_mul.le.trans hmul_le_ell
      have hq'_le_q : q' ≤ q := by
        exact hell'_ge_q'.trans (hell_ge.trans hell_le_q)
      exact (not_lt_of_ge hq'_le_q) hq_lt

/--
Appendix D, Lemma 7 for the paper's selected optimal Problem 6 policies:
`t(α) = max {j : x_j > 0}` is weakly increasing in `α`, conditional on the
Lemma 4 active-sparse bridge hypotheses.
-/
theorem lemma7_policyOptimal_lastActive_mono_of_alpha_lt
    {n : ℕ} [NeZero n]
    {alpha alpha' : ℝ} {v : Item n → ℝ}
    {ρ ρ' : TypePolicy 2 n} {ell ell' : ℝ}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_lt : alpha < alpha')
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hitem_eq :
      ∀ l : Item n,
        pairShare alpha v l * (ρ 0 l).toReal +
          (1 - pairShare alpha v l) * (ρ 1 l).toReal = ell)
    (hitem_eq' :
      ∀ l : Item n,
        pairShare alpha' v l * (ρ' 0 l).toReal +
          (1 - pairShare alpha' v l) * (ρ' 1 l).toReal = ell')
    (hopt : Problem6PolicyOptimal alpha v ρ ell)
    (hopt' : Problem6PolicyOptimal alpha' v ρ' ell')
    (hshared : TypePolicy.SharedItemsBound ρ)
    (hshared' : TypePolicy.SharedItemsBound ρ') :
    (TypePolicy.lastActiveTypeZero ρ).val ≤
      (TypePolicy.lastActiveTypeZero ρ').val := by
  let t : Item n := TypePolicy.lastActiveTypeZero ρ
  let t' : Item n := TypePolicy.lastActiveTypeZero ρ'
  have hsparse :
      Problem6SparseEqualizedActive alpha v t
        (fun l : Item n => (ρ 0 l).toReal)
        (fun l : Item n => (ρ 1 l).toReal) ell := by
    dsimp [t]
    exact problem6SparseEqualizedActive_of_policyOptimal_equalized_of_two_lt
      hn halpha0 halpha1 hpos hdec hitem_eq hopt hshared
  have hsparse' :
      Problem6SparseEqualizedActive alpha' v t'
        (fun l : Item n => (ρ' 0 l).toReal)
        (fun l : Item n => (ρ' 1 l).toReal) ell' := by
    dsimp [t']
    exact problem6SparseEqualizedActive_of_policyOptimal_equalized_of_two_lt
      hn halpha0' halpha1' hpos hdec hitem_eq' hopt' hshared'
  exact lemma7_sparseActive_pivot_mono_of_alpha_lt
    halpha0 halpha1 halpha0' halpha1' halpha_lt hpos hsparse hsparse'

/--
Appendix D, Lemma 7 for the paper's equality-form optimal BFS package.
-/
theorem lemma7_equalizedBasicOptimal_lastActive_mono_of_alpha_lt
    {n : ℕ} [NeZero n]
    {alpha alpha' : ℝ} {v : Item n → ℝ}
    {ρ ρ' : TypePolicy 2 n} {ell ell' : ℝ}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_lt : alpha < alpha')
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (h : Problem6EqualizedBasicOptimal alpha v ρ ell)
    (h' : Problem6EqualizedBasicOptimal alpha' v ρ' ell') :
    (TypePolicy.lastActiveTypeZero ρ).val ≤
      (TypePolicy.lastActiveTypeZero ρ').val := by
  exact lemma7_policyOptimal_lastActive_mono_of_alpha_lt
    hn halpha0 halpha1 halpha0' halpha1' halpha_lt
    hpos hdec h.item_eq h'.item_eq h.optimal h'.optimal
    (problem6_sharedItemsBound_of_equalizedBasicOptimal
      halpha0 halpha1 hpos h)
    (problem6_sharedItemsBound_of_equalizedBasicOptimal
      halpha0' halpha1' hpos h')

/--
Uniqueness of the selected active pivot for equality-form optimal BFS packages
at the same `α`.  This is the equality endpoint needed when Lemma 7 is used to
turn the paper's sets `A(t) = {α : t(α)=t}` into intervals.
-/
theorem problem6EqualizedBasicOptimal_lastActive_eq_of_same_alpha
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ}
    {ρ ρ' : TypePolicy 2 n} {ell ell' : ℝ}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (h : Problem6EqualizedBasicOptimal alpha v ρ ell)
    (h' : Problem6EqualizedBasicOptimal alpha v ρ' ell') :
    TypePolicy.lastActiveTypeZero ρ =
      TypePolicy.lastActiveTypeZero ρ' := by
  let t : Item n := TypePolicy.lastActiveTypeZero ρ
  let t' : Item n := TypePolicy.lastActiveTypeZero ρ'
  have hsparse :
      Problem6SparseEqualizedActive alpha v t
        (fun l : Item n => (ρ 0 l).toReal)
        (fun l : Item n => (ρ 1 l).toReal) ell := by
    dsimp [t]
    exact problem6SparseEqualizedActive_of_equalizedBasicOptimal_of_two_lt
      hn halpha0 halpha1 hpos hdec h
  have hsparse' :
      Problem6SparseEqualizedActive alpha v t'
        (fun l : Item n => (ρ' 0 l).toReal)
        (fun l : Item n => (ρ' 1 l).toReal) ell' := by
    dsimp [t']
    exact problem6SparseEqualizedActive_of_equalizedBasicOptimal_of_two_lt
      hn halpha0 halpha1 hpos hdec h'
  have hell_le : ell' ≤ ell := h.optimal.2 ρ' ell' h'.optimal.1
  have hell_ge : ell ≤ ell' := h'.optimal.2 ρ ell h.optimal.1
  have hell : ell = ell' := le_antisymm hell_ge hell_le
  have huniq :=
    problem6SparseEqualizedActive_eq_of_equal_value
      halpha0 halpha1 hpos hsparse hsparse' hell
  exact huniq.1

/--
Appendix D, Lemma 7 in non-strict form for equality-form optimal BFS packages:
the selected active pivot is weakly increasing in `α`.
-/
theorem lemma7_equalizedBasicOptimal_lastActive_mono_of_alpha_le
    {n : ℕ} [NeZero n]
    {alpha alpha' : ℝ} {v : Item n → ℝ}
    {ρ ρ' : TypePolicy 2 n} {ell ell' : ℝ}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (h : Problem6EqualizedBasicOptimal alpha v ρ ell)
    (h' : Problem6EqualizedBasicOptimal alpha' v ρ' ell') :
    (TypePolicy.lastActiveTypeZero ρ).val ≤
      (TypePolicy.lastActiveTypeZero ρ').val := by
  rcases lt_or_eq_of_le halpha_le with halpha_lt | halpha_eq
  · exact lemma7_equalizedBasicOptimal_lastActive_mono_of_alpha_lt
      hn halpha0 halpha1 halpha0' halpha1' halpha_lt hpos hdec h h'
  · subst alpha'
    have hpivot :=
      problem6EqualizedBasicOptimal_lastActive_eq_of_same_alpha
        hn halpha0 halpha1 hpos hdec h h'
    simpa [hpivot]

/--
Appendix D, Lemma 8 interval step: if the paper's selected active pivot agrees
at two endpoint parameters, then every selected equality-form optimal BFS at an
intermediate parameter has that same pivot.  This is the formal version of
`A(t)` being an interval, using Lemma 7 and same-`α` pivot uniqueness.
-/
theorem lemma8_selectedPivot_eq_of_between_equalizedBasicOptimal_endpoints
    {n : ℕ} [NeZero n]
    {alphaLeft alpha alphaRight : ℝ} {v : Item n → ℝ}
    {ρLeft ρ ρRight : TypePolicy 2 n} {ellLeft ell ellRight : ℝ}
    (hn : 2 < n)
    (halphaLeft0 : 0 < alphaLeft) (halphaLeft1 : alphaLeft < 1)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halphaRight0 : 0 < alphaRight) (halphaRight1 : alphaRight < 1)
    (hleft : alphaLeft ≤ alpha)
    (hright : alpha ≤ alphaRight)
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hpivot :
      TypePolicy.lastActiveTypeZero ρLeft =
        TypePolicy.lastActiveTypeZero ρRight)
    (hLeft :
      Problem6EqualizedBasicOptimal alphaLeft v ρLeft ellLeft)
    (h : Problem6EqualizedBasicOptimal alpha v ρ ell)
    (hRight :
      Problem6EqualizedBasicOptimal alphaRight v ρRight ellRight) :
    TypePolicy.lastActiveTypeZero ρ =
      TypePolicy.lastActiveTypeZero ρLeft := by
  have hleft_mono :
      (TypePolicy.lastActiveTypeZero ρLeft).val ≤
        (TypePolicy.lastActiveTypeZero ρ).val :=
    lemma7_equalizedBasicOptimal_lastActive_mono_of_alpha_le
      hn halphaLeft0 halphaLeft1 halpha0 halpha1 hleft
      hpos hdec hLeft h
  have hright_mono :
      (TypePolicy.lastActiveTypeZero ρ).val ≤
        (TypePolicy.lastActiveTypeZero ρLeft).val := by
    have hraw :
        (TypePolicy.lastActiveTypeZero ρ).val ≤
          (TypePolicy.lastActiveTypeZero ρRight).val :=
      lemma7_equalizedBasicOptimal_lastActive_mono_of_alpha_le
        hn halpha0 halpha1 halphaRight0 halphaRight1 hright
        hpos hdec h hRight
    simpa [hpivot] using hraw
  exact Fin.ext (le_antisymm hright_mono hleft_mono)

/--
Appendix D, Lemma 4 uniqueness for equalized optimal Problem 6 policies,
conditional on the paper's shared-item sparsity bound and `2 < n`.
-/
theorem problem6PolicyOptimal_equalized_unique_sparseActive_of_two_lt
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ}
    {ρ ρ' : TypePolicy 2 n} {ell ell' : ℝ}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hitem_eq :
      ∀ l : Item n,
        pairShare alpha v l * (ρ 0 l).toReal +
          (1 - pairShare alpha v l) * (ρ 1 l).toReal = ell)
    (hitem_eq' :
      ∀ l : Item n,
        pairShare alpha v l * (ρ' 0 l).toReal +
          (1 - pairShare alpha v l) * (ρ' 1 l).toReal = ell')
    (hopt : Problem6PolicyOptimal alpha v ρ ell)
    (hopt' : Problem6PolicyOptimal alpha v ρ' ell')
    (hshared : TypePolicy.SharedItemsBound ρ)
    (hshared' : TypePolicy.SharedItemsBound ρ') :
    ∃ t : Item n,
      Problem6SparseEqualizedActive alpha v t
        (fun l : Item n => (ρ 0 l).toReal)
        (fun l : Item n => (ρ 1 l).toReal) ell ∧
      Problem6SparseEqualizedActive alpha v t
        (fun l : Item n => (ρ' 0 l).toReal)
        (fun l : Item n => (ρ' 1 l).toReal) ell' ∧
      ell = ell' ∧
      (fun l : Item n => (ρ 0 l).toReal) =
        (fun l : Item n => (ρ' 0 l).toReal) ∧
      (fun l : Item n => (ρ 1 l).toReal) =
        (fun l : Item n => (ρ' 1 l).toReal) := by
  let t : Item n := TypePolicy.lastActiveTypeZero ρ
  let t' : Item n := TypePolicy.lastActiveTypeZero ρ'
  have hsparse :
      Problem6SparseEqualizedActive alpha v t
        (fun l : Item n => (ρ 0 l).toReal)
        (fun l : Item n => (ρ 1 l).toReal) ell := by
    dsimp [t]
    exact problem6SparseEqualizedActive_of_policyOptimal_equalized_of_two_lt
      hn halpha0 halpha1 hpos hdec hitem_eq hopt hshared
  have hsparse' :
      Problem6SparseEqualizedActive alpha v t'
        (fun l : Item n => (ρ' 0 l).toReal)
        (fun l : Item n => (ρ' 1 l).toReal) ell' := by
    dsimp [t']
    exact problem6SparseEqualizedActive_of_policyOptimal_equalized_of_two_lt
      hn halpha0 halpha1 hpos hdec hitem_eq' hopt' hshared'
  have hell_le : ell' ≤ ell := hopt.2 ρ' ell' hopt'.1
  have hell_ge : ell ≤ ell' := hopt'.2 ρ ell hopt.1
  have hell : ell = ell' := le_antisymm hell_ge hell_le
  have huniq :=
    problem6SparseEqualizedActive_eq_of_equal_value
      halpha0 halpha1 hpos hsparse hsparse' hell
  rcases huniq with ⟨hpivot, hell_eq, hx_eq, hy_eq⟩
  have hsparse'_same :
      Problem6SparseEqualizedActive alpha v t
        (fun l : Item n => (ρ' 0 l).toReal)
        (fun l : Item n => (ρ' 1 l).toReal) ell' := by
    simpa [hpivot] using hsparse'
  exact ⟨t, hsparse, hsparse'_same, hell_eq, hx_eq, hy_eq⟩

/--
Appendix D, Lemma 4 uniqueness for the paper's equality-form optimal BFS
package.
-/
theorem problem6EqualizedBasicOptimal_unique_sparseActive_of_two_lt
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ}
    {ρ ρ' : TypePolicy 2 n} {ell ell' : ℝ}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (h : Problem6EqualizedBasicOptimal alpha v ρ ell)
    (h' : Problem6EqualizedBasicOptimal alpha v ρ' ell') :
    ∃ t : Item n,
      Problem6SparseEqualizedActive alpha v t
        (fun l : Item n => (ρ 0 l).toReal)
        (fun l : Item n => (ρ 1 l).toReal) ell ∧
      Problem6SparseEqualizedActive alpha v t
        (fun l : Item n => (ρ' 0 l).toReal)
        (fun l : Item n => (ρ' 1 l).toReal) ell' ∧
      ell = ell' ∧
      (fun l : Item n => (ρ 0 l).toReal) =
        (fun l : Item n => (ρ' 0 l).toReal) ∧
      (fun l : Item n => (ρ 1 l).toReal) =
        (fun l : Item n => (ρ' 1 l).toReal) := by
  exact problem6PolicyOptimal_equalized_unique_sparseActive_of_two_lt
    hn halpha0 halpha1 hpos hdec h.item_eq h'.item_eq h.optimal h'.optimal
    (problem6_sharedItemsBound_of_equalizedBasicOptimal
      halpha0 halpha1 hpos h)
    (problem6_sharedItemsBound_of_equalizedBasicOptimal
      halpha0 halpha1 hpos h')

/--
Appendix D, Lemma 10, selected-pivot bridge at `α = 1/2`: if a midpoint
candidate has denominator bounds and every later nonnegative closed pivot has
weakly smaller closed value, then an equalized optimal policy cannot select a
pivot after that candidate.
-/
theorem lemma10_half_optimal_lastActive_le_candidate
    {n : ℕ} [NeZero n]
    {v : Item n → ℝ} {ρ : TypePolicy 2 n} {ell : ℝ} {c : Item n}
    (hn : 2 < n)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hboundsc : Problem6ClosedPivotDenominatorBounds (1 / 2) v c)
    (hcompare :
      ∀ {t : Item n}, c.val < t.val →
        Problem6ClosedNonnegativePivots (1 / 2) v t →
          problem6ClosedValue (1 / 2) v t ≤
            problem6ClosedValue (1 / 2) v c)
    (hitem_eq :
      ∀ l : Item n,
        pairShare (1 / 2) v l * (ρ 0 l).toReal +
          (1 - pairShare (1 / 2) v l) * (ρ 1 l).toReal = ell)
    (hopt : Problem6PolicyOptimal (1 / 2) v ρ ell)
    (hshared : TypePolicy.SharedItemsBound ρ) :
    (TypePolicy.lastActiveTypeZero ρ).val ≤ c.val := by
  let t : Item n := TypePolicy.lastActiveTypeZero ρ
  have hsparse :
      Problem6SparseEqualizedActive (1 / 2) v t
        (fun l : Item n => (ρ 0 l).toReal)
        (fun l : Item n => (ρ 1 l).toReal) ell := by
    dsimp [t]
    exact problem6SparseEqualizedActive_of_policyOptimal_equalized_of_two_lt
      hn (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) hpos hdec hitem_eq hopt hshared
  have hvalue :
      ell = problem6ClosedValue (1 / 2) v t :=
    problem6SparseEqualized_value_eq_closed
      (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) hpos hsparse.sparse
  have hpivt :
      Problem6ClosedNonnegativePivots (1 / 2) v t :=
    problem6ClosedNonnegativePivots_of_sparseEqualizedActive
      (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) hpos hsparse
  let hpivc : Problem6ClosedNonnegativePivots (1 / 2) v c :=
    problem6ClosedNonnegativePivots_of_denominatorBounds
      (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) hpos hboundsc
  by_contra hnot
  have hct : c.val < t.val := by
    dsimp [t] at hnot ⊢
    omega
  have hcompare_tc :
      problem6ClosedValue (1 / 2) v t ≤
        problem6ClosedValue (1 / 2) v c :=
    hcompare hct hpivt
  have hfeas_c :
      problem6LPFeasible (1 / 2) v
        (problem6ClosedPolicy (1 / 2) v c
          (by norm_num : (0 : ℝ) < 1 / 2)
          (by norm_num : (1 / 2 : ℝ) < 1) hpos hpivc)
        (problem6ClosedValue (1 / 2) v c) :=
    problem6ClosedPolicy_feasible_of_denominatorBounds
      (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) hpos hboundsc
  have hle_c_ell :
      problem6ClosedValue (1 / 2) v c ≤ ell :=
    hopt.2
      (problem6ClosedPolicy (1 / 2) v c
        (by norm_num : (0 : ℝ) < 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1) hpos hpivc)
      (problem6ClosedValue (1 / 2) v c) hfeas_c
  have hle_ell_c :
      ell ≤ problem6ClosedValue (1 / 2) v c := by
    rw [hvalue]
    exact hcompare_tc
  have hell_c :
      problem6ClosedValue (1 / 2) v c = ell :=
    le_antisymm hle_c_ell hle_ell_c
  exact problem6SparseEqualized_cross_pivot_contradiction_of_right_pivot_active
    (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1) hpos hct
    (problem6Closed_sparseEqualized c
      (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) hpos)
    hsparse.sparse hell_c
    (problem6ClosedY_nonneg
      (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) hpos hpivc c)
    hsparse.x_nonneg hsparse.x_pivot_pos

/--
Appendix D, Lemma 10, selected-pivot bridge at `α = 1/2`, odd-center case.
-/
theorem lemma10_half_optimal_lastActive_le_center
    {n : ℕ} [NeZero n]
    {v : Item n → ℝ} {ρ : TypePolicy 2 n} {ell : ℝ} {c : Item n}
    (hn : 2 < n)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter : c.val = (reverseItem c).val)
    (hitem_eq :
      ∀ l : Item n,
        pairShare (1 / 2) v l * (ρ 0 l).toReal +
          (1 - pairShare (1 / 2) v l) * (ρ 1 l).toReal = ell)
    (hopt : Problem6PolicyOptimal (1 / 2) v ρ ell)
    (hshared : TypePolicy.SharedItemsBound ρ) :
    (TypePolicy.lastActiveTypeZero ρ).val ≤ c.val := by
  exact lemma10_half_optimal_lastActive_le_candidate
    hn hpos hdec
    (problem6ClosedPivotDenominatorBounds_half_center
      (v := v) (t := c) hpos hcenter)
    (fun hct hpivot =>
      problem6ClosedValue_le_of_center_candidate_before
        hpos hcenter hct hpivot)
    hitem_eq hopt hshared

/--
Appendix D, Lemma 10, selected-pivot bridge at `α = 1/2`, even-center case.
-/
theorem lemma10_half_optimal_lastActive_le_succ_center
    {n : ℕ} [NeZero n]
    {v : Item n → ℝ} {ρ : TypePolicy 2 n} {ell : ℝ} {c : Item n}
    (hn : 2 < n)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hsucc : c.val + 1 = (reverseItem c).val)
    (hitem_eq :
      ∀ l : Item n,
        pairShare (1 / 2) v l * (ρ 0 l).toReal +
          (1 - pairShare (1 / 2) v l) * (ρ 1 l).toReal = ell)
    (hopt : Problem6PolicyOptimal (1 / 2) v ρ ell)
    (hshared : TypePolicy.SharedItemsBound ρ) :
    (TypePolicy.lastActiveTypeZero ρ).val ≤ c.val := by
  exact lemma10_half_optimal_lastActive_le_candidate
    hn hpos hdec
    (problem6ClosedPivotDenominatorBounds_half_succ_center
      (v := v) (t := c) hpos hsucc)
    (fun hct hpivot =>
      problem6ClosedValue_le_of_succ_center_candidate_before
        hpos hsucc hct hpivot)
    hitem_eq hopt hshared

/--
Appendix D, Lemma 10 stitched with Lemma 7, odd-center case: for
`α ≤ 1/2`, the selected pivot is no later than the exact center, conditional on
a supplied equalized optimum at the midpoint.
-/
theorem lemma10_alpha_le_half_optimal_lastActive_le_center
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ}
    {ρ ρhalf : TypePolicy 2 n} {ell ellHalf : ℝ} {c : Item n}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha_half : alpha ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter : c.val = (reverseItem c).val)
    (hitem_eq :
      ∀ l : Item n,
        pairShare alpha v l * (ρ 0 l).toReal +
          (1 - pairShare alpha v l) * (ρ 1 l).toReal = ell)
    (hitem_eq_half :
      ∀ l : Item n,
        pairShare (1 / 2) v l * (ρhalf 0 l).toReal +
          (1 - pairShare (1 / 2) v l) * (ρhalf 1 l).toReal = ellHalf)
    (hopt : Problem6PolicyOptimal alpha v ρ ell)
    (hopt_half : Problem6PolicyOptimal (1 / 2) v ρhalf ellHalf)
    (hshared : TypePolicy.SharedItemsBound ρ)
    (hshared_half : TypePolicy.SharedItemsBound ρhalf) :
    (TypePolicy.lastActiveTypeZero ρ).val ≤ c.val := by
  rcases lt_or_eq_of_le halpha_half with halpha_lt_half | halpha_eq_half
  · have hmono :
        (TypePolicy.lastActiveTypeZero ρ).val ≤
          (TypePolicy.lastActiveTypeZero ρhalf).val :=
      lemma7_policyOptimal_lastActive_mono_of_alpha_lt
        hn halpha0 halpha1
        (by norm_num : (0 : ℝ) < 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)
        halpha_lt_half hpos hdec hitem_eq hitem_eq_half
        hopt hopt_half hshared hshared_half
    have hhalf :
        (TypePolicy.lastActiveTypeZero ρhalf).val ≤ c.val :=
      lemma10_half_optimal_lastActive_le_center
        hn hpos hdec hcenter hitem_eq_half hopt_half hshared_half
    exact le_trans hmono hhalf
  · subst alpha
    exact lemma10_half_optimal_lastActive_le_center
      hn hpos hdec hcenter hitem_eq hopt hshared

/--
Appendix D, Lemma 10 stitched with Lemma 7 for the paper's equality-form
optimal BFS package, odd-center case.
-/
theorem lemma10_alpha_le_half_equalizedBasicOptimal_lastActive_le_center
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ}
    {ρ ρhalf : TypePolicy 2 n} {ell ellHalf : ℝ} {c : Item n}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha_half : alpha ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter : c.val = (reverseItem c).val)
    (h : Problem6EqualizedBasicOptimal alpha v ρ ell)
    (hhalf : Problem6EqualizedBasicOptimal (1 / 2) v ρhalf ellHalf) :
    (TypePolicy.lastActiveTypeZero ρ).val ≤ c.val := by
  exact lemma10_alpha_le_half_optimal_lastActive_le_center
    hn halpha0 halpha1 halpha_half hpos hdec hcenter
    h.item_eq hhalf.item_eq h.optimal hhalf.optimal
    (problem6_sharedItemsBound_of_equalizedBasicOptimal
      halpha0 halpha1 hpos h)
    (problem6_sharedItemsBound_of_equalizedBasicOptimal
      (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) hpos hhalf)

/--
Appendix D, Lemma 10 stitched with Lemma 7, even-center case: for
`α ≤ 1/2`, the selected pivot is no later than the item immediately before its
mirror, conditional on a supplied equalized optimum at the midpoint.
-/
theorem lemma10_alpha_le_half_optimal_lastActive_le_succ_center
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ}
    {ρ ρhalf : TypePolicy 2 n} {ell ellHalf : ℝ} {c : Item n}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha_half : alpha ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hsucc : c.val + 1 = (reverseItem c).val)
    (hitem_eq :
      ∀ l : Item n,
        pairShare alpha v l * (ρ 0 l).toReal +
          (1 - pairShare alpha v l) * (ρ 1 l).toReal = ell)
    (hitem_eq_half :
      ∀ l : Item n,
        pairShare (1 / 2) v l * (ρhalf 0 l).toReal +
          (1 - pairShare (1 / 2) v l) * (ρhalf 1 l).toReal = ellHalf)
    (hopt : Problem6PolicyOptimal alpha v ρ ell)
    (hopt_half : Problem6PolicyOptimal (1 / 2) v ρhalf ellHalf)
    (hshared : TypePolicy.SharedItemsBound ρ)
    (hshared_half : TypePolicy.SharedItemsBound ρhalf) :
    (TypePolicy.lastActiveTypeZero ρ).val ≤ c.val := by
  rcases lt_or_eq_of_le halpha_half with halpha_lt_half | halpha_eq_half
  · have hmono :
        (TypePolicy.lastActiveTypeZero ρ).val ≤
          (TypePolicy.lastActiveTypeZero ρhalf).val :=
      lemma7_policyOptimal_lastActive_mono_of_alpha_lt
        hn halpha0 halpha1
        (by norm_num : (0 : ℝ) < 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)
        halpha_lt_half hpos hdec hitem_eq hitem_eq_half
        hopt hopt_half hshared hshared_half
    have hhalf :
        (TypePolicy.lastActiveTypeZero ρhalf).val ≤ c.val :=
      lemma10_half_optimal_lastActive_le_succ_center
        hn hpos hdec hsucc hitem_eq_half hopt_half hshared_half
    exact le_trans hmono hhalf
  · subst alpha
    exact lemma10_half_optimal_lastActive_le_succ_center
      hn hpos hdec hsucc hitem_eq hopt hshared

/--
Appendix D, Lemma 10 stitched with Lemma 7 for the paper's equality-form
optimal BFS package, even-center case.
-/
theorem lemma10_alpha_le_half_equalizedBasicOptimal_lastActive_le_succ_center
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ}
    {ρ ρhalf : TypePolicy 2 n} {ell ellHalf : ℝ} {c : Item n}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha_half : alpha ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hsucc : c.val + 1 = (reverseItem c).val)
    (h : Problem6EqualizedBasicOptimal alpha v ρ ell)
    (hhalf : Problem6EqualizedBasicOptimal (1 / 2) v ρhalf ellHalf) :
    (TypePolicy.lastActiveTypeZero ρ).val ≤ c.val := by
  exact lemma10_alpha_le_half_optimal_lastActive_le_succ_center
    hn halpha0 halpha1 halpha_half hpos hdec hsucc
    h.item_eq hhalf.item_eq h.optimal hhalf.optimal
    (problem6_sharedItemsBound_of_equalizedBasicOptimal
      halpha0 halpha1 hpos h)
    (problem6_sharedItemsBound_of_equalizedBasicOptimal
      (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) hpos hhalf)

/--
Appendix D, Lemma 10 consequence, odd-center case: every selected pivot for
`α ≤ 1/2` lies at or before its mirror.
-/
theorem lemma10_alpha_le_half_equalizedBasicOptimal_lastActive_le_reverse_center
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ}
    {ρ ρhalf : TypePolicy 2 n} {ell ellHalf : ℝ} {c : Item n}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha_half : alpha ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter : c.val = (reverseItem c).val)
    (h : Problem6EqualizedBasicOptimal alpha v ρ ell)
    (hhalf : Problem6EqualizedBasicOptimal (1 / 2) v ρhalf ellHalf) :
    (TypePolicy.lastActiveTypeZero ρ).val ≤
      (reverseItem (TypePolicy.lastActiveTypeZero ρ)).val := by
  let t : Item n := TypePolicy.lastActiveTypeZero ρ
  have ht_le_c : t.val ≤ c.val := by
    dsimp [t]
    exact lemma10_alpha_le_half_equalizedBasicOptimal_lastActive_le_center
      hn halpha0 halpha1 halpha_half hpos hdec hcenter h hhalf
  have hc_arith : 2 * c.val + 1 = n :=
    (val_eq_reverseItem_iff c).mp hcenter
  have ht_arith : 2 * t.val + 1 ≤ n := by omega
  exact (val_le_reverseItem_iff t).mpr ht_arith

/--
Appendix D, Lemma 10 consequence, even-center case: every selected pivot for
`α ≤ 1/2` lies at or before its mirror.
-/
theorem lemma10_alpha_le_half_equalizedBasicOptimal_lastActive_le_reverse_succ_center
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ}
    {ρ ρhalf : TypePolicy 2 n} {ell ellHalf : ℝ} {c : Item n}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha_half : alpha ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hsucc : c.val + 1 = (reverseItem c).val)
    (h : Problem6EqualizedBasicOptimal alpha v ρ ell)
    (hhalf : Problem6EqualizedBasicOptimal (1 / 2) v ρhalf ellHalf) :
    (TypePolicy.lastActiveTypeZero ρ).val ≤
      (reverseItem (TypePolicy.lastActiveTypeZero ρ)).val := by
  let t : Item n := TypePolicy.lastActiveTypeZero ρ
  have ht_le_c : t.val ≤ c.val := by
    dsimp [t]
    exact lemma10_alpha_le_half_equalizedBasicOptimal_lastActive_le_succ_center
      hn halpha0 halpha1 halpha_half hpos hdec hsucc h hhalf
  have hc_arith : 2 * c.val + 2 = n := by
    simp [reverseItem] at hsucc
    omega
  have ht_arith : 2 * t.val + 1 ≤ n := by omega
  exact (val_le_reverseItem_iff t).mpr ht_arith

/--
A certificate that a proposed Problem 6 policy and value solve the finite LP:
the policy attains `ell`, and no feasible policy can exceed `ell`.
-/
structure Problem6OptimalityCertificate {n : ℕ} [NeZero n]
    (alpha : ℝ) (v : Item n → ℝ) (ell : ℝ) where
  policy : TypePolicy 2 n
  feasible : problem6LPFeasible alpha v policy ell
  upper_bound :
    ∀ (ρ : TypePolicy 2 n) (ell' : ℝ),
      problem6LPFeasible alpha v ρ ell' → ell' ≤ ell

/--
Closed-form certificate target for Problem 6: denominator bounds make the
closed coordinates a feasible policy, and the remaining field is the LP
upper-bound proof for the paper's proposed value.
-/
structure Problem6ClosedOptimalityCertificate {n : ℕ} [NeZero n]
    (alpha : ℝ) (v : Item n → ℝ) (t : Item n) : Prop where
  denominator_bounds : Problem6ClosedPivotDenominatorBounds alpha v t
  upper_bound :
    ∀ (ρ : TypePolicy 2 n) (ell' : ℝ),
      problem6LPFeasible alpha v ρ ell' →
        ell' ≤ problem6ClosedValue alpha v t

/--
Dual weights for the closed-form Problem 6 solution.  These are the finite
dual variables implicit in Lemma 5: left items get weight
`λ q_t / q_j`, the pivot gets `λ`, and right items get
`λ (1-q_t)/(1-q_j)`.
-/
noncomputable def problem6ClosedDualWeight {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) (t j : Item n) : ℝ :=
  if j.val < t.val then
    problem6ClosedValue alpha v t * pairShare alpha v t /
      pairShare alpha v j
  else if j = t then
    problem6ClosedValue alpha v t
  else
    problem6ClosedValue alpha v t * (1 - pairShare alpha v t) /
      (1 - pairShare alpha v j)

theorem problem6ClosedDualWeight_before {n : ℕ}
    {alpha : ℝ} {v : Item n → ℝ} {t j : Item n}
    (hj : j.val < t.val) :
    problem6ClosedDualWeight alpha v t j =
      problem6ClosedValue alpha v t * pairShare alpha v t /
        pairShare alpha v j := by
  simp [problem6ClosedDualWeight, hj]

theorem problem6ClosedDualWeight_at {n : ℕ}
    {alpha : ℝ} {v : Item n → ℝ} {t : Item n} :
    problem6ClosedDualWeight alpha v t t =
      problem6ClosedValue alpha v t := by
  simp [problem6ClosedDualWeight]

theorem problem6ClosedDualWeight_after {n : ℕ}
    {alpha : ℝ} {v : Item n → ℝ} {t j : Item n}
    (hj : t.val < j.val) :
    problem6ClosedDualWeight alpha v t j =
      problem6ClosedValue alpha v t * (1 - pairShare alpha v t) /
        (1 - pairShare alpha v j) := by
  have hnlt : ¬ j.val < t.val := by omega
  have hne : j ≠ t := by
    intro h
    subst h
    omega
  simp [problem6ClosedDualWeight, hnlt, hne]

theorem problem6ClosedDualWeight_nonneg {n : ℕ}
    {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j) (j : Item n) :
    0 ≤ problem6ClosedDualWeight alpha v t j := by
  by_cases hjlt : j.val < t.val
  · rw [problem6ClosedDualWeight_before hjlt]
    exact div_nonneg
      (mul_nonneg
        (problem6ClosedValue_pos t halpha0 halpha1 hpos).le
        (pairShare_pos t halpha0 halpha1 hpos).le)
      (pairShare_pos j halpha0 halpha1 hpos).le
  · by_cases hjeq : j = t
    · subst j
      rw [problem6ClosedDualWeight_at]
      exact (problem6ClosedValue_pos t halpha0 halpha1 hpos).le
    · have hjgt : t.val < j.val := by
        have hne_val : j.val ≠ t.val := by
          intro hval
          exact hjeq (Fin.ext hval)
        omega
      rw [problem6ClosedDualWeight_after hjgt]
      exact div_nonneg
        (mul_nonneg
          (problem6ClosedValue_pos t halpha0 halpha1 hpos).le
          (one_sub_pairShare_pos t halpha0 halpha1 hpos).le)
        (one_sub_pairShare_pos j halpha0 halpha1 hpos).le

private theorem problem6ClosedDualWeight_left_part_sum_eq {n : ℕ}
    {alpha : ℝ} {v : Item n → ℝ} {t : Item n} :
    (∑ j : Item n, if j.val < t.val then
        problem6ClosedDualWeight alpha v t j else 0) =
      problem6ClosedValue alpha v t * pairShare alpha v t *
        problem6LeftSum alpha v t := by
  unfold problem6LeftSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro j _hj
  by_cases hjt : j.val < t.val
  · simp [hjt, problem6ClosedDualWeight_before hjt, div_eq_mul_inv,
      mul_comm, mul_left_comm]
  · simp [hjt]

private theorem problem6ClosedDualWeight_right_part_sum_eq {n : ℕ}
    {alpha : ℝ} {v : Item n → ℝ} {t : Item n} :
    (∑ j : Item n, if t.val < j.val then
        problem6ClosedDualWeight alpha v t j else 0) =
      problem6ClosedValue alpha v t * (1 - pairShare alpha v t) *
        problem6RightSum alpha v t := by
  unfold problem6RightSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro j _hj
  by_cases htj : t.val < j.val
  · simp [htj, problem6ClosedDualWeight_after htj, div_eq_mul_inv,
      mul_comm, mul_left_comm]
  · simp [htj]

theorem problem6ClosedDualWeight_sum_eq_one {n : ℕ}
    {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j) :
    (∑ j : Item n, problem6ClosedDualWeight alpha v t j) = 1 := by
  have hsplit :=
    problem6_sum_eq_left_part_add_pivot_add_right_part
      (problem6ClosedDualWeight alpha v t) t
  have hleft :
      (∑ j : Item n, if j.val < t.val then
          problem6ClosedDualWeight alpha v t j else 0) =
        problem6ClosedValue alpha v t * pairShare alpha v t *
          problem6LeftSum alpha v t :=
    problem6ClosedDualWeight_left_part_sum_eq
  have hright :
      (∑ j : Item n, if t.val < j.val then
          problem6ClosedDualWeight alpha v t j else 0) =
        problem6ClosedValue alpha v t * (1 - pairShare alpha v t) *
          problem6RightSum alpha v t :=
    problem6ClosedDualWeight_right_part_sum_eq
  have hDpos := problem6ClosedDenominator_pos t halpha0 halpha1 hpos
  have hDmul :
      problem6ClosedValue alpha v t *
          problem6ClosedDenominator alpha v t = 1 := by
    unfold problem6ClosedValue
    field_simp [ne_of_gt hDpos]
  rw [hsplit, hleft, hright, problem6ClosedDualWeight_at]
  unfold problem6ClosedDenominator at hDmul
  nlinarith

/--
Problem 6 closed-form dual feasibility: the `x_j` coefficients of the dual
weighted item constraints are bounded by `λ q_t`.
-/
theorem problem6ClosedDualWeight_pairShare_le {n : ℕ}
    {alpha : ℝ} {v : Item n → ℝ} {t j : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v) :
    problem6ClosedDualWeight alpha v t j * pairShare alpha v j ≤
      problem6ClosedValue alpha v t * pairShare alpha v t := by
  by_cases hjlt : j.val < t.val
  · rw [problem6ClosedDualWeight_before hjlt]
    have hqj : pairShare alpha v j ≠ 0 :=
      ne_of_gt (pairShare_pos j halpha0 halpha1 hpos)
    calc
      (problem6ClosedValue alpha v t * pairShare alpha v t /
          pairShare alpha v j) * pairShare alpha v j =
          problem6ClosedValue alpha v t * pairShare alpha v t := by
        field_simp [hqj]
      _ ≤ problem6ClosedValue alpha v t * pairShare alpha v t := le_rfl
  · by_cases hjeq : j = t
    · subst j
      rw [problem6ClosedDualWeight_at]
    · have htj : t.val < j.val := by
        have hne_val : j.val ≠ t.val := by
          intro hval
          exact hjeq (Fin.ext hval)
        omega
      have hq_le : pairShare alpha v j ≤ pairShare alpha v t :=
        (pairShare_strictAnti_index
          halpha0 halpha1 hpos hdec htj).le
      have hcoeff :
          ((1 - pairShare alpha v t) /
              (1 - pairShare alpha v j)) *
            pairShare alpha v j ≤ pairShare alpha v t :=
        problem6Dual_right_coeff_le
          (pairShare_lt_one j halpha0 halpha1 hpos) hq_le
      have hmul :=
        mul_le_mul_of_nonneg_left hcoeff
          (problem6ClosedValue_pos t halpha0 halpha1 hpos).le
      rw [problem6ClosedDualWeight_after htj]
      convert hmul using 1
      ring

/--
Problem 6 closed-form dual feasibility: the `y_j` coefficients of the dual
weighted item constraints are bounded by `λ (1-q_t)`.
-/
theorem problem6ClosedDualWeight_one_sub_pairShare_le {n : ℕ}
    {alpha : ℝ} {v : Item n → ℝ} {t j : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v) :
    problem6ClosedDualWeight alpha v t j *
        (1 - pairShare alpha v j) ≤
      problem6ClosedValue alpha v t *
        (1 - pairShare alpha v t) := by
  by_cases hjlt : j.val < t.val
  · have hqt_le : pairShare alpha v t ≤ pairShare alpha v j :=
      (pairShare_strictAnti_index
        halpha0 halpha1 hpos hdec hjlt).le
    have hcoeff :
        (pairShare alpha v t / pairShare alpha v j) *
          (1 - pairShare alpha v j) ≤
            1 - pairShare alpha v t :=
      problem6Dual_left_coeff_le
        (pairShare_pos j halpha0 halpha1 hpos)
        (pairShare_lt_one j halpha0 halpha1 hpos) hqt_le
    have hmul :=
      mul_le_mul_of_nonneg_left hcoeff
        (problem6ClosedValue_pos t halpha0 halpha1 hpos).le
    rw [problem6ClosedDualWeight_before hjlt]
    convert hmul using 1
    ring
  · by_cases hjeq : j = t
    · subst j
      rw [problem6ClosedDualWeight_at]
    · have htj : t.val < j.val := by
        have hne_val : j.val ≠ t.val := by
          intro hval
          exact hjeq (Fin.ext hval)
        omega
      rw [problem6ClosedDualWeight_after htj]
      have hqj : 1 - pairShare alpha v j ≠ 0 :=
        ne_of_gt (one_sub_pairShare_pos j halpha0 halpha1 hpos)
      calc
        (problem6ClosedValue alpha v t *
            (1 - pairShare alpha v t) /
            (1 - pairShare alpha v j)) *
            (1 - pairShare alpha v j) =
            problem6ClosedValue alpha v t *
              (1 - pairShare alpha v t) := by
          field_simp [hqj]
        _ ≤ problem6ClosedValue alpha v t *
              (1 - pairShare alpha v t) := le_rfl

/-- The closed dual has strict `x`-coefficient slack after the pivot. -/
theorem problem6ClosedDualWeight_pairShare_lt_of_after {n : ℕ}
    {alpha : ℝ} {v : Item n → ℝ} {t j : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (htj : t.val < j.val) :
    problem6ClosedDualWeight alpha v t j * pairShare alpha v j <
      problem6ClosedValue alpha v t * pairShare alpha v t := by
  have hq_lt : pairShare alpha v j < pairShare alpha v t :=
    pairShare_strictAnti_index halpha0 halpha1 hpos hdec htj
  have hcoeff :
      ((1 - pairShare alpha v t) /
          (1 - pairShare alpha v j)) * pairShare alpha v j <
        pairShare alpha v t :=
    problem6Dual_right_coeff_lt
      (pairShare_lt_one j halpha0 halpha1 hpos) hq_lt
  have hmul := mul_lt_mul_of_pos_left hcoeff
    (problem6ClosedValue_pos t halpha0 halpha1 hpos)
  rw [problem6ClosedDualWeight_after htj]
  convert hmul using 1 <;> ring

/-- The closed dual has strict `y`-coefficient slack before the pivot. -/
theorem problem6ClosedDualWeight_one_sub_pairShare_lt_of_before {n : ℕ}
    {alpha : ℝ} {v : Item n → ℝ} {t j : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hjt : j.val < t.val) :
    problem6ClosedDualWeight alpha v t j *
        (1 - pairShare alpha v j) <
      problem6ClosedValue alpha v t *
        (1 - pairShare alpha v t) := by
  have hq_lt : pairShare alpha v t < pairShare alpha v j :=
    pairShare_strictAnti_index halpha0 halpha1 hpos hdec hjt
  have hcoeff :
      (pairShare alpha v t / pairShare alpha v j) *
          (1 - pairShare alpha v j) <
        1 - pairShare alpha v t :=
    problem6Dual_left_coeff_lt
      (pairShare_pos j halpha0 halpha1 hpos)
      (pairShare_lt_one j halpha0 halpha1 hpos) hq_lt
  have hmul := mul_lt_mul_of_pos_left hcoeff
    (problem6ClosedValue_pos t halpha0 halpha1 hpos)
  rw [problem6ClosedDualWeight_before hjt]
  convert hmul using 1 <;> ring

/-- Problem 6 dual `x`-budget bound. -/
theorem problem6ClosedDual_x_budget_le {n : ℕ}
    {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (ρ : TypePolicy 2 n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v) :
    (∑ j : Item n,
        problem6ClosedDualWeight alpha v t j *
          pairShare alpha v j * (ρ 0 j).toReal) ≤
      problem6ClosedValue alpha v t * pairShare alpha v t := by
  calc
    (∑ j : Item n,
        problem6ClosedDualWeight alpha v t j *
          pairShare alpha v j * (ρ 0 j).toReal)
        ≤ ∑ j : Item n,
            (problem6ClosedValue alpha v t * pairShare alpha v t) *
              (ρ 0 j).toReal := by
          refine Finset.sum_le_sum ?_
          intro j _hj
          exact mul_le_mul_of_nonneg_right
            (problem6ClosedDualWeight_pairShare_le
              halpha0 halpha1 hpos hdec)
            (ENNReal.toReal_nonneg)
    _ = problem6ClosedValue alpha v t * pairShare alpha v t := by
          rw [← Finset.mul_sum, problem6_typeZero_sum_eq_one]
          ring

/-- Problem 6 dual `y`-budget bound. -/
theorem problem6ClosedDual_y_budget_le {n : ℕ}
    {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (ρ : TypePolicy 2 n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v) :
    (∑ j : Item n,
        problem6ClosedDualWeight alpha v t j *
          (1 - pairShare alpha v j) * (ρ 1 j).toReal) ≤
      problem6ClosedValue alpha v t *
        (1 - pairShare alpha v t) := by
  calc
    (∑ j : Item n,
        problem6ClosedDualWeight alpha v t j *
          (1 - pairShare alpha v j) * (ρ 1 j).toReal)
        ≤ ∑ j : Item n,
            (problem6ClosedValue alpha v t *
              (1 - pairShare alpha v t)) * (ρ 1 j).toReal := by
          refine Finset.sum_le_sum ?_
          intro j _hj
          exact mul_le_mul_of_nonneg_right
            (problem6ClosedDualWeight_one_sub_pairShare_le
              halpha0 halpha1 hpos hdec)
            (ENNReal.toReal_nonneg)
    _ = problem6ClosedValue alpha v t *
          (1 - pairShare alpha v t) := by
          rw [← Finset.mul_sum, problem6_typeOne_sum_eq_one]
          ring

/-- A positive type-`0` coordinate after the pivot makes the dual budget strict. -/
theorem problem6ClosedDual_x_budget_lt_of_after_pos {n : ℕ}
    {alpha : ℝ} {v : Item n → ℝ} {t j : Item n}
    (ρ : TypePolicy 2 n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (htj : t.val < j.val) (hxj : 0 < (ρ 0 j).toReal) :
    (∑ l : Item n,
        problem6ClosedDualWeight alpha v t l *
          pairShare alpha v l * (ρ 0 l).toReal) <
      problem6ClosedValue alpha v t * pairShare alpha v t := by
  calc
    (∑ l : Item n,
        problem6ClosedDualWeight alpha v t l *
          pairShare alpha v l * (ρ 0 l).toReal) <
        ∑ l : Item n,
          (problem6ClosedValue alpha v t * pairShare alpha v t) *
            (ρ 0 l).toReal := by
      refine Finset.sum_lt_sum ?_ ?_
      · intro l _hl
        exact mul_le_mul_of_nonneg_right
          (problem6ClosedDualWeight_pairShare_le
            halpha0 halpha1 hpos hdec)
          ENNReal.toReal_nonneg
      · exact ⟨j, Finset.mem_univ j,
          mul_lt_mul_of_pos_right
            (problem6ClosedDualWeight_pairShare_lt_of_after
              halpha0 halpha1 hpos hdec htj) hxj⟩
    _ = problem6ClosedValue alpha v t * pairShare alpha v t := by
      rw [← Finset.mul_sum, problem6_typeZero_sum_eq_one]
      ring

/-- A positive type-`1` coordinate before the pivot makes the dual budget strict. -/
theorem problem6ClosedDual_y_budget_lt_of_before_pos {n : ℕ}
    {alpha : ℝ} {v : Item n → ℝ} {t j : Item n}
    (ρ : TypePolicy 2 n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hjt : j.val < t.val) (hyj : 0 < (ρ 1 j).toReal) :
    (∑ l : Item n,
        problem6ClosedDualWeight alpha v t l *
          (1 - pairShare alpha v l) * (ρ 1 l).toReal) <
      problem6ClosedValue alpha v t *
        (1 - pairShare alpha v t) := by
  calc
    (∑ l : Item n,
        problem6ClosedDualWeight alpha v t l *
          (1 - pairShare alpha v l) * (ρ 1 l).toReal) <
        ∑ l : Item n,
          (problem6ClosedValue alpha v t *
            (1 - pairShare alpha v t)) * (ρ 1 l).toReal := by
      refine Finset.sum_lt_sum ?_ ?_
      · intro l _hl
        exact mul_le_mul_of_nonneg_right
          (problem6ClosedDualWeight_one_sub_pairShare_le
            halpha0 halpha1 hpos hdec)
          ENNReal.toReal_nonneg
      · exact ⟨j, Finset.mem_univ j,
          mul_lt_mul_of_pos_right
            (problem6ClosedDualWeight_one_sub_pairShare_lt_of_before
              halpha0 halpha1 hpos hdec hjt) hyj⟩
    _ = problem6ClosedValue alpha v t *
          (1 - pairShare alpha v t) := by
      rw [← Finset.mul_sum, problem6_typeOne_sum_eq_one]
      ring

/--
Problem 6 closed-form weak duality certificate: every feasible policy/value is
bounded above by the Lemma 5 closed value for the pivot.
-/
theorem problem6ClosedDual_upper_bound {n : ℕ}
    {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (ρ : TypePolicy 2 n) (ell : ℝ)
    (hfeas : problem6LPFeasible alpha v ρ ell) :
    ell ≤ problem6ClosedValue alpha v t := by
  let w : Item n → ℝ := problem6ClosedDualWeight alpha v t
  have hweighted :
      (∑ j : Item n, w j * ell) ≤
        ∑ j : Item n, w j *
          (pairShare alpha v j * (ρ 0 j).toReal +
            (1 - pairShare alpha v j) * (ρ 1 j).toReal) := by
    refine Finset.sum_le_sum ?_
    intro j _hj
    exact mul_le_mul_of_nonneg_left (hfeas j)
      (problem6ClosedDualWeight_nonneg halpha0 halpha1 hpos j)
  have hleft :
      (∑ j : Item n, w j * ell) = ell := by
    calc
      (∑ j : Item n, w j * ell) = (∑ j : Item n, w j) * ell := by
        rw [Finset.sum_mul]
      _ = ell := by
        rw [show (∑ j : Item n, w j) = 1 by
          simpa [w] using
            problem6ClosedDualWeight_sum_eq_one
              (alpha := alpha) (v := v) (t := t)
              halpha0 halpha1 hpos]
        ring
  have hright_split :
      (∑ j : Item n, w j *
          (pairShare alpha v j * (ρ 0 j).toReal +
            (1 - pairShare alpha v j) * (ρ 1 j).toReal)) =
        (∑ j : Item n,
          w j * pairShare alpha v j * (ρ 0 j).toReal) +
        (∑ j : Item n,
          w j * (1 - pairShare alpha v j) * (ρ 1 j).toReal) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro j _hj
    ring
  have hx :=
    problem6ClosedDual_x_budget_le ρ halpha0 halpha1 hpos hdec
      (t := t)
  have hy :=
    problem6ClosedDual_y_budget_le ρ halpha0 halpha1 hpos hdec
      (t := t)
  calc
    ell = ∑ j : Item n, w j * ell := hleft.symm
    _ ≤ ∑ j : Item n, w j *
          (pairShare alpha v j * (ρ 0 j).toReal +
            (1 - pairShare alpha v j) * (ρ 1 j).toReal) := hweighted
    _ = (∑ j : Item n,
          w j * pairShare alpha v j * (ρ 0 j).toReal) +
        (∑ j : Item n,
          w j * (1 - pairShare alpha v j) * (ρ 1 j).toReal) := hright_split
    _ ≤ problem6ClosedValue alpha v t * pairShare alpha v t +
        problem6ClosedValue alpha v t *
          (1 - pairShare alpha v t) := add_le_add hx hy
    _ = problem6ClosedValue alpha v t := by ring

/--
Denominator bounds plus the closed-form dual certificate produce the full
closed-form optimality certificate for Problem 6.
-/
theorem problem6ClosedOptimalityCertificate_of_denominatorBounds {n : ℕ}
    [NeZero n] {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hbounds : Problem6ClosedPivotDenominatorBounds alpha v t) :
    Problem6ClosedOptimalityCertificate alpha v t where
  denominator_bounds := hbounds
  upper_bound := fun ρ ell hfeas =>
    problem6ClosedDual_upper_bound
      halpha0 halpha1 hpos hdec ρ ell hfeas

/--
Lemma 5 full closed-form optimality certificate: the finite pivot choice
provides denominator bounds, and the closed dual proves the LP upper bound.
-/
theorem problem6ClosedOptimalityCertificate_exists {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v) :
    ∃ t : Item n, Problem6ClosedOptimalityCertificate alpha v t := by
  rcases problem6ClosedPivotDenominatorBounds_exists
      (alpha := alpha) (v := v) halpha0 halpha1 hpos with
    ⟨t, hbounds⟩
  exact ⟨t,
    problem6ClosedOptimalityCertificate_of_denominatorBounds
      halpha0 halpha1 hpos hdec hbounds⟩

/--
The canonical first closed pivot supplies the full closed-form optimality
certificate.
-/
theorem problem6FirstClosedPivot_optimalityCertificate {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v) :
    Problem6ClosedOptimalityCertificate alpha v
      (problem6FirstClosedPivot alpha v halpha0 halpha1 hpos) := by
  exact problem6ClosedOptimalityCertificate_of_denominatorBounds
    halpha0 halpha1 hpos hdec
    (problem6FirstClosedPivot_denominatorBounds
      halpha0 halpha1 hpos)

/-- An optimal Problem 6 value equals any certified closed-form value. -/
theorem problem6PolicyOptimal_value_eq_closedValue_of_certificate
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 2 n} {ell : ℝ}
    {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (cert : Problem6ClosedOptimalityCertificate alpha v t)
    (hopt : Problem6PolicyOptimal alpha v ρ ell) :
    ell = problem6ClosedValue alpha v t := by
  let hpivot : Problem6ClosedNonnegativePivots alpha v t :=
    problem6ClosedNonnegativePivots_of_denominatorBounds
      halpha0 halpha1 hpos cert.denominator_bounds
  let ρclosed : TypePolicy 2 n :=
    problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot
  have hle : ell ≤ problem6ClosedValue alpha v t :=
    cert.upper_bound ρ ell hopt.1
  have hge : problem6ClosedValue alpha v t ≤ ell := by
    apply hopt.2 ρclosed
    dsimp [ρclosed, hpivot]
    exact problem6ClosedPolicy_feasible_of_denominatorBounds
      halpha0 halpha1 hpos cert.denominator_bounds
  exact le_antisymm hle hge

/-- Equalized item equations turn the closed dual's weighted sum into `ell`. -/
theorem problem6ClosedDual_weighted_sum_eq_of_item_eq
    {n : ℕ}
    {alpha : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 2 n} {ell : ℝ}
    {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hitem_eq :
      ∀ j : Item n,
        pairShare alpha v j * (ρ 0 j).toReal +
          (1 - pairShare alpha v j) * (ρ 1 j).toReal = ell) :
    (∑ j : Item n,
        problem6ClosedDualWeight alpha v t j *
          pairShare alpha v j * (ρ 0 j).toReal) +
      (∑ j : Item n,
        problem6ClosedDualWeight alpha v t j *
          (1 - pairShare alpha v j) * (ρ 1 j).toReal) = ell := by
  let w : Item n → ℝ := problem6ClosedDualWeight alpha v t
  calc
    (∑ j : Item n, w j * pairShare alpha v j * (ρ 0 j).toReal) +
        (∑ j : Item n,
          w j * (1 - pairShare alpha v j) * (ρ 1 j).toReal) =
      ∑ j : Item n, w j *
        (pairShare alpha v j * (ρ 0 j).toReal +
          (1 - pairShare alpha v j) * (ρ 1 j).toReal) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl ?_
        intro j _hj
        ring
    _ = ∑ j : Item n, w j * ell := by
      refine Finset.sum_congr rfl ?_
      intro j _hj
      rw [hitem_eq j]
    _ = (∑ j : Item n, w j) * ell := by rw [Finset.sum_mul]
    _ = ell := by
      rw [show (∑ j : Item n, w j) = 1 by
        simpa [w] using
          problem6ClosedDualWeight_sum_eq_one
            (alpha := alpha) (v := v) (t := t)
            halpha0 halpha1 hpos]
      ring

/--
Strict dual slack derives the source Lemma 4 threshold support for every
equalized optimum; no basic-feasible or sparsity premise is required.
-/
theorem problem6PolicyOptimal_equalized_thresholdSupport_of_closedCertificate
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 2 n} {ell : ℝ}
    {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (cert : Problem6ClosedOptimalityCertificate alpha v t)
    (hitem_eq :
      ∀ j : Item n,
        pairShare alpha v j * (ρ 0 j).toReal +
          (1 - pairShare alpha v j) * (ρ 1 j).toReal = ell)
    (hopt : Problem6PolicyOptimal alpha v ρ ell) :
    (∀ {j : Item n}, t.val < j.val → ρ 0 j = 0) ∧
      (∀ {j : Item n}, j.val < t.val → ρ 1 j = 0) := by
  have hvalue : ell = problem6ClosedValue alpha v t :=
    problem6PolicyOptimal_value_eq_closedValue_of_certificate
      halpha0 halpha1 hpos cert hopt
  have hweighted :=
    problem6ClosedDual_weighted_sum_eq_of_item_eq
      (t := t) halpha0 halpha1 hpos hitem_eq
  constructor
  · intro j htj
    by_contra hxj
    have hxj_pos : 0 < (ρ 0 j).toReal :=
      typePolicy_toReal_pos_of_ne_zero ρ hxj
    have hx_lt :=
      problem6ClosedDual_x_budget_lt_of_after_pos
        ρ halpha0 halpha1 hpos hdec htj hxj_pos
    have hy_le :=
      problem6ClosedDual_y_budget_le
        (t := t) ρ halpha0 halpha1 hpos hdec
    have hlt : ell < problem6ClosedValue alpha v t := by
      calc
        ell =
            (∑ l : Item n,
              problem6ClosedDualWeight alpha v t l *
                pairShare alpha v l * (ρ 0 l).toReal) +
            (∑ l : Item n,
              problem6ClosedDualWeight alpha v t l *
                (1 - pairShare alpha v l) * (ρ 1 l).toReal) :=
          hweighted.symm
        _ < problem6ClosedValue alpha v t * pairShare alpha v t +
              problem6ClosedValue alpha v t *
                (1 - pairShare alpha v t) :=
          add_lt_add_of_lt_of_le hx_lt hy_le
        _ = problem6ClosedValue alpha v t := by ring
    rw [hvalue] at hlt
    exact (lt_irrefl _ hlt)
  · intro j hjt
    by_contra hyj
    have hyj_pos : 0 < (ρ 1 j).toReal :=
      typePolicy_toReal_pos_of_ne_zero ρ hyj
    have hx_le :=
      problem6ClosedDual_x_budget_le
        (t := t) ρ halpha0 halpha1 hpos hdec
    have hy_lt :=
      problem6ClosedDual_y_budget_lt_of_before_pos
        ρ halpha0 halpha1 hpos hdec hjt hyj_pos
    have hlt : ell < problem6ClosedValue alpha v t := by
      calc
        ell =
            (∑ l : Item n,
              problem6ClosedDualWeight alpha v t l *
                pairShare alpha v l * (ρ 0 l).toReal) +
            (∑ l : Item n,
              problem6ClosedDualWeight alpha v t l *
                (1 - pairShare alpha v l) * (ρ 1 l).toReal) :=
          hweighted.symm
        _ < problem6ClosedValue alpha v t * pairShare alpha v t +
              problem6ClosedValue alpha v t *
                (1 - pairShare alpha v t) :=
          add_lt_add_of_le_of_lt hx_le hy_lt
        _ = problem6ClosedValue alpha v t := by ring
    rw [hvalue] at hlt
    exact (lt_irrefl _ hlt)

/--
Every equalized Problem 6 optimum has the source-active sparse form at its
last positive `x` coordinate.
-/
theorem problem6PolicyOptimal_equalized_sparseActive
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 2 n} {ell : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hitem_eq :
      ∀ j : Item n,
        pairShare alpha v j * (ρ 0 j).toReal +
          (1 - pairShare alpha v j) * (ρ 1 j).toReal = ell)
    (hopt : Problem6PolicyOptimal alpha v ρ ell) :
    Problem6SparseEqualizedActive alpha v (TypePolicy.lastActiveTypeZero ρ)
      (fun j : Item n => (ρ 0 j).toReal)
      (fun j : Item n => (ρ 1 j).toReal) ell := by
  let t0 : Item n :=
    problem6FirstClosedPivot alpha v halpha0 halpha1 hpos
  let cert : Problem6ClosedOptimalityCertificate alpha v t0 :=
    problem6FirstClosedPivot_optimalityCertificate
      halpha0 halpha1 hpos hdec
  have hsupport :=
    problem6PolicyOptimal_equalized_thresholdSupport_of_closedCertificate
      halpha0 halpha1 hpos hdec cert hitem_eq hopt
  let t : Item n := TypePolicy.lastActiveTypeZero ρ
  have ht_le : t.val ≤ t0.val := by
    by_contra hnot
    have ht0t : t0.val < t.val := by omega
    have hzero : ρ 0 t = 0 := hsupport.1 ht0t
    exact TypePolicy.lastActiveTypeZero_active ρ hzero
  refine
    { sparse :=
        { item_eq := hitem_eq
          sum_x := problem6_typeZero_sum_eq_one ρ
          sum_y := problem6_typeOne_sum_eq_one ρ
          x_after_pivot_zero := ?_
          y_before_pivot_zero := ?_ }
      x_nonneg := fun j => ENNReal.toReal_nonneg
      y_nonneg := fun j => ENNReal.toReal_nonneg
      x_pivot_pos := typePolicy_toReal_pos_of_ne_zero ρ
        (TypePolicy.lastActiveTypeZero_active ρ) }
  · intro j hj
    exact congrArg ENNReal.toReal
      (TypePolicy.typeZero_zero_after_lastActive ρ hj)
  · intro j hj
    have hj0 : j.val < t0.val := lt_of_lt_of_le hj ht_le
    exact congrArg ENNReal.toReal (hsupport.2 hj0)

/-- The canonical first-closed policy directly satisfies Problem 6. -/
theorem problem6FirstClosedPolicy_item_eq_and_optimal
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v) :
    let t := problem6FirstClosedPivot alpha v halpha0 halpha1 hpos
    let ρ := problem6FirstClosedPolicy alpha v halpha0 halpha1 hpos
    (∀ j : Item n,
      pairShare alpha v j * (ρ 0 j).toReal +
        (1 - pairShare alpha v j) * (ρ 1 j).toReal =
          problem6ClosedValue alpha v t) ∧
      Problem6PolicyOptimal alpha v ρ (problem6ClosedValue alpha v t) := by
  dsimp
  let t : Item n :=
    problem6FirstClosedPivot alpha v halpha0 halpha1 hpos
  let cert : Problem6ClosedOptimalityCertificate alpha v t :=
    problem6FirstClosedPivot_optimalityCertificate
      halpha0 halpha1 hpos hdec
  let hpivot : Problem6ClosedNonnegativePivots alpha v t :=
    problem6ClosedNonnegativePivots_of_denominatorBounds
      halpha0 halpha1 hpos cert.denominator_bounds
  have hclosed :
      Problem6EqualizedBasicOptimal alpha v
        (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot)
        (problem6ClosedValue alpha v t) := by
    refine
      { item_eq := ?_
        optimal := ?_
        basic_feasible := ?_ }
    · intro j
      rw [problem6ClosedPolicy_zero_toReal halpha0 halpha1 hpos hpivot,
        problem6ClosedPolicy_one_toReal halpha0 halpha1 hpos hpivot]
      exact problem6Closed_item_eq t j halpha0 halpha1 hpos
    · exact
        ⟨problem6ClosedPolicy_feasible_of_denominatorBounds
            halpha0 halpha1 hpos cert.denominator_bounds,
          cert.upper_bound⟩
    · exact problem6ClosedPolicy_basicFeasibleSupportCertificate
        halpha0 halpha1 hpos hpivot
  have hpolicy :
      problem6FirstClosedPolicy alpha v halpha0 halpha1 hpos =
        problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot := by
    dsimp [t, cert, hpivot]
    exact problem6FirstClosedPolicy_eq_closedPolicy_of_firstClosedPivot_eq
      halpha0 halpha1 hpos rfl
  rw [hpolicy]
  exact ⟨hclosed.item_eq, hclosed.optimal⟩

/--
Appendix D, Lemma 4 uniqueness from primitive Problem 6 equations and global
optimality.  The threshold conclusion is derived internally by strict dual
slack rather than assumed through a basic-feasible package.
-/
theorem problem6PolicyOptimal_equalized_eq_firstClosedPolicy
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 2 n} {ell : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hitem_eq :
      ∀ j : Item n,
        pairShare alpha v j * (ρ 0 j).toReal +
          (1 - pairShare alpha v j) * (ρ 1 j).toReal = ell)
    (hopt : Problem6PolicyOptimal alpha v ρ ell) :
    ρ = problem6FirstClosedPolicy alpha v halpha0 halpha1 hpos ∧
      ell = problem6ClosedValue alpha v
        (problem6FirstClosedPivot alpha v halpha0 halpha1 hpos) := by
  let t : Item n :=
    problem6FirstClosedPivot alpha v halpha0 halpha1 hpos
  let cert : Problem6ClosedOptimalityCertificate alpha v t :=
    problem6FirstClosedPivot_optimalityCertificate
      halpha0 halpha1 hpos hdec
  have hsupport :=
    problem6PolicyOptimal_equalized_thresholdSupport_of_closedCertificate
      halpha0 halpha1 hpos hdec cert hitem_eq hopt
  let x : Item n → ℝ := fun j => (ρ 0 j).toReal
  let y : Item n → ℝ := fun j => (ρ 1 j).toReal
  have hsparse : Problem6SparseEqualized alpha v t x y ell :=
    { item_eq := hitem_eq
      sum_x := problem6_typeZero_sum_eq_one ρ
      sum_y := problem6_typeOne_sum_eq_one ρ
      x_after_pivot_zero := fun {_j} hj =>
        congrArg ENNReal.toReal (hsupport.1 hj)
      y_before_pivot_zero := fun {_j} hj =>
        congrArg ENNReal.toReal (hsupport.2 hj) }
  rcases problem6SparseEqualized_eq_closed
      halpha0 halpha1 hpos hsparse with ⟨hell, hx, hy⟩
  let hpivot : Problem6ClosedNonnegativePivots alpha v t :=
    problem6ClosedNonnegativePivots_of_denominatorBounds
      halpha0 halpha1 hpos cert.denominator_bounds
  have hpolicy_closed :
      ρ = problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot := by
    funext k
    fin_cases k
    · apply pmf_eq_of_forall_toReal_eq
      intro j
      change (ρ 0 j).toReal =
        ((problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot) 0 j).toReal
      rw [problem6ClosedPolicy_zero_toReal]
      exact congrFun hx j
    · apply pmf_eq_of_forall_toReal_eq
      intro j
      change (ρ 1 j).toReal =
        ((problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot) 1 j).toReal
      rw [problem6ClosedPolicy_one_toReal]
      exact congrFun hy j
  have hfirst :
      problem6FirstClosedPolicy alpha v halpha0 halpha1 hpos =
        problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot := by
    dsimp [t, cert, hpivot]
    exact problem6FirstClosedPolicy_eq_closedPolicy_of_firstClosedPivot_eq
      halpha0 halpha1 hpos rfl
  exact ⟨hpolicy_closed.trans hfirst.symm, by simpa [t] using hell⟩

/--
Appendix D, Lemma 4/5 bridge: an equalized optimal Problem 6 policy supplies
the closed-form optimality certificate at its active sparse pivot.
-/
theorem problem6ClosedOptimalityCertificate_of_policyOptimal_equalized_of_two_lt
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 2 n} {ell : ℝ}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hitem_eq :
      ∀ l : Item n,
        pairShare alpha v l * (ρ 0 l).toReal +
          (1 - pairShare alpha v l) * (ρ 1 l).toReal = ell)
    (hopt : Problem6PolicyOptimal alpha v ρ ell)
    (hshared : TypePolicy.SharedItemsBound ρ) :
    Problem6ClosedOptimalityCertificate alpha v
      (TypePolicy.lastActiveTypeZero ρ) := by
  let t : Item n := TypePolicy.lastActiveTypeZero ρ
  have hsparse :
      Problem6SparseEqualizedActive alpha v t
        (fun l : Item n => (ρ 0 l).toReal)
        (fun l : Item n => (ρ 1 l).toReal) ell := by
    dsimp [t]
    exact problem6SparseEqualizedActive_of_policyOptimal_equalized_of_two_lt
      hn halpha0 halpha1 hpos hdec hitem_eq hopt hshared
  have hvalue :
      ell = problem6ClosedValue alpha v t :=
    problem6SparseEqualized_value_eq_closed
      halpha0 halpha1 hpos hsparse.sparse
  have hbounds :
      Problem6ClosedPivotDenominatorBounds alpha v t :=
    problem6ClosedPivotDenominatorBounds_of_sparseEqualizedActive
      halpha0 halpha1 hpos hsparse
  refine
    { denominator_bounds := ?_
      upper_bound := ?_ }
  · simpa [t] using hbounds
  · intro ρ' ell' hfeas'
    have hle : ell' ≤ ell := hopt.2 ρ' ell' hfeas'
    exact hle.trans_eq hvalue

/--
Appendix D, Lemma 4/5 bridge for the paper's equality-form optimal BFS
package: the active sparse bridge and closed-form optimality certificate no
longer need a separate shared-item hypothesis.
-/
theorem problem6ClosedOptimalityCertificate_of_equalizedBasicOptimal_of_two_lt
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 2 n} {ell : ℝ}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (h : Problem6EqualizedBasicOptimal alpha v ρ ell) :
    Problem6ClosedOptimalityCertificate alpha v
      (TypePolicy.lastActiveTypeZero ρ) := by
  exact problem6ClosedOptimalityCertificate_of_policyOptimal_equalized_of_two_lt
    hn halpha0 halpha1 hpos hdec h.item_eq h.optimal
    (problem6_sharedItemsBound_of_equalizedBasicOptimal
      halpha0 halpha1 hpos h)

/--
Lemma 6 consequence from a closed-form optimality certificate: denominator
bounds provide the nonnegative pivot masses, and the strict pre-pivot summation
argument removes the old pivot-gap side condition.
-/
theorem problem6ClosedPolicy_typeFairness_eq_one_of_closed_certificate_alpha_le_half_of_pivot_le_reverse
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha_half : alpha ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (cert : Problem6ClosedOptimalityCertificate alpha v t)
    (hcenter : t.val ≤ (reverseItem t).val) :
    let hpivot : Problem6ClosedNonnegativePivots alpha v t :=
      problem6ClosedNonnegativePivots_of_denominatorBounds
        halpha0 halpha1 hpos cert.denominator_bounds
    TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel alpha v)
        (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot) =
      TypeWeightedRecommendationModel.normalizedTypeUtility
        (twoTypeReducedModel alpha v)
        (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot) 1 := by
  dsimp
  exact problem6ClosedPolicy_typeFairness_eq_one_of_alpha_le_half_of_pivot_le_reverse
    halpha0 halpha1 halpha_half hpos hdec
    (problem6ClosedNonnegativePivots_of_denominatorBounds
      halpha0 halpha1 hpos cert.denominator_bounds)
    hcenter

/--
Lemma 6 consequence for the paper's equality-form optimal BFS package,
assuming the selected pivot is already known to be at or before its mirror.
-/
theorem problem6ClosedPolicy_typeFairness_eq_one_of_equalizedBasicOptimal_alpha_le_half_of_pivot_le_reverse
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 2 n} {ell : ℝ}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha_half : alpha ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (h : Problem6EqualizedBasicOptimal alpha v ρ ell)
    (hcenter :
      (TypePolicy.lastActiveTypeZero ρ).val ≤
        (reverseItem (TypePolicy.lastActiveTypeZero ρ)).val) :
    let t : Item n := TypePolicy.lastActiveTypeZero ρ
    let cert : Problem6ClosedOptimalityCertificate alpha v t :=
      problem6ClosedOptimalityCertificate_of_equalizedBasicOptimal_of_two_lt
        hn halpha0 halpha1 hpos hdec h
    let hpivot : Problem6ClosedNonnegativePivots alpha v t :=
      problem6ClosedNonnegativePivots_of_denominatorBounds
        halpha0 halpha1 hpos cert.denominator_bounds
    TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel alpha v)
        (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot) =
      TypeWeightedRecommendationModel.normalizedTypeUtility
        (twoTypeReducedModel alpha v)
        (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot) 1 := by
  dsimp
  exact
    problem6ClosedPolicy_typeFairness_eq_one_of_closed_certificate_alpha_le_half_of_pivot_le_reverse
      halpha0 halpha1 halpha_half hpos hdec
      (problem6ClosedOptimalityCertificate_of_equalizedBasicOptimal_of_two_lt
        hn halpha0 halpha1 hpos hdec h)
      hcenter

/--
Lemma 6 stitched with Lemma 10 for the paper's equality-form optimal BFS
package, odd-center case.
-/
theorem problem6ClosedPolicy_typeFairness_eq_one_of_equalizedBasicOptimal_alpha_le_half_center
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ}
    {ρ ρhalf : TypePolicy 2 n} {ell ellHalf : ℝ} {c : Item n}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha_half : alpha ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter_c : c.val = (reverseItem c).val)
    (h : Problem6EqualizedBasicOptimal alpha v ρ ell)
    (hhalf : Problem6EqualizedBasicOptimal (1 / 2) v ρhalf ellHalf) :
    let t : Item n := TypePolicy.lastActiveTypeZero ρ
    let cert : Problem6ClosedOptimalityCertificate alpha v t :=
      problem6ClosedOptimalityCertificate_of_equalizedBasicOptimal_of_two_lt
        hn halpha0 halpha1 hpos hdec h
    let hpivot : Problem6ClosedNonnegativePivots alpha v t :=
      problem6ClosedNonnegativePivots_of_denominatorBounds
        halpha0 halpha1 hpos cert.denominator_bounds
    TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel alpha v)
        (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot) =
      TypeWeightedRecommendationModel.normalizedTypeUtility
        (twoTypeReducedModel alpha v)
        (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot) 1 := by
  let t : Item n := TypePolicy.lastActiveTypeZero ρ
  have ht_le_c : t.val ≤ c.val := by
    dsimp [t]
    exact lemma10_alpha_le_half_equalizedBasicOptimal_lastActive_le_center
      hn halpha0 halpha1 halpha_half hpos hdec hcenter_c h hhalf
  have ht_center : t.val ≤ (reverseItem t).val := by
    have hc_arith : 2 * c.val + 1 = n :=
      (val_eq_reverseItem_iff c).mp hcenter_c
    have ht_arith : 2 * t.val + 1 ≤ n := by omega
    exact (val_le_reverseItem_iff t).mpr ht_arith
  dsimp [t]
  exact
    problem6ClosedPolicy_typeFairness_eq_one_of_equalizedBasicOptimal_alpha_le_half_of_pivot_le_reverse
      hn halpha0 halpha1 halpha_half hpos hdec h ht_center

/--
Lemma 6 stitched with Lemma 10 for the paper's equality-form optimal BFS
package, even-center case.
-/
theorem problem6ClosedPolicy_typeFairness_eq_one_of_equalizedBasicOptimal_alpha_le_half_succ_center
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ}
    {ρ ρhalf : TypePolicy 2 n} {ell ellHalf : ℝ} {c : Item n}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha_half : alpha ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hsucc : c.val + 1 = (reverseItem c).val)
    (h : Problem6EqualizedBasicOptimal alpha v ρ ell)
    (hhalf : Problem6EqualizedBasicOptimal (1 / 2) v ρhalf ellHalf) :
    let t : Item n := TypePolicy.lastActiveTypeZero ρ
    let cert : Problem6ClosedOptimalityCertificate alpha v t :=
      problem6ClosedOptimalityCertificate_of_equalizedBasicOptimal_of_two_lt
        hn halpha0 halpha1 hpos hdec h
    let hpivot : Problem6ClosedNonnegativePivots alpha v t :=
      problem6ClosedNonnegativePivots_of_denominatorBounds
        halpha0 halpha1 hpos cert.denominator_bounds
    TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel alpha v)
        (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot) =
      TypeWeightedRecommendationModel.normalizedTypeUtility
        (twoTypeReducedModel alpha v)
        (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot) 1 := by
  let t : Item n := TypePolicy.lastActiveTypeZero ρ
  have ht_le_c : t.val ≤ c.val := by
    dsimp [t]
    exact lemma10_alpha_le_half_equalizedBasicOptimal_lastActive_le_succ_center
      hn halpha0 halpha1 halpha_half hpos hdec hsucc h hhalf
  have ht_center : t.val ≤ (reverseItem t).val := by
    have hc_arith : 2 * c.val + 2 = n := by
      simp [reverseItem] at hsucc
      omega
    have ht_arith : 2 * t.val + 1 ≤ n := by omega
    exact (val_le_reverseItem_iff t).mpr ht_arith
  dsimp [t]
  exact
    problem6ClosedPolicy_typeFairness_eq_one_of_equalizedBasicOptimal_alpha_le_half_of_pivot_le_reverse
      hn halpha0 halpha1 halpha_half hpos hdec h ht_center

/--
The paper's equality-form optimal BFS package identifies the selected policy
with the Lemma 5 closed-form policy at its active pivot.
-/
theorem problem6EqualizedBasicOptimal_policy_eq_closedPolicy_of_two_lt
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 2 n} {ell : ℝ}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (h : Problem6EqualizedBasicOptimal alpha v ρ ell) :
    let t : Item n := TypePolicy.lastActiveTypeZero ρ
    let cert : Problem6ClosedOptimalityCertificate alpha v t :=
      problem6ClosedOptimalityCertificate_of_equalizedBasicOptimal_of_two_lt
        hn halpha0 halpha1 hpos hdec h
    let hpivot : Problem6ClosedNonnegativePivots alpha v t :=
      problem6ClosedNonnegativePivots_of_denominatorBounds
        halpha0 halpha1 hpos cert.denominator_bounds
    ρ = problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot := by
  let t : Item n := TypePolicy.lastActiveTypeZero ρ
  have hsparse :
      Problem6SparseEqualizedActive alpha v t
        (fun l : Item n => (ρ 0 l).toReal)
        (fun l : Item n => (ρ 1 l).toReal) ell := by
    dsimp [t]
    exact problem6SparseEqualizedActive_of_equalizedBasicOptimal_of_two_lt
      hn halpha0 halpha1 hpos hdec h
  rcases problem6SparseEqualized_eq_closed
      halpha0 halpha1 hpos hsparse.sparse with ⟨_hell, hx, hy⟩
  let cert : Problem6ClosedOptimalityCertificate alpha v t :=
    problem6ClosedOptimalityCertificate_of_equalizedBasicOptimal_of_two_lt
      hn halpha0 halpha1 hpos hdec h
  let hpivot : Problem6ClosedNonnegativePivots alpha v t :=
    problem6ClosedNonnegativePivots_of_denominatorBounds
      halpha0 halpha1 hpos cert.denominator_bounds
  change ρ = problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot
  funext k
  fin_cases k
  · apply pmf_eq_of_forall_toReal_eq
    intro j
    change ((ρ 0) j).toReal =
      ((problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot 0) j).toReal
    rw [problem6ClosedPolicy_zero_toReal]
    exact congrFun hx j
  · apply pmf_eq_of_forall_toReal_eq
    intro j
    change ((ρ 1) j).toReal =
      ((problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot 1) j).toReal
    rw [problem6ClosedPolicy_one_toReal]
    exact congrFun hy j

/--
Lemma 6 for the actual selected equality-form optimal BFS policy, conditional
on the selected pivot being at or before its mirror.
-/
theorem problem6EqualizedBasicOptimal_typeFairness_eq_one_of_alpha_le_half_of_pivot_le_reverse
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 2 n} {ell : ℝ}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha_half : alpha ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (h : Problem6EqualizedBasicOptimal alpha v ρ ell)
    (hcenter :
      (TypePolicy.lastActiveTypeZero ρ).val ≤
        (reverseItem (TypePolicy.lastActiveTypeZero ρ)).val) :
    TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel alpha v) ρ =
      TypeWeightedRecommendationModel.normalizedTypeUtility
        (twoTypeReducedModel alpha v) ρ 1 := by
  let t : Item n := TypePolicy.lastActiveTypeZero ρ
  let cert : Problem6ClosedOptimalityCertificate alpha v t :=
    problem6ClosedOptimalityCertificate_of_equalizedBasicOptimal_of_two_lt
      hn halpha0 halpha1 hpos hdec h
  let hpivot : Problem6ClosedNonnegativePivots alpha v t :=
    problem6ClosedNonnegativePivots_of_denominatorBounds
      halpha0 halpha1 hpos cert.denominator_bounds
  have hpolicy :
      ρ = problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot := by
    dsimp [t, cert, hpivot]
    exact problem6EqualizedBasicOptimal_policy_eq_closedPolicy_of_two_lt
      hn halpha0 halpha1 hpos hdec h
  rw [hpolicy]
  exact
    problem6ClosedPolicy_typeFairness_eq_one_of_alpha_le_half_of_pivot_le_reverse
      halpha0 halpha1 halpha_half hpos hdec hpivot (by simpa [t] using hcenter)

/--
Theorem 3 same-selected-pivot step for the actual equality-form optimal BFS
policies: on a first-half interval where the selected pivot does not change,
the selected policy's type fairness is monotone in `α`.
-/
theorem theorem3_typeFairness_mono_of_same_selected_equalizedBasicOptimal
    {n : ℕ} [NeZero n]
    {alpha alpha' : ℝ} {v : Item n → ℝ}
    {ρ ρ' : TypePolicy 2 n} {ell ell' : ℝ}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_half : alpha ≤ 1 / 2)
    (halpha_half' : alpha' ≤ 1 / 2)
    (halpha_le : alpha ≤ alpha')
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hpivot :
      TypePolicy.lastActiveTypeZero ρ =
        TypePolicy.lastActiveTypeZero ρ')
    (hcenter :
      (TypePolicy.lastActiveTypeZero ρ).val ≤
        (reverseItem (TypePolicy.lastActiveTypeZero ρ)).val)
    (h : Problem6EqualizedBasicOptimal alpha v ρ ell)
    (h' : Problem6EqualizedBasicOptimal alpha' v ρ' ell') :
    TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel alpha v) ρ ≤
      TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel alpha' v) ρ' := by
  let t : Item n := TypePolicy.lastActiveTypeZero ρ
  let t' : Item n := TypePolicy.lastActiveTypeZero ρ'
  let cert : Problem6ClosedOptimalityCertificate alpha v t :=
    problem6ClosedOptimalityCertificate_of_equalizedBasicOptimal_of_two_lt
      hn halpha0 halpha1 hpos hdec h
  let cert' : Problem6ClosedOptimalityCertificate alpha' v t' :=
    problem6ClosedOptimalityCertificate_of_equalizedBasicOptimal_of_two_lt
      hn halpha0' halpha1' hpos hdec h'
  let hpiv : Problem6ClosedNonnegativePivots alpha v t :=
    problem6ClosedNonnegativePivots_of_denominatorBounds
      halpha0 halpha1 hpos cert.denominator_bounds
  let hpiv' : Problem6ClosedNonnegativePivots alpha' v t' :=
    problem6ClosedNonnegativePivots_of_denominatorBounds
      halpha0' halpha1' hpos cert'.denominator_bounds
  have hpivot_tt' : t = t' := by
    dsimp [t, t']
    exact hpivot
  let hpiv'_t : Problem6ClosedNonnegativePivots alpha' v t := by
    simpa [hpivot_tt'] using hpiv'
  have hρ_closed :
      ρ = problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpiv := by
    dsimp [t, cert, hpiv]
    exact problem6EqualizedBasicOptimal_policy_eq_closedPolicy_of_two_lt
      hn halpha0 halpha1 hpos hdec h
  have hρ'_closed :
      ρ' = problem6ClosedPolicy alpha' v t halpha0' halpha1' hpos hpiv'_t := by
    have hraw :
        ρ' = problem6ClosedPolicy alpha' v t' halpha0' halpha1' hpos hpiv' := by
      dsimp [t', cert', hpiv']
      exact problem6EqualizedBasicOptimal_policy_eq_closedPolicy_of_two_lt
        hn halpha0' halpha1' hpos hdec h'
    have hclosed_eq :
        problem6ClosedPolicy alpha' v t' halpha0' halpha1' hpos hpiv' =
          problem6ClosedPolicy alpha' v t halpha0' halpha1' hpos hpiv'_t := by
      funext k
      fin_cases k
      · apply pmf_eq_of_forall_toReal_eq
        intro j
        change ((problem6ClosedPolicy alpha' v t' halpha0' halpha1' hpos hpiv' 0) j).toReal =
          ((problem6ClosedPolicy alpha' v t halpha0' halpha1' hpos hpiv'_t 0) j).toReal
        rw [problem6ClosedPolicy_zero_toReal, problem6ClosedPolicy_zero_toReal]
        simp [hpivot_tt']
      · apply pmf_eq_of_forall_toReal_eq
        intro j
        change ((problem6ClosedPolicy alpha' v t' halpha0' halpha1' hpos hpiv' 1) j).toReal =
          ((problem6ClosedPolicy alpha' v t halpha0' halpha1' hpos hpiv'_t 1) j).toReal
        rw [problem6ClosedPolicy_one_toReal, problem6ClosedPolicy_one_toReal]
        simp [hpivot_tt']
    exact hraw.trans hclosed_eq
  have htf :
      TypeWeightedRecommendationModel.typeFairness
          (twoTypeReducedModel alpha v) ρ =
        TypeWeightedRecommendationModel.normalizedTypeUtility
          (twoTypeReducedModel alpha v) ρ 1 :=
    problem6EqualizedBasicOptimal_typeFairness_eq_one_of_alpha_le_half_of_pivot_le_reverse
      hn halpha0 halpha1 halpha_half hpos hdec h hcenter
  have hcenter' :
      (TypePolicy.lastActiveTypeZero ρ').val ≤
        (reverseItem (TypePolicy.lastActiveTypeZero ρ')).val := by
    simpa [← hpivot] using hcenter
  have htf' :
      TypeWeightedRecommendationModel.typeFairness
          (twoTypeReducedModel alpha' v) ρ' =
        TypeWeightedRecommendationModel.normalizedTypeUtility
          (twoTypeReducedModel alpha' v) ρ' 1 :=
    problem6EqualizedBasicOptimal_typeFairness_eq_one_of_alpha_le_half_of_pivot_le_reverse
      hn halpha0' halpha1' halpha_half' hpos hdec h' hcenter'
  rw [htf, htf', hρ_closed, hρ'_closed]
  exact theorem3_fixedPivot_closedPolicy_normalizedTypeUtility_one_mono
    halpha0 halpha1 halpha0' halpha1' halpha_le hpos hdec
    (by simpa [t] using hcenter) hpiv hpiv'_t

/--
Theorem 3 finite-stitch core: along a first-half chain whose adjacent steps
either stay in one selected-pivot interval or repeat the same `α` at a
boundary, the selected policies' type-fairness values are monotone.
-/
theorem theorem3_typeFairness_mono_of_same_selected_or_equal_alpha_chain
    {n : ℕ} [NeZero n]
    {v : Item n → ℝ} (r : ℕ)
    (alphaSeq : ℕ → ℝ)
    (ρSeq : ℕ → TypePolicy 2 n)
    (ellSeq : ℕ → ℝ)
    (hn : 2 < n)
    (halpha0 : ∀ i, i ≤ r → 0 < alphaSeq i)
    (halpha1 : ∀ i, i ≤ r → alphaSeq i < 1)
    (halpha_half : ∀ i, i ≤ r → alphaSeq i ≤ 1 / 2)
    (hstep : ∀ i, i < r → alphaSeq i ≤ alphaSeq (i + 1))
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hpivot_or_eq :
      ∀ i, i < r →
        TypePolicy.lastActiveTypeZero (ρSeq i) =
          TypePolicy.lastActiveTypeZero (ρSeq (i + 1)) ∨
        alphaSeq i = alphaSeq (i + 1))
    (hcenter :
      ∀ i, i < r →
        (TypePolicy.lastActiveTypeZero (ρSeq i)).val ≤
          (reverseItem (TypePolicy.lastActiveTypeZero (ρSeq i))).val)
    (hopt :
      ∀ i, i ≤ r →
        Problem6EqualizedBasicOptimal (alphaSeq i) v (ρSeq i) (ellSeq i)) :
    TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel (alphaSeq 0) v) (ρSeq 0) ≤
      TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel (alphaSeq r) v) (ρSeq r) := by
  induction r with
  | zero =>
      exact le_rfl
  | succ r ih =>
      have hprev :
          TypeWeightedRecommendationModel.typeFairness
              (twoTypeReducedModel (alphaSeq 0) v) (ρSeq 0) ≤
            TypeWeightedRecommendationModel.typeFairness
              (twoTypeReducedModel (alphaSeq r) v) (ρSeq r) := by
        exact ih
          (fun i hi => halpha0 i (Nat.le_trans hi (Nat.le_succ r)))
          (fun i hi => halpha1 i (Nat.le_trans hi (Nat.le_succ r)))
          (fun i hi => halpha_half i (Nat.le_trans hi (Nat.le_succ r)))
          (fun i hi => hstep i (Nat.lt_trans hi (Nat.lt_succ_self r)))
          (fun i hi => hpivot_or_eq i (Nat.lt_trans hi (Nat.lt_succ_self r)))
          (fun i hi => hcenter i (Nat.lt_trans hi (Nat.lt_succ_self r)))
          (fun i hi => hopt i (Nat.le_trans hi (Nat.le_succ r)))
      have hlast :
          TypeWeightedRecommendationModel.typeFairness
              (twoTypeReducedModel (alphaSeq r) v) (ρSeq r) ≤
            TypeWeightedRecommendationModel.typeFairness
              (twoTypeReducedModel (alphaSeq (r + 1)) v) (ρSeq (r + 1)) := by
        rcases hpivot_or_eq r (Nat.lt_succ_self r) with hpivot | halpha_eq
        · exact
            theorem3_typeFairness_mono_of_same_selected_equalizedBasicOptimal
              hn
              (halpha0 r (Nat.le_succ r))
              (halpha1 r (Nat.le_succ r))
              (halpha0 (r + 1) le_rfl)
              (halpha1 (r + 1) le_rfl)
              (halpha_half r (Nat.le_succ r))
              (halpha_half (r + 1) le_rfl)
              (hstep r (Nat.lt_succ_self r))
              hpos hdec hpivot
              (hcenter r (Nat.lt_succ_self r))
              (hopt r (Nat.le_succ r))
              (hopt (r + 1) le_rfl)
        · have hopt_next_same :
              Problem6EqualizedBasicOptimal (alphaSeq r) v
                (ρSeq (r + 1)) (ellSeq (r + 1)) := by
            rw [halpha_eq]
            exact hopt (r + 1) le_rfl
          have hpivot_same :
              TypePolicy.lastActiveTypeZero (ρSeq r) =
                TypePolicy.lastActiveTypeZero (ρSeq (r + 1)) :=
            problem6EqualizedBasicOptimal_lastActive_eq_of_same_alpha
              hn
              (halpha0 r (Nat.le_succ r))
              (halpha1 r (Nat.le_succ r))
              hpos hdec
              (hopt r (Nat.le_succ r))
              hopt_next_same
          have hmono_same :
              TypeWeightedRecommendationModel.typeFairness
                  (twoTypeReducedModel (alphaSeq r) v) (ρSeq r) ≤
                TypeWeightedRecommendationModel.typeFairness
                  (twoTypeReducedModel (alphaSeq r) v) (ρSeq (r + 1)) :=
            theorem3_typeFairness_mono_of_same_selected_equalizedBasicOptimal
              hn
              (halpha0 r (Nat.le_succ r))
              (halpha1 r (Nat.le_succ r))
              (halpha0 r (Nat.le_succ r))
              (halpha1 r (Nat.le_succ r))
              (halpha_half r (Nat.le_succ r))
              (halpha_half r (Nat.le_succ r))
              le_rfl hpos hdec hpivot_same
              (hcenter r (Nat.lt_succ_self r))
              (hopt r (Nat.le_succ r))
              hopt_next_same
          simpa [halpha_eq] using hmono_same
      exact hprev.trans hlast

/--
Theorem 3 finite-stitch core, odd-center case: Lemma 10 supplies the
pivot-before-mirror side condition throughout the first-half chain.
-/
theorem theorem3_typeFairness_mono_firstHalf_center_chain
    {n : ℕ} [NeZero n]
    {v : Item n → ℝ} {c : Item n}
    (r : ℕ)
    (alphaSeq : ℕ → ℝ)
    (ρSeq : ℕ → TypePolicy 2 n)
    (ellSeq : ℕ → ℝ)
    {ρhalf : TypePolicy 2 n} {ellHalf : ℝ}
    (hn : 2 < n)
    (halpha0 : ∀ i, i ≤ r → 0 < alphaSeq i)
    (halpha1 : ∀ i, i ≤ r → alphaSeq i < 1)
    (halpha_half : ∀ i, i ≤ r → alphaSeq i ≤ 1 / 2)
    (hstep : ∀ i, i < r → alphaSeq i ≤ alphaSeq (i + 1))
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter_c : c.val = (reverseItem c).val)
    (hpivot_or_eq :
      ∀ i, i < r →
        TypePolicy.lastActiveTypeZero (ρSeq i) =
          TypePolicy.lastActiveTypeZero (ρSeq (i + 1)) ∨
        alphaSeq i = alphaSeq (i + 1))
    (hopt :
      ∀ i, i ≤ r →
        Problem6EqualizedBasicOptimal (alphaSeq i) v (ρSeq i) (ellSeq i))
    (hhalf :
      Problem6EqualizedBasicOptimal (1 / 2) v ρhalf ellHalf) :
    TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel (alphaSeq 0) v) (ρSeq 0) ≤
      TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel (alphaSeq r) v) (ρSeq r) := by
  exact theorem3_typeFairness_mono_of_same_selected_or_equal_alpha_chain
    r alphaSeq ρSeq ellSeq hn halpha0 halpha1 halpha_half hstep hpos hdec
    hpivot_or_eq
    (fun i hi =>
      lemma10_alpha_le_half_equalizedBasicOptimal_lastActive_le_reverse_center
        hn (halpha0 i (Nat.le_of_lt hi))
        (halpha1 i (Nat.le_of_lt hi))
        (halpha_half i (Nat.le_of_lt hi))
        hpos hdec hcenter_c (hopt i (Nat.le_of_lt hi)) hhalf)
    hopt

/--
Theorem 3 finite-stitch core, even-center case: Lemma 10 supplies the
pivot-before-mirror side condition throughout the first-half chain.
-/
theorem theorem3_typeFairness_mono_firstHalf_succ_center_chain
    {n : ℕ} [NeZero n]
    {v : Item n → ℝ} {c : Item n}
    (r : ℕ)
    (alphaSeq : ℕ → ℝ)
    (ρSeq : ℕ → TypePolicy 2 n)
    (ellSeq : ℕ → ℝ)
    {ρhalf : TypePolicy 2 n} {ellHalf : ℝ}
    (hn : 2 < n)
    (halpha0 : ∀ i, i ≤ r → 0 < alphaSeq i)
    (halpha1 : ∀ i, i ≤ r → alphaSeq i < 1)
    (halpha_half : ∀ i, i ≤ r → alphaSeq i ≤ 1 / 2)
    (hstep : ∀ i, i < r → alphaSeq i ≤ alphaSeq (i + 1))
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hsucc : c.val + 1 = (reverseItem c).val)
    (hpivot_or_eq :
      ∀ i, i < r →
        TypePolicy.lastActiveTypeZero (ρSeq i) =
          TypePolicy.lastActiveTypeZero (ρSeq (i + 1)) ∨
        alphaSeq i = alphaSeq (i + 1))
    (hopt :
      ∀ i, i ≤ r →
        Problem6EqualizedBasicOptimal (alphaSeq i) v (ρSeq i) (ellSeq i))
    (hhalf :
      Problem6EqualizedBasicOptimal (1 / 2) v ρhalf ellHalf) :
    TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel (alphaSeq 0) v) (ρSeq 0) ≤
      TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel (alphaSeq r) v) (ρSeq r) := by
  exact theorem3_typeFairness_mono_of_same_selected_or_equal_alpha_chain
    r alphaSeq ρSeq ellSeq hn halpha0 halpha1 halpha_half hstep hpos hdec
    hpivot_or_eq
    (fun i hi =>
      lemma10_alpha_le_half_equalizedBasicOptimal_lastActive_le_reverse_succ_center
        hn (halpha0 i (Nat.le_of_lt hi))
        (halpha1 i (Nat.le_of_lt hi))
        (halpha_half i (Nat.le_of_lt hi))
        hpos hdec hsucc (hopt i (Nat.le_of_lt hi)) hhalf)
    hopt

/--
Lemma 6 stitched with Lemma 10 for the actual selected equality-form optimal
BFS policy, odd-center case.
-/
theorem problem6EqualizedBasicOptimal_typeFairness_eq_one_of_alpha_le_half_center
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ}
    {ρ ρhalf : TypePolicy 2 n} {ell ellHalf : ℝ} {c : Item n}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha_half : alpha ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter_c : c.val = (reverseItem c).val)
    (h : Problem6EqualizedBasicOptimal alpha v ρ ell)
    (hhalf : Problem6EqualizedBasicOptimal (1 / 2) v ρhalf ellHalf) :
    TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel alpha v) ρ =
      TypeWeightedRecommendationModel.normalizedTypeUtility
        (twoTypeReducedModel alpha v) ρ 1 := by
  let t : Item n := TypePolicy.lastActiveTypeZero ρ
  have ht_le_c : t.val ≤ c.val := by
    dsimp [t]
    exact lemma10_alpha_le_half_equalizedBasicOptimal_lastActive_le_center
      hn halpha0 halpha1 halpha_half hpos hdec hcenter_c h hhalf
  have ht_center : t.val ≤ (reverseItem t).val := by
    have hc_arith : 2 * c.val + 1 = n :=
      (val_eq_reverseItem_iff c).mp hcenter_c
    have ht_arith : 2 * t.val + 1 ≤ n := by omega
    exact (val_le_reverseItem_iff t).mpr ht_arith
  exact
    problem6EqualizedBasicOptimal_typeFairness_eq_one_of_alpha_le_half_of_pivot_le_reverse
      hn halpha0 halpha1 halpha_half hpos hdec h (by simpa [t] using ht_center)

/--
Lemma 6 stitched with Lemma 10 for the actual selected equality-form optimal
BFS policy, even-center case.
-/
theorem problem6EqualizedBasicOptimal_typeFairness_eq_one_of_alpha_le_half_succ_center
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ}
    {ρ ρhalf : TypePolicy 2 n} {ell ellHalf : ℝ} {c : Item n}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha_half : alpha ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hsucc : c.val + 1 = (reverseItem c).val)
    (h : Problem6EqualizedBasicOptimal alpha v ρ ell)
    (hhalf : Problem6EqualizedBasicOptimal (1 / 2) v ρhalf ellHalf) :
    TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel alpha v) ρ =
      TypeWeightedRecommendationModel.normalizedTypeUtility
        (twoTypeReducedModel alpha v) ρ 1 := by
  let t : Item n := TypePolicy.lastActiveTypeZero ρ
  have ht_le_c : t.val ≤ c.val := by
    dsimp [t]
    exact lemma10_alpha_le_half_equalizedBasicOptimal_lastActive_le_succ_center
      hn halpha0 halpha1 halpha_half hpos hdec hsucc h hhalf
  have ht_center : t.val ≤ (reverseItem t).val := by
    have hc_arith : 2 * c.val + 2 = n := by
      simp [reverseItem] at hsucc
      omega
    have ht_arith : 2 * t.val + 1 ≤ n := by omega
    exact (val_le_reverseItem_iff t).mpr ht_arith
  exact
    problem6EqualizedBasicOptimal_typeFairness_eq_one_of_alpha_le_half_of_pivot_le_reverse
      hn halpha0 halpha1 halpha_half hpos hdec h (by simpa [t] using ht_center)

/--
A closed-form certificate supplies the generic `Problem6OptimalityCertificate`
for the value `problem6ClosedValue`.
-/
noncomputable def problem6OptimalityCertificate_of_closed {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (cert : Problem6ClosedOptimalityCertificate alpha v t) :
    Problem6OptimalityCertificate alpha v (problem6ClosedValue alpha v t) where
  policy :=
    problem6ClosedPolicy alpha v t halpha0 halpha1 hpos
      (problem6ClosedNonnegativePivots_of_denominatorBounds
        halpha0 halpha1 hpos cert.denominator_bounds)
  feasible :=
    problem6ClosedPolicy_feasible_of_denominatorBounds
      halpha0 halpha1 hpos cert.denominator_bounds
  upper_bound := cert.upper_bound

/--
Closed-form Problem 6 certificate as the paper's equality-form optimal BFS
package.  The basic-feasible support certificate is supplied by the closed
policy's threshold support.
-/
theorem problem6EqualizedBasicOptimal_of_closed_certificate
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (cert : Problem6ClosedOptimalityCertificate alpha v t) :
    let hpivot : Problem6ClosedNonnegativePivots alpha v t :=
      problem6ClosedNonnegativePivots_of_denominatorBounds
        halpha0 halpha1 hpos cert.denominator_bounds
    Problem6EqualizedBasicOptimal alpha v
      (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot)
      (problem6ClosedValue alpha v t) := by
  dsimp
  let hpivot : Problem6ClosedNonnegativePivots alpha v t :=
    problem6ClosedNonnegativePivots_of_denominatorBounds
      halpha0 halpha1 hpos cert.denominator_bounds
  refine
    { item_eq := ?_
      optimal := ?_
      basic_feasible := ?_ }
  · intro j
    rw [problem6ClosedPolicy_zero_toReal halpha0 halpha1 hpos hpivot,
      problem6ClosedPolicy_one_toReal halpha0 halpha1 hpos hpivot]
    exact problem6Closed_item_eq t j halpha0 halpha1 hpos
  · exact
      ⟨problem6ClosedPolicy_feasible_of_denominatorBounds
          halpha0 halpha1 hpos cert.denominator_bounds,
        cert.upper_bound⟩
  · exact problem6ClosedPolicy_basicFeasibleSupportCertificate
      halpha0 halpha1 hpos hpivot

/--
The canonical first closed pivot yields the paper's equality-form optimal BFS
package.
-/
theorem problem6FirstClosedPivot_equalizedBasicOptimal {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v) :
    let t : Item n :=
      problem6FirstClosedPivot alpha v halpha0 halpha1 hpos
    let cert : Problem6ClosedOptimalityCertificate alpha v t :=
      problem6FirstClosedPivot_optimalityCertificate
        halpha0 halpha1 hpos hdec
    let hpivot : Problem6ClosedNonnegativePivots alpha v t :=
      problem6ClosedNonnegativePivots_of_denominatorBounds
        halpha0 halpha1 hpos cert.denominator_bounds
    Problem6EqualizedBasicOptimal alpha v
      (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot)
      (problem6ClosedValue alpha v t) := by
  dsimp
  exact problem6EqualizedBasicOptimal_of_closed_certificate
    halpha0 halpha1 hpos
    (problem6FirstClosedPivot_optimalityCertificate
      halpha0 halpha1 hpos hdec)

/--
Lemma 5 existence as the paper's equality-form optimal BFS package: the
closed-form pivot, closed policy, and closed value solve Problem 6.
-/
theorem problem6EqualizedBasicOptimal_exists_closed {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v) :
    ∃ t : Item n,
      ∃ cert : Problem6ClosedOptimalityCertificate alpha v t,
        let hpivot : Problem6ClosedNonnegativePivots alpha v t :=
          problem6ClosedNonnegativePivots_of_denominatorBounds
            halpha0 halpha1 hpos cert.denominator_bounds
        Problem6EqualizedBasicOptimal alpha v
          (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot)
          (problem6ClosedValue alpha v t) := by
  rcases problem6ClosedOptimalityCertificate_exists
      (alpha := alpha) (v := v) halpha0 halpha1 hpos hdec with
    ⟨t, cert⟩
  exact ⟨t, cert,
    problem6EqualizedBasicOptimal_of_closed_certificate
      halpha0 halpha1 hpos cert⟩

/--
Problem 6 equality-form optimal BFS existence, hiding the closed-form pivot
and certificate internals.
-/
theorem problem6EqualizedBasicOptimal_exists {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v) :
    ∃ (ρ : TypePolicy 2 n) (ell : ℝ),
      Problem6EqualizedBasicOptimal alpha v ρ ell := by
  rcases problem6EqualizedBasicOptimal_exists_closed
      (alpha := alpha) (v := v) halpha0 halpha1 hpos hdec with
    ⟨t, cert, hclosed⟩
  let hpivot : Problem6ClosedNonnegativePivots alpha v t :=
    problem6ClosedNonnegativePivots_of_denominatorBounds
      halpha0 halpha1 hpos cert.denominator_bounds
  exact ⟨problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot,
    problem6ClosedValue alpha v t, by simpa [hpivot] using hclosed⟩

/--
Appendix D, Lemma 10, odd-center case without an external midpoint BFS
hypothesis.  The midpoint equality-form optimum is the Lemma 5 closed-form
policy at the center pivot.
-/
theorem lemma10_alpha_le_half_equalizedBasicOptimal_lastActive_le_center_of_closed_half
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ}
    {ρ : TypePolicy 2 n} {ell : ℝ} {c : Item n}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha_half : alpha ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter : c.val = (reverseItem c).val)
    (h : Problem6EqualizedBasicOptimal alpha v ρ ell) :
    (TypePolicy.lastActiveTypeZero ρ).val ≤ c.val := by
  let certHalf : Problem6ClosedOptimalityCertificate (1 / 2) v c :=
    problem6ClosedOptimalityCertificate_of_denominatorBounds
      (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) hpos hdec
      (problem6ClosedPivotDenominatorBounds_half_center
        (v := v) (t := c) hpos hcenter)
  let hpivotHalf : Problem6ClosedNonnegativePivots (1 / 2) v c :=
    problem6ClosedNonnegativePivots_of_denominatorBounds
      (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) hpos
      certHalf.denominator_bounds
  let ρhalf : TypePolicy 2 n :=
    problem6ClosedPolicy (1 / 2) v c
      (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) hpos hpivotHalf
  have hhalf :
      Problem6EqualizedBasicOptimal (1 / 2) v ρhalf
        (problem6ClosedValue (1 / 2) v c) := by
    dsimp [ρhalf, hpivotHalf, certHalf]
    exact problem6EqualizedBasicOptimal_of_closed_certificate
      (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) hpos certHalf
  exact lemma10_alpha_le_half_equalizedBasicOptimal_lastActive_le_center
    hn halpha0 halpha1 halpha_half hpos hdec hcenter h hhalf

/--
Appendix D, Lemma 10, even-center case without an external midpoint BFS
hypothesis.  The midpoint equality-form optimum is the Lemma 5 closed-form
policy at the item immediately before its mirror.
-/
theorem lemma10_alpha_le_half_equalizedBasicOptimal_lastActive_le_succ_center_of_closed_half
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ}
    {ρ : TypePolicy 2 n} {ell : ℝ} {c : Item n}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha_half : alpha ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hsucc : c.val + 1 = (reverseItem c).val)
    (h : Problem6EqualizedBasicOptimal alpha v ρ ell) :
    (TypePolicy.lastActiveTypeZero ρ).val ≤ c.val := by
  let certHalf : Problem6ClosedOptimalityCertificate (1 / 2) v c :=
    problem6ClosedOptimalityCertificate_of_denominatorBounds
      (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) hpos hdec
      (problem6ClosedPivotDenominatorBounds_half_succ_center
        (v := v) (t := c) hpos hsucc)
  let hpivotHalf : Problem6ClosedNonnegativePivots (1 / 2) v c :=
    problem6ClosedNonnegativePivots_of_denominatorBounds
      (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) hpos
      certHalf.denominator_bounds
  let ρhalf : TypePolicy 2 n :=
    problem6ClosedPolicy (1 / 2) v c
      (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) hpos hpivotHalf
  have hhalf :
      Problem6EqualizedBasicOptimal (1 / 2) v ρhalf
        (problem6ClosedValue (1 / 2) v c) := by
    dsimp [ρhalf, hpivotHalf, certHalf]
    exact problem6EqualizedBasicOptimal_of_closed_certificate
      (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) hpos certHalf
  exact lemma10_alpha_le_half_equalizedBasicOptimal_lastActive_le_succ_center
    hn halpha0 halpha1 halpha_half hpos hdec hsucc h hhalf

/--
Appendix D, Lemma 10 consequence, odd-center case, using the closed-form
midpoint optimum instead of an external midpoint BFS hypothesis.
-/
theorem lemma10_alpha_le_half_equalizedBasicOptimal_lastActive_le_reverse_center_of_closed_half
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ}
    {ρ : TypePolicy 2 n} {ell : ℝ} {c : Item n}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha_half : alpha ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter : c.val = (reverseItem c).val)
    (h : Problem6EqualizedBasicOptimal alpha v ρ ell) :
    (TypePolicy.lastActiveTypeZero ρ).val ≤
      (reverseItem (TypePolicy.lastActiveTypeZero ρ)).val := by
  let t : Item n := TypePolicy.lastActiveTypeZero ρ
  have ht_le_c : t.val ≤ c.val := by
    dsimp [t]
    exact lemma10_alpha_le_half_equalizedBasicOptimal_lastActive_le_center_of_closed_half
      hn halpha0 halpha1 halpha_half hpos hdec hcenter h
  have hc_arith : 2 * c.val + 1 = n :=
    (val_eq_reverseItem_iff c).mp hcenter
  have ht_arith : 2 * t.val + 1 ≤ n := by omega
  exact (val_le_reverseItem_iff t).mpr ht_arith

/--
Appendix D, Lemma 10 consequence, even-center case, using the closed-form
midpoint optimum instead of an external midpoint BFS hypothesis.
-/
theorem lemma10_alpha_le_half_equalizedBasicOptimal_lastActive_le_reverse_succ_center_of_closed_half
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ}
    {ρ : TypePolicy 2 n} {ell : ℝ} {c : Item n}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha_half : alpha ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hsucc : c.val + 1 = (reverseItem c).val)
    (h : Problem6EqualizedBasicOptimal alpha v ρ ell) :
    (TypePolicy.lastActiveTypeZero ρ).val ≤
      (reverseItem (TypePolicy.lastActiveTypeZero ρ)).val := by
  let t : Item n := TypePolicy.lastActiveTypeZero ρ
  have ht_le_c : t.val ≤ c.val := by
    dsimp [t]
    exact lemma10_alpha_le_half_equalizedBasicOptimal_lastActive_le_succ_center_of_closed_half
      hn halpha0 halpha1 halpha_half hpos hdec hsucc h
  have hc_arith : 2 * c.val + 2 = n := by
    simp [reverseItem] at hsucc
    omega
  have ht_arith : 2 * t.val + 1 ≤ n := by omega
  exact (val_le_reverseItem_iff t).mpr ht_arith

/--
Theorem 3 finite-stitch selected-policy core, odd-center first-half chain,
using the Lemma 5 closed midpoint optimum internally.
-/
theorem theorem3_typeFairness_mono_firstHalf_center_chain_of_closed_half
    {n : ℕ} [NeZero n]
    {v : Item n → ℝ} {c : Item n}
    (r : ℕ)
    (alphaSeq : ℕ → ℝ)
    (ρSeq : ℕ → TypePolicy 2 n)
    (ellSeq : ℕ → ℝ)
    (hn : 2 < n)
    (halpha0 : ∀ i, i ≤ r → 0 < alphaSeq i)
    (halpha1 : ∀ i, i ≤ r → alphaSeq i < 1)
    (halpha_half : ∀ i, i ≤ r → alphaSeq i ≤ 1 / 2)
    (hstep : ∀ i, i < r → alphaSeq i ≤ alphaSeq (i + 1))
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter_c : c.val = (reverseItem c).val)
    (hpivot_or_eq :
      ∀ i, i < r →
        TypePolicy.lastActiveTypeZero (ρSeq i) =
          TypePolicy.lastActiveTypeZero (ρSeq (i + 1)) ∨
        alphaSeq i = alphaSeq (i + 1))
    (hopt :
      ∀ i, i ≤ r →
        Problem6EqualizedBasicOptimal (alphaSeq i) v (ρSeq i) (ellSeq i)) :
    TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel (alphaSeq 0) v) (ρSeq 0) ≤
      TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel (alphaSeq r) v) (ρSeq r) := by
  exact theorem3_typeFairness_mono_of_same_selected_or_equal_alpha_chain
    r alphaSeq ρSeq ellSeq hn halpha0 halpha1 halpha_half hstep hpos hdec
    hpivot_or_eq
    (fun i hi =>
      lemma10_alpha_le_half_equalizedBasicOptimal_lastActive_le_reverse_center_of_closed_half
        hn (halpha0 i (Nat.le_of_lt hi))
        (halpha1 i (Nat.le_of_lt hi))
        (halpha_half i (Nat.le_of_lt hi))
        hpos hdec hcenter_c (hopt i (Nat.le_of_lt hi)))
    hopt

/--
Theorem 3 finite-stitch selected-policy core, even-center first-half chain,
using the Lemma 5 closed midpoint optimum internally.
-/
theorem theorem3_typeFairness_mono_firstHalf_succ_center_chain_of_closed_half
    {n : ℕ} [NeZero n]
    {v : Item n → ℝ} {c : Item n}
    (r : ℕ)
    (alphaSeq : ℕ → ℝ)
    (ρSeq : ℕ → TypePolicy 2 n)
    (ellSeq : ℕ → ℝ)
    (hn : 2 < n)
    (halpha0 : ∀ i, i ≤ r → 0 < alphaSeq i)
    (halpha1 : ∀ i, i ≤ r → alphaSeq i < 1)
    (halpha_half : ∀ i, i ≤ r → alphaSeq i ≤ 1 / 2)
    (hstep : ∀ i, i < r → alphaSeq i ≤ alphaSeq (i + 1))
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hsucc : c.val + 1 = (reverseItem c).val)
    (hpivot_or_eq :
      ∀ i, i < r →
        TypePolicy.lastActiveTypeZero (ρSeq i) =
          TypePolicy.lastActiveTypeZero (ρSeq (i + 1)) ∨
        alphaSeq i = alphaSeq (i + 1))
    (hopt :
      ∀ i, i ≤ r →
        Problem6EqualizedBasicOptimal (alphaSeq i) v (ρSeq i) (ellSeq i)) :
    TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel (alphaSeq 0) v) (ρSeq 0) ≤
      TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel (alphaSeq r) v) (ρSeq r) := by
  exact theorem3_typeFairness_mono_of_same_selected_or_equal_alpha_chain
    r alphaSeq ρSeq ellSeq hn halpha0 halpha1 halpha_half hstep hpos hdec
    hpivot_or_eq
    (fun i hi =>
      lemma10_alpha_le_half_equalizedBasicOptimal_lastActive_le_reverse_succ_center_of_closed_half
        hn (halpha0 i (Nat.le_of_lt hi))
        (halpha1 i (Nat.le_of_lt hi))
        (halpha_half i (Nat.le_of_lt hi))
        hpos hdec hsucc (hopt i (Nat.le_of_lt hi)))
    hopt

/--
Appendix D, Lemma 6 with Lemma 10, odd-center case, using the closed-form
midpoint optimum instead of an external midpoint BFS hypothesis.
-/
theorem problem6EqualizedBasicOptimal_typeFairness_eq_one_of_alpha_le_half_center_of_closed_half
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ}
    {ρ : TypePolicy 2 n} {ell : ℝ} {c : Item n}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha_half : alpha ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter_c : c.val = (reverseItem c).val)
    (h : Problem6EqualizedBasicOptimal alpha v ρ ell) :
    TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel alpha v) ρ =
      TypeWeightedRecommendationModel.normalizedTypeUtility
        (twoTypeReducedModel alpha v) ρ 1 := by
  let t : Item n := TypePolicy.lastActiveTypeZero ρ
  have ht_le_c : t.val ≤ c.val := by
    dsimp [t]
    exact lemma10_alpha_le_half_equalizedBasicOptimal_lastActive_le_center_of_closed_half
      hn halpha0 halpha1 halpha_half hpos hdec hcenter_c h
  have ht_center : t.val ≤ (reverseItem t).val := by
    have hc_arith : 2 * c.val + 1 = n :=
      (val_eq_reverseItem_iff c).mp hcenter_c
    have ht_arith : 2 * t.val + 1 ≤ n := by omega
    exact (val_le_reverseItem_iff t).mpr ht_arith
  exact
    problem6EqualizedBasicOptimal_typeFairness_eq_one_of_alpha_le_half_of_pivot_le_reverse
      hn halpha0 halpha1 halpha_half hpos hdec h (by simpa [t] using ht_center)

/--
Appendix D, Lemma 6 with Lemma 10, even-center case, using the closed-form
midpoint optimum instead of an external midpoint BFS hypothesis.
-/
theorem problem6EqualizedBasicOptimal_typeFairness_eq_one_of_alpha_le_half_succ_center_of_closed_half
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ}
    {ρ : TypePolicy 2 n} {ell : ℝ} {c : Item n}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha_half : alpha ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hsucc : c.val + 1 = (reverseItem c).val)
    (h : Problem6EqualizedBasicOptimal alpha v ρ ell) :
    TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel alpha v) ρ =
      TypeWeightedRecommendationModel.normalizedTypeUtility
        (twoTypeReducedModel alpha v) ρ 1 := by
  let t : Item n := TypePolicy.lastActiveTypeZero ρ
  have ht_le_c : t.val ≤ c.val := by
    dsimp [t]
    exact lemma10_alpha_le_half_equalizedBasicOptimal_lastActive_le_succ_center_of_closed_half
      hn halpha0 halpha1 halpha_half hpos hdec hsucc h
  have ht_center : t.val ≤ (reverseItem t).val := by
    have hc_arith : 2 * c.val + 2 = n := by
      simp [reverseItem] at hsucc
      omega
    have ht_arith : 2 * t.val + 1 ≤ n := by omega
    exact (val_le_reverseItem_iff t).mpr ht_arith
  exact
    problem6EqualizedBasicOptimal_typeFairness_eq_one_of_alpha_le_half_of_pivot_le_reverse
      hn halpha0 halpha1 halpha_half hpos hdec h (by simpa [t] using ht_center)

/-- Feasible objective values for Problem 6's LP. -/
def problem6LPValueSet {n : ℕ} [NeZero n]
    (alpha : ℝ) (v : Item n → ℝ) : Set ℝ :=
  {ell | ∃ ρ : TypePolicy 2 n, problem6LPFeasible alpha v ρ ell}

/-- The optimal value of Problem 6's LP. -/
noncomputable def problem6LPOptimalValue {n : ℕ} [NeZero n]
    (alpha : ℝ) (v : Item n → ℝ) : ℝ :=
  sSup (problem6LPValueSet alpha v)

/-- Problem 6 LP feasibility is equivalent to the reduced item-fairness epigraph. -/
theorem problem6LPFeasible_iff_le_itemFairness
    {n : ℕ} [NeZero n]
    (alpha : ℝ) (v : Item n → ℝ) (ρ : TypePolicy 2 n) (ell : ℝ)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j) :
    problem6LPFeasible alpha v ρ ell ↔
      ell ≤ TypeWeightedRecommendationModel.itemFairness
        (twoTypeReducedModel alpha v) ρ := by
  constructor
  · intro h
    unfold TypeWeightedRecommendationModel.itemFairness AppliedModelingLib.finiteMin
    apply Finset.le_inf'
    intro j _hj
    have hden :=
      typeOneShare_denom_pos halpha0 halpha1 (hpos j) (hpos (reverseItem j))
    rw [twoTypeReducedModel_normalizedItemUtility_eq_pairShare
      alpha v ρ j hden]
    exact h j
  · intro h j
    have hden :=
      typeOneShare_denom_pos halpha0 halpha1 (hpos j) (hpos (reverseItem j))
    have hle :
        TypeWeightedRecommendationModel.itemFairness
            (twoTypeReducedModel alpha v) ρ ≤
          TypeWeightedRecommendationModel.normalizedItemUtility
            (twoTypeReducedModel alpha v) ρ j := by
      exact AppliedModelingLib.finiteMin_le
        (TypeWeightedRecommendationModel.normalizedItemUtility
          (twoTypeReducedModel alpha v) ρ) j
    rw [twoTypeReducedModel_normalizedItemUtility_eq_pairShare
      alpha v ρ j hden] at hle
    exact h.trans hle

/-- Problem 6's LP value set is nonempty. -/
theorem problem6LPValueSet_nonempty
    {n : ℕ} [NeZero n]
    (alpha : ℝ) (v : Item n → ℝ)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j) :
    (problem6LPValueSet alpha v).Nonempty := by
  let ρ : TypePolicy 2 n := TypeWeightedRecommendationModel.uniformTypePolicy
  refine ⟨TypeWeightedRecommendationModel.itemFairness
    (twoTypeReducedModel alpha v) ρ, ?_⟩
  exact ⟨ρ, (problem6LPFeasible_iff_le_itemFairness
    alpha v ρ
    (TypeWeightedRecommendationModel.itemFairness
      (twoTypeReducedModel alpha v) ρ)
    halpha0 halpha1 hpos).mpr le_rfl⟩

/-- Problem 6 LP objective values are bounded above by one. -/
theorem problem6LPValueSet_bddAbove
    {n : ℕ} [NeZero n]
    (alpha : ℝ) (v : Item n → ℝ)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j) :
    BddAbove (problem6LPValueSet alpha v) := by
  refine ⟨1, ?_⟩
  intro ell hell
  obtain ⟨ρ, hρ⟩ := hell
  have hle_item :
      ell ≤ TypeWeightedRecommendationModel.itemFairness
        (twoTypeReducedModel alpha v) ρ :=
    (problem6LPFeasible_iff_le_itemFairness
      alpha v ρ ell halpha0 halpha1 hpos).mp hρ
  let j0 : Item n := Classical.choice inferInstance
  have hitem_le :
      TypeWeightedRecommendationModel.itemFairness
          (twoTypeReducedModel alpha v) ρ ≤
        TypeWeightedRecommendationModel.normalizedItemUtility
          (twoTypeReducedModel alpha v) ρ j0 := by
    exact AppliedModelingLib.finiteMin_le
      (TypeWeightedRecommendationModel.normalizedItemUtility
        (twoTypeReducedModel alpha v) ρ) j0
  have hWeightNonneg :
      (twoTypeReducedModel alpha v).NonnegativeWeights :=
    TypeWeightedRecommendationModel.nonnegativeWeights_of_positiveWeights
      (twoTypeReducedModel alpha v)
      (twoTypeReducedModel_positiveWeights alpha v halpha0 halpha1)
  have hUtilNonneg :
      (twoTypeReducedModel alpha v).NonnegativeUtilities :=
    TypeWeightedRecommendationModel.nonnegativeUtilities_of_positiveUtilities
      (twoTypeReducedModel alpha v)
      (twoTypeReducedModel_positiveUtilities alpha v hpos)
  exact hle_item.trans (hitem_le.trans
    (TypeWeightedRecommendationModel.normalizedItemUtility_le_one_of_nonnegative
      (twoTypeReducedModel alpha v) hWeightNonneg hUtilNonneg ρ j0))

/--
Problem 6 LP equivalence: maximizing the paper's LP objective `λ` has the same
value as the reduced type-level item-fairness optimum.
-/
theorem problem6LPOptimalValue_eq_optimalItemFairness
    {n : ℕ} [NeZero n]
    (alpha : ℝ) (v : Item n → ℝ)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j) :
    problem6LPOptimalValue alpha v =
      TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel alpha v) := by
  have hLPNonempty :=
    problem6LPValueSet_nonempty alpha v halpha0 halpha1 hpos
  have hLPBdd :=
    problem6LPValueSet_bddAbove alpha v halpha0 halpha1 hpos
  have hWeightNonneg :
      (twoTypeReducedModel alpha v).NonnegativeWeights :=
    TypeWeightedRecommendationModel.nonnegativeWeights_of_positiveWeights
      (twoTypeReducedModel alpha v)
      (twoTypeReducedModel_positiveWeights alpha v halpha0 halpha1)
  have hUtilNonneg :
      (twoTypeReducedModel alpha v).NonnegativeUtilities :=
    TypeWeightedRecommendationModel.nonnegativeUtilities_of_positiveUtilities
      (twoTypeReducedModel alpha v)
      (twoTypeReducedModel_positiveUtilities alpha v hpos)
  have hItemBdd :
      BddAbove (TypeWeightedRecommendationModel.attainableItemFairnessSet
        (twoTypeReducedModel alpha v)) :=
    TypeWeightedRecommendationModel.attainableItemFairnessSet_bddAbove_of_nonnegative
      (twoTypeReducedModel alpha v) hWeightNonneg hUtilNonneg
  have hItemNonempty :
      (TypeWeightedRecommendationModel.attainableItemFairnessSet
        (twoTypeReducedModel alpha v)).Nonempty := by
    refine ⟨TypeWeightedRecommendationModel.itemFairness
      (twoTypeReducedModel alpha v)
      (TypeWeightedRecommendationModel.uniformTypePolicy (K := 2) (n := n)), ?_⟩
    exact ⟨TypeWeightedRecommendationModel.uniformTypePolicy (K := 2) (n := n), rfl⟩
  apply le_antisymm
  · unfold problem6LPOptimalValue
    refine csSup_le hLPNonempty ?_
    intro ell hell
    obtain ⟨ρ, hρ⟩ := hell
    have hle_item :
        ell ≤ TypeWeightedRecommendationModel.itemFairness
          (twoTypeReducedModel alpha v) ρ :=
      (problem6LPFeasible_iff_le_itemFairness
        alpha v ρ ell halpha0 halpha1 hpos).mp hρ
    have hitem_mem :
        TypeWeightedRecommendationModel.itemFairness
          (twoTypeReducedModel alpha v) ρ ∈
            TypeWeightedRecommendationModel.attainableItemFairnessSet
              (twoTypeReducedModel alpha v) := by
      exact ⟨ρ, rfl⟩
    exact hle_item.trans (le_csSup hItemBdd hitem_mem)
  · unfold TypeWeightedRecommendationModel.optimalItemFairness
    refine csSup_le hItemNonempty ?_
    intro r hr
    obtain ⟨ρ, hr⟩ := hr
    rw [hr]
    have hlp_mem :
        TypeWeightedRecommendationModel.itemFairness
          (twoTypeReducedModel alpha v) ρ ∈ problem6LPValueSet alpha v := by
      exact ⟨ρ, (problem6LPFeasible_iff_le_itemFairness
        alpha v ρ
        (TypeWeightedRecommendationModel.itemFairness
          (twoTypeReducedModel alpha v) ρ)
        halpha0 halpha1 hpos).mpr le_rfl⟩
    exact le_csSup hLPBdd hlp_mem

/--
If the paper's proposed closed-form policy/value pair satisfies the finite
upper-bound certificate, then it is exactly the Problem 6 LP optimum.
-/
theorem problem6LPOptimalValue_eq_of_certificate
    {n : ℕ} [NeZero n]
    (alpha : ℝ) (v : Item n → ℝ) (ell : ℝ)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (cert : Problem6OptimalityCertificate alpha v ell) :
    problem6LPOptimalValue alpha v = ell := by
  have hLPNonempty :=
    problem6LPValueSet_nonempty alpha v halpha0 halpha1 hpos
  have hLPBdd :=
    problem6LPValueSet_bddAbove alpha v halpha0 halpha1 hpos
  apply le_antisymm
  · unfold problem6LPOptimalValue
    refine csSup_le hLPNonempty ?_
    intro ell' hell'
    obtain ⟨ρ, hρ⟩ := hell'
    exact cert.upper_bound ρ ell' hρ
  · unfold problem6LPOptimalValue
    exact le_csSup hLPBdd ⟨cert.policy, cert.feasible⟩

/--
Problem 6 optimal-value theorem for any policy/value pair that is already
known to solve the epigraph LP.
-/
theorem problem6LPOptimalValue_eq_of_policyOptimal
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 2 n} {ell : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hopt : Problem6PolicyOptimal alpha v ρ ell) :
    problem6LPOptimalValue alpha v = ell := by
  exact problem6LPOptimalValue_eq_of_certificate
    alpha v ell halpha0 halpha1 hpos
    { policy := ρ
      feasible := hopt.1
      upper_bound := hopt.2 }

/--
Any Problem 6 policy-optimal solution is feasible for the reduced
maximal-item-fairness problem at level `γ = 1`.
-/
theorem problem6PolicyOptimal_feasibleAtLevel_one
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 2 n} {ell : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hopt : Problem6PolicyOptimal alpha v ρ ell) :
    TypeWeightedRecommendationModel.feasibleAtLevel
      (twoTypeReducedModel alpha v) 1 ρ := by
  have hLP_eq_item :=
    problem6LPOptimalValue_eq_optimalItemFairness
      alpha v halpha0 halpha1 hpos
  have hLP_eq_ell :=
    problem6LPOptimalValue_eq_of_policyOptimal
      halpha0 halpha1 hpos hopt
  have hell_le_item :
      ell ≤ TypeWeightedRecommendationModel.itemFairness
        (twoTypeReducedModel alpha v) ρ :=
    (problem6LPFeasible_iff_le_itemFairness
      alpha v ρ ell halpha0 halpha1 hpos).mp hopt.1
  simpa [TypeWeightedRecommendationModel.feasibleAtLevel] using
    (calc
      TypeWeightedRecommendationModel.optimalItemFairness
          (twoTypeReducedModel alpha v)
          = problem6LPOptimalValue alpha v := hLP_eq_item.symm
      _ = ell := hLP_eq_ell
      _ ≤ TypeWeightedRecommendationModel.itemFairness
          (twoTypeReducedModel alpha v) ρ := hell_le_item)

/--
Conversely, every policy feasible at maximal item-fairness level `γ = 1`
solves Problem 6 when paired with its reduced item-fairness value.
-/
theorem problem6PolicyOptimal_of_feasibleAtLevel_one
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 2 n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hfeas :
      TypeWeightedRecommendationModel.feasibleAtLevel
        (twoTypeReducedModel alpha v) 1 ρ) :
    Problem6PolicyOptimal alpha v ρ
      (TypeWeightedRecommendationModel.itemFairness
        (twoTypeReducedModel alpha v) ρ) := by
  refine ⟨?_, ?_⟩
  · exact (problem6LPFeasible_iff_le_itemFairness
      alpha v ρ
      (TypeWeightedRecommendationModel.itemFairness
        (twoTypeReducedModel alpha v) ρ)
      halpha0 halpha1 hpos).mpr le_rfl
  · intro ρ' ell' hfeas'
    have hell'_le_item :
        ell' ≤ TypeWeightedRecommendationModel.itemFairness
          (twoTypeReducedModel alpha v) ρ' :=
      (problem6LPFeasible_iff_le_itemFairness
        alpha v ρ' ell' halpha0 halpha1 hpos).mp hfeas'
    have hWeightNonneg :
        (twoTypeReducedModel alpha v).NonnegativeWeights :=
      TypeWeightedRecommendationModel.nonnegativeWeights_of_positiveWeights
        (twoTypeReducedModel alpha v)
        (twoTypeReducedModel_positiveWeights alpha v halpha0 halpha1)
    have hUtilNonneg :
        (twoTypeReducedModel alpha v).NonnegativeUtilities :=
      TypeWeightedRecommendationModel.nonnegativeUtilities_of_positiveUtilities
        (twoTypeReducedModel alpha v)
        (twoTypeReducedModel_positiveUtilities alpha v hpos)
    have hbdd :
        BddAbove (TypeWeightedRecommendationModel.attainableItemFairnessSet
          (twoTypeReducedModel alpha v)) :=
      TypeWeightedRecommendationModel.attainableItemFairnessSet_bddAbove_of_nonnegative
        (twoTypeReducedModel alpha v) hWeightNonneg hUtilNonneg
    have hitem_mem :
        TypeWeightedRecommendationModel.itemFairness
          (twoTypeReducedModel alpha v) ρ' ∈
            TypeWeightedRecommendationModel.attainableItemFairnessSet
              (twoTypeReducedModel alpha v) := by
      exact ⟨ρ', rfl⟩
    have hitem_le_opt :
        TypeWeightedRecommendationModel.itemFairness
            (twoTypeReducedModel alpha v) ρ' ≤
          TypeWeightedRecommendationModel.optimalItemFairness
            (twoTypeReducedModel alpha v) :=
      le_csSup hbdd hitem_mem
    have hopt_le_item :
        TypeWeightedRecommendationModel.optimalItemFairness
            (twoTypeReducedModel alpha v) ≤
          TypeWeightedRecommendationModel.itemFairness
            (twoTypeReducedModel alpha v) ρ := by
      simpa [TypeWeightedRecommendationModel.feasibleAtLevel] using hfeas
    exact hell'_le_item.trans (hitem_le_opt.trans hopt_le_item)

/--
The paper's selected equality-form optimal BFS policy is feasible for the
reduced maximal-item-fairness problem at level `γ = 1`.
-/
theorem problem6EqualizedBasicOptimal_feasibleAtLevel_one
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 2 n} {ell : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (h : Problem6EqualizedBasicOptimal alpha v ρ ell) :
    TypeWeightedRecommendationModel.feasibleAtLevel
      (twoTypeReducedModel alpha v) 1 ρ := by
  exact problem6PolicyOptimal_feasibleAtLevel_one
    halpha0 halpha1 hpos h.optimal

/--
The closed Lemma 5 construction supplies a reduced `γ = 1` feasible policy:
an equality-form optimal BFS policy attains the maximal item-fairness level.
-/
theorem problem6EqualizedBasicOptimal_feasibleAtLevel_one_exists {n : ℕ}
    [NeZero n] {alpha : ℝ} {v : Item n → ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v) :
    ∃ (ρ : TypePolicy 2 n) (ell : ℝ),
      Problem6EqualizedBasicOptimal alpha v ρ ell ∧
        TypeWeightedRecommendationModel.feasibleAtLevel
          (twoTypeReducedModel alpha v) 1 ρ := by
  rcases problem6EqualizedBasicOptimal_exists
      (alpha := alpha) (v := v) halpha0 halpha1 hpos hdec with
    ⟨ρ, ell, h⟩
  exact ⟨ρ, ell, h,
    problem6EqualizedBasicOptimal_feasibleAtLevel_one
      halpha0 halpha1 hpos h⟩

/--
The selected equality-form optimal BFS policy contributes its type-fairness
value to the `γ = 1` feasible type-fairness set.
-/
theorem problem6EqualizedBasicOptimal_typeFairness_mem_attainable_one
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 2 n} {ell : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (h : Problem6EqualizedBasicOptimal alpha v ρ ell) :
    TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel alpha v) ρ ∈
      TypeWeightedRecommendationModel.attainableTypeFairnessAtLevel
        (twoTypeReducedModel alpha v) 1 := by
  exact ⟨ρ,
    problem6EqualizedBasicOptimal_feasibleAtLevel_one
      halpha0 halpha1 hpos h,
    rfl⟩

/--
The selected Problem 6 policy's type fairness is bounded above by the reduced
`U^*_min(1, α)` value.
-/
theorem problem6EqualizedBasicOptimal_typeFairness_le_optimalTypeFairnessAtLevel_one
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 2 n} {ell : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (h : Problem6EqualizedBasicOptimal alpha v ρ ell) :
    TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel alpha v) ρ ≤
      TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel alpha v) 1 := by
  have hbdd :
      BddAbove (TypeWeightedRecommendationModel.attainableTypeFairnessAtLevel
        (twoTypeReducedModel alpha v) 1) :=
    TypeWeightedRecommendationModel.attainableTypeFairnessAtLevel_bddAbove_of_rowHasPositiveItem
      (twoTypeReducedModel alpha v)
      (twoTypeReducedModel_rowHasPositiveItem alpha v hpos) 1
  exact le_csSup hbdd
    (problem6EqualizedBasicOptimal_typeFairness_mem_attainable_one
      halpha0 halpha1 hpos h)

/--
For the closed policy, type `1`'s raw utility is at least the contribution
from receiving the last item, whose mirror value is the first item's value.
-/
theorem problem6ClosedTypeOneRawUtility_ge_first_mul_closedY_last
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hpivot : Problem6ClosedNonnegativePivots alpha v t) :
    v firstItem * problem6ClosedY alpha v t lastItem ≤
      problem6ClosedTypeOneRawUtility alpha v t := by
  rw [problem6ClosedTypeOneRawUtility_eq_mirror_sum]
  have hnonneg :
      ∀ j : Item n,
        0 ≤ v j * problem6ClosedY alpha v t (reverseItem j) := by
    intro j
    exact mul_nonneg (hpos j).le
      (problem6ClosedY_nonneg halpha0 halpha1 hpos hpivot (reverseItem j))
  have hsingle :
      v firstItem * problem6ClosedY alpha v t (reverseItem firstItem) ≤
        ∑ j : Item n, v j * problem6ClosedY alpha v t (reverseItem j) :=
    Finset.single_le_sum (by intro j _hj; exact hnonneg j)
      (Finset.mem_univ firstItem)
  simpa [lastItem] using hsingle

/--
If the pivot lies before the last item, the closed-form last-item `y`
coordinate is at least the Lemma 5 closed value.
-/
theorem problem6ClosedY_last_ge_closedValue_of_pivot_lt_last
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (htlast : t.val < (lastItem : Item n).val) :
    problem6ClosedValue alpha v t ≤
      problem6ClosedY alpha v t lastItem := by
  rw [problem6ClosedY_after alpha v htlast]
  have hval_pos :
      0 < problem6ClosedValue alpha v t :=
    problem6ClosedValue_pos t halpha0 halpha1 hpos
  have hcomp_pos :
      0 < 1 - pairShare alpha v lastItem :=
    one_sub_pairShare_pos lastItem halpha0 halpha1 hpos
  have hcomp_le_one :
      1 - pairShare alpha v lastItem ≤ 1 := by
    have hqpos : 0 < pairShare alpha v lastItem :=
      pairShare_pos lastItem halpha0 halpha1 hpos
    linarith
  calc
    problem6ClosedValue alpha v t =
        problem6ClosedValue alpha v t / 1 := by ring
    _ ≤ problem6ClosedValue alpha v t /
        (1 - pairShare alpha v lastItem) := by
          exact (div_le_div_iff_of_pos_left
            hval_pos (by norm_num : (0 : ℝ) < 1) hcomp_pos).2 hcomp_le_one

/--
The displayed Appendix E lower-bound step: the closed policy gives type `1`
normalized utility at least the closed Problem 6 value.
-/
theorem problem6ClosedPolicy_normalizedTypeUtility_one_ge_closedValue_of_pivot_lt_last
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hpivot : Problem6ClosedNonnegativePivots alpha v t)
    (htlast : t.val < (lastItem : Item n).val) :
    problem6ClosedValue alpha v t ≤
      TypeWeightedRecommendationModel.normalizedTypeUtility
        (twoTypeReducedModel alpha v)
        (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot) 1 := by
  have hy_ge :
      problem6ClosedValue alpha v t ≤
        problem6ClosedY alpha v t lastItem :=
    problem6ClosedY_last_ge_closedValue_of_pivot_lt_last
      halpha0 halpha1 hpos htlast
  have hraw_ge_y :
      v firstItem * problem6ClosedY alpha v t lastItem ≤
        problem6ClosedTypeOneRawUtility alpha v t :=
    problem6ClosedTypeOneRawUtility_ge_first_mul_closedY_last
      halpha0 halpha1 hpos hpivot
  have hfirst_pos : 0 < v (firstItem : Item n) := hpos firstItem
  have hraw_ge :
      v firstItem * problem6ClosedValue alpha v t ≤
        problem6ClosedTypeOneRawUtility alpha v t := by
    exact (mul_le_mul_of_nonneg_left hy_ge hfirst_pos.le).trans hraw_ge_y
  have hbest :
      TypeWeightedRecommendationModel.bestItemUtility
          (twoTypeReducedModel alpha v) 1 =
        v firstItem := by
    rw [twoTypeReducedModel_bestItemUtility_one_eq_zero alpha v]
    change AppliedModelingLib.finiteMax v = v firstItem
    exact finiteMax_eq_firstItem hdec
  unfold TypeWeightedRecommendationModel.normalizedTypeUtility
  rw [problem6ClosedPolicy_rawTypeUtility_one_eq
    halpha0 halpha1 hpos hpivot, hbest]
  rw [le_div_iff₀ hfirst_pos]
  nlinarith

/--
When type `1` is the minimum-utility type for the closed policy, the closed
policy's type fairness is at least the Lemma 5 closed value.
-/
theorem problem6ClosedPolicy_typeFairness_ge_closedValue_of_alpha_le_half_of_pivot_le_reverse_of_pivot_lt_last
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha_half : alpha ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hpivot : Problem6ClosedNonnegativePivots alpha v t)
    (hcenter : t.val ≤ (reverseItem t).val)
    (htlast : t.val < (lastItem : Item n).val) :
    problem6ClosedValue alpha v t ≤
      TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel alpha v)
        (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot) := by
  rw [problem6ClosedPolicy_typeFairness_eq_one_of_alpha_le_half_of_pivot_le_reverse
    halpha0 halpha1 halpha_half hpos hdec hpivot hcenter]
  exact problem6ClosedPolicy_normalizedTypeUtility_one_ge_closedValue_of_pivot_lt_last
    halpha0 halpha1 hpos hdec hpivot htlast

/--
Appendix E true-model lower bound, odd midpoint case: at `α = 1/2`, the
reduced maximal-item-fairness user optimum is strictly above `1/n`.
-/
theorem theorem4_trueModel_optimalTypeFairnessAtLevel_one_gt_inv_card_half_center
    {n : ℕ} [NeZero n]
    {v : Item n → ℝ} {t : Item n}
    (hn : 1 < n)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter : t.val = (reverseItem t).val) :
    (n : ℝ)⁻¹ <
      TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel (1 / 2) v) 1 := by
  let hbounds : Problem6ClosedPivotDenominatorBounds (1 / 2) v t :=
    problem6ClosedPivotDenominatorBounds_half_center
      (v := v) (t := t) hpos hcenter
  let cert : Problem6ClosedOptimalityCertificate (1 / 2) v t :=
    problem6ClosedOptimalityCertificate_of_denominatorBounds
      (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) hpos hdec hbounds
  let hpivot : Problem6ClosedNonnegativePivots (1 / 2) v t :=
    problem6ClosedNonnegativePivots_of_denominatorBounds
      (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) hpos hbounds
  let ρ : TypePolicy 2 n :=
    problem6ClosedPolicy (1 / 2) v t
      (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) hpos hpivot
  have hclosed :
      Problem6EqualizedBasicOptimal (1 / 2) v ρ
        (problem6ClosedValue (1 / 2) v t) := by
    dsimp [ρ, hpivot, cert, hbounds]
    exact problem6EqualizedBasicOptimal_of_closed_certificate
      (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) hpos cert
  have hcenter_le : t.val ≤ (reverseItem t).val := le_of_eq hcenter
  have htlast : t.val < (lastItem : Item n).val := by
    have hcenter_arith : 2 * t.val + 1 = n := by
      exact (val_eq_reverseItem_iff t).mp hcenter
    rw [lastItem_val]
    omega
  have htf_ge :
      problem6ClosedValue (1 / 2) v t ≤
        TypeWeightedRecommendationModel.typeFairness
          (twoTypeReducedModel (1 / 2) v) ρ := by
    dsimp [ρ]
    exact
      problem6ClosedPolicy_typeFairness_ge_closedValue_of_alpha_le_half_of_pivot_le_reverse_of_pivot_lt_last
        (by norm_num : (0 : ℝ) < 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)
        (by norm_num : (1 / 2 : ℝ) ≤ 1 / 2)
        hpos hdec hpivot hcenter_le htlast
  have htf_le_opt :
      TypeWeightedRecommendationModel.typeFairness
          (twoTypeReducedModel (1 / 2) v) ρ ≤
        TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
          (twoTypeReducedModel (1 / 2) v) 1 :=
    problem6EqualizedBasicOptimal_typeFairness_le_optimalTypeFairnessAtLevel_one
      (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) hpos hclosed
  exact lt_of_lt_of_le
    (problem6ClosedValue_half_center_gt_inv_card
      (v := v) (t := t) hn hpos hdec hcenter)
    (htf_ge.trans htf_le_opt)

/--
Appendix E true-model lower bound, even midpoint case: at `α = 1/2`, the
reduced maximal-item-fairness user optimum is strictly above `1/n`.
-/
theorem theorem4_trueModel_optimalTypeFairnessAtLevel_one_gt_inv_card_half_succ_center
    {n : ℕ} [NeZero n]
    {v : Item n → ℝ} {t : Item n}
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hsucc : t.val + 1 = (reverseItem t).val) :
    (n : ℝ)⁻¹ <
      TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel (1 / 2) v) 1 := by
  let hbounds : Problem6ClosedPivotDenominatorBounds (1 / 2) v t :=
    problem6ClosedPivotDenominatorBounds_half_succ_center
      (v := v) (t := t) hpos hsucc
  let cert : Problem6ClosedOptimalityCertificate (1 / 2) v t :=
    problem6ClosedOptimalityCertificate_of_denominatorBounds
      (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) hpos hdec hbounds
  let hpivot : Problem6ClosedNonnegativePivots (1 / 2) v t :=
    problem6ClosedNonnegativePivots_of_denominatorBounds
      (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) hpos hbounds
  let ρ : TypePolicy 2 n :=
    problem6ClosedPolicy (1 / 2) v t
      (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) hpos hpivot
  have hclosed :
      Problem6EqualizedBasicOptimal (1 / 2) v ρ
        (problem6ClosedValue (1 / 2) v t) := by
    dsimp [ρ, hpivot, cert, hbounds]
    exact problem6EqualizedBasicOptimal_of_closed_certificate
      (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) hpos cert
  have hcenter_le : t.val ≤ (reverseItem t).val := by omega
  have htlast : t.val < (lastItem : Item n).val := by
    have hsucc_arith : 2 * t.val + 2 = n := by
      simp [reverseItem] at hsucc
      omega
    rw [lastItem_val]
    omega
  have htf_ge :
      problem6ClosedValue (1 / 2) v t ≤
        TypeWeightedRecommendationModel.typeFairness
          (twoTypeReducedModel (1 / 2) v) ρ := by
    dsimp [ρ]
    exact
      problem6ClosedPolicy_typeFairness_ge_closedValue_of_alpha_le_half_of_pivot_le_reverse_of_pivot_lt_last
        (by norm_num : (0 : ℝ) < 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)
        (by norm_num : (1 / 2 : ℝ) ≤ 1 / 2)
        hpos hdec hpivot hcenter_le htlast
  have htf_le_opt :
      TypeWeightedRecommendationModel.typeFairness
          (twoTypeReducedModel (1 / 2) v) ρ ≤
        TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
          (twoTypeReducedModel (1 / 2) v) 1 :=
    problem6EqualizedBasicOptimal_typeFairness_le_optimalTypeFairnessAtLevel_one
      (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) hpos hclosed
  exact lt_of_lt_of_le
    (problem6ClosedValue_half_succ_center_gt_inv_card
      (v := v) (t := t) hpos hdec hsucc)
    (htf_ge.trans htf_le_opt)

/--
If the selected equality-form optimal BFS policy upper-bounds the type fairness
of every policy feasible at level `γ = 1`, then it realizes the reduced
`U^*_min(1, α)` optimum.
-/
theorem problem6EqualizedBasicOptimal_optimalTypeFairnessAtLevel_one_eq_of_upper_bound
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 2 n} {ell : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (h : Problem6EqualizedBasicOptimal alpha v ρ ell)
    (hupper :
      ∀ ρ' : TypePolicy 2 n,
        TypeWeightedRecommendationModel.feasibleAtLevel
          (twoTypeReducedModel alpha v) 1 ρ' →
        TypeWeightedRecommendationModel.typeFairness
          (twoTypeReducedModel alpha v) ρ' ≤
        TypeWeightedRecommendationModel.typeFairness
          (twoTypeReducedModel alpha v) ρ) :
    TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel alpha v) 1 =
      TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel alpha v) ρ := by
  apply le_antisymm
  · unfold TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
    refine csSup_le ?_ ?_
    · exact ⟨TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel alpha v) ρ,
        problem6EqualizedBasicOptimal_typeFairness_mem_attainable_one
          halpha0 halpha1 hpos h⟩
    · intro r hr
      rcases hr with ⟨ρ', hfeas', hr⟩
      rw [hr]
      exact hupper ρ' hfeas'
  · exact
      problem6EqualizedBasicOptimal_typeFairness_le_optimalTypeFairnessAtLevel_one
        halpha0 halpha1 hpos h

/--
Upper-bound bridge, uniqueness form: any `γ = 1` feasible policy that
equalizes all Problem 6 item constraints and satisfies the shared-item sparsity
bound is the selected equality-form optimal BFS policy.
-/
theorem problem6EqualizedBasicOptimal_policy_eq_of_feasibleAtLevel_one_equalized_shared
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {ρ ρ' : TypePolicy 2 n} {ell : ℝ}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (h : Problem6EqualizedBasicOptimal alpha v ρ ell)
    (hfeas' :
      TypeWeightedRecommendationModel.feasibleAtLevel
        (twoTypeReducedModel alpha v) 1 ρ')
    (hitem_eq' :
      ∀ l : Item n,
        pairShare alpha v l * (ρ' 0 l).toReal +
          (1 - pairShare alpha v l) * (ρ' 1 l).toReal =
        TypeWeightedRecommendationModel.itemFairness
          (twoTypeReducedModel alpha v) ρ')
    (hshared' : TypePolicy.SharedItemsBound ρ') :
    ρ' = ρ := by
  let ell' : ℝ :=
    TypeWeightedRecommendationModel.itemFairness
      (twoTypeReducedModel alpha v) ρ'
  have hopt' : Problem6PolicyOptimal alpha v ρ' ell' := by
    dsimp [ell']
    exact problem6PolicyOptimal_of_feasibleAtLevel_one
      halpha0 halpha1 hpos hfeas'
  have huniq :=
    problem6PolicyOptimal_equalized_unique_sparseActive_of_two_lt
      hn halpha0 halpha1 hpos hdec h.item_eq
      (by simpa [ell'] using hitem_eq')
      h.optimal hopt'
      (problem6_sharedItemsBound_of_equalizedBasicOptimal
        halpha0 halpha1 hpos h)
      hshared'
  rcases huniq with ⟨_t, _hsparse, _hsparse', _hell, hx, hy⟩
  funext k
  fin_cases k
  · apply pmf_eq_of_forall_toReal_eq
    intro j
    change ((ρ' 0) j).toReal = ((ρ 0) j).toReal
    exact (congrFun hx j).symm
  · apply pmf_eq_of_forall_toReal_eq
    intro j
    change ((ρ' 1) j).toReal = ((ρ 1) j).toReal
    exact (congrFun hy j).symm

/--
The corresponding type-fairness uniqueness bridge for `γ = 1` feasible,
equalized, shared policies.
-/
theorem problem6EqualizedBasicOptimal_typeFairness_eq_of_feasibleAtLevel_one_equalized_shared
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {ρ ρ' : TypePolicy 2 n} {ell : ℝ}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (h : Problem6EqualizedBasicOptimal alpha v ρ ell)
    (hfeas' :
      TypeWeightedRecommendationModel.feasibleAtLevel
        (twoTypeReducedModel alpha v) 1 ρ')
    (hitem_eq' :
      ∀ l : Item n,
        pairShare alpha v l * (ρ' 0 l).toReal +
          (1 - pairShare alpha v l) * (ρ' 1 l).toReal =
        TypeWeightedRecommendationModel.itemFairness
          (twoTypeReducedModel alpha v) ρ')
    (hshared' : TypePolicy.SharedItemsBound ρ') :
    TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel alpha v) ρ' =
      TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel alpha v) ρ := by
  rw [problem6EqualizedBasicOptimal_policy_eq_of_feasibleAtLevel_one_equalized_shared
    hn halpha0 halpha1 hpos hdec h hfeas' hitem_eq' hshared']

/--
If every `γ = 1` feasible policy is already in the paper's equalized/shared
canonical form, then the selected equality-form optimal BFS policy realizes the
reduced `U^*_min(1, α)` optimum.
-/
theorem problem6EqualizedBasicOptimal_optimalTypeFairnessAtLevel_one_eq_of_all_feasible_equalized_shared
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 2 n} {ell : ℝ}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (h : Problem6EqualizedBasicOptimal alpha v ρ ell)
    (hcanonical :
      ∀ ρ' : TypePolicy 2 n,
        TypeWeightedRecommendationModel.feasibleAtLevel
          (twoTypeReducedModel alpha v) 1 ρ' →
        (∀ l : Item n,
          pairShare alpha v l * (ρ' 0 l).toReal +
            (1 - pairShare alpha v l) * (ρ' 1 l).toReal =
          TypeWeightedRecommendationModel.itemFairness
            (twoTypeReducedModel alpha v) ρ') ∧
        TypePolicy.SharedItemsBound ρ') :
    TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel alpha v) 1 =
      TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel alpha v) ρ := by
  exact
    problem6EqualizedBasicOptimal_optimalTypeFairnessAtLevel_one_eq_of_upper_bound
      halpha0 halpha1 hpos h
      (fun ρ' hfeas' =>
        let hcanon := hcanonical ρ' hfeas'
        le_of_eq
          (problem6EqualizedBasicOptimal_typeFairness_eq_of_feasibleAtLevel_one_equalized_shared
            hn halpha0 halpha1 hpos hdec h hfeas'
            hcanon.1 hcanon.2))

/--
Proposition-1-shaped upper-bound bridge: if every reduced `γ = 1` feasible
policy has an equalized/shared canonical representative with weakly larger
type fairness, then the selected equality-form optimal BFS policy realizes the
reduced `U^*_min(1, α)` optimum.
-/
theorem problem6EqualizedBasicOptimal_optimalTypeFairnessAtLevel_one_eq_of_feasible_canonicalization
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 2 n} {ell : ℝ}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (h : Problem6EqualizedBasicOptimal alpha v ρ ell)
    (hcanonical :
      ∀ ρ' : TypePolicy 2 n,
        TypeWeightedRecommendationModel.feasibleAtLevel
          (twoTypeReducedModel alpha v) 1 ρ' →
        ∃ ρbar : TypePolicy 2 n,
          TypeWeightedRecommendationModel.feasibleAtLevel
            (twoTypeReducedModel alpha v) 1 ρbar ∧
          (∀ l : Item n,
            pairShare alpha v l * (ρbar 0 l).toReal +
              (1 - pairShare alpha v l) * (ρbar 1 l).toReal =
            TypeWeightedRecommendationModel.itemFairness
              (twoTypeReducedModel alpha v) ρbar) ∧
          TypePolicy.SharedItemsBound ρbar ∧
          TypeWeightedRecommendationModel.typeFairness
            (twoTypeReducedModel alpha v) ρ' ≤
          TypeWeightedRecommendationModel.typeFairness
            (twoTypeReducedModel alpha v) ρbar) :
    TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel alpha v) 1 =
      TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel alpha v) ρ := by
  exact
    problem6EqualizedBasicOptimal_optimalTypeFairnessAtLevel_one_eq_of_upper_bound
      halpha0 halpha1 hpos h
      (fun ρ' hfeas' => by
        rcases hcanonical ρ' hfeas' with
          ⟨ρbar, hbar_feas, hbar_eq, hbar_shared, hle_bar⟩
        have hbar_type :
            TypeWeightedRecommendationModel.typeFairness
                (twoTypeReducedModel alpha v) ρbar =
              TypeWeightedRecommendationModel.typeFairness
                (twoTypeReducedModel alpha v) ρ :=
          problem6EqualizedBasicOptimal_typeFairness_eq_of_feasibleAtLevel_one_equalized_shared
            hn halpha0 halpha1 hpos hdec h hbar_feas hbar_eq hbar_shared
        exact hle_bar.trans hbar_type.le)

/--
For an equality-form optimal Problem 6 policy, every displayed item equality
is equality to the reduced item-fairness value itself.
-/
theorem problem6EqualizedBasicOptimal_item_value_eq_itemFairness
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 2 n} {ell : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (h : Problem6EqualizedBasicOptimal alpha v ρ ell)
    (l : Item n) :
    pairShare alpha v l * (ρ 0 l).toReal +
        (1 - pairShare alpha v l) * (ρ 1 l).toReal =
      TypeWeightedRecommendationModel.itemFairness
        (twoTypeReducedModel alpha v) ρ := by
  let T := twoTypeReducedModel alpha v
  have hell_le_item :
      ell ≤ TypeWeightedRecommendationModel.itemFairness T ρ := by
    dsimp [T]
    exact (problem6LPFeasible_iff_le_itemFairness
      alpha v ρ ell halpha0 halpha1 hpos).mp h.optimal.1
  let j0 : Item n := Classical.choice inferInstance
  have hitem_le_ell :
      TypeWeightedRecommendationModel.itemFairness T ρ ≤ ell := by
    have hle :
        TypeWeightedRecommendationModel.itemFairness T ρ ≤
          TypeWeightedRecommendationModel.normalizedItemUtility T ρ j0 :=
      AppliedModelingLib.finiteMin_le
        (TypeWeightedRecommendationModel.normalizedItemUtility T ρ) j0
    have hden :
        0 < alpha * v j0 + (1 - alpha) * v (reverseItem j0) :=
      typeOneShare_denom_pos halpha0 halpha1
        (hpos j0) (hpos (reverseItem j0))
    dsimp [T] at hle
    rw [twoTypeReducedModel_normalizedItemUtility_eq_pairShare
      alpha v ρ j0 hden] at hle
    exact hle.trans (le_of_eq (h.item_eq j0))
  have hell_eq_item :
      ell = TypeWeightedRecommendationModel.itemFairness T ρ :=
    le_antisymm hell_le_item hitem_le_ell
  exact (h.item_eq l).trans (by simpa [T] using hell_eq_item)

/--
Canonicalization bridge in the LP-selection form: if every reduced `γ = 1`
feasible policy is weakly dominated in type fairness by some equality-form
optimal BFS representative, then the Proposition-1-shaped canonical
representative required above exists.
-/
theorem problem6_feasibleCanonicalization_of_equalizedBasicOptimal_dominance
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdom :
      ∀ ρ' : TypePolicy 2 n,
        TypeWeightedRecommendationModel.feasibleAtLevel
          (twoTypeReducedModel alpha v) 1 ρ' →
        ∃ (ρbar : TypePolicy 2 n) (ellbar : ℝ),
          Problem6EqualizedBasicOptimal alpha v ρbar ellbar ∧
          TypeWeightedRecommendationModel.typeFairness
            (twoTypeReducedModel alpha v) ρ' ≤
          TypeWeightedRecommendationModel.typeFairness
            (twoTypeReducedModel alpha v) ρbar) :
      ∀ ρ' : TypePolicy 2 n,
        TypeWeightedRecommendationModel.feasibleAtLevel
          (twoTypeReducedModel alpha v) 1 ρ' →
        ∃ ρbar : TypePolicy 2 n,
          TypeWeightedRecommendationModel.feasibleAtLevel
            (twoTypeReducedModel alpha v) 1 ρbar ∧
          (∀ l : Item n,
            pairShare alpha v l * (ρbar 0 l).toReal +
              (1 - pairShare alpha v l) * (ρbar 1 l).toReal =
            TypeWeightedRecommendationModel.itemFairness
              (twoTypeReducedModel alpha v) ρbar) ∧
          TypePolicy.SharedItemsBound ρbar ∧
          TypeWeightedRecommendationModel.typeFairness
            (twoTypeReducedModel alpha v) ρ' ≤
          TypeWeightedRecommendationModel.typeFairness
            (twoTypeReducedModel alpha v) ρbar := by
  intro ρ' hfeas'
  rcases hdom ρ' hfeas' with ⟨ρbar, ellbar, hbar, hle⟩
  refine ⟨ρbar, ?_, ?_, ?_, hle⟩
  · exact problem6EqualizedBasicOptimal_feasibleAtLevel_one
      halpha0 halpha1 hpos hbar
  · intro l
    exact problem6EqualizedBasicOptimal_item_value_eq_itemFairness
      halpha0 halpha1 hpos hbar l
  · exact problem6_sharedItemsBound_of_equalizedBasicOptimal
      halpha0 halpha1 hpos hbar

/--
Selected-policy optimality bridge in LP-selection form: the selected
equality-form optimal BFS policy realizes the reduced `U^*_min(1, α)` optimum
if every `γ = 1` feasible policy is weakly dominated by an equality-form
optimal BFS representative.
-/
theorem problem6EqualizedBasicOptimal_optimalTypeFairnessAtLevel_one_eq_of_equalizedBasicOptimal_dominance
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 2 n} {ell : ℝ}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (h : Problem6EqualizedBasicOptimal alpha v ρ ell)
    (hdom :
      ∀ ρ' : TypePolicy 2 n,
        TypeWeightedRecommendationModel.feasibleAtLevel
          (twoTypeReducedModel alpha v) 1 ρ' →
        ∃ (ρbar : TypePolicy 2 n) (ellbar : ℝ),
          Problem6EqualizedBasicOptimal alpha v ρbar ellbar ∧
          TypeWeightedRecommendationModel.typeFairness
            (twoTypeReducedModel alpha v) ρ' ≤
          TypeWeightedRecommendationModel.typeFairness
            (twoTypeReducedModel alpha v) ρbar) :
    TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel alpha v) 1 =
      TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel alpha v) ρ := by
  exact
    problem6EqualizedBasicOptimal_optimalTypeFairnessAtLevel_one_eq_of_feasible_canonicalization
      hn halpha0 halpha1 hpos hdec h
      (problem6_feasibleCanonicalization_of_equalizedBasicOptimal_dominance
        halpha0 halpha1 hpos hdom)

/--
Selected-policy optimality bridge from a single optimal-at-level equality-form
BFS representative: if some equality-form optimal BFS policy solves the
reduced `γ = 1` type-fairness problem, then the selected equality-form optimal
BFS policy realizes the same `U^*_min(1, α)` value.
-/
theorem problem6EqualizedBasicOptimal_optimalTypeFairnessAtLevel_one_eq_of_equalizedBasicOptimal_isOptimalAtLevel
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ}
    {ρ ρstar : TypePolicy 2 n} {ell ellstar : ℝ}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (h : Problem6EqualizedBasicOptimal alpha v ρ ell)
    (hstar : Problem6EqualizedBasicOptimal alpha v ρstar ellstar)
    (hstar_opt :
      TypeWeightedRecommendationModel.IsOptimalAtLevel
        (twoTypeReducedModel alpha v) 1 ρstar) :
    TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel alpha v) 1 =
      TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel alpha v) ρ := by
  exact
    problem6EqualizedBasicOptimal_optimalTypeFairnessAtLevel_one_eq_of_equalizedBasicOptimal_dominance
      hn halpha0 halpha1 hpos hdec h
      (fun ρ' hfeas' =>
        ⟨ρstar, ellstar, hstar,
          TypeWeightedRecommendationModel.typeFairness_le_of_isOptimalAtLevel
            (twoTypeReducedModel alpha v)
            (twoTypeReducedModel_rowHasPositiveItem alpha v hpos)
            hstar_opt hfeas'⟩)

/--
Closed-form Problem 6 optimal-value theorem: after the paper-specific
denominator and upper-bound certificate is supplied, the LP optimum is the
Lemma 5 closed value.
-/
theorem problem6LPOptimalValue_eq_closedValue_of_closed_certificate
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (cert : Problem6ClosedOptimalityCertificate alpha v t) :
    problem6LPOptimalValue alpha v = problem6ClosedValue alpha v t := by
  exact problem6LPOptimalValue_eq_of_certificate
    alpha v (problem6ClosedValue alpha v t) halpha0 halpha1 hpos
    (problem6OptimalityCertificate_of_closed halpha0 halpha1 hpos cert)

/--
First-half dominance consequence of the type-`1` utility dual: for a closed
Lemma 5 pivot at or before its mirror, every reduced `γ = 1` feasible policy has
type fairness no larger than the closed policy.
-/
theorem problem6ClosedPolicy_typeFairness_dominates_feasibleAtLevel_one_of_closed_certificate_alpha_le_half_of_pivot_le_reverse
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha_half : alpha ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (cert : Problem6ClosedOptimalityCertificate alpha v t)
    (hcenter : t.val ≤ (reverseItem t).val)
    (ρ : TypePolicy 2 n)
    (hfeas :
      TypeWeightedRecommendationModel.feasibleAtLevel
        (twoTypeReducedModel alpha v) 1 ρ) :
    TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel alpha v) ρ ≤
      TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel alpha v)
        (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos
          (problem6ClosedNonnegativePivots_of_denominatorBounds
            halpha0 halpha1 hpos cert.denominator_bounds)) := by
  let T := twoTypeReducedModel alpha v
  let hpivot : Problem6ClosedNonnegativePivots alpha v t :=
    problem6ClosedNonnegativePivots_of_denominatorBounds
      halpha0 halpha1 hpos cert.denominator_bounds
  let ρclosed : TypePolicy 2 n :=
    problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot
  have hLP_closed :
      problem6LPOptimalValue alpha v = problem6ClosedValue alpha v t :=
    problem6LPOptimalValue_eq_closedValue_of_closed_certificate
      halpha0 halpha1 hpos cert
  have hitem_opt :
      TypeWeightedRecommendationModel.optimalItemFairness T =
        problem6ClosedValue alpha v t := by
    dsimp [T]
    rw [← problem6LPOptimalValue_eq_optimalItemFairness
      alpha v halpha0 halpha1 hpos]
    exact hLP_closed
  have hitem :
      problem6ClosedValue alpha v t ≤
        TypeWeightedRecommendationModel.itemFairness T ρ := by
    have h := hfeas
    change TypeWeightedRecommendationModel.feasibleAtLevel T 1 ρ at h
    unfold TypeWeightedRecommendationModel.feasibleAtLevel at h
    rw [one_mul, hitem_opt] at h
    exact h
  have hLPFeas :
      problem6LPFeasible alpha v ρ (problem6ClosedValue alpha v t) := by
    simpa [T] using (problem6LPFeasible_iff_le_itemFairness
      alpha v ρ (problem6ClosedValue alpha v t)
      halpha0 halpha1 hpos).mpr hitem
  have hraw :
      TypeWeightedRecommendationModel.rawTypeUtility T ρ 1 ≤
        problem6ClosedTypeOneRawUtility alpha v t := by
    dsimp [T]
    exact
      problem6_typeOneRawUtility_le_closedTypeOneRawUtility_of_closedValue_feasible
        ρ halpha0 halpha1 hpos hdec hLPFeas
  have hbest_nonneg :
      0 ≤ TypeWeightedRecommendationModel.bestItemUtility T 1 := by
    dsimp [T]
    rw [twoTypeReducedModel_bestItemUtility_one_eq_zero alpha v]
    exact (twoTypeReducedModel_bestItemUtility_zero_pos alpha v hpos).le
  have hnorm :
      TypeWeightedRecommendationModel.normalizedTypeUtility T ρ 1 ≤
        TypeWeightedRecommendationModel.normalizedTypeUtility T ρclosed 1 := by
    unfold TypeWeightedRecommendationModel.normalizedTypeUtility
    dsimp [T, ρclosed, hpivot]
    rw [problem6ClosedPolicy_rawTypeUtility_one_eq
      halpha0 halpha1 hpos]
    exact div_le_div_of_nonneg_right hraw hbest_nonneg
  have htype_le_norm :
      TypeWeightedRecommendationModel.typeFairness T ρ ≤
        TypeWeightedRecommendationModel.normalizedTypeUtility T ρ 1 := by
    unfold TypeWeightedRecommendationModel.typeFairness
    exact AppliedModelingLib.finiteMin_le
      (TypeWeightedRecommendationModel.normalizedTypeUtility T ρ) 1
  have hclosed_type :
      TypeWeightedRecommendationModel.typeFairness T ρclosed =
        TypeWeightedRecommendationModel.normalizedTypeUtility T ρclosed 1 := by
    dsimp [T, ρclosed, hpivot]
    exact problem6ClosedPolicy_typeFairness_eq_one_of_alpha_le_half_of_pivot_le_reverse
      halpha0 halpha1 halpha_half hpos hdec
      (problem6ClosedNonnegativePivots_of_denominatorBounds
        halpha0 halpha1 hpos cert.denominator_bounds)
      hcenter
  change TypeWeightedRecommendationModel.typeFairness T ρ ≤
    TypeWeightedRecommendationModel.typeFairness T ρclosed
  exact htype_le_norm.trans (hnorm.trans (le_of_eq hclosed_type.symm))

/--
Adjacent-boundary value continuity for Lemma 8: at a boundary where the lower
crossing inequality for pivot `t` is tight and `u = t+1`, the two adjacent
closed-form values agree.  The proof uses the closed-form optimality
certificates on both sides of the boundary.
-/
theorem problem6ClosedValue_eq_of_adjacent_boundary
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {t u : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hnext : u.val = t.val + 1)
    (hboundary :
      problem6PivotGap alpha v t = - (pairShare alpha v t)⁻¹) :
    problem6ClosedValue alpha v t =
      problem6ClosedValue alpha v u := by
  rcases problem6ClosedPivotDenominatorBounds_adjacent_of_boundary
      halpha0 halpha1 hpos hnext hboundary with
    ⟨hbounds_t, hbounds_u⟩
  let cert_t : Problem6ClosedOptimalityCertificate alpha v t :=
    problem6ClosedOptimalityCertificate_of_denominatorBounds
      halpha0 halpha1 hpos hdec hbounds_t
  let cert_u : Problem6ClosedOptimalityCertificate alpha v u :=
    problem6ClosedOptimalityCertificate_of_denominatorBounds
      halpha0 halpha1 hpos hdec hbounds_u
  calc
    problem6ClosedValue alpha v t =
        problem6LPOptimalValue alpha v := by
      exact (problem6LPOptimalValue_eq_closedValue_of_closed_certificate
        halpha0 halpha1 hpos cert_t).symm
    _ = problem6ClosedValue alpha v u :=
      problem6LPOptimalValue_eq_closedValue_of_closed_certificate
        halpha0 halpha1 hpos cert_u

/--
Appendix D, Lemma 4/5 optimal-value bridge: an equalized optimal Problem 6
policy identifies the LP optimum with the Lemma 5 closed value at its active
sparse pivot.
-/
theorem problem6LPOptimalValue_eq_closedValue_of_policyOptimal_equalized_of_two_lt
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 2 n} {ell : ℝ}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hitem_eq :
      ∀ l : Item n,
        pairShare alpha v l * (ρ 0 l).toReal +
          (1 - pairShare alpha v l) * (ρ 1 l).toReal = ell)
    (hopt : Problem6PolicyOptimal alpha v ρ ell)
    (hshared : TypePolicy.SharedItemsBound ρ) :
    problem6LPOptimalValue alpha v =
      problem6ClosedValue alpha v (TypePolicy.lastActiveTypeZero ρ) := by
  exact problem6LPOptimalValue_eq_closedValue_of_closed_certificate
    halpha0 halpha1 hpos
    (problem6ClosedOptimalityCertificate_of_policyOptimal_equalized_of_two_lt
      hn halpha0 halpha1 hpos hdec hitem_eq hopt hshared)

/--
Appendix D, Lemma 4/5 optimal-value bridge for the paper's equality-form
optimal BFS package.
-/
theorem problem6LPOptimalValue_eq_closedValue_of_equalizedBasicOptimal_of_two_lt
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {ρ : TypePolicy 2 n} {ell : ℝ}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (h : Problem6EqualizedBasicOptimal alpha v ρ ell) :
    problem6LPOptimalValue alpha v =
      problem6ClosedValue alpha v (TypePolicy.lastActiveTypeZero ρ) := by
  exact problem6LPOptimalValue_eq_closedValue_of_policyOptimal_equalized_of_two_lt
    hn halpha0 halpha1 hpos hdec h.item_eq h.optimal
    (problem6_sharedItemsBound_of_equalizedBasicOptimal
      halpha0 halpha1 hpos h)

/--
Appendix D, Lemma 11 interval form: if the same pivot `t` has the paper's
closed-form optimality certificate at `α` and `α'`, then the actual Problem 6
LP optimum is monotone on that fixed-pivot interval.
-/
theorem lemma11_problem6LPOptimalValue_mono_of_fixed_pivot_cert
    {n : ℕ} [NeZero n]
    {alpha alpha' : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter : t.val ≤ (reverseItem t).val)
    (cert : Problem6ClosedOptimalityCertificate alpha v t)
    (cert' : Problem6ClosedOptimalityCertificate alpha' v t) :
    problem6LPOptimalValue alpha v ≤ problem6LPOptimalValue alpha' v := by
  rw [problem6LPOptimalValue_eq_closedValue_of_closed_certificate
      halpha0 halpha1 hpos cert,
    problem6LPOptimalValue_eq_closedValue_of_closed_certificate
      halpha0' halpha1' hpos cert']
  exact lemma11_fixedPivotClosedValue_monotone
    halpha0 halpha1 halpha0' halpha1' halpha_le hpos hdec hcenter

/--
Appendix D, Lemma 11 selected-policy fixed-interval form: if two equalized
optimal policies at `α ≤ α'` select the same pivot `t`, and that pivot lies in
the first half, then the actual Problem 6 LP optimum is monotone.  This derives
the closed-form certificates from the Lemma 4/5 active-pivot bridge.
-/
theorem lemma11_problem6LPOptimalValue_mono_of_same_selected_pivot
    {n : ℕ} [NeZero n]
    {alpha alpha' : ℝ} {v : Item n → ℝ}
    {ρ ρ' : TypePolicy 2 n} {ell ell' : ℝ}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hpivot :
      TypePolicy.lastActiveTypeZero ρ =
        TypePolicy.lastActiveTypeZero ρ')
    (hcenter :
      (TypePolicy.lastActiveTypeZero ρ).val ≤
        (reverseItem (TypePolicy.lastActiveTypeZero ρ)).val)
    (hitem_eq :
      ∀ l : Item n,
        pairShare alpha v l * (ρ 0 l).toReal +
          (1 - pairShare alpha v l) * (ρ 1 l).toReal = ell)
    (hitem_eq' :
      ∀ l : Item n,
        pairShare alpha' v l * (ρ' 0 l).toReal +
          (1 - pairShare alpha' v l) * (ρ' 1 l).toReal = ell')
    (hopt : Problem6PolicyOptimal alpha v ρ ell)
    (hopt' : Problem6PolicyOptimal alpha' v ρ' ell')
    (hshared : TypePolicy.SharedItemsBound ρ)
    (hshared' : TypePolicy.SharedItemsBound ρ') :
    problem6LPOptimalValue alpha v ≤ problem6LPOptimalValue alpha' v := by
  let t : Item n := TypePolicy.lastActiveTypeZero ρ
  let t' : Item n := TypePolicy.lastActiveTypeZero ρ'
  have cert :
      Problem6ClosedOptimalityCertificate alpha v t := by
    dsimp [t]
    exact problem6ClosedOptimalityCertificate_of_policyOptimal_equalized_of_two_lt
      hn halpha0 halpha1 hpos hdec hitem_eq hopt hshared
  have cert' :
      Problem6ClosedOptimalityCertificate alpha' v t := by
    have hcert' :
        Problem6ClosedOptimalityCertificate alpha' v t' := by
      dsimp [t']
      exact problem6ClosedOptimalityCertificate_of_policyOptimal_equalized_of_two_lt
        hn halpha0' halpha1' hpos hdec hitem_eq' hopt' hshared'
    simpa [t, t', hpivot] using hcert'
  exact lemma11_problem6LPOptimalValue_mono_of_fixed_pivot_cert
    halpha0 halpha1 halpha0' halpha1' halpha_le
    hpos hdec (by simpa [t] using hcenter) cert cert'

/--
Appendix D, Lemma 11 selected-policy fixed-interval form for the paper's
equality-form optimal BFS package.
-/
theorem lemma11_problem6LPOptimalValue_mono_of_same_selected_equalizedBasicOptimal
    {n : ℕ} [NeZero n]
    {alpha alpha' : ℝ} {v : Item n → ℝ}
    {ρ ρ' : TypePolicy 2 n} {ell ell' : ℝ}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hpivot :
      TypePolicy.lastActiveTypeZero ρ =
        TypePolicy.lastActiveTypeZero ρ')
    (hcenter :
      (TypePolicy.lastActiveTypeZero ρ).val ≤
        (reverseItem (TypePolicy.lastActiveTypeZero ρ)).val)
    (h : Problem6EqualizedBasicOptimal alpha v ρ ell)
    (h' : Problem6EqualizedBasicOptimal alpha' v ρ' ell') :
    problem6LPOptimalValue alpha v ≤ problem6LPOptimalValue alpha' v := by
  exact lemma11_problem6LPOptimalValue_mono_of_same_selected_pivot
    hn halpha0 halpha1 halpha0' halpha1' halpha_le
    hpos hdec hpivot hcenter h.item_eq h'.item_eq
    h.optimal h'.optimal
    (problem6_sharedItemsBound_of_equalizedBasicOptimal
      halpha0 halpha1 hpos h)
    (problem6_sharedItemsBound_of_equalizedBasicOptimal
      halpha0' halpha1' hpos h')

/--
Appendix D, Lemma 11 canonical first-pivot interval form: if the first
closed-form crossing pivot is the same at `α ≤ α'`, and that pivot lies in the
first half, then the actual Problem 6 LP optimum is monotone on this `A(t)`
interval.  This removes the arbitrary selected-BFS family from the fixed-pivot
step by using the canonical Lemma 5 first crossing pivot.
-/
theorem lemma11_problem6LPOptimalValue_mono_of_same_firstClosedPivot
    {n : ℕ} [NeZero n]
    {alpha alpha' : ℝ} {v : Item n → ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hpivot :
      problem6FirstClosedPivot alpha v halpha0 halpha1 hpos =
        problem6FirstClosedPivot alpha' v halpha0' halpha1' hpos)
    (hcenter :
      (problem6FirstClosedPivot alpha v halpha0 halpha1 hpos).val ≤
        (reverseItem
          (problem6FirstClosedPivot alpha v halpha0 halpha1 hpos)).val) :
    problem6LPOptimalValue alpha v ≤ problem6LPOptimalValue alpha' v := by
  let t : Item n := problem6FirstClosedPivot alpha v halpha0 halpha1 hpos
  have cert : Problem6ClosedOptimalityCertificate alpha v t := by
    dsimp [t]
    exact problem6FirstClosedPivot_optimalityCertificate
      halpha0 halpha1 hpos hdec
  have cert' : Problem6ClosedOptimalityCertificate alpha' v t := by
    have cert'_raw :
        Problem6ClosedOptimalityCertificate alpha' v
          (problem6FirstClosedPivot alpha' v halpha0' halpha1' hpos) :=
      problem6FirstClosedPivot_optimalityCertificate
        halpha0' halpha1' hpos hdec
    simpa [t, hpivot] using cert'_raw
  exact lemma11_problem6LPOptimalValue_mono_of_fixed_pivot_cert
    halpha0 halpha1 halpha0' halpha1' halpha_le
    hpos hdec (by simpa [t] using hcenter) cert cert'

/--
Appendix D, Lemma 11 reduced-model form: on a fixed-pivot interval certified by
the paper's closed-form optimality certificates, the reduced optimal item
fairness is monotone in `α`.
-/
theorem lemma11_reducedOptimalItemFairness_mono_of_fixed_pivot_cert
    {n : ℕ} [NeZero n]
    {alpha alpha' : ℝ} {v : Item n → ℝ} {t : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter : t.val ≤ (reverseItem t).val)
    (cert : Problem6ClosedOptimalityCertificate alpha v t)
    (cert' : Problem6ClosedOptimalityCertificate alpha' v t) :
    TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel alpha v) ≤
      TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel alpha' v) := by
  rw [← problem6LPOptimalValue_eq_optimalItemFairness
      alpha v halpha0 halpha1 hpos,
    ← problem6LPOptimalValue_eq_optimalItemFairness
      alpha' v halpha0' halpha1' hpos]
  exact lemma11_problem6LPOptimalValue_mono_of_fixed_pivot_cert
    halpha0 halpha1 halpha0' halpha1' halpha_le
    hpos hdec hcenter cert cert'

/--
Appendix D, Lemma 8 adjacent-boundary stitch for closed-form pivots: if the
left side of a boundary is certified by pivot `t`, the right side is certified
by the adjacent pivot `u = t+1`, and the lower crossing inequality for `t` is
tight at the boundary, then the reduced optimal item fairness is monotone
across the whole left-boundary-right interval.

This is the formal local version of the paper's continuity stitch between two
consecutive `A(t)` intervals.
-/
theorem lemma8_reducedOptimalItemFairness_mono_across_adjacent_closed_boundary
    {n : ℕ} [NeZero n]
    {alphaLeft alphaBoundary alphaRight : ℝ}
    {v : Item n → ℝ} {t u : Item n}
    (halphaLeft0 : 0 < alphaLeft) (halphaLeft1 : alphaLeft < 1)
    (halphaBoundary0 : 0 < alphaBoundary)
    (halphaBoundary1 : alphaBoundary < 1)
    (halphaRight0 : 0 < alphaRight) (halphaRight1 : alphaRight < 1)
    (hleft_le_boundary : alphaLeft ≤ alphaBoundary)
    (hboundary_le_right : alphaBoundary ≤ alphaRight)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter_t : t.val ≤ (reverseItem t).val)
    (hcenter_u : u.val ≤ (reverseItem u).val)
    (hleft_bounds : Problem6ClosedPivotDenominatorBounds alphaLeft v t)
    (hnext : u.val = t.val + 1)
    (hboundary :
      problem6PivotGap alphaBoundary v t =
        - (pairShare alphaBoundary v t)⁻¹)
    (hright_bounds : Problem6ClosedPivotDenominatorBounds alphaRight v u) :
    TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel alphaLeft v) ≤
      TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel alphaRight v) := by
  rcases problem6ClosedPivotDenominatorBounds_adjacent_of_boundary
      halphaBoundary0 halphaBoundary1 hpos hnext hboundary with
    ⟨hboundary_t, hboundary_u⟩
  have hleft_to_boundary :
      TypeWeightedRecommendationModel.optimalItemFairness
          (twoTypeReducedModel alphaLeft v) ≤
        TypeWeightedRecommendationModel.optimalItemFairness
          (twoTypeReducedModel alphaBoundary v) := by
    exact
      lemma11_reducedOptimalItemFairness_mono_of_fixed_pivot_cert
        halphaLeft0 halphaLeft1
        halphaBoundary0 halphaBoundary1
        hleft_le_boundary hpos hdec hcenter_t
        (problem6ClosedOptimalityCertificate_of_denominatorBounds
          halphaLeft0 halphaLeft1 hpos hdec hleft_bounds)
        (problem6ClosedOptimalityCertificate_of_denominatorBounds
          halphaBoundary0 halphaBoundary1 hpos hdec hboundary_t)
  have hboundary_to_right :
      TypeWeightedRecommendationModel.optimalItemFairness
          (twoTypeReducedModel alphaBoundary v) ≤
        TypeWeightedRecommendationModel.optimalItemFairness
          (twoTypeReducedModel alphaRight v) := by
    exact
      lemma11_reducedOptimalItemFairness_mono_of_fixed_pivot_cert
        halphaBoundary0 halphaBoundary1
        halphaRight0 halphaRight1
        hboundary_le_right hpos hdec hcenter_u
        (problem6ClosedOptimalityCertificate_of_denominatorBounds
          halphaBoundary0 halphaBoundary1 hpos hdec hboundary_u)
        (problem6ClosedOptimalityCertificate_of_denominatorBounds
          halphaRight0 halphaRight1 hpos hdec hright_bounds)
  exact hleft_to_boundary.trans hboundary_to_right

/--
Appendix D, Lemma 8 adjacent-boundary stitch for the canonical Lemma 5 first
closed pivot, odd-center case.  Endpoint canonical pivots supply the closed
certificates, while Lemma 10 supplies the first-half pivot-before-mirror side
conditions.
-/
theorem lemma8_reducedOptimalItemFairness_mono_across_adjacent_firstClosedPivot_boundary_center
    {n : ℕ} [NeZero n]
    {alphaLeft alphaBoundary alphaRight : ℝ}
    {v : Item n → ℝ} {c t u : Item n}
    (halphaLeft0 : 0 < alphaLeft) (halphaLeft1 : alphaLeft < 1)
    (halphaBoundary0 : 0 < alphaBoundary)
    (halphaBoundary1 : alphaBoundary < 1)
    (halphaRight0 : 0 < alphaRight) (halphaRight1 : alphaRight < 1)
    (hleft_le_boundary : alphaLeft ≤ alphaBoundary)
    (hboundary_le_right : alphaBoundary ≤ alphaRight)
    (halphaLeft_half : alphaLeft ≤ 1 / 2)
    (halphaRight_half : alphaRight ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter_c : c.val = (reverseItem c).val)
    (hleft_pivot :
      problem6FirstClosedPivot alphaLeft v
        halphaLeft0 halphaLeft1 hpos = t)
    (hright_pivot :
      problem6FirstClosedPivot alphaRight v
        halphaRight0 halphaRight1 hpos = u)
    (hnext : u.val = t.val + 1)
    (hboundary :
      problem6PivotGap alphaBoundary v t =
        - (pairShare alphaBoundary v t)⁻¹) :
    TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel alphaLeft v) ≤
      TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel alphaRight v) := by
  have hcenter_t :
      t.val ≤ (reverseItem t).val := by
    have h :=
      problem6FirstClosedPivot_le_reverse_of_alpha_le_half_center
        halphaLeft0 halphaLeft1 halphaLeft_half hpos hcenter_c
    simpa [← hleft_pivot] using h
  have hcenter_u :
      u.val ≤ (reverseItem u).val := by
    have h :=
      problem6FirstClosedPivot_le_reverse_of_alpha_le_half_center
        halphaRight0 halphaRight1 halphaRight_half hpos hcenter_c
    simpa [← hright_pivot] using h
  exact
    lemma8_reducedOptimalItemFairness_mono_across_adjacent_closed_boundary
      halphaLeft0 halphaLeft1
      halphaBoundary0 halphaBoundary1
      halphaRight0 halphaRight1
      hleft_le_boundary hboundary_le_right
      hpos hdec hcenter_t hcenter_u
      (by
        simpa [hleft_pivot] using
          problem6FirstClosedPivot_denominatorBounds
            (alpha := alphaLeft) (v := v)
            halphaLeft0 halphaLeft1 hpos)
      hnext hboundary
      (by
        simpa [hright_pivot] using
          problem6FirstClosedPivot_denominatorBounds
            (alpha := alphaRight) (v := v)
            halphaRight0 halphaRight1 hpos)

/--
Appendix D, Lemma 8 adjacent-boundary stitch for the canonical Lemma 5 first
closed pivot, even-center case.
-/
theorem lemma8_reducedOptimalItemFairness_mono_across_adjacent_firstClosedPivot_boundary_succ_center
    {n : ℕ} [NeZero n]
    {alphaLeft alphaBoundary alphaRight : ℝ}
    {v : Item n → ℝ} {c t u : Item n}
    (halphaLeft0 : 0 < alphaLeft) (halphaLeft1 : alphaLeft < 1)
    (halphaBoundary0 : 0 < alphaBoundary)
    (halphaBoundary1 : alphaBoundary < 1)
    (halphaRight0 : 0 < alphaRight) (halphaRight1 : alphaRight < 1)
    (hleft_le_boundary : alphaLeft ≤ alphaBoundary)
    (hboundary_le_right : alphaBoundary ≤ alphaRight)
    (halphaLeft_half : alphaLeft ≤ 1 / 2)
    (halphaRight_half : alphaRight ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hsucc : c.val + 1 = (reverseItem c).val)
    (hleft_pivot :
      problem6FirstClosedPivot alphaLeft v
        halphaLeft0 halphaLeft1 hpos = t)
    (hright_pivot :
      problem6FirstClosedPivot alphaRight v
        halphaRight0 halphaRight1 hpos = u)
    (hnext : u.val = t.val + 1)
    (hboundary :
      problem6PivotGap alphaBoundary v t =
        - (pairShare alphaBoundary v t)⁻¹) :
    TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel alphaLeft v) ≤
      TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel alphaRight v) := by
  have hcenter_t :
      t.val ≤ (reverseItem t).val := by
    have h :=
      problem6FirstClosedPivot_le_reverse_of_alpha_le_half_succ_center
        halphaLeft0 halphaLeft1 halphaLeft_half hpos hsucc
    simpa [← hleft_pivot] using h
  have hcenter_u :
      u.val ≤ (reverseItem u).val := by
    have h :=
      problem6FirstClosedPivot_le_reverse_of_alpha_le_half_succ_center
        halphaRight0 halphaRight1 halphaRight_half hpos hsucc
    simpa [← hright_pivot] using h
  exact
    lemma8_reducedOptimalItemFairness_mono_across_adjacent_closed_boundary
      halphaLeft0 halphaLeft1
      halphaBoundary0 halphaBoundary1
      halphaRight0 halphaRight1
      hleft_le_boundary hboundary_le_right
      hpos hdec hcenter_t hcenter_u
      (by
        simpa [hleft_pivot] using
          problem6FirstClosedPivot_denominatorBounds
            (alpha := alphaLeft) (v := v)
            halphaLeft0 halphaLeft1 hpos)
      hnext hboundary
      (by
        simpa [hright_pivot] using
          problem6FirstClosedPivot_denominatorBounds
            (alpha := alphaRight) (v := v)
            halphaRight0 halphaRight1 hpos)

/--
Appendix D, Lemma 8 finite adjacent-boundary stitch for closed-form pivots:
if each consecutive pair of certified pivots is separated by a tight
`t`/`t+1` boundary, then reduced optimal item fairness is monotone along the
whole boundary sequence.
-/
theorem lemma8_reducedOptimalItemFairness_mono_of_adjacent_closedBoundary_chain
    {n : ℕ} [NeZero n]
    {v : Item n → ℝ} (r : ℕ)
    (alphaSeq boundarySeq : ℕ → ℝ)
    (pivotSeq : ℕ → Item n)
    (halpha0 : ∀ i, i ≤ r → 0 < alphaSeq i)
    (halpha1 : ∀ i, i ≤ r → alphaSeq i < 1)
    (hboundary0 : ∀ i, i < r → 0 < boundarySeq i)
    (hboundary1 : ∀ i, i < r → boundarySeq i < 1)
    (hleft_le_boundary :
      ∀ i, i < r → alphaSeq i ≤ boundarySeq i)
    (hboundary_le_right :
      ∀ i, i < r → boundarySeq i ≤ alphaSeq (i + 1))
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hbounds :
      ∀ i, ∀ hi : i ≤ r,
        Problem6ClosedPivotDenominatorBounds (alphaSeq i) v (pivotSeq i))
    (hcenter :
      ∀ i, ∀ hi : i ≤ r,
        (pivotSeq i).val ≤ (reverseItem (pivotSeq i)).val)
    (hnext :
      ∀ i, i < r → (pivotSeq (i + 1)).val = (pivotSeq i).val + 1)
    (hboundary :
      ∀ i, ∀ hi : i < r,
        problem6PivotGap (boundarySeq i) v (pivotSeq i) =
          - (pairShare (boundarySeq i) v (pivotSeq i))⁻¹) :
    TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel (alphaSeq 0) v) ≤
      TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel (alphaSeq r) v) := by
  induction r with
  | zero =>
      exact le_rfl
  | succ r ih =>
      have hprev :
          TypeWeightedRecommendationModel.optimalItemFairness
              (twoTypeReducedModel (alphaSeq 0) v) ≤
            TypeWeightedRecommendationModel.optimalItemFairness
              (twoTypeReducedModel (alphaSeq r) v) := by
        exact ih
          (fun i hi => halpha0 i (Nat.le_trans hi (Nat.le_succ r)))
          (fun i hi => halpha1 i (Nat.le_trans hi (Nat.le_succ r)))
          (fun i hi => hboundary0 i (Nat.lt_trans hi (Nat.lt_succ_self r)))
          (fun i hi => hboundary1 i (Nat.lt_trans hi (Nat.lt_succ_self r)))
          (fun i hi =>
            hleft_le_boundary i (Nat.lt_trans hi (Nat.lt_succ_self r)))
          (fun i hi =>
            hboundary_le_right i (Nat.lt_trans hi (Nat.lt_succ_self r)))
          (fun i hi => hbounds i (Nat.le_trans hi (Nat.le_succ r)))
          (fun i hi => hcenter i (Nat.le_trans hi (Nat.le_succ r)))
          (fun i hi => hnext i (Nat.lt_trans hi (Nat.lt_succ_self r)))
          (fun i hi => hboundary i (Nat.lt_trans hi (Nat.lt_succ_self r)))
      have hlast :
          TypeWeightedRecommendationModel.optimalItemFairness
              (twoTypeReducedModel (alphaSeq r) v) ≤
            TypeWeightedRecommendationModel.optimalItemFairness
              (twoTypeReducedModel (alphaSeq (r + 1)) v) := by
        exact
          lemma8_reducedOptimalItemFairness_mono_across_adjacent_closed_boundary
            (halpha0 r (Nat.le_succ r))
            (halpha1 r (Nat.le_succ r))
            (hboundary0 r (Nat.lt_succ_self r))
            (hboundary1 r (Nat.lt_succ_self r))
            (halpha0 (r + 1) le_rfl)
            (halpha1 (r + 1) le_rfl)
            (hleft_le_boundary r (Nat.lt_succ_self r))
            (hboundary_le_right r (Nat.lt_succ_self r))
            hpos hdec
            (hcenter r (Nat.le_succ r))
            (hcenter (r + 1) le_rfl)
            (hbounds r (Nat.le_succ r))
            (hnext r (Nat.lt_succ_self r))
            (hboundary r (Nat.lt_succ_self r))
            (hbounds (r + 1) le_rfl)
      exact hprev.trans hlast

/--
Appendix D, Lemma 8 finite adjacent-boundary stitch for canonical first
closed pivots, odd-center case.  Lemma 10 supplies the first-half side
condition at every endpoint of the boundary sequence.
-/
theorem lemma8_reducedOptimalItemFairness_mono_firstHalf_center_adjacentBoundary_chain
    {n : ℕ} [NeZero n]
    {v : Item n → ℝ} {c : Item n}
    (r : ℕ)
    (alphaSeq boundarySeq : ℕ → ℝ)
    (pivotSeq : ℕ → Item n)
    (halpha0 : ∀ i, i ≤ r → 0 < alphaSeq i)
    (halpha1 : ∀ i, i ≤ r → alphaSeq i < 1)
    (halpha_half : ∀ i, i ≤ r → alphaSeq i ≤ 1 / 2)
    (hboundary0 : ∀ i, i < r → 0 < boundarySeq i)
    (hboundary1 : ∀ i, i < r → boundarySeq i < 1)
    (hleft_le_boundary :
      ∀ i, i < r → alphaSeq i ≤ boundarySeq i)
    (hboundary_le_right :
      ∀ i, i < r → boundarySeq i ≤ alphaSeq (i + 1))
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter_c : c.val = (reverseItem c).val)
    (hpivot_def :
      ∀ i, ∀ hi : i ≤ r,
        problem6FirstClosedPivot (alphaSeq i) v
          (halpha0 i hi) (halpha1 i hi) hpos = pivotSeq i)
    (hnext :
      ∀ i, i < r → (pivotSeq (i + 1)).val = (pivotSeq i).val + 1)
    (hboundary :
      ∀ i, ∀ hi : i < r,
        problem6PivotGap (boundarySeq i) v (pivotSeq i) =
          - (pairShare (boundarySeq i) v (pivotSeq i))⁻¹) :
    TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel (alphaSeq 0) v) ≤
      TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel (alphaSeq r) v) := by
  exact
    lemma8_reducedOptimalItemFairness_mono_of_adjacent_closedBoundary_chain
      r alphaSeq boundarySeq pivotSeq halpha0 halpha1
      hboundary0 hboundary1 hleft_le_boundary hboundary_le_right
      hpos hdec
      (fun i hi => by
        simpa [← hpivot_def i hi] using
          problem6FirstClosedPivot_denominatorBounds
            (alpha := alphaSeq i) (v := v)
            (halpha0 i hi) (halpha1 i hi) hpos)
      (fun i hi => by
        have h :=
          problem6FirstClosedPivot_le_reverse_of_alpha_le_half_center
            (halpha0 i hi) (halpha1 i hi) (halpha_half i hi)
            hpos hcenter_c
        simpa [hpivot_def i hi] using h)
      hnext hboundary

/--
Appendix D, Lemma 8 finite adjacent-boundary stitch for canonical first
closed pivots, even-center case.
-/
theorem lemma8_reducedOptimalItemFairness_mono_firstHalf_succ_center_adjacentBoundary_chain
    {n : ℕ} [NeZero n]
    {v : Item n → ℝ} {c : Item n}
    (r : ℕ)
    (alphaSeq boundarySeq : ℕ → ℝ)
    (pivotSeq : ℕ → Item n)
    (halpha0 : ∀ i, i ≤ r → 0 < alphaSeq i)
    (halpha1 : ∀ i, i ≤ r → alphaSeq i < 1)
    (halpha_half : ∀ i, i ≤ r → alphaSeq i ≤ 1 / 2)
    (hboundary0 : ∀ i, i < r → 0 < boundarySeq i)
    (hboundary1 : ∀ i, i < r → boundarySeq i < 1)
    (hleft_le_boundary :
      ∀ i, i < r → alphaSeq i ≤ boundarySeq i)
    (hboundary_le_right :
      ∀ i, i < r → boundarySeq i ≤ alphaSeq (i + 1))
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hsucc : c.val + 1 = (reverseItem c).val)
    (hpivot_def :
      ∀ i, ∀ hi : i ≤ r,
        problem6FirstClosedPivot (alphaSeq i) v
          (halpha0 i hi) (halpha1 i hi) hpos = pivotSeq i)
    (hnext :
      ∀ i, i < r → (pivotSeq (i + 1)).val = (pivotSeq i).val + 1)
    (hboundary :
      ∀ i, ∀ hi : i < r,
        problem6PivotGap (boundarySeq i) v (pivotSeq i) =
          - (pairShare (boundarySeq i) v (pivotSeq i))⁻¹) :
    TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel (alphaSeq 0) v) ≤
      TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel (alphaSeq r) v) := by
  exact
    lemma8_reducedOptimalItemFairness_mono_of_adjacent_closedBoundary_chain
      r alphaSeq boundarySeq pivotSeq halpha0 halpha1
      hboundary0 hboundary1 hleft_le_boundary hboundary_le_right
      hpos hdec
      (fun i hi => by
        simpa [← hpivot_def i hi] using
          problem6FirstClosedPivot_denominatorBounds
            (alpha := alphaSeq i) (v := v)
            (halpha0 i hi) (halpha1 i hi) hpos)
      (fun i hi => by
        have h :=
          problem6FirstClosedPivot_le_reverse_of_alpha_le_half_succ_center
            (halpha0 i hi) (halpha1 i hi) (halpha_half i hi)
            hpos hsucc
        simpa [hpivot_def i hi] using h)
      hnext hboundary

/--
Appendix D, Lemma 8 adjacent canonical-pivot change, odd-center case: if the
canonical first closed pivot moves from `t` to the adjacent pivot `t+1`, the
boundary point exists by IVT and the local boundary stitch proves reduced
item-fairness monotonicity across the whole change.
-/
theorem lemma8_reducedOptimalItemFairness_mono_across_adjacent_firstClosedPivot_change_center
    {n : ℕ} [NeZero n]
    {alphaLeft alphaRight : ℝ}
    {v : Item n → ℝ} {c t u : Item n}
    (halphaLeft0 : 0 < alphaLeft) (halphaLeft1 : alphaLeft < 1)
    (halphaRight0 : 0 < alphaRight) (halphaRight1 : alphaRight < 1)
    (hleft_le_right : alphaLeft ≤ alphaRight)
    (halphaLeft_half : alphaLeft ≤ 1 / 2)
    (halphaRight_half : alphaRight ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter_c : c.val = (reverseItem c).val)
    (hleft_pivot :
      problem6FirstClosedPivot alphaLeft v
        halphaLeft0 halphaLeft1 hpos = t)
    (hright_pivot :
      problem6FirstClosedPivot alphaRight v
        halphaRight0 halphaRight1 hpos = u)
    (hnext : u.val = t.val + 1) :
    TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel alphaLeft v) ≤
      TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel alphaRight v) := by
  rcases problem6FirstClosedPivot_adjacentBoundary_exists
      halphaLeft0 halphaLeft1 halphaRight0 halphaRight1
      hleft_le_right hpos hleft_pivot hright_pivot hnext with
    ⟨alphaBoundary, hleft_le_boundary, hboundary_le_right,
      halphaBoundary0, halphaBoundary1, hboundary⟩
  exact
    lemma8_reducedOptimalItemFairness_mono_across_adjacent_firstClosedPivot_boundary_center
      halphaLeft0 halphaLeft1
      halphaBoundary0 halphaBoundary1
      halphaRight0 halphaRight1
      hleft_le_boundary hboundary_le_right
      halphaLeft_half halphaRight_half
      hpos hdec hcenter_c hleft_pivot hright_pivot
      hnext hboundary

/--
Appendix D, Lemma 8 adjacent canonical-pivot change, even-center case.
-/
theorem lemma8_reducedOptimalItemFairness_mono_across_adjacent_firstClosedPivot_change_succ_center
    {n : ℕ} [NeZero n]
    {alphaLeft alphaRight : ℝ}
    {v : Item n → ℝ} {c t u : Item n}
    (halphaLeft0 : 0 < alphaLeft) (halphaLeft1 : alphaLeft < 1)
    (halphaRight0 : 0 < alphaRight) (halphaRight1 : alphaRight < 1)
    (hleft_le_right : alphaLeft ≤ alphaRight)
    (halphaLeft_half : alphaLeft ≤ 1 / 2)
    (halphaRight_half : alphaRight ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hsucc : c.val + 1 = (reverseItem c).val)
    (hleft_pivot :
      problem6FirstClosedPivot alphaLeft v
        halphaLeft0 halphaLeft1 hpos = t)
    (hright_pivot :
      problem6FirstClosedPivot alphaRight v
        halphaRight0 halphaRight1 hpos = u)
    (hnext : u.val = t.val + 1) :
    TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel alphaLeft v) ≤
      TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel alphaRight v) := by
  rcases problem6FirstClosedPivot_adjacentBoundary_exists
      halphaLeft0 halphaLeft1 halphaRight0 halphaRight1
      hleft_le_right hpos hleft_pivot hright_pivot hnext with
    ⟨alphaBoundary, hleft_le_boundary, hboundary_le_right,
      halphaBoundary0, halphaBoundary1, hboundary⟩
  exact
    lemma8_reducedOptimalItemFairness_mono_across_adjacent_firstClosedPivot_boundary_succ_center
      halphaLeft0 halphaLeft1
      halphaBoundary0 halphaBoundary1
      halphaRight0 halphaRight1
      hleft_le_boundary hboundary_le_right
      halphaLeft_half halphaRight_half
      hpos hdec hsucc hleft_pivot hright_pivot
      hnext hboundary

/--
Appendix D, Lemma 8 finite adjacent canonical-pivot change chain,
odd-center case.
-/
theorem lemma8_reducedOptimalItemFairness_mono_firstHalf_center_adjacentPivotChange_chain
    {n : ℕ} [NeZero n]
    {v : Item n → ℝ} {c : Item n}
    (r : ℕ)
    (alphaSeq : ℕ → ℝ)
    (pivotSeq : ℕ → Item n)
    (halpha0 : ∀ i, i ≤ r → 0 < alphaSeq i)
    (halpha1 : ∀ i, i ≤ r → alphaSeq i < 1)
    (halpha_half : ∀ i, i ≤ r → alphaSeq i ≤ 1 / 2)
    (hstep : ∀ i, i < r → alphaSeq i ≤ alphaSeq (i + 1))
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter_c : c.val = (reverseItem c).val)
    (hpivot_def :
      ∀ i, ∀ hi : i ≤ r,
        problem6FirstClosedPivot (alphaSeq i) v
          (halpha0 i hi) (halpha1 i hi) hpos = pivotSeq i)
    (hnext :
      ∀ i, i < r → (pivotSeq (i + 1)).val = (pivotSeq i).val + 1) :
    TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel (alphaSeq 0) v) ≤
      TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel (alphaSeq r) v) := by
  induction r with
  | zero =>
      exact le_rfl
  | succ r ih =>
      have hprev :
          TypeWeightedRecommendationModel.optimalItemFairness
              (twoTypeReducedModel (alphaSeq 0) v) ≤
            TypeWeightedRecommendationModel.optimalItemFairness
              (twoTypeReducedModel (alphaSeq r) v) := by
        exact ih
          (fun i hi => halpha0 i (Nat.le_trans hi (Nat.le_succ r)))
          (fun i hi => halpha1 i (Nat.le_trans hi (Nat.le_succ r)))
          (fun i hi => halpha_half i (Nat.le_trans hi (Nat.le_succ r)))
          (fun i hi => hstep i (Nat.lt_trans hi (Nat.lt_succ_self r)))
          (fun i hi => hpivot_def i (Nat.le_trans hi (Nat.le_succ r)))
          (fun i hi => hnext i (Nat.lt_trans hi (Nat.lt_succ_self r)))
      have hlast :
          TypeWeightedRecommendationModel.optimalItemFairness
              (twoTypeReducedModel (alphaSeq r) v) ≤
            TypeWeightedRecommendationModel.optimalItemFairness
              (twoTypeReducedModel (alphaSeq (r + 1)) v) := by
        exact
          lemma8_reducedOptimalItemFairness_mono_across_adjacent_firstClosedPivot_change_center
            (halpha0 r (Nat.le_succ r))
            (halpha1 r (Nat.le_succ r))
            (halpha0 (r + 1) le_rfl)
            (halpha1 (r + 1) le_rfl)
            (hstep r (Nat.lt_succ_self r))
            (halpha_half r (Nat.le_succ r))
            (halpha_half (r + 1) le_rfl)
            hpos hdec hcenter_c
            (hpivot_def r (Nat.le_succ r))
            (hpivot_def (r + 1) le_rfl)
            (hnext r (Nat.lt_succ_self r))
      exact hprev.trans hlast

/--
Appendix D, Lemma 8 finite adjacent canonical-pivot change chain,
even-center case.
-/
theorem lemma8_reducedOptimalItemFairness_mono_firstHalf_succ_center_adjacentPivotChange_chain
    {n : ℕ} [NeZero n]
    {v : Item n → ℝ} {c : Item n}
    (r : ℕ)
    (alphaSeq : ℕ → ℝ)
    (pivotSeq : ℕ → Item n)
    (halpha0 : ∀ i, i ≤ r → 0 < alphaSeq i)
    (halpha1 : ∀ i, i ≤ r → alphaSeq i < 1)
    (halpha_half : ∀ i, i ≤ r → alphaSeq i ≤ 1 / 2)
    (hstep : ∀ i, i < r → alphaSeq i ≤ alphaSeq (i + 1))
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hsucc : c.val + 1 = (reverseItem c).val)
    (hpivot_def :
      ∀ i, ∀ hi : i ≤ r,
        problem6FirstClosedPivot (alphaSeq i) v
          (halpha0 i hi) (halpha1 i hi) hpos = pivotSeq i)
    (hnext :
      ∀ i, i < r → (pivotSeq (i + 1)).val = (pivotSeq i).val + 1) :
    TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel (alphaSeq 0) v) ≤
      TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel (alphaSeq r) v) := by
  induction r with
  | zero =>
      exact le_rfl
  | succ r ih =>
      have hprev :
          TypeWeightedRecommendationModel.optimalItemFairness
              (twoTypeReducedModel (alphaSeq 0) v) ≤
            TypeWeightedRecommendationModel.optimalItemFairness
              (twoTypeReducedModel (alphaSeq r) v) := by
        exact ih
          (fun i hi => halpha0 i (Nat.le_trans hi (Nat.le_succ r)))
          (fun i hi => halpha1 i (Nat.le_trans hi (Nat.le_succ r)))
          (fun i hi => halpha_half i (Nat.le_trans hi (Nat.le_succ r)))
          (fun i hi => hstep i (Nat.lt_trans hi (Nat.lt_succ_self r)))
          (fun i hi => hpivot_def i (Nat.le_trans hi (Nat.le_succ r)))
          (fun i hi => hnext i (Nat.lt_trans hi (Nat.lt_succ_self r)))
      have hlast :
          TypeWeightedRecommendationModel.optimalItemFairness
              (twoTypeReducedModel (alphaSeq r) v) ≤
            TypeWeightedRecommendationModel.optimalItemFairness
              (twoTypeReducedModel (alphaSeq (r + 1)) v) := by
        exact
          lemma8_reducedOptimalItemFairness_mono_across_adjacent_firstClosedPivot_change_succ_center
            (halpha0 r (Nat.le_succ r))
            (halpha1 r (Nat.le_succ r))
            (halpha0 (r + 1) le_rfl)
            (halpha1 (r + 1) le_rfl)
            (hstep r (Nat.lt_succ_self r))
            (halpha_half r (Nat.le_succ r))
            (halpha_half (r + 1) le_rfl)
            hpos hdec hsucc
            (hpivot_def r (Nat.le_succ r))
            (hpivot_def (r + 1) le_rfl)
            (hnext r (Nat.lt_succ_self r))
      exact hprev.trans hlast

/--
Appendix D, Lemma 11 reduced-model selected-policy form: the reduced optimal
item fairness is monotone on a same-selected-pivot interval.
-/
theorem lemma11_reducedOptimalItemFairness_mono_of_same_selected_pivot
    {n : ℕ} [NeZero n]
    {alpha alpha' : ℝ} {v : Item n → ℝ}
    {ρ ρ' : TypePolicy 2 n} {ell ell' : ℝ}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hpivot :
      TypePolicy.lastActiveTypeZero ρ =
        TypePolicy.lastActiveTypeZero ρ')
    (hcenter :
      (TypePolicy.lastActiveTypeZero ρ).val ≤
        (reverseItem (TypePolicy.lastActiveTypeZero ρ)).val)
    (hitem_eq :
      ∀ l : Item n,
        pairShare alpha v l * (ρ 0 l).toReal +
          (1 - pairShare alpha v l) * (ρ 1 l).toReal = ell)
    (hitem_eq' :
      ∀ l : Item n,
        pairShare alpha' v l * (ρ' 0 l).toReal +
          (1 - pairShare alpha' v l) * (ρ' 1 l).toReal = ell')
    (hopt : Problem6PolicyOptimal alpha v ρ ell)
    (hopt' : Problem6PolicyOptimal alpha' v ρ' ell')
    (hshared : TypePolicy.SharedItemsBound ρ)
    (hshared' : TypePolicy.SharedItemsBound ρ') :
    TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel alpha v) ≤
      TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel alpha' v) := by
  rw [← problem6LPOptimalValue_eq_optimalItemFairness
      alpha v halpha0 halpha1 hpos,
    ← problem6LPOptimalValue_eq_optimalItemFairness
      alpha' v halpha0' halpha1' hpos]
  exact lemma11_problem6LPOptimalValue_mono_of_same_selected_pivot
    hn halpha0 halpha1 halpha0' halpha1' halpha_le
    hpos hdec hpivot hcenter hitem_eq hitem_eq'
    hopt hopt' hshared hshared'

/--
Appendix D, Lemma 11 reduced-model selected-policy form for the paper's
equality-form optimal BFS package.
-/
theorem lemma11_reducedOptimalItemFairness_mono_of_same_selected_equalizedBasicOptimal
    {n : ℕ} [NeZero n]
    {alpha alpha' : ℝ} {v : Item n → ℝ}
    {ρ ρ' : TypePolicy 2 n} {ell ell' : ℝ}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hpivot :
      TypePolicy.lastActiveTypeZero ρ =
        TypePolicy.lastActiveTypeZero ρ')
    (hcenter :
      (TypePolicy.lastActiveTypeZero ρ).val ≤
        (reverseItem (TypePolicy.lastActiveTypeZero ρ)).val)
    (h : Problem6EqualizedBasicOptimal alpha v ρ ell)
    (h' : Problem6EqualizedBasicOptimal alpha' v ρ' ell') :
    TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel alpha v) ≤
      TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel alpha' v) := by
  rw [← problem6LPOptimalValue_eq_optimalItemFairness
      alpha v halpha0 halpha1 hpos,
    ← problem6LPOptimalValue_eq_optimalItemFairness
      alpha' v halpha0' halpha1' hpos]
  exact lemma11_problem6LPOptimalValue_mono_of_same_selected_equalizedBasicOptimal
    hn halpha0 halpha1 halpha0' halpha1' halpha_le
    hpos hdec hpivot hcenter h h'

/--
Appendix D, Lemma 11 canonical first-pivot reduced-model form: on an `A(t)`
interval where the canonical Lemma 5 first pivot stays fixed in the first half,
the reduced optimal item-fairness value is monotone.
-/
theorem lemma11_reducedOptimalItemFairness_mono_of_same_firstClosedPivot
    {n : ℕ} [NeZero n]
    {alpha alpha' : ℝ} {v : Item n → ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hpivot :
      problem6FirstClosedPivot alpha v halpha0 halpha1 hpos =
        problem6FirstClosedPivot alpha' v halpha0' halpha1' hpos)
    (hcenter :
      (problem6FirstClosedPivot alpha v halpha0 halpha1 hpos).val ≤
        (reverseItem
          (problem6FirstClosedPivot alpha v halpha0 halpha1 hpos)).val) :
    TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel alpha v) ≤
      TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel alpha' v) := by
  rw [← problem6LPOptimalValue_eq_optimalItemFairness
      alpha v halpha0 halpha1 hpos,
    ← problem6LPOptimalValue_eq_optimalItemFairness
      alpha' v halpha0' halpha1' hpos]
  exact lemma11_problem6LPOptimalValue_mono_of_same_firstClosedPivot
    halpha0 halpha1 halpha0' halpha1' halpha_le
    hpos hdec hpivot hcenter

/--
Appendix D, Lemma 8 global canonical first-pivot stitch, odd-center case:
for any two first-half parameters `α ≤ α'`, endpoint canonical first pivots
can be connected by the no-skip adjacent-pivot construction, so reduced
optimal item fairness is monotone.
-/
theorem lemma8_reducedOptimalItemFairness_mono_firstHalf_center_of_firstClosedPivot_endpoints
    {n : ℕ} [NeZero n]
    {alphaLeft alphaRight : ℝ} {v : Item n → ℝ} {c t u : Item n}
    (halphaLeft0 : 0 < alphaLeft) (halphaLeft1 : alphaLeft < 1)
    (halphaRight0 : 0 < alphaRight) (halphaRight1 : alphaRight < 1)
    (hleft_le_right : alphaLeft ≤ alphaRight)
    (halphaLeft_half : alphaLeft ≤ 1 / 2)
    (halphaRight_half : alphaRight ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter_c : c.val = (reverseItem c).val)
    (hleft_pivot :
      problem6FirstClosedPivot alphaLeft v
        halphaLeft0 halphaLeft1 hpos = t)
    (hright_pivot :
      problem6FirstClosedPivot alphaRight v
        halphaRight0 halphaRight1 hpos = u) :
    TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel alphaLeft v) ≤
      TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel alphaRight v) := by
  have htu : t.val ≤ u.val := by
    have h :=
      problem6FirstClosedPivot_mono_alpha
        halphaLeft0 halphaLeft1 halphaRight0 halphaRight1
        hleft_le_right hpos
    simpa [hleft_pivot, hright_pivot] using h
  generalize hgap_eq : u.val - t.val = gap
  revert alphaLeft alphaRight t u
  induction gap using Nat.strong_induction_on with
  | h gap ih =>
      intro alphaLeft alphaRight t u
        halphaLeft0 halphaLeft1 halphaRight0 halphaRight1
        hleft_le_right halphaLeft_half halphaRight_half
        hleft_pivot hright_pivot htu hgap_eq
      by_cases hsame_val : t.val = u.val
      · have htu_eq : t = u := Fin.ext hsame_val
        have hpivot_eq :
            problem6FirstClosedPivot alphaLeft v
                halphaLeft0 halphaLeft1 hpos =
              problem6FirstClosedPivot alphaRight v
                halphaRight0 halphaRight1 hpos := by
          rw [hleft_pivot, hright_pivot, htu_eq]
        have hcenter_t :
            (problem6FirstClosedPivot alphaLeft v
                halphaLeft0 halphaLeft1 hpos).val ≤
              (reverseItem
                (problem6FirstClosedPivot alphaLeft v
                  halphaLeft0 halphaLeft1 hpos)).val :=
          problem6FirstClosedPivot_le_reverse_of_alpha_le_half_center
            halphaLeft0 halphaLeft1 halphaLeft_half hpos hcenter_c
        exact
          lemma11_reducedOptimalItemFairness_mono_of_same_firstClosedPivot
            halphaLeft0 halphaLeft1 halphaRight0 halphaRight1
            hleft_le_right hpos hdec hpivot_eq hcenter_t
      · have ht_lt_u : t.val < u.val := lt_of_le_of_ne htu hsame_val
        by_cases hadj : u.val = t.val + 1
        · exact
            lemma8_reducedOptimalItemFairness_mono_across_adjacent_firstClosedPivot_change_center
              halphaLeft0 halphaLeft1 halphaRight0 halphaRight1
              hleft_le_right halphaLeft_half halphaRight_half
              hpos hdec hcenter_c hleft_pivot hright_pivot hadj
        · have hskip : t.val + 1 < u.val := by omega
          rcases problem6FirstClosedPivot_successor_exists_of_pivot_jump
              halphaLeft0 halphaLeft1 halphaRight0 halphaRight1
              hleft_le_right hpos hleft_pivot hright_pivot hskip with
            ⟨alphaMid, halphaMid0, halphaMid1, s,
              hleft_le_mid, hmid_le_right, hs_val, hmid_pivot⟩
          have halphaMid_half : alphaMid ≤ 1 / 2 :=
            hmid_le_right.trans halphaRight_half
          have hleft_mid :
              TypeWeightedRecommendationModel.optimalItemFairness
                  (twoTypeReducedModel alphaLeft v) ≤
                TypeWeightedRecommendationModel.optimalItemFairness
                  (twoTypeReducedModel alphaMid v) := by
            exact
              lemma8_reducedOptimalItemFairness_mono_across_adjacent_firstClosedPivot_change_center
                halphaLeft0 halphaLeft1 halphaMid0 halphaMid1
                hleft_le_mid halphaLeft_half halphaMid_half
                hpos hdec hcenter_c hleft_pivot hmid_pivot hs_val
          have hs_le_u : s.val ≤ u.val := by
            rw [hs_val]
            exact le_of_lt hskip
          have hsmaller : u.val - s.val < gap := by
            rw [← hgap_eq, hs_val]
            omega
          have hmid_right :
              TypeWeightedRecommendationModel.optimalItemFairness
                  (twoTypeReducedModel alphaMid v) ≤
                TypeWeightedRecommendationModel.optimalItemFairness
                  (twoTypeReducedModel alphaRight v) := by
            exact ih (u.val - s.val) hsmaller
              halphaMid0 halphaMid1 halphaRight0 halphaRight1
              hmid_le_right halphaMid_half halphaRight_half
              hmid_pivot hright_pivot hs_le_u rfl
          exact hleft_mid.trans hmid_right

/--
Appendix D, Lemma 8 global canonical first-pivot stitch, even-center case:
the same no-skip adjacent-pivot construction proves first-half monotonicity
when the two middle items are adjacent.
-/
theorem lemma8_reducedOptimalItemFairness_mono_firstHalf_succ_center_of_firstClosedPivot_endpoints
    {n : ℕ} [NeZero n]
    {alphaLeft alphaRight : ℝ} {v : Item n → ℝ} {c t u : Item n}
    (halphaLeft0 : 0 < alphaLeft) (halphaLeft1 : alphaLeft < 1)
    (halphaRight0 : 0 < alphaRight) (halphaRight1 : alphaRight < 1)
    (hleft_le_right : alphaLeft ≤ alphaRight)
    (halphaLeft_half : alphaLeft ≤ 1 / 2)
    (halphaRight_half : alphaRight ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hsucc : c.val + 1 = (reverseItem c).val)
    (hleft_pivot :
      problem6FirstClosedPivot alphaLeft v
        halphaLeft0 halphaLeft1 hpos = t)
    (hright_pivot :
      problem6FirstClosedPivot alphaRight v
        halphaRight0 halphaRight1 hpos = u) :
    TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel alphaLeft v) ≤
      TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel alphaRight v) := by
  have htu : t.val ≤ u.val := by
    have h :=
      problem6FirstClosedPivot_mono_alpha
        halphaLeft0 halphaLeft1 halphaRight0 halphaRight1
        hleft_le_right hpos
    simpa [hleft_pivot, hright_pivot] using h
  generalize hgap_eq : u.val - t.val = gap
  revert alphaLeft alphaRight t u
  induction gap using Nat.strong_induction_on with
  | h gap ih =>
      intro alphaLeft alphaRight t u
        halphaLeft0 halphaLeft1 halphaRight0 halphaRight1
        hleft_le_right halphaLeft_half halphaRight_half
        hleft_pivot hright_pivot htu hgap_eq
      by_cases hsame_val : t.val = u.val
      · have htu_eq : t = u := Fin.ext hsame_val
        have hpivot_eq :
            problem6FirstClosedPivot alphaLeft v
                halphaLeft0 halphaLeft1 hpos =
              problem6FirstClosedPivot alphaRight v
                halphaRight0 halphaRight1 hpos := by
          rw [hleft_pivot, hright_pivot, htu_eq]
        have hcenter_t :
            (problem6FirstClosedPivot alphaLeft v
                halphaLeft0 halphaLeft1 hpos).val ≤
              (reverseItem
                (problem6FirstClosedPivot alphaLeft v
                  halphaLeft0 halphaLeft1 hpos)).val :=
          problem6FirstClosedPivot_le_reverse_of_alpha_le_half_succ_center
            halphaLeft0 halphaLeft1 halphaLeft_half hpos hsucc
        exact
          lemma11_reducedOptimalItemFairness_mono_of_same_firstClosedPivot
            halphaLeft0 halphaLeft1 halphaRight0 halphaRight1
            hleft_le_right hpos hdec hpivot_eq hcenter_t
      · have ht_lt_u : t.val < u.val := lt_of_le_of_ne htu hsame_val
        by_cases hadj : u.val = t.val + 1
        · exact
            lemma8_reducedOptimalItemFairness_mono_across_adjacent_firstClosedPivot_change_succ_center
              halphaLeft0 halphaLeft1 halphaRight0 halphaRight1
              hleft_le_right halphaLeft_half halphaRight_half
              hpos hdec hsucc hleft_pivot hright_pivot hadj
        · have hskip : t.val + 1 < u.val := by omega
          rcases problem6FirstClosedPivot_successor_exists_of_pivot_jump
              halphaLeft0 halphaLeft1 halphaRight0 halphaRight1
              hleft_le_right hpos hleft_pivot hright_pivot hskip with
            ⟨alphaMid, halphaMid0, halphaMid1, s,
              hleft_le_mid, hmid_le_right, hs_val, hmid_pivot⟩
          have halphaMid_half : alphaMid ≤ 1 / 2 :=
            hmid_le_right.trans halphaRight_half
          have hleft_mid :
              TypeWeightedRecommendationModel.optimalItemFairness
                  (twoTypeReducedModel alphaLeft v) ≤
                TypeWeightedRecommendationModel.optimalItemFairness
                  (twoTypeReducedModel alphaMid v) := by
            exact
              lemma8_reducedOptimalItemFairness_mono_across_adjacent_firstClosedPivot_change_succ_center
                halphaLeft0 halphaLeft1 halphaMid0 halphaMid1
                hleft_le_mid halphaLeft_half halphaMid_half
                hpos hdec hsucc hleft_pivot hmid_pivot hs_val
          have hs_le_u : s.val ≤ u.val := by
            rw [hs_val]
            exact le_of_lt hskip
          have hsmaller : u.val - s.val < gap := by
            rw [← hgap_eq, hs_val]
            omega
          have hmid_right :
              TypeWeightedRecommendationModel.optimalItemFairness
                  (twoTypeReducedModel alphaMid v) ≤
                TypeWeightedRecommendationModel.optimalItemFairness
                  (twoTypeReducedModel alphaRight v) := by
            exact ih (u.val - s.val) hsmaller
              halphaMid0 halphaMid1 halphaRight0 halphaRight1
              hmid_le_right halphaMid_half halphaRight_half
              hmid_pivot hright_pivot hs_le_u rfl
          exact hleft_mid.trans hmid_right

/--
Appendix D, Lemma 8 in paper-style endpoint-free form, odd-center case:
on the first half of the parameter range, reduced optimal item fairness is
monotone in `α`.
-/
theorem lemma8_reducedOptimalItemFairness_mono_firstHalf_center_of_alpha_le
    {n : ℕ} [NeZero n]
    {alpha alpha' : ℝ} {v : Item n → ℝ} {c : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (halpha_half : alpha ≤ 1 / 2)
    (halpha_half' : alpha' ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter_c : c.val = (reverseItem c).val) :
    TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel alpha v) ≤
      TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel alpha' v) := by
  exact
    lemma8_reducedOptimalItemFairness_mono_firstHalf_center_of_firstClosedPivot_endpoints
      (alphaLeft := alpha) (alphaRight := alpha') (v := v) (c := c)
      (t := problem6FirstClosedPivot alpha v halpha0 halpha1 hpos)
      (u := problem6FirstClosedPivot alpha' v halpha0' halpha1' hpos)
      halpha0 halpha1 halpha0' halpha1' halpha_le
      halpha_half halpha_half' hpos hdec hcenter_c rfl rfl

/--
Appendix D, Lemma 8 in paper-style endpoint-free form, even-center case.
-/
theorem lemma8_reducedOptimalItemFairness_mono_firstHalf_succ_center_of_alpha_le
    {n : ℕ} [NeZero n]
    {alpha alpha' : ℝ} {v : Item n → ℝ} {c : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (halpha_half : alpha ≤ 1 / 2)
    (halpha_half' : alpha' ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hsucc : c.val + 1 = (reverseItem c).val) :
    TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel alpha v) ≤
      TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel alpha' v) := by
  exact
    lemma8_reducedOptimalItemFairness_mono_firstHalf_succ_center_of_firstClosedPivot_endpoints
      (alphaLeft := alpha) (alphaRight := alpha') (v := v) (c := c)
      (t := problem6FirstClosedPivot alpha v halpha0 halpha1 hpos)
      (u := problem6FirstClosedPivot alpha' v halpha0' halpha1' hpos)
      halpha0 halpha1 halpha0' halpha1' halpha_le
      halpha_half halpha_half' hpos hdec hsucc rfl rfl

/--
Theorem 3 adjacent-boundary stitch for closed-form policies: fixed-pivot
type-1 utility monotonicity proves each side of the boundary, while uniqueness
of the equality-form optimal Problem 6 policy identifies the two adjacent
closed policies at the tight boundary.
-/
theorem theorem3_typeFairness_mono_across_adjacent_closed_boundary
    {n : ℕ} [NeZero n]
    {alphaLeft alphaBoundary alphaRight : ℝ}
    {v : Item n → ℝ} {t u : Item n}
    (halphaLeft0 : 0 < alphaLeft) (halphaLeft1 : alphaLeft < 1)
    (halphaBoundary0 : 0 < alphaBoundary)
    (halphaBoundary1 : alphaBoundary < 1)
    (halphaRight0 : 0 < alphaRight) (halphaRight1 : alphaRight < 1)
    (hleft_le_boundary : alphaLeft ≤ alphaBoundary)
    (hboundary_le_right : alphaBoundary ≤ alphaRight)
    (halphaLeft_half : alphaLeft ≤ 1 / 2)
    (halphaRight_half : alphaRight ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter_t : t.val ≤ (reverseItem t).val)
    (hcenter_u : u.val ≤ (reverseItem u).val)
    (hleft_bounds : Problem6ClosedPivotDenominatorBounds alphaLeft v t)
    (hnext : u.val = t.val + 1)
    (hboundary :
      problem6PivotGap alphaBoundary v t =
        - (pairShare alphaBoundary v t)⁻¹)
    (hright_bounds : Problem6ClosedPivotDenominatorBounds alphaRight v u) :
    let hpivotLeft : Problem6ClosedNonnegativePivots alphaLeft v t :=
      problem6ClosedNonnegativePivots_of_denominatorBounds
        halphaLeft0 halphaLeft1 hpos hleft_bounds
    let hpivotRight : Problem6ClosedNonnegativePivots alphaRight v u :=
      problem6ClosedNonnegativePivots_of_denominatorBounds
        halphaRight0 halphaRight1 hpos hright_bounds
    TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel alphaLeft v)
        (problem6ClosedPolicy alphaLeft v t
          halphaLeft0 halphaLeft1 hpos hpivotLeft) ≤
      TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel alphaRight v)
        (problem6ClosedPolicy alphaRight v u
          halphaRight0 halphaRight1 hpos hpivotRight) := by
  dsimp
  let hpivotLeft : Problem6ClosedNonnegativePivots alphaLeft v t :=
    problem6ClosedNonnegativePivots_of_denominatorBounds
      halphaLeft0 halphaLeft1 hpos hleft_bounds
  let hpivotRight : Problem6ClosedNonnegativePivots alphaRight v u :=
    problem6ClosedNonnegativePivots_of_denominatorBounds
      halphaRight0 halphaRight1 hpos hright_bounds
  rcases problem6ClosedPivotDenominatorBounds_adjacent_of_boundary
      halphaBoundary0 halphaBoundary1 hpos hnext hboundary with
    ⟨hboundary_t, hboundary_u⟩
  let hpivotBoundaryT :
      Problem6ClosedNonnegativePivots alphaBoundary v t :=
    problem6ClosedNonnegativePivots_of_denominatorBounds
      halphaBoundary0 halphaBoundary1 hpos hboundary_t
  let hpivotBoundaryU :
      Problem6ClosedNonnegativePivots alphaBoundary v u :=
    problem6ClosedNonnegativePivots_of_denominatorBounds
      halphaBoundary0 halphaBoundary1 hpos hboundary_u
  have halphaBoundary_half : alphaBoundary ≤ 1 / 2 :=
    hboundary_le_right.trans halphaRight_half
  have hleft_to_boundary :
      TypeWeightedRecommendationModel.typeFairness
          (twoTypeReducedModel alphaLeft v)
          (problem6ClosedPolicy alphaLeft v t
            halphaLeft0 halphaLeft1 hpos hpivotLeft) ≤
        TypeWeightedRecommendationModel.typeFairness
          (twoTypeReducedModel alphaBoundary v)
          (problem6ClosedPolicy alphaBoundary v t
            halphaBoundary0 halphaBoundary1 hpos hpivotBoundaryT) := by
    rw [
      problem6ClosedPolicy_typeFairness_eq_one_of_alpha_le_half_of_pivot_le_reverse
        halphaLeft0 halphaLeft1 halphaLeft_half hpos hdec hpivotLeft
        hcenter_t,
      problem6ClosedPolicy_typeFairness_eq_one_of_alpha_le_half_of_pivot_le_reverse
        halphaBoundary0 halphaBoundary1 halphaBoundary_half hpos hdec
        hpivotBoundaryT hcenter_t]
    exact
      theorem3_fixedPivot_closedPolicy_normalizedTypeUtility_one_mono
        halphaLeft0 halphaLeft1 halphaBoundary0 halphaBoundary1
        hleft_le_boundary hpos hdec hcenter_t hpivotLeft hpivotBoundaryT
  let certBoundaryT : Problem6ClosedOptimalityCertificate alphaBoundary v t :=
    problem6ClosedOptimalityCertificate_of_denominatorBounds
      halphaBoundary0 halphaBoundary1 hpos hdec hboundary_t
  let certBoundaryU : Problem6ClosedOptimalityCertificate alphaBoundary v u :=
    problem6ClosedOptimalityCertificate_of_denominatorBounds
      halphaBoundary0 halphaBoundary1 hpos hdec hboundary_u
  have hoptBoundaryT :
      Problem6EqualizedBasicOptimal alphaBoundary v
        (problem6ClosedPolicy alphaBoundary v t
          halphaBoundary0 halphaBoundary1 hpos hpivotBoundaryT)
        (problem6ClosedValue alphaBoundary v t) := by
    dsimp [hpivotBoundaryT, certBoundaryT]
    exact
      problem6EqualizedBasicOptimal_of_closed_certificate
        halphaBoundary0 halphaBoundary1 hpos certBoundaryT
  have hoptBoundaryU :
      Problem6EqualizedBasicOptimal alphaBoundary v
        (problem6ClosedPolicy alphaBoundary v u
          halphaBoundary0 halphaBoundary1 hpos hpivotBoundaryU)
        (problem6ClosedValue alphaBoundary v u) := by
    dsimp [hpivotBoundaryU, certBoundaryU]
    exact
      problem6EqualizedBasicOptimal_of_closed_certificate
        halphaBoundary0 halphaBoundary1 hpos certBoundaryU
  have hoptBoundaryTEq :
      TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
          (twoTypeReducedModel alphaBoundary v) 1 =
        TypeWeightedRecommendationModel.typeFairness
          (twoTypeReducedModel alphaBoundary v)
          (problem6ClosedPolicy alphaBoundary v t
            halphaBoundary0 halphaBoundary1 hpos hpivotBoundaryT) :=
    problem6EqualizedBasicOptimal_optimalTypeFairnessAtLevel_one_eq_of_upper_bound
      halphaBoundary0 halphaBoundary1 hpos hoptBoundaryT
      (fun ρ hfeas =>
        problem6ClosedPolicy_typeFairness_dominates_feasibleAtLevel_one_of_closed_certificate_alpha_le_half_of_pivot_le_reverse
          halphaBoundary0 halphaBoundary1 halphaBoundary_half hpos hdec
          certBoundaryT hcenter_t ρ hfeas)
  have hoptBoundaryUEq :
      TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
          (twoTypeReducedModel alphaBoundary v) 1 =
        TypeWeightedRecommendationModel.typeFairness
          (twoTypeReducedModel alphaBoundary v)
          (problem6ClosedPolicy alphaBoundary v u
            halphaBoundary0 halphaBoundary1 hpos hpivotBoundaryU) :=
    problem6EqualizedBasicOptimal_optimalTypeFairnessAtLevel_one_eq_of_upper_bound
      halphaBoundary0 halphaBoundary1 hpos hoptBoundaryU
      (fun ρ hfeas =>
        problem6ClosedPolicy_typeFairness_dominates_feasibleAtLevel_one_of_closed_certificate_alpha_le_half_of_pivot_le_reverse
          halphaBoundary0 halphaBoundary1 halphaBoundary_half hpos hdec
          certBoundaryU hcenter_u ρ hfeas)
  have hboundary_step :
      TypeWeightedRecommendationModel.typeFairness
          (twoTypeReducedModel alphaBoundary v)
          (problem6ClosedPolicy alphaBoundary v t
            halphaBoundary0 halphaBoundary1 hpos hpivotBoundaryT) ≤
        TypeWeightedRecommendationModel.typeFairness
          (twoTypeReducedModel alphaBoundary v)
          (problem6ClosedPolicy alphaBoundary v u
            halphaBoundary0 halphaBoundary1 hpos hpivotBoundaryU) := by
    rw [← hoptBoundaryTEq, ← hoptBoundaryUEq]
  have hboundary_to_right :
      TypeWeightedRecommendationModel.typeFairness
          (twoTypeReducedModel alphaBoundary v)
          (problem6ClosedPolicy alphaBoundary v u
            halphaBoundary0 halphaBoundary1 hpos hpivotBoundaryU) ≤
        TypeWeightedRecommendationModel.typeFairness
          (twoTypeReducedModel alphaRight v)
          (problem6ClosedPolicy alphaRight v u
            halphaRight0 halphaRight1 hpos hpivotRight) := by
    rw [
      problem6ClosedPolicy_typeFairness_eq_one_of_alpha_le_half_of_pivot_le_reverse
        halphaBoundary0 halphaBoundary1 halphaBoundary_half hpos hdec
        hpivotBoundaryU hcenter_u,
      problem6ClosedPolicy_typeFairness_eq_one_of_alpha_le_half_of_pivot_le_reverse
        halphaRight0 halphaRight1 halphaRight_half hpos hdec hpivotRight
        hcenter_u]
    exact
      theorem3_fixedPivot_closedPolicy_normalizedTypeUtility_one_mono
        halphaBoundary0 halphaBoundary1 halphaRight0 halphaRight1
        hboundary_le_right hpos hdec hcenter_u hpivotBoundaryU hpivotRight
  exact hleft_to_boundary.trans (hboundary_step.trans hboundary_to_right)

/--
Theorem 3 adjacent-boundary stitch for the canonical Lemma 5 first closed
pivot, odd-center case.
-/
theorem theorem3_typeFairness_mono_across_adjacent_firstClosedPivot_boundary_center
    {n : ℕ} [NeZero n]
    {alphaLeft alphaBoundary alphaRight : ℝ}
    {v : Item n → ℝ} {c t u : Item n}
    (halphaLeft0 : 0 < alphaLeft) (halphaLeft1 : alphaLeft < 1)
    (halphaBoundary0 : 0 < alphaBoundary)
    (halphaBoundary1 : alphaBoundary < 1)
    (halphaRight0 : 0 < alphaRight) (halphaRight1 : alphaRight < 1)
    (hleft_le_boundary : alphaLeft ≤ alphaBoundary)
    (hboundary_le_right : alphaBoundary ≤ alphaRight)
    (halphaLeft_half : alphaLeft ≤ 1 / 2)
    (halphaRight_half : alphaRight ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter_c : c.val = (reverseItem c).val)
    (hleft_pivot :
      problem6FirstClosedPivot alphaLeft v
        halphaLeft0 halphaLeft1 hpos = t)
    (hright_pivot :
      problem6FirstClosedPivot alphaRight v
        halphaRight0 halphaRight1 hpos = u)
    (hnext : u.val = t.val + 1)
    (hboundary :
      problem6PivotGap alphaBoundary v t =
        - (pairShare alphaBoundary v t)⁻¹) :
    TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel alphaLeft v)
        (problem6FirstClosedPolicy alphaLeft v
          halphaLeft0 halphaLeft1 hpos) ≤
      TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel alphaRight v)
        (problem6FirstClosedPolicy alphaRight v
          halphaRight0 halphaRight1 hpos) := by
  have hcenter_t :
      t.val ≤ (reverseItem t).val := by
    have h :=
      problem6FirstClosedPivot_le_reverse_of_alpha_le_half_center
        halphaLeft0 halphaLeft1 halphaLeft_half hpos hcenter_c
    simpa [← hleft_pivot] using h
  have hcenter_u :
      u.val ≤ (reverseItem u).val := by
    have h :=
      problem6FirstClosedPivot_le_reverse_of_alpha_le_half_center
        halphaRight0 halphaRight1 halphaRight_half hpos hcenter_c
    simpa [← hright_pivot] using h
  have hclosed :=
    theorem3_typeFairness_mono_across_adjacent_closed_boundary
      halphaLeft0 halphaLeft1
      halphaBoundary0 halphaBoundary1
      halphaRight0 halphaRight1
      hleft_le_boundary hboundary_le_right
      halphaLeft_half halphaRight_half
      hpos hdec hcenter_t hcenter_u
      (by
        simpa [hleft_pivot] using
          problem6FirstClosedPivot_denominatorBounds
            (alpha := alphaLeft) (v := v)
            halphaLeft0 halphaLeft1 hpos)
      hnext hboundary
      (by
        simpa [hright_pivot] using
          problem6FirstClosedPivot_denominatorBounds
            (alpha := alphaRight) (v := v)
            halphaRight0 halphaRight1 hpos)
  rw [
    problem6FirstClosedPolicy_eq_closedPolicy_of_firstClosedPivot_eq
      halphaLeft0 halphaLeft1 hpos hleft_pivot,
    problem6FirstClosedPolicy_eq_closedPolicy_of_firstClosedPivot_eq
      halphaRight0 halphaRight1 hpos hright_pivot]
  exact hclosed

/--
Theorem 3 adjacent-boundary stitch for the canonical Lemma 5 first closed
pivot, even-center case.
-/
theorem theorem3_typeFairness_mono_across_adjacent_firstClosedPivot_boundary_succ_center
    {n : ℕ} [NeZero n]
    {alphaLeft alphaBoundary alphaRight : ℝ}
    {v : Item n → ℝ} {c t u : Item n}
    (halphaLeft0 : 0 < alphaLeft) (halphaLeft1 : alphaLeft < 1)
    (halphaBoundary0 : 0 < alphaBoundary)
    (halphaBoundary1 : alphaBoundary < 1)
    (halphaRight0 : 0 < alphaRight) (halphaRight1 : alphaRight < 1)
    (hleft_le_boundary : alphaLeft ≤ alphaBoundary)
    (hboundary_le_right : alphaBoundary ≤ alphaRight)
    (halphaLeft_half : alphaLeft ≤ 1 / 2)
    (halphaRight_half : alphaRight ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hsucc : c.val + 1 = (reverseItem c).val)
    (hleft_pivot :
      problem6FirstClosedPivot alphaLeft v
        halphaLeft0 halphaLeft1 hpos = t)
    (hright_pivot :
      problem6FirstClosedPivot alphaRight v
        halphaRight0 halphaRight1 hpos = u)
    (hnext : u.val = t.val + 1)
    (hboundary :
      problem6PivotGap alphaBoundary v t =
        - (pairShare alphaBoundary v t)⁻¹) :
    TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel alphaLeft v)
        (problem6FirstClosedPolicy alphaLeft v
          halphaLeft0 halphaLeft1 hpos) ≤
      TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel alphaRight v)
        (problem6FirstClosedPolicy alphaRight v
          halphaRight0 halphaRight1 hpos) := by
  have hcenter_t :
      t.val ≤ (reverseItem t).val := by
    have h :=
      problem6FirstClosedPivot_le_reverse_of_alpha_le_half_succ_center
        halphaLeft0 halphaLeft1 halphaLeft_half hpos hsucc
    simpa [← hleft_pivot] using h
  have hcenter_u :
      u.val ≤ (reverseItem u).val := by
    have h :=
      problem6FirstClosedPivot_le_reverse_of_alpha_le_half_succ_center
        halphaRight0 halphaRight1 halphaRight_half hpos hsucc
    simpa [← hright_pivot] using h
  have hclosed :=
    theorem3_typeFairness_mono_across_adjacent_closed_boundary
      halphaLeft0 halphaLeft1
      halphaBoundary0 halphaBoundary1
      halphaRight0 halphaRight1
      hleft_le_boundary hboundary_le_right
      halphaLeft_half halphaRight_half
      hpos hdec hcenter_t hcenter_u
      (by
        simpa [hleft_pivot] using
          problem6FirstClosedPivot_denominatorBounds
            (alpha := alphaLeft) (v := v)
            halphaLeft0 halphaLeft1 hpos)
      hnext hboundary
      (by
        simpa [hright_pivot] using
          problem6FirstClosedPivot_denominatorBounds
            (alpha := alphaRight) (v := v)
            halphaRight0 halphaRight1 hpos)
  rw [
    problem6FirstClosedPolicy_eq_closedPolicy_of_firstClosedPivot_eq
      halphaLeft0 halphaLeft1 hpos hleft_pivot,
    problem6FirstClosedPolicy_eq_closedPolicy_of_firstClosedPivot_eq
      halphaRight0 halphaRight1 hpos hright_pivot]
  exact hclosed

/--
Theorem 3 same-canonical-pivot step, odd-center case: if the canonical
Lemma 5 first closed pivot is unchanged between two first-half parameters,
the canonical closed policy's type fairness is monotone.
-/
theorem theorem3_typeFairness_mono_of_same_firstClosedPivot_center
    {n : ℕ} [NeZero n]
    {alpha alpha' : ℝ} {v : Item n → ℝ} {c : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (halpha_half : alpha ≤ 1 / 2)
    (halpha_half' : alpha' ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter_c : c.val = (reverseItem c).val)
    (hpivot :
      problem6FirstClosedPivot alpha v halpha0 halpha1 hpos =
        problem6FirstClosedPivot alpha' v halpha0' halpha1' hpos) :
    TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel alpha v)
        (problem6FirstClosedPolicy alpha v halpha0 halpha1 hpos) ≤
      TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel alpha' v)
        (problem6FirstClosedPolicy alpha' v halpha0' halpha1' hpos) := by
  let t : Item n := problem6FirstClosedPivot alpha v halpha0 halpha1 hpos
  have hpivot' :
      problem6FirstClosedPivot alpha' v halpha0' halpha1' hpos = t := by
    simpa [t] using hpivot.symm
  have hcenter_t :
      t.val ≤ (reverseItem t).val := by
    dsimp [t]
    exact
      problem6FirstClosedPivot_le_reverse_of_alpha_le_half_center
        halpha0 halpha1 halpha_half hpos hcenter_c
  rw [
    problem6FirstClosedPolicy_eq_closedPolicy_of_firstClosedPivot_eq
      halpha0 halpha1 hpos (show
        problem6FirstClosedPivot alpha v halpha0 halpha1 hpos = t from rfl),
    problem6FirstClosedPolicy_eq_closedPolicy_of_firstClosedPivot_eq
      halpha0' halpha1' hpos hpivot']
  rw [
    problem6ClosedPolicy_typeFairness_eq_one_of_alpha_le_half_of_pivot_le_reverse
      halpha0 halpha1 halpha_half hpos hdec _ hcenter_t,
    problem6ClosedPolicy_typeFairness_eq_one_of_alpha_le_half_of_pivot_le_reverse
      halpha0' halpha1' halpha_half' hpos hdec _ hcenter_t]
  exact
    theorem3_fixedPivot_closedPolicy_normalizedTypeUtility_one_mono
      halpha0 halpha1 halpha0' halpha1' halpha_le hpos hdec
      hcenter_t _ _

/--
Theorem 3 same-canonical-pivot step, even-center case.
-/
theorem theorem3_typeFairness_mono_of_same_firstClosedPivot_succ_center
    {n : ℕ} [NeZero n]
    {alpha alpha' : ℝ} {v : Item n → ℝ} {c : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (halpha_half : alpha ≤ 1 / 2)
    (halpha_half' : alpha' ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hsucc : c.val + 1 = (reverseItem c).val)
    (hpivot :
      problem6FirstClosedPivot alpha v halpha0 halpha1 hpos =
        problem6FirstClosedPivot alpha' v halpha0' halpha1' hpos) :
    TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel alpha v)
        (problem6FirstClosedPolicy alpha v halpha0 halpha1 hpos) ≤
      TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel alpha' v)
        (problem6FirstClosedPolicy alpha' v halpha0' halpha1' hpos) := by
  let t : Item n := problem6FirstClosedPivot alpha v halpha0 halpha1 hpos
  have hpivot' :
      problem6FirstClosedPivot alpha' v halpha0' halpha1' hpos = t := by
    simpa [t] using hpivot.symm
  have hcenter_t :
      t.val ≤ (reverseItem t).val := by
    dsimp [t]
    exact
      problem6FirstClosedPivot_le_reverse_of_alpha_le_half_succ_center
        halpha0 halpha1 halpha_half hpos hsucc
  rw [
    problem6FirstClosedPolicy_eq_closedPolicy_of_firstClosedPivot_eq
      halpha0 halpha1 hpos (show
        problem6FirstClosedPivot alpha v halpha0 halpha1 hpos = t from rfl),
    problem6FirstClosedPolicy_eq_closedPolicy_of_firstClosedPivot_eq
      halpha0' halpha1' hpos hpivot']
  rw [
    problem6ClosedPolicy_typeFairness_eq_one_of_alpha_le_half_of_pivot_le_reverse
      halpha0 halpha1 halpha_half hpos hdec _ hcenter_t,
    problem6ClosedPolicy_typeFairness_eq_one_of_alpha_le_half_of_pivot_le_reverse
      halpha0' halpha1' halpha_half' hpos hdec _ hcenter_t]
  exact
    theorem3_fixedPivot_closedPolicy_normalizedTypeUtility_one_mono
      halpha0 halpha1 halpha0' halpha1' halpha_le hpos hdec
      hcenter_t _ _

/--
Theorem 3 adjacent canonical-pivot change, odd-center case: the tight boundary
is constructed internally from the endpoint pivot change.
-/
theorem theorem3_typeFairness_mono_across_adjacent_firstClosedPivot_change_center
    {n : ℕ} [NeZero n]
    {alphaLeft alphaRight : ℝ}
    {v : Item n → ℝ} {c t u : Item n}
    (halphaLeft0 : 0 < alphaLeft) (halphaLeft1 : alphaLeft < 1)
    (halphaRight0 : 0 < alphaRight) (halphaRight1 : alphaRight < 1)
    (hleft_le_right : alphaLeft ≤ alphaRight)
    (halphaLeft_half : alphaLeft ≤ 1 / 2)
    (halphaRight_half : alphaRight ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter_c : c.val = (reverseItem c).val)
    (hleft_pivot :
      problem6FirstClosedPivot alphaLeft v
        halphaLeft0 halphaLeft1 hpos = t)
    (hright_pivot :
      problem6FirstClosedPivot alphaRight v
        halphaRight0 halphaRight1 hpos = u)
    (hnext : u.val = t.val + 1) :
    TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel alphaLeft v)
        (problem6FirstClosedPolicy alphaLeft v
          halphaLeft0 halphaLeft1 hpos) ≤
      TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel alphaRight v)
        (problem6FirstClosedPolicy alphaRight v
          halphaRight0 halphaRight1 hpos) := by
  rcases problem6FirstClosedPivot_adjacentBoundary_exists
      halphaLeft0 halphaLeft1 halphaRight0 halphaRight1
      hleft_le_right hpos hleft_pivot hright_pivot hnext with
    ⟨alphaBoundary, hleft_le_boundary, hboundary_le_right,
      halphaBoundary0, halphaBoundary1, hboundary⟩
  exact
    theorem3_typeFairness_mono_across_adjacent_firstClosedPivot_boundary_center
      halphaLeft0 halphaLeft1
      halphaBoundary0 halphaBoundary1
      halphaRight0 halphaRight1
      hleft_le_boundary hboundary_le_right
      halphaLeft_half halphaRight_half
      hpos hdec hcenter_c hleft_pivot hright_pivot
      hnext hboundary

/--
Theorem 3 adjacent canonical-pivot change, even-center case.
-/
theorem theorem3_typeFairness_mono_across_adjacent_firstClosedPivot_change_succ_center
    {n : ℕ} [NeZero n]
    {alphaLeft alphaRight : ℝ}
    {v : Item n → ℝ} {c t u : Item n}
    (halphaLeft0 : 0 < alphaLeft) (halphaLeft1 : alphaLeft < 1)
    (halphaRight0 : 0 < alphaRight) (halphaRight1 : alphaRight < 1)
    (hleft_le_right : alphaLeft ≤ alphaRight)
    (halphaLeft_half : alphaLeft ≤ 1 / 2)
    (halphaRight_half : alphaRight ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hsucc : c.val + 1 = (reverseItem c).val)
    (hleft_pivot :
      problem6FirstClosedPivot alphaLeft v
        halphaLeft0 halphaLeft1 hpos = t)
    (hright_pivot :
      problem6FirstClosedPivot alphaRight v
        halphaRight0 halphaRight1 hpos = u)
    (hnext : u.val = t.val + 1) :
    TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel alphaLeft v)
        (problem6FirstClosedPolicy alphaLeft v
          halphaLeft0 halphaLeft1 hpos) ≤
      TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel alphaRight v)
        (problem6FirstClosedPolicy alphaRight v
          halphaRight0 halphaRight1 hpos) := by
  rcases problem6FirstClosedPivot_adjacentBoundary_exists
      halphaLeft0 halphaLeft1 halphaRight0 halphaRight1
      hleft_le_right hpos hleft_pivot hright_pivot hnext with
    ⟨alphaBoundary, hleft_le_boundary, hboundary_le_right,
      halphaBoundary0, halphaBoundary1, hboundary⟩
  exact
    theorem3_typeFairness_mono_across_adjacent_firstClosedPivot_boundary_succ_center
      halphaLeft0 halphaLeft1
      halphaBoundary0 halphaBoundary1
      halphaRight0 halphaRight1
      hleft_le_boundary hboundary_le_right
      halphaLeft_half halphaRight_half
      hpos hdec hsucc hleft_pivot hright_pivot
      hnext hboundary

/--
Theorem 3 global canonical closed-policy first-half stitch, odd-center case:
the no-skip adjacent-pivot construction connects any two endpoint canonical
first pivots.
-/
theorem theorem3_typeFairness_mono_firstHalf_center_of_firstClosedPivot_endpoints
    {n : ℕ} [NeZero n]
    {alphaLeft alphaRight : ℝ} {v : Item n → ℝ} {c t u : Item n}
    (halphaLeft0 : 0 < alphaLeft) (halphaLeft1 : alphaLeft < 1)
    (halphaRight0 : 0 < alphaRight) (halphaRight1 : alphaRight < 1)
    (hleft_le_right : alphaLeft ≤ alphaRight)
    (halphaLeft_half : alphaLeft ≤ 1 / 2)
    (halphaRight_half : alphaRight ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter_c : c.val = (reverseItem c).val)
    (hleft_pivot :
      problem6FirstClosedPivot alphaLeft v
        halphaLeft0 halphaLeft1 hpos = t)
    (hright_pivot :
      problem6FirstClosedPivot alphaRight v
        halphaRight0 halphaRight1 hpos = u) :
    TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel alphaLeft v)
        (problem6FirstClosedPolicy alphaLeft v
          halphaLeft0 halphaLeft1 hpos) ≤
      TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel alphaRight v)
        (problem6FirstClosedPolicy alphaRight v
          halphaRight0 halphaRight1 hpos) := by
  have htu : t.val ≤ u.val := by
    have h :=
      problem6FirstClosedPivot_mono_alpha
        halphaLeft0 halphaLeft1 halphaRight0 halphaRight1
        hleft_le_right hpos
    simpa [hleft_pivot, hright_pivot] using h
  generalize hgap_eq : u.val - t.val = gap
  revert alphaLeft alphaRight t u
  induction gap using Nat.strong_induction_on with
  | h gap ih =>
      intro alphaLeft alphaRight t u
        halphaLeft0 halphaLeft1 halphaRight0 halphaRight1
        hleft_le_right halphaLeft_half halphaRight_half
        hleft_pivot hright_pivot htu hgap_eq
      by_cases hsame_val : t.val = u.val
      · have htu_eq : t = u := Fin.ext hsame_val
        have hpivot_eq :
            problem6FirstClosedPivot alphaLeft v
                halphaLeft0 halphaLeft1 hpos =
              problem6FirstClosedPivot alphaRight v
                halphaRight0 halphaRight1 hpos := by
          rw [hleft_pivot, hright_pivot, htu_eq]
        exact
          theorem3_typeFairness_mono_of_same_firstClosedPivot_center
            halphaLeft0 halphaLeft1 halphaRight0 halphaRight1
            hleft_le_right halphaLeft_half halphaRight_half
            hpos hdec hcenter_c hpivot_eq
      · have ht_lt_u : t.val < u.val := lt_of_le_of_ne htu hsame_val
        by_cases hadj : u.val = t.val + 1
        · exact
            theorem3_typeFairness_mono_across_adjacent_firstClosedPivot_change_center
              halphaLeft0 halphaLeft1 halphaRight0 halphaRight1
              hleft_le_right halphaLeft_half halphaRight_half
              hpos hdec hcenter_c hleft_pivot hright_pivot hadj
        · have hskip : t.val + 1 < u.val := by omega
          rcases problem6FirstClosedPivot_successor_exists_of_pivot_jump
              halphaLeft0 halphaLeft1 halphaRight0 halphaRight1
              hleft_le_right hpos hleft_pivot hright_pivot hskip with
            ⟨alphaMid, halphaMid0, halphaMid1, s,
              hleft_le_mid, hmid_le_right, hs_val, hmid_pivot⟩
          have halphaMid_half : alphaMid ≤ 1 / 2 :=
            hmid_le_right.trans halphaRight_half
          have hleft_mid :
              TypeWeightedRecommendationModel.typeFairness
                  (twoTypeReducedModel alphaLeft v)
                  (problem6FirstClosedPolicy alphaLeft v
                    halphaLeft0 halphaLeft1 hpos) ≤
                TypeWeightedRecommendationModel.typeFairness
                  (twoTypeReducedModel alphaMid v)
                  (problem6FirstClosedPolicy alphaMid v
                    halphaMid0 halphaMid1 hpos) := by
            exact
              theorem3_typeFairness_mono_across_adjacent_firstClosedPivot_change_center
                halphaLeft0 halphaLeft1 halphaMid0 halphaMid1
                hleft_le_mid halphaLeft_half halphaMid_half
                hpos hdec hcenter_c hleft_pivot hmid_pivot hs_val
          have hs_le_u : s.val ≤ u.val := by
            rw [hs_val]
            exact le_of_lt hskip
          have hsmaller : u.val - s.val < gap := by
            rw [← hgap_eq, hs_val]
            omega
          have hmid_right :
              TypeWeightedRecommendationModel.typeFairness
                  (twoTypeReducedModel alphaMid v)
                  (problem6FirstClosedPolicy alphaMid v
                    halphaMid0 halphaMid1 hpos) ≤
                TypeWeightedRecommendationModel.typeFairness
                  (twoTypeReducedModel alphaRight v)
                  (problem6FirstClosedPolicy alphaRight v
                    halphaRight0 halphaRight1 hpos) := by
            exact ih (u.val - s.val) hsmaller
              halphaMid0 halphaMid1 halphaRight0 halphaRight1
              hmid_le_right halphaMid_half halphaRight_half
              hmid_pivot hright_pivot hs_le_u rfl
          exact hleft_mid.trans hmid_right

/--
Theorem 3 global canonical closed-policy first-half stitch, even-center case.
-/
theorem theorem3_typeFairness_mono_firstHalf_succ_center_of_firstClosedPivot_endpoints
    {n : ℕ} [NeZero n]
    {alphaLeft alphaRight : ℝ} {v : Item n → ℝ} {c t u : Item n}
    (halphaLeft0 : 0 < alphaLeft) (halphaLeft1 : alphaLeft < 1)
    (halphaRight0 : 0 < alphaRight) (halphaRight1 : alphaRight < 1)
    (hleft_le_right : alphaLeft ≤ alphaRight)
    (halphaLeft_half : alphaLeft ≤ 1 / 2)
    (halphaRight_half : alphaRight ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hsucc : c.val + 1 = (reverseItem c).val)
    (hleft_pivot :
      problem6FirstClosedPivot alphaLeft v
        halphaLeft0 halphaLeft1 hpos = t)
    (hright_pivot :
      problem6FirstClosedPivot alphaRight v
        halphaRight0 halphaRight1 hpos = u) :
    TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel alphaLeft v)
        (problem6FirstClosedPolicy alphaLeft v
          halphaLeft0 halphaLeft1 hpos) ≤
      TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel alphaRight v)
        (problem6FirstClosedPolicy alphaRight v
          halphaRight0 halphaRight1 hpos) := by
  have htu : t.val ≤ u.val := by
    have h :=
      problem6FirstClosedPivot_mono_alpha
        halphaLeft0 halphaLeft1 halphaRight0 halphaRight1
        hleft_le_right hpos
    simpa [hleft_pivot, hright_pivot] using h
  generalize hgap_eq : u.val - t.val = gap
  revert alphaLeft alphaRight t u
  induction gap using Nat.strong_induction_on with
  | h gap ih =>
      intro alphaLeft alphaRight t u
        halphaLeft0 halphaLeft1 halphaRight0 halphaRight1
        hleft_le_right halphaLeft_half halphaRight_half
        hleft_pivot hright_pivot htu hgap_eq
      by_cases hsame_val : t.val = u.val
      · have htu_eq : t = u := Fin.ext hsame_val
        have hpivot_eq :
            problem6FirstClosedPivot alphaLeft v
                halphaLeft0 halphaLeft1 hpos =
              problem6FirstClosedPivot alphaRight v
                halphaRight0 halphaRight1 hpos := by
          rw [hleft_pivot, hright_pivot, htu_eq]
        exact
          theorem3_typeFairness_mono_of_same_firstClosedPivot_succ_center
            halphaLeft0 halphaLeft1 halphaRight0 halphaRight1
            hleft_le_right halphaLeft_half halphaRight_half
            hpos hdec hsucc hpivot_eq
      · have ht_lt_u : t.val < u.val := lt_of_le_of_ne htu hsame_val
        by_cases hadj : u.val = t.val + 1
        · exact
            theorem3_typeFairness_mono_across_adjacent_firstClosedPivot_change_succ_center
              halphaLeft0 halphaLeft1 halphaRight0 halphaRight1
              hleft_le_right halphaLeft_half halphaRight_half
              hpos hdec hsucc hleft_pivot hright_pivot hadj
        · have hskip : t.val + 1 < u.val := by omega
          rcases problem6FirstClosedPivot_successor_exists_of_pivot_jump
              halphaLeft0 halphaLeft1 halphaRight0 halphaRight1
              hleft_le_right hpos hleft_pivot hright_pivot hskip with
            ⟨alphaMid, halphaMid0, halphaMid1, s,
              hleft_le_mid, hmid_le_right, hs_val, hmid_pivot⟩
          have halphaMid_half : alphaMid ≤ 1 / 2 :=
            hmid_le_right.trans halphaRight_half
          have hleft_mid :
              TypeWeightedRecommendationModel.typeFairness
                  (twoTypeReducedModel alphaLeft v)
                  (problem6FirstClosedPolicy alphaLeft v
                    halphaLeft0 halphaLeft1 hpos) ≤
                TypeWeightedRecommendationModel.typeFairness
                  (twoTypeReducedModel alphaMid v)
                  (problem6FirstClosedPolicy alphaMid v
                    halphaMid0 halphaMid1 hpos) := by
            exact
              theorem3_typeFairness_mono_across_adjacent_firstClosedPivot_change_succ_center
                halphaLeft0 halphaLeft1 halphaMid0 halphaMid1
                hleft_le_mid halphaLeft_half halphaMid_half
                hpos hdec hsucc hleft_pivot hmid_pivot hs_val
          have hs_le_u : s.val ≤ u.val := by
            rw [hs_val]
            exact le_of_lt hskip
          have hsmaller : u.val - s.val < gap := by
            rw [← hgap_eq, hs_val]
            omega
          have hmid_right :
              TypeWeightedRecommendationModel.typeFairness
                  (twoTypeReducedModel alphaMid v)
                  (problem6FirstClosedPolicy alphaMid v
                    halphaMid0 halphaMid1 hpos) ≤
                TypeWeightedRecommendationModel.typeFairness
                  (twoTypeReducedModel alphaRight v)
                  (problem6FirstClosedPolicy alphaRight v
                    halphaRight0 halphaRight1 hpos) := by
            exact ih (u.val - s.val) hsmaller
              halphaMid0 halphaMid1 halphaRight0 halphaRight1
              hmid_le_right halphaMid_half halphaRight_half
              hmid_pivot hright_pivot hs_le_u rfl
          exact hleft_mid.trans hmid_right

/--
Theorem 3 paper-style canonical closed-policy first-half monotonicity,
odd-center case.
-/
theorem theorem3_typeFairness_mono_firstHalf_center_of_alpha_le
    {n : ℕ} [NeZero n]
    {alpha alpha' : ℝ} {v : Item n → ℝ} {c : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (halpha_half : alpha ≤ 1 / 2)
    (halpha_half' : alpha' ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter_c : c.val = (reverseItem c).val) :
    TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel alpha v)
        (problem6FirstClosedPolicy alpha v halpha0 halpha1 hpos) ≤
      TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel alpha' v)
        (problem6FirstClosedPolicy alpha' v halpha0' halpha1' hpos) := by
  exact
    theorem3_typeFairness_mono_firstHalf_center_of_firstClosedPivot_endpoints
      (alphaLeft := alpha) (alphaRight := alpha') (v := v) (c := c)
      (t := problem6FirstClosedPivot alpha v halpha0 halpha1 hpos)
      (u := problem6FirstClosedPivot alpha' v halpha0' halpha1' hpos)
      halpha0 halpha1 halpha0' halpha1' halpha_le
      halpha_half halpha_half' hpos hdec hcenter_c rfl rfl

/--
Theorem 3 paper-style canonical closed-policy first-half monotonicity,
even-center case.
-/
theorem theorem3_typeFairness_mono_firstHalf_succ_center_of_alpha_le
    {n : ℕ} [NeZero n]
    {alpha alpha' : ℝ} {v : Item n → ℝ} {c : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (halpha_half : alpha ≤ 1 / 2)
    (halpha_half' : alpha' ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hsucc : c.val + 1 = (reverseItem c).val) :
    TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel alpha v)
        (problem6FirstClosedPolicy alpha v halpha0 halpha1 hpos) ≤
      TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel alpha' v)
        (problem6FirstClosedPolicy alpha' v halpha0' halpha1' hpos) := by
  exact
    theorem3_typeFairness_mono_firstHalf_succ_center_of_firstClosedPivot_endpoints
      (alphaLeft := alpha) (alphaRight := alpha') (v := v) (c := c)
      (t := problem6FirstClosedPivot alpha v halpha0 halpha1 hpos)
      (u := problem6FirstClosedPivot alpha' v halpha0' halpha1' hpos)
      halpha0 halpha1 halpha0' halpha1' halpha_le
      halpha_half halpha_half' hpos hdec hsucc rfl rfl

/--
Problem 6 canonical closed-policy optimality bridge: under the
Proposition-1-shaped feasible-policy canonicalization assumption, the Lemma 5
first-closed policy realizes the reduced `U^*_min(1, α)` value.
-/
theorem problem6FirstClosedPolicy_optimalTypeFairnessAtLevel_one_eq_of_feasible_canonicalization
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hcanonical :
      ∀ ρ' : TypePolicy 2 n,
        TypeWeightedRecommendationModel.feasibleAtLevel
          (twoTypeReducedModel alpha v) 1 ρ' →
        ∃ ρbar : TypePolicy 2 n,
          TypeWeightedRecommendationModel.feasibleAtLevel
            (twoTypeReducedModel alpha v) 1 ρbar ∧
          (∀ l : Item n,
            pairShare alpha v l * (ρbar 0 l).toReal +
              (1 - pairShare alpha v l) * (ρbar 1 l).toReal =
            TypeWeightedRecommendationModel.itemFairness
              (twoTypeReducedModel alpha v) ρbar) ∧
          TypePolicy.SharedItemsBound ρbar ∧
          TypeWeightedRecommendationModel.typeFairness
            (twoTypeReducedModel alpha v) ρ' ≤
          TypeWeightedRecommendationModel.typeFairness
            (twoTypeReducedModel alpha v) ρbar) :
    TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel alpha v) 1 =
      TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel alpha v)
        (problem6FirstClosedPolicy alpha v halpha0 halpha1 hpos) := by
  let t : Item n :=
    problem6FirstClosedPivot alpha v halpha0 halpha1 hpos
  let hbounds : Problem6ClosedPivotDenominatorBounds alpha v t :=
    problem6FirstClosedPivot_denominatorBounds
      (alpha := alpha) (v := v) halpha0 halpha1 hpos
  let cert : Problem6ClosedOptimalityCertificate alpha v t :=
    problem6ClosedOptimalityCertificate_of_denominatorBounds
      halpha0 halpha1 hpos hdec hbounds
  let hpivot : Problem6ClosedNonnegativePivots alpha v t :=
    problem6ClosedNonnegativePivots_of_denominatorBounds
      halpha0 halpha1 hpos hbounds
  have hclosed :
      Problem6EqualizedBasicOptimal alpha v
        (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot)
        (problem6ClosedValue alpha v t) := by
    dsimp [cert, hpivot]
    exact problem6EqualizedBasicOptimal_of_closed_certificate
      halpha0 halpha1 hpos cert
  have hvalue :
      TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
          (twoTypeReducedModel alpha v) 1 =
        TypeWeightedRecommendationModel.typeFairness
          (twoTypeReducedModel alpha v)
          (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot) :=
    problem6EqualizedBasicOptimal_optimalTypeFairnessAtLevel_one_eq_of_feasible_canonicalization
      hn halpha0 halpha1 hpos hdec hclosed hcanonical
  have hpolicy :
      problem6FirstClosedPolicy alpha v halpha0 halpha1 hpos =
        problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot := by
    dsimp [t, hpivot, hbounds]
    exact
      problem6FirstClosedPolicy_eq_closedPolicy_of_firstClosedPivot_eq
        halpha0 halpha1 hpos (hpivot_eq := rfl)
  rw [hvalue, hpolicy]

/--
Proposition 1 canonicalization bridge supplied by the type-`1` utility dual in
the first half: every `γ = 1` feasible reduced policy is dominated by the
Lemma 5 closed policy at the first closed pivot.
-/
theorem problem6FirstClosedPolicy_feasibleCanonicalization_firstHalf_of_pivot_le_reverse
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha_half : alpha ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter :
      (problem6FirstClosedPivot alpha v halpha0 halpha1 hpos).val ≤
        (reverseItem
          (problem6FirstClosedPivot alpha v halpha0 halpha1 hpos)).val) :
    ∀ ρ' : TypePolicy 2 n,
      TypeWeightedRecommendationModel.feasibleAtLevel
        (twoTypeReducedModel alpha v) 1 ρ' →
      ∃ ρbar : TypePolicy 2 n,
        TypeWeightedRecommendationModel.feasibleAtLevel
          (twoTypeReducedModel alpha v) 1 ρbar ∧
        (∀ l : Item n,
          pairShare alpha v l * (ρbar 0 l).toReal +
            (1 - pairShare alpha v l) * (ρbar 1 l).toReal =
          TypeWeightedRecommendationModel.itemFairness
            (twoTypeReducedModel alpha v) ρbar) ∧
        TypePolicy.SharedItemsBound ρbar ∧
        TypeWeightedRecommendationModel.typeFairness
          (twoTypeReducedModel alpha v) ρ' ≤
        TypeWeightedRecommendationModel.typeFairness
          (twoTypeReducedModel alpha v) ρbar := by
  intro ρ' hfeas'
  let t : Item n :=
    problem6FirstClosedPivot alpha v halpha0 halpha1 hpos
  let hbounds : Problem6ClosedPivotDenominatorBounds alpha v t :=
    problem6FirstClosedPivot_denominatorBounds
      (alpha := alpha) (v := v) halpha0 halpha1 hpos
  let cert : Problem6ClosedOptimalityCertificate alpha v t :=
    problem6ClosedOptimalityCertificate_of_denominatorBounds
      halpha0 halpha1 hpos hdec hbounds
  let hpivot : Problem6ClosedNonnegativePivots alpha v t :=
    problem6ClosedNonnegativePivots_of_denominatorBounds
      halpha0 halpha1 hpos hbounds
  let ρbar : TypePolicy 2 n :=
    problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot
  have hclosed :
      Problem6EqualizedBasicOptimal alpha v ρbar
        (problem6ClosedValue alpha v t) := by
    dsimp [ρbar, cert, hpivot]
    exact problem6EqualizedBasicOptimal_of_closed_certificate
      halpha0 halpha1 hpos cert
  refine ⟨ρbar, ?_, ?_, ?_, ?_⟩
  · exact problem6EqualizedBasicOptimal_feasibleAtLevel_one
      halpha0 halpha1 hpos hclosed
  · intro l
    exact problem6EqualizedBasicOptimal_item_value_eq_itemFairness
      halpha0 halpha1 hpos hclosed l
  · exact problem6_sharedItemsBound_of_equalizedBasicOptimal
      halpha0 halpha1 hpos hclosed
  · dsimp [ρbar, hpivot, cert, hbounds, t]
    exact
      problem6ClosedPolicy_typeFairness_dominates_feasibleAtLevel_one_of_closed_certificate_alpha_le_half_of_pivot_le_reverse
        halpha0 halpha1 halpha_half hpos hdec cert hcenter ρ' hfeas'

theorem problem6FirstClosedPolicy_optimalTypeFairnessAtLevel_one_eq_of_alpha_le_half_of_pivot_le_reverse
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha_half : alpha ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter :
      (problem6FirstClosedPivot alpha v halpha0 halpha1 hpos).val ≤
        (reverseItem
          (problem6FirstClosedPivot alpha v halpha0 halpha1 hpos)).val) :
    TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel alpha v) 1 =
      TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel alpha v)
        (problem6FirstClosedPolicy alpha v halpha0 halpha1 hpos) := by
  let t : Item n :=
    problem6FirstClosedPivot alpha v halpha0 halpha1 hpos
  let hbounds : Problem6ClosedPivotDenominatorBounds alpha v t :=
    problem6FirstClosedPivot_denominatorBounds
      (alpha := alpha) (v := v) halpha0 halpha1 hpos
  let cert : Problem6ClosedOptimalityCertificate alpha v t :=
    problem6ClosedOptimalityCertificate_of_denominatorBounds
      halpha0 halpha1 hpos hdec hbounds
  let hpivot : Problem6ClosedNonnegativePivots alpha v t :=
    problem6ClosedNonnegativePivots_of_denominatorBounds
      halpha0 halpha1 hpos hbounds
  have hclosed :
      Problem6EqualizedBasicOptimal alpha v
        (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot)
        (problem6ClosedValue alpha v t) := by
    dsimp [cert, hpivot]
    exact problem6EqualizedBasicOptimal_of_closed_certificate
      halpha0 halpha1 hpos cert
  have hvalue :
      TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
          (twoTypeReducedModel alpha v) 1 =
        TypeWeightedRecommendationModel.typeFairness
          (twoTypeReducedModel alpha v)
          (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot) :=
    problem6EqualizedBasicOptimal_optimalTypeFairnessAtLevel_one_eq_of_upper_bound
      halpha0 halpha1 hpos hclosed
      (fun ρ hfeas =>
        problem6ClosedPolicy_typeFairness_dominates_feasibleAtLevel_one_of_closed_certificate_alpha_le_half_of_pivot_le_reverse
          halpha0 halpha1 halpha_half hpos hdec cert hcenter ρ hfeas)
  have hpolicy :
      problem6FirstClosedPolicy alpha v halpha0 halpha1 hpos =
        problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot := by
    dsimp [t, hpivot, hbounds]
    exact
      problem6FirstClosedPolicy_eq_closedPolicy_of_firstClosedPivot_eq
        halpha0 halpha1 hpos (hpivot_eq := rfl)
  rw [hvalue, hpolicy]

theorem problem6FirstClosedPolicy_optimalTypeFairnessAtLevel_one_eq_firstHalf_center
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {c : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha_half : alpha ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter_c : c.val = (reverseItem c).val) :
    TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel alpha v) 1 =
      TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel alpha v)
        (problem6FirstClosedPolicy alpha v halpha0 halpha1 hpos) := by
  exact
    problem6FirstClosedPolicy_optimalTypeFairnessAtLevel_one_eq_of_alpha_le_half_of_pivot_le_reverse
      halpha0 halpha1 halpha_half hpos hdec
      (problem6FirstClosedPivot_le_reverse_of_alpha_le_half_center
        halpha0 halpha1 halpha_half hpos hcenter_c)

theorem problem6FirstClosedPolicy_optimalTypeFairnessAtLevel_one_eq_firstHalf_succ_center
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ} {c : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha_half : alpha ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hsucc : c.val + 1 = (reverseItem c).val) :
    TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel alpha v) 1 =
      TypeWeightedRecommendationModel.typeFairness
        (twoTypeReducedModel alpha v)
        (problem6FirstClosedPolicy alpha v halpha0 halpha1 hpos) := by
  exact
    problem6FirstClosedPolicy_optimalTypeFairnessAtLevel_one_eq_of_alpha_le_half_of_pivot_le_reverse
      halpha0 halpha1 halpha_half hpos hdec
      (problem6FirstClosedPivot_le_reverse_of_alpha_le_half_succ_center
        halpha0 halpha1 halpha_half hpos hsucc)

theorem problem6FirstClosedPolicy_feasibleAtLevel_one
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v) :
    TypeWeightedRecommendationModel.feasibleAtLevel
      (twoTypeReducedModel alpha v) 1
      (problem6FirstClosedPolicy alpha v halpha0 halpha1 hpos) := by
  let t : Item n :=
    problem6FirstClosedPivot alpha v halpha0 halpha1 hpos
  let cert : Problem6ClosedOptimalityCertificate alpha v t :=
    problem6FirstClosedPivot_optimalityCertificate
      halpha0 halpha1 hpos hdec
  let hpivot : Problem6ClosedNonnegativePivots alpha v t :=
    problem6ClosedNonnegativePivots_of_denominatorBounds
      halpha0 halpha1 hpos cert.denominator_bounds
  have hclosed :
      Problem6EqualizedBasicOptimal alpha v
        (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot)
        (problem6ClosedValue alpha v t) := by
    dsimp [cert, hpivot]
    exact problem6EqualizedBasicOptimal_of_closed_certificate
      halpha0 halpha1 hpos cert
  have hpolicy :
      problem6FirstClosedPolicy alpha v halpha0 halpha1 hpos =
        problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot := by
    dsimp [t, hpivot, cert]
    exact
      problem6FirstClosedPolicy_eq_closedPolicy_of_firstClosedPivot_eq
        halpha0 halpha1 hpos (hpivot_eq := rfl)
  have hfeas :
      TypeWeightedRecommendationModel.feasibleAtLevel
        (twoTypeReducedModel alpha v) 1
        (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot) :=
    problem6EqualizedBasicOptimal_feasibleAtLevel_one
      halpha0 halpha1 hpos hclosed
  simpa [hpolicy] using hfeas

theorem twoTypeReducedModel_attainableTypeFairnessAtLevel_one_nonempty
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v) :
    (TypeWeightedRecommendationModel.attainableTypeFairnessAtLevel
      (twoTypeReducedModel alpha v) 1).Nonempty := by
  refine ⟨TypeWeightedRecommendationModel.typeFairness
    (twoTypeReducedModel alpha v)
    (problem6FirstClosedPolicy alpha v halpha0 halpha1 hpos), ?_⟩
  exact ⟨problem6FirstClosedPolicy alpha v halpha0 halpha1 hpos,
    problem6FirstClosedPolicy_feasibleAtLevel_one
      halpha0 halpha1 hpos hdec, rfl⟩

/--
Problem 6 canonical closed-policy optimality bridge, packaged as
`IsOptimalAtLevel`.
-/
theorem problem6FirstClosedPolicy_isOptimalAtLevel_one_of_feasible_canonicalization
    {n : ℕ} [NeZero n]
    {alpha : ℝ} {v : Item n → ℝ}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hcanonical :
      ∀ ρ' : TypePolicy 2 n,
        TypeWeightedRecommendationModel.feasibleAtLevel
          (twoTypeReducedModel alpha v) 1 ρ' →
        ∃ ρbar : TypePolicy 2 n,
          TypeWeightedRecommendationModel.feasibleAtLevel
            (twoTypeReducedModel alpha v) 1 ρbar ∧
          (∀ l : Item n,
            pairShare alpha v l * (ρbar 0 l).toReal +
              (1 - pairShare alpha v l) * (ρbar 1 l).toReal =
            TypeWeightedRecommendationModel.itemFairness
              (twoTypeReducedModel alpha v) ρbar) ∧
          TypePolicy.SharedItemsBound ρbar ∧
          TypeWeightedRecommendationModel.typeFairness
            (twoTypeReducedModel alpha v) ρ' ≤
          TypeWeightedRecommendationModel.typeFairness
            (twoTypeReducedModel alpha v) ρbar) :
    TypeWeightedRecommendationModel.IsOptimalAtLevel
      (twoTypeReducedModel alpha v) 1
      (problem6FirstClosedPolicy alpha v halpha0 halpha1 hpos) := by
  let t : Item n :=
    problem6FirstClosedPivot alpha v halpha0 halpha1 hpos
  let hbounds : Problem6ClosedPivotDenominatorBounds alpha v t :=
    problem6FirstClosedPivot_denominatorBounds
      (alpha := alpha) (v := v) halpha0 halpha1 hpos
  let cert : Problem6ClosedOptimalityCertificate alpha v t :=
    problem6ClosedOptimalityCertificate_of_denominatorBounds
      halpha0 halpha1 hpos hdec hbounds
  let hpivot : Problem6ClosedNonnegativePivots alpha v t :=
    problem6ClosedNonnegativePivots_of_denominatorBounds
      halpha0 halpha1 hpos hbounds
  have hclosed :
      Problem6EqualizedBasicOptimal alpha v
        (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot)
        (problem6ClosedValue alpha v t) := by
    dsimp [cert, hpivot]
    exact problem6EqualizedBasicOptimal_of_closed_certificate
      halpha0 halpha1 hpos cert
  have hpolicy :
      problem6FirstClosedPolicy alpha v halpha0 halpha1 hpos =
        problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot := by
    dsimp [t, hpivot, hbounds]
    exact
      problem6FirstClosedPolicy_eq_closedPolicy_of_firstClosedPivot_eq
        halpha0 halpha1 hpos rfl
  refine ⟨?_, ?_⟩
  · have hfeas :
        TypeWeightedRecommendationModel.feasibleAtLevel
          (twoTypeReducedModel alpha v) 1
          (problem6ClosedPolicy alpha v t halpha0 halpha1 hpos hpivot) :=
      problem6EqualizedBasicOptimal_feasibleAtLevel_one
        halpha0 halpha1 hpos hclosed
    simpa [hpolicy] using hfeas
  · exact
      (problem6FirstClosedPolicy_optimalTypeFairnessAtLevel_one_eq_of_feasible_canonicalization
        hn halpha0 halpha1 hpos hdec hcanonical).symm

/--
Theorem 3 reduced-optimum bridge, odd-center first-half endpoint form, under
the Proposition-1-shaped feasible-policy canonicalization assumption at the
two endpoints.
-/
theorem theorem3_optimalTypeFairnessAtLevel_one_mono_firstHalf_center_of_alpha_le_of_feasible_canonicalization
    {n : ℕ} [NeZero n]
    {alpha alpha' : ℝ} {v : Item n → ℝ} {c : Item n}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (halpha_half : alpha ≤ 1 / 2)
    (halpha_half' : alpha' ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter_c : c.val = (reverseItem c).val)
    (hcanonical :
      ∀ ρ : TypePolicy 2 n,
        TypeWeightedRecommendationModel.feasibleAtLevel
          (twoTypeReducedModel alpha v) 1 ρ →
        ∃ ρbar : TypePolicy 2 n,
          TypeWeightedRecommendationModel.feasibleAtLevel
            (twoTypeReducedModel alpha v) 1 ρbar ∧
          (∀ l : Item n,
            pairShare alpha v l * (ρbar 0 l).toReal +
              (1 - pairShare alpha v l) * (ρbar 1 l).toReal =
            TypeWeightedRecommendationModel.itemFairness
              (twoTypeReducedModel alpha v) ρbar) ∧
          TypePolicy.SharedItemsBound ρbar ∧
          TypeWeightedRecommendationModel.typeFairness
            (twoTypeReducedModel alpha v) ρ ≤
          TypeWeightedRecommendationModel.typeFairness
            (twoTypeReducedModel alpha v) ρbar)
    (hcanonical' :
      ∀ ρ : TypePolicy 2 n,
        TypeWeightedRecommendationModel.feasibleAtLevel
          (twoTypeReducedModel alpha' v) 1 ρ →
        ∃ ρbar : TypePolicy 2 n,
          TypeWeightedRecommendationModel.feasibleAtLevel
            (twoTypeReducedModel alpha' v) 1 ρbar ∧
          (∀ l : Item n,
            pairShare alpha' v l * (ρbar 0 l).toReal +
              (1 - pairShare alpha' v l) * (ρbar 1 l).toReal =
            TypeWeightedRecommendationModel.itemFairness
              (twoTypeReducedModel alpha' v) ρbar) ∧
          TypePolicy.SharedItemsBound ρbar ∧
          TypeWeightedRecommendationModel.typeFairness
            (twoTypeReducedModel alpha' v) ρ ≤
          TypeWeightedRecommendationModel.typeFairness
            (twoTypeReducedModel alpha' v) ρbar) :
    TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel alpha v) 1 ≤
      TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel alpha' v) 1 := by
  have hleft :=
    problem6FirstClosedPolicy_optimalTypeFairnessAtLevel_one_eq_of_feasible_canonicalization
      hn halpha0 halpha1 hpos hdec hcanonical
  have hright :=
    problem6FirstClosedPolicy_optimalTypeFairnessAtLevel_one_eq_of_feasible_canonicalization
      hn halpha0' halpha1' hpos hdec hcanonical'
  rw [hleft, hright]
  exact
    theorem3_typeFairness_mono_firstHalf_center_of_alpha_le
      halpha0 halpha1 halpha0' halpha1' halpha_le
      halpha_half halpha_half' hpos hdec hcenter_c

/--
Theorem 3 reduced-optimum bridge, even-center first-half endpoint form, under
the Proposition-1-shaped feasible-policy canonicalization assumption at the
two endpoints.
-/
theorem theorem3_optimalTypeFairnessAtLevel_one_mono_firstHalf_succ_center_of_alpha_le_of_feasible_canonicalization
    {n : ℕ} [NeZero n]
    {alpha alpha' : ℝ} {v : Item n → ℝ} {c : Item n}
    (hn : 2 < n)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (halpha_half : alpha ≤ 1 / 2)
    (halpha_half' : alpha' ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hsucc : c.val + 1 = (reverseItem c).val)
    (hcanonical :
      ∀ ρ : TypePolicy 2 n,
        TypeWeightedRecommendationModel.feasibleAtLevel
          (twoTypeReducedModel alpha v) 1 ρ →
        ∃ ρbar : TypePolicy 2 n,
          TypeWeightedRecommendationModel.feasibleAtLevel
            (twoTypeReducedModel alpha v) 1 ρbar ∧
          (∀ l : Item n,
            pairShare alpha v l * (ρbar 0 l).toReal +
              (1 - pairShare alpha v l) * (ρbar 1 l).toReal =
            TypeWeightedRecommendationModel.itemFairness
              (twoTypeReducedModel alpha v) ρbar) ∧
          TypePolicy.SharedItemsBound ρbar ∧
          TypeWeightedRecommendationModel.typeFairness
            (twoTypeReducedModel alpha v) ρ ≤
          TypeWeightedRecommendationModel.typeFairness
            (twoTypeReducedModel alpha v) ρbar)
    (hcanonical' :
      ∀ ρ : TypePolicy 2 n,
        TypeWeightedRecommendationModel.feasibleAtLevel
          (twoTypeReducedModel alpha' v) 1 ρ →
        ∃ ρbar : TypePolicy 2 n,
          TypeWeightedRecommendationModel.feasibleAtLevel
            (twoTypeReducedModel alpha' v) 1 ρbar ∧
          (∀ l : Item n,
            pairShare alpha' v l * (ρbar 0 l).toReal +
              (1 - pairShare alpha' v l) * (ρbar 1 l).toReal =
            TypeWeightedRecommendationModel.itemFairness
              (twoTypeReducedModel alpha' v) ρbar) ∧
          TypePolicy.SharedItemsBound ρbar ∧
          TypeWeightedRecommendationModel.typeFairness
            (twoTypeReducedModel alpha' v) ρ ≤
          TypeWeightedRecommendationModel.typeFairness
            (twoTypeReducedModel alpha' v) ρbar) :
    TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel alpha v) 1 ≤
      TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel alpha' v) 1 := by
  have hleft :=
    problem6FirstClosedPolicy_optimalTypeFairnessAtLevel_one_eq_of_feasible_canonicalization
      hn halpha0 halpha1 hpos hdec hcanonical
  have hright :=
    problem6FirstClosedPolicy_optimalTypeFairnessAtLevel_one_eq_of_feasible_canonicalization
      hn halpha0' halpha1' hpos hdec hcanonical'
  rw [hleft, hright]
  exact
    theorem3_typeFairness_mono_firstHalf_succ_center_of_alpha_le
      halpha0 halpha1 halpha0' halpha1' halpha_le
      halpha_half halpha_half' hpos hdec hsucc

/--
Theorem 3 reduced-optimum bridge, odd-center first-half endpoint form.  The
type-`1` utility dual supplies the Proposition-1-shaped canonicalization at both
endpoints, so no external canonicalization hypothesis remains.
-/
theorem theorem3_optimalTypeFairnessAtLevel_one_mono_firstHalf_center_of_alpha_le
    {n : ℕ} [NeZero n]
    {alpha alpha' : ℝ} {v : Item n → ℝ} {c : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (halpha_half : alpha ≤ 1 / 2)
    (halpha_half' : alpha' ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter_c : c.val = (reverseItem c).val) :
    TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel alpha v) 1 ≤
      TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel alpha' v) 1 := by
  have hleft :=
    problem6FirstClosedPolicy_optimalTypeFairnessAtLevel_one_eq_firstHalf_center
      halpha0 halpha1 halpha_half hpos hdec hcenter_c
  have hright :=
    problem6FirstClosedPolicy_optimalTypeFairnessAtLevel_one_eq_firstHalf_center
      halpha0' halpha1' halpha_half' hpos hdec hcenter_c
  rw [hleft, hright]
  exact
    theorem3_typeFairness_mono_firstHalf_center_of_alpha_le
      halpha0 halpha1 halpha0' halpha1' halpha_le
      halpha_half halpha_half' hpos hdec hcenter_c

/--
Theorem 3 reduced-optimum bridge, even-center first-half endpoint form.  The
type-`1` utility dual supplies the Proposition-1-shaped canonicalization at both
endpoints, so no external canonicalization hypothesis remains.
-/
theorem theorem3_optimalTypeFairnessAtLevel_one_mono_firstHalf_succ_center_of_alpha_le
    {n : ℕ} [NeZero n]
    {alpha alpha' : ℝ} {v : Item n → ℝ} {c : Item n}
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (halpha0' : 0 < alpha') (halpha1' : alpha' < 1)
    (halpha_le : alpha ≤ alpha')
    (halpha_half : alpha ≤ 1 / 2)
    (halpha_half' : alpha' ≤ 1 / 2)
    (hpos : ∀ j : Item n, 0 < v j)
    (hdec : StrictlyDecreasingByIndex v)
    (hsucc : c.val + 1 = (reverseItem c).val) :
    TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel alpha v) 1 ≤
      TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel alpha' v) 1 := by
  have hleft :=
    problem6FirstClosedPolicy_optimalTypeFairnessAtLevel_one_eq_firstHalf_succ_center
      halpha0 halpha1 halpha_half hpos hdec hsucc
  have hright :=
    problem6FirstClosedPolicy_optimalTypeFairnessAtLevel_one_eq_firstHalf_succ_center
      halpha0' halpha1' halpha_half' hpos hdec hsucc
  rw [hleft, hright]
  exact
    theorem3_typeFairness_mono_firstHalf_succ_center_of_alpha_le
      halpha0 halpha1 halpha0' halpha1' halpha_le
      halpha_half halpha_half' hpos hdec hsucc

/--
Appendix D, Lemma 8 finite-stitch core for closed-form certificates: a finite
chain may either stay inside one certified same-pivot interval, where Lemma 11
applies, or repeat the same `α` at a boundary.  This is the closed-form version
of the paper's continuity stitch across adjacent `A(t)` intervals.
-/
theorem lemma8_reducedOptimalItemFairness_mono_of_closedPivot_cert_or_equal_alpha_chain
    {n : ℕ} [NeZero n]
    {v : Item n → ℝ} (r : ℕ)
    (alphaSeq : ℕ → ℝ)
    (pivotSeq : ℕ → Item n)
    (halpha0 : ∀ i, i ≤ r → 0 < alphaSeq i)
    (halpha1 : ∀ i, i ≤ r → alphaSeq i < 1)
    (hstep : ∀ i, i < r → alphaSeq i ≤ alphaSeq (i + 1))
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hcert :
      ∀ i, ∀ hi : i ≤ r,
        Problem6ClosedOptimalityCertificate (alphaSeq i) v (pivotSeq i))
    (hpivot_or_eq :
      ∀ i, i < r →
        pivotSeq i = pivotSeq (i + 1) ∨
        alphaSeq i = alphaSeq (i + 1))
    (hcenter :
      ∀ i, i < r →
        (pivotSeq i).val ≤ (reverseItem (pivotSeq i)).val) :
    TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel (alphaSeq 0) v) ≤
      TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel (alphaSeq r) v) := by
  induction r with
  | zero =>
      exact le_rfl
  | succ r ih =>
      have hprev :
          TypeWeightedRecommendationModel.optimalItemFairness
              (twoTypeReducedModel (alphaSeq 0) v) ≤
            TypeWeightedRecommendationModel.optimalItemFairness
              (twoTypeReducedModel (alphaSeq r) v) := by
        exact ih
          (fun i hi => halpha0 i (Nat.le_trans hi (Nat.le_succ r)))
          (fun i hi => halpha1 i (Nat.le_trans hi (Nat.le_succ r)))
          (fun i hi => hstep i (Nat.lt_trans hi (Nat.lt_succ_self r)))
          (fun i hi => hcert i (Nat.le_trans hi (Nat.le_succ r)))
          (fun i hi => hpivot_or_eq i (Nat.lt_trans hi (Nat.lt_succ_self r)))
          (fun i hi => hcenter i (Nat.lt_trans hi (Nat.lt_succ_self r)))
      have hlast :
          TypeWeightedRecommendationModel.optimalItemFairness
              (twoTypeReducedModel (alphaSeq r) v) ≤
            TypeWeightedRecommendationModel.optimalItemFairness
              (twoTypeReducedModel (alphaSeq (r + 1)) v) := by
        rcases hpivot_or_eq r (Nat.lt_succ_self r) with hpivot | halpha_eq
        · have cert' :
              Problem6ClosedOptimalityCertificate (alphaSeq (r + 1)) v
                (pivotSeq r) := by
            simpa [hpivot] using hcert (r + 1) le_rfl
          exact
            lemma11_reducedOptimalItemFairness_mono_of_fixed_pivot_cert
              (halpha0 r (Nat.le_succ r))
              (halpha1 r (Nat.le_succ r))
              (halpha0 (r + 1) le_rfl)
              (halpha1 (r + 1) le_rfl)
              (hstep r (Nat.lt_succ_self r))
              hpos hdec
              (hcenter r (Nat.lt_succ_self r))
              (hcert r (Nat.le_succ r))
              cert'
        · simpa [halpha_eq] using
            (le_rfl :
              TypeWeightedRecommendationModel.optimalItemFairness
                (twoTypeReducedModel (alphaSeq r) v) ≤
              TypeWeightedRecommendationModel.optimalItemFairness
                (twoTypeReducedModel (alphaSeq r) v))
      exact hprev.trans hlast

/--
Appendix D, Lemma 8 finite-stitch core for closed-form denominator bounds:
denominator-bounded closed pivots supply the optimality certificates required
by the certified stitch theorem.
-/
theorem lemma8_reducedOptimalItemFairness_mono_of_closedPivotBounds_or_equal_alpha_chain
    {n : ℕ} [NeZero n]
    {v : Item n → ℝ} (r : ℕ)
    (alphaSeq : ℕ → ℝ)
    (pivotSeq : ℕ → Item n)
    (halpha0 : ∀ i, i ≤ r → 0 < alphaSeq i)
    (halpha1 : ∀ i, i ≤ r → alphaSeq i < 1)
    (hstep : ∀ i, i < r → alphaSeq i ≤ alphaSeq (i + 1))
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hbounds :
      ∀ i, ∀ hi : i ≤ r,
        Problem6ClosedPivotDenominatorBounds (alphaSeq i) v (pivotSeq i))
    (hpivot_or_eq :
      ∀ i, i < r →
        pivotSeq i = pivotSeq (i + 1) ∨
        alphaSeq i = alphaSeq (i + 1))
    (hcenter :
      ∀ i, i < r →
        (pivotSeq i).val ≤ (reverseItem (pivotSeq i)).val) :
    TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel (alphaSeq 0) v) ≤
      TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel (alphaSeq r) v) := by
  exact
    lemma8_reducedOptimalItemFairness_mono_of_closedPivot_cert_or_equal_alpha_chain
      r alphaSeq pivotSeq halpha0 halpha1 hstep hpos hdec
      (fun i hi =>
        problem6ClosedOptimalityCertificate_of_denominatorBounds
          (halpha0 i hi) (halpha1 i hi) hpos hdec (hbounds i hi))
      hpivot_or_eq hcenter

/--
Appendix D, Lemma 8 canonical finite-stitch core with explicit boundary
repeats: a finite chain may either stay inside one `A(t)` interval for the
canonical Lemma 5 first crossing pivot, where Lemma 11 applies, or repeat the
same `α` at an interval boundary.

The auxiliary `pivotSeq` records the canonical first pivot at each chain point
without making later hypotheses depend on proof-term choices for
`0 < α < 1`.
-/
theorem lemma8_reducedOptimalItemFairness_mono_of_same_firstClosedPivot_or_equal_alpha_chain
    {n : ℕ} [NeZero n]
    {v : Item n → ℝ} (r : ℕ)
    (alphaSeq : ℕ → ℝ)
    (pivotSeq : ℕ → Item n)
    (halpha0 : ∀ i, i ≤ r → 0 < alphaSeq i)
    (halpha1 : ∀ i, i ≤ r → alphaSeq i < 1)
    (hstep : ∀ i, i < r → alphaSeq i ≤ alphaSeq (i + 1))
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hpivot_def :
      ∀ i, ∀ hi : i ≤ r,
        pivotSeq i =
          problem6FirstClosedPivot (alphaSeq i) v
            (halpha0 i hi) (halpha1 i hi) hpos)
    (hpivot_or_eq :
      ∀ i, i < r →
        pivotSeq i = pivotSeq (i + 1) ∨
        alphaSeq i = alphaSeq (i + 1))
    (hcenter :
      ∀ i, i < r →
        (pivotSeq i).val ≤ (reverseItem (pivotSeq i)).val) :
    TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel (alphaSeq 0) v) ≤
      TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel (alphaSeq r) v) := by
  induction r with
  | zero =>
      exact le_rfl
  | succ r ih =>
      have hprev :
          TypeWeightedRecommendationModel.optimalItemFairness
              (twoTypeReducedModel (alphaSeq 0) v) ≤
            TypeWeightedRecommendationModel.optimalItemFairness
              (twoTypeReducedModel (alphaSeq r) v) := by
        exact ih
          (fun i hi => halpha0 i (Nat.le_trans hi (Nat.le_succ r)))
          (fun i hi => halpha1 i (Nat.le_trans hi (Nat.le_succ r)))
          (fun i hi => hstep i (Nat.lt_trans hi (Nat.lt_succ_self r)))
          (fun i hi => hpivot_def i (Nat.le_trans hi (Nat.le_succ r)))
          (fun i hi => hpivot_or_eq i (Nat.lt_trans hi (Nat.lt_succ_self r)))
          (fun i hi => hcenter i (Nat.lt_trans hi (Nat.lt_succ_self r)))
      have hlast :
          TypeWeightedRecommendationModel.optimalItemFairness
              (twoTypeReducedModel (alphaSeq r) v) ≤
            TypeWeightedRecommendationModel.optimalItemFairness
              (twoTypeReducedModel (alphaSeq (r + 1)) v) := by
        rcases hpivot_or_eq r (Nat.lt_succ_self r) with hpivot | halpha_eq
        · have hfpivot :
              problem6FirstClosedPivot (alphaSeq r) v
                  (halpha0 r (Nat.le_succ r))
                  (halpha1 r (Nat.le_succ r)) hpos =
                problem6FirstClosedPivot (alphaSeq (r + 1)) v
                  (halpha0 (r + 1) le_rfl)
                  (halpha1 (r + 1) le_rfl) hpos := by
            calc
              problem6FirstClosedPivot (alphaSeq r) v
                  (halpha0 r (Nat.le_succ r))
                  (halpha1 r (Nat.le_succ r)) hpos
                  = pivotSeq r := (hpivot_def r (Nat.le_succ r)).symm
              _ = pivotSeq (r + 1) := hpivot
              _ =
                problem6FirstClosedPivot (alphaSeq (r + 1)) v
                  (halpha0 (r + 1) le_rfl)
                  (halpha1 (r + 1) le_rfl) hpos :=
                hpivot_def (r + 1) le_rfl
          have hc :
              (problem6FirstClosedPivot (alphaSeq r) v
                  (halpha0 r (Nat.le_succ r))
                  (halpha1 r (Nat.le_succ r)) hpos).val ≤
                (reverseItem
                  (problem6FirstClosedPivot (alphaSeq r) v
                    (halpha0 r (Nat.le_succ r))
                    (halpha1 r (Nat.le_succ r)) hpos)).val := by
            simpa [hpivot_def r (Nat.le_succ r)] using
              hcenter r (Nat.lt_succ_self r)
          exact
            lemma11_reducedOptimalItemFairness_mono_of_same_firstClosedPivot
              (halpha0 r (Nat.le_succ r))
              (halpha1 r (Nat.le_succ r))
              (halpha0 (r + 1) le_rfl)
              (halpha1 (r + 1) le_rfl)
              (hstep r (Nat.lt_succ_self r))
              hpos hdec hfpivot hc
        · simpa [halpha_eq] using
            (le_rfl :
              TypeWeightedRecommendationModel.optimalItemFairness
                (twoTypeReducedModel (alphaSeq r) v) ≤
              TypeWeightedRecommendationModel.optimalItemFairness
                (twoTypeReducedModel (alphaSeq r) v))
      exact hprev.trans hlast

/--
Appendix D, Lemma 8 canonical first-half finite-stitch core, odd-center case:
on a chain contained in `α ≤ 1/2`, the midpoint Lemma 10 certificate and
canonical pivot monotonicity supply the pivot-before-mirror condition for every
same-`A(t)` step.
-/
theorem lemma8_reducedOptimalItemFairness_mono_firstHalf_center_firstClosedPivot_chain
    {n : ℕ} [NeZero n]
    {v : Item n → ℝ} {c : Item n}
    (r : ℕ)
    (alphaSeq : ℕ → ℝ)
    (pivotSeq : ℕ → Item n)
    (halpha0 : ∀ i, i ≤ r → 0 < alphaSeq i)
    (halpha1 : ∀ i, i ≤ r → alphaSeq i < 1)
    (halpha_half : ∀ i, i ≤ r → alphaSeq i ≤ 1 / 2)
    (hstep : ∀ i, i < r → alphaSeq i ≤ alphaSeq (i + 1))
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter_c : c.val = (reverseItem c).val)
    (hpivot_def :
      ∀ i, ∀ hi : i ≤ r,
        pivotSeq i =
          problem6FirstClosedPivot (alphaSeq i) v
            (halpha0 i hi) (halpha1 i hi) hpos)
    (hpivot_or_eq :
      ∀ i, i < r →
        pivotSeq i = pivotSeq (i + 1) ∨
        alphaSeq i = alphaSeq (i + 1)) :
    TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel (alphaSeq 0) v) ≤
      TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel (alphaSeq r) v) := by
  exact lemma8_reducedOptimalItemFairness_mono_of_same_firstClosedPivot_or_equal_alpha_chain
    r alphaSeq pivotSeq halpha0 halpha1 hstep hpos hdec hpivot_def
    hpivot_or_eq
    (fun i hi => by
      have hc :
          (problem6FirstClosedPivot (alphaSeq i) v
              (halpha0 i (Nat.le_of_lt hi))
              (halpha1 i (Nat.le_of_lt hi)) hpos).val ≤
            (reverseItem
              (problem6FirstClosedPivot (alphaSeq i) v
                (halpha0 i (Nat.le_of_lt hi))
                (halpha1 i (Nat.le_of_lt hi)) hpos)).val :=
        problem6FirstClosedPivot_le_reverse_of_alpha_le_half_center
          (halpha0 i (Nat.le_of_lt hi))
          (halpha1 i (Nat.le_of_lt hi))
          (halpha_half i (Nat.le_of_lt hi))
          hpos hcenter_c
      simpa [hpivot_def i (Nat.le_of_lt hi)] using hc)

/--
Appendix D, Lemma 8 canonical first-half finite-stitch core, even-center case.
-/
theorem lemma8_reducedOptimalItemFairness_mono_firstHalf_succ_center_firstClosedPivot_chain
    {n : ℕ} [NeZero n]
    {v : Item n → ℝ} {c : Item n}
    (r : ℕ)
    (alphaSeq : ℕ → ℝ)
    (pivotSeq : ℕ → Item n)
    (halpha0 : ∀ i, i ≤ r → 0 < alphaSeq i)
    (halpha1 : ∀ i, i ≤ r → alphaSeq i < 1)
    (halpha_half : ∀ i, i ≤ r → alphaSeq i ≤ 1 / 2)
    (hstep : ∀ i, i < r → alphaSeq i ≤ alphaSeq (i + 1))
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hsucc : c.val + 1 = (reverseItem c).val)
    (hpivot_def :
      ∀ i, ∀ hi : i ≤ r,
        pivotSeq i =
          problem6FirstClosedPivot (alphaSeq i) v
            (halpha0 i hi) (halpha1 i hi) hpos)
    (hpivot_or_eq :
      ∀ i, i < r →
        pivotSeq i = pivotSeq (i + 1) ∨
        alphaSeq i = alphaSeq (i + 1)) :
    TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel (alphaSeq 0) v) ≤
      TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel (alphaSeq r) v) := by
  exact lemma8_reducedOptimalItemFairness_mono_of_same_firstClosedPivot_or_equal_alpha_chain
    r alphaSeq pivotSeq halpha0 halpha1 hstep hpos hdec hpivot_def
    hpivot_or_eq
    (fun i hi => by
      have hc :
          (problem6FirstClosedPivot (alphaSeq i) v
              (halpha0 i (Nat.le_of_lt hi))
              (halpha1 i (Nat.le_of_lt hi)) hpos).val ≤
            (reverseItem
              (problem6FirstClosedPivot (alphaSeq i) v
                (halpha0 i (Nat.le_of_lt hi))
                (halpha1 i (Nat.le_of_lt hi)) hpos)).val :=
        problem6FirstClosedPivot_le_reverse_of_alpha_le_half_succ_center
          (halpha0 i (Nat.le_of_lt hi))
          (halpha1 i (Nat.le_of_lt hi))
          (halpha_half i (Nat.le_of_lt hi))
          hpos hsucc
      simpa [hpivot_def i (Nat.le_of_lt hi)] using hc)

/--
Appendix D, Lemma 8 finite-stitch core: if a finite sequence of selected
equality-form optimal BFS policies moves from `α₀` to `αᵣ`, and every adjacent
pair lies in one same-selected-pivot first-half interval, then the reduced
optimal item fairness is monotone along the whole chain.

This isolates the paper's interval-partition/continuity step from the already
formalized same-interval Lemma 11 inequality.
-/
theorem lemma8_reducedOptimalItemFairness_mono_of_same_selected_equalizedBasicOptimal_chain
    {n : ℕ} [NeZero n]
    {v : Item n → ℝ} (r : ℕ)
    (alphaSeq : ℕ → ℝ)
    (ρSeq : ℕ → TypePolicy 2 n)
    (ellSeq : ℕ → ℝ)
    (hn : 2 < n)
    (halpha0 : ∀ i, i ≤ r → 0 < alphaSeq i)
    (halpha1 : ∀ i, i ≤ r → alphaSeq i < 1)
    (hstep : ∀ i, i < r → alphaSeq i ≤ alphaSeq (i + 1))
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hpivot :
      ∀ i, i < r →
        TypePolicy.lastActiveTypeZero (ρSeq i) =
          TypePolicy.lastActiveTypeZero (ρSeq (i + 1)))
    (hcenter :
      ∀ i, i < r →
        (TypePolicy.lastActiveTypeZero (ρSeq i)).val ≤
          (reverseItem (TypePolicy.lastActiveTypeZero (ρSeq i))).val)
    (hopt :
      ∀ i, i ≤ r →
        Problem6EqualizedBasicOptimal (alphaSeq i) v (ρSeq i) (ellSeq i)) :
    TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel (alphaSeq 0) v) ≤
      TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel (alphaSeq r) v) := by
  induction r with
  | zero =>
      exact le_rfl
  | succ r ih =>
      have hprev :
          TypeWeightedRecommendationModel.optimalItemFairness
              (twoTypeReducedModel (alphaSeq 0) v) ≤
            TypeWeightedRecommendationModel.optimalItemFairness
              (twoTypeReducedModel (alphaSeq r) v) := by
        exact ih
          (fun i hi => halpha0 i (Nat.le_trans hi (Nat.le_succ r)))
          (fun i hi => halpha1 i (Nat.le_trans hi (Nat.le_succ r)))
          (fun i hi => hstep i (Nat.lt_trans hi (Nat.lt_succ_self r)))
          (fun i hi => hpivot i (Nat.lt_trans hi (Nat.lt_succ_self r)))
          (fun i hi => hcenter i (Nat.lt_trans hi (Nat.lt_succ_self r)))
          (fun i hi => hopt i (Nat.le_trans hi (Nat.le_succ r)))
      have hlast :
          TypeWeightedRecommendationModel.optimalItemFairness
              (twoTypeReducedModel (alphaSeq r) v) ≤
            TypeWeightedRecommendationModel.optimalItemFairness
              (twoTypeReducedModel (alphaSeq (r + 1)) v) := by
        exact
          lemma11_reducedOptimalItemFairness_mono_of_same_selected_equalizedBasicOptimal
            hn
            (halpha0 r (Nat.le_succ r))
            (halpha1 r (Nat.le_succ r))
            (halpha0 (r + 1) le_rfl)
            (halpha1 (r + 1) le_rfl)
            (hstep r (Nat.lt_succ_self r))
            hpos hdec
            (hpivot r (Nat.lt_succ_self r))
            (hcenter r (Nat.lt_succ_self r))
            (hopt r (Nat.le_succ r))
            (hopt (r + 1) le_rfl)
      exact hprev.trans hlast

/--
Appendix D, Lemma 8 finite-stitch core with explicit boundary repeats: a
finite chain may either stay inside one same-selected-pivot interval, where
Lemma 11 applies, or repeat the same `α` at an interval boundary, where the
optimal value is identical by reflexivity.

This is the formal finite skeleton of the paper's continuity stitch across the
consecutive `A(t)` partition.
-/
theorem lemma8_reducedOptimalItemFairness_mono_of_same_selected_or_equal_alpha_chain
    {n : ℕ} [NeZero n]
    {v : Item n → ℝ} (r : ℕ)
    (alphaSeq : ℕ → ℝ)
    (ρSeq : ℕ → TypePolicy 2 n)
    (ellSeq : ℕ → ℝ)
    (hn : 2 < n)
    (halpha0 : ∀ i, i ≤ r → 0 < alphaSeq i)
    (halpha1 : ∀ i, i ≤ r → alphaSeq i < 1)
    (hstep : ∀ i, i < r → alphaSeq i ≤ alphaSeq (i + 1))
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hpivot_or_eq :
      ∀ i, i < r →
        TypePolicy.lastActiveTypeZero (ρSeq i) =
          TypePolicy.lastActiveTypeZero (ρSeq (i + 1)) ∨
        alphaSeq i = alphaSeq (i + 1))
    (hcenter :
      ∀ i, i < r →
        (TypePolicy.lastActiveTypeZero (ρSeq i)).val ≤
          (reverseItem (TypePolicy.lastActiveTypeZero (ρSeq i))).val)
    (hopt :
      ∀ i, i ≤ r →
        Problem6EqualizedBasicOptimal (alphaSeq i) v (ρSeq i) (ellSeq i)) :
    TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel (alphaSeq 0) v) ≤
      TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel (alphaSeq r) v) := by
  induction r with
  | zero =>
      exact le_rfl
  | succ r ih =>
      have hprev :
          TypeWeightedRecommendationModel.optimalItemFairness
              (twoTypeReducedModel (alphaSeq 0) v) ≤
            TypeWeightedRecommendationModel.optimalItemFairness
              (twoTypeReducedModel (alphaSeq r) v) := by
        exact ih
          (fun i hi => halpha0 i (Nat.le_trans hi (Nat.le_succ r)))
          (fun i hi => halpha1 i (Nat.le_trans hi (Nat.le_succ r)))
          (fun i hi => hstep i (Nat.lt_trans hi (Nat.lt_succ_self r)))
          (fun i hi => hpivot_or_eq i (Nat.lt_trans hi (Nat.lt_succ_self r)))
          (fun i hi => hcenter i (Nat.lt_trans hi (Nat.lt_succ_self r)))
          (fun i hi => hopt i (Nat.le_trans hi (Nat.le_succ r)))
      have hlast :
          TypeWeightedRecommendationModel.optimalItemFairness
              (twoTypeReducedModel (alphaSeq r) v) ≤
            TypeWeightedRecommendationModel.optimalItemFairness
              (twoTypeReducedModel (alphaSeq (r + 1)) v) := by
        rcases hpivot_or_eq r (Nat.lt_succ_self r) with hpivot | halpha_eq
        · exact
            lemma11_reducedOptimalItemFairness_mono_of_same_selected_equalizedBasicOptimal
              hn
              (halpha0 r (Nat.le_succ r))
              (halpha1 r (Nat.le_succ r))
              (halpha0 (r + 1) le_rfl)
              (halpha1 (r + 1) le_rfl)
              (hstep r (Nat.lt_succ_self r))
              hpos hdec
              hpivot
              (hcenter r (Nat.lt_succ_self r))
              (hopt r (Nat.le_succ r))
              (hopt (r + 1) le_rfl)
        · simpa [halpha_eq] using
            (le_rfl :
              TypeWeightedRecommendationModel.optimalItemFairness
                (twoTypeReducedModel (alphaSeq r) v) ≤
              TypeWeightedRecommendationModel.optimalItemFairness
                (twoTypeReducedModel (alphaSeq r) v))
      exact hprev.trans hlast

/--
Appendix D, Lemma 8 finite-stitch core, odd-center case: along a first-half
finite chain, Lemma 10 supplies the pivot-before-mirror side condition needed
by Lemma 11 on every non-boundary step.
-/
theorem lemma8_reducedOptimalItemFairness_mono_firstHalf_center_chain
    {n : ℕ} [NeZero n]
    {v : Item n → ℝ} {c : Item n}
    (r : ℕ)
    (alphaSeq : ℕ → ℝ)
    (ρSeq : ℕ → TypePolicy 2 n)
    (ellSeq : ℕ → ℝ)
    {ρhalf : TypePolicy 2 n} {ellHalf : ℝ}
    (hn : 2 < n)
    (halpha0 : ∀ i, i ≤ r → 0 < alphaSeq i)
    (halpha1 : ∀ i, i ≤ r → alphaSeq i < 1)
    (halpha_half : ∀ i, i ≤ r → alphaSeq i ≤ 1 / 2)
    (hstep : ∀ i, i < r → alphaSeq i ≤ alphaSeq (i + 1))
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter_c : c.val = (reverseItem c).val)
    (hpivot_or_eq :
      ∀ i, i < r →
        TypePolicy.lastActiveTypeZero (ρSeq i) =
          TypePolicy.lastActiveTypeZero (ρSeq (i + 1)) ∨
        alphaSeq i = alphaSeq (i + 1))
    (hopt :
      ∀ i, i ≤ r →
        Problem6EqualizedBasicOptimal (alphaSeq i) v (ρSeq i) (ellSeq i))
    (hhalf :
      Problem6EqualizedBasicOptimal (1 / 2) v ρhalf ellHalf) :
    TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel (alphaSeq 0) v) ≤
      TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel (alphaSeq r) v) := by
  exact lemma8_reducedOptimalItemFairness_mono_of_same_selected_or_equal_alpha_chain
    r alphaSeq ρSeq ellSeq hn halpha0 halpha1 hstep hpos hdec hpivot_or_eq
    (fun i hi =>
      lemma10_alpha_le_half_equalizedBasicOptimal_lastActive_le_reverse_center
        hn (halpha0 i (Nat.le_trans (Nat.le_of_lt hi) (Nat.le_refl r)))
        (halpha1 i (Nat.le_trans (Nat.le_of_lt hi) (Nat.le_refl r)))
        (halpha_half i (Nat.le_trans (Nat.le_of_lt hi) (Nat.le_refl r)))
        hpos hdec hcenter_c
        (hopt i (Nat.le_trans (Nat.le_of_lt hi) (Nat.le_refl r)))
        hhalf)
    hopt

/--
Appendix D, Lemma 8 finite-stitch core, even-center case: along a first-half
finite chain, Lemma 10 supplies the pivot-before-mirror side condition needed
by Lemma 11 on every non-boundary step.
-/
theorem lemma8_reducedOptimalItemFairness_mono_firstHalf_succ_center_chain
    {n : ℕ} [NeZero n]
    {v : Item n → ℝ} {c : Item n}
    (r : ℕ)
    (alphaSeq : ℕ → ℝ)
    (ρSeq : ℕ → TypePolicy 2 n)
    (ellSeq : ℕ → ℝ)
    {ρhalf : TypePolicy 2 n} {ellHalf : ℝ}
    (hn : 2 < n)
    (halpha0 : ∀ i, i ≤ r → 0 < alphaSeq i)
    (halpha1 : ∀ i, i ≤ r → alphaSeq i < 1)
    (halpha_half : ∀ i, i ≤ r → alphaSeq i ≤ 1 / 2)
    (hstep : ∀ i, i < r → alphaSeq i ≤ alphaSeq (i + 1))
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hsucc : c.val + 1 = (reverseItem c).val)
    (hpivot_or_eq :
      ∀ i, i < r →
        TypePolicy.lastActiveTypeZero (ρSeq i) =
          TypePolicy.lastActiveTypeZero (ρSeq (i + 1)) ∨
        alphaSeq i = alphaSeq (i + 1))
    (hopt :
      ∀ i, i ≤ r →
        Problem6EqualizedBasicOptimal (alphaSeq i) v (ρSeq i) (ellSeq i))
    (hhalf :
      Problem6EqualizedBasicOptimal (1 / 2) v ρhalf ellHalf) :
    TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel (alphaSeq 0) v) ≤
      TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel (alphaSeq r) v) := by
  exact lemma8_reducedOptimalItemFairness_mono_of_same_selected_or_equal_alpha_chain
    r alphaSeq ρSeq ellSeq hn halpha0 halpha1 hstep hpos hdec hpivot_or_eq
    (fun i hi =>
      lemma10_alpha_le_half_equalizedBasicOptimal_lastActive_le_reverse_succ_center
        hn (halpha0 i (Nat.le_trans (Nat.le_of_lt hi) (Nat.le_refl r)))
        (halpha1 i (Nat.le_trans (Nat.le_of_lt hi) (Nat.le_refl r)))
        (halpha_half i (Nat.le_trans (Nat.le_of_lt hi) (Nat.le_refl r)))
        hpos hdec hsucc
        (hopt i (Nat.le_trans (Nat.le_of_lt hi) (Nat.le_refl r)))
        hhalf)
    hopt

/--
Appendix D, Lemma 8 finite-stitch core, odd-center case, using the Lemma 5
closed midpoint optimum internally to discharge the first-half side condition.
-/
theorem lemma8_reducedOptimalItemFairness_mono_firstHalf_center_chain_of_closed_half
    {n : ℕ} [NeZero n]
    {v : Item n → ℝ} {c : Item n}
    (r : ℕ)
    (alphaSeq : ℕ → ℝ)
    (ρSeq : ℕ → TypePolicy 2 n)
    (ellSeq : ℕ → ℝ)
    (hn : 2 < n)
    (halpha0 : ∀ i, i ≤ r → 0 < alphaSeq i)
    (halpha1 : ∀ i, i ≤ r → alphaSeq i < 1)
    (halpha_half : ∀ i, i ≤ r → alphaSeq i ≤ 1 / 2)
    (hstep : ∀ i, i < r → alphaSeq i ≤ alphaSeq (i + 1))
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter_c : c.val = (reverseItem c).val)
    (hpivot_or_eq :
      ∀ i, i < r →
        TypePolicy.lastActiveTypeZero (ρSeq i) =
          TypePolicy.lastActiveTypeZero (ρSeq (i + 1)) ∨
        alphaSeq i = alphaSeq (i + 1))
    (hopt :
      ∀ i, i ≤ r →
        Problem6EqualizedBasicOptimal (alphaSeq i) v (ρSeq i) (ellSeq i)) :
    TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel (alphaSeq 0) v) ≤
      TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel (alphaSeq r) v) := by
  exact lemma8_reducedOptimalItemFairness_mono_of_same_selected_or_equal_alpha_chain
    r alphaSeq ρSeq ellSeq hn halpha0 halpha1 hstep hpos hdec hpivot_or_eq
    (fun i hi =>
      lemma10_alpha_le_half_equalizedBasicOptimal_lastActive_le_reverse_center_of_closed_half
        hn (halpha0 i (Nat.le_of_lt hi))
        (halpha1 i (Nat.le_of_lt hi))
        (halpha_half i (Nat.le_of_lt hi))
        hpos hdec hcenter_c (hopt i (Nat.le_of_lt hi)))
    hopt

/--
Appendix D, Lemma 8 finite-stitch core, even-center case, using the Lemma 5
closed midpoint optimum internally to discharge the first-half side condition.
-/
theorem lemma8_reducedOptimalItemFairness_mono_firstHalf_succ_center_chain_of_closed_half
    {n : ℕ} [NeZero n]
    {v : Item n → ℝ} {c : Item n}
    (r : ℕ)
    (alphaSeq : ℕ → ℝ)
    (ρSeq : ℕ → TypePolicy 2 n)
    (ellSeq : ℕ → ℝ)
    (hn : 2 < n)
    (halpha0 : ∀ i, i ≤ r → 0 < alphaSeq i)
    (halpha1 : ∀ i, i ≤ r → alphaSeq i < 1)
    (halpha_half : ∀ i, i ≤ r → alphaSeq i ≤ 1 / 2)
    (hstep : ∀ i, i < r → alphaSeq i ≤ alphaSeq (i + 1))
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hsucc : c.val + 1 = (reverseItem c).val)
    (hpivot_or_eq :
      ∀ i, i < r →
        TypePolicy.lastActiveTypeZero (ρSeq i) =
          TypePolicy.lastActiveTypeZero (ρSeq (i + 1)) ∨
        alphaSeq i = alphaSeq (i + 1))
    (hopt :
      ∀ i, i ≤ r →
        Problem6EqualizedBasicOptimal (alphaSeq i) v (ρSeq i) (ellSeq i)) :
    TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel (alphaSeq 0) v) ≤
      TypeWeightedRecommendationModel.optimalItemFairness
        (twoTypeReducedModel (alphaSeq r) v) := by
  exact lemma8_reducedOptimalItemFairness_mono_of_same_selected_or_equal_alpha_chain
    r alphaSeq ρSeq ellSeq hn halpha0 halpha1 hstep hpos hdec hpivot_or_eq
    (fun i hi =>
      lemma10_alpha_le_half_equalizedBasicOptimal_lastActive_le_reverse_succ_center_of_closed_half
        hn (halpha0 i (Nat.le_of_lt hi))
        (halpha1 i (Nat.le_of_lt hi))
        (halpha_half i (Nat.le_of_lt hi))
        hpos hdec hsucc (hopt i (Nat.le_of_lt hi)))
    hopt

/--
Theorem 3 bridge to the reduced `U^*_min(1, α)` objective: if every selected
equality-form optimal BFS policy in the finite chain also upper-bounds all
`γ = 1` feasible policies in type fairness, then the reduced optimal
type-fairness value is monotone along that chain.
-/
theorem theorem3_optimalTypeFairnessAtLevel_one_mono_of_same_selected_or_equal_alpha_chain_of_upper_bound
    {n : ℕ} [NeZero n]
    {v : Item n → ℝ} (r : ℕ)
    (alphaSeq : ℕ → ℝ)
    (ρSeq : ℕ → TypePolicy 2 n)
    (ellSeq : ℕ → ℝ)
    (hn : 2 < n)
    (halpha0 : ∀ i, i ≤ r → 0 < alphaSeq i)
    (halpha1 : ∀ i, i ≤ r → alphaSeq i < 1)
    (halpha_half : ∀ i, i ≤ r → alphaSeq i ≤ 1 / 2)
    (hstep : ∀ i, i < r → alphaSeq i ≤ alphaSeq (i + 1))
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hpivot_or_eq :
      ∀ i, i < r →
        TypePolicy.lastActiveTypeZero (ρSeq i) =
          TypePolicy.lastActiveTypeZero (ρSeq (i + 1)) ∨
        alphaSeq i = alphaSeq (i + 1))
    (hcenter :
      ∀ i, i < r →
        (TypePolicy.lastActiveTypeZero (ρSeq i)).val ≤
          (reverseItem (TypePolicy.lastActiveTypeZero (ρSeq i))).val)
    (hopt :
      ∀ i, i ≤ r →
        Problem6EqualizedBasicOptimal (alphaSeq i) v (ρSeq i) (ellSeq i))
    (hupper :
      ∀ i, i ≤ r →
        ∀ ρ' : TypePolicy 2 n,
          TypeWeightedRecommendationModel.feasibleAtLevel
            (twoTypeReducedModel (alphaSeq i) v) 1 ρ' →
          TypeWeightedRecommendationModel.typeFairness
            (twoTypeReducedModel (alphaSeq i) v) ρ' ≤
          TypeWeightedRecommendationModel.typeFairness
            (twoTypeReducedModel (alphaSeq i) v) (ρSeq i)) :
    TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel (alphaSeq 0) v) 1 ≤
      TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel (alphaSeq r) v) 1 := by
  have hleft :
      TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
          (twoTypeReducedModel (alphaSeq 0) v) 1 =
        TypeWeightedRecommendationModel.typeFairness
          (twoTypeReducedModel (alphaSeq 0) v) (ρSeq 0) :=
    problem6EqualizedBasicOptimal_optimalTypeFairnessAtLevel_one_eq_of_upper_bound
      (halpha0 0 (Nat.zero_le r))
      (halpha1 0 (Nat.zero_le r))
      hpos
      (hopt 0 (Nat.zero_le r))
      (hupper 0 (Nat.zero_le r))
  have hright :
      TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
          (twoTypeReducedModel (alphaSeq r) v) 1 =
        TypeWeightedRecommendationModel.typeFairness
          (twoTypeReducedModel (alphaSeq r) v) (ρSeq r) :=
    problem6EqualizedBasicOptimal_optimalTypeFairnessAtLevel_one_eq_of_upper_bound
      (halpha0 r le_rfl)
      (halpha1 r le_rfl)
      hpos
      (hopt r le_rfl)
      (hupper r le_rfl)
  rw [hleft, hright]
  exact theorem3_typeFairness_mono_of_same_selected_or_equal_alpha_chain
    r alphaSeq ρSeq ellSeq hn halpha0 halpha1 halpha_half hstep
    hpos hdec hpivot_or_eq hcenter hopt

/--
Theorem 3 bridge to reduced `U^*_min(1, α)`, odd-center first-half chain:
Lemma 10 supplies the first-half pivot condition, while the supplied upper
bound identifies each selected policy with the reduced `γ = 1` type-fairness
optimum.
-/
theorem theorem3_optimalTypeFairnessAtLevel_one_mono_firstHalf_center_chain_of_upper_bound
    {n : ℕ} [NeZero n]
    {v : Item n → ℝ} {c : Item n}
    (r : ℕ)
    (alphaSeq : ℕ → ℝ)
    (ρSeq : ℕ → TypePolicy 2 n)
    (ellSeq : ℕ → ℝ)
    {ρhalf : TypePolicy 2 n} {ellHalf : ℝ}
    (hn : 2 < n)
    (halpha0 : ∀ i, i ≤ r → 0 < alphaSeq i)
    (halpha1 : ∀ i, i ≤ r → alphaSeq i < 1)
    (halpha_half : ∀ i, i ≤ r → alphaSeq i ≤ 1 / 2)
    (hstep : ∀ i, i < r → alphaSeq i ≤ alphaSeq (i + 1))
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter_c : c.val = (reverseItem c).val)
    (hpivot_or_eq :
      ∀ i, i < r →
        TypePolicy.lastActiveTypeZero (ρSeq i) =
          TypePolicy.lastActiveTypeZero (ρSeq (i + 1)) ∨
        alphaSeq i = alphaSeq (i + 1))
    (hopt :
      ∀ i, i ≤ r →
        Problem6EqualizedBasicOptimal (alphaSeq i) v (ρSeq i) (ellSeq i))
    (hhalf :
      Problem6EqualizedBasicOptimal (1 / 2) v ρhalf ellHalf)
    (hupper :
      ∀ i, i ≤ r →
        ∀ ρ' : TypePolicy 2 n,
          TypeWeightedRecommendationModel.feasibleAtLevel
            (twoTypeReducedModel (alphaSeq i) v) 1 ρ' →
          TypeWeightedRecommendationModel.typeFairness
            (twoTypeReducedModel (alphaSeq i) v) ρ' ≤
          TypeWeightedRecommendationModel.typeFairness
            (twoTypeReducedModel (alphaSeq i) v) (ρSeq i)) :
    TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel (alphaSeq 0) v) 1 ≤
      TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel (alphaSeq r) v) 1 := by
  exact
    theorem3_optimalTypeFairnessAtLevel_one_mono_of_same_selected_or_equal_alpha_chain_of_upper_bound
      r alphaSeq ρSeq ellSeq hn halpha0 halpha1 halpha_half hstep
      hpos hdec hpivot_or_eq
      (fun i hi =>
        lemma10_alpha_le_half_equalizedBasicOptimal_lastActive_le_reverse_center
          hn (halpha0 i (Nat.le_of_lt hi))
          (halpha1 i (Nat.le_of_lt hi))
          (halpha_half i (Nat.le_of_lt hi))
          hpos hdec hcenter_c (hopt i (Nat.le_of_lt hi)) hhalf)
      hopt hupper

/--
Theorem 3 bridge to reduced `U^*_min(1, α)`, even-center first-half chain.
-/
theorem theorem3_optimalTypeFairnessAtLevel_one_mono_firstHalf_succ_center_chain_of_upper_bound
    {n : ℕ} [NeZero n]
    {v : Item n → ℝ} {c : Item n}
    (r : ℕ)
    (alphaSeq : ℕ → ℝ)
    (ρSeq : ℕ → TypePolicy 2 n)
    (ellSeq : ℕ → ℝ)
    {ρhalf : TypePolicy 2 n} {ellHalf : ℝ}
    (hn : 2 < n)
    (halpha0 : ∀ i, i ≤ r → 0 < alphaSeq i)
    (halpha1 : ∀ i, i ≤ r → alphaSeq i < 1)
    (halpha_half : ∀ i, i ≤ r → alphaSeq i ≤ 1 / 2)
    (hstep : ∀ i, i < r → alphaSeq i ≤ alphaSeq (i + 1))
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hsucc : c.val + 1 = (reverseItem c).val)
    (hpivot_or_eq :
      ∀ i, i < r →
        TypePolicy.lastActiveTypeZero (ρSeq i) =
          TypePolicy.lastActiveTypeZero (ρSeq (i + 1)) ∨
        alphaSeq i = alphaSeq (i + 1))
    (hopt :
      ∀ i, i ≤ r →
        Problem6EqualizedBasicOptimal (alphaSeq i) v (ρSeq i) (ellSeq i))
    (hhalf :
      Problem6EqualizedBasicOptimal (1 / 2) v ρhalf ellHalf)
    (hupper :
      ∀ i, i ≤ r →
        ∀ ρ' : TypePolicy 2 n,
          TypeWeightedRecommendationModel.feasibleAtLevel
            (twoTypeReducedModel (alphaSeq i) v) 1 ρ' →
          TypeWeightedRecommendationModel.typeFairness
            (twoTypeReducedModel (alphaSeq i) v) ρ' ≤
          TypeWeightedRecommendationModel.typeFairness
            (twoTypeReducedModel (alphaSeq i) v) (ρSeq i)) :
    TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel (alphaSeq 0) v) 1 ≤
      TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel (alphaSeq r) v) 1 := by
  exact
    theorem3_optimalTypeFairnessAtLevel_one_mono_of_same_selected_or_equal_alpha_chain_of_upper_bound
      r alphaSeq ρSeq ellSeq hn halpha0 halpha1 halpha_half hstep
      hpos hdec hpivot_or_eq
      (fun i hi =>
        lemma10_alpha_le_half_equalizedBasicOptimal_lastActive_le_reverse_succ_center
          hn (halpha0 i (Nat.le_of_lt hi))
          (halpha1 i (Nat.le_of_lt hi))
          (halpha_half i (Nat.le_of_lt hi))
          hpos hdec hsucc (hopt i (Nat.le_of_lt hi)) hhalf)
      hopt hupper

/--
Theorem 3 bridge to reduced `U^*_min(1, α)`, odd-center first-half chain,
using the Lemma 5 closed midpoint optimum internally.
-/
theorem theorem3_optimalTypeFairnessAtLevel_one_mono_firstHalf_center_chain_of_upper_bound_closed_half
    {n : ℕ} [NeZero n]
    {v : Item n → ℝ} {c : Item n}
    (r : ℕ)
    (alphaSeq : ℕ → ℝ)
    (ρSeq : ℕ → TypePolicy 2 n)
    (ellSeq : ℕ → ℝ)
    (hn : 2 < n)
    (halpha0 : ∀ i, i ≤ r → 0 < alphaSeq i)
    (halpha1 : ∀ i, i ≤ r → alphaSeq i < 1)
    (halpha_half : ∀ i, i ≤ r → alphaSeq i ≤ 1 / 2)
    (hstep : ∀ i, i < r → alphaSeq i ≤ alphaSeq (i + 1))
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter_c : c.val = (reverseItem c).val)
    (hpivot_or_eq :
      ∀ i, i < r →
        TypePolicy.lastActiveTypeZero (ρSeq i) =
          TypePolicy.lastActiveTypeZero (ρSeq (i + 1)) ∨
        alphaSeq i = alphaSeq (i + 1))
    (hopt :
      ∀ i, i ≤ r →
        Problem6EqualizedBasicOptimal (alphaSeq i) v (ρSeq i) (ellSeq i))
    (hupper :
      ∀ i, i ≤ r →
        ∀ ρ' : TypePolicy 2 n,
          TypeWeightedRecommendationModel.feasibleAtLevel
            (twoTypeReducedModel (alphaSeq i) v) 1 ρ' →
          TypeWeightedRecommendationModel.typeFairness
            (twoTypeReducedModel (alphaSeq i) v) ρ' ≤
          TypeWeightedRecommendationModel.typeFairness
            (twoTypeReducedModel (alphaSeq i) v) (ρSeq i)) :
    TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel (alphaSeq 0) v) 1 ≤
      TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel (alphaSeq r) v) 1 := by
  exact
    theorem3_optimalTypeFairnessAtLevel_one_mono_of_same_selected_or_equal_alpha_chain_of_upper_bound
      r alphaSeq ρSeq ellSeq hn halpha0 halpha1 halpha_half hstep
      hpos hdec hpivot_or_eq
      (fun i hi =>
        lemma10_alpha_le_half_equalizedBasicOptimal_lastActive_le_reverse_center_of_closed_half
          hn (halpha0 i (Nat.le_of_lt hi))
          (halpha1 i (Nat.le_of_lt hi))
          (halpha_half i (Nat.le_of_lt hi))
          hpos hdec hcenter_c (hopt i (Nat.le_of_lt hi)))
      hopt hupper

/--
Theorem 3 bridge to reduced `U^*_min(1, α)`, even-center first-half chain,
using the Lemma 5 closed midpoint optimum internally.
-/
theorem theorem3_optimalTypeFairnessAtLevel_one_mono_firstHalf_succ_center_chain_of_upper_bound_closed_half
    {n : ℕ} [NeZero n]
    {v : Item n → ℝ} {c : Item n}
    (r : ℕ)
    (alphaSeq : ℕ → ℝ)
    (ρSeq : ℕ → TypePolicy 2 n)
    (ellSeq : ℕ → ℝ)
    (hn : 2 < n)
    (halpha0 : ∀ i, i ≤ r → 0 < alphaSeq i)
    (halpha1 : ∀ i, i ≤ r → alphaSeq i < 1)
    (halpha_half : ∀ i, i ≤ r → alphaSeq i ≤ 1 / 2)
    (hstep : ∀ i, i < r → alphaSeq i ≤ alphaSeq (i + 1))
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hsucc : c.val + 1 = (reverseItem c).val)
    (hpivot_or_eq :
      ∀ i, i < r →
        TypePolicy.lastActiveTypeZero (ρSeq i) =
          TypePolicy.lastActiveTypeZero (ρSeq (i + 1)) ∨
        alphaSeq i = alphaSeq (i + 1))
    (hopt :
      ∀ i, i ≤ r →
        Problem6EqualizedBasicOptimal (alphaSeq i) v (ρSeq i) (ellSeq i))
    (hupper :
      ∀ i, i ≤ r →
        ∀ ρ' : TypePolicy 2 n,
          TypeWeightedRecommendationModel.feasibleAtLevel
            (twoTypeReducedModel (alphaSeq i) v) 1 ρ' →
          TypeWeightedRecommendationModel.typeFairness
            (twoTypeReducedModel (alphaSeq i) v) ρ' ≤
          TypeWeightedRecommendationModel.typeFairness
            (twoTypeReducedModel (alphaSeq i) v) (ρSeq i)) :
    TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel (alphaSeq 0) v) 1 ≤
      TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel (alphaSeq r) v) 1 := by
  exact
    theorem3_optimalTypeFairnessAtLevel_one_mono_of_same_selected_or_equal_alpha_chain_of_upper_bound
      r alphaSeq ρSeq ellSeq hn halpha0 halpha1 halpha_half hstep
      hpos hdec hpivot_or_eq
      (fun i hi =>
        lemma10_alpha_le_half_equalizedBasicOptimal_lastActive_le_reverse_succ_center_of_closed_half
          hn (halpha0 i (Nat.le_of_lt hi))
          (halpha1 i (Nat.le_of_lt hi))
          (halpha_half i (Nat.le_of_lt hi))
          hpos hdec hsucc (hopt i (Nat.le_of_lt hi)))
      hopt hupper

/--
Theorem 3 bridge to the reduced `U^*_min(1, α)` objective using the
Proposition-1-shaped canonicalization step: along a first-half finite chain,
if every reduced `γ = 1` feasible policy has an equalized/shared canonical
representative with weakly larger type fairness, then the reduced optimal
type-fairness value is monotone along the chain.
-/
theorem theorem3_optimalTypeFairnessAtLevel_one_mono_of_same_selected_or_equal_alpha_chain_of_feasible_canonicalization
    {n : ℕ} [NeZero n]
    {v : Item n → ℝ} (r : ℕ)
    (alphaSeq : ℕ → ℝ)
    (ρSeq : ℕ → TypePolicy 2 n)
    (ellSeq : ℕ → ℝ)
    (hn : 2 < n)
    (halpha0 : ∀ i, i ≤ r → 0 < alphaSeq i)
    (halpha1 : ∀ i, i ≤ r → alphaSeq i < 1)
    (halpha_half : ∀ i, i ≤ r → alphaSeq i ≤ 1 / 2)
    (hstep : ∀ i, i < r → alphaSeq i ≤ alphaSeq (i + 1))
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hpivot_or_eq :
      ∀ i, i < r →
        TypePolicy.lastActiveTypeZero (ρSeq i) =
          TypePolicy.lastActiveTypeZero (ρSeq (i + 1)) ∨
        alphaSeq i = alphaSeq (i + 1))
    (hcenter :
      ∀ i, i < r →
        (TypePolicy.lastActiveTypeZero (ρSeq i)).val ≤
          (reverseItem (TypePolicy.lastActiveTypeZero (ρSeq i))).val)
    (hopt :
      ∀ i, i ≤ r →
        Problem6EqualizedBasicOptimal (alphaSeq i) v (ρSeq i) (ellSeq i))
    (hcanonical :
      ∀ i, i ≤ r →
        ∀ ρ' : TypePolicy 2 n,
          TypeWeightedRecommendationModel.feasibleAtLevel
            (twoTypeReducedModel (alphaSeq i) v) 1 ρ' →
          ∃ ρbar : TypePolicy 2 n,
            TypeWeightedRecommendationModel.feasibleAtLevel
              (twoTypeReducedModel (alphaSeq i) v) 1 ρbar ∧
            (∀ l : Item n,
              pairShare (alphaSeq i) v l * (ρbar 0 l).toReal +
                (1 - pairShare (alphaSeq i) v l) * (ρbar 1 l).toReal =
              TypeWeightedRecommendationModel.itemFairness
                (twoTypeReducedModel (alphaSeq i) v) ρbar) ∧
            TypePolicy.SharedItemsBound ρbar ∧
            TypeWeightedRecommendationModel.typeFairness
              (twoTypeReducedModel (alphaSeq i) v) ρ' ≤
            TypeWeightedRecommendationModel.typeFairness
              (twoTypeReducedModel (alphaSeq i) v) ρbar) :
    TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel (alphaSeq 0) v) 1 ≤
      TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel (alphaSeq r) v) 1 := by
  have hleft :
      TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
          (twoTypeReducedModel (alphaSeq 0) v) 1 =
        TypeWeightedRecommendationModel.typeFairness
          (twoTypeReducedModel (alphaSeq 0) v) (ρSeq 0) :=
    problem6EqualizedBasicOptimal_optimalTypeFairnessAtLevel_one_eq_of_feasible_canonicalization
      hn
      (halpha0 0 (Nat.zero_le r))
      (halpha1 0 (Nat.zero_le r))
      hpos hdec
      (hopt 0 (Nat.zero_le r))
      (hcanonical 0 (Nat.zero_le r))
  have hright :
      TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
          (twoTypeReducedModel (alphaSeq r) v) 1 =
        TypeWeightedRecommendationModel.typeFairness
          (twoTypeReducedModel (alphaSeq r) v) (ρSeq r) :=
    problem6EqualizedBasicOptimal_optimalTypeFairnessAtLevel_one_eq_of_feasible_canonicalization
      hn
      (halpha0 r le_rfl)
      (halpha1 r le_rfl)
      hpos hdec
      (hopt r le_rfl)
      (hcanonical r le_rfl)
  rw [hleft, hright]
  exact theorem3_typeFairness_mono_of_same_selected_or_equal_alpha_chain
    r alphaSeq ρSeq ellSeq hn halpha0 halpha1 halpha_half hstep
    hpos hdec hpivot_or_eq hcenter hopt

/--
Theorem 3 reduced-optimum bridge, odd-center first-half chain, with the
Proposition-1-shaped feasible-policy canonicalization assumption.
-/
theorem theorem3_optimalTypeFairnessAtLevel_one_mono_firstHalf_center_chain_of_feasible_canonicalization
    {n : ℕ} [NeZero n]
    {v : Item n → ℝ} {c : Item n}
    (r : ℕ)
    (alphaSeq : ℕ → ℝ)
    (ρSeq : ℕ → TypePolicy 2 n)
    (ellSeq : ℕ → ℝ)
    {ρhalf : TypePolicy 2 n} {ellHalf : ℝ}
    (hn : 2 < n)
    (halpha0 : ∀ i, i ≤ r → 0 < alphaSeq i)
    (halpha1 : ∀ i, i ≤ r → alphaSeq i < 1)
    (halpha_half : ∀ i, i ≤ r → alphaSeq i ≤ 1 / 2)
    (hstep : ∀ i, i < r → alphaSeq i ≤ alphaSeq (i + 1))
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter_c : c.val = (reverseItem c).val)
    (hpivot_or_eq :
      ∀ i, i < r →
        TypePolicy.lastActiveTypeZero (ρSeq i) =
          TypePolicy.lastActiveTypeZero (ρSeq (i + 1)) ∨
        alphaSeq i = alphaSeq (i + 1))
    (hopt :
      ∀ i, i ≤ r →
        Problem6EqualizedBasicOptimal (alphaSeq i) v (ρSeq i) (ellSeq i))
    (hhalf :
      Problem6EqualizedBasicOptimal (1 / 2) v ρhalf ellHalf)
    (hcanonical :
      ∀ i, i ≤ r →
        ∀ ρ' : TypePolicy 2 n,
          TypeWeightedRecommendationModel.feasibleAtLevel
            (twoTypeReducedModel (alphaSeq i) v) 1 ρ' →
          ∃ ρbar : TypePolicy 2 n,
            TypeWeightedRecommendationModel.feasibleAtLevel
              (twoTypeReducedModel (alphaSeq i) v) 1 ρbar ∧
            (∀ l : Item n,
              pairShare (alphaSeq i) v l * (ρbar 0 l).toReal +
                (1 - pairShare (alphaSeq i) v l) * (ρbar 1 l).toReal =
              TypeWeightedRecommendationModel.itemFairness
                (twoTypeReducedModel (alphaSeq i) v) ρbar) ∧
            TypePolicy.SharedItemsBound ρbar ∧
            TypeWeightedRecommendationModel.typeFairness
              (twoTypeReducedModel (alphaSeq i) v) ρ' ≤
            TypeWeightedRecommendationModel.typeFairness
              (twoTypeReducedModel (alphaSeq i) v) ρbar) :
    TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel (alphaSeq 0) v) 1 ≤
      TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel (alphaSeq r) v) 1 := by
  exact
    theorem3_optimalTypeFairnessAtLevel_one_mono_of_same_selected_or_equal_alpha_chain_of_feasible_canonicalization
      r alphaSeq ρSeq ellSeq hn halpha0 halpha1 halpha_half hstep
      hpos hdec hpivot_or_eq
      (fun i hi =>
        lemma10_alpha_le_half_equalizedBasicOptimal_lastActive_le_reverse_center
          hn (halpha0 i (Nat.le_of_lt hi))
          (halpha1 i (Nat.le_of_lt hi))
          (halpha_half i (Nat.le_of_lt hi))
          hpos hdec hcenter_c (hopt i (Nat.le_of_lt hi)) hhalf)
      hopt hcanonical

/--
Theorem 3 reduced-optimum bridge, even-center first-half chain, with the
Proposition-1-shaped feasible-policy canonicalization assumption.
-/
theorem theorem3_optimalTypeFairnessAtLevel_one_mono_firstHalf_succ_center_chain_of_feasible_canonicalization
    {n : ℕ} [NeZero n]
    {v : Item n → ℝ} {c : Item n}
    (r : ℕ)
    (alphaSeq : ℕ → ℝ)
    (ρSeq : ℕ → TypePolicy 2 n)
    (ellSeq : ℕ → ℝ)
    {ρhalf : TypePolicy 2 n} {ellHalf : ℝ}
    (hn : 2 < n)
    (halpha0 : ∀ i, i ≤ r → 0 < alphaSeq i)
    (halpha1 : ∀ i, i ≤ r → alphaSeq i < 1)
    (halpha_half : ∀ i, i ≤ r → alphaSeq i ≤ 1 / 2)
    (hstep : ∀ i, i < r → alphaSeq i ≤ alphaSeq (i + 1))
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hsucc : c.val + 1 = (reverseItem c).val)
    (hpivot_or_eq :
      ∀ i, i < r →
        TypePolicy.lastActiveTypeZero (ρSeq i) =
          TypePolicy.lastActiveTypeZero (ρSeq (i + 1)) ∨
        alphaSeq i = alphaSeq (i + 1))
    (hopt :
      ∀ i, i ≤ r →
        Problem6EqualizedBasicOptimal (alphaSeq i) v (ρSeq i) (ellSeq i))
    (hhalf :
      Problem6EqualizedBasicOptimal (1 / 2) v ρhalf ellHalf)
    (hcanonical :
      ∀ i, i ≤ r →
        ∀ ρ' : TypePolicy 2 n,
          TypeWeightedRecommendationModel.feasibleAtLevel
            (twoTypeReducedModel (alphaSeq i) v) 1 ρ' →
          ∃ ρbar : TypePolicy 2 n,
            TypeWeightedRecommendationModel.feasibleAtLevel
              (twoTypeReducedModel (alphaSeq i) v) 1 ρbar ∧
            (∀ l : Item n,
              pairShare (alphaSeq i) v l * (ρbar 0 l).toReal +
                (1 - pairShare (alphaSeq i) v l) * (ρbar 1 l).toReal =
              TypeWeightedRecommendationModel.itemFairness
                (twoTypeReducedModel (alphaSeq i) v) ρbar) ∧
            TypePolicy.SharedItemsBound ρbar ∧
            TypeWeightedRecommendationModel.typeFairness
              (twoTypeReducedModel (alphaSeq i) v) ρ' ≤
            TypeWeightedRecommendationModel.typeFairness
              (twoTypeReducedModel (alphaSeq i) v) ρbar) :
    TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel (alphaSeq 0) v) 1 ≤
      TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel (alphaSeq r) v) 1 := by
  exact
    theorem3_optimalTypeFairnessAtLevel_one_mono_of_same_selected_or_equal_alpha_chain_of_feasible_canonicalization
      r alphaSeq ρSeq ellSeq hn halpha0 halpha1 halpha_half hstep
      hpos hdec hpivot_or_eq
      (fun i hi =>
        lemma10_alpha_le_half_equalizedBasicOptimal_lastActive_le_reverse_succ_center
          hn (halpha0 i (Nat.le_of_lt hi))
          (halpha1 i (Nat.le_of_lt hi))
          (halpha_half i (Nat.le_of_lt hi))
          hpos hdec hsucc (hopt i (Nat.le_of_lt hi)) hhalf)
      hopt hcanonical

/--
Theorem 3 reduced-optimum bridge, odd-center first-half chain, with
Proposition-1-shaped canonicalization and the Lemma 5 closed midpoint optimum.
-/
theorem theorem3_optimalTypeFairnessAtLevel_one_mono_firstHalf_center_chain_of_feasible_canonicalization_closed_half
    {n : ℕ} [NeZero n]
    {v : Item n → ℝ} {c : Item n}
    (r : ℕ)
    (alphaSeq : ℕ → ℝ)
    (ρSeq : ℕ → TypePolicy 2 n)
    (ellSeq : ℕ → ℝ)
    (hn : 2 < n)
    (halpha0 : ∀ i, i ≤ r → 0 < alphaSeq i)
    (halpha1 : ∀ i, i ≤ r → alphaSeq i < 1)
    (halpha_half : ∀ i, i ≤ r → alphaSeq i ≤ 1 / 2)
    (hstep : ∀ i, i < r → alphaSeq i ≤ alphaSeq (i + 1))
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter_c : c.val = (reverseItem c).val)
    (hpivot_or_eq :
      ∀ i, i < r →
        TypePolicy.lastActiveTypeZero (ρSeq i) =
          TypePolicy.lastActiveTypeZero (ρSeq (i + 1)) ∨
        alphaSeq i = alphaSeq (i + 1))
    (hopt :
      ∀ i, i ≤ r →
        Problem6EqualizedBasicOptimal (alphaSeq i) v (ρSeq i) (ellSeq i))
    (hcanonical :
      ∀ i, i ≤ r →
        ∀ ρ' : TypePolicy 2 n,
          TypeWeightedRecommendationModel.feasibleAtLevel
            (twoTypeReducedModel (alphaSeq i) v) 1 ρ' →
          ∃ ρbar : TypePolicy 2 n,
            TypeWeightedRecommendationModel.feasibleAtLevel
              (twoTypeReducedModel (alphaSeq i) v) 1 ρbar ∧
            (∀ l : Item n,
              pairShare (alphaSeq i) v l * (ρbar 0 l).toReal +
                (1 - pairShare (alphaSeq i) v l) * (ρbar 1 l).toReal =
              TypeWeightedRecommendationModel.itemFairness
                (twoTypeReducedModel (alphaSeq i) v) ρbar) ∧
            TypePolicy.SharedItemsBound ρbar ∧
            TypeWeightedRecommendationModel.typeFairness
              (twoTypeReducedModel (alphaSeq i) v) ρ' ≤
            TypeWeightedRecommendationModel.typeFairness
              (twoTypeReducedModel (alphaSeq i) v) ρbar) :
    TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel (alphaSeq 0) v) 1 ≤
      TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel (alphaSeq r) v) 1 := by
  exact
    theorem3_optimalTypeFairnessAtLevel_one_mono_of_same_selected_or_equal_alpha_chain_of_feasible_canonicalization
      r alphaSeq ρSeq ellSeq hn halpha0 halpha1 halpha_half hstep
      hpos hdec hpivot_or_eq
      (fun i hi =>
        lemma10_alpha_le_half_equalizedBasicOptimal_lastActive_le_reverse_center_of_closed_half
          hn (halpha0 i (Nat.le_of_lt hi))
          (halpha1 i (Nat.le_of_lt hi))
          (halpha_half i (Nat.le_of_lt hi))
          hpos hdec hcenter_c (hopt i (Nat.le_of_lt hi)))
      hopt hcanonical

/--
Theorem 3 reduced-optimum bridge, even-center first-half chain, with
Proposition-1-shaped canonicalization and the Lemma 5 closed midpoint optimum.
-/
theorem theorem3_optimalTypeFairnessAtLevel_one_mono_firstHalf_succ_center_chain_of_feasible_canonicalization_closed_half
    {n : ℕ} [NeZero n]
    {v : Item n → ℝ} {c : Item n}
    (r : ℕ)
    (alphaSeq : ℕ → ℝ)
    (ρSeq : ℕ → TypePolicy 2 n)
    (ellSeq : ℕ → ℝ)
    (hn : 2 < n)
    (halpha0 : ∀ i, i ≤ r → 0 < alphaSeq i)
    (halpha1 : ∀ i, i ≤ r → alphaSeq i < 1)
    (halpha_half : ∀ i, i ≤ r → alphaSeq i ≤ 1 / 2)
    (hstep : ∀ i, i < r → alphaSeq i ≤ alphaSeq (i + 1))
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hsucc : c.val + 1 = (reverseItem c).val)
    (hpivot_or_eq :
      ∀ i, i < r →
        TypePolicy.lastActiveTypeZero (ρSeq i) =
          TypePolicy.lastActiveTypeZero (ρSeq (i + 1)) ∨
        alphaSeq i = alphaSeq (i + 1))
    (hopt :
      ∀ i, i ≤ r →
        Problem6EqualizedBasicOptimal (alphaSeq i) v (ρSeq i) (ellSeq i))
    (hcanonical :
      ∀ i, i ≤ r →
        ∀ ρ' : TypePolicy 2 n,
          TypeWeightedRecommendationModel.feasibleAtLevel
            (twoTypeReducedModel (alphaSeq i) v) 1 ρ' →
          ∃ ρbar : TypePolicy 2 n,
            TypeWeightedRecommendationModel.feasibleAtLevel
              (twoTypeReducedModel (alphaSeq i) v) 1 ρbar ∧
            (∀ l : Item n,
              pairShare (alphaSeq i) v l * (ρbar 0 l).toReal +
                (1 - pairShare (alphaSeq i) v l) * (ρbar 1 l).toReal =
              TypeWeightedRecommendationModel.itemFairness
                (twoTypeReducedModel (alphaSeq i) v) ρbar) ∧
            TypePolicy.SharedItemsBound ρbar ∧
            TypeWeightedRecommendationModel.typeFairness
              (twoTypeReducedModel (alphaSeq i) v) ρ' ≤
            TypeWeightedRecommendationModel.typeFairness
              (twoTypeReducedModel (alphaSeq i) v) ρbar) :
    TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel (alphaSeq 0) v) 1 ≤
      TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel (alphaSeq r) v) 1 := by
  exact
    theorem3_optimalTypeFairnessAtLevel_one_mono_of_same_selected_or_equal_alpha_chain_of_feasible_canonicalization
      r alphaSeq ρSeq ellSeq hn halpha0 halpha1 halpha_half hstep
      hpos hdec hpivot_or_eq
      (fun i hi =>
        lemma10_alpha_le_half_equalizedBasicOptimal_lastActive_le_reverse_succ_center_of_closed_half
          hn (halpha0 i (Nat.le_of_lt hi))
          (halpha1 i (Nat.le_of_lt hi))
          (halpha_half i (Nat.le_of_lt hi))
          hpos hdec hsucc (hopt i (Nat.le_of_lt hi)))
      hopt hcanonical

/--
Theorem 3 reduced-optimum bridge in LP-selection form: along a first-half
finite chain, if every reduced `γ = 1` feasible policy is weakly dominated by
some equality-form optimal BFS representative, then `U^*_min(1, α)` is
monotone along the chain.
-/
theorem theorem3_optimalTypeFairnessAtLevel_one_mono_of_same_selected_or_equal_alpha_chain_of_equalizedBasicOptimal_dominance
    {n : ℕ} [NeZero n]
    {v : Item n → ℝ} (r : ℕ)
    (alphaSeq : ℕ → ℝ)
    (ρSeq : ℕ → TypePolicy 2 n)
    (ellSeq : ℕ → ℝ)
    (hn : 2 < n)
    (halpha0 : ∀ i, i ≤ r → 0 < alphaSeq i)
    (halpha1 : ∀ i, i ≤ r → alphaSeq i < 1)
    (halpha_half : ∀ i, i ≤ r → alphaSeq i ≤ 1 / 2)
    (hstep : ∀ i, i < r → alphaSeq i ≤ alphaSeq (i + 1))
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hpivot_or_eq :
      ∀ i, i < r →
        TypePolicy.lastActiveTypeZero (ρSeq i) =
          TypePolicy.lastActiveTypeZero (ρSeq (i + 1)) ∨
        alphaSeq i = alphaSeq (i + 1))
    (hcenter :
      ∀ i, i < r →
        (TypePolicy.lastActiveTypeZero (ρSeq i)).val ≤
          (reverseItem (TypePolicy.lastActiveTypeZero (ρSeq i))).val)
    (hopt :
      ∀ i, i ≤ r →
        Problem6EqualizedBasicOptimal (alphaSeq i) v (ρSeq i) (ellSeq i))
    (hdom :
      ∀ i, i ≤ r →
        ∀ ρ' : TypePolicy 2 n,
          TypeWeightedRecommendationModel.feasibleAtLevel
            (twoTypeReducedModel (alphaSeq i) v) 1 ρ' →
        ∃ (ρbar : TypePolicy 2 n) (ellbar : ℝ),
          Problem6EqualizedBasicOptimal (alphaSeq i) v ρbar ellbar ∧
          TypeWeightedRecommendationModel.typeFairness
            (twoTypeReducedModel (alphaSeq i) v) ρ' ≤
          TypeWeightedRecommendationModel.typeFairness
            (twoTypeReducedModel (alphaSeq i) v) ρbar) :
    TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel (alphaSeq 0) v) 1 ≤
      TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel (alphaSeq r) v) 1 := by
  exact
    theorem3_optimalTypeFairnessAtLevel_one_mono_of_same_selected_or_equal_alpha_chain_of_feasible_canonicalization
      r alphaSeq ρSeq ellSeq hn halpha0 halpha1 halpha_half hstep
      hpos hdec hpivot_or_eq hcenter hopt
      (fun i hi =>
        problem6_feasibleCanonicalization_of_equalizedBasicOptimal_dominance
          (halpha0 i hi) (halpha1 i hi) hpos (hdom i hi))

/--
Theorem 3 reduced-optimum bridge, odd-center first-half chain, in the
LP-selection dominance form.
-/
theorem theorem3_optimalTypeFairnessAtLevel_one_mono_firstHalf_center_chain_of_equalizedBasicOptimal_dominance
    {n : ℕ} [NeZero n]
    {v : Item n → ℝ} {c : Item n}
    (r : ℕ)
    (alphaSeq : ℕ → ℝ)
    (ρSeq : ℕ → TypePolicy 2 n)
    (ellSeq : ℕ → ℝ)
    {ρhalf : TypePolicy 2 n} {ellHalf : ℝ}
    (hn : 2 < n)
    (halpha0 : ∀ i, i ≤ r → 0 < alphaSeq i)
    (halpha1 : ∀ i, i ≤ r → alphaSeq i < 1)
    (halpha_half : ∀ i, i ≤ r → alphaSeq i ≤ 1 / 2)
    (hstep : ∀ i, i < r → alphaSeq i ≤ alphaSeq (i + 1))
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter_c : c.val = (reverseItem c).val)
    (hpivot_or_eq :
      ∀ i, i < r →
        TypePolicy.lastActiveTypeZero (ρSeq i) =
          TypePolicy.lastActiveTypeZero (ρSeq (i + 1)) ∨
        alphaSeq i = alphaSeq (i + 1))
    (hopt :
      ∀ i, i ≤ r →
        Problem6EqualizedBasicOptimal (alphaSeq i) v (ρSeq i) (ellSeq i))
    (hhalf :
      Problem6EqualizedBasicOptimal (1 / 2) v ρhalf ellHalf)
    (hdom :
      ∀ i, i ≤ r →
        ∀ ρ' : TypePolicy 2 n,
          TypeWeightedRecommendationModel.feasibleAtLevel
            (twoTypeReducedModel (alphaSeq i) v) 1 ρ' →
        ∃ (ρbar : TypePolicy 2 n) (ellbar : ℝ),
          Problem6EqualizedBasicOptimal (alphaSeq i) v ρbar ellbar ∧
          TypeWeightedRecommendationModel.typeFairness
            (twoTypeReducedModel (alphaSeq i) v) ρ' ≤
          TypeWeightedRecommendationModel.typeFairness
            (twoTypeReducedModel (alphaSeq i) v) ρbar) :
    TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel (alphaSeq 0) v) 1 ≤
      TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel (alphaSeq r) v) 1 := by
  exact
    theorem3_optimalTypeFairnessAtLevel_one_mono_firstHalf_center_chain_of_feasible_canonicalization
      r alphaSeq ρSeq ellSeq hn halpha0 halpha1 halpha_half hstep
      hpos hdec hcenter_c hpivot_or_eq hopt hhalf
      (fun i hi =>
        problem6_feasibleCanonicalization_of_equalizedBasicOptimal_dominance
          (halpha0 i hi) (halpha1 i hi) hpos (hdom i hi))

/--
Theorem 3 reduced-optimum bridge, even-center first-half chain, in the
LP-selection dominance form.
-/
theorem theorem3_optimalTypeFairnessAtLevel_one_mono_firstHalf_succ_center_chain_of_equalizedBasicOptimal_dominance
    {n : ℕ} [NeZero n]
    {v : Item n → ℝ} {c : Item n}
    (r : ℕ)
    (alphaSeq : ℕ → ℝ)
    (ρSeq : ℕ → TypePolicy 2 n)
    (ellSeq : ℕ → ℝ)
    {ρhalf : TypePolicy 2 n} {ellHalf : ℝ}
    (hn : 2 < n)
    (halpha0 : ∀ i, i ≤ r → 0 < alphaSeq i)
    (halpha1 : ∀ i, i ≤ r → alphaSeq i < 1)
    (halpha_half : ∀ i, i ≤ r → alphaSeq i ≤ 1 / 2)
    (hstep : ∀ i, i < r → alphaSeq i ≤ alphaSeq (i + 1))
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hsucc : c.val + 1 = (reverseItem c).val)
    (hpivot_or_eq :
      ∀ i, i < r →
        TypePolicy.lastActiveTypeZero (ρSeq i) =
          TypePolicy.lastActiveTypeZero (ρSeq (i + 1)) ∨
        alphaSeq i = alphaSeq (i + 1))
    (hopt :
      ∀ i, i ≤ r →
        Problem6EqualizedBasicOptimal (alphaSeq i) v (ρSeq i) (ellSeq i))
    (hhalf :
      Problem6EqualizedBasicOptimal (1 / 2) v ρhalf ellHalf)
    (hdom :
      ∀ i, i ≤ r →
        ∀ ρ' : TypePolicy 2 n,
          TypeWeightedRecommendationModel.feasibleAtLevel
            (twoTypeReducedModel (alphaSeq i) v) 1 ρ' →
        ∃ (ρbar : TypePolicy 2 n) (ellbar : ℝ),
          Problem6EqualizedBasicOptimal (alphaSeq i) v ρbar ellbar ∧
          TypeWeightedRecommendationModel.typeFairness
            (twoTypeReducedModel (alphaSeq i) v) ρ' ≤
          TypeWeightedRecommendationModel.typeFairness
            (twoTypeReducedModel (alphaSeq i) v) ρbar) :
    TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel (alphaSeq 0) v) 1 ≤
      TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel (alphaSeq r) v) 1 := by
  exact
    theorem3_optimalTypeFairnessAtLevel_one_mono_firstHalf_succ_center_chain_of_feasible_canonicalization
      r alphaSeq ρSeq ellSeq hn halpha0 halpha1 halpha_half hstep
      hpos hdec hsucc hpivot_or_eq hopt hhalf
      (fun i hi =>
        problem6_feasibleCanonicalization_of_equalizedBasicOptimal_dominance
          (halpha0 i hi) (halpha1 i hi) hpos (hdom i hi))

/--
Theorem 3 reduced-optimum bridge, odd-center first-half chain, in the
LP-selection dominance form, with the Lemma 5 closed midpoint optimum.
-/
theorem theorem3_optimalTypeFairnessAtLevel_one_mono_firstHalf_center_chain_of_equalizedBasicOptimal_dominance_closed_half
    {n : ℕ} [NeZero n]
    {v : Item n → ℝ} {c : Item n}
    (r : ℕ)
    (alphaSeq : ℕ → ℝ)
    (ρSeq : ℕ → TypePolicy 2 n)
    (ellSeq : ℕ → ℝ)
    (hn : 2 < n)
    (halpha0 : ∀ i, i ≤ r → 0 < alphaSeq i)
    (halpha1 : ∀ i, i ≤ r → alphaSeq i < 1)
    (halpha_half : ∀ i, i ≤ r → alphaSeq i ≤ 1 / 2)
    (hstep : ∀ i, i < r → alphaSeq i ≤ alphaSeq (i + 1))
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hcenter_c : c.val = (reverseItem c).val)
    (hpivot_or_eq :
      ∀ i, i < r →
        TypePolicy.lastActiveTypeZero (ρSeq i) =
          TypePolicy.lastActiveTypeZero (ρSeq (i + 1)) ∨
        alphaSeq i = alphaSeq (i + 1))
    (hopt :
      ∀ i, i ≤ r →
        Problem6EqualizedBasicOptimal (alphaSeq i) v (ρSeq i) (ellSeq i))
    (hdom :
      ∀ i, i ≤ r →
        ∀ ρ' : TypePolicy 2 n,
          TypeWeightedRecommendationModel.feasibleAtLevel
            (twoTypeReducedModel (alphaSeq i) v) 1 ρ' →
        ∃ (ρbar : TypePolicy 2 n) (ellbar : ℝ),
          Problem6EqualizedBasicOptimal (alphaSeq i) v ρbar ellbar ∧
          TypeWeightedRecommendationModel.typeFairness
            (twoTypeReducedModel (alphaSeq i) v) ρ' ≤
          TypeWeightedRecommendationModel.typeFairness
            (twoTypeReducedModel (alphaSeq i) v) ρbar) :
    TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel (alphaSeq 0) v) 1 ≤
      TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel (alphaSeq r) v) 1 := by
  exact
    theorem3_optimalTypeFairnessAtLevel_one_mono_firstHalf_center_chain_of_feasible_canonicalization_closed_half
      r alphaSeq ρSeq ellSeq hn halpha0 halpha1 halpha_half hstep
      hpos hdec hcenter_c hpivot_or_eq hopt
      (fun i hi =>
        problem6_feasibleCanonicalization_of_equalizedBasicOptimal_dominance
          (halpha0 i hi) (halpha1 i hi) hpos (hdom i hi))

/--
Theorem 3 reduced-optimum bridge, even-center first-half chain, in the
LP-selection dominance form, with the Lemma 5 closed midpoint optimum.
-/
theorem theorem3_optimalTypeFairnessAtLevel_one_mono_firstHalf_succ_center_chain_of_equalizedBasicOptimal_dominance_closed_half
    {n : ℕ} [NeZero n]
    {v : Item n → ℝ} {c : Item n}
    (r : ℕ)
    (alphaSeq : ℕ → ℝ)
    (ρSeq : ℕ → TypePolicy 2 n)
    (ellSeq : ℕ → ℝ)
    (hn : 2 < n)
    (halpha0 : ∀ i, i ≤ r → 0 < alphaSeq i)
    (halpha1 : ∀ i, i ≤ r → alphaSeq i < 1)
    (halpha_half : ∀ i, i ≤ r → alphaSeq i ≤ 1 / 2)
    (hstep : ∀ i, i < r → alphaSeq i ≤ alphaSeq (i + 1))
    (hpos : ∀ l : Item n, 0 < v l)
    (hdec : StrictlyDecreasingByIndex v)
    (hsucc : c.val + 1 = (reverseItem c).val)
    (hpivot_or_eq :
      ∀ i, i < r →
        TypePolicy.lastActiveTypeZero (ρSeq i) =
          TypePolicy.lastActiveTypeZero (ρSeq (i + 1)) ∨
        alphaSeq i = alphaSeq (i + 1))
    (hopt :
      ∀ i, i ≤ r →
        Problem6EqualizedBasicOptimal (alphaSeq i) v (ρSeq i) (ellSeq i))
    (hdom :
      ∀ i, i ≤ r →
        ∀ ρ' : TypePolicy 2 n,
          TypeWeightedRecommendationModel.feasibleAtLevel
            (twoTypeReducedModel (alphaSeq i) v) 1 ρ' →
        ∃ (ρbar : TypePolicy 2 n) (ellbar : ℝ),
          Problem6EqualizedBasicOptimal (alphaSeq i) v ρbar ellbar ∧
          TypeWeightedRecommendationModel.typeFairness
            (twoTypeReducedModel (alphaSeq i) v) ρ' ≤
          TypeWeightedRecommendationModel.typeFairness
            (twoTypeReducedModel (alphaSeq i) v) ρbar) :
    TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel (alphaSeq 0) v) 1 ≤
      TypeWeightedRecommendationModel.optimalTypeFairnessAtLevel
        (twoTypeReducedModel (alphaSeq r) v) 1 := by
  exact
    theorem3_optimalTypeFairnessAtLevel_one_mono_firstHalf_succ_center_chain_of_feasible_canonicalization_closed_half
      r alphaSeq ρSeq ellSeq hn halpha0 halpha1 halpha_half hstep
      hpos hdec hsucc hpivot_or_eq hopt
      (fun i hi =>
        problem6_feasibleCanonicalization_of_equalizedBasicOptimal_dominance
          (halpha0 i hi) (halpha1 i hi) hpos (hdom i hi))

end OpposingTypes
end GCG24UserItemFairness
