import PRPKG24AccuracyDiversity.AppendixD1GenericI

/-!
# Corrected generic Appendix D.1(ii)

This file develops the raw finite-integer core of the corrected power-tail
branch of Lemma D.1.  The source's displayed ratio-of-objectives step is not
valid because both saturation deficits tend to zero.  Every comparison here is
instead made directly between the original weighted deficits
`sum p_i * (A - h a_i)`.

The source statement also needs positive weights on the finite support.  The
theorems below deliberately take that support as the whole finite type; a
zero-weight support reduction belongs at the paper-facing bridge rather than
inside this raw optimizer argument.
-/

open Filter Topology
open scoped BigOperators

namespace PRPKG24AccuracyDiversity
namespace AppendixD1GenericII

open AppliedModelingLib
open AppendixD1GenericI

/-- The positive saturation deficit used in corrected D.1(ii). -/
abbrev saturationGap (A : ℝ) (h : ℕ → ℝ) (a : ℕ) : ℝ :=
  AppendixD1GenericI.saturationGap A h a

/--
Eventual positivity of the saturation gap propagates to every finite count
when the source value function is monotone.  Strict monotonicity is not
needed for the D.1(ii) interiority argument.
-/
theorem saturationGap_pos_of_monotone_of_eventually_pos
    {A : ℝ} {h : ℕ → ℝ} (hmono : Monotone h)
    (heventual : ∀ᶠ a in atTop, 0 < saturationGap A h a) :
    ∀ a : ℕ, 0 < saturationGap A h a := by
  obtain ⟨K, hK⟩ := eventually_atTop.1 heventual
  intro a
  by_cases ha : K ≤ a
  · exact hK a ha
  · have haK : a ≤ K := Nat.le_of_lt (Nat.lt_of_not_ge ha)
    have hle := hmono haK
    have hKpos := hK K le_rfl
    dsimp [saturationGap, AppendixD1GenericI.saturationGap] at hle hKpos ⊢
    linarith

/--
The corrected D.1(ii) power-tail condition gives two-sided raw deficit bounds
with arbitrary relative slack.  Unlike the source proof, this is an inequality
for deficits themselves, not a quotient of two vanishing objectives.
-/
theorem eventually_saturationGap_power_bounds
    {A B sigma : ℝ} {h : ℕ → ℝ}
    (hB_pos : 0 < B) (hsigma_neg : sigma < 0)
    (htail :
      Tendsto
        (fun a : ℕ =>
          saturationGap A h a / (B * (a : ℝ) ^ sigma))
        atTop (nhds 1))
    {delta : ℝ} (hdelta_pos : 0 < delta) :
    ∀ᶠ a : ℕ in atTop,
      (1 - delta) * (B * (a : ℝ) ^ sigma) < saturationGap A h a ∧
        saturationGap A h a < (1 + delta) * (B * (a : ℝ) ^ sigma) := by
  have hnear : Set.Ioo (1 - delta) (1 + delta) ∈ nhds (1 : ℝ) :=
    Ioo_mem_nhds (by linarith) (by linarith)
  filter_upwards [htail.eventually hnear, eventually_gt_atTop 0] with
    a hratio ha_pos
  have ha_real_pos : 0 < (a : ℝ) := by exact_mod_cast ha_pos
  have hpow_pos : 0 < (a : ℝ) ^ sigma :=
    Real.rpow_pos_of_pos ha_real_pos sigma
  have hden_pos : 0 < B * (a : ℝ) ^ sigma :=
    mul_pos hB_pos hpow_pos
  have hden_ne : B * (a : ℝ) ^ sigma ≠ 0 := ne_of_gt hden_pos
  have hratio_mul :
      (saturationGap A h a / (B * (a : ℝ) ^ sigma)) *
          (B * (a : ℝ) ^ sigma) =
        saturationGap A h a := by
    field_simp [hden_ne]
  have hlow := mul_lt_mul_of_pos_right hratio.1 hden_pos
  have hhigh := mul_lt_mul_of_pos_right hratio.2 hden_pos
  rw [hratio_mul] at hlow hhigh
  exact ⟨hlow, hhigh⟩

/--
The literal corrected D.1(ii) power tail already entails eventual positivity
of the saturation gap.  Thus this fact is not an additional source-model
assumption at the paper-facing boundary.
-/
theorem eventually_saturationGap_pos_of_power_tail
    {A B sigma : ℝ} {h : ℕ → ℝ}
    (hB_pos : 0 < B) (hsigma_neg : sigma < 0)
    (htail :
      Tendsto
        (fun a : ℕ =>
          saturationGap A h a / (B * (a : ℝ) ^ sigma))
        atTop (nhds 1)) :
    ∀ᶠ a : ℕ in atTop, 0 < saturationGap A h a := by
  have hbounds :=
    eventually_saturationGap_power_bounds hB_pos hsigma_neg htail
      (delta := (1 / 2 : ℝ)) (by norm_num)
  filter_upwards [hbounds, eventually_gt_atTop 0] with a ha ha_pos
  have ha_real_pos : 0 < (a : ℝ) := by exact_mod_cast ha_pos
  have hden_pos : 0 < B * (a : ℝ) ^ sigma :=
    mul_pos hB_pos (Real.rpow_pos_of_pos ha_real_pos sigma)
  have hfactor_pos : 0 < 1 - (1 / 2 : ℝ) := by norm_num
  exact lt_trans (mul_pos hfactor_pos hden_pos) ha.1

/-- The raw corrected power-tail condition forces the saturation deficit to zero. -/
theorem tendsto_saturationGap_nhds_zero_of_power_tail
    {A B sigma : ℝ} {h : ℕ → ℝ}
    (hB_pos : 0 < B) (hsigma_neg : sigma < 0)
    (htail :
      Tendsto
        (fun a : ℕ =>
          saturationGap A h a / (B * (a : ℝ) ^ sigma))
        atTop (nhds 1)) :
    Tendsto (saturationGap A h) atTop (nhds 0) := by
  have hpow :
      Tendsto (fun a : ℕ => (a : ℝ) ^ sigma) atTop (nhds 0) := by
    have hbase :=
      (tendsto_rpow_neg_atTop (neg_pos.mpr hsigma_neg)).comp
        tendsto_natCast_atTop_atTop
    simpa only [neg_neg, Function.comp_apply] using hbase
  have hden :
      Tendsto (fun a : ℕ => B * (a : ℝ) ^ sigma) atTop (nhds 0) :=
    by simpa using (tendsto_const_nhds.mul hpow :
      Tendsto (fun a : ℕ => B * (a : ℝ) ^ sigma) atTop (nhds (B * 0)))
  have hprod :
      Tendsto
        (fun a : ℕ =>
          (saturationGap A h a / (B * (a : ℝ) ^ sigma)) *
            (B * (a : ℝ) ^ sigma))
        atTop (nhds 0) :=
    by simpa using htail.mul hden
  refine hprod.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with a ha_pos
  have ha_real_pos : 0 < (a : ℝ) := by exact_mod_cast ha_pos
  have hpow_pos : 0 < (a : ℝ) ^ sigma :=
    Real.rpow_pos_of_pos ha_real_pos sigma
  have hden_ne : B * (a : ℝ) ^ sigma ≠ 0 :=
    mul_ne_zero (ne_of_gt hB_pos) (ne_of_gt hpow_pos)
  field_simp [hden_ne]

/--
The total weighted deficit of the literal balanced integer competitor tends to
zero under the corrected D.1(ii) power tail.
-/
theorem tendsto_balanced_weighted_saturationGap_sum_nhds_zero_of_power_tail
    {m : ℕ} [NeZero m] {A B sigma : ℝ} {h : ℕ → ℝ}
    (p : ItemType m → ℝ)
    (hB_pos : 0 < B) (hsigma_neg : sigma < 0)
    (htail :
      Tendsto
        (fun a : ℕ =>
          saturationGap A h a / (B * (a : ℝ) ^ sigma))
        atTop (nhds 1)) :
    Tendsto
      (fun N : ℕ =>
        ∑ i : ItemType m,
          p i * saturationGap A h ((balancedAllocation m N).count i))
      atTop (nhds 0) := by
  have hgap_zero :
      Tendsto (saturationGap A h) atTop (nhds 0) :=
    tendsto_saturationGap_nhds_zero_of_power_tail hB_pos hsigma_neg htail
  have hsum :
      Tendsto
        (fun N : ℕ =>
          ∑ i : ItemType m,
            p i * saturationGap A h ((balancedAllocation m N).count i))
        atTop (nhds (∑ _i : ItemType m, (0 : ℝ))) := by
    exact tendsto_finset_sum Finset.univ (fun i _ => by
      simpa using
        (tendsto_const_nhds (x := p i)).mul
          (hgap_zero.comp
            (tendsto_balancedAllocation_count_atTop (m := m) i)))
  simpa using hsum

/--
A power-tail deficit at a coordinate held below `r * N` eventually dominates
the balanced-coordinate deficit, provided the explicit coefficient condition
holds.  This is the direct block-separation estimate needed to upgrade mere
divergence of optimal counts to a positive linear lower bound.
-/
theorem eventually_saturationGap_power_separation_of_count_le
    {m : ℕ} [NeZero m] {A B sigma : ℝ} {h : ℕ → ℝ}
    {a : ℕ → ℕ} {r c C : ℝ}
    (hr_pos : 0 < r) (hrc : r < c) (hc_uniform : c < 1 / (m : ℝ))
    (hC_pos : 0 < C) (hcoefficient : C * c ^ sigma < r ^ sigma)
    (hB_pos : 0 < B) (hsigma_neg : sigma < 0)
    (hgap_pos : ∀ n : ℕ, 0 < saturationGap A h n)
    (htail :
      Tendsto
        (fun n : ℕ =>
          saturationGap A h n / (B * (n : ℝ) ^ sigma))
        atTop (nhds 1))
    (ha_atTop : Tendsto a atTop atTop) :
    ∀ᶠ N : ℕ in atTop,
      (a N : ℝ) ≤ r * (N : ℝ) ->
        C * saturationGap A h (N / m) < saturationGap A h (a N) := by
  let R : ℝ := r ^ sigma
  let S : ℝ := C * c ^ sigma
  have hc_pos : 0 < c := lt_trans hr_pos hrc
  have hR_pos : 0 < R := by
    dsimp [R]
    exact Real.rpow_pos_of_pos hr_pos sigma
  have hS_pos : 0 < S := by
    dsimp [S]
    exact mul_pos hC_pos (Real.rpow_pos_of_pos hc_pos sigma)
  have hSR : S < R := by
    simpa [R, S] using hcoefficient
  let delta : ℝ := (R - S) / (2 * (R + S))
  have hsum_pos : 0 < R + S := add_pos hR_pos hS_pos
  have hden_pos : 0 < 2 * (R + S) := mul_pos (by norm_num) hsum_pos
  have hdelta_pos : 0 < delta := by
    dsimp [delta]
    exact div_pos (sub_pos.mpr hSR) hden_pos
  have hdelta_lt_one : delta < 1 := by
    dsimp [delta]
    apply (div_lt_iff₀ hden_pos).mpr
    nlinarith
  have hdelta_mul : delta * (R + S) = (R - S) / 2 := by
    dsimp [delta]
    field_simp [ne_of_gt hsum_pos]
  have hdelta_separation : (1 + delta) * S < (1 - delta) * R := by
    nlinarith [hdelta_mul]
  have hraw_bounds :=
    eventually_saturationGap_power_bounds hB_pos hsigma_neg htail hdelta_pos
  have ha_bounds :
      ∀ᶠ N : ℕ in atTop,
        (1 - delta) * (B * (a N : ℝ) ^ sigma) <
            saturationGap A h (a N) ∧
          saturationGap A h (a N) <
            (1 + delta) * (B * (a N : ℝ) ^ sigma) :=
    ha_atTop.eventually hraw_bounds
  have hq_bounds :
      ∀ᶠ N : ℕ in atTop,
        (1 - delta) * (B * ((N / m : ℕ) : ℝ) ^ sigma) <
            saturationGap A h (N / m) ∧
          saturationGap A h (N / m) <
            (1 + delta) * (B * ((N / m : ℕ) : ℝ) ^ sigma) :=
    (tendsto_nat_div_typeCount_atTop (m := m)).eventually hraw_bounds
  have hfloor :
      ∀ᶠ N : ℕ in atTop, c * (N : ℝ) < ((N / m : ℕ) : ℝ) :=
    eventually_mul_lt_nat_div hc_uniform
  have ha_pos_nat : ∀ᶠ N : ℕ in atTop, 0 < a N :=
    ha_atTop.eventually (eventually_gt_atTop 0)
  have ha_pos : ∀ᶠ N : ℕ in atTop, 0 < (a N : ℝ) := by
    filter_upwards [ha_pos_nat] with N hN
    exact_mod_cast hN
  filter_upwards [ha_bounds, hq_bounds, hfloor, ha_pos, eventually_gt_atTop 0]
    with N ha hq hfloorN haN_pos hN_pos
  intro hcountN
  have hN_real_pos : 0 < (N : ℝ) := by exact_mod_cast hN_pos
  have hNpow_pos : 0 < (N : ℝ) ^ sigma :=
    Real.rpow_pos_of_pos hN_real_pos sigma
  have hpow_a : r ^ sigma * (N : ℝ) ^ sigma ≤ (a N : ℝ) ^ sigma := by
    calc
      r ^ sigma * (N : ℝ) ^ sigma = (r * (N : ℝ)) ^ sigma := by
        rw [Real.mul_rpow hr_pos.le hN_real_pos.le]
      _ ≤ (a N : ℝ) ^ sigma :=
        Real.rpow_le_rpow_of_nonpos haN_pos hcountN hsigma_neg.le
  have hq_pos : 0 < ((N / m : ℕ) : ℝ) :=
    lt_trans (mul_pos hc_pos hN_real_pos) hfloorN
  have hpow_q : ((N / m : ℕ) : ℝ) ^ sigma ≤
      c ^ sigma * (N : ℝ) ^ sigma := by
    calc
      ((N / m : ℕ) : ℝ) ^ sigma ≤ (c * (N : ℝ)) ^ sigma :=
          Real.rpow_le_rpow_of_nonpos (mul_pos hc_pos hN_real_pos)
            hfloorN.le hsigma_neg.le
      _ = c ^ sigma * (N : ℝ) ^ sigma := by
          rw [Real.mul_rpow hc_pos.le hN_real_pos.le]
  have hleft_factor_nonneg : 0 ≤ C * ((1 + delta) * B) := by
    have : 0 ≤ 1 + delta := by linarith
    positivity
  have hmid_q :
      C * ((1 + delta) * (B * ((N / m : ℕ) : ℝ) ^ sigma)) ≤
        C * ((1 + delta) * (B * (c ^ sigma * (N : ℝ) ^ sigma))) := by
    calc
      C * ((1 + delta) * (B * ((N / m : ℕ) : ℝ) ^ sigma)) =
          (C * ((1 + delta) * B)) * ((N / m : ℕ) : ℝ) ^ sigma := by ring
      _ ≤ (C * ((1 + delta) * B)) *
          (c ^ sigma * (N : ℝ) ^ sigma) :=
        mul_le_mul_of_nonneg_left hpow_q hleft_factor_nonneg
      _ = C * ((1 + delta) * (B * (c ^ sigma * (N : ℝ) ^ sigma))) := by ring
  have hBN_pos : 0 < B * (N : ℝ) ^ sigma :=
    mul_pos hB_pos hNpow_pos
  have hmid_strict :
      C * ((1 + delta) * (B * (c ^ sigma * (N : ℝ) ^ sigma))) <
        (1 - delta) * (B * (r ^ sigma * (N : ℝ) ^ sigma)) := by
    have hscaled := mul_lt_mul_of_pos_right hdelta_separation hBN_pos
    calc
      C * ((1 + delta) * (B * (c ^ sigma * (N : ℝ) ^ sigma))) =
          ((1 + delta) * S) * (B * (N : ℝ) ^ sigma) := by
            dsimp [S]
            ring
      _ < ((1 - delta) * R) * (B * (N : ℝ) ^ sigma) := hscaled
      _ = (1 - delta) * (B * (r ^ sigma * (N : ℝ) ^ sigma)) := by
            dsimp [R]
            ring
  have hright_factor_nonneg : 0 ≤ (1 - delta) * B := by
    have : 0 ≤ 1 - delta := by linarith
    positivity
  have hmid_a :
      (1 - delta) * (B * (r ^ sigma * (N : ℝ) ^ sigma)) ≤
        (1 - delta) * (B * (a N : ℝ) ^ sigma) := by
    calc
      (1 - delta) * (B * (r ^ sigma * (N : ℝ) ^ sigma)) =
          ((1 - delta) * B) * (r ^ sigma * (N : ℝ) ^ sigma) := by ring
      _ ≤ ((1 - delta) * B) * (a N : ℝ) ^ sigma :=
        mul_le_mul_of_nonneg_left hpow_a hright_factor_nonneg
      _ = (1 - delta) * (B * (a N : ℝ) ^ sigma) := by ring
  calc
    C * saturationGap A h (N / m) <
        C * ((1 + delta) * (B * ((N / m : ℕ) : ℝ) ^ sigma)) :=
      mul_lt_mul_of_pos_left hq.2 hC_pos
    _ ≤ C * ((1 + delta) * (B * (c ^ sigma * (N : ℝ) ^ sigma))) := hmid_q
    _ < (1 - delta) * (B * (r ^ sigma * (N : ℝ) ^ sigma)) := hmid_strict
    _ ≤ (1 - delta) * (B * (a N : ℝ) ^ sigma) := hmid_a
    _ < saturationGap A h (a N) := ha.1

/--
For every positive comparison coefficient and every negative power, there is
a strictly positive fraction below a prescribed positive scale whose power is
large enough for the raw-deficit separation argument.  This is the elementary
existence step behind eventual linear interiority.
-/
theorem exists_positive_power_fraction_with_coefficient_separation
    {C c sigma : ℝ}
    (hC_pos : 0 < C) (hc_pos : 0 < c) (hsigma_neg : sigma < 0) :
    ∃ r : ℝ, 0 < r ∧ r < c ∧ C * c ^ sigma < r ^ sigma := by
  let d : ℝ := (C + 1) ^ (1 / sigma)
  let r : ℝ := c * d
  have hC_one : 1 < C + 1 := by linarith
  have hinv_neg : 1 / sigma < 0 := one_div_neg.mpr hsigma_neg
  have hd_pos : 0 < d := by
    dsimp [d]
    exact Real.rpow_pos_of_pos (by linarith) _
  have hd_lt_one : d < 1 := by
    dsimp [d]
    exact Real.rpow_lt_one_of_one_lt_of_neg hC_one hinv_neg
  have hr_pos : 0 < r := mul_pos hc_pos hd_pos
  have hrc : r < c := by
    dsimp [r]
    nlinarith
  have hd_pow : d ^ sigma = C + 1 := by
    dsimp [d]
    rw [← Real.rpow_mul (by linarith : 0 ≤ C + 1)]
    have hmul : (1 / sigma) * sigma = 1 := by
      field_simp [ne_of_lt hsigma_neg]
    rw [hmul, Real.rpow_one]
  have hr_pow : r ^ sigma = c ^ sigma * (C + 1) := by
    dsimp [r]
    rw [Real.mul_rpow hc_pos.le (Real.rpow_nonneg (le_of_lt (by linarith : 0 < C + 1)) _),
      hd_pow]
  refine ⟨r, hr_pos, hrc, ?_⟩
  rw [hr_pow]
  have hcpow_pos : 0 < c ^ sigma := Real.rpow_pos_of_pos hc_pos sigma
  nlinarith

/--
Raw fixed-total optimality compares the actual and any feasible competitor's
weighted saturation deficits in the correct direction.  This is the direct
replacement for the invalid source ratio step in equations (55)--(61).
-/
theorem weighted_saturationGap_sum_le_of_optimal
    {m : ℕ} {A : ℝ} {h : ℕ → ℝ}
    (p : ItemType m → ℝ)
    (seq : AppliedModelingLib.Allocation.OptimalSequence
      (fun _ : ℕ => p) (fun _ : ℕ => fun _ : ItemType m => h))
    (N : ℕ) (b : CountAllocation m)
    (hb : ConsumptionModel.FeasibleAtTotal N b) :
    (∑ i : ItemType m,
      p i * saturationGap A h ((seq.allocation N).count i)) ≤
      ∑ i : ItemType m, p i * saturationGap A h (b.count i) := by
  have hopt := (seq.optimal N).2 b hb
  have hgap_eq (a : CountAllocation m) :
      (∑ i : ItemType m, p i * saturationGap A h (a.count i)) =
        (∑ i : ItemType m, p i * A) -
          AppliedModelingLib.Allocation.objective a p (fun _ : ItemType m => h) := by
    calc
      (∑ i : ItemType m, p i * saturationGap A h (a.count i)) =
          ∑ i : ItemType m, (p i * A - p i * h (a.count i)) := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            simp only [saturationGap, AppendixD1GenericI.saturationGap]
            ring
      _ = (∑ i : ItemType m, p i * A) -
          AppliedModelingLib.Allocation.objective a p (fun _ : ItemType m => h) := by
            rw [Finset.sum_sub_distrib]
            rfl
  rw [hgap_eq (seq.allocation N), hgap_eq b]
  linarith

/-! The next helper receives only the interiority fact proved below.  Keeping
it private prevents a convergence/interiority certificate from becoming a
paper-facing premise. -/
private theorem eventually_optimalAllocation_count_gt_linear_of_power_tail_of_count_atTop
    {m : ℕ} [NeZero m] {A B sigma : ℝ} {h : ℕ → ℝ}
    (p : ItemType m → ℝ)
    (seq : AppliedModelingLib.Allocation.OptimalSequence
      (fun _ : ℕ => p) (fun _ : ℕ => fun _ : ItemType m => h))
    (hp_pos : ∀ i : ItemType m, 0 < p i)
    (hmono : Monotone h)
    (hB_pos : 0 < B) (hsigma_neg : sigma < 0)
    (hgap_eventual_pos : ∀ᶠ n in atTop, 0 < saturationGap A h n)
    (htail :
      Tendsto
        (fun n : ℕ =>
          saturationGap A h n / (B * (n : ℝ) ^ sigma))
        atTop (nhds 1))
    (t : ItemType m)
    (hcoord_top :
      Tendsto (fun N : ℕ => (seq.allocation N).count t) atTop atTop)
    {r c : ℝ}
    (hr_pos : 0 < r) (hrc : r < c) (hc_uniform : c < 1 / (m : ℝ))
    (hcoefficient :
      ((∑ i : ItemType m, p i) / p t) * c ^ sigma < r ^ sigma) :
    ∀ᶠ N : ℕ in atTop,
      r * (N : ℝ) < ((seq.allocation N).count t : ℝ) := by
  have hgap_pos : ∀ n : ℕ, 0 < saturationGap A h n :=
    saturationGap_pos_of_monotone_of_eventually_pos hmono hgap_eventual_pos
  have hgap_antitone : Antitone (saturationGap A h) := by
    intro a b hab
    dsimp [saturationGap, AppendixD1GenericI.saturationGap]
    linarith [hmono hab]
  let totalWeight : ℝ := ∑ i : ItemType m, p i
  have htotalWeight_pos : 0 < totalWeight := by
    have hterm_le : p t ≤ ∑ i : ItemType m, p i :=
      Finset.single_le_sum (fun i _hi => (hp_pos i).le) (Finset.mem_univ t)
    dsimp [totalWeight]
    exact lt_of_lt_of_le (hp_pos t) hterm_le
  let C : ℝ := totalWeight / p t
  have hC_pos : 0 < C := by
    dsimp [C]
    exact div_pos htotalWeight_pos (hp_pos t)
  have hcoefficient' : C * c ^ sigma < r ^ sigma := by
    simpa [C, totalWeight] using hcoefficient
  have hseparation :
      ∀ᶠ N : ℕ in atTop,
        ((seq.allocation N).count t : ℝ) ≤ r * (N : ℝ) ->
          C * saturationGap A h (N / m) <
            saturationGap A h ((seq.allocation N).count t) :=
    eventually_saturationGap_power_separation_of_count_le
      (m := m) (A := A) (B := B) (sigma := sigma) (h := h)
      (a := fun N => (seq.allocation N).count t) (r := r) (c := c) (C := C)
      hr_pos hrc hc_uniform hC_pos hcoefficient' hB_pos hsigma_neg
      hgap_pos htail hcoord_top
  filter_upwards [hseparation] with N hseparationN
  by_contra hnot
  have hcount_le : ((seq.allocation N).count t : ℝ) ≤ r * (N : ℝ) :=
    le_of_not_gt hnot
  have hsep := hseparationN hcount_le
  have hbalanced_sum_le :
      (∑ i : ItemType m,
        p i * saturationGap A h ((balancedAllocation m N).count i)) ≤
          totalWeight * saturationGap A h (N / m) := by
    calc
      (∑ i : ItemType m,
        p i * saturationGap A h ((balancedAllocation m N).count i)) ≤
          ∑ i : ItemType m, p i * saturationGap A h (N / m) := by
            refine Finset.sum_le_sum ?_
            intro i _hi
            exact mul_le_mul_of_nonneg_left
              (hgap_antitone (div_le_balancedAllocation_count m N i))
              (hp_pos i).le
      _ = totalWeight * saturationGap A h (N / m) := by
            rw [Finset.sum_mul]
  have hterm_le_actual :
      p t * saturationGap A h ((seq.allocation N).count t) ≤
        ∑ i : ItemType m,
          p i * saturationGap A h ((seq.allocation N).count i) := by
    exact Finset.single_le_sum
      (fun i _hi => mul_nonneg (hp_pos i).le (hgap_pos _).le)
      (Finset.mem_univ t)
  have hactual_le :
      p t * saturationGap A h ((seq.allocation N).count t) ≤
        totalWeight * saturationGap A h (N / m) := by
    exact hterm_le_actual.trans
      ((weighted_saturationGap_sum_le_of_optimal
        (A := A) p seq N (balancedAllocation m N)
        (balancedAllocation_feasible (m := m) N)).trans hbalanced_sum_le)
  have hsep_weighted :
      totalWeight * saturationGap A h (N / m) <
        p t * saturationGap A h ((seq.allocation N).count t) := by
    calc
      totalWeight * saturationGap A h (N / m) =
          p t * (C * saturationGap A h (N / m)) := by
            dsimp [C]
            field_simp [ne_of_gt (hp_pos t)]
      _ < p t * saturationGap A h ((seq.allocation N).count t) :=
        mul_lt_mul_of_pos_left hsep (hp_pos t)
  exact (not_lt_of_ge hactual_le) hsep_weighted

/--
Every positive-weight coordinate of a literal optimizer diverges under the
corrected D.1(ii) tail.  The proof uses only raw deficit optimality against
the balanced integer competitor; no limiting objective or share convergence
is assumed.
-/
theorem tendsto_optimalAllocation_count_atTop_of_power_tail
    {m : ℕ} [NeZero m] {A B sigma : ℝ} {h : ℕ → ℝ}
    (p : ItemType m → ℝ)
    (seq : AppliedModelingLib.Allocation.OptimalSequence
      (fun _ : ℕ => p) (fun _ : ℕ => fun _ : ItemType m => h))
    (hp_pos : ∀ i : ItemType m, 0 < p i)
    (hmono : Monotone h)
    (hB_pos : 0 < B) (hsigma_neg : sigma < 0)
    (hgap_eventual_pos : ∀ᶠ a : ℕ in atTop, 0 < saturationGap A h a)
    (htail :
      Tendsto
        (fun a : ℕ =>
          saturationGap A h a / (B * (a : ℝ) ^ sigma))
        atTop (nhds 1))
    (t : ItemType m) :
    Tendsto (fun N : ℕ => (seq.allocation N).count t) atTop atTop := by
  have hgap_pos : ∀ a : ℕ, 0 < saturationGap A h a :=
    saturationGap_pos_of_monotone_of_eventually_pos hmono hgap_eventual_pos
  have hgap_antitone : Antitone (saturationGap A h) := by
    intro a b hab
    dsimp [saturationGap, AppendixD1GenericI.saturationGap]
    linarith [hmono hab]
  have hbalanced_zero :=
    tendsto_balanced_weighted_saturationGap_sum_nhds_zero_of_power_tail
      p hB_pos hsigma_neg htail
  rw [tendsto_atTop]
  intro K
  have hKterm_pos : 0 < p t * saturationGap A h K :=
    mul_pos (hp_pos t) (hgap_pos K)
  have hbalanced_small :
      ∀ᶠ N : ℕ in atTop,
        (∑ i : ItemType m,
          p i * saturationGap A h ((balancedAllocation m N).count i)) <
          p t * saturationGap A h K :=
    hbalanced_zero (isOpen_Iio.mem_nhds hKterm_pos)
  filter_upwards [hbalanced_small] with N hsmall
  by_contra hnot
  have hcount_le : (seq.allocation N).count t ≤ K :=
    Nat.le_of_lt (Nat.lt_of_not_ge hnot)
  have hgap_ge :
      saturationGap A h K ≤ saturationGap A h ((seq.allocation N).count t) :=
    hgap_antitone hcount_le
  have hweighted_ge :
      p t * saturationGap A h K ≤
        p t * saturationGap A h ((seq.allocation N).count t) :=
    mul_le_mul_of_nonneg_left hgap_ge (hp_pos t).le
  have hterm_le_sum :
      p t * saturationGap A h ((seq.allocation N).count t) ≤
        ∑ i : ItemType m,
          p i * saturationGap A h ((seq.allocation N).count i) := by
    exact Finset.single_le_sum
      (fun i _hi => mul_nonneg (hp_pos i).le (hgap_pos _).le)
      (Finset.mem_univ t)
  have hopt_gap :=
    weighted_saturationGap_sum_le_of_optimal
      (A := A) p seq N (balancedAllocation m N)
      (balancedAllocation_feasible (m := m) N)
  have hcontradiction : p t * saturationGap A h K < p t * saturationGap A h K := by
    calc
      p t * saturationGap A h K ≤
          p t * saturationGap A h ((seq.allocation N).count t) := hweighted_ge
      _ ≤ ∑ i : ItemType m,
          p i * saturationGap A h ((seq.allocation N).count i) := hterm_le_sum
      _ ≤ ∑ i : ItemType m,
          p i * saturationGap A h ((balancedAllocation m N).count i) := hopt_gap
      _ < p t * saturationGap A h K := hsmall
  exact (lt_irrefl _) hcontradiction

/--
Source-shaped D.1(ii) coordinate divergence: eventual gap positivity is
derived from the displayed positive-coefficient negative-power tail, rather
than supplied as a separate assumption.  The finite support remains explicitly
all-positive in this raw core.
-/
theorem source_tendsto_optimalAllocation_count_atTop_of_power_tail
    {m : ℕ} [NeZero m] {A B sigma : ℝ} {h : ℕ → ℝ}
    (p : ItemType m → ℝ)
    (seq : AppliedModelingLib.Allocation.OptimalSequence
      (fun _ : ℕ => p) (fun _ : ℕ => fun _ : ItemType m => h))
    (hp_pos : ∀ i : ItemType m, 0 < p i)
    (hmono : Monotone h)
    (hB_pos : 0 < B) (hsigma_neg : sigma < 0)
    (htail :
      Tendsto
        (fun a : ℕ =>
          saturationGap A h a / (B * (a : ℝ) ^ sigma))
        atTop (nhds 1))
    (t : ItemType m) :
    Tendsto (fun N : ℕ => (seq.allocation N).count t) atTop atTop := by
  exact tendsto_optimalAllocation_count_atTop_of_power_tail
    p seq hp_pos hmono hB_pos hsigma_neg
    (eventually_saturationGap_pos_of_power_tail hB_pos hsigma_neg htail)
    htail t

/--
Under an explicit power-coefficient separation, no positive-weight coordinate
of a literal optimizer can stay below the indicated linear fraction.  The
proof first derives coordinate divergence from raw deficit optimality, then
uses the raw power-tail block comparison; it takes no interiority or optimizer
convergence certificate as a premise.
-/
theorem eventually_optimalAllocation_count_gt_linear_of_power_tail
    {m : ℕ} [NeZero m] {A B sigma : ℝ} {h : ℕ → ℝ}
    (p : ItemType m → ℝ)
    (seq : AppliedModelingLib.Allocation.OptimalSequence
      (fun _ : ℕ => p) (fun _ : ℕ => fun _ : ItemType m => h))
    (hp_pos : ∀ i : ItemType m, 0 < p i)
    (hmono : Monotone h)
    (hB_pos : 0 < B) (hsigma_neg : sigma < 0)
    (hgap_eventual_pos : ∀ᶠ n in atTop, 0 < saturationGap A h n)
    (htail :
      Tendsto
        (fun n : ℕ =>
          saturationGap A h n / (B * (n : ℝ) ^ sigma))
        atTop (nhds 1))
    (t : ItemType m) {r c : ℝ}
    (hr_pos : 0 < r) (hrc : r < c) (hc_uniform : c < 1 / (m : ℝ))
    (hcoefficient :
      ((∑ i : ItemType m, p i) / p t) * c ^ sigma < r ^ sigma) :
    ∀ᶠ N : ℕ in atTop,
      r * (N : ℝ) < ((seq.allocation N).count t : ℝ) := by
  apply eventually_optimalAllocation_count_gt_linear_of_power_tail_of_count_atTop
    p seq hp_pos hmono hB_pos hsigma_neg hgap_eventual_pos htail t
  · exact tendsto_optimalAllocation_count_atTop_of_power_tail
      p seq hp_pos hmono hB_pos hsigma_neg hgap_eventual_pos htail t
  · exact hr_pos
  · exact hrc
  · exact hc_uniform
  · exact hcoefficient

/--
Source-shaped D.1(ii) raw power-separation conclusion with no independent
eventual-gap premise.  Positivity follows from the displayed tail bounds.
-/
theorem source_eventually_optimalAllocation_count_gt_linear_of_power_tail
    {m : ℕ} [NeZero m] {A B sigma : ℝ} {h : ℕ → ℝ}
    (p : ItemType m → ℝ)
    (seq : AppliedModelingLib.Allocation.OptimalSequence
      (fun _ : ℕ => p) (fun _ : ℕ => fun _ : ItemType m => h))
    (hp_pos : ∀ i : ItemType m, 0 < p i)
    (hmono : Monotone h)
    (hB_pos : 0 < B) (hsigma_neg : sigma < 0)
    (htail :
      Tendsto
        (fun n : ℕ =>
          saturationGap A h n / (B * (n : ℝ) ^ sigma))
        atTop (nhds 1))
    (t : ItemType m) {r c : ℝ}
    (hr_pos : 0 < r) (hrc : r < c) (hc_uniform : c < 1 / (m : ℝ))
    (hcoefficient :
      ((∑ i : ItemType m, p i) / p t) * c ^ sigma < r ^ sigma) :
    ∀ᶠ N : ℕ in atTop,
      r * (N : ℝ) < ((seq.allocation N).count t : ℝ) := by
  exact eventually_optimalAllocation_count_gt_linear_of_power_tail
    p seq hp_pos hmono hB_pos hsigma_neg
    (eventually_saturationGap_pos_of_power_tail hB_pos hsigma_neg htail)
    htail t hr_pos hrc hc_uniform hcoefficient

/--
Every positive-weight coordinate has some strictly positive eventual linear
lower bound under the corrected D.1(ii) assumptions.  The fraction is
constructed from the primitive weights and tail exponent inside the proof.
-/
theorem exists_eventual_positive_linear_lower_bound_of_power_tail
    {m : ℕ} [NeZero m] {A B sigma : ℝ} {h : ℕ → ℝ}
    (p : ItemType m → ℝ)
    (seq : AppliedModelingLib.Allocation.OptimalSequence
      (fun _ : ℕ => p) (fun _ : ℕ => fun _ : ItemType m => h))
    (hp_pos : ∀ i : ItemType m, 0 < p i)
    (hmono : Monotone h)
    (hB_pos : 0 < B) (hsigma_neg : sigma < 0)
    (hgap_eventual_pos : ∀ᶠ n in atTop, 0 < saturationGap A h n)
    (htail :
      Tendsto
        (fun n : ℕ =>
          saturationGap A h n / (B * (n : ℝ) ^ sigma))
        atTop (nhds 1))
    (t : ItemType m) :
    ∃ r : ℝ, 0 < r ∧
      ∀ᶠ N : ℕ in atTop,
        r * (N : ℝ) < ((seq.allocation N).count t : ℝ) := by
  have hm_nat : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hm : 0 < (m : ℝ) := by exact_mod_cast hm_nat
  let u : ℝ := 1 / (m : ℝ)
  have hu_pos : 0 < u := by
    dsimp [u]
    exact one_div_pos.mpr hm
  let c : ℝ := u / 2
  have hc_pos : 0 < c := by
    dsimp [c]
    positivity
  have hc_uniform : c < 1 / (m : ℝ) := by
    dsimp [c, u]
    linarith
  let C : ℝ := (∑ i : ItemType m, p i) / p t
  have htotalWeight_pos : 0 < ∑ i : ItemType m, p i := by
    have hterm_le : p t ≤ ∑ i : ItemType m, p i :=
      Finset.single_le_sum (fun i _hi => (hp_pos i).le) (Finset.mem_univ t)
    exact lt_of_lt_of_le (hp_pos t) hterm_le
  have hC_pos : 0 < C := by
    dsimp [C]
    exact div_pos htotalWeight_pos (hp_pos t)
  obtain ⟨r, hr_pos, hrc, hcoefficient⟩ :=
    exists_positive_power_fraction_with_coefficient_separation
      hC_pos hc_pos hsigma_neg
  refine ⟨r, hr_pos, ?_⟩
  apply eventually_optimalAllocation_count_gt_linear_of_power_tail
    p seq hp_pos hmono hB_pos hsigma_neg hgap_eventual_pos htail t
    hr_pos hrc hc_uniform
  simpa [C] using hcoefficient

/--
Source-shaped positive-linear interiority for corrected D.1(ii).  It derives
the only eventual-gap fact from the literal tail condition and leaves the
all-positive finite support explicit.
-/
theorem source_exists_eventual_positive_linear_lower_bound_of_power_tail
    {m : ℕ} [NeZero m] {A B sigma : ℝ} {h : ℕ → ℝ}
    (p : ItemType m → ℝ)
    (seq : AppliedModelingLib.Allocation.OptimalSequence
      (fun _ : ℕ => p) (fun _ : ℕ => fun _ : ItemType m => h))
    (hp_pos : ∀ i : ItemType m, 0 < p i)
    (hmono : Monotone h)
    (hB_pos : 0 < B) (hsigma_neg : sigma < 0)
    (htail :
      Tendsto
        (fun n : ℕ =>
          saturationGap A h n / (B * (n : ℝ) ^ sigma))
        atTop (nhds 1))
    (t : ItemType m) :
    ∃ r : ℝ, 0 < r ∧
      ∀ᶠ N : ℕ in atTop,
        r * (N : ℝ) < ((seq.allocation N).count t : ℝ) := by
  exact exists_eventual_positive_linear_lower_bound_of_power_tail
    p seq hp_pos hmono hB_pos hsigma_neg
    (eventually_saturationGap_pos_of_power_tail hB_pos hsigma_neg htail)
    htail t

/--
The raw weighted saturation deficit of every selected optimizer vanishes.
This records the useful conclusion of the repaired source comparison without
turning a quotient of two vanishing deficits into an assumption.
-/
theorem tendsto_optimal_weighted_saturationGap_sum_nhds_zero_of_power_tail
    {m : ℕ} [NeZero m] {A B sigma : ℝ} {h : ℕ → ℝ}
    (p : ItemType m → ℝ)
    (seq : AppliedModelingLib.Allocation.OptimalSequence
      (fun _ : ℕ => p) (fun _ : ℕ => fun _ : ItemType m => h))
    (hp_pos : ∀ i : ItemType m, 0 < p i)
    (hmono : Monotone h)
    (hB_pos : 0 < B) (hsigma_neg : sigma < 0)
    (hgap_eventual_pos : ∀ᶠ a : ℕ in atTop, 0 < saturationGap A h a)
    (htail :
      Tendsto
        (fun a : ℕ =>
          saturationGap A h a / (B * (a : ℝ) ^ sigma))
        atTop (nhds 1)) :
    Tendsto
      (fun N : ℕ =>
        ∑ i : ItemType m,
          p i * saturationGap A h ((seq.allocation N).count i))
      atTop (nhds 0) := by
  have hgap_pos : ∀ a : ℕ, 0 < saturationGap A h a :=
    saturationGap_pos_of_monotone_of_eventually_pos hmono hgap_eventual_pos
  have hbalanced_zero :=
    tendsto_balanced_weighted_saturationGap_sum_nhds_zero_of_power_tail
      p hB_pos hsigma_neg htail
  refine squeeze_zero ?_ ?_ hbalanced_zero
  · intro N
    exact Finset.sum_nonneg
      (fun i _hi => mul_nonneg (hp_pos i).le (hgap_pos _).le)
  · intro N
    exact weighted_saturationGap_sum_le_of_optimal
      (A := A) p seq N (balancedAllocation m N)
      (balancedAllocation_feasible (m := m) N)

end AppendixD1GenericII
end PRPKG24AccuracyDiversity
