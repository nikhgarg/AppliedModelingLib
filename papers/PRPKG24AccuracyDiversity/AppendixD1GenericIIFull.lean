import PRPKG24AccuracyDiversity.AppendixD1GenericII
import PRPKG24AccuracyDiversity.AppendixD1GenericIII
import PRPKG24AccuracyDiversity.AppendixD1GenericPower
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Corrected generic Appendix D.1(ii), full endpoint

This module is intentionally separate from the raw-interiority core in
`AppendixD1GenericII`.  It will derive the negative-power limiting
minimization and compact stability argument from literal integer optimality.
-/

open Filter Topology
open scoped BigOperators

namespace PRPKG24AccuracyDiversity
namespace AppendixD1GenericIIFull

open AppliedModelingLib
open AppendixD1GenericII
open AppendixD1GenericIII
open AppendixD1GenericPower

/-- The corrected D.1(ii) target weight. -/
noncomputable def targetWeight
    {m : ℕ} (p : ItemType m → ℝ) (sigma : ℝ) (i : ItemType m) : ℝ :=
  sourcePowerWeight p sigma i

/-- The corrected D.1(ii) target share. -/
noncomputable def targetShare
    {m : ℕ} (p : ItemType m → ℝ) (sigma : ℝ) (i : ItemType m) : ℝ :=
  normalizedWeight (targetWeight p sigma) i

/-- The continuous negative-power deficit objective derived from the source tail. -/
noncomputable def weightedNegativePowerObjective
    {m : ℕ} (p : ItemType m → ℝ) (sigma : ℝ) (x : ItemType m → ℝ) : ℝ :=
  ∑ i : ItemType m, p i * x i ^ sigma

theorem targetWeight_pos
    {m : ℕ} (p : ItemType m → ℝ) {sigma : ℝ}
    (hsigma_lt_one : sigma < 1) (hp_pos : ∀ i, 0 < p i)
    (i : ItemType m) :
    0 < targetWeight p sigma i := by
  exact sourcePowerWeight_pos p hsigma_lt_one hp_pos i

theorem targetShare_pos
    {m : ℕ} [NeZero m] (p : ItemType m → ℝ) {sigma : ℝ}
    (hsigma_lt_one : sigma < 1) (hp_pos : ∀ i, 0 < p i)
    (i : ItemType m) :
    0 < targetShare p sigma i := by
  exact normalizedWeight_pos (targetWeight p sigma)
    (fun j => targetWeight_pos p hsigma_lt_one hp_pos j) i

theorem sum_targetShare_eq_one
    {m : ℕ} [NeZero m] (p : ItemType m → ℝ) {sigma : ℝ}
    (hsigma_lt_one : sigma < 1) (hp_pos : ∀ i, 0 < p i) :
    (∑ i : ItemType m, targetShare p sigma i) = 1 := by
  exact sum_normalizedWeight_eq_one (targetWeight p sigma)
    (fun j => targetWeight_pos p hsigma_lt_one hp_pos j)

/-- The transformed source weights recover the original likelihood weights. -/
theorem targetWeight_power_eq
    {m : ℕ} (p : ItemType m → ℝ) {sigma : ℝ}
    (hsigma_lt_one : sigma < 1) (hp_pos : ∀ i, 0 < p i)
    (i : ItemType m) :
    targetWeight p sigma i ^ (1 - sigma) = p i := by
  exact sourcePowerWeight_power_eq p hsigma_lt_one hp_pos i

/-- The target's negative-power value has the expected closed form. -/
theorem weightedNegativePowerObjective_target
    {m : ℕ} [NeZero m] (p : ItemType m → ℝ) {sigma : ℝ}
    (hsigma_lt_one : sigma < 1) (hp_pos : ∀ i, 0 < p i) :
    weightedNegativePowerObjective p sigma (targetShare p sigma) =
      (∑ i : ItemType m, targetWeight p sigma i) ^ (1 - sigma) := by
  let W : ℝ := ∑ i : ItemType m, targetWeight p sigma i
  have hW_pos : 0 < W := by
    dsimp [W]
    exact Finset.sum_pos
      (fun i _ => targetWeight_pos p hsigma_lt_one hp_pos i)
      Finset.univ_nonempty
  have hW_ne : W ≠ 0 := ne_of_gt hW_pos
  unfold weightedNegativePowerObjective targetShare normalizedWeight
  change (∑ i : ItemType m, p i *
      (targetWeight p sigma i / W) ^ sigma) = W ^ (1 - sigma)
  calc
    (∑ i : ItemType m, p i *
        (targetWeight p sigma i / W) ^ sigma) =
        ∑ i : ItemType m, targetWeight p sigma i / W ^ sigma := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [Real.div_rpow (targetWeight_pos p hsigma_lt_one hp_pos i).le hW_pos.le]
          have hweight := targetWeight_power_eq p hsigma_lt_one hp_pos i
          have hfactor : targetWeight p sigma i =
              targetWeight p sigma i ^ (1 - sigma) *
                targetWeight p sigma i ^ sigma := by
            calc
              targetWeight p sigma i = targetWeight p sigma i ^ 1 :=
                (Real.rpow_one _).symm
              _ = targetWeight p sigma i ^ ((1 - sigma) + sigma) := by
                congr 1
                ring
              _ = targetWeight p sigma i ^ (1 - sigma) *
                  targetWeight p sigma i ^ sigma :=
                Real.rpow_add (targetWeight_pos p hsigma_lt_one hp_pos i)
                  (1 - sigma) sigma
          rw [← hweight]
          calc
            targetWeight p sigma i ^ (1 - sigma) *
                (targetWeight p sigma i ^ sigma / W ^ sigma) =
                (targetWeight p sigma i ^ (1 - sigma) *
                  targetWeight p sigma i ^ sigma) / W ^ sigma := by ring
            _ = targetWeight p sigma i / W ^ sigma := by rw [← hfactor]
    _ = W / W ^ sigma := by
      rw [← Finset.sum_div]
    _ = W ^ (1 - sigma) := by
      have hWfactor : W = W ^ (1 - sigma) * W ^ sigma := by
        calc
          W = W ^ 1 := (Real.rpow_one _).symm
          _ = W ^ ((1 - sigma) + sigma) := by
            congr 1
            ring
          _ = W ^ (1 - sigma) * W ^ sigma :=
            Real.rpow_add hW_pos (1 - sigma) sigma
      calc
        W / W ^ sigma =
            (W ^ (1 - sigma) * W ^ sigma) / W ^ sigma := by rw [← hWfactor]
        _ = W ^ (1 - sigma) := by
              field_simp [ne_of_gt (Real.rpow_pos_of_pos hW_pos sigma)]

/-! The next checkpoint isolates the continuous variational lower bound. -/

/-- The continuous negative-power objective is nonnegative on the positive simplex. -/
theorem weightedNegativePowerObjective_nonneg
    {m : ℕ} (p : ItemType m → ℝ) (sigma : ℝ) (x : ItemType m → ℝ)
    (hp_pos : ∀ i, 0 < p i) (hx_pos : ∀ i, 0 < x i) :
    0 ≤ weightedNegativePowerObjective p sigma x := by
  unfold weightedNegativePowerObjective
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (hp_pos i).le (Real.rpow_nonneg (hx_pos i).le sigma)

/--
The corrected target minimizes the continuous negative-power objective on the
strictly positive simplex.  This is a direct Holder argument; it is not an
optimizer or convergence certificate.
-/
theorem weightedNegativePowerObjective_target_le
    {m : ℕ} [NeZero m] (p : ItemType m → ℝ) {sigma : ℝ}
    (hsigma_neg : sigma < 0) (hp_pos : ∀ i, 0 < p i)
    (x : ItemType m → ℝ) (hx_pos : ∀ i, 0 < x i)
    (hx_sum : (∑ i : ItemType m, x i) = 1) :
    weightedNegativePowerObjective p sigma (targetShare p sigma) ≤
      weightedNegativePowerObjective p sigma x := by
  let r : ℝ := 1 - sigma
  let s : ℝ := r / (r - 1)
  let W : ℝ := ∑ i : ItemType m, targetWeight p sigma i
  let f : ItemType m → ℝ := fun i =>
    targetWeight p sigma i * x i ^ (sigma / r)
  let g : ItemType m → ℝ := fun i => x i ^ (-sigma / r)
  have hr_one : 1 < r := by
    dsimp [r]
    linarith
  have hr_pos : 0 < r := lt_trans zero_lt_one hr_one
  have hr_ne : r ≠ 0 := ne_of_gt hr_pos
  have hs_holder : r.HolderConjugate s := by
    dsimp [s]
    simpa [Real.conjExponent] using Real.HolderConjugate.conjExponent hr_one
  have hW_pos : 0 < W := by
    dsimp [W]
    exact Finset.sum_pos
      (fun i _ => targetWeight_pos p (by linarith) hp_pos i)
      Finset.univ_nonempty
  have hfg : (∑ i : ItemType m, f i * g i) = W := by
    dsimp [f, g, W]
    refine Finset.sum_congr rfl ?_
    intro i _
    calc
      (targetWeight p sigma i * x i ^ (sigma / r)) *
          x i ^ (-sigma / r) =
          targetWeight p sigma i *
            (x i ^ (sigma / r) * x i ^ (-sigma / r)) := by ring
      _ = targetWeight p sigma i * x i ^ (sigma / r + -sigma / r) := by
        rw [← Real.rpow_add (hx_pos i)]
      _ = targetWeight p sigma i := by
        have hexp : sigma / r + -sigma / r = 0 := by ring
        rw [hexp, Real.rpow_zero, mul_one]
  have hfr : ∀ i : ItemType m, f i ^ r = p i * x i ^ sigma := by
    intro i
    dsimp [f]
    rw [Real.mul_rpow (targetWeight_pos p (by linarith) hp_pos i).le
      (Real.rpow_nonneg (hx_pos i).le _)]
    rw [← Real.rpow_mul (hx_pos i).le]
    have hexp : (sigma / r) * r = sigma := by
      field_simp [hr_ne]
    rw [hexp, targetWeight_power_eq p (by linarith) hp_pos i]
  have hgs : ∀ i : ItemType m, g i ^ s = x i := by
    intro i
    dsimp [g]
    rw [← Real.rpow_mul (hx_pos i).le]
    have hrs : (-sigma / r) * s = 1 := by
      have hsigma_ne : sigma ≠ 0 := ne_of_lt hsigma_neg
      have hr_sub : r - 1 = -sigma := by
        dsimp [r]
        ring
      calc
        (-sigma / r) * s = (-sigma / r) * (r / (r - 1)) := by rfl
        _ = -sigma / (r - 1) := by field_simp [hr_ne]
        _ = 1 := by rw [hr_sub]; field_simp [hsigma_ne]
    rw [hrs, Real.rpow_one]
  have hf_nonneg : ∀ i ∈ Finset.univ, 0 ≤ f i := by
    intro i _
    dsimp [f]
    exact mul_nonneg
      (targetWeight_pos p (by linarith) hp_pos i).le
      (Real.rpow_nonneg (hx_pos i).le _)
  have hg_nonneg : ∀ i ∈ Finset.univ, 0 ≤ g i := by
    intro i _
    exact Real.rpow_nonneg (hx_pos i).le _
  have hholder := Real.inner_le_Lp_mul_Lq_of_nonneg
    (s := Finset.univ) hs_holder hf_nonneg hg_nonneg
  have hholder' : W ≤ weightedNegativePowerObjective p sigma x ^ (1 / r) := by
    calc
      W = ∑ i : ItemType m, f i * g i := hfg.symm
      _ ≤ (∑ i : ItemType m, f i ^ r) ^ (1 / r) *
          (∑ i : ItemType m, g i ^ s) ^ (1 / s) := hholder
      _ = weightedNegativePowerObjective p sigma x ^ (1 / r) := by
        have hsum_f : (∑ i : ItemType m, f i ^ r) =
            weightedNegativePowerObjective p sigma x := by
          unfold weightedNegativePowerObjective
          exact Finset.sum_congr rfl (fun i _ => hfr i)
        have hsum_g : (∑ i : ItemType m, g i ^ s) = 1 := by
          calc
            (∑ i : ItemType m, g i ^ s) = ∑ i : ItemType m, x i :=
              Finset.sum_congr rfl (fun i _ => hgs i)
            _ = 1 := hx_sum
        rw [hsum_f, hsum_g]
        simp
  have hF_nonneg : 0 ≤ weightedNegativePowerObjective p sigma x :=
    weightedNegativePowerObjective_nonneg p sigma x hp_pos hx_pos
  have hraised := Real.rpow_le_rpow hW_pos.le hholder' hr_pos.le
  have hW_le : W ^ r ≤ weightedNegativePowerObjective p sigma x := by
    calc
      W ^ r ≤ (weightedNegativePowerObjective p sigma x ^ (1 / r)) ^ r := hraised
      _ = weightedNegativePowerObjective p sigma x ^ ((1 / r) * r) :=
        (Real.rpow_mul hF_nonneg (1 / r) r).symm
      _ = weightedNegativePowerObjective p sigma x := by
        have hinv : (1 / r) * r = 1 := by field_simp [hr_ne]
        rw [hinv, Real.rpow_one]
  rw [weightedNegativePowerObjective_target p (by linarith) hp_pos]
  simpa [W, r] using hW_le

/-- A negative real power is strictly convex on the positive half-line. -/
theorem strictConvexOn_rpow_of_neg {sigma : ℝ} (hsigma_neg : sigma < 0) :
    StrictConvexOn ℝ (Set.Ioi 0) (fun z : ℝ => z ^ sigma) := by
  apply strictConvexOn_of_deriv2_pos' (convex_Ioi 0)
  · intro z hz
    exact (continuousAt_id.rpow_const
      (Or.inl (ne_of_gt hz))).continuousWithinAt
  intro z hz
  rw [Real.iter_deriv_rpow_const sigma z 2]
  simp [descPochhammer]
  have hz_pos : 0 < z := hz
  have hpow_pos : 0 < z ^ (sigma - 2) := Real.rpow_pos_of_pos hz_pos _
  have hcoefficient_pos : 0 < sigma * (sigma - 1) :=
    mul_pos_of_neg_of_neg (by linarith) (by linarith)
  exact mul_pos hcoefficient_pos hpow_pos

/-- The corrected target is the unique minimizer on the positive simplex. -/
theorem weightedNegativePowerObjective_target_lt_of_ne
    {m : ℕ} [NeZero m] (p : ItemType m → ℝ) {sigma : ℝ}
    (hsigma_neg : sigma < 0) (hp_pos : ∀ i, 0 < p i)
    (x : ItemType m → ℝ) (hx_pos : ∀ i, 0 < x i)
    (hx_sum : (∑ i : ItemType m, x i) = 1)
    (hx_ne : x ≠ targetShare p sigma) :
    weightedNegativePowerObjective p sigma (targetShare p sigma) <
      weightedNegativePowerObjective p sigma x := by
  let q : ItemType m → ℝ := targetShare p sigma
  let W : ℝ := ∑ i : ItemType m, targetWeight p sigma i
  let z : ItemType m → ℝ := fun i => x i / q i
  have hq_pos : ∀ i, 0 < q i := by
    intro i
    exact targetShare_pos p (by linarith) hp_pos i
  have hq_sum : (∑ i : ItemType m, q i) = 1 := by
    dsimp [q]
    exact sum_targetShare_eq_one p (by linarith) hp_pos
  have hW_pos : 0 < W := by
    dsimp [W]
    exact Finset.sum_pos
      (fun i _ => targetWeight_pos p (by linarith) hp_pos i)
      Finset.univ_nonempty
  have hz_pos : ∀ i, 0 < z i := by
    intro i
    dsimp [z]
    exact div_pos (hx_pos i) (hq_pos i)
  have hmean : (∑ i : ItemType m, q i * z i) = 1 := by
    calc
      (∑ i : ItemType m, q i * z i) = ∑ i : ItemType m, x i := by
        refine Finset.sum_congr rfl ?_
        intro i _
        dsimp [z]
        field_simp [ne_of_gt (hq_pos i)]
      _ = 1 := hx_sum
  have hnonconstant : ∃ j ∈ Finset.univ, ∃ k ∈ Finset.univ, z j ≠ z k := by
    by_contra hnot
    push Not at hnot
    let anchor : ItemType m := Classical.choice (inferInstance : Nonempty (ItemType m))
    have hconstant : ∀ i : ItemType m, z i = z anchor := by
      intro i
      exact hnot i (Finset.mem_univ i) anchor (Finset.mem_univ anchor)
    have hmean_constant : (∑ i : ItemType m, q i * z i) = z anchor := by
      calc
        (∑ i : ItemType m, q i * z i) =
            ∑ i : ItemType m, q i * z anchor := by
              exact Finset.sum_congr rfl (fun i _ => by rw [hconstant i])
        _ = (∑ i : ItemType m, q i) * z anchor := by rw [Finset.sum_mul]
        _ = z anchor := by rw [hq_sum, one_mul]
    have hanchor_one : z anchor = 1 := by linarith [hmean, hmean_constant]
    apply hx_ne
    funext i
    have hzi_one : z i = 1 := (hconstant i).trans hanchor_one
    dsimp [z] at hzi_one
    have hxi : x i = q i := by
      field_simp [ne_of_gt (hq_pos i)] at hzi_one
      linarith
    simpa [q] using hxi
  have hjensen := (strictConvexOn_rpow_of_neg hsigma_neg).map_sum_lt
    (t := Finset.univ) (w := q) (p := z)
    (fun i _ => hq_pos i)
    hq_sum
    (fun i _ => hz_pos i)
    hnonconstant
  have hjensen' : 1 < ∑ i : ItemType m, q i * z i ^ sigma := by
    simpa only [smul_eq_mul, hmean, Real.one_rpow] using hjensen
  have hweight_eq : ∀ i : ItemType m, targetWeight p sigma i = W * q i := by
    intro i
    change targetWeight p sigma i = W * (targetWeight p sigma i / W)
    field_simp [ne_of_gt hW_pos]
  have hterm : ∀ i : ItemType m,
      p i * x i ^ sigma = W ^ (1 - sigma) * (q i * z i ^ sigma) := by
    intro i
    have hqz : x i = q i * z i := by
      dsimp [z]
      field_simp [ne_of_gt (hq_pos i)]
    calc
      p i * x i ^ sigma =
          targetWeight p sigma i ^ (1 - sigma) * (q i * z i) ^ sigma := by
            rw [targetWeight_power_eq p (by linarith) hp_pos i, hqz]
      _ = (W * q i) ^ (1 - sigma) * (q i * z i) ^ sigma := by
            rw [hweight_eq i]
      _ = (W ^ (1 - sigma) * q i ^ (1 - sigma)) *
          (q i ^ sigma * z i ^ sigma) := by
            rw [Real.mul_rpow hW_pos.le (hq_pos i).le,
              Real.mul_rpow (hq_pos i).le (hz_pos i).le]
      _ = W ^ (1 - sigma) * (q i * z i ^ sigma) := by
            have hqfactor : q i ^ (1 - sigma) * q i ^ sigma = q i := by
              calc
                q i ^ (1 - sigma) * q i ^ sigma =
                    q i ^ ((1 - sigma) + sigma) := by
                      rw [← Real.rpow_add (hq_pos i)]
                _ = q i := by
                      have hexp : (1 - sigma) + sigma = (1 : ℝ) := by ring
                      rw [hexp, Real.rpow_one]
            calc
              (W ^ (1 - sigma) * q i ^ (1 - sigma)) *
                  (q i ^ sigma * z i ^ sigma) =
                  W ^ (1 - sigma) *
                    ((q i ^ (1 - sigma) * q i ^ sigma) * z i ^ sigma) := by
                      ring
              _ = W ^ (1 - sigma) * (q i * z i ^ sigma) := by rw [hqfactor]
  have hobjective_eq : weightedNegativePowerObjective p sigma x =
      W ^ (1 - sigma) * (∑ i : ItemType m, q i * z i ^ sigma) := by
    unfold weightedNegativePowerObjective
    calc
      (∑ i : ItemType m, p i * x i ^ sigma) =
          ∑ i : ItemType m, W ^ (1 - sigma) * (q i * z i ^ sigma) :=
            Finset.sum_congr rfl (fun i _ => hterm i)
      _ = W ^ (1 - sigma) * (∑ i : ItemType m, q i * z i ^ sigma) := by
            rw [Finset.mul_sum]
  have hscale_pos : 0 < W ^ (1 - sigma) :=
    Real.rpow_pos_of_pos hW_pos _
  have hstrict : W ^ (1 - sigma) < weightedNegativePowerObjective p sigma x := by
    rw [hobjective_eq]
    nlinarith [mul_lt_mul_of_pos_left hjensen' hscale_pos]
  rw [weightedNegativePowerObjective_target p (by linarith) hp_pos]
  simpa [W] using hstrict

/-- Tail quotient algebra after normalizing a positive count by its total. -/
theorem saturationGapQuotient_mul_scaled_rpow
    {A B sigma : ℝ} {h : ℕ → ℝ} {a N : ℕ}
    (hB_ne : B ≠ 0) (ha_pos : 0 < a) (hN_pos : 0 < N) :
    (saturationGap A h a / (B * (a : ℝ) ^ sigma)) *
        ((a : ℝ) / (N : ℝ)) ^ sigma =
      saturationGap A h a / (B * (N : ℝ) ^ sigma) := by
  have ha_real_pos : 0 < (a : ℝ) := by exact_mod_cast ha_pos
  have hN_real_pos : 0 < (N : ℝ) := by exact_mod_cast hN_pos
  have ha_pow_ne : (a : ℝ) ^ sigma ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos ha_real_pos sigma)
  have hN_pow_ne : (N : ℝ) ^ sigma ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hN_real_pos sigma)
  rw [Real.div_rpow ha_real_pos.le hN_real_pos.le]
  field_simp [hB_ne, ha_pow_ne, hN_pow_ne]

/--
A literal finite allocation family whose counts and shares converge to a
positive profile has the corresponding normalized saturation-deficit limit.
All asymptotic factors are derived from the displayed tail quotient.
-/
theorem tendsto_normalized_weighted_saturationGap_of_power_tail
    {m : ℕ} [NeZero m] {A B sigma : ℝ} {h : ℕ → ℝ}
    (p : ItemType m → ℝ) (a : ℕ → CountAllocation m)
    (r : ItemType m → ℝ)
    (hB_pos : 0 < B)
    (htail : Tendsto
      (fun n : ℕ => saturationGap A h n / (B * (n : ℝ) ^ sigma))
      atTop (nhds 1))
    (htotal : ∀ N, AppliedModelingLib.Allocation.total (a N) = N)
    (hcounts : ∀ i, Tendsto (fun N : ℕ => (a N).count i) atTop atTop)
    (hshare : ∀ i, Tendsto
      (fun N : ℕ => AppliedModelingLib.Allocation.share (a N) i) atTop (nhds (r i)))
    (hr_pos : ∀ i, 0 < r i) :
    Tendsto
      (fun N : ℕ =>
        (∑ i : ItemType m, p i * saturationGap A h ((a N).count i)) /
          (B * (N : ℝ) ^ sigma))
      atTop (nhds (weightedNegativePowerObjective p sigma r)) := by
  have hterms : ∀ i : ItemType m,
      Tendsto
        (fun N : ℕ =>
          p i * saturationGap A h ((a N).count i) /
            (B * (N : ℝ) ^ sigma))
        atTop (nhds (p i * r i ^ sigma)) := by
    intro i
    have hquot : Tendsto
        (fun N : ℕ =>
          saturationGap A h ((a N).count i) /
            (B * (((a N).count i : ℕ) : ℝ) ^ sigma))
        atTop (nhds 1) := by
      exact htail.comp (hcounts i)
    have hshare_pow : Tendsto
        (fun N : ℕ => AppliedModelingLib.Allocation.share (a N) i ^ sigma)
        atTop (nhds (r i ^ sigma)) :=
      (hshare i).rpow_const (Or.inl (ne_of_gt (hr_pos i)))
    have hprod_base := (tendsto_const_nhds (x := p i)).mul
      (hquot.mul hshare_pow)
    have hprod : Tendsto
        (fun N : ℕ => p i *
          (saturationGap A h ((a N).count i) /
            (B * (((a N).count i : ℕ) : ℝ) ^ sigma) *
            AppliedModelingLib.Allocation.share (a N) i ^ sigma))
        atTop (nhds (p i * r i ^ sigma)) := by
      simpa [one_mul] using hprod_base
    refine hprod.congr' ?_
    filter_upwards [(hcounts i).eventually_gt_atTop 0, eventually_gt_atTop 0]
      with N hcount_pos hN_pos
    have htotal_ne : AppliedModelingLib.Allocation.total (a N) ≠ 0 := by
      rw [htotal N]
      exact Nat.ne_of_gt hN_pos
    have hshare_eq : AppliedModelingLib.Allocation.share (a N) i =
        ((a N).count i : ℝ) / (N : ℝ) := by
      rw [AppliedModelingLib.Allocation.share_eq_div_of_total_ne_zero
        (a := a N) (k := i) htotal_ne, htotal N]
    have htail_eq := saturationGapQuotient_mul_scaled_rpow
      (A := A) (h := h) (sigma := sigma) (ne_of_gt hB_pos) hcount_pos hN_pos
    rw [hshare_eq]
    calc
      p i *
          ((saturationGap A h ((a N).count i) /
            (B * (((a N).count i : ℕ) : ℝ) ^ sigma)) *
            (((a N).count i : ℝ) / (N : ℝ)) ^ sigma) =
          p i * (saturationGap A h ((a N).count i) /
            (B * (N : ℝ) ^ sigma)) := by
            rw [htail_eq]
      _ = p i * saturationGap A h ((a N).count i) /
          (B * (N : ℝ) ^ sigma) := by ring
  have hsum := tendsto_finset_sum Finset.univ
    (fun i _ => hterms i)
  simpa [weightedNegativePowerObjective, Finset.sum_div] using hsum

/-- The internally rounded corrected target is a literal feasible comparator. -/
theorem tendsto_targetIntegerCompetitor_normalized_saturationGap_of_power_tail
    {m : ℕ} [NeZero m] {A B sigma : ℝ} {h : ℕ → ℝ}
    (p : ItemType m → ℝ)
    (hB_pos : 0 < B)
    (hsigma_neg : sigma < 0)
    (htail : Tendsto
      (fun n : ℕ => saturationGap A h n / (B * (n : ℝ) ^ sigma))
      atTop (nhds 1))
    (hp_pos : ∀ i, 0 < p i) :
    Tendsto
      (fun N : ℕ =>
        (∑ i : ItemType m,
          p i * saturationGap A h
            ((normalizedIntegerCompetitor (targetWeight p sigma) N).count i)) /
          (B * (N : ℝ) ^ sigma))
      atTop (nhds (weightedNegativePowerObjective p sigma (targetShare p sigma))) := by
  exact tendsto_normalized_weighted_saturationGap_of_power_tail
    p (normalizedIntegerCompetitor (targetWeight p sigma)) (targetShare p sigma)
    hB_pos htail
    (fun N => normalizedIntegerCompetitor_total (targetWeight p sigma)
      (fun i => targetWeight_pos p (by linarith) hp_pos i) N)
    (fun i => tendsto_normalizedIntegerCompetitor_count_atTop
      (targetWeight p sigma)
      (fun j => targetWeight_pos p (by linarith) hp_pos j) i)
    (fun i => by
      simpa [targetShare] using
        tendsto_normalizedIntegerCompetitor_share_nhds_normalizedWeight
          (targetWeight p sigma)
          (fun j => targetWeight_pos p (by linarith) hp_pos j) i)
    (fun i => targetShare_pos p (by linarith) hp_pos i)

/--
The selected literal optimizer's normalized deficit is eventually bounded
below by the negative-power objective of its own share vector.  This is the
raw, direction-correct replacement for the source's invalid ratio of two
vanishing objective values.
-/
theorem eventually_negativePowerObjective_le_normalized_selected_saturationGap
    {m : ℕ} [NeZero m] {A B sigma : ℝ} {h : ℕ → ℝ}
    (p : ItemType m → ℝ)
    (seq : AppliedModelingLib.Allocation.OptimalSequence
      (fun _ : ℕ => p) (fun _ : ℕ => fun _ : ItemType m => h))
    (hp_pos : ∀ i, 0 < p i)
    (hmono : Monotone h)
    (hB_pos : 0 < B) (hsigma_neg : sigma < 0)
    (htail : Tendsto
      (fun n : ℕ => saturationGap A h n / (B * (n : ℝ) ^ sigma))
      atTop (nhds 1))
    {delta : ℝ} (hdelta_pos : 0 < delta) :
    ∀ᶠ N : ℕ in atTop,
      (1 - delta) * weightedNegativePowerObjective p sigma
          (fun i => AppliedModelingLib.Allocation.share (seq.allocation N) i) ≤
        (∑ i : ItemType m,
          p i * saturationGap A h ((seq.allocation N).count i)) /
          (B * (N : ℝ) ^ sigma) := by
  have hcounts : ∀ i : ItemType m,
      Tendsto (fun N : ℕ => (seq.allocation N).count i) atTop atTop := by
    intro i
    exact source_tendsto_optimalAllocation_count_atTop_of_power_tail
      p seq hp_pos hmono hB_pos hsigma_neg htail i
  have hcount_pos : ∀ᶠ N : ℕ in atTop, ∀ i : ItemType m,
      0 < (seq.allocation N).count i := by
    refine Filter.eventually_all.2 ?_
    intro i
    exact (hcounts i).eventually_gt_atTop 0
  have hquot_lower : ∀ᶠ N : ℕ in atTop, ∀ i : ItemType m,
      1 - delta < saturationGap A h ((seq.allocation N).count i) /
        (B * (((seq.allocation N).count i : ℕ) : ℝ) ^ sigma) := by
    refine Filter.eventually_all.2 ?_
    intro i
    exact (htail.comp (hcounts i))
      (Ioi_mem_nhds (by linarith))
  filter_upwards [eventually_gt_atTop 0, hcount_pos, hquot_lower]
    with N hN_pos hcountN hquotN
  have htotal_ne : AppliedModelingLib.Allocation.total (seq.allocation N) ≠ 0 := by
    rw [(seq.optimal N).1]
    exact Nat.ne_of_gt hN_pos
  have hraw_eq :
      (∑ i : ItemType m,
        p i * saturationGap A h ((seq.allocation N).count i)) /
          (B * (N : ℝ) ^ sigma) =
        ∑ i : ItemType m, p i *
          ((saturationGap A h ((seq.allocation N).count i) /
            (B * (((seq.allocation N).count i : ℕ) : ℝ) ^ sigma)) *
            AppliedModelingLib.Allocation.share (seq.allocation N) i ^ sigma) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl ?_
    intro i _
    have hshare_eq : AppliedModelingLib.Allocation.share (seq.allocation N) i =
        ((seq.allocation N).count i : ℝ) / (N : ℝ) := by
      rw [AppliedModelingLib.Allocation.share_eq_div_of_total_ne_zero
        (a := seq.allocation N) (k := i) htotal_ne, (seq.optimal N).1]
    have htail_eq := saturationGapQuotient_mul_scaled_rpow
      (A := A) (h := h) (sigma := sigma) (ne_of_gt hB_pos)
      (hcountN i) hN_pos
    rw [hshare_eq]
    calc
      p i * saturationGap A h ((seq.allocation N).count i) /
          (B * (N : ℝ) ^ sigma) =
          p i * (saturationGap A h ((seq.allocation N).count i) /
            (B * (N : ℝ) ^ sigma)) := by ring
      _ = p i *
          ((saturationGap A h ((seq.allocation N).count i) /
            (B * (((seq.allocation N).count i : ℕ) : ℝ) ^ sigma)) *
            (((seq.allocation N).count i : ℝ) / (N : ℝ)) ^ sigma) := by
            rw [htail_eq]
  rw [hraw_eq]
  unfold weightedNegativePowerObjective
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum ?_
  intro i _
  have hshare_pow_nonneg : 0 ≤
      AppliedModelingLib.Allocation.share (seq.allocation N) i ^ sigma :=
    Real.rpow_nonneg
      (AppliedModelingLib.Allocation.share_nonneg (seq.allocation N) i) sigma
  have hbase := mul_le_mul_of_nonneg_right (hquotN i).le hshare_pow_nonneg
  have hscaled := mul_le_mul_of_nonneg_left hbase (hp_pos i).le
  convert hscaled using 1 ; ring

/-- The negative-power objective is continuous on every positive finite domain. -/
theorem continuousOn_weightedNegativePowerObjective_of_forall_pos
    {m : ℕ} (p : ItemType m → ℝ) (sigma : ℝ) :
    ContinuousOn (weightedNegativePowerObjective p sigma)
      {x : ItemType m → ℝ | ∀ i, 0 < x i} := by
  classical
  unfold weightedNegativePowerObjective
  refine continuousOn_finset_sum Finset.univ ?_
  intro i _
  exact continuousOn_const.mul
    ((continuous_apply i).continuousOn.rpow_const
      (fun x hx => Or.inl (ne_of_gt (hx i))))

/--
Corrected generic Lemma D.1(ii).  For strictly positive finite weights and a
literal fixed-total optimizer, the displayed negative-power saturation tail
forces the optimizer shares to converge to the profile proportional to
`p_i ^ (1 / (1 - sigma))`.  Interiority, the rounded comparator, normalized
tail bounds, and compact strict separation are all derived internally.
-/
theorem corrected_lemmaD1_ii_powerTail_optimizer_shares
    {m : ℕ} [NeZero m] {A B sigma : ℝ} {h : ℕ → ℝ}
    (p : ItemType m → ℝ)
    (seq : AppliedModelingLib.Allocation.OptimalSequence
      (fun _ : ℕ => p) (fun _ : ℕ => fun _ : ItemType m => h))
    (hp_pos : ∀ i, 0 < p i)
    (hmono : Monotone h)
    (hB_pos : 0 < B) (hsigma_neg : sigma < 0)
    (htail : Tendsto
      (fun n : ℕ => saturationGap A h n / (B * (n : ℝ) ^ sigma))
      atTop (nhds 1)) :
    seq.toSequence.ConvergesToProfile (targetShare p sigma) := by
  classical
  have hinterior : ∀ i : ItemType m, ∃ r : ℝ, 0 < r ∧
      ∀ᶠ N : ℕ in atTop,
        r * (N : ℝ) < ((seq.allocation N).count i : ℝ) := by
    intro i
    exact source_exists_eventual_positive_linear_lower_bound_of_power_tail
      p seq hp_pos hmono hB_pos hsigma_neg htail i
  choose r hr_pos hr_linear using hinterior
  let q : ItemType m → ℝ := targetShare p sigma
  let lower : ItemType m → ℝ := fun i =>
    min (r i / 2) (q i / 2)
  let s : Set (ItemType m → ℝ) :=
    stdSimplex ℝ (ItemType m) ∩
      {x : ItemType m → ℝ | ∀ i, lower i ≤ x i}
  have hq_pos : ∀ i, 0 < q i := by
    intro i
    dsimp [q]
    exact targetShare_pos p (by linarith) hp_pos i
  have hq_sum : (∑ i : ItemType m, q i) = 1 := by
    dsimp [q]
    exact sum_targetShare_eq_one p (by linarith) hp_pos
  have hlower_pos : ∀ i, 0 < lower i := by
    intro i
    dsimp [lower]
    exact lt_min (by linarith [hr_pos i]) (by linarith [hq_pos i])
  have hclosed_lower :
      IsClosed {x : ItemType m → ℝ | ∀ i, lower i ≤ x i} := by
    simpa [Set.setOf_forall] using
      (isClosed_iInter fun i : ItemType m =>
        (isClosed_le (continuous_const : Continuous fun _ : ItemType m → ℝ => lower i)
          (continuous_apply i)))
  have hscompact : IsCompact s := by
    dsimp [s]
    exact (isCompact_stdSimplex ℝ (ItemType m)).inter_right hclosed_lower
  have hs_pos : ∀ x : ItemType m → ℝ, x ∈ s → ∀ i, 0 < x i := by
    intro x hx i
    exact lt_of_lt_of_le (hlower_pos i) (hx.2 i)
  have hq_mem : q ∈ s := by
    constructor
    · constructor
      · intro i
        exact (hq_pos i).le
      · exact hq_sum
    · intro i
      dsimp [lower]
      exact (min_le_right _ _).trans (by linarith [hq_pos i])
  have hs_cont : ContinuousOn
      (fun x : ItemType m → ℝ => -weightedNegativePowerObjective p sigma x) s :=
    (continuousOn_weightedNegativePowerObjective_of_forall_pos p sigma).neg.mono
      (fun x hx => hs_pos x hx)
  have hs_strict : ∀ x : ItemType m → ℝ, x ∈ s → x ≠ q ->
      -weightedNegativePowerObjective p sigma x <
        -weightedNegativePowerObjective p sigma q := by
    intro x hx hx_ne
    have hmin : weightedNegativePowerObjective p sigma q <
        weightedNegativePowerObjective p sigma x := by
      simpa [q] using weightedNegativePowerObjective_target_lt_of_ne
        p hsigma_neg hp_pos x (hs_pos x hx) hx.1.2 (by simpa [q] using hx_ne)
    linarith
  have hshare_lower : ∀ᶠ N : ℕ in atTop, ∀ i : ItemType m,
      lower i ≤ AppliedModelingLib.Allocation.share (seq.allocation N) i := by
    refine Filter.eventually_all.2 ?_
    intro i
    filter_upwards [hr_linear i, eventually_gt_atTop 0] with N hlinearN hN_pos
    have htotal_ne : AppliedModelingLib.Allocation.total (seq.allocation N) ≠ 0 := by
      rw [(seq.optimal N).1]
      exact Nat.ne_of_gt hN_pos
    have hshare_eq : AppliedModelingLib.Allocation.share (seq.allocation N) i =
        ((seq.allocation N).count i : ℝ) / (N : ℝ) := by
      rw [AppliedModelingLib.Allocation.share_eq_div_of_total_ne_zero
        (a := seq.allocation N) (k := i) htotal_ne, (seq.optimal N).1]
    have hN_real_pos : 0 < (N : ℝ) := by exact_mod_cast hN_pos
    have hr_lt_share : r i < AppliedModelingLib.Allocation.share (seq.allocation N) i := by
      rw [hshare_eq]
      exact (lt_div_iff₀ hN_real_pos).2 hlinearN
    exact le_of_lt (calc
      lower i ≤ r i / 2 := min_le_left _ _
      _ < r i := by linarith [hr_pos i]
      _ < AppliedModelingLib.Allocation.share (seq.allocation N) i := hr_lt_share)
  have hactual_mem : ∀ᶠ N : ℕ in atTop,
      (fun i => AppliedModelingLib.Allocation.share (seq.allocation N) i) ∈ s := by
    filter_upwards [hshare_lower, eventually_gt_atTop 0] with N hlowerN hN_pos
    constructor
    · constructor
      · intro i
        exact AppliedModelingLib.Allocation.share_nonneg (seq.allocation N) i
      · exact AppliedModelingLib.Allocation.sum_share_eq_one_of_total_ne_zero
          (seq.allocation N) (by
            rw [(seq.optimal N).1]
            exact Nat.ne_of_gt hN_pos)
    · exact hlowerN
  intro t
  change Tendsto
    (fun N : ℕ => AppliedModelingLib.Allocation.share (seq.allocation N) t)
    atTop (nhds (q t))
  rw [Metric.tendsto_nhds]
  intro epsilon hepsilon_pos
  let epsilonHalf : ℝ := epsilon / 2
  have hepsilonHalf_pos : 0 < epsilonHalf := by
    dsimp [epsilonHalf]
    linarith
  obtain ⟨eta, heta_pos, hseparate⟩ :=
    exists_gap_on_isCompact_of_strict_unique_max s
      (fun x : ItemType m → ℝ => -weightedNegativePowerObjective p sigma x)
      q hscompact hs_cont hs_strict epsilonHalf hepsilonHalf_pos
  let V : ℝ := weightedNegativePowerObjective p sigma q
  let C : ℝ := ∑ i : ItemType m, p i * lower i ^ sigma
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact Finset.sum_nonneg fun i _ =>
      mul_nonneg (hp_pos i).le (Real.rpow_nonneg (hlower_pos i).le sigma)
  let D : ℝ := C + eta + 1
  have hD_pos : 0 < D := by
    dsimp [D]
    linarith
  have hC_lt_D : C < D := by
    dsimp [D]
    linarith
  let delta : ℝ := eta / (3 * D)
  have hdelta_pos : 0 < delta := by
    dsimp [delta]
    exact div_pos heta_pos (mul_pos (by norm_num) hD_pos)
  have hdeltaD : delta * D = eta / 3 := by
    dsimp [delta]
    field_simp [ne_of_gt hD_pos]
  have hdeltaC_lt : delta * C < eta / 3 := by
    calc
      delta * C < delta * D := mul_lt_mul_of_pos_left hC_lt_D hdelta_pos
      _ = eta / 3 := hdeltaD
  have hselected_lower :=
    eventually_negativePowerObjective_le_normalized_selected_saturationGap
      p seq hp_pos hmono hB_pos hsigma_neg htail hdelta_pos
  have hcandidate_limit :=
    tendsto_targetIntegerCompetitor_normalized_saturationGap_of_power_tail
      p hB_pos hsigma_neg htail hp_pos
  have hcandidate_upper : ∀ᶠ N : ℕ in atTop,
      (∑ i : ItemType m,
        p i * saturationGap A h
          ((normalizedIntegerCompetitor (targetWeight p sigma) N).count i)) /
          (B * (N : ℝ) ^ sigma) < V + eta / 3 := by
    have htarget_lt : weightedNegativePowerObjective p sigma (targetShare p sigma) <
        V + eta / 3 := by
      change V < V + eta / 3
      linarith
    have h := hcandidate_limit (Iio_mem_nhds htarget_lt)
    simpa [V, q] using h
  filter_upwards [hactual_mem, hselected_lower, hcandidate_upper,
    eventually_gt_atTop 0] with N hmemN hselectedN hcandidateN hN_pos
  have hN_real_pos : 0 < (N : ℝ) := by exact_mod_cast hN_pos
  have hden_pos : 0 < B * (N : ℝ) ^ sigma :=
    mul_pos hB_pos (Real.rpow_pos_of_pos hN_real_pos sigma)
  have hgap_opt := weighted_saturationGap_sum_le_of_optimal
    (A := A) p seq N (normalizedIntegerCompetitor (targetWeight p sigma) N)
    (normalizedIntegerCompetitor_total (targetWeight p sigma)
      (fun i => targetWeight_pos p (by linarith) hp_pos i) N)
  have hnormalized_opt :
      (∑ i : ItemType m,
        p i * saturationGap A h ((seq.allocation N).count i)) /
          (B * (N : ℝ) ^ sigma) ≤
        (∑ i : ItemType m,
          p i * saturationGap A h
            ((normalizedIntegerCompetitor (targetWeight p sigma) N).count i)) /
          (B * (N : ℝ) ^ sigma) :=
    (div_le_div_iff_of_pos_right hden_pos).2 hgap_opt
  have hobjective_le_C :
      weightedNegativePowerObjective p sigma
        (fun i => AppliedModelingLib.Allocation.share (seq.allocation N) i) ≤ C := by
    unfold weightedNegativePowerObjective C
    refine Finset.sum_le_sum ?_
    intro i _
    have hpow_le :
        AppliedModelingLib.Allocation.share (seq.allocation N) i ^ sigma ≤
          lower i ^ sigma :=
      Real.rpow_le_rpow_of_nonpos (hlower_pos i) (hmemN.2 i) hsigma_neg.le
    exact mul_le_mul_of_nonneg_left hpow_le (hp_pos i).le
  have hnormalized_lt :
      (1 - delta) * weightedNegativePowerObjective p sigma
          (fun i => AppliedModelingLib.Allocation.share (seq.allocation N) i) <
        V + eta / 3 :=
    lt_of_le_of_lt hselectedN (hnormalized_opt.trans_lt hcandidateN)
  have hobjective_lt :
      weightedNegativePowerObjective p sigma
        (fun i => AppliedModelingLib.Allocation.share (seq.allocation N) i) < V + eta := by
    have hscaled : delta *
        weightedNegativePowerObjective p sigma
          (fun i => AppliedModelingLib.Allocation.share (seq.allocation N) i) ≤ delta * C :=
      mul_le_mul_of_nonneg_left hobjective_le_C hdelta_pos.le
    have hsum_lt :
        (1 - delta) * weightedNegativePowerObjective p sigma
          (fun i => AppliedModelingLib.Allocation.share (seq.allocation N) i) +
          delta * weightedNegativePowerObjective p sigma
            (fun i => AppliedModelingLib.Allocation.share (seq.allocation N) i) <
          (V + eta / 3) + eta / 3 :=
      calc
        (1 - delta) * weightedNegativePowerObjective p sigma
            (fun i => AppliedModelingLib.Allocation.share (seq.allocation N) i) +
            delta * weightedNegativePowerObjective p sigma
              (fun i => AppliedModelingLib.Allocation.share (seq.allocation N) i) ≤
            (1 - delta) * weightedNegativePowerObjective p sigma
              (fun i => AppliedModelingLib.Allocation.share (seq.allocation N) i) + delta * C :=
              add_le_add_right hscaled _
        _ < (V + eta / 3) + eta / 3 := add_lt_add hnormalized_lt hdeltaC_lt
    nlinarith
  have hnot_far : ¬ epsilonHalf <
      |AppliedModelingLib.Allocation.share (seq.allocation N) t - q t| := by
    intro hfar
    have hgapN := hseparate
      (fun i => AppliedModelingLib.Allocation.share (seq.allocation N) i) hmemN ⟨t, hfar⟩
    have hobjective_ge : V + eta ≤ weightedNegativePowerObjective p sigma
        (fun i => AppliedModelingLib.Allocation.share (seq.allocation N) i) := by
      dsimp [V]
      linarith
    exact (not_lt_of_ge hobjective_ge) hobjective_lt
  have habs_le :
      |AppliedModelingLib.Allocation.share (seq.allocation N) t - q t| ≤ epsilonHalf :=
    le_of_not_gt hnot_far
  have habs_lt :
      |AppliedModelingLib.Allocation.share (seq.allocation N) t - q t| < epsilon :=
    lt_of_le_of_lt habs_le (by dsimp [epsilonHalf]; linarith)
  simpa [q, Real.dist_eq] using habs_lt

end AppendixD1GenericIIFull
end PRPKG24AccuracyDiversity
