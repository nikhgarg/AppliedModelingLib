import PRPKG24AccuracyDiversity.AppendixD1GenericPower
import AppliedModelingLib.Foundations.Math.Asymptotics
import AppliedModelingLib.Applications.RecommenderSystems.AllocationSequence

/-!
# Corrected generic Appendix D.1(iv)

This file is the source-facing raw-allocation work for Appendix D.1(iv).
The source claims that a fixed-total integer maximizer of
`sum_i p_i * h(a_i)` has shares proportional to
`p_i^(1 / (1 - sigma))` when `h(a) / (B * a^sigma) -> 1`, where
`0 < sigma < 1`.

The exact-power benchmark is proved in `AppendixD1GenericPower`.  Here the
tail comparisons are kept explicit and are derived from the displayed tail
hypothesis; no limiting objective, optimizer-convergence, or FOC certificate
is accepted as an input.

The source proof also uses strict increase while stating only strict
concavity.  Under the positive unbounded power tail, strict discrete
concavity itself implies that increase; the raw optimizer route derives it
internally rather than strengthening the source-facing hypotheses.
-/

open Filter Topology
open scoped BigOperators

namespace PRPKG24AccuracyDiversity
namespace AppendixD1GenericIV

open AppliedModelingLib
open AppendixD1GenericPower

/-- The source's discrete forward increment. -/
def forwardIncrement (h : ℕ → ℝ) (a : ℕ) : ℝ := h (a + 1) - h a

/-- The source's discrete strict-concavity convention, made explicit. -/
def StrictDiscreteConcave (h : ℕ → ℝ) : Prop := StrictAnti (forwardIncrement h)

/-- Monotonicity makes every discrete forward increment nonnegative. -/
theorem forwardIncrement_nonneg_of_monotone
    {h : ℕ → ℝ} (hmono : Monotone h) (a : ℕ) :
    0 ≤ forwardIncrement h a := by
  unfold forwardIncrement
  exact sub_nonneg.mpr (hmono (Nat.le_succ a))

/--
On the infinite count domain, monotonicity plus strict discrete concavity
already forces each forward increment to be strictly positive: a zero
increment would make the next, strictly smaller increment negative.
-/
theorem forwardIncrement_pos_of_monotone_strictDiscreteConcave
    {h : ℕ → ℝ} (hmono : Monotone h) (hconc : StrictDiscreteConcave h)
    (a : ℕ) :
    0 < forwardIncrement h a := by
  have hnext_nonneg : 0 ≤ forwardIncrement h (a + 1) :=
    forwardIncrement_nonneg_of_monotone hmono (a + 1)
  have hnext_lt : forwardIncrement h (a + 1) < forwardIncrement h a :=
    hconc (Nat.lt_succ_self a)
  linarith

/-- The source's strict-increase use follows from its monotonicity and strict concavity. -/
theorem strictMono_of_monotone_strictDiscreteConcave
    {h : ℕ → ℝ} (hmono : Monotone h) (hconc : StrictDiscreteConcave h) :
    StrictMono h := by
  intro a b hab
  exact AppliedModelingLib.lt_of_adjacent_lt_chain h hab (fun k _ _ => by
    exact sub_pos.mp
      (forwardIncrement_pos_of_monotone_strictDiscreteConcave hmono hconc k))

/-- The corrected D.1(iv) power-tail quotient. -/
noncomputable def powerTailQuotient
    (h : ℕ → ℝ) (B sigma : ℝ) (a : ℕ) : ℝ :=
  h a / (B * (a : ℝ) ^ sigma)

/-- The literal finite objective in the source's D.1(iv) allocation problem. -/
noncomputable def rawPowerTailObjective
    {m : ℕ} (p : Fin m → ℝ) (h : ℕ → ℝ)
    (a : AppliedModelingLib.Allocation (Fin m)) : ℝ :=
  ∑ i : Fin m, p i * h (a.count i)

/-- The corrected D.1(iv) target weights in the source's `p_i` notation. -/
noncomputable def targetWeight
    {m : ℕ} (p : Fin m → ℝ) (sigma : ℝ) (i : Fin m) : ℝ :=
  sourcePowerWeight p sigma i

/-- The corrected D.1(iv) target shares. -/
noncomputable def targetShare
    {m : ℕ} [NeZero m] (p : Fin m → ℝ) (sigma : ℝ)
    (i : Fin m) : ℝ :=
  AppendixD1GenericPower.targetShare (targetWeight p sigma) i

theorem targetWeight_pos
    {m : ℕ} (p : Fin m → ℝ) {sigma : ℝ}
    (hsigma_lt_one : sigma < 1) (hp_pos : ∀ i, 0 < p i)
    (i : Fin m) :
    0 < targetWeight p sigma i :=
  sourcePowerWeight_pos p hsigma_lt_one hp_pos i

theorem targetShare_pos
    {m : ℕ} [NeZero m] (p : Fin m → ℝ) {sigma : ℝ}
    (hsigma_lt_one : sigma < 1) (hp_pos : ∀ i, 0 < p i)
    (i : Fin m) :
    0 < targetShare p sigma i := by
  exact AppendixD1GenericPower.targetShare_pos (targetWeight p sigma)
    (fun j => targetWeight_pos p hsigma_lt_one hp_pos j) i

theorem sum_targetShare_eq_one
    {m : ℕ} [NeZero m] (p : Fin m → ℝ) {sigma : ℝ}
    (hsigma_lt_one : sigma < 1) (hp_pos : ∀ i, 0 < p i) :
    (∑ i : Fin m, targetShare p sigma i) = 1 := by
  exact AppendixD1GenericPower.sum_targetShare_eq_one (targetWeight p sigma)
    (fun j => targetWeight_pos p hsigma_lt_one hp_pos j)

/--
The power-tail limit supplies two-sided multiplicative bounds on the literal
value function.  This is the only asymptotic premise used by later raw
comparisons.
-/
theorem eventually_power_tail_bounds
    {B sigma : ℝ} {h : ℕ → ℝ}
    (hB_pos : 0 < B) (hsigma_pos : 0 < sigma)
    (htail : Tendsto (powerTailQuotient h B sigma) atTop (nhds 1))
    {delta : ℝ} (hdelta_pos : 0 < delta) :
    ∀ᶠ a : ℕ in atTop,
      (1 - delta) * (B * (a : ℝ) ^ sigma) < h a ∧
        h a < (1 + delta) * (B * (a : ℝ) ^ sigma) := by
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
      powerTailQuotient h B sigma a * (B * (a : ℝ) ^ sigma) = h a := by
    simp only [powerTailQuotient]
    field_simp [hden_ne]
  have hlow := mul_lt_mul_of_pos_right hratio.1 hden_pos
  have hhigh := mul_lt_mul_of_pos_right hratio.2 hden_pos
  rw [hratio_mul] at hlow hhigh
  exact ⟨hlow, hhigh⟩

/-- The positive D.1(iv) power tail makes the literal value function unbounded. -/
theorem tendsto_value_atTop_of_power_tail
    {B sigma : ℝ} {h : ℕ → ℝ}
    (hB_pos : 0 < B) (hsigma_pos : 0 < sigma)
    (htail : Tendsto (powerTailQuotient h B sigma) atTop (nhds 1)) :
    Tendsto h atTop atTop := by
  have hhalfB_pos : 0 < (1 / 2 : ℝ) * B :=
    mul_pos (by norm_num) hB_pos
  have hbase : Tendsto (fun a : ℕ => ((1 / 2 : ℝ) * B) * (a : ℝ) ^ sigma)
      atTop atTop :=
    (tendsto_rpow_atTop hsigma_pos).comp tendsto_natCast_atTop_atTop |>.const_mul_atTop
      hhalfB_pos
  have hbound := eventually_power_tail_bounds hB_pos hsigma_pos htail
    (delta := (1 / 2 : ℝ)) (by norm_num)
  refine Filter.tendsto_atTop.2 ?_
  intro C
  filter_upwards [Filter.tendsto_atTop.1 hbase C, hbound] with a hbase_a htail_a
  have hhalf : ((1 - (1 / 2 : ℝ)) * (B * (a : ℝ) ^ sigma)) =
      ((1 / 2 : ℝ) * B) * (a : ℝ) ^ sigma := by ring
  rw [← hhalf] at hbase_a
  exact hbase_a.trans htail_a.1.le

/--
Strict discrete concavity plus an unbounded value function forces every
increment to be positive.  Thus source monotonicity is derived rather than
silently strengthened into a new hypothesis.
-/
theorem forwardIncrement_pos_of_strictDiscreteConcave_of_tendsto_atTop
    {h : ℕ → ℝ} (hconc : StrictDiscreteConcave h)
    (hunbounded : Tendsto h atTop atTop) (a : ℕ) :
    0 < forwardIncrement h a := by
  by_contra hnot
  have hnonpos : forwardIncrement h a ≤ 0 := le_of_not_gt hnot
  obtain ⟨N, hN⟩ := eventually_atTop.1
    ((Filter.tendsto_atTop.1 hunbounded) (h (a + 1) + 1))
  let n : ℕ := max N (a + 2)
  have hn_ge_N : N ≤ n := le_max_left _ _
  have hn_gt : a + 1 < n := by
    dsimp [n]
    omega
  have hn_value : h (a + 1) < h n := by
    have := hN n hn_ge_N
    linarith
  have hdecrease : h n < h (a + 1) := by
    have hneg_chain :
        -h (a + 1) < -h n :=
      AppliedModelingLib.lt_of_adjacent_lt_chain (fun k : ℕ => -h k) hn_gt (by
        intro k hk hkn
        have hak : a < k := lt_of_lt_of_le (Nat.lt_succ_self a) hk
        have hinc_lt : forwardIncrement h k < forwardIncrement h a :=
          hconc hak
        have hinc_neg : forwardIncrement h k < 0 :=
          lt_of_lt_of_le hinc_lt hnonpos
        unfold forwardIncrement at hinc_neg
        linarith)
    linarith
  exact (not_lt_of_ge hdecrease.le) hn_value

/-- The source's strict increase is a theorem under its positive power tail. -/
theorem strictMono_of_strictDiscreteConcave_of_power_tail
    {B sigma : ℝ} {h : ℕ → ℝ}
    (hB_pos : 0 < B) (hsigma_pos : 0 < sigma)
    (htail : Tendsto (powerTailQuotient h B sigma) atTop (nhds 1))
    (hconc : StrictDiscreteConcave h) :
    StrictMono h := by
  have hunbounded := tendsto_value_atTop_of_power_tail hB_pos hsigma_pos htail
  intro a b hab
  exact AppliedModelingLib.lt_of_adjacent_lt_chain h hab (fun k _ _ => by
    exact sub_pos.mp
      (forwardIncrement_pos_of_strictDiscreteConcave_of_tendsto_atTop
        hconc hunbounded k))

/--
The tail quotient can be rewritten after scaling a count by the total.  This
is the componentwise algebra behind the product-limit step in source (69).
-/
theorem powerTailQuotient_mul_scaled_rpow
    {B sigma : ℝ} {h : ℕ → ℝ} {a N : ℕ}
    (hB_ne : B ≠ 0) (ha_pos : 0 < a) (hN_pos : 0 < N) :
    powerTailQuotient h B sigma a * ((a : ℝ) / (N : ℝ)) ^ sigma =
      h a / (B * (N : ℝ) ^ sigma) := by
  have ha_real_pos : 0 < (a : ℝ) := by exact_mod_cast ha_pos
  have hN_real_pos : 0 < (N : ℝ) := by exact_mod_cast hN_pos
  have ha_pow_ne : (a : ℝ) ^ sigma ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos ha_real_pos sigma)
  have hN_pow_ne : (N : ℝ) ^ sigma ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hN_real_pos sigma)
  unfold powerTailQuotient
  rw [Real.div_rpow ha_real_pos.le hN_real_pos.le]
  field_simp [hB_ne, ha_pow_ne, hN_pow_ne]

/--
Componentwise normalized tail algebra.  If a coordinate count and its scaled
share have the displayed limits, then the literal value contribution has the
corresponding power limit.  This proves, rather than assumes, the product
rule used in source (69).
-/
theorem tendsto_normalized_value_of_power_tail
    {B sigma r : ℝ} {h : ℕ → ℝ} {a : ℕ → ℕ}
    (hB_pos : 0 < B) (hsigma_pos : 0 < sigma)
    (htail : Tendsto (powerTailQuotient h B sigma) atTop (nhds 1))
    (ha_atTop : Tendsto a atTop atTop)
    (hshare : Tendsto (fun N : ℕ => (a N : ℝ) / (N : ℝ)) atTop (nhds r)) :
    Tendsto (fun N : ℕ => h (a N) / (B * (N : ℝ) ^ sigma))
      atTop (nhds (r ^ sigma)) := by
  have hquot : Tendsto (fun N : ℕ => powerTailQuotient h B sigma (a N))
      atTop (nhds 1) :=
    htail.comp ha_atTop
  have hshare_pow : Tendsto
      (fun N : ℕ => ((a N : ℝ) / (N : ℝ)) ^ sigma)
      atTop (nhds (r ^ sigma)) :=
    hshare.rpow_const (Or.inr hsigma_pos.le)
  have hprod := hquot.mul hshare_pow
  have ha_pos : ∀ᶠ N : ℕ in atTop, 0 < a N :=
    ha_atTop (eventually_gt_atTop 0)
  have hN_pos : ∀ᶠ N : ℕ in atTop, 0 < N :=
    eventually_gt_atTop 0
  have hrewrite :
      (fun N : ℕ => powerTailQuotient h B sigma (a N) *
          ((a N : ℝ) / (N : ℝ)) ^ sigma) =ᶠ[atTop]
        fun N : ℕ => h (a N) / (B * (N : ℝ) ^ sigma) := by
    filter_upwards [ha_pos, hN_pos] with N haN hN
    rw [powerTailQuotient_mul_scaled_rpow (ne_of_gt hB_pos) haN hN]
  simpa using hprod.congr' hrewrite

/-- A sublinear positive power divided by its argument tends to zero. -/
theorem tendsto_rpow_div_natCast_nhds_zero
    {sigma : ℝ} (hsigma_lt_one : sigma < 1) :
    Tendsto (fun a : ℕ => (a : ℝ) ^ sigma / (a : ℝ))
      atTop (nhds 0) := by
  have hgap_pos : 0 < 1 - sigma := sub_pos.mpr hsigma_lt_one
  have hbase : Tendsto (fun a : ℕ => (a : ℝ) ^ (-(1 - sigma)))
      atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hgap_pos).comp tendsto_natCast_atTop_atTop
  have hrewrite :
      (fun a : ℕ => (a : ℝ) ^ (-(1 - sigma))) =ᶠ[atTop]
        fun a : ℕ => (a : ℝ) ^ sigma / (a : ℝ) := by
    filter_upwards [eventually_gt_atTop 0] with a ha
    have ha_ne : (a : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt ha
    rw [← Real.rpow_sub_one ha_ne sigma]
    congr 1
    ring
  exact hbase.congr' hrewrite

/--
The displayed D.1(iv) tail is sublinear.  This is an internal consequence of
`0 < sigma < 1`, not an extra growth or marginal certificate.
-/
theorem tendsto_value_div_natCast_nhds_zero_of_power_tail
    {B sigma : ℝ} {h : ℕ → ℝ}
    (hB_pos : 0 < B) (hsigma_lt_one : sigma < 1)
    (htail : Tendsto (powerTailQuotient h B sigma) atTop (nhds 1)) :
    Tendsto (fun a : ℕ => h a / (a : ℝ)) atTop (nhds 0) := by
  have hpow : Tendsto (fun a : ℕ => (a : ℝ) ^ sigma / (a : ℝ))
      atTop (nhds 0) :=
    tendsto_rpow_div_natCast_nhds_zero hsigma_lt_one
  have hscaled : Tendsto
      (fun a : ℕ => B * ((a : ℝ) ^ sigma / (a : ℝ)))
      atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hpow : Tendsto
      (fun a : ℕ => B * ((a : ℝ) ^ sigma / (a : ℝ)))
        atTop (nhds (B * 0)))
  have hprod := htail.mul hscaled
  have hrewrite :
      (fun a : ℕ => powerTailQuotient h B sigma a *
          (B * ((a : ℝ) ^ sigma / (a : ℝ)))) =ᶠ[atTop]
        fun a : ℕ => h a / (a : ℝ) := by
    filter_upwards [eventually_gt_atTop 0] with a ha
    have ha_real_pos : 0 < (a : ℝ) := by exact_mod_cast ha
    have ha_pow_ne : (a : ℝ) ^ sigma ≠ 0 :=
      ne_of_gt (Real.rpow_pos_of_pos ha_real_pos sigma)
    unfold powerTailQuotient
    field_simp [ne_of_gt hB_pos, ne_of_gt ha_real_pos, ha_pow_ne]
  simpa using hprod.congr' hrewrite

/--
Discrete concavity bounds the current increment by the average of all earlier
increments.  This finite telescoping estimate is the raw replacement for an
unproved derivative asymptotic.
-/
theorem forwardIncrement_le_average_of_strictDiscreteConcave
    {h : ℕ → ℝ} (hconc : StrictDiscreteConcave h) (a : ℕ) :
    forwardIncrement h a ≤
      (h (a + 1) - h 0) / ((a + 1 : ℕ) : ℝ) := by
  have hsum :
      ((a + 1 : ℕ) : ℝ) * forwardIncrement h a ≤
        ∑ k ∈ Finset.range (a + 1), forwardIncrement h k := by
    calc
      ((a + 1 : ℕ) : ℝ) * forwardIncrement h a =
          ∑ _k ∈ Finset.range (a + 1), forwardIncrement h a := by
            simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ k ∈ Finset.range (a + 1), forwardIncrement h k := by
            refine Finset.sum_le_sum ?_
            intro k hk
            exact hconc.antitone
              (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
  have htel :
      (∑ k ∈ Finset.range (a + 1), forwardIncrement h k) = h (a + 1) - h 0 := by
    simpa [forwardIncrement] using AppliedModelingLib.sum_range_adjacent_sub h (a + 1)
  have hden_pos : 0 < ((a + 1 : ℕ) : ℝ) := by positivity
  rw [htel] at hsum
  calc
    forwardIncrement h a =
        (((a + 1 : ℕ) : ℝ) * forwardIncrement h a) / ((a + 1 : ℕ) : ℝ) := by
          field_simp [ne_of_gt hden_pos]
    _ ≤ (h (a + 1) - h 0) / ((a + 1 : ℕ) : ℝ) :=
          div_le_div_of_nonneg_right hsum hden_pos.le

/--
The D.1(iv) tail and discrete concavity force diminishing one-unit gains.
This is derived from the raw value function through a telescoping average;
it is not supplied as a marginal or FOC hypothesis.
-/
theorem tendsto_forwardIncrement_nhds_zero_of_power_tail
    {B sigma : ℝ} {h : ℕ → ℝ}
    (hB_pos : 0 < B) (hsigma_pos : 0 < sigma) (hsigma_lt_one : sigma < 1)
    (hconc : StrictDiscreteConcave h)
    (htail : Tendsto (powerTailQuotient h B sigma) atTop (nhds 1)) :
    Tendsto (forwardIncrement h) atTop (nhds 0) := by
  have hmono : Monotone h :=
    (strictMono_of_strictDiscreteConcave_of_power_tail
      hB_pos hsigma_pos htail hconc).monotone
  have hvalue : Tendsto (fun a : ℕ => h a / (a : ℝ)) atTop (nhds 0) :=
    tendsto_value_div_natCast_nhds_zero_of_power_tail hB_pos hsigma_lt_one htail
  have hvalue_succ :
      Tendsto (fun a : ℕ => h (a + 1) / ((a + 1 : ℕ) : ℝ))
        atTop (nhds 0) := by
    simpa [Function.comp_def] using hvalue.comp (tendsto_add_atTop_nat 1)
  have hzero : Tendsto (fun a : ℕ => h 0 / ((a + 1 : ℕ) : ℝ))
      atTop (nhds 0) := by
    simpa [Function.comp_def] using
      (tendsto_const_div_atTop_nhds_zero_nat (h 0 : ℝ)).comp
        (tendsto_add_atTop_nat 1)
  have havg : Tendsto
      (fun a : ℕ => (h (a + 1) - h 0) / ((a + 1 : ℕ) : ℝ))
        atTop (nhds 0) := by
    simpa [sub_div] using hvalue_succ.sub hzero
  exact squeeze_zero
    (fun a => forwardIncrement_nonneg_of_monotone hmono a)
    (forwardIncrement_le_average_of_strictDiscreteConcave hconc) havg

/--
Raw source interiority for corrected D.1(iv).  With positive finite weights,
discrete strict concavity, and the displayed sublinear power-tail, no
coordinate of a literal fixed-total optimizer can remain
bounded.  The argument is a one-unit exchange against an overlarge donor;
there is no assumed interiority, FOC certificate, or optimizer limit.
-/
theorem tendsto_optimalAllocation_count_atTop_of_power_tail
    {m : ℕ} [NeZero m] {B sigma : ℝ} {h : ℕ → ℝ}
    (p : Fin m → ℝ)
    (seq : AppliedModelingLib.Allocation.OptimalSequence
      (fun _ : ℕ => p) (fun _ : ℕ => fun _ : Fin m => h))
    (hp_pos : ∀ i, 0 < p i)
    (hB_pos : 0 < B) (hsigma_pos : 0 < sigma) (hsigma_lt_one : sigma < 1)
    (hconc : StrictDiscreteConcave h)
    (htail : Tendsto (powerTailQuotient h B sigma) atTop (nhds 1))
    (t : Fin m) :
    Tendsto (fun N : ℕ => (seq.allocation N).count t) atTop atTop := by
  have hinc_zero : Tendsto (forwardIncrement h) atTop (nhds 0) :=
    tendsto_forwardIncrement_nhds_zero_of_power_tail
      hB_pos hsigma_pos hsigma_lt_one hconc htail
  have hmono : Monotone h :=
    (strictMono_of_strictDiscreteConcave_of_power_tail
      hB_pos hsigma_pos htail hconc).monotone
  have hweight_pos : 0 < ∑ i : Fin m, p i :=
    Finset.sum_pos (fun i _ => hp_pos i) Finset.univ_nonempty
  rw [tendsto_atTop]
  intro K
  let d : ℝ := p t * forwardIncrement h K
  have hd_pos : 0 < d := by
    dsimp [d]
    exact mul_pos (hp_pos t)
      (forwardIncrement_pos_of_monotone_strictDiscreteConcave hmono hconc K)
  let W : ℝ := ∑ i : Fin m, p i
  have hW_pos : 0 < W := by simpa [W] using hweight_pos
  let eps : ℝ := d / W
  have heps_pos : 0 < eps := div_pos hd_pos hW_pos
  have hinc_small : ∀ᶠ q : ℕ in atTop, forwardIncrement h q < eps :=
    hinc_zero (Iio_mem_nhds heps_pos)
  obtain ⟨L, hL⟩ := eventually_atTop.1 hinc_small
  let M : ℕ := max K L + 1
  have hlargeN : ∀ᶠ N : ℕ in atTop, m * M < N :=
    eventually_gt_atTop _
  filter_upwards [hlargeN] with N hNlarge
  by_contra hnot
  have hcount_t_lt : (seq.allocation N).count t < K :=
    Nat.lt_of_not_ge hnot
  have htotal : AppliedModelingLib.Allocation.total (seq.allocation N) = N :=
    (seq.optimal N).1
  obtain ⟨j, hj_large⟩ :=
    AppliedModelingLib.Allocation.exists_count_gt_of_card_mul_lt_total
      (seq.allocation N) (by
        simpa [Fintype.card_fin, M, htotal] using hNlarge)
  have hj_ne_t : j ≠ t := by
    intro hjt
    subst j
    have hM_gt_K : K < M := by
      dsimp [M]
      omega
    exact (not_lt_of_ge (Nat.le_of_lt hcount_t_lt))
      (lt_trans hM_gt_K hj_large)
  have hj_pos : 0 < (seq.allocation N).count j :=
    lt_of_lt_of_le (Nat.zero_lt_succ _) (Nat.le_of_lt hj_large)
  have hj_pred_ge_L : L ≤ (seq.allocation N).count j - 1 := by
    have hM_ge_L : L + 1 ≤ M := by
      dsimp [M]
      omega
    have hcount_ge : L + 1 ≤ (seq.allocation N).count j :=
      Nat.le_of_lt (lt_of_le_of_lt hM_ge_L hj_large)
    omega
  have hdonor_small :
      forwardIncrement h ((seq.allocation N).count j - 1) < eps :=
    hL _ hj_pred_ge_L
  have hinc_nonneg :
      0 ≤ forwardIncrement h ((seq.allocation N).count j - 1) :=
    forwardIncrement_nonneg_of_monotone hmono _
  have htarget_increment :
      forwardIncrement h K ≤ forwardIncrement h ((seq.allocation N).count t) := by
    exact hconc.antitone (Nat.le_of_lt hcount_t_lt)
  have htarget_weighted :
      d ≤ p t * forwardIncrement h ((seq.allocation N).count t) := by
    dsimp [d]
    exact mul_le_mul_of_nonneg_left htarget_increment (hp_pos t).le
  have hweight_j : p j ≤ W := by
    dsimp [W]
    exact Finset.single_le_sum (fun i _ => (hp_pos i).le) (Finset.mem_univ j)
  have hdonor_weighted_le :
      p j * forwardIncrement h ((seq.allocation N).count j - 1) ≤
        W * forwardIncrement h ((seq.allocation N).count j - 1) := by
    exact mul_le_mul_of_nonneg_right hweight_j hinc_nonneg
  have hdonor_weighted_lt :
      p j * forwardIncrement h ((seq.allocation N).count j - 1) < d := by
    calc
      p j * forwardIncrement h ((seq.allocation N).count j - 1) ≤
          W * forwardIncrement h ((seq.allocation N).count j - 1) :=
            hdonor_weighted_le
      _ < W * eps := mul_lt_mul_of_pos_left hdonor_small hW_pos
      _ = d := by
        dsimp [eps]
        field_simp [ne_of_gt hW_pos]
  have hopt_exchange :=
    AppliedModelingLib.Allocation.weightedForwardMarginal_le_weightedBackwardMarginal_of_optimum
      (a := seq.allocation N) (weight := p)
      (valueOfCount := fun _ : Fin m => h) (N := N)
      (seq.optimal N) hj_ne_t hj_pos
  have hopt_exchange' :
      p t * forwardIncrement h ((seq.allocation N).count t) ≤
        p j * forwardIncrement h ((seq.allocation N).count j - 1) := by
    unfold AppliedModelingLib.Allocation.weightedForwardMarginal
      AppliedModelingLib.Allocation.weightedBackwardMarginal
      AppliedModelingLib.Allocation.marginal at hopt_exchange
    rw [dif_neg (ne_of_gt hj_pos)] at hopt_exchange
    change
      p t * (h ((seq.allocation N).count t + 1) - h ((seq.allocation N).count t)) ≤
        p j * (h ((seq.allocation N).count j - 1 + 1) -
          h ((seq.allocation N).count j - 1))
    rw [Nat.sub_add_cancel (Nat.succ_le_iff.mpr hj_pos)]
    exact hopt_exchange
  have hcontradiction : d < d := by
    calc
      d ≤ p t * forwardIncrement h ((seq.allocation N).count t) :=
        htarget_weighted
      _ ≤ p j * forwardIncrement h ((seq.allocation N).count j - 1) :=
        hopt_exchange'
      _ < d := hdonor_weighted_lt
  exact (lt_irrefl _) hcontradiction

/--
Finite weighted aggregation of the componentwise tail calculation.  The
profile `r` may have zero coordinates: count divergence is enough to apply
the tail ratio, while continuity of the positive power handles a vanishing
scaled share.
-/
theorem tendsto_normalized_weighted_values_of_power_tail
    {m : ℕ} [NeZero m] {B sigma : ℝ} {h : ℕ → ℝ}
    (p : Fin m → ℝ) (a : ℕ → Fin m → ℕ) (r : Fin m → ℝ)
    (hB_pos : 0 < B) (hsigma_pos : 0 < sigma)
    (htail : Tendsto (powerTailQuotient h B sigma) atTop (nhds 1))
    (ha_atTop : ∀ i, Tendsto (fun N : ℕ => a N i) atTop atTop)
    (hshare : ∀ i,
      Tendsto (fun N : ℕ => (a N i : ℝ) / (N : ℝ)) atTop (nhds (r i))) :
    Tendsto
      (fun N : ℕ => ∑ i : Fin m,
        p i * (h (a N i) / (B * (N : ℝ) ^ sigma)))
      atTop (nhds (∑ i : Fin m, p i * (r i ^ sigma))) := by
  have hterm : ∀ i : Fin m,
      Tendsto
        (fun N : ℕ => p i * (h (a N i) / (B * (N : ℝ) ^ sigma)))
        atTop (nhds (p i * (r i ^ sigma))) := by
    intro i
    exact (tendsto_const_nhds.mul
      (tendsto_normalized_value_of_power_tail hB_pos hsigma_pos htail
        (ha_atTop i) (hshare i)))
  exact tendsto_finset_sum Finset.univ (fun i _ => hterm i)

/--
The previous finite aggregation is stated directly for the source's literal
allocation objective.  It is the fully checked version of the first equality
in source (69), conditional only on an actual limiting allocation profile and
the raw tail/count facts proved above.
-/
theorem tendsto_normalized_rawPowerTailObjective_of_power_tail
    {m : ℕ} [NeZero m] {B sigma : ℝ} {h : ℕ → ℝ}
    (p : Fin m → ℝ) (a : ℕ → AppliedModelingLib.Allocation (Fin m)) (r : Fin m → ℝ)
    (hB_pos : 0 < B) (hsigma_pos : 0 < sigma)
    (htail : Tendsto (powerTailQuotient h B sigma) atTop (nhds 1))
    (ha_atTop : ∀ i, Tendsto (fun N : ℕ => (a N).count i) atTop atTop)
    (hshare : ∀ i,
      Tendsto (fun N : ℕ => ((a N).count i : ℝ) / (N : ℝ))
        atTop (nhds (r i))) :
    Tendsto
      (fun N : ℕ => rawPowerTailObjective p h (a N) /
        (B * (N : ℝ) ^ sigma))
      atTop (nhds (∑ i : Fin m, p i * (r i ^ sigma))) := by
  have hsum := tendsto_normalized_weighted_values_of_power_tail
    p (fun N i => (a N).count i) r hB_pos hsigma_pos htail ha_atTop hshare
  have hrewrite :
      (fun N : ℕ => rawPowerTailObjective p h (a N) /
        (B * (N : ℝ) ^ sigma)) =ᶠ[atTop]
        fun N : ℕ => ∑ i : Fin m,
          p i * (h ((a N).count i) / (B * (N : ℝ) ^ sigma)) := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hN_real_pos : 0 < (N : ℝ) := by exact_mod_cast hN
    have hN_pow_ne : (N : ℝ) ^ sigma ≠ 0 :=
      ne_of_gt (Real.rpow_pos_of_pos hN_real_pos sigma)
    unfold rawPowerTailObjective
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl ?_
    intro i _
    field_simp [ne_of_gt hB_pos, hN_pow_ne]
  exact hsum.congr' hrewrite.symm

/--
The corrected continuous D.1(iv) objective has the advertised target as a
maximizer on the probability simplex.  This is derived from Holder's bound in
the exact-power module, with the source coefficients translated explicitly.
-/
theorem sourcePowerObjective_le_target_of_simplex
    {m : ℕ} [NeZero m] (p : Fin m → ℝ) {sigma : ℝ}
    (hsigma_pos : 0 < sigma) (hsigma_lt_one : sigma < 1)
    (hp_pos : ∀ i, 0 < p i) (x : Fin m → ℝ)
    (hx_nonneg : ∀ i, 0 ≤ x i) (hx_sum : (∑ i, x i) = 1) :
    sourcePowerObjective p sigma x ≤
      sourcePowerObjective p sigma (targetShare p sigma) := by
  have htarget := weightedPowerObjective_target_maximizes
    (sourcePowerWeight p sigma) hsigma_pos hsigma_lt_one
    (fun i => sourcePowerWeight_pos p hsigma_lt_one hp_pos i)
    x hx_nonneg hx_sum
  have hx_eq := sourcePowerObjective_eq_weightedPowerObjective
    p hsigma_lt_one hp_pos x
  have htarget_eq := sourcePowerObjective_eq_weightedPowerObjective
    p hsigma_lt_one hp_pos (targetShare p sigma)
  rw [hx_eq, htarget_eq]
  simpa [targetShare] using htarget

/--
The continuous corrected objective has a strict gap away from its target.
This is a proved strict-concavity fact, not the source's unproved Lagrange
multiplier assertion or a caller-supplied compactness-gap certificate.
-/
theorem sourcePowerObjective_lt_target_of_simplex_ne
    {m : ℕ} [NeZero m] (p : Fin m → ℝ) {sigma : ℝ}
    (hsigma_pos : 0 < sigma) (hsigma_lt_one : sigma < 1)
    (hp_pos : ∀ i, 0 < p i) (x : Fin m → ℝ)
    (hx_nonneg : ∀ i, 0 ≤ x i) (hx_sum : (∑ i, x i) = 1)
    (hx_ne : x ≠ targetShare p sigma) :
    sourcePowerObjective p sigma x <
      sourcePowerObjective p sigma (targetShare p sigma) := by
  let w : Fin m → ℝ := sourcePowerWeight p sigma
  let g : Fin m → ℝ → ℝ := fun i z => w i ^ (1 - sigma) * z ^ sigma
  let q : Fin m → ℝ := targetShare p sigma
  have hw_pos : ∀ i, 0 < w i := by
    intro i
    exact sourcePowerWeight_pos p hsigma_lt_one hp_pos i
  have hq_nonneg : ∀ i, 0 ≤ q i := by
    intro i
    exact (targetShare_pos p hsigma_lt_one hp_pos i).le
  have hq_sum : (∑ i, q i) = 1 := by
    exact sum_targetShare_eq_one p hsigma_lt_one hp_pos
  have hconc : ∀ i, StrictConcaveOn ℝ (Set.Ici 0) (g i) := by
    intro i
    exact weightedPowerCoordinate_strictConcaveOn w i hsigma_pos hsigma_lt_one
      (hw_pos i)
  have hq_opt : ∀ z : Fin m → ℝ,
      (∀ i, 0 ≤ z i) -> (∑ i, z i) = 1 ->
        GeneralRounding.objective g z ≤ GeneralRounding.objective g q := by
    intro z hz hsum
    have hmax := weightedPowerObjective_target_maximizes
      w hsigma_pos hsigma_lt_one hw_pos z hz hsum
    simpa [GeneralRounding.objective, weightedPowerObjective, g, q] using hmax
  have hstrict := GeneralRounding.objective_lt_of_ne_of_strictConcave_maximizer
    g 1 q x hconc hq_nonneg hq_sum hq_opt hx_nonneg hx_sum (by
      intro h
      exact hx_ne (by simpa [q] using h))
  have hx_eq := sourcePowerObjective_eq_weightedPowerObjective
    p hsigma_lt_one hp_pos x
  have hq_eq := sourcePowerObjective_eq_weightedPowerObjective
    p hsigma_lt_one hp_pos q
  rw [hx_eq, hq_eq]
  simpa [GeneralRounding.objective, weightedPowerObjective, g, w, q] using hstrict

/-- The positive-power source objective is continuous on the whole finite simplex. -/
theorem continuous_sourcePowerObjective
    {m : ℕ} (p : Fin m → ℝ) (sigma : ℝ) (hsigma_nonneg : 0 ≤ sigma) :
    Continuous (sourcePowerObjective p sigma) := by
  unfold sourcePowerObjective
  refine continuous_finset_sum Finset.univ ?_
  intro i _
  exact continuous_const.mul
    ((Real.continuous_rpow_const hsigma_nonneg).comp (continuous_apply i))

/--
A canonical literal integer comparator: an actual fixed-total maximizer of
the exact positive-power benchmark.  Its existence comes from finite search,
not from a rounding or asymptotic certificate.
-/
noncomputable def powerBenchmarkAllocation
    {m : ℕ} [NeZero m] (p : Fin m → ℝ) (sigma : ℝ) (N : ℕ) :
    AppliedModelingLib.Allocation (Fin m) :=
  Classical.choose
    (AppliedModelingLib.Allocation.exists_isOptimalAtTotal
      p (fun _ : Fin m => fun q : ℕ => (q : ℝ) ^ sigma) N)

theorem powerBenchmarkAllocation_total
    {m : ℕ} [NeZero m] (p : Fin m → ℝ) (sigma : ℝ) (N : ℕ) :
    AppliedModelingLib.Allocation.total (powerBenchmarkAllocation p sigma N) = N := by
  exact (Classical.choose_spec
    (AppliedModelingLib.Allocation.exists_isOptimalAtTotal
      p (fun _ : Fin m => fun q : ℕ => (q : ℝ) ^ sigma) N)).1

theorem powerBenchmarkAllocation_optimal
    {m : ℕ} [NeZero m] (p : Fin m → ℝ) (sigma : ℝ) (N : ℕ) :
    ∀ b : AppliedModelingLib.Allocation (Fin m),
      AppliedModelingLib.Allocation.total b = N ->
        AppliedModelingLib.Allocation.objective b p
          (fun _ : Fin m => fun q : ℕ => (q : ℝ) ^ sigma) ≤
          AppliedModelingLib.Allocation.objective (powerBenchmarkAllocation p sigma N) p
            (fun _ : Fin m => fun q : ℕ => (q : ℝ) ^ sigma) := by
  exact (Classical.choose_spec
    (AppliedModelingLib.Allocation.exists_isOptimalAtTotal
      p (fun _ : Fin m => fun q : ℕ => (q : ℝ) ^ sigma) N)).2

/-- The canonical benchmark lies in the checked finite rounding window. -/
theorem powerBenchmarkAllocation_rounding_window
    {m : ℕ} [NeZero m] (p : Fin m → ℝ) {sigma : ℝ}
    (hsigma_pos : 0 < sigma) (hsigma_lt_one : sigma < 1)
    (hp_pos : ∀ i, 0 < p i) (N : ℕ) :
    ∀ t : Fin m,
      ⌊(N : ℝ) * targetShare p sigma t⌋₊ <
          (powerBenchmarkAllocation p sigma N).count t + m ∧
        (powerBenchmarkAllocation p sigma N).count t <
          ⌊(N : ℝ) * targetShare p sigma t⌋₊ + m := by
  have hsum :
      (∑ i : Fin m, (powerBenchmarkAllocation p sigma N).count i) = N := by
    simpa [AppliedModelingLib.Allocation.total] using
      powerBenchmarkAllocation_total p sigma N
  have hopt : ∀ b : Fin m → ℕ, (∑ i : Fin m, b i) = N ->
      sourcePowerObjective p sigma (fun i => (b i : ℝ)) ≤
        sourcePowerObjective p sigma
          (fun i => ((powerBenchmarkAllocation p sigma N).count i : ℝ)) := by
    intro b hb
    let bAlloc : AppliedModelingLib.Allocation (Fin m) := ⟨b⟩
    have hbtotal : AppliedModelingLib.Allocation.total bAlloc = N := by
      simpa [bAlloc, AppliedModelingLib.Allocation.total] using hb
    have h := powerBenchmarkAllocation_optimal p sigma N bAlloc hbtotal
    simpa [bAlloc, AppliedModelingLib.Allocation.objective, sourcePowerObjective] using h
  simpa [targetShare, Fintype.card_fin] using
    lemmaD1_iv_exactPower_integer_maximizer_rounding_window
      p hsigma_pos hsigma_lt_one hp_pos N
      (fun i => (powerBenchmarkAllocation p sigma N).count i) hsum hopt

/-- Every positive-target benchmark coordinate diverges, by its checked rounding window. -/
theorem tendsto_powerBenchmarkAllocation_count_atTop
    {m : ℕ} [NeZero m] (p : Fin m → ℝ) {sigma : ℝ}
    (hsigma_pos : 0 < sigma) (hsigma_lt_one : sigma < 1)
    (hp_pos : ∀ i, 0 < p i) (t : Fin m) :
    Tendsto (fun N : ℕ => (powerBenchmarkAllocation p sigma N).count t)
      atTop atTop := by
  have hq_pos : 0 < targetShare p sigma t :=
    targetShare_pos p hsigma_lt_one hp_pos t
  have hfloor : Tendsto
      (fun N : ℕ => ⌊(N : ℝ) * targetShare p sigma t⌋₊)
      atTop atTop :=
    AppliedModelingLib.Math.tendsto_nat_floor_mul_const_atTop hq_pos
  refine Filter.tendsto_atTop.2 ?_
  intro K
  have hfloor_large : ∀ᶠ N : ℕ in atTop,
      K + m + 1 ≤ ⌊(N : ℝ) * targetShare p sigma t⌋₊ :=
    Filter.tendsto_atTop.1 hfloor (K + m + 1)
  filter_upwards [hfloor_large] with N hN
  have hwindow :=
    powerBenchmarkAllocation_rounding_window
      p hsigma_pos hsigma_lt_one hp_pos N t
  omega

/-- The canonical exact-power benchmark has the corrected target shares. -/
theorem tendsto_powerBenchmarkAllocation_count_div_targetShare
    {m : ℕ} [NeZero m] (p : Fin m → ℝ) {sigma : ℝ}
    (hsigma_pos : 0 < sigma) (hsigma_lt_one : sigma < 1)
    (hp_pos : ∀ i, 0 < p i) (t : Fin m) :
    Tendsto
      (fun N : ℕ => ((powerBenchmarkAllocation p sigma N).count t : ℝ) /
        (N : ℝ))
      atTop (nhds (targetShare p sigma t)) := by
  let q : ℝ := targetShare p sigma t
  let f : ℕ → ℕ := fun N => ⌊(N : ℝ) * q⌋₊
  let a : ℕ → ℕ := fun N => (powerBenchmarkAllocation p sigma N).count t
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    exact (targetShare_pos p hsigma_lt_one hp_pos t).le
  have hfloor : Tendsto (fun N : ℕ => (f N : ℝ) / (N : ℝ))
      atTop (nhds q) := by
    simpa [f] using AppliedModelingLib.Math.tendsto_nat_floor_mul_const_div_nat hq_nonneg
  have hcard : Tendsto (fun N : ℕ => (m : ℝ) / (N : ℝ))
      atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (m : ℝ)
  have hlower : Tendsto
      (fun N : ℕ => (f N : ℝ) / (N : ℝ) - (m : ℝ) / (N : ℝ))
      atTop (nhds q) := by
    simpa using hfloor.sub hcard
  have hupper : Tendsto
      (fun N : ℕ => (f N : ℝ) / (N : ℝ) + (m : ℝ) / (N : ℝ))
      atTop (nhds q) := by
    simpa using hfloor.add hcard
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with N hN
    have hN_real_pos : 0 < (N : ℝ) := by exact_mod_cast hN
    have hwindow :=
      powerBenchmarkAllocation_rounding_window
        p hsigma_pos hsigma_lt_one hp_pos N t
    have hlow : (f N : ℝ) - (m : ℝ) ≤ (a N : ℝ) := by
      dsimp [f, a]
      have hwindow_real :
          (⌊(N : ℝ) * targetShare p sigma t⌋₊ : ℝ) <
            ((powerBenchmarkAllocation p sigma N).count t : ℝ) + (m : ℝ) := by
        exact_mod_cast hwindow.1
      linarith
    have hdiv := div_le_div_of_nonneg_right hlow hN_real_pos.le
    simpa [sub_div] using hdiv
  · filter_upwards [eventually_gt_atTop 0] with N hN
    have hN_real_pos : 0 < (N : ℝ) := by exact_mod_cast hN
    have hwindow :=
      powerBenchmarkAllocation_rounding_window
        p hsigma_pos hsigma_lt_one hp_pos N t
    have hhigh : (a N : ℝ) ≤ (f N : ℝ) + (m : ℝ) := by
      dsimp [f, a]
      have hwindow_real :
          ((powerBenchmarkAllocation p sigma N).count t : ℝ) <
            (⌊(N : ℝ) * targetShare p sigma t⌋₊ : ℝ) + (m : ℝ) := by
        exact_mod_cast hwindow.2
      exact hwindow_real.le
    have hdiv := div_le_div_of_nonneg_right hhigh hN_real_pos.le
    simpa [add_div] using hdiv

/--
Once every coordinate of a literal optimizer lies in the power-tail regime,
its normalized raw objective is bounded above by the continuous power
objective plus the explicit tail allowance.  This is an internal uniform
comparison over the *selected* optimizers; it does not assume a limiting
objective bound or a profile-convergence certificate.
-/
theorem eventually_normalized_rawPowerTailObjective_le_sourcePowerObjective_add
    {m : ℕ} [NeZero m] {B sigma : ℝ} {h : ℕ → ℝ}
    (p : Fin m → ℝ)
    (seq : AppliedModelingLib.Allocation.OptimalSequence
      (fun _ : ℕ => p) (fun _ : ℕ => fun _ : Fin m => h))
    (hp_pos : ∀ i, 0 < p i)
    (hB_pos : 0 < B) (hsigma_pos : 0 < sigma) (hsigma_lt_one : sigma < 1)
    (hconc : StrictDiscreteConcave h)
    (htail : Tendsto (powerTailQuotient h B sigma) atTop (nhds 1))
    {delta : ℝ} (hdelta_pos : 0 < delta) :
    ∀ᶠ N : ℕ in atTop,
      rawPowerTailObjective p h (seq.allocation N) /
          (B * (N : ℝ) ^ sigma) ≤
        sourcePowerObjective p sigma
            (fun i => AppliedModelingLib.Allocation.share (seq.allocation N) i) +
          delta * ∑ i : Fin m, p i := by
  have hcounts_atTop : ∀ i,
      Tendsto (fun N : ℕ => (seq.allocation N).count i) atTop atTop := by
    intro i
    exact tendsto_optimalAllocation_count_atTop_of_power_tail
      p seq hp_pos hB_pos hsigma_pos hsigma_lt_one hconc htail i
  have hcount_pos : ∀ᶠ N : ℕ in atTop, ∀ i,
      0 < (seq.allocation N).count i := by
    refine Filter.eventually_all.2 ?_
    intro i
    exact (hcounts_atTop i).eventually_gt_atTop 0
  have hquotient_lt : ∀ᶠ N : ℕ in atTop, ∀ i,
      powerTailQuotient h B sigma ((seq.allocation N).count i) < 1 + delta := by
    refine Filter.eventually_all.2 ?_
    intro i
    exact (htail.comp (hcounts_atTop i))
      (Iio_mem_nhds (by linarith))
  filter_upwards [eventually_gt_atTop 0, hcount_pos, hquotient_lt] with
      N hN hcountN hquotientN
  have hN_real_pos : 0 < (N : ℝ) := by exact_mod_cast hN
  have htotal : AppliedModelingLib.Allocation.total (seq.allocation N) = N :=
    (seq.optimal N).1
  have htotal_ne : AppliedModelingLib.Allocation.total (seq.allocation N) ≠ 0 := by
    rw [htotal]
    exact Nat.ne_of_gt hN
  have hshare_nonneg : ∀ i : Fin m,
      0 ≤ AppliedModelingLib.Allocation.share (seq.allocation N) i := by
    intro i
    exact AppliedModelingLib.Allocation.share_nonneg (seq.allocation N) i
  have hshare_le_one : ∀ i : Fin m,
      AppliedModelingLib.Allocation.share (seq.allocation N) i ≤ 1 := by
    intro i
    rw [AppliedModelingLib.Allocation.share_eq_div_of_total_ne_zero
      (a := seq.allocation N) (k := i) htotal_ne, htotal]
    apply (div_le_one hN_real_pos).mpr
    have hcount_le_total := AppliedModelingLib.Allocation.count_le_total
      (seq.allocation N) i
    exact_mod_cast (by simpa [htotal] using hcount_le_total :
      (seq.allocation N).count i ≤ N)
  have hrewrite :
      rawPowerTailObjective p h (seq.allocation N) /
          (B * (N : ℝ) ^ sigma) =
        ∑ i : Fin m, p i *
          (powerTailQuotient h B sigma ((seq.allocation N).count i) *
            (AppliedModelingLib.Allocation.share (seq.allocation N) i) ^ sigma) := by
    unfold rawPowerTailObjective
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl ?_
    intro i _
    have hshare_eq :
        AppliedModelingLib.Allocation.share (seq.allocation N) i =
          ((seq.allocation N).count i : ℝ) / (N : ℝ) := by
      rw [AppliedModelingLib.Allocation.share_eq_div_of_total_ne_zero
        (a := seq.allocation N) (k := i) htotal_ne, htotal]
    have htail_eq := powerTailQuotient_mul_scaled_rpow
      (h := h) (sigma := sigma) (ne_of_gt hB_pos) (hcountN i) hN
    rw [hshare_eq]
    calc
      p i * h ((seq.allocation N).count i) / (B * (N : ℝ) ^ sigma) =
          p i * (h ((seq.allocation N).count i) /
            (B * (N : ℝ) ^ sigma)) := by ring
      _ = p i *
          (powerTailQuotient h B sigma ((seq.allocation N).count i) *
            (((seq.allocation N).count i : ℝ) / (N : ℝ)) ^ sigma) := by
          rw [htail_eq]
  rw [hrewrite]
  calc
    ∑ i : Fin m, p i *
        (powerTailQuotient h B sigma ((seq.allocation N).count i) *
          (AppliedModelingLib.Allocation.share (seq.allocation N) i) ^ sigma) ≤
        ∑ i : Fin m,
          (p i * (AppliedModelingLib.Allocation.share (seq.allocation N) i) ^ sigma +
            p i * delta) := by
      refine Finset.sum_le_sum ?_
      intro i _
      have hpow_nonneg : 0 ≤
          (AppliedModelingLib.Allocation.share (seq.allocation N) i) ^ sigma :=
        Real.rpow_nonneg (hshare_nonneg i) sigma
      have hpow_le_one :
          (AppliedModelingLib.Allocation.share (seq.allocation N) i) ^ sigma ≤ 1 :=
        Real.rpow_le_one (hshare_nonneg i) (hshare_le_one i) hsigma_pos.le
      have hbase :
          powerTailQuotient h B sigma ((seq.allocation N).count i) *
              (AppliedModelingLib.Allocation.share (seq.allocation N) i) ^ sigma ≤
            (AppliedModelingLib.Allocation.share (seq.allocation N) i) ^ sigma + delta := by
        calc
          powerTailQuotient h B sigma ((seq.allocation N).count i) *
              (AppliedModelingLib.Allocation.share (seq.allocation N) i) ^ sigma ≤
              (1 + delta) *
                (AppliedModelingLib.Allocation.share (seq.allocation N) i) ^ sigma :=
            mul_le_mul_of_nonneg_right (hquotientN i).le hpow_nonneg
          _ = (AppliedModelingLib.Allocation.share (seq.allocation N) i) ^ sigma +
                delta * (AppliedModelingLib.Allocation.share (seq.allocation N) i) ^ sigma := by
                ring
          _ ≤ (AppliedModelingLib.Allocation.share (seq.allocation N) i) ^ sigma +
                delta * 1 := by
                have hdelta_mul :
                    delta * (AppliedModelingLib.Allocation.share (seq.allocation N) i) ^ sigma ≤
                      delta * 1 :=
                  mul_le_mul_of_nonneg_left hpow_le_one hdelta_pos.le
                calc
                  (AppliedModelingLib.Allocation.share (seq.allocation N) i) ^ sigma +
                      delta * (AppliedModelingLib.Allocation.share (seq.allocation N) i) ^ sigma =
                      delta * (AppliedModelingLib.Allocation.share (seq.allocation N) i) ^ sigma +
                        (AppliedModelingLib.Allocation.share (seq.allocation N) i) ^ sigma := by
                        ring
                  _ ≤ delta * 1 +
                        (AppliedModelingLib.Allocation.share (seq.allocation N) i) ^ sigma :=
                      by
                        simpa [add_comm] using
                          (add_le_add_left hdelta_mul
                            ((AppliedModelingLib.Allocation.share (seq.allocation N) i) ^ sigma))
                  _ = (AppliedModelingLib.Allocation.share (seq.allocation N) i) ^ sigma +
                        delta * 1 := by
                        ring
          _ = (AppliedModelingLib.Allocation.share (seq.allocation N) i) ^ sigma + delta := by
                ring
      have hmul := mul_le_mul_of_nonneg_left hbase (hp_pos i).le
      simpa [mul_add] using hmul
    _ = sourcePowerObjective p sigma
          (fun i => AppliedModelingLib.Allocation.share (seq.allocation N) i) +
        delta * ∑ i : Fin m, p i := by
      unfold sourcePowerObjective
      rw [Finset.sum_add_distrib, ← Finset.sum_mul]
      ring

/--
Raw finite optimality forces the selected optimizer's continuous power
objective arbitrarily close to the corrected target value from below.  The
benchmark allocation, its tail limit, and the comparison allowance are all
constructed from the literal model in this theorem.
-/
theorem eventually_sourcePowerObjective_target_sub_lt_optimal
    {m : ℕ} [NeZero m] {B sigma : ℝ} {h : ℕ → ℝ}
    (p : Fin m → ℝ)
    (seq : AppliedModelingLib.Allocation.OptimalSequence
      (fun _ : ℕ => p) (fun _ : ℕ => fun _ : Fin m => h))
    (hp_pos : ∀ i, 0 < p i)
    (hB_pos : 0 < B) (hsigma_pos : 0 < sigma) (hsigma_lt_one : sigma < 1)
    (hconc : StrictDiscreteConcave h)
    (htail : Tendsto (powerTailQuotient h B sigma) atTop (nhds 1))
    {epsilon : ℝ} (hepsilon_pos : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop,
      sourcePowerObjective p sigma (targetShare p sigma) - epsilon <
        sourcePowerObjective p sigma
          (fun i => AppliedModelingLib.Allocation.share (seq.allocation N) i) := by
  let totalWeight : ℝ := ∑ i : Fin m, p i
  have htotalWeight_pos : 0 < totalWeight := by
    dsimp [totalWeight]
    exact Finset.sum_pos (fun i _ => hp_pos i) Finset.univ_nonempty
  let tailAllowance : ℝ := epsilon / (2 * totalWeight)
  have htailAllowance_pos : 0 < tailAllowance := by
    dsimp [tailAllowance]
    exact div_pos hepsilon_pos (mul_pos (by norm_num) htotalWeight_pos)
  have hallowance_eq : tailAllowance * totalWeight = epsilon / 2 := by
    dsimp [tailAllowance]
    field_simp [ne_of_gt htotalWeight_pos]
  have hactual_upper :=
    eventually_normalized_rawPowerTailObjective_le_sourcePowerObjective_add
      p seq hp_pos hB_pos hsigma_pos hsigma_lt_one hconc htail htailAllowance_pos
  have hbenchmark_counts_atTop : ∀ i,
      Tendsto (fun N : ℕ => (powerBenchmarkAllocation p sigma N).count i)
        atTop atTop := by
    intro i
    exact tendsto_powerBenchmarkAllocation_count_atTop
      p hsigma_pos hsigma_lt_one hp_pos i
  have hbenchmark_share : ∀ i,
      Tendsto
        (fun N : ℕ => ((powerBenchmarkAllocation p sigma N).count i : ℝ) /
          (N : ℝ))
        atTop (nhds (targetShare p sigma i)) := by
    intro i
    exact tendsto_powerBenchmarkAllocation_count_div_targetShare
      p hsigma_pos hsigma_lt_one hp_pos i
  have hbenchmark_value_limit :=
    tendsto_normalized_rawPowerTailObjective_of_power_tail
      p (powerBenchmarkAllocation p sigma) (targetShare p sigma)
      hB_pos hsigma_pos htail hbenchmark_counts_atTop hbenchmark_share
  have hepsilon_half_pos : 0 < epsilon / 2 := by linarith
  have hbenchmark_lower : ∀ᶠ N : ℕ in atTop,
      sourcePowerObjective p sigma (targetShare p sigma) - epsilon / 2 <
        rawPowerTailObjective p h (powerBenchmarkAllocation p sigma N) /
          (B * (N : ℝ) ^ sigma) := by
    have h := hbenchmark_value_limit
      (Ioi_mem_nhds (sub_lt_self
        (∑ i : Fin m, p i * (targetShare p sigma i) ^ sigma)
        hepsilon_half_pos))
    simpa [sourcePowerObjective] using h
  filter_upwards [eventually_gt_atTop 0, hactual_upper, hbenchmark_lower] with
      N hN hactualN hbenchmarkN
  have hN_real_pos : 0 < (N : ℝ) := by exact_mod_cast hN
  have hden_pos : 0 < B * (N : ℝ) ^ sigma :=
    mul_pos hB_pos (Real.rpow_pos_of_pos hN_real_pos sigma)
  have hraw_opt := (seq.optimal N).2 (powerBenchmarkAllocation p sigma N)
    (powerBenchmarkAllocation_total p sigma N)
  have hraw_opt' :
      rawPowerTailObjective p h (powerBenchmarkAllocation p sigma N) ≤
        rawPowerTailObjective p h (seq.allocation N) := by
    simpa [rawPowerTailObjective, AppliedModelingLib.Allocation.objective] using hraw_opt
  have hnormalized_opt :
      rawPowerTailObjective p h (powerBenchmarkAllocation p sigma N) /
          (B * (N : ℝ) ^ sigma) ≤
        rawPowerTailObjective p h (seq.allocation N) /
          (B * (N : ℝ) ^ sigma) :=
    (div_le_div_iff_of_pos_right hden_pos).2 hraw_opt'
  dsimp [totalWeight] at hallowance_eq hactualN
  linarith

/--
Any actual limiting profile of literal D.1(iv) finite optimizers is the
corrected power target.  The proof constructs its own exact-power benchmark
competitor, proves both raw objective limits from the displayed tail, and
uses finite optimality only for the literal objective comparison.
-/
theorem limitProfile_eq_targetShare_of_rawPowerTail_optimality
    {m : ℕ} [NeZero m] {B sigma : ℝ} {h : ℕ → ℝ}
    (p : Fin m → ℝ)
    (seq : AppliedModelingLib.Allocation.OptimalSequence
      (fun _ : ℕ => p) (fun _ : ℕ => fun _ : Fin m => h))
    (hp_pos : ∀ i, 0 < p i)
    (hB_pos : 0 < B) (hsigma_pos : 0 < sigma) (hsigma_lt_one : sigma < 1)
    (hconc : StrictDiscreteConcave h)
    (htail : Tendsto (powerTailQuotient h B sigma) atTop (nhds 1))
    (r : Fin m → ℝ)
    (hshare : ∀ i,
      Tendsto (fun N : ℕ => ((seq.allocation N).count i : ℝ) / (N : ℝ))
        atTop (nhds (r i))) :
    r = targetShare p sigma := by
  have hr_nonneg : ∀ i, 0 ≤ r i := by
    intro i
    apply ge_of_tendsto (hshare i)
    filter_upwards with N
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hsum_tendsto : Tendsto
      (fun N : ℕ => ∑ i : Fin m,
        ((seq.allocation N).count i : ℝ) / (N : ℝ))
      atTop (nhds (∑ i : Fin m, r i)) :=
    tendsto_finset_sum Finset.univ (fun i _ => hshare i)
  have hsum_eq_one :
      (fun N : ℕ => ∑ i : Fin m,
        ((seq.allocation N).count i : ℝ) / (N : ℝ)) =ᶠ[atTop]
          fun _ : ℕ => (1 : ℝ) := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    rw [← Finset.sum_div]
    have htotal : AppliedModelingLib.Allocation.total (seq.allocation N) = N :=
      (seq.optimal N).1
    change ((∑ i : Fin m, ((seq.allocation N).count i : ℝ)) / (N : ℝ)) = 1
    rw [← Nat.cast_sum, ← AppliedModelingLib.Allocation.total, htotal]
    field_simp [ne_of_gt (by exact_mod_cast hN : (0 : ℝ) < (N : ℝ))]
  have hr_sum : (∑ i : Fin m, r i) = 1 := by
    have hconst : Tendsto
        (fun N : ℕ => ∑ i : Fin m,
          ((seq.allocation N).count i : ℝ) / (N : ℝ))
        atTop (nhds 1) :=
      tendsto_const_nhds.congr' hsum_eq_one.symm
    exact tendsto_nhds_unique hsum_tendsto hconst
  have hseq_counts_atTop : ∀ i,
      Tendsto (fun N : ℕ => (seq.allocation N).count i) atTop atTop := by
    intro i
    exact tendsto_optimalAllocation_count_atTop_of_power_tail
      p seq hp_pos hB_pos hsigma_pos hsigma_lt_one hconc htail i
  have hseq_value_limit := tendsto_normalized_rawPowerTailObjective_of_power_tail
    p seq.allocation r hB_pos hsigma_pos htail hseq_counts_atTop hshare
  have hbenchmark_counts_atTop : ∀ i,
      Tendsto (fun N : ℕ => (powerBenchmarkAllocation p sigma N).count i)
        atTop atTop := by
    intro i
    exact tendsto_powerBenchmarkAllocation_count_atTop
      p hsigma_pos hsigma_lt_one hp_pos i
  have hbenchmark_share : ∀ i,
      Tendsto
        (fun N : ℕ => ((powerBenchmarkAllocation p sigma N).count i : ℝ) /
          (N : ℝ))
        atTop (nhds (targetShare p sigma i)) := by
    intro i
    exact tendsto_powerBenchmarkAllocation_count_div_targetShare
      p hsigma_pos hsigma_lt_one hp_pos i
  have hbenchmark_value_limit :=
    tendsto_normalized_rawPowerTailObjective_of_power_tail
      p (powerBenchmarkAllocation p sigma) (targetShare p sigma)
      hB_pos hsigma_pos htail hbenchmark_counts_atTop hbenchmark_share
  have hbenchmark_le_seq : ∀ᶠ N : ℕ in atTop,
      rawPowerTailObjective p h (powerBenchmarkAllocation p sigma N) /
          (B * (N : ℝ) ^ sigma) ≤
        rawPowerTailObjective p h (seq.allocation N) /
          (B * (N : ℝ) ^ sigma) := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hN_real_pos : 0 < (N : ℝ) := by exact_mod_cast hN
    have hden_pos : 0 < B * (N : ℝ) ^ sigma :=
      mul_pos hB_pos (Real.rpow_pos_of_pos hN_real_pos sigma)
    have hopt := (seq.optimal N).2 (powerBenchmarkAllocation p sigma N)
      (powerBenchmarkAllocation_total p sigma N)
    have hraw :
        rawPowerTailObjective p h (powerBenchmarkAllocation p sigma N) ≤
          rawPowerTailObjective p h (seq.allocation N) := by
      simpa [rawPowerTailObjective, AppliedModelingLib.Allocation.objective] using hopt
    exact (div_le_div_iff_of_pos_right hden_pos).2 hraw
  have htarget_le_r :
      sourcePowerObjective p sigma (targetShare p sigma) ≤
        sourcePowerObjective p sigma r := by
    have hle := le_of_tendsto_of_tendsto
      hbenchmark_value_limit hseq_value_limit hbenchmark_le_seq
    simpa [sourcePowerObjective] using hle
  have hr_le_target :
      sourcePowerObjective p sigma r ≤
        sourcePowerObjective p sigma (targetShare p sigma) :=
    sourcePowerObjective_le_target_of_simplex
      p hsigma_pos hsigma_lt_one hp_pos r hr_nonneg hr_sum
  by_contra hr_ne
  have hstrict :
      sourcePowerObjective p sigma r <
        sourcePowerObjective p sigma (targetShare p sigma) :=
    sourcePowerObjective_lt_target_of_simplex_ne
      p hsigma_pos hsigma_lt_one hp_pos r hr_nonneg hr_sum hr_ne
  exact (not_lt_of_ge htarget_le_r) hstrict

/--
Corrected generic Lemma D.1(iv).  For positive finite weights and a literal
fixed-total optimizer, the displayed positive sublinear power tail forces
shares to converge to the profile proportional to
`p_i ^ (1 / (1 - sigma))`.  The proof constructs the raw benchmark,
interiority, tail comparison, continuous maximizer, and compact strict gap
internally; it accepts no limiting-objective, FOC, or convergence certificate.
-/
theorem corrected_lemmaD1_iv_powerTail_optimizer_shares
    {m : ℕ} [NeZero m] {B sigma : ℝ} {h : ℕ → ℝ}
    (p : Fin m → ℝ)
    (seq : AppliedModelingLib.Allocation.OptimalSequence
      (fun _ : ℕ => p) (fun _ : ℕ => fun _ : Fin m => h))
    (hp_pos : ∀ i, 0 < p i)
    (hB_pos : 0 < B) (hsigma_pos : 0 < sigma) (hsigma_lt_one : sigma < 1)
    (hconc : StrictDiscreteConcave h)
    (htail : Tendsto (powerTailQuotient h B sigma) atTop (nhds 1)) :
    seq.toSequence.ConvergesToProfile (targetShare p sigma) := by
  have htarget_simplex : targetShare p sigma ∈ stdSimplex ℝ (Fin m) := by
    constructor
    · intro i
      exact (targetShare_pos p hsigma_lt_one hp_pos i).le
    · exact sum_targetShare_eq_one p hsigma_lt_one hp_pos
  have hcontinuous : ContinuousOn (sourcePowerObjective p sigma)
      (stdSimplex ℝ (Fin m)) :=
    (continuous_sourcePowerObjective p sigma hsigma_pos.le).continuousOn
  have hstrict : ∀ x : Fin m → ℝ, x ∈ stdSimplex ℝ (Fin m) ->
      x ≠ targetShare p sigma ->
        sourcePowerObjective p sigma x <
          sourcePowerObjective p sigma (targetShare p sigma) := by
    intro x hx hx_ne
    exact sourcePowerObjective_lt_target_of_simplex_ne
      p hsigma_pos hsigma_lt_one hp_pos x hx.1 hx.2 hx_ne
  intro t
  change Tendsto
    (fun N : ℕ => AppliedModelingLib.Allocation.share (seq.allocation N) t)
    atTop (nhds (targetShare p sigma t))
  rw [Metric.tendsto_nhds]
  intro epsilon hepsilon_pos
  let epsilonHalf : ℝ := epsilon / 2
  have hepsilonHalf_pos : 0 < epsilonHalf := by
    dsimp [epsilonHalf]
    linarith
  obtain ⟨eta, heta_pos, hseparate⟩ :=
    AppliedModelingLib.Allocation.exists_gap_on_stdSimplex_of_strict_unique_max
      (sourcePowerObjective p sigma) (targetShare p sigma)
      htarget_simplex hcontinuous hstrict epsilonHalf hepsilonHalf_pos
  have hobjective_lower : ∀ᶠ N : ℕ in atTop,
      sourcePowerObjective p sigma (targetShare p sigma) - eta <
        sourcePowerObjective p sigma
          (fun i => AppliedModelingLib.Allocation.share (seq.allocation N) i) :=
    eventually_sourcePowerObjective_target_sub_lt_optimal
      p seq hp_pos hB_pos hsigma_pos hsigma_lt_one hconc htail heta_pos
  filter_upwards [eventually_gt_atTop 0, hobjective_lower] with N hN hobjectiveN
  have htotal_ne : AppliedModelingLib.Allocation.total (seq.allocation N) ≠ 0 := by
    rw [(seq.optimal N).1]
    exact Nat.ne_of_gt hN
  have hactual_simplex :
      (fun i => AppliedModelingLib.Allocation.share (seq.allocation N) i) ∈
        stdSimplex ℝ (Fin m) := by
    constructor
    · intro i
      exact AppliedModelingLib.Allocation.share_nonneg (seq.allocation N) i
    · exact AppliedModelingLib.Allocation.sum_share_eq_one_of_total_ne_zero
        (seq.allocation N) htotal_ne
  have hnot_far : ¬ epsilonHalf <
      |AppliedModelingLib.Allocation.share (seq.allocation N) t - targetShare p sigma t| := by
    intro hfar
    have hgapN := hseparate
      (fun i => AppliedModelingLib.Allocation.share (seq.allocation N) i)
      hactual_simplex ⟨t, hfar⟩
    exact (not_lt_of_ge hgapN) hobjectiveN
  have habs_le :
      |AppliedModelingLib.Allocation.share (seq.allocation N) t - targetShare p sigma t| ≤
        epsilonHalf :=
    le_of_not_gt hnot_far
  have habs_lt :
      |AppliedModelingLib.Allocation.share (seq.allocation N) t - targetShare p sigma t| <
        epsilon :=
    lt_of_le_of_lt habs_le (by
      dsimp [epsilonHalf]
      linarith)
  simpa [Real.dist_eq] using habs_lt

end AppendixD1GenericIV
end PRPKG24AccuracyDiversity
