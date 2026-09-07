import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.BigOperators

open Filter Topology
open Asymptotics
open scoped BigOperators

namespace AppliedModelingLib
namespace Math

/-- A sequence tends to zero. -/
def TendsToZero (ε : ℕ → ℝ) : Prop :=
  Tendsto ε atTop (nhds 0)

/-- `x n` is asymptotically equivalent to `y n`, expressed as `x n / y n -> 1`. -/
def AsymptoticEquivalent (x y : ℕ → ℝ) : Prop :=
  Tendsto (fun n => x n / y n) atTop (nhds 1)

/--
Eventual nonnegative upper bounds give ordinary Big-O bounds.  This is a
small bridge from exact algorithmic runtime inequalities to paper-style
Landau notation.
-/
theorem isBigO_of_eventually_abs_le
    {α : Type*} {l : Filter α} {f g : α → ℝ}
    (hg_nonneg : ∀ᶠ x in l, 0 ≤ g x)
    (hbound : ∀ᶠ x in l, |f x| ≤ g x) :
    Asymptotics.IsBigO l f g := by
  refine Asymptotics.IsBigO.of_bound' ?_
  filter_upwards [hg_nonneg, hbound] with x hg hx
  simpa [Real.norm_eq_abs, abs_of_nonneg hg] using hx

/--
Nonnegative functions bounded by a nonnegative comparison function are Big-O of
that comparison function.
-/
theorem isBigO_of_eventually_nonneg_le
    {α : Type*} {l : Filter α} {f g : α → ℝ}
    (hf_nonneg : ∀ᶠ x in l, 0 ≤ f x)
    (hg_nonneg : ∀ᶠ x in l, 0 ≤ g x)
    (hle : ∀ᶠ x in l, f x ≤ g x) :
    Asymptotics.IsBigO l f g := by
  refine isBigO_of_eventually_abs_le hg_nonneg ?_
  filter_upwards [hf_nonneg, hle] with x hf hx
  simpa [abs_of_nonneg hf] using hx

/--
Nonnegative functions bounded by a fixed nonnegative multiple of the comparison
function are Big-O of that comparison function.
-/
theorem isBigO_of_eventually_nonneg_le_const_mul
    {α : Type*} {l : Filter α} {f g : α → ℝ} {C : ℝ}
    (_hC : 0 ≤ C)
    (hf_nonneg : ∀ᶠ x in l, 0 ≤ f x)
    (hg_nonneg : ∀ᶠ x in l, 0 ≤ g x)
    (hle : ∀ᶠ x in l, f x ≤ C * g x) :
    Asymptotics.IsBigO l f g := by
  refine Asymptotics.IsBigO.of_bound C ?_
  filter_upwards [hf_nonneg, hg_nonneg, hle] with x hf hg hx
  simpa [Real.norm_eq_abs, abs_of_nonneg hf, abs_of_nonneg hg] using hx

/--
If a positive fixed multiple of a nonnegative function is eventually bounded
by a nonnegative comparison function, then the function is Big-O of that
comparison function.  This is the lower-bound counterpart of the usual
constant-multiple upper-bound packaging.
-/
theorem isBigO_of_eventually_pos_mul_le
    {α : Type*} {l : Filter α} {f g : α → ℝ} {c : ℝ}
    (hc : 0 < c)
    (hf_nonneg : ∀ᶠ x in l, 0 ≤ f x)
    (hg_nonneg : ∀ᶠ x in l, 0 ≤ g x)
    (hle : ∀ᶠ x in l, c * f x ≤ g x) :
    Asymptotics.IsBigO l f g := by
  refine isBigO_of_eventually_nonneg_le_const_mul
    (C := c⁻¹) (inv_nonneg.mpr hc.le) hf_nonneg hg_nonneg ?_
  filter_upwards [hle] with x hx
  calc
    f x = c⁻¹ * (c * f x) := by
      field_simp [hc.ne']
    _ ≤ c⁻¹ * g x := mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hc.le)

/--
Specialized Big-O bridge for quadratic log-style runtime envelopes
`C * g^2`.
-/
theorem isBigO_of_eventually_le_mul_sq
    {α : Type*} {l : Filter α} {f g : α → ℝ} {C : ℝ}
    (hC : 0 ≤ C)
    (hf_nonneg : ∀ᶠ x in l, 0 ≤ f x)
    (hle : ∀ᶠ x in l, f x ≤ C * (g x) ^ 2) :
    Asymptotics.IsBigO l f (fun x => C * (g x) ^ 2) := by
  refine isBigO_of_eventually_nonneg_le hf_nonneg ?_ hle
  filter_upwards with x
  exact mul_nonneg hC (sq_nonneg (g x))

/-- A sequence is bounded by C / N. -/
def TendsToZeroInv (ε : ℕ → ℝ) : Prop :=
  ∃ C > 0, ∀ N, 0 < N → |ε N| ≤ C / (N : ℝ)

/-- A sequence is bounded by C / sqrt(N). -/
def TendsToZeroInvSqrt (ε : ℕ → ℝ) : Prop :=
  ∃ C > 0, ∀ N, 0 < N → |ε N| ≤ C / Real.sqrt (N : ℝ)

/-- A sequence has exact paper-style `C / N` error rate. -/
def ExactInvRate (ε : ℕ → ℝ) : Prop :=
  ∃ C > 0, ∀ N, ε N = C / (N : ℝ)

/-- A sequence has exact paper-style `C / sqrt N` error rate. -/
def ExactInvSqrtRate (ε : ℕ → ℝ) : Prop :=
  ∃ C > 0, ∀ N, ε N = C / Real.sqrt (N : ℝ)

/-- A positive linear real rate along natural counts has exponentially
vanishing tail.  This is the standard numerical tail interface used by
concentration bounds with fixed positive coefficients.

Library provenance: this directly composes Mathlib's
`Real.tendsto_exp_neg_atTop_nhds_zero` from
[`Analysis/SpecialFunctions/Exp.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Analysis/SpecialFunctions/Exp.lean),
at the pinned Apache-2.0 Mathlib commit. No external Lean source is copied or
ported. -/
theorem tendsto_exp_neg_nat_mul_nhds_zero {rate : ℝ} (hrate : 0 < rate) :
    Tendsto (fun count : ℕ => Real.exp (-(rate * (count : ℝ)))) atTop (nhds 0) := by
  have hlinear : Tendsto (fun count : ℕ => rate * (count : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hrate
  exact Real.tendsto_exp_neg_atTop_nhds_zero.comp hlinear

/-- A fixed real numerator divided by powers of a real base greater than one
vanishes along natural exponents.

Library provenance: this directly composes Mathlib's
`tendsto_pow_atTop_atTop_of_one_lt` from
[`Analysis/SpecificLimits/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Analysis/SpecificLimits/Basic.lean),
at the pinned Apache-2.0 Mathlib commit. No external Lean source is copied or
ported. -/
theorem tendsto_const_div_pow_nat_nhds_zero {constant base : ℝ} (hbase : 1 < base) :
    Tendsto (fun exponent : ℕ => constant / base ^ exponent) atTop (nhds 0) := by
  exact tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt hbase)

/-- Every positive failure tolerance admits a nonnegative exponential
confidence level whose residual `exp (-confidence)` is strictly smaller.

Library provenance: this directly reuses Mathlib's
`Real.tendsto_exp_neg_atTop_nhds_zero` from
[`Analysis/SpecialFunctions/Exp.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Analysis/SpecialFunctions/Exp.lean),
at the pinned Apache-2.0 Mathlib commit. No external Lean source is copied or
ported. -/
theorem exists_nonneg_exp_neg_lt_of_pos {tolerance : ℝ} (htolerance : 0 < tolerance) :
    ∃ confidence : ℝ, 0 ≤ confidence ∧ Real.exp (-confidence) < tolerance := by
  have hsmall : ∀ᶠ confidence : ℝ in atTop, Real.exp (-confidence) < tolerance :=
    Real.tendsto_exp_neg_atTop_nhds_zero (isOpen_Iio.mem_nhds htolerance)
  rcases Filter.eventually_atTop.mp hsmall with ⟨confidence, hconfidence⟩
  refine ⟨max confidence 0, le_max_right _ _, ?_⟩
  exact hconfidence (max confidence 0) (le_max_left _ _)

/-- Positive roundwise tolerances admit a deterministic nonnegative
confidence schedule with a strictly smaller exponential residual in every
round. -/
theorem exists_nonneg_exp_neg_schedule_lt_of_pos
    (tolerance : ℕ → ℝ) (htolerance : ∀ round, 0 < tolerance round) :
    ∃ confidence : ℕ → ℝ, (∀ round, 0 ≤ confidence round) ∧
      ∀ round, Real.exp (-(confidence round)) < tolerance round := by
  classical
  choose confidence hconfidence_nonneg hconfidence using fun round =>
    exists_nonneg_exp_neg_lt_of_pos (htolerance round)
  exact ⟨confidence, hconfidence_nonneg, hconfidence⟩

/-- A positive fixed real rate eventually exceeds one after multiplication by
the natural sample count.  It packages the deterministic rate-gate inversion
common to exponential concentration bounds. -/
theorem eventually_one_le_nat_mul_of_pos {rate : ℝ} (hrate : 0 < rate) :
    ∀ᶠ count : ℕ in atTop, 1 ≤ (count : ℝ) * rate := by
  have hlinear : Tendsto (fun count : ℕ => rate * (count : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hrate
  simpa [mul_comm] using hlinear.eventually (eventually_ge_atTop 1)

/--
Changing finitely many entries of a zero-convergent error schedule preserves
zero convergence.
-/
theorem tendsToZero_if_lt_const
    {ε : ℕ → ℝ} (hε : TendsToZero ε) (threshold : ℕ) (C : ℝ) :
    TendsToZero (fun N => if N < threshold then C else ε N) := by
  rw [TendsToZero] at hε ⊢
  refine Tendsto.congr' ?_ hε
  filter_upwards [eventually_atTop.2
      ⟨threshold, fun N hN => hN⟩] with N hN
  simp [not_lt.mpr hN]

/--
Turn a family of eventual thresholds for tolerances `1 / (m + 1)` into a
single nonnegative error schedule.

At problem size `N`, the schedule uses the reciprocal of the largest tolerance
index whose threshold is at most `N`.  This is useful when an asymptotic proof
provides, for every fixed tolerance, a tail threshold, while an optimization
argument needs one concrete `o(1)` error sequence.
-/
noncomputable def reciprocalThresholdError (threshold : ℕ → ℕ) (N : ℕ) : ℝ :=
  1 / (((Nat.findGreatest (fun m => threshold m ≤ N) N + 1 : ℕ) : ℝ))

theorem reciprocalThresholdError_nonneg (threshold : ℕ → ℕ) (N : ℕ) :
    0 ≤ reciprocalThresholdError threshold N := by
  unfold reciprocalThresholdError
  positivity

theorem reciprocalThresholdError_tendsToZero (threshold : ℕ → ℕ) :
    TendsToZero (reciprocalThresholdError threshold) := by
  rw [TendsToZero]
  refine tendsto_order.2 ?_
  constructor
  · intro a ha
    filter_upwards with N
    have hnonneg := reciprocalThresholdError_nonneg threshold N
    linarith
  · intro b hb
    rcases exists_nat_one_div_lt hb with ⟨m, hm⟩
    let K : ℕ := max m (threshold m)
    refine eventually_atTop.2 ⟨K, ?_⟩
    intro N hN
    have hm_le_N : m ≤ N := le_trans (Nat.le_max_left m (threshold m)) hN
    have hthreshold_le_N : threshold m ≤ N :=
      le_trans (Nat.le_max_right m (threshold m)) hN
    have hfind_ge :
        m ≤ Nat.findGreatest (fun r => threshold r ≤ N) N :=
      Nat.le_findGreatest hm_le_N hthreshold_le_N
    have hden_le :
        (m + 1 : ℝ) ≤
          ((Nat.findGreatest (fun r => threshold r ≤ N) N + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ hfind_ge
    have hden_pos : 0 < (m + 1 : ℝ) := by positivity
    have hden_find_pos :
        0 <
          ((Nat.findGreatest (fun r => threshold r ≤ N) N + 1 : ℕ) : ℝ) := by
      positivity
    have hle :
        reciprocalThresholdError threshold N ≤ 1 / (m + 1 : ℝ) := by
      unfold reciprocalThresholdError
      exact one_div_le_one_div_of_le hden_pos hden_le
    exact lt_of_le_of_lt hle hm

theorem reciprocalThresholdError_le_of_threshold_le
    (threshold : ℕ → ℕ) {m N : ℕ}
    (hm_le_N : m ≤ N) (hthreshold_le_N : threshold m ≤ N) :
    reciprocalThresholdError threshold N ≤ 1 / (m + 1 : ℝ) := by
  have hfind_ge :
      m ≤ Nat.findGreatest (fun r => threshold r ≤ N) N :=
    Nat.le_findGreatest hm_le_N hthreshold_le_N
  have hden_le :
      (m + 1 : ℝ) ≤
        ((Nat.findGreatest (fun r => threshold r ≤ N) N + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ hfind_ge
  have hden_find_pos :
      0 <
        ((Nat.findGreatest (fun r => threshold r ≤ N) N + 1 : ℕ) : ℝ) := by
    positivity
  have hden_pos : 0 < (m + 1 : ℝ) := by positivity
  unfold reciprocalThresholdError
  exact one_div_le_one_div_of_le hden_pos hden_le

/--
Prefix-scaled envelope of a pointwise error sequence.

At problem size `N`, this records the largest product `ε q * q` among
`q ≤ N`, normalized by `N`.  Thus `prefixScaledError ε N * N` dominates every
prefix product.  If `ε q -> 0` and `ε` is nonnegative, then this normalized
prefix envelope also tends to zero.
-/
noncomputable def prefixScaledError (ε : ℕ → ℝ) (N : ℕ) : ℝ :=
  if h : N = 0 then 0
  else
    ((Finset.range (N + 1)).sup'
      (by exact ⟨0, by simp⟩)
      (fun q => ε q * (q : ℝ))) / (N : ℝ)

theorem prefixScaledError_nonneg
    (ε : ℕ → ℝ) (hε_nonneg : ∀ q, 0 ≤ ε q) (N : ℕ) :
    0 ≤ prefixScaledError ε N := by
  by_cases hN : N = 0
  · simp [prefixScaledError, hN]
  · have hzero_mem : 0 ∈ Finset.range (N + 1) := by simp
    have hsup_nonneg :
        0 ≤
          (Finset.range (N + 1)).sup'
            (by exact ⟨0, by simp⟩)
            (fun q => ε q * (q : ℝ)) := by
      simpa using
        (Finset.le_sup'
          (s := Finset.range (N + 1))
          (f := fun q => ε q * (q : ℝ)) hzero_mem)
    simp [prefixScaledError, hN]
    exact div_nonneg hsup_nonneg (Nat.cast_nonneg N)

theorem le_prefixScaledError_mul_nat
    (ε : ℕ → ℝ) {q N : ℕ} (hN_pos : 0 < N) (hq_le_N : q ≤ N) :
    ε q * (q : ℝ) ≤ prefixScaledError ε N * (N : ℝ) := by
  have hq_mem : q ∈ Finset.range (N + 1) := by
    simp
    omega
  have hle :
      ε q * (q : ℝ) ≤
        (Finset.range (N + 1)).sup'
          (by exact ⟨0, by simp⟩)
          (fun q => ε q * (q : ℝ)) :=
    Finset.le_sup'
      (s := Finset.range (N + 1))
      (f := fun q => ε q * (q : ℝ)) hq_mem
  have hN_ne : (N : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hN_pos)
  calc
    ε q * (q : ℝ)
        ≤ (Finset.range (N + 1)).sup'
            (by exact ⟨0, by simp⟩)
            (fun q => ε q * (q : ℝ)) := hle
    _ = prefixScaledError ε N * (N : ℝ) := by
          simp [prefixScaledError, Nat.ne_of_gt hN_pos, hN_ne]

theorem prefixScaledError_tendsToZero
    (ε : ℕ → ℝ) (hε_nonneg : ∀ q, 0 ≤ ε q)
    (hε_zero : TendsToZero ε) :
    TendsToZero (prefixScaledError ε) := by
  rw [TendsToZero] at hε_zero ⊢
  refine tendsto_order.2 ?_
  constructor
  · intro a ha
    filter_upwards with N
    have hnonneg := prefixScaledError_nonneg ε hε_nonneg N
    linarith
  · intro b hb
    have hhalf_pos : 0 < b / 2 := by linarith
    have hε_small_eventually :
        ∀ᶠ q in atTop, ε q < b / 2 := by
      exact hε_zero.eventually (eventually_lt_nhds hhalf_pos)
    rcases eventually_atTop.1 hε_small_eventually with
      ⟨K, hK⟩
    let C : ℝ :=
      max 0
        ((Finset.range (K + 1)).sup'
          (by exact ⟨0, by simp⟩)
          (fun q => ε q * (q : ℝ)))
    have hC_div_zero :
        Tendsto (fun N : ℕ => C / (N : ℝ)) atTop (nhds 0) :=
      tendsto_const_div_atTop_nhds_zero_nat C
    have hC_small_eventually :
        ∀ᶠ N : ℕ in atTop, C / (N : ℝ) < b / 2 :=
      hC_div_zero.eventually (eventually_lt_nhds hhalf_pos)
    filter_upwards
      [hC_small_eventually,
        eventually_atTop.2 ⟨K + 1, fun N hN => hN⟩]
      with N hC_small hN_large
    have hN_pos : 0 < N := by omega
    have hN_real_pos : 0 < (N : ℝ) := by exact_mod_cast hN_pos
    have hN_real_ne : (N : ℝ) ≠ 0 := ne_of_gt hN_real_pos
    have hsup_le :
        (Finset.range (N + 1)).sup'
            (by exact ⟨0, by simp⟩)
            (fun q => ε q * (q : ℝ)) ≤
          (b / 2) * (N : ℝ) := by
      refine Finset.sup'_le
        (s := Finset.range (N + 1))
        (H := by exact ⟨0, by simp⟩)
        (f := fun q => ε q * (q : ℝ)) ?_
      intro q hq_mem
      have hq_le_N : q ≤ N := by
        simp at hq_mem
        omega
      by_cases hK_le_q : K ≤ q
      · have hε_q_le : ε q ≤ b / 2 := le_of_lt (hK q hK_le_q)
        calc
          ε q * (q : ℝ)
              ≤ (b / 2) * (q : ℝ) :=
                mul_le_mul_of_nonneg_right hε_q_le (Nat.cast_nonneg q)
          _ ≤ (b / 2) * (N : ℝ) := by
                exact mul_le_mul_of_nonneg_left
                  (by exact_mod_cast hq_le_N) hhalf_pos.le
      · have hq_lt_K : q < K := Nat.lt_of_not_ge hK_le_q
        have hq_prefix_mem : q ∈ Finset.range (K + 1) := by
          simp
          omega
        have hterm_le_C :
            ε q * (q : ℝ) ≤ C := by
          have hterm_le_sup :
              ε q * (q : ℝ) ≤
                (Finset.range (K + 1)).sup'
                  (by exact ⟨0, by simp⟩)
                  (fun q => ε q * (q : ℝ)) :=
            Finset.le_sup'
              (s := Finset.range (K + 1))
              (f := fun q => ε q * (q : ℝ)) hq_prefix_mem
          exact le_trans hterm_le_sup (le_max_right _ _)
        have hC_lt :
            C < (b / 2) * (N : ℝ) := by
          calc
            C = (C / (N : ℝ)) * (N : ℝ) := by
                  field_simp [hN_real_ne]
            _ < (b / 2) * (N : ℝ) :=
                  mul_lt_mul_of_pos_right hC_small hN_real_pos
        exact le_trans hterm_le_C (le_of_lt hC_lt)
    have hpref_le_half : prefixScaledError ε N ≤ b / 2 := by
      simp [prefixScaledError, Nat.ne_of_gt hN_pos]
      calc
        ((Finset.range (N + 1)).sup'
            (by exact ⟨0, by simp⟩)
            (fun q => ε q * (q : ℝ))) / (N : ℝ)
            ≤ ((b / 2) * (N : ℝ)) / (N : ℝ) :=
              div_le_div_of_nonneg_right hsup_le hN_real_pos.le
        _ = b / 2 := by
              field_simp [hN_real_ne]
    linarith

namespace AsymptoticEquivalent

theorem congr_left_eventually
    {x x' y : ℕ → ℝ}
    (hxx' : ∀ᶠ n in atTop, x n = x' n)
    (h : AsymptoticEquivalent x' y) :
    AsymptoticEquivalent x y := by
  rw [AsymptoticEquivalent] at h ⊢
  refine Tendsto.congr' ?_ h
  filter_upwards [hxx'] with n hn
  rw [hn]

theorem congr_right_eventually
    {x y y' : ℕ → ℝ}
    (hyy' : ∀ᶠ n in atTop, y n = y' n)
    (h : AsymptoticEquivalent x y) :
    AsymptoticEquivalent x y' := by
  rw [AsymptoticEquivalent] at h ⊢
  refine Tendsto.congr' ?_ h
  filter_upwards [hyy'] with n hn
  rw [hn]

theorem eventually_ratio_mem_Icc
    {x y : ℕ → ℝ} (h : AsymptoticEquivalent x y)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      1 - ε ≤ x n / y n ∧ x n / y n ≤ 1 + ε := by
  have hlow : ∀ᶠ n in atTop, 1 - ε ≤ x n / y n := by
    exact h.eventually_const_le (by linarith)
  have hhigh : ∀ᶠ n in atTop, x n / y n ≤ 1 + ε := by
    exact h.eventually_le_const (by linarith)
  filter_upwards [hlow, hhigh] with n hnlow hnhigh
  exact ⟨hnlow, hnhigh⟩

theorem eventually_sandwich_of_pos_right
    {x y : ℕ → ℝ} (h : AsymptoticEquivalent x y)
    (hy_pos : ∀ᶠ n in atTop, 0 < y n)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      (1 - ε) * y n ≤ x n ∧ x n ≤ (1 + ε) * y n := by
  filter_upwards [h.eventually_ratio_mem_Icc hε, hy_pos] with n hratio hy
  have heq : x n = (x n / y n) * y n := by
    field_simp [ne_of_gt hy]
  constructor
  · calc
      (1 - ε) * y n ≤ (x n / y n) * y n :=
        mul_le_mul_of_nonneg_right hratio.1 hy.le
      _ = x n := by rw [← heq]
  · calc
      x n = (x n / y n) * y n := heq
      _ ≤ (1 + ε) * y n :=
        mul_le_mul_of_nonneg_right hratio.2 hy.le

end AsymptoticEquivalent

/--
If finitely many terms are each asymptotic to a nonzero coefficient times a
common scale, then their finite sum is asymptotic to the sum of the
coefficients times that scale.
-/
theorem finite_sum_asymptoticEquivalent_common_scale
    {ι : Type*} [Fintype ι]
    (term : ι → ℕ → ℝ) (coeff : ι → ℝ) (scale : ℕ → ℝ)
    (hcoeff_ne : ∀ i, coeff i ≠ 0)
    (htotal_ne : (∑ i : ι, coeff i) ≠ 0)
    (hscale_ne : ∀ᶠ n in atTop, scale n ≠ 0)
    (hterm :
      ∀ i,
        AsymptoticEquivalent (term i)
          (fun n => coeff i * scale n)) :
    AsymptoticEquivalent
      (fun n => ∑ i : ι, term i n)
      (fun n => (∑ i : ι, coeff i) * scale n) := by
  have hterm_scaled :
      ∀ i,
        Tendsto (fun n => term i n / scale n) atTop (nhds (coeff i)) := by
    intro i
    have hmul :
        Tendsto
          (fun n => term i n / (coeff i * scale n) * coeff i)
          atTop (nhds (1 * coeff i)) := by
      simpa [mul_comm] using (hterm i).const_mul (coeff i)
    refine Tendsto.congr' ?_ (by simpa using hmul)
    filter_upwards [hscale_ne] with n hn_scale
    have hi := hcoeff_ne i
    field_simp [hi, hn_scale]
  have hsum_scaled :
      Tendsto
        (fun n => ∑ i : ι, term i n / scale n)
        atTop (nhds (∑ i : ι, coeff i)) := by
    exact tendsto_finset_sum Finset.univ
      (fun i _ => hterm_scaled i)
  have hratio_scaled :
      Tendsto
        (fun n => (∑ i : ι, term i n / scale n) /
          (∑ i : ι, coeff i))
        atTop (nhds 1) := by
    have hdiv := hsum_scaled.div_const (∑ i : ι, coeff i)
    simpa [htotal_ne] using hdiv
  refine Tendsto.congr' ?_ hratio_scaled
  filter_upwards [hscale_ne] with n hn_scale
  have hsum_div :
      (∑ i : ι, term i n / scale n) =
        (∑ i : ι, term i n) / scale n := by
    simp_rw [div_eq_mul_inv]
    rw [Finset.sum_mul]
  rw [hsum_div]
  field_simp [htotal_ne, hn_scale]

/--
If a main term is asymptotic to `coeff * scale` and a remainder is `o(scale)`,
their sum has the same asymptotic equivalent.
-/
theorem asymptoticEquivalent_add_negligible_common_scale
    (main remainder scale : ℕ → ℝ) (coeff : ℝ)
    (hcoeff_ne : coeff ≠ 0)
    (hscale_ne : ∀ᶠ n in atTop, scale n ≠ 0)
    (hmain :
      AsymptoticEquivalent main
        (fun n => coeff * scale n))
    (hremainder :
      Tendsto (fun n => remainder n / scale n) atTop (nhds 0)) :
    AsymptoticEquivalent
      (fun n => main n + remainder n)
      (fun n => coeff * scale n) := by
  have hremainder_ratio :
      Tendsto
        (fun n => remainder n / (coeff * scale n))
        atTop (nhds 0) := by
    have hdiv :=
      hremainder.div_const coeff
    refine Tendsto.congr' ?_ (by simpa [hcoeff_ne] using hdiv)
    filter_upwards [hscale_ne] with n hn_scale
    field_simp [hcoeff_ne, hn_scale]
  rw [AsymptoticEquivalent] at hmain ⊢
  have hsum := hmain.add hremainder_ratio
  refine Tendsto.congr' ?_ (by simpa using hsum)
  filter_upwards [hscale_ne] with n hn_scale
  field_simp [hcoeff_ne, hn_scale]

theorem ExactInvRate_implies_TendsToZeroInv (ε : ℕ → ℝ) :
    ExactInvRate ε → TendsToZeroInv ε := by
  intro ⟨C, hCpos, hε⟩
  refine ⟨C, hCpos, ?_⟩
  intro N hN
  rw [hε N]
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN
  have hnonneg : 0 ≤ C / (N : ℝ) := div_nonneg hCpos.le hNpos.le
  rw [abs_of_nonneg hnonneg]

theorem ExactInvSqrtRate_implies_TendsToZeroInvSqrt (ε : ℕ → ℝ) :
    ExactInvSqrtRate ε → TendsToZeroInvSqrt ε := by
  intro ⟨C, hCpos, hε⟩
  refine ⟨C, hCpos, ?_⟩
  intro N hN
  rw [hε N]
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN
  have hsqrt_pos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNpos
  have hnonneg : 0 ≤ C / Real.sqrt (N : ℝ) := div_nonneg hCpos.le hsqrt_pos.le
  rw [abs_of_nonneg hnonneg]

theorem TendsToZeroInv_implies_TendsToZero (ε : ℕ → ℝ) :
    TendsToZeroInv ε → TendsToZero ε := by
  intro ⟨C, hCpos, hbound⟩
  rw [TendsToZero]
  have h_zero : Tendsto (fun N : ℕ => C / (N : ℝ)) atTop (nhds 0) := tendsto_const_div_atTop_nhds_zero_nat C
  have h_neg_zero : Tendsto (fun N : ℕ => -(C / (N : ℝ))) atTop (nhds 0) := by
    have h := h_zero.neg
    rwa [neg_zero] at h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' h_neg_zero h_zero
  · filter_upwards [eventually_gt_atTop 0] with N hN
    have h1 := hbound N hN
    rw [abs_le] at h1
    exact h1.1
  · filter_upwards [eventually_gt_atTop 0] with N hN
    have h1 := hbound N hN
    rw [abs_le] at h1
    exact h1.2

theorem ExactInvRate_implies_TendsToZero (ε : ℕ → ℝ) :
    ExactInvRate ε → TendsToZero ε := by
  intro hε
  exact TendsToZeroInv_implies_TendsToZero ε
    (ExactInvRate_implies_TendsToZeroInv ε hε)

theorem TendsToZeroInvSqrt_implies_TendsToZero (ε : ℕ → ℝ) :
    TendsToZeroInvSqrt ε → TendsToZero ε := by
  intro ⟨C, hCpos, hbound⟩
  rw [TendsToZero]
  have h_sqrt_atTop :
      Tendsto (fun N : ℕ => Real.sqrt (N : ℝ)) atTop atTop := by
    exact Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have h_zero :
      Tendsto (fun N : ℕ => C / Real.sqrt (N : ℝ)) atTop (nhds 0) := by
    exact Filter.Tendsto.const_div_atTop h_sqrt_atTop C
  have h_neg_zero :
      Tendsto (fun N : ℕ => -(C / Real.sqrt (N : ℝ))) atTop (nhds 0) := by
    have h := h_zero.neg
    rwa [neg_zero] at h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' h_neg_zero h_zero
  · filter_upwards [eventually_gt_atTop 0] with N hN
    have h1 := hbound N hN
    rw [abs_le] at h1
    exact h1.1
  · filter_upwards [eventually_gt_atTop 0] with N hN
    have h1 := hbound N hN
    rw [abs_le] at h1
    exact h1.2

theorem ExactInvSqrtRate_implies_TendsToZero (ε : ℕ → ℝ) :
    ExactInvSqrtRate ε → TendsToZero ε := by
  intro hε
  exact TendsToZeroInvSqrt_implies_TendsToZero ε
    (ExactInvSqrtRate_implies_TendsToZeroInvSqrt ε hε)

/-- A sequence tends to zero if it is eventually dominated by `C / N`. -/
theorem TendsToZero_of_eventually_abs_le_inv (ε : ℕ → ℝ) {C : ℝ}
    (_hC : 0 < C) (hbound : ∀ᶠ N in atTop, |ε N| ≤ C / (N : ℝ)) :
    TendsToZero ε := by
  rw [TendsToZero]
  have h_zero : Tendsto (fun N : ℕ => C / (N : ℝ)) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat C
  have h_neg_zero : Tendsto (fun N : ℕ => -(C / (N : ℝ))) atTop (nhds 0) := by
    have h := h_zero.neg
    rwa [neg_zero] at h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' h_neg_zero h_zero
  · filter_upwards [hbound, eventually_gt_atTop 0] with N hN hNpos
    rw [abs_le] at hN
    exact hN.1
  · filter_upwards [hbound, eventually_gt_atTop 0] with N hN hNpos
    rw [abs_le] at hN
    exact hN.2

/-- A nonnegative sequence bounded by `C / N` tends to zero. -/
theorem TendsToZero_of_nonneg_le_const_div
    (ε : ℕ → ℝ) {C : ℝ}
    (hC : 0 < C)
    (hnonneg : ∀ N, 0 ≤ ε N)
    (hbound : ∀ N, 0 < N → ε N ≤ C / (N : ℝ)) :
    TendsToZero ε := by
  refine TendsToZero_of_eventually_abs_le_inv ε hC ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  rw [abs_of_nonneg (hnonneg N)]
  exact hbound N hN

/--
A sequence tends to zero if its absolute value is eventually bounded by another
sequence tending to zero.
-/
theorem TendsToZero_of_eventually_abs_le_tendsto_zero
    (ε bound : ℕ → ℝ)
    (hbound_zero : Tendsto bound atTop (nhds 0))
    (hbound : ∀ᶠ N in atTop, |ε N| ≤ bound N) :
    TendsToZero ε := by
  rw [TendsToZero]
  have hneg_zero : Tendsto (fun N => -bound N) atTop (nhds 0) := by
    have h := hbound_zero.neg
    rwa [neg_zero] at h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hneg_zero hbound_zero
  · filter_upwards [hbound] with N hN
    exact (abs_le.mp hN).1
  · filter_upwards [hbound] with N hN
    exact (abs_le.mp hN).2

/--
The integer sample count `floor (N * g)` has asymptotic rate `g`.
This is the deterministic normalization step for floor-sampled
large-deviation statements.
-/
theorem tendsto_nat_floor_mul_const_div_nat
    {g : ℝ} (hg_nonneg : 0 ≤ g) :
    Tendsto
      (fun N : ℕ => ((Nat.floor ((N : ℝ) * g) : ℝ) / (N : ℝ)))
      atTop (nhds g) := by
  have hlower_tendsto :
      Tendsto (fun N : ℕ => g - 1 / (N : ℝ)) atTop (nhds g) := by
    have hzero :
        Tendsto (fun N : ℕ => (1 : ℝ) / (N : ℝ)) atTop (nhds 0) :=
      tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)
    simpa using (tendsto_const_nhds.sub hzero)
  have hupper_tendsto :
      Tendsto (fun N : ℕ => g) atTop (nhds g) :=
    tendsto_const_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hlower_tendsto hupper_tendsto ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with N hN
    have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN
    have hfloor_gt :
        (N : ℝ) * g - 1 <
          (Nat.floor ((N : ℝ) * g) : ℝ) := by
      have hlt :
          (N : ℝ) * g <
            (Nat.floor ((N : ℝ) * g) : ℝ) + 1 :=
        Nat.lt_floor_add_one ((N : ℝ) * g)
      linarith
    have hdiv :
        ((N : ℝ) * g - 1) / (N : ℝ) ≤
          (Nat.floor ((N : ℝ) * g) : ℝ) / (N : ℝ) :=
      div_le_div_of_nonneg_right hfloor_gt.le hNpos.le
    have hleft :
        ((N : ℝ) * g - 1) / (N : ℝ) = g - 1 / (N : ℝ) := by
      field_simp [hNpos.ne']
    simpa [hleft] using hdiv
  · filter_upwards [eventually_gt_atTop 0] with N hN
    have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN
    have harg_nonneg : 0 ≤ (N : ℝ) * g :=
      mul_nonneg (Nat.cast_nonneg N) hg_nonneg
    have hfloor_le :
        (Nat.floor ((N : ℝ) * g) : ℝ) ≤ (N : ℝ) * g :=
      Nat.floor_le harg_nonneg
    have hdiv :
        (Nat.floor ((N : ℝ) * g) : ℝ) / (N : ℝ) ≤
          ((N : ℝ) * g) / (N : ℝ) :=
      div_le_div_of_nonneg_right hfloor_le hNpos.le
    have hright : ((N : ℝ) * g) / (N : ℝ) = g := by
      field_simp [hNpos.ne']
    exact hdiv.trans_eq hright

/--
Uniform one-step floor-grid approximation: for `Q > 0` and `x ≥ 0`,
`floor (Q*x)/Q` is within `1/Q` of `x`.
-/
theorem nat_floor_mul_div_sub_abs_lt_inv
    {Q : ℕ} (hQ : 0 < Q) {x : ℝ} (hx : 0 ≤ x) :
    |(((Nat.floor ((Q : ℝ) * x) : ℝ) / (Q : ℝ)) - x)| <
      1 / (Q : ℝ) := by
  let n : ℕ := Nat.floor ((Q : ℝ) * x)
  have hQpos : 0 < (Q : ℝ) := by exact_mod_cast hQ
  have hfloor_le : (n : ℝ) ≤ (Q : ℝ) * x := by
    dsimp [n]
    exact Nat.floor_le (mul_nonneg hQpos.le hx)
  have hfloor_div_le : (n : ℝ) / (Q : ℝ) ≤ x := by
    rw [div_le_iff₀ hQpos]
    simpa [mul_comm] using hfloor_le
  have hscaled_lt : (Q : ℝ) * x < (n : ℝ) + 1 := by
    dsimp [n]
    exact Nat.lt_floor_add_one ((Q : ℝ) * x)
  have hx_lt : x < ((n : ℝ) + 1) / (Q : ℝ) := by
    rw [lt_div_iff₀ hQpos]
    simpa [mul_comm] using hscaled_lt
  have hright : (n : ℝ) / (Q : ℝ) - x < 1 / (Q : ℝ) := by
    have hnonpos : (n : ℝ) / (Q : ℝ) - x ≤ 0 := by linarith
    have hone_pos : 0 < 1 / (Q : ℝ) := by positivity
    linarith
  have hleft : -(1 / (Q : ℝ)) < (n : ℝ) / (Q : ℝ) - x := by
    have hx_lt_add : x < (n : ℝ) / (Q : ℝ) + 1 / (Q : ℝ) := by
      calc
        x < ((n : ℝ) + 1) / (Q : ℝ) := hx_lt
        _ = (n : ℝ) / (Q : ℝ) + 1 / (Q : ℝ) := by ring
    linarith
  simpa [n] using abs_lt.mpr ⟨hleft, hright⟩

/--
Floor selector for source-style finite parameter choices: if
`s = floor (m / a)`, then `a * (s - 1) < m`.  The subtraction makes the
inequality strict even when `m / a` is an integer.
-/
theorem nat_mul_floor_div_sub_one_lt
    {m a : ℕ} (hm : 0 < m) (ha : 0 < a) :
    (a : ℝ) * (((Nat.floor ((m : ℝ) / (a : ℝ)) - 1 : ℕ) : ℝ)) <
      (m : ℝ) := by
  let s : ℕ := Nat.floor ((m : ℝ) / (a : ℝ))
  have ha_real_pos : 0 < (a : ℝ) := by exact_mod_cast ha
  by_cases hs_zero : s = 0
  · simp [s, hs_zero]
    exact_mod_cast hm
  · have hs_pos : 0 < s := Nat.pos_of_ne_zero hs_zero
    have hsub_lt_nat : s - 1 < s := by omega
    have hsub_lt : (((s - 1 : ℕ) : ℝ)) < (s : ℝ) := by
      exact_mod_cast hsub_lt_nat
    have harg_nonneg : 0 ≤ (m : ℝ) / (a : ℝ) := by
      exact div_nonneg (Nat.cast_nonneg _) ha_real_pos.le
    have hfloor_le : (s : ℝ) ≤ (m : ℝ) / (a : ℝ) := by
      simpa [s] using Nat.floor_le harg_nonneg
    have hleft_lt :
        (a : ℝ) * (((s - 1 : ℕ) : ℝ)) < (a : ℝ) * (s : ℝ) :=
      mul_lt_mul_of_pos_left hsub_lt ha_real_pos
    have hright_le :
        (a : ℝ) * (s : ℝ) ≤ (a : ℝ) * ((m : ℝ) / (a : ℝ)) :=
      mul_le_mul_of_nonneg_left hfloor_le ha_real_pos.le
    have hmul_div : (a : ℝ) * ((m : ℝ) / (a : ℝ)) = (m : ℝ) := by
      field_simp [ha_real_pos.ne']
    exact lt_of_lt_of_le hleft_lt (by simpa [hmul_div] using hright_le)

/--
Floor-division bridge: if `a * n <= m` over the reals, then
`n <= floor(m/a)`.
-/
theorem nat_le_floor_div_of_mul_le
    {m a n : ℕ} (ha : 0 < a)
    (h : (a : ℝ) * (n : ℝ) ≤ (m : ℝ)) :
    n ≤ Nat.floor ((m : ℝ) / (a : ℝ)) := by
  have ha_real_pos : 0 < (a : ℝ) := by exact_mod_cast ha
  have hn_le_div : (n : ℝ) ≤ (m : ℝ) / (a : ℝ) := by
    rw [le_div_iff₀ ha_real_pos]
    simpa [mul_comm] using h
  exact Nat.le_floor hn_le_div

/--
Strict floor-division bridge: if `a * n < m` over the reals, then
`n <= floor(m/a)`.
-/
theorem nat_le_floor_div_of_mul_lt
    {m a n : ℕ} (ha : 0 < a)
    (h : (a : ℝ) * (n : ℝ) < (m : ℝ)) :
    n ≤ Nat.floor ((m : ℝ) / (a : ℝ)) :=
  nat_le_floor_div_of_mul_le ha h.le

/--
Logarithmic floor-power selector: for `1 < k` and `1 ≤ s`, if
`p = floor(log s / (2 log k))`, then `k^(2p) ≤ s`.
-/
theorem pow_two_mul_nat_floor_log_div_le
    {k s : ℕ} (hk : 1 < k) (hs : 1 ≤ s) :
    ((k : ℝ) ^
        (2 * Nat.floor (Real.log (s : ℝ) / (2 * Real.log (k : ℝ))) : ℕ)) ≤
      (s : ℝ) := by
  let p : ℕ := Nat.floor (Real.log (s : ℝ) / (2 * Real.log (k : ℝ)))
  have hk_real_pos : 0 < (k : ℝ) := by exact_mod_cast (zero_lt_one.trans hk)
  have hs_real_pos : 0 < (s : ℝ) := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hs)
  have hlogk_pos : 0 < Real.log (k : ℝ) := by
    exact Real.log_pos (by exact_mod_cast hk)
  have hlogs_nonneg : 0 ≤ Real.log (s : ℝ) := by
    exact Real.log_nonneg (by exact_mod_cast hs)
  have harg_nonneg :
      0 ≤ Real.log (s : ℝ) / (2 * Real.log (k : ℝ)) := by
    exact div_nonneg hlogs_nonneg (by positivity)
  have hfloor_le :
      (p : ℝ) ≤ Real.log (s : ℝ) / (2 * Real.log (k : ℝ)) := by
    simpa [p] using Nat.floor_le harg_nonneg
  have hp_log :
      (2 * (p : ℝ)) * Real.log (k : ℝ) ≤ Real.log (s : ℝ) := by
    have hmul :=
      mul_le_mul_of_nonneg_right hfloor_le (by positivity : 0 ≤ 2 * Real.log (k : ℝ))
    have hden_ne : 2 * Real.log (k : ℝ) ≠ 0 := by positivity
    calc
      (2 * (p : ℝ)) * Real.log (k : ℝ) =
          (p : ℝ) * (2 * Real.log (k : ℝ)) := by ring
      _ ≤ (Real.log (s : ℝ) / (2 * Real.log (k : ℝ))) *
            (2 * Real.log (k : ℝ)) := hmul
      _ = Real.log (s : ℝ) := by
            field_simp [hden_ne]
  have hlogpow :
      Real.log ((k : ℝ) ^ (2 * p)) ≤ Real.log (s : ℝ) := by
    rw [Real.log_pow]
    norm_num
    simpa [mul_assoc, mul_comm, mul_left_comm] using hp_log
  have hpow_pos : 0 < (k : ℝ) ^ (2 * p) := pow_pos hk_real_pos _
  have hpow_le : (k : ℝ) ^ (2 * p) ≤ (s : ℝ) :=
    (Real.log_le_log_iff hpow_pos hs_real_pos).mp hlogpow
  simpa [p] using hpow_le

/--
Logarithmic ceiling-power selector: for `1 < k` and `1 ≤ s`, if
`p = ceil(log s / (2 log k))`, then `s ≤ k^(2p)`.
-/
theorem le_pow_two_mul_nat_ceil_log_div
    {k s : ℕ} (hk : 1 < k) (hs : 1 ≤ s) :
    (s : ℝ) ≤
      ((k : ℝ) ^
        (2 * Nat.ceil (Real.log (s : ℝ) / (2 * Real.log (k : ℝ))) : ℕ)) := by
  let p : ℕ := Nat.ceil (Real.log (s : ℝ) / (2 * Real.log (k : ℝ)))
  have hk_real_pos : 0 < (k : ℝ) := by exact_mod_cast (zero_lt_one.trans hk)
  have hs_real_pos : 0 < (s : ℝ) := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hs)
  have hlogk_pos : 0 < Real.log (k : ℝ) := by
    exact Real.log_pos (by exact_mod_cast hk)
  have hceil_ge :
      Real.log (s : ℝ) / (2 * Real.log (k : ℝ)) ≤ (p : ℝ) := by
    simpa [p] using Nat.le_ceil (Real.log (s : ℝ) / (2 * Real.log (k : ℝ)))
  have hlog_le :
      Real.log (s : ℝ) ≤ (2 * (p : ℝ)) * Real.log (k : ℝ) := by
    have hmul :=
      mul_le_mul_of_nonneg_right hceil_ge (by positivity : 0 ≤ 2 * Real.log (k : ℝ))
    have hden_ne : 2 * Real.log (k : ℝ) ≠ 0 := by positivity
    calc
      Real.log (s : ℝ) =
          (Real.log (s : ℝ) / (2 * Real.log (k : ℝ))) *
            (2 * Real.log (k : ℝ)) := by
            field_simp [hden_ne]
      _ ≤ (p : ℝ) * (2 * Real.log (k : ℝ)) := hmul
      _ = (2 * (p : ℝ)) * Real.log (k : ℝ) := by ring
  have hlogpow :
      Real.log (s : ℝ) ≤ Real.log ((k : ℝ) ^ (2 * p)) := by
    rw [Real.log_pow]
    norm_num
    simpa [mul_assoc, mul_comm, mul_left_comm] using hlog_le
  have hpow_pos : 0 < (k : ℝ) ^ (2 * p) := pow_pos hk_real_pos _
  have hs_le : (s : ℝ) ≤ (k : ℝ) ^ (2 * p) :=
    (Real.log_le_log_iff hs_real_pos hpow_pos).mp hlogpow
  simpa [p] using hs_le

/--
A nonnegative real floor is at least half the original value once the original
value is at least one.
-/
theorem half_le_nat_floor_of_one_le {x : ℝ} (hx : 1 ≤ x) :
    x / 2 ≤ (Nat.floor x : ℝ) := by
  by_cases hx_lt_two : x < 2
  · have hfloor_pos : 0 < Nat.floor x := Nat.floor_pos.mpr hx
    have hone_le_floor : (1 : ℝ) ≤ (Nat.floor x : ℝ) := by
      exact_mod_cast hfloor_pos
    calc
      x / 2 ≤ 1 := by linarith
      _ ≤ (Nat.floor x : ℝ) := hone_le_floor
  · have hx_two : 2 ≤ x := le_of_not_gt hx_lt_two
    have hfloor_lt : x < (Nat.floor x : ℝ) + 1 :=
      Nat.lt_floor_add_one x
    have hx_half : x / 2 ≤ x - 1 := by linarith
    calc
      x / 2 ≤ x - 1 := hx_half
      _ ≤ (Nat.floor x : ℝ) := le_of_lt (by linarith)

/--
If `s >= k^2`, then the logarithmic selector argument
`log s / (2 log k)` is at least one.
-/
theorem one_le_log_div_of_sq_le
    {k s : ℕ} (hk : 1 < k)
    (hsq : (k : ℝ) ^ 2 ≤ (s : ℝ)) :
    (1 : ℝ) ≤ Real.log (s : ℝ) / (2 * Real.log (k : ℝ)) := by
  have hk_real_pos : 0 < (k : ℝ) := by exact_mod_cast (zero_lt_one.trans hk)
  have hk_sq_pos : 0 < (k : ℝ) ^ 2 := pow_pos hk_real_pos _
  have hlog_sq :
      Real.log ((k : ℝ) ^ 2) ≤ Real.log (s : ℝ) :=
    Real.log_le_log hk_sq_pos hsq
  have htwo_log :
      2 * Real.log (k : ℝ) ≤ Real.log (s : ℝ) := by
    rw [Real.log_pow] at hlog_sq
    norm_num at hlog_sq
    simpa using hlog_sq
  have hden_pos : 0 < 2 * Real.log (k : ℝ) := by
    have hlogk_pos : 0 < Real.log (k : ℝ) := by
      exact Real.log_pos (by exact_mod_cast hk)
    positivity
  rw [le_div_iff₀ hden_pos]
  simpa using htwo_log

/--
If `s` is at least `k^2`, then the logarithmic floor-power selector is at
least one.
-/
theorem one_le_nat_floor_log_div_of_sq_le
    {k s : ℕ} (hk : 1 < k)
    (hsq : (k : ℝ) ^ 2 ≤ (s : ℝ)) :
    1 ≤ Nat.floor (Real.log (s : ℝ) / (2 * Real.log (k : ℝ))) := by
  apply Nat.le_floor
  simpa using one_le_log_div_of_sq_le (k := k) (s := s) hk hsq

/--
If `s >= k^2`, the floor-power selector keeps a constant fraction of the
source logarithmic ratio.
-/
theorem half_log_div_le_nat_floor_log_div_of_sq_le
    {k s : ℕ} (hk : 1 < k)
    (hsq : (k : ℝ) ^ 2 ≤ (s : ℝ)) :
    Real.log (s : ℝ) / (4 * Real.log (k : ℝ)) ≤
      (Nat.floor (Real.log (s : ℝ) / (2 * Real.log (k : ℝ))) : ℝ) := by
  have hone :
      (1 : ℝ) ≤ Real.log (s : ℝ) / (2 * Real.log (k : ℝ)) :=
    one_le_log_div_of_sq_le (k := k) (s := s) hk hsq
  have hhalf :=
    half_le_nat_floor_of_one_le
      (x := Real.log (s : ℝ) / (2 * Real.log (k : ℝ))) hone
  have hrearrange :
      (Real.log (s : ℝ) / (2 * Real.log (k : ℝ))) / 2 =
        Real.log (s : ℝ) / (4 * Real.log (k : ℝ)) := by ring
  simpa [hrearrange] using hhalf

/--
One-step dyadic floor-window arithmetic.  For `x ∈ [0,1]`, the refined grid
index `floor((2*M - 1) * x)` stays within the two-index window around
`2 * floor(M*x)`.
-/
theorem nat_floor_two_mul_sub_one_mul_window
    {M : ℕ} (hM : 0 < M) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    let old := Nat.floor ((M : ℝ) * x)
    let refined := Nat.floor (((2 : ℝ) * (M : ℝ) - 1) * x)
    refined ≤ 2 * old + 1 ∧ 2 * old ≤ refined + 2 := by
  let old := Nat.floor ((M : ℝ) * x)
  let refined := Nat.floor (((2 : ℝ) * (M : ℝ) - 1) * x)
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast hM
  have hMx_nonneg : 0 ≤ (M : ℝ) * x :=
    mul_nonneg hMpos.le hx0
  have hold_le : (old : ℝ) ≤ (M : ℝ) * x := by
    dsimp [old]
    exact Nat.floor_le hMx_nonneg
  have hMx_lt : (M : ℝ) * x < (old : ℝ) + 1 := by
    dsimp [old]
    exact Nat.lt_floor_add_one ((M : ℝ) * x)
  have href_lt :
      ((2 : ℝ) * (M : ℝ) - 1) * x < (refined : ℝ) + 1 := by
    dsimp [refined]
    exact Nat.lt_floor_add_one (((2 : ℝ) * (M : ℝ) - 1) * x)
  constructor
  · have hscale_le : ((2 : ℝ) * (M : ℝ) - 1) * x ≤
        ((2 : ℝ) * (M : ℝ)) * x := by
      nlinarith [hx0]
    have hscale_lt : ((2 : ℝ) * (M : ℝ) - 1) * x <
        ((2 * old + 2 : ℕ) : ℝ) := by
      norm_num [Nat.cast_add, Nat.cast_mul]
      nlinarith [hscale_le, hMx_lt]
    have hfloor_lt : refined < 2 * old + 2 := by
      have hn : 2 * old + 2 ≠ 0 := by omega
      exact (Nat.floor_lt' (a := ((2 : ℝ) * (M : ℝ) - 1) * x) hn).2
        (by simpa using hscale_lt)
    omega
  · have hscale_lower :
        ((2 : ℝ) * (M : ℝ)) * x ≤
          ((2 : ℝ) * (M : ℝ) - 1) * x + 1 := by
      nlinarith [hx1]
    have href_plus :
        ((2 : ℝ) * (M : ℝ) - 1) * x + 1 <
          (refined : ℝ) + 2 := by
      linarith
    have hreal : ((2 * old : ℕ) : ℝ) ≤ ((refined + 2 : ℕ) : ℝ) := by
      norm_num [Nat.cast_add, Nat.cast_mul]
      nlinarith [hold_le, hscale_lower, href_plus]
    have hnat : 2 * old ≤ refined + 2 := by
      exact_mod_cast hreal
    simpa [old, refined] using hnat

/--
Dyadic floor-window arithmetic for repeated `M ↦ 2*M - 1` refinements.  The
refined grid size `2^q*(M-1)+1` stays in a `2^q`-wide index window around
`2^q * floor(M*x)` for `x ∈ [0,1]`.
-/
theorem nat_floor_dyadic_pred_add_one_mul_window
    {M q : ℕ} (hM : 0 < M) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    let scale := 2 ^ q
    let old := Nat.floor ((M : ℝ) * x)
    let refined := Nat.floor (((scale * (M - 1) + 1 : ℕ) : ℝ) * x)
    refined ≤ scale * old + scale ∧
      scale * old ≤ refined + scale := by
  let scale : ℕ := 2 ^ q
  let old := Nat.floor ((M : ℝ) * x)
  let refined := Nat.floor (((scale * (M - 1) + 1 : ℕ) : ℝ) * x)
  have hscale_pos : 0 < scale := by
    dsimp [scale]
    positivity
  have hscale_nonneg_real : 0 ≤ (scale : ℝ) := by exact_mod_cast hscale_pos.le
  have hMx_nonneg : 0 ≤ (M : ℝ) * x :=
    mul_nonneg (by exact_mod_cast hM.le) hx0
  have hold_le : (old : ℝ) ≤ (M : ℝ) * x := by
    dsimp [old]
    exact Nat.floor_le hMx_nonneg
  have hMx_lt : (M : ℝ) * x < (old : ℝ) + 1 := by
    dsimp [old]
    exact Nat.lt_floor_add_one ((M : ℝ) * x)
  have href_lt :
      ((scale * (M - 1) + 1 : ℕ) : ℝ) * x < (refined : ℝ) + 1 := by
    dsimp [refined]
    exact Nat.lt_floor_add_one
      (((scale * (M - 1) + 1 : ℕ) : ℝ) * x)
  have hM_decomp : M = (M - 1) + 1 := by omega
  have hscaleM_decomp :
      scale * M = (scale * (M - 1) + 1) + (scale - 1) := by
    calc
      scale * M = scale * ((M - 1) + 1) :=
        congrArg (fun n : ℕ => scale * n) hM_decomp
      _ = scale * (M - 1) + scale := by
        rw [Nat.mul_add, Nat.mul_one]
      _ = (scale * (M - 1) + 1) + (scale - 1) := by
        omega
  have href_grid_le :
      scale * (M - 1) + 1 ≤ scale * M := by
    rw [hscaleM_decomp]
    omega
  constructor
  · have hscale_le :
        ((scale * (M - 1) + 1 : ℕ) : ℝ) * x ≤
          ((scale * M : ℕ) : ℝ) * x := by
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast href_grid_le) hx0
    have hscaleM_x_eq :
        ((scale * M : ℕ) : ℝ) * x = (scale : ℝ) * ((M : ℝ) * x) := by
      norm_num [Nat.cast_mul]
      ring
    have hscaled_Mx_lt :
        ((scale * M : ℕ) : ℝ) * x <
          (scale : ℝ) * ((old : ℝ) + 1) := by
      rw [hscaleM_x_eq]
      exact mul_lt_mul_of_pos_left hMx_lt (by exact_mod_cast hscale_pos)
    have hscale_le_norm :
        (((scale : ℝ) * ((M - 1 : ℕ) : ℝ) + 1) * x) ≤
          ((scale * M : ℕ) : ℝ) * x := by
      simpa [Nat.cast_add, Nat.cast_mul] using hscale_le
    have hscaled_Mx_lt_norm :
        ((scale * M : ℕ) : ℝ) * x <
          (scale : ℝ) * (old : ℝ) + (scale : ℝ) := by
      nlinarith [hscaled_Mx_lt]
    have hscale_lt :
        ((scale * (M - 1) + 1 : ℕ) : ℝ) * x <
          ((scale * old + scale + 1 : ℕ) : ℝ) := by
      norm_num [Nat.cast_add, Nat.cast_mul]
      nlinarith [hscale_le_norm, hscaled_Mx_lt_norm]
    have hfloor_lt : refined < scale * old + scale + 1 := by
      have hn : scale * old + scale + 1 ≠ 0 := by omega
      exact
        (Nat.floor_lt'
          (a := ((scale * (M - 1) + 1 : ℕ) : ℝ) * x) hn).2
          (by simpa using hscale_lt)
    have hle_local : refined ≤ scale * old + scale :=
      Nat.le_of_lt_succ (by
        simpa [Nat.succ_eq_add_one, add_assoc] using hfloor_lt)
    simpa [scale, old, refined] using hle_local
  · have hscaleM_decomp_real :
        ((scale * M : ℕ) : ℝ) =
          ((scale * (M - 1) + 1 : ℕ) : ℝ) +
            ((scale - 1 : ℕ) : ℝ) := by
      exact_mod_cast hscaleM_decomp
    have hscaleM_le :
        ((scale * M : ℕ) : ℝ) * x ≤
          ((scale * (M - 1) + 1 : ℕ) : ℝ) * x +
            ((scale - 1 : ℕ) : ℝ) := by
      calc
        ((scale * M : ℕ) : ℝ) * x =
            (((scale * (M - 1) + 1 : ℕ) : ℝ) +
              ((scale - 1 : ℕ) : ℝ)) * x := by
                rw [hscaleM_decomp_real]
        _ = ((scale * (M - 1) + 1 : ℕ) : ℝ) * x +
            ((scale - 1 : ℕ) : ℝ) * x := by ring
        _ ≤ ((scale * (M - 1) + 1 : ℕ) : ℝ) * x +
            ((scale - 1 : ℕ) : ℝ) := by
              have hsub_nonneg : 0 ≤ ((scale - 1 : ℕ) : ℝ) := by positivity
              have hmul :
                  ((scale - 1 : ℕ) : ℝ) * x ≤
                    ((scale - 1 : ℕ) : ℝ) * 1 :=
                mul_le_mul_of_nonneg_left hx1 hsub_nonneg
              nlinarith
    have hold_scaled :
        ((scale * old : ℕ) : ℝ) ≤ ((scale * M : ℕ) : ℝ) * x := by
      have hscaleM_x_eq :
          ((scale * M : ℕ) : ℝ) * x = (scale : ℝ) * ((M : ℝ) * x) := by
        norm_num [Nat.cast_mul]
        ring
      rw [hscaleM_x_eq]
      norm_num [Nat.cast_mul]
      exact mul_le_mul_of_nonneg_left hold_le hscale_nonneg_real
    have hscale_sub_add_cast :
        ((scale - 1 : ℕ) : ℝ) + 1 = (scale : ℝ) := by
      exact_mod_cast (Nat.sub_add_cancel hscale_pos)
    have hscaleM_le_norm :
        ((scale * M : ℕ) : ℝ) * x ≤
          (((scale : ℝ) * ((M - 1 : ℕ) : ℝ) + 1) * x) +
            ((scale - 1 : ℕ) : ℝ) := by
      simpa [Nat.cast_add, Nat.cast_mul] using hscaleM_le
    have href_lt_norm :
        (((scale : ℝ) * ((M - 1 : ℕ) : ℝ) + 1) * x) <
          (refined : ℝ) + 1 := by
      simpa [Nat.cast_add, Nat.cast_mul] using href_lt
    have hold_scaled_norm :
        (scale : ℝ) * (old : ℝ) ≤ ((scale * M : ℕ) : ℝ) * x := by
      simpa [Nat.cast_mul] using hold_scaled
    have hreal_norm :
        (scale : ℝ) * (old : ℝ) ≤ (refined : ℝ) + (scale : ℝ) := by
      nlinarith [hold_scaled_norm, hscaleM_le_norm, href_lt_norm,
        hscale_sub_add_cast]
    have hreal :
        ((scale * old : ℕ) : ℝ) ≤ ((refined + scale : ℕ) : ℝ) := by
      simpa [Nat.cast_add, Nat.cast_mul] using hreal_norm
    exact_mod_cast hreal

/--
Equispaced quantile grids converge uniformly to the identity on `[0,1]`.
This is the reusable floor-grid scaffold behind interval-quantile
convergence arguments.
-/
theorem tendstoUniformlyOn_nat_floor_mul_div_Icc_zero_one :
    TendstoUniformlyOn
      (fun Q : ℕ => fun x : ℝ =>
        (Nat.floor ((Q : ℝ) * x) : ℝ) / (Q : ℝ))
      (fun x : ℝ => x) atTop (Set.Icc (0 : ℝ) 1) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  rcases exists_nat_one_div_lt hε with ⟨m, hm⟩
  refine eventually_atTop.2 ⟨m + 1, ?_⟩
  intro Q hQ x hx
  have hQpos_nat : 0 < Q := Nat.succ_pos m |>.trans_le hQ
  have hQpos : 0 < (Q : ℝ) := by exact_mod_cast hQpos_nat
  have hmpos : 0 < ((m + 1 : ℕ) : ℝ) := by positivity
  have hrec :
      1 / (Q : ℝ) ≤ 1 / (((m + 1 : ℕ) : ℝ)) := by
    exact one_div_le_one_div_of_le hmpos (by exact_mod_cast hQ)
  have hclose :=
    nat_floor_mul_div_sub_abs_lt_inv (Q := Q) hQpos_nat (x := x) hx.1
  calc
    dist x ((Nat.floor ((Q : ℝ) * x) : ℝ) / (Q : ℝ))
        = |((Nat.floor ((Q : ℝ) * x) : ℝ) / (Q : ℝ)) - x| := by
          rw [Real.dist_eq, abs_sub_comm]
    _ < 1 / (Q : ℝ) := hclose
    _ ≤ 1 / (((m + 1 : ℕ) : ℝ)) := hrec
    _ < ε := by
          simpa [Nat.cast_add, Nat.cast_one] using hm

/-- If `g > 0`, then `floor (N * g)` diverges to infinity. -/
theorem tendsto_nat_floor_mul_const_atTop
    {g : ℝ} (hg_pos : 0 < g) :
    Tendsto (fun N : ℕ => Nat.floor ((N : ℝ) * g)) atTop atTop := by
  rw [tendsto_atTop]
  intro B
  have hratio :
      Tendsto
        (fun N : ℕ =>
          ((Nat.floor ((N : ℝ) * g) : ℝ) / (N : ℝ)))
        atTop (nhds g) :=
    tendsto_nat_floor_mul_const_div_nat hg_pos.le
  have hhalf_pos : 0 < g / 2 := by linarith
  have hratio_event :
      ∀ᶠ N : ℕ in atTop,
        g / 2 <
          ((Nat.floor ((N : ℝ) * g) : ℝ) / (N : ℝ)) :=
    hratio.eventually (Ioi_mem_nhds (show g / 2 < g by linarith))
  let K : ℕ := Nat.floor ((2 * (B : ℝ)) / g) + 1
  have hK_bound : (2 * (B : ℝ)) / g < (K : ℝ) := by
    dsimp [K]
    have hlt :
        (2 * (B : ℝ)) / g <
          (Nat.floor ((2 * (B : ℝ)) / g) : ℝ) + 1 :=
      Nat.lt_floor_add_one ((2 * (B : ℝ)) / g)
    simpa using hlt
  refine (hratio_event.and (Filter.eventually_ge_atTop K)).mono ?_
  intro N hN
  rcases hN with ⟨hratioN, hNK⟩
  have hN_pos : 0 < (N : ℝ) := by
    have hK_pos : 0 < K := Nat.succ_pos _
    exact_mod_cast lt_of_lt_of_le hK_pos hNK
  have hB_lt_half :
      (B : ℝ) < (N : ℝ) * (g / 2) := by
    have hK_le_N : (K : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNK
    calc
      (B : ℝ) < K * (g / 2) := by
        have hmul := mul_lt_mul_of_pos_right hK_bound hhalf_pos
        field_simp [ne_of_gt hg_pos] at hmul
        linarith
      _ ≤ (N : ℝ) * (g / 2) :=
        mul_le_mul_of_nonneg_right hK_le_N hhalf_pos.le
  have hfloor_gt :
      (B : ℝ) < (Nat.floor ((N : ℝ) * g) : ℝ) := by
    have hmul :
        (N : ℝ) * (g / 2) <
          (Nat.floor ((N : ℝ) * g) : ℝ) := by
      have hmul' :=
        mul_lt_mul_of_pos_right hratioN hN_pos
      field_simp [ne_of_gt hN_pos] at hmul'
      rw [mul_comm g (N : ℝ)] at hmul'
      linarith
    exact lt_trans hB_lt_half hmul
  exact_mod_cast le_of_lt hfloor_gt

/--
If a real-valued scale is eventually positive and tends to zero, then any
positive constant divided by that scale diverges to `atTop`.
-/
theorem tendsto_const_div_atTop_of_pos_tendsto_zero
    {ι : Type*} {l : Filter ι} {scale : ι → ℝ} {C : ℝ}
    (hC_pos : 0 < C)
    (hscale_zero : Tendsto scale l (nhds 0))
    (hscale_pos : ∀ᶠ i in l, 0 < scale i) :
    Tendsto (fun i => C / scale i) l atTop := by
  have hscale_nhdsGT :
      Tendsto scale l (𝓝[>] (0 : ℝ)) := by
    exact tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      scale hscale_zero hscale_pos
  have hinv : Tendsto (fun i => (scale i)⁻¹) l atTop :=
    hscale_nhdsGT.inv_tendsto_nhdsGT_zero
  simpa [div_eq_mul_inv] using
    (tendsto_const_mul_atTop_of_pos hC_pos).mpr hinv

/-- `log N` tends to infinity along natural numbers. -/
theorem tendsto_log_nat_atTop :
    Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

/-- A constant divided by `log N` tends to zero. -/
theorem tendsto_const_div_log_nat_nhds_zero (C : ℝ) :
    Tendsto (fun N : ℕ => C / Real.log (N : ℝ)) atTop (nhds 0) :=
  Filter.Tendsto.const_div_atTop tendsto_log_nat_atTop C

/-- `log N / sqrt N` tends to zero. -/
theorem tendsto_log_div_sqrt_nat_nhds_zero :
    Tendsto
      (fun N : ℕ => Real.log (N : ℝ) / Real.sqrt (N : ℝ))
      atTop (nhds 0) := by
  have hreal :
      Tendsto (fun x : ℝ => Real.log x / Real.sqrt x) atTop (nhds 0) := by
    simpa [Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_atTop (r := (1 / 2 : ℝ))
        (by norm_num)).tendsto_div_nhds_zero
  exact hreal.comp tendsto_natCast_atTop_atTop

/-- `log(N)^2 / sqrt(N)` tends to zero. -/
theorem tendsto_log_sq_div_sqrt_nat_nhds_zero :
    Tendsto
      (fun N : ℕ => (Real.log (N : ℝ)) ^ 2 / Real.sqrt (N : ℝ))
      atTop (nhds 0) := by
  have hreal :
      Tendsto (fun x : ℝ => (Real.log x) ^ 2 / Real.sqrt x)
        atTop (nhds 0) := by
    simpa [Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  exact hreal.comp tendsto_natCast_atTop_atTop

/-- A sequence tends to zero if it is eventually dominated by `C / √N`. -/
theorem TendsToZero_of_eventually_abs_le_inv_sqrt (ε : ℕ → ℝ) {C : ℝ}
    (_hC : 0 < C) (hbound : ∀ᶠ N in atTop, |ε N| ≤ C / Real.sqrt (N : ℝ)) :
    TendsToZero ε := by
  rw [TendsToZero]
  have h_sqrt_atTop :
      Tendsto (fun N : ℕ => Real.sqrt (N : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have h_zero : Tendsto (fun N : ℕ => C / Real.sqrt (N : ℝ)) atTop (nhds 0) :=
    Filter.Tendsto.const_div_atTop h_sqrt_atTop C
  have h_neg_zero : Tendsto (fun N : ℕ => -(C / Real.sqrt (N : ℝ))) atTop (nhds 0) := by
    have h := h_zero.neg
    rwa [neg_zero] at h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' h_neg_zero h_zero
  · filter_upwards [hbound, eventually_gt_atTop 0] with N hN hNpos
    rw [abs_le] at hN
    exact hN.1
  · filter_upwards [hbound, eventually_gt_atTop 0] with N hN hNpos
    rw [abs_le] at hN
    exact hN.2

/-- An exact geometric tail has logarithmic saturation ratio one. -/
theorem log_geometric_tail_ratio
    {C r : ℝ} (hC : 0 < C) (hr_pos : 0 < r) (hr_lt_one : r < 1) :
    Tendsto
      (fun N : ℕ =>
        Real.log (C * r ^ N) / (Real.log r * (N : ℝ)))
      atTop (nhds 1) := by
  have hlog_neg : Real.log r < 0 := Real.log_neg hr_pos hr_lt_one
  have hlog_ne : Real.log r ≠ 0 := ne_of_lt hlog_neg
  have hconst :
      Tendsto
        (fun N : ℕ => (Real.log C / Real.log r) / (N : ℝ))
        atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (Real.log C / Real.log r)
  have hlim :
      Tendsto
        (fun N : ℕ => 1 + (Real.log C / Real.log r) / (N : ℝ))
        atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add hconst
  refine Tendsto.congr' ?_ hlim
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hN_ne : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hrpow_ne : r ^ N ≠ 0 := pow_ne_zero N hr_pos.ne'
  symm
  calc
    Real.log (C * r ^ N) / (Real.log r * (N : ℝ))
        = (Real.log C + (N : ℝ) * Real.log r) /
            (Real.log r * (N : ℝ)) := by
          rw [Real.log_mul hC.ne' hrpow_ne, Real.log_pow]
    _ = 1 + (Real.log C / Real.log r) / (N : ℝ) := by
          field_simp [hlog_ne, hN_ne]
          ring

/-- `log N / N -> 0`. -/
theorem tendsto_log_nat_div_nat_nhds_zero :
    Tendsto
      (fun N : ℕ => Real.log (N : ℝ) / (N : ℝ))
      atTop (nhds 0) := by
  have hreal :
      Tendsto (fun x : ℝ => Real.log x / x) atTop (nhds 0) := by
    simpa using
      (isLittleO_log_rpow_atTop (r := (1 : ℝ)) (by norm_num)).tendsto_div_nhds_zero
  exact hreal.comp tendsto_natCast_atTop_atTop

/--
Any fixed real-power polynomial factor is killed by a geometric term along
natural-number indices.
-/
theorem rpow_mul_geometric_tendsto_zero
    (s : ℝ) {rho : ℝ} (hrho_pos : 0 < rho) (hrho_lt_one : rho < 1) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ s * rho ^ N)
      atTop (nhds 0) := by
  have hlog_neg : Real.log rho < 0 := Real.log_neg hrho_pos hrho_lt_one
  have hreal :
      Tendsto (fun x : ℝ => x ^ s * Real.exp (Real.log rho * x))
        atTop (nhds 0) := by
    simpa [neg_mul, neg_neg, mul_comm, mul_left_comm, mul_assoc] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
        s (-Real.log rho) (neg_pos.mpr hlog_neg)
  refine Tendsto.congr' ?_ (hreal.comp tendsto_natCast_atTop_atTop)
  filter_upwards with N
  have hexp :
      Real.exp (Real.log rho * (N : ℝ)) = rho ^ N := by
    calc
      Real.exp (Real.log rho * (N : ℝ))
          = Real.exp ((N : ℝ) * Real.log rho) := by rw [mul_comm]
      _ = (Real.exp (Real.log rho)) ^ N := Real.exp_nat_mul (Real.log rho) N
      _ = rho ^ N := by rw [Real.exp_log hrho_pos]
  change (N : ℝ) ^ s * Real.exp (Real.log rho * (N : ℝ)) =
    (N : ℝ) ^ s * rho ^ N
  rw [hexp]

/-- Natural square root tends to infinity along natural numbers. -/
theorem tendsto_nat_sqrt_atTop :
    Tendsto (fun N : ℕ => Nat.sqrt N) atTop atTop := by
  rw [tendsto_atTop]
  intro M
  refine eventually_atTop.2 ⟨M * M, ?_⟩
  intro N hN
  exact (Nat.le_sqrt).2 hN

/-- The real cast of `N + 1` tends to infinity along natural numbers. -/
theorem tendsto_nat_succ_cast_atTop :
    Tendsto (fun N : ℕ => (((N + 1 : ℕ) : ℝ))) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)

/-- Any fixed real constant divided by `N + 1` is eventually at most `1 / 2`. -/
theorem eventually_const_div_nat_succ_le_half (C : ℝ) :
    ∀ᶠ N : ℕ in atTop, C / (((N + 1 : ℕ) : ℝ)) ≤ 1 / 2 := by
  have hlim :
      Tendsto (fun N : ℕ => C / (((N + 1 : ℕ) : ℝ))) atTop (nhds 0) :=
    Filter.Tendsto.const_div_atTop tendsto_nat_succ_cast_atTop C
  have hnear :
      ∀ᶠ N : ℕ in atTop,
        C / (((N + 1 : ℕ) : ℝ)) ∈ Set.Iio (1 / 2 : ℝ) :=
    hlim (isOpen_Iio.mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [hnear] with N hN
  exact le_of_lt hN

/--
The elementary logarithmic endpoint rate `-log(1 - 1/(N+1))` tends to zero.
-/
theorem tendsto_neg_log_one_sub_inv_nat_succ_nhds_zero :
    Tendsto
      (fun N : ℕ => -Real.log (1 - 1 / (((N + 1 : ℕ) : ℝ))))
      atTop (nhds 0) := by
  have hinv :
      Tendsto (fun N : ℕ => (1 : ℝ) / (((N + 1 : ℕ) : ℝ)))
        atTop (nhds 0) :=
    Filter.Tendsto.const_div_atTop tendsto_nat_succ_cast_atTop (1 : ℝ)
  have harg :
      Tendsto (fun N : ℕ => 1 - (1 : ℝ) / (((N + 1 : ℕ) : ℝ)))
        atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub hinv
  have hlog :
      Tendsto
        (fun N : ℕ => Real.log (1 - (1 : ℝ) / (((N + 1 : ℕ) : ℝ))))
        atTop (nhds 0) := by
    simpa [Real.log_one] using
      (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp harg
  simpa using hlog.neg

/-- Adding a real constant to `(N + 1 : ℝ)` still tends to infinity. -/
theorem tendsto_nat_succ_cast_add_const_atTop (d : ℝ) :
    Tendsto (fun N : ℕ => (((N + 1 : ℕ) : ℝ) + d)) atTop atTop :=
  tendsto_atTop_add_const_right atTop d tendsto_nat_succ_cast_atTop

/-- A positive real power of `(N + 1 : ℝ)` tends to infinity. -/
theorem tendsto_nat_succ_cast_rpow_atTop {β : ℝ} (hβ_pos : 0 < β) :
    Tendsto (fun N : ℕ => (((N + 1 : ℕ) : ℝ) ^ β)) atTop atTop :=
  (tendsto_rpow_atTop hβ_pos).comp tendsto_nat_succ_cast_atTop

/-- A negative real power of `(N + 1 : ℝ)` tends to zero. -/
theorem tendsto_nat_succ_cast_rpow_neg_nhds_zero {β : ℝ}
    (hβ_pos : 0 < β) :
    Tendsto (fun N : ℕ => (((N + 1 : ℕ) : ℝ) ^ (-β)))
      atTop (nhds 0) :=
  (tendsto_rpow_neg_atTop hβ_pos).comp tendsto_nat_succ_cast_atTop

/--
Uniform negative-power bound gives eventual uniform smallness.  This is the
paper-neutral form of the common step from an `O(N^{-β})` estimate, uniform
over a family indexed by `α N`, to "smaller than any positive tolerance"
eventually.
-/
theorem eventually_forall_lt_of_uniform_rpow_neg_bound
    {α : ℕ → Type*} {f : ∀ N : ℕ, α N → ℝ}
    {A β : ℝ} {N0 : ℕ}
    (hβ_pos : 0 < β)
    (hbound :
      ∀ N : ℕ, N0 ≤ N →
        ∀ a : α N,
          f N a ≤ A * Real.rpow (((N + 1 : ℕ) : ℝ)) (-β)) :
    ∀ tol : ℝ, 0 < tol →
      ∀ᶠ N : ℕ in atTop, ∀ a : α N, f N a < tol := by
  intro tol htol
  have hupper_zero :
      Tendsto
        (fun N : ℕ => A * Real.rpow (((N + 1 : ℕ) : ℝ)) (-β))
        atTop (nhds 0) := by
    have hpow := tendsto_nat_succ_cast_rpow_neg_nhds_zero hβ_pos
    simpa using (tendsto_const_nhds.mul hpow : Tendsto
      (fun N : ℕ => A * Real.rpow (((N + 1 : ℕ) : ℝ)) (-β))
      atTop (nhds (A * 0)))
  have hsmall :
      ∀ᶠ N : ℕ in atTop,
        A * Real.rpow (((N + 1 : ℕ) : ℝ)) (-β) < tol :=
    hupper_zero (isOpen_Iio.mem_nhds htol)
  filter_upwards [eventually_ge_atTop N0, hsmall] with N hN hsmallN a
  exact lt_of_le_of_lt (hbound N hN a) hsmallN

/-- A negative real power of `(N + 1 : ℝ) + d` tends to zero. -/
theorem tendsto_nat_succ_cast_add_const_rpow_neg_nhds_zero
    (d : ℝ) {β : ℝ} (hβ_pos : 0 < β) :
    Tendsto (fun N : ℕ => ((((N + 1 : ℕ) : ℝ) + d) ^ (-β)))
      atTop (nhds 0) :=
  (tendsto_rpow_neg_atTop hβ_pos).comp
    (tendsto_nat_succ_cast_add_const_atTop d)

/-- The square root of `(N + 1 : ℝ)` tends to infinity. -/
theorem tendsto_sqrt_nat_succ_cast_atTop :
    Tendsto (fun N : ℕ => Real.sqrt (((N + 1 : ℕ) : ℝ))) atTop atTop :=
  Real.tendsto_sqrt_atTop.comp tendsto_nat_succ_cast_atTop

/-- Canonical inverse-square-root error schedule `1 / sqrt (N+1)`. -/
noncomputable def invSqrtSuccError (N : ℕ) : ℝ :=
  1 / Real.sqrt (((N + 1 : ℕ) : ℝ))

theorem invSqrtSuccError_nonneg (N : ℕ) :
    0 ≤ invSqrtSuccError N := by
  unfold invSqrtSuccError
  positivity

theorem invSqrtSuccError_tendsToZero :
    TendsToZero invSqrtSuccError := by
  rw [TendsToZero]
  refine Tendsto.congr' ?_
    (Filter.Tendsto.const_div_atTop tendsto_sqrt_nat_succ_cast_atTop (1 : ℝ))
  filter_upwards with N
  simp [invSqrtSuccError, one_div, Nat.cast_add]

/-- `N / sqrt (N+1)`, equivalently `invSqrtSuccError N * N`, tends to infinity. -/
theorem invSqrtSuccError_mul_nat_tendsto_atTop :
    Tendsto (fun N : ℕ => invSqrtSuccError N * (N : ℝ)) atTop atTop := by
  have hhalf_sqrt :
      Tendsto
        (fun N : ℕ => (1 / 2 : ℝ) * Real.sqrt (((N + 1 : ℕ) : ℝ)))
        atTop atTop :=
    Filter.Tendsto.const_mul_atTop
      (by norm_num : (0 : ℝ) < 1 / 2) tendsto_sqrt_nat_succ_cast_atTop
  refine tendsto_atTop_mono' atTop ?_ hhalf_sqrt
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN_real : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hbase_pos : 0 < (((N + 1 : ℕ) : ℝ)) := by positivity
  have hsqrt_pos : 0 < Real.sqrt (((N + 1 : ℕ) : ℝ)) :=
    Real.sqrt_pos.mpr hbase_pos
  have hbase_div_le_N :
      (((N + 1 : ℕ) : ℝ)) / 2 ≤ (N : ℝ) := by
    have hbase_eq : (((N + 1 : ℕ) : ℝ)) = (N : ℝ) + 1 := by norm_num
    nlinarith
  unfold invSqrtSuccError
  calc
    (1 / 2 : ℝ) * Real.sqrt (((N + 1 : ℕ) : ℝ))
        =
          (((N + 1 : ℕ) : ℝ)) /
            (2 * Real.sqrt (((N + 1 : ℕ) : ℝ))) := by
          field_simp [hsqrt_pos.ne']
          rw [Real.sq_sqrt hbase_pos.le]
    _ ≤ (N : ℝ) / Real.sqrt (((N + 1 : ℕ) : ℝ)) := by
          rw [div_le_div_iff₀ (by positivity : 0 < 2 * Real.sqrt (((N + 1 : ℕ) : ℝ)))
            hsqrt_pos]
          nlinarith
    _ = (1 / Real.sqrt (((N + 1 : ℕ) : ℝ))) * (N : ℝ) := by ring

/--
The growing scale `N / sqrt(N+1)` eventually dominates every fixed finite
family of real bounds.
-/
theorem invSqrtSuccError_mul_nat_eventually_gt_fintype_pair
    {ι κ : Type*} [Fintype ι] [Fintype κ] (B : ι → κ → ℝ) :
    ∀ᶠ N in atTop,
      ∀ i : ι, ∀ j : κ,
        B i j < invSqrtSuccError N * (N : ℝ) := by
  classical
  refine eventually_all.2 ?_
  intro i
  refine eventually_all.2 ?_
  intro j
  exact invSqrtSuccError_mul_nat_tendsto_atTop.eventually_gt_atTop (B i j)

/--
If a scaled-count gap beats the source and destination additive shifts, then
the corresponding shifted destination count is below the shifted source count.

This is the arithmetic core used by finite FOC arguments that compare
backward and forward marginals with one-count or constant shifts.
-/
theorem scaled_gap_absorbs_additive_shifts
    {qsrc qdst wsrc wdst srcShift dstShift : ℝ}
    (hshift_lt_gap :
      srcShift / wsrc + dstShift / wdst <
        qsrc / wsrc - qdst / wdst) :
    (qdst + dstShift) / wdst < (qsrc - srcShift) / wsrc := by
  have hdst :
      (qdst + dstShift) / wdst =
        qdst / wdst + dstShift / wdst := by ring
  have hsrc :
      (qsrc - srcShift) / wsrc =
        qsrc / wsrc - srcShift / wsrc := by ring
  rw [hdst, hsrc]
  linarith

/-- The integer square-root gap `(sqrt N + 1) / N` tends to zero. -/
theorem nat_sqrt_gap_error_tendsToZero :
    TendsToZero
      (fun N : ℕ => ((Nat.sqrt N + 1 : ℕ) : ℝ) / (N : ℝ)) := by
  refine TendsToZero_of_eventually_abs_le_inv_sqrt
    (fun N : ℕ => ((Nat.sqrt N + 1 : ℕ) : ℝ) / (N : ℝ))
    (by norm_num : (0 : ℝ) < 2) ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN_pos : 0 < (N : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mp hN)
  have hN_nonneg : 0 ≤ (N : ℝ) := hN_pos.le
  have hsqrt_pos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hN_pos
  have hsqrt_ge_one : 1 ≤ Real.sqrt (N : ℝ) := by
    rw [Real.one_le_sqrt]
    exact_mod_cast hN
  have hnat_sqrt_le : (Nat.sqrt N : ℝ) ≤ Real.sqrt (N : ℝ) :=
    Real.nat_sqrt_le_real_sqrt
  have hnum_le :
      ((Nat.sqrt N + 1 : ℕ) : ℝ) ≤ 2 * Real.sqrt (N : ℝ) := by
    norm_num
    linarith
  have hval_nonneg :
      0 ≤ ((Nat.sqrt N + 1 : ℕ) : ℝ) / (N : ℝ) := by
    positivity
  rw [abs_of_nonneg hval_nonneg]
  calc
    ((Nat.sqrt N + 1 : ℕ) : ℝ) / (N : ℝ)
        ≤ (2 * Real.sqrt (N : ℝ)) / (N : ℝ) :=
          div_le_div_of_nonneg_right hnum_le hN_nonneg
    _ = 2 / Real.sqrt (N : ℝ) := by
          field_simp [hsqrt_pos.ne']
          rw [Real.sq_sqrt hN_nonneg]

/--
For any `0 < rho < 1`, a square-root gap kills every fixed polynomial factor:
`N^k * rho^(sqrt N) -> 0`.
-/
theorem nat_sqrt_gap_polynomial_geometric_tends_to_zero
    (k : ℕ) {rho : ℝ} (hrho_pos : 0 < rho) (hrho_lt_one : rho < 1) :
    Tendsto
      (fun N : ℕ => (N : ℝ) ^ k * rho ^ (Nat.sqrt N))
      atTop (nhds 0) := by
  have hsucc_base :
      Tendsto
        (fun m : ℕ => (((m + 1 : ℕ) : ℝ) ^ (2 * k)) * rho ^ (m + 1))
        atTop (nhds 0) :=
          (tendsto_pow_const_mul_const_pow_of_lt_one (2 * k)
        hrho_pos.le hrho_lt_one).comp (tendsto_add_atTop_nat 1)
  have hsucc :
      Tendsto
        (fun m : ℕ => (((m + 1 : ℕ) : ℝ) ^ (2 * k)) * rho ^ m)
        atTop (nhds 0) := by
    have hmul :=
      hsucc_base.const_mul rho⁻¹
    refine Tendsto.congr' ?_ (by simpa using hmul)
    filter_upwards with m
    have hpow : rho ^ (m + 1) = rho ^ m * rho := by
      rw [pow_succ]
    rw [hpow]
    field_simp [hrho_pos.ne']
    ring_nf
    norm_num [Nat.cast_add, add_comm, mul_comm]
  have hupper_lim :
      Tendsto
        (fun N : ℕ =>
          (((Nat.sqrt N + 1 : ℕ) : ℝ) ^ (2 * k)) *
            rho ^ (Nat.sqrt N))
        atTop (nhds 0) :=
    hsucc.comp tendsto_nat_sqrt_atTop
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hupper_lim ?_ ?_
  · filter_upwards with N
    positivity
  · filter_upwards with N
    let m : ℕ := Nat.sqrt N
    have hN_le_nat : N ≤ (m + 1) ^ 2 :=
      le_of_lt (by simpa [m] using Nat.lt_succ_sqrt' N)
    have hN_le_real : (N : ℝ) ≤ ((m + 1 : ℕ) : ℝ) ^ 2 := by
      exact_mod_cast hN_le_nat
    have hpow_le :
        (N : ℝ) ^ k ≤ (((m + 1 : ℕ) : ℝ) ^ 2) ^ k :=
      pow_le_pow_left₀ (by positivity) hN_le_real k
    have hpow_eq :
        (((m + 1 : ℕ) : ℝ) ^ 2) ^ k =
          ((m + 1 : ℕ) : ℝ) ^ (2 * k) := by
      rw [pow_mul]
    have hpow_le' :
        (N : ℝ) ^ k ≤ ((m + 1 : ℕ) : ℝ) ^ (2 * k) := by
      calc
        (N : ℝ) ^ k ≤ (((m + 1 : ℕ) : ℝ) ^ 2) ^ k := hpow_le
        _ = ((m + 1 : ℕ) : ℝ) ^ (2 * k) := hpow_eq
    have htail_nonneg : 0 ≤ rho ^ m := pow_nonneg hrho_pos.le m
    calc
      (N : ℝ) ^ k * rho ^ (Nat.sqrt N)
          = (N : ℝ) ^ k * rho ^ m := by rfl
      _ ≤ (((m + 1 : ℕ) : ℝ) ^ (2 * k)) * rho ^ m :=
            mul_le_mul_of_nonneg_right
              hpow_le' htail_nonneg
      _ = (((Nat.sqrt N + 1 : ℕ) : ℝ) ^ (2 * k)) *
            rho ^ (Nat.sqrt N) := by rfl

/--
Multiplying a geometric tail by any fixed polynomial factor does not change the
logarithmic saturation ratio.
-/
theorem log_polynomial_geometric_tail_ratio
    {C r : ℝ} (d : ℕ)
    (hC : 0 < C) (hr_pos : 0 < r) (hr_lt_one : r < 1) :
    Tendsto
      (fun N : ℕ =>
        Real.log (C * (N : ℝ) ^ d * r ^ N) /
          (Real.log r * (N : ℝ)))
      atTop (nhds 1) := by
  have hlog_neg : Real.log r < 0 := Real.log_neg hr_pos hr_lt_one
  have hlog_ne : Real.log r ≠ 0 := ne_of_lt hlog_neg
  have hconst :
      Tendsto
        (fun N : ℕ => (Real.log C / Real.log r) / (N : ℝ))
        atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (Real.log C / Real.log r)
  have hlog_over_N :
      Tendsto
        (fun N : ℕ =>
          ((d : ℝ) / Real.log r) *
            (Real.log (N : ℝ) / (N : ℝ)))
        atTop (nhds 0) := by
    simpa using tendsto_log_nat_div_nat_nhds_zero.const_mul
      ((d : ℝ) / Real.log r)
  have hlim :
      Tendsto
        (fun N : ℕ =>
          1 + (Real.log C / Real.log r) / (N : ℝ) +
            ((d : ℝ) / Real.log r) *
              (Real.log (N : ℝ) / (N : ℝ)))
        atTop (nhds 1) := by
    have hfirst :
        Tendsto
          (fun N : ℕ => 1 + (Real.log C / Real.log r) / (N : ℝ))
          atTop (nhds 1) := by
      simpa using tendsto_const_nhds.add hconst
    simpa using hfirst.add hlog_over_N
  refine Tendsto.congr' ?_ hlim
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hN_pos : 0 < (N : ℝ) := by exact_mod_cast hN
  have hN_ne : (N : ℝ) ≠ 0 := ne_of_gt hN_pos
  have hNpow_ne : (N : ℝ) ^ d ≠ 0 := pow_ne_zero d hN_ne
  have hrpow_ne : r ^ N ≠ 0 := pow_ne_zero N hr_pos.ne'
  symm
  calc
    Real.log (C * (N : ℝ) ^ d * r ^ N) /
          (Real.log r * (N : ℝ))
        =
        (Real.log C + (d : ℝ) * Real.log (N : ℝ) +
            (N : ℝ) * Real.log r) /
          (Real.log r * (N : ℝ)) := by
          rw [Real.log_mul (mul_ne_zero hC.ne' hNpow_ne) hrpow_ne,
            Real.log_mul hC.ne' hNpow_ne, Real.log_pow, Real.log_pow]
    _ = 1 + (Real.log C / Real.log r) / (N : ℝ) +
          ((d : ℝ) / Real.log r) *
            (Real.log (N : ℝ) / (N : ℝ)) := by
          field_simp [hlog_ne, hN_ne]
          ring

/--
Lower geometric and upper polynomial-times-geometric bounds squeeze the
logarithmic saturation ratio to one.
-/
theorem log_tail_ratio_of_geometric_bounds
    {gap : ℕ → ℝ} {lower upper r : ℝ} (d : ℕ)
    (hlower_pos : 0 < lower) (hupper_pos : 0 < upper)
    (hr_pos : 0 < r) (hr_lt_one : r < 1)
    (hlower :
      ∀ᶠ N in atTop, lower * r ^ N ≤ gap N)
    (hupper :
      ∀ᶠ N in atTop, gap N ≤ upper * (N : ℝ) ^ d * r ^ N) :
    Tendsto
      (fun N : ℕ =>
        Real.log (gap N) / (Real.log r * (N : ℝ)))
      atTop (nhds 1) := by
  have hlog_neg : Real.log r < 0 := Real.log_neg hr_pos hr_lt_one
  have hlow_lim :=
    log_polynomial_geometric_tail_ratio
      d hupper_pos hr_pos hr_lt_one
  have hup_lim :=
    log_geometric_tail_ratio
      hlower_pos hr_pos hr_lt_one
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow_lim hup_lim ?_ ?_
  · filter_upwards [hlower, hupper, eventually_gt_atTop 0] with N hlowerN hupperN hN
    have hN_pos : 0 < (N : ℝ) := by exact_mod_cast hN
    have hden_neg : Real.log r * (N : ℝ) < 0 :=
      mul_neg_of_neg_of_pos hlog_neg hN_pos
    have hlower_tail_pos : 0 < lower * r ^ N :=
      mul_pos hlower_pos (pow_pos hr_pos N)
    have hgap_pos : 0 < gap N := lt_of_lt_of_le hlower_tail_pos hlowerN
    have hupper_tail_pos : 0 < upper * (N : ℝ) ^ d * r ^ N := by
      positivity
    have hlog_le :
        Real.log (gap N) ≤
          Real.log (upper * (N : ℝ) ^ d * r ^ N) :=
      Real.log_le_log hgap_pos hupperN
    exact (div_le_div_right_of_neg hden_neg).2 hlog_le
  · filter_upwards [hlower, hupper, eventually_gt_atTop 0] with N hlowerN hupperN hN
    have hN_pos : 0 < (N : ℝ) := by exact_mod_cast hN
    have hden_neg : Real.log r * (N : ℝ) < 0 :=
      mul_neg_of_neg_of_pos hlog_neg hN_pos
    have hlower_tail_pos : 0 < lower * r ^ N :=
      mul_pos hlower_pos (pow_pos hr_pos N)
    have hgap_pos : 0 < gap N := lt_of_lt_of_le hlower_tail_pos hlowerN
    have hlog_le :
        Real.log (lower * r ^ N) ≤ Real.log (gap N) :=
      Real.log_le_log hlower_tail_pos hlowerN
    exact (div_le_div_right_of_neg hden_neg).2 hlog_le

/--
If a nonnegative sequence is bounded by a constant, then dividing it by `N`
tends to zero.
-/
theorem TendsToZero_ratio_of_nonneg_bounded (x : ℕ → ℝ) {C : ℝ}
    (hC : 0 < C) (hx_nonneg : ∀ N, 0 ≤ x N) (hx_bound : ∀ N, x N ≤ C) :
    TendsToZero fun N => x N / (N : ℝ) := by
  refine TendsToZero_of_eventually_abs_le_inv (fun N => x N / (N : ℝ)) hC ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hNreal_pos : 0 < (N : ℝ) := by exact_mod_cast hN
  have hdiv_nonneg : 0 ≤ x N / (N : ℝ) :=
    div_nonneg (hx_nonneg N) hNreal_pos.le
  rw [abs_of_nonneg hdiv_nonneg]
  exact div_le_div_of_nonneg_right (hx_bound N) hNreal_pos.le

/-- Rounding a nonnegative real upward on the reciprocal successor grid
converges back to that real. -/
theorem tendsto_nat_ceil_mul_succ_cast_div
    {a : ℝ} (ha : 0 ≤ a) :
    Tendsto (fun N : ℕ =>
      ((Nat.ceil (a * ((N + 1 : ℕ) : ℝ)) : ℝ) / ((N + 1 : ℕ) : ℝ)))
      atTop (nhds a) := by
  simpa using
    (tendsto_nat_ceil_mul_div_atTop ha).comp tendsto_nat_succ_cast_atTop

/--
Order is closed under limits of real sequences: if `x N <= y N` for every
index and the two sequences converge, then the limiting values satisfy the same
inequality.
-/
theorem le_of_tendsto_atTop_of_forall_le
    {x y : ℕ → ℝ} {X Y : ℝ}
    (hx : Tendsto x atTop (nhds X))
    (hy : Tendsto y atTop (nhds Y))
    (hle : ∀ N, x N ≤ y N) :
    X ≤ Y :=
  le_of_tendsto_of_tendsto' hx hy hle

end Math
end AppliedModelingLib
