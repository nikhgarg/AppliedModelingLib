import PRPKG24AccuracyDiversity.MainTheorems

/-!
# Corrected generic Appendix D.1(i)

This module is reserved for a direct proof of the corrected generic
Lemma D.1(i).  It deliberately works from the raw finite integer allocation
problem and the displayed logarithmic tail hypothesis; it does not route
through a limiting-objective or optimizer-convergence certificate.

The source statement needs explicit positive weights, monotonicity, a
negative logarithmic-tail coefficient, a positive power, and eventual
positivity of `A - h`.  The first construction below is the literal balanced
integer competitor used in the source contradiction argument.
-/

open Filter Topology
open scoped BigOperators

namespace PRPKG24AccuracyDiversity
namespace AppendixD1GenericI

open AppliedModelingLib

/-- The positive gap to the finite saturation value in corrected D.1(i). -/
def saturationGap (A : ℝ) (h : ℕ → ℝ) (a : ℕ) : ℝ := A - h a

/-- Monotonicity of `h` makes the saturation gap antitone. -/
theorem saturationGap_antitone_of_monotone
    {A : ℝ} {h : ℕ → ℝ} (hmono : Monotone h) :
    Antitone (saturationGap A h) := by
  intro a b hab
  dsimp [saturationGap]
  linarith [hmono hab]

/--
The source proof needs the saturation gap to be positive at every finite
count. Eventual positivity plus monotonicity supplies that missing fact.
-/
theorem saturationGap_pos_of_monotone_of_eventually_pos
    {A : ℝ} {h : ℕ → ℝ} (hmono : Monotone h)
    (heventual : ∀ᶠ a in atTop, 0 < saturationGap A h a) :
    ∀ a : ℕ, 0 < saturationGap A h a := by
  obtain ⟨K, hK⟩ := eventually_atTop.1 heventual
  intro a
  by_cases ha : K ≤ a
  · exact hK a ha
  · have haK : a < K := Nat.lt_of_not_ge ha
    have hle := hmono (Nat.le_of_lt haK)
    have hKpos := hK K le_rfl
    dsimp [saturationGap] at hle hKpos ⊢
    linarith

/--
The corrected raw logarithmic-tail condition supplies two-sided exponential
bounds, with an arbitrarily small relative slack.  This is the analytic
inequality used directly in the source optimizer comparison.
-/
theorem eventually_log_saturationGap_bounds
    {A B sigma : ℝ} {h : ℕ → ℝ}
    (hB_neg : B < 0) (hsigma_pos : 0 < sigma)
    (hlog :
      Tendsto
        (fun a : ℕ =>
          Real.log (saturationGap A h a) /
            (B * (a : ℝ) ^ sigma))
        atTop (nhds 1))
    {delta : ℝ} (hdelta_pos : 0 < delta) :
    ∀ᶠ a : ℕ in atTop,
      (1 + delta) * (B * (a : ℝ) ^ sigma) <
          Real.log (saturationGap A h a) ∧
        Real.log (saturationGap A h a) <
          (1 - delta) * (B * (a : ℝ) ^ sigma) := by
  have hnear : Set.Ioo (1 - delta) (1 + delta) ∈ nhds (1 : ℝ) :=
    Ioo_mem_nhds (by linarith) (by linarith)
  filter_upwards [hlog.eventually hnear, eventually_gt_atTop 0] with
    a hratio ha_pos
  have ha_real_pos : 0 < (a : ℝ) := by exact_mod_cast ha_pos
  have hpow_pos : 0 < (a : ℝ) ^ sigma :=
    Real.rpow_pos_of_pos ha_real_pos sigma
  have hden_neg : B * (a : ℝ) ^ sigma < 0 :=
    mul_neg_of_neg_of_pos hB_neg hpow_pos
  have hden_ne : B * (a : ℝ) ^ sigma ≠ 0 := ne_of_lt hden_neg
  have hB_ne : B ≠ 0 := ne_of_lt hB_neg
  have hratio_mul :
      (Real.log (saturationGap A h a) /
          (B * (a : ℝ) ^ sigma)) *
          (B * (a : ℝ) ^ sigma) =
        Real.log (saturationGap A h a) := by
    field_simp [hden_ne, hB_ne]
  have hlow := mul_lt_mul_of_neg_right hratio.2 hden_neg
  have hhigh := mul_lt_mul_of_neg_right hratio.1 hden_neg
  rw [hratio_mul] at hlow hhigh
  exact ⟨hlow, hhigh⟩

/--
The corrected logarithmic tail approaches zero.  This is derived from the
displayed limit itself, rather than supplied as a tail or optimizer
certificate.
-/
theorem tendsto_saturationGap_nhds_zero_of_log_tail
    {A B sigma : ℝ} {h : ℕ → ℝ}
    (hB_neg : B < 0) (hsigma_pos : 0 < sigma)
    (hgap_pos : ∀ᶠ a : ℕ in atTop, 0 < saturationGap A h a)
    (hlog :
      Tendsto
        (fun a : ℕ =>
          Real.log (saturationGap A h a) /
            (B * (a : ℝ) ^ sigma))
        atTop (nhds 1)) :
    Tendsto (saturationGap A h) atTop (nhds 0) := by
  have hpow :
      Tendsto (fun a : ℕ => (a : ℝ) ^ sigma) atTop atTop :=
    (tendsto_rpow_atTop hsigma_pos).comp tendsto_natCast_atTop_atTop
  have hden :
      Tendsto (fun a : ℕ => B * (a : ℝ) ^ sigma) atTop atBot :=
    hpow.const_mul_atTop_of_neg hB_neg
  have harg :
      Tendsto
        (fun a : ℕ =>
          (Real.log (saturationGap A h a) /
            (B * (a : ℝ) ^ sigma)) *
            (B * (a : ℝ) ^ sigma))
        atTop atBot :=
    hlog.pos_mul_atBot (by norm_num) hden
  have hlog_gap :
      Tendsto (fun a : ℕ => Real.log (saturationGap A h a)) atTop atBot := by
    refine harg.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with a ha_pos
    have ha_real_pos : 0 < (a : ℝ) := by exact_mod_cast ha_pos
    have hpow_pos : 0 < (a : ℝ) ^ sigma :=
      Real.rpow_pos_of_pos ha_real_pos sigma
    have hden_ne : B * (a : ℝ) ^ sigma ≠ 0 := by
      exact mul_ne_zero (ne_of_lt hB_neg) (ne_of_gt hpow_pos)
    field_simp [hden_ne, ne_of_lt hB_neg]
  have hexp :
      Tendsto (fun a : ℕ => Real.exp (Real.log (saturationGap A h a)))
        atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp hlog_gap
  refine hexp.congr' ?_
  filter_upwards [hgap_pos] with a ha_pos
  exact Real.exp_log ha_pos

/-- Canonical balanced allocation of `N` units across the source's `m` types. -/
def balancedAllocation (m N : ℕ) : CountAllocation m where
  count := fun i => N / m + if i.1 < N % m then 1 else 0

@[simp] theorem balancedAllocation_count (m N : ℕ) (i : ItemType m) :
    (balancedAllocation m N).count i =
      N / m + if i.1 < N % m then 1 else 0 := rfl

/-- The canonical balanced competitor has exactly the advertised total. -/
theorem balancedAllocation_feasible {m : ℕ} [NeZero m] (N : ℕ) :
    ConsumptionModel.FeasibleAtTotal N (balancedAllocation m N) := by
  classical
  change (∑ i : Fin m, (N / m + if i.val < N % m then 1 else 0)) = N
  have hrem_lt : N % m < m := Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne m))
  have hite :
      (∑ i : Fin m, if i.val < N % m then 1 else 0) = N % m := by
    rw [Finset.sum_ite]
    simp [Fin.card_filter_val_lt, Nat.min_eq_right (Nat.le_of_lt hrem_lt)]
  calc
    (∑ i : Fin m, (N / m + if i.val < N % m then 1 else 0))
        = (∑ _i : Fin m, N / m) +
            ∑ i : Fin m, if i.val < N % m then 1 else 0 :=
          Finset.sum_add_distrib
    _ = m * (N / m) + N % m := by
          rw [show (∑ _i : Fin m, N / m) = m * (N / m) by simp]
          exact congrArg (fun x => m * (N / m) + x) hite
    _ = N := Nat.div_add_mod N m

/-- Every balanced coordinate is at least the integer average. -/
theorem div_le_balancedAllocation_count (m N : ℕ) (i : ItemType m) :
    N / m ≤ (balancedAllocation m N).count i := by
  simp [balancedAllocation]

/-- Every balanced coordinate is at most one above the integer average. -/
theorem balancedAllocation_count_le_div_add_one (m N : ℕ) (i : ItemType m) :
    (balancedAllocation m N).count i ≤ N / m + 1 := by
  simp [balancedAllocation]
  split_ifs <;> omega

/-- The integer average of a growing total diverges for a fixed nonzero type count. -/
theorem tendsto_nat_div_typeCount_atTop {m : ℕ} [NeZero m] :
    Tendsto (fun N : ℕ => N / m) atTop atTop :=
  Nat.tendsto_div_const_atTop (NeZero.ne m)

/-- Each balanced-coordinate count diverges with the total. -/
theorem tendsto_balancedAllocation_count_atTop
    {m : ℕ} [NeZero m] (i : ItemType m) :
    Tendsto (fun N : ℕ => (balancedAllocation m N).count i) atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_ (tendsto_nat_div_typeCount_atTop (m := m))
  filter_upwards with N
  exact div_le_balancedAllocation_count m N i

/--
The total weighted saturation gap of the literal balanced competitor tends to
zero under the raw corrected logarithmic tail.
-/
theorem tendsto_balanced_weighted_saturationGap_sum_nhds_zero
    {m : ℕ} [NeZero m] {A B sigma : ℝ} {h : ℕ → ℝ}
    (p : ItemType m → ℝ)
    (hB_neg : B < 0) (hsigma_pos : 0 < sigma)
    (hgap_pos : ∀ᶠ a : ℕ in atTop, 0 < saturationGap A h a)
    (hlog :
      Tendsto
        (fun a : ℕ =>
          Real.log (saturationGap A h a) /
            (B * (a : ℝ) ^ sigma))
        atTop (nhds 1)) :
    Tendsto
      (fun N : ℕ =>
        ∑ i : ItemType m,
          p i * saturationGap A h ((balancedAllocation m N).count i))
      atTop (nhds 0) := by
  have hgap_zero :
      Tendsto (saturationGap A h) atTop (nhds 0) :=
    tendsto_saturationGap_nhds_zero_of_log_tail
      hB_neg hsigma_pos hgap_pos hlog
  have hsum :
      Tendsto
        (fun N : ℕ =>
          ∑ i : ItemType m,
            p i * saturationGap A h ((balancedAllocation m N).count i))
        atTop (nhds (∑ _i : ItemType m, (0 : ℝ))) := by
    exact tendsto_finset_sum Finset.univ (fun i _ => by
      simpa using
        (tendsto_const_nhds (x := p i)).mul
          (hgap_zero.comp (tendsto_balancedAllocation_count_atTop (m := m) i)))
  simpa using hsum

/--
Optimality for the literal separable objective is equivalently a reverse
comparison of weighted saturation gaps against the literal balanced
competitor.  No normalized objective is introduced.
-/
theorem weighted_saturationGap_sum_le_balanced_of_optimal
    {m : ℕ} [NeZero m] {A : ℝ} {h : ℕ → ℝ}
    (p : ItemType m → ℝ)
    (seq : AppliedModelingLib.Allocation.OptimalSequence
      (fun _ : ℕ => p) (fun _ : ℕ => fun _ : ItemType m => h)) (N : ℕ) :
    (∑ i : ItemType m,
      p i * saturationGap A h ((seq.allocation N).count i)) ≤
      ∑ i : ItemType m,
        p i * saturationGap A h ((balancedAllocation m N).count i) := by
  have hopt := (seq.optimal N).2 (balancedAllocation m N)
    (balancedAllocation_feasible (m := m) N)
  have hgap_eq (a : CountAllocation m) :
      (∑ i : ItemType m, p i * saturationGap A h (a.count i)) =
        (∑ i : ItemType m, p i * A) -
          AppliedModelingLib.Allocation.objective a p (fun _ : ItemType m => h) := by
    calc
      (∑ i : ItemType m, p i * saturationGap A h (a.count i))
          = ∑ i : ItemType m, (p i * A - p i * h (a.count i)) := by
              refine Finset.sum_congr rfl ?_
              intro i _hi
              simp only [saturationGap]
              ring
      _ = (∑ i : ItemType m, p i * A) -
          AppliedModelingLib.Allocation.objective a p (fun _ : ItemType m => h) := by
              rw [Finset.sum_sub_distrib]
              rfl
  rw [hgap_eq (seq.allocation N), hgap_eq (balancedAllocation m N)]
  linarith

/--
Every coordinate of a literal optimal allocation diverges.  This is the
interiority step used by the source proof, derived by comparing its raw gap
objective to the balanced integer competitor.
-/
theorem tendsto_optimalAllocation_count_atTop_of_log_tail
    {m : ℕ} [NeZero m] {A B sigma : ℝ} {h : ℕ → ℝ}
    (p : ItemType m → ℝ)
    (seq : AppliedModelingLib.Allocation.OptimalSequence
      (fun _ : ℕ => p) (fun _ : ℕ => fun _ : ItemType m => h))
    (hp_pos : ∀ i : ItemType m, 0 < p i)
    (hmono : Monotone h)
    (hB_neg : B < 0) (hsigma_pos : 0 < sigma)
    (hgap_eventual_pos : ∀ᶠ a : ℕ in atTop, 0 < saturationGap A h a)
    (hlog :
      Tendsto
        (fun a : ℕ =>
          Real.log (saturationGap A h a) /
            (B * (a : ℝ) ^ sigma))
        atTop (nhds 1))
    (t : ItemType m) :
    Tendsto (fun N : ℕ => (seq.allocation N).count t) atTop atTop := by
  have hgap_pos : ∀ a : ℕ, 0 < saturationGap A h a :=
    saturationGap_pos_of_monotone_of_eventually_pos hmono hgap_eventual_pos
  have hgap_antitone : Antitone (saturationGap A h) :=
    saturationGap_antitone_of_monotone hmono
  have hbalanced_zero :=
    tendsto_balanced_weighted_saturationGap_sum_nhds_zero
      p hB_neg hsigma_pos hgap_eventual_pos hlog
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
    weighted_saturationGap_sum_le_balanced_of_optimal (A := A) p seq N
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
The integer average is eventually above every strictly smaller real fraction
of the total.  This keeps the floor error explicit in the raw finite problem.
-/
theorem eventually_mul_lt_nat_div
    {m : ℕ} [NeZero m] {c : ℝ}
    (hc : c < 1 / (m : ℝ)) :
    ∀ᶠ N : ℕ in atTop, c * (N : ℝ) < (N / m : ℕ) := by
  have hm_nat : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hm : 0 < (m : ℝ) := by exact_mod_cast hm_nat
  have hd_pos : 0 < 1 / (m : ℝ) - c := sub_pos.mpr hc
  have hlinear :
      Tendsto (fun N : ℕ => (1 / (m : ℝ) - c) * (N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hd_pos
  have hlarge :
      ∀ᶠ N : ℕ in atTop, 1 ≤ (1 / (m : ℝ) - c) * (N : ℝ) :=
    hlinear.eventually_ge_atTop 1
  filter_upwards [hlarge] with N hN
  have hrem_lt : ((N % m : ℕ) : ℝ) < (m : ℝ) := by
    exact_mod_cast Nat.mod_lt N hm_nat
  have hdecomp :
      (N : ℝ) = (m : ℝ) * ((N / m : ℕ) : ℝ) + ((N % m : ℕ) : ℝ) := by
    exact_mod_cast (Nat.div_add_mod N m).symm
  have hfloor :
      (N : ℝ) / (m : ℝ) - 1 < ((N / m : ℕ) : ℝ) := by
    rw [sub_lt_iff_lt_add]
    apply (div_lt_iff₀ hm).mpr
    nlinarith
  have hdiv : (1 / (m : ℝ)) * (N : ℝ) = (N : ℝ) / (m : ℝ) := by
    field_simp [hm.ne']
  have hN' : 1 ≤ (N : ℝ) / (m : ℝ) - c * (N : ℝ) := by
    calc
      1 ≤ (1 / (m : ℝ) - c) * (N : ℝ) := hN
      _ = (N : ℝ) / (m : ℝ) - c * (N : ℝ) := by
        rw [sub_mul, hdiv]
  nlinarith

/--
Raw logarithmic tails separate a coordinate held below a smaller linear
fraction from the balanced integer competitor.  The conclusion is a literal
gap inequality, not a normalized limiting-objective comparison.
-/
theorem eventually_saturationGap_separation_of_count_le
    {m : ℕ} [NeZero m] {A B sigma : ℝ} {h : ℕ → ℝ}
    {a : ℕ → ℕ} {r c C : ℝ}
    (hr_nonneg : 0 ≤ r) (hrc : r < c) (hc_uniform : c < 1 / (m : ℝ))
    (hB_neg : B < 0) (hsigma_pos : 0 < sigma)
    (hgap_pos : ∀ n : ℕ, 0 < saturationGap A h n)
    (hlog :
      Tendsto
        (fun n : ℕ =>
          Real.log (saturationGap A h n) /
            (B * (n : ℝ) ^ sigma))
        atTop (nhds 1))
    (ha_atTop : Tendsto a atTop atTop)
    (hC_pos : 0 < C) :
    ∀ᶠ N : ℕ in atTop,
      (a N : ℝ) ≤ r * (N : ℝ) ->
        C * saturationGap A h (N / m) < saturationGap A h (a N) := by
  let x : ℝ := r ^ sigma
  let y : ℝ := c ^ sigma
  have hc_pos : 0 < c := lt_of_le_of_lt hr_nonneg hrc
  have hx_nonneg : 0 ≤ x := by
    dsimp [x]
    exact Real.rpow_nonneg hr_nonneg sigma
  have hy_pos : 0 < y := by
    dsimp [y]
    exact Real.rpow_pos_of_pos hc_pos sigma
  have hxy : x < y := by
    dsimp [x, y]
    exact Real.rpow_lt_rpow hr_nonneg hrc hsigma_pos
  let delta : ℝ := (y - x) / (2 * (x + y))
  have hsum_pos : 0 < x + y := by linarith
  have hden_pos : 0 < 2 * (x + y) := mul_pos (by norm_num) hsum_pos
  have hdelta_pos : 0 < delta := by
    dsimp [delta]
    exact div_pos (sub_pos.mpr hxy) hden_pos
  have hdelta_lt_one : delta < 1 := by
    dsimp [delta]
    apply (div_lt_iff₀ hden_pos).mpr
    nlinarith
  have hdelta_mul : delta * (x + y) = (y - x) / 2 := by
    dsimp [delta]
    field_simp [ne_of_gt hsum_pos]
  have hdelta_separation : (1 + delta) * x < (1 - delta) * y := by
    nlinarith
  have hbracket_neg : (1 + delta) * x - (1 - delta) * y < 0 := by
    linarith
  let K : ℝ := B * ((1 + delta) * x - (1 - delta) * y)
  have hK_pos : 0 < K := by
    dsimp [K]
    exact mul_pos_of_neg_of_neg hB_neg hbracket_neg
  have hpow_top :
      Tendsto (fun N : ℕ => (N : ℝ) ^ sigma) atTop atTop :=
    (tendsto_rpow_atTop hsigma_pos).comp tendsto_natCast_atTop_atTop
  have hK_top :
      Tendsto (fun N : ℕ => K * (N : ℝ) ^ sigma) atTop atTop :=
    hpow_top.const_mul_atTop hK_pos
  have hgrow :
      ∀ᶠ N : ℕ in atTop, Real.log C < K * (N : ℝ) ^ sigma :=
    hK_top.eventually_gt_atTop (Real.log C)
  have hraw_bounds :=
    eventually_log_saturationGap_bounds hB_neg hsigma_pos hlog hdelta_pos
  have ha_bounds :
      ∀ᶠ N : ℕ in atTop,
        (1 + delta) * (B * (a N : ℝ) ^ sigma) <
            Real.log (saturationGap A h (a N)) ∧
          Real.log (saturationGap A h (a N)) <
            (1 - delta) * (B * (a N : ℝ) ^ sigma) :=
    ha_atTop.eventually hraw_bounds
  have hq_bounds :
      ∀ᶠ N : ℕ in atTop,
        (1 + delta) * (B * ((N / m : ℕ) : ℝ) ^ sigma) <
            Real.log (saturationGap A h (N / m)) ∧
          Real.log (saturationGap A h (N / m)) <
            (1 - delta) * (B * ((N / m : ℕ) : ℝ) ^ sigma) :=
    (tendsto_nat_div_typeCount_atTop (m := m)).eventually hraw_bounds
  have hfloor :
      ∀ᶠ N : ℕ in atTop, c * (N : ℝ) < ((N / m : ℕ) : ℝ) :=
    eventually_mul_lt_nat_div hc_uniform
  filter_upwards [ha_bounds, hq_bounds, hfloor, hgrow] with
    N ha hq hfloorN hgrowN
  intro hcountN
  have hpow_a :
      (a N : ℝ) ^ sigma ≤ x * (N : ℝ) ^ sigma := by
    calc
      (a N : ℝ) ^ sigma ≤ (r * (N : ℝ)) ^ sigma :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) hcountN hsigma_pos.le
      _ = x * (N : ℝ) ^ sigma := by
        rw [Real.mul_rpow hr_nonneg (Nat.cast_nonneg _)]
  have hpow_q :
      y * (N : ℝ) ^ sigma ≤ ((N / m : ℕ) : ℝ) ^ sigma := by
    calc
      y * (N : ℝ) ^ sigma = (c * (N : ℝ)) ^ sigma := by
        rw [Real.mul_rpow hc_pos.le (Nat.cast_nonneg _)]
      _ ≤ ((N / m : ℕ) : ℝ) ^ sigma :=
        Real.rpow_le_rpow (mul_nonneg hc_pos.le (Nat.cast_nonneg _))
          hfloorN.le hsigma_pos.le
  have hleft :
      (1 + delta) * (B * (x * (N : ℝ) ^ sigma)) <
        Real.log (saturationGap A h (a N)) := by
    have hBmul :
        B * (x * (N : ℝ) ^ sigma) ≤ B * (a N : ℝ) ^ sigma :=
      mul_le_mul_of_nonpos_left hpow_a hB_neg.le
    have hfac_nonneg : 0 ≤ 1 + delta := by linarith
    exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_left hBmul hfac_nonneg) ha.1
  have hright :
      Real.log (saturationGap A h (N / m)) <
        (1 - delta) * (B * (y * (N : ℝ) ^ sigma)) := by
    have hBmul :
        B * ((N / m : ℕ) : ℝ) ^ sigma ≤ B * (y * (N : ℝ) ^ sigma) :=
      mul_le_mul_of_nonpos_left hpow_q hB_neg.le
    have hfac_nonneg : 0 ≤ 1 - delta := by linarith
    exact lt_of_lt_of_le hq.2
      (mul_le_mul_of_nonneg_left hBmul hfac_nonneg)
  have hK_expand :
      K * (N : ℝ) ^ sigma =
        (1 + delta) * (B * (x * (N : ℝ) ^ sigma)) -
          (1 - delta) * (B * (y * (N : ℝ) ^ sigma)) := by
    dsimp [K]
    ring
  have hlog_lt :
      Real.log C + Real.log (saturationGap A h (N / m)) <
        Real.log (saturationGap A h (a N)) := by
    linarith
  calc
    C * saturationGap A h (N / m) =
        Real.exp (Real.log C) *
          Real.exp (Real.log (saturationGap A h (N / m))) := by
      rw [Real.exp_log hC_pos, Real.exp_log (hgap_pos _)]
    _ = Real.exp (Real.log C + Real.log (saturationGap A h (N / m))) :=
      (Real.exp_add _ _).symm
    _ < Real.exp (Real.log (saturationGap A h (a N))) :=
      Real.exp_lt_exp.mpr hlog_lt
    _ = saturationGap A h (a N) := Real.exp_log (hgap_pos _)

/--
No coordinate of a literal optimizer can remain below a fixed nonnegative
fraction strictly smaller than the uniform share.  This applies the raw-log
separation directly to the original finite integer objective.
-/
theorem eventually_optimalAllocation_count_gt_linear_of_log_tail
    {m : ℕ} [NeZero m] {A B sigma : ℝ} {h : ℕ → ℝ}
    (p : ItemType m → ℝ)
    (seq : AppliedModelingLib.Allocation.OptimalSequence
      (fun _ : ℕ => p) (fun _ : ℕ => fun _ : ItemType m => h))
    (hp_pos : ∀ i : ItemType m, 0 < p i)
    (hmono : Monotone h)
    (hB_neg : B < 0) (hsigma_pos : 0 < sigma)
    (hgap_eventual_pos : ∀ᶠ n in atTop, 0 < saturationGap A h n)
    (hlog :
      Tendsto
        (fun n : ℕ =>
          Real.log (saturationGap A h n) /
            (B * (n : ℝ) ^ sigma))
        atTop (nhds 1))
    (t : ItemType m) {r : ℝ}
    (hr_nonneg : 0 ≤ r) (hr_uniform : r < 1 / (m : ℝ)) :
    ∀ᶠ N : ℕ in atTop,
      r * (N : ℝ) < ((seq.allocation N).count t : ℝ) := by
  have hm_nat : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hm : 0 < (m : ℝ) := by exact_mod_cast hm_nat
  let u : ℝ := 1 / (m : ℝ)
  let c : ℝ := (r + u) / 2
  have hrc : r < c := by
    dsimp [c, u]
    linarith
  have hc_uniform : c < 1 / (m : ℝ) := by
    dsimp [c, u]
    linarith
  have hgap_pos : ∀ n : ℕ, 0 < saturationGap A h n :=
    saturationGap_pos_of_monotone_of_eventually_pos hmono hgap_eventual_pos
  have hgap_antitone : Antitone (saturationGap A h) :=
    saturationGap_antitone_of_monotone hmono
  have hcoord_top :
      Tendsto (fun N : ℕ => (seq.allocation N).count t) atTop atTop :=
    tendsto_optimalAllocation_count_atTop_of_log_tail
      p seq hp_pos hmono hB_neg hsigma_pos hgap_eventual_pos hlog t
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
  have hseparation :
      ∀ᶠ N : ℕ in atTop,
        ((seq.allocation N).count t : ℝ) ≤ r * (N : ℝ) ->
          C * saturationGap A h (N / m) <
            saturationGap A h ((seq.allocation N).count t) :=
    eventually_saturationGap_separation_of_count_le
      (m := m) (A := A) (B := B) (sigma := sigma) (h := h)
      (a := fun N => (seq.allocation N).count t) (r := r) (c := c) (C := C)
      hr_nonneg hrc hc_uniform hB_neg hsigma_pos hgap_pos hlog hcoord_top hC_pos
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
      ((weighted_saturationGap_sum_le_balanced_of_optimal (A := A) p seq N).trans
        hbalanced_sum_le)
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

/-- A linear lower bound on an optimal count is the same lower bound on its share. -/
theorem eventually_optimalAllocation_share_gt_of_log_tail
    {m : ℕ} [NeZero m] {A B sigma : ℝ} {h : ℕ → ℝ}
    (p : ItemType m → ℝ)
    (seq : AppliedModelingLib.Allocation.OptimalSequence
      (fun _ : ℕ => p) (fun _ : ℕ => fun _ : ItemType m => h))
    (hp_pos : ∀ i : ItemType m, 0 < p i)
    (hmono : Monotone h)
    (hB_neg : B < 0) (hsigma_pos : 0 < sigma)
    (hgap_eventual_pos : ∀ᶠ n in atTop, 0 < saturationGap A h n)
    (hlog :
      Tendsto
        (fun n : ℕ =>
          Real.log (saturationGap A h n) /
            (B * (n : ℝ) ^ sigma))
        atTop (nhds 1))
    (t : ItemType m) {r : ℝ}
    (hr_nonneg : 0 ≤ r) (hr_uniform : r < 1 / (m : ℝ)) :
    ∀ᶠ N : ℕ in atTop,
      r < AppliedModelingLib.Allocation.share (seq.allocation N) t := by
  have hcount :=
    eventually_optimalAllocation_count_gt_linear_of_log_tail
      p seq hp_pos hmono hB_neg hsigma_pos hgap_eventual_pos hlog t
      hr_nonneg hr_uniform
  filter_upwards [hcount, eventually_gt_atTop 0] with N hcountN hN_pos
  have htotal : AppliedModelingLib.Allocation.total (seq.allocation N) = N :=
    (seq.optimal N).1
  have htotal_ne : AppliedModelingLib.Allocation.total (seq.allocation N) ≠ 0 := by
    rw [htotal]
    exact Nat.ne_of_gt hN_pos
  rw [AppliedModelingLib.Allocation.share_eq_div_of_total_ne_zero
    (a := seq.allocation N) (k := t) htotal_ne, htotal]
  exact (lt_div_iff₀ (by exact_mod_cast hN_pos)).mpr hcountN

/--
On a finite non-singleton carrier, strict lower bounds on all other shares
give the complementary strict upper bound on the selected share.
-/
theorem share_lt_one_sub_other_lower_bounds
    {m : ℕ} [NeZero m] (a : CountAllocation m) (t : ItemType m) {r : ℝ}
    (hm_one_lt : 1 < m)
    (hsum : ∑ i : ItemType m, AppliedModelingLib.Allocation.share a i = 1)
    (hother : ∀ i : ItemType m, i ≠ t -> r < AppliedModelingLib.Allocation.share a i) :
    AppliedModelingLib.Allocation.share a t <
      1 - ((m - 1 : ℕ) : ℝ) * r := by
  let s : Finset (ItemType m) := Finset.univ.erase t
  have hs_nonempty : s.Nonempty := by
    apply Finset.card_pos.mp
    dsimp [s]
    rw [Finset.card_erase_of_mem (Finset.mem_univ t)]
    simpa [ItemType, Fintype.card_fin] using Nat.sub_pos_of_lt hm_one_lt
  have hsum_lower :
      (∑ i ∈ s, r) < ∑ i ∈ s, AppliedModelingLib.Allocation.share a i := by
    refine Finset.sum_lt_sum_of_nonempty hs_nonempty ?_
    intro i hi
    apply hother i
    intro hit
    subst i
    exact (Finset.mem_erase.mp hi).1 rfl
  have hconst :
      (∑ _i ∈ s, r) = ((m - 1 : ℕ) : ℝ) * r := by
    dsimp [s]
    rw [Finset.sum_const]
    simp [Finset.card_erase_of_mem (Finset.mem_univ t), Fintype.card_fin,
      nsmul_eq_mul]
  have hsum_erase :
      (∑ i ∈ s, AppliedModelingLib.Allocation.share a i) +
          AppliedModelingLib.Allocation.share a t = 1 := by
    calc
      (∑ i ∈ s, AppliedModelingLib.Allocation.share a i) +
          AppliedModelingLib.Allocation.share a t =
            ∑ i : ItemType m, AppliedModelingLib.Allocation.share a i := by
              dsimp [s]
              exact Finset.sum_erase_add Finset.univ
                (fun i => AppliedModelingLib.Allocation.share a i) (Finset.mem_univ t)
      _ = 1 := hsum
  rw [hconst] at hsum_lower
  linarith

/--
Corrected generic Lemma D.1(i): under the explicit all-positive,
monotone raw logarithmic-tail model, every literal optimal integer
allocation has uniform asymptotic shares.  The proof uses the finite objective
and its balanced integer competitor throughout.
-/
theorem corrected_lemmaD1_i_uniform_optimizer_shares_of_log_tail
    {m : ℕ} [NeZero m] {A B sigma : ℝ} {h : ℕ → ℝ}
    (p : ItemType m → ℝ)
    (seq : AppliedModelingLib.Allocation.OptimalSequence
      (fun _ : ℕ => p) (fun _ : ℕ => fun _ : ItemType m => h))
    (hp_pos : ∀ i : ItemType m, 0 < p i)
    (hmono : Monotone h)
    (hB_neg : B < 0) (hsigma_pos : 0 < sigma)
    (hgap_eventual_pos : ∀ᶠ n in atTop, 0 < saturationGap A h n)
    (hlog :
      Tendsto
        (fun n : ℕ =>
          Real.log (saturationGap A h n) /
            (B * (n : ℝ) ^ sigma))
        atTop (nhds 1)) :
    seq.toSequence.ConvergesToProfile
      (fun _ : ItemType m => 1 / (m : ℝ)) := by
  let u : ℝ := 1 / (m : ℝ)
  have hm_nat : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hm : 0 < (m : ℝ) := by exact_mod_cast hm_nat
  have hu_pos : 0 < u := by
    dsimp [u]
    exact one_div_pos.mpr hm
  intro t
  change Tendsto
    (fun N : ℕ => AppliedModelingLib.Allocation.share (seq.allocation N) t)
    atTop (nhds u)
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro lower hlower
    by_cases hlower_nonneg : 0 ≤ lower
    · exact eventually_optimalAllocation_share_gt_of_log_tail
        p seq hp_pos hmono hB_neg hsigma_pos hgap_eventual_pos hlog t
        hlower_nonneg (by simpa [u] using hlower)
    · filter_upwards with N
      have hlower_zero : lower < 0 := lt_of_not_ge hlower_nonneg
      exact lt_of_lt_of_le hlower_zero
        (AppliedModelingLib.Allocation.share_nonneg (a := seq.allocation N) (k := t))
  · intro upper hupper
    by_cases hm_one : m = 1
    · subst m
      filter_upwards [eventually_gt_atTop 0] with N hN_pos
      have htotal : AppliedModelingLib.Allocation.total (seq.allocation N) = N :=
        (seq.optimal N).1
      have htotal_ne : AppliedModelingLib.Allocation.total (seq.allocation N) ≠ 0 := by
        rw [htotal]
        exact Nat.ne_of_gt hN_pos
      have hsum :
          ∑ i : ItemType 1, AppliedModelingLib.Allocation.share (seq.allocation N) i = 1 :=
        AppliedModelingLib.Allocation.sum_share_eq_one_of_total_ne_zero
          (a := seq.allocation N) htotal_ne
      have ht_zero : t = 0 := Fin.eq_zero t
      subst t
      have hshare : AppliedModelingLib.Allocation.share (seq.allocation N) 0 = 1 := by
        simpa using hsum
      have hu_one : u = 1 := by simp [u]
      rw [hshare, ← hu_one]
      exact hupper
    · have hm_one_lt : 1 < m := by omega
      by_cases hupper_one : 1 ≤ upper
      · let r : ℝ := 0
        have hr_nonneg : 0 ≤ r := by dsimp [r]; norm_num
        have hr_uniform : r < 1 / (m : ℝ) := by
          dsimp [r]
          exact hu_pos
        have hall_lower :
            ∀ᶠ N : ℕ in atTop, ∀ i : ItemType m,
              r < AppliedModelingLib.Allocation.share (seq.allocation N) i :=
          Filter.eventually_all.2 (fun i =>
            eventually_optimalAllocation_share_gt_of_log_tail
              p seq hp_pos hmono hB_neg hsigma_pos hgap_eventual_pos hlog i
              hr_nonneg hr_uniform)
        filter_upwards [hall_lower, eventually_gt_atTop 0] with N hallN hN_pos
        have htotal : AppliedModelingLib.Allocation.total (seq.allocation N) = N :=
          (seq.optimal N).1
        have htotal_ne : AppliedModelingLib.Allocation.total (seq.allocation N) ≠ 0 := by
          rw [htotal]
          exact Nat.ne_of_gt hN_pos
        have hsum :
            ∑ i : ItemType m, AppliedModelingLib.Allocation.share (seq.allocation N) i = 1 :=
          AppliedModelingLib.Allocation.sum_share_eq_one_of_total_ne_zero
            (a := seq.allocation N) htotal_ne
        have hshare_lt_one :
            AppliedModelingLib.Allocation.share (seq.allocation N) t < 1 := by
          simpa [r] using
            (share_lt_one_sub_other_lower_bounds (a := seq.allocation N) t
              (r := r) hm_one_lt hsum (fun i _hi => hallN i))
        exact hshare_lt_one.trans_le hupper_one
      · have hupper_lt_one : upper < 1 := lt_of_not_ge hupper_one
        let M : ℝ := ((m - 1 : ℕ) : ℝ)
        have hm_sub_pos : 0 < m - 1 := Nat.sub_pos_of_lt hm_one_lt
        have hM_pos : 0 < M := by
          dsimp [M]
          exact_mod_cast hm_sub_pos
        have hM_ne : M ≠ 0 := ne_of_gt hM_pos
        have hM_u : M * u = 1 - u := by
          dsimp [M, u]
          rw [Nat.cast_sub (Nat.one_le_of_lt hm_nat)]
          field_simp [ne_of_gt hm]
          norm_num
        let r : ℝ := u - (upper - u) / M
        have heps_pos : 0 < upper - u := sub_pos.mpr hupper
        have heps_lt : upper - u < M * u := by
          rw [hM_u]
          linarith
        have hdiv_lt_u : (upper - u) / M < u := by
          apply (div_lt_iff₀ hM_pos).mpr
          nlinarith
        have hr_pos : 0 < r := by
          dsimp [r]
          linarith
        have hr_uniform : r < 1 / (m : ℝ) := by
          have hdiv_pos : 0 < (upper - u) / M := div_pos heps_pos hM_pos
          dsimp [r]
          dsimp [u] at hdiv_pos ⊢
          linarith
        have hall_lower :
            ∀ᶠ N : ℕ in atTop, ∀ i : ItemType m,
              r < AppliedModelingLib.Allocation.share (seq.allocation N) i :=
          Filter.eventually_all.2 (fun i =>
            eventually_optimalAllocation_share_gt_of_log_tail
              p seq hp_pos hmono hB_neg hsigma_pos hgap_eventual_pos hlog i
              hr_pos.le hr_uniform)
        filter_upwards [hall_lower, eventually_gt_atTop 0] with N hallN hN_pos
        have htotal : AppliedModelingLib.Allocation.total (seq.allocation N) = N :=
          (seq.optimal N).1
        have htotal_ne : AppliedModelingLib.Allocation.total (seq.allocation N) ≠ 0 := by
          rw [htotal]
          exact Nat.ne_of_gt hN_pos
        have hsum :
            ∑ i : ItemType m, AppliedModelingLib.Allocation.share (seq.allocation N) i = 1 :=
          AppliedModelingLib.Allocation.sum_share_eq_one_of_total_ne_zero
            (a := seq.allocation N) htotal_ne
        have hshare_bound :=
          share_lt_one_sub_other_lower_bounds (a := seq.allocation N) t
            (r := r) hm_one_lt hsum (fun i _hi => hallN i)
        have hbound_eq : 1 - M * r = upper := by
          calc
            1 - M * r = 1 - (M * u - (upper - u)) := by
              dsimp [r]
              rw [mul_sub, mul_div_cancel₀ _ hM_ne]
            _ = upper := by rw [hM_u]; ring
        have hcoefficient : ((m - 1 : ℕ) : ℝ) = M := by rfl
        rw [hcoefficient, hbound_eq] at hshare_bound
        exact hshare_bound

end AppendixD1GenericI
end PRPKG24AccuracyDiversity
