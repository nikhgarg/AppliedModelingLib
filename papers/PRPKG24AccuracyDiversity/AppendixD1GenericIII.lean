import PRPKG24AccuracyDiversity.MainTheorems
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Corrected generic Appendix D.1(iii)

This file develops the source-facing raw-allocation route for the logarithmic
branch of Lemma D.1.  In particular, it does not assume a limiting objective,
an optimizer-convergence certificate, or an interiority certificate.  The
first nontrivial obligation is that every coordinate of a literal finite
optimizer eventually becomes large; the source uses this fact before applying
its logarithmic asymptotic, but does not formalize the exchange argument.

The source's conclusion must use `p / sum p`; its displayed `p` conclusion is
the special case where the type probabilities have already been normalized.
-/

open Filter Topology
open scoped BigOperators

namespace PRPKG24AccuracyDiversity
namespace AppendixD1GenericIII

open AppliedModelingLib

/-- The source's discrete forward increment. -/
def forwardIncrement (h : ℕ → ℝ) (a : ℕ) : ℝ := h (a + 1) - h a

/-- The source's discrete strict-concavity convention, made explicit. -/
def StrictDiscreteConcave (h : ℕ → ℝ) : Prop := StrictAnti (forwardIncrement h)

/-- The logarithmic remainder occurring in corrected Lemma D.1(iii). -/
noncomputable def logRemainder (h : ℕ → ℝ) (B C : ℝ) (a : ℕ) : ℝ :=
  h a - B * Real.log (a : ℝ) - C

/--
The stated logarithmic asymptotic forces the one-step increments to vanish.
This is the analytic fact needed to compare a bounded destination with a
large donor in the *raw* finite allocation problem.
-/
theorem tendsto_forwardIncrement_nhds_zero_of_log_remainder
    {h : ℕ → ℝ} {B C : ℝ}
    (hrem : Tendsto (logRemainder h B C) atTop (nhds 0)) :
    Tendsto (forwardIncrement h) atTop (nhds 0) := by
  have hrem_succ :
      Tendsto (fun a : ℕ => logRemainder h B C (a + 1)) atTop (nhds 0) :=
    hrem.comp (tendsto_add_atTop_nat 1)
  have hlog :
      Tendsto
        (fun a : ℕ => Real.log ((a + 1 : ℕ) : ℝ) - Real.log (a : ℝ))
        atTop (nhds 0) := by
    simpa using Real.tendsto_log_nat_add_one_sub_log
  have hsum :
      Tendsto
        (fun a : ℕ =>
          (logRemainder h B C (a + 1) - logRemainder h B C a) +
            B * (Real.log ((a + 1 : ℕ) : ℝ) - Real.log (a : ℝ)))
        atTop (nhds 0) := by
    simpa using (hrem_succ.sub hrem).add (hlog.const_mul B)
  refine hsum.congr' ?_
  filter_upwards with a
  simp only [forwardIncrement, logRemainder]
  norm_num [Nat.cast_add]
  ring

/--
Source monotonicity and strict decrease of discrete forward increments force
every increment to be positive: a zero increment would make the next one
negative, contradicting monotonicity.
-/
theorem forwardIncrement_pos_of_monotone_strictDiscreteConcave
    {h : ℕ → ℝ} (hmono : Monotone h) (hconc : StrictDiscreteConcave h)
    (a : ℕ) : 0 < forwardIncrement h a := by
  have hnonneg : 0 ≤ forwardIncrement h a := by
    unfold forwardIncrement
    exact sub_nonneg.mpr (hmono (Nat.le_succ a))
  by_contra hnot
  have hzero : forwardIncrement h a = 0 := le_antisymm (le_of_not_gt hnot) hnonneg
  have hnext_lt : forwardIncrement h (a + 1) < forwardIncrement h a :=
    hconc (Nat.lt_succ_self a)
  have hnext_nonneg : 0 ≤ forwardIncrement h (a + 1) := by
    unfold forwardIncrement
    exact sub_nonneg.mpr (hmono (Nat.le_succ (a + 1)))
  linarith

/-- The same source conditions recover strict monotonicity internally. -/
theorem strictMono_of_monotone_strictDiscreteConcave
    {h : ℕ → ℝ} (hmono : Monotone h) (hconc : StrictDiscreteConcave h) :
    StrictMono h :=
  strictMono_nat_of_lt_succ fun a => by
    have hpos := forwardIncrement_pos_of_monotone_strictDiscreteConcave hmono hconc a
    unfold forwardIncrement at hpos
    linarith

/-- A finite positive weight profile has a positive total mass. -/
theorem weightSum_pos
    {m : ℕ} [NeZero m] (p : ItemType m → ℝ)
    (hp_pos : ∀ i, 0 < p i) :
    0 < ∑ i : ItemType m, p i := by
  exact Finset.sum_pos (fun i _ => hp_pos i) Finset.univ_nonempty

/-- Each nonnegative coordinate weight is bounded by the total weight. -/
theorem weight_le_weightSum
    {m : ℕ} (p : ItemType m → ℝ)
    (hp_nonneg : ∀ i, 0 ≤ p i) (i : ItemType m) :
    p i ≤ ∑ j : ItemType m, p j := by
  exact Finset.single_le_sum (fun j _ => hp_nonneg j) (Finset.mem_univ i)

/-- The corrected D.1(iii) target share, including the necessary normalization. -/
noncomputable def normalizedWeight
    {m : ℕ} (p : ItemType m → ℝ) (i : ItemType m) : ℝ :=
  p i / ∑ j : ItemType m, p j

theorem normalizedWeight_pos
    {m : ℕ} [NeZero m] (p : ItemType m → ℝ)
    (hp_pos : ∀ i, 0 < p i) (i : ItemType m) :
    0 < normalizedWeight p i := by
  unfold normalizedWeight
  exact div_pos (hp_pos i) (weightSum_pos p hp_pos)

theorem sum_normalizedWeight_eq_one
    {m : ℕ} [NeZero m] (p : ItemType m → ℝ)
    (hp_pos : ∀ i, 0 < p i) :
    (∑ i : ItemType m, normalizedWeight p i) = 1 := by
  have hsum_ne : (∑ i : ItemType m, p i) ≠ 0 :=
    ne_of_gt (weightSum_pos p hp_pos)
  unfold normalizedWeight
  rw [← Finset.sum_div]
  field_simp

/-- The continuous logarithmic objective used only after it is derived from the raw model. -/
noncomputable def weightedLogObjective
    {m : ℕ} (p x : ItemType m → ℝ) : ℝ :=
  ∑ i : ItemType m, p i * Real.log (x i)

/--
Corrected source variational fact: `sum p_i log x_i` is maximized, not
minimized, at the normalized positive weight vector.
-/
theorem weightedLogObjective_le_normalizedWeight
    {m : ℕ} [NeZero m] (p x : ItemType m → ℝ)
    (hp_pos : ∀ i, 0 < p i)
    (hx_pos : ∀ i, 0 < x i)
    (hx_sum : (∑ i : ItemType m, x i) = 1) :
    weightedLogObjective p x ≤ weightedLogObjective p (normalizedWeight p) := by
  let W : ℝ := ∑ i : ItemType m, p i
  have hW_pos : 0 < W := by
    simpa [W] using weightSum_pos p hp_pos
  have hq_pos : ∀ i, 0 < normalizedWeight p i :=
    fun i => normalizedWeight_pos p hp_pos i
  have hterm : ∀ i : ItemType m,
      p i * Real.log (x i / normalizedWeight p i) ≤
        p i * (x i / normalizedWeight p i - 1) := by
    intro i
    exact mul_le_mul_of_nonneg_left
      (Real.log_le_sub_one_of_pos (div_pos (hx_pos i) (hq_pos i)))
      (hp_pos i).le
  have hweighted :
      (∑ i : ItemType m, p i * Real.log (x i / normalizedWeight p i)) ≤
        ∑ i : ItemType m, p i * (x i / normalizedWeight p i - 1) :=
    Finset.sum_le_sum (fun i _ => hterm i)
  have hright_zero :
      (∑ i : ItemType m, p i * (x i / normalizedWeight p i - 1)) = 0 := by
    have hterm_eq : ∀ i : ItemType m,
        p i * (x i / normalizedWeight p i - 1) = W * x i - p i := by
      intro i
      have hq : normalizedWeight p i = p i / W := by
        simp [normalizedWeight, W]
      rw [hq]
      field_simp [ne_of_gt (hp_pos i), ne_of_gt hW_pos]
    calc
      (∑ i : ItemType m, p i * (x i / normalizedWeight p i - 1)) =
          ∑ i : ItemType m, (W * x i - p i) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            exact hterm_eq i
      _ = W * (∑ i : ItemType m, x i) - ∑ i : ItemType m, p i := by
            rw [Finset.sum_sub_distrib, Finset.mul_sum]
      _ = 0 := by simp [hx_sum, W]
  have hleft_eq :
      (∑ i : ItemType m, p i * Real.log (x i / normalizedWeight p i)) =
        weightedLogObjective p x - weightedLogObjective p (normalizedWeight p) := by
    unfold weightedLogObjective
    calc
      (∑ i : ItemType m, p i * Real.log (x i / normalizedWeight p i)) =
          ∑ i : ItemType m,
            (p i * Real.log (x i) - p i * Real.log (normalizedWeight p i)) := by
              refine Finset.sum_congr rfl ?_
              intro i _
              rw [Real.log_div (hx_pos i).ne' (hq_pos i).ne']
              ring
      _ = (∑ i : ItemType m, p i * Real.log (x i)) -
          ∑ i : ItemType m, p i * Real.log (normalizedWeight p i) :=
            by rw [Finset.sum_sub_distrib]
  rw [hleft_eq, hright_zero] at hweighted
  linarith

/-- The corrected logarithmic variational maximum is strict away from `p / sum p`. -/
theorem weightedLogObjective_lt_normalizedWeight_of_ne
    {m : ℕ} [NeZero m] (p x : ItemType m → ℝ)
    (hp_pos : ∀ i, 0 < p i)
    (hx_pos : ∀ i, 0 < x i)
    (hx_sum : (∑ i : ItemType m, x i) = 1)
    (hx_ne : x ≠ normalizedWeight p) :
    weightedLogObjective p x < weightedLogObjective p (normalizedWeight p) := by
  let W : ℝ := ∑ i : ItemType m, p i
  have hW_pos : 0 < W := by
    simpa [W] using weightSum_pos p hp_pos
  have hq_pos : ∀ i, 0 < normalizedWeight p i :=
    fun i => normalizedWeight_pos p hp_pos i
  obtain ⟨j, hj_ne⟩ := Function.ne_iff.mp hx_ne
  have hj_ratio_ne_one : x j / normalizedWeight p j ≠ 1 := by
    intro hratio
    apply hj_ne
    field_simp [ne_of_gt (hq_pos j)] at hratio
    exact hratio
  have hterm_le : ∀ i : ItemType m,
      p i * Real.log (x i / normalizedWeight p i) ≤
        p i * (x i / normalizedWeight p i - 1) := by
    intro i
    exact mul_le_mul_of_nonneg_left
      (Real.log_le_sub_one_of_pos (div_pos (hx_pos i) (hq_pos i)))
      (hp_pos i).le
  have hterm_lt :
      p j * Real.log (x j / normalizedWeight p j) <
        p j * (x j / normalizedWeight p j - 1) := by
    exact mul_lt_mul_of_pos_left
      (Real.log_lt_sub_one_of_pos
        (div_pos (hx_pos j) (hq_pos j)) hj_ratio_ne_one)
      (hp_pos j)
  have hweighted_lt :
      (∑ i : ItemType m, p i * Real.log (x i / normalizedWeight p i)) <
        ∑ i : ItemType m, p i * (x i / normalizedWeight p i - 1) := by
    refine Finset.sum_lt_sum (fun i _ => hterm_le i) ?_
    exact ⟨j, Finset.mem_univ j, hterm_lt⟩
  have hright_zero :
      (∑ i : ItemType m, p i * (x i / normalizedWeight p i - 1)) = 0 := by
    have hterm_eq : ∀ i : ItemType m,
        p i * (x i / normalizedWeight p i - 1) = W * x i - p i := by
      intro i
      have hq : normalizedWeight p i = p i / W := by
        simp [normalizedWeight, W]
      rw [hq]
      field_simp [ne_of_gt (hp_pos i), ne_of_gt hW_pos]
    calc
      (∑ i : ItemType m, p i * (x i / normalizedWeight p i - 1)) =
          ∑ i : ItemType m, (W * x i - p i) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            exact hterm_eq i
      _ = W * (∑ i : ItemType m, x i) - ∑ i : ItemType m, p i := by
            rw [Finset.sum_sub_distrib, Finset.mul_sum]
      _ = 0 := by simp [hx_sum, W]
  have hleft_eq :
      (∑ i : ItemType m, p i * Real.log (x i / normalizedWeight p i)) =
        weightedLogObjective p x - weightedLogObjective p (normalizedWeight p) := by
    unfold weightedLogObjective
    calc
      (∑ i : ItemType m, p i * Real.log (x i / normalizedWeight p i)) =
          ∑ i : ItemType m,
            (p i * Real.log (x i) - p i * Real.log (normalizedWeight p i)) := by
              refine Finset.sum_congr rfl ?_
              intro i _
              rw [Real.log_div (hx_pos i).ne' (hq_pos i).ne']
              ring
      _ = (∑ i : ItemType m, p i * Real.log (x i)) -
          ∑ i : ItemType m, p i * Real.log (normalizedWeight p i) :=
            by rw [Finset.sum_sub_distrib]
  rw [hleft_eq, hright_zero] at hweighted_lt
  linarith

/-- The finite weighted sum of logarithmic remainders. -/
noncomputable def weightedLogRemainderSum
    {m : ℕ} (p : ItemType m → ℝ) (h : ℕ → ℝ) (B C : ℝ)
    (a : CountAllocation m) : ℝ :=
  ∑ i : ItemType m, p i * logRemainder h B C (a.count i)

/--
After every coordinate of a count allocation diverges, its finite remainder
sum vanishes.  This is a direct finite-sum consequence of the source's
pointwise logarithmic asymptotic.
-/
theorem tendsto_weightedLogRemainderSum_nhds_zero
    {m : ℕ} {B C : ℝ} {h : ℕ → ℝ}
    (p : ItemType m → ℝ) (a : ℕ → CountAllocation m)
    (hrem : Tendsto (logRemainder h B C) atTop (nhds 0))
    (ha_top : ∀ i : ItemType m,
      Tendsto (fun N : ℕ => (a N).count i) atTop atTop) :
    Tendsto
      (fun N : ℕ => weightedLogRemainderSum p h B C (a N))
      atTop (nhds 0) := by
  have hsum :
      Tendsto
        (fun N : ℕ =>
          ∑ i : ItemType m,
            p i * logRemainder h B C ((a N).count i))
        atTop (nhds (∑ _i : ItemType m, (0 : ℝ))) := by
    exact tendsto_finset_sum Finset.univ (fun i _ => by
      simpa using
        (tendsto_const_nhds (x := p i)).mul (hrem.comp (ha_top i)))
  simpa [weightedLogRemainderSum] using hsum

/--
Raw objective comparison after the source's logarithmic expansion.  Both
allocation families have literal total `N` and all coordinates diverge; no
limiting-objective estimate is assumed.  The conclusion says the difference
between the raw objective difference and its weighted-log counterpart tends
to zero.
-/
theorem tendsto_rawObjective_sub_weightedLogComparison_nhds_zero
    {m : ℕ} [NeZero m] {B C : ℝ} {h : ℕ → ℝ}
    (p : ItemType m → ℝ)
    (a b : ℕ → CountAllocation m)
    (ha_total : ∀ N, AppliedModelingLib.Allocation.total (a N) = N)
    (hb_total : ∀ N, AppliedModelingLib.Allocation.total (b N) = N)
    (ha_top : ∀ i : ItemType m,
      Tendsto (fun N : ℕ => (a N).count i) atTop atTop)
    (hb_top : ∀ i : ItemType m,
      Tendsto (fun N : ℕ => (b N).count i) atTop atTop)
    (hrem : Tendsto (logRemainder h B C) atTop (nhds 0)) :
    Tendsto
      (fun N : ℕ =>
        (AppliedModelingLib.Allocation.objective (a N) p (fun _ : ItemType m => h) -
          AppliedModelingLib.Allocation.objective (b N) p (fun _ : ItemType m => h)) -
          B *
            (weightedLogObjective p
                (fun i => AppliedModelingLib.Allocation.share (a N) i) -
              weightedLogObjective p
                (fun i => AppliedModelingLib.Allocation.share (b N) i)))
      atTop (nhds 0) := by
  let ra : ℕ → ℝ := fun N => weightedLogRemainderSum p h B C (a N)
  let rb : ℕ → ℝ := fun N => weightedLogRemainderSum p h B C (b N)
  have hra : Tendsto ra atTop (nhds 0) := by
    simpa [ra] using tendsto_weightedLogRemainderSum_nhds_zero p a hrem ha_top
  have hrb : Tendsto rb atTop (nhds 0) := by
    simpa [rb] using tendsto_weightedLogRemainderSum_nhds_zero p b hrem hb_top
  have hrem_diff : Tendsto (fun N : ℕ => ra N - rb N) atTop (nhds 0) :=
    by simpa using hra.sub hrb
  have ha_pos : ∀ᶠ N : ℕ in atTop, ∀ i : ItemType m, 0 < (a N).count i := by
    refine Filter.eventually_all.2 ?_
    intro i
    exact (ha_top i).eventually_gt_atTop 0
  have hb_pos : ∀ᶠ N : ℕ in atTop, ∀ i : ItemType m, 0 < (b N).count i := by
    refine Filter.eventually_all.2 ?_
    intro i
    exact (hb_top i).eventually_gt_atTop 0
  have hraw_eq :
      ∀ᶠ N : ℕ in atTop,
        (AppliedModelingLib.Allocation.objective (a N) p (fun _ : ItemType m => h) -
          AppliedModelingLib.Allocation.objective (b N) p (fun _ : ItemType m => h)) -
          B *
            (weightedLogObjective p
                (fun i => AppliedModelingLib.Allocation.share (a N) i) -
              weightedLogObjective p
                (fun i => AppliedModelingLib.Allocation.share (b N) i)) =
          ra N - rb N := by
    filter_upwards [ha_pos, hb_pos, eventually_gt_atTop 0] with N haN hbN hN_pos
    have hN_ne : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN_pos)
    have hshare_a : ∀ i : ItemType m,
        ((a N).count i : ℝ) =
          (N : ℝ) * AppliedModelingLib.Allocation.share (a N) i := by
      intro i
      rw [AppliedModelingLib.Allocation.share_eq_div_of_total_ne_zero
        (a := a N) (k := i)]
      · rw [ha_total N]
        field_simp
      · rw [ha_total N]
        exact Nat.ne_of_gt hN_pos
    have hshare_b : ∀ i : ItemType m,
        ((b N).count i : ℝ) =
          (N : ℝ) * AppliedModelingLib.Allocation.share (b N) i := by
      intro i
      rw [AppliedModelingLib.Allocation.share_eq_div_of_total_ne_zero
        (a := b N) (k := i)]
      · rw [hb_total N]
        field_simp
      · rw [hb_total N]
        exact Nat.ne_of_gt hN_pos
    have hshare_a_pos : ∀ i : ItemType m,
        0 < AppliedModelingLib.Allocation.share (a N) i := by
      intro i
      have hcount_pos : 0 < ((a N).count i : ℝ) := by exact_mod_cast haN i
      have hprod : 0 < (N : ℝ) * AppliedModelingLib.Allocation.share (a N) i := by
        rw [← hshare_a i]
        exact hcount_pos
      have hN_real : 0 < (N : ℝ) := by exact_mod_cast hN_pos
      nlinarith
    have hshare_b_pos : ∀ i : ItemType m,
        0 < AppliedModelingLib.Allocation.share (b N) i := by
      intro i
      have hcount_pos : 0 < ((b N).count i : ℝ) := by exact_mod_cast hbN i
      have hprod : 0 < (N : ℝ) * AppliedModelingLib.Allocation.share (b N) i := by
        rw [← hshare_b i]
        exact hcount_pos
      have hN_real : 0 < (N : ℝ) := by exact_mod_cast hN_pos
      nlinarith
    have hlog_a : ∀ i : ItemType m,
        Real.log ((a N).count i : ℝ) =
          Real.log (N : ℝ) + Real.log (AppliedModelingLib.Allocation.share (a N) i) := by
      intro i
      rw [hshare_a i, Real.log_mul hN_ne (hshare_a_pos i).ne']
    have hlog_b : ∀ i : ItemType m,
        Real.log ((b N).count i : ℝ) =
          Real.log (N : ℝ) + Real.log (AppliedModelingLib.Allocation.share (b N) i) := by
      intro i
      rw [hshare_b i, Real.log_mul hN_ne (hshare_b_pos i).ne']
    have hvalue_a : ∀ i : ItemType m,
        h ((a N).count i) =
          B * (Real.log (N : ℝ) + Real.log (AppliedModelingLib.Allocation.share (a N) i)) + C +
            logRemainder h B C ((a N).count i) := by
      intro i
      unfold logRemainder
      rw [← hlog_a i]
      ring
    have hvalue_b : ∀ i : ItemType m,
        h ((b N).count i) =
          B * (Real.log (N : ℝ) + Real.log (AppliedModelingLib.Allocation.share (b N) i)) + C +
            logRemainder h B C ((b N).count i) := by
      intro i
      unfold logRemainder
      rw [← hlog_b i]
      ring
    unfold AppliedModelingLib.Allocation.objective weightedLogObjective ra rb
      weightedLogRemainderSum
    simp only
    rw [show
      (∑ i : ItemType m, p i * h ((a N).count i)) =
        ∑ i : ItemType m,
          p i *
            (B * (Real.log (N : ℝ) + Real.log (AppliedModelingLib.Allocation.share (a N) i)) + C +
              logRemainder h B C ((a N).count i)) by
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [hvalue_a i],
      show
      (∑ i : ItemType m, p i * h ((b N).count i)) =
        ∑ i : ItemType m,
          p i *
            (B * (Real.log (N : ℝ) + Real.log (AppliedModelingLib.Allocation.share (b N) i)) + C +
              logRemainder h B C ((b N).count i)) by
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [hvalue_b i]]
    ring_nf
    simp only [Finset.sum_add_distrib, Finset.mul_sum]
    have hNcancel :
        (∑ x : ItemType m, p x * B * Real.log (N : ℝ)) =
          ∑ x : ItemType m, B * Real.log (N : ℝ) * p x := by
      refine Finset.sum_congr rfl ?_
      intro x _
      ring
    have hshare_a_reorder :
        (∑ x : ItemType m, p x * B * Real.log (AppliedModelingLib.Allocation.share (a N) x)) =
          ∑ x : ItemType m, B * (p x * Real.log (AppliedModelingLib.Allocation.share (a N) x)) := by
      refine Finset.sum_congr rfl ?_
      intro x _
      ring
    have hshare_b_reorder :
        (∑ x : ItemType m, B * p x * Real.log (AppliedModelingLib.Allocation.share (b N) x)) =
          ∑ x : ItemType m, B * (p x * Real.log (AppliedModelingLib.Allocation.share (b N) x)) := by
      refine Finset.sum_congr rfl ?_
      intro x _
      ring
    have hCcancel :
        (∑ x : ItemType m, p x * C) = ∑ x : ItemType m, C * p x := by
      refine Finset.sum_congr rfl ?_
      intro x _
      ring
    rw [hNcancel, hshare_a_reorder, hshare_b_reorder, hCcancel]
    ring
  refine hrem_diff.congr' ?_
  filter_upwards [hraw_eq] with N hN
  exact hN.symm

/-- A fixed available type used only to absorb the finite floor remainder. -/
noncomputable def roundingAnchor {m : ℕ} [NeZero m] : ItemType m :=
  Classical.choice (inferInstance : Nonempty (ItemType m))

/-- Coordinatewise floors of the corrected normalized target. -/
noncomputable def normalizedFloorCount
    {m : ℕ} (p : ItemType m → ℝ) (N : ℕ) (i : ItemType m) : ℕ :=
  ⌊(N : ℝ) * normalizedWeight p i⌋₊

/--
An explicit feasible integer competitor for the corrected logarithmic target.
All non-anchor coordinates are floored; the anchor absorbs exactly the finite
remainder.  This is a construction, not a caller-provided rounding certificate.
-/
noncomputable def normalizedIntegerCompetitor
    {m : ℕ} [NeZero m] (p : ItemType m → ℝ) (N : ℕ) : CountAllocation m where
  count := fun i =>
    if i = roundingAnchor then
      N - ∑ j ∈ Finset.univ.erase roundingAnchor, normalizedFloorCount p N j
    else normalizedFloorCount p N i

theorem sum_normalizedFloorCount_erase_le
    {m : ℕ} [NeZero m] (p : ItemType m → ℝ)
    (hp_pos : ∀ i, 0 < p i) (N : ℕ) :
    (∑ j ∈ Finset.univ.erase (roundingAnchor : ItemType m),
      normalizedFloorCount p N j) ≤ N := by
  let q : ItemType m → ℝ := normalizedWeight p
  have hq_nonneg : ∀ i, 0 ≤ q i := fun i => (normalizedWeight_pos p hp_pos i).le
  have hfloor_le : ∀ j : ItemType m,
      ((normalizedFloorCount p N j : ℕ) : ℝ) ≤ (N : ℝ) * q j := by
    intro j
    exact Nat.floor_le (mul_nonneg (Nat.cast_nonneg _) (hq_nonneg j))
  have herase_le :
      ((∑ j ∈ Finset.univ.erase (roundingAnchor : ItemType m),
        normalizedFloorCount p N j : ℕ) : ℝ) ≤ (N : ℝ) := by
    calc
      ((∑ j ∈ Finset.univ.erase (roundingAnchor : ItemType m),
        normalizedFloorCount p N j : ℕ) : ℝ) =
          ∑ j ∈ Finset.univ.erase (roundingAnchor : ItemType m),
            ((normalizedFloorCount p N j : ℕ) : ℝ) := by
              norm_num [Nat.cast_sum]
      _ ≤ ∑ j ∈ Finset.univ.erase (roundingAnchor : ItemType m),
          (N : ℝ) * q j :=
            Finset.sum_le_sum (fun j _ => hfloor_le j)
      _ ≤ ∑ j : ItemType m, (N : ℝ) * q j := by
            calc
              (∑ j ∈ Finset.univ.erase (roundingAnchor : ItemType m),
                (N : ℝ) * q j) ≤
                  (N : ℝ) * q (roundingAnchor : ItemType m) +
                    ∑ j ∈ Finset.univ.erase (roundingAnchor : ItemType m),
                      (N : ℝ) * q j := by
                        exact le_add_of_nonneg_left
                          (mul_nonneg (Nat.cast_nonneg _) (hq_nonneg _))
              _ = ∑ j : ItemType m, (N : ℝ) * q j := by
                    exact Finset.add_sum_erase Finset.univ
                      (fun j : ItemType m => (N : ℝ) * q j) (Finset.mem_univ _)
      _ = (N : ℝ) := by
            rw [← Finset.mul_sum, sum_normalizedWeight_eq_one p hp_pos, mul_one]
  exact_mod_cast herase_le

/-- The sum of all normalized target floors never exceeds its intended total. -/
theorem sum_normalizedFloorCount_le
    {m : ℕ} [NeZero m] (p : ItemType m → ℝ)
    (hp_pos : ∀ i, 0 < p i) (N : ℕ) :
    (∑ j : ItemType m, normalizedFloorCount p N j) ≤ N := by
  let q : ItemType m → ℝ := normalizedWeight p
  have hq_nonneg : ∀ i, 0 ≤ q i := fun i => (normalizedWeight_pos p hp_pos i).le
  have hfloor_le : ∀ j : ItemType m,
      ((normalizedFloorCount p N j : ℕ) : ℝ) ≤ (N : ℝ) * q j := by
    intro j
    exact Nat.floor_le (mul_nonneg (Nat.cast_nonneg _) (hq_nonneg j))
  have hsum_le :
      ((∑ j : ItemType m, normalizedFloorCount p N j : ℕ) : ℝ) ≤ (N : ℝ) := by
    calc
      ((∑ j : ItemType m, normalizedFloorCount p N j : ℕ) : ℝ) =
          ∑ j : ItemType m, ((normalizedFloorCount p N j : ℕ) : ℝ) := by
            norm_num [Nat.cast_sum]
      _ ≤ ∑ j : ItemType m, (N : ℝ) * q j :=
            Finset.sum_le_sum (fun j _ => hfloor_le j)
      _ = (N : ℝ) := by
            rw [← Finset.mul_sum, sum_normalizedWeight_eq_one p hp_pos, mul_one]
  exact_mod_cast hsum_le

/-- The constructed normalized integer competitor has exactly total `N`. -/
theorem normalizedIntegerCompetitor_total
    {m : ℕ} [NeZero m] (p : ItemType m → ℝ)
    (hp_pos : ∀ i, 0 < p i) (N : ℕ) :
    AppliedModelingLib.Allocation.total (normalizedIntegerCompetitor p N) = N := by
  classical
  let anchor : ItemType m := roundingAnchor
  let S : ℕ := ∑ j ∈ Finset.univ.erase anchor, normalizedFloorCount p N j
  have hS_le : S ≤ N := by
    simpa [S, anchor] using sum_normalizedFloorCount_erase_le p hp_pos N
  change (∑ i : ItemType m,
    if i = anchor then N - S else normalizedFloorCount p N i) = N
  have hsum :
      (∑ i : ItemType m,
        if i = anchor then N - S else normalizedFloorCount p N i) =
          (N - S) + ∑ i ∈ Finset.univ.erase anchor, normalizedFloorCount p N i := by
    rw [← Finset.add_sum_erase Finset.univ
      (fun i : ItemType m =>
        if i = anchor then N - S else normalizedFloorCount p N i)
      (Finset.mem_univ anchor)]
    simp only [if_pos]
    refine congrArg (fun z : ℕ => N - S + z) ?_
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hine : i ≠ anchor := Finset.ne_of_mem_erase hi
    simp [hine]
  rw [hsum]
  change N - S + S = N
  exact Nat.sub_add_cancel hS_le

/-- A positive normalized target has a floor count diverging with `N`. -/
theorem tendsto_normalizedFloorCount_atTop
    {m : ℕ} [NeZero m] (p : ItemType m → ℝ)
    (hp_pos : ∀ i, 0 < p i) (i : ItemType m) :
    Tendsto (fun N : ℕ => normalizedFloorCount p N i) atTop atTop := by
  have hq_pos : 0 < normalizedWeight p i := normalizedWeight_pos p hp_pos i
  have hgrow :
      Tendsto (fun N : ℕ => (N : ℝ) * normalizedWeight p i) atTop atTop := by
    simpa [mul_comm] using
      tendsto_natCast_atTop_atTop.const_mul_atTop hq_pos
  rw [tendsto_atTop]
  intro K
  filter_upwards [hgrow.eventually_ge_atTop (K : ℝ)] with N hN
  exact Nat.le_floor hN

/-- The anchor count contains its own normalized floor as well as the remainder. -/
theorem normalizedFloorCount_le_normalizedIntegerCompetitor_count
    {m : ℕ} [NeZero m] (p : ItemType m → ℝ)
    (hp_pos : ∀ i, 0 < p i) (N : ℕ) :
    normalizedFloorCount p N (roundingAnchor : ItemType m) ≤
      (normalizedIntegerCompetitor p N).count (roundingAnchor : ItemType m) := by
  classical
  let anchor : ItemType m := roundingAnchor
  let S : ℕ := ∑ j ∈ Finset.univ.erase anchor, normalizedFloorCount p N j
  have hsum_all :
      normalizedFloorCount p N anchor + S ≤ N := by
    have hdecomp :
        normalizedFloorCount p N anchor + S =
          ∑ j : ItemType m, normalizedFloorCount p N j := by
      dsimp [S]
      exact Finset.add_sum_erase Finset.univ
        (fun j : ItemType m => normalizedFloorCount p N j) (Finset.mem_univ anchor)
    rw [hdecomp]
    exact sum_normalizedFloorCount_le p hp_pos N
  have hfloor_le : normalizedFloorCount p N anchor ≤ N - S :=
    Nat.le_sub_of_add_le hsum_all
  simpa [normalizedIntegerCompetitor, anchor, S] using hfloor_le

/-- Every coordinate of the internally constructed normalized competitor diverges. -/
theorem tendsto_normalizedIntegerCompetitor_count_atTop
    {m : ℕ} [NeZero m] (p : ItemType m → ℝ)
    (hp_pos : ∀ i, 0 < p i) (i : ItemType m) :
    Tendsto (fun N : ℕ => (normalizedIntegerCompetitor p N).count i) atTop atTop := by
  have hfloor_top :
      Tendsto (fun N : ℕ => normalizedFloorCount p N i) atTop atTop :=
    tendsto_normalizedFloorCount_atTop p hp_pos i
  refine tendsto_atTop_mono' atTop ?_ hfloor_top
  filter_upwards with N
  by_cases hi : i = (roundingAnchor : ItemType m)
  · subst i
    exact normalizedFloorCount_le_normalizedIntegerCompetitor_count p hp_pos N
  · simp [normalizedIntegerCompetitor, hi]

/-- Each non-anchor floor differs from its real target by at most one. -/
theorem abs_normalizedFloorCount_sub_target_le_one
    {m : ℕ} [NeZero m] (p : ItemType m → ℝ)
    (hp_pos : ∀ i, 0 < p i) (N : ℕ) (i : ItemType m) :
    |((normalizedFloorCount p N i : ℕ) : ℝ) -
        (N : ℝ) * normalizedWeight p i| ≤ 1 := by
  unfold normalizedFloorCount
  exact Nat.abs_floor_sub_le
    (mul_nonneg (Nat.cast_nonneg _) (normalizedWeight_pos p hp_pos i).le)

/-- The anchor absorbs at most one floor error from each other coordinate. -/
theorem abs_normalizedIntegerCompetitor_anchor_sub_target_le_card
    {m : ℕ} [NeZero m] (p : ItemType m → ℝ)
    (hp_pos : ∀ i, 0 < p i) (N : ℕ) :
    |(((normalizedIntegerCompetitor p N).count (roundingAnchor : ItemType m) : ℕ) : ℝ) -
        (N : ℝ) * normalizedWeight p (roundingAnchor : ItemType m)| ≤
      (Fintype.card (ItemType m) : ℝ) := by
  classical
  let anchor : ItemType m := roundingAnchor
  let q : ItemType m → ℝ := normalizedWeight p
  let S : ℕ := ∑ j ∈ Finset.univ.erase anchor, normalizedFloorCount p N j
  have hS_le : S ≤ N := by
    simpa [S, anchor] using sum_normalizedFloorCount_erase_le p hp_pos N
  have hS_cast :
      (S : ℝ) = ∑ j ∈ Finset.univ.erase anchor,
        ((normalizedFloorCount p N j : ℕ) : ℝ) := by
    simp [S, Nat.cast_sum]
  have hsum_q :
      (N : ℝ) * q anchor +
          ∑ j ∈ Finset.univ.erase anchor, (N : ℝ) * q j = (N : ℝ) := by
    calc
      (N : ℝ) * q anchor +
          ∑ j ∈ Finset.univ.erase anchor, (N : ℝ) * q j =
            (N : ℝ) * (q anchor + ∑ j ∈ Finset.univ.erase anchor, q j) := by
              rw [← Finset.mul_sum]
              ring
      _ = (N : ℝ) * ∑ j : ItemType m, q j := by
            rw [Finset.add_sum_erase Finset.univ q (Finset.mem_univ anchor)]
      _ = (N : ℝ) := by
            rw [show (∑ j : ItemType m, q j) = 1 by
              simpa [q] using sum_normalizedWeight_eq_one p hp_pos, mul_one]
  have hcount_anchor :
      (normalizedIntegerCompetitor p N).count anchor = N - S := by
    simp [normalizedIntegerCompetitor, anchor, S]
  have herror :
      (((normalizedIntegerCompetitor p N).count anchor : ℕ) : ℝ) -
          (N : ℝ) * q anchor =
        ∑ j ∈ Finset.univ.erase anchor,
          ((N : ℝ) * q j - ((normalizedFloorCount p N j : ℕ) : ℝ)) := by
    rw [hcount_anchor, Nat.cast_sub hS_le, hS_cast, Finset.sum_sub_distrib]
    linarith
  have hterm_nonneg : ∀ j : ItemType m,
      0 ≤ (N : ℝ) * q j - ((normalizedFloorCount p N j : ℕ) : ℝ) := by
    intro j
    exact sub_nonneg.mpr
      (Nat.floor_le (mul_nonneg (Nat.cast_nonneg _)
        (normalizedWeight_pos p hp_pos j).le))
  have hterm_le_one : ∀ j : ItemType m,
      (N : ℝ) * q j - ((normalizedFloorCount p N j : ℕ) : ℝ) ≤ 1 := by
    intro j
    have hlt : (N : ℝ) * q j < (normalizedFloorCount p N j : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    linarith
  have hsum_nonneg :
      0 ≤ ∑ j ∈ Finset.univ.erase anchor,
        ((N : ℝ) * q j - ((normalizedFloorCount p N j : ℕ) : ℝ)) :=
    Finset.sum_nonneg (fun j _ => hterm_nonneg j)
  have hsum_le_card :
      (∑ j ∈ Finset.univ.erase anchor,
        ((N : ℝ) * q j - ((normalizedFloorCount p N j : ℕ) : ℝ))) ≤
          (Fintype.card (ItemType m) : ℝ) := by
    calc
      (∑ j ∈ Finset.univ.erase anchor,
        ((N : ℝ) * q j - ((normalizedFloorCount p N j : ℕ) : ℝ))) ≤
          ∑ _j ∈ Finset.univ.erase anchor, (1 : ℝ) :=
            Finset.sum_le_sum (fun j _ => hterm_le_one j)
      _ = ((Finset.univ.erase anchor).card : ℝ) := by simp
      _ ≤ (Fintype.card (ItemType m) : ℝ) := by
            exact_mod_cast Finset.card_le_card (Finset.erase_subset _ _)
  change |(((normalizedIntegerCompetitor p N).count anchor : ℕ) : ℝ) -
      (N : ℝ) * q anchor| ≤ (Fintype.card (ItemType m) : ℝ)
  rw [herror, abs_of_nonneg hsum_nonneg]
  exact hsum_le_card

/--
The raw source interiority step for corrected D.1(iii).

For a positive finite type distribution, a strictly increasing, discretely
strictly concave `h` with `h(a) - B log a - C -> 0` cannot have an optimal
coordinate bounded along an unbounded sequence of fixed-total problems.  The
proof invokes only the literal one-unit exchange condition of each finite
optimizer.  No continuous relaxation or allocation-limit premise is used.
-/
theorem tendsto_optimalAllocation_count_atTop_of_log_remainder
    {m : ℕ} [NeZero m] {B C : ℝ} {h : ℕ → ℝ}
    (p : ItemType m → ℝ)
    (seq : AppliedModelingLib.Allocation.OptimalSequence
      (fun _ : ℕ => p) (fun _ : ℕ => fun _ : ItemType m => h))
    (hp_pos : ∀ i : ItemType m, 0 < p i)
    (hmono : Monotone h)
    (hconc : StrictDiscreteConcave h)
    (hrem : Tendsto (logRemainder h B C) atTop (nhds 0))
    (t : ItemType m) :
    Tendsto (fun N : ℕ => (seq.allocation N).count t) atTop atTop := by
  have hinc_zero : Tendsto (forwardIncrement h) atTop (nhds 0) :=
    tendsto_forwardIncrement_nhds_zero_of_log_remainder hrem
  have hweight_pos : 0 < ∑ i : ItemType m, p i :=
    weightSum_pos p hp_pos
  rw [tendsto_atTop]
  intro K
  let d : ℝ := p t * forwardIncrement h K
  have hd_pos : 0 < d := by
    dsimp [d]
    exact mul_pos (hp_pos t)
      (forwardIncrement_pos_of_monotone_strictDiscreteConcave hmono hconc K)
  let W : ℝ := ∑ i : ItemType m, p i
  have hW_pos : 0 < W := by
    simpa [W] using hweight_pos
  let eps : ℝ := d / W
  have heps_pos : 0 < eps := div_pos hd_pos hW_pos
  have hinc_small :
      ∀ᶠ q : ℕ in atTop, forwardIncrement h q < eps :=
    hinc_zero (Iio_mem_nhds heps_pos)
  obtain ⟨L, hL⟩ := eventually_atTop.1 hinc_small
  let M : ℕ := max K L + 1
  have hlargeN :
      ∀ᶠ N : ℕ in atTop, m * M < N :=
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
    (forwardIncrement_pos_of_monotone_strictDiscreteConcave hmono hconc _).le
  have htarget_increment :
      forwardIncrement h K ≤ forwardIncrement h ((seq.allocation N).count t) := by
    exact hconc.antitone (Nat.le_of_lt hcount_t_lt)
  have htarget_weighted :
      d ≤ p t * forwardIncrement h ((seq.allocation N).count t) := by
    dsimp [d]
    exact mul_le_mul_of_nonneg_left htarget_increment (hp_pos t).le
  have hweight_j : p j ≤ W := by
    simpa [W] using weight_le_weightSum p (fun i => (hp_pos i).le) j
  have hdonor_weighted_le :
      p j * forwardIncrement h ((seq.allocation N).count j - 1) ≤
        W * forwardIncrement h ((seq.allocation N).count j - 1) :=
    by
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
      (valueOfCount := fun _ : ItemType m => h) (N := N)
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

/-- A uniformly bounded count error disappears after division by the total. -/
theorem tendsto_count_div_of_abs_sub_target_le
    {a : ℕ → ℕ} {q K : ℝ}
    (hbound : ∀ N : ℕ, |((a N : ℕ) : ℝ) - (N : ℝ) * q| ≤ K) :
    Tendsto (fun N : ℕ => ((a N : ℕ) : ℝ) / (N : ℝ)) atTop (nhds q) := by
  let err : ℕ → ℝ := fun N => ((a N : ℕ) : ℝ) - (N : ℝ) * q
  have herr_lower : ∀ᶠ N : ℕ in atTop, -K ≤ err N := by
    filter_upwards with N
    exact (abs_le.mp (hbound N)).1
  have herr_upper : ∀ᶠ N : ℕ in atTop, err N ≤ K := by
    filter_upwards with N
    exact (abs_le.mp (hbound N)).2
  have herr_div : Tendsto (fun N : ℕ => err N / (N : ℝ)) atTop (nhds 0) :=
    tendsto_bdd_div_atTop_nhds_zero herr_lower herr_upper
      tendsto_natCast_atTop_atTop
  have hsum : Tendsto (fun N : ℕ => err N / (N : ℝ) + q) atTop (nhds q) := by
    simpa using herr_div.add tendsto_const_nhds
  refine hsum.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hN_ne : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  dsimp [err]
  field_simp
  ring

/-- Every rounded-competitor coordinate has an error bounded by the type count. -/
theorem abs_normalizedIntegerCompetitor_count_sub_target_le_card
    {m : ℕ} [NeZero m] (p : ItemType m → ℝ)
    (hp_pos : ∀ i, 0 < p i) (N : ℕ) (i : ItemType m) :
    |(((normalizedIntegerCompetitor p N).count i : ℕ) : ℝ) -
        (N : ℝ) * normalizedWeight p i| ≤ (Fintype.card (ItemType m) : ℝ) := by
  classical
  by_cases hi : i = (roundingAnchor : ItemType m)
  · subst i
    exact abs_normalizedIntegerCompetitor_anchor_sub_target_le_card p hp_pos N
  · have hfloor := abs_normalizedFloorCount_sub_target_le_one p hp_pos N i
    have hcard_one : (1 : ℝ) ≤ (Fintype.card (ItemType m) : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mpr (Fintype.card_pos : 0 < Fintype.card (ItemType m)))
    calc
      |(((normalizedIntegerCompetitor p N).count i : ℕ) : ℝ) -
          (N : ℝ) * normalizedWeight p i| =
          |((normalizedFloorCount p N i : ℕ) : ℝ) -
            (N : ℝ) * normalizedWeight p i| := by
              simp [normalizedIntegerCompetitor, hi]
      _ ≤ 1 := hfloor
      _ ≤ (Fintype.card (ItemType m) : ℝ) := hcard_one

/-- The internally rounded raw competitor converges to the normalized weights. -/
theorem tendsto_normalizedIntegerCompetitor_share_nhds_normalizedWeight
    {m : ℕ} [NeZero m] (p : ItemType m → ℝ)
    (hp_pos : ∀ i, 0 < p i) (i : ItemType m) :
    Tendsto
      (fun N : ℕ => AppliedModelingLib.Allocation.share (normalizedIntegerCompetitor p N) i)
      atTop (nhds (normalizedWeight p i)) := by
  have hratio : Tendsto
      (fun N : ℕ =>
        (((normalizedIntegerCompetitor p N).count i : ℕ) : ℝ) / (N : ℝ))
      atTop (nhds (normalizedWeight p i)) :=
    tendsto_count_div_of_abs_sub_target_le
      (fun N =>
        abs_normalizedIntegerCompetitor_count_sub_target_le_card p hp_pos N i)
  refine hratio.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  have htotal : AppliedModelingLib.Allocation.total (normalizedIntegerCompetitor p N) = N :=
    normalizedIntegerCompetitor_total p hp_pos N
  have htotal_ne : AppliedModelingLib.Allocation.total (normalizedIntegerCompetitor p N) ≠ 0 := by
    rw [htotal]
    exact Nat.ne_of_gt hN
  rw [AppliedModelingLib.Allocation.share_eq_div_of_total_ne_zero
    (a := normalizedIntegerCompetitor p N) (k := i) htotal_ne, htotal]

/--
Internal compact separation: a continuous objective with a strict unique
maximizer loses a uniform positive amount outside any coordinate neighborhood.
-/
theorem exists_gap_on_isCompact_of_strict_unique_max
    {κ : Type*} [Fintype κ] (s : Set (κ → ℝ))
    (objective : (κ → ℝ) → ℝ) (target : κ → ℝ)
    (hcompact : IsCompact s) (hcont : ContinuousOn objective s)
    (hstrict : ∀ x : κ → ℝ, x ∈ s → x ≠ target → objective x < objective target) :
    ∀ ε : ℝ, 0 < ε →
      ∃ η : ℝ, 0 < η ∧
        ∀ x : κ → ℝ, x ∈ s →
          (∃ k : κ, ε < |x k - target k|) →
            objective x ≤ objective target - η := by
  classical
  intro ε hε_pos
  let bad : Set (κ → ℝ) :=
    s ∩ {x : κ → ℝ | ∃ k : κ, ε ≤ |x k - target k|}
  have hclosed_coord :
      ∀ k : κ, IsClosed {x : κ → ℝ | ε ≤ |x k - target k|} := by
    intro k
    exact isClosed_le continuous_const
      ((continuous_apply k).sub continuous_const).abs
  have hclosed_far :
      IsClosed {x : κ → ℝ | ∃ k : κ, ε ≤ |x k - target k|} := by
    simpa [Set.setOf_exists] using
      (isClosed_iUnion_of_finite (fun k : κ => hclosed_coord k))
  have hcompact_bad : IsCompact bad :=
    hcompact.inter_right hclosed_far
  by_cases hbad_empty : bad = ∅
  · refine ⟨1, by norm_num, ?_⟩
    intro x hx hfar
    have hx_bad : x ∈ bad := by
      rcases hfar with ⟨k, hk⟩
      exact ⟨hx, ⟨k, le_of_lt hk⟩⟩
    rw [hbad_empty] at hx_bad
    exact hx_bad.elim
  · have hbad_nonempty : bad.Nonempty := Set.nonempty_iff_ne_empty.mpr hbad_empty
    have hcont_bad : ContinuousOn objective bad :=
      hcont.mono (by intro x hx; exact hx.1)
    rcases hcompact_bad.exists_isMaxOn hbad_nonempty hcont_bad with
      ⟨x₀, hx₀_bad, hx₀_max⟩
    have hx₀_ne : x₀ ≠ target := by
      intro hx_eq
      rcases hx₀_bad.2 with ⟨k, hk⟩
      subst x₀
      simp at hk
      linarith
    have hstrict₀ : objective x₀ < objective target :=
      hstrict x₀ hx₀_bad.1 hx₀_ne
    let η : ℝ := objective target - objective x₀
    have hη_pos : 0 < η := by
      dsimp [η]
      linarith
    refine ⟨η, hη_pos, ?_⟩
    intro x hx hfar
    have hx_bad : x ∈ bad := by
      rcases hfar with ⟨k, hk⟩
      exact ⟨hx, ⟨k, le_of_lt hk⟩⟩
    have hx_le := hx₀_max hx_bad
    have hx_le' : objective x ≤ objective x₀ := by
      simpa using hx_le
    dsimp [η]
    linarith

/-- The weighted-log objective is continuous on every strictly positive domain. -/
theorem continuousOn_weightedLogObjective_of_forall_pos
    {m : ℕ} (p : ItemType m → ℝ) :
    ContinuousOn (weightedLogObjective p)
      {x : ItemType m → ℝ | ∀ i, 0 < x i} := by
  classical
  unfold weightedLogObjective
  refine continuousOn_finset_sum Finset.univ ?_
  intro i _
  exact continuousOn_const.mul
    ((continuous_apply i).continuousOn.log
      (fun x hx => ne_of_gt (hx i)))

/-- Coordinatewise convergence to a positive profile transports through the finite log sum. -/
theorem tendsto_weightedLogObjective_of_tendsto_coordinates
    {m : ℕ} (p q : ItemType m → ℝ) (x : ℕ → ItemType m → ℝ)
    (hq_pos : ∀ i, 0 < q i)
    (hx : ∀ i, Tendsto (fun N : ℕ => x N i) atTop (nhds (q i))) :
    Tendsto (fun N : ℕ => weightedLogObjective p (x N)) atTop
      (nhds (weightedLogObjective p q)) := by
  unfold weightedLogObjective
  apply tendsto_finset_sum
  intro i _
  exact (tendsto_const_nhds.mul ((hx i).log (ne_of_gt (hq_pos i))))

/-- The internally rounded competitor attains the corrected log benchmark asymptotically. -/
theorem tendsto_weightedLogObjective_normalizedIntegerCompetitor_nhds_normalizedWeight
    {m : ℕ} [NeZero m] (p : ItemType m → ℝ)
    (hp_pos : ∀ i, 0 < p i) :
    Tendsto
      (fun N : ℕ => weightedLogObjective p
        (fun i => AppliedModelingLib.Allocation.share (normalizedIntegerCompetitor p N) i))
      atTop (nhds (weightedLogObjective p (normalizedWeight p))) := by
  exact tendsto_weightedLogObjective_of_tendsto_coordinates p (normalizedWeight p)
    (fun N i => AppliedModelingLib.Allocation.share (normalizedIntegerCompetitor p N) i)
    (fun i => normalizedWeight_pos p hp_pos i)
    (fun i => tendsto_normalizedIntegerCompetitor_share_nhds_normalizedWeight p hp_pos i)

/--
Raw finite optimality forces the optimizer's log objective arbitrarily close
to the corrected maximum from below.  The comparison allocation, its total,
its coordinate growth, and the asymptotic expansion are all constructed here.
-/
theorem eventually_weightedLogObjective_target_sub_lt_optimal
    {m : ℕ} [NeZero m] {B C : ℝ} {h : ℕ → ℝ}
    (p : ItemType m → ℝ)
    (seq : AppliedModelingLib.Allocation.OptimalSequence
      (fun _ : ℕ => p) (fun _ : ℕ => fun _ : ItemType m => h))
    (hp_pos : ∀ i : ItemType m, 0 < p i)
    (hmono : Monotone h) (hconc : StrictDiscreteConcave h)
    (hB_pos : 0 < B)
    (hrem : Tendsto (logRemainder h B C) atTop (nhds 0))
    {δ : ℝ} (hδ_pos : 0 < δ) :
    ∀ᶠ N : ℕ in atTop,
      weightedLogObjective p (normalizedWeight p) - δ <
        weightedLogObjective p
          (fun i => AppliedModelingLib.Allocation.share (seq.allocation N) i) := by
  let a : ℕ → CountAllocation m := fun N => seq.allocation N
  let b : ℕ → CountAllocation m := fun N => normalizedIntegerCompetitor p N
  let La : ℕ → ℝ := fun N => weightedLogObjective p
    (fun i => AppliedModelingLib.Allocation.share (a N) i)
  let Lb : ℕ → ℝ := fun N => weightedLogObjective p
    (fun i => AppliedModelingLib.Allocation.share (b N) i)
  let Lq : ℝ := weightedLogObjective p (normalizedWeight p)
  have ha_total : ∀ N : ℕ, AppliedModelingLib.Allocation.total (a N) = N := by
    intro N
    exact (seq.optimal N).1
  have hb_total : ∀ N : ℕ, AppliedModelingLib.Allocation.total (b N) = N := by
    intro N
    exact normalizedIntegerCompetitor_total p hp_pos N
  have ha_top : ∀ i : ItemType m,
      Tendsto (fun N : ℕ => (a N).count i) atTop atTop := by
    intro i
    exact tendsto_optimalAllocation_count_atTop_of_log_remainder
      p seq hp_pos hmono hconc hrem i
  have hb_top : ∀ i : ItemType m,
      Tendsto (fun N : ℕ => (b N).count i) atTop atTop := by
    intro i
    exact tendsto_normalizedIntegerCompetitor_count_atTop p hp_pos i
  have hraw : Tendsto
      (fun N : ℕ =>
        (AppliedModelingLib.Allocation.objective (a N) p (fun _ : ItemType m => h) -
          AppliedModelingLib.Allocation.objective (b N) p (fun _ : ItemType m => h)) -
          B * (La N - Lb N))
      atTop (nhds 0) := by
    simpa [a, b, La, Lb] using
      tendsto_rawObjective_sub_weightedLogComparison_nhds_zero
        p a b ha_total hb_total ha_top hb_top hrem
  have hbenchmark : Tendsto Lb atTop (nhds Lq) := by
    simpa [b, Lb, Lq] using
      tendsto_weightedLogObjective_normalizedIntegerCompetitor_nhds_normalizedWeight
        p hp_pos
  let δthird : ℝ := δ / 3
  have hδthird_pos : 0 < δthird := by
    dsimp [δthird]
    positivity
  have hbenchmark_lower :
      ∀ᶠ N : ℕ in atTop, Lq - δthird < Lb N :=
    hbenchmark (Ioi_mem_nhds (sub_lt_self Lq hδthird_pos))
  have hraw_upper :
      ∀ᶠ N : ℕ in atTop,
        (AppliedModelingLib.Allocation.objective (a N) p (fun _ : ItemType m => h) -
          AppliedModelingLib.Allocation.objective (b N) p (fun _ : ItemType m => h)) -
            B * (La N - Lb N) < B * δthird :=
    hraw (Iio_mem_nhds (mul_pos hB_pos hδthird_pos))
  filter_upwards [hbenchmark_lower, hraw_upper] with N hbenchN hrawN
  have hopt :
      AppliedModelingLib.Allocation.objective (b N) p (fun _ : ItemType m => h) ≤
        AppliedModelingLib.Allocation.objective (a N) p (fun _ : ItemType m => h) :=
    (seq.optimal N).2 (b N) (hb_total N)
  have hmul : B * (-(La N - Lb N)) < B * δthird := by
    nlinarith
  have hdiff : -δthird < La N - Lb N := by
    have hneg : -(La N - Lb N) < δthird := by
      nlinarith
    linarith
  dsimp [La, Lq] at hbenchN hdiff ⊢
  dsimp [δthird] at hbenchN hdiff
  linarith

/--
The raw log-objective comparison yields an explicit eventual positive floor on
every optimizer share.  This is derived before, and used only to justify, the
internal compact positive-domain separation.
-/
theorem eventually_optimalAllocation_share_ge_log_floor
    {m : ℕ} [NeZero m] {B C : ℝ} {h : ℕ → ℝ}
    (p : ItemType m → ℝ)
    (seq : AppliedModelingLib.Allocation.OptimalSequence
      (fun _ : ℕ => p) (fun _ : ℕ => fun _ : ItemType m => h))
    (hp_pos : ∀ i : ItemType m, 0 < p i)
    (hmono : Monotone h) (hconc : StrictDiscreteConcave h)
    (hB_pos : 0 < B)
    (hrem : Tendsto (logRemainder h B C) atTop (nhds 0)) :
    ∀ᶠ N : ℕ in atTop, ∀ i : ItemType m,
      Real.exp
          ((weightedLogObjective p (normalizedWeight p) - 1) / p i) ≤
        AppliedModelingLib.Allocation.share (seq.allocation N) i := by
  let Lq : ℝ := weightedLogObjective p (normalizedWeight p)
  have hL : ∀ᶠ N : ℕ in atTop,
      Lq - 1 < weightedLogObjective p
        (fun i => AppliedModelingLib.Allocation.share (seq.allocation N) i) := by
    simpa [Lq] using
      eventually_weightedLogObjective_target_sub_lt_optimal
        p seq hp_pos hmono hconc hB_pos hrem (by norm_num : (0 : ℝ) < 1)
  have hcount_top : ∀ i : ItemType m,
      Tendsto (fun N : ℕ => (seq.allocation N).count i) atTop atTop := by
    intro i
    exact tendsto_optimalAllocation_count_atTop_of_log_remainder
      p seq hp_pos hmono hconc hrem i
  have hcount_pos : ∀ᶠ N : ℕ in atTop, ∀ i : ItemType m,
      0 < (seq.allocation N).count i := by
    refine Filter.eventually_all.2 ?_
    intro i
    exact (hcount_top i).eventually_gt_atTop 0
  filter_upwards [hL, hcount_pos, eventually_gt_atTop 0] with N hLN hcountN hN
  intro i
  let x : ItemType m → ℝ :=
    fun j => AppliedModelingLib.Allocation.share (seq.allocation N) j
  have htotal : AppliedModelingLib.Allocation.total (seq.allocation N) = N :=
    (seq.optimal N).1
  have htotal_ne : AppliedModelingLib.Allocation.total (seq.allocation N) ≠ 0 := by
    rw [htotal]
    exact Nat.ne_of_gt hN
  have hx_simplex : x ∈ stdSimplex ℝ (ItemType m) := by
    constructor
    · intro j
      exact AppliedModelingLib.Allocation.share_nonneg (a := seq.allocation N) (k := j)
    · dsimp [x]
      exact AppliedModelingLib.Allocation.sum_share_eq_one_of_total_ne_zero
        (a := seq.allocation N) htotal_ne
  have hx_pos : ∀ j : ItemType m, 0 < x j := by
    intro j
    dsimp [x]
    exact AppliedModelingLib.Allocation.share_pos_of_count_pos
      (a := seq.allocation N) j (hcountN j)
  have hterm_nonpos : ∀ j : ItemType m, p j * Real.log (x j) ≤ 0 := by
    intro j
    apply mul_nonpos_of_nonneg_of_nonpos (hp_pos j).le
    exact Real.log_nonpos (hx_simplex.1 j)
      (mem_Icc_of_mem_stdSimplex hx_simplex j).2
  have hsum_erase_nonpos :
      (∑ j ∈ Finset.univ.erase i, p j * Real.log (x j)) ≤ 0 :=
    Finset.sum_nonpos (fun j _ => hterm_nonpos j)
  have hsum_erase :
      (∑ j ∈ Finset.univ.erase i, p j * Real.log (x j)) +
          p i * Real.log (x i) = weightedLogObjective p x := by
    unfold weightedLogObjective
    exact Finset.sum_erase_add Finset.univ
      (fun j => p j * Real.log (x j)) (Finset.mem_univ i)
  have hcoord_upper : weightedLogObjective p x ≤ p i * Real.log (x i) := by
    linarith
  have hcoord_lower : Lq - 1 ≤ p i * Real.log (x i) := by
    exact le_trans (le_of_lt hLN) hcoord_upper
  have hlog_lower : (Lq - 1) / p i ≤ Real.log (x i) :=
    (div_le_iff₀ (hp_pos i)).mpr (by simpa [mul_comm] using hcoord_lower)
  have hexp : Real.exp ((Lq - 1) / p i) ≤ x i := by
    calc
      Real.exp ((Lq - 1) / p i) ≤ Real.exp (Real.log (x i)) :=
        Real.exp_le_exp.mpr hlog_lower
      _ = x i := Real.exp_log (hx_pos i)
  simpa [Lq, x] using hexp

/--
Corrected generic Lemma D.1(iii).  For strictly positive raw weights, the
literal fixed-total optimizer converges to `p / sum p`.  The source's
``minimum'' is corrected to the unique log-objective maximum; monotonicity and
the source's discrete strict concavity are both explicit.
-/
theorem corrected_lemmaD1_iii_normalized_optimizer_shares_of_log_remainder
    {m : ℕ} [NeZero m] {B C : ℝ} {h : ℕ → ℝ}
    (p : ItemType m → ℝ)
    (seq : AppliedModelingLib.Allocation.OptimalSequence
      (fun _ : ℕ => p) (fun _ : ℕ => fun _ : ItemType m => h))
    (hp_pos : ∀ i : ItemType m, 0 < p i)
    (hmono : Monotone h) (hconc : StrictDiscreteConcave h)
    (hB_pos : 0 < B)
    (hrem : Tendsto (logRemainder h B C) atTop (nhds 0)) :
    seq.toSequence.ConvergesToProfile (normalizedWeight p) := by
  classical
  let Lq : ℝ := weightedLogObjective p (normalizedWeight p)
  let lower : ItemType m → ℝ :=
    fun i => Real.exp ((Lq - 1) / p i)
  let s : Set (ItemType m → ℝ) :=
    stdSimplex ℝ (ItemType m) ∩ {x : ItemType m → ℝ | ∀ i, lower i ≤ x i}
  have hlower_pos : ∀ i : ItemType m, 0 < lower i := by
    intro i
    exact Real.exp_pos _
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
    have hx_lower : ∀ i : ItemType m, lower i ≤ x i := hx.2
    exact lt_of_lt_of_le (hlower_pos i) (hx_lower i)
  have hs_cont : ContinuousOn (weightedLogObjective p) s :=
    (continuousOn_weightedLogObjective_of_forall_pos p).mono
      (fun x hx => hs_pos x hx)
  have hs_strict :
      ∀ x : ItemType m → ℝ, x ∈ s → x ≠ normalizedWeight p →
        weightedLogObjective p x < weightedLogObjective p (normalizedWeight p) := by
    intro x hx hx_ne
    exact weightedLogObjective_lt_normalizedWeight_of_ne p x hp_pos
      (hs_pos x hx) hx.1.2 hx_ne
  have hfloor : ∀ᶠ N : ℕ in atTop, ∀ i : ItemType m,
      lower i ≤ AppliedModelingLib.Allocation.share (seq.allocation N) i := by
    simpa [lower, Lq] using
      eventually_optimalAllocation_share_ge_log_floor
        p seq hp_pos hmono hconc hB_pos hrem
  have hactual_mem : ∀ᶠ N : ℕ in atTop,
      (fun i => AppliedModelingLib.Allocation.share (seq.allocation N) i) ∈ s := by
    filter_upwards [hfloor, eventually_gt_atTop 0] with N hfloorN hN
    constructor
    · constructor
      · intro i
        exact AppliedModelingLib.Allocation.share_nonneg (a := seq.allocation N) (k := i)
      · exact AppliedModelingLib.Allocation.sum_share_eq_one_of_total_ne_zero
          (a := seq.allocation N) (by
            rw [(seq.optimal N).1]
            exact Nat.ne_of_gt hN)
    · exact hfloorN
  intro t
  change Tendsto
    (fun N : ℕ => AppliedModelingLib.Allocation.share (seq.allocation N) t)
    atTop (nhds (normalizedWeight p t))
  rw [Metric.tendsto_nhds]
  intro ε hε_pos
  let εhalf : ℝ := ε / 2
  have hεhalf_pos : 0 < εhalf := by
    dsimp [εhalf]
    positivity
  obtain ⟨η, hη_pos, hseparate⟩ :=
    exists_gap_on_isCompact_of_strict_unique_max s (weightedLogObjective p)
      (normalizedWeight p) hscompact hs_cont hs_strict εhalf hεhalf_pos
  have hobjective_lower : ∀ᶠ N : ℕ in atTop,
      Lq - η < weightedLogObjective p
        (fun i => AppliedModelingLib.Allocation.share (seq.allocation N) i) := by
    simpa [Lq] using
      eventually_weightedLogObjective_target_sub_lt_optimal
        p seq hp_pos hmono hconc hB_pos hrem hη_pos
  filter_upwards [hactual_mem, hobjective_lower] with N hmemN hobjN
  have hnot_far :
      ¬ εhalf <
        |AppliedModelingLib.Allocation.share (seq.allocation N) t - normalizedWeight p t| := by
    intro hfar
    have hgapN := hseparate
      (fun i => AppliedModelingLib.Allocation.share (seq.allocation N) i) hmemN ⟨t, hfar⟩
    exact (not_lt_of_ge hgapN) hobjN
  have habs_le :
      |AppliedModelingLib.Allocation.share (seq.allocation N) t - normalizedWeight p t| ≤ εhalf :=
    le_of_not_gt hnot_far
  have habs_lt :
      |AppliedModelingLib.Allocation.share (seq.allocation N) t - normalizedWeight p t| < ε :=
    lt_of_le_of_lt habs_le (by dsimp [εhalf]; linarith)
  simpa [Real.dist_eq] using habs_lt

/--
Source-probability wrapper for corrected Lemma D.1(iii).  When the raw
weights are explicitly normalized probabilities, the corrected target
`p / sum p` is definitionally the source-shaped profile `p`.
-/
theorem corrected_lemmaD1_iii_probability_optimizer_shares_of_log_remainder
    {m : ℕ} [NeZero m] {B C : ℝ} {h : ℕ → ℝ}
    (p : ItemType m → ℝ)
    (seq : AppliedModelingLib.Allocation.OptimalSequence
      (fun _ : ℕ => p) (fun _ : ℕ => fun _ : ItemType m => h))
    (hp_pos : ∀ i : ItemType m, 0 < p i)
    (hsum : (∑ i : ItemType m, p i) = 1)
    (hmono : Monotone h) (hconc : StrictDiscreteConcave h)
    (hB_pos : 0 < B)
    (hrem : Tendsto (logRemainder h B C) atTop (nhds 0)) :
    seq.toSequence.ConvergesToProfile p := by
  have hnormalized : normalizedWeight p = p := by
    funext i
    simp [normalizedWeight, hsum]
  simpa [hnormalized] using
    corrected_lemmaD1_iii_normalized_optimizer_shares_of_log_remainder
      p seq hp_pos hmono hconc hB_pos hrem

end AppendixD1GenericIII
end PRPKG24AccuracyDiversity
