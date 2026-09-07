import AppliedModelingLib.Foundations.Probability.FiniteSupportMGF
import AppliedModelingLib.Foundations.Probability.FiniteProductTernaryCounts
import AppliedModelingLib.Foundations.Probability.LargeDeviations
import AppliedModelingLib.Foundations.Math.BinomialBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.ENNReal.BigOperators

open scoped BigOperators
open Filter

namespace AppliedModelingLib
namespace Probability

noncomputable section

/-!
# Finite IID Large-Deviation Bounds

Reusable finite iid Chernoff infrastructure for paper proofs that reduce
pairwise learning mistakes to sample sums of finite score gaps.

This file deliberately starts with upper-bound certificates. Exact Cramer
lower bounds and compact/Laplace-principle results belong in later layers.
-/

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Sum of a real-valued score over a finite iid sample. -/
def finiteIidScoreSum {ι : Type*} [Fintype ι]
    (score : α → ℝ) (sample : ι → α) : ℝ :=
  ∑ i : ι, score (sample i)

/-- The finite-sample sum of the complementary score `1 - score`. -/
theorem finiteIidScoreSum_one_sub_eq_card_sub {ι : Type*} [Fintype ι]
    (score : α → ℝ) (sample : ι → α) :
    finiteIidScoreSum (fun a : α => 1 - score a) sample =
      (Fintype.card ι : ℝ) - finiteIidScoreSum score sample := by
  unfold finiteIidScoreSum
  rw [Finset.sum_sub_distrib]
  simp [Finset.sum_const, nsmul_eq_mul]

/-- Empirical count of a value in a finite sample. -/
def empiricalCount {ι : Type*} [Fintype ι]
    (sample : ι → α) (a : α) : ℕ :=
  (successIndexSet (fun x : α => x = a) sample).card

/-- A finite sample sum can be regrouped by empirical counts of signal values. -/
theorem finiteIidScoreSum_eq_sum_empiricalCount
    {ι : Type*} [Fintype ι]
    (score : α → ℝ) (sample : ι → α) :
    finiteIidScoreSum score sample =
      ∑ a : α, (empiricalCount sample a : ℝ) * score a := by
  classical
  unfold finiteIidScoreSum empiricalCount
  calc
    ∑ i : ι, score (sample i)
        =
        ∑ i : ι, ∑ a : α,
          (if sample i = a then score a else (0 : ℝ)) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          have hsingle :
              (∑ a : α, if sample i = a then score a else (0 : ℝ)) =
                score (sample i) := by
            simp
          rw [hsingle]
    _ =
        ∑ a : α, ∑ i : ι,
          (if sample i = a then score a else (0 : ℝ)) := by
          exact Finset.sum_comm
    _ =
        ∑ a : α,
          ((successIndexSet (fun x : α => x = a) sample).card : ℝ) *
            score a := by
          refine Finset.sum_congr rfl ?_
          intro a _
          calc
            ∑ i : ι, (if sample i = a then score a else (0 : ℝ))
                =
                (((Finset.univ : Finset ι).filter
                    (fun i => sample i = a)).sum (fun _i => score a)) := by
                  rw [← Finset.sum_filter]
            _ =
                ((successIndexSet (fun x : α => x = a) sample).card : ℝ) *
                  score a := by
                  simp [successIndexSet, Finset.sum_const, nsmul_eq_mul]

/-- Left-tail probability for an iid finite sample of size `n`. -/
def finiteIidScoreLeftTailProb
    (μ : PMF α) (score : α → ℝ) (threshold : ℝ) (n : ℕ) : ℝ :=
  pmfProb (pmfProduct (Fin n) α μ)
    (fun sample : Fin n → α => finiteIidScoreSum score sample ≤ threshold)

/--
If every positive-mass atom has nonnegative score, the nonpositive iid
left-tail is exactly the event that every draw has score zero.  Zero-mass
negative atoms do not matter because every product sample using one has zero
mass.
-/
theorem finiteIidScoreLeftTailProb_eq_zero_score_prob_pow_of_support_nonneg
    (μ : PMF α) (score : α → ℝ)
    (hsupport : ∀ a, 0 < (μ a).toReal → 0 ≤ score a)
    (n : ℕ) :
    finiteIidScoreLeftTailProb μ score 0 n =
      (pmfProb μ (fun a => score a = 0)) ^ n := by
  classical
  let μn := pmfProduct (Fin n) α μ
  let leftEvent : (Fin n → α) → Prop :=
    fun sample => finiteIidScoreSum score sample ≤ 0
  let zeroEvent : (Fin n → α) → Prop :=
    fun sample => ∀ i : Fin n, score (sample i) = 0
  have hzero_imp_left : ∀ sample, zeroEvent sample → leftEvent sample := by
    intro sample hzero
    have hsum_zero :
        finiteIidScoreSum score sample = 0 := by
      dsimp [finiteIidScoreSum]
      calc
        ∑ i : Fin n, score (sample i)
            = ∑ _i : Fin n, (0 : ℝ) := by
              refine Finset.sum_congr rfl ?_
              intro i _
              exact hzero i
        _ = 0 := by simp
    exact le_of_eq hsum_zero
  have hsplit :=
    pmfProb_eq_add_diff_of_imp μn zeroEvent leftEvent hzero_imp_left
  have hres_zero :
      pmfProb μn (fun sample => leftEvent sample ∧ ¬ zeroEvent sample) = 0 := by
    refine pmfProb_eq_zero_of_no_mass μn
      (fun sample => leftEvent sample ∧ ¬ zeroEvent sample) ?_
    intro sample hsample
    rw [pmfProduct_apply_toReal]
    by_contra hprod_ne
    have hmass_pos : ∀ i : Fin n, 0 < (μ (sample i)).toReal := by
      intro i
      have hne : (μ (sample i)).toReal ≠ 0 := by
        exact (Finset.prod_ne_zero_iff.mp hprod_ne) i (Finset.mem_univ i)
      exact lt_of_le_of_ne ENNReal.toReal_nonneg hne.symm
    have hscore_nonneg : ∀ i : Fin n, 0 ≤ score (sample i) := by
      intro i
      exact hsupport (sample i) (hmass_pos i)
    have hexists_pos : ∃ i : Fin n, 0 < score (sample i) := by
      rcases not_forall.mp hsample.2 with ⟨i, hne_zero⟩
      exact ⟨i, lt_of_le_of_ne (hscore_nonneg i) (Ne.symm hne_zero)⟩
    have hsum_pos : 0 < finiteIidScoreSum score sample := by
      dsimp [finiteIidScoreSum]
      refine Finset.sum_pos' ?_ ?_
      · intro i _
        exact hscore_nonneg i
      · rcases hexists_pos with ⟨i, hpos⟩
        exact ⟨i, Finset.mem_univ i, hpos⟩
    exact not_lt_of_ge hsample.1 hsum_pos
  have hzero_prob :
      pmfProb μn zeroEvent =
        (pmfProb μ (fun a => score a = 0)) ^ n := by
    have hpoint : ∀ sample : Fin n → α,
        (pmfProduct (Fin n) α μ sample).toReal *
            (if ∀ i : Fin n, score (sample i) = 0 then (1 : ℝ) else 0) =
          ∏ i : Fin n,
            ((μ (sample i)).toReal *
              (if score (sample i) = 0 then (1 : ℝ) else 0)) := by
      intro sample
      by_cases hall : ∀ i : Fin n, score (sample i) = 0
      · simp [hall]
      · rcases not_forall.mp hall with ⟨i, hi⟩
        have hprod_zero :
            ∏ j : Fin n,
                (if score (sample j) = 0 then
                  (μ (sample j)).toReal else 0) = 0 := by
          rw [Finset.prod_eq_zero (Finset.mem_univ i)]
          simp [hi]
        simp [hall, hprod_zero]
    unfold μn zeroEvent pmfProb pmfExp
    calc
      ∑ sample : Fin n → α,
          (pmfProduct (Fin n) α μ sample).toReal *
            (if ∀ i : Fin n, score (sample i) = 0 then (1 : ℝ) else 0)
          =
          ∑ sample : Fin n → α,
            ∏ i : Fin n,
              ((μ (sample i)).toReal *
                (if score (sample i) = 0 then (1 : ℝ) else 0)) := by
            exact Finset.sum_congr rfl (fun sample _ => hpoint sample)
      _ =
          ∏ _i : Fin n,
            ∑ a : α,
              ((μ a).toReal *
                (if score a = 0 then (1 : ℝ) else 0)) := by
            symm
            simpa using
              (Finset.prod_univ_sum
                (t := fun _i : Fin n => (Finset.univ : Finset α))
                (f := fun _i a => (μ a).toReal *
                  (if score a = 0 then (1 : ℝ) else 0)))
      _ =
          (pmfProb μ (fun a => score a = 0)) ^ n := by
            simp [pmfProb, pmfExp, Finset.prod_const]
  calc
    finiteIidScoreLeftTailProb μ score 0 n
        = pmfProb μn leftEvent := by
            rfl
    _ = pmfProb μn zeroEvent +
          pmfProb μn (fun sample => leftEvent sample ∧ ¬ zeroEvent sample) :=
            hsplit
    _ = (pmfProb μ (fun a => score a = 0)) ^ n := by
            rw [hres_zero, add_zero, hzero_prob]

/--
One-sided finite-support exact-rate certificate for the finite real boundary
case: if all positive-mass scores are nonnegative and the zero-score atom has
probability `pZero > 0`, the nonpositive left-tail is exactly `pZero^n` and
has rate `-log pZero`.
-/
theorem finiteIidScoreLeftTail_exponentialRateCertificate_of_support_nonneg_zero_prob
    (μ : PMF α) (score : α → ℝ)
    (hsupport : ∀ a, 0 < (μ a).toReal → 0 ≤ score a)
    {pZero : ℝ}
    (hpZero :
      pmfProb μ (fun a => score a = 0) = pZero)
    (hpZero_pos : 0 < pZero) :
    ExponentialRateCertificate
      (fun n : ℕ => finiteIidScoreLeftTailProb μ score 0 n)
      (-Real.log pZero) := by
  let pure : ℕ → ℝ :=
    fun n => 1 * Real.exp (-(n : ℝ) * (-Real.log pZero))
  have hp_pow : ∀ n : ℕ, pZero ^ n = pure n := by
    intro n
    dsimp [pure]
    calc
      pZero ^ n = (Real.exp (Real.log pZero)) ^ n := by
        rw [Real.exp_log hpZero_pos]
      _ = Real.exp ((n : ℝ) * Real.log pZero) := by
        rw [Real.exp_nat_mul]
      _ = 1 * Real.exp (-(n : ℝ) * (-Real.log pZero)) := by
        ring_nf
  have htail : ∀ n : ℕ,
      finiteIidScoreLeftTailProb μ score 0 n = pure n := by
    intro n
    rw [finiteIidScoreLeftTailProb_eq_zero_score_prob_pow_of_support_nonneg
      μ score hsupport n, hpZero, hp_pow n]
  have hpure_cert :
      ExponentialRateCertificate pure (-Real.log pZero) := by
    simpa [pure] using
      exponentialRateCertificate_const_mul_exp
        (C := 1) (rate := -Real.log pZero) (by norm_num : (0 : ℝ) < 1)
  refine
    { eventually_pos := ?_
      has_rate := ?_ }
  · filter_upwards [hpure_cert.eventually_pos] with n hpos
    simpa [htail n] using hpos
  · refine hpure_cert.has_rate.congr' ?_
    filter_upwards with n
    simp [logDecay, htail n]

/--
If every positive-mass atom has strictly positive score, the nonpositive
finite iid left-tail is eventually empty.  The `n = 0` sample still has
empty-sum score zero, so the statement is correctly eventual rather than
pointwise.
-/
theorem finiteIidScoreLeftTailProb_eventually_zero_of_support_pos
    (μ : PMF α) (score : α → ℝ)
    (hsupport : ∀ a, 0 < (μ a).toReal → 0 < score a) :
    ∀ᶠ n in atTop, finiteIidScoreLeftTailProb μ score 0 n = 0 := by
  classical
  have hsupport_nonneg :
      ∀ a, 0 < (μ a).toReal → 0 ≤ score a := by
    intro a hmass
    exact (hsupport a hmass).le
  have hzero_prob : pmfProb μ (fun a => score a = 0) = 0 := by
    refine pmfProb_eq_zero_of_no_mass μ (fun a => score a = 0) ?_
    intro a hscore_zero
    by_cases hmass : 0 < (μ a).toReal
    · have hscore_pos := hsupport a hmass
      exfalso
      exact (lt_irrefl (0 : ℝ)) (by simpa [hscore_zero] using hscore_pos)
    · exact le_antisymm (le_of_not_gt hmass) ENNReal.toReal_nonneg
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [finiteIidScoreLeftTailProb_eq_zero_score_prob_pow_of_support_nonneg
    μ score hsupport_nonneg n, hzero_prob]
  have hn_pos : 0 < n := lt_of_lt_of_le zero_lt_one hn
  simpa using (zero_pow (Nat.ne_of_gt hn_pos) : (0 : ℝ) ^ n = 0)

/--
Strictly positive finite score support gives an eventually empty iid left-tail,
so it satisfies an exponential upper bound at every finite target rate.
-/
theorem finiteIidScoreLeftTail_hasExpUpperBoundWithConst_of_support_pos
    (μ : PMF α) (score : α → ℝ)
    (hsupport : ∀ a, 0 < (μ a).toReal → 0 < score a)
    (targetRate : ℝ) :
    HasExpUpperBoundWithConst
      (fun n : ℕ => finiteIidScoreLeftTailProb μ score 0 n)
      targetRate :=
  HasExpUpperBoundWithConst.of_eventually_zero
    (finiteIidScoreLeftTailProb_eventually_zero_of_support_pos μ score hsupport)

/--
Exponential tilt of a finite score law at dual parameter `z`.

The tilted one-voter mass is proportional to
`μ(a) * exp (z * score a)`.  This is the standard change-of-measure law used
by finite-support Cramer lower bounds.
-/
noncomputable def finiteExponentialTilt
    (μ : PMF α) (score : α → ℝ) (z : ℝ) : PMF α :=
  PMF.ofFintype
    (fun a : α =>
      ENNReal.ofReal
        ((μ a).toReal * Real.exp (z * score a) / finiteMGF μ score z))
    (by
      classical
      have hterm_nonneg :
          ∀ a : α,
            0 ≤ (μ a).toReal * Real.exp (z * score a) /
              finiteMGF μ score z := by
        intro a
        exact div_nonneg
          (mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le)
          (finiteMGF_pos μ score z).le
      have hsum_real :
          (∑ a : α,
              (μ a).toReal * Real.exp (z * score a) /
                finiteMGF μ score z) = 1 := by
        rw [← Finset.sum_div]
        field_simp [(finiteMGF_pos μ score z).ne']
        rfl
      calc
        (∑ a : α,
            ENNReal.ofReal
              ((μ a).toReal * Real.exp (z * score a) /
                finiteMGF μ score z))
            =
            ENNReal.ofReal
              (∑ a : α,
                (μ a).toReal * Real.exp (z * score a) /
                  finiteMGF μ score z) := by
              symm
              exact ENNReal.ofReal_sum_of_nonneg
                (s := (Finset.univ : Finset α))
                (f := fun a : α =>
                  (μ a).toReal * Real.exp (z * score a) /
                    finiteMGF μ score z)
                (by intro a _; exact hterm_nonneg a)
        _ = 1 := by
              rw [hsum_real]
              norm_num)

@[simp]
theorem finiteExponentialTilt_apply_toReal
    (μ : PMF α) (score : α → ℝ) (z : ℝ) (a : α) :
    (finiteExponentialTilt μ score z a).toReal =
      (μ a).toReal * Real.exp (z * score a) / finiteMGF μ score z := by
  unfold finiteExponentialTilt
  rw [PMF.ofFintype_apply]
  exact ENNReal.toReal_ofReal
    (div_nonneg
      (mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le)
      (finiteMGF_pos μ score z).le)

theorem finiteExponentialTilt_apply_toReal_mul_normalizer
    (μ : PMF α) (score : α → ℝ) (z : ℝ) (a : α) :
    (finiteExponentialTilt μ score z a).toReal *
        finiteMGF μ score z * Real.exp (-(z * score a)) =
      (μ a).toReal := by
  rw [finiteExponentialTilt_apply_toReal]
  field_simp [(finiteMGF_pos μ score z).ne']
  rw [mul_assoc, ← Real.exp_add]
  ring_nf
  simp

/-- Exponential tilting preserves exactly the positive support of the base law. -/
theorem finiteExponentialTilt_apply_toReal_pos_iff
    (μ : PMF α) (score : α → ℝ) (z : ℝ) (a : α) :
    0 < (finiteExponentialTilt μ score z a).toReal ↔
      0 < (μ a).toReal := by
  rw [finiteExponentialTilt_apply_toReal]
  constructor
  · intro h
    by_contra hnot
    have hzero : (μ a).toReal = 0 :=
      le_antisymm (le_of_not_gt hnot) ENNReal.toReal_nonneg
    simp [hzero] at h
  · intro h
    exact div_pos (mul_pos h (Real.exp_pos _)) (finiteMGF_pos μ score z)

/--
The expected score under the exponential tilt is the finite log-MGF derivative
numerator divided by the finite MGF.
-/
theorem pmfExp_finiteExponentialTilt_eq
    (μ : PMF α) (score : α → ℝ) (z : ℝ) :
    pmfExp (finiteExponentialTilt μ score z) score =
      (∑ a : α,
        (μ a).toReal * (score a * Real.exp (z * score a))) /
        finiteMGF μ score z := by
  unfold pmfExp
  calc
    ∑ a : α, (finiteExponentialTilt μ score z a).toReal * score a
        =
        ∑ a : α,
          ((μ a).toReal * Real.exp (z * score a) /
              finiteMGF μ score z) * score a := by
          refine Finset.sum_congr rfl ?_
          intro a _
          rw [finiteExponentialTilt_apply_toReal]
    _ =
        ∑ a : α,
          ((μ a).toReal * (score a * Real.exp (z * score a))) /
            finiteMGF μ score z := by
          refine Finset.sum_congr rfl ?_
          intro a _
          ring
    _ =
        (∑ a : α,
          (μ a).toReal * (score a * Real.exp (z * score a))) /
            finiteMGF μ score z := by
          rw [Finset.sum_div]

/-- A stationary exponential tilt has zero tilted expected score. -/
theorem pmfExp_finiteExponentialTilt_eq_zero_of_stationary
    (μ : PMF α) (score : α → ℝ) {z : ℝ}
    (hstationary :
      (∑ a : α,
        (μ a).toReal * (score a * Real.exp (z * score a))) = 0) :
    pmfExp (finiteExponentialTilt μ score z) score = 0 := by
  rw [pmfExp_finiteExponentialTilt_eq, hstationary]
  simp

/--
Iid product mass under the original law, expressed through the exponentially
tilted product law.
-/
theorem pmfProduct_apply_toReal_eq_tilted_mul_mgf_pow_exp
    (μ : PMF α) (score : α → ℝ) (z : ℝ) {n : ℕ}
    (sample : Fin n → α) :
    (pmfProduct (Fin n) α μ sample).toReal =
      (pmfProduct (Fin n) α (finiteExponentialTilt μ score z) sample).toReal *
        (finiteMGF μ score z) ^ n *
          Real.exp (-(z * finiteIidScoreSum score sample)) := by
  classical
  rw [pmfProduct_apply_toReal, pmfProduct_apply_toReal]
  calc
    ∏ i : Fin n, (μ (sample i)).toReal
        =
        ∏ i : Fin n,
          ((finiteExponentialTilt μ score z (sample i)).toReal *
            finiteMGF μ score z * Real.exp (-(z * score (sample i)))) := by
          refine Finset.prod_congr rfl ?_
          intro i _
          rw [finiteExponentialTilt_apply_toReal_mul_normalizer]
    _ =
        (∏ i : Fin n,
            (finiteExponentialTilt μ score z (sample i)).toReal) *
          (∏ i : Fin n, finiteMGF μ score z) *
            (∏ i : Fin n, Real.exp (-(z * score (sample i)))) := by
          rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    _ =
        (∏ i : Fin n,
            (finiteExponentialTilt μ score z (sample i)).toReal) *
          (finiteMGF μ score z) ^ n *
            Real.exp (∑ i : Fin n, -(z * score (sample i))) := by
          rw [Finset.prod_const]
          rw [← Real.exp_sum]
          simp
    _ =
        (∏ i : Fin n,
            (finiteExponentialTilt μ score z (sample i)).toReal) *
          (finiteMGF μ score z) ^ n *
            Real.exp (-(z * finiteIidScoreSum score sample)) := by
          congr 2
          simp [finiteIidScoreSum, Finset.mul_sum]

/--
Exponential-tilting lower-bound bridge.  If a sample lies in a bounded
left-tail window under the tilted law, its original-law mass is at least the
tilted mass times `finiteMGF μ score z ^ n`, up to the fixed factor
`exp (z * windowBound)`.
-/
theorem finiteIidScoreLeftTailProb_ge_tilted_window
    (μ : PMF α) (score : α → ℝ) {z windowBound : ℝ}
    (hz : z ≤ 0) (n : ℕ) :
    (finiteMGF μ score z) ^ n * Real.exp (z * windowBound) *
        pmfProb
          (pmfProduct (Fin n) α (finiteExponentialTilt μ score z))
          (fun sample : Fin n → α =>
            -windowBound ≤ finiteIidScoreSum score sample ∧
              finiteIidScoreSum score sample ≤ 0) ≤
      finiteIidScoreLeftTailProb μ score 0 n := by
  classical
  let tilt := finiteExponentialTilt μ score z
  let M := finiteMGF μ score z
  let window : (Fin n → α) → Prop := fun sample =>
    -windowBound ≤ finiteIidScoreSum score sample ∧
      finiteIidScoreSum score sample ≤ 0
  let tail : (Fin n → α) → Prop := fun sample =>
    finiteIidScoreSum score sample ≤ 0
  unfold finiteIidScoreLeftTailProb pmfProb pmfExp
  calc
    M ^ n * Real.exp (z * windowBound) *
        (∑ sample : Fin n → α,
          (pmfProduct (Fin n) α tilt sample).toReal *
            if window sample then 1 else 0)
        =
        ∑ sample : Fin n → α,
          (M ^ n * Real.exp (z * windowBound)) *
            ((pmfProduct (Fin n) α tilt sample).toReal *
              if window sample then 1 else 0) := by
          rw [Finset.mul_sum]
    _ ≤
        ∑ sample : Fin n → α,
          (pmfProduct (Fin n) α μ sample).toReal *
            if tail sample then 1 else 0 := by
          refine Finset.sum_le_sum ?_
          intro sample _
          by_cases hwindow : window sample
          · have htail : tail sample := hwindow.2
            simp [hwindow, htail]
            let S := finiteIidScoreSum score sample
            have hS_ge : -windowBound ≤ S := hwindow.1
            have hnonneg_window : 0 ≤ windowBound + S := by
              linarith
            have hmul_nonpos : z * (windowBound + S) ≤ 0 :=
              mul_nonpos_of_nonpos_of_nonneg hz hnonneg_window
            have harg : z * windowBound ≤ -(z * S) := by
              have hsplit : z * windowBound + z * S ≤ 0 := by
                calc
                  z * windowBound + z * S = z * (windowBound + S) := by ring
                  _ ≤ 0 := hmul_nonpos
              linarith
            have hexp_le :
                Real.exp (z * windowBound) ≤ Real.exp (-(z * S)) :=
              Real.exp_le_exp.mpr harg
            have hscale_nonneg :
                0 ≤ (pmfProduct (Fin n) α tilt sample).toReal * M ^ n :=
              mul_nonneg ENNReal.toReal_nonneg
                (pow_nonneg (finiteMGF_nonneg μ score z) n)
            have hle :
                (pmfProduct (Fin n) α tilt sample).toReal * M ^ n *
                    Real.exp (z * windowBound) ≤
                  (pmfProduct (Fin n) α tilt sample).toReal * M ^ n *
                    Real.exp (-(z * S)) :=
              mul_le_mul_of_nonneg_left hexp_le hscale_nonneg
            calc
              (M ^ n * Real.exp (z * windowBound)) *
                  (∏ i : Fin n, (tilt (sample i)).toReal)
                  =
                  (pmfProduct (Fin n) α tilt sample).toReal * M ^ n *
                    Real.exp (z * windowBound) := by
                    rw [pmfProduct_apply_toReal]
                    ring
              _ ≤
                  (pmfProduct (Fin n) α tilt sample).toReal * M ^ n *
                    Real.exp (-(z * S)) := hle
              _ = ∏ i : Fin n, (μ (sample i)).toReal := by
                  rw [← pmfProduct_apply_toReal]
                  simpa [tilt, M, S] using
                    (pmfProduct_apply_toReal_eq_tilted_mul_mgf_pow_exp
                      μ score z sample).symm
          · by_cases htail : tail sample
            · have hprod_nonneg :
                  0 ≤ ∏ i : Fin n, (μ (sample i)).toReal :=
                Finset.prod_nonneg
                  (fun i _ => ENNReal.toReal_nonneg)
              simpa [hwindow, htail, pmfProduct_apply_toReal] using
                hprod_nonneg
            · simp [hwindow, htail]

/--
The event of a prescribed empirical count vector is contained in the iid
left-tail event whenever that count vector has nonpositive total score.
-/
theorem pmfProduct_prob_empiricalCounts_le_finiteIidScoreLeftTailProb
    (μ : PMF α) (score : α → ℝ) {n : ℕ} (k : α → ℕ)
    (hk_tail : ∑ a : α, (k a : ℝ) * score a ≤ 0) :
    pmfProb (pmfProduct (Fin n) α μ)
        (fun sample : Fin n → α =>
          ∀ a : α, empiricalCount sample a = k a) ≤
      finiteIidScoreLeftTailProb μ score 0 n := by
  classical
  refine
    pmfProb_le_of_imp
      (pmfProduct (Fin n) α μ)
      (fun sample : Fin n → α =>
        ∀ a : α, empiricalCount sample a = k a)
      (fun sample : Fin n → α => finiteIidScoreSum score sample ≤ 0)
      ?_
  intro sample hcounts
  rw [finiteIidScoreSum_eq_sum_empiricalCount]
  calc
    ∑ a : α, (empiricalCount sample a : ℝ) * score a
        = ∑ a : α, (k a : ℝ) * score a := by
          refine Finset.sum_congr rfl ?_
          intro a _
          rw [hcounts a]
    _ ≤ 0 := hk_tail

/--
For a ternary score written as `+1`, `-1`, or `0` according to two disjoint
events, the sample sum is the up-count minus the down-count.
-/
theorem finiteIidScoreSum_eq_card_up_sub_card_down
    {ι : Type*} [Fintype ι]
    (score : α → ℝ) (up down : α → Prop)
    [DecidablePred up] [DecidablePred down]
    (hdisj : ∀ a : α, up a → down a → False)
    (hscore :
      ∀ a : α, score a =
        if up a then (1 : ℝ) else if down a then (-1 : ℝ) else 0)
    (sample : ι → α) :
    finiteIidScoreSum score sample =
      ((successIndexSet up sample).card : ℝ) -
        ((successIndexSet down sample).card : ℝ) := by
  classical
  unfold finiteIidScoreSum
  have hpoint :
      ∀ i : ι,
        score (sample i) =
          (if up (sample i) then (1 : ℝ) else 0) -
            (if down (sample i) then (1 : ℝ) else 0) := by
    intro i
    by_cases hup : up (sample i)
    · have hnot_down : ¬ down (sample i) :=
        fun hdown => hdisj (sample i) hup hdown
      simp [hscore, hup, hnot_down]
    · by_cases hdown : down (sample i)
      · simp [hscore, hup, hdown]
      · simp [hscore, hup, hdown]
  calc
    ∑ i : ι, score (sample i)
        =
        ∑ i : ι,
          ((if up (sample i) then (1 : ℝ) else 0) -
            (if down (sample i) then (1 : ℝ) else 0)) := by
          exact Finset.sum_congr rfl (fun i _ => hpoint i)
    _ =
        (∑ i : ι, if up (sample i) then (1 : ℝ) else 0) -
          ∑ i : ι, if down (sample i) then (1 : ℝ) else 0 := by
          rw [Finset.sum_sub_distrib]
    _ =
        ((successIndexSet up sample).card : ℝ) -
          ((successIndexSet down sample).card : ℝ) := by
          simp [successIndexSet]

/--
An exact ternary count event with no more up-gaps than down-gaps is contained
in the iid left tail.
-/
theorem finiteIidScoreLeftTailProb_ge_ternary_counts
    (μ : PMF α) (score : α → ℝ) (up down : α → Prop)
    [DecidablePred up] [DecidablePred down]
    (hdisj : ∀ a : α, up a → down a → False)
    (hscore :
      ∀ a : α, score a =
        if up a then (1 : ℝ) else if down a then (-1 : ℝ) else 0)
    {i j n : ℕ} (hij : i ≤ j) :
    (Nat.choose n i : ℝ) * (Nat.choose (n - i) j : ℝ) *
        (pmfProb μ up) ^ i * (pmfProb μ down) ^ j *
          (pmfProb μ (fun a => ¬ up a ∧ ¬ down a)) ^ (n - i - j) ≤
      finiteIidScoreLeftTailProb μ score 0 n := by
  classical
  let countEvent : (Fin n → α) → Prop := fun sample =>
    (successIndexSet up sample).card = i ∧
      (successIndexSet down sample).card = j
  let tailEvent : (Fin n → α) → Prop := fun sample =>
    finiteIidScoreSum score sample ≤ 0
  have hcount_le_tail :
      pmfProb (pmfProduct (Fin n) α μ) countEvent ≤
        pmfProb (pmfProduct (Fin n) α μ) tailEvent := by
    refine pmfProb_le_of_imp (pmfProduct (Fin n) α μ) countEvent tailEvent ?_
    intro sample hcount
    have hsum :=
      finiteIidScoreSum_eq_card_up_sub_card_down
        (score := score) (up := up) (down := down) hdisj hscore sample
    rw [hcount.1, hcount.2] at hsum
    change finiteIidScoreSum score sample ≤ 0
    rw [hsum]
    exact sub_nonpos.mpr (by exact_mod_cast hij)
  have hcount_eq :
      pmfProb (pmfProduct (Fin n) α μ) countEvent =
        (Nat.choose n i : ℝ) * (Nat.choose (n - i) j : ℝ) *
          (pmfProb μ up) ^ i * (pmfProb μ down) ^ j *
            (pmfProb μ (fun a => ¬ up a ∧ ¬ down a)) ^ (n - i - j) := by
    simpa [countEvent, Fintype.card_fin, mul_assoc] using
      (pmfProduct_prob_two_disjoint_success_counts_eq
        (ι := Fin n) (α := α) μ up down hdisj i j)
  simpa [finiteIidScoreLeftTailProb, tailEvent, countEvent, hcount_eq] using
    hcount_le_tail

/--
One nonzero-count layer lower bound for a ternary iid score.  The layer uses
the central split `floor(m/2)` up-scores and `ceil(m/2)` down-scores, so it is
contained in the left tail when `pDown <= pUp`.
-/
theorem finiteIidScoreLeftTailProb_ge_ternary_central_layer
    (μ : PMF α) (score : α → ℝ) {pUp pDown : ℝ}
    (hUp : 0 < pUp) (hDown : 0 < pDown) (hle : pDown ≤ pUp)
    (hscore : ∀ a, score a = 1 ∨ score a = 0 ∨ score a = -1)
    (hUpProb : pmfProb μ (fun a => score a = 1) = pUp)
    (hDownProb : pmfProb μ (fun a => score a = -1) = pDown)
    {m n : ℕ} (hmn : m ≤ n) :
    ((Nat.choose n m : ℕ) : ℝ) *
        (Real.sqrt (pDown / pUp) *
          (2 * Real.sqrt (pUp * pDown)) ^ m /
            (((m + 1 : ℕ) : ℝ))) *
          (1 - pUp - pDown) ^ (n - m) ≤
      finiteIidScoreLeftTailProb μ score 0 n := by
  classical
  let up : α → Prop := fun a => score a = 1
  let down : α → Prop := fun a => score a = -1
  let i : ℕ := m / 2
  let j : ℕ := m - m / 2
  have hdisj : ∀ a, up a → down a → False := by
    intro a hup hdown
    have : (1 : ℝ) = -1 := hup.symm.trans hdown
    norm_num at this
  have hscore_if :
      ∀ a : α, score a =
        if up a then (1 : ℝ) else if down a then (-1 : ℝ) else 0 := by
    intro a
    by_cases hup : up a
    · simp [up, hup]
    · by_cases hdown : down a
      · simp [up, down, hup, hdown]
      · have hzero : score a = 0 := by
          rcases hscore a with hone | hzero | hneg
          · exact False.elim (hup hone)
          · exact hzero
          · exact False.elim (hdown hneg)
        simp [up, down, hup, hdown, hzero]
  have hzero_prob :
      pmfProb μ (fun a => ¬ up a ∧ ¬ down a) = 1 - pUp - pDown := by
    have hsplit :=
      pmfProb_not_and_not_eq_one_sub_add_of_disjoint μ up down hdisj
    simpa [up, down, hUpProb, hDownProb] using hsplit
  have hij : i ≤ j := by
    dsimp [i, j]
    omega
  have hi_le_m : i ≤ m := by
    dsimp [i]
    exact Nat.div_le_self m 2
  have hij_sum : i + j = m := by
    dsimp [i, j]
    omega
  have hm_sub_i : m - i = j := by
    dsimp [i, j]
  have hn_sub_i_sub_j : n - i - j = n - m := by
    omega
  have hchoose_nat :
      Nat.choose n m * Nat.choose m i =
        Nat.choose n i * Nat.choose (n - i) j := by
    simpa [hm_sub_i] using
      (Nat.choose_mul (n := n) (k := m) (s := i) hi_le_m)
  have hcentral :=
    AppliedModelingLib.FiniteSum.central_sign_weight_lower hUp hDown hle m
  have hchoose_nonneg :
      0 ≤ ((Nat.choose n m : ℕ) : ℝ) := by positivity
  have hp0_nonneg : 0 ≤ 1 - pUp - pDown := by
    rw [← hzero_prob]
    exact pmfProb_nonneg μ (fun a => ¬ up a ∧ ¬ down a)
  have hscale_nonneg :
      0 ≤ ((Nat.choose n m : ℕ) : ℝ) *
        (1 - pUp - pDown) ^ (n - m) := by
    exact mul_nonneg hchoose_nonneg (pow_nonneg hp0_nonneg _)
  have hscaled := mul_le_mul_of_nonneg_left hcentral hscale_nonneg
  have hcount :=
    finiteIidScoreLeftTailProb_ge_ternary_counts
      (μ := μ) (score := score) (up := up) (down := down)
      hdisj hscore_if (i := i) (j := j) (n := n) hij
  calc
    ((Nat.choose n m : ℕ) : ℝ) *
        (Real.sqrt (pDown / pUp) *
          (2 * Real.sqrt (pUp * pDown)) ^ m /
            (((m + 1 : ℕ) : ℝ))) *
          (1 - pUp - pDown) ^ (n - m)
        =
        (((Nat.choose n m : ℕ) : ℝ) *
          (1 - pUp - pDown) ^ (n - m)) *
          (Real.sqrt (pDown / pUp) *
            (2 * Real.sqrt (pUp * pDown)) ^ m /
              (((m + 1 : ℕ) : ℝ))) := by
          ring
    _ ≤
        (((Nat.choose n m : ℕ) : ℝ) *
          (1 - pUp - pDown) ^ (n - m)) *
          (((Nat.choose m i : ℕ) : ℝ) *
            (pUp ^ i * pDown ^ j)) := hscaled
    _ =
        ((Nat.choose n i : ℕ) : ℝ) *
          ((Nat.choose (n - i) j : ℕ) : ℝ) *
            (pmfProb μ up) ^ i * (pmfProb μ down) ^ j *
              (pmfProb μ (fun a => ¬ up a ∧ ¬ down a)) ^ (n - i - j) := by
          rw [hUpProb, hDownProb, hzero_prob, hn_sub_i_sub_j]
          have hchoose_real :
              ((Nat.choose n m : ℕ) : ℝ) *
                  ((Nat.choose m i : ℕ) : ℝ) =
                ((Nat.choose n i : ℕ) : ℝ) *
                  ((Nat.choose (n - i) j : ℕ) : ℝ) := by
            exact_mod_cast hchoose_nat
          rw [← hchoose_real]
          ring
    _ ≤ finiteIidScoreLeftTailProb μ score 0 n := hcount

/--
Concrete polynomially corrected lower bound for a ternary iid left tail.

For `0 < pDown <= pUp`, one central sign split inside a binomial layer,
chosen by averaging over the binomial expansion of the closed-form base, gives
a degree-two polynomial correction to the exact ternary Chernoff base.
-/
theorem finiteIidScoreLeftTailProb_ge_ternary_base_div_succ_sq
    (μ : PMF α) (score : α → ℝ) {pUp pDown : ℝ}
    (hUp : 0 < pUp) (hDown : 0 < pDown) (hle : pDown ≤ pUp)
    (hscore : ∀ a, score a = 1 ∨ score a = 0 ∨ score a = -1)
    (hUpProb : pmfProb μ (fun a => score a = 1) = pUp)
    (hDownProb : pmfProb μ (fun a => score a = -1) = pDown) :
    ∀ n : ℕ,
      Real.sqrt (pDown / pUp) *
          (2 * Real.sqrt (pUp * pDown) + (1 - pUp - pDown)) ^ n /
            ((((n + 1 : ℕ) : ℝ) ^ 2)) ≤
        finiteIidScoreLeftTailProb μ score 0 n := by
  classical
  intro n
  let x : ℝ := 2 * Real.sqrt (pUp * pDown)
  let y : ℝ := 1 - pUp - pDown
  let c : ℝ := Real.sqrt (pDown / pUp)
  obtain ⟨m, hm, havg⟩ :=
    AppliedModelingLib.FiniteSum.exists_binomial_layer_ge_average x y n
  have hmle : m ≤ n := by
    exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  let layerMass : ℝ := ((Nat.choose n m : ℕ) : ℝ) * x ^ m * y ^ (n - m)
  have hx_nonneg : 0 ≤ x := by
    dsimp [x]
    positivity
  have hy_nonneg : 0 ≤ y := by
    let up : α → Prop := fun a => score a = 1
    let down : α → Prop := fun a => score a = -1
    have hdisj : ∀ a, up a → down a → False := by
      intro a hup hdown
      have : (1 : ℝ) = -1 := hup.symm.trans hdown
      norm_num at this
    have hzero_prob :
        pmfProb μ (fun a => ¬ up a ∧ ¬ down a) = y := by
      have hsplit :=
        pmfProb_not_and_not_eq_one_sub_add_of_disjoint μ up down hdisj
      simpa [up, down, y, hUpProb, hDownProb] using hsplit
    simpa [hzero_prob] using
      pmfProb_nonneg μ (fun a => ¬ up a ∧ ¬ down a)
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    positivity
  have hdenN_pos : 0 < (((n + 1 : ℕ) : ℝ)) := by positivity
  have hdenM_pos : 0 < (((m + 1 : ℕ) : ℝ)) := by positivity
  have hdenM_le_denN : (((m + 1 : ℕ) : ℝ)) ≤ (((n + 1 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.succ_le_succ hmle
  have hcoef_le :
      c / (((n + 1 : ℕ) : ℝ)) ≤ c / (((m + 1 : ℕ) : ℝ)) :=
    div_le_div_of_nonneg_left hc_nonneg hdenM_pos hdenM_le_denN
  have hlayerMass_nonneg : 0 ≤ layerMass := by
    dsimp [layerMass]
    positivity
  have hcoefN_nonneg : 0 ≤ c / (((n + 1 : ℕ) : ℝ)) := by positivity
  have hfrom_avg :
      (c / (((n + 1 : ℕ) : ℝ))) *
          ((x + y) ^ n / (((n + 1 : ℕ) : ℝ))) ≤
        (c / (((n + 1 : ℕ) : ℝ))) * layerMass := by
    exact mul_le_mul_of_nonneg_left (by simpa [layerMass] using havg)
      hcoefN_nonneg
  have hto_central :
      (c / (((n + 1 : ℕ) : ℝ))) * layerMass ≤
        (c / (((m + 1 : ℕ) : ℝ))) * layerMass := by
    exact mul_le_mul_of_nonneg_right hcoef_le hlayerMass_nonneg
  have hlayer_tail :=
    finiteIidScoreLeftTailProb_ge_ternary_central_layer
      (μ := μ) (score := score) hUp hDown hle hscore hUpProb hDownProb
      (m := m) (n := n) hmle
  calc
    c * (x + y) ^ n / ((((n + 1 : ℕ) : ℝ) ^ 2))
        =
        (c / (((n + 1 : ℕ) : ℝ))) *
          ((x + y) ^ n / (((n + 1 : ℕ) : ℝ))) := by
          ring
    _ ≤ (c / (((n + 1 : ℕ) : ℝ))) * layerMass := hfrom_avg
    _ ≤ (c / (((m + 1 : ℕ) : ℝ))) * layerMass := hto_central
    _ =
        ((Nat.choose n m : ℕ) : ℝ) *
          (c * x ^ m / (((m + 1 : ℕ) : ℝ))) *
            y ^ (n - m) := by
          dsimp [layerMass]
          ring
    _ ≤ finiteIidScoreLeftTailProb μ score 0 n := by
          simpa [x, y, c, Nat.succ_eq_add_one, mul_assoc] using hlayer_tail

/--
A positive-mass one-sample event gives positive probability to every iid
left-tail event, provided samples whose coordinates all satisfy that event
force the tail inequality.
-/
theorem finiteIidScoreLeftTailProb_pos_of_event
    (μ : PMF α) (score : α → ℝ) {event : α → Prop} [DecidablePred event]
    {threshold : ℝ}
    (hevent_pos : 0 < pmfProb μ event)
    (hforce :
      ∀ {n : ℕ} (sample : Fin n → α),
        (∀ i : Fin n, event (sample i)) →
          finiteIidScoreSum score sample ≤ threshold) :
    ∀ n : ℕ, 0 < finiteIidScoreLeftTailProb μ score threshold n := by
  classical
  rcases (pmfProb_pos_iff_exists_pos_mass μ event).mp hevent_pos with
    ⟨a₀, ha₀, hmass⟩
  intro n
  let sample : Fin n → α := fun _ => a₀
  have htail : finiteIidScoreSum score sample ≤ threshold :=
    hforce sample (fun _ => ha₀)
  have hmass_sample : 0 < (pmfProduct (Fin n) α μ sample).toReal := by
    rw [pmfProduct_apply_toReal]
    exact Finset.prod_pos (fun i _ => by simpa [sample] using hmass)
  exact
    pmfProb_pos_of_mass
      (pmfProduct (Fin n) α μ)
      (fun sample : Fin n → α => finiteIidScoreSum score sample ≤ threshold)
      sample htail hmass_sample

/--
A single iid sample path lower-bounds the finite iid left-tail probability by
its product atom mass.
-/
theorem pmfProduct_sample_mass_le_finiteIidScoreLeftTailProb
    (μ : PMF α) (score : α → ℝ) {threshold : ℝ} {n : ℕ}
    (sample : Fin n → α)
    (htail : finiteIidScoreSum score sample ≤ threshold) :
    (pmfProduct (Fin n) α μ sample).toReal ≤
      finiteIidScoreLeftTailProb μ score threshold n := by
  simpa [finiteIidScoreLeftTailProb] using
    pmf_apply_toReal_le_pmfProb_of_mem
      (pmfProduct (Fin n) α μ)
      (fun sample : Fin n → α => finiteIidScoreSum score sample ≤ threshold)
      sample htail

/--
Eventual-positive form of `finiteIidScoreLeftTailProb_pos_of_event`.
-/
theorem finiteIidScoreLeftTailProb_eventually_pos_of_event
    (μ : PMF α) (score : α → ℝ) {event : α → Prop} [DecidablePred event]
    {threshold : ℝ}
    (hevent_pos : 0 < pmfProb μ event)
    (hforce :
      ∀ {n : ℕ} (sample : Fin n → α),
        (∀ i : Fin n, event (sample i)) →
          finiteIidScoreSum score sample ≤ threshold) :
    ∀ᶠ n : ℕ in atTop, 0 < finiteIidScoreLeftTailProb μ score threshold n :=
  Filter.Eventually.of_forall
    (finiteIidScoreLeftTailProb_pos_of_event μ score hevent_pos hforce)

/--
Checkable lower-bound certificate for finite iid left tails.  A downstream
paper can provide one explicit left-tail sample path for each large `n` whose
product atom mass has the displayed polynomially corrected geometric lower
bound.
-/
structure FiniteIidScorePathLowerCertificate
    (μ : PMF α) (score : α → ℝ) where
  base : ℝ
  lowerConst : ℝ
  degree : ℕ
  base_pos : 0 < base
  lowerConst_pos : 0 < lowerConst
  sample : (n : ℕ) → Fin n → α
  sample_tail :
    ∀ n : ℕ, finiteIidScoreSum score (sample n) ≤ 0
  sample_mass_lower :
    ∀ᶠ n : ℕ in atTop,
      lowerConst * base ^ n / (((n.succ : ℕ) : ℝ) ^ degree) ≤
        (pmfProduct (Fin n) α μ (sample n)).toReal

namespace FiniteIidScorePathLowerCertificate

/--
A path lower certificate yields exponential lower bounds at every slower rate
than its geometric base.
-/
theorem hasExpLowerBoundWithConst
    {μ : PMF α} {score : α → ℝ}
    (C : FiniteIidScorePathLowerCertificate μ score)
    {targetRate : ℝ} (htarget : -Real.log C.base < targetRate) :
    HasExpLowerBoundWithConst
      (fun n => finiteIidScoreLeftTailProb μ score 0 n) targetRate := by
  refine
    HasExpLowerBoundWithConst.of_eventually_geometric_div_polynomial_lower
      C.degree C.lowerConst_pos C.base_pos htarget ?_
  filter_upwards [C.sample_mass_lower] with n hmass
  exact hmass.trans
    (pmfProduct_sample_mass_le_finiteIidScoreLeftTailProb
      (μ := μ) (score := score) (threshold := 0)
      (sample := C.sample n) (C.sample_tail n))

end FiniteIidScorePathLowerCertificate

/--
Checkable lower-bound certificate for finite iid left tails stated directly at
the tail-probability level.  This is the right target for empirical-type and
multinomial lower bounds, whose exponential contribution includes the number of
samples with a prescribed type rather than just one canonical sample path.
-/
structure FiniteIidScoreTailLowerCertificate
    (μ : PMF α) (score : α → ℝ) where
  base : ℝ
  lowerConst : ℝ
  degree : ℕ
  base_pos : 0 < base
  lowerConst_pos : 0 < lowerConst
  tail_prob_lower :
    ∀ᶠ n : ℕ in atTop,
      lowerConst * base ^ n / (((n.succ : ℕ) : ℝ) ^ degree) ≤
        finiteIidScoreLeftTailProb μ score 0 n

namespace FiniteIidScoreTailLowerCertificate

/--
A direct tail-probability lower certificate yields exponential lower bounds at
every slower rate than its geometric base.
-/
theorem hasExpLowerBoundWithConst
    {μ : PMF α} {score : α → ℝ}
    (C : FiniteIidScoreTailLowerCertificate μ score)
    {targetRate : ℝ} (htarget : -Real.log C.base < targetRate) :
    HasExpLowerBoundWithConst
      (fun n => finiteIidScoreLeftTailProb μ score 0 n) targetRate := by
  exact
    HasExpLowerBoundWithConst.of_eventually_geometric_div_polynomial_lower
      C.degree C.lowerConst_pos C.base_pos htarget C.tail_prob_lower

end FiniteIidScoreTailLowerCertificate

/--
Tail lower certificate from polynomial mass in a bounded tilted left-tail
window.  This is the reusable change-of-measure step in finite-support Cramer
lower-bound proofs; the remaining analytic/combinatorial work is to prove the
tilted-window mass lower bound.
-/
def finiteIidScoreTailLowerCertificate_of_tilted_window
    (μ : PMF α) (score : α → ℝ) {z windowBound lowerConst : ℝ}
    {degree : ℕ}
    (hz : z ≤ 0)
    (hlowerConst_pos : 0 < lowerConst)
    (hwindow :
      ∀ᶠ n : ℕ in atTop,
        lowerConst / (((n.succ : ℕ) : ℝ) ^ degree) ≤
          pmfProb
            (pmfProduct (Fin n) α (finiteExponentialTilt μ score z))
            (fun sample : Fin n → α =>
              -windowBound ≤ finiteIidScoreSum score sample ∧
                finiteIidScoreSum score sample ≤ 0)) :
    FiniteIidScoreTailLowerCertificate μ score where
  base := finiteMGF μ score z
  lowerConst := lowerConst * Real.exp (z * windowBound)
  degree := degree
  base_pos := finiteMGF_pos μ score z
  lowerConst_pos := mul_pos hlowerConst_pos (Real.exp_pos _)
  tail_prob_lower := by
    filter_upwards [hwindow] with n hn
    have hbridge :=
      finiteIidScoreLeftTailProb_ge_tilted_window
        (μ := μ) (score := score) (z := z)
        (windowBound := windowBound) hz n
    have hscale_nonneg :
        0 ≤ (finiteMGF μ score z) ^ n * Real.exp (z * windowBound) :=
      mul_nonneg (pow_nonneg (finiteMGF_nonneg μ score z) n)
        (Real.exp_pos _).le
    calc
      (lowerConst * Real.exp (z * windowBound)) *
          (finiteMGF μ score z) ^ n /
            (((n.succ : ℕ) : ℝ) ^ degree)
          =
          (finiteMGF μ score z) ^ n * Real.exp (z * windowBound) *
            (lowerConst / (((n.succ : ℕ) : ℝ) ^ degree)) := by
            ring
      _ ≤
          (finiteMGF μ score z) ^ n * Real.exp (z * windowBound) *
            pmfProb
              (pmfProduct (Fin n) α (finiteExponentialTilt μ score z))
              (fun sample : Fin n → α =>
                -windowBound ≤ finiteIidScoreSum score sample ∧
                  finiteIidScoreSum score sample ≤ 0) := by
            exact mul_le_mul_of_nonneg_left hn hscale_nonneg
      _ ≤ finiteIidScoreLeftTailProb μ score 0 n := hbridge

/--
The exponential moment of a finite iid sample sum factors as the one-sample
finite MGF raised to the number of coordinates.
-/
theorem pmfProduct_exp_score_sum_eq_finiteMGF_pow
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : PMF α) (score : α → ℝ) (z : ℝ) :
    pmfExp (pmfProduct ι α μ)
        (fun sample : ι → α =>
          Real.exp (∑ i : ι, z * score (sample i))) =
      (finiteMGF μ score z) ^ Fintype.card ι := by
  classical
  unfold pmfExp finiteMGF
  calc
    ∑ sample : ι → α,
        (pmfProduct ι α μ sample).toReal *
          Real.exp (∑ i : ι, z * score (sample i))
        =
        ∑ sample : ι → α,
          ∏ i : ι, ((μ (sample i)).toReal *
            Real.exp (z * score (sample i))) := by
          refine Finset.sum_congr rfl ?_
          intro sample _
          rw [pmfProduct_apply_toReal, Real.exp_sum]
          rw [Finset.prod_mul_distrib]
    _ =
        ∏ i : ι, ∑ a : α,
          (μ a).toReal * Real.exp (z * score a) := by
          symm
          simpa using
            (Finset.prod_univ_sum
              (t := fun _i : ι => (Finset.univ : Finset α))
              (f := fun _i a =>
                (μ a).toReal * Real.exp (z * score a)))
    _ =
        (∑ a : α, (μ a).toReal * Real.exp (z * score a)) ^
          Fintype.card ι := by
          simp [Finset.prod_const]

/--
Plan-facing iid sum MGF: the MGF of a finite iid sample sum is the
`Fintype.card ι`-th power of the one-sample finite MGF.
-/
theorem iid_sum_mgf
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : PMF α) (score : α → ℝ) (z : ℝ) :
    pmfExp (pmfProduct ι α μ)
        (fun sample : ι → α =>
          Real.exp (z * finiteIidScoreSum score sample)) =
      (finiteMGF μ score z) ^ Fintype.card ι := by
  simpa [finiteIidScoreSum, Finset.mul_sum] using
    pmfProduct_exp_score_sum_eq_finiteMGF_pow
      (ι := ι) μ score z

/--
Chernoff upper bound for the left tail of a finite iid score sum.  If `z <= 0`,
then on the event `sum score <= 0`, `1 <= exp(z * sum score)`.
-/
theorem finiteIidScoreLeftTailProb_le_finiteMGF_pow_of_nonpos
    (μ : PMF α) (score : α → ℝ) {z : ℝ} (hz : z ≤ 0) (n : ℕ) :
    finiteIidScoreLeftTailProb μ score 0 n ≤
      (finiteMGF μ score z) ^ n := by
  classical
  unfold finiteIidScoreLeftTailProb pmfProb
  have hpoint :
      ∀ sample : Fin n → α,
        (if finiteIidScoreSum score sample ≤ 0 then (1 : ℝ) else 0) ≤
          Real.exp (∑ i : Fin n, z * score (sample i)) := by
    intro sample
    by_cases htail : finiteIidScoreSum score sample ≤ 0
    · have hmul_nonneg :
          0 ≤ z * finiteIidScoreSum score sample := by
        exact mul_nonneg_of_nonpos_of_nonpos hz htail
      have hone :
          (1 : ℝ) ≤ Real.exp (z * finiteIidScoreSum score sample) := by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr hmul_nonneg
      have hsum :
          (∑ i : Fin n, z * score (sample i)) =
            z * finiteIidScoreSum score sample := by
        simp [finiteIidScoreSum, Finset.mul_sum]
      simpa [htail, hsum]
    · exact by
        simp [htail, (Real.exp_pos _).le]
  calc
    pmfExp (pmfProduct (Fin n) α μ)
        (fun sample : Fin n → α =>
          if finiteIidScoreSum score sample ≤ 0 then (1 : ℝ) else 0)
        ≤
        pmfExp (pmfProduct (Fin n) α μ)
          (fun sample : Fin n → α =>
            Real.exp (∑ i : Fin n, z * score (sample i))) :=
          pmfExp_le_pmfExp_of_forall_le
            (pmfProduct (Fin n) α μ) _ _ hpoint
    _ = (finiteMGF μ score z) ^ n := by
          simpa using
            pmfProduct_exp_score_sum_eq_finiteMGF_pow
              (ι := Fin n) μ score z

/--
If one finite-MGF dual point is bounded by `exp (-rate)`, the iid left-tail
sequence has an exponential upper-bound certificate at `rate`.
-/
theorem finiteIidScoreLeftTail_hasExpUpperBoundWithConst_of_mgf_le_exp_neg
    (μ : PMF α) (score : α → ℝ) {z rate : ℝ}
    (hz : z ≤ 0)
    (hmgf : finiteMGF μ score z ≤ Real.exp (-rate)) :
    HasExpUpperBoundWithConst
      (fun n => finiteIidScoreLeftTailProb μ score 0 n) rate := by
  refine ⟨1, zero_lt_one, ?_⟩
  filter_upwards with n
  have htail_nonneg :
      0 ≤ finiteIidScoreLeftTailProb μ score 0 n :=
    pmfProb_nonneg (pmfProduct (Fin n) α μ)
      (fun sample : Fin n → α => finiteIidScoreSum score sample ≤ 0)
  refine ⟨htail_nonneg, ?_⟩
  have hchernoff :=
    finiteIidScoreLeftTailProb_le_finiteMGF_pow_of_nonpos μ score hz n
  have hpow :
      (finiteMGF μ score z) ^ n ≤ (Real.exp (-rate)) ^ n :=
    pow_le_pow_left₀ (finiteMGF_nonneg μ score z) hmgf n
  have hexp_pow :
      (Real.exp (-rate)) ^ n = Real.exp (-(n : ℝ) * rate) := by
    rw [← Real.exp_nat_mul]
    ring_nf
  calc
    finiteIidScoreLeftTailProb μ score 0 n ≤ (finiteMGF μ score z) ^ n :=
      hchernoff
    _ ≤ (Real.exp (-rate)) ^ n := hpow
    _ = 1 * Real.exp (-(n : ℝ) * rate) := by
      rw [hexp_pow]
      ring

/--
If a nonpositive Chernoff dual has negative log-MGF at least `rate`, then the
iid left-tail sequence has an exponential upper-bound certificate at `rate`.
This is the paper-facing form used when a proof identifies an explicit dual
parameter rather than comparing raw MGFs.
-/
theorem finiteIidScoreLeftTail_hasExpUpperBoundWithConst_of_nonpos_dual_rate_le
    (μ : PMF α) (score : α → ℝ) {z rate : ℝ}
    (hz : z ≤ 0)
    (hrate : rate ≤ -finiteLogMGF μ score z) :
    HasExpUpperBoundWithConst
      (fun n => finiteIidScoreLeftTailProb μ score 0 n) rate := by
  refine
    finiteIidScoreLeftTail_hasExpUpperBoundWithConst_of_mgf_le_exp_neg
      (μ := μ) (score := score) (z := z) (rate := rate) hz ?_
  rw [← exp_finiteLogMGF μ score z]
  exact Real.exp_le_exp.mpr (by linarith)

/--
Pointwise finite iid Chernoff upper bound from a nonpositive dual parameter
and a lower bound on the dual rate.
-/
theorem finiteIidScoreLeftTailProb_le_exp_of_nonpos_dual_rate_le
    (μ : PMF α) (score : α → ℝ) {z rate : ℝ}
    (hz : z ≤ 0)
    (hrate : rate ≤ -finiteLogMGF μ score z)
    (n : ℕ) :
    finiteIidScoreLeftTailProb μ score 0 n ≤
      Real.exp (-(n : ℝ) * rate) := by
  have hmgf : finiteMGF μ score z ≤ Real.exp (-rate) := by
    rw [← exp_finiteLogMGF μ score z]
    exact Real.exp_le_exp.mpr (by linarith)
  have hchernoff :=
    finiteIidScoreLeftTailProb_le_finiteMGF_pow_of_nonpos μ score hz n
  have hpow :
      (finiteMGF μ score z) ^ n ≤ (Real.exp (-rate)) ^ n :=
    pow_le_pow_left₀ (finiteMGF_nonneg μ score z) hmgf n
  have hexp_pow :
      (Real.exp (-rate)) ^ n = Real.exp (-(n : ℝ) * rate) := by
    rw [← Real.exp_nat_mul]
    ring_nf
  calc
    finiteIidScoreLeftTailProb μ score 0 n ≤ (finiteMGF μ score z) ^ n :=
      hchernoff
    _ ≤ (Real.exp (-rate)) ^ n := hpow
    _ = Real.exp (-(n : ℝ) * rate) := hexp_pow

/--
Plan-facing finite iid Chernoff upper certificate from a nonpositive dual
parameter and a lower bound on the dual rate.
-/
theorem finite_iid_chernoff_upper_certificate_of_nonpos_dual
    (μ : PMF α) (score : α → ℝ) {z rate : ℝ}
    (hz : z ≤ 0)
    (hrate : rate ≤ -finiteLogMGF μ score z) :
    HasExpUpperBoundWithConst
      (fun n => finiteIidScoreLeftTailProb μ score 0 n) rate :=
  finiteIidScoreLeftTail_hasExpUpperBoundWithConst_of_nonpos_dual_rate_le
    μ score hz hrate

/--
Generic finite Chernoff upper-bound side.  If the one-voter score has
nonnegative mean and the finite log-MGF range is bounded below, then every
target rate strictly below the source Chernoff exponent has an iid left-tail
upper-bound certificate.
-/
theorem finiteIidScoreLeftTail_upperBounds_of_lt_chernoffRate
    (μ : PMF α) (score : α → ℝ)
    (hmean : 0 ≤ pmfExp μ score)
    (hbdd :
      BddBelow (Set.range fun z : ℝ => finiteLogMGF μ score z)) :
    ∀ targetRate, targetRate < finiteChernoffRate μ score →
      HasExpUpperBoundWithConst
        (fun n => finiteIidScoreLeftTailProb μ score 0 n) targetRate := by
  intro targetRate htarget
  by_cases htarget_nonpos : targetRate ≤ 0
  · refine
      finiteIidScoreLeftTail_hasExpUpperBoundWithConst_of_nonpos_dual_rate_le
        (μ := μ) (score := score) (z := 0) (rate := targetRate)
        le_rfl ?_
    simpa [finiteLogMGF_zero] using htarget_nonpos
  · have htarget_pos : 0 < targetRate := lt_of_not_ge htarget_nonpos
    have hinf_lt : sInf (Set.range fun z : ℝ => finiteLogMGF μ score z) <
        -targetRate := by
      dsimp [finiteChernoffRate] at htarget
      linarith
    rcases (csInf_lt_iff hbdd (Set.range_nonempty
        (fun z : ℝ => finiteLogMGF μ score z))).1 hinf_lt with
      ⟨logValue, hlogValue_mem, hlogValue_lt⟩
    rcases hlogValue_mem with ⟨z, rfl⟩
    have hlog_neg : finiteLogMGF μ score z < 0 := by
      linarith
    have hz_neg : z < 0 := by
      by_contra hz_not_neg
      have hz_nonneg : 0 ≤ z := le_of_not_gt hz_not_neg
      have hlog_nonneg :
          0 ≤ finiteLogMGF μ score z :=
        finiteLogMGF_nonneg_of_nonneg_dual_of_pmfExp_nonneg
          μ score hmean hz_nonneg
      linarith
    refine
      finiteIidScoreLeftTail_hasExpUpperBoundWithConst_of_nonpos_dual_rate_le
        (μ := μ) (score := score) (z := z) (rate := targetRate)
        (le_of_lt hz_neg) ?_
    linarith

/--
Plan-facing finite iid Chernoff upper certificate at every target rate below
the finite-support Chernoff exponent.
-/
theorem finite_iid_chernoff_upper_certificate
    (μ : PMF α) (score : α → ℝ)
    (hmean : 0 ≤ pmfExp μ score)
    (hbdd :
      BddBelow (Set.range fun z : ℝ => finiteLogMGF μ score z)) :
    ∀ targetRate, targetRate < finiteChernoffRate μ score →
      HasExpUpperBoundWithConst
        (fun n => finiteIidScoreLeftTailProb μ score 0 n) targetRate :=
  finiteIidScoreLeftTail_upperBounds_of_lt_chernoffRate μ score hmean hbdd

/--
Generic finite Chernoff upper-bound side with boundedness discharged by
positive-mass support on both sides of zero.
-/
theorem finiteIidScoreLeftTail_upperBounds_of_lt_chernoffRate_of_pos_neg_atoms
    (μ : PMF α) (score : α → ℝ)
    (hmean : 0 ≤ pmfExp μ score)
    {aPos aNeg : α}
    (hmassPos : 0 < (μ aPos).toReal)
    (hscorePos : 0 < score aPos)
    (hmassNeg : 0 < (μ aNeg).toReal)
    (hscoreNeg : score aNeg < 0) :
    ∀ targetRate, targetRate < finiteChernoffRate μ score →
      HasExpUpperBoundWithConst
        (fun n => finiteIidScoreLeftTailProb μ score 0 n) targetRate :=
  finiteIidScoreLeftTail_upperBounds_of_lt_chernoffRate
    μ score hmean
    (finiteLogMGF_bddBelow_of_pos_neg_atoms
      μ score hmassPos hscorePos hmassNeg hscoreNeg)

/--
Plan-facing finite iid Chernoff upper certificate with finite-support
boundedness discharged by positive-mass atoms on both sides of zero.
-/
theorem finite_iid_chernoff_upper_certificate_of_pos_neg_atoms
    (μ : PMF α) (score : α → ℝ)
    (hmean : 0 ≤ pmfExp μ score)
    {aPos aNeg : α}
    (hmassPos : 0 < (μ aPos).toReal)
    (hscorePos : 0 < score aPos)
    (hmassNeg : 0 < (μ aNeg).toReal)
    (hscoreNeg : score aNeg < 0) :
    ∀ targetRate, targetRate < finiteChernoffRate μ score →
      HasExpUpperBoundWithConst
        (fun n => finiteIidScoreLeftTailProb μ score 0 n) targetRate :=
  finiteIidScoreLeftTail_upperBounds_of_lt_chernoffRate_of_pos_neg_atoms
    μ score hmean hmassPos hscorePos hmassNeg hscoreNeg

/--
If a finite one-voter score has positive mean, then its iid nonpositive
left-tail probability has some strictly positive exponential upper-bound rate.
This is the local Chernoff consequence used by paper-level consistency
arguments before proving an exact Cramer rate.
-/
theorem finiteIidScoreLeftTail_exists_pos_expUpperBoundWithConst_of_pmfExp_pos
    (μ : PMF α) (score : α → ℝ)
    (hmean : 0 < pmfExp μ score) :
    ∃ rate : ℝ,
      0 < rate ∧
        HasExpUpperBoundWithConst
          (fun n => finiteIidScoreLeftTailProb μ score 0 n) rate := by
  rcases exists_neg_finiteMGF_lt_one_of_pmfExp_pos μ score hmean with
    ⟨z, hz_neg, hmgf_lt_one⟩
  let rate : ℝ := -Real.log (finiteMGF μ score z)
  have hmgf_pos : 0 < finiteMGF μ score z :=
    finiteMGF_pos μ score z
  have hrate_pos : 0 < rate := by
    have hlog_lt_zero :
        Real.log (finiteMGF μ score z) < 0 := by
      simpa using
        (Real.log_lt_log hmgf_pos hmgf_lt_one)
    dsimp [rate]
    linarith
  have hz_nonpos : z ≤ 0 := le_of_lt hz_neg
  have hmgf_exp :
      finiteMGF μ score z ≤ Real.exp (-rate) := by
    have hexp : Real.exp (-rate) = finiteMGF μ score z := by
      dsimp [rate]
      rw [neg_neg]
      exact Real.exp_log hmgf_pos
    rw [hexp]
  exact
    ⟨rate, hrate_pos,
      finiteIidScoreLeftTail_hasExpUpperBoundWithConst_of_mgf_le_exp_neg
        μ score hz_nonpos hmgf_exp⟩

/--
Finite iid Cramer certificate for one score law at the Chernoff exponent
`-inf_z log E exp(z X)`.  This keeps the analytic lower-bound theorem as a
small, reusable boundary while making the downstream exact-rate construction
fully uniform across papers.
-/
structure FiniteIidScoreCramerCertificate
    (μ : PMF α) (score : α → ℝ) where
  eventually_pos :
    ∀ᶠ n in atTop, 0 < finiteIidScoreLeftTailProb μ score 0 n
  upper_bounds :
    ∀ targetRate, targetRate < finiteChernoffRate μ score →
      HasExpUpperBoundWithConst
        (fun n => finiteIidScoreLeftTailProb μ score 0 n) targetRate
  lower_bounds :
    ∀ targetRate, finiteChernoffRate μ score < targetRate →
      HasExpLowerBoundWithConst
        (fun n => finiteIidScoreLeftTailProb μ score 0 n) targetRate

namespace FiniteIidScoreCramerCertificate

/-- A finite iid Cramer certificate yields the exact exponential-rate object. -/
theorem exponentialRateCertificate
    {μ : PMF α} {score : α → ℝ}
    (C : FiniteIidScoreCramerCertificate μ score) :
    ExponentialRateCertificate
      (fun n => finiteIidScoreLeftTailProb μ score 0 n)
      (finiteChernoffRate μ score) where
  eventually_pos := C.eventually_pos
  has_rate :=
    hasExponentialRate_of_expUpperLowerBounds
      C.eventually_pos C.upper_bounds C.lower_bounds

end FiniteIidScoreCramerCertificate

/--
Build the standard finite iid Cramer certificate from a reusable upper-bound
proof and a checkable explicit left-tail path lower certificate.
-/
theorem finiteIidScoreCramerCertificate_of_pathLower
    (μ : PMF α) (score : α → ℝ)
    (hupper :
      ∀ targetRate, targetRate < finiteChernoffRate μ score →
        HasExpUpperBoundWithConst
          (fun n => finiteIidScoreLeftTailProb μ score 0 n) targetRate)
    (C : FiniteIidScorePathLowerCertificate μ score)
    (hrate : -Real.log C.base = finiteChernoffRate μ score) :
    FiniteIidScoreCramerCertificate μ score := by
  refine
    { eventually_pos := ?_
      upper_bounds := hupper
      lower_bounds := ?_ }
  · filter_upwards [C.sample_mass_lower] with n hmass
    have htail_ge :
        C.lowerConst * C.base ^ n /
            (((n.succ : ℕ) : ℝ) ^ C.degree) ≤
          finiteIidScoreLeftTailProb μ score 0 n := by
      exact hmass.trans
        (pmfProduct_sample_mass_le_finiteIidScoreLeftTailProb
          (μ := μ) (score := score) (threshold := 0)
          (sample := C.sample n) (C.sample_tail n))
    have hgeom_pos :
        0 <
          C.lowerConst * C.base ^ n /
            (((n.succ : ℕ) : ℝ) ^ C.degree) := by
      have hbase_pow_pos : 0 < C.base ^ n := pow_pos C.base_pos n
      have hnum_pos : 0 < C.lowerConst * C.base ^ n :=
        mul_pos C.lowerConst_pos hbase_pow_pos
      have hden_pos : 0 < (((n.succ : ℕ) : ℝ) ^ C.degree) := by
        positivity
      exact div_pos hnum_pos hden_pos
    exact lt_of_lt_of_le hgeom_pos htail_ge
  · intro targetRate htarget
    exact C.hasExpLowerBoundWithConst (by
      rw [hrate]
      exact htarget)

/--
Build the standard finite iid Cramer certificate from a reusable upper-bound
proof and a direct lower bound on the left-tail probabilities.
-/
theorem finiteIidScoreCramerCertificate_of_tailLower
    (μ : PMF α) (score : α → ℝ)
    (hupper :
      ∀ targetRate, targetRate < finiteChernoffRate μ score →
        HasExpUpperBoundWithConst
          (fun n => finiteIidScoreLeftTailProb μ score 0 n) targetRate)
    (C : FiniteIidScoreTailLowerCertificate μ score)
    (hrate : -Real.log C.base = finiteChernoffRate μ score) :
    FiniteIidScoreCramerCertificate μ score := by
  refine
    { eventually_pos := ?_
      upper_bounds := hupper
      lower_bounds := ?_ }
  · filter_upwards [C.tail_prob_lower] with n htail
    have hgeom_pos :
        0 <
          C.lowerConst * C.base ^ n /
            (((n.succ : ℕ) : ℝ) ^ C.degree) := by
      have hbase_pow_pos : 0 < C.base ^ n := pow_pos C.base_pos n
      have hnum_pos : 0 < C.lowerConst * C.base ^ n :=
        mul_pos C.lowerConst_pos hbase_pow_pos
      have hden_pos : 0 < (((n.succ : ℕ) : ℝ) ^ C.degree) := by
        positivity
      exact div_pos hnum_pos hden_pos
    exact lt_of_lt_of_le hgeom_pos htail
  · intro targetRate htarget
    exact C.hasExpLowerBoundWithConst (by
      rw [hrate]
      exact htarget)

/--
Build the standard finite iid Cramer certificate from a bounded-window lower
bound under an exponential tilt.  The remaining analytic input is that the
chosen tilt realizes the finite Chernoff rate.
-/
theorem finiteIidScoreCramerCertificate_of_tilted_window
    (μ : PMF α) (score : α → ℝ)
    (hupper :
      ∀ targetRate, targetRate < finiteChernoffRate μ score →
        HasExpUpperBoundWithConst
          (fun n => finiteIidScoreLeftTailProb μ score 0 n) targetRate)
    {z windowBound lowerConst : ℝ} {degree : ℕ}
    (hz : z ≤ 0)
    (hlowerConst_pos : 0 < lowerConst)
    (hwindow :
      ∀ᶠ n : ℕ in atTop,
        lowerConst / (((n.succ : ℕ) : ℝ) ^ degree) ≤
          pmfProb
            (pmfProduct (Fin n) α (finiteExponentialTilt μ score z))
            (fun sample : Fin n → α =>
              -windowBound ≤ finiteIidScoreSum score sample ∧
                finiteIidScoreSum score sample ≤ 0))
    (hrate :
      -Real.log (finiteMGF μ score z) = finiteChernoffRate μ score) :
    FiniteIidScoreCramerCertificate μ score :=
  finiteIidScoreCramerCertificate_of_tailLower
    μ score hupper
    (finiteIidScoreTailLowerCertificate_of_tilted_window
      (μ := μ) (score := score) hz hlowerConst_pos hwindow)
    (by simpa using hrate)

/--
Tilted-window finite iid Cramer certificate with the Chernoff upper side
discharged by nonnegative mean and positive-mass atoms on both sides of zero.
-/
theorem finiteIidScoreCramerCertificate_of_tilted_window_of_mean_nonneg_pos_neg_atoms
    (μ : PMF α) (score : α → ℝ)
    (hmean : 0 ≤ pmfExp μ score)
    {aPos aNeg : α}
    (hmassPos : 0 < (μ aPos).toReal)
    (hscorePos : 0 < score aPos)
    (hmassNeg : 0 < (μ aNeg).toReal)
    (hscoreNeg : score aNeg < 0)
    {z windowBound lowerConst : ℝ} {degree : ℕ}
    (hz : z ≤ 0)
    (hlowerConst_pos : 0 < lowerConst)
    (hwindow :
      ∀ᶠ n : ℕ in atTop,
        lowerConst / (((n.succ : ℕ) : ℝ) ^ degree) ≤
          pmfProb
            (pmfProduct (Fin n) α (finiteExponentialTilt μ score z))
            (fun sample : Fin n → α =>
              -windowBound ≤ finiteIidScoreSum score sample ∧
                finiteIidScoreSum score sample ≤ 0))
    (hrate :
      -Real.log (finiteMGF μ score z) = finiteChernoffRate μ score) :
    FiniteIidScoreCramerCertificate μ score :=
  finiteIidScoreCramerCertificate_of_tilted_window
    μ score
    (finiteIidScoreLeftTail_upperBounds_of_lt_chernoffRate_of_pos_neg_atoms
      μ score hmean hmassPos hscorePos hmassNeg hscoreNeg)
    hz hlowerConst_pos hwindow hrate

/--
Tilted-window finite iid Cramer certificate from a stationary Chernoff tilt.
Convexity of the finite log-MGF identifies the tilted base with the Chernoff
rate, leaving only the tilted-window mass lower bound as the lower-tail input.
-/
theorem finiteIidScoreCramerCertificate_of_stationary_tilted_window_of_mean_nonneg_pos_neg_atoms
    (μ : PMF α) (score : α → ℝ)
    (hmean : 0 ≤ pmfExp μ score)
    {aPos aNeg : α}
    (hmassPos : 0 < (μ aPos).toReal)
    (hscorePos : 0 < score aPos)
    (hmassNeg : 0 < (μ aNeg).toReal)
    (hscoreNeg : score aNeg < 0)
    {z windowBound lowerConst : ℝ} {degree : ℕ}
    (hz : z ≤ 0)
    (hstationary :
      (∑ a : α,
        (μ a).toReal * (score a * Real.exp (z * score a))) = 0)
    (hlowerConst_pos : 0 < lowerConst)
    (hwindow :
      ∀ᶠ n : ℕ in atTop,
        lowerConst / (((n.succ : ℕ) : ℝ) ^ degree) ≤
          pmfProb
            (pmfProduct (Fin n) α (finiteExponentialTilt μ score z))
            (fun sample : Fin n → α =>
              -windowBound ≤ finiteIidScoreSum score sample ∧
                finiteIidScoreSum score sample ≤ 0)) :
    FiniteIidScoreCramerCertificate μ score := by
  have hrate :
      -Real.log (finiteMGF μ score z) = finiteChernoffRate μ score := by
    symm
    exact
      finiteChernoffRate_eq_neg_log_base_of_convex_stationary
        μ score (finiteLogMGF_convex μ score) hstationary (by rfl)
  exact
    finiteIidScoreCramerCertificate_of_tilted_window_of_mean_nonneg_pos_neg_atoms
      μ score hmean hmassPos hscorePos hmassNeg hscoreNeg
      hz hlowerConst_pos hwindow hrate

/--
Build the standard finite iid Cramer certificate from a reusable upper-bound
proof and a path lower-bound witness available at every strictly slower
target rate.  This is often the most convenient method-of-types interface: the
lower-bound proof may choose a different empirical type for each target rate.
-/
theorem finiteIidScoreCramerCertificate_of_pathLower_witnesses
    (μ : PMF α) (score : α → ℝ)
    (hupper :
      ∀ targetRate, targetRate < finiteChernoffRate μ score →
        HasExpUpperBoundWithConst
          (fun n => finiteIidScoreLeftTailProb μ score 0 n) targetRate)
    (hlower :
      ∀ targetRate, finiteChernoffRate μ score < targetRate →
        ∃ C : FiniteIidScorePathLowerCertificate μ score,
          -Real.log C.base < targetRate) :
    FiniteIidScoreCramerCertificate μ score := by
  refine
    { eventually_pos := ?_
      upper_bounds := hupper
      lower_bounds := ?_ }
  · rcases hlower (finiteChernoffRate μ score + 1) (by linarith) with
      ⟨C, _hC⟩
    filter_upwards [C.sample_mass_lower] with n hmass
    have htail_ge :
        C.lowerConst * C.base ^ n /
            (((n.succ : ℕ) : ℝ) ^ C.degree) ≤
          finiteIidScoreLeftTailProb μ score 0 n := by
      exact hmass.trans
        (pmfProduct_sample_mass_le_finiteIidScoreLeftTailProb
          (μ := μ) (score := score) (threshold := 0)
          (sample := C.sample n) (C.sample_tail n))
    have hgeom_pos :
        0 <
          C.lowerConst * C.base ^ n /
            (((n.succ : ℕ) : ℝ) ^ C.degree) := by
      have hbase_pow_pos : 0 < C.base ^ n := pow_pos C.base_pos n
      have hnum_pos : 0 < C.lowerConst * C.base ^ n :=
        mul_pos C.lowerConst_pos hbase_pow_pos
      have hden_pos : 0 < (((n.succ : ℕ) : ℝ) ^ C.degree) := by
        positivity
      exact div_pos hnum_pos hden_pos
    exact lt_of_lt_of_le hgeom_pos htail_ge
  · intro targetRate htarget
    rcases hlower targetRate htarget with ⟨C, hC⟩
    exact C.hasExpLowerBoundWithConst hC

/--
Build the standard finite iid Cramer certificate from a reusable upper-bound
proof and a direct tail-probability lower-bound witness available at every
strictly slower target rate.
-/
theorem finiteIidScoreCramerCertificate_of_tailLower_witnesses
    (μ : PMF α) (score : α → ℝ)
    (hupper :
      ∀ targetRate, targetRate < finiteChernoffRate μ score →
        HasExpUpperBoundWithConst
          (fun n => finiteIidScoreLeftTailProb μ score 0 n) targetRate)
    (hlower :
      ∀ targetRate, finiteChernoffRate μ score < targetRate →
        ∃ C : FiniteIidScoreTailLowerCertificate μ score,
          -Real.log C.base < targetRate) :
    FiniteIidScoreCramerCertificate μ score := by
  refine
    { eventually_pos := ?_
      upper_bounds := hupper
      lower_bounds := ?_ }
  · rcases hlower (finiteChernoffRate μ score + 1) (by linarith) with
      ⟨C, _hC⟩
    filter_upwards [C.tail_prob_lower] with n htail
    have hgeom_pos :
        0 <
          C.lowerConst * C.base ^ n /
            (((n.succ : ℕ) : ℝ) ^ C.degree) := by
      have hbase_pow_pos : 0 < C.base ^ n := pow_pos C.base_pos n
      have hnum_pos : 0 < C.lowerConst * C.base ^ n :=
        mul_pos C.lowerConst_pos hbase_pow_pos
      have hden_pos : 0 < (((n.succ : ℕ) : ℝ) ^ C.degree) := by
        positivity
      exact div_pos hnum_pos hden_pos
    exact lt_of_lt_of_le hgeom_pos htail
  · intro targetRate htarget
    rcases hlower targetRate htarget with ⟨C, hC⟩
    exact C.hasExpLowerBoundWithConst hC

/--
Finite iid Cramer certificate specialized to a candidate pair score gap.
-/
abbrev FiniteIidScoreGapCramerCertificate
    (μ : PMF α) (hiScore loScore : α → ℝ) : Prop :=
  FiniteIidScoreCramerCertificate μ
    (fun a => hiScore a - loScore a)

/--
Path lower certificate specialized to a candidate-pair score gap.
-/
abbrev FiniteIidScoreGapPathLowerCertificate
    (μ : PMF α) (hiScore loScore : α → ℝ) : Type _ :=
  FiniteIidScorePathLowerCertificate μ
    (fun a => hiScore a - loScore a)

/--
Direct tail-probability lower certificate specialized to a candidate-pair score
gap.
-/
abbrev FiniteIidScoreGapTailLowerCertificate
    (μ : PMF α) (hiScore loScore : α → ℝ) : Type _ :=
  FiniteIidScoreTailLowerCertificate μ
    (fun a => hiScore a - loScore a)

/--
Score-gap form of `finiteIidScoreCramerCertificate_of_pathLower`.
-/
theorem finiteIidScoreGapCramerCertificate_of_pathLower
    (μ : PMF α) (hiScore loScore : α → ℝ)
    (hupper :
      ∀ targetRate,
        targetRate <
          finiteChernoffRate μ (fun a => hiScore a - loScore a) →
        HasExpUpperBoundWithConst
          (fun n =>
            finiteIidScoreLeftTailProb μ
              (fun a => hiScore a - loScore a) 0 n) targetRate)
    (C : FiniteIidScoreGapPathLowerCertificate μ hiScore loScore)
    (hrate :
      -Real.log C.base =
        finiteChernoffRate μ (fun a => hiScore a - loScore a)) :
    FiniteIidScoreGapCramerCertificate μ hiScore loScore := by
  simpa [FiniteIidScoreGapCramerCertificate,
    FiniteIidScoreGapPathLowerCertificate] using
    finiteIidScoreCramerCertificate_of_pathLower
      (μ := μ) (score := fun a => hiScore a - loScore a)
      hupper
      C hrate

/--
Score-gap form of `finiteIidScoreCramerCertificate_of_tailLower`.
-/
theorem finiteIidScoreGapCramerCertificate_of_tailLower
    (μ : PMF α) (hiScore loScore : α → ℝ)
    (hupper :
      ∀ targetRate,
        targetRate <
          finiteChernoffRate μ (fun a => hiScore a - loScore a) →
        HasExpUpperBoundWithConst
          (fun n =>
            finiteIidScoreLeftTailProb μ
              (fun a => hiScore a - loScore a) 0 n) targetRate)
    (C : FiniteIidScoreGapTailLowerCertificate μ hiScore loScore)
    (hrate :
      -Real.log C.base =
        finiteChernoffRate μ (fun a => hiScore a - loScore a)) :
    FiniteIidScoreGapCramerCertificate μ hiScore loScore := by
  simpa [FiniteIidScoreGapCramerCertificate,
    FiniteIidScoreGapTailLowerCertificate] using
    finiteIidScoreCramerCertificate_of_tailLower
      (μ := μ) (score := fun a => hiScore a - loScore a)
      hupper
      C hrate

/--
Score-gap form of `finiteIidScoreCramerCertificate_of_tilted_window`.
-/
theorem finiteIidScoreGapCramerCertificate_of_tilted_window
    (μ : PMF α) (hiScore loScore : α → ℝ)
    (hupper :
      ∀ targetRate,
        targetRate <
          finiteChernoffRate μ (fun a => hiScore a - loScore a) →
        HasExpUpperBoundWithConst
          (fun n =>
            finiteIidScoreLeftTailProb μ
              (fun a => hiScore a - loScore a) 0 n) targetRate)
    {z windowBound lowerConst : ℝ} {degree : ℕ}
    (hz : z ≤ 0)
    (hlowerConst_pos : 0 < lowerConst)
    (hwindow :
      ∀ᶠ n : ℕ in atTop,
        lowerConst / (((n.succ : ℕ) : ℝ) ^ degree) ≤
          pmfProb
            (pmfProduct (Fin n) α
              (finiteExponentialTilt μ (fun a => hiScore a - loScore a) z))
            (fun sample : Fin n → α =>
              -windowBound ≤
                  finiteIidScoreSum
                    (fun a => hiScore a - loScore a) sample ∧
                finiteIidScoreSum
                    (fun a => hiScore a - loScore a) sample ≤ 0))
    (hrate :
      -Real.log (finiteMGF μ (fun a => hiScore a - loScore a) z) =
        finiteChernoffRate μ (fun a => hiScore a - loScore a)) :
    FiniteIidScoreGapCramerCertificate μ hiScore loScore := by
  simpa [FiniteIidScoreGapCramerCertificate] using
    finiteIidScoreCramerCertificate_of_tilted_window
      (μ := μ) (score := fun a => hiScore a - loScore a)
      hupper hz hlowerConst_pos hwindow hrate

/--
Score-gap tilted-window Cramer certificate with the Chernoff upper side
discharged by nonnegative mean and positive-mass gap atoms.
-/
theorem finiteIidScoreGapCramerCertificate_of_tilted_window_of_mean_nonneg_pos_neg_atoms
    (μ : PMF α) (hiScore loScore : α → ℝ)
    (hmean : 0 ≤ pmfExp μ (fun a => hiScore a - loScore a))
    {aPos aNeg : α}
    (hmassPos : 0 < (μ aPos).toReal)
    (hgapPos : 0 < hiScore aPos - loScore aPos)
    (hmassNeg : 0 < (μ aNeg).toReal)
    (hgapNeg : hiScore aNeg - loScore aNeg < 0)
    {z windowBound lowerConst : ℝ} {degree : ℕ}
    (hz : z ≤ 0)
    (hlowerConst_pos : 0 < lowerConst)
    (hwindow :
      ∀ᶠ n : ℕ in atTop,
        lowerConst / (((n.succ : ℕ) : ℝ) ^ degree) ≤
          pmfProb
            (pmfProduct (Fin n) α
              (finiteExponentialTilt μ (fun a => hiScore a - loScore a) z))
            (fun sample : Fin n → α =>
              -windowBound ≤
                  finiteIidScoreSum
                    (fun a => hiScore a - loScore a) sample ∧
                finiteIidScoreSum
                    (fun a => hiScore a - loScore a) sample ≤ 0))
    (hrate :
      -Real.log (finiteMGF μ (fun a => hiScore a - loScore a) z) =
        finiteChernoffRate μ (fun a => hiScore a - loScore a)) :
    FiniteIidScoreGapCramerCertificate μ hiScore loScore := by
  simpa [FiniteIidScoreGapCramerCertificate] using
    finiteIidScoreCramerCertificate_of_tilted_window_of_mean_nonneg_pos_neg_atoms
      (μ := μ) (score := fun a => hiScore a - loScore a)
      hmean hmassPos hgapPos hmassNeg hgapNeg
      hz hlowerConst_pos hwindow hrate

/--
Score-gap form of
`finiteIidScoreCramerCertificate_of_stationary_tilted_window_of_mean_nonneg_pos_neg_atoms`.
-/
theorem finiteIidScoreGapCramerCertificate_of_stationary_tilted_window_of_mean_nonneg_pos_neg_atoms
    (μ : PMF α) (hiScore loScore : α → ℝ)
    (hmean : 0 ≤ pmfExp μ (fun a => hiScore a - loScore a))
    {aPos aNeg : α}
    (hmassPos : 0 < (μ aPos).toReal)
    (hgapPos : 0 < hiScore aPos - loScore aPos)
    (hmassNeg : 0 < (μ aNeg).toReal)
    (hgapNeg : hiScore aNeg - loScore aNeg < 0)
    {z windowBound lowerConst : ℝ} {degree : ℕ}
    (hz : z ≤ 0)
    (hstationary :
      (∑ a : α,
        (μ a).toReal *
          ((hiScore a - loScore a) *
            Real.exp (z * (hiScore a - loScore a)))) = 0)
    (hlowerConst_pos : 0 < lowerConst)
    (hwindow :
      ∀ᶠ n : ℕ in atTop,
        lowerConst / (((n.succ : ℕ) : ℝ) ^ degree) ≤
          pmfProb
            (pmfProduct (Fin n) α
              (finiteExponentialTilt μ (fun a => hiScore a - loScore a) z))
            (fun sample : Fin n → α =>
              -windowBound ≤
                  finiteIidScoreSum
                    (fun a => hiScore a - loScore a) sample ∧
                finiteIidScoreSum
                    (fun a => hiScore a - loScore a) sample ≤ 0)) :
    FiniteIidScoreGapCramerCertificate μ hiScore loScore := by
  simpa [FiniteIidScoreGapCramerCertificate] using
    finiteIidScoreCramerCertificate_of_stationary_tilted_window_of_mean_nonneg_pos_neg_atoms
      (μ := μ) (score := fun a => hiScore a - loScore a)
      hmean hmassPos hgapPos hmassNeg hgapNeg
      hz hstationary hlowerConst_pos hwindow

/--
Score-gap form of `finiteIidScoreCramerCertificate_of_pathLower_witnesses`.
-/
theorem finiteIidScoreGapCramerCertificate_of_pathLower_witnesses
    (μ : PMF α) (hiScore loScore : α → ℝ)
    (hupper :
      ∀ targetRate,
        targetRate <
          finiteChernoffRate μ (fun a => hiScore a - loScore a) →
        HasExpUpperBoundWithConst
          (fun n =>
            finiteIidScoreLeftTailProb μ
              (fun a => hiScore a - loScore a) 0 n) targetRate)
    (hlower :
      ∀ targetRate,
        finiteChernoffRate μ (fun a => hiScore a - loScore a) <
          targetRate →
        ∃ C : FiniteIidScoreGapPathLowerCertificate μ hiScore loScore,
          -Real.log C.base < targetRate) :
    FiniteIidScoreGapCramerCertificate μ hiScore loScore := by
  simpa [FiniteIidScoreGapCramerCertificate,
    FiniteIidScoreGapPathLowerCertificate] using
    finiteIidScoreCramerCertificate_of_pathLower_witnesses
      (μ := μ) (score := fun a => hiScore a - loScore a)
      hupper hlower

/--
Score-gap form of `finiteIidScoreCramerCertificate_of_tailLower_witnesses`.
-/
theorem finiteIidScoreGapCramerCertificate_of_tailLower_witnesses
    (μ : PMF α) (hiScore loScore : α → ℝ)
    (hupper :
      ∀ targetRate,
        targetRate <
          finiteChernoffRate μ (fun a => hiScore a - loScore a) →
        HasExpUpperBoundWithConst
          (fun n =>
            finiteIidScoreLeftTailProb μ
              (fun a => hiScore a - loScore a) 0 n) targetRate)
    (hlower :
      ∀ targetRate,
        finiteChernoffRate μ (fun a => hiScore a - loScore a) <
          targetRate →
        ∃ C : FiniteIidScoreGapTailLowerCertificate μ hiScore loScore,
          -Real.log C.base < targetRate) :
    FiniteIidScoreGapCramerCertificate μ hiScore loScore := by
  simpa [FiniteIidScoreGapCramerCertificate,
    FiniteIidScoreGapTailLowerCertificate] using
    finiteIidScoreCramerCertificate_of_tailLower_witnesses
      (μ := μ) (score := fun a => hiScore a - loScore a)
      hupper hlower

/--
Pairwise finite iid score-gap mistake probability for a common voter law.
-/
def finiteIidPairwiseScoreGapLeftTailProb
    {Candidate : Type*}
    (μ : PMF α) (score : Candidate → α → ℝ)
    (hi lo : Candidate) (n : ℕ) : ℝ :=
  finiteIidScoreLeftTailProb μ
    (fun a => score hi a - score lo a) 0 n

/-- Pairwise finite iid score-gap Chernoff exponent for a common voter law. -/
def finiteIidPairwiseScoreGapChernoffRate
    {Candidate : Type*}
    (μ : PMF α) (score : Candidate → α → ℝ)
    (hi lo : Candidate) : ℝ :=
  finiteChernoffRate μ (fun a => score hi a - score lo a)

/--
Build a pairwise exact-rate certificate from finite iid Cramer certificates for
each ordered candidate pair.
-/
def finiteIidPairwiseScoreGapRateCertificate
    {Candidate : Type*} [Fintype Candidate]
    (μ : PMF α) (score : Candidate → α → ℝ)
    (cramer :
      ∀ hi lo : Candidate,
        FiniteIidScoreGapCramerCertificate μ (score hi) (score lo)) :
    PairwiseErrorRateCertificate Candidate where
  errorProb := finiteIidPairwiseScoreGapLeftTailProb μ score
  rate := finiteIidPairwiseScoreGapChernoffRate μ score
  has_rate := by
    intro hi lo
    simpa [finiteIidPairwiseScoreGapLeftTailProb,
      finiteIidPairwiseScoreGapChernoffRate,
      FiniteIidScoreGapCramerCertificate] using
      (cramer hi lo).exponentialRateCertificate

/--
Ternary approval-gap specialization of the finite iid Chernoff upper bound.
The assumption `hmgf` connects a concrete finite score law to the algebraic
ternary MGF with plus, minus, and zero probabilities.
-/
theorem finiteIidScoreLeftTail_hasExpUpperBoundWithConst_of_ternaryGapMGF
    (μ : PMF α) (score : α → ℝ) {pUp pDown : ℝ}
    (hUp : 0 < pUp) (hDown : 0 < pDown)
    (hle : pDown ≤ pUp) (hsum : pUp + pDown ≤ 1)
    (hmgf :
      finiteMGF μ score (ternaryGapChernoffDual pUp pDown) =
        ternaryGapMGF pUp pDown (ternaryGapChernoffDual pUp pDown)) :
    HasExpUpperBoundWithConst
      (fun n => finiteIidScoreLeftTailProb μ score 0 n)
      (ternaryGapClosedChernoffRate pUp pDown) := by
  refine
    finiteIidScoreLeftTail_hasExpUpperBoundWithConst_of_mgf_le_exp_neg
      (μ := μ) (score := score)
      (z := ternaryGapChernoffDual pUp pDown)
      (rate := ternaryGapClosedChernoffRate pUp pDown)
      (ternaryGapChernoffDual_nonpos hUp hDown hle)
      ?_
  calc
    finiteMGF μ score (ternaryGapChernoffDual pUp pDown)
        = ternaryGapMGF pUp pDown (ternaryGapChernoffDual pUp pDown) :=
          hmgf
    _ = Real.exp (-(ternaryGapClosedChernoffRate pUp pDown)) :=
          ternaryGapMGF_chernoffDual_eq_exp_neg_closedRate
            hUp hDown hsum
    _ ≤ Real.exp (-(ternaryGapClosedChernoffRate pUp pDown)) :=
          le_rfl

/--
For an actual finite ternary score law, the abstract finite Chernoff exponent
coincides with the closed ternary approval-gap exponent.
-/
theorem finiteChernoffRate_eq_ternaryGapClosedChernoffRate_of_ternary_scores
    (μ : PMF α) (score : α → ℝ) {pUp pDown : ℝ}
    (hUp : 0 < pUp) (hDown : 0 < pDown)
    (hscore : ∀ a, score a = 1 ∨ score a = 0 ∨ score a = -1)
    (hUpProb : pmfProb μ (fun a => score a = 1) = pUp)
    (hDownProb : pmfProb μ (fun a => score a = -1) = pDown) :
    finiteChernoffRate μ score = ternaryGapClosedChernoffRate pUp pDown := by
  classical
  let up : α → Prop := fun a => score a = 1
  let down : α → Prop := fun a => score a = -1
  have hdisj : ∀ a, up a → down a → False := by
    intro a hup hdown
    have : (1 : ℝ) = -1 := hup.symm.trans hdown
    norm_num at this
  have hzero_prob :
      pmfProb μ (fun a => ¬up a ∧ ¬down a) =
        1 - pUp - pDown := by
    have hsplit :=
      pmfProb_not_and_not_eq_one_sub_add_of_disjoint μ up down hdisj
    simpa [up, down, hUpProb, hDownProb] using hsplit
  have hsum : pUp + pDown ≤ 1 := by
    have hnonneg :
        0 ≤ pmfProb μ (fun a => ¬up a ∧ ¬down a) :=
      pmfProb_nonneg μ (fun a => ¬up a ∧ ¬down a)
    rw [hzero_prob] at hnonneg
    linarith
  have hlog_eq :
      (fun z : ℝ => finiteLogMGF μ score z) =
        fun z : ℝ => ternaryGapLogMGF pUp pDown z := by
    funext z
    rw [finiteLogMGF, ternaryGapLogMGF,
      finiteMGF_eq_ternaryGapMGF_of_score_eq_ternary
        μ score hscore hUpProb hDownProb z]
  rw [finiteChernoffRate, hlog_eq]
  exact (ternaryGapClosedChernoffRate_eq_neg_sInf_logMGF hUp hDown hsum).symm

/--
Ternary finite-score lower bound at every rate above the closed ternary
Chernoff exponent.
-/
theorem finiteIidScoreLeftTail_hasExpLowerBoundWithConst_of_ternary_scores
    (μ : PMF α) (score : α → ℝ) {pUp pDown : ℝ}
    (hUp : 0 < pUp) (hDown : 0 < pDown)
    (hle : pDown ≤ pUp)
    (hscore : ∀ a, score a = 1 ∨ score a = 0 ∨ score a = -1)
    (hUpProb : pmfProb μ (fun a => score a = 1) = pUp)
    (hDownProb : pmfProb μ (fun a => score a = -1) = pDown) :
    ∀ targetRate, ternaryGapClosedChernoffRate pUp pDown < targetRate →
      HasExpLowerBoundWithConst
        (fun n => finiteIidScoreLeftTailProb μ score 0 n) targetRate := by
  classical
  let up : α → Prop := fun a => score a = 1
  let down : α → Prop := fun a => score a = -1
  have hdisj : ∀ a, up a → down a → False := by
    intro a hup hdown
    have : (1 : ℝ) = -1 := hup.symm.trans hdown
    norm_num at this
  have hzero_prob :
      pmfProb μ (fun a => ¬up a ∧ ¬down a) =
        1 - pUp - pDown := by
    have hsplit :=
      pmfProb_not_and_not_eq_one_sub_add_of_disjoint μ up down hdisj
    simpa [up, down, hUpProb, hDownProb] using hsplit
  have hsum : pUp + pDown ≤ 1 := by
    have hnonneg :
        0 ≤ pmfProb μ (fun a => ¬up a ∧ ¬down a) :=
      pmfProb_nonneg μ (fun a => ¬up a ∧ ¬down a)
    rw [hzero_prob] at hnonneg
    linarith
  have hbase_pos :
      0 < 2 * Real.sqrt (pUp * pDown) + 1 - pUp - pDown :=
    ternaryGap_closedExpr_pos hUp hDown hsum
  intro targetRate htarget
  refine
    HasExpLowerBoundWithConst.of_eventually_geometric_div_polynomial_lower
      2 (Real.sqrt_pos.mpr (div_pos hDown hUp)) hbase_pos ?_ ?_
  · simpa [ternaryGapClosedChernoffRate] using htarget
  · exact Filter.Eventually.of_forall (fun n => by
      have hbase_eq :
          2 * Real.sqrt (pUp * pDown) + 1 - pUp - pDown =
            2 * Real.sqrt (pUp * pDown) + (1 - pUp - pDown) := by
        ring
      have h :=
        finiteIidScoreLeftTailProb_ge_ternary_base_div_succ_sq
          (μ := μ) (score := score) hUp hDown hle hscore hUpProb hDownProb n
      simpa [hbase_eq, Nat.succ_eq_add_one] using h)

/--
Finite iid Cramer certificate for nondegenerate ternary scores with
`0 < pDown <= pUp`.
-/
theorem finiteIidScoreCramerCertificate_of_ternary_scores
    (μ : PMF α) (score : α → ℝ) {pUp pDown : ℝ}
    (hUp : 0 < pUp) (hDown : 0 < pDown)
    (hle : pDown ≤ pUp)
    (hscore : ∀ a, score a = 1 ∨ score a = 0 ∨ score a = -1)
    (hUpProb : pmfProb μ (fun a => score a = 1) = pUp)
    (hDownProb : pmfProb μ (fun a => score a = -1) = pDown) :
    FiniteIidScoreCramerCertificate μ score := by
  classical
  let up : α → Prop := fun a => score a = 1
  let down : α → Prop := fun a => score a = -1
  have hdisj : ∀ a, up a → down a → False := by
    intro a hup hdown
    have : (1 : ℝ) = -1 := hup.symm.trans hdown
    norm_num at this
  have hzero_prob :
      pmfProb μ (fun a => ¬up a ∧ ¬down a) =
        1 - pUp - pDown := by
    have hsplit :=
      pmfProb_not_and_not_eq_one_sub_add_of_disjoint μ up down hdisj
    simpa [up, down, hUpProb, hDownProb] using hsplit
  have hsum : pUp + pDown ≤ 1 := by
    have hnonneg :
        0 ≤ pmfProb μ (fun a => ¬up a ∧ ¬down a) :=
      pmfProb_nonneg μ (fun a => ¬up a ∧ ¬down a)
    rw [hzero_prob] at hnonneg
    linarith
  have hrate :
      finiteChernoffRate μ score =
        ternaryGapClosedChernoffRate pUp pDown :=
    finiteChernoffRate_eq_ternaryGapClosedChernoffRate_of_ternary_scores
      μ score hUp hDown hscore hUpProb hDownProb
  refine
    { eventually_pos := ?_
      upper_bounds := ?_
      lower_bounds := ?_ }
  · have hevent_pos : 0 < pmfProb μ (fun a => score a = -1) := by
      rw [hDownProb]
      exact hDown
    exact
      finiteIidScoreLeftTailProb_eventually_pos_of_event
        (μ := μ) (score := score)
        (event := fun a => score a = -1)
        (threshold := 0)
        hevent_pos
        (by
          intro n sample hall
          unfold finiteIidScoreSum
          calc
            ∑ i : Fin n, score (sample i)
                = ∑ _i : Fin n, (-1 : ℝ) := by
                    exact Finset.sum_congr rfl (fun i _ => hall i)
            _ = -(n : ℝ) := by
                    simp [Finset.sum_const, nsmul_eq_mul]
            _ ≤ 0 := by
                    exact neg_nonpos.mpr (Nat.cast_nonneg n))
  · intro targetRate htarget
    have htarget_closed :
        targetRate < ternaryGapClosedChernoffRate pUp pDown := by
      simpa [hrate] using htarget
    have hmgf :
        finiteMGF μ score (ternaryGapChernoffDual pUp pDown) =
          ternaryGapMGF pUp pDown (ternaryGapChernoffDual pUp pDown) :=
      finiteMGF_eq_ternaryGapMGF_of_score_eq_ternary
        μ score hscore hUpProb hDownProb (ternaryGapChernoffDual pUp pDown)
    exact
      HasExpUpperBoundWithConst.weaken_rate
        (finiteIidScoreLeftTail_hasExpUpperBoundWithConst_of_ternaryGapMGF
          μ score hUp hDown hle hsum hmgf)
        (le_of_lt htarget_closed)
  · intro targetRate htarget
    have htarget_closed :
        ternaryGapClosedChernoffRate pUp pDown < targetRate := by
      simpa [hrate] using htarget
    exact
      finiteIidScoreLeftTail_hasExpLowerBoundWithConst_of_ternary_scores
        μ score hUp hDown hle hscore hUpProb hDownProb
        targetRate htarget_closed

/-- Pairwise finite score-gap left-tail probability. -/
def finiteIidScoreGapLeftTailProb
    (μ : PMF α) (hiScore loScore : α → ℝ) (n : ℕ) : ℝ :=
  finiteIidScoreLeftTailProb μ (fun a => hiScore a - loScore a) 0 n

/--
Chernoff upper-bound certificate for a finite iid score-gap law from one
nonpositive dual parameter.
-/
theorem finiteIidScoreGapLeftTail_hasExpUpperBoundWithConst_of_dual
    (μ : PMF α) (hiScore loScore : α → ℝ) {z : ℝ}
    (hz : z ≤ 0) :
    HasExpUpperBoundWithConst
      (finiteIidScoreGapLeftTailProb μ hiScore loScore)
      (-(finiteLogMGF μ (fun a => hiScore a - loScore a) z)) := by
  simpa [finiteIidScoreGapLeftTailProb] using
    finiteIidScoreLeftTail_hasExpUpperBoundWithConst_of_mgf_le_exp_neg
      (μ := μ) (score := fun a => hiScore a - loScore a)
      (z := z)
      (rate := -(finiteLogMGF μ (fun a => hiScore a - loScore a) z))
      hz
      (by
        rw [neg_neg]
        exact le_of_eq (exp_finiteLogMGF μ
          (fun a => hiScore a - loScore a) z).symm)

/--
Score-gap form of
`finiteIidScoreLeftTail_hasExpUpperBoundWithConst_of_nonpos_dual_rate_le`.
-/
theorem finiteIidScoreGapLeftTail_hasExpUpperBoundWithConst_of_nonpos_dual_rate_le
    (μ : PMF α) (hiScore loScore : α → ℝ) {z rate : ℝ}
    (hz : z ≤ 0)
    (hrate :
      rate ≤ -finiteLogMGF μ (fun a => hiScore a - loScore a) z) :
    HasExpUpperBoundWithConst
      (finiteIidScoreGapLeftTailProb μ hiScore loScore) rate := by
  simpa [finiteIidScoreGapLeftTailProb] using
    finiteIidScoreLeftTail_hasExpUpperBoundWithConst_of_nonpos_dual_rate_le
      (μ := μ) (score := fun a => hiScore a - loScore a)
      (z := z) (rate := rate) hz hrate

/--
Score-gap form of `finiteIidScoreLeftTail_upperBounds_of_lt_chernoffRate`.
-/
theorem finiteIidScoreGapLeftTail_upperBounds_of_lt_chernoffRate
    (μ : PMF α) (hiScore loScore : α → ℝ)
    (hmean : 0 ≤ pmfExp μ (fun a => hiScore a - loScore a))
    (hbdd :
      BddBelow (Set.range fun z : ℝ =>
        finiteLogMGF μ (fun a => hiScore a - loScore a) z)) :
    ∀ targetRate,
      targetRate < finiteChernoffRate μ (fun a => hiScore a - loScore a) →
        HasExpUpperBoundWithConst
          (finiteIidScoreGapLeftTailProb μ hiScore loScore) targetRate := by
  intro targetRate htarget
  simpa [finiteIidScoreGapLeftTailProb] using
    finiteIidScoreLeftTail_upperBounds_of_lt_chernoffRate
      (μ := μ) (score := fun a => hiScore a - loScore a)
      hmean hbdd targetRate htarget

/--
Score-gap form of
`finiteIidScoreLeftTail_upperBounds_of_lt_chernoffRate_of_pos_neg_atoms`.
-/
theorem finiteIidScoreGapLeftTail_upperBounds_of_lt_chernoffRate_of_pos_neg_atoms
    (μ : PMF α) (hiScore loScore : α → ℝ)
    (hmean : 0 ≤ pmfExp μ (fun a => hiScore a - loScore a))
    {aPos aNeg : α}
    (hmassPos : 0 < (μ aPos).toReal)
    (hgapPos : 0 < hiScore aPos - loScore aPos)
    (hmassNeg : 0 < (μ aNeg).toReal)
    (hgapNeg : hiScore aNeg - loScore aNeg < 0) :
    ∀ targetRate,
      targetRate < finiteChernoffRate μ (fun a => hiScore a - loScore a) →
        HasExpUpperBoundWithConst
          (finiteIidScoreGapLeftTailProb μ hiScore loScore) targetRate := by
  intro targetRate htarget
  simpa [finiteIidScoreGapLeftTailProb] using
    finiteIidScoreLeftTail_upperBounds_of_lt_chernoffRate_of_pos_neg_atoms
      (μ := μ) (score := fun a => hiScore a - loScore a)
      hmean hmassPos hgapPos hmassNeg hgapNeg targetRate htarget

/--
Positive expected one-voter score gap gives some strictly positive exponential
upper-bound rate for the finite iid score-gap left-tail probability.
-/
theorem finiteIidScoreGapLeftTail_exists_pos_expUpperBoundWithConst_of_pmfExp_gap_pos
    (μ : PMF α) (hiScore loScore : α → ℝ)
    (hmean : 0 < pmfExp μ (fun a => hiScore a - loScore a)) :
    ∃ rate : ℝ,
      0 < rate ∧
        HasExpUpperBoundWithConst
          (finiteIidScoreGapLeftTailProb μ hiScore loScore) rate := by
  simpa [finiteIidScoreGapLeftTailProb] using
    finiteIidScoreLeftTail_exists_pos_expUpperBoundWithConst_of_pmfExp_pos
      (μ := μ) (score := fun a => hiScore a - loScore a) hmean

/--
Exact exponential-rate certificate for a finite iid score-gap left-tail
probability from a reusable finite iid Cramer certificate.
-/
theorem finiteIidScoreGapLeftTail_exponentialRateCertificate_of_cramer
    (μ : PMF α) (hiScore loScore : α → ℝ)
    (C : FiniteIidScoreGapCramerCertificate μ hiScore loScore) :
    ExponentialRateCertificate
      (finiteIidScoreGapLeftTailProb μ hiScore loScore)
      (finiteScoreGapChernoffRate μ hiScore loScore) := by
  simpa [finiteIidScoreGapLeftTailProb, finiteScoreGapChernoffRate,
    FiniteIidScoreGapCramerCertificate] using
    C.exponentialRateCertificate

/--
Exact exponential-rate certificate for a finite iid score-gap left tail from
an explicit path lower certificate and an externally supplied Chernoff upper
side.
-/
theorem finiteIidScoreGapLeftTail_exponentialRateCertificate_of_pathLower
    (μ : PMF α) (hiScore loScore : α → ℝ)
    (hupper :
      ∀ targetRate,
        targetRate < finiteScoreGapChernoffRate μ hiScore loScore →
        HasExpUpperBoundWithConst
          (finiteIidScoreGapLeftTailProb μ hiScore loScore) targetRate)
    (C : FiniteIidScoreGapPathLowerCertificate μ hiScore loScore)
    (hrate :
      -Real.log C.base = finiteScoreGapChernoffRate μ hiScore loScore) :
    ExponentialRateCertificate
      (finiteIidScoreGapLeftTailProb μ hiScore loScore)
      (finiteScoreGapChernoffRate μ hiScore loScore) := by
  refine finiteIidScoreGapLeftTail_exponentialRateCertificate_of_cramer
    μ hiScore loScore ?_
  exact
    finiteIidScoreGapCramerCertificate_of_pathLower
      μ hiScore loScore
      (fun targetRate htarget => by
        simpa [finiteIidScoreGapLeftTailProb] using
          hupper targetRate
            (by simpa [finiteScoreGapChernoffRate] using htarget))
      C
      (by simpa [finiteScoreGapChernoffRate] using hrate)

/--
Exact exponential-rate certificate for a finite iid score-gap left tail from
a direct tail-probability lower certificate and an externally supplied Chernoff
upper side.
-/
theorem finiteIidScoreGapLeftTail_exponentialRateCertificate_of_tailLower
    (μ : PMF α) (hiScore loScore : α → ℝ)
    (hupper :
      ∀ targetRate,
        targetRate < finiteScoreGapChernoffRate μ hiScore loScore →
        HasExpUpperBoundWithConst
          (finiteIidScoreGapLeftTailProb μ hiScore loScore) targetRate)
    (C : FiniteIidScoreGapTailLowerCertificate μ hiScore loScore)
    (hrate :
      -Real.log C.base = finiteScoreGapChernoffRate μ hiScore loScore) :
    ExponentialRateCertificate
      (finiteIidScoreGapLeftTailProb μ hiScore loScore)
      (finiteScoreGapChernoffRate μ hiScore loScore) := by
  refine finiteIidScoreGapLeftTail_exponentialRateCertificate_of_cramer
    μ hiScore loScore ?_
  exact
    finiteIidScoreGapCramerCertificate_of_tailLower
      μ hiScore loScore
      (fun targetRate htarget => by
        simpa [finiteIidScoreGapLeftTailProb] using
          hupper targetRate
            (by simpa [finiteScoreGapChernoffRate] using htarget))
      C
      (by simpa [finiteScoreGapChernoffRate] using hrate)

/--
Exact exponential-rate certificate for a finite iid score-gap left tail from a
bounded-window lower bound under an exponential tilt.
-/
theorem finiteIidScoreGapLeftTail_exponentialRateCertificate_of_tilted_window
    (μ : PMF α) (hiScore loScore : α → ℝ)
    (hupper :
      ∀ targetRate,
        targetRate < finiteScoreGapChernoffRate μ hiScore loScore →
        HasExpUpperBoundWithConst
          (finiteIidScoreGapLeftTailProb μ hiScore loScore) targetRate)
    {z windowBound lowerConst : ℝ} {degree : ℕ}
    (hz : z ≤ 0)
    (hlowerConst_pos : 0 < lowerConst)
    (hwindow :
      ∀ᶠ n : ℕ in atTop,
        lowerConst / (((n.succ : ℕ) : ℝ) ^ degree) ≤
          pmfProb
            (pmfProduct (Fin n) α
              (finiteExponentialTilt μ (fun a => hiScore a - loScore a) z))
            (fun sample : Fin n → α =>
              -windowBound ≤
                  finiteIidScoreSum
                    (fun a => hiScore a - loScore a) sample ∧
                finiteIidScoreSum
                    (fun a => hiScore a - loScore a) sample ≤ 0))
    (hrate :
      -Real.log (finiteMGF μ (fun a => hiScore a - loScore a) z) =
        finiteScoreGapChernoffRate μ hiScore loScore) :
    ExponentialRateCertificate
      (finiteIidScoreGapLeftTailProb μ hiScore loScore)
      (finiteScoreGapChernoffRate μ hiScore loScore) := by
  refine finiteIidScoreGapLeftTail_exponentialRateCertificate_of_cramer
    μ hiScore loScore ?_
  exact
    finiteIidScoreGapCramerCertificate_of_tilted_window
      μ hiScore loScore
      (fun targetRate htarget => by
        simpa [finiteIidScoreGapLeftTailProb] using
          hupper targetRate
            (by simpa [finiteScoreGapChernoffRate] using htarget))
      hz hlowerConst_pos hwindow
      (by simpa [finiteScoreGapChernoffRate] using hrate)

/--
Exact finite iid score-gap left-tail rate from a path lower certificate, with
the Chernoff upper side discharged by nonnegative mean and bounded-below
finite log-MGF range.
-/
theorem finiteIidScoreGapLeftTail_exponentialRateCertificate_of_pathLower_of_mean_nonneg
    (μ : PMF α) (hiScore loScore : α → ℝ)
    (hmean : 0 ≤ pmfExp μ (fun a => hiScore a - loScore a))
    (hbdd :
      BddBelow (Set.range fun z : ℝ =>
        finiteLogMGF μ (fun a => hiScore a - loScore a) z))
    (C : FiniteIidScoreGapPathLowerCertificate μ hiScore loScore)
    (hrate :
      -Real.log C.base = finiteScoreGapChernoffRate μ hiScore loScore) :
    ExponentialRateCertificate
      (finiteIidScoreGapLeftTailProb μ hiScore loScore)
      (finiteScoreGapChernoffRate μ hiScore loScore) :=
  finiteIidScoreGapLeftTail_exponentialRateCertificate_of_pathLower
    μ hiScore loScore
    (fun targetRate htarget => by
      simpa [finiteScoreGapChernoffRate] using
        finiteIidScoreGapLeftTail_upperBounds_of_lt_chernoffRate
          μ hiScore loScore hmean hbdd targetRate
          (by simpa [finiteScoreGapChernoffRate] using htarget))
    C hrate

/--
Exact finite iid score-gap left-tail rate from a tail lower certificate, with
the Chernoff upper side discharged by nonnegative mean and bounded-below
finite log-MGF range.
-/
theorem finiteIidScoreGapLeftTail_exponentialRateCertificate_of_tailLower_of_mean_nonneg
    (μ : PMF α) (hiScore loScore : α → ℝ)
    (hmean : 0 ≤ pmfExp μ (fun a => hiScore a - loScore a))
    (hbdd :
      BddBelow (Set.range fun z : ℝ =>
        finiteLogMGF μ (fun a => hiScore a - loScore a) z))
    (C : FiniteIidScoreGapTailLowerCertificate μ hiScore loScore)
    (hrate :
      -Real.log C.base = finiteScoreGapChernoffRate μ hiScore loScore) :
    ExponentialRateCertificate
      (finiteIidScoreGapLeftTailProb μ hiScore loScore)
      (finiteScoreGapChernoffRate μ hiScore loScore) :=
  finiteIidScoreGapLeftTail_exponentialRateCertificate_of_tailLower
    μ hiScore loScore
    (fun targetRate htarget => by
      simpa [finiteScoreGapChernoffRate] using
        finiteIidScoreGapLeftTail_upperBounds_of_lt_chernoffRate
          μ hiScore loScore hmean hbdd targetRate
          (by simpa [finiteScoreGapChernoffRate] using htarget))
    C hrate

/--
Exact finite iid score-gap left-tail rate from a path lower certificate, with
bounded-below finite log-MGF range discharged by positive-mass atoms on both
sides of zero.
-/
theorem finiteIidScoreGapLeftTail_exponentialRateCertificate_of_pathLower_of_mean_nonneg_pos_neg_atoms
    (μ : PMF α) (hiScore loScore : α → ℝ)
    (hmean : 0 ≤ pmfExp μ (fun a => hiScore a - loScore a))
    {aPos aNeg : α}
    (hmassPos : 0 < (μ aPos).toReal)
    (hgapPos : 0 < hiScore aPos - loScore aPos)
    (hmassNeg : 0 < (μ aNeg).toReal)
    (hgapNeg : hiScore aNeg - loScore aNeg < 0)
    (C : FiniteIidScoreGapPathLowerCertificate μ hiScore loScore)
    (hrate :
      -Real.log C.base = finiteScoreGapChernoffRate μ hiScore loScore) :
    ExponentialRateCertificate
      (finiteIidScoreGapLeftTailProb μ hiScore loScore)
      (finiteScoreGapChernoffRate μ hiScore loScore) :=
  finiteIidScoreGapLeftTail_exponentialRateCertificate_of_pathLower_of_mean_nonneg
    μ hiScore loScore hmean
    (finiteScoreGapLogMGF_bddBelow_of_pos_neg_atoms
      μ hiScore loScore hmassPos hgapPos hmassNeg hgapNeg)
    C hrate

/--
Exact finite iid score-gap left-tail rate from a tail lower certificate, with
bounded-below finite log-MGF range discharged by positive-mass atoms on both
sides of zero.
-/
theorem finiteIidScoreGapLeftTail_exponentialRateCertificate_of_tailLower_of_mean_nonneg_pos_neg_atoms
    (μ : PMF α) (hiScore loScore : α → ℝ)
    (hmean : 0 ≤ pmfExp μ (fun a => hiScore a - loScore a))
    {aPos aNeg : α}
    (hmassPos : 0 < (μ aPos).toReal)
    (hgapPos : 0 < hiScore aPos - loScore aPos)
    (hmassNeg : 0 < (μ aNeg).toReal)
    (hgapNeg : hiScore aNeg - loScore aNeg < 0)
    (C : FiniteIidScoreGapTailLowerCertificate μ hiScore loScore)
    (hrate :
      -Real.log C.base = finiteScoreGapChernoffRate μ hiScore loScore) :
    ExponentialRateCertificate
      (finiteIidScoreGapLeftTailProb μ hiScore loScore)
      (finiteScoreGapChernoffRate μ hiScore loScore) :=
  finiteIidScoreGapLeftTail_exponentialRateCertificate_of_tailLower_of_mean_nonneg
    μ hiScore loScore hmean
    (finiteScoreGapLogMGF_bddBelow_of_pos_neg_atoms
      μ hiScore loScore hmassPos hgapPos hmassNeg hgapNeg)
    C hrate

/--
Ternary approval-gap specialization for pairwise finite score gaps.
-/
theorem finiteIidScoreGapLeftTail_hasExpUpperBoundWithConst_of_ternaryGapMGF
    (μ : PMF α) (hiScore loScore : α → ℝ) {pUp pDown : ℝ}
    (hUp : 0 < pUp) (hDown : 0 < pDown)
    (hle : pDown ≤ pUp) (hsum : pUp + pDown ≤ 1)
    (hmgf :
      finiteMGF μ (fun a => hiScore a - loScore a)
          (ternaryGapChernoffDual pUp pDown) =
        ternaryGapMGF pUp pDown (ternaryGapChernoffDual pUp pDown)) :
    HasExpUpperBoundWithConst
      (finiteIidScoreGapLeftTailProb μ hiScore loScore)
      (ternaryGapClosedChernoffRate pUp pDown) := by
  simpa [finiteIidScoreGapLeftTailProb] using
    finiteIidScoreLeftTail_hasExpUpperBoundWithConst_of_ternaryGapMGF
      (μ := μ) (score := fun a => hiScore a - loScore a)
      hUp hDown hle hsum hmgf

/--
Score-gap form of `finiteIidScoreCramerCertificate_of_ternary_scores`.
-/
theorem finiteIidScoreGapCramerCertificate_of_ternary_scores
    (μ : PMF α) (hiScore loScore : α → ℝ) {pUp pDown : ℝ}
    (hUp : 0 < pUp) (hDown : 0 < pDown)
    (hle : pDown ≤ pUp)
    (hscore :
      ∀ a,
        hiScore a - loScore a = 1 ∨
          hiScore a - loScore a = 0 ∨
          hiScore a - loScore a = -1)
    (hUpProb :
      pmfProb μ (fun a => hiScore a - loScore a = 1) = pUp)
    (hDownProb :
      pmfProb μ (fun a => hiScore a - loScore a = -1) = pDown) :
    FiniteIidScoreGapCramerCertificate μ hiScore loScore := by
  simpa [FiniteIidScoreGapCramerCertificate] using
    finiteIidScoreCramerCertificate_of_ternary_scores
      (μ := μ) (score := fun a => hiScore a - loScore a)
      hUp hDown hle hscore hUpProb hDownProb

/--
Exact exponential-rate certificate for a finite iid ternary score-gap left
tail.  This is the reusable closed form for approval-style gaps: the Chernoff
upper bound comes from the ternary MGF minimizer, and the lower bound comes
from the finite central-layer counting argument.
-/
theorem finiteIidScoreLeftTail_exponentialRateCertificate_of_ternary_scores
    (μ : PMF α) (score : α → ℝ) {pUp pDown : ℝ}
    (hUp : 0 < pUp) (hDown : 0 < pDown)
    (hle : pDown ≤ pUp)
    (hscore : ∀ a, score a = 1 ∨ score a = 0 ∨ score a = -1)
    (hUpProb : pmfProb μ (fun a => score a = 1) = pUp)
    (hDownProb : pmfProb μ (fun a => score a = -1) = pDown) :
    ExponentialRateCertificate
      (fun n => finiteIidScoreLeftTailProb μ score 0 n)
      (ternaryGapClosedChernoffRate pUp pDown) := by
  classical
  let up : α → Prop := fun a => score a = 1
  let down : α → Prop := fun a => score a = -1
  have hdisj : ∀ a, up a → down a → False := by
    intro a hup hdown
    have : (1 : ℝ) = -1 := hup.symm.trans hdown
    norm_num at this
  have hzero_prob :
      pmfProb μ (fun a => ¬up a ∧ ¬down a) =
        1 - pUp - pDown := by
    have hsplit :=
      pmfProb_not_and_not_eq_one_sub_add_of_disjoint μ up down hdisj
    simpa [up, down, hUpProb, hDownProb] using hsplit
  have hsum : pUp + pDown ≤ 1 := by
    have hnonneg :
        0 ≤ pmfProb μ (fun a => ¬up a ∧ ¬down a) :=
      pmfProb_nonneg μ (fun a => ¬up a ∧ ¬down a)
    rw [hzero_prob] at hnonneg
    linarith
  have hbase_pos :
      0 < 2 * Real.sqrt (pUp * pDown) + 1 - pUp - pDown :=
    ternaryGap_closedExpr_pos hUp hDown hsum
  have hpos :
      ∀ᶠ n : ℕ in atTop, 0 < finiteIidScoreLeftTailProb μ score 0 n := by
    have hevent_pos : 0 < pmfProb μ (fun a => score a = -1) := by
      rw [hDownProb]
      exact hDown
    exact
      finiteIidScoreLeftTailProb_eventually_pos_of_event
        (μ := μ) (score := score)
        (event := fun a => score a = -1)
        (threshold := 0)
        hevent_pos
        (by
          intro n sample hall
          unfold finiteIidScoreSum
          calc
            ∑ i : Fin n, score (sample i)
                = ∑ _i : Fin n, (-1 : ℝ) := by
                    exact Finset.sum_congr rfl (fun i _ => hall i)
            _ = -(n : ℝ) := by
                    simp [Finset.sum_const, nsmul_eq_mul]
            _ ≤ 0 := by
                    exact neg_nonpos.mpr (Nat.cast_nonneg n))
  refine ⟨hpos, ?_⟩
  refine hasExponentialRate_of_expUpperLowerBounds hpos ?_ ?_
  · intro targetRate htarget
    have hmgf :
        finiteMGF μ score (ternaryGapChernoffDual pUp pDown) =
          ternaryGapMGF pUp pDown (ternaryGapChernoffDual pUp pDown) :=
      finiteMGF_eq_ternaryGapMGF_of_score_eq_ternary
        μ score hscore hUpProb hDownProb (ternaryGapChernoffDual pUp pDown)
    exact
      HasExpUpperBoundWithConst.weaken_rate
        (finiteIidScoreLeftTail_hasExpUpperBoundWithConst_of_ternaryGapMGF
          μ score hUp hDown hle hsum hmgf)
        (le_of_lt htarget)
  · intro targetRate htarget
    refine
      HasExpLowerBoundWithConst.of_eventually_geometric_div_polynomial_lower
        2 (Real.sqrt_pos.mpr (div_pos hDown hUp)) hbase_pos ?_ ?_
    · simpa [ternaryGapClosedChernoffRate] using htarget
    · exact Filter.Eventually.of_forall (fun n => by
        have hbase_eq :
            2 * Real.sqrt (pUp * pDown) + 1 - pUp - pDown =
              2 * Real.sqrt (pUp * pDown) + (1 - pUp - pDown) := by
          ring
        have h :=
          finiteIidScoreLeftTailProb_ge_ternary_base_div_succ_sq
            (μ := μ) (score := score) hUp hDown hle hscore hUpProb hDownProb n
        simpa [hbase_eq, Nat.succ_eq_add_one] using h)

/--
Score-gap form of
`finiteIidScoreLeftTail_exponentialRateCertificate_of_ternary_scores`.
-/
theorem finiteIidScoreGapLeftTail_exponentialRateCertificate_of_ternary_scores
    (μ : PMF α) (hiScore loScore : α → ℝ) {pUp pDown : ℝ}
    (hUp : 0 < pUp) (hDown : 0 < pDown)
    (hle : pDown ≤ pUp)
    (hscore :
      ∀ a,
        hiScore a - loScore a = 1 ∨
          hiScore a - loScore a = 0 ∨
          hiScore a - loScore a = -1)
    (hUpProb :
      pmfProb μ (fun a => hiScore a - loScore a = 1) = pUp)
    (hDownProb :
      pmfProb μ (fun a => hiScore a - loScore a = -1) = pDown) :
    ExponentialRateCertificate
      (finiteIidScoreGapLeftTailProb μ hiScore loScore)
      (ternaryGapClosedChernoffRate pUp pDown) := by
  simpa [finiteIidScoreGapLeftTailProb] using
    finiteIidScoreLeftTail_exponentialRateCertificate_of_ternary_scores
      (μ := μ) (score := fun a => hiScore a - loScore a)
      hUp hDown hle hscore hUpProb hDownProb

end

end Probability
end AppliedModelingLib
