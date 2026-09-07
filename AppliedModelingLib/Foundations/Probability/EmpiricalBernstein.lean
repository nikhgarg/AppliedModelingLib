import AppliedModelingLib.Foundations.Probability.EmpiricalVarianceSelfBounding
import AppliedModelingLib.Foundations.Probability.FiniteBennett
import AppliedModelingLib.Foundations.Probability.FiniteHerbst
import AppliedModelingLib.Foundations.Probability.FiniteSelfBoundingLowerTail

/-!
# Finite empirical-variance concentration

This module instantiates the checked finite self-bounding tail theorem for
Maurer--Pontil's literal statistic `Z = n V_n` on a finite iid product.
-/

namespace AppliedModelingLib

/-- Maurer--Pontil's upper self-bounding tail for the literal scaled unbiased
sample variance `Z = n V_n` of a finite `[0,1]`-valued iid sample. -/
theorem finiteSampleValueScaledPairwiseVariance_upperTail
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}
    (law : PMF α) (statistic : α → ℝ) (hn : 2 ≤ n)
    (hunit : ∀ value, 0 ≤ statistic value ∧ statistic value ≤ 1)
    {threshold : ℝ} (hthreshold : 0 < threshold) :
    pmfProb (pmfProduct (Fin n) α law)
        (fun sample =>
          pmfExp (pmfProduct (Fin n) α law)
              (finiteSampleValueScaledPairwiseVariance statistic) + threshold <
            finiteSampleValueScaledPairwiseVariance statistic sample) ≤
      Real.exp (-threshold ^ 2 /
        (2 * ((n : ℝ) / ((n : ℝ) - 1)) *
            pmfExp (pmfProduct (Fin n) α law)
              (finiteSampleValueScaledPairwiseVariance statistic) +
          ((n : ℝ) / ((n : ℝ) - 1)) * threshold)) := by
  have hcount_pos : 0 < (n : ℝ) := by
    exact_mod_cast (show 0 < n from lt_of_lt_of_le (by omega) hn)
  have hden_pos : 0 < (n : ℝ) - 1 := by
    have : (1 : ℝ) < n := by
      exact_mod_cast (show 1 < n from lt_of_lt_of_le (by omega) hn)
    linarith
  have hscale : 0 < (n : ℝ) / ((n : ℝ) - 1) := div_pos hcount_pos hden_pos
  exact FiniteSelfBounding.pmfProb_upperTail_le_exp_all
    (finiteSampleValueScaledPairwiseVariance_isFiniteSelfBounding statistic hn hunit)
    (law := law) hscale hthreshold

/-- Maurer--Pontil's lower self-bounding tail for the literal scaled unbiased
sample variance `Z = n V_n` of a finite `[0,1]`-valued iid sample. -/
theorem finiteSampleValueScaledPairwiseVariance_lowerTail
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}
    (law : PMF α) (statistic : α → ℝ) (hn : 2 ≤ n)
    (hunit : ∀ value, 0 ≤ statistic value ∧ statistic value ≤ 1)
    {threshold : ℝ} (hthreshold : 0 < threshold) :
    pmfProb (pmfProduct (Fin n) α law)
        (fun sample =>
          finiteSampleValueScaledPairwiseVariance statistic sample <
            pmfExp (pmfProduct (Fin n) α law)
              (finiteSampleValueScaledPairwiseVariance statistic) - threshold) ≤
      Real.exp (-threshold ^ 2 /
        (2 * ((n : ℝ) / ((n : ℝ) - 1)) *
          pmfExp (pmfProduct (Fin n) α law)
            (finiteSampleValueScaledPairwiseVariance statistic))) := by
  have hcount_pos : 0 < (n : ℝ) := by
    exact_mod_cast (show 0 < n from lt_of_lt_of_le (by omega) hn)
  have hden_pos : 0 < (n : ℝ) - 1 := by
    have : (1 : ℝ) < n := by
      exact_mod_cast (show 1 < n from lt_of_lt_of_le (by omega) hn)
    linarith
  have hscale : 1 ≤ (n : ℝ) / ((n : ℝ) - 1) := by
    apply (le_div_iff₀ hden_pos).2
    linarith
  exact FiniteSelfBounding.pmfProb_lowerTail_le_exp
    (finiteSampleValueScaledPairwiseVariance_isFiniteSelfBounding statistic hn hunit)
    (law := law) hscale hthreshold

/-- The same upper-tail inequality in the usual unbiased-variance
normalization.  It is obtained by the exact identity `Z = n V_n`, not by a
change of convention. -/
theorem finiteSampleValueUnbiasedVariance_upperTail
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}
    (law : PMF α) (statistic : α → ℝ) (hn : 2 ≤ n)
    (hunit : ∀ value, 0 ≤ statistic value ∧ statistic value ≤ 1)
    {threshold : ℝ} (hthreshold : 0 < threshold) :
    pmfProb (pmfProduct (Fin n) α law)
        (fun sample =>
          pmfExp (pmfProduct (Fin n) α law)
              (fun draw => finiteSampleUnbiasedVariance (statistic ∘ draw)) + threshold <
            finiteSampleUnbiasedVariance (statistic ∘ sample)) ≤
      Real.exp (-((n : ℝ) - 1) * threshold ^ 2 /
        (2 * pmfExp (pmfProduct (Fin n) α law)
            (fun draw => finiteSampleUnbiasedVariance (statistic ∘ draw)) + threshold)) := by
  let productLaw : PMF (Fin n → α) := pmfProduct (Fin n) α law
  let variance : (Fin n → α) → ℝ := fun sample =>
    finiteSampleUnbiasedVariance (statistic ∘ sample)
  let scaled : (Fin n → α) → ℝ :=
    finiteSampleValueScaledPairwiseVariance statistic
  have hcount_pos : 0 < (n : ℝ) := by
    exact_mod_cast (show 0 < n from lt_of_lt_of_le (by omega) hn)
  have hden_pos : 0 < (n : ℝ) - 1 := by
    have : (1 : ℝ) < n := by
      exact_mod_cast (show 1 < n from lt_of_lt_of_le (by omega) hn)
    linarith
  have hscaled (sample : Fin n → α) : scaled sample = (n : ℝ) * variance sample := by
    unfold scaled variance finiteSampleValueScaledPairwiseVariance
      finiteSampleScaledPairwiseVariance
    rw [finiteSamplePairwiseVariance_eq_unbiasedVariance _ hn]
  have hmean : pmfExp productLaw scaled = (n : ℝ) * pmfExp productLaw variance := by
    calc
      pmfExp productLaw scaled = pmfExp productLaw (fun sample => (n : ℝ) * variance sample) :=
        pmfExp_congr productLaw hscaled
      _ = (n : ℝ) * pmfExp productLaw variance :=
        pmfExp_const_mul productLaw (n : ℝ) variance
  have hsource := finiteSampleValueScaledPairwiseVariance_upperTail
    law statistic hn hunit (threshold := (n : ℝ) * threshold)
      (mul_pos hcount_pos hthreshold)
  change pmfProb productLaw
      (fun sample => pmfExp productLaw scaled + (n : ℝ) * threshold < scaled sample) ≤
    Real.exp (-((n : ℝ) * threshold) ^ 2 /
      (2 * ((n : ℝ) / ((n : ℝ) - 1)) * pmfExp productLaw scaled +
        ((n : ℝ) / ((n : ℝ) - 1)) * ((n : ℝ) * threshold))) at hsource
  rw [hmean] at hsource
  have hevent : ∀ sample,
      (n : ℝ) * pmfExp productLaw variance + (n : ℝ) * threshold < scaled sample ↔
        pmfExp productLaw variance + threshold < variance sample := by
    intro sample
    rw [hscaled]
    constructor <;> intro h <;> nlinarith
  rw [pmfProb_congr productLaw hevent] at hsource
  calc
    pmfProb (pmfProduct (Fin n) α law)
        (fun sample =>
          pmfExp (pmfProduct (Fin n) α law)
              (fun draw => finiteSampleUnbiasedVariance (statistic ∘ draw)) + threshold <
            finiteSampleUnbiasedVariance (statistic ∘ sample)) =
        pmfProb productLaw
          (fun sample => pmfExp productLaw variance + threshold < variance sample) := by
      rfl
    _ ≤ Real.exp (-((n : ℝ) * threshold) ^ 2 /
        (2 * ((n : ℝ) / ((n : ℝ) - 1)) * ((n : ℝ) * pmfExp productLaw variance) +
          ((n : ℝ) / ((n : ℝ) - 1)) * ((n : ℝ) * threshold))) := hsource
    _ = Real.exp (-((n : ℝ) - 1) * threshold ^ 2 /
        (2 * pmfExp productLaw variance + threshold)) := by
      congr 1
      field_simp [hcount_pos.ne', hden_pos.ne']
    _ = Real.exp (-((n : ℝ) - 1) * threshold ^ 2 /
        (2 * pmfExp (pmfProduct (Fin n) α law)
            (fun draw => finiteSampleUnbiasedVariance (statistic ∘ draw)) + threshold)) := by
      rfl

/-- The lower self-bounding inequality in the usual unbiased-variance
normalization.  It follows from the literal identity `Z = n V_n`. -/
theorem finiteSampleValueUnbiasedVariance_lowerTail
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}
    (law : PMF α) (statistic : α → ℝ) (hn : 2 ≤ n)
    (hunit : ∀ value, 0 ≤ statistic value ∧ statistic value ≤ 1)
    {threshold : ℝ} (hthreshold : 0 < threshold) :
    pmfProb (pmfProduct (Fin n) α law)
        (fun sample =>
          finiteSampleUnbiasedVariance (statistic ∘ sample) <
            pmfExp (pmfProduct (Fin n) α law)
              (fun draw => finiteSampleUnbiasedVariance (statistic ∘ draw)) - threshold) ≤
      Real.exp (-((n : ℝ) - 1) * threshold ^ 2 /
        (2 * pmfExp (pmfProduct (Fin n) α law)
          (fun draw => finiteSampleUnbiasedVariance (statistic ∘ draw)))) := by
  let productLaw : PMF (Fin n → α) := pmfProduct (Fin n) α law
  let variance : (Fin n → α) → ℝ := fun sample =>
    finiteSampleUnbiasedVariance (statistic ∘ sample)
  let scaled : (Fin n → α) → ℝ :=
    finiteSampleValueScaledPairwiseVariance statistic
  have hcount_pos : 0 < (n : ℝ) := by
    exact_mod_cast (show 0 < n from lt_of_lt_of_le (by omega) hn)
  have hden_pos : 0 < (n : ℝ) - 1 := by
    have : (1 : ℝ) < n := by
      exact_mod_cast (show 1 < n from lt_of_lt_of_le (by omega) hn)
    linarith
  have hscaled (sample : Fin n → α) : scaled sample = (n : ℝ) * variance sample := by
    unfold scaled variance finiteSampleValueScaledPairwiseVariance
      finiteSampleScaledPairwiseVariance
    rw [finiteSamplePairwiseVariance_eq_unbiasedVariance _ hn]
  have hmean : pmfExp productLaw scaled = (n : ℝ) * pmfExp productLaw variance := by
    calc
      pmfExp productLaw scaled = pmfExp productLaw (fun sample => (n : ℝ) * variance sample) :=
        pmfExp_congr productLaw hscaled
      _ = (n : ℝ) * pmfExp productLaw variance :=
        pmfExp_const_mul productLaw (n : ℝ) variance
  have hsource := finiteSampleValueScaledPairwiseVariance_lowerTail
    law statistic hn hunit (threshold := (n : ℝ) * threshold)
      (mul_pos hcount_pos hthreshold)
  change pmfProb productLaw
      (fun sample => scaled sample < pmfExp productLaw scaled - (n : ℝ) * threshold) ≤
    Real.exp (-((n : ℝ) * threshold) ^ 2 /
      (2 * ((n : ℝ) / ((n : ℝ) - 1)) * pmfExp productLaw scaled)) at hsource
  rw [hmean] at hsource
  have hevent : ∀ sample,
      scaled sample < (n : ℝ) * pmfExp productLaw variance - (n : ℝ) * threshold ↔
        variance sample < pmfExp productLaw variance - threshold := by
    intro sample
    rw [hscaled]
    constructor <;> intro h <;> nlinarith
  rw [pmfProb_congr productLaw hevent] at hsource
  calc
    pmfProb (pmfProduct (Fin n) α law)
        (fun sample =>
          finiteSampleUnbiasedVariance (statistic ∘ sample) <
            pmfExp (pmfProduct (Fin n) α law)
              (fun draw => finiteSampleUnbiasedVariance (statistic ∘ draw)) - threshold) =
        pmfProb productLaw
          (fun sample => variance sample < pmfExp productLaw variance - threshold) := by
            rfl
    _ ≤ Real.exp (-((n : ℝ) * threshold) ^ 2 /
        (2 * ((n : ℝ) / ((n : ℝ) - 1)) *
          ((n : ℝ) * pmfExp productLaw variance))) := hsource
    _ = Real.exp (-((n : ℝ) - 1) * threshold ^ 2 /
        (2 * pmfExp productLaw variance)) := by
          congr 1
          field_simp [hcount_pos.ne', hden_pos.ne']
    _ = Real.exp (-((n : ℝ) - 1) * threshold ^ 2 /
        (2 * pmfExp (pmfProduct (Fin n) α law)
          (fun draw => finiteSampleUnbiasedVariance (statistic ∘ draw)))) := by
          rfl

/-- Maurer--Pontil's first standard-deviation confidence bound on a finite
iid `[0,1]` sample.  This is their Theorem 10, first display, written with a
positive logarithmic confidence parameter rather than `log (1 / δ)`.  It is
an exact consequence of the lower self-bounding tail after the source's
square-completion step. -/
theorem finiteSampleValueUnbiasedVariance_sqrtMean_upperTail
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}
    (law : PMF α) (statistic : α → ℝ) (hn : 2 ≤ n)
    (hunit : ∀ value, 0 ≤ statistic value ∧ statistic value ≤ 1)
    {logLevel : ℝ} (hlogLevel : 0 < logLevel) :
    pmfProb (pmfProduct (Fin n) α law)
        (fun sample =>
          Real.sqrt (pmfExp (pmfProduct (Fin n) α law)
              (fun draw => finiteSampleUnbiasedVariance (statistic ∘ draw))) >
            Real.sqrt (finiteSampleUnbiasedVariance (statistic ∘ sample)) +
              Real.sqrt (2 * logLevel / ((n : ℝ) - 1))) ≤
      Real.exp (-logLevel) := by
  let productLaw : PMF (Fin n → α) := pmfProduct (Fin n) α law
  let variance : (Fin n → α) → ℝ := fun sample =>
    finiteSampleUnbiasedVariance (statistic ∘ sample)
  let mean : ℝ := pmfExp productLaw variance
  let deviation : ℝ := Real.sqrt (logLevel / (2 * ((n : ℝ) - 1)))
  have hden_pos : 0 < (n : ℝ) - 1 := by
    have : (1 : ℝ) < n := by
      exact_mod_cast (show 1 < n from lt_of_lt_of_le (by omega) hn)
    linarith
  have hmean_nonneg : 0 ≤ mean := by
    exact pmfExp_nonneg_of_forall_nonneg productLaw variance
      (fun sample => finiteSampleUnbiasedVariance_nonneg (statistic ∘ sample) hn)
  have hdeviation_pos : 0 < deviation := by
    apply Real.sqrt_pos.2
    exact div_pos hlogLevel (mul_pos (by norm_num) hden_pos)
  have hgap : Real.sqrt (2 * logLevel / ((n : ℝ) - 1)) = 2 * deviation := by
    change Real.sqrt (2 * logLevel / ((n : ℝ) - 1)) =
      2 * Real.sqrt (logLevel / (2 * ((n : ℝ) - 1)))
    have hfactor : 2 * logLevel / ((n : ℝ) - 1) =
        4 * (logLevel / (2 * ((n : ℝ) - 1))) := by
      field_simp [hden_pos.ne']
      ring
    rw [hfactor, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  change pmfProb productLaw
      (fun sample => Real.sqrt mean > Real.sqrt (variance sample) +
        Real.sqrt (2 * logLevel / ((n : ℝ) - 1))) ≤ Real.exp (-logLevel)
  by_cases hmean_zero : mean = 0
  · have hzero : pmfProb productLaw
        (fun sample => Real.sqrt mean > Real.sqrt (variance sample) +
          Real.sqrt (2 * logLevel / ((n : ℝ) - 1))) = 0 := by
      apply pmfProb_eq_zero_of_no_mass productLaw
      intro sample hsample
      exfalso
      rw [hmean_zero] at hsample
      norm_num at hsample
      nlinarith [Real.sqrt_nonneg (variance sample),
        Real.sqrt_nonneg (2 * logLevel / ((n : ℝ) - 1))]
    rw [hzero]
    exact (Real.exp_pos _).le
  · have hmean_pos : 0 < mean := lt_of_le_of_ne hmean_nonneg (Ne.symm hmean_zero)
    have hthreshold : 0 < 2 * Real.sqrt mean * deviation := by positivity
    have htail := finiteSampleValueUnbiasedVariance_lowerTail
      law statistic hn hunit hthreshold
    change pmfProb productLaw
        (fun sample => variance sample < mean - 2 * Real.sqrt mean * deviation) ≤
      Real.exp (-((n : ℝ) - 1) * (2 * Real.sqrt mean * deviation) ^ 2 /
        (2 * mean)) at htail
    have hevent : ∀ sample,
        Real.sqrt mean > Real.sqrt (variance sample) +
          Real.sqrt (2 * logLevel / ((n : ℝ) - 1)) →
          variance sample < mean - 2 * Real.sqrt mean * deviation := by
      intro sample hsample
      rw [hgap] at hsample
      have hvariance_nonneg : 0 ≤ variance sample :=
        finiteSampleUnbiasedVariance_nonneg (statistic ∘ sample) hn
      have hsquare : (Real.sqrt (variance sample) + 2 * deviation) ^ 2 <
          (Real.sqrt mean) ^ 2 := by
        apply (sq_lt_sq₀ (by positivity) (Real.sqrt_nonneg _)).mpr
        exact hsample
      have hsquare_mean : (Real.sqrt mean) ^ 2 = mean :=
        Real.sq_sqrt hmean_nonneg
      have hsquare_variance : (Real.sqrt (variance sample)) ^ 2 = variance sample :=
        Real.sq_sqrt hvariance_nonneg
      have hroot_variance_nonneg : 0 ≤ Real.sqrt (variance sample) :=
        Real.sqrt_nonneg _
      have hroot_mean_nonneg : 0 ≤ Real.sqrt mean := Real.sqrt_nonneg _
      nlinarith
    calc
      pmfProb productLaw
          (fun sample => Real.sqrt mean > Real.sqrt (variance sample) +
            Real.sqrt (2 * logLevel / ((n : ℝ) - 1))) ≤
          pmfProb productLaw
            (fun sample => variance sample < mean - 2 * Real.sqrt mean * deviation) :=
        pmfProb_le_of_imp productLaw _ _ hevent
      _ ≤ Real.exp (-((n : ℝ) - 1) * (2 * Real.sqrt mean * deviation) ^ 2 /
          (2 * mean)) := htail
      _ = Real.exp (-logLevel) := by
        congr 1
        have hsquare_mean : (Real.sqrt mean) ^ 2 = mean :=
          Real.sq_sqrt hmean_nonneg
        have hsquare_deviation : deviation ^ 2 =
            logLevel / (2 * ((n : ℝ) - 1)) := by
          exact Real.sq_sqrt (le_of_lt (div_pos hlogLevel
            (mul_pos (by norm_num) hden_pos)))
        calc
          -((n : ℝ) - 1) * (2 * Real.sqrt mean * deviation) ^ 2 /
              (2 * mean) =
              -((n : ℝ) - 1) *
                (4 * (Real.sqrt mean) ^ 2 * deviation ^ 2) / (2 * mean) := by
                ring
          _ = -logLevel := by
            rw [hsquare_mean, hsquare_deviation]
            field_simp [hden_pos.ne', hmean_pos.ne']
            ring

/-- Maurer--Pontil's second standard-deviation confidence bound on a finite
iid `[0,1]` sample (Theorem 10, second display).  The upper variance tail
provides a slightly stronger intermediate variance threshold; the final
square-root relaxation is the one printed in the source. -/
theorem finiteSampleValueUnbiasedVariance_sqrtVariance_upperTail
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}
    (law : PMF α) (statistic : α → ℝ) (hn : 2 ≤ n)
    (hunit : ∀ value, 0 ≤ statistic value ∧ statistic value ≤ 1)
    {logLevel : ℝ} (hlogLevel : 0 < logLevel) :
    pmfProb (pmfProduct (Fin n) α law)
        (fun sample =>
          Real.sqrt (finiteSampleUnbiasedVariance (statistic ∘ sample)) >
            Real.sqrt (pmfExp (pmfProduct (Fin n) α law)
              (fun draw => finiteSampleUnbiasedVariance (statistic ∘ draw))) +
              Real.sqrt (2 * logLevel / ((n : ℝ) - 1))) ≤
      Real.exp (-logLevel) := by
  let productLaw : PMF (Fin n → α) := pmfProduct (Fin n) α law
  let variance : (Fin n → α) → ℝ := fun sample =>
    finiteSampleUnbiasedVariance (statistic ∘ sample)
  let mean : ℝ := pmfExp productLaw variance
  let deviation : ℝ := Real.sqrt (logLevel / (2 * ((n : ℝ) - 1)))
  let threshold : ℝ :=
    2 * Real.sqrt mean * deviation + 2 * deviation ^ 2
  have hden_pos : 0 < (n : ℝ) - 1 := by
    have : (1 : ℝ) < n := by
      exact_mod_cast (show 1 < n from lt_of_lt_of_le (by omega) hn)
    linarith
  have hmean_nonneg : 0 ≤ mean := by
    exact pmfExp_nonneg_of_forall_nonneg productLaw variance
      (fun sample => finiteSampleUnbiasedVariance_nonneg (statistic ∘ sample) hn)
  have hdeviation_pos : 0 < deviation := by
    apply Real.sqrt_pos.2
    exact div_pos hlogLevel (mul_pos (by norm_num) hden_pos)
  have hthreshold_pos : 0 < threshold := by
    dsimp [threshold]
    nlinarith [sq_pos_of_pos hdeviation_pos,
      mul_nonneg (Real.sqrt_nonneg mean) hdeviation_pos.le]
  have hgap : Real.sqrt (2 * logLevel / ((n : ℝ) - 1)) = 2 * deviation := by
    change Real.sqrt (2 * logLevel / ((n : ℝ) - 1)) =
      2 * Real.sqrt (logLevel / (2 * ((n : ℝ) - 1)))
    have hfactor : 2 * logLevel / ((n : ℝ) - 1) =
        4 * (logLevel / (2 * ((n : ℝ) - 1))) := by
      field_simp [hden_pos.ne']
      ring
    rw [hfactor, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  change pmfProb productLaw
      (fun sample => Real.sqrt (variance sample) > Real.sqrt mean +
        Real.sqrt (2 * logLevel / ((n : ℝ) - 1))) ≤ Real.exp (-logLevel)
  have htail := finiteSampleValueUnbiasedVariance_upperTail
    law statistic hn hunit hthreshold_pos
  change pmfProb productLaw
      (fun sample => mean + threshold < variance sample) ≤
    Real.exp (-((n : ℝ) - 1) * threshold ^ 2 / (2 * mean + threshold)) at htail
  have hevent : ∀ sample,
      Real.sqrt (variance sample) > Real.sqrt mean +
        Real.sqrt (2 * logLevel / ((n : ℝ) - 1)) →
        mean + threshold < variance sample := by
    intro sample hsample
    rw [hgap] at hsample
    have hvariance_nonneg : 0 ≤ variance sample :=
      finiteSampleUnbiasedVariance_nonneg (statistic ∘ sample) hn
    have hsquare : (Real.sqrt mean + 2 * deviation) ^ 2 <
        (Real.sqrt (variance sample)) ^ 2 := by
      apply (sq_lt_sq₀ (by positivity) (Real.sqrt_nonneg _)).mpr
      exact hsample
    have hsquare_mean : (Real.sqrt mean) ^ 2 = mean :=
      Real.sq_sqrt hmean_nonneg
    have hsquare_variance : (Real.sqrt (variance sample)) ^ 2 = variance sample :=
      Real.sq_sqrt hvariance_nonneg
    dsimp [threshold]
    nlinarith [Real.sqrt_nonneg mean, hdeviation_pos.le]
  have hden_tail_pos : 0 < 2 * mean + threshold := by positivity
  have hratio : logLevel ≤
      ((n : ℝ) - 1) * threshold ^ 2 / (2 * mean + threshold) := by
    apply (le_div_iff₀ hden_tail_pos).2
    have hsquare_mean : (Real.sqrt mean) ^ 2 = mean :=
      Real.sq_sqrt hmean_nonneg
    have hsquare_deviation : deviation ^ 2 =
        logLevel / (2 * ((n : ℝ) - 1)) := by
      exact Real.sq_sqrt (le_of_lt (div_pos hlogLevel
        (mul_pos (by norm_num) hden_pos)))
    have hlogLevel : logLevel = 2 * ((n : ℝ) - 1) * deviation ^ 2 := by
      rw [hsquare_deviation]
      field_simp [hden_pos.ne']
    have hidentity :
        ((n : ℝ) - 1) * threshold ^ 2 -
            logLevel * (2 * mean + threshold) =
          4 * ((n : ℝ) - 1) * Real.sqrt mean * deviation ^ 3 := by
      have htwo_mean : 2 * mean = 2 * (Real.sqrt mean) ^ 2 := by
        rw [hsquare_mean]
      rw [hlogLevel, htwo_mean]
      dsimp [threshold]
      ring
    rw [← sub_nonneg]
    rw [hidentity]
    positivity
  calc
    pmfProb productLaw
        (fun sample => Real.sqrt (variance sample) > Real.sqrt mean +
          Real.sqrt (2 * logLevel / ((n : ℝ) - 1))) ≤
        pmfProb productLaw (fun sample => mean + threshold < variance sample) :=
      pmfProb_le_of_imp productLaw _ _ hevent
    _ ≤ Real.exp (-((n : ℝ) - 1) * threshold ^ 2 / (2 * mean + threshold)) := htail
    _ ≤ Real.exp (-logLevel) := by
      apply Real.exp_le_exp.mpr
      rw [show -((n : ℝ) - 1) * threshold ^ 2 / (2 * mean + threshold) =
          -(((n : ℝ) - 1) * threshold ^ 2 / (2 * mean + threshold)) by ring]
      exact neg_le_neg hratio

/-- The source's square-root arithmetic: a population-variance Bennett
radius is bounded by the observable unbiased-variance radius on the first
Theorem-10 standard-deviation event. -/
private theorem finiteSampleMean_populationRadius_le_empiricalRadius
    {n : ℕ} {populationVariance empiricalVariance logLevel : ℝ}
    (hn : 2 ≤ n) (hlogLevel : 0 < logLevel)
    (hpopulationVariance : 0 ≤ populationVariance)
    (hempiricalVariance : 0 ≤ empiricalVariance)
    (hstd : Real.sqrt populationVariance ≤
      Real.sqrt empiricalVariance +
        Real.sqrt (2 * logLevel / ((n : ℝ) - 1))) :
    (Real.sqrt (2 * (n : ℝ) * populationVariance * logLevel) +
      logLevel / 3) / (n : ℝ) ≤
      Real.sqrt (2 * empiricalVariance * logLevel / (n : ℝ)) +
        7 * logLevel / (3 * ((n : ℝ) - 1)) := by
  let count : ℝ := n
  let denominator : ℝ := count - 1
  let scale : ℝ := Real.sqrt (2 * count * logLevel)
  let populationRoot : ℝ := Real.sqrt populationVariance
  let empiricalRoot : ℝ := Real.sqrt empiricalVariance
  let deviation : ℝ := Real.sqrt (2 * logLevel / denominator)
  have hcount_pos : 0 < count := by
    dsimp [count]
    exact_mod_cast (lt_of_lt_of_le (by omega) hn)
  have hdenominator_pos : 0 < denominator := by
    dsimp [denominator]
    have hcount_gt_one : (1 : ℝ) < count := by
      dsimp [count]
      exact_mod_cast (lt_of_lt_of_le (by omega) hn)
    linarith
  have hscale_sq : scale ^ 2 = 2 * count * logLevel := by
    dsimp [scale]
    exact Real.sq_sqrt (by positivity)
  have hpopulationRoot_sq : populationRoot ^ 2 = populationVariance := by
    dsimp [populationRoot]
    exact Real.sq_sqrt hpopulationVariance
  have hempiricalRoot_sq : empiricalRoot ^ 2 = empiricalVariance := by
    dsimp [empiricalRoot]
    exact Real.sq_sqrt hempiricalVariance
  have hdeviation_sq : deviation ^ 2 = 2 * logLevel / denominator := by
    dsimp [deviation]
    exact Real.sq_sqrt (by positivity)
  have hpopulation_product :
      Real.sqrt (2 * count * populationVariance * logLevel) =
        scale * populationRoot := by
    change Real.sqrt (2 * count * populationVariance * logLevel) =
      Real.sqrt (2 * count * logLevel) * Real.sqrt populationVariance
    rw [show 2 * count * populationVariance * logLevel =
        (2 * count * logLevel) * populationVariance by ring]
    exact Real.sqrt_mul (by positivity) populationVariance
  have hempirical_product : scale * empiricalRoot / count =
      Real.sqrt (2 * empiricalVariance * logLevel / count) := by
    have hleft_nonneg : 0 ≤ scale * empiricalRoot / count := by positivity
    have hright_nonneg : 0 ≤ Real.sqrt (2 * empiricalVariance * logLevel / count) :=
      Real.sqrt_nonneg _
    have hleft_sq : (scale * empiricalRoot / count) ^ 2 =
        2 * empiricalVariance * logLevel / count := by
      rw [div_pow, mul_pow, hscale_sq, hempiricalRoot_sq]
      field_simp [hcount_pos.ne']
    have hright_sq : (Real.sqrt (2 * empiricalVariance * logLevel / count)) ^ 2 =
        2 * empiricalVariance * logLevel / count := by
      exact Real.sq_sqrt (by positivity)
    nlinarith
  have hdeviation_term : scale * deviation / count ≤
      2 * logLevel / denominator := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    rw [div_pow, mul_pow, hscale_sq, hdeviation_sq]
    field_simp [hcount_pos.ne', hdenominator_pos.ne']
    dsimp [denominator] at *
    nlinarith [sq_nonneg logLevel]
  have hscaled : scale / count * populationRoot ≤
      scale / count * (empiricalRoot + deviation) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    simpa [populationRoot, empiricalRoot, deviation, denominator] using hstd
  have hscaled' : scale * populationRoot / count ≤
      scale * empiricalRoot / count + scale * deviation / count := by
    convert hscaled using 1 <;> ring
  have hlinear : 2 * logLevel / denominator + logLevel / (3 * count) ≤
      7 * logLevel / (3 * denominator) := by
    field_simp [hcount_pos.ne', hdenominator_pos.ne']
    dsimp [denominator] at *
    nlinarith
  change (Real.sqrt (2 * count * populationVariance * logLevel) +
      logLevel / 3) / count ≤
      Real.sqrt (2 * empiricalVariance * logLevel / count) +
        7 * logLevel / (3 * denominator)
  rw [hpopulation_product]
  calc
    (scale * populationRoot + logLevel / 3) / count =
        scale * populationRoot / count + logLevel / (3 * count) := by
          field_simp [hcount_pos.ne']
    _ ≤ scale * empiricalRoot / count + scale * deviation / count +
          logLevel / (3 * count) := by linarith
    _ ≤ Real.sqrt (2 * empiricalVariance * logLevel / count) +
          2 * logLevel / denominator + logLevel / (3 * count) := by
          rw [hempirical_product]
          linarith
    _ ≤ Real.sqrt (2 * empiricalVariance * logLevel / count) +
          7 * logLevel / (3 * denominator) := by linarith

/-- Maurer--Pontil's finite iid empirical-Bernstein lower confidence bound
(Theorem 4), for the literal unbiased pairwise sample variance.  The proof
combines the finite Bennett mean tail with the first Theorem-10
standard-deviation event by a two-event union bound. -/
theorem pmfProb_finiteSampleMean_lowerTail_empiricalBernstein
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}
    (law : PMF α) (statistic : α → ℝ) (hn : 2 ≤ n)
    (hunit : ∀ outcome, 0 ≤ statistic outcome ∧ statistic outcome ≤ 1)
    {logLevel : ℝ} (hlogLevel : 0 < logLevel) :
    pmfProb (pmfProduct (Fin n) α law)
        (fun sample =>
          finiteRealSampleMean (statistic ∘ sample) <
            pmfExp law statistic -
              (Real.sqrt (2 * finiteSampleUnbiasedVariance
                  (statistic ∘ sample) * logLevel / (n : ℝ)) +
                7 * logLevel / (3 * ((n : ℝ) - 1)))) ≤
      2 * Real.exp (-logLevel) := by
  let productLaw : PMF (Fin n → α) := pmfProduct (Fin n) α law
  let sampleVariance : (Fin n → α) → ℝ := fun sample =>
    finiteSampleUnbiasedVariance (statistic ∘ sample)
  let populationVariance : ℝ := pmfVariance law statistic
  let meanFailure : (Fin n → α) → Prop := fun sample =>
    finiteRealSampleMean (statistic ∘ sample) <
      pmfExp law statistic -
        (Real.sqrt (2 * (n : ℝ) * populationVariance * logLevel) +
          logLevel / 3) / (n : ℝ)
  let stdFailure : (Fin n → α) → Prop := fun sample =>
    Real.sqrt populationVariance > Real.sqrt (sampleVariance sample) +
      Real.sqrt (2 * logLevel / ((n : ℝ) - 1))
  let empiricalFailure : (Fin n → α) → Prop := fun sample =>
    finiteRealSampleMean (statistic ∘ sample) <
      pmfExp law statistic -
        (Real.sqrt (2 * sampleVariance sample * logLevel / (n : ℝ)) +
          7 * logLevel / (3 * ((n : ℝ) - 1)))
  have hpopulationVariance_nonneg : 0 ≤ populationVariance := by
    dsimp [populationVariance]
    exact pmfVariance_nonneg law statistic
  have hsampleVariance_nonneg (sample : Fin n → α) :
      0 ≤ sampleVariance sample := by
    dsimp [sampleVariance]
    exact finiteSampleUnbiasedVariance_nonneg (statistic ∘ sample) hn
  have hmeanTail : pmfProb productLaw meanFailure ≤ Real.exp (-logLevel) := by
    dsimp [productLaw, meanFailure, populationVariance]
    exact pmfProb_finiteSampleMean_lowerTail_le_exp_neg_of_unit
      law statistic (lt_of_lt_of_le (by omega) hn) hlogLevel hunit
  have hstdTail : pmfProb productLaw stdFailure ≤ Real.exp (-logLevel) := by
    have hsource := finiteSampleValueUnbiasedVariance_sqrtMean_upperTail
      law statistic hn hunit hlogLevel
    rw [pmfExp_finiteSampleUnbiasedVariance_eq_pmfVariance law statistic hn] at hsource
    simpa [productLaw, sampleVariance, populationVariance, stdFailure] using hsource
  have himp : ∀ sample, empiricalFailure sample →
      meanFailure sample ∨ stdFailure sample := by
    intro sample hfailure
    by_cases hstd : stdFailure sample
    · exact Or.inr hstd
    · left
      have hstdGood : Real.sqrt populationVariance ≤
          Real.sqrt (sampleVariance sample) +
            Real.sqrt (2 * logLevel / ((n : ℝ) - 1)) := le_of_not_gt hstd
      have hradius := finiteSampleMean_populationRadius_le_empiricalRadius
        hn hlogLevel hpopulationVariance_nonneg (hsampleVariance_nonneg sample) hstdGood
      dsimp [empiricalFailure, meanFailure] at hfailure ⊢
      dsimp [populationVariance] at hradius
      linarith
  calc
    pmfProb (pmfProduct (Fin n) α law) empiricalFailure ≤
        pmfProb productLaw (fun sample => meanFailure sample ∨ stdFailure sample) := by
          change pmfProb productLaw empiricalFailure ≤ _
          exact pmfProb_le_of_imp productLaw _ _ himp
    _ ≤ pmfProb productLaw meanFailure + pmfProb productLaw stdFailure :=
      pmfProb_or_le productLaw meanFailure stdFailure
    _ ≤ 2 * Real.exp (-logLevel) := by linarith

/-- The upper companion of Maurer--Pontil's finite iid empirical-Bernstein
bound.  It is obtained by applying the checked lower-tail theorem to the
complemented unit-interval statistic; complementation preserves the literal
unbiased sample variance. -/
theorem pmfProb_finiteSampleMean_upperTail_empiricalBernstein
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}
    (law : PMF α) (statistic : α → ℝ) (hn : 2 ≤ n)
    (hunit : ∀ outcome, 0 ≤ statistic outcome ∧ statistic outcome ≤ 1)
    {logLevel : ℝ} (hlogLevel : 0 < logLevel) :
    pmfProb (pmfProduct (Fin n) α law)
        (fun sample =>
          pmfExp law statistic +
              (Real.sqrt (2 * finiteSampleUnbiasedVariance
                  (statistic ∘ sample) * logLevel / (n : ℝ)) +
                7 * logLevel / (3 * ((n : ℝ) - 1))) <
            finiteRealSampleMean (statistic ∘ sample)) ≤
      2 * Real.exp (-logLevel) := by
  let complement : α → ℝ := fun outcome => 1 - statistic outcome
  have hn_pos : 0 < n := lt_of_lt_of_le (by omega) hn
  have hcomplement_unit : ∀ outcome, 0 ≤ complement outcome ∧ complement outcome ≤ 1 := by
    intro outcome
    dsimp [complement]
    obtain ⟨hlower, hupper⟩ := hunit outcome
    constructor <;> linarith
  let lowerFailure : (Fin n → α) → Prop := fun sample =>
    finiteRealSampleMean (complement ∘ sample) <
      pmfExp law complement -
        (Real.sqrt (2 * finiteSampleUnbiasedVariance
            (complement ∘ sample) * logLevel / (n : ℝ)) +
          7 * logLevel / (3 * ((n : ℝ) - 1)))
  have hsource :
      pmfProb (pmfProduct (Fin n) α law) lowerFailure ≤ 2 * Real.exp (-logLevel) := by
    simpa [lowerFailure] using
      (pmfProb_finiteSampleMean_lowerTail_empiricalBernstein
        law complement hn hcomplement_unit hlogLevel)
  let upperFailure : (Fin n → α) → Prop := fun sample =>
    pmfExp law statistic +
        (Real.sqrt (2 * finiteSampleUnbiasedVariance
            (statistic ∘ sample) * logLevel / (n : ℝ)) +
          7 * logLevel / (3 * ((n : ℝ) - 1))) <
      finiteRealSampleMean (statistic ∘ sample)
  have hfailure_iff (sample : Fin n → α) : upperFailure sample ↔ lowerFailure sample := by
    have hmean : finiteRealSampleMean (complement ∘ sample) =
        1 - finiteRealSampleMean (statistic ∘ sample) := by
      simpa [complement, Function.comp_def] using
        (finiteSampleMean_one_sub (statistic ∘ sample) hn_pos)
    have hvariance : finiteSampleUnbiasedVariance (complement ∘ sample) =
        finiteSampleUnbiasedVariance (statistic ∘ sample) := by
      simpa [complement, Function.comp_def] using
        (finiteSampleUnbiasedVariance_one_sub (statistic ∘ sample) hn_pos)
    have hpopulation : pmfExp law complement = 1 - pmfExp law statistic := by
      simpa [complement] using pmfExp_one_sub law statistic
    dsimp [upperFailure, lowerFailure]
    rw [hmean, hvariance, hpopulation]
    constructor <;> intro hfailure <;> linarith
  calc
    pmfProb (pmfProduct (Fin n) α law) upperFailure =
        pmfProb (pmfProduct (Fin n) α law) lowerFailure :=
      by
        apply pmfProb_congr
        exact hfailure_iff
    _ ≤ 2 * Real.exp (-logLevel) := hsource

end AppliedModelingLib
