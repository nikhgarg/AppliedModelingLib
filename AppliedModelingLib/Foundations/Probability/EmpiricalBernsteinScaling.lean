import AppliedModelingLib.Foundations.Probability.EmpiricalBernstein
import Mathlib.Tactic

/-!
# Range scaling for finite empirical-Bernstein confidence bounds

Maurer--Pontil's theorem is stated for observations in `[0, 1]`.  This module
transports its literal finite-sample bound to observations in `[0, B]`,
preserving both the linear and the empirical-variance terms.
-/

namespace AppliedModelingLib

/-- The finite iid lower empirical-Bernstein tail scales from `[0,1]` to a
positive range `[0,B]`. -/
theorem pmfProb_finiteSampleMean_lowerTail_empiricalBernstein_of_nonneg_le_scale
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}
    (law : PMF α) (statistic : α → ℝ) (hn : 2 ≤ n)
    {scale : ℝ} (hscale : 0 < scale)
    (hbounded : ∀ outcome, 0 ≤ statistic outcome ∧ statistic outcome ≤ scale)
    {logLevel : ℝ} (hlogLevel : 0 < logLevel) :
    pmfProb (pmfProduct (Fin n) α law)
        (fun sample =>
          finiteRealSampleMean (statistic ∘ sample) <
            pmfExp law statistic -
              (Real.sqrt (2 * finiteSampleUnbiasedVariance
                  (statistic ∘ sample) * logLevel / (n : ℝ)) +
                7 * scale * logLevel / (3 * ((n : ℝ) - 1)))) ≤
      2 * Real.exp (-logLevel) := by
  let normalized : α → ℝ := fun outcome => statistic outcome / scale
  have hunit : ∀ outcome, 0 ≤ normalized outcome ∧ normalized outcome ≤ 1 := by
    intro outcome
    obtain ⟨hlower, hupper⟩ := hbounded outcome
    constructor
    · exact div_nonneg hlower hscale.le
    · exact (div_le_iff₀ hscale).2 (by simpa using hupper)
  have hsource := pmfProb_finiteSampleMean_lowerTail_empiricalBernstein
    law normalized hn hunit hlogLevel
  have hmeanSample (sample : Fin n → α) :
      finiteRealSampleMean (statistic ∘ sample) =
        scale * finiteRealSampleMean (normalized ∘ sample) := by
    calc
      finiteRealSampleMean (statistic ∘ sample) =
          finiteRealSampleMean (fun index => scale * (normalized ∘ sample) index) := by
        congr 1
        funext index
        dsimp [normalized]
        field_simp [hscale.ne']
      _ = scale * finiteRealSampleMean (normalized ∘ sample) :=
        finiteSampleMean_mul_left scale (normalized ∘ sample)
  have hvarianceSample (sample : Fin n → α) :
      finiteSampleUnbiasedVariance (statistic ∘ sample) =
        scale ^ 2 * finiteSampleUnbiasedVariance (normalized ∘ sample) := by
    calc
      finiteSampleUnbiasedVariance (statistic ∘ sample) =
          finiteSampleUnbiasedVariance (fun index => scale * (normalized ∘ sample) index) := by
        congr 1
        funext index
        dsimp [normalized]
        field_simp [hscale.ne']
      _ = scale ^ 2 * finiteSampleUnbiasedVariance (normalized ∘ sample) :=
        finiteSampleUnbiasedVariance_mul_left scale (normalized ∘ sample)
  have hpopulation : pmfExp law statistic = scale * pmfExp law normalized := by
    calc
      pmfExp law statistic = pmfExp law (fun outcome => scale * normalized outcome) := by
        apply pmfExp_congr
        intro outcome
        dsimp [normalized]
        field_simp [hscale.ne']
      _ = scale * pmfExp law normalized := pmfExp_const_mul law scale normalized
  have hsqrt (variance : ℝ) :
      Real.sqrt (2 * (scale ^ 2 * variance) * logLevel / (n : ℝ)) =
        scale * Real.sqrt (2 * variance * logLevel / (n : ℝ)) := by
    have hfactor :
        2 * (scale ^ 2 * variance) * logLevel / (n : ℝ) =
          scale ^ 2 * (2 * variance * logLevel / (n : ℝ)) := by ring
    rw [hfactor, Real.sqrt_mul (sq_nonneg scale), Real.sqrt_sq_eq_abs,
      abs_of_pos hscale]
  have hlinear (x : ℝ) :
      scale * x + 7 * scale * logLevel / (3 * ((n : ℝ) - 1)) =
        scale * (x + 7 * logLevel / (3 * ((n : ℝ) - 1))) := by
    ring
  have hevent (sample : Fin n → α) :
      (finiteRealSampleMean (statistic ∘ sample) <
          pmfExp law statistic -
            (Real.sqrt (2 * finiteSampleUnbiasedVariance
                (statistic ∘ sample) * logLevel / (n : ℝ)) +
              7 * scale * logLevel / (3 * ((n : ℝ) - 1)))) ↔
        finiteRealSampleMean (normalized ∘ sample) <
          pmfExp law normalized -
            (Real.sqrt (2 * finiteSampleUnbiasedVariance
                (normalized ∘ sample) * logLevel / (n : ℝ)) +
              7 * logLevel / (3 * ((n : ℝ) - 1))) := by
    rw [hmeanSample, hpopulation, hvarianceSample, hsqrt, hlinear]
    constructor <;> intro h <;> nlinarith
  rw [pmfProb_congr (pmfProduct (Fin n) α law) hevent]
  exact hsource

/-- The finite iid upper empirical-Bernstein tail scales from `[0,1]` to a
positive range `[0,B]`. -/
theorem pmfProb_finiteSampleMean_upperTail_empiricalBernstein_of_nonneg_le_scale
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}
    (law : PMF α) (statistic : α → ℝ) (hn : 2 ≤ n)
    {scale : ℝ} (hscale : 0 < scale)
    (hbounded : ∀ outcome, 0 ≤ statistic outcome ∧ statistic outcome ≤ scale)
    {logLevel : ℝ} (hlogLevel : 0 < logLevel) :
    pmfProb (pmfProduct (Fin n) α law)
        (fun sample =>
          pmfExp law statistic +
              (Real.sqrt (2 * finiteSampleUnbiasedVariance
                  (statistic ∘ sample) * logLevel / (n : ℝ)) +
                7 * scale * logLevel / (3 * ((n : ℝ) - 1))) <
            finiteRealSampleMean (statistic ∘ sample)) ≤
      2 * Real.exp (-logLevel) := by
  let normalized : α → ℝ := fun outcome => statistic outcome / scale
  have hunit : ∀ outcome, 0 ≤ normalized outcome ∧ normalized outcome ≤ 1 := by
    intro outcome
    obtain ⟨hlower, hupper⟩ := hbounded outcome
    constructor
    · exact div_nonneg hlower hscale.le
    · exact (div_le_iff₀ hscale).2 (by simpa using hupper)
  have hsource := pmfProb_finiteSampleMean_upperTail_empiricalBernstein
    law normalized hn hunit hlogLevel
  have hmeanSample (sample : Fin n → α) :
      finiteRealSampleMean (statistic ∘ sample) =
        scale * finiteRealSampleMean (normalized ∘ sample) := by
    calc
      finiteRealSampleMean (statistic ∘ sample) =
          finiteRealSampleMean (fun index => scale * (normalized ∘ sample) index) := by
        congr 1
        funext index
        dsimp [normalized]
        field_simp [hscale.ne']
      _ = scale * finiteRealSampleMean (normalized ∘ sample) :=
        finiteSampleMean_mul_left scale (normalized ∘ sample)
  have hvarianceSample (sample : Fin n → α) :
      finiteSampleUnbiasedVariance (statistic ∘ sample) =
        scale ^ 2 * finiteSampleUnbiasedVariance (normalized ∘ sample) := by
    calc
      finiteSampleUnbiasedVariance (statistic ∘ sample) =
          finiteSampleUnbiasedVariance (fun index => scale * (normalized ∘ sample) index) := by
        congr 1
        funext index
        dsimp [normalized]
        field_simp [hscale.ne']
      _ = scale ^ 2 * finiteSampleUnbiasedVariance (normalized ∘ sample) :=
        finiteSampleUnbiasedVariance_mul_left scale (normalized ∘ sample)
  have hpopulation : pmfExp law statistic = scale * pmfExp law normalized := by
    calc
      pmfExp law statistic = pmfExp law (fun outcome => scale * normalized outcome) := by
        apply pmfExp_congr
        intro outcome
        dsimp [normalized]
        field_simp [hscale.ne']
      _ = scale * pmfExp law normalized := pmfExp_const_mul law scale normalized
  have hsqrt (variance : ℝ) :
      Real.sqrt (2 * (scale ^ 2 * variance) * logLevel / (n : ℝ)) =
        scale * Real.sqrt (2 * variance * logLevel / (n : ℝ)) := by
    have hfactor :
        2 * (scale ^ 2 * variance) * logLevel / (n : ℝ) =
          scale ^ 2 * (2 * variance * logLevel / (n : ℝ)) := by ring
    rw [hfactor, Real.sqrt_mul (sq_nonneg scale), Real.sqrt_sq_eq_abs,
      abs_of_pos hscale]
  have hlinear (x : ℝ) :
      scale * x + 7 * scale * logLevel / (3 * ((n : ℝ) - 1)) =
        scale * (x + 7 * logLevel / (3 * ((n : ℝ) - 1))) := by
    ring
  have hevent (sample : Fin n → α) :
      (pmfExp law statistic +
          (Real.sqrt (2 * finiteSampleUnbiasedVariance
              (statistic ∘ sample) * logLevel / (n : ℝ)) +
            7 * scale * logLevel / (3 * ((n : ℝ) - 1))) <
          finiteRealSampleMean (statistic ∘ sample) ↔
        pmfExp law normalized +
          (Real.sqrt (2 * finiteSampleUnbiasedVariance
              (normalized ∘ sample) * logLevel / (n : ℝ)) +
            7 * logLevel / (3 * ((n : ℝ) - 1))) <
          finiteRealSampleMean (normalized ∘ sample)) := by
    rw [hmeanSample, hpopulation, hvarianceSample, hsqrt, hlinear]
    constructor <;> intro h <;> nlinarith
  rw [pmfProb_congr (pmfProduct (Fin n) α law) hevent]
  exact hsource

/-- Maurer--Pontil's first standard-deviation confidence bound scales from
`[0,1]` to a positive range `[0,B]`.  Both the population expectation of the
unbiased variance and each realized unbiased variance acquire the same
`B²` factor, so their square roots and the deviation term acquire `B`. -/
theorem pmfProb_finiteSampleUnbiasedVariance_sqrtMean_upperTail_of_nonneg_le_scale
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}
    (law : PMF α) (statistic : α → ℝ) (hn : 2 ≤ n)
    {scale : ℝ} (hscale : 0 < scale)
    (hbounded : ∀ outcome, 0 ≤ statistic outcome ∧ statistic outcome ≤ scale)
    {logLevel : ℝ} (hlogLevel : 0 < logLevel) :
    pmfProb (pmfProduct (Fin n) α law)
        (fun sample =>
          Real.sqrt (pmfExp (pmfProduct (Fin n) α law)
              (fun draw => finiteSampleUnbiasedVariance (statistic ∘ draw))) >
            Real.sqrt (finiteSampleUnbiasedVariance (statistic ∘ sample)) +
              scale * Real.sqrt (2 * logLevel / ((n : ℝ) - 1))) ≤
      Real.exp (-logLevel) := by
  let normalized : α → ℝ := fun outcome => statistic outcome / scale
  have hunit : ∀ outcome, 0 ≤ normalized outcome ∧ normalized outcome ≤ 1 := by
    intro outcome
    obtain ⟨hlower, hupper⟩ := hbounded outcome
    constructor
    · exact div_nonneg hlower hscale.le
    · exact (div_le_iff₀ hscale).2 (by simpa using hupper)
  have hsource := finiteSampleValueUnbiasedVariance_sqrtMean_upperTail
    law normalized hn hunit hlogLevel
  have hvarianceSample (sample : Fin n → α) :
      finiteSampleUnbiasedVariance (statistic ∘ sample) =
        scale ^ 2 * finiteSampleUnbiasedVariance (normalized ∘ sample) := by
    calc
      finiteSampleUnbiasedVariance (statistic ∘ sample) =
          finiteSampleUnbiasedVariance (fun index => scale * (normalized ∘ sample) index) := by
        congr 1
        funext index
        dsimp [normalized]
        field_simp [hscale.ne']
      _ = scale ^ 2 * finiteSampleUnbiasedVariance (normalized ∘ sample) :=
        finiteSampleUnbiasedVariance_mul_left scale (normalized ∘ sample)
  have hvarianceMean :
      pmfExp (pmfProduct (Fin n) α law)
          (fun draw => finiteSampleUnbiasedVariance (statistic ∘ draw)) =
        scale ^ 2 * pmfExp (pmfProduct (Fin n) α law)
          (fun draw => finiteSampleUnbiasedVariance (normalized ∘ draw)) := by
    calc
      pmfExp (pmfProduct (Fin n) α law)
          (fun draw => finiteSampleUnbiasedVariance (statistic ∘ draw)) =
          pmfExp (pmfProduct (Fin n) α law)
            (fun draw => scale ^ 2 * finiteSampleUnbiasedVariance (normalized ∘ draw)) := by
        apply pmfExp_congr
        intro draw
        exact hvarianceSample draw
      _ = scale ^ 2 * pmfExp (pmfProduct (Fin n) α law)
          (fun draw => finiteSampleUnbiasedVariance (normalized ∘ draw)) :=
        pmfExp_const_mul _ _ _
  have hsqrt (variance : ℝ) :
      Real.sqrt (scale ^ 2 * variance) = scale * Real.sqrt variance := by
    rw [Real.sqrt_mul (sq_nonneg scale), Real.sqrt_sq_eq_abs, abs_of_pos hscale]
  have hevent (sample : Fin n → α) :
      (Real.sqrt (pmfExp (pmfProduct (Fin n) α law)
          (fun draw => finiteSampleUnbiasedVariance (statistic ∘ draw))) >
          Real.sqrt (finiteSampleUnbiasedVariance (statistic ∘ sample)) +
            scale * Real.sqrt (2 * logLevel / ((n : ℝ) - 1))) ↔
        Real.sqrt (pmfExp (pmfProduct (Fin n) α law)
          (fun draw => finiteSampleUnbiasedVariance (normalized ∘ draw))) >
          Real.sqrt (finiteSampleUnbiasedVariance (normalized ∘ sample)) +
            Real.sqrt (2 * logLevel / ((n : ℝ) - 1)) := by
    rw [hvarianceMean, hvarianceSample, hsqrt, hsqrt]
    constructor <;> intro hfailure <;> nlinarith
  rw [pmfProb_congr (pmfProduct (Fin n) α law) hevent]
  exact hsource

/-- The reciprocal Maurer--Pontil standard-deviation confidence bound also
scales exactly from `[0,1]` to a positive range `[0,B]`. -/
theorem pmfProb_finiteSampleUnbiasedVariance_sqrtVariance_upperTail_of_nonneg_le_scale
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}
    (law : PMF α) (statistic : α → ℝ) (hn : 2 ≤ n)
    {scale : ℝ} (hscale : 0 < scale)
    (hbounded : ∀ outcome, 0 ≤ statistic outcome ∧ statistic outcome ≤ scale)
    {logLevel : ℝ} (hlogLevel : 0 < logLevel) :
    pmfProb (pmfProduct (Fin n) α law)
        (fun sample =>
          Real.sqrt (finiteSampleUnbiasedVariance (statistic ∘ sample)) >
            Real.sqrt (pmfExp (pmfProduct (Fin n) α law)
              (fun draw => finiteSampleUnbiasedVariance (statistic ∘ draw))) +
              scale * Real.sqrt (2 * logLevel / ((n : ℝ) - 1))) ≤
      Real.exp (-logLevel) := by
  let normalized : α → ℝ := fun outcome => statistic outcome / scale
  have hunit : ∀ outcome, 0 ≤ normalized outcome ∧ normalized outcome ≤ 1 := by
    intro outcome
    obtain ⟨hlower, hupper⟩ := hbounded outcome
    constructor
    · exact div_nonneg hlower hscale.le
    · exact (div_le_iff₀ hscale).2 (by simpa using hupper)
  have hsource := finiteSampleValueUnbiasedVariance_sqrtVariance_upperTail
    law normalized hn hunit hlogLevel
  have hvarianceSample (sample : Fin n → α) :
      finiteSampleUnbiasedVariance (statistic ∘ sample) =
        scale ^ 2 * finiteSampleUnbiasedVariance (normalized ∘ sample) := by
    calc
      finiteSampleUnbiasedVariance (statistic ∘ sample) =
          finiteSampleUnbiasedVariance (fun index => scale * (normalized ∘ sample) index) := by
        congr 1
        funext index
        dsimp [normalized]
        field_simp [hscale.ne']
      _ = scale ^ 2 * finiteSampleUnbiasedVariance (normalized ∘ sample) :=
        finiteSampleUnbiasedVariance_mul_left scale (normalized ∘ sample)
  have hvarianceMean :
      pmfExp (pmfProduct (Fin n) α law)
          (fun draw => finiteSampleUnbiasedVariance (statistic ∘ draw)) =
        scale ^ 2 * pmfExp (pmfProduct (Fin n) α law)
          (fun draw => finiteSampleUnbiasedVariance (normalized ∘ draw)) := by
    calc
      pmfExp (pmfProduct (Fin n) α law)
          (fun draw => finiteSampleUnbiasedVariance (statistic ∘ draw)) =
          pmfExp (pmfProduct (Fin n) α law)
            (fun draw => scale ^ 2 * finiteSampleUnbiasedVariance (normalized ∘ draw)) := by
        apply pmfExp_congr
        intro draw
        exact hvarianceSample draw
      _ = scale ^ 2 * pmfExp (pmfProduct (Fin n) α law)
          (fun draw => finiteSampleUnbiasedVariance (normalized ∘ draw)) :=
        pmfExp_const_mul _ _ _
  have hsqrt (variance : ℝ) :
      Real.sqrt (scale ^ 2 * variance) = scale * Real.sqrt variance := by
    rw [Real.sqrt_mul (sq_nonneg scale), Real.sqrt_sq_eq_abs, abs_of_pos hscale]
  have hevent (sample : Fin n → α) :
      (Real.sqrt (finiteSampleUnbiasedVariance (statistic ∘ sample)) >
          Real.sqrt (pmfExp (pmfProduct (Fin n) α law)
            (fun draw => finiteSampleUnbiasedVariance (statistic ∘ draw))) +
            scale * Real.sqrt (2 * logLevel / ((n : ℝ) - 1))) ↔
        Real.sqrt (finiteSampleUnbiasedVariance (normalized ∘ sample)) >
          Real.sqrt (pmfExp (pmfProduct (Fin n) α law)
            (fun draw => finiteSampleUnbiasedVariance (normalized ∘ draw))) +
            Real.sqrt (2 * logLevel / ((n : ℝ) - 1)) := by
    rw [hvarianceSample, hvarianceMean, hsqrt, hsqrt]
    constructor <;> intro hfailure <;> nlinarith
  rw [pmfProb_congr (pmfProduct (Fin n) α law) hevent]
  exact hsource

end AppliedModelingLib
