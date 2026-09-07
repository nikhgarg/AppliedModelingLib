import AppliedModelingLib.Foundations.Probability.ExponentialTilt
import Mathlib.Probability.Moments.SubGaussian

/-!
# Finite Pinsker inequality

This module derives the finite `ℓ₁` Pinsker bound for probability mass
functions with a full-support reference.  The proof uses the variational
lower bound for finite KL and Hoeffding's lemma applied to the signed mass
difference witness.
-/

open scoped BigOperators

namespace AppliedModelingLib

/--
A finite PMF's centred moment-generating function obeys Hoeffding's bound
when the score lies in `[-1, 1]`.
-/
theorem finiteMGF_centered_le_exp_half_sq
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (law : PMF Outcome) (score : Outcome → ℝ)
    (hscore_lower : ∀ outcome, -1 ≤ score outcome)
    (hscore_upper : ∀ outcome, score outcome ≤ 1)
    (step : ℝ) :
    Probability.finiteMGF law
        (fun outcome => score outcome - pmfExp law score) step ≤
      Real.exp (step ^ 2 / 2) := by
  classical
  letI : MeasurableSpace Outcome := ⊤
  have hmeas : AEMeasurable score law.toMeasure := Measurable.aemeasurable (by fun_prop)
  have hbounded : ∀ᵐ outcome ∂law.toMeasure, score outcome ∈ Set.Icc (-1 : ℝ) 1 :=
    Filter.Eventually.of_forall fun outcome => ⟨hscore_lower outcome, hscore_upper outcome⟩
  have hsubgaussian := ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc
    (μ := law.toMeasure) hmeas hbounded
  have hmgf := hsubgaussian.mgf_le step
  rw [pmfExp_eq_integral_toMeasure law score]
  rw [ProbabilityTheory.mgf, PMF.integral_eq_sum] at hmgf
  norm_num at hmgf
  simpa [Probability.finiteMGF, smul_eq_mul] using hmgf

/--
The finite KL divergence dominates every scaled expected-score functional
minus the corresponding log partition function.  This is the finite
variational inequality used by the Pinsker argument below.
-/
theorem scaled_pmfExp_sub_log_finiteMGF_le_finiteKLDivergence
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (candidate reference : PMF Outcome) (utility : Outcome → ℝ)
    (inverseTemperature : ℝ) (hreference : PMFFullSupport reference) :
    inverseTemperature * pmfExp candidate utility -
        Real.log (Probability.finiteMGF reference utility inverseTemperature) ≤
      finiteKLDivergence candidate reference := by
  have hlog : ∀ outcome : Outcome,
      Real.log (exponentialTilt reference utility inverseTemperature outcome).toReal =
        Real.log (reference outcome).toReal + inverseTemperature * utility outcome -
          Real.log (Probability.finiteMGF reference utility inverseTemperature) := by
    intro outcome
    have hratio := exponentialTilt_log_ratio
      reference utility inverseTemperature hreference outcome
    linarith
  have hkl :
      finiteKLDivergence candidate
          (exponentialTilt reference utility inverseTemperature) =
        finiteKLDivergence candidate reference -
          inverseTemperature * pmfExp candidate utility +
            Real.log (Probability.finiteMGF reference utility inverseTemperature) := by
    unfold finiteKLDivergence pmfExp
    calc
      ∑ outcome : Outcome,
          (candidate outcome).toReal *
            (Real.log (candidate outcome).toReal -
              Real.log (exponentialTilt reference utility inverseTemperature outcome).toReal) =
          ∑ outcome : Outcome,
            (((candidate outcome).toReal *
              (Real.log (candidate outcome).toReal - Real.log (reference outcome).toReal) -
              inverseTemperature * ((candidate outcome).toReal * utility outcome)) +
              (candidate outcome).toReal *
                Real.log (Probability.finiteMGF reference utility inverseTemperature)) := by
              refine Finset.sum_congr rfl fun outcome _ => ?_
              rw [hlog outcome]
              ring
      _ =
          (∑ outcome : Outcome,
            (candidate outcome).toReal *
              (Real.log (candidate outcome).toReal - Real.log (reference outcome).toReal)) -
            inverseTemperature *
              (∑ outcome : Outcome, (candidate outcome).toReal * utility outcome) +
              (∑ outcome : Outcome, (candidate outcome).toReal) *
                Real.log (Probability.finiteMGF reference utility inverseTemperature) := by
              rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
                ← Finset.mul_sum, Finset.sum_mul]
      _ = finiteKLDivergence candidate reference -
          inverseTemperature * pmfExp candidate utility +
            Real.log (Probability.finiteMGF reference utility inverseTemperature) := by
              rw [pmfToRealSum]
              simp only [finiteKLDivergence, pmfExp]
              ring
  have hnonneg := finiteKLDivergence_nonneg candidate
    (exponentialTilt reference utility inverseTemperature)
    (exponentialTilt_fullSupport reference utility inverseTemperature hreference)
  rw [hkl] at hnonneg
  linarith

/--
The finite variational KL lower bound needs only absolute continuity of the
candidate with respect to the reference.  At reference-zero atoms the
candidate mass is zero, so the pointwise tilt identity is used only on the
common positive support.
-/
theorem scaled_pmfExp_sub_log_finiteMGF_le_finiteKLDivergence_of_absoluteContinuous
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (candidate reference : PMF Outcome) (utility : Outcome → ℝ)
    (inverseTemperature : ℝ)
    (hcontinuous : PMFAbsoluteContinuous candidate reference) :
    inverseTemperature * pmfExp candidate utility -
        Real.log (Probability.finiteMGF reference utility inverseTemperature) ≤
      finiteKLDivergence candidate reference := by
  have htiltContinuous : PMFAbsoluteContinuous candidate
      (exponentialTilt reference utility inverseTemperature) := by
    intro outcome hcandidate
    rw [exponentialTilt_apply_toReal]
    exact div_pos
      (mul_pos (hcontinuous outcome hcandidate) (Real.exp_pos _))
      (Probability.finiteMGF_pos reference utility inverseTemperature)
  have hkl :
      finiteKLDivergence candidate
          (exponentialTilt reference utility inverseTemperature) =
        finiteKLDivergence candidate reference -
          inverseTemperature * pmfExp candidate utility +
            Real.log (Probability.finiteMGF reference utility inverseTemperature) := by
    unfold finiteKLDivergence pmfExp
    calc
      ∑ outcome : Outcome,
          (candidate outcome).toReal *
            (Real.log (candidate outcome).toReal -
              Real.log (exponentialTilt reference utility inverseTemperature outcome).toReal) =
          ∑ outcome : Outcome,
            (((candidate outcome).toReal *
              (Real.log (candidate outcome).toReal - Real.log (reference outcome).toReal) -
              inverseTemperature * ((candidate outcome).toReal * utility outcome)) +
              (candidate outcome).toReal *
                Real.log (Probability.finiteMGF reference utility inverseTemperature)) := by
            refine Finset.sum_congr rfl fun outcome _ => ?_
            by_cases hcandidate_zero : (candidate outcome).toReal = 0
            · simp [hcandidate_zero]
            · have hcandidate_pos : 0 < (candidate outcome).toReal :=
                lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hcandidate_zero)
              have href_pos : 0 < (reference outcome).toReal :=
                hcontinuous outcome hcandidate_pos
              have hratio := exponentialTilt_log_ratio_of_pos
                reference utility inverseTemperature href_pos
              have hlogtilt :
                  Real.log (exponentialTilt reference utility inverseTemperature outcome).toReal =
                    Real.log (reference outcome).toReal + inverseTemperature * utility outcome -
                      Real.log (Probability.finiteMGF reference utility inverseTemperature) := by
                linarith
              rw [hlogtilt]
              ring
      _ =
          (∑ outcome : Outcome,
            (candidate outcome).toReal *
              (Real.log (candidate outcome).toReal - Real.log (reference outcome).toReal)) -
            inverseTemperature *
              (∑ outcome : Outcome, (candidate outcome).toReal * utility outcome) +
              (∑ outcome : Outcome, (candidate outcome).toReal) *
                Real.log (Probability.finiteMGF reference utility inverseTemperature) := by
              rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
                ← Finset.mul_sum, Finset.sum_mul]
      _ = finiteKLDivergence candidate reference -
          inverseTemperature * pmfExp candidate utility +
            Real.log (Probability.finiteMGF reference utility inverseTemperature) := by
              rw [pmfToRealSum]
              simp only [finiteKLDivergence, pmfExp]
              ring
  have hnonneg := finiteKLDivergence_nonneg_of_absoluteContinuous candidate
    (exponentialTilt reference utility inverseTemperature) htiltContinuous
  rw [hkl] at hnonneg
  linarith

/--
The `±1` witness that selects the positive part of a finite PMF mass
difference.  Its expectation gap is exactly the coordinate `ℓ₁` distance.
-/
noncomputable def pmfMassDifferenceSign
    {Outcome : Type*} [DecidableEq Outcome]
    (first second : PMF Outcome) (outcome : Outcome) : ℝ :=
  if (second outcome).toReal ≤ (first outcome).toReal then 1 else -1

theorem pmfMassDifferenceSign_mem_Icc
    {Outcome : Type*} [DecidableEq Outcome]
    (first second : PMF Outcome) (outcome : Outcome) :
    pmfMassDifferenceSign first second outcome ∈ Set.Icc (-1 : ℝ) 1 := by
  unfold pmfMassDifferenceSign
  split <;> norm_num

/--
The signed-mass witness turns the difference of finite expectations into the
finite `ℓ₁` distance of the two real mass vectors.
-/
theorem pmfExp_sub_pmfExp_massDifferenceSign_eq_l1
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (first second : PMF Outcome) :
    pmfExp first (pmfMassDifferenceSign first second) -
        pmfExp second (pmfMassDifferenceSign first second) =
      FiniteDimensionalNorms.l1
        (fun outcome => (first outcome).toReal - (second outcome).toReal) := by
  have hterm : ∀ outcome : Outcome,
      ((first outcome).toReal - (second outcome).toReal) *
          pmfMassDifferenceSign first second outcome =
        |(first outcome).toReal - (second outcome).toReal| := by
    intro outcome
    unfold pmfMassDifferenceSign
    split
    · rw [mul_one, abs_of_nonneg]
      exact sub_nonneg.mpr ‹(second outcome).toReal ≤ (first outcome).toReal›
    · rw [mul_neg, abs_of_neg]
      · ring
      · exact sub_neg.mpr (lt_of_not_ge ‹¬ (second outcome).toReal ≤ (first outcome).toReal›)
  unfold pmfExp FiniteDimensionalNorms.l1
  calc
    (∑ outcome : Outcome,
        (first outcome).toReal * pmfMassDifferenceSign first second outcome) -
        ∑ outcome : Outcome,
          (second outcome).toReal * pmfMassDifferenceSign first second outcome =
      ∑ outcome : Outcome,
        ((first outcome).toReal - (second outcome).toReal) *
          pmfMassDifferenceSign first second outcome := by
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun outcome _ => ?_
          ring
    _ = ∑ outcome : Outcome,
        |(first outcome).toReal - (second outcome).toReal| := by
        refine Finset.sum_congr rfl fun outcome _ => hterm outcome

/--
Variational KL lower bound along the signed-mass witness.  Hoeffding's lemma
controls the witness's centred log-MGF, so this is a fully finite statement.
-/
theorem finiteKLDivergence_signed_mass_lower_bound
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (first second : PMF Outcome) (hsecond : PMFFullSupport second) (step : ℝ) :
    step *
        FiniteDimensionalNorms.l1
          (fun outcome => (first outcome).toReal - (second outcome).toReal) -
        step ^ 2 / 2 ≤
      finiteKLDivergence first second := by
  let witness : Outcome → ℝ := pmfMassDifferenceSign first second
  have hwitness_lower : ∀ outcome, -1 ≤ witness outcome := by
    intro outcome
    exact (pmfMassDifferenceSign_mem_Icc first second outcome).1
  have hwitness_upper : ∀ outcome, witness outcome ≤ 1 := by
    intro outcome
    exact (pmfMassDifferenceSign_mem_Icc first second outcome).2
  have hcentered := finiteMGF_centered_le_exp_half_sq
    second witness hwitness_lower hwitness_upper step
  have hlogcentered :
      Probability.finiteLogMGF second
          (fun outcome => witness outcome - pmfExp second witness) step ≤
        step ^ 2 / 2 := by
    unfold Probability.finiteLogMGF
    exact (Real.log_le_iff_le_exp
      (Probability.finiteMGF_pos second
        (fun outcome => witness outcome - pmfExp second witness) step)).mpr hcentered
  rw [Probability.finiteLogMGF_sub_const] at hlogcentered
  change Real.log (Probability.finiteMGF second witness step) -
      step * pmfExp second witness ≤ step ^ 2 / 2 at hlogcentered
  have hvariational := scaled_pmfExp_sub_log_finiteMGF_le_finiteKLDivergence
    first second witness step hsecond
  have hmasses := pmfExp_sub_pmfExp_massDifferenceSign_eq_l1 first second
  change pmfExp first witness - pmfExp second witness = _ at hmasses
  calc
    step * FiniteDimensionalNorms.l1
          (fun outcome => (first outcome).toReal - (second outcome).toReal) -
        step ^ 2 / 2 =
      step * pmfExp first witness - step * pmfExp second witness - step ^ 2 / 2 := by
        rw [← hmasses]
        ring
    _ ≤ finiteKLDivergence first second := by linarith

/--
The signed-mass variational lower bound also holds when the reference PMF may
vanish away from the first PMF's support.
-/
theorem finiteKLDivergence_signed_mass_lower_bound_of_absoluteContinuous
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (first second : PMF Outcome) (hcontinuous : PMFAbsoluteContinuous first second) (step : ℝ) :
    step *
        FiniteDimensionalNorms.l1
          (fun outcome => (first outcome).toReal - (second outcome).toReal) -
        step ^ 2 / 2 ≤
      finiteKLDivergence first second := by
  let witness : Outcome → ℝ := pmfMassDifferenceSign first second
  have hwitness_lower : ∀ outcome, -1 ≤ witness outcome := by
    intro outcome
    exact (pmfMassDifferenceSign_mem_Icc first second outcome).1
  have hwitness_upper : ∀ outcome, witness outcome ≤ 1 := by
    intro outcome
    exact (pmfMassDifferenceSign_mem_Icc first second outcome).2
  have hcentered := finiteMGF_centered_le_exp_half_sq
    second witness hwitness_lower hwitness_upper step
  have hlogcentered :
      Probability.finiteLogMGF second
          (fun outcome => witness outcome - pmfExp second witness) step ≤
        step ^ 2 / 2 := by
    unfold Probability.finiteLogMGF
    exact (Real.log_le_iff_le_exp
      (Probability.finiteMGF_pos second
        (fun outcome => witness outcome - pmfExp second witness) step)).mpr hcentered
  rw [Probability.finiteLogMGF_sub_const] at hlogcentered
  change Real.log (Probability.finiteMGF second witness step) -
      step * pmfExp second witness ≤ step ^ 2 / 2 at hlogcentered
  have hvariational :=
    scaled_pmfExp_sub_log_finiteMGF_le_finiteKLDivergence_of_absoluteContinuous
      first second witness step hcontinuous
  have hmasses := pmfExp_sub_pmfExp_massDifferenceSign_eq_l1 first second
  change pmfExp first witness - pmfExp second witness = _ at hmasses
  calc
    step * FiniteDimensionalNorms.l1
          (fun outcome => (first outcome).toReal - (second outcome).toReal) -
        step ^ 2 / 2 =
      step * pmfExp first witness - step * pmfExp second witness - step ^ 2 / 2 := by
        rw [← hmasses]
        ring
    _ ≤ finiteKLDivergence first second := by linarith

/--
Finite Pinsker inequality in the repository's real-mass and coordinate-`ℓ₁`
API.  The full-support reference is exactly what makes the KL expression
finite and gives the entropy strong-convexity inequality needed by NLHF.
-/
theorem finitePinsker_l1_sq_le_finiteKLDivergence
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (first second : PMF Outcome) (hsecond : PMFFullSupport second) :
    (1 / 2 : ℝ) *
        (FiniteDimensionalNorms.l1
          (fun outcome => (first outcome).toReal - (second outcome).toReal)) ^ 2 ≤
      finiteKLDivergence first second := by
  have hbound := finiteKLDivergence_signed_mass_lower_bound first second hsecond
    (FiniteDimensionalNorms.l1
      (fun outcome => (first outcome).toReal - (second outcome).toReal))
  nlinarith

/--
Finite Pinsker inequality with the source-faithful absolute-continuity
hypothesis.  No full-support condition is needed: zero reference atoms carry
zero first-law mass and are handled by the preceding variational lemma.
-/
theorem finitePinsker_l1_sq_le_finiteKLDivergence_of_absoluteContinuous
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (first second : PMF Outcome) (hcontinuous : PMFAbsoluteContinuous first second) :
    (1 / 2 : ℝ) *
        (FiniteDimensionalNorms.l1
          (fun outcome => (first outcome).toReal - (second outcome).toReal)) ^ 2 ≤
      finiteKLDivergence first second := by
  have hbound :=
    finiteKLDivergence_signed_mass_lower_bound_of_absoluteContinuous first second hcontinuous
      (FiniteDimensionalNorms.l1
        (fun outcome => (first outcome).toReal - (second outcome).toReal))
  nlinarith

end AppliedModelingLib
