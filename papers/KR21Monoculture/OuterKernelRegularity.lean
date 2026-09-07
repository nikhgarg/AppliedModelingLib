import KR21Monoculture.Distributional
import AppliedModelingLib.Foundations.Math.IntegralConvergence

open AppliedModelingLib MeasureTheory Filter
open scoped Topology

namespace KR21Monoculture

/-!
# Regularity of finite ranking kernels under an outer value law

This file supplies a dominated-convergence bridge used by source-shaped outer
arguments.  It derives continuity of an averaged finite-PMF payoff from
atomwise continuity, atom measurability, and coordinatewise first moments.
No continuity of the already-averaged payoff is assumed.
-/

namespace DistributionalAccuracyFamily

/-- A finite expected selected-coordinate payoff remains continuous after
averaging over an outer value law.  The proof is termwise dominated
convergence: every PMF atom lies in `[0, 1]`, so the selected coordinate's
absolute value is an integrable dominator. -/
theorem continuousAt_outerExpected_pmfExp_valueSelection_of_atomwise
    {n : ℕ} {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (D : Measure (ValueProfile n))
    (law : ℝ → ValueProfile n → PMF alpha)
    (select : alpha → Candidate n) (theta0 : ℝ)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D)
    (hatom_measurable : ∀ theta a,
      AEStronglyMeasurable (fun value : ValueProfile n =>
        ((law theta value) a).toReal) D)
    (hatom_continuous : ∀ value a,
      EpsilonContinuousAt (fun theta => ((law theta value) a).toReal) theta0) :
    ContinuousAt
      (fun theta => outerExpected D
        (fun value => AppliedModelingLib.pmfExp (law theta value)
          (fun a => value (select a)))) theta0 := by
  let term : alpha → ℝ → ValueProfile n → ℝ :=
    fun a theta value => ((law theta value) a).toReal * value (select a)
  have hterm_integrable : ∀ a theta, Integrable (term a theta) D := by
    intro a theta
    refine (hvalue (select a)).abs.mono' ?_ ?_
    · exact (hatom_measurable theta a).mul
        (hvalue (select a)).aestronglyMeasurable
    · filter_upwards with value
      dsimp [term]
      rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
      simpa [mul_comm] using
        (mul_le_of_le_one_right (abs_nonneg (value (select a)))
          (AppliedModelingLib.pmf_apply_toReal_le_one (law theta value) a))
  have hterm_continuous : ∀ a,
      ContinuousAt (fun theta => ∫ value, term a theta value ∂D) theta0 := by
    intro a
    change Tendsto (fun theta => ∫ value, term a theta value ∂D)
      (𝓝 theta0) (𝓝 (∫ value, term a theta0 value ∂D))
    have hlim : ∀ᵐ value ∂D,
        Tendsto (fun theta => term a theta value) (𝓝 theta0)
          (𝓝 (term a theta0 value)) := by
      filter_upwards with value
      exact
        ((continuousAt_of_epsilonContinuousAt
          (hatom_continuous value a)).tendsto.mul tendsto_const_nhds)
    exact MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (fun value => |value (select a)|)
      (Filter.Eventually.of_forall fun theta =>
        (hatom_measurable theta a).mul
          (hvalue (select a)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun theta => by
        filter_upwards with value
        dsimp [term]
        rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
        simpa [mul_comm] using
          (mul_le_of_le_one_right (abs_nonneg (value (select a)))
            (AppliedModelingLib.pmf_apply_toReal_le_one (law theta value) a)))
      (hvalue (select a)).abs hlim
  have hsum : ContinuousAt
      (fun theta => ∑ a : alpha, ∫ value, term a theta value ∂D) theta0 := by
    exact AppliedModelingLib.continuousAt_finset_sum Finset.univ
      (fun a _ => hterm_continuous a)
  have hrewrite :
      (fun theta => outerExpected D
        (fun value => AppliedModelingLib.pmfExp (law theta value)
          (fun a => value (select a)))) =
        fun theta => ∑ a : alpha, ∫ value, term a theta value ∂D := by
    funext theta
    unfold outerExpected AppliedModelingLib.pmfExp
    rw [MeasureTheory.integral_finset_sum]
    intro a _
    exact hterm_integrable a theta
  rw [hrewrite]
  exact hsum

/-- Epsilon-delta version of
`continuousAt_outerExpected_pmfExp_valueSelection_of_atomwise`. -/
theorem epsilonContinuousAt_outerExpected_pmfExp_valueSelection_of_atomwise
    {n : ℕ} {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (D : Measure (ValueProfile n))
    (law : ℝ → ValueProfile n → PMF alpha)
    (select : alpha → Candidate n) (theta0 : ℝ)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D)
    (hatom_measurable : ∀ theta a,
      AEStronglyMeasurable (fun value : ValueProfile n =>
        ((law theta value) a).toReal) D)
    (hatom_continuous : ∀ value a,
      EpsilonContinuousAt (fun theta => ((law theta value) a).toReal) theta0) :
    EpsilonContinuousAt
      (fun theta => outerExpected D
        (fun value => AppliedModelingLib.pmfExp (law theta value)
          (fun a => value (select a)))) theta0 :=
  epsilonContinuousAt_of_continuousAt
    (continuousAt_outerExpected_pmfExp_valueSelection_of_atomwise
      D law select theta0 hvalue hatom_measurable hatom_continuous)

/-- A finite independent-pair expected selected-coordinate payoff remains
continuous after averaging over an outer value law when only the right ranking
kernel varies with the parameter.  Both PMF factors are bounded by one, so a
single selected-coordinate first moment remains a dominator. -/
theorem continuousAt_outerExpected_pmfPairExp_right_valueSelection_of_atomwise
    {n : ℕ} {alpha beta : Type*}
    [Fintype alpha] [DecidableEq alpha] [Fintype beta] [DecidableEq beta]
    (D : Measure (ValueProfile n))
    (leftLaw : ValueProfile n → PMF alpha)
    (rightLaw : ℝ → ValueProfile n → PMF beta)
    (select : alpha → beta → Candidate n) (theta0 : ℝ)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D)
    (hleft_measurable : ∀ a,
      AEStronglyMeasurable (fun value : ValueProfile n =>
        ((leftLaw value) a).toReal) D)
    (hright_measurable : ∀ theta b,
      AEStronglyMeasurable (fun value : ValueProfile n =>
        ((rightLaw theta value) b).toReal) D)
    (hright_continuous : ∀ value b,
      EpsilonContinuousAt (fun theta => ((rightLaw theta value) b).toReal) theta0) :
    ContinuousAt
      (fun theta => outerExpected D
        (fun value => AppliedModelingLib.pmfPairExp (leftLaw value) (rightLaw theta value)
          (fun a b => value (select a b)))) theta0 := by
  let term : alpha → beta → ℝ → ValueProfile n → ℝ :=
    fun a b theta value =>
      ((leftLaw value) a).toReal * ((rightLaw theta value) b).toReal *
        value (select a b)
  have hterm_bound : ∀ a b theta value,
      ‖term a b theta value‖ ≤ |value (select a b)| := by
    intro a b theta value
    dsimp [term]
    rw [abs_mul, abs_mul,
      abs_of_nonneg ENNReal.toReal_nonneg,
      abs_of_nonneg ENNReal.toReal_nonneg]
    calc
      ((leftLaw value) a).toReal * ((rightLaw theta value) b).toReal *
          |value (select a b)| =
        ((leftLaw value) a).toReal *
          (((rightLaw theta value) b).toReal * |value (select a b)|) := by
          ring
      _ ≤ ((rightLaw theta value) b).toReal * |value (select a b)| := by
        rw [mul_comm]
        exact mul_le_of_le_one_right
          (mul_nonneg ENNReal.toReal_nonneg (abs_nonneg _))
          (AppliedModelingLib.pmf_apply_toReal_le_one (leftLaw value) a)
      _ ≤ |value (select a b)| := by
        rw [mul_comm]
        exact mul_le_of_le_one_right (abs_nonneg (value (select a b)))
          (AppliedModelingLib.pmf_apply_toReal_le_one (rightLaw theta value) b)
  have hterm_integrable : ∀ a b theta, Integrable (term a b theta) D := by
    intro a b theta
    refine (hvalue (select a b)).abs.mono' ?_ ?_
    · exact ((hleft_measurable a).mul (hright_measurable theta b)).mul
        (hvalue (select a b)).aestronglyMeasurable
    · filter_upwards with value
      exact hterm_bound a b theta value
  have hterm_continuous : ∀ a b,
      ContinuousAt (fun theta => ∫ value, term a b theta value ∂D) theta0 := by
    intro a b
    change Tendsto (fun theta => ∫ value, term a b theta value ∂D)
      (𝓝 theta0) (𝓝 (∫ value, term a b theta0 value ∂D))
    have hlim : ∀ᵐ value ∂D,
        Tendsto (fun theta => term a b theta value) (𝓝 theta0)
          (𝓝 (term a b theta0 value)) := by
      filter_upwards with value
      have hright := (continuousAt_of_epsilonContinuousAt
        (hright_continuous value b)).tendsto
      exact (tendsto_const_nhds.mul hright).mul tendsto_const_nhds
    exact MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (fun value => |value (select a b)|)
      (Filter.Eventually.of_forall fun theta =>
        ((hleft_measurable a).mul (hright_measurable theta b)).mul
          (hvalue (select a b)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun theta => by
        filter_upwards with value
        exact hterm_bound a b theta value)
      (hvalue (select a b)).abs hlim
  have hsum : ContinuousAt
      (fun theta => ∑ a : alpha, ∑ b : beta,
        ∫ value, term a b theta value ∂D) theta0 := by
    exact AppliedModelingLib.continuousAt_finset_sum Finset.univ
      (fun a _ => AppliedModelingLib.continuousAt_finset_sum Finset.univ
        (fun b _ => hterm_continuous a b))
  have hrewrite :
      (fun theta => outerExpected D
        (fun value => AppliedModelingLib.pmfPairExp (leftLaw value) (rightLaw theta value)
          (fun a b => value (select a b)))) =
        fun theta => ∑ a : alpha, ∑ b : beta,
          ∫ value, term a b theta value ∂D := by
    funext theta
    unfold outerExpected AppliedModelingLib.pmfPairExp AppliedModelingLib.pmfExp
    simp_rw [Finset.mul_sum]
    simp only [term, mul_assoc]
    rw [MeasureTheory.integral_finset_sum]
    · refine Finset.sum_congr rfl ?_
      intro a _
      exact MeasureTheory.integral_finset_sum Finset.univ
        (fun b _ => by
          simpa [term, mul_assoc] using hterm_integrable a b theta)
    · intro a _
      exact MeasureTheory.integrable_finset_sum Finset.univ
        (fun b _ => by
          simpa [term, mul_assoc] using hterm_integrable a b theta)
  rw [hrewrite]
  exact hsum

/-- Epsilon-delta version of the right-varying pair-payoff regularity bridge. -/
theorem epsilonContinuousAt_outerExpected_pmfPairExp_right_valueSelection_of_atomwise
    {n : ℕ} {alpha beta : Type*}
    [Fintype alpha] [DecidableEq alpha] [Fintype beta] [DecidableEq beta]
    (D : Measure (ValueProfile n))
    (leftLaw : ValueProfile n → PMF alpha)
    (rightLaw : ℝ → ValueProfile n → PMF beta)
    (select : alpha → beta → Candidate n) (theta0 : ℝ)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D)
    (hleft_measurable : ∀ a,
      AEStronglyMeasurable (fun value : ValueProfile n =>
        ((leftLaw value) a).toReal) D)
    (hright_measurable : ∀ theta b,
      AEStronglyMeasurable (fun value : ValueProfile n =>
        ((rightLaw theta value) b).toReal) D)
    (hright_continuous : ∀ value b,
      EpsilonContinuousAt (fun theta => ((rightLaw theta value) b).toReal) theta0) :
    EpsilonContinuousAt
      (fun theta => outerExpected D
        (fun value => AppliedModelingLib.pmfPairExp (leftLaw value) (rightLaw theta value)
          (fun a b => value (select a b)))) theta0 :=
  epsilonContinuousAt_of_continuousAt
    (continuousAt_outerExpected_pmfPairExp_right_valueSelection_of_atomwise
      D leftLaw rightLaw select theta0 hvalue hleft_measurable
      hright_measurable hright_continuous)

/-- The source's outer all-algorithm payoff `f` is continuous in algorithm
accuracy when finite ranking atoms are measurable in the value draw and
atomwise continuous in accuracy.  Coordinatewise first moments are sufficient
for the two finite payoff terms. -/
theorem epsilonContinuousAt_theorem1_f_of_atomwise
    {n : ℕ} (F : DistributionalAccuracyFamily n)
    (D : Measure (ValueProfile n)) (thetaH theta0 : ℝ)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D)
    (hatom_measurable : ∀ theta pi,
      AEStronglyMeasurable (fun profile : ValueProfile n =>
        ((F.dist theta profile) pi).toReal) D)
    (hatom_continuous : ∀ value pi,
      EpsilonContinuousAt (fun theta => ((F.dist theta value) pi).toReal) theta0) :
    EpsilonContinuousAt
      (fun thetaA => F.theorem1_f D thetaA thetaH) theta0 := by
  change EpsilonContinuousAt
    (fun thetaA => outerExpected D
      (fun value => expectedFirstMoverUtility (F.dist thetaA value) value) +
      outerExpected D
        (fun value => expectedSecondMoverShared (F.dist thetaA value) value)) theta0
  apply epsilonContinuousAt_add
  · exact epsilonContinuousAt_outerExpected_pmfExp_valueSelection_of_atomwise
      D F.dist firstChoice theta0 hvalue
      (fun theta pi => hatom_measurable theta pi) hatom_continuous
  · exact epsilonContinuousAt_outerExpected_pmfExp_valueSelection_of_atomwise
      D F.dist secondChoice theta0 hvalue
      (fun theta pi => hatom_measurable theta pi) hatom_continuous

/-- The source's outer mixed payoff `g` is continuous in algorithm accuracy
under the same atomwise and first-moment regularity.  The human first-mover
term is constant; the remaining term is a right-varying finite pair payoff. -/
theorem epsilonContinuousAt_theorem1_g_of_atomwise
    {n : ℕ} (F : DistributionalAccuracyFamily n)
    (D : Measure (ValueProfile n)) (thetaH theta0 : ℝ)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D)
    (hatom_measurable : ∀ theta pi,
      AEStronglyMeasurable (fun profile : ValueProfile n =>
        ((F.dist theta profile) pi).toReal) D)
    (hatom_continuous : ∀ value pi,
      EpsilonContinuousAt (fun theta => ((F.dist theta value) pi).toReal) theta0) :
    EpsilonContinuousAt
      (fun thetaA => F.theorem1_g D thetaA thetaH) theta0 := by
  change EpsilonContinuousAt
    (fun thetaA => outerExpected D
      (fun value => expectedFirstMoverUtility (F.dist thetaH value) value) +
      outerExpected D
        (fun value => expectedSecondMoverIndependent
          (F.dist thetaH value) (F.dist thetaA value) value)) theta0
  apply epsilonContinuousAt_add
  · exact epsilonContinuousAt_const _ theta0
  · exact epsilonContinuousAt_outerExpected_pmfPairExp_right_valueSelection_of_atomwise
      D (fun value => F.dist thetaH value) F.dist
      (fun second first => bestRemainingAfter second (firstChoice first)) theta0 hvalue
      (fun pi => hatom_measurable thetaH pi)
      (fun theta pi => hatom_measurable theta pi) hatom_continuous

end DistributionalAccuracyFamily

end KR21Monoculture
