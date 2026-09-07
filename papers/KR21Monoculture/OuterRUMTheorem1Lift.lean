import KR21Monoculture.OuterKernelRegularity
import KR21Monoculture.Theorem2OuterConditionalSource
import KR21Monoculture.Definition2AsymptoticBridge

open AppliedModelingLib MeasureTheory Filter
open scoped Topology

namespace KR21Monoculture
namespace DistributionalAccuracyFamily

/-!
# Outer RUM Theorem 1 lift

The source fixes the true value order before introducing the outer law `D`.
This module therefore works with one fixed ranking center and an almost-
everywhere source-order condition; it never sorts or relabels individual value
profiles.  The central new step is a dominated-convergence lift of atomwise
high-accuracy concentration to one common algorithmic accuracy outside the
outer expectation.

Kernel measurability and finite first moments remain visible hypotheses.  They
are analytic regularity required to interpret the source's real-valued outer
payoffs, not conclusions inferred from a model declaration name.
-/

/-- Atomwise convergence to a fixed finite PMF transports through a
selected-coordinate outer expectation. -/
theorem tendsto_outerExpected_pmfExp_valueSelection_of_atomwise
    {n : ℕ} {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    (D : Measure (ValueProfile n))
    (law : ℝ → ValueProfile n → PMF alpha)
    (limitLaw : PMF alpha)
    (select : alpha → Candidate n)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D)
    (hatom_measurable : ∀ theta a,
      AEStronglyMeasurable (fun value : ValueProfile n =>
        ((law theta value) a).toReal) D)
    (hatom_tendsto : ∀ᵐ value ∂D, ∀ a,
      Tendsto (fun theta => ((law theta value) a).toReal) atTop
        (𝓝 ((limitLaw a).toReal))) :
    Tendsto
      (fun theta => outerExpected D
        (fun value => AppliedModelingLib.pmfExp (law theta value)
          (fun a => value (select a)))) atTop
      (𝓝 (outerExpected D
        (fun value => AppliedModelingLib.pmfExp limitLaw
          (fun a => value (select a))))) := by
  let term : alpha → ℝ → ValueProfile n → ℝ :=
    fun a theta value => ((law theta value) a).toReal * value (select a)
  let limitTerm : alpha → ValueProfile n → ℝ :=
    fun a value => (limitLaw a).toReal * value (select a)
  have hterm_tendsto : ∀ a,
      Tendsto (fun theta => ∫ value, term a theta value ∂D) atTop
        (𝓝 (∫ value, limitTerm a value ∂D)) := by
    intro a
    have hlim : ∀ᵐ value ∂D,
        Tendsto (fun theta => term a theta value) atTop
          (𝓝 (limitTerm a value)) := by
      filter_upwards [hatom_tendsto] with value hvalue_tendsto
      exact (hvalue_tendsto a).mul tendsto_const_nhds
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
  have hsum : Tendsto
      (fun theta => ∑ a : alpha, ∫ value, term a theta value ∂D) atTop
      (𝓝 (∑ a : alpha, ∫ value, limitTerm a value ∂D)) := by
    exact tendsto_finset_sum Finset.univ (fun a _ => hterm_tendsto a)
  have hrewrite :
      (fun theta => outerExpected D
        (fun value => AppliedModelingLib.pmfExp (law theta value)
          (fun a => value (select a)))) =
        fun theta => ∑ a : alpha, ∫ value, term a theta value ∂D := by
    funext theta
    unfold outerExpected AppliedModelingLib.pmfExp
    rw [MeasureTheory.integral_finset_sum]
    intro a _
    refine (hvalue (select a)).abs.mono' ?_ ?_
    · exact (hatom_measurable theta a).mul
        (hvalue (select a)).aestronglyMeasurable
    · filter_upwards with value
      dsimp [term]
      rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
      simpa [mul_comm] using
        (mul_le_of_le_one_right (abs_nonneg (value (select a)))
          (AppliedModelingLib.pmf_apply_toReal_le_one (law theta value) a))
  have hlimit_rewrite :
      outerExpected D (fun value => AppliedModelingLib.pmfExp limitLaw
        (fun a => value (select a))) =
        ∑ a : alpha, ∫ value, limitTerm a value ∂D := by
    unfold outerExpected AppliedModelingLib.pmfExp
    rw [MeasureTheory.integral_finset_sum]
    intro a _
    exact (hvalue (select a)).const_mul _
  rw [hrewrite, hlimit_rewrite]
  exact hsum

/-- Atomwise convergence of the first ranking law transports through a finite
independent-pair selected-coordinate outer expectation. -/
theorem tendsto_outerExpected_pmfPairExp_right_valueSelection_of_atomwise
    {n : ℕ} {alpha beta : Type*}
    [Fintype alpha] [DecidableEq alpha] [Fintype beta] [DecidableEq beta]
    (D : Measure (ValueProfile n))
    (leftLaw : ValueProfile n → PMF alpha)
    (rightLaw : ℝ → ValueProfile n → PMF beta)
    (limitRightLaw : PMF beta)
    (select : alpha → beta → Candidate n)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D)
    (hleft_measurable : ∀ a,
      AEStronglyMeasurable (fun value : ValueProfile n =>
        ((leftLaw value) a).toReal) D)
    (hright_measurable : ∀ theta b,
      AEStronglyMeasurable (fun value : ValueProfile n =>
        ((rightLaw theta value) b).toReal) D)
    (hright_tendsto : ∀ᵐ value ∂D, ∀ b,
      Tendsto (fun theta => ((rightLaw theta value) b).toReal) atTop
        (𝓝 ((limitRightLaw b).toReal))) :
    Tendsto
      (fun theta => outerExpected D
        (fun value => AppliedModelingLib.pmfPairExp (leftLaw value) (rightLaw theta value)
          (fun a b => value (select a b)))) atTop
      (𝓝 (outerExpected D
        (fun value => AppliedModelingLib.pmfPairExp (leftLaw value) limitRightLaw
          (fun a b => value (select a b))))) := by
  let term : alpha → beta → ℝ → ValueProfile n → ℝ :=
    fun a b theta value =>
      ((leftLaw value) a).toReal * ((rightLaw theta value) b).toReal *
        value (select a b)
  let limitTerm : alpha → beta → ValueProfile n → ℝ :=
    fun a b value =>
      ((leftLaw value) a).toReal * (limitRightLaw b).toReal * value (select a b)
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
  have hlimitTerm_bound : ∀ a b value,
      ‖limitTerm a b value‖ ≤ |value (select a b)| := by
    intro a b value
    dsimp [limitTerm]
    rw [abs_mul, abs_mul,
      abs_of_nonneg ENNReal.toReal_nonneg,
      abs_of_nonneg ENNReal.toReal_nonneg]
    calc
      ((leftLaw value) a).toReal * (limitRightLaw b).toReal *
          |value (select a b)| =
        ((leftLaw value) a).toReal *
          ((limitRightLaw b).toReal * |value (select a b)|) := by
          ring
      _ ≤ (limitRightLaw b).toReal * |value (select a b)| := by
          rw [mul_comm]
          exact mul_le_of_le_one_right
            (mul_nonneg ENNReal.toReal_nonneg (abs_nonneg _))
            (AppliedModelingLib.pmf_apply_toReal_le_one (leftLaw value) a)
      _ ≤ |value (select a b)| := by
          rw [mul_comm]
          exact mul_le_of_le_one_right (abs_nonneg (value (select a b)))
            (AppliedModelingLib.pmf_apply_toReal_le_one limitRightLaw b)
  have hlimitTerm_integrable : ∀ a b, Integrable (limitTerm a b) D := by
    intro a b
    refine (hvalue (select a b)).abs.mono' ?_ ?_
    · exact ((hleft_measurable a).mul aestronglyMeasurable_const).mul
        (hvalue (select a b)).aestronglyMeasurable
    · filter_upwards with value
      exact hlimitTerm_bound a b value
  have hterm_tendsto : ∀ a b,
      Tendsto (fun theta => ∫ value, term a b theta value ∂D) atTop
        (𝓝 (∫ value, limitTerm a b value ∂D)) := by
    intro a b
    have hlim : ∀ᵐ value ∂D,
        Tendsto (fun theta => term a b theta value) atTop
          (𝓝 (limitTerm a b value)) := by
      filter_upwards [hright_tendsto] with value hvalue_tendsto
      exact (tendsto_const_nhds.mul (hvalue_tendsto b)).mul tendsto_const_nhds
    exact MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (fun value => |value (select a b)|)
      (Filter.Eventually.of_forall fun theta =>
        ((hleft_measurable a).mul (hright_measurable theta b)).mul
          (hvalue (select a b)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun theta => by
        filter_upwards with value
        exact hterm_bound a b theta value)
      (hvalue (select a b)).abs hlim
  have hsum : Tendsto
      (fun theta => ∑ a : alpha, ∑ b : beta,
        ∫ value, term a b theta value ∂D) atTop
      (𝓝 (∑ a : alpha, ∑ b : beta,
        ∫ value, limitTerm a b value ∂D)) := by
    exact tendsto_finset_sum Finset.univ (fun a _ =>
      tendsto_finset_sum Finset.univ (fun b _ => hterm_tendsto a b))
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
  have hlimit_rewrite :
      outerExpected D
        (fun value => AppliedModelingLib.pmfPairExp (leftLaw value) limitRightLaw
          (fun a b => value (select a b))) =
        ∑ a : alpha, ∑ b : beta,
          ∫ value, limitTerm a b value ∂D := by
    unfold outerExpected AppliedModelingLib.pmfPairExp AppliedModelingLib.pmfExp
    simp_rw [Finset.mul_sum]
    simp only [limitTerm, mul_assoc]
    rw [MeasureTheory.integral_finset_sum]
    · refine Finset.sum_congr rfl ?_
      intro a _
      exact MeasureTheory.integral_finset_sum Finset.univ
        (fun b _ => by
          simpa [limitTerm, mul_assoc] using hlimitTerm_integrable a b)
    · intro a _
      exact MeasureTheory.integrable_finset_sum Finset.univ
        (fun b _ => by
          simpa [limitTerm, mul_assoc] using hlimitTerm_integrable a b)
  rw [hrewrite, hlimit_rewrite]
  exact hsum

/-- The high-accuracy limit of the source's outer all-algorithm payoff. -/
noncomputable def theorem1_f_pureCenterLimit {n : ℕ}
    (D : Measure (ValueProfile n)) (center : Ranking n) : ℝ :=
  outerExpected D (fun value =>
      expectedFirstMoverUtility (PMF.pure center) value) +
    outerExpected D (fun value =>
      expectedSecondMoverShared (PMF.pure center) value)

/-- The high-accuracy limit of the source's outer mixed payoff, with the human
law held fixed and the algorithmic first-mover law converging to `center`. -/
noncomputable def theorem1_g_pureCenterLimit {n : ℕ}
    (F : DistributionalAccuracyFamily n) (D : Measure (ValueProfile n))
    (thetaH : ℝ) (center : Ranking n) : ℝ :=
  outerExpected D (fun value =>
      expectedFirstMoverUtility (F.dist thetaH value) value) +
    outerExpected D (fun value =>
      expectedSecondMoverIndependent (F.dist thetaH value) (PMF.pure center) value)

/-- Atomwise convergence of the algorithmic ranking law gives convergence of
the already-averaged all-algorithm payoff. -/
theorem tendsto_theorem1_f_to_pureCenterLimit_of_atomwise
    {n : ℕ} (F : DistributionalAccuracyFamily n)
    (D : Measure (ValueProfile n)) (thetaH : ℝ) (center : Ranking n)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D)
    (hatom_measurable : ∀ theta pi,
      AEStronglyMeasurable (fun value : ValueProfile n =>
        ((F.dist theta value) pi).toReal) D)
    (hatom_tendsto : ∀ᵐ value ∂D, ∀ pi,
      Tendsto (fun theta => ((F.dist theta value) pi).toReal) atTop
        (𝓝 (((PMF.pure center : PMF (Ranking n)) pi).toReal))) :
    Tendsto (fun thetaA => F.theorem1_f D thetaA thetaH) atTop
      (𝓝 (theorem1_f_pureCenterLimit D center)) := by
  have hfirst := tendsto_outerExpected_pmfExp_valueSelection_of_atomwise
    D F.dist (PMF.pure center) firstChoice hvalue hatom_measurable hatom_tendsto
  have hsecond := tendsto_outerExpected_pmfExp_valueSelection_of_atomwise
    D F.dist (PMF.pure center) secondChoice hvalue hatom_measurable hatom_tendsto
  change Tendsto
    (fun thetaA => outerExpected D
      (fun value => expectedFirstMoverUtility (F.dist thetaA value) value) +
      outerExpected D
        (fun value => expectedSecondMoverShared (F.dist thetaA value) value)) atTop
      (𝓝 (theorem1_f_pureCenterLimit D center))
  simpa [theorem1_f_pureCenterLimit, expectedFirstMoverUtility,
    expectedSecondMoverShared] using hfirst.add hsecond

/-- Atomwise convergence of the algorithmic ranking law gives convergence of
the already-averaged mixed payoff, with the human law fixed at `thetaH`. -/
theorem tendsto_theorem1_g_to_pureCenterLimit_of_atomwise
    {n : ℕ} (F : DistributionalAccuracyFamily n)
    (D : Measure (ValueProfile n)) (thetaH : ℝ) (center : Ranking n)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D)
    (hatom_measurable : ∀ theta pi,
      AEStronglyMeasurable (fun value : ValueProfile n =>
        ((F.dist theta value) pi).toReal) D)
    (hatom_tendsto : ∀ᵐ value ∂D, ∀ pi,
      Tendsto (fun theta => ((F.dist theta value) pi).toReal) atTop
        (𝓝 (((PMF.pure center : PMF (Ranking n)) pi).toReal))) :
    Tendsto (fun thetaA => F.theorem1_g D thetaA thetaH) atTop
      (𝓝 (F.theorem1_g_pureCenterLimit D thetaH center)) := by
  have hsecond :=
    tendsto_outerExpected_pmfPairExp_right_valueSelection_of_atomwise
      D (fun value => F.dist thetaH value) F.dist (PMF.pure center)
      (fun second first => bestRemainingAfter second (firstChoice first)) hvalue
      (fun pi => hatom_measurable thetaH pi) hatom_measurable hatom_tendsto
  change Tendsto
    (fun thetaA => outerExpected D
      (fun value => expectedFirstMoverUtility (F.dist thetaH value) value) +
      outerExpected D
        (fun value => expectedSecondMoverIndependent
          (F.dist thetaH value) (F.dist thetaA value) value)) atTop
      (𝓝 (F.theorem1_g_pureCenterLimit D thetaH center))
  simpa [theorem1_g_pureCenterLimit, expectedFirstMoverUtility,
    expectedSecondMoverIndependent, secondMoverUtility] using tendsto_const_nhds.add hsecond

/-- A strict pure-center limit gap is eventually realized by one common
algorithmic accuracy outside the outer expectation. -/
theorem exists_outer_first_dominance_of_atomwise_tendsto
    {n : ℕ} (F : DistributionalAccuracyFamily n)
    (D : Measure (ValueProfile n)) (thetaH : ℝ) (center : Ranking n)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D)
    (hatom_measurable : ∀ theta pi,
      AEStronglyMeasurable (fun value : ValueProfile n =>
        ((F.dist theta value) pi).toReal) D)
    (hatom_tendsto : ∀ᵐ value ∂D, ∀ pi,
      Tendsto (fun theta => ((F.dist theta value) pi).toReal) atTop
        (𝓝 (((PMF.pure center : PMF (Ranking n)) pi).toReal)))
    (hpure_gap : F.theorem1_g_pureCenterLimit D thetaH center <
      theorem1_f_pureCenterLimit D center) :
    ∀ lower, thetaH < lower → ∃ hi, lower < hi ∧
      F.theorem1_g D hi thetaH < F.theorem1_f D hi thetaH := by
  intro lower _
  have hf := tendsto_theorem1_f_to_pureCenterLimit_of_atomwise
    F D thetaH center hvalue hatom_measurable hatom_tendsto
  have hg := tendsto_theorem1_g_to_pureCenterLimit_of_atomwise
    F D thetaH center hvalue hatom_measurable hatom_tendsto
  have hdiff : Tendsto
      (fun thetaA => F.theorem1_f D thetaA thetaH - F.theorem1_g D thetaA thetaH)
      atTop
      (𝓝 (theorem1_f_pureCenterLimit D center -
        F.theorem1_g_pureCenterLimit D thetaH center)) := hf.sub hg
  have hlimit_pos : 0 < theorem1_f_pureCenterLimit D center -
      F.theorem1_g_pureCenterLimit D thetaH center := sub_pos.mpr hpure_gap
  have heventual_positive : ∀ᶠ thetaA in atTop,
      0 < F.theorem1_f D thetaA thetaH - F.theorem1_g D thetaA thetaH :=
    hdiff.eventually (eventually_gt_nhds hlimit_pos)
  rcases (heventual_positive.and (eventually_gt_atTop lower)).exists with
    ⟨hi, hpositive, hlower_hi⟩
  exact ⟨hi, hlower_hi, sub_pos.mp hpositive⟩

/-- The source's fixed true order, imposed only on the support of `D`, and
pointwise Definition 2 imply the strict outer pure-center limit gap.  The four
integrability hypotheses make the conversion between the two separately
averaged payoff terms and their pointwise sums explicit. -/
theorem theorem1_pureCenterLimit_gap_of_ae_pointwise
    {n : ℕ} (F : DistributionalAccuracyFamily n)
    (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    (thetaH : ℝ) (center : Ranking n)
    (hgfirst : Integrable (fun value =>
      expectedFirstMoverUtility (F.dist thetaH value) value) D)
    (hgsecond : Integrable (fun value =>
      expectedSecondMoverIndependent (F.dist thetaH value) (PMF.pure center) value) D)
    (hffirst : Integrable (fun value =>
      expectedFirstMoverUtility (PMF.pure center) value) D)
    (hfsecond : Integrable (fun value =>
      expectedSecondMoverShared (PMF.pure center) value) D)
    (hstrict_order : ∀ᵐ value ∂D, StrictlyOrderedBy center value)
    (hpointwise_prefers_independent : ∀ᵐ value ∂D,
      Model.PrefersIndependentReranking (F.dist thetaH value) value) :
    F.theorem1_g_pureCenterLimit D thetaH center <
      theorem1_f_pureCenterLimit D center := by
  have hpoint_gap : ∀ᵐ value ∂D,
      expectedFirstMoverUtility (F.dist thetaH value) value +
          expectedSecondMoverIndependent (F.dist thetaH value) (PMF.pure center) value <
        expectedFirstMoverUtility (PMF.pure center) value +
          expectedSecondMoverShared (PMF.pure center) value := by
    filter_upwards [hstrict_order, hpointwise_prefers_independent] with value
      hvalue hpref
    exact
      AccuracyFamily.expected_human_against_pureCenter_lt_pureCenter_payoff_of_prefersIndependent
        (F.dist thetaH value) center value hvalue hpref
  unfold theorem1_g_pureCenterLimit theorem1_f_pureCenterLimit outerExpected
  rw [← integral_add hgfirst hgsecond, ← integral_add hffirst hfsecond]
  exact integral_lt_integral_of_ae_lt_of_probability D
    (hgfirst.add hgsecond) (hffirst.add hfsecond) hpoint_gap

/-- Full outer-law Theorem 1 lift.  Its concentration premise is atomwise but
the conclusion uses a single `thetaA` after integration over `D`; continuity,
the two source preference premises, and the remaining dominance comparison are
kept as explicit semantic obligations. -/
theorem distributional_theorem1_of_outer_atomwise_regular
    {n : ℕ} (F : DistributionalAccuracyFamily n)
    (D : Measure (ValueProfile n)) (thetaH : ℝ) (center : Ranking n)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D)
    (hatom_measurable : ∀ theta pi,
      AEStronglyMeasurable (fun value : ValueProfile n =>
        ((F.dist theta value) pi).toReal) D)
    (hatom_continuous : ∀ value pi theta,
      EpsilonContinuousAt (fun theta' => ((F.dist theta' value) pi).toReal) theta)
    (hatom_tendsto : ∀ᵐ value ∂D, ∀ pi,
      Tendsto (fun theta => ((F.dist theta value) pi).toReal) atTop
        (𝓝 (((PMF.pure center : PMF (Ranking n)) pi).toReal)))
    (hprefers_independent : F.PrefersIndependentReranking D thetaH)
    (hpure_gap : F.theorem1_g_pureCenterLimit D thetaH center <
      theorem1_f_pureCenterLimit D center)
    (hprefers_weaker : ∀ thetaA, thetaH < thetaA →
      F.PrefersWeakerCompetition D thetaA thetaH)
    (halgorithm_against_human : ∀ thetaA, thetaH < thetaA →
      F.theorem1_h D thetaA thetaH <
        F.theorem1_algorithmAgainstHuman D thetaA thetaH) :
    F.DistributionalTheorem1Target D thetaH := by
  apply distributional_theorem1 F D thetaH
  refine {
    prefers_independent_at_equal := hprefers_independent
    f_continuity := ?_
    g_continuity := ?_
    asymptotic_first_dominance := ?_
    prefers_weaker_above := hprefers_weaker
    algorithm_against_human_above := halgorithm_against_human
  }
  · intro theta _
    exact epsilonContinuousAt_theorem1_f_of_atomwise F D thetaH theta hvalue
      hatom_measurable (fun value pi => hatom_continuous value pi theta)
  · intro theta _
    exact epsilonContinuousAt_theorem1_g_of_atomwise F D thetaH theta hvalue
      hatom_measurable (fun value pi => hatom_continuous value pi theta)
  · exact exists_outer_first_dominance_of_atomwise_tendsto
      F D thetaH center hvalue hatom_measurable hatom_tendsto hpure_gap

end DistributionalAccuracyFamily
end KR21Monoculture
