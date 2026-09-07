import AppliedModelingLib.Foundations.Probability.FinitePinsker
import AppliedModelingLib.Foundations.Probability.FiniteKLDataProcessing
import AppliedModelingLib.Privacy.Finite

/-!
# Finite KL stability

The finite version of Kullback--Leibler stability used in adaptive data
analysis.  The public conversion to total variation is Pinsker's inequality
under absolute continuity, so laws may have zero-probability atoms outside
their common support.
-/

namespace AppliedModelingLib.Privacy

section Closeness

variable {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]

/-- One directed finite KL bound, with the absolute-continuity condition that
makes the real finite-sum expression a genuine divergence. -/
def KLClose (epsilon : ℝ) (first second : PMF Outcome) : Prop :=
  PMFAbsoluteContinuous first second ∧
    finiteKLDivergence first second ≤ 2 * epsilon ^ 2

/-- Pinsker converts the paper's `2 ε²` KL convention to its `ε`
total-variation convention. -/
theorem KLClose.toTVClose {epsilon : ℝ} {first second : PMF Outcome}
    (hepsilon : 0 ≤ epsilon) (h : KLClose epsilon first second) :
    TVClose epsilon first second := by
  apply TVClose.of_half_l1_le
  have hpinsker :=
    finitePinsker_l1_sq_le_finiteKLDivergence_of_absoluteContinuous first second h.1
  have hl1_nonneg : 0 ≤
      FiniteDimensionalNorms.l1
        (fun outcome => (first outcome).toReal - (second outcome).toReal) := by
    unfold FiniteDimensionalNorms.l1
    exact Finset.sum_nonneg fun outcome _ => abs_nonneg _
  nlinarith [h.2]

/-- Arbitrary finite randomized post-processing preserves the KL-stability
parameter. -/
theorem KLClose.bind {Input Output : Type*}
    [Fintype Input] [DecidableEq Input] [Fintype Output] [DecidableEq Output]
    {epsilon : ℝ} {first second : PMF Input}
    (h : KLClose epsilon first second) (kernel : Input → PMF Output) :
    KLClose epsilon (first.bind kernel) (second.bind kernel) :=
  ⟨h.1.bind kernel, (finiteKLDivergence_bind_le first second h.1 kernel).trans h.2⟩

/-- The singleton-event consequence of finite pure max-KL closeness. -/
theorem MaxKLClose.pointwise
    {epsilon : ℝ} {first second : PMF Outcome}
    (h : MaxKLClose epsilon 0 first second) (outcome : Outcome) :
    (first outcome).toReal ≤ Real.exp epsilon * (second outcome).toReal := by
  simpa only [eventProbability, Finset.mem_singleton, pmfProb_singleton, add_zero] using
    h.1 ({outcome} : Finset Outcome)

/-- The finite log-likelihood ratio, defined also at zero-mass atoms.  Under
pure max-KL closeness the two laws have common support, so its values on
positive-probability atoms are the ordinary privacy losses. -/
noncomputable def logLikelihoodRatio (first second : PMF Outcome) : Outcome → ℝ :=
  fun outcome => Real.log (first outcome).toReal - Real.log (second outcome).toReal

/-- Pure two-sided max-KL closeness bounds every finite privacy-loss value. -/
theorem MaxKLClose.logLikelihoodRatio_abs_le
    {epsilon : ℝ} {first second : PMF Outcome}
    (h : MaxKLClose epsilon 0 first second) (hepsilon : 0 ≤ epsilon) :
    ∀ outcome, |logLikelihoodRatio first second outcome| ≤ epsilon := by
  intro outcome
  have hforward : (first outcome).toReal ≤ Real.exp epsilon * (second outcome).toReal :=
    h.pointwise outcome
  have hreverse : (second outcome).toReal ≤ Real.exp epsilon * (first outcome).toReal :=
    h.symm.pointwise outcome
  by_cases hfirstZero : (first outcome).toReal = 0
  · have hsecondZero : (second outcome).toReal = 0 := by
      rw [hfirstZero] at hreverse
      simp only [mul_zero] at hreverse
      exact le_antisymm hreverse ENNReal.toReal_nonneg
    simp [logLikelihoodRatio, hfirstZero, hsecondZero, hepsilon]
  · have hfirstPos : 0 < (first outcome).toReal :=
      lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hfirstZero)
    have hsecondPos : 0 < (second outcome).toReal := by
      by_contra hsecondPos
      have hsecondZero : (second outcome).toReal = 0 :=
        le_antisymm (le_of_not_gt hsecondPos) ENNReal.toReal_nonneg
      rw [hsecondZero] at hforward
      simp only [mul_zero] at hforward
      exact (not_lt_of_ge hforward) hfirstPos
    have hforwardRatio : (first outcome).toReal / (second outcome).toReal ≤
        Real.exp epsilon :=
      (div_le_iff₀ hsecondPos).2 hforward
    have hreverseRatio : (second outcome).toReal / (first outcome).toReal ≤
        Real.exp epsilon :=
      (div_le_iff₀ hfirstPos).2 hreverse
    have hupper : logLikelihoodRatio first second outcome ≤ epsilon := by
      unfold logLikelihoodRatio
      rw [← Real.log_div hfirstPos.ne' hsecondPos.ne']
      exact (Real.log_le_iff_le_exp (div_pos hfirstPos hsecondPos)).2 hforwardRatio
    have hlower : -epsilon ≤ logLikelihoodRatio first second outcome := by
      have hlog : Real.log ((second outcome).toReal / (first outcome).toReal) ≤ epsilon :=
        (Real.log_le_iff_le_exp (div_pos hsecondPos hfirstPos)).2 hreverseRatio
      rw [Real.log_div hsecondPos.ne' hfirstPos.ne'] at hlog
      unfold logLikelihoodRatio
      linarith
    exact abs_le.mpr ⟨hlower, hupper⟩

/--
Pure max-KL closeness gives the source paper's KL-stability parameter in the
unit privacy regime.  The proof is the finite likelihood-ratio argument:
the two event inequalities give a bounded privacy loss, and the exponential
remainder cancels because the two laws have common support and total mass one.
-/
theorem MaxKLClose.toKLClose
    {epsilon : ℝ} {first second : PMF Outcome}
    (h : MaxKLClose epsilon 0 first second)
    (hepsilonNonneg : 0 ≤ epsilon) (hepsilonOne : epsilon ≤ 1) :
    KLClose epsilon first second := by
  let loss : Outcome → ℝ := fun outcome =>
    Real.log (first outcome).toReal - Real.log (second outcome).toReal
  have hforward : ∀ outcome : Outcome,
      (first outcome).toReal ≤ Real.exp epsilon * (second outcome).toReal :=
    fun outcome => h.pointwise outcome
  have hreverse : ∀ outcome : Outcome,
      (second outcome).toReal ≤ Real.exp epsilon * (first outcome).toReal :=
    fun outcome => h.symm.pointwise outcome
  have hcontinuous : PMFAbsoluteContinuous first second := by
    intro outcome hfirstPos
    by_contra hsecondPos
    have hsecondZero : (second outcome).toReal = 0 :=
      le_antisymm (le_of_not_gt hsecondPos) ENNReal.toReal_nonneg
    have hbound := hforward outcome
    rw [hsecondZero] at hbound
    simp only [mul_zero] at hbound
    exact (not_lt_of_ge hbound) hfirstPos
  refine ⟨hcontinuous, ?_⟩
  have hlossBound : ∀ outcome : Outcome, |loss outcome| ≤ epsilon := by
    intro outcome
    by_cases hfirstZero : (first outcome).toReal = 0
    · have hsecondZero : (second outcome).toReal = 0 := by
        have hbound := hreverse outcome
        rw [hfirstZero] at hbound
        simp only [mul_zero] at hbound
        exact le_antisymm hbound ENNReal.toReal_nonneg
      simp [loss, hfirstZero, hsecondZero, hepsilonNonneg]
    · have hfirstPos : 0 < (first outcome).toReal :=
        lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hfirstZero)
      have hsecondPos : 0 < (second outcome).toReal := hcontinuous outcome hfirstPos
      have hforwardRatio : (first outcome).toReal / (second outcome).toReal ≤
          Real.exp epsilon :=
        (div_le_iff₀ hsecondPos).2 (hforward outcome)
      have hreverseRatio : (second outcome).toReal / (first outcome).toReal ≤
          Real.exp epsilon :=
        (div_le_iff₀ hfirstPos).2 (hreverse outcome)
      have hupper : loss outcome ≤ epsilon := by
        change Real.log (first outcome).toReal - Real.log (second outcome).toReal ≤ epsilon
        rw [← Real.log_div hfirstPos.ne' hsecondPos.ne']
        exact (Real.log_le_iff_le_exp (div_pos hfirstPos hsecondPos)).2 hforwardRatio
      have hlower : -epsilon ≤ loss outcome := by
        have hlog : Real.log ((second outcome).toReal / (first outcome).toReal) ≤ epsilon :=
          (Real.log_le_iff_le_exp (div_pos hsecondPos hfirstPos)).2 hreverseRatio
        rw [Real.log_div hsecondPos.ne' hfirstPos.ne'] at hlog
        dsimp [loss]
        linarith
      exact abs_le.mpr ⟨hlower, hupper⟩
  have hmassExp : ∀ outcome : Outcome,
      (first outcome).toReal * Real.exp (-loss outcome) = (second outcome).toReal := by
    intro outcome
    by_cases hfirstZero : (first outcome).toReal = 0
    · have hsecondZero : (second outcome).toReal = 0 := by
        have hbound := hreverse outcome
        rw [hfirstZero] at hbound
        simp only [mul_zero] at hbound
        exact le_antisymm hbound ENNReal.toReal_nonneg
      simp [hfirstZero, hsecondZero]
    · have hfirstPos : 0 < (first outcome).toReal :=
        lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hfirstZero)
      have hsecondPos : 0 < (second outcome).toReal := hcontinuous outcome hfirstPos
      dsimp [loss]
      rw [neg_sub, Real.exp_sub, Real.exp_log hsecondPos, Real.exp_log hfirstPos]
      field_simp [hfirstPos.ne']
  have hpointwise : ∀ outcome : Outcome,
      (first outcome).toReal * loss outcome ≤
        (first outcome).toReal * (1 - Real.exp (-loss outcome) + loss outcome ^ 2) := by
    intro outcome
    have hremainder : loss outcome ≤
        1 - Real.exp (-loss outcome) + loss outcome ^ 2 := by
      have habsOne : |loss outcome| ≤ 1 := (hlossBound outcome).trans hepsilonOne
      have hrem := Real.abs_exp_sub_one_sub_id_le (x := -loss outcome) (by
        simpa using habsOne)
      have hupper : Real.exp (-loss outcome) - 1 - (-loss outcome) ≤
          (-loss outcome) ^ 2 :=
        (le_abs_self _).trans hrem
      nlinarith
    exact mul_le_mul_of_nonneg_left hremainder ENNReal.toReal_nonneg
  have hsquare : ∀ outcome : Outcome,
      (first outcome).toReal * loss outcome ^ 2 ≤
        (first outcome).toReal * epsilon ^ 2 := by
    intro outcome
    apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
    exact sq_le_sq.mpr (by simpa [abs_of_nonneg hepsilonNonneg] using hlossBound outcome)
  have hsumExp : ∑ outcome : Outcome,
      (first outcome).toReal * Real.exp (-loss outcome) = 1 := by
    calc
      (∑ outcome : Outcome,
          (first outcome).toReal * Real.exp (-loss outcome)) =
          ∑ outcome : Outcome, (second outcome).toReal := by
            exact Finset.sum_congr rfl fun outcome _ => hmassExp outcome
      _ = 1 := pmfToRealSum second
  unfold finiteKLDivergence
  change (∑ outcome : Outcome, (first outcome).toReal * loss outcome) ≤ 2 * epsilon ^ 2
  calc
    (∑ outcome : Outcome, (first outcome).toReal * loss outcome) ≤
        ∑ outcome : Outcome,
          (first outcome).toReal * (1 - Real.exp (-loss outcome) + loss outcome ^ 2) :=
      Finset.sum_le_sum fun outcome _ => hpointwise outcome
    _ = ∑ outcome : Outcome, (first outcome).toReal * loss outcome ^ 2 := by
      rw [show (∑ outcome : Outcome,
          (first outcome).toReal * (1 - Real.exp (-loss outcome) + loss outcome ^ 2)) =
          (∑ outcome : Outcome, (first outcome).toReal) -
            (∑ outcome : Outcome,
              (first outcome).toReal * Real.exp (-loss outcome)) +
            ∑ outcome : Outcome, (first outcome).toReal * loss outcome ^ 2 by
        calc
          (∑ outcome : Outcome,
              (first outcome).toReal *
                (1 - Real.exp (-loss outcome) + loss outcome ^ 2)) =
              ∑ outcome : Outcome,
                ((first outcome).toReal -
                  (first outcome).toReal * Real.exp (-loss outcome) +
                  (first outcome).toReal * loss outcome ^ 2) := by
                apply Finset.sum_congr rfl
                intro outcome _
                ring
          _ = (∑ outcome : Outcome, (first outcome).toReal) -
                (∑ outcome : Outcome,
                  (first outcome).toReal * Real.exp (-loss outcome)) +
                ∑ outcome : Outcome, (first outcome).toReal * loss outcome ^ 2 := by
                rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]]
      rw [pmfToRealSum first, hsumExp]
      ring
    _ ≤ ∑ outcome : Outcome, (first outcome).toReal * epsilon ^ 2 :=
      Finset.sum_le_sum fun outcome _ => hsquare outcome
    _ = epsilon ^ 2 := by
      rw [← Finset.sum_mul, pmfToRealSum first]
      ring
    _ ≤ 2 * epsilon ^ 2 := by nlinarith [sq_nonneg epsilon]

end Closeness

section Stability

variable {Dataset Output : Type*} [Fintype Output] [DecidableEq Output]

/-- An algorithm is KL-stable if every directed adjacent output pair satisfies
the source paper's finite KL bound. -/
def KLStable (adjacent : Dataset → Dataset → Prop)
    (algorithm : Dataset → PMF Output) (epsilon : ℝ) : Prop :=
  ∀ ⦃first second : Dataset⦄, adjacent first second →
    KLClose epsilon (algorithm first) (algorithm second)

/-- KL stability implies total-variation stability with the same parameter. -/
theorem KLStable.toTVStable
    {adjacent : Dataset → Dataset → Prop} {algorithm : Dataset → PMF Output}
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (h : KLStable adjacent algorithm epsilon) :
    TVStable adjacent algorithm epsilon := by
  intro first second hadjacent
  exact (h hadjacent).toTVClose hepsilon

/-- Arbitrary finite randomized post-processing preserves KL stability. -/
theorem KLStable.bind {PostOutput : Type*}
    [Fintype PostOutput] [DecidableEq PostOutput]
    {adjacent : Dataset → Dataset → Prop}
    {algorithm : Dataset → PMF Output} {epsilon : ℝ}
    (h : KLStable adjacent algorithm epsilon)
    (kernel : Output → PMF PostOutput) :
    KLStable adjacent (fun dataset => (algorithm dataset).bind kernel) epsilon := by
  intro first second hadjacent
  exact (h hadjacent).bind kernel

end Stability

end AppliedModelingLib.Privacy
