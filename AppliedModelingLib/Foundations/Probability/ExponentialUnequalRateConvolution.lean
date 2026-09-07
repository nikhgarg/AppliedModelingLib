import AppliedModelingLib.Foundations.Probability.ExponentialReflectedDifference
import Mathlib.Tactic

/-!
# Unequal-rate exponential convolution mixture

This module proves a density-level identity for two positive exponential
rates.  Splitting an independent `Exp(theta) x Exp(lambda)` pair according to
which coordinate is smaller identifies the original `Exp(theta)` coordinate
as a mixture of a fresh `Exp(theta + lambda)` clock and that clock preceded by
an independent `Exp(theta)` residual.  The result is measure-theoretic and
does not use a queueing model.
-/

namespace AppliedModelingLib.Probability

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal MeasureTheory

noncomputable section

/-- On the branch where the second clock is at least the first, retain the
first clock and record the nonnegative excess of the second. -/
def exponentialDifferenceComplementUnshear : (ℝ × ℝ) → ℝ × ℝ :=
  fun p => (p.1, p.2 - p.1)

theorem measurable_exponentialDifferenceComplementUnshear :
    Measurable exponentialDifferenceComplementUnshear := by
  exact measurable_fst.prodMk (measurable_snd.sub measurable_fst)

/-- The complementary shear preserves planar Lebesgue measure. -/
theorem exponentialDifferenceComplementUnshear_measurePreserving :
    MeasurePreserving exponentialDifferenceComplementUnshear
      (volume.prod volume) (volume.prod volume) := by
  simpa [exponentialDifferenceComplementUnshear] using
    (measurePreserving_prod_sub (volume : Measure ℝ) (volume : Measure ℝ))

/-- The complement branch has the factorized density of an
`Exp(theta + lambda)` clock and an independent `Exp(lambda)` excess. -/
def exponentialDifferenceComplementOutputDensity
    (theta lambda : ℝ) : (ℝ × ℝ) → ℝ≥0∞ :=
  fun p => ENNReal.ofReal (theta / (theta + lambda)) *
    exponentialPairDensity (theta + lambda) lambda p

theorem measurable_exponentialDifferenceComplementOutputDensity
    (theta lambda : ℝ) :
    Measurable (exponentialDifferenceComplementOutputDensity theta lambda) := by
  exact measurable_const.mul (measurable_exponentialPairDensity _ _)

private theorem exponentialDifferenceComplement_density_eq_output_comp_unshear
    {theta lambda : ℝ}
    (htheta : 0 < theta) (hlambda : 0 < lambda)
    (p : ℝ × ℝ) :
    exponentialDifferencePositiveCarrierᶜ.indicator
      (exponentialPairDensity theta lambda) p =
      exponentialDifferenceComplementOutputDensity theta lambda
        (exponentialDifferenceComplementUnshear p) := by
  rcases p with ⟨x, a⟩
  simp only [exponentialDifferenceComplementOutputDensity,
    exponentialDifferenceComplementUnshear, exponentialPairDensity]
  by_cases hcarrier : (x, a) ∈ exponentialDifferencePositiveCarrierᶜ
  · rw [Set.indicator_of_mem hcarrier]
    change ¬ a < x at hcarrier
    have hxa : x ≤ a := le_of_not_gt hcarrier
    by_cases hx : 0 ≤ x
    · have ha : 0 ≤ a := hx.trans hxa
      have hexcess : 0 ≤ a - x := sub_nonneg.mpr hxa
      change exponentialPDF theta x * exponentialPDF lambda a =
        ENNReal.ofReal (theta / (theta + lambda)) *
          (exponentialPDF (theta + lambda) x * exponentialPDF lambda (a - x))
      rw [exponentialPDF_of_nonneg hx, exponentialPDF_of_nonneg ha,
        exponentialPDF_of_nonneg hx, exponentialPDF_of_nonneg hexcess]
      have hsum_pos : 0 < theta + lambda := add_pos htheta hlambda
      have hratio_nonneg : 0 ≤ theta / (theta + lambda) :=
        div_nonneg htheta.le hsum_pos.le
      have hreal :
          theta * Real.exp (-(theta * x)) *
              (lambda * Real.exp (-(lambda * a))) =
            (theta / (theta + lambda)) *
              ((theta + lambda) * Real.exp (-((theta + lambda) * x)) *
                (lambda * Real.exp (-(lambda * (a - x))))) := by
        calc
          theta * Real.exp (-(theta * x)) *
              (lambda * Real.exp (-(lambda * a))) =
              theta * lambda * Real.exp (-(theta * x) + -(lambda * a)) := by
                rw [Real.exp_add]
                ring
          _ = theta * lambda * Real.exp
              (-((theta + lambda) * x) + -(lambda * (a - x))) := by
                congr 2
                ring
          _ = (theta / (theta + lambda)) *
              ((theta + lambda) * Real.exp (-((theta + lambda) * x)) *
                (lambda * Real.exp (-(lambda * (a - x))))) := by
                rw [Real.exp_add]
                field_simp [ne_of_gt hsum_pos]
      have hfirst_nonneg :
          0 ≤ theta * Real.exp (-(theta * x)) := by positivity
      have hsecond_nonneg :
          0 ≤ (theta + lambda) * Real.exp (-((theta + lambda) * x)) := by
        positivity
      rw [← ENNReal.ofReal_mul hfirst_nonneg,
        ← ENNReal.ofReal_mul hsecond_nonneg,
        ← ENNReal.ofReal_mul hratio_nonneg]
      exact congrArg ENNReal.ofReal hreal
    · have hxneg : x < 0 := lt_of_not_ge hx
      change exponentialPDF theta x * exponentialPDF lambda a =
        ENNReal.ofReal (theta / (theta + lambda)) *
          (exponentialPDF (theta + lambda) x * exponentialPDF lambda (a - x))
      rw [exponentialPDF_of_neg hxneg, exponentialPDF_of_neg hxneg]
      simp
  · rw [Set.indicator_of_notMem hcarrier]
    change ¬ (¬ a < x) at hcarrier
    have hax : a < x := not_not.mp hcarrier
    have hexcess_neg : a - x < 0 := by linarith
    change 0 = ENNReal.ofReal (theta / (theta + lambda)) *
      (exponentialPDF (theta + lambda) x * exponentialPDF lambda (a - x))
    rw [exponentialPDF_of_neg hexcess_neg]
    simp

/-- The density calculation for the complementary branch, before projecting
away its independent excess coordinate. -/
theorem map_exponentialDifferenceComplementUnshear_expMeasure_prod_restrict_compl
    {theta lambda : ℝ} (htheta : 0 < theta) (hlambda : 0 < lambda) :
    Measure.map exponentialDifferenceComplementUnshear
      (((expMeasure theta).prod (expMeasure lambda)).restrict
        exponentialDifferencePositiveCarrierᶜ) =
      ENNReal.ofReal (theta / (theta + lambda)) •
        ((expMeasure (theta + lambda)).prod (expMeasure lambda)) := by
  have hdensity :
      exponentialDifferencePositiveCarrierᶜ.indicator
        (exponentialPairDensity theta lambda) =ᵐ[volume.prod volume]
        exponentialDifferenceComplementOutputDensity theta lambda ∘
          exponentialDifferenceComplementUnshear := by
    exact Filter.Eventually.of_forall
      (fun p => exponentialDifferenceComplement_density_eq_output_comp_unshear
        htheta hlambda p)
  calc
    Measure.map exponentialDifferenceComplementUnshear
        (((expMeasure theta).prod (expMeasure lambda)).restrict
          exponentialDifferencePositiveCarrierᶜ) =
        Measure.map exponentialDifferenceComplementUnshear
          ((volume.prod volume).withDensity
            (exponentialDifferencePositiveCarrierᶜ.indicator
              (exponentialPairDensity theta lambda))) := by
          rw [expMeasure_prod_eq_withDensity_exponentialPair,
            MeasureTheory.restrict_withDensity
              measurableSet_exponentialDifferencePositiveCarrier.compl,
            ← MeasureTheory.withDensity_indicator
              measurableSet_exponentialDifferencePositiveCarrier.compl]
    _ = Measure.map exponentialDifferenceComplementUnshear
          ((volume.prod volume).withDensity
            (exponentialDifferenceComplementOutputDensity theta lambda ∘
              exponentialDifferenceComplementUnshear)) := by
          congr 1
          exact MeasureTheory.withDensity_congr_ae hdensity
    _ = (volume.prod volume).withDensity
          (exponentialDifferenceComplementOutputDensity theta lambda) :=
      AppliedModelingLib.Probability.PoissonProcess.map_withDensity_comp_of_measurePreserving
        exponentialDifferenceComplementUnshear_measurePreserving
        (exponentialDifferenceComplementOutputDensity theta lambda)
        (measurable_exponentialDifferenceComplementOutputDensity _ _)
    _ = ENNReal.ofReal (theta / (theta + lambda)) •
          ((expMeasure (theta + lambda)).prod (expMeasure lambda)) := by
      rw [expMeasure_prod_eq_withDensity_exponentialPair,
        ← MeasureTheory.withDensity_smul
          (ENNReal.ofReal (theta / (theta + lambda)))
          (measurable_exponentialPairDensity _ _)]
      rfl

/-- Projecting the branch where the second clock is first gives the
convolution component of the unequal-rate mixture. -/
theorem map_fst_expMeasure_prod_restrict_positive_eq_weighted_conv
    {theta lambda : ℝ} (htheta : 0 < theta) (hlambda : 0 < lambda) :
    Measure.map Prod.fst
      (((expMeasure theta).prod (expMeasure lambda)).restrict
        exponentialDifferencePositiveCarrier) =
      ENNReal.ofReal (lambda / (theta + lambda)) •
        (expMeasure theta ∗ expMeasure (theta + lambda)) := by
  letI : IsProbabilityMeasure (expMeasure theta) :=
    isProbabilityMeasure_expMeasure htheta
  letI : IsProbabilityMeasure (expMeasure lambda) :=
    isProbabilityMeasure_expMeasure hlambda
  letI : IsProbabilityMeasure (expMeasure (theta + lambda)) :=
    isProbabilityMeasure_expMeasure (add_pos htheta hlambda)
  let μ : Measure (ℝ × ℝ) :=
    ((expMeasure theta).prod (expMeasure lambda)).restrict
      exponentialDifferencePositiveCarrier
  calc
    Measure.map Prod.fst μ =
        Measure.map ((fun q : ℝ × ℝ => q.1 + q.2) ∘
          exponentialDifferenceUnshear) μ := by
          congr 1
          funext p
          rcases p with ⟨x, a⟩
          simp [exponentialDifferenceUnshear]
    _ = Measure.map (fun q : ℝ × ℝ => q.1 + q.2)
          (Measure.map exponentialDifferenceUnshear μ) := by
          exact (Measure.map_map
            (measurable_fst.add measurable_snd)
            measurable_exponentialDifferenceUnshear).symm
    _ = Measure.map (fun q : ℝ × ℝ => q.1 + q.2)
          (ENNReal.ofReal (lambda / (theta + lambda)) •
            ((expMeasure theta).prod (expMeasure (theta + lambda)))) := by
          rw [show μ =
              ((expMeasure theta).prod (expMeasure lambda)).restrict
                exponentialDifferencePositiveCarrier by rfl]
          rw [map_exponentialDifferenceUnshear_expMeasure_prod_restrict_positive
            htheta hlambda]
    _ = ENNReal.ofReal (lambda / (theta + lambda)) •
          (expMeasure theta ∗ expMeasure (theta + lambda)) := by
          rw [Measure.map_smul]
          rfl

/-- Projecting the branch where the first clock is first gives the fresh
short-clock component of the unequal-rate mixture. -/
theorem map_fst_expMeasure_prod_restrict_compl_eq_weighted_expMeasure
    {theta lambda : ℝ} (htheta : 0 < theta) (hlambda : 0 < lambda) :
    Measure.map Prod.fst
      (((expMeasure theta).prod (expMeasure lambda)).restrict
        exponentialDifferencePositiveCarrierᶜ) =
      ENNReal.ofReal (theta / (theta + lambda)) •
        expMeasure (theta + lambda) := by
  letI : IsProbabilityMeasure (expMeasure theta) :=
    isProbabilityMeasure_expMeasure htheta
  letI : IsProbabilityMeasure (expMeasure lambda) :=
    isProbabilityMeasure_expMeasure hlambda
  letI : IsProbabilityMeasure (expMeasure (theta + lambda)) :=
    isProbabilityMeasure_expMeasure (add_pos htheta hlambda)
  let μ : Measure (ℝ × ℝ) :=
    ((expMeasure theta).prod (expMeasure lambda)).restrict
      exponentialDifferencePositiveCarrierᶜ
  calc
    Measure.map Prod.fst μ =
        Measure.map (Prod.fst ∘ exponentialDifferenceComplementUnshear) μ := by
          rfl
    _ = Measure.map Prod.fst
          (Measure.map exponentialDifferenceComplementUnshear μ) := by
          exact (Measure.map_map measurable_fst
            measurable_exponentialDifferenceComplementUnshear).symm
    _ = Measure.map Prod.fst
          (ENNReal.ofReal (theta / (theta + lambda)) •
            ((expMeasure (theta + lambda)).prod (expMeasure lambda))) := by
          rw [show μ =
              ((expMeasure theta).prod (expMeasure lambda)).restrict
                exponentialDifferencePositiveCarrierᶜ by rfl]
          rw [map_exponentialDifferenceComplementUnshear_expMeasure_prod_restrict_compl
            htheta hlambda]
    _ = ENNReal.ofReal (theta / (theta + lambda)) •
          expMeasure (theta + lambda) := by
          rw [Measure.map_smul, Measure.map_fst_prod, measure_univ, one_smul]

/-- Exact unequal-rate exponential mixture identity.  This is the law-level
calculation needed to combine a reflected exponential prework branch with an
independent rate-`theta + lambda` service time. -/
theorem weighted_expMeasure_unequalRate_conv_eq_expMeasure
    {theta lambda : ℝ} (htheta : 0 < theta) (hlambda : 0 < lambda) :
    ENNReal.ofReal (theta / (theta + lambda)) • expMeasure (theta + lambda) +
      ENNReal.ofReal (lambda / (theta + lambda)) •
        (expMeasure theta ∗ expMeasure (theta + lambda)) =
      expMeasure theta := by
  letI : IsProbabilityMeasure (expMeasure theta) :=
    isProbabilityMeasure_expMeasure htheta
  letI : IsProbabilityMeasure (expMeasure lambda) :=
    isProbabilityMeasure_expMeasure hlambda
  letI : IsProbabilityMeasure (expMeasure (theta + lambda)) :=
    isProbabilityMeasure_expMeasure (add_pos htheta hlambda)
  let pair : Measure (ℝ × ℝ) :=
    (expMeasure theta).prod (expMeasure lambda)
  calc
    ENNReal.ofReal (theta / (theta + lambda)) • expMeasure (theta + lambda) +
        ENNReal.ofReal (lambda / (theta + lambda)) •
          (expMeasure theta ∗ expMeasure (theta + lambda)) =
        Measure.map Prod.fst (pair.restrict exponentialDifferencePositiveCarrierᶜ) +
          Measure.map Prod.fst (pair.restrict exponentialDifferencePositiveCarrier) := by
            rw [show pair = (expMeasure theta).prod (expMeasure lambda) by rfl,
              map_fst_expMeasure_prod_restrict_compl_eq_weighted_expMeasure htheta hlambda,
              map_fst_expMeasure_prod_restrict_positive_eq_weighted_conv htheta hlambda]
    _ = Measure.map Prod.fst
          (pair.restrict exponentialDifferencePositiveCarrier +
            pair.restrict exponentialDifferencePositiveCarrierᶜ) := by
          rw [Measure.map_add _ _ measurable_fst]
          exact add_comm _ _
    _ = Measure.map Prod.fst pair := by
          rw [Measure.restrict_add_restrict_compl
            measurableSet_exponentialDifferencePositiveCarrier]
    _ = expMeasure theta := by
          rw [show pair = (expMeasure theta).prod (expMeasure lambda) by rfl,
            Measure.map_fst_prod, measure_univ, one_smul]

end

end AppliedModelingLib.Probability
