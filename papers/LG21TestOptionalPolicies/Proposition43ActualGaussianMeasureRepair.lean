import LG21TestOptionalPolicies.MainTheorems

/-!
# Proposition 4.3: Actual Gaussian Measure Repair

The previous Proposition 4.3 route represented posterior-output laws by a
tagged `LG21GaussianMixtureLaw`.  This module instead uses the concrete
mathlib Gaussian measures carried by `GaussianScaleLaw.toMeasure`.

The repair keeps the paper's two comparisons separate.  Observable fairness
is conditional on the realized non-test signal vector, where no-access PBO is
a point mass and access PBO is a conditional Gaussian output.  Demographic
fairness compares the two marginal posterior-output measures induced by one
finite Gaussian signal family.  The finite family `M` contains every base
signal; `M.withExtraSignal` adds the observed test as the `none` coordinate of
one larger finite Gaussian signal family.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib
open AppliedModelingLib.Probability
open MeasureTheory
open ProbabilityTheory

/--
Concrete Gaussian laws with strictly different positive scales are different
actual measures.  The proof uses Gaussian-measure identifiability, so it does
not rely on a tagged-law constructor being injective.
-/
theorem lg21_gaussianScaleLaw_toMeasure_ne_of_scale_lt
    {Llow Lhigh : GaussianScaleLaw}
    (hscale : Llow.scale < Lhigh.scale) :
    Llow.toMeasure ≠ Lhigh.toMeasure := by
  intro hmeasure
  have hparams :
      Llow.mean = Lhigh.mean ∧
        Llow.varianceNNReal = Lhigh.varianceNNReal :=
    ProbabilityTheory.gaussianReal_ext_iff.mp hmeasure
  have hsq : Llow.scale ^ 2 = Lhigh.scale ^ 2 := by
    have hcoe : (Llow.varianceNNReal : ℝ) =
        (Lhigh.varianceNNReal : ℝ) :=
      congrArg NNReal.toReal hparams.2
    change Llow.scale ^ 2 = Lhigh.scale ^ 2 at hcoe
    exact hcoe
  have hsq_lt : Llow.scale ^ 2 < Lhigh.scale ^ 2 :=
    (sq_lt_sq₀ Llow.scale_pos.le Lhigh.scale_pos.le).2 hscale
  exact (ne_of_lt hsq_lt) hsq

/-- A nondegenerate Gaussian output measure cannot equal any point mass. -/
theorem lg21_gaussianScaleLaw_toMeasure_ne_dirac
    (L : GaussianScaleLaw) (x : ℝ) :
    L.toMeasure ≠ Measure.dirac x := by
  intro hmeasure
  have happly := congrArg (fun μ : Measure ℝ => μ ({x} : Set ℝ)) hmeasure
  change L.toMeasure ({x} : Set ℝ) = Measure.dirac x ({x} : Set ℝ) at happly
  rw [L.toMeasure_singleton_eq_zero x] at happly
  norm_num at happly

/--
After fixing the non-test signal vector, this is the one-signal Gaussian
prior-to-test update induced by the original finite signal family.  Its prior
is the posterior after the observed base signals, and its one signal is the
extra test.
-/
def lg21P43ConditionalExtraTestPrior
    {Feature : Type*} [Fintype Feature]
    (M : GaussianOffsetSignalFamily Feature) (base : Feature → ℝ)
    (extraNoiseVar : ℝ) (hextraNoiseVar : 0 < extraNoiseVar) :
    GaussianPriorSignal where
  priorMean := M.posteriorMean base
  priorVar := M.centeredFamily.posteriorVariance
  noiseVar := extraNoiseVar
  priorVar_pos := M.centeredFamily.posteriorVariance_pos
  noiseVar_pos := hextraNoiseVar

/--
The actual conditional raw-test law after observing the non-test signal
vector.  It is Gaussian with the base posterior mean and the sum of posterior
and test-noise variances.
-/
def lg21P43ConditionalExtraTestScoreLaw
    {Feature : Type*} [Fintype Feature]
    (M : GaussianOffsetSignalFamily Feature) (base : Feature → ℝ)
    (extraNoiseMean extraNoiseVar : ℝ) (hextraNoiseVar : 0 < extraNoiseVar) :
    GaussianScaleLaw where
  mean := M.posteriorMean base + extraNoiseMean
  scale := Real.sqrt (M.centeredFamily.posteriorVariance + extraNoiseVar)
  scale_pos :=
    Real.sqrt_pos.mpr
      (add_pos M.centeredFamily.posteriorVariance_pos hextraNoiseVar)

/--
The access-side PBO output law at fixed observed base features.  This is the
positive affine image of the actual conditional Gaussian test-score law, not
a tagged Gaussian object.
-/
def lg21P43ConditionalAccessOutputLaw
    {Feature : Type*} [Fintype Feature]
    (M : GaussianOffsetSignalFamily Feature) (base : Feature → ℝ)
    (extraNoiseMean extraNoiseVar : ℝ) (hextraNoiseVar : 0 < extraNoiseVar) :
    GaussianScaleLaw :=
  GaussianPriorSignal.posteriorMeanRawSignalScaleLaw
    (lg21P43ConditionalExtraTestPrior M base extraNoiseVar hextraNoiseVar)
    extraNoiseMean
    (lg21P43ConditionalExtraTestScoreLaw
      M base extraNoiseMean extraNoiseVar hextraNoiseVar)

/-- The conditional access-side PBO output remains centered at the base posterior mean. -/
theorem lg21P43ConditionalAccessOutputLaw_mean
    {Feature : Type*} [Fintype Feature]
    (M : GaussianOffsetSignalFamily Feature) (base : Feature → ℝ)
    (extraNoiseMean extraNoiseVar : ℝ) (hextraNoiseVar : 0 < extraNoiseVar) :
    (lg21P43ConditionalAccessOutputLaw
      M base extraNoiseMean extraNoiseVar hextraNoiseVar).mean =
      M.posteriorMean base := by
  exact
    GaussianPriorSignal.posteriorMeanRawSignalScaleLaw_mean_of_signal_mean_eq
      (lg21P43ConditionalExtraTestPrior M base extraNoiseVar hextraNoiseVar)
      (by rfl)

/--
Source-faithful observable-law inequality for Proposition 4.3.  Conditional
on all non-test observed features, no-access PBO is the deterministic base
posterior estimate while access PBO is the nondegenerate Gaussian output from
the additional test.  Their *actual measures* differ.
-/
theorem paper_proposition4_3_actual_measure_observable_law_ne_at_fixed_base
    {Feature : Type*} [Fintype Feature]
    (M : GaussianOffsetSignalFamily Feature) (base : Feature → ℝ)
    (extraNoiseMean extraNoiseVar : ℝ) (hextraNoiseVar : 0 < extraNoiseVar) :
    (lg21P43ConditionalAccessOutputLaw
      M base extraNoiseMean extraNoiseVar hextraNoiseVar).toMeasure ≠
      Measure.dirac (M.posteriorMean base) :=
  lg21_gaussianScaleLaw_toMeasure_ne_dirac
    (lg21P43ConditionalAccessOutputLaw
      M base extraNoiseMean extraNoiseVar hextraNoiseVar)
    (M.posteriorMean base)

/--
Source-shaped Proposition 4.3 measure obligations from one finite Gaussian
signal family.  The first conjunct is the genuine *conditional* observable
comparison at every fixed vector of non-test features.  The second is the
genuine *marginal* demographic comparison after integrating the Gaussian base
signals: `posteriorMeanScaleLaw` is the no-access output law and adding the
test creates the access output law.  The two arguments are intentionally
separate; a pointwise conditional inequality alone would not justify a
general mixture inequality.
-/
theorem paper_proposition4_3_actual_gaussian_measure_observable_and_demographic_gaps
    {Feature : Type*} [Fintype Feature] [Nonempty Feature]
    (M : GaussianOffsetSignalFamily Feature)
    (extraNoiseMean extraNoiseVar : ℝ) (hextraNoiseVar : 0 < extraNoiseVar) :
    (∀ base : Feature → ℝ,
      (lg21P43ConditionalAccessOutputLaw
        M base extraNoiseMean extraNoiseVar hextraNoiseVar).toMeasure ≠
        Measure.dirac (M.posteriorMean base)) ∧
      M.posteriorMeanScaleLaw.toMeasure ≠
        (GaussianOffsetSignalFamily.posteriorMeanScaleLaw
          (M.withExtraSignal extraNoiseMean extraNoiseVar hextraNoiseVar)).toMeasure := by
  refine ⟨?_, ?_⟩
  · intro base
    exact paper_proposition4_3_actual_measure_observable_law_ne_at_fixed_base
      M base extraNoiseMean extraNoiseVar hextraNoiseVar
  · exact lg21_gaussianScaleLaw_toMeasure_ne_of_scale_lt
      (paper_gaussian_estimate_scale_lt_of_extra_signal
        M extraNoiseMean extraNoiseVar hextraNoiseVar)

end

end LG21TestOptionalPolicies
