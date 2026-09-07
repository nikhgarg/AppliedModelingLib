import AppliedModelingLib.Queueing.MM1.TwoSided.MarkedFactor
import Mathlib.Tactic

/-!
# Two-sided marked M/M/1 path on the Poisson suspension

This module forms the concrete product of the good two-sided Poisson
suspension with the edge-mark factor of the reversible two-sided uniformized
M/M/1 trajectory.  It is the correctly typed input to
`timedEmbeddedSuspensionFlow`: both the clock and marked queue path are now
two-sided and share the same integer event labels.

The generic timing module already turns full integer-shift invariance of this
queue path into a stationary real-time skew-product law. The remaining open
step is therefore exactly that full discrete path-invariance theorem. No
thinning, Palm, or PASTA claim is made here.
-/

namespace AppliedModelingLib.Probability.Queueing

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

open PoissonProcess

/-- The actual two-sided marked path obtained by edge-marking the existing
reversible queue-length construction. -/
noncomputable def geoNNPMF_uniformized_twoSidedMarkedTrajMeasure
    (rho : ℝ≥0) (hrho : rho < 1) : Measure (ℤ → (ℕ × Bool)) :=
  (reversibleStateAnchoredTwoSidedTrajMeasure
    (geoNNPMF rho hrho).toMeasure
    (countablePMFKernel
      (reflectedBirthDeathKernel (uniformizedBirthProbability rho)
        (uniformizedBirthProbability_le_one rho)))).map edgeMarkedPath

/-- The actual edge-marked two-sided M/M/1 trajectory is a probability law. -/
theorem isProbabilityMeasure_geoNNPMF_uniformized_twoSidedMarkedTrajMeasure
    (rho : ℝ≥0) (hrho : rho < 1) :
    IsProbabilityMeasure (geoNNPMF_uniformized_twoSidedMarkedTrajMeasure rho hrho) := by
  let M : Measure (ℤ → ℕ) := reversibleStateAnchoredTwoSidedTrajMeasure
    (geoNNPMF rho hrho).toMeasure
    (countablePMFKernel
      (reflectedBirthDeathKernel (uniformizedBirthProbability rho)
        (uniformizedBirthProbability_le_one rho)))
  have hMprob : IsProbabilityMeasure M := by
    let S : Measure (ℕ × ((ℕ → ℕ) × (ℕ → ℕ))) :=
      stateAndIndependentTailsMeasure (geoNNPMF rho hrho).toMeasure
        (countablePMFKernel
          (reflectedBirthDeathKernel (uniformizedBirthProbability rho)
            (uniformizedBirthProbability_le_one rho)))
    have hSprob : IsProbabilityMeasure S := by
      dsimp [S, stateAndIndependentTailsMeasure]
      infer_instance
    letI : IsProbabilityMeasure S := hSprob
    change IsProbabilityMeasure (S.map spliceStateAndTails)
    exact Measure.isProbabilityMeasure_map measurable_spliceStateAndTails.aemeasurable
  letI : IsProbabilityMeasure M := hMprob
  change IsProbabilityMeasure (M.map edgeMarkedPath)
  exact Measure.isProbabilityMeasure_map measurable_edgeMarkedPath.aemeasurable

/-- Couple the actual two-sided edge-marked M/M/1 path to the good Poisson
suspension. This is the concrete product measure on which the timed action is
defined. -/
noncomputable def geoNNPMF_uniformized_twoSidedMarkedSuspensionProductMeasure
    (rate : ℝ) (rho : ℝ≥0) (hrho : rho < 1) :
    Measure (GoodSuspensionState × (ℤ → (ℕ × Bool))) :=
  timedEmbeddedSuspensionProductMeasure rate
    (geoNNPMF_uniformized_twoSidedMarkedTrajMeasure rho hrho)

/-- The concrete real-time marked M/M/1 suspension becomes a stationary law
as soon as its actual two-sided embedded path is proved invariant under every
integer relabeling. This records the precise discrete proof obligation without
claiming it has been discharged. -/
noncomputable def geoNNPMF_uniformized_twoSidedMarkedSuspensionShiftInvariantLaw_of_intPathShift
    {rate : ℝ} (hrate : 0 < rate) (rho : ℝ≥0) (hrho : rho < 1)
    (hpath : ∀ k : ℤ,
      MeasurePreserving (intPathShift k)
        (geoNNPMF_uniformized_twoSidedMarkedTrajMeasure rho hrho)
        (geoNNPMF_uniformized_twoSidedMarkedTrajMeasure rho hrho)) :
    Palm.ShiftInvariantProbabilityLaw (GoodSuspensionState × (ℤ → (ℕ × Bool))) := by
  letI : IsProbabilityMeasure (geoNNPMF_uniformized_twoSidedMarkedTrajMeasure rho hrho) :=
    isProbabilityMeasure_geoNNPMF_uniformized_twoSidedMarkedTrajMeasure rho hrho
  simpa only [geoNNPMF_uniformized_twoSidedMarkedSuspensionProductMeasure] using
    timedEmbeddedSuspensionShiftInvariantLaw_of_intPathShift hrate
      (geoNNPMF_uniformized_twoSidedMarkedTrajMeasure rho hrho) hpath

/-- Each integer coordinate of the actual two-sided marked trajectory has the
geometric-state/Bernoulli-mark product law. -/
theorem geoNNPMF_uniformized_twoSidedMarkedTraj_coordinate_hasLaw
    (rho : ℝ≥0) (hrho : rho < 1) (i : ℤ) :
    HasLaw (fun x : ℤ → (ℕ × Bool) => x i)
      ((geoNNPMF rho hrho).toMeasure.prod
        (uniformizationArrivalMark (uniformizedBirthProbability rho)
          (uniformizedBirthProbability_le_one rho)).toMeasure)
      (geoNNPMF_uniformized_twoSidedMarkedTrajMeasure rho hrho) := by
  let M : Measure (ℤ → ℕ) := reversibleStateAnchoredTwoSidedTrajMeasure
    (geoNNPMF rho hrho).toMeasure
    (countablePMFKernel
      (reflectedBirthDeathKernel (uniformizedBirthProbability rho)
        (uniformizedBirthProbability_le_one rho)))
  let f : (ℤ → ℕ) → ℕ × Bool := fun x => edgeMarkedPath x i
  have hf : Measurable f := by
    change Measurable (fun x : ℤ → ℕ =>
      markedEdgeProjection (x i, x (i + 1)))
    exact measurable_markedEdgeProjection.comp
      ((measurable_pi_apply i).prodMk (measurable_pi_apply (i + 1)))
  have hlaw := geoNNPMF_uniformized_twoSided_edgeMarked_coordinate_hasLaw rho hrho i
  refine ⟨(measurable_pi_apply i).aemeasurable, ?_⟩
  change Measure.map (fun x : ℤ → (ℕ × Bool) => x i) (M.map edgeMarkedPath) = _
  calc
    Measure.map (fun x : ℤ → (ℕ × Bool) => x i) (M.map edgeMarkedPath) =
        Measure.map f M := by
          rw [Measure.map_map (measurable_pi_apply i) measurable_edgeMarkedPath]
          rfl
    _ = _ := hlaw.map_eq

/-- The product with the good Poisson suspension preserves the verified
state/current-mark law on every marked-path coordinate. -/
theorem geoNNPMF_uniformized_twoSidedMarkedSuspension_coordinate_hasLaw
    {rate : ℝ} (hrate : 0 < rate) (rho : ℝ≥0) (hrho : rho < 1) (i : ℤ) :
    HasLaw (fun z : GoodSuspensionState × (ℤ → (ℕ × Bool)) => z.2 i)
      ((geoNNPMF rho hrho).toMeasure.prod
        (uniformizationArrivalMark (uniformizedBirthProbability rho)
          (uniformizedBirthProbability_le_one rho)).toMeasure)
      (geoNNPMF_uniformized_twoSidedMarkedSuspensionProductMeasure rate rho hrho) := by
  let P : Measure GoodSuspensionState := goodSuspensionMeasure rate
  let Q : Measure (ℤ → (ℕ × Bool)) :=
    geoNNPMF_uniformized_twoSidedMarkedTrajMeasure rho hrho
  let f : (ℤ → (ℕ × Bool)) → ℕ × Bool := fun x => x i
  have hf : Measurable f := measurable_pi_apply i
  have hlaw := geoNNPMF_uniformized_twoSidedMarkedTraj_coordinate_hasLaw rho hrho i
  letI : IsProbabilityMeasure P := by
    dsimp [P]
    exact isProbabilityMeasure_goodSuspensionMeasure hrate
  letI : IsProbabilityMeasure Q :=
    isProbabilityMeasure_geoNNPMF_uniformized_twoSidedMarkedTrajMeasure rho hrho
  refine ⟨(hf.comp measurable_snd).aemeasurable, ?_⟩
  change Measure.map (fun z : GoodSuspensionState × (ℤ → (ℕ × Bool)) => f z.2)
      (P.prod Q) = _
  calc
    Measure.map (fun z : GoodSuspensionState × (ℤ → (ℕ × Bool)) => f z.2)
        (P.prod Q) = Measure.map f (Measure.map Prod.snd (P.prod Q)) := by
          symm
          rw [Measure.map_map hf measurable_snd]
          rfl
    _ = Measure.map f Q := by
          rw [Measure.map_snd_prod, measure_univ, one_smul]
    _ = _ := hlaw.map_eq

end

end AppliedModelingLib.Probability.Queueing
