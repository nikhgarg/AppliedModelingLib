import AppliedModelingLib.Queueing.MM1.Marked.Suspension
import AppliedModelingLib.Queueing.MM1.TwoSided.TrajectoryShift
import Mathlib.Tactic

/-!
# Edge-mark factor of a two-sided M/M/1 path

This module turns the existing two-sided reversible queue-length trajectory
into a marked embedded path without introducing a new reverse kernel.  The
current event mark is recovered deterministically from its outgoing edge:
`true` exactly when the queue rises by one.  This factor commutes with integer
relabeling, which is the compatibility needed by the timed suspension action.

The current results establish the one-coordinate state/current-mark product
law at every integer index and transport full integer-shift invariance from
the unmarked trajectory to its edge-mark factor. They do not themselves prove
that unmarked path-stationarity layer, thinning, Palm, or PASTA.
-/

namespace AppliedModelingLib.Probability.Queueing

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

/-- Recover the state/current-event-mark path from a two-sided queue-length
path by marking each edge as an arrival precisely when it rises by one. -/
def edgeMarkedPath (x : ℤ → ℕ) : ℤ → (ℕ × Bool) :=
  fun i => (x i, isArrivalEdge (x i) (x (i + 1)))

theorem edgeMarkedPath_apply (x : ℤ → ℕ) (i : ℤ) :
    edgeMarkedPath x i = (x i, isArrivalEdge (x i) (x (i + 1))) := rfl

theorem measurable_edgeMarkedPath : Measurable edgeMarkedPath := by
  apply measurable_pi_lambda
  intro i
  change Measurable (fun x : ℤ → ℕ =>
    markedEdgeProjection (x i, x (i + 1)))
  exact measurable_markedEdgeProjection.comp
    ((measurable_pi_apply i).prodMk (measurable_pi_apply (i + 1)))

/-- Edge marking commutes with integer relabeling, so it can be transported by
the timed suspension action once the unmarked two-sided path is stationary. -/
theorem edgeMarkedPath_intPathShift (k : ℤ) (x : ℤ → ℕ) :
    edgeMarkedPath (intPathShift k x) = intPathShift k (edgeMarkedPath x) := by
  funext i
  change (x (k + i), isArrivalEdge (x (k + i)) (x (k + (i + 1)))) =
    (x (k + i), isArrivalEdge (x (k + i)) (x ((k + i) + 1)))
  have hindex : k + (i + 1) = (k + i) + 1 := by ring
  rw [hindex]

/-- Full integer-shift preservation of the unmarked reversible trajectory
transfers directly to the deterministic edge-mark factor. -/
theorem geoNNPMF_uniformized_twoSided_edgeMarkedMap_intPathShift_measurePreserving_of_unmarked
    (rho : ℝ≥0) (hrho : rho < 1)
    (hpath : ∀ k : ℤ,
      MeasurePreserving (intPathShift k)
        (reversibleStateAnchoredTwoSidedTrajMeasure
          (geoNNPMF rho hrho).toMeasure
          (countablePMFKernel
            (reflectedBirthDeathKernel (uniformizedBirthProbability rho)
              (uniformizedBirthProbability_le_one rho))))
        (reversibleStateAnchoredTwoSidedTrajMeasure
          (geoNNPMF rho hrho).toMeasure
          (countablePMFKernel
            (reflectedBirthDeathKernel (uniformizedBirthProbability rho)
              (uniformizedBirthProbability_le_one rho)))))
    (k : ℤ) :
    MeasurePreserving (intPathShift k)
      ((reversibleStateAnchoredTwoSidedTrajMeasure
        (geoNNPMF rho hrho).toMeasure
        (countablePMFKernel
          (reflectedBirthDeathKernel (uniformizedBirthProbability rho)
            (uniformizedBirthProbability_le_one rho)))).map edgeMarkedPath)
      ((reversibleStateAnchoredTwoSidedTrajMeasure
        (geoNNPMF rho hrho).toMeasure
        (countablePMFKernel
          (reflectedBirthDeathKernel (uniformizedBirthProbability rho)
            (uniformizedBirthProbability_le_one rho)))).map edgeMarkedPath) := by
  let M : Measure (ℤ → ℕ) := reversibleStateAnchoredTwoSidedTrajMeasure
    (geoNNPMF rho hrho).toMeasure
    (countablePMFKernel
      (reflectedBirthDeathKernel (uniformizedBirthProbability rho)
        (uniformizedBirthProbability_le_one rho)))
  change MeasurePreserving (intPathShift k) (M.map edgeMarkedPath) (M.map edgeMarkedPath)
  apply measurePreserving_intPathShift_map_of_commutes M edgeMarkedPath
    measurable_edgeMarkedPath
  · intro j x
    exact edgeMarkedPath_intPathShift j x
  · exact hpath k

/-- Every integer-indexed edge of the reversible stable uniformized M/M/1
trajectory has the exact product law of its pre-event geometric queue state
and recovered Bernoulli arrival mark. -/
theorem geoNNPMF_uniformized_twoSided_edgeMarked_coordinate_hasLaw
    (rho : ℝ≥0) (hrho : rho < 1) (i : ℤ) :
    HasLaw (fun x : ℤ → ℕ => edgeMarkedPath x i)
      ((geoNNPMF rho hrho).toMeasure.prod
        (uniformizationArrivalMark (uniformizedBirthProbability rho)
          (uniformizedBirthProbability_le_one rho)).toMeasure)
      (reversibleStateAnchoredTwoSidedTrajMeasure
        (geoNNPMF rho hrho).toMeasure
        (countablePMFKernel
          (reflectedBirthDeathKernel (uniformizedBirthProbability rho)
            (uniformizedBirthProbability_le_one rho)))) := by
  let π := (geoNNPMF rho hrho).toMeasure
  let p := uniformizedBirthProbability rho
  let K : Kernel ℕ ℕ := countablePMFKernel
    (reflectedBirthDeathKernel p (uniformizedBirthProbability_le_one rho))
  let M : Measure (ℤ → ℕ) := reversibleStateAnchoredTwoSidedTrajMeasure π K
  let pair : (ℤ → ℕ) → ℕ × ℕ := fun x => (x i, x (i + 1))
  have hpair : Measurable pair :=
    (measurable_pi_apply i).prodMk (measurable_pi_apply (i + 1))
  have hpairLaw : M.map pair = π ⊗ₘ K := by
    exact PMFDetailedBalance.reversibleStateAnchoredTwoSidedTrajMeasure_consecutivePair
      (geoNNPMF_detailedBalance rho hrho) i
  refine ⟨(measurable_markedEdgeProjection.comp hpair).aemeasurable, ?_⟩
  change M.map (fun x : ℤ → ℕ =>
    (x i, isArrivalEdge (x i) (x (i + 1)))) = _
  calc
    M.map (fun x : ℤ → ℕ =>
        (x i, isArrivalEdge (x i) (x (i + 1)))) =
        Measure.map markedEdgeProjection (M.map pair) := by
          symm
          rw [Measure.map_map measurable_markedEdgeProjection hpair]
          rfl
    _ = Measure.map markedEdgeProjection (π ⊗ₘ K) := by rw [hpairLaw]
    _ = π.prod (uniformizationArrivalMark p
          (uniformizedBirthProbability_le_one rho)).toMeasure := by
      exact map_markedEdgeProjection_compProd_reflectedBirthDeathKernel π p
        (uniformizedBirthProbability_le_one rho)

end

end AppliedModelingLib.Probability.Queueing
