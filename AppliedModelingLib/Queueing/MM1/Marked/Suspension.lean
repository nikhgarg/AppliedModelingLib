import AppliedModelingLib.Foundations.Probability.Processes.TimedEmbedded.Core
import AppliedModelingLib.Queueing.MM1.Marked.StateTrajectory

/-!
# M/M/1 specialization of a timed embedded suspension

The foundational timed-embedded flow is generic.  This module supplies only
the product law and consecutive-mark consequence for the uniformized marked
M/M/1 trajectory.
-/

namespace AppliedModelingLib.Probability.Queueing

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

open PoissonProcess

/-- The anchored product law that actually combines the existing stationary
one-sided marked M/M/1 trajectory with the two-sided exponential suspension.
It is deliberately not named a real-time stationary law: the marked path has
not yet been extended to an invariant two-sided law. -/
noncomputable def stationaryMarkedMM1SuspensionProductMeasure
    (rate : ℝ) (rho : ℝ≥0) (hrho : rho < 1) :
    Measure (GoodSuspensionState × (ℕ → (ℕ × Bool))) :=
  (goodSuspensionMeasure rate).prod
    (stationaryTrajMeasure
      (markedStatePMF (geoNNPMF rho hrho) (uniformizedBirthProbability rho)
        (uniformizedBirthProbability_le_one rho)).toMeasure
      (markedStateUniformizationMeasureKernel (uniformizedBirthProbability rho)
        (uniformizedBirthProbability_le_one rho)))

/-- The anchored product preserves the already-verified two-consecutive-mark
law on its marked-trajectory factor. -/
theorem stationaryMarkedMM1SuspensionProduct_consecutiveMarks_hasLaw
    {rate : ℝ} (hrate : 0 < rate) (rho : ℝ≥0) (hrho : rho < 1) (n : ℕ) :
    HasLaw
      (fun z : GoodSuspensionState × (ℕ → (ℕ × Bool)) =>
        ((z.2 n).2, (z.2 (n + 1)).2))
      (AppliedModelingLib.pmfProd
        (uniformizationArrivalMark (uniformizedBirthProbability rho)
          (uniformizedBirthProbability_le_one rho))
        (uniformizationArrivalMark (uniformizedBirthProbability rho)
          (uniformizedBirthProbability_le_one rho))).toMeasure
      (stationaryMarkedMM1SuspensionProductMeasure rate rho hrho) := by
  let P : Measure GoodSuspensionState := goodSuspensionMeasure rate
  let Q : Measure (ℕ → (ℕ × Bool)) := stationaryTrajMeasure
    (markedStatePMF (geoNNPMF rho hrho) (uniformizedBirthProbability rho)
      (uniformizedBirthProbability_le_one rho)).toMeasure
    (markedStateUniformizationMeasureKernel (uniformizedBirthProbability rho)
      (uniformizedBirthProbability_le_one rho))
  let f : (ℕ → (ℕ × Bool)) → Bool × Bool :=
    fun x => ((x n).2, (x (n + 1)).2)
  have hf : Measurable f :=
    (measurable_snd.comp (measurable_pi_apply n)).prodMk
      (measurable_snd.comp (measurable_pi_apply (n + 1)))
  have hlaw := geoNNPMF_stationaryMarkedStateTraj_consecutiveMarks_hasLaw rho hrho n
  letI : IsProbabilityMeasure P := by
    dsimp [P]
    exact isProbabilityMeasure_goodSuspensionMeasure hrate
  letI : IsProbabilityMeasure Q := by
    dsimp [Q]
    unfold stationaryTrajMeasure
    infer_instance
  refine ⟨(hf.comp measurable_snd).aemeasurable, ?_⟩
  change Measure.map (fun z : GoodSuspensionState × (ℕ → (ℕ × Bool)) => f z.2)
      (P.prod Q) = _
  calc
    Measure.map (fun z : GoodSuspensionState × (ℕ → (ℕ × Bool)) => f z.2)
        (P.prod Q) = Measure.map f (Measure.map Prod.snd (P.prod Q)) := by
          symm
          rw [Measure.map_map hf measurable_snd]
          rfl
    _ = Measure.map f Q := by
          rw [Measure.map_snd_prod, measure_univ, one_smul]
    _ = _ := hlaw.map_eq

end

end AppliedModelingLib.Probability.Queueing
