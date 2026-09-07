import AppliedModelingLib.Queueing.NonpreemptivePriorityStationaryRemoteTrajectory
import Mathlib.Tactic

/-!
# Classwise canonical stationary priority waiting work

This module provides the classwise decomposition of the nonnegative canonical
customer representation of stationary priority waiting work.
-/

namespace AppliedModelingLib.Queueing

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

/-- The nonnegative canonical waiting work contributed by one arrival class.
The class index is fixed while the sum ranges over that class's integer arrival
labels. -/
noncomputable def stationaryPriorityRemotePastClassWaitingWorkCanonicalNN
    {n : ℕ} (meanService : Fin n → ℝ) (arrivalClass : Fin n) :
    ℝ × (Fin n → StationaryPoissonWorkPath) → ENNReal :=
  fun p => ∑' label : ℤ, ENNReal.ofReal
    (stationaryPriorityRemotePastWaitingIdentifierContributionCanonical meanService
      (Sigma.mk arrivalClass label) p)

/-- The classwise canonical waiting-work sum is Borel. -/
theorem measurable_uncurry_stationaryPriorityRemotePastClassWaitingWorkCanonicalNN
    {n : ℕ} (meanService : Fin n → ℝ) (arrivalClass : Fin n) :
    Measurable
      (stationaryPriorityRemotePastClassWaitingWorkCanonicalNN meanService arrivalClass) := by
  apply Measurable.ennreal_tsum
  intro label
  exact
    (measurable_uncurry_stationaryPriorityRemotePastWaitingIdentifierContributionCanonical
      meanService (Sigma.mk arrivalClass label)).ennreal_ofReal

/-- Summing the classwise canonical contributions through a priority level is
exactly the canonical at-least-as-urgent waiting-work sum. -/
theorem sum_stationaryPriorityRemotePastClassWaitingWorkCanonicalNN_eq_atLeastAsUrgent
    {n : ℕ} (meanService : Fin n → ℝ) (priority : Fin n)
    (p : ℝ × (Fin n → StationaryPoissonWorkPath)) :
    ∑ arrivalClass ∈ Finset.univ.filter (fun j : Fin n => j ≤ priority),
      stationaryPriorityRemotePastClassWaitingWorkCanonicalNN meanService arrivalClass p =
      stationaryPriorityRemotePastAtLeastAsUrgentWaitingWorkCanonicalNN meanService priority p := by
  classical
  let f : NonpreemptivePriorityArrivalIndex n → ENNReal := fun q =>
    ENNReal.ofReal
      (stationaryPriorityRemotePastWaitingIdentifierContributionCanonical meanService q p)
  change ∑ arrivalClass ∈ Finset.univ.filter (fun j : Fin n => j ≤ priority),
      ∑' label : ℤ, f (Sigma.mk arrivalClass label) =
      ∑' q : NonpreemptivePriorityArrivalIndex n,
        if q.1 ≤ priority then f q else 0
  rw [ENNReal.tsum_sigma', tsum_fintype, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro arrivalClass _
  by_cases hpriority : arrivalClass ≤ priority <;> simp [hpriority]

end

end AppliedModelingLib.Queueing
