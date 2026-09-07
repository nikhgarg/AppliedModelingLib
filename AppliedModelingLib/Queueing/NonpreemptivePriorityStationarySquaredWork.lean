import AppliedModelingLib.Queueing.NonpreemptivePriorityCanonicalPastCapacitySplit
import AppliedModelingLib.Queueing.NonpreemptivePriorityCanonicalPastStateMeasurability
import AppliedModelingLib.Queueing.NonpreemptivePriorityStationaryStateComponents

/-!
# Square-integrable stationary priority workload envelopes

This module supplies the uniform second-moment envelope that permits finite
priority-trace energy identities to be used without retaining a terminal
boundary contribution at linear time scale.
-/

namespace AppliedModelingLib.Queueing

open AppliedModelingLib.Probability
open AppliedModelingLib.Probability.PoissonProcess
open AppliedModelingLib.Probability.Queueing
open MeasureTheory ProbabilityTheory

noncomputable section

/-- Every empty-start finite replay from the stationary strict past has its
squared residual-work ledger bounded almost surely by the square of the
literal remote-past workload. -/
theorem ae_forall_stationaryPriorityFiniteWindowSquaredResidualWork_le_remotePast_sq
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) :
    ∀ᵐ omega ∂Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate,
      ∀ horizon : ℕ,
        totalNonpreemptivePrioritySquaredResidualWork
          (stationaryPriorityFiniteWindowState meanService omega (-(horizon : ℝ)) 0) ≤
          (stationaryPriorityRemotePastResidualWork meanService omega) ^ 2 := by
  have hfiniteNonnegative : ∀ᵐ omega ∂
      Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate,
      ∀ horizon : ℕ,
        nonnegativeNonpreemptivePriorityResidualWork
          (stationaryPriorityFiniteWindowState meanService omega (-(horizon : ℝ)) 0) := by
    rw [ae_all_iff]
    intro horizon
    exact ae_nonnegativeNonpreemptivePriorityResidualWork_stationaryPriorityFiniteWindowState
      arrivalRate meanService harrivalRate hmeanService (-(horizon : ℝ)) 0
  filter_upwards [
    hfiniteNonnegative,
    ae_forall_totalResidualWork_stationaryPriorityFiniteWindowState_le_remotePast
      arrivalRate meanService harrivalRate hmeanService hstable] with omega hnonnegative htotal
  intro horizon
  let state := stationaryPriorityFiniteWindowState meanService omega (-(horizon : ℝ)) 0
  have hstateTotalNonnegative : 0 ≤ totalNonpreemptivePriorityResidualWork state :=
    totalNonpreemptivePriorityResidualWork_nonneg state (hnonnegative horizon)
  have hremoteNonnegative : 0 ≤ stationaryPriorityRemotePastResidualWork meanService omega :=
    le_trans hstateTotalNonnegative (htotal horizon)
  calc
    totalNonpreemptivePrioritySquaredResidualWork state ≤
        (totalNonpreemptivePriorityResidualWork state) ^ 2 :=
      totalNonpreemptivePrioritySquaredResidualWork_le_sq_totalNonpreemptivePriorityResidualWork
        state (hnonnegative horizon)
    _ ≤ (stationaryPriorityRemotePastResidualWork meanService omega) ^ 2 :=
      (sq_le_sq₀ hstateTotalNonnegative hremoteNonnegative).2 (htotal horizon)

/-- Each finite stationary strict-past squared residual ledger is integrable
under strict total load. -/
theorem integrable_stationaryPriorityFiniteWindowSquaredResidualWork
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1)
    (hn : 0 < n) (horizon : ℕ) :
    Integrable (fun omega => totalNonpreemptivePrioritySquaredResidualWork
      (stationaryPriorityFiniteWindowState meanService omega (-(horizon : ℝ)) 0))
      (Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate) := by
  let P := Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate
  let F : (Fin n → StationaryPoissonWorkPath) → ℝ := fun omega =>
    totalNonpreemptivePrioritySquaredResidualWork
      (stationaryPriorityFiniteWindowState meanService omega (-(horizon : ℝ)) 0)
  let G : (Fin n → StationaryPoissonWorkPath) → ℝ := fun omega =>
    (stationaryPriorityRemotePastResidualWork meanService omega) ^ 2
  have hmeas : AEStronglyMeasurable F P := by
    simpa [F, P] using
      (stationaryPriorityFiniteWindowSquaredResidualWork_hasLaw_canonicalPast
        arrivalRate meanService harrivalRate (horizon : ℝ)).aemeasurable.aestronglyMeasurable
  have hG : Integrable G P := by
    simpa [G, P] using
      MM1DirectCausal.integrable_sq_stationaryPriorityRemotePastResidualWork_of_totalStable
        arrivalRate meanService harrivalRate hmeanService hstable hn
  refine Integrable.mono' hG hmeas ?_
  filter_upwards [
    ae_forall_stationaryPriorityFiniteWindowSquaredResidualWork_le_remotePast_sq
      arrivalRate meanService harrivalRate hmeanService hstable] with omega hle
  have hnonnegative : 0 ≤ F omega := by
    dsimp [F]
    exact totalNonpreemptivePrioritySquaredResidualWork_nonneg _
  rw [Real.norm_of_nonneg hnonnegative]
  simpa [F, G] using hle horizon

/-- The finite terminal squared residual-work expectation is uniformly
bounded by the stationary workload second moment. -/
theorem integral_stationaryPriorityFiniteWindowSquaredResidualWork_le_remotePast_sq
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1)
    (hn : 0 < n) (horizon : ℕ) :
    ∫ omega, totalNonpreemptivePrioritySquaredResidualWork
      (stationaryPriorityFiniteWindowState meanService omega (-(horizon : ℝ)) 0)
      ∂Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate ≤
      ∫ omega, (stationaryPriorityRemotePastResidualWork meanService omega) ^ 2
      ∂Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate := by
  apply integral_mono_ae
  · exact integrable_stationaryPriorityFiniteWindowSquaredResidualWork
      arrivalRate meanService harrivalRate hmeanService hstable hn horizon
  · exact MM1DirectCausal.integrable_sq_stationaryPriorityRemotePastResidualWork_of_totalStable
      arrivalRate meanService harrivalRate hmeanService hstable hn
  · filter_upwards [
      ae_forall_stationaryPriorityFiniteWindowSquaredResidualWork_le_remotePast_sq
        arrivalRate meanService harrivalRate hmeanService hstable] with omega hle
    exact hle horizon

/-- The squared residual ledger of the literal remote-past state is bounded
almost surely by the square of its total residual workload. -/
theorem ae_stationaryPriorityRemotePastSquaredResidualWork_le_remotePast_sq
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) :
    ∀ᵐ omega ∂Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate,
      stationaryPriorityRemotePastSquaredResidualWork meanService omega ≤
        (stationaryPriorityRemotePastResidualWork meanService omega) ^ 2 := by
  filter_upwards [
    ae_all_stationaryPriorityWorkRequirement_positive
      arrivalRate meanService harrivalRate hmeanService,
    ae_exists_stationaryPriorityRemotePastState_liveCoalescence
      arrivalRate meanService harrivalRate hmeanService hstable] with omega hpositive hcoalesces
  rcases hcoalesces with ⟨cutoff, hcutoffNonnegative, hcoalesces⟩
  let horizon : ℕ := Nat.ceil cutoff
  have hcutoff : cutoff ≤ (horizon : ℝ) := by
    dsimp [horizon]
    exact Nat.le_ceil cutoff
  let state := stationaryPriorityFiniteWindowState meanService omega (-(horizon : ℝ)) 0
  have hjobs : ∀ job ∈ stationaryPriorityArrivalWindowJobs
      meanService omega (-(horizon : ℝ)) 0, 0 ≤ job.serviceWork := by
    intro job hjob
    rcases (mem_stationaryPriorityArrivalWindowJobs_iff
      meanService omega (-(horizon : ℝ)) 0 job).mp hjob with ⟨i, k, _, hjob⟩
    subst job
    exact (hpositive i k).le
  have hstateNonnegative : nonnegativeNonpreemptivePriorityResidualWork state := by
    exact nonnegativeNonpreemptivePriorityResidualWork_stationaryPriorityFiniteWindowState
      meanService omega (-(horizon : ℝ)) 0 hjobs
  have hlive : liveEquivalentNonpreemptivePriorityWorkState state
      (stationaryPriorityRemotePastState meanService omega) :=
    hcoalesces (horizon : ℝ) hcutoff
  change totalNonpreemptivePrioritySquaredResidualWork
      (stationaryPriorityRemotePastState meanService omega) ≤
      (stationaryPriorityRemotePastResidualWork meanService omega) ^ 2
  calc
    totalNonpreemptivePrioritySquaredResidualWork
        (stationaryPriorityRemotePastState meanService omega) =
        totalNonpreemptivePrioritySquaredResidualWork state :=
      (totalNonpreemptivePrioritySquaredResidualWork_eq_of_liveEquivalent hlive).symm
    _ ≤ (totalNonpreemptivePriorityResidualWork state) ^ 2 :=
      totalNonpreemptivePrioritySquaredResidualWork_le_sq_totalNonpreemptivePriorityResidualWork
        state hstateNonnegative
    _ = (stationaryPriorityRemotePastResidualWork meanService omega) ^ 2 := by
      change (totalNonpreemptivePriorityResidualWork state) ^ 2 =
        (totalNonpreemptivePriorityResidualWork
          (stationaryPriorityRemotePastState meanService omega)) ^ 2
      rw [totalNonpreemptivePriorityResidualWork_eq_of_liveEquivalent hlive]

/-- The squared residual ledger of the literal remote-past state is
integrable under strict total load. -/
theorem integrable_stationaryPriorityRemotePastSquaredResidualWork
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1)
    (hn : 0 < n) :
    Integrable (stationaryPriorityRemotePastSquaredResidualWork meanService)
      (Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate) := by
  let P := Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate
  let F : (Fin n → StationaryPoissonWorkPath) → ℝ :=
    stationaryPriorityRemotePastSquaredResidualWork meanService
  let G : (Fin n → StationaryPoissonWorkPath) → ℝ := fun omega =>
    (stationaryPriorityRemotePastResidualWork meanService omega) ^ 2
  have hG : Integrable G P := by
    simpa [G, P] using
      MM1DirectCausal.integrable_sq_stationaryPriorityRemotePastResidualWork_of_totalStable
        arrivalRate meanService harrivalRate hmeanService hstable hn
  refine Integrable.mono' hG
    (aemeasurable_stationaryPriorityRemotePastSquaredResidualWork
      arrivalRate meanService harrivalRate hmeanService hstable).aestronglyMeasurable ?_
  filter_upwards [
    ae_stationaryPriorityRemotePastSquaredResidualWork_le_remotePast_sq
      arrivalRate meanService harrivalRate hmeanService hstable] with omega hle
  have hnonnegative : 0 ≤ F omega := by
    dsimp [F]
    exact totalNonpreemptivePrioritySquaredResidualWork_nonneg _
  rw [Real.norm_of_nonneg hnonnegative]
  simpa [F, G] using hle

/-- The stationary squared residual ledger has constant expected occupation
along every finite physical-time interval. -/
theorem integral_stationaryPriorityRemotePastSquaredResidualWork_flow_Ioc
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1)
    (hn : 0 < n) (a b : ℝ) (hab : a ≤ b) :
    ∫ p : ℝ × (Fin n → StationaryPoissonWorkPath),
      stationaryPriorityRemotePastSquaredResidualWork meanService
        (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow p.1 p.2) ∂
        ((MeasureTheory.volume.restrict (Set.Ioc a b)).prod
          (Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate)) =
      (b - a) * ∫ omega, stationaryPriorityRemotePastSquaredResidualWork meanService omega ∂
        Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate := by
  exact Probability.PoissonProcess.integral_uncurry_comp_multiclassStationaryPoissonWorkFlow_Ioc
    arrivalRate harrivalRate
    (stationaryPriorityRemotePastSquaredResidualWork meanService)
    (integrable_stationaryPriorityRemotePastSquaredResidualWork
      arrivalRate meanService harrivalRate hmeanService hstable hn)
    a b hab

/-- The expected terminal squared residual ledger of empty-start strict-past
replays converges to the literal remote-past squared ledger. -/
theorem tendsto_integral_stationaryPriorityFiniteWindowSquaredResidualWork
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1)
    (hn : 0 < n) :
    Filter.Tendsto (fun horizon : ℕ =>
      ∫ omega, totalNonpreemptivePrioritySquaredResidualWork
        (stationaryPriorityFiniteWindowState meanService omega (-(horizon : ℝ)) 0)
        ∂Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate)
      Filter.atTop
      (nhds (∫ omega, stationaryPriorityRemotePastSquaredResidualWork meanService omega
        ∂Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate)) := by
  let P := Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate
  let F : ℕ → (Fin n → StationaryPoissonWorkPath) → ℝ := fun horizon omega =>
    totalNonpreemptivePrioritySquaredResidualWork
      (stationaryPriorityFiniteWindowState meanService omega (-(horizon : ℝ)) 0)
  let f : (Fin n → StationaryPoissonWorkPath) → ℝ :=
    stationaryPriorityRemotePastSquaredResidualWork meanService
  let g : (Fin n → StationaryPoissonWorkPath) → ℝ := fun omega =>
    (stationaryPriorityRemotePastResidualWork meanService omega) ^ 2
  have hmeas : ∀ horizon, AEStronglyMeasurable (F horizon) P := by
    intro horizon
    simpa [F, P] using
      (stationaryPriorityFiniteWindowSquaredResidualWork_hasLaw_canonicalPast
        arrivalRate meanService harrivalRate (horizon : ℝ)).aemeasurable.aestronglyMeasurable
  have hgint : Integrable g P := by
    simpa [g, P] using
      MM1DirectCausal.integrable_sq_stationaryPriorityRemotePastResidualWork_of_totalStable
        arrivalRate meanService harrivalRate hmeanService hstable hn
  have hbound : ∀ horizon, ∀ᵐ omega ∂P, ‖F horizon omega‖ ≤ g omega := by
    intro horizon
    filter_upwards [
      ae_forall_stationaryPriorityFiniteWindowSquaredResidualWork_le_remotePast_sq
        arrivalRate meanService harrivalRate hmeanService hstable] with omega hle
    have hnonnegative : 0 ≤ F horizon omega := by
      dsimp [F]
      exact totalNonpreemptivePrioritySquaredResidualWork_nonneg _
    rw [Real.norm_of_nonneg hnonnegative]
    simpa [F, g] using hle horizon
  have hlimit : ∀ᵐ omega ∂P, Filter.Tendsto (fun horizon : ℕ => F horizon omega)
      Filter.atTop (nhds (f omega)) := by
    filter_upwards [
      ae_eventually_stationaryPriorityFiniteWindowSquaredResidualWork_eq_remotePast
        arrivalRate meanService harrivalRate hmeanService hstable] with omega heventual
    exact tendsto_nhds_of_eventually_eq (by simpa [F, f] using heventual)
  simpa [F, f, P, g] using
    (MeasureTheory.tendsto_integral_of_dominated_convergence
      (μ := P) (F := F) (f := f) g hmeas hgint hbound hlimit)

/-- The expected terminal squared-work boundary of a strict-past replay
vanishes after division by its natural horizon. -/
theorem tendsto_integral_stationaryPriorityFiniteWindowSquaredResidualWork_div_natCast
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1)
    (hn : 0 < n) :
    Filter.Tendsto (fun horizon : ℕ =>
      (∫ omega, totalNonpreemptivePrioritySquaredResidualWork
        (stationaryPriorityFiniteWindowState meanService omega (-(horizon : ℝ)) 0)
        ∂Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate) /
        (horizon : ℝ))
      Filter.atTop (nhds 0) := by
  exact (tendsto_integral_stationaryPriorityFiniteWindowSquaredResidualWork
    arrivalRate meanService harrivalRate hmeanService hstable hn).div_atTop
      tendsto_natCast_atTop_atTop

end

end AppliedModelingLib.Queueing
