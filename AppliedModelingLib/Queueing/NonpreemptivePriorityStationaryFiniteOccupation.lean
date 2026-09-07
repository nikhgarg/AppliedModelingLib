import AppliedModelingLib.Queueing.NonpreemptivePriorityStationaryPathMeasurability
import AppliedModelingLib.Queueing.NonpreemptivePriorityStationarySquaredWork
import Mathlib.Tactic

/-!
# Integrability of finite stationary priority occupations

This module supplies the product-space integrability prerequisite for passing
finite priority-trace occupation identities through Fubini.  It concerns only
literal empty-start finite windows and their marked-input domination.
-/

namespace AppliedModelingLib.Queueing

open MeasureTheory ProbabilityTheory

noncomputable section

/-- The active residual of an empty-start replay over a fixed past window is
integrable jointly in its physical observation time and the marked stationary
input. -/
theorem integrable_uncurry_activeNonpreemptivePriorityResidualWork_stationaryPriorityFiniteWindow
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (horizon : ℕ) :
    Integrable (fun p : ℝ × (Fin n → StationaryPoissonWorkPath) =>
      activeNonpreemptivePriorityResidualWork
        (stationaryPriorityFiniteWindowState meanService p.2 (-(horizon : ℝ)) p.1))
      ((MeasureTheory.volume.restrict (Set.Ioc (-(horizon : ℝ)) 0)).prod
        (Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate)) := by
  let μI : Measure ℝ := MeasureTheory.volume.restrict (Set.Ioc (-(horizon : ℝ)) 0)
  let P := Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate
  let F : ℝ × (Fin n → StationaryPoissonWorkPath) → ℝ := fun p =>
    activeNonpreemptivePriorityResidualWork
      (stationaryPriorityFiniteWindowState meanService p.2 (-(horizon : ℝ)) p.1)
  let G : ℝ × (Fin n → StationaryPoissonWorkPath) → ℝ := fun p =>
    stationaryPriorityTotalPastWorkAggregate meanService p.2 (horizon : ℝ)
  letI : IsProbabilityMeasure P := by
    dsimp [P]
    exact Probability.PoissonProcess.isProbabilityMeasure_multiclassStationaryPoissonWorkMeasure
      arrivalRate harrivalRate
  letI : IsFiniteMeasure μI := by
    dsimp [μI]
    infer_instance
  have hGbase : Integrable (fun omega =>
      stationaryPriorityTotalPastWorkAggregate meanService omega (horizon : ℝ)) P := by
    simpa [P] using integrable_stationaryPriorityTotalPastWorkAggregate
      arrivalRate meanService harrivalRate (horizon : ℝ) (Nat.cast_nonneg horizon)
  have hG : Integrable G (μI.prod P) := by
    simpa [G] using hGbase.comp_snd μI
  have hmeas : AEStronglyMeasurable F (μI.prod P) := by
    exact (measurable_uncurry_stationaryPriorityFiniteWindowActiveResidualWork
      meanService (-(horizon : ℝ))).aestronglyMeasurable
  refine Integrable.mono' hG hmeas ?_
  have htime : ∀ᵐ p : ℝ × (Fin n → StationaryPoissonWorkPath) ∂μI.prod P,
      p.1 ∈ Set.Ioc (-(horizon : ℝ)) 0 := by
    exact (Measure.quasiMeasurePreserving_fst (μ := μI) (ν := P)).ae
      (MeasureTheory.ae_restrict_mem measurableSet_Ioc)
  have hpositive : ∀ᵐ p : ℝ × (Fin n → StationaryPoissonWorkPath) ∂μI.prod P,
      ∀ i k, 0 < stationaryPriorityWorkRequirement meanService i p.2 k := by
    exact (Measure.quasiMeasurePreserving_snd (μ := μI) (ν := P)).ae
      (ae_all_stationaryPriorityWorkRequirement_positive
        arrivalRate meanService harrivalRate hmeanService)
  filter_upwards [htime, hpositive] with p hp hpositive
  have hleft : -(horizon : ℝ) ≤ p.1 := hp.1.le
  have hright : p.1 ≤ 0 := hp.2
  have hwindow : ∀ job ∈ stationaryPriorityArrivalWindowJobs meanService p.2
      (-(horizon : ℝ)) 0, 0 < job.serviceWork := by
    intro job hjob
    rcases (mem_stationaryPriorityArrivalWindowJobs_iff
      meanService p.2 (-(horizon : ℝ)) 0 job).mp hjob with ⟨i, k, _, hjob⟩
    subst job
    exact hpositive i k
  have hprefix : ∀ job ∈ stationaryPriorityArrivalWindowJobs meanService p.2
      (-(horizon : ℝ)) p.1, 0 ≤ job.serviceWork := by
    intro job hjob
    exact (hwindow job (by
      rw [stationaryPriorityArrivalWindowJobs_append
        meanService p.2 (-(horizon : ℝ)) p.1 0 hleft hright]
      exact List.mem_append_left _ hjob)).le
  let state := stationaryPriorityFiniteWindowState meanService p.2 (-(horizon : ℝ)) p.1
  have hstate : nonnegativeNonpreemptivePriorityResidualWork state := by
    exact nonnegativeNonpreemptivePriorityResidualWork_stationaryPriorityFiniteWindowState
      meanService p.2 (-(horizon : ℝ)) p.1 hprefix
  have hactiveNonnegative : 0 ≤ F p := by
    dsimp [F, state]
    unfold activeNonpreemptivePriorityResidualWork
    cases hactive :
        (stationaryPriorityFiniteWindowState meanService p.2 (-(horizon : ℝ)) p.1).active with
    | none => simp
    | some active => exact hstate.1 active hactive
  rw [Real.norm_of_nonneg hactiveNonnegative]
  calc
    F p = activeNonpreemptivePriorityResidualWork state := rfl
    _ ≤ totalNonpreemptivePriorityResidualWork state :=
      activeNonpreemptivePriorityResidualWork_le_total state hstate
    _ ≤ stationaryPriorityArrivalWindowTotalWork meanService p.2 (-(horizon : ℝ)) 0 :=
      totalResidualWork_stationaryPriorityFiniteWindowState_le_windowTotalWork_of_le
        meanService p.2 (-(horizon : ℝ)) p.1 0 hleft hright hwindow
    _ = G p := by
      exact stationaryPriorityArrivalWindowTotalWork_neg_to_zero
        meanService p.2 (horizon : ℝ)

/-- Reindexing a finite-window active occupation by the stationary input flow
turns it into the integral of the expected empty-start active residual over
its elapsed past horizon. -/
theorem integral_uncurry_activeNonpreemptivePriorityResidualWork_stationaryPriorityFiniteWindow_eq_intervalIntegral
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (horizon : ℕ) :
    (∫ p : ℝ × (Fin n → StationaryPoissonWorkPath),
      activeNonpreemptivePriorityResidualWork
        (stationaryPriorityFiniteWindowState meanService p.2 (-(horizon : ℝ)) p.1) ∂
        ((MeasureTheory.volume.restrict (Set.Ioc (-(horizon : ℝ)) 0)).prod
          (Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate))) =
      ∫ u in 0..(horizon : ℝ), ∫ omega,
        activeNonpreemptivePriorityResidualWork
          (stationaryPriorityFiniteWindowState meanService omega (-u) 0) ∂
          Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate := by
  let μI : Measure ℝ := MeasureTheory.volume.restrict (Set.Ioc (-(horizon : ℝ)) 0)
  let P := Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate
  let A : ℝ → (Fin n → StationaryPoissonWorkPath) → ℝ := fun t omega =>
    activeNonpreemptivePriorityResidualWork
      (stationaryPriorityFiniteWindowState meanService omega (-(horizon : ℝ)) t)
  let F : ℝ → (Fin n → StationaryPoissonWorkPath) → ℝ := fun u omega =>
    activeNonpreemptivePriorityResidualWork
      (stationaryPriorityFiniteWindowState meanService omega (-u) 0)
  letI : IsProbabilityMeasure P := by
    dsimp [P]
    exact Probability.PoissonProcess.isProbabilityMeasure_multiclassStationaryPoissonWorkMeasure
      arrivalRate harrivalRate
  letI : IsFiniteMeasure μI := by
    dsimp [μI]
    infer_instance
  have hA : Integrable (Function.uncurry A) (μI.prod P) := by
    simpa [A, μI, P] using
      integrable_uncurry_activeNonpreemptivePriorityResidualWork_stationaryPriorityFiniteWindow
        arrivalRate meanService harrivalRate hmeanService horizon
  have htime : ∀ t : ℝ,
      (∫ omega, A t omega ∂P) = ∫ omega, F (t + (horizon : ℝ)) omega ∂P := by
    intro t
    have hshift : ∀ᵐ omega ∂P,
        F (t + (horizon : ℝ))
          (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow t omega) =
          A t omega := by
      change ∀ᵐ omega ∂P,
        activeNonpreemptivePriorityResidualWork
          (stationaryPriorityFiniteWindowState meanService
            (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow t omega)
            (-(t + (horizon : ℝ))) 0) =
          activeNonpreemptivePriorityResidualWork
            (stationaryPriorityFiniteWindowState meanService omega (-(horizon : ℝ)) t)
      convert
        (ae_activeNonpreemptivePriorityResidualWork_stationaryPriorityFiniteWindow_flow
          arrivalRate meanService harrivalRate t (-(horizon : ℝ)) t) using 1 <;> ring_nf
    calc
      (∫ omega, A t omega ∂P) =
          ∫ omega, F (t + (horizon : ℝ))
            (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow t omega) ∂P := by
              symm
              exact MeasureTheory.integral_congr_ae hshift
      _ = ∫ omega, F (t + (horizon : ℝ)) omega ∂P := by
        simpa [P, Function.comp_def] using
          (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow_measurePreserving
            arrivalRate harrivalRate t).hasLaw.integral_comp
              (f := F (t + (horizon : ℝ)))
              (stationaryPriorityFiniteWindowActiveResidualWork_hasLaw_canonicalPast
                arrivalRate meanService harrivalRate (t + (horizon : ℝ))).aemeasurable.aestronglyMeasurable
  calc
    ∫ p : ℝ × (Fin n → StationaryPoissonWorkPath), A p.1 p.2 ∂μI.prod P =
        ∫ t, (∫ omega, A t omega ∂P) ∂μI :=
      MeasureTheory.integral_prod _ hA
    _ = ∫ t in (-(horizon : ℝ))..0, (∫ omega, A t omega ∂P) := by
      simp only [μI, intervalIntegral.integral_of_le
        (neg_nonpos.mpr (Nat.cast_nonneg horizon))]
    _ = ∫ t in (-(horizon : ℝ))..0, (∫ omega,
        F (t + (horizon : ℝ)) omega ∂P) := by
      apply intervalIntegral.integral_congr
      intro t ht
      exact htime t
    _ = ∫ u in 0..(horizon : ℝ), (∫ omega, F u omega ∂P) := by
      simpa only [neg_add_cancel, zero_add] using
        (intervalIntegral.integral_comp_add_right
          (f := fun u => ∫ omega, F u omega ∂P)
          (a := -(horizon : ℝ)) (b := 0) (horizon : ℝ))

/-- The expected empty-start active residual is interval-integrable on every
finite nonnegative horizon.  Its proof is obtained by transporting the
jointly integrable finite replay occupation through the stationary flow. -/
theorem intervalIntegrable_expected_activeNonpreemptivePriorityResidualWork_stationaryPriorityFiniteWindow
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (horizon : ℕ) :
    IntervalIntegrable (fun u : ℝ => ∫ omega,
      activeNonpreemptivePriorityResidualWork
        (stationaryPriorityFiniteWindowState meanService omega (-u) 0) ∂
        Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate)
      MeasureTheory.volume 0 (horizon : ℝ) := by
  let μI : Measure ℝ := MeasureTheory.volume.restrict (Set.Ioc (-(horizon : ℝ)) 0)
  let P := Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate
  let A : ℝ → (Fin n → StationaryPoissonWorkPath) → ℝ := fun t omega =>
    activeNonpreemptivePriorityResidualWork
      (stationaryPriorityFiniteWindowState meanService omega (-(horizon : ℝ)) t)
  let F : ℝ → (Fin n → StationaryPoissonWorkPath) → ℝ := fun u omega =>
    activeNonpreemptivePriorityResidualWork
      (stationaryPriorityFiniteWindowState meanService omega (-u) 0)
  letI : IsProbabilityMeasure P := by
    dsimp [P]
    exact Probability.PoissonProcess.isProbabilityMeasure_multiclassStationaryPoissonWorkMeasure
      arrivalRate harrivalRate
  letI : IsFiniteMeasure μI := by
    dsimp [μI]
    infer_instance
  have hA : Integrable (Function.uncurry A) (μI.prod P) := by
    simpa [A, μI, P] using
      integrable_uncurry_activeNonpreemptivePriorityResidualWork_stationaryPriorityFiniteWindow
        arrivalRate meanService harrivalRate hmeanService horizon
  have htime : ∀ t : ℝ,
      (∫ omega, A t omega ∂P) = ∫ omega, F (t + (horizon : ℝ)) omega ∂P := by
    intro t
    have hshift : ∀ᵐ omega ∂P,
        F (t + (horizon : ℝ))
          (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow t omega) =
          A t omega := by
      change ∀ᵐ omega ∂P,
        activeNonpreemptivePriorityResidualWork
          (stationaryPriorityFiniteWindowState meanService
            (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow t omega)
            (-(t + (horizon : ℝ))) 0) =
          activeNonpreemptivePriorityResidualWork
            (stationaryPriorityFiniteWindowState meanService omega (-(horizon : ℝ)) t)
      convert
        (ae_activeNonpreemptivePriorityResidualWork_stationaryPriorityFiniteWindow_flow
          arrivalRate meanService harrivalRate t (-(horizon : ℝ)) t) using 1 <;> ring_nf
    calc
      (∫ omega, A t omega ∂P) =
          ∫ omega, F (t + (horizon : ℝ))
            (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow t omega) ∂P := by
              symm
              exact MeasureTheory.integral_congr_ae hshift
      _ = ∫ omega, F (t + (horizon : ℝ)) omega ∂P := by
        simpa [P, Function.comp_def] using
          (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow_measurePreserving
            arrivalRate harrivalRate t).hasLaw.integral_comp
              (f := F (t + (horizon : ℝ)))
              (stationaryPriorityFiniteWindowActiveResidualWork_hasLaw_canonicalPast
                arrivalRate meanService harrivalRate (t + (horizon : ℝ))).aemeasurable.aestronglyMeasurable
  have hAintegral : Integrable (fun t => ∫ omega, A t omega ∂P) μI :=
    hA.integral_prod_left
  have hAinterval : IntervalIntegrable (fun t => ∫ omega, A t omega ∂P)
      MeasureTheory.volume (-(horizon : ℝ)) 0 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le
      (neg_nonpos.mpr (Nat.cast_nonneg horizon))]
    simpa [μI] using hAintegral
  have hshifted : IntervalIntegrable (fun t => ∫ omega,
      F (t + (horizon : ℝ)) omega ∂P)
      MeasureTheory.volume (-(horizon : ℝ)) 0 := by
    apply hAinterval.congr
    intro t ht
    exact htime t
  simpa [F, P] using
    (IntervalIntegrable.comp_add_right_iff
      (f := fun u => ∫ omega, F u omega ∂P)
      (a := -(horizon : ℝ)) (b := 0) (c := (horizon : ℝ))).mp hshifted

/-- A locally interval-integrable real function converging at positive
infinity has the same limit as its interval averages over `[0,n]`.  This
is the continuous-time counterpart needed to combine a finite occupation
identity with the usual discrete Cesàro theorem. -/
theorem tendsto_natCast_inv_mul_intervalIntegral_zero_of_tendsto
    {f : ℝ → ℝ} {limit : ℝ}
    (hlocal : ∀ horizon : ℕ,
      IntervalIntegrable f MeasureTheory.volume 0 (horizon : ℝ))
    (hlimit : Filter.Tendsto f Filter.atTop (nhds limit)) :
    Filter.Tendsto (fun horizon : ℕ => (horizon : ℝ)⁻¹ *
      ∫ u in 0..(horizon : ℝ), f u) Filter.atTop (nhds limit) := by
  have hblock : Filter.Tendsto (fun horizon : ℕ =>
      ∫ u in (horizon : ℝ)..((horizon + 1 : ℕ) : ℝ), f u)
      Filter.atTop (nhds limit) := by
    refine Metric.tendsto_atTop.2 ?_
    intro ε hε
    rcases (Metric.tendsto_atTop.1 hlimit) (ε / 2) (by linarith) with
      ⟨threshold, hthreshold⟩
    refine ⟨Nat.ceil threshold, ?_⟩
    intro horizon hhorizon
    have hthresholdHorizon : threshold ≤ (horizon : ℝ) := by
      calc
        threshold ≤ (Nat.ceil threshold : ℝ) := Nat.le_ceil threshold
        _ ≤ (horizon : ℝ) := by exact_mod_cast hhorizon
    have hinterval : IntervalIntegrable f MeasureTheory.volume
        (horizon : ℝ) ((horizon + 1 : ℕ) : ℝ) := by
      apply (hlocal (horizon + 1)).mono_set
      intro u hu
      have hstep : (horizon : ℝ) ≤ ((horizon + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.le_succ horizon
      rw [Set.uIcc_of_le hstep] at hu
      rw [Set.uIcc_of_le (by positivity)]
      have hnonnegative : (0 : ℝ) ≤ (horizon : ℝ) := Nat.cast_nonneg horizon
      exact ⟨hnonnegative.trans hu.1, hu.2⟩
    have hconst : IntervalIntegrable (fun _ : ℝ => limit) MeasureTheory.volume
        (horizon : ℝ) ((horizon + 1 : ℕ) : ℝ) :=
      intervalIntegrable_const (by finiteness)
    have hsub : (∫ u in (horizon : ℝ)..((horizon + 1 : ℕ) : ℝ), f u) - limit =
        ∫ u in (horizon : ℝ)..((horizon + 1 : ℕ) : ℝ), (f u - limit) := by
      calc
        (∫ u in (horizon : ℝ)..((horizon + 1 : ℕ) : ℝ), f u) - limit =
            (∫ u in (horizon : ℝ)..((horizon + 1 : ℕ) : ℝ), f u) -
              ∫ _ in (horizon : ℝ)..((horizon + 1 : ℕ) : ℝ), limit := by
                rw [intervalIntegral.integral_const]
                norm_num
        _ = ∫ u in (horizon : ℝ)..((horizon + 1 : ℕ) : ℝ), (f u - limit) := by
          symm
          exact intervalIntegral.integral_sub hinterval hconst
    have hnorm : ‖(∫ u in (horizon : ℝ)..((horizon + 1 : ℕ) : ℝ), f u) - limit‖ ≤
        ε / 2 := by
      rw [hsub]
      calc
        ‖∫ u in (horizon : ℝ)..((horizon + 1 : ℕ) : ℝ), (f u - limit)‖ ≤
            (ε / 2) * |((horizon + 1 : ℕ) : ℝ) - (horizon : ℝ)| := by
              apply intervalIntegral.norm_integral_le_of_norm_le_const
              intro u hu
              rw [Set.uIoc_of_le (by exact_mod_cast Nat.le_succ horizon)] at hu
              have hthresholdU : threshold ≤ u := hthresholdHorizon.trans hu.1.le
              simpa only [Real.norm_eq_abs] using
                (le_of_lt (by simpa only [Real.dist_eq] using hthreshold u hthresholdU))
        _ = ε / 2 := by norm_num
    simpa only [Real.dist_eq, Real.norm_eq_abs] using lt_of_le_of_lt hnorm (by linarith)
  have hsum : ∀ horizon : ℕ,
      (∑ k ∈ Finset.range horizon,
        ∫ u in (k : ℝ)..((k + 1 : ℕ) : ℝ), f u) =
        ∫ u in 0..(horizon : ℝ), f u := by
    intro horizon
    simpa using (intervalIntegral.sum_integral_adjacent_intervals_Ico
      (f := f) (a := fun k : ℕ => (k : ℝ)) (m := 0) (n := horizon)
      (Nat.zero_le horizon) (fun k _ => by
        apply (hlocal (k + 1)).mono_set
        intro u hu
        have hstep : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
          exact_mod_cast Nat.le_succ k
        rw [Set.uIcc_of_le hstep] at hu
        rw [Set.uIcc_of_le (by positivity)]
        have hnonnegative : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
        exact ⟨hnonnegative.trans hu.1, hu.2⟩))
  apply hblock.cesaro.congr'
  filter_upwards with horizon
  rw [hsum horizon]

/-- The normalized active occupation of an empty-start finite stationary
replay converges to the expectation of the literal remote-past active
residual. -/
theorem tendsto_natCast_inv_mul_integral_uncurry_activeNonpreemptivePriorityResidualWork_stationaryPriorityFiniteWindow
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) (hn : 0 < n) :
    Filter.Tendsto (fun horizon : ℕ => (horizon : ℝ)⁻¹ *
      (∫ p : ℝ × (Fin n → StationaryPoissonWorkPath),
        activeNonpreemptivePriorityResidualWork
          (stationaryPriorityFiniteWindowState meanService p.2 (-(horizon : ℝ)) p.1) ∂
          ((MeasureTheory.volume.restrict (Set.Ioc (-(horizon : ℝ)) 0)).prod
            (Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate))))
      Filter.atTop
      (nhds (∫ omega, stationaryPriorityRemotePastActiveResidualWork meanService omega ∂
        Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate)) := by
  let f : ℝ → ℝ := fun u => ∫ omega,
    activeNonpreemptivePriorityResidualWork
      (stationaryPriorityFiniteWindowState meanService omega (-u) 0) ∂
      Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate
  have hcesaro : Filter.Tendsto (fun horizon : ℕ => (horizon : ℝ)⁻¹ *
      ∫ u in 0..(horizon : ℝ), f u) Filter.atTop
      (nhds (∫ omega, stationaryPriorityRemotePastActiveResidualWork meanService omega ∂
        Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate)) :=
    tendsto_natCast_inv_mul_intervalIntegral_zero_of_tendsto
      (fun horizon => by
        simpa [f] using
          intervalIntegrable_expected_activeNonpreemptivePriorityResidualWork_stationaryPriorityFiniteWindow
            arrivalRate meanService harrivalRate hmeanService horizon)
      (by
        simpa [f] using
          tendsto_integral_activeResidualWork_stationaryPriorityFiniteWindowState_real
            arrivalRate meanService harrivalRate hmeanService hstable hn)
  apply hcesaro.congr'
  filter_upwards with horizon
  rw [integral_uncurry_activeNonpreemptivePriorityResidualWork_stationaryPriorityFiniteWindow_eq_intervalIntegral
    arrivalRate meanService harrivalRate hmeanService horizon]

/-- Integrating the finite squared-work energy balance over stationary input
gives an exact expected finite-window occupation identity. -/
theorem integral_stationaryPriorityFiniteWindowSquaredResidualWork_add_two_mul_occupation
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1)
    (hn : 0 < n) (horizon : ℕ) :
    (∫ omega, totalNonpreemptivePrioritySquaredResidualWork
      (stationaryPriorityFiniteWindowState meanService omega (-(horizon : ℝ)) 0)
      ∂Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate) +
      2 * (∫ p : ℝ × (Fin n → StationaryPoissonWorkPath),
        activeNonpreemptivePriorityResidualWork
          (stationaryPriorityFiniteWindowState meanService p.2 (-(horizon : ℝ)) p.1)
        ∂((MeasureTheory.volume.restrict (Set.Ioc (-(horizon : ℝ)) 0)).prod
          (Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate))) =
      2 * (∑ i, arrivalRate i * meanService i ^ 2) * (horizon : ℝ) := by
  let μI : Measure ℝ := MeasureTheory.volume.restrict (Set.Ioc (-(horizon : ℝ)) 0)
  let P := Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate
  let f : ℝ → (Fin n → StationaryPoissonWorkPath) → ℝ := fun t omega =>
    activeNonpreemptivePriorityResidualWork
      (stationaryPriorityFiniteWindowState meanService omega (-(horizon : ℝ)) t)
  let S : (Fin n → StationaryPoissonWorkPath) → ℝ := fun omega =>
    totalNonpreemptivePrioritySquaredResidualWork
      (stationaryPriorityFiniteWindowState meanService omega (-(horizon : ℝ)) 0)
  let R : (Fin n → StationaryPoissonWorkPath) → ℝ := fun omega =>
    stationaryPriorityTotalPastSquareWorkAggregate meanService omega (horizon : ℝ)
  letI : IsProbabilityMeasure P := by
    dsimp [P]
    exact Probability.PoissonProcess.isProbabilityMeasure_multiclassStationaryPoissonWorkMeasure
      arrivalRate harrivalRate
  letI : IsFiniteMeasure μI := by
    dsimp [μI]
    infer_instance
  have hf : Integrable (Function.uncurry f) (μI.prod P) := by
    simpa [f, μI, P] using
      integrable_uncurry_activeNonpreemptivePriorityResidualWork_stationaryPriorityFiniteWindow
        arrivalRate meanService harrivalRate hmeanService horizon
  have hS : Integrable S P := by
    simpa [S, P] using
      integrable_stationaryPriorityFiniteWindowSquaredResidualWork
        arrivalRate meanService harrivalRate hmeanService hstable hn horizon
  have hR : Integrable R P := by
    simpa [R, P] using integrable_stationaryPriorityTotalPastSquareWorkAggregate
      arrivalRate meanService harrivalRate (horizon : ℝ) (Nat.cast_nonneg horizon)
  have hocc : Integrable (fun omega =>
      ∫ t in (-(horizon : ℝ))..0, f t omega) P := by
    simpa only [μI, intervalIntegral.integral_of_le (neg_nonpos.mpr (Nat.cast_nonneg horizon))]
      using hf.integral_prod_right
  have hle : (-(horizon : ℝ)) ≤ 0 :=
    neg_nonpos.mpr (Nat.cast_nonneg horizon)
  have hfSwap : Integrable (Function.uncurry f)
      ((MeasureTheory.volume.restrict (Set.uIoc (-(horizon : ℝ)) 0)).prod P) := by
    simpa only [μI, Set.uIoc_of_le hle] using hf
  have hproduct : (∫ p : ℝ × (Fin n → StationaryPoissonWorkPath), f p.1 p.2
      ∂μI.prod P) = ∫ omega, (∫ t in (-(horizon : ℝ))..0, f t omega) ∂P := by
    calc
      ∫ p : ℝ × (Fin n → StationaryPoissonWorkPath), f p.1 p.2 ∂μI.prod P =
          ∫ t, (∫ omega, f t omega ∂P) ∂μI :=
        MeasureTheory.integral_prod _ hf
      _ = ∫ t in (-(horizon : ℝ))..0, (∫ omega, f t omega ∂P) := by
        simp only [μI, intervalIntegral.integral_of_le
          (neg_nonpos.mpr (Nat.cast_nonneg horizon))]
      _ = ∫ omega, (∫ t in (-(horizon : ℝ))..0, f t omega) ∂P :=
        MeasureTheory.intervalIntegral_integral_swap hfSwap
  have henergy : ∀ᵐ omega ∂P,
      S omega + 2 * (∫ t in (-(horizon : ℝ))..0, f t omega) = R omega := by
    filter_upwards [ae_all_stationaryPriorityWorkRequirement_positive
      arrivalRate meanService harrivalRate hmeanService] with omega hpositive
    apply stationaryPriorityFiniteWindow_squaredResidualWork_energy_integral_neg_to_zero
      meanService omega (horizon : ℝ) (Nat.cast_nonneg horizon)
    intro job hjob
    rcases (mem_stationaryPriorityArrivalWindowJobs_iff
      meanService omega (-(horizon : ℝ)) 0 job).mp hjob with ⟨i, k, _, hjob⟩
    subst job
    exact hpositive i k
  have hintegral : (∫ omega, S omega +
      2 * (∫ t in (-(horizon : ℝ))..0, f t omega) ∂P) = ∫ omega, R omega ∂P :=
    MeasureTheory.integral_congr_ae henergy
  calc
    (∫ omega, S omega ∂P) +
        2 * (∫ p : ℝ × (Fin n → StationaryPoissonWorkPath), f p.1 p.2 ∂μI.prod P) =
        (∫ omega, S omega ∂P) +
          2 * (∫ omega, (∫ t in (-(horizon : ℝ))..0, f t omega) ∂P) := by
          rw [hproduct]
    _ = ∫ omega, S omega + 2 *
          (∫ t in (-(horizon : ℝ))..0, f t omega) ∂P := by
          symm
          rw [MeasureTheory.integral_add hS (hocc.const_mul 2),
            MeasureTheory.integral_const_mul]
    _ = ∫ omega, R omega ∂P := hintegral
    _ = 2 * (∑ i, arrivalRate i * meanService i ^ 2) * (horizon : ℝ) := by
      simpa [R, P] using integral_stationaryPriorityTotalPastSquareWorkAggregate
        arrivalRate meanService harrivalRate (horizon : ℝ) (Nat.cast_nonneg horizon)

/-- The literal stationary active-residual expectation is the marked-Poisson
second-moment rate.  This follows by dividing the exact finite squared-work
energy balance by the horizon and using the finite-occupation limit. -/
theorem integral_stationaryPriorityRemotePastActiveResidualWork_eq_squareWorkRate
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) (hn : 0 < n) :
    (∫ omega, stationaryPriorityRemotePastActiveResidualWork meanService omega ∂
      Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate) =
      ∑ i, arrivalRate i * meanService i ^ 2 := by
  let P := Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate
  let S : ℕ → ℝ := fun horizon => ∫ omega,
    totalNonpreemptivePrioritySquaredResidualWork
      (stationaryPriorityFiniteWindowState meanService omega (-(horizon : ℝ)) 0) ∂P
  let A : ℕ → ℝ := fun horizon => ∫ p : ℝ × (Fin n → StationaryPoissonWorkPath),
    activeNonpreemptivePriorityResidualWork
      (stationaryPriorityFiniteWindowState meanService p.2 (-(horizon : ℝ)) p.1) ∂
      ((MeasureTheory.volume.restrict (Set.Ioc (-(horizon : ℝ)) 0)).prod P)
  let R : ℝ := ∑ i, arrivalRate i * meanService i ^ 2
  let L : ℝ := ∫ omega, stationaryPriorityRemotePastActiveResidualWork meanService omega ∂P
  have hterminal : Filter.Tendsto (fun horizon : ℕ => S horizon / (horizon : ℝ))
      Filter.atTop (nhds 0) := by
    simpa [S, P] using
      tendsto_integral_stationaryPriorityFiniteWindowSquaredResidualWork_div_natCast
        arrivalRate meanService harrivalRate hmeanService hstable hn
  have hactive : Filter.Tendsto (fun horizon : ℕ => (horizon : ℝ)⁻¹ * A horizon)
      Filter.atTop (nhds L) := by
    simpa [A, L, P] using
      tendsto_natCast_inv_mul_integral_uncurry_activeNonpreemptivePriorityResidualWork_stationaryPriorityFiniteWindow
        arrivalRate meanService harrivalRate hmeanService hstable hn
  have hsum : Filter.Tendsto (fun horizon : ℕ =>
      S horizon / (horizon : ℝ) + 2 * ((horizon : ℝ)⁻¹ * A horizon))
      Filter.atTop (nhds (0 + 2 * L)) :=
    hterminal.add (hactive.const_mul 2)
  have hbalance : (fun horizon : ℕ =>
      S horizon / (horizon : ℝ) + 2 * ((horizon : ℝ)⁻¹ * A horizon)) =ᶠ[Filter.atTop]
      fun _ => 2 * R := by
    filter_upwards [Filter.eventually_ge_atTop 1] with horizon hhorizon
    have hnonzero : (horizon : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt (lt_of_lt_of_le (by norm_num) hhorizon)
    have henergy : S horizon + 2 * A horizon =
        2 * R * (horizon : ℝ) := by
      simpa [S, A, R, P] using
        integral_stationaryPriorityFiniteWindowSquaredResidualWork_add_two_mul_occupation
          arrivalRate meanService harrivalRate hmeanService hstable hn horizon
    calc
      S horizon / (horizon : ℝ) + 2 * ((horizon : ℝ)⁻¹ * A horizon) =
          (S horizon + 2 * A horizon) / (horizon : ℝ) := by
            field_simp [hnonzero]
      _ = (2 * R * (horizon : ℝ)) / (horizon : ℝ) := by rw [henergy]
      _ = 2 * R := by field_simp [hnonzero]
  have hlimit : 0 + 2 * L = 2 * R :=
    tendsto_nhds_unique (hsum.congr' hbalance) tendsto_const_nhds
  dsimp [L, R, P] at hlimit ⊢
  linarith

/-- The priority-filtered waiting work of an empty-start replay over a fixed
past window is jointly integrable in physical observation time and marked
stationary input. -/
theorem integrable_uncurry_priorityWaitingResidualWorkAtLeastAsUrgent_stationaryPriorityFiniteWindow
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (priority : Fin n) (horizon : ℕ) :
    Integrable (fun p : ℝ × (Fin n → StationaryPoissonWorkPath) =>
      priorityWaitingResidualWorkAtLeastAsUrgent
        (stationaryPriorityFiniteWindowState meanService p.2 (-(horizon : ℝ)) p.1) priority)
      ((MeasureTheory.volume.restrict (Set.Ioc (-(horizon : ℝ)) 0)).prod
        (Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate)) := by
  let μI : Measure ℝ := MeasureTheory.volume.restrict (Set.Ioc (-(horizon : ℝ)) 0)
  let P := Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate
  let F : ℝ × (Fin n → StationaryPoissonWorkPath) → ℝ := fun p =>
    priorityWaitingResidualWorkAtLeastAsUrgent
      (stationaryPriorityFiniteWindowState meanService p.2 (-(horizon : ℝ)) p.1) priority
  let G : ℝ × (Fin n → StationaryPoissonWorkPath) → ℝ := fun p =>
    stationaryPriorityTotalPastWorkAggregate meanService p.2 (horizon : ℝ)
  letI : IsProbabilityMeasure P := by
    dsimp [P]
    exact Probability.PoissonProcess.isProbabilityMeasure_multiclassStationaryPoissonWorkMeasure
      arrivalRate harrivalRate
  letI : IsFiniteMeasure μI := by
    dsimp [μI]
    infer_instance
  have hGbase : Integrable (fun omega =>
      stationaryPriorityTotalPastWorkAggregate meanService omega (horizon : ℝ)) P := by
    simpa [P] using integrable_stationaryPriorityTotalPastWorkAggregate
      arrivalRate meanService harrivalRate (horizon : ℝ) (Nat.cast_nonneg horizon)
  have hG : Integrable G (μI.prod P) := by
    simpa [G] using hGbase.comp_snd μI
  have hmeas : AEStronglyMeasurable F (μI.prod P) := by
    exact (measurable_uncurry_stationaryPriorityFiniteWindowAtLeastAsUrgentWaitingWork
      meanService (-(horizon : ℝ)) priority).aestronglyMeasurable
  refine Integrable.mono' hG hmeas ?_
  have htime : ∀ᵐ p : ℝ × (Fin n → StationaryPoissonWorkPath) ∂μI.prod P,
      p.1 ∈ Set.Ioc (-(horizon : ℝ)) 0 := by
    exact (Measure.quasiMeasurePreserving_fst (μ := μI) (ν := P)).ae
      (MeasureTheory.ae_restrict_mem measurableSet_Ioc)
  have hpositive : ∀ᵐ p : ℝ × (Fin n → StationaryPoissonWorkPath) ∂μI.prod P,
      ∀ i k, 0 < stationaryPriorityWorkRequirement meanService i p.2 k := by
    exact (Measure.quasiMeasurePreserving_snd (μ := μI) (ν := P)).ae
      (ae_all_stationaryPriorityWorkRequirement_positive
        arrivalRate meanService harrivalRate hmeanService)
  filter_upwards [htime, hpositive] with p hp hpositive
  have hleft : -(horizon : ℝ) ≤ p.1 := hp.1.le
  have hright : p.1 ≤ 0 := hp.2
  have hwindow : ∀ job ∈ stationaryPriorityArrivalWindowJobs meanService p.2
      (-(horizon : ℝ)) 0, 0 < job.serviceWork := by
    intro job hjob
    rcases (mem_stationaryPriorityArrivalWindowJobs_iff
      meanService p.2 (-(horizon : ℝ)) 0 job).mp hjob with ⟨i, k, _, hjob⟩
    subst job
    exact hpositive i k
  have hprefix : ∀ job ∈ stationaryPriorityArrivalWindowJobs meanService p.2
      (-(horizon : ℝ)) p.1, 0 ≤ job.serviceWork := by
    intro job hjob
    exact (hwindow job (by
      rw [stationaryPriorityArrivalWindowJobs_append
        meanService p.2 (-(horizon : ℝ)) p.1 0 hleft hright]
      exact List.mem_append_left _ hjob)).le
  let state := stationaryPriorityFiniteWindowState meanService p.2 (-(horizon : ℝ)) p.1
  have hstate : nonnegativeNonpreemptivePriorityResidualWork state := by
    exact nonnegativeNonpreemptivePriorityResidualWork_stationaryPriorityFiniteWindowState
      meanService p.2 (-(horizon : ℝ)) p.1 hprefix
  have hwaitingNonnegative : 0 ≤ F p := by
    dsimp [F, state]
    exact priorityWaitingResidualWorkAtLeastAsUrgent_nonneg _ hstate priority
  rw [Real.norm_of_nonneg hwaitingNonnegative]
  calc
    F p = priorityWaitingResidualWorkAtLeastAsUrgent state priority := rfl
    _ ≤ totalNonpreemptivePriorityResidualWork state :=
      priorityWaitingResidualWorkAtLeastAsUrgent_le_total state hstate priority
    _ ≤ stationaryPriorityArrivalWindowTotalWork meanService p.2 (-(horizon : ℝ)) 0 :=
      totalResidualWork_stationaryPriorityFiniteWindowState_le_windowTotalWork_of_le
        meanService p.2 (-(horizon : ℝ)) p.1 0 hleft hright hwindow
    _ = G p := by
      exact stationaryPriorityArrivalWindowTotalWork_neg_to_zero
        meanService p.2 (horizon : ℝ)

/-- Reindexing a finite-window priority-filtered waiting occupation by the
stationary input flow turns it into the interval integral of the expected
empty-start waiting work over its elapsed past horizon. -/
theorem integral_uncurry_priorityWaitingResidualWorkAtLeastAsUrgent_stationaryPriorityFiniteWindow_eq_intervalIntegral
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (priority : Fin n) (horizon : ℕ) :
    (∫ p : ℝ × (Fin n → StationaryPoissonWorkPath),
      priorityWaitingResidualWorkAtLeastAsUrgent
        (stationaryPriorityFiniteWindowState meanService p.2 (-(horizon : ℝ)) p.1) priority ∂
        ((MeasureTheory.volume.restrict (Set.Ioc (-(horizon : ℝ)) 0)).prod
          (Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate))) =
      ∫ u in 0..(horizon : ℝ), ∫ omega,
        priorityWaitingResidualWorkAtLeastAsUrgent
          (stationaryPriorityFiniteWindowState meanService omega (-u) 0) priority ∂
          Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate := by
  let μI : Measure ℝ := MeasureTheory.volume.restrict (Set.Ioc (-(horizon : ℝ)) 0)
  let P := Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate
  let A : ℝ → (Fin n → StationaryPoissonWorkPath) → ℝ := fun t omega =>
    priorityWaitingResidualWorkAtLeastAsUrgent
      (stationaryPriorityFiniteWindowState meanService omega (-(horizon : ℝ)) t) priority
  let F : ℝ → (Fin n → StationaryPoissonWorkPath) → ℝ := fun u omega =>
    priorityWaitingResidualWorkAtLeastAsUrgent
      (stationaryPriorityFiniteWindowState meanService omega (-u) 0) priority
  letI : IsProbabilityMeasure P := by
    dsimp [P]
    exact Probability.PoissonProcess.isProbabilityMeasure_multiclassStationaryPoissonWorkMeasure
      arrivalRate harrivalRate
  letI : IsFiniteMeasure μI := by
    dsimp [μI]
    infer_instance
  have hA : Integrable (Function.uncurry A) (μI.prod P) := by
    simpa [A, μI, P] using
      integrable_uncurry_priorityWaitingResidualWorkAtLeastAsUrgent_stationaryPriorityFiniteWindow
        arrivalRate meanService harrivalRate hmeanService priority horizon
  have htime : ∀ t : ℝ,
      (∫ omega, A t omega ∂P) = ∫ omega, F (t + (horizon : ℝ)) omega ∂P := by
    intro t
    have hshift : ∀ᵐ omega ∂P,
        F (t + (horizon : ℝ))
          (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow t omega) =
          A t omega := by
      change ∀ᵐ omega ∂P,
        priorityWaitingResidualWorkAtLeastAsUrgent
          (stationaryPriorityFiniteWindowState meanService
            (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow t omega)
            (-(t + (horizon : ℝ))) 0) priority =
          priorityWaitingResidualWorkAtLeastAsUrgent
            (stationaryPriorityFiniteWindowState meanService omega (-(horizon : ℝ)) t) priority
      convert
        (ae_priorityWaitingResidualWorkAtLeastAsUrgent_stationaryPriorityFiniteWindow_flow
          arrivalRate meanService harrivalRate t (-(horizon : ℝ)) t priority) using 1 <;> ring_nf
    calc
      (∫ omega, A t omega ∂P) =
          ∫ omega, F (t + (horizon : ℝ))
            (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow t omega) ∂P := by
              symm
              exact MeasureTheory.integral_congr_ae hshift
      _ = ∫ omega, F (t + (horizon : ℝ)) omega ∂P := by
        simpa [P, Function.comp_def] using
          (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow_measurePreserving
            arrivalRate harrivalRate t).hasLaw.integral_comp
              (f := F (t + (horizon : ℝ)))
              (stationaryPriorityFiniteWindowAtLeastAsUrgentWaitingWork_hasLaw_canonicalPast
                arrivalRate meanService harrivalRate priority (t + (horizon : ℝ))).aemeasurable.aestronglyMeasurable
  calc
    ∫ p : ℝ × (Fin n → StationaryPoissonWorkPath), A p.1 p.2 ∂μI.prod P =
        ∫ t, (∫ omega, A t omega ∂P) ∂μI :=
      MeasureTheory.integral_prod _ hA
    _ = ∫ t in (-(horizon : ℝ))..0, (∫ omega, A t omega ∂P) := by
      simp only [μI, intervalIntegral.integral_of_le
        (neg_nonpos.mpr (Nat.cast_nonneg horizon))]
    _ = ∫ t in (-(horizon : ℝ))..0, (∫ omega,
        F (t + (horizon : ℝ)) omega ∂P) := by
      apply intervalIntegral.integral_congr
      intro t ht
      exact htime t
    _ = ∫ u in 0..(horizon : ℝ), (∫ omega, F u omega ∂P) := by
      simpa only [neg_add_cancel, zero_add] using
        (intervalIntegral.integral_comp_add_right
          (f := fun u => ∫ omega, F u omega ∂P)
          (a := -(horizon : ℝ)) (b := 0) (horizon : ℝ))

/-- The expected empty-start priority-filtered waiting work is
interval-integrable on every finite nonnegative horizon. -/
theorem intervalIntegrable_expected_priorityWaitingResidualWorkAtLeastAsUrgent_stationaryPriorityFiniteWindow
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (priority : Fin n) (horizon : ℕ) :
    IntervalIntegrable (fun u : ℝ => ∫ omega,
      priorityWaitingResidualWorkAtLeastAsUrgent
        (stationaryPriorityFiniteWindowState meanService omega (-u) 0) priority ∂
        Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate)
      MeasureTheory.volume 0 (horizon : ℝ) := by
  let μI : Measure ℝ := MeasureTheory.volume.restrict (Set.Ioc (-(horizon : ℝ)) 0)
  let P := Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate
  let A : ℝ → (Fin n → StationaryPoissonWorkPath) → ℝ := fun t omega =>
    priorityWaitingResidualWorkAtLeastAsUrgent
      (stationaryPriorityFiniteWindowState meanService omega (-(horizon : ℝ)) t) priority
  let F : ℝ → (Fin n → StationaryPoissonWorkPath) → ℝ := fun u omega =>
    priorityWaitingResidualWorkAtLeastAsUrgent
      (stationaryPriorityFiniteWindowState meanService omega (-u) 0) priority
  letI : IsProbabilityMeasure P := by
    dsimp [P]
    exact Probability.PoissonProcess.isProbabilityMeasure_multiclassStationaryPoissonWorkMeasure
      arrivalRate harrivalRate
  letI : IsFiniteMeasure μI := by
    dsimp [μI]
    infer_instance
  have hA : Integrable (Function.uncurry A) (μI.prod P) := by
    simpa [A, μI, P] using
      integrable_uncurry_priorityWaitingResidualWorkAtLeastAsUrgent_stationaryPriorityFiniteWindow
        arrivalRate meanService harrivalRate hmeanService priority horizon
  have htime : ∀ t : ℝ,
      (∫ omega, A t omega ∂P) = ∫ omega, F (t + (horizon : ℝ)) omega ∂P := by
    intro t
    have hshift : ∀ᵐ omega ∂P,
        F (t + (horizon : ℝ))
          (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow t omega) =
          A t omega := by
      change ∀ᵐ omega ∂P,
        priorityWaitingResidualWorkAtLeastAsUrgent
          (stationaryPriorityFiniteWindowState meanService
            (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow t omega)
            (-(t + (horizon : ℝ))) 0) priority =
          priorityWaitingResidualWorkAtLeastAsUrgent
            (stationaryPriorityFiniteWindowState meanService omega (-(horizon : ℝ)) t) priority
      convert
        (ae_priorityWaitingResidualWorkAtLeastAsUrgent_stationaryPriorityFiniteWindow_flow
          arrivalRate meanService harrivalRate t (-(horizon : ℝ)) t priority) using 1 <;> ring_nf
    calc
      (∫ omega, A t omega ∂P) =
          ∫ omega, F (t + (horizon : ℝ))
            (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow t omega) ∂P := by
              symm
              exact MeasureTheory.integral_congr_ae hshift
      _ = ∫ omega, F (t + (horizon : ℝ)) omega ∂P := by
        simpa [P, Function.comp_def] using
          (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow_measurePreserving
            arrivalRate harrivalRate t).hasLaw.integral_comp
              (f := F (t + (horizon : ℝ)))
              (stationaryPriorityFiniteWindowAtLeastAsUrgentWaitingWork_hasLaw_canonicalPast
                arrivalRate meanService harrivalRate priority (t + (horizon : ℝ))).aemeasurable.aestronglyMeasurable
  have hAintegral : Integrable (fun t => ∫ omega, A t omega ∂P) μI :=
    hA.integral_prod_left
  have hAinterval : IntervalIntegrable (fun t => ∫ omega, A t omega ∂P)
      MeasureTheory.volume (-(horizon : ℝ)) 0 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le
      (neg_nonpos.mpr (Nat.cast_nonneg horizon))]
    simpa [μI] using hAintegral
  have hshifted : IntervalIntegrable (fun t => ∫ omega,
      F (t + (horizon : ℝ)) omega ∂P)
      MeasureTheory.volume (-(horizon : ℝ)) 0 := by
    apply hAinterval.congr
    intro t ht
    exact htime t
  simpa [F, P] using
    (IntervalIntegrable.comp_add_right_iff
      (f := fun u => ∫ omega, F u omega ∂P)
      (a := -(horizon : ℝ)) (b := 0) (c := (horizon : ℝ))).mp hshifted

/-- The normalized priority-filtered waiting occupation of an empty-start
finite stationary replay converges to the expectation of the corresponding
literal remote-past waiting workload. -/
theorem tendsto_natCast_inv_mul_integral_uncurry_priorityWaitingResidualWorkAtLeastAsUrgent_stationaryPriorityFiniteWindow
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) (hn : 0 < n)
    (priority : Fin n) :
    Filter.Tendsto (fun horizon : ℕ => (horizon : ℝ)⁻¹ *
      (∫ p : ℝ × (Fin n → StationaryPoissonWorkPath),
        priorityWaitingResidualWorkAtLeastAsUrgent
          (stationaryPriorityFiniteWindowState meanService p.2 (-(horizon : ℝ)) p.1) priority ∂
          ((MeasureTheory.volume.restrict (Set.Ioc (-(horizon : ℝ)) 0)).prod
            (Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate))))
      Filter.atTop
      (nhds (∫ omega,
        stationaryPriorityRemotePastAtLeastAsUrgentWaitingWork meanService priority omega ∂
          Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate)) := by
  let f : ℝ → ℝ := fun u => ∫ omega,
    priorityWaitingResidualWorkAtLeastAsUrgent
      (stationaryPriorityFiniteWindowState meanService omega (-u) 0) priority ∂
      Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate
  have hcesaro : Filter.Tendsto (fun horizon : ℕ => (horizon : ℝ)⁻¹ *
      ∫ u in 0..(horizon : ℝ), f u) Filter.atTop
      (nhds (∫ omega,
        stationaryPriorityRemotePastAtLeastAsUrgentWaitingWork meanService priority omega ∂
          Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate)) :=
    tendsto_natCast_inv_mul_intervalIntegral_zero_of_tendsto
      (fun horizon => by
        simpa [f] using
          intervalIntegrable_expected_priorityWaitingResidualWorkAtLeastAsUrgent_stationaryPriorityFiniteWindow
            arrivalRate meanService harrivalRate hmeanService priority horizon)
      (by
        simpa [f] using
          tendsto_integral_priorityWaitingResidualWorkAtLeastAsUrgent_stationaryPriorityFiniteWindowState_real
            arrivalRate meanService harrivalRate hmeanService hstable hn priority)
  apply hcesaro.congr'
  filter_upwards with horizon
  rw [integral_uncurry_priorityWaitingResidualWorkAtLeastAsUrgent_stationaryPriorityFiniteWindow_eq_intervalIntegral
    arrivalRate meanService harrivalRate hmeanService priority horizon]

end

end AppliedModelingLib.Queueing
