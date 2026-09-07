import AppliedModelingLib.Foundations.Probability.StationaryPoissonWorkPastRate

/-!
# Future marked-work rate for stationary Poisson suspension input

This module proves the forward counterpart of the stationary marked-Poisson
past-work law.  It identifies literal work in `(0, t]` with the residual and
future equilibrium renewal coordinates and transports the marked-renewal
strong law.  It is an input-process result only: no queue state or response
claim is made here.
-/

namespace AppliedModelingLib.Probability.Queueing

open MeasureTheory ProbabilityTheory Filter Finset
open PoissonProcess
open scoped Topology ProbabilityTheory

noncomputable section

/-- Total literal work of stationary marked-Poisson arrivals in `(0, t]`. -/
def stationaryPoissonWorkFutureAggregate
    (z : GoodSuspensionState × (ℤ → ℝ)) (t : ℝ) : ℝ :=
  (suspensionBaseArrivalIndicesRightClosed 0 t z.1).sum
    (stationaryPoissonWorkRequirement z)

/-- Reindex an integer work-mark path by the equilibrium forward enumeration.
The first coordinate is the first arrival strictly after the deterministic
origin. -/
def equilibriumForwardWorkPath (work : ℤ → ℝ) : ℕ → ℝ :=
  fun n => twoSidedGap (Int.ofNat (n + 1)) work

/-- The equilibrium-coordinate marked work accumulated in the canonical
future renewal window. -/
def equilibriumMarkedFutureWork
    (z : ((ℕ → ℝ) × (ℕ → ℝ)) × (ℤ → ℝ)) (t : ℝ) : ℝ :=
  canonicalMarkedWork (equilibriumFuturePath z.1) (equilibriumForwardWorkPath z.2) t

theorem measurable_equilibriumForwardWorkPath :
    Measurable equilibriumForwardWorkPath := by
  refine measurable_pi_iff.2 fun n => ?_
  exact measurable_twoSidedGap (Int.ofNat (n + 1))

/-- The equilibrium forward reindexing of an iid two-sided unit-exponential
work path is again a canonical iid unit-exponential path. -/
theorem equilibriumForwardWorkPath_measurePreserving :
    MeasurePreserving equilibriumForwardWorkPath
      (twoSidedInterarrivalMeasure (1 : ℝ))
      (exponentialInterarrivalMeasure (1 : ℝ)) := by
  refine ⟨measurable_equilibriumForwardWorkPath, ?_⟩
  letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure (1 : ℝ)) :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure (by norm_num)
  change Measure.map
    (fun work n => twoSidedGap (Int.ofNat (n + 1)) work)
    (twoSidedInterarrivalMeasure (1 : ℝ)) =
      exponentialInterarrivalMeasure (1 : ℝ)
  rw [ProbabilityTheory.iIndepFun_iff_map_fun_eq_infinitePi_map
    (fun n => measurable_twoSidedGap (Int.ofNat (n + 1))) |>.mp]
  · simp only [exponentialInterarrivalMeasure]
    congr 1
    funext n
    exact (twoSidedGap_hasLaw (by norm_num : 0 < (1 : ℝ))
      (Int.ofNat (n + 1))).map_eq
  · exact ProbabilityTheory.iIndepFun.precomp
      (g := fun n : ℕ => Int.ofNat (n + 1))
      (by
        intro a b hab
        exact Nat.add_right_cancel (Int.ofNat.inj hab))
      (iIndepFun_twoSidedGap (by norm_num : 0 < (1 : ℝ)))

/-- In the equilibrium marked product carrier, the residual-and-future
arrival path is a canonical rate-`rate` exponential renewal path. -/
theorem equilibriumFuturePath_fst_measurePreserving
    {rate : ℝ} (hrate : 0 < rate) :
    MeasurePreserving
      (fun z : ((ℕ → ℝ) × (ℕ → ℝ)) × (ℤ → ℝ) => equilibriumFuturePath z.1)
      ((equilibriumTwoSidedBaseMeasure rate).prod
        (twoSidedInterarrivalMeasure (1 : ℝ)))
      (exponentialInterarrivalMeasure rate) := by
  let μ : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure rate
  let ν : Measure (ℤ → ℝ) := twoSidedInterarrivalMeasure (1 : ℝ)
  letI : IsProbabilityMeasure μ :=
    isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  letI : IsProbabilityMeasure ν :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure (by norm_num)
  have hfst : MeasurePreserving
      (Prod.fst : ((ℕ → ℝ) × (ℕ → ℝ)) × (ℤ → ℝ) → (ℕ → ℝ) × (ℕ → ℝ))
      ((μ.prod μ).prod ν) (μ.prod μ) :=
    measurePreserving_fst
  have hhead : MeasurePreserving
      (Prod.fst : (ℕ → ℝ) × (ℕ → ℝ) → ℕ → ℝ) (μ.prod μ) μ :=
    measurePreserving_fst
  simpa [μ, ν, equilibriumTwoSidedBaseMeasure, equilibriumFuturePath,
    Function.comp_def] using hhead.comp hfst

/-- The equilibrium residual-and-future arrival coordinate itself has the
canonical rate-`rate` renewal law. -/
theorem equilibriumFuturePath_measurePreserving
    {rate : ℝ} (hrate : 0 < rate) :
    MeasurePreserving equilibriumFuturePath
      (equilibriumTwoSidedBaseMeasure rate)
      (exponentialInterarrivalMeasure rate) := by
  let μ : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure rate
  letI : IsProbabilityMeasure μ :=
    isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  simpa [μ, equilibriumTwoSidedBaseMeasure, equilibriumFuturePath] using
    (measurePreserving_fst : MeasurePreserving Prod.fst (μ.prod μ) μ)

/-- In the equilibrium marked product carrier, the labelled future work path
has the canonical iid unit-exponential law. -/
theorem equilibriumForwardWorkPath_snd_measurePreserving
    {rate : ℝ} (hrate : 0 < rate) :
    MeasurePreserving
      (fun z : ((ℕ → ℝ) × (ℕ → ℝ)) × (ℤ → ℝ) =>
        equilibriumForwardWorkPath z.2)
      ((equilibriumTwoSidedBaseMeasure rate).prod
        (twoSidedInterarrivalMeasure (1 : ℝ)))
      (exponentialInterarrivalMeasure (1 : ℝ)) := by
  let μ : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure rate
  let ν : Measure (ℤ → ℝ) := twoSidedInterarrivalMeasure (1 : ℝ)
  letI : IsProbabilityMeasure μ :=
    isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  letI : IsProbabilityMeasure ν :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure (by norm_num)
  have hsnd : MeasurePreserving
      (Prod.snd : ((ℕ → ℝ) × (ℕ → ℝ)) × (ℤ → ℝ) → ℤ → ℝ)
      ((μ.prod μ).prod ν) ν :=
    measurePreserving_snd
  simpa [μ, ν, equilibriumTwoSidedBaseMeasure, Function.comp_def] using
    equilibriumForwardWorkPath_measurePreserving.comp hsnd

/-- The joint canonical input obtained from the equilibrium future arrival
coordinate and its independent future work-mark path. -/
def equilibriumFutureMarkedInput
    (z : ((ℕ → ℝ) × (ℕ → ℝ)) × (ℤ → ℝ)) : (ℕ → ℝ) × (ℕ → ℝ) :=
  (equilibriumFuturePath z.1, equilibriumForwardWorkPath z.2)

/-- The joint equilibrium future input preserves the independent canonical
arrival-and-mark product law. -/
theorem equilibriumFutureMarkedInput_measurePreserving
    {rate : ℝ} (hrate : 0 < rate) :
    MeasurePreserving equilibriumFutureMarkedInput
      ((equilibriumTwoSidedBaseMeasure rate).prod
        (twoSidedInterarrivalMeasure (1 : ℝ)))
      ((exponentialInterarrivalMeasure rate).prod
        (exponentialInterarrivalMeasure (1 : ℝ))) := by
  letI : IsProbabilityMeasure (equilibriumTwoSidedBaseMeasure rate) :=
    isProbabilityMeasure_equilibriumTwoSidedBaseMeasure hrate
  letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure (1 : ℝ)) :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure (by norm_num)
  simpa [equilibriumFutureMarkedInput] using
    (equilibriumFuturePath_measurePreserving hrate).prod
      equilibriumForwardWorkPath_measurePreserving

/-- Equilibrium marked future work is Borel measurable. -/
theorem measurable_equilibriumMarkedFutureWork (t : ℝ) :
    Measurable (fun z : ((ℕ → ℝ) × (ℕ → ℝ)) × (ℤ → ℝ) =>
      equilibriumMarkedFutureWork z t) := by
  have harrival : Measurable (fun z : ((ℕ → ℝ) × (ℕ → ℝ)) × (ℤ → ℝ) =>
      equilibriumFuturePath z.1) := by
    simpa [equilibriumFuturePath] using
      ((measurable_fst : Measurable (fun p : (ℕ → ℝ) × (ℕ → ℝ) => p.1)).comp
        (measurable_fst : Measurable
          (fun z : ((ℕ → ℝ) × (ℕ → ℝ)) × (ℤ → ℝ) => z.1)))
  have hwork : Measurable (fun z : ((ℕ → ℝ) × (ℕ → ℝ)) × (ℤ → ℝ) =>
      equilibriumForwardWorkPath z.2) :=
    measurable_equilibriumForwardWorkPath.comp measurable_snd
  simpa [equilibriumMarkedFutureWork] using
    (measurable_canonicalMarkedWork t).comp (harrival.prodMk hwork)

/-- Equilibrium finite-horizon marked future work is integrable. -/
theorem integrable_equilibriumMarkedFutureWork
    {rate t : ℝ} (hrate : 0 < rate) (ht : 0 ≤ t) :
    Integrable (fun z : ((ℕ → ℝ) × (ℕ → ℝ)) × (ℤ → ℝ) =>
      equilibriumMarkedFutureWork z t)
      ((equilibriumTwoSidedBaseMeasure rate).prod
        (twoSidedInterarrivalMeasure (1 : ℝ))) := by
  letI : IsProbabilityMeasure (equilibriumTwoSidedBaseMeasure rate) :=
    isProbabilityMeasure_equilibriumTwoSidedBaseMeasure hrate
  letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure (1 : ℝ)) :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure (by norm_num)
  simpa [equilibriumMarkedFutureWork, equilibriumFutureMarkedInput,
    Function.comp_def] using
    ((equilibriumFutureMarkedInput_measurePreserving hrate).integrable_comp
      (measurable_canonicalMarkedWork t).aestronglyMeasurable).mpr
      (integrable_canonicalMarkedWork hrate ht)

/-- The expected equilibrium marked future work over `(0,t]` is `rate * t`. -/
theorem integral_equilibriumMarkedFutureWork
    {rate t : ℝ} (hrate : 0 < rate) (ht : 0 ≤ t) :
    ∫ z : ((ℕ → ℝ) × (ℕ → ℝ)) × (ℤ → ℝ), equilibriumMarkedFutureWork z t
      ∂((equilibriumTwoSidedBaseMeasure rate).prod
        (twoSidedInterarrivalMeasure (1 : ℝ))) = rate * t := by
  letI : IsProbabilityMeasure (equilibriumTwoSidedBaseMeasure rate) :=
    isProbabilityMeasure_equilibriumTwoSidedBaseMeasure hrate
  letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure (1 : ℝ)) :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure (by norm_num)
  simpa [equilibriumMarkedFutureWork, equilibriumFutureMarkedInput,
    Function.comp_def] using
    (equilibriumFutureMarkedInput_measurePreserving hrate).hasLaw.integral_comp
      (f := fun y : (ℕ → ℝ) × (ℕ → ℝ) => canonicalMarkedWork y.1 y.2 t)
      (measurable_canonicalMarkedWork t).aestronglyMeasurable |>.trans
      (integral_canonicalMarkedWork hrate ht)

/-- The finite equilibrium future enumerator is exactly the canonical marked
renewal sum under its displayed forward reindexing. -/
theorem equilibriumMarkedFutureWork_eq_forwardArrivalSum
    (z : ((ℕ → ℝ) × (ℕ → ℝ)) × (ℤ → ℝ)) (t : ℝ) :
    equilibriumMarkedFutureWork z t =
      (equilibriumForwardArrivalIndices t z.1).sum (fun i => z.2 i) := by
  unfold equilibriumMarkedFutureWork canonicalMarkedWork
  rw [equilibriumForwardArrivalIndices, Finset.sum_image]
  · rfl
  · intro m _ n _ hmn
    exact Nat.add_right_cancel (Int.ofNat.inj hmn)

/-- The literal stationary future work ledger agrees almost surely with the
equilibrium-coordinate marked future sum at each fixed horizon. -/
theorem ae_stationaryPoissonWorkFutureAggregate_eq_equilibriumMarkedFutureWork
    {rate : ℝ} (hrate : 0 < rate) (t : ℝ) :
    ∀ᵐ z ∂stationaryPoissonWorkMeasure rate,
      stationaryPoissonWorkFutureAggregate z t =
        equilibriumMarkedFutureWork (stationaryPoissonWorkToEquilibrium z) t := by
  let μe : Measure ((ℕ → ℝ) × (ℕ → ℝ)) := equilibriumTwoSidedBaseMeasure rate
  let μw : Measure (ℤ → ℝ) := twoSidedInterarrivalMeasure (1 : ℝ)
  letI : IsProbabilityMeasure μe :=
    isProbabilityMeasure_equilibriumTwoSidedBaseMeasure hrate
  letI : IsProbabilityMeasure μw :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure (by norm_num)
  have henum : ∀ᵐ y ∂μe.prod μw, ∀ u : ℝ, ∀ i : ℤ,
      i ∈ equilibriumForwardArrivalIndices u y.1 ↔
        0 < equilibriumBaseArrival y.1 i ∧ equilibriumBaseArrival y.1 i ≤ u := by
    refine ae_of_ae_map (μ := μe.prod μw) (f := Prod.fst)
      (p := fun omega : (ℕ → ℝ) × (ℕ → ℝ) => ∀ u : ℝ, ∀ i : ℤ,
        i ∈ equilibriumForwardArrivalIndices u omega ↔
          0 < equilibriumBaseArrival omega i ∧ equilibriumBaseArrival omega i ≤ u)
      measurable_fst.aemeasurable ?_
    rw [Measure.map_fst_prod, measure_univ, one_smul]
    exact ae_all_mem_equilibriumForwardArrivalIndices_iff hrate
  have hlift : ∀ᵐ z ∂stationaryPoissonWorkMeasure rate, ∀ u : ℝ, ∀ i : ℤ,
      i ∈ equilibriumForwardArrivalIndices u (stationaryPoissonWorkToEquilibrium z).1 ↔
        0 < equilibriumBaseArrival (stationaryPoissonWorkToEquilibrium z).1 i ∧
          equilibriumBaseArrival (stationaryPoissonWorkToEquilibrium z).1 i ≤ u := by
    refine ae_of_ae_map (μ := stationaryPoissonWorkMeasure rate)
      (f := stationaryPoissonWorkToEquilibrium)
      (p := fun y : ((ℕ → ℝ) × (ℕ → ℝ)) × (ℤ → ℝ) => ∀ u : ℝ, ∀ i : ℤ,
        i ∈ equilibriumForwardArrivalIndices u y.1 ↔
          0 < equilibriumBaseArrival y.1 i ∧ equilibriumBaseArrival y.1 i ≤ u)
      measurable_stationaryPoissonWorkToEquilibrium.aemeasurable ?_
    rw [(stationaryPoissonWorkToEquilibrium_measurePreserving hrate).map_eq]
    simpa [μe, μw] using henum
  filter_upwards [hlift] with z henum_z
  have hindices :
      suspensionBaseArrivalIndicesRightClosed 0 t z.1 =
        equilibriumForwardArrivalIndices t (stationaryPoissonWorkToEquilibrium z).1 := by
    ext i
    change i ∈ suspensionBaseArrivalIndicesRightClosed 0 t z.1 ↔
      i ∈ equilibriumForwardArrivalIndices t (suspensionToEquilibrium z.1.1)
    calc
      i ∈ suspensionBaseArrivalIndicesRightClosed 0 t z.1 ↔
          0 < suspensionBaseArrival z.1 i ∧ suspensionBaseArrival z.1 i ≤ t :=
        mem_suspensionBaseArrivalIndicesRightClosed_iff 0 t z.1 i
      _ ↔ 0 < equilibriumBaseArrival (suspensionToEquilibrium z.1.1) i ∧
          equilibriumBaseArrival (suspensionToEquilibrium z.1.1) i ≤ t := by
            change (0 < candidatePalmArrival z.1.1.1 i - z.1.1.2 ∧
              candidatePalmArrival z.1.1.1 i - z.1.1.2 ≤ t) ↔
              0 < equilibriumBaseArrival (suspensionToEquilibrium z.1.1) i ∧
                equilibriumBaseArrival (suspensionToEquilibrium z.1.1) i ≤ t
            rw [equilibriumBaseArrival_suspensionToEquilibrium]
      _ ↔ i ∈ equilibriumForwardArrivalIndices t
          (suspensionToEquilibrium z.1.1) := (henum_z t i).symm
  rw [stationaryPoissonWorkFutureAggregate, hindices]
  symm
  simpa [stationaryPoissonWorkToEquilibrium, stationaryPoissonWorkRequirement] using
    (equilibriumMarkedFutureWork_eq_forwardArrivalSum
      (stationaryPoissonWorkToEquilibrium z) t)

/-- Literal stationary future work is integrable at each deterministic
horizon. -/
theorem integrable_stationaryPoissonWorkFutureAggregate
    {rate t : ℝ} (hrate : 0 < rate) (ht : 0 ≤ t) :
    Integrable (fun z => stationaryPoissonWorkFutureAggregate z t)
      (stationaryPoissonWorkMeasure rate) := by
  letI : IsProbabilityMeasure (stationaryPoissonWorkMeasure rate) :=
    isProbabilityMeasure_stationaryPoissonWorkMeasure hrate
  have hequilibrium : Integrable (fun z =>
      equilibriumMarkedFutureWork (stationaryPoissonWorkToEquilibrium z) t)
      (stationaryPoissonWorkMeasure rate) := by
    simpa [Function.comp_def] using
      ((stationaryPoissonWorkToEquilibrium_measurePreserving hrate).integrable_comp
        (measurable_equilibriumMarkedFutureWork t).aestronglyMeasurable).mpr
        (integrable_equilibriumMarkedFutureWork hrate ht)
  refine hequilibrium.congr ?_
  filter_upwards [ae_stationaryPoissonWorkFutureAggregate_eq_equilibriumMarkedFutureWork
    hrate t] with z hz
  exact hz.symm

/-- The expected literal stationary marked-Poisson work arriving in `(0,t]`
is `rate * t`. -/
theorem integral_stationaryPoissonWorkFutureAggregate
    {rate t : ℝ} (hrate : 0 < rate) (ht : 0 ≤ t) :
    ∫ z, stationaryPoissonWorkFutureAggregate z t ∂stationaryPoissonWorkMeasure rate =
      rate * t := by
  calc
    ∫ z, stationaryPoissonWorkFutureAggregate z t ∂stationaryPoissonWorkMeasure rate =
        ∫ z, equilibriumMarkedFutureWork (stationaryPoissonWorkToEquilibrium z) t
          ∂stationaryPoissonWorkMeasure rate := by
            refine MeasureTheory.integral_congr_ae ?_
            exact ae_stationaryPoissonWorkFutureAggregate_eq_equilibriumMarkedFutureWork
              hrate t
    _ = ∫ y, equilibriumMarkedFutureWork y t
          ∂((equilibriumTwoSidedBaseMeasure rate).prod
            (twoSidedInterarrivalMeasure (1 : ℝ))) := by
            simpa [Function.comp_def] using
              (stationaryPoissonWorkToEquilibrium_measurePreserving hrate).hasLaw.integral_comp
                (f := fun y => equilibriumMarkedFutureWork y t)
                (measurable_equilibriumMarkedFutureWork t).aestronglyMeasurable
    _ = rate * t := integral_equilibriumMarkedFutureWork hrate ht

/-- Under the explicit equilibrium arrival coordinate and independent work
path, canonical future-window work has almost-sure rate `rate`. -/
theorem ae_tendsto_equilibriumMarkedFutureWork_div_atTop
    {rate : ℝ} (hrate : 0 < rate) :
    ∀ᵐ z ∂((equilibriumTwoSidedBaseMeasure rate).prod
      (twoSidedInterarrivalMeasure (1 : ℝ))),
      Tendsto (fun t : ℝ => equilibriumMarkedFutureWork z t / t)
        atTop (nhds rate) := by
  simpa only [equilibriumMarkedFutureWork] using
    (ae_tendsto_canonicalMarkedWork_div_atTop_of_marginal_measurePreserving hrate
      (fun z : ((ℕ → ℝ) × (ℕ → ℝ)) × (ℤ → ℝ) => equilibriumFuturePath z.1)
      (fun z : ((ℕ → ℝ) × (ℕ → ℝ)) × (ℤ → ℝ) =>
        equilibriumForwardWorkPath z.2)
      (equilibriumFuturePath_fst_measurePreserving hrate)
      (equilibriumForwardWorkPath_snd_measurePreserving hrate))

/-- The literal work aggregate of stationary marked-Poisson arrivals in
`(0,t]`, divided by elapsed time, converges almost surely to the arrival
rate.  This uses the actual stationary suspension and its labelled iid marks. -/
theorem ae_tendsto_stationaryPoissonWorkFutureAggregate_div_atTop
    {rate : ℝ} (hrate : 0 < rate) :
    ∀ᵐ z ∂stationaryPoissonWorkMeasure rate,
      Tendsto (fun t : ℝ => stationaryPoissonWorkFutureAggregate z t / t)
        atTop (nhds rate) := by
  let μe : Measure ((ℕ → ℝ) × (ℕ → ℝ)) := equilibriumTwoSidedBaseMeasure rate
  let μw : Measure (ℤ → ℝ) := twoSidedInterarrivalMeasure (1 : ℝ)
  letI : IsProbabilityMeasure μe :=
    isProbabilityMeasure_equilibriumTwoSidedBaseMeasure hrate
  letI : IsProbabilityMeasure μw :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure (by norm_num)
  have henum : ∀ᵐ z ∂μe.prod μw, ∀ t : ℝ, ∀ i : ℤ,
      i ∈ equilibriumForwardArrivalIndices t z.1 ↔
        0 < equilibriumBaseArrival z.1 i ∧ equilibriumBaseArrival z.1 i ≤ t := by
    refine ae_of_ae_map (μ := μe.prod μw) (f := Prod.fst)
      (p := fun ω : (ℕ → ℝ) × (ℕ → ℝ) => ∀ t : ℝ, ∀ i : ℤ,
        i ∈ equilibriumForwardArrivalIndices t ω ↔
          0 < equilibriumBaseArrival ω i ∧ equilibriumBaseArrival ω i ≤ t)
      measurable_fst.aemeasurable ?_
    rw [Measure.map_fst_prod, measure_univ, one_smul]
    exact ae_all_mem_equilibriumForwardArrivalIndices_iff hrate
  have htarget : ∀ᵐ z ∂μe.prod μw,
      Tendsto (fun t : ℝ => equilibriumMarkedFutureWork z t / t)
        atTop (nhds rate) ∧
      (∀ t : ℝ, ∀ i : ℤ,
        i ∈ equilibriumForwardArrivalIndices t z.1 ↔
          0 < equilibriumBaseArrival z.1 i ∧ equilibriumBaseArrival z.1 i ≤ t) := by
    filter_upwards [ae_tendsto_equilibriumMarkedFutureWork_div_atTop hrate, henum]
      with z hwork henum_z
    exact ⟨hwork, henum_z⟩
  have hlift : ∀ᵐ z ∂stationaryPoissonWorkMeasure rate,
      Tendsto (fun t : ℝ =>
        equilibriumMarkedFutureWork (stationaryPoissonWorkToEquilibrium z) t / t)
          atTop (nhds rate) ∧
      (∀ t : ℝ, ∀ i : ℤ,
        i ∈ equilibriumForwardArrivalIndices t
          (stationaryPoissonWorkToEquilibrium z).1 ↔
          0 < equilibriumBaseArrival (stationaryPoissonWorkToEquilibrium z).1 i ∧
            equilibriumBaseArrival (stationaryPoissonWorkToEquilibrium z).1 i ≤ t) := by
    refine ae_of_ae_map (μ := stationaryPoissonWorkMeasure rate)
      (f := stationaryPoissonWorkToEquilibrium)
      (p := fun z : ((ℕ → ℝ) × (ℕ → ℝ)) × (ℤ → ℝ) =>
        Tendsto (fun t : ℝ => equilibriumMarkedFutureWork z t / t)
          atTop (nhds rate) ∧
        (∀ t : ℝ, ∀ i : ℤ,
          i ∈ equilibriumForwardArrivalIndices t z.1 ↔
            0 < equilibriumBaseArrival z.1 i ∧ equilibriumBaseArrival z.1 i ≤ t))
      measurable_stationaryPoissonWorkToEquilibrium.aemeasurable ?_
    rw [(stationaryPoissonWorkToEquilibrium_measurePreserving hrate).map_eq]
    exact htarget
  filter_upwards [hlift] with z hz
  rcases hz with ⟨hwork, henum_z⟩
  refine hwork.congr' ?_
  refine Filter.Eventually.of_forall fun t => ?_
  have hindices :
      suspensionBaseArrivalIndicesRightClosed 0 t z.1 =
        equilibriumForwardArrivalIndices t
          (stationaryPoissonWorkToEquilibrium z).1 := by
    ext i
    change i ∈ suspensionBaseArrivalIndicesRightClosed 0 t z.1 ↔
      i ∈ equilibriumForwardArrivalIndices t (suspensionToEquilibrium z.1.1)
    calc
      i ∈ suspensionBaseArrivalIndicesRightClosed 0 t z.1 ↔
          0 < suspensionBaseArrival z.1 i ∧ suspensionBaseArrival z.1 i ≤ t :=
        mem_suspensionBaseArrivalIndicesRightClosed_iff 0 t z.1 i
      _ ↔ 0 < equilibriumBaseArrival (suspensionToEquilibrium z.1.1) i ∧
          equilibriumBaseArrival (suspensionToEquilibrium z.1.1) i ≤ t := by
        change (0 < candidatePalmArrival z.1.1.1 i - z.1.1.2 ∧
            candidatePalmArrival z.1.1.1 i - z.1.1.2 ≤ t) ↔
          0 < equilibriumBaseArrival (suspensionToEquilibrium z.1.1) i ∧
            equilibriumBaseArrival (suspensionToEquilibrium z.1.1) i ≤ t
        rw [equilibriumBaseArrival_suspensionToEquilibrium]
      _ ↔ i ∈ equilibriumForwardArrivalIndices t
          (suspensionToEquilibrium z.1.1) := by
        exact (henum_z t i).symm
  have hsum : stationaryPoissonWorkFutureAggregate z t =
      equilibriumMarkedFutureWork (stationaryPoissonWorkToEquilibrium z) t := by
    rw [stationaryPoissonWorkFutureAggregate, hindices]
    symm
    simpa [stationaryPoissonWorkToEquilibrium, stationaryPoissonWorkRequirement] using
      (equilibriumMarkedFutureWork_eq_forwardArrivalSum
        (stationaryPoissonWorkToEquilibrium z) t)
  change equilibriumMarkedFutureWork (stationaryPoissonWorkToEquilibrium z) t / t =
    stationaryPoissonWorkFutureAggregate z t / t
  exact congrArg (fun x : ℝ => x / t) hsum.symm

end

end AppliedModelingLib.Probability.Queueing
