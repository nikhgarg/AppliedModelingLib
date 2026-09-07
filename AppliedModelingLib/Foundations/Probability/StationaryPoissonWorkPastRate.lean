import AppliedModelingLib.Foundations.Probability.PoissonSuspensionWorkMarks
import AppliedModelingLib.Foundations.Probability.PoissonSuspensionCampbellBridge
import AppliedModelingLib.Foundations.Probability.ExponentialMarkedRenewalWorkRate
import Mathlib.Tactic

/-!
# Past marked-work rate for stationary Poisson suspension input

This module proves an input-process law only.  It identifies the literal
work marks of arrivals in `[-t, 0)` in the stationary marked Poisson
suspension and transports the canonical marked-renewal strong law to that
source coordinate.  It does not define a queue, a service discipline, a
reset, or a stationary workload.
-/

namespace AppliedModelingLib.Probability.Queueing

open MeasureTheory ProbabilityTheory Filter Finset
open PoissonProcess
open scoped Topology ProbabilityTheory

noncomputable section

/-- Total literal work of stationary marked-Poisson arrivals in `[-t, 0)`. -/
def stationaryPoissonWorkPastAggregate
    (z : GoodSuspensionState × (ℤ → ℝ)) (t : ℝ) : ℝ :=
  (suspensionBaseArrivalIndices (-t) 0 z.1).sum
    (stationaryPoissonWorkRequirement z)

/-- Reindex an integer work-mark path by the equilibrium past enumeration.
The first coordinate is the last arrival before the deterministic origin. -/
def equilibriumBackwardWorkPath (work : ℤ → ℝ) : ℕ → ℝ :=
  fun n => twoSidedGap (equilibriumBackwardArrivalIndex n) work

/-- The equilibrium-coordinate marked work accumulated in the canonical past
renewal window. -/
def equilibriumMarkedPastWork
    (z : ((ℕ → ℝ) × (ℕ → ℝ)) × (ℤ → ℝ)) (t : ℝ) : ℝ :=
  canonicalMarkedWork (equilibriumPastPath z.1) (equilibriumBackwardWorkPath z.2) t

/-- The deterministic coordinate map from the stationary marked suspension to
the origin-split equilibrium arrival coordinate, retaining the same labelled
work-mark path. -/
def stationaryPoissonWorkToEquilibrium :
    (GoodSuspensionState × (ℤ → ℝ)) → ((ℕ → ℝ) × (ℕ → ℝ)) × (ℤ → ℝ) :=
  fun z => (suspensionToEquilibrium z.1.1, z.2)

theorem measurable_equilibriumBackwardWorkPath :
    Measurable equilibriumBackwardWorkPath := by
  refine measurable_pi_iff.2 fun n => ?_
  exact measurable_twoSidedGap (equilibriumBackwardArrivalIndex n)

theorem measurable_stationaryPoissonWorkToEquilibrium :
    Measurable stationaryPoissonWorkToEquilibrium := by
  exact
    (measurable_suspensionToEquilibrium.comp
      (measurable_subtype_coe.comp measurable_fst)).prodMk measurable_snd

/-- The equilibrium past reindexing of an iid two-sided unit-exponential
work path is again a canonical iid unit-exponential path. -/
theorem equilibriumBackwardWorkPath_measurePreserving :
    MeasurePreserving equilibriumBackwardWorkPath
      (twoSidedInterarrivalMeasure (1 : ℝ))
      (exponentialInterarrivalMeasure (1 : ℝ)) := by
  refine ⟨measurable_equilibriumBackwardWorkPath, ?_⟩
  letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure (1 : ℝ)) :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure (by norm_num)
  change Measure.map
    (fun work n => twoSidedGap (equilibriumBackwardArrivalIndex n) work)
    (twoSidedInterarrivalMeasure (1 : ℝ)) =
      exponentialInterarrivalMeasure (1 : ℝ)
  rw [ProbabilityTheory.iIndepFun_iff_map_fun_eq_infinitePi_map
    (fun n => measurable_twoSidedGap (equilibriumBackwardArrivalIndex n)) |>.mp]
  · simp only [exponentialInterarrivalMeasure]
    congr 1
    funext n
    exact (twoSidedGap_hasLaw (by norm_num : 0 < (1 : ℝ))
      (equilibriumBackwardArrivalIndex n)).map_eq
  · exact ProbabilityTheory.iIndepFun.precomp
      (g := equilibriumBackwardArrivalIndex)
      equilibriumBackwardArrivalIndex_injective
      (iIndepFun_twoSidedGap (by norm_num : 0 < (1 : ℝ)))

/-- The finite equilibrium past enumerator is exactly the canonical marked
renewal sum under its displayed reindexing. -/
theorem equilibriumMarkedPastWork_eq_backwardArrivalSum
    (z : ((ℕ → ℝ) × (ℕ → ℝ)) × (ℤ → ℝ)) (t : ℝ) :
    equilibriumMarkedPastWork z t =
      (equilibriumBackwardArrivalIndices t z.1).sum (fun i => z.2 i) := by
  unfold equilibriumMarkedPastWork canonicalMarkedWork
  rw [equilibriumBackwardArrivalIndices, Finset.sum_image]
  · rfl
  · intro m hm n hn hmn
    exact equilibriumBackwardArrivalIndex_injective hmn

/-- In the equilibrium marked product carrier, the age-and-past arrival path
is a canonical rate-`rate` exponential renewal path. -/
theorem equilibriumPastPath_fst_measurePreserving
    {rate : ℝ} (hrate : 0 < rate) :
    MeasurePreserving
      (fun z : ((ℕ → ℝ) × (ℕ → ℝ)) × (ℤ → ℝ) => equilibriumPastPath z.1)
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
  have hsnd : MeasurePreserving
      (Prod.snd : (ℕ → ℝ) × (ℕ → ℝ) → (ℕ → ℝ))
      (μ.prod μ) μ :=
    measurePreserving_snd
  simpa [μ, ν, equilibriumTwoSidedBaseMeasure, equilibriumPastPath,
    Function.comp_def] using hsnd.comp hfst

/-- In the equilibrium marked product carrier, the labelled past work path
has the canonical iid unit-exponential law. -/
theorem equilibriumBackwardWorkPath_snd_measurePreserving
    {rate : ℝ} (hrate : 0 < rate) :
    MeasurePreserving
      (fun z : ((ℕ → ℝ) × (ℕ → ℝ)) × (ℤ → ℝ) =>
        equilibriumBackwardWorkPath z.2)
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
      (Prod.snd : ((ℕ → ℝ) × (ℕ → ℝ)) × (ℤ → ℝ) → (ℤ → ℝ))
      ((μ.prod μ).prod ν) ν :=
    measurePreserving_snd
  simpa [μ, ν, equilibriumTwoSidedBaseMeasure, Function.comp_def] using
    equilibriumBackwardWorkPath_measurePreserving.comp hsnd

/-- The joint canonical input obtained from the equilibrium past-arrival
coordinate and its independent backward work-mark path. -/
def equilibriumPastMarkedInput
    (z : ((ℕ → ℝ) × (ℕ → ℝ)) × (ℤ → ℝ)) : (ℕ → ℝ) × (ℕ → ℝ) :=
  (equilibriumPastPath z.1, equilibriumBackwardWorkPath z.2)

/-- The equilibrium past input preserves the independent canonical
arrival-and-mark product law. -/
theorem equilibriumPastMarkedInput_measurePreserving
    {rate : ℝ} (hrate : 0 < rate) :
    MeasurePreserving equilibriumPastMarkedInput
      ((equilibriumTwoSidedBaseMeasure rate).prod
        (twoSidedInterarrivalMeasure (1 : ℝ)))
      ((exponentialInterarrivalMeasure rate).prod
        (exponentialInterarrivalMeasure (1 : ℝ))) := by
  letI : IsProbabilityMeasure (equilibriumTwoSidedBaseMeasure rate) :=
    isProbabilityMeasure_equilibriumTwoSidedBaseMeasure hrate
  letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure (1 : ℝ)) :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure (by norm_num)
  let μ : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure rate
  letI : IsProbabilityMeasure μ :=
    isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  have hbase : MeasurePreserving equilibriumPastPath
      (equilibriumTwoSidedBaseMeasure rate) μ := by
    simpa [μ, equilibriumTwoSidedBaseMeasure, equilibriumPastPath] using
      (measurePreserving_snd : MeasurePreserving Prod.snd (μ.prod μ) μ)
  simpa [equilibriumPastMarkedInput] using
    hbase.prod
      equilibriumBackwardWorkPath_measurePreserving

/-- Equilibrium finite-horizon marked past work is Borel measurable. -/
theorem measurable_equilibriumMarkedPastWork (t : ℝ) :
    Measurable (fun z : ((ℕ → ℝ) × (ℕ → ℝ)) × (ℤ → ℝ) =>
      equilibriumMarkedPastWork z t) := by
  have harrival : Measurable (fun z : ((ℕ → ℝ) × (ℕ → ℝ)) × (ℤ → ℝ) =>
      equilibriumPastPath z.1) := by
    simpa [equilibriumPastPath] using
      ((measurable_snd : Measurable (fun p : (ℕ → ℝ) × (ℕ → ℝ) => p.2)).comp
        (measurable_fst : Measurable
          (fun z : ((ℕ → ℝ) × (ℕ → ℝ)) × (ℤ → ℝ) => z.1)))
  have hwork : Measurable (fun z : ((ℕ → ℝ) × (ℕ → ℝ)) × (ℤ → ℝ) =>
      equilibriumBackwardWorkPath z.2) :=
    measurable_equilibriumBackwardWorkPath.comp measurable_snd
  simpa [equilibriumMarkedPastWork] using
    (measurable_canonicalMarkedWork t).comp (harrival.prodMk hwork)

/-- Equilibrium finite-horizon marked past work is integrable. -/
theorem integrable_equilibriumMarkedPastWork
    {rate t : ℝ} (hrate : 0 < rate) (ht : 0 ≤ t) :
    Integrable (fun z : ((ℕ → ℝ) × (ℕ → ℝ)) × (ℤ → ℝ) =>
      equilibriumMarkedPastWork z t)
      ((equilibriumTwoSidedBaseMeasure rate).prod
        (twoSidedInterarrivalMeasure (1 : ℝ))) := by
  letI : IsProbabilityMeasure (equilibriumTwoSidedBaseMeasure rate) :=
    isProbabilityMeasure_equilibriumTwoSidedBaseMeasure hrate
  letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure (1 : ℝ)) :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure (by norm_num)
  simpa [equilibriumMarkedPastWork, equilibriumPastMarkedInput,
    Function.comp_def] using
    ((equilibriumPastMarkedInput_measurePreserving hrate).integrable_comp
      (measurable_canonicalMarkedWork t).aestronglyMeasurable).mpr
      (integrable_canonicalMarkedWork hrate ht)

/-- The expected equilibrium marked past work over `[-t,0)` is
`rate * t`. -/
theorem integral_equilibriumMarkedPastWork
    {rate t : ℝ} (hrate : 0 < rate) (ht : 0 ≤ t) :
    ∫ z : ((ℕ → ℝ) × (ℕ → ℝ)) × (ℤ → ℝ), equilibriumMarkedPastWork z t
      ∂((equilibriumTwoSidedBaseMeasure rate).prod
        (twoSidedInterarrivalMeasure (1 : ℝ))) = rate * t := by
  letI : IsProbabilityMeasure (equilibriumTwoSidedBaseMeasure rate) :=
    isProbabilityMeasure_equilibriumTwoSidedBaseMeasure hrate
  letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure (1 : ℝ)) :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure (by norm_num)
  simpa [equilibriumMarkedPastWork, equilibriumPastMarkedInput,
    Function.comp_def] using
    (equilibriumPastMarkedInput_measurePreserving hrate).hasLaw.integral_comp
      (f := fun y : (ℕ → ℝ) × (ℕ → ℝ) => canonicalMarkedWork y.1 y.2 t)
      (measurable_canonicalMarkedWork t).aestronglyMeasurable |>.trans
      (integral_canonicalMarkedWork hrate ht)

/-- The stationary marked suspension transports to the equilibrium
origin-split arrival coordinate while retaining its independent labelled work
path. -/
theorem stationaryPoissonWorkToEquilibrium_measurePreserving
    {rate : ℝ} (hrate : 0 < rate) :
    MeasurePreserving stationaryPoissonWorkToEquilibrium
      (stationaryPoissonWorkMeasure rate)
      ((equilibriumTwoSidedBaseMeasure rate).prod
        (twoSidedInterarrivalMeasure (1 : ℝ))) := by
  let μg : Measure GoodSuspensionState := goodSuspensionMeasure rate
  let μw : Measure (ℤ → ℝ) := twoSidedInterarrivalMeasure (1 : ℝ)
  letI : IsProbabilityMeasure μg := isProbabilityMeasure_goodSuspensionMeasure hrate
  letI : IsProbabilityMeasure μw :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure (by norm_num)
  have hbaseMap :
      Measure.map (fun p : GoodSuspensionState => suspensionToEquilibrium p.1) μg =
        equilibriumTwoSidedBaseMeasure rate := by
    calc
      Measure.map (fun p : GoodSuspensionState => suspensionToEquilibrium p.1) μg =
          Measure.map suspensionToEquilibrium
            (Measure.map (Subtype.val : GoodSuspensionState → ((ℤ → ℝ) × ℝ)) μg) := by
            symm
            simpa only [Function.comp_apply] using
              (Measure.map_map (μ := μg) measurable_suspensionToEquilibrium
                measurable_subtype_coe)
      _ = Measure.map suspensionToEquilibrium (suspensionMeasure rate) := by
            rw [map_goodSuspensionMeasure_subtype_val hrate]
      _ = equilibriumTwoSidedBaseMeasure rate :=
            hasSuspensionEquilibriumBridge hrate
  have hbase : MeasurePreserving
      (fun p : GoodSuspensionState => suspensionToEquilibrium p.1) μg
      (equilibriumTwoSidedBaseMeasure rate) :=
    ⟨measurable_suspensionToEquilibrium.comp measurable_subtype_coe, hbaseMap⟩
  simpa [stationaryPoissonWorkMeasure, timedEmbeddedSuspensionProductMeasure,
    stationaryPoissonWorkToEquilibrium, μg, μw] using
    hbase.prod (MeasurePreserving.id μw)

/-- Under the explicit equilibrium arrival coordinate and independent work
path, canonical past-window work has almost-sure rate `rate`. -/
theorem ae_tendsto_equilibriumMarkedPastWork_div_atTop
    {rate : ℝ} (hrate : 0 < rate) :
    ∀ᵐ z ∂((equilibriumTwoSidedBaseMeasure rate).prod
      (twoSidedInterarrivalMeasure (1 : ℝ))),
      Tendsto (fun t : ℝ => equilibriumMarkedPastWork z t / t)
        atTop (nhds rate) := by
  simpa only [equilibriumMarkedPastWork] using
    (ae_tendsto_canonicalMarkedWork_div_atTop_of_marginal_measurePreserving hrate
      (fun z : ((ℕ → ℝ) × (ℕ → ℝ)) × (ℤ → ℝ) => equilibriumPastPath z.1)
      (fun z : ((ℕ → ℝ) × (ℕ → ℝ)) × (ℤ → ℝ) =>
        equilibriumBackwardWorkPath z.2)
      (equilibriumPastPath_fst_measurePreserving hrate)
      (equilibriumBackwardWorkPath_snd_measurePreserving hrate))

/-- The equilibrium backward enumerator has its literal `[-t, 0)` meaning
simultaneously for every finite time on one full-measure event.  The
all-times form is needed to transfer a `Tendsto` statement, rather than only
a collection of fixed-time equalities. -/
theorem ae_all_mem_equilibriumBackwardArrivalIndices_iff
    {rate : ℝ} (hrate : 0 < rate) :
    ∀ᵐ ω ∂equilibriumTwoSidedBaseMeasure rate, ∀ t : ℝ, ∀ i : ℤ,
      i ∈ equilibriumBackwardArrivalIndices t ω ↔
        -t ≤ equilibriumBaseArrival ω i ∧ equilibriumBaseArrival ω i < 0 := by
  let μ := exponentialInterarrivalMeasure rate
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  have hpastCount : ∀ᵐ ω : (ℕ → ℝ) × (ℕ → ℝ) ∂μ.prod μ,
      ∀ u : ℝ, ∀ n : ℕ,
        n < canonicalRenewalCount u ω.2 ↔ arrivalTime n ω.2 ≤ u := by
    refine ae_of_ae_map (μ := μ.prod μ) (f := Prod.snd)
      (p := fun ξ : ℕ → ℝ => ∀ u : ℝ, ∀ n : ℕ,
        n < canonicalRenewalCount u ξ ↔ arrivalTime n ξ ≤ u)
      measurable_snd.aemeasurable ?_
    rw [Measure.map_snd_prod, measure_univ, one_smul]
    exact ae_lt_canonicalRenewalCount_iff_arrivalTime_le hrate
  have hfuture : ∀ᵐ ω : (ℕ → ℝ) × (ℕ → ℝ) ∂μ.prod μ,
      ∀ n : ℕ, 0 < interarrival n ω.1 := by
    refine ae_of_ae_map (μ := μ.prod μ) (f := Prod.fst)
      (p := fun ξ : ℕ → ℝ => ∀ n : ℕ, 0 < interarrival n ξ)
      measurable_fst.aemeasurable ?_
    rw [Measure.map_fst_prod, measure_univ, one_smul]
    exact ae_all_interarrival_positive hrate
  have hpast : ∀ᵐ ω : (ℕ → ℝ) × (ℕ → ℝ) ∂μ.prod μ,
      ∀ n : ℕ, 0 < interarrival n ω.2 := by
    refine ae_of_ae_map (μ := μ.prod μ) (f := Prod.snd)
      (p := fun ξ : ℕ → ℝ => ∀ n : ℕ, 0 < interarrival n ξ)
      measurable_snd.aemeasurable ?_
    rw [Measure.map_snd_prod, measure_univ, one_smul]
    exact ae_all_interarrival_positive hrate
  filter_upwards [hpastCount, hfuture, hpast] with ω hcount hfuture hpast
  intro t i
  constructor
  · intro hi
    obtain ⟨n, hn, rfl⟩ :=
      (mem_equilibriumBackwardArrivalIndices_iff t ω i).mp hi
    have htime : arrivalTime n ω.2 ≤ t := (hcount t n).mp hn
    constructor
    · rw [equilibriumBaseArrival_backwardIndex]
      exact neg_le_neg htime
    · rw [equilibriumBaseArrival_backwardIndex]
      apply neg_lt_zero.mpr
      exact lt_of_lt_of_le (by simpa [arrivalTime_zero] using hpast 0)
        ((arrivalTime_strictMono_of_positive ω.2 hpast).monotone (Nat.zero_le n))
  · rintro ⟨hle, hneg⟩
    cases i with
    | ofNat m =>
        cases m with
        | zero =>
            apply (mem_equilibriumBackwardArrivalIndices_iff t ω 0).mpr
            refine ⟨0, ?_, rfl⟩
            apply (hcount t 0).mpr
            change -t ≤ equilibriumBaseArrival ω 0 at hle
            rw [equilibriumBaseArrival_zero] at hle
            change -t ≤ -interarrival 0 ω.2 at hle
            simpa [arrivalTime_zero] using (neg_le_neg_iff.mp hle)
        | succ n =>
            rw [equilibriumBaseArrival_ofNat_succ] at hneg
            have hpos : 0 < arrivalTime n ω.1 :=
              lt_of_lt_of_le (by simpa [arrivalTime_zero] using hfuture 0)
                ((arrivalTime_strictMono_of_positive ω.1 hfuture).monotone (Nat.zero_le n))
            exact (not_lt_of_ge hpos.le hneg).elim
    | negSucc n =>
        apply (mem_equilibriumBackwardArrivalIndices_iff t ω (Int.negSucc n)).mpr
        refine ⟨n + 1, ?_, by simp [equilibriumBackwardArrivalIndex]⟩
        apply (hcount t (n + 1)).mpr
        rw [equilibriumBaseArrival_negSucc] at hle
        exact neg_le_neg_iff.mp hle

/-- At every fixed horizon, the literal stationary strict-past index set is
almost surely the equilibrium backward index set under the suspension-to-
equilibrium coordinate map.  This is a finite-ledger statement, separate from
any particular aggregate formed from the selected arrivals. -/
theorem ae_stationaryPoissonWorkPastIndices_eq_equilibriumBackwardArrivalIndices
    {rate : ℝ} (hrate : 0 < rate) (t : ℝ) :
    ∀ᵐ z ∂stationaryPoissonWorkMeasure rate,
      suspensionBaseArrivalIndices (-t) 0 z.1 =
        equilibriumBackwardArrivalIndices t
          (stationaryPoissonWorkToEquilibrium z).1 := by
  let μe : Measure ((ℕ → ℝ) × (ℕ → ℝ)) := equilibriumTwoSidedBaseMeasure rate
  let μw : Measure (ℤ → ℝ) := twoSidedInterarrivalMeasure (1 : ℝ)
  letI : IsProbabilityMeasure μe :=
    isProbabilityMeasure_equilibriumTwoSidedBaseMeasure hrate
  letI : IsProbabilityMeasure μw :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure (by norm_num)
  have henum : ∀ᵐ y ∂μe.prod μw, ∀ u : ℝ, ∀ i : ℤ,
      i ∈ equilibriumBackwardArrivalIndices u y.1 ↔
        -u ≤ equilibriumBaseArrival y.1 i ∧ equilibriumBaseArrival y.1 i < 0 := by
    refine ae_of_ae_map (μ := μe.prod μw) (f := Prod.fst)
      (p := fun omega : (ℕ → ℝ) × (ℕ → ℝ) => ∀ u : ℝ, ∀ i : ℤ,
        i ∈ equilibriumBackwardArrivalIndices u omega ↔
          -u ≤ equilibriumBaseArrival omega i ∧ equilibriumBaseArrival omega i < 0)
      measurable_fst.aemeasurable ?_
    rw [Measure.map_fst_prod, measure_univ, one_smul]
    exact ae_all_mem_equilibriumBackwardArrivalIndices_iff hrate
  have hlift : ∀ᵐ z ∂stationaryPoissonWorkMeasure rate, ∀ u : ℝ, ∀ i : ℤ,
      i ∈ equilibriumBackwardArrivalIndices u (stationaryPoissonWorkToEquilibrium z).1 ↔
        -u ≤ equilibriumBaseArrival (stationaryPoissonWorkToEquilibrium z).1 i ∧
          equilibriumBaseArrival (stationaryPoissonWorkToEquilibrium z).1 i < 0 := by
    refine ae_of_ae_map (μ := stationaryPoissonWorkMeasure rate)
      (f := stationaryPoissonWorkToEquilibrium)
      (p := fun y : ((ℕ → ℝ) × (ℕ → ℝ)) × (ℤ → ℝ) => ∀ u : ℝ, ∀ i : ℤ,
        i ∈ equilibriumBackwardArrivalIndices u y.1 ↔
          -u ≤ equilibriumBaseArrival y.1 i ∧ equilibriumBaseArrival y.1 i < 0)
      measurable_stationaryPoissonWorkToEquilibrium.aemeasurable ?_
    rw [(stationaryPoissonWorkToEquilibrium_measurePreserving hrate).map_eq]
    simpa [μe, μw] using henum
  filter_upwards [hlift] with z henum_z
  ext i
  change i ∈ suspensionBaseArrivalIndices (-t) 0 z.1 ↔
    i ∈ equilibriumBackwardArrivalIndices t (suspensionToEquilibrium z.1.1)
  calc
    i ∈ suspensionBaseArrivalIndices (-t) 0 z.1 ↔
        -t ≤ suspensionBaseArrival z.1 i ∧ suspensionBaseArrival z.1 i < 0 :=
      mem_suspensionBaseArrivalIndices_iff (-t) 0 z.1 i
    _ ↔ -t ≤ equilibriumBaseArrival (suspensionToEquilibrium z.1.1) i ∧
        equilibriumBaseArrival (suspensionToEquilibrium z.1.1) i < 0 := by
      change (-t ≤ candidatePalmArrival z.1.1.1 i - z.1.1.2 ∧
          candidatePalmArrival z.1.1.1 i - z.1.1.2 < 0) ↔
        -t ≤ equilibriumBaseArrival (suspensionToEquilibrium z.1.1) i ∧
          equilibriumBaseArrival (suspensionToEquilibrium z.1.1) i < 0
      rw [equilibriumBaseArrival_suspensionToEquilibrium]
    _ ↔ i ∈ equilibriumBackwardArrivalIndices t
        (suspensionToEquilibrium z.1.1) := (henum_z t i).symm

/-- The literal stationary past-work ledger agrees almost surely with its
equilibrium-coordinate marked-renewal representation at each fixed horizon. -/
theorem ae_stationaryPoissonWorkPastAggregate_eq_equilibriumMarkedPastWork
    {rate : ℝ} (hrate : 0 < rate) (t : ℝ) :
    ∀ᵐ z ∂stationaryPoissonWorkMeasure rate,
      stationaryPoissonWorkPastAggregate z t =
        equilibriumMarkedPastWork (stationaryPoissonWorkToEquilibrium z) t := by
  let μe : Measure ((ℕ → ℝ) × (ℕ → ℝ)) := equilibriumTwoSidedBaseMeasure rate
  let μw : Measure (ℤ → ℝ) := twoSidedInterarrivalMeasure (1 : ℝ)
  letI : IsProbabilityMeasure μe :=
    isProbabilityMeasure_equilibriumTwoSidedBaseMeasure hrate
  letI : IsProbabilityMeasure μw :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure (by norm_num)
  have henum : ∀ᵐ y ∂μe.prod μw, ∀ u : ℝ, ∀ i : ℤ,
      i ∈ equilibriumBackwardArrivalIndices u y.1 ↔
        -u ≤ equilibriumBaseArrival y.1 i ∧ equilibriumBaseArrival y.1 i < 0 := by
    refine ae_of_ae_map (μ := μe.prod μw) (f := Prod.fst)
      (p := fun omega : (ℕ → ℝ) × (ℕ → ℝ) => ∀ u : ℝ, ∀ i : ℤ,
        i ∈ equilibriumBackwardArrivalIndices u omega ↔
          -u ≤ equilibriumBaseArrival omega i ∧ equilibriumBaseArrival omega i < 0)
      measurable_fst.aemeasurable ?_
    rw [Measure.map_fst_prod, measure_univ, one_smul]
    exact ae_all_mem_equilibriumBackwardArrivalIndices_iff hrate
  have hlift : ∀ᵐ z ∂stationaryPoissonWorkMeasure rate, ∀ u : ℝ, ∀ i : ℤ,
      i ∈ equilibriumBackwardArrivalIndices u (stationaryPoissonWorkToEquilibrium z).1 ↔
        -u ≤ equilibriumBaseArrival (stationaryPoissonWorkToEquilibrium z).1 i ∧
          equilibriumBaseArrival (stationaryPoissonWorkToEquilibrium z).1 i < 0 := by
    refine ae_of_ae_map (μ := stationaryPoissonWorkMeasure rate)
      (f := stationaryPoissonWorkToEquilibrium)
      (p := fun y : ((ℕ → ℝ) × (ℕ → ℝ)) × (ℤ → ℝ) => ∀ u : ℝ, ∀ i : ℤ,
        i ∈ equilibriumBackwardArrivalIndices u y.1 ↔
          -u ≤ equilibriumBaseArrival y.1 i ∧ equilibriumBaseArrival y.1 i < 0)
      measurable_stationaryPoissonWorkToEquilibrium.aemeasurable ?_
    rw [(stationaryPoissonWorkToEquilibrium_measurePreserving hrate).map_eq]
    simpa [μe, μw] using henum
  filter_upwards [hlift] with z henum_z
  have hindices :
      suspensionBaseArrivalIndices (-t) 0 z.1 =
        equilibriumBackwardArrivalIndices t
          (stationaryPoissonWorkToEquilibrium z).1 := by
    ext i
    change i ∈ suspensionBaseArrivalIndices (-t) 0 z.1 ↔
      i ∈ equilibriumBackwardArrivalIndices t (suspensionToEquilibrium z.1.1)
    calc
      i ∈ suspensionBaseArrivalIndices (-t) 0 z.1 ↔
          -t ≤ suspensionBaseArrival z.1 i ∧ suspensionBaseArrival z.1 i < 0 :=
        mem_suspensionBaseArrivalIndices_iff (-t) 0 z.1 i
      _ ↔ -t ≤ equilibriumBaseArrival (suspensionToEquilibrium z.1.1) i ∧
          equilibriumBaseArrival (suspensionToEquilibrium z.1.1) i < 0 := by
        change (-t ≤ candidatePalmArrival z.1.1.1 i - z.1.1.2 ∧
            candidatePalmArrival z.1.1.1 i - z.1.1.2 < 0) ↔
          -t ≤ equilibriumBaseArrival (suspensionToEquilibrium z.1.1) i ∧
            equilibriumBaseArrival (suspensionToEquilibrium z.1.1) i < 0
        rw [equilibriumBaseArrival_suspensionToEquilibrium]
      _ ↔ i ∈ equilibriumBackwardArrivalIndices t
          (suspensionToEquilibrium z.1.1) := by
        exact (henum_z t i).symm
  rw [stationaryPoissonWorkPastAggregate, hindices]
  symm
  simpa [stationaryPoissonWorkToEquilibrium, stationaryPoissonWorkRequirement] using
    (equilibriumMarkedPastWork_eq_backwardArrivalSum
      (stationaryPoissonWorkToEquilibrium z) t)

/-- Literal stationary past work is integrable at each deterministic horizon. -/
theorem integrable_stationaryPoissonWorkPastAggregate
    {rate t : ℝ} (hrate : 0 < rate) (ht : 0 ≤ t) :
    Integrable (fun z => stationaryPoissonWorkPastAggregate z t)
      (stationaryPoissonWorkMeasure rate) := by
  letI : IsProbabilityMeasure (stationaryPoissonWorkMeasure rate) :=
    isProbabilityMeasure_stationaryPoissonWorkMeasure hrate
  have hequilibrium : Integrable (fun z =>
      equilibriumMarkedPastWork (stationaryPoissonWorkToEquilibrium z) t)
      (stationaryPoissonWorkMeasure rate) := by
    simpa [Function.comp_def] using
      ((stationaryPoissonWorkToEquilibrium_measurePreserving hrate).integrable_comp
        (measurable_equilibriumMarkedPastWork t).aestronglyMeasurable).mpr
        (integrable_equilibriumMarkedPastWork hrate ht)
  refine hequilibrium.congr ?_
  filter_upwards [ae_stationaryPoissonWorkPastAggregate_eq_equilibriumMarkedPastWork
    hrate t] with z hz
  exact hz.symm

/-- The expected literal stationary marked-Poisson work arriving in `[-t,0)`
is `rate * t`. -/
theorem integral_stationaryPoissonWorkPastAggregate
    {rate t : ℝ} (hrate : 0 < rate) (ht : 0 ≤ t) :
    ∫ z, stationaryPoissonWorkPastAggregate z t ∂stationaryPoissonWorkMeasure rate =
      rate * t := by
  calc
    ∫ z, stationaryPoissonWorkPastAggregate z t ∂stationaryPoissonWorkMeasure rate =
        ∫ z, equilibriumMarkedPastWork (stationaryPoissonWorkToEquilibrium z) t
          ∂stationaryPoissonWorkMeasure rate := by
            refine MeasureTheory.integral_congr_ae ?_
            exact ae_stationaryPoissonWorkPastAggregate_eq_equilibriumMarkedPastWork
              hrate t
    _ = ∫ y, equilibriumMarkedPastWork y t
          ∂((equilibriumTwoSidedBaseMeasure rate).prod
            (twoSidedInterarrivalMeasure (1 : ℝ))) := by
            simpa [Function.comp_def] using
              (stationaryPoissonWorkToEquilibrium_measurePreserving hrate).hasLaw.integral_comp
                (f := fun y => equilibriumMarkedPastWork y t)
                (measurable_equilibriumMarkedPastWork t).aestronglyMeasurable
    _ = rate * t := integral_equilibriumMarkedPastWork hrate ht

/-- The literal work aggregate of stationary marked-Poisson arrivals in
`[-t, 0)`, divided by elapsed time, converges almost surely to the arrival
rate.  This is a source-input statement: it uses the real stationary
suspension coordinates and their actual labelled iid work marks. -/
theorem ae_tendsto_stationaryPoissonWorkPastAggregate_div_atTop
    {rate : ℝ} (hrate : 0 < rate) :
    ∀ᵐ z ∂stationaryPoissonWorkMeasure rate,
      Tendsto (fun t : ℝ => stationaryPoissonWorkPastAggregate z t / t)
        atTop (nhds rate) := by
  let μe : Measure ((ℕ → ℝ) × (ℕ → ℝ)) := equilibriumTwoSidedBaseMeasure rate
  let μw : Measure (ℤ → ℝ) := twoSidedInterarrivalMeasure (1 : ℝ)
  letI : IsProbabilityMeasure μe :=
    isProbabilityMeasure_equilibriumTwoSidedBaseMeasure hrate
  letI : IsProbabilityMeasure μw :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure (by norm_num)
  have henum : ∀ᵐ z ∂μe.prod μw, ∀ t : ℝ, ∀ i : ℤ,
      i ∈ equilibriumBackwardArrivalIndices t z.1 ↔
        -t ≤ equilibriumBaseArrival z.1 i ∧ equilibriumBaseArrival z.1 i < 0 := by
    refine ae_of_ae_map (μ := μe.prod μw) (f := Prod.fst)
      (p := fun ω : (ℕ → ℝ) × (ℕ → ℝ) => ∀ t : ℝ, ∀ i : ℤ,
        i ∈ equilibriumBackwardArrivalIndices t ω ↔
          -t ≤ equilibriumBaseArrival ω i ∧ equilibriumBaseArrival ω i < 0)
      measurable_fst.aemeasurable ?_
    rw [Measure.map_fst_prod, measure_univ, one_smul]
    exact ae_all_mem_equilibriumBackwardArrivalIndices_iff hrate
  have htarget : ∀ᵐ z ∂μe.prod μw,
      Tendsto (fun t : ℝ => equilibriumMarkedPastWork z t / t)
        atTop (nhds rate) ∧
      (∀ t : ℝ, ∀ i : ℤ,
        i ∈ equilibriumBackwardArrivalIndices t z.1 ↔
          -t ≤ equilibriumBaseArrival z.1 i ∧ equilibriumBaseArrival z.1 i < 0) := by
    filter_upwards [ae_tendsto_equilibriumMarkedPastWork_div_atTop hrate, henum]
      with z hwork henum_z
    exact ⟨hwork, henum_z⟩
  have hlift : ∀ᵐ z ∂stationaryPoissonWorkMeasure rate,
      Tendsto (fun t : ℝ =>
        equilibriumMarkedPastWork (stationaryPoissonWorkToEquilibrium z) t / t)
          atTop (nhds rate) ∧
      (∀ t : ℝ, ∀ i : ℤ,
        i ∈ equilibriumBackwardArrivalIndices t
          (stationaryPoissonWorkToEquilibrium z).1 ↔
          -t ≤ equilibriumBaseArrival (stationaryPoissonWorkToEquilibrium z).1 i ∧
            equilibriumBaseArrival (stationaryPoissonWorkToEquilibrium z).1 i < 0) := by
    refine ae_of_ae_map (μ := stationaryPoissonWorkMeasure rate)
      (f := stationaryPoissonWorkToEquilibrium)
      (p := fun z : ((ℕ → ℝ) × (ℕ → ℝ)) × (ℤ → ℝ) =>
        Tendsto (fun t : ℝ => equilibriumMarkedPastWork z t / t)
          atTop (nhds rate) ∧
        (∀ t : ℝ, ∀ i : ℤ,
          i ∈ equilibriumBackwardArrivalIndices t z.1 ↔
            -t ≤ equilibriumBaseArrival z.1 i ∧ equilibriumBaseArrival z.1 i < 0))
      measurable_stationaryPoissonWorkToEquilibrium.aemeasurable ?_
    rw [(stationaryPoissonWorkToEquilibrium_measurePreserving hrate).map_eq]
    exact htarget
  filter_upwards [hlift] with z hz
  rcases hz with ⟨hwork, henum_z⟩
  refine hwork.congr' ?_
  refine Filter.Eventually.of_forall fun t => ?_
  have hindices :
      suspensionBaseArrivalIndices (-t) 0 z.1 =
        equilibriumBackwardArrivalIndices t
          (stationaryPoissonWorkToEquilibrium z).1 := by
    ext i
    change i ∈ suspensionBaseArrivalIndices (-t) 0 z.1 ↔
      i ∈ equilibriumBackwardArrivalIndices t (suspensionToEquilibrium z.1.1)
    calc
      i ∈ suspensionBaseArrivalIndices (-t) 0 z.1 ↔
          -t ≤ suspensionBaseArrival z.1 i ∧ suspensionBaseArrival z.1 i < 0 :=
        mem_suspensionBaseArrivalIndices_iff (-t) 0 z.1 i
      _ ↔ -t ≤ equilibriumBaseArrival (suspensionToEquilibrium z.1.1) i ∧
          equilibriumBaseArrival (suspensionToEquilibrium z.1.1) i < 0 := by
        change (-t ≤ candidatePalmArrival z.1.1.1 i - z.1.1.2 ∧
            candidatePalmArrival z.1.1.1 i - z.1.1.2 < 0) ↔
          -t ≤ equilibriumBaseArrival (suspensionToEquilibrium z.1.1) i ∧
            equilibriumBaseArrival (suspensionToEquilibrium z.1.1) i < 0
        rw [equilibriumBaseArrival_suspensionToEquilibrium]
      _ ↔ i ∈ equilibriumBackwardArrivalIndices t
          (suspensionToEquilibrium z.1.1) := by
        exact (henum_z t i).symm
  have hsum : stationaryPoissonWorkPastAggregate z t =
      equilibriumMarkedPastWork (stationaryPoissonWorkToEquilibrium z) t := by
    rw [stationaryPoissonWorkPastAggregate, hindices]
    symm
    simpa [stationaryPoissonWorkToEquilibrium, stationaryPoissonWorkRequirement] using
      (equilibriumMarkedPastWork_eq_backwardArrivalSum
        (stationaryPoissonWorkToEquilibrium z) t)
  change equilibriumMarkedPastWork (stationaryPoissonWorkToEquilibrium z) t / t =
    stationaryPoissonWorkPastAggregate z t / t
  exact congrArg (fun x : ℝ => x / t) hsum.symm

end

end AppliedModelingLib.Probability.Queueing
