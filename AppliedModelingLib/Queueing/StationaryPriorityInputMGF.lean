import AppliedModelingLib.Foundations.Probability.PalmTaggedPoissonWorkFutureMGF
import AppliedModelingLib.Foundations.Probability.StationaryPoissonWorkFutureMGF
import AppliedModelingLib.Queueing.StationaryPriorityInput

/-!
# Exponential moments of multiclass Palm priority input

Each individual class's literal future-work ledger inherits the exact
compound-Poisson exponential moment from its selected or stationary input
coordinate.  No queue response or stopping-time claim is made here.
-/

namespace AppliedModelingLib.Queueing

open MeasureTheory ProbabilityTheory Filter
open AppliedModelingLib.Probability
open AppliedModelingLib.Probability.PoissonProcess
open scoped ENNReal

noncomputable section

variable {Class : Type*} [Fintype Class]

local instance stationaryPriorityInputMGFDecidableEq : DecidableEq Class := Classical.decEq Class

/-- The selected class's scaled post-tag work has an integrable exponential
moment whenever the product of the tilt and mean service is below one. -/
theorem integrable_exp_mul_stationaryPriorityClassTaggedFutureWorkAggregate
    (arrivalRate meanService : Class → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (i : Class) (t tilt : ℝ) (ht : 0 ≤ t)
    (htilt : tilt * meanService i < 1) :
    Integrable (fun z => Real.exp
      (tilt * stationaryPriorityClassTaggedFutureWorkAggregate meanService i z t))
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag := by
  let tagged := Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero
    (harrivalRate i)
  let passive := multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i
  letI : IsProbabilityMeasure tagged.Ptag := tagged.isProbability
  letI : IsProbabilityMeasure passive.Pbase := passive.isProbability
  have hraw : Integrable (fun y : (ℤ → ℝ) × (ℤ → ℝ) =>
      Real.exp ((tilt * meanService i) *
        palmTaggedPoissonWorkFutureAggregate y t)) tagged.Ptag := by
    change Integrable (fun y : (ℤ → ℝ) × (ℤ → ℝ) =>
      Real.exp ((tilt * meanService i) *
        palmTaggedPoissonWorkFutureAggregate y t))
      ((twoSidedInterarrivalMeasure (arrivalRate i)).prod
        (twoSidedInterarrivalMeasure (1 : ℝ)))
    exact integrable_exp_mul_palmTaggedPoissonWorkFutureAggregate
      (harrivalRate i) ht htilt
  have hlift : Integrable (fun z :
      MulticlassStationaryPoissonWorkClassTaggedSample Class i =>
      Real.exp ((tilt * meanService i) *
        palmTaggedPoissonWorkFutureAggregate z.1 t))
      (tagged.Ptag.prod passive.Pbase) := by
    simpa [Function.comp_def] using hraw.comp_fst passive.Pbase
  change Integrable (fun z => Real.exp
      (tilt * stationaryPriorityClassTaggedFutureWorkAggregate meanService i z t))
      (tagged.Ptag.prod passive.Pbase)
  refine hlift.congr ?_
  filter_upwards with z
  rw [stationaryPriorityClassTaggedFutureWorkAggregate_eq]
  congr 1
  ring

/-- The selected class's scaled post-tag work has the exact compound-Poisson
MGF at its physical arrival rate. -/
theorem integral_exp_mul_stationaryPriorityClassTaggedFutureWorkAggregate
    (arrivalRate meanService : Class → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (i : Class) (t tilt : ℝ) (ht : 0 ≤ t)
    (htilt : tilt * meanService i < 1) :
    ∫ z, Real.exp
        (tilt * stationaryPriorityClassTaggedFutureWorkAggregate meanService i z t)
      ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag =
      Real.exp ((arrivalRate i * t) *
        (1 / (1 - tilt * meanService i) - 1)) := by
  let tagged := Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero
    (harrivalRate i)
  let passive := multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i
  letI : IsProbabilityMeasure tagged.Ptag := tagged.isProbability
  letI : IsProbabilityMeasure passive.Pbase := passive.isProbability
  have hraw : Integrable (fun y : (ℤ → ℝ) × (ℤ → ℝ) =>
      Real.exp ((tilt * meanService i) *
        palmTaggedPoissonWorkFutureAggregate y t)) tagged.Ptag := by
    change Integrable (fun y : (ℤ → ℝ) × (ℤ → ℝ) =>
      Real.exp ((tilt * meanService i) *
        palmTaggedPoissonWorkFutureAggregate y t))
      ((twoSidedInterarrivalMeasure (arrivalRate i)).prod
        (twoSidedInterarrivalMeasure (1 : ℝ)))
    exact integrable_exp_mul_palmTaggedPoissonWorkFutureAggregate
      (harrivalRate i) ht htilt
  calc
    ∫ z, Real.exp
        (tilt * stationaryPriorityClassTaggedFutureWorkAggregate meanService i z t)
        ∂(tagged.Ptag.prod passive.Pbase) =
        ∫ z, Real.exp ((tilt * meanService i) *
          palmTaggedPoissonWorkFutureAggregate z.1 t)
          ∂(tagged.Ptag.prod passive.Pbase) := by
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards with z
            rw [stationaryPriorityClassTaggedFutureWorkAggregate_eq]
            congr 1
            ring
    _ = ∫ y : (ℤ → ℝ) × (ℤ → ℝ),
        Real.exp ((tilt * meanService i) *
          palmTaggedPoissonWorkFutureAggregate y t) ∂tagged.Ptag := by
            simpa [Function.comp_def] using
              (measurePreserving_fst : MeasurePreserving Prod.fst
                (tagged.Ptag.prod passive.Pbase) tagged.Ptag).hasLaw.integral_comp
                (f := fun y : (ℤ → ℝ) × (ℤ → ℝ) =>
                  Real.exp ((tilt * meanService i) *
                    palmTaggedPoissonWorkFutureAggregate y t))
                hraw.aestronglyMeasurable
    _ = Real.exp ((arrivalRate i * t) *
        (1 / (1 - tilt * meanService i) - 1)) := by
          change ∫ y : (ℤ → ℝ) × (ℤ → ℝ),
              Real.exp ((tilt * meanService i) *
                palmTaggedPoissonWorkFutureAggregate y t)
              ∂((twoSidedInterarrivalMeasure (arrivalRate i)).prod
                (twoSidedInterarrivalMeasure (1 : ℝ))) = _
          exact integral_exp_mul_palmTaggedPoissonWorkFutureAggregate
            (harrivalRate i) ht htilt

/-- A passive class's scaled post-origin work has an integrable exponential
moment under the selected class's Palm law. -/
theorem integrable_exp_mul_stationaryPriorityTaggedFutureWorkAggregate_of_ne
    (arrivalRate meanService : Class → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i j : Class) (hji : j ≠ i) (t tilt : ℝ) (ht : 0 ≤ t)
    (htilt : tilt * meanService j < 1) :
    Integrable (fun z => Real.exp
      (tilt * stationaryPriorityTaggedFutureWorkAggregate meanService i z j t))
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag := by
  let tagged := Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero
    (harrivalRate i)
  let passive := multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i
  let restRate : {k : Class // k ≠ i} → ℝ := fun k => arrivalRate k.1
  let selectedPassive : {k : Class // k ≠ i} := ⟨j, hji⟩
  letI : IsProbabilityMeasure tagged.Ptag := tagged.isProbability
  letI : IsProbabilityMeasure passive.Pbase := passive.isProbability
  have hraw : Integrable (fun path : StationaryPoissonWorkPath =>
      Real.exp ((tilt * meanService j) *
        Probability.Queueing.stationaryPoissonWorkFutureAggregate path t))
      (Probability.Queueing.stationaryPoissonWorkMeasure (arrivalRate j)) :=
    Probability.Queueing.integrable_exp_mul_stationaryPoissonWorkFutureAggregate
      (harrivalRate j) ht htilt
  have hrest : Integrable (fun w : {k : Class // k ≠ i} →
      StationaryPoissonWorkPath =>
      Real.exp ((tilt * meanService j) *
        Probability.Queueing.stationaryPoissonWorkFutureAggregate
          (w selectedPassive) t)) passive.Pbase := by
    change Integrable (fun w : {k : Class // k ≠ i} →
        StationaryPoissonWorkPath =>
        Real.exp ((tilt * meanService j) *
          Probability.Queueing.stationaryPoissonWorkFutureAggregate
          (w selectedPassive) t))
        (Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure restRate)
    simpa [restRate, selectedPassive] using
      ((Probability.PoissonProcess.measurePreserving_multiclassStationaryPoissonWorkPath
        restRate (fun k => harrivalRate k.1) selectedPassive).integrable_comp
        hraw.aestronglyMeasurable).mpr hraw
  have hlift : Integrable (fun z :
      MulticlassStationaryPoissonWorkClassTaggedSample Class i =>
      Real.exp ((tilt * meanService j) *
        Probability.Queueing.stationaryPoissonWorkFutureAggregate
          (z.2 selectedPassive) t)) (tagged.Ptag.prod passive.Pbase) := by
    simpa [Function.comp_def] using hrest.comp_snd tagged.Ptag
  change Integrable (fun z => Real.exp
      (tilt * stationaryPriorityTaggedFutureWorkAggregate meanService i z j t))
      (tagged.Ptag.prod passive.Pbase)
  refine hlift.congr ?_
  filter_upwards with z
  rw [stationaryPriorityTaggedFutureWorkAggregate_of_ne meanService i j hji]
  congr 1
  ring

/-- A passive class's scaled post-origin work has the exact compound-Poisson
MGF under the selected class's Palm law. -/
theorem integral_exp_mul_stationaryPriorityTaggedFutureWorkAggregate_of_ne
    (arrivalRate meanService : Class → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i j : Class) (hji : j ≠ i) (t tilt : ℝ) (ht : 0 ≤ t)
    (htilt : tilt * meanService j < 1) :
    ∫ z, Real.exp
        (tilt * stationaryPriorityTaggedFutureWorkAggregate meanService i z j t)
      ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag =
      Real.exp ((arrivalRate j * t) *
        (1 / (1 - tilt * meanService j) - 1)) := by
  let tagged := Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero
    (harrivalRate i)
  let passive := multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i
  let restRate : {k : Class // k ≠ i} → ℝ := fun k => arrivalRate k.1
  let selectedPassive : {k : Class // k ≠ i} := ⟨j, hji⟩
  letI : IsProbabilityMeasure tagged.Ptag := tagged.isProbability
  letI : IsProbabilityMeasure passive.Pbase := passive.isProbability
  have hraw : Integrable (fun path : StationaryPoissonWorkPath =>
      Real.exp ((tilt * meanService j) *
        Probability.Queueing.stationaryPoissonWorkFutureAggregate path t))
      (Probability.Queueing.stationaryPoissonWorkMeasure (arrivalRate j)) :=
    Probability.Queueing.integrable_exp_mul_stationaryPoissonWorkFutureAggregate
      (harrivalRate j) ht htilt
  have hrest : Integrable (fun w : {k : Class // k ≠ i} →
      StationaryPoissonWorkPath =>
      Real.exp ((tilt * meanService j) *
        Probability.Queueing.stationaryPoissonWorkFutureAggregate
          (w selectedPassive) t)) passive.Pbase := by
    change Integrable (fun w : {k : Class // k ≠ i} →
        StationaryPoissonWorkPath =>
        Real.exp ((tilt * meanService j) *
          Probability.Queueing.stationaryPoissonWorkFutureAggregate
          (w selectedPassive) t))
        (Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure restRate)
    simpa [restRate, selectedPassive] using
      ((Probability.PoissonProcess.measurePreserving_multiclassStationaryPoissonWorkPath
        restRate (fun k => harrivalRate k.1) selectedPassive).integrable_comp
        hraw.aestronglyMeasurable).mpr hraw
  calc
    ∫ z, Real.exp
        (tilt * stationaryPriorityTaggedFutureWorkAggregate meanService i z j t)
        ∂(tagged.Ptag.prod passive.Pbase) =
        ∫ z, Real.exp ((tilt * meanService j) *
          Probability.Queueing.stationaryPoissonWorkFutureAggregate
            (z.2 selectedPassive) t) ∂(tagged.Ptag.prod passive.Pbase) := by
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards with z
            rw [stationaryPriorityTaggedFutureWorkAggregate_of_ne meanService i j hji]
            congr 1
            ring
    _ = ∫ w : {k : Class // k ≠ i} → StationaryPoissonWorkPath,
        Real.exp ((tilt * meanService j) *
          Probability.Queueing.stationaryPoissonWorkFutureAggregate
            (w selectedPassive) t) ∂passive.Pbase := by
            simpa [Function.comp_def] using
              (measurePreserving_snd : MeasurePreserving Prod.snd
                (tagged.Ptag.prod passive.Pbase) passive.Pbase).hasLaw.integral_comp
                (f := fun w : {k : Class // k ≠ i} →
                  StationaryPoissonWorkPath =>
                  Real.exp ((tilt * meanService j) *
                    Probability.Queueing.stationaryPoissonWorkFutureAggregate
                      (w selectedPassive) t))
                hrest.aestronglyMeasurable
    _ = ∫ path : StationaryPoissonWorkPath,
        Real.exp ((tilt * meanService j) *
          Probability.Queueing.stationaryPoissonWorkFutureAggregate path t)
          ∂Probability.Queueing.stationaryPoissonWorkMeasure (arrivalRate j) := by
            simpa [restRate, selectedPassive, Function.comp_def] using
              (Probability.PoissonProcess.measurePreserving_multiclassStationaryPoissonWorkPath
                restRate (fun k => harrivalRate k.1) selectedPassive).hasLaw.integral_comp
                (f := fun path : StationaryPoissonWorkPath =>
                  Real.exp ((tilt * meanService j) *
                    Probability.Queueing.stationaryPoissonWorkFutureAggregate path t))
                hraw.aestronglyMeasurable
    _ = Real.exp ((arrivalRate j * t) *
        (1 / (1 - tilt * meanService j) - 1)) :=
      Probability.Queueing.integral_exp_mul_stationaryPoissonWorkFutureAggregate
        (harrivalRate j) ht htilt

/-- Every class's post-tag work has an integrable exponential moment under
the literal selected-arrival Palm law. -/
theorem integrable_exp_mul_stationaryPriorityTaggedFutureWorkAggregate
    (arrivalRate meanService : Class → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i j : Class) (t tilt : ℝ) (ht : 0 ≤ t)
    (htilt : tilt * meanService j < 1) :
    Integrable (fun z => Real.exp
      (tilt * stationaryPriorityTaggedFutureWorkAggregate meanService i z j t))
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag := by
  by_cases hji : j = i
  · subst j
    simpa only [stationaryPriorityTaggedFutureWorkAggregate_self] using
      integrable_exp_mul_stationaryPriorityClassTaggedFutureWorkAggregate
        arrivalRate meanService harrivalRate i t tilt ht htilt
  · exact integrable_exp_mul_stationaryPriorityTaggedFutureWorkAggregate_of_ne
      arrivalRate meanService harrivalRate i j hji t tilt ht htilt

/-- Every class's post-tag work has its exact compound-Poisson MGF under the
literal selected-arrival Palm law. -/
theorem integral_exp_mul_stationaryPriorityTaggedFutureWorkAggregate
    (arrivalRate meanService : Class → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i j : Class) (t tilt : ℝ) (ht : 0 ≤ t)
    (htilt : tilt * meanService j < 1) :
    ∫ z, Real.exp
        (tilt * stationaryPriorityTaggedFutureWorkAggregate meanService i z j t)
      ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag =
      Real.exp ((arrivalRate j * t) *
        (1 / (1 - tilt * meanService j) - 1)) := by
  by_cases hji : j = i
  · subst j
    simpa only [stationaryPriorityTaggedFutureWorkAggregate_self] using
      integral_exp_mul_stationaryPriorityClassTaggedFutureWorkAggregate
        arrivalRate meanService harrivalRate i t tilt ht htilt
  · exact integral_exp_mul_stationaryPriorityTaggedFutureWorkAggregate_of_ne
      arrivalRate meanService harrivalRate i j hji t tilt ht htilt

/-- Chernoff's upper-tail bound for one literal class ledger on the selected
Palm carrier. -/
theorem measureReal_stationaryPriorityTaggedFutureWorkAggregate_ge_le
    (arrivalRate meanService : Class → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i j : Class) (t tilt threshold : ℝ) (ht : 0 ≤ t)
    (htilt_nonneg : 0 ≤ tilt) (htilt : tilt * meanService j < 1) :
    (Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag.real
        {z | threshold ≤ stationaryPriorityTaggedFutureWorkAggregate meanService i z j t} ≤
      Real.exp (-tilt * threshold) *
        Real.exp ((arrivalRate j * t) *
          (1 / (1 - tilt * meanService j) - 1)) := by
  let tagged := Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero
    (harrivalRate i)
  let passive := multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i
  letI : IsProbabilityMeasure tagged.Ptag := tagged.isProbability
  letI : IsProbabilityMeasure passive.Pbase := passive.isProbability
  let X : MulticlassStationaryPoissonWorkClassTaggedSample Class i → ℝ :=
    fun z => stationaryPriorityTaggedFutureWorkAggregate meanService i z j t
  have hint : Integrable (fun z => Real.exp (tilt * X z))
      (tagged.Ptag.prod passive.Pbase) := by
    simpa [X] using
      integrable_exp_mul_stationaryPriorityTaggedFutureWorkAggregate
        arrivalRate meanService harrivalRate i j t tilt ht htilt
  calc
    (tagged.Ptag.prod passive.Pbase).real {z | threshold ≤ X z} ≤
        Real.exp (-tilt * threshold) *
          mgf X (tagged.Ptag.prod passive.Pbase) tilt :=
      measure_ge_le_exp_mul_mgf threshold htilt_nonneg hint
    _ = Real.exp (-tilt * threshold) *
        Real.exp ((arrivalRate j * t) *
          (1 / (1 - tilt * meanService j) - 1)) := by
      rw [show mgf X (tagged.Ptag.prod passive.Pbase) tilt =
        ∫ z, Real.exp (tilt * X z) ∂(tagged.Ptag.prod passive.Pbase) by rfl]
      congr 1
      simpa [X] using
        integral_exp_mul_stationaryPriorityTaggedFutureWorkAggregate
          arrivalRate meanService harrivalRate i j t tilt ht htilt

/-- A finite total future-work ledger can exceed a threshold only if one class
ledger exceeds its equal share. -/
theorem setOf_totalFutureWork_ge_subset_iUnion_classFutureWork_ge
    (meanService : Class → ℝ) (i : Class)
    (t threshold : ℝ) (hcard : 0 < Fintype.card Class) :
    {z : MulticlassStationaryPoissonWorkClassTaggedSample Class i |
      threshold ≤ stationaryPriorityTaggedTotalFutureWorkAggregate meanService i z t} ⊆
      ⋃ j, {z | threshold / (Fintype.card Class : ℝ) ≤
        stationaryPriorityTaggedFutureWorkAggregate meanService i z j t} := by
  intro z hz
  by_contra hnot
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, not_exists] at hnot
  have hlt : ∀ j, stationaryPriorityTaggedFutureWorkAggregate meanService i z j t <
      threshold / (Fintype.card Class : ℝ) := fun j => lt_of_not_ge (hnot j)
  have hsum_lt : ∑ j, stationaryPriorityTaggedFutureWorkAggregate meanService i z j t <
      ∑ _j : Class, threshold / (Fintype.card Class : ℝ) := by
    apply Finset.sum_lt_sum_of_nonempty
      (Finset.card_pos.mp (by simpa using hcard))
    intro j _
    exact hlt j
  have hcard_ne : (Fintype.card Class : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hcard
  have hconst : ∑ _j : Class, threshold / (Fintype.card Class : ℝ) = threshold := by
    rw [Finset.sum_const, Finset.card_univ]
    simp only [nsmul_eq_mul]
    field_simp
  change threshold ≤ ∑ j,
    stationaryPriorityTaggedFutureWorkAggregate meanService i z j t at hz
  linarith

/-- The selected-Palm total future-work tail is bounded by the finite sum of
the classwise Chernoff bounds. -/
theorem measureReal_stationaryPriorityTaggedTotalFutureWorkAggregate_ge_le
    (arrivalRate meanService : Class → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i : Class) (t threshold tilt : ℝ) (ht : 0 ≤ t) (hcard : 0 < Fintype.card Class)
    (htilt_nonneg : 0 ≤ tilt) (htilt : ∀ j, tilt * meanService j < 1) :
    (Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag.real
        {z | threshold ≤ stationaryPriorityTaggedTotalFutureWorkAggregate meanService i z t} ≤
      ∑ j, Real.exp (-tilt * (threshold / (Fintype.card Class : ℝ))) *
        Real.exp ((arrivalRate j * t) *
          (1 / (1 - tilt * meanService j) - 1)) := by
  let tagged := Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero
    (harrivalRate i)
  let passive := multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i
  letI : IsProbabilityMeasure tagged.Ptag := tagged.isProbability
  letI : IsProbabilityMeasure passive.Pbase := passive.isProbability
  let classTail : Class → Set (MulticlassStationaryPoissonWorkClassTaggedSample Class i) :=
    fun j => {z | threshold / (Fintype.card Class : ℝ) ≤
      stationaryPriorityTaggedFutureWorkAggregate meanService i z j t}
  calc
    (tagged.Ptag.prod passive.Pbase).real
        {z | threshold ≤ stationaryPriorityTaggedTotalFutureWorkAggregate meanService i z t} ≤
        (tagged.Ptag.prod passive.Pbase).real (⋃ j, classTail j) := by
          apply MeasureTheory.measureReal_mono
          · change {z | threshold ≤
              stationaryPriorityTaggedTotalFutureWorkAggregate meanService i z t} ⊆
                ⋃ j, {z | threshold / (Fintype.card Class : ℝ) ≤
                  stationaryPriorityTaggedFutureWorkAggregate meanService i z j t}
            exact setOf_totalFutureWork_ge_subset_iUnion_classFutureWork_ge
              (Class := Class) meanService i t threshold hcard
          · finiteness
    _ ≤ ∑ j, (tagged.Ptag.prod passive.Pbase).real (classTail j) :=
      MeasureTheory.measureReal_iUnion_fintype_le
        (μ := tagged.Ptag.prod passive.Pbase) classTail
    _ ≤ ∑ j, Real.exp (-tilt * (threshold / (Fintype.card Class : ℝ))) *
        Real.exp ((arrivalRate j * t) *
          (1 / (1 - tilt * meanService j) - 1)) := by
      refine Finset.sum_le_sum fun j _ => ?_
      simpa [classTail] using
        measureReal_stationaryPriorityTaggedFutureWorkAggregate_ge_le
          arrivalRate meanService harrivalRate i j t tilt
          (threshold / (Fintype.card Class : ℝ)) ht htilt_nonneg (htilt j)

/-- A total future-work threshold is exceeded only if one class exceeds a
specified classwise threshold whose sum is no larger than that total. -/
theorem setOf_totalFutureWork_ge_subset_iUnion_classFutureWork_ge_of_sum_le
    (meanService : Class → ℝ) (i : Class) (t threshold : ℝ)
    (classThreshold : Class → ℝ)
    (hcard : 0 < Fintype.card Class)
    (hsum : ∑ j, classThreshold j ≤ threshold) :
    {z : MulticlassStationaryPoissonWorkClassTaggedSample Class i |
      threshold ≤ stationaryPriorityTaggedTotalFutureWorkAggregate meanService i z t} ⊆
      ⋃ j, {z | classThreshold j ≤
        stationaryPriorityTaggedFutureWorkAggregate meanService i z j t} := by
  intro z hz
  by_contra hnot
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, not_exists] at hnot
  have hlt : ∀ j, stationaryPriorityTaggedFutureWorkAggregate meanService i z j t <
      classThreshold j := fun j => lt_of_not_ge (hnot j)
  have hsum_lt : ∑ j, stationaryPriorityTaggedFutureWorkAggregate meanService i z j t <
      ∑ j, classThreshold j := by
    apply Finset.sum_lt_sum_of_nonempty
      (Finset.card_pos.mp (by simpa using hcard))
    intro j _
    exact hlt j
  change threshold ≤ ∑ j,
    stationaryPriorityTaggedFutureWorkAggregate meanService i z j t at hz
  linarith

/-- The selected-Palm total future-work tail is bounded by the sum of
classwise Chernoff bounds for any admissible allocation of its threshold. -/
theorem measureReal_stationaryPriorityTaggedTotalFutureWorkAggregate_ge_le_of_sum_le
    (arrivalRate meanService : Class → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i : Class) (t threshold tilt : ℝ) (ht : 0 ≤ t)
    (classThreshold : Class → ℝ)
    (hcard : 0 < Fintype.card Class)
    (hsum : ∑ j, classThreshold j ≤ threshold)
    (htilt_nonneg : 0 ≤ tilt) (htilt : ∀ j, tilt * meanService j < 1) :
    (Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag.real
        {z | threshold ≤ stationaryPriorityTaggedTotalFutureWorkAggregate meanService i z t} ≤
      ∑ j, Real.exp (-tilt * classThreshold j) *
        Real.exp ((arrivalRate j * t) *
          (1 / (1 - tilt * meanService j) - 1)) := by
  let tagged := Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero
    (harrivalRate i)
  let passive := multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i
  letI : IsProbabilityMeasure tagged.Ptag := tagged.isProbability
  letI : IsProbabilityMeasure passive.Pbase := passive.isProbability
  let classTail : Class → Set (MulticlassStationaryPoissonWorkClassTaggedSample Class i) :=
    fun j => {z | classThreshold j ≤
      stationaryPriorityTaggedFutureWorkAggregate meanService i z j t}
  calc
    (tagged.Ptag.prod passive.Pbase).real
        {z | threshold ≤ stationaryPriorityTaggedTotalFutureWorkAggregate meanService i z t} ≤
        (tagged.Ptag.prod passive.Pbase).real (⋃ j, classTail j) := by
          apply MeasureTheory.measureReal_mono
          · change {z | threshold ≤
              stationaryPriorityTaggedTotalFutureWorkAggregate meanService i z t} ⊆
                ⋃ j, {z | classThreshold j ≤
                  stationaryPriorityTaggedFutureWorkAggregate meanService i z j t}
            exact setOf_totalFutureWork_ge_subset_iUnion_classFutureWork_ge_of_sum_le
              (Class := Class) meanService i t threshold classThreshold hcard hsum
          · finiteness
    _ ≤ ∑ j, (tagged.Ptag.prod passive.Pbase).real (classTail j) :=
      MeasureTheory.measureReal_iUnion_fintype_le
        (μ := tagged.Ptag.prod passive.Pbase) classTail
    _ ≤ ∑ j, Real.exp (-tilt * classThreshold j) *
        Real.exp ((arrivalRate j * t) *
          (1 / (1 - tilt * meanService j) - 1)) := by
      refine Finset.sum_le_sum fun j _ => ?_
      simpa [classTail] using
        measureReal_stationaryPriorityTaggedFutureWorkAggregate_ge_le
          arrivalRate meanService harrivalRate i j t tilt
          (classThreshold j) ht htilt_nonneg (htilt j)

/-- With classwise linear threshold rates whose sum is below the total rate,
the total future-work tail is bounded by a finite sum of exponentials. -/
theorem measureReal_stationaryPriorityTaggedTotalFutureWork_ge_le_exponentialSum
    (arrivalRate meanService : Class → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i : Class) (t totalThresholdRate tilt : ℝ) (ht : 0 ≤ t)
    (classThresholdRate : Class → ℝ)
    (hcard : 0 < Fintype.card Class)
    (hsum : ∑ j, classThresholdRate j ≤ totalThresholdRate)
    (htilt_nonneg : 0 ≤ tilt) (htilt : ∀ j, tilt * meanService j < 1) :
    (Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag.real
        {z | totalThresholdRate * t ≤
          stationaryPriorityTaggedTotalFutureWorkAggregate meanService i z t} ≤
      ∑ j, Real.exp
        ((-tilt * classThresholdRate j + arrivalRate j *
          (1 / (1 - tilt * meanService j) - 1)) * t) := by
  have hsumT : ∑ j, classThresholdRate j * t ≤ totalThresholdRate * t := by
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right hsum ht
  calc
    (Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag.real
        {z | totalThresholdRate * t ≤
          stationaryPriorityTaggedTotalFutureWorkAggregate meanService i z t} ≤
      ∑ j, Real.exp (-tilt * (classThresholdRate j * t)) *
        Real.exp ((arrivalRate j * t) *
          (1 / (1 - tilt * meanService j) - 1)) :=
      measureReal_stationaryPriorityTaggedTotalFutureWorkAggregate_ge_le_of_sum_le
        arrivalRate meanService harrivalRate i t (totalThresholdRate * t) tilt ht
        (fun j => classThresholdRate j * t) hcard hsumT htilt_nonneg htilt
    _ = ∑ j, Real.exp
        ((-tilt * classThresholdRate j + arrivalRate j *
          (1 / (1 - tilt * meanService j) - 1)) * t) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← Real.exp_add]
      congr 1
      ring

/-- The finite-exponential total future-work tail bound in extended
nonnegative-real measure form. -/
theorem measure_stationaryPriorityTaggedTotalFutureWork_ge_le_exponentialSum
    (arrivalRate meanService : Class → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (i : Class) (t totalThresholdRate tilt : ℝ) (ht : 0 ≤ t)
    (classThresholdRate : Class → ℝ)
    (hcard : 0 < Fintype.card Class)
    (hsum : ∑ j, classThresholdRate j ≤ totalThresholdRate)
    (htilt_nonneg : 0 ≤ tilt) (htilt : ∀ j, tilt * meanService j < 1) :
    (Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag
        {z | totalThresholdRate * t ≤
          stationaryPriorityTaggedTotalFutureWorkAggregate meanService i z t} ≤
      ∑ j, ENNReal.ofReal (Real.exp
        ((-tilt * classThresholdRate j + arrivalRate j *
          (1 / (1 - tilt * meanService j) - 1)) * t)) := by
  let tagged := Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero
    (harrivalRate i)
  let passive := multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i
  letI : IsProbabilityMeasure tagged.Ptag := tagged.isProbability
  letI : IsProbabilityMeasure passive.Pbase := passive.isProbability
  let μ := tagged.Ptag.prod passive.Pbase
  let s : Set (MulticlassStationaryPoissonWorkClassTaggedSample Class i) :=
    {z | totalThresholdRate * t ≤
      stationaryPriorityTaggedTotalFutureWorkAggregate meanService i z t}
  let bound : Class → ℝ := fun j => Real.exp
    ((-tilt * classThresholdRate j + arrivalRate j *
      (1 / (1 - tilt * meanService j) - 1)) * t)
  have hreal : μ.real s ≤ ∑ j, bound j := by
    simpa [μ, tagged, passive, s, bound] using
      measureReal_stationaryPriorityTaggedTotalFutureWork_ge_le_exponentialSum
        arrivalRate meanService harrivalRate i t totalThresholdRate tilt ht
        classThresholdRate hcard hsum htilt_nonneg htilt
  change μ s ≤ ∑ j, ENNReal.ofReal (bound j)
  have hfinite : μ s ≠ ∞ := by finiteness
  calc
    μ s = ENNReal.ofReal (μ s).toReal := (ENNReal.ofReal_toReal hfinite).symm
    _ ≤ ENNReal.ofReal (∑ j, bound j) := ENNReal.ofReal_le_ofReal hreal
    _ = ∑ j, ENNReal.ofReal (bound j) :=
      ENNReal.ofReal_sum_of_nonneg fun j _ => (Real.exp_pos _).le

end

end AppliedModelingLib.Queueing
