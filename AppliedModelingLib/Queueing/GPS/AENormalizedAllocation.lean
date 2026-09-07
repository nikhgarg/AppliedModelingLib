import AppliedModelingLib.Queueing.GPS.AERateFloor

/-!
# A.e. normalized GPS allocation to FCFS comparison

This module derives the a.e. guaranteed service floor from the normalized GPS
allocation formula itself.  It only asks for the allocation identity and the
positive/unit-bounded active-weight sum almost everywhere on each actual job
interval.  It then converts the path to `CoupledAERateFloorGPSPath`, whose
existing theorem yields the FCFS comparator recurrence.
-/

namespace AppliedModelingLib.Probability.Queueing

open scoped Topology

noncomputable section

/--
Pathwise data for an ideal fluid GPS class whose normalized allocation identity
holds almost everywhere on each actual job interval.  All a.e. assertions use
the same restricted volume measure, so their conjunction is available a.e.
without fixing arbitrary endpoint values.
-/
structure CoupledAENormalizedIdealFluidGPSPath
    (initialBusyUntil : ℝ) (arrival work departure : ℕ → ℝ)
    (capacity weight : ℝ) where
  capacity_nonneg : 0 ≤ capacity
  weight_nonneg : 0 ≤ weight
  guaranteed_rate_pos : 0 < capacity * weight
  actualServiceStart : ℕ → ℝ
  arrival_le_actualServiceStart : ∀ n, arrival n ≤ actualServiceStart n
  departure_after_actualServiceStart : ∀ n,
    actualServiceStart n ≤ departure n
  actualStart_zero_le_comparatorStart :
    actualServiceStart 0 ≤ max (arrival 0) initialBusyUntil
  actualStart_succ_le_comparatorStart : ∀ n,
    actualServiceStart (n + 1) ≤ max (arrival (n + 1)) (departure n)
  activeWeightSum : ℝ → ℝ
  instantaneousClassRate : ℝ → ℝ
  service : ℝ → ℝ
  rate_intervalIntegrable : ∀ n,
    IntervalIntegrable instantaneousClassRate MeasureTheory.volume
      (actualServiceStart n) (departure n)
  ae_gps_allocation_on_actual_job : ∀ n,
    ∀ᵐ t ∂(MeasureTheory.volume.restrict
      (Set.Icc (actualServiceStart n) (departure n))),
      instantaneousClassRate t =
        idealGPSClassRate capacity weight (activeWeightSum t)
  ae_activeWeightSum_pos_on_actual_job : ∀ n,
    ∀ᵐ t ∂(MeasureTheory.volume.restrict
      (Set.Icc (actualServiceStart n) (departure n))),
      0 < activeWeightSum t
  ae_activeWeightSum_le_one_on_actual_job : ∀ n,
    ∀ᵐ t ∂(MeasureTheory.volume.restrict
      (Set.Icc (actualServiceStart n) (departure n))),
      activeWeightSum t ≤ 1
  service_increment_eq_integral : ∀ n,
    service (departure n) - service (actualServiceStart n) =
      ∫ t in actualServiceStart n..departure n, instantaneousClassRate t
  completed_work_eq_service : ∀ n,
    service (departure n) - service (actualServiceStart n) = work n

namespace CoupledAENormalizedIdealFluidGPSPath

variable {initialBusyUntil capacity weight : ℝ} {arrival work departure : ℕ → ℝ}

/-- The normalized allocation formula yields the a.e. unnormalized GPS floor. -/
theorem ae_guaranteed_rate_floor_on_actual_job
    (H : CoupledAENormalizedIdealFluidGPSPath
      initialBusyUntil arrival work departure capacity weight) (n : ℕ) :
    ∀ᵐ t ∂(MeasureTheory.volume.restrict
      (Set.Icc (H.actualServiceStart n) (departure n))),
      capacity * weight ≤ H.instantaneousClassRate t := by
  filter_upwards [H.ae_gps_allocation_on_actual_job n,
    H.ae_activeWeightSum_pos_on_actual_job n,
    H.ae_activeWeightSum_le_one_on_actual_job n] with t halloc hpos hle
  rw [halloc]
  exact idealGPSClassRate_ge_guaranteed H.capacity_nonneg H.weight_nonneg hpos hle

/-- Forgetting the normalized representation yields the reusable a.e.-floor path. -/
def toAERateFloorGPSPath
    (H : CoupledAENormalizedIdealFluidGPSPath
      initialBusyUntil arrival work departure capacity weight) :
    CoupledAERateFloorGPSPath initialBusyUntil arrival work departure capacity weight where
  capacity_nonneg := H.capacity_nonneg
  weight_nonneg := H.weight_nonneg
  guaranteed_rate_pos := H.guaranteed_rate_pos
  actualServiceStart := H.actualServiceStart
  arrival_le_actualServiceStart := H.arrival_le_actualServiceStart
  departure_after_actualServiceStart := H.departure_after_actualServiceStart
  actualStart_zero_le_comparatorStart := H.actualStart_zero_le_comparatorStart
  actualStart_succ_le_comparatorStart := H.actualStart_succ_le_comparatorStart
  instantaneousClassRate := H.instantaneousClassRate
  service := H.service
  rate_intervalIntegrable := H.rate_intervalIntegrable
  ae_guaranteed_rate_floor_on_actual_job := H.ae_guaranteed_rate_floor_on_actual_job
  service_increment_eq_integral := H.service_increment_eq_integral
  completed_work_eq_service := H.completed_work_eq_service

/--
The a.e. normalized GPS path supplies the existing constant-rate FCFS
comparison recurrence through its derived a.e. guaranteed-rate floor.
-/
theorem toFCFSServiceFloorUpperBoundFromInitial
    (H : CoupledAENormalizedIdealFluidGPSPath
      initialBusyUntil arrival work departure capacity weight) :
    FCFSServiceFloorUpperBoundFromInitial initialBusyUntil arrival work departure
      (capacity * weight) :=
  H.toAERateFloorGPSPath.toFCFSServiceFloorUpperBoundFromInitial

end CoupledAENormalizedIdealFluidGPSPath

/--
Finite-class source-model data for the tagged class of an ideal fluid GPS
queue.  The active classes and class weights are the multiclass inputs from the
paper model; positivity and unit-boundedness of the tagged class denominator
are derived from the tagged class being active and from the condition that the
total SLA-class weight is at most one.
-/
structure TaggedClassAENormalizedGPSSourcePath
    (ι : Type*) [Fintype ι] [DecidableEq ι]
    (tag : ι) (initialBusyUntil : ℝ) (arrival work departure : ℕ → ℝ)
    (capacity : ℝ) (weight : ι → ℝ) where
  capacity_nonneg : 0 ≤ capacity
  weight_nonneg : ∀ i, 0 ≤ weight i
  total_weight_le_one : Finset.univ.sum weight ≤ 1
  tagged_guaranteed_rate_pos : 0 < capacity * weight tag
  actualServiceStart : ℕ → ℝ
  arrival_le_actualServiceStart : ∀ n, arrival n ≤ actualServiceStart n
  departure_after_actualServiceStart : ∀ n,
    actualServiceStart n ≤ departure n
  actualStart_zero_le_comparatorStart :
    actualServiceStart 0 ≤ max (arrival 0) initialBusyUntil
  actualStart_succ_le_comparatorStart : ∀ n,
    actualServiceStart (n + 1) ≤ max (arrival (n + 1)) (departure n)
  activeClasses : ℝ → Finset ι
  activeWeightSum : ℝ → ℝ
  instantaneousClassRate : ℝ → ℝ
  service : ℝ → ℝ
  rate_intervalIntegrable : ∀ n,
    IntervalIntegrable instantaneousClassRate MeasureTheory.volume
      (actualServiceStart n) (departure n)
  ae_tag_active_on_actual_job : ∀ n,
    ∀ᵐ t ∂(MeasureTheory.volume.restrict
      (Set.Icc (actualServiceStart n) (departure n))),
      tag ∈ activeClasses t
  ae_activeWeightSum_eq_on_actual_job : ∀ n,
    ∀ᵐ t ∂(MeasureTheory.volume.restrict
      (Set.Icc (actualServiceStart n) (departure n))),
      activeWeightSum t = (activeClasses t).sum weight
  ae_gps_allocation_on_actual_job : ∀ n,
    ∀ᵐ t ∂(MeasureTheory.volume.restrict
      (Set.Icc (actualServiceStart n) (departure n))),
      instantaneousClassRate t =
        idealGPSClassRate capacity (weight tag) (activeWeightSum t)
  service_increment_eq_integral : ∀ n,
    service (departure n) - service (actualServiceStart n) =
      ∫ t in actualServiceStart n..departure n, instantaneousClassRate t
  completed_work_eq_service : ∀ n,
    service (departure n) - service (actualServiceStart n) = work n

namespace TaggedClassAENormalizedGPSSourcePath

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {tag : ι} {initialBusyUntil capacity : ℝ}
variable {arrival work departure : ℕ → ℝ} {weight : ι → ℝ}

/-- The source model's positive tagged guaranteed rate makes the tagged weight positive. -/
theorem tagged_weight_pos
    (H : TaggedClassAENormalizedGPSSourcePath ι tag initialBusyUntil
      arrival work departure capacity weight) :
    0 < weight tag := by
  have hnonneg := H.weight_nonneg tag
  by_contra hnot
  have hle : weight tag ≤ 0 := le_of_not_gt hnot
  have hzero : weight tag = 0 := le_antisymm hle hnonneg
  have hprod : 0 < capacity * weight tag := H.tagged_guaranteed_rate_pos
  rw [hzero, mul_zero] at hprod
  have hbad : (0 : ℝ) < 0 := hprod
  exact (lt_irrefl (0 : ℝ)) hbad

/--
On a tagged job interval the active denominator is positive because the tagged
class is active and its weight is positive.
-/
theorem ae_activeWeightSum_pos_on_actual_job
    (H : TaggedClassAENormalizedGPSSourcePath ι tag initialBusyUntil
      arrival work departure capacity weight) (n : ℕ) :
    ∀ᵐ t ∂(MeasureTheory.volume.restrict
      (Set.Icc (H.actualServiceStart n) (departure n))),
      0 < H.activeWeightSum t := by
  filter_upwards [H.ae_activeWeightSum_eq_on_actual_job n,
    H.ae_tag_active_on_actual_job n] with t hsum htag
  rw [hsum]
  exact lt_of_lt_of_le H.tagged_weight_pos
    (Finset.single_le_sum (fun i _ => H.weight_nonneg i) htag)

/--
The active denominator is at most one because active classes are a subset of
the finite SLA classes and total SLA-class weight is at most one.
-/
theorem ae_activeWeightSum_le_one_on_actual_job
    (H : TaggedClassAENormalizedGPSSourcePath ι tag initialBusyUntil
      arrival work departure capacity weight) (n : ℕ) :
    ∀ᵐ t ∂(MeasureTheory.volume.restrict
      (Set.Icc (H.actualServiceStart n) (departure n))),
      H.activeWeightSum t ≤ 1 := by
  filter_upwards [H.ae_activeWeightSum_eq_on_actual_job n] with t hsum
  rw [hsum]
  exact (Finset.sum_le_univ_sum_of_nonneg
    (s := H.activeClasses t) (f := weight)
    (fun i => H.weight_nonneg i)).trans H.total_weight_le_one

/--
The multiclass source-model assumptions instantiate the tagged-class
normalized GPS path consumed by the FCFS comparison layer.
-/
def toCoupledAENormalizedIdealFluidGPSPath
    (H : TaggedClassAENormalizedGPSSourcePath ι tag initialBusyUntil
      arrival work departure capacity weight) :
    CoupledAENormalizedIdealFluidGPSPath initialBusyUntil arrival work departure
      capacity (weight tag) where
  capacity_nonneg := H.capacity_nonneg
  weight_nonneg := H.weight_nonneg tag
  guaranteed_rate_pos := H.tagged_guaranteed_rate_pos
  actualServiceStart := H.actualServiceStart
  arrival_le_actualServiceStart := H.arrival_le_actualServiceStart
  departure_after_actualServiceStart := H.departure_after_actualServiceStart
  actualStart_zero_le_comparatorStart := H.actualStart_zero_le_comparatorStart
  actualStart_succ_le_comparatorStart := H.actualStart_succ_le_comparatorStart
  activeWeightSum := H.activeWeightSum
  instantaneousClassRate := H.instantaneousClassRate
  service := H.service
  rate_intervalIntegrable := H.rate_intervalIntegrable
  ae_gps_allocation_on_actual_job := H.ae_gps_allocation_on_actual_job
  ae_activeWeightSum_pos_on_actual_job := H.ae_activeWeightSum_pos_on_actual_job
  ae_activeWeightSum_le_one_on_actual_job := H.ae_activeWeightSum_le_one_on_actual_job
  service_increment_eq_integral := H.service_increment_eq_integral
  completed_work_eq_service := H.completed_work_eq_service

end TaggedClassAENormalizedGPSSourcePath

/--
Finite-class source-model data for only the tagged job.  This is the local
form needed for a response-tail bound at tag index zero: it records the tagged
job's service interval, the active GPS denominator on that interval, the
normalized allocation identity, and the tagged work/service identity.
-/
structure TaggedJobAENormalizedGPSSourcePath
    (ι : Type*) [Fintype ι] [DecidableEq ι]
    (tag : ι) (initialBusyUntil : ℝ) (arrival work departure : ℕ → ℝ)
    (capacity : ℝ) (weight : ι → ℝ) where
  capacity_nonneg : 0 ≤ capacity
  weight_nonneg : ∀ i, 0 ≤ weight i
  total_weight_le_one : Finset.univ.sum weight ≤ 1
  tagged_guaranteed_rate_pos : 0 < capacity * weight tag
  actualServiceStart : ℝ
  arrival_le_actualServiceStart : arrival 0 ≤ actualServiceStart
  departure_after_actualServiceStart : actualServiceStart ≤ departure 0
  actualStart_le_comparatorStart :
    actualServiceStart ≤ max (arrival 0) initialBusyUntil
  activeClasses : ℝ → Finset ι
  activeWeightSum : ℝ → ℝ
  instantaneousClassRate : ℝ → ℝ
  service : ℝ → ℝ
  rate_intervalIntegrable :
    IntervalIntegrable instantaneousClassRate MeasureTheory.volume
      actualServiceStart (departure 0)
  ae_tag_active_on_actual_job :
    ∀ᵐ t ∂(MeasureTheory.volume.restrict
      (Set.Icc actualServiceStart (departure 0))),
      tag ∈ activeClasses t
  ae_activeWeightSum_eq_on_actual_job :
    ∀ᵐ t ∂(MeasureTheory.volume.restrict
      (Set.Icc actualServiceStart (departure 0))),
      activeWeightSum t = (activeClasses t).sum weight
  ae_gps_allocation_on_actual_job :
    ∀ᵐ t ∂(MeasureTheory.volume.restrict
      (Set.Icc actualServiceStart (departure 0))),
      instantaneousClassRate t =
        idealGPSClassRate capacity (weight tag) (activeWeightSum t)
  service_increment_eq_integral :
    service (departure 0) - service actualServiceStart =
      ∫ t in actualServiceStart..departure 0, instantaneousClassRate t
  completed_work_eq_service :
    service (departure 0) - service actualServiceStart = work 0

namespace TaggedJobAENormalizedGPSSourcePath

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {tag : ι} {initialBusyUntil capacity : ℝ}
variable {arrival work departure : ℕ → ℝ} {weight : ι → ℝ}

/-- Positive tagged guaranteed rate implies positive tagged weight. -/
theorem tagged_weight_pos
    (H : TaggedJobAENormalizedGPSSourcePath ι tag initialBusyUntil
      arrival work departure capacity weight) :
    0 < weight tag := by
  have hnonneg := H.weight_nonneg tag
  by_contra hnot
  have hle : weight tag ≤ 0 := le_of_not_gt hnot
  have hzero : weight tag = 0 := le_antisymm hle hnonneg
  have hprod : 0 < capacity * weight tag := H.tagged_guaranteed_rate_pos
  rw [hzero, mul_zero] at hprod
  have hbad : (0 : ℝ) < 0 := hprod
  exact (lt_irrefl (0 : ℝ)) hbad

/-- The tagged job's active GPS denominator is positive almost everywhere. -/
theorem ae_activeWeightSum_pos_on_actual_job
    (H : TaggedJobAENormalizedGPSSourcePath ι tag initialBusyUntil
      arrival work departure capacity weight) :
    ∀ᵐ t ∂(MeasureTheory.volume.restrict
      (Set.Icc H.actualServiceStart (departure 0))),
      0 < H.activeWeightSum t := by
  filter_upwards [H.ae_activeWeightSum_eq_on_actual_job,
    H.ae_tag_active_on_actual_job] with t hsum htag
  rw [hsum]
  exact lt_of_lt_of_le H.tagged_weight_pos
    (Finset.single_le_sum (fun i _ => H.weight_nonneg i) htag)

/-- The tagged job's active GPS denominator is at most one almost everywhere. -/
theorem ae_activeWeightSum_le_one_on_actual_job
    (H : TaggedJobAENormalizedGPSSourcePath ι tag initialBusyUntil
      arrival work departure capacity weight) :
    ∀ᵐ t ∂(MeasureTheory.volume.restrict
      (Set.Icc H.actualServiceStart (departure 0))),
      H.activeWeightSum t ≤ 1 := by
  filter_upwards [H.ae_activeWeightSum_eq_on_actual_job] with t hsum
  rw [hsum]
  exact (Finset.sum_le_univ_sum_of_nonneg
    (s := H.activeClasses t) (f := weight)
    (fun i => H.weight_nonneg i)).trans H.total_weight_le_one

/-- The normalized allocation gives the tagged job its guaranteed rate floor. -/
theorem ae_guaranteed_rate_floor_on_actual_job
    (H : TaggedJobAENormalizedGPSSourcePath ι tag initialBusyUntil
      arrival work departure capacity weight) :
    ∀ᵐ t ∂(MeasureTheory.volume.restrict
      (Set.Icc H.actualServiceStart (departure 0))),
      capacity * weight tag ≤ H.instantaneousClassRate t := by
  filter_upwards [H.ae_gps_allocation_on_actual_job,
    H.ae_activeWeightSum_pos_on_actual_job,
    H.ae_activeWeightSum_le_one_on_actual_job] with t halloc hpos hle
  rw [halloc]
  exact idealGPSClassRate_ge_guaranteed H.capacity_nonneg (H.weight_nonneg tag)
    hpos hle

/-- Integrating the tagged job's a.e. rate floor gives its work floor. -/
theorem integrated_rate_floor
    (H : TaggedJobAENormalizedGPSSourcePath ι tag initialBusyUntil
      arrival work departure capacity weight) :
    capacity * weight tag * (departure 0 - H.actualServiceStart) ≤
      H.service (departure 0) - H.service H.actualServiceStart := by
  rw [H.service_increment_eq_integral]
  exact intervalIntegral_ge_const_of_ae_le
    H.departure_after_actualServiceStart H.rate_intervalIntegrable
    H.ae_guaranteed_rate_floor_on_actual_job

/-- The tagged job completes within its guaranteed-rate service window. -/
theorem departure_zero_le_actualStart_add_work_div
    (H : TaggedJobAENormalizedGPSSourcePath ι tag initialBusyUntil
      arrival work departure capacity weight) :
    departure 0 ≤ H.actualServiceStart + work 0 / (capacity * weight tag) := by
  have hservice := H.integrated_rate_floor
  rw [H.completed_work_eq_service] at hservice
  have hduration : departure 0 - H.actualServiceStart ≤
      work 0 / (capacity * weight tag) := by
    apply (le_div_iff₀ H.tagged_guaranteed_rate_pos).2
    nlinarith [hservice]
  linarith

/-- The tagged job's departure is bounded by the initial-workload FCFS comparator. -/
theorem departure_zero_le_fcfsDepartureFrom
    (H : TaggedJobAENormalizedGPSSourcePath ι tag initialBusyUntil
      arrival work departure capacity weight) :
    departure 0 ≤
      fcfsDepartureFrom initialBusyUntil arrival work (capacity * weight tag) 0 := by
  calc
    departure 0 ≤ H.actualServiceStart + work 0 / (capacity * weight tag) :=
      H.departure_zero_le_actualStart_add_work_div
    _ ≤ max (arrival 0) initialBusyUntil + work 0 / (capacity * weight tag) := by
      linarith [H.actualStart_le_comparatorStart]
    _ = fcfsDepartureFrom initialBusyUntil arrival work (capacity * weight tag) 0 := by
      rfl

/-- The tagged job's response is bounded by the initial-workload FCFS comparator. -/
theorem responseTime_zero_le_fcfsResponseTimeFrom
    (H : TaggedJobAENormalizedGPSSourcePath ι tag initialBusyUntil
      arrival work departure capacity weight) :
    responseTime arrival departure 0 ≤
      responseTime arrival
        (fcfsDepartureFrom initialBusyUntil arrival work (capacity * weight tag)) 0 := by
  unfold responseTime
  exact sub_le_sub_right H.departure_zero_le_fcfsDepartureFrom (arrival 0)

end TaggedJobAENormalizedGPSSourcePath

/-- Active GPS classes are exactly the finite classes whose backlog indicator is true. -/
def gpsBackloggedClasses
    (ι : Type*) [Fintype ι] (backlogged : ℝ → ι → Bool) (t : ℝ) : Finset ι :=
  Finset.univ.filter (fun i => backlogged t i = true)

/-- The GPS denominator induced by finite class weights and backlog indicators. -/
def gpsBackloggedWeightSum
    (ι : Type*) [Fintype ι] (weight : ι → ℝ)
    (backlogged : ℝ → ι → Bool) (t : ℝ) : ℝ :=
  (gpsBackloggedClasses ι backlogged t).sum weight

/-- The instantaneous normalized GPS rate of a tagged class, computed from
finite backlog indicators. -/
def gpsBackloggedClassRate
    (ι : Type*) [Fintype ι] (tag : ι) (capacity : ℝ) (weight : ι → ℝ)
    (backlogged : ℝ → ι → Bool) (t : ℝ) : ℝ :=
  idealGPSClassRate capacity (weight tag)
    (gpsBackloggedWeightSum ι weight backlogged t)

/-- Pointwise-equal finite backlog indicators induce the same tagged GPS rate. -/
theorem gpsBackloggedClassRate_congr_at
    {ι : Type*} [Fintype ι] (tag : ι) (capacity : ℝ)
    (weight : ι → ℝ) {backlogged₁ backlogged₂ : ℝ → ι → Bool}
    {t : ℝ} (hbacklogged : ∀ i, backlogged₁ t i = backlogged₂ t i) :
    gpsBackloggedClassRate ι tag capacity weight backlogged₁ t =
      gpsBackloggedClassRate ι tag capacity weight backlogged₂ t := by
  simp [gpsBackloggedClassRate, gpsBackloggedWeightSum,
    gpsBackloggedClasses, hbacklogged]

/-- Cumulative tagged service generated by the backlog-induced GPS rate from
an actual service-start time. -/
def gpsBackloggedCumulativeServiceFrom
    (ι : Type*) [Fintype ι] (tag : ι) (capacity : ℝ) (weight : ι → ℝ)
    (backlogged : ℝ → ι → Bool) (start t : ℝ) : ℝ :=
  ∫ u in start..t, gpsBackloggedClassRate ι tag capacity weight backlogged u

/--
For finitely many classes, a measurable backlog-induced GPS rate is locally
interval-integrable.  The rate takes only finitely many values, one for each
Boolean backlog snapshot, so measurability plus finite interval measure gives
integrability on every bounded interval.
-/
theorem gpsBackloggedClassRate_intervalIntegrable_all_of_measurable
    {ι : Type*} [Fintype ι]
    (tag : ι) (capacity : ℝ) (weight : ι → ℝ)
    (backlogged : ℝ → ι → Bool)
    (hmeas :
      Measurable (gpsBackloggedClassRate ι tag capacity weight backlogged)) :
    ∀ a b : ℝ,
      IntervalIntegrable
        (gpsBackloggedClassRate ι tag capacity weight backlogged)
        MeasureTheory.volume a b := by
  classical
  let rate := gpsBackloggedClassRate ι tag capacity weight backlogged
  let snapshotRate : (ι → Bool) → ℝ :=
    fun b =>
      idealGPSClassRate capacity (weight tag)
        ((Finset.univ.filter (fun i => b i = true)).sum weight)
  have hsubset_norm :
      Set.range (fun t : ℝ => ‖rate t‖) ⊆
        Set.range (fun b : ι → Bool => ‖snapshotRate b‖) := by
    rintro y ⟨t, rfl⟩
    refine ⟨fun i => backlogged t i, ?_⟩
    simp [rate, snapshotRate, gpsBackloggedClassRate,
      gpsBackloggedWeightSum, gpsBackloggedClasses]
  have hbdd_snapshot :
      BddAbove (Set.range (fun b : ι → Bool => ‖snapshotRate b‖)) :=
    (Set.finite_range (fun b : ι → Bool => ‖snapshotRate b‖)).bddAbove
  have hbdd_rate : BddAbove (Set.range (fun t : ℝ => ‖rate t‖)) :=
    BddAbove.mono hsubset_norm hbdd_snapshot
  rcases hbdd_rate with ⟨C, hC⟩
  have hintegrable_Icc : ∀ a b : ℝ,
      MeasureTheory.IntegrableOn rate (Set.Icc a b) MeasureTheory.volume := by
    intro a b
    refine MeasureTheory.IntegrableOn.of_bound
      (μ := MeasureTheory.volume) (s := Set.Icc a b)
      measure_Icc_lt_top hmeas.aestronglyMeasurable.restrict C ?_
    filter_upwards with t
    exact hC ⟨t, rfl⟩
  intro a b
  by_cases hab : a ≤ b
  · rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    exact hintegrable_Icc a b
  · have hba : b ≤ a := le_of_not_ge hab
    rw [IntervalIntegrable.symm_iff]
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hba]
    exact hintegrable_Icc b a

/--
If each finite class backlog indicator is measurable, then the induced GPS
weight denominator is measurable.
-/
theorem gpsBackloggedWeightSum_measurable
    {ι : Type*} [Fintype ι]
    (weight : ι → ℝ) (backlogged : ℝ → ι → Bool)
    (hbacklogged_meas : ∀ i, Measurable (fun t => backlogged t i)) :
    Measurable (gpsBackloggedWeightSum ι weight backlogged) := by
  classical
  have hsum : Measurable
      (fun t : ℝ =>
        (Finset.univ : Finset ι).sum
          (fun i => if backlogged t i = true then weight i else 0)) := by
    exact Finset.measurable_sum Finset.univ fun i _ =>
      Measurable.ite
        ((MeasurableSet.singleton true).preimage (hbacklogged_meas i))
        measurable_const measurable_const
  convert hsum using 1
  funext t
  simp [gpsBackloggedWeightSum, gpsBackloggedClasses, Finset.sum_filter]

/--
If each finite class backlog indicator is measurable, then the finite-state
backlog-induced GPS rate is measurable.
-/
theorem gpsBackloggedClassRate_measurable
    {ι : Type*} [Fintype ι]
    (tag : ι) (capacity : ℝ) (weight : ι → ℝ)
    (backlogged : ℝ → ι → Bool)
    (hbacklogged_meas : ∀ i, Measurable (fun t => backlogged t i)) :
    Measurable (gpsBackloggedClassRate ι tag capacity weight backlogged) := by
  unfold gpsBackloggedClassRate idealGPSClassRate
  exact measurable_const.div
    (gpsBackloggedWeightSum_measurable weight backlogged hbacklogged_meas)

/--
Per-class measurable backlog indicators are enough to make the finite
backlog-induced GPS rate locally interval-integrable on all bounded intervals.
-/
theorem gpsBackloggedClassRate_intervalIntegrable_all_of_backlogged_measurable
    {ι : Type*} [Fintype ι]
    (tag : ι) (capacity : ℝ) (weight : ι → ℝ)
    (backlogged : ℝ → ι → Bool)
    (hbacklogged_meas : ∀ i, Measurable (fun t => backlogged t i)) :
    ∀ a b : ℝ,
      IntervalIntegrable
        (gpsBackloggedClassRate ι tag capacity weight backlogged)
        MeasureTheory.volume a b :=
  gpsBackloggedClassRate_intervalIntegrable_all_of_measurable tag capacity
    weight backlogged
    (gpsBackloggedClassRate_measurable tag capacity weight backlogged
      hbacklogged_meas)

/-- A positive weighted capacity with nonnegative weight implies positive
weight. -/
theorem weight_pos_of_mul_pos_of_nonneg {capacity weight : ℝ}
    (hweight_nonneg : 0 ≤ weight) (hpos : 0 < capacity * weight) :
    0 < weight := by
  by_contra hnot
  have hle : weight ≤ 0 := le_of_not_gt hnot
  have hzero : weight = 0 := le_antisymm hle hweight_nonneg
  rw [hzero, mul_zero] at hpos
  exact (lt_irrefl (0 : ℝ)) hpos

/-- A positive weighted capacity with nonnegative weight implies positive capacity. -/
theorem capacity_pos_of_mul_pos_of_nonneg {capacity weight : ℝ}
    (hweight_nonneg : 0 ≤ weight) (hpos : 0 < capacity * weight) :
    0 < capacity := by
  by_contra hnot
  have hcapacity_nonpos : capacity ≤ 0 := le_of_not_gt hnot
  have hproduct_nonpos : capacity * weight ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hcapacity_nonpos hweight_nonneg
  exact (not_lt_of_ge hproduct_nonpos) hpos

/-- A true backlog indicator puts the class in the finite active set. -/
theorem mem_gpsBackloggedClasses_of_eq_true
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {backlogged : ℝ → ι → Bool} {t : ℝ} {i : ι}
    (hbacklogged : backlogged t i = true) :
    i ∈ gpsBackloggedClasses ι backlogged t := by
  simp [gpsBackloggedClasses, hbacklogged]

/-- If the tagged class is backlogged, its weight is included in the
backlog-induced GPS denominator. -/
theorem weight_le_gpsBackloggedWeightSum_of_tag_backlogged
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {tag : ι} {weight : ι → ℝ} {backlogged : ℝ → ι → Bool} {t : ℝ}
    (hweight_nonneg : ∀ i, 0 ≤ weight i)
    (htag_backlogged : backlogged t tag = true) :
    weight tag ≤ gpsBackloggedWeightSum ι weight backlogged t := by
  exact Finset.single_le_sum
    (fun i _ => hweight_nonneg i)
    (mem_gpsBackloggedClasses_of_eq_true htag_backlogged)

/-- If the tagged class has positive weight and is backlogged, then the
backlog-induced GPS denominator is positive. -/
theorem gpsBackloggedWeightSum_pos_of_tag_backlogged
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {tag : ι} {weight : ι → ℝ} {backlogged : ℝ → ι → Bool} {t : ℝ}
    (hweight_nonneg : ∀ i, 0 ≤ weight i)
    (htagged_weight_pos : 0 < weight tag)
    (htag_backlogged : backlogged t tag = true) :
    0 < gpsBackloggedWeightSum ι weight backlogged t :=
  lt_of_lt_of_le htagged_weight_pos
    (weight_le_gpsBackloggedWeightSum_of_tag_backlogged
      hweight_nonneg htag_backlogged)

/-- The backlog-induced GPS denominator is bounded by the total class weight. -/
theorem gpsBackloggedWeightSum_le_univ_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (weight : ι → ℝ) (backlogged : ℝ → ι → Bool) (t : ℝ)
    (hweight_nonneg : ∀ i, 0 ≤ weight i) :
    gpsBackloggedWeightSum ι weight backlogged t ≤ Finset.univ.sum weight := by
  exact Finset.sum_le_univ_sum_of_nonneg
    (s := gpsBackloggedClasses ι backlogged t) (f := weight)
    (fun i => hweight_nonneg i)

/-- The backlog-induced GPS denominator is at most one when total class weight
is at most one. -/
theorem gpsBackloggedWeightSum_le_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (weight : ι → ℝ) (backlogged : ℝ → ι → Bool) (t : ℝ)
    (hweight_nonneg : ∀ i, 0 ≤ weight i)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1) :
    gpsBackloggedWeightSum ι weight backlogged t ≤ 1 :=
  (gpsBackloggedWeightSum_le_univ_sum weight backlogged t
    hweight_nonneg).trans htotal_weight_le_one

/-- The finite backlog-induced GPS denominator is nonnegative. -/
theorem gpsBackloggedWeightSum_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (weight : ι → ℝ) (backlogged : ℝ → ι → Bool) (t : ℝ)
    (hweight_nonneg : ∀ i, 0 ≤ weight i) :
    0 ≤ gpsBackloggedWeightSum ι weight backlogged t := by
  unfold gpsBackloggedWeightSum
  exact Finset.sum_nonneg fun i _hi => hweight_nonneg i

/-- The backlog-induced GPS class rate is nonnegative under nonnegative capacity and weights. -/
theorem gpsBackloggedClassRate_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {tag : ι} {capacity : ℝ} {weight : ι → ℝ}
    {backlogged : ℝ → ι → Bool} (t : ℝ)
    (hcapacity : 0 ≤ capacity)
    (hweight_nonneg : ∀ i, 0 ≤ weight i) :
    0 ≤ gpsBackloggedClassRate ι tag capacity weight backlogged t := by
  unfold gpsBackloggedClassRate idealGPSClassRate
  exact div_nonneg (mul_nonneg hcapacity (hweight_nonneg tag))
    (gpsBackloggedWeightSum_nonneg weight backlogged t hweight_nonneg)

/-- A backlogged tagged class receives at least its guaranteed GPS rate under
the backlog-induced normalized GPS rule. -/
theorem gpsBackloggedClassRate_ge_guaranteed_of_tag_backlogged
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {tag : ι} {capacity : ℝ} {weight : ι → ℝ}
    {backlogged : ℝ → ι → Bool} {t : ℝ}
    (hcapacity : 0 ≤ capacity)
    (hweight_nonneg : ∀ i, 0 ≤ weight i)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hguaranteed_rate_pos : 0 < capacity * weight tag)
    (htag_backlogged : backlogged t tag = true) :
    capacity * weight tag ≤
      gpsBackloggedClassRate ι tag capacity weight backlogged t := by
  have htagged_weight_pos : 0 < weight tag :=
    weight_pos_of_mul_pos_of_nonneg
      (hweight_nonneg tag) hguaranteed_rate_pos
  exact idealGPSClassRate_ge_guaranteed hcapacity (hweight_nonneg tag)
    (gpsBackloggedWeightSum_pos_of_tag_backlogged
      hweight_nonneg htagged_weight_pos htag_backlogged)
    (gpsBackloggedWeightSum_le_one weight backlogged t
      hweight_nonneg htotal_weight_le_one)

/-- A backlogged tagged class has nonnegative backlog-induced GPS rate. -/
theorem gpsBackloggedClassRate_nonneg_of_tag_backlogged
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {tag : ι} {capacity : ℝ} {weight : ι → ℝ}
    {backlogged : ℝ → ι → Bool} {t : ℝ}
    (hcapacity : 0 ≤ capacity)
    (hweight_nonneg : ∀ i, 0 ≤ weight i)
    (htagged_weight_pos : 0 < weight tag)
    (htag_backlogged : backlogged t tag = true) :
    0 ≤ gpsBackloggedClassRate ι tag capacity weight backlogged t := by
  have hden_pos :=
    gpsBackloggedWeightSum_pos_of_tag_backlogged
      hweight_nonneg htagged_weight_pos htag_backlogged
  unfold gpsBackloggedClassRate idealGPSClassRate
  exact div_nonneg (mul_nonneg hcapacity (hweight_nonneg tag))
    hden_pos.le

/-- A backlogged tagged class receives no more than the whole server capacity
under the backlog-induced normalized GPS rate. -/
theorem gpsBackloggedClassRate_le_capacity_of_tag_backlogged
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {tag : ι} {capacity : ℝ} {weight : ι → ℝ}
    {backlogged : ℝ → ι → Bool} {t : ℝ}
    (hcapacity : 0 ≤ capacity)
    (hweight_nonneg : ∀ i, 0 ≤ weight i)
    (htagged_weight_pos : 0 < weight tag)
    (htag_backlogged : backlogged t tag = true) :
    gpsBackloggedClassRate ι tag capacity weight backlogged t ≤ capacity := by
  have hden_pos :=
    gpsBackloggedWeightSum_pos_of_tag_backlogged
      hweight_nonneg htagged_weight_pos htag_backlogged
  have hweight_le_den :=
    weight_le_gpsBackloggedWeightSum_of_tag_backlogged
      hweight_nonneg htag_backlogged
  unfold gpsBackloggedClassRate idealGPSClassRate
  rw [div_le_iff₀ hden_pos]
  exact mul_le_mul_of_nonneg_left hweight_le_den hcapacity

/-- On a tagged-backlogged time, the backlog-induced GPS tagged rate lies
between zero and the full server capacity. -/
theorem gpsBackloggedClassRate_mem_Icc_of_tag_backlogged
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {tag : ι} {capacity : ℝ} {weight : ι → ℝ}
    {backlogged : ℝ → ι → Bool} {t : ℝ}
    (hcapacity : 0 ≤ capacity)
    (hweight_nonneg : ∀ i, 0 ≤ weight i)
    (hguaranteed_rate_pos : 0 < capacity * weight tag)
    (htag_backlogged : backlogged t tag = true) :
    gpsBackloggedClassRate ι tag capacity weight backlogged t ∈
      Set.Icc 0 capacity := by
  have htagged_weight_pos : 0 < weight tag :=
    weight_pos_of_mul_pos_of_nonneg
      (hweight_nonneg tag) hguaranteed_rate_pos
  exact ⟨
    gpsBackloggedClassRate_nonneg_of_tag_backlogged
      hcapacity hweight_nonneg htagged_weight_pos htag_backlogged,
    gpsBackloggedClassRate_le_capacity_of_tag_backlogged
      hcapacity hweight_nonneg htagged_weight_pos htag_backlogged⟩

/--
Lebesgue-a.e. points of a closed service interval lie in the corresponding
open interval.  The only excluded points are the two endpoints.
-/
theorem ae_mem_Ioo_restrict_Icc (a b : ℝ) :
    ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc a b)),
      t ∈ Set.Ioo a b := by
  rw [MeasureTheory.ae_iff]
  rw [MeasureTheory.Measure.restrict_apply' measurableSet_Icc]
  refine MeasureTheory.measure_mono_null (t := ({a} ∪ {b} : Set ℝ)) ?_ ?_
  · intro x hx
    rcases hx with ⟨hx_not_open, hx_closed⟩
    simp only [Set.mem_setOf_eq, Set.mem_Ioo, Set.mem_Icc] at hx_not_open hx_closed
    have hboundary : x = a ∨ x = b := by
      rcases not_and_or.mp hx_not_open with hleft | hright
      · left
        exact le_antisymm (le_of_not_gt hleft) hx_closed.1
      · right
        exact le_antisymm hx_closed.2 (le_of_not_gt hright)
    rcases hboundary with rfl | rfl <;> simp
  · exact MeasureTheory.measure_union_null
      (MeasureTheory.measure_singleton a) (MeasureTheory.measure_singleton b)

/--
A pointwise property on the open service interval holds a.e. on the closed
service interval, since the endpoints have zero Lebesgue measure.
-/
theorem ae_restrict_Icc_of_forall_mem_Ioo {p : ℝ → Prop} {a b : ℝ}
    (hp : ∀ t, t ∈ Set.Ioo a b → p t) :
    ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc a b)), p t := by
  filter_upwards [ae_mem_Ioo_restrict_Icc a b] with t ht
  exact hp t ht

/--
Local tagged-job GPS source data with active classes defined by backlog
indicators.  This is closer to the manuscript model than an abstract active
set: at each time, the denominator is the sum of weights of classes currently
backlogged.
-/
structure TaggedJobAENormalizedGPSBacklogSourcePath
    (ι : Type*) [Fintype ι] [DecidableEq ι]
    (tag : ι) (initialBusyUntil : ℝ) (arrival work departure : ℕ → ℝ)
    (capacity : ℝ) (weight : ι → ℝ) where
  capacity_nonneg : 0 ≤ capacity
  weight_nonneg : ∀ i, 0 ≤ weight i
  total_weight_le_one : Finset.univ.sum weight ≤ 1
  tagged_guaranteed_rate_pos : 0 < capacity * weight tag
  actualServiceStart : ℝ
  arrival_le_actualServiceStart : arrival 0 ≤ actualServiceStart
  departure_after_actualServiceStart : actualServiceStart ≤ departure 0
  actualStart_le_comparatorStart :
    actualServiceStart ≤ max (arrival 0) initialBusyUntil
  backlogged : ℝ → ι → Bool
  instantaneousClassRate : ℝ → ℝ
  service : ℝ → ℝ
  rate_intervalIntegrable :
    IntervalIntegrable instantaneousClassRate MeasureTheory.volume
      actualServiceStart (departure 0)
  ae_tag_backlogged_on_actual_job :
    ∀ᵐ t ∂(MeasureTheory.volume.restrict
      (Set.Icc actualServiceStart (departure 0))),
      backlogged t tag = true
  ae_gps_allocation_on_actual_job :
    ∀ᵐ t ∂(MeasureTheory.volume.restrict
      (Set.Icc actualServiceStart (departure 0))),
      instantaneousClassRate t =
        idealGPSClassRate capacity (weight tag)
          (gpsBackloggedWeightSum ι weight backlogged t)
  service_increment_eq_integral :
    service (departure 0) - service actualServiceStart =
      ∫ t in actualServiceStart..departure 0, instantaneousClassRate t
  completed_work_eq_service :
    service (departure 0) - service actualServiceStart = work 0

namespace TaggedJobAENormalizedGPSBacklogSourcePath

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {tag : ι} {initialBusyUntil capacity : ℝ}
variable {arrival work departure : ℕ → ℝ} {weight : ι → ℝ}

/--
Backlog indicators instantiate the finite active-class source path by taking
the active classes to be the currently backlogged classes.
-/
def toTaggedJobAENormalizedGPSSourcePath
    (H : TaggedJobAENormalizedGPSBacklogSourcePath ι tag initialBusyUntil
      arrival work departure capacity weight) :
    TaggedJobAENormalizedGPSSourcePath ι tag initialBusyUntil arrival work departure
      capacity weight where
  capacity_nonneg := H.capacity_nonneg
  weight_nonneg := H.weight_nonneg
  total_weight_le_one := H.total_weight_le_one
  tagged_guaranteed_rate_pos := H.tagged_guaranteed_rate_pos
  actualServiceStart := H.actualServiceStart
  arrival_le_actualServiceStart := H.arrival_le_actualServiceStart
  departure_after_actualServiceStart := H.departure_after_actualServiceStart
  actualStart_le_comparatorStart := H.actualStart_le_comparatorStart
  activeClasses := gpsBackloggedClasses ι H.backlogged
  activeWeightSum := gpsBackloggedWeightSum ι weight H.backlogged
  instantaneousClassRate := H.instantaneousClassRate
  service := H.service
  rate_intervalIntegrable := H.rate_intervalIntegrable
  ae_tag_active_on_actual_job := by
    filter_upwards [H.ae_tag_backlogged_on_actual_job] with t htag
    simpa [gpsBackloggedClasses] using htag
  ae_activeWeightSum_eq_on_actual_job := by
    filter_upwards with t
    rfl
  ae_gps_allocation_on_actual_job := H.ae_gps_allocation_on_actual_job
  service_increment_eq_integral := H.service_increment_eq_integral
  completed_work_eq_service := H.completed_work_eq_service

/--
The backlog-indicator source model bounds the tagged response by the
initial-workload FCFS comparator.
-/
theorem responseTime_zero_le_fcfsResponseTimeFrom
    (H : TaggedJobAENormalizedGPSBacklogSourcePath ι tag initialBusyUntil
      arrival work departure capacity weight) :
    responseTime arrival departure 0 ≤
      responseTime arrival
        (fcfsDepartureFrom initialBusyUntil arrival work (capacity * weight tag)) 0 :=
  H.toTaggedJobAENormalizedGPSSourcePath.responseTime_zero_le_fcfsResponseTimeFrom

end TaggedJobAENormalizedGPSBacklogSourcePath

/--
Local tagged-job GPS source data where the tagged class is required to be
backlogged pointwise on the open service interval.  This is the open-interval
variant of `TaggedJobAENormalizedGPSBacklogSourcePath`; endpoint values are
irrelevant for the a.e. allocation proof.
-/
structure TaggedJobAENormalizedGPSOpenBacklogSourcePath
    (ι : Type*) [Fintype ι] [DecidableEq ι]
    (tag : ι) (initialBusyUntil : ℝ) (arrival work departure : ℕ → ℝ)
    (capacity : ℝ) (weight : ι → ℝ) where
  capacity_nonneg : 0 ≤ capacity
  weight_nonneg : ∀ i, 0 ≤ weight i
  total_weight_le_one : Finset.univ.sum weight ≤ 1
  tagged_guaranteed_rate_pos : 0 < capacity * weight tag
  actualServiceStart : ℝ
  arrival_le_actualServiceStart : arrival 0 ≤ actualServiceStart
  departure_after_actualServiceStart : actualServiceStart ≤ departure 0
  actualStart_le_comparatorStart :
    actualServiceStart ≤ max (arrival 0) initialBusyUntil
  backlogged : ℝ → ι → Bool
  instantaneousClassRate : ℝ → ℝ
  service : ℝ → ℝ
  rate_intervalIntegrable :
    IntervalIntegrable instantaneousClassRate MeasureTheory.volume
      actualServiceStart (departure 0)
  tag_backlogged_on_open_actual_job :
    ∀ t, t ∈ Set.Ioo actualServiceStart (departure 0) →
      backlogged t tag = true
  ae_gps_allocation_on_actual_job :
    ∀ᵐ t ∂(MeasureTheory.volume.restrict
      (Set.Icc actualServiceStart (departure 0))),
      instantaneousClassRate t =
        idealGPSClassRate capacity (weight tag)
          (gpsBackloggedWeightSum ι weight backlogged t)
  service_increment_eq_integral :
    service (departure 0) - service actualServiceStart =
      ∫ t in actualServiceStart..departure 0, instantaneousClassRate t
  completed_work_eq_service :
    service (departure 0) - service actualServiceStart = work 0

namespace TaggedJobAENormalizedGPSOpenBacklogSourcePath

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {tag : ι} {initialBusyUntil capacity : ℝ}
variable {arrival work departure : ℕ → ℝ} {weight : ι → ℝ}

/--
The open-interval source condition supplies the closed-interval a.e. backlog
condition used by the finite active-class proof.
-/
def toTaggedJobAENormalizedGPSBacklogSourcePath
    (H : TaggedJobAENormalizedGPSOpenBacklogSourcePath ι tag initialBusyUntil
      arrival work departure capacity weight) :
    TaggedJobAENormalizedGPSBacklogSourcePath ι tag initialBusyUntil
      arrival work departure capacity weight where
  capacity_nonneg := H.capacity_nonneg
  weight_nonneg := H.weight_nonneg
  total_weight_le_one := H.total_weight_le_one
  tagged_guaranteed_rate_pos := H.tagged_guaranteed_rate_pos
  actualServiceStart := H.actualServiceStart
  arrival_le_actualServiceStart := H.arrival_le_actualServiceStart
  departure_after_actualServiceStart := H.departure_after_actualServiceStart
  actualStart_le_comparatorStart := H.actualStart_le_comparatorStart
  backlogged := H.backlogged
  instantaneousClassRate := H.instantaneousClassRate
  service := H.service
  rate_intervalIntegrable := H.rate_intervalIntegrable
  ae_tag_backlogged_on_actual_job :=
    ae_restrict_Icc_of_forall_mem_Ioo H.tag_backlogged_on_open_actual_job
  ae_gps_allocation_on_actual_job := H.ae_gps_allocation_on_actual_job
  service_increment_eq_integral := H.service_increment_eq_integral
  completed_work_eq_service := H.completed_work_eq_service

/--
The open-backlog source model bounds the tagged response by the initial-workload
FCFS comparator.
-/
theorem responseTime_zero_le_fcfsResponseTimeFrom
    (H : TaggedJobAENormalizedGPSOpenBacklogSourcePath ι tag initialBusyUntil
      arrival work departure capacity weight) :
    responseTime arrival departure 0 ≤
      responseTime arrival
        (fcfsDepartureFrom initialBusyUntil arrival work (capacity * weight tag)) 0 :=
  H.toTaggedJobAENormalizedGPSBacklogSourcePath.responseTime_zero_le_fcfsResponseTimeFrom

end TaggedJobAENormalizedGPSOpenBacklogSourcePath

/--
Local tagged-job GPS source data with backlog-induced class rate and cumulative
service defined by the integral of that rate.  This is closer to the physical
fluid queue than `TaggedJobAENormalizedGPSOpenBacklogSourcePath`: the only
remaining work-completion input is the statement that the tagged job's
backlog-induced cumulative service reaches its work at departure.
-/
structure TaggedJobGPSOpenBacklogIntegralSourcePath
    (ι : Type*) [Fintype ι] [DecidableEq ι]
    (tag : ι) (initialBusyUntil : ℝ) (arrival work departure : ℕ → ℝ)
    (capacity : ℝ) (weight : ι → ℝ) where
  capacity_nonneg : 0 ≤ capacity
  weight_nonneg : ∀ i, 0 ≤ weight i
  total_weight_le_one : Finset.univ.sum weight ≤ 1
  tagged_guaranteed_rate_pos : 0 < capacity * weight tag
  actualServiceStart : ℝ
  arrival_le_actualServiceStart : arrival 0 ≤ actualServiceStart
  departure_after_actualServiceStart : actualServiceStart ≤ departure 0
  actualStart_le_comparatorStart :
    actualServiceStart ≤ max (arrival 0) initialBusyUntil
  backlogged : ℝ → ι → Bool
  rate_intervalIntegrable :
    IntervalIntegrable
      (gpsBackloggedClassRate ι tag capacity weight backlogged)
      MeasureTheory.volume actualServiceStart (departure 0)
  tag_backlogged_on_open_actual_job :
    ∀ t, t ∈ Set.Ioo actualServiceStart (departure 0) →
      backlogged t tag = true
  service_integral_eq_work :
    ∫ t in actualServiceStart..departure 0,
        gpsBackloggedClassRate ι tag capacity weight backlogged t = work 0

namespace TaggedJobGPSOpenBacklogIntegralSourcePath

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {tag : ι} {initialBusyUntil capacity : ℝ}
variable {arrival work departure : ℕ → ℝ} {weight : ι → ℝ}

/-- Times at which cumulative tagged service from `start` has reached `work`. -/
def cumulativeServiceHitSet
    (start work : ℝ) (cumulativeService : ℝ → ℝ) : Set ℝ :=
  {t | start ≤ t ∧ work ≤ cumulativeService t}

/-- First hitting time of a cumulative-service work threshold. -/
def cumulativeServiceFirstHitTime
    (start work : ℝ) (cumulativeService : ℝ → ℝ) : ℝ :=
  sInf (cumulativeServiceHitSet start work cumulativeService)

/--
The source-level statement that `departureTime` is the first hitting time of
the cumulative-service work threshold, with a finite hit witness.
-/
def cumulativeServiceFirstHitAt
    (start work : ℝ) (cumulativeService : ℝ → ℝ)
    (departureTime : ℝ) : Prop :=
  departureTime = cumulativeServiceFirstHitTime start work cumulativeService ∧
    (cumulativeServiceHitSet start work cumulativeService).Nonempty

/-- A concrete reachability witness makes the cumulative-service hit set nonempty. -/
theorem cumulativeServiceHitSet_nonempty_of_reaches
    {start jobWork witness : ℝ} {cumulativeService : ℝ → ℝ}
    (hstart : start ≤ witness)
    (hreaches : jobWork ≤ cumulativeService witness) :
    (cumulativeServiceHitSet start jobWork cumulativeService).Nonempty :=
  ⟨witness, hstart, hreaches⟩

/--
Construct the first-hit-at source statement from the first-hit-time definition
and a finite reachability witness.
-/
theorem cumulativeServiceFirstHitAt_of_eq_firstHitTime_of_reaches
    {start jobWork departureTime witness : ℝ}
    {cumulativeService : ℝ → ℝ}
    (hdeparture :
      departureTime =
        cumulativeServiceFirstHitTime start jobWork cumulativeService)
    (hstart : start ≤ witness)
    (hreaches : jobWork ≤ cumulativeService witness) :
    cumulativeServiceFirstHitAt start jobWork cumulativeService departureTime :=
  ⟨hdeparture, cumulativeServiceHitSet_nonempty_of_reaches hstart hreaches⟩

/--
For a continuous cumulative-service path, the set of times at which the tagged
job has received at least its required work is closed.
-/
theorem cumulativeServiceHitSet_isClosed_of_continuous
    {start jobWork : ℝ} {cumulativeService : ℝ → ℝ}
    (hcontinuous : Continuous cumulativeService) :
    IsClosed (cumulativeServiceHitSet start jobWork cumulativeService) := by
  change IsClosed
    ({t : ℝ | start ≤ t} ∩ {t : ℝ | jobWork ≤ cumulativeService t})
  exact isClosed_Ici.inter (isClosed_Ici.preimage hcontinuous)

/--
For a continuous cumulative-service path, the first hitting time defined as the
infimum of the nonempty hit set is the least hit.
-/
theorem isLeast_sInf_cumulativeServiceHitSet_of_continuous
    {start jobWork : ℝ} {cumulativeService : ℝ → ℝ}
    (hcontinuous : Continuous cumulativeService)
    (hnonempty :
      (cumulativeServiceHitSet start jobWork cumulativeService).Nonempty) :
    IsLeast (cumulativeServiceHitSet start jobWork cumulativeService)
      (sInf (cumulativeServiceHitSet start jobWork cumulativeService)) := by
  refine (cumulativeServiceHitSet_isClosed_of_continuous
    (start := start) (jobWork := jobWork)
    (cumulativeService := cumulativeService) hcontinuous).isLeast_csInf
      hnonempty ?_
  exact ⟨start, fun t ht => ht.1⟩

/--
A continuous cumulative-service path turns the source-level first-hit-time
definition into the least-hit property used by the pathwise GPS comparison.
-/
theorem cumulativeServiceFirstHitAt_isLeast_of_continuous
    {start jobWork departureTime : ℝ} {cumulativeService : ℝ → ℝ}
    (hcontinuous : Continuous cumulativeService)
    (hfirst :
      cumulativeServiceFirstHitAt start jobWork cumulativeService
        departureTime) :
    IsLeast (cumulativeServiceHitSet start jobWork cumulativeService)
      departureTime := by
  rw [hfirst.1]
  change IsLeast (cumulativeServiceHitSet start jobWork cumulativeService)
    (sInf (cumulativeServiceHitSet start jobWork cumulativeService))
  exact isLeast_sInf_cumulativeServiceHitSet_of_continuous
    (start := start) (jobWork := jobWork)
    (cumulativeService := cumulativeService) hcontinuous hfirst.2

/--
Chronological GPS departure recurrence generated by backlog-induced class
rates.  Each job departs at the first time its cumulative class service from
its own service start reaches its work requirement.
-/
def gpsBackloggedDepartureFrom
    (initialBusyUntil : ℝ) (arrival work : ℕ → ℝ)
    (capacity : ℝ) (weight : ι → ℝ)
    (backlogged : ℝ → ι → Bool) : ℕ → ℝ
  | 0 =>
      let start := max (arrival 0) initialBusyUntil
      cumulativeServiceFirstHitTime start (work 0)
        (fun t =>
          ∫ u in start..t,
            gpsBackloggedClassRate ι tag capacity weight backlogged u)
  | n + 1 =>
      let start := max (arrival (n + 1))
        (gpsBackloggedDepartureFrom initialBusyUntil arrival work capacity
          weight backlogged n)
      cumulativeServiceFirstHitTime start (work (n + 1))
        (fun t =>
          ∫ u in start..t,
            gpsBackloggedClassRate ι tag capacity weight backlogged u)

/-- The zero-th chronological GPS departure is the first hit from the initial comparator start. -/
theorem gpsBackloggedDepartureFrom_zero
    (initialBusyUntil : ℝ) (arrival work : ℕ → ℝ)
    (capacity : ℝ) (weight : ι → ℝ)
    (backlogged : ℝ → ι → Bool) :
    gpsBackloggedDepartureFrom (ι := ι) (tag := tag)
      initialBusyUntil arrival work capacity weight backlogged 0 =
      cumulativeServiceFirstHitTime (max (arrival 0) initialBusyUntil)
        (work 0)
        (fun t =>
          ∫ u in (max (arrival 0) initialBusyUntil)..t,
            gpsBackloggedClassRate ι tag capacity weight backlogged u) :=
  rfl

/--
A finite hit witness shows that the zero-th chronological GPS departure
satisfies the source-level first-hit-time statement.
-/
theorem gpsBackloggedDepartureFrom_zero_firstHitAt_of_reaches
    {initialBusyUntil witness : ℝ} {arrival work : ℕ → ℝ}
    {capacity : ℝ} {weight : ι → ℝ}
    {backlogged : ℝ → ι → Bool}
    (hstart : max (arrival 0) initialBusyUntil ≤ witness)
    (hreaches :
      work 0 ≤
        ∫ u in (max (arrival 0) initialBusyUntil)..witness,
          gpsBackloggedClassRate ι tag capacity weight backlogged u) :
    cumulativeServiceFirstHitAt (max (arrival 0) initialBusyUntil)
      (work 0)
      (fun t =>
        ∫ u in (max (arrival 0) initialBusyUntil)..t,
          gpsBackloggedClassRate ι tag capacity weight backlogged u)
      (gpsBackloggedDepartureFrom (ι := ι) (tag := tag)
        initialBusyUntil arrival work capacity weight backlogged 0) :=
  cumulativeServiceFirstHitAt_of_eq_firstHitTime_of_reaches
    (by rfl) hstart hreaches

/-- The successor chronological GPS departure is the first hit from the next comparator start. -/
theorem gpsBackloggedDepartureFrom_succ
    (initialBusyUntil : ℝ) (arrival work : ℕ → ℝ)
    (capacity : ℝ) (weight : ι → ℝ)
    (backlogged : ℝ → ι → Bool) (n : ℕ) :
    gpsBackloggedDepartureFrom (ι := ι) (tag := tag)
      initialBusyUntil arrival work capacity weight backlogged (n + 1) =
      cumulativeServiceFirstHitTime
        (max (arrival (n + 1))
          (gpsBackloggedDepartureFrom (ι := ι) (tag := tag)
            initialBusyUntil arrival work capacity weight backlogged n))
        (work (n + 1))
        (fun t =>
          ∫ u in
            (max (arrival (n + 1))
              (gpsBackloggedDepartureFrom (ι := ι) (tag := tag)
                initialBusyUntil arrival work capacity weight backlogged n))..t,
            gpsBackloggedClassRate ι tag capacity weight backlogged u) :=
  rfl

/--
A finite hit witness shows that a successor chronological GPS departure
satisfies the source-level first-hit-time statement.
-/
theorem gpsBackloggedDepartureFrom_succ_firstHitAt_of_reaches
    {initialBusyUntil witness : ℝ} {arrival work : ℕ → ℝ}
    {capacity : ℝ} {weight : ι → ℝ}
    {backlogged : ℝ → ι → Bool} {n : ℕ}
    (hstart :
      max (arrival (n + 1))
        (gpsBackloggedDepartureFrom (ι := ι) (tag := tag)
          initialBusyUntil arrival work capacity weight backlogged n) ≤
        witness)
    (hreaches :
      work (n + 1) ≤
        ∫ u in
          (max (arrival (n + 1))
            (gpsBackloggedDepartureFrom (ι := ι) (tag := tag)
              initialBusyUntil arrival work capacity weight backlogged n))..witness,
          gpsBackloggedClassRate ι tag capacity weight backlogged u) :
    cumulativeServiceFirstHitAt
      (max (arrival (n + 1))
        (gpsBackloggedDepartureFrom (ι := ι) (tag := tag)
          initialBusyUntil arrival work capacity weight backlogged n))
      (work (n + 1))
      (fun t =>
        ∫ u in
          (max (arrival (n + 1))
            (gpsBackloggedDepartureFrom (ι := ι) (tag := tag)
              initialBusyUntil arrival work capacity weight backlogged n))..t,
          gpsBackloggedClassRate ι tag capacity weight backlogged u)
      (gpsBackloggedDepartureFrom (ι := ι) (tag := tag)
        initialBusyUntil arrival work capacity weight backlogged (n + 1)) :=
  cumulativeServiceFirstHitAt_of_eq_firstHitTime_of_reaches
    (by rfl) hstart hreaches

/--
If the tagged class is backlogged throughout an open interval and its
guaranteed GPS work over that interval covers `jobWork`, then cumulative
tagged GPS service reaches `jobWork` by the end of the interval.
-/
theorem cumulativeService_reaches_of_tag_backlogged_on_open
    {start finish jobWork capacity : ℝ} {weight : ι → ℝ}
    {backlogged : ℝ → ι → Bool}
    (hcapacity : 0 ≤ capacity)
    (hweight_nonneg : ∀ i, 0 ≤ weight i)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (htagged_guaranteed_rate_pos : 0 < capacity * weight tag)
    (hstart_finish : start ≤ finish)
    (hrate_integrable :
      IntervalIntegrable
        (gpsBackloggedClassRate ι tag capacity weight backlogged)
        MeasureTheory.volume start finish)
    (htag_backlogged : ∀ t, t ∈ Set.Ioo start finish →
      backlogged t tag = true)
    (hwork_le_floor :
      jobWork ≤ capacity * weight tag * (finish - start)) :
    jobWork ≤
      ∫ u in start..finish,
        gpsBackloggedClassRate ι tag capacity weight backlogged u := by
  have htag_ae :
      ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc start finish)),
        backlogged t tag = true :=
    ae_restrict_Icc_of_forall_mem_Ioo htag_backlogged
  have hfloor_ae :
      ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc start finish)),
        capacity * weight tag ≤
          gpsBackloggedClassRate ι tag capacity weight backlogged t := by
    filter_upwards [htag_ae] with t htag
    exact gpsBackloggedClassRate_ge_guaranteed_of_tag_backlogged
      hcapacity hweight_nonneg htotal_weight_le_one
      htagged_guaranteed_rate_pos htag
  exact hwork_le_floor.trans
    (intervalIntegral_ge_const_of_ae_le hstart_finish hrate_integrable
      hfloor_ae)

/--
If the tagged class is backlogged through its guaranteed service window, then
that window is a finite hit witness for the cumulative tagged GPS service.
-/
theorem cumulativeService_reaches_at_guaranteedWindow_of_tag_backlogged_on_open
    {start jobWork capacity : ℝ} {weight : ι → ℝ}
    {backlogged : ℝ → ι → Bool}
    (hcapacity : 0 ≤ capacity)
    (hweight_nonneg : ∀ i, 0 ≤ weight i)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (htagged_guaranteed_rate_pos : 0 < capacity * weight tag)
    (hwork_nonneg : 0 ≤ jobWork)
    (hrate_integrable :
      IntervalIntegrable
        (gpsBackloggedClassRate ι tag capacity weight backlogged)
          MeasureTheory.volume start
        (start + jobWork / (capacity * weight tag)))
    (htag_backlogged : ∀ t,
      t ∈ Set.Ioo start (start + jobWork / (capacity * weight tag)) →
        backlogged t tag = true) :
    jobWork ≤
      ∫ u in start..(start + jobWork / (capacity * weight tag)),
        gpsBackloggedClassRate ι tag capacity weight backlogged u := by
  have hrate_pos : 0 < capacity * weight tag :=
    htagged_guaranteed_rate_pos
  have hstart_finish :
      start ≤ start + jobWork / (capacity * weight tag) := by
    have hdiv_nonneg :
        0 ≤ jobWork / (capacity * weight tag) :=
      div_nonneg hwork_nonneg hrate_pos.le
    linarith
  have hfloor_eq :
      capacity * weight tag *
          ((start + jobWork / (capacity * weight tag)) - start) =
        jobWork := by
    have hne : capacity * weight tag ≠ 0 := ne_of_gt hrate_pos
    rw [add_sub_cancel_left, mul_div_cancel₀ jobWork hne]
  exact
    cumulativeService_reaches_of_tag_backlogged_on_open
      (tag := tag) hcapacity hweight_nonneg htotal_weight_le_one
      htagged_guaranteed_rate_pos hstart_finish hrate_integrable
      htag_backlogged (by rw [hfloor_eq])

/--
If an unfinished tagged job is marked backlogged throughout its guaranteed
service window, then cumulative tagged GPS service reaches the job's work by
the end of that window.
-/
theorem cumulativeService_reaches_at_guaranteedWindow_of_backlogged_if_unfinished
    {start jobWork capacity : ℝ} {weight : ι → ℝ}
    {backlogged : ℝ → ι → Bool}
    (hcapacity : 0 ≤ capacity)
    (hweight_nonneg : ∀ i, 0 ≤ weight i)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (htagged_guaranteed_rate_pos : 0 < capacity * weight tag)
    (hwork_nonneg : 0 ≤ jobWork)
    (hrate_integrable :
      IntervalIntegrable
        (gpsBackloggedClassRate ι tag capacity weight backlogged)
        MeasureTheory.volume start
        (start + jobWork / (capacity * weight tag)))
    (hbacklogged_of_unfinished : ∀ t,
      t ∈ Set.Ioo start (start + jobWork / (capacity * weight tag)) →
        (∫ u in start..t,
          gpsBackloggedClassRate ι tag capacity weight backlogged u) <
          jobWork →
        backlogged t tag = true) :
    jobWork ≤
      ∫ u in start..(start + jobWork / (capacity * weight tag)),
        gpsBackloggedClassRate ι tag capacity weight backlogged u := by
  let finish := start + jobWork / (capacity * weight tag)
  have hfinish_def : finish = start + jobWork / (capacity * weight tag) := rfl
  have hstart_finish : start ≤ finish := by
    have hdiv_nonneg : 0 ≤ jobWork / (capacity * weight tag) :=
      div_nonneg hwork_nonneg htagged_guaranteed_rate_pos.le
    dsimp [finish]
    linarith
  by_contra hnot
  have hfinish_lt_work :
      ∫ u in start..finish,
        gpsBackloggedClassRate ι tag capacity weight backlogged u < jobWork := by
    exact lt_of_not_ge (by simpa [finish] using hnot)
  have hrate_nonneg_ae :
      ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ioc start finish)),
        0 ≤ gpsBackloggedClassRate ι tag capacity weight backlogged t := by
    filter_upwards with t
    exact gpsBackloggedClassRate_nonneg t hcapacity hweight_nonneg
  have htag_backlogged : ∀ t, t ∈ Set.Ioo start finish →
      backlogged t tag = true := by
    intro t ht
    have hcum_le_finish :
        (∫ u in start..t,
          gpsBackloggedClassRate ι tag capacity weight backlogged u) ≤
          ∫ u in start..finish,
            gpsBackloggedClassRate ι tag capacity weight backlogged u := by
      exact
        intervalIntegral.integral_mono_interval
          (μ := MeasureTheory.volume)
          (f := gpsBackloggedClassRate ι tag capacity weight backlogged)
          (a := start) (b := t) (c := start) (d := finish)
          le_rfl ht.1.le ht.2.le hrate_nonneg_ae hrate_integrable
    exact hbacklogged_of_unfinished t (by simpa [finish] using ht)
      (lt_of_le_of_lt hcum_le_finish hfinish_lt_work)
  have hreach_finish :
      jobWork ≤
        ∫ u in start..finish,
          gpsBackloggedClassRate ι tag capacity weight backlogged u := by
    simpa [finish] using
      (cumulativeService_reaches_at_guaranteedWindow_of_tag_backlogged_on_open
        (tag := tag) hcapacity hweight_nonneg htotal_weight_le_one
        htagged_guaranteed_rate_pos hwork_nonneg hrate_integrable
        (by simpa [finish] using htag_backlogged))
  exact (not_lt_of_ge hreach_finish) hfinish_lt_work

/--
If `departure` is the first time cumulative service has reached the job's
work, then cumulative service is still strictly below the work at every
interior pre-departure time.
-/
theorem cumulativeService_lt_work_of_isLeast_hit
    {start jobWork departureTime : ℝ} {cumulativeService : ℝ → ℝ}
    (hfirst : IsLeast
      (cumulativeServiceHitSet start jobWork cumulativeService) departureTime)
    {t : ℝ} (ht : t ∈ Set.Ioo start departureTime) :
    cumulativeService t < jobWork := by
  by_contra hnot
  have hge : jobWork ≤ cumulativeService t := le_of_not_gt hnot
  have ht_hit : t ∈ cumulativeServiceHitSet start jobWork cumulativeService := by
    exact ⟨le_of_lt ht.1, hge⟩
  have hdeparture_le_t : departureTime ≤ t := hfirst.2 ht_hit
  exact (not_le_of_gt ht.2) hdeparture_le_t

/--
For a continuous cumulative-service path, a least-hit departure cannot
overshoot the tagged job's work.  Thus equality at departure follows from
least-hit plus the source fact that the cumulative service starts below work.
-/
theorem cumulativeService_eq_work_of_isLeast_hit_of_continuousAt
    {start jobWork departureTime : ℝ} {cumulativeService : ℝ → ℝ}
    (hfirst : IsLeast
      (cumulativeServiceHitSet start jobWork cumulativeService) departureTime)
    (hstart_below : cumulativeService start < jobWork)
    (hcontinuous : ContinuousAt cumulativeService departureTime) :
    cumulativeService departureTime = jobWork := by
  apply le_antisymm ?_ hfirst.1.2
  by_contra hnot
  have hgt : jobWork < cumulativeService departureTime := lt_of_not_ge hnot
  have hstart_lt_departure : start < departureTime := by
    have hne : start ≠ departureTime := by
      intro h
      have hhit_start : jobWork ≤ cumulativeService start := by
        simpa [h] using hfirst.1.2
      exact (not_lt_of_ge hhit_start) hstart_below
    exact lt_of_le_of_ne hfirst.1.1 hne
  have heventually_gt :
      ∀ᶠ t in 𝓝 departureTime, jobWork < cumulativeService t :=
    ContinuousAt.eventually_lt continuousAt_const hcontinuous hgt
  rcases (Metric.eventually_nhds_iff).1 heventually_gt with
    ⟨ε, hε_pos, hε⟩
  let δ := min (ε / 2) ((departureTime - start) / 2)
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    rw [lt_min_iff]
    constructor <;> linarith
  have hδ_nonneg : 0 ≤ δ := le_of_lt hδ_pos
  have hδ_le_ε : δ ≤ ε / 2 := by
    dsimp [δ]
    exact min_le_left _ _
  have hδ_le_start : δ ≤ (departureTime - start) / 2 := by
    dsimp [δ]
    exact min_le_right _ _
  let t := departureTime - δ
  have ht_dist : dist t departureTime < ε := by
    rw [Real.dist_eq]
    have habs : |t - departureTime| = δ := by
      dsimp [t]
      rw [sub_sub_cancel_left, abs_neg, abs_of_nonneg hδ_nonneg]
    rw [habs]
    linarith
  have ht_lt_departure : t < departureTime := by
    dsimp [t]
    linarith
  have hstart_le_t : start ≤ t := by
    dsimp [t]
    linarith
  have ht_hit : t ∈ cumulativeServiceHitSet start jobWork cumulativeService := by
    exact ⟨hstart_le_t, le_of_lt (hε ht_dist)⟩
  have hdeparture_le_t : departureTime ≤ t := hfirst.2 ht_hit
  exact (not_le_of_gt ht_lt_departure) hdeparture_le_t

/--
Build the integral open-backlog tagged-job source path from first-hit
cumulative-service facts.  The source process must prove that cumulative
tagged GPS service is still below the tagged job's work throughout the open
service interval and equals the job's work at departure.  The backlog field is
then only required to agree with unfinished tagged work on that open interval.
-/
def ofFirstHitCumulativeService
    (hcapacity : 0 ≤ capacity)
    (hweight_nonneg : ∀ i, 0 ≤ weight i)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (htagged_guaranteed_rate_pos : 0 < capacity * weight tag)
    (actualServiceStart : ℝ)
    (harrival_le_start : arrival 0 ≤ actualServiceStart)
    (hstart_le_departure : actualServiceStart ≤ departure 0)
    (hstart_le_comparator :
      actualServiceStart ≤ max (arrival 0) initialBusyUntil)
    (backlogged : ℝ → ι → Bool)
    (hrate_integrable :
      IntervalIntegrable
        (gpsBackloggedClassRate ι tag capacity weight backlogged)
        MeasureTheory.volume actualServiceStart (departure 0))
    (hbacklogged_of_unfinished : ∀ t,
      t ∈ Set.Ioo actualServiceStart (departure 0) →
        (∫ u in actualServiceStart..t,
          gpsBackloggedClassRate ι tag capacity weight backlogged u) < work 0 →
        backlogged t tag = true)
    (hcumulative_before_departure_lt_work : ∀ t,
      t ∈ Set.Ioo actualServiceStart (departure 0) →
        (∫ u in actualServiceStart..t,
          gpsBackloggedClassRate ι tag capacity weight backlogged u) < work 0)
    (hcumulative_at_departure_eq_work :
      ∫ u in actualServiceStart..departure 0,
        gpsBackloggedClassRate ι tag capacity weight backlogged u = work 0) :
    TaggedJobGPSOpenBacklogIntegralSourcePath ι tag initialBusyUntil
      arrival work departure capacity weight where
  capacity_nonneg := hcapacity
  weight_nonneg := hweight_nonneg
  total_weight_le_one := htotal_weight_le_one
  tagged_guaranteed_rate_pos := htagged_guaranteed_rate_pos
  actualServiceStart := actualServiceStart
  arrival_le_actualServiceStart := harrival_le_start
  departure_after_actualServiceStart := hstart_le_departure
  actualStart_le_comparatorStart := hstart_le_comparator
  backlogged := backlogged
  rate_intervalIntegrable := hrate_integrable
  tag_backlogged_on_open_actual_job := by
    intro t ht
    exact hbacklogged_of_unfinished t ht
      (hcumulative_before_departure_lt_work t ht)
  service_integral_eq_work := hcumulative_at_departure_eq_work

/--
Specialized first-hit constructor when the tagged service starts at the
comparison start `max (arrival 0) initialBusyUntil`.  This discharges the
arrival/start and comparator-start timing fields by definition, leaving the
source process to prove only departure after that start, rate integrability,
and the first-hit cumulative-service facts.
-/
def ofFirstHitFromComparatorStart
    (hcapacity : 0 ≤ capacity)
    (hweight_nonneg : ∀ i, 0 ≤ weight i)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (htagged_guaranteed_rate_pos : 0 < capacity * weight tag)
    (hstart_le_departure :
      max (arrival 0) initialBusyUntil ≤ departure 0)
    (backlogged : ℝ → ι → Bool)
    (hrate_integrable :
      IntervalIntegrable
        (gpsBackloggedClassRate ι tag capacity weight backlogged)
        MeasureTheory.volume (max (arrival 0) initialBusyUntil) (departure 0))
    (hbacklogged_of_unfinished : ∀ t,
      t ∈ Set.Ioo (max (arrival 0) initialBusyUntil) (departure 0) →
        (∫ u in (max (arrival 0) initialBusyUntil)..t,
          gpsBackloggedClassRate ι tag capacity weight backlogged u) < work 0 →
        backlogged t tag = true)
    (hcumulative_before_departure_lt_work : ∀ t,
      t ∈ Set.Ioo (max (arrival 0) initialBusyUntil) (departure 0) →
        (∫ u in (max (arrival 0) initialBusyUntil)..t,
          gpsBackloggedClassRate ι tag capacity weight backlogged u) < work 0)
    (hcumulative_at_departure_eq_work :
      ∫ u in (max (arrival 0) initialBusyUntil)..departure 0,
        gpsBackloggedClassRate ι tag capacity weight backlogged u = work 0) :
    TaggedJobGPSOpenBacklogIntegralSourcePath ι tag initialBusyUntil
      arrival work departure capacity weight :=
  ofFirstHitCumulativeService hcapacity hweight_nonneg htotal_weight_le_one
    htagged_guaranteed_rate_pos (max (arrival 0) initialBusyUntil)
    (le_max_left (arrival 0) initialBusyUntil) hstart_le_departure
    le_rfl backlogged hrate_integrable hbacklogged_of_unfinished
    hcumulative_before_departure_lt_work hcumulative_at_departure_eq_work

/--
Comparator-start constructor from a genuine first-hit characterization of the
departure time.  The least-hit premise replaces the separate source obligation
that cumulative tagged service is below the job's work before departure.
-/
def ofLeastHitFromComparatorStart
    (hcapacity : 0 ≤ capacity)
    (hweight_nonneg : ∀ i, 0 ≤ weight i)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (htagged_guaranteed_rate_pos : 0 < capacity * weight tag)
    (backlogged : ℝ → ι → Bool)
    (hrate_integrable :
      IntervalIntegrable
        (gpsBackloggedClassRate ι tag capacity weight backlogged)
        MeasureTheory.volume (max (arrival 0) initialBusyUntil) (departure 0))
    (hbacklogged_of_unfinished : ∀ t,
      t ∈ Set.Ioo (max (arrival 0) initialBusyUntil) (departure 0) →
        (∫ u in (max (arrival 0) initialBusyUntil)..t,
          gpsBackloggedClassRate ι tag capacity weight backlogged u) < work 0 →
        backlogged t tag = true)
    (hdeparture_isLeast_hit : IsLeast
      (cumulativeServiceHitSet
        (max (arrival 0) initialBusyUntil) (work 0)
        (fun t =>
          ∫ u in (max (arrival 0) initialBusyUntil)..t,
            gpsBackloggedClassRate ι tag capacity weight backlogged u))
      (departure 0))
    (hcumulative_at_departure_eq_work :
      ∫ u in (max (arrival 0) initialBusyUntil)..departure 0,
        gpsBackloggedClassRate ι tag capacity weight backlogged u = work 0) :
    TaggedJobGPSOpenBacklogIntegralSourcePath ι tag initialBusyUntil
      arrival work departure capacity weight :=
  ofFirstHitFromComparatorStart hcapacity hweight_nonneg htotal_weight_le_one
    htagged_guaranteed_rate_pos hdeparture_isLeast_hit.1.1 backlogged
    hrate_integrable hbacklogged_of_unfinished
    (fun t ht =>
      cumulativeService_lt_work_of_isLeast_hit
        hdeparture_isLeast_hit ht)
    hcumulative_at_departure_eq_work

/--
Comparator-start constructor from a least-hit characterization when the
cumulative service path is continuous at departure.  Work positivity shows the
path starts below the work threshold, and continuity rules out overshoot, so
the equality-at-departure field is derived rather than assumed.
-/
def ofLeastHitFromComparatorStartOfContinuous
    (hcapacity : 0 ≤ capacity)
    (hweight_nonneg : ∀ i, 0 ≤ weight i)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (htagged_guaranteed_rate_pos : 0 < capacity * weight tag)
    (backlogged : ℝ → ι → Bool)
    (hrate_integrable :
      IntervalIntegrable
        (gpsBackloggedClassRate ι tag capacity weight backlogged)
        MeasureTheory.volume (max (arrival 0) initialBusyUntil) (departure 0))
    (hbacklogged_of_unfinished : ∀ t,
      t ∈ Set.Ioo (max (arrival 0) initialBusyUntil) (departure 0) →
        (∫ u in (max (arrival 0) initialBusyUntil)..t,
          gpsBackloggedClassRate ι tag capacity weight backlogged u) < work 0 →
        backlogged t tag = true)
    (hdeparture_isLeast_hit : IsLeast
      (cumulativeServiceHitSet
        (max (arrival 0) initialBusyUntil) (work 0)
        (fun t =>
          ∫ u in (max (arrival 0) initialBusyUntil)..t,
            gpsBackloggedClassRate ι tag capacity weight backlogged u))
      (departure 0))
    (hwork_pos : 0 < work 0)
    (hcontinuous_at_departure : ContinuousAt
      (fun t =>
        ∫ u in (max (arrival 0) initialBusyUntil)..t,
          gpsBackloggedClassRate ι tag capacity weight backlogged u)
      (departure 0)) :
    TaggedJobGPSOpenBacklogIntegralSourcePath ι tag initialBusyUntil
      arrival work departure capacity weight :=
  ofLeastHitFromComparatorStart hcapacity hweight_nonneg htotal_weight_le_one
    htagged_guaranteed_rate_pos backlogged hrate_integrable
    hbacklogged_of_unfinished hdeparture_isLeast_hit
    (cumulativeService_eq_work_of_isLeast_hit_of_continuousAt
      (start := max (arrival 0) initialBusyUntil) (jobWork := work 0)
      (departureTime := departure 0)
      (cumulativeService := fun t =>
        ∫ u in (max (arrival 0) initialBusyUntil)..t,
          gpsBackloggedClassRate ι tag capacity weight backlogged u)
      hdeparture_isLeast_hit (by simpa using hwork_pos)
      hcontinuous_at_departure)

/--
Comparator-start constructor from least-hit and local interval integrability.
Local integrability gives continuity of the cumulative-service primitive, so
equality at departure is again derived rather than assumed.
-/
def ofLeastHitFromComparatorStartOfLocallyIntegrable
    (hcapacity : 0 ≤ capacity)
    (hweight_nonneg : ∀ i, 0 ≤ weight i)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (htagged_guaranteed_rate_pos : 0 < capacity * weight tag)
    (backlogged : ℝ → ι → Bool)
    (hrate_intervalIntegrable_all :
      ∀ a b : ℝ,
        IntervalIntegrable
          (gpsBackloggedClassRate ι tag capacity weight backlogged)
          MeasureTheory.volume a b)
    (hbacklogged_of_unfinished : ∀ t,
      t ∈ Set.Ioo (max (arrival 0) initialBusyUntil) (departure 0) →
        (∫ u in (max (arrival 0) initialBusyUntil)..t,
          gpsBackloggedClassRate ι tag capacity weight backlogged u) < work 0 →
        backlogged t tag = true)
    (hdeparture_isLeast_hit : IsLeast
      (cumulativeServiceHitSet
        (max (arrival 0) initialBusyUntil) (work 0)
        (fun t =>
          ∫ u in (max (arrival 0) initialBusyUntil)..t,
            gpsBackloggedClassRate ι tag capacity weight backlogged u))
      (departure 0))
    (hwork_pos : 0 < work 0) :
    TaggedJobGPSOpenBacklogIntegralSourcePath ι tag initialBusyUntil
      arrival work departure capacity weight :=
  ofLeastHitFromComparatorStartOfContinuous hcapacity hweight_nonneg
    htotal_weight_le_one htagged_guaranteed_rate_pos backlogged
    (hrate_intervalIntegrable_all
      (max (arrival 0) initialBusyUntil) (departure 0))
    hbacklogged_of_unfinished hdeparture_isLeast_hit hwork_pos
    ((intervalIntegral.continuous_primitive hrate_intervalIntegrable_all
      (max (arrival 0) initialBusyUntil)).continuousAt)

/--
Comparator-start constructor from least-hit and measurability of the finite
backlog-induced GPS rate.  Since there are finitely many classes, the measured
rate has finite range and is locally interval-integrable on every bounded
interval.
-/
def ofLeastHitFromComparatorStartOfMeasurableRate
    (hcapacity : 0 ≤ capacity)
    (hweight_nonneg : ∀ i, 0 ≤ weight i)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (htagged_guaranteed_rate_pos : 0 < capacity * weight tag)
    (backlogged : ℝ → ι → Bool)
    (hmeas_rate :
      Measurable (gpsBackloggedClassRate ι tag capacity weight backlogged))
    (hbacklogged_of_unfinished : ∀ t,
      t ∈ Set.Ioo (max (arrival 0) initialBusyUntil) (departure 0) →
        (∫ u in (max (arrival 0) initialBusyUntil)..t,
          gpsBackloggedClassRate ι tag capacity weight backlogged u) < work 0 →
        backlogged t tag = true)
    (hdeparture_isLeast_hit : IsLeast
      (cumulativeServiceHitSet
        (max (arrival 0) initialBusyUntil) (work 0)
        (fun t =>
          ∫ u in (max (arrival 0) initialBusyUntil)..t,
            gpsBackloggedClassRate ι tag capacity weight backlogged u))
      (departure 0))
    (hwork_pos : 0 < work 0) :
    TaggedJobGPSOpenBacklogIntegralSourcePath ι tag initialBusyUntil
      arrival work departure capacity weight :=
  ofLeastHitFromComparatorStartOfLocallyIntegrable hcapacity hweight_nonneg
    htotal_weight_le_one htagged_guaranteed_rate_pos backlogged
    (gpsBackloggedClassRate_intervalIntegrable_all_of_measurable
      tag capacity weight backlogged hmeas_rate)
    hbacklogged_of_unfinished hdeparture_isLeast_hit hwork_pos

/--
Comparator-start constructor from least-hit and per-class measurable backlog
indicators.  The finite-state GPS rate is then measurable and locally
interval-integrable.
-/
def ofLeastHitFromComparatorStartOfBackloggedMeasurable
    (hcapacity : 0 ≤ capacity)
    (hweight_nonneg : ∀ i, 0 ≤ weight i)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (htagged_guaranteed_rate_pos : 0 < capacity * weight tag)
    (backlogged : ℝ → ι → Bool)
    (hbacklogged_meas : ∀ i, Measurable (fun t => backlogged t i))
    (hbacklogged_of_unfinished : ∀ t,
      t ∈ Set.Ioo (max (arrival 0) initialBusyUntil) (departure 0) →
        (∫ u in (max (arrival 0) initialBusyUntil)..t,
          gpsBackloggedClassRate ι tag capacity weight backlogged u) < work 0 →
        backlogged t tag = true)
    (hdeparture_isLeast_hit : IsLeast
      (cumulativeServiceHitSet
        (max (arrival 0) initialBusyUntil) (work 0)
        (fun t =>
          ∫ u in (max (arrival 0) initialBusyUntil)..t,
            gpsBackloggedClassRate ι tag capacity weight backlogged u))
      (departure 0))
    (hwork_pos : 0 < work 0) :
    TaggedJobGPSOpenBacklogIntegralSourcePath ι tag initialBusyUntil
      arrival work departure capacity weight :=
  ofLeastHitFromComparatorStartOfMeasurableRate hcapacity hweight_nonneg
    htotal_weight_le_one htagged_guaranteed_rate_pos backlogged
    (gpsBackloggedClassRate_measurable tag capacity weight backlogged
      hbacklogged_meas)
    hbacklogged_of_unfinished hdeparture_isLeast_hit hwork_pos

/--
Comparator-start constructor when the source defines departure as the infimum
of the cumulative-service hit set.  Continuity and nonemptiness turn this
concrete first-hit definition into the least-hit premise used by the pathwise
open-backlog bridge.
-/
def ofSInfHitFromComparatorStartOfContinuous
    (hcapacity : 0 ≤ capacity)
    (hweight_nonneg : ∀ i, 0 ≤ weight i)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (htagged_guaranteed_rate_pos : 0 < capacity * weight tag)
    (backlogged : ℝ → ι → Bool)
    (hrate_integrable :
      IntervalIntegrable
        (gpsBackloggedClassRate ι tag capacity weight backlogged)
        MeasureTheory.volume (max (arrival 0) initialBusyUntil) (departure 0))
    (hbacklogged_of_unfinished : ∀ t,
      t ∈ Set.Ioo (max (arrival 0) initialBusyUntil) (departure 0) →
        (∫ u in (max (arrival 0) initialBusyUntil)..t,
          gpsBackloggedClassRate ι tag capacity weight backlogged u) < work 0 →
        backlogged t tag = true)
    (hdeparture_eq_sInf : departure 0 =
      sInf (cumulativeServiceHitSet
        (max (arrival 0) initialBusyUntil) (work 0)
        (fun t =>
          ∫ u in (max (arrival 0) initialBusyUntil)..t,
            gpsBackloggedClassRate ι tag capacity weight backlogged u)))
    (hhit_nonempty :
      (cumulativeServiceHitSet
        (max (arrival 0) initialBusyUntil) (work 0)
        (fun t =>
          ∫ u in (max (arrival 0) initialBusyUntil)..t,
            gpsBackloggedClassRate ι tag capacity weight backlogged u)).Nonempty)
    (hwork_pos : 0 < work 0)
    (hcontinuous : Continuous
      (fun t =>
        ∫ u in (max (arrival 0) initialBusyUntil)..t,
          gpsBackloggedClassRate ι tag capacity weight backlogged u)) :
    TaggedJobGPSOpenBacklogIntegralSourcePath ι tag initialBusyUntil
      arrival work departure capacity weight :=
  ofLeastHitFromComparatorStartOfContinuous hcapacity hweight_nonneg
    htotal_weight_le_one htagged_guaranteed_rate_pos backlogged
    hrate_integrable hbacklogged_of_unfinished
    (by
      rw [hdeparture_eq_sInf]
      exact isLeast_sInf_cumulativeServiceHitSet_of_continuous
        (start := max (arrival 0) initialBusyUntil) (jobWork := work 0)
        (cumulativeService := fun t =>
          ∫ u in (max (arrival 0) initialBusyUntil)..t,
            gpsBackloggedClassRate ι tag capacity weight backlogged u)
        hcontinuous hhit_nonempty)
    hwork_pos hcontinuous.continuousAt

/--
Comparator-start `sInf` first-hit constructor from local interval
integrability.  The cumulative tagged-service primitive is continuous, so the
concrete first-hit definition supplies a least hit.
-/
def ofSInfHitFromComparatorStartOfLocallyIntegrable
    (hcapacity : 0 ≤ capacity)
    (hweight_nonneg : ∀ i, 0 ≤ weight i)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (htagged_guaranteed_rate_pos : 0 < capacity * weight tag)
    (backlogged : ℝ → ι → Bool)
    (hrate_intervalIntegrable_all :
      ∀ a b : ℝ,
        IntervalIntegrable
          (gpsBackloggedClassRate ι tag capacity weight backlogged)
          MeasureTheory.volume a b)
    (hbacklogged_of_unfinished : ∀ t,
      t ∈ Set.Ioo (max (arrival 0) initialBusyUntil) (departure 0) →
        (∫ u in (max (arrival 0) initialBusyUntil)..t,
          gpsBackloggedClassRate ι tag capacity weight backlogged u) < work 0 →
        backlogged t tag = true)
    (hdeparture_eq_sInf : departure 0 =
      sInf (cumulativeServiceHitSet
        (max (arrival 0) initialBusyUntil) (work 0)
        (fun t =>
          ∫ u in (max (arrival 0) initialBusyUntil)..t,
            gpsBackloggedClassRate ι tag capacity weight backlogged u)))
    (hhit_nonempty :
      (cumulativeServiceHitSet
        (max (arrival 0) initialBusyUntil) (work 0)
        (fun t =>
          ∫ u in (max (arrival 0) initialBusyUntil)..t,
            gpsBackloggedClassRate ι tag capacity weight backlogged u)).Nonempty)
    (hwork_pos : 0 < work 0) :
    TaggedJobGPSOpenBacklogIntegralSourcePath ι tag initialBusyUntil
      arrival work departure capacity weight :=
  ofSInfHitFromComparatorStartOfContinuous hcapacity hweight_nonneg
    htotal_weight_le_one htagged_guaranteed_rate_pos backlogged
    (hrate_intervalIntegrable_all
      (max (arrival 0) initialBusyUntil) (departure 0))
    hbacklogged_of_unfinished hdeparture_eq_sInf hhit_nonempty hwork_pos
    (intervalIntegral.continuous_primitive hrate_intervalIntegrable_all
      (max (arrival 0) initialBusyUntil))

/--
Comparator-start `sInf` first-hit constructor from measurability of the finite
backlog-induced GPS rate.
-/
def ofSInfHitFromComparatorStartOfMeasurableRate
    (hcapacity : 0 ≤ capacity)
    (hweight_nonneg : ∀ i, 0 ≤ weight i)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (htagged_guaranteed_rate_pos : 0 < capacity * weight tag)
    (backlogged : ℝ → ι → Bool)
    (hmeas_rate :
      Measurable (gpsBackloggedClassRate ι tag capacity weight backlogged))
    (hbacklogged_of_unfinished : ∀ t,
      t ∈ Set.Ioo (max (arrival 0) initialBusyUntil) (departure 0) →
        (∫ u in (max (arrival 0) initialBusyUntil)..t,
          gpsBackloggedClassRate ι tag capacity weight backlogged u) < work 0 →
        backlogged t tag = true)
    (hdeparture_eq_sInf : departure 0 =
      sInf (cumulativeServiceHitSet
        (max (arrival 0) initialBusyUntil) (work 0)
        (fun t =>
          ∫ u in (max (arrival 0) initialBusyUntil)..t,
            gpsBackloggedClassRate ι tag capacity weight backlogged u)))
    (hhit_nonempty :
      (cumulativeServiceHitSet
        (max (arrival 0) initialBusyUntil) (work 0)
        (fun t =>
          ∫ u in (max (arrival 0) initialBusyUntil)..t,
            gpsBackloggedClassRate ι tag capacity weight backlogged u)).Nonempty)
    (hwork_pos : 0 < work 0) :
    TaggedJobGPSOpenBacklogIntegralSourcePath ι tag initialBusyUntil
      arrival work departure capacity weight :=
  ofSInfHitFromComparatorStartOfLocallyIntegrable hcapacity hweight_nonneg
    htotal_weight_le_one htagged_guaranteed_rate_pos backlogged
    (gpsBackloggedClassRate_intervalIntegrable_all_of_measurable
      tag capacity weight backlogged hmeas_rate)
    hbacklogged_of_unfinished hdeparture_eq_sInf hhit_nonempty hwork_pos

/--
Comparator-start `sInf` first-hit constructor from per-class measurable backlog
indicators.
-/
def ofSInfHitFromComparatorStartOfBackloggedMeasurable
    (hcapacity : 0 ≤ capacity)
    (hweight_nonneg : ∀ i, 0 ≤ weight i)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (htagged_guaranteed_rate_pos : 0 < capacity * weight tag)
    (backlogged : ℝ → ι → Bool)
    (hbacklogged_meas : ∀ i, Measurable (fun t => backlogged t i))
    (hbacklogged_of_unfinished : ∀ t,
      t ∈ Set.Ioo (max (arrival 0) initialBusyUntil) (departure 0) →
        (∫ u in (max (arrival 0) initialBusyUntil)..t,
          gpsBackloggedClassRate ι tag capacity weight backlogged u) < work 0 →
        backlogged t tag = true)
    (hdeparture_eq_sInf : departure 0 =
      sInf (cumulativeServiceHitSet
        (max (arrival 0) initialBusyUntil) (work 0)
        (fun t =>
          ∫ u in (max (arrival 0) initialBusyUntil)..t,
            gpsBackloggedClassRate ι tag capacity weight backlogged u)))
    (hhit_nonempty :
      (cumulativeServiceHitSet
        (max (arrival 0) initialBusyUntil) (work 0)
        (fun t =>
          ∫ u in (max (arrival 0) initialBusyUntil)..t,
            gpsBackloggedClassRate ι tag capacity weight backlogged u)).Nonempty)
    (hwork_pos : 0 < work 0) :
    TaggedJobGPSOpenBacklogIntegralSourcePath ι tag initialBusyUntil
      arrival work departure capacity weight :=
  ofSInfHitFromComparatorStartOfMeasurableRate hcapacity hweight_nonneg
    htotal_weight_le_one htagged_guaranteed_rate_pos backlogged
    (gpsBackloggedClassRate_measurable tag capacity weight backlogged
      hbacklogged_meas)
    hbacklogged_of_unfinished hdeparture_eq_sInf hhit_nonempty hwork_pos

/--
Comparator-start constructor from the source-level first-hit-time statement.
Continuity turns that definition into the least-hit premise used internally.
-/
def ofFirstHitTimeFromComparatorStartOfContinuous
    (hcapacity : 0 ≤ capacity)
    (hweight_nonneg : ∀ i, 0 ≤ weight i)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (htagged_guaranteed_rate_pos : 0 < capacity * weight tag)
    (backlogged : ℝ → ι → Bool)
    (hrate_integrable :
      IntervalIntegrable
        (gpsBackloggedClassRate ι tag capacity weight backlogged)
        MeasureTheory.volume (max (arrival 0) initialBusyUntil) (departure 0))
    (hbacklogged_of_unfinished : ∀ t,
      t ∈ Set.Ioo (max (arrival 0) initialBusyUntil) (departure 0) →
        (∫ u in (max (arrival 0) initialBusyUntil)..t,
          gpsBackloggedClassRate ι tag capacity weight backlogged u) < work 0 →
        backlogged t tag = true)
    (hdeparture_firstHit :
      cumulativeServiceFirstHitAt
        (max (arrival 0) initialBusyUntil) (work 0)
        (fun t =>
          ∫ u in (max (arrival 0) initialBusyUntil)..t,
            gpsBackloggedClassRate ι tag capacity weight backlogged u)
        (departure 0))
    (hwork_pos : 0 < work 0)
    (hcontinuous : Continuous
      (fun t =>
        ∫ u in (max (arrival 0) initialBusyUntil)..t,
          gpsBackloggedClassRate ι tag capacity weight backlogged u)) :
    TaggedJobGPSOpenBacklogIntegralSourcePath ι tag initialBusyUntil
      arrival work departure capacity weight :=
  ofLeastHitFromComparatorStartOfContinuous hcapacity hweight_nonneg
    htotal_weight_le_one htagged_guaranteed_rate_pos backlogged
    hrate_integrable hbacklogged_of_unfinished
    (cumulativeServiceFirstHitAt_isLeast_of_continuous
      (start := max (arrival 0) initialBusyUntil) (jobWork := work 0)
      (departureTime := departure 0)
      (cumulativeService := fun t =>
        ∫ u in (max (arrival 0) initialBusyUntil)..t,
          gpsBackloggedClassRate ι tag capacity weight backlogged u)
      hcontinuous hdeparture_firstHit)
    hwork_pos hcontinuous.continuousAt

/--
Comparator-start first-hit-time constructor from local interval integrability.
-/
def ofFirstHitTimeFromComparatorStartOfLocallyIntegrable
    (hcapacity : 0 ≤ capacity)
    (hweight_nonneg : ∀ i, 0 ≤ weight i)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (htagged_guaranteed_rate_pos : 0 < capacity * weight tag)
    (backlogged : ℝ → ι → Bool)
    (hrate_intervalIntegrable_all :
      ∀ a b : ℝ,
        IntervalIntegrable
          (gpsBackloggedClassRate ι tag capacity weight backlogged)
          MeasureTheory.volume a b)
    (hbacklogged_of_unfinished : ∀ t,
      t ∈ Set.Ioo (max (arrival 0) initialBusyUntil) (departure 0) →
        (∫ u in (max (arrival 0) initialBusyUntil)..t,
          gpsBackloggedClassRate ι tag capacity weight backlogged u) < work 0 →
        backlogged t tag = true)
    (hdeparture_firstHit :
      cumulativeServiceFirstHitAt
        (max (arrival 0) initialBusyUntil) (work 0)
        (fun t =>
          ∫ u in (max (arrival 0) initialBusyUntil)..t,
            gpsBackloggedClassRate ι tag capacity weight backlogged u)
        (departure 0))
    (hwork_pos : 0 < work 0) :
    TaggedJobGPSOpenBacklogIntegralSourcePath ι tag initialBusyUntil
      arrival work departure capacity weight :=
  ofFirstHitTimeFromComparatorStartOfContinuous hcapacity hweight_nonneg
    htotal_weight_le_one htagged_guaranteed_rate_pos backlogged
    (hrate_intervalIntegrable_all
      (max (arrival 0) initialBusyUntil) (departure 0))
    hbacklogged_of_unfinished hdeparture_firstHit hwork_pos
    (intervalIntegral.continuous_primitive hrate_intervalIntegrable_all
      (max (arrival 0) initialBusyUntil))

/--
Comparator-start first-hit-time constructor from measurability of the finite
backlog-induced GPS rate.
-/
def ofFirstHitTimeFromComparatorStartOfMeasurableRate
    (hcapacity : 0 ≤ capacity)
    (hweight_nonneg : ∀ i, 0 ≤ weight i)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (htagged_guaranteed_rate_pos : 0 < capacity * weight tag)
    (backlogged : ℝ → ι → Bool)
    (hmeas_rate :
      Measurable (gpsBackloggedClassRate ι tag capacity weight backlogged))
    (hbacklogged_of_unfinished : ∀ t,
      t ∈ Set.Ioo (max (arrival 0) initialBusyUntil) (departure 0) →
        (∫ u in (max (arrival 0) initialBusyUntil)..t,
          gpsBackloggedClassRate ι tag capacity weight backlogged u) < work 0 →
        backlogged t tag = true)
    (hdeparture_firstHit :
      cumulativeServiceFirstHitAt
        (max (arrival 0) initialBusyUntil) (work 0)
        (fun t =>
          ∫ u in (max (arrival 0) initialBusyUntil)..t,
            gpsBackloggedClassRate ι tag capacity weight backlogged u)
        (departure 0))
    (hwork_pos : 0 < work 0) :
    TaggedJobGPSOpenBacklogIntegralSourcePath ι tag initialBusyUntil
      arrival work departure capacity weight :=
  ofFirstHitTimeFromComparatorStartOfLocallyIntegrable hcapacity hweight_nonneg
    htotal_weight_le_one htagged_guaranteed_rate_pos backlogged
    (gpsBackloggedClassRate_intervalIntegrable_all_of_measurable
      tag capacity weight backlogged hmeas_rate)
    hbacklogged_of_unfinished hdeparture_firstHit hwork_pos

/--
Comparator-start first-hit-time constructor from per-class measurable backlog
indicators.
-/
def ofFirstHitTimeFromComparatorStartOfBackloggedMeasurable
    (hcapacity : 0 ≤ capacity)
    (hweight_nonneg : ∀ i, 0 ≤ weight i)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (htagged_guaranteed_rate_pos : 0 < capacity * weight tag)
    (backlogged : ℝ → ι → Bool)
    (hbacklogged_meas : ∀ i, Measurable (fun t => backlogged t i))
    (hbacklogged_of_unfinished : ∀ t,
      t ∈ Set.Ioo (max (arrival 0) initialBusyUntil) (departure 0) →
        (∫ u in (max (arrival 0) initialBusyUntil)..t,
          gpsBackloggedClassRate ι tag capacity weight backlogged u) < work 0 →
        backlogged t tag = true)
    (hdeparture_firstHit :
      cumulativeServiceFirstHitAt
        (max (arrival 0) initialBusyUntil) (work 0)
        (fun t =>
          ∫ u in (max (arrival 0) initialBusyUntil)..t,
            gpsBackloggedClassRate ι tag capacity weight backlogged u)
        (departure 0))
    (hwork_pos : 0 < work 0) :
    TaggedJobGPSOpenBacklogIntegralSourcePath ι tag initialBusyUntil
      arrival work departure capacity weight :=
  ofFirstHitTimeFromComparatorStartOfMeasurableRate hcapacity hweight_nonneg
    htotal_weight_le_one htagged_guaranteed_rate_pos backlogged
    (gpsBackloggedClassRate_measurable tag capacity weight backlogged
      hbacklogged_meas)
    hbacklogged_of_unfinished hdeparture_firstHit hwork_pos

/--
The integral-defined source path supplies the open-backlog a.e. normalized GPS
source path by using the backlog-induced rate as the instantaneous rate and
its interval integral as cumulative service.
-/
def toTaggedJobAENormalizedGPSOpenBacklogSourcePath
    (H : TaggedJobGPSOpenBacklogIntegralSourcePath ι tag initialBusyUntil
      arrival work departure capacity weight) :
    TaggedJobAENormalizedGPSOpenBacklogSourcePath ι tag initialBusyUntil
      arrival work departure capacity weight where
  capacity_nonneg := H.capacity_nonneg
  weight_nonneg := H.weight_nonneg
  total_weight_le_one := H.total_weight_le_one
  tagged_guaranteed_rate_pos := H.tagged_guaranteed_rate_pos
  actualServiceStart := H.actualServiceStart
  arrival_le_actualServiceStart := H.arrival_le_actualServiceStart
  departure_after_actualServiceStart := H.departure_after_actualServiceStart
  actualStart_le_comparatorStart := H.actualStart_le_comparatorStart
  backlogged := H.backlogged
  instantaneousClassRate :=
    gpsBackloggedClassRate ι tag capacity weight H.backlogged
  service :=
    gpsBackloggedCumulativeServiceFrom ι tag capacity weight H.backlogged
      H.actualServiceStart
  rate_intervalIntegrable := H.rate_intervalIntegrable
  tag_backlogged_on_open_actual_job := H.tag_backlogged_on_open_actual_job
  ae_gps_allocation_on_actual_job := by
    filter_upwards with t
    rfl
  service_increment_eq_integral := by
    simp [gpsBackloggedCumulativeServiceFrom]
  completed_work_eq_service := by
    simpa [gpsBackloggedCumulativeServiceFrom] using H.service_integral_eq_work

/--
The integral-defined source path has the guaranteed tagged GPS rate floor
almost everywhere on the closed service interval.  The proof uses only the
open-interval tagged-backlog condition and endpoint nullity.
-/
theorem ae_guaranteed_rate_floor_on_actual_job
    (H : TaggedJobGPSOpenBacklogIntegralSourcePath ι tag initialBusyUntil
      arrival work departure capacity weight) :
    ∀ᵐ t ∂(MeasureTheory.volume.restrict
      (Set.Icc H.actualServiceStart (departure 0))),
      capacity * weight tag ≤
        gpsBackloggedClassRate ι tag capacity weight H.backlogged t := by
  have hbacklog :
      ∀ᵐ t ∂(MeasureTheory.volume.restrict
        (Set.Icc H.actualServiceStart (departure 0))),
        H.backlogged t tag = true :=
    ae_restrict_Icc_of_forall_mem_Ioo H.tag_backlogged_on_open_actual_job
  filter_upwards [hbacklog] with t htag
  exact gpsBackloggedClassRate_ge_guaranteed_of_tag_backlogged
    H.capacity_nonneg H.weight_nonneg H.total_weight_le_one
    H.tagged_guaranteed_rate_pos htag

/--
Integrating the backlog-induced GPS rate over the tagged service interval
gives at least the tagged guaranteed-rate work floor.
-/
theorem integrated_rate_floor
    (H : TaggedJobGPSOpenBacklogIntegralSourcePath ι tag initialBusyUntil
      arrival work departure capacity weight) :
    capacity * weight tag * (departure 0 - H.actualServiceStart) ≤
      ∫ t in H.actualServiceStart..departure 0,
        gpsBackloggedClassRate ι tag capacity weight H.backlogged t :=
  intervalIntegral_ge_const_of_ae_le
    H.departure_after_actualServiceStart H.rate_intervalIntegrable
    H.ae_guaranteed_rate_floor_on_actual_job

/--
The tagged job completes within the service window generated by its guaranteed
GPS share.
-/
theorem departure_zero_le_actualStart_add_work_div
    (H : TaggedJobGPSOpenBacklogIntegralSourcePath ι tag initialBusyUntil
      arrival work departure capacity weight) :
    departure 0 ≤ H.actualServiceStart + work 0 / (capacity * weight tag) := by
  have hfloor := H.integrated_rate_floor
  rw [H.service_integral_eq_work] at hfloor
  have hduration : departure 0 - H.actualServiceStart ≤
      work 0 / (capacity * weight tag) := by
    apply (le_div_iff₀ H.tagged_guaranteed_rate_pos).2
    nlinarith [hfloor]
  linarith

/--
The integral-defined open-backlog source model bounds the tagged response by
the initial-workload FCFS comparator.
-/
theorem responseTime_zero_le_fcfsResponseTimeFrom
    (H : TaggedJobGPSOpenBacklogIntegralSourcePath ι tag initialBusyUntil
      arrival work departure capacity weight) :
    responseTime arrival departure 0 ≤
      responseTime arrival
        (fcfsDepartureFrom initialBusyUntil arrival work (capacity * weight tag)) 0 :=
  H.toTaggedJobAENormalizedGPSOpenBacklogSourcePath.responseTime_zero_le_fcfsResponseTimeFrom

/--
If the tagged GPS source starts at the comparison start and satisfies the
first-hit cumulative-service facts, then its tagged response is bounded by the
initial-workload FCFS comparator.  This is a direct pathwise comparison form
for an actual multiclass GPS queue construction.
-/
theorem responseTime_zero_le_fcfsResponseTimeFrom_ofFirstHitFromComparatorStart
    (hcapacity : 0 ≤ capacity)
    (hweight_nonneg : ∀ i, 0 ≤ weight i)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (htagged_guaranteed_rate_pos : 0 < capacity * weight tag)
    (hstart_le_departure :
      max (arrival 0) initialBusyUntil ≤ departure 0)
    (backlogged : ℝ → ι → Bool)
    (hrate_integrable :
      IntervalIntegrable
        (gpsBackloggedClassRate ι tag capacity weight backlogged)
        MeasureTheory.volume (max (arrival 0) initialBusyUntil) (departure 0))
    (hbacklogged_of_unfinished : ∀ t,
      t ∈ Set.Ioo (max (arrival 0) initialBusyUntil) (departure 0) →
        (∫ u in (max (arrival 0) initialBusyUntil)..t,
          gpsBackloggedClassRate ι tag capacity weight backlogged u) < work 0 →
        backlogged t tag = true)
    (hcumulative_before_departure_lt_work : ∀ t,
      t ∈ Set.Ioo (max (arrival 0) initialBusyUntil) (departure 0) →
        (∫ u in (max (arrival 0) initialBusyUntil)..t,
          gpsBackloggedClassRate ι tag capacity weight backlogged u) < work 0)
    (hcumulative_at_departure_eq_work :
      ∫ u in (max (arrival 0) initialBusyUntil)..departure 0,
        gpsBackloggedClassRate ι tag capacity weight backlogged u = work 0) :
    responseTime arrival departure 0 ≤
      responseTime arrival
        (fcfsDepartureFrom initialBusyUntil arrival work (capacity * weight tag)) 0 :=
  (ofFirstHitFromComparatorStart hcapacity hweight_nonneg htotal_weight_le_one
    htagged_guaranteed_rate_pos hstart_le_departure backlogged hrate_integrable
    hbacklogged_of_unfinished hcumulative_before_departure_lt_work
    hcumulative_at_departure_eq_work).responseTime_zero_le_fcfsResponseTimeFrom

/--
For a source-defined GPS departure, the unfinished-work backlog invariant on
the tagged job's guaranteed service window gives the zero-th departure bound
needed by the FCFS comparator.
-/
theorem gpsBackloggedDepartureFrom_zero_le_guaranteedWindow_of_backlogged_if_unfinished
    (hcapacity : 0 ≤ capacity)
    (hweight_nonneg : ∀ i, 0 ≤ weight i)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (htagged_guaranteed_rate_pos : 0 < capacity * weight tag)
    (backlogged : ℝ → ι → Bool)
    (hbacklogged_meas : ∀ i, Measurable (fun t => backlogged t i))
    (hwork_nonneg : 0 ≤ work 0)
    (hbacklogged_of_unfinished_on_guaranteed_window : ∀ t,
      t ∈ Set.Ioo
        (max (arrival 0) initialBusyUntil)
        (max (arrival 0) initialBusyUntil +
          work 0 / (capacity * weight tag)) →
      (∫ u in (max (arrival 0) initialBusyUntil)..t,
        gpsBackloggedClassRate ι tag capacity weight backlogged u) <
        work 0 →
      backlogged t tag = true) :
    gpsBackloggedDepartureFrom (ι := ι) (tag := tag)
      initialBusyUntil arrival work capacity weight backlogged 0 ≤
      max (arrival 0) initialBusyUntil + work 0 / (capacity * weight tag) := by
  let completionTime :=
    max (arrival 0) initialBusyUntil + work 0 / (capacity * weight tag)
  have hrate_intervalIntegrable_all :
      ∀ a b : ℝ,
        IntervalIntegrable
          (gpsBackloggedClassRate ι tag capacity weight backlogged)
          MeasureTheory.volume a b :=
    gpsBackloggedClassRate_intervalIntegrable_all_of_backlogged_measurable
      tag capacity weight backlogged hbacklogged_meas
  have hstart_completion :
      max (arrival 0) initialBusyUntil ≤ completionTime := by
    have hdiv_nonneg :
        0 ≤ work 0 / (capacity * weight tag) :=
      div_nonneg hwork_nonneg htagged_guaranteed_rate_pos.le
    dsimp [completionTime]
    linarith
  have hreaches :
      work 0 ≤
        ∫ u in (max (arrival 0) initialBusyUntil)..completionTime,
          gpsBackloggedClassRate ι tag capacity weight backlogged u := by
    dsimp [completionTime]
    exact
      cumulativeService_reaches_at_guaranteedWindow_of_backlogged_if_unfinished
        (tag := tag) hcapacity hweight_nonneg htotal_weight_le_one
        htagged_guaranteed_rate_pos hwork_nonneg
        (hrate_intervalIntegrable_all
          (max (arrival 0) initialBusyUntil)
          (max (arrival 0) initialBusyUntil +
            work 0 / (capacity * weight tag)))
        hbacklogged_of_unfinished_on_guaranteed_window
  have hfirst :
      cumulativeServiceFirstHitAt
        (max (arrival 0) initialBusyUntil) (work 0)
        (fun t =>
          ∫ u in (max (arrival 0) initialBusyUntil)..t,
            gpsBackloggedClassRate ι tag capacity weight backlogged u)
        (gpsBackloggedDepartureFrom (ι := ι) (tag := tag)
          initialBusyUntil arrival work capacity weight backlogged 0) :=
    gpsBackloggedDepartureFrom_zero_firstHitAt_of_reaches
      (ι := ι) (tag := tag)
      (initialBusyUntil := initialBusyUntil)
      (arrival := arrival) (work := work)
      (capacity := capacity) (weight := weight)
      (backlogged := backlogged) (witness := completionTime)
      hstart_completion hreaches
  have hcontinuous :
      Continuous
        (fun t =>
          ∫ u in (max (arrival 0) initialBusyUntil)..t,
            gpsBackloggedClassRate ι tag capacity weight backlogged u) :=
    intervalIntegral.continuous_primitive hrate_intervalIntegrable_all
      (max (arrival 0) initialBusyUntil)
  have hleast :
      IsLeast
        (cumulativeServiceHitSet
          (max (arrival 0) initialBusyUntil) (work 0)
          (fun t =>
            ∫ u in (max (arrival 0) initialBusyUntil)..t,
              gpsBackloggedClassRate ι tag capacity weight backlogged u))
        (gpsBackloggedDepartureFrom (ι := ι) (tag := tag)
          initialBusyUntil arrival work capacity weight backlogged 0) :=
    cumulativeServiceFirstHitAt_isLeast_of_continuous hcontinuous hfirst
  have hcompletion_hit :
      completionTime ∈
        cumulativeServiceHitSet
          (max (arrival 0) initialBusyUntil) (work 0)
          (fun t =>
            ∫ u in (max (arrival 0) initialBusyUntil)..t,
              gpsBackloggedClassRate ι tag capacity weight backlogged u) :=
    ⟨hstart_completion, hreaches⟩
  exact hleast.2 hcompletion_hit

/--
If the zero-th departure is the source-defined GPS first-hit departure and
unfinished tagged work implies tagged backlog on the guaranteed service
window, then the tagged response is bounded by the initial-workload FCFS
comparator at rate `capacity * weight tag`.
-/
theorem responseTime_zero_le_fcfsResponseTimeFrom_ofGPSDepartureFromUnfinishedWindowBackloggedMeasurable
    (hcapacity : 0 ≤ capacity)
    (hweight_nonneg : ∀ i, 0 ≤ weight i)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (htagged_guaranteed_rate_pos : 0 < capacity * weight tag)
    (backlogged : ℝ → ι → Bool)
    (hbacklogged_meas : ∀ i, Measurable (fun t => backlogged t i))
    (hdeparture_eq_gps :
      departure 0 =
        gpsBackloggedDepartureFrom (ι := ι) (tag := tag)
          initialBusyUntil arrival work capacity weight backlogged 0)
    (hwork_nonneg : 0 ≤ work 0)
    (hbacklogged_of_unfinished_on_guaranteed_window : ∀ t,
      t ∈ Set.Ioo
        (max (arrival 0) initialBusyUntil)
        (max (arrival 0) initialBusyUntil +
          work 0 / (capacity * weight tag)) →
      (∫ u in (max (arrival 0) initialBusyUntil)..t,
        gpsBackloggedClassRate ι tag capacity weight backlogged u) <
        work 0 →
      backlogged t tag = true) :
    responseTime arrival departure 0 ≤
      responseTime arrival
        (fcfsDepartureFrom initialBusyUntil arrival work (capacity * weight tag))
        0 := by
  have hdeparture_le :
      departure 0 ≤
        fcfsDepartureFrom initialBusyUntil arrival work
          (capacity * weight tag) 0 := by
    rw [hdeparture_eq_gps]
    simpa [fcfsDepartureFrom] using
      (gpsBackloggedDepartureFrom_zero_le_guaranteedWindow_of_backlogged_if_unfinished
        (ι := ι) (tag := tag)
        (initialBusyUntil := initialBusyUntil)
        (arrival := arrival) (work := work)
        (capacity := capacity) (weight := weight)
        hcapacity hweight_nonneg htotal_weight_le_one
        htagged_guaranteed_rate_pos backlogged hbacklogged_meas hwork_nonneg
        hbacklogged_of_unfinished_on_guaranteed_window)
  unfold responseTime
  exact sub_le_sub_right hdeparture_le (arrival 0)

/--
Remaining-work formulation of the unfinished-window bridge.  If the tagged
remaining work on the guaranteed service window is exactly initial work minus
cumulative tagged GPS service, and positive remaining work implies tagged
backlog membership, then the source-defined zero-th GPS departure is bounded
by the initial-workload FCFS comparator.
-/
theorem responseTime_zero_le_fcfsResponseTimeFrom_ofGPSDepartureFromPositiveRemainingWork
    (hcapacity : 0 ≤ capacity)
    (hweight_nonneg : ∀ i, 0 ≤ weight i)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (htagged_guaranteed_rate_pos : 0 < capacity * weight tag)
    (backlogged : ℝ → ι → Bool)
    (hbacklogged_meas : ∀ i, Measurable (fun t => backlogged t i))
    (hdeparture_eq_gps :
      departure 0 =
        gpsBackloggedDepartureFrom (ι := ι) (tag := tag)
          initialBusyUntil arrival work capacity weight backlogged 0)
    (hwork_nonneg : 0 ≤ work 0)
    (remainingWork : ℝ → ℝ)
    (hremaining_eq_on_guaranteed_window : ∀ t,
      t ∈ Set.Ioo
        (max (arrival 0) initialBusyUntil)
        (max (arrival 0) initialBusyUntil +
          work 0 / (capacity * weight tag)) →
      remainingWork t =
        work 0 -
          ∫ u in (max (arrival 0) initialBusyUntil)..t,
            gpsBackloggedClassRate ι tag capacity weight backlogged u)
    (hbacklogged_of_positive_remainingWork : ∀ t,
      t ∈ Set.Ioo
        (max (arrival 0) initialBusyUntil)
        (max (arrival 0) initialBusyUntil +
          work 0 / (capacity * weight tag)) →
      0 < remainingWork t →
      backlogged t tag = true) :
    responseTime arrival departure 0 ≤
      responseTime arrival
        (fcfsDepartureFrom initialBusyUntil arrival work (capacity * weight tag))
        0 :=
  responseTime_zero_le_fcfsResponseTimeFrom_ofGPSDepartureFromUnfinishedWindowBackloggedMeasurable
    hcapacity hweight_nonneg htotal_weight_le_one htagged_guaranteed_rate_pos
    backlogged hbacklogged_meas hdeparture_eq_gps hwork_nonneg
    (by
      intro t ht hunfinished
      exact hbacklogged_of_positive_remainingWork t ht
        (by
        rw [hremaining_eq_on_guaranteed_window t ht]
        linarith))

/--
Canonical tagged remaining work from a service start: initial tagged work minus
the cumulative GPS service assigned to the tagged class by the backlog path.
-/
def gpsTaggedRemainingWorkFrom
    (start jobWork capacity : ℝ) (weight : ι → ℝ)
    (backlogged : ℝ → ι → Bool) (t : ℝ) : ℝ :=
  jobWork -
    ∫ u in start..t,
      gpsBackloggedClassRate ι tag capacity weight backlogged u

/-- At the service start, canonical tagged remaining work is the tagged job work. -/
theorem gpsTaggedRemainingWorkFrom_start
    (start jobWork capacity : ℝ) (weight : ι → ℝ)
    (backlogged : ℝ → ι → Bool) :
    gpsTaggedRemainingWorkFrom (ι := ι) (tag := tag)
        start jobWork capacity weight backlogged start = jobWork := by
  simp [gpsTaggedRemainingWorkFrom]

/--
Canonical classwise remaining work generated from initial class work and the
backlog-induced GPS service rates.
-/
def gpsRemainingWorkVectorFrom
    (start : ℝ) (initialWork : ι → ℝ) (capacity : ℝ)
    (weight : ι → ℝ) (backlogged : ℝ → ι → Bool)
    (t : ℝ) (i : ι) : ℝ :=
  initialWork i -
    ∫ u in start..t,
      gpsBackloggedClassRate ι i capacity weight backlogged u

/-- At the service start, the canonical classwise remaining-work vector equals initial work. -/
theorem gpsRemainingWorkVectorFrom_start
    (start : ℝ) (initialWork : ι → ℝ) (capacity : ℝ)
    (weight : ι → ℝ) (backlogged : ℝ → ι → Bool) (i : ι) :
    gpsRemainingWorkVectorFrom start initialWork capacity weight backlogged
        start i = initialWork i := by
  simp [gpsRemainingWorkVectorFrom]

/--
Measurable finite-class backlog indicators generate measurable canonical
classwise remaining-work coordinates.
-/
theorem gpsRemainingWorkVectorFrom_measurable_of_backlogged_measurable
    (start : ℝ) (initialWork : ι → ℝ) (capacity : ℝ)
    (weight : ι → ℝ) (backlogged : ℝ → ι → Bool)
    (hbacklogged_meas : ∀ i, Measurable (fun t => backlogged t i)) :
    ∀ i, Measurable (fun t =>
      gpsRemainingWorkVectorFrom start initialWork capacity weight backlogged t i) := by
  intro i
  have hcontinuous :
      Continuous (fun t : ℝ =>
        ∫ u in start..t,
          gpsBackloggedClassRate ι i capacity weight backlogged u) :=
    intervalIntegral.continuous_primitive
      (gpsBackloggedClassRate_intervalIntegrable_all_of_backlogged_measurable
        i capacity weight backlogged hbacklogged_meas)
      start
  exact measurable_const.sub hcontinuous.measurable

/--
The tagged coordinate of the classwise remaining-work vector is the tagged
remaining-work expression when the tagged initial work is `jobWork`.
-/
theorem gpsRemainingWorkVectorFrom_tag_eq_gpsTaggedRemainingWorkFrom
    {start jobWork capacity : ℝ} {initialWork : ι → ℝ}
    {weight : ι → ℝ} {backlogged : ℝ → ι → Bool} {t : ℝ}
    (hinitial_tag : initialWork tag = jobWork) :
    gpsRemainingWorkVectorFrom (ι := ι) start initialWork capacity weight
        backlogged t tag =
      gpsTaggedRemainingWorkFrom (ι := ι) (tag := tag)
        start jobWork capacity weight backlogged t := by
  simp [gpsRemainingWorkVectorFrom, gpsTaggedRemainingWorkFrom, hinitial_tag]

/--
Canonical remaining-work formulation of the unfinished-window bridge.  This is
the source-model version with remaining work fixed to initial tagged work minus
cumulative tagged GPS service, rather than supplied as an arbitrary process.
-/
theorem responseTime_zero_le_fcfsResponseTimeFrom_ofGPSDepartureFromCanonicalRemainingWork
    (hcapacity : 0 ≤ capacity)
    (hweight_nonneg : ∀ i, 0 ≤ weight i)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (htagged_guaranteed_rate_pos : 0 < capacity * weight tag)
    (backlogged : ℝ → ι → Bool)
    (hbacklogged_meas : ∀ i, Measurable (fun t => backlogged t i))
    (hdeparture_eq_gps :
      departure 0 =
        gpsBackloggedDepartureFrom (ι := ι) (tag := tag)
          initialBusyUntil arrival work capacity weight backlogged 0)
    (hwork_nonneg : 0 ≤ work 0)
    (hbacklogged_of_positive_canonicalRemainingWork : ∀ t,
      t ∈ Set.Ioo
        (max (arrival 0) initialBusyUntil)
        (max (arrival 0) initialBusyUntil +
          work 0 / (capacity * weight tag)) →
      0 < gpsTaggedRemainingWorkFrom (ι := ι) (tag := tag)
        (max (arrival 0) initialBusyUntil) (work 0)
        capacity weight backlogged t →
      backlogged t tag = true) :
    responseTime arrival departure 0 ≤
      responseTime arrival
        (fcfsDepartureFrom initialBusyUntil arrival work (capacity * weight tag))
        0 :=
  responseTime_zero_le_fcfsResponseTimeFrom_ofGPSDepartureFromPositiveRemainingWork
    hcapacity hweight_nonneg htotal_weight_le_one htagged_guaranteed_rate_pos
    backlogged hbacklogged_meas hdeparture_eq_gps hwork_nonneg
    (gpsTaggedRemainingWorkFrom (ι := ι) (tag := tag)
      (max (arrival 0) initialBusyUntil) (work 0)
      capacity weight backlogged)
    (by intro t ht; rfl)
    hbacklogged_of_positive_canonicalRemainingWork

/--
Source-state formulation of the canonical remaining-work bridge.  If the
tagged backlog indicator is exactly the positivity indicator for canonical
tagged remaining work on the guaranteed service window, then the canonical
remaining-work backlog premise follows directly.
-/
theorem responseTime_zero_le_fcfsResponseTimeFrom_ofGPSDepartureFromCanonicalBacklogState
    (hcapacity : 0 ≤ capacity)
    (hweight_nonneg : ∀ i, 0 ≤ weight i)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (htagged_guaranteed_rate_pos : 0 < capacity * weight tag)
    (backlogged : ℝ → ι → Bool)
    (hbacklogged_meas : ∀ i, Measurable (fun t => backlogged t i))
    (hdeparture_eq_gps :
      departure 0 =
        gpsBackloggedDepartureFrom (ι := ι) (tag := tag)
          initialBusyUntil arrival work capacity weight backlogged 0)
    (hwork_nonneg : 0 ≤ work 0)
    (hbacklogged_eq_positive_canonicalRemainingWork : ∀ t,
      t ∈ Set.Ioo
        (max (arrival 0) initialBusyUntil)
        (max (arrival 0) initialBusyUntil +
          work 0 / (capacity * weight tag)) →
      backlogged t tag =
        decide (0 < gpsTaggedRemainingWorkFrom (ι := ι) (tag := tag)
          (max (arrival 0) initialBusyUntil) (work 0)
          capacity weight backlogged t)) :
    responseTime arrival departure 0 ≤
      responseTime arrival
        (fcfsDepartureFrom initialBusyUntil arrival work (capacity * weight tag))
        0 :=
  responseTime_zero_le_fcfsResponseTimeFrom_ofGPSDepartureFromCanonicalRemainingWork
    hcapacity hweight_nonneg htotal_weight_le_one htagged_guaranteed_rate_pos
    backlogged hbacklogged_meas hdeparture_eq_gps hwork_nonneg
    (by
      intro t ht hpositive
      rw [hbacklogged_eq_positive_canonicalRemainingWork t ht]
      simp [hpositive])

/--
Source-defined chronological GPS departure with tagged backlog state defined
by positive canonical remaining work, with `gpsBackloggedDepartureFrom` as the
departure process.
-/
theorem responseTime_zero_le_fcfsResponseTimeFrom_ofSourceGPSDepartureFromCanonicalBacklogState
    (hcapacity : 0 ≤ capacity)
    (hweight_nonneg : ∀ i, 0 ≤ weight i)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (htagged_guaranteed_rate_pos : 0 < capacity * weight tag)
    (backlogged : ℝ → ι → Bool)
    (hbacklogged_meas : ∀ i, Measurable (fun t => backlogged t i))
    (hwork_nonneg : 0 ≤ work 0)
    (hbacklogged_eq_positive_canonicalRemainingWork : ∀ t,
      t ∈ Set.Ioo
        (max (arrival 0) initialBusyUntil)
        (max (arrival 0) initialBusyUntil +
          work 0 / (capacity * weight tag)) →
      backlogged t tag =
        decide (0 < gpsTaggedRemainingWorkFrom (ι := ι) (tag := tag)
          (max (arrival 0) initialBusyUntil) (work 0)
          capacity weight backlogged t)) :
    responseTime arrival
        (gpsBackloggedDepartureFrom (ι := ι) (tag := tag)
          initialBusyUntil arrival work capacity weight backlogged) 0 ≤
      responseTime arrival
        (fcfsDepartureFrom initialBusyUntil arrival work (capacity * weight tag))
        0 :=
  responseTime_zero_le_fcfsResponseTimeFrom_ofGPSDepartureFromCanonicalBacklogState
    (departure := gpsBackloggedDepartureFrom (ι := ι) (tag := tag)
      initialBusyUntil arrival work capacity weight backlogged)
    hcapacity hweight_nonneg htotal_weight_le_one htagged_guaranteed_rate_pos
    backlogged hbacklogged_meas rfl hwork_nonneg
    hbacklogged_eq_positive_canonicalRemainingWork

/--
Backlog indicators generated by a real-valued remaining-work state vector:
a class is backlogged exactly when its remaining work is positive.
-/
def gpsBackloggedFromRemainingWork
    (remainingWork : ℝ → ι → ℝ) (t : ℝ) (i : ι) : Bool :=
  decide (0 < remainingWork t i)

/--
Positive initial class work makes the backlog generated from the canonical
remaining-work vector true at the service start.
-/
theorem gpsBackloggedFromRemainingWork_gpsRemainingWorkVectorFrom_start_eq_true_of_initialWork_pos
    {start capacity : ℝ} {initialWork : ι → ℝ}
    {weight : ι → ℝ} {backlogged : ℝ → ι → Bool} {i : ι}
    (hpos : 0 < initialWork i) :
    gpsBackloggedFromRemainingWork
        (gpsRemainingWorkVectorFrom start initialWork capacity weight backlogged)
        start i = true := by
  simp [gpsBackloggedFromRemainingWork, gpsRemainingWorkVectorFrom, hpos]

/--
Measurable remaining-work coordinates generate measurable finite-class backlog
indicators.
-/
theorem gpsBackloggedFromRemainingWork_measurable
    (remainingWork : ℝ → ι → ℝ)
    (hremaining_meas : ∀ i, Measurable (fun t => remainingWork t i)) :
    ∀ i, Measurable (fun t => gpsBackloggedFromRemainingWork remainingWork t i) := by
  classical
  intro i
  unfold gpsBackloggedFromRemainingWork
  exact Measurable.ite
    (measurableSet_lt measurable_const (hremaining_meas i))
    measurable_const measurable_const

/--
Source-defined chronological GPS departure with backlog generated from a
measurable remaining-work state vector.  The tagged coordinate's evolution
equation on the guaranteed service window implies the canonical backlog-state
premise used by the response comparison.
-/
theorem responseTime_zero_le_fcfsResponseTimeFrom_ofSourceGPSDepartureFromRemainingWorkState
    (hcapacity : 0 ≤ capacity)
    (hweight_nonneg : ∀ i, 0 ≤ weight i)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (htagged_guaranteed_rate_pos : 0 < capacity * weight tag)
    (remainingWork : ℝ → ι → ℝ)
    (hremaining_meas : ∀ i, Measurable (fun t => remainingWork t i))
    (hwork_nonneg : 0 ≤ work 0)
    (htag_remainingWork_eq_canonical : ∀ t,
      t ∈ Set.Ioo
        (max (arrival 0) initialBusyUntil)
        (max (arrival 0) initialBusyUntil +
          work 0 / (capacity * weight tag)) →
      remainingWork t tag =
        gpsTaggedRemainingWorkFrom (ι := ι) (tag := tag)
          (max (arrival 0) initialBusyUntil) (work 0)
          capacity weight (gpsBackloggedFromRemainingWork remainingWork) t) :
    responseTime arrival
        (gpsBackloggedDepartureFrom (ι := ι) (tag := tag)
          initialBusyUntil arrival work capacity weight
          (gpsBackloggedFromRemainingWork remainingWork)) 0 ≤
      responseTime arrival
        (fcfsDepartureFrom initialBusyUntil arrival work (capacity * weight tag))
        0 :=
  responseTime_zero_le_fcfsResponseTimeFrom_ofSourceGPSDepartureFromCanonicalBacklogState
    hcapacity hweight_nonneg htotal_weight_le_one htagged_guaranteed_rate_pos
    (gpsBackloggedFromRemainingWork remainingWork)
    (gpsBackloggedFromRemainingWork_measurable remainingWork hremaining_meas)
    hwork_nonneg
    (by
      intro t ht
      simp [gpsBackloggedFromRemainingWork,
        htag_remainingWork_eq_canonical t ht])

/--
Pathwise source certificate for the zero-th tagged job in a finite-class GPS
queue.  It records the exact deterministic obligations needed to compare the
source-defined GPS departure with the initial-workload FCFS comparator: finite
measurable backlog indicators, source-defined first-hit departure, nonnegative
tagged work, and the invariant that unfinished tagged work is marked
backlogged on the guaranteed service window.
-/
structure TaggedJobGPSUnfinishedWindowSourcePath
    (ι : Type*) [Fintype ι] [DecidableEq ι]
    (tag : ι) (initialBusyUntil : ℝ) (arrival work departure : ℕ → ℝ)
    (capacity : ℝ) (weight : ι → ℝ) where
  capacity_nonneg : 0 ≤ capacity
  weight_nonneg : ∀ i, 0 ≤ weight i
  total_weight_le_one : Finset.univ.sum weight ≤ 1
  tagged_guaranteed_rate_pos : 0 < capacity * weight tag
  backlogged : ℝ → ι → Bool
  backlogged_measurable : ∀ i, Measurable (fun t => backlogged t i)
  departure_eq_gps :
    departure 0 =
      gpsBackloggedDepartureFrom (ι := ι) (tag := tag)
        initialBusyUntil arrival work capacity weight backlogged 0
  work_nonneg : 0 ≤ work 0
  backlogged_of_unfinished_on_guaranteed_window : ∀ t,
    t ∈ Set.Ioo
      (max (arrival 0) initialBusyUntil)
      (max (arrival 0) initialBusyUntil + work 0 / (capacity * weight tag)) →
    (∫ u in (max (arrival 0) initialBusyUntil)..t,
      gpsBackloggedClassRate ι tag capacity weight backlogged u) < work 0 →
    backlogged t tag = true

namespace TaggedJobGPSUnfinishedWindowSourcePath

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {tag : ι} {initialBusyUntil capacity : ℝ}
variable {arrival work departure : ℕ → ℝ} {weight : ι → ℝ}

/--
The unfinished-window source certificate directly supplies the tagged
response bound used by the stochastic false-mark FCFS comparison.
-/
theorem responseTime_zero_le_fcfsResponseTimeFrom
    (H : TaggedJobGPSUnfinishedWindowSourcePath ι tag initialBusyUntil
      arrival work departure capacity weight) :
    responseTime arrival departure 0 ≤
      responseTime arrival
        (fcfsDepartureFrom initialBusyUntil arrival work (capacity * weight tag))
        0 :=
  responseTime_zero_le_fcfsResponseTimeFrom_ofGPSDepartureFromUnfinishedWindowBackloggedMeasurable
    H.capacity_nonneg H.weight_nonneg H.total_weight_le_one
    H.tagged_guaranteed_rate_pos H.backlogged H.backlogged_measurable
    H.departure_eq_gps H.work_nonneg
    H.backlogged_of_unfinished_on_guaranteed_window

/--
The unfinished-window certificate supplies the source-defined cumulative
service first-hit statement for the tagged job's departure.
-/
theorem departure_zero_cumulativeServiceFirstHitAt
    (H : TaggedJobGPSUnfinishedWindowSourcePath ι tag initialBusyUntil
      arrival work departure capacity weight) :
    cumulativeServiceFirstHitAt
      (max (arrival 0) initialBusyUntil) (work 0)
      (fun t =>
        ∫ u in (max (arrival 0) initialBusyUntil)..t,
          gpsBackloggedClassRate ι tag capacity weight H.backlogged u)
      (departure 0) := by
  let completionTime :=
    max (arrival 0) initialBusyUntil + work 0 / (capacity * weight tag)
  have hrate_intervalIntegrable_all :
      ∀ a b : ℝ,
        IntervalIntegrable
          (gpsBackloggedClassRate ι tag capacity weight H.backlogged)
          MeasureTheory.volume a b :=
    gpsBackloggedClassRate_intervalIntegrable_all_of_backlogged_measurable
      tag capacity weight H.backlogged H.backlogged_measurable
  have hstart_completion :
      max (arrival 0) initialBusyUntil ≤ completionTime := by
    have hdiv_nonneg :
        0 ≤ work 0 / (capacity * weight tag) :=
      div_nonneg H.work_nonneg H.tagged_guaranteed_rate_pos.le
    dsimp [completionTime]
    linarith
  have hreaches :
      work 0 ≤
        ∫ u in (max (arrival 0) initialBusyUntil)..completionTime,
          gpsBackloggedClassRate ι tag capacity weight H.backlogged u := by
    dsimp [completionTime]
    exact
      cumulativeService_reaches_at_guaranteedWindow_of_backlogged_if_unfinished
        (tag := tag) H.capacity_nonneg H.weight_nonneg
        H.total_weight_le_one H.tagged_guaranteed_rate_pos H.work_nonneg
        (hrate_intervalIntegrable_all
          (max (arrival 0) initialBusyUntil)
          (max (arrival 0) initialBusyUntil +
            work 0 / (capacity * weight tag)))
        H.backlogged_of_unfinished_on_guaranteed_window
  have hfirst_gps :
      cumulativeServiceFirstHitAt
        (max (arrival 0) initialBusyUntil) (work 0)
        (fun t =>
          ∫ u in (max (arrival 0) initialBusyUntil)..t,
            gpsBackloggedClassRate ι tag capacity weight H.backlogged u)
        (gpsBackloggedDepartureFrom (ι := ι) (tag := tag)
          initialBusyUntil arrival work capacity weight H.backlogged 0) :=
    gpsBackloggedDepartureFrom_zero_firstHitAt_of_reaches
      (ι := ι) (tag := tag)
      (initialBusyUntil := initialBusyUntil)
      (arrival := arrival) (work := work)
      (capacity := capacity) (weight := weight)
      (backlogged := H.backlogged) (witness := completionTime)
      hstart_completion hreaches
  simpa [H.departure_eq_gps] using hfirst_gps

/--
The source-defined first-hit statement is a least-hit statement for the
continuous cumulative tagged service path.
-/
theorem departure_zero_isLeast_hit
    (H : TaggedJobGPSUnfinishedWindowSourcePath ι tag initialBusyUntil
      arrival work departure capacity weight) :
    IsLeast
      (cumulativeServiceHitSet
        (max (arrival 0) initialBusyUntil) (work 0)
        (fun t =>
          ∫ u in (max (arrival 0) initialBusyUntil)..t,
            gpsBackloggedClassRate ι tag capacity weight H.backlogged u))
      (departure 0) := by
  have hrate_intervalIntegrable_all :
      ∀ a b : ℝ,
        IntervalIntegrable
          (gpsBackloggedClassRate ι tag capacity weight H.backlogged)
          MeasureTheory.volume a b :=
    gpsBackloggedClassRate_intervalIntegrable_all_of_backlogged_measurable
      tag capacity weight H.backlogged H.backlogged_measurable
  have hcontinuous :
      Continuous
        (fun t =>
          ∫ u in (max (arrival 0) initialBusyUntil)..t,
            gpsBackloggedClassRate ι tag capacity weight H.backlogged u) :=
    intervalIntegral.continuous_primitive hrate_intervalIntegrable_all
      (max (arrival 0) initialBusyUntil)
  exact
    cumulativeServiceFirstHitAt_isLeast_of_continuous hcontinuous
      H.departure_zero_cumulativeServiceFirstHitAt

/--
The tagged source departure lies within the guaranteed service window.
-/
theorem departure_zero_le_guaranteedWindow
    (H : TaggedJobGPSUnfinishedWindowSourcePath ι tag initialBusyUntil
      arrival work departure capacity weight) :
    departure 0 ≤
      max (arrival 0) initialBusyUntil + work 0 / (capacity * weight tag) := by
  rw [H.departure_eq_gps]
  exact
    gpsBackloggedDepartureFrom_zero_le_guaranteedWindow_of_backlogged_if_unfinished
      (ι := ι) (tag := tag)
      (initialBusyUntil := initialBusyUntil)
      (arrival := arrival) (work := work)
      (capacity := capacity) (weight := weight)
      H.capacity_nonneg H.weight_nonneg H.total_weight_le_one
      H.tagged_guaranteed_rate_pos H.backlogged H.backlogged_measurable
      H.work_nonneg H.backlogged_of_unfinished_on_guaranteed_window

/--
Before the least-hit departure, cumulative tagged GPS service is still below
the tagged job's work.
-/
theorem cumulativeService_before_departure_lt_work
    (H : TaggedJobGPSUnfinishedWindowSourcePath ι tag initialBusyUntil
      arrival work departure capacity weight) {t : ℝ}
    (ht : t ∈ Set.Ioo (max (arrival 0) initialBusyUntil) (departure 0)) :
    (∫ u in (max (arrival 0) initialBusyUntil)..t,
      gpsBackloggedClassRate ι tag capacity weight H.backlogged u) < work 0 :=
  cumulativeService_lt_work_of_isLeast_hit H.departure_zero_isLeast_hit ht

/--
For positive tagged work, cumulative tagged GPS service equals the tagged
job's work at the source-defined departure.
-/
theorem cumulativeService_at_departure_eq_work_of_work_pos
    (H : TaggedJobGPSUnfinishedWindowSourcePath ι tag initialBusyUntil
      arrival work departure capacity weight)
    (hwork_pos : 0 < work 0) :
    (∫ u in (max (arrival 0) initialBusyUntil)..departure 0,
      gpsBackloggedClassRate ι tag capacity weight H.backlogged u) = work 0 := by
  let cumulativeService : ℝ → ℝ :=
    fun t =>
      ∫ u in (max (arrival 0) initialBusyUntil)..t,
        gpsBackloggedClassRate ι tag capacity weight H.backlogged u
  have hrate_intervalIntegrable_all :
      ∀ a b : ℝ,
        IntervalIntegrable
          (gpsBackloggedClassRate ι tag capacity weight H.backlogged)
          MeasureTheory.volume a b :=
    gpsBackloggedClassRate_intervalIntegrable_all_of_backlogged_measurable
      tag capacity weight H.backlogged H.backlogged_measurable
  have hcontinuous :
      Continuous cumulativeService := by
    dsimp [cumulativeService]
    exact
      intervalIntegral.continuous_primitive hrate_intervalIntegrable_all
        (max (arrival 0) initialBusyUntil)
  have hfirst :
      IsLeast
        (cumulativeServiceHitSet
          (max (arrival 0) initialBusyUntil) (work 0) cumulativeService)
        (departure 0) := by
    simpa [cumulativeService] using H.departure_zero_isLeast_hit
  have hstart_below :
      cumulativeService (max (arrival 0) initialBusyUntil) < work 0 := by
    simpa [cumulativeService] using hwork_pos
  have heq :
      cumulativeService (departure 0) = work 0 :=
    cumulativeService_eq_work_of_isLeast_hit_of_continuousAt
      (start := max (arrival 0) initialBusyUntil)
      (jobWork := work 0) (departureTime := departure 0)
      (cumulativeService := cumulativeService)
      hfirst hstart_below
      hcontinuous.continuousAt
  simpa [cumulativeService] using heq

/--
With positive tagged work, the unfinished-window certificate yields the
open-backlog integral source certificate at the comparator start.
-/
def toOpenBacklogIntegralSourcePath_of_work_pos
    (H : TaggedJobGPSUnfinishedWindowSourcePath ι tag initialBusyUntil
      arrival work departure capacity weight)
    (hwork_pos : 0 < work 0) :
    TaggedJobGPSOpenBacklogIntegralSourcePath ι tag initialBusyUntil
      arrival work departure capacity weight :=
  ofFirstHitFromComparatorStart H.capacity_nonneg H.weight_nonneg
    H.total_weight_le_one H.tagged_guaranteed_rate_pos
    H.departure_zero_isLeast_hit.1.1 H.backlogged
    (gpsBackloggedClassRate_intervalIntegrable_all_of_backlogged_measurable
      tag capacity weight H.backlogged H.backlogged_measurable
      (max (arrival 0) initialBusyUntil) (departure 0))
    (by
      intro t ht hunfinished
      exact H.backlogged_of_unfinished_on_guaranteed_window t
        ⟨ht.1, lt_of_lt_of_le ht.2 H.departure_zero_le_guaranteedWindow⟩
        hunfinished)
    (fun t ht => H.cumulativeService_before_departure_lt_work ht)
    (H.cumulativeService_at_departure_eq_work_of_work_pos hwork_pos)

end TaggedJobGPSUnfinishedWindowSourcePath

/--
Pathwise source certificate whose backlog condition is stated through tagged
remaining work.  This matches the natural GPS queue state: on the guaranteed
service window, remaining tagged work is initial work minus cumulative tagged
GPS service, and positive remaining work means the tagged class is backlogged.
-/
structure TaggedJobGPSRemainingWorkSourcePath
    (ι : Type*) [Fintype ι] [DecidableEq ι]
    (tag : ι) (initialBusyUntil : ℝ) (arrival work departure : ℕ → ℝ)
    (capacity : ℝ) (weight : ι → ℝ) where
  capacity_nonneg : 0 ≤ capacity
  weight_nonneg : ∀ i, 0 ≤ weight i
  total_weight_le_one : Finset.univ.sum weight ≤ 1
  tagged_guaranteed_rate_pos : 0 < capacity * weight tag
  backlogged : ℝ → ι → Bool
  backlogged_measurable : ∀ i, Measurable (fun t => backlogged t i)
  departure_eq_gps :
    departure 0 =
      gpsBackloggedDepartureFrom (ι := ι) (tag := tag)
        initialBusyUntil arrival work capacity weight backlogged 0
  work_nonneg : 0 ≤ work 0
  remainingWork : ℝ → ℝ
  remainingWork_eq_on_guaranteed_window : ∀ t,
    t ∈ Set.Ioo
      (max (arrival 0) initialBusyUntil)
      (max (arrival 0) initialBusyUntil + work 0 / (capacity * weight tag)) →
    remainingWork t =
      work 0 -
        ∫ u in (max (arrival 0) initialBusyUntil)..t,
          gpsBackloggedClassRate ι tag capacity weight backlogged u
  backlogged_of_positive_remainingWork : ∀ t,
    t ∈ Set.Ioo
      (max (arrival 0) initialBusyUntil)
      (max (arrival 0) initialBusyUntil + work 0 / (capacity * weight tag)) →
    0 < remainingWork t →
    backlogged t tag = true

namespace TaggedJobGPSRemainingWorkSourcePath

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {tag : ι} {initialBusyUntil capacity : ℝ}
variable {arrival work departure : ℕ → ℝ} {weight : ι → ℝ}

/-- A remaining-work source certificate implies the unfinished-window certificate. -/
def toUnfinishedWindowSourcePath
    (H : TaggedJobGPSRemainingWorkSourcePath ι tag initialBusyUntil
      arrival work departure capacity weight) :
    TaggedJobGPSUnfinishedWindowSourcePath ι tag initialBusyUntil
      arrival work departure capacity weight where
  capacity_nonneg := H.capacity_nonneg
  weight_nonneg := H.weight_nonneg
  total_weight_le_one := H.total_weight_le_one
  tagged_guaranteed_rate_pos := H.tagged_guaranteed_rate_pos
  backlogged := H.backlogged
  backlogged_measurable := H.backlogged_measurable
  departure_eq_gps := H.departure_eq_gps
  work_nonneg := H.work_nonneg
  backlogged_of_unfinished_on_guaranteed_window := by
    intro t ht hunfinished
    exact H.backlogged_of_positive_remainingWork t ht
      (by
        rw [H.remainingWork_eq_on_guaranteed_window t ht]
        linarith)

/--
The remaining-work source certificate directly supplies the tagged response
bound used by the stochastic false-mark FCFS comparison.
-/
theorem responseTime_zero_le_fcfsResponseTimeFrom
    (H : TaggedJobGPSRemainingWorkSourcePath ι tag initialBusyUntil
      arrival work departure capacity weight) :
    responseTime arrival departure 0 ≤
      responseTime arrival
        (fcfsDepartureFrom initialBusyUntil arrival work (capacity * weight tag))
        0 :=
  H.toUnfinishedWindowSourcePath.responseTime_zero_le_fcfsResponseTimeFrom

end TaggedJobGPSRemainingWorkSourcePath

/--
Pathwise source certificate whose remaining work is the canonical tagged GPS
state: initial tagged work minus cumulative tagged GPS service from the service
start.  The only backlog-state premise is that positive canonical remaining
work marks the tagged class as backlogged on the guaranteed service window.
-/
structure TaggedJobGPSCanonicalRemainingWorkSourcePath
    (ι : Type*) [Fintype ι] [DecidableEq ι]
    (tag : ι) (initialBusyUntil : ℝ) (arrival work departure : ℕ → ℝ)
    (capacity : ℝ) (weight : ι → ℝ) where
  capacity_nonneg : 0 ≤ capacity
  weight_nonneg : ∀ i, 0 ≤ weight i
  total_weight_le_one : Finset.univ.sum weight ≤ 1
  tagged_guaranteed_rate_pos : 0 < capacity * weight tag
  backlogged : ℝ → ι → Bool
  backlogged_measurable : ∀ i, Measurable (fun t => backlogged t i)
  departure_eq_gps :
    departure 0 =
      gpsBackloggedDepartureFrom (ι := ι) (tag := tag)
        initialBusyUntil arrival work capacity weight backlogged 0
  work_nonneg : 0 ≤ work 0
  backlogged_of_positive_canonicalRemainingWork : ∀ t,
    t ∈ Set.Ioo
      (max (arrival 0) initialBusyUntil)
      (max (arrival 0) initialBusyUntil + work 0 / (capacity * weight tag)) →
    0 < gpsTaggedRemainingWorkFrom (ι := ι) (tag := tag)
      (max (arrival 0) initialBusyUntil) (work 0)
      capacity weight backlogged t →
    backlogged t tag = true

namespace TaggedJobGPSCanonicalRemainingWorkSourcePath

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {tag : ι} {initialBusyUntil capacity : ℝ}
variable {arrival work departure : ℕ → ℝ} {weight : ι → ℝ}

/-- A canonical remaining-work source certificate implies the remaining-work certificate. -/
def toRemainingWorkSourcePath
    (H : TaggedJobGPSCanonicalRemainingWorkSourcePath ι tag initialBusyUntil
      arrival work departure capacity weight) :
    TaggedJobGPSRemainingWorkSourcePath ι tag initialBusyUntil
      arrival work departure capacity weight where
  capacity_nonneg := H.capacity_nonneg
  weight_nonneg := H.weight_nonneg
  total_weight_le_one := H.total_weight_le_one
  tagged_guaranteed_rate_pos := H.tagged_guaranteed_rate_pos
  backlogged := H.backlogged
  backlogged_measurable := H.backlogged_measurable
  departure_eq_gps := H.departure_eq_gps
  work_nonneg := H.work_nonneg
  remainingWork :=
    gpsTaggedRemainingWorkFrom (ι := ι) (tag := tag)
      (max (arrival 0) initialBusyUntil) (work 0)
      capacity weight H.backlogged
  remainingWork_eq_on_guaranteed_window := by
    intro t ht
    rfl
  backlogged_of_positive_remainingWork :=
    H.backlogged_of_positive_canonicalRemainingWork

/--
The canonical remaining-work source certificate directly supplies the tagged
response bound used by the stochastic false-mark FCFS comparison.
-/
theorem responseTime_zero_le_fcfsResponseTimeFrom
    (H : TaggedJobGPSCanonicalRemainingWorkSourcePath ι tag initialBusyUntil
      arrival work departure capacity weight) :
    responseTime arrival departure 0 ≤
      responseTime arrival
        (fcfsDepartureFrom initialBusyUntil arrival work (capacity * weight tag))
        0 :=
  H.toRemainingWorkSourcePath.responseTime_zero_le_fcfsResponseTimeFrom

end TaggedJobGPSCanonicalRemainingWorkSourcePath

/--
Pathwise source certificate where the tagged backlog state is defined by
positive canonical tagged remaining work on the guaranteed service window.
-/
structure TaggedJobGPSCanonicalBacklogStateSourcePath
    (ι : Type*) [Fintype ι] [DecidableEq ι]
    (tag : ι) (initialBusyUntil : ℝ) (arrival work departure : ℕ → ℝ)
    (capacity : ℝ) (weight : ι → ℝ) where
  capacity_nonneg : 0 ≤ capacity
  weight_nonneg : ∀ i, 0 ≤ weight i
  total_weight_le_one : Finset.univ.sum weight ≤ 1
  tagged_guaranteed_rate_pos : 0 < capacity * weight tag
  backlogged : ℝ → ι → Bool
  backlogged_measurable : ∀ i, Measurable (fun t => backlogged t i)
  departure_eq_gps :
    departure 0 =
      gpsBackloggedDepartureFrom (ι := ι) (tag := tag)
        initialBusyUntil arrival work capacity weight backlogged 0
  work_nonneg : 0 ≤ work 0
  backlogged_eq_positive_canonicalRemainingWork : ∀ t,
    t ∈ Set.Ioo
      (max (arrival 0) initialBusyUntil)
      (max (arrival 0) initialBusyUntil + work 0 / (capacity * weight tag)) →
    backlogged t tag =
      decide (0 < gpsTaggedRemainingWorkFrom (ι := ι) (tag := tag)
        (max (arrival 0) initialBusyUntil) (work 0)
        capacity weight backlogged t)

namespace TaggedJobGPSCanonicalBacklogStateSourcePath

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {tag : ι} {initialBusyUntil capacity : ℝ}
variable {arrival work departure : ℕ → ℝ} {weight : ι → ℝ}

/-- A canonical backlog-state certificate implies the canonical remaining-work certificate. -/
def toCanonicalRemainingWorkSourcePath
    (H : TaggedJobGPSCanonicalBacklogStateSourcePath ι tag initialBusyUntil
      arrival work departure capacity weight) :
    TaggedJobGPSCanonicalRemainingWorkSourcePath ι tag initialBusyUntil
      arrival work departure capacity weight where
  capacity_nonneg := H.capacity_nonneg
  weight_nonneg := H.weight_nonneg
  total_weight_le_one := H.total_weight_le_one
  tagged_guaranteed_rate_pos := H.tagged_guaranteed_rate_pos
  backlogged := H.backlogged
  backlogged_measurable := H.backlogged_measurable
  departure_eq_gps := H.departure_eq_gps
  work_nonneg := H.work_nonneg
  backlogged_of_positive_canonicalRemainingWork := by
    intro t ht hpositive
    rw [H.backlogged_eq_positive_canonicalRemainingWork t ht]
    simp [hpositive]

/--
The canonical backlog-state source certificate directly supplies the tagged
response bound used by the stochastic false-mark FCFS comparison.
-/
theorem responseTime_zero_le_fcfsResponseTimeFrom
    (H : TaggedJobGPSCanonicalBacklogStateSourcePath ι tag initialBusyUntil
      arrival work departure capacity weight) :
    responseTime arrival departure 0 ≤
      responseTime arrival
        (fcfsDepartureFrom initialBusyUntil arrival work (capacity * weight tag))
        0 :=
  H.toCanonicalRemainingWorkSourcePath.responseTime_zero_le_fcfsResponseTimeFrom

/--
Constructor for the canonical backlog-state source path when the departure
process is the source-defined GPS first-hit recurrence.
-/
def ofSourceGPSDepartureFrom
    (hcapacity : 0 ≤ capacity)
    (hweight_nonneg : ∀ i, 0 ≤ weight i)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (htagged_guaranteed_rate_pos : 0 < capacity * weight tag)
    (backlogged : ℝ → ι → Bool)
    (hbacklogged_meas : ∀ i, Measurable (fun t => backlogged t i))
    (hwork_nonneg : 0 ≤ work 0)
    (hbacklogged_eq_positive_canonicalRemainingWork : ∀ t,
      t ∈ Set.Ioo
        (max (arrival 0) initialBusyUntil)
        (max (arrival 0) initialBusyUntil +
          work 0 / (capacity * weight tag)) →
      backlogged t tag =
        decide (0 < gpsTaggedRemainingWorkFrom (ι := ι) (tag := tag)
          (max (arrival 0) initialBusyUntil) (work 0)
          capacity weight backlogged t)) :
    TaggedJobGPSCanonicalBacklogStateSourcePath ι tag initialBusyUntil
      arrival work
      (gpsBackloggedDepartureFrom (ι := ι) (tag := tag)
        initialBusyUntil arrival work capacity weight backlogged)
      capacity weight where
  capacity_nonneg := hcapacity
  weight_nonneg := hweight_nonneg
  total_weight_le_one := htotal_weight_le_one
  tagged_guaranteed_rate_pos := htagged_guaranteed_rate_pos
  backlogged := backlogged
  backlogged_measurable := hbacklogged_meas
  departure_eq_gps := rfl
  work_nonneg := hwork_nonneg
  backlogged_eq_positive_canonicalRemainingWork :=
    hbacklogged_eq_positive_canonicalRemainingWork

/--
Constructor for the source-defined GPS path when backlog is generated by a
measurable classwise remaining-work vector and the tagged coordinate agrees
with canonical tagged remaining work on the guaranteed service window.
-/
def ofSourceGPSDepartureFromRemainingWorkState
    (hcapacity : 0 ≤ capacity)
    (hweight_nonneg : ∀ i, 0 ≤ weight i)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (htagged_guaranteed_rate_pos : 0 < capacity * weight tag)
    (remainingWork : ℝ → ι → ℝ)
    (hremaining_meas : ∀ i, Measurable (fun t => remainingWork t i))
    (hwork_nonneg : 0 ≤ work 0)
    (htag_remainingWork_eq_canonical : ∀ t,
      t ∈ Set.Ioo
        (max (arrival 0) initialBusyUntil)
        (max (arrival 0) initialBusyUntil +
          work 0 / (capacity * weight tag)) →
      remainingWork t tag =
        gpsTaggedRemainingWorkFrom (ι := ι) (tag := tag)
          (max (arrival 0) initialBusyUntil) (work 0)
          capacity weight (gpsBackloggedFromRemainingWork remainingWork) t) :
    TaggedJobGPSCanonicalBacklogStateSourcePath ι tag initialBusyUntil
      arrival work
      (gpsBackloggedDepartureFrom (ι := ι) (tag := tag)
        initialBusyUntil arrival work capacity weight
        (gpsBackloggedFromRemainingWork remainingWork))
      capacity weight :=
  ofSourceGPSDepartureFrom hcapacity hweight_nonneg htotal_weight_le_one
    htagged_guaranteed_rate_pos
    (gpsBackloggedFromRemainingWork remainingWork)
    (gpsBackloggedFromRemainingWork_measurable remainingWork hremaining_meas)
    hwork_nonneg
    (by
      intro t ht
      simp [gpsBackloggedFromRemainingWork,
        htag_remainingWork_eq_canonical t ht])

/--
Constructor for the source-defined GPS path when backlog is generated by a
measurable classwise remaining-work vector.  The source only needs to identify
the tagged initial coordinate with the tagged job work and prove the tagged
coordinate's classwise remaining-work evolution on the guaranteed service
window; the canonical tagged remaining-work formulation is derived internally.
-/
def ofSourceGPSDepartureFromRemainingWorkVector
    (hcapacity : 0 ≤ capacity)
    (hweight_nonneg : ∀ i, 0 ≤ weight i)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (htagged_guaranteed_rate_pos : 0 < capacity * weight tag)
    (initialWork : ι → ℝ)
    (remainingWork : ℝ → ι → ℝ)
    (hremaining_meas : ∀ i, Measurable (fun t => remainingWork t i))
    (hwork_nonneg : 0 ≤ work 0)
    (hinitial_tag : initialWork tag = work 0)
    (htag_remainingWork_eq_vector : ∀ t,
      t ∈ Set.Ioo
        (max (arrival 0) initialBusyUntil)
        (max (arrival 0) initialBusyUntil +
          work 0 / (capacity * weight tag)) →
      remainingWork t tag =
        gpsRemainingWorkVectorFrom
          (max (arrival 0) initialBusyUntil)
          initialWork capacity weight
          (gpsBackloggedFromRemainingWork remainingWork) t tag) :
    TaggedJobGPSCanonicalBacklogStateSourcePath ι tag initialBusyUntil
      arrival work
      (gpsBackloggedDepartureFrom (ι := ι) (tag := tag)
        initialBusyUntil arrival work capacity weight
        (gpsBackloggedFromRemainingWork remainingWork))
      capacity weight :=
  ofSourceGPSDepartureFromRemainingWorkState hcapacity hweight_nonneg
    htotal_weight_le_one htagged_guaranteed_rate_pos remainingWork
    hremaining_meas hwork_nonneg
    (by
      intro t ht
      calc
        remainingWork t tag =
            gpsRemainingWorkVectorFrom
              (max (arrival 0) initialBusyUntil)
              initialWork capacity weight
              (gpsBackloggedFromRemainingWork remainingWork) t tag :=
          htag_remainingWork_eq_vector t ht
        _ =
            gpsTaggedRemainingWorkFrom (ι := ι) (tag := tag)
              (max (arrival 0) initialBusyUntil) (work 0)
              capacity weight (gpsBackloggedFromRemainingWork remainingWork) t :=
          gpsRemainingWorkVectorFrom_tag_eq_gpsTaggedRemainingWorkFrom
            (ι := ι) (tag := tag)
            (start := max (arrival 0) initialBusyUntil)
            (jobWork := work 0)
            (capacity := capacity) (initialWork := initialWork)
            (weight := weight)
            (backlogged := gpsBackloggedFromRemainingWork remainingWork)
            (t := t) hinitial_tag)

/--
The classwise remaining-work-vector constructor yields the unfinished-window
source certificate: measurable backlog indicators, source-defined departure,
and tagged backlog whenever the tagged job is unfinished on the guaranteed
service window.
-/
def unfinishedWindowSourcePath_ofSourceGPSDepartureFromRemainingWorkVector
    (hcapacity : 0 ≤ capacity)
    (hweight_nonneg : ∀ i, 0 ≤ weight i)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (htagged_guaranteed_rate_pos : 0 < capacity * weight tag)
    (initialWork : ι → ℝ)
    (remainingWork : ℝ → ι → ℝ)
    (hremaining_meas : ∀ i, Measurable (fun t => remainingWork t i))
    (hwork_nonneg : 0 ≤ work 0)
    (hinitial_tag : initialWork tag = work 0)
    (htag_remainingWork_eq_vector : ∀ t,
      t ∈ Set.Ioo
        (max (arrival 0) initialBusyUntil)
        (max (arrival 0) initialBusyUntil +
          work 0 / (capacity * weight tag)) →
      remainingWork t tag =
        gpsRemainingWorkVectorFrom
          (max (arrival 0) initialBusyUntil)
          initialWork capacity weight
          (gpsBackloggedFromRemainingWork remainingWork) t tag) :
    TaggedJobGPSUnfinishedWindowSourcePath ι tag initialBusyUntil
      arrival work
      (gpsBackloggedDepartureFrom (ι := ι) (tag := tag)
      initialBusyUntil arrival work capacity weight
      (gpsBackloggedFromRemainingWork remainingWork))
      capacity weight :=
  let H :=
    ofSourceGPSDepartureFromRemainingWorkVector
      (ι := ι) (tag := tag) (initialBusyUntil := initialBusyUntil)
      (arrival := arrival) (work := work) (capacity := capacity)
      (weight := weight) hcapacity hweight_nonneg htotal_weight_le_one
      htagged_guaranteed_rate_pos initialWork remainingWork hremaining_meas
      hwork_nonneg hinitial_tag htag_remainingWork_eq_vector
  H.toCanonicalRemainingWorkSourcePath.toRemainingWorkSourcePath.toUnfinishedWindowSourcePath

/--
The classwise remaining-work-vector constructor directly yields the tagged
response comparison against the FCFS initial-workload comparator.
-/
theorem responseTime_zero_le_fcfsResponseTimeFrom_ofSourceGPSDepartureFromRemainingWorkVector
    (hcapacity : 0 ≤ capacity)
    (hweight_nonneg : ∀ i, 0 ≤ weight i)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (htagged_guaranteed_rate_pos : 0 < capacity * weight tag)
    (initialWork : ι → ℝ)
    (remainingWork : ℝ → ι → ℝ)
    (hremaining_meas : ∀ i, Measurable (fun t => remainingWork t i))
    (hwork_nonneg : 0 ≤ work 0)
    (hinitial_tag : initialWork tag = work 0)
    (htag_remainingWork_eq_vector : ∀ t,
      t ∈ Set.Ioo
        (max (arrival 0) initialBusyUntil)
        (max (arrival 0) initialBusyUntil +
          work 0 / (capacity * weight tag)) →
      remainingWork t tag =
        gpsRemainingWorkVectorFrom
          (max (arrival 0) initialBusyUntil)
          initialWork capacity weight
          (gpsBackloggedFromRemainingWork remainingWork) t tag) :
    responseTime arrival
        (gpsBackloggedDepartureFrom (ι := ι) (tag := tag)
          initialBusyUntil arrival work capacity weight
          (gpsBackloggedFromRemainingWork remainingWork)) 0 ≤
      responseTime arrival
        (fcfsDepartureFrom initialBusyUntil arrival work (capacity * weight tag))
        0 :=
  (unfinishedWindowSourcePath_ofSourceGPSDepartureFromRemainingWorkVector
    (ι := ι) (tag := tag) (initialBusyUntil := initialBusyUntil)
    (arrival := arrival) (work := work) (capacity := capacity)
    (weight := weight) hcapacity hweight_nonneg htotal_weight_le_one
    htagged_guaranteed_rate_pos initialWork remainingWork hremaining_meas
    hwork_nonneg hinitial_tag htag_remainingWork_eq_vector).responseTime_zero_le_fcfsResponseTimeFrom

end TaggedJobGPSCanonicalBacklogStateSourcePath

end TaggedJobGPSOpenBacklogIntegralSourcePath

/--
All-jobs finite-class GPS source data with active classes defined by backlog
indicators.  The certificate records the tagged class's actual service interval
for every arrival, the backlog-induced GPS rate, and a cumulative service path
whose interval increments equal completed work.
-/
structure TaggedClassGPSOpenBacklogIntegralSourcePath
    (ι : Type*) [Fintype ι] [DecidableEq ι]
    (tag : ι) (initialBusyUntil : ℝ) (arrival work departure : ℕ → ℝ)
    (capacity : ℝ) (weight : ι → ℝ) where
  capacity_nonneg : 0 ≤ capacity
  weight_nonneg : ∀ i, 0 ≤ weight i
  total_weight_le_one : Finset.univ.sum weight ≤ 1
  tagged_guaranteed_rate_pos : 0 < capacity * weight tag
  actualServiceStart : ℕ → ℝ
  arrival_le_actualServiceStart : ∀ n, arrival n ≤ actualServiceStart n
  departure_after_actualServiceStart : ∀ n,
    actualServiceStart n ≤ departure n
  actualStart_zero_le_comparatorStart :
    actualServiceStart 0 ≤ max (arrival 0) initialBusyUntil
  actualStart_succ_le_comparatorStart : ∀ n,
    actualServiceStart (n + 1) ≤ max (arrival (n + 1)) (departure n)
  backlogged : ℝ → ι → Bool
  service : ℝ → ℝ
  rate_intervalIntegrable : ∀ n,
    IntervalIntegrable
      (gpsBackloggedClassRate ι tag capacity weight backlogged)
      MeasureTheory.volume (actualServiceStart n) (departure n)
  tag_backlogged_on_open_actual_job : ∀ n t,
    t ∈ Set.Ioo (actualServiceStart n) (departure n) →
      backlogged t tag = true
  service_increment_eq_integral : ∀ n,
    service (departure n) - service (actualServiceStart n) =
      ∫ t in actualServiceStart n..departure n,
        gpsBackloggedClassRate ι tag capacity weight backlogged t
  completed_work_eq_service : ∀ n,
    service (departure n) - service (actualServiceStart n) = work n

namespace TaggedClassGPSOpenBacklogIntegralSourcePath

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {tag : ι} {initialBusyUntil capacity : ℝ}
variable {arrival work departure : ℕ → ℝ} {weight : ι → ℝ}

open TaggedJobGPSOpenBacklogIntegralSourcePath

/-- Chronological tagged-class service starts for the FCFS/GPS comparator recurrence. -/
def comparatorServiceStartFrom
    (initialBusyUntil : ℝ) (arrival departure : ℕ → ℝ) : ℕ → ℝ
  | 0 => max (arrival 0) initialBusyUntil
  | n + 1 => max (arrival (n + 1)) (departure n)

/-- Global cumulative tagged-class GPS service induced by backlog indicators. -/
def globalCumulativeService
    (capacity : ℝ) (weight : ι → ℝ) (backlogged : ℝ → ι → Bool)
    (t : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..t,
    gpsBackloggedClassRate ι tag capacity weight backlogged u

/--
The global cumulative service process has interval increments equal to the
corresponding backlog-induced GPS rate integral.
-/
theorem globalCumulativeService_increment_eq_integral
    {backlogged : ℝ → ι → Bool}
    (hrate_intervalIntegrable_all : ∀ a b : ℝ,
      IntervalIntegrable
        (gpsBackloggedClassRate ι tag capacity weight backlogged)
        MeasureTheory.volume a b)
    (a b : ℝ) :
    globalCumulativeService (ι := ι) (tag := tag)
        capacity weight backlogged b -
      globalCumulativeService (ι := ι) (tag := tag)
        capacity weight backlogged a =
      ∫ u in a..b,
        gpsBackloggedClassRate ι tag capacity weight backlogged u := by
  simpa [globalCumulativeService] using
    (intervalIntegral.integral_interval_sub_left
      (μ := MeasureTheory.volume)
      (f := fun u : ℝ =>
        gpsBackloggedClassRate ι tag capacity weight backlogged u)
      (a := (0 : ℝ)) (b := b) (c := a)
      (hrate_intervalIntegrable_all (0 : ℝ) b)
      (hrate_intervalIntegrable_all (0 : ℝ) a))

/--
Constructor from all-jobs actual service starts and interval-integral work
identities.  The service process is the global cumulative tagged-class GPS
service induced by the backlog indicators.
-/
def ofGlobalCumulativeService
    (hcapacity : 0 ≤ capacity)
    (hweight_nonneg : ∀ i, 0 ≤ weight i)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (htagged_guaranteed_rate_pos : 0 < capacity * weight tag)
    (actualServiceStart : ℕ → ℝ)
    (harrival_le_actualServiceStart : ∀ n,
      arrival n ≤ actualServiceStart n)
    (hdeparture_after_actualServiceStart : ∀ n,
      actualServiceStart n ≤ departure n)
    (hactualStart_zero_le_comparatorStart :
      actualServiceStart 0 ≤ max (arrival 0) initialBusyUntil)
    (hactualStart_succ_le_comparatorStart : ∀ n,
      actualServiceStart (n + 1) ≤ max (arrival (n + 1)) (departure n))
    (backlogged : ℝ → ι → Bool)
    (hrate_intervalIntegrable_all : ∀ a b : ℝ,
      IntervalIntegrable
        (gpsBackloggedClassRate ι tag capacity weight backlogged)
        MeasureTheory.volume a b)
    (htag_backlogged_on_open_actual_job : ∀ n t,
      t ∈ Set.Ioo (actualServiceStart n) (departure n) →
        backlogged t tag = true)
    (hcompleted_work_eq_integral : ∀ n,
      ∫ t in actualServiceStart n..departure n,
        gpsBackloggedClassRate ι tag capacity weight backlogged t =
          work n) :
    TaggedClassGPSOpenBacklogIntegralSourcePath ι tag initialBusyUntil
      arrival work departure capacity weight where
  capacity_nonneg := hcapacity
  weight_nonneg := hweight_nonneg
  total_weight_le_one := htotal_weight_le_one
  tagged_guaranteed_rate_pos := htagged_guaranteed_rate_pos
  actualServiceStart := actualServiceStart
  arrival_le_actualServiceStart := harrival_le_actualServiceStart
  departure_after_actualServiceStart := hdeparture_after_actualServiceStart
  actualStart_zero_le_comparatorStart := hactualStart_zero_le_comparatorStart
  actualStart_succ_le_comparatorStart := hactualStart_succ_le_comparatorStart
  backlogged := backlogged
  service :=
    globalCumulativeService (ι := ι) (tag := tag)
      capacity weight backlogged
  rate_intervalIntegrable := fun n =>
    hrate_intervalIntegrable_all (actualServiceStart n) (departure n)
  tag_backlogged_on_open_actual_job := htag_backlogged_on_open_actual_job
  service_increment_eq_integral := by
    intro n
    exact globalCumulativeService_increment_eq_integral
      (ι := ι) (tag := tag) (capacity := capacity) (weight := weight)
      (backlogged := backlogged) hrate_intervalIntegrable_all
      (actualServiceStart n) (departure n)
  completed_work_eq_service := by
    intro n
    rw [globalCumulativeService_increment_eq_integral
      (ι := ι) (tag := tag) (capacity := capacity) (weight := weight)
      (backlogged := backlogged) hrate_intervalIntegrable_all
      (actualServiceStart n) (departure n)]
    exact hcompleted_work_eq_integral n

/--
Constructor for chronological source data whose actual service starts are the
comparator starts `max(arrival n, previous departure)`.
-/
def ofComparatorStartGlobalCumulativeService
    (hcapacity : 0 ≤ capacity)
    (hweight_nonneg : ∀ i, 0 ≤ weight i)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (htagged_guaranteed_rate_pos : 0 < capacity * weight tag)
    (hdeparture_after_comparatorStart : ∀ n,
      comparatorServiceStartFrom initialBusyUntil arrival departure n ≤
        departure n)
    (backlogged : ℝ → ι → Bool)
    (hrate_intervalIntegrable_all : ∀ a b : ℝ,
      IntervalIntegrable
        (gpsBackloggedClassRate ι tag capacity weight backlogged)
        MeasureTheory.volume a b)
    (htag_backlogged_on_open_actual_job : ∀ n t,
      t ∈ Set.Ioo
        (comparatorServiceStartFrom initialBusyUntil arrival departure n)
        (departure n) →
        backlogged t tag = true)
    (hcompleted_work_eq_integral : ∀ n,
      ∫ t in
        comparatorServiceStartFrom initialBusyUntil arrival departure n..
          departure n,
        gpsBackloggedClassRate ι tag capacity weight backlogged t =
          work n) :
    TaggedClassGPSOpenBacklogIntegralSourcePath ι tag initialBusyUntil
      arrival work departure capacity weight :=
  ofGlobalCumulativeService hcapacity hweight_nonneg htotal_weight_le_one
    htagged_guaranteed_rate_pos
    (comparatorServiceStartFrom initialBusyUntil arrival departure)
    (by
      intro n
      cases n <;> simp [comparatorServiceStartFrom])
    hdeparture_after_comparatorStart
    (by simp [comparatorServiceStartFrom])
    (by
      intro n
      simp [comparatorServiceStartFrom])
    backlogged hrate_intervalIntegrable_all
    htag_backlogged_on_open_actual_job hcompleted_work_eq_integral

/--
All-arrivals constructor for the chronological source-defined GPS departure
recurrence.  The source supplies measurable backlog indicators, nonnegative tagged
work, and the invariant that unfinished tagged-class work implies tagged
backlog on each guaranteed service window.
-/
def ofSourceGPSDepartureFromUnfinishedWindow
    (hcapacity : 0 ≤ capacity)
    (hweight_nonneg : ∀ i, 0 ≤ weight i)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (htagged_guaranteed_rate_pos : 0 < capacity * weight tag)
    (backlogged : ℝ → ι → Bool)
    (hbacklogged_meas : ∀ i, Measurable (fun t => backlogged t i))
    (hwork_nonneg : ∀ n, 0 ≤ work n)
    (hbacklogged_of_unfinished_on_guaranteed_window : ∀ n t,
      t ∈ Set.Ioo
        (comparatorServiceStartFrom initialBusyUntil arrival
          (gpsBackloggedDepartureFrom (ι := ι) (tag := tag)
            initialBusyUntil arrival work capacity weight backlogged) n)
        (comparatorServiceStartFrom initialBusyUntil arrival
          (gpsBackloggedDepartureFrom (ι := ι) (tag := tag)
            initialBusyUntil arrival work capacity weight backlogged) n +
          work n / (capacity * weight tag)) →
      (∫ u in
        comparatorServiceStartFrom initialBusyUntil arrival
          (gpsBackloggedDepartureFrom (ι := ι) (tag := tag)
            initialBusyUntil arrival work capacity weight backlogged) n..t,
        gpsBackloggedClassRate ι tag capacity weight backlogged u) <
        work n →
      backlogged t tag = true) :
    TaggedClassGPSOpenBacklogIntegralSourcePath ι tag initialBusyUntil
      arrival work
      (gpsBackloggedDepartureFrom (ι := ι) (tag := tag)
        initialBusyUntil arrival work capacity weight backlogged)
      capacity weight := by
  let dep : ℕ → ℝ :=
    gpsBackloggedDepartureFrom (ι := ι) (tag := tag)
      initialBusyUntil arrival work capacity weight backlogged
  let start : ℕ → ℝ :=
    comparatorServiceStartFrom initialBusyUntil arrival dep
  change TaggedClassGPSOpenBacklogIntegralSourcePath ι tag initialBusyUntil
    arrival work dep capacity weight
  have hrate_intervalIntegrable_all : ∀ a b : ℝ,
      IntervalIntegrable
        (gpsBackloggedClassRate ι tag capacity weight backlogged)
        MeasureTheory.volume a b :=
    gpsBackloggedClassRate_intervalIntegrable_all_of_backlogged_measurable
      tag capacity weight backlogged hbacklogged_meas
  have hreaches : ∀ n,
      work n ≤
        ∫ u in start n..(start n + work n / (capacity * weight tag)),
          gpsBackloggedClassRate ι tag capacity weight backlogged u := by
    intro n
    exact
      cumulativeService_reaches_at_guaranteedWindow_of_backlogged_if_unfinished
        (tag := tag) hcapacity hweight_nonneg htotal_weight_le_one
        htagged_guaranteed_rate_pos (hwork_nonneg n)
        (hrate_intervalIntegrable_all (start n)
          (start n + work n / (capacity * weight tag)))
        (by
          intro t ht hunfinished
          exact hbacklogged_of_unfinished_on_guaranteed_window n t
            (by simpa [start, dep] using ht)
            (by simpa [start, dep] using hunfinished))
  have hstart_completion : ∀ n,
      start n ≤ start n + work n / (capacity * weight tag) := by
    intro n
    have hdiv_nonneg :
        0 ≤ work n / (capacity * weight tag) :=
      div_nonneg (hwork_nonneg n) htagged_guaranteed_rate_pos.le
    linarith
  have hfirst : ∀ n,
      cumulativeServiceFirstHitAt (start n) (work n)
        (fun t =>
          ∫ u in start n..t,
            gpsBackloggedClassRate ι tag capacity weight backlogged u)
        (dep n) := by
    intro n
    cases n with
    | zero =>
        simpa [start, dep, comparatorServiceStartFrom] using
          (gpsBackloggedDepartureFrom_zero_firstHitAt_of_reaches
            (ι := ι) (tag := tag)
            (initialBusyUntil := initialBusyUntil)
            (arrival := arrival) (work := work)
            (capacity := capacity) (weight := weight)
            (backlogged := backlogged)
            (witness := start 0 + work 0 / (capacity * weight tag))
            (hstart_completion 0)
            (by simpa [start] using hreaches 0))
    | succ n =>
        simpa [start, dep, comparatorServiceStartFrom] using
          (gpsBackloggedDepartureFrom_succ_firstHitAt_of_reaches
            (ι := ι) (tag := tag)
            (initialBusyUntil := initialBusyUntil)
            (arrival := arrival) (work := work)
            (capacity := capacity) (weight := weight)
            (backlogged := backlogged) (n := n)
            (witness := start (n + 1) +
              work (n + 1) / (capacity * weight tag))
            (hstart_completion (n + 1))
            (by simpa [start, dep, comparatorServiceStartFrom] using
              hreaches (n + 1)))
  have hcontinuous : ∀ n,
      Continuous
        (fun t =>
          ∫ u in start n..t,
            gpsBackloggedClassRate ι tag capacity weight backlogged u) := by
    intro n
    exact intervalIntegral.continuous_primitive
      hrate_intervalIntegrable_all (start n)
  have hleast : ∀ n,
      IsLeast
        (cumulativeServiceHitSet (start n) (work n)
          (fun t =>
            ∫ u in start n..t,
              gpsBackloggedClassRate ι tag capacity weight backlogged u))
        (dep n) := by
    intro n
    exact cumulativeServiceFirstHitAt_isLeast_of_continuous
      (hcontinuous n) (hfirst n)
  have hcompletion_hit : ∀ n,
      start n + work n / (capacity * weight tag) ∈
        cumulativeServiceHitSet (start n) (work n)
          (fun t =>
            ∫ u in start n..t,
              gpsBackloggedClassRate ι tag capacity weight backlogged u) := by
    intro n
    exact ⟨hstart_completion n, hreaches n⟩
  refine ofComparatorStartGlobalCumulativeService
    (ι := ι) (tag := tag) hcapacity hweight_nonneg htotal_weight_le_one
    htagged_guaranteed_rate_pos ?_ backlogged hrate_intervalIntegrable_all
    ?_ ?_
  · intro n
    exact (hleast n).1.1
  · intro n t ht
    have hdep_le_completion :
        dep n ≤ start n + work n / (capacity * weight tag) :=
      (hleast n).2 (hcompletion_hit n)
    have ht_window : t ∈ Set.Ioo
        (start n) (start n + work n / (capacity * weight tag)) :=
      ⟨ht.1, lt_of_lt_of_le ht.2 hdep_le_completion⟩
    have hunfinished :
        (∫ u in start n..t,
          gpsBackloggedClassRate ι tag capacity weight backlogged u) <
          work n :=
      cumulativeService_lt_work_of_isLeast_hit (hleast n) ht
    exact hbacklogged_of_unfinished_on_guaranteed_window n t
      (by simpa [start, dep] using ht_window)
      (by simpa [start, dep] using hunfinished)
  · intro n
    by_cases hpos : 0 < work n
    · have hstart_below :
          (∫ u in start n..start n,
            gpsBackloggedClassRate ι tag capacity weight backlogged u) <
            work n := by
        simpa using hpos
      exact
        cumulativeService_eq_work_of_isLeast_hit_of_continuousAt
          (start := start n) (jobWork := work n)
          (departureTime := dep n)
          (cumulativeService := fun t =>
            ∫ u in start n..t,
              gpsBackloggedClassRate ι tag capacity weight backlogged u)
          (hleast n) hstart_below (hcontinuous n).continuousAt
    · have hwork_zero : work n = 0 :=
        le_antisymm (le_of_not_gt hpos) (hwork_nonneg n)
      have hstart_hit :
          start n ∈
            cumulativeServiceHitSet (start n) (work n)
              (fun t =>
                ∫ u in start n..t,
                  gpsBackloggedClassRate ι tag capacity weight backlogged u) := by
        refine ⟨le_rfl, ?_⟩
        simp [hwork_zero]
      have hdep_le_start : dep n ≤ start n := (hleast n).2 hstart_hit
      have hstart_le_dep : start n ≤ dep n := (hleast n).1.1
      have hdep_eq : dep n = start n :=
        le_antisymm hdep_le_start hstart_le_dep
      simpa [start, hdep_eq, hwork_zero]

/--
The backlog-integral source certificate instantiates the tagged-class
a.e.-normalized GPS path used by the pathwise comparison layer.
-/
def toTaggedClassAENormalizedGPSSourcePath
    (H : TaggedClassGPSOpenBacklogIntegralSourcePath ι tag initialBusyUntil
      arrival work departure capacity weight) :
    TaggedClassAENormalizedGPSSourcePath ι tag initialBusyUntil
      arrival work departure capacity weight where
  capacity_nonneg := H.capacity_nonneg
  weight_nonneg := H.weight_nonneg
  total_weight_le_one := H.total_weight_le_one
  tagged_guaranteed_rate_pos := H.tagged_guaranteed_rate_pos
  actualServiceStart := H.actualServiceStart
  arrival_le_actualServiceStart := H.arrival_le_actualServiceStart
  departure_after_actualServiceStart := H.departure_after_actualServiceStart
  actualStart_zero_le_comparatorStart := H.actualStart_zero_le_comparatorStart
  actualStart_succ_le_comparatorStart := H.actualStart_succ_le_comparatorStart
  activeClasses := gpsBackloggedClasses ι H.backlogged
  activeWeightSum := gpsBackloggedWeightSum ι weight H.backlogged
  instantaneousClassRate :=
    gpsBackloggedClassRate ι tag capacity weight H.backlogged
  service := H.service
  rate_intervalIntegrable := H.rate_intervalIntegrable
  ae_tag_active_on_actual_job := by
    intro n
    exact ae_restrict_Icc_of_forall_mem_Ioo fun t ht => by
      have hbacklogged := H.tag_backlogged_on_open_actual_job n t ht
      simp [gpsBackloggedClasses, hbacklogged]
  ae_activeWeightSum_eq_on_actual_job := by
    intro n
    filter_upwards with t
    rfl
  ae_gps_allocation_on_actual_job := by
    intro n
    filter_upwards with t
    rfl
  service_increment_eq_integral := H.service_increment_eq_integral
  completed_work_eq_service := H.completed_work_eq_service

/--
The same source certificate yields the coupled a.e.-normalized GPS path with
tagged guaranteed weight.
-/
def toCoupledAENormalizedIdealFluidGPSPath
    (H : TaggedClassGPSOpenBacklogIntegralSourcePath ι tag initialBusyUntil
      arrival work departure capacity weight) :
    CoupledAENormalizedIdealFluidGPSPath initialBusyUntil arrival work departure
      capacity (weight tag) :=
  H.toTaggedClassAENormalizedGPSSourcePath.toCoupledAENormalizedIdealFluidGPSPath

end TaggedClassGPSOpenBacklogIntegralSourcePath

end

end AppliedModelingLib.Probability.Queueing
