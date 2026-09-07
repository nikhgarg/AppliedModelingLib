import AppliedModelingLib.Foundations.Probability.PalmMarkedCampbell
import AppliedModelingLib.Queueing.MM1.PalmPASTA
import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalRenewalCountMarginal
import AppliedModelingLib.Foundations.Probability.PoissonFiniteHorizonMarkedThinning
import AppliedModelingLib.Queueing.MM1.ForwardReverse.MarkedSuspension
import AppliedModelingLib.Foundations.Probability.Processes.TimedEmbedded.MarkedPointSet
import AppliedModelingLib.Queueing.MM1.TwoSided.FullStationarity

/-!
# Direct marked Palm certificate for the forward/reverse M/M/1 carrier

This module turns a full unmarked integer-path stationarity theorem into a
stationary Palm certificate for the selected true-mark M/M/1 arrivals.  The
selected point process is represented by a covariant Boolean selector on the
all-event enumeration, so no independent survivor re-enumeration is assumed.
-/

namespace AppliedModelingLib.Probability.Queueing

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

noncomputable section

open PoissonProcess

def timedEmbeddedStateMarkZero : ((ℤ → ℝ) × (ℤ → (ℕ × Bool))) → Bool :=
  fun z => (z.2 0).2

theorem measurable_timedEmbeddedStateMarkZero :
    Measurable timedEmbeddedStateMarkZero :=
  measurable_snd.comp ((measurable_pi_apply 0).comp measurable_snd)

theorem timedEmbeddedStateMark_recenterAt_zero
    (z : GoodSuspensionState × (ℤ → (ℕ × Bool))) (i : ℤ) :
    (z.2 i).2 = timedEmbeddedStateMarkZero (timedEmbeddedRecenterAt z i) := by
  simp [timedEmbeddedStateMarkZero, timedEmbeddedRecenterAt, intPathShift]

def timedEmbeddedStateMarkTruePointSet
    (z : GoodSuspensionState × (ℤ → (ℕ × Bool))) : Set ℝ :=
  {u | ∃ i, (z.2 i).2 = true ∧ timedEmbeddedArrival z i = u}

theorem timedEmbeddedStateMarkTruePointSet_flow
    (z : GoodSuspensionState × (ℤ → (ℕ × Bool))) (t : ℝ) :
    timedEmbeddedStateMarkTruePointSet
      (timedEmbeddedSuspensionFlow (α := ℕ × Bool) t z) =
      (fun u : ℝ => u - t) '' timedEmbeddedStateMarkTruePointSet z := by
  exact timedEmbeddedSelectedPointSet_flow Prod.snd z t

theorem timedEmbeddedTaggedArrivalAtZero_stateMarkZero_hasLaw_of_pathZeroLaw
    {π : Measure ℕ} {B : Measure Bool}
    [IsProbabilityMeasure π] [IsProbabilityMeasure B]
    (P : Measure (ℤ → (ℕ × Bool))) [IsProbabilityMeasure P]
    (hzero : HasLaw (fun x : ℤ → (ℕ × Bool) => x 0) (π.prod B) P)
    {rate : ℝ} (hrate : 0 < rate) :
    HasLaw timedEmbeddedStateMarkZero B
      (timedEmbeddedTaggedArrivalAtZero rate hrate P).Ptag := by
  let coord : (ℤ → (ℕ × Bool)) → ℕ × Bool := fun x => x 0
  let mark : (ℤ → (ℕ × Bool)) → Bool := fun x => (x 0).2
  have hcoord : Measurable coord := measurable_pi_apply 0
  have hmark : Measurable mark := measurable_snd.comp hcoord
  have htag := timedEmbeddedTaggedArrivalAtZero_pathStatistic_hasLaw P
    mark hmark rate hrate
  refine ⟨measurable_timedEmbeddedStateMarkZero.aemeasurable, ?_⟩
  change Measure.map (fun z : (ℤ → ℝ) × (ℤ → (ℕ × Bool)) => mark z.2)
    (timedEmbeddedTaggedArrivalAtZero rate hrate P).Ptag = B
  calc
    Measure.map (fun z : (ℤ → ℝ) × (ℤ → (ℕ × Bool)) => mark z.2)
        (timedEmbeddedTaggedArrivalAtZero rate hrate P).Ptag =
        Measure.map mark P := htag.map_eq
    _ = Measure.map Prod.snd (Measure.map coord P) := by
        symm
        rw [Measure.map_map measurable_snd hcoord]
        rfl
    _ = Measure.map Prod.snd (π.prod B) := by
        rw [hzero.map_eq]
    _ = B := by
        rw [Measure.map_snd_prod, measure_univ, one_smul]

theorem timedEmbeddedTaggedArrivalAtZero_stateMarkZero_true_mass_of_pathZeroLaw
    {π : Measure ℕ} {B : Measure Bool}
    [IsProbabilityMeasure π] [IsProbabilityMeasure B]
    (P : Measure (ℤ → (ℕ × Bool))) [IsProbabilityMeasure P]
    (hzero : HasLaw (fun x : ℤ → (ℕ × Bool) => x 0) (π.prod B) P)
    {rate : ℝ} (hrate : 0 < rate) :
    (timedEmbeddedTaggedArrivalAtZero rate hrate P).Ptag
      (timedEmbeddedStateMarkZero ⁻¹' ({true} : Set Bool)) = B {true} := by
  have hmark := timedEmbeddedTaggedArrivalAtZero_stateMarkZero_hasLaw_of_pathZeroLaw
    (π := π) (B := B) P hzero hrate
  rw [← Measure.map_apply_of_aemeasurable hmark.aemeasurable
    (MeasurableSet.singleton true), hmark.map_eq]

theorem geoNNPMF_uniformized_forwardReverseMarkedTagged_true_mass
    {rate : ℝ} (hrate : 0 < rate) (rho : ℝ≥0) (hrho : rho < 1) :
    (geoNNPMF_uniformized_forwardReverseMarkedTaggedArrivalAtZero
      hrate rho hrho).Ptag
      (timedEmbeddedStateMarkZero ⁻¹' ({true} : Set Bool)) =
      (uniformizationArrivalMark (uniformizedBirthProbability rho)
        (uniformizedBirthProbability_le_one rho)).toMeasure {true} := by
  let π : Measure ℕ := (geoNNPMF rho hrho).toMeasure
  let B : Measure Bool :=
    (uniformizationArrivalMark (uniformizedBirthProbability rho)
      (uniformizedBirthProbability_le_one rho)).toMeasure
  let P : Measure (ℤ → (ℕ × Bool)) :=
    geoNNPMF_uniformized_forwardReverseMarkedTrajMeasure rho hrho
  letI : IsProbabilityMeasure π := by
    dsimp [π]
    infer_instance
  letI : IsProbabilityMeasure B := by
    dsimp [B]
    infer_instance
  letI : IsProbabilityMeasure P :=
    isProbabilityMeasure_geoNNPMF_uniformized_forwardReverseMarkedTrajMeasure rho hrho
  have hzero : HasLaw (fun x : ℤ → (ℕ × Bool) => x 0) (π.prod B) P := by
    simpa [π, B, P] using
      (geoNNPMF_uniformized_forwardReverseMarkedTraj_zero_coordinate_hasLaw rho hrho)
  change (timedEmbeddedTaggedArrivalAtZero rate hrate P).Ptag
      (timedEmbeddedStateMarkZero ⁻¹' ({true} : Set Bool)) = B {true}
  exact timedEmbeddedTaggedArrivalAtZero_stateMarkZero_true_mass_of_pathZeroLaw
    (π := π) (B := B) P hzero hrate

theorem geoNNPMF_uniformized_forwardReverseMarkedTagged_true_mass_ofReal
    {rate : ℝ} (hrate : 0 < rate) (rho : ℝ≥0) (hrho : rho < 1) :
    (geoNNPMF_uniformized_forwardReverseMarkedTaggedArrivalAtZero
      hrate rho hrho).Ptag
      (timedEmbeddedStateMarkZero ⁻¹' ({true} : Set Bool)) =
      ENNReal.ofReal (uniformizedBirthProbability rho : ℝ) := by
  rw [geoNNPMF_uniformized_forwardReverseMarkedTagged_true_mass
    hrate rho hrho]
  exact uniformizationArrivalMark_true_mass_ofReal
    (uniformizedBirthProbability rho)
    (uniformizedBirthProbability_le_one rho)

theorem geoNNPMF_uniformized_forwardReverseMarkedTagged_true_mass_ne_zero
    {rate : ℝ} (hrate : 0 < rate) (rho : ℝ≥0) (hrho : rho < 1)
    (hrho_pos : 0 < rho) :
    (geoNNPMF_uniformized_forwardReverseMarkedTaggedArrivalAtZero
      hrate rho hrho).Ptag
      (timedEmbeddedStateMarkZero ⁻¹' ({true} : Set Bool)) ≠ 0 := by
  rw [geoNNPMF_uniformized_forwardReverseMarkedTagged_true_mass
    hrate rho hrho]
  exact uniformizationArrivalMark_true_mass_ne_zero_of_rho_pos hrho_pos

noncomputable def
    geoNNPMF_uniformized_forwardReverseMarkedCampbellCertificate_of_unmarkedIntPathShift
    {rate : ℝ} (hrate : 0 < rate) (rho : ℝ≥0) (hrho : rho < 1)
    (hrho_pos : 0 < rho)
    (hpath : ∀ k : ℤ,
      MeasurePreserving (intPathShift k)
        (geoNNPMF_uniformized_forwardReverseTrajMeasure rho hrho)
        (geoNNPMF_uniformized_forwardReverseTrajMeasure rho hrho)) :
    Palm.MarkedCampbellPalmTaggedArrivalCertificate
      (geoNNPMF_uniformized_forwardReverseMarkedSuspensionShiftInvariantLaw_of_unmarkedIntPathShift
        hrate rho hrho hpath)
      ((geoNNPMF_uniformized_forwardReverseMarkedTaggedArrivalAtZero
        hrate rho hrho).conditionOn
          (timedEmbeddedStateMarkZero ⁻¹' ({true} : Set Bool))
          (geoNNPMF_uniformized_forwardReverseMarkedTagged_true_mass_ne_zero
            hrate rho hrho hrho_pos)) := by
  let H :=
    geoNNPMF_uniformized_forwardReverseMarkedSuspensionCampbellCertificate_of_unmarkedIntPathShift
      hrate rho hrho hpath
  let markAt : (GoodSuspensionState × (ℤ → (ℕ × Bool))) → ℤ → Bool :=
    fun z i => (z.2 i).2
  let p : ℝ := (uniformizedBirthProbability rho : ℝ)
  have hmark : ∀ z i, markAt z i =
      timedEmbeddedStateMarkZero (H.recenterAt z i) := by
    intro z i
    change (z.2 i).2 = timedEmbeddedStateMarkZero (timedEmbeddedRecenterAt z i)
    exact timedEmbeddedStateMark_recenterAt_zero z i
  have hpointShift : ∀ t, ∀ᵐ z ∂
      (geoNNPMF_uniformized_forwardReverseMarkedSuspensionShiftInvariantLaw_of_unmarkedIntPathShift
        hrate rho hrho hpath).Pbase,
      Palm.trueMarkedPointSet H.baseArrivals markAt
          ((geoNNPMF_uniformized_forwardReverseMarkedSuspensionShiftInvariantLaw_of_unmarkedIntPathShift
            hrate rho hrho hpath).shift t z) =
        (fun u : ℝ => u - t) '' Palm.trueMarkedPointSet H.baseArrivals markAt z := by
    intro t
    filter_upwards [] with z
    change timedEmbeddedStateMarkTruePointSet
        (timedEmbeddedSuspensionFlow (α := ℕ × Bool) t z) =
      (fun u : ℝ => u - t) '' timedEmbeddedStateMarkTruePointSet z
    exact timedEmbeddedStateMarkTruePointSet_flow z t
  have hmass :
      (geoNNPMF_uniformized_forwardReverseMarkedTaggedArrivalAtZero
        hrate rho hrho).Ptag
        (timedEmbeddedStateMarkZero ⁻¹' ({true} : Set Bool)) =
        ENNReal.ofReal p := by
    simpa [p] using
      (geoNNPMF_uniformized_forwardReverseMarkedTagged_true_mass_ofReal
        hrate rho hrho)
  have htrue :
      (geoNNPMF_uniformized_forwardReverseMarkedTaggedArrivalAtZero
        hrate rho hrho).Ptag
        (timedEmbeddedStateMarkZero ⁻¹' ({true} : Set Bool)) ≠ 0 :=
    geoNNPMF_uniformized_forwardReverseMarkedTagged_true_mass_ne_zero
      hrate rho hrho hrho_pos
  have hp : 0 < p := by
    dsimp [p]
    exact_mod_cast uniformizedBirthProbability_pos hrho_pos
  have hselectedRate : 0 < H.arrivalRate * p := by
    change 0 < rate * p
    exact mul_pos hrate hp
  exact Palm.markedCampbellCertificate_conditionOnTrue H
    timedEmbeddedStateMarkZero measurable_timedEmbeddedStateMarkZero markAt hmark
    hpointShift p hmass htrue hselectedRate

theorem
    geoNNPMF_uniformized_forwardReverseMarkedCampbellCertificate_of_unmarkedIntPathShift_arrivalRate
    {rate : ℝ} (hrate : 0 < rate) (rho : ℝ≥0) (hrho : rho < 1)
    (hrho_pos : 0 < rho)
    (hpath : ∀ k : ℤ,
      MeasurePreserving (intPathShift k)
        (geoNNPMF_uniformized_forwardReverseTrajMeasure rho hrho)
        (geoNNPMF_uniformized_forwardReverseTrajMeasure rho hrho)) :
    (geoNNPMF_uniformized_forwardReverseMarkedCampbellCertificate_of_unmarkedIntPathShift
      hrate rho hrho hrho_pos hpath).arrivalRate =
      rate * (uniformizedBirthProbability rho : ℝ) := by
  rfl

/-- Detailed balance upgrades the forward/reverse M/M/1 construction to a
full integer-shift-invariant two-sided path law. -/
theorem geoNNPMF_uniformized_forwardReverseTraj_intPathShift_measurePreserving
    (rho : ℝ≥0) (hrho : rho < 1) (k : ℤ) :
    MeasurePreserving (intPathShift k)
      (geoNNPMF_uniformized_forwardReverseTrajMeasure rho hrho)
      (geoNNPMF_uniformized_forwardReverseTrajMeasure rho hrho) := by
  exact Kernel.ReversePairBalance.forwardReverseTwoSidedTrajMeasure_intPathShift_measurePreserving
    (geoNNPMF_uniformized_forwardReverse_reversePairBalance rho hrho)
    (geoNNPMF_uniformized_kernelInvariant rho hrho) k

/-- The concrete forward/reverse M/M/1 suspension therefore has a genuine
stationary Palm certificate for its selected true-mark arrivals. -/
noncomputable def geoNNPMF_uniformized_forwardReverseMarkedCampbellCertificate
    {rate : ℝ} (hrate : 0 < rate) (rho : ℝ≥0) (hrho : rho < 1)
    (hrho_pos : 0 < rho) :
    Palm.MarkedCampbellPalmTaggedArrivalCertificate
      (geoNNPMF_uniformized_forwardReverseMarkedSuspensionShiftInvariantLaw_of_unmarkedIntPathShift
        hrate rho hrho
        (fun k => geoNNPMF_uniformized_forwardReverseTraj_intPathShift_measurePreserving
          rho hrho k))
      ((geoNNPMF_uniformized_forwardReverseMarkedTaggedArrivalAtZero
        hrate rho hrho).conditionOn
          (timedEmbeddedStateMarkZero ⁻¹' ({true} : Set Bool))
          (geoNNPMF_uniformized_forwardReverseMarkedTagged_true_mass_ne_zero
            hrate rho hrho hrho_pos)) :=
  geoNNPMF_uniformized_forwardReverseMarkedCampbellCertificate_of_unmarkedIntPathShift
    hrate rho hrho hrho_pos
    (fun k => geoNNPMF_uniformized_forwardReverseTraj_intPathShift_measurePreserving
      rho hrho k)

/-- Its selected-event intensity is the uniformization rate times the true
arrival-mark probability. -/
theorem geoNNPMF_uniformized_forwardReverseMarkedCampbellCertificate_arrivalRate
    {rate : ℝ} (hrate : 0 < rate) (rho : ℝ≥0) (hrho : rho < 1)
    (hrho_pos : 0 < rho) :
    (geoNNPMF_uniformized_forwardReverseMarkedCampbellCertificate
      hrate rho hrho hrho_pos).arrivalRate =
      rate * (uniformizedBirthProbability rho : ℝ) := by
  exact
    geoNNPMF_uniformized_forwardReverseMarkedCampbellCertificate_of_unmarkedIntPathShift_arrivalRate
      hrate rho hrho hrho_pos
      (fun k => geoNNPMF_uniformized_forwardReverseTraj_intPathShift_measurePreserving
        rho hrho k)

/-- At the M/M/1 uniformization clock, the selected marked Palm intensity is
the physical arrival rate. -/
theorem geoNNPMF_uniformized_forwardReverseMarkedCampbellCertificate_physicalArrivalRate
    {arrivalRate serviceRate : ℝ≥0}
    (harrival_pos : 0 < arrivalRate) (hstable : arrivalRate < serviceRate) :
    (geoNNPMF_uniformized_forwardReverseMarkedCampbellCertificate
      (rate := ((arrivalRate + serviceRate : ℝ≥0) : ℝ))
      (by
        exact_mod_cast
          (add_pos_of_pos_of_nonneg harrival_pos (zero_le serviceRate)))
      (mm1TrafficIntensityNN arrivalRate serviceRate)
      (mm1TrafficIntensityNN_lt_one hstable)
      (mm1TrafficIntensityNN_pos harrival_pos
        (lt_trans harrival_pos hstable))).arrivalRate =
      (arrivalRate : ℝ) := by
  rw [geoNNPMF_uniformized_forwardReverseMarkedCampbellCertificate_arrivalRate]
  exact total_uniformized_rate_mul_birthProbability_real
    (lt_trans harrival_pos hstable)

/-! ## Finite embedded post-tag mark blocks -/

private def twoArrivalMarks : ((ℕ × ℕ) × ℕ) → Bool × Bool :=
  fun z => (isArrivalEdge z.1.1 z.1.2, isArrivalEdge z.1.2 z.2)

private theorem measurable_twoArrivalMarks : Measurable twoArrivalMarks :=
  measurable_of_countable _

private theorem twoArrivalMarks_productLaw
    (π : Measure ℕ) [IsProbabilityMeasure π]
    (p : ℝ≥0) (hp : p ≤ 1) :
    Measure.map twoArrivalMarks
      ((π ⊗ₘ countablePMFKernel (reflectedBirthDeathKernel p hp)) ⊗ₘ
        (countablePMFKernel (reflectedBirthDeathKernel p hp)).prodMkLeft ℕ) =
      (uniformizationArrivalMark p hp).toMeasure.prod
        (uniformizationArrivalMark p hp).toMeasure := by
  let B : Measure Bool := (uniformizationArrivalMark p hp).toMeasure
  let K : Kernel ℕ ℕ := countablePMFKernel (reflectedBirthDeathKernel p hp)
  let μ : Measure (ℕ × ℕ) := π ⊗ₘ K
  let L : Kernel (ℕ × ℕ) ℕ := K.prodMkLeft ℕ
  let mark : ℕ × ℕ → Bool := fun z => isArrivalEdge z.1 z.2
  have hmark_measurable : Measurable mark := measurable_of_countable _
  have hmap_mark : Measure.map mark μ = B := by
    calc
      Measure.map mark μ = Measure.map Prod.snd (Measure.map markedEdgeProjection μ) := by
        symm
        rw [Measure.map_map measurable_snd measurable_markedEdgeProjection]
        rfl
      _ = Measure.map Prod.snd (π.prod B) := by
        rw [map_markedEdgeProjection_compProd_reflectedBirthDeathKernel]
      _ = B := by
        rw [Measure.map_snd_prod, measure_univ, one_smul]
  apply Measure.ext_of_singleton
  rintro ⟨a, b⟩
  let Ea : Set (ℕ × ℕ) := {z | mark z = a}
  have hEa : MeasurableSet Ea :=
    (measurableSet_singleton a).preimage hmark_measurable
  have hμEa : μ Ea = B {a} := by
    calc
      μ Ea = Measure.map mark μ {a} := by
        rw [Measure.map_apply hmark_measurable (measurableSet_singleton a)]
        rfl
      _ = B {a} := by rw [hmap_mark]
  have hlocal (q : ℕ) :
      K q (isArrivalEdge q ⁻¹' ({b} : Set Bool)) = B {b} := by
    have h := congrArg (fun ν : Measure Bool => ν {b})
      (map_isArrivalEdge_reflectedBirthDeathKernel p hp q)
    change Measure.map (isArrivalEdge q)
      (reflectedBirthDeathKernel p hp q).toMeasure {b} = B {b} at h
    rw [Measure.map_apply (measurable_of_countable _)
      (measurableSet_singleton b)] at h
    simpa [K, B] using h
  have hfiber (z : ℕ × ℕ) :
      L z (Prod.mk z ⁻¹' (twoArrivalMarks ⁻¹' ({(a, b)} : Set (Bool × Bool)))) =
        Ea.indicator (fun _ => B {b}) z := by
    by_cases hz : mark z = a
    · have hz' : isArrivalEdge z.1 z.2 = a := hz
      change K z.2
        (Prod.mk z ⁻¹' (twoArrivalMarks ⁻¹' ({(a, b)} : Set (Bool × Bool)))) = _
      rw [show Prod.mk z ⁻¹' (twoArrivalMarks ⁻¹' ({(a, b)} : Set (Bool × Bool))) =
          isArrivalEdge z.2 ⁻¹' ({b} : Set Bool) by
            ext q
            simp [twoArrivalMarks, hz']]
      rw [hlocal]
      simp [Ea, hz]
    · have hz' : isArrivalEdge z.1 z.2 ≠ a := hz
      change K z.2
        (Prod.mk z ⁻¹' (twoArrivalMarks ⁻¹' ({(a, b)} : Set (Bool × Bool)))) = _
      rw [show Prod.mk z ⁻¹' (twoArrivalMarks ⁻¹' ({(a, b)} : Set (Bool × Bool))) =
          ∅ by
            ext q
            simp [twoArrivalMarks, hz']]
      simp [Ea, hz]
  have hpre : MeasurableSet (twoArrivalMarks ⁻¹' ({(a, b)} : Set (Bool × Bool))) :=
    (measurableSet_singleton _).preimage measurable_twoArrivalMarks
  change Measure.map twoArrivalMarks (μ ⊗ₘ L) {(a, b)} = B.prod B {(a, b)}
  rw [Measure.map_apply measurable_twoArrivalMarks (measurableSet_singleton _),
    Measure.compProd_apply hpre]
  calc
    (∫⁻ z, L z (Prod.mk z ⁻¹' (twoArrivalMarks ⁻¹' ({(a, b)} : Set (Bool × Bool)))) ∂μ) =
        ∫⁻ z, Ea.indicator (fun _ => B {b}) z ∂μ := by
          apply lintegral_congr_ae
          filter_upwards [] with z
          exact hfiber z
    _ = B {b} * μ Ea := by
      exact MeasureTheory.lintegral_indicator_const hEa (B {b})
    _ = B {a} * B {b} := by rw [hμEa, mul_comm]
    _ = B.prod B {(a, b)} := by
      rw [← Set.singleton_prod_singleton, Measure.prod_prod]

private def threeArrivalMarks : (((ℕ × ℕ) × ℕ) × ℕ) → Bool × (Bool × Bool) :=
  fun z => (isArrivalEdge z.1.1.1 z.1.1.2,
    (isArrivalEdge z.1.1.2 z.1.2, isArrivalEdge z.1.2 z.2))

private theorem measurable_threeArrivalMarks : Measurable threeArrivalMarks :=
  measurable_of_countable _

private theorem threeArrivalMarks_productLaw
    (π : Measure ℕ) [IsProbabilityMeasure π]
    (p : ℝ≥0) (hp : p ≤ 1) :
    Measure.map threeArrivalMarks
      (((π ⊗ₘ countablePMFKernel (reflectedBirthDeathKernel p hp)) ⊗ₘ
        (countablePMFKernel (reflectedBirthDeathKernel p hp)).prodMkLeft ℕ) ⊗ₘ
        (countablePMFKernel (reflectedBirthDeathKernel p hp)).prodMkLeft (ℕ × ℕ)) =
      (uniformizationArrivalMark p hp).toMeasure.prod
        ((uniformizationArrivalMark p hp).toMeasure.prod
          (uniformizationArrivalMark p hp).toMeasure) := by
  let B : Measure Bool := (uniformizationArrivalMark p hp).toMeasure
  let K : Kernel ℕ ℕ := countablePMFKernel (reflectedBirthDeathKernel p hp)
  let ν : Measure ((ℕ × ℕ) × ℕ) := (π ⊗ₘ K) ⊗ₘ K.prodMkLeft ℕ
  let L : Kernel ((ℕ × ℕ) × ℕ) ℕ := K.prodMkLeft (ℕ × ℕ)
  let prior : ((ℕ × ℕ) × ℕ) → Bool × Bool := twoArrivalMarks
  have hprior : Measure.map prior ν = B.prod B := by
    simpa [ν, prior, K, B] using twoArrivalMarks_productLaw π p hp
  apply Measure.ext_of_singleton
  rintro ⟨a, b, c⟩
  let Eab : Set ((ℕ × ℕ) × ℕ) := {z | prior z = (a, b)}
  have hEab : MeasurableSet Eab :=
    (measurableSet_singleton _).preimage measurable_twoArrivalMarks
  have hνEab : ν Eab = (B.prod B) {(a, b)} := by
    calc
      ν Eab = Measure.map prior ν {(a, b)} := by
        rw [Measure.map_apply measurable_twoArrivalMarks (measurableSet_singleton _)]
        rfl
      _ = (B.prod B) {(a, b)} := by rw [hprior]
  have hlocal (q : ℕ) :
      K q (isArrivalEdge q ⁻¹' ({c} : Set Bool)) = B {c} := by
    have h := congrArg (fun μ : Measure Bool => μ {c})
      (map_isArrivalEdge_reflectedBirthDeathKernel p hp q)
    change Measure.map (isArrivalEdge q)
      (reflectedBirthDeathKernel p hp q).toMeasure {c} = B {c} at h
    rw [Measure.map_apply (measurable_of_countable _)
      (measurableSet_singleton c)] at h
    simpa [K, B] using h
  have hfiber (z : (ℕ × ℕ) × ℕ) :
      L z (Prod.mk z ⁻¹' (threeArrivalMarks ⁻¹'
        ({(a, (b, c))} : Set (Bool × (Bool × Bool))))) =
        Eab.indicator (fun _ => B {c}) z := by
    by_cases hz : prior z = (a, b)
    · rcases z with ⟨⟨q₀, q₁⟩, q₂⟩
      change prior ((q₀, q₁), q₂) = (a, b) at hz
      have hpair : (isArrivalEdge q₀ q₁, isArrivalEdge q₁ q₂) = (a, b) := by
        simpa [prior, twoArrivalMarks] using hz
      have h₀₁ : isArrivalEdge q₀ q₁ = a := congrArg Prod.fst hpair
      have h₁₂ : isArrivalEdge q₁ q₂ = b := congrArg Prod.snd hpair
      change K q₂
        (Prod.mk ((q₀, q₁), q₂) ⁻¹' (threeArrivalMarks ⁻¹'
          ({(a, (b, c))} : Set (Bool × (Bool × Bool))))) = _
      rw [show Prod.mk ((q₀, q₁), q₂) ⁻¹'
          (threeArrivalMarks ⁻¹' ({(a, (b, c))} : Set (Bool × (Bool × Bool)))) =
          isArrivalEdge q₂ ⁻¹' ({c} : Set Bool) by
            ext q₃
            simp [threeArrivalMarks, h₀₁, h₁₂]]
      rw [hlocal]
      simp [Eab, hz]
    · rcases z with ⟨⟨q₀, q₁⟩, q₂⟩
      change prior ((q₀, q₁), q₂) ≠ (a, b) at hz
      have hpairne : (isArrivalEdge q₀ q₁, isArrivalEdge q₁ q₂) ≠ (a, b) := by
        simpa [prior, twoArrivalMarks] using hz
      have hnot : ¬ (isArrivalEdge q₀ q₁ = a ∧ isArrivalEdge q₁ q₂ = b) := by
        intro h
        apply hpairne
        exact Prod.ext h.1 h.2
      change K q₂
        (Prod.mk ((q₀, q₁), q₂) ⁻¹' (threeArrivalMarks ⁻¹'
          ({(a, (b, c))} : Set (Bool × (Bool × Bool))))) = _
      rw [show Prod.mk ((q₀, q₁), q₂) ⁻¹'
          (threeArrivalMarks ⁻¹' ({(a, (b, c))} : Set (Bool × (Bool × Bool)))) =
          ∅ by
            ext q₃
            simp [threeArrivalMarks]
            exact fun h₀₁ h₁₂ _ => hnot ⟨h₀₁, h₁₂⟩]
      simp [Eab, hz]
  have hpre : MeasurableSet (threeArrivalMarks ⁻¹'
      ({(a, (b, c))} : Set (Bool × (Bool × Bool)))) :=
    (measurableSet_singleton _).preimage measurable_threeArrivalMarks
  change Measure.map threeArrivalMarks (ν ⊗ₘ L) {(a, (b, c))} =
    B.prod (B.prod B) {(a, (b, c))}
  rw [Measure.map_apply measurable_threeArrivalMarks (measurableSet_singleton _),
    Measure.compProd_apply hpre]
  calc
    (∫⁻ z, L z (Prod.mk z ⁻¹' (threeArrivalMarks ⁻¹'
      ({(a, (b, c))} : Set (Bool × (Bool × Bool))))) ∂ν) =
        ∫⁻ z, Eab.indicator (fun _ => B {c}) z ∂ν := by
          apply lintegral_congr_ae
          filter_upwards [] with z
          exact hfiber z
    _ = B {c} * ν Eab := by
      exact MeasureTheory.lintegral_indicator_const hEab (B {c})
    _ = B {c} * (B.prod B) {(a, b)} := by rw [hνEab]
    _ = B.prod (B.prod B) {(a, (b, c))} := by
      have hab : (B.prod B) {(a, b)} = B {b} * B {a} := by
        rw [← Set.singleton_prod_singleton, Measure.prod_prod, mul_comm]
      have hbc : (B.prod B) {(b, c)} = B {c} * B {b} := by
        rw [← Set.singleton_prod_singleton, Measure.prod_prod, mul_comm]
      have hout : B.prod (B.prod B) {(a, (b, c))} =
          (B.prod B) {(b, c)} * B {a} := by
        rw [← Set.singleton_prod_singleton, Measure.prod_prod, mul_comm]
      rw [hab, hout, hbc]
      ac_rfl

private theorem cond_snd_hasLaw_of_pair_product
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {m : Ω → Bool × Bool} (hm : Measurable m)
    {B : Measure Bool} [IsProbabilityMeasure B]
    (H : HasLaw m (B.prod B) P) (htrue : B {true} ≠ 0) :
    HasLaw (fun ω => (m ω).2) B (P[| {ω | (m ω).1 = true}]) := by
  let E : Set Ω := {ω | (m ω).1 = true}
  let A : Bool → Set Ω := fun b => {ω | (m ω).2 = b}
  have hE : MeasurableSet E :=
    (measurableSet_singleton true).preimage (measurable_fst.comp hm)
  have hPE : P E = B {true} := by
    calc
      P E = Measure.map m P (({true} : Set Bool) ×ˢ Set.univ) := by
        rw [Measure.map_apply hm ((measurableSet_singleton _).prod MeasurableSet.univ)]
        congr 1
        ext ω
        simp [E]
      _ = (B.prod B) (({true} : Set Bool) ×ˢ Set.univ) := by rw [H.map_eq]
      _ = B {true} := by rw [Measure.prod_prod, measure_univ, mul_one]
  have hPEA (b : Bool) : P (E ∩ A b) = B {true} * B {b} := by
    calc
      P (E ∩ A b) = Measure.map m P (({true} : Set Bool) ×ˢ ({b} : Set Bool)) := by
        rw [Measure.map_apply hm ((measurableSet_singleton _).prod
          (measurableSet_singleton _))]
        rw [show E ∩ A b =
            m ⁻¹' (({true} : Set Bool) ×ˢ ({b} : Set Bool)) by
          ext ω
          rcases hω : m ω with ⟨u, v⟩
          simp [E, A, hω]]
      _ = (B.prod B) (({true} : Set Bool) ×ˢ ({b} : Set Bool)) := by rw [H.map_eq]
      _ = B {true} * B {b} := by rw [Measure.prod_prod, mul_comm]
  refine ⟨(measurable_snd.comp hm).aemeasurable, ?_⟩
  change Measure.map (fun ω => (m ω).2) (P[| E]) = B
  apply Measure.ext_of_singleton
  intro b
  have hmap :
      Measure.map (fun ω => (m ω).2) (P[| E]) {b} =
        (P[| E]) ((fun ω => (m ω).2) ⁻¹' ({b} : Set Bool)) :=
    Measure.map_apply (f := fun ω => (m ω).2)
      (measurable_snd.comp hm) (measurableSet_singleton _)
  rw [hmap]
  change P[A b | E] = B {b}
  rw [cond_apply hE P (A b), hPE, hPEA, ← mul_assoc,
    ENNReal.inv_mul_cancel htrue (measure_ne_top B {true}), one_mul]

private theorem cond_futurePair_hasLaw_of_three_product
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {m : Ω → Bool × (Bool × Bool)} (hm : Measurable m)
    {B : Measure Bool} [IsProbabilityMeasure B]
    (H : HasLaw m (B.prod (B.prod B)) P) (htrue : B {true} ≠ 0) :
    HasLaw (fun ω => (m ω).2) (B.prod B)
      (P[| {ω | (m ω).1 = true}]) := by
  let E : Set Ω := {ω | (m ω).1 = true}
  let A : (Bool × Bool) → Set Ω := fun y => {ω | (m ω).2 = y}
  have hE : MeasurableSet E :=
    (measurableSet_singleton true).preimage (measurable_fst.comp hm)
  have hPE : P E = B {true} := by
    calc
      P E = Measure.map m P (({true} : Set Bool) ×ˢ Set.univ) := by
        rw [Measure.map_apply hm ((measurableSet_singleton _).prod MeasurableSet.univ)]
        congr 1
        ext ω
        simp [E]
      _ = (B.prod (B.prod B)) (({true} : Set Bool) ×ˢ Set.univ) := by rw [H.map_eq]
      _ = B {true} := by rw [Measure.prod_prod, measure_univ, mul_one]
  have hPEA (y : Bool × Bool) : P (E ∩ A y) = B {true} * (B.prod B) {y} := by
    calc
      P (E ∩ A y) = Measure.map m P (({true} : Set Bool) ×ˢ ({y} : Set (Bool × Bool))) := by
        rw [Measure.map_apply hm ((measurableSet_singleton _).prod
          (measurableSet_singleton _))]
        rw [show E ∩ A y = m ⁻¹'
            (({true} : Set Bool) ×ˢ ({y} : Set (Bool × Bool))) by
          ext ω
          rcases hω : m ω with ⟨u, v⟩
          simp [E, A, hω]]
      _ = (B.prod (B.prod B)) (({true} : Set Bool) ×ˢ ({y} : Set (Bool × Bool))) := by
        rw [H.map_eq]
      _ = B {true} * (B.prod B) {y} := by rw [Measure.prod_prod, mul_comm]
  refine ⟨(measurable_snd.comp hm).aemeasurable, ?_⟩
  change Measure.map (fun ω => (m ω).2) (P[| E]) = B.prod B
  apply Measure.ext_of_singleton
  intro y
  have hmap :
      Measure.map (fun ω => (m ω).2) (P[| E]) {y} =
        (P[| E]) ((fun ω => (m ω).2) ⁻¹' ({y} : Set (Bool × Bool))) :=
    Measure.map_apply (f := fun ω => (m ω).2)
      (measurable_snd.comp hm) (measurableSet_singleton _)
  rw [hmap]
  change P[A y | E] = (B.prod B) {y}
  rw [cond_apply hE P (A y), hPE, hPEA, ← mul_assoc,
    ENNReal.inv_mul_cancel htrue (measure_ne_top B {true}), one_mul]

/-- The first two embedded event marks of the forward/reverse M/M/1 carrier
have the exact Bernoulli product law.  This is a two-coordinate finite-window
result, not a claim of an infinite iid mark tail. -/
theorem geoNNPMF_uniformized_forwardReverseMarkedTraj_marks_zero_one_hasLaw
    (rho : ℝ≥0) (hrho : rho < 1) :
    HasLaw (fun x : ℤ → (ℕ × Bool) => ((x 0).2, (x 1).2))
      ((uniformizationArrivalMark (uniformizedBirthProbability rho)
        (uniformizedBirthProbability_le_one rho)).toMeasure.prod
        (uniformizationArrivalMark (uniformizedBirthProbability rho)
          (uniformizedBirthProbability_le_one rho)).toMeasure)
      (geoNNPMF_uniformized_forwardReverseMarkedTrajMeasure rho hrho) := by
  let π : Measure ℕ := (geoNNPMF rho hrho).toMeasure
  let p : ℝ≥0 := uniformizedBirthProbability rho
  let hp : p ≤ 1 := uniformizedBirthProbability_le_one rho
  let K : Kernel ℕ ℕ := countablePMFKernel (reflectedBirthDeathKernel p hp)
  let M : Measure (ℤ → ℕ) := geoNNPMF_uniformized_forwardReverseTrajMeasure rho hrho
  have htriple : M.map (fun x => ((x 0, x (1 : ℤ)), x (2 : ℤ))) =
      (π ⊗ₘ K) ⊗ₘ K.prodMkLeft ℕ := by
    simpa [π, p, hp, K, M] using
      (forwardReverseTwoSidedTrajMeasure_zeroOneTwoTriple
        (π := (geoNNPMF rho hrho).toMeasure)
        (K := countablePMFKernel
          (reflectedBirthDeathKernel (uniformizedBirthProbability rho)
            (uniformizedBirthProbability_le_one rho)))
        (Kr := countablePMFKernel
          (reflectedBirthDeathKernel (uniformizedBirthProbability rho)
            (uniformizedBirthProbability_le_one rho))))
  have hedge : Measurable edgeMarkedPath := measurable_edgeMarkedPath
  have hmarks : Measurable (fun x : ℤ → (ℕ × Bool) => ((x 0).2, (x 1).2)) :=
    ((measurable_snd.comp (measurable_pi_apply 0)).prodMk
      (measurable_snd.comp (measurable_pi_apply 1)))
  have htripleMap : Measurable (fun x : ℤ → ℕ => ((x 0, x (1 : ℤ)), x (2 : ℤ))) :=
    (((measurable_pi_apply 0).prodMk (measurable_pi_apply (1 : ℤ))).prodMk
      (measurable_pi_apply (2 : ℤ)))
  refine ⟨hmarks.aemeasurable, ?_⟩
  change Measure.map (fun x : ℤ → (ℕ × Bool) => ((x 0).2, (x 1).2))
      (M.map edgeMarkedPath) = _
  calc
    Measure.map (fun x : ℤ → (ℕ × Bool) => ((x 0).2, (x 1).2))
        (M.map edgeMarkedPath) =
        Measure.map (fun x : ℤ → ℕ =>
          (isArrivalEdge (x 0) (x (1 : ℤ)),
            isArrivalEdge (x (1 : ℤ)) (x (2 : ℤ)))) M := by
          rw [Measure.map_map hmarks hedge]
          rfl
    _ = Measure.map twoArrivalMarks
        (Measure.map (fun x : ℤ → ℕ => ((x 0, x (1 : ℤ)), x (2 : ℤ))) M) := by
          symm
          rw [Measure.map_map measurable_twoArrivalMarks htripleMap]
          rfl
    _ = Measure.map twoArrivalMarks ((π ⊗ₘ K) ⊗ₘ K.prodMkLeft ℕ) := by rw [htriple]
    _ = _ := by
      simpa [p, hp] using twoArrivalMarks_productLaw π p hp

private theorem geoNNPMF_uniformized_forwardReverseMarkedTraj_marks_zero_one_two_hasLaw
    (rho : ℝ≥0) (hrho : rho < 1) :
    HasLaw (fun x : ℤ → (ℕ × Bool) => ((x 0).2, ((x 1).2, (x 2).2)))
      ((uniformizationArrivalMark (uniformizedBirthProbability rho)
        (uniformizedBirthProbability_le_one rho)).toMeasure.prod
        ((uniformizationArrivalMark (uniformizedBirthProbability rho)
          (uniformizedBirthProbability_le_one rho)).toMeasure.prod
          (uniformizationArrivalMark (uniformizedBirthProbability rho)
            (uniformizedBirthProbability_le_one rho)).toMeasure))
      (geoNNPMF_uniformized_forwardReverseMarkedTrajMeasure rho hrho) := by
  let π : Measure ℕ := (geoNNPMF rho hrho).toMeasure
  let p : ℝ≥0 := uniformizedBirthProbability rho
  let hp : p ≤ 1 := uniformizedBirthProbability_le_one rho
  let K : Kernel ℕ ℕ := countablePMFKernel (reflectedBirthDeathKernel p hp)
  let M : Measure (ℤ → ℕ) := geoNNPMF_uniformized_forwardReverseTrajMeasure rho hrho
  let ν : Measure ((ℕ × ℕ) × ℕ) := (π ⊗ₘ K) ⊗ₘ K.prodMkLeft ℕ
  have htriple : M.map (fun x => ((x 0, x (1 : ℤ)), x (2 : ℤ))) = ν := by
    simpa [π, p, hp, K, M, ν] using
      (forwardReverseTwoSidedTrajMeasure_zeroOneTwoTriple
        (π := (geoNNPMF rho hrho).toMeasure)
        (K := countablePMFKernel
          (reflectedBirthDeathKernel (uniformizedBirthProbability rho)
            (uniformizedBirthProbability_le_one rho)))
        (Kr := countablePMFKernel
          (reflectedBirthDeathKernel (uniformizedBirthProbability rho)
            (uniformizedBirthProbability_le_one rho))))
  have hquad : M.map (fun x => (((x 0, x (1 : ℤ)), x (2 : ℤ)), x (3 : ℤ))) =
      ν ⊗ₘ K.prodMkLeft (ℕ × ℕ) := by
    calc
      M.map (fun x => (((x 0, x (1 : ℤ)), x (2 : ℤ)), x (3 : ℤ))) =
          M.map (fun x => ((x 0, x (1 : ℤ)), x (2 : ℤ))) ⊗ₘ K.prodMkLeft (ℕ × ℕ) := by
            simpa [π, p, hp, K, M] using
              (forwardReverseTwoSidedTrajMeasure_zeroOneTwoThree_factor
                (π := (geoNNPMF rho hrho).toMeasure)
                (K := countablePMFKernel
                  (reflectedBirthDeathKernel (uniformizedBirthProbability rho)
                    (uniformizedBirthProbability_le_one rho)))
                (Kr := countablePMFKernel
                  (reflectedBirthDeathKernel (uniformizedBirthProbability rho)
                    (uniformizedBirthProbability_le_one rho))))
      _ = ν ⊗ₘ K.prodMkLeft (ℕ × ℕ) := by rw [htriple]
  have hedge : Measurable edgeMarkedPath := measurable_edgeMarkedPath
  have hmarks : Measurable
      (fun x : ℤ → (ℕ × Bool) => ((x 0).2, ((x 1).2, (x 2).2))) :=
    (measurable_snd.comp (measurable_pi_apply 0)).prodMk
      ((measurable_snd.comp (measurable_pi_apply 1)).prodMk
        (measurable_snd.comp (measurable_pi_apply 2)))
  have hquadMap : Measurable
      (fun x : ℤ → ℕ => (((x 0, x (1 : ℤ)), x (2 : ℤ)), x (3 : ℤ))) :=
    (((measurable_pi_apply 0).prodMk (measurable_pi_apply (1 : ℤ))).prodMk
      (measurable_pi_apply (2 : ℤ))).prodMk (measurable_pi_apply (3 : ℤ))
  refine ⟨hmarks.aemeasurable, ?_⟩
  change Measure.map (fun x : ℤ → (ℕ × Bool) => ((x 0).2, ((x 1).2, (x 2).2)))
      (M.map edgeMarkedPath) = _
  calc
    Measure.map (fun x : ℤ → (ℕ × Bool) => ((x 0).2, ((x 1).2, (x 2).2)))
        (M.map edgeMarkedPath) =
        Measure.map (fun x : ℤ → ℕ =>
          (isArrivalEdge (x 0) (x (1 : ℤ)),
            (isArrivalEdge (x (1 : ℤ)) (x (2 : ℤ)),
              isArrivalEdge (x (2 : ℤ)) (x (3 : ℤ))))) M := by
          rw [Measure.map_map hmarks hedge]
          rfl
    _ = Measure.map threeArrivalMarks
        (Measure.map (fun x : ℤ → ℕ => (((x 0, x (1 : ℤ)), x (2 : ℤ)), x (3 : ℤ))) M) := by
          symm
          rw [Measure.map_map measurable_threeArrivalMarks hquadMap]
          rfl
    _ = Measure.map threeArrivalMarks (ν ⊗ₘ K.prodMkLeft (ℕ × ℕ)) := by rw [hquad]
    _ = _ := by
      simpa [ν, p, hp, K] using threeArrivalMarks_productLaw π p hp

/-- Under the selected tagged-arrival law used by the direct marked-Palm
certificate, the immediately following embedded event mark has the original
Bernoulli law.  This is a one-step finite-horizon statement; it does not claim
an infinite iid post-arrival mark tail. -/
theorem geoNNPMF_uniformized_forwardReverseMarkedSelectedTag_nextMark_hasLaw
    {rate : ℝ} (hrate : 0 < rate) (rho : ℝ≥0) (hrho : rho < 1)
    (hrho_pos : 0 < rho) :
    HasLaw (fun z : (ℤ → ℝ) × (ℤ → (ℕ × Bool)) => (z.2 1).2)
      (uniformizationArrivalMark (uniformizedBirthProbability rho)
        (uniformizedBirthProbability_le_one rho)).toMeasure
      ((geoNNPMF_uniformized_forwardReverseMarkedTaggedArrivalAtZero
        hrate rho hrho).conditionOn
          (timedEmbeddedStateMarkZero ⁻¹' ({true} : Set Bool))
          (geoNNPMF_uniformized_forwardReverseMarkedTagged_true_mass_ne_zero
            hrate rho hrho hrho_pos)).Ptag := by
  let P : Measure (ℤ → (ℕ × Bool)) :=
    geoNNPMF_uniformized_forwardReverseMarkedTrajMeasure rho hrho
  let B : Measure Bool :=
    (uniformizationArrivalMark (uniformizedBirthProbability rho)
      (uniformizedBirthProbability_le_one rho)).toMeasure
  let T := geoNNPMF_uniformized_forwardReverseMarkedTaggedArrivalAtZero
    hrate rho hrho
  let m : ((ℤ → ℝ) × (ℤ → (ℕ × Bool))) → Bool × Bool :=
    fun z => ((z.2 0).2, (z.2 1).2)
  letI : IsProbabilityMeasure P := by
    dsimp [P]
    exact isProbabilityMeasure_geoNNPMF_uniformized_forwardReverseMarkedTrajMeasure rho hrho
  letI : IsProbabilityMeasure B := by
    dsimp [B]
    infer_instance
  letI : IsProbabilityMeasure T.Ptag := by
    dsimp [T]
    exact (geoNNPMF_uniformized_forwardReverseMarkedTaggedArrivalAtZero
      hrate rho hrho).isProbability
  have hpathPair : HasLaw (fun x : ℤ → (ℕ × Bool) => ((x 0).2, (x 1).2))
      (B.prod B) P := by
    simpa [P, B] using
      (geoNNPMF_uniformized_forwardReverseMarkedTraj_marks_zero_one_hasLaw rho hrho)
  have htagRaw := timedEmbeddedTaggedArrivalAtZero_pathStatistic_hasLaw P
    (fun x : ℤ → (ℕ × Bool) => ((x 0).2, (x 1).2))
    ((measurable_snd.comp (measurable_pi_apply 0)).prodMk
      (measurable_snd.comp (measurable_pi_apply 1))) rate hrate
  have htagPair : HasLaw m (B.prod B) T.Ptag := by
    refine ⟨((measurable_snd.comp ((measurable_pi_apply 0).comp measurable_snd)).prodMk
      (measurable_snd.comp ((measurable_pi_apply 1).comp measurable_snd))).aemeasurable, ?_⟩
    change Measure.map m T.Ptag = B.prod B
    calc
      Measure.map m T.Ptag = Measure.map
          (fun x : ℤ → (ℕ × Bool) => ((x 0).2, (x 1).2)) P := by
            exact htagRaw.map_eq
      _ = B.prod B := hpathPair.map_eq
  have hm : Measurable m :=
    (measurable_snd.comp ((measurable_pi_apply 0).comp measurable_snd)).prodMk
      (measurable_snd.comp ((measurable_pi_apply 1).comp measurable_snd))
  have htrue : B {true} ≠ 0 := by
    dsimp [B]
    exact uniformizationArrivalMark_true_mass_ne_zero_of_rho_pos hrho_pos
  have hcond := cond_snd_hasLaw_of_pair_product hm htagPair htrue
  change HasLaw (fun z : (ℤ → ℝ) × (ℤ → (ℕ × Bool)) => (m z).2) B
    (T.conditionOn (timedEmbeddedStateMarkZero ⁻¹' ({true} : Set Bool))
      (geoNNPMF_uniformized_forwardReverseMarkedTagged_true_mass_ne_zero
        hrate rho hrho hrho_pos)).Ptag
  rw [TaggedArrivalAtZero.conditionOn_Ptag]
  simpa [m, timedEmbeddedStateMarkZero] using hcond

/-- On the actual selected true-arrival Palm tag, the gap to the next
all-event epoch and that next event's Boolean mark have the exponential times
Bernoulli product law.  This combines the direct conditional tagged law with
the finite one-step edge-mark calculation; it is not a full marked-thinning
or infinite iid-tail theorem. -/
theorem geoNNPMF_uniformized_forwardReverseMarkedSelectedTag_firstGap_nextMark_hasLaw
    {rate : ℝ} (hrate : 0 < rate) (rho : ℝ≥0) (hrho : rho < 1)
    (hrho_pos : 0 < rho) :
    HasLaw
      (fun z : (ℤ → ℝ) × (ℤ → (ℕ × Bool)) =>
        (twoSidedGap 0 z.1, (z.2 1).2))
      ((ProbabilityTheory.expMeasure rate).prod
        (uniformizationArrivalMark (uniformizedBirthProbability rho)
          (uniformizedBirthProbability_le_one rho)).toMeasure)
      ((geoNNPMF_uniformized_forwardReverseMarkedTaggedArrivalAtZero
        hrate rho hrho).conditionOn
          (timedEmbeddedStateMarkZero ⁻¹' ({true} : Set Bool))
          (geoNNPMF_uniformized_forwardReverseMarkedTagged_true_mass_ne_zero
            hrate rho hrho hrho_pos)).Ptag := by
  let P : Measure (ℤ → (ℕ × Bool)) :=
    geoNNPMF_uniformized_forwardReverseMarkedTrajMeasure rho hrho
  let B : Measure Bool :=
    (uniformizationArrivalMark (uniformizedBirthProbability rho)
      (uniformizedBirthProbability_le_one rho)).toMeasure
  let A : Set (ℤ → (ℕ × Bool)) := timedEmbeddedPathZeroTrueSet Prod.snd
  letI : IsProbabilityMeasure P := by
    dsimp [P]
    exact isProbabilityMeasure_geoNNPMF_uniformized_forwardReverseMarkedTrajMeasure
      rho hrho
  letI : IsProbabilityMeasure B := by
    dsimp [B]
    infer_instance
  have hfull : (timedEmbeddedTaggedArrivalAtZero rate hrate P).Ptag
      ((timedEmbeddedTaggedPathZeroMark Prod.snd) ⁻¹' ({true} : Set Bool)) ≠ 0 := by
    change (geoNNPMF_uniformized_forwardReverseMarkedTaggedArrivalAtZero
      hrate rho hrho).Ptag
      (timedEmbeddedStateMarkZero ⁻¹' ({true} : Set Bool)) ≠ 0
    exact geoNNPMF_uniformized_forwardReverseMarkedTagged_true_mass_ne_zero
      hrate rho hrho hrho_pos
  have htrue : P A ≠ 0 := by
    rw [measure_timedEmbeddedTaggedPathZeroMark_true hrate P Prod.snd] at hfull
    simpa [A] using hfull
  let Q : Measure (ℤ → (ℕ × Bool)) := P[| A]
  letI : IsProbabilityMeasure Q := by
    dsimp [Q, A]
    exact ProbabilityTheory.cond_isProbabilityMeasure htrue
  let mark : (ℤ → (ℕ × Bool)) → Bool := fun x => (x 1).2
  have hmark : Measurable mark :=
    measurable_snd.comp (measurable_pi_apply (1 : ℤ))
  have hconditioned :
      ((geoNNPMF_uniformized_forwardReverseMarkedTaggedArrivalAtZero
        hrate rho hrho).conditionOn
          (timedEmbeddedStateMarkZero ⁻¹' ({true} : Set Bool))
          (geoNNPMF_uniformized_forwardReverseMarkedTagged_true_mass_ne_zero
            hrate rho hrho hrho_pos)).Ptag =
      (timedEmbeddedTaggedArrivalAtZero_conditionedOnPathZeroTrue
        hrate P Prod.snd htrue).Ptag := by
    simpa [P, A] using
      (timedEmbeddedTaggedArrivalAtZero_conditionOnPathZeroTrue_Ptag
        hrate P Prod.snd htrue hfull)
  have hgeneric :=
    timedEmbeddedTaggedArrivalAtZero_conditionedOnPathZeroTrue_firstGap_pathStatistic_hasLaw
      hrate P Prod.snd htrue mark hmark
  have hnext := geoNNPMF_uniformized_forwardReverseMarkedSelectedTag_nextMark_hasLaw
    hrate rho hrho hrho_pos
  have hnext' : HasLaw (fun z : (ℤ → ℝ) × (ℤ → (ℕ × Bool)) => mark z.2) B
      (timedEmbeddedTaggedArrivalAtZero_conditionedOnPathZeroTrue
        hrate P Prod.snd htrue).Ptag := by
    rw [← hconditioned]
    simpa [mark, B] using hnext
  have hstat : HasLaw (fun z : (ℤ → ℝ) × (ℤ → (ℕ × Bool)) => mark z.2)
      (Q.map mark)
      (timedEmbeddedTaggedArrivalAtZero_conditionedOnPathZeroTrue
        hrate P Prod.snd htrue).Ptag := by
    simpa [timedEmbeddedTaggedArrivalAtZero_conditionedOnPathZeroTrue, Q, A] using
      (timedEmbeddedTaggedArrivalAtZero_pathStatistic_hasLaw Q mark hmark rate hrate)
  have hQmap : Q.map mark = B := hstat.map_eq.symm.trans hnext'.map_eq
  refine ⟨((measurable_twoSidedGap 0).comp measurable_fst |>.prodMk
    (hmark.comp measurable_snd)).aemeasurable, ?_⟩
  change Measure.map (fun z : (ℤ → ℝ) × (ℤ → (ℕ × Bool)) =>
      (twoSidedGap 0 z.1, mark z.2)) _ = (ProbabilityTheory.expMeasure rate).prod B
  calc
    Measure.map (fun z : (ℤ → ℝ) × (ℤ → (ℕ × Bool)) =>
        (twoSidedGap 0 z.1, mark z.2))
        ((geoNNPMF_uniformized_forwardReverseMarkedTaggedArrivalAtZero
          hrate rho hrho).conditionOn
            (timedEmbeddedStateMarkZero ⁻¹' ({true} : Set Bool))
            (geoNNPMF_uniformized_forwardReverseMarkedTagged_true_mass_ne_zero
              hrate rho hrho hrho_pos)).Ptag =
        Measure.map (fun z : (ℤ → ℝ) × (ℤ → (ℕ × Bool)) =>
          (twoSidedGap 0 z.1, mark z.2))
          (timedEmbeddedTaggedArrivalAtZero_conditionedOnPathZeroTrue
            hrate P Prod.snd htrue).Ptag := by rw [hconditioned]
    _ = (ProbabilityTheory.expMeasure rate).prod (Q.map mark) := hgeneric.map_eq
    _ = (ProbabilityTheory.expMeasure rate).prod B := by rw [hQmap]

/-- Lift any checked marginal of the actual selected direct Palm tag to a
product law with its complete future all-event Palm-gap path.  The result is
about the same selected tag on both sides; it does not replace its path factor
with a synthetic independent copy.

The theorem establishes only clock/path-factor independence.  Mark thinning,
post-tag service counts, and an infinite iid mark tail remain separate. -/
theorem geoNNPMF_uniformized_forwardReverseMarkedSelectedTag_futureGapPath_pathStatistic_hasLaw_of_hasLaw
    {rate : ℝ} (hrate : 0 < rate) (rho : ℝ≥0) (hrho : rho < 1)
    (hrho_pos : 0 < rho)
    {β : Type*} [MeasurableSpace β]
    (stat : (ℤ → (ℕ × Bool)) → β) (hstat : Measurable stat)
    (ν : Measure β)
    (hstatlaw : HasLaw
      (fun z : (ℤ → ℝ) × (ℤ → (ℕ × Bool)) => stat z.2) ν
      ((geoNNPMF_uniformized_forwardReverseMarkedTaggedArrivalAtZero
        hrate rho hrho).conditionOn
          (timedEmbeddedStateMarkZero ⁻¹' ({true} : Set Bool))
          (geoNNPMF_uniformized_forwardReverseMarkedTagged_true_mass_ne_zero
            hrate rho hrho hrho_pos)).Ptag) :
    HasLaw
      (fun z : (ℤ → ℝ) × (ℤ → (ℕ × Bool)) =>
        (candidateFutureGapPath z.1, stat z.2))
      ((exponentialInterarrivalMeasure rate).prod ν)
      ((geoNNPMF_uniformized_forwardReverseMarkedTaggedArrivalAtZero
        hrate rho hrho).conditionOn
          (timedEmbeddedStateMarkZero ⁻¹' ({true} : Set Bool))
          (geoNNPMF_uniformized_forwardReverseMarkedTagged_true_mass_ne_zero
            hrate rho hrho hrho_pos)).Ptag := by
  let P : Measure (ℤ → (ℕ × Bool)) :=
    geoNNPMF_uniformized_forwardReverseMarkedTrajMeasure rho hrho
  let A : Set (ℤ → (ℕ × Bool)) := timedEmbeddedPathZeroTrueSet Prod.snd
  letI : IsProbabilityMeasure P := by
    dsimp [P]
    exact isProbabilityMeasure_geoNNPMF_uniformized_forwardReverseMarkedTrajMeasure
      rho hrho
  have hfull : (timedEmbeddedTaggedArrivalAtZero rate hrate P).Ptag
      ((timedEmbeddedTaggedPathZeroMark Prod.snd) ⁻¹' ({true} : Set Bool)) ≠ 0 := by
    change (geoNNPMF_uniformized_forwardReverseMarkedTaggedArrivalAtZero
      hrate rho hrho).Ptag
      (timedEmbeddedStateMarkZero ⁻¹' ({true} : Set Bool)) ≠ 0
    exact geoNNPMF_uniformized_forwardReverseMarkedTagged_true_mass_ne_zero
      hrate rho hrho hrho_pos
  have htrue : P A ≠ 0 := by
    rw [measure_timedEmbeddedTaggedPathZeroMark_true hrate P Prod.snd] at hfull
    simpa [A] using hfull
  let Q : Measure (ℤ → (ℕ × Bool)) := P[| A]
  letI : IsProbabilityMeasure Q := by
    dsimp [Q, A]
    exact ProbabilityTheory.cond_isProbabilityMeasure htrue
  have hconditioned :
      ((geoNNPMF_uniformized_forwardReverseMarkedTaggedArrivalAtZero
        hrate rho hrho).conditionOn
          (timedEmbeddedStateMarkZero ⁻¹' ({true} : Set Bool))
          (geoNNPMF_uniformized_forwardReverseMarkedTagged_true_mass_ne_zero
            hrate rho hrho hrho_pos)).Ptag =
      (timedEmbeddedTaggedArrivalAtZero_conditionedOnPathZeroTrue
        hrate P Prod.snd htrue).Ptag := by
    simpa [P, A] using
      (timedEmbeddedTaggedArrivalAtZero_conditionOnPathZeroTrue_Ptag
        hrate P Prod.snd htrue hfull)
  have hgeneric :=
    timedEmbeddedTaggedArrivalAtZero_conditionedOnPathZeroTrue_futureGapPath_pathStatistic_hasLaw
      hrate P Prod.snd htrue stat hstat
  have hstatMap : HasLaw
      (fun z : (ℤ → ℝ) × (ℤ → (ℕ × Bool)) => stat z.2) (Q.map stat)
      (timedEmbeddedTaggedArrivalAtZero_conditionedOnPathZeroTrue
        hrate P Prod.snd htrue).Ptag := by
    simpa [timedEmbeddedTaggedArrivalAtZero_conditionedOnPathZeroTrue, Q, A] using
      (timedEmbeddedTaggedArrivalAtZero_pathStatistic_hasLaw Q stat hstat rate hrate)
  have hstatlaw' : HasLaw
      (fun z : (ℤ → ℝ) × (ℤ → (ℕ × Bool)) => stat z.2) ν
      (timedEmbeddedTaggedArrivalAtZero_conditionedOnPathZeroTrue
        hrate P Prod.snd htrue).Ptag := by
    rw [← hconditioned]
    exact hstatlaw
  have hQmap : Q.map stat = ν := hstatMap.map_eq.symm.trans hstatlaw'.map_eq
  have hfuture : Measurable candidateFutureGapPath :=
    measurable_pi_iff.2 fun n => measurable_twoSidedGap (Int.ofNat n)
  refine ⟨((hfuture.comp measurable_fst).prodMk
    (hstat.comp measurable_snd)).aemeasurable, ?_⟩
  change Measure.map (fun z : (ℤ → ℝ) × (ℤ → (ℕ × Bool)) =>
      (candidateFutureGapPath z.1, stat z.2)) _ =
    (exponentialInterarrivalMeasure rate).prod ν
  calc
    Measure.map (fun z : (ℤ → ℝ) × (ℤ → (ℕ × Bool)) =>
        (candidateFutureGapPath z.1, stat z.2))
        ((geoNNPMF_uniformized_forwardReverseMarkedTaggedArrivalAtZero
          hrate rho hrho).conditionOn
            (timedEmbeddedStateMarkZero ⁻¹' ({true} : Set Bool))
            (geoNNPMF_uniformized_forwardReverseMarkedTagged_true_mass_ne_zero
              hrate rho hrho hrho_pos)).Ptag =
        Measure.map (fun z : (ℤ → ℝ) × (ℤ → (ℕ × Bool)) =>
          (candidateFutureGapPath z.1, stat z.2))
          (timedEmbeddedTaggedArrivalAtZero_conditionedOnPathZeroTrue
            hrate P Prod.snd htrue).Ptag := by rw [hconditioned]
    _ = (exponentialInterarrivalMeasure rate).prod (Q.map stat) := hgeneric.map_eq
    _ = (exponentialInterarrivalMeasure rate).prod ν := by rw [hQmap]

/-- The full future all-event Palm-gap path is iid exponential and has the
product law with the immediately following actual edge mark under the direct
selected true-arrival tag.  This alone does not thin the all-event clock into
a service process. -/
theorem geoNNPMF_uniformized_forwardReverseMarkedSelectedTag_futureGapPath_nextMark_hasLaw
    {rate : ℝ} (hrate : 0 < rate) (rho : ℝ≥0) (hrho : rho < 1)
    (hrho_pos : 0 < rho) :
    HasLaw
      (fun z : (ℤ → ℝ) × (ℤ → (ℕ × Bool)) =>
        (candidateFutureGapPath z.1, (z.2 1).2))
      ((exponentialInterarrivalMeasure rate).prod
        (uniformizationArrivalMark (uniformizedBirthProbability rho)
          (uniformizedBirthProbability_le_one rho)).toMeasure)
      ((geoNNPMF_uniformized_forwardReverseMarkedTaggedArrivalAtZero
        hrate rho hrho).conditionOn
          (timedEmbeddedStateMarkZero ⁻¹' ({true} : Set Bool))
          (geoNNPMF_uniformized_forwardReverseMarkedTagged_true_mass_ne_zero
            hrate rho hrho hrho_pos)).Ptag := by
  let B : Measure Bool :=
    (uniformizationArrivalMark (uniformizedBirthProbability rho)
      (uniformizedBirthProbability_le_one rho)).toMeasure
  have hmark : Measurable (fun x : ℤ → (ℕ × Bool) => (x 1).2) :=
    measurable_snd.comp (measurable_pi_apply (1 : ℤ))
  have hnext := geoNNPMF_uniformized_forwardReverseMarkedSelectedTag_nextMark_hasLaw
    hrate rho hrho hrho_pos
  simpa [B] using
    (geoNNPMF_uniformized_forwardReverseMarkedSelectedTag_futureGapPath_pathStatistic_hasLaw_of_hasLaw
      hrate rho hrho hrho_pos (fun x : ℤ → (ℕ × Bool) => (x 1).2) hmark B hnext)

/-- Under the selected tagged-arrival law used by the direct marked-Palm
certificate, the first two post-arrival embedded event marks have the product
of their Bernoulli laws.  This is a finite two-step result, not an infinite
iid-tail assertion. -/
theorem geoNNPMF_uniformized_forwardReverseMarkedSelectedTag_nextTwoMarks_hasLaw
    {rate : ℝ} (hrate : 0 < rate) (rho : ℝ≥0) (hrho : rho < 1)
    (hrho_pos : 0 < rho) :
    HasLaw (fun z : (ℤ → ℝ) × (ℤ → (ℕ × Bool)) => ((z.2 1).2, (z.2 2).2))
      ((uniformizationArrivalMark (uniformizedBirthProbability rho)
        (uniformizedBirthProbability_le_one rho)).toMeasure.prod
        (uniformizationArrivalMark (uniformizedBirthProbability rho)
          (uniformizedBirthProbability_le_one rho)).toMeasure)
      ((geoNNPMF_uniformized_forwardReverseMarkedTaggedArrivalAtZero
        hrate rho hrho).conditionOn
          (timedEmbeddedStateMarkZero ⁻¹' ({true} : Set Bool))
          (geoNNPMF_uniformized_forwardReverseMarkedTagged_true_mass_ne_zero
            hrate rho hrho hrho_pos)).Ptag := by
  let P : Measure (ℤ → (ℕ × Bool)) :=
    geoNNPMF_uniformized_forwardReverseMarkedTrajMeasure rho hrho
  let B : Measure Bool :=
    (uniformizationArrivalMark (uniformizedBirthProbability rho)
      (uniformizedBirthProbability_le_one rho)).toMeasure
  let T := geoNNPMF_uniformized_forwardReverseMarkedTaggedArrivalAtZero
    hrate rho hrho
  let m : ((ℤ → ℝ) × (ℤ → (ℕ × Bool))) → Bool × (Bool × Bool) :=
    fun z => ((z.2 0).2, ((z.2 1).2, (z.2 2).2))
  letI : IsProbabilityMeasure P := by
    dsimp [P]
    exact isProbabilityMeasure_geoNNPMF_uniformized_forwardReverseMarkedTrajMeasure rho hrho
  letI : IsProbabilityMeasure B := by
    dsimp [B]
    infer_instance
  letI : IsProbabilityMeasure T.Ptag := by
    dsimp [T]
    exact (geoNNPMF_uniformized_forwardReverseMarkedTaggedArrivalAtZero
      hrate rho hrho).isProbability
  have hpathTriple : HasLaw
      (fun x : ℤ → (ℕ × Bool) => ((x 0).2, ((x 1).2, (x 2).2)))
      (B.prod (B.prod B)) P := by
    simpa [P, B] using
      (geoNNPMF_uniformized_forwardReverseMarkedTraj_marks_zero_one_two_hasLaw rho hrho)
  have htagRaw := timedEmbeddedTaggedArrivalAtZero_pathStatistic_hasLaw P
    (fun x : ℤ → (ℕ × Bool) => ((x 0).2, ((x 1).2, (x 2).2)))
    ((measurable_snd.comp (measurable_pi_apply 0)).prodMk
      ((measurable_snd.comp (measurable_pi_apply 1)).prodMk
        (measurable_snd.comp (measurable_pi_apply 2)))) rate hrate
  have htagTriple : HasLaw m (B.prod (B.prod B)) T.Ptag := by
    refine ⟨((measurable_snd.comp ((measurable_pi_apply 0).comp measurable_snd)).prodMk
      ((measurable_snd.comp ((measurable_pi_apply 1).comp measurable_snd)).prodMk
        (measurable_snd.comp ((measurable_pi_apply 2).comp measurable_snd)))).aemeasurable, ?_⟩
    change Measure.map m T.Ptag = B.prod (B.prod B)
    calc
      Measure.map m T.Ptag = Measure.map
          (fun x : ℤ → (ℕ × Bool) => ((x 0).2, ((x 1).2, (x 2).2))) P := by
            exact htagRaw.map_eq
      _ = B.prod (B.prod B) := hpathTriple.map_eq
  have hm : Measurable m :=
    (measurable_snd.comp ((measurable_pi_apply 0).comp measurable_snd)).prodMk
      ((measurable_snd.comp ((measurable_pi_apply 1).comp measurable_snd)).prodMk
        (measurable_snd.comp ((measurable_pi_apply 2).comp measurable_snd)))
  have htrue : B {true} ≠ 0 := by
    dsimp [B]
    exact uniformizationArrivalMark_true_mass_ne_zero_of_rho_pos hrho_pos
  have hcond := cond_futurePair_hasLaw_of_three_product hm htagTriple htrue
  change HasLaw (fun z : (ℤ → ℝ) × (ℤ → (ℕ × Bool)) => (m z).2) (B.prod B)
    (T.conditionOn (timedEmbeddedStateMarkZero ⁻¹' ({true} : Set Bool))
      (geoNNPMF_uniformized_forwardReverseMarkedTagged_true_mass_ne_zero
        hrate rho hrho hrho_pos)).Ptag
  rw [TaggedArrivalAtZero.conditionOn_Ptag]
  simpa [m, timedEmbeddedStateMarkZero] using hcond

private def stateMarkOneFuture : ((ℕ × ℕ) × ℕ) → (ℕ × Bool) × Bool :=
  fun z => ((z.1.1, isArrivalEdge z.1.2 z.2), isArrivalEdge z.1.1 z.1.2)

private theorem measurable_stateMarkOneFuture : Measurable stateMarkOneFuture :=
  measurable_of_countable _

private theorem stateMarkOneFuture_productLaw
    (π : Measure ℕ) [IsProbabilityMeasure π]
    (p : ℝ≥0) (hp : p ≤ 1) :
    Measure.map stateMarkOneFuture
      ((π ⊗ₘ countablePMFKernel (reflectedBirthDeathKernel p hp)) ⊗ₘ
        (countablePMFKernel (reflectedBirthDeathKernel p hp)).prodMkLeft ℕ) =
      (π.prod (uniformizationArrivalMark p hp).toMeasure).prod
        (uniformizationArrivalMark p hp).toMeasure := by
  let B : Measure Bool := (uniformizationArrivalMark p hp).toMeasure
  let K : Kernel ℕ ℕ := countablePMFKernel (reflectedBirthDeathKernel p hp)
  let μ : Measure (ℕ × ℕ) := π ⊗ₘ K
  let L : Kernel (ℕ × ℕ) ℕ := K.prodMkLeft ℕ
  let edgeMark : ℕ × ℕ → Bool := fun z => isArrivalEdge z.1 z.2
  have hedgeMark : Measurable edgeMark := measurable_of_countable _
  have hmap_edge : Measure.map markedEdgeProjection μ = π.prod B := by
    exact map_markedEdgeProjection_compProd_reflectedBirthDeathKernel π p hp
  apply Measure.ext_of_singleton
  rintro ⟨⟨q, nextMark⟩, currentMark⟩
  let E : Set (ℕ × ℕ) := {z | z.1 = q ∧ edgeMark z = currentMark}
  have hE : MeasurableSet E :=
    ((measurableSet_singleton q).preimage measurable_fst).inter
      ((measurableSet_singleton currentMark).preimage hedgeMark)
  have hμE : μ E = (π.prod B) {(q, currentMark)} := by
    calc
      μ E = Measure.map markedEdgeProjection μ {(q, currentMark)} := by
        rw [Measure.map_apply measurable_markedEdgeProjection (measurableSet_singleton _)]
        congr 1
        ext z
        simp [E, edgeMark, markedEdgeProjection]
      _ = (π.prod B) {(q, currentMark)} := by rw [hmap_edge]
  have hlocal (s : ℕ) :
      K s (isArrivalEdge s ⁻¹' ({nextMark} : Set Bool)) = B {nextMark} := by
    have h := congrArg (fun ν : Measure Bool => ν {nextMark})
      (map_isArrivalEdge_reflectedBirthDeathKernel p hp s)
    change Measure.map (isArrivalEdge s)
      (reflectedBirthDeathKernel p hp s).toMeasure {nextMark} = B {nextMark} at h
    rw [Measure.map_apply (measurable_of_countable _)
      (measurableSet_singleton nextMark)] at h
    simpa [K, B] using h
  have hfiber (z : ℕ × ℕ) :
      L z (Prod.mk z ⁻¹' (stateMarkOneFuture ⁻¹'
        ({((q, nextMark), currentMark)} : Set ((ℕ × Bool) × Bool)))) =
        E.indicator (fun _ => B {nextMark}) z := by
    by_cases hz : z ∈ E
    · rcases z with ⟨q₀, q₁⟩
      have hq : q₀ = q := hz.1
      have hm : isArrivalEdge q₀ q₁ = currentMark := hz.2
      have hm' : isArrivalEdge q q₁ = currentMark := by
        simpa [hq] using hm
      change K q₁
        (Prod.mk (q₀, q₁) ⁻¹' (stateMarkOneFuture ⁻¹'
          ({((q, nextMark), currentMark)} : Set ((ℕ × Bool) × Bool)))) = _
      rw [show Prod.mk (q₀, q₁) ⁻¹'
          (stateMarkOneFuture ⁻¹' ({((q, nextMark), currentMark)} :
            Set ((ℕ × Bool) × Bool))) =
          isArrivalEdge q₁ ⁻¹' ({nextMark} : Set Bool) by
            ext q₂
            simp [stateMarkOneFuture, hq, hm']]
      rw [hlocal]
      simp [hz]
    · rcases z with ⟨q₀, q₁⟩
      have hnot : ¬ (q₀ = q ∧ isArrivalEdge q₀ q₁ = currentMark) := by
        simpa [E, edgeMark] using hz
      change K q₁
        (Prod.mk (q₀, q₁) ⁻¹' (stateMarkOneFuture ⁻¹'
          ({((q, nextMark), currentMark)} : Set ((ℕ × Bool) × Bool)))) = _
      rw [show Prod.mk (q₀, q₁) ⁻¹'
          (stateMarkOneFuture ⁻¹' ({((q, nextMark), currentMark)} :
            Set ((ℕ × Bool) × Bool))) = ∅ by
            ext q₂
            simp [stateMarkOneFuture]
            exact fun hq _ hm => hnot ⟨hq, hm⟩]
      simp [hz]
  have hpre : MeasurableSet (stateMarkOneFuture ⁻¹'
      ({((q, nextMark), currentMark)} : Set ((ℕ × Bool) × Bool))) :=
    (measurableSet_singleton _).preimage measurable_stateMarkOneFuture
  change Measure.map stateMarkOneFuture (μ ⊗ₘ L) {((q, nextMark), currentMark)} =
    (π.prod B).prod B {((q, nextMark), currentMark)}
  rw [Measure.map_apply measurable_stateMarkOneFuture (measurableSet_singleton _),
    Measure.compProd_apply hpre]
  calc
    (∫⁻ z, L z (Prod.mk z ⁻¹' (stateMarkOneFuture ⁻¹'
      ({((q, nextMark), currentMark)} : Set ((ℕ × Bool) × Bool)))) ∂μ) =
        ∫⁻ z, E.indicator (fun _ => B {nextMark}) z ∂μ := by
          apply lintegral_congr_ae
          filter_upwards [] with z
          exact hfiber z
    _ = B {nextMark} * μ E := by
      exact MeasureTheory.lintegral_indicator_const hE (B {nextMark})
    _ = B {nextMark} * (π.prod B) {(q, currentMark)} := by rw [hμE]
    _ = (π.prod B).prod B {((q, nextMark), currentMark)} := by
      have hqmark : (π.prod B) {(q, currentMark)} = B {currentMark} * π {q} := by
        rw [← Set.singleton_prod_singleton, Measure.prod_prod, mul_comm]
      have hqnext : (π.prod B) {(q, nextMark)} = B {nextMark} * π {q} := by
        rw [← Set.singleton_prod_singleton, Measure.prod_prod, mul_comm]
      have hout : (π.prod B).prod B {((q, nextMark), currentMark)} =
          B {currentMark} * (π.prod B) {(q, nextMark)} := by
        rw [← Set.singleton_prod_singleton, Measure.prod_prod, mul_comm]
      calc
        B {nextMark} * (π.prod B) {(q, currentMark)} =
            B {nextMark} * (B {currentMark} * π {q}) := by rw [hqmark]
        _ = B {currentMark} * (B {nextMark} * π {q}) := by ac_rfl
        _ = B {currentMark} * (π.prod B) {(q, nextMark)} := by rw [hqnext]
        _ = (π.prod B).prod B {((q, nextMark), currentMark)} := hout.symm

private theorem geoNNPMF_uniformized_forwardReverseMarkedTraj_state_nextMark_currentMark_hasLaw
    (rho : ℝ≥0) (hrho : rho < 1) :
    HasLaw
      (fun x : ℤ → (ℕ × Bool) => (((x 0).1, (x 1).2), (x 0).2))
      (((geoNNPMF rho hrho).toMeasure.prod
        (uniformizationArrivalMark (uniformizedBirthProbability rho)
          (uniformizedBirthProbability_le_one rho)).toMeasure).prod
        (uniformizationArrivalMark (uniformizedBirthProbability rho)
          (uniformizedBirthProbability_le_one rho)).toMeasure)
      (geoNNPMF_uniformized_forwardReverseMarkedTrajMeasure rho hrho) := by
  let π : Measure ℕ := (geoNNPMF rho hrho).toMeasure
  let p : ℝ≥0 := uniformizedBirthProbability rho
  let hp : p ≤ 1 := uniformizedBirthProbability_le_one rho
  let K : Kernel ℕ ℕ := countablePMFKernel (reflectedBirthDeathKernel p hp)
  let M : Measure (ℤ → ℕ) := geoNNPMF_uniformized_forwardReverseTrajMeasure rho hrho
  have htriple : M.map (fun x => ((x 0, x (1 : ℤ)), x (2 : ℤ))) =
      (π ⊗ₘ K) ⊗ₘ K.prodMkLeft ℕ := by
    simpa [π, p, hp, K, M] using
      (forwardReverseTwoSidedTrajMeasure_zeroOneTwoTriple
        (π := (geoNNPMF rho hrho).toMeasure)
        (K := countablePMFKernel
          (reflectedBirthDeathKernel (uniformizedBirthProbability rho)
            (uniformizedBirthProbability_le_one rho)))
        (Kr := countablePMFKernel
          (reflectedBirthDeathKernel (uniformizedBirthProbability rho)
            (uniformizedBirthProbability_le_one rho))))
  have hedge : Measurable edgeMarkedPath := measurable_edgeMarkedPath
  have hstat : Measurable
      (fun x : ℤ → (ℕ × Bool) => (((x 0).1, (x 1).2), (x 0).2)) :=
    ((measurable_fst.comp (measurable_pi_apply 0)).prodMk
      (measurable_snd.comp (measurable_pi_apply 1))).prodMk
        (measurable_snd.comp (measurable_pi_apply 0))
  have htripleMap : Measurable (fun x : ℤ → ℕ => ((x 0, x (1 : ℤ)), x (2 : ℤ))) :=
    (((measurable_pi_apply 0).prodMk (measurable_pi_apply (1 : ℤ))).prodMk
      (measurable_pi_apply (2 : ℤ)))
  refine ⟨hstat.aemeasurable, ?_⟩
  change Measure.map (fun x : ℤ → (ℕ × Bool) => (((x 0).1, (x 1).2), (x 0).2))
      (M.map edgeMarkedPath) = _
  calc
    Measure.map (fun x : ℤ → (ℕ × Bool) => (((x 0).1, (x 1).2), (x 0).2))
        (M.map edgeMarkedPath) =
        Measure.map (fun x : ℤ → ℕ =>
          ((x 0, isArrivalEdge (x (1 : ℤ)) (x (2 : ℤ))),
            isArrivalEdge (x 0) (x (1 : ℤ)))) M := by
          rw [Measure.map_map hstat hedge]
          rfl
    _ = Measure.map stateMarkOneFuture
        (Measure.map (fun x : ℤ → ℕ => ((x 0, x (1 : ℤ)), x (2 : ℤ))) M) := by
          symm
          rw [Measure.map_map measurable_stateMarkOneFuture htripleMap]
          rfl
    _ = Measure.map stateMarkOneFuture ((π ⊗ₘ K) ⊗ₘ K.prodMkLeft ℕ) := by rw [htriple]
    _ = _ := by
      simpa [p, hp] using stateMarkOneFuture_productLaw π p hp

private theorem cond_stateNextMark_hasLaw_of_product
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {m : Ω → (ℕ × Bool) × Bool} (hm : Measurable m)
    {π : Measure ℕ} {B : Measure Bool}
    [IsProbabilityMeasure π] [IsProbabilityMeasure B]
    (H : HasLaw m ((π.prod B).prod B) P) (htrue : B {true} ≠ 0) :
    HasLaw (fun ω => (m ω).1) (π.prod B)
      (P[| {ω | (m ω).2 = true}]) := by
  let E : Set Ω := {ω | (m ω).2 = true}
  let A : (ℕ × Bool) → Set Ω := fun y => {ω | (m ω).1 = y}
  have hE : MeasurableSet E :=
    (measurableSet_singleton true).preimage (measurable_snd.comp hm)
  have hPE : P E = B {true} := by
    calc
      P E = Measure.map m P (Set.univ ×ˢ ({true} : Set Bool)) := by
        rw [Measure.map_apply hm (MeasurableSet.univ.prod (measurableSet_singleton _))]
        congr 1
        ext ω
        simp [E]
      _ = ((π.prod B).prod B) (Set.univ ×ˢ ({true} : Set Bool)) := by rw [H.map_eq]
      _ = B {true} := by rw [Measure.prod_prod, measure_univ, one_mul]
  have hPEA (y : ℕ × Bool) : P (E ∩ A y) = B {true} * (π.prod B) {y} := by
    calc
      P (E ∩ A y) = Measure.map m P (({y} : Set (ℕ × Bool)) ×ˢ ({true} : Set Bool)) := by
        rw [Measure.map_apply hm ((measurableSet_singleton _).prod
          (measurableSet_singleton _))]
        rw [show E ∩ A y = m ⁻¹'
            (({y} : Set (ℕ × Bool)) ×ˢ ({true} : Set Bool)) by
          ext ω
          rcases hω : m ω with ⟨u, v⟩
          simp [E, A, hω, and_comm]]
      _ = ((π.prod B).prod B) (({y} : Set (ℕ × Bool)) ×ˢ ({true} : Set Bool)) := by
        rw [H.map_eq]
      _ = B {true} * (π.prod B) {y} := by rw [Measure.prod_prod, mul_comm]
  refine ⟨(measurable_fst.comp hm).aemeasurable, ?_⟩
  change Measure.map (fun ω => (m ω).1) (P[| E]) = π.prod B
  apply Measure.ext_of_singleton
  intro y
  have hmap :
      Measure.map (fun ω => (m ω).1) (P[| E]) {y} =
        (P[| E]) ((fun ω => (m ω).1) ⁻¹' ({y} : Set (ℕ × Bool))) :=
    Measure.map_apply (f := fun ω => (m ω).1)
      (measurable_fst.comp hm) (measurableSet_singleton _)
  rw [hmap]
  change P[A y | E] = (π.prod B) {y}
  rw [cond_apply hE P (A y), hPE, hPEA, ← mul_assoc,
    ENNReal.inv_mul_cancel htrue (measure_ne_top B {true}), one_mul]

/-- Under the actual selected true-tag law, the embedded pre-arrival queue
length and the next embedded event mark have the product of the stationary
geometric and Bernoulli laws.  This is an exact one-step factorization, not a
claim about a full post-tag iid tail or a continuous-time service process. -/
theorem geoNNPMF_uniformized_forwardReverseMarkedSelectedTag_state_nextMark_hasLaw
    {rate : ℝ} (hrate : 0 < rate) (rho : ℝ≥0) (hrho : rho < 1)
    (hrho_pos : 0 < rho) :
    HasLaw
      (fun z : (ℤ → ℝ) × (ℤ → (ℕ × Bool)) => ((z.2 0).1, (z.2 1).2))
      ((geoNNPMF rho hrho).toMeasure.prod
        (uniformizationArrivalMark (uniformizedBirthProbability rho)
          (uniformizedBirthProbability_le_one rho)).toMeasure)
      ((geoNNPMF_uniformized_forwardReverseMarkedTaggedArrivalAtZero
        hrate rho hrho).conditionOn
          (timedEmbeddedStateMarkZero ⁻¹' ({true} : Set Bool))
          (geoNNPMF_uniformized_forwardReverseMarkedTagged_true_mass_ne_zero
            hrate rho hrho hrho_pos)).Ptag := by
  let π : Measure ℕ := (geoNNPMF rho hrho).toMeasure
  let B : Measure Bool :=
    (uniformizationArrivalMark (uniformizedBirthProbability rho)
      (uniformizedBirthProbability_le_one rho)).toMeasure
  let P : Measure (ℤ → (ℕ × Bool)) :=
    geoNNPMF_uniformized_forwardReverseMarkedTrajMeasure rho hrho
  let T := geoNNPMF_uniformized_forwardReverseMarkedTaggedArrivalAtZero
    hrate rho hrho
  let m : ((ℤ → ℝ) × (ℤ → (ℕ × Bool))) → (ℕ × Bool) × Bool :=
    fun z => (((z.2 0).1, (z.2 1).2), (z.2 0).2)
  letI : IsProbabilityMeasure π := by
    dsimp [π]
    infer_instance
  letI : IsProbabilityMeasure B := by
    dsimp [B]
    infer_instance
  letI : IsProbabilityMeasure P := by
    dsimp [P]
    exact isProbabilityMeasure_geoNNPMF_uniformized_forwardReverseMarkedTrajMeasure rho hrho
  letI : IsProbabilityMeasure T.Ptag := by
    dsimp [T]
    exact (geoNNPMF_uniformized_forwardReverseMarkedTaggedArrivalAtZero
      hrate rho hrho).isProbability
  have hpath : HasLaw
      (fun x : ℤ → (ℕ × Bool) => (((x 0).1, (x 1).2), (x 0).2))
      ((π.prod B).prod B) P := by
    simpa [π, B, P] using
      (geoNNPMF_uniformized_forwardReverseMarkedTraj_state_nextMark_currentMark_hasLaw
        rho hrho)
  have htagRaw := timedEmbeddedTaggedArrivalAtZero_pathStatistic_hasLaw P
    (fun x : ℤ → (ℕ × Bool) => (((x 0).1, (x 1).2), (x 0).2))
    (((measurable_fst.comp (measurable_pi_apply 0)).prodMk
      (measurable_snd.comp (measurable_pi_apply 1))).prodMk
        (measurable_snd.comp (measurable_pi_apply 0))) rate hrate
  have htag : HasLaw m ((π.prod B).prod B) T.Ptag := by
    refine ⟨(((measurable_fst.comp ((measurable_pi_apply 0).comp measurable_snd)).prodMk
      (measurable_snd.comp ((measurable_pi_apply 1).comp measurable_snd))).prodMk
        (measurable_snd.comp ((measurable_pi_apply 0).comp measurable_snd))).aemeasurable, ?_⟩
    change Measure.map m T.Ptag = (π.prod B).prod B
    calc
      Measure.map m T.Ptag = Measure.map
          (fun x : ℤ → (ℕ × Bool) => (((x 0).1, (x 1).2), (x 0).2)) P := by
            exact htagRaw.map_eq
      _ = (π.prod B).prod B := hpath.map_eq
  have hm : Measurable m :=
    ((measurable_fst.comp ((measurable_pi_apply 0).comp measurable_snd)).prodMk
      (measurable_snd.comp ((measurable_pi_apply 1).comp measurable_snd))).prodMk
        (measurable_snd.comp ((measurable_pi_apply 0).comp measurable_snd))
  have htrue : B {true} ≠ 0 := by
    dsimp [B]
    exact uniformizationArrivalMark_true_mass_ne_zero_of_rho_pos hrho_pos
  have hcond := cond_stateNextMark_hasLaw_of_product hm htag htrue
  change HasLaw (fun z : (ℤ → ℝ) × (ℤ → (ℕ × Bool)) => (m z).1) (π.prod B)
    (T.conditionOn (timedEmbeddedStateMarkZero ⁻¹' ({true} : Set Bool))
      (geoNNPMF_uniformized_forwardReverseMarkedTagged_true_mass_ne_zero
        hrate rho hrho hrho_pos)).Ptag
  rw [TaggedArrivalAtZero.conditionOn_Ptag]
  simpa [m, timedEmbeddedStateMarkZero] using hcond

private def stateMarkTwoFuture : (((ℕ × ℕ) × ℕ) × ℕ) → (ℕ × (Bool × Bool)) × Bool :=
  fun z => ((z.1.1.1,
    (isArrivalEdge z.1.1.2 z.1.2, isArrivalEdge z.1.2 z.2)),
    isArrivalEdge z.1.1.1 z.1.1.2)

private theorem measurable_stateMarkTwoFuture : Measurable stateMarkTwoFuture :=
  measurable_of_countable _

private theorem stateMarkTwoFuture_productLaw
    (π : Measure ℕ) [IsProbabilityMeasure π]
    (p : ℝ≥0) (hp : p ≤ 1) :
    Measure.map stateMarkTwoFuture
      (((π ⊗ₘ countablePMFKernel (reflectedBirthDeathKernel p hp)) ⊗ₘ
        (countablePMFKernel (reflectedBirthDeathKernel p hp)).prodMkLeft ℕ) ⊗ₘ
        (countablePMFKernel (reflectedBirthDeathKernel p hp)).prodMkLeft (ℕ × ℕ)) =
      (π.prod ((uniformizationArrivalMark p hp).toMeasure.prod
        (uniformizationArrivalMark p hp).toMeasure)).prod
        (uniformizationArrivalMark p hp).toMeasure := by
  let B : Measure Bool := (uniformizationArrivalMark p hp).toMeasure
  let K : Kernel ℕ ℕ := countablePMFKernel (reflectedBirthDeathKernel p hp)
  let ν : Measure ((ℕ × ℕ) × ℕ) := (π ⊗ₘ K) ⊗ₘ K.prodMkLeft ℕ
  let L : Kernel ((ℕ × ℕ) × ℕ) ℕ := K.prodMkLeft (ℕ × ℕ)
  let prior : ((ℕ × ℕ) × ℕ) → (ℕ × Bool) × Bool := stateMarkOneFuture
  have hprior : Measure.map prior ν = (π.prod B).prod B := by
    simpa [ν, prior, K, B] using stateMarkOneFuture_productLaw π p hp
  apply Measure.ext_of_singleton
  rintro ⟨⟨q, mark₁, mark₂⟩, mark₀⟩
  let E : Set ((ℕ × ℕ) × ℕ) := {z | prior z = ((q, mark₁), mark₀)}
  have hE : MeasurableSet E :=
    (measurableSet_singleton _).preimage measurable_stateMarkOneFuture
  have hνE : ν E = ((π.prod B).prod B) {((q, mark₁), mark₀)} := by
    calc
      ν E = Measure.map prior ν {((q, mark₁), mark₀)} := by
        rw [Measure.map_apply measurable_stateMarkOneFuture (measurableSet_singleton _)]
        rfl
      _ = ((π.prod B).prod B) {((q, mark₁), mark₀)} := by rw [hprior]
  have hlocal (s : ℕ) :
      K s (isArrivalEdge s ⁻¹' ({mark₂} : Set Bool)) = B {mark₂} := by
    have h := congrArg (fun μ : Measure Bool => μ {mark₂})
      (map_isArrivalEdge_reflectedBirthDeathKernel p hp s)
    change Measure.map (isArrivalEdge s)
      (reflectedBirthDeathKernel p hp s).toMeasure {mark₂} = B {mark₂} at h
    rw [Measure.map_apply (measurable_of_countable _)
      (measurableSet_singleton mark₂)] at h
    simpa [K, B] using h
  have hfiber (z : (ℕ × ℕ) × ℕ) :
      L z (Prod.mk z ⁻¹' (stateMarkTwoFuture ⁻¹'
        ({((q, (mark₁, mark₂)), mark₀)} : Set ((ℕ × (Bool × Bool)) × Bool)))) =
        E.indicator (fun _ => B {mark₂}) z := by
    by_cases hz : z ∈ E
    · rcases z with ⟨⟨q₀, q₁⟩, q₂⟩
      have hprior' : ((q₀, isArrivalEdge q₁ q₂), isArrivalEdge q₀ q₁) =
          ((q, mark₁), mark₀) := by
        simpa [E, prior, stateMarkOneFuture] using hz
      have hq : q₀ = q := congrArg (fun x => x.1.1) hprior'
      have hm₁ : isArrivalEdge q₁ q₂ = mark₁ := congrArg (fun x => x.1.2) hprior'
      have hm₀ : isArrivalEdge q₀ q₁ = mark₀ := congrArg Prod.snd hprior'
      have hm₀' : isArrivalEdge q q₁ = mark₀ := by
        simpa [hq] using hm₀
      change K q₂
        (Prod.mk ((q₀, q₁), q₂) ⁻¹' (stateMarkTwoFuture ⁻¹'
          ({((q, (mark₁, mark₂)), mark₀)} : Set ((ℕ × (Bool × Bool)) × Bool)))) = _
      rw [show Prod.mk ((q₀, q₁), q₂) ⁻¹'
          (stateMarkTwoFuture ⁻¹' ({((q, (mark₁, mark₂)), mark₀)} :
            Set ((ℕ × (Bool × Bool)) × Bool))) =
          isArrivalEdge q₂ ⁻¹' ({mark₂} : Set Bool) by
            ext q₃
            simp [stateMarkTwoFuture, hq, hm₁, hm₀']]
      rw [hlocal]
      simp [hz]
    · rcases z with ⟨⟨q₀, q₁⟩, q₂⟩
      have hnot : ¬ ((q₀, isArrivalEdge q₁ q₂), isArrivalEdge q₀ q₁) =
          ((q, mark₁), mark₀) := by
        simpa [E, prior, stateMarkOneFuture] using hz
      change K q₂
        (Prod.mk ((q₀, q₁), q₂) ⁻¹' (stateMarkTwoFuture ⁻¹'
          ({((q, (mark₁, mark₂)), mark₀)} : Set ((ℕ × (Bool × Bool)) × Bool)))) = _
      rw [show Prod.mk ((q₀, q₁), q₂) ⁻¹'
          (stateMarkTwoFuture ⁻¹' ({((q, (mark₁, mark₂)), mark₀)} :
            Set ((ℕ × (Bool × Bool)) × Bool))) = ∅ by
            ext q₃
            simp [stateMarkTwoFuture]
            intro hq hm₁ hm₂ hm₀
            apply hnot
            exact Prod.ext (Prod.ext hq hm₁) hm₀]
      simp [hz]
  have hpre : MeasurableSet (stateMarkTwoFuture ⁻¹'
      ({((q, (mark₁, mark₂)), mark₀)} : Set ((ℕ × (Bool × Bool)) × Bool))) :=
    (measurableSet_singleton _).preimage measurable_stateMarkTwoFuture
  change Measure.map stateMarkTwoFuture (ν ⊗ₘ L) {((q, (mark₁, mark₂)), mark₀)} =
    (π.prod (B.prod B)).prod B {((q, (mark₁, mark₂)), mark₀)}
  rw [Measure.map_apply measurable_stateMarkTwoFuture (measurableSet_singleton _),
    Measure.compProd_apply hpre]
  calc
    (∫⁻ z, L z (Prod.mk z ⁻¹' (stateMarkTwoFuture ⁻¹'
      ({((q, (mark₁, mark₂)), mark₀)} : Set ((ℕ × (Bool × Bool)) × Bool)))) ∂ν) =
        ∫⁻ z, E.indicator (fun _ => B {mark₂}) z ∂ν := by
          apply lintegral_congr_ae
          filter_upwards [] with z
          exact hfiber z
    _ = B {mark₂} * ν E := by
      exact MeasureTheory.lintegral_indicator_const hE (B {mark₂})
    _ = B {mark₂} * ((π.prod B).prod B) {((q, mark₁), mark₀)} := by rw [hνE]
    _ = (π.prod (B.prod B)).prod B {((q, (mark₁, mark₂)), mark₀)} := by
      have hinner₀₁ : ((π.prod B).prod B) {((q, mark₁), mark₀)} =
          (π {q} * B {mark₁}) * B {mark₀} := by
        rw [← Set.singleton_prod_singleton, Measure.prod_prod,
          ← Set.singleton_prod_singleton, Measure.prod_prod]
      have hinner₁₂ : (B.prod B) {(mark₁, mark₂)} = B {mark₁} * B {mark₂} := by
        rw [← Set.singleton_prod_singleton, Measure.prod_prod]
      have hout : (π.prod (B.prod B)).prod B {((q, (mark₁, mark₂)), mark₀)} =
          (π {q} * (B.prod B) {(mark₁, mark₂)}) * B {mark₀} := by
        rw [← Set.singleton_prod_singleton, Measure.prod_prod,
          ← Set.singleton_prod_singleton, Measure.prod_prod]
      rw [hinner₀₁, hout, hinner₁₂]
      ac_rfl

private theorem geoNNPMF_uniformized_forwardReverseMarkedTraj_state_nextTwoMarks_currentMark_hasLaw
    (rho : ℝ≥0) (hrho : rho < 1) :
    HasLaw
      (fun x : ℤ → (ℕ × Bool) =>
        (((x 0).1, ((x 1).2, (x 2).2)), (x 0).2))
      (((geoNNPMF rho hrho).toMeasure.prod
        ((uniformizationArrivalMark (uniformizedBirthProbability rho)
          (uniformizedBirthProbability_le_one rho)).toMeasure.prod
          (uniformizationArrivalMark (uniformizedBirthProbability rho)
            (uniformizedBirthProbability_le_one rho)).toMeasure)).prod
        (uniformizationArrivalMark (uniformizedBirthProbability rho)
          (uniformizedBirthProbability_le_one rho)).toMeasure)
      (geoNNPMF_uniformized_forwardReverseMarkedTrajMeasure rho hrho) := by
  let π : Measure ℕ := (geoNNPMF rho hrho).toMeasure
  let p : ℝ≥0 := uniformizedBirthProbability rho
  let hp : p ≤ 1 := uniformizedBirthProbability_le_one rho
  let K : Kernel ℕ ℕ := countablePMFKernel (reflectedBirthDeathKernel p hp)
  let M : Measure (ℤ → ℕ) := geoNNPMF_uniformized_forwardReverseTrajMeasure rho hrho
  let ν : Measure ((ℕ × ℕ) × ℕ) := (π ⊗ₘ K) ⊗ₘ K.prodMkLeft ℕ
  have htriple : M.map (fun x => ((x 0, x (1 : ℤ)), x (2 : ℤ))) = ν := by
    simpa [π, p, hp, K, M, ν] using
      (forwardReverseTwoSidedTrajMeasure_zeroOneTwoTriple
        (π := (geoNNPMF rho hrho).toMeasure)
        (K := countablePMFKernel
          (reflectedBirthDeathKernel (uniformizedBirthProbability rho)
            (uniformizedBirthProbability_le_one rho)))
        (Kr := countablePMFKernel
          (reflectedBirthDeathKernel (uniformizedBirthProbability rho)
            (uniformizedBirthProbability_le_one rho))))
  have hquad : M.map (fun x => (((x 0, x (1 : ℤ)), x (2 : ℤ)), x (3 : ℤ))) =
      ν ⊗ₘ K.prodMkLeft (ℕ × ℕ) := by
    calc
      M.map (fun x => (((x 0, x (1 : ℤ)), x (2 : ℤ)), x (3 : ℤ))) =
          M.map (fun x => ((x 0, x (1 : ℤ)), x (2 : ℤ))) ⊗ₘ K.prodMkLeft (ℕ × ℕ) := by
            simpa [π, p, hp, K, M] using
              (forwardReverseTwoSidedTrajMeasure_zeroOneTwoThree_factor
                (π := (geoNNPMF rho hrho).toMeasure)
                (K := countablePMFKernel
                  (reflectedBirthDeathKernel (uniformizedBirthProbability rho)
                    (uniformizedBirthProbability_le_one rho)))
                (Kr := countablePMFKernel
                  (reflectedBirthDeathKernel (uniformizedBirthProbability rho)
                    (uniformizedBirthProbability_le_one rho))))
      _ = ν ⊗ₘ K.prodMkLeft (ℕ × ℕ) := by rw [htriple]
  have hedge : Measurable edgeMarkedPath := measurable_edgeMarkedPath
  have hstat : Measurable
      (fun x : ℤ → (ℕ × Bool) =>
        (((x 0).1, ((x 1).2, (x 2).2)), (x 0).2)) :=
    ((measurable_fst.comp (measurable_pi_apply 0)).prodMk
      ((measurable_snd.comp (measurable_pi_apply 1)).prodMk
        (measurable_snd.comp (measurable_pi_apply 2)))).prodMk
      (measurable_snd.comp (measurable_pi_apply 0))
  have hquadMap : Measurable
      (fun x : ℤ → ℕ => (((x 0, x (1 : ℤ)), x (2 : ℤ)), x (3 : ℤ))) :=
    (((measurable_pi_apply 0).prodMk (measurable_pi_apply (1 : ℤ))).prodMk
      (measurable_pi_apply (2 : ℤ))).prodMk (measurable_pi_apply (3 : ℤ))
  refine ⟨hstat.aemeasurable, ?_⟩
  change Measure.map
      (fun x : ℤ → (ℕ × Bool) =>
        (((x 0).1, ((x 1).2, (x 2).2)), (x 0).2))
      (M.map edgeMarkedPath) = _
  calc
    Measure.map
        (fun x : ℤ → (ℕ × Bool) =>
          (((x 0).1, ((x 1).2, (x 2).2)), (x 0).2))
        (M.map edgeMarkedPath) =
        Measure.map (fun x : ℤ → ℕ =>
          ((x 0, (isArrivalEdge (x (1 : ℤ)) (x (2 : ℤ)),
            isArrivalEdge (x (2 : ℤ)) (x (3 : ℤ)))),
            isArrivalEdge (x 0) (x (1 : ℤ)))) M := by
          rw [Measure.map_map hstat hedge]
          rfl
    _ = Measure.map stateMarkTwoFuture
        (Measure.map (fun x : ℤ → ℕ =>
          (((x 0, x (1 : ℤ)), x (2 : ℤ)), x (3 : ℤ))) M) := by
          symm
          rw [Measure.map_map measurable_stateMarkTwoFuture hquadMap]
          rfl
    _ = Measure.map stateMarkTwoFuture (ν ⊗ₘ K.prodMkLeft (ℕ × ℕ)) := by
      rw [hquad]
    _ = _ := by
      simpa [ν, p, hp, K] using stateMarkTwoFuture_productLaw π p hp

private theorem cond_stateNextTwoMarks_hasLaw_of_product
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {m : Ω → (ℕ × (Bool × Bool)) × Bool} (hm : Measurable m)
    {π : Measure ℕ} {B : Measure Bool}
    [IsProbabilityMeasure π] [IsProbabilityMeasure B]
    (H : HasLaw m ((π.prod (B.prod B)).prod B) P) (htrue : B {true} ≠ 0) :
    HasLaw (fun ω => (m ω).1) (π.prod (B.prod B))
      (P[| {ω | (m ω).2 = true}]) := by
  let E : Set Ω := {ω | (m ω).2 = true}
  let A : (ℕ × (Bool × Bool)) → Set Ω := fun y => {ω | (m ω).1 = y}
  have hE : MeasurableSet E :=
    (measurableSet_singleton true).preimage (measurable_snd.comp hm)
  have hPE : P E = B {true} := by
    calc
      P E = Measure.map m P (Set.univ ×ˢ ({true} : Set Bool)) := by
        rw [Measure.map_apply hm (MeasurableSet.univ.prod (measurableSet_singleton _))]
        congr 1
        ext ω
        simp [E]
      _ = ((π.prod (B.prod B)).prod B) (Set.univ ×ˢ ({true} : Set Bool)) := by
        rw [H.map_eq]
      _ = B {true} := by rw [Measure.prod_prod, measure_univ, one_mul]
  have hPEA (y : ℕ × (Bool × Bool)) :
      P (E ∩ A y) = B {true} * (π.prod (B.prod B)) {y} := by
    calc
      P (E ∩ A y) = Measure.map m P
          (({y} : Set (ℕ × (Bool × Bool))) ×ˢ ({true} : Set Bool)) := by
        rw [Measure.map_apply hm ((measurableSet_singleton _).prod
          (measurableSet_singleton _))]
        rw [show E ∩ A y = m ⁻¹'
            (({y} : Set (ℕ × (Bool × Bool))) ×ˢ ({true} : Set Bool)) by
          ext ω
          rcases hω : m ω with ⟨u, v⟩
          simp [E, A, hω, and_comm]]
      _ = ((π.prod (B.prod B)).prod B)
          (({y} : Set (ℕ × (Bool × Bool))) ×ˢ ({true} : Set Bool)) := by
        rw [H.map_eq]
      _ = B {true} * (π.prod (B.prod B)) {y} := by
        rw [Measure.prod_prod, mul_comm]
  refine ⟨(measurable_fst.comp hm).aemeasurable, ?_⟩
  change Measure.map (fun ω => (m ω).1) (P[| E]) = π.prod (B.prod B)
  apply Measure.ext_of_singleton
  intro y
  have hmap :
      Measure.map (fun ω => (m ω).1) (P[| E]) {y} =
        (P[| E]) ((fun ω => (m ω).1) ⁻¹'
          ({y} : Set (ℕ × (Bool × Bool)))) :=
    Measure.map_apply (f := fun ω => (m ω).1)
      (measurable_fst.comp hm) (measurableSet_singleton _)
  rw [hmap]
  change P[A y | E] = (π.prod (B.prod B)) {y}
  rw [cond_apply hE P (A y), hPE, hPEA, ← mul_assoc,
    ENNReal.inv_mul_cancel htrue (measure_ne_top B {true}), one_mul]

/-- Under the actual selected true-tag law, the embedded pre-arrival queue
length and the ordered pair of the next two embedded event marks have the
product of the stationary geometric law and two Bernoulli laws.  This is an
exact finite two-step factorization, not a claim about a full post-tag iid tail
or a continuous-time service process. -/
theorem geoNNPMF_uniformized_forwardReverseMarkedSelectedTag_state_nextTwoMarks_hasLaw
    {rate : ℝ} (hrate : 0 < rate) (rho : ℝ≥0) (hrho : rho < 1)
    (hrho_pos : 0 < rho) :
    HasLaw
      (fun z : (ℤ → ℝ) × (ℤ → (ℕ × Bool)) =>
        ((z.2 0).1, ((z.2 1).2, (z.2 2).2)))
      ((geoNNPMF rho hrho).toMeasure.prod
        ((uniformizationArrivalMark (uniformizedBirthProbability rho)
          (uniformizedBirthProbability_le_one rho)).toMeasure.prod
          (uniformizationArrivalMark (uniformizedBirthProbability rho)
            (uniformizedBirthProbability_le_one rho)).toMeasure))
      ((geoNNPMF_uniformized_forwardReverseMarkedTaggedArrivalAtZero
        hrate rho hrho).conditionOn
          (timedEmbeddedStateMarkZero ⁻¹' ({true} : Set Bool))
          (geoNNPMF_uniformized_forwardReverseMarkedTagged_true_mass_ne_zero
            hrate rho hrho hrho_pos)).Ptag := by
  let π : Measure ℕ := (geoNNPMF rho hrho).toMeasure
  let B : Measure Bool :=
    (uniformizationArrivalMark (uniformizedBirthProbability rho)
      (uniformizedBirthProbability_le_one rho)).toMeasure
  let P : Measure (ℤ → (ℕ × Bool)) :=
    geoNNPMF_uniformized_forwardReverseMarkedTrajMeasure rho hrho
  let T := geoNNPMF_uniformized_forwardReverseMarkedTaggedArrivalAtZero
    hrate rho hrho
  let m : ((ℤ → ℝ) × (ℤ → (ℕ × Bool))) → (ℕ × (Bool × Bool)) × Bool :=
    fun z => (((z.2 0).1, ((z.2 1).2, (z.2 2).2)), (z.2 0).2)
  letI : IsProbabilityMeasure π := by
    dsimp [π]
    infer_instance
  letI : IsProbabilityMeasure B := by
    dsimp [B]
    infer_instance
  letI : IsProbabilityMeasure P := by
    dsimp [P]
    exact isProbabilityMeasure_geoNNPMF_uniformized_forwardReverseMarkedTrajMeasure rho hrho
  letI : IsProbabilityMeasure T.Ptag := by
    dsimp [T]
    exact (geoNNPMF_uniformized_forwardReverseMarkedTaggedArrivalAtZero
      hrate rho hrho).isProbability
  have hpath : HasLaw
      (fun x : ℤ → (ℕ × Bool) =>
        (((x 0).1, ((x 1).2, (x 2).2)), (x 0).2))
      ((π.prod (B.prod B)).prod B) P := by
    simpa [π, B, P] using
      (geoNNPMF_uniformized_forwardReverseMarkedTraj_state_nextTwoMarks_currentMark_hasLaw
        rho hrho)
  have htagRaw := timedEmbeddedTaggedArrivalAtZero_pathStatistic_hasLaw P
    (fun x : ℤ → (ℕ × Bool) =>
      (((x 0).1, ((x 1).2, (x 2).2)), (x 0).2))
    (((measurable_fst.comp (measurable_pi_apply 0)).prodMk
      ((measurable_snd.comp (measurable_pi_apply 1)).prodMk
        (measurable_snd.comp (measurable_pi_apply 2)))).prodMk
        (measurable_snd.comp (measurable_pi_apply 0))) rate hrate
  have htag : HasLaw m ((π.prod (B.prod B)).prod B) T.Ptag := by
    refine ⟨(((measurable_fst.comp ((measurable_pi_apply 0).comp measurable_snd)).prodMk
      ((measurable_snd.comp ((measurable_pi_apply 1).comp measurable_snd)).prodMk
        (measurable_snd.comp ((measurable_pi_apply 2).comp measurable_snd)))).prodMk
        (measurable_snd.comp ((measurable_pi_apply 0).comp measurable_snd))).aemeasurable, ?_⟩
    change Measure.map m T.Ptag = (π.prod (B.prod B)).prod B
    calc
      Measure.map m T.Ptag = Measure.map
          (fun x : ℤ → (ℕ × Bool) =>
            (((x 0).1, ((x 1).2, (x 2).2)), (x 0).2)) P := by
            exact htagRaw.map_eq
      _ = (π.prod (B.prod B)).prod B := hpath.map_eq
  have hm : Measurable m :=
    ((measurable_fst.comp ((measurable_pi_apply 0).comp measurable_snd)).prodMk
      ((measurable_snd.comp ((measurable_pi_apply 1).comp measurable_snd)).prodMk
        (measurable_snd.comp ((measurable_pi_apply 2).comp measurable_snd)))).prodMk
      (measurable_snd.comp ((measurable_pi_apply 0).comp measurable_snd))
  have htrue : B {true} ≠ 0 := by
    dsimp [B]
    exact uniformizationArrivalMark_true_mass_ne_zero_of_rho_pos hrho_pos
  have hcond := cond_stateNextTwoMarks_hasLaw_of_product hm htag htrue
  change HasLaw
    (fun z : (ℤ → ℝ) × (ℤ → (ℕ × Bool)) => (m z).1)
    (π.prod (B.prod B))
    (T.conditionOn (timedEmbeddedStateMarkZero ⁻¹' ({true} : Set Bool))
      (geoNNPMF_uniformized_forwardReverseMarkedTagged_true_mass_ne_zero
        hrate rho hrho hrho_pos)).Ptag
  rw [TaggedArrivalAtZero.conditionOn_Ptag]
  simpa [m, timedEmbeddedStateMarkZero] using hcond

/-- The embedded coordinate-zero state of the stationary marked suspension has
the geometric M/M/1 marginal. -/
theorem geoNNPMF_uniformized_forwardReverseMarked_base_zero_state_hasLaw
    {rate : ℝ} (hrate : 0 < rate) (rho : ℝ≥0) (hrho : rho < 1) :
    HasLaw (fun z : GoodSuspensionState × (ℤ → (ℕ × Bool)) => (z.2 0).1)
      (geoNNPMF rho hrho).toMeasure
      (geoNNPMF_uniformized_forwardReverseMarkedSuspensionShiftInvariantLaw_of_unmarkedIntPathShift
        hrate rho hrho
        (fun k => geoNNPMF_uniformized_forwardReverseTraj_intPathShift_measurePreserving
          rho hrho k)).Pbase := by
  let π : Measure ℕ := (geoNNPMF rho hrho).toMeasure
  let B : Measure Bool :=
    (uniformizationArrivalMark (uniformizedBirthProbability rho)
      (uniformizedBirthProbability_le_one rho)).toMeasure
  letI : IsProbabilityMeasure π := by
    dsimp [π]
    infer_instance
  letI : IsProbabilityMeasure B := by
    dsimp [B]
    infer_instance
  have hzero := geoNNPMF_uniformized_forwardReverseMarkedSuspension_zero_coordinate_hasLaw
    hrate rho hrho
  refine ⟨(measurable_fst.comp ((measurable_pi_apply 0).comp measurable_snd)).aemeasurable, ?_⟩
  change Measure.map (fun z : GoodSuspensionState × (ℤ → (ℕ × Bool)) => (z.2 0).1)
      (geoNNPMF_uniformized_forwardReverseMarkedSuspensionProductMeasure rate rho hrho) = π
  calc
    Measure.map (fun z : GoodSuspensionState × (ℤ → (ℕ × Bool)) => (z.2 0).1)
        (geoNNPMF_uniformized_forwardReverseMarkedSuspensionProductMeasure rate rho hrho) =
        Measure.map Prod.fst
          (Measure.map (fun z : GoodSuspensionState × (ℤ → (ℕ × Bool)) => z.2 0)
            (geoNNPMF_uniformized_forwardReverseMarkedSuspensionProductMeasure rate rho hrho)) := by
          symm
          rw [Measure.map_map measurable_fst
            ((measurable_pi_apply 0).comp measurable_snd)]
          rfl
    _ = Measure.map Prod.fst (π.prod B) := by
          rw [hzero.map_eq]
    _ = π := by
          rw [Measure.map_fst_prod, measure_univ, one_smul]

/-- Before selecting the true mark, the tagged all-event state/mark coordinate
has the stationary geometric/Bernoulli product law. -/
theorem geoNNPMF_uniformized_forwardReverseMarked_tagged_zero_coordinate_hasLaw
    {rate : ℝ} (hrate : 0 < rate) (rho : ℝ≥0) (hrho : rho < 1) :
    HasLaw (fun z : (ℤ → ℝ) × (ℤ → (ℕ × Bool)) => z.2 0)
      ((geoNNPMF rho hrho).toMeasure.prod
        (uniformizationArrivalMark (uniformizedBirthProbability rho)
          (uniformizedBirthProbability_le_one rho)).toMeasure)
      (geoNNPMF_uniformized_forwardReverseMarkedTaggedArrivalAtZero
        hrate rho hrho).Ptag := by
  let π : Measure ℕ := (geoNNPMF rho hrho).toMeasure
  let B : Measure Bool :=
    (uniformizationArrivalMark (uniformizedBirthProbability rho)
      (uniformizedBirthProbability_le_one rho)).toMeasure
  let P : Measure (ℤ → (ℕ × Bool)) :=
    geoNNPMF_uniformized_forwardReverseMarkedTrajMeasure rho hrho
  letI : IsProbabilityMeasure π := by
    dsimp [π]
    infer_instance
  letI : IsProbabilityMeasure B := by
    dsimp [B]
    infer_instance
  letI : IsProbabilityMeasure P :=
    isProbabilityMeasure_geoNNPMF_uniformized_forwardReverseMarkedTrajMeasure rho hrho
  have hpath := timedEmbeddedTaggedArrivalAtZero_pathStatistic_hasLaw P
    (fun x : ℤ → (ℕ × Bool) => x 0) (measurable_pi_apply 0) rate hrate
  have hzero : HasLaw (fun x : ℤ → (ℕ × Bool) => x 0) (π.prod B) P := by
    simpa [π, B, P] using
      (geoNNPMF_uniformized_forwardReverseMarkedTraj_zero_coordinate_hasLaw rho hrho)
  refine ⟨(((measurable_pi_apply 0).comp measurable_snd)).aemeasurable, ?_⟩
  change Measure.map (fun z : (ℤ → ℝ) × (ℤ → (ℕ × Bool)) => z.2 0)
      (timedEmbeddedTaggedArrivalAtZero rate hrate P).Ptag = π.prod B
  exact hpath.map_eq.trans hzero.map_eq

/-- Conditioning the all-event tag on a true arrival leaves its embedded
pre-arrival queue-length marginal geometric. -/
theorem geoNNPMF_uniformized_forwardReverseMarked_selected_tag_zero_state_hasLaw
    {rate : ℝ} (hrate : 0 < rate) (rho : ℝ≥0) (hrho : rho < 1)
    (hrho_pos : 0 < rho) :
    HasLaw (fun z : (ℤ → ℝ) × (ℤ → (ℕ × Bool)) => (z.2 0).1)
      (geoNNPMF rho hrho).toMeasure
      ((geoNNPMF_uniformized_forwardReverseMarkedTaggedArrivalAtZero
        hrate rho hrho).conditionOn
          (timedEmbeddedStateMarkZero ⁻¹' ({true} : Set Bool))
          (geoNNPMF_uniformized_forwardReverseMarkedTagged_true_mass_ne_zero
            hrate rho hrho hrho_pos)).Ptag := by
  let π : Measure ℕ := (geoNNPMF rho hrho).toMeasure
  let B : Measure Bool :=
    (uniformizationArrivalMark (uniformizedBirthProbability rho)
      (uniformizedBirthProbability_le_one rho)).toMeasure
  let P : Measure ((ℤ → ℝ) × (ℤ → (ℕ × Bool))) :=
    (geoNNPMF_uniformized_forwardReverseMarkedTaggedArrivalAtZero
      hrate rho hrho).Ptag
  letI : IsProbabilityMeasure π := by
    dsimp [π]
    infer_instance
  letI : IsProbabilityMeasure B := by
    dsimp [B]
    infer_instance
  letI : IsProbabilityMeasure P := by
    dsimp [P]
    exact (geoNNPMF_uniformized_forwardReverseMarkedTaggedArrivalAtZero
      hrate rho hrho).isProbability
  have hcoord : HasLaw (fun z : (ℤ → ℝ) × (ℤ → (ℕ × Bool)) => z.2 0)
      (π.prod B) P := by
    simpa [π, B, P] using
      (geoNNPMF_uniformized_forwardReverseMarked_tagged_zero_coordinate_hasLaw
        hrate rho hrho)
  change HasLaw (fun z : (ℤ → ℝ) × (ℤ → (ℕ × Bool)) => (z.2 0).1) π
    (P[| {z | (z.2 0).2 = true}])
  have htrue : B {true} ≠ 0 := by
    change (uniformizationArrivalMark (uniformizedBirthProbability rho)
      (uniformizedBirthProbability_le_one rho)).toMeasure {true} ≠ 0
    rw [← geoNNPMF_uniformized_forwardReverseMarkedTagged_true_mass
      hrate rho hrho]
    exact geoNNPMF_uniformized_forwardReverseMarkedTagged_true_mass_ne_zero
      hrate rho hrho hrho_pos
  exact cond_state_hasLaw_of_stateMark_product
    ((measurable_pi_apply 0).comp measurable_snd) hcoord htrue

/-- The full future all-event Palm-gap path is iid exponential and has the
product law with the selected tag's pre-arrival queue length.  This is a
clock-versus-tagged-state statement, not a construction of post-tag service
or GPS response dynamics. -/
theorem geoNNPMF_uniformized_forwardReverseMarkedSelectedTag_futureGapPath_preArrivalQueueLength_hasLaw
    {rate : ℝ} (hrate : 0 < rate) (rho : ℝ≥0) (hrho : rho < 1)
    (hrho_pos : 0 < rho) :
    HasLaw
      (fun z : (ℤ → ℝ) × (ℤ → (ℕ × Bool)) =>
        (candidateFutureGapPath z.1, (z.2 0).1))
      ((exponentialInterarrivalMeasure rate).prod
        (geoNNPMF rho hrho).toMeasure)
      ((geoNNPMF_uniformized_forwardReverseMarkedTaggedArrivalAtZero
        hrate rho hrho).conditionOn
          (timedEmbeddedStateMarkZero ⁻¹' ({true} : Set Bool))
          (geoNNPMF_uniformized_forwardReverseMarkedTagged_true_mass_ne_zero
            hrate rho hrho hrho_pos)).Ptag := by
  have hstate : Measurable (fun x : ℤ → (ℕ × Bool) => (x 0).1) :=
    measurable_fst.comp (measurable_pi_apply 0)
  have hzero := geoNNPMF_uniformized_forwardReverseMarked_selected_tag_zero_state_hasLaw
    hrate rho hrho hrho_pos
  simpa using
    (geoNNPMF_uniformized_forwardReverseMarkedSelectedTag_futureGapPath_pathStatistic_hasLaw_of_hasLaw
      hrate rho hrho hrho_pos (fun x : ℤ → (ℕ × Bool) => (x 0).1) hstate
      ((geoNNPMF rho hrho).toMeasure) hzero)

/-- The complete post-tag all-event gap path under the actual selected Palm
tag has the canonical iid exponential law.  This is the clock before any
arrival/potential-service mark thinning. -/
theorem geoNNPMF_uniformized_forwardReverseMarkedSelectedTag_futureGapPath_hasLaw
    {rate : ℝ} (hrate : 0 < rate) (rho : ℝ≥0) (hrho : rho < 1)
    (hrho_pos : 0 < rho) :
    HasLaw
      (fun z : (ℤ → ℝ) × (ℤ → (ℕ × Bool)) => candidateFutureGapPath z.1)
      (exponentialInterarrivalMeasure rate)
      ((geoNNPMF_uniformized_forwardReverseMarkedTaggedArrivalAtZero
        hrate rho hrho).conditionOn
          (timedEmbeddedStateMarkZero ⁻¹' ({true} : Set Bool))
          (geoNNPMF_uniformized_forwardReverseMarkedTagged_true_mass_ne_zero
            hrate rho hrho hrho_pos)).Ptag := by
  let π : Measure ℕ := (geoNNPMF rho hrho).toMeasure
  letI : IsProbabilityMeasure π := by
    dsimp [π]
    infer_instance
  have hpair :=
    geoNNPMF_uniformized_forwardReverseMarkedSelectedTag_futureGapPath_preArrivalQueueLength_hasLaw
      hrate rho hrho hrho_pos
  have hfst : HasLaw Prod.fst (exponentialInterarrivalMeasure rate)
      ((exponentialInterarrivalMeasure rate).prod π) := by
    refine ⟨measurable_fst.aemeasurable, ?_⟩
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  simpa [Function.comp_def] using hfst.comp hpair

/-- Every fixed nonnegative horizon of the actual selected-Palm all-event
clock has its Poisson law.  This is an unthinned clock statement; the
corresponding false-mark service-count law still requires finite-prefix mark
thinning. -/
theorem geoNNPMF_uniformized_forwardReverseMarkedSelectedTag_allEventCount_hasLaw_poisson
    {rate t : ℝ} (hrate : 0 < rate) (rho : ℝ≥0) (hrho : rho < 1)
    (hrho_pos : 0 < rho) (ht : 0 ≤ t) :
    HasLaw
      (fun z : (ℤ → ℝ) × (ℤ → (ℕ × Bool)) =>
        canonicalRenewalCount t (suspensionFuturePath z.1))
      (ProbabilityTheory.poissonMeasure
        (⟨rate * t, mul_nonneg hrate.le ht⟩ : ℝ≥0))
      ((geoNNPMF_uniformized_forwardReverseMarkedTaggedArrivalAtZero
        hrate rho hrho).conditionOn
          (timedEmbeddedStateMarkZero ⁻¹' ({true} : Set Bool))
          (geoNNPMF_uniformized_forwardReverseMarkedTagged_true_mass_ne_zero
            hrate rho hrho hrho_pos)).Ptag := by
  have hfuture :=
    geoNNPMF_uniformized_forwardReverseMarkedSelectedTag_futureGapPath_hasLaw
      hrate rho hrho hrho_pos
  simpa [candidateFutureGapPath, suspensionFuturePath] using
    ((canonicalRenewalCount_hasLaw_poisson hrate ht).comp hfuture)

/-- At every fixed horizon, the selected tag's pre-arrival queue length and
the actual unthinned post-tag all-event count have their exact product law.
This establishes clock/state independence only; it does not turn false marks
into potential-service completions. -/
theorem geoNNPMF_uniformized_forwardReverseMarkedSelectedTag_preArrivalQueueLength_allEventCount_hasLaw
    {rate t : ℝ} (hrate : 0 < rate) (rho : ℝ≥0) (hrho : rho < 1)
    (hrho_pos : 0 < rho) (ht : 0 ≤ t) :
    HasLaw
      (fun z : (ℤ → ℝ) × (ℤ → (ℕ × Bool)) =>
        ((z.2 0).1, canonicalRenewalCount t (suspensionFuturePath z.1)))
      ((geoNNPMF rho hrho).toMeasure.prod
        (ProbabilityTheory.poissonMeasure
          (⟨rate * t, mul_nonneg hrate.le ht⟩ : ℝ≥0)))
      ((geoNNPMF_uniformized_forwardReverseMarkedTaggedArrivalAtZero
        hrate rho hrho).conditionOn
          (timedEmbeddedStateMarkZero ⁻¹' ({true} : Set Bool))
          (geoNNPMF_uniformized_forwardReverseMarkedTagged_true_mass_ne_zero
            hrate rho hrho hrho_pos)).Ptag := by
  let G : Measure (ℕ → ℝ) := exponentialInterarrivalMeasure rate
  let π : Measure ℕ := (geoNNPMF rho hrho).toMeasure
  let C : Measure ℕ := ProbabilityTheory.poissonMeasure
    (⟨rate * t, mul_nonneg hrate.le ht⟩ : ℝ≥0)
  letI : IsProbabilityMeasure G := by
    dsimp [G]
    exact isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  letI : IsProbabilityMeasure π := by
    dsimp [π]
    infer_instance
  have hpair :=
    geoNNPMF_uniformized_forwardReverseMarkedSelectedTag_futureGapPath_preArrivalQueueLength_hasLaw
      hrate rho hrho hrho_pos
  have hcount : HasLaw (canonicalRenewalCount t) C G := by
    simpa [G, C] using canonicalRenewalCount_hasLaw_poisson hrate ht
  have htransform : HasLaw
      (fun x : (ℕ → ℝ) × ℕ => (x.2, canonicalRenewalCount t x.1))
      (π.prod C) (G.prod π) := by
    refine ⟨((measurable_snd).prodMk
      ((measurable_canonicalRenewalCount t).comp measurable_fst)).aemeasurable, ?_⟩
    change Measure.map (fun x : (ℕ → ℝ) × ℕ =>
      (x.2, canonicalRenewalCount t x.1)) (G.prod π) = π.prod C
    have hprod : Measure.map (Prod.map (canonicalRenewalCount t) id) (G.prod π) =
        C.prod π := by
      calc
        Measure.map (Prod.map (canonicalRenewalCount t) id) (G.prod π) =
            (G.map (canonicalRenewalCount t)).prod (π.map id) := by
              exact (Measure.map_prod_map G π (measurable_canonicalRenewalCount t)
                measurable_id).symm
        _ = C.prod π := by rw [hcount.map_eq, Measure.map_id]
    calc
      Measure.map (fun x : (ℕ → ℝ) × ℕ =>
          (x.2, canonicalRenewalCount t x.1)) (G.prod π) =
          Measure.map Prod.swap
            (Measure.map (Prod.map (canonicalRenewalCount t) id) (G.prod π)) := by
              rw [Measure.map_map measurable_swap
                ((measurable_canonicalRenewalCount t).prodMap measurable_id)]
              rfl
      _ = Measure.map Prod.swap (C.prod π) := by
        rw [hprod]
      _ = π.prod C := by rw [Measure.prod_swap]
  simpa [G, π, C, Function.comp_def, candidateFutureGapPath, suspensionFuturePath] using
    htransform.comp hpair

/-- The selected tag's pre-arrival queue length is independent of the actual
unthinned all-event clock count at each fixed nonnegative horizon.  The
remaining service proof must separately establish marked thinning. -/
theorem geoNNPMF_uniformized_forwardReverseMarkedSelectedTag_preArrivalQueueLength_indep_allEventCount
    {rate t : ℝ} (hrate : 0 < rate) (rho : ℝ≥0) (hrho : rho < 1)
    (hrho_pos : 0 < rho) (ht : 0 ≤ t) :
    (fun z : (ℤ → ℝ) × (ℤ → (ℕ × Bool)) => (z.2 0).1) ⟂ᵢ[
      ((geoNNPMF_uniformized_forwardReverseMarkedTaggedArrivalAtZero
        hrate rho hrho).conditionOn
          (timedEmbeddedStateMarkZero ⁻¹' ({true} : Set Bool))
          (geoNNPMF_uniformized_forwardReverseMarkedTagged_true_mass_ne_zero
            hrate rho hrho hrho_pos)).Ptag]
      (fun z : (ℤ → ℝ) × (ℤ → (ℕ × Bool)) =>
        canonicalRenewalCount t (suspensionFuturePath z.1)) := by
  let tagged := geoNNPMF_uniformized_forwardReverseMarkedTaggedArrivalAtZero
    hrate rho hrho
  let selected := tagged.conditionOn
    (timedEmbeddedStateMarkZero ⁻¹' ({true} : Set Bool))
    (geoNNPMF_uniformized_forwardReverseMarkedTagged_true_mass_ne_zero
      hrate rho hrho hrho_pos)
  let P := selected.Ptag
  letI : IsProbabilityMeasure P := by
    exact selected.isProbability
  let q : ((ℤ → ℝ) × (ℤ → (ℕ × Bool))) → ℕ := fun z => (z.2 0).1
  let c : ((ℤ → ℝ) × (ℤ → (ℕ × Bool))) → ℕ :=
    fun z => canonicalRenewalCount t (suspensionFuturePath z.1)
  change q ⟂ᵢ[P] c
  have hjoint :=
    geoNNPMF_uniformized_forwardReverseMarkedSelectedTag_preArrivalQueueLength_allEventCount_hasLaw
      hrate rho hrho hrho_pos ht
  have hq := geoNNPMF_uniformized_forwardReverseMarked_selected_tag_zero_state_hasLaw
    hrate rho hrho hrho_pos
  have hc := geoNNPMF_uniformized_forwardReverseMarkedSelectedTag_allEventCount_hasLaw_poisson
    hrate rho hrho hrho_pos ht
  apply (indepFun_iff_map_prod_eq_prod_map_map
    ((measurable_fst.comp ((measurable_pi_apply 0).comp measurable_snd)).aemeasurable)
    (((measurable_canonicalRenewalCount t).comp
      ((measurable_pi_iff.2 fun n => measurable_twoSidedGap (Int.ofNat n)).comp
        measurable_fst)).aemeasurable)).2
  change Measure.map (fun z => (q z, c z)) P = (P.map q).prod (P.map c)
  change Measure.map (fun z => ((z.2 0).1, canonicalRenewalCount t (suspensionFuturePath z.1))) P = _
  change Measure.map (fun z => ((z.2 0).1, canonicalRenewalCount t (suspensionFuturePath z.1)))
    selected.Ptag = _
  rw [show selected.Ptag =
    ((geoNNPMF_uniformized_forwardReverseMarkedTaggedArrivalAtZero
      hrate rho hrho).conditionOn
        (timedEmbeddedStateMarkZero ⁻¹' ({true} : Set Bool))
        (geoNNPMF_uniformized_forwardReverseMarkedTagged_true_mass_ne_zero
          hrate rho hrho hrho_pos)).Ptag by rfl,
    hjoint.map_eq, hq.map_eq, hc.map_eq]

/-- The concrete selected true-arrival Palm construction, together with its
embedded queue-length PASTA identity.  This does not yet supply post-tag
service or GPS response dynamics. -/
noncomputable def geoNNPMF_uniformized_forwardReverseMarked_stationaryPalmPASTACertificate
    {rate : ℝ} (hrate : 0 < rate) (rho : ℝ≥0) (hrho : rho < 1)
    (hrho_pos : 0 < rho) :
    Palm.MarkedStationaryPalmPASTAQueueLengthCertificate
      (geoNNPMF_uniformized_forwardReverseMarkedSuspensionShiftInvariantLaw_of_unmarkedIntPathShift
        hrate rho hrho
        (fun k => geoNNPMF_uniformized_forwardReverseTraj_intPathShift_measurePreserving
          rho hrho k))
      ((geoNNPMF_uniformized_forwardReverseMarkedTaggedArrivalAtZero
        hrate rho hrho).conditionOn
          (timedEmbeddedStateMarkZero ⁻¹' ({true} : Set Bool))
          (geoNNPMF_uniformized_forwardReverseMarkedTagged_true_mass_ne_zero
            hrate rho hrho hrho_pos)) where
  toMarkedCampbellPalmTaggedArrivalCertificate :=
    geoNNPMF_uniformized_forwardReverseMarkedCampbellCertificate
      hrate rho hrho hrho_pos
  stationaryQueueLength := fun z => (z.2 0).1
  preArrivalQueueLength := fun z => (z.2 0).1
  stationaryQueueLength_measurable :=
    measurable_fst.comp ((measurable_pi_apply 0).comp measurable_snd)
  preArrivalQueueLength_measurable :=
    measurable_fst.comp ((measurable_pi_apply 0).comp measurable_snd)
  pasta_queue_length := by
    have hbase := geoNNPMF_uniformized_forwardReverseMarked_base_zero_state_hasLaw
      hrate rho hrho
    have htag := geoNNPMF_uniformized_forwardReverseMarked_selected_tag_zero_state_hasLaw
      hrate rho hrho hrho_pos
    refine ⟨(measurable_fst.comp ((measurable_pi_apply 0).comp measurable_snd)).aemeasurable, ?_⟩
    exact htag.map_eq.trans hbase.map_eq.symm

/-- The concrete stationary marked base has the geometric law at the queue
coordinate used by its selected-Palm PASTA certificate. -/
theorem geoNNPMF_uniformized_forwardReverseMarked_stationaryPalmPASTA_embeddedQueueLength_hasLaw
    {rate : ℝ} (hrate : 0 < rate) (rho : ℝ≥0) (hrho : rho < 1)
    (hrho_pos : 0 < rho) :
    HasLaw
      (geoNNPMF_uniformized_forwardReverseMarked_stationaryPalmPASTACertificate
        hrate rho hrho hrho_pos).to_pasta.stationaryQueueLength
      (geometricMeasure (p := 1 - (rho : ℝ))
        (sub_pos.mpr (by exact_mod_cast hrho))
        (sub_le_self 1 (by positivity : 0 ≤ (rho : ℝ))))
      (geoNNPMF_uniformized_forwardReverseMarkedSuspensionShiftInvariantLaw_of_unmarkedIntPathShift
        hrate rho hrho
        (fun k => geoNNPMF_uniformized_forwardReverseTraj_intPathShift_measurePreserving
          rho hrho k)).Pbase := by
  have hbase := geoNNPMF_uniformized_forwardReverseMarked_base_zero_state_hasLaw
    hrate rho hrho
  simpa [geoNNPMF_uniformized_forwardReverseMarked_stationaryPalmPASTACertificate,
    geoNNPMF_toMeasure_eq_geometricMeasure] using hbase

/-- Exact geometric tail of the stationary embedded queue statistic in the
concrete selected true-arrival Palm construction. -/
theorem geoNNPMF_uniformized_forwardReverseMarked_stationaryPalmPASTA_embeddedQueueLength_tail
    {rate : ℝ} (hrate : 0 < rate) (rho : ℝ≥0) (hrho : rho < 1)
    (hrho_pos : 0 < rho) (k : ℕ) :
    (geoNNPMF_uniformized_forwardReverseMarkedSuspensionShiftInvariantLaw_of_unmarkedIntPathShift
      hrate rho hrho
      (fun j => geoNNPMF_uniformized_forwardReverseTraj_intPathShift_measurePreserving
        rho hrho j)).Pbase.real
      {z | k ≤
        (geoNNPMF_uniformized_forwardReverseMarked_stationaryPalmPASTACertificate
          hrate rho hrho hrho_pos).to_pasta.stationaryQueueLength z} =
      (rho : ℝ) ^ k := by
  exact
    (geoNNPMF_uniformized_forwardReverseMarked_stationaryPalmPASTACertificate
      hrate rho hrho hrho_pos).to_pasta.real_stationaryQueueLength_tail_of_geometric_hasLaw
      (rho : ℝ) (by positivity) (by exact_mod_cast hrho)
      (geoNNPMF_uniformized_forwardReverseMarked_stationaryPalmPASTA_embeddedQueueLength_hasLaw
        hrate rho hrho hrho_pos) k

/-- At physical M/M/1 rates, the direct stationary marked-Palm construction
discharges the queue-tail premise used in the GPS response-tail reduction. -/
theorem geoNNPMF_uniformized_forwardReverseMarked_stationaryPalmPASTA_embeddedQueueLength_tail_of_rates
    {arrivalRate serviceRate : ℝ≥0}
    (harrival_pos : 0 < arrivalRate) (hstable : arrivalRate < serviceRate) :
    let rate : ℝ := ((arrivalRate + serviceRate : ℝ≥0) : ℝ)
    let hrate : 0 < rate := by
      exact_mod_cast (add_pos_of_pos_of_nonneg harrival_pos (zero_le serviceRate))
    let rho : ℝ≥0 := mm1TrafficIntensityNN arrivalRate serviceRate
    let hrho : rho < 1 := mm1TrafficIntensityNN_lt_one hstable
    let hrho_pos : 0 < rho := mm1TrafficIntensityNN_pos harrival_pos
      (lt_trans harrival_pos hstable)
    let H := geoNNPMF_uniformized_forwardReverseMarked_stationaryPalmPASTACertificate
      hrate rho hrho hrho_pos
    ∀ k : ℕ,
      (geoNNPMF_uniformized_forwardReverseMarkedSuspensionShiftInvariantLaw_of_unmarkedIntPathShift
        hrate rho hrho
        (fun j => geoNNPMF_uniformized_forwardReverseTraj_intPathShift_measurePreserving
          rho hrho j)).Pbase.real {z | k ≤ H.to_pasta.stationaryQueueLength z} =
        ((arrivalRate : ℝ) / (serviceRate : ℝ)) ^ k := by
  dsimp only
  intro k
  simpa only [coe_mm1TrafficIntensityNN_eq_mm1TrafficIntensity,
    mm1TrafficIntensity] using
    (geoNNPMF_uniformized_forwardReverseMarked_stationaryPalmPASTA_embeddedQueueLength_tail
      (rate := ((arrivalRate + serviceRate : ℝ≥0) : ℝ))
      (by
        exact_mod_cast
          (add_pos_of_pos_of_nonneg harrival_pos (zero_le serviceRate)))
      (mm1TrafficIntensityNN arrivalRate serviceRate)
      (mm1TrafficIntensityNN_lt_one hstable)
      (mm1TrafficIntensityNN_pos harrival_pos (lt_trans harrival_pos hstable)) k)

/-- The finite iid product measure on Boolean marks.  This is only a
finite-prefix object. -/
def iidPrefix (B : Measure Bool) (n : ℕ) : Measure (Fin n → Bool) :=
  Measure.pi (fun _ => B)

theorem iidPrefix_snoc
    (B : Measure Bool) [IsProbabilityMeasure B] (n : ℕ) :
    Measure.map (fun p : (Fin n → Bool) × Bool => snocWindow p.1 p.2)
      ((iidPrefix B n).prod B) = iidPrefix B (n + 1) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Bool) (Fin.last n)
  have he := measurePreserving_piFinSuccAbove
    (fun _ : Fin (n + 1) => B) (Fin.last n)
  have hfun :
      (fun p : (Fin n → Bool) × Bool => snocWindow p.1 p.2) =
        e.symm ∘ Prod.swap := by
    funext p
    simp [e, snocWindow, Fin.snocEquiv]
  calc
    Measure.map (fun p : (Fin n → Bool) × Bool => snocWindow p.1 p.2)
        ((iidPrefix B n).prod B) =
        Measure.map e.symm (Measure.map Prod.swap ((iidPrefix B n).prod B)) := by
          rw [Measure.map_map e.symm.measurable measurable_swap, hfun]
    _ = Measure.map e.symm (B.prod (iidPrefix B n)) := by
          rw [Measure.prod_swap]
    _ = iidPrefix B (n + 1) := by
          simpa [e, iidPrefix] using he.symm.map_eq

/-- A new reflected transition contributes an arrival/departure mark with the
same Bernoulli law independently of every retained countable history. -/
theorem retainedHistory_nextMark_productLaw
    {γ : Type*} [MeasurableSpace γ] [Countable γ] [MeasurableSingletonClass γ]
    (μ : Measure (γ × ℕ)) [IsProbabilityMeasure μ]
    (p : ℝ≥0) (hp : p ≤ 1) :
    Measure.map (fun z : (γ × ℕ) × ℕ =>
      (z.1.1, isArrivalEdge z.1.2 z.2))
      (μ ⊗ₘ (countablePMFKernel (reflectedBirthDeathKernel p hp)).prodMkLeft γ) =
      (Measure.map Prod.fst μ).prod (uniformizationArrivalMark p hp).toMeasure := by
  let B : Measure Bool := (uniformizationArrivalMark p hp).toMeasure
  let K : Kernel ℕ ℕ := countablePMFKernel (reflectedBirthDeathKernel p hp)
  let L : Kernel (γ × ℕ) ℕ := K.prodMkLeft γ
  let mark : (γ × ℕ) × ℕ → γ × Bool :=
    fun z => (z.1.1, isArrivalEdge z.1.2 z.2)
  have hmark : Measurable mark := measurable_of_countable _
  apply Measure.ext_of_singleton
  rintro ⟨history, nextMark⟩
  let E : Set (γ × ℕ) := {z | z.1 = history}
  have hE : MeasurableSet E :=
    (measurableSet_singleton history).preimage measurable_fst
  have hμE : μ E = Measure.map Prod.fst μ {history} := by
    rw [Measure.map_apply measurable_fst (measurableSet_singleton _)]
    rfl
  have hlocal (q : ℕ) :
      K q (isArrivalEdge q ⁻¹' ({nextMark} : Set Bool)) = B {nextMark} := by
    have h := congrArg (fun ν : Measure Bool => ν {nextMark})
      (map_isArrivalEdge_reflectedBirthDeathKernel p hp q)
    change Measure.map (isArrivalEdge q)
      (reflectedBirthDeathKernel p hp q).toMeasure {nextMark} = B {nextMark} at h
    rw [Measure.map_apply (measurable_of_countable _)
      (measurableSet_singleton nextMark)] at h
    simpa [K, B] using h
  have hfiber (z : γ × ℕ) :
      L z (Prod.mk z ⁻¹' (mark ⁻¹' ({(history, nextMark)} : Set (γ × Bool)))) =
        E.indicator (fun _ => B {nextMark}) z := by
    by_cases hz : z ∈ E
    · rcases z with ⟨g, q⟩
      have hg : g = history := hz
      change K q
        (Prod.mk (g, q) ⁻¹' (mark ⁻¹' ({(history, nextMark)} : Set (γ × Bool)))) = _
      rw [show Prod.mk (g, q) ⁻¹'
          (mark ⁻¹' ({(history, nextMark)} : Set (γ × Bool))) =
          isArrivalEdge q ⁻¹' ({nextMark} : Set Bool) by
            ext q'
            simp [mark, hg]]
      rw [hlocal]
      simp [E, hz]
    · rcases z with ⟨g, q⟩
      have hg : g ≠ history := by
        simpa [E] using hz
      change K q
        (Prod.mk (g, q) ⁻¹' (mark ⁻¹' ({(history, nextMark)} : Set (γ × Bool)))) = _
      rw [show Prod.mk (g, q) ⁻¹'
          (mark ⁻¹' ({(history, nextMark)} : Set (γ × Bool))) = ∅ by
            ext q'
            simp [mark, hg]]
      simp [E, hz]
  have hpre : MeasurableSet (mark ⁻¹' ({(history, nextMark)} : Set (γ × Bool))) :=
    (measurableSet_singleton _).preimage hmark
  change Measure.map mark (μ ⊗ₘ L) {(history, nextMark)} =
    (Measure.map Prod.fst μ).prod B {(history, nextMark)}
  rw [Measure.map_apply hmark (measurableSet_singleton _), Measure.compProd_apply hpre]
  calc
    (∫⁻ z, L z (Prod.mk z ⁻¹' (mark ⁻¹'
      ({(history, nextMark)} : Set (γ × Bool)))) ∂μ) =
        ∫⁻ z, E.indicator (fun _ => B {nextMark}) z ∂μ := by
          apply lintegral_congr_ae
          filter_upwards [] with z
          exact hfiber z
    _ = B {nextMark} * μ E := by
      exact MeasureTheory.lintegral_indicator_const hE (B {nextMark})
    _ = B {nextMark} * Measure.map Prod.fst μ {history} := by rw [hμE]
    _ = (Measure.map Prod.fst μ).prod B {(history, nextMark)} := by
      rw [← Set.singleton_prod_singleton, Measure.prod_prod, mul_comm]

def edgeMarkPrefix (n : ℕ) (w : Fin (n + 2) → ℕ) :
    ℕ × (Fin (n + 1) → Bool) :=
  (w 0, fun i => isArrivalEdge (w i.castSucc) (w i.succ))

theorem measurable_edgeMarkPrefix (n : ℕ) :
    Measurable (edgeMarkPrefix n) :=
  measurable_of_countable _

def appendEdgeMarkPrefix (n : ℕ) :
    (ℕ × (Fin (n + 1) → Bool)) × Bool → ℕ × (Fin (n + 2) → Bool) :=
  fun p => (p.1.1, snocWindow p.1.2 p.2)

theorem measurable_appendEdgeMarkPrefix (n : ℕ) :
    Measurable (appendEdgeMarkPrefix n) :=
  measurable_of_countable _

theorem edgeMarkPrefix_snoc (n : ℕ) (w : Fin (n + 2) → ℕ) (q : ℕ) :
    edgeMarkPrefix (n + 1) (snocWindow w q) =
      appendEdgeMarkPrefix n
        (edgeMarkPrefix n w, isArrivalEdge (w (Fin.last (n + 1))) q) := by
  apply Prod.ext
  · rfl
  · funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [edgeMarkPrefix, appendEdgeMarkPrefix, snocWindow]
    · have hsucc : (j.castSucc : Fin (n + 2)).succ = (j.succ).castSucc := by
        rfl
      have hvalue : (@Fin.snoc (n + 2) (fun _ => ℕ) w q) j.castSucc.succ =
          w j.succ := by
        simpa only [hsucc] using
          (@Fin.snoc_castSucc (n + 2) (fun _ => ℕ) q w j.succ)
      simp only [edgeMarkPrefix, appendEdgeMarkPrefix]
      simpa [snocWindow] using
        congrArg (fun r => isArrivalEdge (w j.castSucc) r) hvalue

theorem state_iidPrefix_snoc
    (π : Measure ℕ) (B : Measure Bool) [IsProbabilityMeasure π]
    [IsProbabilityMeasure B] (n : ℕ) :
    Measure.map (appendEdgeMarkPrefix n)
      ((π.prod (iidPrefix B (n + 1))).prod B) =
      π.prod (iidPrefix B (n + 2)) := by
  let I : Measure (Fin (n + 1) → Bool) := iidPrefix B (n + 1)
  let snoc : (Fin (n + 1) → Bool) × Bool → Fin (n + 2) → Bool :=
    fun p => snocWindow p.1 p.2
  have hsnoc : Measurable snoc := measurable_snocWindow (n + 1)
  have hfun : appendEdgeMarkPrefix n =
      (Prod.map id snoc) ∘ (MeasurableEquiv.prodAssoc :
        ((ℕ × (Fin (n + 1) → Bool)) × Bool) ≃ᵐ
          ℕ × ((Fin (n + 1) → Bool) × Bool)) := by
    rfl
  have hassoc := measurePreserving_prodAssoc π I B
  calc
    Measure.map (appendEdgeMarkPrefix n) ((π.prod I).prod B) =
        Measure.map (Prod.map id snoc)
          (Measure.map MeasurableEquiv.prodAssoc ((π.prod I).prod B)) := by
            rw [Measure.map_map (measurable_id.prodMap hsnoc)
              MeasurableEquiv.prodAssoc.measurable, hfun]
    _ = Measure.map (Prod.map id snoc) (π.prod (I.prod B)) := by
          rw [hassoc.map_eq]
    _ = (Measure.map id π).prod (Measure.map snoc (I.prod B)) := by
          rw [Measure.map_prod_map π (I.prod B) measurable_id hsnoc]
    _ = π.prod (iidPrefix B (n + 2)) := by
          rw [Measure.map_id, show Measure.map snoc (I.prod B) =
            iidPrefix B (n + 2) by
              simpa [I, snoc] using iidPrefix_snoc B (n + 1)]

def singletonMarkWindow (b : Bool) : Fin 1 → Bool := fun _ => b

theorem iidPrefix_zero (B : Measure Bool) :
    iidPrefix B 0 = Measure.dirac (fun i : Fin 0 => Fin.elim0 i) := by
  exact Measure.pi_of_empty _ _

theorem iidPrefix_one_from_singleton
    (B : Measure Bool) [IsProbabilityMeasure B] :
    Measure.map singletonMarkWindow B = iidPrefix B 1 := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 1 => Bool) 0
  let empty : Fin 0 → Bool := fun i => Fin.elim0 i
  have he := measurePreserving_piFinSuccAbove
    (fun _ : Fin 1 => B) 0
  have hfun : singletonMarkWindow = e.symm ∘ fun b => (b, empty) := by
    funext b
    funext i
    fin_cases i
    rfl
  calc
    Measure.map singletonMarkWindow B =
        Measure.map e.symm (Measure.map (fun b => (b, empty)) B) := by
          rw [Measure.map_map e.symm.measurable (measurable_of_countable _), hfun]
    _ = Measure.map e.symm (B.prod (Measure.dirac empty)) := by
          rw [Measure.prod_dirac]
    _ = Measure.map e.symm (B.prod (iidPrefix B 0)) := by
          rw [iidPrefix_zero]
    _ = iidPrefix B 1 := by
          simpa [e] using he.symm.map_eq

/-- Bridge the finite product measure to the literal iid-mark PMF used by
the finite marked-Poisson construction. -/
theorem iidPrefix_eq_iidMarks_toMeasure
    (p : ℝ≥0) (hp : p ≤ 1) (n : ℕ) :
    iidPrefix (uniformizationArrivalMark p hp).toMeasure n =
      (FiniteHorizonMarkedPoisson.iidMarks p hp n).toMeasure := by
  apply Measure.ext_of_singleton
  intro marks
  have hsingleton : ({marks} : Set (Fin n → Bool)) =
      Set.univ.pi (fun i : Fin n => ({marks i} : Set Bool)) := by
    ext x
    constructor
    · intro hx
      subst x
      simp
    · intro hx
      apply funext
      intro i
      simpa using hx i (by simp)
  rw [PMF.toMeasure_apply_singleton
    (FiniteHorizonMarkedPoisson.iidMarks p hp n)
      marks (measurableSet_singleton _)]
  change Measure.pi (fun _ : Fin n =>
    (uniformizationArrivalMark p hp).toMeasure) {marks} = _
  rw [hsingleton, Measure.pi_pi]
  simp [FiniteHorizonMarkedPoisson.iidMarks, uniformizationArrivalMark]

def edgeMarkPrefixHistoryLast (n : ℕ) (w : Fin (n + 2) → ℕ) :
    (ℕ × (Fin (n + 1) → Bool)) × ℕ :=
  (edgeMarkPrefix n w, w (Fin.last (n + 1)))

theorem measurable_edgeMarkPrefixHistoryLast (n : ℕ) :
    Measurable (edgeMarkPrefixHistoryLast n) :=
  measurable_of_countable _

/-- One Markov extension appends an independent Bernoulli mark to every
finite edge-mark prefix. -/
theorem edgeMarkPrefix_transition
    (ν : Measure (Fin (n + 2) → ℕ)) [IsProbabilityMeasure ν]
    (p : ℝ≥0) (hp : p ≤ 1) :
    Measure.map (edgeMarkPrefix (n + 1))
      (Measure.map (fun z : (Fin (n + 2) → ℕ) × ℕ => snocWindow z.1 z.2)
        (ν ⊗ₘ (countablePMFKernel (reflectedBirthDeathKernel p hp) ∘ₖ
          Kernel.deterministic
            (fun w : Fin (n + 2) → ℕ => w (Fin.last (n + 1)))
            (measurable_pi_apply _)))) =
      Measure.map (appendEdgeMarkPrefix n)
        ((Measure.map (edgeMarkPrefix n) ν).prod
          (uniformizationArrivalMark p hp).toMeasure) := by
  let γ : Type := ℕ × (Fin (n + 1) → Bool)
  let K : Kernel ℕ ℕ := countablePMFKernel (reflectedBirthDeathKernel p hp)
  let f : (Fin (n + 2) → ℕ) → γ × ℕ := edgeMarkPrefixHistoryLast n
  let L : Kernel (Fin (n + 2) → ℕ) ℕ := K ∘ₖ
    Kernel.deterministic
      (fun w : Fin (n + 2) → ℕ => w (Fin.last (n + 1)))
      (measurable_pi_apply _)
  let snoc : (Fin (n + 2) → ℕ) × ℕ → Fin (n + 3) → ℕ :=
    fun z => snocWindow z.1 z.2
  let h : (Fin (n + 2) → ℕ) × ℕ → γ × Bool :=
    fun z => (edgeMarkPrefix n z.1,
      isArrivalEdge (z.1 (Fin.last (n + 1))) z.2)
  let mark : (γ × ℕ) × ℕ → γ × Bool :=
    fun z => (z.1.1, isArrivalEdge z.1.2 z.2)
  have hf : Measurable f := measurable_edgeMarkPrefixHistoryLast n
  have hsnoc : Measurable snoc := measurable_snocWindow (n + 2)
  have hh : Measurable h := measurable_of_countable _
  have hmark : Measurable mark := measurable_of_countable _
  have happend : Measurable (appendEdgeMarkPrefix n) :=
    measurable_appendEdgeMarkPrefix n
  have hframe : Measurable (fun z : (Fin (n + 2) → ℕ) × ℕ => (f z.1, z.2)) :=
    hf.comp measurable_fst |>.prodMk measurable_snd
  have hKprod : K ∘ₖ Kernel.deterministic Prod.snd measurable_snd =
      K.prodMkLeft γ := by
    rw [Kernel.comp_deterministic_eq_comap]
    rfl
  have hthrough :
      Measure.map (fun z : (Fin (n + 2) → ℕ) × ℕ => (f z.1, z.2))
        (ν ⊗ₘ L) =
        (Measure.map f ν) ⊗ₘ K.prodMkLeft γ := by
    change Measure.map (fun z : (Fin (n + 2) → ℕ) × ℕ => (f z.1, z.2))
      (ν ⊗ₘ (K ∘ₖ Kernel.deterministic
        ((Prod.snd : γ × ℕ → ℕ) ∘ f) (measurable_snd.comp hf))) = _
    rw [Measure.compProd_map_through ν K f hf Prod.snd measurable_snd, hKprod]
  letI : IsProbabilityMeasure (Measure.map f ν) :=
    Measure.isProbabilityMeasure_map hf.aemeasurable
  have hmarklaw :
      Measure.map mark ((Measure.map f ν) ⊗ₘ K.prodMkLeft γ) =
        (Measure.map (edgeMarkPrefix n) ν).prod
          (uniformizationArrivalMark p hp).toMeasure := by
    calc
      Measure.map mark ((Measure.map f ν) ⊗ₘ K.prodMkLeft γ) =
          (Measure.map Prod.fst (Measure.map f ν)).prod
            (uniformizationArrivalMark p hp).toMeasure := by
              exact retainedHistory_nextMark_productLaw (Measure.map f ν) p hp
      _ = (Measure.map (edgeMarkPrefix n) ν).prod
            (uniformizationArrivalMark p hp).toMeasure := by
              rw [Measure.map_map measurable_fst hf]
              rfl
  calc
    Measure.map (edgeMarkPrefix (n + 1)) (Measure.map snoc (ν ⊗ₘ L)) =
        Measure.map (fun z : (Fin (n + 2) → ℕ) × ℕ =>
          edgeMarkPrefix (n + 1) (snoc z)) (ν ⊗ₘ L) := by
            rw [Measure.map_map (measurable_edgeMarkPrefix (n + 1)) hsnoc]
            rfl
    _ = Measure.map (fun z : (Fin (n + 2) → ℕ) × ℕ =>
          appendEdgeMarkPrefix n (h z)) (ν ⊗ₘ L) := by
            congr 1
            funext z
            exact edgeMarkPrefix_snoc n z.1 z.2
    _ = Measure.map (appendEdgeMarkPrefix n)
          (Measure.map h (ν ⊗ₘ L)) := by
            rw [Measure.map_map happend hh]
            rfl
    _ = Measure.map (appendEdgeMarkPrefix n)
          (Measure.map mark
            (Measure.map (fun z : (Fin (n + 2) → ℕ) × ℕ => (f z.1, z.2))
              (ν ⊗ₘ L))) := by
            congr 1
            rw [Measure.map_map hmark hframe]
            rfl
    _ = Measure.map (appendEdgeMarkPrefix n)
          (Measure.map mark ((Measure.map f ν) ⊗ₘ K.prodMkLeft γ)) := by
            rw [hthrough]
    _ = _ := by rw [hmarklaw]

def forwardEdgeMarkPrefix (n : ℕ) (x : ℤ → ℕ) :
    ℕ × (Fin (n + 1) → Bool) :=
  edgeMarkPrefix n (forwardWindow n x)

theorem measurable_forwardEdgeMarkPrefix (n : ℕ) :
    Measurable (forwardEdgeMarkPrefix n) :=
  (measurable_edgeMarkPrefix n).comp (measurable_forwardWindow n)

theorem forwardReverse_edgeMarkPrefix_base_hasLaw
    (π : Measure ℕ) [IsProbabilityMeasure π]
    (p : ℝ≥0) (hp : p ≤ 1)
    (hstationary : (countablePMFKernel (reflectedBirthDeathKernel p hp)).Invariant π) :
    HasLaw (forwardEdgeMarkPrefix 0)
      (π.prod (iidPrefix (uniformizationArrivalMark p hp).toMeasure 1))
      (forwardReverseTwoSidedTrajMeasure π
        (countablePMFKernel (reflectedBirthDeathKernel p hp))
        (countablePMFKernel (reflectedBirthDeathKernel p hp))) := by
  let B : Measure Bool := (uniformizationArrivalMark p hp).toMeasure
  let K : Kernel ℕ ℕ := countablePMFKernel (reflectedBirthDeathKernel p hp)
  let M : Measure (ℤ → ℕ) := forwardReverseTwoSidedTrajMeasure π K K
  let pair : (ℤ → ℕ) → ℕ × ℕ := fun x => (x 0, x 1)
  let stateMark : ℕ × Bool → ℕ × (Fin 1 → Bool) :=
    fun z => (z.1, singletonMarkWindow z.2)
  let pairPrefix : ℕ × ℕ → ℕ × (Fin 1 → Bool) :=
    fun z => (z.1, singletonMarkWindow (isArrivalEdge z.1 z.2))
  have hpair : M.map pair = π ⊗ₘ K := by
    simpa [M, pair, K] using
      (forwardReverseTwoSidedTrajMeasure_zeroOnePair
        (π := π) (K := K) (Kr := K) hstationary)
  have hpairPrefix : pairPrefix = stateMark ∘ markedEdgeProjection := by
    funext z
    rfl
  have hstateMark : Measurable stateMark := measurable_of_countable _
  have hpairPrefixMeasurable : Measurable pairPrefix := measurable_of_countable _
  have hpairMeasurable : Measurable pair :=
    (measurable_pi_apply 0).prodMk (measurable_pi_apply 1)
  have htarget : Measure.map stateMark (π.prod B) =
      π.prod (iidPrefix B 1) := by
    calc
      Measure.map stateMark (π.prod B) =
          (Measure.map id π).prod (Measure.map singletonMarkWindow B) := by
            rw [show stateMark = Prod.map id singletonMarkWindow by rfl,
              Measure.map_prod_map π B measurable_id (measurable_of_countable _)]
      _ = π.prod (iidPrefix B 1) := by
            rw [Measure.map_id, iidPrefix_one_from_singleton]
  refine ⟨(measurable_forwardEdgeMarkPrefix 0).aemeasurable, ?_⟩
  calc
    Measure.map (forwardEdgeMarkPrefix 0) M = Measure.map pairPrefix (M.map pair) := by
      rw [Measure.map_map hpairPrefixMeasurable hpairMeasurable]
      congr 1
      funext x
      dsimp [forwardEdgeMarkPrefix, edgeMarkPrefix, forwardWindow,
        pairPrefix, pair]
      apply Prod.ext
      · rfl
      · funext i
        fin_cases i
        rfl
    _ = Measure.map pairPrefix (π ⊗ₘ K) := by rw [hpair]
    _ = Measure.map stateMark (Measure.map markedEdgeProjection (π ⊗ₘ K)) := by
      rw [Measure.map_map hstateMark measurable_markedEdgeProjection, hpairPrefix]
    _ = Measure.map stateMark (π.prod B) := by
      rw [map_markedEdgeProjection_compProd_reflectedBirthDeathKernel]
    _ = π.prod (iidPrefix B 1) := htarget

/-- For every finite `n`, the stationary initial state together with edge
marks `0, …, n` has the geometric/state product law with a finite iid
Bernoulli mark block.  This is deliberately finite-prefix only. -/
theorem forwardReverse_edgeMarkPrefix_hasLaw
    (π : Measure ℕ) [IsProbabilityMeasure π]
    (p : ℝ≥0) (hp : p ≤ 1)
    (hstationary : (countablePMFKernel (reflectedBirthDeathKernel p hp)).Invariant π)
    (n : ℕ) :
    HasLaw (forwardEdgeMarkPrefix n)
      (π.prod (iidPrefix (uniformizationArrivalMark p hp).toMeasure (n + 1)))
      (forwardReverseTwoSidedTrajMeasure π
        (countablePMFKernel (reflectedBirthDeathKernel p hp))
        (countablePMFKernel (reflectedBirthDeathKernel p hp))) := by
  let B : Measure Bool := (uniformizationArrivalMark p hp).toMeasure
  let K : Kernel ℕ ℕ := countablePMFKernel (reflectedBirthDeathKernel p hp)
  let M : Measure (ℤ → ℕ) := forwardReverseTwoSidedTrajMeasure π K K
  have hT : IsProbabilityMeasure (stationaryTrajMeasure π K) := by
    unfold stationaryTrajMeasure
    infer_instance
  letI : IsProbabilityMeasure (stationaryTrajMeasure π K) := hT
  have hsource : IsProbabilityMeasure (forwardReverseTwoSidedSourceMeasure π K K) := by
    unfold forwardReverseTwoSidedSourceMeasure
    infer_instance
  letI : IsProbabilityMeasure (forwardReverseTwoSidedSourceMeasure π K K) := hsource
  have hM : IsProbabilityMeasure M := by
    dsimp [M]
    unfold forwardReverseTwoSidedTrajMeasure
    exact Measure.isProbabilityMeasure_map measurable_spliceForwardReverse.aemeasurable
  letI : IsProbabilityMeasure M := hM
  induction n with
  | zero =>
      simpa [B, K, M] using
        (forwardReverse_edgeMarkPrefix_base_hasLaw π p hp hstationary)
  | succ n ih =>
      let ν : Measure (Fin (n + 2) → ℕ) := M.map (forwardWindow n)
      let L : Kernel (Fin (n + 2) → ℕ) ℕ := K ∘ₖ
        Kernel.deterministic
          (fun w : Fin (n + 2) → ℕ => w (Fin.last (n + 1)))
          (measurable_pi_apply _)
      let snoc : (Fin (n + 2) → ℕ) × ℕ → Fin (n + 3) → ℕ :=
        fun z => snocWindow z.1 z.2
      letI : IsProbabilityMeasure ν :=
        Measure.isProbabilityMeasure_map (measurable_forwardWindow n).aemeasurable
      have hfactor : M.map (forwardWindow (n + 1)) =
          Measure.map snoc (ν ⊗ₘ L) := by
        simpa [M, ν, L, K, snoc] using
          (forwardReverseTwoSidedTrajMeasure_forwardWindow_succ_factor
            (π := π) (K := K) (Kr := K) n)
      have hprefix : Measure.map (edgeMarkPrefix n) ν =
          Measure.map (forwardEdgeMarkPrefix n) M := by
        rw [show ν = M.map (forwardWindow n) by rfl,
          Measure.map_map (measurable_edgeMarkPrefix n) (measurable_forwardWindow n)]
        rfl
      refine ⟨(measurable_forwardEdgeMarkPrefix (n + 1)).aemeasurable, ?_⟩
      calc
        Measure.map (forwardEdgeMarkPrefix (n + 1)) M =
            Measure.map (edgeMarkPrefix (n + 1))
              (M.map (forwardWindow (n + 1))) := by
                rw [Measure.map_map (measurable_edgeMarkPrefix (n + 1))
                  (measurable_forwardWindow (n + 1))]
                rfl
        _ = Measure.map (edgeMarkPrefix (n + 1)) (Measure.map snoc (ν ⊗ₘ L)) := by
              rw [hfactor]
        _ = Measure.map (appendEdgeMarkPrefix n)
              ((Measure.map (edgeMarkPrefix n) ν).prod B) := by
              simpa [B, K, L, snoc] using (edgeMarkPrefix_transition ν p hp)
        _ = Measure.map (appendEdgeMarkPrefix n)
              ((π.prod (iidPrefix B (n + 1))).prod B) := by
              rw [hprefix, ih.map_eq]
        _ = π.prod (iidPrefix B (n + 2)) := by
              exact state_iidPrefix_snoc π B n

def markedStateMarkPrefix (n : ℕ) (x : ℤ → (ℕ × Bool)) :
    ℕ × (Fin (n + 1) → Bool) :=
  ((x 0).1, fun i => (x (Int.ofNat i.1)).2)

theorem measurable_markedStateMarkPrefix (n : ℕ) :
    Measurable (markedStateMarkPrefix n) := by
  apply (measurable_fst.comp (measurable_pi_apply 0)).prodMk
  apply measurable_pi_lambda
  intro i
  exact measurable_snd.comp (measurable_pi_apply (Int.ofNat i.1))

/-- The actual edge-marked M/M/1 path has, at each finite prefix, the joint
law of its initial queue and an iid block of marks beginning at the current
edge.  No infinite iid mark-path assertion is made. -/
theorem geoNNPMF_uniformized_forwardReverseMarkedTraj_state_markPrefix_hasLaw
    (rho : ℝ≥0) (hrho : rho < 1) (n : ℕ) :
    HasLaw (markedStateMarkPrefix n)
      ((geoNNPMF rho hrho).toMeasure.prod
        (iidPrefix
          (uniformizationArrivalMark (uniformizedBirthProbability rho)
            (uniformizedBirthProbability_le_one rho)).toMeasure
          (n + 1)))
      (geoNNPMF_uniformized_forwardReverseMarkedTrajMeasure rho hrho) := by
  let π : Measure ℕ := (geoNNPMF rho hrho).toMeasure
  let p : ℝ≥0 := uniformizedBirthProbability rho
  let hp : p ≤ 1 := uniformizedBirthProbability_le_one rho
  let K : Kernel ℕ ℕ := countablePMFKernel (reflectedBirthDeathKernel p hp)
  let M : Measure (ℤ → ℕ) := geoNNPMF_uniformized_forwardReverseTrajMeasure rho hrho
  let P : Measure (ℤ → (ℕ × Bool)) :=
    geoNNPMF_uniformized_forwardReverseMarkedTrajMeasure rho hrho
  have hraw : HasLaw (forwardEdgeMarkPrefix n)
      (π.prod (iidPrefix (uniformizationArrivalMark p hp).toMeasure (n + 1))) M := by
    simpa [π, p, hp, K, M] using
      (forwardReverse_edgeMarkPrefix_hasLaw π p hp
        (geoNNPMF_uniformized_kernelInvariant rho hrho) n)
  refine ⟨(measurable_markedStateMarkPrefix n).aemeasurable, ?_⟩
  change Measure.map (markedStateMarkPrefix n) (M.map edgeMarkedPath) = _
  calc
    Measure.map (markedStateMarkPrefix n) (M.map edgeMarkedPath) =
        Measure.map (forwardEdgeMarkPrefix n) M := by
          rw [Measure.map_map (measurable_markedStateMarkPrefix n)
            measurable_edgeMarkedPath]
          have hfun : markedStateMarkPrefix n ∘ edgeMarkedPath = forwardEdgeMarkPrefix n := by
            funext x
            apply Prod.ext
            · rfl
            · funext i
              rfl
          rw [hfun]
    _ = π.prod (iidPrefix (uniformizationArrivalMark p hp).toMeasure (n + 1)) :=
      hraw.map_eq

def splitZeroMarkPrefix (n : ℕ) :
    ℕ × (Fin (n + 1) → Bool) → (ℕ × (Fin n → Bool)) × Bool :=
  fun z => ((z.1, fun i => z.2 i.succ), z.2 0)

theorem measurable_splitZeroMarkPrefix (n : ℕ) :
    Measurable (splitZeroMarkPrefix n) :=
  measurable_of_countable _

theorem splitZeroMarkPrefix_productLaw
    (π : Measure ℕ) (B : Measure Bool)
    [IsProbabilityMeasure π] [IsProbabilityMeasure B] (n : ℕ) :
    Measure.map (splitZeroMarkPrefix n)
      (π.prod (iidPrefix B (n + 1))) =
      (π.prod (iidPrefix B n)).prod B := by
  let I : Measure (Fin n → Bool) := iidPrefix B n
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Bool) 0
  let reorder : ℕ × (Bool × (Fin n → Bool)) → (ℕ × (Fin n → Bool)) × Bool :=
    fun z => ((z.1, z.2.2), z.2.1)
  have he : Measure.map e (iidPrefix B (n + 1)) = B.prod I := by
    simpa [e, I, iidPrefix] using
      (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => B) 0).map_eq
  have hfirst :
      Measure.map (Prod.map id e) (π.prod (iidPrefix B (n + 1))) =
        π.prod (B.prod I) := by
    calc
      Measure.map (Prod.map id e) (π.prod (iidPrefix B (n + 1))) =
          (Measure.map id π).prod (Measure.map e (iidPrefix B (n + 1))) := by
            rw [Measure.map_prod_map π (iidPrefix B (n + 1)) measurable_id e.measurable]
      _ = π.prod (B.prod I) := by rw [Measure.map_id, he]
  have horder : Measure.map reorder (π.prod (B.prod I)) =
      (π.prod I).prod B := by
    let a : ℕ × (Bool × (Fin n → Bool)) → (ℕ × Bool) × (Fin n → Bool) :=
      MeasurableEquiv.prodAssoc.symm
    let b : (ℕ × Bool) × (Fin n → Bool) → (Bool × ℕ) × (Fin n → Bool) :=
      Prod.map Prod.swap id
    let c : (Bool × ℕ) × (Fin n → Bool) → Bool × (ℕ × (Fin n → Bool)) :=
      MeasurableEquiv.prodAssoc
    let d : Bool × (ℕ × (Fin n → Bool)) → (ℕ × (Fin n → Bool)) × Bool :=
      Prod.swap
    have ha_m : Measurable a := MeasurableEquiv.prodAssoc.symm.measurable
    have hb_m : Measurable b := measurable_swap.prodMap measurable_id
    have hc_m : Measurable c := MeasurableEquiv.prodAssoc.measurable
    have hd_m : Measurable d := measurable_swap
    have ha : Measure.map a (π.prod (B.prod I)) = (π.prod B).prod I := by
      simpa [a] using (measurePreserving_prodAssoc π B I).symm.map_eq
    have hb : Measure.map b ((π.prod B).prod I) = (B.prod π).prod I := by
      calc
        Measure.map b ((π.prod B).prod I) =
            (Measure.map Prod.swap (π.prod B)).prod (Measure.map id I) := by
              rw [show b = Prod.map Prod.swap id by rfl,
                Measure.map_prod_map (π.prod B) I measurable_swap measurable_id]
        _ = (B.prod π).prod I := by rw [Measure.prod_swap, Measure.map_id]
    have hc : Measure.map c ((B.prod π).prod I) = B.prod (π.prod I) := by
      simpa [c] using (Measure.prodAssoc_prod (μ := B) (ν := π) (τ := I))
    have hd : Measure.map d (B.prod (π.prod I)) = (π.prod I).prod B := by
      rw [show d = Prod.swap by rfl, Measure.prod_swap]
    calc
      Measure.map reorder (π.prod (B.prod I)) =
          Measure.map d (Measure.map c (Measure.map b (Measure.map a
            (π.prod (B.prod I))))) := by
              rw [Measure.map_map hd_m hc_m,
                Measure.map_map (hd_m.comp hc_m) hb_m,
                Measure.map_map ((hd_m.comp hc_m).comp hb_m) ha_m]
              congr 1
      _ = Measure.map d (Measure.map c (Measure.map b ((π.prod B).prod I))) := by rw [ha]
      _ = Measure.map d (Measure.map c ((B.prod π).prod I)) := by rw [hb]
      _ = Measure.map d (B.prod (π.prod I)) := by rw [hc]
      _ = (π.prod I).prod B := hd
  have hsplit : splitZeroMarkPrefix n = reorder ∘ Prod.map id e := by
    funext z
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · funext i
        change z.2 i.succ = z.2 i.succ
        rfl
    · simp [splitZeroMarkPrefix, reorder, e]
  calc
    Measure.map (splitZeroMarkPrefix n) (π.prod (iidPrefix B (n + 1))) =
        Measure.map reorder (Measure.map (Prod.map id e)
          (π.prod (iidPrefix B (n + 1)))) := by
            rw [Measure.map_map (measurable_of_countable _)
              (measurable_id.prodMap e.measurable), hsplit]
    _ = Measure.map reorder (π.prod (B.prod I)) := by rw [hfirst]
    _ = (π.prod I).prod B := horder

theorem cond_history_hasLaw_of_historyMark_product
    {Ω γ : Type*} [MeasurableSpace Ω] [MeasurableSpace γ]
    [Countable γ] [MeasurableSingletonClass γ]
    {P : Measure Ω} {μ : Measure γ} {B : Measure Bool}
    [IsProbabilityMeasure P] [IsProbabilityMeasure μ] [IsProbabilityMeasure B]
    {historyMark : Ω → γ × Bool}
    (hhistoryMark : Measurable historyMark)
    (H : HasLaw historyMark (μ.prod B) P)
    (htrue : B {true} ≠ 0) :
    HasLaw (fun ω => (historyMark ω).1) μ
      (P[| {ω | (historyMark ω).2 = true}]) := by
  let E : Set Ω := {ω | (historyMark ω).2 = true}
  have hE : MeasurableSet E :=
    (measurableSet_singleton _).preimage (measurable_snd.comp hhistoryMark)
  have hPE : P E = B {true} := by
    calc
      P E = Measure.map historyMark P ((Set.univ : Set γ) ×ˢ ({true} : Set Bool)) := by
        rw [Measure.map_apply hhistoryMark (MeasurableSet.univ.prod
          (measurableSet_singleton _))]
        congr 1
        ext ω
        simp [E]
      _ = (μ.prod B) ((Set.univ : Set γ) ×ˢ ({true} : Set Bool)) := by
        rw [H.map_eq]
      _ = B {true} := by rw [Measure.prod_prod, measure_univ, one_mul]
  have hhistory : Measurable (fun ω => (historyMark ω).1) :=
    measurable_fst.comp hhistoryMark
  refine ⟨hhistory.aemeasurable, ?_⟩
  apply Measure.ext_of_singleton
  intro q
  let Q : Set Ω := {ω | (historyMark ω).1 = q}
  have hPEQ : P (E ∩ Q) = B {true} * μ {q} := by
    let T : Set (γ × Bool) := ({q} : Set γ) ×ˢ ({true} : Set Bool)
    have hT : MeasurableSet T :=
      (measurableSet_singleton _).prod (measurableSet_singleton _)
    have hpre : historyMark ⁻¹' T = E ∩ Q := by
      ext ω
      rcases hhm : historyMark ω with ⟨a, b⟩
      simp [hhm, E, Q, T, and_comm]
    calc
      P (E ∩ Q) = P (historyMark ⁻¹' T) := by rw [hpre]
      _ = Measure.map historyMark P T := by
        rw [Measure.map_apply_of_aemeasurable H.aemeasurable hT]
      _ = (μ.prod B) T := by rw [H.map_eq]
      _ = B {true} * μ {q} := by
        rw [show T = ({q} : Set γ) ×ˢ ({true} : Set Bool) by rfl,
          Measure.prod_prod, mul_comm]
  rw [Measure.map_apply hhistory (measurableSet_singleton _)]
  change P[Q | E] = μ {q}
  rw [cond_apply hE P Q, hPE, hPEQ, ← mul_assoc,
    ENNReal.inv_mul_cancel htrue (measure_ne_top B {true}), one_mul]

def selectedStateFutureMarkPrefix (n : ℕ)
    (z : (ℤ → ℝ) × (ℤ → (ℕ × Bool))) : ℕ × (Fin n → Bool) :=
  ((z.2 0).1, fun i => (z.2 (Int.ofNat (i.1 + 1))).2)

theorem measurable_selectedStateFutureMarkPrefix (n : ℕ) :
    Measurable (selectedStateFutureMarkPrefix n) := by
  apply (measurable_fst.comp ((measurable_pi_apply 0).comp measurable_snd)).prodMk
  apply measurable_pi_lambda
  intro i
  exact measurable_snd.comp
    ((measurable_pi_apply (Int.ofNat (i.1 + 1))).comp measurable_snd)

/-- Under the actual selected true-arrival Palm tag, every finite post-tag
block of all-event marks is iid Bernoulli and jointly independent of the
pre-arrival queue.  The statement is finite-prefix only (not an infinite iid
tail), and its mark-law target is the concrete finite PMF used by marked
Poisson thinning. -/
theorem geoNNPMF_uniformized_forwardReverseMarkedSelectedTag_state_futureMarkPrefix_hasLaw
    {rate : ℝ} (hrate : 0 < rate) (rho : ℝ≥0) (hrho : rho < 1)
    (hrho_pos : 0 < rho) (n : ℕ) :
    HasLaw (selectedStateFutureMarkPrefix n)
      ((geoNNPMF rho hrho).toMeasure.prod
        (FiniteHorizonMarkedPoisson.iidMarks (uniformizedBirthProbability rho)
          (uniformizedBirthProbability_le_one rho) n).toMeasure)
      ((geoNNPMF_uniformized_forwardReverseMarkedTaggedArrivalAtZero
        hrate rho hrho).conditionOn
          (timedEmbeddedStateMarkZero ⁻¹' ({true} : Set Bool))
          (geoNNPMF_uniformized_forwardReverseMarkedTagged_true_mass_ne_zero
            hrate rho hrho hrho_pos)).Ptag := by
  let π : Measure ℕ := (geoNNPMF rho hrho).toMeasure
  let p : ℝ≥0 := uniformizedBirthProbability rho
  let hp : p ≤ 1 := uniformizedBirthProbability_le_one rho
  let B : Measure Bool := (uniformizationArrivalMark p hp).toMeasure
  let I : Measure (Fin n → Bool) := iidPrefix B n
  let R : Measure (ℤ → (ℕ × Bool)) :=
    geoNNPMF_uniformized_forwardReverseMarkedTrajMeasure rho hrho
  let T := geoNNPMF_uniformized_forwardReverseMarkedTaggedArrivalAtZero
    hrate rho hrho
  let P : Measure ((ℤ → ℝ) × (ℤ → (ℕ × Bool))) := T.Ptag
  let mPath : (ℤ → (ℕ × Bool)) → (ℕ × (Fin n → Bool)) × Bool :=
    splitZeroMarkPrefix n ∘ markedStateMarkPrefix n
  let m : ((ℤ → ℝ) × (ℤ → (ℕ × Bool))) → (ℕ × (Fin n → Bool)) × Bool :=
    fun z => mPath z.2
  letI : IsProbabilityMeasure R := by
    dsimp [R]
    exact isProbabilityMeasure_geoNNPMF_uniformized_forwardReverseMarkedTrajMeasure
      rho hrho
  letI : IsProbabilityMeasure P := by
    dsimp [P, T]
    exact (geoNNPMF_uniformized_forwardReverseMarkedTaggedArrivalAtZero
      hrate rho hrho).isProbability
  letI : IsProbabilityMeasure π := by
    dsimp [π]
    infer_instance
  letI : IsProbabilityMeasure B := by
    dsimp [B]
    infer_instance
  letI : IsProbabilityMeasure I := by
    dsimp [I, iidPrefix]
    infer_instance
  letI : IsProbabilityMeasure (π.prod I) := by infer_instance
  have hpath : HasLaw (markedStateMarkPrefix n)
      (π.prod (iidPrefix B (n + 1))) R := by
    simpa [π, p, hp, B, R] using
      (geoNNPMF_uniformized_forwardReverseMarkedTraj_state_markPrefix_hasLaw
        rho hrho n)
  have hmPath : Measurable mPath :=
    (measurable_splitZeroMarkPrefix n).comp (measurable_markedStateMarkPrefix n)
  have hpathSplit : HasLaw mPath ((π.prod I).prod B) R := by
    refine ⟨hmPath.aemeasurable, ?_⟩
    calc
      Measure.map mPath R =
          Measure.map (splitZeroMarkPrefix n)
            (Measure.map (markedStateMarkPrefix n) R) := by
              rw [Measure.map_map (measurable_splitZeroMarkPrefix n)
                (measurable_markedStateMarkPrefix n)]
      _ = Measure.map (splitZeroMarkPrefix n)
            (π.prod (iidPrefix B (n + 1))) := by rw [hpath.map_eq]
      _ = (π.prod I).prod B := by
            simpa [I] using (splitZeroMarkPrefix_productLaw π B n)
  have htagLift := timedEmbeddedTaggedArrivalAtZero_pathStatistic_hasLaw R
    mPath hmPath rate hrate
  have hm : Measurable m := hmPath.comp measurable_snd
  have htag : HasLaw m ((π.prod I).prod B) P := by
    refine ⟨hm.aemeasurable, ?_⟩
    change Measure.map (fun z => mPath z.2) P = (π.prod I).prod B
    exact htagLift.map_eq.trans hpathSplit.map_eq
  have htrue : B {true} ≠ 0 := by
    dsimp [B, p, hp]
    exact uniformizationArrivalMark_true_mass_ne_zero_of_rho_pos hrho_pos
  have hcond := cond_history_hasLaw_of_historyMark_product hm htag htrue
  change HasLaw (selectedStateFutureMarkPrefix n)
    (π.prod (FiniteHorizonMarkedPoisson.iidMarks p hp n).toMeasure)
    (T.conditionOn
      (timedEmbeddedStateMarkZero ⁻¹' ({true} : Set Bool))
      (geoNNPMF_uniformized_forwardReverseMarkedTagged_true_mass_ne_zero
        hrate rho hrho hrho_pos)).Ptag
  rw [TaggedArrivalAtZero.conditionOn_Ptag]
  rw [← iidPrefix_eq_iidMarks_toMeasure p hp n]
  simpa [selectedStateFutureMarkPrefix, m, mPath, splitZeroMarkPrefix,
    markedStateMarkPrefix, timedEmbeddedStateMarkZero, I] using hcond

end

end AppliedModelingLib.Probability.Queueing
