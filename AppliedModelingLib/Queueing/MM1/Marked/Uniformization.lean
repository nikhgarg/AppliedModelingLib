import AppliedModelingLib.Queueing.MM1.Trajectory.Transition
import Mathlib.Probability.HasLaw
import Mathlib.Probability.ConditionalProbability
import Mathlib.Tactic

/-!
# One-step marked uniformization for M/M/1

This module gives a one-step realization of the reflected uniformized M/M/1
kernel.  A Boolean mark is an arrival when it is `true` and a potential-service
attempt when it is `false`; the deterministic update reflects a potential
service attempt at zero.  The results are deliberately one-edge statements.
They do not construct a marked clock path, prove thinning, identify a CTMC,
or establish Palm/PASTA properties.
-/

namespace AppliedModelingLib.Probability.Queueing

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

/-- A `true` mark is an arrival; a `false` mark is a potential-service attempt
and is reflected when the queue is empty. -/
def reflectedBirthDeathUpdate (q : ℕ) : Bool → ℕ :=
  fun mark => if mark then q + 1 else q - 1

/-- Recover the arrival mark from a nearest-neighbor transition edge. -/
def isArrivalEdge (q q' : ℕ) : Bool :=
  decide (q' = q + 1)

@[simp] theorem reflectedBirthDeathUpdate_arrival (q : ℕ) :
    reflectedBirthDeathUpdate q true = q + 1 := rfl

@[simp] theorem reflectedBirthDeathUpdate_potentialService (q : ℕ) :
    reflectedBirthDeathUpdate q false = q - 1 := rfl

@[simp] theorem isArrivalEdge_reflectedBirthDeathUpdate (q : ℕ) (mark : Bool) :
    isArrivalEdge q (reflectedBirthDeathUpdate q mark) = mark := by
  cases mark <;> simp [isArrivalEdge, reflectedBirthDeathUpdate]

/-- The Bernoulli arrival-versus-potential-service mark distribution. -/
def uniformizationArrivalMark (p : ℝ≥0) (hp : p ≤ 1) : PMF Bool :=
  PMF.bernoulli p hp

theorem uniformizationArrivalMark_true_mass
    (p : ℝ≥0) (hp : p ≤ 1) :
    (uniformizationArrivalMark p hp).toMeasure {true} = (p : ℝ≥0∞) := by
  simp [uniformizationArrivalMark]

theorem uniformizationArrivalMark_true_mass_ofReal
    (p : ℝ≥0) (hp : p ≤ 1) :
    (uniformizationArrivalMark p hp).toMeasure {true} =
      ENNReal.ofReal (p : ℝ) := by
  simpa only [ENNReal.ofReal_coe_nnreal] using
    (uniformizationArrivalMark_true_mass p hp)

/-- The probability mass of a `false` mark (a potential-service attempt). -/
theorem uniformizationArrivalMark_false_mass
    (p : ℝ≥0) (hp : p ≤ 1) :
    (uniformizationArrivalMark p hp).toMeasure {false} =
      ((1 - p : ℝ≥0) : ℝ≥0∞) := by
  simp [uniformizationArrivalMark]

theorem uniformizedBirthProbability_pos
    {rho : ℝ≥0} (hrho_pos : 0 < rho) :
    0 < uniformizedBirthProbability rho := by
  unfold uniformizedBirthProbability
  exact div_pos hrho_pos (by positivity)

theorem uniformizationArrivalMark_true_mass_ne_zero_of_rho_pos
    {rho : ℝ≥0} (hrho_pos : 0 < rho) :
    (uniformizationArrivalMark (uniformizedBirthProbability rho)
      (uniformizedBirthProbability_le_one rho)).toMeasure {true} ≠ 0 := by
  rw [uniformizationArrivalMark_true_mass]
  exact ENNReal.coe_ne_zero.mpr <|
    ne_of_gt (uniformizedBirthProbability_pos hrho_pos)

theorem total_uniformized_rate_mul_birthProbability
    {arrivalRate serviceRate : ℝ≥0} (hservice_pos : 0 < serviceRate) :
    (arrivalRate + serviceRate) *
      uniformizedBirthProbability
        (mm1TrafficIntensityNN arrivalRate serviceRate) = arrivalRate := by
  rw [uniformizedBirthProbability_eq_rate_fraction hservice_pos]
  apply NNReal.eq
  norm_cast
  field_simp [ne_of_gt (add_pos_of_pos_of_nonneg hservice_pos (zero_le _))]

/-- At the physical M/M/1 rates, the uniformization clock rate times the
`false`-mark probability is exactly the potential-service rate. -/
theorem total_uniformized_rate_mul_potentialServiceProbability
    {arrivalRate serviceRate : ℝ≥0} (hservice_pos : 0 < serviceRate) :
    (arrivalRate + serviceRate) *
      (1 - uniformizedBirthProbability
        (mm1TrafficIntensityNN arrivalRate serviceRate)) = serviceRate := by
  rw [mul_tsub, mul_one,
    total_uniformized_rate_mul_birthProbability hservice_pos]
  exact add_tsub_cancel_left arrivalRate serviceRate

/-- In measure/intensity form, the `false`-mark mass of the physical
uniformization clock is exactly the potential-service intensity. -/
theorem total_uniformized_rate_mul_false_mark_mass
    {arrivalRate serviceRate : ℝ≥0} (hservice_pos : 0 < serviceRate) :
    ENNReal.ofReal ((arrivalRate + serviceRate : ℝ≥0) : ℝ) *
      (uniformizationArrivalMark
        (uniformizedBirthProbability
          (mm1TrafficIntensityNN arrivalRate serviceRate))
        (uniformizedBirthProbability_le_one _)).toMeasure {false} =
      ENNReal.ofReal (serviceRate : ℝ) := by
  rw [uniformizationArrivalMark_false_mass]
  simp only [ENNReal.ofReal_coe_nnreal]
  exact_mod_cast total_uniformized_rate_mul_potentialServiceProbability hservice_pos

theorem mm1TrafficIntensityNN_pos
    {arrivalRate serviceRate : ℝ≥0}
    (harrival_pos : 0 < arrivalRate) (hservice_pos : 0 < serviceRate) :
    0 < mm1TrafficIntensityNN arrivalRate serviceRate := by
  unfold mm1TrafficIntensityNN
  exact div_pos harrival_pos hservice_pos

theorem uniformizedBirthProbability_pos_of_positive_arrival
    {arrivalRate serviceRate : ℝ≥0}
    (harrival_pos : 0 < arrivalRate) (hstable : arrivalRate < serviceRate) :
    0 < uniformizedBirthProbability
      (mm1TrafficIntensityNN arrivalRate serviceRate) := by
  rw [uniformizedBirthProbability_eq_rate_fraction (lt_trans harrival_pos hstable)]
  exact div_pos harrival_pos
    (add_pos_of_pos_of_nonneg harrival_pos (zero_le _))

theorem uniformizedArrivalMark_true_mass_ne_zero_of_rates_pos
    {arrivalRate serviceRate : ℝ≥0}
    (harrival_pos : 0 < arrivalRate) (hservice_pos : 0 < serviceRate) :
    (uniformizationArrivalMark
      (uniformizedBirthProbability
        (mm1TrafficIntensityNN arrivalRate serviceRate))
      (uniformizedBirthProbability_le_one _)).toMeasure {true} ≠ 0 := by
  exact uniformizationArrivalMark_true_mass_ne_zero_of_rho_pos
    (mm1TrafficIntensityNN_pos harrival_pos hservice_pos)

theorem uniformizedArrivalMark_true_mass_rate
    {arrivalRate serviceRate : ℝ≥0}
    (hservice_pos : 0 < serviceRate) :
    (uniformizationArrivalMark
      (uniformizedBirthProbability
        (mm1TrafficIntensityNN arrivalRate serviceRate))
      (uniformizedBirthProbability_le_one _)).toMeasure {true} =
      (arrivalRate / (arrivalRate + serviceRate) : ℝ≥0) := by
  rw [uniformizationArrivalMark_true_mass]
  rw [uniformizedBirthProbability_eq_rate_fraction hservice_pos]

theorem uniformizedArrivalMark_true_mass_ofReal_rate
    {arrivalRate serviceRate : ℝ≥0} :
    (uniformizationArrivalMark
      (uniformizedBirthProbability
        (mm1TrafficIntensityNN arrivalRate serviceRate))
      (uniformizedBirthProbability_le_one _)).toMeasure {true} =
      ENNReal.ofReal
        (uniformizedBirthProbability
          (mm1TrafficIntensityNN arrivalRate serviceRate) : ℝ) := by
  exact uniformizationArrivalMark_true_mass_ofReal
      (uniformizedBirthProbability
        (mm1TrafficIntensityNN arrivalRate serviceRate))
      (uniformizedBirthProbability_le_one _)

theorem uniformizedArrivalMark_true_mass_ne_zero_rate
    {arrivalRate serviceRate : ℝ≥0}
    (harrival_pos : 0 < arrivalRate) (hstable : arrivalRate < serviceRate) :
    (uniformizationArrivalMark
      (uniformizedBirthProbability
        (mm1TrafficIntensityNN arrivalRate serviceRate))
      (uniformizedBirthProbability_le_one _)).toMeasure {true} ≠ 0 := by
  exact uniformizedArrivalMark_true_mass_ne_zero_of_rates_pos
    harrival_pos (lt_trans harrival_pos hstable)

theorem total_uniformized_rate_mul_birthProbability_real
    {arrivalRate serviceRate : ℝ≥0} (hservice_pos : 0 < serviceRate) :
    ((arrivalRate + serviceRate : ℝ≥0) : ℝ) *
      (uniformizedBirthProbability
        (mm1TrafficIntensityNN arrivalRate serviceRate) : ℝ) =
      (arrivalRate : ℝ) := by
  exact_mod_cast
    total_uniformized_rate_mul_birthProbability hservice_pos

theorem total_uniformized_rate_mul_birthProbability_ennreal
    {arrivalRate serviceRate : ℝ≥0} (hservice_pos : 0 < serviceRate) :
    ENNReal.ofReal
      (((arrivalRate + serviceRate : ℝ≥0) : ℝ) *
        (uniformizedBirthProbability
          (mm1TrafficIntensityNN arrivalRate serviceRate) : ℝ)) =
      ENNReal.ofReal (arrivalRate : ℝ) := by
  rw [total_uniformized_rate_mul_birthProbability_real hservice_pos]

theorem total_uniformized_rate_mul_true_mark_mass
    {arrivalRate serviceRate : ℝ≥0}
    (hservice_pos : 0 < serviceRate) :
    ENNReal.ofReal ((arrivalRate + serviceRate : ℝ≥0) : ℝ) *
      (uniformizationArrivalMark
        (uniformizedBirthProbability
          (mm1TrafficIntensityNN arrivalRate serviceRate))
        (uniformizedBirthProbability_le_one _)).toMeasure {true} =
      ENNReal.ofReal (arrivalRate : ℝ) := by
  rw [uniformizationArrivalMark_true_mass]
  simp only [ENNReal.ofReal_coe_nnreal]
  exact_mod_cast
    total_uniformized_rate_mul_birthProbability hservice_pos

/-- The joint law of a mark and the deterministic next state from a fixed
pretransition queue length. -/
def markedUniformizationStep (p : ℝ≥0) (hp : p ≤ 1) (q : ℕ) : PMF (Bool × ℕ) :=
  (uniformizationArrivalMark p hp).map
    (fun mark => (mark, reflectedBirthDeathUpdate q mark))

/-- Forgetting the mark in the marked step gives exactly the existing reflected
birth--death transition PMF. -/
theorem markedUniformizationStep_map_snd
    (p : ℝ≥0) (hp : p ≤ 1) (q : ℕ) :
    (markedUniformizationStep p hp q).map Prod.snd =
      reflectedBirthDeathKernel p hp q := by
  rw [markedUniformizationStep, PMF.map_comp]
  change (uniformizationArrivalMark p hp).map
      (fun mark => reflectedBirthDeathUpdate q mark) = _
  rfl

/-- Forgetting the next state leaves the original Bernoulli mark PMF. -/
theorem markedUniformizationStep_map_fst
    (p : ℝ≥0) (hp : p ≤ 1) (q : ℕ) :
    (markedUniformizationStep p hp q).map Prod.fst =
      uniformizationArrivalMark p hp := by
  rw [markedUniformizationStep, PMF.map_comp]
  simpa using (PMF.map_id (uniformizationArrivalMark p hp))

/-- Recovering the mark from the next-state coordinate of the marked step
also leaves the Bernoulli mark law. -/
theorem markedUniformizationStep_map_recoveredMark
    (p : ℝ≥0) (hp : p ≤ 1) (q : ℕ) :
    (markedUniformizationStep p hp q).map
      (fun z => isArrivalEdge q z.2) = uniformizationArrivalMark p hp := by
  rw [markedUniformizationStep, PMF.map_comp]
  simpa [Function.comp_def] using (PMF.map_id (uniformizationArrivalMark p hp))

/-- The fixed-state marked step has the stated exact PMF. -/
theorem markedUniformizationStep_apply
    (p : ℝ≥0) (hp : p ≤ 1) (q : ℕ) (mark : Bool) (q' : ℕ) :
    markedUniformizationStep p hp q (mark, q') =
      if q' = reflectedBirthDeathUpdate q mark then
        uniformizationArrivalMark p hp mark
      else 0 := by
  rw [markedUniformizationStep, PMF.map_apply]
  cases mark <;> simp [reflectedBirthDeathUpdate]

/-- Canonical one-step `HasLaw` statement: sampling a Bernoulli mark and
applying the deterministic reflected update has the marked-step PMF. -/
theorem markedUniformizationStep_hasLaw
    (p : ℝ≥0) (hp : p ≤ 1) (q : ℕ) :
    HasLaw (fun mark => (mark, reflectedBirthDeathUpdate q mark))
      (markedUniformizationStep p hp q).toMeasure
      (uniformizationArrivalMark p hp).toMeasure := by
  refine ⟨(measurable_of_countable _).aemeasurable, ?_⟩
  exact PMF.toMeasure_map (fun mark => (mark, reflectedBirthDeathUpdate q mark))
    (uniformizationArrivalMark p hp)
    (measurable_of_countable _)

/-- At every fixed pretransition state, recovering the mark from the reflected
next-state edge has exactly the Bernoulli mark law. -/
theorem map_isArrivalEdge_reflectedBirthDeathKernel
    (p : ℝ≥0) (hp : p ≤ 1) (q : ℕ) :
    Measure.map (isArrivalEdge q) (reflectedBirthDeathKernel p hp q).toMeasure =
      (uniformizationArrivalMark p hp).toMeasure := by
  rw [PMF.toMeasure_map (isArrivalEdge q) (reflectedBirthDeathKernel p hp q)
    (measurable_of_countable _)]
  change (((PMF.bernoulli p hp).map
      (fun mark => reflectedBirthDeathUpdate q mark)).map
      (isArrivalEdge q)).toMeasure = (uniformizationArrivalMark p hp).toMeasure
  rw [PMF.map_comp]
  change ((PMF.bernoulli p hp).map
      (fun mark => isArrivalEdge q (reflectedBirthDeathUpdate q mark))).toMeasure = _
  simpa [uniformizationArrivalMark] using
    congrArg PMF.toMeasure (PMF.map_id (PMF.bernoulli p hp))

/-- Keep the pretransition state while recovering the arrival mark from its
unmarked successor. -/
def markedEdgeProjection : ℕ × ℕ → ℕ × Bool :=
  fun z => (z.1, isArrivalEdge z.1 z.2)

theorem measurable_markedEdgeProjection : Measurable markedEdgeProjection :=
  measurable_of_countable _

theorem markedEdgeProjection_preimage_singleton (q : ℕ) (mark : Bool) :
    markedEdgeProjection ⁻¹' ({(q, mark)} : Set (ℕ × Bool)) =
      {q} ×ˢ (isArrivalEdge q ⁻¹' {mark}) := by
  ext z
  rcases z with ⟨a, b⟩
  by_cases ha : a = q
  · subst a
    simp [markedEdgeProjection]
  · simp [markedEdgeProjection, ha]

/-- Under any s-finite pretransition law, the transition-pair pushforward
which records whether the edge is an arrival is exactly the product of that
state law and the Bernoulli mark law. -/
theorem map_markedEdgeProjection_compProd_reflectedBirthDeathKernel
    (μ : Measure ℕ) [SFinite μ] (p : ℝ≥0) (hp : p ≤ 1) :
    Measure.map markedEdgeProjection
      (μ ⊗ₘ countablePMFKernel (reflectedBirthDeathKernel p hp)) =
      μ.prod (uniformizationArrivalMark p hp).toMeasure := by
  let K : Kernel ℕ ℕ :=
    countablePMFKernel (reflectedBirthDeathKernel p hp)
  letI : IsMarkovKernel K := by
    dsimp [K]
    infer_instance
  apply Measure.ext_of_singleton
  rintro ⟨q, mark⟩
  have hmark : MeasurableSet (isArrivalEdge q ⁻¹' ({mark} : Set Bool)) :=
    (measurable_of_countable _) (measurableSet_singleton _)
  have hlocal : K q (isArrivalEdge q ⁻¹' ({mark} : Set Bool)) =
      (uniformizationArrivalMark p hp).toMeasure {mark} := by
    rw [← Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _),
      show K q = (reflectedBirthDeathKernel p hp q).toMeasure by rfl,
      map_isArrivalEdge_reflectedBirthDeathKernel p hp q]
  calc
    Measure.map markedEdgeProjection (μ ⊗ₘ K) {(q, mark)} =
        (μ ⊗ₘ K) ({q} ×ˢ (isArrivalEdge q ⁻¹' {mark})) := by
          rw [Measure.map_apply measurable_markedEdgeProjection
            (measurableSet_singleton _), markedEdgeProjection_preimage_singleton]
    _ = ∫⁻ x in {q}, K x (isArrivalEdge q ⁻¹' {mark}) ∂μ := by
          rw [Measure.compProd_apply_prod (measurableSet_singleton _) hmark]
    _ = K q (isArrivalEdge q ⁻¹' {mark}) * μ {q} := by
          rw [MeasureTheory.lintegral_singleton]
    _ = μ {q} * (uniformizationArrivalMark p hp).toMeasure {mark} := by
          rw [hlocal, mul_comm]
    _ = (μ.prod (uniformizationArrivalMark p hp).toMeasure) {(q, mark)} := by
          rw [← Set.singleton_prod_singleton, Measure.prod_prod]

/-- On an invariant embedded trajectory, the pretransition state and the
arrival-versus-potential-service mark recovered from a consecutive edge have
the independent product law. This is a one-edge statement only. -/
theorem stationaryTrajMeasure_consecutivePair_isArrivalEdge_hasLaw
    {π : Measure ℕ} [IsProbabilityMeasure π]
    (p : ℝ≥0) (hp : p ≤ 1)
    (hstationary : Kernel.Invariant
      (countablePMFKernel (reflectedBirthDeathKernel p hp)) π)
    (n : ℕ) :
    HasLaw
      (fun x : ℕ → ℕ => (x n, isArrivalEdge (x n) (x (n + 1))))
      (π.prod (uniformizationArrivalMark p hp).toMeasure)
      (stationaryTrajMeasure π
        (countablePMFKernel (reflectedBirthDeathKernel p hp))) := by
  have hpair : Measurable (fun x : ℕ → ℕ => (x n, x (n + 1))) :=
    (measurable_pi_apply _).prodMk (measurable_pi_apply _)
  refine ⟨(measurable_markedEdgeProjection.comp hpair).aemeasurable, ?_⟩
  calc
    Measure.map
        (fun x : ℕ → ℕ => (x n, isArrivalEdge (x n) (x (n + 1))))
        (stationaryTrajMeasure π
          (countablePMFKernel (reflectedBirthDeathKernel p hp))) =
        Measure.map markedEdgeProjection
          (Measure.map (fun x : ℕ → ℕ => (x n, x (n + 1)))
            (stationaryTrajMeasure π
              (countablePMFKernel (reflectedBirthDeathKernel p hp)))) := by
          symm
          rw [Measure.map_map measurable_markedEdgeProjection hpair]
          rfl
    _ = Measure.map markedEdgeProjection
          (π ⊗ₘ countablePMFKernel (reflectedBirthDeathKernel p hp)) := by
          rw [stationaryTrajMeasure_consecutivePair hstationary n]
    _ = π.prod (uniformizationArrivalMark p hp).toMeasure :=
          map_markedEdgeProjection_compProd_reflectedBirthDeathKernel π p hp

/-- Stable uniformized M/M/1 specialization of the one-edge state/mark
product law. The mark is recovered from an embedded transition, not from a
continuous-time arrival or service clock. -/
theorem geoNNPMF_uniformized_stationaryTraj_consecutivePair_isArrivalEdge_hasLaw
    (rho : ℝ≥0) (hrho : rho < 1) (n : ℕ) :
    HasLaw
      (fun x : ℕ → ℕ => (x n, isArrivalEdge (x n) (x (n + 1))))
      ((geoNNPMF rho hrho).toMeasure.prod
        (uniformizationArrivalMark (uniformizedBirthProbability rho)
          (uniformizedBirthProbability_le_one rho)).toMeasure)
      (stationaryTrajMeasure (geoNNPMF rho hrho).toMeasure
        (countablePMFKernel
          (reflectedBirthDeathKernel (uniformizedBirthProbability rho)
            (uniformizedBirthProbability_le_one rho)))) := by
  exact stationaryTrajMeasure_consecutivePair_isArrivalEdge_hasLaw
    (uniformizedBirthProbability rho)
    (uniformizedBirthProbability_le_one rho)
    (geoNNPMF_uniformized_kernelInvariant rho hrho) n

/-- Equality form of the stable stationary transition-pair pushforward. -/
theorem geoNNPMF_uniformized_stationaryTraj_consecutivePair_isArrivalEdge_map_eq
    (rho : ℝ≥0) (hrho : rho < 1) (n : ℕ) :
    Measure.map
      (fun x : ℕ → ℕ => (x n, isArrivalEdge (x n) (x (n + 1))))
      (stationaryTrajMeasure (geoNNPMF rho hrho).toMeasure
        (countablePMFKernel
          (reflectedBirthDeathKernel (uniformizedBirthProbability rho)
            (uniformizedBirthProbability_le_one rho)))) =
      (geoNNPMF rho hrho).toMeasure.prod
        (uniformizationArrivalMark (uniformizedBirthProbability rho)
          (uniformizedBirthProbability_le_one rho)).toMeasure :=
  (geoNNPMF_uniformized_stationaryTraj_consecutivePair_isArrivalEdge_hasLaw
    rho hrho n).map_eq

/-- A product state/mark law factors the embedded event that the pre-edge
state exceeds a threshold and the recovered mark is an arrival. -/
theorem measure_preState_ge_and_arrivalMark_eq_of_hasLaw
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {π : Measure ℕ} {B : Measure Bool} [SFinite B]
    {stateMark : Ω → ℕ × Bool}
    (H : HasLaw stateMark (π.prod B) P) (k : ℕ) :
    P {ω | k ≤ (stateMark ω).1 ∧ (stateMark ω).2 = true} =
      B {true} * π {q | k ≤ q} := by
  let A : Set ℕ := {q | k ≤ q}
  let T : Set (ℕ × Bool) := A ×ˢ ({true} : Set Bool)
  have hT : MeasurableSet T :=
    measurableSet_Ici.prod (measurableSet_singleton _)
  have hpre : stateMark ⁻¹' T =
      {ω | k ≤ (stateMark ω).1 ∧ (stateMark ω).2 = true} := by
    ext ω
    simp [T, A]
  calc
    P {ω | k ≤ (stateMark ω).1 ∧ (stateMark ω).2 = true} =
        P (stateMark ⁻¹' T) := by rw [hpre]
    _ = Measure.map stateMark P T := by
      rw [Measure.map_apply_of_aemeasurable H.aemeasurable hT]
    _ = (π.prod B) T := by rw [H.map_eq]
    _ = B {true} * π A := by
      rw [show T = A ×ˢ ({true} : Set Bool) by rfl, Measure.prod_prod, mul_comm]

/-- Conditioning a product state/mark law on a `true` mark leaves the state
tail unchanged. This is an embedded-event conditional statement; it becomes a
Palm/PASTA conclusion only after a marked Campbell construction identifies the
conditioned law with a genuine tagged-arrival law. -/
theorem cond_measure_preState_ge_eq_of_hasLaw
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {π : Measure ℕ} {B : Measure Bool}
    [IsProbabilityMeasure P] [IsProbabilityMeasure π] [IsProbabilityMeasure B]
    {stateMark : Ω → ℕ × Bool}
    (hstateMark : Measurable stateMark)
    (H : HasLaw stateMark (π.prod B) P)
    (htrue : B {true} ≠ 0) (k : ℕ) :
    (P[| {ω | (stateMark ω).2 = true}])
        {ω | k ≤ (stateMark ω).1} =
      π {q | k ≤ q} := by
  let E : Set Ω := {ω | (stateMark ω).2 = true}
  let A : Set Ω := {ω | k ≤ (stateMark ω).1}
  have hE : MeasurableSet E := by
    exact (measurableSet_singleton _).preimage
      (measurable_snd.comp hstateMark)
  have hPE : P E = B {true} := by
    simpa [E] using
      (measure_preState_ge_and_arrivalMark_eq_of_hasLaw H 0)
  have hPEA : P (E ∩ A) = B {true} * π {q | k ≤ q} := by
    simpa [E, A, and_comm, and_left_comm, and_assoc] using
      (measure_preState_ge_and_arrivalMark_eq_of_hasLaw H k)
  change P[A | E] = _
  rw [cond_apply hE P A, hPE, hPEA, ← mul_assoc,
    ENNReal.inv_mul_cancel htrue (measure_ne_top B {true}), one_mul]

/-- Conditioning a product state/mark law on a `true` mark preserves the
entire state law, not only its tails. As above, this is an embedded-event
conditional fact and needs a marked Campbell construction before it carries
Palm/PASTA provenance. -/
theorem cond_state_hasLaw_of_stateMark_product
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {π : Measure ℕ} {B : Measure Bool}
    [IsProbabilityMeasure P] [IsProbabilityMeasure π] [IsProbabilityMeasure B]
    {stateMark : Ω → ℕ × Bool}
    (hstateMark : Measurable stateMark)
    (H : HasLaw stateMark (π.prod B) P)
    (htrue : B {true} ≠ 0) :
    HasLaw (fun ω => (stateMark ω).1) π
      (P[| {ω | (stateMark ω).2 = true}]) := by
  let E : Set Ω := {ω | (stateMark ω).2 = true}
  have hE : MeasurableSet E := by
    exact (measurableSet_singleton _).preimage
      (measurable_snd.comp hstateMark)
  have hPE : P E = B {true} := by
    simpa [E] using
      (measure_preState_ge_and_arrivalMark_eq_of_hasLaw H 0)
  have hstate : Measurable (fun ω => (stateMark ω).1) :=
    measurable_fst.comp hstateMark
  refine ⟨hstate.aemeasurable, ?_⟩
  apply Measure.ext_of_singleton
  intro q
  let Q : Set Ω := {ω | (stateMark ω).1 = q}
  have hPEQ : P (E ∩ Q) = B {true} * π {q} := by
    let T : Set (ℕ × Bool) := ({q} : Set ℕ) ×ˢ ({true} : Set Bool)
    have hT : MeasurableSet T :=
      (measurableSet_singleton _).prod (measurableSet_singleton _)
    have hpre : stateMark ⁻¹' T = E ∩ Q := by
      ext ω
      rcases hsm : stateMark ω with ⟨a, b⟩
      simp [hsm, E, Q, T, and_comm]
    calc
      P (E ∩ Q) = P (stateMark ⁻¹' T) := by rw [hpre]
      _ = Measure.map stateMark P T := by
        rw [Measure.map_apply_of_aemeasurable H.aemeasurable hT]
      _ = (π.prod B) T := by rw [H.map_eq]
      _ = B {true} * π {q} := by
        rw [show T = ({q} : Set ℕ) ×ˢ ({true} : Set Bool) by rfl,
          Measure.prod_prod, mul_comm]
  rw [Measure.map_apply hstate (measurableSet_singleton _)]
  change P[Q | E] = π {q}
  rw [cond_apply hE P Q, hPE, hPEQ, ← mul_assoc,
    ENNReal.inv_mul_cancel htrue (measure_ne_top B {true}), one_mul]

/-- In the stable uniformized M/M/1 embedded chain, a queue-length tail event
and the recovered next-edge arrival mark factor exactly.  This is an
embedded-event precursor to PASTA, not a continuous-time arrival Palm law. -/
theorem measure_geoNNPMF_uniformized_stationaryTraj_preState_ge_and_isArrivalEdge
    (rho : ℝ≥0) (hrho : rho < 1) (n k : ℕ) :
    (stationaryTrajMeasure (geoNNPMF rho hrho).toMeasure
      (countablePMFKernel
        (reflectedBirthDeathKernel (uniformizedBirthProbability rho)
          (uniformizedBirthProbability_le_one rho))))
      {x | k ≤ x n ∧ isArrivalEdge (x n) (x (n + 1)) = true} =
      (uniformizationArrivalMark (uniformizedBirthProbability rho)
        (uniformizedBirthProbability_le_one rho)).toMeasure {true} *
        (geoNNPMF rho hrho).toMeasure {q | k ≤ q} := by
  exact measure_preState_ge_and_arrivalMark_eq_of_hasLaw
    (geoNNPMF_uniformized_stationaryTraj_consecutivePair_isArrivalEdge_hasLaw
      rho hrho n) k

end

end AppliedModelingLib.Probability.Queueing
