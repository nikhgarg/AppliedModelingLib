import GN21DriverSurgePricing.MainTheorems
import AppliedModelingLib.Foundations.Probability.ExponentialInterarrival
import Mathlib.Probability.Independence.InfinitePi

/-!
# Explicit raw renewal-cycle seeds for GN21

This module removes the IID-law fields from the immediate proof boundary for
GN21 Lemmas 1 and 3.  A raw seed contains four independent exponential
interarrival streams (the two state-conditioned arrival clocks and the two
state-switch clocks) and two independent IID trip-mark streams.  An outer
countable product independently supplies one such seed for every proposed
larger renewal cycle.

This is deliberately not a claim that a global calendar-time source process
has already been decomposed into renewal cycles.  The still-open mathematical
work is explicit in the two constructors below: a measurable observable must
be shown to implement the source cycle semantics, be integrable, and have the
displayed cycle mean.  Once those obligations are proved, IID and
identically-distributed conclusions follow from the literal product model,
rather than being supplied in a certificate or record.
-/

namespace GN21DriverSurgePricing

open MeasureTheory
open ProbabilityTheory
open scoped ProbabilityTheory ENNReal

noncomputable section

/-- Raw potential inputs for one proposed larger GN21 renewal cycle. -/
abbrev GN21RawCycleSeed :=
  Prod (Fin 4 -> (Nat -> Real)) (Fin 2 -> (Nat -> TripLength))

/-- The four raw clock rates, ordered as arrival `I`, arrival `J`, switch
`I -> J`, and switch `J -> I`. -/
def gn21CycleClockRate
    (arrivalI arrivalJ switchIJ switchJI : Real) : Fin 4 -> Real
  | 0 => arrivalI
  | 1 => arrivalJ
  | 2 => switchIJ
  | 3 => switchJI

/-- The state-indexed source trip-mark laws. -/
def gn21CycleMarkLaw (muI muJ : Measure TripLength) : Fin 2 -> Measure TripLength
  | 0 => muI
  | 1 => muJ

/--
The literal product law for one raw cycle seed.  Its first coordinate consists
of four independent canonical exponential interarrival paths; its second
coordinate consists of two independent IID trip-mark paths.
-/
def gn21RawCycleSeedMeasure
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real) : Measure GN21RawCycleSeed :=
  (Measure.infinitePi fun clock : Fin 4 =>
    AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
      (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI clock)).prod
  (Measure.infinitePi fun state : Fin 2 =>
    Measure.infinitePi fun _ : Nat => gn21CycleMarkLaw muI muJ state)

/-- The `n`th raw exponential clock gap of a cycle, indexed by source role. -/
def gn21RawCycleClock (clock : Fin 4) (n : Nat) : GN21RawCycleSeed -> Real :=
  fun seed => seed.1 clock n

/-- The `n`th raw trip-length mark of a cycle, indexed by starting state. -/
def gn21RawCycleMark (state : Fin 2) (n : Nat) : GN21RawCycleSeed -> TripLength :=
  fun seed => seed.2 state n

/-- The source law of a trip conditional on its length being accepted. -/
def gn21AcceptedTripLaw (mu : Measure TripLength) (sigma : TripPolicy) :
    Measure TripLength :=
  ProbabilityTheory.cond mu sigma

/-- A positive-mass accepted-trip restriction is a probability law. -/
theorem gn21AcceptedTripLaw_isProbability
    (mu : Measure TripLength) (sigma : TripPolicy)
    [IsProbabilityMeasure mu]
    (hmass : 0 < singleStateTripMass mu sigma) :
    IsProbabilityMeasure (gn21AcceptedTripLaw mu sigma) := by
  apply ProbabilityTheory.cond_isProbabilityMeasure_of_finite
  · intro hzero
    have hmass_zero : singleStateTripMass mu sigma = 0 := by
      simp [singleStateTripMass, hzero]
    linarith
  · exact measure_ne_top _ _

/--
Every real accepted-trip expectation is its source set integral divided by the
accepted mass.  This is the conditional-mark calculation needed after a
marked-arrival thinning construction; it does not itself claim that thinning.
-/
theorem gn21AcceptedTripLaw_integral_eq_setIntegral_div
    (mu : Measure TripLength) (sigma : TripPolicy)
    [IsProbabilityMeasure mu]
    (hmass : 0 < singleStateTripMass mu sigma)
    (f : TripLength -> Real) :
    (∫ tau, f tau ∂gn21AcceptedTripLaw mu sigma) =
      (∫ tau in sigma, f tau ∂mu) / singleStateTripMass mu sigma := by
  have hmass_ne : (mu sigma).toReal ≠ 0 := by
    exact ne_of_gt (by simpa [singleStateTripMass] using hmass)
  unfold gn21AcceptedTripLaw ProbabilityTheory.cond
  rw [integral_smul_measure]
  rw [ENNReal.toReal_inv]
  unfold singleStateTripMass
  change (mu sigma).toReal⁻¹ * (∫ tau in sigma, f tau ∂mu) =
    (∫ tau in sigma, f tau ∂mu) / (mu sigma).toReal
  field_simp

/-- The conditional accepted-trip mean length is the paper's mean-length term. -/
theorem gn21AcceptedTripLaw_integral_id
    (mu : Measure TripLength) (sigma : TripPolicy)
    [IsProbabilityMeasure mu]
    (hmass : 0 < singleStateTripMass mu sigma) :
    (∫ tau, tau ∂gn21AcceptedTripLaw mu sigma) =
      singleStateTripTime mu sigma / singleStateTripMass mu sigma := by
  simpa [singleStateTripTime] using
    gn21AcceptedTripLaw_integral_eq_setIntegral_div mu sigma hmass
      (fun tau : TripLength => tau)

/-- The conditional accepted-trip mean payment is the paper's `W_i` term. -/
theorem gn21AcceptedTripLaw_integral_payment
    (mu : Measure TripLength) (w : PricingFunction) (sigma : TripPolicy)
    [IsProbabilityMeasure mu]
    (hmass : 0 < singleStateTripMass mu sigma) :
    (∫ tau, w tau ∂gn21AcceptedTripLaw mu sigma) =
      singleStateTripPayment mu w sigma / singleStateTripMass mu sigma := by
  simpa [singleStateTripPayment] using
    gn21AcceptedTripLaw_integral_eq_setIntegral_div mu sigma hmass w

/--
The conditional chance of being in the opposite state at accepted-trip
completion is the normalized switch-probability set integral.
-/
theorem gn21AcceptedTripLaw_integral_switchProb
    (mu : Measure TripLength) (sigma : TripPolicy)
    (switchIJ switchJI : Real)
    [IsProbabilityMeasure mu]
    (hmass : 0 < singleStateTripMass mu sigma) :
    (∫ tau, gn21SwitchProb switchIJ switchJI tau
      ∂gn21AcceptedTripLaw mu sigma) =
      (∫ tau in sigma, gn21SwitchProb switchIJ switchJI tau ∂mu) /
        singleStateTripMass mu sigma := by
  exact gn21AcceptedTripLaw_integral_eq_setIntegral_div mu sigma hmass
    (gn21SwitchProb switchIJ switchJI)

/-- The raw seed law is a probability measure when the source rates are
positive and both source trip laws are probability measures. -/
theorem isProbabilityMeasure_gn21RawCycleSeedMeasure
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI) :
    IsProbabilityMeasure
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  let clockRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
  have hclockRate : forall clock : Fin 4, 0 < clockRate clock := by
    intro clock
    fin_cases clock <;> simp [clockRate, gn21CycleClockRate, harrivalI,
      harrivalJ, hswitchIJ, hswitchJI]
  letI : forall clock : Fin 4, IsProbabilityMeasure
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
        (clockRate clock)) := fun clock =>
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      (hclockRate clock)
  letI : IsProbabilityMeasure
      (Measure.infinitePi fun clock : Fin 4 =>
        AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
          (clockRate clock)) := inferInstance
  let markLaw := gn21CycleMarkLaw muI muJ
  letI : forall state : Fin 2, IsProbabilityMeasure (markLaw state) := by
    intro state
    fin_cases state <;> simp only [markLaw, gn21CycleMarkLaw]
    all_goals infer_instance
  letI : forall state : Fin 2, IsProbabilityMeasure
      (Measure.infinitePi fun _ : Nat => markLaw state) := fun state => inferInstance
  letI : IsProbabilityMeasure
      (Measure.infinitePi fun state : Fin 2 =>
        Measure.infinitePi fun _ : Nat => markLaw state) := inferInstance
  change IsProbabilityMeasure
    ((Measure.infinitePi fun clock : Fin 4 =>
      AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
        (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI clock)).prod
    (Measure.infinitePi fun state : Fin 2 =>
      Measure.infinitePi fun _ : Nat => gn21CycleMarkLaw muI muJ state))
  simpa only [clockRate, markLaw] using
    (inferInstance : IsProbabilityMeasure
      ((Measure.infinitePi fun clock : Fin 4 =>
        AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
          (clockRate clock)).prod
      (Measure.infinitePi fun state : Fin 2 =>
        Measure.infinitePi fun _ : Nat => markLaw state)))

/-- Every raw clock coordinate has the exact prescribed exponential law. -/
theorem gn21RawCycleClock_hasLaw
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (clock : Fin 4) (n : Nat) :
    HasLaw (gn21RawCycleClock clock n)
      (ProbabilityTheory.expMeasure
        (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI clock))
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  let clockRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
  have hclockRate : forall c : Fin 4, 0 < clockRate c := by
    intro c
    fin_cases c <;> simp [clockRate, gn21CycleClockRate, harrivalI,
      harrivalJ, hswitchIJ, hswitchJI]
  let clockMeasure : Measure (Fin 4 -> Nat -> Real) :=
    Measure.infinitePi fun c : Fin 4 =>
      AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
        (clockRate c)
  letI : forall c : Fin 4, IsProbabilityMeasure
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
        (clockRate c)) := fun c =>
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      (hclockRate c)
  letI : IsProbabilityMeasure clockMeasure := by
    dsimp [clockMeasure]
    infer_instance
  let markLaw := gn21CycleMarkLaw muI muJ
  let markMeasure : Measure (Fin 2 -> Nat -> TripLength) :=
    Measure.infinitePi fun state : Fin 2 =>
      Measure.infinitePi fun _ : Nat => markLaw state
  letI : forall state : Fin 2, IsProbabilityMeasure (markLaw state) := by
    intro state
    fin_cases state <;> simp only [markLaw, gn21CycleMarkLaw]
    all_goals infer_instance
  letI : forall state : Fin 2, IsProbabilityMeasure
      (Measure.infinitePi fun _ : Nat => markLaw state) := fun state => inferInstance
  letI : IsProbabilityMeasure markMeasure := by
    dsimp [markMeasure]
    infer_instance
  have hfst : HasLaw (Prod.fst : GN21RawCycleSeed -> Fin 4 -> Nat -> Real)
      clockMeasure (clockMeasure.prod markMeasure) := by
    refine ⟨measurable_fst.aemeasurable, ?_⟩
    rw [Measure.map_fst_prod]
    simp
  have hstream : HasLaw (Function.eval clock)
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
        (clockRate clock)) clockMeasure :=
    (measurePreserving_eval_infinitePi
      (fun c : Fin 4 =>
        AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
          (clockRate c)) clock).hasLaw
  have hclock : HasLaw (fun seed : GN21RawCycleSeed => seed.1 clock)
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
        (clockRate clock)) (clockMeasure.prod markMeasure) := by
    simpa only [Function.comp_apply] using hstream.comp hfst
  have hinterarrival :=
    AppliedModelingLib.Probability.PoissonProcess.interarrival_hasLaw (hclockRate clock) n
  change HasLaw (fun seed : GN21RawCycleSeed => seed.1 clock n)
    (ProbabilityTheory.expMeasure (clockRate clock))
    (clockMeasure.prod markMeasure)
  simpa only [Function.comp_apply] using hinterarrival.comp hclock

/-- Every raw trip-mark coordinate has the source state-conditioned mark law. -/
theorem gn21RawCycleMark_hasLaw
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (n : Nat) :
    HasLaw (gn21RawCycleMark state n) (gn21CycleMarkLaw muI muJ state)
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  let clockRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
  have hclockRate : forall c : Fin 4, 0 < clockRate c := by
    intro c
    fin_cases c <;> simp [clockRate, gn21CycleClockRate, harrivalI,
      harrivalJ, hswitchIJ, hswitchJI]
  let clockMeasure : Measure (Fin 4 -> Nat -> Real) :=
    Measure.infinitePi fun c : Fin 4 =>
      AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
        (clockRate c)
  letI : forall c : Fin 4, IsProbabilityMeasure
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
        (clockRate c)) := fun c =>
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      (hclockRate c)
  letI : IsProbabilityMeasure clockMeasure := by
    dsimp [clockMeasure]
    infer_instance
  let markLaw := gn21CycleMarkLaw muI muJ
  let markMeasure : Measure (Fin 2 -> Nat -> TripLength) :=
    Measure.infinitePi fun s : Fin 2 =>
      Measure.infinitePi fun _ : Nat => markLaw s
  letI : forall s : Fin 2, IsProbabilityMeasure (markLaw s) := by
    intro s
    fin_cases s <;> simp only [markLaw, gn21CycleMarkLaw]
    all_goals infer_instance
  letI : forall s : Fin 2, IsProbabilityMeasure
      (Measure.infinitePi fun _ : Nat => markLaw s) := fun s => inferInstance
  letI : IsProbabilityMeasure markMeasure := by
    dsimp [markMeasure]
    infer_instance
  have hsnd : HasLaw (Prod.snd : GN21RawCycleSeed -> Fin 2 -> Nat -> TripLength)
      markMeasure (clockMeasure.prod markMeasure) := by
    refine ⟨measurable_snd.aemeasurable, ?_⟩
    rw [Measure.map_snd_prod]
    simp
  have hstate : HasLaw (Function.eval state)
      (Measure.infinitePi fun _ : Nat => markLaw state) markMeasure :=
    (measurePreserving_eval_infinitePi
      (fun s : Fin 2 => Measure.infinitePi fun _ : Nat => markLaw s) state).hasLaw
  have hmarks : HasLaw (fun seed : GN21RawCycleSeed => seed.2 state)
      (Measure.infinitePi fun _ : Nat => markLaw state)
      (clockMeasure.prod markMeasure) := by
    simpa only [Function.comp_apply] using hstate.comp hsnd
  have hmark : HasLaw (Function.eval n) (markLaw state)
      (Measure.infinitePi fun _ : Nat => markLaw state) :=
    (measurePreserving_eval_infinitePi (fun _ : Nat => markLaw state) n).hasLaw
  change HasLaw (fun seed : GN21RawCycleSeed => seed.2 state n)
    (markLaw state) (clockMeasure.prod markMeasure)
  simpa only [Function.comp_apply] using hmark.comp hmarks

/-- Independent raw seeds for the successive proposed larger renewal cycles. -/
def gn21RawCycleSeedPathMeasure
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real) :
    Measure (Nat -> GN21RawCycleSeed) :=
  Measure.infinitePi fun _ : Nat =>
    gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI

/-- The `n`th raw renewal-cycle seed. -/
def gn21RawCycleSeedAt (n : Nat) : (Nat -> GN21RawCycleSeed) -> GN21RawCycleSeed :=
  fun omega => omega n

theorem measurable_gn21RawCycleSeedAt (n : Nat) :
    Measurable (gn21RawCycleSeedAt n) := by
  exact measurable_pi_apply n

theorem isProbabilityMeasure_gn21RawCycleSeedPathMeasure
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI) :
    IsProbabilityMeasure
      (gn21RawCycleSeedPathMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  letI : IsProbabilityMeasure
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) :=
    isProbabilityMeasure_gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ
      switchIJ switchJI harrivalI harrivalJ hswitchIJ hswitchJI
  change IsProbabilityMeasure
    (Measure.infinitePi fun _ : Nat =>
      gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI)
  infer_instance

theorem gn21RawCycleSeedAt_hasLaw
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (n : Nat) :
    HasLaw (gn21RawCycleSeedAt n)
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI)
      (gn21RawCycleSeedPathMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  let raw := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  letI : IsProbabilityMeasure raw :=
    isProbabilityMeasure_gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ
      switchIJ switchJI harrivalI harrivalJ hswitchIJ hswitchJI
  change HasLaw (Function.eval n) raw (Measure.infinitePi fun _ : Nat => raw)
  exact (measurePreserving_eval_infinitePi (fun _ : Nat => raw) n).hasLaw

theorem iIndepFun_gn21RawCycleSeedAt
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI) :
    iIndepFun gn21RawCycleSeedAt
      (gn21RawCycleSeedPathMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  let raw := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  letI : IsProbabilityMeasure raw :=
    isProbabilityMeasure_gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ
      switchIJ switchJI harrivalI harrivalJ hswitchIJ hswitchJI
  change iIndepFun (fun n (omega : Nat -> GN21RawCycleSeed) => omega n)
    (Measure.infinitePi fun _ : Nat => raw)
  exact @ProbabilityTheory.iIndepFun_infinitePi Nat
    (fun _ : Nat => GN21RawCycleSeed) (fun _ => inferInstance)
    (fun _ : Nat => GN21RawCycleSeed) (fun _ => inferInstance)
    (fun _ : Nat => raw) (fun _ => inferInstance)
    (fun _ : Nat => id) (fun _ => measurable_id)

/-- A measurable statistic of independently drawn raw seeds is IID. -/
theorem iIndepFun_gn21CycleObservable
    {alpha : Type*} [MeasurableSpace alpha]
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (observable : GN21RawCycleSeed -> alpha)
    (hobservable : Measurable observable) :
    iIndepFun
      (fun n omega => observable (gn21RawCycleSeedAt n omega))
      (gn21RawCycleSeedPathMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  simpa only [Function.comp_apply] using
    (iIndepFun_gn21RawCycleSeedAt muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI).comp
      (fun _ : Nat => observable) (fun _ : Nat => hobservable)

theorem gn21CycleObservable_identDistrib
    {alpha : Type*} [MeasurableSpace alpha]
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (observable : GN21RawCycleSeed -> alpha)
    (hobservable : Measurable observable)
    (n : Nat) :
    IdentDistrib
      (fun omega => observable (gn21RawCycleSeedAt n omega))
      (fun omega => observable (gn21RawCycleSeedAt 0 omega))
      (gn21RawCycleSeedPathMeasure muI muJ arrivalI arrivalJ switchIJ switchJI)
      (gn21RawCycleSeedPathMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  simpa only [Function.comp_apply] using
    ((gn21RawCycleSeedAt_hasLaw muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI n).identDistrib
      (gn21RawCycleSeedAt_hasLaw muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI 0)).comp hobservable

theorem integrable_gn21CycleObservable
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (observable : GN21RawCycleSeed -> Real)
    (hobservable : Measurable observable)
    (hintegrable : Integrable observable
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI))
    (n : Nat) :
    Integrable (fun omega => observable (gn21RawCycleSeedAt n omega))
      (gn21RawCycleSeedPathMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  let raw := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  letI : IsProbabilityMeasure raw :=
    isProbabilityMeasure_gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ
      switchIJ switchJI harrivalI harrivalJ hswitchIJ hswitchJI
  have hpres : MeasurePreserving (Function.eval n)
      (Measure.infinitePi fun _ : Nat => raw) raw :=
    measurePreserving_eval_infinitePi (fun _ : Nat => raw) n
  change Integrable (Function.comp observable (Function.eval n))
    (Measure.infinitePi fun _ : Nat => raw)
  exact (hpres.integrable_comp hobservable.aestronglyMeasurable).mpr (by
    simpa only [raw] using hintegrable)

theorem integral_gn21CycleObservable_eq
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (observable : GN21RawCycleSeed -> Real)
    (hobservable : Measurable observable)
    (n : Nat) :
    (∫ omega, observable (gn21RawCycleSeedAt n omega)
      ∂gn21RawCycleSeedPathMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) =
      ∫ seed, observable seed
        ∂gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI := by
  have hmap : Measure.map (gn21RawCycleSeedAt n)
      (gn21RawCycleSeedPathMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) =
      gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI :=
    (gn21RawCycleSeedAt_hasLaw muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI n).map_eq
  have hmeas : AEStronglyMeasurable observable
      (Measure.map (gn21RawCycleSeedAt n)
        (gn21RawCycleSeedPathMeasure muI muJ arrivalI arrivalJ switchIJ switchJI)) := by
    rw [hmap]
    exact hobservable.aestronglyMeasurable
  calc
    (∫ omega, observable (gn21RawCycleSeedAt n omega)
      ∂gn21RawCycleSeedPathMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) =
        ∫ seed, observable seed ∂Measure.map (gn21RawCycleSeedAt n)
          (gn21RawCycleSeedPathMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
          exact (integral_map
            (μ := gn21RawCycleSeedPathMeasure muI muJ arrivalI arrivalJ switchIJ switchJI)
            (φ := gn21RawCycleSeedAt n) (f := observable)
            (measurable_gn21RawCycleSeedAt n).aemeasurable hmeas).symm
    _ = ∫ seed, observable seed
      ∂gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI := by
        rw [hmap]

/--
Construct the IID part of GN21 Lemma 3 directly from a product of source
arrival-clock, state-switch-clock, and trip-mark streams.  The caller still
has to prove that its two observables are the actual renewal-cycle state times
and establish their source mean identities; IID, identical-law, and transport
of integrability are derived here rather than carried as model fields.
-/
def gn21TimeFractionIIDCycleModel_of_rawCycleObservables
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    (sigmaI sigmaJ : TripPolicy)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (hsigmaI_measurable : MeasurableSet sigmaI)
    (hsigmaJ_measurable : MeasurableSet sigmaJ)
    (hsigmaI_subset : Set.Subset sigmaI acceptAllPolicy)
    (hsigmaJ_subset : Set.Subset sigmaJ acceptAllPolicy)
    (hmassI : 0 < singleStateTripMass muI sigmaI)
    (hmassJ : 0 < singleStateTripMass muJ sigmaJ)
    (stateTimeI stateTimeJ : GN21RawCycleSeed -> Real)
    (hstateTimeI_measurable : Measurable stateTimeI)
    (hstateTimeJ_measurable : Measurable stateTimeJ)
    (hstateTimeI_integrable : Integrable stateTimeI
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI))
    (hstateTimeJ_integrable : Integrable stateTimeJ
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI))
    (hstateTimeI_mean :
      (∫ seed, stateTimeI seed
        ∂gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) =
        gn21ExpectedStateTimeInRenewalCycle arrivalI
          (singleStateTripMass muI sigmaI) switchIJ
          (gn21StateCycleTime muI arrivalI sigmaI)
          (gn21ExitWeightIntegral muI arrivalI switchIJ switchJI sigmaI))
    (hstateTimeJ_mean :
      (∫ seed, stateTimeJ seed
        ∂gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) =
        gn21ExpectedStateTimeInRenewalCycle arrivalJ
          (singleStateTripMass muJ sigmaJ) switchJI
          (gn21StateCycleTime muJ arrivalJ sigmaJ)
          (gn21ExitWeightIntegral muJ arrivalJ switchJI switchIJ sigmaJ)) :
    GN21TimeFractionIIDCycleModel
      (gn21RawCycleSeedPathMeasure muI muJ arrivalI arrivalJ switchIJ switchJI)
      muI muJ arrivalI arrivalJ switchIJ switchJI sigmaI sigmaJ := by
  refine
    { stateTimeI := fun n omega => stateTimeI (gn21RawCycleSeedAt n omega)
      stateTimeJ := fun n omega => stateTimeJ (gn21RawCycleSeedAt n omega)
      arrivalI_pos := harrivalI
      arrivalJ_pos := harrivalJ
      switchIJ_pos := hswitchIJ
      switchJI_pos := hswitchJI
      σI_measurable := hsigmaI_measurable
      σJ_measurable := hsigmaJ_measurable
      σI_subset := hsigmaI_subset
      σJ_subset := hsigmaJ_subset
      massI_pos := hmassI
      massJ_pos := hmassJ
      stateTimeI_integrable := ?_
      stateTimeJ_integrable := ?_
      stateTimeI_independent := ?_
      stateTimeJ_independent := ?_
      stateTimeI_identDistrib := ?_
      stateTimeJ_identDistrib := ?_
      stateTimeI_mean_eq := ?_
      stateTimeJ_mean_eq := ?_ }
  · exact integrable_gn21CycleObservable muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI stateTimeI hstateTimeI_measurable
      hstateTimeI_integrable 0
  · exact integrable_gn21CycleObservable muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI stateTimeJ hstateTimeJ_measurable
      hstateTimeJ_integrable 0
  · intro n m hnm
    exact (iIndepFun_gn21CycleObservable muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI stateTimeI hstateTimeI_measurable).indepFun hnm
  · intro n m hnm
    exact (iIndepFun_gn21CycleObservable muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI stateTimeJ hstateTimeJ_measurable).indepFun hnm
  · intro n
    exact gn21CycleObservable_identDistrib muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI stateTimeI hstateTimeI_measurable n
  · intro n
    exact gn21CycleObservable_identDistrib muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI stateTimeJ hstateTimeJ_measurable n
  · calc
      (∫ omega, stateTimeI (gn21RawCycleSeedAt 0 omega)
        ∂gn21RawCycleSeedPathMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) =
          ∫ seed, stateTimeI seed
            ∂gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI :=
        integral_gn21CycleObservable_eq muI muJ arrivalI arrivalJ switchIJ switchJI
          harrivalI harrivalJ hswitchIJ hswitchJI stateTimeI hstateTimeI_measurable 0
      _ = _ := hstateTimeI_mean
  · calc
      (∫ omega, stateTimeJ (gn21RawCycleSeedAt 0 omega)
        ∂gn21RawCycleSeedPathMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) =
          ∫ seed, stateTimeJ seed
            ∂gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI :=
        integral_gn21CycleObservable_eq muI muJ arrivalI arrivalJ switchIJ switchJI
          harrivalI harrivalJ hswitchIJ hswitchJI stateTimeJ hstateTimeJ_measurable 0
      _ = _ := hstateTimeJ_mean

/--
The analogous direct constructor for GN21 Lemma 1.  All four cycle sequences
are deterministic measurable observables of one independently drawn raw
cycle seed; consequently the constructor proves their IID obligations.  It
deliberately retains only the mathematical work that has not yet been
constructed: the observable process semantics, integrability, and four
source mean calculations.
-/
def gn21DynamicIIDCycleModel_of_rawCycleObservables
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    (wI wJ : PricingFunction) (sigmaI sigmaJ : TripPolicy)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (hsigmaI_measurable : MeasurableSet sigmaI)
    (hsigmaJ_measurable : MeasurableSet sigmaJ)
    (hsigmaI_subset : Set.Subset sigmaI acceptAllPolicy)
    (hsigmaJ_subset : Set.Subset sigmaJ acceptAllPolicy)
    (hmassI : 0 < singleStateTripMass muI sigmaI)
    (hmassJ : 0 < singleStateTripMass muJ sigmaJ)
    (stateTimeI stateTimeJ stateEarningI stateEarningJ : GN21RawCycleSeed -> Real)
    (hstateTimeI_measurable : Measurable stateTimeI)
    (hstateTimeJ_measurable : Measurable stateTimeJ)
    (hstateEarningI_measurable : Measurable stateEarningI)
    (hstateEarningJ_measurable : Measurable stateEarningJ)
    (hstateTimeI_integrable : Integrable stateTimeI
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI))
    (hstateTimeJ_integrable : Integrable stateTimeJ
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI))
    (hstateEarningI_integrable : Integrable stateEarningI
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI))
    (hstateEarningJ_integrable : Integrable stateEarningJ
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI))
    (hstateTimeI_mean :
      (∫ seed, stateTimeI seed
        ∂gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) =
        gn21ExpectedStateTimeInRenewalCycle arrivalI
          (singleStateTripMass muI sigmaI) switchIJ
          (gn21StateCycleTime muI arrivalI sigmaI)
          (gn21ExitWeightIntegral muI arrivalI switchIJ switchJI sigmaI))
    (hstateTimeJ_mean :
      (∫ seed, stateTimeJ seed
        ∂gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) =
        gn21ExpectedStateTimeInRenewalCycle arrivalJ
          (singleStateTripMass muJ sigmaJ) switchJI
          (gn21StateCycleTime muJ arrivalJ sigmaJ)
          (gn21ExitWeightIntegral muJ arrivalJ switchJI switchIJ sigmaJ))
    (hstateEarningI_mean :
      (∫ seed, stateEarningI seed
        ∂gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) =
        gn21ExpectedStateEarningInRenewalCycle arrivalI
          (singleStateTripMass muI sigmaI) switchIJ
          (gn21StateMeanEarning muI wI sigmaI)
          (gn21ExitWeightIntegral muI arrivalI switchIJ switchJI sigmaI))
    (hstateEarningJ_mean :
      (∫ seed, stateEarningJ seed
        ∂gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) =
        gn21ExpectedStateEarningInRenewalCycle arrivalJ
          (singleStateTripMass muJ sigmaJ) switchJI
          (gn21StateMeanEarning muJ wJ sigmaJ)
          (gn21ExitWeightIntegral muJ arrivalJ switchJI switchIJ sigmaJ)) :
    GN21DynamicIIDCycleModel
      (gn21RawCycleSeedPathMeasure muI muJ arrivalI arrivalJ switchIJ switchJI)
      muI muJ arrivalI arrivalJ switchIJ switchJI wI wJ sigmaI sigmaJ := by
  let timeModel : GN21TimeFractionIIDCycleModel
      (gn21RawCycleSeedPathMeasure muI muJ arrivalI arrivalJ switchIJ switchJI)
      muI muJ arrivalI arrivalJ switchIJ switchJI sigmaI sigmaJ :=
    gn21TimeFractionIIDCycleModel_of_rawCycleObservables muI muJ
      arrivalI arrivalJ switchIJ switchJI sigmaI sigmaJ harrivalI harrivalJ
      hswitchIJ hswitchJI hsigmaI_measurable hsigmaJ_measurable hsigmaI_subset
      hsigmaJ_subset hmassI hmassJ stateTimeI stateTimeJ hstateTimeI_measurable
      hstateTimeJ_measurable hstateTimeI_integrable hstateTimeJ_integrable
      hstateTimeI_mean hstateTimeJ_mean
  refine
    { toGN21TimeFractionIIDCycleModel := timeModel
      stateEarningI := fun n omega => stateEarningI (gn21RawCycleSeedAt n omega)
      stateEarningJ := fun n omega => stateEarningJ (gn21RawCycleSeedAt n omega)
      stateEarningI_integrable := ?_
      stateEarningJ_integrable := ?_
      stateEarningI_independent := ?_
      stateEarningJ_independent := ?_
      stateEarningI_identDistrib := ?_
      stateEarningJ_identDistrib := ?_
      stateEarningI_mean_eq := ?_
      stateEarningJ_mean_eq := ?_ }
  · exact integrable_gn21CycleObservable muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI stateEarningI hstateEarningI_measurable
      hstateEarningI_integrable 0
  · exact integrable_gn21CycleObservable muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI stateEarningJ hstateEarningJ_measurable
      hstateEarningJ_integrable 0
  · intro n m hnm
    exact (iIndepFun_gn21CycleObservable muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI stateEarningI
      hstateEarningI_measurable).indepFun hnm
  · intro n m hnm
    exact (iIndepFun_gn21CycleObservable muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI stateEarningJ
      hstateEarningJ_measurable).indepFun hnm
  · intro n
    exact gn21CycleObservable_identDistrib muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI stateEarningI hstateEarningI_measurable n
  · intro n
    exact gn21CycleObservable_identDistrib muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI stateEarningJ hstateEarningJ_measurable n
  · calc
      (∫ omega, stateEarningI (gn21RawCycleSeedAt 0 omega)
        ∂gn21RawCycleSeedPathMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) =
          ∫ seed, stateEarningI seed
            ∂gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI :=
        integral_gn21CycleObservable_eq muI muJ arrivalI arrivalJ switchIJ switchJI
          harrivalI harrivalJ hswitchIJ hswitchJI stateEarningI
          hstateEarningI_measurable 0
      _ = _ := hstateEarningI_mean
  · calc
      (∫ omega, stateEarningJ (gn21RawCycleSeedAt 0 omega)
        ∂gn21RawCycleSeedPathMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) =
          ∫ seed, stateEarningJ seed
            ∂gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI :=
        integral_gn21CycleObservable_eq muI muJ arrivalI arrivalJ switchIJ switchJI
          harrivalI harrivalJ hswitchIJ hswitchJI stateEarningJ
          hstateEarningJ_measurable 0
      _ = _ := hstateEarningJ_mean

end
end GN21DriverSurgePricing
