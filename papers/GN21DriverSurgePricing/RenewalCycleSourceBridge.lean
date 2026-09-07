import GN21DriverSurgePricing.RenewalCycleSeeds
import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalNonexplosion
import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalRenewalCountMarginal
import AppliedModelingLib.Foundations.Probability.IndependentPairLaw
import AppliedModelingLib.Foundations.Probability.PoissonFiniteHorizonMarkedThinning

/-!
# Source-component bridge for GN21 renewal cycles

This module proves moment transport and deterministic-horizon marked-count
thinning for the literal product-space inputs used by `RenewalCycleSeeds`.
It intentionally stops before asserting an all-time marked point-process
thinning/restart theorem, a CTMC strong-Markov theorem at trip-completion
times, or the random-index Wald calculation for a larger cycle.  Those are the
remaining source-process obligations for GN21 Lemmas 1 and 3.
-/

namespace GN21DriverSurgePricing

open MeasureTheory
open ProbabilityTheory
open scoped ProbabilityTheory ENNReal NNReal

noncomputable section

/-- A raw clock coordinate in a GN21 cycle is integrable under the literal
four-clock/two-mark product law. -/
theorem integrable_gn21RawCycleClock
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (clock : Fin 4) (n : Nat) :
    Integrable (gn21RawCycleClock clock n)
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  let rate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI clock
  have hrate : 0 < rate := by
    fin_cases clock <;> simp [rate, gn21CycleClockRate, harrivalI, harrivalJ,
      hswitchIJ, hswitchJI]
  let M : AppliedModelingLib.Probability.Exponential.Model :=
    AppliedModelingLib.Probability.Exponential.Model.mk rate hrate
  have hExp : Integrable (fun x : Real => x) (ProbabilityTheory.expMeasure rate) := by
    simpa [AppliedModelingLib.Probability.Exponential.Model.measure, M] using M.integrable_id
  have hLaw := gn21RawCycleClock_hasLaw muI muJ arrivalI arrivalJ switchIJ switchJI
    harrivalI harrivalJ hswitchIJ hswitchJI clock n
  have hmap : Measure.map (gn21RawCycleClock clock n)
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) =
      ProbabilityTheory.expMeasure rate := by
    simpa [rate] using hLaw.map_eq
  have hmapInt : Integrable (fun x : Real => x)
      (Measure.map (gn21RawCycleClock clock n)
        (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI)) := by
    rw [hmap]
    exact hExp
  simpa [Function.comp_def] using
    (integrable_map_measure aestronglyMeasurable_id hLaw.aemeasurable).mp hmapInt

/-- The mean of every literal raw clock coordinate is the reciprocal of its
source rate. -/
theorem integral_gn21RawCycleClock_eq_inv_rate
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (clock : Fin 4) (n : Nat) :
    (∫ seed, gn21RawCycleClock clock n seed
      ∂gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) =
      1 / gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI clock := by
  let rate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI clock
  have hrate : 0 < rate := by
    fin_cases clock <;> simp [rate, gn21CycleClockRate, harrivalI, harrivalJ,
      hswitchIJ, hswitchJI]
  let M : AppliedModelingLib.Probability.Exponential.Model :=
    AppliedModelingLib.Probability.Exponential.Model.mk rate hrate
  have hLaw := gn21RawCycleClock_hasLaw muI muJ arrivalI arrivalJ switchIJ switchJI
    harrivalI harrivalJ hswitchIJ hswitchJI clock n
  calc
    (∫ seed, gn21RawCycleClock clock n seed
      ∂gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) =
        ∫ x, x ∂ProbabilityTheory.expMeasure rate := by
          simpa [rate] using hLaw.integral_eq
    _ = M.expectedMaxValue 1 := by
      simpa [AppliedModelingLib.Probability.Exponential.Model.measure, M] using
        M.integral_id_eq_expectedMaxValue_one
    _ = 1 / rate := by
      simp [AppliedModelingLib.Probability.Exponential.Model.expectedMaxValue,
        AppliedModelingLib.Probability.Exponential.expectedMaxValueOfRate_one, M]
    _ = 1 / gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI clock := by
      rfl

/-- Integrability of a source mark transports to every literal raw mark
coordinate.  This is used for trip-length, payout, and CTMC transition
probability observables before any stopping construction is introduced. -/
theorem integrable_gn21RawCycleMark_comp
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (n : Nat) (f : TripLength -> Real)
    (hintegrable : Integrable f (gn21CycleMarkLaw muI muJ state)) :
    Integrable (fun seed => f (gn21RawCycleMark state n seed))
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  have hLaw := gn21RawCycleMark_hasLaw muI muJ arrivalI arrivalJ switchIJ switchJI
    harrivalI harrivalJ hswitchIJ hswitchJI state n
  have hmapInt : Integrable f
      (Measure.map (gn21RawCycleMark state n)
        (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI)) := by
    rw [hLaw.map_eq]
    exact hintegrable
  have hfmap : AEStronglyMeasurable f
      (Measure.map (gn21RawCycleMark state n)
        (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI)) := by
    rw [hLaw.map_eq]
    exact hintegrable.aestronglyMeasurable
  simpa [Function.comp_def] using
    (integrable_map_measure hfmap hLaw.aemeasurable).mp hmapInt

/-- Every integrable source-mark statistic has exactly its source integral at
each raw mark coordinate. -/
theorem integral_gn21RawCycleMark_comp_eq
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (n : Nat) (f : TripLength -> Real)
    (hintegrable : Integrable f (gn21CycleMarkLaw muI muJ state)) :
    (∫ seed, f (gn21RawCycleMark state n seed)
      ∂gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) =
      ∫ tau, f tau ∂gn21CycleMarkLaw muI muJ state := by
  have hLaw := gn21RawCycleMark_hasLaw muI muJ arrivalI arrivalJ switchIJ switchJI
    harrivalI harrivalJ hswitchIJ hswitchJI state n
  simpa [Function.comp_def] using hLaw.integral_comp hintegrable.aestronglyMeasurable

/-!
## Literal request-clock stream

The raw seed also exposes each state-conditioned request clock as one complete
canonical exponential interarrival path.  The fixed-time Poisson marginal
below is a source-facing property of that actual path; it is deliberately not
misidentified with the accepted-request process.
-/

/-- The entire raw request-clock path has the literal canonical exponential
interarrival law under the raw GN21 product seed. -/
theorem gn21RawCycleClockStream_hasLaw
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (clock : Fin 4) :
    HasLaw (fun seed : GN21RawCycleSeed => seed.1 clock)
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
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
  change HasLaw (fun seed : GN21RawCycleSeed => seed.1 clock)
    (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
      (clockRate clock)) (clockMeasure.prod markMeasure)
  simpa only [Function.comp_apply] using hstream.comp hfst

/-- At every deterministic nonnegative time, the actual raw request-clock
path has the claimed Poisson count marginal.  This intentionally precedes,
rather than assumes, the missing accepted-mark thinning result. -/
theorem gn21RawRequestCount_hasLaw_poisson
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (clock : Fin 4) (t : Real) (ht : 0 <= t) :
    HasLaw
      (fun seed : GN21RawCycleSeed =>
        AppliedModelingLib.Probability.PoissonProcess.canonicalRenewalCount t (seed.1 clock))
      (ProbabilityTheory.poissonMeasure
        (⟨gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI clock * t,
          mul_nonneg (by
            fin_cases clock
            · exact harrivalI.le
            · exact harrivalJ.le
            · exact hswitchIJ.le
            · exact hswitchJI.le) ht⟩ : ℝ≥0))
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  let rate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI clock
  have hrate : 0 < rate := by
    fin_cases clock <;> simp [rate, gn21CycleClockRate, harrivalI, harrivalJ,
      hswitchIJ, hswitchJI]
  have hstream := gn21RawCycleClockStream_hasLaw muI muJ arrivalI arrivalJ
    switchIJ switchJI harrivalI harrivalJ hswitchIJ hswitchJI clock
  have hcount :=
    AppliedModelingLib.Probability.PoissonProcess.canonicalRenewalCount_hasLaw_poisson
      (rate := rate) (t := t) hrate ht
  simpa [rate, Function.comp_def] using hcount.comp hstream

/-!
## Literal acceptance-mark stream

The source's accepted-request thinning starts by classifying each raw iid trip
mark according to the policy.  This section proves that classification on the
actual `GN21RawCycleSeed` product space.  It does not yet show that the
selected marked arrivals form a Poisson process: that requires a random-index
marked-thinning theorem connecting this iid mark stream to the arrival clock.
-/

/-- The Boolean acceptance classification of a source trip-length mark. -/
noncomputable def gn21AcceptanceMark (sigma : TripPolicy) : TripLength -> Bool := by
  classical
  exact fun tau => if tau ∈ sigma then true else false

/-- Policy measurability makes the Boolean acceptance classification
measurable. -/
theorem measurable_gn21AcceptanceMark
    (sigma : TripPolicy) (hsigma : MeasurableSet sigma) :
    Measurable (gn21AcceptanceMark sigma) := by
  classical
  unfold gn21AcceptanceMark
  exact Measurable.ite hsigma measurable_const measurable_const

/-- The `true` atom of the classified mark is exactly the policy set. -/
theorem gn21AcceptanceMark_preimage_true (sigma : TripPolicy) :
    gn21AcceptanceMark sigma ⁻¹' ({true} : Set Bool) = sigma := by
  classical
  ext tau
  simp [gn21AcceptanceMark]

/-- Classifying an actual source mark as accepted has exactly its source
accepted mass. -/
theorem measure_map_gn21AcceptanceMark_true
    (mu : Measure TripLength) (sigma : TripPolicy)
    (hsigma : MeasurableSet sigma) :
    Measure.map (gn21AcceptanceMark sigma) mu ({true} : Set Bool) = mu sigma := by
  rw [Measure.map_apply (measurable_gn21AcceptanceMark sigma hsigma)
    (measurableSet_singleton true), gn21AcceptanceMark_preimage_true]

/-- The full raw mark stream for either state is a literal iid stream under
the raw GN21 product measure.  This exposes the joint stream law that the
coordinate-level transport lemmas alone do not provide. -/
theorem gn21RawCycleMarkStream_hasLaw
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) :
    HasLaw (fun seed : GN21RawCycleSeed => seed.2 state)
      (Measure.infinitePi fun _ : Nat => gn21CycleMarkLaw muI muJ state)
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
  change HasLaw (fun seed : GN21RawCycleSeed => seed.2 state)
    (Measure.infinitePi fun _ : Nat => markLaw state)
    (clockMeasure.prod markMeasure)
  simpa only [Function.comp_apply] using hstate.comp hsnd

/-- A literal source request-clock stream and a literal source mark stream
are jointly distributed as their independent product laws.  This is the raw
input factorization used when the accepted-mark stopping index selects a
suffix of the clock stream. -/
theorem gn21RawCycleClockStream_markStream_hasLaw_prod
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (clock : Fin 4) (state : Fin 2) :
    HasLaw (fun seed : GN21RawCycleSeed => (seed.1 clock, seed.2 state))
      ((AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
        (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI clock)).prod
        (Measure.infinitePi fun _ : Nat => gn21CycleMarkLaw muI muJ state))
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  let clockRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
  let clockMeasure : Measure (Fin 4 -> Nat -> Real) :=
    Measure.infinitePi fun c : Fin 4 =>
      AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
        (clockRate c)
  let markLaw := gn21CycleMarkLaw muI muJ
  let markMeasure : Measure (Fin 2 -> Nat -> TripLength) :=
    Measure.infinitePi fun s : Fin 2 =>
      Measure.infinitePi fun _ : Nat => markLaw s
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let clockStream : (Fin 4 -> Nat -> Real) -> Nat -> Real := Function.eval clock
  let markStream : (Fin 2 -> Nat -> TripLength) -> Nat -> TripLength := Function.eval state
  have hclockRate : ∀ c : Fin 4, 0 < clockRate c := by
    intro c
    fin_cases c <;> simp [clockRate, gn21CycleClockRate, harrivalI,
      harrivalJ, hswitchIJ, hswitchJI]
  letI : ∀ c : Fin 4, IsProbabilityMeasure
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
        (clockRate c)) := fun c =>
    AppliedModelingLib.Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      (hclockRate c)
  letI : IsProbabilityMeasure clockMeasure := by
    dsimp [clockMeasure]
    infer_instance
  letI : ∀ s : Fin 2, IsProbabilityMeasure (markLaw s) := by
    intro s
    fin_cases s <;> simp only [markLaw, gn21CycleMarkLaw]
    all_goals infer_instance
  letI : ∀ s : Fin 2, IsProbabilityMeasure
      (Measure.infinitePi fun _ : Nat => markLaw s) := fun s => inferInstance
  letI : IsProbabilityMeasure markMeasure := by
    dsimp [markMeasure]
    infer_instance
  letI : IsProbabilityMeasure P := by
    simpa [P] using isProbabilityMeasure_gn21RawCycleSeedMeasure
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI
  have hclockMeas : Measurable clockStream := by
    simpa [clockStream] using (measurable_pi_apply clock :
      Measurable (Function.eval clock : (Fin 4 -> Nat -> Real) -> Nat -> Real))
  have hmarkMeas : Measurable markStream := by
    simpa [markStream] using (measurable_pi_apply state :
      Measurable (Function.eval state : (Fin 2 -> Nat -> TripLength) -> Nat -> TripLength))
  have hclock : HasLaw clockStream
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
        (clockRate clock)) clockMeasure := by
    simpa [clockStream] using
      (measurePreserving_eval_infinitePi
        (fun c : Fin 4 =>
          AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
            (clockRate c)) clock).hasLaw
  have hmark : HasLaw markStream
      (Measure.infinitePi fun _ : Nat => markLaw state) markMeasure := by
    simpa [markStream] using
      (measurePreserving_eval_infinitePi
        (fun s : Fin 2 => Measure.infinitePi fun _ : Nat => markLaw s) state).hasLaw
  have hclockSource : HasLaw (Prod.fst : GN21RawCycleSeed -> Fin 4 -> Nat -> Real)
      clockMeasure P := by
    refine ⟨measurable_fst.aemeasurable, ?_⟩
    change Measure.map Prod.fst (clockMeasure.prod markMeasure) = clockMeasure
    rw [Measure.map_fst_prod]
    simp
  have hmarkSource : HasLaw (Prod.snd : GN21RawCycleSeed -> Fin 2 -> Nat -> TripLength)
      markMeasure P := by
    refine ⟨measurable_snd.aemeasurable, ?_⟩
    change Measure.map Prod.snd (clockMeasure.prod markMeasure) = markMeasure
    rw [Measure.map_snd_prod]
    simp
  have hclockRaw : HasLaw (fun seed : GN21RawCycleSeed => clockStream seed.1)
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
        (clockRate clock)) P := hclock.comp hclockSource
  have hmarkRaw : HasLaw (fun seed : GN21RawCycleSeed => markStream seed.2)
      (Measure.infinitePi fun _ : Nat => markLaw state) P := hmark.comp hmarkSource
  have hindep : ProbabilityTheory.IndepFun
      (fun seed : GN21RawCycleSeed => clockStream seed.1)
      (fun seed : GN21RawCycleSeed => markStream seed.2) P := by
    simpa [P, Function.comp_def] using
      (ProbabilityTheory.indepFun_prod hclockMeas hmarkMeas)
  simpa [P, clockRate, markLaw, clockStream, markStream, gn21RawCycleClock,
    gn21RawCycleMark] using
    (AppliedModelingLib.Probability.indepFun_hasLaw_prodMk hclockRaw hmarkRaw hindep)

/-- The policy-classified raw mark stream has the literal iid product law of
the classified one-mark measure.  This is an all-stream statement, not merely
a finite-horizon count identity. -/
theorem gn21RawAcceptedMarkStream_hasLaw
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy)
    (hsigma : MeasurableSet sigma) :
    HasLaw
      (fun seed : GN21RawCycleSeed =>
        fun n : Nat => gn21AcceptanceMark sigma (gn21RawCycleMark state n seed))
      (Measure.infinitePi fun _ : Nat =>
        Measure.map (gn21AcceptanceMark sigma) (gn21CycleMarkLaw muI muJ state))
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  let M := gn21CycleMarkLaw muI muJ state
  let rawStream : GN21RawCycleSeed -> Nat -> TripLength :=
    fun seed => seed.2 state
  let classify : (Nat -> TripLength) -> Nat -> Bool :=
    fun stream n => gn21AcceptanceMark sigma (stream n)
  have hM_prob : IsProbabilityMeasure M := by
    dsimp [M, gn21CycleMarkLaw]
    fin_cases state <;> infer_instance
  letI : IsProbabilityMeasure M := hM_prob
  have hraw_meas : Measurable rawStream := by
    exact (measurable_pi_apply state).comp measurable_snd
  have hclassify_meas : Measurable classify := by
    apply measurable_pi_lambda
    intro n
    exact (measurable_gn21AcceptanceMark sigma hsigma).comp
      (measurable_pi_apply n)
  have hraw := gn21RawCycleMarkStream_hasLaw muI muJ arrivalI arrivalJ
    switchIJ switchJI harrivalI harrivalJ hswitchIJ hswitchJI state
  have hraw' : HasLaw rawStream (Measure.infinitePi fun _ : Nat => M)
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
    simpa [rawStream, M] using hraw
  refine ⟨(hclassify_meas.comp hraw_meas).aemeasurable, ?_⟩
  calc
    Measure.map (fun seed : GN21RawCycleSeed =>
        fun n : Nat => gn21AcceptanceMark sigma (gn21RawCycleMark state n seed))
        (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) =
      Measure.map classify
        (Measure.map rawStream
          (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI)) := by
        symm
        simpa [classify, rawStream, gn21RawCycleMark, Function.comp_def] using
          (Measure.map_map hclassify_meas hraw_meas)
    _ = Measure.map classify (Measure.infinitePi fun _ : Nat => M) := by
      rw [hraw'.map_eq]
    _ = Measure.infinitePi fun _ : Nat =>
        Measure.map (gn21AcceptanceMark sigma) M := by
      simpa [classify] using
        (Measure.infinitePi_map_pi (μ := fun _ : Nat => M)
          (f := fun _ : Nat => gn21AcceptanceMark sigma)
          (fun _ : Nat => measurable_gn21AcceptanceMark sigma hsigma))

/-!
## Finite raw marked horizons

For a deterministic horizon, the raw request count and every matching finite
accepted-mark prefix are functions of separate factors of the literal source
seed.  The following helpers express those prefixes with the finite-index
product measures used by the existing finite marked-Poisson construction.
-/

/-- The finite range index set is canonically equivalent to `Fin n`.  Keeping
the range subtype visible lets the proof use `infinitePi_map_restrict` without
silently replacing an actual mark prefix by a synthetic vector. -/
def gn21FinRangeEquiv (n : Nat) : Fin n ≃ (Finset.range n) where
  toFun i := ⟨i, Finset.mem_range.mpr i.isLt⟩
  invFun i := ⟨i, Finset.mem_range.mp i.2⟩
  left_inv i := by
    ext
    rfl
  right_inv i := by
    ext
    rfl

/-- The actual first `n` acceptance bits, indexed by the literal finite
range of source request indices. -/
def gn21RawAcceptedMarkRangePrefix
    (state : Fin 2) (sigma : TripPolicy) (n : Nat) :
    GN21RawCycleSeed -> (Finset.range n) -> Bool :=
  fun seed i => gn21AcceptanceMark sigma (gn21RawCycleMark state i seed)

/-- The same actual first `n` acceptance bits, reindexed by `Fin n` for the
finite marked-Poisson sample interface. -/
def gn21RawAcceptedMarkPrefix
    (state : Fin 2) (sigma : TripPolicy) (n : Nat) :
    GN21RawCycleSeed -> Fin n -> Bool :=
  fun seed i => gn21AcceptanceMark sigma (gn21RawCycleMark state i seed)

/-- Reindexing the literal range prefix by `gn21FinRangeEquiv` gives the
ordinary `Fin n` prefix definition exactly. -/
theorem gn21RawAcceptedMarkPrefix_eq_rangePrefix_comp
    (state : Fin 2) (sigma : TripPolicy) (n : Nat) :
    gn21RawAcceptedMarkPrefix state sigma n =
      fun seed prefixIndex =>
        gn21RawAcceptedMarkRangePrefix state sigma n seed
          (gn21FinRangeEquiv n prefixIndex) := by
  funext seed i
  rfl

/-- Every deterministic prefix of actual source acceptance bits has the
literal finite product law obtained by restricting the raw iid mark stream.
This is a finite-prefix theorem only; it does not yet identify the random
arrival-count prefix with a thinned Poisson process. -/
theorem gn21RawAcceptedMarkRangePrefix_hasLaw
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy)
    (hsigma : MeasurableSet sigma) (n : Nat) :
    HasLaw (gn21RawAcceptedMarkRangePrefix state sigma n)
      (Measure.pi fun _ : (Finset.range n) =>
        Measure.map (gn21AcceptanceMark sigma) (gn21CycleMarkLaw muI muJ state))
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  let M := gn21CycleMarkLaw muI muJ state
  let B := Measure.map (gn21AcceptanceMark sigma) M
  let I : Finset Nat := Finset.range n
  have hM_prob : IsProbabilityMeasure M := by
    dsimp [M, gn21CycleMarkLaw]
    fin_cases state <;> infer_instance
  letI : IsProbabilityMeasure M := hM_prob
  letI : IsProbabilityMeasure B := by
    dsimp [B]
    exact Measure.isProbabilityMeasure_map
      (measurable_gn21AcceptanceMark sigma hsigma).aemeasurable
  have hstream := gn21RawAcceptedMarkStream_hasLaw muI muJ arrivalI arrivalJ
    switchIJ switchJI harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma
  have hstream' : HasLaw
      (fun seed : GN21RawCycleSeed =>
        fun index : Nat => gn21AcceptanceMark sigma (gn21RawCycleMark state index seed))
      (Measure.infinitePi fun _ : Nat => B)
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
    simpa [B, M] using hstream
  have hrestrict : MeasurePreserving I.restrict
      (Measure.infinitePi fun _ : Nat => B)
      (Measure.pi fun _ : I => B) :=
    ⟨Finset.measurable_restrict I,
      MeasureTheory.Measure.infinitePi_map_restrict (fun _ : Nat => B)⟩
  change HasLaw (gn21RawAcceptedMarkRangePrefix state sigma n)
    (Measure.pi fun _ : (Finset.range n) => B)
    (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI)
  simpa [gn21RawAcceptedMarkRangePrefix, I, Function.comp_def] using
    hrestrict.hasLaw.comp hstream'

/-- At a deterministic horizon, the actual raw request count and the matching
actual finite acceptance-bit prefix have their independent product law.  This
is the source-process input required by finite marked-Poisson thinning: the
prefix is taken from the same raw mark stream, not drawn after observing the
count. -/
theorem gn21RawRequestCountAndAcceptedMarkRangePrefix_hasLaw
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (clock : Fin 4) (state : Fin 2) (sigma : TripPolicy)
    (hsigma : MeasurableSet sigma) (t : Real) (ht : 0 <= t) (n : Nat) :
    HasLaw
      (fun seed : GN21RawCycleSeed =>
        (AppliedModelingLib.Probability.PoissonProcess.canonicalRenewalCount t (seed.1 clock),
          gn21RawAcceptedMarkRangePrefix state sigma n seed))
      ((ProbabilityTheory.poissonMeasure
        (⟨gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI clock * t,
          mul_nonneg (by
            fin_cases clock
            · exact harrivalI.le
            · exact harrivalJ.le
            · exact hswitchIJ.le
            · exact hswitchJI.le) ht⟩ : ℝ≥0)).prod
        (Measure.pi fun _ : (Finset.range n) =>
          Measure.map (gn21AcceptanceMark sigma) (gn21CycleMarkLaw muI muJ state)))
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  let clockRate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
  let rate := clockRate clock
  have hclockRate : forall c : Fin 4, 0 < clockRate c := by
    intro c
    fin_cases c <;> simp [clockRate, gn21CycleClockRate, harrivalI,
      harrivalJ, hswitchIJ, hswitchJI]
  have hrate : 0 < rate := hclockRate clock
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
  let M := markLaw state
  let B := Measure.map (gn21AcceptanceMark sigma) M
  let markMeasure : Measure (Fin 2 -> Nat -> TripLength) :=
    Measure.infinitePi fun s : Fin 2 =>
      Measure.infinitePi fun _ : Nat => markLaw s
  letI : forall s : Fin 2, IsProbabilityMeasure (markLaw s) := by
    intro s
    fin_cases s <;> simp only [markLaw, gn21CycleMarkLaw]
    all_goals infer_instance
  letI : IsProbabilityMeasure M := by
    dsimp [M]
    infer_instance
  letI : IsProbabilityMeasure B := by
    dsimp [B]
    exact Measure.isProbabilityMeasure_map
      (measurable_gn21AcceptanceMark sigma hsigma).aemeasurable
  letI : forall s : Fin 2, IsProbabilityMeasure
      (Measure.infinitePi fun _ : Nat => markLaw s) := fun s => inferInstance
  letI : IsProbabilityMeasure markMeasure := by
    dsimp [markMeasure]
    infer_instance
  let countLaw : Measure Nat := ProbabilityTheory.poissonMeasure
    (⟨rate * t, mul_nonneg hrate.le ht⟩ : ℝ≥0)
  let I : Finset Nat := Finset.range n
  let classify : (Nat -> TripLength) -> Nat -> Bool :=
    fun stream index => gn21AcceptanceMark sigma (stream index)
  have hclockStream : MeasurePreserving (Function.eval clock) clockMeasure
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure rate) := by
    simpa [clockMeasure, rate] using
      (measurePreserving_eval_infinitePi
        (fun c : Fin 4 =>
          AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure
            (clockRate c)) clock)
  have hcountBase : MeasurePreserving
      (AppliedModelingLib.Probability.PoissonProcess.canonicalRenewalCount t)
      (AppliedModelingLib.Probability.PoissonProcess.exponentialInterarrivalMeasure rate)
      countLaw := by
    refine ⟨AppliedModelingLib.Probability.PoissonProcess.measurable_canonicalRenewalCount t, ?_⟩
    exact (AppliedModelingLib.Probability.PoissonProcess.canonicalRenewalCount_hasLaw_poisson
      hrate ht).map_eq
  have hcount : MeasurePreserving
      (fun clocks : Fin 4 -> Nat -> Real =>
        AppliedModelingLib.Probability.PoissonProcess.canonicalRenewalCount t (clocks clock))
      clockMeasure countLaw := by
    simpa [Function.comp_def] using hcountBase.comp hclockStream
  have hstate : MeasurePreserving (Function.eval state) markMeasure
      (Measure.infinitePi fun _ : Nat => M) := by
    simpa [markMeasure, M] using
      (measurePreserving_eval_infinitePi
        (fun s : Fin 2 => Measure.infinitePi fun _ : Nat => markLaw s) state)
  have hclassify_meas : Measurable classify := by
    apply measurable_pi_lambda
    intro index
    exact (measurable_gn21AcceptanceMark sigma hsigma).comp
      (measurable_pi_apply index)
  have hclassify : MeasurePreserving classify
      (Measure.infinitePi fun _ : Nat => M)
      (Measure.infinitePi fun _ : Nat => B) := by
    refine ⟨hclassify_meas, ?_⟩
    simpa [classify, B] using
      (Measure.infinitePi_map_pi (μ := fun _ : Nat => M)
        (f := fun _ : Nat => gn21AcceptanceMark sigma)
        (fun _ : Nat => measurable_gn21AcceptanceMark sigma hsigma))
  have hrestrict : MeasurePreserving I.restrict
      (Measure.infinitePi fun _ : Nat => B)
      (Measure.pi fun _ : I => B) :=
    ⟨Finset.measurable_restrict I,
      MeasureTheory.Measure.infinitePi_map_restrict (fun _ : Nat => B)⟩
  have hprefix : MeasurePreserving
      (fun marks : Fin 2 -> Nat -> TripLength =>
        I.restrict (classify (marks state)))
      markMeasure (Measure.pi fun _ : I => B) := by
    simpa [Function.comp_def] using hrestrict.comp (hclassify.comp hstate)
  have hjoint := hcount.prod hprefix
  change HasLaw
    (fun seed : (Fin 4 -> Nat -> Real) × (Fin 2 -> Nat -> TripLength) =>
      (AppliedModelingLib.Probability.PoissonProcess.canonicalRenewalCount t (seed.1 clock),
        gn21RawAcceptedMarkRangePrefix state sigma n seed))
    (countLaw.prod (Measure.pi fun _ : I => B))
    (clockMeasure.prod markMeasure)
  simpa [gn21RawAcceptedMarkRangePrefix, I, classify, Function.comp_def] using
    hjoint.hasLaw

/-- The `false` atom of the policy classifier is the complement of the policy
set. -/
theorem gn21AcceptanceMark_preimage_false (sigma : TripPolicy) :
    gn21AcceptanceMark sigma ⁻¹' ({false} : Set Bool) = sigmaᶜ := by
  classical
  ext tau
  simp [gn21AcceptanceMark]

/-- Once its success probability is identified with the source policy mass,
the classified one-mark law is exactly Mathlib's Bernoulli PMF measure. -/
theorem measure_map_gn21AcceptanceMark_eq_bernoulli
    (mu : Measure TripLength) (sigma : TripPolicy)
    [IsProbabilityMeasure mu]
    (hsigma : MeasurableSet sigma)
    (p : ℝ≥0) (hp : p <= 1)
    (hp_mass : (p : ℝ≥0∞) = mu sigma) :
    Measure.map (gn21AcceptanceMark sigma) mu =
      (PMF.bernoulli p hp).toMeasure := by
  apply Measure.ext_of_singleton
  intro b
  cases b with
  | false =>
      rw [Measure.map_apply (measurable_gn21AcceptanceMark sigma hsigma)
        (measurableSet_singleton false), gn21AcceptanceMark_preimage_false,
        measure_compl hsigma (measure_ne_top mu sigma), measure_univ,
        PMF.toMeasure_apply_singleton (PMF.bernoulli p hp) false
          (measurableSet_singleton false), PMF.bernoulli_apply]
      change 1 - mu sigma = ↑(1 - p)
      rw [ENNReal.coe_sub, ← hp_mass]
      simp
  | true =>
      rw [measure_map_gn21AcceptanceMark_true mu sigma hsigma,
        PMF.toMeasure_apply_singleton (PMF.bernoulli p hp) true
          (measurableSet_singleton true), PMF.bernoulli_apply]
      simpa using hp_mass.symm

/-- The source policy mass represented as the Bernoulli parameter used by the
finite marked-Poisson construction. -/
def gn21AcceptanceProbability
    (mu : Measure TripLength) (sigma : TripPolicy) : ℝ≥0 :=
  (mu sigma).toNNReal

/-- The Bernoulli parameter coerces back to the actual source policy mass. -/
theorem coe_gn21AcceptanceProbability
    (mu : Measure TripLength) (sigma : TripPolicy) [IsFiniteMeasure mu] :
    (gn21AcceptanceProbability mu sigma : ℝ≥0∞) = mu sigma := by
  unfold gn21AcceptanceProbability
  exact ENNReal.coe_toNNReal (measure_ne_top mu sigma)

/-- A source policy mass is a valid Bernoulli probability. -/
theorem gn21AcceptanceProbability_le_one
    (mu : Measure TripLength) (sigma : TripPolicy) [IsProbabilityMeasure mu] :
    gn21AcceptanceProbability mu sigma <= 1 := by
  apply ENNReal.coe_le_coe.mp
  rw [coe_gn21AcceptanceProbability]
  simpa using (measure_mono (Set.subset_univ sigma) : mu sigma <= mu Set.univ)

/-- In real-valued source notation, the finite-thinning Bernoulli parameter
is exactly the paper's accepted-trip mass `F(sigma)`. -/
theorem gn21AcceptanceProbability_toReal_eq_singleStateTripMass
    (mu : Measure TripLength) (sigma : TripPolicy) :
    (gn21AcceptanceProbability mu sigma : Real) = singleStateTripMass mu sigma := by
  rfl

/-- The finite iid-mark PMF used by the marked-Poisson library is exactly the
finite product measure of its Bernoulli one-mark law. -/
theorem gn21_iidMarks_toMeasure_eq_pi_bernoulli
    (p : ℝ≥0) (hp : p <= 1) (n : Nat) :
    (AppliedModelingLib.Probability.FiniteHorizonMarkedPoisson.iidMarks p hp n).toMeasure =
      Measure.pi (fun _ : Fin n => (PMF.bernoulli p hp).toMeasure) := by
  apply Measure.ext_of_singleton
  intro marks
  have hsingleton : ({marks} : Set (Fin n -> Bool)) =
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
      (AppliedModelingLib.Probability.FiniteHorizonMarkedPoisson.iidMarks p hp n)
      marks (measurableSet_singleton _), hsingleton, Measure.pi_pi]
  simp [AppliedModelingLib.Probability.FiniteHorizonMarkedPoisson.iidMarks]

/-- Reindexing a finite range-restricted prefix by `Fin n` preserves its iid
product law. -/
theorem gn21RangePrefixReindex_measurePreserving
    (B : Measure Bool) [IsProbabilityMeasure B] (n : Nat) :
    MeasurePreserving
      (fun marks : (Finset.range n) -> Bool =>
        fun i : Fin n => marks (gn21FinRangeEquiv n i))
      (Measure.pi fun _ : (Finset.range n) => B)
      (Measure.pi fun _ : Fin n => B) := by
  let I : Finset Nat := Finset.range n
  let e : Fin n ≃ I := gn21FinRangeEquiv n
  have hforward : MeasurePreserving
      (MeasurableEquiv.piCongrLeft (fun _ : I => Bool) e)
      (Measure.pi fun _ : Fin n => B)
      (Measure.pi fun _ : I => B) :=
    MeasureTheory.measurePreserving_piCongrLeft (fun _ : I => B) e
  change MeasurePreserving
    (fun marks : I -> Bool => fun i : Fin n => marks (e i))
    (Measure.pi fun _ : I => B)
    (Measure.pi fun _ : Fin n => B)
  simpa [MeasurableEquiv.piCongrLeft] using hforward.symm

/-- The actual raw request count and matching `Fin n` acceptance prefix have
the finite marked-Poisson library's exact count-times-iid-mark law whenever
the Bernoulli parameter is identified with the source policy mass. -/
theorem gn21RawRequestCountAndAcceptedMarkPrefix_hasLaw_iid
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (clock : Fin 4) (state : Fin 2) (sigma : TripPolicy)
    (hsigma : MeasurableSet sigma) (t : Real) (ht : 0 <= t) (n : Nat)
    (p : ℝ≥0) (hp : p <= 1)
    (hp_mass : (p : ℝ≥0∞) = gn21CycleMarkLaw muI muJ state sigma) :
    HasLaw
      (fun seed : GN21RawCycleSeed =>
        (AppliedModelingLib.Probability.PoissonProcess.canonicalRenewalCount t (seed.1 clock),
          gn21RawAcceptedMarkPrefix state sigma n seed))
      ((ProbabilityTheory.poissonMeasure
        (⟨gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI clock * t,
          mul_nonneg (by
            fin_cases clock
            · exact harrivalI.le
            · exact harrivalJ.le
            · exact hswitchIJ.le
            · exact hswitchJI.le) ht⟩ : ℝ≥0)).prod
        (AppliedModelingLib.Probability.FiniteHorizonMarkedPoisson.iidMarks p hp n).toMeasure)
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  let rate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI clock
  have hrate : 0 < rate := by
    fin_cases clock <;> simp [rate, gn21CycleClockRate, harrivalI, harrivalJ,
      hswitchIJ, hswitchJI]
  let countLaw : Measure Nat := ProbabilityTheory.poissonMeasure
    (⟨rate * t, mul_nonneg hrate.le ht⟩ : ℝ≥0)
  let M := gn21CycleMarkLaw muI muJ state
  let B := Measure.map (gn21AcceptanceMark sigma) M
  let I : Finset Nat := Finset.range n
  have hM_prob : IsProbabilityMeasure M := by
    dsimp [M, gn21CycleMarkLaw]
    fin_cases state <;> infer_instance
  letI : IsProbabilityMeasure M := hM_prob
  letI : IsProbabilityMeasure B := by
    dsimp [B]
    exact Measure.isProbabilityMeasure_map
      (measurable_gn21AcceptanceMark sigma hsigma).aemeasurable
  have hRange := gn21RawRequestCountAndAcceptedMarkRangePrefix_hasLaw
    muI muJ arrivalI arrivalJ switchIJ switchJI harrivalI harrivalJ hswitchIJ hswitchJI
    clock state sigma hsigma t ht n
  have hRange' : HasLaw
      (fun seed : GN21RawCycleSeed =>
        (AppliedModelingLib.Probability.PoissonProcess.canonicalRenewalCount t (seed.1 clock),
          gn21RawAcceptedMarkRangePrefix state sigma n seed))
      (countLaw.prod (Measure.pi fun _ : I => B))
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
    simpa [countLaw, rate, I, B, M] using hRange
  have hreindex := gn21RangePrefixReindex_measurePreserving B n
  have hpairReindex := (MeasurePreserving.id countLaw).prod hreindex
  have hFin : HasLaw
      (fun seed : GN21RawCycleSeed =>
        (AppliedModelingLib.Probability.PoissonProcess.canonicalRenewalCount t (seed.1 clock),
          fun i : Fin n =>
            gn21RawAcceptedMarkRangePrefix state sigma n seed
              (gn21FinRangeEquiv n i)))
      (countLaw.prod (Measure.pi fun _ : Fin n => B))
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
    simpa [Prod.map, Function.comp_def] using hpairReindex.hasLaw.comp hRange'
  have hBernoulli : B = (PMF.bernoulli p hp).toMeasure := by
    exact measure_map_gn21AcceptanceMark_eq_bernoulli M sigma hsigma p hp
      (by simpa [M] using hp_mass)
  have hiid : Measure.pi (fun _ : Fin n => B) =
      (AppliedModelingLib.Probability.FiniteHorizonMarkedPoisson.iidMarks p hp n).toMeasure := by
    rw [hBernoulli]
    exact (gn21_iidMarks_toMeasure_eq_pi_bernoulli p hp n).symm
  rw [hiid] at hFin
  change HasLaw
    (fun seed : GN21RawCycleSeed =>
      (AppliedModelingLib.Probability.PoissonProcess.canonicalRenewalCount t (seed.1 clock),
        gn21RawAcceptedMarkPrefix state sigma n seed))
    (countLaw.prod
      (AppliedModelingLib.Probability.FiniteHorizonMarkedPoisson.iidMarks p hp n).toMeasure)
    (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI)
  simpa [gn21RawAcceptedMarkPrefix, gn21RawAcceptedMarkRangePrefix,
    gn21FinRangeEquiv] using hFin

/-- The literal finite marked-Poisson sample over an actual raw GN21 request
horizon.  Its length is the actual canonical request count and its marks are
the matching initial segment of the same source mark stream. -/
def gn21RawFiniteHorizonMarkedSample
    (clock : Fin 4) (state : Fin 2) (sigma : TripPolicy) (t : Real) :
    GN21RawCycleSeed -> AppliedModelingLib.Probability.FiniteHorizonMarkedPoisson.Sample :=
  fun seed =>
    let N := AppliedModelingLib.Probability.PoissonProcess.canonicalRenewalCount t (seed.1 clock)
    ⟨N, fun i => gn21AcceptanceMark sigma (gn21RawCycleMark state i seed)⟩

/-- The actual random-length source horizon sample is measurable.  Its atoms
are specified by one raw renewal-count atom and a finite set of actual source
mark-coordinate atoms. -/
theorem measurable_gn21RawFiniteHorizonMarkedSample
    (clock : Fin 4) (state : Fin 2) (sigma : TripPolicy)
    (hsigma : MeasurableSet sigma) (t : Real) :
    Measurable (gn21RawFiniteHorizonMarkedSample clock state sigma t) := by
  classical
  let N : GN21RawCycleSeed -> Nat := fun seed =>
    AppliedModelingLib.Probability.PoissonProcess.canonicalRenewalCount t (seed.1 clock)
  have hN : Measurable N :=
    AppliedModelingLib.Probability.PoissonProcess.measurable_canonicalRenewalCount t |>.comp
      ((measurable_pi_apply clock).comp measurable_fst)
  refine measurable_to_countable' ?_
  rintro ⟨n, marks⟩
  have hpreimage :
      gn21RawFiniteHorizonMarkedSample clock state sigma t ⁻¹' ({⟨n, marks⟩} : Set _) =
        (N ⁻¹' ({n} : Set Nat)) ∩
          ⋂ i : Fin n, {seed : GN21RawCycleSeed |
            gn21AcceptanceMark sigma (gn21RawCycleMark state i seed) = marks i} := by
    ext seed
    simp [gn21RawFiniteHorizonMarkedSample, N]
    intro hn
    subst n
    constructor
    · intro h i
      exact congr_fun (eq_of_heq h) i
    · intro h
      exact heq_of_eq (funext h)
  rw [hpreimage]
  apply (hN (measurableSet_singleton _)).inter
  apply MeasurableSet.iInter
  intro i
  exact measurableSet_eq.preimage (by
    simpa [gn21RawCycleMark, Function.comp_def] using
      ((measurable_gn21AcceptanceMark sigma hsigma).comp
        ((measurable_pi_apply i.1).comp
          ((measurable_pi_apply state).comp measurable_snd))))

/-- The actual random-length GN21 request horizon has exactly the literal
finite marked-Poisson sample law.  This proves deterministic-horizon marked
thinning from the raw clock and mark seed, rather than supplying it as a
source-model assumption. -/
theorem gn21RawFiniteHorizonMarkedSample_hasLaw
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (clock : Fin 4) (state : Fin 2) (sigma : TripPolicy)
    (hsigma : MeasurableSet sigma) (t : Real) (ht : 0 <= t)
    (p : ℝ≥0) (hp : p <= 1)
    (hp_mass : (p : ℝ≥0∞) = gn21CycleMarkLaw muI muJ state sigma) :
    HasLaw (gn21RawFiniteHorizonMarkedSample clock state sigma t)
      (AppliedModelingLib.Probability.FiniteHorizonMarkedPoisson.jointPMF
        (⟨gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI clock * t,
          mul_nonneg (by
            fin_cases clock
            · exact harrivalI.le
            · exact harrivalJ.le
            · exact hswitchIJ.le
            · exact hswitchJI.le) ht⟩ : ℝ≥0) p hp).toMeasure
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  let rate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI clock
  have hrate : 0 < rate := by
    fin_cases clock <;> simp [rate, gn21CycleClockRate, harrivalI, harrivalJ,
      hswitchIJ, hswitchJI]
  let mean : ℝ≥0 := ⟨rate * t, mul_nonneg hrate.le ht⟩
  refine ⟨(measurable_gn21RawFiniteHorizonMarkedSample clock state sigma hsigma t).aemeasurable,
    ?_⟩
  apply Measure.ext_of_singleton
  rintro ⟨n, marks⟩
  let N : GN21RawCycleSeed -> Nat := fun seed =>
    AppliedModelingLib.Probability.PoissonProcess.canonicalRenewalCount t (seed.1 clock)
  let markVector : GN21RawCycleSeed -> Fin n -> Bool := fun seed i =>
    gn21AcceptanceMark sigma (gn21RawCycleMark state i seed)
  have hN : Measurable N :=
    AppliedModelingLib.Probability.PoissonProcess.measurable_canonicalRenewalCount t |>.comp
      ((measurable_pi_apply clock).comp measurable_fst)
  have hmarkVector : Measurable markVector := by
    apply measurable_pi_lambda
    intro i
    simpa [markVector, gn21RawCycleMark, Function.comp_def] using
      ((measurable_gn21AcceptanceMark sigma hsigma).comp
        ((measurable_pi_apply i.1).comp
          ((measurable_pi_apply state).comp measurable_snd)))
  have hpref : HasLaw (fun seed : GN21RawCycleSeed =>
      (N seed, markVector seed))
      ((ProbabilityTheory.poissonMeasure mean).prod
        (AppliedModelingLib.Probability.FiniteHorizonMarkedPoisson.iidMarks p hp n).toMeasure)
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
    simpa [N, markVector, mean, rate] using
      (gn21RawRequestCountAndAcceptedMarkPrefix_hasLaw_iid
        muI muJ arrivalI arrivalJ switchIJ switchJI harrivalI harrivalJ hswitchIJ hswitchJI
        clock state sigma hsigma t ht n p hp hp_mass)
  have hpreimage :
      gn21RawFiniteHorizonMarkedSample clock state sigma t ⁻¹' ({⟨n, marks⟩} : Set _) =
        (fun seed : GN21RawCycleSeed => (N seed, markVector seed)) ⁻¹'
          ({(n, marks)} : Set _) := by
    ext seed
    simp [gn21RawFiniteHorizonMarkedSample, N, markVector]
    intro hn
    subst n
    constructor
    · intro h
      exact eq_of_heq h
    · intro h
      exact heq_of_eq h
  rw [Measure.map_apply
      (measurable_gn21RawFiniteHorizonMarkedSample clock state sigma hsigma t)
      (measurableSet_singleton _), hpreimage,
    ← Measure.map_apply (hN.prodMk hmarkVector) (measurableSet_singleton _),
    hpref.map_eq, ← Set.singleton_prod_singleton, Measure.prod_prod,
    PMF.toMeasure_apply_singleton
      (AppliedModelingLib.Probability.FiniteHorizonMarkedPoisson.jointPMF mean p hp)
      (AppliedModelingLib.Probability.FiniteHorizonMarkedPoisson.Sample.mk n marks)
      (measurableSet_singleton _),
    AppliedModelingLib.Probability.FiniteHorizonMarkedPoisson.jointPMF_apply]
  calc
    (ProbabilityTheory.poissonMeasure mean) {n} *
        (AppliedModelingLib.Probability.FiniteHorizonMarkedPoisson.iidMarks p hp n).toMeasure {marks} =
        ((ProbabilityTheory.poissonMeasure mean).toPMF).toMeasure {n} *
          (AppliedModelingLib.Probability.FiniteHorizonMarkedPoisson.iidMarks p hp n).toMeasure
            {marks} := by
              rw [Measure.toPMF_toMeasure]
    _ = (ProbabilityTheory.poissonMeasure mean).toPMF n *
          AppliedModelingLib.Probability.FiniteHorizonMarkedPoisson.iidMarks p hp n marks := by
            rw [PMF.toMeasure_apply_singleton (ProbabilityTheory.poissonMeasure mean).toPMF n
              (measurableSet_singleton _),
              PMF.toMeasure_apply_singleton
                (AppliedModelingLib.Probability.FiniteHorizonMarkedPoisson.iidMarks p hp n)
                marks (measurableSet_singleton _)]

/-- The number of accepted requests among the actual raw requests up to a
deterministic horizon. -/
def gn21RawAcceptedRequestCount
    (clock : Fin 4) (state : Fin 2) (sigma : TripPolicy) (t : Real) :
    GN21RawCycleSeed -> Nat :=
  fun seed => AppliedModelingLib.Probability.FiniteHorizonMarkedPoisson.kept
    (gn21RawFiniteHorizonMarkedSample clock state sigma t seed)

/-- Deterministic-horizon marked-Poisson thinning for the actual GN21 raw
source seed: the retained accepted-request count is Poisson with the thinned
mean.  This does not yet claim independent increments or a stopped-process
memoryless theorem. -/
theorem gn21RawAcceptedRequestCount_hasLaw_poisson
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (clock : Fin 4) (state : Fin 2) (sigma : TripPolicy)
    (hsigma : MeasurableSet sigma) (t : Real) (ht : 0 <= t)
    (p : ℝ≥0) (hp : p <= 1)
    (hp_mass : (p : ℝ≥0∞) = gn21CycleMarkLaw muI muJ state sigma) :
    HasLaw (gn21RawAcceptedRequestCount clock state sigma t)
      (ProbabilityTheory.poissonMeasure
        (NNReal.mk (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI clock * t)
          (mul_nonneg (by
            fin_cases clock
            · exact harrivalI.le
            · exact harrivalJ.le
            · exact hswitchIJ.le
            · exact hswitchJI.le) ht) * p))
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  let rate := gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI clock
  have hrate : 0 < rate := by
    fin_cases clock <;> simp [rate, gn21CycleClockRate, harrivalI, harrivalJ,
      hswitchIJ, hswitchJI]
  let mean : ℝ≥0 := ⟨rate * t, mul_nonneg hrate.le ht⟩
  have hsample := gn21RawFiniteHorizonMarkedSample_hasLaw
    muI muJ arrivalI arrivalJ switchIJ switchJI harrivalI harrivalJ hswitchIJ hswitchJI
    clock state sigma hsigma t ht p hp hp_mass
  simpa [gn21RawAcceptedRequestCount, mean, rate, Function.comp_def] using
    (AppliedModelingLib.Probability.FiniteHorizonMarkedPoisson.kept_hasLaw mean p hp).comp hsample

/-- Source-mass specialization of deterministic-horizon marked thinning. -/
theorem gn21RawAcceptedRequestCount_hasLaw_poisson_of_sourceMass
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (clock : Fin 4) (state : Fin 2) (sigma : TripPolicy)
    (hsigma : MeasurableSet sigma) (t : Real) (ht : 0 <= t) :
    HasLaw (gn21RawAcceptedRequestCount clock state sigma t)
      (ProbabilityTheory.poissonMeasure
        (NNReal.mk (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI clock * t)
          (mul_nonneg (by
            fin_cases clock
            · exact harrivalI.le
            · exact harrivalJ.le
            · exact hswitchIJ.le
            · exact hswitchJI.le) ht) *
          gn21AcceptanceProbability (gn21CycleMarkLaw muI muJ state) sigma))
      (gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  let M := gn21CycleMarkLaw muI muJ state
  have hM_prob : IsProbabilityMeasure M := by
    dsimp [M, gn21CycleMarkLaw]
    fin_cases state <;> infer_instance
  letI : IsProbabilityMeasure M := hM_prob
  exact gn21RawAcceptedRequestCount_hasLaw_poisson
    muI muJ arrivalI arrivalJ switchIJ switchJI harrivalI harrivalJ hswitchIJ hswitchJI
    clock state sigma hsigma t ht (gn21AcceptanceProbability M sigma)
    (gn21AcceptanceProbability_le_one M sigma)
    (by simpa [M] using coe_gn21AcceptanceProbability M sigma)

/-- A source statistic integrable on the accepted policy remains integrable
under the literal conditional accepted-mark law. -/
theorem integrable_gn21AcceptedTripLaw_of_integrableOn
    (mu : Measure TripLength) (sigma : TripPolicy) (f : TripLength -> Real)
    (hmass : 0 < singleStateTripMass mu sigma)
    (hintegrable : IntegrableOn f sigma mu) :
    Integrable f (gn21AcceptedTripLaw mu sigma) := by
  have hmass_ne : mu sigma ≠ 0 := by
    intro hzero
    have : singleStateTripMass mu sigma = 0 := by
      simp [singleStateTripMass, hzero]
    linarith
  unfold gn21AcceptedTripLaw ProbabilityTheory.cond
  exact hintegrable.integrable.smul_measure (ENNReal.inv_ne_top.2 hmass_ne)

/-- The CTMC switch-probability statistic is integrable on an accepted-mark
law from the paper's primitive positivity and feasible-policy conditions; no
extra integrability certificate for this bounded statistic is needed. -/
theorem integrable_gn21SwitchProb_underAcceptedTripLaw
    (mu : Measure TripLength) (sigma : TripPolicy)
    (switchIJ switchJI : Real)
    [IsProbabilityMeasure mu]
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (hsigma_measurable : MeasurableSet sigma)
    (hsigma_subset : Set.Subset sigma acceptAllPolicy)
    (hmass : 0 < singleStateTripMass mu sigma) :
    Integrable (gn21SwitchProb switchIJ switchJI)
      (gn21AcceptedTripLaw mu sigma) := by
  have hsum : 0 < switchIJ + switchJI := add_pos hswitchIJ hswitchJI
  have hq_meas : Measurable (gn21SwitchProb switchIJ switchJI) :=
    (continuous_gn21SwitchProb switchIJ switchJI).measurable
  have hq_integrable : IntegrableOn (gn21SwitchProb switchIJ switchJI) sigma mu := by
    refine Measure.integrableOn_of_bounded (M := (1 : Real)) (measure_ne_top mu sigma)
      hq_meas.aestronglyMeasurable ?_
    refine (ae_restrict_iff' hsigma_measurable).2
      (Filter.Eventually.of_forall fun tau htau => ?_)
    have hnonneg : 0 <= gn21SwitchProb switchIJ switchJI tau :=
      paper_lemma2_switch_probability_nonneg switchIJ switchJI tau
        (le_of_lt hswitchIJ) hsum (le_of_lt (hsigma_subset htau))
    have hle : gn21SwitchProb switchIJ switchJI tau <= 1 :=
      paper_lemma2_switch_probability_le_one switchIJ switchJI tau
        (le_of_lt hswitchIJ) (le_of_lt hswitchJI) hsum
        (le_of_lt (hsigma_subset htau))
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hle
  exact integrable_gn21AcceptedTripLaw_of_integrableOn mu sigma
    (gn21SwitchProb switchIJ switchJI) hmass hq_integrable

/-- An integrable source trip length remains integrable after conditioning on
an accepted request.  This is the trip-duration input to the Appendix D.1
subcycle calculation. -/
theorem integrable_gn21AcceptedTripLength
    (mu : Measure TripLength) (sigma : TripPolicy)
    (hmass : 0 < singleStateTripMass mu sigma)
    (htime : IntegrableOn (fun tau : TripLength => tau) sigma mu) :
    Integrable (fun tau : TripLength => tau) (gn21AcceptedTripLaw mu sigma) := by
  exact integrable_gn21AcceptedTripLaw_of_integrableOn mu sigma
    (fun tau : TripLength => tau) hmass htime

/-- An integrable source payout remains integrable after conditioning on an
accepted request. -/
theorem integrable_gn21AcceptedTripPayment
    (mu : Measure TripLength) (w : PricingFunction) (sigma : TripPolicy)
    (hmass : 0 < singleStateTripMass mu sigma)
    (hpayment : IntegrableOn w sigma mu) :
    Integrable w (gn21AcceptedTripLaw mu sigma) := by
  exact integrable_gn21AcceptedTripLaw_of_integrableOn mu sigma w hmass hpayment

/-!
## Literal post-thinning race inputs

Appendix D.1 next compares an accepted-arrival clock of rate
`lambda * F(sigma)` with the open-state CTMC switch clock.  The following is
the literal independent product probability space for those *post-thinning*
inputs and the conditional accepted mark.  It is not asserted to be a map of
`GN21RawCycleSeed`: proving that equivalence is precisely the missing
all-time marked-Poisson thinning theorem.
-/

/-- The three independent inputs used by one post-thinning open-state race:
accepted-arrival delay, state-switch delay, and accepted trip mark. -/
abbrev GN21PostThinningRaceSeed := Real × Real × TripLength

/-- Literal product law for the post-thinning competing-clock inputs. -/
def gn21PostThinningRaceSeedMeasure
    (mu : Measure TripLength) (arrivalRate switchRate : Real) (sigma : TripPolicy) :
    Measure GN21PostThinningRaceSeed :=
  (ProbabilityTheory.expMeasure (arrivalRate * singleStateTripMass mu sigma)).prod
    ((ProbabilityTheory.expMeasure switchRate).prod (gn21AcceptedTripLaw mu sigma))

/-- The accepted-arrival clock coordinate of a post-thinning race seed. -/
def gn21PostThinningAcceptedArrivalDelay : GN21PostThinningRaceSeed -> Real :=
  fun seed => seed.1

/-- The open-state switch-clock coordinate of a post-thinning race seed. -/
def gn21PostThinningStateSwitchDelay : GN21PostThinningRaceSeed -> Real :=
  fun seed => seed.2.1

/-- The conditional accepted trip mark of a post-thinning race seed. -/
def gn21PostThinningTripMark : GN21PostThinningRaceSeed -> TripLength :=
  fun seed => seed.2.2

/-- The post-thinning race seed law is a probability measure under the paper's
positive arrival, accepted-mass, and switch-rate hypotheses. -/
theorem isProbabilityMeasure_gn21PostThinningRaceSeedMeasure
    (mu : Measure TripLength) (arrivalRate switchRate : Real) (sigma : TripPolicy)
    [IsProbabilityMeasure mu]
    (harrival : 0 < arrivalRate) (hswitch : 0 < switchRate)
    (hmass : 0 < singleStateTripMass mu sigma) :
    IsProbabilityMeasure
      (gn21PostThinningRaceSeedMeasure mu arrivalRate switchRate sigma) := by
  have haccepted_rate : 0 < arrivalRate * singleStateTripMass mu sigma :=
    mul_pos harrival hmass
  letI : IsProbabilityMeasure
      (ProbabilityTheory.expMeasure (arrivalRate * singleStateTripMass mu sigma)) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure haccepted_rate
  letI : IsProbabilityMeasure (ProbabilityTheory.expMeasure switchRate) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure hswitch
  letI : IsProbabilityMeasure (gn21AcceptedTripLaw mu sigma) :=
    gn21AcceptedTripLaw_isProbability mu sigma hmass
  change IsProbabilityMeasure
    ((ProbabilityTheory.expMeasure (arrivalRate * singleStateTripMass mu sigma)).prod
      ((ProbabilityTheory.expMeasure switchRate).prod (gn21AcceptedTripLaw mu sigma)))
  infer_instance

/-- The literal post-thinning accepted-arrival delay has its stipulated
exponential law. -/
theorem gn21PostThinningAcceptedArrivalDelay_hasLaw
    (mu : Measure TripLength) (arrivalRate switchRate : Real) (sigma : TripPolicy)
    [IsProbabilityMeasure mu]
    (harrival : 0 < arrivalRate) (hswitch : 0 < switchRate)
    (hmass : 0 < singleStateTripMass mu sigma) :
    HasLaw gn21PostThinningAcceptedArrivalDelay
      (ProbabilityTheory.expMeasure (arrivalRate * singleStateTripMass mu sigma))
      (gn21PostThinningRaceSeedMeasure mu arrivalRate switchRate sigma) := by
  have haccepted_rate : 0 < arrivalRate * singleStateTripMass mu sigma :=
    mul_pos harrival hmass
  let A := ProbabilityTheory.expMeasure (arrivalRate * singleStateTripMass mu sigma)
  let B := (ProbabilityTheory.expMeasure switchRate).prod (gn21AcceptedTripLaw mu sigma)
  letI : IsProbabilityMeasure A := by
    simpa [A] using ProbabilityTheory.isProbabilityMeasure_expMeasure haccepted_rate
  letI : IsProbabilityMeasure (ProbabilityTheory.expMeasure switchRate) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure hswitch
  letI : IsProbabilityMeasure (gn21AcceptedTripLaw mu sigma) :=
    gn21AcceptedTripLaw_isProbability mu sigma hmass
  letI : IsProbabilityMeasure B := by
    dsimp [B]
    infer_instance
  change HasLaw (Prod.fst : Real × (Real × TripLength) -> Real) A (A.prod B)
  refine ⟨measurable_fst.aemeasurable, ?_⟩
  rw [Measure.map_fst_prod]
  simp

/-- The literal post-thinning state-switch delay has its stipulated
exponential law. -/
theorem gn21PostThinningStateSwitchDelay_hasLaw
    (mu : Measure TripLength) (arrivalRate switchRate : Real) (sigma : TripPolicy)
    [IsProbabilityMeasure mu]
    (harrival : 0 < arrivalRate) (hswitch : 0 < switchRate)
    (hmass : 0 < singleStateTripMass mu sigma) :
    HasLaw gn21PostThinningStateSwitchDelay (ProbabilityTheory.expMeasure switchRate)
      (gn21PostThinningRaceSeedMeasure mu arrivalRate switchRate sigma) := by
  have haccepted_rate : 0 < arrivalRate * singleStateTripMass mu sigma :=
    mul_pos harrival hmass
  let A := ProbabilityTheory.expMeasure (arrivalRate * singleStateTripMass mu sigma)
  let S := ProbabilityTheory.expMeasure switchRate
  let M := gn21AcceptedTripLaw mu sigma
  let B := S.prod M
  letI : IsProbabilityMeasure A := by
    simpa [A] using ProbabilityTheory.isProbabilityMeasure_expMeasure haccepted_rate
  letI : IsProbabilityMeasure S := by
    simpa [S] using ProbabilityTheory.isProbabilityMeasure_expMeasure hswitch
  letI : IsProbabilityMeasure M := by
    simpa [M] using gn21AcceptedTripLaw_isProbability mu sigma hmass
  letI : IsProbabilityMeasure B := by
    dsimp [B]
    infer_instance
  have hsnd : HasLaw (Prod.snd : Real × (Real × TripLength) -> Real × TripLength)
      B (A.prod B) := by
    refine ⟨measurable_snd.aemeasurable, ?_⟩
    rw [Measure.map_snd_prod]
    simp
  have hfst : HasLaw (Prod.fst : Real × TripLength -> Real) S (S.prod M) := by
    refine ⟨measurable_fst.aemeasurable, ?_⟩
    rw [Measure.map_fst_prod]
    simp
  change HasLaw (fun seed : Real × (Real × TripLength) => seed.2.1) S (A.prod B)
  simpa only [Function.comp_apply] using hfst.comp hsnd

/-- The literal post-thinning trip mark has the conditional accepted-mark law. -/
theorem gn21PostThinningTripMark_hasLaw
    (mu : Measure TripLength) (arrivalRate switchRate : Real) (sigma : TripPolicy)
    [IsProbabilityMeasure mu]
    (harrival : 0 < arrivalRate) (hswitch : 0 < switchRate)
    (hmass : 0 < singleStateTripMass mu sigma) :
    HasLaw gn21PostThinningTripMark (gn21AcceptedTripLaw mu sigma)
      (gn21PostThinningRaceSeedMeasure mu arrivalRate switchRate sigma) := by
  have haccepted_rate : 0 < arrivalRate * singleStateTripMass mu sigma :=
    mul_pos harrival hmass
  let A := ProbabilityTheory.expMeasure (arrivalRate * singleStateTripMass mu sigma)
  let S := ProbabilityTheory.expMeasure switchRate
  let M := gn21AcceptedTripLaw mu sigma
  let B := S.prod M
  letI : IsProbabilityMeasure A := by
    simpa [A] using ProbabilityTheory.isProbabilityMeasure_expMeasure haccepted_rate
  letI : IsProbabilityMeasure S := by
    simpa [S] using ProbabilityTheory.isProbabilityMeasure_expMeasure hswitch
  letI : IsProbabilityMeasure M := by
    simpa [M] using gn21AcceptedTripLaw_isProbability mu sigma hmass
  letI : IsProbabilityMeasure B := by
    dsimp [B]
    infer_instance
  have hsnd : HasLaw (Prod.snd : Real × (Real × TripLength) -> Real × TripLength)
      B (A.prod B) := by
    refine ⟨measurable_snd.aemeasurable, ?_⟩
    rw [Measure.map_snd_prod]
    simp
  have hsnd' : HasLaw (Prod.snd : Real × TripLength -> TripLength) M (S.prod M) := by
    refine ⟨measurable_snd.aemeasurable, ?_⟩
    rw [Measure.map_snd_prod]
    simp
  change HasLaw (fun seed : Real × (Real × TripLength) => seed.2.2) M (A.prod B)
  simpa only [Function.comp_apply] using hsnd'.comp hsnd

private theorem integral_eq_inv_rate_of_expLaw
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) (clock : Omega -> Real) (rate : Real)
    (hrate : 0 < rate)
    (hLaw : HasLaw clock (ProbabilityTheory.expMeasure rate) P) :
    (∫ omega, clock omega ∂P) = 1 / rate := by
  let M : AppliedModelingLib.Probability.Exponential.Model :=
    AppliedModelingLib.Probability.Exponential.Model.mk rate hrate
  calc
    (∫ omega, clock omega ∂P) = ∫ x, x ∂ProbabilityTheory.expMeasure rate :=
      hLaw.integral_eq
    _ = M.expectedMaxValue 1 := by
      simpa [AppliedModelingLib.Probability.Exponential.Model.measure, M] using
        M.integral_id_eq_expectedMaxValue_one
    _ = 1 / rate := by
      simp [AppliedModelingLib.Probability.Exponential.Model.expectedMaxValue,
        AppliedModelingLib.Probability.Exponential.expectedMaxValueOfRate_one, M]

/-- Exact mean of the literal post-thinning accepted-arrival delay. -/
theorem integral_gn21PostThinningAcceptedArrivalDelay_eq_inv_rate
    (mu : Measure TripLength) (arrivalRate switchRate : Real) (sigma : TripPolicy)
    [IsProbabilityMeasure mu]
    (harrival : 0 < arrivalRate) (hswitch : 0 < switchRate)
    (hmass : 0 < singleStateTripMass mu sigma) :
    (∫ seed, gn21PostThinningAcceptedArrivalDelay seed
      ∂gn21PostThinningRaceSeedMeasure mu arrivalRate switchRate sigma) =
      1 / (arrivalRate * singleStateTripMass mu sigma) := by
  exact integral_eq_inv_rate_of_expLaw
    (gn21PostThinningRaceSeedMeasure mu arrivalRate switchRate sigma)
    gn21PostThinningAcceptedArrivalDelay
    (arrivalRate * singleStateTripMass mu sigma) (mul_pos harrival hmass)
    (gn21PostThinningAcceptedArrivalDelay_hasLaw mu arrivalRate switchRate sigma
      harrival hswitch hmass)

/-- Exact mean of the literal post-thinning open-state switch delay. -/
theorem integral_gn21PostThinningStateSwitchDelay_eq_inv_rate
    (mu : Measure TripLength) (arrivalRate switchRate : Real) (sigma : TripPolicy)
    [IsProbabilityMeasure mu]
    (harrival : 0 < arrivalRate) (hswitch : 0 < switchRate)
    (hmass : 0 < singleStateTripMass mu sigma) :
    (∫ seed, gn21PostThinningStateSwitchDelay seed
      ∂gn21PostThinningRaceSeedMeasure mu arrivalRate switchRate sigma) =
      1 / switchRate := by
  exact integral_eq_inv_rate_of_expLaw
    (gn21PostThinningRaceSeedMeasure mu arrivalRate switchRate sigma)
    gn21PostThinningStateSwitchDelay switchRate hswitch
    (gn21PostThinningStateSwitchDelay_hasLaw mu arrivalRate switchRate sigma
      harrival hswitch hmass)

/-- Every integrable accepted-mark statistic transports exactly through the
literal post-thinning race seed. -/
theorem integral_gn21PostThinningTripMark_comp_eq
    (mu : Measure TripLength) (arrivalRate switchRate : Real) (sigma : TripPolicy)
    [IsProbabilityMeasure mu]
    (harrival : 0 < arrivalRate) (hswitch : 0 < switchRate)
    (hmass : 0 < singleStateTripMass mu sigma)
    (f : TripLength -> Real)
    (hintegrable : Integrable f (gn21AcceptedTripLaw mu sigma)) :
    (∫ seed, f (gn21PostThinningTripMark seed)
      ∂gn21PostThinningRaceSeedMeasure mu arrivalRate switchRate sigma) =
      ∫ tau, f tau ∂gn21AcceptedTripLaw mu sigma := by
  have hLaw := gn21PostThinningTripMark_hasLaw mu arrivalRate switchRate sigma
    harrival hswitch hmass
  simpa [Function.comp_def] using hLaw.integral_comp hintegrable.aestronglyMeasurable

/-!
## Appendix D.1 post-thinning component equations

The following three equations are the exact calculations made after the
source proof invokes marked-Poisson thinning.  They are deliberately written
in terms of an already thinned accepted-arrival clock and the literal
conditional accepted-mark law.  Thus they prove the source algebra without
claiming that the raw full-request stream has already been thinned or that a
CTMC has already been restarted at a random trip-completion time.
-/

/-- Once an accepted-arrival clock has rate `lambda * F(sigma)`, its holding
time plus the accepted-trip duration has exactly Appendix D.1's expected
subcycle-length expression. -/
theorem gn21_expected_subcycle_time_from_post_thinning_components
    (mu : Measure TripLength) (arrivalRate switchRate : Real) (sigma : TripPolicy)
    [IsProbabilityMeasure mu]
    (harrival : 0 < arrivalRate)
    (hswitch : 0 <= switchRate)
    (hmass : 0 < singleStateTripMass mu sigma) :
    1 / (arrivalRate * singleStateTripMass mu sigma + switchRate) +
        (arrivalRate * singleStateTripMass mu sigma) /
            (arrivalRate * singleStateTripMass mu sigma + switchRate) *
          (∫ tau, tau ∂gn21AcceptedTripLaw mu sigma) =
      gn21SubcycleLength arrivalRate (singleStateTripMass mu sigma) switchRate
        (gn21StateCycleTime mu arrivalRate sigma) := by
  rw [gn21AcceptedTripLaw_integral_id mu sigma hmass]
  have hmass_ne : singleStateTripMass mu sigma ≠ 0 := ne_of_gt hmass
  have harrival_mass_pos : 0 < arrivalRate * singleStateTripMass mu sigma :=
    mul_pos harrival hmass
  have hden_ne : arrivalRate * singleStateTripMass mu sigma + switchRate ≠ 0 :=
    ne_of_gt (add_pos_of_pos_of_nonneg harrival_mass_pos hswitch)
  unfold gn21SubcycleLength gn21StateCycleTime
  field_simp [hmass_ne, hden_ne, ne_of_gt harrival_mass_pos]

/-- Once an accepted-arrival clock has rate `lambda * F(sigma)`, the expected
accepted-trip payout contribution has exactly Appendix D.1's subcycle-earning
expression. -/
theorem gn21_expected_subcycle_earning_from_post_thinning_components
    (mu : Measure TripLength) (arrivalRate switchRate : Real)
    (w : PricingFunction) (sigma : TripPolicy)
    [IsProbabilityMeasure mu]
    (hmass : 0 < singleStateTripMass mu sigma) :
    (arrivalRate * singleStateTripMass mu sigma) /
          (arrivalRate * singleStateTripMass mu sigma + switchRate) *
        (∫ tau, w tau ∂gn21AcceptedTripLaw mu sigma) =
      gn21SubcycleEarning arrivalRate (singleStateTripMass mu sigma) switchRate
        (gn21StateMeanEarning mu w sigma) := by
  rw [gn21AcceptedTripLaw_integral_payment mu w sigma hmass]
  rfl

/-- The state-exit probability computed from a state switch while open plus a
CTMC switch during an accepted trip is exactly Appendix D.1's `p_ij`.
The remaining process obligation is to construct this Bernoulli event from
the literal CTMC path and prove the displayed conditional probability. -/
theorem gn21_cross_subcycle_probability_from_post_thinning_components
    (mu : Measure TripLength) (arrivalRate switchIJ switchJI : Real)
    (sigma : TripPolicy)
    [IsProbabilityMeasure mu]
    (hmass : 0 < singleStateTripMass mu sigma)
    (hden : arrivalRate * singleStateTripMass mu sigma + switchIJ ≠ 0) :
    switchIJ / (arrivalRate * singleStateTripMass mu sigma + switchIJ) +
        (arrivalRate * singleStateTripMass mu sigma) /
            (arrivalRate * singleStateTripMass mu sigma + switchIJ) *
          (∫ tau, gn21SwitchProb switchIJ switchJI tau
            ∂gn21AcceptedTripLaw mu sigma) =
      gn21CrossSubcycleProb arrivalRate (singleStateTripMass mu sigma) switchIJ
        (gn21ExitWeightIntegral mu arrivalRate switchIJ switchJI sigma) := by
  rw [gn21AcceptedTripLaw_integral_switchProb mu sigma switchIJ switchJI hmass]
  have hmass_ne : singleStateTripMass mu sigma ≠ 0 := ne_of_gt hmass
  unfold gn21CrossSubcycleProb gn21ExitWeightIntegral
  field_simp [hmass_ne, hden]

end
end GN21DriverSurgePricing
