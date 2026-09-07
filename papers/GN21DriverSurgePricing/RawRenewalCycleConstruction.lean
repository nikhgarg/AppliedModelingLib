import GN21DriverSurgePricing.RawPostThinningRaceBridge
import AppliedModelingLib.Foundations.Probability.IidFirstHitStoppedReward

/-!
# Finite-horizon source subcycle construction for GN21

The source specifies reopening after an accepted trip.  This module therefore
uses a literal IID sequence of raw source-input packages for proposed
successive open-state subcycles.  It proves only finite-horizon stopped-sum
facts.  Connecting the unbounded construction to one global calendar-time
arrival/CTMC path still requires the remaining stopped-process regeneration
bridge.
-/

namespace GN21DriverSurgePricing

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

/-- The bounded index of the first literal exit among proposed subcycles in
one fixed open state.  The cap is a total fallback, so this is a genuine
prefix stopping index without an unproved pathwise termination assertion. -/
noncomputable def gn21RawSubcycleCappedExitIndex
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (cap : ℕ) :
    AppliedModelingLib.Probability.IIDStream.PrefixStoppingIndex
      (α := GN21RawCycleSeed) :=
  AppliedModelingLib.Probability.IIDStream.firstHitCappedStoppingIndex
    (gn21RawPostThinningRaceExitState state sigma)
    (measurableSet_gn21RawPostThinningRaceExitState state sigma hsigma) cap

/-- The finite source time accumulated by the proposed same-state subcycles
through their bounded first exit. -/
def gn21RawSubcycleCappedTime
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (cap : ℕ) : (Nat -> GN21RawCycleSeed) -> Real :=
  AppliedModelingLib.Probability.IIDStream.PrefixStoppingIndex.truncatedStoppedReward
    (gn21RawSubcycleCappedExitIndex state sigma hsigma cap)
    (gn21RawPostThinningRaceSubcycleTime state sigma) cap

/-- The finite source earning accumulated by the proposed same-state
subcycles through their bounded first exit. -/
def gn21RawSubcycleCappedEarning
    (state : Fin 2) (w : PricingFunction) (sigma : TripPolicy)
    (hsigma : MeasurableSet sigma) (cap : ℕ) :
    (Nat -> GN21RawCycleSeed) -> Real :=
  AppliedModelingLib.Probability.IIDStream.PrefixStoppingIndex.truncatedStoppedReward
    (gn21RawSubcycleCappedExitIndex state sigma hsigma cap)
    (gn21RawPostThinningRaceSubcycleEarning state w sigma) cap

/-- The unbounded same-state raw proposal time through the first literal exit.
The finite capped construction supplies the prefix events; the generic IID
stopped-reward theorem later establishes this total sum is integrable under
the paper's positive exit probability. -/
noncomputable def gn21RawSubcycleStoppedTime
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma) :
    (Nat -> GN21RawCycleSeed) -> Real :=
  AppliedModelingLib.Probability.IIDStream.firstHitStoppedReward
    (gn21RawPostThinningRaceExitState state sigma)
    (measurableSet_gn21RawPostThinningRaceExitState state sigma hsigma)
    (gn21RawPostThinningRaceSubcycleTime state sigma)

/-- The unbounded same-state raw proposal earnings through the first literal
exit.  Its integrability below uses only the source payout integrability
condition, not pointwise payoff measurability. -/
noncomputable def gn21RawSubcycleStoppedEarning
    (state : Fin 2) (w : PricingFunction) (sigma : TripPolicy)
    (hsigma : MeasurableSet sigma) :
    (Nat -> GN21RawCycleSeed) -> Real :=
  AppliedModelingLib.Probability.IIDStream.firstHitStoppedReward
    (gn21RawPostThinningRaceExitState state sigma)
    (measurableSet_gn21RawPostThinningRaceExitState state sigma hsigma)
    (gn21RawPostThinningRaceSubcycleEarning state w sigma)

/-- The bounded source exit index has the exact IID geometric continuation
probability, stated at the source raw-seed product measure. -/
theorem measure_gn21RawSubcycleCappedExitIndex_continuationEvent
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (cap n : Nat) :
    (gn21RawCycleSeedPathMeasure muI muJ arrivalI arrivalJ switchIJ switchJI)
      ((gn21RawSubcycleCappedExitIndex state sigma hsigma cap).continuationEvent n) =
      if n ≤ cap then
        ((gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI)
          (gn21RawPostThinningRaceExitState state sigma)ᶜ) ^ n else 0 := by
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  letI : IsProbabilityMeasure P := by
    dsimp [P]
    exact isProbabilityMeasure_gn21RawCycleSeedMeasure
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI
  simpa [gn21RawCycleSeedPathMeasure,
    AppliedModelingLib.Probability.IIDStream.measure,
    gn21RawSubcycleCappedExitIndex, P] using
    (AppliedModelingLib.Probability.IIDStream.measure_continuationEvent_firstHitCappedStoppingIndex
      P (gn21RawPostThinningRaceExitState state sigma)
      (measurableSet_gn21RawPostThinningRaceExitState state sigma hsigma) cap n)

/-- The literal raw exit event has positive probability under the paper's
positive source rates and feasible positive-mass policy domain. -/
theorem measureReal_gn21RawPostThinningRaceExitState_pos
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) :
    ((gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI)
      (gn21RawPostThinningRaceExitState state sigma)).toReal > 0 := by
  fin_cases state
  · change ((gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI)
      (gn21RawPostThinningRaceExitState 0 sigma)).toReal > 0
    rw [measure_gn21RawPostThinningRaceExitState_zero_toReal_eq_crossSubcycleProb
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI sigma hsigma hsigma_subset
      (by simpa [gn21CycleMarkLaw] using hmass)]
    exact gn21CrossSubcycleProb_pos_of_primitives
      muI arrivalI switchIJ switchJI sigma harrivalI hswitchIJ
      (add_pos hswitchIJ hswitchJI) hsigma hsigma_subset
      (by simpa [gn21CycleMarkLaw] using hmass)
  · change ((gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI)
      (gn21RawPostThinningRaceExitState 1 sigma)).toReal > 0
    rw [measure_gn21RawPostThinningRaceExitState_one_toReal_eq_crossSubcycleProb
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI sigma hsigma hsigma_subset
      (by simpa [gn21CycleMarkLaw] using hmass)]
    exact gn21CrossSubcycleProb_pos_of_primitives
      muJ arrivalJ switchJI switchIJ sigma harrivalJ hswitchJI
      (add_pos hswitchJI hswitchIJ) hsigma hsigma_subset
      (by simpa [gn21CycleMarkLaw] using hmass)

/-- In either start state, the literal raw exit probability is exactly the
paper's cross-subcycle probability. -/
theorem measureReal_gn21RawPostThinningRaceExitState_eq_crossSubcycleProb
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) :
    ((gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI)
      (gn21RawPostThinningRaceExitState state sigma)).toReal =
      gn21CrossSubcycleProb
        (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI (gn21ArrivalClockIndex state))
        (singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma)
        (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
          (RawTwoStateCTMC.switchClockIndex state))
        (gn21ExitWeightIntegral (gn21CycleMarkLaw muI muJ state)
          (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (gn21ArrivalClockIndex state))
          (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (RawTwoStateCTMC.switchClockIndex state))
          (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (RawTwoStateCTMC.switchClockIndex
              (AppliedModelingLib.Probability.TwoStateSwitching.otherState state)))
          sigma) := by
  fin_cases state
  · simpa [gn21CycleMarkLaw, gn21CycleClockRate, gn21ArrivalClockIndex,
      RawTwoStateCTMC.switchClockIndex,
      AppliedModelingLib.Probability.TwoStateSwitching.otherState] using
      (measure_gn21RawPostThinningRaceExitState_zero_toReal_eq_crossSubcycleProb
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI sigma hsigma hsigma_subset
        (by simpa [gn21CycleMarkLaw] using hmass))
  · simpa [gn21CycleMarkLaw, gn21CycleClockRate, gn21ArrivalClockIndex,
      RawTwoStateCTMC.switchClockIndex,
      AppliedModelingLib.Probability.TwoStateSwitching.otherState] using
      (measure_gn21RawPostThinningRaceExitState_one_toReal_eq_crossSubcycleProb
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI sigma hsigma hsigma_subset
        (by simpa [gn21CycleMarkLaw] using hmass))

/-- Under the source primitives, the IID raw proposal construction reaches a
literal exit almost surely.  This is a statement about the proposal model;
identification with a single calendar-time path is a separate bridge. -/
theorem ae_exists_gn21RawPostThinningRaceExit
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) :
    ∀ᵐ omega ∂gn21RawCycleSeedPathMeasure muI muJ arrivalI arrivalJ switchIJ switchJI,
      ∃ n, omega n ∈ gn21RawPostThinningRaceExitState state sigma := by
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let E := gn21RawPostThinningRaceExitState state sigma
  letI : IsProbabilityMeasure P := by
    dsimp [P]
    exact isProbabilityMeasure_gn21RawCycleSeedMeasure
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI
  apply AppliedModelingLib.Probability.IIDStream.ae_exists_firstHit P E
    (measurableSet_gn21RawPostThinningRaceExitState state sigma hsigma)
  have hreal : 0 < (P E).toReal := by
    simpa [P, E] using
      (measureReal_gn21RawPostThinningRaceExitState_pos
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hsigma_subset hmass)
  simpa [P, E, gn21RawCycleSeedPathMeasure,
    AppliedModelingLib.Probability.IIDStream.measure] using
    (ENNReal.toReal_pos_iff.mp hreal).1

/-- The real raw no-exit probability is strictly below one.  This is the
finite-horizon geometric summability input; it is derived from the literal
exit event rather than assumed as a renewal parameter. -/
theorem measureReal_gn21RawPostThinningRaceNoExit_lt_one
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) :
    ((gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI)
      (gn21RawPostThinningRaceExitState state sigma)ᶜ).toReal < 1 := by
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let E := gn21RawPostThinningRaceExitState state sigma
  letI : IsProbabilityMeasure P := by
    dsimp [P]
    exact isProbabilityMeasure_gn21RawCycleSeedMeasure
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI
  apply AppliedModelingLib.Probability.IIDStream.measureReal_compl_lt_one_of_pos
    P E (measurableSet_gn21RawPostThinningRaceExitState state sigma hsigma)
  have hreal : 0 < (P E).toReal := by
    simpa [P, E] using
      (measureReal_gn21RawPostThinningRaceExitState_pos
        muI muJ arrivalI arrivalJ switchIJ switchJI
        harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hsigma_subset hmass)
  exact (ENNReal.toReal_pos_iff.mp hreal).1

/-- The literal raw no-exit probabilities form a summable geometric tail. -/
theorem summable_measureReal_gn21RawPostThinningRaceNoExit_pow
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) :
    Summable fun n : Nat =>
      ((gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI)
        (gn21RawPostThinningRaceExitState state sigma)ᶜ).toReal ^ n := by
  apply summable_geometric_of_lt_one ENNReal.toReal_nonneg
  exact measureReal_gn21RawPostThinningRaceNoExit_lt_one
    muI muJ arrivalI arrivalJ switchIJ switchJI
    harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hsigma_subset hmass

/-- The literal no-exit geometric multiplier is the reciprocal of the
Appendix-D cross-subcycle probability. -/
theorem tsum_measureReal_gn21RawPostThinningRaceNoExit_pow_eq_inv_crossSubcycleProb
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma) :
    (∑' n : Nat,
      ((gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI)
        (gn21RawPostThinningRaceExitState state sigma)ᶜ).toReal ^ n) =
      (gn21CrossSubcycleProb
        (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI (gn21ArrivalClockIndex state))
        (singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma)
        (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
          (RawTwoStateCTMC.switchClockIndex state))
        (gn21ExitWeightIntegral (gn21CycleMarkLaw muI muJ state)
          (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (gn21ArrivalClockIndex state))
          (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (RawTwoStateCTMC.switchClockIndex state))
          (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (RawTwoStateCTMC.switchClockIndex
              (AppliedModelingLib.Probability.TwoStateSwitching.otherState state)))
          sigma))⁻¹ := by
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let E := gn21RawPostThinningRaceExitState state sigma
  letI : IsProbabilityMeasure P := by
    dsimp [P]
    exact isProbabilityMeasure_gn21RawCycleSeedMeasure
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI
  have hE_pos : 0 < P E := by
    have hreal : 0 < (P E).toReal := by
      simpa [P, E] using
        (measureReal_gn21RawPostThinningRaceExitState_pos
          muI muJ arrivalI arrivalJ switchIJ switchJI
          harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hsigma_subset hmass)
    exact (ENNReal.toReal_pos_iff.mp hreal).1
  rw [AppliedModelingLib.Probability.IIDStream.tsum_firstHitContinuation_eq_inv_measureReal
    P E (measurableSet_gn21RawPostThinningRaceExitState state sigma hsigma) hE_pos]
  rw [measureReal_gn21RawPostThinningRaceExitState_eq_crossSubcycleProb
    muI muJ arrivalI arrivalJ switchIJ switchJI
    harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hsigma_subset hmass]

/-- The literal raw proposal time through the first exit is integrable.  The
final subcycle may jointly determine its exit and duration, so this uses
prefix measurability rather than independence of an exit count from the
terminal duration. -/
theorem integrable_gn21RawSubcycleStoppedTime
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma)
    (htime : IntegrableOn (fun tau : TripLength => tau) sigma
      (gn21CycleMarkLaw muI muJ state)) :
    Integrable (gn21RawSubcycleStoppedTime state sigma hsigma)
      (gn21RawCycleSeedPathMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let E := gn21RawPostThinningRaceExitState state sigma
  let r := gn21RawPostThinningRaceSubcycleTime state sigma
  letI : IsProbabilityMeasure P := by
    dsimp [P]
    exact isProbabilityMeasure_gn21RawCycleSeedMeasure
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI
  have hE_meas : MeasurableSet E :=
    measurableSet_gn21RawPostThinningRaceExitState state sigma hsigma
  have hE_pos : 0 < P E := by
    have hreal : 0 < (P E).toReal := by
      simpa [P, E] using
        (measureReal_gn21RawPostThinningRaceExitState_pos
          muI muJ arrivalI arrivalJ switchIJ switchJI
          harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hsigma_subset hmass)
    exact (ENNReal.toReal_pos_iff.mp hreal).1
  have hr_integrable : Integrable r P := by
    simpa [P, r] using integrable_gn21RawPostThinningRaceSubcycleTime
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hmass htime
  simpa [gn21RawCycleSeedPathMeasure, gn21RawSubcycleStoppedTime, P, E, r,
    AppliedModelingLib.Probability.IIDStream.measure] using
    (AppliedModelingLib.Probability.IIDStream.integrable_firstHitStoppedReward
      P E hE_meas hE_pos r hr_integrable)

/-- The literal raw proposal time through the first exit has the exact
geometric Wald expectation. -/
theorem integral_gn21RawSubcycleStoppedTime
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma)
    (htime : IntegrableOn (fun tau : TripLength => tau) sigma
      (gn21CycleMarkLaw muI muJ state)) :
    (∫ omega, gn21RawSubcycleStoppedTime state sigma hsigma omega
      ∂gn21RawCycleSeedPathMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) =
      (∑' n : Nat,
        ((gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI)
          (gn21RawPostThinningRaceExitState state sigma)ᶜ).toReal ^ n) *
      (∫ seed, gn21RawPostThinningRaceSubcycleTime state sigma seed
        ∂gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let E := gn21RawPostThinningRaceExitState state sigma
  let r := gn21RawPostThinningRaceSubcycleTime state sigma
  letI : IsProbabilityMeasure P := by
    dsimp [P]
    exact isProbabilityMeasure_gn21RawCycleSeedMeasure
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI
  have hE_meas : MeasurableSet E :=
    measurableSet_gn21RawPostThinningRaceExitState state sigma hsigma
  have hE_pos : 0 < P E := by
    have hreal : 0 < (P E).toReal := by
      simpa [P, E] using
        (measureReal_gn21RawPostThinningRaceExitState_pos
          muI muJ arrivalI arrivalJ switchIJ switchJI
          harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hsigma_subset hmass)
    exact (ENNReal.toReal_pos_iff.mp hreal).1
  have hr_integrable : Integrable r P := by
    simpa [P, r] using integrable_gn21RawPostThinningRaceSubcycleTime
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hmass htime
  simpa [gn21RawCycleSeedPathMeasure, gn21RawSubcycleStoppedTime, P, E, r,
    AppliedModelingLib.Probability.IIDStream.measure] using
    (AppliedModelingLib.Probability.IIDStream.integral_firstHitStoppedReward
      P E hE_meas hE_pos r hr_integrable)

/-- The literal raw first-exit time has the reciprocal cross-subcycle
probability multiplier times the Appendix-D one-subcycle time. -/
theorem integral_gn21RawSubcycleStoppedTime_eq_cross_inv_mul_subcycleLength
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma)
    (htime : IntegrableOn (fun tau : TripLength => tau) sigma
      (gn21CycleMarkLaw muI muJ state)) :
    (∫ omega, gn21RawSubcycleStoppedTime state sigma hsigma omega
      ∂gn21RawCycleSeedPathMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) =
      (gn21CrossSubcycleProb
        (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI (gn21ArrivalClockIndex state))
        (singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma)
        (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
          (RawTwoStateCTMC.switchClockIndex state))
        (gn21ExitWeightIntegral (gn21CycleMarkLaw muI muJ state)
          (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (gn21ArrivalClockIndex state))
          (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (RawTwoStateCTMC.switchClockIndex state))
          (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (RawTwoStateCTMC.switchClockIndex
              (AppliedModelingLib.Probability.TwoStateSwitching.otherState state)))
          sigma))⁻¹ *
      gn21SubcycleLength
        (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI (gn21ArrivalClockIndex state))
        (singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma)
        (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
          (RawTwoStateCTMC.switchClockIndex state))
        (gn21StateCycleTime (gn21CycleMarkLaw muI muJ state)
          (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (gn21ArrivalClockIndex state)) sigma) := by
  rw [integral_gn21RawSubcycleStoppedTime
    muI muJ arrivalI arrivalJ switchIJ switchJI
    harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hsigma_subset hmass htime,
    integral_gn21RawPostThinningRaceSubcycleTime_eq
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hmass htime,
    tsum_measureReal_gn21RawPostThinningRaceNoExit_pow_eq_inv_crossSubcycleProb
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hsigma_subset hmass]

/-- The raw first-exit state time is exactly the Appendix-D expected state
time in a larger renewal cycle. -/
theorem integral_gn21RawSubcycleStoppedTime_eq_expectedStateTimeInRenewalCycle
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma)
    (htime : IntegrableOn (fun tau : TripLength => tau) sigma
      (gn21CycleMarkLaw muI muJ state)) :
    (∫ omega, gn21RawSubcycleStoppedTime state sigma hsigma omega
      ∂gn21RawCycleSeedPathMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) =
      gn21ExpectedStateTimeInRenewalCycle
        (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI (gn21ArrivalClockIndex state))
        (singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma)
        (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
          (RawTwoStateCTMC.switchClockIndex state))
        (gn21StateCycleTime (gn21CycleMarkLaw muI muJ state)
          (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (gn21ArrivalClockIndex state)) sigma)
        (gn21ExitWeightIntegral (gn21CycleMarkLaw muI muJ state)
          (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (gn21ArrivalClockIndex state))
          (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (RawTwoStateCTMC.switchClockIndex state))
          (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (RawTwoStateCTMC.switchClockIndex
              (AppliedModelingLib.Probability.TwoStateSwitching.otherState state)))
          sigma) := by
  simpa [gn21ExpectedStateTimeInRenewalCycle, div_eq_mul_inv, mul_comm] using
    (integral_gn21RawSubcycleStoppedTime_eq_cross_inv_mul_subcycleLength
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hsigma_subset hmass htime)

/-- The literal raw proposal earnings through the first exit are integrable
under the source payout integrability condition. -/
theorem integrable_gn21RawSubcycleStoppedEarning
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (w : PricingFunction) (sigma : TripPolicy)
    (hsigma : MeasurableSet sigma)
    (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma)
    (hpayment : IntegrableOn w sigma (gn21CycleMarkLaw muI muJ state)) :
    Integrable (gn21RawSubcycleStoppedEarning state w sigma hsigma)
      (gn21RawCycleSeedPathMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let E := gn21RawPostThinningRaceExitState state sigma
  let r := gn21RawPostThinningRaceSubcycleEarning state w sigma
  letI : IsProbabilityMeasure P := by
    dsimp [P]
    exact isProbabilityMeasure_gn21RawCycleSeedMeasure
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI
  have hE_meas : MeasurableSet E :=
    measurableSet_gn21RawPostThinningRaceExitState state sigma hsigma
  have hE_pos : 0 < P E := by
    have hreal : 0 < (P E).toReal := by
      simpa [P, E] using
        (measureReal_gn21RawPostThinningRaceExitState_pos
          muI muJ arrivalI arrivalJ switchIJ switchJI
          harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hsigma_subset hmass)
    exact (ENNReal.toReal_pos_iff.mp hreal).1
  have hr_integrable : Integrable r P := by
    simpa [P, r] using integrable_gn21RawPostThinningRaceSubcycleEarning
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI state w sigma hsigma hmass hpayment
  simpa [gn21RawCycleSeedPathMeasure, gn21RawSubcycleStoppedEarning, P, E, r,
    AppliedModelingLib.Probability.IIDStream.measure] using
    (AppliedModelingLib.Probability.IIDStream.integrable_firstHitStoppedReward
      P E hE_meas hE_pos r hr_integrable)

/-- The literal raw proposal earnings through the first exit have the exact
geometric Wald expectation. -/
theorem integral_gn21RawSubcycleStoppedEarning
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (w : PricingFunction) (sigma : TripPolicy)
    (hsigma : MeasurableSet sigma)
    (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma)
    (hpayment : IntegrableOn w sigma (gn21CycleMarkLaw muI muJ state)) :
    (∫ omega, gn21RawSubcycleStoppedEarning state w sigma hsigma omega
      ∂gn21RawCycleSeedPathMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) =
      (∑' n : Nat,
        ((gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI)
          (gn21RawPostThinningRaceExitState state sigma)ᶜ).toReal ^ n) *
      (∫ seed, gn21RawPostThinningRaceSubcycleEarning state w sigma seed
        ∂gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let E := gn21RawPostThinningRaceExitState state sigma
  let r := gn21RawPostThinningRaceSubcycleEarning state w sigma
  letI : IsProbabilityMeasure P := by
    dsimp [P]
    exact isProbabilityMeasure_gn21RawCycleSeedMeasure
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI
  have hE_meas : MeasurableSet E :=
    measurableSet_gn21RawPostThinningRaceExitState state sigma hsigma
  have hE_pos : 0 < P E := by
    have hreal : 0 < (P E).toReal := by
      simpa [P, E] using
        (measureReal_gn21RawPostThinningRaceExitState_pos
          muI muJ arrivalI arrivalJ switchIJ switchJI
          harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hsigma_subset hmass)
    exact (ENNReal.toReal_pos_iff.mp hreal).1
  have hr_integrable : Integrable r P := by
    simpa [P, r] using integrable_gn21RawPostThinningRaceSubcycleEarning
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI state w sigma hsigma hmass hpayment
  simpa [gn21RawCycleSeedPathMeasure, gn21RawSubcycleStoppedEarning, P, E, r,
    AppliedModelingLib.Probability.IIDStream.measure] using
    (AppliedModelingLib.Probability.IIDStream.integral_firstHitStoppedReward
      P E hE_meas hE_pos r hr_integrable)

/-- The unbounded raw proposal earning has the geometric-series multiplier
times the paper's literal one-subcycle earning expression. -/
theorem integral_gn21RawSubcycleStoppedEarning_eq_geometric_tsum_mul_subcycleEarning
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (w : PricingFunction) (sigma : TripPolicy)
    (hsigma : MeasurableSet sigma)
    (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma)
    (hpayment : IntegrableOn w sigma (gn21CycleMarkLaw muI muJ state)) :
    (∫ omega, gn21RawSubcycleStoppedEarning state w sigma hsigma omega
      ∂gn21RawCycleSeedPathMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) =
      (∑' n : Nat,
        ((gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI)
          (gn21RawPostThinningRaceExitState state sigma)ᶜ).toReal ^ n) *
      gn21SubcycleEarning
        (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI (gn21ArrivalClockIndex state))
        (singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma)
        (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
          (RawTwoStateCTMC.switchClockIndex state))
        (gn21StateMeanEarning (gn21CycleMarkLaw muI muJ state) w sigma) := by
  rw [integral_gn21RawSubcycleStoppedEarning
    muI muJ arrivalI arrivalJ switchIJ switchJI
    harrivalI harrivalJ hswitchIJ hswitchJI state w sigma hsigma hsigma_subset hmass hpayment,
    integral_gn21RawPostThinningRaceSubcycleEarning_eq
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI state w sigma hsigma hmass hpayment]

/-- The raw first-exit state earnings are exactly the Appendix-D expected
state earnings in a larger renewal cycle. -/
theorem integral_gn21RawSubcycleStoppedEarning_eq_expectedStateEarningInRenewalCycle
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (w : PricingFunction) (sigma : TripPolicy)
    (hsigma : MeasurableSet sigma)
    (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma)
    (hpayment : IntegrableOn w sigma (gn21CycleMarkLaw muI muJ state)) :
    (∫ omega, gn21RawSubcycleStoppedEarning state w sigma hsigma omega
      ∂gn21RawCycleSeedPathMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) =
      gn21ExpectedStateEarningInRenewalCycle
        (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI (gn21ArrivalClockIndex state))
        (singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma)
        (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
          (RawTwoStateCTMC.switchClockIndex state))
        (gn21StateMeanEarning (gn21CycleMarkLaw muI muJ state) w sigma)
        (gn21ExitWeightIntegral (gn21CycleMarkLaw muI muJ state)
          (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (gn21ArrivalClockIndex state))
          (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (RawTwoStateCTMC.switchClockIndex state))
          (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (RawTwoStateCTMC.switchClockIndex
              (AppliedModelingLib.Probability.TwoStateSwitching.otherState state)))
          sigma) := by
  rw [integral_gn21RawSubcycleStoppedEarning_eq_geometric_tsum_mul_subcycleEarning
    muI muJ arrivalI arrivalJ switchIJ switchJI
    harrivalI harrivalJ hswitchIJ hswitchJI state w sigma hsigma hsigma_subset hmass hpayment,
    tsum_measureReal_gn21RawPostThinningRaceNoExit_pow_eq_inv_crossSubcycleProb
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hsigma_subset hmass]
  simp only [gn21ExpectedStateEarningInRenewalCycle, div_eq_mul_inv, mul_comm]

/-- Finite-horizon Wald identity for the literal source subcycle-time
observable.  The stopping decision may depend on the current raw subcycle,
so this result uses the prefix-stopping identity rather than an unwarranted
independence assertion between the exit count and subcycle time. -/
theorem integral_gn21RawSubcycleCappedTime_eq_geometric_sum_mul
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma)
    (htime : IntegrableOn (fun tau : TripLength => tau) sigma
      (gn21CycleMarkLaw muI muJ state))
    (cap : Nat) :
    (∫ omega, gn21RawSubcycleCappedTime state sigma hsigma cap omega
      ∂gn21RawCycleSeedPathMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) =
      (∑ n ∈ Finset.range (cap + 1),
        ((gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI)
          (gn21RawPostThinningRaceExitState state sigma)ᶜ).toReal ^ n) *
      (∫ seed, gn21RawPostThinningRaceSubcycleTime state sigma seed
        ∂gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) := by
  let P := gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  let τ := gn21RawSubcycleCappedExitIndex state sigma hsigma cap
  let r := gn21RawPostThinningRaceSubcycleTime state sigma
  letI : IsProbabilityMeasure P := by
    dsimp [P]
    exact isProbabilityMeasure_gn21RawCycleSeedMeasure
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI
  have hr_meas : Measurable r := by
    let race := gn21RawPostThinningRaceSeed state sigma
    have hrace : Measurable race :=
      measurable_gn21RawPostThinningRaceSeed state sigma hsigma
    have hminimum : Measurable (gn21RawPostThinningRaceMinimum state sigma) := by
      exact AppliedModelingLib.Probability.measurable_exponentialRaceMinimum.comp
        ((measurable_fst.comp hrace).prodMk
          ((measurable_fst.comp measurable_snd).comp hrace))
    have hcontribution : Measurable
        (gn21RawPostThinningRaceAcceptedContribution state sigma (fun tau => tau)) :=
      measurable_gn21RawPostThinningRaceAcceptedContribution state sigma
        (fun tau => tau) hsigma measurable_id
    simpa [r, gn21RawPostThinningRaceSubcycleTime] using
      hminimum.add hcontribution
  have hr_integrable : Integrable r P := by
    simpa [P, r] using integrable_gn21RawPostThinningRaceSubcycleTime
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hmass htime
  have hwald :=
    AppliedModelingLib.Probability.IIDStream.PrefixStoppingIndex.integral_truncatedStoppedReward
      P τ r hr_meas hr_integrable cap
  have hcont (n : Nat) (hn : n ∈ Finset.range (cap + 1)) :
      (AppliedModelingLib.Probability.IIDStream.measure P).real
        (τ.continuationEvent n) =
      (P (gn21RawPostThinningRaceExitState state sigma)ᶜ).toReal ^ n := by
    have hnle : n ≤ cap := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
    change ((gn21RawCycleSeedPathMeasure muI muJ arrivalI arrivalJ switchIJ switchJI)
      ((gn21RawSubcycleCappedExitIndex state sigma hsigma cap).continuationEvent n)).toReal = _
    rw [measure_gn21RawSubcycleCappedExitIndex_continuationEvent
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma cap n,
      if_pos hnle]
    simpa [P] using ENNReal.toReal_pow
  change (∫ omega, AppliedModelingLib.Probability.IIDStream.PrefixStoppingIndex.truncatedStoppedReward
      τ r cap omega
      ∂AppliedModelingLib.Probability.IIDStream.measure P) = _
  rw [hwald]
  congr 1
  · apply Finset.sum_congr rfl
    intro n hn
    exact hcont n hn

/-- Finite-horizon expected same-state source time is the geometric partial
sum times the literal one-subcycle mean from the paper's components. -/
theorem integral_gn21RawSubcycleCappedTime_eq_geometric_sum_mul_subcycleLength
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma)
    (htime : IntegrableOn (fun tau : TripLength => tau) sigma
      (gn21CycleMarkLaw muI muJ state))
    (cap : Nat) :
    (∫ omega, gn21RawSubcycleCappedTime state sigma hsigma cap omega
      ∂gn21RawCycleSeedPathMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) =
      (∑ n ∈ Finset.range (cap + 1),
        ((gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI)
          (gn21RawPostThinningRaceExitState state sigma)ᶜ).toReal ^ n) *
      gn21SubcycleLength
        (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI (gn21ArrivalClockIndex state))
        (singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma)
        (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
          (RawTwoStateCTMC.switchClockIndex state))
        (gn21StateCycleTime (gn21CycleMarkLaw muI muJ state)
          (gn21CycleClockRate arrivalI arrivalJ switchIJ switchJI
            (gn21ArrivalClockIndex state)) sigma) := by
  rw [integral_gn21RawSubcycleCappedTime_eq_geometric_sum_mul
    muI muJ arrivalI arrivalJ switchIJ switchJI
    harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hmass htime cap,
    integral_gn21RawPostThinningRaceSubcycleTime_eq
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hmass htime]

/-- The expectations of bounded repeated-subcycle times converge to the
geometric-series multiplier times the literal one-subcycle mean.  This is an
expectation-limit statement only; the remaining unbounded stopped-sum
integrability and global calendar-path bridge are deliberately separate. -/
theorem tendsto_integral_gn21RawSubcycleCappedTime
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : Real)
    [IsProbabilityMeasure muI] [IsProbabilityMeasure muJ]
    (harrivalI : 0 < arrivalI) (harrivalJ : 0 < arrivalJ)
    (hswitchIJ : 0 < switchIJ) (hswitchJI : 0 < switchJI)
    (state : Fin 2) (sigma : TripPolicy) (hsigma : MeasurableSet sigma)
    (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (hmass : 0 < singleStateTripMass (gn21CycleMarkLaw muI muJ state) sigma)
    (htime : IntegrableOn (fun tau : TripLength => tau) sigma
      (gn21CycleMarkLaw muI muJ state)) :
    Filter.Tendsto
      (fun cap : Nat => ∫ omega, gn21RawSubcycleCappedTime state sigma hsigma cap omega
        ∂gn21RawCycleSeedPathMeasure muI muJ arrivalI arrivalJ switchIJ switchJI)
      Filter.atTop
      (nhds
        ((∑' n : Nat,
          ((gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI)
            (gn21RawPostThinningRaceExitState state sigma)ᶜ).toReal ^ n) *
          (∫ seed, gn21RawPostThinningRaceSubcycleTime state sigma seed
            ∂gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI))) := by
  let q := ((gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI)
    (gn21RawPostThinningRaceExitState state sigma)ᶜ).toReal
  let mean := ∫ seed, gn21RawPostThinningRaceSubcycleTime state sigma seed
    ∂gn21RawCycleSeedMeasure muI muJ arrivalI arrivalJ switchIJ switchJI
  have hsum : Summable fun n : Nat => q ^ n := by
    simpa [q] using summable_measureReal_gn21RawPostThinningRaceNoExit_pow
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hsigma_subset hmass
  have htendsto : Filter.Tendsto
      (fun cap : Nat => ∑ n ∈ Finset.range (cap + 1), q ^ n)
      Filter.atTop (nhds (∑' n : Nat, q ^ n)) := by
    simpa only [Function.comp_apply] using
      hsum.hasSum.tendsto_sum_nat.comp (Filter.tendsto_add_atTop_nat 1)
  have heq :
      (fun cap : Nat => ∫ omega, gn21RawSubcycleCappedTime state sigma hsigma cap omega
        ∂gn21RawCycleSeedPathMeasure muI muJ arrivalI arrivalJ switchIJ switchJI) =
      fun cap : Nat => (∑ n ∈ Finset.range (cap + 1), q ^ n) * mean := by
    funext cap
    simpa [q, mean] using integral_gn21RawSubcycleCappedTime_eq_geometric_sum_mul
      muI muJ arrivalI arrivalJ switchIJ switchJI
      harrivalI harrivalJ hswitchIJ hswitchJI state sigma hsigma hmass htime cap
  rw [heq]
  simpa [q, mean] using htendsto.mul_const mean

end

end GN21DriverSurgePricing
