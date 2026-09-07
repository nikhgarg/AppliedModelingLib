import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalHeadTail
import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalIncrementBoundary
import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalDeterministicResidualTail

/-!
# Alternating two-state switching paths

This module constructs a two-state switching sample path directly from the
two alternating holding-time streams.  It intentionally establishes only the
path-level and measurability layer.  Identifying its law with a particular
two-state CTMC transition kernel, and proving random-time restart, are
separate probabilistic obligations.
-/

namespace AppliedModelingLib.Probability

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace TwoStateSwitching

open Filter

/-- The unique state other than `i` in a two-state system. -/
def otherState (i : Fin 2) : Fin 2 := if i = 0 then 1 else 0

@[simp] theorem otherState_zero : otherState 0 = 1 := by
  simp [otherState]

@[simp] theorem otherState_one : otherState 1 = 0 := by
  simp [otherState]

theorem otherState_ne (i : Fin 2) : otherState i ≠ i := by
  fin_cases i <;> simp

theorem otherState_otherState (i : Fin 2) : otherState (otherState i) = i := by
  fin_cases i <;> simp

/-- State occupied after exactly `n` switches from `initial`. -/
def stateAfterSwitches (initial : Fin 2) (n : Nat) : Fin 2 :=
  if Even n then initial else otherState initial

@[simp] theorem stateAfterSwitches_even (initial : Fin 2) {n : Nat}
    (hn : Even n) : stateAfterSwitches initial n = initial := by
  simp [stateAfterSwitches, hn]

@[simp] theorem stateAfterSwitches_odd (initial : Fin 2) {n : Nat}
    (hn : Odd n) : stateAfterSwitches initial n = otherState initial := by
  rw [stateAfterSwitches, if_neg]
  exact Nat.not_even_iff_odd.mpr hn

/-- Switching for `m` holds and then for `n` more holds is the same as
switching for their sum. -/
theorem stateAfterSwitches_add (initial : Fin 2) (m n : Nat) :
    stateAfterSwitches initial (m + n) =
      stateAfterSwitches (stateAfterSwitches initial m) n := by
  rcases m.even_or_odd' with ⟨a, rfl | rfl⟩ <;>
    rcases n.even_or_odd' with ⟨b, rfl | rfl⟩
  · have hm : Even (2 * a) := ⟨a, by omega⟩
    have hn : Even (2 * b) := ⟨b, by omega⟩
    have hsum : Even (2 * a + 2 * b) := hm.add hn
    rw [stateAfterSwitches_even initial hsum,
      stateAfterSwitches_even initial hm,
      stateAfterSwitches_even initial hn]
  · have hm : Even (2 * a) := ⟨a, by omega⟩
    have hn : Odd (2 * b + 1) := ⟨b, by omega⟩
    have hsum : Odd (2 * a + (2 * b + 1)) := hm.add_odd hn
    rw [stateAfterSwitches_odd initial hsum,
      stateAfterSwitches_even initial hm,
      stateAfterSwitches_odd initial hn]
  · have hm : Odd (2 * a + 1) := ⟨a, by omega⟩
    have hn : Even (2 * b) := ⟨b, by omega⟩
    have hsum : Odd ((2 * a + 1) + 2 * b) := hm.add_even hn
    rw [stateAfterSwitches_odd initial hsum,
      stateAfterSwitches_odd initial hm,
      stateAfterSwitches_even (otherState initial) hn]
  · have hm : Odd (2 * a + 1) := ⟨a, by omega⟩
    have hn : Odd (2 * b + 1) := ⟨b, by omega⟩
    have hsum : Even ((2 * a + 1) + (2 * b + 1)) := hm.add_odd hn
    rw [stateAfterSwitches_even initial hsum,
      stateAfterSwitches_odd initial hm,
      stateAfterSwitches_odd (otherState initial) hn,
      otherState_otherState]

/-- The `n`th holding time of an alternating two-state path.  The `n / 2`th
entry of the current state's holding-time stream is consumed. -/
def alternatingGap (initial : Fin 2) (switchGaps : Fin 2 -> Nat -> Real)
    (n : Nat) : Real :=
  switchGaps (stateAfterSwitches initial n) (n / 2)

/-- The whole alternating holding-time sequence encoded by two state-specific
holding-time streams. -/
def alternatingGaps (initial : Fin 2) :
    (Fin 2 -> Nat -> Real) -> Nat -> Real :=
  fun switchGaps n => alternatingGap initial switchGaps n

/-- Recover state-indexed holding-time streams from a single alternating
sequence whose first hold belongs to `initial`.  This is the literal inverse
of `alternatingGaps`: even coordinates belong to the current initial state
and odd coordinates to the other state. -/
def switchGapsOfAlternating (initial : Fin 2) (gaps : Nat -> Real) :
    Fin 2 -> Nat -> Real :=
  fun state n => if state = initial then gaps (2 * n) else gaps (2 * n + 1)

/-- The state-indexed streams strictly after `k` completed visits to each
state.  This deterministic-index shift is distinct from the calendar-time
residual construction below. -/
def switchGapsAfterPairs (switchGaps : Fin 2 -> Nat -> Real) (k : Nat) :
    Fin 2 -> Nat -> Real :=
  fun state => PoissonProcess.futureInterarrival k (switchGaps state)

/-- Residual state-indexed visit streams when the current active visit of
`initial` has already lasted `elapsed`.  Only the first active coordinate is
reduced; every later active coordinate and every inactive coordinate is
retained literally. -/
def switchGapsAfterActiveElapsed (initial : Fin 2)
    (switchGaps : Fin 2 -> Nat -> Real) (elapsed : Real) :
    Fin 2 -> Nat -> Real :=
  fun state n =>
    if state = initial then
      if n = 0 then switchGaps state 0 - elapsed else switchGaps state n
    else switchGaps state n

/-- Reassemble the two state-specific gap streams from an ordered pair. -/
def twoStateGapsOfPair : (Nat -> Real) × (Nat -> Real) -> Fin 2 -> Nat -> Real
  | (left, right), 0 => left
  | (left, right), 1 => right

/-- Relabel the two state-indexed streams by the nontrivial permutation of
`Fin 2`.  This is a deterministic coordinate operation, used to transport
state-zero alternating facts to state-one starts without changing any clock
law by assertion. -/
def swapStateIndexedGaps (switchGaps : Fin 2 -> Nat -> Real) :
    Fin 2 -> Nat -> Real :=
  fun state => switchGaps (otherState state)

/-- Relabeling the two finite state coordinates is Borel measurable. -/
theorem measurable_swapStateIndexedGaps : Measurable swapStateIndexedGaps := by
  apply measurable_pi_lambda
  intro state
  apply measurable_pi_lambda
  intro n
  exact (measurable_pi_apply n).comp (measurable_pi_apply (otherState state))

/-- The ordered-pair representation commutes with swapping its two source
coordinates and relabeling the two states. -/
theorem twoStateGapsOfPair_swap_eq_swapStateIndexedGaps
    (pair : (Nat -> Real) × (Nat -> Real)) :
    twoStateGapsOfPair (Prod.swap pair) =
      swapStateIndexedGaps (twoStateGapsOfPair pair) := by
  funext state n
  fin_cases state <;> simp [twoStateGapsOfPair, swapStateIndexedGaps]

theorem measurable_twoStateGapsOfPair : Measurable twoStateGapsOfPair := by
  apply measurable_pi_lambda
  intro state
  fin_cases state
  · exact measurable_fst
  · exact measurable_snd

/-- Even-numbered alternating holds consume the corresponding gap of the
initial-state stream. -/
theorem alternatingGap_two_mul
    (initial : Fin 2) (switchGaps : Fin 2 -> Nat -> Real) (n : Nat) :
    alternatingGap initial switchGaps (2 * n) = switchGaps initial n := by
  have hEven : Even (2 * n) := ⟨n, by omega⟩
  have hdiv : (2 * n) / 2 = n := by omega
  simp [alternatingGap, hEven, hdiv]

/-- Odd-numbered alternating holds consume the corresponding gap of the
opposite-state stream. -/
theorem alternatingGap_two_mul_add_one
    (initial : Fin 2) (switchGaps : Fin 2 -> Nat -> Real) (n : Nat) :
    alternatingGap initial switchGaps (2 * n + 1) =
      switchGaps (otherState initial) n := by
  have hOdd : Odd (2 * n + 1) := ⟨n, by omega⟩
  have hdiv : (2 * n + 1) / 2 = n := by omega
  rw [alternatingGap, stateAfterSwitches_odd initial hOdd, hdiv]

/-- Deinterleaving and immediately reinterleaving an alternating sequence is
pathwise exact. -/
theorem alternatingGaps_switchGapsOfAlternating
    (initial : Fin 2) (gaps : Nat -> Real) :
    alternatingGaps initial (switchGapsOfAlternating initial gaps) = gaps := by
  funext n
  rcases n.even_or_odd' with ⟨k, rfl | rfl⟩
  · simp only [alternatingGaps]
    rw [alternatingGap_two_mul]
    simp [switchGapsOfAlternating]
  · simp only [alternatingGaps]
    rw [alternatingGap_two_mul_add_one]
    simp [switchGapsOfAlternating, otherState_ne]

/-- After exactly `2 * k` alternating holds, the remaining literal
alternating coordinates are those obtained by shifting both state-specific
visit streams by `k`. -/
theorem futureInterarrival_two_mul_alternatingGaps
    (initial : Fin 2) (switchGaps : Fin 2 -> Nat -> Real) (k : Nat) :
    PoissonProcess.futureInterarrival (2 * k)
      (alternatingGaps initial switchGaps) =
      alternatingGaps initial (switchGapsAfterPairs switchGaps k) := by
  funext n
  rcases n.even_or_odd' with ⟨m, rfl | rfl⟩
  · have hindex : 2 * k + 2 * m = 2 * (k + m) := by omega
    change alternatingGap initial switchGaps (2 * k + 2 * m) =
      alternatingGap initial (switchGapsAfterPairs switchGaps k) (2 * m)
    rw [hindex, alternatingGap_two_mul, alternatingGap_two_mul]
    rfl
  · have hindex : 2 * k + (2 * m + 1) = 2 * (k + m) + 1 := by omega
    change alternatingGap initial switchGaps (2 * k + (2 * m + 1)) =
      alternatingGap initial (switchGapsAfterPairs switchGaps k) (2 * m + 1)
    rw [hindex, alternatingGap_two_mul_add_one, alternatingGap_two_mul_add_one]
    rfl

/-- Deinterleaving an alternating first-gap residual changes exactly the
first visit duration of the active state. -/
theorem switchGapsOfAlternating_firstGapResidualTail
    (initial : Fin 2) (switchGaps : Fin 2 -> Nat -> Real) (elapsed : Real) :
    switchGapsOfAlternating initial
      (PoissonProcess.firstGapResidualTail elapsed
        (alternatingGaps initial switchGaps)) =
      switchGapsAfterActiveElapsed initial switchGaps elapsed := by
  funext state n
  by_cases hstate : state = initial
  · subst state
    cases n with
    | zero =>
        rw [show switchGapsOfAlternating initial
          (PoissonProcess.firstGapResidualTail elapsed
            (alternatingGaps initial switchGaps)) initial 0 =
              PoissonProcess.firstGapResidualTail elapsed
                (alternatingGaps initial switchGaps) 0 by
              simp [switchGapsOfAlternating]]
        simp [switchGapsAfterActiveElapsed]
        change PoissonProcess.interarrival 0 (alternatingGaps initial switchGaps) - elapsed =
          switchGaps initial 0 - elapsed
        change alternatingGap initial switchGaps 0 - elapsed = switchGaps initial 0 - elapsed
        rw [show 0 = 2 * 0 by rfl, alternatingGap_two_mul]
    | succ n =>
        rw [show switchGapsOfAlternating initial
          (PoissonProcess.firstGapResidualTail elapsed
            (alternatingGaps initial switchGaps)) initial (n + 1) =
              PoissonProcess.firstGapResidualTail elapsed
                (alternatingGaps initial switchGaps) (2 * (n + 1)) by
              simp [switchGapsOfAlternating]]
        simp [switchGapsAfterActiveElapsed]
        change PoissonProcess.interarrival (2 * (n + 1))
          (alternatingGaps initial switchGaps) = switchGaps initial (n + 1)
        change alternatingGap initial switchGaps (2 * (n + 1)) = switchGaps initial (n + 1)
        rw [alternatingGap_two_mul]
  · rw [switchGapsOfAlternating]
    simp only [if_neg hstate]
    simp only [switchGapsAfterActiveElapsed, if_neg hstate]
    rw [show 2 * n + 1 = (2 * n) + 1 by omega]
    simp [PoissonProcess.firstGapResidualTail]
    change alternatingGap initial switchGaps (2 * n + 1) = switchGaps state n
    rw [alternatingGap_two_mul_add_one]
    have hother : state = otherState initial := by
      fin_cases initial <;> fin_cases state <;> simp_all
    rw [hother]

/-- The elapsed time before the `(2 * k)`th alternating hold is the sum of
the first `k` visit durations from each state-specific stream. -/
theorem arrivalPrefix_two_mul_alternatingGaps
    (initial : Fin 2) (switchGaps : Fin 2 -> Nat -> Real) (k : Nat) :
    PoissonProcess.arrivalPrefix (2 * k) (alternatingGaps initial switchGaps) =
      PoissonProcess.arrivalPrefix k (switchGaps initial) +
        PoissonProcess.arrivalPrefix k (switchGaps (otherState initial)) := by
  induction k with
  | zero =>
      simp [PoissonProcess.arrivalPrefix]
  | succ k ih =>
      have ih' :
          (∑ i ∈ Finset.range (2 * k),
            PoissonProcess.interarrival i (alternatingGaps initial switchGaps)) =
            (∑ i ∈ Finset.range k, PoissonProcess.interarrival i (switchGaps initial)) +
              ∑ i ∈ Finset.range k,
                PoissonProcess.interarrival i (switchGaps (otherState initial)) := by
        simpa [PoissonProcess.arrivalPrefix] using ih
      rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega,
        PoissonProcess.arrivalPrefix, Finset.sum_range_succ,
        show 2 * k + 1 = (2 * k) + 1 by omega,
        Finset.sum_range_succ, ih', PoissonProcess.arrivalPrefix,
        Finset.sum_range_succ]
      rw [PoissonProcess.arrivalPrefix, Finset.sum_range_succ]
      simp only [PoissonProcess.interarrival]
      change
        ((∑ i ∈ Finset.range k, PoissonProcess.interarrival i (switchGaps initial)) +
            ∑ i ∈ Finset.range k,
              PoissonProcess.interarrival i (switchGaps (otherState initial)) +
            alternatingGap initial switchGaps (2 * k)) +
          alternatingGap initial switchGaps (2 * k + 1) =
          ((∑ i ∈ Finset.range k, PoissonProcess.interarrival i (switchGaps initial)) +
            switchGaps initial k) +
            ((∑ i ∈ Finset.range k,
              PoissonProcess.interarrival i (switchGaps (otherState initial))) +
              switchGaps (otherState initial) k)
      rw [alternatingGap_two_mul, alternatingGap_two_mul_add_one]
      ring

/-- On the fiber where a calendar time lies in the `(k+1)`st visit to the
initial state, the literal residual alternating path is the memoryless
residual of that active visit followed by the two deterministically shifted
state-specific streams. -/
theorem residualTail_alternatingGaps_of_count_eq_two_mul
    (initial : Fin 2) (switchGaps : Fin 2 -> Nat -> Real)
    (t : Real) (k : Nat)
    (hcount : PoissonProcess.canonicalRenewalCount t
      (alternatingGaps initial switchGaps) = 2 * k) :
    PoissonProcess.residualTail t (alternatingGaps initial switchGaps) =
      PoissonProcess.firstGapResidualTail
        (t - (PoissonProcess.arrivalPrefix k (switchGaps initial) +
          PoissonProcess.arrivalPrefix k (switchGaps (otherState initial))))
        (alternatingGaps initial (switchGapsAfterPairs switchGaps k)) := by
  rw [PoissonProcess.residualTail_eq_firstGapResidualTail_on_countFiber
    t (alternatingGaps initial switchGaps) (2 * k) hcount,
    futureInterarrival_two_mul_alternatingGaps,
    arrivalPrefix_two_mul_alternatingGaps]

/-- The elapsed time before the `(2 * k + 1)`st alternating hold consists of
`k + 1` completed visits to the initial state and `k` to the other state. -/
theorem arrivalPrefix_two_mul_add_one_alternatingGaps
    (initial : Fin 2) (switchGaps : Fin 2 -> Nat -> Real) (k : Nat) :
    PoissonProcess.arrivalPrefix (2 * k + 1) (alternatingGaps initial switchGaps) =
      PoissonProcess.arrivalPrefix (k + 1) (switchGaps initial) +
        PoissonProcess.arrivalPrefix k (switchGaps (otherState initial)) := by
  rw [PoissonProcess.arrivalPrefix, Finset.sum_range_succ]
  have hprefix := arrivalPrefix_two_mul_alternatingGaps initial switchGaps k
  change
    PoissonProcess.arrivalPrefix (2 * k) (alternatingGaps initial switchGaps) +
      alternatingGap initial switchGaps (2 * k) =
      PoissonProcess.arrivalPrefix (k + 1) (switchGaps initial) +
        PoissonProcess.arrivalPrefix k (switchGaps (otherState initial))
  have hinit : PoissonProcess.arrivalPrefix (k + 1) (switchGaps initial) =
      PoissonProcess.arrivalPrefix k (switchGaps initial) + switchGaps initial k := by
    simp [PoissonProcess.arrivalPrefix, PoissonProcess.interarrival,
      Finset.sum_range_succ]
  rw [hprefix, hinit, alternatingGap_two_mul]
  ring

/-- Joint measurability of the state-indexed deinterleaving operation. -/
theorem measurable_switchGapsOfAlternating :
    Measurable (fun z : (Fin 2) × (Nat -> Real) =>
      switchGapsOfAlternating z.1 z.2) := by
  classical
  apply measurable_pi_lambda
  intro state
  apply measurable_pi_lambda
  intro n
  letI : DecidablePred (fun z : (Fin 2) × (Nat -> Real) => state = z.1) :=
    fun _ => inferInstance
  have hstate : MeasurableSet {z : (Fin 2) × (Nat -> Real) | state = z.1} := by
    rw [show {z : (Fin 2) × (Nat -> Real) | state = z.1} =
      Prod.fst ⁻¹' {state} by ext z; simp [eq_comm]]
    exact measurable_fst (measurableSet_singleton state)
  have heven : Measurable (fun z : (Fin 2) × (Nat -> Real) => z.2 (2 * n)) :=
    (measurable_pi_apply (2 * n)).comp measurable_snd
  have hodd : Measurable (fun z : (Fin 2) × (Nat -> Real) => z.2 (2 * n + 1)) :=
    (measurable_pi_apply (2 * n + 1)).comp measurable_snd
  simpa [switchGapsOfAlternating] using Measurable.ite hstate heven hodd

private theorem arrivalTime_succ
    (gaps : Nat -> Real) (n : Nat) :
    PoissonProcess.arrivalTime (n + 1) gaps =
      PoissonProcess.arrivalTime n gaps + gaps (n + 1) := by
  simp [PoissonProcess.arrivalTime, PoissonProcess.interarrival,
    Finset.sum_range_succ]

/-- At every completed pair of alternating holds, elapsed time is exactly the
sum of the corresponding finite prefixes of the two state-specific streams. -/
theorem arrivalTime_two_mul_add_one_alternatingGaps
    (initial : Fin 2) (switchGaps : Fin 2 -> Nat -> Real) (n : Nat) :
    PoissonProcess.arrivalTime (2 * n + 1) (alternatingGaps initial switchGaps) =
      PoissonProcess.arrivalTime n (switchGaps initial) +
        PoissonProcess.arrivalTime n (switchGaps (otherState initial)) := by
  induction n with
  | zero =>
      simp [PoissonProcess.arrivalTime, PoissonProcess.interarrival,
        alternatingGaps, alternatingGap, stateAfterSwitches, otherState,
        Finset.sum_range_succ]
  | succ n ih =>
      have hfirstIndex : 2 * n + 1 + 1 = 2 * (n + 1) := by omega
      have hsecondIndex : (2 * n + 1 + 1) + 1 = 2 * (n + 1) + 1 := by omega
      calc
        PoissonProcess.arrivalTime (2 * (n + 1) + 1)
            (alternatingGaps initial switchGaps) =
            PoissonProcess.arrivalTime (2 * n + 1 + 1)
              (alternatingGaps initial switchGaps) +
              (alternatingGaps initial switchGaps) (2 * n + 1 + 1 + 1) := by
              rw [show 2 * (n + 1) + 1 = (2 * n + 1 + 1) + 1 by omega,
                arrivalTime_succ]
        _ = (PoissonProcess.arrivalTime (2 * n + 1)
              (alternatingGaps initial switchGaps) +
              (alternatingGaps initial switchGaps) (2 * n + 1 + 1)) +
              (alternatingGaps initial switchGaps) (2 * n + 1 + 1 + 1) := by
              rw [arrivalTime_succ]
        _ = (PoissonProcess.arrivalTime n (switchGaps initial) +
              PoissonProcess.arrivalTime n (switchGaps (otherState initial)) +
              switchGaps initial (n + 1)) +
              switchGaps (otherState initial) (n + 1) := by
              rw [ih]
              change
                (PoissonProcess.arrivalTime n (switchGaps initial) +
                    PoissonProcess.arrivalTime n (switchGaps (otherState initial)) +
                    alternatingGap initial switchGaps (2 * n + 1 + 1)) +
                    alternatingGap initial switchGaps (2 * n + 1 + 1 + 1) = _
              rw [hfirstIndex,
                alternatingGap_two_mul, alternatingGap_two_mul_add_one]
        _ = PoissonProcess.arrivalTime (n + 1) (switchGaps initial) +
              PoissonProcess.arrivalTime (n + 1)
                (switchGaps (otherState initial)) := by
              rw [arrivalTime_succ, arrivalTime_succ]
              ring

/-- An alternating holding-time path is nonexplosive whenever its two source
streams have nonnegative gaps and the initial-state stream's finite arrival
times diverge.  The paired-arrival identity makes the lower bound explicit. -/
theorem tendsto_arrivalTime_alternatingGaps
    (initial : Fin 2) (switchGaps : Fin 2 -> Nat -> Real)
    (hnonneg : ∀ state n, 0 ≤ switchGaps state n)
    (hdiv : Tendsto (fun n : Nat =>
      PoissonProcess.arrivalTime n (switchGaps initial)) atTop atTop) :
    Tendsto (fun n : Nat =>
      PoissonProcess.arrivalTime n (alternatingGaps initial switchGaps)) atTop atTop := by
  have haltNonneg : ∀ n, 0 ≤ PoissonProcess.interarrival n
      (alternatingGaps initial switchGaps) := by
    intro n
    simpa [PoissonProcess.interarrival, alternatingGaps, alternatingGap] using
      hnonneg (stateAfterSwitches initial n) (n / 2)
  have hmono : Monotone (fun n : Nat =>
      PoissonProcess.arrivalTime n (alternatingGaps initial switchGaps)) :=
    PoissonProcess.arrivalTime_mono_of_nonnegative _ haltNonneg
  have hotherNonneg : ∀ n, 0 ≤
      PoissonProcess.arrivalTime n (switchGaps (otherState initial)) := by
    apply PoissonProcess.arrivalTime_nonnegative_of_interarrival_nonnegative
    intro n
    simpa [PoissonProcess.interarrival] using hnonneg (otherState initial) n
  have hpaired : Tendsto (fun n : Nat =>
      PoissonProcess.arrivalTime n (switchGaps initial) +
        PoissonProcess.arrivalTime n (switchGaps (otherState initial))) atTop atTop :=
    tendsto_atTop_mono (fun n => le_add_of_nonneg_right (hotherNonneg n)) hdiv
  apply tendsto_atTop_of_monotone_of_subseq (l := atTop)
    (φ := fun n : Nat => 2 * n + 1) hmono
  change Tendsto (fun n : Nat =>
    PoissonProcess.arrivalTime (2 * n + 1)
      (alternatingGaps initial switchGaps)) atTop atTop
  convert hpaired using 1
  funext n
  exact arrivalTime_two_mul_add_one_alternatingGaps initial switchGaps n

/-- Under the product of two positive-rate canonical exponential-interarrival
laws, the concrete alternating holding-time path is nonexplosive almost
surely. -/
theorem ae_tendsto_arrivalTime_alternatingGaps_prod
    (initial : Fin 2) (leftRate rightRate : Real)
    (hleft : 0 < leftRate) (hright : 0 < rightRate) :
    ∀ᵐ pair ∂
      (PoissonProcess.exponentialInterarrivalMeasure leftRate).prod
        (PoissonProcess.exponentialInterarrivalMeasure rightRate),
      Tendsto (fun n : Nat =>
        PoissonProcess.arrivalTime n
          (alternatingGaps initial (twoStateGapsOfPair pair))) atTop atTop := by
  let leftMeasure := PoissonProcess.exponentialInterarrivalMeasure leftRate
  let rightMeasure := PoissonProcess.exponentialInterarrivalMeasure rightRate
  letI : IsProbabilityMeasure leftMeasure :=
    PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure hleft
  letI : IsProbabilityMeasure rightMeasure :=
    PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure hright
  have hleftNonneg : ∀ᵐ pair ∂leftMeasure.prod rightMeasure,
      ∀ n, 0 ≤ pair.1 n := by
    refine ae_of_ae_map (μ := leftMeasure.prod rightMeasure) (f := Prod.fst)
      (p := fun gaps : Nat -> Real => ∀ n, 0 ≤ gaps n)
      measurable_fst.aemeasurable ?_
    rw [Measure.map_fst_prod, measure_univ, one_smul]
    simpa [PoissonProcess.interarrival] using
      PoissonProcess.ae_all_interarrival_nonnegative hleft
  have hrightNonneg : ∀ᵐ pair ∂leftMeasure.prod rightMeasure,
      ∀ n, 0 ≤ pair.2 n := by
    refine ae_of_ae_map (μ := leftMeasure.prod rightMeasure) (f := Prod.snd)
      (p := fun gaps : Nat -> Real => ∀ n, 0 ≤ gaps n)
      measurable_snd.aemeasurable ?_
    rw [Measure.map_snd_prod, measure_univ, one_smul]
    simpa [PoissonProcess.interarrival] using
      PoissonProcess.ae_all_interarrival_nonnegative hright
  have hleftDiv : ∀ᵐ pair ∂leftMeasure.prod rightMeasure,
      Tendsto (fun n : Nat => PoissonProcess.arrivalTime n pair.1) atTop atTop := by
    refine ae_of_ae_map (μ := leftMeasure.prod rightMeasure) (f := Prod.fst)
      (p := fun gaps : Nat -> Real =>
        Tendsto (fun n : Nat => PoissonProcess.arrivalTime n gaps) atTop atTop)
      measurable_fst.aemeasurable ?_
    rw [Measure.map_fst_prod, measure_univ, one_smul]
    exact PoissonProcess.ae_arrivalTime_tendsto_atTop hleft
  have hrightDiv : ∀ᵐ pair ∂leftMeasure.prod rightMeasure,
      Tendsto (fun n : Nat => PoissonProcess.arrivalTime n pair.2) atTop atTop := by
    refine ae_of_ae_map (μ := leftMeasure.prod rightMeasure) (f := Prod.snd)
      (p := fun gaps : Nat -> Real =>
        Tendsto (fun n : Nat => PoissonProcess.arrivalTime n gaps) atTop atTop)
      measurable_snd.aemeasurable ?_
    rw [Measure.map_snd_prod, measure_univ, one_smul]
    exact PoissonProcess.ae_arrivalTime_tendsto_atTop hright
  change ∀ᵐ pair ∂leftMeasure.prod rightMeasure,
    Tendsto (fun n : Nat =>
      PoissonProcess.arrivalTime n
        (alternatingGaps initial (twoStateGapsOfPair pair))) atTop atTop
  fin_cases initial
  · filter_upwards [hleftNonneg, hrightNonneg, hleftDiv] with pair hleft0 hright0 hdiv
    apply tendsto_arrivalTime_alternatingGaps 0 (twoStateGapsOfPair pair) _ hdiv
    intro state n
    fin_cases state
    · simpa [twoStateGapsOfPair] using hleft0 n
    · simpa [twoStateGapsOfPair] using hright0 n
  · filter_upwards [hleftNonneg, hrightNonneg, hrightDiv] with pair hleft0 hright0 hdiv
    apply tendsto_arrivalTime_alternatingGaps 1 (twoStateGapsOfPair pair) _ hdiv
    intro state n
    fin_cases state
    · simpa [twoStateGapsOfPair] using hleft0 n
    · simpa [twoStateGapsOfPair] using hright0 n

theorem measurable_alternatingGaps (initial : Fin 2) :
    Measurable (alternatingGaps initial) := by
  apply measurable_pi_lambda
  intro n
  exact (measurable_pi_apply (n / 2)).comp
    (measurable_pi_apply (stateAfterSwitches initial n))

/-- Remove the consumed first holding time from the stream of the initial
state, leaving the other state's stream untouched. -/
def switchGapsAfterFirst (initial : Fin 2) (switchGaps : Fin 2 -> Nat -> Real) :
    Fin 2 -> Nat -> Real :=
  fun state n => if state = initial then switchGaps state (n + 1) else switchGaps state n

theorem stateAfterSwitches_succ (initial : Fin 2) (n : Nat) :
    stateAfterSwitches initial (n + 1) =
      stateAfterSwitches (otherState initial) n := by
  rcases n.even_or_odd' with ⟨k, rfl | rfl⟩
  · have hEven : Even (2 * k) := ⟨k, by omega⟩
    have hOdd : Odd (2 * k + 1) := hEven.add_one
    rw [stateAfterSwitches_odd initial hOdd,
      stateAfterSwitches_even (otherState initial) hEven]
  · have hOdd : Odd (2 * k + 1) := ⟨k, by omega⟩
    have hEven : Even (2 * k + 1 + 1) := hOdd.add_one
    rw [stateAfterSwitches_even initial hEven,
      stateAfterSwitches_odd (otherState initial) hOdd,
      otherState_otherState]

private theorem alternatingGap_succ_eq_tail
    (initial : Fin 2) (switchGaps : Fin 2 -> Nat -> Real) (n : Nat) :
    alternatingGap initial switchGaps (n + 1) =
      alternatingGap (otherState initial) (switchGapsAfterFirst initial switchGaps) n := by
  fin_cases initial
  · rcases n.even_or_odd' with ⟨k, rfl | rfl⟩
    · have hEven : Even (2 * k) := ⟨k, by omega⟩
      have hOdd : Odd (2 * k + 1) := hEven.add_one
      have hnotEven : ¬ Even (2 * k + 1) := Nat.not_even_iff_odd.mpr hOdd
      have hdiv : (2 * k + 1) / 2 = k := by omega
      simp [alternatingGap, switchGapsAfterFirst, stateAfterSwitches,
        otherState, hEven, hnotEven, hdiv]
    · have hOdd : Odd (2 * k + 1) := ⟨k, by omega⟩
      have hnotEven : ¬ Even (2 * k + 1) := Nat.not_even_iff_odd.mpr hOdd
      have hEven : Even (2 * k + 1 + 1) := hOdd.add_one
      have hdiv : (2 * k + 1) / 2 = k := by omega
      have hdivSucc : (2 * k + 1 + 1) / 2 = k + 1 := by omega
      simp [alternatingGap, switchGapsAfterFirst, stateAfterSwitches,
        otherState, hnotEven, hEven, hdiv, hdivSucc]
  · rcases n.even_or_odd' with ⟨k, rfl | rfl⟩
    · have hEven : Even (2 * k) := ⟨k, by omega⟩
      have hOdd : Odd (2 * k + 1) := hEven.add_one
      have hnotEven : ¬ Even (2 * k + 1) := Nat.not_even_iff_odd.mpr hOdd
      have hdiv : (2 * k + 1) / 2 = k := by omega
      simp [alternatingGap, switchGapsAfterFirst, stateAfterSwitches,
        otherState, hEven, hnotEven, hdiv]
    · have hOdd : Odd (2 * k + 1) := ⟨k, by omega⟩
      have hnotEven : ¬ Even (2 * k + 1) := Nat.not_even_iff_odd.mpr hOdd
      have hEven : Even (2 * k + 1 + 1) := hOdd.add_one
      have hdiv : (2 * k + 1) / 2 = k := by omega
      have hdivSucc : (2 * k + 1 + 1) / 2 = k + 1 := by omega
      simp [alternatingGap, switchGapsAfterFirst, stateAfterSwitches,
        otherState, hnotEven, hEven, hdiv, hdivSucc]

/-- The alternating holding-time path is its literal first holding time
prepended to the switched-state path with precisely that one consumed stream
coordinate removed. -/
theorem alternatingGaps_eq_prepend_tail
    (initial : Fin 2) (switchGaps : Fin 2 -> Nat -> Real) :
    alternatingGaps initial switchGaps =
      PoissonProcess.prependInterarrival (switchGaps initial 0)
        (alternatingGaps (otherState initial)
          (switchGapsAfterFirst initial switchGaps)) := by
  funext n
  cases n with
  | zero =>
      simp [alternatingGaps, alternatingGap, PoissonProcess.prependInterarrival,
        stateAfterSwitches]
  | succ n =>
      simpa [alternatingGaps, PoissonProcess.prependInterarrival] using
        alternatingGap_succ_eq_tail initial switchGaps n

/-- Removing the first alternating coordinate gives the opposite-state path
on the literal state-indexed tails. -/
theorem futureInterarrival_one_alternatingGaps
    (initial : Fin 2) (switchGaps : Fin 2 -> Nat -> Real) :
    PoissonProcess.futureInterarrival 1 (alternatingGaps initial switchGaps) =
      alternatingGaps (otherState initial) (switchGapsAfterFirst initial switchGaps) := by
  funext n
  change alternatingGap initial switchGaps (1 + n) =
    alternatingGap (otherState initial) (switchGapsAfterFirst initial switchGaps) n
  simpa [Nat.add_comm] using alternatingGap_succ_eq_tail initial switchGaps n

/-- After exactly `2 * k + 1` alternating holds, the next hold belongs to the
other state and the remaining state-indexed streams are the literal first-tail
of the pair shifted after `k` visits each. -/
theorem futureInterarrival_two_mul_add_one_alternatingGaps
    (initial : Fin 2) (switchGaps : Fin 2 -> Nat -> Real) (k : Nat) :
    PoissonProcess.futureInterarrival (2 * k + 1)
      (alternatingGaps initial switchGaps) =
      alternatingGaps (otherState initial)
        (switchGapsAfterFirst initial (switchGapsAfterPairs switchGaps k)) := by
  calc
    PoissonProcess.futureInterarrival (2 * k + 1)
        (alternatingGaps initial switchGaps) =
      PoissonProcess.futureInterarrival 1
        (PoissonProcess.futureInterarrival (2 * k)
          (alternatingGaps initial switchGaps)) := by
            funext n
            simp [PoissonProcess.futureInterarrival, PoissonProcess.interarrival,
              Nat.add_assoc]
    _ = PoissonProcess.futureInterarrival 1
        (alternatingGaps initial (switchGapsAfterPairs switchGaps k)) := by
          rw [futureInterarrival_two_mul_alternatingGaps]
    _ = alternatingGaps (otherState initial)
        (switchGapsAfterFirst initial (switchGapsAfterPairs switchGaps k)) := by
          exact futureInterarrival_one_alternatingGaps initial
            (switchGapsAfterPairs switchGaps k)

/-- On the fiber where a calendar time lies in the `(k+1)`st visit to the
other state, the literal residual alternating path is the residual active
other-state visit followed by the deterministically shifted source streams. -/
theorem residualTail_alternatingGaps_of_count_eq_two_mul_add_one
    (initial : Fin 2) (switchGaps : Fin 2 -> Nat -> Real)
    (t : Real) (k : Nat)
    (hcount : PoissonProcess.canonicalRenewalCount t
      (alternatingGaps initial switchGaps) = 2 * k + 1) :
    PoissonProcess.residualTail t (alternatingGaps initial switchGaps) =
      PoissonProcess.firstGapResidualTail
        (t - (PoissonProcess.arrivalPrefix (k + 1) (switchGaps initial) +
          PoissonProcess.arrivalPrefix k (switchGaps (otherState initial))))
        (alternatingGaps (otherState initial)
          (switchGapsAfterFirst initial (switchGapsAfterPairs switchGaps k))) := by
  rw [PoissonProcess.residualTail_eq_firstGapResidualTail_on_countFiber
    t (alternatingGaps initial switchGaps) (2 * k + 1) hcount,
    futureInterarrival_two_mul_add_one_alternatingGaps,
    arrivalPrefix_two_mul_add_one_alternatingGaps]

/-- The state of the alternating path at calendar time `t`, using the
canonical renewal count of its concrete alternating holding-time sequence. -/
noncomputable def stateAt (initial : Fin 2)
    (switchGaps : Fin 2 -> Nat -> Real) (t : Real) : Fin 2 :=
  stateAfterSwitches initial
    (PoissonProcess.canonicalRenewalCount t (alternatingGaps initial switchGaps))

/-- State-indexed future holding streams seen from a literal calendar time.
The first coordinate of the residual alternating path is the remaining part
of the *active* hold; deinterleaving then assigns all later holds to their
actual source states.  This definition is pathwise and makes no Markov or
fresh-tail assumption. -/
noncomputable def switchGapsAfterElapsed (initial : Fin 2)
    (switchGaps : Fin 2 -> Nat -> Real) (t : Real) : Fin 2 -> Nat -> Real :=
  switchGapsOfAlternating (stateAt initial switchGaps t)
    (PoissonProcess.residualTail t (alternatingGaps initial switchGaps))

/-- Starting a relabeled pair in state zero produces exactly the same
alternating holding-time sequence as starting the original pair in state one. -/
theorem alternatingGaps_zero_swapPair_eq_alternatingGaps_one
    (pair : (Nat -> Real) × (Nat -> Real)) :
    alternatingGaps 0 (twoStateGapsOfPair (Prod.swap pair)) =
      alternatingGaps 1 (twoStateGapsOfPair pair) := by
  funext n
  rcases n.even_or_odd' with ⟨k, rfl | rfl⟩
  · simp only [alternatingGaps]
    rw [alternatingGap_two_mul, alternatingGap_two_mul]
    rfl
  · simp only [alternatingGaps]
    rw [alternatingGap_two_mul_add_one, alternatingGap_two_mul_add_one]
    rfl

/-- The state-zero endpoint of the swapped pair is the relabeling of the
state-one endpoint of the original pair. -/
theorem stateAt_zero_swapPair_eq_otherState_stateAt_one
    (pair : (Nat -> Real) × (Nat -> Real)) (t : Real) :
    stateAt 0 (twoStateGapsOfPair (Prod.swap pair)) t =
      otherState (stateAt 1 (twoStateGapsOfPair pair) t) := by
  unfold stateAt
  rw [alternatingGaps_zero_swapPair_eq_alternatingGaps_one]
  rcases (PoissonProcess.canonicalRenewalCount t
      (alternatingGaps 1 (twoStateGapsOfPair pair))).even_or_odd' with
    ⟨k, hk | hk⟩
  · rw [hk, stateAfterSwitches_even 0 ⟨k, by omega⟩,
      stateAfterSwitches_even 1 ⟨k, by omega⟩]
    simp
  · rw [hk, stateAfterSwitches_odd 0 ⟨k, by omega⟩,
      stateAfterSwitches_odd 1 ⟨k, by omega⟩]
    simp

/-- Relabeling the state-indexed deinterleaving swaps its initial state. -/
theorem swapStateIndexedGaps_switchGapsOfAlternating
    (initial : Fin 2) (gaps : Nat -> Real) :
    swapStateIndexedGaps (switchGapsOfAlternating initial gaps) =
      switchGapsOfAlternating (otherState initial) gaps := by
  funext state n
  fin_cases initial <;> fin_cases state <;>
    simp [swapStateIndexedGaps, switchGapsOfAlternating]

/-- The literal future streams from a state-one start are the state relabeling
of the literal future streams from the swapped state-zero representation. -/
theorem switchGapsAfterElapsed_one_eq_swapStateIndexedGaps_zero_swapPair
    (pair : (Nat -> Real) × (Nat -> Real)) (t : Real) :
    switchGapsAfterElapsed 1 (twoStateGapsOfPair pair) t =
      swapStateIndexedGaps
        (switchGapsAfterElapsed 0 (twoStateGapsOfPair (Prod.swap pair)) t) := by
  have hgaps := alternatingGaps_zero_swapPair_eq_alternatingGaps_one pair
  have hstate := stateAt_zero_swapPair_eq_otherState_stateAt_one pair t
  unfold switchGapsAfterElapsed
  rw [hstate, hgaps]
  symm
  rw [swapStateIndexedGaps_switchGapsOfAlternating]
  exact congrArg (fun initial => switchGapsOfAlternating initial
    (PoissonProcess.residualTail t
      (alternatingGaps 1 (twoStateGapsOfPair pair))))
    (otherState_otherState (stateAt 1 (twoStateGapsOfPair pair) t))

/-- Reassembling the future state-indexed streams from a calendar time gives
exactly the literal residual alternating sequence. -/
theorem alternatingGaps_switchGapsAfterElapsed
    (initial : Fin 2) (switchGaps : Fin 2 -> Nat -> Real) (t : Real) :
    alternatingGaps (stateAt initial switchGaps t)
      (switchGapsAfterElapsed initial switchGaps t) =
        PoissonProcess.residualTail t (alternatingGaps initial switchGaps) := by
  exact alternatingGaps_switchGapsOfAlternating
    (stateAt initial switchGaps t)
    (PoissonProcess.residualTail t (alternatingGaps initial switchGaps))

/-- On an even alternating-count fiber, the calendar-time state-indexed
future streams are exactly the residual active initial-state visit together
with the deterministically shifted source streams. -/
theorem switchGapsAfterElapsed_of_count_eq_two_mul
    (initial : Fin 2) (switchGaps : Fin 2 -> Nat -> Real)
    (t : Real) (k : Nat)
    (hcount : PoissonProcess.canonicalRenewalCount t
      (alternatingGaps initial switchGaps) = 2 * k) :
    switchGapsAfterElapsed initial switchGaps t =
      switchGapsAfterActiveElapsed initial (switchGapsAfterPairs switchGaps k)
        (t - (PoissonProcess.arrivalPrefix k (switchGaps initial) +
          PoissonProcess.arrivalPrefix k (switchGaps (otherState initial))) ) := by
  have hstate : stateAt initial switchGaps t = initial := by
    unfold stateAt
    rw [hcount]
    exact stateAfterSwitches_even initial ⟨k, by omega⟩
  unfold switchGapsAfterElapsed
  rw [hstate, residualTail_alternatingGaps_of_count_eq_two_mul initial switchGaps t k hcount,
    switchGapsOfAlternating_firstGapResidualTail]

/-- On an odd alternating-count fiber, the calendar-time state-indexed
future streams are the residual active other-state visit together with the
literal shifted source streams. -/
theorem switchGapsAfterElapsed_of_count_eq_two_mul_add_one
    (initial : Fin 2) (switchGaps : Fin 2 -> Nat -> Real)
    (t : Real) (k : Nat)
    (hcount : PoissonProcess.canonicalRenewalCount t
      (alternatingGaps initial switchGaps) = 2 * k + 1) :
    switchGapsAfterElapsed initial switchGaps t =
      switchGapsAfterActiveElapsed (otherState initial)
        (switchGapsAfterFirst initial (switchGapsAfterPairs switchGaps k))
        (t - (PoissonProcess.arrivalPrefix (k + 1) (switchGaps initial) +
          PoissonProcess.arrivalPrefix k (switchGaps (otherState initial))) ) := by
  have hstate : stateAt initial switchGaps t = otherState initial := by
    unfold stateAt
    rw [hcount]
    exact stateAfterSwitches_odd initial ⟨k, by omega⟩
  unfold switchGapsAfterElapsed
  rw [hstate,
    residualTail_alternatingGaps_of_count_eq_two_mul_add_one initial switchGaps t k hcount,
    switchGapsOfAlternating_firstGapResidualTail]

/-- After a calendar-time shift, the literal alternating state path is driven
by the residual alternating sequence, reassembled under the actual current
state.  The arrival-existence hypotheses isolate nonexplosion; no stochastic
restart assertion is used here. -/
theorem stateAt_add_eq_stateAt_afterElapsed
    (initial : Fin 2) (switchGaps : Fin 2 -> Nat -> Real) (s h : Real)
    (hh : 0 ≤ h)
    (hS : ∃ n : Nat, s < PoissonProcess.arrivalTime n
      (alternatingGaps initial switchGaps))
    (hSH : ∃ n : Nat, s + h < PoissonProcess.arrivalTime n
      (alternatingGaps initial switchGaps))
    (hTail : ∃ m : Nat, h < PoissonProcess.arrivalTime m
      (PoissonProcess.residualTail s (alternatingGaps initial switchGaps))) :
    stateAt initial switchGaps (s + h) =
      stateAt (stateAt initial switchGaps s)
        (switchGapsAfterElapsed initial switchGaps s) h := by
  unfold stateAt switchGapsAfterElapsed
  simp only [stateAt]
  rw [alternatingGaps_switchGapsOfAlternating]
  rw [PoissonProcess.canonicalRenewalCount_add_eq_residualTailCount s h hh _ hS hSH hTail]
  exact stateAfterSwitches_add initial _ _

/-- Calendar-time shifting of state-indexed switch streams is associative:
shifting by `s` and then by a nonnegative `h` gives the same literal future
streams as shifting once by `s + h`.  The arrival hypotheses are precisely
the pathwise nonexplosion conditions required for the renewal-count algebra. -/
theorem switchGapsAfterElapsed_add_eq_switchGapsAfterElapsed_comp
    (initial : Fin 2) (switchGaps : Fin 2 -> Nat -> Real) (s h : Real)
    (hh : 0 ≤ h)
    (hS : ∃ n : Nat, s < PoissonProcess.arrivalTime n
      (alternatingGaps initial switchGaps))
    (hSH : ∃ n : Nat, s + h < PoissonProcess.arrivalTime n
      (alternatingGaps initial switchGaps))
    (hTail : ∃ m : Nat, h < PoissonProcess.arrivalTime m
      (PoissonProcess.residualTail s (alternatingGaps initial switchGaps))) :
    switchGapsAfterElapsed initial switchGaps (s + h) =
      switchGapsAfterElapsed (stateAt initial switchGaps s)
        (switchGapsAfterElapsed initial switchGaps s) h := by
  have hstate := stateAt_add_eq_stateAt_afterElapsed
    initial switchGaps s h hh hS hSH hTail
  change switchGapsOfAlternating (stateAt initial switchGaps (s + h))
      (PoissonProcess.residualTail (s + h) (alternatingGaps initial switchGaps)) =
    switchGapsOfAlternating
      (stateAt (stateAt initial switchGaps s)
        (switchGapsAfterElapsed initial switchGaps s) h)
      (PoissonProcess.residualTail h
        (alternatingGaps (stateAt initial switchGaps s)
          (switchGapsAfterElapsed initial switchGaps s)))
  rw [hstate, alternatingGaps_switchGapsAfterElapsed,
    PoissonProcess.residualTail_add_eq_residualTail_comp s h hh
      (alternatingGaps initial switchGaps) hS hSH hTail]

/-- Before the literal first holding time has elapsed, the alternating path
remains in its initial state. -/
theorem stateAt_eq_initial_of_lt_firstGap
    (initial : Fin 2) (switchGaps : Fin 2 -> Nat -> Real) (t : Real)
    (ht : t < switchGaps initial 0) :
    stateAt initial switchGaps t = initial := by
  have hcount : PoissonProcess.canonicalRenewalCount t
      (alternatingGaps initial switchGaps) = 0 := by
    apply (PoissonProcess.canonicalRenewalCount_eq_zero_iff t
      (alternatingGaps initial switchGaps)).mpr
    left
    simpa [PoissonProcess.arrivalTime, PoissonProcess.interarrival,
      alternatingGaps, alternatingGap, stateAfterSwitches] using ht
  simp [stateAt, hcount, stateAfterSwitches]

/-- After the concrete first holding time has elapsed, the alternating path
is exactly the switched-state path driven by the unconsumed literal stream
tails.  The sole premise is nonexplosion of that remaining alternating path. -/
theorem stateAt_head_add_eq_switched_tail
    (initial : Fin 2) (switchGaps : Fin 2 -> Nat -> Real)
    (htail : Tendsto (fun n : Nat =>
      PoissonProcess.arrivalTime n
        (alternatingGaps (otherState initial)
          (switchGapsAfterFirst initial switchGaps))) atTop atTop)
    (t : Real) (ht : 0 ≤ t) :
    stateAt initial switchGaps (switchGaps initial 0 + t) =
      stateAt (otherState initial) (switchGapsAfterFirst initial switchGaps) t := by
  unfold stateAt
  rw [alternatingGaps_eq_prepend_tail]
  rw [PoissonProcess.canonicalRenewalCount_head_add_prependInterarrival
    (switchGaps initial 0)
    (alternatingGaps (otherState initial) (switchGapsAfterFirst initial switchGaps))
    htail t ht]
  exact stateAfterSwitches_succ initial _

private theorem measurable_stateAfterSwitches (initial : Fin 2) :
    Measurable (stateAfterSwitches initial) := by
  exact measurable_of_countable _

/-- Joint measurability of the concrete state endpoint in the switching paths
and calendar time. -/
theorem measurable_stateAt (initial : Fin 2) :
    Measurable (fun z : (Fin 2 -> Nat -> Real) × Real => stateAt initial z.1 z.2) := by
  let gaps : (Fin 2 -> Nat -> Real) -> Nat -> Real := alternatingGaps initial
  have hgaps : Measurable gaps := by
    simpa [gaps] using measurable_alternatingGaps initial
  have hcount : Measurable (fun z : (Fin 2 -> Nat -> Real) × Real =>
      PoissonProcess.canonicalRenewalCount z.2 (gaps z.1)) := by
    have hjoint : Measurable (fun z : (Fin 2 -> Nat -> Real) × Real =>
        (z.2, gaps z.1)) :=
      measurable_snd.prodMk (hgaps.comp measurable_fst)
    exact PoissonProcess.measurable_canonicalRenewalCount_joint.comp hjoint
  exact (measurable_stateAfterSwitches initial).comp hcount

/-- The state-indexed residual-hold reassembly is jointly measurable in the
literal switch streams and calendar time. -/
theorem measurable_switchGapsAfterElapsed (initial : Fin 2) :
    Measurable (fun z : (Fin 2 -> Nat -> Real) × Real =>
      switchGapsAfterElapsed initial z.1 z.2) := by
  let tail : (Fin 2 -> Nat -> Real) × Real -> Nat -> Real :=
    fun z => PoissonProcess.residualTail z.2 (alternatingGaps initial z.1)
  have htail : Measurable tail := by
    exact PoissonProcess.measurable_residualTail_joint.comp
      (measurable_snd.prodMk ((measurable_alternatingGaps initial).comp measurable_fst))
  simpa [switchGapsAfterElapsed, tail] using
    measurable_switchGapsOfAlternating.comp ((measurable_stateAt initial).prodMk htail)

/-- For every fixed time, the concrete alternating endpoint is measurable in
the pair of source holding-time streams. -/
theorem measurable_stateAt_fixedTime (initial : Fin 2) (t : Real) :
    Measurable (fun switchGaps : Fin 2 -> Nat -> Real => stateAt initial switchGaps t) := by
  exact (measurable_stateAt initial).comp (measurable_id.prodMk measurable_const)

/-- Probability of a specified two-state endpoint under an arbitrary path
measure.  This is a measure-valued function of calendar time; finiteness and
regularity of a particular path law are separate questions. -/
noncomputable def stateProbability
    (μ : Measure (Fin 2 -> Nat -> Real)) (initial target : Fin 2) (t : Real) : ℝ≥0∞ :=
  μ {switchGaps | stateAt initial switchGaps t = target}

/-- Endpoint probabilities are measurable in calendar time whenever the path
law is s-finite.  The proof integrates the jointly measurable finite-state
indicator over the path carrier. -/
theorem measurable_stateProbability
    (μ : Measure (Fin 2 -> Nat -> Real)) [SFinite μ]
    (initial target : Fin 2) :
    Measurable (stateProbability μ initial target) := by
  let f : Real × (Fin 2 -> Nat -> Real) -> ℝ≥0∞ := fun z =>
    if stateAt initial z.2 z.1 = target then 1 else 0
  have hf : Measurable f := by
    apply Measurable.ite
    · exact ((measurable_stateAt initial).comp
        (measurable_snd.prodMk measurable_fst)) (measurableSet_singleton _)
    · exact measurable_const
    · exact measurable_const
  have hint : Measurable fun t : Real => ∫⁻ switchGaps, f (t, switchGaps) ∂μ :=
    hf.lintegral_prod_right'
  convert hint using 1
  funext t
  change μ {switchGaps | stateAt initial switchGaps t = target} =
    ∫⁻ switchGaps, if stateAt initial switchGaps t = target then 1 else 0 ∂μ
  symm
  let E : Set (Fin 2 -> Nat -> Real) :=
    {switchGaps | stateAt initial switchGaps t = target}
  have hE : MeasurableSet E :=
    (measurable_stateAt_fixedTime initial t) (measurableSet_singleton _)
  calc
    ∫⁻ switchGaps, if stateAt initial switchGaps t = target then 1 else 0 ∂μ =
        ∫⁻ switchGaps, E.indicator (fun _ => 1) switchGaps ∂μ := by
          apply lintegral_congr
          intro switchGaps
          by_cases h : stateAt initial switchGaps t = target <;> simp [E, h]
    _ = ∫⁻ _ in E, 1 ∂μ := by
          rw [MeasureTheory.lintegral_indicator hE]
    _ = μ E := by simp
    _ = μ {switchGaps | stateAt initial switchGaps t = target} := rfl

/-- Under a probability path law, every alternating-path endpoint mass is at
most one. -/
theorem stateProbability_le_one
    (μ : Measure (Fin 2 -> Nat -> Real)) [IsProbabilityMeasure μ]
    (initial target : Fin 2) (t : Real) :
    stateProbability μ initial target t ≤ 1 := by
  exact (measure_mono (Set.subset_univ _)).trans_eq (measure_univ)

/-- Endpoint probabilities under a probability path law are finite. -/
theorem stateProbability_ne_top
    (μ : Measure (Fin 2 -> Nat -> Real)) [IsProbabilityMeasure μ]
    (initial target : Fin 2) (t : Real) :
    stateProbability μ initial target t ≠ ∞ := by
  exact ne_top_of_le_ne_top ENNReal.one_ne_top
    (stateProbability_le_one μ initial target t)

/-- The real-valued endpoint mass is measurable in time under an s-finite
path law.  Under a probability law, the accompanying bounds below make this
the bounded real quantity used in analytic renewal equations. -/
theorem measurable_stateProbability_toReal
    (μ : Measure (Fin 2 -> Nat -> Real)) [SFinite μ]
    (initial target : Fin 2) :
    Measurable (fun t => (stateProbability μ initial target t).toReal) := by
  exact (measurable_stateProbability μ initial target).ennreal_toReal

theorem stateProbability_toReal_nonneg
    (μ : Measure (Fin 2 -> Nat -> Real))
    (initial target : Fin 2) (t : Real) :
    0 ≤ (stateProbability μ initial target t).toReal :=
  ENNReal.toReal_nonneg

theorem stateProbability_toReal_le_one
    (μ : Measure (Fin 2 -> Nat -> Real)) [IsProbabilityMeasure μ]
    (initial target : Fin 2) (t : Real) :
    (stateProbability μ initial target t).toReal ≤ 1 := by
  rw [← ENNReal.toReal_one]
  exact ENNReal.toReal_mono ENNReal.one_ne_top
    (stateProbability_le_one μ initial target t)

/-- A two-state endpoint is always either the initial state or its unique
other state. -/
theorem stateAt_eq_initial_or_eq_otherState
    (initial : Fin 2) (switchGaps : Fin 2 -> Nat -> Real) (t : Real) :
    stateAt initial switchGaps t = initial ∨
      stateAt initial switchGaps t = otherState initial := by
  fin_cases initial
  · rcases Fin.eq_zero_or_eq_succ (stateAt 0 switchGaps t) with hzero | ⟨i, hi⟩
    · exact Or.inl hzero
    · fin_cases i
      exact Or.inr (by simpa [otherState] using hi)
  · rcases Fin.eq_zero_or_eq_succ (stateAt 1 switchGaps t) with hzero | ⟨i, hi⟩
    · exact Or.inr (by simpa [otherState] using hzero)
    · fin_cases i
      exact Or.inl (by simpa using hi)

/-- The two endpoint events partition a probability law on alternating
two-state paths.  This is kept at the measure level so source-specific
first-step equations can use it before choosing a real-valued analytic
representation. -/
theorem measure_stateAt_eq_initial_add_eq_otherState
    {μ : Measure (Fin 2 -> Nat -> Real)} [IsProbabilityMeasure μ]
    (initial : Fin 2) (t : Real) :
    μ {switchGaps | stateAt initial switchGaps t = initial} +
      μ {switchGaps | stateAt initial switchGaps t = otherState initial} = 1 := by
  let Einitial : Set (Fin 2 -> Nat -> Real) :=
    {switchGaps | stateAt initial switchGaps t = initial}
  let Eother : Set (Fin 2 -> Nat -> Real) :=
    {switchGaps | stateAt initial switchGaps t = otherState initial}
  have hinitial : MeasurableSet Einitial := by
    exact (measurable_stateAt_fixedTime initial t) (measurableSet_singleton _)
  have hother : MeasurableSet Eother := by
    exact (measurable_stateAt_fixedTime initial t) (measurableSet_singleton _)
  have hdisjoint : Disjoint Einitial Eother := by
    refine Set.disjoint_left.2 ?_
    intro switchGaps hinitial hother
    exact otherState_ne initial (hother.symm.trans hinitial)
  have hunion : Einitial ∪ Eother = Set.univ := by
    ext switchGaps
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    exact stateAt_eq_initial_or_eq_otherState initial switchGaps t
  calc
    μ {switchGaps | stateAt initial switchGaps t = initial} +
        μ {switchGaps | stateAt initial switchGaps t = otherState initial} =
        μ (Einitial ∪ Eother) := by
          symm
          exact measure_union hdisjoint hother
    _ = μ Set.univ := by rw [hunion]
    _ = 1 := measure_univ

/-- Real-valued form of the two-state endpoint partition.  Finiteness comes
from the probability-law bound rather than from an implicit coercion. -/
theorem stateProbability_toReal_initial_add_eq_otherState
    {μ : Measure (Fin 2 -> Nat -> Real)} [IsProbabilityMeasure μ]
    (initial : Fin 2) (t : Real) :
    (stateProbability μ initial initial t).toReal +
      (stateProbability μ initial (otherState initial) t).toReal = 1 := by
  have hpartition := congrArg ENNReal.toReal
    (measure_stateAt_eq_initial_add_eq_otherState (μ := μ) initial t)
  have hsum :
      (stateProbability μ initial initial t +
        stateProbability μ initial (otherState initial) t).toReal = 1 := by
    simpa only [stateProbability, ENNReal.toReal_one] using hpartition
  calc
    (stateProbability μ initial initial t).toReal +
        (stateProbability μ initial (otherState initial) t).toReal =
        (stateProbability μ initial initial t +
          stateProbability μ initial (otherState initial) t).toReal := by
          symm
          exact ENNReal.toReal_add (stateProbability_ne_top μ initial initial t)
            (stateProbability_ne_top μ initial (otherState initial) t)
    _ = 1 := hsum

/-- The endpoint of a two-state switching path whose two state-indexed gap
streams are supplied as an ordered pair together with a calendar time.  This
is the product-space form used when an external random completion time is
independent of the literal switch-clock pair. -/
noncomputable def stateAtPairAtTime (initial : Fin 2) :
    ((Nat -> Real) × (Nat -> Real)) × Real -> Fin 2 :=
  fun pairAndTime =>
    stateAt initial (twoStateGapsOfPair pairAndTime.1) pairAndTime.2

/-- Measurability of the ordered-pair/time endpoint functional. -/
theorem measurable_stateAtPairAtTime (initial : Fin 2) :
    Measurable (stateAtPairAtTime initial) := by
  exact (measurable_stateAt initial).comp
    ((measurable_twoStateGapsOfPair.comp measurable_fst).prodMk measurable_snd)

/-- The deterministic first-step endpoint functional: a literal active head
either has not elapsed, or leaves an opposite-state tail path at the remaining
time.  A separate pathwise theorem supplies this functional for an actual
alternating sample path. -/
noncomputable def firstStepStateAt (initial : Fin 2) (t : Real)
    (tailAndHead : ((Nat -> Real) × (Nat -> Real)) × Real) : Fin 2 :=
  if tailAndHead.2 ≤ t then
    stateAt (otherState initial) (twoStateGapsOfPair tailAndHead.1)
      (t - tailAndHead.2)
  else initial

theorem measurable_firstStepStateAt (initial : Fin 2) (t : Real) :
    Measurable (firstStepStateAt initial t) := by
  let htailPath : ((Nat -> Real) × (Nat -> Real)) × Real -> Fin 2 :=
    fun tailAndHead =>
      stateAt (otherState initial) (twoStateGapsOfPair tailAndHead.1)
        (t - tailAndHead.2)
  have htailPath_meas : Measurable htailPath := by
    exact (measurable_stateAt (otherState initial)).comp
      ((measurable_twoStateGapsOfPair.comp measurable_fst).prodMk
        (measurable_const.sub measurable_snd))
  exact Measurable.ite (measurableSet_le measurable_snd measurable_const)
    htailPath_meas measurable_const

/-- First-step integral equation for the probability of the opposite state.
The first holding time must have elapsed; conditional on its value, the event
is exactly that the opposite-state tail path is still in the opposite state at
the remaining elapsed time.  The statement is measure-level so it can be
instantiated with any factorized holding-time law before an analytic density
calculation is chosen. -/
theorem measure_firstStepStateAt_eq_other
    {μ : Measure ((Nat -> Real) × (Nat -> Real))} {ν : Measure Real}
    [SFinite μ] [SFinite ν] (initial : Fin 2) (t : Real) :
    (μ.prod ν) ((firstStepStateAt initial t) ⁻¹' {otherState initial}) =
      ∫⁻ tail, ν {head | head ≤ t ∧
        stateAt (otherState initial) (twoStateGapsOfPair tail) (t - head) =
          otherState initial} ∂μ := by
  have hevent : MeasurableSet
      ((firstStepStateAt initial t) ⁻¹' {otherState initial}) :=
    (measurable_firstStepStateAt initial t) (measurableSet_singleton _)
  rw [Measure.prod_apply hevent]
  apply lintegral_congr
  intro tail
  congr 1
  ext head
  simp only [Set.mem_preimage, Set.mem_setOf_eq]
  by_cases hhead : head ≤ t
  · simp [firstStepStateAt, hhead]
  · simp [firstStepStateAt, hhead, Ne.symm (otherState_ne initial)]

/-- The same opposite-state first-step equation with the holding-time measure
as the outer integral.  This is the Volterra orientation: after a candidate
first hold `head`, integrate the tail-path event at the residual time
`t - head`. -/
theorem measure_firstStepStateAt_eq_other_lintegral_head
    {μ : Measure ((Nat -> Real) × (Nat -> Real))} {ν : Measure Real}
    [SFinite μ] [SFinite ν] (initial : Fin 2) (t : Real) :
    (μ.prod ν) ((firstStepStateAt initial t) ⁻¹' {otherState initial}) =
      ∫⁻ head, μ {tail | head ≤ t ∧
        stateAt (otherState initial) (twoStateGapsOfPair tail) (t - head) =
          otherState initial} ∂ν := by
  let E : Set (((Nat -> Real) × (Nat -> Real)) × Real) :=
    (firstStepStateAt initial t) ⁻¹' {otherState initial}
  have hE : MeasurableSet E :=
    (measurable_firstStepStateAt initial t) (measurableSet_singleton _)
  calc
    (μ.prod ν) E = Measure.map Prod.swap (ν.prod μ) E := by
      rw [Measure.prod_swap]
    _ = (ν.prod μ) (Prod.swap ⁻¹' E) := by
      rw [Measure.map_apply measurable_swap hE]
    _ = ∫⁻ head, μ (Prod.mk head ⁻¹' (Prod.swap ⁻¹' E)) ∂ν := by
      rw [Measure.prod_apply (measurable_swap hE)]
    _ = ∫⁻ head, μ {tail | head ≤ t ∧
        stateAt (otherState initial) (twoStateGapsOfPair tail) (t - head) =
          otherState initial} ∂ν := by
      apply lintegral_congr
      intro head
      congr 1
      ext tail
      simp only [Set.mem_preimage, Set.mem_setOf_eq]
      by_cases hhead : head ≤ t
      · simp [E, firstStepStateAt, hhead]
      · simp [E, firstStepStateAt, hhead, Ne.symm (otherState_ne initial)]

end TwoStateSwitching

end

end AppliedModelingLib.Probability
