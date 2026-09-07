import AppliedModelingLib.Queueing.ManyServerUniformization
import Mathlib.Probability.HasLaw
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Tactic

/-!
# Marked uniformization for many-server queues

The potential-event kernel of a many-server queue first chooses whether the
event is an arrival or a potential service completion.  This module retains
that event kind as a Boolean mark while preserving the exact unmarked
transition PMF.  The arrival mark has a state-independent Bernoulli law; the
success of a potential-service event remains state dependent through the busy
fraction.
-/

namespace AppliedModelingLib.Probability.Queueing

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

/-- The state-independent arrival-versus-potential-service mark of a
many-server uniformization. -/
def manyServerUniformizationArrivalMark
    (trafficIntensity : ℝ≥0) : PMF Bool :=
  PMF.bernoulli (uniformizedBirthProbability trafficIntensity)
    (uniformizedBirthProbability_le_one trafficIntensity)

/-- At zero traffic intensity every potential event is a service opportunity. -/
theorem manyServerUniformizationArrivalMark_zero :
    manyServerUniformizationArrivalMark 0 = PMF.pure false := by
  ext arrival
  cases arrival <;>
    simp [manyServerUniformizationArrivalMark, uniformizedBirthProbability]

/-- The real expectation of the state-independent arrival mark is its
uniformization arrival probability. -/
theorem integral_manyServerUniformizationArrivalMark_arrival
    (trafficIntensity : ℝ≥0) :
    (∫ arrival : Bool,
      if arrival then (1 : ℝ) else 0 ∂
        (manyServerUniformizationArrivalMark trafficIntensity).toMeasure) =
      (uniformizedBirthProbability trafficIntensity : ℝ) := by
  simp [manyServerUniformizationArrivalMark, PMF.integral_eq_sum, PMF.bernoulli]

/-- Averaging a service-only observable over the independent uniformization
mark simply multiplies it by the potential-service probability. -/
theorem integral_manyServerUniformizationArrivalMark_serviceOnly
    (trafficIntensity : ℝ≥0) (value : ℝ) :
    (∫ arrival : Bool,
      if arrival then 0 else value ∂
        (manyServerUniformizationArrivalMark trafficIntensity).toMeasure) =
      ((1 - uniformizedBirthProbability trafficIntensity : ℝ≥0) : ℝ) * value := by
  have hpotential :
      (1 - (uniformizedBirthProbability trafficIntensity : ℝ≥0∞)).toReal =
        ((1 - uniformizedBirthProbability trafficIntensity : ℝ≥0) : ℝ) := by
    change ((↑(1 : ℝ≥0) - ↑(uniformizedBirthProbability trafficIntensity) : ℝ≥0∞).toReal = _)
    rw [← ENNReal.coe_sub]
    exact ENNReal.coe_toReal _
  simp [manyServerUniformizationArrivalMark, PMF.integral_eq_sum, PMF.bernoulli,
    hpotential]

/-- Given a potential event kind, the many-server queue either takes the
corresponding arrival step or samples whether a potential service finds a
busy server. -/
def manyServerUniformizedStateUpdate
    (servers : ℕ) (hservers : 0 < servers) (state : ℕ) : Bool → PMF ℕ
  | true => PMF.pure (state + 1)
  | false =>
      (PMF.bernoulli (manyServerBusyFraction servers state)
        (manyServerBusyFraction_le_one servers state hservers)).map
        (fun service => if service then state - 1 else state)

/-- The original unmarked kernel is the Bernoulli potential-event mark
followed by the conditional state update. -/
theorem manyServerUniformizedKernel_eq_arrivalMark_bind
    (trafficIntensity : ℝ≥0) (servers : ℕ) (hservers : 0 < servers)
    (state : ℕ) :
    manyServerUniformizedKernel trafficIntensity servers hservers state =
      (manyServerUniformizationArrivalMark trafficIntensity).bind
        (manyServerUniformizedStateUpdate servers hservers state) := by
  change (PMF.bernoulli (uniformizedBirthProbability trafficIntensity)
      (uniformizedBirthProbability_le_one trafficIntensity)).bind (fun arrival =>
        if arrival then PMF.pure (state + 1) else
          (PMF.bernoulli (manyServerBusyFraction servers state)
            (manyServerBusyFraction_le_one servers state hservers)).map
            (fun service => if service then state - 1 else state)) =
    (PMF.bernoulli (uniformizedBirthProbability trafficIntensity)
      (uniformizedBirthProbability_le_one trafficIntensity)).bind
        (manyServerUniformizedStateUpdate servers hservers state)
  apply congrArg (fun update : Bool → PMF ℕ =>
    (PMF.bernoulli (uniformizedBirthProbability trafficIntensity)
      (uniformizedBirthProbability_le_one trafficIntensity)).bind update)
  funext arrival
  cases arrival <;> rfl

/-- A marked potential event records whether it was an arrival and the queue
length after the corresponding arrival, successful service, or idle-service
attempt. -/
def manyServerMarkedUniformizationStep
    (trafficIntensity : ℝ≥0) (servers : ℕ) (hservers : 0 < servers)
    (state : ℕ) : PMF (Bool × ℕ) :=
  (manyServerUniformizationArrivalMark trafficIntensity).bind fun arrival =>
    (manyServerUniformizedStateUpdate servers hservers state arrival).map
      (fun successor => (arrival, successor))

/-- Forgetting the mark of a marked potential event recovers the exact
many-server uniformized transition PMF. -/
theorem manyServerMarkedUniformizationStep_map_snd
    (trafficIntensity : ℝ≥0) (servers : ℕ) (hservers : 0 < servers)
    (state : ℕ) :
    (manyServerMarkedUniformizationStep trafficIntensity servers hservers state).map Prod.snd =
      manyServerUniformizedKernel trafficIntensity servers hservers state := by
  rw [manyServerMarkedUniformizationStep, PMF.map_bind]
  rw [manyServerUniformizedKernel_eq_arrivalMark_bind]
  apply congrArg (fun transition : Bool → PMF ℕ =>
    (manyServerUniformizationArrivalMark trafficIntensity).bind transition)
  funext arrival
  rw [PMF.map_comp]
  simpa [Function.comp_def] using
    PMF.map_id (manyServerUniformizedStateUpdate servers hservers state arrival)

/-- Forgetting the successor state of a marked potential event leaves the
state-independent Bernoulli arrival mark. -/
theorem manyServerMarkedUniformizationStep_map_fst
    (trafficIntensity : ℝ≥0) (servers : ℕ) (hservers : 0 < servers)
    (state : ℕ) :
    (manyServerMarkedUniformizationStep trafficIntensity servers hservers state).map Prod.fst =
      manyServerUniformizationArrivalMark trafficIntensity := by
  rw [manyServerMarkedUniformizationStep, PMF.map_bind]
  calc
    (manyServerUniformizationArrivalMark trafficIntensity).bind (fun arrival =>
        ((manyServerUniformizedStateUpdate servers hservers state arrival).map
          (fun successor => (arrival, successor))).map Prod.fst) =
        (manyServerUniformizationArrivalMark trafficIntensity).bind PMF.pure := by
          apply congrArg (fun transition : Bool → PMF Bool =>
            (manyServerUniformizationArrivalMark trafficIntensity).bind transition)
          funext arrival
          rw [PMF.map_comp]
          change (manyServerUniformizedStateUpdate servers hservers state arrival).map
            (Function.const ℕ arrival) = PMF.pure arrival
          exact PMF.map_const _ arrival
    _ = manyServerUniformizationArrivalMark trafficIntensity := PMF.bind_pure _

/-- A transition is an arrival precisely when it moves the queue one state
upward. -/
def manyServerIsArrivalEdge (state successor : ℕ) : Bool :=
  decide (successor = state + 1)

@[simp] theorem manyServerIsArrivalEdge_marked_step
    (state : ℕ) (arrival : Bool) (service : Bool) :
    manyServerIsArrivalEdge state
      (if arrival then state + 1 else if service then state - 1 else state) = arrival := by
  cases arrival <;> cases service <;>
    simp [manyServerIsArrivalEdge]

/-- Recovering the arrival mark from the successor state of a marked event
agrees with its explicit Boolean mark. -/
theorem manyServerMarkedUniformizationStep_map_recoveredArrivalMark
    (trafficIntensity : ℝ≥0) (servers : ℕ) (hservers : 0 < servers)
    (state : ℕ) :
    (manyServerMarkedUniformizationStep trafficIntensity servers hservers state).map
        (fun z => manyServerIsArrivalEdge state z.2) =
      manyServerUniformizationArrivalMark trafficIntensity := by
  rw [manyServerMarkedUniformizationStep, PMF.map_bind]
  calc
    (manyServerUniformizationArrivalMark trafficIntensity).bind (fun arrival =>
        ((manyServerUniformizedStateUpdate servers hservers state arrival).map
          (fun successor => (arrival, successor))).map
          (fun z => manyServerIsArrivalEdge state z.2)) =
        (manyServerUniformizationArrivalMark trafficIntensity).bind PMF.pure := by
          apply congrArg (fun transition : Bool → PMF Bool =>
            (manyServerUniformizationArrivalMark trafficIntensity).bind transition)
          funext arrival
          cases arrival
          · simp only [manyServerUniformizedStateUpdate]
            rw [PMF.map_comp, PMF.map_comp]
            change (PMF.bernoulli (manyServerBusyFraction servers state)
              (manyServerBusyFraction_le_one servers state hservers)).map
                (fun service => manyServerIsArrivalEdge state
                  (if service then state - 1 else state)) = PMF.pure false
            rw [show (fun service => manyServerIsArrivalEdge state
                (if service then state - 1 else state)) = Function.const Bool false by
              funext service
              simpa using manyServerIsArrivalEdge_marked_step state false service]
            exact PMF.map_const _ false
          · simp only [manyServerUniformizedStateUpdate]
            rw [PMF.pure_map, PMF.pure_map]
            congr 1
            simp [manyServerIsArrivalEdge]
    _ = manyServerUniformizationArrivalMark trafficIntensity := PMF.bind_pure _

end

end AppliedModelingLib.Probability.Queueing
