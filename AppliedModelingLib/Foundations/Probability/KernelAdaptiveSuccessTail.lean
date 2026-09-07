import AppliedModelingLib.Foundations.Probability.FiniteAdaptiveSuccessTail
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# Success-count tails for adaptive measurable kernels

This module lifts the finite-PMF one-sixth success argument to genuinely
continuous, history-dependent experiments.  A trajectory is constructed by
Ionescu--Tulcea from Markov kernels.  At every round an opportunity event and
a nested success event may depend measurably on the entire preceding prefix
and on the fresh outcome.  If each conditional opportunity mass is at most
six times its conditional success mass, the same multiplicative
supermartingale controls the total opportunity count.

No independence between the round events is assumed.  This is the appropriate
interface for adaptive Laplace mechanisms such as HR10.
-/

namespace AppliedModelingLib

open MeasureTheory ProbabilityTheory Set Preorder

noncomputable section

/-- The history/fresh-outcome pair observed at one adaptive round. -/
abbrev KernelAdaptiveRoundPair (Outcome : Type*) (round : ℕ) :=
  (((i : Finset.Iic round) → Outcome) × Outcome)

/-- Extract the history through `round` and the fresh coordinate `round + 1`
from an infinite trajectory.  Coordinate zero is the initial dummy/state
coordinate; round zero consumes coordinate one. -/
def kernelAdaptiveRoundPair
    {Outcome : Type*} (round : ℕ) (trace : ℕ → Outcome) :
    KernelAdaptiveRoundPair Outcome round :=
  (frestrictLe round trace, trace (round + 1))

theorem measurable_kernelAdaptiveRoundPair
    {Outcome : Type*} [MeasurableSpace Outcome] (round : ℕ) :
    Measurable (kernelAdaptiveRoundPair (Outcome := Outcome) round) :=
  (measurable_frestrictLe round).prodMk (measurable_pi_apply (round + 1))

/-- The one-round multiplier associated with measurable opportunity and
success sets. -/
noncomputable def oneSixthSetMultiplier
    {Outcome : Type*} (opportunity success : Set Outcome)
    (outcome : Outcome) : ℝ := by
  classical
  exact if outcome ∈ opportunity then
      if outcome ∈ success then 6 / 11 else 12 / 11
    else
      1

theorem oneSixthSetMultiplier_pos
    {Outcome : Type*} (opportunity success : Set Outcome)
    (outcome : Outcome) :
    0 < oneSixthSetMultiplier opportunity success outcome := by
  classical
  by_cases hopportunity : outcome ∈ opportunity
  · by_cases hsuccess : outcome ∈ success <;>
      simp [oneSixthSetMultiplier, hopportunity, hsuccess]
  · simp [oneSixthSetMultiplier, hopportunity]

theorem oneSixthSetMultiplier_le
    {Outcome : Type*} (opportunity success : Set Outcome)
    (outcome : Outcome) :
    oneSixthSetMultiplier opportunity success outcome ≤ 12 / 11 := by
  classical
  by_cases hopportunity : outcome ∈ opportunity
  · by_cases hsuccess : outcome ∈ success <;>
      simp [oneSixthSetMultiplier, hopportunity, hsuccess] <;> norm_num
  · simp [oneSixthSetMultiplier, hopportunity]
    norm_num

theorem measurable_oneSixthSetMultiplier
    {Outcome : Type*} [MeasurableSpace Outcome]
    {opportunity success : Set Outcome}
    (hopportunity : MeasurableSet opportunity)
    (hsuccess : MeasurableSet success) :
    Measurable (oneSixthSetMultiplier opportunity success) := by
  classical
  unfold oneSixthSetMultiplier
  exact Measurable.ite hopportunity
    (Measurable.ite hsuccess measurable_const measurable_const)
    measurable_const

/-- Indicator algebra for the one-round multiplier. -/
theorem oneSixthSetMultiplier_eq_indicators
    {Outcome : Type*} (opportunity success : Set Outcome)
    (hsubset : success ⊆ opportunity) (outcome : Outcome) :
    oneSixthSetMultiplier opportunity success outcome =
      1 + opportunity.indicator (fun _ => (1 : ℝ)) outcome / 11 -
        6 * success.indicator (fun _ => (1 : ℝ)) outcome / 11 := by
  classical
  by_cases hopportunity : outcome ∈ opportunity
  · by_cases hsuccess : outcome ∈ success <;>
      simp [oneSixthSetMultiplier, hopportunity, hsuccess] <;> norm_num
  · have hnotSuccess : outcome ∉ success := fun hsuccess =>
      hopportunity (hsubset hsuccess)
    simp [oneSixthSetMultiplier, hopportunity, hnotSuccess]

/-- Conditional expected multiplier bound for an arbitrary probability
measure. -/
theorem integral_oneSixthSetMultiplier_le_one
    {Outcome : Type*} [MeasurableSpace Outcome]
    (law : Measure Outcome) [IsProbabilityMeasure law]
    (opportunity success : Set Outcome)
    (hopportunity : MeasurableSet opportunity)
    (hsuccess : MeasurableSet success)
    (hsubset : success ⊆ opportunity)
    (hmass : law.real opportunity ≤ 6 * law.real success) :
    ∫ outcome, oneSixthSetMultiplier opportunity success outcome ∂law ≤ 1 := by
  let opportunityIndicator : Outcome → ℝ :=
    opportunity.indicator (fun _ => 1)
  let successIndicator : Outcome → ℝ :=
    success.indicator (fun _ => 1)
  have hopportunityInt : Integrable opportunityIndicator law := by
    exact Integrable.indicator (integrable_const _) hopportunity
  have hsuccessInt : Integrable successIndicator law := by
    exact Integrable.indicator (integrable_const _) hsuccess
  have hpoint : oneSixthSetMultiplier opportunity success = fun outcome =>
      1 + opportunityIndicator outcome / 11 -
        6 * successIndicator outcome / 11 := by
    funext outcome
    exact oneSixthSetMultiplier_eq_indicators opportunity success hsubset outcome
  rw [hpoint, integral_sub]
  · rw [integral_add]
    · rw [integral_const, integral_div, integral_div, integral_const_mul]
      have hopportunityIntegral : ∫ x, opportunityIndicator x ∂law =
          law.real opportunity := by
        exact integral_indicator_one hopportunity
      have hsuccessIntegral : ∫ x, successIndicator x ∂law =
          law.real success := by
        exact integral_indicator_one hsuccess
      rw [hopportunityIntegral, hsuccessIntegral]
      simp only [probReal_univ, one_smul]
      nlinarith
    · exact integrable_const _
    · exact hopportunityInt.div_const _
  · exact (integrable_const _).add (hopportunityInt.div_const _)
  · exact (hsuccessInt.const_mul _).div_const _

/-- Prefix weight accumulated through `rounds` adaptive rounds. -/
noncomputable def kernelAdaptivePrefixSuccessWeight
    {Outcome : Type*}
    (opportunity success : ∀ round, Set (KernelAdaptiveRoundPair Outcome round)) :
    (rounds : ℕ) → ((i : Finset.Iic rounds) → Outcome) → ℝ
  | 0, _ => 1
  | rounds + 1, history =>
      kernelAdaptivePrefixSuccessWeight opportunity success rounds
          (frestrictLe₂ (π := fun _ : ℕ => Outcome) rounds.le_succ history) *
        oneSixthSetMultiplier (opportunity rounds) (success rounds)
          (frestrictLe₂ (π := fun _ : ℕ => Outcome) rounds.le_succ history,
            history ⟨rounds + 1, Finset.mem_Iic.mpr le_rfl⟩)

/-- Infinite-trajectory form of the prefix weight. -/
def kernelAdaptiveSuccessWeight
    {Outcome : Type*}
    (opportunity success : ∀ round, Set (KernelAdaptiveRoundPair Outcome round))
    (rounds : ℕ) (trace : ℕ → Outcome) : ℝ :=
  kernelAdaptivePrefixSuccessWeight opportunity success rounds
    (frestrictLe rounds trace)

/-- Indicator of a round event, with classical membership hidden behind a
noncomputable definition so theorem statements do not carry a decidability
parameter. -/
noncomputable def kernelAdaptiveEventIndicator
    {Outcome : Type*}
    (event : ∀ round, Set (KernelAdaptiveRoundPair Outcome round))
    (round : ℕ) (trace : ℕ → Outcome) : ℕ := by
  classical
  exact if kernelAdaptiveRoundPair round trace ∈ event round then 1 else 0

/-- Opportunity/success count through a finite horizon. -/
noncomputable def kernelAdaptiveEventCount
    {Outcome : Type*}
    (event : ∀ round, Set (KernelAdaptiveRoundPair Outcome round))
    (rounds : ℕ) (trace : ℕ → Outcome) : ℕ := by
  classical
  exact ∑ round ∈ Finset.range rounds,
      kernelAdaptiveEventIndicator event round trace

/-- The prefix recursion agrees with the history/fresh-coordinate pair read
from an infinite trace. -/
theorem kernelAdaptiveSuccessWeight_succ
    {Outcome : Type*}
    (opportunity success : ∀ round, Set (KernelAdaptiveRoundPair Outcome round))
    (rounds : ℕ) (trace : ℕ → Outcome) :
    kernelAdaptiveSuccessWeight opportunity success (rounds + 1) trace =
      kernelAdaptiveSuccessWeight opportunity success rounds trace *
        oneSixthSetMultiplier (opportunity rounds) (success rounds)
          (kernelAdaptiveRoundPair rounds trace) := by
  rfl

/-- Appending one round adds its event indicator to the count. -/
theorem kernelAdaptiveEventCount_succ
    {Outcome : Type*}
    (event : ∀ round, Set (KernelAdaptiveRoundPair Outcome round))
    (rounds : ℕ) (trace : ℕ → Outcome) :
    kernelAdaptiveEventCount event (rounds + 1) trace =
      kernelAdaptiveEventCount event rounds trace +
        kernelAdaptiveEventIndicator event rounds trace := by
  classical
  simp [kernelAdaptiveEventCount, Finset.sum_range_succ]

/-- Measurability of the last history/fresh-coordinate pair on a finite
prefix. -/
theorem measurable_kernelAdaptivePrefixLastPair
    {Outcome : Type*} [MeasurableSpace Outcome] (rounds : ℕ) :
    Measurable (fun history : ((i : Finset.Iic (rounds + 1)) → Outcome) =>
      (frestrictLe₂ (π := fun _ : ℕ => Outcome) rounds.le_succ history,
        history ⟨rounds + 1, Finset.mem_Iic.mpr le_rfl⟩)) :=
  (measurable_frestrictLe₂ (X := fun _ : ℕ => Outcome) rounds.le_succ).prodMk
    (measurable_pi_apply
      (⟨rounds + 1, Finset.mem_Iic.mpr le_rfl⟩ : Finset.Iic (rounds + 1)))

/-- Prefix weights are measurable when every round event is measurable. -/
theorem measurable_kernelAdaptivePrefixSuccessWeight
    {Outcome : Type*} [MeasurableSpace Outcome]
    (opportunity success : ∀ round, Set (KernelAdaptiveRoundPair Outcome round))
    (hopportunity : ∀ round, MeasurableSet (opportunity round))
    (hsuccess : ∀ round, MeasurableSet (success round)) :
    ∀ rounds, Measurable
      (kernelAdaptivePrefixSuccessWeight opportunity success rounds) := by
  intro rounds
  induction rounds with
  | zero => exact measurable_const
  | succ rounds ih =>
      change Measurable (fun history =>
        kernelAdaptivePrefixSuccessWeight opportunity success rounds
            (frestrictLe₂ (π := fun _ : ℕ => Outcome) rounds.le_succ history) *
          oneSixthSetMultiplier (opportunity rounds) (success rounds)
            (frestrictLe₂ (π := fun _ : ℕ => Outcome) rounds.le_succ history,
              history ⟨rounds + 1, Finset.mem_Iic.mpr le_rfl⟩))
      exact (ih.comp (measurable_frestrictLe₂
          (X := fun _ : ℕ => Outcome) rounds.le_succ)).mul
        ((measurable_oneSixthSetMultiplier
          (hopportunity rounds) (hsuccess rounds)).comp
            (measurable_kernelAdaptivePrefixLastPair rounds))

/-- Infinite-trajectory weights are measurable. -/
theorem measurable_kernelAdaptiveSuccessWeight
    {Outcome : Type*} [MeasurableSpace Outcome]
    (opportunity success : ∀ round, Set (KernelAdaptiveRoundPair Outcome round))
    (hopportunity : ∀ round, MeasurableSet (opportunity round))
    (hsuccess : ∀ round, MeasurableSet (success round))
    (rounds : ℕ) :
    Measurable (kernelAdaptiveSuccessWeight opportunity success rounds) :=
  (measurable_kernelAdaptivePrefixSuccessWeight opportunity success
    hopportunity hsuccess rounds).comp (measurable_frestrictLe rounds)

/-- Prefix weights are positive. -/
theorem kernelAdaptivePrefixSuccessWeight_pos
    {Outcome : Type*}
    (opportunity success : ∀ round, Set (KernelAdaptiveRoundPair Outcome round)) :
    ∀ rounds (history : (i : Finset.Iic rounds) → Outcome),
      0 < kernelAdaptivePrefixSuccessWeight opportunity success rounds history := by
  intro rounds
  induction rounds with
  | zero => intro history; simp [kernelAdaptivePrefixSuccessWeight]
  | succ rounds ih =>
      intro history
      exact mul_pos (ih _) (oneSixthSetMultiplier_pos _ _ _)

/-- A deterministic finite-horizon bound used to obtain integrability. -/
theorem kernelAdaptivePrefixSuccessWeight_le_pow
    {Outcome : Type*}
    (opportunity success : ∀ round, Set (KernelAdaptiveRoundPair Outcome round)) :
    ∀ rounds (history : (i : Finset.Iic rounds) → Outcome),
      kernelAdaptivePrefixSuccessWeight opportunity success rounds history ≤
        (12 / 11 : ℝ) ^ rounds := by
  intro rounds
  induction rounds with
  | zero => intro history; simp [kernelAdaptivePrefixSuccessWeight]
  | succ rounds ih =>
      intro history
      change kernelAdaptivePrefixSuccessWeight opportunity success rounds _ *
          oneSixthSetMultiplier (opportunity rounds) (success rounds) _ ≤ _
      rw [pow_succ]
      exact mul_le_mul (ih _) (oneSixthSetMultiplier_le _ _ _)
        (oneSixthSetMultiplier_pos _ _ _).le (by positivity)

/-- Finite-horizon trajectory weights are integrable under any probability
law. -/
theorem integrable_kernelAdaptiveSuccessWeight
    {Outcome : Type*} [MeasurableSpace Outcome]
    (law : Measure (ℕ → Outcome)) [IsProbabilityMeasure law]
    (opportunity success : ∀ round, Set (KernelAdaptiveRoundPair Outcome round))
    (hopportunity : ∀ round, MeasurableSet (opportunity round))
    (hsuccess : ∀ round, MeasurableSet (success round))
    (rounds : ℕ) :
    Integrable (kernelAdaptiveSuccessWeight opportunity success rounds) law := by
  apply Integrable.of_bound
    (measurable_kernelAdaptiveSuccessWeight opportunity success
      hopportunity hsuccess rounds).aestronglyMeasurable
    ((12 / 11 : ℝ) ^ rounds)
  filter_upwards [] with trace
  rw [Real.norm_eq_abs, abs_of_pos]
  · exact kernelAdaptivePrefixSuccessWeight_le_pow opportunity success rounds _
  · exact kernelAdaptivePrefixSuccessWeight_pos opportunity success rounds _

/-- The continuous adaptive accumulated multiplier has expectation at most
one.  This is the Ionescu--Tulcea supermartingale step. -/
theorem integral_kernelAdaptiveSuccessWeight_le_one
    {Outcome : Type*} [MeasurableSpace Outcome]
    (initialLaw : Measure Outcome) [IsProbabilityMeasure initialLaw]
    (kernel : ∀ round,
      Kernel ((i : Finset.Iic round) → Outcome) Outcome)
    [∀ round, IsMarkovKernel (kernel round)]
    (opportunity success : ∀ round, Set (KernelAdaptiveRoundPair Outcome round))
    (hopportunity : ∀ round, MeasurableSet (opportunity round))
    (hsuccess : ∀ round, MeasurableSet (success round))
    (hsubset : ∀ round, success round ⊆ opportunity round)
    (hmass : ∀ round history,
      (kernel round history).real
          (Prod.mk history ⁻¹' opportunity round) ≤
        6 * (kernel round history).real
          (Prod.mk history ⁻¹' success round)) :
    ∀ rounds,
      ∫ trace, kernelAdaptiveSuccessWeight opportunity success rounds trace
          ∂Kernel.trajMeasure initialLaw kernel ≤ 1 := by
  intro rounds
  induction rounds with
  | zero => simp [kernelAdaptiveSuccessWeight,
      kernelAdaptivePrefixSuccessWeight]
  | succ rounds ih =>
      let trajectory : Measure (ℕ → Outcome) :=
        Kernel.trajMeasure initialLaw kernel
      let historyMeasure : Measure ((i : Finset.Iic rounds) → Outcome) :=
        trajectory.map (frestrictLe rounds)
      let pairMap : (ℕ → Outcome) →
          KernelAdaptiveRoundPair Outcome rounds :=
        kernelAdaptiveRoundPair rounds
      let integrand : KernelAdaptiveRoundPair Outcome rounds → ℝ :=
        fun pair =>
          kernelAdaptivePrefixSuccessWeight opportunity success rounds pair.1 *
            oneSixthSetMultiplier (opportunity rounds) (success rounds) pair
      letI : IsProbabilityMeasure trajectory := by
        dsimp [trajectory]
        infer_instance
      letI : IsProbabilityMeasure historyMeasure := by
        dsimp [historyMeasure]
        exact Measure.isProbabilityMeasure_map
          (measurable_frestrictLe rounds).aemeasurable
      have hintegrandMeasurable : Measurable integrand := by
        dsimp [integrand]
        exact ((measurable_kernelAdaptivePrefixSuccessWeight opportunity success
          hopportunity hsuccess rounds).comp measurable_fst).mul
            (measurable_oneSixthSetMultiplier
              (hopportunity rounds) (hsuccess rounds))
      have hintegrandBound : ∀ pair,
          |integrand pair| ≤ (12 / 11 : ℝ) ^ (rounds + 1) := by
        intro pair
        rw [abs_of_pos]
        · dsimp [integrand]
          rw [pow_succ]
          exact mul_le_mul
            (kernelAdaptivePrefixSuccessWeight_le_pow
              opportunity success rounds pair.1)
            (oneSixthSetMultiplier_le _ _ _)
            (oneSixthSetMultiplier_pos _ _ _).le (by positivity)
        · dsimp [integrand]
          exact mul_pos
            (kernelAdaptivePrefixSuccessWeight_pos
              opportunity success rounds pair.1)
            (oneSixthSetMultiplier_pos _ _ _)
      have hintegrand : Integrable integrand
          (historyMeasure ⊗ₘ kernel rounds) := by
        apply Integrable.of_bound hintegrandMeasurable.aestronglyMeasurable
          ((12 / 11 : ℝ) ^ (rounds + 1))
        exact ae_of_all _ hintegrandBound
      have hpairMap : Measurable pairMap :=
        measurable_kernelAdaptiveRoundPair rounds
      have hjoint : trajectory.map pairMap =
          historyMeasure ⊗ₘ kernel rounds := by
        dsimp [trajectory, historyMeasure, pairMap]
        exact Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure.symm
      have hprefixIntegrable : Integrable
          (kernelAdaptivePrefixSuccessWeight opportunity success rounds)
          historyMeasure := by
        apply Integrable.of_bound
          (measurable_kernelAdaptivePrefixSuccessWeight opportunity success
            hopportunity hsuccess rounds).aestronglyMeasurable
          ((12 / 11 : ℝ) ^ rounds)
        filter_upwards [] with history
        rw [Real.norm_eq_abs, abs_of_pos]
        · exact kernelAdaptivePrefixSuccessWeight_le_pow
            opportunity success rounds history
        · exact kernelAdaptivePrefixSuccessWeight_pos
            opportunity success rounds history
      calc
        (∫ trace, kernelAdaptiveSuccessWeight opportunity success
            (rounds + 1) trace ∂trajectory) =
            ∫ trace, integrand (pairMap trace) ∂trajectory := by
          apply integral_congr_ae
          filter_upwards [] with trace
          exact kernelAdaptiveSuccessWeight_succ
            opportunity success rounds trace
        _ = ∫ pair, integrand pair ∂trajectory.map pairMap := by
          exact (integral_map hpairMap.aemeasurable
            hintegrandMeasurable.aestronglyMeasurable).symm
        _ = ∫ pair, integrand pair ∂(historyMeasure ⊗ₘ kernel rounds) := by
          rw [hjoint]
        _ = ∫ history, ∫ next, integrand (history, next)
              ∂kernel rounds history ∂historyMeasure := by
          exact Measure.integral_compProd hintegrand
        _ ≤ ∫ history,
              kernelAdaptivePrefixSuccessWeight opportunity success rounds history
              ∂historyMeasure := by
          apply integral_mono_ae hintegrand.integral_compProd hprefixIntegrable
          filter_upwards [] with history
          dsimp [integrand]
          rw [integral_const_mul]
          have hconditional := integral_oneSixthSetMultiplier_le_one
            (kernel rounds history)
            (Prod.mk history ⁻¹' opportunity rounds)
            (Prod.mk history ⁻¹' success rounds)
            ((hopportunity rounds).preimage measurable_prodMk_left)
            ((hsuccess rounds).preimage measurable_prodMk_left)
            (preimage_mono (hsubset rounds))
            (hmass rounds history)
          exact mul_le_of_le_one_right
            (kernelAdaptivePrefixSuccessWeight_pos
              opportunity success rounds history).le hconditional
        _ = ∫ trace, kernelAdaptiveSuccessWeight opportunity success rounds trace
              ∂trajectory := by
          exact integral_map (measurable_frestrictLe rounds).aemeasurable
            (measurable_kernelAdaptivePrefixSuccessWeight opportunity success
              hopportunity hsuccess rounds).aestronglyMeasurable
        _ ≤ 1 := ih

/-- One-round multiplier as an opportunity factor and a success penalty. -/
theorem oneSixthSetMultiplier_eq_eventIndicator_powers
    {Outcome : Type*}
    (opportunity success : ∀ round, Set (KernelAdaptiveRoundPair Outcome round))
    (hsubset : ∀ round, success round ⊆ opportunity round)
    (round : ℕ) (trace : ℕ → Outcome) :
    oneSixthSetMultiplier (opportunity round) (success round)
        (kernelAdaptiveRoundPair round trace) =
      (12 / 11 : ℝ) ^ kernelAdaptiveEventIndicator opportunity round trace *
        (1 / 2 : ℝ) ^ kernelAdaptiveEventIndicator success round trace := by
  classical
  let pair := kernelAdaptiveRoundPair round trace
  by_cases hopportunity : pair ∈ opportunity round
  · by_cases hsuccess : pair ∈ success round <;>
      simp [oneSixthSetMultiplier, kernelAdaptiveEventIndicator, pair,
        hopportunity, hsuccess] <;> norm_num
  · have hnotSuccess : pair ∉ success round := fun hsuccess =>
      hopportunity (hsubset round hsuccess)
    simp [oneSixthSetMultiplier, kernelAdaptiveEventIndicator, pair,
      hopportunity, hnotSuccess]

/-- Closed form of the continuous adaptive multiplier in terms of event
counts. -/
theorem kernelAdaptiveSuccessWeight_eq_count_powers
    {Outcome : Type*}
    (opportunity success : ∀ round, Set (KernelAdaptiveRoundPair Outcome round))
    (hsubset : ∀ round, success round ⊆ opportunity round) :
    ∀ rounds (trace : ℕ → Outcome),
    kernelAdaptiveSuccessWeight opportunity success rounds trace =
      (12 / 11 : ℝ) ^ kernelAdaptiveEventCount opportunity rounds trace *
        (1 / 2 : ℝ) ^ kernelAdaptiveEventCount success rounds trace := by
  intro rounds
  induction rounds with
  | zero =>
      intro trace
      simp [kernelAdaptiveSuccessWeight, kernelAdaptivePrefixSuccessWeight,
        kernelAdaptiveEventCount]
  | succ rounds ih =>
      intro trace
      rw [kernelAdaptiveSuccessWeight_succ,
        kernelAdaptiveEventCount_succ, kernelAdaptiveEventCount_succ,
        ih trace,
        oneSixthSetMultiplier_eq_eventIndicator_powers
          opportunity success hsubset]
      rw [pow_add, pow_add]
      ring

/-- Logarithm of the continuous adaptive multiplier. -/
theorem log_kernelAdaptiveSuccessWeight
    {Outcome : Type*}
    (opportunity success : ∀ round, Set (KernelAdaptiveRoundPair Outcome round))
    (hsubset : ∀ round, success round ⊆ opportunity round)
    (rounds : ℕ) (trace : ℕ → Outcome) :
    Real.log (kernelAdaptiveSuccessWeight opportunity success rounds trace) =
      (kernelAdaptiveEventCount opportunity rounds trace : ℝ) *
          Real.log (12 / 11 : ℝ) -
        (kernelAdaptiveEventCount success rounds trace : ℝ) * Real.log 2 := by
  rw [kernelAdaptiveSuccessWeight_eq_count_powers
    opportunity success hsubset]
  have hbase : (12 / 11 : ℝ) ≠ 0 := by norm_num
  have hhalf : (1 / 2 : ℝ) ≠ 0 := by norm_num
  rw [Real.log_mul (pow_ne_zero _ hbase) (pow_ne_zero _ hhalf),
    Real.log_pow, Real.log_pow]
  have hlogHalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one]
    ring
  rw [hlogHalf]
  ring

/-- The HR10 count threshold forces the continuous adaptive multiplier above
the Markov threshold. -/
theorem kernelAdaptiveSuccessWeight_gt_two_div
    {Outcome : Type*}
    (opportunity success : ∀ round, Set (KernelAdaptiveRoundPair Outcome round))
    (hsubset : ∀ round, success round ⊆ opportunity round)
    {rounds maxSuccesses : ℕ} (hmaxSuccesses : 0 < maxSuccesses)
    {delta : ℝ} (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (trace : ℕ → Outcome)
    (hopportunityCount :
      32 * (maxSuccesses : ℝ) * Real.log (2 / delta) <
        (kernelAdaptiveEventCount opportunity rounds trace : ℝ))
    (hsuccessCount :
      kernelAdaptiveEventCount success rounds trace ≤ maxSuccesses) :
    2 / delta < kernelAdaptiveSuccessWeight opportunity success rounds trace := by
  let opportunityCount : ℝ :=
    kernelAdaptiveEventCount opportunity rounds trace
  let successCount : ℝ := kernelAdaptiveEventCount success rounds trace
  let maxCount : ℝ := maxSuccesses
  let confidenceLog : ℝ := Real.log (2 / delta)
  have hratioPos : 0 < (2 / delta : ℝ) := div_pos (by norm_num) hdelta
  have hratioTwo : (2 : ℝ) ≤ 2 / delta := by
    rw [le_div_iff₀ hdelta]
    nlinarith
  have hconfidence : (2 / 3 : ℝ) ≤ confidenceLog := by
    exact two_thirds_le_log_two.trans
      (Real.log_le_log (by norm_num : (0 : ℝ) < 2) hratioTwo)
  have hopportunityNonneg : 0 ≤ opportunityCount := by
    dsimp [opportunityCount]
    positivity
  have hsuccessNonneg : 0 ≤ successCount := by
    dsimp [successCount]
    positivity
  have hmaxOne : 1 ≤ maxCount := by
    dsimp [maxCount]
    exact_mod_cast (show 1 ≤ maxSuccesses by omega)
  have hmaxNonneg : 0 ≤ maxCount := by linarith
  have hopportunityLog :
      (8 / 3 : ℝ) * maxCount * confidenceLog <
        opportunityCount * Real.log (12 / 11 : ℝ) := by
    have hscaled := mul_lt_mul_of_pos_right hopportunityCount
      (show (0 : ℝ) < 1 / 12 by norm_num)
    have hbase := mul_le_mul_of_nonneg_left
      one_twelfth_le_log_twelve_elevenths hopportunityNonneg
    dsimp [opportunityCount, maxCount, confidenceLog] at hscaled ⊢
    calc
      (8 / 3 : ℝ) * (maxSuccesses : ℝ) * Real.log (2 / delta) =
          (32 * (maxSuccesses : ℝ) * Real.log (2 / delta)) *
            (1 / 12) := by ring
      _ < (kernelAdaptiveEventCount opportunity rounds trace : ℝ) *
          (1 / 12) := hscaled
      _ ≤ (kernelAdaptiveEventCount opportunity rounds trace : ℝ) *
          Real.log (12 / 11 : ℝ) := hbase
  have hsuccessCast : successCount ≤ maxCount := by
    dsimp [successCount, maxCount]
    exact_mod_cast hsuccessCount
  have hlogTwoNonneg : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hsuccessLog : successCount * Real.log 2 ≤ maxCount := by
    calc
      successCount * Real.log 2 ≤ maxCount * Real.log 2 :=
        mul_le_mul_of_nonneg_right hsuccessCast hlogTwoNonneg
      _ ≤ maxCount * 1 :=
        mul_le_mul_of_nonneg_left log_two_lt_one.le hmaxNonneg
      _ = maxCount := by ring
  have hlogWeight :
      (8 / 3 : ℝ) * maxCount * confidenceLog - maxCount <
        Real.log (kernelAdaptiveSuccessWeight opportunity success rounds trace) := by
    rw [log_kernelAdaptiveSuccessWeight opportunity success hsubset]
    dsimp [opportunityCount, successCount, maxCount] at hopportunityLog hsuccessLog ⊢
    linarith
  have hcoefficient :
      0 ≤ (8 / 3 : ℝ) * confidenceLog - 1 := by
    nlinarith
  have hproduct :
      0 ≤ (maxCount - 1) * ((8 / 3 : ℝ) * confidenceLog - 1) :=
    mul_nonneg (by linarith) hcoefficient
  have hconfidenceGap :
      confidenceLog <
        (8 / 3 : ℝ) * maxCount * confidenceLog - maxCount := by
    nlinarith
  have hlogThreshold :
      confidenceLog <
        Real.log (kernelAdaptiveSuccessWeight opportunity success rounds trace) :=
    hconfidenceGap.trans hlogWeight
  have hweightPos :
      0 < kernelAdaptiveSuccessWeight opportunity success rounds trace :=
    kernelAdaptivePrefixSuccessWeight_pos opportunity success rounds _
  have hexp := (Real.lt_log_iff_exp_lt hweightPos).1 hlogThreshold
  have hexpConfidence : Real.exp confidenceLog = 2 / delta := by
    exact Real.exp_log hratioPos
  rw [hexpConfidence] at hexp
  exact hexp

/-- Adaptive one-sixth success-count tail for measurable Markov kernels. -/
theorem kernelAdaptiveOneSixthOpportunityTail
    {Outcome : Type*} [MeasurableSpace Outcome]
    (initialLaw : Measure Outcome) [IsProbabilityMeasure initialLaw]
    (kernel : ∀ round,
      Kernel ((i : Finset.Iic round) → Outcome) Outcome)
    [∀ round, IsMarkovKernel (kernel round)]
    (opportunity success : ∀ round, Set (KernelAdaptiveRoundPair Outcome round))
    (hopportunity : ∀ round, MeasurableSet (opportunity round))
    (hsuccess : ∀ round, MeasurableSet (success round))
    (hsubset : ∀ round, success round ⊆ opportunity round)
    (hmass : ∀ round history,
      (kernel round history).real
          (Prod.mk history ⁻¹' opportunity round) ≤
        6 * (kernel round history).real
          (Prod.mk history ⁻¹' success round))
    (rounds maxSuccesses : ℕ) (hmaxSuccesses : 0 < maxSuccesses)
    (delta : ℝ) (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1) :
    (Kernel.trajMeasure initialLaw kernel).real {trace |
      32 * (maxSuccesses : ℝ) * Real.log (2 / delta) <
          (kernelAdaptiveEventCount opportunity rounds trace : ℝ) ∧
        kernelAdaptiveEventCount success rounds trace ≤ maxSuccesses} ≤
      delta / 2 := by
  let trajectory : Measure (ℕ → Outcome) :=
    Kernel.trajMeasure initialLaw kernel
  let weight : (ℕ → Outcome) → ℝ :=
    kernelAdaptiveSuccessWeight opportunity success rounds
  let threshold : ℝ := 2 / delta
  letI : IsProbabilityMeasure trajectory := by
    dsimp [trajectory]
    infer_instance
  have hweightNonneg : 0 ≤ᵐ[trajectory] weight := by
    filter_upwards [] with trace
    exact (kernelAdaptivePrefixSuccessWeight_pos
      opportunity success rounds _).le
  have hweightIntegrable : Integrable weight trajectory :=
    integrable_kernelAdaptiveSuccessWeight trajectory opportunity success
      hopportunity hsuccess rounds
  have hexpectation : ∫ trace, weight trace ∂trajectory ≤ 1 :=
    integral_kernelAdaptiveSuccessWeight_le_one initialLaw kernel
      opportunity success hopportunity hsuccess hsubset hmass rounds
  have hthresholdPos : 0 < threshold := div_pos (by norm_num) hdelta
  have hmarkov : threshold * trajectory.real {trace | threshold ≤ weight trace} ≤ 1 :=
    (mul_meas_ge_le_integral_of_nonneg hweightNonneg hweightIntegrable
      threshold).trans hexpectation
  have htail : trajectory.real {trace | threshold ≤ weight trace} ≤ delta / 2 := by
    have hdiv : trajectory.real {trace | threshold ≤ weight trace} ≤
        1 / threshold := by
      rw [le_div_iff₀ hthresholdPos]
      simpa [mul_comm] using hmarkov
    calc
      trajectory.real {trace | threshold ≤ weight trace} ≤ 1 / threshold := hdiv
      _ = delta / 2 := by
        dsimp [threshold]
        field_simp [hdelta.ne']
  have hinclusion : {trace |
      32 * (maxSuccesses : ℝ) * Real.log (2 / delta) <
          (kernelAdaptiveEventCount opportunity rounds trace : ℝ) ∧
        kernelAdaptiveEventCount success rounds trace ≤ maxSuccesses} ⊆
      {trace | threshold ≤ weight trace} := by
    intro trace htrace
    exact (kernelAdaptiveSuccessWeight_gt_two_div opportunity success hsubset
      hmaxSuccesses hdelta hdeltaOne trace htrace.1 htrace.2).le
  exact (measureReal_mono hinclusion (measure_ne_top trajectory _)).trans htail

end

end AppliedModelingLib
