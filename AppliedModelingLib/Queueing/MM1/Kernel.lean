import AppliedModelingLib.Queueing.MM1.Uniformization
import Mathlib.Probability.Kernel.Invariance
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Countable M/M/1 jump kernels and Mathlib invariance

This module lifts the reflected countable PMF jump kernel to Mathlib's
`Kernel` API.  It transfers PMF stationarity to `Kernel.Invariant` and proves
that every finite-step kernel preserves the geometric stationary marginal.

It still does not construct an infinite stationary trajectory or the
continuous-time Poisson-clock M/M/1 path; those require a separate
Ionescu--Tulcea and time-change construction.
-/

open scoped ENNReal NNReal

namespace AppliedModelingLib.Probability.Queueing

open MeasureTheory ProbabilityTheory

/-- Interpret a countable PMF transition matrix as a Mathlib Markov kernel.
This generic lift is used both for the queue-length chain and for augmented
countable states that carry an event mark. -/
noncomputable def countablePMFKernel
    {α : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (K : CountableMarkovKernel α) : Kernel α α :=
  Kernel.ofFunOfCountable fun n => (K n).toMeasure

/-- Interpret a countable PMF-valued transition between possibly different
countable state spaces as a Mathlib Markov kernel. -/
noncomputable def countablePMFKernelTo
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Countable α] [Countable β] [MeasurableSingletonClass α]
    [MeasurableSingletonClass β] (K : α → PMF β) : Kernel α β :=
  Kernel.ofFunOfCountable fun state => (K state).toMeasure

instance {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Countable α] [Countable β] [MeasurableSingletonClass α]
    [MeasurableSingletonClass β] (K : α → PMF β) :
    IsMarkovKernel (countablePMFKernelTo K) where
  isProbabilityMeasure state := by
    change IsProbabilityMeasure ((K state).toMeasure)
    infer_instance

instance {α : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (K : CountableMarkovKernel α) : IsMarkovKernel (countablePMFKernel K) where
  isProbabilityMeasure n := by
    change IsProbabilityMeasure ((K n).toMeasure)
    infer_instance

lemma pmf_toMeasure_eq_count_withDensity
    {α : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (p : PMF α) :
  p.toMeasure = Measure.count.withDensity p := by
  ext s hs
  rw [PMF.toMeasure_apply_eq_tsum, withDensity_apply _ hs,
    ← lintegral_indicator hs, lintegral_count]

lemma bind_countablePMFKernel_eq_pmf_bind_toMeasure
    {α : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (π : PMF α) (K : CountableMarkovKernel α) :
  π.toMeasure.bind (countablePMFKernel K) = (π.bind K).toMeasure := by
  ext s hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable _), countablePMFKernel,
    pmf_toMeasure_eq_count_withDensity π,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_of_countable _)
      (measurable_of_countable _),
    lintegral_count]
  rw [PMF.toMeasure_bind_apply π K s hs]
  rfl

/-- Binding a countable PMF through its measure-valued kernel lift agrees
exactly with PMF binding, also when the input and output state spaces differ. -/
lemma bind_countablePMFKernelTo_eq_pmf_bind_toMeasure
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Countable α] [Countable β] [MeasurableSingletonClass α]
    [MeasurableSingletonClass β] (π : PMF α) (K : α → PMF β) :
    π.toMeasure.bind (countablePMFKernelTo K) = (π.bind K).toMeasure := by
  ext s hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable _), countablePMFKernelTo,
    pmf_toMeasure_eq_count_withDensity π,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_of_countable _)
      (measurable_of_countable _), lintegral_count]
  rw [PMF.toMeasure_bind_apply π K s hs]
  rfl

/-- The joint PMF obtained by sampling an input state and then one output
from a countable PMF-valued transition between countable state spaces. -/
noncomputable def initialTransitionPairPMFTo
    {α β : Type*} (initial : PMF α) (kernel : α → PMF β) : PMF (α × β) :=
  initial.bind fun state => PMF.map (Prod.mk state) (kernel state)

/-- The measure of a cross-space countable initial/transition pair PMF is the
composition product of the initial measure and the corresponding kernel. -/
theorem initialTransitionPairPMFTo_toMeasure_eq_compProd
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Countable α] [Countable β] [MeasurableSingletonClass α]
    [MeasurableSingletonClass β] (initial : PMF α) (kernel : α → PMF β) :
    (initialTransitionPairPMFTo initial kernel).toMeasure =
      initial.toMeasure ⊗ₘ countablePMFKernelTo kernel := by
  ext s hs
  rw [initialTransitionPairPMFTo, PMF.toMeasure_bind_apply initial (fun state =>
    PMF.map (Prod.mk state) (kernel state)) s hs]
  rw [Measure.compProd_apply hs]
  rw [pmf_toMeasure_eq_count_withDensity initial,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_of_countable _)
      (measurable_of_countable _), lintegral_count]
  apply tsum_congr
  intro state
  rw [← PMF.toMeasure_map (Prod.mk state) (kernel state) measurable_prodMk_left,
    Measure.map_apply measurable_prodMk_left hs]
  rfl

namespace CountableMarkovKernel

/-- Lifting the Kleisli iterate of a countable transition PMF gives exactly
the corresponding power of its Mathlib Markov kernel. -/
theorem countablePMFKernel_iterate_eq_pow
    {α : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (kernel : CountableMarkovKernel α) (steps : ℕ) :
    countablePMFKernel (iterate kernel steps) = countablePMFKernel kernel ^ steps := by
  induction steps with
  | zero =>
      rw [iterate_zero, pow_zero]
      apply Kernel.ext
      intro state
      unfold countablePMFKernel Kernel.ofFunOfCountable
      change (PMF.pure state).toMeasure = Kernel.id state
      rw [PMF.toMeasure_pure, Kernel.id_apply]
  | succ steps ih =>
      rw [iterate_succ, Kernel.pow_add (countablePMFKernel kernel) steps 1, ← ih]
      simp only [pow_one]
      apply Kernel.ext
      intro state
      rw [Kernel.comp_apply]
      exact (bind_countablePMFKernel_eq_pmf_bind_toMeasure
        (kernel state) (iterate kernel steps)).symm

/-- The joint PMF obtained by sampling an initial state from `initial` and
then one transition from a countable-state transition PMF. -/
noncomputable def initialTransitionPairPMF {α : Type*}
    (initial : PMF α) (kernel : CountableMarkovKernel α) : PMF (α × α) :=
  initial.bind fun state => PMF.map (Prod.mk state) (kernel state)

/-- The measure of the initial/next-state pair PMF is Mathlib's composition
product of the initial measure with the lifted transition kernel. -/
theorem initialTransitionPairPMF_toMeasure_eq_compProd
    {α : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (initial : PMF α) (kernel : CountableMarkovKernel α) :
    (initialTransitionPairPMF initial kernel).toMeasure =
      initial.toMeasure ⊗ₘ countablePMFKernel kernel := by
  ext s hs
  rw [initialTransitionPairPMF, PMF.toMeasure_bind_apply initial (fun state =>
    PMF.map (Prod.mk state) (kernel state)) s hs]
  rw [Measure.compProd_apply hs]
  rw [pmf_toMeasure_eq_count_withDensity initial,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_of_countable _)
      (measurable_of_countable _), lintegral_count]
  apply tsum_congr
  intro state
  rw [← PMF.toMeasure_map (Prod.mk state) (kernel state) measurable_prodMk_left,
    Measure.map_apply measurable_prodMk_left hs]
  rfl

/-- The continuous-parameter Markov kernel obtained by Poissonizing the
finite-step transition PMFs of a countable-state chain. -/
noncomputable def poissonizedKernel
    {α : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (kernel : CountableMarkovKernel α) (mean : NNReal) : Kernel α α :=
  countablePMFKernel (poissonized kernel mean)

/-- At zero exposure, Poissonization gives the identity Markov kernel. -/
theorem poissonizedKernel_zero
    {α : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (kernel : CountableMarkovKernel α) :
    poissonizedKernel kernel 0 = Kernel.id := by
  apply Kernel.ext
  intro state
  change (poissonized kernel 0 state).toMeasure = Kernel.id state
  rw [poissonized_zero, PMF.toMeasure_pure, Kernel.id_apply]

/-- The Poissonized transition kernels satisfy the continuous-parameter
Chapman--Kolmogorov equation. The composition order is the usual kernel order:
the right-hand kernel advances through the first exposure. -/
theorem poissonizedKernel_comp
    {α : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (kernel : CountableMarkovKernel α) (firstMean secondMean : NNReal) :
    poissonizedKernel kernel secondMean ∘ₖ poissonizedKernel kernel firstMean =
      poissonizedKernel kernel (firstMean + secondMean) := by
  apply Kernel.ext
  intro state
  rw [Kernel.comp_apply]
  change (poissonized kernel firstMean state).toMeasure.bind
      (countablePMFKernel (poissonized kernel secondMean)) =
    (poissonized kernel (firstMean + secondMean) state).toMeasure
  rw [bind_countablePMFKernel_eq_pmf_bind_toMeasure,
    poissonized_bind_poissonized]

/-- Parameterize a Poissonized transition kernel by a nonnegative real clock
rate and a nonnegative real time. -/
noncomputable def poissonizedKernelAtRate
    {α : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (kernel : CountableMarkovKernel α) (rate : ℝ) (hRate : 0 ≤ rate)
    (time : ℝ≥0) : Kernel α α :=
  poissonizedKernel kernel
    (PoissonProcess.rateExposureParam rate (time : ℝ)
      (mul_nonneg hRate (NNReal.coe_nonneg time)))

/-- A fixed-rate Poissonized transition kernel forms a time-homogeneous
continuous-time semigroup. -/
theorem poissonizedKernelAtRate_comp
    {α : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (kernel : CountableMarkovKernel α) (rate : ℝ) (hRate : 0 ≤ rate)
    (firstTime secondTime : ℝ≥0) :
    poissonizedKernelAtRate kernel rate hRate secondTime ∘ₖ
      poissonizedKernelAtRate kernel rate hRate firstTime =
        poissonizedKernelAtRate kernel rate hRate (firstTime + secondTime) := by
  unfold poissonizedKernelAtRate
  rw [poissonizedKernel_comp]
  congr 1
  exact (PoissonProcess.rateExposureParam_add rate (firstTime : ℝ) (secondTime : ℝ)
    hRate (NNReal.coe_nonneg firstTime) (NNReal.coe_nonneg secondTime)).symm

/-- The initial/terminal pair under a Poissonized transition row can also be
sampled by first drawing the Poisson number of finite transitions. -/
theorem initialTransitionPairPMF_poissonized_eq_bind
    {α : Type*} (initial : PMF α) (kernel : CountableMarkovKernel α)
    (mean : NNReal) :
    initialTransitionPairPMF initial (poissonized kernel mean) =
      (ProbabilityTheory.poissonMeasure mean).toPMF.bind
        (fun steps => initialTransitionPairPMF initial (iterate kernel steps)) := by
  unfold initialTransitionPairPMF poissonized
  simp_rw [PMF.map_bind]
  rw [PMF.bind_comm]

/-- The composition product with a Poissonized transition kernel is exactly
the Poisson mixture of the finite-step composition products. -/
theorem compProd_poissonizedKernel_apply_eq_lintegral_iterate
    {α : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (initial : PMF α) (kernel : CountableMarkovKernel α) (mean : NNReal)
    (s : Set (α × α)) (hs : MeasurableSet s) :
    (initial.toMeasure ⊗ₘ poissonizedKernel kernel mean) s =
      ∫⁻ steps, (initial.toMeasure ⊗ₘ
        countablePMFKernel (iterate kernel steps)) s ∂
        ProbabilityTheory.poissonMeasure mean := by
  change (initial.toMeasure ⊗ₘ countablePMFKernel (poissonized kernel mean)) s = _
  rw [← initialTransitionPairPMF_toMeasure_eq_compProd initial
      (poissonized kernel mean)]
  rw [initialTransitionPairPMF_poissonized_eq_bind,
    PMF.toMeasure_bind_apply _ _ s hs]
  conv_rhs => rw [← Measure.toPMF_toMeasure (ProbabilityTheory.poissonMeasure mean)]
  rw [pmf_toMeasure_eq_count_withDensity
    (ProbabilityTheory.poissonMeasure mean).toPMF,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_of_countable _)
      (measurable_of_countable _), lintegral_count]
  simp_rw [initialTransitionPairPMF_toMeasure_eq_compProd]
  rfl

end CountableMarkovKernel

theorem PMFStationary.kernelInvariant
    {α : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    {K : CountableMarkovKernel α} {π : PMF α}
    (hstationary : PMFStationary K π) :
    Kernel.Invariant (countablePMFKernel K) π.toMeasure := by
  rw [Kernel.Invariant, bind_countablePMFKernel_eq_pmf_bind_toMeasure, hstationary]

/-- Every finite-step transition kernel preserves the stationary marginal. -/
theorem PMFStationary.kernelInvariant_pow
    {α : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    {K : CountableMarkovKernel α} {π : PMF α}
    (hstationary : PMFStationary K π) (n : ℕ) :
    Kernel.Invariant (countablePMFKernel K ^ n) π.toMeasure := by
  induction n with
  | zero =>
      rw [pow_zero, Kernel.Invariant]
      ext s hs
      rw [Measure.bind_apply hs (Kernel.aemeasurable _)]
      change (∫⁻ a, Kernel.id a s ∂π.toMeasure) = π.toMeasure s
      simp_rw [Kernel.id_apply, Measure.dirac_apply' _ hs]
      exact lintegral_indicator_one hs
  | succ n ih =>
      rw [pow_succ]
      exact ih.comp hstationary.kernelInvariant

/-- A stationary PMF is preserved by every finite Kleisli iterate of its
countable transition kernel. -/
theorem PMFStationary.iterate
    {α : Type*} {K : CountableMarkovKernel α} {π : PMF α}
    (hstationary : PMFStationary K π) (steps : ℕ) :
    π.bind (CountableMarkovKernel.iterate K steps) = π := by
  induction steps with
  | zero =>
      simp [CountableMarkovKernel.iterate]
  | succ steps ih =>
      rw [CountableMarkovKernel.iterate_succ]
      rw [← PMF.bind_bind, hstationary, ih]

/-- Poissonizing a stationary countable transition kernel preserves its
stationary PMF. -/
theorem PMFStationary.poissonized
    {α : Type*} {K : CountableMarkovKernel α} {π : PMF α}
    (hstationary : PMFStationary K π) (mean : NNReal) :
    π.bind (CountableMarkovKernel.poissonized K mean) = π := by
  unfold CountableMarkovKernel.poissonized
  calc
    (π.bind fun state =>
      (ProbabilityTheory.poissonMeasure mean).toPMF.bind
        (fun steps => CountableMarkovKernel.iterate K steps state)) =
        (ProbabilityTheory.poissonMeasure mean).toPMF.bind
          (fun steps => π.bind (CountableMarkovKernel.iterate K steps)) := by
            exact PMF.bind_comm π (ProbabilityTheory.poissonMeasure mean).toPMF
              (fun state steps => CountableMarkovKernel.iterate K steps state)
    _ = (ProbabilityTheory.poissonMeasure mean).toPMF.bind (fun _ => π) := by
      congr 1
      funext steps
      exact hstationary.iterate steps
    _ = π := PMF.bind_const _ _

/-- The continuous-parameter Poissonized kernel preserves the measure induced
by any stationary countable PMF. -/
theorem PMFStationary.poissonizedKernelInvariant
    {α : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    {K : CountableMarkovKernel α} {π : PMF α}
    (hstationary : PMFStationary K π) (mean : NNReal) :
    Kernel.Invariant (CountableMarkovKernel.poissonizedKernel K mean) π.toMeasure := by
  change π.toMeasure.bind (countablePMFKernel
    (CountableMarkovKernel.poissonized K mean)) = π.toMeasure
  rw [bind_countablePMFKernel_eq_pmf_bind_toMeasure, hstationary.poissonized]

/-- A fixed-rate Poissonized transition semigroup preserves the measure
induced by any stationary countable PMF at every nonnegative time. -/
theorem PMFStationary.poissonizedKernelAtRateInvariant
    {α : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    {K : CountableMarkovKernel α} {π : PMF α}
    (hstationary : PMFStationary K π) (rate : ℝ) (hRate : 0 ≤ rate)
    (time : ℝ≥0) :
    Kernel.Invariant
      (CountableMarkovKernel.poissonizedKernelAtRate K rate hRate time)
      π.toMeasure := by
  exact hstationary.poissonizedKernelInvariant _

theorem geoNNPMF_uniformized_kernelInvariant
    (rho : ℝ≥0) (hrho : rho < 1) :
    Kernel.Invariant
      (countablePMFKernel
        (reflectedBirthDeathKernel (uniformizedBirthProbability rho)
          (uniformizedBirthProbability_le_one rho)))
      (geoNNPMF rho hrho).toMeasure :=
  (geoNNPMF_uniformized_stationary rho hrho).kernelInvariant

end AppliedModelingLib.Probability.Queueing
