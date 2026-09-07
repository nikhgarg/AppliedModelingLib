import AppliedModelingLib.Foundations.Probability.PoissonParameterKernel
import AppliedModelingLib.Queueing.MM1.Kernel
import Mathlib.Probability.Kernel.Composition.Prod

/-!
# Countable-state transitions over a random duration

This module combines a countable potential-event chain with the measurable
Poisson kernel for a nonnegative exposure. It yields a genuine Markov kernel
whose inputs are an exposure and an initial state, rather than a
certificate-shaped random-time transition.
-/

namespace AppliedModelingLib.Probability.Queueing

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal NNReal

/-- Given a state and a number of potential events, apply exactly that many
steps of a countable Markov kernel. -/
noncomputable def countableIterateTransitionKernel
    {α : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (kernel : CountableMarkovKernel α) : Kernel (α × ℕ) α :=
  Kernel.ofFunOfCountable fun stateAndSteps =>
    (CountableMarkovKernel.iterate kernel stateAndSteps.2 stateAndSteps.1).toMeasure

instance countableIterateTransitionKernel_isMarkov
    {α : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (kernel : CountableMarkovKernel α) :
    IsMarkovKernel (countableIterateTransitionKernel kernel) where
  isProbabilityMeasure stateAndSteps := by
    change IsProbabilityMeasure
      (CountableMarkovKernel.iterate kernel stateAndSteps.2 stateAndSteps.1).toMeasure
    infer_instance

/-- Given a number of potential events and an initial state, retain that count
alongside the state after exactly that many transitions. -/
noncomputable def countableIterateTransitionWithCountKernel
    {α : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (kernel : CountableMarkovKernel α) : Kernel (ℕ × α) (ℕ × α) :=
  (Kernel.deterministic Prod.fst measurable_fst) ×ₖ
    (countableIterateTransitionKernel kernel ∘ₖ
      Kernel.deterministic Prod.swap measurable_swap)

instance countableIterateTransitionWithCountKernel_isMarkov
    {α : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (kernel : CountableMarkovKernel α) :
    IsMarkovKernel (countableIterateTransitionWithCountKernel kernel) := by
  unfold countableIterateTransitionWithCountKernel
  infer_instance

/-- A retained-count transition has the deterministic count marginal and the
ordinary iterated transition as its state marginal. -/
theorem countableIterateTransitionWithCountKernel_apply
    {α : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (kernel : CountableMarkovKernel α) (steps : ℕ) (state : α) :
    countableIterateTransitionWithCountKernel kernel (steps, state) =
      (Measure.dirac steps).prod
        (CountableMarkovKernel.iterate kernel steps state).toMeasure := by
  rw [countableIterateTransitionWithCountKernel, Kernel.prod_apply,
    Kernel.deterministic_apply, Kernel.comp_deterministic_eq_comap,
    Kernel.comap_apply]
  rfl

/-- With an initial state fixed, retain a sampled event count together with
the state after that many transitions. -/
noncomputable def countableIterateTransitionFromStateKernel
    {α : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (kernel : CountableMarkovKernel α) (state : α) : Kernel ℕ (ℕ × α) :=
  countableIterateTransitionWithCountKernel kernel ∘ₖ
    Kernel.deterministic (fun steps : ℕ => (steps, state))
      (measurable_id.prodMk measurable_const)

/-- The fixed-state retained-count kernel evaluates to the ordinary
deterministic-count transition. -/
theorem countableIterateTransitionFromStateKernel_apply
    {α : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (kernel : CountableMarkovKernel α) (state : α) (steps : ℕ) :
    countableIterateTransitionFromStateKernel kernel state steps =
      countableIterateTransitionWithCountKernel kernel (steps, state) := by
  rw [countableIterateTransitionFromStateKernel,
    Kernel.comp_deterministic_eq_comap, Kernel.comap_apply]

/-- A fixed-state retained-count row is the image of the ordinary iterated
state-transition measure under pairing with its deterministic count. -/
theorem countableIterateTransitionFromStateKernel_apply_eq_map
    {α : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (kernel : CountableMarkovKernel α) (state : α) (steps : ℕ) :
    countableIterateTransitionFromStateKernel kernel state steps =
      Measure.map (Prod.mk steps)
        (CountableMarkovKernel.iterate kernel steps state).toMeasure := by
  rw [countableIterateTransitionFromStateKernel_apply,
    countableIterateTransitionWithCountKernel_apply, Measure.dirac_prod]

/-- A count-retaining iterated transition is almost surely supported on the
corresponding iterated state-transition support. -/
theorem ae_mem_iterate_support_countableIterateTransitionWithCountKernel
    {α : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (kernel : CountableMarkovKernel α) (steps : ℕ) (state : α) :
    ∀ᵐ output ∂countableIterateTransitionWithCountKernel kernel (steps, state),
      output.2 ∈ (CountableMarkovKernel.iterate kernel output.1 state).support := by
  rw [countableIterateTransitionWithCountKernel_apply]
  apply (Measure.ae_prod_iff_ae_ae (Set.to_countable _).measurableSet).2
  have hcount : ∀ᵐ count ∂Measure.dirac steps, count = steps := by
    exact (ae_dirac_iff (Set.to_countable _).measurableSet).2 rfl
  filter_upwards [hcount] with count hcount
  subst count
  have hsupp : ∀ᵐ next ∂(CountableMarkovKernel.iterate kernel steps state).toMeasure,
      next ∈ (CountableMarkovKernel.iterate kernel steps state).support := by
    change (CountableMarkovKernel.iterate kernel steps state).support ∈
      ae (CountableMarkovKernel.iterate kernel steps state).toMeasure
    rw [mem_ae_iff_prob_eq_one
      (CountableMarkovKernel.iterate kernel steps state).support_countable.measurableSet]
    exact (PMF.toMeasure_apply_eq_one_iff
      (CountableMarkovKernel.iterate kernel steps state)
      (CountableMarkovKernel.iterate kernel steps state).support_countable.measurableSet).2
        (fun _ membership => membership)
  exact hsupp

/-- Forgetting the retained count recovers the ordinary iterated state
transition. -/
theorem countableIterateTransitionWithCountKernel_snd
    {α : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (kernel : CountableMarkovKernel α) :
    (countableIterateTransitionWithCountKernel kernel).snd =
      countableIterateTransitionKernel kernel ∘ₖ
        Kernel.deterministic Prod.swap measurable_swap := by
  rw [countableIterateTransitionWithCountKernel, Kernel.snd_prod]

/-- Poissonize a countable transition kernel at a nonnegative exposure while
retaining the initial state. Its input is `(exposure, initialState)`. -/
noncomputable def poissonizedParameterTransitionKernel
    {α : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (kernel : CountableMarkovKernel α) : Kernel (ℝ≥0 × α) α :=
  countableIterateTransitionKernel kernel ∘ₖ
    ((Kernel.deterministic Prod.snd measurable_snd) ×ₖ
      (AppliedModelingLib.Probability.poissonParameterKernel.prodMkRight α))

instance poissonizedParameterTransitionKernel_isMarkov
    {α : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (kernel : CountableMarkovKernel α) :
    IsMarkovKernel (poissonizedParameterTransitionKernel kernel) := by
  unfold poissonizedParameterTransitionKernel
  infer_instance

/-- Poissonize a countable transition kernel while retaining the sampled
potential-event count together with the resulting state. -/
noncomputable def poissonizedParameterTransitionWithCountKernel
    {α : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (kernel : CountableMarkovKernel α) : Kernel (ℝ≥0 × α) (ℕ × α) :=
  countableIterateTransitionWithCountKernel kernel ∘ₖ
    ((AppliedModelingLib.Probability.poissonParameterKernel.prodMkRight α) ×ₖ
      Kernel.deterministic Prod.snd measurable_snd)

instance poissonizedParameterTransitionWithCountKernel_isMarkov
    {α : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (kernel : CountableMarkovKernel α) :
    IsMarkovKernel (poissonizedParameterTransitionWithCountKernel kernel) := by
  unfold poissonizedParameterTransitionWithCountKernel
  infer_instance

/-- A Poissonized count-retaining transition is almost surely supported on the
corresponding number of iterated transitions from its input state. -/
theorem ae_mem_iterate_support_poissonizedParameterTransitionWithCountKernel
    {α : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (kernel : CountableMarkovKernel α) (mean : ℝ≥0) (state : α) :
    ∀ᵐ output ∂poissonizedParameterTransitionWithCountKernel kernel (mean, state),
      output.2 ∈ (CountableMarkovKernel.iterate kernel output.1 state).support := by
  unfold poissonizedParameterTransitionWithCountKernel
  apply Kernel.ae_comp_of_ae_ae (Set.to_countable _).measurableSet
  let inputKernel : Kernel (ℝ≥0 × α) (ℕ × α) :=
    (AppliedModelingLib.Probability.poissonParameterKernel.prodMkRight α) ×ₖ
      Kernel.deterministic Prod.snd measurable_snd
  have hsndKernel : inputKernel.snd = Kernel.deterministic Prod.snd measurable_snd := by
    dsimp [inputKernel]
    simp
  have hsnd : (inputKernel (mean, state)).map Prod.snd = Measure.dirac state := by
    rw [← Kernel.snd_apply, hsndKernel, Kernel.deterministic_apply]
  have hmiddle : ∀ᵐ middle ∂inputKernel (mean, state), middle.2 = state := by
    refine ae_of_ae_map (μ := inputKernel (mean, state)) (f := Prod.snd)
      (p := fun value : α => value = state) measurable_snd.aemeasurable ?_
    rw [hsnd]
    exact (ae_dirac_iff (Set.to_countable _).measurableSet).2 rfl
  filter_upwards [hmiddle] with middle hmiddle
  have hsupp := ae_mem_iterate_support_countableIterateTransitionWithCountKernel
    kernel middle.1 middle.2
  filter_upwards [hsupp] with output hsupp
  simpa [hmiddle] using hsupp

/-- Forgetting the sampled Poisson count from the retained-count construction
recovers the ordinary parameterized Poisson transition. -/
theorem poissonizedParameterTransitionWithCountKernel_snd
    {α : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (kernel : CountableMarkovKernel α) :
    (poissonizedParameterTransitionWithCountKernel kernel).snd =
      poissonizedParameterTransitionKernel kernel := by
  rw [poissonizedParameterTransitionWithCountKernel, Kernel.snd_comp,
    countableIterateTransitionWithCountKernel_snd, Kernel.comp_assoc]
  change countableIterateTransitionKernel kernel ∘ₖ
      (Kernel.swap ℕ α ∘ₖ
        ((AppliedModelingLib.Probability.poissonParameterKernel.prodMkRight α) ×ₖ
          Kernel.deterministic Prod.snd measurable_snd)) = _
  rw [Kernel.swap_prod]
  rfl

/-- The retained count in a parameterized Poisson transition has precisely the
Poisson law at the input exposure, independently of the countable transition
kernel and its initial state. -/
theorem poissonizedParameterTransitionWithCountKernel_fst_apply
    {α : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (kernel : CountableMarkovKernel α) (mean : ℝ≥0) (state : α) :
    (poissonizedParameterTransitionWithCountKernel kernel).fst (mean, state) =
      ProbabilityTheory.poissonMeasure mean := by
  rw [poissonizedParameterTransitionWithCountKernel, Kernel.fst_comp,
    countableIterateTransitionWithCountKernel, Kernel.fst_prod]
  rw [Kernel.deterministic_comp_eq_map measurable_fst, ← Kernel.fst_eq,
    Kernel.fst_prod]
  rfl

/-- A count-retaining Poissonized row is exactly a mixture over its sampled
Poisson count, followed by the deterministic-count iterated transition.  The
state transition in the mixture is independent of the exposure once the
count has been retained. -/
theorem poissonizedParameterTransitionWithCountKernel_apply_eq_bind_iterate
    {α : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (kernel : CountableMarkovKernel α) (mean : ℝ≥0) (state : α) :
    poissonizedParameterTransitionWithCountKernel kernel (mean, state) =
      (ProbabilityTheory.poissonMeasure mean).bind
        (countableIterateTransitionWithCountKernel kernel ∘ₖ
          Kernel.deterministic (fun steps : ℕ => (steps, state))
            (measurable_id.prodMk measurable_const)) := by
  let fixedCountKernel : Kernel ℕ (ℕ × α) :=
    countableIterateTransitionWithCountKernel kernel ∘ₖ
      Kernel.deterministic (fun steps : ℕ => (steps, state))
        (measurable_id.prodMk measurable_const)
  have hfixed (steps : ℕ) :
      fixedCountKernel steps =
        countableIterateTransitionWithCountKernel kernel (steps, state) := by
    dsimp only [fixedCountKernel]
    rw [Kernel.comp_deterministic_eq_comap, Kernel.comap_apply]
  ext event hevent
  rw [poissonizedParameterTransitionWithCountKernel,
    Kernel.comp_apply' _ _ _ hevent]
  rw [Kernel.lintegral_prod_deterministic measurable_snd
    (AppliedModelingLib.Probability.poissonParameterKernel.prodMkRight α)
    (mean, state) ((countableIterateTransitionWithCountKernel kernel).measurable_coe hevent)]
  change (∫⁻ steps : ℕ,
      countableIterateTransitionWithCountKernel kernel (steps, state) event ∂
        ProbabilityTheory.poissonMeasure mean) =
    (ProbabilityTheory.poissonMeasure mean).bind fixedCountKernel event
  rw [Measure.bind_apply hevent (Kernel.aemeasurable fixedCountKernel)]
  apply lintegral_congr
  intro steps
  rw [hfixed]

/-- Restricting a Poissonized count-retaining kernel to a fixed initial state
factorizes it into the Poisson count kernel followed by the fixed-state
iterated transition kernel. -/
theorem poissonizedParameterTransitionWithCountKernel_comp_fixedState
    {α : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (kernel : CountableMarkovKernel α) (state : α) :
    poissonizedParameterTransitionWithCountKernel kernel ∘ₖ
      Kernel.deterministic (fun mean : ℝ≥0 => (mean, state))
        (measurable_id.prodMk measurable_const) =
      countableIterateTransitionFromStateKernel kernel state ∘ₖ
        AppliedModelingLib.Probability.poissonParameterKernel := by
  apply Kernel.ext
  intro mean
  rw [Kernel.comp_deterministic_eq_comap, Kernel.comap_apply, Kernel.comp_apply]
  simpa [countableIterateTransitionFromStateKernel,
    AppliedModelingLib.Probability.poissonParameterKernel] using
    (poissonizedParameterTransitionWithCountKernel_apply_eq_bind_iterate
      kernel mean state)

/-- After a measurable change of exposure parameter, the fixed-state
count-retaining Poissonization still factors through the Poisson count kernel
and the fixed-state iterated transition kernel. -/
theorem poissonizedParameterTransitionWithCountKernel_comp_fixedState_comp_deterministic
    {δ α : Type*} [MeasurableSpace δ] [MeasurableSpace α]
    [Countable α] [MeasurableSingletonClass α]
    (kernel : CountableMarkovKernel α) (state : α)
    (exposure : δ → ℝ≥0) (hexposure : Measurable exposure) :
    poissonizedParameterTransitionWithCountKernel kernel ∘ₖ
      Kernel.deterministic (fun input : δ => (exposure input, state))
        (hexposure.prodMk measurable_const) =
      countableIterateTransitionFromStateKernel kernel state ∘ₖ
        AppliedModelingLib.Probability.poissonParameterKernel ∘ₖ
          Kernel.deterministic exposure hexposure := by
  calc
    poissonizedParameterTransitionWithCountKernel kernel ∘ₖ
        Kernel.deterministic (fun input : δ => (exposure input, state))
          (hexposure.prodMk measurable_const) =
        poissonizedParameterTransitionWithCountKernel kernel ∘ₖ
          (Kernel.deterministic (fun mean : ℝ≥0 => (mean, state))
            (measurable_id.prodMk measurable_const) ∘ₖ
            Kernel.deterministic exposure hexposure) := by
              congr 1
              rw [Kernel.deterministic_comp_deterministic]
              rfl
    _ = (poissonizedParameterTransitionWithCountKernel kernel ∘ₖ
          Kernel.deterministic (fun mean : ℝ≥0 => (mean, state))
            (measurable_id.prodMk measurable_const)) ∘ₖ
          Kernel.deterministic exposure hexposure := by
            exact (Kernel.comp_assoc _ _ _).symm
    _ = countableIterateTransitionFromStateKernel kernel state ∘ₖ
          AppliedModelingLib.Probability.poissonParameterKernel ∘ₖ
          Kernel.deterministic exposure hexposure := by
            rw [poissonizedParameterTransitionWithCountKernel_comp_fixedState]

/-- At a fixed exposure and initial state, the measurable parameterized
Poissonization is exactly the ordinary Poissonized transition row. -/
theorem poissonizedParameterTransitionKernel_apply
    {α : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (kernel : CountableMarkovKernel α) (mean : ℝ≥0) (state : α) :
    poissonizedParameterTransitionKernel kernel (mean, state) =
      CountableMarkovKernel.poissonizedKernel kernel mean state := by
  ext event hevent
  rw [poissonizedParameterTransitionKernel, Kernel.comp_apply' _ _ _ hevent]
  rw [Kernel.lintegral_deterministic_prod measurable_snd
    (AppliedModelingLib.Probability.poissonParameterKernel.prodMkRight α)
    (mean, state) ((countableIterateTransitionKernel kernel).measurable_coe hevent)]
  change ∫⁻ steps : ℕ, (CountableMarkovKernel.iterate kernel steps state).toMeasure event ∂
      ProbabilityTheory.poissonMeasure mean =
    (CountableMarkovKernel.poissonized kernel mean state).toMeasure event
  rw [← Measure.toPMF_toMeasure (ProbabilityTheory.poissonMeasure mean)]
  rw [pmf_toMeasure_eq_count_withDensity]
  rw [lintegral_withDensity_eq_lintegral_mul _ (measurable_of_countable _)
    (measurable_of_countable _), lintegral_count]
  rw [CountableMarkovKernel.poissonized, PMF.toMeasure_bind_apply _ _ event hevent]
  rfl

end AppliedModelingLib.Probability.Queueing
