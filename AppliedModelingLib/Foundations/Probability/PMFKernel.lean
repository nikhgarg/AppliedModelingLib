import AppliedModelingLib.Foundations.Probability.FiniteExpectation
import Mathlib.Probability.Kernel.Composition.MeasureComp

/-!
# PMF-valued transition kernels

This module lifts a countable PMF-valued transition rule to Mathlib's measure
kernel interface.  The bridge keeps finite-PMF rollout recursions and
Ionescu--Tulcea trajectory arguments on the same transition law.
-/

namespace AppliedModelingLib

open MeasureTheory ProbabilityTheory

/-- A discrete stochastic kernel represented directly as a PMF-valued map.
Domain-specific policies and transition rules may use transparent aliases of
this carrier while retaining their own semantic names. -/
abbrev PMFKernel (Input Output : Type*) := Input → PMF Output

namespace PMFKernel

/-- PMF-valued kernels are equal when their output laws agree pointwise. -/
theorem ext {Input Output : Type*} {first second : PMFKernel Input Output}
    (h : ∀ input, first input = second input) : first = second :=
  funext h

/-- Embed a deterministic map as a PMF-valued kernel. -/
noncomputable def pure {Input Output : Type*}
    (output : Input → Output) : PMFKernel Input Output :=
  fun input => PMF.pure (output input)

@[simp] theorem pure_apply {Input Output : Type*}
    (output : Input → Output) (input : Input) :
    pure output input = PMF.pure (output input) := rfl

/-- Compose two PMF-valued kernels by PMF bind. -/
noncomputable def comp {Input Middle Output : Type*}
    (first : PMFKernel Input Middle) (second : PMFKernel Middle Output) :
    PMFKernel Input Output :=
  fun input => (first input).bind second

@[simp] theorem comp_apply {Input Middle Output : Type*}
    (first : PMFKernel Input Middle) (second : PMFKernel Middle Output)
    (input : Input) :
    comp first second input = (first input).bind second := rfl

/-- Composition of PMF-valued kernels is associative. -/
theorem comp_assoc {Input Middle Penultimate Output : Type*}
    (first : PMFKernel Input Middle) (second : PMFKernel Middle Penultimate)
    (third : PMFKernel Penultimate Output) :
    comp (comp first second) third = comp first (comp second third) := by
  apply ext
  intro input
  exact PMF.bind_bind (first input) second third

/-- A kernel assigns positive support to an output when its point mass is
nonzero. -/
def Supports {Input Output : Type*}
    (kernel : PMFKernel Input Output) (input : Input) (output : Output) : Prop :=
  kernel input output ≠ 0

/-- The expectation of a score under one output law of a finite PMF kernel. -/
noncomputable def expectedValue {Input Output : Type*}
    [Fintype Output] [DecidableEq Output]
    (kernel : PMFKernel Input Output) (score : Input → Output → ℝ)
    (input : Input) : ℝ :=
  pmfExp (kernel input) (score input)

/-- Expected values through a composed finite kernel satisfy the tower rule. -/
theorem expectedValue_comp {Input Middle Output : Type*}
    [Fintype Middle] [DecidableEq Middle]
    [Fintype Output] [DecidableEq Output]
    (first : PMFKernel Input Middle) (second : PMFKernel Middle Output)
    (score : Output → ℝ) (input : Input) :
    expectedValue (comp first second) (fun _ output => score output) input =
      expectedValue first (fun _ middle =>
        expectedValue second (fun _ output => score output) middle) input := by
  unfold expectedValue comp
  exact pmfExp_bind (first input) second score

end PMFKernel

/-- Regard a countable PMF-valued transition rule as a measure kernel. -/
noncomputable def pmfToMeasureKernel
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Countable α] [Countable β] [MeasurableSingletonClass α]
    [MeasurableSingletonClass β] (transition : PMFKernel α β) : Kernel α β :=
  Kernel.ofFunOfCountable fun input => (transition input).toMeasure

instance pmfToMeasureKernel.isMarkovKernel
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Countable α] [Countable β] [MeasurableSingletonClass α]
    [MeasurableSingletonClass β] (transition : PMFKernel α β) :
    IsMarkovKernel (pmfToMeasureKernel transition) where
  isProbabilityMeasure input := by
    change IsProbabilityMeasure ((transition input).toMeasure)
    infer_instance

/-- The measure of a PMF is count measure weighted by its point masses. -/
private theorem pmf_toMeasure_eq_count_withDensity
    {α : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (law : PMF α) :
    law.toMeasure = Measure.count.withDensity law := by
  ext event hevent
  rw [PMF.toMeasure_apply_eq_tsum, withDensity_apply _ hevent,
    ← lintegral_indicator hevent, lintegral_count]

/-- Composing a PMF measure with its PMF-valued kernel is its PMF bind. -/
theorem pmfToMeasure_bind_pmfToMeasureKernel_eq_pmf_bind_toMeasure
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Countable α] [Countable β] [MeasurableSingletonClass α]
    [MeasurableSingletonClass β] (law : PMF α) (transition : PMFKernel α β) :
    pmfToMeasureKernel transition ∘ₘ law.toMeasure = (law.bind transition).toMeasure := by
  ext event hevent
  rw [Measure.bind_apply hevent (Kernel.aemeasurable _), pmfToMeasureKernel,
    pmf_toMeasure_eq_count_withDensity law,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_of_countable _)
      (measurable_of_countable _), lintegral_count]
  rw [PMF.toMeasure_bind_apply law transition event hevent]
  rfl

/-- A finite-output PMF-valued rule is a genuine measure kernel over an
arbitrary measurable input space when each output mass is measurable in the
input.  This is the appropriate bridge for an algorithm whose finite random
trace distribution is selected from a continuously distributed data set. -/
noncomputable def pmfToMeasureKernelOfFinite
    {Input Output : Type*} [MeasurableSpace Input] [MeasurableSpace Output]
    [Fintype Output] [MeasurableSingletonClass Output]
    (transition : PMFKernel Input Output)
    (hmeasurable : ∀ output, Measurable (fun input => transition input output)) :
    Kernel Input Output where
  toFun input := (transition input).toMeasure
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun event hevent => ?_
    simp_rw [PMF.toMeasure_apply_fintype]
    apply Finset.measurable_fun_sum
    intro output _
    by_cases houtput : output ∈ event
    · simpa only [Set.indicator_of_mem houtput] using hmeasurable output
    · simpa only [Set.indicator_of_notMem houtput] using measurable_const

/-- The finite-output kernel has exactly the intended conditional PMF law. -/
theorem pmfToMeasureKernelOfFinite_apply
    {Input Output : Type*} [MeasurableSpace Input] [MeasurableSpace Output]
    [Fintype Output] [MeasurableSingletonClass Output]
    (transition : PMFKernel Input Output)
    (hmeasurable : ∀ output, Measurable (fun input => transition input output))
    (input : Input) :
    pmfToMeasureKernelOfFinite transition hmeasurable input = (transition input).toMeasure := rfl

/-- The finite-output PMF kernel is Markov because every PMF induces a
probability measure. -/
theorem isMarkovKernel_pmfToMeasureKernelOfFinite
    {Input Output : Type*} [MeasurableSpace Input] [MeasurableSpace Output]
    [Fintype Output] [MeasurableSingletonClass Output]
    (transition : PMFKernel Input Output)
    (hmeasurable : ∀ output, Measurable (fun input => transition input output)) :
    IsMarkovKernel (pmfToMeasureKernelOfFinite transition hmeasurable) where
  isProbabilityMeasure input := by
    change IsProbabilityMeasure ((transition input).toMeasure)
    infer_instance

/-- A finite-PMF conditional tail is the corresponding real-probability tail
under its measurable measure-kernel realization. -/
theorem measureReal_pmfToMeasureKernelOfFinite_apply_le_of_pmfProb_le
    {Input Output : Type*} [MeasurableSpace Input] [MeasurableSpace Output]
    [Fintype Output] [DecidableEq Output] [DiscreteMeasurableSpace Output]
    (transition : PMFKernel Input Output)
    (hmeasurable : ∀ output, Measurable (fun input => transition input output))
    (event : Input → Output → Prop) [∀ input, DecidablePred (event input)]
    (bound : ℝ) (hbound : ∀ input, pmfProb (transition input) (event input) ≤ bound) :
    ∀ input, (pmfToMeasureKernelOfFinite transition hmeasurable input).real
      {output | event input output} ≤ bound := by
  intro input
  rw [pmfToMeasureKernelOfFinite_apply, ← pmfProb_eq_toMeasure_real]
  exact hbound input

end AppliedModelingLib
