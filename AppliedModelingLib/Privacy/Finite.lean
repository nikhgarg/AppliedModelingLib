import AppliedModelingLib.Foundations.Probability.IndependentProduct
import AppliedModelingLib.Foundations.Probability.Kernel
import AppliedModelingLib.Foundations.Probability.FiniteTransport
import AppliedModelingLib.Foundations.Math.FiniteDimensionalNorms
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.Layercake

open scoped BigOperators
open MeasureTheory Set

namespace AppliedModelingLib.Privacy

/-!
# Finite max-KL stability and post-processing

This file gives finite, executable probability semantics for the privacy and
algorithmic-stability arguments used by Hardt--Rothblum (2010),
Bassily--Nissim--Smith--Steinke--Ullman (2016), and
Hébert-Johnson--Kim--Reingold--Rothblum (2018).

Events are finite sets.  This is extensionally complete on a finite output
space and avoids hiding measurability assumptions in paper-facing theorems.
The randomized post-processing theorem below is genuinely a theorem about an
arbitrary finite Markov kernel.  Its proof realizes all kernel randomness on
one data-independent finite tape and then applies the event inequality
pointwise in that tape.  Consequently the additive `delta` is paid once, not
once per output atom.
-/

section Events

variable {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]

/-- Probability of a finite event under a finite probability mass function. -/
noncomputable def eventProbability (law : PMF Outcome) (event : Finset Outcome) : ℝ :=
  AppliedModelingLib.pmfProb law (fun outcome => outcome ∈ event)

/-- Pull an event back through a deterministic map. -/
def preimageEvent {Input Output : Type*} [Fintype Input] [DecidableEq Input]
    [DecidableEq Output] (f : Input → Output) (event : Finset Output) : Finset Input :=
  Finset.univ.filter (fun input => f input ∈ event)

@[simp]
theorem mem_preimageEvent {Input Output : Type*} [Fintype Input] [DecidableEq Input]
    [DecidableEq Output] (f : Input → Output) (event : Finset Output) (input : Input) :
    input ∈ preimageEvent f event ↔ f input ∈ event := by
  simp [preimageEvent]

/-- A pushforward hits an event exactly when its input hits the preimage event. -/
theorem eventProbability_map {Input Output : Type*}
    [Fintype Input] [DecidableEq Input] [Fintype Output] [DecidableEq Output]
    (law : PMF Input) (f : Input → Output) (event : Finset Output) :
    eventProbability (law.map f) event =
      eventProbability law (preimageEvent f event) := by
  classical
  unfold eventProbability
  rw [AppliedModelingLib.pmfProb_map]
  apply AppliedModelingLib.pmfProb_congr
  intro input
  simp [preimageEvent]

end Events

section Closeness

variable {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]

/--
One directed `(epsilon, delta)` max-KL event inequality.

This is the directed inequality appearing literally in the definitions of
differential privacy and max-KL stability.  Symmetry belongs either in the
adjacency relation or in `MaxKLClose`, rather than being silently baked into
this primitive.
-/
def ApproxDomination (epsilon delta : ℝ) (first second : PMF Outcome) : Prop :=
  ∀ event : Finset Outcome,
    eventProbability first event ≤
      Real.exp epsilon * eventProbability second event + delta

/-- Two distributions satisfy the max-KL event inequalities in both directions. -/
def MaxKLClose (epsilon delta : ℝ) (first second : PMF Outcome) : Prop :=
  ApproxDomination epsilon delta first second ∧
    ApproxDomination epsilon delta second first

/--
An approximate domination inequality follows when pointwise domination holds
outside a bad event whose probability under the first law is at most `delta`.
This is the finite privacy-loss-tail principle: the exceptional probability is
paid once for the whole event, not once per exceptional atom.
-/
theorem ApproxDomination.of_pointwise_outside_bad
    {epsilon delta : ℝ} (first second : PMF Outcome) (bad : Finset Outcome)
    (hbad : eventProbability first bad ≤ delta)
    (hpoint : ∀ outcome, outcome ∉ bad →
      (first outcome).toReal ≤ Real.exp epsilon * (second outcome).toReal) :
    ApproxDomination epsilon delta first second := by
  classical
  intro event
  unfold eventProbability at hbad ⊢
  rw [AppliedModelingLib.pmfProb_eq_inter_add_inter_not first
    (fun outcome => outcome ∈ event) (fun outcome => outcome ∈ bad)]
  have hbadPart :
      AppliedModelingLib.pmfProb first (fun outcome => outcome ∈ event ∧ outcome ∈ bad) ≤
        AppliedModelingLib.pmfProb first (fun outcome => outcome ∈ bad) := by
    exact AppliedModelingLib.pmfProb_le_of_imp first _ _ (fun _ h => h.2)
  have hgoodPart :
      AppliedModelingLib.pmfProb first (fun outcome => outcome ∈ event ∧ outcome ∉ bad) ≤
        Real.exp epsilon *
          AppliedModelingLib.pmfProb second (fun outcome => outcome ∈ event) := by
    unfold AppliedModelingLib.pmfProb AppliedModelingLib.pmfExp
    calc
      (∑ outcome : Outcome,
          (first outcome).toReal *
            (if outcome ∈ event ∧ outcome ∉ bad then (1 : ℝ) else 0)) ≤
          ∑ outcome : Outcome,
            Real.exp epsilon * (second outcome).toReal *
              (if outcome ∈ event then (1 : ℝ) else 0) := by
        apply Finset.sum_le_sum
        intro outcome _
        by_cases hevent : outcome ∈ event
        · by_cases houtside : outcome ∉ bad
          · simp [hevent, houtside, hpoint outcome houtside]
          · simp [hevent, houtside, mul_nonneg (Real.exp_pos _).le ENNReal.toReal_nonneg]
        · simp [hevent]
      _ = Real.exp epsilon *
          ∑ outcome : Outcome,
            (second outcome).toReal *
              (if outcome ∈ event then (1 : ℝ) else 0) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro outcome _
        ring
  nlinarith

/-- Directed approximate domination is transitive, with the standard scaled
second exceptional probability. -/
theorem ApproxDomination.trans
    {epsilon₁ delta₁ epsilon₂ delta₂ : ℝ}
    {first middle last : PMF Outcome}
    (hfirst : ApproxDomination epsilon₁ delta₁ first middle)
    (hsecond : ApproxDomination epsilon₂ delta₂ middle last) :
    ApproxDomination (epsilon₁ + epsilon₂)
      (delta₁ + Real.exp epsilon₁ * delta₂) first last := by
  intro event
  have h₁ := hfirst event
  have h₂ := hsecond event
  have hexp : 0 ≤ Real.exp epsilon₁ := (Real.exp_pos _).le
  calc
    eventProbability first event ≤
        Real.exp epsilon₁ * eventProbability middle event + delta₁ := h₁
    _ ≤ Real.exp epsilon₁ *
          (Real.exp epsilon₂ * eventProbability last event + delta₂) + delta₁ := by
      simpa [add_comm] using
        (add_le_add_right (mul_le_mul_of_nonneg_left h₂ hexp) delta₁)
    _ = Real.exp (epsilon₁ + epsilon₂) * eventProbability last event +
          (delta₁ + Real.exp epsilon₁ * delta₂) := by
      rw [Real.exp_add]
      ring

/-- Every finite law is max-KL close to itself for nonnegative parameters. -/
theorem ApproxDomination.refl (law : PMF Outcome) {epsilon delta : ℝ}
    (hepsilon : 0 ≤ epsilon) (hdelta : 0 ≤ delta) :
    ApproxDomination epsilon delta law law := by
  intro event
  have hprob := AppliedModelingLib.pmfProb_nonneg law (fun outcome ↦ outcome ∈ event)
  have hexp : 1 ≤ Real.exp epsilon := Real.one_le_exp hepsilon
  calc
    eventProbability law event = 1 * eventProbability law event + 0 := by ring
    _ ≤ Real.exp epsilon * eventProbability law event + delta := by
      exact add_le_add (mul_le_mul_of_nonneg_right hexp hprob) hdelta

/-- Reflexive two-sided max-KL closeness. -/
theorem MaxKLClose.refl (law : PMF Outcome) {epsilon delta : ℝ}
    (hepsilon : 0 ≤ epsilon) (hdelta : 0 ≤ delta) :
    MaxKLClose epsilon delta law law :=
  ⟨ApproxDomination.refl law hepsilon hdelta,
    ApproxDomination.refl law hepsilon hdelta⟩

theorem MaxKLClose.symm {epsilon delta : ℝ} {first second : PMF Outcome}
    (h : MaxKLClose epsilon delta first second) :
    MaxKLClose epsilon delta second first :=
  ⟨h.2, h.1⟩

/-- Deterministic post-processing preserves a directed max-KL inequality. -/
theorem ApproxDomination.map {Output : Type*}
    [Fintype Output] [DecidableEq Output]
    {epsilon delta : ℝ} {first second : PMF Outcome}
    (h : ApproxDomination epsilon delta first second) (f : Outcome → Output) :
    ApproxDomination epsilon delta (first.map f) (second.map f) := by
  intro event
  rw [eventProbability_map, eventProbability_map]
  exact h (preimageEvent f event)

/-- Deterministic post-processing preserves two-sided max-KL closeness. -/
theorem MaxKLClose.map {Output : Type*}
    [Fintype Output] [DecidableEq Output]
    {epsilon delta : ℝ} {first second : PMF Outcome}
    (h : MaxKLClose epsilon delta first second) (f : Outcome → Output) :
    MaxKLClose epsilon delta (first.map f) (second.map f) :=
  ⟨h.1.map f, h.2.map f⟩

/--
Directed max-KL domination transfers from events to bounded nonnegative
expectations.  This is the finite layer-cake step used throughout BNS16: the
additive event error is integrated over an interval of length `bound`, so it
becomes `delta * bound` rather than an output-cardinality loss.
-/
theorem ApproxDomination.expectation_le
    {epsilon delta : ℝ} {first second : PMF Outcome}
    (h : ApproxDomination epsilon delta first second)
    (value : Outcome → ℝ) (bound : ℝ)
    (hvalueNonneg : ∀ outcome, 0 ≤ value outcome)
    (hvalueBound : ∀ outcome, value outcome ≤ bound) :
    AppliedModelingLib.pmfExp first value ≤
      Real.exp epsilon * AppliedModelingLib.pmfExp second value + delta * bound := by
  classical
  letI : MeasurableSpace Outcome := ⊤
  let firstMeasure : Measure Outcome := first.toMeasure
  let secondMeasure : Measure Outcome := second.toMeasure
  have hboundNonneg : 0 ≤ bound := by
    obtain ⟨outcome, _houtcome⟩ := first.support_nonempty
    exact (hvalueNonneg outcome).trans (hvalueBound outcome)
  have hfirstIntegrable : Integrable value firstMeasure := by
    apply Integrable.of_bound (measurable_of_finite value).aestronglyMeasurable bound
    filter_upwards [] with outcome
    rw [Real.norm_eq_abs, abs_of_nonneg (hvalueNonneg outcome)]
    exact hvalueBound outcome
  have hsecondIntegrable : Integrable value secondMeasure := by
    apply Integrable.of_bound (measurable_of_finite value).aestronglyMeasurable bound
    filter_upwards [] with outcome
    rw [Real.norm_eq_abs, abs_of_nonneg (hvalueNonneg outcome)]
    exact hvalueBound outcome
  let firstTail : ℝ → ℝ := fun threshold =>
    firstMeasure.real {outcome | threshold ≤ value outcome}
  let secondTail : ℝ → ℝ := fun threshold =>
    secondMeasure.real {outcome | threshold ≤ value outcome}
  have hfirstTailAntitone : Antitone firstTail := by
    intro lower upper hlowerUpper
    unfold firstTail Measure.real
    apply ENNReal.toReal_mono
    · exact measure_ne_top _ _
    · apply measure_mono
      intro outcome houtcome
      exact hlowerUpper.trans houtcome
  have hsecondTailAntitone : Antitone secondTail := by
    intro lower upper hlowerUpper
    unfold secondTail Measure.real
    apply ENNReal.toReal_mono
    · exact measure_ne_top _ _
    · apply measure_mono
      intro outcome houtcome
      exact hlowerUpper.trans houtcome
  have hfirstTailIntegrable : IntegrableOn firstTail (Ioc 0 bound) := by
    apply Integrable.of_bound
      hfirstTailAntitone.measurable.aestronglyMeasurable.restrict 1
    filter_upwards [] with threshold
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact measureReal_le_one
    · exact measureReal_nonneg
  have hsecondTailIntegrable : IntegrableOn secondTail (Ioc 0 bound) := by
    apply Integrable.of_bound
      hsecondTailAntitone.measurable.aestronglyMeasurable.restrict 1
    filter_upwards [] with threshold
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact measureReal_le_one
    · exact measureReal_nonneg
  have htail : ∀ threshold, firstTail threshold ≤
      Real.exp epsilon * secondTail threshold + delta := by
    intro threshold
    let event := Finset.univ.filter (fun outcome => threshold ≤ value outcome)
    have hprob := h event
    have hfirst : eventProbability first event = firstTail threshold := by
      unfold eventProbability firstTail firstMeasure
      rw [AppliedModelingLib.pmfProb_eq_toMeasure_real]
      congr 1
      ext outcome
      simp [event]
    have hsecond : eventProbability second event = secondTail threshold := by
      unfold eventProbability secondTail secondMeasure
      rw [AppliedModelingLib.pmfProb_eq_toMeasure_real]
      congr 1
      ext outcome
      simp [event]
    rwa [hfirst, hsecond] at hprob
  rw [AppliedModelingLib.pmfExp_eq_integral_toMeasure,
    AppliedModelingLib.pmfExp_eq_integral_toMeasure]
  change (∫ outcome, value outcome ∂firstMeasure) ≤
    Real.exp epsilon * (∫ outcome, value outcome ∂secondMeasure) + delta * bound
  rw [hfirstIntegrable.integral_eq_integral_Ioc_meas_le
      (Filter.Eventually.of_forall hvalueNonneg)
      (Filter.Eventually.of_forall hvalueBound)]
  rw [hsecondIntegrable.integral_eq_integral_Ioc_meas_le
      (Filter.Eventually.of_forall hvalueNonneg)
      (Filter.Eventually.of_forall hvalueBound)]
  change (∫ threshold in Ioc 0 bound, firstTail threshold) ≤
    Real.exp epsilon * (∫ threshold in Ioc 0 bound, secondTail threshold) + delta * bound
  have hconst : IntegrableOn (fun _ : ℝ => delta) (Ioc 0 bound) :=
    integrableOn_const (hs := by exact measure_Ioc_lt_top.ne)
  calc
    (∫ threshold in Ioc 0 bound, firstTail threshold) ≤
        ∫ threshold in Ioc 0 bound,
          (Real.exp epsilon * secondTail threshold + delta) := by
      apply integral_mono_ae hfirstTailIntegrable
      · exact (hsecondTailIntegrable.const_mul _).add hconst
      · filter_upwards [] with threshold
        exact htail threshold
    _ = Real.exp epsilon * (∫ threshold in Ioc 0 bound, secondTail threshold) +
          delta * bound := by
      rw [integral_add (hsecondTailIntegrable.const_mul _) hconst]
      rw [integral_const_mul]
      simp [hboundNonneg]
      ring

/--
Two-sided max-KL closeness bounds the difference of expectations of any
`[0, bound]`-valued statistic.  This is the exact finite form of the BNS16
tail-integration estimate.
-/
theorem MaxKLClose.abs_expectation_sub_expectation_le
    {epsilon delta : ℝ} {first second : PMF Outcome}
    (h : MaxKLClose epsilon delta first second)
    (hepsilon : 0 ≤ epsilon)
    (value : Outcome → ℝ) (bound : ℝ)
    (hvalueNonneg : ∀ outcome, 0 ≤ value outcome)
    (hvalueBound : ∀ outcome, value outcome ≤ bound) :
    |AppliedModelingLib.pmfExp first value - AppliedModelingLib.pmfExp second value| ≤
      (Real.exp epsilon - 1 + delta) * bound := by
  have hboundNonneg : 0 ≤ bound := by
    obtain ⟨outcome, _houtcome⟩ := first.support_nonempty
    exact (hvalueNonneg outcome).trans (hvalueBound outcome)
  have hfirstBound := AppliedModelingLib.pmfExp_le_of_forall_le first value bound hvalueBound
  have hsecondBound := AppliedModelingLib.pmfExp_le_of_forall_le second value bound hvalueBound
  have hforward := h.1.expectation_le value bound hvalueNonneg hvalueBound
  have hbackward := h.2.expectation_le value bound hvalueNonneg hvalueBound
  have hcoefficient : 0 ≤ Real.exp epsilon - 1 :=
    sub_nonneg.mpr (Real.one_le_exp hepsilon)
  have hforwardScale :
      (Real.exp epsilon - 1) * AppliedModelingLib.pmfExp second value ≤
        (Real.exp epsilon - 1) * bound :=
    mul_le_mul_of_nonneg_left hsecondBound hcoefficient
  have hbackwardScale :
      (Real.exp epsilon - 1) * AppliedModelingLib.pmfExp first value ≤
        (Real.exp epsilon - 1) * bound :=
    mul_le_mul_of_nonneg_left hfirstBound hcoefficient
  rw [abs_le]
  constructor <;> nlinarith

end Closeness

section CommonPriorKernels

variable {Input Outcome : Type*}
  [Fintype Input] [DecidableEq Input]
  [Fintype Outcome] [DecidableEq Outcome]

/--
Pointwise directed max-KL domination of two kernels survives averaging over a
common prior, even when the joint output retains the sampled input.  The
additive error is paid once because the prior masses sum to one.
-/
theorem ApproxDomination.kernelJoint
    {epsilon delta : ℝ} (prior : PMF Input)
    (first second : Input → PMF Outcome)
    (h : ∀ input, ApproxDomination epsilon delta (first input) (second input)) :
    ApproxDomination epsilon delta
      (AppliedModelingLib.pmfKernelJoint prior first)
      (AppliedModelingLib.pmfKernelJoint prior second) := by
  classical
  intro event
  unfold eventProbability AppliedModelingLib.pmfKernelJoint
  rw [AppliedModelingLib.pmfProb_bind, AppliedModelingLib.pmfProb_bind]
  have hpoint : ∀ input,
      AppliedModelingLib.pmfProb ((first input).map (fun outcome => (input, outcome)))
          (fun pair => pair ∈ event) ≤
        Real.exp epsilon *
          AppliedModelingLib.pmfProb ((second input).map (fun outcome => (input, outcome)))
            (fun pair => pair ∈ event) + delta := by
    intro input
    have hslice := h input
      (preimageEvent (fun outcome => (input, outcome)) event)
    simpa [eventProbability, AppliedModelingLib.pmfProb_map, preimageEvent] using hslice
  calc
    AppliedModelingLib.pmfExp prior
        (fun input =>
          AppliedModelingLib.pmfProb ((first input).map (fun outcome => (input, outcome)))
            (fun pair => pair ∈ event)) ≤
        AppliedModelingLib.pmfExp prior
          (fun input =>
            Real.exp epsilon *
              AppliedModelingLib.pmfProb ((second input).map (fun outcome => (input, outcome)))
                (fun pair => pair ∈ event) + delta) := by
      unfold AppliedModelingLib.pmfExp
      apply Finset.sum_le_sum
      intro input _
      exact mul_le_mul_of_nonneg_left (hpoint input) ENNReal.toReal_nonneg
    _ = Real.exp epsilon *
          AppliedModelingLib.pmfExp prior
            (fun input =>
              AppliedModelingLib.pmfProb ((second input).map (fun outcome => (input, outcome)))
                (fun pair => pair ∈ event)) + delta := by
      rw [AppliedModelingLib.pmfExp_add, AppliedModelingLib.pmfExp_const_mul,
        AppliedModelingLib.pmfExp_const]

/-- Pointwise two-sided closeness of common-prior kernels gives close joints. -/
theorem MaxKLClose.kernelJoint
    {epsilon delta : ℝ} (prior : PMF Input)
    (first second : Input → PMF Outcome)
    (h : ∀ input, MaxKLClose epsilon delta (first input) (second input)) :
    MaxKLClose epsilon delta
      (AppliedModelingLib.pmfKernelJoint prior first)
      (AppliedModelingLib.pmfKernelJoint prior second) :=
  ⟨ApproxDomination.kernelJoint prior first second (fun input => (h input).1),
    ApproxDomination.kernelJoint prior second first (fun input => (h input).2)⟩

end CommonPriorKernels

section RandomizedPostprocessing

variable {Input Seed Output : Type*}
  [Fintype Input] [DecidableEq Input]
  [Fintype Seed] [DecidableEq Seed]
  [Fintype Output] [DecidableEq Output]

/--
Apply a deterministic function using a random seed independent of the input
law.  Drawing the seed first is only a semantic choice; independence makes it
equivalent to drawing the input first.
-/
noncomputable def seededPostprocess
    (law : PMF Input) (seedLaw : PMF Seed) (f : Input → Seed → Output) : PMF Output :=
  seedLaw.bind (fun seed => law.map (fun input => f input seed))

/-- Event probability of a seeded post-processing is the seed-average preimage mass. -/
theorem eventProbability_seededPostprocess
    (law : PMF Input) (seedLaw : PMF Seed) (f : Input → Seed → Output)
    (event : Finset Output) :
    eventProbability (seededPostprocess law seedLaw f) event =
      AppliedModelingLib.pmfExp seedLaw
        (fun seed => eventProbability law (preimageEvent (fun input => f input seed) event)) := by
  classical
  unfold eventProbability seededPostprocess
  rw [AppliedModelingLib.pmfProb_bind]
  apply AppliedModelingLib.pmfExp_congr
  intro seed
  rw [AppliedModelingLib.pmfProb_map]
  apply AppliedModelingLib.pmfProb_congr
  intro input
  simp [preimageEvent]

/-- A common independent random tape preserves a directed max-KL inequality. -/
theorem ApproxDomination.seededPostprocess
    {epsilon delta : ℝ} {first second : PMF Input}
    (h : ApproxDomination epsilon delta first second)
    (seedLaw : PMF Seed) (f : Input → Seed → Output) :
    ApproxDomination epsilon delta
      (seededPostprocess first seedLaw f)
      (seededPostprocess second seedLaw f) := by
  intro event
  rw [eventProbability_seededPostprocess, eventProbability_seededPostprocess]
  calc
    AppliedModelingLib.pmfExp seedLaw
        (fun seed => eventProbability first (preimageEvent (fun input => f input seed) event))
        ≤ AppliedModelingLib.pmfExp seedLaw
            (fun seed => Real.exp epsilon *
                eventProbability second (preimageEvent (fun input => f input seed) event) + delta) := by
          apply AppliedModelingLib.pmfExp_le_pmfExp_of_forall_le
          intro seed
          exact h (preimageEvent (fun input => f input seed) event)
    _ = Real.exp epsilon *
          AppliedModelingLib.pmfExp seedLaw
            (fun seed => eventProbability second
              (preimageEvent (fun input => f input seed) event)) + delta := by
          rw [AppliedModelingLib.pmfExp_add, AppliedModelingLib.pmfExp_const_mul,
            AppliedModelingLib.pmfExp_const]

/-- A common independent random tape preserves two-sided max-KL closeness. -/
theorem MaxKLClose.seededPostprocess
    {epsilon delta : ℝ} {first second : PMF Input}
    (h : MaxKLClose epsilon delta first second)
    (seedLaw : PMF Seed) (f : Input → Seed → Output) :
    MaxKLClose epsilon delta
      (seededPostprocess first seedLaw f)
      (seededPostprocess second seedLaw f) :=
  ⟨h.1.seededPostprocess seedLaw f, h.2.seededPostprocess seedLaw f⟩

end RandomizedPostprocessing

section KernelPostprocessing

variable {Input Output : Type*}
  [Fintype Input] [DecidableEq Input]
  [Fintype Output] [DecidableEq Output]

/-- A single finite random tape carrying one draw from every kernel row. -/
noncomputable def kernelTape (kernel : Input → PMF Output) : PMF (Input → Output) :=
  AppliedModelingLib.pmfPi kernel

/--
The common-tape realization of an arbitrary finite Markov kernel.  The output
coordinate selected by `input` has law `kernel input`.
-/
noncomputable def tapedKernelPostprocess
    (law : PMF Input) (kernel : Input → PMF Output) : PMF Output :=
  seededPostprocess law (kernelTape kernel) (fun input tape => tape input)

/-- The common-tape realization has the same event probabilities as PMF bind. -/
theorem eventProbability_tapedKernelPostprocess
    (law : PMF Input) (kernel : Input → PMF Output) (event : Finset Output) :
    eventProbability (tapedKernelPostprocess law kernel) event =
      eventProbability (law.bind kernel) event := by
  classical
  calc
    eventProbability (tapedKernelPostprocess law kernel) event =
        AppliedModelingLib.pmfExp (kernelTape kernel)
          (fun tape => eventProbability law
            (preimageEvent (fun input => tape input) event)) := by
          exact eventProbability_seededPostprocess law (kernelTape kernel)
            (fun input tape => tape input) event
    _ = AppliedModelingLib.pmfPairExp (kernelTape kernel) law
          (fun tape input => if tape input ∈ event then (1 : ℝ) else 0) := by
          unfold AppliedModelingLib.pmfPairExp
          apply AppliedModelingLib.pmfExp_congr
          intro tape
          unfold eventProbability
          apply AppliedModelingLib.pmfExp_congr
          intro input
          simp [preimageEvent]
    _ = AppliedModelingLib.pmfPairExp law (kernelTape kernel)
          (fun input tape => if tape input ∈ event then (1 : ℝ) else 0) := by
          exact AppliedModelingLib.pmfPairExp_swap (kernelTape kernel) law
            (fun tape input => if tape input ∈ event then (1 : ℝ) else 0)
    _ = AppliedModelingLib.pmfExp law (fun input => eventProbability (kernel input) event) := by
          unfold AppliedModelingLib.pmfPairExp
          apply AppliedModelingLib.pmfExp_congr
          intro input
          unfold eventProbability AppliedModelingLib.pmfProb kernelTape
          exact AppliedModelingLib.pmfExp_pmfPi_eval_eq kernel input
            (fun output => if output ∈ event then (1 : ℝ) else 0)
    _ = eventProbability (law.bind kernel) event := by
          unfold eventProbability
          rw [AppliedModelingLib.pmfProb_bind]

/--
Randomized post-processing by an arbitrary finite kernel preserves a directed
max-KL event inequality (BNS16, Lemma 2.1).
-/
theorem ApproxDomination.bind
    {epsilon delta : ℝ} {first second : PMF Input}
    (h : ApproxDomination epsilon delta first second)
    (kernel : Input → PMF Output) :
    ApproxDomination epsilon delta (first.bind kernel) (second.bind kernel) := by
  intro event
  rw [← eventProbability_tapedKernelPostprocess first kernel event,
    ← eventProbability_tapedKernelPostprocess second kernel event]
  exact h.seededPostprocess (kernelTape kernel) (fun input tape => tape input) event

/-- Composition with a data-dependent finite post-processing kernel.  The
input law has one directed max-KL budget, while each matched kernel row has a
second directed budget.  The additive error of the second stage is scaled by
the first exponential factor, exactly as in sequential differential privacy. -/
theorem ApproxDomination.bind_of_pointwise
    {epsilonInput deltaInput epsilonKernel deltaKernel : ℝ}
    {first second : PMF Input}
    (hinput : ApproxDomination epsilonInput deltaInput first second)
    (firstKernel secondKernel : Input → PMF Output)
    (hkernel : ∀ input,
      ApproxDomination epsilonKernel deltaKernel
        (firstKernel input) (secondKernel input)) :
    ApproxDomination (epsilonInput + epsilonKernel)
      (deltaInput + Real.exp epsilonInput * deltaKernel)
      (first.bind firstKernel) (second.bind secondKernel) := by
  intro event
  have hvalueNonneg : ∀ input,
      0 ≤ eventProbability (firstKernel input) event := by
    intro input
    exact AppliedModelingLib.pmfProb_nonneg _ _
  have hvalueBound : ∀ input,
      eventProbability (firstKernel input) event ≤ 1 := by
    intro input
    exact AppliedModelingLib.pmfProb_le_one _ _
  have hinputExpectation := hinput.expectation_le
    (fun input => eventProbability (firstKernel input) event) 1
    hvalueNonneg hvalueBound
  rw [show eventProbability (first.bind firstKernel) event =
      AppliedModelingLib.pmfExp first (fun input => eventProbability (firstKernel input) event) by
        unfold eventProbability
        rw [AppliedModelingLib.pmfProb_bind],
    show eventProbability (second.bind secondKernel) event =
      AppliedModelingLib.pmfExp second (fun input => eventProbability (secondKernel input) event) by
        unfold eventProbability
        rw [AppliedModelingLib.pmfProb_bind]]
  calc
    AppliedModelingLib.pmfExp first (fun input => eventProbability (firstKernel input) event) ≤
        Real.exp epsilonInput *
          AppliedModelingLib.pmfExp second
            (fun input => eventProbability (firstKernel input) event) + deltaInput :=
      by simpa using hinputExpectation
    _ ≤ Real.exp epsilonInput *
          AppliedModelingLib.pmfExp second
            (fun input => Real.exp epsilonKernel *
              eventProbability (secondKernel input) event + deltaKernel) + deltaInput := by
      have hkernelExpectation := AppliedModelingLib.pmfExp_le_pmfExp_of_forall_le second
        (fun input => eventProbability (firstKernel input) event)
        (fun input => Real.exp epsilonKernel *
          eventProbability (secondKernel input) event + deltaKernel)
        (fun input => hkernel input event)
      simpa [add_comm] using
        (add_le_add_right
          (mul_le_mul_of_nonneg_left hkernelExpectation
            (Real.exp_pos epsilonInput).le)
          deltaInput)
    _ = Real.exp (epsilonInput + epsilonKernel) *
          AppliedModelingLib.pmfExp second
            (fun input => eventProbability (secondKernel input) event) +
          (deltaInput + Real.exp epsilonInput * deltaKernel) := by
      rw [AppliedModelingLib.pmfExp_add, AppliedModelingLib.pmfExp_const_mul,
        AppliedModelingLib.pmfExp_const, Real.exp_add]
      ring

/-- Two-sided form of data-dependent finite-kernel composition. -/
theorem MaxKLClose.bind_of_pointwise
    {epsilonInput deltaInput epsilonKernel deltaKernel : ℝ}
    {first second : PMF Input}
    (hinput : MaxKLClose epsilonInput deltaInput first second)
    (firstKernel secondKernel : Input → PMF Output)
    (hkernel : ∀ input,
      MaxKLClose epsilonKernel deltaKernel
        (firstKernel input) (secondKernel input)) :
    MaxKLClose (epsilonInput + epsilonKernel)
      (deltaInput + Real.exp epsilonInput * deltaKernel)
      (first.bind firstKernel) (second.bind secondKernel) :=
  ⟨hinput.1.bind_of_pointwise firstKernel secondKernel (fun input => (hkernel input).1),
    hinput.2.bind_of_pointwise secondKernel firstKernel (fun input => (hkernel input).2)⟩

/-- Arbitrary finite randomized post-processing preserves max-KL closeness. -/
theorem MaxKLClose.bind
    {epsilon delta : ℝ} {first second : PMF Input}
    (h : MaxKLClose epsilon delta first second)
    (kernel : Input → PMF Output) :
    MaxKLClose epsilon delta (first.bind kernel) (second.bind kernel) :=
  ⟨h.1.bind kernel, h.2.bind kernel⟩

end KernelPostprocessing

section TotalVariation

variable {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]

/--
The source-paper total-variation distance bound, expressed directly through
its event characterization.  On a finite output carrier every subset is a
`Finset`, so this has exactly the quantification in BNS16 Definition 4.1.
-/
def TVClose (epsilon : ℝ) (first second : PMF Outcome) : Prop :=
  ∀ event : Finset Outcome,
    |eventProbability first event - eventProbability second event| ≤ epsilon

/--
Two-sided `(ε, δ)` max-KL closeness implies the source paper's
`(2 ε + δ)` total-variation bound in the unit privacy regime.  This is the
eventwise implication stated in BNS16 Section 4; it does not require a
finite-density or full-support convention.
-/
theorem MaxKLClose.toTVClose
    {epsilon delta : ℝ} {first second : PMF Outcome}
    (h : MaxKLClose epsilon delta first second)
    (hepsilonNonneg : 0 ≤ epsilon) (hepsilonOne : epsilon ≤ 1) :
    TVClose (2 * epsilon + delta) first second := by
  have habsEpsilon : |epsilon| ≤ 1 := by
    rw [abs_of_nonneg hepsilonNonneg]
    exact hepsilonOne
  have hexpSub : Real.exp epsilon - 1 ≤ 2 * epsilon := by
    have h := Real.abs_exp_sub_one_le habsEpsilon
    rw [abs_of_nonneg (sub_nonneg.mpr (Real.one_le_exp hepsilonNonneg)),
      abs_of_nonneg hepsilonNonneg] at h
    linarith
  intro event
  have hfirstBound : eventProbability first event ≤ 1 := by
    exact AppliedModelingLib.pmfProb_le_one first (fun outcome => outcome ∈ event)
  have hsecondBound : eventProbability second event ≤ 1 := by
    exact AppliedModelingLib.pmfProb_le_one second (fun outcome => outcome ∈ event)
  have hfirstNonneg : 0 ≤ eventProbability first event := by
    exact AppliedModelingLib.pmfProb_nonneg first (fun outcome => outcome ∈ event)
  have hsecondNonneg : 0 ≤ eventProbability second event := by
    exact AppliedModelingLib.pmfProb_nonneg second (fun outcome => outcome ∈ event)
  have hforward := h.1 event
  have hreverse := h.2 event
  rw [abs_le]
  constructor <;> nlinarith

/-- Total variation is symmetric at the level of its event characterization. -/
theorem TVClose.symm {epsilon : ℝ} {first second : PMF Outcome}
    (h : TVClose epsilon first second) :
    TVClose epsilon second first := by
  intro event
  simpa [abs_sub_comm] using h event

/-- Finite total-variation event bounds obey the triangle inequality. -/
theorem TVClose.triangle {epsilon₁ epsilon₂ : ℝ}
    {first middle last : PMF Outcome}
    (hfirst : TVClose epsilon₁ first middle)
    (hsecond : TVClose epsilon₂ middle last) :
    TVClose (epsilon₁ + epsilon₂) first last := by
  intro event
  calc
    |eventProbability first event - eventProbability last event| ≤
        |eventProbability first event - eventProbability middle event| +
          |eventProbability middle event - eventProbability last event| := by
            rw [show eventProbability first event - eventProbability last event =
              (eventProbability first event - eventProbability middle event) +
                (eventProbability middle event - eventProbability last event) by ring]
            exact abs_add_le _ _
    _ ≤ epsilon₁ + epsilon₂ := add_le_add (hfirst event) (hsecond event)

/-- Deterministic post-processing preserves finite total-variation closeness. -/
theorem TVClose.map {Output : Type*}
    [Fintype Output] [DecidableEq Output]
    {epsilon : ℝ} {first second : PMF Outcome}
    (h : TVClose epsilon first second) (f : Outcome → Output) :
    TVClose epsilon (first.map f) (second.map f) := by
  intro event
  rw [eventProbability_map, eventProbability_map]
  exact h (preimageEvent f event)

/-- A total-variation event bound gives the directed additive event inequality
with `epsilon = 0` in the multiplicative parameter. -/
theorem TVClose.approxDomination {epsilon : ℝ} {first second : PMF Outcome}
    (h : TVClose epsilon first second) :
    ApproxDomination 0 epsilon first second := by
  intro event
  rw [Real.exp_zero, one_mul]
  have hdiff : eventProbability first event - eventProbability second event ≤ epsilon :=
    (le_abs_self (eventProbability first event - eventProbability second event)).trans (h event)
  linarith

/-- Total variation controls the change of every finite bounded nonnegative
expectation.  This is the finite layer-cake consequence used in BNS16
Lemma 4.6. -/
theorem TVClose.abs_expectation_sub_le
    {epsilon : ℝ} {first second : PMF Outcome}
    (h : TVClose epsilon first second)
    (value : Outcome → ℝ) (bound : ℝ)
    (hvalueNonneg : ∀ outcome, 0 ≤ value outcome)
    (hvalueBound : ∀ outcome, value outcome ≤ bound) :
    |AppliedModelingLib.pmfExp first value - AppliedModelingLib.pmfExp second value| ≤ epsilon * bound := by
  have hforward := h.approxDomination.expectation_le value bound
    hvalueNonneg hvalueBound
  have hbackward := h.symm.approxDomination.expectation_le value bound
    hvalueNonneg hvalueBound
  rw [Real.exp_zero, one_mul] at hforward hbackward
  rw [abs_le]
  constructor <;> linarith

/--
The finite coordinate `ℓ¹` discrepancy bounds every event-probability gap by
one half of that discrepancy.  Centering an indicator at `1 / 2` is what
supplies the sharp factor one half.
-/
theorem TVClose.of_half_l1_le
    {epsilon : ℝ} {first second : PMF Outcome}
    (hl1 : (1 / 2 : ℝ) *
      AppliedModelingLib.FiniteDimensionalNorms.l1
        (fun outcome => (first outcome).toReal - (second outcome).toReal) ≤ epsilon) :
    TVClose epsilon first second := by
  intro event
  let indicator : Outcome → ℝ := fun outcome => if outcome ∈ event then 1 else 0
  change |AppliedModelingLib.pmfExp first indicator - AppliedModelingLib.pmfExp second indicator| ≤ epsilon
  have hcenter :
      |AppliedModelingLib.pmfExp first indicator - AppliedModelingLib.pmfExp second indicator| =
        |AppliedModelingLib.pmfExp first (fun outcome => indicator outcome - (1 / 2 : ℝ)) -
          AppliedModelingLib.pmfExp second (fun outcome => indicator outcome - (1 / 2 : ℝ))| := by
    congr 1
    rw [AppliedModelingLib.pmfExp_sub, AppliedModelingLib.pmfExp_const,
      AppliedModelingLib.pmfExp_sub, AppliedModelingLib.pmfExp_const]
    ring
  have hcenterBound : ∀ outcome, |indicator outcome - (1 / 2 : ℝ)| ≤ (1 / 2 : ℝ) := by
    intro outcome
    dsimp [indicator]
    by_cases hmem : outcome ∈ event
    · norm_num [hmem]
    · norm_num [hmem]
  calc
    |AppliedModelingLib.pmfExp first indicator - AppliedModelingLib.pmfExp second indicator| =
        |AppliedModelingLib.pmfExp first (fun outcome => indicator outcome - (1 / 2 : ℝ)) -
          AppliedModelingLib.pmfExp second (fun outcome => indicator outcome - (1 / 2 : ℝ))| := hcenter
    _ ≤ ∑ outcome : Outcome,
        |(first outcome).toReal - (second outcome).toReal| *
          |indicator outcome - (1 / 2 : ℝ)| :=
      AppliedModelingLib.abs_pmfExp_sub_le_sum_abs_atom_mul first second _
    _ ≤ ∑ outcome : Outcome,
        |(first outcome).toReal - (second outcome).toReal| * (1 / 2 : ℝ) := by
      refine Finset.sum_le_sum fun outcome _ => ?_
      exact mul_le_mul_of_nonneg_left (hcenterBound outcome) (abs_nonneg _)
    _ = (1 / 2 : ℝ) *
        AppliedModelingLib.FiniteDimensionalNorms.l1
          (fun outcome => (first outcome).toReal - (second outcome).toReal) := by
      rw [AppliedModelingLib.FiniteDimensionalNorms.normL1_eq_sum_abs, Finset.mul_sum]
      refine Finset.sum_congr rfl fun outcome _ => by ring
    _ ≤ epsilon := hl1

end TotalVariation

section TVRandomizedPostprocessing

variable {Input Seed Output : Type*}
  [Fintype Input] [DecidableEq Input]
  [Fintype Seed] [DecidableEq Seed]
  [Fintype Output] [DecidableEq Output]

/-- A common independent finite random tape preserves total-variation closeness. -/
theorem TVClose.seededPostprocess
    {epsilon : ℝ} {first second : PMF Input}
    (h : TVClose epsilon first second)
    (seedLaw : PMF Seed) (f : Input → Seed → Output) :
    TVClose epsilon
      (seededPostprocess first seedLaw f)
      (seededPostprocess second seedLaw f) := by
  intro event
  rw [eventProbability_seededPostprocess, eventProbability_seededPostprocess]
  exact FiniteCoupling.abs_pmfExp_sub_le_of_forall_abs_sub_le seedLaw _ _ epsilon
    (fun seed => h (preimageEvent (fun input => f input seed) event))

/-- Arbitrary finite randomized post-processing preserves total variation. -/
theorem TVClose.bind
    {epsilon : ℝ} {first second : PMF Input}
    (h : TVClose epsilon first second)
    (kernel : Input → PMF Output) :
    TVClose epsilon (first.bind kernel) (second.bind kernel) := by
  intro event
  rw [← eventProbability_tapedKernelPostprocess first kernel event,
    ← eventProbability_tapedKernelPostprocess second kernel event]
  exact h.seededPostprocess (kernelTape kernel) (fun input tape => tape input) event

end TVRandomizedPostprocessing

section TVCommonPriorKernels

variable {Input Outcome : Type*}
  [Fintype Input] [DecidableEq Input]
  [Fintype Outcome] [DecidableEq Outcome]

/-- Pointwise total-variation closeness of common-prior kernels gives close
joint laws. -/
theorem TVClose.kernelJoint
    {epsilon : ℝ} (prior : PMF Input)
    (first second : Input → PMF Outcome)
    (h : ∀ input, TVClose epsilon (first input) (second input)) :
    TVClose epsilon
      (AppliedModelingLib.pmfKernelJoint prior first)
      (AppliedModelingLib.pmfKernelJoint prior second) := by
  intro event
  unfold eventProbability AppliedModelingLib.pmfKernelJoint
  rw [AppliedModelingLib.pmfProb_bind, AppliedModelingLib.pmfProb_bind]
  apply FiniteCoupling.abs_pmfExp_sub_le_of_forall_abs_sub_le prior _ _ epsilon
  intro input
  have hmap := (h input).map (fun outcome => (input, outcome)) event
  simpa [eventProbability] using hmap

end TVCommonPriorKernels

section Stability

variable {Dataset Output : Type*}
  [Fintype Output] [DecidableEq Output]

/-- A randomized algorithm satisfies the directed max-KL bound on adjacent inputs. -/
def MaxKLStable (adjacent : Dataset → Dataset → Prop)
    (algorithm : Dataset → PMF Output) (epsilon delta : ℝ) : Prop :=
  ∀ ⦃first second : Dataset⦄, adjacent first second →
    ApproxDomination epsilon delta (algorithm first) (algorithm second)

/-- Stability under a symmetric adjacency relation gives two-sided closeness. -/
theorem MaxKLStable.close_of_symmetric
    {adjacent : Dataset → Dataset → Prop} (hadjacent : Symmetric adjacent)
    {algorithm : Dataset → PMF Output} {epsilon delta : ℝ}
    (h : MaxKLStable adjacent algorithm epsilon delta)
    {first second : Dataset} (hfirstSecond : adjacent first second) :
    MaxKLClose epsilon delta (algorithm first) (algorithm second) :=
  ⟨h hfirstSecond, h (hadjacent hfirstSecond)⟩

/-- Deterministic post-processing preserves max-KL stability. -/
theorem MaxKLStable.map {PostOutput : Type*}
    [Fintype PostOutput] [DecidableEq PostOutput]
    {adjacent : Dataset → Dataset → Prop}
    {algorithm : Dataset → PMF Output} {epsilon delta : ℝ}
    (h : MaxKLStable adjacent algorithm epsilon delta) (f : Output → PostOutput) :
    MaxKLStable adjacent (fun dataset => (algorithm dataset).map f) epsilon delta := by
  intro first second hfirstSecond
  exact (h hfirstSecond).map f

/-- Arbitrary finite randomized post-processing preserves max-KL stability. -/
theorem MaxKLStable.bind {PostOutput : Type*}
    [Fintype PostOutput] [DecidableEq PostOutput]
    {adjacent : Dataset → Dataset → Prop}
    {algorithm : Dataset → PMF Output} {epsilon delta : ℝ}
    (h : MaxKLStable adjacent algorithm epsilon delta)
    (kernel : Output → PMF PostOutput) :
    MaxKLStable adjacent (fun dataset => (algorithm dataset).bind kernel) epsilon delta := by
  intro first second hfirstSecond
  exact (h hfirstSecond).bind kernel

/-- Sequential composition of a stable finite algorithm with a post-processing
kernel that may also depend on the private dataset.  The kernel condition is
matched at each possible first-stage output, so the theorem covers adaptive
selection rules such as the exponential mechanism. -/
theorem MaxKLStable.bind_of_pointwise
    {PostOutput : Type*} [Fintype PostOutput] [DecidableEq PostOutput]
    {adjacent : Dataset → Dataset → Prop}
    {algorithm : Dataset → PMF Output}
    {epsilonInput deltaInput epsilonKernel deltaKernel : ℝ}
    (hinput : MaxKLStable adjacent algorithm epsilonInput deltaInput)
    (firstKernel : Dataset → Output → PMF PostOutput)
    (hkernel : ∀ first second output, adjacent first second →
      MaxKLClose epsilonKernel deltaKernel
        (firstKernel first output) (firstKernel second output)) :
    MaxKLStable adjacent
      (fun dataset => (algorithm dataset).bind (firstKernel dataset))
      (epsilonInput + epsilonKernel)
      (deltaInput + Real.exp epsilonInput * deltaKernel) := by
  intro first second hadjacent
  exact (hinput hadjacent).bind_of_pointwise
    (firstKernel first) (firstKernel second)
    (fun output => (hkernel first second output hadjacent).1)

/-- An algorithm is TV-stable when adjacent inputs have close output laws in
the event-wise total-variation sense. -/
def TVStable (adjacent : Dataset → Dataset → Prop)
    (algorithm : Dataset → PMF Output) (epsilon : ℝ) : Prop :=
  ∀ ⦃first second : Dataset⦄, adjacent first second →
    TVClose epsilon (algorithm first) (algorithm second)

/-- Deterministic post-processing preserves TV stability. -/
theorem TVStable.map {PostOutput : Type*}
    [Fintype PostOutput] [DecidableEq PostOutput]
    {adjacent : Dataset → Dataset → Prop}
    {algorithm : Dataset → PMF Output} {epsilon : ℝ}
    (h : TVStable adjacent algorithm epsilon) (f : Output → PostOutput) :
    TVStable adjacent (fun dataset => (algorithm dataset).map f) epsilon := by
  intro first second hfirstSecond
  exact (h hfirstSecond).map f

/-- Arbitrary finite randomized post-processing preserves TV stability. -/
theorem TVStable.bind {PostOutput : Type*}
    [Fintype PostOutput] [DecidableEq PostOutput]
    {adjacent : Dataset → Dataset → Prop}
    {algorithm : Dataset → PMF Output} {epsilon : ℝ}
    (h : TVStable adjacent algorithm epsilon)
    (kernel : Output → PMF PostOutput) :
    TVStable adjacent (fun dataset => (algorithm dataset).bind kernel) epsilon := by
  intro first second hfirstSecond
  exact (h hfirstSecond).bind kernel

end Stability

section SampleAdjacency

variable {Index Data : Type*}

/-- Two fixed-size samples differ at exactly one coordinate. -/
def ExactlyOneAdjacent (first second : Index → Data) : Prop :=
  ∃ index : Index,
    first index ≠ second index ∧
      ∀ other : Index, other ≠ index → first other = second other

/-- Exact one-coordinate replacement adjacency is symmetric. -/
theorem exactlyOneAdjacent_symmetric :
    Symmetric (ExactlyOneAdjacent (Index := Index) (Data := Data)) := by
  intro first second h
  obtain ⟨index, hne, hagree⟩ := h
  refine ⟨index, hne.symm, ?_⟩
  intro other hother
  exact (hagree other hother).symm

/-- Two fixed-size samples differ at at most one coordinate. -/
def ReplaceAdjacent (first second : Index → Data) : Prop :=
  ∃ index : Index, ∀ other : Index, other ≠ index → first other = second other

/-- At-most-one-coordinate replacement adjacency is symmetric. -/
theorem replaceAdjacent_symmetric :
    Symmetric (ReplaceAdjacent (Index := Index) (Data := Data)) := by
  intro first second h
  obtain ⟨index, hagree⟩ := h
  refine ⟨index, ?_⟩
  intro other hother
  exact (hagree other hother).symm

theorem ExactlyOneAdjacent.replaceAdjacent {first second : Index → Data}
    (h : ExactlyOneAdjacent first second) : ReplaceAdjacent first second := by
  obtain ⟨index, _hne, hagree⟩ := h
  exact ⟨index, hagree⟩

end SampleAdjacency

end AppliedModelingLib.Privacy
