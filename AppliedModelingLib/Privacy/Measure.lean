import AppliedModelingLib.Foundations.Probability.MeasureInequalities
import AppliedModelingLib.Privacy.Finite
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.Probability.ConditionalProbability

/-!
# Measure-theoretic approximate domination

This is the continuous-output counterpart of `Privacy.Finite`.  It states the
usual directed differential-privacy event inequality on arbitrary measurable
spaces, supports measurable post-processing, and isolates the standard
privacy-loss bad-event argument without assuming a finite transcript carrier.
-/

open MeasureTheory ProbabilityTheory Set

namespace AppliedModelingLib.Privacy

noncomputable section

/-- Directed `(epsilon, delta)` domination for finite measures on an arbitrary
measurable output space. -/
def MeasureApproxDomination
    {Outcome : Type*} [MeasurableSpace Outcome]
    (epsilon delta : ℝ) (first second : Measure Outcome) : Prop :=
  ∀ event : Set Outcome, MeasurableSet event →
    first.real event ≤ Real.exp epsilon * second.real event + delta

/-- Two-sided measure-theoretic max-KL closeness. -/
def MeasureMaxKLClose
    {Outcome : Type*} [MeasurableSpace Outcome]
    (epsilon delta : ℝ) (first second : Measure Outcome) : Prop :=
  MeasureApproxDomination epsilon delta first second ∧
    MeasureApproxDomination epsilon delta second first

/-- A randomized mechanism with arbitrary measurable output space is
measure-theoretically max-KL stable when neighboring inputs induce
two-sided approximate domination. -/
def MeasureMaxKLStable
    {Input Outcome : Type*} [MeasurableSpace Outcome]
    (adjacent : Input → Input → Prop) (mechanism : Input → Measure Outcome)
    (epsilon delta : ℝ) : Prop :=
  ∀ first second, adjacent first second →
    MeasureMaxKLClose epsilon delta (mechanism first) (mechanism second)

/-- Any finite measure is two-sided close to itself for nonnegative privacy
parameters. -/
theorem MeasureMaxKLClose.refl
    {Outcome : Type*} [MeasurableSpace Outcome]
    (law : Measure Outcome) {epsilon delta : ℝ}
    (hepsilon : 0 ≤ epsilon) (hdelta : 0 ≤ delta) :
    MeasureMaxKLClose epsilon delta law law := by
  have hdirected : MeasureApproxDomination epsilon delta law law := by
    intro event hevent
    have hexp : 1 ≤ Real.exp epsilon := by
      simpa using (Real.exp_le_exp.mpr hepsilon)
    have hmass : 0 ≤ law.real event := measureReal_nonneg
    calc
      law.real event = 1 * law.real event + 0 := by ring
      _ ≤ Real.exp epsilon * law.real event + delta :=
        add_le_add (mul_le_mul_of_nonneg_right hexp hmass) hdelta
  exact ⟨hdirected, hdirected⟩

/-- Directed domination is monotone in both privacy parameters. -/
theorem MeasureApproxDomination.mono
    {Outcome : Type*} [MeasurableSpace Outcome]
    {epsilon delta epsilon' delta' : ℝ} {first second : Measure Outcome}
    (h : MeasureApproxDomination epsilon delta first second)
    (hepsilon : epsilon ≤ epsilon') (hdelta : delta ≤ delta') :
    MeasureApproxDomination epsilon' delta' first second := by
  intro event hevent
  have hbase := h event hevent
  have hexp : Real.exp epsilon ≤ Real.exp epsilon' :=
    Real.exp_le_exp.mpr hepsilon
  have hmass : 0 ≤ second.real event := measureReal_nonneg
  calc
    first.real event ≤ Real.exp epsilon * second.real event + delta := hbase
    _ ≤ Real.exp epsilon' * second.real event + delta' :=
      add_le_add (mul_le_mul_of_nonneg_right hexp hmass) hdelta

/-- Two-sided closeness is monotone in both privacy parameters. -/
theorem MeasureMaxKLClose.mono
    {Outcome : Type*} [MeasurableSpace Outcome]
    {epsilon delta epsilon' delta' : ℝ} {first second : Measure Outcome}
    (h : MeasureMaxKLClose epsilon delta first second)
    (hepsilon : epsilon ≤ epsilon') (hdelta : delta ≤ delta') :
    MeasureMaxKLClose epsilon' delta' first second :=
  ⟨h.1.mono hepsilon hdelta, h.2.mono hepsilon hdelta⟩

/-- A privacy-loss exceptional event can be paid once, provided domination
holds on the part of every event outside that exception. -/
theorem MeasureApproxDomination.of_outside_bad
    {Outcome : Type*} [MeasurableSpace Outcome]
    {epsilon delta : ℝ} (first second : Measure Outcome)
    [IsFiniteMeasure first] [IsFiniteMeasure second]
    (bad : Set Outcome) (hbadMeasurable : MeasurableSet bad)
    (hbad : first.real bad ≤ delta)
    (houtside : ∀ event : Set Outcome, MeasurableSet event →
      first.real (event \ bad) ≤ Real.exp epsilon * second.real event) :
    MeasureApproxDomination epsilon delta first second := by
  intro event hevent
  have hsplit := measureReal_inter_add_diff (μ := first) (s := event)
    (t := bad) hbadMeasurable
  have hinter : first.real (event ∩ bad) ≤ first.real bad :=
    measureReal_mono inter_subset_right
  have hout := houtside event hevent
  linarith

/-- Pure pointwise event domination is the zero-exception special case. -/
theorem MeasureApproxDomination.of_eventwise
    {Outcome : Type*} [MeasurableSpace Outcome]
    {epsilon delta : ℝ} {first second : Measure Outcome}
    (hdelta : 0 ≤ delta)
    (h : ∀ event : Set Outcome, MeasurableSet event →
      first.real event ≤ Real.exp epsilon * second.real event) :
    MeasureApproxDomination epsilon delta first second := by
  intro event hevent
  exact (h event hevent).trans (by linarith)

/-- Measurable deterministic post-processing preserves directed approximate
domination. -/
theorem MeasureApproxDomination.map
    {Input Output : Type*} [MeasurableSpace Input] [MeasurableSpace Output]
    {epsilon delta : ℝ} {first second : Measure Input}
    (h : MeasureApproxDomination epsilon delta first second)
    (f : Input → Output) (hf : Measurable f) :
    MeasureApproxDomination epsilon delta (first.map f) (second.map f) := by
  intro event hevent
  simp only [Measure.real_def]
  rw [Measure.map_apply hf hevent, Measure.map_apply hf hevent]
  exact h (f ⁻¹' event) (hevent.preimage hf)

/-- Measurable deterministic post-processing preserves two-sided closeness. -/
theorem MeasureMaxKLClose.map
    {Input Output : Type*} [MeasurableSpace Input] [MeasurableSpace Output]
    {epsilon delta : ℝ} {first second : Measure Input}
    (h : MeasureMaxKLClose epsilon delta first second)
    (f : Input → Output) (hf : Measurable f) :
    MeasureMaxKLClose epsilon delta (first.map f) (second.map f) :=
  ⟨h.1.map f hf, h.2.map f hf⟩

/-- Two measurable post-processings of the same law are `(0, delta)`
max-KL-close when they can differ only on a source event of probability at
most `delta`. -/
theorem MeasureMaxKLClose.map_of_agree_outside
    {Seed Output : Type*} [MeasurableSpace Seed] [MeasurableSpace Output]
    (law : Measure Seed) [IsFiniteMeasure law] (first second : Seed → Output)
    (hfirst : Measurable first) (hsecond : Measurable second)
    (bad : Set Seed) (delta : ℝ)
    (hbad : law.real bad ≤ delta)
    (hagrees : ∀ seed, seed ∉ bad → first seed = second seed) :
    MeasureMaxKLClose 0 delta (law.map first) (law.map second) := by
  have hforward : MeasureApproxDomination 0 delta (law.map first) (law.map second) := by
    intro event hevent
    simp only [Measure.real_def, Measure.map_apply hfirst hevent,
      Measure.map_apply hsecond hevent]
    have hsubset : {seed | first seed ∈ event} ⊆ {seed | second seed ∈ event} ∪ bad := by
      intro seed hseed
      by_cases hseedBad : seed ∈ bad
      · exact Or.inr hseedBad
      · left
        simpa [hagrees seed hseedBad] using hseed
    calc
      law.real {seed | first seed ∈ event} ≤
          law.real ({seed | second seed ∈ event} ∪ bad) :=
        measureReal_mono hsubset (measure_ne_top _ _)
      _ ≤ law.real {seed | second seed ∈ event} + law.real bad :=
        measureReal_union_le _ _
      _ ≤ law.real {seed | second seed ∈ event} + delta :=
        add_le_add_right hbad _
      _ = Real.exp 0 * law.real {seed | second seed ∈ event} + delta := by simp
  have hbackward : MeasureApproxDomination 0 delta (law.map second) (law.map first) := by
    intro event hevent
    simp only [Measure.real_def, Measure.map_apply hsecond hevent,
      Measure.map_apply hfirst hevent]
    have hsubset : {seed | second seed ∈ event} ⊆ {seed | first seed ∈ event} ∪ bad := by
      intro seed hseed
      by_cases hseedBad : seed ∈ bad
      · exact Or.inr hseedBad
      · left
        simpa [hagrees seed hseedBad] using hseed
    calc
      law.real {seed | second seed ∈ event} ≤
          law.real ({seed | first seed ∈ event} ∪ bad) :=
        measureReal_mono hsubset (measure_ne_top _ _)
      _ ≤ law.real {seed | first seed ∈ event} + law.real bad :=
        measureReal_union_le _ _
      _ ≤ law.real {seed | first seed ∈ event} + delta :=
        add_le_add_right hbad _
      _ = Real.exp 0 * law.real {seed | first seed ∈ event} + delta := by simp
  exact ⟨hforward, hbackward⟩

/-- Converting probability measures on a finite discrete space to `PMF`s
preserves directed approximate domination.  This is the bridge from a
continuous private mechanism followed by finite measurable post-processing to
the finite transcript semantics used by adaptive-data-analysis transfer
theorems. -/
theorem MeasureApproxDomination.toPMF
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    [MeasurableSpace Outcome] [DiscreteMeasurableSpace Outcome]
    {epsilon delta : ℝ} {first second : Measure Outcome}
    [IsProbabilityMeasure first] [IsProbabilityMeasure second]
    (h : MeasureApproxDomination epsilon delta first second) :
    ApproxDomination epsilon delta first.toPMF second.toPMF := by
  intro event
  have hevent : MeasurableSet ({outcome | outcome ∈ event} : Set Outcome) :=
    MeasurableSet.of_discrete
  simpa [eventProbability, AppliedModelingLib.pmfProb_eq_toMeasure_real,
    Measure.toPMF_toMeasure] using
    h ({outcome | outcome ∈ event} : Set Outcome) hevent

/-- Finite `PMF` conversion also preserves the two-sided max-KL relation. -/
theorem MeasureMaxKLClose.toPMF
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    [MeasurableSpace Outcome] [DiscreteMeasurableSpace Outcome]
    {epsilon delta : ℝ} {first second : Measure Outcome}
    [IsProbabilityMeasure first] [IsProbabilityMeasure second]
    (h : MeasureMaxKLClose epsilon delta first second) :
    MaxKLClose epsilon delta first.toPMF second.toPMF :=
  ⟨h.1.toPMF, h.2.toPMF⟩

/-- Real-valued event mass under conditioning is the familiar ratio. -/
theorem cond_real_apply
    {Outcome : Type*} [MeasurableSpace Outcome]
    (measure : Measure Outcome) (conditioning event : Set Outcome)
    (hconditioning : MeasurableSet conditioning) :
    (measure[|conditioning]).real event =
      measure.real (conditioning ∩ event) / measure.real conditioning := by
  rw [Measure.real_def, cond_apply hconditioning]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, Measure.real_def]
  ring

/-- Conditioning both laws on the same positive-probability event doubles a
pure privacy parameter.  One factor controls the restricted numerator; the
second controls the ratio of the two normalizing constants. -/
theorem MeasureApproxDomination.cond_of_reverse
    {Outcome : Type*} [MeasurableSpace Outcome]
    {epsilon : ℝ} {first second : Measure Outcome}
    (hforward : MeasureApproxDomination epsilon 0 first second)
    (hreverse : MeasureApproxDomination epsilon 0 second first)
    (conditioning : Set Outcome) (hconditioning : MeasurableSet conditioning)
    (hfirstPos : 0 < first.real conditioning)
    (hsecondPos : 0 < second.real conditioning) :
    MeasureApproxDomination (epsilon + epsilon) 0
      first[|conditioning] second[|conditioning] := by
  intro event hevent
  have hnumerator :
      first.real (conditioning ∩ event) ≤
        Real.exp epsilon * second.real (conditioning ∩ event) := by
    simpa using hforward (conditioning ∩ event)
      (hconditioning.inter hevent)
  have hnormalizer :
      second.real conditioning ≤
        Real.exp epsilon * first.real conditioning := by
    simpa using hreverse conditioning hconditioning
  have hfirstNumerator : 0 ≤ first.real (conditioning ∩ event) :=
    measureReal_nonneg
  have hsecondNumerator : 0 ≤ second.real (conditioning ∩ event) :=
    measureReal_nonneg
  have hsecondMass : 0 ≤ second.real conditioning := measureReal_nonneg
  have hexp : 0 ≤ Real.exp epsilon := (Real.exp_pos _).le
  have hproduct :
      first.real (conditioning ∩ event) * second.real conditioning ≤
        (Real.exp (epsilon + epsilon) *
          second.real (conditioning ∩ event)) * first.real conditioning := by
    calc
      first.real (conditioning ∩ event) * second.real conditioning ≤
          (Real.exp epsilon * second.real (conditioning ∩ event)) *
            second.real conditioning :=
        mul_le_mul_of_nonneg_right hnumerator hsecondMass
      _ ≤ (Real.exp epsilon * second.real (conditioning ∩ event)) *
            (Real.exp epsilon * first.real conditioning) :=
        mul_le_mul_of_nonneg_left hnormalizer
          (mul_nonneg hexp hsecondNumerator)
      _ = (Real.exp (epsilon + epsilon) *
          second.real (conditioning ∩ event)) * first.real conditioning := by
        rw [Real.exp_add]
        ring
  rw [cond_real_apply first conditioning event hconditioning,
    cond_real_apply second conditioning event hconditioning]
  simpa [mul_div_assoc] using
    (div_le_div_iff₀ hfirstPos hsecondPos).2 hproduct

/-- Two-sided pure privacy is preserved under common conditioning with twice
the parameter. -/
theorem MeasureMaxKLClose.cond
    {Outcome : Type*} [MeasurableSpace Outcome]
    {epsilon : ℝ} {first second : Measure Outcome}
    (h : MeasureMaxKLClose epsilon 0 first second)
    (conditioning : Set Outcome) (hconditioning : MeasurableSet conditioning)
    (hfirstPos : 0 < first.real conditioning)
    (hsecondPos : 0 < second.real conditioning) :
    MeasureMaxKLClose (epsilon + epsilon) 0
      first[|conditioning] second[|conditioning] :=
  ⟨h.1.cond_of_reverse h.2 conditioning hconditioning hfirstPos hsecondPos,
    h.2.cond_of_reverse h.1 conditioning hconditioning hsecondPos hfirstPos⟩

/-- Directed measure domination is transitive with the standard scaled second
exceptional probability. -/
theorem MeasureApproxDomination.trans
    {Outcome : Type*} [MeasurableSpace Outcome]
    {epsilon₁ delta₁ epsilon₂ delta₂ : ℝ}
    {first middle last : Measure Outcome}
    (hfirst : MeasureApproxDomination epsilon₁ delta₁ first middle)
    (hsecond : MeasureApproxDomination epsilon₂ delta₂ middle last) :
    MeasureApproxDomination (epsilon₁ + epsilon₂)
      (delta₁ + Real.exp epsilon₁ * delta₂) first last := by
  intro event hevent
  have h₁ := hfirst event hevent
  have h₂ := hsecond event hevent
  have hexp : 0 ≤ Real.exp epsilon₁ := (Real.exp_pos _).le
  calc
    first.real event ≤ Real.exp epsilon₁ * middle.real event + delta₁ := h₁
    _ ≤ Real.exp epsilon₁ *
          (Real.exp epsilon₂ * last.real event + delta₂) + delta₁ := by
      simpa [add_comm] using
        add_le_add_right (mul_le_mul_of_nonneg_left h₂ hexp) delta₁
    _ = Real.exp (epsilon₁ + epsilon₂) * last.real event +
          (delta₁ + Real.exp epsilon₁ * delta₂) := by
      rw [Real.exp_add]
      ring

end

end AppliedModelingLib.Privacy
