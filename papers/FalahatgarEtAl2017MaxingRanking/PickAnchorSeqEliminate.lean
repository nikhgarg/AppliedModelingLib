import FalahatgarEtAl2017MaxingRanking.PickAnchorTail
import FalahatgarEtAl2017MaxingRanking.SubsetSequentialElimination
import FalahatgarEtAl2017MaxingRanking.AdaptiveSeqEliminateProbability
import FalahatgarEtAl2017MaxingRanking.AdaptiveSeqEliminateCost
import Mathlib.Data.List.FinRange

/-!
# Pick-Anchor's sampled Seq-Eliminate run

The sample in Lemma 3 / Appendix A.5 is an ordered fresh list, whereas
Seq-Eliminate consumes an initial incumbent and a challenger list.  This file
is the source-faithful bridge between those two representations.  In
particular, its local maximum is required to lie in the realized sample--it is
not a global maximum smuggled into a sampled subproblem.
-/

namespace FalahatgarEtAl2017MaxingRanking

open AppliedModelingLib PreferenceRL
open MeasureTheory ProbabilityTheory

/-- The ordered list underlying a fresh Pick-Anchor sample. -/
noncomputable def pickAnchorSampleList {Arm : Type*}
    {count : ℕ} (sample : finiteFreshList Arm count ∅) : List Arm :=
  List.ofFn sample.1

/-- Every fresh-sample slot appears exactly once in `pickAnchorSampleList`. -/
theorem pickAnchorSampleList_length {Arm : Type*}
    {count : ℕ} (sample : finiteFreshList Arm count ∅) :
    (pickAnchorSampleList sample).length = count := by
  simp [pickAnchorSampleList]

/-- Membership in the sampler's finite set agrees with membership in its ordered list. -/
theorem mem_pickAnchorSampleList_iff {Arm : Type*} [DecidableEq Arm]
    {count : ℕ} (sample : finiteFreshList Arm count ∅) (arm : Arm) :
    arm ∈ pickAnchorSampleList sample ↔ arm ∈ pickAnchorSampleSet sample := by
  classical
  constructor
  · rw [pickAnchorSampleList, List.mem_ofFn']
    rintro ⟨slot, rfl⟩
    exact (finiteFreshList_mem_prefixSet_iff sample (sample.1 slot)).2
      ⟨slot, slot.isLt, rfl⟩
  · intro hsample
    rw [pickAnchorSampleList, List.mem_ofFn']
    rcases (finiteFreshList_mem_prefixSet_iff sample arm).1 hsample with
      ⟨slot, _hslot, hvalue⟩
    exact ⟨slot, hvalue⟩

/-- A fresh Pick-Anchor sample has no duplicated input arms. -/
theorem pickAnchorSampleList_nodup {Arm : Type*}
    {count : ℕ} (sample : finiteFreshList Arm count ∅) :
    (pickAnchorSampleList sample).Nodup := by
  apply List.nodup_ofFn.mpr
  exact sample.2.1

/-- The first realized sample arm is Seq-Eliminate's initial incumbent. -/
noncomputable def pickAnchorSampleInitial {Arm : Type*}
    {count : ℕ} (sample : finiteFreshList Arm count ∅) (hcount : 0 < count) : Arm :=
  sample.1 ⟨0, hcount⟩

/-- The remaining realized sample arms are Seq-Eliminate's challengers. -/
noncomputable def pickAnchorSampleChallengers {Arm : Type*}
    {count : ℕ} (sample : finiteFreshList Arm count ∅) : List Arm :=
  (pickAnchorSampleList sample).tail

/-- A nonempty fresh sample decomposes into its source-order head and tail. -/
theorem pickAnchorSampleList_eq_initial_cons_challengers {Arm : Type*}
    {count : ℕ} (sample : finiteFreshList Arm count ∅) (hcount : 0 < count) :
    pickAnchorSampleList sample =
      pickAnchorSampleInitial sample hcount :: pickAnchorSampleChallengers sample := by
  cases count with
  | zero => omega
  | succ count =>
      simp [pickAnchorSampleList, pickAnchorSampleInitial, pickAnchorSampleChallengers]

/-- Seq-Eliminate makes exactly one call per sampled arm after the first. -/
theorem pickAnchorSampleChallengers_length {Arm : Type*}
    {count : ℕ} (sample : finiteFreshList Arm count ∅) (hcount : 0 < count) :
    (pickAnchorSampleChallengers sample).length = count - 1 := by
  have hsplit := pickAnchorSampleList_eq_initial_cons_challengers sample hcount
  have hlength := pickAnchorSampleList_length sample
  rw [hsplit, List.length_cons] at hlength
  omega

/-- A positive-size fresh sample has a nonempty source-order list. -/
theorem pickAnchorSampleList_ne_nil {Arm : Type*}
    {count : ℕ} (sample : finiteFreshList Arm count ∅) (hcount : 0 < count) :
    pickAnchorSampleList sample ≠ [] := by
  intro hnil
  have hlength := pickAnchorSampleList_length sample
  rw [hnil] at hlength
  simp at hlength
  omega

/--
Every nonempty Pick-Anchor sample has its own weak maximum under the source's
complete SST model.  This is the `q*` selected in Appendix A.5, and is not
assumed to be a maximum of the unsampled population.
-/
theorem exists_pickAnchorSample_localMaximum
    {Arm : Type*} [DecidableEq Arm]
    {count : ℕ} (sample : finiteFreshList Arm count ∅) (hcount : 0 < count)
    (preferenceGap : Arm → Arm → ℝ)
    (hcomplete : PreferenceComplete preferenceGap)
    (hsst : StrongStochasticTransitivity preferenceGap) :
    ∃ maximum, maximum ∈ pickAnchorSampleSet sample ∧
      ∀ arm ∈ pickAnchorSampleSet sample, 0 ≤ preferenceGap maximum arm := by
  rcases exists_listMaximum_of_preferenceComplete preferenceGap hcomplete hsst
    (pickAnchorSampleList sample) (pickAnchorSampleList_ne_nil sample hcount) with
      ⟨maximum, hmaximumMem, hmaximum⟩
  refine ⟨maximum, (mem_pickAnchorSampleList_iff sample maximum).1 hmaximumMem, ?_⟩
  intro arm harm
  exact hmaximum arm ((mem_pickAnchorSampleList_iff sample arm).2 harm)

/-- The actual sampled Seq-Eliminate output used by Pick-Anchor. -/
noncomputable def pickAnchorSampleSeqEliminate {Arm : Type*}
    {count : ℕ} (step : Arm → Arm → Arm)
    (sample : finiteFreshList Arm count ∅) (hcount : 0 < count) : Arm :=
  sequentialEliminate step (pickAnchorSampleInitial sample hcount)
    (pickAnchorSampleChallengers sample)

/-- A source Seq-Eliminate step retains either its incumbent or its challenger. -/
theorem adaptiveCompareStep_returns_input
    {Arm Ω : Type*}
    (observation : Arm → Arm → ℕ → Ω → ℝ) (count : ℕ)
    (epsilon delta : ℝ) (outcome : Ω) (incumbent challenger : Arm) :
    adaptiveCompareStep observation count epsilon delta outcome incumbent challenger = incumbent ∨
      adaptiveCompareStep observation count epsilon delta outcome incumbent challenger = challenger := by
  unfold adaptiveCompareStep
  split <;> simp

/-- Pick-Anchor's Seq-Eliminate output is one of the actually sampled arms. -/
theorem pickAnchorSample_seqEliminate_mem_sampleSet
    {Arm : Type*} [DecidableEq Arm]
    {count : ℕ} (step : Arm → Arm → Arm)
    (hstep : ∀ incumbent challenger,
      step incumbent challenger = incumbent ∨ step incumbent challenger = challenger)
    (sample : finiteFreshList Arm count ∅) (hcount : 0 < count) :
    pickAnchorSampleSeqEliminate step sample hcount ∈ pickAnchorSampleSet sample := by
  apply (mem_pickAnchorSampleList_iff sample
    (pickAnchorSampleSeqEliminate step sample hcount)).1
  rw [pickAnchorSampleList_eq_initial_cons_challengers sample hcount]
  simpa [pickAnchorSampleSeqEliminate] using
    (sequentialEliminate_mem_input_of_step_returns_input step hstep
      (pickAnchorSampleInitial sample hcount) (pickAnchorSampleChallengers sample))

/-- The concrete adaptive Pick-Anchor winner remains in the realized sample. -/
theorem pickAnchorSample_adaptiveSeqEliminate_mem_sampleSet
    {Arm Ω : Type*} [DecidableEq Arm]
    {count : ℕ} (observation : Arm → Arm → ℕ → Ω → ℝ) (budget : ℕ)
    (epsilon delta : ℝ) (outcome : Ω)
    (sample : finiteFreshList Arm count ∅) (hcount : 0 < count) :
    pickAnchorSampleSeqEliminate
      (adaptiveCompareStep observation budget epsilon delta outcome) sample hcount ∈
      pickAnchorSampleSet sample :=
  pickAnchorSample_seqEliminate_mem_sampleSet
    (adaptiveCompareStep observation budget epsilon delta outcome)
    (adaptiveCompareStep_returns_input observation budget epsilon delta outcome) sample hcount

/--
The realized adaptive Pick-Anchor Seq-Eliminate phase has at most one capped
adaptive comparison for every sampled arm after the first.
-/
theorem pickAnchorSample_adaptiveSeqEliminate_stoppingTimes_sum_le
    {Arm Ω : Type*}
    {count : ℕ} (sample : finiteFreshList Arm count ∅) (hcount : 0 < count)
    (observation : Arm → Arm → ℕ → Ω → ℝ) (budget : ℕ)
    (epsilon delta : ℝ) (outcome : Ω) :
    (adaptiveSeqEliminateStoppingTimes observation budget epsilon delta outcome
      (pickAnchorSampleInitial sample hcount)
      (pickAnchorSampleChallengers sample)).sum ≤
      (count - 1) * budget := by
  calc
    (adaptiveSeqEliminateStoppingTimes observation budget epsilon delta outcome
      (pickAnchorSampleInitial sample hcount)
      (pickAnchorSampleChallengers sample)).sum ≤
        (pickAnchorSampleChallengers sample).length * budget :=
          adaptiveSeqEliminateStoppingTimes_sum_le observation budget epsilon delta outcome
            (pickAnchorSampleInitial sample hcount) (pickAnchorSampleChallengers sample)
    _ = (count - 1) * budget := by
      rw [pickAnchorSampleChallengers_length sample hcount]

/--
Algorithm 5 invokes `Seq-Eliminate(Q, ε, δ / 2)`.  Since that subroutine
divides its confidence equally over its `|Q|` candidate calls, every realized
comparison has source confidence parameter `δ / (2 |Q|)`.  This is the exact
finite comparison cap for the source schedule, with the executable ceiling
inside `fixedSampleBudget` made explicit.

The probability proof for this adaptive, sample-indexed call family is kept
separate: this deterministic theorem does not replace it with a larger
all-pairs schedule.
-/
theorem pickAnchorSample_adaptiveSeqEliminate_stoppingTimes_sum_le_sourceSchedule
    {Arm Ω : Type*}
    {count : ℕ} (sample : finiteFreshList Arm count ∅) (hcount : 0 < count)
    (observation : Arm → Arm → ℕ → Ω → ℝ) (epsilon delta : ℝ) (outcome : Ω) :
    (adaptiveSeqEliminateStoppingTimes observation
      (fixedSampleBudget 0 epsilon ((delta / 2) / (count : ℝ))) epsilon
      ((delta / 2) / (count : ℝ)) outcome
      (pickAnchorSampleInitial sample hcount)
      (pickAnchorSampleChallengers sample)).sum ≤
      (count - 1) * fixedSampleBudget 0 epsilon ((delta / 2) / (count : ℝ)) := by
  exact pickAnchorSample_adaptiveSeqEliminate_stoppingTimes_sum_le sample hcount observation
    (fixedSampleBudget 0 epsilon ((delta / 2) / (count : ℝ))) epsilon
    ((delta / 2) / (count : ℝ)) outcome

/--
A list-local maximum of a realized Pick-Anchor sample yields a maximum premise
for the sampled Seq-Eliminate theorem.  The premise explicitly includes both
membership in the sample and domination only over sampled arms.
-/
theorem pickAnchorSample_listAbsoluteMaximum_of_localMaximum
    {Arm : Type*} [DecidableEq Arm]
    {count : ℕ} (sample : finiteFreshList Arm count ∅) (hcount : 0 < count)
    (preferenceGap : Arm → Arm → ℝ) (maximum : Arm)
    (hmaximumMem : maximum ∈ pickAnchorSampleSet sample)
    (hmaximum : ∀ arm ∈ pickAnchorSampleSet sample,
      0 ≤ preferenceGap maximum arm) :
    ListAbsoluteMaximum preferenceGap maximum
      (pickAnchorSampleInitial sample hcount)
      (pickAnchorSampleChallengers sample) := by
  have hsplit := pickAnchorSampleList_eq_initial_cons_challengers sample hcount
  have hmaximumList : maximum ∈ pickAnchorSampleList sample :=
    (mem_pickAnchorSampleList_iff sample maximum).2 hmaximumMem
  constructor
  · rw [hsplit] at hmaximumList
    simpa using hmaximumList
  · intro competitor hcompetitor
    apply hmaximum competitor
    apply (mem_pickAnchorSampleList_iff sample competitor).1
    rw [hsplit]
    simpa using hcompetitor

/--
A list-local `ε`-maximum is exactly an `ε`-maximum of the corresponding
finite Pick-Anchor sample set.
-/
theorem pickAnchorSample_listEpsilonMaximum_implies_sampleEpsilonMaximum
    {Arm : Type*} [DecidableEq Arm]
    {count : ℕ} (sample : finiteFreshList Arm count ∅) (hcount : 0 < count)
    (preferenceGap : Arm → Arm → ℝ) (epsilon : ℝ) (selected : Arm)
    (hmaximum : ListEpsilonMaximum preferenceGap epsilon
      (pickAnchorSampleInitial sample hcount) (pickAnchorSampleChallengers sample) selected) :
    ∀ arm ∈ pickAnchorSampleSet sample, -epsilon ≤ preferenceGap selected arm := by
  intro arm harm
  apply hmaximum arm
  have hlist : arm ∈ pickAnchorSampleList sample :=
    (mem_pickAnchorSampleList_iff sample arm).2 harm
  rw [pickAnchorSampleList_eq_initial_cons_challengers sample hcount] at hlist
  simpa using hlist

/--
Appendix A.5's deterministic sampled-winner statement: a valid Seq-Eliminate
run is an `ε`-maximum of the *realized Pick-Anchor sample*.  It deliberately
does not assume the globally best arm was sampled.
-/
theorem pickAnchorSample_seqEliminate_epsilonMaximum_of_localMaximum
    {Arm : Type*} [DecidableEq Arm]
    {count : ℕ} (sample : finiteFreshList Arm count ∅) (hcount : 0 < count)
    (preferenceGap : Arm → Arm → ℝ) (epsilon : ℝ) (step : Arm → Arm → Arm)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hepsilon : 0 ≤ epsilon)
    (hvalid : SequentialEliminationStepValid preferenceGap epsilon step)
    (maximum : Arm)
    (hmaximumMem : maximum ∈ pickAnchorSampleSet sample)
    (hmaximum : ∀ arm ∈ pickAnchorSampleSet sample,
      0 ≤ preferenceGap maximum arm) :
    ∀ arm ∈ pickAnchorSampleSet sample,
      -epsilon ≤ preferenceGap
        (pickAnchorSampleSeqEliminate step sample hcount) arm := by
  have hlocal := pickAnchorSample_listAbsoluteMaximum_of_localMaximum
    sample hcount preferenceGap maximum hmaximumMem hmaximum
  have hresult := sequentialEliminate_listEpsilonMaximum_of_listMaximumAppears
    preferenceGap epsilon step hantisymmetric hsst hepsilon hvalid maximum
    (pickAnchorSampleInitial sample hcount) (pickAnchorSampleChallengers sample) hlocal
  intro arm harm
  apply hresult arm
  have hlist : arm ∈ pickAnchorSampleList sample :=
    (mem_pickAnchorSampleList_iff sample arm).2 harm
  rw [pickAnchorSampleList_eq_initial_cons_challengers sample hcount] at hlist
  simpa using hlist

/--
The sampled adaptive Seq-Eliminate winner satisfies the source's sample-local
`ε`-maximum conclusion whenever every ordered-pair adaptive call is valid on
the realized observation outcome.  This is the deterministic event to which
the finite all-pairs failure bound applies.
-/
theorem pickAnchorSample_adaptiveSeqEliminate_epsilonMaximum_of_allPairCallValid
    {Arm Ω : Type*} [DecidableEq Arm]
    {count : ℕ} (sample : finiteFreshList Arm count ∅) (hcount : 0 < count)
    (observation : Arm → Arm → ℕ → Ω → ℝ) (budget : ℕ)
    (preferenceGap : Arm → Arm → ℝ) (epsilon delta : ℝ) (outcome : Ω)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hepsilon : 0 ≤ epsilon)
    (hvalid : ∀ incumbent challenger,
      AdaptiveCompareStepCallValid observation budget preferenceGap epsilon delta outcome
        incumbent challenger)
    (maximum : Arm)
    (hmaximumMem : maximum ∈ pickAnchorSampleSet sample)
    (hmaximum : ∀ arm ∈ pickAnchorSampleSet sample,
      0 ≤ preferenceGap maximum arm) :
    ∀ arm ∈ pickAnchorSampleSet sample,
      -epsilon ≤ preferenceGap
        (pickAnchorSampleSeqEliminate
          (adaptiveCompareStep observation budget epsilon delta outcome) sample hcount) arm :=
  pickAnchorSample_seqEliminate_epsilonMaximum_of_localMaximum
    sample hcount preferenceGap epsilon
    (adaptiveCompareStep observation budget epsilon delta outcome)
    hantisymmetric hsst hepsilon hvalid maximum hmaximumMem hmaximum

/--
The finite all-pairs adaptive-Compare bound transfers to a Pick-Anchor winner
even when the fresh sample is itself a component of the probability outcome.
The local best arm may therefore vary with the realized sample; no global-max
assumption is introduced.  A product construction that makes sampling and
comparison streams independent can instantiate the explicit iid hypotheses.
-/
theorem pickAnchorSample_adaptiveSeqEliminate_failure_probability_of_allPairBudget
    {Arm Ω : Type*} [MeasurableSpace Ω] [Fintype Arm] [DecidableEq Arm] [Nonempty Arm]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (observation : Arm → Arm → ℕ → Ω → ℝ)
    (preferenceGap : Arm → Arm → ℝ) (epsilon eta : ℝ)
    (hindependent : ∀ challenger incumbent,
      iIndepFun (observation challenger incumbent) law)
    (hmeasurable : ∀ challenger incumbent sampleIndex,
      Measurable (observation challenger incumbent sampleIndex))
    (hbounded : ∀ challenger incumbent,
      ∀ sampleIndex < fixedSampleBudget 0 epsilon (eta / (Fintype.card (Arm × Arm) : ℝ)),
        ∀ᵐ outcome ∂law, observation challenger incumbent sampleIndex outcome ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ challenger incumbent,
      ∀ sampleIndex < fixedSampleBudget 0 epsilon (eta / (Fintype.card (Arm × Arm) : ℝ)),
        law[observation challenger incumbent sampleIndex] =
          1 / 2 + preferenceGap challenger incumbent)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hself : ∀ arm, preferenceGap arm arm = 0)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hepsilon : 0 < epsilon)
    (heta : 0 < eta) (hetaLeOne : eta ≤ 1)
    {sampleCount : ℕ} (sample : Ω → finiteFreshList Arm sampleCount ∅)
    (hsampleCount : 0 < sampleCount)
    (maximum : Ω → Arm)
    (hmaximumMem : ∀ outcome,
      maximum outcome ∈ pickAnchorSampleSet (sample outcome))
    (hmaximum : ∀ outcome arm, arm ∈ pickAnchorSampleSet (sample outcome) →
      0 ≤ preferenceGap (maximum outcome) arm) :
    law.real {outcome | ¬ ∀ arm ∈ pickAnchorSampleSet (sample outcome),
      -epsilon ≤ preferenceGap
        (pickAnchorSampleSeqEliminate
          (adaptiveCompareStep observation
            (fixedSampleBudget 0 epsilon (eta / (Fintype.card (Arm × Arm) : ℝ)))
            epsilon (eta / (Fintype.card (Arm × Arm) : ℝ)) outcome)
          (sample outcome) hsampleCount) arm} ≤ eta := by
  calc
    law.real {outcome | ¬ ∀ arm ∈ pickAnchorSampleSet (sample outcome),
        -epsilon ≤ preferenceGap
          (pickAnchorSampleSeqEliminate
            (adaptiveCompareStep observation
              (fixedSampleBudget 0 epsilon (eta / (Fintype.card (Arm × Arm) : ℝ)))
              epsilon (eta / (Fintype.card (Arm × Arm) : ℝ)) outcome)
            (sample outcome) hsampleCount) arm} ≤
        law.real {outcome | ∃ pair : Arm × Arm,
          ¬ AdaptiveCompareStepCallValid observation
            (fixedSampleBudget 0 epsilon (eta / (Fintype.card (Arm × Arm) : ℝ)))
            preferenceGap epsilon (eta / (Fintype.card (Arm × Arm) : ℝ))
            outcome pair.2 pair.1} := by
          refine measureReal_mono (μ := law) ?_ (measure_ne_top law _)
          intro outcome hwinnerFailure
          by_contra hnoCallFailure
          apply hwinnerFailure
          refine pickAnchorSample_adaptiveSeqEliminate_epsilonMaximum_of_allPairCallValid
            (sample outcome) hsampleCount observation
            (fixedSampleBudget 0 epsilon (eta / (Fintype.card (Arm × Arm) : ℝ)))
            preferenceGap epsilon (eta / (Fintype.card (Arm × Arm) : ℝ)) outcome
            hantisymmetric hsst (le_of_lt hepsilon) ?_
            (maximum outcome) (hmaximumMem outcome) (hmaximum outcome)
          intro incumbent challenger
          by_contra hinvalid
          exact hnoCallFailure ⟨(challenger, incumbent), hinvalid⟩
    _ ≤ eta :=
      adaptiveCompare_allPairCallValid_failure_probability_of_ceilingBudget law
        observation preferenceGap epsilon eta hindependent hmeasurable hbounded hmean
        hantisymmetric hself hepsilon heta hetaLeOne

/--
The same sampled-winner failure bound with Appendix A.5's local `q*` obtained
internally from the complete SST model.  Thus a caller need not postulate a
sample-specific maximum selection function.
-/
theorem pickAnchorSample_adaptiveSeqEliminate_failure_probability_of_completeSST
    {Arm Ω : Type*} [MeasurableSpace Ω] [Fintype Arm] [DecidableEq Arm] [Nonempty Arm]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (observation : Arm → Arm → ℕ → Ω → ℝ)
    (preferenceGap : Arm → Arm → ℝ) (epsilon eta : ℝ)
    (hindependent : ∀ challenger incumbent,
      iIndepFun (observation challenger incumbent) law)
    (hmeasurable : ∀ challenger incumbent sampleIndex,
      Measurable (observation challenger incumbent sampleIndex))
    (hbounded : ∀ challenger incumbent,
      ∀ sampleIndex < fixedSampleBudget 0 epsilon (eta / (Fintype.card (Arm × Arm) : ℝ)),
        ∀ᵐ outcome ∂law, observation challenger incumbent sampleIndex outcome ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ challenger incumbent,
      ∀ sampleIndex < fixedSampleBudget 0 epsilon (eta / (Fintype.card (Arm × Arm) : ℝ)),
        law[observation challenger incumbent sampleIndex] =
          1 / 2 + preferenceGap challenger incumbent)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hself : ∀ arm, preferenceGap arm arm = 0)
    (hcomplete : PreferenceComplete preferenceGap)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hepsilon : 0 < epsilon)
    (heta : 0 < eta) (hetaLeOne : eta ≤ 1)
    {sampleCount : ℕ} (sample : Ω → finiteFreshList Arm sampleCount ∅)
    (hsampleCount : 0 < sampleCount) :
    law.real {outcome | ¬ ∀ arm ∈ pickAnchorSampleSet (sample outcome),
      -epsilon ≤ preferenceGap
        (pickAnchorSampleSeqEliminate
          (adaptiveCompareStep observation
            (fixedSampleBudget 0 epsilon (eta / (Fintype.card (Arm × Arm) : ℝ)))
            epsilon (eta / (Fintype.card (Arm × Arm) : ℝ)) outcome)
          (sample outcome) hsampleCount) arm} ≤ eta := by
  let maximum : Ω → Arm := fun outcome =>
    Classical.choose (exists_pickAnchorSample_localMaximum
      (sample outcome) hsampleCount preferenceGap hcomplete hsst)
  apply pickAnchorSample_adaptiveSeqEliminate_failure_probability_of_allPairBudget
    law observation preferenceGap epsilon eta hindependent hmeasurable hbounded hmean
    hantisymmetric hself hsst hepsilon heta hetaLeOne sample hsampleCount maximum
  · intro outcome
    exact (Classical.choose_spec (exists_pickAnchorSample_localMaximum
      (sample outcome) hsampleCount preferenceGap hcomplete hsst)).1
  · intro outcome arm harm
    exact (Classical.choose_spec (exists_pickAnchorSample_localMaximum
      (sample outcome) hsampleCount preferenceGap hcomplete hsst)).2 arm harm

/--
Appendix A.5's concrete sampled-winner half of Lemma 3.  The sample size uses
the source's `log (2 / δ)` rule while Seq-Eliminate receives confidence
`δ / 2`, exactly as Algorithm 5 invokes `Seq-Eliminate(Q, ε, 2δ)` in the
paper's inverse-confidence notation.
-/
theorem pickAnchorSource_sampleWinner_failure_probability_le_delta_half
    {Arm Ω : Type*} [MeasurableSpace Ω] [Fintype Arm] [DecidableEq Arm] [Nonempty Arm]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (cutoff : ℕ) (delta epsilon : ℝ)
    (observation : Arm → Arm → ℕ → Ω → ℝ)
    (preferenceGap : Arm → Arm → ℝ)
    (hindependent : ∀ challenger incumbent,
      iIndepFun (observation challenger incumbent) law)
    (hmeasurable : ∀ challenger incumbent sampleIndex,
      Measurable (observation challenger incumbent sampleIndex))
    (hbounded : ∀ challenger incumbent,
      ∀ sampleIndex < fixedSampleBudget 0 epsilon
          ((delta / 2) / (Fintype.card (Arm × Arm) : ℝ)),
        ∀ᵐ outcome ∂law, observation challenger incumbent sampleIndex outcome ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ challenger incumbent,
      ∀ sampleIndex < fixedSampleBudget 0 epsilon
          ((delta / 2) / (Fintype.card (Arm × Arm) : ℝ)),
        law[observation challenger incumbent sampleIndex] =
          1 / 2 + preferenceGap challenger incumbent)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hself : ∀ arm, preferenceGap arm arm = 0)
    (hcomplete : PreferenceComplete preferenceGap)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hcutoff : 0 < cutoff)
    (hepsilon : 0 < epsilon)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1)
    (sample : Ω → finiteFreshList Arm
      (pickAnchorSampleCount (Fintype.card Arm) cutoff delta) ∅) :
    law.real {outcome | ¬ ∀ arm ∈ pickAnchorSampleSet (sample outcome),
      -epsilon ≤ preferenceGap
        (pickAnchorSampleSeqEliminate
          (adaptiveCompareStep observation
            (fixedSampleBudget 0 epsilon
              ((delta / 2) / (Fintype.card (Arm × Arm) : ℝ)))
            epsilon ((delta / 2) / (Fintype.card (Arm × Arm) : ℝ)) outcome)
          (sample outcome)
          (pickAnchorSampleCount_pos (Fintype.card Arm) cutoff delta
            Fintype.card_pos hcutoff hdelta hdeltaLeOne)) arm} ≤ delta / 2 := by
  exact pickAnchorSample_adaptiveSeqEliminate_failure_probability_of_completeSST
    law observation preferenceGap epsilon (delta / 2)
    hindependent hmeasurable hbounded hmean hantisymmetric hself hcomplete hsst hepsilon
    (by positivity) (by linarith) sample
    (pickAnchorSampleCount_pos (Fintype.card Arm) cutoff delta
      Fintype.card_pos hcutoff hdelta hdeltaLeOne)

end FalahatgarEtAl2017MaxingRanking
