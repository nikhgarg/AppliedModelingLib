import AppliedModelingLib.Learning.ReinforcementLearning.Preference.IIDConcentration
import FalahatgarEtAl2017MaxingRanking.CoreDefinitions
import FalahatgarEtAl2017MaxingRanking.FixedSampleCompare
import FalahatgarEtAl2017MaxingRanking.SampleBudget
import FalahatgarEtAl2017MaxingRanking.AdaptiveCompareProbability
import FalahatgarEtAl2017MaxingRanking.OptMaximizeFinal

/-!
# OPT-Maximize final-check probability composition

This file formalizes Lemma 16's finite union-bound step independently of the
earlier Pick-Anchor and Prune analysis.
-/

namespace FalahatgarEtAl2017MaxingRanking

open AppliedModelingLib PreferenceRL
open MeasureTheory ProbabilityTheory

/-- The source's final loop: retain the anchor exactly when every test returns lower. -/
noncomputable def indexedFinalCheckOutput {Ω Arm : Type*}
    (callCount : ℕ) (anchor fallback : Arm)
    (decision : ℕ → Ω → CompareDecision) (outcome : Ω) : Arm :=
  if ∀ index < callCount, decision index outcome = .lower then anchor else fallback

/--
Lemma 16's union-bound form.  When `anchor` is already an `ε`-maximum, the
final loop returns an `ε`-maximum with probability at least one minus the
number of calls times their common failure budget.
-/
theorem indexedFinalCheck_epsilonMaximum_probability
    {Ω Arm : Type*} [MeasurableSpace Ω]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (callCount : ℕ) (anchor fallback : Arm)
    (decision : ℕ → Ω → CompareDecision) (preferenceGap : Arm → Arm → ℝ)
    (epsilon failureBudget : ℝ)
    (hmeasurable : ∀ index < callCount,
      MeasurableSet {outcome | decision index outcome = .lower})
    (hfailure : ∀ index < callCount,
      law.real {outcome | decision index outcome ≠ .lower} ≤ failureBudget)
    (hanchor : EpsilonMaximum preferenceGap epsilon anchor) :
    1 - (callCount : ℝ) * failureBudget ≤
      law.real {outcome |
        EpsilonMaximum preferenceGap epsilon
          (indexedFinalCheckOutput callCount anchor fallback decision outcome)} := by
  have hallGood := finiteSequential_goodEvent_probability law callCount
    (fun index outcome => decision index outcome = .lower) failureBudget
    hmeasurable hfailure
  calc
    1 - (callCount : ℝ) * failureBudget ≤
        law.real {outcome | ∀ index < callCount, decision index outcome = .lower} := hallGood
    _ ≤ law.real {outcome |
        EpsilonMaximum preferenceGap epsilon
          (indexedFinalCheckOutput callCount anchor fallback decision outcome)} := by
      refine measureReal_mono (μ := law) ?_ (measure_ne_top law _)
      intro outcome hall
      change ∀ index < callCount, decision index outcome = .lower at hall
      change EpsilonMaximum preferenceGap epsilon
        (indexedFinalCheckOutput callCount anchor fallback decision outcome)
      unfold indexedFinalCheckOutput
      rw [if_pos hall]
      exact hanchor

/-- The ceiling-budget fixed-sample Compare decision at one final-loop call. -/
noncomputable def fixedSampleFinalDecision {Ω : Type*}
    (observation : ℕ → ℕ → Ω → ℝ) (lower upper delta : ℝ)
    (call : ℕ) (outcome : Ω) : CompareDecision :=
  fixedSampleCompare (observation call) (fixedSampleBudget lower upper delta) lower upper outcome

/--
Lemma 16's fixed-schedule form with concrete Compare batches.  The source's
`2ε/3`-maximum anchor is an immediate instantiation with `lower = 2ε/3` and
`upper = ε`; this theorem retains the more general two-threshold statement.
-/
theorem fixedSampleFinalCheck_epsilonMaximum_probability
    {Ω Arm : Type*} [MeasurableSpace Ω]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (callCount : ℕ) (observation : ℕ → ℕ → Ω → ℝ)
    (anchor fallback : Arm) (preferenceGap : Arm → Arm → ℝ)
    (epsilon lower upper trueGap delta : ℝ)
    (hindependent : ∀ call < callCount, iIndepFun (observation call) law)
    (hmeasurable : ∀ call < callCount, ∀ sample,
      Measurable (observation call sample))
    (hbounded : ∀ call < callCount, ∀ sample < fixedSampleBudget lower upper delta,
      ∀ᵐ outcome ∂law, observation call sample outcome ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ call < callCount, ∀ sample < fixedSampleBudget lower upper delta,
      law[observation call sample] = 1 / 2 + trueGap)
    (hdecisionMeasurable : ∀ call < callCount,
      MeasurableSet {outcome |
        fixedSampleFinalDecision observation lower upper delta call outcome = .lower})
    (hgap : trueGap ≤ lower)
    (hseparation : lower < upper)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1)
    (hanchor : EpsilonMaximum preferenceGap epsilon anchor) :
    1 - (callCount : ℝ) * delta ≤
      law.real {outcome |
        EpsilonMaximum preferenceGap epsilon
          (indexedFinalCheckOutput callCount anchor fallback
            (fun call outcome =>
              fixedSampleFinalDecision observation lower upper delta call outcome)
            outcome)} := by
  apply indexedFinalCheck_epsilonMaximum_probability law callCount anchor fallback
    (fun call outcome => fixedSampleFinalDecision observation lower upper delta call outcome)
    preferenceGap epsilon delta hdecisionMeasurable
  · intro call hcall
    exact fixedSampleCompare_lower_failure_probability_of_ceilingBudget law
      (observation call) lower upper trueGap delta
      (hindependent call hcall) (hmeasurable call hcall)
      (hbounded call hcall) (hmean call hcall) hgap hseparation hdelta hdeltaLeOne
  · exact hanchor

/-- The adaptive Compare decision in the final OPT-Maximize loop. -/
noncomputable def adaptiveFinalDecision {Ω : Type*}
    (observation : ℕ → ℕ → Ω → ℝ) (lower upper delta : ℝ)
    (callCount call : ℕ) (outcome : Ω) : CompareDecision :=
  adaptiveCompare (observation call)
    (fixedSampleBudget lower upper (delta / (4 * (callCount : ℝ))))
    lower upper (delta / (4 * (callCount : ℝ))) outcome

/--
Lemma 16's concrete adaptive-Compare form.  Its `delta / (4 * callCount)`
allocation makes all lower decisions in the final loop fail with probability
at most `delta / 4`.
-/
theorem adaptiveFinalCheck_epsilonMaximum_probability
    {Ω Arm : Type*} [MeasurableSpace Ω]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (callCount : ℕ) (observation : ℕ → ℕ → Ω → ℝ)
    (anchor fallback : Arm) (preferenceGap : Arm → Arm → ℝ)
    (epsilon lower upper trueGap delta : ℝ)
    (hcallCount : 0 < callCount)
    (hindependent : ∀ call < callCount, iIndepFun (observation call) law)
    (hmeasurable : ∀ call < callCount, ∀ sample,
      Measurable (observation call sample))
    (hbounded : ∀ call < callCount,
      ∀ sample < fixedSampleBudget lower upper (delta / (4 * (callCount : ℝ))),
        ∀ᵐ outcome ∂law, observation call sample outcome ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ call < callCount,
      ∀ sample < fixedSampleBudget lower upper (delta / (4 * (callCount : ℝ))),
        law[observation call sample] = 1 / 2 + trueGap)
    (hdecisionMeasurable : ∀ call < callCount,
      MeasurableSet {outcome |
        adaptiveFinalDecision observation lower upper delta callCount call outcome = .lower})
    (hgap : trueGap ≤ lower)
    (hseparation : lower < upper)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1)
    (hanchor : EpsilonMaximum preferenceGap epsilon anchor) :
    1 - delta / 4 ≤
      law.real {outcome |
        EpsilonMaximum preferenceGap epsilon
          (indexedFinalCheckOutput callCount anchor fallback
            (fun call outcome =>
              adaptiveFinalDecision observation lower upper delta callCount call outcome)
            outcome)} := by
  have hcallCountReal : 0 < (callCount : ℝ) := by exact_mod_cast hcallCount
  have hdenominator : 0 < 4 * (callCount : ℝ) := mul_pos (by norm_num) hcallCountReal
  have hcallDeltaPos : 0 < delta / (4 * (callCount : ℝ)) :=
    div_pos hdelta hdenominator
  have hcallDeltaLeOne : delta / (4 * (callCount : ℝ)) ≤ 1 := by
    apply (div_le_iff₀ hdenominator).mpr
    have hdenominatorGeOne : 1 ≤ 4 * (callCount : ℝ) := by
      have hcountGeOne : 1 ≤ (callCount : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mpr hcallCount)
      nlinarith
    nlinarith
  have hperCall : ∀ call < callCount,
      law.real {outcome |
        adaptiveFinalDecision observation lower upper delta callCount call outcome ≠ .lower} ≤
        delta / (4 * (callCount : ℝ)) := by
    intro call hcall
    change law.real {outcome | adaptiveCompare (observation call)
      (fixedSampleBudget lower upper (delta / (4 * (callCount : ℝ)))) lower upper
      (delta / (4 * (callCount : ℝ))) outcome ≠ .lower} ≤
        delta / (4 * (callCount : ℝ))
    exact adaptiveCompare_lower_failure_probability_of_ceilingBudget law
      (observation call) lower upper trueGap (delta / (4 * (callCount : ℝ)))
      (hindependent call hcall) (hmeasurable call hcall)
      (hbounded call hcall) (hmean call hcall) hgap hseparation hcallDeltaPos hcallDeltaLeOne
  have hloop := indexedFinalCheck_epsilonMaximum_probability law callCount anchor fallback
    (fun call outcome => adaptiveFinalDecision observation lower upper delta callCount call outcome)
    preferenceGap epsilon (delta / (4 * (callCount : ℝ))) hdecisionMeasurable hperCall hanchor
  calc
    1 - delta / 4 = 1 - (callCount : ℝ) * (delta / (4 * (callCount : ℝ))) := by
      field_simp [ne_of_gt hcallCountReal]
    _ ≤ law.real {outcome |
      EpsilonMaximum preferenceGap epsilon
        (indexedFinalCheckOutput callCount anchor fallback
          (fun call outcome =>
            adaptiveFinalDecision observation lower upper delta callCount call outcome)
          outcome)} := hloop

/--
Lemma 18's detection branch: any probability bound for the absolute maximum's
upper decision transfers directly to the final OPT-Maximize output, provided
the fallback is an `ε`-winner of the pruned candidate set.
-/
theorem optMaximizeFinalOutput_failure_probability_of_maxDetection
    {Ω Arm : Type*} [MeasurableSpace Ω] [Fintype Arm] [DecidableEq Arm]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (preferenceGap : Arm → Arm → ℝ) (epsilon : ℝ)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hepsilon : 0 ≤ epsilon)
    (maximum anchor fallback : Arm) (candidates : Finset Arm)
    (decision : Arm → Ω → CompareDecision)
    (hmaximum : AbsoluteMaximum preferenceGap maximum)
    (hmaximumMem : maximum ∈ candidates)
    (hfallback : ∀ candidate ∈ candidates,
      -epsilon ≤ preferenceGap fallback candidate)
    (failureBudget : ℝ)
    (hdetectFailure : law.real {outcome | decision maximum outcome ≠ .upper} ≤ failureBudget) :
    law.real {outcome | ¬ EpsilonMaximum preferenceGap epsilon
      (optMaximizeFinalOutput anchor fallback candidates (fun candidate => decision candidate outcome))} ≤
      failureBudget := by
  have hsubset :
      {outcome | ¬ EpsilonMaximum preferenceGap epsilon
        (optMaximizeFinalOutput anchor fallback candidates (fun candidate => decision candidate outcome))} ⊆
        {outcome | decision maximum outcome ≠ .upper} := by
    intro outcome hfailure
    by_contra hnotDetect
    apply hfailure
    apply optMaximizeFinalOutput_epsilonMaximum_of_subsetWinner preferenceGap epsilon
      hantisymmetric hsst hepsilon maximum anchor fallback candidates
      (fun candidate => decision candidate outcome)
    · exact hmaximum
    · exact hmaximumMem
    · exact hfallback
    · intro _hstrict
      exact not_ne_iff.mp hnotDetect
  exact (measureReal_mono (μ := law) hsubset (measure_ne_top law _)).trans hdetectFailure

/--
The full Lemma 18 probability composition: final failure is contained in the
union of fallback-Seq-Eliminate failure and failure to detect the absolute
maximum.  No independence between those two phases is assumed.
-/
theorem optMaximizeFinalOutput_failure_probability_of_subsetWinner_and_maxDetection
    {Ω Arm : Type*} [MeasurableSpace Ω] [Fintype Arm] [DecidableEq Arm]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (preferenceGap : Arm → Arm → ℝ) (epsilon : ℝ)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hepsilon : 0 ≤ epsilon)
    (maximum anchor : Arm) (fallback : Ω → Arm) (candidates : Finset Arm)
    (decision : Arm → Ω → CompareDecision)
    (hmaximum : AbsoluteMaximum preferenceGap maximum)
    (hmaximumMem : maximum ∈ candidates)
    (fallbackFailure detectFailure : ℝ)
    (hfallbackFailure : law.real {outcome | ¬ ∀ candidate ∈ candidates,
      -epsilon ≤ preferenceGap (fallback outcome) candidate} ≤ fallbackFailure)
    (hdetectFailure : law.real {outcome | decision maximum outcome ≠ .upper} ≤ detectFailure) :
    law.real {outcome | ¬ EpsilonMaximum preferenceGap epsilon
      (optMaximizeFinalOutput anchor (fallback outcome) candidates
        (fun candidate => decision candidate outcome))} ≤
      fallbackFailure + detectFailure := by
  let fallbackBad : Set Ω := {outcome | ¬ ∀ candidate ∈ candidates,
    -epsilon ≤ preferenceGap (fallback outcome) candidate}
  let detectionBad : Set Ω := {outcome | decision maximum outcome ≠ .upper}
  have hsubset :
      {outcome | ¬ EpsilonMaximum preferenceGap epsilon
        (optMaximizeFinalOutput anchor (fallback outcome) candidates
          (fun candidate => decision candidate outcome))} ⊆
        fallbackBad ∪ detectionBad := by
    intro outcome hfailure
    by_cases hfallback : ∀ candidate ∈ candidates, -epsilon ≤ preferenceGap (fallback outcome) candidate
    · by_cases hdetect : decision maximum outcome = .upper
      · exact False.elim (hfailure
          (optMaximizeFinalOutput_epsilonMaximum_of_subsetWinner preferenceGap epsilon
            hantisymmetric hsst hepsilon maximum anchor (fallback outcome) candidates
            (fun candidate => decision candidate outcome) hmaximum hmaximumMem hfallback
            (fun _hstrict => hdetect)))
      · exact Or.inr hdetect
    · exact Or.inl hfallback
  calc
    law.real {outcome | ¬ EpsilonMaximum preferenceGap epsilon
        (optMaximizeFinalOutput anchor (fallback outcome) candidates
          (fun candidate => decision candidate outcome))} ≤
        law.real (fallbackBad ∪ detectionBad) :=
      measureReal_mono hsubset
    _ ≤ law.real fallbackBad + law.real detectionBad := measureReal_union_le _ _
    _ ≤ fallbackFailure + detectFailure := by
      dsimp [fallbackBad, detectionBad]
      linarith

/-- An `ε`-maximum failure bound immediately bounds failure to win a candidate subset. -/
theorem subsetWinner_failure_probability_of_epsilonMaximum
    {Ω Arm : Type*} [MeasurableSpace Ω] [DecidableEq Arm]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (preferenceGap : Arm → Arm → ℝ) (epsilon : ℝ)
    (fallback : Ω → Arm) (candidates : Finset Arm) (failureBudget : ℝ)
    (hfallback : law.real {outcome | ¬ EpsilonMaximum preferenceGap epsilon (fallback outcome)} ≤
      failureBudget) :
    law.real {outcome | ¬ ∀ candidate ∈ candidates,
      -epsilon ≤ preferenceGap (fallback outcome) candidate} ≤ failureBudget := by
  apply (measureReal_mono (μ := law) ?_ (measure_ne_top law _)).trans hfallback
  intro outcome hfailure
  by_contra hmaximum
  apply hfailure
  have hmaximum' : EpsilonMaximum preferenceGap epsilon (fallback outcome) := not_not.mp hmaximum
  intro candidate hcandidate
  exact hmaximum' candidate

/--
Lemma 18's endgame expressed directly in terms of the preceding
Seq-Eliminate output: if that (possibly random) fallback is an `ε`-maximum
except on a small event, the final maximum-detection check adds only its own
failure probability.  The two phases need not be independent.
-/
theorem optMaximizeFinalOutput_failure_probability_of_epsilonMaximum_and_maxDetection
    {Ω Arm : Type*} [MeasurableSpace Ω] [Fintype Arm] [DecidableEq Arm]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (preferenceGap : Arm → Arm → ℝ) (epsilon : ℝ)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hepsilon : 0 ≤ epsilon)
    (maximum anchor : Arm) (fallback : Ω → Arm) (candidates : Finset Arm)
    (decision : Arm → Ω → CompareDecision)
    (hmaximum : AbsoluteMaximum preferenceGap maximum)
    (hmaximumMem : maximum ∈ candidates)
    (fallbackFailure detectFailure : ℝ)
    (hfallback : law.real {outcome | ¬ EpsilonMaximum preferenceGap epsilon (fallback outcome)} ≤
      fallbackFailure)
    (hdetectFailure : law.real {outcome | decision maximum outcome ≠ .upper} ≤ detectFailure) :
    law.real {outcome | ¬ EpsilonMaximum preferenceGap epsilon
      (optMaximizeFinalOutput anchor (fallback outcome) candidates
        (fun candidate => decision candidate outcome))} ≤
      fallbackFailure + detectFailure := by
  apply optMaximizeFinalOutput_failure_probability_of_subsetWinner_and_maxDetection
    law preferenceGap epsilon hantisymmetric hsst hepsilon maximum anchor fallback candidates
    decision hmaximum hmaximumMem fallbackFailure detectFailure
  · exact subsetWinner_failure_probability_of_epsilonMaximum law preferenceGap epsilon
      fallback candidates fallbackFailure hfallback
  · exact hdetectFailure

/--
Lemma 18 with the source's adaptive Compare detector for the absolute maximum.
The remaining OPT-Maximize proof need only establish the earlier candidate-set
and fallback premises visible below.
-/
theorem adaptiveOptMaximizeFinalOutput_failure_probability
    {Ω Arm : Type*} [MeasurableSpace Ω] [Fintype Arm] [DecidableEq Arm]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (observation : Arm → ℕ → Ω → ℝ)
    (preferenceGap : Arm → Arm → ℝ) (epsilon : ℝ)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hepsilon : 0 ≤ epsilon)
    (maximum anchor fallback : Arm) (candidates : Finset Arm)
    (lower upper trueGap delta : ℝ)
    (hmaximum : AbsoluteMaximum preferenceGap maximum)
    (hmaximumMem : maximum ∈ candidates)
    (hfallback : ∀ candidate ∈ candidates,
      -epsilon ≤ preferenceGap fallback candidate)
    (hindependent : iIndepFun (observation maximum) law)
    (hmeasurable : ∀ sample, Measurable (observation maximum sample))
    (hbounded : ∀ sample < fixedSampleBudget lower upper delta,
      ∀ᵐ outcome ∂law, observation maximum sample outcome ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ sample < fixedSampleBudget lower upper delta,
      law[observation maximum sample] = 1 / 2 + trueGap)
    (hgap : upper ≤ trueGap) (hseparation : lower < upper)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    law.real {outcome | ¬ EpsilonMaximum preferenceGap epsilon
      (optMaximizeFinalOutput anchor fallback candidates
        (fun candidate => adaptiveCompare (observation candidate)
          (fixedSampleBudget lower upper delta) lower upper delta outcome))} ≤ delta := by
  apply optMaximizeFinalOutput_failure_probability_of_maxDetection law preferenceGap epsilon
    hantisymmetric hsst hepsilon maximum anchor fallback candidates
    (fun candidate outcome => adaptiveCompare (observation candidate)
      (fixedSampleBudget lower upper delta) lower upper delta outcome)
    hmaximum hmaximumMem hfallback delta
  exact adaptiveCompare_upper_failure_probability_of_ceilingBudget law
    (observation maximum) lower upper trueGap delta hindependent hmeasurable hbounded hmean
    hgap hseparation hdelta hdeltaLeOne

/--
The random-fallback version of Lemma 18's final detector.  This is the form
used after Seq-Eliminate runs on the pruned candidate set: its failure budget
and the final Compare budget add, without any phase-independence hypothesis.
-/
theorem adaptiveOptMaximizeFinalOutput_failure_probability_of_epsilonMaximum
    {Ω Arm : Type*} [MeasurableSpace Ω] [Fintype Arm] [DecidableEq Arm]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (observation : Arm → ℕ → Ω → ℝ)
    (preferenceGap : Arm → Arm → ℝ) (epsilon : ℝ)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hepsilon : 0 ≤ epsilon)
    (maximum anchor : Arm) (fallback : Ω → Arm) (candidates : Finset Arm)
    (lower upper trueGap delta : ℝ)
    (hmaximum : AbsoluteMaximum preferenceGap maximum)
    (hmaximumMem : maximum ∈ candidates)
    (fallbackFailure : ℝ)
    (hfallback : law.real {outcome | ¬ EpsilonMaximum preferenceGap epsilon (fallback outcome)} ≤
      fallbackFailure)
    (hindependent : iIndepFun (observation maximum) law)
    (hmeasurable : ∀ sample, Measurable (observation maximum sample))
    (hbounded : ∀ sample < fixedSampleBudget lower upper delta,
      ∀ᵐ outcome ∂law, observation maximum sample outcome ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ sample < fixedSampleBudget lower upper delta,
      law[observation maximum sample] = 1 / 2 + trueGap)
    (hgap : upper ≤ trueGap) (hseparation : lower < upper)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    law.real {outcome | ¬ EpsilonMaximum preferenceGap epsilon
      (optMaximizeFinalOutput anchor (fallback outcome) candidates
        (fun candidate => adaptiveCompare (observation candidate)
          (fixedSampleBudget lower upper delta) lower upper delta outcome))} ≤
      fallbackFailure + delta := by
  apply optMaximizeFinalOutput_failure_probability_of_epsilonMaximum_and_maxDetection
    law preferenceGap epsilon hantisymmetric hsst hepsilon maximum anchor fallback candidates
    (fun candidate outcome => adaptiveCompare (observation candidate)
      (fixedSampleBudget lower upper delta) lower upper delta outcome)
    hmaximum hmaximumMem fallbackFailure delta hfallback
  exact adaptiveCompare_upper_failure_probability_of_ceilingBudget law
    (observation maximum) lower upper trueGap delta hindependent hmeasurable hbounded hmean
    hgap hseparation hdelta hdeltaLeOne

/--
The final detector need only be charged on the branch where the anchor is not
an `ε`-maximum.  On an already-adequate anchor that branch is empty; otherwise
SST makes the absolute maximum's gap exceed `ε`, which is enough for the
adaptive Compare upper-decision guarantee.
-/
theorem adaptiveMaximumDetection_failure_probability
    {Ω Arm : Type*} [MeasurableSpace Ω] [Fintype Arm] [DecidableEq Arm]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (observation : Arm → ℕ → Ω → ℝ)
    (preferenceGap : Arm → Arm → ℝ) (epsilon : ℝ)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hepsilon : 0 ≤ epsilon)
    (maximum anchor : Arm) (lower upper trueGap delta : ℝ)
    (hmaximum : AbsoluteMaximum preferenceGap maximum)
    (hindependent : iIndepFun (observation maximum) law)
    (hmeasurable : ∀ sample, Measurable (observation maximum sample))
    (hbounded : ∀ sample < fixedSampleBudget lower upper delta,
      ∀ᵐ outcome ∂law, observation maximum sample outcome ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ sample < fixedSampleBudget lower upper delta,
      law[observation maximum sample] = 1 / 2 + trueGap)
    (htrueGap : trueGap = preferenceGap maximum anchor)
    (hdetectorUpper : upper ≤ epsilon) (hseparation : lower < upper)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    law.real {outcome | epsilon < preferenceGap maximum anchor ∧
      adaptiveCompare (observation maximum) (fixedSampleBudget lower upper delta)
        lower upper delta outcome ≠ .upper} ≤ delta := by
  by_cases hanchorMaximum : EpsilonMaximum preferenceGap epsilon anchor
  · have hnotStrict : ¬ epsilon < preferenceGap maximum anchor := by
      intro hstrict
      have hanchorBound := hanchorMaximum maximum
      rw [hantisymmetric maximum anchor] at hanchorBound
      linarith
    have hempty : {outcome | epsilon < preferenceGap maximum anchor ∧
        adaptiveCompare (observation maximum) (fixedSampleBudget lower upper delta)
          lower upper delta outcome ≠ .upper} = ∅ := by
      ext outcome
      simp [hnotStrict]
    rw [hempty]
    simpa using (le_of_lt hdelta)
  · have hstrict : epsilon < preferenceGap maximum anchor :=
      absoluteMaximum_gap_gt_of_not_epsilonMaximum preferenceGap epsilon hantisymmetric hsst
        hepsilon maximum anchor hmaximum hanchorMaximum
    have hgap : upper ≤ trueGap := by
      rw [htrueGap]
      linarith
    calc
      law.real {outcome | epsilon < preferenceGap maximum anchor ∧
          adaptiveCompare (observation maximum) (fixedSampleBudget lower upper delta)
            lower upper delta outcome ≠ .upper} ≤
          law.real {outcome | adaptiveCompare (observation maximum)
            (fixedSampleBudget lower upper delta) lower upper delta outcome ≠ .upper} := by
              refine measureReal_mono (μ := law) ?_ (measure_ne_top law _)
              intro outcome hfailure
              exact hfailure.2
      _ ≤ delta :=
        adaptiveCompare_upper_failure_probability_of_ceilingBudget law
          (observation maximum) lower upper trueGap delta hindependent hmeasurable hbounded hmean
          hgap hseparation hdelta hdeltaLeOne

end FalahatgarEtAl2017MaxingRanking
