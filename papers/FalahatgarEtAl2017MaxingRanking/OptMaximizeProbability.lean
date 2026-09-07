import FalahatgarEtAl2017MaxingRanking.FinalCheckProbability
import FalahatgarEtAl2017MaxingRanking.AdaptiveSeqEliminateProbability
import FalahatgarEtAl2017MaxingRanking.PruneProbability

/-!
# OPT-Maximize probability composition with a random pruned set

The source's three phases share randomness through their observed comparisons.
This file uses event containment and union bounds, rather than an unjustified
independence assumption between Pick-Anchor, Prune, and Seq-Eliminate.
-/

namespace FalahatgarEtAl2017MaxingRanking

open AppliedModelingLib PreferenceRL
open MeasureTheory ProbabilityTheory

/--
The source Theorem-6 branch composition.  A failed final output is charged
only to one of four source events: an erroneous upper decision when the anchor
is already an `anchorError`-maximum, loss of the absolute maximum when it is
not, failure of the fallback on a retained maximum, or failure to detect that
maximum when the anchor is not an `epsilon`-maximum.  No independence between
these events is used.
-/
theorem optMaximizeFinalOutput_failure_probability_of_anchor_or_candidate
    {Ω Arm : Type*} [MeasurableSpace Ω] [Fintype Arm] [DecidableEq Arm]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (preferenceGap : Arm → Arm → ℝ) (anchorError epsilon : ℝ)
    (hanchorError : anchorError ≤ epsilon)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hepsilon : 0 ≤ epsilon)
    (maximum anchor : Arm) (fallback : Ω → Arm) (candidates : Ω → Finset Arm)
    (decision : Arm → Ω → CompareDecision)
    (hmaximum : AbsoluteMaximum preferenceGap maximum)
    (anchorTestFailure candidateFailure fallbackFailure detectFailure : ℝ)
    (hanchorTestFailure : law.real {outcome |
      EpsilonMaximum preferenceGap anchorError anchor ∧
        ∃ candidate ∈ candidates outcome, decision candidate outcome = .upper} ≤ anchorTestFailure)
    (hcandidateFailure : law.real {outcome |
      ¬ EpsilonMaximum preferenceGap anchorError anchor ∧ maximum ∉ candidates outcome} ≤
        candidateFailure)
    (hfallbackFailure : law.real {outcome |
      maximum ∈ candidates outcome ∧
        ¬ ∀ candidate ∈ candidates outcome,
          -epsilon ≤ preferenceGap (fallback outcome) candidate} ≤ fallbackFailure)
    (hdetectFailure : law.real {outcome |
      epsilon < preferenceGap maximum anchor ∧ decision maximum outcome ≠ .upper} ≤ detectFailure) :
    law.real {outcome | ¬ EpsilonMaximum preferenceGap epsilon
      (optMaximizeFinalOutput anchor (fallback outcome) (candidates outcome)
        (fun candidate => decision candidate outcome))} ≤
      anchorTestFailure + candidateFailure + fallbackFailure + detectFailure := by
  let anchorTestBad : Set Ω := {outcome |
    EpsilonMaximum preferenceGap anchorError anchor ∧
      ∃ candidate ∈ candidates outcome, decision candidate outcome = .upper}
  let candidateBad : Set Ω := {outcome |
    ¬ EpsilonMaximum preferenceGap anchorError anchor ∧ maximum ∉ candidates outcome}
  let fallbackBad : Set Ω := {outcome |
    maximum ∈ candidates outcome ∧
      ¬ ∀ candidate ∈ candidates outcome,
        -epsilon ≤ preferenceGap (fallback outcome) candidate}
  let detectionBad : Set Ω := {outcome |
    epsilon < preferenceGap maximum anchor ∧ decision maximum outcome ≠ .upper}
  have hsubset :
      {outcome | ¬ EpsilonMaximum preferenceGap epsilon
        (optMaximizeFinalOutput anchor (fallback outcome) (candidates outcome)
          (fun candidate => decision candidate outcome))} ⊆
        ((anchorTestBad ∪ candidateBad) ∪ fallbackBad) ∪ detectionBad := by
    intro outcome hfailure
    by_cases hanchor : EpsilonMaximum preferenceGap anchorError anchor
    · by_cases hupper : ∃ candidate ∈ candidates outcome,
        decision candidate outcome = .upper
      · exact Or.inl (Or.inl (Or.inl ⟨hanchor, hupper⟩))
      · exfalso
        apply hfailure
        unfold optMaximizeFinalOutput
        rw [if_neg hupper]
        exact epsilonMaximum_mono preferenceGap anchorError epsilon anchor hanchor hanchorError
    · by_cases hmaximumMem : maximum ∈ candidates outcome
      · by_cases hfallback : ∀ candidate ∈ candidates outcome,
          -epsilon ≤ preferenceGap (fallback outcome) candidate
        · by_cases hstrict : epsilon < preferenceGap maximum anchor
          · by_cases hdetect : decision maximum outcome = .upper
            · exfalso
              apply hfailure
              exact optMaximizeFinalOutput_epsilonMaximum_of_subsetWinner preferenceGap epsilon
                hantisymmetric hsst hepsilon maximum anchor (fallback outcome) (candidates outcome)
                (fun candidate => decision candidate outcome) hmaximum hmaximumMem hfallback
                (fun _ => hdetect)
            · exact Or.inr ⟨hstrict, hdetect⟩
          · exfalso
            apply hfailure
            exact optMaximizeFinalOutput_epsilonMaximum_of_subsetWinner preferenceGap epsilon
              hantisymmetric hsst hepsilon maximum anchor (fallback outcome) (candidates outcome)
              (fun candidate => decision candidate outcome) hmaximum hmaximumMem hfallback
              (fun hneeded => False.elim (hstrict hneeded))
        · exact Or.inl (Or.inr ⟨hmaximumMem, hfallback⟩)
      · exact Or.inl (Or.inl (Or.inr ⟨hanchor, hmaximumMem⟩))
  calc
    law.real {outcome | ¬ EpsilonMaximum preferenceGap epsilon
        (optMaximizeFinalOutput anchor (fallback outcome) (candidates outcome)
          (fun candidate => decision candidate outcome))} ≤
        law.real (((anchorTestBad ∪ candidateBad) ∪ fallbackBad) ∪ detectionBad) :=
      measureReal_mono hsubset
    _ ≤ law.real ((anchorTestBad ∪ candidateBad) ∪ fallbackBad) +
        law.real detectionBad := measureReal_union_le _ _
    _ ≤ law.real (anchorTestBad ∪ candidateBad) + law.real fallbackBad +
        law.real detectionBad := by
      have hunion := measureReal_union_le (μ := law) (anchorTestBad ∪ candidateBad) fallbackBad
      linarith
    _ ≤ law.real anchorTestBad + law.real candidateBad + law.real fallbackBad +
        law.real detectionBad := by
      have hunion := measureReal_union_le (μ := law) anchorTestBad candidateBad
      linarith
    _ ≤ anchorTestFailure + candidateFailure + fallbackFailure + detectFailure := by
      dsimp [anchorTestBad, candidateBad, fallbackBad, detectionBad]
      linarith

/--
On candidate sets that contain the absolute maximum, a global
`ε`-maximum guarantee for the Seq-Eliminate fallback gives the subset-winner
guarantee required by Lemma 18.
-/
theorem adaptiveSeqEliminate_candidateContainsMax_subsetWinner_failure_probability
    {Ω Arm : Type*} [MeasurableSpace Ω] [Fintype Arm] [DecidableEq Arm] [Nonempty Arm]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (observation : Arm → Arm → ℕ → Ω → ℝ)
    (preferenceGap : Arm → Arm → ℝ) (epsilon delta : ℝ)
    (hindependent : ∀ challenger incumbent,
      iIndepFun (observation challenger incumbent) law)
    (hmeasurable : ∀ challenger incumbent sample,
      Measurable (observation challenger incumbent sample))
    (hbounded : ∀ challenger incumbent,
      ∀ sample < fixedSampleBudget 0 epsilon (delta / (Fintype.card (Arm × Arm) : ℝ)),
        ∀ᵐ outcome ∂law, observation challenger incumbent sample outcome ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ challenger incumbent,
      ∀ sample < fixedSampleBudget 0 epsilon (delta / (Fintype.card (Arm × Arm) : ℝ)),
        law[observation challenger incumbent sample] =
          1 / 2 + preferenceGap challenger incumbent)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hself : ∀ arm, preferenceGap arm arm = 0)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hepsilon : 0 < epsilon)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1)
    (maximum : Arm) (candidates : Ω → Finset Arm)
    (initial : Ω → Arm) (challengers : Ω → List Arm)
    (henumerates : ∀ outcome, maximum ∈ candidates outcome →
      initial outcome :: challengers outcome = (candidates outcome).toList)
    (hmaximum : AbsoluteMaximum preferenceGap maximum) :
    law.real {outcome | maximum ∈ candidates outcome ∧
      ¬ ∀ candidate ∈ candidates outcome,
        -epsilon ≤ preferenceGap
          (sequentialEliminate
            (adaptiveCompareStep observation
              (fixedSampleBudget 0 epsilon (delta / (Fintype.card (Arm × Arm) : ℝ)))
              epsilon (delta / (Fintype.card (Arm × Arm) : ℝ)) outcome)
            (initial outcome) (challengers outcome)) candidate} ≤ delta := by
  calc
    law.real {outcome | maximum ∈ candidates outcome ∧
        ¬ ∀ candidate ∈ candidates outcome,
          -epsilon ≤ preferenceGap
            (sequentialEliminate
              (adaptiveCompareStep observation
                (fixedSampleBudget 0 epsilon (delta / (Fintype.card (Arm × Arm) : ℝ)))
                epsilon (delta / (Fintype.card (Arm × Arm) : ℝ)) outcome)
              (initial outcome) (challengers outcome)) candidate} ≤
        law.real {outcome | maximum ∈ candidates outcome ∧
          ¬ EpsilonMaximum preferenceGap epsilon
            (sequentialEliminate
              (adaptiveCompareStep observation
                (fixedSampleBudget 0 epsilon (delta / (Fintype.card (Arm × Arm) : ℝ)))
                epsilon (delta / (Fintype.card (Arm × Arm) : ℝ)) outcome)
              (initial outcome) (challengers outcome))} := by
                refine measureReal_mono (μ := law) ?_ (measure_ne_top law _)
                intro outcome hfailure
                rcases hfailure with ⟨hmaximumMem, hsubsetFailure⟩
                refine ⟨hmaximumMem, ?_⟩
                by_contra hnotMaximum
                apply hsubsetFailure
                have hfallbackMaximum : EpsilonMaximum preferenceGap epsilon
                    (sequentialEliminate
                      (adaptiveCompareStep observation
                        (fixedSampleBudget 0 epsilon (delta / (Fintype.card (Arm × Arm) : ℝ)))
                        epsilon (delta / (Fintype.card (Arm × Arm) : ℝ)) outcome)
                      (initial outcome) (challengers outcome)) := hnotMaximum
                intro candidate _hcandidate
                exact hfallbackMaximum candidate
    _ ≤ delta :=
      adaptiveSeqEliminate_candidateContainsMax_failure_probability_of_ceilingBudget law
        observation preferenceGap epsilon delta hindependent hmeasurable hbounded hmean
        hantisymmetric hself hsst hepsilon hdelta hdeltaLeOne maximum candidates initial challengers
        henumerates hmaximum

/--
Lemma 18 with a random pruned candidate set.  The output can fail only if
Prune loses the absolute maximum, the fallback fails to win that retained set,
or the final test misses the maximum.  The bound is purely a union bound.
-/
theorem optMaximizeFinalOutput_failure_probability_of_dynamicCandidates
    {Ω Arm : Type*} [MeasurableSpace Ω] [Fintype Arm] [DecidableEq Arm]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (preferenceGap : Arm → Arm → ℝ) (epsilon : ℝ)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hepsilon : 0 ≤ epsilon)
    (maximum anchor : Arm) (fallback : Ω → Arm) (candidates : Ω → Finset Arm)
    (decision : Arm → Ω → CompareDecision)
    (hmaximum : AbsoluteMaximum preferenceGap maximum)
    (candidateFailure fallbackFailure detectFailure : ℝ)
    (hcandidateFailure : law.real {outcome | maximum ∉ candidates outcome} ≤ candidateFailure)
    (hfallbackFailure : law.real {outcome | maximum ∈ candidates outcome ∧
      ¬ ∀ candidate ∈ candidates outcome,
        -epsilon ≤ preferenceGap (fallback outcome) candidate} ≤ fallbackFailure)
    (hdetectFailure : law.real {outcome |
      epsilon < preferenceGap maximum anchor ∧ decision maximum outcome ≠ .upper} ≤ detectFailure) :
    law.real {outcome | ¬ EpsilonMaximum preferenceGap epsilon
      (optMaximizeFinalOutput anchor (fallback outcome) (candidates outcome)
        (fun candidate => decision candidate outcome))} ≤
      candidateFailure + fallbackFailure + detectFailure := by
  let candidateBad : Set Ω := {outcome | maximum ∉ candidates outcome}
  let fallbackBad : Set Ω := {outcome | maximum ∈ candidates outcome ∧
    ¬ ∀ candidate ∈ candidates outcome,
      -epsilon ≤ preferenceGap (fallback outcome) candidate}
  let detectionBad : Set Ω := {outcome |
    epsilon < preferenceGap maximum anchor ∧ decision maximum outcome ≠ .upper}
  have hsubset :
      {outcome | ¬ EpsilonMaximum preferenceGap epsilon
        (optMaximizeFinalOutput anchor (fallback outcome) (candidates outcome)
          (fun candidate => decision candidate outcome))} ⊆
        candidateBad ∪ fallbackBad ∪ detectionBad := by
    intro outcome hfailure
    dsimp only [candidateBad, fallbackBad, detectionBad]
    simp only [Set.mem_union, Set.mem_setOf_eq]
    by_cases hmaximumMem : maximum ∈ candidates outcome
    · by_cases hfallback : ∀ candidate ∈ candidates outcome,
        -epsilon ≤ preferenceGap (fallback outcome) candidate
      · by_cases hstrict : epsilon < preferenceGap maximum anchor
        · by_cases hdetect : decision maximum outcome = .upper
          · exact False.elim (hfailure
              (optMaximizeFinalOutput_epsilonMaximum_of_subsetWinner preferenceGap epsilon
                hantisymmetric hsst hepsilon maximum anchor (fallback outcome) (candidates outcome)
                (fun candidate => decision candidate outcome) hmaximum hmaximumMem hfallback
                (fun _hstrict => hdetect)))
          · exact Or.inr ⟨hstrict, hdetect⟩
        · exact False.elim (hfailure
            (optMaximizeFinalOutput_epsilonMaximum_of_subsetWinner preferenceGap epsilon
              hantisymmetric hsst hepsilon maximum anchor (fallback outcome) (candidates outcome)
              (fun candidate => decision candidate outcome) hmaximum hmaximumMem hfallback
              (fun hneeded => False.elim (hstrict hneeded))))
      · exact Or.inl (Or.inr ⟨hmaximumMem, hfallback⟩)
    · exact Or.inl (Or.inl hmaximumMem)
  calc
    law.real {outcome | ¬ EpsilonMaximum preferenceGap epsilon
        (optMaximizeFinalOutput anchor (fallback outcome) (candidates outcome)
          (fun candidate => decision candidate outcome))} ≤
        law.real (candidateBad ∪ fallbackBad ∪ detectionBad) :=
      measureReal_mono hsubset
    _ ≤ law.real (candidateBad ∪ fallbackBad) + law.real detectionBad :=
      measureReal_union_le _ _
    _ ≤ law.real candidateBad + law.real fallbackBad + law.real detectionBad := by
      have hfirst := measureReal_union_le (μ := law) candidateBad fallbackBad
      linarith
    _ ≤ candidateFailure + fallbackFailure + detectFailure := by
      dsimp [candidateBad, fallbackBad, detectionBad]
      linarith

/--
The concrete OPT-Maximize endgame after a randomized Prune output.  It joins
Prune's maximum-retention bound, the simultaneous adaptive Seq-Eliminate
bound, and any final-maximum detection bound.  Each component remains an
explicit hypothesis because the source assigns them to different subroutines.
-/
theorem optMaximizeFinalOutput_failure_probability_of_adaptiveSeqEliminate
    {Ω Arm : Type*} [MeasurableSpace Ω] [Fintype Arm] [DecidableEq Arm] [Nonempty Arm]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (observation : Arm → Arm → ℕ → Ω → ℝ)
    (preferenceGap : Arm → Arm → ℝ) (epsilon delta : ℝ)
    (hindependent : ∀ challenger incumbent,
      iIndepFun (observation challenger incumbent) law)
    (hmeasurable : ∀ challenger incumbent sample,
      Measurable (observation challenger incumbent sample))
    (hbounded : ∀ challenger incumbent,
      ∀ sample < fixedSampleBudget 0 epsilon (delta / (Fintype.card (Arm × Arm) : ℝ)),
        ∀ᵐ outcome ∂law, observation challenger incumbent sample outcome ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ challenger incumbent,
      ∀ sample < fixedSampleBudget 0 epsilon (delta / (Fintype.card (Arm × Arm) : ℝ)),
        law[observation challenger incumbent sample] =
          1 / 2 + preferenceGap challenger incumbent)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hself : ∀ arm, preferenceGap arm arm = 0)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hepsilon : 0 < epsilon)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1)
    (maximum anchor : Arm) (candidates : Ω → Finset Arm)
    (initial : Ω → Arm) (challengers : Ω → List Arm)
    (henumerates : ∀ outcome, maximum ∈ candidates outcome →
      initial outcome :: challengers outcome = (candidates outcome).toList)
    (decision : Arm → Ω → CompareDecision)
    (hmaximum : AbsoluteMaximum preferenceGap maximum)
    (candidateFailure detectFailure : ℝ)
    (hcandidateFailure : law.real {outcome | maximum ∉ candidates outcome} ≤ candidateFailure)
    (hdetectFailure : law.real {outcome |
      epsilon < preferenceGap maximum anchor ∧ decision maximum outcome ≠ .upper} ≤ detectFailure) :
    law.real {outcome | ¬ EpsilonMaximum preferenceGap epsilon
      (optMaximizeFinalOutput anchor
        (sequentialEliminate
          (adaptiveCompareStep observation
            (fixedSampleBudget 0 epsilon (delta / (Fintype.card (Arm × Arm) : ℝ)))
            epsilon (delta / (Fintype.card (Arm × Arm) : ℝ)) outcome)
          (initial outcome) (challengers outcome))
        (candidates outcome) (fun candidate => decision candidate outcome))} ≤
      candidateFailure + delta + detectFailure := by
  apply optMaximizeFinalOutput_failure_probability_of_dynamicCandidates law
    preferenceGap epsilon hantisymmetric hsst (le_of_lt hepsilon) maximum anchor
    (fun outcome => sequentialEliminate
      (adaptiveCompareStep observation
        (fixedSampleBudget 0 epsilon (delta / (Fintype.card (Arm × Arm) : ℝ)))
        epsilon (delta / (Fintype.card (Arm × Arm) : ℝ)) outcome)
      (initial outcome) (challengers outcome)) candidates decision hmaximum
    candidateFailure delta detectFailure hcandidateFailure
  · exact adaptiveSeqEliminate_candidateContainsMax_subsetWinner_failure_probability law
      observation preferenceGap epsilon delta hindependent hmeasurable hbounded hmean
      hantisymmetric hself hsst hepsilon hdelta hdeltaLeOne maximum candidates initial challengers
      henumerates hmaximum
  · exact hdetectFailure

/--
OPT-Maximize's non-`upper`-maximum branch with the source's adaptive Prune
schedule.  The candidate-loss term is discharged by Lemma 13's protected
absolute-maximum argument; the remaining two terms are adaptive
Seq-Eliminate and final-detection failures.
-/
theorem optMaximizeFinalOutput_failure_probability_of_adaptivePrune_and_adaptiveSeqEliminate
    {Ω Arm : Type*} [MeasurableSpace Ω] [Fintype Arm] [DecidableEq Arm] [Nonempty Arm]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (seqObservation : Arm → Arm → ℕ → Ω → ℝ)
    (pruneObservation : ℕ → Arm → ℕ → Ω → ℝ)
    (preferenceGap : Arm → Arm → ℝ) (epsilon seqDelta : ℝ)
    (hindependent : ∀ challenger incumbent,
      iIndepFun (seqObservation challenger incumbent) law)
    (hmeasurable : ∀ challenger incumbent sample,
      Measurable (seqObservation challenger incumbent sample))
    (hbounded : ∀ challenger incumbent,
      ∀ sample < fixedSampleBudget 0 epsilon
        (seqDelta / (Fintype.card (Arm × Arm) : ℝ)),
        ∀ᵐ outcome ∂law, seqObservation challenger incumbent sample outcome ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ challenger incumbent,
      ∀ sample < fixedSampleBudget 0 epsilon
        (seqDelta / (Fintype.card (Arm × Arm) : ℝ)),
        law[seqObservation challenger incumbent sample] =
          1 / 2 + preferenceGap challenger incumbent)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hself : ∀ arm, preferenceGap arm arm = 0)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hepsilon : 0 < epsilon)
    (hseqDelta : 0 < seqDelta) (hseqDeltaLeOne : seqDelta ≤ 1)
    (roundCount : ℕ) (active : Finset Arm) (maximum anchor : Arm)
    (lower upper pruneDelta : ℝ)
    (hupperNonnegative : 0 ≤ upper)
    (hmaximum : AbsoluteMaximum preferenceGap maximum)
    (hmaximumMem : maximum ∈ active)
    (hanchorNotMaximum : ¬ EpsilonMaximum preferenceGap upper anchor)
    (hpruneIndependent : ∀ round < roundCount,
      iIndepFun (pruneObservation round maximum) law)
    (hpruneMeasurable : ∀ round < roundCount, ∀ sample,
      Measurable (pruneObservation round maximum sample))
    (hpruneBounded : ∀ round < roundCount,
      ∀ sample < fixedSampleBudget lower upper (adaptivePruneRoundDelta pruneDelta round),
        ∀ᵐ outcome ∂law,
          pruneObservation round maximum sample outcome ∈ Set.Icc (0 : ℝ) 1)
    (hpruneMean : ∀ round < roundCount,
      ∀ sample < fixedSampleBudget lower upper (adaptivePruneRoundDelta pruneDelta round),
        law[pruneObservation round maximum sample] =
          1 / 2 + preferenceGap maximum anchor)
    (hpruneSeparation : lower < upper)
    (hpruneDelta : 0 < pruneDelta) (hpruneDeltaLeOne : pruneDelta ≤ 1)
    (initial : Ω → Arm) (challengers : Ω → List Arm)
    (henumerates : ∀ outcome,
      maximum ∈ indexedPruneRounds roundCount
        (adaptivePruneDecision pruneObservation lower upper pruneDelta) outcome active →
      initial outcome :: challengers outcome =
        (indexedPruneRounds roundCount
          (adaptivePruneDecision pruneObservation lower upper pruneDelta) outcome active).toList)
    (decision : Arm → Ω → CompareDecision) (detectFailure : ℝ)
    (hdetectFailure : law.real {outcome |
      epsilon < preferenceGap maximum anchor ∧ decision maximum outcome ≠ .upper} ≤ detectFailure) :
    law.real {outcome | ¬ EpsilonMaximum preferenceGap epsilon
      (optMaximizeFinalOutput anchor
        (sequentialEliminate
          (adaptiveCompareStep seqObservation
            (fixedSampleBudget 0 epsilon
              (seqDelta / (Fintype.card (Arm × Arm) : ℝ)))
            epsilon (seqDelta / (Fintype.card (Arm × Arm) : ℝ)) outcome)
          (initial outcome) (challengers outcome))
        (indexedPruneRounds roundCount
          (adaptivePruneDecision pruneObservation lower upper pruneDelta) outcome active)
        (fun candidate => decision candidate outcome))} ≤
      pruneDelta / 2 + seqDelta + detectFailure := by
  apply optMaximizeFinalOutput_failure_probability_of_adaptiveSeqEliminate law
    seqObservation preferenceGap epsilon seqDelta hindependent hmeasurable hbounded hmean
    hantisymmetric hself hsst hepsilon hseqDelta hseqDeltaLeOne maximum anchor
    (fun outcome => indexedPruneRounds roundCount
      (adaptivePruneDecision pruneObservation lower upper pruneDelta) outcome active)
    initial challengers henumerates decision hmaximum (pruneDelta / 2) detectFailure
  · exact adaptivePrune_absoluteMaximum_failure_probability_of_anchorNotEpsilonMaximum law
      roundCount pruneObservation active maximum anchor preferenceGap lower upper pruneDelta
      hantisymmetric hsst hupperNonnegative hmaximum hmaximumMem hanchorNotMaximum
      hpruneIndependent hpruneMeasurable hpruneBounded hpruneMean hpruneSeparation
      hpruneDelta hpruneDeltaLeOne
  · exact hdetectFailure

end FalahatgarEtAl2017MaxingRanking
