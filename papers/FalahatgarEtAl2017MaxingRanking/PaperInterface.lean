import FalahatgarEtAl2017MaxingRanking.MainTheorems
import FalahatgarEtAl2017MaxingRanking.FinsetSeqEliminate
import FalahatgarEtAl2017MaxingRanking.Assumptions
import FalahatgarEtAl2017MaxingRanking.FiniteSSTExistence
import FalahatgarEtAl2017MaxingRanking.FreshFinalCheck
import FalahatgarEtAl2017MaxingRanking.OptMaximizeResource

/-!
# Human-Facing Paper Interface: Maxing and Ranking with Noisy Comparisons

This source-presentation-shaped surface has one transparent proposition for
each independently numbered main-paper or supplement result in scope. Main
Theorem 9 and Supplement Theorem 22 have identical mathematical statements but
remain separate rows because the source does not explicitly identify the two
numbers as a restatement. Multi-clause source results bundle their correctness and resource
clauses in one Spec. Source definitions, stochastic models, and algorithms
route to actual imported declarations rather than artificial proposition rows.
-/

namespace FalahatgarEtAl2017MaxingRanking

open AppliedModelingLib PreferenceRL
open MeasureTheory ProbabilityTheory

/--
Source-facing proposition for the main-paper prose claim that every finite SST
model has a maximum element and a ranking.
-/
def sstMaximumAndRankingExistenceSpec : Prop :=
  ∀ {Arm : Type*} [Fintype Arm] [Nonempty Arm],
    let _ : DecidableEq Arm := Classical.decEq Arm
    ∀
    (preferenceGap : Arm → Arm → ℝ)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hsst : StrongStochasticTransitivity preferenceGap),
    (∃ maximum, AbsoluteMaximum preferenceGap maximum) ∧
      ∃ ranking : Fin (Fintype.card Arm) → Arm,
        PreferenceRanking preferenceGap ranking

/-- Source-facing proposition for Main Lemma 1. -/
def lemma1_compareSpec : Prop :=
  (∀ {Ω : Type*}
    (observation : ℕ → Ω → ℝ) (lower upper delta : ℝ) (outcome : Ω)
    (hseparation : lower < upper) (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1),
    adaptiveCompareStoppingTime observation (fixedSampleBudget lower upper delta)
        lower upper delta outcome ≤ fixedSampleBudget lower upper delta ∧
      2 / (upper - lower) ^ 2 * Real.log (2 / delta) ≤
        (fixedSampleBudget lower upper delta : ℝ) ∧
      (fixedSampleBudget lower upper delta : ℝ) <
        2 / (upper - lower) ^ 2 * Real.log (2 / delta) + 1) ∧
  (∀ {Ω : Type*} [MeasurableSpace Ω]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (observation : ℕ → Ω → ℝ) (lower upper trueGap delta : ℝ)
    (hindependent : iIndepFun (fun index : Fin (fixedSampleBudget lower upper delta) =>
      observation index.val) law)
    (hmeasurable : ∀ index < fixedSampleBudget lower upper delta,
      Measurable (observation index))
    (hbounded : ∀ index < fixedSampleBudget lower upper delta, ∀ᵐ outcome ∂law,
      observation index outcome ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ index < fixedSampleBudget lower upper delta,
      law[observation index] = 1 / 2 + trueGap)
    (hgap : trueGap ≤ lower) (hseparation : lower < upper)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1),
    law.real {outcome | adaptiveCompare observation (fixedSampleBudget lower upper delta)
      lower upper delta outcome ≠ .lower} ≤ delta) ∧
  (∀ {Ω : Type*} [MeasurableSpace Ω]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (observation : ℕ → Ω → ℝ) (lower upper trueGap delta : ℝ)
    (hindependent : iIndepFun (fun index : Fin (fixedSampleBudget lower upper delta) =>
      observation index.val) law)
    (hmeasurable : ∀ index < fixedSampleBudget lower upper delta,
      Measurable (observation index))
    (hbounded : ∀ index < fixedSampleBudget lower upper delta, ∀ᵐ outcome ∂law,
      observation index outcome ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ index < fixedSampleBudget lower upper delta,
      law[observation index] = 1 / 2 + trueGap)
    (hgap : upper ≤ trueGap) (hseparation : lower < upper)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1),
    law.real {outcome | adaptiveCompare observation (fixedSampleBudget lower upper delta)
      lower upper delta outcome ≠ .upper} ≤ delta)

/-- Source-facing proposition for Main Theorem 2. -/
def theorem2_seqEliminateSpec : Prop :=
  (∀ {Arm : Type*} [Fintype Arm] [Nonempty Arm],
    let _ : DecidableEq Arm := Classical.decEq Arm
    ∀
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap) (epsilon delta : ℝ)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hself : ∀ arm, preferenceGap arm arm = 0)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hepsilon : 0 < epsilon) (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1),
    1 - delta ≤ canonicalFreshUniformSeqEliminateEpsilonMaximumProbability
      preferenceGap hprobability epsilon delta) ∧
  (∀ (armCount : ℕ) (epsilon delta : ℝ) (harmCount : 0 < armCount)
    (hepsilon : 0 < epsilon) (hepsilonLeOne : epsilon ≤ 1)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1),
    seqEliminateSourceComparisonEnvelope armCount epsilon delta ≤
      3 * (armCount : ℝ) *
        (1 + Real.log ((armCount : ℝ) / delta)) / epsilon ^ 2)

/-- Source-facing proposition for Main Lemma 3. -/
def lemma3_pickAnchorSpec : Prop :=
  (∀ {Arm : Type*} [Fintype Arm] [Nonempty Arm],
    let _ : DecidableEq Arm := Classical.decEq Arm
    ∀
    (cutoff : ℕ) (delta epsilon : ℝ)
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (hcutoff : 0 < cutoff) (hcutoffLeCard : cutoff ≤ Fintype.card Arm)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) (hepsilon : 0 < epsilon)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hself : ∀ arm, preferenceGap arm arm = 0)
    (hsst : StrongStochasticTransitivity preferenceGap),
    1 - delta ≤ freshPickAnchorUniformGoodAnchorProbability
      cutoff delta epsilon
      (fun sample => canonicalFreshPickAnchorOutcomeLaw sample
        (pickAnchorSourceSampleCount_pos cutoff delta hcutoff hdelta hdeltaLeOne)
        preferenceGap hprobability epsilon
        ((delta / 2) /
          (pickAnchorSampleCount (Fintype.card Arm) cutoff delta : ℝ)))
      (fun sample => canonicalFreshPickAnchorObservation sample epsilon
        ((delta / 2) / (pickAnchorSampleCount (Fintype.card Arm) cutoff delta : ℝ)))
      preferenceGap hcutoff hdelta hdeltaLeOne) ∧
  (∀ {Arm : Type*} [Fintype Arm] [Nonempty Arm]
    (cutoff : ℕ) (epsilon delta : ℝ)
    (hcutoff : 0 < cutoff) (hepsilon : 0 < epsilon) (hepsilonLeOne : epsilon ≤ 1)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1),
    (((pickAnchorSampleCount (Fintype.card Arm) cutoff delta - 1) *
      fixedSampleBudget 0 epsilon
        ((delta / 2) / (pickAnchorSampleCount (Fintype.card Arm) cutoff delta : ℝ)) : ℕ) : ℝ) ≤
      5 *
          ((Fintype.card Arm : ℝ) / (cutoff : ℝ) * Real.log (2 / delta) + 1) *
        (1 + Real.log
          (((Fintype.card Arm : ℝ) / (cutoff : ℝ) * Real.log (2 / delta) + 1) / delta)) /
        epsilon ^ 2)

/-- Source-facing proposition for Main Remark 4. -/
def remark4_pickAnchorLinearCutoffSpec : Prop :=
  ∀ {Arm : Type*} [Fintype Arm] [Nonempty Arm]
    (cutoff : ℕ) (c epsilon delta : ℝ)
    (hcutoff : 0 < cutoff) (hepsilon : 0 < epsilon) (hepsilonLeOne : epsilon ≤ 1)
    (hc : 0 < c) (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1)
    (hlinearCutoff : (Fintype.card Arm : ℝ) / (cutoff : ℝ) ≤ 1 / c),
    (((pickAnchorSampleCount (Fintype.card Arm) cutoff delta - 1) *
      fixedSampleBudget 0 epsilon
        ((delta / 2) / (pickAnchorSampleCount (Fintype.card Arm) cutoff delta : ℝ)) : ℕ) : ℝ) ≤
      5 *
          (1 / c * Real.log (2 / delta) + 1) *
        (1 + Real.log
          ((1 / c * Real.log (2 / delta) + 1) / delta)) /
        epsilon ^ 2

/-- Source-facing proposition for Main Lemma 5. -/
def lemma5_pruneSpec : Prop :=
  ∀ {Arm : Type*} [Fintype Arm],
    let _ : DecidableEq Arm := Classical.decEq Arm
    ∀
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (anchor : Arm) (lower upper delta : ℝ) (cutoff : ℕ)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hupperNonnegative : 0 ≤ upper)
    (hanchor : GoodAnchor preferenceGap lower cutoff anchor)
    (hseparation : lower < upper) (hdelta : 0 < delta) (hdeltaHalf : delta ≤ 1 / 2)
    (hcutoff : Real.sqrt (6 * (Fintype.card Arm : ℝ) *
      Real.log (Fintype.card Arm : ℝ)) ≤ (cutoff : ℝ))
    (hdeltaLower : 1 / (Fintype.card Arm : ℝ) ≤ delta),
    let roundCount := sourcePruneRoundCount (Fintype.card Arm)
    let maxBatch := sourcePruneMaxBatch (Arm := Arm) lower upper delta
    let hbudget : ∀ round < roundCount,
        fixedSampleBudget lower upper (adaptivePruneRoundDelta delta round) ≤ maxBatch :=
      fixedSampleBudget_le_sourcePruneMaxBatch_of_source_round lower upper delta
    let outcomeLaw := canonicalFreshPruneOutcomeLaw preferenceGap hprobability roundCount anchor
      lower upper delta maxBatch hbudget
    let decision := canonicalFreshPruneDecision (Arm := Arm) roundCount lower upper delta maxBatch
      hbudget
    (1 - delta / 2 ≤
      pmfProb
        (freshStoppedPruneTraceLaw cutoff (Finset.univ : Finset Arm)
          outcomeLaw decision roundCount)
        (fun state => state.1.card ≤ 2 * cutoff ∧
          (stoppedPruneTraceComparisonCount roundCount cutoff lower upper delta state.2 : ℝ) ≤
            sourceLemma5PruneComparisonRateBound
              (Fintype.card Arm) lower upper delta)) ∧
      (¬ EpsilonMaximum preferenceGap upper anchor →
        1 - delta / 2 ≤
          pmfProbClassical
            (freshStoppedPruneActiveLaw (Finset.univ : Finset Arm) outcomeLaw cutoff decision
              roundCount)
            (fun active => ∃ maximum, AbsoluteMaximum preferenceGap maximum ∧
              maximum ∈ active))

/-- Source-facing proposition for Main Theorem 6. -/
def theorem6_optMaximizeSpec : Prop :=
  (∀ {Arm : Type*} [Fintype Arm] [Nonempty Arm]
    (epsilon delta : ℝ)
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hself : ∀ arm, preferenceGap arm arm = 0)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hepsilon : 0 < epsilon),
    let _ : DecidableEq Arm := Classical.decEq Arm
    let maximum := Classical.choose
      (exists_absoluteMaximum_of_preferenceComplete_sst preferenceGap
        (preferenceComplete_of_antisymmetric preferenceGap hantisymmetric) hsst)
    1 - delta ≤ canonicalOptMaximizeAlgorithm3SourcePopulationJointEnvelopeProbability
      (epsilon / 3) (2 * epsilon / 3) epsilon delta
      (sourceOptMaximizeAlgorithm3PruneMaxBatch
        (Arm := Arm) (epsilon / 3) (2 * epsilon / 3) delta)
      preferenceGap maximum hprobability hdelta hdeltaLeOne
      (by
        intro round hround
        exact fixedSampleBudget_le_sourceOptMaximizeAlgorithm3PruneMaxBatch
          (epsilon / 3) (2 * epsilon / 3) delta round hround)) ∧
  (∀ {epsilon delta : ℝ} (hepsilon : 0 < epsilon)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1),
    Asymptotics.IsBigO Filter.atTop
      (fun armCount : ℕ => sourceOptMaximizeAlgorithm3TotalRateEnvelope
        armCount epsilon delta)
      (fun armCount : ℕ =>
        (armCount : ℝ) * (1 + Real.log (1 / delta)) / epsilon ^ 2))

/-- Source-facing proposition for Main Theorem 7. -/
def theorem7_rankingLowerBoundSpec : Prop :=
  ∀ {Seed : Type*} [Fintype Seed] [Nonempty Seed],
    let _ : DecidableEq Seed := Classical.decEq Seed
    ∀
    {n comparisonBudget : ℕ} {mu : ℝ} (seedLaw : PMF Seed) (hmu : 0 < mu)
    (hmuHalf : mu ≤ 1 / 2) (hcard : 2 ≤ n)
    (hmuSource : mu ≤ 1 / (n : ℝ) ^ 10)
    (hbudget : (comparisonBudget : ℝ) ≤ (n : ℝ) ^ 2 / 20)
    (procedure : Seed → Theorem7AdaptiveRankingProcedure n comparisonBudget),
    ∃ coordinate : unorderedComparisonCoordinate (Fin n), ∃ orientation : Bool,
      ¬ ((7 : ℝ) / 8 ≤ theorem7SeededSmallMuInstanceSuccessProbability
        seedLaw mu hmu.le hmuHalf hcard procedure coordinate orientation)

/-- Source-facing proposition for Main Theorem 8. -/
def theorem8_bordaMaxingSpec : Prop :=
  ∃ coefficient : ℝ,
    ∀ {Arm : Type*} [Fintype Arm] [Nonempty Arm]
      (epsilon delta : ℝ),
      0 < epsilon → epsilon ≤ 1 → 0 < delta → delta ≤ 1 →
      ∃ algorithm : FiniteAdaptiveBordaMaxingAlgorithm Arm,
        ∀ (winProbability : Arm → Arm → ℝ),
          ∀ hprobability : BordaWinProbabilities winProbability,
          1 - delta ≤ finiteAdaptiveBordaMaxingSuccessProbability
            winProbability hprobability epsilon algorithm ∧
          ∀ rewards,
            (algorithm.executionComparisonCount rewards : ℝ) ≤
              coefficient * Fintype.card Arm *
                (1 + Real.log (1 / (delta / 2))) / epsilon ^ 2

/-- Source-facing proposition for Main Theorem 9 / Supplement Theorem 22. -/
def theorem9_bordaRankingSpec : Prop :=
  (∀ {Arm : Type*} [Fintype Arm] [Nonempty Arm]
    (winProbability : Arm → Arm → ℝ) (hprobability : BordaWinProbabilities winProbability)
    (epsilon delta : ℝ) (hepsilon : 0 < epsilon)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1),
    let _ : DecidableEq Arm := Classical.decEq Arm
    ∃ rankingRule : (Arm → ℝ) → Fin (Fintype.card Arm) → Arm,
      IsEmpiricalBordaRankingRule rankingRule ∧
        (canonicalBordaBatchLaw winProbability hprobability
          (bordaSampleBudget (Fintype.card Arm) epsilon delta)).toMeasure.real
          {labelTable | ¬ EpsilonBordaRanking winProbability epsilon
            (rankingRule (fun arm => bordaEmpiricalScore
              (canonicalBordaBatchObservation
                (bordaSampleBudget (Fintype.card Arm) epsilon delta) arm)
              (bordaSampleBudget (Fintype.card Arm) epsilon delta) labelTable))} ≤ delta) ∧
  (∀ (armCount : ℕ) (epsilon delta : ℝ) (harmCount : 0 < armCount)
    (hepsilon : 0 < epsilon) (hepsilonLeOne : epsilon ≤ 1)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1),
    (bordaTotalSampleCount armCount epsilon delta : ℝ) ≤
      3 * (armCount : ℝ) *
        (1 + Real.log ((armCount : ℝ) / delta)) / epsilon ^ 2)

/-- Source-facing proposition for Supplement Lemma 10. -/
def lemma10_compareCapSpec : Prop :=
  ∀ {Ω : Type*}
    (observation : ℕ → Ω → ℝ) (lower upper delta : ℝ) (outcome : Ω)
    (hlower : 0 ≤ lower) (hseparation : lower < upper)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1),
    adaptiveCompareStoppingTime observation (fixedSampleBudget lower upper delta)
        lower upper delta outcome ≤ fixedSampleBudget lower upper delta ∧
      2 / (upper - lower) ^ 2 * Real.log (2 / delta) ≤
        (fixedSampleBudget lower upper delta : ℝ) ∧
      (fixedSampleBudget lower upper delta : ℝ) <
        2 / (upper - lower) ^ 2 * Real.log (2 / delta) + 1

/-- Source-facing proposition for Supplement Lemma 11. -/
def lemma11_compareLowerSpec : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (observation : ℕ → Ω → ℝ) (lower upper trueGap delta : ℝ)
    (hindependent : iIndepFun (fun index : Fin (fixedSampleBudget lower upper delta) =>
      observation index.val) law)
    (hmeasurable : ∀ index < fixedSampleBudget lower upper delta,
      Measurable (observation index))
    (hbounded : ∀ index < fixedSampleBudget lower upper delta, ∀ᵐ outcome ∂law,
      observation index outcome ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ index < fixedSampleBudget lower upper delta,
      law[observation index] = 1 / 2 + trueGap)
    (hgap : trueGap ≤ lower) (hlower : 0 ≤ lower) (hseparation : lower < upper)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1),
    law.real {outcome | adaptiveCompare observation (fixedSampleBudget lower upper delta)
      lower upper delta outcome ≠ .lower} ≤ delta

/-- Source-facing proposition for Supplement Lemma 12. -/
def lemma12_compareUpperSpec : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (observation : ℕ → Ω → ℝ) (lower upper trueGap delta : ℝ)
    (hindependent : iIndepFun (fun index : Fin (fixedSampleBudget lower upper delta) =>
      observation index.val) law)
    (hmeasurable : ∀ index < fixedSampleBudget lower upper delta,
      Measurable (observation index))
    (hbounded : ∀ index < fixedSampleBudget lower upper delta, ∀ᵐ outcome ∂law,
      observation index outcome ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ index < fixedSampleBudget lower upper delta,
      law[observation index] = 1 / 2 + trueGap)
    (hgap : upper ≤ trueGap) (hlower : 0 ≤ lower) (hseparation : lower < upper)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1),
    law.real {outcome | adaptiveCompare observation (fixedSampleBudget lower upper delta)
      lower upper delta outcome ≠ .upper} ≤ delta

/-- Source-facing proposition for Supplement Lemma 13. -/
def lemma13_pruneRetentionSpec : Prop :=
  ∀ {Ω Arm : Type*} [MeasurableSpace Ω],
    let _ : DecidableEq Arm := Classical.decEq Arm
    ∀
    (law : Measure Ω) [IsProbabilityMeasure law]
    (roundCount : ℕ) (observation : ℕ → Arm → ℕ → Ω → ℝ)
    (active : Finset Arm) (kept : Arm)
    (lower upper centeredGap delta : ℝ)
    (hmem : kept ∈ active)
    (hindependent : ∀ round < roundCount,
      iIndepFun (fun sample : Fin (fixedSampleBudget lower upper
        (adaptivePruneRoundDelta delta round)) => observation round kept sample.val) law)
    (hmeasurable : ∀ round < roundCount,
      ∀ sample < fixedSampleBudget lower upper (adaptivePruneRoundDelta delta round),
        Measurable (observation round kept sample))
    (hbounded : ∀ round < roundCount,
      ∀ sample < fixedSampleBudget lower upper (adaptivePruneRoundDelta delta round),
        ∀ᵐ outcome ∂law, observation round kept sample outcome ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ round < roundCount,
      ∀ sample < fixedSampleBudget lower upper (adaptivePruneRoundDelta delta round),
        law[observation round kept sample] = 1 / 2 + centeredGap)
    (hdecisionMeasurable : ∀ round < roundCount,
      MeasurableSet {outcome |
        adaptivePruneDecision observation lower upper delta round kept outcome = .upper})
    (hgap : upper ≤ centeredGap)
    (hseparation : lower < upper)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1),
    1 - delta / 2 ≤
      law.real {outcome | kept ∈ indexedPruneRounds roundCount
        (adaptivePruneDecision observation lower upper delta) outcome active}

/-- Source-facing proposition for Supplement Lemma 14. -/
def lemma14_pruneOneRoundSpec : Prop :=
  ∀ {Arm : Type*} [Fintype Arm],
    let _ : DecidableEq Arm := Classical.decEq Arm
    ∀
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (active : Finset Arm) (anchor : Arm) (lower upper delta : ℝ)
    (cutoff : ℕ)
    (hanchor : GoodAnchor preferenceGap lower cutoff anchor)
    (hseparation : lower < upper) (hdelta : 0 < delta)
    (hdeltaLeOne : delta ≤ 1)
    (hcutoff : 8 * (Real.log (Fintype.card Arm : ℝ)) ^ 2 ≤ (cutoff : ℝ))
    (hdeltaLower : 1 / (Fintype.card Arm : ℝ) ≤ delta)
    (hdeltaUpper : delta ≤ (cutoff : ℝ) / (Fintype.card Arm : ℝ)),
    (canonicalPruneRoundBatchLaw preferenceGap hprobability active anchor
      (fixedSampleBudget lower upper (delta / 4))).toMeasure.real {batchTable |
        ¬ (pruneRound active
          (canonicalPruneRoundDecision active lower upper (delta / 4) batchTable)).card ≤
            2 * cutoff} ≤ delta / 2 ∧
      ((active.card * fixedSampleBudget lower upper (delta / 4) : ℕ) : ℝ) ≤
        (active.card : ℝ) *
          (2 / (upper - lower) ^ 2 * Real.log (2 / (delta / 4)) + 1)

/-- Source-facing proposition for Supplement Lemma 15. -/
def lemma15_pruneMultiRoundSpec : Prop :=
  ∀ {Arm : Type*} [Fintype Arm],
    let _ : DecidableEq Arm := Classical.decEq Arm
    ∀
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (anchor : Arm) (lower upper delta : ℝ) (cutoff : ℕ) (initial : Finset Arm)
    (hanchor : GoodAnchor preferenceGap lower cutoff anchor)
    (hseparation : lower < upper) (hdelta : 0 < delta) (hdeltaHalf : delta ≤ 1 / 2)
    (hcutoff : Real.sqrt (6 * (Fintype.card Arm : ℝ) *
      Real.log (Fintype.card Arm : ℝ)) < (cutoff : ℝ))
    (hdeltaLower : (cutoff : ℝ) / (Fintype.card Arm : ℝ) ≤ delta),
    let maxBatch := sourcePruneMaxBatch (Arm := Arm) lower upper delta
    let hbudget : ∀ round < sourcePruneRoundCount (Fintype.card Arm),
        fixedSampleBudget lower upper (adaptivePruneRoundDelta delta round) ≤ maxBatch :=
      fixedSampleBudget_le_sourcePruneMaxBatch_of_source_round lower upper delta
    1 - delta / 2 ≤
      pmfProb
        (freshStoppedPruneTraceStateLaw preferenceGap lower
          (sourceLemma5PruneContractionFactor (Fintype.card Arm) cutoff delta) cutoff anchor initial
          (canonicalFreshPruneOutcomeLaw preferenceGap hprobability
            (sourcePruneRoundCount (Fintype.card Arm)) anchor lower upper delta maxBatch hbudget)
          (canonicalFreshPruneDecision (sourcePruneRoundCount (Fintype.card Arm))
            lower upper delta maxBatch hbudget)
          (sourcePruneRoundCount (Fintype.card Arm)))
        (fun stateFailure => stateFailure.1.1.card ≤ 2 * cutoff ∧
          (stoppedPruneTraceComparisonCount (sourcePruneRoundCount (Fintype.card Arm))
            cutoff lower upper delta stateFailure.1.2 : ℝ) ≤
            sourceLemma5PruneComparisonRateBound (Fintype.card Arm) lower upper delta)

/-- Source-facing proposition for Supplement Lemma 16. -/
def lemma16_finalCheckAnchorSpec : Prop :=
  ∀ {Arm : Type*} [Fintype Arm] [Nonempty Arm]
    (anchor fallback : Arm) (candidates : Finset Arm)
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (epsilon delta : ℝ)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hanchor : EpsilonMaximum preferenceGap (2 * epsilon / 3) anchor)
    (hepsilon : 0 < epsilon) (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1),
    let _ : DecidableEq Arm := Classical.decEq Arm
    1 - delta / 4 ≤ pmfProbClassical
      (canonicalFreshFinalCheckOutputLaw anchor fallback candidates preferenceGap hprobability
        (2 * epsilon / 3) epsilon ((delta / 4) / (Fintype.card Arm : ℝ)))
      (fun output => output = anchor)

/-- Source-facing proposition for Supplement Lemma 17. -/
def lemma17_anchorPruneSpec : Prop :=
  ∀ {Arm : Type*} [Fintype Arm] [Nonempty Arm],
    let _ : DecidableEq Arm := Classical.decEq Arm
    ∀
    (epsilon delta : ℝ) (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hself : ∀ arm, preferenceGap arm arm = 0)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hepsilon : 0 < epsilon) (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1)
    (hdeltaLower : 1 / (Fintype.card Arm : ℝ) ≤ delta),
    let maximum := Classical.choose
      (exists_absoluteMaximum_of_preferenceComplete_sst preferenceGap
        (preferenceComplete_of_antisymmetric preferenceGap hantisymmetric) hsst)
    let cutoff := sourceOptMaximizeCutoff (Fintype.card Arm)
    let maxBatch := sourceOptMaximizeAlgorithm3PruneMaxBatch
      (Arm := Arm) (epsilon / 3) (2 * epsilon / 3) delta
    (1 - delta / 2 ≤
        canonicalOptMaximizeAnchorPruneTraceSourceSuccessProbability
          cutoff (delta / 4) (delta / 4) (epsilon / 3) (2 * epsilon / 3)
          maxBatch preferenceGap maximum hprobability
          (sourceOptMaximizeCutoff_pos (Fintype.card Arm) Fintype.card_pos)
          (by linarith) (by linarith)
          (by
            intro round hround
            exact fixedSampleBudget_le_sourceOptMaximizeAlgorithm3PruneMaxBatch
              (epsilon / 3) (2 * epsilon / 3) delta round hround)) ∧
      Asymptotics.IsBigO Filter.atTop
        (fun armCount : ℕ => sourceOptMaximizeAlgorithm3RateEnvelope
          armCount (epsilon / 3) (2 * epsilon / 3) epsilon delta)
        (fun armCount : ℕ =>
          (armCount : ℝ) * (1 + Real.log (1 / delta)) / epsilon ^ 2)

/-- Source-facing proposition for Supplement Lemma 18. -/
def lemma18_optMaximizeTailSpec : Prop :=
  ∀ {Arm : Type*} [Fintype Arm] [Nonempty Arm]
    (anchor : Arm) (candidates : Finset Arm)
    (epsilon delta : ℝ)
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hself : ∀ arm, preferenceGap arm arm = 0)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hepsilon : 0 < epsilon) (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1)
    (hdeltaLower : 1 / (Fintype.card Arm : ℝ) ≤ delta)
    (hbranch : EpsilonMaximum preferenceGap (2 * epsilon / 3) anchor ∨
      ∃ maximum, AbsoluteMaximum preferenceGap maximum ∧ maximum ∈ candidates),
    let _ : DecidableEq Arm := Classical.decEq Arm
    (1 - delta / 2 ≤
      pmfProbClassical
        (canonicalOptMaximizeTailSourceLaw anchor candidates preferenceGap hprobability
          epsilon delta)
        (fun fallbackOutput => EpsilonMaximum preferenceGap epsilon fallbackOutput.2)) ∧
      (optMaximizeFinalTailComparisonCap candidates (2 * epsilon / 3) epsilon
          ((delta / 4) / (Fintype.card Arm : ℝ)) epsilon (delta / 4) : ℝ) ≤
        optMaximizeFinalTailAlgorithm3SourceBudget candidates (2 * epsilon / 3) epsilon
          epsilon delta

/-- Source-facing proposition for Supplement Lemma 19. -/
def lemma19_estimateProbabilitySpec : Prop :=
  ∀ {Arm : Type*}
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (challenger incumbent : Arm) (epsilon delta : ℝ)
    (hepsilon : 0 < epsilon)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1),
    (1 / (2 * epsilon ^ 2) * Real.log (2 / delta) ≤
        (estimateProbabilitySampleBudget epsilon delta : ℝ) ∧
      (estimateProbabilitySampleBudget epsilon delta : ℝ) <
        1 / (2 * epsilon ^ 2) * Real.log (2 / delta) + 1) ∧
      (canonicalComparisonBatchLaw preferenceGap hprobability challenger incumbent
        (estimateProbabilitySampleBudget epsilon delta)).toMeasure.real {batch | ¬
          |bordaEmpiricalScore
              (canonicalComparisonBatchObservation (estimateProbabilitySampleBudget epsilon delta))
              (estimateProbabilitySampleBudget epsilon delta) batch -
            (1 / 2 + preferenceGap challenger incumbent)| < epsilon} ≤ delta

/-- Source-facing proposition for Supplement Lemma 20. -/
def lemma20_strongTransitivityRankingSpec : Prop :=
  (∀ {Arm : Type*} [Fintype Arm] [Nonempty Arm],
    let _ : DecidableEq Arm := Classical.decEq Arm
    ∀
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (epsilon delta : ℝ)
    (sourceRanking : Fin (Fintype.card Arm) → Arm)
    (hsourceRanking : PreferenceRanking preferenceGap sourceRanking)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hcard : 0 < Fintype.card Arm) (hepsilon : 0 < epsilon)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1),
    1 - delta ≤ pmfProbClassical
      (canonicalStrongTransitivityBatchLaw preferenceGap hprobability epsilon delta)
      (fun batchTable => EpsilonPreferenceRanking preferenceGap epsilon
        (strongTransitivityRankingOutput
          (canonicalStrongTransitivityRankingEstimate epsilon delta batchTable) epsilon))) ∧
  (∀ (armCount : ℕ) (epsilon delta : ℝ) (harmCount : 0 < armCount)
    (hepsilon : 0 < epsilon) (hepsilonLeOne : epsilon ≤ 1)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1),
    (strongTransitivityComparisonCount (Arm := Fin armCount) epsilon delta : ℝ) ≤
      5 * (armCount : ℝ) ^ 2 *
        (1 + Real.log ((armCount : ℝ) / delta)) / epsilon ^ 2)

/-- Source-facing proposition for Supplement Lemma 21. -/
def lemma21_estimateBordaScoreSpec : Prop :=
  ∀ {Arm : Type*} [Fintype Arm] [Nonempty Arm],
    let _ : DecidableEq Arm := Classical.decEq Arm
    ∀
    (winProbability : Arm → Arm → ℝ)
    (hprobability : BordaWinProbabilities winProbability)
    (arm : Arm) (epsilon delta : ℝ)
    (hepsilon : 0 < epsilon) (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1),
    (1 / (2 * epsilon ^ 2) * Real.log (2 / delta) ≤
        (estimateBordaScoreSampleBudget epsilon delta : ℝ) ∧
      (estimateBordaScoreSampleBudget epsilon delta : ℝ) <
        1 / (2 * epsilon ^ 2) * Real.log (2 / delta) + 1) ∧
      (canonicalBordaBatchLaw winProbability hprobability
        (estimateBordaScoreSampleBudget epsilon delta)).toMeasure.real {labelTable | ¬
          |bordaEmpiricalScore
              (canonicalBordaBatchObservation (estimateBordaScoreSampleBudget epsilon delta) arm)
              (estimateBordaScoreSampleBudget epsilon delta) labelTable -
            bordaScore winProbability arm| < epsilon} ≤ delta

/-- Source-facing proposition for Supplement Theorem 22. -/
def theorem22_bordaRankingSpec : Prop :=
  (∀ {Arm : Type*} [Fintype Arm] [Nonempty Arm]
    (winProbability : Arm → Arm → ℝ) (hprobability : BordaWinProbabilities winProbability)
    (epsilon delta : ℝ) (hepsilon : 0 < epsilon)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1),
    let _ : DecidableEq Arm := Classical.decEq Arm
    ∃ rankingRule : (Arm → ℝ) → Fin (Fintype.card Arm) → Arm,
      IsEmpiricalBordaRankingRule rankingRule ∧
        (canonicalBordaBatchLaw winProbability hprobability
          (bordaSampleBudget (Fintype.card Arm) epsilon delta)).toMeasure.real
          {labelTable | ¬ EpsilonBordaRanking winProbability epsilon
            (rankingRule (fun arm => bordaEmpiricalScore
              (canonicalBordaBatchObservation
                (bordaSampleBudget (Fintype.card Arm) epsilon delta) arm)
              (bordaSampleBudget (Fintype.card Arm) epsilon delta) labelTable))} ≤ delta) ∧
  (∀ (armCount : ℕ) (epsilon delta : ℝ) (harmCount : 0 < armCount)
    (hepsilon : 0 < epsilon) (hepsilonLeOne : epsilon ≤ 1)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1),
    (bordaTotalSampleCount armCount epsilon delta : ℝ) ≤
      3 * (armCount : ℝ) *
        (1 + Real.log ((armCount : ℝ) / delta)) / epsilon ^ 2)

end FalahatgarEtAl2017MaxingRanking
