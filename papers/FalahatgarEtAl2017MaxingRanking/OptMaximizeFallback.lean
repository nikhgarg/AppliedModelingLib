import FalahatgarEtAl2017MaxingRanking.OptMaximizeAnchorPrune
import FalahatgarEtAl2017MaxingRanking.FinsetSeqEliminate

/-!
# OPT-Maximize through its fallback Seq-Eliminate phase

The fallback is sampled only after both the realized anchor and its realized
Prune candidate set are known.  This file records that three-phase dependent
finite PMF and the branch composition needed by Lemma 18: an anchor that is
already sufficiently good needs no retained maximum, while the other branch
uses the fallback after the maximum is retained.
-/

namespace FalahatgarEtAl2017MaxingRanking

open AppliedModelingLib PreferenceRL
open MeasureTheory ProbabilityTheory

/-- Sample the fallback output conditionally on the realized anchor and Prune set. -/
noncomputable def optMaximizeAnchorPruneFallbackLaw
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (anchorLaw : PMF Arm) (pruneLaw : Arm → PMF (Finset Arm))
    (fallbackLaw : Arm → Finset Arm → PMF Arm) : PMF ((Arm × Finset Arm) × Arm) :=
  (optMaximizeAnchorPruneLaw anchorLaw pruneLaw).bind fun anchorCandidates =>
    (fallbackLaw anchorCandidates.1 anchorCandidates.2).map fun fallback =>
      (anchorCandidates, fallback)

/-- Erasing the fallback coordinate recovers the dependent Pick-Anchor/Prune PMF. -/
theorem optMaximizeAnchorPruneFallbackLaw_map_fstPair_eq
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (anchorLaw : PMF Arm) (pruneLaw : Arm → PMF (Finset Arm))
    (fallbackLaw : Arm → Finset Arm → PMF Arm) :
    (optMaximizeAnchorPruneFallbackLaw anchorLaw pruneLaw fallbackLaw).map
      (fun anchorCandidatesFallback => anchorCandidatesFallback.1) =
      optMaximizeAnchorPruneLaw anchorLaw pruneLaw := by
  unfold optMaximizeAnchorPruneFallbackLaw
  rw [PMF.map_bind]
  simp_rw [PMF.map_comp]
  change (optMaximizeAnchorPruneLaw anchorLaw pruneLaw).bind (fun anchorCandidates =>
    (fallbackLaw anchorCandidates.1 anchorCandidates.2).map
      (Function.const Arm anchorCandidates)) = optMaximizeAnchorPruneLaw anchorLaw pruneLaw
  simp

/-- An event depending only on the first two phases has the same probability after fallback. -/
theorem optMaximizeAnchorPruneFallbackLaw_fstPair_probability
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (anchorLaw : PMF Arm) (pruneLaw : Arm → PMF (Finset Arm))
    (fallbackLaw : Arm → Finset Arm → PMF Arm)
    (event : Arm → Finset Arm → Prop) [∀ anchor candidates, Decidable (event anchor candidates)] :
    pmfProb (optMaximizeAnchorPruneFallbackLaw anchorLaw pruneLaw fallbackLaw)
      (fun anchorCandidatesFallback =>
        event anchorCandidatesFallback.1.1 anchorCandidatesFallback.1.2) =
      pmfProb (optMaximizeAnchorPruneLaw anchorLaw pruneLaw)
        (fun anchorCandidates => event anchorCandidates.1 anchorCandidates.2) := by
  calc
    pmfProb (optMaximizeAnchorPruneFallbackLaw anchorLaw pruneLaw fallbackLaw)
        (fun anchorCandidatesFallback =>
          event anchorCandidatesFallback.1.1 anchorCandidatesFallback.1.2) =
        pmfProb
          ((optMaximizeAnchorPruneFallbackLaw anchorLaw pruneLaw fallbackLaw).map
            (fun anchorCandidatesFallback =>
              anchorCandidatesFallback.1))
          (fun anchorCandidates => event anchorCandidates.1 anchorCandidates.2) := by
            symm
            exact pmfProb_map _ _ _
    _ = pmfProb (optMaximizeAnchorPruneLaw anchorLaw pruneLaw)
          (fun anchorCandidates => event anchorCandidates.1 anchorCandidates.2) := by
            rw [optMaximizeAnchorPruneFallbackLaw_map_fstPair_eq]

/-- A uniform conditional fallback failure bound holds after the realized Prune set is sampled. -/
theorem optMaximizeAnchorPruneFallbackLaw_maximumRetained_conditional_failure_le
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (anchorLaw : PMF Arm) (pruneLaw : Arm → PMF (Finset Arm))
    (fallbackLaw : Arm → Finset Arm → PMF Arm)
    (maximumRetained : Arm → Finset Arm → Prop) (failure : Arm → Finset Arm → Arm → Prop)
    (failureBudget : ℝ) (hbudgetNonnegative : 0 ≤ failureBudget)
    [∀ anchor candidates, Decidable (maximumRetained anchor candidates)]
    [∀ anchor candidates fallback, Decidable (failure anchor candidates fallback)]
    (hfailure : ∀ anchor candidates, maximumRetained anchor candidates →
      pmfProb (fallbackLaw anchor candidates) (failure anchor candidates) ≤ failureBudget) :
    pmfProb (optMaximizeAnchorPruneFallbackLaw anchorLaw pruneLaw fallbackLaw)
      (fun anchorCandidatesFallback =>
        maximumRetained anchorCandidatesFallback.1.1 anchorCandidatesFallback.1.2 ∧
          failure anchorCandidatesFallback.1.1 anchorCandidatesFallback.1.2
            anchorCandidatesFallback.2) ≤ failureBudget := by
  classical
  unfold optMaximizeAnchorPruneFallbackLaw
  apply pmfProb_adaptiveStep_le_of_historywiseBound
    (optMaximizeAnchorPruneLaw anchorLaw pruneLaw)
    (fun anchorCandidates => fallbackLaw anchorCandidates.1 anchorCandidates.2)
    (fun anchorCandidates fallback =>
      maximumRetained anchorCandidates.1 anchorCandidates.2 ∧
        failure anchorCandidates.1 anchorCandidates.2 fallback)
    failureBudget
  intro anchorCandidates
  by_cases hretained : maximumRetained anchorCandidates.1 anchorCandidates.2
  · simpa [hretained] using hfailure anchorCandidates.1 anchorCandidates.2 hretained
  · simpa [hretained, pmfProb] using hbudgetNonnegative

/--
The fallback phase only spends its failure budget on the branch where Prune
retained the maximum.  Thus an earlier `anchorGood ∨ maximumRetained` event
and a conditional fallback success event compose without any independence
assumption.
-/
theorem optMaximizeAnchorPruneFallbackLaw_branch_success_probability_ge_one_sub_add
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (anchorLaw : PMF Arm) (pruneLaw : Arm → PMF (Finset Arm))
    (fallbackLaw : Arm → Finset Arm → PMF Arm)
    (anchorGood maximumRetained : Arm → Finset Arm → Prop)
    (fallbackSuccess : Arm → Finset Arm → Arm → Prop)
    (firstFailure fallbackFailure : ℝ)
    [∀ anchor candidates, Decidable (anchorGood anchor candidates)]
    [∀ anchor candidates, Decidable (maximumRetained anchor candidates)]
    [∀ anchor candidates fallback, Decidable (fallbackSuccess anchor candidates fallback)]
    (hfirst : 1 - firstFailure ≤
      pmfProb (optMaximizeAnchorPruneLaw anchorLaw pruneLaw)
        (fun anchorCandidates =>
          anchorGood anchorCandidates.1 anchorCandidates.2 ∨
            maximumRetained anchorCandidates.1 anchorCandidates.2))
    (hfallbackFailure : pmfProb
      (optMaximizeAnchorPruneFallbackLaw anchorLaw pruneLaw fallbackLaw)
      (fun anchorCandidatesFallback =>
        maximumRetained anchorCandidatesFallback.1.1 anchorCandidatesFallback.1.2 ∧
          ¬ fallbackSuccess anchorCandidatesFallback.1.1 anchorCandidatesFallback.1.2
            anchorCandidatesFallback.2) ≤ fallbackFailure) :
    1 - (firstFailure + fallbackFailure) ≤
      pmfProb (optMaximizeAnchorPruneFallbackLaw anchorLaw pruneLaw fallbackLaw)
        (fun anchorCandidatesFallback =>
          anchorGood anchorCandidatesFallback.1.1 anchorCandidatesFallback.1.2 ∨
            (maximumRetained anchorCandidatesFallback.1.1 anchorCandidatesFallback.1.2 ∧
              fallbackSuccess anchorCandidatesFallback.1.1 anchorCandidatesFallback.1.2
                anchorCandidatesFallback.2)) := by
  classical
  let law := optMaximizeAnchorPruneFallbackLaw anchorLaw pruneLaw fallbackLaw
  let firstBad : (Arm × Finset Arm) × Arm → Prop := fun anchorCandidatesFallback =>
    ¬ (anchorGood anchorCandidatesFallback.1.1 anchorCandidatesFallback.1.2 ∨
      maximumRetained anchorCandidatesFallback.1.1 anchorCandidatesFallback.1.2)
  let fallbackBad : (Arm × Finset Arm) × Arm → Prop := fun anchorCandidatesFallback =>
    maximumRetained anchorCandidatesFallback.1.1 anchorCandidatesFallback.1.2 ∧
      ¬ fallbackSuccess anchorCandidatesFallback.1.1 anchorCandidatesFallback.1.2
        anchorCandidatesFallback.2
  let success : (Arm × Finset Arm) × Arm → Prop := fun anchorCandidatesFallback =>
    anchorGood anchorCandidatesFallback.1.1 anchorCandidatesFallback.1.2 ∨
      (maximumRetained anchorCandidatesFallback.1.1 anchorCandidatesFallback.1.2 ∧
        fallbackSuccess anchorCandidatesFallback.1.1 anchorCandidatesFallback.1.2
          anchorCandidatesFallback.2)
  have hfirstFailure : pmfProb law firstBad ≤ firstFailure := by
    change pmfProb law (fun anchorCandidatesFallback =>
      ¬ (anchorGood anchorCandidatesFallback.1.1 anchorCandidatesFallback.1.2 ∨
        maximumRetained anchorCandidatesFallback.1.1 anchorCandidatesFallback.1.2)) ≤ firstFailure
    rw [pmfProb_compl]
    have hfirstMarg : pmfProb law (fun anchorCandidatesFallback =>
        anchorGood anchorCandidatesFallback.1.1 anchorCandidatesFallback.1.2 ∨
          maximumRetained anchorCandidatesFallback.1.1 anchorCandidatesFallback.1.2) =
        pmfProb (optMaximizeAnchorPruneLaw anchorLaw pruneLaw)
          (fun anchorCandidates =>
            anchorGood anchorCandidates.1 anchorCandidates.2 ∨
              maximumRetained anchorCandidates.1 anchorCandidates.2) := by
      simpa only [law] using
        (optMaximizeAnchorPruneFallbackLaw_fstPair_probability anchorLaw pruneLaw fallbackLaw
          (fun anchor candidates => anchorGood anchor candidates ∨ maximumRetained anchor candidates))
    rw [hfirstMarg]
    linarith
  have hfallbackFailure' : pmfProb law fallbackBad ≤ fallbackFailure := by
    simpa [law, fallbackBad] using hfallbackFailure
  have hunion : pmfProb law (fun anchorCandidatesFallback =>
      firstBad anchorCandidatesFallback ∨ fallbackBad anchorCandidatesFallback) ≤
      firstFailure + fallbackFailure :=
    (pmfProb_or_le law firstBad fallbackBad).trans
      (add_le_add hfirstFailure hfallbackFailure')
  have hcomplement : pmfProb law (fun anchorCandidatesFallback => ¬ success anchorCandidatesFallback) ≤
      pmfProb law (fun anchorCandidatesFallback =>
        firstBad anchorCandidatesFallback ∨ fallbackBad anchorCandidatesFallback) := by
    apply pmfProb_le_of_imp
    intro anchorCandidatesFallback
    by_cases hanchorGood :
      anchorGood anchorCandidatesFallback.1.1 anchorCandidatesFallback.1.2 <;>
      by_cases hmaximumRetained :
        maximumRetained anchorCandidatesFallback.1.1 anchorCandidatesFallback.1.2 <;>
      by_cases hfallbackSuccess : fallbackSuccess anchorCandidatesFallback.1.1
        anchorCandidatesFallback.1.2 anchorCandidatesFallback.2 <;>
      simp [success, firstBad, fallbackBad, hanchorGood, hmaximumRetained, hfallbackSuccess]
  have hfailure : pmfProb law (fun anchorCandidatesFallback => ¬ success anchorCandidatesFallback) ≤
      firstFailure + fallbackFailure := hcomplement.trans hunion
  change 1 - (firstFailure + fallbackFailure) ≤ pmfProb law success
  calc
    1 - (firstFailure + fallbackFailure) ≤
        1 - pmfProb law (fun anchorCandidatesFallback => ¬ success anchorCandidatesFallback) := by
          linarith
    _ = pmfProb law success := by
      rw [pmfProb_compl]
      ring

/-- The source PMF through OPT-Maximize's fresh fallback Seq-Eliminate call. -/
noncomputable def canonicalOptMaximizeAnchorPruneFallbackSourceLaw
    {Arm : Type*} [Fintype Arm] [Nonempty Arm]
    (cutoff : ℕ) (anchorDelta pruneDelta fallbackDelta fallbackEpsilon lower upper : ℝ) (maxBatch : ℕ)
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (hcutoff : 0 < cutoff) (hanchorDelta : 0 < anchorDelta)
    (hanchorDeltaLeOne : anchorDelta ≤ 1)
    (hbudget : ∀ round < Fintype.card Arm,
      fixedSampleBudget lower upper (adaptivePruneRoundDelta pruneDelta round) ≤ maxBatch) :
    PMF ((Arm × Finset Arm) × Arm) := by
  classical
  exact optMaximizeAnchorPruneFallbackLaw
    (canonicalFreshPickAnchorSourceOutputLaw cutoff anchorDelta lower preferenceGap hprobability
      hcutoff hanchorDelta hanchorDeltaLeOne)
    (fun anchor => freshStoppedPruneActiveLaw Finset.univ
      (canonicalFreshPruneOutcomeLaw preferenceGap hprobability (Fintype.card Arm) anchor
        lower upper pruneDelta maxBatch hbudget)
      cutoff
      (canonicalFreshPruneDecision (Fintype.card Arm) lower upper pruneDelta maxBatch hbudget)
      (Fintype.card Arm))
    (fun anchor candidates => canonicalFreshFinsetSeqEliminateOutputLaw anchor candidates
      preferenceGap hprobability fallbackEpsilon (fallbackDelta / (candidates.card : ℝ)))

/-- The branch event after the source fallback call. -/
noncomputable def canonicalOptMaximizeAnchorPruneFallbackSourceSuccessProbability
    {Arm : Type*} [Fintype Arm] [Nonempty Arm]
    (cutoff : ℕ) (anchorDelta pruneDelta fallbackDelta fallbackEpsilon lower upper : ℝ) (maxBatch : ℕ)
    (preferenceGap : Arm → Arm → ℝ) (maximum : Arm)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (hcutoff : 0 < cutoff) (hanchorDelta : 0 < anchorDelta)
    (hanchorDeltaLeOne : anchorDelta ≤ 1)
    (hbudget : ∀ round < Fintype.card Arm,
      fixedSampleBudget lower upper (adaptivePruneRoundDelta pruneDelta round) ≤ maxBatch) : ℝ := by
  classical
  exact pmfProb
    (canonicalOptMaximizeAnchorPruneFallbackSourceLaw cutoff anchorDelta pruneDelta fallbackDelta
      fallbackEpsilon lower upper maxBatch preferenceGap hprobability hcutoff hanchorDelta
      hanchorDeltaLeOne hbudget)
    (fun anchorCandidatesFallback =>
      EpsilonMaximum preferenceGap upper anchorCandidatesFallback.1.1 ∨
        (maximum ∈ anchorCandidatesFallback.1.2 ∧
          EpsilonMaximum preferenceGap fallbackEpsilon anchorCandidatesFallback.2))

/--
The concrete source PMF remains successful after its fallback Seq-Eliminate
call.  The first two-phase Lemma-17 event costs `anchorDelta + pruneDelta`;
on the retained-maximum branch the source fallback schedule costs only
`fallbackDelta`.
-/
theorem canonicalOptMaximizeAnchorPruneFallbackSource_branch_success_probability
    {Arm : Type*} [Fintype Arm] [Nonempty Arm]
    (cutoff : ℕ) (anchorDelta pruneDelta fallbackDelta fallbackEpsilon lower upper : ℝ) (maxBatch : ℕ)
    (preferenceGap : Arm → Arm → ℝ) (maximum : Arm)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (ranking : Fin (Fintype.card Arm) → Arm)
    (hranking : PreferenceRanking preferenceGap ranking)
    (hcutoff : 0 < cutoff) (hcutoffLeCard : cutoff ≤ Fintype.card Arm)
    (hanchorDelta : 0 < anchorDelta) (hanchorDeltaLeOne : anchorDelta ≤ 1)
    (hlower : 0 < lower)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hself : ∀ arm, preferenceGap arm arm = 0)
    (hcomplete : PreferenceComplete preferenceGap)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hbudget : ∀ round < Fintype.card Arm,
      fixedSampleBudget lower upper (adaptivePruneRoundDelta pruneDelta round) ≤ maxBatch)
    (hupperNonnegative : 0 ≤ upper)
    (hmaximumAbsolute : AbsoluteMaximum preferenceGap maximum)
    (hseparation : lower < upper) (hpruneDelta : 0 < pruneDelta)
    (hpruneDeltaHalf : pruneDelta ≤ 1 / 2)
    (hcard : 2 ≤ Fintype.card Arm)
    (hpruneCutoff : Real.sqrt (6 * (Fintype.card Arm : ℝ) *
      Real.log (Fintype.card Arm : ℝ)) < (cutoff : ℝ))
    (hpruneDeltaLower : (cutoff : ℝ) / (Fintype.card Arm : ℝ) ≤ pruneDelta)
    (hfallbackEpsilon : 0 < fallbackEpsilon)
    (hfallbackDelta : 0 < fallbackDelta) (hfallbackDeltaLeOne : fallbackDelta ≤ 1) :
    1 - (anchorDelta + pruneDelta + fallbackDelta) ≤
      canonicalOptMaximizeAnchorPruneFallbackSourceSuccessProbability cutoff anchorDelta pruneDelta
        fallbackDelta fallbackEpsilon lower upper maxBatch preferenceGap maximum hprobability hcutoff
        hanchorDelta hanchorDeltaLeOne hbudget := by
  classical
  let anchorLaw : PMF Arm :=
    canonicalFreshPickAnchorSourceOutputLaw cutoff anchorDelta lower preferenceGap hprobability
      hcutoff hanchorDelta hanchorDeltaLeOne
  let pruneLaw : Arm → PMF (Finset Arm) := fun anchor =>
    freshStoppedPruneActiveLaw Finset.univ
      (canonicalFreshPruneOutcomeLaw preferenceGap hprobability (Fintype.card Arm) anchor
        lower upper pruneDelta maxBatch hbudget)
      cutoff
      (canonicalFreshPruneDecision (Fintype.card Arm) lower upper pruneDelta maxBatch hbudget)
      (Fintype.card Arm)
  let fallbackLaw : Arm → Finset Arm → PMF Arm := fun anchor candidates =>
    canonicalFreshFinsetSeqEliminateOutputLaw anchor candidates preferenceGap hprobability fallbackEpsilon
      (fallbackDelta / (candidates.card : ℝ))
  have hfirstStrong := canonicalOptMaximizeAnchorPruneSource_success_probability
    cutoff anchorDelta pruneDelta lower upper maxBatch preferenceGap maximum hprobability ranking
    hranking hcutoff hcutoffLeCard hanchorDelta hanchorDeltaLeOne hlower hantisymmetric hself
    hcomplete hsst hbudget hupperNonnegative hmaximumAbsolute hseparation hpruneDelta
    hpruneDeltaHalf hcard hpruneCutoff hpruneDeltaLower
  have hfirst : 1 - (anchorDelta + pruneDelta) ≤
      pmfProb (optMaximizeAnchorPruneLaw anchorLaw pruneLaw)
        (fun anchorCandidates =>
          EpsilonMaximum preferenceGap upper anchorCandidates.1 ∨ maximum ∈ anchorCandidates.2) := by
    change 1 - (anchorDelta + pruneDelta) ≤
      pmfProb (optMaximizeAnchorPruneLaw anchorLaw pruneLaw)
        (fun anchorCandidates => GoodAnchor preferenceGap lower cutoff anchorCandidates.1 ∧
          anchorCandidates.2.card ≤ 2 * cutoff ∧
            (EpsilonMaximum preferenceGap upper anchorCandidates.1 ∨ maximum ∈ anchorCandidates.2))
      at hfirstStrong
    exact hfirstStrong.trans
      (pmfProb_le_of_imp _ _ _ (by
        intro anchorCandidates hsuccess
        exact hsuccess.2.2))
  have hfallbackFailure : pmfProb
      (optMaximizeAnchorPruneFallbackLaw anchorLaw pruneLaw fallbackLaw)
      (fun anchorCandidatesFallback =>
        maximum ∈ anchorCandidatesFallback.1.2 ∧
          ¬ EpsilonMaximum preferenceGap fallbackEpsilon anchorCandidatesFallback.2) ≤ fallbackDelta := by
    apply optMaximizeAnchorPruneFallbackLaw_maximumRetained_conditional_failure_le
      anchorLaw pruneLaw fallbackLaw (fun _ candidates => maximum ∈ candidates)
      (fun _ _ fallback => ¬ EpsilonMaximum preferenceGap fallbackEpsilon fallback)
      fallbackDelta (le_of_lt hfallbackDelta)
    intro anchor candidates hmaximumMem
    have hfallback := canonicalFreshFinsetSeqEliminate_epsilonMaximum_probability_of_sourceSchedule
      anchor candidates preferenceGap hprobability fallbackEpsilon fallbackDelta hantisymmetric hself hsst
      hfallbackEpsilon hfallbackDelta hfallbackDeltaLeOne maximum hmaximumAbsolute hmaximumMem
    unfold canonicalFreshFinsetSeqEliminateEpsilonMaximumProbability at hfallback
    rw [pmfProbClassical_eq_pmfProb] at hfallback
    change pmfProb (fallbackLaw anchor candidates)
      (fun fallback => ¬ EpsilonMaximum preferenceGap fallbackEpsilon fallback) ≤ fallbackDelta
    rw [pmfProb_compl]
    simpa only [fallbackLaw] using (show 1 -
      pmfProb (fallbackLaw anchor candidates) (EpsilonMaximum preferenceGap fallbackEpsilon) ≤ fallbackDelta by
        linarith)
  change 1 - (anchorDelta + pruneDelta + fallbackDelta) ≤
    pmfProb (optMaximizeAnchorPruneFallbackLaw anchorLaw pruneLaw fallbackLaw)
      (fun anchorCandidatesFallback =>
        EpsilonMaximum preferenceGap upper anchorCandidatesFallback.1.1 ∨
          (maximum ∈ anchorCandidatesFallback.1.2 ∧
            EpsilonMaximum preferenceGap fallbackEpsilon anchorCandidatesFallback.2))
  have hbranch := optMaximizeAnchorPruneFallbackLaw_branch_success_probability_ge_one_sub_add
    anchorLaw pruneLaw fallbackLaw
    (fun anchor _ => EpsilonMaximum preferenceGap upper anchor)
    (fun _ candidates => maximum ∈ candidates)
    (fun _ _ fallback => EpsilonMaximum preferenceGap fallbackEpsilon fallback)
    (anchorDelta + pruneDelta) fallbackDelta hfirst hfallbackFailure
  linarith

end FalahatgarEtAl2017MaxingRanking
