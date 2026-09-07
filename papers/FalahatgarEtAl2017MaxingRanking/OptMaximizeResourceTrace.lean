import FalahatgarEtAl2017MaxingRanking.CanonicalPruneSourceSchedule
import FalahatgarEtAl2017MaxingRanking.OptMaximizeAnchorPrune
import FalahatgarEtAl2017MaxingRanking.OptMaximizeResource
import FalahatgarEtAl2017MaxingRanking.FreshFinalCheckTrace
import FalahatgarEtAl2017MaxingRanking.SourceCutoff
import FalahatgarEtAl2017MaxingRanking.PickAnchorCost

/-!
# Trace-aware first phases of OPT-Maximize

This module keeps Algorithm 3's source integer Prune horizon and its literal
stopped comparison trace in the dependent Pick-Anchor--Prune execution.  The
trace is bookkeeping only: its active-set marginal is proved equal to the
candidate execution supplied to downstream phases.
-/

namespace FalahatgarEtAl2017MaxingRanking

open AppliedModelingLib PreferenceRL
open MeasureTheory ProbabilityTheory

/-- The literal source batch allocation made by Pick-Anchor's Seq-Eliminate call. -/
noncomputable def optMaximizePickAnchorComparisonCap {Arm : Type*} [Fintype Arm]
    (cutoff : ℕ) (anchorDelta lower : ℝ) : ℕ :=
  (pickAnchorSampleCount (Fintype.card Arm) cutoff anchorDelta - 1) *
    fixedSampleBudget 0 lower
      ((anchorDelta / 2) /
        (pickAnchorSampleCount (Fintype.card Arm) cutoff anchorDelta : ℝ))

/-- Every source Prune round is bounded by one finite common batch cap. -/
noncomputable def sourceOptMaximizeAlgorithm3PruneMaxBatch
    {Arm : Type*} [Fintype Arm] (lower upper delta : ℝ) : ℕ :=
  (Finset.range (sourcePruneRoundCount (Fintype.card Arm) + 1)).sup' (by
    exact ⟨0, Finset.mem_range.mpr (Nat.succ_pos _)⟩)
    (fun round => fixedSampleBudget lower upper (adaptivePruneRoundDelta (delta / 4) round))

/-- Every actual Algorithm-3 Prune round is below the common batch cap. -/
theorem fixedSampleBudget_le_sourceOptMaximizeAlgorithm3PruneMaxBatch
    {Arm : Type*} [Fintype Arm] (lower upper delta : ℝ) (round : ℕ)
    (hround : round < sourcePruneRoundCount (Fintype.card Arm)) :
    fixedSampleBudget lower upper (adaptivePruneRoundDelta (delta / 4) round) ≤
      sourceOptMaximizeAlgorithm3PruneMaxBatch (Arm := Arm) lower upper delta := by
  unfold sourceOptMaximizeAlgorithm3PruneMaxBatch
  apply Finset.le_sup' (fun round =>
    fixedSampleBudget lower upper (adaptivePruneRoundDelta (delta / 4) round))
  simp only [Finset.mem_range]
  omega

/-- Pick-Anchor's literal finite cap is below its transparent source-count envelope. -/
theorem optMaximizePickAnchorComparisonCap_real_le_sourceCountEnvelope_generic
    {Arm : Type*} [Fintype Arm] [Nonempty Arm]
    (cutoff : ℕ) (lower anchorDelta : ℝ)
    (hcutoff : 0 < cutoff) (hanchorDelta : 0 < anchorDelta)
    (hanchorDeltaLeOne : anchorDelta ≤ 1) :
    (optMaximizePickAnchorComparisonCap (Arm := Arm) cutoff anchorDelta lower : ℝ) ≤
      ((pickAnchorSampleCount (Fintype.card Arm) cutoff anchorDelta - 1 : ℕ) : ℝ) *
        (2 / lower ^ 2 *
          Real.log (4 * (pickAnchorSampleCount (Fintype.card Arm) cutoff anchorDelta : ℝ) /
            anchorDelta) + 1) := by
  let count : ℕ := pickAnchorSampleCount (Fintype.card Arm) cutoff anchorDelta
  have hcountPos : 0 < count := by
    dsimp [count]
    exact pickAnchorSampleCount_pos (Fintype.card Arm) cutoff anchorDelta
      Fintype.card_pos hcutoff hanchorDelta hanchorDeltaLeOne
  have hcountReal : 0 < (count : ℝ) := by exact_mod_cast hcountPos
  have hraw := pickAnchorSample_ceilingComparisonCap count lower anchorDelta
    hcountPos hanchorDelta hanchorDeltaLeOne
  have hlogRewrite : 2 / ((anchorDelta / 2) / (count : ℝ)) =
      4 * (count : ℝ) / anchorDelta := by
    field_simp [ne_of_gt hanchorDelta, ne_of_gt hcountReal]
    ring
  change
    (((count - 1) * fixedSampleBudget 0 lower
      ((anchorDelta / 2) / (count : ℝ)) : ℕ) : ℝ) ≤ _
  calc
    (((count - 1) * fixedSampleBudget 0 lower
      ((anchorDelta / 2) / (count : ℝ)) : ℕ) : ℝ) ≤
        ((count - 1 : ℕ) : ℝ) *
          (2 / lower ^ 2 * Real.log (2 / ((anchorDelta / 2) / (count : ℝ))) + 1) := hraw
    _ = ((count - 1 : ℕ) : ℝ) *
          (2 / lower ^ 2 * Real.log (4 * (count : ℝ) / anchorDelta) + 1) := by
      rw [hlogRewrite]

/--
The finite comparison-cap object after Algorithm 3's first two phases.  The
tail term is the already-proved cap for steps 8--13; it depends only on the
realized retained candidate set, not on an independence assumption.
-/
noncomputable def optMaximizeTraceAndTailComparisonCap {Arm : Type*} [Fintype Arm]
    [DecidableEq Arm]
    (cutoff : ℕ) (anchorDelta pruneDelta lower upper finalEta fallbackEpsilon fallbackDelta : ℝ)
    (trace : Fin (sourcePruneRoundCount (Fintype.card Arm)) → Finset Arm)
    (candidates : Finset Arm) : ℕ :=
  optMaximizePickAnchorComparisonCap (Arm := Arm) cutoff anchorDelta lower +
    stoppedPruneTraceComparisonCount (sourcePruneRoundCount (Fintype.card Arm))
      cutoff lower upper pruneDelta trace +
    optMaximizeFinalTailComparisonCap candidates lower upper finalEta fallbackEpsilon fallbackDelta

/-- Draw an anchor, then run its trace-recording stopped-Prune execution. -/
noncomputable def optMaximizeAnchorPruneTraceLaw {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (roundCount : ℕ) (anchorLaw : PMF Arm)
    (pruneTraceLaw : Arm → PMF (stoppedPruneTraceState Arm roundCount × Bool)) :
    PMF (Arm × (stoppedPruneTraceState Arm roundCount × Bool)) :=
  anchorLaw.bind fun anchor => (pruneTraceLaw anchor).map fun stateFailure =>
    (anchor, stateFailure)

/--
Erasing trace and failure bookkeeping recovers the ordinary dependent
Pick-Anchor--Prune candidate-set PMF.
-/
theorem optMaximizeAnchorPruneTraceLaw_map_activeLaw
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (roundCount : ℕ) (anchorLaw : PMF Arm)
    (pruneTraceLaw : Arm → PMF (stoppedPruneTraceState Arm roundCount × Bool))
    (pruneLaw : Arm → PMF (Finset Arm))
    (hactive : ∀ anchor,
      (pruneTraceLaw anchor).map (fun stateFailure => stateFailure.1.1) = pruneLaw anchor) :
    (optMaximizeAnchorPruneTraceLaw roundCount anchorLaw pruneTraceLaw).map
      (fun anchorStateFailure => (anchorStateFailure.1, anchorStateFailure.2.1.1)) =
      optMaximizeAnchorPruneLaw anchorLaw pruneLaw := by
  unfold optMaximizeAnchorPruneTraceLaw optMaximizeAnchorPruneLaw
  rw [PMF.map_bind]
  simp_rw [PMF.map_comp]
  have hkernel : (fun anchor =>
      (pruneTraceLaw anchor).map (fun stateFailure =>
        (anchor, stateFailure.1.1))) =
      (fun anchor => (pruneLaw anchor).map fun active => (anchor, active)) := by
    funext anchor
    calc
      (pruneTraceLaw anchor).map (fun stateFailure => (anchor, stateFailure.1.1)) =
          ((pruneTraceLaw anchor).map (fun stateFailure => stateFailure.1.1)).map
            (fun active => (anchor, active)) := by
              rw [PMF.map_comp]
              rfl
      _ = (pruneLaw anchor).map (fun active => (anchor, active)) := by rw [hactive anchor]
  change anchorLaw.bind (fun anchor =>
      (pruneTraceLaw anchor).map (fun stateFailure => (anchor, stateFailure.1.1))) =
    anchorLaw.bind fun anchor => (pruneLaw anchor).map fun active => (anchor, active)
  rw [hkernel]

/-- An anchor-only event has the same probability after trace-recording Prune. -/
theorem optMaximizeAnchorPruneTraceLaw_fst_probability
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (roundCount : ℕ) (anchorLaw : PMF Arm)
    (pruneTraceLaw : Arm → PMF (stoppedPruneTraceState Arm roundCount × Bool))
    (event : Arm → Prop) [DecidablePred event] :
    pmfProb (optMaximizeAnchorPruneTraceLaw roundCount anchorLaw pruneTraceLaw)
      (fun anchorStateFailure => event anchorStateFailure.1) =
      pmfProb anchorLaw event := by
  classical
  unfold optMaximizeAnchorPruneTraceLaw
  rw [pmfProb_bind]
  simp_rw [pmfProb_map]
  unfold pmfProb
  apply pmfExp_congr
  intro anchor
  by_cases hevent : event anchor <;> simp [hevent, pmfExp_const]

/-- A uniform trace failure bound lifts through a preceding random anchor. -/
theorem optMaximizeAnchorPruneTraceLaw_goodAnchor_conditional_failure_le
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (roundCount : ℕ) (anchorLaw : PMF Arm)
    (pruneTraceLaw : Arm → PMF (stoppedPruneTraceState Arm roundCount × Bool))
    (goodAnchor : Arm → Prop)
    (failure : Arm → stoppedPruneTraceState Arm roundCount × Bool → Prop)
    (failureBudget : ℝ) (hbudgetNonnegative : 0 ≤ failureBudget)
    [DecidablePred goodAnchor] [∀ anchor, DecidablePred (failure anchor)]
    (hfailure : ∀ anchor, goodAnchor anchor →
      pmfProb (pruneTraceLaw anchor) (failure anchor) ≤ failureBudget) :
    pmfProb (optMaximizeAnchorPruneTraceLaw roundCount anchorLaw pruneTraceLaw)
      (fun anchorStateFailure =>
        goodAnchor anchorStateFailure.1 ∧
          failure anchorStateFailure.1 anchorStateFailure.2) ≤ failureBudget := by
  classical
  unfold optMaximizeAnchorPruneTraceLaw
  apply pmfProb_adaptiveStep_le_of_historywiseBound anchorLaw pruneTraceLaw
    (fun anchor stateFailure => goodAnchor anchor ∧ failure anchor stateFailure) failureBudget
  intro anchor
  by_cases hgood : goodAnchor anchor
  · simpa [hgood] using hfailure anchor hgood
  · simpa [hgood, pmfProb] using hbudgetNonnegative

/--
The trace-aware first two phases have the usual dependent failure composition;
the result is stated on the same PMF carrying the Prune resource trace.
-/
theorem optMaximizeAnchorPruneTraceLaw_success_probability_ge_one_sub_add
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (roundCount : ℕ) (anchorLaw : PMF Arm)
    (pruneTraceLaw : Arm → PMF (stoppedPruneTraceState Arm roundCount × Bool))
    (goodAnchor : Arm → Prop)
    (candidateSuccess : Arm → stoppedPruneTraceState Arm roundCount × Bool → Prop)
    (anchorFailure pruneFailure : ℝ)
    [DecidablePred goodAnchor] [∀ anchor, DecidablePred (candidateSuccess anchor)]
    (hanchorFailure : pmfProb anchorLaw (fun anchor => ¬ goodAnchor anchor) ≤ anchorFailure)
    (hpruneFailure :
      pmfProb (optMaximizeAnchorPruneTraceLaw roundCount anchorLaw pruneTraceLaw)
        (fun anchorStateFailure => goodAnchor anchorStateFailure.1 ∧
          ¬ candidateSuccess anchorStateFailure.1 anchorStateFailure.2) ≤ pruneFailure) :
    1 - (anchorFailure + pruneFailure) ≤
      pmfProb (optMaximizeAnchorPruneTraceLaw roundCount anchorLaw pruneTraceLaw)
        (fun anchorStateFailure => goodAnchor anchorStateFailure.1 ∧
          candidateSuccess anchorStateFailure.1 anchorStateFailure.2) := by
  classical
  let law := optMaximizeAnchorPruneTraceLaw roundCount anchorLaw pruneTraceLaw
  let anchorBad : Arm × (stoppedPruneTraceState Arm roundCount × Bool) → Prop :=
    fun anchorStateFailure => ¬ goodAnchor anchorStateFailure.1
  let pruneBad : Arm × (stoppedPruneTraceState Arm roundCount × Bool) → Prop :=
    fun anchorStateFailure =>
      goodAnchor anchorStateFailure.1 ∧
        ¬ candidateSuccess anchorStateFailure.1 anchorStateFailure.2
  let success : Arm × (stoppedPruneTraceState Arm roundCount × Bool) → Prop :=
    fun anchorStateFailure =>
      goodAnchor anchorStateFailure.1 ∧
        candidateSuccess anchorStateFailure.1 anchorStateFailure.2
  have hanchorBad : pmfProb law anchorBad ≤ anchorFailure := by
    change pmfProb (optMaximizeAnchorPruneTraceLaw roundCount anchorLaw pruneTraceLaw)
      (fun anchorStateFailure => ¬ goodAnchor anchorStateFailure.1) ≤ anchorFailure
    calc
      pmfProb (optMaximizeAnchorPruneTraceLaw roundCount anchorLaw pruneTraceLaw)
          (fun anchorStateFailure => ¬ goodAnchor anchorStateFailure.1) =
          pmfProb anchorLaw (fun anchor => ¬ goodAnchor anchor) :=
        optMaximizeAnchorPruneTraceLaw_fst_probability roundCount anchorLaw pruneTraceLaw
          (fun anchor => ¬ goodAnchor anchor)
      _ ≤ anchorFailure := hanchorFailure
  have hpruneBad : pmfProb law pruneBad ≤ pruneFailure := by
    simpa [law, pruneBad] using hpruneFailure
  have hfailureUnion : pmfProb law (fun anchorStateFailure =>
      anchorBad anchorStateFailure ∨ pruneBad anchorStateFailure) ≤ anchorFailure + pruneFailure :=
    (pmfProb_or_le law anchorBad pruneBad).trans (add_le_add hanchorBad hpruneBad)
  have hfailureEq : pmfProb law (fun anchorStateFailure => ¬ success anchorStateFailure) =
      pmfProb law (fun anchorStateFailure =>
        anchorBad anchorStateFailure ∨ pruneBad anchorStateFailure) := by
    apply pmfProb_congr
    intro anchorStateFailure
    by_cases hgood : goodAnchor anchorStateFailure.1 <;>
      by_cases hcandidate : candidateSuccess anchorStateFailure.1 anchorStateFailure.2 <;>
      simp [success, anchorBad, pruneBad, hgood, hcandidate]
  have hfailure : pmfProb law (fun anchorStateFailure => ¬ success anchorStateFailure) ≤
      anchorFailure + pruneFailure := hfailureEq.trans_le hfailureUnion
  change 1 - (anchorFailure + pruneFailure) ≤ pmfProb law success
  calc
    1 - (anchorFailure + pruneFailure) ≤
        1 - pmfProb law (fun anchorStateFailure => ¬ success anchorStateFailure) := by
          linarith
    _ = pmfProb law success := by
          rw [pmfProb_compl]
          ring

/--
Adjoin the source tail cap to a high-probability Pick-Anchor--Prune trace
event.  This is pure finite cap arithmetic: fallback and final checking cannot
exceed their already-established cap conditional on the retained set.
-/
theorem optMaximizeTraceAndTailComparisonCap_probability_of_priorSuccess
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (law : PMF (Arm ×
      (stoppedPruneTraceState Arm (sourcePruneRoundCount (Fintype.card Arm)) × Bool)))
    (preferenceGap : Arm → Arm → ℝ) (maximum : Arm)
    (cutoff : ℕ) (anchorDelta pruneDelta lower upper finalEta fallbackEpsilon fallbackDelta : ℝ)
    (pruneBound successBound : ℝ)
    [DecidablePred (GoodAnchor preferenceGap lower cutoff)]
    [∀ anchor, Decidable (EpsilonMaximum preferenceGap upper anchor)]
    (hprior : successBound ≤ pmfProb law (fun anchorStateFailure =>
      GoodAnchor preferenceGap lower cutoff anchorStateFailure.1 ∧
        anchorStateFailure.2.2 = false ∧
          anchorStateFailure.2.1.1.card ≤ 2 * cutoff ∧
          (stoppedPruneTraceComparisonCount (sourcePruneRoundCount (Fintype.card Arm))
            cutoff lower upper pruneDelta anchorStateFailure.2.1.2 : ℝ) ≤
            pruneBound ∧
          (EpsilonMaximum preferenceGap upper anchorStateFailure.1 ∨
            maximum ∈ anchorStateFailure.2.1.1))) :
    successBound ≤ pmfProb law (fun anchorStateFailure =>
      GoodAnchor preferenceGap lower cutoff anchorStateFailure.1 ∧
        anchorStateFailure.2.2 = false ∧
          anchorStateFailure.2.1.1.card ≤ 2 * cutoff ∧
          (EpsilonMaximum preferenceGap upper anchorStateFailure.1 ∨
            maximum ∈ anchorStateFailure.2.1.1) ∧
          (optMaximizeTraceAndTailComparisonCap cutoff anchorDelta pruneDelta lower upper
            finalEta fallbackEpsilon fallbackDelta anchorStateFailure.2.1.2
            anchorStateFailure.2.1.1 : ℝ) ≤
            (optMaximizePickAnchorComparisonCap (Arm := Arm) cutoff anchorDelta lower : ℝ) +
              pruneBound +
              (optMaximizeFinalTailComparisonCap anchorStateFailure.2.1.1 lower upper
                finalEta fallbackEpsilon fallbackDelta : ℝ)) := by
  apply hprior.trans
  apply pmfProb_le_of_imp
  intro anchorStateFailure hsuccess
  refine ⟨hsuccess.1, hsuccess.2.1, hsuccess.2.2.1, hsuccess.2.2.2.2, ?_⟩
  unfold optMaximizeTraceAndTailComparisonCap
  rw [Nat.cast_add, Nat.cast_add]
  exact add_le_add (add_le_add le_rfl hsuccess.2.2.2.1) le_rfl

/--
The active candidate-set execution at Algorithm 2's literal integer source
horizon.  This is a source-faithful counterpart of the earlier conservative
full-card round interface.
-/
noncomputable def canonicalOptMaximizeAnchorPruneSourceLogActiveLaw
    {Arm : Type*} [Fintype Arm] [Nonempty Arm] [DecidableEq Arm]
    (cutoff : ℕ) (anchorDelta pruneDelta lower upper : ℝ) (maxBatch : ℕ)
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (hcutoff : 0 < cutoff) (hanchorDelta : 0 < anchorDelta)
    (hanchorDeltaLeOne : anchorDelta ≤ 1)
    (hbudget : ∀ round < sourcePruneRoundCount (Fintype.card Arm),
      fixedSampleBudget lower upper (adaptivePruneRoundDelta pruneDelta round) ≤ maxBatch) :
    PMF (Arm × Finset Arm) := by
  classical
  exact optMaximizeAnchorPruneLaw
    (canonicalFreshPickAnchorSourceOutputLaw cutoff anchorDelta lower preferenceGap hprobability
      hcutoff hanchorDelta hanchorDeltaLeOne)
    (fun anchor => freshStoppedPruneActiveLaw Finset.univ
      (canonicalFreshPruneOutcomeLaw preferenceGap hprobability
        (sourcePruneRoundCount (Fintype.card Arm)) anchor lower upper pruneDelta maxBatch hbudget)
      cutoff
      (canonicalFreshPruneDecision (sourcePruneRoundCount (Fintype.card Arm))
        lower upper pruneDelta maxBatch hbudget)
      (sourcePruneRoundCount (Fintype.card Arm)))

/--
The source-horizon trace execution for Algorithm 3's first two phases.  The
actual comparison schedule uses `pruneDelta`; the trace's proof-only
contraction monitor uses the larger of that confidence and the cutoff ratio.
Maximum retention is proved on this same execution through its active-set
marginal rather than by changing the law or its failure flag.
-/
noncomputable def canonicalOptMaximizeAnchorPruneTraceSourceLaw
    {Arm : Type*} [Fintype Arm] [Nonempty Arm] [DecidableEq Arm]
    (cutoff : ℕ) (anchorDelta pruneDelta lower upper : ℝ) (maxBatch : ℕ)
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (maximum : Arm)
    (hcutoff : 0 < cutoff) (hanchorDelta : 0 < anchorDelta)
    (hanchorDeltaLeOne : anchorDelta ≤ 1)
    (hbudget : ∀ round < sourcePruneRoundCount (Fintype.card Arm),
      fixedSampleBudget lower upper (adaptivePruneRoundDelta pruneDelta round) ≤ maxBatch) :
    PMF (Arm ×
      (stoppedPruneTraceState Arm (sourcePruneRoundCount (Fintype.card Arm)) × Bool)) := by
  classical
  exact optMaximizeAnchorPruneTraceLaw (sourcePruneRoundCount (Fintype.card Arm))
    (canonicalFreshPickAnchorSourceOutputLaw cutoff anchorDelta lower preferenceGap hprobability
      hcutoff hanchorDelta hanchorDeltaLeOne)
    (fun anchor =>
      freshStoppedPruneTraceStateLaw preferenceGap lower
        (sourceLemma5PruneContractionFactor (Fintype.card Arm) cutoff pruneDelta)
        cutoff anchor Finset.univ
        (canonicalFreshPruneOutcomeLaw preferenceGap hprobability
          (sourcePruneRoundCount (Fintype.card Arm)) anchor lower upper pruneDelta maxBatch hbudget)
        (canonicalFreshPruneDecision (sourcePruneRoundCount (Fintype.card Arm))
          lower upper pruneDelta maxBatch hbudget)
        (sourcePruneRoundCount (Fintype.card Arm)))

/--
The raw conditional Lemma-17 trace event.  A good anchor either already meets
the `upper` threshold, or the same stopped execution retains the designated
absolute maximum.  The exact inverse-square contraction tail remains visible
until the enclosing Algorithm-3 proof allocates its global confidence budget.
-/
theorem canonicalFreshStoppedPruneTrace_lemma17_candidate_and_cost_success_probability_raw
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (anchor maximum : Arm) (lower upper delta : ℝ) (maxBatch cutoff : ℕ)
    (hbudget : ∀ round < sourcePruneRoundCount (Fintype.card Arm),
      fixedSampleBudget lower upper (adaptivePruneRoundDelta delta round) ≤ maxBatch)
    (initial : Finset Arm)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hupperNonnegative : 0 ≤ upper)
    (hmaximumAbsolute : AbsoluteMaximum preferenceGap maximum)
    (hanchor : GoodAnchor preferenceGap lower cutoff anchor)
    (hmaximum : maximum ∈ initial)
    (hseparation : lower < upper) (hdelta : 0 < delta) (hdeltaHalf : delta ≤ 1 / 2)
    (hcutoffPos : 0 < cutoff)
    (hcutoff : Real.sqrt (6 * (Fintype.card Arm : ℝ) *
      Real.log (Fintype.card Arm : ℝ)) ≤ (cutoff : ℝ))
    [Decidable (EpsilonMaximum preferenceGap upper anchor)] :
    1 - (1 / (Fintype.card Arm : ℝ) ^ 2 + delta / 2) ≤
      pmfProb
        (freshStoppedPruneTraceStateLaw preferenceGap lower
          (sourceLemma5PruneContractionFactor (Fintype.card Arm) cutoff delta)
          cutoff anchor initial
          (canonicalFreshPruneOutcomeLaw preferenceGap hprobability
            (sourcePruneRoundCount (Fintype.card Arm)) anchor lower upper delta maxBatch hbudget)
          (canonicalFreshPruneDecision (sourcePruneRoundCount (Fintype.card Arm))
            lower upper delta maxBatch hbudget)
          (sourcePruneRoundCount (Fintype.card Arm)))
        (fun stateFailure => stateFailure.2 = false ∧
          stateFailure.1.1.card ≤ 2 * cutoff ∧
          (stoppedPruneTraceComparisonCount (sourcePruneRoundCount (Fintype.card Arm))
            cutoff lower upper delta stateFailure.1.2 : ℝ) ≤
            sourceLemma5PruneComparisonRateBound (Fintype.card Arm) lower upper delta ∧
          (EpsilonMaximum preferenceGap upper anchor ∨ maximum ∈ stateFailure.1.1)) := by
  classical
  by_cases hanchorMaximum : EpsilonMaximum preferenceGap upper anchor
  · have hsource :=
      canonicalFreshStoppedPruneTrace_card_size_cost_success_probability_ge_one_sub_card_inv_sq_of_sourceLemma5_sharpEnvelope
      preferenceGap hprobability anchor lower upper delta maxBatch cutoff hbudget initial hanchor
      hseparation hdelta hdeltaHalf hcutoffPos hcutoff
    calc
      1 - (1 / (Fintype.card Arm : ℝ) ^ 2 + delta / 2) ≤
          1 - 1 / (Fintype.card Arm : ℝ) ^ 2 := by linarith
      _ ≤ pmfProb
          (freshStoppedPruneTraceStateLaw preferenceGap lower
            (sourceLemma5PruneContractionFactor (Fintype.card Arm) cutoff delta)
            cutoff anchor initial
            (canonicalFreshPruneOutcomeLaw preferenceGap hprobability
              (sourcePruneRoundCount (Fintype.card Arm)) anchor lower upper delta maxBatch hbudget)
            (canonicalFreshPruneDecision (sourcePruneRoundCount (Fintype.card Arm))
              lower upper delta maxBatch hbudget)
            (sourcePruneRoundCount (Fintype.card Arm)))
          (fun stateFailure => stateFailure.2 = false ∧
            stateFailure.1.1.card ≤ 2 * cutoff ∧
            (stoppedPruneTraceComparisonCount (sourcePruneRoundCount (Fintype.card Arm))
              cutoff lower upper delta stateFailure.1.2 : ℝ) ≤
              sourceLemma5PruneComparisonRateBound (Fintype.card Arm) lower upper delta) := hsource
      _ ≤ pmfProb
          (freshStoppedPruneTraceStateLaw preferenceGap lower
            (sourceLemma5PruneContractionFactor (Fintype.card Arm) cutoff delta)
            cutoff anchor initial
            (canonicalFreshPruneOutcomeLaw preferenceGap hprobability
              (sourcePruneRoundCount (Fintype.card Arm)) anchor lower upper delta maxBatch hbudget)
            (canonicalFreshPruneDecision (sourcePruneRoundCount (Fintype.card Arm))
              lower upper delta maxBatch hbudget)
            (sourcePruneRoundCount (Fintype.card Arm)))
          (fun stateFailure => stateFailure.2 = false ∧
            stateFailure.1.1.card ≤ 2 * cutoff ∧
            (stoppedPruneTraceComparisonCount (sourcePruneRoundCount (Fintype.card Arm))
              cutoff lower upper delta stateFailure.1.2 : ℝ) ≤
              sourceLemma5PruneComparisonRateBound (Fintype.card Arm) lower upper delta ∧
            (EpsilonMaximum preferenceGap upper anchor ∨ maximum ∈ stateFailure.1.1)) := by
              apply pmfProb_le_of_imp
              intro stateFailure hsuccess
              exact ⟨hsuccess.1, hsuccess.2.1, hsuccess.2.2, Or.inl hanchorMaximum⟩
  · have hgap : upper ≤ preferenceGap maximum anchor := by
      exact le_of_lt (absoluteMaximum_gap_gt_of_not_epsilonMaximum preferenceGap upper
        hantisymmetric hsst hupperNonnegative maximum anchor hmaximumAbsolute hanchorMaximum)
    have hsource := canonicalFreshStoppedPruneTrace_card_size_cost_and_max_probability_ge_raw
      preferenceGap hprobability anchor maximum lower upper delta maxBatch cutoff hbudget initial
      hanchor hmaximum hgap hseparation hdelta hdeltaHalf hcutoffPos hcutoff
    exact hsource.trans (pmfProb_le_of_imp _ _ _ (by
      intro stateFailure hsuccess
      exact ⟨hsuccess.1, hsuccess.2.1, hsuccess.2.2.1, Or.inr hsuccess.2.2.2⟩))

/-- The source probability of the trace-aware Pick-Anchor--Prune success event. -/
noncomputable def canonicalOptMaximizeAnchorPruneTraceSourceSuccessProbability
    {Arm : Type*} [Fintype Arm] [Nonempty Arm] [DecidableEq Arm]
    (cutoff : ℕ) (anchorDelta pruneDelta lower upper : ℝ) (maxBatch : ℕ)
    (preferenceGap : Arm → Arm → ℝ) (maximum : Arm)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (hcutoff : 0 < cutoff) (hanchorDelta : 0 < anchorDelta)
    (hanchorDeltaLeOne : anchorDelta ≤ 1)
    (hbudget : ∀ round < sourcePruneRoundCount (Fintype.card Arm),
      fixedSampleBudget lower upper (adaptivePruneRoundDelta pruneDelta round) ≤ maxBatch) : ℝ := by
  classical
  exact pmfProb
    (canonicalOptMaximizeAnchorPruneTraceSourceLaw cutoff anchorDelta pruneDelta lower upper
      maxBatch preferenceGap hprobability maximum hcutoff hanchorDelta hanchorDeltaLeOne hbudget)
    (fun anchorStateFailure =>
      GoodAnchor preferenceGap lower cutoff anchorStateFailure.1 ∧
        anchorStateFailure.2.2 = false ∧
          anchorStateFailure.2.1.1.card ≤ 2 * cutoff ∧
          (stoppedPruneTraceComparisonCount (sourcePruneRoundCount (Fintype.card Arm))
            cutoff lower upper pruneDelta anchorStateFailure.2.1.2 : ℝ) ≤
            sourceLemma5PruneComparisonRateBound (Fintype.card Arm) lower upper pruneDelta ∧
          (EpsilonMaximum preferenceGap upper anchorStateFailure.1 ∨
            maximum ∈ anchorStateFailure.2.1.1))

/--
The first two Algorithm-3 phases, at the source integer Prune horizon, jointly
supply the Lemma-17 candidate event and its literal stopped resource trace.
-/
theorem canonicalOptMaximizeAnchorPruneTraceSource_success_probability_raw
    {Arm : Type*} [Fintype Arm] [Nonempty Arm] [DecidableEq Arm]
    (cutoff : ℕ) (anchorDelta pruneDelta lower upper : ℝ) (maxBatch : ℕ)
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
    (hbudget : ∀ round < sourcePruneRoundCount (Fintype.card Arm),
      fixedSampleBudget lower upper (adaptivePruneRoundDelta pruneDelta round) ≤ maxBatch)
    (hupperNonnegative : 0 ≤ upper)
    (hmaximumAbsolute : AbsoluteMaximum preferenceGap maximum)
    (hseparation : lower < upper) (hpruneDelta : 0 < pruneDelta)
    (hpruneDeltaHalf : pruneDelta ≤ 1 / 2)
    (hpruneCutoff : Real.sqrt (6 * (Fintype.card Arm : ℝ) *
      Real.log (Fintype.card Arm : ℝ)) < (cutoff : ℝ)) :
    1 - (anchorDelta + (1 / (Fintype.card Arm : ℝ) ^ 2 + pruneDelta / 2)) ≤
      canonicalOptMaximizeAnchorPruneTraceSourceSuccessProbability
        cutoff anchorDelta pruneDelta lower upper maxBatch preferenceGap maximum hprobability
        hcutoff hanchorDelta hanchorDeltaLeOne hbudget := by
  classical
  let roundCount := sourcePruneRoundCount (Fintype.card Arm)
  let anchorLaw : PMF Arm :=
    canonicalFreshPickAnchorSourceOutputLaw cutoff anchorDelta lower preferenceGap hprobability
      hcutoff hanchorDelta hanchorDeltaLeOne
  let pruneTraceLaw : Arm → PMF (stoppedPruneTraceState Arm roundCount × Bool) := fun anchor =>
    freshStoppedPruneTraceStateLaw preferenceGap lower
      (sourceLemma5PruneContractionFactor (Fintype.card Arm) cutoff pruneDelta)
      cutoff anchor Finset.univ
      (canonicalFreshPruneOutcomeLaw preferenceGap hprobability roundCount anchor
        lower upper pruneDelta maxBatch hbudget)
      (canonicalFreshPruneDecision roundCount lower upper pruneDelta maxBatch hbudget)
      roundCount
  let candidateSuccess : Arm → stoppedPruneTraceState Arm roundCount × Bool → Prop :=
    fun anchor stateFailure =>
      stateFailure.2 = false ∧ stateFailure.1.1.card ≤ 2 * cutoff ∧
        (stoppedPruneTraceComparisonCount roundCount cutoff lower upper pruneDelta
          stateFailure.1.2 : ℝ) ≤
          sourceLemma5PruneComparisonRateBound (Fintype.card Arm) lower upper pruneDelta ∧
        (EpsilonMaximum preferenceGap upper anchor ∨ maximum ∈ stateFailure.1.1)
  have hanchorSuccess : 1 - anchorDelta ≤
      pmfProb anchorLaw (GoodAnchor preferenceGap lower cutoff) := by
    have hsource :=
      canonicalFreshPickAnchorSourceOutputLaw_goodAnchor_highProbability_of_preferenceRanking
        cutoff anchorDelta lower preferenceGap hprobability ranking hranking hcutoff hcutoffLeCard
        hanchorDelta hanchorDeltaLeOne hlower hantisymmetric hself hcomplete hsst
    simpa only [anchorLaw, canonicalFreshPickAnchorSourceGoodAnchorProbability,
      pmfProbClassical_eq_pmfProb] using hsource
  have hanchorFailure : pmfProb anchorLaw
      (fun anchor => ¬ GoodAnchor preferenceGap lower cutoff anchor) ≤ anchorDelta := by
    rw [pmfProb_compl]
    linarith
  have hpruneFailure :
      pmfProb (optMaximizeAnchorPruneTraceLaw roundCount anchorLaw pruneTraceLaw)
        (fun anchorStateFailure =>
          GoodAnchor preferenceGap lower cutoff anchorStateFailure.1 ∧
            ¬ candidateSuccess anchorStateFailure.1 anchorStateFailure.2) ≤
              1 / (Fintype.card Arm : ℝ) ^ 2 + pruneDelta / 2 := by
    apply optMaximizeAnchorPruneTraceLaw_goodAnchor_conditional_failure_le
      roundCount anchorLaw pruneTraceLaw (GoodAnchor preferenceGap lower cutoff)
      (fun anchor stateFailure => ¬ candidateSuccess anchor stateFailure)
      (1 / (Fintype.card Arm : ℝ) ^ 2 + pruneDelta / 2) (by positivity)
    intro anchor hgood
    have hcandidate :=
      canonicalFreshStoppedPruneTrace_lemma17_candidate_and_cost_success_probability_raw
      preferenceGap hprobability anchor maximum lower upper pruneDelta maxBatch cutoff hbudget Finset.univ
      hantisymmetric hsst hupperNonnegative hmaximumAbsolute hgood (Finset.mem_univ maximum)
      hseparation hpruneDelta hpruneDeltaHalf hcutoff hpruneCutoff.le
    change pmfProb (pruneTraceLaw anchor) (fun stateFailure =>
      ¬ candidateSuccess anchor stateFailure) ≤
        1 / (Fintype.card Arm : ℝ) ^ 2 + pruneDelta / 2
    rw [pmfProb_compl]
    have hcandidate' : 1 - (1 / (Fintype.card Arm : ℝ) ^ 2 + pruneDelta / 2) ≤
        pmfProb (pruneTraceLaw anchor) (candidateSuccess anchor) := by
      simpa only [pruneTraceLaw, candidateSuccess, roundCount] using hcandidate
    linarith
  change 1 - (anchorDelta + (1 / (Fintype.card Arm : ℝ) ^ 2 + pruneDelta / 2)) ≤
    pmfProb (optMaximizeAnchorPruneTraceLaw roundCount anchorLaw pruneTraceLaw)
      (fun anchorStateFailure =>
        GoodAnchor preferenceGap lower cutoff anchorStateFailure.1 ∧
          candidateSuccess anchorStateFailure.1 anchorStateFailure.2)
  exact optMaximizeAnchorPruneTraceLaw_success_probability_ge_one_sub_add
    roundCount anchorLaw pruneTraceLaw (GoodAnchor preferenceGap lower cutoff) candidateSuccess
    anchorDelta (1 / (Fintype.card Arm : ℝ) ^ 2 + pruneDelta / 2)
    hanchorFailure hpruneFailure

/-- If the whole population already meets Prune's stopping threshold, the
Prune trace and its source-rate resource event are deterministic.  The first
two Algorithm-3 phases then spend only Pick-Anchor's failure budget. -/
theorem canonicalOptMaximizeAnchorPruneTraceSource_success_probability_of_initial_small
    {Arm : Type*} [Fintype Arm] [Nonempty Arm] [DecidableEq Arm]
    (cutoff : ℕ) (anchorDelta pruneDelta lower upper : ℝ) (maxBatch : ℕ)
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
    (hbudget : ∀ round < sourcePruneRoundCount (Fintype.card Arm),
      fixedSampleBudget lower upper (adaptivePruneRoundDelta pruneDelta round) ≤ maxBatch)
    (hpruneDelta : 0 < pruneDelta) (hpruneDeltaLeOne : pruneDelta ≤ 1)
    (hsize : Fintype.card Arm ≤ 2 * cutoff) :
    1 - anchorDelta ≤
      canonicalOptMaximizeAnchorPruneTraceSourceSuccessProbability
        cutoff anchorDelta pruneDelta lower upper maxBatch preferenceGap maximum hprobability
        hcutoff hanchorDelta hanchorDeltaLeOne hbudget := by
  classical
  let roundCount := sourcePruneRoundCount (Fintype.card Arm)
  let anchorLaw : PMF Arm :=
    canonicalFreshPickAnchorSourceOutputLaw cutoff anchorDelta lower preferenceGap hprobability
      hcutoff hanchorDelta hanchorDeltaLeOne
  let pruneTraceLaw : Arm → PMF (stoppedPruneTraceState Arm roundCount × Bool) := fun anchor =>
    freshStoppedPruneTraceStateLaw preferenceGap lower
      (sourceLemma5PruneContractionFactor (Fintype.card Arm) cutoff pruneDelta)
      cutoff anchor Finset.univ
      (canonicalFreshPruneOutcomeLaw preferenceGap hprobability roundCount anchor
        lower upper pruneDelta maxBatch hbudget)
      (canonicalFreshPruneDecision roundCount lower upper pruneDelta maxBatch hbudget)
      roundCount
  let candidateSuccess : Arm → stoppedPruneTraceState Arm roundCount × Bool → Prop :=
    fun anchor stateFailure =>
      stateFailure.2 = false ∧ stateFailure.1.1.card ≤ 2 * cutoff ∧
        (stoppedPruneTraceComparisonCount roundCount cutoff lower upper pruneDelta
          stateFailure.1.2 : ℝ) ≤
          sourceLemma5PruneComparisonRateBound (Fintype.card Arm) lower upper pruneDelta ∧
        (EpsilonMaximum preferenceGap upper anchor ∨ maximum ∈ stateFailure.1.1)
  have hanchorSuccess : 1 - anchorDelta ≤
      pmfProb anchorLaw (GoodAnchor preferenceGap lower cutoff) := by
    have hsource :=
      canonicalFreshPickAnchorSourceOutputLaw_goodAnchor_highProbability_of_preferenceRanking
        cutoff anchorDelta lower preferenceGap hprobability ranking hranking hcutoff hcutoffLeCard
        hanchorDelta hanchorDeltaLeOne hlower hantisymmetric hself hcomplete hsst
    simpa only [anchorLaw, canonicalFreshPickAnchorSourceGoodAnchorProbability,
      pmfProbClassical_eq_pmfProb] using hsource
  have hanchorFailure : pmfProb anchorLaw
      (fun anchor => ¬ GoodAnchor preferenceGap lower cutoff anchor) ≤ anchorDelta := by
    rw [pmfProb_compl]
    linarith
  have hpruneFailure :
      pmfProb (optMaximizeAnchorPruneTraceLaw roundCount anchorLaw pruneTraceLaw)
        (fun anchorStateFailure =>
          GoodAnchor preferenceGap lower cutoff anchorStateFailure.1 ∧
            ¬ candidateSuccess anchorStateFailure.1 anchorStateFailure.2) ≤ 0 := by
    apply optMaximizeAnchorPruneTraceLaw_goodAnchor_conditional_failure_le
      roundCount anchorLaw pruneTraceLaw (GoodAnchor preferenceGap lower cutoff)
      (fun anchor stateFailure => ¬ candidateSuccess anchor stateFailure) 0 le_rfl
    intro anchor _
    have hone :=
      canonicalFreshStoppedPruneTrace_card_size_cost_and_max_probability_eq_one_of_initial_small
        preferenceGap hprobability anchor maximum lower upper pruneDelta maxBatch cutoff hbudget
        Finset.univ hpruneDelta hpruneDeltaLeOne (by simpa using hsize)
        (Finset.mem_univ maximum)
    have hcandidate : pmfProb (pruneTraceLaw anchor) (candidateSuccess anchor) = 1 := by
      apply le_antisymm (pmfProb_le_one _ _)
      calc
        1 = pmfProb (pruneTraceLaw anchor) (fun stateFailure =>
            stateFailure.2 = false ∧
              stateFailure.1.1.card ≤ 2 * cutoff ∧
              (stoppedPruneTraceComparisonCount roundCount cutoff lower upper pruneDelta
                stateFailure.1.2 : ℝ) ≤
                sourceLemma5PruneComparisonRateBound (Fintype.card Arm) lower upper pruneDelta ∧
              maximum ∈ stateFailure.1.1) := by
                simpa only [pruneTraceLaw, roundCount] using hone.symm
        _ ≤ pmfProb (pruneTraceLaw anchor) (candidateSuccess anchor) := by
          apply pmfProb_le_of_imp
          intro stateFailure hsuccess
          exact ⟨hsuccess.1, hsuccess.2.1, hsuccess.2.2.1, Or.inr hsuccess.2.2.2⟩
    change pmfProb (pruneTraceLaw anchor)
      (fun stateFailure => ¬ candidateSuccess anchor stateFailure) ≤ 0
    rw [pmfProb_compl, hcandidate]
    norm_num
  change 1 - anchorDelta ≤
    pmfProb (optMaximizeAnchorPruneTraceLaw roundCount anchorLaw pruneTraceLaw)
      (fun anchorStateFailure =>
        GoodAnchor preferenceGap lower cutoff anchorStateFailure.1 ∧
          candidateSuccess anchorStateFailure.1 anchorStateFailure.2)
  have hcompose := optMaximizeAnchorPruneTraceLaw_success_probability_ge_one_sub_add
    roundCount anchorLaw pruneTraceLaw (GoodAnchor preferenceGap lower cutoff) candidateSuccess
    anchorDelta 0 hanchorFailure hpruneFailure
  linarith

/--
The traditional Lemma-15 premise converts the raw inverse-square contraction
tail into the remaining half of Prune's confidence allocation.
-/
theorem canonicalOptMaximizeAnchorPruneTraceSource_success_probability
    {Arm : Type*} [Fintype Arm] [Nonempty Arm] [DecidableEq Arm]
    (cutoff : ℕ) (anchorDelta pruneDelta lower upper : ℝ) (maxBatch : ℕ)
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
    (hbudget : ∀ round < sourcePruneRoundCount (Fintype.card Arm),
      fixedSampleBudget lower upper (adaptivePruneRoundDelta pruneDelta round) ≤ maxBatch)
    (hupperNonnegative : 0 ≤ upper)
    (hmaximumAbsolute : AbsoluteMaximum preferenceGap maximum)
    (hseparation : lower < upper) (hpruneDelta : 0 < pruneDelta)
    (hpruneDeltaHalf : pruneDelta ≤ 1 / 2)
    (hpruneCutoff : Real.sqrt (6 * (Fintype.card Arm : ℝ) *
      Real.log (Fintype.card Arm : ℝ)) < (cutoff : ℝ))
    (hpruneDeltaLower : (cutoff : ℝ) / (Fintype.card Arm : ℝ) ≤ pruneDelta) :
    1 - (anchorDelta + pruneDelta) ≤
      canonicalOptMaximizeAnchorPruneTraceSourceSuccessProbability
        cutoff anchorDelta pruneDelta lower upper maxBatch preferenceGap maximum hprobability
        hcutoff hanchorDelta hanchorDeltaLeOne hbudget := by
  have hcardPosNat : 0 < Fintype.card Arm := Fintype.card_pos_iff.mpr inferInstance
  have hcardPos : 0 < (Fintype.card Arm : ℝ) := by exact_mod_cast hcardPosNat
  have hcardTwoNat : 2 ≤ Fintype.card Arm := by
    by_contra hnot
    have hcardOne : Fintype.card Arm = 1 := by omega
    have hcutoffOne : cutoff = 1 := by omega
    norm_num [hcardOne, hcutoffOne] at hpruneDeltaLower
    linarith
  have hcardTwo : (2 : ℝ) ≤ Fintype.card Arm := by exact_mod_cast hcardTwoNat
  have hcutoffOne : (1 : ℝ) ≤ cutoff := by exact_mod_cast hcutoff
  have htail : 1 / (Fintype.card Arm : ℝ) ^ 2 ≤ pruneDelta / 2 := by
    have hscale : 1 / (Fintype.card Arm : ℝ) ^ 2 ≤
        (cutoff : ℝ) / (2 * (Fintype.card Arm : ℝ)) := by
      apply (le_div_iff₀ (by positivity : 0 < 2 * (Fintype.card Arm : ℝ))).mpr
      field_simp [ne_of_gt hcardPos]
      nlinarith
    calc
      1 / (Fintype.card Arm : ℝ) ^ 2 ≤
          (cutoff : ℝ) / (2 * (Fintype.card Arm : ℝ)) := hscale
      _ = ((cutoff : ℝ) / (Fintype.card Arm : ℝ)) / 2 := by ring
      _ ≤ pruneDelta / 2 := by gcongr
  have hraw := canonicalOptMaximizeAnchorPruneTraceSource_success_probability_raw
    cutoff anchorDelta pruneDelta lower upper maxBatch preferenceGap maximum hprobability ranking
    hranking hcutoff hcutoffLeCard hanchorDelta hanchorDeltaLeOne hlower hantisymmetric hself
    hcomplete hsst hbudget hupperNonnegative hmaximumAbsolute hseparation hpruneDelta
    hpruneDeltaHalf hpruneCutoff
  exact (by linarith : 1 - (anchorDelta + pruneDelta) ≤
    1 - (anchorDelta + (1 / (Fintype.card Arm : ℝ) ^ 2 + pruneDelta / 2))).trans hraw

/--
The probability of the source finite comparison-cap event after Pick-Anchor
and trace-recording Prune, with the bounded fallback/final tail appended.
-/
noncomputable def canonicalOptMaximizeTraceAndTailComparisonCapProbability
    {Arm : Type*} [Fintype Arm] [Nonempty Arm] [DecidableEq Arm]
    (cutoff : ℕ) (anchorDelta pruneDelta lower upper finalEta fallbackEpsilon fallbackDelta : ℝ)
    (maxBatch : ℕ) (preferenceGap : Arm → Arm → ℝ) (maximum : Arm)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (hcutoff : 0 < cutoff) (hanchorDelta : 0 < anchorDelta)
    (hanchorDeltaLeOne : anchorDelta ≤ 1)
    (hbudget : ∀ round < sourcePruneRoundCount (Fintype.card Arm),
      fixedSampleBudget lower upper (adaptivePruneRoundDelta pruneDelta round) ≤ maxBatch) : ℝ := by
  classical
  exact pmfProb
    (canonicalOptMaximizeAnchorPruneTraceSourceLaw cutoff anchorDelta pruneDelta lower upper
      maxBatch preferenceGap hprobability maximum hcutoff hanchorDelta hanchorDeltaLeOne hbudget)
    (fun anchorStateFailure =>
      GoodAnchor preferenceGap lower cutoff anchorStateFailure.1 ∧
        anchorStateFailure.2.2 = false ∧
          anchorStateFailure.2.1.1.card ≤ 2 * cutoff ∧
          (EpsilonMaximum preferenceGap upper anchorStateFailure.1 ∨
            maximum ∈ anchorStateFailure.2.1.1) ∧
          (optMaximizeTraceAndTailComparisonCap cutoff anchorDelta pruneDelta lower upper
            finalEta fallbackEpsilon fallbackDelta anchorStateFailure.2.1.2
            anchorStateFailure.2.1.1 : ℝ) ≤
            (optMaximizePickAnchorComparisonCap (Arm := Arm) cutoff anchorDelta lower : ℝ) +
              sourceLemma5PruneComparisonRateBound (Fintype.card Arm) lower upper pruneDelta +
              (optMaximizeFinalTailComparisonCap anchorStateFailure.2.1.1 lower upper
                finalEta fallbackEpsilon fallbackDelta : ℝ))

/--
The first-two-phase source failure budget controls the complete finite cap
obtained by appending Algorithm 3's independently bounded tail.
-/
theorem canonicalOptMaximizeTraceAndTailComparisonCap_probability
    {Arm : Type*} [Fintype Arm] [Nonempty Arm] [DecidableEq Arm]
    (cutoff : ℕ) (anchorDelta pruneDelta lower upper finalEta fallbackEpsilon fallbackDelta : ℝ)
    (maxBatch : ℕ) (preferenceGap : Arm → Arm → ℝ) (maximum : Arm)
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
    (hbudget : ∀ round < sourcePruneRoundCount (Fintype.card Arm),
      fixedSampleBudget lower upper (adaptivePruneRoundDelta pruneDelta round) ≤ maxBatch)
    (hupperNonnegative : 0 ≤ upper)
    (hmaximumAbsolute : AbsoluteMaximum preferenceGap maximum)
    (hseparation : lower < upper) (hpruneDelta : 0 < pruneDelta)
    (hpruneDeltaHalf : pruneDelta ≤ 1 / 2)
    (hpruneCutoff : Real.sqrt (6 * (Fintype.card Arm : ℝ) *
      Real.log (Fintype.card Arm : ℝ)) < (cutoff : ℝ))
    (hpruneDeltaLower : (cutoff : ℝ) / (Fintype.card Arm : ℝ) ≤ pruneDelta) :
    1 - (anchorDelta + pruneDelta) ≤
      canonicalOptMaximizeTraceAndTailComparisonCapProbability cutoff anchorDelta pruneDelta
        lower upper finalEta fallbackEpsilon fallbackDelta maxBatch preferenceGap maximum
        hprobability hcutoff hanchorDelta hanchorDeltaLeOne hbudget := by
  classical
  have hprior := canonicalOptMaximizeAnchorPruneTraceSource_success_probability
    cutoff anchorDelta pruneDelta lower upper maxBatch preferenceGap maximum hprobability ranking
    hranking hcutoff hcutoffLeCard hanchorDelta hanchorDeltaLeOne hlower hantisymmetric hself
    hcomplete hsst hbudget hupperNonnegative hmaximumAbsolute hseparation hpruneDelta
    hpruneDeltaHalf hpruneCutoff hpruneDeltaLower
  unfold canonicalOptMaximizeTraceAndTailComparisonCapProbability
  apply optMaximizeTraceAndTailComparisonCap_probability_of_priorSuccess
  simpa only [canonicalOptMaximizeAnchorPruneTraceSourceSuccessProbability] using hprior

/-- The source trace law projects exactly to its source-horizon active-set law. -/
theorem canonicalOptMaximizeAnchorPruneTraceSourceLaw_map_activeLaw
    {Arm : Type*} [Fintype Arm] [Nonempty Arm] [DecidableEq Arm]
    (cutoff : ℕ) (anchorDelta pruneDelta lower upper : ℝ) (maxBatch : ℕ)
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (maximum : Arm)
    (hcutoff : 0 < cutoff) (hanchorDelta : 0 < anchorDelta)
    (hanchorDeltaLeOne : anchorDelta ≤ 1)
    (hbudget : ∀ round < sourcePruneRoundCount (Fintype.card Arm),
      fixedSampleBudget lower upper (adaptivePruneRoundDelta pruneDelta round) ≤ maxBatch) :
    (canonicalOptMaximizeAnchorPruneTraceSourceLaw cutoff anchorDelta pruneDelta lower upper maxBatch
      preferenceGap hprobability maximum hcutoff hanchorDelta hanchorDeltaLeOne hbudget).map
      (fun anchorStateFailure => (anchorStateFailure.1, anchorStateFailure.2.1.1)) =
      canonicalOptMaximizeAnchorPruneSourceLogActiveLaw cutoff anchorDelta pruneDelta lower upper
        maxBatch preferenceGap hprobability hcutoff hanchorDelta hanchorDeltaLeOne hbudget := by
  classical
  unfold canonicalOptMaximizeAnchorPruneTraceSourceLaw
    canonicalOptMaximizeAnchorPruneSourceLogActiveLaw
  apply optMaximizeAnchorPruneTraceLaw_map_activeLaw
  intro anchor
  exact
      freshStoppedPruneTraceStateLaw_map_activeLaw preferenceGap lower
      (sourceLemma5PruneContractionFactor (Fintype.card Arm) cutoff pruneDelta)
      cutoff anchor Finset.univ
      (canonicalFreshPruneOutcomeLaw preferenceGap hprobability
        (sourcePruneRoundCount (Fintype.card Arm)) anchor lower upper pruneDelta maxBatch hbudget)
      (canonicalFreshPruneDecision (sourcePruneRoundCount (Fintype.card Arm))
        lower upper pruneDelta maxBatch hbudget)
      (sourcePruneRoundCount (Fintype.card Arm))

/-- Sample the fallback conditionally on the realized Pick-Anchor--Prune trace. -/
noncomputable def optMaximizeAnchorPruneTraceFallbackLaw
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (roundCount : ℕ) (anchorLaw : PMF Arm)
    (pruneTraceLaw : Arm → PMF (stoppedPruneTraceState Arm roundCount × Bool))
    (fallbackLaw : Arm → Finset Arm → PMF Arm) :
    PMF ((Arm × (stoppedPruneTraceState Arm roundCount × Bool)) × Arm) := by
  classical
  exact (optMaximizeAnchorPruneTraceLaw roundCount anchorLaw pruneTraceLaw).bind
    fun anchorStateFailure =>
      (fallbackLaw anchorStateFailure.1 anchorStateFailure.2.1.1).map fun fallback =>
        (anchorStateFailure, fallback)

/--
The complete non-base execution keeps the Pick-Anchor--Prune trace while
sampling the fallback and final-loop outputs conditionally on that realized
trace.  Thus all four Algorithm-3 phases live on one finite PMF.
-/
noncomputable def optMaximizeAnchorPruneTraceFallbackFinalLaw
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (roundCount : ℕ) (anchorLaw : PMF Arm)
    (pruneTraceLaw : Arm → PMF (stoppedPruneTraceState Arm roundCount × Bool))
    (fallbackLaw : Arm → Finset Arm → PMF Arm)
    (finalLaw : Arm → Finset Arm → Arm → PMF Arm) :
    PMF (((Arm × (stoppedPruneTraceState Arm roundCount × Bool)) × Arm) × Arm) := by
  classical
  exact (optMaximizeAnchorPruneTraceFallbackLaw roundCount anchorLaw pruneTraceLaw fallbackLaw).bind
    fun traceFallback =>
      (finalLaw traceFallback.1.1 traceFallback.1.2.1.1 traceFallback.2).map
        fun output => (traceFallback, output)

/--
The returned-arm marginal of the trace-carrying execution is determined only
by the anchor and retained candidate set.  Any auxiliary trace flag therefore
erases before the fallback and final phases are compared to their ordinary
four-phase law.
-/
theorem optMaximizeAnchorPruneTraceFallbackFinalLaw_map_output_eq
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (roundCount : ℕ) (anchorLaw : PMF Arm)
    (pruneTraceLaw : Arm → PMF (stoppedPruneTraceState Arm roundCount × Bool))
    (pruneLaw : Arm → PMF (Finset Arm))
    (fallbackLaw : Arm → Finset Arm → PMF Arm)
    (finalLaw : Arm → Finset Arm → Arm → PMF Arm)
    (hactive : ∀ anchor,
      (pruneTraceLaw anchor).map (fun stateFailure => stateFailure.1.1) = pruneLaw anchor) :
    (optMaximizeAnchorPruneTraceFallbackFinalLaw roundCount anchorLaw pruneTraceLaw fallbackLaw
      finalLaw).map Prod.snd =
      (optMaximizeAnchorPruneFallbackFinalLaw anchorLaw pruneLaw fallbackLaw finalLaw).map Prod.snd := by
  classical
  let traceLaw := optMaximizeAnchorPruneTraceLaw roundCount anchorLaw pruneTraceLaw
  let ordinaryLaw := optMaximizeAnchorPruneLaw anchorLaw pruneLaw
  let eraseTrace : Arm × (stoppedPruneTraceState Arm roundCount × Bool) → Arm × Finset Arm :=
    fun anchorStateFailure => (anchorStateFailure.1, anchorStateFailure.2.1.1)
  let tailLaw : Arm × Finset Arm → PMF Arm := fun anchorCandidates =>
    (fallbackLaw anchorCandidates.1 anchorCandidates.2).bind fun fallback =>
      (finalLaw anchorCandidates.1 anchorCandidates.2 fallback).map id
  have htrace :
      (optMaximizeAnchorPruneTraceFallbackFinalLaw roundCount anchorLaw pruneTraceLaw fallbackLaw
        finalLaw).map Prod.snd = traceLaw.bind (tailLaw ∘ eraseTrace) := by
    unfold optMaximizeAnchorPruneTraceFallbackFinalLaw
      optMaximizeAnchorPruneTraceFallbackLaw traceLaw tailLaw eraseTrace
    rw [PMF.map_bind]
    simp_rw [PMF.bind_bind, PMF.bind_map]
    simp_rw [PMF.map_comp]
    rfl
  have hord :
      (optMaximizeAnchorPruneFallbackFinalLaw anchorLaw pruneLaw fallbackLaw finalLaw).map Prod.snd =
        ordinaryLaw.bind tailLaw := by
    unfold optMaximizeAnchorPruneFallbackFinalLaw optMaximizeAnchorPruneFallbackLaw
      ordinaryLaw tailLaw
    rw [PMF.map_bind]
    simp_rw [PMF.bind_bind, PMF.bind_map]
    simp_rw [PMF.map_comp]
    rfl
  have hmap : traceLaw.map eraseTrace = ordinaryLaw := by
    dsimp only [traceLaw, eraseTrace, ordinaryLaw]
    exact optMaximizeAnchorPruneTraceLaw_map_activeLaw roundCount anchorLaw pruneTraceLaw pruneLaw
      hactive
  calc
    (optMaximizeAnchorPruneTraceFallbackFinalLaw roundCount anchorLaw pruneTraceLaw fallbackLaw
      finalLaw).map Prod.snd = traceLaw.bind (tailLaw ∘ eraseTrace) := htrace
    _ = (traceLaw.map eraseTrace).bind tailLaw := by rw [PMF.bind_map]
    _ = ordinaryLaw.bind tailLaw := by rw [hmap]
    _ = (optMaximizeAnchorPruneFallbackFinalLaw anchorLaw pruneLaw fallbackLaw finalLaw).map Prod.snd :=
      hord.symm

noncomputable local instance (priority := 100) classicalDecidableEq (α : Type*) : DecidableEq α :=
  Classical.decEq α

/-- The complete final-loop trace is indexed by its realized Pick/Prune/fallback history. -/
abbrev optMaximizeAnchorPruneTraceFallbackFinalTraceState {Arm : Type*} [DecidableEq Arm]
    (roundCount : ℕ) :=
  Sigma fun traceFallback : (Arm × (stoppedPruneTraceState Arm roundCount × Bool)) × Arm =>
    finalCheckTraceState traceFallback.1.2.1.1

/--
The four-phase execution with a queried-prefix trace for the early-stopping
final loop.  The fallback outcome is pre-sampled conditionally on Prune but
its comparison count is charged only when a final upper decision invokes it.
-/
noncomputable def optMaximizeAnchorPruneTraceFallbackFinalTraceLaw
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (roundCount : ℕ) (anchorLaw : PMF Arm)
    (pruneTraceLaw : Arm → PMF (stoppedPruneTraceState Arm roundCount × Bool))
    (fallbackLaw : Arm → Finset Arm → PMF Arm)
    (finalTraceLaw : (anchor : Arm) → (candidates : Finset Arm) → (fallback : Arm) →
      PMF (finalCheckTraceState candidates)) :
    PMF (optMaximizeAnchorPruneTraceFallbackFinalTraceState (Arm := Arm) roundCount) := by
  classical
  exact (optMaximizeAnchorPruneTraceFallbackLaw roundCount anchorLaw pruneTraceLaw fallbackLaw).bind
    fun traceFallback =>
      (finalTraceLaw traceFallback.1.1 traceFallback.1.2.1.1 traceFallback.2).map
        fun finalTraceState => Sigma.mk traceFallback finalTraceState

/-- The returned arm selected by a final-loop queried-prefix trace. -/
noncomputable def optMaximizeAnchorPruneTraceFallbackFinalTraceOutputLaw
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (roundCount : ℕ) (anchorLaw : PMF Arm)
    (pruneTraceLaw : Arm → PMF (stoppedPruneTraceState Arm roundCount × Bool))
    (fallbackLaw : Arm → Finset Arm → PMF Arm)
    (finalTraceLaw : (anchor : Arm) → (candidates : Finset Arm) → (fallback : Arm) →
      PMF (finalCheckTraceState candidates)) : PMF Arm :=
  (optMaximizeAnchorPruneTraceFallbackFinalTraceLaw roundCount anchorLaw pruneTraceLaw fallbackLaw
    finalTraceLaw).map fun traceFallbackFinalTrace =>
      if traceFallbackFinalTrace.2.2 then traceFallbackFinalTrace.1.1.1 else
        traceFallbackFinalTrace.1.2

/--
The literal source-batch count on a final-loop trace.  The fallback term is
zero on the anchor-return path and otherwise has its exact Seq-Eliminate
batch allocation; the final term counts only the queried prefix.
-/
noncomputable def optMaximizeTraceFallbackFinalTraceComparisonCount
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (cutoff : ℕ) (anchorDelta pruneDelta lower upper finalEta fallbackEpsilon fallbackDelta : ℝ)
    (traceFallbackFinalTrace :
      optMaximizeAnchorPruneTraceFallbackFinalTraceState (Arm := Arm)
        (sourcePruneRoundCount (Fintype.card Arm))) : ℕ :=
  optMaximizePickAnchorComparisonCap (Arm := Arm) cutoff anchorDelta lower +
    stoppedPruneTraceComparisonCount (sourcePruneRoundCount (Fintype.card Arm))
      cutoff lower upper pruneDelta traceFallbackFinalTrace.1.1.2.1.2 +
    (if traceFallbackFinalTrace.2.2 then 0 else
      optMaximizeFallbackComparisonCap traceFallbackFinalTrace.1.1.2.1.1
        fallbackEpsilon fallbackDelta) +
    finalCheckTraceComparisonCount traceFallbackFinalTrace.1.1.2.1.1 lower upper finalEta
      traceFallbackFinalTrace.2.1

/-- The literal final-loop trace count is bounded by the established tail cap. -/
theorem optMaximizeTraceFallbackFinalTraceComparisonCount_le_cap
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (cutoff : ℕ) (anchorDelta pruneDelta lower upper finalEta fallbackEpsilon fallbackDelta : ℝ)
    (traceFallbackFinalTrace :
      optMaximizeAnchorPruneTraceFallbackFinalTraceState (Arm := Arm)
        (sourcePruneRoundCount (Fintype.card Arm))) :
    optMaximizeTraceFallbackFinalTraceComparisonCount cutoff anchorDelta pruneDelta lower upper
      finalEta fallbackEpsilon fallbackDelta traceFallbackFinalTrace ≤
      optMaximizeTraceAndTailComparisonCap cutoff anchorDelta pruneDelta lower upper finalEta
        fallbackEpsilon fallbackDelta traceFallbackFinalTrace.1.1.2.1.2
        traceFallbackFinalTrace.1.1.2.1.1 := by
  unfold optMaximizeTraceFallbackFinalTraceComparisonCount
    optMaximizeTraceAndTailComparisonCap optMaximizeFinalTailComparisonCap
  have hfinal := finalCheckTraceComparisonCount_le_cap traceFallbackFinalTrace.1.1.2.1.1
    lower upper finalEta traceFallbackFinalTrace.2.1
  by_cases hnoUpper : traceFallbackFinalTrace.2.2
  · simp [hnoUpper]
    omega
  · simp [hnoUpper]
    omega

/--
Replacing a final output PMF by a prefix-trace PMF preserves the returned-arm
law whenever each trace projects to that final output law.
-/
theorem optMaximizeAnchorPruneTraceFallbackFinalTraceOutputLaw_eq
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (roundCount : ℕ) (anchorLaw : PMF Arm)
    (pruneTraceLaw : Arm → PMF (stoppedPruneTraceState Arm roundCount × Bool))
    (fallbackLaw : Arm → Finset Arm → PMF Arm)
    (finalTraceLaw : (anchor : Arm) → (candidates : Finset Arm) → (fallback : Arm) →
      PMF (finalCheckTraceState candidates))
    (finalLaw : Arm → Finset Arm → Arm → PMF Arm)
    (hfinal : ∀ anchor candidates fallback,
      (finalTraceLaw anchor candidates fallback).map
        (fun finalTraceState => if finalTraceState.2 then anchor else fallback) =
          finalLaw anchor candidates fallback) :
    optMaximizeAnchorPruneTraceFallbackFinalTraceOutputLaw roundCount anchorLaw pruneTraceLaw
      fallbackLaw finalTraceLaw =
      (optMaximizeAnchorPruneTraceFallbackFinalLaw roundCount anchorLaw pruneTraceLaw fallbackLaw
        finalLaw).map Prod.snd := by
  classical
  let traceFallbackLaw :=
    optMaximizeAnchorPruneTraceFallbackLaw roundCount anchorLaw pruneTraceLaw fallbackLaw
  have htrace :
      optMaximizeAnchorPruneTraceFallbackFinalTraceOutputLaw roundCount anchorLaw pruneTraceLaw
        fallbackLaw finalTraceLaw =
      traceFallbackLaw.bind fun traceFallback =>
        (finalTraceLaw traceFallback.1.1 traceFallback.1.2.1.1 traceFallback.2).map
          (fun finalTraceState => if finalTraceState.2 then traceFallback.1.1 else
            traceFallback.2) := by
    unfold optMaximizeAnchorPruneTraceFallbackFinalTraceOutputLaw
      optMaximizeAnchorPruneTraceFallbackFinalTraceLaw
    rw [PMF.map_bind]
    simp_rw [PMF.map_comp]
    rfl
  have hnormal :
      (optMaximizeAnchorPruneTraceFallbackFinalLaw roundCount anchorLaw pruneTraceLaw fallbackLaw
        finalLaw).map Prod.snd =
      traceFallbackLaw.bind fun traceFallback =>
        (finalLaw traceFallback.1.1 traceFallback.1.2.1.1 traceFallback.2).map id := by
    unfold optMaximizeAnchorPruneTraceFallbackFinalLaw traceFallbackLaw
    rw [PMF.map_bind]
    simp_rw [PMF.map_comp]
    rfl
  calc
    optMaximizeAnchorPruneTraceFallbackFinalTraceOutputLaw roundCount anchorLaw pruneTraceLaw
        fallbackLaw finalTraceLaw =
      traceFallbackLaw.bind fun traceFallback =>
        (finalTraceLaw traceFallback.1.1 traceFallback.1.2.1.1 traceFallback.2).map
          (fun finalTraceState => if finalTraceState.2 then traceFallback.1.1 else
            traceFallback.2) := htrace
    _ = traceFallbackLaw.bind fun traceFallback =>
        finalLaw traceFallback.1.1 traceFallback.1.2.1.1 traceFallback.2 := by
      congr 1
      funext traceFallback
      exact hfinal traceFallback.1.1 traceFallback.1.2.1.1 traceFallback.2
    _ = traceFallbackLaw.bind fun traceFallback =>
        (finalLaw traceFallback.1.1 traceFallback.1.2.1.1 traceFallback.2).map id := by
      congr 1
      funext traceFallback
      symm
      exact PMF.map_id _
    _ = (optMaximizeAnchorPruneTraceFallbackFinalLaw roundCount anchorLaw pruneTraceLaw fallbackLaw
      finalLaw).map Prod.snd := hnormal.symm

/--
Keeping the complete Pick--Prune--fallback history while projecting a final
queried-prefix trace to its returned arm recovers the ordinary four-phase
execution law.  The stronger history-preserving form supports joint events.
-/
theorem optMaximizeAnchorPruneTraceFallbackFinalTraceLaw_map_history_output_eq
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (roundCount : ℕ) (anchorLaw : PMF Arm)
    (pruneTraceLaw : Arm → PMF (stoppedPruneTraceState Arm roundCount × Bool))
    (fallbackLaw : Arm → Finset Arm → PMF Arm)
    (finalTraceLaw : (anchor : Arm) → (candidates : Finset Arm) → (fallback : Arm) →
      PMF (finalCheckTraceState candidates))
    (finalLaw : Arm → Finset Arm → Arm → PMF Arm)
    (hfinal : ∀ anchor candidates fallback,
      (finalTraceLaw anchor candidates fallback).map
        (fun finalTraceState => if finalTraceState.2 then anchor else fallback) =
          finalLaw anchor candidates fallback) :
    (optMaximizeAnchorPruneTraceFallbackFinalTraceLaw roundCount anchorLaw pruneTraceLaw fallbackLaw
      finalTraceLaw).map (fun traceFallbackFinalTrace =>
        (traceFallbackFinalTrace.1,
          if traceFallbackFinalTrace.2.2 then traceFallbackFinalTrace.1.1.1 else
            traceFallbackFinalTrace.1.2)) =
      optMaximizeAnchorPruneTraceFallbackFinalLaw roundCount anchorLaw pruneTraceLaw fallbackLaw
        finalLaw := by
  classical
  unfold optMaximizeAnchorPruneTraceFallbackFinalTraceLaw
    optMaximizeAnchorPruneTraceFallbackFinalLaw
  rw [PMF.map_bind]
  simp_rw [PMF.map_comp]
  congr 1
  funext traceFallback
  calc
    (finalTraceLaw traceFallback.1.1 traceFallback.1.2.1.1 traceFallback.2).map
        (fun finalTraceState =>
          (traceFallback, if finalTraceState.2 then traceFallback.1.1 else traceFallback.2)) =
        ((finalTraceLaw traceFallback.1.1 traceFallback.1.2.1.1 traceFallback.2).map
          (fun finalTraceState => if finalTraceState.2 then traceFallback.1.1 else
            traceFallback.2)).map (fun output => (traceFallback, output)) := by
          rw [PMF.map_comp]
          rfl
    _ = (finalLaw traceFallback.1.1 traceFallback.1.2.1.1 traceFallback.2).map
        (fun output => (traceFallback, output)) := by
          rw [hfinal traceFallback.1.1 traceFallback.1.2.1.1 traceFallback.2]

/-- An event fixed before the final loop has the same probability after its prefix trace is sampled. -/
theorem optMaximizeAnchorPruneTraceFallbackFinalTraceLaw_traceFallback_probability
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (roundCount : ℕ) (anchorLaw : PMF Arm)
    (pruneTraceLaw : Arm → PMF (stoppedPruneTraceState Arm roundCount × Bool))
    (fallbackLaw : Arm → Finset Arm → PMF Arm)
    (finalTraceLaw : (anchor : Arm) → (candidates : Finset Arm) → (fallback : Arm) →
      PMF (finalCheckTraceState candidates))
    (event : (Arm × (stoppedPruneTraceState Arm roundCount × Bool)) × Arm → Prop)
    [DecidablePred event] :
    pmfProb (optMaximizeAnchorPruneTraceFallbackFinalTraceLaw roundCount anchorLaw pruneTraceLaw
      fallbackLaw finalTraceLaw)
      (fun traceFallbackFinalTrace => event traceFallbackFinalTrace.1) =
      pmfProb (optMaximizeAnchorPruneTraceFallbackLaw roundCount anchorLaw pruneTraceLaw fallbackLaw)
        event := by
  classical
  unfold optMaximizeAnchorPruneTraceFallbackFinalTraceLaw
  rw [pmfProb_bind]
  simp_rw [pmfProb_map]
  unfold pmfProb
  apply pmfExp_congr
  intro traceFallback
  by_cases hevent : event traceFallback <;> simp [hevent, pmfExp_const]

/--
Algorithm 3's source-horizon non-base execution, with one state recording
the Prune trace and the conditional fallback and final-loop outcomes.
-/
noncomputable def canonicalOptMaximizeTraceFallbackFinalSourceLaw
    {Arm : Type*} [Fintype Arm] [Nonempty Arm] [DecidableEq Arm]
    (cutoff : ℕ)
    (anchorDelta pruneDelta fallbackDelta finalDelta lower upper epsilon : ℝ) (maxBatch : ℕ)
    (preferenceGap : Arm → Arm → ℝ) (maximum : Arm)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (hcutoff : 0 < cutoff) (hanchorDelta : 0 < anchorDelta)
    (hanchorDeltaLeOne : anchorDelta ≤ 1)
    (hbudget : ∀ round < sourcePruneRoundCount (Fintype.card Arm),
      fixedSampleBudget lower upper (adaptivePruneRoundDelta pruneDelta round) ≤ maxBatch) :
    PMF (((Arm × (stoppedPruneTraceState Arm (sourcePruneRoundCount (Fintype.card Arm)) × Bool)) × Arm) ×
      Arm) := by
  classical
  exact optMaximizeAnchorPruneTraceFallbackFinalLaw
    (sourcePruneRoundCount (Fintype.card Arm))
    (canonicalFreshPickAnchorSourceOutputLaw cutoff anchorDelta lower preferenceGap hprobability
      hcutoff hanchorDelta hanchorDeltaLeOne)
    (fun anchor =>
      freshStoppedPruneTraceStateLaw preferenceGap lower
        (sourceLemma5PruneContractionFactor (Fintype.card Arm) cutoff pruneDelta)
        cutoff anchor Finset.univ
        (canonicalFreshPruneOutcomeLaw preferenceGap hprobability
          (sourcePruneRoundCount (Fintype.card Arm)) anchor lower upper pruneDelta maxBatch hbudget)
        (canonicalFreshPruneDecision (sourcePruneRoundCount (Fintype.card Arm))
          lower upper pruneDelta maxBatch hbudget)
        (sourcePruneRoundCount (Fintype.card Arm)))
    (fun anchor candidates => canonicalFreshFinsetSeqEliminateOutputLaw anchor candidates
      preferenceGap hprobability epsilon (fallbackDelta / (candidates.card : ℝ)))
    (fun anchor candidates fallback => canonicalFreshFinalCheckOutputLaw anchor fallback candidates
      preferenceGap hprobability upper epsilon (finalDelta / (Fintype.card Arm : ℝ)))

/--
The source-horizon four-phase execution with the final loop's literal
early-stopping queried-prefix trace.
-/
noncomputable def canonicalOptMaximizeTraceFallbackFinalTraceSourceLaw
    {Arm : Type*} [Fintype Arm] [Nonempty Arm] [DecidableEq Arm]
    (cutoff : ℕ)
    (anchorDelta pruneDelta fallbackDelta finalDelta lower upper epsilon : ℝ) (maxBatch : ℕ)
    (preferenceGap : Arm → Arm → ℝ) (maximum : Arm)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (hcutoff : 0 < cutoff) (hanchorDelta : 0 < anchorDelta)
    (hanchorDeltaLeOne : anchorDelta ≤ 1)
    (hbudget : ∀ round < sourcePruneRoundCount (Fintype.card Arm),
      fixedSampleBudget lower upper (adaptivePruneRoundDelta pruneDelta round) ≤ maxBatch) :
    PMF (optMaximizeAnchorPruneTraceFallbackFinalTraceState (Arm := Arm)
      (sourcePruneRoundCount (Fintype.card Arm))) := by
  classical
  exact optMaximizeAnchorPruneTraceFallbackFinalTraceLaw
    (sourcePruneRoundCount (Fintype.card Arm))
    (canonicalFreshPickAnchorSourceOutputLaw cutoff anchorDelta lower preferenceGap hprobability
      hcutoff hanchorDelta hanchorDeltaLeOne)
    (fun anchor =>
      freshStoppedPruneTraceStateLaw preferenceGap lower
        (sourceLemma5PruneContractionFactor (Fintype.card Arm) cutoff pruneDelta)
        cutoff anchor Finset.univ
        (canonicalFreshPruneOutcomeLaw preferenceGap hprobability
          (sourcePruneRoundCount (Fintype.card Arm)) anchor lower upper pruneDelta maxBatch hbudget)
        (canonicalFreshPruneDecision (sourcePruneRoundCount (Fintype.card Arm))
          lower upper pruneDelta maxBatch hbudget)
        (sourcePruneRoundCount (Fintype.card Arm)))
    (fun anchor candidates => canonicalFreshFinsetSeqEliminateOutputLaw anchor candidates
      preferenceGap hprobability epsilon (fallbackDelta / (candidates.card : ℝ)))
    (fun anchor candidates fallback => canonicalFreshFinalCheckTraceLaw anchor candidates preferenceGap
      hprobability upper epsilon (finalDelta / (Fintype.card Arm : ℝ)))

/-- The returned-arm law of the source early-stopping final-loop trace. -/
noncomputable def canonicalOptMaximizeTraceFallbackFinalTraceSourceOutputLaw
    {Arm : Type*} [Fintype Arm] [Nonempty Arm] [DecidableEq Arm]
    (cutoff : ℕ)
    (anchorDelta pruneDelta fallbackDelta finalDelta lower upper epsilon : ℝ) (maxBatch : ℕ)
    (preferenceGap : Arm → Arm → ℝ) (maximum : Arm)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (hcutoff : 0 < cutoff) (hanchorDelta : 0 < anchorDelta)
    (hanchorDeltaLeOne : anchorDelta ≤ 1)
    (hbudget : ∀ round < sourcePruneRoundCount (Fintype.card Arm),
      fixedSampleBudget lower upper (adaptivePruneRoundDelta pruneDelta round) ≤ maxBatch) : PMF Arm := by
  classical
  exact (canonicalOptMaximizeTraceFallbackFinalTraceSourceLaw cutoff anchorDelta pruneDelta
    fallbackDelta finalDelta lower upper epsilon maxBatch preferenceGap maximum hprobability hcutoff
    hanchorDelta hanchorDeltaLeOne hbudget).map fun traceFallbackFinalTrace =>
      if traceFallbackFinalTrace.2.2 then traceFallbackFinalTrace.1.1.1 else
        traceFallbackFinalTrace.1.2

/-- The returned-arm law of the early-stopping final trace is the established four-phase law. -/
theorem canonicalOptMaximizeTraceFallbackFinalTraceSourceOutputLaw_eq
    {Arm : Type*} [Fintype Arm] [Nonempty Arm] [DecidableEq Arm]
    (cutoff : ℕ)
    (anchorDelta pruneDelta fallbackDelta finalDelta lower upper epsilon : ℝ) (maxBatch : ℕ)
    (preferenceGap : Arm → Arm → ℝ) (maximum : Arm)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (hcutoff : 0 < cutoff) (hanchorDelta : 0 < anchorDelta)
    (hanchorDeltaLeOne : anchorDelta ≤ 1)
    (hbudget : ∀ round < sourcePruneRoundCount (Fintype.card Arm),
      fixedSampleBudget lower upper (adaptivePruneRoundDelta pruneDelta round) ≤ maxBatch) :
    canonicalOptMaximizeTraceFallbackFinalTraceSourceOutputLaw cutoff anchorDelta pruneDelta
      fallbackDelta finalDelta lower upper epsilon maxBatch preferenceGap maximum hprobability hcutoff
      hanchorDelta hanchorDeltaLeOne hbudget =
      (canonicalOptMaximizeTraceFallbackFinalSourceLaw cutoff anchorDelta pruneDelta fallbackDelta
        finalDelta lower upper epsilon maxBatch preferenceGap maximum hprobability hcutoff hanchorDelta
        hanchorDeltaLeOne hbudget).map Prod.snd := by
  unfold canonicalOptMaximizeTraceFallbackFinalTraceSourceOutputLaw
    canonicalOptMaximizeTraceFallbackFinalTraceSourceLaw
  apply optMaximizeAnchorPruneTraceFallbackFinalTraceOutputLaw_eq
  intro anchor candidates fallback
  exact canonicalFreshFinalCheckTraceOutputLaw_eq anchor fallback candidates preferenceGap hprobability
    upper epsilon (finalDelta / (Fintype.card Arm : ℝ))

/--
The uninstrumented source-log non-base output law.  It uses the same actual
Pick-Anchor, Prune, fallback, and final-check kernels, without an
absolute-maximum analysis flag in its state.
-/
noncomputable def canonicalOptMaximizeSourceLogFinalOutputLaw
    {Arm : Type*} [Fintype Arm] [Nonempty Arm] [DecidableEq Arm]
    (cutoff : ℕ)
    (anchorDelta pruneDelta fallbackDelta finalDelta lower upper epsilon : ℝ) (maxBatch : ℕ)
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (hcutoff : 0 < cutoff) (hanchorDelta : 0 < anchorDelta)
    (hanchorDeltaLeOne : anchorDelta ≤ 1)
    (hbudget : ∀ round < sourcePruneRoundCount (Fintype.card Arm),
      fixedSampleBudget lower upper (adaptivePruneRoundDelta pruneDelta round) ≤ maxBatch) : PMF Arm := by
  classical
  exact (optMaximizeAnchorPruneFallbackFinalLaw
    (canonicalFreshPickAnchorSourceOutputLaw cutoff anchorDelta lower preferenceGap hprobability
      hcutoff hanchorDelta hanchorDeltaLeOne)
    (fun anchor => freshStoppedPruneActiveLaw Finset.univ
      (canonicalFreshPruneOutcomeLaw preferenceGap hprobability
          (sourcePruneRoundCount (Fintype.card Arm)) anchor lower upper pruneDelta maxBatch hbudget)
      cutoff
      (canonicalFreshPruneDecision (sourcePruneRoundCount (Fintype.card Arm))
        lower upper pruneDelta maxBatch hbudget)
      (sourcePruneRoundCount (Fintype.card Arm)))
    (fun anchor candidates => canonicalFreshFinsetSeqEliminateOutputLaw anchor candidates
      preferenceGap hprobability epsilon (fallbackDelta / (candidates.card : ℝ)))
    (fun anchor candidates fallback => canonicalFreshFinalCheckOutputLaw anchor fallback candidates
      preferenceGap hprobability upper epsilon (finalDelta / (Fintype.card Arm : ℝ)))).map Prod.snd

/--
The instrumented stopped-Prune trace has the same returned-arm marginal as
the uninstrumented source-log Algorithm-3 non-base execution.
-/
theorem canonicalOptMaximizeTraceFallbackFinalSourceLaw_map_output_eq
    {Arm : Type*} [Fintype Arm] [Nonempty Arm] [DecidableEq Arm]
    (cutoff : ℕ)
    (anchorDelta pruneDelta fallbackDelta finalDelta lower upper epsilon : ℝ) (maxBatch : ℕ)
    (preferenceGap : Arm → Arm → ℝ) (maximum : Arm)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (hcutoff : 0 < cutoff) (hanchorDelta : 0 < anchorDelta)
    (hanchorDeltaLeOne : anchorDelta ≤ 1)
    (hbudget : ∀ round < sourcePruneRoundCount (Fintype.card Arm),
      fixedSampleBudget lower upper (adaptivePruneRoundDelta pruneDelta round) ≤ maxBatch) :
    (canonicalOptMaximizeTraceFallbackFinalSourceLaw cutoff anchorDelta pruneDelta fallbackDelta
      finalDelta lower upper epsilon maxBatch preferenceGap maximum hprobability hcutoff hanchorDelta
      hanchorDeltaLeOne hbudget).map Prod.snd =
      canonicalOptMaximizeSourceLogFinalOutputLaw cutoff anchorDelta pruneDelta fallbackDelta finalDelta
        lower upper epsilon maxBatch preferenceGap hprobability hcutoff hanchorDelta hanchorDeltaLeOne
        hbudget := by
  classical
  unfold canonicalOptMaximizeTraceFallbackFinalSourceLaw
    canonicalOptMaximizeSourceLogFinalOutputLaw
  apply optMaximizeAnchorPruneTraceFallbackFinalLaw_map_output_eq
  intro anchor
  exact freshStoppedPruneTraceStateLaw_map_activeLaw preferenceGap lower
    (sourceLemma5PruneContractionFactor (Fintype.card Arm) cutoff pruneDelta)
    cutoff anchor Finset.univ
    (canonicalFreshPruneOutcomeLaw preferenceGap hprobability
      (sourcePruneRoundCount (Fintype.card Arm)) anchor lower upper pruneDelta maxBatch hbudget)
    (canonicalFreshPruneDecision (sourcePruneRoundCount (Fintype.card Arm))
      lower upper pruneDelta maxBatch hbudget)
    (sourcePruneRoundCount (Fintype.card Arm))

/--
The source comparison-cap event evaluated on the complete four-phase trace.
The tail outcomes are retained even though the deterministic cap depends only
on the realized retained set.
-/
noncomputable def canonicalOptMaximizeTraceFallbackFinalSourceResourceProbability
    {Arm : Type*} [Fintype Arm] [Nonempty Arm] [DecidableEq Arm]
    (cutoff : ℕ)
    (anchorDelta pruneDelta fallbackDelta finalDelta lower upper epsilon : ℝ) (maxBatch : ℕ)
    (preferenceGap : Arm → Arm → ℝ) (maximum : Arm)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (hcutoff : 0 < cutoff) (hanchorDelta : 0 < anchorDelta)
    (hanchorDeltaLeOne : anchorDelta ≤ 1)
    (hbudget : ∀ round < sourcePruneRoundCount (Fintype.card Arm),
      fixedSampleBudget lower upper (adaptivePruneRoundDelta pruneDelta round) ≤ maxBatch) : ℝ := by
  classical
  exact pmfProb
    (canonicalOptMaximizeTraceFallbackFinalSourceLaw cutoff anchorDelta pruneDelta fallbackDelta
      finalDelta lower upper epsilon maxBatch preferenceGap maximum hprobability hcutoff hanchorDelta
      hanchorDeltaLeOne hbudget)
    (fun traceFallbackOutput =>
      GoodAnchor preferenceGap lower cutoff traceFallbackOutput.1.1.1 ∧
        traceFallbackOutput.1.1.2.2 = false ∧
          traceFallbackOutput.1.1.2.1.1.card ≤ 2 * cutoff ∧
          (EpsilonMaximum preferenceGap upper traceFallbackOutput.1.1.1 ∨
            maximum ∈ traceFallbackOutput.1.1.2.1.1) ∧
          (optMaximizeTraceAndTailComparisonCap cutoff anchorDelta pruneDelta lower upper
            (finalDelta / (Fintype.card Arm : ℝ)) epsilon fallbackDelta
            traceFallbackOutput.1.1.2.1.2 traceFallbackOutput.1.1.2.1.1 : ℝ) ≤
            (optMaximizePickAnchorComparisonCap (Arm := Arm) cutoff anchorDelta lower : ℝ) +
              sourceLemma5PruneComparisonRateBound (Fintype.card Arm) lower upper pruneDelta +
              (optMaximizeFinalTailComparisonCap traceFallbackOutput.1.1.2.1.1 lower upper
                (finalDelta / (Fintype.card Arm : ℝ)) epsilon fallbackDelta : ℝ))

/--
An event determined before the fallback is sampled has the same probability
on the complete four-phase execution.  This is the finite-PMF dependency
bridge used to attach the tail to the stopped-Prune trace.
-/
theorem optMaximizeAnchorPruneTraceFallbackFinalLaw_prior_probability
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (roundCount : ℕ) (anchorLaw : PMF Arm)
    (pruneTraceLaw : Arm → PMF (stoppedPruneTraceState Arm roundCount × Bool))
    (fallbackLaw : Arm → Finset Arm → PMF Arm)
    (finalLaw : Arm → Finset Arm → Arm → PMF Arm)
    (event : Arm → stoppedPruneTraceState Arm roundCount × Bool → Prop)
    [∀ anchor stateFailure, Decidable (event anchor stateFailure)] :
    pmfProb (optMaximizeAnchorPruneTraceFallbackFinalLaw roundCount anchorLaw pruneTraceLaw
      fallbackLaw finalLaw)
      (fun traceFallbackOutput => event traceFallbackOutput.1.1.1 traceFallbackOutput.1.1.2) =
      pmfProb (optMaximizeAnchorPruneTraceLaw roundCount anchorLaw pruneTraceLaw)
        (fun anchorStateFailure => event anchorStateFailure.1 anchorStateFailure.2) := by
  classical
  unfold optMaximizeAnchorPruneTraceFallbackFinalLaw
  rw [pmfProb_bind]
  simp_rw [pmfProb_map]
  have hfinal : ∀ traceFallback :
      ((Arm × (stoppedPruneTraceState Arm roundCount × Bool)) × Arm),
      pmfProb (finalLaw traceFallback.1.1 traceFallback.1.2.1.1 traceFallback.2)
        (fun _ => event traceFallback.1.1 traceFallback.1.2) =
        if event traceFallback.1.1 traceFallback.1.2 then 1 else 0 := by
    intro traceFallback
    by_cases hevent : event traceFallback.1.1 traceFallback.1.2 <;>
      simp [hevent, pmfProb, pmfExp_const]
  simp_rw [hfinal]
  change pmfProb
      (optMaximizeAnchorPruneTraceFallbackLaw roundCount anchorLaw pruneTraceLaw fallbackLaw)
      (fun traceFallback => event traceFallback.1.1 traceFallback.1.2) =
    pmfProb (optMaximizeAnchorPruneTraceLaw roundCount anchorLaw pruneTraceLaw)
      (fun anchorStateFailure => event anchorStateFailure.1 anchorStateFailure.2)
  unfold optMaximizeAnchorPruneTraceFallbackLaw
  rw [pmfProb_bind]
  simp_rw [pmfProb_map]
  unfold pmfProb
  apply pmfExp_congr
  intro anchorStateFailure
  by_cases hevent : event anchorStateFailure.1 anchorStateFailure.2 <;>
    simp [hevent, pmfExp_const]

/-- Erasing the fallback output preserves every Pick-Anchor--Prune trace event. -/
theorem optMaximizeAnchorPruneTraceFallbackLaw_prior_probability
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (roundCount : ℕ) (anchorLaw : PMF Arm)
    (pruneTraceLaw : Arm → PMF (stoppedPruneTraceState Arm roundCount × Bool))
    (fallbackLaw : Arm → Finset Arm → PMF Arm)
    (event : Arm → stoppedPruneTraceState Arm roundCount × Bool → Prop)
    [∀ anchor stateFailure, Decidable (event anchor stateFailure)] :
    pmfProb (optMaximizeAnchorPruneTraceFallbackLaw roundCount anchorLaw pruneTraceLaw fallbackLaw)
      (fun traceFallback => event traceFallback.1.1 traceFallback.1.2) =
      pmfProb (optMaximizeAnchorPruneTraceLaw roundCount anchorLaw pruneTraceLaw)
        (fun anchorStateFailure => event anchorStateFailure.1 anchorStateFailure.2) := by
  classical
  unfold optMaximizeAnchorPruneTraceFallbackLaw
  rw [pmfProb_bind]
  simp_rw [pmfProb_map]
  unfold pmfProb
  apply pmfExp_congr
  intro anchorStateFailure
  by_cases hevent : event anchorStateFailure.1 anchorStateFailure.2 <;>
    simp [hevent, pmfExp_const]

/--
The fallback consumes its failure budget only on the retained-maximum branch,
and is sampled conditionally on the realized stopped-Prune trace.
-/
theorem optMaximizeAnchorPruneTraceFallbackLaw_branch_success_probability_ge_one_sub_add
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (roundCount : ℕ) (anchorLaw : PMF Arm)
    (pruneTraceLaw : Arm → PMF (stoppedPruneTraceState Arm roundCount × Bool))
    (fallbackLaw : Arm → Finset Arm → PMF Arm)
    (traceGood maximumRetained : Arm → stoppedPruneTraceState Arm roundCount × Bool → Prop)
    (fallbackSuccess : Arm → stoppedPruneTraceState Arm roundCount × Bool → Arm → Prop)
    (firstFailure fallbackFailure : ℝ) (hfallbackFailureNonnegative : 0 ≤ fallbackFailure)
    [∀ anchor stateFailure, Decidable (traceGood anchor stateFailure)]
    [∀ anchor stateFailure, Decidable (maximumRetained anchor stateFailure)]
    [∀ anchor stateFailure fallback, Decidable (fallbackSuccess anchor stateFailure fallback)]
    (hfirst : 1 - firstFailure ≤
      pmfProb (optMaximizeAnchorPruneTraceLaw roundCount anchorLaw pruneTraceLaw)
        (fun anchorStateFailure =>
          traceGood anchorStateFailure.1 anchorStateFailure.2 ∨
            maximumRetained anchorStateFailure.1 anchorStateFailure.2))
    (hfallback : ∀ anchor stateFailure,
      maximumRetained anchor stateFailure →
      pmfProb (fallbackLaw anchor stateFailure.1.1)
        (fun fallback => ¬ fallbackSuccess anchor stateFailure fallback) ≤ fallbackFailure) :
    1 - (firstFailure + fallbackFailure) ≤
      pmfProb (optMaximizeAnchorPruneTraceFallbackLaw roundCount anchorLaw pruneTraceLaw fallbackLaw)
        (fun traceFallback =>
          traceGood traceFallback.1.1 traceFallback.1.2 ∨
            (maximumRetained traceFallback.1.1 traceFallback.1.2 ∧
              fallbackSuccess traceFallback.1.1 traceFallback.1.2 traceFallback.2)) := by
  classical
  let law := optMaximizeAnchorPruneTraceFallbackLaw roundCount anchorLaw pruneTraceLaw fallbackLaw
  let firstBad : (Arm × (stoppedPruneTraceState Arm roundCount × Bool)) × Arm → Prop :=
    fun traceFallback =>
      ¬ (traceGood traceFallback.1.1 traceFallback.1.2 ∨
        maximumRetained traceFallback.1.1 traceFallback.1.2)
  let fallbackBad : (Arm × (stoppedPruneTraceState Arm roundCount × Bool)) × Arm → Prop :=
    fun traceFallback =>
      maximumRetained traceFallback.1.1 traceFallback.1.2 ∧
        ¬ fallbackSuccess traceFallback.1.1 traceFallback.1.2 traceFallback.2
  let success : (Arm × (stoppedPruneTraceState Arm roundCount × Bool)) × Arm → Prop :=
    fun traceFallback =>
      traceGood traceFallback.1.1 traceFallback.1.2 ∨
        (maximumRetained traceFallback.1.1 traceFallback.1.2 ∧
          fallbackSuccess traceFallback.1.1 traceFallback.1.2 traceFallback.2)
  have hfirstBad : pmfProb law firstBad ≤ firstFailure := by
    change pmfProb law (fun traceFallback =>
      ¬ (traceGood traceFallback.1.1 traceFallback.1.2 ∨
        maximumRetained traceFallback.1.1 traceFallback.1.2)) ≤ firstFailure
    rw [pmfProb_compl]
    have hfirstMarg : pmfProb law (fun traceFallback =>
        traceGood traceFallback.1.1 traceFallback.1.2 ∨
          maximumRetained traceFallback.1.1 traceFallback.1.2) =
        pmfProb (optMaximizeAnchorPruneTraceLaw roundCount anchorLaw pruneTraceLaw)
          (fun anchorStateFailure =>
            traceGood anchorStateFailure.1 anchorStateFailure.2 ∨
              maximumRetained anchorStateFailure.1 anchorStateFailure.2) := by
      simpa only [law] using
        (optMaximizeAnchorPruneTraceFallbackLaw_prior_probability roundCount anchorLaw pruneTraceLaw
          fallbackLaw (fun anchor stateFailure =>
            traceGood anchor stateFailure ∨ maximumRetained anchor stateFailure))
    rw [hfirstMarg]
    linarith
  have hfallbackBad : pmfProb law fallbackBad ≤ fallbackFailure := by
    change pmfProb law (fun traceFallback =>
      maximumRetained traceFallback.1.1 traceFallback.1.2 ∧
        ¬ fallbackSuccess traceFallback.1.1 traceFallback.1.2 traceFallback.2) ≤ fallbackFailure
    unfold law optMaximizeAnchorPruneTraceFallbackLaw
    apply pmfProb_adaptiveStep_le_of_historywiseBound
      (optMaximizeAnchorPruneTraceLaw roundCount anchorLaw pruneTraceLaw)
      (fun anchorStateFailure => fallbackLaw anchorStateFailure.1 anchorStateFailure.2.1.1)
      (fun anchorStateFailure fallback =>
        maximumRetained anchorStateFailure.1 anchorStateFailure.2 ∧
          ¬ fallbackSuccess anchorStateFailure.1 anchorStateFailure.2 fallback)
      fallbackFailure
    intro anchorStateFailure
    by_cases hmaximum : maximumRetained anchorStateFailure.1 anchorStateFailure.2
    · simp only [hmaximum, true_and]
      exact hfallback anchorStateFailure.1 anchorStateFailure.2 hmaximum
    · simp only [hmaximum, false_and, pmfProb_false]
      exact hfallbackFailureNonnegative
  have hunion : pmfProb law (fun traceFallback =>
      firstBad traceFallback ∨ fallbackBad traceFallback) ≤ firstFailure + fallbackFailure :=
    (pmfProb_or_le law firstBad fallbackBad).trans
      (add_le_add hfirstBad hfallbackBad)
  have hcomplement : pmfProb law (fun traceFallback => ¬ success traceFallback) ≤
      pmfProb law (fun traceFallback => firstBad traceFallback ∨ fallbackBad traceFallback) := by
    apply pmfProb_le_of_imp
    intro traceFallback hfailure
    by_cases htraceGood : traceGood traceFallback.1.1 traceFallback.1.2 <;>
      by_cases hmaximumRetained : maximumRetained traceFallback.1.1 traceFallback.1.2 <;>
      by_cases hfallbackSuccess : fallbackSuccess traceFallback.1.1 traceFallback.1.2 traceFallback.2 <;>
      simp [success, firstBad, fallbackBad, htraceGood, hmaximumRetained, hfallbackSuccess] at hfailure ⊢
  have hfailure : pmfProb law (fun traceFallback => ¬ success traceFallback) ≤
      firstFailure + fallbackFailure := hcomplement.trans hunion
  change 1 - (firstFailure + fallbackFailure) ≤ pmfProb law success
  calc
    1 - (firstFailure + fallbackFailure) ≤
        1 - pmfProb law (fun traceFallback => ¬ success traceFallback) := by linarith
    _ = pmfProb law success := by
      rw [pmfProb_compl]
      ring

/-- Erasing only the final output recovers the conditional fallback execution. -/
theorem optMaximizeAnchorPruneTraceFallbackFinalLaw_traceFallback_probability
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (roundCount : ℕ) (anchorLaw : PMF Arm)
    (pruneTraceLaw : Arm → PMF (stoppedPruneTraceState Arm roundCount × Bool))
    (fallbackLaw : Arm → Finset Arm → PMF Arm)
    (finalLaw : Arm → Finset Arm → Arm → PMF Arm)
    (event : (Arm × (stoppedPruneTraceState Arm roundCount × Bool)) × Arm → Prop)
    [DecidablePred event] :
    pmfProb (optMaximizeAnchorPruneTraceFallbackFinalLaw roundCount anchorLaw pruneTraceLaw
      fallbackLaw finalLaw) (fun traceFallbackOutput => event traceFallbackOutput.1) =
      pmfProb (optMaximizeAnchorPruneTraceFallbackLaw roundCount anchorLaw pruneTraceLaw fallbackLaw)
        event := by
  classical
  unfold optMaximizeAnchorPruneTraceFallbackFinalLaw
  rw [pmfProb_bind]
  simp_rw [pmfProb_map]
  have hfinal : ∀ traceFallback :
      ((Arm × (stoppedPruneTraceState Arm roundCount × Bool)) × Arm),
      pmfProb (finalLaw traceFallback.1.1 traceFallback.1.2.1.1 traceFallback.2)
        (fun _ => event traceFallback) = if event traceFallback then 1 else 0 := by
    intro traceFallback
    by_cases hevent : event traceFallback <;> simp [hevent, pmfProb, pmfExp_const]
  simp_rw [hfinal]
  rfl

/--
Compose a trace-conditioned fallback success event with the fresh final-loop
guarantee, without treating any phase of Algorithm 3 as independent.
-/
theorem optMaximizeAnchorPruneTraceFallbackFinalLaw_success_probability_ge_one_sub_add
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (roundCount : ℕ) (anchorLaw : PMF Arm)
    (pruneTraceLaw : Arm → PMF (stoppedPruneTraceState Arm roundCount × Bool))
    (fallbackLaw : Arm → Finset Arm → PMF Arm)
    (finalLaw : Arm → Finset Arm → Arm → PMF Arm)
    (priorSuccess : (Arm × (stoppedPruneTraceState Arm roundCount × Bool)) × Arm → Prop)
    (outputSuccess : Arm → stoppedPruneTraceState Arm roundCount × Bool → Arm → Arm → Prop)
    (priorFailure finalFailure : ℝ) (hfinalFailureNonnegative : 0 ≤ finalFailure)
    [DecidablePred priorSuccess]
    [∀ anchor stateFailure fallback output,
      Decidable (outputSuccess anchor stateFailure fallback output)]
    (hprior : 1 - priorFailure ≤
      pmfProb (optMaximizeAnchorPruneTraceFallbackLaw roundCount anchorLaw pruneTraceLaw fallbackLaw)
        priorSuccess)
    (hfinal : ∀ traceFallback,
      priorSuccess traceFallback →
      1 - finalFailure ≤
        pmfProb (finalLaw traceFallback.1.1 traceFallback.1.2.1.1 traceFallback.2)
          (outputSuccess traceFallback.1.1 traceFallback.1.2 traceFallback.2)) :
    1 - (priorFailure + finalFailure) ≤
      pmfProb (optMaximizeAnchorPruneTraceFallbackFinalLaw roundCount anchorLaw pruneTraceLaw
        fallbackLaw finalLaw)
        (fun traceFallbackOutput =>
          outputSuccess traceFallbackOutput.1.1.1 traceFallbackOutput.1.1.2
            traceFallbackOutput.1.2 traceFallbackOutput.2) := by
  classical
  let priorLaw := optMaximizeAnchorPruneTraceFallbackLaw roundCount anchorLaw pruneTraceLaw fallbackLaw
  let law := optMaximizeAnchorPruneTraceFallbackFinalLaw roundCount anchorLaw pruneTraceLaw
    fallbackLaw finalLaw
  let priorBad : ((Arm × (stoppedPruneTraceState Arm roundCount × Bool)) × Arm) × Arm → Prop :=
    fun traceFallbackOutput => ¬ priorSuccess traceFallbackOutput.1
  let finalBad : ((Arm × (stoppedPruneTraceState Arm roundCount × Bool)) × Arm) × Arm → Prop :=
    fun traceFallbackOutput =>
      priorSuccess traceFallbackOutput.1 ∧
        ¬ outputSuccess traceFallbackOutput.1.1.1 traceFallbackOutput.1.1.2
          traceFallbackOutput.1.2 traceFallbackOutput.2
  let success : ((Arm × (stoppedPruneTraceState Arm roundCount × Bool)) × Arm) × Arm → Prop :=
    fun traceFallbackOutput =>
      outputSuccess traceFallbackOutput.1.1.1 traceFallbackOutput.1.1.2
        traceFallbackOutput.1.2 traceFallbackOutput.2
  have hpriorMarg : pmfProb law (fun traceFallbackOutput =>
      priorSuccess traceFallbackOutput.1) = pmfProb priorLaw priorSuccess := by
    simpa only [law, priorLaw] using
      (optMaximizeAnchorPruneTraceFallbackFinalLaw_traceFallback_probability
        roundCount anchorLaw pruneTraceLaw fallbackLaw finalLaw priorSuccess)
  have hpriorBad : pmfProb law priorBad ≤ priorFailure := by
    change pmfProb law (fun traceFallbackOutput => ¬ priorSuccess traceFallbackOutput.1) ≤
      priorFailure
    rw [pmfProb_compl, hpriorMarg]
    linarith
  have hfinalBad : pmfProb law finalBad ≤ finalFailure := by
    change pmfProb
      (priorLaw.bind fun traceFallback =>
        (finalLaw traceFallback.1.1 traceFallback.1.2.1.1 traceFallback.2).map fun output =>
          (traceFallback, output))
      (fun traceFallbackOutput =>
        priorSuccess traceFallbackOutput.1 ∧
          ¬ outputSuccess traceFallbackOutput.1.1.1 traceFallbackOutput.1.1.2
            traceFallbackOutput.1.2 traceFallbackOutput.2) ≤ finalFailure
    apply pmfProb_adaptiveStep_le_of_historywiseBound priorLaw
      (fun traceFallback => finalLaw traceFallback.1.1 traceFallback.1.2.1.1 traceFallback.2)
      (fun traceFallback output =>
        priorSuccess traceFallback ∧
          ¬ outputSuccess traceFallback.1.1 traceFallback.1.2 traceFallback.2 output)
      finalFailure
    intro traceFallback
    by_cases hsuccess : priorSuccess traceFallback
    · simp only [hsuccess, true_and]
      rw [pmfProb_compl]
      linarith [hfinal traceFallback hsuccess]
    · simp only [hsuccess, false_and, pmfProb_false]
      exact hfinalFailureNonnegative
  have hunion : pmfProb law (fun traceFallbackOutput =>
      priorBad traceFallbackOutput ∨ finalBad traceFallbackOutput) ≤ priorFailure + finalFailure :=
    (pmfProb_or_le law priorBad finalBad).trans (add_le_add hpriorBad hfinalBad)
  have hcomplement : pmfProb law (fun traceFallbackOutput => ¬ success traceFallbackOutput) ≤
      pmfProb law (fun traceFallbackOutput =>
        priorBad traceFallbackOutput ∨ finalBad traceFallbackOutput) := by
    apply pmfProb_le_of_imp
    intro traceFallbackOutput hfailure
    by_cases hpriorSuccess : priorSuccess traceFallbackOutput.1 <;>
      by_cases houtputSuccess : outputSuccess traceFallbackOutput.1.1.1 traceFallbackOutput.1.1.2
        traceFallbackOutput.1.2 traceFallbackOutput.2 <;>
      simp [success, priorBad, finalBad, hpriorSuccess, houtputSuccess] at hfailure ⊢
  have hfailure : pmfProb law (fun traceFallbackOutput => ¬ success traceFallbackOutput) ≤
      priorFailure + finalFailure := hcomplement.trans hunion
  change 1 - (priorFailure + finalFailure) ≤ pmfProb law success
  calc
    1 - (priorFailure + finalFailure) ≤
        1 - pmfProb law (fun traceFallbackOutput => ¬ success traceFallbackOutput) := by linarith
    _ = pmfProb law success := by
      rw [pmfProb_compl]
      ring

/--
The final conditional comparison preserves a proved prior execution event
when its output-success conclusion is recorded jointly rather than projected
away.  This is the finite-PMF composition form needed for joint correctness
and resource statements.
-/
theorem optMaximizeAnchorPruneTraceFallbackFinalLaw_prior_and_success_probability_ge_one_sub_add
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (roundCount : ℕ) (anchorLaw : PMF Arm)
    (pruneTraceLaw : Arm → PMF (stoppedPruneTraceState Arm roundCount × Bool))
    (fallbackLaw : Arm → Finset Arm → PMF Arm)
    (finalLaw : Arm → Finset Arm → Arm → PMF Arm)
    (priorSuccess : (Arm × (stoppedPruneTraceState Arm roundCount × Bool)) × Arm → Prop)
    (outputSuccess : Arm → stoppedPruneTraceState Arm roundCount × Bool → Arm → Arm → Prop)
    (priorFailure finalFailure : ℝ) (hfinalFailureNonnegative : 0 ≤ finalFailure)
    [DecidablePred priorSuccess]
    [∀ anchor stateFailure fallback output,
      Decidable (outputSuccess anchor stateFailure fallback output)]
    (hprior : 1 - priorFailure ≤
      pmfProb (optMaximizeAnchorPruneTraceFallbackLaw roundCount anchorLaw pruneTraceLaw fallbackLaw)
        priorSuccess)
    (hfinal : ∀ traceFallback,
      priorSuccess traceFallback →
      1 - finalFailure ≤
        pmfProb (finalLaw traceFallback.1.1 traceFallback.1.2.1.1 traceFallback.2)
          (outputSuccess traceFallback.1.1 traceFallback.1.2 traceFallback.2)) :
    1 - (priorFailure + finalFailure) ≤
      pmfProb (optMaximizeAnchorPruneTraceFallbackFinalLaw roundCount anchorLaw pruneTraceLaw
        fallbackLaw finalLaw)
        (fun traceFallbackOutput =>
          priorSuccess traceFallbackOutput.1 ∧
            outputSuccess traceFallbackOutput.1.1.1 traceFallbackOutput.1.1.2
              traceFallbackOutput.1.2 traceFallbackOutput.2) := by
  classical
  let priorLaw := optMaximizeAnchorPruneTraceFallbackLaw roundCount anchorLaw pruneTraceLaw fallbackLaw
  let law := optMaximizeAnchorPruneTraceFallbackFinalLaw roundCount anchorLaw pruneTraceLaw
    fallbackLaw finalLaw
  let priorBad : ((Arm × (stoppedPruneTraceState Arm roundCount × Bool)) × Arm) × Arm → Prop :=
    fun traceFallbackOutput => ¬ priorSuccess traceFallbackOutput.1
  let finalBad : ((Arm × (stoppedPruneTraceState Arm roundCount × Bool)) × Arm) × Arm → Prop :=
    fun traceFallbackOutput =>
      priorSuccess traceFallbackOutput.1 ∧
        ¬ outputSuccess traceFallbackOutput.1.1.1 traceFallbackOutput.1.1.2
          traceFallbackOutput.1.2 traceFallbackOutput.2
  let success : ((Arm × (stoppedPruneTraceState Arm roundCount × Bool)) × Arm) × Arm → Prop :=
    fun traceFallbackOutput =>
      priorSuccess traceFallbackOutput.1 ∧
        outputSuccess traceFallbackOutput.1.1.1 traceFallbackOutput.1.1.2
          traceFallbackOutput.1.2 traceFallbackOutput.2
  have hpriorMarg : pmfProb law (fun traceFallbackOutput =>
      priorSuccess traceFallbackOutput.1) = pmfProb priorLaw priorSuccess := by
    simpa only [law, priorLaw] using
      (optMaximizeAnchorPruneTraceFallbackFinalLaw_traceFallback_probability
        roundCount anchorLaw pruneTraceLaw fallbackLaw finalLaw priorSuccess)
  have hpriorBad : pmfProb law priorBad ≤ priorFailure := by
    change pmfProb law (fun traceFallbackOutput => ¬ priorSuccess traceFallbackOutput.1) ≤
      priorFailure
    rw [pmfProb_compl, hpriorMarg]
    linarith
  have hfinalBad : pmfProb law finalBad ≤ finalFailure := by
    change pmfProb
      (priorLaw.bind fun traceFallback =>
        (finalLaw traceFallback.1.1 traceFallback.1.2.1.1 traceFallback.2).map fun output =>
          (traceFallback, output))
      (fun traceFallbackOutput =>
        priorSuccess traceFallbackOutput.1 ∧
          ¬ outputSuccess traceFallbackOutput.1.1.1 traceFallbackOutput.1.1.2
            traceFallbackOutput.1.2 traceFallbackOutput.2) ≤ finalFailure
    apply pmfProb_adaptiveStep_le_of_historywiseBound priorLaw
      (fun traceFallback => finalLaw traceFallback.1.1 traceFallback.1.2.1.1 traceFallback.2)
      (fun traceFallback output =>
        priorSuccess traceFallback ∧
          ¬ outputSuccess traceFallback.1.1 traceFallback.1.2 traceFallback.2 output)
      finalFailure
    intro traceFallback
    by_cases hsuccess : priorSuccess traceFallback
    · simp only [hsuccess, true_and]
      rw [pmfProb_compl]
      linarith [hfinal traceFallback hsuccess]
    · simp only [hsuccess, false_and, pmfProb_false]
      exact hfinalFailureNonnegative
  have hunion : pmfProb law (fun traceFallbackOutput =>
      priorBad traceFallbackOutput ∨ finalBad traceFallbackOutput) ≤ priorFailure + finalFailure :=
    (pmfProb_or_le law priorBad finalBad).trans (add_le_add hpriorBad hfinalBad)
  have hcomplement : pmfProb law (fun traceFallbackOutput => ¬ success traceFallbackOutput) ≤
      pmfProb law (fun traceFallbackOutput =>
        priorBad traceFallbackOutput ∨ finalBad traceFallbackOutput) := by
    apply pmfProb_le_of_imp
    intro traceFallbackOutput hfailure
    by_cases hpriorSuccess : priorSuccess traceFallbackOutput.1 <;>
      by_cases houtputSuccess : outputSuccess traceFallbackOutput.1.1.1 traceFallbackOutput.1.1.2
        traceFallbackOutput.1.2 traceFallbackOutput.2 <;>
      simp [success, priorBad, finalBad, hpriorSuccess, houtputSuccess] at hfailure ⊢
  have hfailure : pmfProb law (fun traceFallbackOutput => ¬ success traceFallbackOutput) ≤
      priorFailure + finalFailure := hcomplement.trans hunion
  change 1 - (priorFailure + finalFailure) ≤ pmfProb law success
  calc
    1 - (priorFailure + finalFailure) ≤
        1 - pmfProb law (fun traceFallbackOutput => ¬ success traceFallbackOutput) := by linarith
    _ = pmfProb law success := by
      rw [pmfProb_compl]
      ring

/-- The target `ε`-maximum probability of the complete source-horizon trace. -/
noncomputable def canonicalOptMaximizeTraceFallbackFinalSourceEpsilonMaximumProbability
    {Arm : Type*} [Fintype Arm] [Nonempty Arm] [DecidableEq Arm]
    (cutoff : ℕ)
    (anchorDelta pruneDelta fallbackDelta finalDelta lower upper epsilon : ℝ) (maxBatch : ℕ)
    (preferenceGap : Arm → Arm → ℝ) (maximum : Arm)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (hcutoff : 0 < cutoff) (hanchorDelta : 0 < anchorDelta)
    (hanchorDeltaLeOne : anchorDelta ≤ 1)
    (hbudget : ∀ round < sourcePruneRoundCount (Fintype.card Arm),
      fixedSampleBudget lower upper (adaptivePruneRoundDelta pruneDelta round) ≤ maxBatch) : ℝ := by
  classical
  exact pmfProb
    (canonicalOptMaximizeTraceFallbackFinalSourceLaw cutoff anchorDelta pruneDelta fallbackDelta
      finalDelta lower upper epsilon maxBatch preferenceGap maximum hprobability hcutoff hanchorDelta
      hanchorDeltaLeOne hbudget)
    (fun traceFallbackOutput => EpsilonMaximum preferenceGap epsilon traceFallbackOutput.2)

/--
Lemma 18 and the non-base correctness portion of Theorem 6 on the source
integer Prune horizon.  The four phases are one conditional finite PMF, so
the displayed failure sum uses no phase-independence hypothesis.
-/
theorem canonicalOptMaximizeTraceFallbackFinalSource_epsilonMaximum_probability
    {Arm : Type*} [Fintype Arm] [Nonempty Arm] [DecidableEq Arm]
    (cutoff : ℕ)
    (anchorDelta pruneDelta fallbackDelta finalDelta lower upper epsilon : ℝ) (maxBatch : ℕ)
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
    (hbudget : ∀ round < sourcePruneRoundCount (Fintype.card Arm),
      fixedSampleBudget lower upper (adaptivePruneRoundDelta pruneDelta round) ≤ maxBatch)
    (hupperNonnegative : 0 ≤ upper)
    (hmaximumAbsolute : AbsoluteMaximum preferenceGap maximum)
    (hseparation : lower < upper) (hpruneDelta : 0 < pruneDelta)
    (hpruneDeltaHalf : pruneDelta ≤ 1 / 2)
    (hpruneCutoff : Real.sqrt (6 * (Fintype.card Arm : ℝ) *
      Real.log (Fintype.card Arm : ℝ)) < (cutoff : ℝ))
    (hpruneDeltaLower : (cutoff : ℝ) / (Fintype.card Arm : ℝ) ≤ pruneDelta)
    (hepsilon : 0 < epsilon) (hfallbackDelta : 0 < fallbackDelta)
    (hfallbackDeltaLeOne : fallbackDelta ≤ 1)
    (hfinalSeparation : upper < epsilon) (hfinalDelta : 0 < finalDelta)
    (hfinalDeltaLeOne : finalDelta ≤ 1) :
    1 - (anchorDelta + pruneDelta + fallbackDelta + finalDelta) ≤
      canonicalOptMaximizeTraceFallbackFinalSourceEpsilonMaximumProbability cutoff anchorDelta
        pruneDelta fallbackDelta finalDelta lower upper epsilon maxBatch preferenceGap maximum hprobability
        hcutoff hanchorDelta hanchorDeltaLeOne hbudget := by
  classical
  let roundCount := sourcePruneRoundCount (Fintype.card Arm)
  let anchorLaw : PMF Arm :=
    canonicalFreshPickAnchorSourceOutputLaw cutoff anchorDelta lower preferenceGap hprobability
      hcutoff hanchorDelta hanchorDeltaLeOne
  let pruneTraceLaw : Arm → PMF (stoppedPruneTraceState Arm roundCount × Bool) := fun anchor =>
    freshStoppedPruneTraceStateLaw preferenceGap lower
      (sourceLemma5PruneContractionFactor (Fintype.card Arm) cutoff pruneDelta)
      cutoff anchor Finset.univ
      (canonicalFreshPruneOutcomeLaw preferenceGap hprobability roundCount anchor lower upper
        pruneDelta maxBatch hbudget)
      (canonicalFreshPruneDecision roundCount lower upper pruneDelta maxBatch hbudget)
      roundCount
  let fallbackLaw : Arm → Finset Arm → PMF Arm := fun anchor candidates =>
    canonicalFreshFinsetSeqEliminateOutputLaw anchor candidates preferenceGap hprobability epsilon
      (fallbackDelta / (candidates.card : ℝ))
  let finalLaw : Arm → Finset Arm → Arm → PMF Arm := fun anchor candidates fallback =>
    canonicalFreshFinalCheckOutputLaw anchor fallback candidates preferenceGap hprobability upper epsilon
      (finalDelta / (Fintype.card Arm : ℝ))
  let priorSuccess : (Arm × (stoppedPruneTraceState Arm roundCount × Bool)) × Arm → Prop :=
    fun traceFallback =>
      EpsilonMaximum preferenceGap upper traceFallback.1.1 ∨
        (maximum ∈ traceFallback.1.2.1.1 ∧
          EpsilonMaximum preferenceGap epsilon traceFallback.2)
  let outputSuccess : Arm → stoppedPruneTraceState Arm roundCount × Bool → Arm → Arm → Prop :=
    fun _ _ _ output => EpsilonMaximum preferenceGap epsilon output
  have hfirstStrong := canonicalOptMaximizeAnchorPruneTraceSource_success_probability
    cutoff anchorDelta pruneDelta lower upper maxBatch preferenceGap maximum hprobability ranking
    hranking hcutoff hcutoffLeCard hanchorDelta hanchorDeltaLeOne hlower hantisymmetric hself
    hcomplete hsst hbudget hupperNonnegative hmaximumAbsolute hseparation hpruneDelta
    hpruneDeltaHalf hpruneCutoff hpruneDeltaLower
  have hfirst : 1 - (anchorDelta + pruneDelta) ≤
      pmfProb (optMaximizeAnchorPruneTraceLaw roundCount anchorLaw pruneTraceLaw)
        (fun anchorStateFailure =>
          EpsilonMaximum preferenceGap upper anchorStateFailure.1 ∨
            maximum ∈ anchorStateFailure.2.1.1) := by
    change 1 - (anchorDelta + pruneDelta) ≤
      pmfProb (optMaximizeAnchorPruneTraceLaw roundCount anchorLaw pruneTraceLaw)
        (fun anchorStateFailure =>
          GoodAnchor preferenceGap lower cutoff anchorStateFailure.1 ∧
            anchorStateFailure.2.2 = false ∧
              anchorStateFailure.2.1.1.card ≤ 2 * cutoff ∧
              (stoppedPruneTraceComparisonCount roundCount cutoff lower upper pruneDelta
                anchorStateFailure.2.1.2 : ℝ) ≤
                sourceLemma5PruneComparisonRateBound (Fintype.card Arm) lower upper pruneDelta ∧
              (EpsilonMaximum preferenceGap upper anchorStateFailure.1 ∨
                maximum ∈ anchorStateFailure.2.1.1)) at hfirstStrong
    exact hfirstStrong.trans
      (pmfProb_le_of_imp _ _ _ (by
        intro anchorStateFailure hsuccess
        exact hsuccess.2.2.2.2))
  have hfallback : ∀ (anchor : Arm)
      (stateFailure : stoppedPruneTraceState Arm roundCount × Bool),
      maximum ∈ stateFailure.1.1 →
      pmfProb (fallbackLaw anchor stateFailure.1.1)
        (fun fallback => ¬ EpsilonMaximum preferenceGap epsilon fallback) ≤ fallbackDelta := by
    intro anchor stateFailure hmaximumMem
    have hsource := canonicalFreshFinsetSeqEliminate_epsilonMaximum_probability_of_sourceSchedule
      anchor stateFailure.1.1 preferenceGap hprobability epsilon fallbackDelta hantisymmetric hself hsst
      hepsilon hfallbackDelta hfallbackDeltaLeOne maximum hmaximumAbsolute hmaximumMem
    unfold canonicalFreshFinsetSeqEliminateEpsilonMaximumProbability at hsource
    have hsource' : 1 - fallbackDelta ≤
        pmfProb (fallbackLaw anchor stateFailure.1.1) (EpsilonMaximum preferenceGap epsilon) := by
      simpa only [fallbackLaw, pmfProbClassical] using hsource
    change pmfProb (fallbackLaw anchor stateFailure.1.1)
      (fun fallback => ¬ EpsilonMaximum preferenceGap epsilon fallback) ≤ fallbackDelta
    rw [pmfProb_compl]
    linarith
  have hprior := optMaximizeAnchorPruneTraceFallbackLaw_branch_success_probability_ge_one_sub_add
    roundCount anchorLaw pruneTraceLaw fallbackLaw
    (fun anchor _ => EpsilonMaximum preferenceGap upper anchor)
    (fun _ stateFailure => maximum ∈ stateFailure.1.1)
    (fun _ _ fallback => EpsilonMaximum preferenceGap epsilon fallback)
    (anchorDelta + pruneDelta) fallbackDelta (le_of_lt hfallbackDelta) hfirst hfallback
  have hcardPositiveNat : 0 < Fintype.card Arm := Fintype.card_pos_iff.mpr inferInstance
  have hcardPositive : 0 < (Fintype.card Arm : ℝ) := by exact_mod_cast hcardPositiveNat
  have heta : 0 < finalDelta / (Fintype.card Arm : ℝ) := div_pos hfinalDelta hcardPositive
  have hetaLeOne : finalDelta / (Fintype.card Arm : ℝ) ≤ 1 := by
    calc
      finalDelta / (Fintype.card Arm : ℝ) ≤ finalDelta :=
        div_le_self (le_of_lt hfinalDelta) (by
          exact_mod_cast (Nat.succ_le_iff.mpr hcardPositiveNat))
      _ ≤ 1 := hfinalDeltaLeOne
  have hfinal : ∀ traceFallback,
      priorSuccess traceFallback →
      1 - finalDelta ≤
        pmfProb (finalLaw traceFallback.1.1 traceFallback.1.2.1.1 traceFallback.2)
          (outputSuccess traceFallback.1.1 traceFallback.1.2 traceFallback.2) := by
    intro traceFallback hsuccess
    have hcardLe : traceFallback.1.2.1.1.card ≤ Fintype.card Arm :=
      Finset.card_le_univ _
    have hcost : (traceFallback.1.2.1.1.card : ℝ) *
        (finalDelta / (Fintype.card Arm : ℝ)) ≤ finalDelta := by
      calc
        (traceFallback.1.2.1.1.card : ℝ) * (finalDelta / (Fintype.card Arm : ℝ)) ≤
            (Fintype.card Arm : ℝ) * (finalDelta / (Fintype.card Arm : ℝ)) := by
              apply mul_le_mul_of_nonneg_right
                (by exact_mod_cast hcardLe) (le_of_lt heta)
        _ = finalDelta := by field_simp [ne_of_gt hcardPositive]
    rcases hsuccess with hanchor | ⟨hmaximumMem, hfallbackSuccess⟩
    · have hphase := canonicalFreshFinalCheck_epsilonMaximum_probability_of_anchor
        traceFallback.1.1 traceFallback.2 traceFallback.1.2.1.1 preferenceGap hprobability epsilon
        upper epsilon (finalDelta / (Fintype.card Arm : ℝ)) hantisymmetric hanchor
        (le_of_lt hfinalSeparation) hfinalSeparation heta hetaLeOne
      change 1 - finalDelta ≤ pmfProb
        (canonicalFreshFinalCheckOutputLaw traceFallback.1.1 traceFallback.2 traceFallback.1.2.1.1
          preferenceGap hprobability upper epsilon (finalDelta / (Fintype.card Arm : ℝ)))
        (EpsilonMaximum preferenceGap epsilon)
      rw [pmfProbClassical_eq_pmfProb] at hphase
      linarith
    · have hphase := canonicalFreshFinalCheck_epsilonMaximum_probability_of_retained_maximum_or_anchor
        traceFallback.1.1 traceFallback.2 maximum traceFallback.1.2.1.1 preferenceGap hprobability
        epsilon upper epsilon (finalDelta / (Fintype.card Arm : ℝ)) hantisymmetric hsst
        (le_of_lt hepsilon) hmaximumAbsolute hmaximumMem hfallbackSuccess le_rfl hfinalSeparation heta
        hetaLeOne
      change 1 - finalDelta ≤ pmfProb
        (canonicalFreshFinalCheckOutputLaw traceFallback.1.1 traceFallback.2 traceFallback.1.2.1.1
          preferenceGap hprobability upper epsilon (finalDelta / (Fintype.card Arm : ℝ)))
        (EpsilonMaximum preferenceGap epsilon)
      rw [pmfProbClassical_eq_pmfProb] at hphase
      linarith
  have hcompose := optMaximizeAnchorPruneTraceFallbackFinalLaw_success_probability_ge_one_sub_add
    roundCount anchorLaw pruneTraceLaw fallbackLaw finalLaw priorSuccess outputSuccess
    (anchorDelta + pruneDelta + fallbackDelta) finalDelta (le_of_lt hfinalDelta)
    (by simpa only [priorSuccess, anchorLaw, pruneTraceLaw, fallbackLaw] using hprior) hfinal
  unfold canonicalOptMaximizeTraceFallbackFinalSourceEpsilonMaximumProbability
    canonicalOptMaximizeTraceFallbackFinalSourceLaw
  change 1 - (anchorDelta + pruneDelta + fallbackDelta + finalDelta) ≤
    pmfProb (optMaximizeAnchorPruneTraceFallbackFinalLaw roundCount anchorLaw pruneTraceLaw fallbackLaw
      finalLaw) (fun traceFallbackOutput => EpsilonMaximum preferenceGap epsilon traceFallbackOutput.2)
  linarith

/--
The source's four equal `δ/4` allocations give the non-base Algorithm-3
branch its literal `1 - δ` correctness guarantee on the trace-carrying PMF.
-/
theorem canonicalOptMaximizeTraceFallbackFinalSource_epsilonMaximum_probability_of_algorithm3_nonbase
    {Arm : Type*} [Fintype Arm] [Nonempty Arm] [DecidableEq Arm]
    (cutoff : ℕ) (lower upper epsilon delta : ℝ) (maxBatch : ℕ)
    (preferenceGap : Arm → Arm → ℝ) (maximum : Arm)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (ranking : Fin (Fintype.card Arm) → Arm)
    (hranking : PreferenceRanking preferenceGap ranking)
    (hcutoff : 0 < cutoff) (hcutoffLeCard : cutoff ≤ Fintype.card Arm)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) (hlower : 0 < lower)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hself : ∀ arm, preferenceGap arm arm = 0)
    (hcomplete : PreferenceComplete preferenceGap)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hbudget : ∀ round < sourcePruneRoundCount (Fintype.card Arm),
      fixedSampleBudget lower upper (adaptivePruneRoundDelta (delta / 4) round) ≤ maxBatch)
    (hupperNonnegative : 0 ≤ upper)
    (hmaximumAbsolute : AbsoluteMaximum preferenceGap maximum)
    (hseparation : lower < upper)
    (hpruneCutoff : Real.sqrt (6 * (Fintype.card Arm : ℝ) *
      Real.log (Fintype.card Arm : ℝ)) < (cutoff : ℝ))
    (hpruneDeltaLower : (cutoff : ℝ) / (Fintype.card Arm : ℝ) ≤ delta / 4)
    (hepsilon : 0 < epsilon) (hfinalSeparation : upper < epsilon) :
    1 - delta ≤
      canonicalOptMaximizeTraceFallbackFinalSourceEpsilonMaximumProbability cutoff (delta / 4)
        (delta / 4) (delta / 4) (delta / 4) lower upper epsilon maxBatch preferenceGap maximum
        hprobability hcutoff (by linarith) (by linarith) hbudget := by
  have hsource := canonicalOptMaximizeTraceFallbackFinalSource_epsilonMaximum_probability
    cutoff (delta / 4) (delta / 4) (delta / 4) (delta / 4) lower upper epsilon maxBatch
    preferenceGap maximum hprobability ranking hranking hcutoff hcutoffLeCard
    (by linarith) (by linarith) hlower hantisymmetric hself hcomplete hsst hbudget
    hupperNonnegative hmaximumAbsolute hseparation (by linarith) (by linarith) hpruneCutoff
    hpruneDeltaLower hepsilon (by linarith) (by linarith) hfinalSeparation (by linarith)
    (by linarith)
  linarith

/--
An instrumented source Algorithm-3 output law.  In the non-base branch the
absolute maximum indexes only the trace's retention flag; the returned arm is
the final coordinate of the four-phase execution.
-/
noncomputable def canonicalOptMaximizeTraceAlgorithmSourceOutputLaw
    {Arm : Type*} [Fintype Arm] [Nonempty Arm] [DecidableEq Arm]
    (cutoff : ℕ) (lower upper epsilon delta : ℝ) (maxBatch : ℕ)
    (preferenceGap : Arm → Arm → ℝ) (maximum : Arm)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) (hcutoff : 0 < cutoff)
    (hbudget : ∀ round < sourcePruneRoundCount (Fintype.card Arm),
      fixedSampleBudget lower upper (adaptivePruneRoundDelta (delta / 4) round) ≤ maxBatch) :
    PMF Arm := by
  classical
  if hbase : delta ≤ 1 / (Fintype.card Arm : ℝ) then
    exact canonicalOptMaximizeBaseSourceOutputLaw preferenceGap hprobability epsilon delta
  else
    exact (canonicalOptMaximizeTraceFallbackFinalSourceLaw cutoff (delta / 4) (delta / 4)
      (delta / 4) (delta / 4) lower upper epsilon maxBatch preferenceGap maximum hprobability hcutoff
      (by linarith) (by linarith) hbudget).map fun traceFallbackOutput =>
        traceFallbackOutput.2

/-- The `ε`-maximum probability of the instrumented source Algorithm-3 output. -/
noncomputable def canonicalOptMaximizeTraceAlgorithmSourceEpsilonMaximumProbability
    {Arm : Type*} [Fintype Arm] [Nonempty Arm] [DecidableEq Arm]
    (cutoff : ℕ) (lower upper epsilon delta : ℝ) (maxBatch : ℕ)
    (preferenceGap : Arm → Arm → ℝ) (maximum : Arm)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) (hcutoff : 0 < cutoff)
    (hbudget : ∀ round < sourcePruneRoundCount (Fintype.card Arm),
      fixedSampleBudget lower upper (adaptivePruneRoundDelta (delta / 4) round) ≤ maxBatch) : ℝ := by
  classical
  exact pmfProb
    (canonicalOptMaximizeTraceAlgorithmSourceOutputLaw cutoff lower upper epsilon delta maxBatch
      preferenceGap maximum hprobability hdelta hdeltaLeOne hcutoff hbudget)
    (EpsilonMaximum preferenceGap epsilon)

/--
The base and source-horizon non-base branches of the instrumented Algorithm-3
output each satisfy the paper's `1 - δ` guarantee.
-/
theorem canonicalOptMaximizeTraceAlgorithmSource_epsilonMaximum_probability
    {Arm : Type*} [Fintype Arm] [Nonempty Arm] [DecidableEq Arm]
    (cutoff : ℕ) (lower upper epsilon delta : ℝ) (maxBatch : ℕ)
    (preferenceGap : Arm → Arm → ℝ) (maximum : Arm)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (ranking : Fin (Fintype.card Arm) → Arm)
    (hranking : PreferenceRanking preferenceGap ranking)
    (hcutoff : 0 < cutoff) (hcutoffLeCard : cutoff ≤ Fintype.card Arm)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) (hlower : 0 < lower)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hself : ∀ arm, preferenceGap arm arm = 0)
    (hcomplete : PreferenceComplete preferenceGap)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hbudget : ∀ round < sourcePruneRoundCount (Fintype.card Arm),
      fixedSampleBudget lower upper (adaptivePruneRoundDelta (delta / 4) round) ≤ maxBatch)
    (hupperNonnegative : 0 ≤ upper)
    (hmaximumAbsolute : AbsoluteMaximum preferenceGap maximum)
    (hseparation : lower < upper)
    (hpruneCutoff : Real.sqrt (6 * (Fintype.card Arm : ℝ) *
      Real.log (Fintype.card Arm : ℝ)) < (cutoff : ℝ))
    (hpruneDeltaLower : (cutoff : ℝ) / (Fintype.card Arm : ℝ) ≤ delta / 4)
    (hepsilon : 0 < epsilon) (hfinalSeparation : upper < epsilon) :
    1 - delta ≤
      canonicalOptMaximizeTraceAlgorithmSourceEpsilonMaximumProbability cutoff lower upper epsilon
        delta maxBatch preferenceGap maximum hprobability hdelta hdeltaLeOne hcutoff hbudget := by
  classical
  unfold canonicalOptMaximizeTraceAlgorithmSourceEpsilonMaximumProbability
    canonicalOptMaximizeTraceAlgorithmSourceOutputLaw
  split
  · exact canonicalOptMaximizeBaseSource_epsilonMaximum_probability preferenceGap hprobability
      epsilon delta hantisymmetric hself hsst hepsilon hdelta hdeltaLeOne maximum hmaximumAbsolute
  · rw [pmfProb_map]
    exact canonicalOptMaximizeTraceFallbackFinalSource_epsilonMaximum_probability_of_algorithm3_nonbase
      cutoff lower upper epsilon delta maxBatch preferenceGap maximum hprobability ranking hranking
      hcutoff hcutoffLeCard hdelta hdeltaLeOne hlower hantisymmetric hself hcomplete hsst hbudget
      hupperNonnegative hmaximumAbsolute hseparation hpruneCutoff hpruneDeltaLower hepsilon
      hfinalSeparation

/--
The source Algorithm-3 output law with the integer Prune horizon.  Unlike the
instrumented analysis law, this returned-arm PMF has no maximum witness.
-/
noncomputable def canonicalOptMaximizeSourceLogAlgorithmOutputLaw
    {Arm : Type*} [Fintype Arm] [Nonempty Arm] [DecidableEq Arm]
    (cutoff : ℕ) (lower upper epsilon delta : ℝ) (maxBatch : ℕ)
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) (hcutoff : 0 < cutoff)
    (hbudget : ∀ round < sourcePruneRoundCount (Fintype.card Arm),
      fixedSampleBudget lower upper (adaptivePruneRoundDelta (delta / 4) round) ≤ maxBatch) :
    PMF Arm := by
  classical
  if hbase : delta ≤ 1 / (Fintype.card Arm : ℝ) then
    exact canonicalOptMaximizeBaseSourceOutputLaw preferenceGap hprobability epsilon delta
  else
    exact canonicalOptMaximizeSourceLogFinalOutputLaw cutoff (delta / 4) (delta / 4)
      (delta / 4) (delta / 4) lower upper epsilon maxBatch preferenceGap hprobability hcutoff
      (by linarith) (by linarith) hbudget

/-- The `ε`-maximum probability of source Algorithm 3 at its integer Prune horizon. -/
noncomputable def canonicalOptMaximizeSourceLogAlgorithmEpsilonMaximumProbability
    {Arm : Type*} [Fintype Arm] [Nonempty Arm] [DecidableEq Arm]
    (cutoff : ℕ) (lower upper epsilon delta : ℝ) (maxBatch : ℕ)
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) (hcutoff : 0 < cutoff)
    (hbudget : ∀ round < sourcePruneRoundCount (Fintype.card Arm),
      fixedSampleBudget lower upper (adaptivePruneRoundDelta (delta / 4) round) ≤ maxBatch) : ℝ := by
  classical
  exact pmfProb
    (canonicalOptMaximizeSourceLogAlgorithmOutputLaw cutoff lower upper epsilon delta maxBatch
      preferenceGap hprobability hdelta hdeltaLeOne hcutoff hbudget)
    (EpsilonMaximum preferenceGap epsilon)

/--
The source Algorithm-3 returned-arm law, including the `δ ≤ 1/n` base branch,
satisfies the literal `1 - δ` correctness guarantee at the source integer
Prune horizon.
-/
theorem canonicalOptMaximizeSourceLogAlgorithm_epsilonMaximum_probability
    {Arm : Type*} [Fintype Arm] [Nonempty Arm] [DecidableEq Arm]
    (cutoff : ℕ) (lower upper epsilon delta : ℝ) (maxBatch : ℕ)
    (preferenceGap : Arm → Arm → ℝ) (maximum : Arm)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (ranking : Fin (Fintype.card Arm) → Arm)
    (hranking : PreferenceRanking preferenceGap ranking)
    (hcutoff : 0 < cutoff) (hcutoffLeCard : cutoff ≤ Fintype.card Arm)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) (hlower : 0 < lower)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hself : ∀ arm, preferenceGap arm arm = 0)
    (hcomplete : PreferenceComplete preferenceGap)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hbudget : ∀ round < sourcePruneRoundCount (Fintype.card Arm),
      fixedSampleBudget lower upper (adaptivePruneRoundDelta (delta / 4) round) ≤ maxBatch)
    (hupperNonnegative : 0 ≤ upper)
    (hmaximumAbsolute : AbsoluteMaximum preferenceGap maximum)
    (hseparation : lower < upper)
    (hpruneCutoff : Real.sqrt (6 * (Fintype.card Arm : ℝ) *
      Real.log (Fintype.card Arm : ℝ)) < (cutoff : ℝ))
    (hpruneDeltaLower : (cutoff : ℝ) / (Fintype.card Arm : ℝ) ≤ delta / 4)
    (hepsilon : 0 < epsilon) (hfinalSeparation : upper < epsilon) :
    1 - delta ≤ canonicalOptMaximizeSourceLogAlgorithmEpsilonMaximumProbability cutoff lower
      upper epsilon delta maxBatch preferenceGap hprobability hdelta hdeltaLeOne hcutoff hbudget := by
  classical
  unfold canonicalOptMaximizeSourceLogAlgorithmEpsilonMaximumProbability
    canonicalOptMaximizeSourceLogAlgorithmOutputLaw
  split
  · exact canonicalOptMaximizeBaseSource_epsilonMaximum_probability preferenceGap hprobability
      epsilon delta hantisymmetric hself hsst hepsilon hdelta hdeltaLeOne maximum hmaximumAbsolute
  · rw [← canonicalOptMaximizeTraceFallbackFinalSourceLaw_map_output_eq cutoff (delta / 4)
      (delta / 4) (delta / 4) (delta / 4) lower upper epsilon maxBatch preferenceGap maximum
      hprobability hcutoff (by linarith) (by linarith) hbudget]
    rw [pmfProb_map]
    exact canonicalOptMaximizeTraceFallbackFinalSource_epsilonMaximum_probability_of_algorithm3_nonbase
      cutoff lower upper epsilon delta maxBatch preferenceGap maximum hprobability ranking hranking
      hcutoff hcutoffLeCard hdelta hdeltaLeOne hlower hantisymmetric hself hcomplete hsst hbudget
      hupperNonnegative hmaximumAbsolute hseparation hpruneCutoff hpruneDeltaLower hepsilon
      hfinalSeparation

/--
The source comparison-cap event evaluated on the four-phase trace whose final
coordinate records the queried early-stopping prefix.  Its resource count is
the literal fixed-batch allocation made before the source loop returns.
-/
noncomputable def canonicalOptMaximizeTraceFallbackFinalTraceSourceResourceProbability
    {Arm : Type*} [Fintype Arm] [Nonempty Arm] [DecidableEq Arm]
    (cutoff : ℕ)
    (anchorDelta pruneDelta fallbackDelta finalDelta lower upper epsilon : ℝ) (maxBatch : ℕ)
    (preferenceGap : Arm → Arm → ℝ) (maximum : Arm)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (hcutoff : 0 < cutoff) (hanchorDelta : 0 < anchorDelta)
    (hanchorDeltaLeOne : anchorDelta ≤ 1)
    (hbudget : ∀ round < sourcePruneRoundCount (Fintype.card Arm),
      fixedSampleBudget lower upper (adaptivePruneRoundDelta pruneDelta round) ≤ maxBatch) : ℝ := by
  classical
  exact pmfProb
    (canonicalOptMaximizeTraceFallbackFinalTraceSourceLaw cutoff anchorDelta pruneDelta fallbackDelta
      finalDelta lower upper epsilon maxBatch preferenceGap maximum hprobability hcutoff hanchorDelta
      hanchorDeltaLeOne hbudget)
    (fun traceFallbackFinalTrace =>
      GoodAnchor preferenceGap lower cutoff traceFallbackFinalTrace.1.1.1 ∧
        traceFallbackFinalTrace.1.1.2.2 = false ∧
          traceFallbackFinalTrace.1.1.2.1.1.card ≤ 2 * cutoff ∧
          (EpsilonMaximum preferenceGap upper traceFallbackFinalTrace.1.1.1 ∨
            maximum ∈ traceFallbackFinalTrace.1.1.2.1.1) ∧
          (optMaximizeTraceFallbackFinalTraceComparisonCount cutoff anchorDelta pruneDelta lower upper
            (finalDelta / (Fintype.card Arm : ℝ)) epsilon fallbackDelta traceFallbackFinalTrace : ℝ) ≤
            (optMaximizePickAnchorComparisonCap (Arm := Arm) cutoff anchorDelta lower : ℝ) +
              sourceLemma5PruneComparisonRateBound (Fintype.card Arm) lower upper pruneDelta +
              (optMaximizeFinalTailComparisonCap traceFallbackFinalTrace.1.1.2.1.1 lower upper
                (finalDelta / (Fintype.card Arm : ℝ)) epsilon fallbackDelta : ℝ))

/--
Compatibility name for the literal early-stopping resource event with Prune's
proved source-rate bound.  The paper claims only the resulting asymptotic
rate, so the canonical path keeps the reusable source bound rather than a
second, trace-shape-specific finite envelope.
-/
noncomputable def canonicalOptMaximizeTraceFallbackFinalTraceSourceLogEnvelopeProbability
    {Arm : Type*} [Fintype Arm] [Nonempty Arm] [DecidableEq Arm]
    (cutoff : ℕ)
    (anchorDelta pruneDelta fallbackDelta finalDelta lower upper epsilon : ℝ) (maxBatch : ℕ)
    (preferenceGap : Arm → Arm → ℝ) (maximum : Arm)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (hcutoff : 0 < cutoff) (hanchorDelta : 0 < anchorDelta)
    (hanchorDeltaLeOne : anchorDelta ≤ 1)
    (hbudget : ∀ round < sourcePruneRoundCount (Fintype.card Arm),
      fixedSampleBudget lower upper (adaptivePruneRoundDelta pruneDelta round) ≤ maxBatch) : ℝ := by
  classical
  exact pmfProb
    (canonicalOptMaximizeTraceFallbackFinalTraceSourceLaw cutoff anchorDelta pruneDelta fallbackDelta
      finalDelta lower upper epsilon maxBatch preferenceGap maximum hprobability hcutoff hanchorDelta
      hanchorDeltaLeOne hbudget)
    (fun traceFallbackFinalTrace =>
      GoodAnchor preferenceGap lower cutoff traceFallbackFinalTrace.1.1.1 ∧
        traceFallbackFinalTrace.1.1.2.2 = false ∧
          traceFallbackFinalTrace.1.1.2.1.1.card ≤ 2 * cutoff ∧
          (EpsilonMaximum preferenceGap upper traceFallbackFinalTrace.1.1.1 ∨
            maximum ∈ traceFallbackFinalTrace.1.1.2.1.1) ∧
          (optMaximizeTraceFallbackFinalTraceComparisonCount cutoff anchorDelta pruneDelta lower upper
            (finalDelta / (Fintype.card Arm : ℝ)) epsilon fallbackDelta traceFallbackFinalTrace : ℝ) ≤
            (optMaximizePickAnchorComparisonCap (Arm := Arm) cutoff anchorDelta lower : ℝ) +
              sourceLemma5PruneComparisonRateBound (Fintype.card Arm) lower upper pruneDelta +
              (optMaximizeFinalTailComparisonCap traceFallbackFinalTrace.1.1.2.1.1 lower upper
                (finalDelta / (Fintype.card Arm : ℝ)) epsilon fallbackDelta : ℝ))

/--
Algorithm 3's literal four-phase resource event at its source `δ / 4`
allocation, using the proved Prune source-rate bound and the literal
early-stopping tail bound.
-/
noncomputable def canonicalOptMaximizeTraceFallbackFinalTraceAlgorithm3SourceEnvelopeProbability
    {Arm : Type*} [Fintype Arm] [Nonempty Arm] [DecidableEq Arm]
    (cutoff : ℕ) (lower upper epsilon delta : ℝ) (maxBatch : ℕ)
    (preferenceGap : Arm → Arm → ℝ) (maximum : Arm)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (hcutoff : 0 < cutoff) (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1)
    (hbudget : ∀ round < sourcePruneRoundCount (Fintype.card Arm),
      fixedSampleBudget lower upper (adaptivePruneRoundDelta (delta / 4) round) ≤ maxBatch) : ℝ := by
  classical
  exact pmfProb
    (canonicalOptMaximizeTraceFallbackFinalTraceSourceLaw cutoff (delta / 4) (delta / 4)
      (delta / 4) (delta / 4) lower upper epsilon maxBatch preferenceGap maximum hprobability
      hcutoff (by linarith) (by linarith) hbudget)
    (fun traceFallbackFinalTrace =>
      GoodAnchor preferenceGap lower cutoff traceFallbackFinalTrace.1.1.1 ∧
        traceFallbackFinalTrace.1.1.2.2 = false ∧
          traceFallbackFinalTrace.1.1.2.1.1.card ≤ 2 * cutoff ∧
          (EpsilonMaximum preferenceGap upper traceFallbackFinalTrace.1.1.1 ∨
            maximum ∈ traceFallbackFinalTrace.1.1.2.1.1) ∧
          (optMaximizeTraceFallbackFinalTraceComparisonCount cutoff (delta / 4) (delta / 4)
            lower upper ((delta / 4) / (Fintype.card Arm : ℝ)) epsilon (delta / 4)
            traceFallbackFinalTrace : ℝ) ≤
            (optMaximizePickAnchorComparisonCap (Arm := Arm) cutoff (delta / 4) lower : ℝ) +
              sourceLemma5PruneComparisonRateBound (Fintype.card Arm) lower upper (delta / 4) +
              optMaximizeFinalTailAlgorithm3SourceBudget traceFallbackFinalTrace.1.1.2.1.1
                lower upper epsilon delta)

/--
The source Theorem-6 event on the literal Algorithm-3 trace: the returned arm
is an `ε`-maximum and the same execution obeys the finite source-log resource
envelope.  The event, rather than two marginal probability statements, is the
relevant object for the source's simultaneous guarantee.
-/
noncomputable def canonicalOptMaximizeTraceFallbackFinalTraceAlgorithm3SourceJointEnvelopeProbability
    {Arm : Type*} [Fintype Arm] [Nonempty Arm] [DecidableEq Arm]
    (cutoff : ℕ) (lower upper epsilon delta : ℝ) (maxBatch : ℕ)
    (preferenceGap : Arm → Arm → ℝ) (maximum : Arm)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (hcutoff : 0 < cutoff) (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1)
    (hbudget : ∀ round < sourcePruneRoundCount (Fintype.card Arm),
      fixedSampleBudget lower upper (adaptivePruneRoundDelta (delta / 4) round) ≤ maxBatch) : ℝ := by
  classical
  exact pmfProb
    (canonicalOptMaximizeTraceFallbackFinalTraceSourceLaw cutoff (delta / 4) (delta / 4)
      (delta / 4) (delta / 4) lower upper epsilon maxBatch preferenceGap maximum hprobability
      hcutoff (by linarith) (by linarith) hbudget)
    (fun traceFallbackFinalTrace =>
      EpsilonMaximum preferenceGap epsilon
          (if traceFallbackFinalTrace.2.2 then traceFallbackFinalTrace.1.1.1 else
            traceFallbackFinalTrace.1.2) ∧
        GoodAnchor preferenceGap lower cutoff traceFallbackFinalTrace.1.1.1 ∧
          traceFallbackFinalTrace.1.1.2.2 = false ∧
            traceFallbackFinalTrace.1.1.2.1.1.card ≤ 2 * cutoff ∧
            (EpsilonMaximum preferenceGap upper traceFallbackFinalTrace.1.1.1 ∨
              maximum ∈ traceFallbackFinalTrace.1.1.2.1.1) ∧
            (optMaximizeTraceFallbackFinalTraceComparisonCount cutoff (delta / 4) (delta / 4)
              lower upper ((delta / 4) / (Fintype.card Arm : ℝ)) epsilon (delta / 4)
              traceFallbackFinalTrace : ℝ) ≤
              (optMaximizePickAnchorComparisonCap (Arm := Arm) cutoff (delta / 4) lower : ℝ) +
                sourceLemma5PruneComparisonRateBound (Fintype.card Arm) lower upper (delta / 4) +
                optMaximizeFinalTailAlgorithm3SourceBudget traceFallbackFinalTrace.1.1.2.1.1
                  lower upper epsilon delta)

/--
The literal early-stopping resource event is at least as likely as the
previous cap event: every queried prefix is bounded pointwise by that cap.
-/
theorem canonicalOptMaximizeTraceFallbackFinalTraceSourceResourceProbability_ge_source_resource
    {Arm : Type*} [Fintype Arm] [Nonempty Arm] [DecidableEq Arm]
    (cutoff : ℕ)
    (anchorDelta pruneDelta fallbackDelta finalDelta lower upper epsilon : ℝ) (maxBatch : ℕ)
    (preferenceGap : Arm → Arm → ℝ) (maximum : Arm)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (hcutoff : 0 < cutoff) (hanchorDelta : 0 < anchorDelta)
    (hanchorDeltaLeOne : anchorDelta ≤ 1)
    (hbudget : ∀ round < sourcePruneRoundCount (Fintype.card Arm),
      fixedSampleBudget lower upper (adaptivePruneRoundDelta pruneDelta round) ≤ maxBatch) :
    canonicalOptMaximizeTraceFallbackFinalSourceResourceProbability cutoff anchorDelta pruneDelta
      fallbackDelta finalDelta lower upper epsilon maxBatch preferenceGap maximum hprobability hcutoff
      hanchorDelta hanchorDeltaLeOne hbudget ≤
      canonicalOptMaximizeTraceFallbackFinalTraceSourceResourceProbability cutoff anchorDelta pruneDelta
        fallbackDelta finalDelta lower upper epsilon maxBatch preferenceGap maximum hprobability hcutoff
        hanchorDelta hanchorDeltaLeOne hbudget := by
  classical
  let roundCount := sourcePruneRoundCount (Fintype.card Arm)
  let anchorLaw : PMF Arm :=
    canonicalFreshPickAnchorSourceOutputLaw cutoff anchorDelta lower preferenceGap hprobability
      hcutoff hanchorDelta hanchorDeltaLeOne
  let pruneTraceLaw : Arm → PMF (stoppedPruneTraceState Arm roundCount × Bool) := fun anchor =>
    freshStoppedPruneTraceStateLaw preferenceGap lower
      (sourceLemma5PruneContractionFactor (Fintype.card Arm) cutoff pruneDelta)
      cutoff anchor Finset.univ
      (canonicalFreshPruneOutcomeLaw preferenceGap hprobability roundCount anchor lower upper
        pruneDelta maxBatch hbudget)
      (canonicalFreshPruneDecision roundCount lower upper pruneDelta maxBatch hbudget) roundCount
  let fallbackLaw : Arm → Finset Arm → PMF Arm := fun anchor candidates =>
    canonicalFreshFinsetSeqEliminateOutputLaw anchor candidates preferenceGap hprobability epsilon
      (fallbackDelta / (candidates.card : ℝ))
  let finalTraceLaw : (anchor : Arm) → (candidates : Finset Arm) → (fallback : Arm) →
      PMF (finalCheckTraceState candidates) := fun anchor candidates _ =>
    canonicalFreshFinalCheckTraceLaw anchor candidates preferenceGap hprobability upper epsilon
      (finalDelta / (Fintype.card Arm : ℝ))
  let sourceEvent : Arm → stoppedPruneTraceState Arm roundCount × Bool → Prop :=
    fun anchor stateFailure =>
      GoodAnchor preferenceGap lower cutoff anchor ∧
        stateFailure.2 = false ∧ stateFailure.1.1.card ≤ 2 * cutoff ∧
          (EpsilonMaximum preferenceGap upper anchor ∨ maximum ∈ stateFailure.1.1) ∧
          (optMaximizeTraceAndTailComparisonCap cutoff anchorDelta pruneDelta lower upper
            (finalDelta / (Fintype.card Arm : ℝ)) epsilon fallbackDelta stateFailure.1.2
            stateFailure.1.1 : ℝ) ≤
            (optMaximizePickAnchorComparisonCap (Arm := Arm) cutoff anchorDelta lower : ℝ) +
              sourceLemma5PruneComparisonRateBound (Fintype.card Arm) lower upper pruneDelta +
              (optMaximizeFinalTailComparisonCap stateFailure.1.1 lower upper
                (finalDelta / (Fintype.card Arm : ℝ)) epsilon fallbackDelta : ℝ)
  let traceEvent : (Arm × (stoppedPruneTraceState Arm roundCount × Bool)) × Arm → Prop :=
    fun traceFallback => sourceEvent traceFallback.1.1 traceFallback.1.2
  let literalEvent : optMaximizeAnchorPruneTraceFallbackFinalTraceState (Arm := Arm) roundCount →
      Prop := fun traceFallbackFinalTrace =>
    GoodAnchor preferenceGap lower cutoff traceFallbackFinalTrace.1.1.1 ∧
      traceFallbackFinalTrace.1.1.2.2 = false ∧
        traceFallbackFinalTrace.1.1.2.1.1.card ≤ 2 * cutoff ∧
        (EpsilonMaximum preferenceGap upper traceFallbackFinalTrace.1.1.1 ∨
          maximum ∈ traceFallbackFinalTrace.1.1.2.1.1) ∧
        (optMaximizeTraceFallbackFinalTraceComparisonCount cutoff anchorDelta pruneDelta lower upper
          (finalDelta / (Fintype.card Arm : ℝ)) epsilon fallbackDelta traceFallbackFinalTrace : ℝ) ≤
          (optMaximizePickAnchorComparisonCap (Arm := Arm) cutoff anchorDelta lower : ℝ) +
            sourceLemma5PruneComparisonRateBound (Fintype.card Arm) lower upper pruneDelta +
            (optMaximizeFinalTailComparisonCap traceFallbackFinalTrace.1.1.2.1.1 lower upper
              (finalDelta / (Fintype.card Arm : ℝ)) epsilon fallbackDelta : ℝ)
  let anchorPruneLaw := optMaximizeAnchorPruneTraceLaw roundCount anchorLaw pruneTraceLaw
  let traceLaw := optMaximizeAnchorPruneTraceFallbackFinalTraceLaw roundCount anchorLaw pruneTraceLaw
    fallbackLaw finalTraceLaw
  have hmarginal : pmfProb traceLaw (fun traceFallbackFinalTrace =>
      traceEvent traceFallbackFinalTrace.1) =
      pmfProb anchorPruneLaw (fun anchorStateFailure =>
        sourceEvent anchorStateFailure.1 anchorStateFailure.2) := by
    calc
      pmfProb traceLaw (fun traceFallbackFinalTrace => traceEvent traceFallbackFinalTrace.1) =
          pmfProb (optMaximizeAnchorPruneTraceFallbackLaw roundCount anchorLaw pruneTraceLaw
            fallbackLaw) traceEvent := by
              exact optMaximizeAnchorPruneTraceFallbackFinalTraceLaw_traceFallback_probability
                roundCount anchorLaw pruneTraceLaw fallbackLaw finalTraceLaw traceEvent
      _ = pmfProb anchorPruneLaw (fun anchorStateFailure =>
          sourceEvent anchorStateFailure.1 anchorStateFailure.2) := by
            exact optMaximizeAnchorPruneTraceFallbackLaw_prior_probability roundCount anchorLaw
              pruneTraceLaw fallbackLaw sourceEvent
  have hsubset : pmfProb traceLaw (fun traceFallbackFinalTrace =>
      traceEvent traceFallbackFinalTrace.1) ≤ pmfProb traceLaw literalEvent := by
    apply pmfProb_le_of_imp
    intro traceFallbackFinalTrace hsource
    rcases hsource with ⟨hgood, hstopped, hcard, hmaximum, hcap⟩
    refine ⟨hgood, hstopped, hcard, hmaximum, ?_⟩
    have hliteral :
        (optMaximizeTraceFallbackFinalTraceComparisonCount cutoff anchorDelta pruneDelta lower upper
          (finalDelta / (Fintype.card Arm : ℝ)) epsilon fallbackDelta traceFallbackFinalTrace : ℝ) ≤
        (optMaximizeTraceAndTailComparisonCap cutoff anchorDelta pruneDelta lower upper
          (finalDelta / (Fintype.card Arm : ℝ)) epsilon fallbackDelta
          traceFallbackFinalTrace.1.1.2.1.2 traceFallbackFinalTrace.1.1.2.1.1 : ℝ) := by
      exact_mod_cast optMaximizeTraceFallbackFinalTraceComparisonCount_le_cap cutoff anchorDelta
        pruneDelta lower upper (finalDelta / (Fintype.card Arm : ℝ)) epsilon fallbackDelta
        traceFallbackFinalTrace
    exact hliteral.trans hcap
  have hcombined : pmfProb anchorPruneLaw (fun anchorStateFailure =>
      sourceEvent anchorStateFailure.1 anchorStateFailure.2) ≤ pmfProb traceLaw literalEvent := by
    rw [← hmarginal]
    exact hsubset
  calc
    canonicalOptMaximizeTraceFallbackFinalSourceResourceProbability cutoff anchorDelta pruneDelta
        fallbackDelta finalDelta lower upper epsilon maxBatch preferenceGap maximum hprobability hcutoff
        hanchorDelta hanchorDeltaLeOne hbudget =
      pmfProb anchorPruneLaw (fun anchorStateFailure =>
        sourceEvent anchorStateFailure.1 anchorStateFailure.2) := by
          unfold canonicalOptMaximizeTraceFallbackFinalSourceResourceProbability
            canonicalOptMaximizeTraceFallbackFinalSourceLaw
          simpa only [roundCount, anchorLaw, pruneTraceLaw, fallbackLaw, sourceEvent,
            anchorPruneLaw] using
            (optMaximizeAnchorPruneTraceFallbackFinalLaw_prior_probability
              (roundCount := roundCount) (anchorLaw := anchorLaw) (pruneTraceLaw := pruneTraceLaw)
              (fallbackLaw := fallbackLaw)
              (finalLaw := fun anchor candidates fallback =>
                canonicalFreshFinalCheckOutputLaw anchor fallback candidates preferenceGap hprobability
                  upper epsilon (finalDelta / (Fintype.card Arm : ℝ)))
              (event := sourceEvent))
    _ ≤ pmfProb traceLaw literalEvent := hcombined
    _ = canonicalOptMaximizeTraceFallbackFinalTraceSourceResourceProbability cutoff anchorDelta
        pruneDelta fallbackDelta finalDelta lower upper epsilon maxBatch preferenceGap maximum hprobability
        hcutoff hanchorDelta hanchorDeltaLeOne hbudget := by
          rfl

/--
The early-stopping source resource event implies its finite Prune source-log
envelope.  This is a pointwise cost simplification on the existing PMF.
-/
theorem canonicalOptMaximizeTraceFallbackFinalTraceSourceLogEnvelopeProbability_ge_resource
    {Arm : Type*} [Fintype Arm] [Nonempty Arm] [DecidableEq Arm]
    (cutoff : ℕ)
    (anchorDelta pruneDelta fallbackDelta finalDelta lower upper epsilon : ℝ) (maxBatch : ℕ)
    (preferenceGap : Arm → Arm → ℝ) (maximum : Arm)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (hcutoff : 0 < cutoff) (hanchorDelta : 0 < anchorDelta)
    (hanchorDeltaLeOne : anchorDelta ≤ 1)
    (hbudget : ∀ round < sourcePruneRoundCount (Fintype.card Arm),
      fixedSampleBudget lower upper (adaptivePruneRoundDelta pruneDelta round) ≤ maxBatch)
    (hpruneDelta : 0 < pruneDelta) (hpruneDeltaLeOne : pruneDelta ≤ 1) :
    canonicalOptMaximizeTraceFallbackFinalTraceSourceResourceProbability cutoff anchorDelta pruneDelta
      fallbackDelta finalDelta lower upper epsilon maxBatch preferenceGap maximum hprobability hcutoff
      hanchorDelta hanchorDeltaLeOne hbudget ≤
      canonicalOptMaximizeTraceFallbackFinalTraceSourceLogEnvelopeProbability cutoff anchorDelta
        pruneDelta fallbackDelta finalDelta lower upper epsilon maxBatch preferenceGap maximum hprobability
        hcutoff hanchorDelta hanchorDeltaLeOne hbudget := by
  rfl

/--
At Algorithm 3's four equal confidence allocations, the generic finite
source-log event implies the single source-log envelope with its tail written
in the source's `log (8 / δ)` form.
-/
theorem canonicalOptMaximizeTraceFallbackFinalTraceAlgorithm3SourceEnvelopeProbability_ge_logEnvelope
    {Arm : Type*} [Fintype Arm] [Nonempty Arm] [DecidableEq Arm]
    (cutoff : ℕ) (lower upper epsilon delta : ℝ) (maxBatch : ℕ)
    (preferenceGap : Arm → Arm → ℝ) (maximum : Arm)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (hcutoff : 0 < cutoff) (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1)
    (hbudget : ∀ round < sourcePruneRoundCount (Fintype.card Arm),
      fixedSampleBudget lower upper (adaptivePruneRoundDelta (delta / 4) round) ≤ maxBatch) :
    canonicalOptMaximizeTraceFallbackFinalTraceSourceLogEnvelopeProbability cutoff (delta / 4)
      (delta / 4) (delta / 4) (delta / 4) lower upper epsilon maxBatch preferenceGap maximum
      hprobability hcutoff (by linarith) (by linarith) hbudget ≤
      canonicalOptMaximizeTraceFallbackFinalTraceAlgorithm3SourceEnvelopeProbability cutoff lower
        upper epsilon delta maxBatch preferenceGap maximum hprobability hcutoff hdelta hdeltaLeOne
        hbudget := by
  classical
  unfold canonicalOptMaximizeTraceFallbackFinalTraceSourceLogEnvelopeProbability
    canonicalOptMaximizeTraceFallbackFinalTraceAlgorithm3SourceEnvelopeProbability
  apply pmfProb_le_of_imp
  intro traceFallbackFinalTrace hsource
  rcases hsource with ⟨hgood, hstopped, hcard, hmaximum, hcount⟩
  refine ⟨hgood, hstopped, hcard, hmaximum, ?_⟩
  have htail := optMaximizeFinalTailComparisonCap_real_le_algorithm3SourceEnvelope
    traceFallbackFinalTrace.1.1.2.1.1 lower upper epsilon delta hdelta hdeltaLeOne
  linarith

/--
Erasing the fallback and final coordinates maps the source four-phase trace
resource event exactly to the already established Pick-Anchor--Prune event.
-/
theorem canonicalOptMaximizeTraceFallbackFinalSourceResourceProbability_eq
    {Arm : Type*} [Fintype Arm] [Nonempty Arm] [DecidableEq Arm]
    (cutoff : ℕ)
    (anchorDelta pruneDelta fallbackDelta finalDelta lower upper epsilon : ℝ) (maxBatch : ℕ)
    (preferenceGap : Arm → Arm → ℝ) (maximum : Arm)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (hcutoff : 0 < cutoff) (hanchorDelta : 0 < anchorDelta)
    (hanchorDeltaLeOne : anchorDelta ≤ 1)
    (hbudget : ∀ round < sourcePruneRoundCount (Fintype.card Arm),
      fixedSampleBudget lower upper (adaptivePruneRoundDelta pruneDelta round) ≤ maxBatch) :
    canonicalOptMaximizeTraceFallbackFinalSourceResourceProbability cutoff anchorDelta pruneDelta
      fallbackDelta finalDelta lower upper epsilon maxBatch preferenceGap maximum hprobability hcutoff
      hanchorDelta hanchorDeltaLeOne hbudget =
      canonicalOptMaximizeTraceAndTailComparisonCapProbability cutoff anchorDelta pruneDelta lower upper
        (finalDelta / (Fintype.card Arm : ℝ)) epsilon fallbackDelta maxBatch preferenceGap maximum
        hprobability hcutoff hanchorDelta hanchorDeltaLeOne hbudget := by
  classical
  unfold canonicalOptMaximizeTraceFallbackFinalSourceResourceProbability
    canonicalOptMaximizeTraceAndTailComparisonCapProbability
    canonicalOptMaximizeTraceFallbackFinalSourceLaw
  simpa using
    (optMaximizeAnchorPruneTraceFallbackFinalLaw_prior_probability
      (roundCount := sourcePruneRoundCount (Fintype.card Arm))
      (anchorLaw := canonicalFreshPickAnchorSourceOutputLaw cutoff anchorDelta lower preferenceGap
        hprobability hcutoff hanchorDelta hanchorDeltaLeOne)
      (pruneTraceLaw := fun anchor =>
        freshStoppedPruneTraceStateLaw preferenceGap lower
          (sourceLemma5PruneContractionFactor (Fintype.card Arm) cutoff pruneDelta)
          cutoff anchor Finset.univ
          (canonicalFreshPruneOutcomeLaw preferenceGap hprobability
            (sourcePruneRoundCount (Fintype.card Arm)) anchor lower upper pruneDelta maxBatch hbudget)
          (canonicalFreshPruneDecision (sourcePruneRoundCount (Fintype.card Arm))
            lower upper pruneDelta maxBatch hbudget)
          (sourcePruneRoundCount (Fintype.card Arm)))
      (fallbackLaw := fun anchor candidates => canonicalFreshFinsetSeqEliminateOutputLaw anchor candidates
        preferenceGap hprobability epsilon (fallbackDelta / (candidates.card : ℝ)))
      (finalLaw := fun anchor candidates fallback => canonicalFreshFinalCheckOutputLaw anchor fallback
        candidates preferenceGap hprobability upper epsilon (finalDelta / (Fintype.card Arm : ℝ)))
      (event := fun anchor stateFailure =>
        GoodAnchor preferenceGap lower cutoff anchor ∧
          stateFailure.2 = false ∧ stateFailure.1.1.card ≤ 2 * cutoff ∧
            (EpsilonMaximum preferenceGap upper anchor ∨ maximum ∈ stateFailure.1.1) ∧
            (optMaximizeTraceAndTailComparisonCap cutoff anchorDelta pruneDelta lower upper
              (finalDelta / (Fintype.card Arm : ℝ)) epsilon fallbackDelta stateFailure.1.2
              stateFailure.1.1 : ℝ) ≤
              (optMaximizePickAnchorComparisonCap (Arm := Arm) cutoff anchorDelta lower : ℝ) +
                sourceLemma5PruneComparisonRateBound (Fintype.card Arm) lower upper pruneDelta +
                (optMaximizeFinalTailComparisonCap stateFailure.1.1 lower upper
                  (finalDelta / (Fintype.card Arm : ℝ)) epsilon fallbackDelta : ℝ)))

/--
The complete source-horizon non-base execution carries the final-tail cap on
the same PMF as Pick-Anchor, the stopped-Prune trace, and both tail outputs.
-/
theorem canonicalOptMaximizeTraceFallbackFinalSourceResourceProbability_ge
    {Arm : Type*} [Fintype Arm] [Nonempty Arm] [DecidableEq Arm]
    (cutoff : ℕ)
    (anchorDelta pruneDelta fallbackDelta finalDelta lower upper epsilon : ℝ) (maxBatch : ℕ)
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
    (hbudget : ∀ round < sourcePruneRoundCount (Fintype.card Arm),
      fixedSampleBudget lower upper (adaptivePruneRoundDelta pruneDelta round) ≤ maxBatch)
    (hupperNonnegative : 0 ≤ upper)
    (hmaximumAbsolute : AbsoluteMaximum preferenceGap maximum)
    (hseparation : lower < upper) (hpruneDelta : 0 < pruneDelta)
    (hpruneDeltaHalf : pruneDelta ≤ 1 / 2)
    (hpruneCutoff : Real.sqrt (6 * (Fintype.card Arm : ℝ) *
      Real.log (Fintype.card Arm : ℝ)) < (cutoff : ℝ))
    (hpruneDeltaLower : (cutoff : ℝ) / (Fintype.card Arm : ℝ) ≤ pruneDelta) :
    1 - (anchorDelta + pruneDelta) ≤
      canonicalOptMaximizeTraceFallbackFinalSourceResourceProbability cutoff anchorDelta pruneDelta
        fallbackDelta finalDelta lower upper epsilon maxBatch preferenceGap maximum hprobability hcutoff
        hanchorDelta hanchorDeltaLeOne hbudget := by
  rw [canonicalOptMaximizeTraceFallbackFinalSourceResourceProbability_eq]
  exact canonicalOptMaximizeTraceAndTailComparisonCap_probability cutoff anchorDelta pruneDelta lower
    upper (finalDelta / (Fintype.card Arm : ℝ)) epsilon fallbackDelta maxBatch preferenceGap maximum
    hprobability ranking hranking hcutoff hcutoffLeCard hanchorDelta hanchorDeltaLeOne hlower
    hantisymmetric hself hcomplete hsst hbudget hupperNonnegative hmaximumAbsolute hseparation
    hpruneDelta hpruneDeltaHalf hpruneCutoff hpruneDeltaLower

/--
The source-horizon early-stopping trace satisfies the same high-probability
resource bound, now for its literal queried final-loop prefix.
-/
theorem canonicalOptMaximizeTraceFallbackFinalTraceSourceResourceProbability_ge
    {Arm : Type*} [Fintype Arm] [Nonempty Arm] [DecidableEq Arm]
    (cutoff : ℕ)
    (anchorDelta pruneDelta fallbackDelta finalDelta lower upper epsilon : ℝ) (maxBatch : ℕ)
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
    (hbudget : ∀ round < sourcePruneRoundCount (Fintype.card Arm),
      fixedSampleBudget lower upper (adaptivePruneRoundDelta pruneDelta round) ≤ maxBatch)
    (hupperNonnegative : 0 ≤ upper)
    (hmaximumAbsolute : AbsoluteMaximum preferenceGap maximum)
    (hseparation : lower < upper) (hpruneDelta : 0 < pruneDelta)
    (hpruneDeltaHalf : pruneDelta ≤ 1 / 2)
    (hpruneCutoff : Real.sqrt (6 * (Fintype.card Arm : ℝ) *
      Real.log (Fintype.card Arm : ℝ)) < (cutoff : ℝ))
    (hpruneDeltaLower : (cutoff : ℝ) / (Fintype.card Arm : ℝ) ≤ pruneDelta) :
    1 - (anchorDelta + pruneDelta) ≤
      canonicalOptMaximizeTraceFallbackFinalTraceSourceResourceProbability cutoff anchorDelta
        pruneDelta fallbackDelta finalDelta lower upper epsilon maxBatch preferenceGap maximum hprobability
        hcutoff hanchorDelta hanchorDeltaLeOne hbudget := by
  calc
    1 - (anchorDelta + pruneDelta) ≤
        canonicalOptMaximizeTraceFallbackFinalSourceResourceProbability cutoff anchorDelta pruneDelta
          fallbackDelta finalDelta lower upper epsilon maxBatch preferenceGap maximum hprobability hcutoff
          hanchorDelta hanchorDeltaLeOne hbudget :=
      canonicalOptMaximizeTraceFallbackFinalSourceResourceProbability_ge cutoff anchorDelta pruneDelta
        fallbackDelta finalDelta lower upper epsilon maxBatch preferenceGap maximum hprobability ranking
        hranking hcutoff hcutoffLeCard hanchorDelta hanchorDeltaLeOne hlower hantisymmetric hself
        hcomplete hsst hbudget hupperNonnegative hmaximumAbsolute hseparation hpruneDelta
        hpruneDeltaHalf hpruneCutoff hpruneDeltaLower
    _ ≤ canonicalOptMaximizeTraceFallbackFinalTraceSourceResourceProbability cutoff anchorDelta
        pruneDelta fallbackDelta finalDelta lower upper epsilon maxBatch preferenceGap maximum hprobability
        hcutoff hanchorDelta hanchorDeltaLeOne hbudget :=
      canonicalOptMaximizeTraceFallbackFinalTraceSourceResourceProbability_ge_source_resource cutoff
        anchorDelta pruneDelta fallbackDelta finalDelta lower upper epsilon maxBatch preferenceGap maximum
        hprobability hcutoff hanchorDelta hanchorDeltaLeOne hbudget

/--
The finite source-log envelope for the literal early-stopping execution holds
with the same first-two-phase resource probability.
-/
theorem canonicalOptMaximizeTraceFallbackFinalTraceSourceLogEnvelopeProbability_ge
    {Arm : Type*} [Fintype Arm] [Nonempty Arm] [DecidableEq Arm]
    (cutoff : ℕ)
    (anchorDelta pruneDelta fallbackDelta finalDelta lower upper epsilon : ℝ) (maxBatch : ℕ)
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
    (hbudget : ∀ round < sourcePruneRoundCount (Fintype.card Arm),
      fixedSampleBudget lower upper (adaptivePruneRoundDelta pruneDelta round) ≤ maxBatch)
    (hupperNonnegative : 0 ≤ upper)
    (hmaximumAbsolute : AbsoluteMaximum preferenceGap maximum)
    (hseparation : lower < upper) (hpruneDelta : 0 < pruneDelta)
    (hpruneDeltaHalf : pruneDelta ≤ 1 / 2)
    (hpruneCutoff : Real.sqrt (6 * (Fintype.card Arm : ℝ) *
      Real.log (Fintype.card Arm : ℝ)) < (cutoff : ℝ))
    (hpruneDeltaLower : (cutoff : ℝ) / (Fintype.card Arm : ℝ) ≤ pruneDelta) :
    1 - (anchorDelta + pruneDelta) ≤
      canonicalOptMaximizeTraceFallbackFinalTraceSourceLogEnvelopeProbability cutoff anchorDelta
        pruneDelta fallbackDelta finalDelta lower upper epsilon maxBatch preferenceGap maximum hprobability
        hcutoff hanchorDelta hanchorDeltaLeOne hbudget := by
  calc
    1 - (anchorDelta + pruneDelta) ≤
        canonicalOptMaximizeTraceFallbackFinalTraceSourceResourceProbability cutoff anchorDelta
          pruneDelta fallbackDelta finalDelta lower upper epsilon maxBatch preferenceGap maximum hprobability
          hcutoff hanchorDelta hanchorDeltaLeOne hbudget :=
      canonicalOptMaximizeTraceFallbackFinalTraceSourceResourceProbability_ge cutoff anchorDelta
        pruneDelta fallbackDelta finalDelta lower upper epsilon maxBatch preferenceGap maximum hprobability
        ranking hranking hcutoff hcutoffLeCard hanchorDelta hanchorDeltaLeOne hlower hantisymmetric
        hself hcomplete hsst hbudget hupperNonnegative hmaximumAbsolute hseparation hpruneDelta
        hpruneDeltaHalf hpruneCutoff hpruneDeltaLower
    _ ≤ canonicalOptMaximizeTraceFallbackFinalTraceSourceLogEnvelopeProbability cutoff anchorDelta
        pruneDelta fallbackDelta finalDelta lower upper epsilon maxBatch preferenceGap maximum hprobability
        hcutoff hanchorDelta hanchorDeltaLeOne hbudget :=
      canonicalOptMaximizeTraceFallbackFinalTraceSourceLogEnvelopeProbability_ge_resource cutoff
        anchorDelta pruneDelta fallbackDelta finalDelta lower upper epsilon maxBatch preferenceGap maximum
        hprobability hcutoff hanchorDelta hanchorDeltaLeOne hbudget hpruneDelta (by linarith)

/--
Algorithm 3's non-base source allocation has one finite resource envelope for
the literal stopped execution.  Its first two phases spend total failure
budget `δ / 2`; the tail resource bound is deterministic on every trace.
-/
theorem canonicalOptMaximizeTraceFallbackFinalTraceAlgorithm3SourceEnvelopeProbability_ge
    {Arm : Type*} [Fintype Arm] [Nonempty Arm] [DecidableEq Arm]
    (cutoff : ℕ) (lower upper epsilon delta : ℝ) (maxBatch : ℕ)
    (preferenceGap : Arm → Arm → ℝ) (maximum : Arm)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (ranking : Fin (Fintype.card Arm) → Arm)
    (hranking : PreferenceRanking preferenceGap ranking)
    (hcutoff : 0 < cutoff) (hcutoffLeCard : cutoff ≤ Fintype.card Arm)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) (hlower : 0 < lower)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hself : ∀ arm, preferenceGap arm arm = 0)
    (hcomplete : PreferenceComplete preferenceGap)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hbudget : ∀ round < sourcePruneRoundCount (Fintype.card Arm),
      fixedSampleBudget lower upper (adaptivePruneRoundDelta (delta / 4) round) ≤ maxBatch)
    (hupperNonnegative : 0 ≤ upper)
    (hmaximumAbsolute : AbsoluteMaximum preferenceGap maximum)
    (hseparation : lower < upper)
    (hpruneCutoff : Real.sqrt (6 * (Fintype.card Arm : ℝ) *
      Real.log (Fintype.card Arm : ℝ)) < (cutoff : ℝ))
    (hpruneDeltaLower : (cutoff : ℝ) / (Fintype.card Arm : ℝ) ≤ delta / 4) :
    1 - delta / 2 ≤
      canonicalOptMaximizeTraceFallbackFinalTraceAlgorithm3SourceEnvelopeProbability cutoff lower
        upper epsilon delta maxBatch preferenceGap maximum hprobability hcutoff hdelta hdeltaLeOne
        hbudget := by
  calc
    1 - delta / 2 = 1 - (delta / 4 + delta / 4) := by ring
    _ ≤ canonicalOptMaximizeTraceFallbackFinalTraceSourceLogEnvelopeProbability cutoff (delta / 4)
        (delta / 4) (delta / 4) (delta / 4) lower upper epsilon maxBatch preferenceGap maximum
        hprobability hcutoff (by linarith) (by linarith) hbudget :=
      canonicalOptMaximizeTraceFallbackFinalTraceSourceLogEnvelopeProbability_ge cutoff (delta / 4)
        (delta / 4) (delta / 4) (delta / 4) lower upper epsilon maxBatch preferenceGap maximum
        hprobability ranking hranking hcutoff hcutoffLeCard (by linarith) (by linarith) hlower
        hantisymmetric hself hcomplete hsst hbudget hupperNonnegative hmaximumAbsolute hseparation
        (by linarith) (by linarith) hpruneCutoff hpruneDeltaLower
    _ ≤ canonicalOptMaximizeTraceFallbackFinalTraceAlgorithm3SourceEnvelopeProbability cutoff
        lower upper epsilon delta maxBatch preferenceGap maximum hprobability hcutoff hdelta hdeltaLeOne
        hbudget :=
      canonicalOptMaximizeTraceFallbackFinalTraceAlgorithm3SourceEnvelopeProbability_ge_logEnvelope
        cutoff lower upper epsilon delta maxBatch preferenceGap maximum hprobability hcutoff hdelta
        hdeltaLeOne hbudget

/--
The non-base branch of Theorem 6 has a single finite-PMF event on which the
literal returned arm is an `ε`-maximum and the complete queried execution
satisfies Algorithm 3's finite source-log resource envelope.
-/
theorem canonicalOptMaximizeTraceFallbackFinalTraceAlgorithm3SourceJointEnvelopeProbability_ge_of_anchorPrune
    {Arm : Type*} [Fintype Arm] [Nonempty Arm] [DecidableEq Arm]
    (cutoff : ℕ) (lower upper epsilon delta : ℝ) (maxBatch : ℕ)
    (preferenceGap : Arm → Arm → ℝ) (maximum : Arm)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (ranking : Fin (Fintype.card Arm) → Arm)
    (hranking : PreferenceRanking preferenceGap ranking)
    (hcutoff : 0 < cutoff) (hcutoffLeCard : cutoff ≤ Fintype.card Arm)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) (hlower : 0 < lower)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hself : ∀ arm, preferenceGap arm arm = 0)
    (hcomplete : PreferenceComplete preferenceGap)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hbudget : ∀ round < sourcePruneRoundCount (Fintype.card Arm),
      fixedSampleBudget lower upper (adaptivePruneRoundDelta (delta / 4) round) ≤ maxBatch)
    (hupperNonnegative : 0 ≤ upper)
    (hmaximumAbsolute : AbsoluteMaximum preferenceGap maximum)
    (hseparation : lower < upper)
    (firstFailure : ℝ)
    (hfirstStrong : 1 - firstFailure ≤
      canonicalOptMaximizeAnchorPruneTraceSourceSuccessProbability cutoff (delta / 4)
        (delta / 4) lower upper maxBatch preferenceGap maximum hprobability hcutoff
        (by linarith) (by linarith) hbudget)
    (hfailureBudget : firstFailure + delta / 4 + delta / 4 ≤ delta)
    (hepsilon : 0 < epsilon) (hfinalSeparation : upper < epsilon) :
    1 - delta ≤
      canonicalOptMaximizeTraceFallbackFinalTraceAlgorithm3SourceJointEnvelopeProbability cutoff
        lower upper epsilon delta maxBatch preferenceGap maximum hprobability hcutoff hdelta hdeltaLeOne
        hbudget := by
  classical
  let roundCount := sourcePruneRoundCount (Fintype.card Arm)
  let anchorLaw : PMF Arm :=
    canonicalFreshPickAnchorSourceOutputLaw cutoff (delta / 4) lower preferenceGap hprobability
      hcutoff (by linarith) (by linarith)
  let pruneTraceLaw : Arm → PMF (stoppedPruneTraceState Arm roundCount × Bool) := fun anchor =>
    freshStoppedPruneTraceStateLaw preferenceGap lower
      (sourceLemma5PruneContractionFactor (Fintype.card Arm) cutoff (delta / 4))
      cutoff anchor Finset.univ
      (canonicalFreshPruneOutcomeLaw preferenceGap hprobability roundCount anchor
        lower upper (delta / 4) maxBatch hbudget)
      (canonicalFreshPruneDecision roundCount lower upper (delta / 4) maxBatch hbudget)
      roundCount
  let fallbackLaw : Arm → Finset Arm → PMF Arm := fun anchor candidates =>
    canonicalFreshFinsetSeqEliminateOutputLaw anchor candidates preferenceGap hprobability epsilon
      ((delta / 4) / (candidates.card : ℝ))
  let finalLaw : Arm → Finset Arm → Arm → PMF Arm := fun anchor candidates fallback =>
    canonicalFreshFinalCheckOutputLaw anchor fallback candidates preferenceGap hprobability upper epsilon
      ((delta / 4) / (Fintype.card Arm : ℝ))
  let finalTraceLaw : (anchor : Arm) → (candidates : Finset Arm) → (fallback : Arm) →
      PMF (finalCheckTraceState candidates) := fun anchor candidates _ =>
    canonicalFreshFinalCheckTraceLaw anchor candidates preferenceGap hprobability upper epsilon
      ((delta / 4) / (Fintype.card Arm : ℝ))
  let firstResource : Arm → stoppedPruneTraceState Arm roundCount × Bool → Prop :=
    fun anchor stateFailure =>
      GoodAnchor preferenceGap lower cutoff anchor ∧
        stateFailure.2 = false ∧ stateFailure.1.1.card ≤ 2 * cutoff ∧
          (stoppedPruneTraceComparisonCount roundCount cutoff lower upper (delta / 4)
            stateFailure.1.2 : ℝ) ≤
            sourceLemma5PruneComparisonRateBound (Fintype.card Arm) lower upper (delta / 4) ∧
          (EpsilonMaximum preferenceGap upper anchor ∨ maximum ∈ stateFailure.1.1)
  let traceGood : Arm → stoppedPruneTraceState Arm roundCount × Bool → Prop :=
    fun anchor stateFailure => firstResource anchor stateFailure ∧
      EpsilonMaximum preferenceGap upper anchor
  let maximumRetained : Arm → stoppedPruneTraceState Arm roundCount × Bool → Prop :=
    fun anchor stateFailure => firstResource anchor stateFailure ∧ maximum ∈ stateFailure.1.1
  let fallbackSuccess : Arm → stoppedPruneTraceState Arm roundCount × Bool → Arm → Prop :=
    fun _ _ fallback => EpsilonMaximum preferenceGap epsilon fallback
  let priorSuccess : (Arm × (stoppedPruneTraceState Arm roundCount × Bool)) × Arm → Prop :=
    fun traceFallback =>
      traceGood traceFallback.1.1 traceFallback.1.2 ∨
        (maximumRetained traceFallback.1.1 traceFallback.1.2 ∧
          fallbackSuccess traceFallback.1.1 traceFallback.1.2 traceFallback.2)
  let outputSuccess : Arm → stoppedPruneTraceState Arm roundCount × Bool → Arm → Arm → Prop :=
    fun _ _ _ output => EpsilonMaximum preferenceGap epsilon output
  have hfirstResource : 1 - firstFailure ≤
      pmfProb (optMaximizeAnchorPruneTraceLaw roundCount anchorLaw pruneTraceLaw)
        (fun anchorStateFailure => firstResource anchorStateFailure.1 anchorStateFailure.2) := by
    unfold canonicalOptMaximizeAnchorPruneTraceSourceSuccessProbability
      canonicalOptMaximizeAnchorPruneTraceSourceLaw at hfirstStrong
    simpa only [firstResource, anchorLaw, pruneTraceLaw, roundCount] using hfirstStrong
  have hfirst : 1 - firstFailure ≤
      pmfProb (optMaximizeAnchorPruneTraceLaw roundCount anchorLaw pruneTraceLaw)
        (fun anchorStateFailure =>
          traceGood anchorStateFailure.1 anchorStateFailure.2 ∨
            maximumRetained anchorStateFailure.1 anchorStateFailure.2) := by
    apply hfirstResource.trans
    apply pmfProb_le_of_imp
    intro anchorStateFailure hsuccess
    rcases hsuccess.2.2.2.2 with hanchor | hmaximum
    · exact Or.inl ⟨hsuccess, hanchor⟩
    · exact Or.inr ⟨hsuccess, hmaximum⟩
  have hfallback : ∀ (anchor : Arm)
      (stateFailure : stoppedPruneTraceState Arm roundCount × Bool),
      maximumRetained anchor stateFailure →
      pmfProb (fallbackLaw anchor stateFailure.1.1)
        (fun fallback => ¬ fallbackSuccess anchor stateFailure fallback) ≤ delta / 4 := by
    intro anchor stateFailure hretained
    have hsource := canonicalFreshFinsetSeqEliminate_epsilonMaximum_probability_of_sourceSchedule
      anchor stateFailure.1.1 preferenceGap hprobability epsilon (delta / 4) hantisymmetric hself hsst
      hepsilon (by linarith) (by linarith) maximum hmaximumAbsolute hretained.2
    unfold canonicalFreshFinsetSeqEliminateEpsilonMaximumProbability at hsource
    have hsource' : 1 - delta / 4 ≤
        pmfProb (fallbackLaw anchor stateFailure.1.1)
          (EpsilonMaximum preferenceGap epsilon) := by
      simpa only [fallbackLaw, pmfProbClassical] using hsource
    change pmfProb (fallbackLaw anchor stateFailure.1.1)
      (fun fallback => ¬ EpsilonMaximum preferenceGap epsilon fallback) ≤ delta / 4
    rw [pmfProb_compl]
    linarith
  have hprior := optMaximizeAnchorPruneTraceFallbackLaw_branch_success_probability_ge_one_sub_add
    roundCount anchorLaw pruneTraceLaw fallbackLaw traceGood maximumRetained fallbackSuccess
    firstFailure (delta / 4) (by linarith) hfirst hfallback
  have hcardPositiveNat : 0 < Fintype.card Arm := Fintype.card_pos_iff.mpr inferInstance
  have hcardPositive : 0 < (Fintype.card Arm : ℝ) := by exact_mod_cast hcardPositiveNat
  have heta : 0 < (delta / 4) / (Fintype.card Arm : ℝ) := by positivity
  have hetaLeOne : (delta / 4) / (Fintype.card Arm : ℝ) ≤ 1 := by
    calc
      (delta / 4) / (Fintype.card Arm : ℝ) ≤ delta / 4 :=
        div_le_self (by linarith) (by
          exact_mod_cast (Nat.succ_le_iff.mpr hcardPositiveNat))
      _ ≤ 1 := by linarith
  have hfinal : ∀ traceFallback,
      priorSuccess traceFallback →
      1 - delta / 4 ≤
        pmfProb (finalLaw traceFallback.1.1 traceFallback.1.2.1.1 traceFallback.2)
          (outputSuccess traceFallback.1.1 traceFallback.1.2 traceFallback.2) := by
    intro traceFallback hsuccess
    have hcardLe : traceFallback.1.2.1.1.card ≤ Fintype.card Arm := Finset.card_le_univ _
    have hcost : (traceFallback.1.2.1.1.card : ℝ) *
        ((delta / 4) / (Fintype.card Arm : ℝ)) ≤ delta / 4 := by
      calc
        (traceFallback.1.2.1.1.card : ℝ) * ((delta / 4) / (Fintype.card Arm : ℝ)) ≤
            (Fintype.card Arm : ℝ) * ((delta / 4) / (Fintype.card Arm : ℝ)) := by
              apply mul_le_mul_of_nonneg_right
                (by exact_mod_cast hcardLe) (le_of_lt heta)
        _ = delta / 4 := by field_simp [ne_of_gt hcardPositive]
    rcases hsuccess with ⟨_, hanchor⟩ | ⟨⟨_, hmaximumMem⟩, hfallbackSuccess⟩
    · have hphase := canonicalFreshFinalCheck_epsilonMaximum_probability_of_anchor
        traceFallback.1.1 traceFallback.2 traceFallback.1.2.1.1 preferenceGap hprobability epsilon
        upper epsilon ((delta / 4) / (Fintype.card Arm : ℝ)) hantisymmetric hanchor
        (le_of_lt hfinalSeparation) hfinalSeparation heta hetaLeOne
      change 1 - delta / 4 ≤ pmfProb
        (canonicalFreshFinalCheckOutputLaw traceFallback.1.1 traceFallback.2 traceFallback.1.2.1.1
          preferenceGap hprobability upper epsilon ((delta / 4) / (Fintype.card Arm : ℝ)))
        (EpsilonMaximum preferenceGap epsilon)
      rw [pmfProbClassical_eq_pmfProb] at hphase
      linarith
    · have hphase := canonicalFreshFinalCheck_epsilonMaximum_probability_of_retained_maximum_or_anchor
        traceFallback.1.1 traceFallback.2 maximum traceFallback.1.2.1.1 preferenceGap hprobability
        epsilon upper epsilon ((delta / 4) / (Fintype.card Arm : ℝ)) hantisymmetric hsst
        (le_of_lt hepsilon)
        hmaximumAbsolute hmaximumMem hfallbackSuccess le_rfl hfinalSeparation heta hetaLeOne
      change 1 - delta / 4 ≤ pmfProb
        (canonicalFreshFinalCheckOutputLaw traceFallback.1.1 traceFallback.2 traceFallback.1.2.1.1
          preferenceGap hprobability upper epsilon ((delta / 4) / (Fintype.card Arm : ℝ)))
        (EpsilonMaximum preferenceGap epsilon)
      rw [pmfProbClassical_eq_pmfProb] at hphase
      linarith
  have hcompose := optMaximizeAnchorPruneTraceFallbackFinalLaw_prior_and_success_probability_ge_one_sub_add
    roundCount anchorLaw pruneTraceLaw fallbackLaw finalLaw priorSuccess outputSuccess
    (firstFailure + delta / 4) (delta / 4) (by linarith)
    (by simpa only [priorSuccess, anchorLaw, pruneTraceLaw, fallbackLaw] using hprior) hfinal
  have hmap := optMaximizeAnchorPruneTraceFallbackFinalTraceLaw_map_history_output_eq
    roundCount anchorLaw pruneTraceLaw fallbackLaw finalTraceLaw finalLaw (by
      intro anchor candidates fallback
      simpa only [finalTraceLaw, finalLaw, canonicalFreshFinalCheckTraceOutputLaw] using
        (canonicalFreshFinalCheckTraceOutputLaw_eq anchor fallback candidates preferenceGap hprobability
          upper epsilon ((delta / 4) / (Fintype.card Arm : ℝ))) )
  unfold canonicalOptMaximizeTraceFallbackFinalTraceAlgorithm3SourceJointEnvelopeProbability
    canonicalOptMaximizeTraceFallbackFinalTraceSourceLaw
  change 1 - delta ≤
    pmfProb (optMaximizeAnchorPruneTraceFallbackFinalTraceLaw roundCount anchorLaw pruneTraceLaw
      fallbackLaw finalTraceLaw) (fun traceFallbackFinalTrace =>
        EpsilonMaximum preferenceGap epsilon
            (if traceFallbackFinalTrace.2.2 then traceFallbackFinalTrace.1.1.1 else
              traceFallbackFinalTrace.1.2) ∧
          GoodAnchor preferenceGap lower cutoff traceFallbackFinalTrace.1.1.1 ∧
            traceFallbackFinalTrace.1.1.2.2 = false ∧
              traceFallbackFinalTrace.1.1.2.1.1.card ≤ 2 * cutoff ∧
              (EpsilonMaximum preferenceGap upper traceFallbackFinalTrace.1.1.1 ∨
                maximum ∈ traceFallbackFinalTrace.1.1.2.1.1) ∧
              (optMaximizeTraceFallbackFinalTraceComparisonCount cutoff (delta / 4) (delta / 4)
                lower upper ((delta / 4) / (Fintype.card Arm : ℝ)) epsilon (delta / 4)
                traceFallbackFinalTrace : ℝ) ≤
                (optMaximizePickAnchorComparisonCap (Arm := Arm) cutoff (delta / 4) lower : ℝ) +
                  sourceLemma5PruneComparisonRateBound (Fintype.card Arm) lower upper (delta / 4) +
                  optMaximizeFinalTailAlgorithm3SourceBudget traceFallbackFinalTrace.1.1.2.1.1
                    lower upper epsilon delta)
  calc
    1 - delta ≤ 1 - ((firstFailure + delta / 4) + delta / 4) := by linarith
    _ ≤ pmfProb (optMaximizeAnchorPruneTraceFallbackFinalLaw roundCount anchorLaw pruneTraceLaw
        fallbackLaw finalLaw) (fun traceFallbackOutput =>
          priorSuccess traceFallbackOutput.1 ∧
            outputSuccess traceFallbackOutput.1.1.1 traceFallbackOutput.1.1.2
              traceFallbackOutput.1.2 traceFallbackOutput.2) := hcompose
    _ = pmfProb (optMaximizeAnchorPruneTraceFallbackFinalTraceLaw roundCount anchorLaw pruneTraceLaw
        fallbackLaw finalTraceLaw) (fun traceFallbackFinalTrace =>
          priorSuccess traceFallbackFinalTrace.1 ∧
            EpsilonMaximum preferenceGap epsilon
              (if traceFallbackFinalTrace.2.2 then traceFallbackFinalTrace.1.1.1 else
                traceFallbackFinalTrace.1.2)) := by
      rw [← hmap, pmfProb_map]
    _ ≤ pmfProb (optMaximizeAnchorPruneTraceFallbackFinalTraceLaw roundCount anchorLaw pruneTraceLaw
        fallbackLaw finalTraceLaw) (fun traceFallbackFinalTrace =>
          EpsilonMaximum preferenceGap epsilon
              (if traceFallbackFinalTrace.2.2 then traceFallbackFinalTrace.1.1.1 else
                traceFallbackFinalTrace.1.2) ∧
            GoodAnchor preferenceGap lower cutoff traceFallbackFinalTrace.1.1.1 ∧
              traceFallbackFinalTrace.1.1.2.2 = false ∧
                traceFallbackFinalTrace.1.1.2.1.1.card ≤ 2 * cutoff ∧
                (EpsilonMaximum preferenceGap upper traceFallbackFinalTrace.1.1.1 ∨
                  maximum ∈ traceFallbackFinalTrace.1.1.2.1.1) ∧
                (optMaximizeTraceFallbackFinalTraceComparisonCount cutoff (delta / 4) (delta / 4)
                  lower upper ((delta / 4) / (Fintype.card Arm : ℝ)) epsilon (delta / 4)
                  traceFallbackFinalTrace : ℝ) ≤
                  (optMaximizePickAnchorComparisonCap (Arm := Arm) cutoff (delta / 4) lower : ℝ) +
                    sourceLemma5PruneComparisonRateBound (Fintype.card Arm) lower upper (delta / 4) +
                    optMaximizeFinalTailAlgorithm3SourceBudget traceFallbackFinalTrace.1.1.2.1.1
                      lower upper epsilon delta) := by
      apply pmfProb_le_of_imp
      intro traceFallbackFinalTrace hsuccess
      rcases hsuccess with ⟨hprior, houtput⟩
      have hfirst : firstResource traceFallbackFinalTrace.1.1.1 traceFallbackFinalTrace.1.1.2 := by
        rcases hprior with hprior | hprior
        · exact hprior.1
        · exact hprior.1.1
      rcases hfirst with ⟨hgood, hstopped, hcard, hprune, hbranch⟩
      refine ⟨houtput, hgood, hstopped, hcard, hbranch, ?_⟩
      have htail := optMaximizeFinalTailComparisonCap_real_le_algorithm3SourceEnvelope
        traceFallbackFinalTrace.1.1.2.1.1 lower upper epsilon delta hdelta hdeltaLeOne
      have hliteral :
          (optMaximizeTraceFallbackFinalTraceComparisonCount cutoff (delta / 4) (delta / 4)
            lower upper ((delta / 4) / (Fintype.card Arm : ℝ)) epsilon (delta / 4)
            traceFallbackFinalTrace : ℝ) ≤
            (optMaximizeTraceAndTailComparisonCap cutoff (delta / 4) (delta / 4) lower upper
              ((delta / 4) / (Fintype.card Arm : ℝ)) epsilon (delta / 4)
              traceFallbackFinalTrace.1.1.2.1.2 traceFallbackFinalTrace.1.1.2.1.1 : ℝ) := by
        exact_mod_cast optMaximizeTraceFallbackFinalTraceComparisonCount_le_cap cutoff (delta / 4)
          (delta / 4) lower upper ((delta / 4) / (Fintype.card Arm : ℝ)) epsilon (delta / 4)
          traceFallbackFinalTrace
      simp only [optMaximizeTraceAndTailComparisonCap, Nat.cast_add] at hliteral
      dsimp only [roundCount] at hprune hliteral
      linarith

/-- The traditional Lemma-15 budget premise recovers the equal-allocation
specialization of the generic four-phase composition theorem. -/
theorem canonicalOptMaximizeTraceFallbackFinalTraceAlgorithm3SourceJointEnvelopeProbability_ge
    {Arm : Type*} [Fintype Arm] [Nonempty Arm] [DecidableEq Arm]
    (cutoff : ℕ) (lower upper epsilon delta : ℝ) (maxBatch : ℕ)
    (preferenceGap : Arm → Arm → ℝ) (maximum : Arm)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (ranking : Fin (Fintype.card Arm) → Arm)
    (hranking : PreferenceRanking preferenceGap ranking)
    (hcutoff : 0 < cutoff) (hcutoffLeCard : cutoff ≤ Fintype.card Arm)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) (hlower : 0 < lower)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hself : ∀ arm, preferenceGap arm arm = 0)
    (hcomplete : PreferenceComplete preferenceGap)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hbudget : ∀ round < sourcePruneRoundCount (Fintype.card Arm),
      fixedSampleBudget lower upper (adaptivePruneRoundDelta (delta / 4) round) ≤ maxBatch)
    (hupperNonnegative : 0 ≤ upper)
    (hmaximumAbsolute : AbsoluteMaximum preferenceGap maximum)
    (hseparation : lower < upper)
    (hpruneCutoff : Real.sqrt (6 * (Fintype.card Arm : ℝ) *
      Real.log (Fintype.card Arm : ℝ)) < (cutoff : ℝ))
    (hpruneDeltaLower : (cutoff : ℝ) / (Fintype.card Arm : ℝ) ≤ delta / 4)
    (hepsilon : 0 < epsilon) (hfinalSeparation : upper < epsilon) :
    1 - delta ≤
      canonicalOptMaximizeTraceFallbackFinalTraceAlgorithm3SourceJointEnvelopeProbability cutoff
        lower upper epsilon delta maxBatch preferenceGap maximum hprobability hcutoff hdelta hdeltaLeOne
        hbudget := by
  have hfirstStrong := canonicalOptMaximizeAnchorPruneTraceSource_success_probability
    cutoff (delta / 4) (delta / 4) lower upper maxBatch preferenceGap maximum hprobability ranking
    hranking hcutoff hcutoffLeCard (by linarith) (by linarith) hlower hantisymmetric hself
    hcomplete hsst hbudget hupperNonnegative hmaximumAbsolute hseparation (by linarith)
    (by linarith) hpruneCutoff hpruneDeltaLower
  exact
    canonicalOptMaximizeTraceFallbackFinalTraceAlgorithm3SourceJointEnvelopeProbability_ge_of_anchorPrune
      cutoff lower upper epsilon delta maxBatch preferenceGap maximum hprobability ranking hranking
      hcutoff hcutoffLeCard hdelta hdeltaLeOne hlower hantisymmetric hself hcomplete hsst hbudget
      hupperNonnegative hmaximumAbsolute hseparation
      (delta / 4 + delta / 4) hfirstStrong (by ring_nf; exact le_rfl) hepsilon
      hfinalSeparation

/-- Above the base branch, a population of at least eight charges the raw
inverse-square contraction tail to one eighth of the displayed confidence. -/
theorem one_div_nat_sq_le_delta_div_eight
    (armCount : ℕ) (delta : ℝ) (hcard : 8 ≤ armCount)
    (hdeltaLower : 1 / (armCount : ℝ) ≤ delta) :
    1 / (armCount : ℝ) ^ 2 ≤ delta / 8 := by
  have hcardReal : (8 : ℝ) ≤ armCount := by exact_mod_cast hcard
  have hcardPos : (0 : ℝ) < armCount := lt_of_lt_of_le (by norm_num) hcardReal
  have hinvNonnegative : 0 ≤ 1 / (armCount : ℝ) := by positivity
  have hdeltaNonnegative : 0 ≤ delta := hinvNonnegative.trans hdeltaLower
  have hinvEight : 1 / (armCount : ℝ) ≤ (1 / 8 : ℝ) :=
    one_div_le_one_div_of_le (by norm_num) hcardReal
  calc
    1 / (armCount : ℝ) ^ 2 =
        (1 / (armCount : ℝ)) * (1 / (armCount : ℝ)) := by ring
    _ ≤ delta * (1 / (armCount : ℝ)) := by
      exact mul_le_mul_of_nonneg_right hdeltaLower hinvNonnegative
    _ ≤ delta * (1 / 8 : ℝ) := by
      exact mul_le_mul_of_nonneg_left hinvEight hdeltaNonnegative
    _ = delta / 8 := by ring

/--
Supplement Lemma 17 at Algorithm 3's printed cutoff and `delta / 4` phase
budgets. The small-population branch is already stopped; in the remaining
branch the printed `1/n ≤ delta` premise absorbs the inverse-square tail.
-/
theorem canonicalOptMaximizeAnchorPruneTraceSource_success_probability_algorithm3_sourceCutoff
    {Arm : Type*} [Fintype Arm] [Nonempty Arm] [DecidableEq Arm]
    (lower upper delta : ℝ) (maxBatch : ℕ)
    (preferenceGap : Arm → Arm → ℝ) (maximum : Arm)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (ranking : Fin (Fintype.card Arm) → Arm)
    (hranking : PreferenceRanking preferenceGap ranking)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) (hlower : 0 < lower)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hself : ∀ arm, preferenceGap arm arm = 0)
    (hcomplete : PreferenceComplete preferenceGap)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hbudget : ∀ round < sourcePruneRoundCount (Fintype.card Arm),
      fixedSampleBudget lower upper (adaptivePruneRoundDelta (delta / 4) round) ≤ maxBatch)
    (hupperNonnegative : 0 ≤ upper)
    (hmaximumAbsolute : AbsoluteMaximum preferenceGap maximum)
    (hseparation : lower < upper)
    (hdeltaLower : 1 / (Fintype.card Arm : ℝ) ≤ delta) :
    let cutoff := sourceOptMaximizeCutoff (Fintype.card Arm)
    1 - delta / 2 ≤
      canonicalOptMaximizeAnchorPruneTraceSourceSuccessProbability
        cutoff (delta / 4) (delta / 4) lower upper maxBatch preferenceGap maximum
        hprobability (sourceOptMaximizeCutoff_pos (Fintype.card Arm) Fintype.card_pos)
        (by linarith) (by linarith) hbudget := by
  dsimp only
  let cutoff := sourceOptMaximizeCutoff (Fintype.card Arm)
  have hcutoff : 0 < cutoff := sourceOptMaximizeCutoff_pos _ Fintype.card_pos
  have hcutoffLeCard : cutoff ≤ Fintype.card Arm := sourceOptMaximizeCutoff_le_armCount _
  by_cases hsmall : Fintype.card Arm ≤ 2 * cutoff
  · have hfirst :=
      canonicalOptMaximizeAnchorPruneTraceSource_success_probability_of_initial_small
        cutoff (delta / 4) (delta / 4) lower upper maxBatch preferenceGap maximum hprobability
        ranking hranking hcutoff hcutoffLeCard (by linarith) (by linarith) hlower
        hantisymmetric hself hcomplete hsst hbudget (by linarith) (by linarith) hsmall
    linarith
  · have hlarge : 2 * cutoff < Fintype.card Arm := by omega
    have hcutoffLt : cutoff < Fintype.card Arm := by omega
    have hpruneCutoff : Real.sqrt (6 * (Fintype.card Arm : ℝ) *
        Real.log (Fintype.card Arm : ℝ)) < (cutoff : ℝ) := by
      simpa only [cutoff] using
        sourceOptMaximizeCutoff_sqrt_lt_of_lt_armCount (Fintype.card Arm) hcutoffLt
    have hcardNine : 9 ≤ Fintype.card Arm := by
      simpa only [cutoff] using
        nine_le_armCount_of_two_mul_sourceOptMaximizeCutoff_lt (Fintype.card Arm) hlarge
    have htail : 1 / (Fintype.card Arm : ℝ) ^ 2 ≤ delta / 8 :=
      one_div_nat_sq_le_delta_div_eight (Fintype.card Arm) delta (by omega) hdeltaLower
    have hfirst := canonicalOptMaximizeAnchorPruneTraceSource_success_probability_raw
      cutoff (delta / 4) (delta / 4) lower upper maxBatch preferenceGap maximum hprobability
      ranking hranking hcutoff hcutoffLeCard (by linarith) (by linarith) hlower hantisymmetric
      hself hcomplete hsst hbudget hupperNonnegative hmaximumAbsolute hseparation (by linarith)
      (by linarith) hpruneCutoff
    linarith

/-- On the literal non-base Algorithm-3 branch, the source's equal `δ/4`
allocations close without the extra cutoff-ratio premise.  If the population
already meets Prune's stopping threshold, Prune is deterministic; otherwise
the rounded source cutoff forces a large enough population to absorb the raw
inverse-square contraction tail. -/
theorem canonicalOptMaximizeTraceFallbackFinalTraceAlgorithm3SourceJointEnvelopeProbability_ge_nonbase
    {Arm : Type*} [Fintype Arm] [Nonempty Arm] [DecidableEq Arm]
    (lower upper epsilon delta : ℝ) (maxBatch : ℕ)
    (preferenceGap : Arm → Arm → ℝ) (maximum : Arm)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (ranking : Fin (Fintype.card Arm) → Arm)
    (hranking : PreferenceRanking preferenceGap ranking)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) (hlower : 0 < lower)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hself : ∀ arm, preferenceGap arm arm = 0)
    (hcomplete : PreferenceComplete preferenceGap)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hbudget : ∀ round < sourcePruneRoundCount (Fintype.card Arm),
      fixedSampleBudget lower upper (adaptivePruneRoundDelta (delta / 4) round) ≤ maxBatch)
    (hupperNonnegative : 0 ≤ upper)
    (hmaximumAbsolute : AbsoluteMaximum preferenceGap maximum)
    (hseparation : lower < upper)
    (hepsilon : 0 < epsilon) (hfinalSeparation : upper < epsilon)
    (hnonbase : 1 / (Fintype.card Arm : ℝ) < delta) :
    let cutoff := sourceOptMaximizeCutoff (Fintype.card Arm)
    1 - delta ≤
      canonicalOptMaximizeTraceFallbackFinalTraceAlgorithm3SourceJointEnvelopeProbability cutoff
        lower upper epsilon delta maxBatch preferenceGap maximum hprobability
        (sourceOptMaximizeCutoff_pos (Fintype.card Arm) Fintype.card_pos)
        hdelta hdeltaLeOne hbudget := by
  dsimp only
  let cutoff := sourceOptMaximizeCutoff (Fintype.card Arm)
  have hcutoff : 0 < cutoff := sourceOptMaximizeCutoff_pos _ Fintype.card_pos
  have hcutoffLeCard : cutoff ≤ Fintype.card Arm := sourceOptMaximizeCutoff_le_armCount _
  by_cases hsmall : Fintype.card Arm ≤ 2 * cutoff
  · have hfirstStrong :=
      canonicalOptMaximizeAnchorPruneTraceSource_success_probability_of_initial_small
        cutoff (delta / 4) (delta / 4) lower upper maxBatch preferenceGap maximum hprobability
        ranking hranking hcutoff hcutoffLeCard (by linarith) (by linarith) hlower
        hantisymmetric hself hcomplete hsst hbudget (by linarith) (by linarith) hsmall
    exact
      canonicalOptMaximizeTraceFallbackFinalTraceAlgorithm3SourceJointEnvelopeProbability_ge_of_anchorPrune
        cutoff lower upper epsilon delta maxBatch preferenceGap maximum hprobability ranking hranking
        hcutoff hcutoffLeCard hdelta hdeltaLeOne hlower hantisymmetric hself hcomplete hsst hbudget
        hupperNonnegative hmaximumAbsolute hseparation (delta / 4) hfirstStrong (by linarith)
        hepsilon hfinalSeparation
  · have hlarge : 2 * cutoff < Fintype.card Arm := by omega
    have hcutoffLt : cutoff < Fintype.card Arm := by omega
    have hpruneCutoff : Real.sqrt (6 * (Fintype.card Arm : ℝ) *
        Real.log (Fintype.card Arm : ℝ)) < (cutoff : ℝ) := by
      simpa only [cutoff] using
        sourceOptMaximizeCutoff_sqrt_lt_of_lt_armCount (Fintype.card Arm) hcutoffLt
    have hcardNine : 9 ≤ Fintype.card Arm := by
      simpa only [cutoff] using
        nine_le_armCount_of_two_mul_sourceOptMaximizeCutoff_lt (Fintype.card Arm) hlarge
    have htail : 1 / (Fintype.card Arm : ℝ) ^ 2 ≤ delta / 8 :=
      one_div_nat_sq_le_delta_div_eight (Fintype.card Arm) delta (by omega) hnonbase.le
    have hfirstStrong := canonicalOptMaximizeAnchorPruneTraceSource_success_probability_raw
      cutoff (delta / 4) (delta / 4) lower upper maxBatch preferenceGap maximum hprobability
      ranking hranking hcutoff hcutoffLeCard (by linarith) (by linarith) hlower hantisymmetric
      hself hcomplete hsst hbudget hupperNonnegative hmaximumAbsolute hseparation (by linarith)
      (by linarith) hpruneCutoff
    exact
      canonicalOptMaximizeTraceFallbackFinalTraceAlgorithm3SourceJointEnvelopeProbability_ge_of_anchorPrune
        cutoff lower upper epsilon delta maxBatch preferenceGap maximum hprobability ranking hranking
        hcutoff hcutoffLeCard hdelta hdeltaLeOne hlower hantisymmetric hself hcomplete hsst hbudget
        hupperNonnegative hmaximumAbsolute hseparation
        (delta / 4 + (1 / (Fintype.card Arm : ℝ) ^ 2 + (delta / 4) / 2)) hfirstStrong
        (by linarith) hepsilon hfinalSeparation

/--
The source Algorithm-3 branch split, with a joint finite event in each branch.
For `δ ≤ 1/n` this is the whole-set Seq-Eliminate cap; otherwise it is the
literal four-phase queried-prefix event.
-/
noncomputable def canonicalOptMaximizeTraceAlgorithm3SourceJointEnvelopeProbability
    {Arm : Type*} [Fintype Arm] [Nonempty Arm] [DecidableEq Arm]
    (cutoff : ℕ) (lower upper epsilon delta : ℝ) (maxBatch : ℕ)
    (preferenceGap : Arm → Arm → ℝ) (maximum : Arm)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (hcutoff : 0 < cutoff) (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1)
    (hbudget : ∀ round < sourcePruneRoundCount (Fintype.card Arm),
      fixedSampleBudget lower upper (adaptivePruneRoundDelta (delta / 4) round) ≤ maxBatch) : ℝ := by
  classical
  if delta ≤ 1 / (Fintype.card Arm : ℝ) then
    exact canonicalOptMaximizeBaseSourceJointResourceProbability preferenceGap hprobability epsilon delta
  else
    exact canonicalOptMaximizeTraceFallbackFinalTraceAlgorithm3SourceJointEnvelopeProbability cutoff
      lower upper epsilon delta maxBatch preferenceGap maximum hprobability hcutoff hdelta hdeltaLeOne
      hbudget

/--
The complete Algorithm-3 source branch split has a simultaneous output and
finite resource event of probability at least `1 - δ`.  The two branches keep
their distinct literal finite caps until the later asymptotic packaging step.
-/
theorem canonicalOptMaximizeTraceAlgorithm3SourceJointEnvelopeProbability_ge
    {Arm : Type*} [Fintype Arm] [Nonempty Arm] [DecidableEq Arm]
    (cutoff : ℕ) (lower upper epsilon delta : ℝ) (maxBatch : ℕ)
    (preferenceGap : Arm → Arm → ℝ) (maximum : Arm)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (ranking : Fin (Fintype.card Arm) → Arm)
    (hranking : PreferenceRanking preferenceGap ranking)
    (hcutoff : 0 < cutoff) (hcutoffLeCard : cutoff ≤ Fintype.card Arm)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) (hlower : 0 < lower)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hself : ∀ arm, preferenceGap arm arm = 0)
    (hcomplete : PreferenceComplete preferenceGap)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hbudget : ∀ round < sourcePruneRoundCount (Fintype.card Arm),
      fixedSampleBudget lower upper (adaptivePruneRoundDelta (delta / 4) round) ≤ maxBatch)
    (hupperNonnegative : 0 ≤ upper)
    (hmaximumAbsolute : AbsoluteMaximum preferenceGap maximum)
    (hseparation : lower < upper)
    (hpruneCutoff : Real.sqrt (6 * (Fintype.card Arm : ℝ) *
      Real.log (Fintype.card Arm : ℝ)) < (cutoff : ℝ))
    (hpruneDeltaLower : (cutoff : ℝ) / (Fintype.card Arm : ℝ) ≤ delta / 4)
    (hepsilon : 0 < epsilon) (hfinalSeparation : upper < epsilon) :
    1 - delta ≤
      canonicalOptMaximizeTraceAlgorithm3SourceJointEnvelopeProbability cutoff lower upper epsilon
        delta maxBatch preferenceGap maximum hprobability hcutoff hdelta hdeltaLeOne hbudget := by
  unfold canonicalOptMaximizeTraceAlgorithm3SourceJointEnvelopeProbability
  split
  · exact canonicalOptMaximizeBaseSource_joint_resource_probability preferenceGap hprobability
      epsilon delta hantisymmetric hself hsst hepsilon hdelta hdeltaLeOne maximum hmaximumAbsolute
  · exact canonicalOptMaximizeTraceFallbackFinalTraceAlgorithm3SourceJointEnvelopeProbability_ge
      cutoff lower upper epsilon delta maxBatch preferenceGap maximum hprobability ranking hranking hcutoff
      hcutoffLeCard hdelta hdeltaLeOne hlower hantisymmetric hself hcomplete hsst hbudget
      hupperNonnegative hmaximumAbsolute hseparation hpruneCutoff hpruneDeltaLower hepsilon
      hfinalSeparation

/-- The literal Algorithm-3 branch split at the rounded source cutoff.  Unlike
the compatibility theorem above for an arbitrary supplied cutoff, this source
specialization needs no additional cutoff-to-confidence premise. -/
theorem canonicalOptMaximizeTraceAlgorithm3SourceJointEnvelopeProbability_ge_sourceCutoff
    {Arm : Type*} [Fintype Arm] [Nonempty Arm] [DecidableEq Arm]
    (lower upper epsilon delta : ℝ) (maxBatch : ℕ)
    (preferenceGap : Arm → Arm → ℝ) (maximum : Arm)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (ranking : Fin (Fintype.card Arm) → Arm)
    (hranking : PreferenceRanking preferenceGap ranking)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) (hlower : 0 < lower)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hself : ∀ arm, preferenceGap arm arm = 0)
    (hcomplete : PreferenceComplete preferenceGap)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hbudget : ∀ round < sourcePruneRoundCount (Fintype.card Arm),
      fixedSampleBudget lower upper (adaptivePruneRoundDelta (delta / 4) round) ≤ maxBatch)
    (hupperNonnegative : 0 ≤ upper)
    (hmaximumAbsolute : AbsoluteMaximum preferenceGap maximum)
    (hseparation : lower < upper)
    (hepsilon : 0 < epsilon) (hfinalSeparation : upper < epsilon) :
    1 - delta ≤
      canonicalOptMaximizeTraceAlgorithm3SourceJointEnvelopeProbability
        (sourceOptMaximizeCutoff (Fintype.card Arm)) lower upper epsilon delta maxBatch
        preferenceGap maximum hprobability
        (sourceOptMaximizeCutoff_pos (Fintype.card Arm) Fintype.card_pos)
        hdelta hdeltaLeOne hbudget := by
  unfold canonicalOptMaximizeTraceAlgorithm3SourceJointEnvelopeProbability
  split
  · exact canonicalOptMaximizeBaseSource_joint_resource_probability preferenceGap hprobability
      epsilon delta hantisymmetric hself hsst hepsilon hdelta hdeltaLeOne maximum hmaximumAbsolute
  · rename_i hnonbase
    exact
      canonicalOptMaximizeTraceFallbackFinalTraceAlgorithm3SourceJointEnvelopeProbability_ge_nonbase
        lower upper epsilon delta maxBatch preferenceGap maximum hprobability ranking hranking hdelta
        hdeltaLeOne hlower hantisymmetric hself hcomplete hsst hbudget hupperNonnegative
        hmaximumAbsolute hseparation hepsilon hfinalSeparation (lt_of_not_ge hnonbase)

end FalahatgarEtAl2017MaxingRanking
