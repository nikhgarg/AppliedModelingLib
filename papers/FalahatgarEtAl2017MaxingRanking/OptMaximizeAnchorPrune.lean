import FalahatgarEtAl2017MaxingRanking.PickAnchorRankedTop
import FalahatgarEtAl2017MaxingRanking.FreshStoppedPruneRetention

/-!
# First two OPT-Maximize phases on one finite PMF

Algorithm 3 first obtains an anchor, then samples fresh Prune outcomes
conditional on that realized anchor.  This module records the resulting
dependent two-phase PMF and its finite failure composition; no independence
between Pick-Anchor and Prune is assumed or needed.
-/

namespace FalahatgarEtAl2017MaxingRanking

open AppliedModelingLib PreferenceRL
open MeasureTheory ProbabilityTheory

/-- Draw an anchor, then a fresh candidate set conditional on that anchor. -/
noncomputable def optMaximizeAnchorPruneLaw {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (anchorLaw : PMF Arm) (pruneLaw : Arm → PMF (Finset Arm)) :
    PMF (Arm × Finset Arm) :=
  anchorLaw.bind fun anchor => (pruneLaw anchor).map fun candidates => (anchor, candidates)

/-- The canonical finite-PMF output of Algorithm 5, before Algorithm 2 runs. -/
noncomputable def canonicalFreshPickAnchorSourceOutputLaw
    {Arm : Type*} [Fintype Arm] [Nonempty Arm]
    (cutoff : ℕ) (delta epsilon : ℝ) (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (hcutoff : 0 < cutoff) (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    PMF Arm := by
  classical
  let count := pickAnchorSampleCount (Fintype.card Arm) cutoff delta
  let hcount : 0 < count := pickAnchorSourceSampleCount_pos cutoff delta hcutoff hdelta hdeltaLeOne
  exact (freshPickAnchorJointLaw
    (pickAnchorUniformSampleLaw count
      (pickAnchorSampleCount_le_armCount (Fintype.card Arm) cutoff delta))
    (fun sample => canonicalFreshPickAnchorOutcomeLaw sample hcount preferenceGap hprobability
      epsilon ((delta / 2) / (count : ℝ)))
    (fun sample => canonicalFreshPickAnchorObservation sample epsilon ((delta / 2) / (count : ℝ)))
    preferenceGap epsilon ((delta / 2) / (count : ℝ)) hcount).map
      (fun sampleStateFailure => sampleStateFailure.2.1)

/-- The GoodAnchor probability of the canonical Pick-Anchor output PMF. -/
noncomputable def canonicalFreshPickAnchorSourceGoodAnchorProbability
    {Arm : Type*} [Fintype Arm] [Nonempty Arm]
    (cutoff : ℕ) (delta epsilon : ℝ) (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (hcutoff : 0 < cutoff) (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) : ℝ := by
  classical
  exact pmfProbClassical
      (canonicalFreshPickAnchorSourceOutputLaw cutoff delta epsilon preferenceGap hprobability
        hcutoff hdelta hdeltaLeOne)
      (GoodAnchor preferenceGap epsilon cutoff)

/-- The source Pick-Anchor probability is exactly the GoodAnchor probability of its output law. -/
theorem canonicalFreshPickAnchorSourceGoodAnchorProbability_eq
    {Arm : Type*} [Fintype Arm] [Nonempty Arm]
    (cutoff : ℕ) (delta epsilon : ℝ) (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (hcutoff : 0 < cutoff) (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    canonicalFreshPickAnchorSourceGoodAnchorProbability cutoff delta epsilon preferenceGap hprobability
      hcutoff hdelta hdeltaLeOne =
      freshPickAnchorUniformGoodAnchorProbability
        cutoff delta epsilon
        (fun sample => canonicalFreshPickAnchorOutcomeLaw sample
          (pickAnchorSourceSampleCount_pos cutoff delta hcutoff hdelta hdeltaLeOne)
          preferenceGap hprobability epsilon
          ((delta / 2) / (pickAnchorSampleCount (Fintype.card Arm) cutoff delta : ℝ)))
        (fun sample => canonicalFreshPickAnchorObservation sample epsilon
          ((delta / 2) / (pickAnchorSampleCount (Fintype.card Arm) cutoff delta : ℝ)))
        preferenceGap hcutoff hdelta hdeltaLeOne := by
  classical
  unfold canonicalFreshPickAnchorSourceGoodAnchorProbability
  unfold canonicalFreshPickAnchorSourceOutputLaw
  unfold freshPickAnchorUniformGoodAnchorProbability freshPickAnchorJointGoodAnchorProbability
  unfold pmfProbClassical
  rw [pmfProb_map]

/-- Lemma 3 on the actual canonical Pick-Anchor output marginal. -/
theorem canonicalFreshPickAnchorSourceOutputLaw_goodAnchor_highProbability_of_preferenceRanking
    {Arm : Type*} [Fintype Arm] [Nonempty Arm]
    (cutoff : ℕ) (delta epsilon : ℝ) (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (ranking : Fin (Fintype.card Arm) → Arm)
    (hranking : PreferenceRanking preferenceGap ranking)
    (hcutoff : 0 < cutoff) (hcutoffLeCard : cutoff ≤ Fintype.card Arm)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) (hepsilon : 0 < epsilon)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hself : ∀ arm, preferenceGap arm arm = 0)
    (hcomplete : PreferenceComplete preferenceGap)
    (hsst : StrongStochasticTransitivity preferenceGap)
    : 1 - delta ≤ canonicalFreshPickAnchorSourceGoodAnchorProbability
      cutoff delta epsilon preferenceGap hprobability hcutoff hdelta hdeltaLeOne := by
  classical
  rw [canonicalFreshPickAnchorSourceGoodAnchorProbability_eq]
  exact canonicalFreshPickAnchorUniform_goodAnchor_highProbability_of_preferenceRanking
    cutoff delta epsilon preferenceGap hprobability ranking hranking hcutoff hcutoffLeCard hdelta
    hdeltaLeOne hepsilon hantisymmetric hself hcomplete hsst

/-- The anchor-only event has the same probability after the fresh Prune phase. -/
theorem optMaximizeAnchorPruneLaw_fst_probability
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (anchorLaw : PMF Arm) (pruneLaw : Arm → PMF (Finset Arm))
    (event : Arm → Prop) [DecidablePred event] :
    pmfProb (optMaximizeAnchorPruneLaw anchorLaw pruneLaw)
      (fun anchorCandidates => event anchorCandidates.1) =
      pmfProb anchorLaw event := by
  classical
  unfold optMaximizeAnchorPruneLaw
  rw [pmfProb_bind]
  simp_rw [pmfProb_map]
  unfold pmfProb
  apply pmfExp_congr
  intro anchor
  by_cases hevent : event anchor <;> simp [hevent, pmfExp_const]

/--
A uniform Prune failure bound on good anchors remains valid after sampling
the anchor first.  On non-good anchors the tracked event is false, so no
conditional Prune premise is required there.
-/
theorem optMaximizeAnchorPruneLaw_goodAnchor_conditional_failure_le
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (anchorLaw : PMF Arm) (pruneLaw : Arm → PMF (Finset Arm))
    (goodAnchor : Arm → Prop) (failure : Arm → Finset Arm → Prop)
    (failureBudget : ℝ) (hbudgetNonnegative : 0 ≤ failureBudget)
    [DecidablePred goodAnchor] [∀ anchor, DecidablePred (failure anchor)]
    (hfailure : ∀ anchor, goodAnchor anchor →
      pmfProb (pruneLaw anchor) (failure anchor) ≤ failureBudget) :
    pmfProb (optMaximizeAnchorPruneLaw anchorLaw pruneLaw)
      (fun anchorCandidates =>
        goodAnchor anchorCandidates.1 ∧ failure anchorCandidates.1 anchorCandidates.2) ≤
      failureBudget := by
  classical
  unfold optMaximizeAnchorPruneLaw
  apply pmfProb_adaptiveStep_le_of_historywiseBound anchorLaw pruneLaw
    (fun anchor candidates => goodAnchor anchor ∧ failure anchor candidates) failureBudget
  intro anchor
  by_cases hgood : goodAnchor anchor
  · simpa [hgood] using hfailure anchor hgood
  · simpa [hgood, pmfProb] using hbudgetNonnegative

/--
The two-phase anchor/Prune success event has probability at least one minus
the Pick-Anchor failure budget plus the good-anchor conditional Prune budget.
-/
theorem optMaximizeAnchorPruneLaw_success_probability_ge_one_sub_add
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (anchorLaw : PMF Arm) (pruneLaw : Arm → PMF (Finset Arm))
    (goodAnchor : Arm → Prop) (candidateSuccess : Arm → Finset Arm → Prop)
    (anchorFailure pruneFailure : ℝ)
    [DecidablePred goodAnchor] [∀ anchor, DecidablePred (candidateSuccess anchor)]
    (hanchorFailure : pmfProb anchorLaw (fun anchor => ¬ goodAnchor anchor) ≤ anchorFailure)
    (hpruneFailure : pmfProb (optMaximizeAnchorPruneLaw anchorLaw pruneLaw)
      (fun anchorCandidates => goodAnchor anchorCandidates.1 ∧
        ¬ candidateSuccess anchorCandidates.1 anchorCandidates.2) ≤ pruneFailure) :
    1 - (anchorFailure + pruneFailure) ≤
      pmfProb (optMaximizeAnchorPruneLaw anchorLaw pruneLaw)
        (fun anchorCandidates => goodAnchor anchorCandidates.1 ∧
          candidateSuccess anchorCandidates.1 anchorCandidates.2) := by
  classical
  let law := optMaximizeAnchorPruneLaw anchorLaw pruneLaw
  let anchorBad : Arm × Finset Arm → Prop := fun anchorCandidates =>
    ¬ goodAnchor anchorCandidates.1
  let pruneBad : Arm × Finset Arm → Prop := fun anchorCandidates =>
    goodAnchor anchorCandidates.1 ∧ ¬ candidateSuccess anchorCandidates.1 anchorCandidates.2
  let success : Arm × Finset Arm → Prop := fun anchorCandidates =>
    goodAnchor anchorCandidates.1 ∧ candidateSuccess anchorCandidates.1 anchorCandidates.2
  have hanchorBad : pmfProb law anchorBad ≤ anchorFailure := by
    change pmfProb (optMaximizeAnchorPruneLaw anchorLaw pruneLaw)
      (fun anchorCandidates => ¬ goodAnchor anchorCandidates.1) ≤ anchorFailure
    calc
      pmfProb (optMaximizeAnchorPruneLaw anchorLaw pruneLaw)
          (fun anchorCandidates => ¬ goodAnchor anchorCandidates.1) =
          pmfProb anchorLaw (fun anchor => ¬ goodAnchor anchor) :=
        optMaximizeAnchorPruneLaw_fst_probability anchorLaw pruneLaw
          (fun anchor => ¬ goodAnchor anchor)
      _ ≤ anchorFailure := hanchorFailure
  have hpruneBad : pmfProb law pruneBad ≤ pruneFailure := by
    simpa [law, pruneBad] using hpruneFailure
  have hfailureUnion : pmfProb law (fun anchorCandidates =>
      anchorBad anchorCandidates ∨ pruneBad anchorCandidates) ≤ anchorFailure + pruneFailure :=
    (pmfProb_or_le law anchorBad pruneBad).trans (add_le_add hanchorBad hpruneBad)
  have hfailureEq : pmfProb law (fun anchorCandidates => ¬ success anchorCandidates) =
      pmfProb law (fun anchorCandidates => anchorBad anchorCandidates ∨ pruneBad anchorCandidates) := by
    apply pmfProb_congr
    intro anchorCandidates
    by_cases hgood : goodAnchor anchorCandidates.1 <;>
      by_cases hcandidate : candidateSuccess anchorCandidates.1 anchorCandidates.2 <;>
      simp [success, anchorBad, pruneBad, hgood, hcandidate]
  have hfailure : pmfProb law (fun anchorCandidates => ¬ success anchorCandidates) ≤
      anchorFailure + pruneFailure := hfailureEq.trans_le hfailureUnion
  change 1 - (anchorFailure + pruneFailure) ≤ pmfProb law success
  calc
    1 - (anchorFailure + pruneFailure) ≤
        1 - pmfProb law (fun anchorCandidates => ¬ success anchorCandidates) := by
          linarith
    _ = pmfProb law success := by
          rw [pmfProb_compl]
          ring

/--
Lemma 17 on the actual stopped-Prune active-set law.  A good anchor either is
already an `upper`-maximum, or the absolute maximum is retained; in both cases
the candidate set has the source cardinality endpoint with probability at
least `1 - delta`.
-/
theorem canonicalFreshStoppedPruneActive_lemma17_candidate_success_probability
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (anchor maximum : Arm) (lower upper delta : ℝ) (maxBatch cutoff : ℕ)
    (hbudget : ∀ round < Fintype.card Arm,
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
    (hcard : 2 ≤ Fintype.card Arm)
    (hcutoff : Real.sqrt (6 * (Fintype.card Arm : ℝ) *
      Real.log (Fintype.card Arm : ℝ)) < (cutoff : ℝ))
    (hdeltaLower : (cutoff : ℝ) / (Fintype.card Arm : ℝ) ≤ delta)
    [Decidable (EpsilonMaximum preferenceGap upper anchor)] :
    1 - delta ≤
      pmfProb
        (freshStoppedPruneActiveLaw initial
          (canonicalFreshPruneOutcomeLaw preferenceGap hprobability (Fintype.card Arm) anchor
            lower upper delta maxBatch hbudget)
          cutoff
          (canonicalFreshPruneDecision (Fintype.card Arm) lower upper delta maxBatch hbudget)
          (Fintype.card Arm))
        (fun active => active.card ≤ 2 * cutoff ∧
          (EpsilonMaximum preferenceGap upper anchor ∨ maximum ∈ active)) := by
  by_cases hanchorMaximum : EpsilonMaximum preferenceGap upper anchor
  · have hsize := canonicalFreshStoppedPruneActive_card_success_probability_of_sourceLemma15
      preferenceGap hprobability anchor lower upper delta maxBatch cutoff hbudget initial hanchor
      hseparation hdelta hdeltaHalf hcard hcutoff hdeltaLower
    calc
      1 - delta ≤ 1 - delta / 2 := by linarith
      _ ≤ pmfProb
          (freshStoppedPruneActiveLaw initial
            (canonicalFreshPruneOutcomeLaw preferenceGap hprobability (Fintype.card Arm) anchor
              lower upper delta maxBatch hbudget)
            cutoff
            (canonicalFreshPruneDecision (Fintype.card Arm) lower upper delta maxBatch hbudget)
            (Fintype.card Arm))
          (fun active => active.card ≤ 2 * cutoff) := hsize
      _ ≤ pmfProb
          (freshStoppedPruneActiveLaw initial
            (canonicalFreshPruneOutcomeLaw preferenceGap hprobability (Fintype.card Arm) anchor
              lower upper delta maxBatch hbudget)
            cutoff
            (canonicalFreshPruneDecision (Fintype.card Arm) lower upper delta maxBatch hbudget)
            (Fintype.card Arm))
          (fun active => active.card ≤ 2 * cutoff ∧
            (EpsilonMaximum preferenceGap upper anchor ∨ maximum ∈ active)) := by
              apply pmfProb_le_of_imp
              intro active hsize
              exact ⟨hsize, Or.inl hanchorMaximum⟩
  · have hretain := canonicalFreshStoppedPruneActive_card_and_max_success_probability_of_not_epsilonMaximum
      preferenceGap hprobability anchor maximum lower upper delta maxBatch cutoff hbudget initial
      hantisymmetric hsst hupperNonnegative hmaximumAbsolute hanchorMaximum hanchor hmaximum
      hseparation hdelta hdeltaHalf hcard hcutoff hdeltaLower
    calc
      1 - delta ≤ pmfProb
          (freshStoppedPruneActiveLaw initial
            (canonicalFreshPruneOutcomeLaw preferenceGap hprobability (Fintype.card Arm) anchor
              lower upper delta maxBatch hbudget)
            cutoff
            (canonicalFreshPruneDecision (Fintype.card Arm) lower upper delta maxBatch hbudget)
            (Fintype.card Arm))
          (fun active => active.card ≤ 2 * cutoff ∧ maximum ∈ active) := hretain
      _ ≤ pmfProb
          (freshStoppedPruneActiveLaw initial
            (canonicalFreshPruneOutcomeLaw preferenceGap hprobability (Fintype.card Arm) anchor
              lower upper delta maxBatch hbudget)
            cutoff
            (canonicalFreshPruneDecision (Fintype.card Arm) lower upper delta maxBatch hbudget)
            (Fintype.card Arm))
          (fun active => active.card ≤ 2 * cutoff ∧
            (EpsilonMaximum preferenceGap upper anchor ∨ maximum ∈ active)) := by
              apply pmfProb_le_of_imp
              intro active hsuccess
              exact ⟨hsuccess.1, Or.inr hsuccess.2⟩

/-- The dependent source PMF for OPT-Maximize's Pick-Anchor and Prune phases. -/
noncomputable def canonicalOptMaximizeAnchorPruneSourceLaw
    {Arm : Type*} [Fintype Arm] [Nonempty Arm]
    (cutoff : ℕ) (anchorDelta pruneDelta lower upper : ℝ) (maxBatch : ℕ)
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (hcutoff : 0 < cutoff) (hanchorDelta : 0 < anchorDelta)
    (hanchorDeltaLeOne : anchorDelta ≤ 1)
    (hbudget : ∀ round < Fintype.card Arm,
      fixedSampleBudget lower upper (adaptivePruneRoundDelta pruneDelta round) ≤ maxBatch) :
    PMF (Arm × Finset Arm) := by
  classical
  exact optMaximizeAnchorPruneLaw
    (canonicalFreshPickAnchorSourceOutputLaw cutoff anchorDelta lower preferenceGap hprobability
      hcutoff hanchorDelta hanchorDeltaLeOne)
    (fun anchor => freshStoppedPruneActiveLaw Finset.univ
      (canonicalFreshPruneOutcomeLaw preferenceGap hprobability (Fintype.card Arm) anchor
        lower upper pruneDelta maxBatch hbudget)
      cutoff
      (canonicalFreshPruneDecision (Fintype.card Arm) lower upper pruneDelta maxBatch hbudget)
      (Fintype.card Arm))

/-- The first two source phases succeed when the anchor is good and Prune has Lemma 17's endpoint. -/
noncomputable def canonicalOptMaximizeAnchorPruneSourceSuccessProbability
    {Arm : Type*} [Fintype Arm] [Nonempty Arm]
    (cutoff : ℕ) (anchorDelta pruneDelta lower upper : ℝ) (maxBatch : ℕ)
    (preferenceGap : Arm → Arm → ℝ) (maximum : Arm)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (hcutoff : 0 < cutoff) (hanchorDelta : 0 < anchorDelta)
    (hanchorDeltaLeOne : anchorDelta ≤ 1)
    (hbudget : ∀ round < Fintype.card Arm,
      fixedSampleBudget lower upper (adaptivePruneRoundDelta pruneDelta round) ≤ maxBatch) : ℝ := by
  classical
  exact pmfProb
    (canonicalOptMaximizeAnchorPruneSourceLaw cutoff anchorDelta pruneDelta lower upper maxBatch
      preferenceGap hprobability hcutoff hanchorDelta hanchorDeltaLeOne hbudget)
    (fun anchorCandidates =>
      GoodAnchor preferenceGap lower cutoff anchorCandidates.1 ∧
        anchorCandidates.2.card ≤ 2 * cutoff ∧
          (EpsilonMaximum preferenceGap upper anchorCandidates.1 ∨ maximum ∈ anchorCandidates.2))

/--
The first two phases of Algorithm 3 have the source failure composition:
Pick-Anchor costs `anchorDelta`, and conditional stopped Prune costs
`pruneDelta`.  The law is a dependent PMF, so this does not assume the two
algorithmic phases are independent.
-/
theorem canonicalOptMaximizeAnchorPruneSource_success_probability
    {Arm : Type*} [Fintype Arm] [Nonempty Arm]
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
    (hbudget : ∀ round < Fintype.card Arm,
      fixedSampleBudget lower upper (adaptivePruneRoundDelta pruneDelta round) ≤ maxBatch)
    (hupperNonnegative : 0 ≤ upper)
    (hmaximumAbsolute : AbsoluteMaximum preferenceGap maximum)
    (hseparation : lower < upper) (hpruneDelta : 0 < pruneDelta)
    (hpruneDeltaHalf : pruneDelta ≤ 1 / 2)
    (hcard : 2 ≤ Fintype.card Arm)
    (hpruneCutoff : Real.sqrt (6 * (Fintype.card Arm : ℝ) *
      Real.log (Fintype.card Arm : ℝ)) < (cutoff : ℝ))
    (hpruneDeltaLower : (cutoff : ℝ) / (Fintype.card Arm : ℝ) ≤ pruneDelta) :
    1 - (anchorDelta + pruneDelta) ≤
      canonicalOptMaximizeAnchorPruneSourceSuccessProbability
        cutoff anchorDelta pruneDelta lower upper maxBatch preferenceGap maximum hprobability
        hcutoff hanchorDelta hanchorDeltaLeOne hbudget := by
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
  let candidateSuccess : Arm → Finset Arm → Prop := fun anchor active =>
    active.card ≤ 2 * cutoff ∧
      (EpsilonMaximum preferenceGap upper anchor ∨ maximum ∈ active)
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
  have hpruneFailure : pmfProb (optMaximizeAnchorPruneLaw anchorLaw pruneLaw)
      (fun anchorCandidates => GoodAnchor preferenceGap lower cutoff anchorCandidates.1 ∧
        ¬ candidateSuccess anchorCandidates.1 anchorCandidates.2) ≤ pruneDelta := by
    apply optMaximizeAnchorPruneLaw_goodAnchor_conditional_failure_le
      anchorLaw pruneLaw (GoodAnchor preferenceGap lower cutoff)
      (fun anchor active => ¬ candidateSuccess anchor active) pruneDelta (le_of_lt hpruneDelta)
    intro anchor hgood
    have hcandidate := canonicalFreshStoppedPruneActive_lemma17_candidate_success_probability
      preferenceGap hprobability anchor maximum lower upper pruneDelta maxBatch cutoff hbudget
      Finset.univ hantisymmetric hsst hupperNonnegative hmaximumAbsolute hgood
      (Finset.mem_univ maximum) hseparation hpruneDelta hpruneDeltaHalf hcard hpruneCutoff
      hpruneDeltaLower
    change pmfProb (pruneLaw anchor) (fun active => ¬ candidateSuccess anchor active) ≤ pruneDelta
    rw [pmfProb_compl]
    have hcandidate' : 1 - pruneDelta ≤
        pmfProb (pruneLaw anchor) (candidateSuccess anchor) := by
      simpa only [pruneLaw, candidateSuccess] using hcandidate
    linarith
  change 1 - (anchorDelta + pruneDelta) ≤
    pmfProb (optMaximizeAnchorPruneLaw anchorLaw pruneLaw)
      (fun anchorCandidates => GoodAnchor preferenceGap lower cutoff anchorCandidates.1 ∧
        candidateSuccess anchorCandidates.1 anchorCandidates.2)
  exact optMaximizeAnchorPruneLaw_success_probability_ge_one_sub_add
    anchorLaw pruneLaw (GoodAnchor preferenceGap lower cutoff) candidateSuccess
    anchorDelta pruneDelta hanchorFailure hpruneFailure

end FalahatgarEtAl2017MaxingRanking
