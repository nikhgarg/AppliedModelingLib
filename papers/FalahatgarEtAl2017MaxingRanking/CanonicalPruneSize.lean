import FalahatgarEtAl2017MaxingRanking.CanonicalPruneBatches
import FalahatgarEtAl2017MaxingRanking.PruneSize

/-!
# Canonical Prune-round size guarantee

The source's Prune size argument counts threshold-nonbetter arms that receive
an erroneous upper decision.  This file binds that count to the actual finite
Bernoulli product model, leaving only the printed Lemma 14 numeric tail
condition as an explicit arithmetic premise.
-/

namespace FalahatgarEtAl2017MaxingRanking

open AppliedModelingLib PreferenceRL
open MeasureTheory ProbabilityTheory

/--
One canonical Prune round reduces a good-anchor active set to at most twice
the source cutoff, except with the supplied finite Hoeffding tail probability.
The margin and tail assumptions are precisely the numerical endpoint of the
source's Lemma 14 calculation; the stochastic comparison and survivor-count
bridges are proved here from the finite product law.
-/
theorem canonicalPruneRound_card_failure_probability_of_goodAnchor
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (active : Finset Arm) (anchor : Arm) (lower upper eta : ℝ)
    (cutoff : ℕ) (failure : ℝ)
    (hanchor : GoodAnchor preferenceGap lower cutoff anchor)
    (hseparation : lower < upper) (heta : 0 < eta) (hetaLeOne : eta ≤ 1)
    (hmargin : 0 ≤ (cutoff : ℝ) -
      ((active.filter fun arm => preferenceGap arm anchor ≤ lower).card : ℝ) * eta)
    (htail : Real.exp (-((cutoff : ℝ) -
      ((active.filter fun arm => preferenceGap arm anchor ≤ lower).card : ℝ) * eta) ^ 2 /
      (2 * ((active.filter fun arm => preferenceGap arm anchor ≤ lower).card : ℝ) *
        (1 / 4 : ℝ))) ≤ failure) :
    (canonicalPruneRoundBatchLaw preferenceGap hprobability active anchor
      (fixedSampleBudget lower upper eta)).toMeasure.real {batchTable |
        ¬ (pruneRound active
          (canonicalPruneRoundDecision active lower upper eta batchTable)).card ≤ 2 * cutoff} ≤
      failure := by
  classical
  let badActive : Finset Arm := active.filter fun arm => preferenceGap arm anchor ≤ lower
  let embed : badActive → active := fun arm =>
    ⟨arm.val, (Finset.mem_filter.mp arm.property).1⟩
  let law := (canonicalPruneRoundBatchLaw preferenceGap hprobability active anchor
    (fixedSampleBudget lower upper eta)).toMeasure
  letI : IsProbabilityMeasure law := by
    dsimp [law]
    infer_instance
  let survival : badActive →
      (active → Fin (fixedSampleBudget lower upper eta) → Bool) → ℝ := fun arm batchTable =>
    if canonicalPruneRoundDecision active lower upper eta batchTable arm.val = .upper then 1 else 0
  have hembed : Function.Injective embed := by
    intro first second hequal
    apply Subtype.ext
    exact congrArg (fun arm : active => arm.val) hequal
  have hsurvivalFunction : survival = fun arm =>
      canonicalPruneRoundUpperSurvival active lower upper eta (embed arm) := by
    funext arm batchTable
    simp [survival, embed, canonicalPruneRoundDecision,
      canonicalPruneRoundUpperSurvival, (Finset.mem_filter.mp arm.property).1]
  have hindependent : iIndepFun survival law := by
    rw [hsurvivalFunction]
    simpa [law] using
      (iIndepFun_canonicalPruneRoundUpperSurvival preferenceGap hprobability active anchor
        lower upper eta).precomp hembed
  have hmeasurable : ∀ arm, Measurable (survival arm) := by
    rw [hsurvivalFunction]
    intro arm
    exact measurable_canonicalPruneRoundUpperSurvival active lower upper eta (embed arm)
  have hbounded : ∀ arm, ∀ᵐ batchTable ∂law,
      survival arm batchTable ∈ Set.Icc (0 : ℝ) 1 := by
    rw [hsurvivalFunction]
    intro arm
    exact Filter.Eventually.of_forall fun batchTable =>
      canonicalPruneRoundUpperSurvival_mem_Icc active lower upper eta (embed arm) batchTable
  have hmeanBound : ∀ arm, law[survival arm] ≤ eta := by
    rw [hsurvivalFunction]
    intro arm
    apply integral_canonicalPruneRoundUpperSurvival_le preferenceGap hprobability active anchor
      lower upper eta (embed arm)
    · exact (Finset.mem_filter.mp arm.property).2
    · exact hseparation
    · exact heta
    · exact hetaLeOne
  have hcard : ∀ batchTable,
      (((pruneRound active
        (canonicalPruneRoundDecision active lower upper eta batchTable)).filter
        fun arm => preferenceGap arm anchor ≤ lower).card : ℝ) =
        ∑ arm, survival arm batchTable := by
    intro batchTable
    change
      (((pruneRound active
        (canonicalPruneRoundDecision active lower upper eta batchTable)).filter
        fun arm => preferenceGap arm anchor ≤ lower).card : ℝ) =
        ∑ arm : badActive,
          if canonicalPruneRoundDecision active lower upper eta batchTable arm.val = .upper then 1 else 0
    rw [← Finset.sum_subtype badActive (by simp)
      (fun arm => if canonicalPruneRoundDecision active lower upper eta batchTable arm = .upper then 1 else 0)]
    rw [Finset.sum_boole]
    congr 1
    simp [badActive, pruneRound, Finset.filter_filter, and_comm]
  have hsurvivalFailure : law.real {batchTable | (cutoff : ℝ) <
      ∑ arm, survival arm batchTable} ≤ failure := by
    apply boundedIndependentSurvivalSum_exceeds_probability_finset law survival eta cutoff failure
      hindependent hmeasurable hbounded hmeanBound
    · rw [Fintype.card_coe]
      simpa [badActive] using hmargin
    · rw [Fintype.card_coe]
      simpa [badActive] using htail
  change law.real {batchTable |
    ¬ (pruneRound active
      (canonicalPruneRoundDecision active lower upper eta batchTable)).card ≤ 2 * cutoff} ≤ failure
  calc
    law.real {batchTable |
        ¬ (pruneRound active
          (canonicalPruneRoundDecision active lower upper eta batchTable)).card ≤ 2 * cutoff} ≤
        law.real {batchTable | (cutoff : ℝ) < ∑ arm, survival arm batchTable} := by
      refine measureReal_mono ?_ (measure_ne_top law _)
      intro batchTable hfailure
      have hbadNotLe : ¬
          ((pruneRound active
            (canonicalPruneRoundDecision active lower upper eta batchTable)).filter
            fun arm => preferenceGap arm anchor ≤ lower).card ≤ cutoff := by
        intro hbad
        exact hfailure
          (pruneRound_card_le_two_mul_of_goodAnchor_and_badSurvivors
            preferenceGap lower cutoff anchor active
            (canonicalPruneRoundDecision active lower upper eta batchTable) hanchor hbad)
      have hbadLt : cutoff <
          ((pruneRound active
            (canonicalPruneRoundDecision active lower upper eta batchTable)).filter
            fun arm => preferenceGap arm anchor ≤ lower).card :=
        Nat.lt_of_not_ge hbadNotLe
      have hbadLtReal : (cutoff : ℝ) <
          (((pruneRound active
            (canonicalPruneRoundDecision active lower upper eta batchTable)).filter
            fun arm => preferenceGap arm anchor ≤ lower).card : ℝ) := by
        exact_mod_cast hbadLt
      rw [hcard batchTable] at hbadLtReal
      exact hbadLtReal
    _ ≤ failure := hsurvivalFailure

end FalahatgarEtAl2017MaxingRanking
