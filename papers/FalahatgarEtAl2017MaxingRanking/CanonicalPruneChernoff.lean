import FalahatgarEtAl2017MaxingRanking.CanonicalPruneBatches
import FalahatgarEtAl2017MaxingRanking.PruneSize
import FalahatgarEtAl2017MaxingRanking.PruneMultiplicative

/-!
# Canonical Prune Chernoff endpoint

This specializes the finite-indicator Chernoff bound to the actual Prune
filter under the heterogeneous Bernoulli product law for one active round.
-/

namespace FalahatgarEtAl2017MaxingRanking

open AppliedModelingLib PreferenceRL
open MeasureTheory ProbabilityTheory

/--
The source's multiplicative Prune-size endpoint for one canonical round.  The
right side is the direct finite exponential-moment bound; Lemma 14's displayed
numeric assumptions are handled separately as arithmetic.
-/
theorem canonicalPruneRound_card_failure_probability_of_goodAnchor_exponential
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (active : Finset Arm) (anchor : Arm) (lower upper eta : ℝ)
    (cutoff : ℕ) (t : ℝ)
    (hanchor : GoodAnchor preferenceGap lower cutoff anchor)
    (hseparation : lower < upper) (heta : 0 < eta) (hetaLeOne : eta ≤ 1) (ht : 0 ≤ t) :
    (canonicalPruneRoundBatchLaw preferenceGap hprobability active anchor
      (fixedSampleBudget lower upper eta)).toMeasure.real {batchTable |
        ¬ (pruneRound active
          (canonicalPruneRoundDecision active lower upper eta batchTable)).card ≤ 2 * cutoff} ≤
      Real.exp (-t * (cutoff : ℝ) +
        ((active.filter fun arm => preferenceGap arm anchor ≤ lower).card : ℝ) *
          ((Real.exp t - 1) * eta)) := by
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
  have hmeanBound : ∀ arm, law[survival arm] ≤ eta := by
    rw [hsurvivalFunction]
    intro arm
    apply integral_canonicalPruneRoundUpperSurvival_le preferenceGap hprobability active anchor
      lower upper eta (embed arm)
    · exact (Finset.mem_filter.mp arm.property).2
    · exact hseparation
    · exact heta
    · exact hetaLeOne
  have hindicator : ∀ arm batchTable, survival arm batchTable = 0 ∨ survival arm batchTable = 1 := by
    intro arm batchTable
    unfold survival
    split <;> simp
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
  have hbadTail := independentIndicatorSum_ge_probability_exponential law survival eta cutoff t
    hindependent hmeasurable hindicator hmeanBound ht
  change law.real {batchTable |
    ¬ (pruneRound active
      (canonicalPruneRoundDecision active lower upper eta batchTable)).card ≤ 2 * cutoff} ≤
      Real.exp (-t * (cutoff : ℝ) +
        ((active.filter fun arm => preferenceGap arm anchor ≤ lower).card : ℝ) *
          ((Real.exp t - 1) * eta))
  calc
    law.real {batchTable |
        ¬ (pruneRound active
          (canonicalPruneRoundDecision active lower upper eta batchTable)).card ≤ 2 * cutoff} ≤
        law.real {batchTable | (cutoff : ℝ) ≤ ∑ arm, survival arm batchTable} := by
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
      exact hbadLtReal.le
    _ ≤ Real.exp (-t * (cutoff : ℝ) +
        ((active.filter fun arm => preferenceGap arm anchor ≤ lower).card : ℝ) *
          ((Real.exp t - 1) * eta)) := by
      rw [Fintype.card_coe] at hbadTail
      simpa [badActive] using hbadTail

/--
The finite Chernoff tail for the threshold-nonbetter survivors of one Prune
round.  Unlike the Lemma-14 endpoint, this theorem does not use a good-anchor
cardinality bound: it is the one-round contraction estimate used in Lemma 15.
-/
theorem canonicalPruneRound_badSurvivorCard_probability_exponential
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (active : Finset Arm) (anchor : Arm) (lower upper eta threshold t : ℝ)
    (hseparation : lower < upper) (heta : 0 < eta) (hetaLeOne : eta ≤ 1) (ht : 0 ≤ t) :
    (canonicalPruneRoundBatchLaw preferenceGap hprobability active anchor
      (fixedSampleBudget lower upper eta)).toMeasure.real {batchTable | threshold ≤
        (((pruneRound active
          (canonicalPruneRoundDecision active lower upper eta batchTable)).filter
          fun arm => preferenceGap arm anchor ≤ lower).card : ℝ)} ≤
      Real.exp (-t * threshold +
        ((active.filter fun arm => preferenceGap arm anchor ≤ lower).card : ℝ) *
          ((Real.exp t - 1) * eta)) := by
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
  have hmeanBound : ∀ arm, law[survival arm] ≤ eta := by
    rw [hsurvivalFunction]
    intro arm
    apply integral_canonicalPruneRoundUpperSurvival_le preferenceGap hprobability active anchor
      lower upper eta (embed arm)
    · exact (Finset.mem_filter.mp arm.property).2
    · exact hseparation
    · exact heta
    · exact hetaLeOne
  have hindicator : ∀ arm batchTable, survival arm batchTable = 0 ∨ survival arm batchTable = 1 := by
    intro arm batchTable
    unfold survival
    split <;> simp
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
  have htail := independentIndicatorSum_ge_probability_exponential law survival eta threshold t
    hindependent hmeasurable hindicator hmeanBound ht
  change law.real {batchTable | threshold ≤
    (((pruneRound active
      (canonicalPruneRoundDecision active lower upper eta batchTable)).filter
      fun arm => preferenceGap arm anchor ≤ lower).card : ℝ)} ≤
      Real.exp (-t * threshold +
        ((active.filter fun arm => preferenceGap arm anchor ≤ lower).card : ℝ) *
          ((Real.exp t - 1) * eta))
  calc
    law.real {batchTable | threshold ≤
        (((pruneRound active
          (canonicalPruneRoundDecision active lower upper eta batchTable)).filter
          fun arm => preferenceGap arm anchor ≤ lower).card : ℝ)} =
        law.real {batchTable | threshold ≤ ∑ arm, survival arm batchTable} := by
          congr 1
          ext batchTable
          simp only [Set.mem_setOf_eq]
          rw [hcard batchTable]
    _ ≤ Real.exp (-t * threshold +
        ((active.filter fun arm => preferenceGap arm anchor ≤ lower).card : ℝ) *
          ((Real.exp t - 1) * eta)) := by
      rw [Fintype.card_coe] at htail
      simpa [badActive] using htail

end FalahatgarEtAl2017MaxingRanking
