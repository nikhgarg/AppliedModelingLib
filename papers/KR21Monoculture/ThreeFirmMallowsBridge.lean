import KR21Monoculture.QuantitativeWitnesses
import AppliedModelingLib.SocialChoice.Ranking.Mallows

open AppliedModelingLib

namespace KR21Monoculture

/-!
# Four-candidate executable-ranking bridge

`Ranking n` in the reusable library ranks `Candidate n = Fin (n + 2)`.
Consequently, the source's four-candidate executable domain is bridged to
`Ranking 2`, rather than to literal `Ranking 4` (which would have six
candidates).  This module establishes only the finite ranking and unnormalised
weight correspondence; normalization and the full source experiment are
separate obligations.
-/

open AppliedModelingLib.SocialChoice.Ranking

/-- Every named source ranking acts bijectively on the four candidate slots. -/
theorem sourceFourRankingAt_bijective (pi : SourceFourRanking) :
    Function.Bijective (sourceFourRankingAt pi) := by
  cases pi <;> decide

/-- Convert a source's named four-candidate ranking into the library's
four-candidate (`Ranking 2`) permutation representation. -/
noncomputable def sourceFourRankingToRanking (pi : SourceFourRanking) : Ranking 2 :=
  Equiv.ofBijective (sourceFourRankingAt pi) (sourceFourRankingAt_bijective pi)

/-- The converted permutation has exactly the source table's slot action. -/
theorem sourceFourRankingToRanking_apply (pi : SourceFourRanking)
    (slot : Candidate 2) :
    sourceFourRankingToRanking pi slot = sourceFourRankingAt pi slot := by
  rfl

/-- The source inversion table agrees with the library's Kendall distance from
the identity center. -/
theorem sourceExecutableInversionCount_eq_kendallTau (pi : SourceFourRanking) :
    sourceExecutableInversionCount pi =
      kendallTau (Equiv.refl (Candidate 2)) (sourceFourRankingToRanking pi) := by
  rw [sourceExecutableInversionCount_eq_byPairs]
  unfold sourceExecutableInversionCountByPairs kendallTau
  classical
  apply Finset.card_bij
    (fun ij _ =>
      (sourceFourRankingToRanking pi ij.2, sourceFourRankingToRanking pi ij.1))
  · intro ij hij
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hij
    simp only [inversionFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · simpa only [rankOf, Equiv.refl_apply,
        sourceFourRankingToRanking_apply] using hij.2
    · simpa only [rankOf, Equiv.symm_apply_apply] using hij.1
  · intro ij₁ hij₁ ij₂ hij₂ h
    apply Prod.ext
    · exact (sourceFourRankingToRanking pi).injective (Prod.ext_iff.mp h).2
    · exact (sourceFourRankingToRanking pi).injective (Prod.ext_iff.mp h).1
  · intro ab hab
    have hab' :
        invertedPair (Equiv.refl (Candidate 2)) (sourceFourRankingToRanking pi) ab := by
      simpa only [inversionFinset, Finset.mem_filter, Finset.mem_univ, true_and] using hab
    have hab_first : ab.1 < ab.2 := by
      simpa only [rankOf, Equiv.refl_apply] using hab'.1
    have hab_second :
        (sourceFourRankingToRanking pi).symm ab.2 <
          (sourceFourRankingToRanking pi).symm ab.1 := by
      simpa only [rankOf] using hab'.2
    refine ⟨((sourceFourRankingToRanking pi).symm ab.2,
      (sourceFourRankingToRanking pi).symm ab.1), ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact hab_second
      · simpa only [← sourceFourRankingToRanking_apply,
          Equiv.apply_symm_apply] using hab_first
    · simp only [Equiv.apply_symm_apply]

/-- After casting the source inverse Mallows parameter to reals, its
unnormalised rational weight is the library's identity-centered Mallows
weight. -/
theorem sourceExecutableMallowsWeight_cast (q : ℚ) (pi : SourceFourRanking) :
    ((q ^ sourceExecutableInversionCount pi : ℚ) : ℝ) =
      mallowsWeight (q : ℝ) (Equiv.refl (Candidate 2))
        (sourceFourRankingToRanking pi) := by
  rw [sourceExecutableInversionCount_eq_kendallTau]
  simp only [Rat.cast_pow, mallowsWeight]

/-- The source's algorithm parameter `q = 1/2` has the corresponding real
library Mallows weight. -/
theorem sourceAlgorithmMallowsWeight_cast (pi : SourceFourRanking) :
    ((sourceAlgorithmQ ^ sourceExecutableInversionCount pi : ℚ) : ℝ) =
      mallowsWeight ((1 : ℝ) / 2) (Equiv.refl (Candidate 2))
        (sourceFourRankingToRanking pi) := by
  simpa only [sourceAlgorithmQ, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    using sourceExecutableMallowsWeight_cast sourceAlgorithmQ pi

/-- The source's human parameter `q = 4/7` has the corresponding real library
Mallows weight. -/
theorem sourceHumanMallowsWeight_cast (pi : SourceFourRanking) :
    ((sourceHumanQ ^ sourceExecutableInversionCount pi : ℚ) : ℝ) =
      mallowsWeight ((4 : ℝ) / 7) (Equiv.refl (Candidate 2))
        (sourceFourRankingToRanking pi) := by
  simpa only [sourceHumanQ, Rat.cast_div, Rat.cast_ofNat]
    using sourceExecutableMallowsWeight_cast sourceHumanQ pi

end KR21Monoculture
