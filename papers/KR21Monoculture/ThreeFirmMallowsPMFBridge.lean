import KR21Monoculture.ThreeFirmMallowsBridge
import Mathlib.Data.Fintype.EquivFin

open scoped BigOperators
open AppliedModelingLib

namespace KR21Monoculture

/-!
# Four-candidate source Mallows PMF bridge

The source executable model names the twenty-four rankings of four candidates.
The reusable ranking library represents four candidates as `Ranking 2`, since
`Candidate n = Fin (n + 2)`.  This module proves that the named executable
ranking domain is bijective with that library domain and that its rational
Mallows atoms, including their finite partition normalization, agree after
casting with the library's real `MallowsSpec.ofQ` law.

It deliberately stops at one Mallows ranking draw.  It does not assert an
iid-product, cardinal-value, arrival-order, or full three-firm experiment
bridge.
-/

open AppliedModelingLib.SocialChoice.Ranking

/-- Distinct named source rows have distinct four-slot ranking actions. -/
theorem sourceFourRankingToRanking_injective :
    Function.Injective sourceFourRankingToRanking := by
  intro pi sigma h
  have haction : sourceFourRankingAt pi = sourceFourRankingAt sigma := by
    have hfun : (sourceFourRankingToRanking pi : Candidate 2 → Candidate 2) =
        (sourceFourRankingToRanking sigma : Candidate 2 → Candidate 2) :=
      congrArg (fun ranking : Ranking 2 => ranking.toFun) h
    funext slot
    simpa only [← sourceFourRankingToRanking_apply] using congrFun hfun slot
  cases pi <;> cases sigma <;>
    simp_all [sourceFourRankingAt, Fin.ext_iff]

/-- The named source ranking enumeration and `Ranking 2` are both 24-element
finite domains.  This cardinality calculation is used only after proving the
source conversion injective. -/
theorem sourceFourRanking_card_eq_rankingTwo_card :
    Fintype.card SourceFourRanking = Fintype.card (Ranking 2) := by
  rw [Fintype.card_perm]
  decide

/-- The source's named four-candidate ranking conversion is a bijection onto
the library's four-candidate ranking type. -/
theorem sourceFourRankingToRanking_bijective :
    Function.Bijective sourceFourRankingToRanking := by
  exact (Fintype.bijective_iff_injective_and_card _).2
    ⟨sourceFourRankingToRanking_injective,
      sourceFourRanking_card_eq_rankingTwo_card⟩

/-- Explicit finite equivalence from the source's twenty-four named rankings
to all library permutations on four candidates. -/
noncomputable def sourceFourRankingEquivRanking :
    SourceFourRanking ≃ Ranking 2 :=
  Equiv.ofBijective sourceFourRankingToRanking
    sourceFourRankingToRanking_bijective

@[simp] theorem sourceFourRankingEquivRanking_apply (pi : SourceFourRanking) :
    sourceFourRankingEquivRanking pi = sourceFourRankingToRanking pi := rfl

/-- Casting the source finite partition function to reals gives exactly the
library partition function, with the sum transported along the proved finite
ranking equivalence. -/
theorem sourceExecutableMallowsPartition_cast (q : ℚ) :
    ((sourceExecutableMallowsPartition q : ℚ) : ℝ) =
      mallowsPartition (q : ℝ) (Equiv.refl (Candidate 2)) := by
  unfold sourceExecutableMallowsPartition mallowsPartition
  calc
    ((∑ pi : SourceFourRanking,
        q ^ sourceExecutableInversionCount pi : ℚ) : ℝ) =
        ∑ pi : SourceFourRanking,
          ((q ^ sourceExecutableInversionCount pi : ℚ) : ℝ) := by
          norm_cast
    _ = ∑ pi : SourceFourRanking,
        mallowsWeight (q : ℝ) (Equiv.refl (Candidate 2))
          (sourceFourRankingToRanking pi) := by
          apply Finset.sum_congr rfl
          intro pi _
          exact sourceExecutableMallowsWeight_cast q pi
    _ = ∑ ranking : Ranking 2,
        mallowsWeight (q : ℝ) (Equiv.refl (Candidate 2)) ranking := by
          exact Equiv.sum_comp sourceFourRankingEquivRanking
            (fun ranking : Ranking 2 =>
              mallowsWeight (q : ℝ) (Equiv.refl (Candidate 2)) ranking)

/-- A positive source rational parameter yields the corresponding positive
real inverse-Mallows parameter. -/
theorem sourceQ_cast_pos {q : ℚ} (hq : 0 < q) : 0 < (q : ℝ) := by
  exact_mod_cast hq

/-- The executable finite partition is positive at every positive inverse
parameter.  This is obtained from the transported library partition, rather
than assumed as a property of the source table. -/
theorem sourceExecutableMallowsPartition_pos {q : ℚ} (hq : 0 < q) :
    0 < sourceExecutableMallowsPartition q := by
  have hreal : 0 < ((sourceExecutableMallowsPartition q : ℚ) : ℝ) := by
    rw [sourceExecutableMallowsPartition_cast]
    exact mallowsPartition_pos (sourceQ_cast_pos hq)
      (Equiv.refl (Candidate 2))
  exact_mod_cast hreal

/-- The source formula `q^d / Z` is a normalized finite law at each positive
parameter.  The equality uses the source's literal finite partition sum. -/
theorem sourceExecutableMallowsMass_sum (q : ℚ) (hq : 0 < q) :
    (∑ pi : SourceFourRanking, sourceExecutableMallowsMass q pi) = 1 := by
  unfold sourceExecutableMallowsMass
  rw [← Finset.sum_div]
  simpa [sourceExecutableMallowsPartition] using
    (div_self (ne_of_gt (sourceExecutableMallowsPartition_pos hq)))

/-- At every positive rational parameter, the source executable normalized
atom mass agrees with the actual library finite Mallows PMF at the converted
ranking. -/
theorem sourceExecutableMallowsMass_cast_eq_mallowsPMF
    (q : ℚ) (hq : 0 < q) (pi : SourceFourRanking) :
    ((sourceExecutableMallowsMass q pi : ℚ) : ℝ) =
      ((mallowsPMF (q : ℝ) (Equiv.refl (Candidate 2))
        (sourceQ_cast_pos hq)) (sourceFourRankingToRanking pi)).toReal := by
  rw [mallowsPMF_apply_toReal]
  unfold sourceExecutableMallowsMass
  rw [Rat.cast_div, sourceExecutableMallowsWeight_cast,
    sourceExecutableMallowsPartition_cast]

/-- The same atomwise bridge stated through the public concrete
`MallowsSpec.ofQ` interface. -/
theorem sourceExecutableMallowsMass_cast_eq_mallowsSpecOfQ
    (q : ℚ) (hq : 0 < q) (pi : SourceFourRanking) :
    ((sourceExecutableMallowsMass q pi : ℚ) : ℝ) =
      ((MallowsSpec.ofQ (Equiv.refl (Candidate 2)) (q : ℝ)
        (sourceQ_cast_pos hq)).law
          (sourceFourRankingToRanking pi)).toReal := by
  simpa [MallowsSpec.ofQ] using
    sourceExecutableMallowsMass_cast_eq_mallowsPMF q hq pi

/-- Nonnegativity of the real cast of every normalized source atom follows
from its identification with an actual library PMF atom. -/
theorem sourceExecutableMallowsMass_cast_nonneg
    (q : ℚ) (hq : 0 < q) (pi : SourceFourRanking) :
    0 ≤ ((sourceExecutableMallowsMass q pi : ℚ) : ℝ) := by
  rw [sourceExecutableMallowsMass_cast_eq_mallowsPMF q hq pi]
  exact ENNReal.toReal_nonneg

/-- The executable source formula, packaged as an actual finite PMF over its
named ranking rows.  Its normalization proof is derived from the literal
partition sum, not postulated. -/
noncomputable def sourceExecutableMallowsPMF (q : ℚ) (hq : 0 < q) :
    PMF SourceFourRanking :=
  PMF.ofFintype
    (fun pi => ENNReal.ofReal ((sourceExecutableMallowsMass q pi : ℚ) : ℝ))
    (by
      have hnonneg :
          ∀ pi ∈ (Finset.univ : Finset SourceFourRanking),
            0 ≤ ((sourceExecutableMallowsMass q pi : ℚ) : ℝ) := by
        intro pi _
        exact sourceExecutableMallowsMass_cast_nonneg q hq pi
      have hsum :
          (∑ pi : SourceFourRanking,
            ((sourceExecutableMallowsMass q pi : ℚ) : ℝ)) = 1 := by
        exact_mod_cast sourceExecutableMallowsMass_sum q hq
      calc
        (∑ pi : SourceFourRanking,
            ENNReal.ofReal ((sourceExecutableMallowsMass q pi : ℚ) : ℝ)) =
            ENNReal.ofReal
              (∑ pi : SourceFourRanking,
                ((sourceExecutableMallowsMass q pi : ℚ) : ℝ)) := by
              rw [ENNReal.ofReal_sum_of_nonneg hnonneg]
        _ = 1 := by rw [hsum]; norm_num)

/-- The newly packaged source PMF has exactly the same real atom masses as
the library `MallowsSpec.ofQ` PMF after the proved ranking conversion. -/
theorem sourceExecutableMallowsPMF_apply_toReal_eq_mallowsSpecOfQ
    (q : ℚ) (hq : 0 < q) (pi : SourceFourRanking) :
    ((sourceExecutableMallowsPMF q hq pi).toReal) =
      ((MallowsSpec.ofQ (Equiv.refl (Candidate 2)) (q : ℝ)
        (sourceQ_cast_pos hq)).law
          (sourceFourRankingToRanking pi)).toReal := by
  rw [sourceExecutableMallowsPMF, PMF.ofFintype_apply,
    ENNReal.toReal_ofReal
      (sourceExecutableMallowsMass_cast_nonneg q hq pi)]
  exact sourceExecutableMallowsMass_cast_eq_mallowsSpecOfQ q hq pi

/-- Exact ENNReal atom equality between the packaged source PMF and the
library PMF.  Together with `sourceFourRankingToRanking_bijective`, this is a
finite-law correspondence rather than merely a numerical table comparison. -/
theorem sourceExecutableMallowsPMF_apply_eq_mallowsSpecOfQ
    (q : ℚ) (hq : 0 < q) (pi : SourceFourRanking) :
    sourceExecutableMallowsPMF q hq pi =
      (MallowsSpec.ofQ (Equiv.refl (Candidate 2)) (q : ℝ)
        (sourceQ_cast_pos hq)).law (sourceFourRankingToRanking pi) := by
  apply (ENNReal.toReal_eq_toReal_iff'
    ((sourceExecutableMallowsPMF q hq).apply_ne_top pi)
    ((MallowsSpec.ofQ (Equiv.refl (Candidate 2)) (q : ℝ)
      (sourceQ_cast_pos hq)).law.apply_ne_top
        (sourceFourRankingToRanking pi))).mp
  exact sourceExecutableMallowsPMF_apply_toReal_eq_mallowsSpecOfQ q hq pi

/-- The executable algorithmic inverse parameter is positive. -/
theorem sourceAlgorithmQ_pos : 0 < sourceAlgorithmQ := by
  norm_num [sourceAlgorithmQ]

/-- The executable human inverse parameter is positive. -/
theorem sourceHumanQ_pos : 0 < sourceHumanQ := by
  norm_num [sourceHumanQ]

/-- The library's four-candidate partition at the source algorithm parameter
has the exact rationally transported value. -/
theorem mallowsPartition_rankingTwo_algorithm :
    mallowsPartition ((1 : ℝ) / 2) (Equiv.refl (Candidate 2)) =
      (315 : ℝ) / 64 := by
  calc
    mallowsPartition ((1 : ℝ) / 2) (Equiv.refl (Candidate 2)) =
        ((sourceExecutableMallowsPartition sourceAlgorithmQ : ℚ) : ℝ) := by
          symm
          simpa only [sourceAlgorithmQ, Rat.cast_div, Rat.cast_one,
            Rat.cast_ofNat] using
            sourceExecutableMallowsPartition_cast sourceAlgorithmQ
    _ = ((315 / 64 : ℚ) : ℝ) := by
      rw [sourceExecutableMallowsPartition_algorithm]
    _ = (315 : ℝ) / 64 := by norm_num

/-- The library's four-candidate partition at the source human parameter has
the exact rationally transported value. -/
theorem mallowsPartition_rankingTwo_human :
    mallowsPartition ((4 : ℝ) / 7) (Equiv.refl (Candidate 2)) =
      (731445 : ℝ) / 117649 := by
  calc
    mallowsPartition ((4 : ℝ) / 7) (Equiv.refl (Candidate 2)) =
        ((sourceExecutableMallowsPartition sourceHumanQ : ℚ) : ℝ) := by
          symm
          simpa only [sourceHumanQ, Rat.cast_div, Rat.cast_ofNat] using
            sourceExecutableMallowsPartition_cast sourceHumanQ
    _ = ((731445 / 117649 : ℚ) : ℝ) := by
      rw [sourceExecutableMallowsPartition_human]
    _ = (731445 : ℝ) / 117649 := by norm_num

/-- The transparent algorithm table is a normalized finite source law, before
its atomwise identification with the library PMF below. -/
theorem sourceAlgorithmMallowsMass_sum_from_executable :
    (∑ pi : SourceFourRanking, sourceAlgorithmMallowsMass pi) = 1 := by
  simp_rw [sourceAlgorithmMallowsMass_eq_executable]
  exact sourceExecutableMallowsMass_sum sourceAlgorithmQ sourceAlgorithmQ_pos

/-- The source's transparent algorithmic mass table is the library's actual
four-candidate Mallows law at `q = 1/2`, atom by atom. -/
theorem sourceAlgorithmMallowsMass_cast_eq_mallowsSpecOfQ
    (pi : SourceFourRanking) :
    ((sourceAlgorithmMallowsMass pi : ℚ) : ℝ) =
      ((MallowsSpec.ofQ (Equiv.refl (Candidate 2)) ((1 : ℝ) / 2)
        (by norm_num)).law (sourceFourRankingToRanking pi)).toReal := by
  rw [sourceAlgorithmMallowsMass_eq_executable]
  simpa only [sourceAlgorithmQ, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    using sourceExecutableMallowsMass_cast_eq_mallowsSpecOfQ
      sourceAlgorithmQ sourceAlgorithmQ_pos pi

/-- The source's transparent human mass table is the library's actual
four-candidate Mallows law at `q = 4/7`, atom by atom. -/
theorem sourceHumanMallowsMass_cast_eq_mallowsSpecOfQ
    (pi : SourceFourRanking) :
    ((sourceHumanMallowsMass pi : ℚ) : ℝ) =
      ((MallowsSpec.ofQ (Equiv.refl (Candidate 2)) ((4 : ℝ) / 7)
        (by norm_num)).law (sourceFourRankingToRanking pi)).toReal := by
  rw [sourceHumanMallowsMass_eq_executable]
  simpa only [sourceHumanQ, Rat.cast_div, Rat.cast_ofNat]
    using sourceExecutableMallowsMass_cast_eq_mallowsSpecOfQ
      sourceHumanQ sourceHumanQ_pos pi

end KR21Monoculture
