import SeshadriUgander2020IIATesting.AppendixCyclePackingComposition
import SeshadriUgander2020IIATesting.Testing

/-!
# Corrected finite form of Corollary 1

The source's Appendix Lemma 10 has a rational mean bound whose denominator
can be nonpositive.  This module states the resulting Corollary 1 testing
bound on exactly the positive-denominator range; the unconditional `2n`
branch remains available in the Appendix cycle-packing module.
-/

namespace SeshadriUgander2020IIATesting

namespace ChoiceFrame

variable {F : ChoiceFrame}

/-- The corrected Appendix-Lemma-10 mean bound used by Corollary 1. -/
noncomputable def sourceCorollaryMeanBound : ℝ :=
  min
    ((F.incidenceCount : ℝ) * (4 * Real.logb 2 (Fintype.card F.Item)) /
      ((F.incidenceCount : ℝ) - 4 * (Fintype.card F.Item : ℝ) +
        2 * (4 * Real.logb 2 (Fintype.card F.Item))))
    (2 * (Fintype.card F.Item : ℝ))

/-- The corrected Appendix-Lemma-10 dispersion bound used by Corollary 1. -/
noncomputable def sourceCorollaryDispersionBound : ℝ :=
  min
    (4 * Real.logb 2 (Fintype.card F.Item) +
      (4 * (Fintype.card F.Item : ℝ) *
        (2 * (Fintype.card F.Item : ℝ) -
          4 * Real.logb 2 (Fintype.card F.Item))) /
        (F.incidenceCount : ℝ))
    (2 * (Fintype.card F.Item : ℝ))

/-- A fully finite, source-corrected Corollary 1.  The construction of the
two-tier cycle decomposition is explicit; the premise records both the
necessary positive denominator in the printed mean branch and Theorem 1's
implicit small-separation condition. -/
theorem productTestingLowerBound_sourceCorollaryOne
    (hEulerian : F.Eulerian) (hnfour : 4 ≤ Fintype.card F.Item)
    (hden : 0 < (F.incidenceCount : ℝ) - 4 * (Fintype.card F.Item : ℝ) +
      2 * (4 * Real.logb 2 (Fintype.card F.Item)))
    (δ : ℝ) (hδ_nonneg : 0 ≤ δ)
    (hsmall : 2 * F.sourceCorollaryMeanBound * δ ≤ 1) (N : ℕ) :
    ChoiceSystem.ProductTestingLowerBound (F := F) N δ
      (1 / 2 - (1 / 4 : ℝ) *
        Real.sqrt (Real.exp
          ((8 * F.sourceCorollaryMeanBound ^ 4 *
              F.sourceCorollaryDispersionBound * (N : ℝ) ^ 2 * δ ^ 4) /
            (F.incidenceCount : ℝ)) - 1)) := by
  obtain ⟨P, Q, hQcomplete, hbudget, htwoTier⟩ :=
    F.eulerian_incidenceGraph_exists_source_twoTierCycleBounds hEulerian
  let D := F.composedCycleDecomposition P Q hQcomplete
  let W : D.AlternatingCycleWitness := by
    simpa [D] using F.composedCycleDecomposition_alternatingCycleWitness P Q hQcomplete
  have hmean : D.cycleMean ≤ F.sourceCorollaryMeanBound := by
    simpa [D, sourceCorollaryMeanBound] using
      F.sourceComposed_cycleMean_le_source_min P Q hQcomplete hbudget hnfour hden
  have hdispersion : CycleMixture.cycleDispersion F.incidenceCount D.length ≤
      F.sourceCorollaryDispersionBound := by
    simpa [D, sourceCorollaryDispersionBound] using
      F.sourceComposed_cycleDispersion_le_source_min P Q hQcomplete hbudget hnfour
  simpa [D] using D.productTestingLowerBound_of_cycleStatisticBounds W
    F.sourceCorollaryMeanBound F.sourceCorollaryDispersionBound hmean hdispersion
    δ hδ_nonneg hsmall N

end ChoiceFrame

end SeshadriUgander2020IIATesting
