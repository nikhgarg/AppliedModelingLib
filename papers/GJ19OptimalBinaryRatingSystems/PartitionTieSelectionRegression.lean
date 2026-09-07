import GJ19OptimalBinaryRatingSystems.PartitionTieSelection

/-!
# Regression examples for the full cross-cell value

Four equal cells distinguish the primary objective from the nontrivial-error
component weight: the bottom-to-top rectangle contributes `1/16` to value.
-/

namespace GJ19OptimalBinaryRatingSystems

noncomputable section
open MeasureTheory Set
open scoped BigOperators Classical

/-- Four equal cells have full unnormalized cross-cell value `3/8`. -/
theorem allCrossCellValue_four_equal_cells :
    allCrossCellValue (fun _ : ℝ × ℝ => (1 : ℝ))
      (fun i : Fin 5 => (i.val : ℝ) / 4) = 3 / 8 := by
  norm_num [allCrossCellValue, Fin.sum_univ_succ, MeasureTheory.measureReal_prod_prod]
  norm_num [Fin.lt_def]

/-- The error component weight omits the bottom-to-top rectangle. -/
theorem nontrivialCellWeight_four_equal_cells :
    nontrivialCellWeightFiniteObjective volume 2 (fun _ : ℝ × ℝ => (1 : ℝ))
      (fun i : Fin 5 => (i.val : ℝ) / 4) = 5 / 16 := by
  rw [nontrivialCellWeightFiniteObjective_volume_const_eq_gapProduct]
  dsimp only
  have hstep (i : Fin 4) :
      finiteCutpointVectorEval 4 (fun i : Fin 5 => (i.val : ℝ) / 4) (i.val + 1) -
        finiteCutpointVectorEval 4 (fun i : Fin 5 => (i.val : ℝ) / 4) i.val = 1 / 4 := by
    fin_cases i <;> norm_num [finiteCutpointVectorEval]
  simp_rw [hstep]
  have hcard : Fintype.card (theorem31OrderedNontrivialPairComponent 2) = 5 := by decide
  norm_num [hcard]

/-- A strictly increasing source matching function on a nontrivial continuum. -/
theorem sourceMatchingFunction_affine_example :
    SourceMatchingFunction (fun x : ℝ => 1 / 2 + x / 4) := by
  refine ⟨?_, ?_, ⟨1 / 4, by norm_num, ?_⟩⟩
  · intro x hx y hy hxy
    dsimp
    linarith
  · intro x hx
    rcases hx with ⟨hx0, hx1⟩
    dsimp
    linarith
  · intro x hx
    rcases hx with ⟨hx0, hx1⟩
    dsimp
    linarith

/-- The general construction yields nonempty continuum cells and strictly
ordered levels with nonconstant matching. -/
theorem exists_strict_design_affine_matching_example :
    ∃ s : Fin 4 → ℝ, ∃ levels : Fin 3 → ℝ,
      s ∈ finiteOrderedCutpointSet 3 ∧ StrictMono s ∧
      BinaryEndpointLevelVector levels ∧
      BinaryEndpointAwareAdjacentRatesEqualize levels
        (finiteCutpointSampleRate (fun x : ℝ => 1 / 2 + x / 4) s) := by
  obtain ⟨s, levels, hs, hstrict, hl, heq, _hlex⟩ :=
    exists_strict_allCrossCell_lexicographic_formula (m := 1) (by norm_num)
      (fun _ : ℝ × ℝ => (1 : ℝ))
      (integrableOn_const (by rw [Measure.prod_prod]; norm_num))
      (by intros; norm_num) _ sourceMatchingFunction_affine_example
  exact ⟨s, levels, hs, hstrict, hl, heq⟩

/-- A source-allowed jump immediately to the right of an included cutpoint. -/
def matchingJumpExample (x : ℝ) : ℝ := if x ≤ 1 / 2 then 1 / 4 else 3 / 4

theorem sourceMatchingFunction_jump_example : SourceMatchingFunction matchingJumpExample := by
  refine ⟨?_, ?_, ⟨1 / 8, by norm_num, ?_⟩⟩
  · intro x hx y hy hxy
    unfold matchingJumpExample
    split_ifs <;> norm_num at * <;> linarith
  · intro x hx
    unfold matchingJumpExample
    split_ifs <;> norm_num
  · intro x hx
    unfold matchingJumpExample
    split_ifs <;> norm_num

/-- Source cells retain the lower-cutpoint rate even at this discontinuity. -/
theorem source_cell_rate_includes_jump_boundary :
    sourceFiniteSampleRate matchingJumpExample
      (fun i : Fin 3 => (i.val : ℝ) / 2) (1 : Fin 2) = 1 / 4 := by
  have hs : (fun i : Fin 3 => (i.val : ℝ) / 2) ∈ sourceStrictCutpointSet 2 := by
    refine ⟨?_, by norm_num, by norm_num⟩
    intro i j hij
    dsimp
    exact div_lt_div_of_pos_right (by exact_mod_cast hij) (by norm_num)
  rw [sourceFiniteSampleRate_eq_finiteCutpointSampleRate
    matchingJumpExample sourceMatchingFunction_jump_example _ hs]
  norm_num [finiteCutpointSampleRate, matchingJumpExample]

/-- Reassigning that boundary to an Ioc cell changes the infimum to `3/4`.
It is safe to change endpoint ownership only in the integral adapter. -/
theorem Ioc_cell_rate_excludes_jump_boundary :
    sInf (matchingJumpExample '' Ioc (1 / 2 : ℝ) 1) = 3 / 4 := by
  have himage : matchingJumpExample '' Ioc (1 / 2 : ℝ) 1 = {3 / 4} := by
    ext y
    simp only [mem_image, mem_singleton_iff]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [matchingJumpExample, if_neg (not_le.mpr hx.1)]
    · rintro rfl
      exact ⟨1, by norm_num, by norm_num [matchingJumpExample]⟩
  rw [himage]
  simp

end
end GJ19OptimalBinaryRatingSystems
