import AppliedModelingLib.Foundations.Math.FiniteRanking
import PG24NoisyMatchingMarkets.MainTheorems
import PG24NoisyMatchingMarkets.Theorem3DenseGapGeometry

/-!
# PG24 Theorem 3 canonical ranked cutoffs

The paper says that coalition cutoffs may be sorted without loss of
generality.  This module implements that step semantically: it uses the
library's tie-broken finite ranking of an arbitrary cutoff function, then
transports rank windows and suffixes back to the original college indices.
No sorted-index source assumption is used.
-/

namespace PG24NoisyMatchingMarkets

noncomputable section

/-- The cardinality of the indexed coalition used by the ranked-cutoff route. -/
theorem theorem3_ranked_cutoff_univ_card (C : ℕ) :
    (Finset.univ : Finset (Fin (C + 1))).card = C + 1 := by
  simp

/-- The college at a tie-broken nondecreasing cutoff rank. -/
noncomputable def theorem3RankedCollege
    (C : ℕ) (cutoff : Fin (C + 1) → ℝ) : Fin (C + 1) → Fin (C + 1) :=
  AppliedModelingLib.FiniteRanking.rankAgentByValue
    (Finset.univ : Finset (Fin (C + 1))) cutoff
    (theorem3_ranked_cutoff_univ_card C)

/-- The cutoff value at a tie-broken nondecreasing cutoff rank. -/
noncomputable def theorem3RankedCutoff
    (C : ℕ) (cutoff : Fin (C + 1) → ℝ) : Fin (C + 1) → ℝ :=
  AppliedModelingLib.FiniteRanking.rankValueByValue
    (Finset.univ : Finset (Fin (C + 1))) cutoff
    (theorem3_ranked_cutoff_univ_card C)

/-- A ranked cutoff is the original cutoff of its ranked college. -/
theorem theorem3RankedCutoff_eq_original
    (C : ℕ) (cutoff : Fin (C + 1) → ℝ) (i : Fin (C + 1)) :
    theorem3RankedCutoff C cutoff i =
      cutoff (theorem3RankedCollege C cutoff i) := by
  exact
    AppliedModelingLib.FiniteRanking.rankValueByValue_eq_value
      (Finset.univ : Finset (Fin (C + 1))) cutoff
      (theorem3_ranked_cutoff_univ_card C) i

/-- The canonical ranked cutoff vector is nondecreasing. -/
theorem theorem3RankedCutoff_mono
    (C : ℕ) (cutoff : Fin (C + 1) → ℝ)
    {i j : Fin (C + 1)} (hij : i.val ≤ j.val) :
    theorem3RankedCutoff C cutoff i ≤ theorem3RankedCutoff C cutoff j := by
  rcases lt_or_eq_of_le hij with hij_lt | hij_eq
  · exact
      AppliedModelingLib.FiniteRanking.rankValueByValue_mono
        (Finset.univ : Finset (Fin (C + 1))) cutoff
        (theorem3_ranked_cutoff_univ_card C) i j hij_lt
  · have hij_fin : i = j := Fin.ext hij_eq
    subst j
    exact le_rfl

/--
The canonical ranked cutoff vector extended to natural ranks.  Values beyond
the finite coalition are clamped at its final rank solely so that the generic
finite telescoping lemma can be applied without an implicit index convention.
-/
noncomputable def theorem3RankedCutoffNat
    (C : ℕ) (cutoff : Fin (C + 1) → ℝ) (rank : ℕ) : ℝ :=
  theorem3RankedCutoff C cutoff
    ⟨min rank C, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩

/-- The natural-rank extension remains nondecreasing. -/
theorem theorem3RankedCutoffNat_mono
    (C : ℕ) (cutoff : Fin (C + 1) → ℝ) :
    Monotone (theorem3RankedCutoffNat C cutoff) := by
  intro i j hij
  apply theorem3RankedCutoff_mono C cutoff
  exact min_le_min_right C hij

/-- Within the coalition range, the natural-rank extension is the exact rank. -/
theorem theorem3RankedCutoffNat_eq_rankedCutoff
    (C : ℕ) (cutoff : Fin (C + 1) → ℝ) {rank : ℕ}
    (hrank : rank ≤ C) :
    theorem3RankedCutoffNat C cutoff rank =
      theorem3RankedCutoff C cutoff ⟨rank, Nat.lt_succ_of_le hrank⟩ := by
  simp [theorem3RankedCutoffNat, Nat.min_eq_left hrank]

/-- The natural-rank cutoff is the cutoff of its canonical ranked college. -/
theorem theorem3RankedCutoffNat_eq_cutoff_rankedCollege
    (C : ℕ) (cutoff : Fin (C + 1) → ℝ) (rank : ℕ) :
    theorem3RankedCutoffNat C cutoff rank =
      cutoff (theorem3RankedCollege C cutoff
        ⟨min rank C, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩) := by
  unfold theorem3RankedCutoffNat
  exact theorem3RankedCutoff_eq_original C cutoff _

/--
The dense-window / large-gap dichotomy applies to the canonical ranking of an
arbitrary finite cutoff function.  Thus the source's "without loss of
generality, sort the cutoffs" sentence is a derived construction rather than
a theorem premise.
-/
theorem theorem3_ranked_denseWindow_or_rounded_large_gap
    {C : ℕ} {denseExponent prefixExponent width : ℝ}
    (cutoff : Fin (C + 1) → ℝ)
    (hC_pos : 0 < C)
    (hfit :
      theorem3DenseWindowCount C denseExponent ≤
        theorem3EarlyPrefixRank C prefixExponent) :
    (∃ start : ℕ,
      start + theorem3DenseWindowCount C denseExponent ≤
          theorem3DenseGapBlockCount C denseExponent prefixExponent *
            theorem3DenseWindowCount C denseExponent ∧
        theorem1TailDenseRankWindow (theorem3RankedCutoffNat C cutoff) start
          (theorem3DenseWindowCount C denseExponent) width) ∨
      theorem3RankedCutoffNat C cutoff 0 +
          (theorem3DenseGapBlockCount C denseExponent prefixExponent : ℝ) *
            width <
        theorem3RankedCutoffNat C cutoff
          (theorem3EarlyPrefixRank C prefixExponent) :=
  theorem3_denseWindow_or_rounded_large_gap
    (theorem3RankedCutoffNat C cutoff) hC_pos
    (theorem3RankedCutoffNat_mono C cutoff) hfit

/-- The original-college suffix obtained by deleting the first `cut` ranks. -/
noncomputable def theorem3RankedSuffix
    (C : ℕ) (cutoff : Fin (C + 1) → ℝ) (cut : ℕ) :
    Finset (Fin (C + 1)) :=
  AppliedModelingLib.FiniteRanking.upperRankFinset
    (Finset.univ : Finset (Fin (C + 1))) cutoff
    (theorem3_ranked_cutoff_univ_card C) cut

/-- A ranked suffix is a subset of the original coalition. -/
theorem theorem3RankedSuffix_subset
    (C : ℕ) (cutoff : Fin (C + 1) → ℝ) (cut : ℕ) :
    theorem3RankedSuffix C cutoff cut ⊆
      (Finset.univ : Finset (Fin (C + 1))) := by
  exact
    AppliedModelingLib.FiniteRanking.upperRankFinset_subset
      (Finset.univ : Finset (Fin (C + 1))) cutoff
      (theorem3_ranked_cutoff_univ_card C) cut

/-- Exact cardinality of the original-college ranked suffix. -/
theorem theorem3RankedSuffix_card
    (C : ℕ) (cutoff : Fin (C + 1) → ℝ) (cut : ℕ) :
    (theorem3RankedSuffix C cutoff cut).card =
      (C + 1) - min (C + 1) cut := by
  exact
    AppliedModelingLib.FiniteRanking.upperRankFinset_card
      (Finset.univ : Finset (Fin (C + 1))) cutoff
      (theorem3_ranked_cutoff_univ_card C) cut

/--
Deleting a rank prefix that is smaller than an `epsilon` fraction leaves a
large semantic suffix in the exact paper sense.  This is independent of the
names or original ordering of colleges.
-/
theorem theorem3CoalitionLargeSubset_rankedSuffix_of_cut_fraction_lt
    {C cut : ℕ} {epsilon : ℝ} (cutoff : Fin (C + 1) → ℝ)
    (hcut : cut ≤ C)
    (hcut_fraction :
      (cut : ℝ) / (((C + 1 : ℕ) : ℝ)) < epsilon) :
    CoalitionLargeSubset
      (Finset.univ : Finset (Fin (C + 1)))
      (theorem3RankedSuffix C cutoff cut) epsilon := by
  refine ⟨theorem3RankedSuffix_subset C cutoff cut, ?_, ?_⟩
  · simpa using (show 0 < (((C + 1 : ℕ) : ℝ)) by
      exact_mod_cast Nat.succ_pos C)
  · have hcut_succ : cut ≤ C + 1 :=
      le_trans hcut (Nat.le_succ C)
    have hden_pos : 0 < (((C + 1 : ℕ) : ℝ)) := by
      exact_mod_cast Nat.succ_pos C
    have hden_ne : (((C + 1 : ℕ) : ℝ)) ≠ 0 := ne_of_gt hden_pos
    have hsuffix_card :
        ((theorem3RankedSuffix C cutoff cut).card : ℝ) =
          (((C + 1 : ℕ) : ℝ)) - (cut : ℝ) := by
      rw [theorem3RankedSuffix_card,
        min_eq_right hcut_succ]
      norm_cast
    have huniv_card :
        (((Finset.univ : Finset (Fin (C + 1))).card : ℝ)) =
          (((C + 1 : ℕ) : ℝ)) := by
      simp
    calc
      1 - epsilon < 1 -
          (cut : ℝ) / (((C + 1 : ℕ) : ℝ)) := by linarith
      _ = ((theorem3RankedSuffix C cutoff cut).card : ℝ) /
          (((Finset.univ : Finset (Fin (C + 1))).card : ℝ)) := by
        rw [hsuffix_card, huniv_card]
        field_simp [hden_ne]

/-- A suffix beginning no later than a small prefix is itself a large subset. -/
theorem theorem3CoalitionLargeSubset_rankedSuffix_of_le_cut_fraction_lt
    {C start cut : ℕ} {epsilon : ℝ} (cutoff : Fin (C + 1) → ℝ)
    (hstart_cut : start ≤ cut) (hcut : cut ≤ C)
    (hcut_fraction :
      (cut : ℝ) / (((C + 1 : ℕ) : ℝ)) < epsilon) :
    CoalitionLargeSubset
      (Finset.univ : Finset (Fin (C + 1)))
      (theorem3RankedSuffix C cutoff start) epsilon := by
  apply theorem3CoalitionLargeSubset_rankedSuffix_of_cut_fraction_lt
    cutoff (le_trans hstart_cut hcut)
  have hden_pos : 0 < (((C + 1 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.succ_pos C
  exact lt_of_le_of_lt
    (div_le_div_of_nonneg_right (by exact_mod_cast hstart_cut) hden_pos.le)
    hcut_fraction

/--
Every original college in a ranked suffix has cutoff at least the cutoff at
the suffix's first rank.  This is the semantic substitute for an assumed
sorted-index cutoff-floor clause.
-/
theorem theorem3RankedCutoff_le_cutoff_of_mem_rankedSuffix
    (C : ℕ) (cutoff : Fin (C + 1) → ℝ) {cut : ℕ}
    (hcut : cut ≤ C) {college : Fin (C + 1)}
    (hcollege : college ∈ theorem3RankedSuffix C cutoff cut) :
    theorem3RankedCutoff C cutoff
        ⟨cut, Nat.lt_succ_of_le hcut⟩ ≤ cutoff college := by
  rcases Finset.mem_image.mp hcollege with ⟨i, hi, rfl⟩
  have hcut_i : cut ≤ i.val := (Finset.mem_filter.mp hi).2
  change theorem3RankedCutoff C cutoff
      ⟨cut, Nat.lt_succ_of_le hcut⟩ ≤
    cutoff (theorem3RankedCollege C cutoff i)
  rw [← theorem3RankedCutoff_eq_original C cutoff i]
  exact theorem3RankedCutoff_mono C cutoff hcut_i

/-- The suffix floor stated through the natural-rank extension. -/
theorem theorem3RankedCutoffNat_le_cutoff_of_mem_rankedSuffix
    (C : ℕ) (cutoff : Fin (C + 1) → ℝ) {cut : ℕ}
    (hcut : cut ≤ C) {college : Fin (C + 1)}
    (hcollege : college ∈ theorem3RankedSuffix C cutoff cut) :
    theorem3RankedCutoffNat C cutoff cut ≤ cutoff college := by
  rw [theorem3RankedCutoffNat_eq_rankedCutoff C cutoff hcut]
  exact theorem3RankedCutoff_le_cutoff_of_mem_rankedSuffix
    C cutoff hcut hcollege

/-- The original-college set represented by a closed interval of cutoff ranks. -/
noncomputable def theorem3RankedWindow
    (C : ℕ) (cutoff : Fin (C + 1) → ℝ)
    (start terminal : Fin (C + 1)) : Finset (Fin (C + 1)) :=
  (Finset.Icc start terminal).image (theorem3RankedCollege C cutoff)

/-- A ranked window has the same cardinality as its finite rank interval. -/
theorem theorem3RankedWindow_card
    (C : ℕ) (cutoff : Fin (C + 1) → ℝ)
    (start terminal : Fin (C + 1)) :
    (theorem3RankedWindow C cutoff start terminal).card =
      terminal.val + 1 - start.val := by
  unfold theorem3RankedWindow
  rw [Finset.card_image_of_injective]
  · exact Fin.card_Icc start terminal
  · exact
      AppliedModelingLib.FiniteRanking.rankAgentByValue_injective
        (Finset.univ : Finset (Fin (C + 1))) cutoff
        (theorem3_ranked_cutoff_univ_card C)

/--
Every original college in a ranked window has cutoff between the cutoffs at
the two window endpoints.
-/
theorem theorem3RankedWindow_cutoff_bounds
    (C : ℕ) (cutoff : Fin (C + 1) → ℝ)
    (start terminal : Fin (C + 1)) {college : Fin (C + 1)}
    (hcollege : college ∈ theorem3RankedWindow C cutoff start terminal) :
    theorem3RankedCutoff C cutoff start ≤ cutoff college ∧
      cutoff college ≤ theorem3RankedCutoff C cutoff terminal := by
  rcases Finset.mem_image.mp hcollege with ⟨i, hi, rfl⟩
  have hi_bounds := Finset.mem_Icc.mp hi
  constructor
  · rw [← theorem3RankedCutoff_eq_original C cutoff i]
    exact theorem3RankedCutoff_mono C cutoff hi_bounds.1
  · rw [← theorem3RankedCutoff_eq_original C cutoff i]
    exact theorem3RankedCutoff_mono C cutoff hi_bounds.2

/-- A semantic ranked window lies inside the semantic suffix at its first rank. -/
theorem theorem3RankedWindow_subset_rankedSuffix
    (C : ℕ) (cutoff : Fin (C + 1) → ℝ)
    (start terminal : Fin (C + 1)) :
    theorem3RankedWindow C cutoff start terminal ⊆
      theorem3RankedSuffix C cutoff start.val := by
  intro college hcollege
  rcases Finset.mem_image.mp hcollege with ⟨i, hi, rfl⟩
  unfold theorem3RankedSuffix
  refine Finset.mem_image.mpr ⟨i, ?_, rfl⟩
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ i, (Finset.mem_Icc.mp hi).1⟩

/--
A dense natural-rank window gives the cutoff ceiling needed by the iid
dense-cluster probability bound on its semantic original-college window.
-/
theorem theorem3RankedWindow_cutoff_le_start_add_of_denseRankWindow
    (C start stride : ℕ) (cutoff : Fin (C + 1) → ℝ) (width : ℝ)
    (hterminal : start + stride ≤ C)
    (hdense :
      theorem1TailDenseRankWindow (theorem3RankedCutoffNat C cutoff)
        start stride width)
    {college : Fin (C + 1)}
    (hcollege : college ∈ theorem3RankedWindow C cutoff
      ⟨start, Nat.lt_succ_of_le (le_trans (Nat.le_add_right start stride) hterminal)⟩
      ⟨start + stride, Nat.lt_succ_of_le hterminal⟩) :
    cutoff college ≤ theorem3RankedCutoffNat C cutoff start + width := by
  have hwindow_upper :=
    (theorem3RankedWindow_cutoff_bounds C cutoff
      ⟨start, Nat.lt_succ_of_le
        (le_trans (Nat.le_add_right start stride) hterminal)⟩
      ⟨start + stride, Nat.lt_succ_of_le hterminal⟩ hcollege).2
  have hdense_upper :=
    (hdense (start + stride) (by omega) le_rfl).2
  calc
    cutoff college ≤ theorem3RankedCutoff C cutoff
        ⟨start + stride, Nat.lt_succ_of_le hterminal⟩ := hwindow_upper
    _ = theorem3RankedCutoffNat C cutoff (start + stride) :=
      (theorem3RankedCutoffNat_eq_rankedCutoff C cutoff hterminal).symm
    _ ≤ theorem3RankedCutoffNat C cutoff start + width := hdense_upper

/--
If a source rank window starts at `start` and has `stride + 1` ranks, its
semantic original-college window has exactly that many colleges.  The terminal
bound is explicit, so no out-of-range `P_(C^phi)` index is hidden.
-/
theorem theorem3RankedWindow_card_of_start_add_stride_le
    (C start stride : ℕ) (cutoff : Fin (C + 1) → ℝ)
    (hterminal : start + stride ≤ C) :
    (theorem3RankedWindow C cutoff
      ⟨start, Nat.lt_succ_of_le (le_trans (Nat.le_add_right start stride) hterminal)⟩
      ⟨start + stride, Nat.lt_succ_of_le hterminal⟩).card = stride + 1 := by
  rw [theorem3RankedWindow_card]
  change (start + stride) + 1 - start = stride + 1
  omega

end

end PG24NoisyMatchingMarkets
