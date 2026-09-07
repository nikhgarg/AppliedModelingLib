import PG24NoisyMatchingMarkets.Theorem3RankedCutoffs
import PG24NoisyMatchingMarkets.Theorem3RoundedScaleFit
import PG24NoisyMatchingMarkets.Theorem1RoundedChebyshevRates

open Filter
open AppliedModelingLib.Matching

namespace PG24NoisyMatchingMarkets

noncomputable section

universe u

/-- The source dense-window scale is strictly below the early-prefix scale. -/
theorem theorem1TailPhi2_lt_phi3 {beta gamma : ℝ}
    (hbeta : 0 < beta) (hgamma : 0 < gamma) :
    theorem1TailPhi2 beta gamma < theorem1TailPhi3 beta gamma := by
  have hden_pos : 0 < theorem1TailDenom beta gamma :=
    theorem1TailDenom_pos hbeta hgamma
  have hnum_lt : 5 * gamma + 6 <
      theorem1TailDenom beta gamma - 2 * beta * gamma := by
    unfold theorem1TailDenom
    nlinarith [mul_pos hbeta hgamma]
  calc
    theorem1TailPhi2 beta gamma =
        (5 * gamma + 6) / theorem1TailDenom beta gamma := rfl
    _ < (theorem1TailDenom beta gamma - 2 * beta * gamma) /
        theorem1TailDenom beta gamma :=
      div_lt_div_of_pos_right hnum_lt hden_pos
    _ = theorem1TailPhi3 beta gamma := by
      unfold theorem1TailPhi3
      field_simp [ne_of_gt hden_pos]

/--
The paper's rounded dense-window size eventually fits inside its rounded
early cutoff prefix.  This is derived from the source exponents, including
the ceiling/floor choices, rather than assumed by a selected-cutoff route.
-/
theorem theorem1DenseWindowCount_eventually_le_earlyPrefixRank
    {beta gamma : ℝ} (hbeta : 0 < beta) (hgamma : 0 < gamma) :
    ∀ᶠ C : ℕ in atTop,
      theorem3DenseWindowCount C (theorem1TailPhi2 beta gamma) ≤
        theorem3EarlyPrefixRank C (theorem1TailPhi3 beta gamma) :=
  theorem3DenseWindowCount_eventually_le_earlyPrefixRank
    (theorem1TailPhi2_pos hbeta hgamma).le
    (theorem1TailPhi2_lt_phi3 hbeta hgamma)

/-- The rounded early rank is a valid cutoff rank whenever the market is nonempty. -/
theorem theorem1EarlyPrefixRank_le_marketIndex
    {C : ℕ} {beta gamma : ℝ}
    (hbeta : 0 < beta) (hgamma : 0 < gamma) (hC_pos : 0 < C) :
    theorem3EarlyPrefixRank C (theorem1TailPhi3 beta gamma) ≤ C := by
  have hC_one : 1 ≤ C := Nat.succ_le_iff.mpr hC_pos
  have hC_real_one : (1 : ℝ) ≤ (C : ℝ) := by
    exact_mod_cast hC_one
  have hphi3_le_one : theorem1TailPhi3 beta gamma ≤ 1 := by
    have hK_nonneg : 0 ≤ theorem1TailK beta gamma :=
      (theorem1TailK_pos hbeta hgamma).le
    linarith [theorem1Tail_one_sub_phi3_eq_K beta gamma]
  have hfloor : (theorem3EarlyPrefixRank C
      (theorem1TailPhi3 beta gamma) : ℝ) ≤
      Real.rpow (C : ℝ) (theorem1TailPhi3 beta gamma) := by
    unfold theorem3EarlyPrefixRank
    exact Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg C) _)
  have hpower : Real.rpow (C : ℝ) (theorem1TailPhi3 beta gamma) ≤
      (C : ℝ) := by
    calc
      Real.rpow (C : ℝ) (theorem1TailPhi3 beta gamma) ≤
          Real.rpow (C : ℝ) 1 :=
        Real.rpow_le_rpow_of_exponent_le hC_real_one hphi3_le_one
      _ = (C : ℝ) := Real.rpow_one _
  exact_mod_cast hfloor.trans hpower

/--
At a canonical cutoff rank, colleges strictly below that cutoff occupy only
earlier ranks.  This supplies the sparse lower-block cardinality used by the
dense branch without assuming that college indices were pre-sorted.
-/
theorem theorem1CutoffBelowBlock_card_le_rank_start
    (C start : ℕ) (cutoff : Fin (C + 1) -> ℝ)
    (hstart : start ≤ C) :
    (theorem1CutoffBelowBlock (Finset.univ : Finset (Fin (C + 1))) cutoff
      (theorem3RankedCutoff C cutoff ⟨start, Nat.lt_succ_of_le hstart⟩)).card ≤
      start := by
  classical
  let pivot : ℝ := theorem3RankedCutoff C cutoff
    ⟨start, Nat.lt_succ_of_le hstart⟩
  let below : Finset (Fin (C + 1)) :=
    theorem1CutoffBelowBlock (Finset.univ : Finset (Fin (C + 1))) cutoff pivot
  let rankedLower : Finset (Fin (C + 1)) :=
    AppliedModelingLib.FiniteRanking.lowerRankFinset
      (Finset.univ : Finset (Fin (C + 1))) cutoff
      (theorem3_ranked_cutoff_univ_card C) start
  have hsubset : below ⊆ rankedLower := by
    intro college hcollege
    have hbelow : cutoff college < pivot := (Finset.mem_filter.mp hcollege).2
    have himage : college ∈ Finset.image
        (AppliedModelingLib.FiniteRanking.rankAgentByValue
          (Finset.univ : Finset (Fin (C + 1))) cutoff
          (theorem3_ranked_cutoff_univ_card C)) Finset.univ := by
      rw [AppliedModelingLib.FiniteRanking.image_rankAgentByValue_univ]
      exact Finset.mem_univ _
    rcases Finset.mem_image.mp himage with ⟨rank, _hrank_univ, hrank⟩
    refine Finset.mem_image.mpr ⟨rank, ?_, hrank⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ rank, ?_⟩
    by_contra hnot_lt
    have hstart_rank : start ≤ rank.val := Nat.le_of_not_gt hnot_lt
    have hmono := theorem3RankedCutoff_mono C cutoff
      (i := ⟨start, Nat.lt_succ_of_le hstart⟩) (j := rank) hstart_rank
    have hcollege_value : cutoff college = theorem3RankedCutoff C cutoff rank := by
      calc
        cutoff college = cutoff (theorem3RankedCollege C cutoff rank) := by
          simpa [theorem3RankedCollege] using congrArg cutoff hrank.symm
        _ = theorem3RankedCutoff C cutoff rank :=
          (theorem3RankedCutoff_eq_original C cutoff rank).symm
    have hpivot_value : pivot = theorem3RankedCutoff C cutoff
        ⟨start, Nat.lt_succ_of_le hstart⟩ := rfl
    rw [hcollege_value, hpivot_value] at hbelow
    exact (not_lt_of_ge hmono) hbelow
  calc
    below.card ≤ rankedLower.card := Finset.card_le_card hsubset
    _ = min (C + 1) start :=
      AppliedModelingLib.FiniteRanking.lowerRankFinset_card
        (Finset.univ : Finset (Fin (C + 1))) cutoff
        (theorem3_ranked_cutoff_univ_card C) start
    _ ≤ start := Nat.min_le_right _ _

/--
A canonical dense rank window is a concrete dense window of original college
indices at its first ranked cutoff.  This transports both endpoint geometry
and the finite cardinality back from the tie-broken ranking.
-/
theorem theorem1RankedDenseWindow_subset_cutoffWindowBlock
    (C start stride : ℕ) (cutoff : Fin (C + 1) -> ℝ) (width : ℝ)
    (hterminal : start + stride ≤ C)
    (hdense : theorem1TailDenseRankWindow
      (theorem3RankedCutoffNat C cutoff) start stride width) :
    theorem3RankedWindow C cutoff
      ⟨start, Nat.lt_succ_of_le
        (le_trans (Nat.le_add_right start stride) hterminal)⟩
      ⟨start + stride, Nat.lt_succ_of_le hterminal⟩ ⊆
      theorem1CutoffWindowBlock (Finset.univ : Finset (Fin (C + 1))) cutoff
        (theorem3RankedCutoffNat C cutoff start) width := by
  intro college hcollege
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  constructor
  · have hbounds := theorem3RankedWindow_cutoff_bounds C cutoff
      ⟨start, Nat.lt_succ_of_le
        (le_trans (Nat.le_add_right start stride) hterminal)⟩
      ⟨start + stride, Nat.lt_succ_of_le hterminal⟩ hcollege
    rw [theorem3RankedCutoffNat_eq_rankedCutoff C cutoff
      (le_trans (Nat.le_add_right start stride) hterminal)]
    exact hbounds.1
  · exact theorem3RankedWindow_cutoff_le_start_add_of_denseRankWindow
      C start stride cutoff width hterminal hdense hcollege

/--
The original-college cutoff window inherited from a dense ranked window has
at least the ranked window's exact number of colleges.
-/
theorem theorem1CutoffWindowBlock_card_ge_of_rankedDenseWindow
    (C start stride : ℕ) (cutoff : Fin (C + 1) -> ℝ) (width : ℝ)
    (hterminal : start + stride ≤ C)
    (hdense : theorem1TailDenseRankWindow
      (theorem3RankedCutoffNat C cutoff) start stride width) :
    stride + 1 ≤
      (theorem1CutoffWindowBlock (Finset.univ : Finset (Fin (C + 1))) cutoff
        (theorem3RankedCutoffNat C cutoff start) width).card := by
  calc
    stride + 1 =
        (theorem3RankedWindow C cutoff
          ⟨start, Nat.lt_succ_of_le
            (le_trans (Nat.le_add_right start stride) hterminal)⟩
          ⟨start + stride, Nat.lt_succ_of_le hterminal⟩).card := by
      symm
      exact theorem3RankedWindow_card_of_start_add_stride_le
        C start stride cutoff hterminal
    _ ≤ (theorem1CutoffWindowBlock
          (Finset.univ : Finset (Fin (C + 1))) cutoff
          (theorem3RankedCutoffNat C cutoff start) width).card :=
      Finset.card_le_card
        (theorem1RankedDenseWindow_subset_cutoffWindowBlock
          C start stride cutoff width hterminal hdense)

/--
For the actual selected cutoff vector, canonical ranking yields the source
dense-window/large-gap alternative.  No input assumes an ordering of college
names: ties are broken by the finite-ranking construction.
-/
theorem theorem1_selectedStable_ranked_denseWindow_or_large_gap_eventually
    {StudentType : Type u} [MeasurableSpace StudentType]
    (Mseq : ∀ C : ℕ, CutoffMarket StudentType (Fin (C + 1)))
    (Iseq : ∀ C : ℕ, SupplyDemandInterface (Mseq C))
    (selected : ∀ C : ℕ,
      { matching : (Mseq C).Matching // (Mseq C).Stable matching })
    (cutoffOut : ∀ C : ℕ, (Mseq C).Cutoff -> Fin (C + 1) -> ℝ)
    {beta gamma : ℝ} (hbeta : 0 < beta) (hgamma : 0 < gamma) :
    ∀ᶠ C : ℕ in atTop,
      (∃ start : ℕ,
        start + theorem3DenseWindowCount C (theorem1TailPhi2 beta gamma) ≤
            theorem3DenseGapBlockCount C
              (theorem1TailPhi2 beta gamma) (theorem1TailPhi3 beta gamma) *
              theorem3DenseWindowCount C (theorem1TailPhi2 beta gamma) ∧
          theorem1TailDenseRankWindow
            (theorem3RankedCutoffNat C
              (cutoffOut C
                ((Iseq C).marketClearingCutoffOfStable (selected C).2)))
            start
            (theorem3DenseWindowCount C (theorem1TailPhi2 beta gamma))
            (theorem1DenseDeviationRadius C beta gamma)) ∨
        theorem3RankedCutoffNat C
          (cutoffOut C
            ((Iseq C).marketClearingCutoffOfStable (selected C).2)) 0 +
          (theorem3DenseGapBlockCount C
            (theorem1TailPhi2 beta gamma) (theorem1TailPhi3 beta gamma) : ℝ) *
            theorem1DenseDeviationRadius C beta gamma <
          theorem3RankedCutoffNat C
            (cutoffOut C
              ((Iseq C).marketClearingCutoffOfStable (selected C).2))
            (theorem3EarlyPrefixRank C (theorem1TailPhi3 beta gamma)) := by
  filter_upwards [eventually_gt_atTop 0,
    theorem1DenseWindowCount_eventually_le_earlyPrefixRank hbeta hgamma]
      with C hC_pos hfit
  exact theorem3_ranked_denseWindow_or_rounded_large_gap
    (cutoffOut C
      ((Iseq C).marketClearingCutoffOfStable (selected C).2))
    hC_pos hfit

end

end PG24NoisyMatchingMarkets
