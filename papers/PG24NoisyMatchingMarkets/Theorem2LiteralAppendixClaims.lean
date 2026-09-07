import PG24NoisyMatchingMarkets.Theorem2TwoScaleReducedModelBoundaryRate
import Mathlib.Tactic

/-!
# PG24 Theorem 2 literal appendix claims

This module realizes the two preliminary appendix lemmas in
`source_tex/proof-amplifying.tex` directly from literal iid coalition sampling,
the cutoff demand rule, and clearing capacity.  In particular, the cutoff
divergence below is not assumed as a source-shaped geometry certificate.
-/

open Filter Topology MeasureTheory
open AppliedModelingLib.Matching

namespace PG24NoisyMatchingMarkets

noncomputable section

universe u v w x

/--
Literal-source form of Appendix Lemma `unbounded-cutoffs`.

The paper orders the `C` college cutoffs and calls the block after index
`epsilon C` its large-firm block.  The finite-product convention here has
`Fin (C + 1)` coordinates, and `epsilonFloorSplitIndex epsilon C` is the
corresponding rounded prefix boundary.  Every cutoff in the resulting suffix
eventually exceeds each fixed real floor, uniformly for the supplied
source-stable economy sequence.
-/
theorem theorem2_literalSource_unbounded_cutoffs_eventually
    {StudentTypeSeq : ℕ → Type u} [∀ C, MeasurableSpace (StudentTypeSeq C)]
    {OutcomeSeq : ℕ → Type v} [∀ C, MeasurableSpace (OutcomeSeq C)]
    {GlobalCollegeSeq : ℕ → Type w} [∀ C, Fintype (GlobalCollegeSeq C)]
    (CutoffSeq : ℕ → Type x)
    (noiseLaw eta : Measure ℝ)
    [IsProbabilityMeasure noiseLaw] [IsProbabilityMeasure eta]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    {totalSupply epsilon : ℝ}
    (hepsilon_pos : 0 < epsilon) (htotalSupply_lt_one : totalSupply < 1)
    (data : ∀ C : ℕ,
      PG24LiteralSourceStableData C noiseLaw eta totalSupply
        (StudentTypeSeq C) (OutcomeSeq C) (GlobalCollegeSeq C) (CutoffSeq C))
    (hsorted :
      ∀ C : ℕ, ∀ i j : Fin (C + 1), (i : ℕ) ≤ (j : ℕ) →
        ((data C).toExtendedCoalitionSourceStableInstance.localCutoff i) ≤
          ((data C).toExtendedCoalitionSourceStableInstance.localCutoff j)) :
    ∀ P : ℝ, ∀ᶠ C : ℕ in atTop,
      ∀ c ∈ indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C,
        P < (data C).toExtendedCoalitionSourceStableInstance.localCutoff c := by
  have hsorted_eventually :
      ∀ᶠ C : ℕ in atTop,
        ∀ i j : Fin (C + 1), (i : ℕ) ≤ (j : ℕ) →
          ((data C).toExtendedCoalitionSourceStableInstance.localCutoff i) ≤
            ((data C).toExtendedCoalitionSourceStableInstance.localCutoff j) :=
    Filter.Eventually.of_forall hsorted
  rcases theorem2_literalSource_exists_sigma_suffix_geometry_of_longTailed
      CutoffSeq noiseLaw eta hlong
      (splitTol := 2 * epsilon) (vHigh := 0)
      (by linarith) htotalSupply_lt_one data hsorted_eventually with
    ⟨_sigma, _hsigma_pos, hcutoff, _htail⟩
  intro P
  have hsplit : (2 * epsilon) / 2 = epsilon := by ring
  filter_upwards [hcutoff (P + 1)] with C hcutoffC c hc
  rw [hsplit] at hcutoffC
  have hfloor : P + 1 ≤
      (data C).toExtendedCoalitionSourceStableInstance.localCutoff c := by
    exact hcutoffC c hc
  linarith

/--
Literal-source form of the unnamed large-firm tail lemma following `apple`.

The source writes an `O(1 / C)` upper-tail bound for every cutoff in its
large-firm suffix.  The source-native capacity route first yields the stronger
nonempty-product denominator `C + 1`; the final comparison recovers the
printed `sigma / C` rate for positive market sizes.
-/
theorem theorem2_literalSource_large_firm_tail_bound_eventually
    {StudentTypeSeq : ℕ → Type u} [∀ C, MeasurableSpace (StudentTypeSeq C)]
    {OutcomeSeq : ℕ → Type v} [∀ C, MeasurableSpace (OutcomeSeq C)]
    {GlobalCollegeSeq : ℕ → Type w} [∀ C, Fintype (GlobalCollegeSeq C)]
    (CutoffSeq : ℕ → Type x)
    (noiseLaw eta : Measure ℝ)
    [IsProbabilityMeasure noiseLaw] [IsProbabilityMeasure eta]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    {totalSupply epsilon vHigh : ℝ}
    (hepsilon_pos : 0 < epsilon) (htotalSupply_lt_one : totalSupply < 1)
    (data : ∀ C : ℕ,
      PG24LiteralSourceStableData C noiseLaw eta totalSupply
        (StudentTypeSeq C) (OutcomeSeq C) (GlobalCollegeSeq C) (CutoffSeq C))
    (hsorted :
      ∀ C : ℕ, ∀ i j : Fin (C + 1), (i : ℕ) ≤ (j : ℕ) →
        ((data C).toExtendedCoalitionSourceStableInstance.localCutoff i) ≤
          ((data C).toExtendedCoalitionSourceStableInstance.localCutoff j)) :
    ∃ sigma : ℝ, 0 < sigma ∧
      ∀ᶠ C : ℕ in atTop,
        ∀ c ∈ indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C,
          AppliedModelingLib.Probability.upperTailMass noiseLaw
              ((data C).toExtendedCoalitionSourceStableInstance.localCutoff c - vHigh) ≤
            sigma / (C : ℝ) := by
  have hsorted_eventually :
      ∀ᶠ C : ℕ in atTop,
        ∀ i j : Fin (C + 1), (i : ℕ) ≤ (j : ℕ) →
          ((data C).toExtendedCoalitionSourceStableInstance.localCutoff i) ≤
            ((data C).toExtendedCoalitionSourceStableInstance.localCutoff j) :=
    Filter.Eventually.of_forall hsorted
  rcases theorem2_literalSource_exists_sigma_suffix_geometry_of_longTailed
      CutoffSeq noiseLaw eta hlong
      (splitTol := 2 * epsilon) (vHigh := vHigh)
      (by linarith) htotalSupply_lt_one data hsorted_eventually with
    ⟨sigma, hsigma_pos, _hcutoff, htail⟩
  refine ⟨sigma, hsigma_pos, ?_⟩
  have hsplit : (2 * epsilon) / 2 = epsilon := by ring
  rw [hsplit] at htail
  filter_upwards [htail, Filter.eventually_atTop.2 ⟨1, fun C hC => hC⟩] with
    C htailC hC_one c hc
  have hC_pos : 0 < (C : ℝ) := by
    exact_mod_cast (show 0 < C by omega)
  have hC_le_succ : (C : ℝ) ≤ ((C + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_succ C
  exact (htailC c hc).trans
    (div_le_div_of_nonneg_left hsigma_pos.le hC_pos hC_le_succ)

/--
Literal-source form of Appendix Lemma `apple`.

Once the large-firm cutoffs diverge, long-tailed survival gives the source
ratio for every large-firm cutoff.  Positivity of the denominator is explicit:
it follows eventually from long-tailed survival and makes the printed ratio a
genuine conditional-tail comparison rather than Lean's totalized division.
-/
theorem theorem2_literalSource_apple_eventually
    {StudentTypeSeq : ℕ → Type u} [∀ C, MeasurableSpace (StudentTypeSeq C)]
    {OutcomeSeq : ℕ → Type v} [∀ C, MeasurableSpace (OutcomeSeq C)]
    {GlobalCollegeSeq : ℕ → Type w} [∀ C, Fintype (GlobalCollegeSeq C)]
    (CutoffSeq : ℕ → Type x)
    (noiseLaw eta : Measure ℝ)
    [IsProbabilityMeasure noiseLaw] [IsProbabilityMeasure eta]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    {totalSupply epsilon vLow vHigh : ℝ}
    (hepsilon_pos : 0 < epsilon) (hv : vLow < vHigh)
    (htotalSupply_lt_one : totalSupply < 1)
    (data : ∀ C : ℕ,
      PG24LiteralSourceStableData C noiseLaw eta totalSupply
        (StudentTypeSeq C) (OutcomeSeq C) (GlobalCollegeSeq C) (CutoffSeq C))
    (hsorted :
      ∀ C : ℕ, ∀ i j : Fin (C + 1), (i : ℕ) ≤ (j : ℕ) →
        ((data C).toExtendedCoalitionSourceStableInstance.localCutoff i) ≤
          ((data C).toExtendedCoalitionSourceStableInstance.localCutoff j)) :
    ∀ᶠ C : ℕ in atTop,
      ∀ c ∈ indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C,
        0 < AppliedModelingLib.Probability.upperTailMass noiseLaw
            ((data C).toExtendedCoalitionSourceStableInstance.localCutoff c - vHigh) ∧
          1 - epsilon <
            AppliedModelingLib.Probability.upperTailMass noiseLaw
                ((data C).toExtendedCoalitionSourceStableInstance.localCutoff c - vLow) /
              AppliedModelingLib.Probability.upperTailMass noiseLaw
                ((data C).toExtendedCoalitionSourceStableInstance.localCutoff c - vHigh) := by
  let cutoff : (C : ℕ) → Fin (C + 1) → ℝ :=
    fun C => (data C).toExtendedCoalitionSourceStableInstance.localCutoff
  have hcutoff : ∀ P : ℝ, ∀ᶠ C : ℕ in atTop,
      ∀ c ∈ indexSuffixLarge (epsilonFloorSplitIndex epsilon C) C,
        P < cutoff C c := by
    simpa [cutoff] using
      (theorem2_literalSource_unbounded_cutoffs_eventually
        CutoffSeq noiseLaw eta hlong hepsilon_pos htotalSupply_lt_one data hsorted)
  have htail_pos :
      ∀ᶠ z : ℝ in atTop,
        0 < AppliedModelingLib.Probability.upperTailMass noiseLaw z :=
    hlong.eventually_pos
      (fun z => AppliedModelingLib.Probability.upperTailMass_nonneg noiseLaw z)
  rcases Filter.eventually_atTop.1 htail_pos with ⟨posFloor, hposFloor⟩
  let d : ℝ := vHigh - vLow
  have hd : 0 < d := by
    dsimp [d]
    linarith
  rcases Filter.eventually_atTop.1
      (LongTailedSurvival.eventually_ratio_gt hlong hd hepsilon_pos) with
    ⟨ratioFloor, hratioFloor⟩
  filter_upwards
      [hcutoff (max (posFloor + vHigh) (ratioFloor + vHigh))] with
    C hcutoffC c hc
  have hpos_arg : posFloor ≤ cutoff C c - vHigh := by
    have hfloor := hcutoffC c hc
    have hmax : posFloor + vHigh ≤
        max (posFloor + vHigh) (ratioFloor + vHigh) :=
      le_max_left _ _
    linarith
  have hratio_arg : ratioFloor ≤ cutoff C c - vHigh := by
    have hfloor := hcutoffC c hc
    have hmax : ratioFloor + vHigh ≤
        max (posFloor + vHigh) (ratioFloor + vHigh) :=
      le_max_right _ _
    linarith
  have hpos : 0 < AppliedModelingLib.Probability.upperTailMass noiseLaw
      (cutoff C c - vHigh) :=
    hposFloor _ hpos_arg
  have hratio := hratioFloor (cutoff C c - vHigh) hratio_arg
  have hshift : (cutoff C c - vHigh) + d = cutoff C c - vLow := by
    dsimp [d]
    ring
  rw [hshift] at hratio
  refine ⟨hpos, ?_⟩
  exact hratio

end

end PG24NoisyMatchingMarkets
