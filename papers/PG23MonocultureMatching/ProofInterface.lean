import PG23MonocultureMatching.PaperInterface

/-!
# Proof endpoints for Monoculture in Matching Markets

This module owns the Lean proof endpoints paired with the transparent
source-semantic `Spec` declarations in `PaperInterface.lean`.
-/

namespace PG23MonocultureMatching
namespace PaperInterface

noncomputable section

open AppliedModelingLib
open AppliedModelingLib.Probability
open MeasureTheory
open ProbabilityTheory
open Filter Set
open AppliedModelingLib.Matching
open AL16SupplyDemandMatching
open scoped Topology

universe u v w

private theorem completeLatticeOn_transport
    {α : Type u} {β : Type w}
    {validα : α -> Prop} {validβ : β -> Prop}
    {leα : α -> α -> Prop} {leβ : β -> β -> Prop}
    (f : α -> β) (g : β -> α)
    (hf : ∀ x, validα x -> validβ (f x))
    (hg : ∀ y, validβ y -> validα (g y))
    (hgf : ∀ x, validα x -> g (f x) = x)
    (hfg : ∀ y, validβ y -> f (g y) = y)
    (horder : ∀ {x y}, validα x -> validα y ->
      (leβ (f x) (f y) ↔ leα x y))
    (L : CompleteLatticeOn validβ leβ) :
    CompleteLatticeOn validα leα := by
  refine
    { exists_valid := ?_
      le_refl := ?_
      le_trans := ?_
      le_antisymm := ?_
      sup_exists := ?_
      inf_exists := ?_ }
  · rcases L.exists_valid with ⟨y, hy⟩
    exact ⟨g y, hg y hy⟩
  · intro x hx
    exact (horder hx hx).mp (L.le_refl (hf x hx))
  · intro x y z hx hy hz hxy hyz
    apply (horder hx hz).mp
    exact L.le_trans (hf x hx) (hf y hy) (hf z hz)
      ((horder hx hy).mpr hxy) ((horder hy hz).mpr hyz)
  · intro x y hx hy hxy hyx
    have hfeq : f x = f y :=
      L.le_antisymm (hf x hx) (hf y hy)
        ((horder hx hy).mpr hxy) ((horder hy hx).mpr hyx)
    calc
      x = g (f x) := (hgf x hx).symm
      _ = g (f y) := congrArg g hfeq
      _ = y := hgf y hy
  · intro S hS
    let T : Set β := {y | ∃ x, S x ∧ validα x ∧ y = f x}
    have hT : ∃ y, T y ∧ validβ y := by
      rcases hS with ⟨x, hxS, hx⟩
      exact ⟨f x, ⟨x, hxS, hx, rfl⟩, hf x hx⟩
    rcases L.sup_exists T hT with ⟨y, hy⟩
    have hyvalid : validβ y := hy.1.1
    have hgyvalid : validα (g y) := hg y hyvalid
    refine ⟨g y, ?_⟩
    constructor
    · refine ⟨hgyvalid, ?_⟩
      intro x hxS hx
      apply (horder hx hgyvalid).mp
      rw [hfg y hyvalid]
      exact hy.1.2 (f x) ⟨x, hxS, hx, rfl⟩ (hf x hx)
    · intro z hz
      apply (horder hgyvalid hz.1).mp
      rw [hfg y hyvalid]
      apply hy.2 (f z)
      refine ⟨hf z hz.1, ?_⟩
      intro q hq hqvalid
      rcases hq with ⟨x, hxS, hx, rfl⟩
      exact (horder hx hz.1).mpr (hz.2 x hxS hx)
  · intro S hS
    let T : Set β := {y | ∃ x, S x ∧ validα x ∧ y = f x}
    have hT : ∃ y, T y ∧ validβ y := by
      rcases hS with ⟨x, hxS, hx⟩
      exact ⟨f x, ⟨x, hxS, hx, rfl⟩, hf x hx⟩
    rcases L.inf_exists T hT with ⟨y, hy⟩
    have hyvalid : validβ y := hy.1.1
    have hgyvalid : validα (g y) := hg y hyvalid
    refine ⟨g y, ?_⟩
    constructor
    · refine ⟨hgyvalid, ?_⟩
      intro x hxS hx
      apply (horder hgyvalid hx).mp
      rw [hfg y hyvalid]
      exact hy.1.2 (f x) ⟨x, hxS, hx, rfl⟩ (hf x hx)
    · intro z hz
      apply (horder hz.1 hgyvalid).mp
      rw [hfg y hyvalid]
      apply hy.2 (f z)
      refine ⟨hf z hz.1, ?_⟩
      intro q hq hqvalid
      rcases hq with ⟨x, hxS, hx, rfl⟩
      exact (horder hz.1 hx).mpr (hz.2 x hxS hx)

private theorem rawCutoffSup_isPointwiseLeastUpperBound
    {College : Type v}
    (Z : Set (College -> ℝ)) (hZ : Z.Nonempty)
    (bound : College -> ℝ)
    (hbound : ∀ P : College -> ℝ, Z P -> pg23RawCutoffLe P bound) :
    (∀ P : College -> ℝ, Z P -> pg23RawCutoffLe P (pg23RawCutoffSup Z)) ∧
      ∀ upper : College -> ℝ,
        (∀ P : College -> ℝ, Z P -> pg23RawCutoffLe P upper) ->
          pg23RawCutoffLe (pg23RawCutoffSup Z) upper := by
  constructor
  · intro P hP c
    unfold pg23RawCutoffSup
    apply le_csSup
    · exact ⟨bound c, by
        intro x hx
        rcases hx with ⟨Q, hQ, rfl⟩
        exact hbound Q hQ c⟩
    · exact ⟨P, hP, rfl⟩
  · intro upper hupper c
    unfold pg23RawCutoffSup
    apply csSup_le
    · rcases hZ with ⟨P, hP⟩
      exact ⟨P c, ⟨P, hP, rfl⟩⟩
    · intro x hx
      rcases hx with ⟨P, hP, rfl⟩
      exact hupper P hP c

private theorem rawCutoffInf_isPointwiseGreatestLowerBound
    {College : Type v}
    (Z : Set (College -> ℝ)) (hZ : Z.Nonempty)
    (bound : College -> ℝ)
    (hbound : ∀ P : College -> ℝ, Z P -> pg23RawCutoffLe bound P) :
    (∀ P : College -> ℝ, Z P -> pg23RawCutoffLe (pg23RawCutoffInf Z) P) ∧
      ∀ lower : College -> ℝ,
        (∀ P : College -> ℝ, Z P -> pg23RawCutoffLe lower P) ->
          pg23RawCutoffLe lower (pg23RawCutoffInf Z) := by
  constructor
  · intro P hP c
    unfold pg23RawCutoffInf
    apply csInf_le
    · exact ⟨bound c, by
        intro x hx
        rcases hx with ⟨Q, hQ, rfl⟩
        exact hbound Q hQ c⟩
    · exact ⟨P, hP, rfl⟩
  · intro lower hlower c
    unfold pg23RawCutoffInf
    apply le_csInf
    · rcases hZ with ⟨P, hP⟩
      exact ⟨P c, ⟨P, hP, rfl⟩⟩
    · intro x hx
      rcases hx with ⟨P, hP, rfl⟩
      exact hlower P hP c

variable {College : Type v} [Fintype College] [Nonempty College]

/--
Appendix CDF observation: for any source probability law with connected
support, the lower CDF is strictly increasing on the support interior and lies
in `(0,1)` there; every positive finite power of that lower CDF has the same
properties.  This is the corrected support-interior reading of the printed
`F_V`, `F_X`, and `F_X^n` clauses, without endpoint CDF equalities.

Source status: corrected support-invariant source proposition
Source note: `source_tex/proofs.tex:1-24`.
-/
theorem review_proposition_cdfIncreasing_connectedSupport
    (law : Measure ℝ) [IsProbabilityMeasure law]
    (hconnected : pg23ConnectedSupport law) :
    StrictMonoOn (AppliedModelingLib.Probability.lowerCDFMass law)
        (interior law.support) ∧
      (∀ x ∈ interior law.support,
        AppliedModelingLib.Probability.lowerCDFMass law x ∈ Ioo (0 : ℝ) 1) ∧
      (∀ n : ℕ, 0 < n ->
        StrictMonoOn
            (fun x : ℝ => (AppliedModelingLib.Probability.lowerCDFMass law x) ^ n)
            (interior law.support) ∧
          ∀ x ∈ interior law.support,
            (AppliedModelingLib.Probability.lowerCDFMass law x) ^ n ∈ Ioo (0 : ℝ) 1) := by
  exact ⟨
    pg23_lowerCDFMass_strictMonoOn_interior_support law hconnected,
    (fun x hx =>
      pg23_lowerCDFMass_mem_Ioo_of_mem_interior_support law hconnected hx),
    (fun n hn => ⟨
      pg23_lowerCDFMass_pow_strictMonoOn_interior_support law hconnected hn,
      fun x hx =>
        pg23_lowerCDFMass_pow_mem_Ioo_of_mem_interior_support law hconnected
          hn hx⟩)⟩
/--
Appendix nonzero-measure observation: any open interval meeting the support
interior has positive measure.  This is the version actually used by the
cutoff and Theorem 2 interval arguments.

Source status: corrected support-invariant source proposition
Source note: `source_tex/proofs.tex:26-35`.
-/
theorem review_proposition_nonzeroMeasure_openInterval
    (law : Measure ℝ) [IsProbabilityMeasure law] {a b : ℝ}
    (hintersects : (Ioo a b ∩ interior law.support).Nonempty) :
    0 < law.real (Ioo a b) := by
  exact pg23_openInterval_measureReal_pos_of_intersects_interior_support
    law hintersects
/--
Supply and Demand Lemma for the literal monoculture law.

Source status: direct source theorem with equal capacities
Source note: `source_tex/model.tex:22-42,48-55`.
-/
theorem review_lemma1_supplyDemand_monoculture
    (valueLaw noiseLaw : Measure ℝ)
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
    (S : ℝ) (hS : 0 < S ∧ S < 1) :
    ∀ matching : PG23Matching College,
      pg23SourceStableMatching
          (pg23MonocultureTypeLaw (College := College) valueLaw noiseLaw)
          (fun _ : College => S / (Fintype.card College : ℝ)) matching ↔
        ∃ P : College -> ℝ,
          pg23SourceMarketClearing
              (pg23SourceAggregateDemand
                (pg23MonocultureTypeLaw
                  (College := College) valueLaw noiseLaw))
              (fun _ : College => S / (Fintype.card College : ℝ)) P ∧
            matching = pg23SourceChoice P := by
  simpa [pg23MonocultureSupplyDemandLemmaStatement,
    pg23SupplyDemandLemmaStatement] using
    (pg23MonocultureSupplyDemandLemma_of_primitives
      (College := College) valueLaw noiseLaw S hS)
/--
Supply and Demand Lemma for the literal polyculture law.

Source status: direct source theorem with equal capacities
Source note: `source_tex/model.tex:22-42,57-61`.
-/
theorem review_lemma1_supplyDemand_polyculture
    (valueLaw noiseLaw : Measure ℝ)
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
    (S : ℝ) (hS : 0 < S ∧ S < 1) :
    ∀ matching : PG23Matching College,
      pg23SourceStableMatching
          (pg23PolycultureTypeLaw (College := College) valueLaw noiseLaw)
          (fun _ : College => S / (Fintype.card College : ℝ)) matching ↔
        ∃ P : College -> ℝ,
          pg23SourceMarketClearing
              (pg23SourceAggregateDemand
                (pg23PolycultureTypeLaw
                  (College := College) valueLaw noiseLaw))
              (fun _ : College => S / (Fintype.card College : ℝ)) P ∧
            matching = pg23SourceChoice P := by
  simpa [pg23PolycultureSupplyDemandLemmaStatement,
    pg23SupplyDemandLemmaStatement] using
    (pg23PolycultureSupplyDemandLemma_of_primitives
      (College := College) valueLaw noiseLaw S hS)
/--
Equal Cutoffs Lemma for monoculture: existence, uniqueness among every raw
clearing vector, and common coordinates.

Source status: direct source theorem with explicit score-level nullity
Source note: `source_tex/model.tex:65-75`; `source_tex/proofs.tex:38-123`.
-/
theorem review_lemma2_equalCutoffs_monoculture
    (valueLaw noiseLaw : Measure ℝ)
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
    (hvalue : pg23ConnectedSupport valueLaw)
    (hnoise : pg23ConnectedSupport noiseLaw)
    (hlevel : pg23SourceScoreLevelNull
      (pg23MonocultureTypeLaw (College := College) valueLaw noiseLaw))
    (S : ℝ) (hS : 0 < S ∧ S < 1) :
    ∃ P : College -> ℝ,
      pg23SourceMarketClearing
          (pg23SourceAggregateDemand
            (pg23MonocultureTypeLaw (College := College) valueLaw noiseLaw))
          (fun _ : College => S / (Fintype.card College : ℝ)) P ∧
        (∀ Q : College -> ℝ,
          pg23SourceMarketClearing
              (pg23SourceAggregateDemand
                (pg23MonocultureTypeLaw
                  (College := College) valueLaw noiseLaw))
              (fun _ : College => S / (Fintype.card College : ℝ)) Q ->
            Q = P) ∧
        ∃ p : ℝ, ∀ c : College, P c = p := by
  simpa [pg23MonocultureEqualCutoffsLemmaStatement,
    pg23EqualCutoffsLemmaStatement] using
    (pg23MonocultureEqualCutoffsLemma_of_primitives
      (College := College) valueLaw noiseLaw hvalue hnoise hlevel S hS)
/--
Equal Cutoffs Lemma for polyculture: existence, uniqueness among every raw
clearing vector, and common coordinates.

Source status: direct source theorem with explicit score-level nullity
Source note: `source_tex/model.tex:65-75`; `source_tex/proofs.tex:38-123`.
-/
theorem review_lemma2_equalCutoffs_polyculture
    (valueLaw noiseLaw : Measure ℝ)
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
    (hvalue : pg23ConnectedSupport valueLaw)
    (hnoise : pg23ConnectedSupport noiseLaw)
    (hlevel : pg23SourceScoreLevelNull
      (pg23PolycultureTypeLaw (College := College) valueLaw noiseLaw))
    (S : ℝ) (hS : 0 < S ∧ S < 1) :
    ∃ P : College -> ℝ,
      pg23SourceMarketClearing
          (pg23SourceAggregateDemand
            (pg23PolycultureTypeLaw (College := College) valueLaw noiseLaw))
          (fun _ : College => S / (Fintype.card College : ℝ)) P ∧
        (∀ Q : College -> ℝ,
          pg23SourceMarketClearing
              (pg23SourceAggregateDemand
                (pg23PolycultureTypeLaw
                  (College := College) valueLaw noiseLaw))
              (fun _ : College => S / (Fintype.card College : ℝ)) Q ->
            Q = P) ∧
        ∃ p : ℝ, ∀ c : College, P c = p := by
  simpa [pg23PolycultureEqualCutoffsLemmaStatement,
    pg23EqualCutoffsLemmaStatement] using
    (pg23PolycultureEqualCutoffsLemma_of_primitives
      (College := College) valueLaw noiseLaw hvalue hnoise hlevel S hS)
/--
Probability formula proposition: at the shared cutoff, the monoculture match
probability is the strict tail of the common noise draw, and the polyculture
match probability is the strict tail of the maximum iid noise draw.

Source status: direct source probability formula with visible nonatomic noise
regularity
Source note: `source_tex/model.tex:80-97`; proof dependency
`source_tex/model.tex:76-79`.
-/
theorem review_proposition_probabilityFormula
    {n : ℕ} [NeZero n]
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw] [NoAtoms noiseLaw]
    (ranking : PG23Ranking (Fin n)) (v Pmono Ppoly : ℝ) :
    noiseLaw.real {noise : ℝ |
      ∃ c : Fin n,
        pg23ActiveSourceChoice Finset.univ (fun _ : Fin n => Pmono)
          (pg23MonocultureType v noise ranking) = some c} =
      AppliedModelingLib.Probability.upperTailMass noiseLaw (Pmono - v) ∧
    (Measure.pi (fun _ : Fin n => noiseLaw)).real {noise : Fin n -> ℝ |
      ∃ c : Fin n,
        pg23ActiveSourceChoice Finset.univ (fun _ : Fin n => Ppoly)
          (pg23PolycultureType v ranking noise) = some c} =
      (pg23PolycultureMaxNoiseLaw (College := Fin n) noiseLaw).real
        (Ioi (Ppoly - v)) := by
  exact ⟨
    pg23MonocultureActiveSourceChoice_matchProbability_eq_upperTailMass
      noiseLaw v Pmono ranking,
    pg23PolycultureActiveSourceChoice_matchProbability_eq_maxNoiseTail
      noiseLaw v Ppoly ranking⟩
/--
Corollary 4: with at least two colleges, the monoculture shared cutoff is
strictly below the polyculture shared cutoff.

Source status: corrected support-invariant source theorem
Source note: `source_tex/model.tex:98-104`; `source_tex/proofs.tex:135-166`.
-/
theorem review_corollary4_monocultureCutoff_lt_polycultureCutoff
    {n : ℕ} [NeZero n]
    (valueLaw noiseLaw : Measure ℝ)
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
    (hn : 1 < n)
    (hvalue : pg23ConnectedSupport valueLaw)
    (hnoise : pg23ConnectedSupport noiseLaw)
    (hnoise_nondegenerate :
      ∃ x y : ℝ, x ∈ noiseLaw.support ∧ y ∈ noiseLaw.support ∧ x < y)
    {Pmono Ppoly S : ℝ} (hS : 0 < S ∧ S < 1)
    (hmono_level :
      ∀ c : Fin n, ∀ x : ℝ,
        (pg23MonocultureTypeLaw (College := Fin n) valueLaw noiseLaw)
          {theta | pg23SourceScore theta c = x} = 0)
    (hpoly_level :
      ∀ c : Fin n, ∀ x : ℝ,
        (pg23PolycultureTypeLaw (College := Fin n) valueLaw noiseLaw)
          {theta | pg23SourceScore theta c = x} = 0)
    (hmono_clear : pg23SourceMarketClearing
      (pg23SourceAggregateDemand
        (pg23MonocultureTypeLaw (College := Fin n) valueLaw noiseLaw))
      (fun _ : Fin n => S / (Fintype.card (Fin n) : ℝ))
      (fun _ : Fin n => Pmono))
    (hpoly_clear : pg23SourceMarketClearing
      (pg23SourceAggregateDemand
        (pg23PolycultureTypeLaw (College := Fin n) valueLaw noiseLaw))
      (fun _ : Fin n => S / (Fintype.card (Fin n) : ℝ))
      (fun _ : Fin n => Ppoly)) :
    Pmono < Ppoly := by
  exact pg23Corollary4_monocultureCutoff_lt_polycultureCutoff
    valueLaw noiseLaw hn hvalue hnoise hnoise_nondegenerate hS
    hmono_level hpoly_level hmono_clear hpoly_clear
/--
Theorem 1 probability clauses: both polyculture pointwise limits and
monoculture invariance in the number of colleges.

Source status: corrected source theorem with visible regularity
Source note: `source_tex/results.tex:8-29`; `source_tex/proofs.tex:168-261`.
-/
theorem review_theorem1_probability
    (valueLaw noiseLaw : Measure ℝ)
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
    [NoAtoms valueLaw]
    (hvalue : pg23ConnectedSupport valueLaw)
    (hnoise : pg23ConnectedSupport noiseLaw)
    {monoCutoff polyCutoff : ℕ -> ℝ}
    {vS S : ℝ} (hS : 0 < S ∧ S < 1)
    (htail : AppliedModelingLib.Probability.upperTailMass valueLaw vS = S)
    (hmaximum : pg23MaximumConcentratingNoiseLaw noiseLaw)
    (hmono_level : ∀ n : ℕ, pg23SourceScoreLevelNull
      (pg23MonocultureTypeLaw
        (College := Fin (n + 1)) valueLaw noiseLaw))
    (hpoly_level : ∀ n : ℕ, pg23SourceScoreLevelNull
      (pg23PolycultureTypeLaw
        (College := Fin (n + 1)) valueLaw noiseLaw))
    (hmono_clear : ∀ n : ℕ, pg23SourceMarketClearing
      (pg23SourceAggregateDemand
        (pg23MonocultureTypeLaw
          (College := Fin (n + 1)) valueLaw noiseLaw))
      (fun _ : Fin (n + 1) => S / (Fintype.card (Fin (n + 1)) : ℝ))
      (fun _ : Fin (n + 1) => monoCutoff n))
    (hpoly_clear : ∀ n : ℕ, pg23SourceMarketClearing
      (pg23SourceAggregateDemand
        (pg23PolycultureTypeLaw
          (College := Fin (n + 1)) valueLaw noiseLaw))
      (fun _ : Fin (n + 1) => S / (Fintype.card (Fin (n + 1)) : ℝ))
      (fun _ : Fin (n + 1) => polyCutoff n)) :
    (∀ v : ℝ, v < vS ->
      Tendsto
        (fun n : ℕ => AppliedModelingLib.Matching.cutoffCrossingProbability
          (Measure.pi (fun _ : Fin (n + 1) => noiseLaw)) Finset.univ
          v (fun _ : Fin (n + 1) => polyCutoff n))
        Filter.atTop (nhds 0)) ∧
    (∀ v : ℝ, vS < v ->
      Tendsto
        (fun n : ℕ => AppliedModelingLib.Matching.cutoffCrossingProbability
          (Measure.pi (fun _ : Fin (n + 1) => noiseLaw)) Finset.univ
          v (fun _ : Fin (n + 1) => polyCutoff n))
        Filter.atTop (nhds 1)) ∧
    (∀ v : ℝ, ∀ m n : ℕ,
      AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => noiseLaw))
          v (fun _ : Fin (m + 1) => monoCutoff m) 0 =
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (n + 1) => noiseLaw))
          v (fun _ : Fin (n + 1) => monoCutoff n) 0) := by
  exact pg23Theorem1_probability_of_literal_commonCutoffClearing
    valueLaw noiseLaw hvalue hnoise hS htail hmaximum.2 hmono_level hpoly_level
    hmono_clear hpoly_clear
/--
Theorem 1 welfare clauses: polyculture convergence to efficient upper-tail
welfare, monoculture welfare invariance, and strict monoculture suboptimality.

Source status: corrected source theorem with direct rearrangement proof
Source note: `source_tex/results.tex:10-29`; `source_tex/proofs.tex:254-268`.
-/
theorem review_theorem1_welfare
    (valueLaw noiseLaw : Measure ℝ)
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
    [NoAtoms valueLaw]
    (hvalue : pg23ConnectedSupport valueLaw)
    (hnoise : pg23ConnectedSupport noiseLaw)
    (hnoise_nondegenerate :
      ∃ x y : ℝ, x ∈ noiseLaw.support ∧ y ∈ noiseLaw.support ∧ x < y)
    {monoCutoff polyCutoff : ℕ -> ℝ}
    {vS S : ℝ} (hS : 0 < S ∧ S < 1)
    (htail : AppliedModelingLib.Probability.upperTailMass valueLaw vS = S)
    (hmaximum : pg23MaximumConcentratingNoiseLaw noiseLaw)
    (hmono_level : ∀ n : ℕ, pg23SourceScoreLevelNull
      (pg23MonocultureTypeLaw
        (College := Fin (n + 1)) valueLaw noiseLaw))
    (hpoly_level : ∀ n : ℕ, pg23SourceScoreLevelNull
      (pg23PolycultureTypeLaw
        (College := Fin (n + 1)) valueLaw noiseLaw))
    (hmono_clear : ∀ n : ℕ, pg23SourceMarketClearing
      (pg23SourceAggregateDemand
        (pg23MonocultureTypeLaw
          (College := Fin (n + 1)) valueLaw noiseLaw))
      (fun _ : Fin (n + 1) => S / (Fintype.card (Fin (n + 1)) : ℝ))
      (fun _ : Fin (n + 1) => monoCutoff n))
    (hpoly_clear : ∀ n : ℕ, pg23SourceMarketClearing
      (pg23SourceAggregateDemand
        (pg23PolycultureTypeLaw
          (College := Fin (n + 1)) valueLaw noiseLaw))
      (fun _ : Fin (n + 1) => S / (Fintype.card (Fin (n + 1)) : ℝ))
      (fun _ : Fin (n + 1) => polyCutoff n))
    (habs_integrable : Integrable (fun v : ℝ => |v|) valueLaw) :
    Tendsto
      (fun n : ℕ => ∫ v : ℝ, v *
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (Measure.pi (fun _ : Fin (n + 1) => noiseLaw)) Finset.univ
          v (fun _ : Fin (n + 1) => polyCutoff n) ∂valueLaw)
      Filter.atTop
      (nhds (∫ v : ℝ, v * (if vS < v then (1 : ℝ) else 0) ∂valueLaw)) ∧
    (∀ m n : ℕ,
      (∫ v : ℝ, v *
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (m + 1) => noiseLaw)) v
          (fun _ : Fin (m + 1) => monoCutoff m) 0 ∂valueLaw) =
      ∫ v : ℝ, v *
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin (n + 1) => noiseLaw)) v
          (fun _ : Fin (n + 1) => monoCutoff n) 0 ∂valueLaw) ∧
    (∫ v : ℝ, v *
      AppliedModelingLib.Matching.singleCutoffCrossingProbability
        (Measure.pi (fun _ : Fin 1 => noiseLaw)) v
        (fun _ : Fin 1 => monoCutoff 0) 0 ∂valueLaw) <
      ∫ v : ℝ, v * (if vS < v then (1 : ℝ) else 0) ∂valueLaw := by
  exact pg23Theorem1_welfare_of_literal_commonCutoffClearing
    valueLaw noiseLaw hvalue hnoise hnoise_nondegenerate hS htail hmaximum.2
    hmono_level hpoly_level hmono_clear hpoly_clear habs_integrable
/--
Theorem 2(i): top-choice probability is weakly higher under monoculture and
strictly higher on a positive-mass support-interior region.

Source status: corrected support-invariant source theorem
Source note: `source_tex/results.tex:80-87`; `source_tex/proofs.tex:276-293`.
-/
theorem review_theorem2_part_i_topChoiceProbability
    {n : ℕ} [NeZero n]
    (valueLaw noiseLaw : Measure ℝ)
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
    (hn : 1 < n)
    (hvalue : pg23ConnectedSupport valueLaw)
    (hnoise : pg23ConnectedSupport noiseLaw)
    (hnoise_nondegenerate :
      ∃ x y : ℝ, x ∈ noiseLaw.support ∧ y ∈ noiseLaw.support ∧ x < y)
    {Pmono Ppoly S : ℝ} (hS : 0 < S ∧ S < 1)
    (hmono_level :
      ∀ c : Fin n, ∀ x : ℝ,
        (pg23MonocultureTypeLaw (College := Fin n) valueLaw noiseLaw)
          {theta | pg23SourceScore theta c = x} = 0)
    (hpoly_level :
      ∀ c : Fin n, ∀ x : ℝ,
        (pg23PolycultureTypeLaw (College := Fin n) valueLaw noiseLaw)
          {theta | pg23SourceScore theta c = x} = 0)
    (hmono_clear : pg23SourceMarketClearing
      (pg23SourceAggregateDemand
        (pg23MonocultureTypeLaw (College := Fin n) valueLaw noiseLaw))
      (fun _ : Fin n => S / (Fintype.card (Fin n) : ℝ))
      (fun _ : Fin n => Pmono))
    (hpoly_clear : pg23SourceMarketClearing
      (pg23SourceAggregateDemand
        (pg23PolycultureTypeLaw (College := Fin n) valueLaw noiseLaw))
      (fun _ : Fin n => S / (Fintype.card (Fin n) : ℝ))
      (fun _ : Fin n => Ppoly)) :
    (∀ v : ℝ,
      AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin n => noiseLaw)) v
          (fun _ : Fin n => Ppoly) ⟨0, Nat.zero_lt_of_lt hn⟩ ≤
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin n => noiseLaw)) v
          (fun _ : Fin n => Pmono) ⟨0, Nat.zero_lt_of_lt hn⟩) ∧
    0 < valueLaw (pg23NoiseInteriorCutoffRegion noiseLaw Pmono) ∧
    (∀ v ∈ pg23NoiseInteriorCutoffRegion noiseLaw Pmono,
      AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin n => noiseLaw)) v
          (fun _ : Fin n => Ppoly) ⟨0, Nat.zero_lt_of_lt hn⟩ <
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin n => noiseLaw)) v
          (fun _ : Fin n => Pmono) ⟨0, Nat.zero_lt_of_lt hn⟩) := by
  exact pg23Theorem2_topChoiceProbability_mono_ge_poly
    valueLaw noiseLaw hn hvalue hnoise hnoise_nondegenerate hS
    hmono_level hpoly_level hmono_clear hpoly_clear
/--
Theorem 2(ii): every literal monoculture choice has top rank.  Lean rank `0`
is the paper's one-based rank `1`.

Source status: direct source theorem
Source note: `source_tex/results.tex:88-92`; `source_tex/proofs.tex:296`.
-/
theorem review_theorem2_part_ii_monocultureChoice_rank_eq_zero
    (value noise cutoff : ℝ)
    (rank : College -> Fin (Fintype.card College))
    (hrank : Function.Bijective rank) (c : College)
    (hchoice :
      pg23SourceChoice (fun _ : College => cutoff)
        (pg23MonocultureType value noise
          (Equiv.ofBijective rank hrank)) = some c) :
    pg23SourceRank
        (pg23MonocultureType value noise (Equiv.ofBijective rank hrank)) c = 0 := by
  exact pg23Theorem2_monocultureSourceChoice_rank_eq_zero
    value noise cutoff (Equiv.ofBijective rank hrank) c hchoice
/--
Theorem 2(iii): on a positive-mass set above the efficient threshold where
monoculture matching is not certain, polyculture eventually has strictly
higher match probability.

Source status: corrected support-invariant source theorem
Source note: `source_tex/results.tex:93-99`; `source_tex/proofs.tex:299-325`.
-/
theorem review_theorem2_part_iii_eventualMatchAdvantage
    (valueLaw noiseLaw : Measure ℝ)
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
    [NoAtoms valueLaw]
    (hvalue : IsPreconnected valueLaw.support)
    (hnoise : IsPreconnected noiseLaw.support)
    (hnoise_nondegenerate :
      ∃ x y : ℝ, x ∈ noiseLaw.support ∧ y ∈ noiseLaw.support ∧ x < y)
    {monoCutoff polyCutoff : ℕ -> ℝ}
    {vS S : ℝ} (hS : 0 < S ∧ S < 1)
    (htail : AppliedModelingLib.Probability.upperTailMass valueLaw vS = S)
    (hmaximum : pg23MaximumConcentratingNoiseLaw noiseLaw)
    (hmono_level : ∀ n : ℕ, pg23SourceScoreLevelNull
      (pg23MonocultureTypeLaw
        (College := Fin (n + 1)) valueLaw noiseLaw))
    (hpoly_level : ∀ n : ℕ, pg23SourceScoreLevelNull
      (pg23PolycultureTypeLaw
        (College := Fin (n + 1)) valueLaw noiseLaw))
    (hmono_clear : ∀ n : ℕ, pg23SourceMarketClearing
      (pg23SourceAggregateDemand
        (pg23MonocultureTypeLaw
          (College := Fin (n + 1)) valueLaw noiseLaw))
      (fun _ : Fin (n + 1) => S / (Fintype.card (Fin (n + 1)) : ℝ))
      (fun _ : Fin (n + 1) => monoCutoff n))
    (hpoly_clear : ∀ n : ℕ, pg23SourceMarketClearing
      (pg23SourceAggregateDemand
        (pg23PolycultureTypeLaw
          (College := Fin (n + 1)) valueLaw noiseLaw))
      (fun _ : Fin (n + 1) => S / (Fintype.card (Fin (n + 1)) : ℝ))
      (fun _ : Fin (n + 1) => polyCutoff n)) :
    0 < valueLaw {v : ℝ | vS < v ∧
      AppliedModelingLib.Matching.singleCutoffCrossingProbability
        (Measure.pi (fun _ : Fin 1 => noiseLaw)) v
        (fun _ : Fin 1 => monoCutoff 0) 0 < 1} ∧
    (∀ v : ℝ,
      v ∈ {w : ℝ | vS < w ∧
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
          (Measure.pi (fun _ : Fin 1 => noiseLaw)) w
          (fun _ : Fin 1 => monoCutoff 0) 0 < 1} ->
      ∀ᶠ n : ℕ in Filter.atTop,
        AppliedModelingLib.Matching.singleCutoffCrossingProbability
            (Measure.pi (fun _ : Fin (n + 1) => noiseLaw)) v
            (fun _ : Fin (n + 1) => monoCutoff n) 0 <
          AppliedModelingLib.Matching.cutoffCrossingProbability
            (Measure.pi (fun _ : Fin (n + 1) => noiseLaw)) Finset.univ v
            (fun _ : Fin (n + 1) => polyCutoff n)) := by
  exact pg23Theorem2_eventualMatchAdvantage_on_positiveRegion
    valueLaw noiseLaw hvalue hnoise hnoise_nondegenerate hS htail hmaximum.2
    hmono_level hpoly_level hmono_clear hpoly_clear
/--
Differential-access Equal Cutoffs Lemma, symmetry step: for an equal-capacity
differential law invariant under college relabeling, any explicitly supplied
least and greatest exact-clearing raw cutoffs have common coordinates.

This is not the full existence/uniqueness lemma; the least/greatest premises
are visible because the active-demand model's lattice/existence step remains
separate proof work.

Source status: source proof step with explicit extrema premises
Source note: `source_tex/results.tex:130-151`.
-/
theorem review_lemma_equalCutoffs_differentialAccess_extremaConstant
    {n : ℕ}
    (typeLaw : Measure (PG23DifferentialApplicantType College n))
    (hlaw :
      ∀ sigma : Equiv.Perm College,
        Measure.map (pg23DifferentialRelabelApplicant
          (College := College) (n := n) sigma) typeLaw = typeLaw)
    (S : ℝ) (bot top : College -> ℝ)
    (hbot :
      pg23DifferentialSourceMarketClearing
          (pg23DifferentialSourceAggregateDemand typeLaw)
          (fun _ : College => S / (Fintype.card College : ℝ)) bot ∧
        ∀ P : College -> ℝ,
          pg23DifferentialSourceMarketClearing
            (pg23DifferentialSourceAggregateDemand typeLaw)
            (fun _ : College => S / (Fintype.card College : ℝ)) P ->
          pg23RawCutoffLe bot P)
    (htop :
      pg23DifferentialSourceMarketClearing
          (pg23DifferentialSourceAggregateDemand typeLaw)
          (fun _ : College => S / (Fintype.card College : ℝ)) top ∧
        ∀ P : College -> ℝ,
          pg23DifferentialSourceMarketClearing
            (pg23DifferentialSourceAggregateDemand typeLaw)
            (fun _ : College => S / (Fintype.card College : ℝ)) P ->
          pg23RawCutoffLe P top) :
    (∃ p : ℝ, ∀ c : College, bot c = p) ∧
      ∃ p : ℝ, ∀ c : College, top c = p := by
  have hcapacity :
      ∀ sigma : Equiv.Perm College, ∀ c : College,
        (fun _ : College => S / (Fintype.card College : ℝ)) (sigma c) =
          (fun _ : College => S / (Fintype.card College : ℝ)) c := by
    intro sigma c
    rfl
  exact ⟨
    pg23DifferentialSourceMarketClearing_least_constant_of_typeLaw_relabel
      typeLaw (fun _ : College => S / (Fintype.card College : ℝ))
      hlaw hcapacity bot hbot,
    pg23DifferentialSourceMarketClearing_greatest_constant_of_typeLaw_relabel
      typeLaw (fun _ : College => S / (Fintype.card College : ℝ))
      hlaw hcapacity top htop⟩
/--
Differential-access positive-cutoff continuity: at normalized cutoff vectors
whose coordinates are strictly above the inactive sentinel `0`, aggregate
demand is sequentially continuous under positive score-level nullity.

Source status: proved analytic bridge for the differential-access cutoff proof
Source note: `source_tex/results.tex:130-151`.
-/
theorem review_lemma_equalCutoffs_differentialAccess_positiveDemandContinuity
    {n : ℕ}
    (typeLaw : Measure (PG23DifferentialApplicantType College n))
    [IsProbabilityMeasure typeLaw]
    (hlevel : pg23DifferentialPositiveNormalizedScoreLevelNull typeLaw)
    (Pseq : ℕ -> AL16Cutoff College) (Q : AL16Cutoff College)
    (hQpos : ∀ c : College, 0 < al16CutoffValue Q c)
    (hPQ : al16CoordinatewiseTendsto Pseq Q) :
    ∀ c : College,
      Tendsto
        (fun m => pg23DifferentialNormalizedSourceAggregateDemand typeLaw
          (Pseq m) c)
        atTop
        (nhds (pg23DifferentialNormalizedSourceAggregateDemand typeLaw Q c)) := by
  intro c
  exact pg23DifferentialNormalizedAggregateDemand_tendsto_of_positive_coordinatewiseTendsto
    typeLaw hlevel Pseq Q hQpos hPQ c
/--
Differential-access positive-cutoff continuity for the source product law:
raw score-level nullity of the base PG23 law implies the positive normalized
level-null condition needed by the bounded differential score.
-/
theorem review_lemma_equalCutoffs_differentialAccess_positiveDemandContinuity_of_raw
    {n : ℕ}
    (accessLaw : Measure (Fin n)) [IsProbabilityMeasure accessLaw]
    (baseLaw : Measure (PG23ApplicantType College)) [IsProbabilityMeasure baseLaw]
    (hbase : pg23SourceScoreLevelNull baseLaw)
    (Pseq : ℕ -> AL16Cutoff College) (Q : AL16Cutoff College)
    (hQpos : ∀ c : College, 0 < al16CutoffValue Q c)
    (hPQ : al16CoordinatewiseTendsto Pseq Q) :
    ∀ c : College,
      Tendsto
        (fun m => pg23DifferentialNormalizedSourceAggregateDemand
          (pg23DifferentialTypeLaw (College := College) accessLaw baseLaw)
          (Pseq m) c)
        atTop
        (nhds (pg23DifferentialNormalizedSourceAggregateDemand
          (pg23DifferentialTypeLaw (College := College) accessLaw baseLaw)
          Q c)) := by
  letI : IsProbabilityMeasure
      (pg23DifferentialTypeLaw (College := College) accessLaw baseLaw) :=
    pg23DifferentialTypeLaw_isProbabilityMeasure accessLaw baseLaw
  intro c
  exact pg23DifferentialNormalizedAggregateDemand_tendsto_of_positive_coordinatewiseTendsto
    (pg23DifferentialTypeLaw (College := College) accessLaw baseLaw)
    (pg23DifferentialPositiveNormalizedScoreLevelNull_of_raw accessLaw baseLaw hbase)
    Pseq Q hQpos hPQ c
/--
Differential-access continuity at a product-law clearing cutoff: for equal
capacity `S / |C|` with `S < 1`, positivity of the bounded clearing cutoff is
derived from first-rank mass, so the continuity theorem needs only raw
score-level nullity of the base law.
-/
theorem review_lemma_equalCutoffs_differentialAccess_productClearingContinuity
    {n : ℕ}
    (accessLaw : Measure (Fin n)) [IsProbabilityMeasure accessLaw]
    (baseLaw : Measure (PG23ApplicantType College)) [IsProbabilityMeasure baseLaw]
    (hbase_level : pg23SourceScoreLevelNull baseLaw)
    (htop : ∀ c : College,
      baseLaw.real (pg23TopRankSet c) = 1 / (Fintype.card College : ℝ))
    (S : ℝ) (hSlt : S < 1)
    (Pseq : ℕ -> AL16Cutoff College) (Q : AL16Cutoff College)
    (hQ :
      al16SourceMarketClearing
        (pg23DifferentialNormalizedSourceAggregateDemand
          (pg23DifferentialTypeLaw (College := College) accessLaw baseLaw))
        (fun _ : College => S / (Fintype.card College : ℝ)) Q)
    (hPQ : al16CoordinatewiseTendsto Pseq Q) :
    ∀ c : College,
      Tendsto
        (fun m => pg23DifferentialNormalizedSourceAggregateDemand
          (pg23DifferentialTypeLaw (College := College) accessLaw baseLaw)
          (Pseq m) c)
        atTop
        (nhds (pg23DifferentialNormalizedSourceAggregateDemand
          (pg23DifferentialTypeLaw (College := College) accessLaw baseLaw) Q c)) := by
  intro c
  exact pg23DifferentialNormalizedAggregateDemand_tendsto_at_productClearing_of_raw
    accessLaw baseLaw hbase_level htop S hSlt
    (fun _ : College => S / (Fintype.card College : ℝ))
    (fun _ => rfl) Pseq Q hQ hPQ c
/--
Positive-target closure of differential-access bounded clearing: a
coordinatewise limit of clearing cutoffs is clearing when the limit cutoff is
strictly above the inactive sentinel in every coordinate.
-/
theorem review_lemma_equalCutoffs_differentialAccess_positiveLimitClosure
    {n : ℕ}
    (typeLaw : Measure (PG23DifferentialApplicantType College n))
    [IsProbabilityMeasure typeLaw]
    (hlevel : pg23DifferentialPositiveNormalizedScoreLevelNull typeLaw)
    (capacity : College -> ℝ)
    (Pseq : ℕ -> AL16Cutoff College) (Q : AL16Cutoff College)
    (hQpos : ∀ c : College, 0 < al16CutoffValue Q c)
    (hclear :
      ∀ m : ℕ,
        al16SourceMarketClearing
          (pg23DifferentialNormalizedSourceAggregateDemand typeLaw)
          capacity (Pseq m))
    (hlim : al16CoordinatewiseTendsto Pseq Q) :
    al16SourceMarketClearing
      (pg23DifferentialNormalizedSourceAggregateDemand typeLaw) capacity Q := by
  exact pg23DifferentialNormalizedMarketClearing_of_positive_coordinatewise_limit
    typeLaw hlevel capacity Pseq Q hQpos hclear hlim
/--
Differential-access endpoint repair: under the product law, equal capacity
`S / |C|` with `S < 1` gives a positive coordinatewise lower bound shared by
all bounded normalized clearing cutoffs.
-/
theorem review_lemma_equalCutoffs_differentialAccess_uniformPositiveCutoffLowerBound
    {n : ℕ}
    (accessLaw : Measure (Fin n)) [IsProbabilityMeasure accessLaw]
    (baseLaw : Measure (PG23ApplicantType College)) [IsProbabilityMeasure baseLaw]
    (htop : ∀ c : College,
      baseLaw.real (pg23TopRankSet c) = 1 / (Fintype.card College : ℝ))
    (S : ℝ) (hSlt : S < 1) (c : College) :
    ∃ eps : ℝ, 0 < eps ∧
      ∀ Q : AL16Cutoff College,
        al16SourceMarketClearing
          (pg23DifferentialNormalizedSourceAggregateDemand
            (pg23DifferentialTypeLaw (College := College) accessLaw baseLaw))
          (fun _ : College => S / (Fintype.card College : ℝ)) Q ->
        eps ≤ al16CutoffValue Q c := by
  exact pg23DifferentialNormalizedMarketClearing_cutoff_uniform_pos_of_base
    accessLaw baseLaw htop S hSlt
    (fun _ : College => S / (Fintype.card College : ℝ)) (fun _ => rfl) c
/--
Differential-access product-law closedness: a coordinatewise limit of bounded
normalized clearing cutoffs is clearing.  The positivity needed for continuity
is derived from the lower-bound theorem above.
-/
theorem review_lemma_equalCutoffs_differentialAccess_productLimitClosure
    {n : ℕ}
    (accessLaw : Measure (Fin n)) [IsProbabilityMeasure accessLaw]
    (baseLaw : Measure (PG23ApplicantType College)) [IsProbabilityMeasure baseLaw]
    (hbase_level : pg23SourceScoreLevelNull baseLaw)
    (htop : ∀ c : College,
      baseLaw.real (pg23TopRankSet c) = 1 / (Fintype.card College : ℝ))
    (S : ℝ) (hSlt : S < 1)
    (Pseq : ℕ -> AL16Cutoff College) (Q : AL16Cutoff College)
    (hclear :
      ∀ m : ℕ,
        al16SourceMarketClearing
          (pg23DifferentialNormalizedSourceAggregateDemand
            (pg23DifferentialTypeLaw (College := College) accessLaw baseLaw))
          (fun _ : College => S / (Fintype.card College : ℝ)) (Pseq m))
    (hlim : al16CoordinatewiseTendsto Pseq Q) :
    al16SourceMarketClearing
      (pg23DifferentialNormalizedSourceAggregateDemand
        (pg23DifferentialTypeLaw (College := College) accessLaw baseLaw))
      (fun _ : College => S / (Fintype.card College : ℝ)) Q := by
  exact pg23DifferentialNormalizedMarketClearing_of_product_coordinatewise_limit_of_raw
    accessLaw baseLaw hbase_level htop S hSlt
    (fun _ : College => S / (Fintype.card College : ℝ)) (fun _ => rfl)
    Pseq Q hclear hlim
/--
Differential-access Equal Cutoffs Lemma, bounded product-law lattice step:
raw score-level nullity and first-rank/equal-capacity primitives recover the
A-L complete lattice without assuming global continuity at the sentinel.
-/
theorem review_lemma_equalCutoffs_differentialAccess_productClearingLattice
    {n : ℕ}
    (accessLaw : Measure (Fin n)) [IsProbabilityMeasure accessLaw]
    (baseLaw : Measure (PG23ApplicantType College)) [IsProbabilityMeasure baseLaw]
    (hbase_level : pg23SourceScoreLevelNull baseLaw)
    (htop : ∀ c : College,
      baseLaw.real (pg23TopRankSet c) = 1 / (Fintype.card College : ℝ))
    (S : ℝ) (hSpos : 0 < S) (hSlt : S < 1) :
    CompleteLatticeOn
      (al16SourceMarketClearing
        (pg23DifferentialNormalizedSourceAggregateDemand
          (pg23DifferentialTypeLaw (College := College) accessLaw baseLaw))
        (fun _ : College => S / (Fintype.card College : ℝ)))
      al16CutoffLe := by
  have hnonempty := pg23DifferentialNormalizedMarketClearing_nonempty_of_product_raw
    accessLaw baseLaw hbase_level htop S hSpos hSlt
    (fun _ : College => S / (Fintype.card College : ℝ)) (fun _ => rfl)
  exact pg23DifferentialNormalizedMarketClearing_completeLattice_of_product_raw
    accessLaw baseLaw hbase_level htop S hSlt
    (fun _ : College => S / (Fintype.card College : ℝ)) (fun _ => rfl) hnonempty
/--
Differential-access Equal Cutoffs Lemma, bounded product-law extrema: under the
source capacity range `0 < S < 1`, product-law relabeling symmetry makes the
least and greatest bounded normalized clearing cutoffs coordinate-constant.
-/
theorem review_lemma_equalCutoffs_differentialAccess_productExtrema_from_raw
    {n : ℕ}
    (accessLaw : Measure (Fin n)) [IsProbabilityMeasure accessLaw]
    (baseLaw : Measure (PG23ApplicantType College)) [IsProbabilityMeasure baseLaw]
    (hbase_level : pg23SourceScoreLevelNull baseLaw)
    (htop : ∀ c : College,
      baseLaw.real (pg23TopRankSet c) = 1 / (Fintype.card College : ℝ))
    (hbase_relabel :
      ∀ sigma : Equiv.Perm College,
        Measure.map (pg23RelabelApplicant (College := College) sigma) baseLaw =
          baseLaw)
    (S : ℝ) (hSpos : 0 < S) (hSlt : S < 1) :
    ∃ bot top : AL16Cutoff College,
      al16SourceMarketClearing
          (pg23DifferentialNormalizedSourceAggregateDemand
            (pg23DifferentialTypeLaw (College := College) accessLaw baseLaw))
          (fun _ : College => S / (Fintype.card College : ℝ)) bot ∧
      (∀ Q : AL16Cutoff College,
        al16SourceMarketClearing
          (pg23DifferentialNormalizedSourceAggregateDemand
            (pg23DifferentialTypeLaw (College := College) accessLaw baseLaw))
          (fun _ : College => S / (Fintype.card College : ℝ)) Q ->
        al16CutoffLe bot Q) ∧
      al16SourceMarketClearing
          (pg23DifferentialNormalizedSourceAggregateDemand
            (pg23DifferentialTypeLaw (College := College) accessLaw baseLaw))
          (fun _ : College => S / (Fintype.card College : ℝ)) top ∧
      (∀ Q : AL16Cutoff College,
        al16SourceMarketClearing
          (pg23DifferentialNormalizedSourceAggregateDemand
            (pg23DifferentialTypeLaw (College := College) accessLaw baseLaw))
          (fun _ : College => S / (Fintype.card College : ℝ)) Q ->
        al16CutoffLe Q top) ∧
      (∃ qbot : ℝ, ∀ c : College, al16CutoffValue bot c = qbot) ∧
      (∃ qtop : ℝ, ∀ c : College, al16CutoffValue top c = qtop) := by
  exact pg23DifferentialNormalizedMarketClearing_extremaConstant_of_product_raw
    accessLaw baseLaw hbase_level htop hbase_relabel S hSpos hSlt
    (fun _ : College => S / (Fintype.card College : ℝ)) (fun _ => rfl)
/--
Differential-access Equal Cutoffs Lemma, raw product-law existence step: under
the source capacity range `0 < S < 1`, product-law primitives give a finite raw
exact-clearing cutoff with common coordinates.

This is still weaker than the printed lemma's uniqueness clause; it states the
source-exact shared-cutoff existence part proved by the current lattice bridge.
-/
theorem review_lemma_equalCutoffs_differentialAccess_productRawSharedCutoff_from_raw
    {n : ℕ}
    (accessLaw : Measure (Fin n)) [IsProbabilityMeasure accessLaw]
    (baseLaw : Measure (PG23ApplicantType College)) [IsProbabilityMeasure baseLaw]
    (hbase_level : pg23SourceScoreLevelNull baseLaw)
    (htop : ∀ c : College,
      baseLaw.real (pg23TopRankSet c) = 1 / (Fintype.card College : ℝ))
    (hbase_relabel :
      ∀ sigma : Equiv.Perm College,
        Measure.map (pg23RelabelApplicant (College := College) sigma) baseLaw =
          baseLaw)
    (S : ℝ) (hS : 0 < S ∧ S < 1) :
    ∃ P : College -> ℝ,
      pg23DifferentialSourceMarketClearing
          (pg23DifferentialSourceAggregateDemand
            (pg23DifferentialTypeLaw (College := College) accessLaw baseLaw))
          (fun _ : College => S / (Fintype.card College : ℝ)) P ∧
        ∃ p : ℝ, ∀ c : College, P c = p := by
  exact pg23DifferentialSourceMarketClearing_exists_constant_of_product_raw
    accessLaw baseLaw hbase_level htop hbase_relabel S hS.1 hS.2
    (fun _ : College => S / (Fintype.card College : ℝ)) (fun _ => rfl)
/--
Monoculture instance of the differential-access shared-cutoff existence step.
The visible score-level-null premise is the regularity needed to transport the
bounded normalized witness back to a finite raw cutoff.
-/
theorem review_lemma_equalCutoffs_differentialAccess_monocultureRawSharedCutoff
    {n : ℕ}
    (accessLaw : Measure (Fin n)) [IsProbabilityMeasure accessLaw]
    (valueLaw noiseLaw : Measure ℝ)
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
    (hlevel : pg23SourceScoreLevelNull
      (pg23MonocultureTypeLaw (College := College) valueLaw noiseLaw))
    (S : ℝ) (hS : 0 < S ∧ S < 1) :
    ∃ P : College -> ℝ,
      pg23DifferentialSourceMarketClearing
          (pg23DifferentialSourceAggregateDemand
            (pg23MonocultureDifferentialTypeLaw
              (College := College) accessLaw valueLaw noiseLaw))
          (fun _ : College => S / (Fintype.card College : ℝ)) P ∧
        ∃ p : ℝ, ∀ c : College, P c = p := by
  let baseLaw := pg23MonocultureTypeLaw (College := College) valueLaw noiseLaw
  letI : IsProbabilityMeasure baseLaw :=
    pg23MonocultureTypeLaw_isProbabilityMeasure valueLaw noiseLaw
  simpa [baseLaw, pg23MonocultureDifferentialTypeLaw] using
    (review_lemma_equalCutoffs_differentialAccess_productRawSharedCutoff_from_raw
      (College := College) accessLaw baseLaw hlevel
      (pg23MonocultureTopRankSet_measure_eq_one_div_card valueLaw noiseLaw)
      (fun sigma => pg23MonocultureTypeLaw_relabel sigma valueLaw noiseLaw)
      S hS)
/--
Monoculture half of the differential-access Equal Cutoffs Lemma: finite raw
exact-clearing cutoffs exist, are unique, and have common coordinates.

Source status: direct monoculture instance with explicit connected-support and
score-level-null regularity.
Source note: `source_tex/results.tex:151-155`; `source_tex/proofs.tex:329-365`.
-/
theorem review_lemma_equalCutoffs_differentialAccess_monoculture
    {n : ℕ}
    (accessLaw : Measure (Fin n)) [IsProbabilityMeasure accessLaw]
    (valueLaw noiseLaw : Measure ℝ)
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
    (hvalue : pg23ConnectedSupport valueLaw)
    (hnoise : pg23ConnectedSupport noiseLaw)
    (hlevel : pg23SourceScoreLevelNull
      (pg23MonocultureTypeLaw (College := College) valueLaw noiseLaw))
    (S : ℝ) (hS : 0 < S ∧ S < 1) :
    ∃ P : College -> ℝ,
      pg23DifferentialSourceMarketClearing
          (pg23DifferentialSourceAggregateDemand
            (pg23MonocultureDifferentialTypeLaw
              (College := College) accessLaw valueLaw noiseLaw))
          (fun _ : College => S / (Fintype.card College : ℝ)) P ∧
        (∀ Q : College -> ℝ,
          pg23DifferentialSourceMarketClearing
              (pg23DifferentialSourceAggregateDemand
                (pg23MonocultureDifferentialTypeLaw
                  (College := College) accessLaw valueLaw noiseLaw))
              (fun _ : College => S / (Fintype.card College : ℝ)) Q ->
            Q = P) ∧
        ∃ p : ℝ, ∀ c : College, P c = p := by
  rcases
    review_lemma_equalCutoffs_differentialAccess_monocultureRawSharedCutoff
      (College := College) accessLaw valueLaw noiseLaw hlevel S hS with
    ⟨P, hP, hconstant⟩
  refine ⟨P, hP, ?_, hconstant⟩
  intro Q hQ
  exact pg23MonocultureDifferentialSourceMarketClearing_unique
    accessLaw valueLaw noiseLaw hvalue hnoise hlevel S hS Q P hQ hP
/--
Polyculture instance of the differential-access shared-cutoff existence step.
As above, this proves shared-cutoff existence and does not assert the printed
uniqueness clause.
-/
theorem review_lemma_equalCutoffs_differentialAccess_polycultureRawSharedCutoff
    {n : ℕ}
    (accessLaw : Measure (Fin n)) [IsProbabilityMeasure accessLaw]
    (valueLaw noiseLaw : Measure ℝ)
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
    (hlevel : pg23SourceScoreLevelNull
      (pg23PolycultureTypeLaw (College := College) valueLaw noiseLaw))
    (S : ℝ) (hS : 0 < S ∧ S < 1) :
    ∃ P : College -> ℝ,
      pg23DifferentialSourceMarketClearing
          (pg23DifferentialSourceAggregateDemand
            (pg23PolycultureDifferentialTypeLaw
              (College := College) accessLaw valueLaw noiseLaw))
          (fun _ : College => S / (Fintype.card College : ℝ)) P ∧
        ∃ p : ℝ, ∀ c : College, P c = p := by
  let baseLaw := pg23PolycultureTypeLaw (College := College) valueLaw noiseLaw
  letI : IsProbabilityMeasure baseLaw :=
    pg23PolycultureTypeLaw_isProbabilityMeasure valueLaw noiseLaw
  simpa [baseLaw, pg23PolycultureDifferentialTypeLaw] using
    (review_lemma_equalCutoffs_differentialAccess_productRawSharedCutoff_from_raw
      (College := College) accessLaw baseLaw hlevel
      (pg23PolycultureTopRankSet_measure_eq_one_div_card valueLaw noiseLaw)
      (fun sigma => pg23PolycultureTypeLaw_relabel sigma valueLaw noiseLaw)
      S hS)
/--
Polyculture differential-access Equal Cutoffs Lemma, with the remaining
one-dimensional probability obligation exposed: the common-cutoff matched-mass
event must be the weak upper tail of a connected active-score law.  This is the
source's random top-k active-maximum scalar step.
-/
theorem review_lemma_equalCutoffs_differentialAccess_polyculture_of_matchedTailLaw
    {n : ℕ}
    (accessLaw : Measure (Fin n)) [IsProbabilityMeasure accessLaw]
    (valueLaw noiseLaw : Measure ℝ)
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
    (hlevel : pg23SourceScoreLevelNull
      (pg23PolycultureTypeLaw (College := College) valueLaw noiseLaw))
    (S : ℝ) (hS : 0 < S ∧ S < 1)
    (scoreLaw : Measure ℝ) [IsProbabilityMeasure scoreLaw]
    (hconnected : IsPreconnected scoreLaw.support)
    (htail :
      ∀ p : ℝ,
        scoreLaw.real (Ici p) =
          (pg23PolycultureDifferentialTypeLaw
            (College := College) accessLaw valueLaw noiseLaw).real
            {theta | ∃ c : College,
              pg23DifferentialSourceChoice (fun _ : College => p) theta =
                some c}) :
    ∃ P : College -> ℝ,
      pg23DifferentialSourceMarketClearing
          (pg23DifferentialSourceAggregateDemand
            (pg23PolycultureDifferentialTypeLaw
              (College := College) accessLaw valueLaw noiseLaw))
          (fun _ : College => S / (Fintype.card College : ℝ)) P ∧
        (∀ Q : College -> ℝ,
          pg23DifferentialSourceMarketClearing
              (pg23DifferentialSourceAggregateDemand
                (pg23PolycultureDifferentialTypeLaw
                  (College := College) accessLaw valueLaw noiseLaw))
              (fun _ : College => S / (Fintype.card College : ℝ)) Q ->
            Q = P) ∧
        ∃ p : ℝ, ∀ c : College, P c = p := by
  rcases
    review_lemma_equalCutoffs_differentialAccess_polycultureRawSharedCutoff
      (College := College) accessLaw valueLaw noiseLaw hlevel S hS with
    ⟨P, hP, hconstant⟩
  refine ⟨P, hP, ?_, hconstant⟩
  intro Q hQ
  exact
    pg23PolycultureDifferentialSourceMarketClearing_unique_of_matchedTailLaw
      accessLaw valueLaw noiseLaw hlevel S hS scoreLaw hconnected htail
      Q P hQ hP
/--
Polyculture differential-access Equal Cutoffs Lemma reduced to the concrete
active-maximum connected-support obligation for random top-k applications.
-/
theorem review_lemma_equalCutoffs_differentialAccess_polyculture_of_activeMaxScoreConnected
    {n : ℕ}
    (accessLaw : Measure (Fin n)) [IsProbabilityMeasure accessLaw]
    (valueLaw noiseLaw : Measure ℝ)
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
    (hlevel : pg23SourceScoreLevelNull
      (pg23PolycultureTypeLaw (College := College) valueLaw noiseLaw))
    (S : ℝ) (hS : 0 < S ∧ S < 1)
    (hconnected :
      IsPreconnected
        (pg23DifferentialActiveMaxScoreLaw
          (College := College)
          (pg23PolycultureDifferentialTypeLaw
            (College := College) accessLaw valueLaw noiseLaw)).support) :
    ∃ P : College -> ℝ,
      pg23DifferentialSourceMarketClearing
          (pg23DifferentialSourceAggregateDemand
            (pg23PolycultureDifferentialTypeLaw
              (College := College) accessLaw valueLaw noiseLaw))
          (fun _ : College => S / (Fintype.card College : ℝ)) P ∧
        (∀ Q : College -> ℝ,
          pg23DifferentialSourceMarketClearing
              (pg23DifferentialSourceAggregateDemand
                (pg23PolycultureDifferentialTypeLaw
                  (College := College) accessLaw valueLaw noiseLaw))
              (fun _ : College => S / (Fintype.card College : ℝ)) Q ->
            Q = P) ∧
        ∃ p : ℝ, ∀ c : College, P c = p := by
  rcases
    review_lemma_equalCutoffs_differentialAccess_polycultureRawSharedCutoff
      (College := College) accessLaw valueLaw noiseLaw hlevel S hS with
    ⟨P, hP, hconstant⟩
  refine ⟨P, hP, ?_, hconstant⟩
  intro Q hQ
  exact
    pg23PolycultureDifferentialSourceMarketClearing_unique_of_activeMaxScoreConnected
      accessLaw valueLaw noiseLaw hlevel S hS hconnected Q P hQ hP
/--
Polyculture differential-access Equal Cutoffs Lemma from the source
connected-support primitives.  The random top-k active-maximum scalar step is
proved in `ConcreteAnalysis` by identifying its support with the primitive
`value + noise` sum-law support.
-/
theorem review_lemma_equalCutoffs_differentialAccess_polyculture
    {n : ℕ}
    (accessLaw : Measure (Fin n)) [IsProbabilityMeasure accessLaw]
    (valueLaw noiseLaw : Measure ℝ)
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
    (hvalue : pg23ConnectedSupport valueLaw)
    (hnoise : pg23ConnectedSupport noiseLaw)
    (hlevel : pg23SourceScoreLevelNull
      (pg23PolycultureTypeLaw (College := College) valueLaw noiseLaw))
    (S : ℝ) (hS : 0 < S ∧ S < 1) :
    ∃ P : College -> ℝ,
      pg23DifferentialSourceMarketClearing
          (pg23DifferentialSourceAggregateDemand
            (pg23PolycultureDifferentialTypeLaw
              (College := College) accessLaw valueLaw noiseLaw))
          (fun _ : College => S / (Fintype.card College : ℝ)) P ∧
        (∀ Q : College -> ℝ,
          pg23DifferentialSourceMarketClearing
              (pg23DifferentialSourceAggregateDemand
                (pg23PolycultureDifferentialTypeLaw
                  (College := College) accessLaw valueLaw noiseLaw))
              (fun _ : College => S / (Fintype.card College : ℝ)) Q ->
            Q = P) ∧
        ∃ p : ℝ, ∀ c : College, P c = p := by
  rcases
    review_lemma_equalCutoffs_differentialAccess_polycultureRawSharedCutoff
      (College := College) accessLaw valueLaw noiseLaw hlevel S hS with
    ⟨P, hP, hconstant⟩
  refine ⟨P, hP, ?_, hconstant⟩
  intro Q hQ
  exact
    pg23PolycultureDifferentialSourceMarketClearing_unique
      accessLaw valueLaw noiseLaw hvalue hnoise hlevel S hS Q P hQ hP
/--
Differential-access Nash proposition, finite strategy form.  Equal cutoffs
enter through an iid success-indicator law shared by all colleges; finite
product-law reindexing derives the favorite-success coupling between
deviation-only applications and the missing top-choice applications.  Under
those ex-ante payoff semantics, the top-`k` application set has no profitable
deviation.

Source note: `source_tex/results.tex:159-163`.
-/
theorem review_proposition_nash_differentialApplicationAccess
    [DecidableEq College]
    (k : ℕ) (rank : College -> ℕ) (topChoiceSet : Finset College)
    (successAtom : PMF Bool)
    (outsideUtility : ℝ) (utility : College -> ℝ)
    (feasible : Finset College -> Prop)
    (htopChoiceSet : ∀ c : College, c ∈ topChoiceSet ↔ rank c < k)
    (htop_feasible : feasible topChoiceSet)
    (hfeasible_card :
      ∀ deviation : Finset College,
        feasible deviation ->
          deviation.card = topChoiceSet.card)
    (hrank_utility :
      ∀ c d : College, rank c < rank d ->
        utility d ≤ utility c) :
    NoProfitableApplicationDeviation
      (fun applicationSet =>
        expectedFavoriteSuccessfulApplicationUtility
          (iidEqualCutoffSuccessLaw successAtom applicationSet)
          outsideUtility utility applicationSet)
      topChoiceSet feasible := by
  classical
  have _htop_feasible : feasible topChoiceSet := htop_feasible
  exact
    proposition6_nashEquilibrium_of_iid_equal_cutoff_favorite_success
      (topChoiceSet := topChoiceSet)
      (feasible := feasible)
      (successAtom := successAtom)
      (outsideUtility := outsideUtility)
      (utility := utility)
      hfeasible_card
      (by
        intro c hc d hd
        have hc_rank : rank c < k := (htopChoiceSet c).mp hc
        have hd_rank : ¬ rank d < k := by
          intro hd_rank
          exact hd ((htopChoiceSet d).mpr hd_rank)
        exact hrank_utility c d (lt_of_lt_of_le hc_rank (le_of_not_gt hd_rank)))
/--
Differential-access Equal Cutoffs Lemma, raw product-law uniqueness lift: once
the common-cutoff scalar clearing equation is unique, the A-L lattice and
symmetry bridge make every finite raw exact-clearing vector unique.

The scalar uniqueness premise is the remaining one-dimensional strict-tail
content of the printed proof.
-/
theorem review_lemma_equalCutoffs_differentialAccess_productUnique_from_scalarCommonCutoff
    {n : ℕ}
    (accessLaw : Measure (Fin n)) [IsProbabilityMeasure accessLaw]
    (baseLaw : Measure (PG23ApplicantType College)) [IsProbabilityMeasure baseLaw]
    (hbase_level : pg23SourceScoreLevelNull baseLaw)
    (htop : ∀ c : College,
      baseLaw.real (pg23TopRankSet c) = 1 / (Fintype.card College : ℝ))
    (hbase_relabel :
      ∀ sigma : Equiv.Perm College,
        Measure.map (pg23RelabelApplicant (College := College) sigma) baseLaw =
          baseLaw)
    (S : ℝ) (hS : 0 < S ∧ S < 1)
    (hcommon_unique :
      ∀ p q : ℝ,
        pg23DifferentialSourceMarketClearing
            (pg23DifferentialSourceAggregateDemand
              (pg23DifferentialTypeLaw (College := College) accessLaw baseLaw))
            (fun _ : College => S / (Fintype.card College : ℝ))
            (fun _ : College => p) ->
        pg23DifferentialSourceMarketClearing
            (pg23DifferentialSourceAggregateDemand
              (pg23DifferentialTypeLaw (College := College) accessLaw baseLaw))
            (fun _ : College => S / (Fintype.card College : ℝ))
            (fun _ : College => q) ->
          p = q) :
    ∀ P Q : College -> ℝ,
      pg23DifferentialSourceMarketClearing
          (pg23DifferentialSourceAggregateDemand
            (pg23DifferentialTypeLaw (College := College) accessLaw baseLaw))
          (fun _ : College => S / (Fintype.card College : ℝ)) P ->
      pg23DifferentialSourceMarketClearing
          (pg23DifferentialSourceAggregateDemand
            (pg23DifferentialTypeLaw (College := College) accessLaw baseLaw))
          (fun _ : College => S / (Fintype.card College : ℝ)) Q ->
        P = Q := by
  exact pg23DifferentialSourceMarketClearing_unique_of_product_raw_scalar_unique
    accessLaw baseLaw hbase_level htop hbase_relabel S hS.1 hS.2
    (fun _ : College => S / (Fintype.card College : ℝ)) (fun _ => rfl)
    hcommon_unique
/--
Monoculture differential-access Equal Cutoffs uniqueness, reduced to the
remaining source-to-scalar clearing bridge for common cutoffs.  Connected
primitive supports then give the scalar uniqueness internally.
-/
theorem review_lemma_equalCutoffs_differentialAccess_monocultureUnique_from_scalarClearingBridge
    {n : ℕ}
    (accessLaw : Measure (Fin n)) [IsProbabilityMeasure accessLaw]
    (valueLaw noiseLaw : Measure ℝ)
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
    (hvalue : pg23ConnectedSupport valueLaw)
    (hnoise : pg23ConnectedSupport noiseLaw)
    (hlevel : pg23SourceScoreLevelNull
      (pg23MonocultureTypeLaw (College := College) valueLaw noiseLaw))
    (S : ℝ) (hS : 0 < S ∧ S < 1)
    (hscalar_of_clear :
      ∀ p : ℝ,
        pg23DifferentialSourceMarketClearing
            (pg23DifferentialSourceAggregateDemand
              (pg23MonocultureDifferentialTypeLaw
                (College := College) accessLaw valueLaw noiseLaw))
            (fun _ : College => S / (Fintype.card College : ℝ))
            (fun _ : College => p) ->
          pg23MonocultureScalarMatchDemand valueLaw noiseLaw p = S) :
    ∀ P Q : College -> ℝ,
      pg23DifferentialSourceMarketClearing
          (pg23DifferentialSourceAggregateDemand
            (pg23MonocultureDifferentialTypeLaw
              (College := College) accessLaw valueLaw noiseLaw))
          (fun _ : College => S / (Fintype.card College : ℝ)) P ->
      pg23DifferentialSourceMarketClearing
          (pg23DifferentialSourceAggregateDemand
            (pg23MonocultureDifferentialTypeLaw
              (College := College) accessLaw valueLaw noiseLaw))
          (fun _ : College => S / (Fintype.card College : ℝ)) Q ->
        P = Q :=
  pg23MonocultureDifferentialSourceMarketClearing_unique_of_scalarClearingBridge
    accessLaw valueLaw noiseLaw hvalue hnoise hlevel S hS hscalar_of_clear
/--
Differential-access Equal Cutoffs Lemma, bounded cutoff lattice step: from
explicit normalized demand continuity and a nonempty normalized clearing set,
the A-L lattice gives least and greatest normalized clearing cutoffs, and
relabeling symmetry makes both coordinate-constant.

Source status: source proof step with explicit continuity/nonempty premises
Source note: `source_tex/results.tex:130-151`.
-/
theorem review_lemma_equalCutoffs_differentialAccess_normalizedExtrema_from_lattice
    {n : ℕ}
    (typeLaw : Measure (PG23DifferentialApplicantType College n))
    [IsProbabilityMeasure typeLaw]
    (hlaw :
      ∀ sigma : Equiv.Perm College,
        Measure.map (pg23DifferentialRelabelApplicant
          (College := College) (n := n) sigma) typeLaw = typeLaw)
    (S : ℝ)
    (hdemand_continuous :
      ∀ (Pseq : ℕ -> AL16Cutoff College) (Q : AL16Cutoff College),
        al16CoordinatewiseTendsto Pseq Q ->
          ∀ c : College,
            Tendsto
              (fun m => pg23DifferentialNormalizedSourceAggregateDemand typeLaw
                (Pseq m) c)
              atTop
              (nhds (pg23DifferentialNormalizedSourceAggregateDemand typeLaw Q c)))
    (hnonempty :
      ∃ Q : AL16Cutoff College,
        al16SourceMarketClearing
          (pg23DifferentialNormalizedSourceAggregateDemand typeLaw)
          (fun _ : College => S / (Fintype.card College : ℝ)) Q) :
    ∃ bot top : AL16Cutoff College,
      al16SourceMarketClearing
          (pg23DifferentialNormalizedSourceAggregateDemand typeLaw)
          (fun _ : College => S / (Fintype.card College : ℝ)) bot ∧
      (∀ Q : AL16Cutoff College,
        al16SourceMarketClearing
          (pg23DifferentialNormalizedSourceAggregateDemand typeLaw)
          (fun _ : College => S / (Fintype.card College : ℝ)) Q ->
        al16CutoffLe bot Q) ∧
      al16SourceMarketClearing
          (pg23DifferentialNormalizedSourceAggregateDemand typeLaw)
          (fun _ : College => S / (Fintype.card College : ℝ)) top ∧
      (∀ Q : AL16Cutoff College,
        al16SourceMarketClearing
          (pg23DifferentialNormalizedSourceAggregateDemand typeLaw)
          (fun _ : College => S / (Fintype.card College : ℝ)) Q ->
        al16CutoffLe Q top) ∧
      (∃ qbot : ℝ, ∀ c : College, al16CutoffValue bot c = qbot) ∧
      (∃ qtop : ℝ, ∀ c : College, al16CutoffValue top c = qtop) := by
  have hcapacity :
      ∀ sigma : Equiv.Perm College, ∀ c : College,
        (fun _ : College => S / (Fintype.card College : ℝ)) (sigma c) =
          (fun _ : College => S / (Fintype.card College : ℝ)) c := by
    intro sigma c
    rfl
  exact pg23DifferentialNormalizedMarketClearing_extremaConstant_of_lattice_primitives
    typeLaw (fun _ : College => S / (Fintype.card College : ℝ))
    hlaw hcapacity hdemand_continuous hnonempty

private theorem cutoffWeakCrossingProbability_univ_constant_iidProduct_eq_one_sub_Iio_pow
    {applications : ℕ}
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (v cutoff : ℝ) :
    AppliedModelingLib.Matching.cutoffWeakCrossingProbability
        (Measure.pi (fun _ : Fin applications => noiseLaw)) Finset.univ v
        (fun _ : Fin applications => cutoff) =
      1 - (noiseLaw.real (Iio (cutoff - v))) ^ applications := by
  classical
  let productMeasure : Measure (Fin applications -> ℝ) :=
    Measure.pi (fun _ : Fin applications => noiseLaw)
  haveI : IsProbabilityMeasure productMeasure := by
    dsimp [productMeasure]
    infer_instance
  let crossingSet : Set (Fin applications -> ℝ) :=
    {noise : Fin applications -> ℝ |
      AppliedModelingLib.Matching.cutoffWeaklyCrossedOn Finset.univ
        (AppliedModelingLib.Matching.noisyScore v noise)
        (fun _ : Fin applications => cutoff)}
  let noCrossingSet : Set (Fin applications -> ℝ) :=
    Set.pi Set.univ (fun _ : Fin applications => Iio (cutoff - v))
  have hcompl : crossingSetᶜ = noCrossingSet := by
    ext noise
    constructor
    · intro hno
      change noise ∉ crossingSet at hno
      intro c _hc
      simp only [mem_Iio]
      by_contra hnot_lt
      apply hno
      change AppliedModelingLib.Matching.cutoffWeaklyCrossedOn Finset.univ
        (AppliedModelingLib.Matching.noisyScore v noise)
        (fun _ : Fin applications => cutoff)
      refine ⟨c, Finset.mem_univ c, ?_⟩
      simp only [AppliedModelingLib.Matching.noisyScore]
      linarith
    · intro hno hcross
      change noise ∈ noCrossingSet at hno
      change AppliedModelingLib.Matching.cutoffWeaklyCrossedOn Finset.univ
        (AppliedModelingLib.Matching.noisyScore v noise)
        (fun _ : Fin applications => cutoff) at hcross
      rcases hcross with ⟨c, _hc, hle⟩
      have hlt : noise c < cutoff - v := by
        simpa only [mem_Iio] using hno c (Set.mem_univ c)
      simp only [AppliedModelingLib.Matching.noisyScore] at hle
      linarith
  have hno_meas : MeasurableSet noCrossingSet := by
    dsimp [noCrossingSet]
    exact MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Iio)
  have hcross_meas : MeasurableSet crossingSet := by
    rw [← compl_compl crossingSet, hcompl]
    exact hno_meas.compl
  have hno_real :
      productMeasure.real noCrossingSet =
        (noiseLaw.real (Iio (cutoff - v))) ^ applications := by
    have hmeasure :
        productMeasure noCrossingSet =
          ∏ _ : Fin applications, noiseLaw (Iio (cutoff - v)) := by
      dsimp [productMeasure, noCrossingSet]
      rw [Measure.pi_pi]
    rw [Measure.real, hmeasure, ENNReal.toReal_prod]
    simp [Measure.real, Finset.prod_const]
  have hcompl_real :
      productMeasure.real noCrossingSet =
        1 - productMeasure.real crossingSet := by
    rw [← hcompl]
    exact probReal_compl_eq_one_sub (μ := productMeasure) hcross_meas
  have htarget :
      productMeasure.real crossingSet =
        1 - (noiseLaw.real (Iio (cutoff - v))) ^ applications := by
    linarith
  simpa [AppliedModelingLib.Matching.cutoffWeakCrossingProbability,
    productMeasure, crossingSet] using htarget

private theorem pg23PolycultureActiveSourceChoice_matchProbability_eq_one_sub_Iio_pow
    {applications : ℕ}
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (v cutoff : ℝ) :
    (Measure.pi (fun _ : Fin applications => noiseLaw)).real
        {noise : Fin applications -> ℝ |
          ∃ c : Fin applications,
            pg23ActiveSourceChoice Finset.univ
                (fun _ : Fin applications => cutoff)
                (pg23PolycultureType v
                  (Fintype.equivFin (Fin applications)) noise) = some c} =
      1 - (noiseLaw.real (Iio (cutoff - v))) ^ applications := by
  rw [pg23PolycultureActiveSourceChoice_matchProbability_eq_cutoffWeakCrossingProbability]
  exact
    cutoffWeakCrossingProbability_univ_constant_iidProduct_eq_one_sub_Iio_pow
      noiseLaw v cutoff

private theorem
    pg23MonocultureActiveSourceChoice_matchProbability_eq_weakSingleNoiseEvent
    (noiseLaw : Measure ℝ) (applications : ℕ) (v cutoff : ℝ) :
    noiseLaw.real {noise : ℝ |
        ∃ c : Fin (applications + 1),
          pg23ActiveSourceChoice Finset.univ
              (fun _ : Fin (applications + 1) => cutoff)
              (pg23MonocultureType v noise
                (Fintype.equivFin (Fin (applications + 1)))) = some c} =
      noiseLaw.real {noise : ℝ | cutoff ≤ v + noise} := by
  congr 1
  ext noise
  constructor
  · intro hmatch
    have hweak :=
      (pg23MonocultureActiveSourceChoice_matched_iff_cutoffWeaklyCrossedOn
        v noise (Fintype.equivFin (Fin (applications + 1))) Finset.univ
        (fun _ : Fin (applications + 1) => cutoff)).1 hmatch
    rcases hweak with ⟨c, _hc, hle⟩
    simpa [AppliedModelingLib.Matching.noisyScore] using hle
  · intro hle
    let c : Fin (applications + 1) := ⟨0, Nat.zero_lt_succ applications⟩
    apply
      (pg23MonocultureActiveSourceChoice_matched_iff_cutoffWeaklyCrossedOn
        v noise (Fintype.equivFin (Fin (applications + 1))) Finset.univ
        (fun _ : Fin (applications + 1) => cutoff)).2
    refine ⟨c, Finset.mem_univ c, ?_⟩
    simpa [AppliedModelingLib.Matching.noisyScore] using hle

private theorem measureReal_Iio_mem_Ioo_of_mem_interior_support
    (law : Measure ℝ) [IsProbabilityMeasure law]
    {x : ℝ} (hx : x ∈ interior law.support) :
    law.real (Iio x) ∈ Ioo (0 : ℝ) 1 := by
  have hnhds : interior law.support ∈ 𝓝 x := isOpen_interior.mem_nhds hx
  rcases Metric.mem_nhds_iff.mp hnhds with ⟨delta, hdelta, hball⟩
  let y : ℝ := x - delta / 2
  have hy_ball : y ∈ Metric.ball x delta := by
    rw [Metric.mem_ball, Real.dist_eq]
    dsimp [y]
    rw [abs_of_nonpos]
    · linarith
    · linarith
  have hy_support : y ∈ law.support := interior_subset (hball hy_ball)
  have hy_lt : y < x := by
    dsimp [y]
    linarith
  have hIio_measure_pos : 0 < law (Iio x) :=
    (Measure.mem_support_iff_forall y).mp hy_support (Iio x)
      (Iio_mem_nhds hy_lt)
  have hIio_real_pos : 0 < law.real (Iio x) :=
    ENNReal.toReal_pos hIio_measure_pos.ne' (measure_ne_top law _)
  have hlocal := pg23_twoSidedPositiveIntervalMass_of_mem_interior_support law hx
  have hIci_measure_pos : 0 < law (Ici x) := by
    apply lt_of_lt_of_le (hlocal.right_pos 1 zero_lt_one)
    apply measure_mono
    intro z hz
    exact hz.1.le
  have hIci_real_pos : 0 < law.real (Ici x) :=
    ENNReal.toReal_pos hIci_measure_pos.ne' (measure_ne_top law _)
  have hcompl :=
    probReal_compl_eq_one_sub (μ := law) (s := Iio x) measurableSet_Iio
  have hIci_real : law.real (Ici x) = 1 - law.real (Iio x) := by
    simpa [compl_Iio] using hcompl
  exact ⟨hIio_real_pos, by linarith⟩

/--
Theorem 3: monoculture conditional match probability is access-count
invariant, while polyculture is weakly increasing and strictly increasing on
the noise-support interior.  `k : Fin n` represents `k + 1` applications, so
the source domain `1,...,n` is enforced by the type.

Source status: direct probability theorem for shared cutoffs
Source note: `source_tex/results.tex:174-190`; `source_tex/proofs.tex:367-376`.
-/
theorem review_theorem3_differentialApplicationAccess
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (monoCutoff polyCutoff : ℕ -> ℝ) :
    (∀ (n : ℕ) (k : Fin n) (v : ℝ),
      pg23MonocultureConditionalMatchProbability
          noiseLaw (k.val + 1) v (monoCutoff n) =
        AppliedModelingLib.Probability.upperTailMass noiseLaw (monoCutoff n - v)) ∧
    (∀ (n : ℕ) (k₁ k₂ : Fin n) (v : ℝ),
      pg23MonocultureConditionalMatchProbability
          noiseLaw (k₁.val + 1) v (monoCutoff n) =
        pg23MonocultureConditionalMatchProbability
          noiseLaw (k₂.val + 1) v (monoCutoff n)) ∧
    (∀ (n : ℕ) (k₁ k₂ : Fin n) (v : ℝ), k₁ ≤ k₂ ->
      AppliedModelingLib.Matching.cutoffCrossingProbability
          (Measure.pi (fun _ : Fin (k₁.val + 1) => noiseLaw)) Finset.univ v
          (fun _ : Fin (k₁.val + 1) => polyCutoff n) ≤
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (Measure.pi (fun _ : Fin (k₂.val + 1) => noiseLaw)) Finset.univ v
          (fun _ : Fin (k₂.val + 1) => polyCutoff n)) ∧
    (∀ (n : ℕ) (v : ℝ), polyCutoff n - v ∈ interior noiseLaw.support ->
      ∀ {k₁ k₂ : Fin n}, k₁ < k₂ ->
        AppliedModelingLib.Matching.cutoffCrossingProbability
            (Measure.pi (fun _ : Fin (k₁.val + 1) => noiseLaw)) Finset.univ v
            (fun _ : Fin (k₁.val + 1) => polyCutoff n) <
          AppliedModelingLib.Matching.cutoffCrossingProbability
            (Measure.pi (fun _ : Fin (k₂.val + 1) => noiseLaw)) Finset.univ v
            (fun _ : Fin (k₂.val + 1) => polyCutoff n)) := by
  exact pg23Theorem3_differentialApplicationAccess
    noiseLaw monoCutoff polyCutoff
/--
Theorem 3 with the source proof's monoculture bridge `P_mono,kappa = P_mono`.
The bridge is derived from connected primitive supports, a nonatomic value
law, a finite probability law over application access, baseline scalar
clearing, and the common raw differential monoculture clearing cutoff; the
polyculture part remains the shared-cutoff differential-access probability
comparison.

Source status: direct probability theorem with proved monoculture scalar bridge
under a visible nonatomic value-law regularity strengthening
Source note: `source_tex/results.tex:174-190`; `source_tex/proofs.tex:367-376`.
-/
theorem review_theorem3_differentialApplicationAccess_with_monocultureScalarBridge
    (valueLaw noiseLaw : Measure ℝ)
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
    [NoAtoms valueLaw]
    (hvalue : pg23ConnectedSupport valueLaw)
    (hnoise : pg23ConnectedSupport noiseLaw)
    {n : ℕ} (accessLaw : Measure (Fin n)) [IsProbabilityMeasure accessLaw]
    {Pmono PmonoDiff PpolyDiff S : ℝ} (hS : 0 < S ∧ S < 1)
    (hmono :
      pg23MonocultureScalarMatchDemand valueLaw noiseLaw Pmono = S)
    (hmonoDiff_clear :
      pg23DifferentialSourceMarketClearing
          (pg23DifferentialSourceAggregateDemand
            (pg23MonocultureDifferentialTypeLaw
              (College := College) accessLaw valueLaw noiseLaw))
          (fun _ : College => S / (Fintype.card College : ℝ))
          (fun _ : College => PmonoDiff)) :
    (∀ (k : Fin n) (v : ℝ),
      pg23MonocultureConditionalMatchProbability
          noiseLaw (k.val + 1) v PmonoDiff =
        AppliedModelingLib.Probability.upperTailMass noiseLaw (Pmono - v)) ∧
    (∀ (k₁ k₂ : Fin n) (v : ℝ),
      pg23MonocultureConditionalMatchProbability
          noiseLaw (k₁.val + 1) v PmonoDiff =
        pg23MonocultureConditionalMatchProbability
          noiseLaw (k₂.val + 1) v PmonoDiff) ∧
    (∀ (k₁ k₂ : Fin n) (v : ℝ), k₁ ≤ k₂ ->
      AppliedModelingLib.Matching.cutoffCrossingProbability
          (Measure.pi (fun _ : Fin (k₁.val + 1) => noiseLaw)) Finset.univ v
          (fun _ : Fin (k₁.val + 1) => PpolyDiff) ≤
        AppliedModelingLib.Matching.cutoffCrossingProbability
          (Measure.pi (fun _ : Fin (k₂.val + 1) => noiseLaw)) Finset.univ v
          (fun _ : Fin (k₂.val + 1) => PpolyDiff)) ∧
    (∀ (v : ℝ), PpolyDiff - v ∈ interior noiseLaw.support ->
      ∀ {k₁ k₂ : Fin n}, k₁ < k₂ ->
        AppliedModelingLib.Matching.cutoffCrossingProbability
            (Measure.pi (fun _ : Fin (k₁.val + 1) => noiseLaw)) Finset.univ v
            (fun _ : Fin (k₁.val + 1) => PpolyDiff) <
          AppliedModelingLib.Matching.cutoffCrossingProbability
            (Measure.pi (fun _ : Fin (k₂.val + 1) => noiseLaw)) Finset.univ v
            (fun _ : Fin (k₂.val + 1) => PpolyDiff)) := by
  have hlevel :
      pg23SourceScoreLevelNull
        (pg23MonocultureTypeLaw (College := College) valueLaw noiseLaw) :=
    pg23MonocultureTypeLaw_scoreLevelNull_of_noAtoms_value valueLaw noiseLaw
  exact pg23Theorem3_differentialApplicationAccess_with_accessLawScalarBridge
    valueLaw noiseLaw hvalue hnoise accessLaw hS hmono
    (pg23MonocultureDifferentialSourceMarketClearing_commonCutoff_differentialScalar
      (College := College) accessLaw valueLaw noiseLaw hlevel hmonoDiff_clear)
/-- Checked proof endpoint for the v11 source-item target `review_proposition_cdfIncreasing_connectedSupport`. -/
theorem review_proposition_cdfIncreasing_connectedSupportSpec_proof : review_proposition_cdfIncreasing_connectedSupportSpec := by
  unfold review_proposition_cdfIncreasing_connectedSupportSpec
  exact review_proposition_cdfIncreasing_connectedSupport
/-- Checked proof endpoint for the v11 source-item target `review_proposition_nonzeroMeasure_openInterval`. -/
theorem review_proposition_nonzeroMeasure_openIntervalSpec_proof : review_proposition_nonzeroMeasure_openIntervalSpec := by
  unfold review_proposition_nonzeroMeasure_openIntervalSpec
  exact review_proposition_nonzeroMeasure_openInterval
/-- Checked proof endpoint for the v11 source-item target `review_lemma1_supplyDemand_monoculture`. -/
theorem review_lemma1_supplyDemand_monocultureSpec_proof
    {College : Type v} [Fintype College] [Nonempty College] :
    review_lemma1_supplyDemand_monocultureSpec (College := College) := by
  unfold review_lemma1_supplyDemand_monocultureSpec
  exact review_lemma1_supplyDemand_monoculture (College := College)
/-- Checked proof endpoint for the v11 source-item target `review_lemma1_supplyDemand_polyculture`. -/
theorem review_lemma1_supplyDemand_polycultureSpec_proof
    {College : Type v} [Fintype College] [Nonempty College] :
    review_lemma1_supplyDemand_polycultureSpec (College := College) := by
  unfold review_lemma1_supplyDemand_polycultureSpec
  exact review_lemma1_supplyDemand_polyculture (College := College)
/-- Checked proof endpoint for the v11 source-item target `review_lemma2_equalCutoffs_monoculture`. -/
theorem review_lemma2_equalCutoffs_monocultureSpec_proof
    {College : Type v} [Fintype College] [Nonempty College] :
    review_lemma2_equalCutoffs_monocultureSpec (College := College) := by
  unfold review_lemma2_equalCutoffs_monocultureSpec
  exact review_lemma2_equalCutoffs_monoculture (College := College)
/-- Checked proof endpoint for the v11 source-item target `review_lemma2_equalCutoffs_polyculture`. -/
theorem review_lemma2_equalCutoffs_polycultureSpec_proof
    {College : Type v} [Fintype College] [Nonempty College] :
    review_lemma2_equalCutoffs_polycultureSpec (College := College) := by
  unfold review_lemma2_equalCutoffs_polycultureSpec
  exact review_lemma2_equalCutoffs_polyculture (College := College)
/-- Checked proof endpoint for the v11 source-item target `review_proposition_probabilityFormula`. -/
theorem review_proposition_probabilityFormulaSpec_proof : review_proposition_probabilityFormulaSpec := by
  unfold review_proposition_probabilityFormulaSpec
  exact review_proposition_probabilityFormula
/-- Checked proof endpoint for the v11 source-item target `review_corollary4_monocultureCutoff_lt_polycultureCutoff`. -/
theorem review_corollary4_monocultureCutoff_lt_polycultureCutoffSpec_proof : review_corollary4_monocultureCutoff_lt_polycultureCutoffSpec := by
  unfold review_corollary4_monocultureCutoff_lt_polycultureCutoffSpec
  exact review_corollary4_monocultureCutoff_lt_polycultureCutoff
/-- Checked proof endpoint for the v11 source-item target `review_theorem1_probability`. -/
theorem review_theorem1_probabilitySpec_proof : review_theorem1_probabilitySpec := by
  unfold review_theorem1_probabilitySpec
  exact review_theorem1_probability
/-- Checked proof endpoint for the v11 source-item target `review_theorem1_welfare`. -/
theorem review_theorem1_welfareSpec_proof : review_theorem1_welfareSpec := by
  unfold review_theorem1_welfareSpec
  exact review_theorem1_welfare
/-- Checked proof endpoint for the v11 source-item target `review_theorem2_part_i_topChoiceProbability`. -/
theorem review_theorem2_part_i_topChoiceProbabilitySpec_proof : review_theorem2_part_i_topChoiceProbabilitySpec := by
  unfold review_theorem2_part_i_topChoiceProbabilitySpec
  exact review_theorem2_part_i_topChoiceProbability
/-- Checked proof endpoint for the v11 source-item target `review_theorem2_part_ii_monocultureChoice_rank_eq_zero`. -/
theorem review_theorem2_part_ii_monocultureChoice_rank_eq_zeroSpec_proof
    {College : Type v} [Fintype College] [Nonempty College] :
    review_theorem2_part_ii_monocultureChoice_rank_eq_zeroSpec (College := College) := by
  unfold review_theorem2_part_ii_monocultureChoice_rank_eq_zeroSpec
  exact review_theorem2_part_ii_monocultureChoice_rank_eq_zero (College := College)
/-- Checked proof endpoint for the v11 source-item target `review_theorem2_part_iii_eventualMatchAdvantage`. -/
theorem review_theorem2_part_iii_eventualMatchAdvantageSpec_proof : review_theorem2_part_iii_eventualMatchAdvantageSpec := by
  unfold review_theorem2_part_iii_eventualMatchAdvantageSpec
  exact review_theorem2_part_iii_eventualMatchAdvantage
/-- Checked proof endpoint for the v11 source-item target `review_theorem3_differentialApplicationAccess`. -/
theorem review_theorem3_differentialApplicationAccessSpec_proof :
    review_theorem3_differentialApplicationAccessSpec := by
  unfold review_theorem3_differentialApplicationAccessSpec
  intro College _ _ valueLaw noiseLaw _ _ _ hvalue hnoise n accessLaw _
    Pmono PmonoDiff PpolyDiff S hS hmono hmonoDiff_clear
  have hlevel : pg23SourceScoreLevelNull
      (pg23MonocultureTypeLaw (College := College) valueLaw noiseLaw) :=
    pg23MonocultureTypeLaw_scoreLevelNull_of_noAtoms_value valueLaw noiseLaw
  have hdiff :=
    pg23MonocultureDifferentialSourceMarketClearing_commonCutoff_differentialScalar
      (College := College) accessLaw valueLaw noiseLaw hlevel hmonoDiff_clear
  have hcutoff : PmonoDiff = Pmono :=
    pg23MonocultureDifferentialScalarCutoff_eq_baseline_of_connectedSupport
      valueLaw noiseLaw hvalue hnoise (pg23DifferentialAccessWeights accessLaw)
      (pg23DifferentialAccessWeights_sum_eq_one accessLaw) hS hmono hdiff
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k v
    rw [pg23MonocultureActiveSourceChoice_matchProbability_eq_weakSingleNoiseEvent,
      pg23MonocultureActiveSourceChoice_matchProbability_eq_weakSingleNoiseEvent,
      hcutoff]
  · intro k₁ k₂ v
    rw [
      pg23MonocultureActiveSourceChoice_matchProbability_eq_weakSingleNoiseEvent,
      pg23MonocultureActiveSourceChoice_matchProbability_eq_weakSingleNoiseEvent]
  · intro k₁ k₂ v hk
    rw [
      pg23PolycultureActiveSourceChoice_matchProbability_eq_one_sub_Iio_pow,
      pg23PolycultureActiveSourceChoice_matchProbability_eq_one_sub_Iio_pow]
    have hmass_nonneg : 0 ≤ noiseLaw.real (Iio (PpolyDiff - v)) :=
      measureReal_nonneg
    have hmass_le_one : noiseLaw.real (Iio (PpolyDiff - v)) ≤ 1 :=
      measureReal_le_one
    have hpow :
        (noiseLaw.real (Iio (PpolyDiff - v))) ^ (k₂.val + 1) ≤
          (noiseLaw.real (Iio (PpolyDiff - v))) ^ (k₁.val + 1) :=
      pow_le_pow_of_le_one hmass_nonneg hmass_le_one (Nat.succ_le_succ hk)
    linarith
  · intro v hinterior k₁ k₂ hk
    rw [
      pg23PolycultureActiveSourceChoice_matchProbability_eq_one_sub_Iio_pow,
      pg23PolycultureActiveSourceChoice_matchProbability_eq_one_sub_Iio_pow]
    have hmass := measureReal_Iio_mem_Ioo_of_mem_interior_support
      noiseLaw hinterior
    have hpow :
        (noiseLaw.real (Iio (PpolyDiff - v))) ^ (k₂.val + 1) <
          (noiseLaw.real (Iio (PpolyDiff - v))) ^ (k₁.val + 1) :=
      pow_lt_pow_right_of_lt_one₀ hmass.1 hmass.2 (Nat.succ_lt_succ hk)
    linarith
/-- Checked proof endpoint for the v11 source-item target `review_lemma_equalCutoffs_differentialAccess_monoculture`. -/
theorem review_lemma_equalCutoffs_differentialAccess_monocultureSpec_proof
    {College : Type v} [Fintype College] [Nonempty College] :
    review_lemma_equalCutoffs_differentialAccess_monocultureSpec (College := College) := by
  unfold review_lemma_equalCutoffs_differentialAccess_monocultureSpec
  exact review_lemma_equalCutoffs_differentialAccess_monoculture (College := College)
/-- Checked proof endpoint for the v11 source-item target `review_lemma_equalCutoffs_differentialAccess_polyculture`. -/
theorem review_lemma_equalCutoffs_differentialAccess_polycultureSpec_proof
    {College : Type v} [Fintype College] [Nonempty College] :
    review_lemma_equalCutoffs_differentialAccess_polycultureSpec (College := College) := by
  unfold review_lemma_equalCutoffs_differentialAccess_polycultureSpec
  exact review_lemma_equalCutoffs_differentialAccess_polyculture (College := College)
/-- Checked proof endpoint for the v11 source-item target `review_theorem3_differentialApplicationAccess_with_monocultureScalarBridge`. -/
theorem review_theorem3_differentialApplicationAccess_with_monocultureScalarBridgeSpec_proof
    {College : Type v} [Fintype College] [Nonempty College] :
    review_theorem3_differentialApplicationAccess_with_monocultureScalarBridgeSpec
      (College := College) := by
  unfold review_theorem3_differentialApplicationAccess_with_monocultureScalarBridgeSpec
  exact review_theorem3_differentialApplicationAccess_with_monocultureScalarBridge
    (College := College)
/-- Checked proof endpoint for the v11 source-item target `review_proposition_nash_differentialApplicationAccess`. -/
theorem review_proposition_nash_differentialApplicationAccessSpec_proof :
    review_proposition_nash_differentialApplicationAccessSpec := by
  classical
  intro College _ _
  exact review_proposition_nash_differentialApplicationAccess (College := College)
/-- Checked endpoint for Supply and Demand on the source's general induced type law. -/
theorem review_lemma1_supplyDemandSpec_proof : review_lemma1_supplyDemandSpec := by
  intro College _ _ typeLaw _ S hS
  apply pg23SupplyDemandLemma_of_primitives typeLaw
    (fun _ : College => S / (Fintype.card College : ℝ))
  · intro c
    exact div_pos hS.1 (by exact_mod_cast Fintype.card_pos)
  · have hsum :
        (∑ _c : College, S / (Fintype.card College : ℝ)) = S := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp
    simpa [hsum] using hS.2
/-- Checked endpoint for the two source-model Equal Cutoffs conclusions. -/
theorem review_lemma2_equalCutoffsSpec_proof : review_lemma2_equalCutoffsSpec := by
  intro College _ _
  exact ⟨review_lemma2_equalCutoffs_monocultureSpec_proof (College := College),
    review_lemma2_equalCutoffs_polycultureSpec_proof (College := College)⟩
/-- Checked raw-cutoff realization of the cited general continuum lattice theorem. -/
theorem review_proposition_latticeSpec_proof : review_proposition_latticeSpec := by
  intro College _ _ typeLaw _ hlevel S hSpos hSlt
  let capacity : College -> ℝ :=
    fun _ => S / (Fintype.card College : ℝ)
  have hcapacity_pos : ∀ c : College, 0 < capacity c := by
    intro c
    exact div_pos hSpos (by exact_mod_cast Fintype.card_pos)
  have hcapacity_sum : (∑ c : College, capacity c) = S := by
    simp only [capacity]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  letI : IsProbabilityMeasure (pg23NormalizedTypeLaw typeLaw) :=
    pg23NormalizedTypeLaw_isProbabilityMeasure typeLaw
  have hstrict : al16SourceStrictPreferences (pg23NormalizedTypeLaw typeLaw) :=
    pg23NormalizedTypeLaw_strictPreferences_of_raw typeLaw hlevel
  rcases al16TheoremA1_of_concrete_continuum_primitives
      (pg23NormalizedTypeLaw typeLaw) capacity hcapacity_pos hstrict with
    ⟨hnonempty, hlattice⟩
  have hinterior : ∀ Q : AL16Cutoff College,
      al16SourceMarketClearing
          (al16SourceAggregateDemand (pg23NormalizedTypeLaw typeLaw)) capacity Q ->
        ∀ c : College,
          0 < al16CutoffValue Q c ∧ al16CutoffValue Q c < 1 := by
    intro Q hQ c
    constructor
    · by_contra hnot
      have hzero : al16CutoffValue Q c = 0 :=
        le_antisymm (le_of_not_gt hnot) (Q c).property.1
      have houtside : al16SourceOutsideDemand (pg23NormalizedTypeLaw typeLaw) Q = 0 :=
        al16SourceOutsideDemand_eq_zero_of_cutoff_eq_zero
          (pg23NormalizedTypeLaw typeLaw) hzero
      have hpartition :
          al16SourceOutsideDemand (pg23NormalizedTypeLaw typeLaw) Q +
              ∑ d : College,
                al16SourceAggregateDemand (pg23NormalizedTypeLaw typeLaw) Q d = 1 := by
        simpa [al16SourceOutsideDemand, al16SourceAggregateDemand] using
          (al16UnitMassPartition_of_measure_choice
            (pg23NormalizedTypeLaw typeLaw) al16SourceChoice
            al16SourceChoice_fiber_measurable Q)
      have hsum_le :
          (∑ d : College,
              al16SourceAggregateDemand (pg23NormalizedTypeLaw typeLaw) Q d) ≤
            ∑ d : College, capacity d :=
        Finset.sum_le_sum fun d _ => hQ.1 d
      rw [hcapacity_sum] at hsum_le
      rw [houtside, zero_add] at hpartition
      linarith
    · exact pg23NormalizedMarketClearing_cutoff_lt_one
        typeLaw hlevel capacity hcapacity_pos Q hQ c
  let rawValid : (College -> ℝ) -> Prop :=
    pg23SourceMarketClearing (pg23SourceAggregateDemand typeLaw) capacity
  let normalizedValid : AL16Cutoff College -> Prop :=
    al16SourceMarketClearing
      (al16SourceAggregateDemand (pg23NormalizedTypeLaw typeLaw)) capacity
  have hnormalize : ∀ P, rawValid P -> normalizedValid (pg23NormalizedCutoff P) := by
    intro P hP
    exact pg23NormalizedMarketClearing_of_raw typeLaw capacity P hP
  have hdenormalize : ∀ Q, normalizedValid Q ->
      rawValid (pg23DenormalizedCutoff Q) := by
    intro Q hQ
    exact pg23SourceMarketClearing_of_normalized typeLaw capacity Q
      (hinterior Q hQ) hQ
  have hdenormalize_normalize : ∀ P, rawValid P ->
      pg23DenormalizedCutoff (pg23NormalizedCutoff P) = P := by
    intro P _
    funext c
    exact pg23ScoreDenormalize_normalize (P c)
  have hnormalize_denormalize : ∀ Q, normalizedValid Q ->
      pg23NormalizedCutoff (pg23DenormalizedCutoff Q) = Q := by
    intro Q hQ
    exact pg23NormalizedCutoff_denormalized_eq Q (hinterior Q hQ)
  have horder_all : ∀ {P Q : College -> ℝ},
      (al16CutoffLe (pg23NormalizedCutoff P) (pg23NormalizedCutoff Q) ↔
        pg23RawCutoffLe P Q) := by
    intro P Q
    constructor
    · intro h c
      exact (pg23ScoreNormalize_le_iff (P c) (Q c)).mp (h c)
    · intro h c
      exact (pg23ScoreNormalize_le_iff (P c) (Q c)).mpr (h c)
  have horder : ∀ {P Q}, rawValid P -> rawValid Q ->
      (al16CutoffLe (pg23NormalizedCutoff P) (pg23NormalizedCutoff Q) ↔
        pg23RawCutoffLe P Q) := by
    intro P Q _ _
    exact horder_all
  constructor
  · rcases hnonempty with ⟨Q, hQ⟩
    exact ⟨pg23DenormalizedCutoff Q, hdenormalize Q hQ⟩
  constructor
  · exact completeLatticeOn_transport
      pg23NormalizedCutoff pg23DenormalizedCutoff
      hnormalize hdenormalize hdenormalize_normalize hnormalize_denormalize
      horder hlattice
  constructor
  · intro Z hZ hZclear
    let T : Set (AL16Cutoff College) :=
      fun Q => ∃ P : College -> ℝ, Z P ∧ Q = pg23NormalizedCutoff P
    have hT : T.Nonempty := by
      rcases hZ with ⟨P, hP⟩
      exact ⟨pg23NormalizedCutoff P, P, hP, rfl⟩
    have hTclear : ∀ Q : AL16Cutoff College, T Q -> normalizedValid Q := by
      intro Q hQ
      rcases hQ with ⟨P, hP, rfl⟩
      exact hnormalize P (hZclear P hP)
    let Qsup : AL16Cutoff College := al16PointwiseSup T hT
    have hsup :=
      pg23NormalizedMarketClearing_pointwiseSup
        typeLaw hlevel capacity T hT hTclear
    have hQsup_clear : normalizedValid Qsup := by
      exact hsup.2.1.1
    have hQsup_interior :
        ∀ c : College,
          0 < al16CutoffValue Qsup c ∧ al16CutoffValue Qsup c < 1 :=
      hinterior Qsup hQsup_clear
    let R : College -> ℝ := pg23DenormalizedCutoff Qsup
    have hRclear : rawValid R := hdenormalize Qsup hQsup_clear
    have hnormalize_R : pg23NormalizedCutoff R = Qsup :=
      pg23NormalizedCutoff_denormalized_eq Qsup hQsup_interior
    have hRupper :
        ∀ P : College -> ℝ, Z P -> pg23RawCutoffLe P R := by
      intro P hP
      apply horder_all.mp
      rw [hnormalize_R]
      exact hsup.1.1 (pg23NormalizedCutoff P) ⟨P, hP, rfl⟩
    have hRleast :
        ∀ upper : College -> ℝ,
          (∀ P : College -> ℝ, Z P -> pg23RawCutoffLe P upper) ->
            pg23RawCutoffLe R upper := by
      intro upper hupper
      apply horder_all.mp
      rw [hnormalize_R]
      apply hsup.1.2 (pg23NormalizedCutoff upper)
      intro Q hQ
      rcases hQ with ⟨P, hP, rfl⟩
      exact horder_all.mpr (hupper P hP)
    have hraw := rawCutoffSup_isPointwiseLeastUpperBound Z hZ R hRupper
    have hsup_eq : pg23RawCutoffSup Z = R := by
      funext c
      apply le_antisymm
      · exact hraw.2 R hRupper c
      · exact hRleast (pg23RawCutoffSup Z) hraw.1 c
    rw [hsup_eq]
    constructor
    · exact ⟨hRclear, fun P hP _hPclear => hRupper P hP⟩
    · intro upper hupper
      exact hRleast upper (fun P hP => hupper.2 P hP (hZclear P hP))
  · intro Z hZ hZclear
    let T : Set (AL16Cutoff College) :=
      fun Q => ∃ P : College -> ℝ, Z P ∧ Q = pg23NormalizedCutoff P
    have hT : T.Nonempty := by
      rcases hZ with ⟨P, hP⟩
      exact ⟨pg23NormalizedCutoff P, P, hP, rfl⟩
    have hTclear : ∀ Q : AL16Cutoff College, T Q -> normalizedValid Q := by
      intro Q hQ
      rcases hQ with ⟨P, hP, rfl⟩
      exact hnormalize P (hZclear P hP)
    let Qinf : AL16Cutoff College := al16PointwiseInf T hT
    have hinf :=
      pg23NormalizedMarketClearing_pointwiseInf
        typeLaw hlevel capacity T hT hTclear
    have hQinf_clear : normalizedValid Qinf := by
      exact hinf.2.1.1
    have hQinf_interior :
        ∀ c : College,
          0 < al16CutoffValue Qinf c ∧ al16CutoffValue Qinf c < 1 :=
      hinterior Qinf hQinf_clear
    let R : College -> ℝ := pg23DenormalizedCutoff Qinf
    have hRclear : rawValid R := hdenormalize Qinf hQinf_clear
    have hnormalize_R : pg23NormalizedCutoff R = Qinf :=
      pg23NormalizedCutoff_denormalized_eq Qinf hQinf_interior
    have hRlower :
        ∀ P : College -> ℝ, Z P -> pg23RawCutoffLe R P := by
      intro P hP
      apply horder_all.mp
      rw [hnormalize_R]
      exact hinf.1.1 (pg23NormalizedCutoff P) ⟨P, hP, rfl⟩
    have hRgreatest :
        ∀ lower : College -> ℝ,
          (∀ P : College -> ℝ, Z P -> pg23RawCutoffLe lower P) ->
            pg23RawCutoffLe lower R := by
      intro lower hlower
      apply horder_all.mp
      rw [hnormalize_R]
      apply hinf.1.2 (pg23NormalizedCutoff lower)
      intro Q hQ
      rcases hQ with ⟨P, hP, rfl⟩
      exact horder_all.mpr (hlower P hP)
    have hraw := rawCutoffInf_isPointwiseGreatestLowerBound Z hZ R hRlower
    have hinf_eq : pg23RawCutoffInf Z = R := by
      funext c
      apply le_antisymm
      · exact hRgreatest (pg23RawCutoffInf Z) hraw.1 c
      · exact hraw.2 R hRlower c
    rw [hinf_eq]
    constructor
    · exact ⟨hRclear, fun P hP _hPclear => hRlower P hP⟩
    · intro lower hlower
      exact hRgreatest lower (fun P hP => hlower.2 P hP (hZclear P hP))
/-- Checked three-part Lemma 10 route from literal polyculture market clearing. -/
theorem review_lemma10_threePartSpec_proof : review_lemma10_threePartSpec := by
  intro valueLaw noiseLaw _ _ hvalue polyCutoff vS S hS htail hmaximum hpoly_clear
  rcases hmaximum with ⟨_hfinite, hconc⟩
  let sampleLaw : ∀ n : ℕ, Measure (Fin (n + 1) → ℝ) :=
    fun n => Measure.pi (fun _ : Fin (n + 1) => noiseLaw)
  have hprob : ∀ n, IsProbabilityMeasure (sampleLaw n) := by
    intro n
    dsimp [sampleLaw]
    infer_instance
  have hstrict_right :
      ∀ ε : ℝ, 0 < ε →
        AppliedModelingLib.Probability.upperTailMass valueLaw (vS + ε / 2) < S := by
    intro ε hε
    have hle :
        AppliedModelingLib.Probability.upperTailMass valueLaw (vS + ε / 2) ≤ S := by
      rw [← htail]
      exact AppliedModelingLib.Probability.upperTailMass_antitone valueLaw (by linarith)
    apply lt_of_le_of_ne hle
    intro heq
    have hsame :=
      pg23_cutoff_eq_of_connectedSupport_strictTail_eq
        valueLaw hvalue hS.1 hS.2 heq htail
    linarith
  have hstrict_left :
      ∀ ε : ℝ, 0 < ε →
        S < AppliedModelingLib.Probability.upperTailMass valueLaw (vS - ε / 2) := by
    intro ε hε
    have hle :
        S ≤ AppliedModelingLib.Probability.upperTailMass valueLaw (vS - ε / 2) := by
      rw [← htail]
      exact AppliedModelingLib.Probability.upperTailMass_antitone valueLaw (by linarith)
    apply lt_of_le_of_ne hle
    intro heq
    have hsame :=
      pg23_cutoff_eq_of_connectedSupport_strictTail_eq
        valueLaw hvalue hS.1 hS.2 htail heq.symm
    linarith
  let weakMatch : ℕ → ℝ → ℝ := fun n v =>
    AppliedModelingLib.Matching.cutoffWeakCrossingProbability
      (sampleLaw n) (Finset.univ : Finset (Fin (n + 1))) v
      (fun _ => polyCutoff n)
  have hint : ∀ n, Integrable (weakMatch n) valueLaw := by
    intro n
    letI : IsProbabilityMeasure (sampleLaw n) := hprob n
    have hmono : Monotone (weakMatch n) := by
      intro v w hvw
      unfold weakMatch AppliedModelingLib.Matching.cutoffWeakCrossingProbability
      exact measureReal_mono
        (fun noise hnoise => by
          rcases hnoise with ⟨c, hc, hcross⟩
          refine ⟨c, hc, ?_⟩
          dsimp [AppliedModelingLib.Matching.noisyScore] at hcross ⊢
          linarith)
        (measure_ne_top (sampleLaw n) _)
    refine Integrable.of_bound hmono.measurable.aestronglyMeasurable 1 ?_
    filter_upwards with v
    have hnonneg : 0 ≤ weakMatch n v := by
      simp [weakMatch,
        AppliedModelingLib.Matching.cutoffWeakCrossingProbability]
    have hle : weakMatch n v ≤ 1 := by
      simpa [weakMatch,
        AppliedModelingLib.Matching.cutoffWeakCrossingProbability] using
        (measureReal_le_one
          (μ := sampleLaw n)
          (s := {noise : Fin (n + 1) → ℝ |
            AppliedModelingLib.Matching.cutoffWeaklyCrossedOn Finset.univ
              (AppliedModelingLib.Matching.noisyScore v noise)
              (fun _ => polyCutoff n)}))
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hle
  have hclear : ∀ n, ∫ v, weakMatch n v ∂valueLaw = S := by
    intro n
    letI : IsProbabilityMeasure (sampleLaw n) := hprob n
    letI : IsProbabilityMeasure
        (pg23PolycultureTypeLaw
          (College := Fin (n + 1)) valueLaw noiseLaw) :=
      pg23PolycultureTypeLaw_isProbabilityMeasure valueLaw noiseLaw
    let maxNoiseLaw :=
      pg23PolycultureMaxNoiseLaw (College := Fin (n + 1)) noiseLaw
    letI : IsProbabilityMeasure maxNoiseLaw :=
      pg23PolycultureMaxNoiseLaw_isProbabilityMeasure noiseLaw
    have hweak := pg23SourceMarketClearing_commonCutoff_weakTail_eq_supply
      (pg23PolycultureTypeLaw
        (College := Fin (n + 1)) valueLaw noiseLaw)
      (s := S) (p := polyCutoff n) (by simpa using hpoly_clear n)
    rw [pg23PolycultureSourceMaxScoreLaw_eq_sumMaxNoiseLaw] at hweak
    let event : Set (ℝ × ℝ) := {z | polyCutoff n ≤ z.1 + z.2}
    have hevent : MeasurableSet event := by
      exact measurableSet_le measurable_const (by fun_prop)
    have hproduct : (valueLaw.prod maxNoiseLaw).real event = S := by
      have hmap := map_measureReal_apply
        (μ := valueLaw.prod maxNoiseLaw)
        (f := fun z : ℝ × ℝ => z.1 + z.2)
        (s := Ici (polyCutoff n))
        (by fun_prop : Measurable (fun z : ℝ × ℝ => z.1 + z.2))
        measurableSet_Ici
      have hpreimage :
          (fun z : ℝ × ℝ => z.1 + z.2) ⁻¹' Ici (polyCutoff n) = event := by
        ext z
        rfl
      rw [hpreimage] at hmap
      rw [← hmap]
      exact hweak
    calc
      (∫ v, weakMatch n v ∂valueLaw) =
          ∫ v, maxNoiseLaw.real (Prod.mk v ⁻¹' event) ∂valueLaw := by
        apply integral_congr_ae
        filter_upwards with v
        have hsection : Prod.mk v ⁻¹' event = Ici (polyCutoff n - v) := by
          ext x
          simp only [event, mem_preimage, mem_setOf_eq, mem_Ici]
          constructor <;> intro h <;> linarith
        rw [hsection]
        unfold maxNoiseLaw pg23PolycultureMaxNoiseLaw
        rw [map_measureReal_apply
          (μ := sampleLaw n)
          (f := pg23PolycultureMaxNoise (College := Fin (n + 1)))
          (s := Ici (polyCutoff n - v))
          pg23PolycultureMaxNoise_measurable measurableSet_Ici]
        unfold weakMatch
          AppliedModelingLib.Matching.cutoffWeakCrossingProbability
        congr 1
        ext noise
        simp only [mem_preimage, mem_Ici, pg23PolycultureMaxNoise,
          AppliedModelingLib.Matching.cutoffWeaklyCrossedOn,
          AppliedModelingLib.Matching.noisyScore, Finset.le_sup'_iff,
          Finset.mem_univ, true_and]
        apply exists_congr
        intro c
        constructor <;> intro h <;> linarith
      _ = (valueLaw.prod maxNoiseLaw).real event :=
        pg23_integral_sectionProbability_eq_productProbability
          valueLaw maxNoiseLaw hevent
      _ = S := hproduct
  have hupper_low :
      ∀ eps delta : ℝ, 0 < eps → 0 < delta → delta < 1 →
        ∀ᶠ n : ℕ in atTop,
          ∀ v : ℝ,
            v ≤ polyCutoff n -
                AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
                  sampleLaw n - eps / 2 →
              weakMatch n v ≤ delta := by
    intro eps delta heps hdelta _hdelta_lt_one
    have heps3 : 0 < eps / 3 := by positivity
    have hdev :
        ∀ᶠ n : ℕ in atTop,
          AppliedModelingLib.Probability.topOrderDeviationProbability
            (sampleLaw n)
            (AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n)
            (eps / 3) < delta :=
      hconc (eps / 3) heps3 (isOpen_Iio.mem_nhds hdelta)
    filter_upwards [hdev] with n hn v hv
    letI : IsProbabilityMeasure (sampleLaw n) := hprob n
    have hweak_le_shifted :
        weakMatch n v ≤
          AppliedModelingLib.Matching.cutoffCrossingProbability
            (sampleLaw n) (Finset.univ : Finset (Fin (n + 1)))
            (v + eps / 12) (fun _ => polyCutoff n) := by
      unfold weakMatch
        AppliedModelingLib.Matching.cutoffWeakCrossingProbability
        AppliedModelingLib.Matching.cutoffCrossingProbability
      exact measureReal_mono
        (fun noise hnoise => by
          rcases hnoise with ⟨c, hc, hcross⟩
          refine ⟨c, hc, ?_⟩
          dsimp [AppliedModelingLib.Matching.noisyScore] at hcross ⊢
          linarith)
        (measure_ne_top (sampleLaw n) _)
    have hsep :
        AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n +
            eps / 3 ≤
          polyCutoff n - (v + eps / 12) := by
      linarith
    exact le_of_lt (lt_of_le_of_lt
      (hweak_le_shifted.trans
        (AppliedModelingLib.Matching.cutoffCrossingProbability_univ_constant_le_topOrderDeviationProbability_of_center_add_le
          (sampleLaw n) hsep)) hn)
  have hupper_high :
      ∀ eps delta : ℝ, 0 < eps → 0 < delta → delta < 1 →
        ∀ᶠ n : ℕ in atTop,
          ∀ v : ℝ,
            polyCutoff n -
                AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
                  sampleLaw n - eps / 2 < v →
              weakMatch n v ≤ 1 := by
    intro eps delta heps hdelta hdelta_lt_one
    filter_upwards with n v hv
    letI : IsProbabilityMeasure (sampleLaw n) := hprob n
    simpa [weakMatch,
      AppliedModelingLib.Matching.cutoffWeakCrossingProbability] using
      (measureReal_le_one
        (μ := sampleLaw n)
        (s := {noise : Fin (n + 1) → ℝ |
          AppliedModelingLib.Matching.cutoffWeaklyCrossedOn Finset.univ
            (AppliedModelingLib.Matching.noisyScore v noise)
            (fun _ => polyCutoff n)}))
  have hlower_high :
      ∀ eps delta : ℝ, 0 < eps → 0 < delta → delta < 1 →
        ∀ᶠ n : ℕ in atTop,
          ∀ v : ℝ,
            polyCutoff n -
                AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
                  sampleLaw n + eps / 2 < v →
              1 - delta ≤ weakMatch n v := by
    intro eps delta heps hdelta _hdelta_lt_one
    have heps3 : 0 < eps / 3 := by positivity
    have hdev :
        ∀ᶠ n : ℕ in atTop,
          AppliedModelingLib.Probability.topOrderDeviationProbability
            (sampleLaw n)
            (AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n)
            (eps / 3) < delta :=
      hconc (eps / 3) heps3 (isOpen_Iio.mem_nhds hdelta)
    filter_upwards [hdev] with n hn v hv
    letI : IsProbabilityMeasure (sampleLaw n) := hprob n
    have hstrict_le_weak :
        AppliedModelingLib.Matching.cutoffCrossingProbability
            (sampleLaw n) (Finset.univ : Finset (Fin (n + 1))) v
            (fun _ => polyCutoff n) ≤ weakMatch n v := by
      unfold weakMatch
        AppliedModelingLib.Matching.cutoffWeakCrossingProbability
        AppliedModelingLib.Matching.cutoffCrossingProbability
      exact measureReal_mono
        (fun noise hnoise => by
          rcases hnoise with ⟨c, hc, hcross⟩
          exact ⟨c, hc, le_of_lt hcross⟩)
        (measure_ne_top (sampleLaw n) _)
    have hsep :
        polyCutoff n - v <
          AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n -
            eps / 3 := by
      linarith
    have hfail :=
      AppliedModelingLib.Matching.one_sub_cutoffCrossingProbability_univ_constant_le_topOrderDeviationProbability_of_lt_center_sub
        (sampleLaw n) heps3 hsep
    linarith
  have hlower_low_nonneg :
      ∀ eps delta : ℝ, 0 < eps → 0 < delta → delta < 1 →
        ∀ᶠ n : ℕ in atTop,
          ∀ v : ℝ,
            ¬ polyCutoff n -
                AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
                  sampleLaw n + eps / 2 < v →
              0 ≤ weakMatch n v := by
    intro eps delta heps hdelta hdelta_lt_one
    filter_upwards with n v hv
    simp [weakMatch,
      AppliedModelingLib.Matching.cutoffWeakCrossingProbability]
  have hthreshold :=
    lemma10_threshold_tendsto_of_marketClearing_integral_split_le
      (η := valueLaw) (matchProb := weakMatch)
      (threshold := fun n : ℕ =>
        polyCutoff n -
          AppliedModelingLib.Probability.expectedTopOrderStatisticSeq sampleLaw n)
      (vS := vS) (supply := S)
      hstrict_right hstrict_left hint hclear hupper_low hupper_high
      hlower_high hlower_low_nonneg
  refine ⟨?_, ?_, hthreshold⟩
  · intro eps delta heps hdelta
    let q : ℝ := min (eps / 2) (1 / 2)
    have hq_pos : 0 < q := by
      exact lt_min (by positivity) (by norm_num)
    have hq_lt_one : q < 1 :=
      lt_of_le_of_lt (min_le_right _ _) (by norm_num)
    have hq_lt_eps : q < eps :=
      lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hdistance : 0 < 2 * delta / 3 := by positivity
    have hbound :=
      hupper_low (2 * delta / 3) q hdistance hq_pos hq_lt_one
    filter_upwards [hbound] with n hn
    intro v hv
    have hv' :
        v ≤ polyCutoff n -
            AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
              sampleLaw n - (2 * delta / 3) / 2 := by
      linarith
    exact lt_of_le_of_lt (hn v hv') hq_lt_eps
  · intro eps delta heps hdelta
    let q : ℝ := min (eps / 2) (1 / 2)
    have hq_pos : 0 < q := by
      exact lt_min (by positivity) (by norm_num)
    have hq_lt_one : q < 1 :=
      lt_of_le_of_lt (min_le_right _ _) (by norm_num)
    have hq_lt_eps : q < eps :=
      lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hdistance : 0 < 2 * delta / 3 := by positivity
    have hbound :=
      hlower_high (2 * delta / 3) q hdistance hq_pos hq_lt_one
    filter_upwards [hbound] with n hn
    intro v hv
    have hv' :
        polyCutoff n -
            AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
              sampleLaw n + (2 * delta / 3) / 2 < v := by
      linarith
    exact lt_of_lt_of_le (by linarith : 1 - eps < 1 - q) (hn v hv')
/-!
The selected source statements below use the literal weak affordability event.
The established strict probability route is transported to that event under
nonatomic noise, so no boundary mass is lost at equality.
-/
private theorem
    singleCutoffCrossingProbability_iidProduct_constant_eq_weakSingleNoiseEvent
    {n : ℕ} [NeZero n]
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw] [NoAtoms noiseLaw]
    (v cutoff : ℝ) (c : Fin n) :
    AppliedModelingLib.Matching.singleCutoffCrossingProbability
        (Measure.pi (fun _ : Fin n => noiseLaw)) v
        (fun _ : Fin n => cutoff) c =
      noiseLaw.real {noise : ℝ | cutoff ≤ v + noise} := by
  rw [
    AppliedModelingLib.Matching.singleCutoffCrossingProbability_iidProduct_constant_eq_upperTailMass]
  unfold AppliedModelingLib.Probability.upperTailMass
  have hevent :
      {noise : ℝ | cutoff ≤ v + noise} = Set.Ici (cutoff - v) := by
    ext noise
    simp only [Set.mem_setOf_eq, Set.mem_Ici]
    constructor <;> intro h <;> linarith
  rw [hevent]
  exact MeasureTheory.measureReal_congr
    (MeasureTheory.Ioi_ae_eq_Ici (μ := noiseLaw) (a := cutoff - v))

private theorem
    cutoffCrossingProbability_iidProduct_eq_cutoffWeakCrossingProbability_of_noAtoms
    {n : ℕ} [NeZero n]
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw] [NoAtoms noiseLaw]
    (active : Finset (Fin n)) (v : ℝ) (cutoff : Fin n → ℝ) :
    AppliedModelingLib.Matching.cutoffCrossingProbability
        (Measure.pi (fun _ : Fin n => noiseLaw)) active v cutoff =
      AppliedModelingLib.Matching.cutoffWeakCrossingProbability
        (Measure.pi (fun _ : Fin n => noiseLaw)) active v cutoff := by
  exact
    (AppliedModelingLib.Matching.cutoffWeakCrossingProbability_iidProduct_eq_cutoffCrossingProbability_of_noAtoms
      noiseLaw active v cutoff).symm

/-- Checked endpoint for the complete source Theorem 1 statement. -/
theorem review_theorem1_wisdomSpec_proof : review_theorem1_wisdomSpec := by
  unfold review_theorem1_wisdomSpec
  constructor
  · intro valueLaw noiseLaw _ _ _ _ hvalue hnoise
      monoCutoff polyCutoff vS S hS htail hmaximum
      hmono_level hpoly_level hmono_clear hpoly_clear
    simpa only [
      cutoffCrossingProbability_iidProduct_eq_cutoffWeakCrossingProbability_of_noAtoms,
      singleCutoffCrossingProbability_iidProduct_constant_eq_weakSingleNoiseEvent] using
      (review_theorem1_probability valueLaw noiseLaw hvalue hnoise hS htail
        hmaximum hmono_level hpoly_level hmono_clear hpoly_clear)
  · intro valueLaw noiseLaw _ _ _ _ hvalue hnoise hnoise_nondegenerate
      monoCutoff polyCutoff vS S hS htail hmaximum
      hmono_level hpoly_level hmono_clear hpoly_clear habs_integrable
    simpa only [
      cutoffCrossingProbability_iidProduct_eq_cutoffWeakCrossingProbability_of_noAtoms,
      singleCutoffCrossingProbability_iidProduct_constant_eq_weakSingleNoiseEvent] using
      (review_theorem1_welfare valueLaw noiseLaw hvalue hnoise
        hnoise_nondegenerate hS htail hmaximum hmono_level hpoly_level
        hmono_clear hpoly_clear habs_integrable)
/-- Checked endpoint for the complete source Theorem 2 statement. -/
theorem review_theorem2_topChoiceSpec_proof : review_theorem2_topChoiceSpec := by
  unfold review_theorem2_topChoiceSpec
  refine ⟨?_, ?_, ?_⟩
  · intro n _ valueLaw noiseLaw _ _ _ hn hvalue hnoise
      hnoise_nondegenerate Pmono Ppoly S hS
      hmono_level hpoly_level hmono_clear hpoly_clear
    simpa only [
      singleCutoffCrossingProbability_iidProduct_constant_eq_weakSingleNoiseEvent] using
      (review_theorem2_part_i_topChoiceProbability valueLaw noiseLaw hn
        hvalue hnoise hnoise_nondegenerate hS hmono_level hpoly_level
        hmono_clear hpoly_clear)
  · intro College _ _
    exact review_theorem2_part_ii_monocultureChoice_rank_eq_zeroSpec_proof
      (College := College)
  · intro valueLaw noiseLaw _ _ _ _ hvalue hnoise hnoise_nondegenerate
      monoCutoff polyCutoff vS S hS htail hmaximum
      hmono_level hpoly_level hmono_clear hpoly_clear
    simpa only [
      cutoffCrossingProbability_iidProduct_eq_cutoffWeakCrossingProbability_of_noAtoms,
      singleCutoffCrossingProbability_iidProduct_constant_eq_weakSingleNoiseEvent] using
      (review_theorem2_part_iii_eventualMatchAdvantage valueLaw noiseLaw
        hvalue hnoise hnoise_nondegenerate hS htail hmaximum hmono_level
        hpoly_level hmono_clear hpoly_clear)
/-- Checked endpoint for the complete differential-access Equal Cutoffs Lemma. -/
theorem review_lemma_equalCutoffs_differentialAccessSpec_proof :
    review_lemma_equalCutoffs_differentialAccessSpec := by
  intro College _ _
  exact ⟨review_lemma_equalCutoffs_differentialAccess_monocultureSpec_proof
      (College := College),
    review_lemma_equalCutoffs_differentialAccess_polycultureSpec_proof
      (College := College)⟩

end

end PaperInterface

end PG23MonocultureMatching
/-! ## Current source-ledger proof endpoints -/
