import PG23MonocultureMatching.ConcreteAnalysis
import PG23MonocultureMatching.Assumptions

/-!
# Paper Interface: Monoculture in Matching Markets

This is the compact review surface for the scoped PG23 remediation chain.  It
contains the literal continuum Supply and Demand and Equal Cutoffs lemmas,
Corollary 4, and the direct clauses of Theorems 1--3.  Abstract compatibility
routes remain proof internals in `MainTheorems.lean`.

The source permits unbounded support endpoints.  Accordingly, strict interval
claims use the invariant predicate `P - v ∈ interior law.support`.  The status
and validation report document this interpretation and the additional
nonatomic/score-level-null regularity needed to reconcile weak affordability
with the paper's strict probability formulas.
-/

namespace PG23MonocultureMatching
namespace PaperInterface

open Filter MeasureTheory Set
open AppliedModelingLib.Matching
open AL16SupplyDemandMatching
open scoped Topology

universe v

variable {College : Type v} [Fintype College] [Nonempty College]

/-! ## Appendix support observations -/



/-! ## Continuum cutoff characterization -/





/-! ## Cutoff comparison and Theorem 1 -/





/-! ## Theorem 2 -/




/-! ## Differential application access -/























/-- Transparent v11 source-item target for `review_proposition_cdfIncreasing_connectedSupport`. -/
def review_proposition_cdfIncreasing_connectedSupportSpec : Prop :=
  ∀
    (law : Measure ℝ) [IsProbabilityMeasure law]
    (hconnected : pg23ConnectedSupport law), StrictMonoOn (AppliedModelingLib.Probability.lowerCDFMass law)
        (interior law.support) ∧
      (∀ x ∈ interior law.support,
        AppliedModelingLib.Probability.lowerCDFMass law x ∈ Ioo (0 : ℝ) 1) ∧
      (∀ n : ℕ, 0 < n ->
        StrictMonoOn
            (fun x : ℝ => (AppliedModelingLib.Probability.lowerCDFMass law x) ^ n)
            (interior law.support) ∧
          ∀ x ∈ interior law.support,
            (AppliedModelingLib.Probability.lowerCDFMass law x) ^ n ∈ Ioo (0 : ℝ) 1)


/-- Transparent v11 source-item target for `review_proposition_nonzeroMeasure_openInterval`. -/
def review_proposition_nonzeroMeasure_openIntervalSpec : Prop :=
  ∀
    (law : Measure ℝ) [IsProbabilityMeasure law] {a b : ℝ}
    (hintersects : (Ioo a b ∩ interior law.support).Nonempty), 0 < law.real (Ioo a b)


/-- Transparent v11 source-item target for `review_lemma1_supplyDemand_monoculture`. -/
def review_lemma1_supplyDemand_monocultureSpec : Prop :=
  (∀
    (valueLaw noiseLaw : Measure ℝ)
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
    (S : ℝ) (hS : 0 < S ∧ S < 1), ∀ matching : PG23Matching College,
      pg23SourceStableMatching
          (pg23MonocultureTypeLaw (College := College) valueLaw noiseLaw)
          (fun _ : College => S / (Fintype.card College : ℝ)) matching ↔
        ∃ P : College -> ℝ,
          pg23SourceMarketClearing
              (pg23SourceAggregateDemand
                (pg23MonocultureTypeLaw
                  (College := College) valueLaw noiseLaw))
              (fun _ : College => S / (Fintype.card College : ℝ)) P ∧
            matching = pg23SourceChoice P)


/-- Transparent v11 source-item target for `review_lemma1_supplyDemand_polyculture`. -/
def review_lemma1_supplyDemand_polycultureSpec : Prop :=
  (∀
    (valueLaw noiseLaw : Measure ℝ)
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
    (S : ℝ) (hS : 0 < S ∧ S < 1), ∀ matching : PG23Matching College,
      pg23SourceStableMatching
          (pg23PolycultureTypeLaw (College := College) valueLaw noiseLaw)
          (fun _ : College => S / (Fintype.card College : ℝ)) matching ↔
        ∃ P : College -> ℝ,
          pg23SourceMarketClearing
              (pg23SourceAggregateDemand
                (pg23PolycultureTypeLaw
                  (College := College) valueLaw noiseLaw))
              (fun _ : College => S / (Fintype.card College : ℝ)) P ∧
            matching = pg23SourceChoice P)


/-- Transparent v11 source-item target for `review_lemma2_equalCutoffs_monoculture`. -/
def review_lemma2_equalCutoffs_monocultureSpec : Prop :=
  (∀
    (valueLaw noiseLaw : Measure ℝ)
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
    (hvalue : pg23ConnectedSupport valueLaw)
    (hnoise : pg23ConnectedSupport noiseLaw)
    (hlevel : pg23SourceScoreLevelNull
      (pg23MonocultureTypeLaw (College := College) valueLaw noiseLaw))
    (S : ℝ) (hS : 0 < S ∧ S < 1), ∃ P : College -> ℝ,
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
        ∃ p : ℝ, ∀ c : College, P c = p)


/-- Transparent v11 source-item target for `review_lemma2_equalCutoffs_polyculture`. -/
def review_lemma2_equalCutoffs_polycultureSpec : Prop :=
  (∀
    (valueLaw noiseLaw : Measure ℝ)
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
    (hvalue : pg23ConnectedSupport valueLaw)
    (hnoise : pg23ConnectedSupport noiseLaw)
    (hlevel : pg23SourceScoreLevelNull
      (pg23PolycultureTypeLaw (College := College) valueLaw noiseLaw))
    (S : ℝ) (hS : 0 < S ∧ S < 1), ∃ P : College -> ℝ,
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
        ∃ p : ℝ, ∀ c : College, P c = p)


/-- Transparent v11 source-item target for `review_proposition_probabilityFormula`. -/
def review_proposition_probabilityFormulaSpec : Prop :=
  ∀
    {n : ℕ} [NeZero n]
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw] [NoAtoms noiseLaw]
    (ranking : PG23Ranking (Fin n)) (v Pmono Ppoly : ℝ), noiseLaw.real {noise : ℝ |
      ∃ c : Fin n,
        pg23ActiveSourceChoice Finset.univ (fun _ : Fin n => Pmono)
          (pg23MonocultureType v noise ranking) = some c} =
      AppliedModelingLib.Probability.upperTailMass noiseLaw (Pmono - v) ∧
    (Measure.pi (fun _ : Fin n => noiseLaw)).real {noise : Fin n -> ℝ |
      ∃ c : Fin n,
        pg23ActiveSourceChoice Finset.univ (fun _ : Fin n => Ppoly)
          (pg23PolycultureType v ranking noise) = some c} =
      (pg23PolycultureMaxNoiseLaw (College := Fin n) noiseLaw).real
        (Ioi (Ppoly - v))


/-- Transparent v11 source-item target for `review_corollary4_monocultureCutoff_lt_polycultureCutoff`. -/
def review_corollary4_monocultureCutoff_lt_polycultureCutoffSpec : Prop :=
  ∀
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
      (fun _ : Fin n => Ppoly)), Pmono < Ppoly


/-- Transparent v11 source-item target for `review_theorem1_probability`. -/
def review_theorem1_probabilitySpec : Prop :=
  (∀
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
      (fun _ : Fin (n + 1) => polyCutoff n)), (∀ v : ℝ, v < vS ->
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
          v (fun _ : Fin (n + 1) => monoCutoff n) 0))


/-- Transparent v11 source-item target for `review_theorem1_welfare`. -/
def review_theorem1_welfareSpec : Prop :=
  (∀
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
    (habs_integrable : Integrable (fun v : ℝ => |v|) valueLaw), Tendsto
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
      ∫ v : ℝ, v * (if vS < v then (1 : ℝ) else 0) ∂valueLaw)


/-- Transparent v11 source-item target for `review_theorem2_part_i_topChoiceProbability`. -/
def review_theorem2_part_i_topChoiceProbabilitySpec : Prop :=
  (∀
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
      (fun _ : Fin n => Ppoly)), (∀ v : ℝ,
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
          (fun _ : Fin n => Pmono) ⟨0, Nat.zero_lt_of_lt hn⟩))


/-- Transparent v11 source-item target for `review_theorem2_part_ii_monocultureChoice_rank_eq_zero`. -/
def review_theorem2_part_ii_monocultureChoice_rank_eq_zeroSpec : Prop :=
  (∀
    (value noise cutoff : ℝ)
    (rank : College -> Fin (Fintype.card College))
    (hrank : Function.Bijective rank) (c : College)
    (hchoice :
      pg23SourceChoice (fun _ : College => cutoff)
        (pg23MonocultureType value noise
          (Equiv.ofBijective rank hrank)) = some c), pg23SourceRank
        (pg23MonocultureType value noise (Equiv.ofBijective rank hrank)) c = 0)


/-- Transparent v11 source-item target for `review_theorem2_part_iii_eventualMatchAdvantage`. -/
def review_theorem2_part_iii_eventualMatchAdvantageSpec : Prop :=
  (∀
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
      (fun _ : Fin (n + 1) => polyCutoff n)), 0 < valueLaw {v : ℝ | vS < v ∧
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
            (fun _ : Fin (n + 1) => polyCutoff n)))


/-- Transparent v11 source-item target for `review_theorem3_differentialApplicationAccess`. -/
def review_theorem3_differentialApplicationAccessSpec : Prop :=
  ∀ {College : Type v} [Fintype College] [Nonempty College],
  ∀
    (valueLaw noiseLaw : Measure ℝ)
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
    [NoAtoms valueLaw]
    (hvalue : pg23ConnectedSupport valueLaw)
    (hnoise : pg23ConnectedSupport noiseLaw)
    {n : ℕ} (accessLaw : Measure (Fin n)) [IsProbabilityMeasure accessLaw]
    {Pmono PmonoDiff PpolyDiff S : ℝ} (hS : 0 < S ∧ S < 1)
    (hmono : pg23MonocultureScalarMatchDemand valueLaw noiseLaw Pmono = S)
    (hmonoDiff_clear :
      pg23DifferentialSourceMarketClearing
          (pg23DifferentialSourceAggregateDemand
            (pg23MonocultureDifferentialTypeLaw
              (College := College) accessLaw valueLaw noiseLaw))
          (fun _ : College => S / (Fintype.card College : ℝ))
          (fun _ : College => PmonoDiff)), (∀ (k : Fin n) (v : ℝ),
      noiseLaw.real {noise : ℝ |
        ∃ c : Fin (k.val + 1),
          pg23ActiveSourceChoice Finset.univ
              (fun _ : Fin (k.val + 1) => PmonoDiff)
              (pg23MonocultureType v noise
                (Fintype.equivFin (Fin (k.val + 1)))) = some c} =
        noiseLaw.real {noise : ℝ |
          ∃ c : Fin 1,
            pg23ActiveSourceChoice Finset.univ (fun _ : Fin 1 => Pmono)
              (pg23MonocultureType v noise (Fintype.equivFin (Fin 1))) = some c}) ∧
    (∀ (k₁ k₂ : Fin n) (v : ℝ),
      noiseLaw.real {noise : ℝ |
        ∃ c : Fin (k₁.val + 1),
          pg23ActiveSourceChoice Finset.univ
              (fun _ : Fin (k₁.val + 1) => PmonoDiff)
              (pg23MonocultureType v noise
                (Fintype.equivFin (Fin (k₁.val + 1)))) = some c} =
        noiseLaw.real {noise : ℝ |
          ∃ c : Fin (k₂.val + 1),
            pg23ActiveSourceChoice Finset.univ
                (fun _ : Fin (k₂.val + 1) => PmonoDiff)
                (pg23MonocultureType v noise
                  (Fintype.equivFin (Fin (k₂.val + 1)))) = some c}) ∧
    (∀ (k₁ k₂ : Fin n) (v : ℝ), k₁ ≤ k₂ ->
      (Measure.pi (fun _ : Fin (k₁.val + 1) => noiseLaw)).real
          {noise : Fin (k₁.val + 1) -> ℝ |
            ∃ c : Fin (k₁.val + 1),
              pg23ActiveSourceChoice Finset.univ
                  (fun _ : Fin (k₁.val + 1) => PpolyDiff)
                  (pg23PolycultureType v
                    (Fintype.equivFin (Fin (k₁.val + 1))) noise) = some c} ≤
        (Measure.pi (fun _ : Fin (k₂.val + 1) => noiseLaw)).real
          {noise : Fin (k₂.val + 1) -> ℝ |
            ∃ c : Fin (k₂.val + 1),
              pg23ActiveSourceChoice Finset.univ
                  (fun _ : Fin (k₂.val + 1) => PpolyDiff)
                  (pg23PolycultureType v
                    (Fintype.equivFin (Fin (k₂.val + 1))) noise) = some c}) ∧
    (∀ (v : ℝ), PpolyDiff - v ∈ interior noiseLaw.support ->
      ∀ {k₁ k₂ : Fin n}, k₁ < k₂ ->
        (Measure.pi (fun _ : Fin (k₁.val + 1) => noiseLaw)).real
            {noise : Fin (k₁.val + 1) -> ℝ |
              ∃ c : Fin (k₁.val + 1),
                pg23ActiveSourceChoice Finset.univ
                    (fun _ : Fin (k₁.val + 1) => PpolyDiff)
                    (pg23PolycultureType v
                      (Fintype.equivFin (Fin (k₁.val + 1))) noise) = some c} <
          (Measure.pi (fun _ : Fin (k₂.val + 1) => noiseLaw)).real
            {noise : Fin (k₂.val + 1) -> ℝ |
              ∃ c : Fin (k₂.val + 1),
                pg23ActiveSourceChoice Finset.univ
                    (fun _ : Fin (k₂.val + 1) => PpolyDiff)
                    (pg23PolycultureType v
                      (Fintype.equivFin (Fin (k₂.val + 1))) noise) = some c})


/-- Transparent v11 source-item target for `review_lemma_equalCutoffs_differentialAccess_monoculture`. -/
def review_lemma_equalCutoffs_differentialAccess_monocultureSpec : Prop :=
  (∀
    {n : ℕ}
    (accessLaw : Measure (Fin n)) [IsProbabilityMeasure accessLaw]
    (valueLaw noiseLaw : Measure ℝ)
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
    (hvalue : pg23ConnectedSupport valueLaw)
    (hnoise : pg23ConnectedSupport noiseLaw)
    (hlevel : pg23SourceScoreLevelNull
      (pg23MonocultureTypeLaw (College := College) valueLaw noiseLaw))
    (S : ℝ) (hS : 0 < S ∧ S < 1), ∃ P : College -> ℝ,
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
        ∃ p : ℝ, ∀ c : College, P c = p)


/-- Transparent v11 source-item target for `review_lemma_equalCutoffs_differentialAccess_polyculture`. -/
def review_lemma_equalCutoffs_differentialAccess_polycultureSpec : Prop :=
  (∀
    {n : ℕ}
    (accessLaw : Measure (Fin n)) [IsProbabilityMeasure accessLaw]
    (valueLaw noiseLaw : Measure ℝ)
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
    (hvalue : pg23ConnectedSupport valueLaw)
    (hnoise : pg23ConnectedSupport noiseLaw)
    (hlevel : pg23SourceScoreLevelNull
      (pg23PolycultureTypeLaw (College := College) valueLaw noiseLaw))
    (S : ℝ) (hS : 0 < S ∧ S < 1), ∃ P : College -> ℝ,
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
        ∃ p : ℝ, ∀ c : College, P c = p)


/-- Transparent v11 source-item target for `review_theorem3_differentialApplicationAccess_with_monocultureScalarBridge`. -/
def review_theorem3_differentialApplicationAccess_with_monocultureScalarBridgeSpec : Prop :=
  (∀
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
          (fun _ : College => PmonoDiff)), (∀ (k : Fin n) (v : ℝ),
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
            (fun _ : Fin (k₂.val + 1) => PpolyDiff)))


/-- Transparent v11 source-item target for `review_proposition_nash_differentialApplicationAccess`. -/
def review_proposition_nash_differentialApplicationAccessSpec : Prop := by
  classical
  exact ∀ {College : Type v} [Fintype College] [Nonempty College],
    ∀
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
          utility d ≤ utility c), NoProfitableApplicationDeviation
        (fun applicationSet =>
          expectedFavoriteSuccessfulApplicationUtility
            (iidEqualCutoffSuccessLaw successAtom applicationSet)
            outsideUtility utility applicationSet)
        topChoiceSet feasible


/-- The source Supply and Demand Lemma on the general induced type law. -/
def review_lemma1_supplyDemandSpec : Prop :=
  ∀ {College : Type v} [Fintype College] [Nonempty College],
    ∀
      (typeLaw : Measure (PG23ApplicantType College))
      [IsProbabilityMeasure typeLaw]
      (S : ℝ) (hS : 0 < S ∧ S < 1), ∀ matching : PG23Matching College,
        pg23SourceStableMatching typeLaw
            (fun _ : College => S / (Fintype.card College : ℝ)) matching ↔
          ∃ P : College -> ℝ,
            pg23SourceMarketClearing
                (pg23SourceAggregateDemand typeLaw)
                (fun _ : College => S / (Fintype.card College : ℝ)) P ∧
              matching = pg23SourceChoice P

/-- The source Equal Cutoffs Lemma specialized to monoculture and polyculture. -/
def review_lemma2_equalCutoffsSpec : Prop :=
  ∀ {College : Type v} [Fintype College] [Nonempty College],
    (∀
        (valueLaw noiseLaw : Measure ℝ)
        [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
        (hvalue : pg23ConnectedSupport valueLaw)
        (hnoise : pg23ConnectedSupport noiseLaw)
        (hlevel : pg23SourceScoreLevelNull
          (pg23MonocultureTypeLaw (College := College) valueLaw noiseLaw))
        (S : ℝ) (hS : 0 < S ∧ S < 1), ∃ P : College -> ℝ,
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
            ∃ p : ℝ, ∀ c : College, P c = p) ∧
      (∀
          (valueLaw noiseLaw : Measure ℝ)
          [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
          (hvalue : pg23ConnectedSupport valueLaw)
          (hnoise : pg23ConnectedSupport noiseLaw)
          (hlevel : pg23SourceScoreLevelNull
            (pg23PolycultureTypeLaw (College := College) valueLaw noiseLaw))
          (S : ℝ) (hS : 0 < S ∧ S < 1), ∃ P : College -> ℝ,
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
              ∃ p : ℝ, ∀ c : College, P c = p)

/--
The cited Azevedo--Leshno lattice theorem transported to PG23's general raw
cutoff coordinates.  Score-level nullity is the cited theorem's Assumption 1.
-/
def review_proposition_latticeSpec : Prop :=
  ∀ {College : Type v} [Fintype College] [Nonempty College]
    (typeLaw : Measure (PG23ApplicantType College)) [IsProbabilityMeasure typeLaw]
    (hlevel : pg23SourceScoreLevelNull typeLaw)
    (S : ℝ), 0 < S → S < 1 →
    (∃ cutoff : College -> ℝ,
      pg23SourceMarketClearing
        (pg23SourceAggregateDemand typeLaw)
        (fun _ : College => S / (Fintype.card College : ℝ)) cutoff) ∧
      CompleteLatticeOn
        (pg23SourceMarketClearing
          (pg23SourceAggregateDemand typeLaw)
          (fun _ : College => S / (Fintype.card College : ℝ)))
        pg23RawCutoffLe ∧
      (∀ Z : Set (College -> ℝ), Z.Nonempty →
        (∀ P : College -> ℝ, Z P →
          pg23SourceMarketClearing
            (pg23SourceAggregateDemand typeLaw)
            (fun _ : College => S / (Fintype.card College : ℝ)) P) →
        IsLeastUpperBoundOn
          (pg23SourceMarketClearing
            (pg23SourceAggregateDemand typeLaw)
            (fun _ : College => S / (Fintype.card College : ℝ)))
          pg23RawCutoffLe Z (pg23RawCutoffSup Z)) ∧
      ∀ Z : Set (College -> ℝ), Z.Nonempty →
        (∀ P : College -> ℝ, Z P →
          pg23SourceMarketClearing
            (pg23SourceAggregateDemand typeLaw)
            (fun _ : College => S / (Fintype.card College : ℝ)) P) →
        IsGreatestLowerBoundOn
          (pg23SourceMarketClearing
            (pg23SourceAggregateDemand typeLaw)
            (fun _ : College => S / (Fintype.card College : ℝ)))
          pg23RawCutoffLe Z (pg23RawCutoffInf Z)


/--
Transparent source target for the source's three-part Lemma 10.  The efficient
value cutoff is fixed by its upper-tail mass, and the polyculture cutoff is the
common cutoff in the literal source market-clearing relation.  The proof uses
that weak clearing equation directly, while maximum concentration supplies the
displayed match-probability conclusions under the same weak affordability rule.
The expected maxima are finite, as required by the source expectation notation.
-/
def review_lemma10_threePartSpec : Prop :=
  ∀ (valueLaw noiseLaw : Measure ℝ)
    [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
    (hvalue : pg23ConnectedSupport valueLaw)
    {polyCutoff : ℕ → ℝ} {vS S : ℝ} (hS : 0 < S ∧ S < 1)
    (htail : AppliedModelingLib.Probability.upperTailMass valueLaw vS = S)
    (hmaximum : pg23MaximumConcentratingNoiseLaw noiseLaw)
    (hpoly_clear : ∀ n : ℕ, pg23SourceMarketClearing
      (pg23SourceAggregateDemand
        (pg23PolycultureTypeLaw
          (College := Fin (n + 1)) valueLaw noiseLaw))
      (fun _ : Fin (n + 1) => S / (Fintype.card (Fin (n + 1)) : ℝ))
      (fun _ : Fin (n + 1) => polyCutoff n)),
    (∀ ε δ, 0 < ε → 0 < δ →
      ∀ᶠ n : ℕ in atTop,
        ∀ v : ℝ,
          v <
              polyCutoff n -
                AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
                  (fun k : ℕ => Measure.pi (fun _ : Fin (k + 1) => noiseLaw)) n -
                  δ / 3 →
            AppliedModelingLib.Matching.cutoffWeakCrossingProbability
              (Measure.pi (fun _ : Fin (n + 1) => noiseLaw))
              (Finset.univ : Finset (Fin (n + 1))) v
              (fun _ => polyCutoff n) < ε) ∧
    (∀ ε δ, 0 < ε → 0 < δ →
      ∀ᶠ n : ℕ in atTop,
        ∀ v : ℝ,
          polyCutoff n -
              AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
                (fun k : ℕ => Measure.pi (fun _ : Fin (k + 1) => noiseLaw)) n +
                δ / 3 < v →
            1 - ε <
              AppliedModelingLib.Matching.cutoffWeakCrossingProbability
                (Measure.pi (fun _ : Fin (n + 1) => noiseLaw))
                (Finset.univ : Finset (Fin (n + 1))) v
                (fun _ => polyCutoff n)) ∧
    Tendsto
      (fun n : ℕ =>
        polyCutoff n -
          AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
            (fun k : ℕ => Measure.pi (fun _ : Fin (k + 1) => noiseLaw)) n)
      atTop (nhds vS)


/-- The two asymptotic clauses jointly stated as source Theorem 1. -/
def review_theorem1_wisdomSpec : Prop :=
  (∀
      (valueLaw noiseLaw : Measure ℝ)
      [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
      [NoAtoms valueLaw] [NoAtoms noiseLaw]
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
        (fun _ : Fin (n + 1) => polyCutoff n)), (∀ v : ℝ, v < vS ->
        Tendsto
          (fun n : ℕ => AppliedModelingLib.Matching.cutoffWeakCrossingProbability
            (Measure.pi (fun _ : Fin (n + 1) => noiseLaw)) Finset.univ
            v (fun _ : Fin (n + 1) => polyCutoff n))
          Filter.atTop (nhds 0)) ∧
      (∀ v : ℝ, vS < v ->
        Tendsto
          (fun n : ℕ => AppliedModelingLib.Matching.cutoffWeakCrossingProbability
            (Measure.pi (fun _ : Fin (n + 1) => noiseLaw)) Finset.univ
            v (fun _ : Fin (n + 1) => polyCutoff n))
          Filter.atTop (nhds 1)) ∧
      (∀ v : ℝ, ∀ m n : ℕ,
        noiseLaw.real {noise : ℝ | monoCutoff m ≤ v + noise} =
          noiseLaw.real {noise : ℝ | monoCutoff n ≤ v + noise})) ∧
    (∀
        (valueLaw noiseLaw : Measure ℝ)
        [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
        [NoAtoms valueLaw] [NoAtoms noiseLaw]
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
        (habs_integrable : Integrable (fun v : ℝ => |v|) valueLaw), Tendsto
          (fun n : ℕ => ∫ v : ℝ, v *
            AppliedModelingLib.Matching.cutoffWeakCrossingProbability
              (Measure.pi (fun _ : Fin (n + 1) => noiseLaw)) Finset.univ
              v (fun _ : Fin (n + 1) => polyCutoff n) ∂valueLaw)
          Filter.atTop
          (nhds (∫ v : ℝ, v * (if vS < v then (1 : ℝ) else 0) ∂valueLaw)) ∧
        (∀ m n : ℕ,
          (∫ v : ℝ, v *
            noiseLaw.real {noise : ℝ | monoCutoff m ≤ v + noise} ∂valueLaw) =
          ∫ v : ℝ, v *
            noiseLaw.real {noise : ℝ | monoCutoff n ≤ v + noise} ∂valueLaw) ∧
        (∫ v : ℝ, v *
          noiseLaw.real {noise : ℝ | monoCutoff 0 ≤ v + noise} ∂valueLaw) <
          ∫ v : ℝ, v * (if vS < v then (1 : ℝ) else 0) ∂valueLaw)

/-- The three clauses jointly stated as source Theorem 2. -/
def review_theorem2_topChoiceSpec : Prop :=
  (∀
      {n : ℕ} [NeZero n]
      (valueLaw noiseLaw : Measure ℝ)
      [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
      [NoAtoms noiseLaw]
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
        (fun _ : Fin n => Ppoly)), (∀ v : ℝ,
        noiseLaw.real {noise : ℝ | Ppoly ≤ v + noise} ≤
          noiseLaw.real {noise : ℝ | Pmono ≤ v + noise}) ∧
      0 < valueLaw (pg23NoiseInteriorCutoffRegion noiseLaw Pmono) ∧
      (∀ v ∈ pg23NoiseInteriorCutoffRegion noiseLaw Pmono,
        noiseLaw.real {noise : ℝ | Ppoly ≤ v + noise} <
          noiseLaw.real {noise : ℝ | Pmono ≤ v + noise})) ∧
    (∀ {College : Type v} [Fintype College] [Nonempty College],
      (∀
          (value noise cutoff : ℝ)
          (rank : College -> Fin (Fintype.card College))
          (hrank : Function.Bijective rank) (c : College)
          (hchoice :
            pg23SourceChoice (fun _ : College => cutoff)
              (pg23MonocultureType value noise
                (Equiv.ofBijective rank hrank)) = some c), pg23SourceRank
              (pg23MonocultureType value noise (Equiv.ofBijective rank hrank)) c = 0)) ∧
    (∀
        (valueLaw noiseLaw : Measure ℝ)
        [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
        [NoAtoms valueLaw] [NoAtoms noiseLaw]
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
          (fun _ : Fin (n + 1) => polyCutoff n)), 0 < valueLaw {v : ℝ | vS < v ∧
          noiseLaw.real {noise : ℝ | monoCutoff 0 ≤ v + noise} < 1} ∧
        (∀ v : ℝ,
          v ∈ {w : ℝ | vS < w ∧
            noiseLaw.real {noise : ℝ | monoCutoff 0 ≤ w + noise} < 1} ->
          ∀ᶠ n : ℕ in Filter.atTop,
            noiseLaw.real {noise : ℝ | monoCutoff n ≤ v + noise} <
              AppliedModelingLib.Matching.cutoffWeakCrossingProbability
                (Measure.pi (fun _ : Fin (n + 1) => noiseLaw)) Finset.univ v
                (fun _ : Fin (n + 1) => polyCutoff n)))

/-- The differential-access Equal Cutoffs Lemma in both source economies. -/
def review_lemma_equalCutoffs_differentialAccessSpec : Prop :=
  ∀ {College : Type v} [Fintype College] [Nonempty College],
    (∀
        {n : ℕ}
        (accessLaw : Measure (Fin n)) [IsProbabilityMeasure accessLaw]
        (valueLaw noiseLaw : Measure ℝ)
        [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
        (hvalue : pg23ConnectedSupport valueLaw)
        (hnoise : pg23ConnectedSupport noiseLaw)
        (hlevel : pg23SourceScoreLevelNull
          (pg23MonocultureTypeLaw (College := College) valueLaw noiseLaw))
        (S : ℝ) (hS : 0 < S ∧ S < 1), ∃ P : College -> ℝ,
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
            ∃ p : ℝ, ∀ c : College, P c = p) ∧
      (∀
          {n : ℕ}
          (accessLaw : Measure (Fin n)) [IsProbabilityMeasure accessLaw]
          (valueLaw noiseLaw : Measure ℝ)
          [IsProbabilityMeasure valueLaw] [IsProbabilityMeasure noiseLaw]
          (hvalue : pg23ConnectedSupport valueLaw)
          (hnoise : pg23ConnectedSupport noiseLaw)
          (hlevel : pg23SourceScoreLevelNull
            (pg23PolycultureTypeLaw (College := College) valueLaw noiseLaw))
          (S : ℝ) (hS : 0 < S ∧ S < 1), ∃ P : College -> ℝ,
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
              ∃ p : ℝ, ∀ c : College, P c = p)

end PaperInterface

end PG23MonocultureMatching
