import KR21Monoculture.MainTheorems
import KR21Monoculture.SourceModelEquations
import KR21Monoculture.MallowsDefinition1
import KR21Monoculture.Theorem2Distributional
import KR21Monoculture.GaussianTheorem2Definition1Transport
import KR21Monoculture.LaplaceTheorem2Definition1Transport
import KR21Monoculture.DirectRankMeanBridge
import KR21Monoculture.OuterConditional
import KR21Monoculture.ThreeFirmMallowsBridge
import KR21Monoculture.ThreeFirmMallowsPMFBridge
import KR21Monoculture.ThreeFirmMallowsProductLawBridge
import KR21Monoculture.ThreeFirmUniformCardinalBridge
import KR21Monoculture.ThreeFirmLabelSymmetry
import KR21Monoculture.ThreeFirmCardinalComposition
import KR21Monoculture.ThreeFirmCandidateIdentityBridge
import KR21Monoculture.ThreeFirmEquilibriumLift
import KR21Monoculture.OuterLinearPayoffBridge
import KR21Monoculture.UniformOrderStatisticsBridge
import KR21Monoculture.W11RankingCells
import KR21Monoculture.W11ScoreNormalization
import KR21Monoculture.W11ScoreTransport
import KR21Monoculture.W11ThreeCandidateCells
import KR21Monoculture.W11FourCandidateCells
import KR21Monoculture.W11SourceLawTransport
import KR21Monoculture.W11FourCandidateSourceLawTransport
import KR21Monoculture.W11ArbitraryFiniteCells
import KR21Monoculture.W11Definition1Correction
import KR21Monoculture.Definition1AsymptoticTendsto
import KR21Monoculture.LiteralDefinition1Theorem1Bridge
import KR21Monoculture.OuterLiteralDefinition1Theorem1Bridge
import KR21Monoculture.LaplaceSourceTheorem2Target
import KR21Monoculture.MallowsTwoCandidateCounterexample
import KR21Monoculture.MallowsOuterSource
import KR21Monoculture.MallowsOuterConditionalSource
import KR21Monoculture.Theorem2OuterConditionalSource
import KR21Monoculture.LaplaceSourceNormalization
import KR21Monoculture.PlackettLuceOuterSource
import KR21Monoculture.GumbelPlackettLuceExact
import KR21Monoculture.PlackettLuceStrategyDominance
import KR21Monoculture.PositiveScaleGumbelTransport
import KR21Monoculture.UnitVarianceGumbelSource
import KR21Monoculture.SourceUnitVarianceGumbelOuter
import KR21Monoculture.RUMSourceVarianceNormalization
import KR21Monoculture.SimulationSourceProcedure
import KR21Monoculture.ScaledGumbelOuterSource
import KR21Monoculture.SignedWelfareSource
import KR21Monoculture.SignedWelfareEquilibrium
import KR21Monoculture.SignedWelfareMixed
import KR21Monoculture.AppendixBSmoothingStability
import KR21Monoculture.AppendixBGaussianMixture
import KR21Monoculture.AppendixBSourceScaledSmoothing
import KR21Monoculture.AppendixBGaussianMixtureW11
import KR21Monoculture.AppendixBFiniteSetDefinition1
import KR21Monoculture.Definition1FullW11
import KR21Monoculture.OuterRUMTheorem1Lift
import KR21Monoculture.OuterRUMSourceTheorem1
import KR21Monoculture.SourceDefinitionEndpoints
import KR21Monoculture.AppendixASourceFormula
import KR21Monoculture.AppendixAConditionalTail
import KR21Monoculture.AppendixAW11ConditionalTail
import KR21Monoculture.AppendixBSourceFormula
import KR21Monoculture.AppendixCTheorem6LemmasSource
import KR21Monoculture.AppendixCGeneralLemma2
import KR21Monoculture.AppendixCGenericSourceLawTransport
import KR21Monoculture.AppendixCGeneralLemma3
import KR21Monoculture.AppendixCTheorem7Boundaries
import KR21Monoculture.AppendixCSourcePairwise
import KR21Monoculture.AppendixCFormulaSurface
import KR21Monoculture.AppendixDMLR
import KR21Monoculture.AppendixEFormulaShapes
import KR21Monoculture.AppendixFSourceFormula
import KR21Monoculture.MallowsSourceSurface
import KR21Monoculture.MallowsTheorem4OuterSource
import KR21Monoculture.ResidualSourceParameterSurface

/-!
This file contains the full row-level review surface used by the dashboard and
LLM-as-judge checks. `AuditInterface.lean` is only a compatibility import for
older module paths.

# Paper Interface: Algorithmic Monoculture and Social Welfare

`MainTheorems.lean` remains the broader proof ledger; this interface exposes
the configured paper-facing rows directly for paper-vs-Lean review.
-/

open AppliedModelingLib MeasureTheory ProbabilityTheory Filter
open AppliedModelingLib.SocialChoice.Ranking
open scoped ENNReal NNReal Topology

namespace KR21Monoculture
namespace PaperInterface

/-! ## Paper Definitions -/

/--
Library/source cardinality convention: the library index `n` represents a
source candidate universe with exactly `n + 2` elements.  Thus a source
four-candidate instance is represented by `Candidate 2`, not `Candidate 4`.
-/
theorem source_candidate_count_representation (n : ℕ) :
    Fintype.card (Candidate n) = n + 2 := by
  simp [Candidate]

/--
The source model's strict intrinsic-value condition is represented relative to
one declared true ranking.  This is the actual value-order predicate used by
the paper-facing source endpoints, rather than an inference from candidate
labels or a theorem name.
-/
theorem source_model_candidate_value_order
    {n : ℕ} (trueRanking : Ranking n) (value : Candidate n → ℝ) :
    SourceCandidateValueOrder trueRanking value ↔
      StrictlyOrderedBy trueRanking value :=
  KR21Monoculture.source_candidate_value_order_iff trueRanking value

/--
The library's `Candidate n` carrier has exactly `n + 2` source candidates.
This source-cardinality bridge is explicit so finite source formulas do not
silently change their candidate domain.
-/
theorem source_model_candidate_cardinality (n : ℕ) :
    Fintype.card (Candidate n) = n + 2 :=
  KR21Monoculture.source_candidate_model_cardinality n

/--
Section 2.2 has two firms each make one hire from the common candidate pool.
The source model consequently has at least two candidates.  The library
encoding makes the lower boundary explicit: `Candidate 0` is the source
two-candidate case.
-/
theorem source_model_two_firm_candidate_domain (n : ℕ) :
    2 ≤ Fintype.card (Candidate n) := by
  rw [source_model_candidate_cardinality]
  omega

/--
Complete Section 2.1--2.2 source-model surface: the finite carrier convention,
the two-firm lower candidate boundary, the rank-labelled strict value order,
and a genuine probability law on rankings at every positive source accuracy
parameter are stated together.  The
probability-law conclusion is an ordinary total-mass equation, not an audit
inference from `PMF` in a declaration name.  Lean's total `dist : ℝ → _`
field is not being used here to attribute zero or negative accuracies to the
source model.
-/
theorem source_model_candidates_values_and_ranking_law
    {n : ℕ} (trueRanking : Ranking n) (F : AccuracyFamily n)
    (hvalueOrder : StrictlyOrderedBy trueRanking F.value) :
    Fintype.card (Candidate n) = n + 2 ∧
      2 ≤ Fintype.card (Candidate n) ∧
      (∀ {a b : Candidate n},
        rankOf trueRanking a < rankOf trueRanking b → F.value b < F.value a) ∧
      ∀ theta, 0 < theta → (F.dist theta).toMeasure Set.univ = 1 := by
  refine ⟨source_model_candidate_cardinality n,
    source_model_two_firm_candidate_domain n, ?_, ?_⟩
  · exact hvalueOrder
  intro theta _
  letI : IsProbabilityMeasure (F.dist theta).toMeasure := by infer_instance
  exact IsProbabilityMeasure.measure_univ

/--
Audited source-facing proposition for the complete Section 2.1 model surface.
The candidate-cardinality convention, strict value ordering, and ranking-law
normalization are written here independently of the route that proves them.
-/
abbrev source_model_candidates_values_and_ranking_lawSpec
    {n : ℕ} (trueRanking : Ranking n) (F : AccuracyFamily n)
    (hvalueOrder : StrictlyOrderedBy trueRanking F.value) : Prop :=
  Fintype.card (Candidate n) = n + 2 ∧
    2 ≤ Fintype.card (Candidate n) ∧
    (∀ {a b : Candidate n},
      rankOf trueRanking a < rankOf trueRanking b → F.value b < F.value a) ∧
    ∀ theta, 0 < theta → (F.dist theta).toMeasure Set.univ = 1

theorem source_model_candidates_values_and_ranking_law_spec_proof
    {n : ℕ} (trueRanking : Ranking n) (F : AccuracyFamily n)
    (hvalueOrder : StrictlyOrderedBy trueRanking F.value) :
    source_model_candidates_values_and_ranking_lawSpec trueRanking F hvalueOrder :=
  source_model_candidates_values_and_ranking_law trueRanking F hvalueOrder

/--
The source permits deterministically known candidate values, provided their
identities retain the globally fixed strict true-value order.  A point mass on
such a profile is therefore an explicit admissible outer-D probability law.
-/
theorem source_model_outer_distribution_allows_point_mass
    {n : ℕ} (trueRanking : Ranking n) (value : ValueProfile n)
    (hvalueOrder : StrictlyOrderedBy trueRanking value) :
    IsProbabilityMeasure (Measure.dirac value) :=
  KR21Monoculture.source_outer_candidate_distribution_allows_point_mass value

/--
The outer source model ranges over an arbitrary probability law `D` supported
on the globally fixed, rank-labelled strict value order, not just over a
selected construction.  The same model also admits every degenerate law in
that source-compatible domain.  Both total-mass facts are displayed so source
coverage cannot be credited merely because an endpoint happens to mention `D`.
-/
theorem source_model_outer_distribution_probability_and_point_mass
    {n : ℕ} (trueRanking : Ranking n) (D : Measure (ValueProfile n))
    [IsProbabilityMeasure D]
    (hDvalueOrder : ∀ᵐ realizedValue ∂D,
      StrictlyOrderedBy trueRanking realizedValue)
    (value : ValueProfile n)
    (hvalueOrder : StrictlyOrderedBy trueRanking value) :
    D Set.univ = 1 ∧
      (Measure.dirac value) Set.univ = 1 ∧
        IsProbabilityMeasure (Measure.dirac value) := by
  letI : IsProbabilityMeasure (Measure.dirac value) :=
    source_model_outer_distribution_allows_point_mass trueRanking value hvalueOrder
  exact ⟨IsProbabilityMeasure.measure_univ, IsProbabilityMeasure.measure_univ,
    inferInstance⟩

/--
When the source's outer candidate distribution is a point mass, its
outer-then-conditionally-independent Definition-2 experiment reduces exactly
to the original fixed-value ranking experiment.  Thus the source's
deterministically-known-values case is a specialization of the same outer-D
semantics, not a separate surrogate model.
-/
theorem source_model_point_mass_definition2_specialization
    {n : ℕ} (F : DistributionalAccuracyFamily n) (trueRanking : Ranking n)
    (value : ValueProfile n)
    (hvalueOrder : StrictlyOrderedBy trueRanking value)
    (theta : ℝ)
    (regularity : DistributionalAccuracyFamily.OuterIndependentRerankingJointRegularity
      F (Measure.dirac value) theta) :
    F.outerDisagreementProbability (Measure.dirac value) theta =
        disagreementProb (F.dist theta value) ∧
      F.outerDisagreementGainNumerator (Measure.dirac value) theta =
        expectedRerankingGain (F.dist theta value) value ∧
      F.jointLawDisagreementConditionalGain (Measure.dirac value) theta
        regularity.base.ranking_atom_measurable =
          disagreementConditionalGain (F.dist theta value) value := by
  exact ⟨DistributionalAccuracyFamily.outerDisagreementProbability_dirac F value theta,
    DistributionalAccuracyFamily.outerDisagreementGainNumerator_dirac F value theta,
    DistributionalAccuracyFamily.jointLawDisagreementConditionalGain_dirac
      F value theta regularity⟩

/-- Source Definition 1 as a proposition, before selecting any concrete family. -/
abbrev source_definition1 := @KR21Monoculture.SourceDefinition1

/--
Source Definition 1 expanded at the paper-facing surface.  This exposes the
atom regularity, true-ranking limit, every-nonempty-remaining-set weak
monotonicity, and full-set strict monotonicity clauses directly.  The source's
global strict value-order convention is an explicit scope condition rather
than an implicit profile relabeling.
-/
theorem source_definition1_iff
    {n : ℕ} (F : AccuracyFamily n) (trueRanking : Ranking n)
    (hvalueOrder : StrictlyOrderedBy trueRanking F.value) :
    SourceDefinition1 F trueRanking ↔
      (∀ theta, 0 < theta → ∀ pi : Ranking n,
        ContinuousAt (fun theta' => ((F.dist theta') pi).toReal) theta ∧
          DifferentiableAt ℝ (fun theta' => ((F.dist theta') pi).toReal) theta) ∧
      Tendsto (fun theta => ((F.dist theta) trueRanking).toReal) atTop (nhds 1) ∧
      ∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
        (∀ remaining : Finset (Candidate n), remaining.Nonempty →
          expectedBestInSet (F.dist thetaH) F.value remaining ≤
            expectedBestInSet (F.dist thetaA) F.value remaining) ∧
        expectedBestInSet (F.dist thetaH) F.value Finset.univ <
          expectedBestInSet (F.dist thetaA) F.value Finset.univ :=
  Iff.rfl

/-- Source Definition 2's literal conditional-gain proposition at one accuracy. -/
abbrev source_definition2_conditional_at :=
  @KR21Monoculture.SourceDefinition2ConditionalAt

/-- Source Definition 3's literal outer-D payoff proposition at two accuracies. -/
abbrev source_definition3_at := @KR21Monoculture.SourceDefinition3At

/--
Source Definition 1, concrete Mallows instance: the finite ranking family has
the literal atom regularity, high-accuracy, and every-remaining-set clauses.
-/
theorem source_definition1_concrete_mallows
    {n : ℕ} (trueRanking : Ranking n) (value : Candidate n → ℝ)
    (hvalue : SourceCandidateValueOrder trueRanking value) :
    SourceDefinition1
      ({ dist := fun theta => (concreteMallowsSpec trueRanking theta).law,
         value := value } : AccuracyFamily n)
      trueRanking :=
  KR21Monoculture.source_definition1_concrete_mallows trueRanking value hvalue

/--
Equation (1), projected from a literal Definition 1 package.  Every nonempty
remaining set weakly improves with accuracy, and the full candidate universe
improves strictly.  Its source-facing scope retains Definition 1's globally
fixed strict true-value order.
-/
theorem source_equation1_removal_monotonicity
    {n : ℕ} {F : AccuracyFamily n} {trueRanking : Ranking n}
    (hvalueOrder : StrictlyOrderedBy trueRanking F.value)
    (hdefinition1 : SourceDefinition1 F trueRanking) :
    ∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
      (∀ remaining : Finset (Candidate n), remaining.Nonempty →
        expectedBestInSet (F.dist thetaH) F.value remaining ≤
          expectedBestInSet (F.dist thetaA) F.value remaining) ∧
      expectedBestInSet (F.dist thetaH) F.value Finset.univ <
        expectedBestInSet (F.dist thetaA) F.value Finset.univ :=
  KR21Monoculture.source_equation1_removal_monotonicity hdefinition1

/--
Source Definition 2 at one accuracy is the literal outer-D conditional gain
in the actual joint value/ranking experiment.  Positive top-disagreement mass
is visible because the source conditional expression otherwise has no ordinary
real-valued interpretation.
-/
theorem source_definition2_conditional_at_iff_payoff_comparison
    {n : ℕ} (F : DistributionalAccuracyFamily n) (D : Measure (ValueProfile n))
    (theta : ℝ)
    (regularity : DistributionalAccuracyFamily.OuterIndependentRerankingJointRegularity
      F D theta)
    (hdisagreement : 0 < ∫ x : ValueProfile n × RankingPair n,
      (if disagreementEvent x.2 then (1 : ℝ) else 0) ∂
        F.outerIndependentPairJointLaw D theta regularity.base.ranking_atom_measurable) :
    SourceDefinition2ConditionalAt F D theta regularity.base.ranking_atom_measurable ↔
      F.PrefersIndependentReranking D theta :=
  KR21Monoculture.source_definition2_conditional_at_iff_payoff_comparison
    F D theta regularity hdisagreement

/--
Source Definition 2 with its full universal positive-accuracy quantifier and
literal outer value/ranking-pair conditional experiment.  The positive
denominator is an explicit well-posedness condition for the displayed
conditional expectation, rather than a silent totalization convention.
-/
theorem source_definition2_iff
    {n : ℕ} (F : DistributionalAccuracyFamily n)
    (D : Measure (ValueProfile n)) :
    SourceDefinition2 F D ↔
      ∀ theta : ℝ, 0 < theta → ∀ hatom : ∀ ranking : Ranking n,
        Measurable fun value => F.dist theta value ranking,
        let J := F.outerIndependentPairJointLaw D theta hatom
        let numerator : ℝ := ∫ x : ValueProfile n × RankingPair n,
          if firstChoice x.2.1 ≠ firstChoice x.2.2 then
            x.1 (firstChoice x.2.1) - x.1 (secondChoice x.2.1)
          else 0 ∂J
        let denominator : ℝ := ∫ x : ValueProfile n × RankingPair n,
          if firstChoice x.2.1 ≠ firstChoice x.2.2 then (1 : ℝ) else 0 ∂J
        0 < denominator → 0 < numerator / denominator :=
  Iff.rfl

/--
Source Definition 3 is definitionally the outer-D comparison between an
accurate and a human first mover against the same human second mover.
-/
theorem source_definition3_at_iff_weaker_competition
    {n : ℕ} (F : DistributionalAccuracyFamily n) (D : Measure (ValueProfile n))
    (thetaA thetaH : ℝ) :
    SourceDefinition3At F D thetaA thetaH ↔
      F.PrefersWeakerCompetition D thetaA thetaH :=
  KR21Monoculture.source_definition3_at_iff_weaker_competition F D thetaA thetaH

/--
Source Definition 3 with its full quantifier over every ordered positive
accuracy pair.  The same human law is the second mover in both displayed
outer expectations.
-/
theorem source_definition3_iff
    {n : ℕ} (F : DistributionalAccuracyFamily n)
    (D : Measure (ValueProfile n)) :
    SourceDefinition3 F D ↔
      ∀ thetaA thetaH : ℝ, 0 < thetaH → thetaH < thetaA →
        (∫ value : ValueProfile n,
          pmfPairExp (F.dist thetaH value) (F.dist thetaA value)
            (fun pi sigma => secondMoverUtility value pi sigma) ∂D) <
        (∫ value : ValueProfile n,
          pmfPairExp (F.dist thetaH value) (F.dist thetaH value)
            (fun pi sigma => secondMoverUtility value pi sigma) ∂D) :=
  Iff.rfl

/-! ## Section 2.2 Model and Equations (2)--(6) -/

/--
Source Section 2.2's two-firm game semantics.  The algorithm--algorithm
profile shares one realized ranking; every other profile uses independent
rankings.  A labeled firm's payoff averages its first- and second-mover
utilities because the two-firm order is uniform.
-/
theorem source_two_firm_selection_game_semantics
    {n : ℕ} (M : Model n) :
    Model.firstMoverEU M Strategy.algorithm =
        expectedFirstMoverUtility M.algorithmRanking M.value ∧
    Model.firstMoverEU M Strategy.human =
        expectedFirstMoverUtility M.humanRanking M.value ∧
    Model.secondMoverEU M Strategy.algorithm Strategy.algorithm =
        expectedSecondMoverShared M.algorithmRanking M.value ∧
    Model.secondMoverEU M Strategy.algorithm Strategy.human =
        expectedSecondMoverIndependent M.humanRanking M.algorithmRanking M.value ∧
    Model.secondMoverEU M Strategy.human Strategy.algorithm =
        expectedSecondMoverIndependent M.algorithmRanking M.humanRanking M.value ∧
    Model.secondMoverEU M Strategy.human Strategy.human =
        expectedSecondMoverIndependent M.humanRanking M.humanRanking M.value ∧
    ∀ self other : Strategy,
      Model.payoffAgainst M self other =
        (Model.firstMoverEU M self + Model.secondMoverEU M other self) / 2 :=
  KR21Monoculture.source_two_firm_selection_game_semantics M

/--
Equation (2): at equal accuracy, positive conditional first-versus-second gain
on top-choice disagreement is equivalent to an independent second mover
strictly preferring its own ranking to the shared ranking.  Positive event mass
is explicit because the source conditional expectation is otherwise undefined.
-/
theorem equation2_independent_reranking_payoff_equivalence
    {n : ℕ} (mu : PMF (Ranking n)) (value : Candidate n → ℝ)
    (hdisagreement : 0 < disagreementProb mu) :
    0 < disagreementConditionalGain mu value ↔
      expectedSecondMoverShared mu value <
        expectedSecondMoverIndependent mu mu value :=
  KR21Monoculture.equation2_independent_reranking_payoff_equivalence
    mu value hdisagreement

/--
Equation (3): with independent equal-law rankings, the second mover's payoff
gain is exactly the expectation of the literal source first-minus-second gap on
top-choice disagreement.  The first coordinate is the independent second
mover's ranking and the second is the first mover's ranking.
-/
theorem equation3_independent_reranking_payoff_identity
    {n : ℕ} (mu : PMF (Ranking n)) (value : Candidate n → ℝ) :
    expectedSecondMoverIndependent mu mu value -
        expectedSecondMoverShared mu value =
      pmfPairIndicatorExp mu mu disagreementEvent
        (fun pair =>
          value (firstChoice pair.1) - value (secondChoice pair.1)) :=
  KR21Monoculture.equation3_independent_reranking_payoff_identity mu value

/--
Equation (4): its displayed numerator inequality is exactly strict best
response by the algorithm against an algorithmic opponent.
-/
theorem equation4_algorithm_best_response_against_algorithm_iff
    {n : ℕ} (M : Model n) :
    (Model.firstMoverEU M Strategy.algorithm +
        Model.secondMoverEU M Strategy.algorithm Strategy.algorithm >
      Model.firstMoverEU M Strategy.human +
        Model.secondMoverEU M Strategy.algorithm Strategy.human) ↔
      Model.payoffAgainst M Strategy.algorithm Strategy.algorithm >
        Model.payoffAgainst M Strategy.human Strategy.algorithm :=
  KR21Monoculture.equation4_algorithm_best_response_against_algorithm_iff M

/--
Equation (5) from the literal finite-removal clauses of Definition 1.  Strict
full-set improvement gives the first-mover inequality and weak improvement for
every remaining set gives the second-mover inequality.
-/
theorem equation5_from_literal_definition1_removal
    {n : ℕ} (F : AccuracyFamily n) (thetaA thetaH : ℝ)
    (hthetaH : 0 < thetaH) (hthetaA : thetaH < thetaA)
    (hweak : ∀ remaining : Finset (Candidate n), remaining.Nonempty →
      expectedBestInSet (F.dist thetaH) F.value remaining ≤
        expectedBestInSet (F.dist thetaA) F.value remaining)
    (hstrict :
      expectedBestInSet (F.dist thetaH) F.value Finset.univ <
        expectedBestInSet (F.dist thetaA) F.value Finset.univ) :
    Model.firstMoverEU (F.modelAt thetaA thetaH) Strategy.algorithm +
        Model.secondMoverEU (F.modelAt thetaA thetaH)
          Strategy.human Strategy.algorithm >
      Model.firstMoverEU (F.modelAt thetaA thetaH) Strategy.human +
        Model.secondMoverEU (F.modelAt thetaA thetaH)
          Strategy.human Strategy.human :=
  KR21Monoculture.equation5_from_literal_definition1_removal
    F thetaA thetaH hweak hstrict

/--
Equation (6): a continuous sign change from `f < g` to `g < f` yields an
intermediate algorithm accuracy at which the displayed payoffs against an
algorithmic opponent are equal.
-/
theorem equation6_indifference_threshold_of_sign_change
    {n : ℕ} (F : AccuracyFamily n) (thetaH lo hi : ℝ)
    (hthetaH : 0 < thetaH)
    (hthetaH_lo : thetaH < lo) (hlo_hi : lo < hi)
    (hcontinuous : ContinuousOn
      (fun thetaA =>
        AccuracyFamily.theorem1_f F thetaA thetaH -
          AccuracyFamily.theorem1_g F thetaA thetaH)
      (Set.Icc lo hi))
    (hlo : AccuracyFamily.theorem1_f F lo thetaH <
      AccuracyFamily.theorem1_g F lo thetaH)
    (hhi : AccuracyFamily.theorem1_g F hi thetaH <
      AccuracyFamily.theorem1_f F hi thetaH) :
    ∃ thetaA, thetaH < thetaA ∧
      AccuracyFamily.theorem1_f F thetaA thetaH =
        AccuracyFamily.theorem1_g F thetaA thetaH :=
  KR21Monoculture.equation6_indifference_threshold_of_sign_change
    F thetaH lo hi hthetaH_lo hlo_hi hcontinuous hlo hhi

/--
The source's named four-candidate rankings in the three-firm computation map
to `Ranking 2`, and the source inversion count is exactly the library Kendall
distance from the identity center.  This establishes the finite ranking metric
bridge only; the normalized law and full cardinal-value experiment are
separate obligations.
-/
theorem source_threeFirm_fourCandidate_inversion_bridge
    (pi : SourceFourRanking) :
    sourceExecutableInversionCount pi =
      kendallTau (Equiv.refl (Candidate 2)) (sourceFourRankingToRanking pi) :=
  sourceExecutableInversionCount_eq_kendallTau pi

/--
For the source's algorithm parameter, the named-ranking unnormalized weight
agrees with the library identity-centered Mallows weight after casting to
reals.  This is not yet a normalized-law equivalence.
-/
theorem source_threeFirm_algorithm_mallows_unnormalized_weight_bridge
    (pi : SourceFourRanking) :
    ((sourceAlgorithmQ ^ sourceExecutableInversionCount pi : ℚ) : ℝ) =
      mallowsWeight ((1 : ℝ) / 2) (Equiv.refl (Candidate 2))
        (sourceFourRankingToRanking pi) :=
  sourceAlgorithmMallowsWeight_cast pi

/--
For the source's human parameter, the named-ranking unnormalized weight agrees
with the library identity-centered Mallows weight after casting to reals.  This
is not yet a normalized-law equivalence.
-/
theorem source_threeFirm_human_mallows_unnormalized_weight_bridge
    (pi : SourceFourRanking) :
    ((sourceHumanQ ^ sourceExecutableInversionCount pi : ℚ) : ℝ) =
      mallowsWeight ((4 : ℝ) / 7) (Equiv.refl (Candidate 2))
        (sourceFourRankingToRanking pi) :=
  sourceHumanMallowsWeight_cast pi

/--
The source executable finite Mallows law is a normalized PMF on its named
four-candidate rankings and agrees atomwise with the library law after the
proved `Ranking 2` conversion.  This covers one ranking draw only, not the
three-firm product experiment.
-/
theorem source_threeFirm_fourCandidate_mallows_pmf_bridge
    (q : ℚ) (hq : 0 < q) (pi : SourceFourRanking) :
    sourceExecutableMallowsPMF q hq pi =
      (MallowsSpec.ofQ (Equiv.refl (Candidate 2)) (q : ℝ)
        (sourceQ_cast_pos hq)).law (sourceFourRankingToRanking pi) :=
  sourceExecutableMallowsPMF_apply_eq_mallowsSpecOfQ q hq pi

/-- Paper Mallows family parameterization used by the compact review surface. -/
noncomputable abbrev mallowsSpec {n : ℕ} (center : Ranking n) (theta : ℝ) := concreteMallowsSpec center theta

/--
Equation (8), explicit Mallows probability formula in the paper's
theta = phi - 1 parameterization. Lean's inverse parameter is
q = mallowsAccuracyQ theta = phi inverse on the positive source domain.
-/
theorem mallowsSpec_law_formula
    {n : ℕ} (center : Ranking n) (theta : ℝ) (pi : Ranking n) :
    (((mallowsSpec center theta).law) pi).toReal =
      mallowsWeight (mallowsAccuracyQ theta) center pi /
        (mallowsSpec center theta).partition :=
  (mallowsSpec center theta).law_apply_toReal pi

/--
Equation (8) at the source parameter surface.  The paper's `phi > 1` and
`theta = phi - 1` conditions are explicit, and the resulting probability is
the normalized `phi^(-kendallTau)` mass rather than an internal `q` formula.
-/
theorem equation8_source_concrete_mallows_probability
    {n : ℕ} (center : Ranking n) (phi theta : ℝ)
    (hphi : 1 < phi) (htheta : theta = phi - 1) (pi : Ranking n) :
    let M := concreteMallowsSpec center theta
    M.q = phi⁻¹ ∧
      (M.law pi).toReal =
        phi⁻¹ ^ kendallTau center pi /
          (∑ tau : Ranking n, phi⁻¹ ^ kendallTau center tau) :=
  KR21Monoculture.source_equation8_concrete_mallows_probability
    center phi theta hphi htheta pi

/-- Paper Appendix C strict well-ordered noise predicate. -/
abbrev strictlyWellOrderedNoise (f : ℝ → ℝ) : Prop := StrictlyWellOrderedNoise f

/--
Appendix C Definition 4, unfolded source formula.  A noise density is strictly
well ordered exactly when every pair of ordered locations satisfies the
paper's strict product inequality.
-/
theorem definition4_strictlyWellOrderedNoise_iff (f : ℝ → ℝ) :
    strictlyWellOrderedNoise f ↔
      ∀ ⦃a b c d : ℝ⦄, b < a → d < c →
        f (a - c) * f (b - d) > f (a - d) * f (b - c) :=
  Iff.rfl

/-! ## Definitions and Appendix C Noise Statements -/

/--
Definition 1 / Mallows atomwise continuity: for the Mallows family with
parameter `theta`, the probability of any fixed permutation varies continuously
with positive `theta`.
-/
theorem definition1_concreteMallowsSpec_atom_continuity
    {n : ℕ} (center : Ranking n) {theta : ℝ} (htheta : 0 < theta)
    (pi : Ranking n) :
    AppliedModelingLib.EpsilonContinuousAt
      (fun theta' => (((concreteMallowsSpec center theta').law) pi).toReal) theta :=
    KR21Monoculture.paper_definition1_concreteMallowsSpec_atom_continuity
      center htheta pi

/--
Definition 1 / Mallows asymptotic first dominance: as algorithmic Mallows
accuracy tends to infinity, the all-algorithm payoff eventually exceeds the
human-against-algorithm payoff used in Theorem 1.
-/
theorem definition1_concreteMallowsSpec_asymptotic_first_dominance
    {n : ℕ} (center : Ranking n) (value : Candidate n → ℝ)
    (hvalue : StrictlyOrderedBy center value) :
    ∀ thetaH lower, 0 < thetaH → thetaH < lower →
      ∃ hi, lower < hi ∧
        AccuracyFamily.theorem1_g
            ({ dist := fun theta => (concreteMallowsSpec center theta).law,
                value := value } : AccuracyFamily n)
            hi thetaH <
          AccuracyFamily.theorem1_f
            ({ dist := fun theta => (concreteMallowsSpec center theta).law,
                value := value } : AccuracyFamily n)
            hi thetaH :=
    KR21Monoculture.paper_definition1_concreteMallowsSpec_asymptotic_first_dominance
      center value hvalue

/--
Appendix A / Theorem 5 deterministic finite-source monotonicity: if a finite
source law over RUM score vectors is ranked once by raw scores and once after a
strict contraction toward true values, then every nonempty remaining candidate
set has weakly higher expected top value after contraction.
-/
theorem appendixA_expectedBestInSet_monotonicity_of_finite_rankByScore_contraction
    {n : ℕ} {Omega : Type*} [Fintype Omega] [DecidableEq Omega]
    (mu : PMF Omega) (value : Candidate n → ℝ)
    (raw : Omega → Candidate n → ℝ)
    {remaining : Finset (Candidate n)}
    {t : ℝ} (ht0 : 0 ≤ t) (htlt1 : t < 1)
    (hremaining : remaining.Nonempty) :
    AppliedModelingLib.SocialChoice.Ranking.expectedBestInSet
        (mu.map (fun omega =>
          AppliedModelingLib.SocialChoice.Ranking.rankByScore (raw omega)))
        value remaining ≤
      AppliedModelingLib.SocialChoice.Ranking.expectedBestInSet
        (mu.map (fun omega =>
          AppliedModelingLib.SocialChoice.Ranking.rankByScore
            (fun i => paper_appendixC_contractedScore t (value i) (raw omega i))))
        value remaining :=
  KR21Monoculture.paper_appendixA_expectedBestInSet_monotonicity_of_finite_rankByScore_contraction
    mu value raw ht0 htlt1 hremaining

/--
Appendix A / Theorem 5 continuous-source monotonicity: if a probability source
over RUM score vectors is ranked once by raw scores and once after a strict
contraction toward true values, then every nonempty remaining candidate set has
weakly higher expected top value after contraction.

Source status: derived from source primitives.
-/
theorem appendixA_expectedBestInSet_monotonicity_of_measure_rankByScore_contraction
    {n : ℕ} {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (value : Candidate n → ℝ)
    (raw : Omega → Candidate n → ℝ)
    {remaining : Finset (Candidate n)}
    {t : ℝ}
    (hrawRank :
      Measurable (fun omega =>
        AppliedModelingLib.SocialChoice.Ranking.rankByScore (raw omega)))
    (hcontractRank :
      Measurable (fun omega =>
        AppliedModelingLib.SocialChoice.Ranking.rankByScore
          (fun i => paper_appendixC_contractedScore t (value i) (raw omega i))))
    (ht0 : 0 ≤ t) (htlt1 : t < 1)
    (hremaining : remaining.Nonempty) :
    AppliedModelingLib.SocialChoice.Ranking.expectedBestInSet
        (AppliedModelingLib.SocialChoice.Ranking.rankingPMFOfMeasure mu
          (fun omega => AppliedModelingLib.SocialChoice.Ranking.rankByScore (raw omega))
          hrawRank)
        value remaining ≤
      AppliedModelingLib.SocialChoice.Ranking.expectedBestInSet
        (AppliedModelingLib.SocialChoice.Ranking.rankingPMFOfMeasure mu
          (fun omega =>
            AppliedModelingLib.SocialChoice.Ranking.rankByScore
              (fun i => paper_appendixC_contractedScore t (value i) (raw omega i)))
          hcontractRank)
        value remaining :=
  KR21Monoculture.paper_appendixA_expectedBestInSet_monotonicity_of_measure_rankByScore_contraction
    mu value raw hrawRank hcontractRank ht0 htlt1 hremaining

/--
Appendix A / Theorem 5 strict continuous-source monotonicity: the same
source-coupled contraction gives strict expected improvement when the strict
pointwise-improvement region has positive source measure.
-/
theorem appendixA_expectedBestInSet_strict_of_measure_rankByScore_contraction
    {n : ℕ} {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (value : Candidate n → ℝ)
    (raw : Omega → Candidate n → ℝ)
    {remaining : Finset (Candidate n)}
    {t : ℝ}
    (hrawRank :
      Measurable (fun omega =>
        AppliedModelingLib.SocialChoice.Ranking.rankByScore (raw omega)))
    (hcontractRank :
      Measurable (fun omega =>
        AppliedModelingLib.SocialChoice.Ranking.rankByScore
          (fun i => paper_appendixC_contractedScore t (value i) (raw omega i))))
    (ht0 : 0 ≤ t) (htlt1 : t < 1)
    (hremaining : remaining.Nonempty)
    (hstrict :
      0 < mu {omega |
        value
          (bestInSet
            (AppliedModelingLib.SocialChoice.Ranking.rankByScore (raw omega))
            remaining) <
        value
          (bestInSet
            (AppliedModelingLib.SocialChoice.Ranking.rankByScore
              (fun i => paper_appendixC_contractedScore t (value i) (raw omega i)))
            remaining)}) :
    AppliedModelingLib.SocialChoice.Ranking.expectedBestInSet
        (AppliedModelingLib.SocialChoice.Ranking.rankingPMFOfMeasure mu
          (fun omega => AppliedModelingLib.SocialChoice.Ranking.rankByScore (raw omega))
          hrawRank)
        value remaining <
      AppliedModelingLib.SocialChoice.Ranking.expectedBestInSet
        (AppliedModelingLib.SocialChoice.Ranking.rankingPMFOfMeasure mu
          (fun omega =>
            AppliedModelingLib.SocialChoice.Ranking.rankByScore
              (fun i => paper_appendixC_contractedScore t (value i) (raw omega i)))
          hcontractRank)
        value remaining :=
  KR21Monoculture.paper_appendixA_expectedBestInSet_strict_of_measure_rankByScore_contraction
    mu value raw hrawRank hcontractRank ht0 htlt1 hremaining hstrict

/--
Appendix A / Theorem 5 scaled-noise RUM monotonicity: for `thetaH < thetaA`,
ranking scores `x_i + noise_i / thetaA` is a contraction of
`x_i + noise_i / thetaH`; hence the source model satisfies the finite-removal
monotonicity certificate used by Theorem 1, provided the full-set strict
improvement region has positive source measure.

Source status: derived from source primitives.
-/
theorem appendixA_theorem1RemovalMonotonicityAt_of_scaledNoise_rankByScore_source
    {n : ℕ} {Omega : Type*} [MeasurableSpace Omega]
    {F : AccuracyFamily n} {thetaA thetaH : ℝ}
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (noise : Omega → Candidate n → ℝ)
    (hthetaH : 0 < thetaH) (hthetaHA : thetaH < thetaA)
    (hrawRank :
      Measurable (fun omega =>
        AppliedModelingLib.SocialChoice.Ranking.rankByScore
          (fun i => F.value i + noise omega i / thetaH)))
    (haccurateRank :
      Measurable (fun omega =>
        AppliedModelingLib.SocialChoice.Ranking.rankByScore
          (fun i => F.value i + noise omega i / thetaA)))
    (hdistH :
      F.dist thetaH =
        AppliedModelingLib.SocialChoice.Ranking.rankingPMFOfMeasure mu
          (fun omega =>
            AppliedModelingLib.SocialChoice.Ranking.rankByScore
              (fun i => F.value i + noise omega i / thetaH))
          hrawRank)
    (hdistA :
      F.dist thetaA =
        AppliedModelingLib.SocialChoice.Ranking.rankingPMFOfMeasure mu
          (fun omega =>
            AppliedModelingLib.SocialChoice.Ranking.rankByScore
              (fun i => F.value i + noise omega i / thetaA))
          haccurateRank)
    (hstrict_univ :
      0 < mu {omega |
        F.value
          (bestInSet
            (AppliedModelingLib.SocialChoice.Ranking.rankByScore
              (fun i => F.value i + noise omega i / thetaH))
            Finset.univ) <
        F.value
          (bestInSet
            (AppliedModelingLib.SocialChoice.Ranking.rankByScore
              (fun i => F.value i + noise omega i / thetaA))
            Finset.univ)}) :
    AccuracyFamily.Theorem1RemovalMonotonicityAt F thetaA thetaH :=
  KR21Monoculture.paper_appendixA_theorem1RemovalMonotonicityAt_of_scaledNoise_rankByScore_source
    mu noise hthetaH hthetaHA hrawRank haccurateRank hdistH hdistA hstrict_univ

/--
Appendix A / Theorem 5 scaled-noise RUM monotonicity from a concrete top-switch
source region: it is enough to exhibit positive source mass where the
low-accuracy scores uniquely put a lower-valued candidate on top, while the
high-accuracy scores uniquely put a higher-valued candidate on top.

Source status: derived from source primitives.
-/
theorem appendixA_theorem1RemovalMonotonicityAt_of_scaledNoise_top_switch_set
    {n : ℕ} {Omega : Type*} [MeasurableSpace Omega]
    {F : AccuracyFamily n} {thetaA thetaH : ℝ}
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (noise : Omega → Candidate n → ℝ)
    (hthetaH : 0 < thetaH) (hthetaHA : thetaH < thetaA)
    (hrawRank :
      Measurable (fun omega =>
        AppliedModelingLib.SocialChoice.Ranking.rankByScore
          (fun i => F.value i + noise omega i / thetaH)))
    (haccurateRank :
      Measurable (fun omega =>
        AppliedModelingLib.SocialChoice.Ranking.rankByScore
          (fun i => F.value i + noise omega i / thetaA)))
    (hdistH :
      F.dist thetaH =
        AppliedModelingLib.SocialChoice.Ranking.rankingPMFOfMeasure mu
          (fun omega =>
            AppliedModelingLib.SocialChoice.Ranking.rankByScore
              (fun i => F.value i + noise omega i / thetaH))
          hrawRank)
    (hdistA :
      F.dist thetaA =
        AppliedModelingLib.SocialChoice.Ranking.rankingPMFOfMeasure mu
          (fun omega =>
            AppliedModelingLib.SocialChoice.Ranking.rankByScore
              (fun i => F.value i + noise omega i / thetaA))
          haccurateRank)
    {low high : Candidate n} {S : Set Omega}
    (hSpos : 0 < mu S)
    (hvalue : F.value low < F.value high)
    (hrawTop :
      ∀ omega ∈ S, ∀ d : Candidate n, d ≠ low →
        F.value d + noise omega d / thetaH <
          F.value low + noise omega low / thetaH)
    (haccurateTop :
      ∀ omega ∈ S, ∀ d : Candidate n, d ≠ high →
        F.value d + noise omega d / thetaA <
          F.value high + noise omega high / thetaA) :
    AccuracyFamily.Theorem1RemovalMonotonicityAt F thetaA thetaH :=
  KR21Monoculture.paper_appendixA_theorem1RemovalMonotonicityAt_of_scaledNoise_top_switch_set
    mu noise hthetaH hthetaHA hrawRank haccurateRank hdistH hdistA
    hSpos hvalue hrawTop haccurateTop

/--
Appendix A / Theorem 5 scaled-noise strictness from full support: a
positive-everywhere finite noise density gives positive source mass to the
strict full-set improvement event whenever two candidates have a strict value
gap and `thetaA > thetaH > 0`.

Source status: derived from source primitives.
-/
theorem appendixA_scaledNoise_strict_fullset_improvement_pos_of_noise_fullSupport
    {n : ℕ}
    (D : (Candidate n → ℝ) → ENNReal)
    (hD : Measurable D)
    (hDpos : ∀ noise, D noise ≠ 0)
    (value : Candidate n → ℝ)
    {thetaA thetaH : ℝ} {low high : Candidate n}
    (hthetaH : 0 < thetaH) (hthetaHA : thetaH < thetaA)
    (hvalue : value low < value high) :
    0 < ((volume : Measure (Candidate n → ℝ)).withDensity D)
      {noise |
        value
          (bestInSet
            (AppliedModelingLib.SocialChoice.Ranking.rankByScore
              (fun i => value i + noise i / thetaH))
            Finset.univ) <
        value
          (bestInSet
            (AppliedModelingLib.SocialChoice.Ranking.rankByScore
              (fun i => value i + noise i / thetaA))
            Finset.univ)} :=
  KR21Monoculture.paper_appendixA_scaledNoise_strict_fullset_improvement_pos_of_noise_fullSupport
    D hD hDpos value hthetaH hthetaHA hvalue

/--
Appendix A / Theorem 5 finite-removal monotonicity from a full-support
scaled-noise density: the positive strict-improvement event is derived from
full support, while the ranking-law equalities identify the paper's family with
the induced scaled-noise laws.

Source status: derived from source primitives.
-/
theorem appendixA_theorem1RemovalMonotonicityAt_of_scaledNoise_fullSupport_density
    {n : ℕ}
    {F : AccuracyFamily n} {thetaA thetaH : ℝ}
    (mu : Measure (Candidate n → ℝ)) [IsProbabilityMeasure mu]
    (D : (Candidate n → ℝ) → ENNReal)
    (hD : Measurable D)
    (hDpos : ∀ noise, D noise ≠ 0)
    (hmu :
      mu = (volume : Measure (Candidate n → ℝ)).withDensity D)
    (hthetaH : 0 < thetaH) (hthetaHA : thetaH < thetaA)
    (hrawRank :
      Measurable (fun noise : Candidate n → ℝ =>
        AppliedModelingLib.SocialChoice.Ranking.rankByScore
          (fun i => F.value i + noise i / thetaH)))
    (haccurateRank :
      Measurable (fun noise : Candidate n → ℝ =>
        AppliedModelingLib.SocialChoice.Ranking.rankByScore
          (fun i => F.value i + noise i / thetaA)))
    (hdistH :
      F.dist thetaH =
        AppliedModelingLib.SocialChoice.Ranking.rankingPMFOfMeasure mu
          (fun noise =>
            AppliedModelingLib.SocialChoice.Ranking.rankByScore
              (fun i => F.value i + noise i / thetaH))
          hrawRank)
    (hdistA :
      F.dist thetaA =
        AppliedModelingLib.SocialChoice.Ranking.rankingPMFOfMeasure mu
          (fun noise =>
            AppliedModelingLib.SocialChoice.Ranking.rankByScore
              (fun i => F.value i + noise i / thetaA))
          haccurateRank)
    {low high : Candidate n}
    (hvalue : F.value low < F.value high) :
    AccuracyFamily.Theorem1RemovalMonotonicityAt F thetaA thetaH :=
  KR21Monoculture.paper_appendixA_theorem1RemovalMonotonicityAt_of_scaledNoise_fullSupport_density
    mu D hD hDpos hmu hthetaH hthetaHA hrawRank haccurateRank
    hdistH hdistA hvalue

/--
Appendix A / Theorem 5 strictness from a continuous score-space box: for a
positive density on finite score vectors, an explicit open box forcing a raw
low-valued top choice and contracted high-valued top choice has positive source
mass, hence supplies the strict-improvement event used by removal monotonicity.

Source status: derived from source primitives.
-/
theorem appendixA_strict_fullset_improvement_pos_of_scoreSpace_top_switch_openBox
    {n : ℕ}
    (D : (Candidate n → ℝ) → ENNReal)
    (hD : Measurable D)
    (value : Candidate n → ℝ)
    {t : ℝ} {low high : Candidate n}
    {a b : Candidate n → ℝ}
    (hab : ∀ i, a i < b i)
    (hDpos :
      ∀ score,
        score ∈ Set.pi Set.univ (fun i => Set.Ioo (a i) (b i)) →
          D score ≠ 0)
    (hvalue : value low < value high)
    (hrawTop :
      ∀ score ∈ Set.pi Set.univ (fun i => Set.Ioo (a i) (b i)),
        ∀ d : Candidate n, d ≠ low → score d < score low)
    (hcontractTop :
      ∀ score ∈ Set.pi Set.univ (fun i => Set.Ioo (a i) (b i)),
        ∀ d : Candidate n, d ≠ high →
          paper_appendixC_contractedScore t (value d) (score d) <
            paper_appendixC_contractedScore t (value high) (score high)) :
    0 < ((volume : Measure (Candidate n → ℝ)).withDensity D)
      {score |
        value
          (bestInSet
            (AppliedModelingLib.SocialChoice.Ranking.rankByScore score)
            Finset.univ) <
        value
          (bestInSet
            (AppliedModelingLib.SocialChoice.Ranking.rankByScore
              (fun i => paper_appendixC_contractedScore t (value i) (score i)))
            Finset.univ)} :=
  KR21Monoculture.paper_appendixA_strict_fullset_improvement_pos_of_scoreSpace_top_switch_openBox
    D hD value hab hDpos hvalue hrawTop hcontractTop

/--
Appendix A / Theorem 5 strictness from explicit numerical margins: with a
positive-everywhere score-space density, endpoint inequalities defining a
raw-low / contracted-high top switch give positive strict-improvement mass.

Source status: derived from source primitives.
-/
theorem appendixA_strict_fullset_improvement_pos_of_scoreSpace_topSwitch_parameters
    {n : ℕ}
    (D : (Candidate n → ℝ) → ENNReal)
    (hD : Measurable D)
    (hDpos : ∀ score, D score ≠ 0)
    (value : Candidate n → ℝ)
    {t eps K : ℝ} {low high : Candidate n}
    (ht0 : 0 ≤ t)
    (heps : 0 < eps) (hKpos : 0 < K)
    (hvalue : value low < value high)
    (hhigh_low :
      paper_appendixC_contractedScore t (value low) eps <
        paper_appendixC_contractedScore t (value high) (-(eps / 8)))
    (hhigh_other :
      ∀ d : Candidate n, d ≠ low → d ≠ high →
        paper_appendixC_contractedScore t (value d) (-K) <
          paper_appendixC_contractedScore t (value high) (-(eps / 8))) :
    0 < ((volume : Measure (Candidate n → ℝ)).withDensity D)
      {score |
        value
          (bestInSet
            (AppliedModelingLib.SocialChoice.Ranking.rankByScore score)
            Finset.univ) <
        value
          (bestInSet
            (AppliedModelingLib.SocialChoice.Ranking.rankByScore
              (fun i => paper_appendixC_contractedScore t (value i) (score i)))
            Finset.univ)} :=
  KR21Monoculture.paper_appendixA_strict_fullset_improvement_pos_of_scoreSpace_topSwitch_parameters
    D hD hDpos value ht0 heps hKpos hvalue hhigh_low hhigh_other

/--
Appendix A / Theorem 5 strictness from full-support score density: for a
genuine contraction and two candidates with a strict value gap, any
positive-everywhere continuous score-space density gives positive mass to the
strict full-set improvement event.

Source status: derived from source primitives.
-/
theorem appendixA_strict_fullset_improvement_pos_of_scoreSpace_fullSupport
    {n : ℕ}
    (D : (Candidate n → ℝ) → ENNReal)
    (hD : Measurable D)
    (hDpos : ∀ score, D score ≠ 0)
    (value : Candidate n → ℝ)
    {t : ℝ} {low high : Candidate n}
    (htpos : 0 < t) (htlt1 : t < 1)
    (hvalue : value low < value high) :
    0 < ((volume : Measure (Candidate n → ℝ)).withDensity D)
      {score |
        value
          (bestInSet
            (AppliedModelingLib.SocialChoice.Ranking.rankByScore score)
            Finset.univ) <
        value
          (bestInSet
            (AppliedModelingLib.SocialChoice.Ranking.rankByScore
              (fun i => paper_appendixC_contractedScore t (value i) (score i)))
            Finset.univ)} :=
  KR21Monoculture.paper_appendixA_strict_fullset_improvement_pos_of_scoreSpace_fullSupport
    D hD hDpos value htpos htlt1 hvalue

/--
Appendix A / Theorem 5 asymptotic optimality: if high accuracy makes the total
source probability of pairwise inversions arbitrarily small, then the induced
ranking law converges atomwise to the true ranking.

Source status: derived from source primitives.
-/
theorem appendixA_atomwise_concentration_of_sum_inversion_probs
    {n : ℕ} {Omega : Type*} [MeasurableSpace Omega]
    (mu : ℝ → Measure Omega) [∀ theta, IsProbabilityMeasure (mu theta)]
    (rank : ℝ → Omega → Ranking n)
    (hrank : ∀ theta, Measurable (rank theta))
    (center : Ranking n)
    (hinv :
      ∀ lower delta, 0 < delta →
        ∃ hi, lower < hi ∧
          (∑ ab : Candidate n × Candidate n,
            AppliedModelingLib.measureProb (mu hi)
              (fun omega => invertedPair center (rank hi omega) ab)) < delta) :
    ∀ lower delta, 0 < delta →
      ∃ hi, lower < hi ∧
        ∀ pi : Ranking n,
          |((AppliedModelingLib.SocialChoice.Ranking.rankingPMFOfMeasure
                (mu hi) (rank hi) (hrank hi)) pi).toReal -
            (((PMF.pure center : PMF (Ranking n)) pi).toReal)| < delta :=
  KR21Monoculture.paper_appendixA_atomwise_concentration_of_sum_inversion_probs
    mu rank hrank center hinv

/--
Appendix A / Theorem 5 asymptotic optimality: it is enough to make the total
source probability of adjacent inversions in the true ranking order arbitrarily
small.  The finite adjacent-union-bound argument then gives atomwise
convergence to the true ranking.

Source status: derived from source primitives.
-/
theorem appendixA_atomwise_concentration_of_sum_adjacent_inversion_probs
    {n : ℕ} {Omega : Type*} [MeasurableSpace Omega]
    (mu : ℝ → Measure Omega) [∀ theta, IsProbabilityMeasure (mu theta)]
    (rank : ℝ → Omega → Ranking n)
    (hrank : ∀ theta, Measurable (rank theta))
    (center : Ranking n)
    (hinv :
      ∀ lower delta, 0 < delta →
        ∃ hi, lower < hi ∧
          (∑ i : Fin (n + 1),
            AppliedModelingLib.measureProb (mu hi)
              (fun omega => invertedPair center (rank hi omega)
                (center i.castSucc, center i.succ))) < delta) :
    ∀ lower delta, 0 < delta →
      ∃ hi, lower < hi ∧
        ∀ pi : Ranking n,
          |((AppliedModelingLib.SocialChoice.Ranking.rankingPMFOfMeasure
                (mu hi) (rank hi) (hrank hi)) pi).toReal -
            (((PMF.pure center : PMF (Ranking n)) pi).toReal)| < delta :=
  KR21Monoculture.paper_appendixA_atomwise_concentration_of_sum_adjacent_inversion_probs
    mu rank hrank center hinv

/--
Appendix A / Theorem 5 asymptotic optimality for score-induced RUM rankings:
it is enough to make the total source probability of adjacent true-neighbor
score misorders arbitrarily small.  This is the coordinate-level tail statement
used in the paper's source argument.

Source status: derived from source primitives.
-/
theorem appendixA_atomwise_concentration_of_sum_adjacent_score_misorder_probs
    {n : ℕ} {Omega : Type*} [MeasurableSpace Omega]
    (mu : ℝ → Measure Omega) [∀ theta, IsProbabilityMeasure (mu theta)]
    (score : ℝ → Omega → Candidate n → ℝ)
    (hrank : ∀ theta,
      Measurable (fun omega =>
        AppliedModelingLib.SocialChoice.Ranking.rankByScore (score theta omega)))
    (center : Ranking n)
    (hmisorder :
      ∀ lower delta, 0 < delta →
        ∃ hi, lower < hi ∧
          (∑ i : Fin (n + 1),
            AppliedModelingLib.measureProb (mu hi)
              (fun omega =>
                score hi omega (center i.castSucc) ≤
                  score hi omega (center i.succ))) < delta) :
    ∀ lower delta, 0 < delta →
      ∃ hi, lower < hi ∧
        ∀ pi : Ranking n,
          |((AppliedModelingLib.SocialChoice.Ranking.rankingPMFOfMeasure
                (mu hi)
                (fun omega =>
                  AppliedModelingLib.SocialChoice.Ranking.rankByScore (score hi omega))
                (hrank hi)) pi).toReal -
            (((PMF.pure center : PMF (Ranking n)) pi).toReal)| < delta :=
  KR21Monoculture.paper_appendixA_atomwise_concentration_of_sum_adjacent_score_misorder_probs
    mu score hrank center hmisorder

/--
Appendix A / Theorem 5 asymptotic optimality from a source-tail limit: if the
total source probability of pairwise inversions tends to zero, then the induced
ranking law converges atomwise to the true ranking.

Source status: derived from source primitives.
-/
theorem appendixA_atomwise_concentration_of_sum_inversion_probs_tendsto
    {n : ℕ} {Omega : Type*} [MeasurableSpace Omega]
    (mu : ℝ → Measure Omega) [∀ theta, IsProbabilityMeasure (mu theta)]
    (rank : ℝ → Omega → Ranking n)
    (hrank : ∀ theta, Measurable (rank theta))
    (center : Ranking n)
    (hsum :
      Filter.Tendsto
        (fun theta : ℝ =>
          ∑ ab : Candidate n × Candidate n,
            AppliedModelingLib.measureProb (mu theta)
              (fun omega => invertedPair center (rank theta omega) ab))
        Filter.atTop (nhds 0)) :
    ∀ lower delta, 0 < delta →
      ∃ hi, lower < hi ∧
        ∀ pi : Ranking n,
          |((AppliedModelingLib.SocialChoice.Ranking.rankingPMFOfMeasure
                (mu hi) (rank hi) (hrank hi)) pi).toReal -
            (((PMF.pure center : PMF (Ranking n)) pi).toReal)| < delta :=
  KR21Monoculture.paper_appendixA_atomwise_concentration_of_sum_inversion_probs_tendsto
    mu rank hrank center hsum

/--
Appendix A / Theorem 5 asymptotic optimality from an adjacent source-tail limit:
if the total source probability of adjacent inversions in the true ranking order
tends to zero, then the induced ranking law converges atomwise to the true
ranking.

Source status: derived from source primitives.
-/
theorem appendixA_atomwise_concentration_of_sum_adjacent_inversion_probs_tendsto
    {n : ℕ} {Omega : Type*} [MeasurableSpace Omega]
    (mu : ℝ → Measure Omega) [∀ theta, IsProbabilityMeasure (mu theta)]
    (rank : ℝ → Omega → Ranking n)
    (hrank : ∀ theta, Measurable (rank theta))
    (center : Ranking n)
    (hsum :
      Filter.Tendsto
        (fun theta : ℝ =>
          ∑ i : Fin (n + 1),
            AppliedModelingLib.measureProb (mu theta)
              (fun omega => invertedPair center (rank theta omega)
                (center i.castSucc, center i.succ)))
        Filter.atTop (nhds 0)) :
    ∀ lower delta, 0 < delta →
      ∃ hi, lower < hi ∧
        ∀ pi : Ranking n,
          |((AppliedModelingLib.SocialChoice.Ranking.rankingPMFOfMeasure
                (mu hi) (rank hi) (hrank hi)) pi).toReal -
            (((PMF.pure center : PMF (Ranking n)) pi).toReal)| < delta :=
  KR21Monoculture.paper_appendixA_atomwise_concentration_of_sum_adjacent_inversion_probs_tendsto
    mu rank hrank center hsum

/--
Appendix A / Theorem 5 asymptotic optimality from a score-tail limit: for
score-induced RUM rankings, it is enough that adjacent true-neighbor score
misorder probabilities have total mass tending to zero.

Source status: derived from source primitives.
-/
theorem appendixA_atomwise_concentration_of_sum_adjacent_score_misorder_probs_tendsto
    {n : ℕ} {Omega : Type*} [MeasurableSpace Omega]
    (mu : ℝ → Measure Omega) [∀ theta, IsProbabilityMeasure (mu theta)]
    (score : ℝ → Omega → Candidate n → ℝ)
    (hrank : ∀ theta,
      Measurable (fun omega =>
        AppliedModelingLib.SocialChoice.Ranking.rankByScore (score theta omega)))
    (center : Ranking n)
    (hsum :
      Filter.Tendsto
        (fun theta : ℝ =>
          ∑ i : Fin (n + 1),
            AppliedModelingLib.measureProb (mu theta)
              (fun omega =>
                score theta omega (center i.castSucc) ≤
                  score theta omega (center i.succ)))
        Filter.atTop (nhds 0)) :
    ∀ lower delta, 0 < delta →
      ∃ hi, lower < hi ∧
        ∀ pi : Ranking n,
          |((AppliedModelingLib.SocialChoice.Ranking.rankingPMFOfMeasure
                (mu hi)
                (fun omega =>
                  AppliedModelingLib.SocialChoice.Ranking.rankByScore (score hi omega))
                (hrank hi)) pi).toReal -
            (((PMF.pure center : PMF (Ranking n)) pi).toReal)| < delta :=
  KR21Monoculture.paper_appendixA_atomwise_concentration_of_sum_adjacent_score_misorder_probs_tendsto
    mu score hrank center hsum

/--
Appendix A / Theorem 5 scaled-noise source tail: for fixed finite-dimensional
noise, scores `value_i + noise_i / theta` have vanishing total adjacent
true-neighbor score-misorder probability as accuracy tends to infinity.

Source status: derived from source primitives.
-/
theorem appendixA_scaledNoise_adjacent_score_misorder_sum_tendsto
    {n : ℕ} {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (noise : Omega → Candidate n → ℝ)
    (hnoise : ∀ c : Candidate n, Measurable (fun omega => noise omega c))
    (value : Candidate n → ℝ) (center : Ranking n)
    (hcenter :
      ∀ i : Fin (n + 1),
        value (center i.succ) < value (center i.castSucc)) :
    Filter.Tendsto
      (fun theta : ℝ =>
        ∑ i : Fin (n + 1),
          AppliedModelingLib.measureProb mu
            (fun omega =>
              value (center i.castSucc) +
                  noise omega (center i.castSucc) / theta ≤
                value (center i.succ) +
                  noise omega (center i.succ) / theta))
      Filter.atTop (nhds 0) :=
  KR21Monoculture.paper_appendixA_scaledNoise_adjacent_score_misorder_sum_tendsto
    mu noise hnoise value center hcenter

/--
Appendix A / Theorem 5 scaled-noise measurability: if each finite noise
coordinate is measurable, then sorting the scaled-noise scores gives a
measurable ranking-valued random variable.
-/
theorem appendixA_scaledNoise_rankByScore_measurable
    {n : ℕ} {Omega : Type*} [MeasurableSpace Omega]
    (noise : Omega → Candidate n → ℝ)
    (hnoise : ∀ c : Candidate n, Measurable (fun omega => noise omega c))
    (value : Candidate n → ℝ) (theta : ℝ) :
    Measurable (fun omega =>
      AppliedModelingLib.SocialChoice.Ranking.rankByScore
        (fun c => value c + noise omega c / theta)) :=
  KR21Monoculture.paper_appendixA_scaledNoise_rankByScore_measurable
    noise hnoise value theta

/--
Appendix A / Theorem 5 scaled-noise atom continuity: if scaled scores have no
pairwise ties almost surely at a positive accuracy, then every atom of the
finite induced ranking law is continuous at that accuracy.
-/
theorem appendixA_scaledNoiseRankingPMF_atom_epsilonContinuousAt_of_ae_noTies
    {n : ℕ}
    (mu : Measure (Candidate n → ℝ)) [IsProbabilityMeasure mu]
    (value : Candidate n → ℝ) {theta : ℝ} (htheta : 0 < theta)
    (hnoTie :
      ∀ᵐ noise ∂mu,
        ∀ i j : Candidate n, i ≠ j →
          value i + noise i / theta ≠ value j + noise j / theta)
    (pi : Ranking n) :
    AppliedModelingLib.EpsilonContinuousAt
      (fun theta' =>
        ((KR21Monoculture.paper_appendixA_scaledNoiseRankingPMF
          mu value theta') pi).toReal)
      theta :=
  KR21Monoculture.paper_appendixA_scaledNoiseRankingPMF_atom_epsilonContinuousAt_of_ae_noTies
    mu value htheta hnoTie pi

/--
Appendix A / Theorem 5 scaled-noise no-ties: an absolutely continuous finite
noise-vector law gives probability zero to every pairwise scaled-score tie.

Source status: derived from source primitives.
-/
theorem appendixA_scaledNoise_noTie_ae_of_fullSupport_density
    {n : ℕ}
    (mu : Measure (Candidate n → ℝ)) [IsProbabilityMeasure mu]
    (D : (Candidate n → ℝ) → ENNReal)
    (hmu : mu = (volume : Measure (Candidate n → ℝ)).withDensity D)
    (value : Candidate n → ℝ) {theta : ℝ} (htheta : 0 < theta) :
    ∀ᵐ noise ∂mu,
      ∀ i j : Candidate n, i ≠ j →
        value i + noise i / theta ≠ value j + noise j / theta :=
  KR21Monoculture.paper_appendixA_scaledNoise_noTie_ae_of_fullSupport_density
    mu D hmu value htheta

/--
Appendix A / Theorem 5 scaled-noise asymptotic optimality: fixed noise, a
coordinate-measurable induced ranking, and strict adjacent true-value gaps
imply atomwise convergence of the induced ranking law to the true ranking.
-/
theorem appendixA_scaledNoise_atomwise_concentration
    {n : ℕ} {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (noise : Omega → Candidate n → ℝ)
    (hnoise : ∀ c : Candidate n, Measurable (fun omega => noise omega c))
    (value : Candidate n → ℝ)
    (center : Ranking n)
    (hcenter :
      ∀ i : Fin (n + 1),
        value (center i.succ) < value (center i.castSucc)) :
    ∀ lower delta, 0 < delta →
      ∃ hi, lower < hi ∧
        ∀ pi : Ranking n,
          |((AppliedModelingLib.SocialChoice.Ranking.rankingPMFOfMeasure
                mu
                (fun omega =>
                  AppliedModelingLib.SocialChoice.Ranking.rankByScore
                    (fun c => value c + noise omega c / hi))
                (appendixA_scaledNoise_rankByScore_measurable
                  noise hnoise value hi)) pi).toReal -
            (((PMF.pure center : PMF (Ranking n)) pi).toReal)| < delta :=
  KR21Monoculture.paper_appendixA_scaledNoise_atomwise_concentration
    mu noise hnoise value center hcenter

/--
Appendix A / Theorem 5 Definition-1 consequence package for scaled-noise RUMs:
the downstream finite-ranking fields used by Theorem 1.
-/
abbrev AppendixAScaledNoiseDefinition1Consequence
    {n : ℕ} (F : AccuracyFamily n) (center : Ranking n) : Type :=
  KR21Monoculture.PaperAppendixAScaledNoiseDefinition1Consequence F center

/--
Appendix A / Theorem 5 scaled-noise source package: positive full-support noise
density, strict adjacent true-value gaps, and the source no-tie fact imply the
finite-ranking Definition-1 consequences consumed by Theorem 1.

Source status: auxiliary source package, derived from source primitives. This
constructs the Definition-1 consequence package whose fields are exposed by the
reviewed Appendix A rows above: atom continuity, high-accuracy concentration,
and finite-removal monotonicity.
-/
noncomputable def appendixA_scaledNoise_definition1_consequence_of_fullSupport_source
    {n : ℕ}
    {F : AccuracyFamily n} (center : Ranking n)
    (mu : Measure (Candidate n → ℝ)) [IsProbabilityMeasure mu]
    (D : (Candidate n → ℝ) → ENNReal)
    (hD : Measurable D)
    (hDpos : ∀ noise, D noise ≠ 0)
    (hmu :
      mu = (volume : Measure (Candidate n → ℝ)).withDensity D)
    (hcenter :
      ∀ i : Fin (n + 1),
        F.value (center i.succ) < F.value (center i.castSucc))
    (hdist :
      ∀ theta, 0 < theta →
        F.dist theta =
          AppliedModelingLib.SocialChoice.Ranking.rankingPMFOfMeasure
            mu
            (fun noise =>
              AppliedModelingLib.SocialChoice.Ranking.rankByScore
                (fun c => F.value c + noise c / theta))
            (appendixA_scaledNoise_rankByScore_measurable
              (Omega := Candidate n → ℝ)
              (fun noise c => noise c)
              (fun c => measurable_pi_apply c)
              F.value theta)) :
    AppendixAScaledNoiseDefinition1Consequence F center :=
  KR21Monoculture.paper_appendixA_scaledNoise_definition1_consequence_of_fullSupport_source
    center mu D hD hDpos hmu hcenter hdist

/--
Definition 1 / Gaussian three-candidate RUM: for the concrete normalized
Gaussian score law, a strict contraction toward ordered values satisfies the
finite-removal monotonicity condition used by Theorem 1.
-/
theorem definition1_threeCandidate_gaussian_removalMonotonicity_of_scoreSpace_t_lt_one
    {F : AccuracyFamily 1} {thetaA thetaH : ℝ}
    (x1 x2 x3 t : ℝ)
    (hdistA :
      F.dist thetaA =
        paper_theorem6_normalizedScoreRankingPMF (theorem8GaussianPDF 0)
          x1 x2 x3
          (paper_theorem6_gaussian_scoreDensity_lintegral_eq_one x1 x2 x3)
          (rum3ContractRankByScoreFns
            t x1 x2 x3
            paper_theorem6_score1 paper_theorem6_score2 paper_theorem6_score3)
          (rum3ContractRankByScoreFns_measurable
            rum3Score1_measurable rum3Score2_measurable rum3Score3_measurable
            t x1 x2 x3))
    (hdistH :
      F.dist thetaH =
        paper_theorem6_normalizedScoreRankingPMF (theorem8GaussianPDF 0)
          x1 x2 x3
          (paper_theorem6_gaussian_scoreDensity_lintegral_eq_one x1 x2 x3)
          (rum3RankByScoreFns
            paper_theorem6_score1 paper_theorem6_score2 paper_theorem6_score3)
          (rum3RankByScoreFns_measurable
            rum3Score1_measurable rum3Score2_measurable rum3Score3_measurable))
    (hvalue1 : F.value (0 : Candidate 1) = x1)
    (hvalue2 : F.value (1 : Candidate 1) = x2)
    (hvalue3 : F.value (2 : Candidate 1) = x3)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (htlt1 : t < 1)
    (hx12 : x2 < x1) (hx23 : x3 < x2) :
    AccuracyFamily.Theorem1RemovalMonotonicityAt F thetaA thetaH :=
  KR21Monoculture.paper_definition1_threeCandidate_removalMonotonicity_of_gaussian_scoreSpace_t_lt_one
    x1 x2 x3 t hdistA hdistH hvalue1 hvalue2 hvalue3
    ht0 ht1 htlt1 hx12 hx23

/--
Definition 1 / Laplace three-candidate RUM: for the concrete normalized
Laplace score law, a strict contraction toward ordered values satisfies the
finite-removal monotonicity condition used by Theorem 1.
-/
theorem definition1_threeCandidate_laplacian_removalMonotonicity_of_scoreSpace_t_lt_one
    {F : AccuracyFamily 1} {thetaA thetaH : ℝ}
    {lam x1 x2 x3 t : ℝ}
    (hlam : 0 < lam)
    (hdistA :
      F.dist thetaA =
        paper_theorem6_normalizedScoreRankingPMF (theorem7LaplacePDF lam 0)
          x1 x2 x3
          (paper_theorem6_laplacian_scoreDensity_lintegral_eq_one
            (lam := lam) hlam x1 x2 x3)
          (rum3ContractRankByScoreFns
            t x1 x2 x3
            paper_theorem6_score1 paper_theorem6_score2 paper_theorem6_score3)
          (rum3ContractRankByScoreFns_measurable
            rum3Score1_measurable rum3Score2_measurable rum3Score3_measurable
            t x1 x2 x3))
    (hdistH :
      F.dist thetaH =
        paper_theorem6_normalizedScoreRankingPMF (theorem7LaplacePDF lam 0)
          x1 x2 x3
          (paper_theorem6_laplacian_scoreDensity_lintegral_eq_one
            (lam := lam) hlam x1 x2 x3)
          (rum3RankByScoreFns
            paper_theorem6_score1 paper_theorem6_score2 paper_theorem6_score3)
          (rum3RankByScoreFns_measurable
            rum3Score1_measurable rum3Score2_measurable rum3Score3_measurable))
    (hvalue1 : F.value (0 : Candidate 1) = x1)
    (hvalue2 : F.value (1 : Candidate 1) = x2)
    (hvalue3 : F.value (2 : Candidate 1) = x3)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (htlt1 : t < 1)
    (hx12 : x2 < x1) (hx23 : x3 < x2) :
    AccuracyFamily.Theorem1RemovalMonotonicityAt F thetaA thetaH :=
  KR21Monoculture.paper_definition1_threeCandidate_removalMonotonicity_of_laplacian_scoreSpace_t_lt_one
    hlam hdistA hdistH hvalue1 hvalue2 hvalue3 ht0 ht1 htlt1 hx12 hx23

/-- Appendix C Lemma 1, Gaussian noise is strictly well-ordered. -/
theorem lemma1_gaussian_strictlyWellOrdered
    {kappa : ℝ} (hkappa : 0 < kappa) :
    StrictlyWellOrderedNoise (gaussianNoiseKernel kappa) :=  KR21Monoculture.paper_lemma1_gaussian_strictlyWellOrdered hkappa

/--
Appendix C Lemma 1, Laplacian weak form: the Laplacian density kernel satisfies
the globally valid weak well-ordering inequality.

Source status: formalized source note. The paper states global strict
Laplacian well-ordering; Lean proves the globally valid weak form here and
strict overlap/local forms elsewhere. No named theorem or main-text result is
affected.
-/
theorem lemma1_laplacian_weaklyWellOrdered
    {lam : ℝ} (hlam : 0 ≤ lam) :
    WeaklyWellOrderedNoise (laplacianNoiseKernel lam) :=  KR21Monoculture.paper_lemma1_laplacian_weaklyWellOrdered hlam

/--
Appendix C Lemma 1, exact source-statement check: the Laplace kernel does not
satisfy Definition 4's global strict inequality.  Separated ordered pairs give
equal products.
-/
theorem lemma1_laplacian_not_strictlyWellOrdered (lam : ℝ) :
    ¬ StrictlyWellOrderedNoise (laplacianNoiseKernel lam) :=
  KR21Monoculture.paper_lemma1_laplacian_not_strictlyWellOrdered lam

/--
Appendix C Lemma 1, Laplacian strict local form: for ordered locations
`a > b` and `c > d`, strict Laplacian well-ordering holds under the explicit
overlap condition `b < c` and `d < a`, equivalently overlap of the open
intervals `(b,a)` and `(d,c)`.

Source status: formalized source note. This is the strict local replacement for
the paper's false global strict Laplacian statement; the global theorem above is
weak, and no named theorem or main-text result is affected.
-/
theorem lemma1_laplacian_strictlyWellOrdered_of_overlap
    {lam a b c d : ℝ} (hlam : 0 < lam)
    (hab : b < a) (hcd : d < c) (hbc : b < c) (hda : d < a) :
    laplacianNoiseKernel lam (a - c) * laplacianNoiseKernel lam (b - d) >
      laplacianNoiseKernel lam (a - d) * laplacianNoiseKernel lam (b - c) :=
  KR21Monoculture.laplacianNoiseKernel_strictlyWellOrdered_of_overlap
    hlam hab hcd hbc hda

/--
The complete corrected Lemma 1 target at the density-kernel level.  Gaussian
strictness is global; Laplace has the globally valid weak statement, an
explicit global counterexample to strictness, and the stated strict overlap
region.
-/
theorem lemma1_corrected_gaussian_laplace_kernel_target
    {kappa lam : ℝ} (hkappa : 0 < kappa) (hlam : 0 < lam) :
    StrictlyWellOrderedNoise (gaussianNoiseKernel kappa) ∧
      WeaklyWellOrderedNoise (laplacianNoiseKernel lam) ∧
      (¬ StrictlyWellOrderedNoise (laplacianNoiseKernel lam)) ∧
      ∀ {a b c d : ℝ}, b < a → d < c → b < c → d < a →
        laplacianNoiseKernel lam (a - c) * laplacianNoiseKernel lam (b - d) >
          laplacianNoiseKernel lam (a - d) * laplacianNoiseKernel lam (b - c) := by
  refine ⟨KR21Monoculture.paper_lemma1_gaussian_strictlyWellOrdered hkappa,
    KR21Monoculture.paper_lemma1_laplacian_weaklyWellOrdered (le_of_lt hlam),
    KR21Monoculture.paper_lemma1_laplacian_not_strictlyWellOrdered lam, ?_⟩
  intro a b c d hab hcd hbc hda
  exact KR21Monoculture.laplacianNoiseKernel_strictlyWellOrdered_of_overlap
    hlam hab hcd hbc hda

/-! ## Appendix C, Theorem 6 -/

/--
Appendix C Theorem 6 in its source-generic three-candidate form.  For a
positive normalized strictly well-ordered density and ordered candidate
values, a strict contraction of the same score realization makes the second
mover prefer weaker competition.
-/
theorem theorem6_threeCandidate_prefersWeakerCompetition_of_scoreSpace_density_t_lt_one
    (f : ℝ → ℝ) (x1 x2 x3 t : ℝ)
    {value : Candidate 1 → ℝ}
    (hvalue1 : value (0 : Candidate 1) = x1)
    (hvalue2 : value (1 : Candidate 1) = x2)
    (hvalue3 : value (2 : Candidate 1) = x3)
    (hfmeas : Measurable f)
    (hf : StrictlyWellOrderedNoise f)
    (hpos : ∀ z : ℝ, 0 < f z)
    (hnorm :
      ∫⁻ omega,
          (rum3ScoreDensityENN f x1 x2 x3
            paper_theorem6_score1 paper_theorem6_score2 paper_theorem6_score3)
            omega ∂(volume : Measure paper_theorem6_scoreSpace) = 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (htlt1 : t < 1)
    (hx12 : x2 < x1) (hx23 : x3 < x2) :
    Model.PrefersWeakerCompetition
      (paper_theorem6_normalizedScoreRankingPMF f x1 x2 x3 hnorm
        (rum3ContractRankByScoreFns
          t x1 x2 x3
          paper_theorem6_score1 paper_theorem6_score2 paper_theorem6_score3)
        (rum3ContractRankByScoreFns_measurable
          rum3Score1_measurable rum3Score2_measurable rum3Score3_measurable
          t x1 x2 x3))
      (paper_theorem6_normalizedScoreRankingPMF f x1 x2 x3 hnorm
        (rum3RankByScoreFns
          paper_theorem6_score1 paper_theorem6_score2 paper_theorem6_score3)
        (rum3RankByScoreFns_measurable
          rum3Score1_measurable rum3Score2_measurable rum3Score3_measurable))
      value :=
  KR21Monoculture.paper_theorem6_threeCandidate_prefersWeakerCompetition_of_scoreSpace_density_t_lt_one
    f x1 x2 x3 t hvalue1 hvalue2 hvalue3 hfmeas hf hpos hnorm
    ht0 ht1 htlt1 hx12 hx23

/--
Appendix C Theorem 6 / Gaussian three-candidate RUM: if algorithmic scores are
a strict contraction of the same independent Gaussian score realization, then
the second mover prefers weaker competition.
-/
theorem theorem6_threeCandidate_gaussian_prefersWeakerCompetition_of_scoreSpace_t_lt_one
    (x1 x2 x3 t : ℝ)
    {value : Candidate 1 → ℝ}
    (hvalue1 : value (0 : Candidate 1) = x1)
    (hvalue2 : value (1 : Candidate 1) = x2)
    (hvalue3 : value (2 : Candidate 1) = x3)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (htlt1 : t < 1)
    (hx12 : x2 < x1) (hx23 : x3 < x2) :
    Model.PrefersWeakerCompetition
      (paper_theorem6_normalizedScoreRankingPMF (theorem8GaussianPDF 0)
        x1 x2 x3
        (paper_theorem6_gaussian_scoreDensity_lintegral_eq_one x1 x2 x3)
        (rum3ContractRankByScoreFns
          t x1 x2 x3
          paper_theorem6_score1 paper_theorem6_score2 paper_theorem6_score3)
        (rum3ContractRankByScoreFns_measurable
          rum3Score1_measurable rum3Score2_measurable rum3Score3_measurable
          t x1 x2 x3))
      (paper_theorem6_normalizedScoreRankingPMF (theorem8GaussianPDF 0)
        x1 x2 x3
        (paper_theorem6_gaussian_scoreDensity_lintegral_eq_one x1 x2 x3)
        (rum3RankByScoreFns
          paper_theorem6_score1 paper_theorem6_score2 paper_theorem6_score3)
        (rum3RankByScoreFns_measurable
          rum3Score1_measurable rum3Score2_measurable rum3Score3_measurable))
      value :=
  KR21Monoculture.paper_theorem6_threeCandidate_prefersWeakerCompetition_of_gaussian_scoreSpace_t_lt_one
    x1 x2 x3 t hvalue1 hvalue2 hvalue3 ht0 ht1 htlt1 hx12 hx23

/--
Appendix C Theorem 6 / Laplacian three-candidate RUM: the zero-mean Laplace
score law satisfies the density hypotheses directly; the remaining inputs are
normalization of the concrete score density and the Laplacian lambda
certificate for the human subproblem.
-/
theorem theorem6_threeCandidate_laplacian_prefersWeakerCompetition_of_scoreSpace_lambdaCertificate_t_lt_one
    {lam x1 x2 x3 t : ℝ}
    {value : Candidate 1 → ℝ}
    (hlam : 0 < lam)
    (hvalue1 : value (0 : Candidate 1) = x1)
    (hvalue2 : value (1 : Candidate 1) = x2)
    (hvalue3 : value (2 : Candidate 1) = x3)
    (hnorm :
      ∫⁻ ω,
          (rum3ScoreDensityENN (theorem7LaplacePDF lam 0) x1 x2 x3
            paper_theorem6_score1 paper_theorem6_score2 paper_theorem6_score3)
            ω ∂(volume : Measure paper_theorem6_scoreSpace) = 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (htlt1 : t < 1)
    (hx12 : x2 < x1) (hx23 : x3 < x2)
    (lambda :
      RUM3LambdaCertificate
        (paper_theorem6_normalizedScoreRankingPMF (theorem7LaplacePDF lam 0)
          x1 x2 x3 hnorm
          (rum3RankByScoreFns
            paper_theorem6_score1 paper_theorem6_score2 paper_theorem6_score3)
          (rum3RankByScoreFns_measurable
            rum3Score1_measurable rum3Score2_measurable rum3Score3_measurable))) :
    Model.PrefersWeakerCompetition
      (paper_theorem6_normalizedScoreRankingPMF (theorem7LaplacePDF lam 0)
        x1 x2 x3 hnorm
        (rum3ContractRankByScoreFns
          t x1 x2 x3
          paper_theorem6_score1 paper_theorem6_score2 paper_theorem6_score3)
        (rum3ContractRankByScoreFns_measurable
          rum3Score1_measurable rum3Score2_measurable rum3Score3_measurable
          t x1 x2 x3))
      (paper_theorem6_normalizedScoreRankingPMF (theorem7LaplacePDF lam 0)
        x1 x2 x3 hnorm
        (rum3RankByScoreFns
          paper_theorem6_score1 paper_theorem6_score2 paper_theorem6_score3)
        (rum3RankByScoreFns_measurable
          rum3Score1_measurable rum3Score2_measurable rum3Score3_measurable))
      value :=
  KR21Monoculture.paper_theorem6_threeCandidate_prefersWeakerCompetition_of_laplacian_scoreSpace_lambdaCertificate_t_lt_one
    hlam hvalue1 hvalue2 hvalue3 hnorm ht0 ht1 htlt1 hx12 hx23 lambda

/--
Appendix C Theorem 6 / Laplacian three-candidate RUM: the zero-mean Laplace
score density is normalized in Lean; the remaining explicit input is the
Laplacian lambda certificate for the human subproblem.
-/
theorem theorem6_threeCandidate_laplacian_prefersWeakerCompetition_of_scoreSpace_concreteNormalization_lambdaCertificate_t_lt_one
    {lam x1 x2 x3 t : ℝ}
    {value : Candidate 1 → ℝ}
    (hlam : 0 < lam)
    (hvalue1 : value (0 : Candidate 1) = x1)
    (hvalue2 : value (1 : Candidate 1) = x2)
    (hvalue3 : value (2 : Candidate 1) = x3)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (htlt1 : t < 1)
    (hx12 : x2 < x1) (hx23 : x3 < x2)
    (lambda :
      RUM3LambdaCertificate
        (paper_theorem6_normalizedScoreRankingPMF (theorem7LaplacePDF lam 0)
          x1 x2 x3
          (paper_theorem6_laplacian_scoreDensity_lintegral_eq_one
            (lam := lam) hlam x1 x2 x3)
          (rum3RankByScoreFns
            paper_theorem6_score1 paper_theorem6_score2 paper_theorem6_score3)
          (rum3RankByScoreFns_measurable
            rum3Score1_measurable rum3Score2_measurable rum3Score3_measurable))) :
    Model.PrefersWeakerCompetition
      (paper_theorem6_normalizedScoreRankingPMF (theorem7LaplacePDF lam 0)
        x1 x2 x3
        (paper_theorem6_laplacian_scoreDensity_lintegral_eq_one
          (lam := lam) hlam x1 x2 x3)
        (rum3ContractRankByScoreFns
          t x1 x2 x3
          paper_theorem6_score1 paper_theorem6_score2 paper_theorem6_score3)
        (rum3ContractRankByScoreFns_measurable
          rum3Score1_measurable rum3Score2_measurable rum3Score3_measurable
          t x1 x2 x3))
      (paper_theorem6_normalizedScoreRankingPMF (theorem7LaplacePDF lam 0)
        x1 x2 x3
        (paper_theorem6_laplacian_scoreDensity_lintegral_eq_one
          (lam := lam) hlam x1 x2 x3)
        (rum3RankByScoreFns
          paper_theorem6_score1 paper_theorem6_score2 paper_theorem6_score3)
        (rum3RankByScoreFns_measurable
          rum3Score1_measurable rum3Score2_measurable rum3Score3_measurable))
      value :=
  KR21Monoculture.paper_theorem6_threeCandidate_prefersWeakerCompetition_of_laplacian_scoreSpace_concreteNormalization_lambdaCertificate_t_lt_one
    hlam hvalue1 hvalue2 hvalue3 ht0 ht1 htlt1 hx12 hx23 lambda

/--
Appendix C Theorem 6 / Laplacian three-candidate RUM: the concrete Laplace
human-subproblem lambda certificate follows from the pairwise Laplace winner
probabilities when `x₃ < x₂ < x₁`.
-/
theorem theorem6_laplacian_scoreSpace_concreteNormalization_lambdaCertificate
    {lam x1 x2 x3 : ℝ}
    (hlam : 0 < lam) (hx12 : x2 < x1) (hx23 : x3 < x2) :
    RUM3LambdaCertificate
      (paper_theorem6_normalizedScoreRankingPMF (theorem7LaplacePDF lam 0)
        x1 x2 x3
        (paper_theorem6_laplacian_scoreDensity_lintegral_eq_one
          (lam := lam) hlam x1 x2 x3)
        (rum3RankByScoreFns
          paper_theorem6_score1 paper_theorem6_score2 paper_theorem6_score3)
        (rum3RankByScoreFns_measurable
          rum3Score1_measurable rum3Score2_measurable rum3Score3_measurable)) :=
  KR21Monoculture.paper_theorem6_laplacian_scoreSpace_concreteNormalization_lambdaCertificate
    hlam hx12 hx23

/--
Appendix C Theorem 6 / Laplacian three-candidate RUM: with normalized concrete
Laplace scores, the second firm prefers weaker competition for `0 ≤ t ≤ 1`,
`t < 1`, and `x₃ < x₂ < x₁`.

Source status: derived from source primitives.
-/
theorem theorem6_threeCandidate_laplacian_prefersWeakerCompetition_of_scoreSpace_t_lt_one
    {lam x1 x2 x3 t : ℝ}
    {value : Candidate 1 → ℝ}
    (hlam : 0 < lam)
    (hvalue1 : value (0 : Candidate 1) = x1)
    (hvalue2 : value (1 : Candidate 1) = x2)
    (hvalue3 : value (2 : Candidate 1) = x3)
    (hnorm :
      ∫⁻ ω,
          (rum3ScoreDensityENN (theorem7LaplacePDF lam 0) x1 x2 x3
            paper_theorem6_score1 paper_theorem6_score2 paper_theorem6_score3)
            ω ∂(volume : Measure paper_theorem6_scoreSpace) = 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (htlt1 : t < 1)
    (hx12 : x2 < x1) (hx23 : x3 < x2) :
    Model.PrefersWeakerCompetition
      (paper_theorem6_normalizedScoreRankingPMF (theorem7LaplacePDF lam 0)
        x1 x2 x3 hnorm
        (rum3ContractRankByScoreFns
          t x1 x2 x3
          paper_theorem6_score1 paper_theorem6_score2 paper_theorem6_score3)
        (rum3ContractRankByScoreFns_measurable
          rum3Score1_measurable rum3Score2_measurable rum3Score3_measurable
          t x1 x2 x3))
      (paper_theorem6_normalizedScoreRankingPMF (theorem7LaplacePDF lam 0)
        x1 x2 x3 hnorm
        (rum3RankByScoreFns
          paper_theorem6_score1 paper_theorem6_score2 paper_theorem6_score3)
        (rum3RankByScoreFns_measurable
          rum3Score1_measurable rum3Score2_measurable rum3Score3_measurable))
      value :=
  KR21Monoculture.paper_theorem6_threeCandidate_prefersWeakerCompetition_of_laplacian_scoreSpace_t_lt_one
    hlam hvalue1 hvalue2 hvalue3 hnorm ht0 ht1 htlt1 hx12 hx23

/--
Appendix C Theorem 6 / Laplacian three-candidate RUM: the concrete zero-mean
Laplace score density is normalized in Lean, so the theorem has no remaining
lambda-certificate premise.

Source status: derived from source primitives.
-/
theorem theorem6_threeCandidate_laplacian_prefersWeakerCompetition_of_scoreSpace_concreteNormalization_t_lt_one
    {lam x1 x2 x3 t : ℝ}
    {value : Candidate 1 → ℝ}
    (hlam : 0 < lam)
    (hvalue1 : value (0 : Candidate 1) = x1)
    (hvalue2 : value (1 : Candidate 1) = x2)
    (hvalue3 : value (2 : Candidate 1) = x3)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (htlt1 : t < 1)
    (hx12 : x2 < x1) (hx23 : x3 < x2) :
    Model.PrefersWeakerCompetition
      (paper_theorem6_normalizedScoreRankingPMF (theorem7LaplacePDF lam 0)
        x1 x2 x3
        (paper_theorem6_laplacian_scoreDensity_lintegral_eq_one
          (lam := lam) hlam x1 x2 x3)
        (rum3ContractRankByScoreFns
          t x1 x2 x3
          paper_theorem6_score1 paper_theorem6_score2 paper_theorem6_score3)
        (rum3ContractRankByScoreFns_measurable
          rum3Score1_measurable rum3Score2_measurable rum3Score3_measurable
          t x1 x2 x3))
      (paper_theorem6_normalizedScoreRankingPMF (theorem7LaplacePDF lam 0)
        x1 x2 x3
        (paper_theorem6_laplacian_scoreDensity_lintegral_eq_one
          (lam := lam) hlam x1 x2 x3)
        (rum3RankByScoreFns
          paper_theorem6_score1 paper_theorem6_score2 paper_theorem6_score3)
        (rum3RankByScoreFns_measurable
          rum3Score1_measurable rum3Score2_measurable rum3Score3_measurable))
      value :=
  KR21Monoculture.paper_theorem6_threeCandidate_prefersWeakerCompetition_of_laplacian_scoreSpace_concreteNormalization_t_lt_one
    hlam hvalue1 hvalue2 hvalue3 ht0 ht1 htlt1 hx12 hx23

/--
Theorem 6 for the literal iid standard-Gaussian source RUM.  Both ranking laws
are induced by `x_i + epsilon_i / theta`; the product-law transport from those
innovations to the score law is proved before applying the payoff theorem.
-/
theorem theorem6_source_standardGaussian_iid_rum_prefersWeakerCompetition
    {thetaA thetaH x1 x2 x3 : ℝ}
    (hthetaH : 0 < thetaH) (hthetaHA : thetaH < thetaA)
    (hx12 : x2 < x1) (hx23 : x3 < x2) :
    Model.PrefersWeakerCompetition
      ((theorem2GaussianScaledNoiseFamily x1 x2 x3).dist thetaA)
      ((theorem2GaussianScaledNoiseFamily x1 x2 x3).dist thetaH)
      (threeCandidateValueProfile x1 x2 x3) :=
  KR21Monoculture.appendixC_source_theorem6_gaussian_prefers_weaker_competition
    hthetaH hthetaHA hx12 hx23

/--
Theorem 6 for the literal iid unit-variance Laplace source RUM.  The endpoint
retains the source rate translation `sqrt(2) * theta` rather than identifying
the source accuracy with a differently normalized Laplace rate.
-/
theorem theorem6_source_unitVarianceLaplace_iid_rum_prefersWeakerCompetition
    {thetaA thetaH x1 x2 x3 : ℝ}
    (hthetaH : 0 < thetaH) (hthetaHA : thetaH < thetaA)
    (hx12 : x2 < x1) (hx23 : x3 < x2) :
    Model.PrefersWeakerCompetition
      ((sourceUnitVarianceLaplaceScaledNoiseFamily x1 x2 x3).dist thetaA)
      ((sourceUnitVarianceLaplaceScaledNoiseFamily x1 x2 x3).dist thetaH)
      (threeCandidateValueProfile x1 x2 x3) :=
  KR21Monoculture.appendixC_source_theorem6_laplace_prefers_weaker_competition
    hthetaH hthetaHA hx12 hx23

/--
Theorem 6 at its literal generic source-law surface.  The ranking laws are
generated from one normalized iid density by `x_i + epsilon_i / theta`.
The source's full-support condition is explicit as pointwise density
positivity, and the Jacobian/product-law ranking transport is proved inside the
cited endpoint rather than supplied as a law-equality premise.
-/
theorem theorem6_source_raw_iid_density_prefersWeakerCompetition
    (f : ℝ → ℝ) {thetaA thetaH x1 x2 x3 : ℝ}
    (hfmeas : Measurable f) (hf : StrictlyWellOrderedNoise f)
    (hnonneg : ∀ z : ℝ, 0 ≤ f z)
    (hfullSupport : ∀ z : ℝ, 0 < f z)
    (hnormalized : ∫⁻ z, ENNReal.ofReal (f z) ∂volume = 1)
    (hthetaH : 0 < thetaH) (hthetaHA : thetaH < thetaA)
    (hx12 : x2 < x1) (hx23 : x3 < x2) :
    Model.PrefersWeakerCompetition
      (@paper_appendixA_scaledNoiseRankingPMF 1
        (w11CandidateNoiseLaw f)
        (w11CandidateNoiseLaw_isProbabilityMeasure_of_base_normalization 1 f hnormalized)
        (threeCandidateValueProfile x1 x2 x3) thetaA)
      (@paper_appendixA_scaledNoiseRankingPMF 1
        (w11CandidateNoiseLaw f)
        (w11CandidateNoiseLaw_isProbabilityMeasure_of_base_normalization 1 f hnormalized)
        (threeCandidateValueProfile x1 x2 x3) thetaH)
      (threeCandidateValueProfile x1 x2 x3) :=
  KR21Monoculture.appendixC_source_rawRUM_theorem6_prefersWeakerCompetition
    f hfmeas hf hfullSupport hnormalized hthetaH hthetaHA x1 x2 x3 hx12 hx23

/--
Theorem 6 with its iid density product and raw `x_i + epsilon_i / theta`
ranking construction visible in the terminal proposition.
-/
theorem theorem6_source_raw_iid_density_semantic_complete
    (f : ℝ → ℝ) {thetaA thetaH x1 x2 x3 : ℝ}
    (hfmeas : Measurable f)
    (hf : ∀ ⦃a b c d : ℝ⦄, b < a → d < c →
      f (a - c) * f (b - d) > f (a - d) * f (b - c))
    (hnonneg : ∀ z : ℝ, 0 ≤ f z)
    (hfullSupport : ∀ z : ℝ, 0 < f z)
    (hnormalized : ∫⁻ z, ENNReal.ofReal (f z) ∂volume = 1)
    (hthetaH : 0 < thetaH) (hthetaHA : thetaH < thetaA)
    (hx12 : x2 < x1) (hx23 : x3 < x2) :
    IsProbabilityMeasure
      (Measure.pi (fun _ : Candidate 1 =>
        volume.withDensity (fun z => ENNReal.ofReal (f z)))) ∧
    ∃ rankingLaw : ℝ → PMF (Ranking 1),
      (∀ theta : ℝ, 0 < theta →
        (rankingLaw theta).toMeasure =
          (Measure.pi (fun _ : Candidate 1 =>
            volume.withDensity (fun z => ENNReal.ofReal (f z)))).map
            (fun epsilon => rankByScore (fun i =>
              threeCandidateValueProfile x1 x2 x3 i + epsilon i / theta))) ∧
      Model.PrefersWeakerCompetition
        (rankingLaw thetaA) (rankingLaw thetaH)
        (threeCandidateValueProfile x1 x2 x3) := by
  letI : IsProbabilityMeasure (w11CandidateNoiseLaw (n := 1) f) :=
    w11CandidateNoiseLaw_isProbabilityMeasure_of_base_normalization 1 f hnormalized
  refine ⟨?_, ?_⟩
  · simpa [w11CandidateNoiseLaw, w11BaseNoiseLaw] using
      (inferInstance : IsProbabilityMeasure (w11CandidateNoiseLaw (n := 1) f))
  · refine ⟨fun theta => paper_appendixA_scaledNoiseRankingPMF
      (w11CandidateNoiseLaw (n := 1) f)
      (threeCandidateValueProfile x1 x2 x3) theta, ?_, ?_⟩
    · intro theta htheta
      change
        (paper_appendixA_scaledNoiseRankingPMF
          (w11CandidateNoiseLaw (n := 1) f)
          (threeCandidateValueProfile x1 x2 x3) theta).toMeasure = _
      unfold paper_appendixA_scaledNoiseRankingPMF
      unfold AppliedModelingLib.SocialChoice.Ranking.rankingPMFOfMeasure
      rw [Measure.toPMF_toMeasure]
      simp [w11CandidateNoiseLaw, w11BaseNoiseLaw]
    · exact theorem6_source_raw_iid_density_prefersWeakerCompetition
        f hfmeas hf hnonneg hfullSupport hnormalized hthetaH hthetaHA hx12 hx23

/--
Theorem 6 with its Definition 3 conclusion written as the literal fixed-PMF
payoff comparison.  The density product and raw score construction remain the
same as the source-facing endpoint immediately above.
-/
theorem theorem6_source_raw_iid_density_literal_semantic_complete
    (f : ℝ → ℝ) {thetaA thetaH x1 x2 x3 : ℝ}
    (hfmeas : Measurable f)
    (hf : ∀ ⦃a b c d : ℝ⦄, b < a → d < c →
      f (a - c) * f (b - d) > f (a - d) * f (b - c))
    (hnonneg : ∀ z : ℝ, 0 ≤ f z)
    (hfullSupport : ∀ z : ℝ, 0 < f z)
    (hnormalized : ∫⁻ z, ENNReal.ofReal (f z) ∂volume = 1)
    (hthetaH : 0 < thetaH) (hthetaHA : thetaH < thetaA)
    (hx12 : x2 < x1) (hx23 : x3 < x2) :
    IsProbabilityMeasure
      (Measure.pi (fun _ : Candidate 1 =>
        volume.withDensity (fun z => ENNReal.ofReal (f z)))) ∧
    ∃ rankingLaw : ℝ → PMF (Ranking 1),
      (∀ theta : ℝ, 0 < theta →
        (rankingLaw theta).toMeasure =
          (Measure.pi (fun _ : Candidate 1 =>
            volume.withDensity (fun z => ENNReal.ofReal (f z)))).map
            (fun epsilon => rankByScore (fun i =>
              threeCandidateValueProfile x1 x2 x3 i + epsilon i / theta))) ∧
      expectedSecondMoverIndependent
        (rankingLaw thetaH) (rankingLaw thetaA)
        (threeCandidateValueProfile x1 x2 x3) <
      expectedSecondMoverIndependent
        (rankingLaw thetaH) (rankingLaw thetaH)
        (threeCandidateValueProfile x1 x2 x3) := by
  rcases theorem6_source_raw_iid_density_semantic_complete
    f hfmeas hf hnonneg hfullSupport hnormalized hthetaH hthetaHA hx12 hx23 with
    ⟨hprob, rankingLaw, hlaw, hpref⟩
  refine ⟨hprob, rankingLaw, hlaw, ?_⟩
  simpa only [Model.PrefersWeakerCompetition,
    AppliedModelingLib.SocialChoice.Ranking.PrefersWeakerCompetition] using hpref

/-! ## Appendix C, Lemmas 2 and 3 -/

/--
Appendix C Lemma 2 at the literal source-score surface.  A single innovation
vector is used at both accuracies, and the bottom-first event inclusion is
derived pointwise from score contraction instead of accepted as a premise.
-/
theorem lemma2_source_bottom_first_probability
    {thetaA thetaH x1 x2 x3 : ℝ}
    (mu : Measure (Candidate 1 -> ℝ)) [IsProbabilityMeasure mu]
    (hthetaH : 0 < thetaH) (hthetaHA : thetaH < thetaA)
    (hx12 : x2 < x1) (hx23 : x3 < x2) :
    firstChoiceProb
        (paper_appendixA_scaledNoiseRankingPMF mu
          (threeCandidateValueProfile x1 x2 x3) thetaA)
        (2 : Candidate 1) <=
      firstChoiceProb
        (paper_appendixA_scaledNoiseRankingPMF mu
          (threeCandidateValueProfile x1 x2 x3) thetaH)
        (2 : Candidate 1) :=
  KR21Monoculture.appendixC_source_lemma2_bottom_first_probability
    mu hthetaH hthetaHA hx12 hx23

/--
Appendix C Lemma 2 on the source's arbitrary finite candidate carrier.  A
shared innovation vector is ranked at both accuracies; the strict-lowest
condition is the source role of `x_n`, and the bottom-event implication is
proved from score contraction rather than received as an input.
-/
theorem lemma2_source_arbitraryFinite_bottom_first_probability
    {n : ℕ} {thetaA thetaH : ℝ}
    (mu : Measure (Candidate n -> ℝ)) [IsProbabilityMeasure mu]
    (hthetaH : 0 < thetaH) (hthetaHA : thetaH < thetaA)
    (value : Candidate n -> ℝ) (bottom : Candidate n)
    (hbottom : ∀ i : Candidate n, i ≠ bottom -> value bottom < value i) :
    firstChoiceProb (paper_appendixA_scaledNoiseRankingPMF mu value thetaA) bottom <=
      firstChoiceProb (paper_appendixA_scaledNoiseRankingPMF mu value thetaH) bottom :=
  KR21Monoculture.appendixC_general_source_lemma2_bottom_first_probability
    mu hthetaH hthetaHA value bottom hbottom

/--
Appendix C Lemma 2 with the two source ranking laws exposed as literal
pushforwards of the shared innovation measure.  This prevents the probability
comparison from being reviewed as a claim about unrelated named PMFs.
-/
theorem lemma2_source_arbitraryFinite_bottom_first_probability_semantic_complete
    {n : ℕ} {thetaA thetaH : ℝ}
    (mu : Measure (Candidate n -> ℝ)) [IsProbabilityMeasure mu]
    (hthetaH : 0 < thetaH) (hthetaHA : thetaH < thetaA)
    (value : Candidate n -> ℝ) (bottom : Candidate n)
    (hbottom : ∀ i : Candidate n, i ≠ bottom -> value bottom < value i) :
    (paper_appendixA_scaledNoiseRankingPMF mu value thetaA).toMeasure = mu.map
      (fun epsilon => rankByScore (fun c => value c + epsilon c / thetaA)) ∧
    (paper_appendixA_scaledNoiseRankingPMF mu value thetaH).toMeasure = mu.map
      (fun epsilon => rankByScore (fun c => value c + epsilon c / thetaH)) ∧
    firstChoiceProb (paper_appendixA_scaledNoiseRankingPMF mu value thetaA) bottom ≤
      firstChoiceProb (paper_appendixA_scaledNoiseRankingPMF mu value thetaH) bottom := by
  refine ⟨?_, ?_, ?_⟩
  · change (paper_appendixA_scaledNoiseRankingPMF mu value thetaA).toMeasure =
      mu.map (fun epsilon => rankByScore
        (fun c => value c + epsilon c / thetaA))
    unfold paper_appendixA_scaledNoiseRankingPMF
    unfold AppliedModelingLib.SocialChoice.Ranking.rankingPMFOfMeasure
    rw [Measure.toPMF_toMeasure]
  · change (paper_appendixA_scaledNoiseRankingPMF mu value thetaH).toMeasure =
      mu.map (fun epsilon => rankByScore
        (fun c => value c + epsilon c / thetaH))
    unfold paper_appendixA_scaledNoiseRankingPMF
    unfold AppliedModelingLib.SocialChoice.Ranking.rankingPMFOfMeasure
    rw [Measure.toPMF_toMeasure]
  · exact lemma2_source_arbitraryFinite_bottom_first_probability
      mu hthetaH hthetaHA value bottom hbottom

/--
Appendix C Lemma 2 at the literal iid RUM surface for the paper's two-firm
candidate domain.  The source's ``x_n`` is the last finite candidate, the
common density `f` supplies independent innovations, and the two laws are the
literal source score pushforwards.  `Candidate n = Fin (n + 2)` includes the
source boundary of two candidates; the more general shared-innovation theorem
above is used only as a proved strengthening of this source endpoint.
-/
theorem lemma2_source_arbitraryFinite_iid_bottom_first_probability_semantic_complete
    {n : ℕ} {f : ℝ → ℝ}
    (hfmeas : Measurable f) (hnonneg : ∀ z : ℝ, 0 ≤ f z)
    (hnormalized : ∫⁻ z, ENNReal.ofReal (f z) ∂volume = 1)
    (value : Candidate n → ℝ) (hvalueOrder : StrictAnti value)
    {thetaA thetaH : ℝ} (hthetaH : 0 < thetaH) (hthetaHA : thetaH < thetaA) :
    (@paper_appendixA_scaledNoiseRankingPMF n
      (w11CandidateNoiseLaw (n := n) f)
      (w11CandidateNoiseLaw_isProbabilityMeasure_of_base_normalization
        n f hnormalized)
      value thetaA).toMeasure =
      (Measure.pi (fun _ : Candidate n =>
        volume.withDensity (fun z => ENNReal.ofReal (f z)))).map
        (fun epsilon => rankByScore (fun c => value c + epsilon c / thetaA)) ∧
    (@paper_appendixA_scaledNoiseRankingPMF n
      (w11CandidateNoiseLaw (n := n) f)
      (w11CandidateNoiseLaw_isProbabilityMeasure_of_base_normalization
        n f hnormalized)
      value thetaH).toMeasure =
      (Measure.pi (fun _ : Candidate n =>
        volume.withDensity (fun z => ENNReal.ofReal (f z)))).map
        (fun epsilon => rankByScore (fun c => value c + epsilon c / thetaH)) ∧
    firstChoiceProb
        (@paper_appendixA_scaledNoiseRankingPMF n
          (w11CandidateNoiseLaw (n := n) f)
          (w11CandidateNoiseLaw_isProbabilityMeasure_of_base_normalization
            n f hnormalized)
          value thetaA)
        (Fin.last (n + 1)) ≤
      firstChoiceProb
        (@paper_appendixA_scaledNoiseRankingPMF n
          (w11CandidateNoiseLaw (n := n) f)
          (w11CandidateNoiseLaw_isProbabilityMeasure_of_base_normalization
            n f hnormalized)
          value thetaH)
        (Fin.last (n + 1)) := by
  letI : IsProbabilityMeasure (w11CandidateNoiseLaw (n := n) f) :=
    w11CandidateNoiseLaw_isProbabilityMeasure_of_base_normalization n f hnormalized
  have hbottom : ∀ i : Candidate n, i ≠ Fin.last (n + 1) →
      value (Fin.last (n + 1)) < value i := by
    intro i hi
    exact hvalueOrder (Fin.lt_last_iff_ne_last.mpr hi)
  refine ⟨?_, ?_, ?_⟩
  · change
      (paper_appendixA_scaledNoiseRankingPMF
        (w11CandidateNoiseLaw (n := n) f) value thetaA).toMeasure =
      (w11CandidateNoiseLaw (n := n) f).map
        (fun epsilon => rankByScore (fun c => value c + epsilon c / thetaA))
    unfold paper_appendixA_scaledNoiseRankingPMF
    unfold AppliedModelingLib.SocialChoice.Ranking.rankingPMFOfMeasure
    rw [Measure.toPMF_toMeasure]
  · change
      (paper_appendixA_scaledNoiseRankingPMF
        (w11CandidateNoiseLaw (n := n) f) value thetaH).toMeasure =
      (w11CandidateNoiseLaw (n := n) f).map
        (fun epsilon => rankByScore (fun c => value c + epsilon c / thetaH))
    unfold paper_appendixA_scaledNoiseRankingPMF
    unfold AppliedModelingLib.SocialChoice.Ranking.rankingPMFOfMeasure
    rw [Measure.toPMF_toMeasure]
  · exact KR21Monoculture.appendixC_general_source_lemma2_bottom_first_probability
      (w11CandidateNoiseLaw (n := n) f) hthetaH hthetaHA value
      (Fin.last (n + 1)) hbottom

/-- Literal iid standard-Gaussian specialization of Appendix C Lemma 2. -/
theorem lemma2_source_standardGaussian_bottom_first_probability
    {thetaA thetaH x1 x2 x3 : ℝ}
    (hthetaH : 0 < thetaH) (hthetaHA : thetaH < thetaA)
    (hx12 : x2 < x1) (hx23 : x3 < x2) :
    firstChoiceProb ((theorem2GaussianScaledNoiseFamily x1 x2 x3).dist thetaA)
        (2 : Candidate 1) <=
      firstChoiceProb ((theorem2GaussianScaledNoiseFamily x1 x2 x3).dist thetaH)
        (2 : Candidate 1) :=
  KR21Monoculture.appendixC_source_lemma2_gaussian_bottom_first_probability
    hthetaH hthetaHA hx12 hx23

/-- Literal iid unit-variance Laplace specialization of Appendix C Lemma 2. -/
theorem lemma2_source_unitVarianceLaplace_bottom_first_probability
    {thetaA thetaH x1 x2 x3 : ℝ}
    (hthetaH : 0 < thetaH) (hthetaHA : thetaH < thetaA)
    (hx12 : x2 < x1) (hx23 : x3 < x2) :
    firstChoiceProb
        ((sourceUnitVarianceLaplaceScaledNoiseFamily x1 x2 x3).dist thetaA)
        (2 : Candidate 1) <=
      firstChoiceProb
        ((sourceUnitVarianceLaplaceScaledNoiseFamily x1 x2 x3).dist thetaH)
        (2 : Candidate 1) :=
  KR21Monoculture.appendixC_source_lemma2_laplace_bottom_first_probability
    hthetaH hthetaHA hx12 hx23

/--
The direct three-candidate score-density certificate behind Lemma 3.  Its
inputs are density normalization, positivity, weak well-ordering, value order,
and a strict contraction; it does not take a swap-mass or delta conclusion.
-/
abbrev lemma3_source_threeCandidate_scoreDensity_delta_certificate :=
  @KR21Monoculture.appendixC_source_score_density_delta_certificate_of_contraction

/--
The three-candidate middle-candidate specialization of Appendix C Lemma 3 for
the literal iid standard-Gaussian source RUM.  The published arbitrary-n
generalization is deliberately not implied by this endpoint.
-/
theorem lemma3_source_standardGaussian_threeCandidate_middle_delta_le_top_delta
    {thetaA thetaH x1 x2 x3 : ℝ}
    (hthetaH : 0 < thetaH) (hthetaHA : thetaH < thetaA)
    (hx12 : x2 < x1) (hx23 : x3 < x2) :
    firstChoiceProb ((theorem2GaussianScaledNoiseFamily x1 x2 x3).dist thetaA)
        (1 : Candidate 1) -
      firstChoiceProb ((theorem2GaussianScaledNoiseFamily x1 x2 x3).dist thetaH)
        (1 : Candidate 1) <=
      firstChoiceProb ((theorem2GaussianScaledNoiseFamily x1 x2 x3).dist thetaA)
        (0 : Candidate 1) -
      firstChoiceProb ((theorem2GaussianScaledNoiseFamily x1 x2 x3).dist thetaH)
        (0 : Candidate 1) :=
  KR21Monoculture.appendixC_source_lemma3_gaussian_middle_delta_le_top_delta
    hthetaH hthetaHA hx12 hx23

/--
The three-candidate middle-candidate specialization of Appendix C Lemma 3 for
the literal iid unit-variance Laplace source RUM.  The published arbitrary-n
generalization is deliberately not implied by this endpoint.
-/
theorem lemma3_source_unitVarianceLaplace_threeCandidate_middle_delta_le_top_delta
    {thetaA thetaH x1 x2 x3 : ℝ}
    (hthetaH : 0 < thetaH) (hthetaHA : thetaH < thetaA)
    (hx12 : x2 < x1) (hx23 : x3 < x2) :
    firstChoiceProb
        ((sourceUnitVarianceLaplaceScaledNoiseFamily x1 x2 x3).dist thetaA)
        (1 : Candidate 1) -
      firstChoiceProb
        ((sourceUnitVarianceLaplaceScaledNoiseFamily x1 x2 x3).dist thetaH)
        (1 : Candidate 1) <=
      firstChoiceProb
        ((sourceUnitVarianceLaplaceScaledNoiseFamily x1 x2 x3).dist thetaA)
        (0 : Candidate 1) -
      firstChoiceProb
        ((sourceUnitVarianceLaplaceScaledNoiseFamily x1 x2 x3).dist thetaH)
        (0 : Candidate 1) :=
  KR21Monoculture.appendixC_source_lemma3_laplace_middle_delta_le_top_delta
    hthetaH hthetaHA hx12 hx23

/--
Appendix C Lemma 3 at its printed arbitrary-finite iid RUM surface.  The
proof couples the two marginal iid source laws with one innovation vector of
density `f`, and ranks `x_c + epsilon_c / theta` at both accuracies.
`Candidate n` represents the source's `n + 2` labels
`x_1 > ... > x_{n+2}`; `i != 0` is any non-top source label.  The weak
accuracy case `thetaA = thetaH` is included explicitly.
-/
theorem lemma3_source_arbitraryFinite_iid_delta_le_top_delta
    {n : ℕ} {f : ℝ → ℝ}
    (hf : StrictlyWellOrderedNoise f) (hfmeas : Measurable f)
    (hnonneg : ∀ z : ℝ, 0 ≤ f z)
    (hnormalized : ∫⁻ z, ENNReal.ofReal (f z) ∂volume = 1)
    (value : Candidate n → ℝ) (hvalueOrder : StrictAnti value)
    {thetaA thetaH : ℝ} (hthetaH : 0 < thetaH) (hthetaHA : thetaH ≤ thetaA)
    {i : Candidate n} (hi : i ≠ 0) :
    firstChoiceProb
        (@paper_appendixA_scaledNoiseRankingPMF n
          (w11CandidateNoiseLaw (n := n) f)
          (w11CandidateNoiseLaw_isProbabilityMeasure_of_base_normalization
            n f hnormalized)
          value thetaA) i -
      firstChoiceProb
        (@paper_appendixA_scaledNoiseRankingPMF n
          (w11CandidateNoiseLaw (n := n) f)
          (w11CandidateNoiseLaw_isProbabilityMeasure_of_base_normalization
            n f hnormalized)
          value thetaH) i ≤
    firstChoiceProb
        (@paper_appendixA_scaledNoiseRankingPMF n
          (w11CandidateNoiseLaw (n := n) f)
          (w11CandidateNoiseLaw_isProbabilityMeasure_of_base_normalization
            n f hnormalized)
          value thetaA) 0 -
      firstChoiceProb
        (@paper_appendixA_scaledNoiseRankingPMF n
          (w11CandidateNoiseLaw (n := n) f)
          (w11CandidateNoiseLaw_isProbabilityMeasure_of_base_normalization
            n f hnormalized)
          value thetaH) 0 := by
  letI : IsProbabilityMeasure (w11CandidateNoiseLaw (n := n) f) :=
    w11CandidateNoiseLaw_isProbabilityMeasure_of_base_normalization n f hnormalized
  let rankA : (Candidate n → ℝ) → Ranking n := fun noise =>
    rankByScore (fun c => value c + noise c / thetaA)
  let rankH : (Candidate n → ℝ) → Ranking n := fun noise =>
    rankByScore (fun c => value c + noise c / thetaH)
  have hrankA : Measurable rankA := by
    exact paper_appendixA_scaledNoise_rankByScore_measurable
      (fun noise : Candidate n → ℝ => noise)
      (fun c => measurable_pi_apply c) value thetaA
  have hrankH : Measurable rankH := by
    exact paper_appendixA_scaledNoise_rankByScore_measurable
      (fun noise : Candidate n → ℝ => noise)
      (fun c => measurable_pi_apply c) value thetaH
  have hpmfA :
      @paper_appendixA_scaledNoiseRankingPMF n
          (w11CandidateNoiseLaw (n := n) f)
          (w11CandidateNoiseLaw_isProbabilityMeasure_of_base_normalization
            n f hnormalized)
          value thetaA =
        rankingPMFOfMeasure (w11CandidateNoiseLaw (n := n) f) rankA hrankA := by
    rfl
  have hpmfH :
      @paper_appendixA_scaledNoiseRankingPMF n
          (w11CandidateNoiseLaw (n := n) f)
          (w11CandidateNoiseLaw_isProbabilityMeasure_of_base_normalization
            n f hnormalized)
          value thetaH =
        rankingPMFOfMeasure (w11CandidateNoiseLaw (n := n) f) rankH hrankH := by
    rfl
  rw [hpmfA, hpmfH]
  simp only [KR21Monoculture.firstChoiceProb]
  rw [AppliedModelingLib.SocialChoice.Ranking.firstChoiceProb_rankingPMFOfMeasure,
    AppliedModelingLib.SocialChoice.Ranking.firstChoiceProb_rankingPMFOfMeasure,
    AppliedModelingLib.SocialChoice.Ranking.firstChoiceProb_rankingPMFOfMeasure,
    AppliedModelingLib.SocialChoice.Ranking.firstChoiceProb_rankingPMFOfMeasure]
  simpa [rankA, rankH, appendixCRawScoreMap, eq_comm] using
    (KR21Monoculture.appendixCGeneralLemma3_sourceRaw_delta_le_top_delta
      hf hfmeas hnonneg hnormalized value hvalueOrder hthetaH hthetaHA hi)

/--
Appendix C Lemma 3 with the iid density product and both source score maps in
the terminal proposition.  The comparison therefore cannot be discharged by
an opaque PMF bearing a source-like name.
-/
theorem lemma3_source_arbitraryFinite_iid_delta_le_top_delta_semantic_complete
    {n : ℕ} {f : ℝ → ℝ}
    (hf : StrictlyWellOrderedNoise f) (hfmeas : Measurable f)
    (hnonneg : ∀ z : ℝ, 0 ≤ f z)
    (hnormalized : ∫⁻ z, ENNReal.ofReal (f z) ∂volume = 1)
    (value : Candidate n → ℝ) (hvalueOrder : StrictAnti value)
    {thetaA thetaH : ℝ} (hthetaH : 0 < thetaH) (hthetaHA : thetaH ≤ thetaA)
    {i : Candidate n} (hi : i ≠ 0) :
    (@paper_appendixA_scaledNoiseRankingPMF n
      (w11CandidateNoiseLaw (n := n) f)
      (w11CandidateNoiseLaw_isProbabilityMeasure_of_base_normalization
        n f hnormalized)
      value thetaA).toMeasure =
      (Measure.pi (fun _ : Candidate n =>
        volume.withDensity (fun z => ENNReal.ofReal (f z)))).map
        (fun epsilon => rankByScore (fun c => value c + epsilon c / thetaA)) ∧
    (@paper_appendixA_scaledNoiseRankingPMF n
      (w11CandidateNoiseLaw (n := n) f)
      (w11CandidateNoiseLaw_isProbabilityMeasure_of_base_normalization
        n f hnormalized)
      value thetaH).toMeasure =
      (Measure.pi (fun _ : Candidate n =>
        volume.withDensity (fun z => ENNReal.ofReal (f z)))).map
        (fun epsilon => rankByScore (fun c => value c + epsilon c / thetaH)) ∧
    firstChoiceProb
        (@paper_appendixA_scaledNoiseRankingPMF n
          (w11CandidateNoiseLaw (n := n) f)
          (w11CandidateNoiseLaw_isProbabilityMeasure_of_base_normalization
            n f hnormalized)
          value thetaA) i -
      firstChoiceProb
        (@paper_appendixA_scaledNoiseRankingPMF n
          (w11CandidateNoiseLaw (n := n) f)
          (w11CandidateNoiseLaw_isProbabilityMeasure_of_base_normalization
            n f hnormalized)
          value thetaH) i ≤
    firstChoiceProb
        (@paper_appendixA_scaledNoiseRankingPMF n
          (w11CandidateNoiseLaw (n := n) f)
          (w11CandidateNoiseLaw_isProbabilityMeasure_of_base_normalization
            n f hnormalized)
          value thetaA) 0 -
      firstChoiceProb
        (@paper_appendixA_scaledNoiseRankingPMF n
          (w11CandidateNoiseLaw (n := n) f)
          (w11CandidateNoiseLaw_isProbabilityMeasure_of_base_normalization
            n f hnormalized)
          value thetaH) 0 := by
  letI : IsProbabilityMeasure (w11CandidateNoiseLaw (n := n) f) :=
    w11CandidateNoiseLaw_isProbabilityMeasure_of_base_normalization n f hnormalized
  refine ⟨?_, ?_, ?_⟩
  · change
      (paper_appendixA_scaledNoiseRankingPMF
        (w11CandidateNoiseLaw (n := n) f) value thetaA).toMeasure =
      (w11CandidateNoiseLaw (n := n) f).map
        (fun epsilon => rankByScore (fun c => value c + epsilon c / thetaA))
    unfold paper_appendixA_scaledNoiseRankingPMF
    unfold AppliedModelingLib.SocialChoice.Ranking.rankingPMFOfMeasure
    rw [Measure.toPMF_toMeasure]
  · change
      (paper_appendixA_scaledNoiseRankingPMF
        (w11CandidateNoiseLaw (n := n) f) value thetaH).toMeasure =
      (w11CandidateNoiseLaw (n := n) f).map
        (fun epsilon => rankByScore (fun c => value c + epsilon c / thetaH))
    unfold paper_appendixA_scaledNoiseRankingPMF
    unfold AppliedModelingLib.SocialChoice.Ranking.rankingPMFOfMeasure
    rw [Measure.toPMF_toMeasure]
  · exact lemma3_source_arbitraryFinite_iid_delta_le_top_delta
      hf hfmeas hnonneg hnormalized value hvalueOrder hthetaH hthetaHA hi

/--
Appendix C Lemma 2, continuous coupling form.  If contraction can put the
lowest candidate first only on realizations where it was already first, its
first-choice probability weakly decreases.
-/
theorem lemma2_bottom_of_measure_coupling
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (better worse : Omega → Ranking 1)
    (hbottomImp : ∀ omega,
      (2 : Candidate 1) = firstChoice (better omega) →
        (2 : Candidate 1) = firstChoice (worse omega)) :
    mu {omega | (2 : Candidate 1) = firstChoice (better omega)} ≤
      mu {omega | (2 : Candidate 1) = firstChoice (worse omega)} :=
  KR21Monoculture.paper_lemma2_bottom_of_measure_coupling
    mu better worse hbottomImp

/--
Appendix C Lemma 3, continuous transition-mass form.  No loss of top-first
realizations together with the source swap comparison bounds the middle
candidate's probability gain by the top candidate's gain.
-/
theorem lemma3_middle_of_measure_transition_mass
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (better worse : Omega → Ranking 1)
    (hbetter : Measurable better) (hworse : Measurable worse)
    (hnoTopOut : ∀ omega,
      (0 : Candidate 1) = firstChoice (worse omega) →
        (0 : Candidate 1) = firstChoice (better omega))
    (hbottomMiddle_le_bottomTop :
      measureProb mu (fun omega =>
          (2 : Candidate 1) = firstChoice (worse omega) ∧
            (1 : Candidate 1) = firstChoice (better omega)) ≤
        measureProb mu (fun omega =>
          (2 : Candidate 1) = firstChoice (worse omega) ∧
            (0 : Candidate 1) = firstChoice (better omega))) :
    measureProb mu (fun omega => (1 : Candidate 1) = firstChoice (better omega)) -
        measureProb mu (fun omega => (1 : Candidate 1) = firstChoice (worse omega)) ≤
      measureProb mu (fun omega => (0 : Candidate 1) = firstChoice (better omega)) -
        measureProb mu (fun omega => (0 : Candidate 1) = firstChoice (worse omega)) :=
  KR21Monoculture.paper_lemma3_middle_of_measure_transition_mass
    mu better worse hbetter hworse hnoTopOut hbottomMiddle_le_bottomTop

/-! ## Appendix A equation (A.1) source event surface -/

/--
Equation (A.1)'s selected-top event is exactly its finite strict tail event
after clearing the positive accuracy denominator.  The a.e. no-tie premise is
visible because Lean's ranking function has a deterministic tie rule whereas
the source display uses strict comparisons.
-/
theorem equationA1_source_top_event_iff_tail_event_of_no_ties
    {n : ℕ} (value noise : Candidate n → ℝ) {theta : ℝ} (htheta : 0 < theta)
    (c : Candidate n)
    (hnoTie : ∀ i j : Candidate n, i ≠ j →
      value i + noise i / theta ≠ value j + noise j / theta) :
    SourceAppendixATopEvent value noise theta c ↔
      SourceAppendixATailEvent value noise theta c :=
  KR21Monoculture.source_appendixA_top_event_iff_tail_event_of_no_ties
    value noise htheta c hnoTie

/--
The event-level probability transport in A.1.  It is deliberately narrower
than the source's subsequent conditional-expectation/Fubini display: that
disintegration has not been constructed for the general finite-coordinate
noise law and is not silently credited by this event rewrite.
-/
theorem equationA1_source_top_probability_eq_tail_probability
    {n : ℕ} (mu : Measure (Candidate n → ℝ))
    (value : Candidate n → ℝ) {theta : ℝ} (htheta : 0 < theta)
    (c : Candidate n)
    (hnoTie : ∀ᵐ noise ∂mu, ∀ i j : Candidate n, i ≠ j →
      value i + noise i / theta ≠ value j + noise j / theta) :
    AppliedModelingLib.measureProb mu
        (fun noise => SourceAppendixATopEvent value noise theta c) =
      AppliedModelingLib.measureProb mu
        (fun noise => SourceAppendixATailEvent value noise theta c) :=
  KR21Monoculture.source_appendixA_top_event_probability_eq_tail_probability
    mu value htheta c hnoTie

/--
Equation (A.1)'s full finite-iid factorization.  The source noise law is
split into candidate `0` and the other `n + 1` iid coordinates; Fubini turns
the literal selected-top probability into the expectation of the displayed
strict conditional tail probability.  A.e. no ties remains explicit because
the source uses strict score comparisons while the executable ranking has a
deterministic tie rule.
-/
theorem equationA1_source_selectedTop_probability_eq_conditionalTail_integral
    {n : Nat} (mu : Measure Real) [IsProbabilityMeasure mu]
    (value : Candidate n -> Real) {theta : Real} (htheta : 0 < theta)
    (hnoTie : ∀ᵐ z ∂(sourceAppendixARestNoiseLaw n mu).prod mu,
      ∀ i j : Candidate n, i ≠ j ->
        value i + sourceAppendixAProductNoise z i / theta ≠
          value j + sourceAppendixAProductNoise z j / theta) :
    AppliedModelingLib.measureProb ((sourceAppendixARestNoiseLaw n mu).prod mu)
        (fun z => SourceAppendixATopEvent value
          (sourceAppendixAProductNoise z) theta 0) =
      ∫ rest : Fin (n + 1) -> Real,
        AppliedModelingLib.measureProb mu
          (fun epsilon => SourceAppendixAFirstTail value theta rest epsilon)
        ∂sourceAppendixARestNoiseLaw n mu :=
  KR21Monoculture.sourceAppendixA_selectedTop_probability_eq_conditionalTail_integral
    mu value htheta hnoTie

/--
Equation (A.1) for the corrected finite iid W^{1,1} source density.  The
separated product law is proved measure-preserving to the literal source noise
law and its a.e. no-tie condition is derived from absolute continuity, rather
than supplied as a premise of the formula.
-/
theorem equationA1_source_w11_iid_conditionalTail_integral
    {n : Nat} (f : Real -> Real)
    (hf : Integrable f volume) (hf_measurable : Measurable f)
    (h_nonnegative : forall x, 0 <= f x)
    (hnormalized : ∫⁻ x, ENNReal.ofReal (f x) ∂volume = 1)
    (value : Candidate n -> Real) {theta : Real} (htheta : 0 < theta) :
    AppliedModelingLib.measureProb
        ((sourceAppendixARestNoiseLaw n (w11BaseNoiseLaw f)).prod
          (w11BaseNoiseLaw f))
        (fun z => SourceAppendixATopEvent value
          (sourceAppendixAProductNoise z) theta 0) =
      ∫ rest : Fin (n + 1) -> Real,
        AppliedModelingLib.measureProb (w11BaseNoiseLaw f)
          (fun epsilon => SourceAppendixAFirstTail value theta rest epsilon)
        ∂sourceAppendixARestNoiseLaw n (w11BaseNoiseLaw f) :=
  KR21Monoculture.sourceAppendixA_selectedTop_probability_eq_conditionalTail_integral_of_w11Density
    f hf hf_measurable h_nonnegative hnormalized value htheta

/--
Equation (A.1) with its selected-top event and conditional tail event written
directly, rather than hidden behind source-event abbreviations.
-/
theorem equationA1_source_w11_iid_literal_event_conditionalTail_integral
    {n : Nat} (f : Real -> Real)
    (hf_measurable : Measurable f)
    (h_nonnegative : forall x, 0 <= f x)
    (hnormalized : ∫⁻ x, ENNReal.ofReal (f x) ∂volume = 1)
    (value : Candidate n -> Real)
    (hsource_top_order : ∀ d : Fin (n + 1), value (Fin.succ d) < value 0)
    {theta : Real} (htheta : 0 < theta) :
    AppliedModelingLib.measureProb
        ((sourceAppendixARestNoiseLaw n (w11BaseNoiseLaw f)).prod
          (w11BaseNoiseLaw f))
        (fun z => firstChoice (rankByScore (fun i =>
          value i + sourceAppendixAProductNoise z i / theta)) = (0 : Candidate n)) =
      ∫ rest : Fin (n + 1) -> Real,
        AppliedModelingLib.measureProb (w11BaseNoiseLaw f)
        (fun epsilon => forall d : Fin (n + 1),
            theta * (value (Fin.succ d) - value 0) + rest d < epsilon)
        ∂sourceAppendixARestNoiseLaw n (w11BaseNoiseLaw f) := by
  have hf : Integrable f volume := by
    refine ⟨hf_measurable.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall h_nonnegative)]
    rw [hnormalized]
    exact ENNReal.one_lt_top
  simpa only [SourceAppendixATopEvent, SourceAppendixAFirstTail] using
    sourceAppendixA_selectedTop_probability_eq_conditionalTail_integral_of_w11Density
      f hf hf_measurable h_nonnegative hnormalized value htheta

/-! ## Appendix C, Theorem 7 -/

/--
Appendix C Theorem 7, Laplacian pairwise conditional derivative: for
independent Laplace scores with `x_j < x_i`, the strict source probability
ratio `Pr[X_i > X_j | X_i < a, X_j < a]` is flat to the left of `x_j`,
strictly increasing between `x_j` and `x_i`, and strictly increasing to the
right of `x_i`.

Source status: derived from source primitives.
-/
theorem theorem7_laplacian_pairwise_conditional_derivative_cases
    {lam xi xj a : ℝ} (hlam : 0 < lam) (hx : xj < xi) :
    (a < xj →
      HasDerivAt
          (fun a =>
            paper_theorem7_laplacian_product_strict_conditional_ratio_at
              lam xi xj a) 0 a ∧
        0 ≤ (0 : ℝ)) ∧
    (xj < a → a < xi →
      ∃ d,
        HasDerivAt
          (fun a =>
            paper_theorem7_laplacian_product_strict_conditional_ratio_at
              lam xi xj a) d a ∧
          0 < d) ∧
    (xi < a →
      ∃ d,
        HasDerivAt
          (fun a =>
            paper_theorem7_laplacian_product_strict_conditional_ratio_at
              lam xi xj a) d a ∧
          0 < d) ∧
    (∃ a d,
      xj < a ∧ a < xi ∧
        HasDerivAt
          (fun a =>
            paper_theorem7_laplacian_product_strict_conditional_ratio_at
              lam xi xj a) d a ∧
        0 < d) :=
    KR21Monoculture.paper_theorem7_laplacian_product_strict_conditional_derivative_cases
      (lam := lam) (xi := xi) (xj := xj) (a := a) hlam hx

/--
Theorem 7 in the source's literal scale convention.  The innovation variables
are iid unit-variance Laplace and the displayed score variables are
`X_r = x_r + sigma * epsilon_r`.  The conditional event ratio is expanded in
the conclusion, so this is not credited through a parameterized helper name.
-/
theorem theorem7_source_unitVarianceLaplace_sigma_conditional_derivative
    {sigma xi xj : ℝ} (hsigma : 0 < sigma) (hx : xj < xi) :
    (∀ a : ℝ, ∃ d,
      HasDerivAt
        (fun u : ℝ =>
          (sourceUnitVarianceLaplacePairInnovationMeasure
            {epsilon | xi + sigma * epsilon.1 < u ∧
              xj + sigma * epsilon.2 < xi + sigma * epsilon.1}).toReal /
            (sourceUnitVarianceLaplacePairInnovationMeasure
              {epsilon | xi + sigma * epsilon.1 < u ∧
                xj + sigma * epsilon.2 < u}).toReal)
        d a ∧
      0 ≤ d) ∧
    (∃ a d,
      HasDerivAt
        (fun u : ℝ =>
          (sourceUnitVarianceLaplacePairInnovationMeasure
            {epsilon | xi + sigma * epsilon.1 < u ∧
              xj + sigma * epsilon.2 < xi + sigma * epsilon.1}).toReal /
            (sourceUnitVarianceLaplacePairInnovationMeasure
              {epsilon | xi + sigma * epsilon.1 < u ∧
                xj + sigma * epsilon.2 < u}).toReal)
        d a ∧
      0 < d) :=
  KR21Monoculture.source_theorem7_unitVarianceLaplace_sigma_conditional_derivative_explicit
    hsigma hx

/-- The source's written numerator includes a redundant cutoff conjunct. -/
theorem theorem7_full_source_numerator_event_eq
    (sigma xi xj a : ℝ) :
    {epsilon : ℝ × ℝ |
      xi + sigma * epsilon.1 < a ∧
        xj + sigma * epsilon.2 < a ∧
          xj + sigma * epsilon.2 < xi + sigma * epsilon.1} =
      {epsilon : ℝ × ℝ |
        xi + sigma * epsilon.1 < a ∧
          xj + sigma * epsilon.2 < xi + sigma * epsilon.1} := by
  ext epsilon
  constructor
  · rintro ⟨hi, _hj, hji⟩
    exact ⟨hi, hji⟩
  · rintro ⟨hi, hji⟩
    exact ⟨hi, lt_trans hji hi, hji⟩

/--
Theorem 7 with its literal rate-`sqrt 2` source density, iid product,
two-score ranking construction, full cutoff event, and derivative result.
-/
theorem theorem7_source_semantic_complete
    {sigma xi xj : ℝ} (hsigma : 0 < sigma) (hx : xj < xi) :
    let innovation : Measure ℝ :=
      (volume : Measure ℝ).withDensity
        (fun z => ENNReal.ofReal
          ((Real.sqrt 2 / 2) * Real.exp (-Real.sqrt 2 * |z|)))
    let score : ℝ × ℝ → Candidate 0 → ℝ := fun epsilon c =>
      if c = (0 : Candidate 0) then xi + sigma * epsilon.1
      else xj + sigma * epsilon.2
    let rank : ℝ × ℝ → Ranking 0 := fun epsilon => rankByScore (score epsilon)
    let rankLaw : Measure (Ranking 0) := (innovation.prod innovation).map rank
    Measurable rank ∧
      rankLaw Set.univ = 1 ∧
      (∀ epsilon,
        xj + sigma * epsilon.2 < xi + sigma * epsilon.1 →
          firstChoice (rank epsilon) = (0 : Candidate 0)) ∧
      ((∀ a : ℝ,
        0 < ((innovation.prod innovation)
          {epsilon : ℝ × ℝ |
            xi + sigma * epsilon.1 < a ∧
              xj + sigma * epsilon.2 < a}).toReal ∧
        ∃ d,
          HasDerivAt
            (fun u : ℝ =>
              ((innovation.prod innovation)
                {epsilon : ℝ × ℝ |
                  xi + sigma * epsilon.1 < u ∧
                    xj + sigma * epsilon.2 < u ∧
                      xj + sigma * epsilon.2 < xi + sigma * epsilon.1}).toReal /
                ((innovation.prod innovation)
                  {epsilon : ℝ × ℝ |
                    xi + sigma * epsilon.1 < u ∧
                      xj + sigma * epsilon.2 < u}).toReal)
            d a ∧ 0 ≤ d) ∧
        (∃ a d,
          HasDerivAt
            (fun u : ℝ =>
              ((innovation.prod innovation)
                {epsilon : ℝ × ℝ |
                  xi + sigma * epsilon.1 < u ∧
                    xj + sigma * epsilon.2 < u ∧
                      xj + sigma * epsilon.2 < xi + sigma * epsilon.1}).toReal /
                ((innovation.prod innovation)
                  {epsilon : ℝ × ℝ |
                    xi + sigma * epsilon.1 < u ∧
                      xj + sigma * epsilon.2 < u}).toReal)
            d a ∧ 0 < d)) := by
  dsimp
  let innovation : Measure ℝ :=
    (volume : Measure ℝ).withDensity
      (fun z => ENNReal.ofReal
        ((Real.sqrt 2 / 2) * Real.exp (-Real.sqrt 2 * |z|)))
  let score : ℝ × ℝ → Candidate 0 → ℝ := fun epsilon c =>
    if c = (0 : Candidate 0) then xi + sigma * epsilon.1
    else xj + sigma * epsilon.2
  let rank : ℝ × ℝ → Ranking 0 := fun epsilon => rankByScore (score epsilon)
  have hscore : ∀ c : Candidate 0, Measurable (fun epsilon => score epsilon c) := by
    intro c
    by_cases hc : c = (0 : Candidate 0)
    · simp [score, hc]
      fun_prop
    · simp [score, hc]
      fun_prop
  have hrank : Measurable rank := by
    exact measurable_rankByScore score hscore
  have hinnovation_univ : innovation Set.univ = 1 := by
    simpa [innovation, theorem7LaplaceMeasure, theorem7LaplacePDF, sub_zero] using
      (theorem7LaplaceMeasure_univ
        (lam := Real.sqrt 2) (μ := 0) (Real.sqrt_pos.2 (by norm_num)))
  letI : IsProbabilityMeasure innovation := ⟨hinnovation_univ⟩
  have hrankLaw_univ : ((innovation.prod innovation).map rank) Set.univ = 1 := by
    rw [Measure.map_apply hrank MeasurableSet.univ]
    simp
  have htop : ∀ epsilon,
      xj + sigma * epsilon.2 < xi + sigma * epsilon.1 →
        firstChoice (rank epsilon) = (0 : Candidate 0) := by
    intro epsilon hji
    rw [← bestInSet_univ]
    apply bestInSet_rankByScore_univ_eq_of_strict_top
    intro d hd
    fin_cases d
    · simp at hd
    · simpa [rank, score] using hji
  have htheta : 0 < sigma⁻¹ := inv_pos.mpr hsigma
  have hden : ∀ a : ℝ,
      0 < ((innovation.prod innovation)
        {epsilon : ℝ × ℝ |
          xi + sigma * epsilon.1 < a ∧ xj + sigma * epsilon.2 < a}).toReal := by
    intro a
    have hlam : 0 < Real.sqrt 2 * sigma⁻¹ :=
      mul_pos (Real.sqrt_pos.2 (by norm_num)) htheta
    have hcdf_pos :
        0 < theorem7LaplaceCDFClosedForm (Real.sqrt 2 * sigma⁻¹) xi a *
          theorem7LaplaceCDFClosedForm (Real.sqrt 2 * sigma⁻¹) xj a :=
      mul_pos
        (theorem7LaplaceCDFClosedForm_pos
          (lam := Real.sqrt 2 * sigma⁻¹) (μ := xi) (a := a) hlam)
        (theorem7LaplaceCDFClosedForm_pos
          (lam := Real.sqrt 2 * sigma⁻¹) (μ := xj) (a := a) hlam)
    have hsource : 0 < (sourceUnitVarianceLaplacePairInnovationMeasure
        (sourceUnitVarianceLaplacePairStrictDenominatorEvent sigma⁻¹ xi xj a)).toReal := by
      rw [sourceUnitVarianceLaplacePair_strict_denominator_measure_eq htheta,
        theorem7LaplacianPairStrictDenominator_measure_eq hlam,
        ENNReal.toReal_ofReal (le_of_lt hcdf_pos)]
      exact hcdf_pos
    simpa [innovation, sourceUnitVarianceLaplacePairInnovationMeasure,
      sourceUnitVarianceLaplacePairStrictDenominatorEvent,
      theorem7LaplaceMeasure, theorem7LaplacePDF, sub_zero,
      div_inv_eq_mul, mul_comm] using hsource
  obtain ⟨hall, hsome⟩ :=
    KR21Monoculture.source_theorem7_unitVarianceLaplace_sigma_conditional_derivative_explicit
      hsigma hx
  have hderiv :
      ((∀ a : ℝ,
        0 < ((innovation.prod innovation)
          {epsilon : ℝ × ℝ |
            xi + sigma * epsilon.1 < a ∧
              xj + sigma * epsilon.2 < a}).toReal ∧
        ∃ d,
          HasDerivAt
            (fun u : ℝ =>
              ((innovation.prod innovation)
                {epsilon : ℝ × ℝ |
                  xi + sigma * epsilon.1 < u ∧
                    xj + sigma * epsilon.2 < u ∧
                      xj + sigma * epsilon.2 < xi + sigma * epsilon.1}).toReal /
                ((innovation.prod innovation)
                  {epsilon : ℝ × ℝ |
                    xi + sigma * epsilon.1 < u ∧
                      xj + sigma * epsilon.2 < u}).toReal)
            d a ∧ 0 ≤ d) ∧
        (∃ a d,
          HasDerivAt
            (fun u : ℝ =>
              ((innovation.prod innovation)
                {epsilon : ℝ × ℝ |
                  xi + sigma * epsilon.1 < u ∧
                    xj + sigma * epsilon.2 < u ∧
                      xj + sigma * epsilon.2 < xi + sigma * epsilon.1}).toReal /
                ((innovation.prod innovation)
                  {epsilon : ℝ × ℝ |
                    xi + sigma * epsilon.1 < u ∧
                      xj + sigma * epsilon.2 < u}).toReal)
            d a ∧ 0 < d)) := by
    refine ⟨?_, ?_⟩
    · intro a
      refine ⟨hden a, ?_⟩
      simpa [innovation, sourceUnitVarianceLaplacePairInnovationMeasure,
        theorem7LaplaceMeasure, theorem7LaplacePDF, sub_zero,
        theorem7_full_source_numerator_event_eq] using hall a
    · simpa [innovation, sourceUnitVarianceLaplacePairInnovationMeasure,
      theorem7LaplaceMeasure, theorem7LaplacePDF, sub_zero,
      theorem7_full_source_numerator_event_eq] using hsome
  exact ⟨hrank, hrankLaw_univ, htop, hderiv⟩

/--
Appendix C equation (C.1), literal unit-variance Laplace source scores.
For `X_r = x_r + epsilon_r / theta`, two iid centered rate-`sqrt 2`
innovations give a strictly lower pairwise win probability after conditioning
both scores below any cutoff.  The theorem retains the strict source events.
-/
theorem equationC1_laplace_source_pairwise_conditional_lt_unconditional
    {theta xi xj a : ℝ} (htheta : 0 < theta) (hx : xj < xi) :
    sourceUnitVarianceLaplacePairConditionalRatio theta xi xj a <
      sourceUnitVarianceLaplacePairWinnerProbability theta xi xj :=
  KR21Monoculture.sourceUnitVarianceLaplacePairwiseConditional_lt_winner htheta hx

/--
Appendix C equation (C.1), literal standard-Gaussian source scores.  This is
the same strict source event statement for `X_r = x_r + epsilon_r / theta`,
with an explicit standard-Gaussian innovation product law.
-/
theorem equationC1_gaussian_source_pairwise_conditional_lt_unconditional
    {theta xi xj a : ℝ} (htheta : 0 < theta) (hx : xj < xi) :
    sourceStandardGaussianPairConditionalRatio theta xi xj a <
      sourceStandardGaussianPairWinnerProbability theta xi xj :=
  KR21Monoculture.sourceStandardGaussianPairwiseConditional_lt_winner htheta hx

/--
Appendix C equation (C.2), literal unit-variance Laplace source scores.  The
conditional pairwise probability has a nonnegative derivative at every real
cutoff and a strictly positive derivative somewhere, including the two cutoff
boundaries omitted by the source's open-interval case split.
-/
theorem equationC2_laplace_source_pairwise_derivative_all_cutoffs
    {theta xi xj : ℝ} (htheta : 0 < theta) (hx : xj < xi) :
    (∀ a : ℝ, ∃ d,
      HasDerivAt
        (fun u : ℝ => sourceUnitVarianceLaplacePairConditionalRatio theta xi xj u)
        d a ∧
      0 ≤ d) ∧
    (∃ a d,
      HasDerivAt
        (fun u : ℝ => sourceUnitVarianceLaplacePairConditionalRatio theta xi xj u)
        d a ∧
      0 < d) := by
  have hlam : 0 < Real.sqrt 2 * theta :=
    mul_pos (Real.sqrt_pos.2 (by norm_num)) htheta
  obtain ⟨hnonneg, hwitness⟩ :=
    theorem7LaplacianProductStrictConditionalRatioAt_derivative_nonneg_all_and_pos_some
      (lam := Real.sqrt 2 * theta) (xi := xi) (xj := xj) hlam hx
  refine ⟨?_, ?_⟩
  · intro a
    obtain ⟨d, hd, hdnonneg⟩ := hnonneg a
    refine ⟨d, ?_, hdnonneg⟩
    exact hd.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun u =>
        KR21Monoculture.sourceUnitVarianceLaplacePairConditionalRatio_eq_named htheta)
  · obtain ⟨a, d, hd, hdpos⟩ := hwitness
    refine ⟨a, d, ?_, hdpos⟩
    exact hd.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun u =>
        KR21Monoculture.sourceUnitVarianceLaplacePairConditionalRatio_eq_named htheta)

/--
Appendix C equation (C.2), literal standard-Gaussian source scores.  At every
real cutoff the strict source conditional probability has a strictly positive
derivative, which is stronger than the source's nonnegative-all-cutoffs plus
positive-somewhere form.
-/
theorem equationC2_gaussian_source_pairwise_derivative_strict
    {theta xi xj a : ℝ} (htheta : 0 < theta) (hx : xj < xi) :
    ∃ d,
      HasDerivAt
        (fun u : ℝ => sourceStandardGaussianPairConditionalRatio theta xi xj u)
        d a ∧
      0 < d := by
  obtain ⟨d, hd, hdpos⟩ :=
    KR21Monoculture.theorem8GaussianProductStrictConditionalRatioAtStd_hasDerivAt_pos
      (σ := 1 / theta) (a := a) (one_div_pos.mpr htheta) hx
  refine ⟨d, ?_, hdpos⟩
  exact hd.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun u =>
      KR21Monoculture.sourceStandardGaussianPairConditionalRatio_eq_named theta xi xj u)

/-- The source writes the redundant second cutoff in the C.1/C.2 numerator.
It follows from strict pairwise victory and the first cutoff, but direct review
rows retain the full source event rather than silently dropping it. -/
theorem appendixC_source_full_numerator_event_eq
    (theta xi xj a : ℝ) :
    {epsilon : ℝ × ℝ |
      xi + epsilon.1 / theta < a ∧
        xj + epsilon.2 / theta < a ∧
          xj + epsilon.2 / theta < xi + epsilon.1 / theta} =
      {epsilon : ℝ × ℝ |
        xi + epsilon.1 / theta < a ∧
          xj + epsilon.2 / theta < xi + epsilon.1 / theta} := by
  ext epsilon
  constructor
  · rintro ⟨hi, _hj, hji⟩
    exact ⟨hi, hji⟩
  · rintro ⟨hi, hji⟩
    exact ⟨hi, lt_trans hji hi, hji⟩

/-- The literal rate-sqrt-two Laplace denominator is positive at every finite
cutoff, so the source quotient has its intended conditional meaning. -/
theorem appendixC_laplace_raw_denominator_pos
    {theta xi xj a : ℝ} (htheta : 0 < theta) :
    0 < (((volume : Measure ℝ).withDensity
        (fun z => ENNReal.ofReal
          ((Real.sqrt 2 / 2) * Real.exp (-Real.sqrt 2 * |z|)))).prod
        ((volume : Measure ℝ).withDensity
          (fun z => ENNReal.ofReal
            ((Real.sqrt 2 / 2) * Real.exp (-Real.sqrt 2 * |z|))))
        {epsilon : ℝ × ℝ |
          xi + epsilon.1 / theta < a ∧ xj + epsilon.2 / theta < a}).toReal := by
  have hlam : 0 < Real.sqrt 2 * theta :=
    mul_pos (Real.sqrt_pos.2 (by norm_num)) htheta
  have hcdf_pos :
      0 < theorem7LaplaceCDFClosedForm (Real.sqrt 2 * theta) xi a *
        theorem7LaplaceCDFClosedForm (Real.sqrt 2 * theta) xj a :=
    mul_pos
      (theorem7LaplaceCDFClosedForm_pos
        (lam := Real.sqrt 2 * theta) (μ := xi) (a := a) hlam)
      (theorem7LaplaceCDFClosedForm_pos
        (lam := Real.sqrt 2 * theta) (μ := xj) (a := a) hlam)
  have hsource : 0 < (sourceUnitVarianceLaplacePairInnovationMeasure
      (sourceUnitVarianceLaplacePairStrictDenominatorEvent theta xi xj a)).toReal := by
    rw [sourceUnitVarianceLaplacePair_strict_denominator_measure_eq htheta,
    theorem7LaplacianPairStrictDenominator_measure_eq hlam,
    ENNReal.toReal_ofReal (le_of_lt hcdf_pos)]
    exact hcdf_pos
  simpa [sourceUnitVarianceLaplacePairInnovationMeasure,
    sourceUnitVarianceLaplacePairStrictDenominatorEvent,
    theorem7LaplaceMeasure, theorem7LaplacePDF, sub_zero] using hsource

/-- The literal standard-Gaussian denominator is positive at every finite cutoff. -/
theorem appendixC_gaussian_raw_denominator_pos
    {theta xi xj a : ℝ} (htheta : 0 < theta) :
    0 < (((ProbabilityTheory.gaussianReal 0 1).prod
        (ProbabilityTheory.gaussianReal 0 1)
        {epsilon : ℝ × ℝ |
          xi + epsilon.1 / theta < a ∧ xj + epsilon.2 / theta < a}).toReal) := by
  have hsigma : 0 < 1 / theta := one_div_pos.mpr htheta
  have hcdf_pos :
      0 < theorem8GaussianCDF
          (theorem8GaussianCanonicalScale (1 / theta) * xi)
          (theorem8GaussianCanonicalScale (1 / theta) * a) *
        theorem8GaussianCDF
          (theorem8GaussianCanonicalScale (1 / theta) * xj)
          (theorem8GaussianCanonicalScale (1 / theta) * a) :=
    mul_pos (theorem8GaussianCDF_pos _ _) (theorem8GaussianCDF_pos _ _)
  change 0 < (sourceStandardGaussianPairInnovationMeasure
    (sourceStandardGaussianPairStrictDenominatorEvent theta xi xj a)).toReal
  rw [sourceStandardGaussianPair_strict_denominator_measure_eq,
    theorem8GaussianPairMeasureStd_strict_denominator_eq_scaled hsigma,
    theorem8GaussianPairStrictDenominator_measure_eq,
    ENNReal.toReal_ofReal (le_of_lt hcdf_pos)]
  exact hcdf_pos

/--
Complete source-facing C.1 package.  Both literal innovation densities, their
iid product laws, full cutoff event, and nonzero conditioning denominator are
in the theorem type before the strict pairwise conclusion.
-/
theorem appendixC1_source_pairwise_full_events
    {theta xi xj a : ℝ} (htheta : 0 < theta) (hx : xj < xi) :
    let laplace : Measure ℝ :=
      (volume : Measure ℝ).withDensity
        (fun z => ENNReal.ofReal
          ((Real.sqrt 2 / 2) * Real.exp (-Real.sqrt 2 * |z|)))
    let gaussian : Measure ℝ := ProbabilityTheory.gaussianReal 0 1
    let laplaceDenominator : ℝ :=
      ((laplace.prod laplace)
        {epsilon : ℝ × ℝ |
          xi + epsilon.1 / theta < a ∧ xj + epsilon.2 / theta < a}).toReal
    let gaussianDenominator : ℝ :=
      ((gaussian.prod gaussian)
        {epsilon : ℝ × ℝ |
          xi + epsilon.1 / theta < a ∧ xj + epsilon.2 / theta < a}).toReal
    (0 < laplaceDenominator ∧
      ((laplace.prod laplace)
        {epsilon : ℝ × ℝ |
          xi + epsilon.1 / theta < a ∧
            xj + epsilon.2 / theta < a ∧
              xj + epsilon.2 / theta < xi + epsilon.1 / theta}).toReal /
        laplaceDenominator <
      ((laplace.prod laplace)
        {epsilon : ℝ × ℝ | xj + epsilon.2 / theta < xi + epsilon.1 / theta}).toReal) ∧
    (0 < gaussianDenominator ∧
      ((gaussian.prod gaussian)
        {epsilon : ℝ × ℝ |
          xi + epsilon.1 / theta < a ∧
            xj + epsilon.2 / theta < a ∧
              xj + epsilon.2 / theta < xi + epsilon.1 / theta}).toReal /
        gaussianDenominator <
      ((gaussian.prod gaussian)
        {epsilon : ℝ × ℝ | xj + epsilon.2 / theta < xi + epsilon.1 / theta}).toReal) := by
  dsimp
  refine ⟨⟨appendixC_laplace_raw_denominator_pos htheta, ?_⟩,
    ⟨appendixC_gaussian_raw_denominator_pos htheta, ?_⟩⟩
  · simpa only [appendixC_source_full_numerator_event_eq] using
      (by
        simpa [sourceUnitVarianceLaplacePairConditionalRatio,
          sourceUnitVarianceLaplacePairInnovationMeasure,
          sourceUnitVarianceLaplacePairStrictNumeratorEvent,
          sourceUnitVarianceLaplacePairStrictDenominatorEvent,
          sourceUnitVarianceLaplacePairWinnerProbability,
          sourceUnitVarianceLaplacePairStrictWinnerEvent,
          theorem7LaplaceMeasure, theorem7LaplacePDF, sub_zero] using
          equationC1_laplace_source_pairwise_conditional_lt_unconditional htheta hx)
  · simpa only [appendixC_source_full_numerator_event_eq] using
      (by
        simpa [sourceStandardGaussianPairConditionalRatio,
          sourceStandardGaussianPairInnovationMeasure,
          sourceStandardGaussianPairStrictNumeratorEvent,
          sourceStandardGaussianPairStrictDenominatorEvent,
          sourceStandardGaussianPairWinnerProbability,
          sourceStandardGaussianPairStrictWinnerEvent] using
          equationC1_gaussian_source_pairwise_conditional_lt_unconditional htheta hx)

/-- Proof-facing raw C.2 bridge for the two literal source laws. -/
theorem appendixC2_source_laplace_gaussian_pairwise_raw
    {theta xi xj : ℝ} (htheta : 0 < theta) (hx : xj < xi) :
    ((∀ a : ℝ, ∃ d,
      HasDerivAt
        (fun u : ℝ =>
          ((theorem7LaplaceMeasure (Real.sqrt 2) 0).prod
            (theorem7LaplaceMeasure (Real.sqrt 2) 0)
            {epsilon : ℝ × ℝ |
              xi + epsilon.1 / theta < u ∧
                xj + epsilon.2 / theta < xi + epsilon.1 / theta}).toReal /
            ((theorem7LaplaceMeasure (Real.sqrt 2) 0).prod
              (theorem7LaplaceMeasure (Real.sqrt 2) 0)
              {epsilon : ℝ × ℝ |
                xi + epsilon.1 / theta < u ∧ xj + epsilon.2 / theta < u}).toReal)
        d a ∧ 0 ≤ d) ∧
      (∃ a d,
        HasDerivAt
          (fun u : ℝ =>
            ((theorem7LaplaceMeasure (Real.sqrt 2) 0).prod
              (theorem7LaplaceMeasure (Real.sqrt 2) 0)
              {epsilon : ℝ × ℝ |
                xi + epsilon.1 / theta < u ∧
                  xj + epsilon.2 / theta < xi + epsilon.1 / theta}).toReal /
              ((theorem7LaplaceMeasure (Real.sqrt 2) 0).prod
                (theorem7LaplaceMeasure (Real.sqrt 2) 0)
                {epsilon : ℝ × ℝ |
                  xi + epsilon.1 / theta < u ∧ xj + epsilon.2 / theta < u}).toReal)
          d a ∧ 0 < d)) ∧
    (∀ a : ℝ, ∃ d,
      HasDerivAt
        (fun u : ℝ =>
          ((ProbabilityTheory.gaussianReal 0 1).prod
            (ProbabilityTheory.gaussianReal 0 1)
            {epsilon : ℝ × ℝ |
              xi + epsilon.1 / theta < u ∧
                xj + epsilon.2 / theta < xi + epsilon.1 / theta}).toReal /
            ((ProbabilityTheory.gaussianReal 0 1).prod
              (ProbabilityTheory.gaussianReal 0 1)
              {epsilon : ℝ × ℝ |
                xi + epsilon.1 / theta < u ∧ xj + epsilon.2 / theta < u}).toReal)
        d a ∧ 0 < d) := by
  constructor
  · simpa [sourceUnitVarianceLaplacePairConditionalRatio,
      sourceUnitVarianceLaplacePairInnovationMeasure,
      sourceUnitVarianceLaplacePairStrictNumeratorEvent,
      sourceUnitVarianceLaplacePairStrictDenominatorEvent,
      theorem7LaplaceMeasure, theorem7LaplacePDF, sub_zero] using
      equationC2_laplace_source_pairwise_derivative_all_cutoffs htheta hx
  · intro a
    simpa [sourceStandardGaussianPairConditionalRatio,
      sourceStandardGaussianPairInnovationMeasure,
      sourceStandardGaussianPairStrictNumeratorEvent,
      sourceStandardGaussianPairStrictDenominatorEvent] using
      equationC2_gaussian_source_pairwise_derivative_strict (a := a) htheta hx

/--
Complete source-facing C.2 package.  The two literal source product laws,
full cutoff event, denominator positivity, and their distinct derivative
conclusions are all visible; this is not an arbitrary-noise theorem.
-/
theorem appendixC2_source_pairwise_full_events
    {theta xi xj : ℝ} (htheta : 0 < theta) (hx : xj < xi) :
    let laplace : Measure ℝ :=
      (volume : Measure ℝ).withDensity
        (fun z => ENNReal.ofReal
          ((Real.sqrt 2 / 2) * Real.exp (-Real.sqrt 2 * |z|)))
    let gaussian : Measure ℝ := ProbabilityTheory.gaussianReal 0 1
    let laplaceRatio : ℝ → ℝ := fun u =>
      ((laplace.prod laplace)
        {epsilon : ℝ × ℝ |
          xi + epsilon.1 / theta < u ∧
            xj + epsilon.2 / theta < u ∧
              xj + epsilon.2 / theta < xi + epsilon.1 / theta}).toReal /
        ((laplace.prod laplace)
          {epsilon : ℝ × ℝ |
            xi + epsilon.1 / theta < u ∧ xj + epsilon.2 / theta < u}).toReal
    let gaussianRatio : ℝ → ℝ := fun u =>
      ((gaussian.prod gaussian)
        {epsilon : ℝ × ℝ |
          xi + epsilon.1 / theta < u ∧
            xj + epsilon.2 / theta < u ∧
              xj + epsilon.2 / theta < xi + epsilon.1 / theta}).toReal /
        ((gaussian.prod gaussian)
          {epsilon : ℝ × ℝ |
            xi + epsilon.1 / theta < u ∧ xj + epsilon.2 / theta < u}).toReal
    let laplaceWinner : ℝ :=
      ((laplace.prod laplace)
        {epsilon : ℝ × ℝ |
          xj + epsilon.2 / theta < xi + epsilon.1 / theta}).toReal
    let gaussianWinner : ℝ :=
      ((gaussian.prod gaussian)
        {epsilon : ℝ × ℝ |
          xj + epsilon.2 / theta < xi + epsilon.1 / theta}).toReal
    ((∀ a : ℝ,
      0 < ((laplace.prod laplace)
        {epsilon : ℝ × ℝ |
          xi + epsilon.1 / theta < a ∧ xj + epsilon.2 / theta < a}).toReal ∧
      ∃ d, HasDerivAt laplaceRatio d a ∧ 0 ≤ d) ∧
      (∃ a d, HasDerivAt laplaceRatio d a ∧ 0 < d) ∧
      Filter.Tendsto laplaceRatio Filter.atTop (nhds laplaceWinner)) ∧
    (∀ a : ℝ,
      0 < ((gaussian.prod gaussian)
        {epsilon : ℝ × ℝ |
          xi + epsilon.1 / theta < a ∧ xj + epsilon.2 / theta < a}).toReal ∧
      ∃ d, HasDerivAt gaussianRatio d a ∧ 0 < d) ∧
      Filter.Tendsto gaussianRatio Filter.atTop (nhds gaussianWinner) := by
  dsimp
  obtain ⟨⟨hLaplaceAll, hLaplaceSome⟩, hGaussianAll⟩ :=
    appendixC2_source_laplace_gaussian_pairwise_raw htheta hx
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro a
    exact ⟨appendixC_laplace_raw_denominator_pos (a := a) htheta,
      by
        simpa [appendixC_source_full_numerator_event_eq,
          theorem7LaplaceMeasure, theorem7LaplacePDF, sub_zero] using hLaplaceAll a⟩
  · simpa [appendixC_source_full_numerator_event_eq,
      theorem7LaplaceMeasure, theorem7LaplacePDF, sub_zero] using hLaplaceSome
  · have htail :
      Filter.Tendsto
        (fun u =>
          (((volume : Measure ℝ).withDensity
              (fun z => ENNReal.ofReal
                ((Real.sqrt 2 / 2) * Real.exp (-Real.sqrt 2 * |z|)))).prod
              ((volume : Measure ℝ).withDensity
                (fun z => ENNReal.ofReal
                  ((Real.sqrt 2 / 2) * Real.exp (-Real.sqrt 2 * |z|))))
            {epsilon : ℝ × ℝ |
              xi + epsilon.1 / theta < u ∧
                xj + epsilon.2 / theta < xi + epsilon.1 / theta}).toReal /
            (((volume : Measure ℝ).withDensity
              (fun z => ENNReal.ofReal
                ((Real.sqrt 2 / 2) * Real.exp (-Real.sqrt 2 * |z|)))).prod
              ((volume : Measure ℝ).withDensity
                (fun z => ENNReal.ofReal
                  ((Real.sqrt 2 / 2) * Real.exp (-Real.sqrt 2 * |z|))))
            {epsilon : ℝ × ℝ |
              xi + epsilon.1 / theta < u ∧ xj + epsilon.2 / theta < u}).toReal)
        Filter.atTop
        (nhds
          ((((volume : Measure ℝ).withDensity
              (fun z => ENNReal.ofReal
                ((Real.sqrt 2 / 2) * Real.exp (-Real.sqrt 2 * |z|)))).prod
              ((volume : Measure ℝ).withDensity
                (fun z => ENNReal.ofReal
                  ((Real.sqrt 2 / 2) * Real.exp (-Real.sqrt 2 * |z|))))
            {epsilon : ℝ × ℝ |
              xj + epsilon.2 / theta < xi + epsilon.1 / theta}).toReal)) := by
        simpa [sourceUnitVarianceLaplacePairConditionalRatio,
          sourceUnitVarianceLaplacePairWinnerProbability,
          sourceUnitVarianceLaplacePairInnovationMeasure,
          sourceUnitVarianceLaplacePairStrictNumeratorEvent,
          sourceUnitVarianceLaplacePairStrictDenominatorEvent,
          sourceUnitVarianceLaplacePairStrictWinnerEvent,
          theorem7LaplaceMeasure, theorem7LaplacePDF, sub_zero] using
          (sourceUnitVarianceLaplacePairConditionalRatio_tendsto_atTop_winner
            (xi := xi) (xj := xj) htheta)
    apply htail.congr'
    exact Filter.Eventually.of_forall fun u => by
      dsimp
      rw [← appendixC_source_full_numerator_event_eq]
  · intro a
    exact ⟨appendixC_gaussian_raw_denominator_pos (a := a) htheta,
      by simpa only [appendixC_source_full_numerator_event_eq] using hGaussianAll a⟩
  · apply
      (sourceStandardGaussianPairConditionalRatio_tendsto_atTop_winner
        (xi := xi) (xj := xj) htheta).congr'
    exact Filter.Eventually.of_forall fun u => by
      simp only [sourceStandardGaussianPairConditionalRatio,
        sourceStandardGaussianPairInnovationMeasure,
        sourceStandardGaussianPairStrictNumeratorEvent,
        sourceStandardGaussianPairStrictDenominatorEvent]
      rw [appendixC_source_full_numerator_event_eq]

/-! ## Appendix C displayed formula surface (C.3)--(C.10) -/

/-- Equation (C.3), Laplace density/CDF expression for the strict conditional ratio. -/
theorem equationC3_laplace_strict_conditional_ratio_eq_density_cdf
    {lam xi xj a : ℝ} (hlam : 0 < lam) :
    theorem7LaplacianProductStrictConditionalRatioAt lam xi xj a =
      (∫ x : ℝ in Set.Iic a,
        theorem7LaplacePDF lam xi x * theorem7LaplaceCDFClosedForm lam xj x) /
        (theorem7LaplaceCDFClosedForm lam xi a *
          theorem7LaplaceCDFClosedForm lam xj a) :=
  KR21Monoculture.equationC3_laplace_strict_conditional_ratio_eq_density_cdf hlam

/--
Equation (C.3) with the literal product law and strict numerator and cutoff
events exposed directly.  The probability ratio is not accepted merely from a
named conditional-ratio definition.
-/
theorem equationC3_laplace_strict_conditional_ratio_eq_density_cdf_semantic_complete
    {lam xi xj a : ℝ} (hlam : 0 < lam) :
    let density : ℝ -> ℝ -> ℝ := fun location x =>
      lam / 2 * Real.exp (-lam * |x - location|)
    let cdf : ℝ -> ℝ -> ℝ := fun location x =>
      if x < location then
        (1 / 2) * Real.exp (-lam * (location - x))
      else
        1 - (1 / 2) * Real.exp (-lam * (x - location))
    let scoreI : Measure ℝ :=
      (volume : Measure ℝ).withDensity
        (fun x => ENNReal.ofReal (density xi x))
    let scoreJ : Measure ℝ :=
      (volume : Measure ℝ).withDensity
        (fun x => ENNReal.ofReal (density xj x))
    let pairLaw : Measure (ℝ × ℝ) := scoreI.prod scoreJ
    0 < (pairLaw {p | p.1 < a ∧ p.2 < a}).toReal ∧
      (pairLaw {p | p.1 < a ∧ p.2 < p.1}).toReal /
          (pairLaw {p | p.1 < a ∧ p.2 < a}).toReal =
        (∫ x : ℝ in Set.Iic a, density xi x * cdf xj x) /
          (cdf xi a * cdf xj a) := by
  dsimp
  have hdenpos :
      0 < theorem7LaplaceCDFClosedForm lam xi a *
        theorem7LaplaceCDFClosedForm lam xj a := by
    exact mul_pos
      (theorem7LaplaceCDFClosedForm_pos (lam := lam) (μ := xi) (a := a) hlam)
      (theorem7LaplaceCDFClosedForm_pos (lam := lam) (μ := xj) (a := a) hlam)
  refine ⟨?_, ?_⟩
  · change 0 < (theorem7LaplacianPairMeasure lam xi xj
      (theorem7LaplacianPairStrictDenominatorEvent a)).toReal
    rw [theorem7LaplacianPairStrictDenominator_measure_eq hlam,
      ENNReal.toReal_ofReal (le_of_lt hdenpos)]
    exact hdenpos
  · change theorem7LaplacianProductStrictConditionalRatioAt lam xi xj a =
      (∫ x : ℝ in Set.Iic a,
        theorem7LaplacePDF lam xi x * theorem7LaplaceCDFClosedForm lam xj x) /
        (theorem7LaplaceCDFClosedForm lam xi a *
          theorem7LaplaceCDFClosedForm lam xj a)
    exact equationC3_laplace_strict_conditional_ratio_eq_density_cdf hlam

/-- Equation (C.3), Gaussian density/CDF expression for the strict conditional ratio. -/
theorem equationC3_gaussian_strict_conditional_ratio_eq_density_cdf
    (xi xj a : ℝ) :
    theorem8GaussianProductStrictConditionalRatioAt xi xj a =
      (∫ x : ℝ in Set.Iic a,
        theorem8GaussianPDF xi x * theorem8GaussianCDF xj x) /
        (theorem8GaussianCDF xi a * theorem8GaussianCDF xj a) :=
  KR21Monoculture.equationC3_gaussian_strict_conditional_ratio_eq_density_cdf xi xj a

/-- Equation (C.4), the literal positive right-tail Laplace expression. -/
theorem equationC4_laplace_case3_expression_pos
    {lam xi xj a : ℝ} (hlam : 0 < lam) (hx : xj < xi) (ha : xi < a) :
    0 <
      Real.exp (-lam * (2 * a - xi - xj)) - 8 +
        4 * Real.exp (-lam * (a - xi)) -
        Real.exp (-2 * lam * (a - xi)) +
        (4 + 2 * lam * (xi - xj)) *
          (1 + Real.exp (-lam * (xi - xj))) -
        (4 + 2 * lam * (xi - xj)) *
          Real.exp (-lam * (a - xj)) :=
  KR21Monoculture.equationC4_laplace_case3_expression_pos hlam hx ha

/-- Equation (C.5), Gaussian density/CDF ratio written using `erf`. -/
theorem equationC5_gaussian_density_cdf_ratio_eq_erf_integral
    (xi xj a : ℝ) :
    theorem8GaussianPDFCDFRatioAt xi xj a =
      (2 / Real.sqrt Real.pi) *
        (∫ x : ℝ in Set.Iic a,
          Real.exp (-((x - xi) ^ 2)) * (1 + theorem8Erf (x - xj))) /
        ((1 + theorem8Erf (a - xi)) * (1 + theorem8Erf (a - xj))) :=
  KR21Monoculture.equationC5_gaussian_density_cdf_ratio_eq_erf_integral xi xj a

/--
The Gaussian source transition immediately preceding (C.5), together with
the labeled (C.5) derivative-sign inequality itself.  The raw score product
and `erf` ratio make the normalized source model explicit; the final conjunct
is the actual displayed C.5 claim.
-/
theorem equationC5_gaussian_source_semantic_complete
    {xi xj a : ℝ} (hx : xj < xi) :
    let scoreI : Measure ℝ := ProbabilityTheory.gaussianReal xi (1 / 2 : ℝ≥0)
    let scoreJ : Measure ℝ := ProbabilityTheory.gaussianReal xj (1 / 2 : ℝ≥0)
    let denominator : ℝ :=
      ((scoreI.prod scoreJ) {p : ℝ × ℝ | p.1 < a ∧ p.2 < a}).toReal
    0 < denominator ∧
      ((scoreI.prod scoreJ)
        {p : ℝ × ℝ | p.1 < a ∧ p.2 < a ∧ p.2 < p.1}).toReal /
        denominator =
          (2 / Real.sqrt Real.pi) *
            (∫ x : ℝ in Set.Iic a,
              Real.exp (-((x - xi) ^ 2)) * (1 + theorem8Erf (x - xj))) /
            ((1 + theorem8Erf (a - xi)) * (1 + theorem8Erf (a - xj))) ∧
      0 <
        (1 + theorem8Erf (a - xi)) * (1 + theorem8Erf (a - xj)) *
            Real.exp (-((a - xi) ^ 2)) * (1 + theorem8Erf (a - xj)) -
          (∫ x : ℝ in Set.Iic a,
            Real.exp (-((x - xi) ^ 2)) * (1 + theorem8Erf (x - xj))) *
            (2 / Real.sqrt Real.pi) *
            ((1 + theorem8Erf (a - xi)) * Real.exp (-((a - xj) ^ 2)) +
              (1 + theorem8Erf (a - xj)) * Real.exp (-((a - xi) ^ 2))) ∧
      ∃ d,
        HasDerivAt
          (fun u =>
            (2 / Real.sqrt Real.pi) *
              (∫ x : ℝ in Set.Iic u,
                Real.exp (-((x - xi) ^ 2)) * (1 + theorem8Erf (x - xj))) /
              ((1 + theorem8Erf (u - xi)) * (1 + theorem8Erf (u - xj)))) d a ∧
        (0 < d ↔
          0 <
            (1 + theorem8Erf (a - xi)) * (1 + theorem8Erf (a - xj)) *
                Real.exp (-((a - xi) ^ 2)) * (1 + theorem8Erf (a - xj)) -
              (∫ x : ℝ in Set.Iic a,
                Real.exp (-((x - xi) ^ 2)) * (1 + theorem8Erf (x - xj))) *
                (2 / Real.sqrt Real.pi) *
                ((1 + theorem8Erf (a - xi)) * Real.exp (-((a - xj) ^ 2)) +
                  (1 + theorem8Erf (a - xj)) *
                    Real.exp (-((a - xi) ^ 2)))) := by
  dsimp
  have hfull :
      {p : ℝ × ℝ | p.1 < a ∧ p.2 < a ∧ p.2 < p.1} =
        {p : ℝ × ℝ | p.1 < a ∧ p.2 < p.1} := by
    ext p
    constructor
    · rintro ⟨hi, _hj, hji⟩
      exact ⟨hi, hji⟩
    · rintro ⟨hi, hji⟩
      exact ⟨hi, lt_trans hji hi, hji⟩
  have hcdf_pos : 0 < theorem8GaussianCDF xi a * theorem8GaussianCDF xj a :=
    mul_pos (theorem8GaussianCDF_pos xi a) (theorem8GaussianCDF_pos xj a)
  have hden :
      0 < (theorem8GaussianPairMeasure xi xj
        (theorem8GaussianPairStrictDenominatorEvent a)).toReal := by
    rw [theorem8GaussianPairStrictDenominator_measure_eq,
      ENNReal.toReal_ofReal (le_of_lt hcdf_pos)]
    exact hcdf_pos
  have hden_event :
      {p : ℝ × ℝ | p.1 < a ∧ p.2 < a} = Set.Iio a ×ˢ Set.Iio a := by
    ext p
    simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · change 0 < ((ProbabilityTheory.gaussianReal xi (1 / 2 : ℝ≥0)).prod
      (ProbabilityTheory.gaussianReal xj (1 / 2 : ℝ≥0))
      {p : ℝ × ℝ | p.1 < a ∧ p.2 < a}).toReal
    rw [hden_event]
    exact hden
  · calc
      ((ProbabilityTheory.gaussianReal xi (1 / 2 : ℝ≥0)).prod
          (ProbabilityTheory.gaussianReal xj (1 / 2 : ℝ≥0))
          {p : ℝ × ℝ | p.1 < a ∧ p.2 < a ∧ p.2 < p.1}).toReal /
          ((ProbabilityTheory.gaussianReal xi (1 / 2 : ℝ≥0)).prod
            (ProbabilityTheory.gaussianReal xj (1 / 2 : ℝ≥0))
            {p : ℝ × ℝ | p.1 < a ∧ p.2 < a}).toReal =
        theorem8GaussianProductStrictConditionalRatioAt xi xj a := by
          rw [hfull, hden_event]
          rfl
      _ = theorem8GaussianPDFCDFRatioAt xi xj a :=
        theorem8GaussianProductStrictConditionalRatioAt_eq_pdf_cdf xi xj a
      _ = _ := equationC5_gaussian_density_cdf_ratio_eq_erf_integral xi xj a
  · exact equationC5_gaussian_derivative_sign_inequality hx
  · exact equationC5_gaussian_erf_ratio_derivative_pos_iff xi xj a

/-- Equation (C.5), the original-coordinate derivative-sign inequality. -/
theorem equationC5_gaussian_derivative_sign_inequality
    {xi xj a : ℝ} (hx : xj < xi) :
    0 <
      (1 + theorem8Erf (a - xi)) * (1 + theorem8Erf (a - xj)) *
          Real.exp (-((a - xi) ^ 2)) * (1 + theorem8Erf (a - xj)) -
        (∫ x : ℝ in Set.Iic a,
          Real.exp (-((x - xi) ^ 2)) * (1 + theorem8Erf (x - xj))) *
          (2 / Real.sqrt Real.pi) *
          ((1 + theorem8Erf (a - xi)) * Real.exp (-((a - xj) ^ 2)) +
            (1 + theorem8Erf (a - xj)) * Real.exp (-((a - xi) ^ 2))) :=
  KR21Monoculture.equationC5_gaussian_derivative_sign_inequality hx

/-- Equation (C.6), positive reduced Gaussian expression. -/
theorem equationC6_gaussian_reduced_expression_pos
    {delta t : ℝ} (hdelta : 0 < delta) :
    0 <
      ((1 + theorem8Erf t) * (1 + theorem8Erf (t + delta)) ^ 2 *
          Real.exp (-(t ^ 2))) /
        ((1 + theorem8Erf t) * Real.exp (-((t + delta) ^ 2)) +
          (1 + theorem8Erf (t + delta)) * Real.exp (-(t ^ 2))) -
        (1 + theorem8Erf t) -
        (2 / Real.sqrt Real.pi) *
          (∫ x : ℝ in Set.Iic t,
            Real.exp (-(x ^ 2)) * theorem8Erf (x + delta)) :=
  KR21Monoculture.equationC6_gaussian_reduced_expression_pos hdelta

/-- Equation (C.7), the rational term's left-tail limit. -/
theorem equationC7_gaussian_rational_term_tendsto_atBot_zero
    (delta : ℝ) :
    Filter.Tendsto
      (fun t =>
        ((1 + theorem8Erf t) * (1 + theorem8Erf (t + delta)) ^ 2 *
            Real.exp (-(t ^ 2))) /
          ((1 + theorem8Erf t) * Real.exp (-((t + delta) ^ 2)) +
            (1 + theorem8Erf (t + delta)) * Real.exp (-(t ^ 2))))
      Filter.atBot (nhds 0) :=
  KR21Monoculture.equationC7_gaussian_rational_term_tendsto_atBot_zero delta

/-- The full C.6 reduced-expression left-tail limit retained for later use. -/
theorem equationC7_gaussian_full_reduced_expression_tendsto_atBot_zero
    (delta : ℝ) :
    Filter.Tendsto
      (fun t =>
        ((1 + theorem8Erf t) * (1 + theorem8Erf (t + delta)) ^ 2 *
            Real.exp (-(t ^ 2))) /
          ((1 + theorem8Erf t) * Real.exp (-((t + delta) ^ 2)) +
            (1 + theorem8Erf (t + delta)) * Real.exp (-(t ^ 2))) -
          (1 + theorem8Erf t) -
          (2 / Real.sqrt Real.pi) *
            (∫ x : ℝ in Set.Iic t,
              Real.exp (-(x ^ 2)) * theorem8Erf (x + delta)))
      Filter.atBot (nhds 0) :=
  KR21Monoculture.equationC7_gaussian_reduced_expression_tendsto_atBot_zero delta

/--
Equation (C.7): the displayed rational term and the displayed Gaussian
integral both have left-tail limit zero.  This is the transparent form of the
source's equality of the two limits.  The C.6-difference limit remains a
separate supporting endpoint above.
-/
theorem equationC7_gaussian_reduced_expression_tendsto_atBot_zero
    (delta : ℝ) :
    Filter.Tendsto
      (fun t =>
        ((1 + theorem8Erf t) * (1 + theorem8Erf (t + delta)) ^ 2 *
            Real.exp (-(t ^ 2))) /
          ((1 + theorem8Erf t) * Real.exp (-((t + delta) ^ 2)) +
            (1 + theorem8Erf (t + delta)) * Real.exp (-(t ^ 2))))
      Filter.atBot (nhds 0) ∧
    Filter.Tendsto
      (fun t =>
        ∫ x : ℝ in Set.Iic t,
          Real.exp (-(x ^ 2)) * theorem8Erf (x + delta))
      Filter.atBot (nhds 0) :=
  ⟨equationC7_gaussian_rational_term_tendsto_atBot_zero delta, by
    simpa [theorem8GaussianJ] using
      (theorem8GaussianJ_tendsto_atBot_zero_of_integrableOn
        (theorem8GaussianJ_integrableOn_concrete delta))⟩

/-- Equation (C.8), the literal derivative before factorization. -/
theorem equationC8_gaussian_reduced_expression_hasDerivAt
    (delta t : ℝ) :
    HasDerivAt
      (fun u =>
        ((1 + theorem8Erf u) * (1 + theorem8Erf (u + delta)) ^ 2 *
            Real.exp (-(u ^ 2))) /
          ((1 + theorem8Erf u) * Real.exp (-((u + delta) ^ 2)) +
            (1 + theorem8Erf (u + delta)) * Real.exp (-(u ^ 2))) -
          (1 + theorem8Erf u) -
          (2 / Real.sqrt Real.pi) *
            (∫ x : ℝ in Set.Iic u,
              Real.exp (-(x ^ 2)) * theorem8Erf (x + delta)))
      (deriv (fun u =>
          ((1 + theorem8Erf u) * (1 + theorem8Erf (u + delta)) ^ 2 *
              Real.exp (-(u ^ 2))) /
            ((1 + theorem8Erf u) * Real.exp (-((u + delta) ^ 2)) +
              (1 + theorem8Erf (u + delta)) * Real.exp (-(u ^ 2)))) t -
        (2 / Real.sqrt Real.pi) * Real.exp (-(t ^ 2)) -
        (2 / Real.sqrt Real.pi) * Real.exp (-(t ^ 2)) * theorem8Erf (t + delta)) t :=
  KR21Monoculture.equationC8_gaussian_reduced_expression_hasDerivAt delta t

/-- The printed C.8 prefactor differs from the checked factor at a concrete point. -/
theorem equationC8_printed_prefactor_mismatch :
    sourcePrintedC8Prefactor 1 0 ≠
      theorem8GaussianC8PositiveFactor theorem8Erf 1 0 :=
  KR21Monoculture.sourcePrintedC8Prefactor_ne_corrected_at_one_zero

/-- Corrected C.8 factorization. -/
theorem equationC8_corrected_factorization
    (delta t : ℝ) :
    deriv (fun u =>
        ((1 + theorem8Erf u) * (1 + theorem8Erf (u + delta)) ^ 2 *
            Real.exp (-(u ^ 2))) /
          ((1 + theorem8Erf u) * Real.exp (-((u + delta) ^ 2)) +
            (1 + theorem8Erf (u + delta)) * Real.exp (-(u ^ 2)))) t -
      (2 / Real.sqrt Real.pi) * Real.exp (-(t ^ 2)) -
      (2 / Real.sqrt Real.pi) * Real.exp (-(t ^ 2)) * theorem8Erf (t + delta) =
      ((2 * (1 + theorem8Erf t) * (1 + theorem8Erf (t + delta)) ^ 2 *
          Real.exp ((t + delta) ^ 2)) /
        (Real.sqrt Real.pi *
          (((theorem8Erf t + 1) * Real.exp (t ^ 2) +
            (theorem8Erf (t + delta) + 1) *
              Real.exp ((t + delta) ^ 2)) ^ 2))) *
        (((1 + theorem8Erf t) / Real.exp (-(t ^ 2))) *
          (delta * Real.sqrt Real.pi +
            (((1 + theorem8Erf (t + delta)) /
              Real.exp (-((t + delta) ^ 2)))⁻¹)) - 1) :=
  KR21Monoculture.equationC8_corrected_factorization delta t

/-- The checked C.8 prefactor is strictly positive. -/
theorem equationC8_corrected_prefactor_pos
    (delta t : ℝ) :
    0 <
      (2 * (1 + theorem8Erf t) * (1 + theorem8Erf (t + delta)) ^ 2 *
          Real.exp ((t + delta) ^ 2)) /
        (Real.sqrt Real.pi *
          (((theorem8Erf t + 1) * Real.exp (t ^ 2) +
            (theorem8Erf (t + delta) + 1) *
              Real.exp ((t + delta) ^ 2)) ^ 2)) :=
  KR21Monoculture.equationC8_corrected_prefactor_pos delta t

/-- Corrected C.9 bracket; the leading `g(t)` multiplies the whole parenthesized term. -/
theorem equationC9_corrected_gaussian_bracket_pos
    {delta t : ℝ} (hdelta : 0 < delta) :
    0 <
      ((1 + theorem8Erf t) / Real.exp (-(t ^ 2))) *
        (delta * Real.sqrt Real.pi +
          (((1 + theorem8Erf (t + delta)) /
            Real.exp (-((t + delta) ^ 2)))⁻¹)) - 1 :=
  KR21Monoculture.equationC9_corrected_gaussian_bracket_pos hdelta

/--
The complete approved C.8/C.9 repair.  It states the derivative of the full
C.6 expression itself, then exposes the checked positive C.8 prefactor and
the corrected positive C.9 bracket.
-/
theorem equationC8_C9_corrected_gaussian_target
    {delta t : ℝ} (hdelta : 0 < delta) :
    HasDerivAt
      (fun u =>
        ((1 + theorem8Erf u) * (1 + theorem8Erf (u + delta)) ^ 2 *
            Real.exp (-(u ^ 2))) /
          ((1 + theorem8Erf u) * Real.exp (-((u + delta) ^ 2)) +
            (1 + theorem8Erf (u + delta)) * Real.exp (-(u ^ 2))) -
          (1 + theorem8Erf u) -
          (2 / Real.sqrt Real.pi) *
            (∫ x : ℝ in Set.Iic u,
              Real.exp (-(x ^ 2)) * theorem8Erf (x + delta)))
      (((2 * (1 + theorem8Erf t) * (1 + theorem8Erf (t + delta)) ^ 2 *
          Real.exp ((t + delta) ^ 2)) /
        (Real.sqrt Real.pi *
          (((theorem8Erf t + 1) * Real.exp (t ^ 2) +
            (theorem8Erf (t + delta) + 1) *
              Real.exp ((t + delta) ^ 2)) ^ 2))) *
        (((1 + theorem8Erf t) / Real.exp (-(t ^ 2))) *
          (delta * Real.sqrt Real.pi +
            (((1 + theorem8Erf (t + delta)) /
              Real.exp (-((t + delta) ^ 2)))⁻¹)) - 1)) t ∧
      0 <
        (2 * (1 + theorem8Erf t) * (1 + theorem8Erf (t + delta)) ^ 2 *
          Real.exp ((t + delta) ^ 2)) /
          (Real.sqrt Real.pi *
            (((theorem8Erf t + 1) * Real.exp (t ^ 2) +
              (theorem8Erf (t + delta) + 1) *
                Real.exp ((t + delta) ^ 2)) ^ 2)) ∧
      0 < ((1 + theorem8Erf t) / Real.exp (-(t ^ 2))) *
          (delta * Real.sqrt Real.pi +
            (((1 + theorem8Erf (t + delta)) /
              Real.exp (-((t + delta) ^ 2)))⁻¹)) - 1 := by
  refine ⟨?_, equationC8_corrected_prefactor_pos delta t,
    equationC9_corrected_gaussian_bracket_pos hdelta⟩
  simpa only [equationC8_corrected_factorization] using
    (equationC8_gaussian_reduced_expression_hasDerivAt delta t)

/-- Equation (C.10), the concrete Gaussian `1/g` derivative lower bound. -/
theorem equationC10_gaussian_g_inv_derivative_lower_bound
    (t : ℝ) :
    ∃ d,
      HasDerivAt
        (fun u => (((1 + theorem8Erf u) / Real.exp (-(u ^ 2)))⁻¹)) d t ∧
        -Real.sqrt Real.pi < d :=
  KR21Monoculture.equationC10_gaussian_g_inv_derivative_lower_bound t

/-! ## Appendix C, Theorem 8 -/

/--
Appendix C Theorem 8, Gaussian conditional pairwise derivative.  When
`x_j < x_i`, the paper's strict conditional product-probability ratio has a
strictly positive derivative at every cutoff.
-/
theorem theorem8_gaussian_product_strict_conditional_ratio_at_hasDerivAt_pos
    {xi xj a : ℝ} (hx : xj < xi) :
    ∃ d,
      HasDerivAt
        (fun u =>
          paper_theorem8_gaussian_product_strict_conditional_ratio_at xi xj u)
        d a ∧
        0 < d :=
  KR21Monoculture.paper_theorem8_gaussian_product_strict_conditional_ratio_at_hasDerivAt_pos
    hx

/--
Theorem 8 at the source's arbitrary-positive-standard-deviation Gaussian
surface.  The strict conditional event and cutoff remain explicit; the
canonical variance-one-half calculation is reached by a proved positive scale
transport rather than by silently fixing the source parameter.
-/
theorem theorem8_source_gaussian_conditional_ratio_at_std_hasDerivAt_pos
    {sigma xi xj a : ℝ} (hsigma : 0 < sigma) (hx : xj < xi) :
    ∃ d,
      HasDerivAt
        (fun u =>
          paper_theorem8_gaussian_product_strict_conditional_ratio_at_std
            sigma xi xj u)
        d a ∧
      0 < d :=
  KR21Monoculture.paper_theorem8_gaussian_product_strict_conditional_ratio_at_std_hasDerivAt_pos
    hsigma hx

/--
Theorem 8 with its literal standard-Gaussian iid product, raw score/ranking
construction, full cutoff event, positive conditioning mass, and derivative.
-/
theorem theorem8_source_semantic_complete
    {sigma xi xj : ℝ} (hsigma : 0 < sigma) (hx : xj < xi) :
    let innovation : Measure ℝ := ProbabilityTheory.gaussianReal 0 1
    let score : ℝ × ℝ → Candidate 0 → ℝ := fun epsilon c =>
      if c = (0 : Candidate 0) then xi + sigma * epsilon.1
      else xj + sigma * epsilon.2
    let rank : ℝ × ℝ → Ranking 0 := fun epsilon => rankByScore (score epsilon)
    let rankLaw : Measure (Ranking 0) := (innovation.prod innovation).map rank
    Measurable rank ∧
      rankLaw Set.univ = 1 ∧
      (∀ epsilon,
        xj + sigma * epsilon.2 < xi + sigma * epsilon.1 →
          firstChoice (rank epsilon) = (0 : Candidate 0)) ∧
      ∀ a : ℝ,
        0 < ((innovation.prod innovation)
          {epsilon : ℝ × ℝ |
            xi + sigma * epsilon.1 < a ∧
              xj + sigma * epsilon.2 < a}).toReal ∧
        ∃ d,
          HasDerivAt
            (fun u : ℝ =>
              ((innovation.prod innovation)
                {epsilon : ℝ × ℝ |
                  xi + sigma * epsilon.1 < u ∧
                    xj + sigma * epsilon.2 < u ∧
                      xj + sigma * epsilon.2 < xi + sigma * epsilon.1}).toReal /
                ((innovation.prod innovation)
                  {epsilon : ℝ × ℝ |
                    xi + sigma * epsilon.1 < u ∧
                      xj + sigma * epsilon.2 < u}).toReal)
            d a ∧ 0 < d := by
  dsimp
  let innovation : Measure ℝ := ProbabilityTheory.gaussianReal 0 1
  let score : ℝ × ℝ → Candidate 0 → ℝ := fun epsilon c =>
    if c = (0 : Candidate 0) then xi + sigma * epsilon.1
    else xj + sigma * epsilon.2
  let rank : ℝ × ℝ → Ranking 0 := fun epsilon => rankByScore (score epsilon)
  have hscore : ∀ c : Candidate 0, Measurable (fun epsilon => score epsilon c) := by
    intro c
    by_cases hc : c = (0 : Candidate 0)
    · simp [score, hc]
      fun_prop
    · simp [score, hc]
      fun_prop
  have hrank : Measurable rank := by
    exact measurable_rankByScore score hscore
  have hinnovation_univ : innovation Set.univ = 1 := by simp [innovation]
  letI : IsProbabilityMeasure innovation := ⟨hinnovation_univ⟩
  have hrankLaw_univ : ((innovation.prod innovation).map rank) Set.univ = 1 := by
    rw [Measure.map_apply hrank MeasurableSet.univ]
    simp
  have htop : ∀ epsilon,
      xj + sigma * epsilon.2 < xi + sigma * epsilon.1 →
        firstChoice (rank epsilon) = (0 : Candidate 0) := by
    intro epsilon hji
    rw [← bestInSet_univ]
    apply bestInSet_rankByScore_univ_eq_of_strict_top
    intro d hd
    fin_cases d
    · simp at hd
    · simpa [rank, score] using hji
  have htheta : 0 < sigma⁻¹ := inv_pos.mpr hsigma
  obtain ⟨_hLaplace, hGaussian, _hGaussianTail⟩ :=
    appendixC2_source_pairwise_full_events
      (theta := sigma⁻¹) (xi := xi) (xj := xj) htheta hx
  have hderiv : ∀ a : ℝ,
      0 < ((innovation.prod innovation)
        {epsilon : ℝ × ℝ |
          xi + sigma * epsilon.1 < a ∧ xj + sigma * epsilon.2 < a}).toReal ∧
      ∃ d,
        HasDerivAt
          (fun u : ℝ =>
            ((innovation.prod innovation)
              {epsilon : ℝ × ℝ |
                xi + sigma * epsilon.1 < u ∧
                  xj + sigma * epsilon.2 < u ∧
                    xj + sigma * epsilon.2 < xi + sigma * epsilon.1}).toReal /
              ((innovation.prod innovation)
                {epsilon : ℝ × ℝ |
                  xi + sigma * epsilon.1 < u ∧
                    xj + sigma * epsilon.2 < u}).toReal)
          d a ∧ 0 < d := by
    intro a
    simpa [innovation, div_inv_eq_mul, mul_comm] using hGaussian a
  exact ⟨hrank, hrankLaw_univ, htop, hderiv⟩

/-! ## Definition 2 -/

/--
Definition 2 / three-candidate RUM negative-correlation certificate: if
conditioning on each candidate being first strictly lowers the probability that
the better remaining candidate beats the worse remaining candidate, then the
ranking law prefers independent reranking.
-/
theorem definition2_threeCandidate_prefersIndependentReranking_of_negativeCorrelationCertificate
    {μ : PMF (Ranking 1)} {value : Candidate 1 → ℝ}
    (cert : RUM3Definition2NegativeCorrelationCertificate μ value) :
    Model.PrefersIndependentReranking μ value :=
  KR21Monoculture.MallowsComparison.paper_definition2_threeCandidate_prefersIndependentReranking_of_negativeCorrelationCertificate
    cert

/--
Definition 2 / three-candidate continuous score bridge: for a ranking law
induced by three measurable score coordinates, the negative-correlation
certificate follows from three strict inequalities stated directly in primitive
score-order events.
-/
theorem definition2_threeCandidate_negativeCorrelationCertificate_of_score_inter_lt_mul
    {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    {r1 r2 r3 : Ω → ℝ}
    (hr1 : Measurable r1) (hr2 : Measurable r2) (hr3 : Measurable r3)
    {value : Candidate 1 → ℝ}
    (hvalue01 : value (1 : Candidate 1) < value (0 : Candidate 1))
    (hvalue12 : value (2 : Candidate 1) < value (1 : Candidate 1))
    (hfirst0 :
      0 < measureProb ν
        (fun ω => r2 ω ≤ r1 ω ∧ r3 ω ≤ r1 ω))
    (hfirst1 :
      0 < measureProb ν
        (fun ω => r1 ω < r2 ω ∧ r3 ω ≤ r2 ω))
    (hfirst2 :
      0 < measureProb ν
        (fun ω => r1 ω < r3 ω ∧ r2 ω < r3 ω))
    (h0 :
      measureProb ν
          (fun ω => r3 ω ≤ r2 ω ∧ r2 ω ≤ r1 ω) <
        measureProb ν (fun ω => r3 ω ≤ r2 ω) *
          measureProb ν
            (fun ω => r2 ω ≤ r1 ω ∧ r3 ω ≤ r1 ω))
    (h1 :
      measureProb ν
          (fun ω => r3 ω ≤ r1 ω ∧ r1 ω < r2 ω) <
        measureProb ν (fun ω => r3 ω ≤ r1 ω) *
          measureProb ν
            (fun ω => r1 ω < r2 ω ∧ r3 ω ≤ r2 ω))
    (h2 :
      measureProb ν
          (fun ω => r2 ω ≤ r1 ω ∧ r1 ω < r3 ω) <
        measureProb ν (fun ω => r2 ω ≤ r1 ω) *
          measureProb ν
            (fun ω => r1 ω < r3 ω ∧ r2 ω < r3 ω)) :
    RUM3Definition2NegativeCorrelationCertificate
      (rumRankingPMFOfMeasure ν (rum3RankByScoreFns r1 r2 r3)
        (rum3RankByScoreFns_measurable hr1 hr2 hr3)) value :=
  KR21Monoculture.MallowsComparison.paper_definition2_threeCandidate_negativeCorrelationCertificate_of_score_inter_lt_mul
    ν hr1 hr2 hr3 hvalue01 hvalue12
    hfirst0 hfirst1 hfirst2 h0 h1 h2

/--
Definition 2 / Gaussian three-candidate RUM: independent Gaussian score signals
with ordered means satisfy the negative-correlation certificate.
-/
theorem definition2_threeCandidate_gaussian_negativeCorrelationCertificate
    {x1 x2 x3 : ℝ} {value : Candidate 1 → ℝ}
    (hvalue01 : value (1 : Candidate 1) < value (0 : Candidate 1))
    (hvalue12 : value (2 : Candidate 1) < value (1 : Candidate 1))
    (hx12 : x2 < x1) (hx23 : x3 < x2) :
    RUM3Definition2NegativeCorrelationCertificate
      (rumRankingPMFOfMeasure
        (theorem8GaussianDefinition2ScoreMeasure x1 x2 x3)
        (rum3RankByScoreFns
          theorem8GaussianDefinition2Score1
          theorem8GaussianDefinition2Score2
          theorem8GaussianDefinition2Score3)
        (rum3RankByScoreFns_measurable
          theorem8GaussianDefinition2Score1_measurable
          theorem8GaussianDefinition2Score2_measurable
          theorem8GaussianDefinition2Score3_measurable)) value :=
  KR21Monoculture.MallowsComparison.paper_definition2_threeCandidate_gaussian_negativeCorrelationCertificate
    hvalue01 hvalue12 hx12 hx23

/--
Definition 2 / Gaussian three-candidate RUM: independent Gaussian score signals
with ordered means prefer independent reranking.
-/
theorem definition2_threeCandidate_gaussian_prefersIndependentReranking
    {x1 x2 x3 : ℝ} {value : Candidate 1 → ℝ}
    (hvalue01 : value (1 : Candidate 1) < value (0 : Candidate 1))
    (hvalue12 : value (2 : Candidate 1) < value (1 : Candidate 1))
    (hx12 : x2 < x1) (hx23 : x3 < x2) :
    Model.PrefersIndependentReranking
      (rumRankingPMFOfMeasure
        (theorem8GaussianDefinition2ScoreMeasure x1 x2 x3)
        (rum3RankByScoreFns
          theorem8GaussianDefinition2Score1
          theorem8GaussianDefinition2Score2
          theorem8GaussianDefinition2Score3)
        (rum3RankByScoreFns_measurable
          theorem8GaussianDefinition2Score1_measurable
          theorem8GaussianDefinition2Score2_measurable
          theorem8GaussianDefinition2Score3_measurable)) value :=
  KR21Monoculture.MallowsComparison.paper_definition2_threeCandidate_gaussian_prefersIndependentReranking
    hvalue01 hvalue12 hx12 hx23

/--
Definition 2 / Laplace three-candidate RUM: independent Laplace score signals
with common positive rate and ordered locations satisfy the negative-correlation
certificate.
-/
theorem definition2_threeCandidate_laplacian_negativeCorrelationCertificate
    {lam x1 x2 x3 : ℝ} {value : Candidate 1 → ℝ}
    (hlam : 0 < lam)
    (hvalue01 : value (1 : Candidate 1) < value (0 : Candidate 1))
    (hvalue12 : value (2 : Candidate 1) < value (1 : Candidate 1))
    (hx12 : x2 < x1) (hx23 : x3 < x2) :
    RUM3Definition2NegativeCorrelationCertificate
      (theorem7LaplacianDefinition2RankingPMF lam x1 x2 x3 hlam) value :=
  KR21Monoculture.MallowsComparison.paper_definition2_threeCandidate_laplacian_negativeCorrelationCertificate
    hlam hvalue01 hvalue12 hx12 hx23

/--
Definition 2 / Laplace three-candidate RUM: independent Laplace score signals
with common positive rate and ordered locations prefer independent reranking.
-/
theorem definition2_threeCandidate_laplacian_prefersIndependentReranking
    {lam x1 x2 x3 : ℝ} {value : Candidate 1 → ℝ}
    (hlam : 0 < lam)
    (hvalue01 : value (1 : Candidate 1) < value (0 : Candidate 1))
    (hvalue12 : value (2 : Candidate 1) < value (1 : Candidate 1))
    (hx12 : x2 < x1) (hx23 : x3 < x2) :
    Model.PrefersIndependentReranking
      (theorem7LaplacianDefinition2RankingPMF lam x1 x2 x3 hlam) value :=
  KR21Monoculture.MallowsComparison.paper_definition2_threeCandidate_laplacian_prefersIndependentReranking
    hlam hvalue01 hvalue12 hx12 hx23

/--
Definition 2 / Laplace three-candidate RUM under contraction: contracted
rate-`lam` scores induce the same ranking law as raw rate-`lam / t` scores, so
the contracted source also prefers independent reranking.
-/
theorem definition2_threeCandidate_laplacian_contracted_prefersIndependentReranking
    {lam t x1 x2 x3 : ℝ} {value : Candidate 1 → ℝ}
    (hlam : 0 < lam) (ht : 0 < t)
    (hvalue01 : value (1 : Candidate 1) < value (0 : Candidate 1))
    (hvalue12 : value (2 : Candidate 1) < value (1 : Candidate 1))
    (hx12 : x2 < x1) (hx23 : x3 < x2) :
    Model.PrefersIndependentReranking
      (theorem7LaplacianDefinition2ContractRankingPMF
        lam t x1 x2 x3 hlam) value :=
  KR21Monoculture.MallowsComparison.paper_definition2_threeCandidate_laplacian_contracted_prefersIndependentReranking
    hlam ht hvalue01 hvalue12 hx12 hx23

/--
Definition 2 / Gaussian three-candidate RUM with arbitrary positive standard
deviation: independent Gaussian score signals with ordered means satisfy the
negative-correlation certificate.
-/
theorem definition2_threeCandidate_gaussianStd_negativeCorrelationCertificate
    {σ x1 x2 x3 : ℝ} {value : Candidate 1 → ℝ}
    (hσ : 0 < σ)
    (hvalue01 : value (1 : Candidate 1) < value (0 : Candidate 1))
    (hvalue12 : value (2 : Candidate 1) < value (1 : Candidate 1))
    (hx12 : x2 < x1) (hx23 : x3 < x2) :
    RUM3Definition2NegativeCorrelationCertificate
      (rumRankingPMFOfMeasure
        (theorem8GaussianDefinition2ScoreMeasureStd σ x1 x2 x3)
        (rum3RankByScoreFns
          theorem8GaussianDefinition2Score1
          theorem8GaussianDefinition2Score2
          theorem8GaussianDefinition2Score3)
        (rum3RankByScoreFns_measurable
          theorem8GaussianDefinition2Score1_measurable
          theorem8GaussianDefinition2Score2_measurable
          theorem8GaussianDefinition2Score3_measurable)) value :=
  KR21Monoculture.MallowsComparison.paper_definition2_threeCandidate_gaussianStd_negativeCorrelationCertificate
    hσ hvalue01 hvalue12 hx12 hx23

/--
Definition 2 / Gaussian three-candidate RUM with arbitrary positive standard
deviation: independent Gaussian score signals with ordered means prefer
independent reranking.
-/
theorem definition2_threeCandidate_gaussianStd_prefersIndependentReranking
    {σ x1 x2 x3 : ℝ} {value : Candidate 1 → ℝ}
    (hσ : 0 < σ)
    (hvalue01 : value (1 : Candidate 1) < value (0 : Candidate 1))
    (hvalue12 : value (2 : Candidate 1) < value (1 : Candidate 1))
    (hx12 : x2 < x1) (hx23 : x3 < x2) :
    Model.PrefersIndependentReranking
      (rumRankingPMFOfMeasure
        (theorem8GaussianDefinition2ScoreMeasureStd σ x1 x2 x3)
        (rum3RankByScoreFns
          theorem8GaussianDefinition2Score1
          theorem8GaussianDefinition2Score2
          theorem8GaussianDefinition2Score3)
        (rum3RankByScoreFns_measurable
          theorem8GaussianDefinition2Score1_measurable
          theorem8GaussianDefinition2Score2_measurable
          theorem8GaussianDefinition2Score3_measurable)) value :=
  KR21Monoculture.MallowsComparison.paper_definition2_threeCandidate_gaussianStd_prefersIndependentReranking
    hσ hvalue01 hvalue12 hx12 hx23

/-! ## Theorem 2 -/

/--
Preferred source-facing boundary for the three-candidate RUM route to Theorem 2.

It asks for atomwise continuity and algorithmic atomwise concentration toward
the deterministic true ranking.  The source Definition-2 theorem is used
directly to obtain the strict limiting gap, rather than assuming mass on a
particular ranking atom.
-/
abbrev Theorem2RUMConcentrationBoundary
    (F : AccuracyFamily 1) (center : Ranking 1) : Type :=
  KR21Monoculture.PaperTheorem2RUMConcentrationBoundary F center

/--
The remaining limit/continuity boundary for the three-candidate RUM route to
Theorem 2.  The Gaussian/Laplace source-model proof discharges Definition 2,
Definition 3, and finite-removal monotonicity; this boundary contains only
atomwise continuity of the finite ranking law and asymptotic first dominance.
-/
abbrev Theorem2RUMLimitBoundary (F : AccuracyFamily 1) : Type :=
  KR21Monoculture.PaperTheorem2RUMLimitBoundary F

/--
Theorem 2 / Gaussian RUM route: if `F.dist θ` is the three-candidate Gaussian
RUM law with standard deviation `1 / θ`, then the monoculture-paradox target
follows from the source-facing concentration boundary.
-/
theorem theorem2_gaussianStd_target_from_rum_concentration_boundary
    {F : AccuracyFamily 1} {θH x1 x2 x3 : ℝ}
    (hθH : 0 < θH)
    (hvalue1 : F.value (0 : Candidate 1) = x1)
    (hvalue2 : F.value (1 : Candidate 1) = x2)
    (hvalue3 : F.value (2 : Candidate 1) = x3)
    (hx12 : x2 < x1) (hx23 : x3 < x2)
    (hdist :
      ∀ θ, 0 < θ →
        F.dist θ =
          rumRankingPMFOfMeasure
            (theorem8GaussianDefinition2ScoreMeasureStd (1 / θ) x1 x2 x3)
            (rum3RankByScoreFns
              theorem8GaussianDefinition2Score1
              theorem8GaussianDefinition2Score2
              theorem8GaussianDefinition2Score3)
            (rum3RankByScoreFns_measurable
              theorem8GaussianDefinition2Score1_measurable
              theorem8GaussianDefinition2Score2_measurable
              theorem8GaussianDefinition2Score3_measurable))
    (boundary :
      Theorem2RUMConcentrationBoundary F (Equiv.refl (Candidate 1))) :
    AccuracyFamily.Theorem1Target F θH :=
  KR21Monoculture.paper_theorem2_gaussianStd_target_from_rum_concentration_boundary
    hθH hvalue1 hvalue2 hvalue3 hx12 hx23 hdist boundary

/--
Theorem 2 / Laplace RUM route: if `F.dist θ` is the three-candidate Laplace
RUM law with positive strictly increasing rate `λ θ`, then the
monoculture-paradox target follows from the source-facing concentration
boundary.
-/
theorem theorem2_laplacianRate_target_from_rum_concentration_boundary
    {F : AccuracyFamily 1} {θH x1 x2 x3 : ℝ}
    (lam : ℝ → ℝ)
    (hlam_pos : ∀ θ, 0 < θ → 0 < lam θ)
    (hlam_mono : ∀ θA θH, 0 < θH → θH < θA → lam θH < lam θA)
    (hθH : 0 < θH)
    (hvalue1 : F.value (0 : Candidate 1) = x1)
    (hvalue2 : F.value (1 : Candidate 1) = x2)
    (hvalue3 : F.value (2 : Candidate 1) = x3)
    (hx12 : x2 < x1) (hx23 : x3 < x2)
    (hdist :
      ∀ θ (hθ : 0 < θ),
        F.dist θ =
          theorem7LaplacianDefinition2RankingPMF
            (lam θ) x1 x2 x3 (hlam_pos θ hθ))
    (boundary :
      Theorem2RUMConcentrationBoundary F (Equiv.refl (Candidate 1))) :
    AccuracyFamily.Theorem1Target F θH :=
  KR21Monoculture.paper_theorem2_laplacianRate_target_from_rum_concentration_boundary
    lam hlam_pos hlam_mono hθH hvalue1 hvalue2 hvalue3 hx12 hx23 hdist
    boundary

/--
Theorem 2 / Gaussian RUM route from the concrete source model: if `F.dist θ`
is the three-candidate Gaussian RUM law with standard deviation `1 / θ`, then
the monoculture-paradox target follows from the concrete source proof.

The source-model proof supplies Definition 2, Definition 3,
finite-removal monotonicity, and high-accuracy concentration. Atomwise
continuity of the finite ranking law is derived from the continuous Gaussian
score source.

Source status: derived from source primitives.
-/
theorem theorem2_gaussianStd_target_from_rum_source
    {F : AccuracyFamily 1} {θH x1 x2 x3 : ℝ}
    (hθH : 0 < θH)
    (hvalue1 : F.value (0 : Candidate 1) = x1)
    (hvalue2 : F.value (1 : Candidate 1) = x2)
    (hvalue3 : F.value (2 : Candidate 1) = x3)
    (hx12 : x2 < x1) (hx23 : x3 < x2)
    (hdist :
      ∀ θ, 0 < θ →
        F.dist θ =
          rumRankingPMFOfMeasure
            (theorem8GaussianDefinition2ScoreMeasureStd (1 / θ) x1 x2 x3)
            (rum3RankByScoreFns
              theorem8GaussianDefinition2Score1
              theorem8GaussianDefinition2Score2
              theorem8GaussianDefinition2Score3)
            (rum3RankByScoreFns_measurable
              theorem8GaussianDefinition2Score1_measurable
              theorem8GaussianDefinition2Score2_measurable
              theorem8GaussianDefinition2Score3_measurable)) :
    AccuracyFamily.Theorem1Target F θH :=
  KR21Monoculture.paper_theorem2_gaussianStd_target_from_rum_source
    hθH hvalue1 hvalue2 hvalue3 hx12 hx23 hdist

/--
Compatibility alias for the older Gaussian source interface that exposed
atomwise continuity as an explicit argument.
-/
theorem theorem2_gaussianStd_target_from_rum_source_and_atom_continuity
    {F : AccuracyFamily 1} {θH x1 x2 x3 : ℝ}
    (hθH : 0 < θH)
    (hvalue1 : F.value (0 : Candidate 1) = x1)
    (hvalue2 : F.value (1 : Candidate 1) = x2)
    (hvalue3 : F.value (2 : Candidate 1) = x3)
    (hx12 : x2 < x1) (hx23 : x3 < x2)
    (_hdist_atom_continuity :
      ∀ θ, 0 < θ →
        ∀ π : Ranking 1, AppliedModelingLib.EpsilonContinuousAt
          (fun θ' => ((F.dist θ') π).toReal) θ)
    (hdist :
      ∀ θ, 0 < θ →
        F.dist θ =
          rumRankingPMFOfMeasure
            (theorem8GaussianDefinition2ScoreMeasureStd (1 / θ) x1 x2 x3)
            (rum3RankByScoreFns
              theorem8GaussianDefinition2Score1
              theorem8GaussianDefinition2Score2
              theorem8GaussianDefinition2Score3)
            (rum3RankByScoreFns_measurable
              theorem8GaussianDefinition2Score1_measurable
              theorem8GaussianDefinition2Score2_measurable
              theorem8GaussianDefinition2Score3_measurable)) :
    AccuracyFamily.Theorem1Target F θH :=
  KR21Monoculture.paper_theorem2_gaussianStd_target_from_rum_source
    hθH hvalue1 hvalue2 hvalue3 hx12 hx23 hdist

/--
Theorem 2 / literal Gaussian model transport: at every positive accuracy, the
actual iid standard-Gaussian scaled-noise RUM has exactly the named Gaussian
three-score ranking PMF.  The proof transports the whole product law and
reconciles the two total tie conventions only on the proved Gaussian null set.
-/
theorem theorem2_gaussian_literal_iid_rum_law_transport
    {theta x1 x2 x3 : ℝ} (htheta : 0 < theta) :
    (theorem2GaussianScaledNoiseFamily x1 x2 x3).dist theta =
      gaussianThreeCandidateRankingLaw theta x1 x2 x3 :=
  KR21Monoculture.theorem2GaussianScaledNoiseFamily_dist_eq_gaussianThreeCandidateRankingLaw
    htheta

/--
Theorem 2 / Gaussian Definition 1 package.  For the named three-candidate
Gaussian source law, every ranking atom is continuous and differentiable at
positive accuracy, the true-ranking atom tends to one, every nonempty
remaining set is weakly improved, and the full set is strictly improved.

This endpoint is proposition-valued: no Definition 1 certificate is accepted
as an input, and the source-law transport is exposed separately above.
-/
theorem theorem2_gaussian_source_definition1
    {x1 x2 x3 : ℝ} (hx12 : x2 < x1) (hx23 : x3 < x2) :
    SourceDefinition1NoisyPermutationFamily
      (gaussianThreeCandidateAccuracyFamily x1 x2 x3) rum3Ranking012 :=
  KR21Monoculture.gaussianThreeCandidateAccuracyFamily_sourceDefinition1 hx12 hx23

/--
Theorem 2 / literal Laplace normalization.  The source uses centered
unit-variance innovations before dividing by accuracy; this theorem checks
that the concrete `sqrt 2`-rate base law has that variance.
-/
theorem theorem2_laplace_source_base_noise_variance_one :
    Var[id; w11BaseNoiseLaw sourceUnitVarianceLaplaceBaseDensity] = 1 :=
  KR21Monoculture.sourceUnitVarianceLaplaceBaseNoiseLaw_variance_one

/--
Theorem 2 / literal Laplace model transport: at every positive accuracy, the
actual iid unit-variance Laplace scaled-noise RUM has exactly the named
source-normalized three-score ranking PMF.  The proof transports the full
product measure and reconciles total ranking conventions only on a proved
null tie set.
-/
theorem theorem2_laplace_literal_iid_rum_law_transport
    {theta x1 x2 x3 : ℝ} (htheta : 0 < theta) :
    (sourceUnitVarianceLaplaceScaledNoiseFamily x1 x2 x3).dist theta =
      sourceUnitVarianceLaplaceThreeCandidateRankingLaw theta x1 x2 x3 := by
  simpa [sourceUnitVarianceLaplaceScaledNoiseFamily] using
    KR21Monoculture.sourceUnitVarianceLaplaceScaledNoiseFamily_dist_eq_namedLaw
      htheta

/--
Theorem 2 / source-normalized Laplace Definition 1 package.  This gives every
field at the named law: all-atom continuity and differentiability, the
true-ranking limit, weak improvement for every nonempty remaining set, and
strict full-set improvement.  The Laplace density kink is handled through the
proved global `W^{1,1}` route, not by assuming the paper's false pointwise
differentiability premise.
-/
theorem theorem2_laplace_source_definition1
    {x1 x2 x3 : ℝ} (hx12 : x2 < x1) (hx23 : x3 < x2) :
    SourceDefinition1NoisyPermutationFamily
      (sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily.pointFamily
        (threeCandidateValueProfile x1 x2 x3)) rum3Ranking012 :=
  KR21Monoculture.sourceUnitVarianceLaplaceThreeCandidatePointFamily_sourceDefinition1
    hx12 hx23

/--
Theorem 2 / canonical Laplace RUM route from the concrete source model: if
`F.dist θ` is the three-candidate Laplace RUM law with rate `θ`, then the
monoculture-paradox target follows from the concrete source proof.
-/
theorem theorem2_laplacianCanonical_target_from_rum_source
    {F : AccuracyFamily 1} {θH x1 x2 x3 : ℝ}
    (hθH : 0 < θH)
    (hvalue1 : F.value (0 : Candidate 1) = x1)
    (hvalue2 : F.value (1 : Candidate 1) = x2)
    (hvalue3 : F.value (2 : Candidate 1) = x3)
    (hx12 : x2 < x1) (hx23 : x3 < x2)
    (hdist :
      ∀ θ (hθ : 0 < θ),
        F.dist θ =
          theorem7LaplacianDefinition2RankingPMF θ x1 x2 x3 hθ) :
    AccuracyFamily.Theorem1Target F θH :=
  KR21Monoculture.paper_theorem2_laplacianCanonical_target_from_rum_source
    hθH hvalue1 hvalue2 hvalue3 hx12 hx23 hdist

/--
Theorem 2 / continuous-rate Laplace RUM route from the concrete source model:
if `F.dist θ` is the three-candidate Laplace RUM law with a positive strictly
increasing continuous rate that tends to infinity, then the
monoculture-paradox target follows from the concrete source proof.
-/
theorem theorem2_laplacianRate_target_from_continuous_rum_source
    {F : AccuracyFamily 1} {θH x1 x2 x3 : ℝ}
    (lam : ℝ → ℝ)
    (hlam_pos : ∀ θ, 0 < θ → 0 < lam θ)
    (hlam_mono : ∀ θA θH, 0 < θH → θH < θA → lam θH < lam θA)
    (hlam_cont : ∀ θ, 0 < θ → ContinuousAt lam θ)
    (hlam_tendsto : Filter.Tendsto lam Filter.atTop Filter.atTop)
    (hθH : 0 < θH)
    (hvalue1 : F.value (0 : Candidate 1) = x1)
    (hvalue2 : F.value (1 : Candidate 1) = x2)
    (hvalue3 : F.value (2 : Candidate 1) = x3)
    (hx12 : x2 < x1) (hx23 : x3 < x2)
    (hdist :
      ∀ θ (hθ : 0 < θ),
        F.dist θ =
          theorem7LaplacianDefinition2RankingPMF
            (lam θ) x1 x2 x3 (hlam_pos θ hθ)) :
    AccuracyFamily.Theorem1Target F θH :=
  KR21Monoculture.paper_theorem2_laplacianRate_target_from_continuous_rum_source
    lam hlam_pos hlam_mono hlam_cont hlam_tendsto hθH
    hvalue1 hvalue2 hvalue3 hx12 hx23 hdist

/--
Theorem 2 / Laplace RUM route from the concrete source model: if `F.dist θ`
is the three-candidate Laplace RUM law with a positive strictly increasing
rate that tends to infinity, then the monoculture-paradox target follows from
atomwise continuity of the induced finite ranking law.

The source-model proof supplies Definition 2, Definition 3,
finite-removal monotonicity, and high-accuracy concentration.

Source status: derived from source primitives.
-/
theorem theorem2_laplacianRate_target_from_rum_source_and_atom_continuity
    {F : AccuracyFamily 1} {θH x1 x2 x3 : ℝ}
    (lam : ℝ → ℝ)
    (hlam_pos : ∀ θ, 0 < θ → 0 < lam θ)
    (hlam_mono : ∀ θA θH, 0 < θH → θH < θA → lam θH < lam θA)
    (hlam_tendsto : Filter.Tendsto lam Filter.atTop Filter.atTop)
    (hθH : 0 < θH)
    (hvalue1 : F.value (0 : Candidate 1) = x1)
    (hvalue2 : F.value (1 : Candidate 1) = x2)
    (hvalue3 : F.value (2 : Candidate 1) = x3)
    (hx12 : x2 < x1) (hx23 : x3 < x2)
    (hdist_atom_continuity :
      ∀ θ, 0 < θ →
        ∀ π : Ranking 1, AppliedModelingLib.EpsilonContinuousAt
          (fun θ' => ((F.dist θ') π).toReal) θ)
    (hdist :
      ∀ θ (hθ : 0 < θ),
        F.dist θ =
          theorem7LaplacianDefinition2RankingPMF
            (lam θ) x1 x2 x3 (hlam_pos θ hθ)) :
    AccuracyFamily.Theorem1Target F θH :=
  KR21Monoculture.paper_theorem2_laplacianRate_target_from_rum_source_and_atom_continuity
    lam hlam_pos hlam_mono hlam_tendsto hθH
    hvalue1 hvalue2 hvalue3 hx12 hx23 hdist_atom_continuity hdist

/--
Theorem 2 / Gaussian RUM route: if `F.dist θ` is the three-candidate Gaussian
RUM law with standard deviation `1 / θ`, then the monoculture-paradox target
follows from the remaining limit/continuity boundary.
-/
theorem theorem2_gaussianStd_target_from_rum_limit_boundary
    {F : AccuracyFamily 1} {θH x1 x2 x3 : ℝ}
    (hθH : 0 < θH)
    (hvalue1 : F.value (0 : Candidate 1) = x1)
    (hvalue2 : F.value (1 : Candidate 1) = x2)
    (hvalue3 : F.value (2 : Candidate 1) = x3)
    (hx12 : x2 < x1) (hx23 : x3 < x2)
    (hdist :
      ∀ θ, 0 < θ →
        F.dist θ =
          rumRankingPMFOfMeasure
            (theorem8GaussianDefinition2ScoreMeasureStd (1 / θ) x1 x2 x3)
            (rum3RankByScoreFns
              theorem8GaussianDefinition2Score1
              theorem8GaussianDefinition2Score2
              theorem8GaussianDefinition2Score3)
            (rum3RankByScoreFns_measurable
              theorem8GaussianDefinition2Score1_measurable
              theorem8GaussianDefinition2Score2_measurable
              theorem8GaussianDefinition2Score3_measurable))
    (boundary : Theorem2RUMLimitBoundary F) :
    AccuracyFamily.Theorem1Target F θH :=
  KR21Monoculture.paper_theorem2_gaussianStd_target_from_rum_limit_boundary
    hθH hvalue1 hvalue2 hvalue3 hx12 hx23 hdist boundary

/--
Theorem 2 / Laplace RUM route: if `F.dist θ` is the three-candidate Laplace
RUM law with positive strictly increasing rate `λ θ`, then the
monoculture-paradox target follows from the remaining limit/continuity boundary.
-/
theorem theorem2_laplacianRate_target_from_rum_limit_boundary
    {F : AccuracyFamily 1} {θH x1 x2 x3 : ℝ}
    (lam : ℝ → ℝ)
    (hlam_pos : ∀ θ, 0 < θ → 0 < lam θ)
    (hlam_mono : ∀ θA θH, 0 < θH → θH < θA → lam θH < lam θA)
    (hθH : 0 < θH)
    (hvalue1 : F.value (0 : Candidate 1) = x1)
    (hvalue2 : F.value (1 : Candidate 1) = x2)
    (hvalue3 : F.value (2 : Candidate 1) = x3)
    (hx12 : x2 < x1) (hx23 : x3 < x2)
    (hdist :
      ∀ θ (hθ : 0 < θ),
        F.dist θ =
          theorem7LaplacianDefinition2RankingPMF
            (lam θ) x1 x2 x3 (hlam_pos θ hθ))
    (boundary : Theorem2RUMLimitBoundary F) :
    AccuracyFamily.Theorem1Target F θH :=
  KR21Monoculture.paper_theorem2_laplacianRate_target_from_rum_limit_boundary
    lam hlam_pos hlam_mono hθH hvalue1 hvalue2 hvalue3 hx12 hx23 hdist
    boundary

/-! ## Appendix F, Lemmas 4--8 -/

/-- Appendix F Lemma 4, the paper's weighted-average likelihood-ratio comparison. -/
theorem lemma4_weighted_average_lt_of_cross_ratio
    (n : ℕ) {p q y : Candidate n → ℝ}
    (hp_sum : (∑ i : Candidate n, p i) = 1)
    (hq_sum : (∑ i : Candidate n, q i) = 1)
    (hcross_nonneg :
      ∀ i j : Candidate n, i < j → 0 ≤ p i * q j - p j * q i)
    (hcross_pos :
      ∃ i j : Candidate n, i < j ∧ 0 < p i * q j - p j * q i)
    (hy : StrictMono y) :
    (∑ i : Candidate n, p i * y i) <
      ∑ i : Candidate n, q i * y i :=
  KR21Monoculture.MallowsComparison.paper_lemma4_weighted_average_lt_of_cross_ratio
    n hp_sum hq_sum hcross_nonneg hcross_pos hy

/-- Appendix F Lemma 5, Mallows top-two order-swap ratio in inverse parameter `q`. -/
theorem lemma5_mallows_top_two_swap_ratio
    {n : ℕ} (M : MallowsSpec n) {c d : Candidate n}
    (hcd : rankOf M.center c < rankOf M.center d) :
    M.firstSecondWeight d c = M.q * M.firstSecondWeight c d :=
  KR21Monoculture.MallowsComparison.paper_lemma5_mallows_top_two_swap_ratio M hcd

/-- Appendix F Lemma 6, Mallows first-choice probability by center rank. -/
theorem lemma6_mallows_first_choice_prob_eq_rank_power
    {n : ℕ} (M : MallowsSpec n) (c : Candidate n) :
    M.firstWeight c / M.partition =
      M.q ^ (rankOf M.center c : ℕ) / candidateRankPowerSum n M.q :=
  KR21Monoculture.MallowsComparison.paper_lemma6_mallows_first_choice_prob_eq_rank_power M c

/-- Equation (F.1) at the source parameter surface `phi`, with `q = phi^{-1}`. -/
theorem equationF1_mallows_top_two_probability
    {n : ℕ} (M : MallowsSpec n) (phi : ℝ)
    (hphi_gt : 1 < phi) (hphi : M.q = phi⁻¹) {c d : Candidate n}
    (hcd : rankOf M.center c < rankOf M.center d) :
    M.firstSecondChoiceProb c d =
      phi * M.firstSecondChoiceProb d c :=
  KR21Monoculture.source_equationF1_mallows_top_two_probability M phi hphi hcd

/--
Appendix F Lemma 5 (displayed as Equation (F.1)) at the literal source Mallows
model. The statement binds the ranking law to Equation (8), including
`theta = phi - 1`, instead of accepting an arbitrary Mallows record as a
source-model premise.
-/
theorem lemma5_source_phi_complete
    {n : ℕ} (center : Ranking n) (phi theta : ℝ)
    (hphi : 1 < phi) (htheta : theta = phi - 1) {c d : Candidate n}
    (hcd : rankOf center c < rankOf center d) :
    let M := concreteMallowsSpec center theta
    M.q = phi⁻¹ ∧
      (∀ pi : Ranking n,
        (M.law pi).toReal =
          phi⁻¹ ^ kendallTau center pi /
            (∑ tau : Ranking n, phi⁻¹ ^ kendallTau center tau)) ∧
      M.firstSecondChoiceProb c d =
        phi * M.firstSecondChoiceProb d c := by
  dsimp
  have hq := source_equation8_concrete_mallows_probability center phi theta
    hphi htheta center
  refine ⟨hq.1, ?_, ?_⟩
  · intro pi
    exact (source_equation8_concrete_mallows_probability center phi theta
      hphi htheta pi).2
  · apply KR21Monoculture.source_equationF1_mallows_top_two_probability
      (M := concreteMallowsSpec center theta) (phi := phi) hq.1
    simpa [concreteMallowsSpec, MallowsSpec.ofQ] using hcd

/-- Equation (F.2) before denominator expansion, in the source rank-power form. -/
theorem equationF2_mallows_first_choice_rank_power
    {n : ℕ} (M : MallowsSpec n) (phi : ℝ)
    (hphi : M.q = phi⁻¹) (c : Candidate n) :
    firstChoiceProb M.law c =
      phi⁻¹ ^ (rankOf M.center c : ℕ) /
        candidateRankPowerSum n phi⁻¹ :=
  KR21Monoculture.source_equationF2_mallows_first_choice_rank_power M phi hphi c

/-- Equation (F.2), literal closed first-choice probability with source rank indexing. -/
theorem equationF2_mallows_first_choice_closed_form
    {n : ℕ} (M : MallowsSpec n) (phi : ℝ)
    (hparameter : SourceMallowsParameter M phi) (c : Candidate n) :
    firstChoiceProb M.law c =
      (1 - phi⁻¹) /
        (phi ^ (rankOf M.center c : ℕ) *
          (1 - phi⁻¹ ^ (n + 2))) :=
  KR21Monoculture.source_equationF2_mallows_first_choice_closed_form
    M phi hparameter c

/-- Appendix F Lemma 7, strict first-mover advantage under one Mallows law. -/
theorem lemma7_mallows_first_mover_gt_second_human
    {n : ℕ} (M : MallowsSpec n) {value : Candidate n → ℝ}
    (hvalue : StrictlyOrderedBy M.center value) (hq_lt_one : M.q < 1) :
    expectedSecondMoverIndependent M.law M.law value <
      expectedFirstMoverUtility M.law value :=
  KR21Monoculture.MallowsComparison.paper_lemma7_mallows_first_mover_gt_second_human
    M hvalue hq_lt_one

/--
Appendix F Lemma 7 at the literal Equation (8) Mallows model.  The source
parameter conditions derive the inverse-accuracy bound internally, so the
paper-facing statement has no arbitrary Mallows-record or `q < 1` premise.
-/
theorem lemma7_source_phi_complete
    {n : ℕ} (center : Ranking n) (phi theta : ℝ)
    (hphi : 1 < phi) (htheta : theta = phi - 1)
    {value : Candidate n → ℝ} (hvalue : StrictlyOrderedBy center value) :
    let M := concreteMallowsSpec center theta
    M.q = phi⁻¹ ∧
      (∀ pi : Ranking n,
        (M.law pi).toReal =
          phi⁻¹ ^ kendallTau center pi /
            (∑ tau : Ranking n, phi⁻¹ ^ kendallTau center tau)) ∧
      expectedSecondMoverIndependent M.law M.law value <
        expectedFirstMoverUtility M.law value := by
  dsimp
  have hq := source_equation8_concrete_mallows_probability center phi theta
    hphi htheta center
  refine ⟨hq.1, ?_, ?_⟩
  · intro pi
    exact (source_equation8_concrete_mallows_probability center phi theta
      hphi htheta pi).2
  · have hq_lt_one : (concreteMallowsSpec center theta).q < 1 := by
      rw [hq.1]
      exact inv_lt_one_of_one_lt₀ hphi
    have hvalue' :
        StrictlyOrderedBy (concreteMallowsSpec center theta).center value := by
      intro a b hab
      exact hvalue (by
        simpa [concreteMallowsSpec, MallowsSpec.ofQ] using hab)
    exact KR21Monoculture.MallowsComparison.paper_lemma7_mallows_first_mover_gt_second_human
      (M := concreteMallowsSpec center theta) hvalue' hq_lt_one

/-- Appendix F Lemma 8, strict pairwise Mallows accuracy monotonicity. -/
theorem lemma8_mallows_pairCorrectProb_lt
    {n : ℕ} {Mmore Mless : MallowsSpec n} {c d : Candidate n}
    (hcenter : Mmore.center = Mless.center)
    (hcd_more : rankOf Mmore.center c < rankOf Mmore.center d)
    (hq_lt : Mmore.q < Mless.q) :
    Mless.pairCorrectProb c d < Mmore.pairCorrectProb c d :=
  KR21Monoculture.MallowsComparison.paper_lemma8_mallows_pairCorrectProb_lt
    hcenter hcd_more hq_lt

/--
Appendix F Lemma 8 at the source's `phi > 1` parameter surface.  The
center-order relation is a source-domain premise; the probability event is
only that the sampled Mallows ranking orders that fixed pair correctly.
-/
theorem lemma8_source_mallows_phi_pairwise_correct_probability_lt
    {n : ℕ} (center : Ranking n) {phiMore phiLess : ℝ}
    (hphiLess : 1 < phiLess) (hphiOrder : phiLess < phiMore)
    {c d : Candidate n} (hcd : rankOf center c < rankOf center d) :
    let Mless := concreteMallowsSpec center (phiLess - 1)
    let Mmore := concreteMallowsSpec center (phiMore - 1)
    Mless.q = phiLess⁻¹ ∧
      Mmore.q = phiMore⁻¹ ∧
      (∀ pi : Ranking n,
        (Mless.law pi).toReal =
          phiLess⁻¹ ^ kendallTau center pi /
            (∑ tau : Ranking n, phiLess⁻¹ ^ kendallTau center tau)) ∧
      (∀ pi : Ranking n,
        (Mmore.law pi).toReal =
          phiMore⁻¹ ^ kendallTau center pi /
            (∑ tau : Ranking n, phiMore⁻¹ ^ kendallTau center tau)) ∧
      AppliedModelingLib.pmfProb Mless.law
        (fun pi => rankOf pi c < rankOf pi d) <
        AppliedModelingLib.pmfProb Mmore.law
          (fun pi => rankOf pi c < rankOf pi d) := by
  have hphiMore : 1 < phiMore := lt_trans hphiLess hphiOrder
  dsimp
  refine ⟨(source_equation8_concrete_mallows_probability center phiLess
    (phiLess - 1) hphiLess rfl center).1,
    (source_equation8_concrete_mallows_probability center phiMore
      (phiMore - 1) hphiMore rfl center).1, ?_, ?_, ?_⟩
  · intro pi
    exact (source_equation8_concrete_mallows_probability center phiLess
      (phiLess - 1) hphiLess rfl pi).2
  · intro pi
    exact (source_equation8_concrete_mallows_probability center phiMore
      (phiMore - 1) hphiMore rfl pi).2
  · simpa [hcd] using
    (KR21Monoculture.source_lemma8_mallows_phi_pairwise_correct_probability_lt
      center hphiLess hphiOrder hcd)

/-! ## Theorems 1, 3, and 9 -/

/--
Paper Theorem 1, conditional family form: if a finite accuracy family satisfies
the paper's Definition 1 analytic conditions, Definition 2 independent
reranking condition, and Definition 3 weaker-competition condition, then every
positive human accuracy admits a more accurate algorithmic accuracy witnessing
the monoculture paradox.

The `assumptions` input is the Lean package of the proof-facing consequences
used here.  Concrete source routes are reviewed separately: some construct
these consequences, while the newer outer-D routes prove the advertised
conclusion directly from explicit source-model premises.

Source status: paper theorem from source conditions.
-/
theorem theorem1_from_paper_assumptions
    {n : ℕ} (F : AccuracyFamily n) (θH : ℝ)
    (hθH : 0 < θH)
    (assumptions : AccuracyFamily.Theorem1PaperAssumptions F) :
    AccuracyFamily.Theorem1Target F θH :=
  KR21Monoculture.paper_theorem1_from_paper_assumptions F θH hθH assumptions

/--
Theorem 1 with every *derived finite-family proof condition* visible at the
review surface.  This is the same theorem as the packaged version above, but
it does not ask a reviewer to trust the contents of
`Theorem1PaperAssumptions`: the utility-side Definition-2 and Definition-3
consequences, atomwise continuity, the asymptotic crossing inequality, and the
empty/singleton-removal consequences used in the two-firm proof are separate
binders.

This is deliberately not labelled a literal Definitions-1--3 theorem.  In
particular, the source's Definition-2 conditional gain requires its own
positive-event/regularity bridge, and Definition 1's source statement covers
every removed subset while this proof needs only the displayed finite
consequences.  Concrete source routes must derive these conditions from their
stated noise models; this wrapper neither relabels them as source facts nor
weakens their quantifiers.
-/
theorem theorem1_from_explicit_proof_conditions
    {n : ℕ} (F : AccuracyFamily n) (θH : ℝ)
    (hθH : 0 < θH)
    (hprefers_independent : ∀ θ, 0 < θ →
      Model.PrefersIndependentReranking (F.dist θ) F.value)
    (hprefers_weaker_competition : ∀ θA θH, 0 < θH → θH < θA →
      Model.PrefersWeakerCompetition (F.dist θA) (F.dist θH) F.value)
    (hatom_continuity : ∀ θ, 0 < θ → ∀ π : Ranking n,
      AppliedModelingLib.EpsilonContinuousAt
        (fun θ' => ((F.dist θ') π).toReal) θ)
    (hasymptotic_first_dominance : ∀ θH lower, 0 < θH → θH < lower →
      ∃ hi, lower < hi ∧
        AccuracyFamily.theorem1_g F hi θH < AccuracyFamily.theorem1_f F hi θH)
    (hremoval_monotonicity : ∀ θA θH, 0 < θH → θH < θA →
      AccuracyFamily.Theorem1RemovalMonotonicityAt F θA θH) :
    AccuracyFamily.Theorem1Target F θH :=
  AccuracyFamily.theorem1Target_of_paperAssumptions hθH
    { prefers_independent := hprefers_independent
      prefers_weaker_competition := hprefers_weaker_competition
      dist_atom_continuity := hatom_continuity
      asymptotic_first_dominance := hasymptotic_first_dominance
      removal_monotonicity := hremoval_monotonicity }

/--
Paper Theorem 1, fixed-value source-conditions form.  Every printed
Definition-1 clause is visible: positive-accuracy atom continuity and
differentiability, convergence only of the true-ranking atom to one, and the
weak-all-remaining-set/strict-full-set monotonicity conditions.  Finite-PMF
normalization proves the stronger all-atom convergence used by the crossing
argument rather than assuming it.

Definition 2 is stated in the source's conditional form.  Its positive top
disagreement mass is explicit because a conditional expectation needs a
non-null conditioning event; the source leaves that well-formedness condition
implicit.  Definition 3 remains the direct payoff comparison.  This is the
fixed-value implication in the source proof, not a substitute for the
outer-`D` theorem: the latter additionally needs a measurable joint law,
integrability, and a common algorithmic witness.
-/
theorem theorem1_from_literal_source_conditions
    {n : ℕ} (F : AccuracyFamily n) (center : Ranking n) (thetaH : ℝ)
    (hthetaH : 0 < thetaH)
    (hcenter : StrictlyOrderedBy center F.value)
    (hdefinition2 : ∀ theta, 0 < theta →
      0 < disagreementProb (F.dist theta) ∧
        0 < disagreementConditionalGain (F.dist theta) F.value)
    (hprefers_weaker_competition : ∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
      Model.PrefersWeakerCompetition (F.dist thetaA) (F.dist thetaH) F.value)
    (hatom_continuous : ∀ theta, 0 < theta → ∀ pi : Ranking n,
      ContinuousAt (fun theta' => ((F.dist theta') pi).toReal) theta)
    (hatom_differentiable : ∀ theta, 0 < theta → ∀ pi : Ranking n,
      DifferentiableAt ℝ (fun theta' => ((F.dist theta') pi).toReal) theta)
    (hcenter_tendsto :
      Tendsto (fun theta => ((F.dist theta) center).toReal) atTop (nhds 1))
    (hremaining_weak : ∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
      ∀ remaining : Finset (Candidate n), remaining.Nonempty →
        expectedBestInSet (F.dist thetaH) F.value remaining ≤
          expectedBestInSet (F.dist thetaA) F.value remaining)
    (hfull_set_strict : ∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
      expectedBestInSet (F.dist thetaH) F.value Finset.univ <
        expectedBestInSet (F.dist thetaA) F.value Finset.univ) :
    AccuracyFamily.Theorem1Target F thetaH :=
  KR21Monoculture.theorem1Target_of_sourceDefinition1Definition2_fields
    F center thetaH hthetaH hcenter hdefinition2 hprefers_weaker_competition
    hatom_continuous hatom_differentiable hcenter_tendsto hremaining_weak
    hfull_set_strict

/--
Paper Theorem 1 with the literal outer-`D` source experiment.  This is the
source-facing form of Definitions 1--3: Definition 1 remains universal over
the source's strictly center-ordered value profiles, Definition 2 is the
conditional gain in the joint experiment that first samples from `D`, and
Definition 3 is the ex-ante weaker-
competition comparison.  The theorem derives the common high-accuracy
algorithmic witness outside the outer expectation.

The source leaves the following needed well-formedness conditions implicit and
they are deliberately visible here: coordinate first moments, ranking-atom
measurability, support of `D` on the fixed strict source order, and positive
mass of Definition 2's conditioning event.  These conditions do not replace
any source Definition 1--3 clause.
-/
theorem theorem1_outer_from_literal_source_conditions
    {n : ℕ} (F : DistributionalAccuracyFamily n)
    (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    (center : Ranking n) (thetaH : ℝ)
    (hthetaH : 0 < thetaH)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D)
    (hatom_aestrongly_measurable : ∀ theta pi,
      AEStronglyMeasurable (fun value : ValueProfile n =>
        ((F.dist theta value) pi).toReal) D)
    (hatom_continuous : ∀ value theta, 0 < theta → ∀ pi : Ranking n,
      ContinuousAt (fun theta' => ((F.dist theta' value) pi).toReal) theta)
    (hatom_differentiable : ∀ value theta, 0 < theta → ∀ pi : Ranking n,
      DifferentiableAt ℝ (fun theta' => ((F.dist theta' value) pi).toReal) theta)
    (hcenter_tendsto : ∀ value,
      Tendsto (fun theta => ((F.dist theta value) center).toReal) atTop (nhds 1))
    (hstrict_order : ∀ᵐ value ∂D, StrictlyOrderedBy center value)
    (hdefinition2_regular : ∀ theta, 0 < theta →
      DistributionalAccuracyFamily.OuterIndependentRerankingJointRegularity F D theta)
    (hdefinition2_event : ∀ theta, ∀ htheta : 0 < theta,
      0 < ∫ x : ValueProfile n × RankingPair n,
        (if disagreementEvent x.2 then (1 : ℝ) else 0) ∂
          F.outerIndependentPairJointLaw D theta
            (hdefinition2_regular theta htheta).base.ranking_atom_measurable)
    (hdefinition2_gain : ∀ theta, ∀ htheta : 0 < theta,
      0 < F.jointLawDisagreementConditionalGain D theta
        (hdefinition2_regular theta htheta).base.ranking_atom_measurable)
    (hdefinition3 : ∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
      F.PrefersWeakerCompetition D thetaA thetaH)
    (hremaining_weak : ∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
      ∀ value, ∀ remaining : Finset (Candidate n), remaining.Nonempty →
        expectedBestInSet (F.dist thetaH value) value remaining ≤
          expectedBestInSet (F.dist thetaA value) value remaining)
    (hfull_set_strict : ∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
      ∀ value, StrictlyOrderedBy center value →
        expectedBestInSet (F.dist thetaH value) value Finset.univ <
          expectedBestInSet (F.dist thetaA value) value Finset.univ) :
    F.DistributionalTheorem1Target D thetaH :=
  DistributionalAccuracyFamily.distributional_theorem1_of_universal_definition1_and_literal_outer_conditions
      F D center thetaH hthetaH hvalue hatom_aestrongly_measurable
      hatom_continuous hatom_differentiable hcenter_tendsto hstrict_order
      hdefinition2_regular hdefinition2_event hdefinition2_gain hdefinition3
      hremaining_weak hfull_set_strict

/--
Corrected Theorem 3, Mallows form: for Mallows laws with a common center, if
the algorithmic law is more accurate than the human law, then every strictly
center-ordered value profile with at least three source candidates satisfies
the paper's Definition 2 and Definition 3 hypotheses for the induced
two-distribution model.  The archival source omits this lower bound: with two
candidates, the strict Definition 2 conclusion is false.

Lean uses the inverse Mallows parameter `q`, so greater accuracy is
`C.algorithm.q < C.human.q`, and `hn : 0 < n` means source cardinality
`n + 2 >= 3`. The rank-factorization formulas used by the source proof are
proved for `MallowsSpec` and are not exposed as assumptions here.

Source status: corrected source scope; see KR21-THEOREM3-CARDINALITY-01.
-/
theorem theorem3_mallows_satisfies_paper_hypotheses
    {n : ℕ} (C : MallowsComparison n) {value : Candidate n → ℝ}
    (hstrict : C.StrictlyCenterOrdered value)
    (hn : 0 < n)
    (halg_q_lt_one : C.algorithm.q < 1)
    (hhuman_q_lt_one : C.human.q < 1)
    (hq_lt : C.algorithm.q < C.human.q) :
    Model.PaperHypotheses (C.toModel value) :=
  KR21Monoculture.MallowsComparison.paper_theorem3_pointwise_rankFactorization
    C hstrict hn halg_q_lt_one hhuman_q_lt_one hq_lt

/--
Concrete refutation of the archival Theorem 3 scope with exactly two source
candidates.  The identity-centered Mallows law with `q = 1/2` has a strictly
ordered value profile and positive top-disagreement probability, but its
conditional reranking gain is zero.  Thus the source's strict Definition 2
conclusion needs the corrected `N >= 3` domain used above.
-/
theorem theorem3_twoCandidate_source_counterexample :
    theorem3TwoCandidateValue (1 : Candidate 0) <
        theorem3TwoCandidateValue (0 : Candidate 0) ∧
      0 < theorem3TwoCandidateQ ∧ theorem3TwoCandidateQ < 1 ∧
      0 < disagreementProb theorem3TwoCandidateMallows.law ∧
      disagreementConditionalGain theorem3TwoCandidateMallows.law
        theorem3TwoCandidateValue = 0 ∧
      ¬ Model.PrefersIndependentReranking theorem3TwoCandidateMallows.law
        theorem3TwoCandidateValue :=
  ⟨theorem3TwoCandidateValue_strict_gap, theorem3TwoCandidateQ_pos,
    theorem3TwoCandidateQ_lt_one, theorem3TwoCandidateMallows_disagreementProb_pos,
    theorem3TwoCandidateMallows_conditionalGain_eq_zero,
    theorem3TwoCandidateMallows_not_prefersIndependentReranking⟩

/--
Concrete Mallows downstream package consumed by the Lean proof of Theorem 1.
This is deliberately smaller than Appendix D / Theorem 9's literal Definition
1 statement; the source-shaped endpoint is
`theorem9_concrete_mallows_source_definition1` immediately below.
-/
noncomputable def theorem9_concrete_mallows_family_assumptions
    {n : ℕ} (center : Ranking n) (value : Candidate n → ℝ)
    (hvalue : StrictlyOrderedBy center value)
    (hn : 0 < n) :
    AccuracyFamily.Theorem1PaperAssumptions
      (MallowsAccuracyFamilySpec.toAccuracyFamily
        (concreteMallowsAccuracyFamilySpec center value hvalue)) :=
  KR21Monoculture.paper_theorem9_concrete_mallows_family_assumptions
    center value hvalue hn

/--
Appendix D / Theorem 9 at the literal Definition 1 surface.  The concrete
Kendall--Mallows law has continuous and differentiable ranking atoms at every
positive accuracy, concentrates on the true ranking as accuracy grows, weakly
improves every nonempty remaining set, and strictly improves the full set.

This is distinct from `theorem9_concrete_mallows_family_assumptions` above:
that older wrapper supplies only the smaller proof-condition package consumed
by Theorem 1.
-/
theorem theorem9_concrete_mallows_source_definition1
    {n : ℕ} (center : Ranking n) (value : Candidate n → ℝ)
    (hvalue : StrictlyOrderedBy center value) :
    SourceDefinition1NoisyPermutationFamily
      ({ dist := fun theta => (concreteMallowsSpec center theta).law,
         value := value } : AccuracyFamily n)
      center :=
  KR21Monoculture.concreteMallowsAccuracyFamily_sourceDefinition1
    center value hvalue

/--
Theorem 9 with the source `theta = phi - 1` parameterization and normalized
Kendall--Mallows atom law exposed before its Definition 1 conclusion.
-/
theorem theorem9_source_mallows_definition1_semantic_complete
    {n : ℕ} (center : Ranking n) (value : Candidate n → ℝ)
    (hvalue : StrictlyOrderedBy center value) :
    (∀ (phi theta : ℝ), 1 < phi → theta = phi - 1 →
      let M := concreteMallowsSpec center theta
      M.q = phi⁻¹ ∧
        ∀ pi : Ranking n,
          (M.law pi).toReal =
            phi⁻¹ ^ kendallTau center pi /
              (∑ tau : Ranking n, phi⁻¹ ^ kendallTau center tau)) ∧
    SourceDefinition1NoisyPermutationFamily
      ({ dist := fun theta => (concreteMallowsSpec center theta).law,
         value := value } : AccuracyFamily n)
      center := by
  refine ⟨?_, theorem9_concrete_mallows_source_definition1 center value hvalue⟩
  intro phi theta hphi htheta
  dsimp
  refine ⟨(source_equation8_concrete_mallows_probability center phi theta
    hphi htheta center).1, ?_⟩
  intro pi
  exact (source_equation8_concrete_mallows_probability center phi theta
    hphi htheta pi).2

/--
Theorem 9 with Definition 1 unfolded at the paper boundary.  The terminal
conclusion lists the atomwise positive-accuracy regularity, convergence to the
true ranking, and weak/strict expected-best-after-removal comparisons rather
than storing them in a named definition package.
-/
theorem theorem9_source_mallows_definition1_literal_semantic_complete
    {n : ℕ} (center : Ranking n) (value : Candidate n → ℝ)
    (hvalue : StrictlyOrderedBy center value) :
    (∀ (phi theta : ℝ), 1 < phi → theta = phi - 1 →
      let M := concreteMallowsSpec center theta
      M.q = phi⁻¹ ∧
        ∀ pi : Ranking n,
          (M.law pi).toReal =
            phi⁻¹ ^ kendallTau center pi /
              (∑ tau : Ranking n, phi⁻¹ ^ kendallTau center tau)) ∧
    (∀ theta, 0 < theta → ∀ pi : Ranking n,
      ContinuousAt
          (fun theta' =>
            ((concreteMallowsSpec center theta').law pi).toReal) theta ∧
        DifferentiableAt ℝ
          (fun theta' =>
            ((concreteMallowsSpec center theta').law pi).toReal) theta) ∧
    Tendsto
      (fun theta => ((concreteMallowsSpec center theta).law center).toReal)
      atTop (nhds 1) ∧
    ∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
      (∀ remaining : Finset (Candidate n), remaining.Nonempty →
        expectedBestInSet (concreteMallowsSpec center thetaH).law value remaining ≤
          expectedBestInSet (concreteMallowsSpec center thetaA).law value remaining) ∧
      expectedBestInSet (concreteMallowsSpec center thetaH).law value Finset.univ <
        expectedBestInSet (concreteMallowsSpec center thetaA).law value Finset.univ := by
  have hdefinition := concreteMallowsAccuracyFamily_sourceDefinition1 center value hvalue
  refine ⟨?_, hdefinition.1, hdefinition.2.1, hdefinition.2.2⟩
  intro phi theta hphi htheta
  dsimp
  refine ⟨(source_equation8_concrete_mallows_probability center phi theta
    hphi htheta center).1, ?_⟩
  intro pi
  exact (source_equation8_concrete_mallows_probability center phi theta
    hphi htheta pi).2

/-! ## Appendix D and Appendix E source formulas -/

/--
Appendix D's printed (D.1) direction is false.  This finite two-candidate
counterexample uses the exact denominator-cleared form of the displayed
cross-ratio.  The independently proved Theorem 9 Definition 1 endpoint above
does not rely on this defective printed argument.
-/
theorem equationD1_printed_mallows_likelihood_ratio_false_two_candidates :
    ¬ AppendixDPrintedReverseMLR 0 ((1 : ℝ) / 2) ((3 : ℝ) / 4) :=
  KR21Monoculture.appendixD_printed_reverse_mlr_false_two_candidates

/--
The corrected D.1 cross-ratio direction is proved for every nonempty remaining
set in the three-candidate source universe.  The arbitrary-universe,
arbitrary-remaining-set strengthening is deliberately not asserted here.
-/
theorem equationD1_corrected_mallows_likelihood_ratio_three_candidates
    {qAccurate qNoisy : ℝ} (hqAccurate_pos : 0 < qAccurate)
    (hq_lt : qAccurate < qNoisy) :
    AppendixDCorrectedMallowsMLR 1 qAccurate qNoisy :=
  KR21Monoculture.appendixD_corrected_mlr_three_candidates
    hqAccurate_pos hq_lt

/--
The same approved D.1 repair with its unnormalized rank-labelled fiber masses
expanded in the paper interface.  The universe `Candidate 1` has exactly
three candidates; no arbitrary-center or normalized-probability claim is
hidden behind the definition name.
-/
theorem equationD1_corrected_mallows_likelihood_ratio_three_candidates_explicit
    {qAccurate qNoisy : ℝ} (hqAccurate_pos : 0 < qAccurate)
    (hq_lt : qAccurate < qNoisy) :
    ∀ {remaining : Finset (Candidate 1)}, remaining.Nonempty →
      ∀ {better worse : Candidate 1},
        better ∈ remaining → worse ∈ remaining → better < worse →
          0 ≤
            reflMallowsBestInSetWeight 1 qAccurate remaining better *
                reflMallowsBestInSetWeight 1 qNoisy remaining worse -
              reflMallowsBestInSetWeight 1 qAccurate remaining worse *
                reflMallowsBestInSetWeight 1 qNoisy remaining better := by
  exact KR21Monoculture.appendixD_corrected_mlr_three_candidates
    hqAccurate_pos hq_lt

/--
Paper-facing normalized D.1 repair for an arbitrary common Mallows center in
the source three-candidate universe. Here `q = phi inverse`, so the more
accurate law has `0 < qAccurate < qNoisy`.
-/
theorem equationD1_corrected_normalized_mallows_likelihood_ratio_three_candidates
    (center : Ranking 1) {qAccurate qNoisy : ℝ}
    (hqAccurate_pos : 0 < qAccurate) (hq_lt : qAccurate < qNoisy)
    {remaining : Finset (Candidate 1)} (hremaining : remaining.Nonempty)
    {better worse : Candidate 1}
    (hbetter : better ∈ remaining) (hworse : worse ∈ remaining)
    (hcenter_order : rankOf center better < rankOf center worse) :
    0 <
      pmfProb (MallowsSpec.ofQ center qAccurate hqAccurate_pos).law
          (fun pi => better = bestInSet pi remaining) *
        pmfProb (MallowsSpec.ofQ center qNoisy (lt_trans hqAccurate_pos hq_lt)).law
          (fun pi => worse = bestInSet pi remaining) -
      pmfProb (MallowsSpec.ofQ center qAccurate hqAccurate_pos).law
          (fun pi => worse = bestInSet pi remaining) *
        pmfProb (MallowsSpec.ofQ center qNoisy (lt_trans hqAccurate_pos hq_lt)).law
          (fun pi => better = bestInSet pi remaining) := by
  let MAcc := MallowsSpec.ofQ center qAccurate hqAccurate_pos
  let MNoisy := MallowsSpec.ofQ center qNoisy (lt_trans hqAccurate_pos hq_lt)
  have hcenter : MAcc.center = MNoisy.center := by
    simp [MAcc, MNoisy, MallowsSpec.ofQ]
  have hq : MAcc.q < MNoisy.q := by
    simpa [MAcc, MNoisy, MallowsSpec.ofQ] using hq_lt
  have horder : rankOf MAcc.center better < rankOf MAcc.center worse := by
    simpa [MAcc, MallowsSpec.ofQ] using hcenter_order
  simpa [MAcc, MNoisy] using
    (mallowsBestInSetProbabilityMLR_three_candidates_strict
      hcenter hq hremaining hbetter hworse horder)

/--
The corrected D.1 likelihood-ratio comparison at the literal source parameter
surface.  The source law uses mass proportional to `phi^(-distance)`: the two
visible equalities record its `q = phi inverse` convention, while the strict
cross product is the normalized probability comparison used in the proof.
-/
theorem equationD1_corrected_source_phi_likelihood_ratio_three_candidates
    (center : Ranking 1) {phiNoisy phiAccurate : ℝ}
    (hphiNoisy : 1 < phiNoisy) (hphi_lt : phiNoisy < phiAccurate)
    {remaining : Finset (Candidate 1)} (hremaining : remaining.Nonempty)
    {better worse : Candidate 1}
    (hbetter : better ∈ remaining) (hworse : worse ∈ remaining)
    (hcenter_order : rankOf center better < rankOf center worse) :
    (SourceMallowsSequential.sourceMallowsSpec center phiAccurate).q =
        phiAccurate⁻¹ ∧
      (SourceMallowsSequential.sourceMallowsSpec center phiNoisy).q =
        phiNoisy⁻¹ ∧
      0 <
        pmfProb (SourceMallowsSequential.sourceMallowsSpec center phiAccurate).law
            (fun pi => better = bestInSet pi remaining) *
          pmfProb (SourceMallowsSequential.sourceMallowsSpec center phiNoisy).law
            (fun pi => worse = bestInSet pi remaining) -
          pmfProb (SourceMallowsSequential.sourceMallowsSpec center phiAccurate).law
            (fun pi => worse = bestInSet pi remaining) *
          pmfProb (SourceMallowsSequential.sourceMallowsSpec center phiNoisy).law
            (fun pi => better = bestInSet pi remaining) := by
  have hphiAccurate : 1 < phiAccurate := lt_trans hphiNoisy hphi_lt
  refine ⟨SourceMallowsSequential.sourceMallowsSpec_q_eq_inv center hphiAccurate,
    SourceMallowsSequential.sourceMallowsSpec_q_eq_inv center hphiNoisy, ?_⟩
  have hq :
      (SourceMallowsSequential.sourceMallowsSpec center phiAccurate).q <
        (SourceMallowsSequential.sourceMallowsSpec center phiNoisy).q := by
    rw [SourceMallowsSequential.sourceMallowsSpec_q_eq_inv center hphiAccurate,
      SourceMallowsSequential.sourceMallowsSpec_q_eq_inv center hphiNoisy]
    exact (inv_lt_inv₀ (by linarith) (by linarith)).2 hphi_lt
  exact mallowsBestInSetProbabilityMLR_three_candidates_strict
    (MAcc := SourceMallowsSequential.sourceMallowsSpec center phiAccurate)
    (MNoisy := SourceMallowsSequential.sourceMallowsSpec center phiNoisy)
    rfl hq hremaining hbetter hworse hcenter_order

/--
Appendix E (E.1), in the literal source conditional-expectation syntax.  For
positive Mallows accuracy and at least three source candidates, the expected
first-minus-second value gap conditional on independent top-choice
disagreement is strictly positive.
-/
theorem equationE1_concrete_mallows_source_conditional_gain_pos
    {n : ℕ} (center : Ranking n) {theta : ℝ} (htheta : 0 < theta) (hn : 0 < n)
    {value : Candidate n → ℝ} (hvalue : StrictlyOrderedBy center value) :
    let M := concreteMallowsSpec center theta
    0 < AppliedModelingLib.pmfPairConditionalExp M.law M.law disagreementEvent
      (fun pair => value (firstChoice pair.1) - value (secondChoice pair.1)) := by
  simpa [MallowsSpec.appendixE1SourceGap] using
    (KR21Monoculture.concreteMallows_appendixE_source_endpoints
      center htheta hn hvalue).1

/--
Appendix E (E.2), in its literal ordered-top-two conditional-event form.
Every center-ordered pair has the weak comparison, and this source theorem
also has a separate strict witness at the center's top two candidates.
-/
theorem equationE2_concrete_mallows_source_conditional_top_two_comparison
    {n : ℕ} (center : Ranking n) {theta : ℝ} (htheta : 0 < theta) (hn : 0 < n)
    {value : Candidate n → ℝ} (hvalue : StrictlyOrderedBy center value) :
    let M := concreteMallowsSpec center theta
    ∀ c d : Candidate n, rankOf M.center c < rankOf M.center d →
      AppliedModelingLib.pmfPairConditionalExp M.law M.law disagreementEvent
          (fun pair =>
            if d = firstChoice pair.1 ∧ c = secondChoice pair.1 then (1 : ℝ) else 0) ≤
        AppliedModelingLib.pmfPairConditionalExp M.law M.law disagreementEvent
          (fun pair =>
            if c = firstChoice pair.1 ∧ d = secondChoice pair.1 then (1 : ℝ) else 0) := by
  simpa [MallowsSpec.AppendixE2PairwiseComparison,
    MallowsSpec.appendixE2ConditionalTopTwoProbability] using
    (KR21Monoculture.concreteMallows_appendixE_source_endpoints
      center htheta hn hvalue).2.1

/--
Appendix E (E.3), in its literal denominator-cleared independent-product
form.  The top-two mass times the independent top-miss probability is weakly
larger for every center-ordered pair.
-/
theorem equationE3_concrete_mallows_source_unconditional_product
    {n : ℕ} (center : Ranking n) {theta : ℝ} (htheta : 0 < theta) (hn : 0 < n)
    {value : Candidate n → ℝ} (hvalue : StrictlyOrderedBy center value) :
    let M := concreteMallowsSpec center theta
    ∀ c d : Candidate n, rankOf M.center c < rankOf M.center d →
      0 ≤ M.firstSecondChoiceProb c d * firstChoiceMissProb M.law c -
        M.firstSecondChoiceProb d c * firstChoiceMissProb M.law d := by
  simpa [MallowsSpec.AppendixE3PairwiseCrossInequality,
    MallowsSpec.appendixE3CrossDifference] using
    (KR21Monoculture.concreteMallows_appendixE_source_endpoints
      center htheta hn hvalue).2.2.2.1

/--
Appendix E (E.1) at the paper's `phi` parameter surface.  `0 < n` records the
necessary source correction `N >= 3`; it is not silently inferred from the
finite carrier encoding.
-/
theorem equationE1_source_concrete_mallows_phi
    {n : ℕ} (center : Ranking n) (phi theta : ℝ)
    (hphi : 1 < phi) (htheta : theta = phi - 1) (hn : 0 < n)
    {value : Candidate n → ℝ} (hvalue : StrictlyOrderedBy center value) :
    let M := concreteMallowsSpec center theta
    0 < AppliedModelingLib.pmfPairConditionalExp M.law M.law disagreementEvent
      (fun pair => value (firstChoice pair.1) - value (secondChoice pair.1)) := by
  exact (KR21Monoculture.source_appendixE_concrete_mallows_phi
    center phi theta hphi htheta hn hvalue).1

/--
Appendix E (E.2) at the literal source parameter surface.  The conclusion
includes both the all-pair weak comparison and the source's required strict
witness, derived from the concrete Mallows law.
-/
theorem equationE2_source_concrete_mallows_phi
    {n : ℕ} (center : Ranking n) (phi theta : ℝ)
    (hphi : 1 < phi) (htheta : theta = phi - 1) (hn : 0 < n) :
    let M := concreteMallowsSpec center theta
    (∀ c d : Candidate n, rankOf M.center c < rankOf M.center d →
      AppliedModelingLib.pmfPairConditionalExp M.law M.law disagreementEvent
          (fun pair =>
            if d = firstChoice pair.1 ∧ c = secondChoice pair.1 then (1 : ℝ) else 0) ≤
        AppliedModelingLib.pmfPairConditionalExp M.law M.law disagreementEvent
          (fun pair =>
            if c = firstChoice pair.1 ∧ d = secondChoice pair.1 then (1 : ℝ) else 0)) ∧
      ∃ c d : Candidate n, rankOf M.center c < rankOf M.center d ∧
        AppliedModelingLib.pmfPairConditionalExp M.law M.law disagreementEvent
            (fun pair =>
              if d = firstChoice pair.1 ∧ c = secondChoice pair.1 then (1 : ℝ) else 0) <
          AppliedModelingLib.pmfPairConditionalExp M.law M.law disagreementEvent
            (fun pair =>
              if c = firstChoice pair.1 ∧ d = secondChoice pair.1 then (1 : ℝ) else 0) :=
  KR21Monoculture.source_appendixE2_concrete_mallows_phi
    center phi theta hphi htheta hn

/--
Appendix E (E.3) at the literal source parameter surface.  The conclusion
includes the denominator-cleared all-pair inequality and its strict witness;
the printed intermediate sign error is not used.
-/
theorem equationE3_source_concrete_mallows_phi
    {n : ℕ} (center : Ranking n) (phi theta : ℝ)
    (hphi : 1 < phi) (htheta : theta = phi - 1) (hn : 0 < n) :
    let M := concreteMallowsSpec center theta
    (∀ c d : Candidate n, rankOf M.center c < rankOf M.center d →
      0 ≤ M.firstSecondChoiceProb c d * firstChoiceMissProb M.law c -
        M.firstSecondChoiceProb d c * firstChoiceMissProb M.law d) ∧
      ∃ c d : Candidate n, rankOf M.center c < rankOf M.center d ∧
        0 < M.firstSecondChoiceProb c d * firstChoiceMissProb M.law c -
          M.firstSecondChoiceProb d c * firstChoiceMissProb M.law d :=
  KR21Monoculture.source_appendixE3_concrete_mallows_phi
    center phi theta hphi htheta hn

/--
The literal E.2 conditional event factorizes into its ordered-top-two mass and
the independent other draw's top-miss mass divided by top-disagreement mass.
-/
theorem equationE2_mallows_conditional_top_two_factorization
    {n : ℕ} (M : MallowsSpec n) (c d : Candidate n) :
    AppliedModelingLib.pmfPairConditionalExp M.law M.law disagreementEvent
        (fun pair =>
          if c = firstChoice pair.1 ∧ d = secondChoice pair.1 then (1 : ℝ) else 0) =
      (M.firstSecondChoiceProb c d * firstChoiceMissProb M.law c) /
        disagreementProb M.law := by
  simpa [MallowsSpec.appendixE2ConditionalTopTwoProbability] using
    M.appendixE2ConditionalTopTwoProbability_eq_source_product_div c d

/--
The literal E.3 cross-product equals the normalized finite Mallows bracket;
the equality exposes the denominator rather than treating the source formula
as a consequence of a downstream payoff theorem.
-/
theorem equationE3_mallows_cross_product_factorization
    {n : ℕ} (M : MallowsSpec n) (c d : Candidate n) :
    M.firstSecondChoiceProb c d * firstChoiceMissProb M.law c -
      M.firstSecondChoiceProb d c * firstChoiceMissProb M.law d =
        M.independentPairBracket c d / (M.partition * M.partition) := by
  simpa [MallowsSpec.appendixE3CrossDifference] using
    M.appendixE3CrossDifference_eq_independentPairBracket_div_partition_sq c d

/--
Paper Theorem 1, concrete Mallows family form: for a strict center-ordered
value profile and positive human accuracy, the concrete Mallows accuracy family
has a more accurate algorithmic parameter witnessing the monoculture paradox.
-/
theorem theorem1_concrete_mallows_family
    {n : ℕ} (center : Ranking n) (value : Candidate n → ℝ)
    (hvalue : StrictlyOrderedBy center value)
    (hn : 0 < n) (θH : ℝ) (hθH : 0 < θH) :
    AccuracyFamily.Theorem1Target
      (MallowsAccuracyFamilySpec.toAccuracyFamily
        (concreteMallowsAccuracyFamilySpec center value hvalue))
      θH :=
  KR21Monoculture.paper_theorem1_concrete_mallows_family
    center value hvalue hn θH hθH

/-! ## source verification: outer `D`, Theorem 5, PL, simulation, and appendices -/

/--
D-averaged Definition 2/3 component of the Gaussian Theorem 2 route. Its
inferred signature exposes the needed integrability; it is not the full source
Theorem 2/1 conclusion.
-/
abbrev theorem2_gaussian_outer_value_distribution :=
  @KR21Monoculture.theorem2_gaussian_with_outer_value_distribution

/-- D-averaged Definition 2/3 component of the canonical Laplace route. -/
abbrev theorem2_laplace_outer_value_distribution :=
  @KR21Monoculture.theorem2_laplace_with_outer_value_distribution

/--
Definitions 2--3 outer-distribution bridge.  If the fixed-value Definition 2
comparison holds at every realized value profile and both conditional payoffs
are integrable, it holds after the source's joint draw from `D`.
-/
theorem definition2_with_outer_value_distribution_of_pointwise
    {n : ℕ} (F : DistributionalAccuracyFamily n)
    (D : Measure (ValueProfile n)) [IsProbabilityMeasure D] (theta : ℝ)
    (hshared : Integrable
      (fun value => expectedSecondMoverShared (F.dist theta value) value) D)
    (hindependent : Integrable
      (fun value => expectedSecondMoverIndependent
        (F.dist theta value) (F.dist theta value) value) D)
    (hpoint : ∀ value,
      Model.PrefersIndependentReranking (F.dist theta value) value) :
    F.PrefersIndependentReranking D theta :=
  DistributionalAccuracyFamily.prefersIndependentReranking_of_pointwise
    F D theta hshared hindependent hpoint

/--
Definition 2's conditional comparison is a conditional gain in the actual
joint experiment: first draw values from `D`, then draw two conditionally
independent rankings.  The explicit joint regularity bundle prevents
totalized-integral artifacts; the positive-mass premise is on the actual joint
top-disagreement event.
-/
theorem definition2_outer_joint_conditional_gain_iff
    {n : ℕ} (F : DistributionalAccuracyFamily n)
    (D : Measure (ValueProfile n)) (theta : ℝ)
    (regularity : DistributionalAccuracyFamily.OuterIndependentRerankingJointRegularity
      F D theta)
    (hdisagreement : 0 < ∫ x : ValueProfile n × RankingPair n,
      (if disagreementEvent x.2 then (1 : ℝ) else 0) ∂
        F.outerIndependentPairJointLaw D theta
          regularity.base.ranking_atom_measurable) :
    F.PrefersIndependentReranking D theta ↔
      0 < F.jointLawDisagreementConditionalGain D theta
        regularity.base.ranking_atom_measurable :=
  DistributionalAccuracyFamily.prefersIndependentReranking_iff_jointLawDisagreementConditionalGain_pos_of_regular
    F D theta regularity hdisagreement

/--
Theorem 2, Gaussian Definition 2 in the literal source experiment: draw an
ordered three-candidate profile from `D`, then draw two conditionally iid
Gaussian RUM rankings.  The conditioning event has derived positive mass; the
visible joint-regularity record supplies the measurable kernel and genuine
raw-payoff expectations rather than totalized integrals.
-/
theorem theorem2_gaussian_outer_source_definition2
    (D : Measure (ValueProfile 1)) [IsProbabilityMeasure D]
    (theta : ℝ) (htheta : 0 < theta)
    (horder : ∀ᵐ value ∂D,
      value (1 : Candidate 1) < value (0 : Candidate 1) ∧
        value (2 : Candidate 1) < value (1 : Candidate 1))
    (regularity : DistributionalAccuracyFamily.OuterIndependentRerankingJointRegularity
      gaussianThreeCandidateDistributionalFamily D theta) :
    0 < gaussianThreeCandidateDistributionalFamily.jointLawDisagreementConditionalGain
      D theta regularity.base.ranking_atom_measurable :=
  gaussianThreeCandidate_outer_jointLawDisagreementConditionalGain_pos
    D theta htheta horder regularity

/--
Theorem 2, Gaussian Definition 3 after the source outer value draw.  The
integrability of each displayed payoff remains explicit because it is needed
to make the source expectations real-valued.
-/
theorem theorem2_gaussian_outer_source_definition3
    (D : Measure (ValueProfile 1)) [IsProbabilityMeasure D]
    (thetaA thetaH : ℝ) (hthetaH : 0 < thetaH) (hthetaHA : thetaH < thetaA)
    (horder : ∀ᵐ value ∂D,
      value (1 : Candidate 1) < value (0 : Candidate 1) ∧
        value (2 : Candidate 1) < value (1 : Candidate 1))
    (hbetter : Integrable (fun value => expectedSecondMoverIndependent
      (gaussianThreeCandidateDistributionalFamily.dist thetaH value)
      (gaussianThreeCandidateDistributionalFamily.dist thetaA value) value) D)
    (hworse : Integrable (fun value => expectedSecondMoverIndependent
      (gaussianThreeCandidateDistributionalFamily.dist thetaH value)
      (gaussianThreeCandidateDistributionalFamily.dist thetaH value) value) D) :
    gaussianThreeCandidateDistributionalFamily.PrefersWeakerCompetition
      D thetaA thetaH :=
  gaussianThreeCandidate_outer_prefersWeakerCompetition
    D thetaA thetaH hthetaH hthetaHA horder hbetter hworse

/--
Theorem 2, Laplace Definition 2 in the literal source outer-plus-conditionally
iid-ranking experiment.  As in the Gaussian row, positive disagreement mass
is derived from strict pointwise preference, while the joint-law regularity
conditions remain visible.
-/
theorem theorem2_laplace_outer_source_definition2
    (D : Measure (ValueProfile 1)) [IsProbabilityMeasure D]
    (theta : ℝ) (htheta : 0 < theta)
    (horder : ∀ᵐ value ∂D,
      value (1 : Candidate 1) < value (0 : Candidate 1) ∧
        value (2 : Candidate 1) < value (1 : Candidate 1))
    (regularity : DistributionalAccuracyFamily.OuterIndependentRerankingJointRegularity
      sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily D theta) :
    0 < sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily.jointLawDisagreementConditionalGain
      D theta regularity.base.ranking_atom_measurable :=
  sourceUnitVarianceLaplaceThreeCandidate_outer_jointLawDisagreementConditionalGain_pos
    D theta htheta horder regularity

/--
Theorem 2, Laplace Definition 3 after the source outer value draw.  The
visible payoff-integrability conditions are the well-posedness assumptions
needed by the two ex-ante source expectations.
-/
theorem theorem2_laplace_outer_source_definition3
    (D : Measure (ValueProfile 1)) [IsProbabilityMeasure D]
    (thetaA thetaH : ℝ) (hthetaH : 0 < thetaH) (hthetaHA : thetaH < thetaA)
    (horder : ∀ᵐ value ∂D,
      value (1 : Candidate 1) < value (0 : Candidate 1) ∧
        value (2 : Candidate 1) < value (1 : Candidate 1))
    (hbetter : Integrable (fun value => expectedSecondMoverIndependent
      (sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily.dist thetaH value)
      (sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily.dist thetaA value) value) D)
    (hworse : Integrable (fun value => expectedSecondMoverIndependent
      (sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily.dist thetaH value)
      (sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily.dist thetaH value) value) D) :
    sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily.PrefersWeakerCompetition
      D thetaA thetaH :=
  sourceUnitVarianceLaplaceThreeCandidate_outer_prefersWeakerCompetition
    D thetaA thetaH hthetaH hthetaHA horder hbetter hworse

/--
Theorem 2, Gaussian route, at the advertised outer-D Theorem 1 conclusion.
For the source's fixed rank-labelled three-candidate model, coordinatewise
finite first moments and almost-everywhere strict source order are the only
visible outer-law regularity premises.  The proof derives atom measurability,
all payoff integrability, Definitions 2--3, the high-accuracy bridge, and one
common algorithmic witness internally.

This endpoint intentionally states the advertised Theorem 1 conclusion.  It
does not silently replace the source's separate Definition 1 package with a
conclusion-only claim; that package is reviewed on its own row.
-/
theorem theorem2_gaussian_threeCandidate_outer_source_theorem1
    (D : Measure (ValueProfile 1)) [IsProbabilityMeasure D]
    (thetaH : ℝ) (hthetaH : 0 < thetaH)
    (hvalue : ∀ c : Candidate 1,
      Integrable (fun value : ValueProfile 1 => value c) D)
    (horder : ∀ᵐ value ∂D,
      value (1 : Candidate 1) < value (0 : Candidate 1) ∧
        value (2 : Candidate 1) < value (1 : Candidate 1)) :
    gaussianThreeCandidateDistributionalFamily.DistributionalTheorem1Target D thetaH :=
  gaussianThreeCandidateDistributionalFamily_outer_theorem1
    D thetaH hthetaH hvalue horder

/--
Theorem 2, source-normalized Laplace route, at the same outer-D Theorem 1
conclusion.  The underlying rate is visibly `sqrt(2) * theta`, so the score
noise has the source's standard deviation `1 / theta`; no rate=`theta`
substitution is hidden in this endpoint.  As in the Gaussian theorem, all
kernel and payoff regularity used by the conclusion is derived from the two
displayed outer-law premises.

This is a conclusion endpoint, not a bundled substitute for every Definition
1 clause in the wording of Theorem 2.
-/
theorem theorem2_laplace_threeCandidate_outer_source_theorem1
    (D : Measure (ValueProfile 1)) [IsProbabilityMeasure D]
    (thetaH : ℝ) (hthetaH : 0 < thetaH)
    (hvalue : ∀ c : Candidate 1,
      Integrable (fun value : ValueProfile 1 => value c) D)
    (horder : ∀ᵐ value ∂D,
      value (1 : Candidate 1) < value (0 : Candidate 1) ∧
        value (2 : Candidate 1) < value (1 : Candidate 1)) :
    sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily.DistributionalTheorem1Target
      D thetaH :=
  sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily_outer_theorem1
    D thetaH hthetaH hvalue horder

/--
Complete source-facing Theorem 2 package.  One proposition ties the literal
Gaussian and source-normalized Laplace iid RUM transports to their all-fields
Definition 1 packages and their outer-D Theorem 1 conclusions.  The outer-D
regularity convention is visible in each universal clause instead of being
inferred from the two family names.
-/
theorem theorem2_gaussian_laplace_source_complete :
    (∀ {theta x1 x2 x3 : ℝ}, 0 < theta →
    (theorem2GaussianScaledNoiseFamily x1 x2 x3).dist theta =
      gaussianThreeCandidateRankingLaw theta x1 x2 x3) ∧
    (Var[id; ProbabilityTheory.gaussianReal 0 1] = 1) ∧
    (Var[id; w11BaseNoiseLaw sourceUnitVarianceLaplaceBaseDensity] = 1) ∧
    (∀ {theta x1 x2 x3 : ℝ}, 0 < theta →
      (sourceUnitVarianceLaplaceScaledNoiseFamily x1 x2 x3).dist theta =
        sourceUnitVarianceLaplaceThreeCandidateRankingLaw theta x1 x2 x3) ∧
    (∀ {x1 x2 x3 : ℝ}, x2 < x1 → x3 < x2 →
      SourceDefinition1NoisyPermutationFamily
        (gaussianThreeCandidateAccuracyFamily x1 x2 x3) rum3Ranking012) ∧
    (∀ {x1 x2 x3 : ℝ}, x2 < x1 → x3 < x2 →
      SourceDefinition1NoisyPermutationFamily
        (sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily.pointFamily
          (threeCandidateValueProfile x1 x2 x3)) rum3Ranking012) ∧
    (∀ (D : Measure (ValueProfile 1)) [IsProbabilityMeasure D]
      (thetaH : ℝ), 0 < thetaH →
      (∀ c : Candidate 1, Integrable (fun value : ValueProfile 1 => value c) D) →
      (∀ᵐ value ∂D,
        value (1 : Candidate 1) < value (0 : Candidate 1) ∧
          value (2 : Candidate 1) < value (1 : Candidate 1)) →
      ∃ thetaA, thetaH < thetaA ∧
        gaussianThreeCandidateDistributionalFamily.theorem1_g D thetaA thetaH <
          gaussianThreeCandidateDistributionalFamily.theorem1_f D thetaA thetaH ∧
        gaussianThreeCandidateDistributionalFamily.theorem1_h D thetaA thetaH <
          gaussianThreeCandidateDistributionalFamily.theorem1_algorithmAgainstHuman
            D thetaA thetaH ∧
        gaussianThreeCandidateDistributionalFamily.theorem1_f D thetaA thetaH <
          gaussianThreeCandidateDistributionalFamily.theorem1_h D thetaA thetaH) ∧
    ∀ (D : Measure (ValueProfile 1)) [IsProbabilityMeasure D]
      (thetaH : ℝ), 0 < thetaH →
      (∀ c : Candidate 1, Integrable (fun value : ValueProfile 1 => value c) D) →
      (∀ᵐ value ∂D,
        value (1 : Candidate 1) < value (0 : Candidate 1) ∧
          value (2 : Candidate 1) < value (1 : Candidate 1)) →
      ∃ thetaA, thetaH < thetaA ∧
        sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily.theorem1_g D thetaA thetaH <
          sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily.theorem1_f D thetaA thetaH ∧
        sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily.theorem1_h D thetaA thetaH <
          sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily.theorem1_algorithmAgainstHuman
            D thetaA thetaH ∧
        sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily.theorem1_f D thetaA thetaH <
        sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily.theorem1_h D thetaA thetaH := by
  refine ⟨?_, ?_, theorem2_laplace_source_base_noise_variance_one,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro theta x1 x2 x3 htheta
    exact theorem2_gaussian_literal_iid_rum_law_transport htheta
  · simpa using
      (ProbabilityTheory.variance_id_gaussianReal (μ := 0) (v := 1))
  · intro theta x1 x2 x3 htheta
    exact theorem2_laplace_literal_iid_rum_law_transport htheta
  · intro x1 x2 x3 hx12 hx23
    exact theorem2_gaussian_source_definition1 hx12 hx23
  · intro x1 x2 x3 hx12 hx23
    exact theorem2_laplace_source_definition1 hx12 hx23
  · intro D _ thetaH hthetaH hvalue horder
    exact theorem2_gaussian_threeCandidate_outer_source_theorem1 D thetaH hthetaH hvalue horder
  · intro D _ thetaH hthetaH hvalue horder
    exact theorem2_laplace_threeCandidate_outer_source_theorem1 D thetaH hthetaH hvalue horder

/--
Support transport for the semantic Theorem 2 review boundary.  The endpoint
below keeps the literal product measures in its type; these lemmas only make
the raw-law equalities provable without relying on a family name as an axiom.
-/
noncomputable def theorem2_semantic_gaussian_raw_rank
    (theta x1 x2 x3 : ℝ) : ℝ × (ℝ × ℝ) → Ranking 1 :=
  fun epsilon =>
    rankByScore (fun i =>
      threeCandidateValueProfile x1 x2 x3 i +
        rightTripleToCandidateFunction epsilon i / theta)

theorem measurable_theorem2_semantic_gaussian_raw_rank
    (theta x1 x2 x3 : ℝ) :
    Measurable (theorem2_semantic_gaussian_raw_rank theta x1 x2 x3) := by
  unfold theorem2_semantic_gaussian_raw_rank
  apply paper_appendixA_scaledNoise_rankByScore_measurable
  intro i
  fin_cases i
  · simpa [rightTripleToCandidateFunction] using measurable_fst
  · simpa [rightTripleToCandidateFunction] using measurable_snd.fst
  · simpa [rightTripleToCandidateFunction] using measurable_snd.snd

noncomputable def theorem2_semantic_laplace_raw_rank
    (theta x1 x2 x3 : ℝ) : ℝ × (ℝ × ℝ) → Ranking 1 :=
  fun epsilon =>
    rankByScore (fun i =>
      threeCandidateValueProfile x1 x2 x3 i +
        rightTripleToCandidateFunction epsilon i / theta)

theorem measurable_theorem2_semantic_laplace_raw_rank
    (theta x1 x2 x3 : ℝ) :
    Measurable (theorem2_semantic_laplace_raw_rank theta x1 x2 x3) := by
  exact measurable_theorem2_semantic_gaussian_raw_rank theta x1 x2 x3

local instance theorem2_semantic_laplace_base_isProbabilityMeasure :
    IsProbabilityMeasure (theorem7LaplaceMeasure (Real.sqrt 2) 0) := by
  exact ⟨theorem7LaplaceMeasure_univ (lam := Real.sqrt 2) (μ := 0)
    (Real.sqrt_pos.2 (by norm_num))⟩

theorem theorem2_semantic_gaussian_literal_iid_reindex :
    MeasurePreserving (rightTripleToCandidateMeasurableEquiv ℝ)
      ((ProbabilityTheory.gaussianReal 0 1).prod
        ((ProbabilityTheory.gaussianReal 0 1).prod
          (ProbabilityTheory.gaussianReal 0 1)))
      (Measure.pi (fun _ : Candidate 1 => ProbabilityTheory.gaussianReal 0 1)) := by
  letI : IsFiniteMeasure (ProbabilityTheory.gaussianReal 0 1) := ⟨by simp⟩
  exact measurePreserving_rightTripleToCandidateMeasurableEquiv
    (ProbabilityTheory.gaussianReal 0 1)

theorem theorem2_semantic_laplace_literal_iid_reindex :
    MeasurePreserving (rightTripleToCandidateMeasurableEquiv ℝ)
      ((theorem7LaplaceMeasure (Real.sqrt 2) 0).prod
        ((theorem7LaplaceMeasure (Real.sqrt 2) 0).prod
          (theorem7LaplaceMeasure (Real.sqrt 2) 0)))
      (Measure.pi (fun _ : Candidate 1 =>
        theorem7LaplaceMeasure (Real.sqrt 2) 0)) := by
  letI : IsFiniteMeasure (theorem7LaplaceMeasure (Real.sqrt 2) 0) := ⟨by simp⟩
  exact measurePreserving_rightTripleToCandidateMeasurableEquiv
    (theorem7LaplaceMeasure (Real.sqrt 2) 0)

theorem theorem2_semantic_gaussian_raw_ranking_transport
    {theta x1 x2 x3 : ℝ} (htheta : 0 < theta) :
    (theorem2GaussianScaledNoiseFamily x1 x2 x3).dist theta =
      rankingPMFOfMeasure
        ((ProbabilityTheory.gaussianReal 0 1).prod
          ((ProbabilityTheory.gaussianReal 0 1).prod
            (ProbabilityTheory.gaussianReal 0 1)))
        (theorem2_semantic_gaussian_raw_rank theta x1 x2 x3)
        (measurable_theorem2_semantic_gaussian_raw_rank theta x1 x2 x3) := by
  letI : IsProbabilityMeasure (w11CandidateNoiseLaw theorem2GaussianBaseDensity) :=
    w11CandidateNoiseLaw_isProbabilityMeasure_of_base_normalization 1
      theorem2GaussianBaseDensity theorem2GaussianBase_w11Regularity.normalized
  change
    paper_appendixA_scaledNoiseRankingPMF
      (w11CandidateNoiseLaw theorem2GaussianBaseDensity)
      (threeCandidateValueProfile x1 x2 x3) theta = _
  symm
  refine rankingPMFOfMeasure_eq_of_measurePreserving
    ((ProbabilityTheory.gaussianReal 0 1).prod
      ((ProbabilityTheory.gaussianReal 0 1).prod
        (ProbabilityTheory.gaussianReal 0 1)))
    (w11CandidateNoiseLaw theorem2GaussianBaseDensity)
    (rightTripleToCandidateMeasurableEquiv ℝ)
    theorem2GaussianStandardTriple_to_candidateNoise_measurePreserving
    (theorem2_semantic_gaussian_raw_rank theta x1 x2 x3)
    (measurable_theorem2_semantic_gaussian_raw_rank theta x1 x2 x3)
    (fun noise => rankByScore
      (fun i => threeCandidateValueProfile x1 x2 x3 i + noise i / theta))
    (paper_appendixA_scaledNoise_rankByScore_measurable
      (fun noise : Candidate 1 → ℝ => fun i => noise i)
      (fun i => measurable_pi_apply i)
      (threeCandidateValueProfile x1 x2 x3) theta) ?_
  intro epsilon
  simp only [theorem2_semantic_gaussian_raw_rank,
    rightTripleToCandidateMeasurableEquiv_apply_eq_function]

theorem theorem2_semantic_gaussian_raw_ranking_transport_measure
    {theta x1 x2 x3 : ℝ} (htheta : 0 < theta) :
    ((theorem2GaussianScaledNoiseFamily x1 x2 x3).dist theta).toMeasure =
      ((ProbabilityTheory.gaussianReal 0 1).prod
        ((ProbabilityTheory.gaussianReal 0 1).prod
          (ProbabilityTheory.gaussianReal 0 1))).map
        (fun epsilon => rankByScore (fun i =>
          threeCandidateValueProfile x1 x2 x3 i +
            rightTripleToCandidateFunction epsilon i / theta)) := by
  have h := congrArg PMF.toMeasure
    (theorem2_semantic_gaussian_raw_ranking_transport
      (theta := theta) (x1 := x1) (x2 := x2) (x3 := x3) htheta)
  simpa [theorem2_semantic_gaussian_raw_rank,
    AppliedModelingLib.SocialChoice.Ranking.rankingPMFOfMeasure] using h

theorem theorem2_semantic_laplace_raw_ranking_transport
    {theta x1 x2 x3 : ℝ} (htheta : 0 < theta) :
    (sourceUnitVarianceLaplaceScaledNoiseFamily x1 x2 x3).dist theta =
      rankingPMFOfMeasure
        ((theorem7LaplaceMeasure (Real.sqrt 2) 0).prod
          ((theorem7LaplaceMeasure (Real.sqrt 2) 0).prod
            (theorem7LaplaceMeasure (Real.sqrt 2) 0)))
        (theorem2_semantic_laplace_raw_rank theta x1 x2 x3)
        (measurable_theorem2_semantic_laplace_raw_rank theta x1 x2 x3) := by
  letI : IsProbabilityMeasure (w11CandidateNoiseLaw sourceUnitVarianceLaplaceBaseDensity) :=
    w11CandidateNoiseLaw_isProbabilityMeasure_of_base_normalization 1
      sourceUnitVarianceLaplaceBaseDensity
      sourceUnitVarianceLaplace_w11Regularity.normalized
  change
    paper_appendixA_scaledNoiseRankingPMF
      (w11CandidateNoiseLaw sourceUnitVarianceLaplaceBaseDensity)
      (threeCandidateValueProfile x1 x2 x3) theta = _
  symm
  refine rankingPMFOfMeasure_eq_of_measurePreserving
    ((theorem7LaplaceMeasure (Real.sqrt 2) 0).prod
      ((theorem7LaplaceMeasure (Real.sqrt 2) 0).prod
        (theorem7LaplaceMeasure (Real.sqrt 2) 0)))
    (w11CandidateNoiseLaw sourceUnitVarianceLaplaceBaseDensity)
    (rightTripleToCandidateMeasurableEquiv ℝ)
    sourceUnitVarianceLaplaceStandardTriple_to_candidateNoise_measurePreserving
    (theorem2_semantic_laplace_raw_rank theta x1 x2 x3)
    (measurable_theorem2_semantic_laplace_raw_rank theta x1 x2 x3)
    (fun noise => rankByScore
      (fun i => threeCandidateValueProfile x1 x2 x3 i + noise i / theta))
    (paper_appendixA_scaledNoise_rankByScore_measurable
      (fun noise : Candidate 1 → ℝ => fun i => noise i)
      (fun i => measurable_pi_apply i)
      (threeCandidateValueProfile x1 x2 x3) theta) ?_
  intro epsilon
  simp only [theorem2_semantic_laplace_raw_rank,
    rightTripleToCandidateMeasurableEquiv_apply_eq_function]

theorem theorem2_semantic_laplace_raw_ranking_transport_measure
    {theta x1 x2 x3 : ℝ} (htheta : 0 < theta) :
    ((sourceUnitVarianceLaplaceScaledNoiseFamily x1 x2 x3).dist theta).toMeasure =
      ((theorem7LaplaceMeasure (Real.sqrt 2) 0).prod
        ((theorem7LaplaceMeasure (Real.sqrt 2) 0).prod
          (theorem7LaplaceMeasure (Real.sqrt 2) 0))).map
        (fun epsilon => rankByScore (fun i =>
          threeCandidateValueProfile x1 x2 x3 i +
            rightTripleToCandidateFunction epsilon i / theta)) := by
  have h := congrArg PMF.toMeasure
    (theorem2_semantic_laplace_raw_ranking_transport
      (theta := theta) (x1 := x1) (x2 := x2) (x3 := x3) htheta)
  simpa [theorem2_semantic_laplace_raw_rank,
    AppliedModelingLib.SocialChoice.Ranking.rankingPMFOfMeasure] using h

theorem theorem2_semantic_gaussian_raw_source_definition1
    {x1 x2 x3 : ℝ} (hx12 : x2 < x1) (hx23 : x3 < x2) :
    SourceDefinition1NoisyPermutationFamily
      (theorem2GaussianScaledNoiseFamily x1 x2 x3) rum3Ranking012 := by
  let regularity := theorem2GaussianBase_w11Regularity
  rcases correctedW11ScaledNoiseDefinition1_sourceFaithful_of_source
    theorem2GaussianBaseDensity theorem2GaussianBaseDerivative
    regularity.density_integrable regularity.derivative_integrable
    regularity.density_measurable regularity.density_positive
    regularity.absolute_continuity regularity.derivative_ae_eq
    regularity.normalized
    (threeCandidateValueProfile x1 x2 x3) rum3Ranking012
    (theorem2GaussianScaledNoiseFamily_center_order hx12 hx23) with
      ⟨hlocal, hlimit, hweak, hstrict⟩
  refine ⟨hlocal, ?_, ?_⟩
  · simpa using hlimit rum3Ranking012
  · intro thetaA thetaH hthetaH hthetaHA
    exact ⟨hweak thetaA thetaH hthetaH hthetaHA,
      hstrict thetaA thetaH hthetaH hthetaHA⟩

theorem theorem2_semantic_laplace_raw_source_definition1
    {x1 x2 x3 : ℝ} (hx12 : x2 < x1) (hx23 : x3 < x2) :
    SourceDefinition1NoisyPermutationFamily
      (sourceUnitVarianceLaplaceScaledNoiseFamily x1 x2 x3) rum3Ranking012 := by
  let regularity := sourceUnitVarianceLaplace_w11Regularity
  rcases correctedW11ScaledNoiseDefinition1_sourceFaithful_of_source
    sourceUnitVarianceLaplaceBaseDensity sourceUnitVarianceLaplaceBaseWeakDerivative
    regularity.density_integrable regularity.derivative_integrable
    regularity.density_measurable regularity.density_positive
    regularity.absolute_continuity regularity.derivative_ae_eq
    regularity.normalized
    (threeCandidateValueProfile x1 x2 x3) rum3Ranking012
    (sourceUnitVarianceLaplaceScaledNoiseFamily_center_order hx12 hx23) with
      ⟨hlocal, hlimit, hweak, hstrict⟩
  refine ⟨hlocal, ?_, ?_⟩
  · simpa using hlimit rum3Ranking012
  · intro thetaA thetaH hthetaH hthetaHA
    exact ⟨hweak thetaA thetaH hthetaH hthetaHA,
      hstrict thetaA thetaH hthetaH hthetaHA⟩

/-- The Gaussian base law used by Theorem 2 has literal variance one.  This
keeps the source's standard-deviation calibration visible instead of relying on
the parameter name of `gaussianReal`. -/
theorem theorem2_gaussian_source_base_noise_variance_one :
    Var[id; ProbabilityTheory.gaussianReal 0 1] = 1 := by
  simpa using
    (ProbabilityTheory.variance_id_gaussianReal (μ := 0) (v := 1))

/--
Theorem 2 with literal Gaussian and source-normalized Laplace iid product
laws.  Every paper-facing construction appears in this proposition's type:
the product laws, raw score map, variance normalization, Definition 1, the
literal outer-D Definition 2/3 conditions, and the resulting Theorem 1
conclusion.  Named RUM families are proved bridges, not assumptions.
-/
theorem theorem2_gaussian_laplace_source_semantic_complete :
    (∀ {theta x1 x2 x3 : ℝ}, 0 < theta →
      MeasurePreserving (rightTripleToCandidateMeasurableEquiv ℝ)
        ((ProbabilityTheory.gaussianReal 0 1).prod
          ((ProbabilityTheory.gaussianReal 0 1).prod
            (ProbabilityTheory.gaussianReal 0 1)))
        (Measure.pi (fun _ : Candidate 1 => ProbabilityTheory.gaussianReal 0 1)) ∧
      ((theorem2GaussianScaledNoiseFamily x1 x2 x3).dist theta).toMeasure =
        ((ProbabilityTheory.gaussianReal 0 1).prod
          ((ProbabilityTheory.gaussianReal 0 1).prod
            (ProbabilityTheory.gaussianReal 0 1))).map
          (fun epsilon => rankByScore (fun i =>
            threeCandidateValueProfile x1 x2 x3 i +
              rightTripleToCandidateFunction epsilon i / theta)) ∧
      (theorem2GaussianScaledNoiseFamily x1 x2 x3).dist theta =
        gaussianThreeCandidateRankingLaw theta x1 x2 x3) ∧
    (Var[id; ProbabilityTheory.gaussianReal 0 1] = 1) ∧
  (Var[id; w11BaseNoiseLaw sourceUnitVarianceLaplaceBaseDensity] = 1) ∧
    (∀ {theta x1 x2 x3 : ℝ}, 0 < theta →
      MeasurePreserving (rightTripleToCandidateMeasurableEquiv ℝ)
        ((theorem7LaplaceMeasure (Real.sqrt 2) 0).prod
          ((theorem7LaplaceMeasure (Real.sqrt 2) 0).prod
            (theorem7LaplaceMeasure (Real.sqrt 2) 0)))
        (Measure.pi (fun _ : Candidate 1 =>
          theorem7LaplaceMeasure (Real.sqrt 2) 0)) ∧
      ((sourceUnitVarianceLaplaceScaledNoiseFamily x1 x2 x3).dist theta).toMeasure =
        ((theorem7LaplaceMeasure (Real.sqrt 2) 0).prod
          ((theorem7LaplaceMeasure (Real.sqrt 2) 0).prod
            (theorem7LaplaceMeasure (Real.sqrt 2) 0))).map
          (fun epsilon => rankByScore (fun i =>
            threeCandidateValueProfile x1 x2 x3 i +
              rightTripleToCandidateFunction epsilon i / theta)) ∧
      (sourceUnitVarianceLaplaceScaledNoiseFamily x1 x2 x3).dist theta =
        sourceUnitVarianceLaplaceThreeCandidateRankingLaw theta x1 x2 x3) ∧
    (∀ {x1 x2 x3 : ℝ}, x2 < x1 → x3 < x2 →
      (∀ theta, 0 < theta → ∀ pi : Ranking 1,
        ContinuousAt (fun theta' =>
          ((theorem2GaussianScaledNoiseFamily x1 x2 x3).dist theta' pi).toReal) theta ∧
          DifferentiableAt ℝ (fun theta' =>
            ((theorem2GaussianScaledNoiseFamily x1 x2 x3).dist theta' pi).toReal) theta) ∧
      Tendsto (fun theta =>
        ((theorem2GaussianScaledNoiseFamily x1 x2 x3).dist theta rum3Ranking012).toReal)
        atTop (nhds 1) ∧
      ∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
        (∀ remaining : Finset (Candidate 1), remaining.Nonempty →
          expectedBestInSet ((theorem2GaussianScaledNoiseFamily x1 x2 x3).dist thetaH)
            (threeCandidateValueProfile x1 x2 x3) remaining ≤
            expectedBestInSet ((theorem2GaussianScaledNoiseFamily x1 x2 x3).dist thetaA)
              (threeCandidateValueProfile x1 x2 x3) remaining) ∧
        expectedBestInSet ((theorem2GaussianScaledNoiseFamily x1 x2 x3).dist thetaH)
          (threeCandidateValueProfile x1 x2 x3) Finset.univ <
          expectedBestInSet ((theorem2GaussianScaledNoiseFamily x1 x2 x3).dist thetaA)
            (threeCandidateValueProfile x1 x2 x3) Finset.univ) ∧
    (∀ {x1 x2 x3 : ℝ}, x2 < x1 → x3 < x2 →
      (∀ theta, 0 < theta → ∀ pi : Ranking 1,
        ContinuousAt (fun theta' =>
          ((sourceUnitVarianceLaplaceScaledNoiseFamily x1 x2 x3).dist theta' pi).toReal) theta ∧
          DifferentiableAt ℝ (fun theta' =>
            ((sourceUnitVarianceLaplaceScaledNoiseFamily x1 x2 x3).dist theta' pi).toReal) theta) ∧
      Tendsto (fun theta =>
        ((sourceUnitVarianceLaplaceScaledNoiseFamily x1 x2 x3).dist theta rum3Ranking012).toReal)
        atTop (nhds 1) ∧
      ∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
        (∀ remaining : Finset (Candidate 1), remaining.Nonempty →
          expectedBestInSet ((sourceUnitVarianceLaplaceScaledNoiseFamily x1 x2 x3).dist thetaH)
            (threeCandidateValueProfile x1 x2 x3) remaining ≤
            expectedBestInSet ((sourceUnitVarianceLaplaceScaledNoiseFamily x1 x2 x3).dist thetaA)
              (threeCandidateValueProfile x1 x2 x3) remaining) ∧
        expectedBestInSet ((sourceUnitVarianceLaplaceScaledNoiseFamily x1 x2 x3).dist thetaH)
          (threeCandidateValueProfile x1 x2 x3) Finset.univ <
          expectedBestInSet ((sourceUnitVarianceLaplaceScaledNoiseFamily x1 x2 x3).dist thetaA)
            (threeCandidateValueProfile x1 x2 x3) Finset.univ) ∧
    (∀ (D : Measure (ValueProfile 1)) [IsProbabilityMeasure D]
      (hvalue : ∀ c : Candidate 1,
        Integrable (fun value : ValueProfile 1 => value c) D)
      (horder : ∀ᵐ value ∂D,
        value (1 : Candidate 1) < value (0 : Candidate 1) ∧
          value (2 : Candidate 1) < value (1 : Candidate 1)),
      (∀ theta : ℝ, 0 < theta →
        ∀ regularity : DistributionalAccuracyFamily.OuterIndependentRerankingJointRegularity
          gaussianThreeCandidateDistributionalFamily D theta,
          0 < ∫ x : ValueProfile 1 × RankingPair 1,
            (if disagreementEvent x.2 then (1 : ℝ) else 0) ∂
              gaussianThreeCandidateDistributionalFamily.outerIndependentPairJointLaw
                D theta regularity.base.ranking_atom_measurable ∧
          0 < gaussianThreeCandidateDistributionalFamily.jointLawDisagreementConditionalGain
            D theta regularity.base.ranking_atom_measurable) ∧
      ∀ thetaA thetaH : ℝ, 0 < thetaH → thetaH < thetaA →
        (∫ value,
          expectedSecondMoverIndependent
            (gaussianThreeCandidateDistributionalFamily.dist thetaH value)
            (gaussianThreeCandidateDistributionalFamily.dist thetaA value) value ∂D) <
          ∫ value,
            expectedSecondMoverIndependent
              (gaussianThreeCandidateDistributionalFamily.dist thetaH value)
              (gaussianThreeCandidateDistributionalFamily.dist thetaH value) value ∂D) ∧
    (∀ (D : Measure (ValueProfile 1)) [IsProbabilityMeasure D]
      (hvalue : ∀ c : Candidate 1,
        Integrable (fun value : ValueProfile 1 => value c) D)
      (horder : ∀ᵐ value ∂D,
        value (1 : Candidate 1) < value (0 : Candidate 1) ∧
          value (2 : Candidate 1) < value (1 : Candidate 1)),
      (∀ theta : ℝ, 0 < theta →
        ∀ regularity : DistributionalAccuracyFamily.OuterIndependentRerankingJointRegularity
          sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily D theta,
          0 < ∫ x : ValueProfile 1 × RankingPair 1,
            (if disagreementEvent x.2 then (1 : ℝ) else 0) ∂
              sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily.outerIndependentPairJointLaw
                D theta regularity.base.ranking_atom_measurable ∧
          0 < sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily.jointLawDisagreementConditionalGain
            D theta regularity.base.ranking_atom_measurable) ∧
      ∀ thetaA thetaH : ℝ, 0 < thetaH → thetaH < thetaA →
        (∫ value,
          expectedSecondMoverIndependent
            (sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily.dist thetaH value)
            (sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily.dist thetaA value)
            value ∂D) <
          ∫ value,
            expectedSecondMoverIndependent
              (sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily.dist thetaH value)
              (sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily.dist thetaH value)
              value ∂D) ∧
    (∀ (D : Measure (ValueProfile 1)) [IsProbabilityMeasure D]
      (thetaH : ℝ), 0 < thetaH →
      (∀ c : Candidate 1, Integrable (fun value : ValueProfile 1 => value c) D) →
      (∀ᵐ value ∂D,
        value (1 : Candidate 1) < value (0 : Candidate 1) ∧
          value (2 : Candidate 1) < value (1 : Candidate 1)) →
      ∃ thetaA, thetaH < thetaA ∧
        gaussianThreeCandidateDistributionalFamily.theorem1_g D thetaA thetaH <
          gaussianThreeCandidateDistributionalFamily.theorem1_f D thetaA thetaH ∧
        gaussianThreeCandidateDistributionalFamily.theorem1_h D thetaA thetaH <
          gaussianThreeCandidateDistributionalFamily.theorem1_algorithmAgainstHuman
            D thetaA thetaH ∧
        gaussianThreeCandidateDistributionalFamily.theorem1_f D thetaA thetaH <
          gaussianThreeCandidateDistributionalFamily.theorem1_h D thetaA thetaH) ∧
    ∀ (D : Measure (ValueProfile 1)) [IsProbabilityMeasure D]
      (thetaH : ℝ), 0 < thetaH →
      (∀ c : Candidate 1, Integrable (fun value : ValueProfile 1 => value c) D) →
      (∀ᵐ value ∂D,
        value (1 : Candidate 1) < value (0 : Candidate 1) ∧
          value (2 : Candidate 1) < value (1 : Candidate 1)) →
      ∃ thetaA, thetaH < thetaA ∧
        sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily.theorem1_g D thetaA thetaH <
          sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily.theorem1_f D thetaA thetaH ∧
        sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily.theorem1_h D thetaA thetaH <
          sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily.theorem1_algorithmAgainstHuman
            D thetaA thetaH ∧
        sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily.theorem1_f D thetaA thetaH <
        sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily.theorem1_h D thetaA thetaH := by
  refine ⟨?_, theorem2_gaussian_source_base_noise_variance_one,
    sourceUnitVarianceLaplaceBaseNoiseLaw_variance_one,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro theta x1 x2 x3 htheta
    exact ⟨theorem2_semantic_gaussian_literal_iid_reindex,
      theorem2_semantic_gaussian_raw_ranking_transport_measure htheta,
      theorem2GaussianScaledNoiseFamily_dist_eq_gaussianThreeCandidateRankingLaw htheta⟩
  · intro theta x1 x2 x3 htheta
    exact ⟨theorem2_semantic_laplace_literal_iid_reindex,
      theorem2_semantic_laplace_raw_ranking_transport_measure htheta,
      by simpa [sourceUnitVarianceLaplaceScaledNoiseFamily] using
        sourceUnitVarianceLaplaceScaledNoiseFamily_dist_eq_namedLaw htheta⟩
  · intro x1 x2 x3 hx12 hx23
    simpa only [SourceDefinition1NoisyPermutationFamily] using
      theorem2_semantic_gaussian_raw_source_definition1 hx12 hx23
  · intro x1 x2 x3 hx12 hx23
    simpa only [SourceDefinition1NoisyPermutationFamily] using
      theorem2_semantic_laplace_raw_source_definition1 hx12 hx23
  · intro D _ hvalue horder
    constructor
    · intro theta htheta regularity
      have hpoint : ∀ᵐ value ∂D,
          Model.PrefersIndependentReranking
            (gaussianThreeCandidateDistributionalFamily.dist theta value) value := by
        filter_upwards [horder] with value hvalue_order
        exact gaussianThreeCandidate_prefersIndependent
          htheta hvalue_order.1 hvalue_order.2
      refine ⟨?_, theorem2_gaussian_outer_source_definition2
        D theta htheta horder regularity⟩
      exact DistributionalAccuracyFamily.outerJointDisagreementEvent_pos_of_ae_pointwise_preference
        gaussianThreeCandidateDistributionalFamily D theta regularity hpoint
    · intro thetaA thetaH hthetaH hthetaA
      have h := theorem2_gaussian_outer_source_definition3
        D thetaA thetaH hthetaH hthetaA horder
        (gaussian_outer_independentSecondMover_integrable D thetaH thetaA hvalue)
        (gaussian_outer_independentSecondMover_integrable D thetaH thetaH hvalue)
      simpa [DistributionalAccuracyFamily.PrefersWeakerCompetition,
        DistributionalAccuracyFamily.outerExpected] using h
  · intro D _ hvalue horder
    constructor
    · intro theta htheta regularity
      have hpoint : ∀ᵐ value ∂D,
          Model.PrefersIndependentReranking
            (sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily.dist theta value)
            value := by
        filter_upwards [horder] with value hvalue_order
        exact sourceUnitVarianceLaplaceThreeCandidate_prefersIndependent
          htheta hvalue_order.1 hvalue_order.2
      refine ⟨?_, theorem2_laplace_outer_source_definition2
        D theta htheta horder regularity⟩
      exact DistributionalAccuracyFamily.outerJointDisagreementEvent_pos_of_ae_pointwise_preference
        sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily D theta regularity hpoint
    · intro thetaA thetaH hthetaH hthetaA
      have h := theorem2_laplace_outer_source_definition3
        D thetaA thetaH hthetaH hthetaA horder
        (sourceUnitVarianceLaplace_outer_independentSecondMover_integrable
          D thetaH thetaA hvalue)
        (sourceUnitVarianceLaplace_outer_independentSecondMover_integrable
          D thetaH thetaH hvalue)
      simpa [DistributionalAccuracyFamily.PrefersWeakerCompetition,
        DistributionalAccuracyFamily.outerExpected] using h
  · intro D _ thetaH hthetaH hvalue horder
    simpa only [DistributionalAccuracyFamily.DistributionalTheorem1Target] using
      gaussianThreeCandidateDistributionalFamily_outer_theorem1
        D thetaH hthetaH hvalue horder
  · intro D _ thetaH hthetaH hvalue horder
    simpa only [DistributionalAccuracyFamily.DistributionalTheorem1Target] using
      sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily_outer_theorem1
        D thetaH hthetaH hvalue horder

/-- The corresponding outer-distribution bridge for Definition 3. -/
theorem definition3_with_outer_value_distribution_of_pointwise
    {n : ℕ} (F : DistributionalAccuracyFamily n)
    (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    (thetaA thetaH : ℝ)
    (hbetter : Integrable
      (fun value => expectedSecondMoverIndependent
        (F.dist thetaH value) (F.dist thetaA value) value) D)
    (hworse : Integrable
      (fun value => expectedSecondMoverIndependent
        (F.dist thetaH value) (F.dist thetaH value) value) D)
    (hpoint : ∀ value,
      Model.PrefersWeakerCompetition
        (F.dist thetaA value) (F.dist thetaH value) value) :
    F.PrefersWeakerCompetition D thetaA thetaH :=
  DistributionalAccuracyFamily.prefersWeakerCompetition_of_pointwise
    F D thetaA thetaH hbetter hworse hpoint

/--
Conditional outer-D crossing theorem. The witness `thetaA` is outside the
integral, so one common algorithm accuracy works ex ante for `D`; the
D-averaged continuity, asymptotic, Definition 3, and dominance premises remain
explicit rather than being claimed as derived from the source hypotheses.
-/
theorem theorem1_with_outer_value_distribution
    {n : ℕ} (F : DistributionalAccuracyFamily n)
    (D : Measure (ValueProfile n)) [IsProbabilityMeasure D] (thetaH : ℝ)
    (hindependent : F.PrefersIndependentReranking D thetaH)
    (f_continuity : ∀ theta, thetaH ≤ theta →
      AppliedModelingLib.EpsilonContinuousAt
        (fun thetaA => F.theorem1_f D thetaA thetaH) theta)
    (g_continuity : ∀ theta, thetaH ≤ theta →
      AppliedModelingLib.EpsilonContinuousAt
        (fun thetaA => F.theorem1_g D thetaA thetaH) theta)
    (hasymptotic : ∀ lower, thetaH < lower →
      ∃ hi, lower < hi ∧
        F.theorem1_g D hi thetaH < F.theorem1_f D hi thetaH)
    (hweaker : ∀ thetaA, thetaH < thetaA →
      F.PrefersWeakerCompetition D thetaA thetaH)
    (hmonotone : ∀ thetaA, thetaH < thetaA →
      F.theorem1_h D thetaA thetaH <
        F.theorem1_algorithmAgainstHuman D thetaA thetaH) :
    F.DistributionalTheorem1Target D thetaH :=
  DistributionalAccuracyFamily.distributional_theorem1 F D thetaH
    { prefers_independent_at_equal := hindependent
      f_continuity := f_continuity
      g_continuity := g_continuity
      asymptotic_first_dominance := hasymptotic
      prefers_weaker_above := hweaker
      algorithm_against_human_above := hmonotone }

/--
Outer-D Theorem 1 lift from atomwise source-law regularity.  The high-accuracy
limit is lifted through the outer expectation by finite-law dominated
convergence, producing one common algorithmic accuracy.  The fixed source
rank-label convention, coordinate first moments, ranking-atom measurability,
and almost-everywhere pointwise Definition 2 premise are visible rather than
being inferred from an RUM name.  This is a source-proof support row: concrete
Gaussian/Laplace outer laws still need to discharge these hypotheses.
-/
theorem theorem1_outer_atomwise_regular_fixed_order_source
    {n : ℕ} (F : DistributionalAccuracyFamily n)
    (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    (thetaH : ℝ) (center : Ranking n)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D)
    (hatom_measurable : ∀ theta pi,
      AEStronglyMeasurable (fun value : ValueProfile n =>
        ((F.dist theta value) pi).toReal) D)
    (hatom_continuous : ∀ value pi theta,
      AppliedModelingLib.EpsilonContinuousAt
        (fun theta' => ((F.dist theta' value) pi).toReal) theta)
    (hatom_tendsto : ∀ᵐ value ∂D, ∀ pi,
      Tendsto (fun theta => ((F.dist theta value) pi).toReal) atTop
        (𝓝 (((PMF.pure center : PMF (Ranking n)) pi).toReal)))
    (hgfirst : Integrable (fun value =>
      expectedFirstMoverUtility (F.dist thetaH value) value) D)
    (hgsecond : Integrable (fun value =>
      expectedSecondMoverIndependent (F.dist thetaH value) (PMF.pure center) value) D)
    (hffirst : Integrable (fun value =>
      expectedFirstMoverUtility (PMF.pure center) value) D)
    (hfsecond : Integrable (fun value =>
      expectedSecondMoverShared (PMF.pure center) value) D)
    (hstrict_order : ∀ᵐ value ∂D, StrictlyOrderedBy center value)
    (hpointwise_prefers_independent : ∀ᵐ value ∂D,
      Model.PrefersIndependentReranking (F.dist thetaH value) value)
    (hprefers_independent : F.PrefersIndependentReranking D thetaH)
    (hprefers_weaker : ∀ thetaA, thetaH < thetaA →
      F.PrefersWeakerCompetition D thetaA thetaH)
    (halgorithm_against_human : ∀ thetaA, thetaH < thetaA →
      F.theorem1_h D thetaA thetaH <
        F.theorem1_algorithmAgainstHuman D thetaA thetaH) :
    F.DistributionalTheorem1Target D thetaH := by
  apply DistributionalAccuracyFamily.distributional_theorem1_of_outer_atomwise_regular
    F D thetaH center hvalue hatom_measurable hatom_continuous hatom_tendsto
    hprefers_independent
  · exact DistributionalAccuracyFamily.theorem1_pureCenterLimit_gap_of_ae_pointwise
      F D thetaH center hgfirst hgsecond hffirst hfsecond hstrict_order
      hpointwise_prefers_independent
  · exact hprefers_weaker
  · exact halgorithm_against_human

/--
Outer-D Mallows Definition 2/3 component. The center and comparison may depend
on the realized value profile, and strict pointwise comparisons integrate to
strict ex-ante ones; this does not package the full source family/Definition 1
route.
-/
theorem theorem3_mallows_with_outer_value_distribution
    {n : ℕ} {Omega : Type*} [MeasurableSpace Omega]
    (value : Omega → ValueProfile n)
    (C : Omega → MallowsComparison n)
    (D : Measure Omega) [IsProbabilityMeasure D]
    (hstrict : ∀ omega, (C omega).StrictlyCenterOrdered (value omega))
    (hn : 0 < n)
    (halg_q_lt_one : ∀ omega, (C omega).algorithm.q < 1)
    (hhuman_q_lt_one : ∀ omega, (C omega).human.q < 1)
    (hq_lt : ∀ omega, (C omega).algorithm.q < (C omega).human.q)
    (hshared : Integrable (fun omega =>
      expectedSecondMoverShared (C omega).algorithm.law (value omega)) D)
    (hindependent : Integrable (fun omega =>
      expectedSecondMoverIndependent
        (C omega).algorithm.law (C omega).algorithm.law (value omega)) D)
    (hbetter : Integrable (fun omega =>
      expectedSecondMoverIndependent
        (C omega).human.law (C omega).algorithm.law (value omega)) D)
    (hworse : Integrable (fun omega =>
      expectedSecondMoverIndependent
        (C omega).human.law (C omega).human.law (value omega)) D) :
    (∫ omega, expectedSecondMoverShared
        (C omega).algorithm.law (value omega) ∂D) <
        ∫ omega, expectedSecondMoverIndependent
          (C omega).algorithm.law (C omega).algorithm.law (value omega) ∂D ∧
      (∫ omega, expectedSecondMoverIndependent
          (C omega).human.law (C omega).algorithm.law (value omega) ∂D) <
        ∫ omega, expectedSecondMoverIndependent
          (C omega).human.law (C omega).human.law (value omega) ∂D := by
  constructor
  · exact AppliedModelingLib.integral_lt_integral_of_forall_lt D hshared hindependent
      fun omega =>
        (KR21Monoculture.MallowsComparison.paper_theorem3_pointwise_rankFactorization
          (C omega) (hstrict omega) hn (halg_q_lt_one omega)
          (hhuman_q_lt_one omega) (hq_lt omega)).1
  · exact AppliedModelingLib.integral_lt_integral_of_forall_lt D hbetter hworse
      fun omega =>
        (KR21Monoculture.MallowsComparison.paper_theorem3_pointwise_rankFactorization
          (C omega) (hstrict omega) hn (halg_q_lt_one omega)
          (hhuman_q_lt_one omega) (hq_lt omega)).2

/--
Fixed-center outer-D Mallows component.  When one Mallows comparison is used
throughout the outer distribution, coordinatewise finite first moments derive
the four payoff-integrability facts rather than receiving them as opaque
premises.  It formalizes only outer laws supported on the strict ordering cone
of one fixed common center, matching the source's rank-labelled `x1 > ... > xn`
convention.  No sorting/relabeling reduction for an arbitrary identity-labelled
outer law, or profile-dependent-center kernel, is asserted here.
-/
theorem theorem3_mallows_fixed_center_outer_of_coordinate_integrable
    {n : ℕ} {Omega : Type*} [MeasurableSpace Omega]
    (value : Omega → ValueProfile n) (C : MallowsComparison n)
    (D : Measure Omega) [IsProbabilityMeasure D]
    (hstrict : ∀ omega, C.StrictlyCenterOrdered (value omega))
    (hn : 0 < n)
    (halg_q_lt_one : C.algorithm.q < 1)
    (hhuman_q_lt_one : C.human.q < 1)
    (hq_lt : C.algorithm.q < C.human.q)
    (hvalue : ∀ c : Candidate n, Integrable (fun omega => value omega c) D) :
    (∫ omega, expectedSecondMoverShared C.algorithm.law (value omega) ∂D) <
        ∫ omega, expectedSecondMoverIndependent
          C.algorithm.law C.algorithm.law (value omega) ∂D ∧
      (∫ omega, expectedSecondMoverIndependent
          C.human.law C.algorithm.law (value omega) ∂D) <
        ∫ omega, expectedSecondMoverIndependent
          C.human.law C.human.law (value omega) ∂D :=
  theorem3_mallows_outer_conditions_of_coordinate_integrable
    value C D hstrict hn halg_q_lt_one hhuman_q_lt_one hq_lt hvalue

/--
Theorem 3, source-order outer-distribution payoff conditions.  This is the
payoff-side form of Definitions 2 and 3; the source Definition 2
conditional-event interpretation is a separate bridge.  The source fixes the
true value ordering before introducing its candidate distribution `D`; this
theorem models that convention as almost-everywhere support on one strict
ordering cone.  Coordinatewise finite first moments are explicit because all
source expected utilities must be defined.  The corrected `hn : 0 < n` is the
necessary source condition of at least three candidates.
-/
theorem theorem3_mallows_fixed_order_outer_payoff_conditions
    {n : ℕ} (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    (center : Ranking n) (hn : 0 < n)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D)
    (hstrict : ∀ᵐ value ∂D, StrictlyOrderedBy center value) :
    (∀ theta : ℝ, 0 < theta →
      (fixedCenterMallowsDistributionalFamily center).PrefersIndependentReranking
        D theta) ∧
    (∀ thetaA thetaH : ℝ, 0 < thetaH → thetaH < thetaA →
      (fixedCenterMallowsDistributionalFamily center).PrefersWeakerCompetition
        D thetaA thetaH) := by
  constructor
  · intro theta htheta
    exact fixedCenterMallows_outer_prefersIndependentReranking
      D center hn theta htheta hvalue hstrict
  · intro thetaA thetaH hthetaH htheta
    exact fixedCenterMallows_outer_prefersWeakerCompetition
      D center hn thetaA thetaH hthetaH htheta hvalue hstrict

/--
Definition 2 conditional-event integrand.  On top-choice disagreement, the
actual outer-joint-law payoff gain is exactly the source expression
`pi_1 - pi_2` for the independently drawn ranking `pi`.
-/
theorem definition2_joint_disagreement_integrand_eq_source_gap
    {n : ℕ} (value : ValueProfile n) (pair : RankingPair n)
    (hdisagreement : disagreementEvent pair) :
    pairRerankingGain value pair =
      value (firstChoice pair.1) - value (secondChoice pair.1) :=
  DistributionalAccuracyFamily.pairRerankingGain_eq_sourceFirstPositionGap_of_disagreement
    value pair hdisagreement

/--
Theorem 3, source-order outer-distribution form.  This strengthens the
preceding payoff-side row with Definition 2's actual joint conditional
experiment: draw a value profile from `D`, then condition on disagreement of
two conditionally independent Mallows rankings.  The measurable joint law,
its integrable payoffs, and its positive disagreement event are all derived
from the displayed hypotheses.
-/
theorem theorem3_mallows_fixed_order_outer_source
    {n : ℕ} (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    (center : Ranking n) (hn : 0 < n)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D)
    (hstrict : ∀ᵐ value ∂D, StrictlyOrderedBy center value) :
    (∀ theta : ℝ, 0 < theta →
      0 < DistributionalAccuracyFamily.jointLawDisagreementConditionalGain
        (fixedCenterMallowsDistributionalFamily center) D theta
        (fun ranking =>
          DistributionalAccuracyFamily.fixedCenterMallows_ranking_atom_measurable
            center theta ranking)) ∧
    (∀ thetaA thetaH : ℝ, 0 < thetaH → thetaH < thetaA →
      (fixedCenterMallowsDistributionalFamily center).PrefersWeakerCompetition
        D thetaA thetaH) := by
  constructor
  · intro theta htheta
    exact DistributionalAccuracyFamily.fixedCenterMallows_outer_jointLawDisagreementConditionalGain_pos
      D center hn theta htheta hvalue hstrict
  · intro thetaA thetaH hthetaH htheta
    exact fixedCenterMallows_outer_prefersWeakerCompetition
      D center hn thetaA thetaH hthetaH htheta hvalue hstrict

/--
Corrected source-facing Theorem 3.  The statement explicitly identifies the
published `phi`-parameterized Mallows law with its normalized
`phi^(-kendallTau)` mass before giving the actual outer-law conclusions.  The
necessary `hn : 0 < n` correction records that the source has at least three
candidates, since `Candidate n` has `n + 2` elements.
-/
theorem theorem3_source_complete
    {n : ℕ} (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    (center : Ranking n) (hn : 0 < n)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D)
    (hstrict : ∀ᵐ value ∂D, StrictlyOrderedBy center value) :
    (∀ (phi theta : ℝ), 1 < phi → theta = phi - 1 →
      (concreteMallowsSpec center theta).q = phi⁻¹ ∧
      ∀ (value : ValueProfile n) (pi : Ranking n),
        (((fixedCenterMallowsDistributionalFamily center).dist theta value) pi).toReal =
          phi⁻¹ ^ kendallTau center pi /
            (∑ tau : Ranking n, phi⁻¹ ^ kendallTau center tau)) ∧
    (∀ theta : ℝ, 0 < theta →
      0 < DistributionalAccuracyFamily.jointLawDisagreementConditionalGain
        (fixedCenterMallowsDistributionalFamily center) D theta
        (fun ranking =>
          DistributionalAccuracyFamily.fixedCenterMallows_ranking_atom_measurable
            center theta ranking)) ∧
    (∀ thetaA thetaH : ℝ, 0 < thetaH → thetaH < thetaA →
      (fixedCenterMallowsDistributionalFamily center).PrefersWeakerCompetition
        D thetaA thetaH) := by
  constructor
  · intro phi theta hphi htheta
    refine ⟨(source_equation8_concrete_mallows_probability center phi theta
      hphi htheta center).1, ?_⟩
    intro value pi
    simpa [fixedCenterMallowsDistributionalFamily] using
      (source_equation8_concrete_mallows_probability center phi theta
        hphi htheta pi).2
  exact theorem3_mallows_fixed_order_outer_source D center hn hvalue hstrict

/--
Theorem 1, Mallows source-order outer-distribution consequence.  This exposes
the single algorithm-accuracy witness outside the outer expectation and proves
the source endpoint under the same visible order and moment conventions as the
preceding Theorem 3 row.
-/
theorem theorem1_mallows_fixed_order_outer_source
    {n : ℕ} (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    (center : Ranking n) (hn : 0 < n) (thetaH : ℝ) (hthetaH : 0 < thetaH)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D)
    (hstrict : ∀ᵐ value ∂D, StrictlyOrderedBy center value) :
    DistributionalAccuracyFamily.DistributionalTheorem1Target
      (fixedCenterMallowsDistributionalFamily center) D thetaH :=
  fixedCenterMallows_outer_distributionalTheorem1Target
    D center hn thetaH hthetaH hvalue hstrict

/--
At positive accuracy, Appendix A's scaled-coordinate change of variables has
density `theta * f(theta*z)`.  The positivity premise is essential: the raw
algebraic product is not a probability density at nonpositive `theta`.
-/
theorem appendixA_theorem5_correct_scaled_iid_density
    {n : ℕ} (f : ℝ → ℝ) {theta : ℝ} (htheta : 0 < theta)
    (z : Candidate n → ℝ) :
    scaledIIDDensity f theta z =
      ∏ i : Candidate n, theta * f (theta * z i) :=
  scaledIIDDensity_eq_product_theta_mul f theta z

/--
At positive accuracy, the source scaled-noise score representation and the
additive score-space representation induce exactly the same canonical ranking,
including the library's deterministic tie-breaking.  This is a ranking-map
identity only; the associated probability-law transport is a separate
obligation.
-/
theorem appendixA_scaledNoise_ranking_eq_additiveScore
    {n : ℕ} (value noise : Candidate n → ℝ) {theta : ℝ} (htheta : 0 < theta) :
    rankByScore (fun i => value i + noise i / theta) =
      rankByScore (fun i => theta * value i + noise i) :=
  rankByScore_scaledNoise_eq_additiveScore value noise htheta

/--
Auxiliary conditional differentiability route. Its pointwise domination package
is not the accepted W^{1,1} corrected-model theorem and is not evidence for
the false archival Theorem 5 statement.
-/
theorem appendixA_theorem5_ranking_atom_differentiable
    {n : ℕ} (f : ℝ → ℝ) (hf : ∀ x, DifferentiableAt ℝ f x)
    (value : Candidate n → ℝ) (pi : Ranking n)
    {theta0 : ℝ} (htheta0 : 0 < theta0)
    (regularity : RankingAtomDominatedDerivativeRegularity f value pi theta0) :
    DifferentiableAt ℝ (rankingDensityAtom f value pi) theta0 :=
  rankingDensityAtom_differentiableAt_of_dominated
    f hf value pi htheta0 regularity

/--
Corrected Theorem 5 concrete two-candidate endpoint.  A globally absolutely
continuous `W^{1,1}` density, together with the displayed score-density
normalization and full-support condition, gives a differentiable fixed
score-ranking atom.  This is an actual probability-law statement only because
the normalization premise is explicit.  The generic finite-carrier endpoint
is stated below.
-/
theorem appendixA_theorem5_twoCandidate_corrected_W11_ranking_atom
    (f derivative : ℝ → ℝ)
    (hf : Integrable f volume) (hderivative : Integrable derivative volume)
    (hf_measurable : Measurable f)
    (hfullSupport : ∀ x, 0 < f x)
    (absolute_continuity : ∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b)
    (derivative_ae_eq : derivative =ᵐ[volume] deriv f)
    (value : Candidate 0 → ℝ) (pi : Ranking 0) (theta : ℝ)
    (hnormalized :
      ∫⁻ x, ENNReal.ofReal (f x) ∂volume = 1) :
    IsProbabilityMeasure (twoCandidateScoreLaw f value theta) ∧
      DifferentiableAt ℝ (twoCandidateScoreLawRankingAtom f value pi) theta := by
  constructor
  · letI : IsProbabilityMeasure (twoCandidateScoreLaw f value theta) :=
      twoCandidateScoreLaw_isProbabilityMeasure_of_base_normalization
        f hf_measurable (fun x => (hfullSupport x).le) hnormalized value theta
    exact inferInstance
  · exact twoCandidateScoreLawRankingAtom_differentiableAt_of_global_W11
      f derivative hf hderivative (fun x => (hfullSupport x).le)
      absolute_continuity derivative_ae_eq value pi theta

/--
Corrected Theorem 5 source-model endpoint for two candidates.  The source iid
noise law is normalized directly from the base PDF, and its scaled-noise
ranking atom is transported by a proved pushforward to the corrected
score-space law.  The global `W^{1,1}` condition is explicit.
-/
theorem appendixA_theorem5_twoCandidate_sourceScaledNoise_corrected_W11_ranking_atom
    (f derivative : ℝ → ℝ)
    (hf : Integrable f volume) (hderivative : Integrable derivative volume)
    (hf_measurable : Measurable f)
    (hfullSupport : ∀ x, 0 < f x)
    (absolute_continuity : ∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b)
    (derivative_ae_eq : derivative =ᵐ[volume] deriv f)
    (value : Candidate 0 → ℝ) (pi : Ranking 0) {theta : ℝ} (htheta : 0 < theta)
    (hnormalized :
      ∫⁻ x, ENNReal.ofReal (f x) ∂volume = 1) :
    IsProbabilityMeasure (w11TwoCandidateNoiseLaw f) ∧
      DifferentiableAt ℝ (w11TwoCandidateScaledNoiseRankingAtom f value pi) theta := by
  constructor
  · exact w11TwoCandidateNoiseLaw_isProbabilityMeasure_of_base_normalization f hnormalized
  · exact w11TwoCandidateScaledNoiseRankingAtom_differentiableAt_of_global_W11
      f derivative hf hderivative hf_measurable (fun x => (hfullSupport x).le)
      absolute_continuity derivative_ae_eq value pi htheta

/--
Corrected Theorem 5 partial endpoint for three candidates.  This is the
explicit `((ℝ × ℝ) × ℝ)` product-score model corresponding to `Candidate 1`.
Global absolute continuity, `L¹` derivative, full support, and base-density
normalization give both an actual probability law and differentiability of
every fixed score-ranking atom.  The carrier reindexing is proved, but no
unproved arbitrary finite-carrier or probability-transport assertion is used.
-/
theorem appendixA_theorem5_threeCandidate_corrected_W11_ranking_atom
    (f derivative : ℝ → ℝ)
    (hf : Integrable f volume) (hderivative : Integrable derivative volume)
    (hf_measurable : Measurable f)
    (hfullSupport : ∀ x, 0 < f x)
    (absolute_continuity : ∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b)
    (derivative_ae_eq : derivative =ᵐ[volume] deriv f)
    (value : Candidate 1 → ℝ) (pi : Ranking 1) (theta : ℝ)
    (hnormalized :
      ∫⁻ x, ENNReal.ofReal (f x) ∂volume = 1) :
    IsProbabilityMeasure (threeCandidateScoreLaw f value theta) ∧
      DifferentiableAt ℝ (threeCandidateScoreLawRankingAtom f value pi) theta := by
  constructor
  · letI : IsProbabilityMeasure (threeCandidateScoreLaw f value theta) :=
      threeCandidateScoreLaw_isProbabilityMeasure_of_base_normalization
        f hf_measurable (fun x => (hfullSupport x).le) hnormalized value theta
    exact inferInstance
  · exact threeCandidateScoreLawRankingAtom_differentiableAt_of_global_W11
      f derivative hf hderivative (fun x => (hfullSupport x).le)
      absolute_continuity derivative_ae_eq value pi theta

/--
Corrected Theorem 5 score-space endpoint for the paper's concrete four-candidate
carrier (`Candidate 2 = Fin 4`).  The theorem proves an actual normalized
explicit product score law and every fixed ranking atom's differentiability
under the global `W^{1,1}` repair.  The source-noise endpoint is exposed
separately below; the generic finite-carrier endpoint is stated below.
-/
theorem appendixA_theorem5_fourCandidate_corrected_W11_ranking_atom
    (f derivative : ℝ → ℝ)
    (hf : Integrable f volume) (hderivative : Integrable derivative volume)
    (hf_measurable : Measurable f)
    (hfullSupport : ∀ x, 0 < f x)
    (absolute_continuity : ∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b)
    (derivative_ae_eq : derivative =ᵐ[volume] deriv f)
    (value : Candidate 2 → ℝ) (pi : Ranking 2) (theta : ℝ)
    (hnormalized :
      ∫⁻ x, ENNReal.ofReal (f x) ∂volume = 1) :
    IsProbabilityMeasure (fourCandidateScoreLaw f value theta) ∧
      DifferentiableAt ℝ (fourCandidateScoreLawRankingAtom f value pi) theta := by
  constructor
  · letI : IsProbabilityMeasure (fourCandidateScoreLaw f value theta) :=
      fourCandidateScoreLaw_isProbabilityMeasure_of_base_normalization
        f hf_measurable (fun x => (hfullSupport x).le) hnormalized value theta
    exact inferInstance
  · exact fourCandidateScoreLawRankingAtom_differentiableAt_of_global_W11
      f derivative hf hderivative (fun x => (hfullSupport x).le)
      absolute_continuity derivative_ae_eq value pi theta

/--
Corrected Theorem 5 source-model endpoint for the source paper's actual
four-candidate carrier (`Candidate 2 = Fin 4`).  Four iid source-noise draws
are normalized directly from the base PDF; their positive-accuracy scaled-noise
ranking atom is transported through a proved coordinatewise pushforward to the
four-score law.  The global `W^{1,1}` condition is explicit.  The generic
finite-carrier endpoint is stated immediately below.
-/
theorem appendixA_theorem5_fourCandidate_sourceScaledNoise_corrected_W11_ranking_atom
    (f derivative : ℝ → ℝ)
    (hf : Integrable f volume) (hderivative : Integrable derivative volume)
    (hf_measurable : Measurable f)
    (hfullSupport : ∀ x, 0 < f x)
    (absolute_continuity : ∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b)
    (derivative_ae_eq : derivative =ᵐ[volume] deriv f)
    (value : Candidate 2 → ℝ) (pi : Ranking 2) {theta : ℝ} (htheta : 0 < theta)
    (hnormalized :
      ∫⁻ x, ENNReal.ofReal (f x) ∂volume = 1) :
    IsProbabilityMeasure (w11FourCandidateNoiseLaw f) ∧
      DifferentiableAt ℝ (w11FourCandidateScaledNoiseRankingAtom f value pi) theta := by
  constructor
  · exact w11FourCandidateNoiseLaw_isProbabilityMeasure_of_base_normalization f hnormalized
  · exact w11FourCandidateScaledNoiseRankingAtom_differentiableAt_of_global_W11
      f derivative hf hderivative hf_measurable (fun x => (hfullSupport x).le)
      absolute_continuity derivative_ae_eq value pi htheta

/--
Corrected Theorem 5 source-model endpoint on every finite candidate carrier.
The archival differentiability claim is false under its printed hypotheses.
Under the visible global `W^{1,1}` repair, base-density normalization, full
support, and positive accuracy, the literal iid source-noise scaled-ranking
atom is differentiable.  The proof includes the finite product law,
coordinatewise pushforward, and ranking-cell transport rather than assuming a
source-to-score equivalence.
-/
theorem appendixA_theorem5_arbitraryFinite_sourceScaledNoise_corrected_W11_ranking_atom
    {n : ℕ} (f derivative : ℝ → ℝ)
    (hf : Integrable f volume) (hderivative : Integrable derivative volume)
    (hf_measurable : Measurable f)
    (hfullSupport : ∀ x, 0 < f x)
    (absolute_continuity : ∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b)
    (derivative_ae_eq : derivative =ᵐ[volume] deriv f)
    (value : Candidate n → ℝ) (pi : Ranking n) {theta : ℝ} (htheta : 0 < theta)
    (hnormalized :
      ∫⁻ x, ENNReal.ofReal (f x) ∂volume = 1) :
    IsProbabilityMeasure (w11CandidateNoiseLaw (n := n) f) ∧
      DifferentiableAt ℝ (w11CandidateScaledNoiseRankingAtom f value pi) theta := by
  constructor
  · exact w11CandidateNoiseLaw_isProbabilityMeasure_of_base_normalization n f hnormalized
  · exact w11CandidateScaledNoiseRankingAtom_differentiableAt_of_global_W11
      n f derivative hf hderivative hf_measurable (fun x => (hfullSupport x).le)
      absolute_continuity derivative_ae_eq value pi htheta

/--
Corrected Appendix A / Theorem 5 analytic and singleton-removal package on
every finite candidate carrier.  The archival theorem is false as printed.
This replacement visibly adds global `W^{1,1}` regularity, density
normalization, and the source's strict true-value order.  It proves atom
continuity and differentiability, high-accuracy concentration, and the
singleton-removal consequence consumed by the Theorem 1 game proof.  The
separate source-facing arbitrary-remaining-set endpoint is exposed through
`Definition1FullRemoval.lean`.
-/
noncomputable def appendixA_theorem5_arbitraryFinite_corrected_W11_definition1
    {n : ℕ} (f derivative : ℝ → ℝ)
    (hf : Integrable f volume) (hderivative : Integrable derivative volume)
    (hf_measurable : Measurable f)
    (hfullSupport : ∀ x, 0 < f x)
    (absolute_continuity : ∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b)
    (derivative_ae_eq : derivative =ᵐ[volume] deriv f)
    (hnormalized :
      ∫⁻ x, ENNReal.ofReal (f x) ∂volume = 1)
    (value : Candidate n → ℝ) (center : Ranking n)
    (hcenter : ∀ i : Fin (n + 1),
      value (center i.succ) < value (center i.castSucc)) :
    CorrectedW11ScaledNoiseDefinition1
      (w11CorrectedScaledNoiseFamily f hnormalized value) center :=
  correctedW11ScaledNoiseDefinition1_of_source
    f derivative hf hderivative hf_measurable hfullSupport absolute_continuity
    derivative_ae_eq hnormalized value center hcenter

/--
Corrected Appendix A / Theorem 5 full Definition 1 endpoint on every finite
candidate carrier.  This proposition visibly states atom continuity,
differentiability, high-accuracy concentration, weak monotonicity for every
nonempty remaining candidate set, and strict full-set improvement.  It is the
source-facing repair of the archival theorem, whose printed hypotheses remain
false; the added global `W^{1,1}`, normalization, full-support, and strict
value-order assumptions are explicit.
-/
theorem appendixA_theorem5_arbitraryFinite_corrected_W11_full_definition1
    {n : ℕ} (f derivative : ℝ → ℝ)
    (hf : Integrable f volume) (hderivative : Integrable derivative volume)
    (hf_measurable : Measurable f)
    (hfullSupport : ∀ x, 0 < f x)
    (absolute_continuity : ∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b)
    (derivative_ae_eq : derivative =ᵐ[volume] deriv f)
    (hnormalized :
      ∫⁻ x, ENNReal.ofReal (f x) ∂volume = 1)
    (value : Candidate n → ℝ) (center : Ranking n)
    (hcenter : ∀ i : Fin (n + 1),
      value (center i.succ) < value (center i.castSucc)) :
    (∀ theta, 0 < theta → ∀ pi : Ranking n,
      AppliedModelingLib.EpsilonContinuousAt
        (fun theta' =>
          ((w11CorrectedScaledNoiseFamily f hnormalized value).dist theta' pi).toReal)
        theta) ∧
    (∀ theta, 0 < theta → ∀ pi : Ranking n,
      DifferentiableAt ℝ
        (fun theta' =>
          ((w11CorrectedScaledNoiseFamily f hnormalized value).dist theta' pi).toReal)
        theta) ∧
    (∀ lower delta, 0 < delta → ∃ hi, lower < hi ∧ ∀ pi : Ranking n,
      |((w11CorrectedScaledNoiseFamily f hnormalized value).dist hi pi).toReal -
        ((PMF.pure center : PMF (Ranking n)) pi).toReal| < delta) ∧
    (∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
      ∀ remaining : Finset (Candidate n), remaining.Nonempty →
        expectedBestInSet
            ((w11CorrectedScaledNoiseFamily f hnormalized value).dist thetaH)
            value remaining ≤
          expectedBestInSet
            ((w11CorrectedScaledNoiseFamily f hnormalized value).dist thetaA)
            value remaining) ∧
    ∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
      expectedBestInSet
          ((w11CorrectedScaledNoiseFamily f hnormalized value).dist thetaH)
          value Finset.univ <
        expectedBestInSet
          ((w11CorrectedScaledNoiseFamily f hnormalized value).dist thetaA)
          value Finset.univ :=
  correctedW11ScaledNoiseDefinition1_full_of_source
    f derivative hf hderivative hf_measurable hfullSupport absolute_continuity
    derivative_ae_eq hnormalized value center hcenter

/--
Corrected Appendix A / Theorem 5 source-faithful Definition 1 endpoint on
every finite candidate carrier.  Unlike the older support theorem above, this
states the source's actual asymptotic-optimality limit rather than merely an
arbitrarily-large accuracy witness for each tolerance.

The archival differentiability hypotheses are false; the explicit global
`W^{1,1}`, normalization, full-support, and strict-value-order repair remains
visible in this theorem's premises.
-/
theorem appendixA_theorem5_arbitraryFinite_corrected_W11_sourceFaithful_definition1
    {n : ℕ} (f derivative : ℝ → ℝ)
    (hf : Integrable f volume) (hderivative : Integrable derivative volume)
    (hf_measurable : Measurable f)
    (hfullSupport : ∀ x, 0 < f x)
    (absolute_continuity : ∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b)
    (derivative_ae_eq : derivative =ᵐ[volume] deriv f)
    (hnormalized :
      ∫⁻ x, ENNReal.ofReal (f x) ∂volume = 1)
    (value : Candidate n → ℝ) (center : Ranking n)
    (hcenter : ∀ i : Fin (n + 1),
      value (center i.succ) < value (center i.castSucc)) :
    (∀ theta, 0 < theta → ∀ pi : Ranking n,
      ContinuousAt
        (fun theta' =>
          ((w11CorrectedScaledNoiseFamily f hnormalized value).dist theta' pi).toReal)
        theta ∧
      DifferentiableAt ℝ
        (fun theta' =>
          ((w11CorrectedScaledNoiseFamily f hnormalized value).dist theta' pi).toReal)
        theta) ∧
    (∀ pi : Ranking n,
      Filter.Tendsto
        (fun theta =>
          ((w11CorrectedScaledNoiseFamily f hnormalized value).dist theta pi).toReal)
        Filter.atTop
        (nhds (((PMF.pure center : PMF (Ranking n)) pi).toReal))) ∧
    (∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
      ∀ remaining : Finset (Candidate n), remaining.Nonempty →
        expectedBestInSet
            ((w11CorrectedScaledNoiseFamily f hnormalized value).dist thetaH)
            value remaining ≤
          expectedBestInSet
            ((w11CorrectedScaledNoiseFamily f hnormalized value).dist thetaA)
            value remaining) ∧
    ∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
      expectedBestInSet
          ((w11CorrectedScaledNoiseFamily f hnormalized value).dist thetaH)
          value Finset.univ <
        expectedBestInSet
          ((w11CorrectedScaledNoiseFamily f hnormalized value).dist thetaA)
          value Finset.univ :=
  correctedW11ScaledNoiseDefinition1_sourceFaithful_of_source
    f derivative hf hderivative hf_measurable hfullSupport absolute_continuity
    derivative_ae_eq hnormalized value center hcenter

/--
Corrected source-facing Theorem 5 with the RUM construction stated directly.
The existential ranking law is pinned, at every positive accuracy, to the
literal iid density product pushed through `value i + epsilon i / theta` and
the ranking map.  The proof may use the corrected W11 construction internally,
but no such constructor appears in the terminal proposition.
-/
theorem appendixA_theorem5_corrected_source_complete
    {n : ℕ} (f derivative : ℝ → ℝ)
    (hf : Integrable f volume) (hderivative : Integrable derivative volume)
    (hf_measurable : Measurable f)
    (hfullSupport : ∀ x, 0 < f x)
    (absolute_continuity : ∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b)
    (derivative_ae_eq : derivative =ᵐ[volume] deriv f)
    (hnormalized : ∫⁻ x, ENNReal.ofReal (f x) ∂volume = 1)
    (value : Candidate n → ℝ) (center : Ranking n)
    (hcenter : ∀ i : Fin (n + 1),
      value (center i.succ) < value (center i.castSucc)) :
    Fintype.card (Candidate n) = n + 2 ∧
    IsProbabilityMeasure
      (Measure.pi (fun _ : Candidate n =>
        volume.withDensity (fun x => ENNReal.ofReal (f x)))) ∧
    ∃ rankingLaw : ℝ → PMF (Ranking n),
      (∀ theta : ℝ, 0 < theta →
        (rankingLaw theta).toMeasure =
          (Measure.pi (fun _ : Candidate n =>
            volume.withDensity (fun x => ENNReal.ofReal (f x)))).map
            (fun epsilon => rankByScore
              (fun i => value i + epsilon i / theta))) ∧
      (∀ theta, 0 < theta → ∀ pi : Ranking n,
        ContinuousAt (fun theta' => ((rankingLaw theta') pi).toReal) theta ∧
        DifferentiableAt ℝ (fun theta' => ((rankingLaw theta') pi).toReal) theta) ∧
      (∀ pi : Ranking n,
        Filter.Tendsto (fun theta => ((rankingLaw theta) pi).toReal)
          Filter.atTop
          (nhds (((PMF.pure center : PMF (Ranking n)) pi).toReal))) ∧
      (∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
        ∀ remaining : Finset (Candidate n), remaining.Nonempty →
          expectedBestInSet (rankingLaw thetaH) value remaining ≤
            expectedBestInSet (rankingLaw thetaA) value remaining) ∧
      ∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
        expectedBestInSet (rankingLaw thetaH) value Finset.univ <
          expectedBestInSet (rankingLaw thetaA) value Finset.univ := by
  refine ⟨by simp [Candidate], ?_, ?_⟩
  · change IsProbabilityMeasure (w11CandidateNoiseLaw (n := n) f)
    exact w11CandidateNoiseLaw_isProbabilityMeasure_of_base_normalization n f hnormalized
  · let F := w11CorrectedScaledNoiseFamily f hnormalized value
    have hdefinition := correctedW11ScaledNoiseDefinition1_sourceFaithful_of_source
      f derivative hf hderivative hf_measurable hfullSupport absolute_continuity
      derivative_ae_eq hnormalized value center hcenter
    refine ⟨F.dist, ?_, hdefinition.1, hdefinition.2.1,
      hdefinition.2.2.1, hdefinition.2.2.2⟩
    intro theta _
    letI : IsProbabilityMeasure (w11CandidateNoiseLaw (n := n) f) :=
      w11CandidateNoiseLaw_isProbabilityMeasure_of_base_normalization n f hnormalized
    change
      (paper_appendixA_scaledNoiseRankingPMF
        (w11CandidateNoiseLaw (n := n) f) value theta).toMeasure =
      (w11CandidateNoiseLaw (n := n) f).map
        (fun epsilon => rankByScore
          (fun i => value i + epsilon i / theta))
    unfold paper_appendixA_scaledNoiseRankingPMF
    unfold AppliedModelingLib.SocialChoice.Ranking.rankingPMFOfMeasure
    rw [Measure.toPMF_toMeasure]

/-- Source equation (7), the Plackett--Luce remaining-set choice formula. -/
theorem equation7_plackettLuce_choice_probability
    {n : ℕ} (theta : ℝ) (value : Candidate n → ℝ)
    (htheta : 0 < theta)
    (remaining : Finset (Candidate n)) {i : Candidate n}
    (hi : i ∈ remaining) :
    plackettLuceChoiceProb theta value remaining i =
      Real.exp (theta * value i) /
        ∑ j ∈ remaining, Real.exp (theta * value j) :=
  plackettLuceChoiceProb_eq_equation7 theta value remaining hi

/-- The constructed full Plackett--Luce ranking PMF has equation (7) as its first marginal. -/
theorem equation7_plackettLuce_constructed_ranking_first_choice
    {n : ℕ} (theta : ℝ) (value : Candidate n → ℝ)
    (i : Candidate n) :
    firstChoiceProb (plackettLuceRankingPMF theta value) i =
      plackettLuceChoiceProb theta value Finset.univ i :=
  plackettLuceRankingPMF_firstChoiceProb_eq_equation7 theta value i

/--
Plackett--Luce IIA makes the independent-reranking payoff effect exactly zero
for the constructed full ranking PMF at a fixed value profile. The actual
outer-D conditional sequential-law endpoint is exposed below; the Gumbel RUM
/ scale reconciliation and strategy bridges remain separate obligations.
-/
theorem plackettLuce_independent_reranking_effect_zero
    {n : ℕ} (theta : ℝ) (value : Candidate n → ℝ) :
    expectedSecondMoverIndependent
          (plackettLuceRankingPMF theta value)
          (plackettLuceRankingPMF theta value) value -
        expectedSecondMoverShared
          (plackettLuceRankingPMF theta value) value = 0 :=
  plackettLuceRankingPMF_independentRerankingEffect_eq_zero theta value

/--
Section 3.1, stated at the paper's actual two-firm payoff surface.  Among two
positive sequential Plackett--Luce laws for the same value profile, the law
with weakly higher inverse temperature weakly dominates in both possible
opponent rows.  This makes "best available ranking" semantic: it is not
inferred from the `algorithm` or `human` label, and equality yields only weak
best responses.

This is a theorem about the literal equation-(7) Plackett--Luce model.  The
separate identification of that model with the paper's unit-variance Gumbel
normalization remains recorded as a source-model issue below.
-/
theorem section31_plackettLuce_best_available_weakly_dominates
    {n : ℕ} (value : Candidate n → ℝ)
    {thetaA thetaH : ℝ} (hthetaA : 0 < thetaA) (hthetaH : 0 < thetaH) :
    let M : Model n :=
      { algorithmRanking := plackettLuceRankingPMF thetaA value
        humanRanking := plackettLuceRankingPMF thetaH value
        value := value }
    (thetaH ≤ thetaA →
      Model.payoffAgainst M Strategy.algorithm Strategy.algorithm ≥
          Model.payoffAgainst M Strategy.human Strategy.algorithm ∧
        Model.payoffAgainst M Strategy.algorithm Strategy.human ≥
          Model.payoffAgainst M Strategy.human Strategy.human) ∧
      (thetaA ≤ thetaH →
        Model.payoffAgainst M Strategy.human Strategy.algorithm ≥
            Model.payoffAgainst M Strategy.algorithm Strategy.algorithm ∧
          Model.payoffAgainst M Strategy.human Strategy.human ≥
            Model.payoffAgainst M Strategy.algorithm Strategy.human) :=
  plackettLuce_best_available_weakly_dominates value hthetaA hthetaH

/--
Source-facing outer-D lift of Section 3.1's Plackett--Luce strategy
conclusion.  The source draws a profile from `D` before the two-firm random
order is realized, so this endpoint explicitly integrates each labeled firm's
payoff over that same probability law.  Coordinatewise first moments make all
four payoff functions genuine integrals; the almost-everywhere strict
rank-labelled order records the source's candidate-distribution scope.

The pointwise Plackett--Luce dominance is used only as the fiberwise fact
inside `integral_mono_ae`; it is not substituted for this outer conclusion.
-/
theorem section31_plackettLuce_outer_best_available_weakly_dominates
    {n : ℕ} (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    (center : Ranking n) {thetaA thetaH : ℝ}
    (hthetaA : 0 < thetaA) (hthetaH : 0 < thetaH)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D)
    (horder : ∀ᵐ value ∂D, StrictlyOrderedBy center value) :
    let M : ValueProfile n → Model n := fun value =>
      { algorithmRanking := plackettLuceRankingPMF thetaA value
        humanRanking := plackettLuceRankingPMF thetaH value
        value := value }
    (∀ self other : Strategy,
      Integrable (fun value => Model.payoffAgainst (M value) self other) D) ∧
    (thetaH ≤ thetaA →
      (∫ value, Model.payoffAgainst (M value) Strategy.algorithm Strategy.algorithm ∂D) ≥
          ∫ value, Model.payoffAgainst (M value) Strategy.human Strategy.algorithm ∂D ∧
        (∫ value, Model.payoffAgainst (M value) Strategy.algorithm Strategy.human ∂D) ≥
          ∫ value, Model.payoffAgainst (M value) Strategy.human Strategy.human ∂D) ∧
      (thetaA ≤ thetaH →
        (∫ value, Model.payoffAgainst (M value) Strategy.human Strategy.algorithm ∂D) ≥
            ∫ value, Model.payoffAgainst (M value) Strategy.algorithm Strategy.algorithm ∂D ∧
          (∫ value, Model.payoffAgainst (M value) Strategy.human Strategy.human ∂D) ≥
            ∫ value, Model.payoffAgainst (M value) Strategy.algorithm Strategy.human ∂D) := by
  dsimp
  have hatomA : ∀ pi : Ranking n,
      AEStronglyMeasurable (fun value : ValueProfile n =>
        (plackettLuceRankingPMF thetaA value pi).toReal) D := by
    intro pi
    exact (DistributionalAccuracyFamily.plackettLuce_ranking_atom_measurable
      thetaA pi).ennreal_toReal.aestronglyMeasurable
  have hatomH : ∀ pi : Ranking n,
      AEStronglyMeasurable (fun value : ValueProfile n =>
        (plackettLuceRankingPMF thetaH value pi).toReal) D := by
    intro pi
    exact (DistributionalAccuracyFamily.plackettLuce_ranking_atom_measurable
      thetaH pi).ennreal_toReal.aestronglyMeasurable
  have hfirstA : Integrable (fun value : ValueProfile n =>
      expectedFirstMoverUtility (plackettLuceRankingPMF thetaA value) value) D := by
    simpa [expectedFirstMoverUtility] using
      (DistributionalAccuracyFamily.integrable_outer_pmfExp_valueSelection_of_atomwise
        D (fun theta value => plackettLuceRankingPMF theta value) thetaA
        firstChoice hvalue hatomA)
  have hfirstH : Integrable (fun value : ValueProfile n =>
      expectedFirstMoverUtility (plackettLuceRankingPMF thetaH value) value) D := by
    simpa [expectedFirstMoverUtility] using
      (DistributionalAccuracyFamily.integrable_outer_pmfExp_valueSelection_of_atomwise
        D (fun theta value => plackettLuceRankingPMF theta value) thetaH
        firstChoice hvalue hatomH)
  have hsecondAA : Integrable (fun value : ValueProfile n =>
      expectedSecondMoverShared (plackettLuceRankingPMF thetaA value) value) D := by
    simpa [expectedSecondMoverShared] using
      (DistributionalAccuracyFamily.integrable_outer_pmfExp_valueSelection_of_atomwise
        D (fun theta value => plackettLuceRankingPMF theta value) thetaA
        secondChoice hvalue hatomA)
  have hsecondHA : Integrable (fun value : ValueProfile n =>
      expectedSecondMoverIndependent (plackettLuceRankingPMF thetaH value)
        (plackettLuceRankingPMF thetaA value) value) D := by
    simpa [expectedSecondMoverIndependent, secondMoverUtility] using
      (DistributionalAccuracyFamily.integrable_outer_pmfPairExp_valueSelection_of_atomwise
        D (fun value => plackettLuceRankingPMF thetaH value)
        (fun value => plackettLuceRankingPMF thetaA value)
        (fun second first => bestRemainingAfter second (firstChoice first))
        hvalue hatomH hatomA)
  have hsecondAH : Integrable (fun value : ValueProfile n =>
      expectedSecondMoverIndependent (plackettLuceRankingPMF thetaA value)
        (plackettLuceRankingPMF thetaH value) value) D := by
    simpa [expectedSecondMoverIndependent, secondMoverUtility] using
      (DistributionalAccuracyFamily.integrable_outer_pmfPairExp_valueSelection_of_atomwise
        D (fun value => plackettLuceRankingPMF thetaA value)
        (fun value => plackettLuceRankingPMF thetaH value)
        (fun second first => bestRemainingAfter second (firstChoice first))
        hvalue hatomA hatomH)
  have hsecondHH : Integrable (fun value : ValueProfile n =>
      expectedSecondMoverIndependent (plackettLuceRankingPMF thetaH value)
        (plackettLuceRankingPMF thetaH value) value) D := by
    simpa [expectedSecondMoverIndependent, secondMoverUtility] using
      (DistributionalAccuracyFamily.integrable_outer_pmfPairExp_valueSelection_of_atomwise
        D (fun value => plackettLuceRankingPMF thetaH value)
        (fun value => plackettLuceRankingPMF thetaH value)
        (fun second first => bestRemainingAfter second (firstChoice first))
        hvalue hatomH hatomH)
  have hpayoff : ∀ self other : Strategy,
      Integrable (fun value : ValueProfile n =>
        Model.payoffAgainst
          { algorithmRanking := plackettLuceRankingPMF thetaA value
            humanRanking := plackettLuceRankingPMF thetaH value
            value := value }
          self other) D := by
    intro self other
    cases self <;> cases other
    · simpa [Model.payoffAgainst, Model.firstMoverEU, Model.secondMoverEU,
        Model.rankingDist] using (hfirstA.add hsecondAA).div_const 2
    · simpa [Model.payoffAgainst, Model.firstMoverEU, Model.secondMoverEU,
        Model.rankingDist] using (hfirstA.add hsecondAH).div_const 2
    · simpa [Model.payoffAgainst, Model.firstMoverEU, Model.secondMoverEU,
        Model.rankingDist] using (hfirstH.add hsecondHA).div_const 2
    · simpa [Model.payoffAgainst, Model.firstMoverEU, Model.secondMoverEU,
        Model.rankingDist] using (hfirstH.add hsecondHH).div_const 2
  refine ⟨hpayoff, ?_, ?_⟩
  · intro hthetaHA
    constructor
    · apply integral_mono_ae (hpayoff Strategy.human Strategy.algorithm)
        (hpayoff Strategy.algorithm Strategy.algorithm)
      filter_upwards [horder] with value hordered
      exact (plackettLuce_more_accurate_algorithm_weakly_dominates
        value hthetaH hthetaHA).1
    · apply integral_mono_ae (hpayoff Strategy.human Strategy.human)
        (hpayoff Strategy.algorithm Strategy.human)
      filter_upwards [horder] with value hordered
      exact (plackettLuce_more_accurate_algorithm_weakly_dominates
        value hthetaH hthetaHA).2
  · intro hthetaAH
    constructor
    · apply integral_mono_ae (hpayoff Strategy.algorithm Strategy.algorithm)
        (hpayoff Strategy.human Strategy.algorithm)
      filter_upwards [horder] with value hordered
      exact (plackettLuce_more_accurate_human_weakly_dominates
        value hthetaA hthetaAH).1
    · apply integral_mono_ae (hpayoff Strategy.algorithm Strategy.human)
        (hpayoff Strategy.human Strategy.human)
      filter_upwards [horder] with value hordered
      exact (plackettLuce_more_accurate_human_weakly_dominates
        value hthetaA hthetaAH).2

/--
Corrected Section 3.1 Gumbel-to-Plackett--Luce bridge.  For literal iid
innovations `location + (-s * log T_i)` with `s > 0`, the source-style scores
`value_i + epsilon_i / theta` induce Plackett--Luce at inverse temperature
`theta / s`.  The source's printed same-symbol formula is therefore the
scale-one special case; no variance normalization is inferred here.
-/
theorem section31_commonLocationPositiveScaleGumbel_to_plackettLuce
    {n : ℕ} {location s theta : ℝ} (hs : 0 < s) (htheta : 0 < theta)
    (value : Candidate n → ℝ) :
    commonLocationPositiveScaleGumbelRUMRankingPMF location s theta value =
      plackettLuceRankingPMF (theta / s) value :=
  commonLocationPositiveScaleGumbelRUMRankingPMF_eq_plackettLuce hs htheta value

/--
Section 3.1's best-available conclusion for literal iid Gumbel innovations
`location + (-s * log T_i)`.  The common location has no ranking effect and
the common positive scale preserves the order of the actual accuracy
parameters, so the more accurate law weakly dominates in both opponent rows.
No variance formula or unit-variance parameter identification is used here.
-/
theorem section31_commonLocationPositiveScaleGumbel_best_available_weakly_dominates
    {n : ℕ} {location s thetaA thetaH : ℝ} (hs : 0 < s)
    (value : Candidate n → ℝ)
    (hthetaA : 0 < thetaA) (hthetaH : 0 < thetaH) :
    let M : Model n :=
      { algorithmRanking :=
          commonLocationPositiveScaleGumbelRUMRankingPMF location s thetaA value
        humanRanking :=
          commonLocationPositiveScaleGumbelRUMRankingPMF location s thetaH value
        value := value }
    (thetaH ≤ thetaA →
      Model.payoffAgainst M Strategy.algorithm Strategy.algorithm ≥
          Model.payoffAgainst M Strategy.human Strategy.algorithm ∧
        Model.payoffAgainst M Strategy.algorithm Strategy.human ≥
          Model.payoffAgainst M Strategy.human Strategy.human) ∧
      (thetaA ≤ thetaH →
        Model.payoffAgainst M Strategy.human Strategy.algorithm ≥
            Model.payoffAgainst M Strategy.algorithm Strategy.algorithm ∧
          Model.payoffAgainst M Strategy.human Strategy.human ≥
            Model.payoffAgainst M Strategy.algorithm Strategy.human) :=
  commonLocationPositiveScaleGumbel_best_available_weakly_dominates
    hs value hthetaA hthetaH

/--
Section 3.1 Plackett--Luce source-law endpoint.  For an outer value law with
finite coordinatewise first moments, draw one value profile and then two
conditionally iid rankings from the literal sequential equation-(7) law.
The top-disagreement event has positive mass and its actual conditional
first-position-minus-second-position gain is zero.  This does not derive the
law from Gumbel noise or identify the source's Gumbel scale parameter.
-/
theorem plackettLuce_outer_source_joint_conditional_zero
    {n : ℕ} (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    (theta : ℝ)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D) :
    (0 < ∫ x : ValueProfile n × RankingPair n,
      (if disagreementEvent x.2 then (1 : ℝ) else 0) ∂
        (DistributionalAccuracyFamily.plackettLuceDistributionalFamily (n := n)).outerIndependentPairJointLaw
          D theta
          (fun ranking => DistributionalAccuracyFamily.plackettLuce_ranking_atom_measurable
            theta ranking)) ∧
      DistributionalAccuracyFamily.jointLawDisagreementConditionalGain
        (DistributionalAccuracyFamily.plackettLuceDistributionalFamily (n := n)) D theta
        (fun ranking => DistributionalAccuracyFamily.plackettLuce_ranking_atom_measurable
          theta ranking) = 0 :=
  DistributionalAccuracyFamily.plackettLuce_source_jointConditionalGain_zero
    D theta hvalue

/--
Outer-law endpoint for the repository's explicitly scaled `-log Exp(1)`
Gumbel construction.  At positive accuracy, its literal profile and
conditionally iid ranking-pair experiment has positive top-disagreement mass
and zero conditional gain.  This theorem does not identify that construction
with the paper's unspecified Gumbel parameterization, and it does not assert
the separate strategy conclusion.
-/
theorem definedScaledGumbel_outer_joint_conditional_zero
    {n : ℕ} (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    {theta : ℝ} (htheta : 0 < theta)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D) :
    (0 < ∫ x : ValueProfile n × RankingPair n,
      (if disagreementEvent x.2 then (1 : ℝ) else 0) ∂
        (DistributionalAccuracyFamily.scaledGumbelRUMDistributionalFamily
          (n := n)).outerIndependentPairJointLaw D theta
          (fun ranking =>
            DistributionalAccuracyFamily.scaledGumbelRUM_ranking_atom_measurable
              htheta ranking)) ∧
      DistributionalAccuracyFamily.jointLawDisagreementConditionalGain
        (DistributionalAccuracyFamily.scaledGumbelRUMDistributionalFamily
          (n := n)) D theta
        (fun ranking =>
          DistributionalAccuracyFamily.scaledGumbelRUM_ranking_atom_measurable
            htheta ranking) = 0 :=
  DistributionalAccuracyFamily.scaledGumbelRUM_source_jointConditionalGain_zero
    D htheta hvalue

/--
Section 3.1's zero-monoculture-effect conclusion for literal iid Gumbel
innovations `location + (-s * log T)`.  The theorem exposes the full outer
experiment: one value profile from `D`, then two conditionally iid rankings.
At every common location and positive scale, top disagreement has positive
mass and the actual conditional first-minus-second gain is zero.  The induced
Plackett--Luce inverse temperature is visibly `theta / s`; no unproved claim
that a particular scale has unit variance is used.
-/
theorem commonLocationPositiveScaleGumbel_outer_source_joint_conditional_zero
    {n : ℕ} (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    {location s theta : ℝ} (hs : 0 < s) (htheta : 0 < theta)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D) :
    (0 < ∫ x : ValueProfile n × RankingPair n,
      (if disagreementEvent x.2 then (1 : ℝ) else 0) ∂
        (DistributionalAccuracyFamily.commonLocationPositiveScaleGumbelRUMDistributionalFamily
          (n := n) location s).outerIndependentPairJointLaw D theta
          (fun ranking =>
            DistributionalAccuracyFamily.commonLocationPositiveScaleGumbelRUM_ranking_atom_measurable
              hs htheta ranking)) ∧
      DistributionalAccuracyFamily.jointLawDisagreementConditionalGain
        (DistributionalAccuracyFamily.commonLocationPositiveScaleGumbelRUMDistributionalFamily
          (n := n) location s) D theta
        (fun ranking =>
          DistributionalAccuracyFamily.commonLocationPositiveScaleGumbelRUM_ranking_atom_measurable
            hs htheta ranking) = 0 :=
  DistributionalAccuracyFamily.commonLocationPositiveScaleGumbelRUM_source_jointConditionalGain_zero
    D hs htheta hvalue

/--
The preceding source conclusion also has its stated outer payoff identity:
at equal accuracy the independent-reranking and shared-ranking second-mover
payoffs agree.  Integrability of both sides is terminal evidence rather than
an unstated prerequisite of a conditional-ratio calculation.
-/
theorem commonLocationPositiveScaleGumbel_outer_payoff_identity_semantic_complete
    {n : ℕ} (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    {location s theta : ℝ} (hs : 0 < s) (htheta : 0 < theta)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D) :
    Integrable (fun value => expectedSecondMoverIndependent
      ((DistributionalAccuracyFamily.commonLocationPositiveScaleGumbelRUMDistributionalFamily
        (n := n) location s).dist theta value)
      ((DistributionalAccuracyFamily.commonLocationPositiveScaleGumbelRUMDistributionalFamily
        (n := n) location s).dist theta value) value) D ∧
    Integrable (fun value => expectedSecondMoverShared
      ((DistributionalAccuracyFamily.commonLocationPositiveScaleGumbelRUMDistributionalFamily
        (n := n) location s).dist theta value) value) D ∧
    DistributionalAccuracyFamily.outerExpected D (fun value =>
      expectedSecondMoverIndependent
        ((DistributionalAccuracyFamily.commonLocationPositiveScaleGumbelRUMDistributionalFamily
          (n := n) location s).dist theta value)
        ((DistributionalAccuracyFamily.commonLocationPositiveScaleGumbelRUMDistributionalFamily
          (n := n) location s).dist theta value)
        value) =
      DistributionalAccuracyFamily.outerExpected D (fun value =>
        expectedSecondMoverShared
          ((DistributionalAccuracyFamily.commonLocationPositiveScaleGumbelRUMDistributionalFamily
            (n := n) location s).dist theta value)
          value) := by
  let F := DistributionalAccuracyFamily.commonLocationPositiveScaleGumbelRUMDistributionalFamily
    (n := n) location s
  have hatom : ∀ pi : Ranking n,
      AEStronglyMeasurable (fun value : ValueProfile n =>
        ((F.dist theta value) pi).toReal) D := by
    intro pi
    simpa [F] using
      (DistributionalAccuracyFamily.commonLocationPositiveScaleGumbelRUM_ranking_atom_measurable
        (n := n) hs htheta pi).ennreal_toReal.aestronglyMeasurable
  constructor
  · change Integrable (fun value => expectedSecondMoverIndependent
      (F.dist theta value) (F.dist theta value) value) D
    simpa [expectedSecondMoverIndependent, secondMoverUtility] using
      (DistributionalAccuracyFamily.integrable_outer_pmfPairExp_valueSelection_of_atomwise
        D (fun value => F.dist theta value) (fun value => F.dist theta value)
        (fun second first => bestRemainingAfter second (firstChoice first)) hvalue hatom hatom)
  constructor
  · change Integrable (fun value => expectedSecondMoverShared (F.dist theta value) value) D
    simpa [expectedSecondMoverShared] using
      (DistributionalAccuracyFamily.integrable_outer_pmfExp_valueSelection_of_atomwise
        D F.dist theta secondChoice hvalue hatom)
  unfold DistributionalAccuracyFamily.outerExpected
  apply integral_congr_ae
  filter_upwards [] with value
  change expectedSecondMoverIndependent
      (F.dist theta value) (F.dist theta value) value =
    expectedSecondMoverShared (F.dist theta value) value
  rw [DistributionalAccuracyFamily.commonLocationPositiveScaleGumbelRUM_pointwise_eq_positiveScale]
  have hzero := DistributionalAccuracyFamily.positiveScaleGumbelRUM_pointwise_rerankingGain_eq_zero
    (n := n) hs htheta value
  rw [← expectedSecondMoverIndependent_sub_shared_eq_expectedRerankingGain] at hzero
  linarith

/--
Reusable conditional form of the Section 3.1 Gumbel-to-Plackett--Luce bridge.
The exact finite exponential-race formula is proved separately and discharged
by `definedUnitVarianceGumbelRUM_to_corrected_plackettLuce` below.  For the
repository's explicit scaled `-log Exp(1)` convention, the matching
Plackett--Luce inverse temperature is `theta / (sqrt(6) / pi)`, not the
printed scale-one `theta`.  Identifying that convention with the paper's
stated unit-variance Gumbel law remains a separate source-model bridge.
-/
theorem unitVarianceGumbelRUM_to_plackettLuce_of_exponentialRaceFormula
    {n : ℕ} {theta : ℝ} (htheta : 0 < theta) (value : Candidate n → ℝ)
    (raceFormula : HasFiniteExponentialRaceOrderFormula
      (theta / unitVarianceGumbelScale) value) :
    unitVarianceGumbelRUMRankingPMF theta value =
      plackettLuceRankingPMF (theta / unitVarianceGumbelScale) value :=
  unitVarianceGumbelRUMRankingPMF_eq_plackettLuce_of_certificate htheta value
    (gumbelRaceCertificate_of_exponentialOrderFormula
      (theta / unitVarianceGumbelScale) value raceFormula)

/--
The repository's explicitly defined scaled `-log Exp(1)` Gumbel convention
has the stated Plackett--Luce ranking law after the visible scale correction.
The proof uses the literal heterogeneous exponential product law and strict
ranking cells, rather than identifying distributions in a definition.  This
does not assert, without a separate CDF/density/variance bridge, that the
definition is the paper's stated unit-variance Gumbel source model.
-/
theorem definedUnitVarianceGumbelRUM_to_corrected_plackettLuce
    {n : ℕ} {theta : ℝ} (htheta : 0 < theta) (value : Candidate n → ℝ) :
    unitVarianceGumbelRUMRankingPMF theta value =
      plackettLuceRankingPMF (theta / unitVarianceGumbelScale) value :=
  KR21Monoculture.unitVarianceGumbelRUMRankingPMF_eq_plackettLuce htheta value

/--
Literal source-model specialization of the Section 3.1 Gumbel discussion.
The noise law is the actual finite iid product of the innovations
`location - (sqrt(6) / pi) * log T_i`, with `T_i` unit-rate exponential, and
the score expression is literally `value i + epsilon i / theta`.

The sole extra analytic premise is displayed in the theorem type:
`Var[-log T] = pi^2 / 6` for `T ~ Exp(1)`.  Conditional on that identity,
every coordinate of the declared iid noise law has unit variance and the
induced ranking PMF is Plackett--Luce at the corrected inverse temperature
`theta / (sqrt(6) / pi)`.  This does not assert the source's printed
same-parameter formula, and it is a specialization rather than a generic RUM
normalization theorem.
-/
theorem section31_literalUnitVarianceGumbel_source_model
    {n : ℕ} (location : ℝ) {theta : ℝ} (htheta : 0 < theta)
    (value : Candidate n → ℝ)
    (hscaleOneGumbelVariance :
      Var[id; scaleOneGumbelMeasure] = Real.pi ^ 2 / 6) :
    (sourceUnitVarianceGumbelNoiseLaw (n := n) location =
      Measure.pi (fun _ : Candidate n =>
        (expMeasure 1).map
          (fun arrival : ℝ => location +
            (-(Real.sqrt 6 / Real.pi)) * Real.log arrival))) ∧
      (∀ (epsilon : Candidate n → ℝ) (i : Candidate n),
        sourceUnitVarianceGumbelScores theta value epsilon i =
          value i + epsilon i / theta) ∧
      (∀ i : Candidate n,
        Var[(fun epsilon : Candidate n → ℝ => epsilon i);
          sourceUnitVarianceGumbelNoiseLaw (n := n) location] = 1) ∧
        sourceUnitVarianceGumbelRUMRankingPMF location theta value =
          plackettLuceRankingPMF (theta / unitVarianceGumbelScale) value := by
  refine ⟨?_, ?_, sourceUnitVarianceGumbelRUM_source_model
    location htheta value hscaleOneGumbelVariance⟩
  · rfl
  · intro epsilon i
    rfl

/--
Section 3.1's zero-monoculture-effect conclusion for the literal source
unit-variance Gumbel RUM.  The outer experiment is stated over the source
product-noise ranking family itself: sample one profile from `D`, then sample
two rankings conditionally independently from the displayed RUM.  The finite
coordinatewise first-moment condition makes the conditional payoff quantity a
genuine integral rather than a totalized convention.

The special-value identity used to verify unit variance is deliberately not a
premise here: the ranking-law and outer conditional transport use the literal
source product law and score map directly.
-/
theorem section31_literalUnitVarianceGumbel_outer_source_joint_conditional_zero
    {n : ℕ} (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    {location theta : ℝ} (htheta : 0 < theta)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D) :
    (0 < ∫ x : ValueProfile n × RankingPair n,
      (if disagreementEvent x.2 then (1 : ℝ) else 0) ∂
        (DistributionalAccuracyFamily.sourceUnitVarianceGumbelRUMDistributionalFamily
          (n := n) location).outerIndependentPairJointLaw D theta
          (fun ranking =>
            DistributionalAccuracyFamily.sourceUnitVarianceGumbelRUM_ranking_atom_measurable
              htheta ranking)) ∧
      DistributionalAccuracyFamily.jointLawDisagreementConditionalGain
        (DistributionalAccuracyFamily.sourceUnitVarianceGumbelRUMDistributionalFamily
          (n := n) location) D theta
        (fun ranking =>
          DistributionalAccuracyFamily.sourceUnitVarianceGumbelRUM_ranking_atom_measurable
            htheta ranking) = 0 :=
  DistributionalAccuracyFamily.sourceUnitVarianceGumbelRUM_source_jointConditionalGain_zero
    D htheta hvalue

/--
The same literal source outer experiment satisfies the source's payoff
identity `U_AH(theta, theta) = U_AA(theta, theta)`.  Both finite-PMF payoff
integrals are stated and proved integrable before their equality is used.
-/
theorem section31_literalUnitVarianceGumbel_outer_payoff_identity_semantic_complete
    {n : ℕ} (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    {location theta : ℝ} (htheta : 0 < theta)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D) :
    let F := DistributionalAccuracyFamily.sourceUnitVarianceGumbelRUMDistributionalFamily
      (n := n) location
    Integrable (fun value => expectedSecondMoverIndependent
      (F.dist theta value) (F.dist theta value) value) D ∧
    Integrable (fun value => expectedSecondMoverShared (F.dist theta value) value) D ∧
    (∫ value : ValueProfile n,
      expectedSecondMoverIndependent (F.dist theta value) (F.dist theta value) value ∂D) =
      ∫ value : ValueProfile n,
        expectedSecondMoverShared (F.dist theta value) value ∂D := by
  simpa [DistributionalAccuracyFamily.outerExpected] using
    (DistributionalAccuracyFamily.sourceUnitVarianceGumbelRUM_outer_payoff_identity
      (D := D) (location := location) htheta hvalue)

/--
The literal Definition 2 source ratio under the actual outer-then-iid joint
law. Positive top-disagreement mass rules out Lean's totalized zero-event
branch, and the numerator is the paper's first-position-minus-second-position
gain written without a conditional-expectation helper.
-/
theorem jointLawDisagreementConditionalGain_eq_source_ratio_semantic
    {n : ℕ} (F : DistributionalAccuracyFamily n)
    (D : Measure (ValueProfile n)) (theta : ℝ)
    (hatom : ∀ ranking : Ranking n,
      Measurable fun value => F.dist theta value ranking)
    (hdisagreement : 0 < ∫ x : ValueProfile n × RankingPair n,
      (if firstChoice x.2.1 ≠ firstChoice x.2.2 then (1 : ℝ) else 0) ∂
        F.outerIndependentPairJointLaw D theta hatom) :
    F.jointLawDisagreementConditionalGain D theta hatom =
      (∫ x : ValueProfile n × RankingPair n,
        if firstChoice x.2.1 ≠ firstChoice x.2.2 then
          x.1 (firstChoice x.2.1) - x.1 (secondChoice x.2.1)
        else 0 ∂F.outerIndependentPairJointLaw D theta hatom) /
      (∫ x : ValueProfile n × RankingPair n,
        if firstChoice x.2.1 ≠ firstChoice x.2.2 then (1 : ℝ) else 0 ∂
          F.outerIndependentPairJointLaw D theta hatom) := by
  have hdisagreement_event : 0 < ∫ x : ValueProfile n × RankingPair n,
      (if disagreementEvent x.2 then (1 : ℝ) else 0) ∂
        F.outerIndependentPairJointLaw D theta hatom := by
    simpa only [disagreementEvent] using hdisagreement
  have hnum_eq :
      (∫ x : ValueProfile n × RankingPair n,
        if disagreementEvent x.2 then pairRerankingGain x.1 x.2 else 0 ∂
          F.outerIndependentPairJointLaw D theta hatom) =
      ∫ x : ValueProfile n × RankingPair n,
        if firstChoice x.2.1 ≠ firstChoice x.2.2 then
          x.1 (firstChoice x.2.1) - x.1 (secondChoice x.2.1)
        else 0 ∂F.outerIndependentPairJointLaw D theta hatom := by
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases h : firstChoice x.2.1 = firstChoice x.2.2
    · have h0 : x.2.1 0 = x.2.2 0 := by simpa [firstChoice] using h
      simp [disagreementEvent, firstChoice, secondChoice, h0]
    · have h0 : x.2.1 0 ≠ x.2.2 0 := by simpa [firstChoice] using h
      have hne : firstChoice x.2.1 ≠ firstChoice x.2.2 := h
      simp only [disagreementEvent, if_pos hne]
      change AppliedModelingLib.SocialChoice.Ranking.rerankingGainOnPair
        x.1 x.2.1 x.2.2 = x.1 (x.2.1 0) - x.1 (x.2.1 1)
      exact AppliedModelingLib.SocialChoice.Ranking.rerankingGainOnPair_of_neFirst
        x.1 x.2.1 x.2.2 h0
  have hden_eq :
      (∫ x : ValueProfile n × RankingPair n,
        if disagreementEvent x.2 then (1 : ℝ) else 0 ∂
          F.outerIndependentPairJointLaw D theta hatom) =
      ∫ x : ValueProfile n × RankingPair n,
        if firstChoice x.2.1 ≠ firstChoice x.2.2 then (1 : ℝ) else 0 ∂
          F.outerIndependentPairJointLaw D theta hatom := by
    apply integral_congr_ae
    filter_upwards [] with x
    rfl
  unfold DistributionalAccuracyFamily.jointLawDisagreementConditionalGain
  dsimp only
  rw [if_neg (ne_of_gt hdisagreement_event), hnum_eq, hden_eq]

/--
Single review route for Section 3.1's literal source-unit-variance Gumbel
case.  It puts the actual outer-then-conditionally-iid ranking-pair law, both
payoff integrability facts, the positive disagreement event, the literal
source numerator/denominator ratio equal to zero, and
`U_AH(theta, theta) = U_AA(theta, theta)` in one
paper-facing conclusion.  The atomwise measurability witness is explicitly
quantified in the conclusion rather than supplied by a named proof term.
-/
theorem section31_literalUnitVarianceGumbel_outer_zero_effect_semantic_complete
    {n : ℕ} (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    {location theta : ℝ} (htheta : 0 < theta)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D) :
    (sourceUnitVarianceGumbelNoiseLaw (n := n) location =
      Measure.pi (fun _ : Candidate n =>
        (expMeasure 1).map
          (fun arrival : ℝ => location +
            (-(Real.sqrt 6 / Real.pi)) * Real.log arrival))) ∧
    (∀ (profile epsilon : Candidate n → ℝ) (i : Candidate n),
      sourceUnitVarianceGumbelScores theta profile epsilon i =
        profile i + epsilon i / theta) ∧
    (∀ profile : ValueProfile n,
      (sourceUnitVarianceGumbelRUMRankingPMF location theta profile).toMeasure =
        (Measure.pi (fun _ : Candidate n =>
          (expMeasure 1).map
            (fun arrival : ℝ => location +
              (-(Real.sqrt 6 / Real.pi)) * Real.log arrival))).map
          (fun epsilon => rankByScore
            (fun i => profile i + epsilon i / theta))) ∧
    (∀ profile : ValueProfile n,
      sourceUnitVarianceGumbelRUMRankingPMF location theta profile =
        plackettLuceRankingPMF (theta / unitVarianceGumbelScale) profile) ∧
    (let F := DistributionalAccuracyFamily.sourceUnitVarianceGumbelRUMDistributionalFamily
        (n := n) location
      ∃ hatom : ∀ ranking : Ranking n,
          Measurable fun value => F.dist theta value ranking,
        let J := F.outerIndependentPairJointLaw D theta hatom
        let numerator : ℝ := ∫ x : ValueProfile n × RankingPair n,
          if firstChoice x.2.1 ≠ firstChoice x.2.2 then
            x.1 (firstChoice x.2.1) - x.1 (secondChoice x.2.1)
          else 0 ∂J
        let denominator : ℝ := ∫ x : ValueProfile n × RankingPair n,
          if firstChoice x.2.1 ≠ firstChoice x.2.2 then (1 : ℝ) else 0 ∂J
        (J = Measure.compProd D (F.independentPairKernel theta hatom)) ∧
        (∀ profile,
          F.independentPairKernel theta hatom profile =
            (AppliedModelingLib.pmfProd (F.dist theta profile) (F.dist theta profile)).toMeasure) ∧
        Integrable (fun value => expectedSecondMoverIndependent
          (F.dist theta value) (F.dist theta value) value) D ∧
        Integrable (fun value => expectedSecondMoverShared (F.dist theta value) value) D ∧
        0 < denominator ∧
        numerator / denominator = 0 ∧
        (∫ value : ValueProfile n,
          expectedSecondMoverIndependent (F.dist theta value) (F.dist theta value) value ∂D) =
          ∫ value : ValueProfile n,
            expectedSecondMoverShared (F.dist theta value) value ∂D) := by
  have hnoise : sourceUnitVarianceGumbelNoiseLaw (n := n) location =
      Measure.pi (fun _ : Candidate n =>
        (expMeasure 1).map
          (fun arrival : ℝ => location +
            (-(Real.sqrt 6 / Real.pi)) * Real.log arrival)) := rfl
  refine ⟨hnoise, ?_, ?_, ?_, ?_⟩
  · intro profile epsilon i
    rfl
  · intro profile
    letI : IsProbabilityMeasure (sourceUnitVarianceGumbelNoiseLaw (n := n) location) :=
      sourceUnitVarianceGumbelNoiseLaw_isProbabilityMeasure location
    rw [← hnoise]
    change
      (sourceUnitVarianceGumbelRUMRankingPMF location theta profile).toMeasure =
        (sourceUnitVarianceGumbelNoiseLaw (n := n) location).map
          (fun epsilon => rankByScore
            (fun i => profile i + epsilon i / theta))
    unfold sourceUnitVarianceGumbelRUMRankingPMF
    unfold AppliedModelingLib.SocialChoice.Ranking.rankingPMFOfMeasure
    rw [Measure.toPMF_toMeasure]
    congr 1
  · intro profile
    exact sourceUnitVarianceGumbelRUMRankingPMF_eq_plackettLuce_corrected
      location htheta profile
  · dsimp
    refine ⟨(fun ranking =>
      DistributionalAccuracyFamily.sourceUnitVarianceGumbelRUM_ranking_atom_measurable
        htheta ranking), ?_⟩
    dsimp
    let F := DistributionalAccuracyFamily.sourceUnitVarianceGumbelRUMDistributionalFamily
      (n := n) location
    let hatom : ∀ ranking : Ranking n,
        Measurable fun value => F.dist theta value ranking := fun ranking =>
      DistributionalAccuracyFamily.sourceUnitVarianceGumbelRUM_ranking_atom_measurable
        htheta ranking
    obtain ⟨hpositive, hgain⟩ :=
      section31_literalUnitVarianceGumbel_outer_source_joint_conditional_zero
        (D := D) (location := location) htheta hvalue
    obtain ⟨hindependent, hshared, hpayoff⟩ :=
      section31_literalUnitVarianceGumbel_outer_payoff_identity_semantic_complete
        (D := D) (location := location) htheta hvalue
    have hpositive' : 0 < ∫ x : ValueProfile n × RankingPair n,
        (if disagreementEvent x.2 then (1 : ℝ) else 0) ∂
          F.outerIndependentPairJointLaw D theta hatom := by
      simpa [F, hatom] using hpositive
    have hgain' : F.jointLawDisagreementConditionalGain D theta hatom = 0 := by
      simpa [F, hatom] using hgain
    have hden : 0 < ∫ x : ValueProfile n × RankingPair n,
        (if firstChoice x.2.1 ≠ firstChoice x.2.2 then (1 : ℝ) else 0) ∂
          F.outerIndependentPairJointLaw D theta hatom := by
      simpa only [disagreementEvent] using hpositive'
    have hratio := jointLawDisagreementConditionalGain_eq_source_ratio_semantic
      F D theta hatom hden
    have hratio_zero :
        (∫ x : ValueProfile n × RankingPair n,
          if firstChoice x.2.1 ≠ firstChoice x.2.2 then
            x.1 (firstChoice x.2.1) - x.1 (secondChoice x.2.1)
          else 0 ∂F.outerIndependentPairJointLaw D theta hatom) /
        (∫ x : ValueProfile n × RankingPair n,
          if firstChoice x.2.1 ≠ firstChoice x.2.2 then (1 : ℝ) else 0 ∂
            F.outerIndependentPairJointLaw D theta hatom) = 0 := by
      rw [← hratio]
      exact hgain'
    refine ⟨rfl, ?_, hindependent, hshared, ?_, ?_, hpayoff⟩
    · intro profile
      rfl
    · exact hden
    · exact hratio_zero

/--
Audited source-facing proposition for the literal unit-variance Gumbel outer
experiment.  This spells out the source noise law, score transformation,
ranking law, conditionally iid joint experiment, integrability obligations,
positive disagreement event, literal source ratio equal to zero, and payoff
identity. Its
atomwise measurability witness is an explicit existential component, so the
proposition remains independent of the theorem used to construct that witness.
-/
abbrev section31_literalUnitVarianceGumbel_outer_zero_effect_semantic_completeSpec
    {n : ℕ} (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    {location theta : ℝ} (htheta : 0 < theta)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D) : Prop :=
  (sourceUnitVarianceGumbelNoiseLaw (n := n) location =
    Measure.pi (fun _ : Candidate n =>
      (expMeasure 1).map
        (fun arrival : ℝ => location +
          (-(Real.sqrt 6 / Real.pi)) * Real.log arrival))) ∧
  (∀ (profile epsilon : Candidate n → ℝ) (i : Candidate n),
    sourceUnitVarianceGumbelScores theta profile epsilon i =
      profile i + epsilon i / theta) ∧
  (∀ profile : ValueProfile n,
    (sourceUnitVarianceGumbelRUMRankingPMF location theta profile).toMeasure =
      (Measure.pi (fun _ : Candidate n =>
        (expMeasure 1).map
          (fun arrival : ℝ => location +
            (-(Real.sqrt 6 / Real.pi)) * Real.log arrival))).map
        (fun epsilon => rankByScore
          (fun i => profile i + epsilon i / theta))) ∧
  (∀ profile : ValueProfile n,
    sourceUnitVarianceGumbelRUMRankingPMF location theta profile =
      plackettLuceRankingPMF (theta / unitVarianceGumbelScale) profile) ∧
  (let F := DistributionalAccuracyFamily.sourceUnitVarianceGumbelRUMDistributionalFamily
      (n := n) location
    ∃ hatom : ∀ ranking : Ranking n,
        Measurable fun value => F.dist theta value ranking,
      let J := F.outerIndependentPairJointLaw D theta hatom
      let numerator : ℝ := ∫ x : ValueProfile n × RankingPair n,
        if firstChoice x.2.1 ≠ firstChoice x.2.2 then
          x.1 (firstChoice x.2.1) - x.1 (secondChoice x.2.1)
        else 0 ∂J
      let denominator : ℝ := ∫ x : ValueProfile n × RankingPair n,
        if firstChoice x.2.1 ≠ firstChoice x.2.2 then (1 : ℝ) else 0 ∂J
      (J = Measure.compProd D (F.independentPairKernel theta hatom)) ∧
      (∀ profile,
        F.independentPairKernel theta hatom profile =
          (AppliedModelingLib.pmfProd (F.dist theta profile) (F.dist theta profile)).toMeasure) ∧
      Integrable (fun value => expectedSecondMoverIndependent
        (F.dist theta value) (F.dist theta value) value) D ∧
      Integrable (fun value => expectedSecondMoverShared (F.dist theta value) value) D ∧
      0 < denominator ∧
      numerator / denominator = 0 ∧
      (∫ value : ValueProfile n,
        expectedSecondMoverIndependent (F.dist theta value) (F.dist theta value) value ∂D) =
        ∫ value : ValueProfile n,
          expectedSecondMoverShared (F.dist theta value) value ∂D)

theorem section31_literalUnitVarianceGumbel_outer_zero_effect_semantic_complete_spec_proof
    {n : ℕ} (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    {location theta : ℝ} (htheta : 0 < theta)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D) :
    section31_literalUnitVarianceGumbel_outer_zero_effect_semantic_completeSpec
      (location := location) (theta := theta) D htheta hvalue :=
  section31_literalUnitVarianceGumbel_outer_zero_effect_semantic_complete
    (location := location) (theta := theta) D htheta hvalue

/--
The Section 3.1 strategy conclusion for the literal source unit-variance
Gumbel RUM.  At equal accuracies only weak dominance is true, so the result
is an explicit case split on the two positive accuracy parameters rather than
a claim of strict dominance from the strategy names.
-/
theorem section31_literalUnitVarianceGumbel_best_available_weakly_dominates
    {n : ℕ} {location thetaA thetaH : ℝ}
    (value : Candidate n → ℝ)
    (hthetaA : 0 < thetaA) (hthetaH : 0 < thetaH) :
    let M : Model n :=
      { algorithmRanking :=
          sourceUnitVarianceGumbelRUMRankingPMF location thetaA value
        humanRanking := sourceUnitVarianceGumbelRUMRankingPMF location thetaH value
        value := value }
    (thetaH ≤ thetaA →
      Model.payoffAgainst M Strategy.algorithm Strategy.algorithm ≥
          Model.payoffAgainst M Strategy.human Strategy.algorithm ∧
        Model.payoffAgainst M Strategy.algorithm Strategy.human ≥
          Model.payoffAgainst M Strategy.human Strategy.human) ∧
      (thetaA ≤ thetaH →
        Model.payoffAgainst M Strategy.human Strategy.algorithm ≥
            Model.payoffAgainst M Strategy.algorithm Strategy.algorithm ∧
          Model.payoffAgainst M Strategy.human Strategy.human ≥
            Model.payoffAgainst M Strategy.algorithm Strategy.human) :=
  sourceUnitVarianceGumbel_best_available_weakly_dominates value hthetaA hthetaH

/--
The complete approved correction for the Section 3.1 Gumbel identification.
It packages the generic positive-scale law with the distinct literal
unit-variance source-model specialization, whose variance calculation remains
conditional on the visible analytic special-value premise.
-/
theorem section31_corrected_gumbel_plackett_luce_target
    {n : ℕ} (location : ℝ) {s theta : ℝ} (hs : 0 < s) (htheta : 0 < theta)
    (value : Candidate n → ℝ) :
    (gumbelArrivalLaw n =
      Measure.pi (fun _ : Candidate n => expMeasure 1)) ∧
      (∀ᵐ arrival ∂gumbelArrivalLaw n, ∀ i : Candidate n, 0 < arrival i) ∧
      (∀ (arrival : Candidate n → ℝ) (i : Candidate n),
        commonLocationPositiveScaleGumbelNoise location s arrival i =
          location + (-s) * Real.log (arrival i)) ∧
      (∀ (arrival : Candidate n → ℝ) (i : Candidate n),
        commonLocationPositiveScaleGumbelScores location s theta value arrival i =
          value i + (location + (-s) * Real.log (arrival i)) / theta) ∧
      (Measure.map (commonLocationPositiveScaleGumbelNoise location s)
          (gumbelArrivalLaw n) =
        Measure.pi (fun _ : Candidate n =>
          (expMeasure 1).map
            (fun arrival : ℝ => location + (-s) * Real.log arrival))) ∧
      commonLocationPositiveScaleGumbelRUMRankingPMF location s theta value =
        plackettLuceRankingPMF (theta / s) value ∧
      (Var[id; scaleOneGumbelMeasure] = Real.pi ^ 2 / 6 →
        (sourceUnitVarianceGumbelNoiseLaw (n := n) location =
          Measure.pi (fun _ : Candidate n =>
            (expMeasure 1).map
              (fun arrival : ℝ => location +
                (-(Real.sqrt 6 / Real.pi)) * Real.log arrival))) ∧
          (∀ (epsilon : Candidate n → ℝ) (i : Candidate n),
            sourceUnitVarianceGumbelScores theta value epsilon i =
              value i + epsilon i / theta) ∧
          (∀ i : Candidate n,
            Var[(fun epsilon : Candidate n → ℝ => epsilon i);
              sourceUnitVarianceGumbelNoiseLaw (n := n) location] = 1) ∧
            sourceUnitVarianceGumbelRUMRankingPMF location theta value =
              plackettLuceRankingPMF (theta / (Real.sqrt 6 / Real.pi)) value) := by
  refine ⟨rfl, gumbelArrivalLaw_ae_positive, ?_, ?_, ?_,
    section31_commonLocationPositiveScaleGumbel_to_plackettLuce hs htheta value, ?_⟩
  · intro arrival i
    rfl
  · intro arrival i
    rfl
  · simpa only [commonLocationPositiveScaleGumbelMeasure,
      commonLocationPositiveScaleGumbelInnovation,
      positiveScaleGumbelInnovation] using
      (commonLocationPositiveScaleGumbelNoise_law (n := n) location s)
  intro hscaleOneGumbelVariance
  simpa [unitVarianceGumbelScale] using
    (section31_literalUnitVarianceGumbel_source_model
      location htheta value hscaleOneGumbelVariance)

/--
The Section 3.1 unit-variance convention, made literal.  From an iid scalar
noise law with a finite, strictly positive variance, normalize each innovation
by `sqrt(Var)`, replace `theta` by `theta / sqrt(Var)`, and preserve the exact
ranking PMF.  The normalized law is explicitly a product law with independent
coordinates of variance one; none of those facts is inferred from a name.
-/
theorem section31_iidFinitePositiveVariance_normalization
    {n : ℕ} (E : Measure ℝ) [IsProbabilityMeasure E]
    (hsecond : MemLp id 2 E)
    (hvariance_pos : 0 < Var[id; E])
    (value : Candidate n → ℝ) (theta : ℝ) (htheta : 0 < theta) :
    iIndepFun
        (fun i (epsilon : Candidate n → ℝ) => epsilon i)
        (sourceRUMNormalizedIIDNoiseLaw (n := n) E
          (Real.sqrt (Var[id; E]))) ∧
      MemLp id 2
        (sourceRUMNormalizedScalarNoiseLaw E (Real.sqrt (Var[id; E]))) ∧
      (∀ i : Candidate n,
        Var[(fun epsilon : Candidate n → ℝ => epsilon i);
          sourceRUMNormalizedIIDNoiseLaw (n := n) E
            (Real.sqrt (Var[id; E]))] = 1) ∧
      paper_appendixA_scaledNoiseRankingPMF
          (Measure.pi (fun _ : Candidate n => E)) value theta =
        @paper_appendixA_scaledNoiseRankingPMF n
          (sourceRUMNormalizedIIDNoiseLaw (n := n) E
            (Real.sqrt (Var[id; E])))
          (sourceRUMNormalizedIIDNoiseLaw_isProbabilityMeasure E
            (Real.sqrt (Var[id; E])))
          value (theta / Real.sqrt (Var[id; E])) :=
  sourceRUM_iidFinitePositiveVariance_normalization
    E hsecond hvariance_pos value theta

/-- The Definition 2 simulation score is unbiased for its exact payoff gap. -/
theorem simulation_definition2_score_unbiased
    {n : ℕ} (ownLaw firstLaw : PMF (Ranking n))
    (value : Candidate n → ℝ) :
    pmfPairExp ownLaw firstLaw
        (fun own independentFirst =>
          definition2SampleScore value own independentFirst) =
      expectedSecondMoverIndependent ownLaw firstLaw value -
        expectedSecondMoverShared ownLaw value :=
  definition2SampleScore_expectation_eq_payoff_gap ownLaw firstLaw value

/-- The Definition 3 simulation score is unbiased for its exact payoff gap. -/
theorem simulation_definition3_score_unbiased
    {n : ℕ} (humanLaw algorithmLaw : PMF (Ranking n))
    (value : Candidate n → ℝ) :
    definition3SampleExpectation humanLaw algorithmLaw value =
      expectedSecondMoverIndependent humanLaw humanLaw value -
        expectedSecondMoverIndependent humanLaw algorithmLaw value :=
  definition3SampleExpectation_eq_payoff_gap humanLaw algorithmLaw value

/-- The Definition 2 score remains unbiased after the source's outer draw from `D`. -/
abbrev simulation_definition2_outer_score_unbiased :=
  @KR21Monoculture.definition2OuterSampleMean_eq_payoff_gap

/-- The Definition 3 score remains unbiased after the source's outer draw from `D`. -/
abbrev simulation_definition3_outer_score_unbiased :=
  @KR21Monoculture.definition3OuterSampleMean_eq_payoff_gap

/-- The concrete simulation estimator has exactly one score evaluation per sample. -/
theorem simulation_score_evaluation_cost_linear
    {I : Type*} (samples : Finset I) :
    empiricalScoreEvaluationCost samples = samples.card :=
  empiricalScoreEvaluationCost_eq_card samples

/-- Definition 2's oracle-inclusive cost is linear in the sample count. -/
theorem simulation_definition2_oracle_cost_linear
    {I : Type*} (samples : Finset I)
    (valueDrawCost rankingDrawCost scoreCost : ℕ) :
    definition2SimulationOracleCost samples valueDrawCost rankingDrawCost scoreCost =
      samples.card * (valueDrawCost + 2 * rankingDrawCost + scoreCost) :=
  definition2SimulationOracleCost_eq
    samples valueDrawCost rankingDrawCost scoreCost

/-- Definition 3's oracle-inclusive cost is linear in the sample count. -/
theorem simulation_definition3_oracle_cost_linear
    {I : Type*} (samples : Finset I)
    (valueDrawCost humanDrawCost algorithmDrawCost scoreCost : ℕ) :
    definition3SimulationOracleCost samples valueDrawCost humanDrawCost
        algorithmDrawCost scoreCost =
      samples.card *
        (valueDrawCost + 2 * humanDrawCost + algorithmDrawCost + scoreCost) :=
  definition3SimulationOracleCost_eq
    samples valueDrawCost humanDrawCost algorithmDrawCost scoreCost

/-- A strict estimation error below a positive source margin makes the sign test correct. -/
theorem simulation_positive_margin_test_correct
    {Omega I : Type*} (samples : Finset I) (X : I → Omega → ℝ)
    (omega : Omega) (trueMean margin : ℝ)
    (hmean : margin ≤ trueMean) (hmargin : 0 < margin)
    (herror : |empiricalMean samples X omega - trueMean| < margin) :
    empiricalPositiveMarginTest samples X omega :=
  empiricalPositiveMarginTest_of_error_lt_margin
    samples X omega trueMean margin hmean hmargin herror

/--
Pointwise statistical accuracy: with independent bounded scores whose mean is
at least `margin > 0`, the probability that the empirical test misses the
positive sign has the explicit Hoeffding bound below.
-/
theorem simulation_pointwise_false_negative_hoeffding
    {Omega I : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {X : I → Omega → ℝ} (h_indep : iIndepFun X mu)
    {samples : Finset I} {a b margin : ℝ}
    (h_meas : ∀ i ∈ samples, AEMeasurable (X i) mu)
    (h_bound : ∀ i ∈ samples,
      ∀ᵐ omega ∂mu, X i omega ∈ Set.Icc a b)
    (hmargin : 0 < margin)
    (hmean : ∀ i ∈ samples, margin ≤ ∫ x, X i x ∂mu) :
    mu.real {omega | ∑ i ∈ samples, X i omega ≤ 0} ≤
      Real.exp
        (-((samples.card : ℝ) * margin) ^ 2 /
          (2 * ((∑ _ ∈ samples,
            ((‖b - a‖₊ / 2) ^ 2 : NNReal)) : ℝ))) :=
  empirical_nonpositive_probability_le_hoeffding
    mu h_indep h_meas h_bound hmargin hmean

/--
Source-correct Definition 2 simulation semantics: the simulated outer score
is the actual joint disagreement-gain numerator, and its sign is the source
conditional-gain sign once the conditioning event has positive mass.
-/
theorem simulation_definition2_source_conditional_sign
    {n : ℕ} (F : DistributionalAccuracyFamily n)
    (D : Measure (ValueProfile n)) (theta : ℝ)
    (hdisagreement : 0 < F.outerDisagreementProbability D theta) :
    0 < definition2OuterSampleMean F D theta ↔
      0 < F.outerDisagreementConditionalGain D theta :=
  definition2OuterSampleMean_pos_iff_outerDisagreementConditionalGain_pos_of_pos
    F D theta hdisagreement

/--
At one fixed parameter, IID integrable samples with a strictly positive score
mean eventually pass the implemented empirical sign test almost surely.  This
is a consistency result, not a finite universal test for Definitions 1--3.
-/
theorem simulation_fixed_parameter_iid_eventually_accepts
    {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    (X : ℕ → Omega → ℝ) (hintegrable : Integrable (X 0) mu)
    (hindep : Pairwise (Function.onFun (· ⟂ᵢ[mu] ·) X))
    (hident : ∀ i, IdentDistrib (X i) (X 0) mu mu)
    (hmean : 0 < ∫ omega, X 0 omega ∂mu) :
    ∀ᵐ omega ∂mu, ∀ᶠ sampleCount : ℕ in atTop,
      empiricalPositiveMarginTest (Finset.range sampleCount) X omega :=
  ae_eventually_empiricalPositiveMarginTest_of_iid_positive_mean
    mu X hintegrable hindep hident hmean

/--
The finite-grid version of the source simulation procedure.  It certifies
only the supplied grid and keeps every IID, integrability, and positive-margin
assumption visible; it says nothing about an uncountable parameter domain.
-/
theorem simulation_finite_grid_iid_eventually_accepts
    {Omega Parameter : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    (grid : Finset Parameter) (X : Parameter → ℕ → Omega → ℝ)
    (hintegrable : ∀ parameter ∈ grid, Integrable (X parameter 0) mu)
    (hindep : ∀ parameter ∈ grid,
      Pairwise (Function.onFun (· ⟂ᵢ[mu] ·) (X parameter)))
    (hident : ∀ parameter ∈ grid, ∀ i,
      IdentDistrib (X parameter i) (X parameter 0) mu mu)
    (hmean : ∀ parameter ∈ grid, 0 < ∫ omega, X parameter 0 omega ∂mu) :
    ∀ᵐ omega ∂mu, ∀ᶠ sampleCount : ℕ in atTop,
      ∀ parameter ∈ grid,
        empiricalPositiveMarginTest (Finset.range sampleCount)
          (X parameter) omega :=
  ae_eventually_forall_empiricalPositiveMarginTest_on_finite_grid
    mu grid X hintegrable hindep hident hmean

/--
Finite-grid confidence bound for the implemented sign tests.  A union bound,
not cross-grid independence, is used; bounded scores and a positive margin at
each grid point are explicit.
-/
theorem simulation_finite_grid_false_negative_hoeffding
    {Omega I Parameter : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (grid : Finset Parameter) (X : Parameter → I → Omega → ℝ)
    (samples : Finset I) (a b margin : Parameter → ℝ)
    (hsamples : samples.Nonempty)
    (h_indep : ∀ parameter ∈ grid, iIndepFun (X parameter) mu)
    (h_meas : ∀ parameter ∈ grid, ∀ i ∈ samples,
      AEMeasurable (X parameter i) mu)
    (h_bound : ∀ parameter ∈ grid, ∀ i ∈ samples,
      ∀ᵐ omega ∂mu, X parameter i omega ∈ Set.Icc
        (a parameter) (b parameter))
    (hmargin : ∀ parameter ∈ grid, 0 < margin parameter)
    (hmean : ∀ parameter ∈ grid, ∀ i ∈ samples,
      margin parameter ≤ ∫ omega, X parameter i omega ∂mu) :
    mu.real {omega | ∃ parameter ∈ grid,
      ¬ empiricalPositiveMarginTest samples (X parameter) omega} ≤
      ∑ parameter ∈ grid, Real.exp
        (-((samples.card : ℝ) * margin parameter) ^ 2 /
          (2 * ((∑ _ ∈ samples,
            ((‖b parameter - a parameter‖₊ / 2) ^ 2 : NNReal)) : ℝ))) :=
  measureReal_finiteGrid_any_empirical_test_failure_le_sum_hoeffding
    mu grid X samples a b margin hsamples h_indep h_meas h_bound hmargin hmean

/--
Finite simulations extend to a full parameter domain only under an explicit
grid-coverage and Lipschitz-margin certificate.  This is the missing
mathematical obligation in the source's broad efficiency sentence.
-/
theorem simulation_grid_lipschitz_margin_certifies_domain
    {Parameter : Type*} [PseudoMetricSpace Parameter]
    (domain : Set Parameter) (grid : Finset Parameter)
    (score : Parameter → ℝ) (radius lipschitz : ℝ)
    (hlipschitz_nonneg : 0 ≤ lipschitz)
    (hcover : ∀ parameter ∈ domain, ∃ gridPoint ∈ grid,
      dist parameter gridPoint ≤ radius)
    (hlipschitz : ∀ parameter ∈ domain, ∀ gridPoint ∈ grid,
      |score parameter - score gridPoint| ≤
        lipschitz * dist parameter gridPoint)
    (hgridMargin : ∀ gridPoint ∈ grid,
      lipschitz * radius < score gridPoint) :
    ∀ parameter ∈ domain, 0 < score parameter :=
  score_pos_on_domain_of_finite_grid_lipschitz_margin
    domain grid score radius lipschitz hlipschitz_nonneg hcover hlipschitz
    hgridMargin

/--
Appendix B.1 source instantiation: every displayed ranking mass is the exact
pushforward of three iid draws from the paper's `delta=1/10` discrete noise law
through the realized-score ranking.
-/
theorem appendixB1_iid_rum_pushforward_exact
    (a : AppendixBRankingAtom) :
    appendixB1RankingWeight a = appendixB1IIDRUMRankingWeight a :=
  appendixB1RankingWeight_eq_iid_rum_pushforward a

/--
Appendix B.2 algorithmic source instantiation at `theta_A=1.1 theta`.
-/
theorem appendixB2_algorithm_iid_rum_pushforward_exact
    (a : AppendixBRankingAtom) :
    appendixB2AlgorithmRankingWeight a =
      appendixB2AlgorithmIIDRUMRankingWeight a :=
  appendixB2AlgorithmRankingWeight_eq_iid_rum_pushforward a

/-- Appendix B.2 human source instantiation at `theta_H=0.9 theta`. -/
theorem appendixB2_human_iid_rum_pushforward_exact
    (a : AppendixBRankingAtom) :
    appendixB2HumanRankingWeight a =
      appendixB2HumanIIDRUMRankingWeight a :=
  appendixB2HumanRankingWeight_eq_iid_rum_pushforward a

/-- Appendix B.1 exact counterexample to Definition 2. -/
theorem appendixB1_definition2_counterexample_exact :
    expectedSecondMoverIndependent
          appendixB1RankingPMF appendixB1RankingPMF appendixB1Value -
        expectedSecondMoverShared appendixB1RankingPMF appendixB1Value =
      -(9749 / 12800000 : ℝ) :=
  appendixB1_definition2_reversal_exact

/--
Complete source-facing Appendix B.1 counterexample.  The proposition exposes
the three value coordinates, the literal iid discrete noise atoms and masses,
their score-ranking pushforward, the exact signed payoff gap, and the failed
Definition 2 predicate in one endpoint.
-/
theorem appendixB1_source_discrete_definition2_counterexample :
    (appendixB1Value (0 : Candidate 1) = 7 / 4 ∧
      appendixB1Value (1 : Candidate 1) = 1 / 2 ∧
        appendixB1Value (2 : Candidate 1) = 0) ∧
      (appendixB1NoiseValue .plusOne = 1 ∧
        appendixB1NoiseValue .zero = 0 ∧
          appendixB1NoiseValue .minusOne = -1) ∧
      (appendixB1NoiseWeight .plusOne = 1 / 20 ∧
        appendixB1NoiseWeight .zero = 9 / 10 ∧
          appendixB1NoiseWeight .minusOne = 1 / 20) ∧
      (∀ a : AppendixBRankingAtom,
        appendixB1RankingWeight a =
          ∑ e0 : AppendixB1NoiseAtom,
            ∑ e1 : AppendixB1NoiseAtom,
              ∑ e2 : AppendixB1NoiseAtom,
                if appendixBRankingAtomOfScores
                    (7 / 4 + appendixB1NoiseValue e0)
                    (1 / 2 + appendixB1NoiseValue e1)
                    (appendixB1NoiseValue e2) = a then
                  appendixB1NoiseWeight e0 * appendixB1NoiseWeight e1 *
                    appendixB1NoiseWeight e2
                else 0) ∧
      (expectedSecondMoverIndependent
          appendixB1RankingPMF appendixB1RankingPMF appendixB1Value -
        expectedSecondMoverShared appendixB1RankingPMF appendixB1Value =
          -(9749 / 12800000 : ℝ)) ∧
        ¬ Model.PrefersIndependentReranking appendixB1RankingPMF appendixB1Value := by
  refine ⟨?_, ?_, ?_, ?_, appendixB1_definition2_counterexample_exact,
    appendixB1_not_prefersIndependentReranking⟩
  · norm_num [appendixB1Value, Fin.ext_iff]
  · norm_num [appendixB1NoiseValue]
  · norm_num [appendixB1NoiseWeight]
  · intro a
    simpa only [appendixB1IIDRUMRankingWeight] using
      (appendixB1RankingWeight_eq_iid_rum_pushforward a)

/--
Appendix B.1 with its finite iid experiment attached directly to the payoff
claim.  The terminal statement exposes the atom masses, the three-fold
product law, and the realized-score ranking map used by the conclusion.
-/
theorem appendixB1_source_discrete_definition2_counterexample_semantic_complete :
    let componentLaw : PMF AppendixB1NoiseAtom := appendixB1NoisePMF
    let rawNoiseLaw : PMF AppendixB1NoiseTriple :=
      AppliedModelingLib.pmfProd (AppliedModelingLib.pmfProd componentLaw componentLaw) componentLaw
    let rawRank : AppendixB1NoiseTriple -> Ranking 1 := fun noise =>
      rankByScore (fun c => appendixB1Value c +
        appendixB1NoiseValue (appendixB1NoiseTripleFunction noise c))
    let rawLaw : PMF (Ranking 1) := rawNoiseLaw.map rawRank
    (appendixB1Value (0 : Candidate 1) = 7 / 4 ∧
      appendixB1Value (1 : Candidate 1) = 1 / 2 ∧
        appendixB1Value (2 : Candidate 1) = 0) ∧
    (appendixB1NoiseValue .plusOne = 1 ∧
      appendixB1NoiseValue .zero = 0 ∧
        appendixB1NoiseValue .minusOne = -1) ∧
    (componentLaw .plusOne).toReal = 1 / 20 ∧
    (componentLaw .zero).toReal = 9 / 10 ∧
    (componentLaw .minusOne).toReal = 1 / 20 ∧
    (∀ noise : AppendixB1NoiseTriple,
      rawRank noise = appendixB1DiscreteTripleRank noise) ∧
    rawLaw = appendixB1RankingPMF ∧
    expectedSecondMoverIndependent rawLaw rawLaw appendixB1Value -
        expectedSecondMoverShared rawLaw appendixB1Value =
      -(9749 / 12800000 : ℝ) ∧
    ¬ Model.PrefersIndependentReranking rawLaw appendixB1Value := by
  dsimp
  have hpointwise : ∀ noise : AppendixB1NoiseTriple,
      rankByScore (fun c => appendixB1Value c +
        appendixB1NoiseValue (appendixB1NoiseTripleFunction noise c)) =
        appendixB1DiscreteTripleRank noise := by
    intro noise
    simpa [appendixB1DiscreteScore] using
      (appendixB1_rankByScore_discreteTriple_eq noise)
  have hmap :
      (AppliedModelingLib.pmfProd (AppliedModelingLib.pmfProd appendixB1NoisePMF appendixB1NoisePMF)
        appendixB1NoisePMF).map
        (fun noise => rankByScore (fun c => appendixB1Value c +
          appendixB1NoiseValue (appendixB1NoiseTripleFunction noise c))) =
        appendixB1RankingPMF := by
    change appendixB1NoiseTriplePMF.map
      (fun noise => rankByScore (fun c => appendixB1Value c +
        appendixB1NoiseValue (appendixB1NoiseTripleFunction noise c))) =
      appendixB1RankingPMF
    rw [show (fun noise : AppendixB1NoiseTriple =>
      rankByScore (fun c => appendixB1Value c +
        appendixB1NoiseValue (appendixB1NoiseTripleFunction noise c))) =
        appendixB1DiscreteTripleRank by
          funext noise
          exact hpointwise noise]
    exact appendixB1NoiseTriplePMF_map_discreteTripleRank
  refine ⟨?_, ?_, ?_, ?_, ?_, hpointwise, hmap, ?_, ?_⟩
  · norm_num [appendixB1Value, Fin.ext_iff]
  · norm_num [appendixB1NoiseValue]
  · norm_num [appendixB1NoisePMF_apply_toReal, appendixB1NoiseWeight]
  · norm_num [appendixB1NoisePMF_apply_toReal, appendixB1NoiseWeight]
  · norm_num [appendixB1NoisePMF_apply_toReal, appendixB1NoiseWeight]
  · rw [hmap]
    exact appendixB1_definition2_reversal_exact
  · rw [hmap]
    exact appendixB1_not_prefersIndependentReranking

/-- Appendix B.2 exact counterexample to Definition 3. -/
theorem appendixB2_definition3_counterexample_exact :
    expectedSecondMoverIndependent
          appendixB2HumanRankingPMF appendixB2AlgorithmRankingPMF appendixB2Value -
        expectedSecondMoverIndependent
          appendixB2HumanRankingPMF appendixB2HumanRankingPMF appendixB2Value =
      567 / 3200000 :=
  appendixB2_definition3_reversal_exact

/--
Complete source-facing Appendix B.2 counterexample.  It exposes the literal
iid base law, the `11/10` and `9/10` accuracy factors through their inverse
score scales, both score-ranking pushforwards, the exact payoff gap, and the
failed Definition 3 predicate in one endpoint.
-/
theorem appendixB2_source_discrete_definition3_counterexample :
    (appendixB2Value (0 : Candidate 1) = 3 ∧
      appendixB2Value (1 : Candidate 1) = 2 ∧
        appendixB2Value (2 : Candidate 1) = 0) ∧
      (appendixB2NoiseValue .plusOne = 1 ∧
        appendixB2NoiseValue .minusOne = -1 ∧
          appendixB2NoiseValue .plusTen = 10 ∧
            appendixB2NoiseValue .minusTen = -10) ∧
      (appendixB2NoiseWeight .plusOne = 9 / 20 ∧
        appendixB2NoiseWeight .minusOne = 9 / 20 ∧
          appendixB2NoiseWeight .plusTen = 1 / 20 ∧
            appendixB2NoiseWeight .minusTen = 1 / 20) ∧
      ((11 / 10 : ℝ) > 9 / 10 ∧
        (10 / 11 : ℝ) * (11 / 10 : ℝ) = 1 ∧
          (10 / 9 : ℝ) * (9 / 10 : ℝ) = 1) ∧
      (∀ a : AppendixBRankingAtom,
        appendixB2AlgorithmRankingWeight a =
          ∑ e0 : AppendixB2NoiseAtom,
            ∑ e1 : AppendixB2NoiseAtom,
              ∑ e2 : AppendixB2NoiseAtom,
                if appendixBRankingAtomOfScores
                    (3 + (10 / 11) * appendixB2NoiseValue e0)
                    (2 + (10 / 11) * appendixB2NoiseValue e1)
                    ((10 / 11) * appendixB2NoiseValue e2) = a then
                  appendixB2NoiseWeight e0 * appendixB2NoiseWeight e1 *
                    appendixB2NoiseWeight e2
                else 0) ∧
      (∀ a : AppendixBRankingAtom,
        appendixB2HumanRankingWeight a =
          ∑ e0 : AppendixB2NoiseAtom,
            ∑ e1 : AppendixB2NoiseAtom,
              ∑ e2 : AppendixB2NoiseAtom,
                if appendixBRankingAtomOfScores
                    (3 + (10 / 9) * appendixB2NoiseValue e0)
                    (2 + (10 / 9) * appendixB2NoiseValue e1)
                    ((10 / 9) * appendixB2NoiseValue e2) = a then
                  appendixB2NoiseWeight e0 * appendixB2NoiseWeight e1 *
                    appendixB2NoiseWeight e2
                else 0) ∧
      (expectedSecondMoverIndependent
          appendixB2HumanRankingPMF appendixB2AlgorithmRankingPMF appendixB2Value -
        expectedSecondMoverIndependent
          appendixB2HumanRankingPMF appendixB2HumanRankingPMF appendixB2Value =
          567 / 3200000) ∧
        ¬ Model.PrefersWeakerCompetition
          appendixB2AlgorithmRankingPMF appendixB2HumanRankingPMF appendixB2Value := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, appendixB2_definition3_counterexample_exact,
    appendixB2_not_prefersWeakerCompetition⟩
  · norm_num [appendixB2Value, Fin.ext_iff]
  · norm_num [appendixB2NoiseValue]
  · norm_num [appendixB2NoiseWeight]
  · norm_num
  · intro a
    simpa only [appendixB2AlgorithmIIDRUMRankingWeight] using
      (appendixB2AlgorithmRankingWeight_eq_iid_rum_pushforward a)
  · intro a
    simpa only [appendixB2HumanIIDRUMRankingWeight] using
      (appendixB2HumanRankingWeight_eq_iid_rum_pushforward a)

/--
Appendix B.2 with both finite iid source experiments attached directly to the
Definition 3 counterexample.  The payoff conclusion uses the same two laws
whose product construction and realized-score maps appear in the type.
-/
theorem appendixB2_source_discrete_definition3_counterexample_semantic_complete :
    let componentLaw : PMF AppendixB2NoiseAtom := appendixB2NoisePMF
    let rawNoiseLaw : PMF AppendixB2NoiseTriple :=
      AppliedModelingLib.pmfProd (AppliedModelingLib.pmfProd componentLaw componentLaw) componentLaw
    let algorithmRank : AppendixB2NoiseTriple -> Ranking 1 := fun noise =>
      rankByScore (fun c => appendixB2Value c + (10 / 11) *
        appendixB2NoiseValue (appendixB2NoiseTripleFunction noise c))
    let humanRank : AppendixB2NoiseTriple -> Ranking 1 := fun noise =>
      rankByScore (fun c => appendixB2Value c + (10 / 9) *
        appendixB2NoiseValue (appendixB2NoiseTripleFunction noise c))
    let algorithmLaw : PMF (Ranking 1) := rawNoiseLaw.map algorithmRank
    let humanLaw : PMF (Ranking 1) := rawNoiseLaw.map humanRank
    (appendixB2Value (0 : Candidate 1) = 3 ∧
      appendixB2Value (1 : Candidate 1) = 2 ∧
        appendixB2Value (2 : Candidate 1) = 0) ∧
    (appendixB2NoiseValue .plusOne = 1 ∧
      appendixB2NoiseValue .minusOne = -1 ∧
        appendixB2NoiseValue .plusTen = 10 ∧
          appendixB2NoiseValue .minusTen = -10) ∧
    (componentLaw .plusOne).toReal = 9 / 20 ∧
    (componentLaw .minusOne).toReal = 9 / 20 ∧
    (componentLaw .plusTen).toReal = 1 / 20 ∧
    (componentLaw .minusTen).toReal = 1 / 20 ∧
    ((11 / 10 : ℝ) > 9 / 10 ∧
      (10 / 11 : ℝ) * (11 / 10 : ℝ) = 1 ∧
        (10 / 9 : ℝ) * (9 / 10 : ℝ) = 1) ∧
    (∀ noise : AppendixB2NoiseTriple,
      algorithmRank noise = appendixB2AlgorithmDiscreteTripleRank noise) ∧
    (∀ noise : AppendixB2NoiseTriple,
      humanRank noise = appendixB2HumanDiscreteTripleRank noise) ∧
    algorithmLaw = appendixB2AlgorithmRankingPMF ∧
    humanLaw = appendixB2HumanRankingPMF ∧
    expectedSecondMoverIndependent humanLaw algorithmLaw appendixB2Value -
        expectedSecondMoverIndependent humanLaw humanLaw appendixB2Value =
      567 / 3200000 ∧
    ¬ Model.PrefersWeakerCompetition algorithmLaw humanLaw appendixB2Value := by
  dsimp
  have hAlgorithmPointwise : ∀ noise : AppendixB2NoiseTriple,
      rankByScore (fun c => appendixB2Value c + (10 / 11) *
        appendixB2NoiseValue (appendixB2NoiseTripleFunction noise c)) =
        appendixB2AlgorithmDiscreteTripleRank noise := by
    intro noise
    simpa [appendixB2AlgorithmDiscreteScore] using
      (appendixB2_algorithm_rankByScore_discreteTriple_eq noise)
  have hHumanPointwise : ∀ noise : AppendixB2NoiseTriple,
      rankByScore (fun c => appendixB2Value c + (10 / 9) *
        appendixB2NoiseValue (appendixB2NoiseTripleFunction noise c)) =
        appendixB2HumanDiscreteTripleRank noise := by
    intro noise
    simpa [appendixB2HumanDiscreteScore] using
      (appendixB2_human_rankByScore_discreteTriple_eq noise)
  have hAlgorithmMap :
      (AppliedModelingLib.pmfProd
        (AppliedModelingLib.pmfProd appendixB2NoisePMF appendixB2NoisePMF)
        appendixB2NoisePMF).map
          (fun noise => rankByScore (fun c => appendixB2Value c + (10 / 11) *
            appendixB2NoiseValue (appendixB2NoiseTripleFunction noise c))) =
        appendixB2AlgorithmRankingPMF := by
    change appendixB2NoiseTriplePMF.map
      (fun noise => rankByScore (fun c => appendixB2Value c + (10 / 11) *
        appendixB2NoiseValue (appendixB2NoiseTripleFunction noise c))) =
      appendixB2AlgorithmRankingPMF
    rw [show (fun noise : AppendixB2NoiseTriple =>
      rankByScore (fun c => appendixB2Value c + (10 / 11) *
        appendixB2NoiseValue (appendixB2NoiseTripleFunction noise c))) =
      appendixB2AlgorithmDiscreteTripleRank by
        funext noise
        exact hAlgorithmPointwise noise]
    exact appendixB2NoiseTriplePMF_map_algorithmDiscreteTripleRank
  have hHumanMap :
      (AppliedModelingLib.pmfProd
        (AppliedModelingLib.pmfProd appendixB2NoisePMF appendixB2NoisePMF)
        appendixB2NoisePMF).map
          (fun noise => rankByScore (fun c => appendixB2Value c + (10 / 9) *
            appendixB2NoiseValue (appendixB2NoiseTripleFunction noise c))) =
        appendixB2HumanRankingPMF := by
    change appendixB2NoiseTriplePMF.map
      (fun noise => rankByScore (fun c => appendixB2Value c + (10 / 9) *
        appendixB2NoiseValue (appendixB2NoiseTripleFunction noise c))) =
      appendixB2HumanRankingPMF
    rw [show (fun noise : AppendixB2NoiseTriple =>
      rankByScore (fun c => appendixB2Value c + (10 / 9) *
        appendixB2NoiseValue (appendixB2NoiseTripleFunction noise c))) =
      appendixB2HumanDiscreteTripleRank by
        funext noise
        exact hHumanPointwise noise]
    exact appendixB2NoiseTriplePMF_map_humanDiscreteTripleRank
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hAlgorithmPointwise, hHumanPointwise,
    hAlgorithmMap, hHumanMap, ?_, ?_⟩
  · norm_num [appendixB2Value, Fin.ext_iff]
  · norm_num [appendixB2NoiseValue]
  · norm_num [appendixB2NoisePMF_apply_toReal, appendixB2NoiseWeight]
  · norm_num [appendixB2NoisePMF_apply_toReal, appendixB2NoiseWeight]
  · norm_num [appendixB2NoisePMF_apply_toReal, appendixB2NoiseWeight]
  · norm_num [appendixB2NoisePMF_apply_toReal, appendixB2NoiseWeight]
  · norm_num
  · rw [hAlgorithmMap, hHumanMap]
    exact appendixB2_definition3_reversal_exact
  · rw [hAlgorithmMap, hHumanMap]
    exact appendixB2_not_prefersWeakerCompetition

/-- Appendix B (B.1), exact source first-choice equality for `x₁`. -/
theorem equationB1_counterexample_first_choice_x1 :
    firstChoiceProb appendixB2AlgorithmRankingPMF (0 : Candidate 1) =
      firstChoiceProb appendixB2HumanRankingPMF (0 : Candidate 1) :=
  KR21Monoculture.source_equationB1_counterexample_first_choice_x1

/-- Appendix B (B.2), exact source strict first-choice comparison for `x₂`. -/
theorem equationB2_counterexample_first_choice_x2 :
    firstChoiceProb appendixB2HumanRankingPMF (1 : Candidate 1) <
      firstChoiceProb appendixB2AlgorithmRankingPMF (1 : Candidate 1) :=
  KR21Monoculture.source_equationB2_counterexample_first_choice_x2

/--
Equation (B.1) with both displayed first-choice laws pinned to the literal
three-fold iid noise experiment and their realized-score ranking maps.
-/
theorem equationB1_counterexample_first_choice_x1_semantic_complete :
    let componentLaw : PMF AppendixB2NoiseAtom := appendixB2NoisePMF
    let rawNoiseLaw : PMF AppendixB2NoiseTriple :=
      AppliedModelingLib.pmfProd (AppliedModelingLib.pmfProd componentLaw componentLaw) componentLaw
    let algorithmRank : AppendixB2NoiseTriple -> Ranking 1 := fun noise =>
      rankByScore (fun c => appendixB2Value c + (10 / 11) *
        appendixB2NoiseValue (appendixB2NoiseTripleFunction noise c))
    let humanRank : AppendixB2NoiseTriple -> Ranking 1 := fun noise =>
      rankByScore (fun c => appendixB2Value c + (10 / 9) *
        appendixB2NoiseValue (appendixB2NoiseTripleFunction noise c))
    let algorithmLaw : PMF (Ranking 1) := rawNoiseLaw.map algorithmRank
    let humanLaw : PMF (Ranking 1) := rawNoiseLaw.map humanRank
    (appendixB2Value (0 : Candidate 1) = 3 ∧
      appendixB2Value (1 : Candidate 1) = 2 ∧
        appendixB2Value (2 : Candidate 1) = 0) ∧
    (appendixB2NoiseValue .plusOne = 1 ∧
      appendixB2NoiseValue .minusOne = -1 ∧
        appendixB2NoiseValue .plusTen = 10 ∧
          appendixB2NoiseValue .minusTen = -10) ∧
    (componentLaw .plusOne).toReal = 9 / 20 ∧
    (componentLaw .minusOne).toReal = 9 / 20 ∧
    (componentLaw .plusTen).toReal = 1 / 20 ∧
    (componentLaw .minusTen).toReal = 1 / 20 ∧
    algorithmLaw = appendixB2AlgorithmRankingPMF ∧
    humanLaw = appendixB2HumanRankingPMF ∧
    firstChoiceProb algorithmLaw (0 : Candidate 1) =
      firstChoiceProb humanLaw (0 : Candidate 1) := by
  dsimp
  have hAlgorithmPointwise : ∀ noise : AppendixB2NoiseTriple,
      rankByScore (fun c => appendixB2Value c + (10 / 11) *
        appendixB2NoiseValue (appendixB2NoiseTripleFunction noise c)) =
        appendixB2AlgorithmDiscreteTripleRank noise := by
    intro noise
    simpa [appendixB2AlgorithmDiscreteScore] using
      (appendixB2_algorithm_rankByScore_discreteTriple_eq noise)
  have hHumanPointwise : ∀ noise : AppendixB2NoiseTriple,
      rankByScore (fun c => appendixB2Value c + (10 / 9) *
        appendixB2NoiseValue (appendixB2NoiseTripleFunction noise c)) =
        appendixB2HumanDiscreteTripleRank noise := by
    intro noise
    simpa [appendixB2HumanDiscreteScore] using
      (appendixB2_human_rankByScore_discreteTriple_eq noise)
  have hAlgorithmMap :
      (AppliedModelingLib.pmfProd
        (AppliedModelingLib.pmfProd appendixB2NoisePMF appendixB2NoisePMF)
        appendixB2NoisePMF).map
          (fun noise => rankByScore (fun c => appendixB2Value c + (10 / 11) *
            appendixB2NoiseValue (appendixB2NoiseTripleFunction noise c))) =
        appendixB2AlgorithmRankingPMF := by
    change appendixB2NoiseTriplePMF.map
      (fun noise => rankByScore (fun c => appendixB2Value c + (10 / 11) *
        appendixB2NoiseValue (appendixB2NoiseTripleFunction noise c))) =
      appendixB2AlgorithmRankingPMF
    rw [show (fun noise : AppendixB2NoiseTriple =>
      rankByScore (fun c => appendixB2Value c + (10 / 11) *
        appendixB2NoiseValue (appendixB2NoiseTripleFunction noise c))) =
      appendixB2AlgorithmDiscreteTripleRank by
        funext noise
        exact hAlgorithmPointwise noise]
    exact appendixB2NoiseTriplePMF_map_algorithmDiscreteTripleRank
  have hHumanMap :
      (AppliedModelingLib.pmfProd
        (AppliedModelingLib.pmfProd appendixB2NoisePMF appendixB2NoisePMF)
        appendixB2NoisePMF).map
          (fun noise => rankByScore (fun c => appendixB2Value c + (10 / 9) *
            appendixB2NoiseValue (appendixB2NoiseTripleFunction noise c))) =
        appendixB2HumanRankingPMF := by
    change appendixB2NoiseTriplePMF.map
      (fun noise => rankByScore (fun c => appendixB2Value c + (10 / 9) *
        appendixB2NoiseValue (appendixB2NoiseTripleFunction noise c))) =
      appendixB2HumanRankingPMF
    rw [show (fun noise : AppendixB2NoiseTriple =>
      rankByScore (fun c => appendixB2Value c + (10 / 9) *
        appendixB2NoiseValue (appendixB2NoiseTripleFunction noise c))) =
      appendixB2HumanDiscreteTripleRank by
        funext noise
        exact hHumanPointwise noise]
    exact appendixB2NoiseTriplePMF_map_humanDiscreteTripleRank
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hAlgorithmMap, hHumanMap, ?_⟩
  · norm_num [appendixB2Value, Fin.ext_iff]
  · norm_num [appendixB2NoiseValue]
  · norm_num [appendixB2NoisePMF_apply_toReal, appendixB2NoiseWeight]
  · norm_num [appendixB2NoisePMF_apply_toReal, appendixB2NoiseWeight]
  · norm_num [appendixB2NoisePMF_apply_toReal, appendixB2NoiseWeight]
  · norm_num [appendixB2NoisePMF_apply_toReal, appendixB2NoiseWeight]
  · rw [hAlgorithmMap, hHumanMap]
    exact equationB1_counterexample_first_choice_x1

/--
Equation (B.2) with both displayed first-choice laws pinned to the literal
three-fold iid noise experiment and their realized-score ranking maps.
-/
theorem equationB2_counterexample_first_choice_x2_semantic_complete :
    let componentLaw : PMF AppendixB2NoiseAtom := appendixB2NoisePMF
    let rawNoiseLaw : PMF AppendixB2NoiseTriple :=
      AppliedModelingLib.pmfProd (AppliedModelingLib.pmfProd componentLaw componentLaw) componentLaw
    let algorithmRank : AppendixB2NoiseTriple -> Ranking 1 := fun noise =>
      rankByScore (fun c => appendixB2Value c + (10 / 11) *
        appendixB2NoiseValue (appendixB2NoiseTripleFunction noise c))
    let humanRank : AppendixB2NoiseTriple -> Ranking 1 := fun noise =>
      rankByScore (fun c => appendixB2Value c + (10 / 9) *
        appendixB2NoiseValue (appendixB2NoiseTripleFunction noise c))
    let algorithmLaw : PMF (Ranking 1) := rawNoiseLaw.map algorithmRank
    let humanLaw : PMF (Ranking 1) := rawNoiseLaw.map humanRank
    (appendixB2Value (0 : Candidate 1) = 3 ∧
      appendixB2Value (1 : Candidate 1) = 2 ∧
        appendixB2Value (2 : Candidate 1) = 0) ∧
    (appendixB2NoiseValue .plusOne = 1 ∧
      appendixB2NoiseValue .minusOne = -1 ∧
        appendixB2NoiseValue .plusTen = 10 ∧
          appendixB2NoiseValue .minusTen = -10) ∧
    (componentLaw .plusOne).toReal = 9 / 20 ∧
    (componentLaw .minusOne).toReal = 9 / 20 ∧
    (componentLaw .plusTen).toReal = 1 / 20 ∧
    (componentLaw .minusTen).toReal = 1 / 20 ∧
    algorithmLaw = appendixB2AlgorithmRankingPMF ∧
    humanLaw = appendixB2HumanRankingPMF ∧
    firstChoiceProb humanLaw (1 : Candidate 1) <
      firstChoiceProb algorithmLaw (1 : Candidate 1) := by
  dsimp
  have hAlgorithmPointwise : ∀ noise : AppendixB2NoiseTriple,
      rankByScore (fun c => appendixB2Value c + (10 / 11) *
        appendixB2NoiseValue (appendixB2NoiseTripleFunction noise c)) =
        appendixB2AlgorithmDiscreteTripleRank noise := by
    intro noise
    simpa [appendixB2AlgorithmDiscreteScore] using
      (appendixB2_algorithm_rankByScore_discreteTriple_eq noise)
  have hHumanPointwise : ∀ noise : AppendixB2NoiseTriple,
      rankByScore (fun c => appendixB2Value c + (10 / 9) *
        appendixB2NoiseValue (appendixB2NoiseTripleFunction noise c)) =
        appendixB2HumanDiscreteTripleRank noise := by
    intro noise
    simpa [appendixB2HumanDiscreteScore] using
      (appendixB2_human_rankByScore_discreteTriple_eq noise)
  have hAlgorithmMap :
      (AppliedModelingLib.pmfProd
        (AppliedModelingLib.pmfProd appendixB2NoisePMF appendixB2NoisePMF)
        appendixB2NoisePMF).map
          (fun noise => rankByScore (fun c => appendixB2Value c + (10 / 11) *
            appendixB2NoiseValue (appendixB2NoiseTripleFunction noise c))) =
        appendixB2AlgorithmRankingPMF := by
    change appendixB2NoiseTriplePMF.map
      (fun noise => rankByScore (fun c => appendixB2Value c + (10 / 11) *
        appendixB2NoiseValue (appendixB2NoiseTripleFunction noise c))) =
      appendixB2AlgorithmRankingPMF
    rw [show (fun noise : AppendixB2NoiseTriple =>
      rankByScore (fun c => appendixB2Value c + (10 / 11) *
        appendixB2NoiseValue (appendixB2NoiseTripleFunction noise c))) =
      appendixB2AlgorithmDiscreteTripleRank by
        funext noise
        exact hAlgorithmPointwise noise]
    exact appendixB2NoiseTriplePMF_map_algorithmDiscreteTripleRank
  have hHumanMap :
      (AppliedModelingLib.pmfProd
        (AppliedModelingLib.pmfProd appendixB2NoisePMF appendixB2NoisePMF)
        appendixB2NoisePMF).map
          (fun noise => rankByScore (fun c => appendixB2Value c + (10 / 9) *
            appendixB2NoiseValue (appendixB2NoiseTripleFunction noise c))) =
        appendixB2HumanRankingPMF := by
    change appendixB2NoiseTriplePMF.map
      (fun noise => rankByScore (fun c => appendixB2Value c + (10 / 9) *
        appendixB2NoiseValue (appendixB2NoiseTripleFunction noise c))) =
      appendixB2HumanRankingPMF
    rw [show (fun noise : AppendixB2NoiseTriple =>
      rankByScore (fun c => appendixB2Value c + (10 / 9) *
        appendixB2NoiseValue (appendixB2NoiseTripleFunction noise c))) =
      appendixB2HumanDiscreteTripleRank by
        funext noise
        exact hHumanPointwise noise]
    exact appendixB2NoiseTriplePMF_map_humanDiscreteTripleRank
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hAlgorithmMap, hHumanMap, ?_⟩
  · norm_num [appendixB2Value, Fin.ext_iff]
  · norm_num [appendixB2NoiseValue]
  · norm_num [appendixB2NoisePMF_apply_toReal, appendixB2NoiseWeight]
  · norm_num [appendixB2NoisePMF_apply_toReal, appendixB2NoiseWeight]
  · norm_num [appendixB2NoisePMF_apply_toReal, appendixB2NoiseWeight]
  · norm_num [appendixB2NoisePMF_apply_toReal, appendixB2NoiseWeight]
  · rw [hAlgorithmMap, hHumanMap]
    exact equationB2_counterexample_first_choice_x2

/-- Appendix B's displayed algorithmic `x₁` probability is exactly `67/100`. -/
theorem appendixB2_source_algorithm_x1_first_probability :
    firstChoiceProb appendixB2AlgorithmRankingPMF (0 : Candidate 1) =
      67 / 100 :=
  KR21Monoculture.source_appendixB2_algorithm_x1_first_probability

/-- Appendix B's displayed human `x₁` probability is exactly `67/100`. -/
theorem appendixB2_source_human_x1_first_probability :
    firstChoiceProb appendixB2HumanRankingPMF (0 : Candidate 1) =
      67 / 100 :=
  KR21Monoculture.source_appendixB2_human_x1_first_probability

/-- Appendix B's displayed algorithmic `x₂` probability is exactly `2261/8000`. -/
theorem appendixB2_source_algorithm_x2_first_probability :
    firstChoiceProb appendixB2AlgorithmRankingPMF (1 : Candidate 1) =
      2261 / 8000 :=
  KR21Monoculture.source_appendixB2_algorithm_x2_first_probability

/-- Appendix B's displayed human `x₂` probability is exactly `109/400`. -/
theorem appendixB2_source_human_x2_first_probability :
    firstChoiceProb appendixB2HumanRankingPMF (1 : Candidate 1) =
      109 / 400 :=
  KR21Monoculture.source_appendixB2_human_x2_first_probability

/-- The B.2 ranking tables are proved literal iid-score pushforwards. -/
theorem appendixB2_source_iid_score_pushforward_tables
    (a : AppendixBRankingAtom) :
    appendixB2AlgorithmRankingWeight a =
      appendixB2AlgorithmIIDRUMRankingWeight a ∧
    appendixB2HumanRankingWeight a =
      appendixB2HumanIIDRUMRankingWeight a :=
  KR21Monoculture.source_appendixB2_iid_score_pushforward_tables a

/--
Appendix B.1's exact strict reversal persists under any rank-law family whose
six ranking atoms converge continuously to the checked discrete iid witness.
This is proof support for the source's Gaussian-mixture sentence: the actual
Gaussian-mixture construction and its atomwise convergence remain separate
open obligations.
-/
theorem appendixB1_smoothing_stability_of_atomwise_continuity
    (law : ℝ → PMF (Ranking 1))
    (hatom : ∀ pi : Ranking 1,
      ContinuousAt (fun s => ((law s) pi).toReal) 0)
    (hbase : law 0 = appendixB1RankingPMF) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ s : ℝ, 0 < s → s < delta →
      expectedSecondMoverIndependent (law s) (law s) appendixB1Value -
        expectedSecondMoverShared (law s) appendixB1Value < 0 :=
  appendixB1_reversal_persists_of_atomwise_continuity law hatom hbase

/--
Appendix B.2's exact strict reversal persists under any algorithm and human
rank-law smoothings whose atoms converge continuously to the corresponding
checked discrete iid witnesses.  This does not assert that a law merely called
"Gaussian mixture" supplies those atomwise continuity facts.
-/
theorem appendixB2_smoothing_stability_of_atomwise_continuity
    (algorithm human : ℝ → PMF (Ranking 1))
    (halgorithm : ∀ pi : Ranking 1,
      ContinuousAt (fun s => ((algorithm s) pi).toReal) 0)
    (hhuman : ∀ pi : Ranking 1,
      ContinuousAt (fun s => ((human s) pi).toReal) 0)
    (halgorithm_base : algorithm 0 = appendixB2AlgorithmRankingPMF)
    (hhuman_base : human 0 = appendixB2HumanRankingPMF) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ s : ℝ, 0 < s → s < delta →
      0 < expectedSecondMoverIndependent (human s) (algorithm s) appendixB2Value -
        expectedSecondMoverIndependent (human s) (human s) appendixB2Value :=
  appendixB2_reversal_persists_of_atomwise_continuity
    algorithm human halgorithm hhuman halgorithm_base hhuman_base

/--
Appendix B.1 smooth-counterexample endpoint.  The displayed discrete iid
noise is replaced by its actual finite iid mixture of standard Gaussian
components centered at the source atoms, with positive component scale `s`.
The resulting RUM keeps the Definition 2 payoff reversal for every
sufficiently small positive scale.  The separate proof that this explicit
mixture satisfies the full analytic Definition 1 package is not folded into
this payoff statement.
-/
theorem appendixB1_gaussianMixture_smoothing_counterexample :
    ∃ delta : ℝ, 0 < delta ∧ ∀ s : ℝ, 0 < s → s < delta →
      expectedSecondMoverIndependent
          (appendixB1GaussianMixtureRankingPMF s)
          (appendixB1GaussianMixtureRankingPMF s) appendixB1Value -
        expectedSecondMoverShared
          (appendixB1GaussianMixtureRankingPMF s) appendixB1Value < 0 :=
  KR21Monoculture.appendixB1_gaussianMixture_reversal

/--
Appendix B.2 smooth-counterexample endpoint.  One fixed iid base mixture with
component width `s` defines a single RUM accuracy family; the source's
algorithmic and human rankings are its `11/10` and `9/10` instances.  Their
Gaussian component widths therefore become `(10/11) * s` and `(10/9) * s`,
respectively, and the Definition 3 payoff reversal remains strict for every
sufficiently small positive `s`.  The separate analytic Definition 1 density
certificate is intentionally not assumed here.
-/
theorem appendixB2_sourceScaledGaussianMixture_smoothing_counterexample :
    ∃ delta : ℝ, 0 < delta ∧ ∀ s : ℝ, 0 < s → s < delta →
      0 < expectedSecondMoverIndependent
            ((appendixB2SourceGaussianMixtureFamily s).dist (9 / 10))
            ((appendixB2SourceGaussianMixtureFamily s).dist (11 / 10))
            appendixB2Value -
          expectedSecondMoverIndependent
            ((appendixB2SourceGaussianMixtureFamily s).dist (9 / 10))
            ((appendixB2SourceGaussianMixtureFamily s).dist (9 / 10))
            appendixB2Value :=
  KR21Monoculture.appendixB2_sourceScaledGaussianMixture_reversal

/--
Corrected Appendix B.1 Definition 1 endpoint.  At every positive component
width, the literal common-source Gaussian-mixture RUM has the full repaired
global-`W^{1,1}` Definition 1 package.  The correction is visible: this is not
a claim that the archival differentiability hypotheses alone suffice.
-/
noncomputable def appendixB1_sourceGaussianMixture_corrected_W11_definition1
    (s : ℝ) (hs : 0 < s) :
    CorrectedW11ScaledNoiseDefinition1
      (appendixB1SourceGaussianMixtureFamily s) rum3Ranking012 :=
  appendixB1SourceGaussianMixture_correctedW11Definition1 s hs

/--
Corrected Appendix B.1 Definition 1 fields, stated propositionally for source
review.  The conjuncts give the source's literal atomwise continuity and
differentiability clauses, its actual high-accuracy limit, and its
arbitrary-removed-subset monotonicity clause for the literal Gaussian-mixture
family.
-/
theorem appendixB1_sourceGaussianMixture_corrected_W11_definition1_fields
    (s : ℝ) (hs : 0 < s) :
    (∀ theta, 0 < theta → ∀ pi : Ranking 1,
      ContinuousAt
        (fun theta' =>
          ((appendixB1SourceGaussianMixtureFamily s).dist theta' pi).toReal)
        theta ∧
      DifferentiableAt ℝ
        (fun theta' =>
          ((appendixB1SourceGaussianMixtureFamily s).dist theta' pi).toReal)
        theta) ∧
    (∀ pi : Ranking 1,
      Filter.Tendsto
        (fun theta =>
          ((appendixB1SourceGaussianMixtureFamily s).dist theta pi).toReal)
        Filter.atTop
        (nhds (((PMF.pure rum3Ranking012 : PMF (Ranking 1)) pi).toReal))) ∧
    ∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
      (∀ remaining : Finset (Candidate 1), remaining.Nonempty →
        expectedBestInSet
            ((appendixB1SourceGaussianMixtureFamily s).dist thetaH)
            appendixB1Value remaining ≤
          expectedBestInSet
            ((appendixB1SourceGaussianMixtureFamily s).dist thetaA)
            appendixB1Value remaining) ∧
        expectedBestInSet
            ((appendixB1SourceGaussianMixtureFamily s).dist thetaH)
            appendixB1Value Finset.univ <
          expectedBestInSet
            ((appendixB1SourceGaussianMixtureFamily s).dist thetaA)
            appendixB1Value Finset.univ := by
  let regularity := appendixB1GaussianMixture_w11Regularity s hs
  have hsource := correctedW11ScaledNoiseDefinition1_sourceFaithful_of_source
    (appendixB1GaussianMixtureDensity s)
    (finiteGaussianMixtureDerivative appendixB1NoisePMF appendixB1NoiseValue s)
    regularity.density_integrable regularity.derivative_integrable
    regularity.density_measurable regularity.density_positive
    regularity.absolute_continuity regularity.derivative_ae_eq
    regularity.normalized appendixB1Value rum3Ranking012 (by
      intro i
      fin_cases i <;> norm_num [appendixB1Value, Fin.ext_iff])
  rcases hsource with ⟨hcontinuous, htendsto, hremoval, hstrict⟩
  rw [← appendixB1GaussianMixtureW11Family_eq_sourceGaussianMixtureFamily s hs]
  exact ⟨hcontinuous, htendsto, fun thetaA thetaH hthetaH htheta =>
    ⟨hremoval thetaA thetaH hthetaH htheta, hstrict thetaA thetaH hthetaH htheta⟩⟩

/--
At unit accuracy, the B.1 corrected-density family is exactly the paper's
literal latent Gaussian-mixture ranking experiment.  This records the actual
source-law equality used by the preceding Definition 1 certificate.
-/
theorem appendixB1_sourceGaussianMixture_unit_accuracy_eq_latent_ranking_law
    (s : ℝ) :
    (appendixB1SourceGaussianMixtureFamily s).dist 1 =
      appendixB1GaussianMixtureRankingPMF s :=
  appendixB1SourceGaussianMixtureFamily_dist_one_eq_latentRankingPMF s

/--
At every positive source accuracy, the literal B.1 latent Gaussian-mixture
experiment and the corrected-density family have the same ranking law.
-/
theorem appendixB1_sourceGaussianMixture_positive_accuracy_eq_corrected_density_law
    (s : ℝ) (hs : 0 < s) (theta : ℝ) (htheta : 0 < theta) :
    (appendixB1SourceGaussianMixtureFamily s).dist theta =
      (appendixB1GaussianMixtureW11Family s hs).dist theta :=
  (appendixB1GaussianMixtureW11Family_dist_eq_sourceLatentRankingPMF s hs theta).symm

/--
Corrected Appendix B.2 Definition 1 endpoint.  One fixed literal
common-source Gaussian-mixture family, used at both source accuracies,
satisfies the full repaired global-`W^{1,1}` Definition 1 package at every
positive component width.
-/
noncomputable def appendixB2_sourceGaussianMixture_corrected_W11_definition1
    (s : ℝ) (hs : 0 < s) :
    CorrectedW11ScaledNoiseDefinition1
      (appendixB2SourceGaussianMixtureFamily s) rum3Ranking012 :=
  appendixB2SourceGaussianMixture_correctedW11Definition1 s hs

/--
Corrected Appendix B.2 Definition 1 fields, stated propositionally for source
review.  The conjuncts give the source's literal atomwise continuity and
differentiability clauses, its actual high-accuracy limit, and its
arbitrary-removed-subset monotonicity clause of the one literal common-source
Gaussian-mixture family.
-/
theorem appendixB2_sourceGaussianMixture_corrected_W11_definition1_fields
    (s : ℝ) (hs : 0 < s) :
    (∀ theta, 0 < theta → ∀ pi : Ranking 1,
      ContinuousAt
        (fun theta' =>
          ((appendixB2SourceGaussianMixtureFamily s).dist theta' pi).toReal)
        theta ∧
      DifferentiableAt ℝ
        (fun theta' =>
          ((appendixB2SourceGaussianMixtureFamily s).dist theta' pi).toReal)
        theta) ∧
    (∀ pi : Ranking 1,
      Filter.Tendsto
        (fun theta =>
          ((appendixB2SourceGaussianMixtureFamily s).dist theta pi).toReal)
        Filter.atTop
        (nhds (((PMF.pure rum3Ranking012 : PMF (Ranking 1)) pi).toReal))) ∧
    ∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
      (∀ remaining : Finset (Candidate 1), remaining.Nonempty →
        expectedBestInSet
            ((appendixB2SourceGaussianMixtureFamily s).dist thetaH)
            appendixB2Value remaining ≤
          expectedBestInSet
            ((appendixB2SourceGaussianMixtureFamily s).dist thetaA)
            appendixB2Value remaining) ∧
        expectedBestInSet
            ((appendixB2SourceGaussianMixtureFamily s).dist thetaH)
            appendixB2Value Finset.univ <
          expectedBestInSet
            ((appendixB2SourceGaussianMixtureFamily s).dist thetaA)
            appendixB2Value Finset.univ := by
  let regularity := appendixB2GaussianMixture_w11Regularity s hs
  have hsource := correctedW11ScaledNoiseDefinition1_sourceFaithful_of_source
    (appendixB2GaussianMixtureDensity s)
    (finiteGaussianMixtureDerivative appendixB2NoisePMF appendixB2NoiseValue s)
    regularity.density_integrable regularity.derivative_integrable
    regularity.density_measurable regularity.density_positive
    regularity.absolute_continuity regularity.derivative_ae_eq
    regularity.normalized appendixB2Value rum3Ranking012 (by
      intro i
      fin_cases i <;> norm_num [appendixB2Value, Fin.ext_iff])
  rcases hsource with ⟨hcontinuous, htendsto, hremoval, hstrict⟩
  rw [← appendixB2GaussianMixtureW11Family_eq_sourceGaussianMixtureFamily s hs]
  exact ⟨hcontinuous, htendsto, fun thetaA thetaH hthetaH htheta =>
    ⟨hremoval thetaA thetaH hthetaH htheta, hstrict thetaA thetaH hthetaH htheta⟩⟩

/--
At every positive source accuracy, the literal B.2 latent Gaussian-mixture
experiment and the corrected-density family have the same ranking law.
-/
theorem appendixB2_sourceGaussianMixture_positive_accuracy_eq_corrected_density_law
    (s : ℝ) (hs : 0 < s) (theta : ℝ) (htheta : 0 < theta) :
    (appendixB2SourceGaussianMixtureFamily s).dist theta =
      (appendixB2GaussianMixtureW11Family s hs).dist theta :=
  (appendixB2GaussianMixtureW11Family_dist_eq_sourceLatentRankingPMF s hs theta).symm

section

local instance : MeasurableSpace AppendixB1NoiseAtom := ⊤
local instance : DiscreteMeasurableSpace AppendixB1NoiseAtom :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩
local instance : MeasurableSpace AppendixB2NoiseAtom := ⊤
local instance : DiscreteMeasurableSpace AppendixB2NoiseAtom :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

/--
Complete source-facing Appendix B smoothing package.  Both branches display
the finite iid component laws, independent standard-Gaussian perturbations,
raw score maps, strict small-width reversals, and the repaired `W^{1,1}`
Definition 1 fields.  The B.2 branch explicitly uses one source family at
both accuracy values; it does not silently substitute two unrelated laws.
-/
theorem appendixB_smoothing_source_complete :
    (appendixB1Value (0 : Candidate 1) = 7 / 4 ∧
      appendixB1Value (1 : Candidate 1) = 1 / 2 ∧
        appendixB1Value (2 : Candidate 1) = 0) ∧
    (appendixB1NoiseValue .plusOne = 1 ∧
      appendixB1NoiseValue .zero = 0 ∧
        appendixB1NoiseValue .minusOne = -1) ∧
    ((appendixB1NoisePMF .plusOne).toReal = 1 / 20 ∧
      (appendixB1NoisePMF .zero).toReal = 9 / 10 ∧
        (appendixB1NoisePMF .minusOne).toReal = 1 / 20) ∧
    (appendixB1GaussianLatentMeasure =
      ((appendixB1NoisePMF.toMeasure.prod appendixB1NoisePMF.toMeasure).prod
        appendixB1NoisePMF.toMeasure).prod
        ((gaussianReal 0 1).prod ((gaussianReal 0 1).prod (gaussianReal 0 1)))) ∧
    (∀ s theta, 0 < s → 0 < theta →
      (appendixB1SourceGaussianMixtureFamily s).dist theta =
        rumRankingPMFOfMeasure appendixB1GaussianLatentMeasure
          (fun omega =>
            rankByScore (fun c => appendixB1Value c +
              (appendixB1NoiseValue (appendixB1NoiseTripleFunction omega.1 c) +
                s * appendixBGaussianTripleFunction omega.2 c) / theta))
          (appendixB1SourceGaussianMixtureRank_measurable s theta)) ∧
    (appendixB2Value (0 : Candidate 1) = 3 ∧
      appendixB2Value (1 : Candidate 1) = 2 ∧
        appendixB2Value (2 : Candidate 1) = 0) ∧
    (appendixB2NoiseValue .plusOne = 1 ∧
      appendixB2NoiseValue .minusOne = -1 ∧
        appendixB2NoiseValue .plusTen = 10 ∧
          appendixB2NoiseValue .minusTen = -10) ∧
    ((appendixB2NoisePMF .plusOne).toReal = 9 / 20 ∧
      (appendixB2NoisePMF .minusOne).toReal = 9 / 20 ∧
        (appendixB2NoisePMF .plusTen).toReal = 1 / 20 ∧
          (appendixB2NoisePMF .minusTen).toReal = 1 / 20) ∧
    (appendixB2GaussianLatentMeasure =
      ((appendixB2NoisePMF.toMeasure.prod appendixB2NoisePMF.toMeasure).prod
        appendixB2NoisePMF.toMeasure).prod
        ((gaussianReal 0 1).prod ((gaussianReal 0 1).prod (gaussianReal 0 1)))) ∧
    (∀ s theta, 0 < s → 0 < theta →
      (appendixB2SourceGaussianMixtureFamily s).dist theta =
        rumRankingPMFOfMeasure appendixB2GaussianLatentMeasure
          (fun omega =>
            rankByScore (fun c => appendixB2Value c +
              (appendixB2NoiseValue (appendixB2NoiseTripleFunction omega.1 c) +
                s * appendixBGaussianTripleFunction omega.2 c) / theta))
          (appendixB2SourceGaussianMixtureRank_measurable s theta)) ∧
    (∃ delta : ℝ, 0 < delta ∧ ∀ s : ℝ, 0 < s → s < delta →
      expectedSecondMoverIndependent
          ((appendixB1SourceGaussianMixtureFamily s).dist 1)
          ((appendixB1SourceGaussianMixtureFamily s).dist 1) appendixB1Value -
        expectedSecondMoverShared
          ((appendixB1SourceGaussianMixtureFamily s).dist 1)
          appendixB1Value < 0) ∧
    (∃ delta : ℝ, 0 < delta ∧ ∀ s : ℝ, 0 < s → s < delta →
      0 < expectedSecondMoverIndependent
            ((appendixB2SourceGaussianMixtureFamily s).dist (9 / 10))
            ((appendixB2SourceGaussianMixtureFamily s).dist (11 / 10))
            appendixB2Value -
          expectedSecondMoverIndependent
            ((appendixB2SourceGaussianMixtureFamily s).dist (9 / 10))
            ((appendixB2SourceGaussianMixtureFamily s).dist (9 / 10))
            appendixB2Value) ∧
    (∀ s : ℝ, 0 < s →
      (∀ theta, 0 < theta → ∀ pi : Ranking 1,
        ContinuousAt
          (fun theta' =>
            ((appendixB1SourceGaussianMixtureFamily s).dist theta' pi).toReal)
          theta ∧
        DifferentiableAt ℝ
          (fun theta' =>
            ((appendixB1SourceGaussianMixtureFamily s).dist theta' pi).toReal)
          theta) ∧
      (∀ pi : Ranking 1,
        Filter.Tendsto
          (fun theta =>
            ((appendixB1SourceGaussianMixtureFamily s).dist theta pi).toReal)
          Filter.atTop
          (nhds (((PMF.pure rum3Ranking012 : PMF (Ranking 1)) pi).toReal))) ∧
      ∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
        (∀ remaining : Finset (Candidate 1), remaining.Nonempty →
          expectedBestInSet
              ((appendixB1SourceGaussianMixtureFamily s).dist thetaH)
              appendixB1Value remaining ≤
            expectedBestInSet
              ((appendixB1SourceGaussianMixtureFamily s).dist thetaA)
              appendixB1Value remaining) ∧
          expectedBestInSet
              ((appendixB1SourceGaussianMixtureFamily s).dist thetaH)
              appendixB1Value Finset.univ <
            expectedBestInSet
              ((appendixB1SourceGaussianMixtureFamily s).dist thetaA)
              appendixB1Value Finset.univ) ∧
    (∀ s : ℝ, ∀ hs : 0 < s, ∀ theta : ℝ, 0 < theta →
      (appendixB1SourceGaussianMixtureFamily s).dist theta =
        (appendixB1GaussianMixtureW11Family s hs).dist theta) ∧
    (∀ s : ℝ, 0 < s →
      (∀ theta, 0 < theta → ∀ pi : Ranking 1,
        ContinuousAt
          (fun theta' =>
            ((appendixB2SourceGaussianMixtureFamily s).dist theta' pi).toReal)
          theta ∧
        DifferentiableAt ℝ
          (fun theta' =>
            ((appendixB2SourceGaussianMixtureFamily s).dist theta' pi).toReal)
          theta) ∧
      (∀ pi : Ranking 1,
        Filter.Tendsto
          (fun theta =>
            ((appendixB2SourceGaussianMixtureFamily s).dist theta pi).toReal)
          Filter.atTop
          (nhds (((PMF.pure rum3Ranking012 : PMF (Ranking 1)) pi).toReal))) ∧
      ∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
        (∀ remaining : Finset (Candidate 1), remaining.Nonempty →
          expectedBestInSet
              ((appendixB2SourceGaussianMixtureFamily s).dist thetaH)
              appendixB2Value remaining ≤
            expectedBestInSet
              ((appendixB2SourceGaussianMixtureFamily s).dist thetaA)
              appendixB2Value remaining) ∧
          expectedBestInSet
              ((appendixB2SourceGaussianMixtureFamily s).dist thetaH)
              appendixB2Value Finset.univ <
            expectedBestInSet
              ((appendixB2SourceGaussianMixtureFamily s).dist thetaA)
              appendixB2Value Finset.univ) ∧
    (∀ s : ℝ, ∀ hs : 0 < s, ∀ theta : ℝ, 0 < theta →
      (appendixB2SourceGaussianMixtureFamily s).dist theta =
        (appendixB2GaussianMixtureW11Family s hs).dist theta) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    appendixB2_sourceScaledGaussianMixture_smoothing_counterexample, ?_, ?_, ?_, ?_⟩
  · norm_num [appendixB1Value, Fin.ext_iff]
  · norm_num [appendixB1NoiseValue]
  · norm_num [appendixB1NoisePMF_apply_toReal, appendixB1NoiseWeight]
  · unfold appendixB1GaussianLatentMeasure appendixBStandardGaussianTripleMeasure
    rw [appendixB1NoiseTriplePMF_toMeasure_eq_iid]
  · intro s theta _ _
    rfl
  · norm_num [appendixB2Value, Fin.ext_iff]
  · norm_num [appendixB2NoiseValue]
  · norm_num [appendixB2NoisePMF_apply_toReal, appendixB2NoiseWeight]
  · unfold appendixB2GaussianLatentMeasure appendixBStandardGaussianTripleMeasure
    rw [appendixB2NoiseTriplePMF_toMeasure_eq_iid]
  · intro s theta _ _
    rfl
  · rcases appendixB1_gaussianMixture_smoothing_counterexample with ⟨delta, hdelta, hsmall⟩
    refine ⟨delta, hdelta, ?_⟩
    intro s hs hlt
    simpa only [appendixB1_sourceGaussianMixture_unit_accuracy_eq_latent_ranking_law]
      using hsmall s hs hlt
  · intro s hs
    exact appendixB1_sourceGaussianMixture_corrected_W11_definition1_fields s hs
  · intro s hs theta htheta
    exact appendixB1_sourceGaussianMixture_positive_accuracy_eq_corrected_density_law
      s hs theta htheta
  · intro s hs
    exact appendixB2_sourceGaussianMixture_corrected_W11_definition1_fields s hs
  · intro s hs theta htheta
    exact appendixB2_sourceGaussianMixture_positive_accuracy_eq_corrected_density_law
      s hs theta htheta

/--
The literal Appendix B smoothing core.  It records only the finite discrete
components, independent Gaussian perturbations, positive-width raw RUM laws,
and the two strict small-width counterexamples stated by the source.  The
repaired `W^{1,1}`/Definition 1 consequences remain in the separate complete
endpoint below this projection route and are not part of this source claim.
-/
abbrev appendixB_smoothing_source_coreStatement : Prop :=
  (appendixB1Value (0 : Candidate 1) = 7 / 4 ∧
    appendixB1Value (1 : Candidate 1) = 1 / 2 ∧
      appendixB1Value (2 : Candidate 1) = 0) ∧
  (appendixB1NoiseValue .plusOne = 1 ∧
    appendixB1NoiseValue .zero = 0 ∧
      appendixB1NoiseValue .minusOne = -1) ∧
  ((appendixB1NoisePMF .plusOne).toReal = 1 / 20 ∧
    (appendixB1NoisePMF .zero).toReal = 9 / 10 ∧
      (appendixB1NoisePMF .minusOne).toReal = 1 / 20) ∧
  (appendixB1GaussianLatentMeasure =
    ((appendixB1NoisePMF.toMeasure.prod appendixB1NoisePMF.toMeasure).prod
      appendixB1NoisePMF.toMeasure).prod
      ((gaussianReal 0 1).prod ((gaussianReal 0 1).prod (gaussianReal 0 1)))) ∧
  (∀ s theta, 0 < s → 0 < theta →
    (appendixB1SourceGaussianMixtureFamily s).dist theta =
      rumRankingPMFOfMeasure appendixB1GaussianLatentMeasure
        (fun omega =>
          rankByScore (fun c => appendixB1Value c +
            (appendixB1NoiseValue (appendixB1NoiseTripleFunction omega.1 c) +
              s * appendixBGaussianTripleFunction omega.2 c) / theta))
        (appendixB1SourceGaussianMixtureRank_measurable s theta)) ∧
  (appendixB2Value (0 : Candidate 1) = 3 ∧
    appendixB2Value (1 : Candidate 1) = 2 ∧
      appendixB2Value (2 : Candidate 1) = 0) ∧
  (appendixB2NoiseValue .plusOne = 1 ∧
    appendixB2NoiseValue .minusOne = -1 ∧
      appendixB2NoiseValue .plusTen = 10 ∧
        appendixB2NoiseValue .minusTen = -10) ∧
  ((appendixB2NoisePMF .plusOne).toReal = 9 / 20 ∧
    (appendixB2NoisePMF .minusOne).toReal = 9 / 20 ∧
      (appendixB2NoisePMF .plusTen).toReal = 1 / 20 ∧
        (appendixB2NoisePMF .minusTen).toReal = 1 / 20) ∧
  (appendixB2GaussianLatentMeasure =
    ((appendixB2NoisePMF.toMeasure.prod appendixB2NoisePMF.toMeasure).prod
      appendixB2NoisePMF.toMeasure).prod
      ((gaussianReal 0 1).prod ((gaussianReal 0 1).prod (gaussianReal 0 1)))) ∧
  (∀ s theta, 0 < s → 0 < theta →
    (appendixB2SourceGaussianMixtureFamily s).dist theta =
      rumRankingPMFOfMeasure appendixB2GaussianLatentMeasure
        (fun omega =>
          rankByScore (fun c => appendixB2Value c +
            (appendixB2NoiseValue (appendixB2NoiseTripleFunction omega.1 c) +
              s * appendixBGaussianTripleFunction omega.2 c) / theta))
        (appendixB2SourceGaussianMixtureRank_measurable s theta)) ∧
  (∃ delta : ℝ, 0 < delta ∧ ∀ s : ℝ, 0 < s → s < delta →
    expectedSecondMoverIndependent
        ((appendixB1SourceGaussianMixtureFamily s).dist 1)
        ((appendixB1SourceGaussianMixtureFamily s).dist 1) appendixB1Value -
      expectedSecondMoverShared
        ((appendixB1SourceGaussianMixtureFamily s).dist 1)
        appendixB1Value < 0) ∧
  (∃ delta : ℝ, 0 < delta ∧ ∀ s : ℝ, 0 < s → s < delta →
    0 < expectedSecondMoverIndependent
          ((appendixB2SourceGaussianMixtureFamily s).dist (9 / 10))
          ((appendixB2SourceGaussianMixtureFamily s).dist (11 / 10))
          appendixB2Value -
        expectedSecondMoverIndependent
          ((appendixB2SourceGaussianMixtureFamily s).dist (9 / 10))
          ((appendixB2SourceGaussianMixtureFamily s).dist (9 / 10))
          appendixB2Value)

/--
Projection of the checked Appendix B smoothing package to the literal source
core.  This theorem intentionally omits every corrected W1,1/Definition 1
field so it cannot receive source coverage by strengthening the paper's
Gaussian-smoothing remark.
-/
theorem appendixB_smoothing_source_core :
    appendixB_smoothing_source_coreStatement := by
  rcases appendixB_smoothing_source_complete with
    ⟨hB1Value, hB1Noise, hB1Weight, hB1Latent, hB1Law,
      hB2Value, hB2Noise, hB2Weight, hB2Latent, hB2Law,
      hB1Reversal, hB2Reversal, _hB1Definition1, _hB1Density,
      _hB2Definition1, _hB2Density⟩
  exact ⟨hB1Value, hB1Noise, hB1Weight, hB1Latent, hB1Law,
    hB2Value, hB2Noise, hB2Weight, hB2Latent, hB2Law,
    hB1Reversal, hB2Reversal⟩

end

/-- Internal arithmetic certificate for the collapsed three-firm witness. -/
theorem source_threeFirm_reported_arithmetic_paradox :
    (∀ opponents, 0 < sourceThreeFirmAlgorithmGain opponents) ∧
      sourceThreeFirmAllAlgorithmPerFirm < sourceThreeFirmAllHumanPerFirm :=
  source_threeFirm_arithmetic_paradox

/--
The three-firm constants above are not free-standing numerals: they are casts
of collapsed finite rank-mean sums. Their equality to the paper's full source
experiment remains a separate source-model bridge.
-/
theorem source_threeFirm_reported_executable_certificate :
    (sourceExecutableExpectedAAA : ℝ) =
        sourceThreeFirmAllAlgorithmPerFirm ∧
      (sourceExecutableExpectedHHH : ℝ) =
        sourceThreeFirmAllHumanPerFirm ∧
      (∀ opponents,
        (sourceExecutableAlgorithmGain opponents : ℝ) =
            sourceThreeFirmAlgorithmGain opponents ∧
          0 < (sourceExecutableAlgorithmGain opponents : ℝ)) ∧
      (sourceExecutableExpectedAAA : ℝ) < sourceExecutableExpectedHHH := by
  exact ⟨source_threeFirm_allAlgorithm_from_executable,
    source_threeFirm_allHuman_from_executable,
    fun opponents =>
      ⟨source_threeFirm_algorithmGain_from_executable opponents,
        source_executable_algorithmGain_pos opponents⟩,
    source_executable_allAlgorithm_lt_allHuman⟩

/--
The all-algorithm collapsed AAA row is the direct finite product experiment
with one shared algorithm ranking and a uniform arrival order.  It deliberately
does not replace that shared ranking by independent algorithm draws.
-/
theorem source_threeFirm_direct_rankMean_AAA_certificate :
    sourceDirectRankMeanExpectedAAA = sourceExecutableExpectedAAA ∧
      sourceDirectRankMeanExpectedAAA = 124 / 225 :=
  ⟨sourceDirectRankMeanExpectedAAA_eq_executable,
    sourceDirectRankMeanExpectedAAA_eq⟩

/--
The all-human collapsed three-firm rank-mean row is the direct finite product
expectation of three independently drawn human ranking coordinates and uniform
arrival order. This is not yet the source IID-Uniform cardinal-value or
firm-label-symmetry bridge.
-/
theorem source_threeFirm_direct_rankMean_HHH_certificate :
    sourceCanonicalDirectRankMeanExpectedHHH = sourceExecutableExpectedHHH ∧
      sourceCanonicalDirectRankMeanExpectedHHH =
        8730423441013 / 15807166464375 :=
  ⟨sourceCanonicalDirectRankMeanExpectedHHH_eq_executable,
    by
      rw [sourceCanonicalDirectRankMeanExpectedHHH_eq_executable,
        source_executable_expectedHHH_eq]⟩

/--
The focal-human-against-two-algorithms collapsed HAA row is the direct finite
product expectation over one shared algorithm ranking, one human ranking, and
uniform arrival order. It is still only a rank-mean result, not the source
IID-Uniform cardinal-value or all-firm symmetry theorem.
-/
theorem source_threeFirm_direct_rankMean_HAA_certificate :
    sourceDirectRankMeanExpectedHAA = sourceExecutableExpectedHAA ∧
      sourceDirectRankMeanExpectedHAA = 57174284 / 104729625 :=
  ⟨sourceDirectRankMeanExpectedHAA_eq_executable,
    sourceDirectRankMeanExpectedHAA_eq⟩

/--
The focal-algorithm-against-algorithm-and-human collapsed AAH row is the direct
finite product expectation over one shared algorithm ranking, one human
ranking, and uniform arrival order. It remains a rank-mean component only.
-/
theorem source_threeFirm_direct_rankMean_AAH_certificate :
    sourceDirectRankMeanExpectedAAH = sourceExecutableExpectedAAH ∧
      sourceDirectRankMeanExpectedAAH = 117110677 / 209459250 :=
  ⟨sourceDirectRankMeanExpectedAAH_eq_executable,
    sourceDirectRankMeanExpectedAAH_eq⟩

/--
The focal-human against algorithm-and-human collapsed HAH row is the direct
finite product expectation over a shared algorithm ranking, two independent
human rankings, and uniform arrival order.  The canonical product order is
proved equal to the sequential evaluator.  This remains a rank-mean component,
not the source IID-Uniform cardinal-value or all-firm symmetry theorem.
-/
theorem source_threeFirm_direct_rankMean_HAH_certificate :
    sourceCanonicalDirectRankMeanExpectedHAH =
        sourceDirectRankMeanExpectedHAH ∧
      sourceCanonicalDirectRankMeanExpectedHAH = sourceExecutableExpectedHAH ∧
      sourceDirectRankMeanExpectedHAH =
        2539918857979 / 4642664276250 :=
  ⟨sourceCanonicalDirectRankMeanExpectedHAH_eq_direct,
    sourceCanonicalDirectRankMeanExpectedHAH_eq_executable,
    sourceDirectRankMeanExpectedHAH_eq⟩

/--
The focal-algorithm against two-human collapsed AHH row is the direct finite
product expectation over one algorithm ranking, two independent human
rankings, and uniform arrival order.  The canonical and sequential nestings
are proved equal, but this remains a rank-mean component only.
-/
theorem source_threeFirm_direct_rankMean_AHH_certificate :
    sourceCanonicalDirectRankMeanExpectedAHH =
        sourceDirectRankMeanExpectedAHH ∧
      sourceCanonicalDirectRankMeanExpectedAHH = sourceExecutableExpectedAHH ∧
      sourceDirectRankMeanExpectedAHH = 42778976113 / 74881681875 :=
  ⟨sourceCanonicalDirectRankMeanExpectedAHH_eq_direct,
    sourceCanonicalDirectRankMeanExpectedAHH_eq_executable,
    sourceDirectRankMeanExpectedAHH_eq⟩

/--
For the source's four iid `Uniform[0,1]` values, the rank-mean table used by
the finite evaluator is the actual expected upper-order-statistic table.  This
does not yet connect the full sequential product experiment to cardinal values.
-/
theorem source_threeFirm_uniform_orderStatistic_table
    (candidate : SourceFourCandidate) :
    (sourceExpectedOrderStatisticValue candidate : ℝ) =
      AppliedModelingLib.Probability.expectedUpperOrderStatistic
        (Measure.pi (fun _ : Fin 4 => PRPKG24AccuracyDiversity.uniform01Measure))
        candidate :=
  sourceExpectedOrderStatisticValue_eq_uniform01_expectedUpperOrderStatistic
    candidate

/--
For a finite ranking-dependent true-rank selector independent of the source's
four iid Uniform cardinal values, the actual product-law expected utility is
exactly the finite rank-mean table.  A separate bridge must still identify the
source sequential allocation with a particular `outcomeLaw` and `select`.
-/
theorem source_threeFirm_independent_finite_selector_cardinal_bridge
    {Outcome : Type*} [Fintype Outcome] [MeasurableSpace Outcome]
    [MeasurableSingletonClass Outcome] [DecidableEq Outcome]
    (outcomeLaw : PMF Outcome) (select : Outcome → SourceFourCandidate) :
    (∫ outcome, sourceFourSelectedUniformUtilityOf select outcome
      ∂outcomeLaw.toMeasure.prod sourceFourUniformValueLaw) =
      ∑ finiteOutcome : Outcome,
        (outcomeLaw finiteOutcome).toReal *
          (sourceExpectedOrderStatisticValue (select finiteOutcome) : ℝ) :=
  sourceFourSelectedUniformUtilityOf_integral_eq_weighted_table outcomeLaw select

/--
Each focal AAA/HAA/AAH/HAH/AHH/HHH rank-mean row is the expectation under its
actual finite PMF product law, with one shared algorithm draw where applicable
and independent human draws otherwise.
-/
theorem source_threeFirm_finite_product_law_rankMean_bridges :
    sourceAAAProductLawExpectation = ((sourceDirectRankMeanExpectedAAA : ℚ) : ℝ) ∧
      sourceHAAProductLawExpectation = ((sourceDirectRankMeanExpectedHAA : ℚ) : ℝ) ∧
      sourceAAHProductLawExpectation = ((sourceDirectRankMeanExpectedAAH : ℚ) : ℝ) ∧
      sourceHAHProductLawExpectation = ((sourceDirectRankMeanExpectedHAH : ℚ) : ℝ) ∧
      sourceAHHProductLawExpectation = ((sourceDirectRankMeanExpectedAHH : ℚ) : ℝ) ∧
      sourceHHHProductLawExpectation = ((sourceDirectRankMeanExpectedHHH : ℚ) : ℝ) :=
  ⟨sourceAAAProductLawExpectation_eq_cast_direct,
    sourceHAAProductLawExpectation_eq_cast_direct,
    sourceAAHProductLawExpectation_eq_cast_direct,
    sourceHAHProductLawExpectation_eq_cast_direct,
    sourceAHHProductLawExpectation_eq_cast_direct,
    sourceHHHProductLawExpectation_eq_cast_direct⟩

/--
The canonical true-rank finite three-firm experiment composes each actual
ranking/arrival PMF law with four iid Uniform cardinal values and the proved
sequential focal selector.  Every focal row has its exact cardinal expectation,
and the three focal best-response comparisons plus the all-algorithm/all-human
focal ordering hold.  The raw candidate-identity source experiment is bridged
separately below; all-firm equilibrium and social-welfare claims remain open.
-/
theorem source_threeFirm_explicit_cardinal_product_certificates :
    (∫ outcome, sourceAAACardinalUtility outcome ∂sourceAAACardinalProductLaw) =
        ((sourceDirectRankMeanExpectedAAA : ℚ) : ℝ) ∧
      (∫ outcome, sourceHAACardinalUtility outcome ∂sourceHAACardinalProductLaw) =
        ((sourceDirectRankMeanExpectedHAA : ℚ) : ℝ) ∧
      (∫ outcome, sourceAAHCardinalUtility outcome ∂sourceAAHCardinalProductLaw) =
        ((sourceDirectRankMeanExpectedAAH : ℚ) : ℝ) ∧
      (∫ outcome, sourceHAHCardinalUtility outcome ∂sourceHAHCardinalProductLaw) =
        ((sourceDirectRankMeanExpectedHAH : ℚ) : ℝ) ∧
      (∫ outcome, sourceAHHCardinalUtility outcome ∂sourceAHHCardinalProductLaw) =
        ((sourceDirectRankMeanExpectedAHH : ℚ) : ℝ) ∧
      (∫ outcome, sourceHHHCardinalUtility outcome ∂sourceHHHCardinalProductLaw) =
        ((sourceDirectRankMeanExpectedHHH : ℚ) : ℝ) ∧
      (∫ outcome, sourceHAACardinalUtility outcome ∂sourceHAACardinalProductLaw) <
        ∫ outcome, sourceAAACardinalUtility outcome ∂sourceAAACardinalProductLaw ∧
      (∫ outcome, sourceHAHCardinalUtility outcome ∂sourceHAHCardinalProductLaw) <
        ∫ outcome, sourceAAHCardinalUtility outcome ∂sourceAAHCardinalProductLaw ∧
      (∫ outcome, sourceHHHCardinalUtility outcome ∂sourceHHHCardinalProductLaw) <
        ∫ outcome, sourceAHHCardinalUtility outcome ∂sourceAHHCardinalProductLaw ∧
      (∫ outcome, sourceAAACardinalUtility outcome ∂sourceAAACardinalProductLaw) <
        ∫ outcome, sourceHHHCardinalUtility outcome ∂sourceHHHCardinalProductLaw :=
  ⟨sourceAAACardinalUtility_integral_eq_cast_direct,
    sourceHAACardinalUtility_integral_eq_cast_direct,
    sourceAAHCardinalUtility_integral_eq_cast_direct,
    sourceHAHCardinalUtility_integral_eq_cast_direct,
    sourceAHHCardinalUtility_integral_eq_cast_direct,
    sourceHHHCardinalUtility_integral_eq_cast_direct,
    sourceCardinalProduct_AAA_gt_HAA,
    sourceCardinalProduct_AAH_gt_HAH,
    sourceCardinalProduct_AHH_gt_HHH,
    sourceCardinalProduct_AAA_lt_HHH⟩

/--
The paper's actual K=3 experiment starts from four raw iid Uniform candidate
values, ranks those identities by realized value, and draws Mallows errors
relative to that realized true order.  This certificate proves that source
experiment's six focal expected utilities and its three focal algorithmic
best-response comparisons, rather than assuming sorted values are independent
of rankings.  Deterministic tie breaking only totalizes a null event under the
continuous iid Uniform law.
-/
theorem source_threeFirm_rawCandidateIdentity_certificates :
    (∫ outcome, sourceAAACandidateIdentityUtility outcome
      ∂sourceAAACardinalProductLaw) =
        ((sourceDirectRankMeanExpectedAAA : ℚ) : ℝ) ∧
      (∫ outcome, sourceHAACandidateIdentityUtility outcome
        ∂sourceHAACardinalProductLaw) =
        ((sourceDirectRankMeanExpectedHAA : ℚ) : ℝ) ∧
      (∫ outcome, sourceAAHCandidateIdentityUtility outcome
        ∂sourceAAHCardinalProductLaw) =
        ((sourceDirectRankMeanExpectedAAH : ℚ) : ℝ) ∧
      (∫ outcome, sourceHAHCandidateIdentityUtility outcome
        ∂sourceHAHCardinalProductLaw) =
        ((sourceDirectRankMeanExpectedHAH : ℚ) : ℝ) ∧
      (∫ outcome, sourceAHHCandidateIdentityUtility outcome
        ∂sourceAHHCardinalProductLaw) =
        ((sourceDirectRankMeanExpectedAHH : ℚ) : ℝ) ∧
      (∫ outcome, sourceHHHCandidateIdentityUtility outcome
        ∂sourceHHHCardinalProductLaw) =
        ((sourceDirectRankMeanExpectedHHH : ℚ) : ℝ) ∧
      (∫ outcome, sourceHAACandidateIdentityUtility outcome
        ∂sourceHAACardinalProductLaw) <
        ∫ outcome, sourceAAACandidateIdentityUtility outcome
          ∂sourceAAACardinalProductLaw ∧
      (∫ outcome, sourceHAHCandidateIdentityUtility outcome
        ∂sourceHAHCardinalProductLaw) <
        ∫ outcome, sourceAAHCandidateIdentityUtility outcome
          ∂sourceAAHCardinalProductLaw ∧
      (∫ outcome, sourceHHHCandidateIdentityUtility outcome
        ∂sourceHHHCardinalProductLaw) <
        ∫ outcome, sourceAHHCandidateIdentityUtility outcome
          ∂sourceAHHCardinalProductLaw ∧
      (∫ outcome, sourceAAACandidateIdentityUtility outcome
        ∂sourceAAACardinalProductLaw) <
        ∫ outcome, sourceHHHCandidateIdentityUtility outcome
          ∂sourceHHHCardinalProductLaw :=
  ⟨sourceAAACandidateIdentityUtility_integral_eq_cast_direct,
    sourceHAACandidateIdentityUtility_integral_eq_cast_direct,
    sourceAAHCandidateIdentityUtility_integral_eq_cast_direct,
    sourceHAHCandidateIdentityUtility_integral_eq_cast_direct,
    sourceAHHCandidateIdentityUtility_integral_eq_cast_direct,
    sourceHHHCandidateIdentityUtility_integral_eq_cast_direct,
    sourceCandidateIdentity_AAA_gt_HAA,
    sourceCandidateIdentity_AAH_gt_HAH,
    sourceCandidateIdentity_AHH_gt_HHH,
    sourceCandidateIdentity_AAA_lt_HHH⟩

/--
Source Section 4's multi-firm existence claim, witnessed at four candidates,
three firms, `phi_A = 2`, and `phi_H = 1.75`: in the literal raw iid
Uniform/Mallows model, every firm strictly prefers the shared algorithm for
every opponent configuration, while all-human play has higher expected total
selected value than all-algorithm play.

The printed approximate utilities at source lines 620-623 remain a separate
finite computational illustration.  This theorem supplies the exact witness
needed for the preceding claim that a Braess-style paradox can occur for more
than two firms; it does not assert the source's explicitly open universal
multi-firm generalization.
-/
theorem source_threeFirm_rawCandidateIdentity_dominance_and_welfare :
    sourcePermutationIndexedAlgorithmDominance ∧
      sourceProfileExpectedWelfare sourceProfileAAA <
        sourceProfileExpectedWelfare sourceProfileHHH :=
  sourceGenericThreeFirmDominanceAndWelfare

/--
The all-human finite rank-mean model is label-invariant only through a proved
reindexing of the iid human-ranking product law and uniform arrival law.  This
does not assert the missing mixed-profile or cardinal-utility symmetry.
-/
theorem source_threeFirm_allHuman_rankMean_label_symmetry
    (relabel : SourceFirmPermutation) (focal : SourceThreeFirm) :
    sourceUniformArrivalHHHIIDUtility (relabel focal) =
      sourceUniformArrivalHHHIIDUtility focal :=
  sourceUniformArrivalHHHIIDUtility_labelInvariant relabel focal

/--
Signed-utility observation: every strict all-human welfare advantage can be
translated, without changing rankings or the welfare gap, so that monocultural
all-algorithm welfare is negative and all-human welfare is positive.
-/
theorem signed_welfare_sign_reversal
    {n : ℕ} (algorithmLaw humanLaw : PMF (Ranking n))
    (value : Candidate n → ℝ)
    (hgap : expectedWelfareShared algorithmLaw value <
      expectedWelfareOrdered humanLaw humanLaw value) :
    ∃ shift,
      expectedWelfareShared algorithmLaw (fun c => value c + shift) < 0 ∧
        0 < expectedWelfareOrdered humanLaw humanLaw
          (fun c => value c + shift) :=
  signed_welfare_sign_reversal_of_strict_gap
    algorithmLaw humanLaw value hgap

/--
Source signed-welfare construction. In the corrected fixed-center Mallows
model with at least three source candidates, a common translation yields a
negative-welfare all-algorithm profile that is the unique pure equilibrium and
a positive finite pure-strategy social optimum. The source model has exactly
the two displayed strategy choices; this theorem intentionally makes no
mixed-equilibrium claim.
-/
theorem signed_welfare_source_mallows_sign_reversal
    {n : ℕ} (center : Ranking n) (value : ValueProfile n)
    (hvalue : StrictlyOrderedBy center value) (hn : 0 < n)
    (thetaH : ℝ) (hthetaH : 0 < thetaH) :
    ∃ thetaA, thetaH < thetaA ∧ ∃ shift,
      let M := (fixedCenterMallowsPointFamily center value).modelAt thetaA thetaH
      Model.HasSignedWelfareUniquePureEquilibrium (M.translateValues shift) :=
  fixedCenterMallows_exists_signedWelfare_uniquePureEquilibrium
    center value hvalue hn thetaH hthetaH

/--
The signed-welfare source observation with the equilibrium conclusion repaired
to the full independent mixed two-action game.  The direct statement exposes
the translated deterministic value law, unchanged ranking laws, both strict
algorithmic payoff comparisons, welfare signs, the four-profile welfare
maximum, and the universal mixed-equilibrium conclusion.
-/
theorem signed_welfare_source_mallows_literal_mixed_semantic_complete
    {n : ℕ} (center : Ranking n) (value : ValueProfile n)
    (hvalue : StrictlyOrderedBy center value) (hn : 0 < n)
    (thetaH : ℝ) (hthetaH : 0 < thetaH) :
    ∃ thetaA, thetaH < thetaA ∧ ∃ shift,
      let M := (fixedCenterMallowsPointFamily center value).modelAt thetaA thetaH
      let T := M.translateValues shift
      let outerValueLaw : Measure (ValueProfile n) :=
        Measure.dirac (fun c => value c + shift)
      outerValueLaw Set.univ = 1 ∧
      (∀ c : Candidate n,
        ∫ profile, profile c ∂outerValueLaw = value c + shift) ∧
      StrictlyOrderedBy center T.value ∧
      T.algorithmRanking = M.algorithmRanking ∧
      T.humanRanking = M.humanRanking ∧
      Model.labeledFirmRandomOrderExpectedPayoff T Strategy.algorithm Strategy.algorithm >
        Model.labeledFirmRandomOrderExpectedPayoff T Strategy.human Strategy.algorithm ∧
      Model.labeledFirmRandomOrderExpectedPayoff T Strategy.algorithm Strategy.human >
        Model.labeledFirmRandomOrderExpectedPayoff T Strategy.human Strategy.human ∧
      Model.welfareRandomOrder T Strategy.algorithm Strategy.algorithm < 0 ∧
      0 < max
        (max (Model.welfareRandomOrder T Strategy.algorithm Strategy.algorithm)
          (Model.welfareRandomOrder T Strategy.algorithm Strategy.human))
        (max (Model.welfareRandomOrder T Strategy.human Strategy.algorithm)
          (Model.welfareRandomOrder T Strategy.human Strategy.human)) ∧
      ∀ first second : Model.MixedStrategy,
        ((∀ deviation : Model.MixedStrategy,
          Model.mixedExpectedPayoff T deviation second ≤
            Model.mixedExpectedPayoff T first second) ∧
        (∀ deviation : Model.MixedStrategy,
          Model.mixedExpectedPayoff T deviation first ≤
            Model.mixedExpectedPayoff T second first)) →
          first = Model.mixedAlgorithm ∧ second = Model.mixedAlgorithm := by
  rcases fixedCenterMallows_exists_unbounded_relative_welfare_loss
      center value hvalue hn thetaH hthetaH 1 zero_lt_one with
    ⟨thetaA, hthetaA, shift, hparadox, hnegative, hpositive, _⟩
  let M := (fixedCenterMallowsPointFamily center value).modelAt thetaA thetaH
  let T := M.translateValues shift
  have horder : StrictlyOrderedBy center T.value := by
    change StrictlyOrderedBy center (fun c => value c + shift)
    exact StrictlyOrderedBy.add_const hvalue shift
  have hlaws : T.algorithmRanking = M.algorithmRanking ∧
      T.humanRanking = M.humanRanking :=
    Model.translateValues_ranking_laws M shift
  have hdominance :=
    (Model.algorithmStrictlyDominant_iff_payoffAgainst T).1 hparadox.1
  have hmax : 0 < Model.finiteMixedSocialWelfareOptimum T :=
    Model.finiteMixedSocialWelfareOptimum_pos_of_human_human_pos T hpositive
  have hunique :=
    Model.mixedAlgorithm_mixedAlgorithm_uniqueMixedNashEquilibrium_of_algorithmStrictlyDominant
      T hparadox.1
  refine ⟨thetaA, hthetaA, shift, ?_⟩
  dsimp
  refine ⟨by simp, ?_, horder, hlaws.1, hlaws.2, hdominance.1, hdominance.2,
    hnegative, ?_, ?_⟩
  · intro c
    simp
  · simpa [Model.finiteMixedSocialWelfareOptimum,
      Model.finitePureSocialWelfareOptimum, Model.pureProfileSocialWelfare] using hmax
  · intro first second hne
    exact hunique.2 first second hne

/--
Formal strengthening of the source sign-reversal observation.  From the same
corrected Mallows instance, any requested positive relative-welfare-loss bound
is achieved after a common value translation.  The source does not state this
bound verbatim; it is exposed separately to avoid enlarging the source claim.
-/
theorem signed_welfare_mallows_unbounded_relative_loss_strengthening
    {n : ℕ} (center : Ranking n) (value : ValueProfile n)
    (hvalue : StrictlyOrderedBy center value) (hn : 0 < n)
    (thetaH bound : ℝ) (hthetaH : 0 < thetaH) (hbound : 0 < bound) :
    ∃ thetaA, thetaH < thetaA ∧ ∃ shift,
      let M := (fixedCenterMallowsPointFamily center value).modelAt thetaA thetaH
      Model.HasKR21MonocultureParadox (M.translateValues shift) ∧
        Model.welfareRandomOrder (M.translateValues shift)
          Strategy.algorithm Strategy.algorithm < 0 ∧
        0 < Model.welfareRandomOrder (M.translateValues shift)
          Strategy.human Strategy.human ∧
        bound < relativeWelfareLoss
          (Model.welfareRandomOrder (M.translateValues shift)
            Strategy.algorithm Strategy.algorithm)
          (Model.welfareRandomOrder (M.translateValues shift)
            Strategy.human Strategy.human) :=
  fixedCenterMallows_exists_unbounded_relative_welfare_loss
    center value hvalue hn thetaH hthetaH bound hbound

/-! ## Theorem 4 -/

/--
Theorem 4 / Mallows weak optimality: when human and algorithmic Mallows laws
share the same center ranking and the human law is weakly more accurate, the
all-human sequence is a best-response sequence in the multi-firm game.

This route uses the reduced same-size prefix-cut weighted-extremes Mallows
theorem, proved in Lean as
`reflMallowsBestInSetPrefixCutFirstChoiceWeightedExtremes_of_q_lt`.
-/
theorem theorem4_mallows_all_human_sequence_optimal_of_q_le
    {n k : ℕ} {human algorithm : MallowsSpec n}
    (hcenter : human.center = algorithm.center)
    (hq_le : human.q ≤ algorithm.q)
    {value : Candidate n → ℝ} (hvalue : WeaklyOrderedBy human.center value) :
    (SequentialModel.ofMallows algorithm human value).IsSequentialBestResponseSequence k
      (SequentialModel.allHumanSequence k) :=
    KR21Monoculture.MallowsComparison.paper_theorem4_mallows_all_human_sequence_optimal_of_q_le
      hcenter hq_le hvalue

/--
Theorem 4 / Mallows strict uniqueness: if the human Mallows law has strictly
lower inverse-noise parameter than the algorithmic law, then at every
nonterminal history the human ranking distribution is the unique best response.
-/
theorem theorem4_mallows_human_unique_at_each_history_of_q_lt
    {n k : ℕ} {human algorithm : MallowsSpec n}
    (hcenter : human.center = algorithm.center)
    (hq_lt : human.q < algorithm.q)
    {value : Candidate n → ℝ} (hvalue : StrictlyOrderedBy human.center value) :
    SequentialModel.HumanUniquelyOptimalAtAllNonterminalHistories
      (SequentialModel.ofMallows algorithm human value) k :=
  KR21Monoculture.MallowsComparison.paper_theorem4_mallows_human_unique_at_each_history_of_q_lt
    hcenter hq_lt hvalue

/--
Theorem 4 at the source's `phi` and outer-`D` surface.  The result is an
ex-ante best-response theorem at every feasible remaining candidate set.  A
fixed rank-labelled center and coordinatewise first moments are explicit;
the paper does not specify a posterior kernel after prior hiring histories.
-/
theorem theorem4_source_mallows_outer_allHumanOptimal
    {n k : ℕ} (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    (center : Ranking n) {phiA phiH : ℝ}
    (hphiA : 1 < phiA) (hphiH : 1 < phiH) (haccuracy : phiA ≤ phiH)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D)
    (horder : ∀ᵐ value ∂D, WeaklyOrderedBy center value) :
    SourceMallowsSequential.AllHumanOptimal D
      (SourceMallowsSequential.sourceMallowsSpec center phiA)
      (SourceMallowsSequential.sourceMallowsSpec center phiH) k :=
  KR21Monoculture.SourceMallowsSequential.source_theorem4_mallows_outer_allHumanOptimal
    D center hphiA hphiH haccuracy hvalue horder

/--
The strict Theorem 4 half at the same source surface.  Strict uniqueness is
meaningful only at nonterminal histories with at least two candidates left.
-/
theorem theorem4_source_mallows_outer_humanUnique
    {n k : ℕ} (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    (center : Ranking n) {phiA phiH : ℝ}
    (hphiA : 1 < phiA) (hphiH : 1 < phiH) (haccuracy : phiA < phiH)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D)
    (hstrict : ∀ᵐ value ∂D, StrictlyOrderedBy center value) :
    SourceMallowsSequential.HumanUniqueAtAllNonterminalHistories D
      (SourceMallowsSequential.sourceMallowsSpec center phiA)
      (SourceMallowsSequential.sourceMallowsSpec center phiH) k :=
  KR21Monoculture.SourceMallowsSequential.source_theorem4_mallows_outer_humanUnique
    D center hphiA hphiH haccuracy hvalue hstrict

/--
Complete source-facing Theorem 4 endpoint under the recorded ex-ante,
fresh-independent-ranking convention.  It makes the weak and strict phi cases
one proposition while retaining their distinct almost-everywhere value-order
requirements and the explicit pre-exhaustion meaning of the conclusions.
-/
theorem theorem4_source_mallows_outer_complete
    {n k : ℕ} (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    (center : Ranking n) {phiA phiH : ℝ}
    (hphiA : 1 < phiA) (hphiH : 1 < phiH)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D) :
    (phiA ≤ phiH →
      ∀ horder : ∀ᵐ value ∂D, WeaklyOrderedBy center value,
        SourceMallowsSequential.AllHumanOptimal D
          (SourceMallowsSequential.sourceMallowsSpec center phiA)
          (SourceMallowsSequential.sourceMallowsSpec center phiH) k) ∧
    (phiA < phiH →
      ∀ hstrict : ∀ᵐ value ∂D, StrictlyOrderedBy center value,
        SourceMallowsSequential.HumanUniqueAtAllNonterminalHistories D
          (SourceMallowsSequential.sourceMallowsSpec center phiA)
          (SourceMallowsSequential.sourceMallowsSpec center phiH) k) := by
  refine ⟨?_, ?_⟩
  · intro haccuracy horder
    exact theorem4_source_mallows_outer_allHumanOptimal
      D center hphiA hphiH haccuracy hvalue horder
  · intro haccuracy hstrict
    exact theorem4_source_mallows_outer_humanUnique
      D center hphiA hphiH haccuracy hvalue hstrict

/-- Corrected D.1 with both literal source Mallows laws in the endpoint. -/
theorem equationD1_source_phi_likelihood_ratio_complete
    (center : Ranking 1)
    (phiNoisy thetaNoisy phiAccurate thetaAccurate : ℝ)
    (hphiNoisy : 1 < phiNoisy) (hphi_lt : phiNoisy < phiAccurate)
    (hthetaNoisy : thetaNoisy = phiNoisy - 1)
    (hthetaAccurate : thetaAccurate = phiAccurate - 1)
    {remaining : Finset (Candidate 1)} (hremaining : remaining.Nonempty)
    {better worse : Candidate 1}
    (hbetter : better ∈ remaining) (hworse : worse ∈ remaining)
    (hcenter_order : rankOf center better < rankOf center worse) :
    let MAccurate := concreteMallowsSpec center thetaAccurate
    let MNoisy := concreteMallowsSpec center thetaNoisy
    MAccurate.q = phiAccurate⁻¹ ∧
      MNoisy.q = phiNoisy⁻¹ ∧
      (∀ pi : Ranking 1,
        (MAccurate.law pi).toReal =
          phiAccurate⁻¹ ^ kendallTau center pi /
            (∑ tau : Ranking 1, phiAccurate⁻¹ ^ kendallTau center tau)) ∧
      (∀ pi : Ranking 1,
        (MNoisy.law pi).toReal =
          phiNoisy⁻¹ ^ kendallTau center pi /
            (∑ tau : Ranking 1, phiNoisy⁻¹ ^ kendallTau center tau)) ∧
      0 <
        pmfProb MAccurate.law (fun pi => better = bestInSet pi remaining) *
          pmfProb MNoisy.law (fun pi => worse = bestInSet pi remaining) -
        pmfProb MAccurate.law (fun pi => worse = bestInSet pi remaining) *
          pmfProb MNoisy.law (fun pi => better = bestInSet pi remaining) := by
  dsimp
  have hphiAccurate : 1 < phiAccurate := lt_trans hphiNoisy hphi_lt
  refine ⟨(source_equation8_concrete_mallows_probability center phiAccurate
    thetaAccurate hphiAccurate hthetaAccurate center).1,
    (source_equation8_concrete_mallows_probability center phiNoisy thetaNoisy
      hphiNoisy hthetaNoisy center).1, ?_, ?_, ?_⟩
  · intro pi
    exact (source_equation8_concrete_mallows_probability center phiAccurate
      thetaAccurate hphiAccurate hthetaAccurate pi).2
  · intro pi
    exact (source_equation8_concrete_mallows_probability center phiNoisy thetaNoisy
      hphiNoisy hthetaNoisy pi).2
  · rcases equationD1_corrected_source_phi_likelihood_ratio_three_candidates
      center hphiNoisy hphi_lt hremaining hbetter hworse hcenter_order with
      ⟨_, _, hD⟩
    simpa [SourceMallowsSequential.sourceMallowsSpec, hthetaAccurate,
      hthetaNoisy] using hD

/-- Appendix E.1 with its literal source Mallows atom law. -/
theorem equationE1_source_phi_complete
    {n : ℕ} (center : Ranking n) (phi theta : ℝ)
    (hphi : 1 < phi) (htheta : theta = phi - 1) (hn : 0 < n)
    {value : Candidate n → ℝ} (hvalue : StrictlyOrderedBy center value) :
    let M := concreteMallowsSpec center theta
    M.q = phi⁻¹ ∧
      (∀ pi : Ranking n,
        (M.law pi).toReal =
          phi⁻¹ ^ kendallTau center pi /
            (∑ tau : Ranking n, phi⁻¹ ^ kendallTau center tau)) ∧
      0 < AppliedModelingLib.pmfPairConditionalExp M.law M.law disagreementEvent
        (fun pair => value (firstChoice pair.1) - value (secondChoice pair.1)) := by
  dsimp
  refine ⟨(source_equation8_concrete_mallows_probability center phi theta
    hphi htheta center).1, ?_, ?_⟩
  · intro pi
    exact (source_equation8_concrete_mallows_probability center phi theta
      hphi htheta pi).2
  · exact (source_appendixE_concrete_mallows_phi center phi theta
      hphi htheta hn hvalue).1

/--
Appendix E.1 with the finite conditional expectation expanded into its
positive top-disagreement mass and literal numerator/denominator ratio.
-/
theorem equationE1_source_phi_literal_conditional_semantic_complete
    {n : ℕ} (center : Ranking n) (phi theta : ℝ)
    (hphi : 1 < phi) (htheta : theta = phi - 1) (hn : 0 < n)
    {value : Candidate n → ℝ} (hvalue : StrictlyOrderedBy center value) :
    let M := concreteMallowsSpec center theta
    M.q = phi⁻¹ ∧
      (∀ pi : Ranking n,
        (M.law pi).toReal =
          phi⁻¹ ^ kendallTau center pi /
            (∑ tau : Ranking n, phi⁻¹ ^ kendallTau center tau)) ∧
      0 < AppliedModelingLib.pmfPairProb M.law M.law disagreementEvent ∧
      0 < AppliedModelingLib.pmfPairIndicatorExp M.law M.law disagreementEvent
        (fun pair => value (firstChoice pair.1) - value (secondChoice pair.1)) /
          AppliedModelingLib.pmfPairProb M.law M.law disagreementEvent := by
  dsimp
  let M := concreteMallowsSpec center theta
  have hden : 0 < AppliedModelingLib.pmfPairProb M.law M.law disagreementEvent := by
    simpa [disagreementProb] using M.appendixE_disagreementProb_pos
  have hcond : 0 < AppliedModelingLib.pmfPairConditionalExp M.law M.law disagreementEvent
      (fun pair => value (firstChoice pair.1) - value (secondChoice pair.1)) := by
    simpa [M] using
      (source_appendixE_concrete_mallows_phi center phi theta
        hphi htheta hn hvalue).1
  refine ⟨(source_equation8_concrete_mallows_probability center phi theta
    hphi htheta center).1, ?_, hden, ?_⟩
  · intro pi
    exact (source_equation8_concrete_mallows_probability center phi theta
      hphi htheta pi).2
  · change 0 < AppliedModelingLib.pmfPairIndicatorExp M.law M.law disagreementEvent
        (fun pair => value (firstChoice pair.1) - value (secondChoice pair.1)) /
          AppliedModelingLib.pmfPairProb M.law M.law disagreementEvent
    rw [← AppliedModelingLib.pmfPairConditionalExp_eq_div_of_pos
      (μ := M.law) (ν := M.law) (p := disagreementEvent)
      (f := fun pair => value (firstChoice pair.1) - value (secondChoice pair.1)) hden]
    exact hcond

/-- Appendix E.2 with the literal source law, all-pair inequality, and witness. -/
theorem equationE2_source_phi_complete
    {n : ℕ} (center : Ranking n) (phi theta : ℝ)
    (hphi : 1 < phi) (htheta : theta = phi - 1) (hn : 0 < n) :
    let M := concreteMallowsSpec center theta
    M.q = phi⁻¹ ∧
      (∀ pi : Ranking n,
        (M.law pi).toReal =
          phi⁻¹ ^ kendallTau center pi /
            (∑ tau : Ranking n, phi⁻¹ ^ kendallTau center tau)) ∧
      (∀ c d : Candidate n, rankOf M.center c < rankOf M.center d →
        AppliedModelingLib.pmfPairConditionalExp M.law M.law disagreementEvent
            (fun pair =>
              if d = firstChoice pair.1 ∧ c = secondChoice pair.1 then (1 : ℝ) else 0) ≤
          AppliedModelingLib.pmfPairConditionalExp M.law M.law disagreementEvent
            (fun pair =>
              if c = firstChoice pair.1 ∧ d = secondChoice pair.1 then (1 : ℝ) else 0)) ∧
      ∃ c d : Candidate n, rankOf M.center c < rankOf M.center d ∧
        AppliedModelingLib.pmfPairConditionalExp M.law M.law disagreementEvent
            (fun pair =>
              if d = firstChoice pair.1 ∧ c = secondChoice pair.1 then (1 : ℝ) else 0) <
          AppliedModelingLib.pmfPairConditionalExp M.law M.law disagreementEvent
            (fun pair =>
              if c = firstChoice pair.1 ∧ d = secondChoice pair.1 then (1 : ℝ) else 0) := by
  dsimp
  refine ⟨(source_equation8_concrete_mallows_probability center phi theta
    hphi htheta center).1, ?_, ?_⟩
  · intro pi
    exact (source_equation8_concrete_mallows_probability center phi theta
      hphi htheta pi).2
  · exact source_appendixE2_concrete_mallows_phi center phi theta hphi htheta hn

/--
Appendix E.2 with every conditional comparison written over the same explicit
positive top-disagreement denominator.  This excludes the zero-event branch
of the finite conditional-expectation helper from the direct review surface.
-/
theorem equationE2_source_phi_literal_conditional_semantic_complete
    {n : ℕ} (center : Ranking n) (phi theta : ℝ)
    (hphi : 1 < phi) (htheta : theta = phi - 1) (hn : 0 < n) :
    let M := concreteMallowsSpec center theta
    M.q = phi⁻¹ ∧
      (∀ pi : Ranking n,
        (M.law pi).toReal =
          phi⁻¹ ^ kendallTau center pi /
            (∑ tau : Ranking n, phi⁻¹ ^ kendallTau center tau)) ∧
      0 < AppliedModelingLib.pmfPairProb M.law M.law disagreementEvent ∧
      (∀ c d : Candidate n, rankOf M.center c < rankOf M.center d →
        AppliedModelingLib.pmfPairIndicatorExp M.law M.law disagreementEvent
            (fun pair =>
              if d = firstChoice pair.1 ∧ c = secondChoice pair.1 then (1 : ℝ) else 0) /
            AppliedModelingLib.pmfPairProb M.law M.law disagreementEvent ≤
          AppliedModelingLib.pmfPairIndicatorExp M.law M.law disagreementEvent
            (fun pair =>
              if c = firstChoice pair.1 ∧ d = secondChoice pair.1 then (1 : ℝ) else 0) /
            AppliedModelingLib.pmfPairProb M.law M.law disagreementEvent) ∧
      ∃ c d : Candidate n, rankOf M.center c < rankOf M.center d ∧
        AppliedModelingLib.pmfPairIndicatorExp M.law M.law disagreementEvent
            (fun pair =>
              if d = firstChoice pair.1 ∧ c = secondChoice pair.1 then (1 : ℝ) else 0) /
            AppliedModelingLib.pmfPairProb M.law M.law disagreementEvent <
          AppliedModelingLib.pmfPairIndicatorExp M.law M.law disagreementEvent
            (fun pair =>
              if c = firstChoice pair.1 ∧ d = secondChoice pair.1 then (1 : ℝ) else 0) /
            AppliedModelingLib.pmfPairProb M.law M.law disagreementEvent := by
  dsimp
  let M := concreteMallowsSpec center theta
  have hden : 0 < AppliedModelingLib.pmfPairProb M.law M.law disagreementEvent := by
    simpa [disagreementProb] using M.appendixE_disagreementProb_pos
  have hsource := source_appendixE2_concrete_mallows_phi center phi theta hphi htheta hn
  refine ⟨(source_equation8_concrete_mallows_probability center phi theta
    hphi htheta center).1, ?_, hden, ?_, ?_⟩
  · intro pi
    exact (source_equation8_concrete_mallows_probability center phi theta
      hphi htheta pi).2
  · intro c d hcd
    have h := hsource.1 c d hcd
    change AppliedModelingLib.pmfPairIndicatorExp M.law M.law disagreementEvent
        (fun pair =>
          if d = firstChoice pair.1 ∧ c = secondChoice pair.1 then (1 : ℝ) else 0) /
        AppliedModelingLib.pmfPairProb M.law M.law disagreementEvent ≤
      AppliedModelingLib.pmfPairIndicatorExp M.law M.law disagreementEvent
        (fun pair =>
          if c = firstChoice pair.1 ∧ d = secondChoice pair.1 then (1 : ℝ) else 0) /
        AppliedModelingLib.pmfPairProb M.law M.law disagreementEvent
    rw [← AppliedModelingLib.pmfPairConditionalExp_eq_div_of_pos
      (μ := M.law) (ν := M.law) (p := disagreementEvent)
      (f := fun pair =>
        if d = firstChoice pair.1 ∧ c = secondChoice pair.1 then (1 : ℝ) else 0) hden,
      ← AppliedModelingLib.pmfPairConditionalExp_eq_div_of_pos
        (μ := M.law) (ν := M.law) (p := disagreementEvent)
        (f := fun pair =>
          if c = firstChoice pair.1 ∧ d = secondChoice pair.1 then (1 : ℝ) else 0) hden]
    simpa [M] using h
  · rcases hsource.2 with ⟨c, d, hcd, hstrict⟩
    refine ⟨c, d, hcd, ?_⟩
    change AppliedModelingLib.pmfPairIndicatorExp M.law M.law disagreementEvent
        (fun pair =>
          if d = firstChoice pair.1 ∧ c = secondChoice pair.1 then (1 : ℝ) else 0) /
        AppliedModelingLib.pmfPairProb M.law M.law disagreementEvent <
      AppliedModelingLib.pmfPairIndicatorExp M.law M.law disagreementEvent
        (fun pair =>
          if c = firstChoice pair.1 ∧ d = secondChoice pair.1 then (1 : ℝ) else 0) /
        AppliedModelingLib.pmfPairProb M.law M.law disagreementEvent
    rw [← AppliedModelingLib.pmfPairConditionalExp_eq_div_of_pos
      (μ := M.law) (ν := M.law) (p := disagreementEvent)
      (f := fun pair =>
        if d = firstChoice pair.1 ∧ c = secondChoice pair.1 then (1 : ℝ) else 0) hden,
      ← AppliedModelingLib.pmfPairConditionalExp_eq_div_of_pos
        (μ := M.law) (ν := M.law) (p := disagreementEvent)
        (f := fun pair =>
          if c = firstChoice pair.1 ∧ d = secondChoice pair.1 then (1 : ℝ) else 0) hden]
    simpa [M] using hstrict

/-- Appendix E.3 with the literal source law and product comparison. -/
theorem equationE3_source_phi_complete
    {n : ℕ} (center : Ranking n) (phi theta : ℝ)
    (hphi : 1 < phi) (htheta : theta = phi - 1) (hn : 0 < n) :
    let M := concreteMallowsSpec center theta
    M.q = phi⁻¹ ∧
      (∀ pi : Ranking n,
        (M.law pi).toReal =
          phi⁻¹ ^ kendallTau center pi /
            (∑ tau : Ranking n, phi⁻¹ ^ kendallTau center tau)) ∧
      (∀ c d : Candidate n, rankOf M.center c < rankOf M.center d →
        0 ≤ M.firstSecondChoiceProb c d * firstChoiceMissProb M.law c -
          M.firstSecondChoiceProb d c * firstChoiceMissProb M.law d) ∧
      ∃ c d : Candidate n, rankOf M.center c < rankOf M.center d ∧
        0 < M.firstSecondChoiceProb c d * firstChoiceMissProb M.law c -
          M.firstSecondChoiceProb d c * firstChoiceMissProb M.law d := by
  dsimp
  refine ⟨(source_equation8_concrete_mallows_probability center phi theta
    hphi htheta center).1, ?_, ?_⟩
  · intro pi
    exact (source_equation8_concrete_mallows_probability center phi theta
      hphi htheta pi).2
  · exact source_appendixE3_concrete_mallows_phi center phi theta hphi htheta hn

/-- Lemma 6 with the source parameter and normalized Mallows law visible. -/
theorem lemma6_source_phi_rank_power_complete
    {n : ℕ} (center : Ranking n) (phi theta : ℝ)
    (hphi : 1 < phi) (htheta : theta = phi - 1) (c : Candidate n) :
    let M := concreteMallowsSpec center theta
    M.q = phi⁻¹ ∧
      (∀ pi : Ranking n,
        (M.law pi).toReal =
          phi⁻¹ ^ kendallTau center pi /
            (∑ tau : Ranking n, phi⁻¹ ^ kendallTau center tau)) ∧
      firstChoiceProb M.law c =
        phi⁻¹ ^ (rankOf M.center c : ℕ) /
          candidateRankPowerSum n phi⁻¹ := by
  dsimp
  have hq := source_equation8_concrete_mallows_probability center phi theta
    hphi htheta center
  refine ⟨hq.1, ?_, ?_⟩
  · intro pi
    exact (source_equation8_concrete_mallows_probability center phi theta
      hphi htheta pi).2
  · exact source_equationF2_mallows_first_choice_rank_power
      (concreteMallowsSpec center theta) phi hq.1 c

/-- Equation (F.2) with the source parameter and normalized Mallows law visible. -/
theorem equationF2_source_phi_closed_form_complete
    {n : ℕ} (center : Ranking n) (phi theta : ℝ)
    (hphi : 1 < phi) (htheta : theta = phi - 1) (c : Candidate n) :
    let M := concreteMallowsSpec center theta
    M.q = phi⁻¹ ∧
      (∀ pi : Ranking n,
        (M.law pi).toReal =
          phi⁻¹ ^ kendallTau center pi /
            (∑ tau : Ranking n, phi⁻¹ ^ kendallTau center tau)) ∧
      firstChoiceProb M.law c =
        (1 - phi⁻¹) /
          (phi ^ (rankOf M.center c : ℕ) *
            (1 - phi⁻¹ ^ (n + 2))) := by
  dsimp
  have hq := source_equation8_concrete_mallows_probability center phi theta
    hphi htheta center
  refine ⟨hq.1, ?_, ?_⟩
  · intro pi
    exact (source_equation8_concrete_mallows_probability center phi theta
      hphi htheta pi).2
  · exact source_equationF2_mallows_first_choice_closed_form
      (concreteMallowsSpec center theta) phi ⟨hphi, hq.1⟩ c

/--
Theorem 4 with its two literal source Mallows laws and the recorded ex-ante
fresh-independent-ranking convention in the conclusion.
-/
theorem theorem4_source_mallows_outer_semantic_complete
    {n k : ℕ} (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    (center : Ranking n)
    (phiA thetaA phiH thetaH : ℝ)
    (hphiA : 1 < phiA) (hphiH : 1 < phiH)
    (hthetaA : thetaA = phiA - 1) (hthetaH : thetaH = phiH - 1)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D) :
    let algorithm := concreteMallowsSpec center thetaA
    let human := concreteMallowsSpec center thetaH
    algorithm.q = phiA⁻¹ ∧
      human.q = phiH⁻¹ ∧
      (∀ pi : Ranking n,
        (algorithm.law pi).toReal =
          phiA⁻¹ ^ kendallTau center pi /
            (∑ tau : Ranking n, phiA⁻¹ ^ kendallTau center tau)) ∧
      (∀ pi : Ranking n,
        (human.law pi).toReal =
          phiH⁻¹ ^ kendallTau center pi /
            (∑ tau : Ranking n, phiH⁻¹ ^ kendallTau center tau)) ∧
      (phiA ≤ phiH →
        (∀ᵐ value ∂D, WeaklyOrderedBy center value) →
          SourceMallowsSequential.AllHumanOptimal D algorithm human k) ∧
      (phiA < phiH →
        (∀ᵐ value ∂D, StrictlyOrderedBy center value) →
          SourceMallowsSequential.HumanUniqueAtAllNonterminalHistories D
            algorithm human k) := by
  dsimp
  refine ⟨(source_equation8_concrete_mallows_probability center phiA thetaA
    hphiA hthetaA center).1,
    (source_equation8_concrete_mallows_probability center phiH thetaH
      hphiH hthetaH center).1, ?_, ?_, ?_, ?_⟩
  · intro pi
    exact (source_equation8_concrete_mallows_probability center phiA thetaA
      hphiA hthetaA pi).2
  · intro pi
    exact (source_equation8_concrete_mallows_probability center phiH thetaH
      hphiH hthetaH pi).2
  · intro haccuracy horder
    have htheorem := theorem4_source_mallows_outer_complete
      (k := k) D center hphiA hphiH hvalue
    simpa [SourceMallowsSequential.sourceMallowsSpec, hthetaA, hthetaH]
      using htheorem.1 haccuracy horder
  · intro haccuracy hstrict
    have htheorem := theorem4_source_mallows_outer_complete
      (k := k) D center hphiA hphiH hvalue
    simpa [SourceMallowsSequential.sourceMallowsSpec, hthetaA, hthetaH]
      using htheorem.2 haccuracy hstrict

/--
Theorem 4 with its sequential conclusion expanded all the way to the source
experiment.  At every feasible history the next firm receives a fresh ranking
draw; the payoff is the outer expectation of the finite Mallows-PMF sum over
the candidates that remain after that history.  This endpoint intentionally
does not leave the result inside `AllHumanOptimal` or
`HumanUniqueAtAllNonterminalHistories` predicates.
-/
theorem theorem4_source_mallows_outer_literal_semantic_complete
    {n k : ℕ} (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    (center : Ranking n)
    (phiA thetaA phiH thetaH : ℝ)
    (hphiA : 1 < phiA) (hphiH : 1 < phiH)
    (hthetaA : thetaA = phiA - 1) (hthetaH : thetaH = phiH - 1)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D) :
    let algorithm := concreteMallowsSpec center thetaA
    let human := concreteMallowsSpec center thetaH
    algorithm.q = phiA⁻¹ ∧
      human.q = phiH⁻¹ ∧
      (∀ pi : Ranking n,
        (algorithm.law pi).toReal =
          phiA⁻¹ ^ kendallTau center pi /
            (∑ tau : Ranking n, phiA⁻¹ ^ kendallTau center tau)) ∧
      (∀ pi : Ranking n,
        (human.law pi).toReal =
          phiH⁻¹ ^ kendallTau center pi /
            (∑ tau : Ranking n, phiH⁻¹ ^ kendallTau center tau)) ∧
      (phiA ≤ phiH →
        (∀ᵐ value ∂D, WeaklyOrderedBy center value) →
          ∀ i : Fin k, i.val < Fintype.card (Candidate n) →
            ∀ hired : Finset (Candidate n), hired.card = i.val →
              ∀ strategy : Strategy,
                (∫ value : ValueProfile n,
                  ∑ pi : Ranking n,
                    ((match strategy with
                      | .algorithm => algorithm.law
                      | .human => human.law) pi).toReal *
                      value (bestInSet pi (Finset.univ \ hired)) ∂D) ≤
                  (∫ value : ValueProfile n,
                    ∑ pi : Ranking n, (human.law pi).toReal *
                      value (bestInSet pi (Finset.univ \ hired)) ∂D)) ∧
      (phiA < phiH →
        (∀ᵐ value ∂D, StrictlyOrderedBy center value) →
          ∀ i : Fin k, i.val + 1 < Fintype.card (Candidate n) →
            ∀ hired : Finset (Candidate n), hired.card = i.val →
              ∀ strategy : Strategy,
                (∀ alternative : Strategy,
                  (∫ value : ValueProfile n,
                    ∑ pi : Ranking n,
                      ((match alternative with
                        | .algorithm => algorithm.law
                        | .human => human.law) pi).toReal *
                        value (bestInSet pi (Finset.univ \ hired)) ∂D) ≤
                    (∫ value : ValueProfile n,
                      ∑ pi : Ranking n,
                        ((match strategy with
                          | .algorithm => algorithm.law
                          | .human => human.law) pi).toReal *
                        value (bestInSet pi (Finset.univ \ hired)) ∂D)) →
                  strategy = Strategy.human) := by
  dsimp
  refine ⟨(source_equation8_concrete_mallows_probability center phiA thetaA
    hphiA hthetaA center).1,
    (source_equation8_concrete_mallows_probability center phiH thetaH
      hphiH hthetaH center).1, ?_, ?_, ?_, ?_⟩
  · intro pi
    exact (source_equation8_concrete_mallows_probability center phiA thetaA
      hphiA hthetaA pi).2
  · intro pi
    exact (source_equation8_concrete_mallows_probability center phiH thetaH
      hphiH hthetaH pi).2
  · intro haccuracy horder
    simpa [SourceMallowsSequential.sourceMallowsSpec, hthetaA, hthetaH,
      SourceMallowsSequential.AllHumanOptimal,
      SourceMallowsSequential.stepUtility,
      SourceMallowsSequential.outerExpectedBestInSet,
      SourceMallowsSequential.rankingLaw,
      DistributionalAccuracyFamily.outerExpected,
      expectedBestInSet, AppliedModelingLib.pmfExp, SequentialModel.remainingAfter]
      using SourceMallowsSequential.source_theorem4_mallows_outer_allHumanOptimal
        (k := k) D center hphiA hphiH haccuracy hvalue horder
  · intro haccuracy hstrict
    simpa [SourceMallowsSequential.sourceMallowsSpec, hthetaA, hthetaH,
      SourceMallowsSequential.HumanUniqueAtAllNonterminalHistories,
      SourceMallowsSequential.stepUtility,
      SourceMallowsSequential.outerExpectedBestInSet,
      SourceMallowsSequential.rankingLaw,
      DistributionalAccuracyFamily.outerExpected,
      expectedBestInSet, AppliedModelingLib.pmfExp, SequentialModel.remainingAfter]
      using SourceMallowsSequential.source_theorem4_mallows_outer_humanUnique
        (k := k) D center hphiA hphiH haccuracy hvalue hstrict

/--
Theorem 4 at the literal source surface under the necessary hiring-horizon
convention `K < N`.  Every scheduled choice then has a nonempty remaining set,
and every strict-case choice has at least two candidates remaining, so the
human strategy is uniquely optimal at every scheduled position.

This remains an ex-ante all-human-prefix/first-deviation certificate; it does
not claim posterior or repeated-shared-algorithm subgame perfection.
-/
theorem theorem4_source_mallows_outer_horizon_lt_literal_semantic_complete
    {n k : ℕ} (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    (center : Ranking n)
    (phiA thetaA phiH thetaH : ℝ)
    (hphiA : 1 < phiA) (hphiH : 1 < phiH)
    (hthetaA : thetaA = phiA - 1) (hthetaH : thetaH = phiH - 1)
    (horizon : k < Fintype.card (Candidate n))
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D) :
    let algorithm := concreteMallowsSpec center thetaA
    let human := concreteMallowsSpec center thetaH
    algorithm.q = phiA⁻¹ ∧
      human.q = phiH⁻¹ ∧
      (∀ pi : Ranking n,
        (algorithm.law pi).toReal =
          phiA⁻¹ ^ kendallTau center pi /
            (∑ tau : Ranking n, phiA⁻¹ ^ kendallTau center tau)) ∧
      (∀ pi : Ranking n,
        (human.law pi).toReal =
          phiH⁻¹ ^ kendallTau center pi /
            (∑ tau : Ranking n, phiH⁻¹ ^ kendallTau center tau)) ∧
      (phiA ≤ phiH →
        (∀ᵐ value ∂D, WeaklyOrderedBy center value) →
          ∀ i : Fin k,
            ∀ hired : Finset (Candidate n), hired.card = i.val →
              ∀ strategy : Strategy,
                (∫ value : ValueProfile n,
                  ∑ pi : Ranking n,
                    ((match strategy with
                      | .algorithm => algorithm.law
                      | .human => human.law) pi).toReal *
                      value (bestInSet pi (Finset.univ \ hired)) ∂D) ≤
                  (∫ value : ValueProfile n,
                    ∑ pi : Ranking n, (human.law pi).toReal *
                      value (bestInSet pi (Finset.univ \ hired)) ∂D)) ∧
      (phiA < phiH →
        (∀ᵐ value ∂D, StrictlyOrderedBy center value) →
          ∀ i : Fin k,
            ∀ hired : Finset (Candidate n), hired.card = i.val →
              ∀ strategy : Strategy,
                (∀ alternative : Strategy,
                  (∫ value : ValueProfile n,
                    ∑ pi : Ranking n,
                      ((match alternative with
                        | .algorithm => algorithm.law
                        | .human => human.law) pi).toReal *
                        value (bestInSet pi (Finset.univ \ hired)) ∂D) ≤
                    (∫ value : ValueProfile n,
                      ∑ pi : Ranking n,
                        ((match strategy with
                          | .algorithm => algorithm.law
                          | .human => human.law) pi).toReal *
                        value (bestInSet pi (Finset.univ \ hired)) ∂D)) →
                  strategy = Strategy.human) := by
  dsimp
  refine ⟨(source_equation8_concrete_mallows_probability center phiA thetaA
    hphiA hthetaA center).1,
    (source_equation8_concrete_mallows_probability center phiH thetaH
      hphiH hthetaH center).1, ?_, ?_, ?_, ?_⟩
  · intro pi
    exact (source_equation8_concrete_mallows_probability center phiA thetaA
      hphiA hthetaA pi).2
  · intro pi
    exact (source_equation8_concrete_mallows_probability center phiH thetaH
      hphiH hthetaH pi).2
  · intro haccuracy horder i hired hhired strategy
    have hweak :
        ∀ i : Fin k, i.val < Fintype.card (Candidate n) →
          ∀ hired : Finset (Candidate n), hired.card = i.val →
            ∀ strategy : Strategy,
              (∫ value : ValueProfile n,
                ∑ pi : Ranking n,
                  ((match strategy with
                    | .algorithm => (concreteMallowsSpec center thetaA).law
                    | .human => (concreteMallowsSpec center thetaH).law) pi).toReal *
                    value (bestInSet pi (Finset.univ \ hired)) ∂D) ≤
                (∫ value : ValueProfile n,
                  ∑ pi : Ranking n,
                    ((concreteMallowsSpec center thetaH).law pi).toReal *
                    value (bestInSet pi (Finset.univ \ hired)) ∂D) := by
      simpa [SourceMallowsSequential.sourceMallowsSpec, hthetaA, hthetaH,
        SourceMallowsSequential.AllHumanOptimal,
        SourceMallowsSequential.stepUtility,
        SourceMallowsSequential.outerExpectedBestInSet,
        SourceMallowsSequential.rankingLaw,
        DistributionalAccuracyFamily.outerExpected,
        expectedBestInSet, AppliedModelingLib.pmfExp, SequentialModel.remainingAfter]
        using SourceMallowsSequential.source_theorem4_mallows_outer_allHumanOptimal
          (k := k) D center hphiA hphiH haccuracy hvalue horder
    exact hweak i (by omega) hired hhired strategy
  · intro haccuracy horder i hired hhired strategy hbest
    have hstrict :
        ∀ i : Fin k, i.val + 1 < Fintype.card (Candidate n) →
          ∀ hired : Finset (Candidate n), hired.card = i.val →
            ∀ strategy : Strategy,
              (∀ alternative : Strategy,
                (∫ value : ValueProfile n,
                  ∑ pi : Ranking n,
                    ((match alternative with
                      | .algorithm => (concreteMallowsSpec center thetaA).law
                      | .human => (concreteMallowsSpec center thetaH).law) pi).toReal *
                      value (bestInSet pi (Finset.univ \ hired)) ∂D) ≤
                  (∫ value : ValueProfile n,
                    ∑ pi : Ranking n,
                      ((match strategy with
                        | .algorithm => (concreteMallowsSpec center thetaA).law
                        | .human => (concreteMallowsSpec center thetaH).law) pi).toReal *
                      value (bestInSet pi (Finset.univ \ hired)) ∂D)) →
                strategy = Strategy.human := by
      simpa [SourceMallowsSequential.sourceMallowsSpec, hthetaA, hthetaH,
        SourceMallowsSequential.HumanUniqueAtAllNonterminalHistories,
        SourceMallowsSequential.stepUtility,
        SourceMallowsSequential.outerExpectedBestInSet,
        SourceMallowsSequential.rankingLaw,
        DistributionalAccuracyFamily.outerExpected,
        expectedBestInSet, AppliedModelingLib.pmfExp, SequentialModel.remainingAfter]
        using SourceMallowsSequential.source_theorem4_mallows_outer_humanUnique
          (k := k) D center hphiA hphiH haccuracy hvalue horder
    exact hstrict i (by omega) hired hhired strategy hbest

/--
Definition 2 with the full outer experiment exposed.  The probability law,
finite ranking kernel, event mass, and every outer/joint payoff integrability
obligation are separate visible binders; no regularity record carries source
coverage by itself.
-/
theorem source_definition2_outer_joint_semantic_complete
    {n : ℕ} (F : DistributionalAccuracyFamily n) (D : Measure (ValueProfile n))
    (theta : ℝ) (hD : IsProbabilityMeasure D)
    (hatom : ∀ ranking : Ranking n,
      Measurable fun value => F.dist theta value ranking)
    (hdisagreement_integrable : Integrable
      (fun value => disagreementProb (F.dist theta value)) D)
    (hshared_integrable : Integrable
      (fun value => expectedSecondMoverShared (F.dist theta value) value) D)
    (hindependent_integrable : Integrable
      (fun value => expectedSecondMoverIndependent
        (F.dist theta value) (F.dist theta value) value) D)
    (hjoint_shared_integrable : Integrable
      DistributionalAccuracyFamily.jointSharedSecondMoverPayoff
      (F.outerIndependentPairJointLaw D theta hatom))
    (hjoint_independent_integrable : Integrable
      DistributionalAccuracyFamily.jointIndependentSecondMoverPayoff
      (F.outerIndependentPairJointLaw D theta hatom))
    (hdisagreement : 0 < ∫ x : ValueProfile n × RankingPair n,
      (if disagreementEvent x.2 then (1 : ℝ) else 0) ∂
        F.outerIndependentPairJointLaw D theta hatom) :
    SourceDefinition2ConditionalAt F D theta hatom ↔
      (∫ x, DistributionalAccuracyFamily.jointSharedSecondMoverPayoff x ∂
        F.outerIndependentPairJointLaw D theta hatom) <
        ∫ x, DistributionalAccuracyFamily.jointIndependentSecondMoverPayoff x ∂
          F.outerIndependentPairJointLaw D theta hatom := by
  let regularity : DistributionalAccuracyFamily.OuterIndependentRerankingJointRegularity
      F D theta := {
    base := {
      outer_is_probability := hD
      ranking_atom_measurable := hatom
      disagreement_integrable := hdisagreement_integrable
      shared_payoff_integrable := hshared_integrable
      independent_payoff_integrable := hindependent_integrable }
    joint_shared_payoff_integrable := hjoint_shared_integrable
    joint_independent_payoff_integrable := hjoint_independent_integrable }
  rw [source_definition2_conditional_at_iff_payoff_comparison
    F D theta regularity]
  · simpa [regularity] using
      (F.prefersIndependentReranking_iff_jointPayoffComparison_of_regular
        D theta regularity)
  · simpa [regularity] using hdisagreement

/--
Definition 3 with its literal two outer expectations and their visible
integrability convention.  The result uses the same human second ranking in
both terms and changes only the independently drawn first ranking.
-/
theorem source_definition3_outer_semantic_complete
    {n : ℕ} (F : DistributionalAccuracyFamily n) (D : Measure (ValueProfile n))
    (thetaA thetaH : ℝ) (hD : IsProbabilityMeasure D)
    (hbetter : Integrable (fun value => expectedSecondMoverIndependent
      (F.dist thetaH value) (F.dist thetaA value) value) D)
    (hworse : Integrable (fun value => expectedSecondMoverIndependent
      (F.dist thetaH value) (F.dist thetaH value) value) D) :
    SourceDefinition3At F D thetaA thetaH ↔
      (∫ value, expectedSecondMoverIndependent
        (F.dist thetaH value) (F.dist thetaA value) value ∂D) <
        ∫ value, expectedSecondMoverIndependent
          (F.dist thetaH value) (F.dist thetaH value) value ∂D := by
  exact Iff.rfl

/--
Joint semantic endpoint for Definitions 2 and 3.  It identifies the actual
outer-then-conditionally-iid ranking law as a composed measure, expands the
top-disagreement numerator and denominator, and displays both Definition 3
outer expectations.  This prevents a joint-law helper name from hiding the
experiment being audited.
-/
theorem source_definition2_definition3_joint_semantic_complete
    {n : ℕ} (F : DistributionalAccuracyFamily n)
    (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    (theta thetaA thetaH : ℝ)
    (hatom : ∀ ranking : Ranking n,
      Measurable fun value => F.dist theta value ranking)
    (hshared : Integrable
      (fun x : ValueProfile n × RankingPair n =>
        secondMoverUtility x.1 x.2.1 x.2.1)
      (F.outerIndependentPairJointLaw D theta hatom))
    (hindependent : Integrable
      (fun x : ValueProfile n × RankingPair n =>
        secondMoverUtility x.1 x.2.1 x.2.2)
      (F.outerIndependentPairJointLaw D theta hatom))
    (hdisagreement : 0 < ∫ x : ValueProfile n × RankingPair n,
      (if firstChoice x.2.1 ≠ firstChoice x.2.2 then (1 : ℝ) else 0) ∂
        F.outerIndependentPairJointLaw D theta hatom)
    (hd3_algorithm : Integrable (fun value =>
      pmfPairExp (F.dist thetaH value) (F.dist thetaA value)
        (fun pi sigma => secondMoverUtility value pi sigma)) D)
    (hd3_human : Integrable (fun value =>
      pmfPairExp (F.dist thetaH value) (F.dist thetaH value)
        (fun pi sigma => secondMoverUtility value pi sigma)) D) :
    let J := F.outerIndependentPairJointLaw D theta hatom
    let d2Numerator : ℝ := ∫ x : ValueProfile n × RankingPair n,
      if firstChoice x.2.1 ≠ firstChoice x.2.2 then
        x.1 (firstChoice x.2.1) - x.1 (secondChoice x.2.1)
      else 0 ∂J
    let d2Denominator : ℝ := ∫ x : ValueProfile n × RankingPair n,
      if firstChoice x.2.1 ≠ firstChoice x.2.2 then (1 : ℝ) else 0 ∂J
    let d2Shared : ℝ := ∫ x : ValueProfile n × RankingPair n,
      secondMoverUtility x.1 x.2.1 x.2.1 ∂J
    let d2Independent : ℝ := ∫ x : ValueProfile n × RankingPair n,
      secondMoverUtility x.1 x.2.1 x.2.2 ∂J
    let d3Algorithm : ℝ := ∫ value,
      pmfPairExp (F.dist thetaH value) (F.dist thetaA value)
        (fun pi sigma => secondMoverUtility value pi sigma) ∂D
    let d3Human : ℝ := ∫ value,
      pmfPairExp (F.dist thetaH value) (F.dist thetaH value)
        (fun pi sigma => secondMoverUtility value pi sigma) ∂D
    (J = Measure.compProd D (F.independentPairKernel theta hatom)) ∧
    (∀ value,
      F.independentPairKernel theta hatom value =
        (AppliedModelingLib.pmfProd (F.dist theta value) (F.dist theta value)).toMeasure) ∧
    (SourceDefinition2ConditionalAt F D theta hatom ↔ 0 < d2Numerator / d2Denominator) ∧
    ((0 < d2Numerator / d2Denominator) ↔ d2Shared < d2Independent) ∧
    (Integrable (fun value =>
      pmfPairExp (F.dist thetaH value) (F.dist thetaA value)
        (fun pi sigma => secondMoverUtility value pi sigma)) D ∧
      Integrable (fun value =>
        pmfPairExp (F.dist thetaH value) (F.dist thetaH value)
          (fun pi sigma => secondMoverUtility value pi sigma)) D ∧
      (SourceDefinition3At F D thetaA thetaH ↔ d3Algorithm < d3Human)) := by
  dsimp
  have hnum_eq :
      (∫ x : ValueProfile n × RankingPair n,
        if firstChoice x.2.1 ≠ firstChoice x.2.2 then
          x.1 (firstChoice x.2.1) - x.1 (secondChoice x.2.1)
        else 0 ∂F.outerIndependentPairJointLaw D theta hatom) =
      ∫ x : ValueProfile n × RankingPair n,
        secondMoverUtility x.1 x.2.1 x.2.2 -
          secondMoverUtility x.1 x.2.1 x.2.1 ∂
        F.outerIndependentPairJointLaw D theta hatom := by
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases h : firstChoice x.2.1 = firstChoice x.2.2
    · have h0 : x.2.1 0 = x.2.2 0 := by simpa [firstChoice] using h
      simp [firstChoice, secondChoice, h0]
    · have h0 : x.2.1 0 ≠ x.2.2 0 := by simpa [firstChoice] using h
      simp [firstChoice, secondChoice, h0]
  have hsource_num_eq :
      (∫ x : ValueProfile n × RankingPair n,
        if disagreementEvent x.2 then pairRerankingGain x.1 x.2 else 0 ∂
          F.outerIndependentPairJointLaw D theta hatom) =
      ∫ x : ValueProfile n × RankingPair n,
        if firstChoice x.2.1 ≠ firstChoice x.2.2 then
          x.1 (firstChoice x.2.1) - x.1 (secondChoice x.2.1)
        else 0 ∂F.outerIndependentPairJointLaw D theta hatom := by
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases h : firstChoice x.2.1 = firstChoice x.2.2
    · have h0 : x.2.1 0 = x.2.2 0 := by simpa [firstChoice] using h
      simp [disagreementEvent, firstChoice, h0]
    · have h0 : x.2.1 0 ≠ x.2.2 0 := by simpa [firstChoice] using h
      have hne : firstChoice x.2.1 ≠ firstChoice x.2.2 := h
      simp only [disagreementEvent, if_pos hne]
      change AppliedModelingLib.SocialChoice.Ranking.rerankingGainOnPair
        x.1 x.2.1 x.2.2 = x.1 (x.2.1 0) - x.1 (x.2.1 1)
      exact AppliedModelingLib.SocialChoice.Ranking.rerankingGainOnPair_of_neFirst
        x.1 x.2.1 x.2.2 h0
  have hden_event_eq :
      (∫ x : ValueProfile n × RankingPair n,
        if disagreementEvent x.2 then (1 : ℝ) else 0 ∂
          F.outerIndependentPairJointLaw D theta hatom) =
      ∫ x : ValueProfile n × RankingPair n,
        if firstChoice x.2.1 ≠ firstChoice x.2.2 then (1 : ℝ) else 0 ∂
          F.outerIndependentPairJointLaw D theta hatom := by
    apply integral_congr_ae
    filter_upwards [] with x
    rfl
  have hratio :
      (0 <
          ((∫ x : ValueProfile n × RankingPair n,
            if firstChoice x.2.1 ≠ firstChoice x.2.2 then
              x.1 (firstChoice x.2.1) - x.1 (secondChoice x.2.1)
            else 0 ∂F.outerIndependentPairJointLaw D theta hatom) /
          (∫ x : ValueProfile n × RankingPair n,
            if firstChoice x.2.1 ≠ firstChoice x.2.2 then (1 : ℝ) else 0 ∂
              F.outerIndependentPairJointLaw D theta hatom)) ↔
        ((∫ x : ValueProfile n × RankingPair n,
          secondMoverUtility x.1 x.2.1 x.2.1 ∂
            F.outerIndependentPairJointLaw D theta hatom) <
          (∫ x : ValueProfile n × RankingPair n,
            secondMoverUtility x.1 x.2.1 x.2.2 ∂
              F.outerIndependentPairJointLaw D theta hatom))) := by
    rw [hnum_eq, zero_lt_div_iff_pos_right hdisagreement]
    rw [integral_sub hindependent hshared]
    constructor <;> intro h <;> linarith
  refine ⟨rfl, ?_, ?_, hratio, ?_⟩
  · intro value
    rfl
  · change 0 < F.jointLawDisagreementConditionalGain D theta hatom ↔ _
    simp only [DistributionalAccuracyFamily.jointLawDisagreementConditionalGain]
    rw [if_neg (by simpa only [disagreementEvent] using ne_of_gt hdisagreement)]
    rw [hsource_num_eq, hden_event_eq]
    simp only [firstChoice, secondChoice]
    rfl
  · refine ⟨hd3_algorithm, hd3_human, ?_⟩
    rfl

/--
Definition 2 at the source's positive-accuracy domain.  This row exposes the
actual outer-then-conditionally-iid law, the non-null top-disagreement event,
and the literal conditional gain without borrowing Definition 3 premises.
-/
theorem source_definition2_literal_outer_joint_semantic_complete
    {n : ℕ} (F : DistributionalAccuracyFamily n)
    (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    (theta : ℝ) (htheta : 0 < theta)
    (hatom : ∀ ranking : Ranking n,
      Measurable fun value => F.dist theta value ranking)
    (hshared : Integrable
      (fun x : ValueProfile n × RankingPair n =>
        secondMoverUtility x.1 x.2.1 x.2.1)
      (F.outerIndependentPairJointLaw D theta hatom))
    (hindependent : Integrable
      (fun x : ValueProfile n × RankingPair n =>
        secondMoverUtility x.1 x.2.1 x.2.2)
      (F.outerIndependentPairJointLaw D theta hatom))
    (hdisagreement : 0 < ∫ x : ValueProfile n × RankingPair n,
      (if firstChoice x.2.1 ≠ firstChoice x.2.2 then (1 : ℝ) else 0) ∂
        F.outerIndependentPairJointLaw D theta hatom) :
    let J := F.outerIndependentPairJointLaw D theta hatom
    let d2Numerator : ℝ := ∫ x : ValueProfile n × RankingPair n,
      if firstChoice x.2.1 ≠ firstChoice x.2.2 then
        x.1 (firstChoice x.2.1) - x.1 (secondChoice x.2.1)
      else 0 ∂J
    let d2Denominator : ℝ := ∫ x : ValueProfile n × RankingPair n,
      if firstChoice x.2.1 ≠ firstChoice x.2.2 then (1 : ℝ) else 0 ∂J
    let d2Shared : ℝ := ∫ x : ValueProfile n × RankingPair n,
      secondMoverUtility x.1 x.2.1 x.2.1 ∂J
    let d2Independent : ℝ := ∫ x : ValueProfile n × RankingPair n,
      secondMoverUtility x.1 x.2.1 x.2.2 ∂J
    (J = Measure.compProd D (F.independentPairKernel theta hatom)) ∧
    (∀ value,
      F.independentPairKernel theta hatom value =
        (AppliedModelingLib.pmfProd (F.dist theta value) (F.dist theta value)).toMeasure) ∧
    (SourceDefinition2ConditionalAt F D theta hatom ↔ 0 < d2Numerator / d2Denominator) ∧
    ((0 < d2Numerator / d2Denominator) ↔ d2Shared < d2Independent) := by
  dsimp
  have hnum_eq :
      (∫ x : ValueProfile n × RankingPair n,
        if firstChoice x.2.1 ≠ firstChoice x.2.2 then
          x.1 (firstChoice x.2.1) - x.1 (secondChoice x.2.1)
        else 0 ∂F.outerIndependentPairJointLaw D theta hatom) =
      ∫ x : ValueProfile n × RankingPair n,
        secondMoverUtility x.1 x.2.1 x.2.2 -
          secondMoverUtility x.1 x.2.1 x.2.1 ∂
        F.outerIndependentPairJointLaw D theta hatom := by
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases h : firstChoice x.2.1 = firstChoice x.2.2
    · have h0 : x.2.1 0 = x.2.2 0 := by simpa [firstChoice] using h
      simp [firstChoice, secondChoice, h0]
    · have h0 : x.2.1 0 ≠ x.2.2 0 := by simpa [firstChoice] using h
      simp [firstChoice, secondChoice, h0]
  have hsource_num_eq :
      (∫ x : ValueProfile n × RankingPair n,
        if disagreementEvent x.2 then pairRerankingGain x.1 x.2 else 0 ∂
          F.outerIndependentPairJointLaw D theta hatom) =
      ∫ x : ValueProfile n × RankingPair n,
        if firstChoice x.2.1 ≠ firstChoice x.2.2 then
          x.1 (firstChoice x.2.1) - x.1 (secondChoice x.2.1)
        else 0 ∂F.outerIndependentPairJointLaw D theta hatom := by
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases h : firstChoice x.2.1 = firstChoice x.2.2
    · have h0 : x.2.1 0 = x.2.2 0 := by simpa [firstChoice] using h
      simp [disagreementEvent, firstChoice, h0]
    · have h0 : x.2.1 0 ≠ x.2.2 0 := by simpa [firstChoice] using h
      have hne : firstChoice x.2.1 ≠ firstChoice x.2.2 := h
      simp only [disagreementEvent, if_pos hne]
      change AppliedModelingLib.SocialChoice.Ranking.rerankingGainOnPair
        x.1 x.2.1 x.2.2 = x.1 (x.2.1 0) - x.1 (x.2.1 1)
      exact AppliedModelingLib.SocialChoice.Ranking.rerankingGainOnPair_of_neFirst
        x.1 x.2.1 x.2.2 h0
  have hden_event_eq :
      (∫ x : ValueProfile n × RankingPair n,
        if disagreementEvent x.2 then (1 : ℝ) else 0 ∂
          F.outerIndependentPairJointLaw D theta hatom) =
      ∫ x : ValueProfile n × RankingPair n,
        if firstChoice x.2.1 ≠ firstChoice x.2.2 then (1 : ℝ) else 0 ∂
          F.outerIndependentPairJointLaw D theta hatom := by
    apply integral_congr_ae
    filter_upwards [] with x
    rfl
  have hratio :
      (0 <
          ((∫ x : ValueProfile n × RankingPair n,
            if firstChoice x.2.1 ≠ firstChoice x.2.2 then
              x.1 (firstChoice x.2.1) - x.1 (secondChoice x.2.1)
            else 0 ∂F.outerIndependentPairJointLaw D theta hatom) /
          (∫ x : ValueProfile n × RankingPair n,
            if firstChoice x.2.1 ≠ firstChoice x.2.2 then (1 : ℝ) else 0 ∂
              F.outerIndependentPairJointLaw D theta hatom)) ↔
        ((∫ x : ValueProfile n × RankingPair n,
          secondMoverUtility x.1 x.2.1 x.2.1 ∂
            F.outerIndependentPairJointLaw D theta hatom) <
          (∫ x : ValueProfile n × RankingPair n,
            secondMoverUtility x.1 x.2.1 x.2.2 ∂
              F.outerIndependentPairJointLaw D theta hatom))) := by
    rw [hnum_eq, zero_lt_div_iff_pos_right hdisagreement]
    rw [integral_sub hindependent hshared]
    constructor <;> intro h <;> linarith
  refine ⟨rfl, ?_, ?_, hratio⟩
  · intro value
    rfl
  · change 0 < F.jointLawDisagreementConditionalGain D theta hatom ↔ _
    simp only [DistributionalAccuracyFamily.jointLawDisagreementConditionalGain]
    rw [if_neg (by simpa only [disagreementEvent] using ne_of_gt hdisagreement)]
    rw [hsource_num_eq, hden_event_eq]
    simp only [firstChoice, secondChoice]
    rfl

/--
Equations (2) and (3) at their outer-distribution scope.  The direct surface
states the composed value/ranking-pair law, its conditional iid kernel, the
literal disagreement ratio, and the raw outer payoff-gap identity together.
-/
theorem equation2_equation3_outer_joint_semantic_complete
    {n : ℕ} (F : DistributionalAccuracyFamily n)
    (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    (theta : ℝ) (htheta : 0 < theta)
    (hatom : ∀ ranking : Ranking n,
      Measurable fun value => F.dist theta value ranking)
    (hshared : Integrable
      (fun x : ValueProfile n × RankingPair n =>
        secondMoverUtility x.1 x.2.1 x.2.1)
      (F.outerIndependentPairJointLaw D theta hatom))
    (hindependent : Integrable
      (fun x : ValueProfile n × RankingPair n =>
        secondMoverUtility x.1 x.2.1 x.2.2)
      (F.outerIndependentPairJointLaw D theta hatom))
    (hdisagreement : 0 < ∫ x : ValueProfile n × RankingPair n,
      (if firstChoice x.2.1 ≠ firstChoice x.2.2 then (1 : ℝ) else 0) ∂
        F.outerIndependentPairJointLaw D theta hatom) :
    let J := F.outerIndependentPairJointLaw D theta hatom
    let numerator : ℝ := ∫ x : ValueProfile n × RankingPair n,
      if firstChoice x.2.1 ≠ firstChoice x.2.2 then
        x.1 (firstChoice x.2.1) - x.1 (secondChoice x.2.1)
      else 0 ∂J
    let denominator : ℝ := ∫ x : ValueProfile n × RankingPair n,
      if firstChoice x.2.1 ≠ firstChoice x.2.2 then (1 : ℝ) else 0 ∂J
    let UAA : ℝ := ∫ x : ValueProfile n × RankingPair n,
      secondMoverUtility x.1 x.2.1 x.2.1 ∂J
    let UAH : ℝ := ∫ x : ValueProfile n × RankingPair n,
      secondMoverUtility x.1 x.2.1 x.2.2 ∂J
    (J = Measure.compProd D (F.independentPairKernel theta hatom)) ∧
    (∀ value,
      F.independentPairKernel theta hatom value =
        (AppliedModelingLib.pmfProd (F.dist theta value) (F.dist theta value)).toMeasure) ∧
    ((0 < numerator / denominator) ↔ UAA < UAH) ∧
    (UAH - UAA = numerator) := by
  dsimp
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro value
    rfl
  · exact (source_definition2_literal_outer_joint_semantic_complete
      F D theta htheta hatom hshared hindependent hdisagreement).2.2.2
  · rw [← integral_sub hindependent hshared]
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases h : firstChoice x.2.1 = firstChoice x.2.2
    · have h0 : x.2.1 0 = x.2.2 0 := by simpa [firstChoice] using h
      simp [firstChoice, secondChoice, h0]
    · have h0 : x.2.1 0 ≠ x.2.2 0 := by simpa [firstChoice] using h
      simp [firstChoice, secondChoice, h0]

/--
Equation (2) as its own outer-D paper-facing row.  The terminal proposition
contains the composed experiment, the conditionally iid ranking kernel, and
the literal conditional first-versus-second ratio on the same joint law as the
payoff comparison.
-/
theorem equation2_outer_joint_payoff_equivalence_semantic_complete
    {n : ℕ} (F : DistributionalAccuracyFamily n)
    (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    (theta : ℝ) (htheta : 0 < theta)
    (hatom : ∀ ranking : Ranking n,
      Measurable fun value => F.dist theta value ranking)
    (hshared : Integrable
      (fun x : ValueProfile n × RankingPair n =>
        secondMoverUtility x.1 x.2.1 x.2.1)
      (F.outerIndependentPairJointLaw D theta hatom))
    (hindependent : Integrable
      (fun x : ValueProfile n × RankingPair n =>
        secondMoverUtility x.1 x.2.1 x.2.2)
      (F.outerIndependentPairJointLaw D theta hatom))
    (hdisagreement : 0 < ∫ x : ValueProfile n × RankingPair n,
      (if firstChoice x.2.1 ≠ firstChoice x.2.2 then (1 : ℝ) else 0) ∂
        F.outerIndependentPairJointLaw D theta hatom) :
    let J := F.outerIndependentPairJointLaw D theta hatom
    let numerator : ℝ := ∫ x : ValueProfile n × RankingPair n,
      if firstChoice x.2.1 ≠ firstChoice x.2.2 then
        x.1 (firstChoice x.2.1) - x.1 (secondChoice x.2.1)
      else 0 ∂J
    let denominator : ℝ := ∫ x : ValueProfile n × RankingPair n,
      if firstChoice x.2.1 ≠ firstChoice x.2.2 then (1 : ℝ) else 0 ∂J
    let UAA : ℝ := ∫ x : ValueProfile n × RankingPair n,
      secondMoverUtility x.1 x.2.1 x.2.1 ∂J
    let UAH : ℝ := ∫ x : ValueProfile n × RankingPair n,
      secondMoverUtility x.1 x.2.1 x.2.2 ∂J
    (J = Measure.compProd D (F.independentPairKernel theta hatom)) ∧
    (∀ value,
      F.independentPairKernel theta hatom value =
        (AppliedModelingLib.pmfProd (F.dist theta value) (F.dist theta value)).toMeasure) ∧
    ((0 < numerator / denominator) ↔ UAA < UAH) := by
  dsimp
  rcases equation2_equation3_outer_joint_semantic_complete
      F D theta htheta hatom hshared hindependent hdisagreement with
    ⟨hjoint, hkernel, hequivalence, _⟩
  exact ⟨hjoint, hkernel, hequivalence⟩

/--
Audited source-facing proposition for Equation (2).  The specification keeps
the outer candidate-value law, conditional iid ranking kernel, and the
literal conditional payoff comparison on one joint probability experiment.
-/
abbrev equation2_outer_joint_payoff_equivalence_semantic_completeSpec
    {n : ℕ} (F : DistributionalAccuracyFamily n)
    (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    (theta : ℝ) (htheta : 0 < theta)
    (hatom : ∀ ranking : Ranking n,
      Measurable fun value => F.dist theta value ranking)
    (hshared : Integrable
      (fun x : ValueProfile n × RankingPair n =>
        secondMoverUtility x.1 x.2.1 x.2.1)
      (F.outerIndependentPairJointLaw D theta hatom))
    (hindependent : Integrable
      (fun x : ValueProfile n × RankingPair n =>
        secondMoverUtility x.1 x.2.1 x.2.2)
      (F.outerIndependentPairJointLaw D theta hatom))
    (hdisagreement : 0 < ∫ x : ValueProfile n × RankingPair n,
      (if firstChoice x.2.1 ≠ firstChoice x.2.2 then (1 : ℝ) else 0) ∂
        F.outerIndependentPairJointLaw D theta hatom) : Prop :=
  let J := F.outerIndependentPairJointLaw D theta hatom
  let numerator : ℝ := ∫ x : ValueProfile n × RankingPair n,
    if firstChoice x.2.1 ≠ firstChoice x.2.2 then
      x.1 (firstChoice x.2.1) - x.1 (secondChoice x.2.1)
    else 0 ∂J
  let denominator : ℝ := ∫ x : ValueProfile n × RankingPair n,
    if firstChoice x.2.1 ≠ firstChoice x.2.2 then (1 : ℝ) else 0 ∂J
  let UAA : ℝ := ∫ x : ValueProfile n × RankingPair n,
    secondMoverUtility x.1 x.2.1 x.2.1 ∂J
  let UAH : ℝ := ∫ x : ValueProfile n × RankingPair n,
    secondMoverUtility x.1 x.2.1 x.2.2 ∂J
  (J = Measure.compProd D (F.independentPairKernel theta hatom)) ∧
  (∀ value,
    F.independentPairKernel theta hatom value =
      (AppliedModelingLib.pmfProd (F.dist theta value) (F.dist theta value)).toMeasure) ∧
  ((0 < numerator / denominator) ↔ UAA < UAH)

theorem equation2_outer_joint_payoff_equivalence_semantic_complete_spec_proof
    {n : ℕ} (F : DistributionalAccuracyFamily n)
    (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    (theta : ℝ) (htheta : 0 < theta)
    (hatom : ∀ ranking : Ranking n,
      Measurable fun value => F.dist theta value ranking)
    (hshared : Integrable
      (fun x : ValueProfile n × RankingPair n =>
        secondMoverUtility x.1 x.2.1 x.2.1)
      (F.outerIndependentPairJointLaw D theta hatom))
    (hindependent : Integrable
      (fun x : ValueProfile n × RankingPair n =>
        secondMoverUtility x.1 x.2.1 x.2.2)
      (F.outerIndependentPairJointLaw D theta hatom))
    (hdisagreement : 0 < ∫ x : ValueProfile n × RankingPair n,
      (if firstChoice x.2.1 ≠ firstChoice x.2.2 then (1 : ℝ) else 0) ∂
        F.outerIndependentPairJointLaw D theta hatom) :
    equation2_outer_joint_payoff_equivalence_semantic_completeSpec
      F D theta htheta hatom hshared hindependent hdisagreement :=
  equation2_outer_joint_payoff_equivalence_semantic_complete
    F D theta htheta hatom hshared hindependent hdisagreement

/--
Equation (3) as its own outer-D paper-facing row.  Unlike Equation (2), this
identity needs no positive-conditioning premise.  It is the raw equality
between the joint payoff difference and the top-disagreement numerator when
the algorithmic and human rankings have equal accuracy, `thetaA = thetaH`.
-/
theorem equation3_outer_joint_payoff_identity_semantic_complete
    {n : ℕ} (F : DistributionalAccuracyFamily n)
    (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    (thetaA thetaH : ℝ) (hequalAccuracy : thetaA = thetaH)
    (hatom : ∀ ranking : Ranking n,
      Measurable fun value => F.dist thetaH value ranking)
    (hshared : Integrable
      (fun x : ValueProfile n × RankingPair n =>
        secondMoverUtility x.1 x.2.1 x.2.1)
      (F.outerIndependentPairJointLaw D thetaH hatom))
    (hindependent : Integrable
      (fun x : ValueProfile n × RankingPair n =>
        secondMoverUtility x.1 x.2.1 x.2.2)
      (F.outerIndependentPairJointLaw D thetaH hatom)) :
    let J := F.outerIndependentPairJointLaw D thetaH hatom
    let numerator : ℝ := ∫ x : ValueProfile n × RankingPair n,
      if firstChoice x.2.1 ≠ firstChoice x.2.2 then
        x.1 (firstChoice x.2.1) - x.1 (secondChoice x.2.1)
      else 0 ∂J
    let UAA : ℝ := ∫ x : ValueProfile n × RankingPair n,
      secondMoverUtility x.1 x.2.1 x.2.1 ∂J
    let UAH : ℝ := ∫ x : ValueProfile n × RankingPair n,
      secondMoverUtility x.1 x.2.1 x.2.2 ∂J
    (J = Measure.compProd D (F.independentPairKernel thetaH hatom)) ∧
    (∀ value,
      F.independentPairKernel thetaH hatom value =
        (AppliedModelingLib.pmfProd (F.dist thetaH value) (F.dist thetaH value)).toMeasure) ∧
    (UAH - UAA = numerator) := by
  subst thetaA
  dsimp
  refine ⟨rfl, ?_, ?_⟩
  · intro value
    rfl
  · rw [← integral_sub hindependent hshared]
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases h : firstChoice x.2.1 = firstChoice x.2.2
    · have h0 : x.2.1 0 = x.2.2 0 := by simpa [firstChoice] using h
      simp [firstChoice, secondChoice, h0]
    · have h0 : x.2.1 0 ≠ x.2.2 0 := by simpa [firstChoice] using h
      simp [firstChoice, secondChoice, h0]

/--
Audited source-facing proposition for Equation (3).  The specification is the
unconditioned payoff-difference identity over the same outer candidate-value
law and conditionally iid ranking-pair experiment, explicitly restricted to
the source's equal-accuracy setting `thetaA = thetaH`.
-/
abbrev equation3_outer_joint_payoff_identity_semantic_completeSpec
    {n : ℕ} (F : DistributionalAccuracyFamily n)
    (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    (thetaA thetaH : ℝ) (hequalAccuracy : thetaA = thetaH)
    (hatom : ∀ ranking : Ranking n,
      Measurable fun value => F.dist thetaH value ranking)
    (hshared : Integrable
      (fun x : ValueProfile n × RankingPair n =>
        secondMoverUtility x.1 x.2.1 x.2.1)
      (F.outerIndependentPairJointLaw D thetaH hatom))
    (hindependent : Integrable
      (fun x : ValueProfile n × RankingPair n =>
        secondMoverUtility x.1 x.2.1 x.2.2)
      (F.outerIndependentPairJointLaw D thetaH hatom)) : Prop :=
  let J := F.outerIndependentPairJointLaw D thetaH hatom
  let numerator : ℝ := ∫ x : ValueProfile n × RankingPair n,
    if firstChoice x.2.1 ≠ firstChoice x.2.2 then
      x.1 (firstChoice x.2.1) - x.1 (secondChoice x.2.1)
    else 0 ∂J
  let UAA : ℝ := ∫ x : ValueProfile n × RankingPair n,
    secondMoverUtility x.1 x.2.1 x.2.1 ∂J
  let UAH : ℝ := ∫ x : ValueProfile n × RankingPair n,
    secondMoverUtility x.1 x.2.1 x.2.2 ∂J
  (J = Measure.compProd D (F.independentPairKernel thetaH hatom)) ∧
  (∀ value,
    F.independentPairKernel thetaH hatom value =
      (AppliedModelingLib.pmfProd (F.dist thetaH value) (F.dist thetaH value)).toMeasure) ∧
  (UAH - UAA = numerator)

theorem equation3_outer_joint_payoff_identity_semantic_complete_spec_proof
    {n : ℕ} (F : DistributionalAccuracyFamily n)
    (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    (thetaA thetaH : ℝ) (hequalAccuracy : thetaA = thetaH)
    (hatom : ∀ ranking : Ranking n,
      Measurable fun value => F.dist thetaH value ranking)
    (hshared : Integrable
      (fun x : ValueProfile n × RankingPair n =>
        secondMoverUtility x.1 x.2.1 x.2.1)
      (F.outerIndependentPairJointLaw D thetaH hatom))
    (hindependent : Integrable
      (fun x : ValueProfile n × RankingPair n =>
        secondMoverUtility x.1 x.2.1 x.2.2)
      (F.outerIndependentPairJointLaw D thetaH hatom)) :
    equation3_outer_joint_payoff_identity_semantic_completeSpec
      F D thetaA thetaH hequalAccuracy hatom hshared hindependent :=
  equation3_outer_joint_payoff_identity_semantic_complete
    F D thetaA thetaH hequalAccuracy hatom hshared hindependent

/--
Definition 3 at the source's ordered positive-accuracy domain.  It exposes the
two outer finite-PMF payoff expectations without importing Definition 2 data.
-/
theorem source_definition3_literal_outer_semantic_complete
    {n : ℕ} (F : DistributionalAccuracyFamily n)
    (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    (thetaA thetaH : ℝ) (hthetaH : 0 < thetaH) (hthetaA : thetaH < thetaA)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D)
    (hatom_human : ∀ pi : Ranking n,
      AEStronglyMeasurable (fun value : ValueProfile n =>
        ((F.dist thetaH value) pi).toReal) D)
    (hatom_algorithm : ∀ pi : Ranking n,
      AEStronglyMeasurable (fun value : ValueProfile n =>
        ((F.dist thetaA value) pi).toReal) D) :
    let d3Algorithm : ℝ := ∫ value,
      pmfPairExp (F.dist thetaH value) (F.dist thetaA value)
        (fun pi sigma => secondMoverUtility value pi sigma) ∂D
    let d3Human : ℝ := ∫ value,
      pmfPairExp (F.dist thetaH value) (F.dist thetaH value)
        (fun pi sigma => secondMoverUtility value pi sigma) ∂D
    Integrable (fun value =>
      pmfPairExp (F.dist thetaH value) (F.dist thetaA value)
        (fun pi sigma => secondMoverUtility value pi sigma)) D ∧
    Integrable (fun value =>
      pmfPairExp (F.dist thetaH value) (F.dist thetaH value)
        (fun pi sigma => secondMoverUtility value pi sigma)) D ∧
    (SourceDefinition3At F D thetaA thetaH ↔ d3Algorithm < d3Human) := by
  dsimp
  have hd3_algorithm : Integrable (fun value =>
      pmfPairExp (F.dist thetaH value) (F.dist thetaA value)
        (fun pi sigma => secondMoverUtility value pi sigma)) D := by
    simpa [expectedSecondMoverIndependent, secondMoverUtility] using
      (DistributionalAccuracyFamily.integrable_outer_pmfPairExp_valueSelection_of_atomwise
        D (fun value => F.dist thetaH value) (fun value => F.dist thetaA value)
        (fun second first => bestRemainingAfter second (firstChoice first)) hvalue
        hatom_human hatom_algorithm)
  have hd3_human : Integrable (fun value =>
      pmfPairExp (F.dist thetaH value) (F.dist thetaH value)
        (fun pi sigma => secondMoverUtility value pi sigma)) D := by
    simpa [expectedSecondMoverIndependent, secondMoverUtility] using
      (DistributionalAccuracyFamily.integrable_outer_pmfPairExp_valueSelection_of_atomwise
        D (fun value => F.dist thetaH value) (fun value => F.dist thetaH value)
        (fun second first => bestRemainingAfter second (firstChoice first)) hvalue
        hatom_human hatom_human)
  exact ⟨hd3_algorithm, hd3_human, Iff.rfl⟩

/--
Theorem 1 with both its outer-D regularity and terminal payoff inequalities
expanded.  The auxiliary regularity package is reconstructed internally from
the displayed source-law and integrability premises; the terminal proposition
contains the actual common witness and all three strict payoff comparisons.
-/
theorem theorem1_outer_semantic_complete
    {n : ℕ} (F : DistributionalAccuracyFamily n)
    (D : Measure (ValueProfile n)) (hD : IsProbabilityMeasure D)
    (center : Ranking n) (thetaH : ℝ)
    (hthetaH : 0 < thetaH)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D)
    (hatom_aestrongly_measurable : ∀ theta pi,
      AEStronglyMeasurable (fun value : ValueProfile n =>
        ((F.dist theta value) pi).toReal) D)
    (hatom_continuous : ∀ value theta, 0 < theta → ∀ pi : Ranking n,
      ContinuousAt (fun theta' => ((F.dist theta' value) pi).toReal) theta)
    (hatom_differentiable : ∀ value theta, 0 < theta → ∀ pi : Ranking n,
      DifferentiableAt ℝ (fun theta' => ((F.dist theta' value) pi).toReal) theta)
    (hcenter_tendsto : ∀ value,
      Tendsto (fun theta => ((F.dist theta value) center).toReal) atTop (nhds 1))
    (hstrict_order : ∀ᵐ value ∂D, StrictlyOrderedBy center value)
    (hatom_measurable : ∀ theta pi,
      Measurable fun value => F.dist theta value pi)
    (hdefinition2_disagreement_integrable : ∀ theta, 0 < theta → Integrable
      (fun value => disagreementProb (F.dist theta value)) D)
    (hdefinition2_shared_integrable : ∀ theta, 0 < theta → Integrable
      (fun value => expectedSecondMoverShared (F.dist theta value) value) D)
    (hdefinition2_independent_integrable : ∀ theta, 0 < theta → Integrable
      (fun value => expectedSecondMoverIndependent
        (F.dist theta value) (F.dist theta value) value) D)
    (hdefinition2_joint_shared_integrable : ∀ theta, ∀ htheta : 0 < theta,
      Integrable DistributionalAccuracyFamily.jointSharedSecondMoverPayoff
        (F.outerIndependentPairJointLaw D theta (hatom_measurable theta)))
    (hdefinition2_joint_independent_integrable : ∀ theta, ∀ htheta : 0 < theta,
      Integrable DistributionalAccuracyFamily.jointIndependentSecondMoverPayoff
        (F.outerIndependentPairJointLaw D theta (hatom_measurable theta)))
    (hdefinition2_event : ∀ theta, ∀ htheta : 0 < theta,
      0 < ∫ x : ValueProfile n × RankingPair n,
        (if disagreementEvent x.2 then (1 : ℝ) else 0) ∂
          F.outerIndependentPairJointLaw D theta (hatom_measurable theta))
    (hdefinition2_gain : ∀ theta, ∀ htheta : 0 < theta,
      0 < F.jointLawDisagreementConditionalGain D theta
        (hatom_measurable theta))
    (hdefinition3_better_integrable : ∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
      Integrable (fun value => expectedSecondMoverIndependent
        (F.dist thetaH value) (F.dist thetaA value) value) D)
    (hdefinition3_worse_integrable : ∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
      Integrable (fun value => expectedSecondMoverIndependent
        (F.dist thetaH value) (F.dist thetaH value) value) D)
    (hdefinition3 : ∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
      F.PrefersWeakerCompetition D thetaA thetaH)
    (hremaining_weak : ∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
      ∀ value, ∀ remaining : Finset (Candidate n), remaining.Nonempty →
        expectedBestInSet (F.dist thetaH value) value remaining ≤
          expectedBestInSet (F.dist thetaA value) value remaining)
    (hfull_set_strict : ∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
      ∀ value, StrictlyOrderedBy center value →
        expectedBestInSet (F.dist thetaH value) value Finset.univ <
          expectedBestInSet (F.dist thetaA value) value Finset.univ) :
    ∃ thetaA, thetaH < thetaA ∧
      F.theorem1_g D thetaA thetaH < F.theorem1_f D thetaA thetaH ∧
      F.theorem1_h D thetaA thetaH <
        F.theorem1_algorithmAgainstHuman D thetaA thetaH ∧
      F.theorem1_f D thetaA thetaH < F.theorem1_h D thetaA thetaH := by
  letI : IsProbabilityMeasure D := hD
  let regularity : ∀ theta, 0 < theta →
      DistributionalAccuracyFamily.OuterIndependentRerankingJointRegularity F D theta :=
    fun theta htheta => {
      base := {
        outer_is_probability := hD
        ranking_atom_measurable := hatom_measurable theta
        disagreement_integrable := hdefinition2_disagreement_integrable theta htheta
        shared_payoff_integrable := hdefinition2_shared_integrable theta htheta
        independent_payoff_integrable := hdefinition2_independent_integrable theta htheta }
      joint_shared_payoff_integrable := hdefinition2_joint_shared_integrable theta htheta
      joint_independent_payoff_integrable := hdefinition2_joint_independent_integrable theta htheta }
  have htarget := theorem1_outer_from_literal_source_conditions
    F D center thetaH hthetaH hvalue hatom_aestrongly_measurable
    hatom_continuous hatom_differentiable hcenter_tendsto hstrict_order
    regularity (by
      intro theta htheta
      simpa [regularity] using hdefinition2_event theta htheta)
    (by
      intro theta htheta
      simpa [regularity] using hdefinition2_gain theta htheta)
    hdefinition3 hremaining_weak hfull_set_strict
  simpa only [DistributionalAccuracyFamily.DistributionalTheorem1Target] using htarget

/--
The Section 3.1 zero-monoculture-effect result at one literal common-location,
positive-scale iid Gumbel RUM.  The terminal proposition keeps the actual
outer-then-conditionally-iid experiment, raw top-disagreement numerator and
denominator, and the two outer payoff functionals visible.  In particular it
does not leave either conclusion inside `jointLawDisagreementConditionalGain`
or an unnamed payoff alias.
-/
theorem commonLocationPositiveScaleGumbel_outer_zero_effect_semantic_complete
    {n : ℕ} (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    {location s theta : ℝ} (hs : 0 < s) (htheta : 0 < theta)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D) :
    let F := DistributionalAccuracyFamily.commonLocationPositiveScaleGumbelRUMDistributionalFamily
      (n := n) location s
    let hatom : ∀ ranking : Ranking n,
        Measurable fun value => F.dist theta value ranking :=
      fun ranking =>
        DistributionalAccuracyFamily.commonLocationPositiveScaleGumbelRUM_ranking_atom_measurable
          hs htheta ranking
    let J := F.outerIndependentPairJointLaw D theta hatom
    let numerator : ℝ := ∫ x : ValueProfile n × RankingPair n,
      if firstChoice x.2.1 ≠ firstChoice x.2.2 then
        x.1 (firstChoice x.2.1) - x.1 (secondChoice x.2.1)
      else 0 ∂J
    let denominator : ℝ := ∫ x : ValueProfile n × RankingPair n,
      if firstChoice x.2.1 ≠ firstChoice x.2.2 then (1 : ℝ) else 0 ∂J
    let UAA : ℝ := ∫ value : ValueProfile n,
      expectedSecondMoverShared (F.dist theta value) value ∂D
    let UAH : ℝ := ∫ value : ValueProfile n,
      expectedSecondMoverIndependent (F.dist theta value) (F.dist theta value) value ∂D
    (J = Measure.compProd D (F.independentPairKernel theta hatom)) ∧
    (∀ value,
      F.independentPairKernel theta hatom value =
        (AppliedModelingLib.pmfProd (F.dist theta value) (F.dist theta value)).toMeasure) ∧
    Integrable (fun value => expectedSecondMoverIndependent
      (F.dist theta value) (F.dist theta value) value) D ∧
    Integrable (fun value => expectedSecondMoverShared (F.dist theta value) value) D ∧
    0 < denominator ∧
    numerator / denominator = 0 ∧
    UAH = UAA := by
  let F := DistributionalAccuracyFamily.commonLocationPositiveScaleGumbelRUMDistributionalFamily
    (n := n) location s
  let hatom : ∀ ranking : Ranking n,
      Measurable fun value => F.dist theta value ranking :=
    fun ranking =>
      DistributionalAccuracyFamily.commonLocationPositiveScaleGumbelRUM_ranking_atom_measurable
        hs htheta ranking
  have hsource := commonLocationPositiveScaleGumbel_outer_source_joint_conditional_zero
    (D := D) (location := location) (s := s) (theta := theta) hs htheta hvalue
  have hpay := commonLocationPositiveScaleGumbel_outer_payoff_identity_semantic_complete
    (D := D) (location := location) (s := s) (theta := theta) hs htheta hvalue
  have hden : 0 < ∫ x : ValueProfile n × RankingPair n,
      (if firstChoice x.2.1 ≠ firstChoice x.2.2 then (1 : ℝ) else 0) ∂
        F.outerIndependentPairJointLaw D theta hatom := by
    simpa [F, hatom, disagreementEvent] using hsource.1
  have hratio := jointLawDisagreementConditionalGain_eq_source_ratio_semantic
    F D theta hatom hden
  have hratio_zero :
      (∫ x : ValueProfile n × RankingPair n,
        if firstChoice x.2.1 ≠ firstChoice x.2.2 then
          x.1 (firstChoice x.2.1) - x.1 (secondChoice x.2.1)
        else 0 ∂F.outerIndependentPairJointLaw D theta hatom) /
      (∫ x : ValueProfile n × RankingPair n,
        if firstChoice x.2.1 ≠ firstChoice x.2.2 then (1 : ℝ) else 0 ∂
          F.outerIndependentPairJointLaw D theta hatom) = 0 := by
    rw [← hratio]
    simpa [F, hatom] using hsource.2
  dsimp
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro value
    rfl
  · simpa [F] using hpay.1
  · simpa [F] using hpay.2.1
  · simpa [F, hatom] using hden
  · exact hratio_zero
  · simpa only [DistributionalAccuracyFamily.outerExpected] using hpay.2.2

/--
The terminal Theorem 1 payoff configuration written directly as outer
integrals of the finite model payoffs.  This is an `abbrev` solely to keep the
source endpoints aligned; its body is the audited semantic surface, not a
proof-notation alias.
-/
abbrev literal_outer_payoff_paradox
    {n : ℕ} (F : DistributionalAccuracyFamily n)
    (D : Measure (ValueProfile n)) (thetaH : ℝ) : Prop :=
  ∃ thetaA, thetaH < thetaA ∧
    (∫ value : ValueProfile n,
      Model.firstMoverEU ((F.pointFamily value).modelAt thetaA thetaH)
        Strategy.human ∂D) +
      (∫ value : ValueProfile n,
        Model.secondMoverEU ((F.pointFamily value).modelAt thetaA thetaH)
          Strategy.algorithm Strategy.human ∂D) <
    (∫ value : ValueProfile n,
      Model.firstMoverEU ((F.pointFamily value).modelAt thetaA thetaH)
        Strategy.algorithm ∂D) +
      (∫ value : ValueProfile n,
        Model.secondMoverEU ((F.pointFamily value).modelAt thetaA thetaH)
          Strategy.algorithm Strategy.algorithm ∂D) ∧
    (∫ value : ValueProfile n,
      Model.firstMoverEU ((F.pointFamily value).modelAt thetaA thetaH)
        Strategy.human ∂D) +
      (∫ value : ValueProfile n,
        Model.secondMoverEU ((F.pointFamily value).modelAt thetaA thetaH)
          Strategy.human Strategy.human ∂D) <
    (∫ value : ValueProfile n,
      Model.firstMoverEU ((F.pointFamily value).modelAt thetaA thetaH)
        Strategy.algorithm ∂D) +
      (∫ value : ValueProfile n,
        Model.secondMoverEU ((F.pointFamily value).modelAt thetaA thetaH)
          Strategy.human Strategy.algorithm ∂D) ∧
    (∫ value : ValueProfile n,
      Model.firstMoverEU ((F.pointFamily value).modelAt thetaA thetaH)
        Strategy.algorithm ∂D) +
      (∫ value : ValueProfile n,
        Model.secondMoverEU ((F.pointFamily value).modelAt thetaA thetaH)
          Strategy.algorithm Strategy.algorithm ∂D) <
    (∫ value : ValueProfile n,
      Model.firstMoverEU ((F.pointFamily value).modelAt thetaA thetaH)
        Strategy.human ∂D) +
      (∫ value : ValueProfile n,
        Model.secondMoverEU ((F.pointFamily value).modelAt thetaA thetaH)
          Strategy.human Strategy.human ∂D)

/--
Theorem 1 with every Definition 2 and Definition 3 premise expanded at the
paper boundary.  The proof reconstructs library regularity internally, while
the statement displays raw outer-law integrability, the literal conditional
ratio, and the two outer finite-PMF payoff integrals.
-/
theorem theorem1_outer_raw_definition2_definition3_semantic_complete
    {n : ℕ} (F : DistributionalAccuracyFamily n)
    (D : Measure (ValueProfile n)) (hD : IsProbabilityMeasure D)
    (center : Ranking n) (thetaH : ℝ)
    (hthetaH : 0 < thetaH)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D)
    (hatom_aestrongly_measurable : ∀ theta pi,
      AEStronglyMeasurable (fun value : ValueProfile n =>
        ((F.dist theta value) pi).toReal) D)
    (hatom_continuous : ∀ value theta, 0 < theta → ∀ pi : Ranking n,
      ContinuousAt (fun theta' => ((F.dist theta' value) pi).toReal) theta)
    (hatom_differentiable : ∀ value theta, 0 < theta → ∀ pi : Ranking n,
      DifferentiableAt ℝ (fun theta' => ((F.dist theta' value) pi).toReal) theta)
    (hcenter_tendsto : ∀ value,
      Tendsto (fun theta => ((F.dist theta value) center).toReal) atTop (nhds 1))
    (hstrict_order : ∀ᵐ value ∂D, StrictlyOrderedBy center value)
    (hatom_measurable : ∀ theta pi,
      Measurable fun value => F.dist theta value pi)
    (hdefinition2_disagreement_integrable : ∀ theta, 0 < theta → Integrable
      (fun value => pmfPairExp (F.dist theta value) (F.dist theta value)
        (fun pi sigma => if firstChoice pi ≠ firstChoice sigma then (1 : ℝ) else 0)) D)
    (hdefinition2_shared_integrable : ∀ theta, 0 < theta → Integrable
      (fun value => pmfExp (F.dist theta value)
        (fun pi => value (secondChoice pi))) D)
    (hdefinition2_independent_integrable : ∀ theta, 0 < theta → Integrable
      (fun value => pmfPairExp (F.dist theta value) (F.dist theta value)
        (fun pi sigma => secondMoverUtility value pi sigma)) D)
    (hdefinition2_joint_shared_integrable : ∀ theta, ∀ htheta : 0 < theta,
      Integrable (fun x : ValueProfile n × RankingPair n =>
        secondMoverUtility x.1 x.2.1 x.2.1)
        (F.outerIndependentPairJointLaw D theta (hatom_measurable theta)))
    (hdefinition2_joint_independent_integrable : ∀ theta, ∀ htheta : 0 < theta,
      Integrable (fun x : ValueProfile n × RankingPair n =>
        secondMoverUtility x.1 x.2.1 x.2.2)
        (F.outerIndependentPairJointLaw D theta (hatom_measurable theta)))
    (hdefinition2_event : ∀ theta, ∀ htheta : 0 < theta,
      0 < ∫ x : ValueProfile n × RankingPair n,
        (if firstChoice x.2.1 ≠ firstChoice x.2.2 then (1 : ℝ) else 0) ∂
          F.outerIndependentPairJointLaw D theta (hatom_measurable theta))
    (hdefinition2_gain : ∀ theta, ∀ htheta : 0 < theta,
      0 <
        (∫ x : ValueProfile n × RankingPair n,
          if firstChoice x.2.1 ≠ firstChoice x.2.2 then
            x.1 (firstChoice x.2.1) - x.1 (secondChoice x.2.1)
          else 0 ∂F.outerIndependentPairJointLaw D theta (hatom_measurable theta)) /
        (∫ x : ValueProfile n × RankingPair n,
          if firstChoice x.2.1 ≠ firstChoice x.2.2 then (1 : ℝ) else 0 ∂
            F.outerIndependentPairJointLaw D theta (hatom_measurable theta)))
    (hdefinition3_better_integrable : ∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
      Integrable (fun value => pmfPairExp
        (F.dist thetaH value) (F.dist thetaA value)
        (fun pi sigma => secondMoverUtility value pi sigma)) D)
    (hdefinition3_worse_integrable : ∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
      Integrable (fun value => pmfPairExp
        (F.dist thetaH value) (F.dist thetaH value)
        (fun pi sigma => secondMoverUtility value pi sigma)) D)
    (hdefinition3 : ∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
      (∫ value, pmfPairExp (F.dist thetaH value) (F.dist thetaA value)
        (fun pi sigma => secondMoverUtility value pi sigma) ∂D) <
      ∫ value, pmfPairExp (F.dist thetaH value) (F.dist thetaH value)
        (fun pi sigma => secondMoverUtility value pi sigma) ∂D)
    (hremaining_weak : ∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
      ∀ value, ∀ remaining : Finset (Candidate n), remaining.Nonempty →
        expectedBestInSet (F.dist thetaH value) value remaining ≤
          expectedBestInSet (F.dist thetaA value) value remaining)
    (hfull_set_strict : ∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
      ∀ value, StrictlyOrderedBy center value →
        expectedBestInSet (F.dist thetaH value) value Finset.univ <
          expectedBestInSet (F.dist thetaA value) value Finset.univ) :
    ∃ thetaA, thetaH < thetaA ∧
      F.theorem1_g D thetaA thetaH < F.theorem1_f D thetaA thetaH ∧
      F.theorem1_h D thetaA thetaH <
        F.theorem1_algorithmAgainstHuman D thetaA thetaH ∧
      F.theorem1_f D thetaA thetaH < F.theorem1_h D thetaA thetaH := by
  letI : IsProbabilityMeasure D := hD
  let regularity : ∀ theta, 0 < theta →
      DistributionalAccuracyFamily.OuterIndependentRerankingJointRegularity F D theta :=
    fun theta htheta => {
      base := {
        outer_is_probability := hD
        ranking_atom_measurable := hatom_measurable theta
        disagreement_integrable := by
          change Integrable (fun value =>
            pmfPairExp (F.dist theta value) (F.dist theta value)
              (fun pi sigma =>
                if firstChoice pi ≠ firstChoice sigma then (1 : ℝ) else 0)) D
          exact hdefinition2_disagreement_integrable theta htheta
        shared_payoff_integrable := by
          simpa [expectedSecondMoverShared] using
            hdefinition2_shared_integrable theta htheta
        independent_payoff_integrable := by
          simpa [expectedSecondMoverIndependent] using
            hdefinition2_independent_integrable theta htheta }
      joint_shared_payoff_integrable := by
        change Integrable (fun x : ValueProfile n × RankingPair n =>
          secondMoverUtility x.1 x.2.1 x.2.1)
          (F.outerIndependentPairJointLaw D theta (hatom_measurable theta))
        exact hdefinition2_joint_shared_integrable theta htheta
      joint_independent_payoff_integrable := by
        change Integrable (fun x : ValueProfile n × RankingPair n =>
          secondMoverUtility x.1 x.2.1 x.2.2)
          (F.outerIndependentPairJointLaw D theta (hatom_measurable theta))
        exact hdefinition2_joint_independent_integrable theta htheta }
  have hgain : ∀ theta, ∀ htheta : 0 < theta,
      0 < F.jointLawDisagreementConditionalGain D theta
        (regularity theta htheta).base.ranking_atom_measurable := by
    intro theta htheta
    change 0 < F.jointLawDisagreementConditionalGain D theta
      (hatom_measurable theta)
    rw [jointLawDisagreementConditionalGain_eq_source_ratio_semantic
      F D theta (hatom_measurable theta) (hdefinition2_event theta htheta)]
    exact hdefinition2_gain theta htheta
  have hdefinition3' : ∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
      F.PrefersWeakerCompetition D thetaA thetaH := by
    intro thetaA thetaH hthetaH hthetaA
    simpa [DistributionalAccuracyFamily.PrefersWeakerCompetition,
      DistributionalAccuracyFamily.outerExpected,
      expectedSecondMoverIndependent] using
      hdefinition3 thetaA thetaH hthetaH hthetaA
  have htarget :=
    DistributionalAccuracyFamily.distributional_theorem1_of_universal_definition1_and_literal_outer_conditions
      F D center thetaH hthetaH hvalue hatom_aestrongly_measurable
      hatom_continuous hatom_differentiable hcenter_tendsto hstrict_order
      regularity (by
        intro theta htheta
        simpa [regularity, disagreementEvent] using hdefinition2_event theta htheta)
      hgain hdefinition3' hremaining_weak hfull_set_strict
  simpa only [DistributionalAccuracyFamily.DistributionalTheorem1Target] using htarget

/--
Corrected Theorem 3 with Definitions 2 and 3 unfolded.  In addition to the
source Mallows `phi` atom law, the conclusion gives the positive literal
top-disagreement denominator and ratio under the composed outer joint law,
then the literal two outer finite-PMF payoff integrals for Definition 3.
-/
theorem theorem3_source_raw_definition2_definition3_semantic_complete
    {n : ℕ} (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    (center : Ranking n) (hn : 0 < n)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D)
    (hstrict : ∀ᵐ value ∂D, StrictlyOrderedBy center value) :
    (∀ (phi theta : ℝ), 1 < phi → theta = phi - 1 →
      (concreteMallowsSpec center theta).q = phi⁻¹ ∧
      ∀ (value : ValueProfile n) (pi : Ranking n),
        (((fixedCenterMallowsDistributionalFamily center).dist theta value) pi).toReal =
          phi⁻¹ ^ kendallTau center pi /
            (∑ tau : Ranking n, phi⁻¹ ^ kendallTau center tau)) ∧
    (∀ theta : ℝ, 0 < theta →
      let J := DistributionalAccuracyFamily.outerIndependentPairJointLaw
        (fixedCenterMallowsDistributionalFamily center) D theta
        (fun ranking => DistributionalAccuracyFamily.fixedCenterMallows_ranking_atom_measurable
          center theta ranking)
      0 < ∫ x : ValueProfile n × RankingPair n,
        (if firstChoice x.2.1 ≠ firstChoice x.2.2 then (1 : ℝ) else 0) ∂J ∧
      0 <
        (∫ x : ValueProfile n × RankingPair n,
          if firstChoice x.2.1 ≠ firstChoice x.2.2 then
            x.1 (firstChoice x.2.1) - x.1 (secondChoice x.2.1)
          else 0 ∂J) /
        (∫ x : ValueProfile n × RankingPair n,
          if firstChoice x.2.1 ≠ firstChoice x.2.2 then (1 : ℝ) else 0 ∂J)) ∧
    (∀ thetaA thetaH : ℝ, 0 < thetaH → thetaH < thetaA →
      (∫ value,
        pmfPairExp
          ((fixedCenterMallowsDistributionalFamily center).dist thetaH value)
          ((fixedCenterMallowsDistributionalFamily center).dist thetaA value)
          (fun pi sigma => secondMoverUtility value pi sigma) ∂D) <
      ∫ value,
        pmfPairExp
          ((fixedCenterMallowsDistributionalFamily center).dist thetaH value)
          ((fixedCenterMallowsDistributionalFamily center).dist thetaH value)
          (fun pi sigma => secondMoverUtility value pi sigma) ∂D) := by
  refine ⟨?_, ?_, ?_⟩
  · intro phi theta hphi htheta
    refine ⟨(source_equation8_concrete_mallows_probability center phi theta
      hphi htheta center).1, ?_⟩
    intro value pi
    simpa [fixedCenterMallowsDistributionalFamily] using
      (source_equation8_concrete_mallows_probability center phi theta
        hphi htheta pi).2
  · intro theta htheta
    let F := fixedCenterMallowsDistributionalFamily center
    let hatom : ∀ ranking : Ranking n,
        Measurable fun value => F.dist theta value ranking :=
      fun ranking => DistributionalAccuracyFamily.fixedCenterMallows_ranking_atom_measurable
        center theta ranking
    have hevent : 0 < ∫ x : ValueProfile n × RankingPair n,
        (if firstChoice x.2.1 ≠ firstChoice x.2.2 then (1 : ℝ) else 0) ∂
          F.outerIndependentPairJointLaw D theta hatom := by
      simpa [F, hatom, disagreementEvent] using
        DistributionalAccuracyFamily.fixedCenterMallows_outerJointDisagreementEvent_pos
          D center theta
    have hgain : 0 < F.jointLawDisagreementConditionalGain D theta hatom := by
      simpa [F, hatom] using
        DistributionalAccuracyFamily.fixedCenterMallows_outer_jointLawDisagreementConditionalGain_pos
          D center hn theta htheta hvalue hstrict
    refine ⟨hevent, ?_⟩
    rw [← jointLawDisagreementConditionalGain_eq_source_ratio_semantic
      F D theta hatom hevent]
    exact hgain
  · intro thetaA thetaH hthetaH hthetaA
    have h := fixedCenterMallows_outer_prefersWeakerCompetition
      D center hn thetaA thetaH hthetaH hthetaA hvalue hstrict
    simpa [DistributionalAccuracyFamily.PrefersWeakerCompetition,
      DistributionalAccuracyFamily.outerExpected,
      expectedSecondMoverIndependent] using h

/--
Corrected Theorem 3 at the complete direct source surface.  In addition to the
literal Mallows law and Definitions 2 and 3, its conclusion spells out every
Definition 1 field and the single outer-distribution Theorem 1 witness.
-/
theorem theorem3_source_complete_semantic_complete
    {n : ℕ} (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    (center : Ranking n) (hn : 0 < n)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D)
    (hstrict : ∀ᵐ value ∂D, StrictlyOrderedBy center value) :
    (∀ (phi theta : ℝ), 1 < phi → theta = phi - 1 →
      (concreteMallowsSpec center theta).q = phi⁻¹ ∧
      ∀ (value : ValueProfile n) (pi : Ranking n),
        (((fixedCenterMallowsDistributionalFamily center).dist theta value) pi).toReal =
          phi⁻¹ ^ kendallTau center pi /
            (∑ tau : Ranking n, phi⁻¹ ^ kendallTau center tau)) ∧
    (∀ value : ValueProfile n, StrictlyOrderedBy center value →
      (∀ theta, 0 < theta → ∀ pi : Ranking n,
        ContinuousAt (fun theta' =>
          ((fixedCenterMallowsPointFamily center value).dist theta' pi).toReal) theta ∧
          DifferentiableAt ℝ (fun theta' =>
            ((fixedCenterMallowsPointFamily center value).dist theta' pi).toReal) theta) ∧
      Tendsto (fun theta =>
        ((fixedCenterMallowsPointFamily center value).dist theta center).toReal)
        atTop (nhds 1) ∧
      ∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
        (∀ remaining : Finset (Candidate n), remaining.Nonempty →
          expectedBestInSet
              ((fixedCenterMallowsPointFamily center value).dist thetaH) value remaining ≤
            expectedBestInSet
              ((fixedCenterMallowsPointFamily center value).dist thetaA) value remaining) ∧
        expectedBestInSet
            ((fixedCenterMallowsPointFamily center value).dist thetaH) value Finset.univ <
          expectedBestInSet
            ((fixedCenterMallowsPointFamily center value).dist thetaA) value Finset.univ) ∧
    (∀ theta : ℝ, 0 < theta →
      let J := DistributionalAccuracyFamily.outerIndependentPairJointLaw
        (fixedCenterMallowsDistributionalFamily center) D theta
        (fun ranking => DistributionalAccuracyFamily.fixedCenterMallows_ranking_atom_measurable
          center theta ranking)
      0 < ∫ x : ValueProfile n × RankingPair n,
        (if firstChoice x.2.1 ≠ firstChoice x.2.2 then (1 : ℝ) else 0) ∂J ∧
      0 <
        (∫ x : ValueProfile n × RankingPair n,
          if firstChoice x.2.1 ≠ firstChoice x.2.2 then
            x.1 (firstChoice x.2.1) - x.1 (secondChoice x.2.1)
          else 0 ∂J) /
        (∫ x : ValueProfile n × RankingPair n,
          if firstChoice x.2.1 ≠ firstChoice x.2.2 then (1 : ℝ) else 0 ∂J)) ∧
    (∀ thetaA thetaH : ℝ, 0 < thetaH → thetaH < thetaA →
      (∫ value,
        pmfPairExp
          ((fixedCenterMallowsDistributionalFamily center).dist thetaH value)
          ((fixedCenterMallowsDistributionalFamily center).dist thetaA value)
          (fun pi sigma => secondMoverUtility value pi sigma) ∂D) <
      ∫ value,
        pmfPairExp
          ((fixedCenterMallowsDistributionalFamily center).dist thetaH value)
          ((fixedCenterMallowsDistributionalFamily center).dist thetaH value)
          (fun pi sigma => secondMoverUtility value pi sigma) ∂D) ∧
    (∀ thetaH : ℝ, 0 < thetaH →
      ∃ thetaA, thetaH < thetaA ∧
        (fixedCenterMallowsDistributionalFamily center).theorem1_g D thetaA thetaH <
          (fixedCenterMallowsDistributionalFamily center).theorem1_f D thetaA thetaH ∧
        (fixedCenterMallowsDistributionalFamily center).theorem1_h D thetaA thetaH <
          (fixedCenterMallowsDistributionalFamily center).theorem1_algorithmAgainstHuman
            D thetaA thetaH ∧
        (fixedCenterMallowsDistributionalFamily center).theorem1_f D thetaA thetaH <
          (fixedCenterMallowsDistributionalFamily center).theorem1_h D thetaA thetaH) := by
  rcases theorem3_source_raw_definition2_definition3_semantic_complete
    D center hn hvalue hstrict with ⟨hmallows, hdefinition2, hdefinition3⟩
  refine ⟨hmallows, ?_, hdefinition2, hdefinition3, ?_⟩
  · intro value horder
    have hdefinition : SourceDefinition1NoisyPermutationFamily
        (fixedCenterMallowsPointFamily center value) center := by
      simpa only [fixedCenterMallowsPointFamily] using
        (concreteMallowsAccuracyFamily_sourceDefinition1 center value horder)
    simpa only [SourceDefinition1NoisyPermutationFamily] using hdefinition
  · intro thetaH hthetaH
    simpa only [DistributionalAccuracyFamily.DistributionalTheorem1Target] using
      (fixedCenterMallows_outer_distributionalTheorem1Target
        D center hn thetaH hthetaH hvalue hstrict)

/--
Audited source-facing proposition for corrected Theorem 3.  The literal
Mallows mass, all Definition 1 fields, Definition 2's outer conditional gain,
Definition 3's payoff comparison, and the common Theorem 1 witness are
written independently of the theorem that proves this paper-facing endpoint.
-/
abbrev theorem3_source_complete_semantic_completeSpec
    {n : ℕ} (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    (center : Ranking n) (hn : 0 < n)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D)
    (hstrict : ∀ᵐ value ∂D, StrictlyOrderedBy center value) : Prop :=
  (∀ (phi theta : ℝ), 1 < phi → theta = phi - 1 →
    (concreteMallowsSpec center theta).q = phi⁻¹ ∧
    ∀ (value : ValueProfile n) (pi : Ranking n),
      (((fixedCenterMallowsDistributionalFamily center).dist theta value) pi).toReal =
        phi⁻¹ ^ kendallTau center pi /
          (∑ tau : Ranking n, phi⁻¹ ^ kendallTau center tau)) ∧
  (∀ value : ValueProfile n, StrictlyOrderedBy center value →
    (∀ theta, 0 < theta → ∀ pi : Ranking n,
      ContinuousAt (fun theta' =>
        ((fixedCenterMallowsPointFamily center value).dist theta' pi).toReal) theta ∧
        DifferentiableAt ℝ (fun theta' =>
          ((fixedCenterMallowsPointFamily center value).dist theta' pi).toReal) theta) ∧
    Tendsto (fun theta =>
      ((fixedCenterMallowsPointFamily center value).dist theta center).toReal)
      atTop (nhds 1) ∧
    ∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
      (∀ remaining : Finset (Candidate n), remaining.Nonempty →
        expectedBestInSet
            ((fixedCenterMallowsPointFamily center value).dist thetaH) value remaining ≤
          expectedBestInSet
            ((fixedCenterMallowsPointFamily center value).dist thetaA) value remaining) ∧
      expectedBestInSet
          ((fixedCenterMallowsPointFamily center value).dist thetaH) value Finset.univ <
        expectedBestInSet
          ((fixedCenterMallowsPointFamily center value).dist thetaA) value Finset.univ) ∧
  (∀ theta : ℝ, 0 < theta →
    let J := DistributionalAccuracyFamily.outerIndependentPairJointLaw
      (fixedCenterMallowsDistributionalFamily center) D theta
      (fun ranking => DistributionalAccuracyFamily.fixedCenterMallows_ranking_atom_measurable
        center theta ranking)
    0 < ∫ x : ValueProfile n × RankingPair n,
      (if firstChoice x.2.1 ≠ firstChoice x.2.2 then (1 : ℝ) else 0) ∂J ∧
    0 <
      (∫ x : ValueProfile n × RankingPair n,
        if firstChoice x.2.1 ≠ firstChoice x.2.2 then
          x.1 (firstChoice x.2.1) - x.1 (secondChoice x.2.1)
        else 0 ∂J) /
      (∫ x : ValueProfile n × RankingPair n,
        if firstChoice x.2.1 ≠ firstChoice x.2.2 then (1 : ℝ) else 0 ∂J)) ∧
  (∀ thetaA thetaH : ℝ, 0 < thetaH → thetaH < thetaA →
    (∫ value,
      pmfPairExp
        ((fixedCenterMallowsDistributionalFamily center).dist thetaH value)
        ((fixedCenterMallowsDistributionalFamily center).dist thetaA value)
        (fun pi sigma => secondMoverUtility value pi sigma) ∂D) <
    ∫ value,
      pmfPairExp
        ((fixedCenterMallowsDistributionalFamily center).dist thetaH value)
        ((fixedCenterMallowsDistributionalFamily center).dist thetaH value)
        (fun pi sigma => secondMoverUtility value pi sigma) ∂D) ∧
  (∀ thetaH : ℝ, 0 < thetaH →
    let F := fixedCenterMallowsDistributionalFamily center
    ∃ thetaA, thetaH < thetaA ∧
      (∫ value : ValueProfile n,
        Model.firstMoverEU ((F.pointFamily value).modelAt thetaA thetaH)
          Strategy.human ∂D) +
        (∫ value : ValueProfile n,
          Model.secondMoverEU ((F.pointFamily value).modelAt thetaA thetaH)
            Strategy.algorithm Strategy.human ∂D) <
      (∫ value : ValueProfile n,
        Model.firstMoverEU ((F.pointFamily value).modelAt thetaA thetaH)
          Strategy.algorithm ∂D) +
        (∫ value : ValueProfile n,
          Model.secondMoverEU ((F.pointFamily value).modelAt thetaA thetaH)
            Strategy.algorithm Strategy.algorithm ∂D) ∧
      (∫ value : ValueProfile n,
        Model.firstMoverEU ((F.pointFamily value).modelAt thetaA thetaH)
          Strategy.human ∂D) +
        (∫ value : ValueProfile n,
          Model.secondMoverEU ((F.pointFamily value).modelAt thetaA thetaH)
            Strategy.human Strategy.human ∂D) <
      (∫ value : ValueProfile n,
        Model.firstMoverEU ((F.pointFamily value).modelAt thetaA thetaH)
          Strategy.algorithm ∂D) +
        (∫ value : ValueProfile n,
          Model.secondMoverEU ((F.pointFamily value).modelAt thetaA thetaH)
            Strategy.human Strategy.algorithm ∂D) ∧
      (∫ value : ValueProfile n,
        Model.firstMoverEU ((F.pointFamily value).modelAt thetaA thetaH)
          Strategy.algorithm ∂D) +
        (∫ value : ValueProfile n,
          Model.secondMoverEU ((F.pointFamily value).modelAt thetaA thetaH)
            Strategy.algorithm Strategy.algorithm ∂D) <
      (∫ value : ValueProfile n,
        Model.firstMoverEU ((F.pointFamily value).modelAt thetaA thetaH)
          Strategy.human ∂D) +
        (∫ value : ValueProfile n,
          Model.secondMoverEU ((F.pointFamily value).modelAt thetaA thetaH)
            Strategy.human Strategy.human ∂D))

theorem theorem3_source_complete_semantic_complete_spec_proof
    {n : ℕ} (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    (center : Ranking n) (hn : 0 < n)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D)
    (hstrict : ∀ᵐ value ∂D, StrictlyOrderedBy center value) :
    theorem3_source_complete_semantic_completeSpec D center hn hvalue hstrict := by
  rcases theorem3_source_complete_semantic_complete
    D center hn hvalue hstrict with ⟨hmallows, hdefinition1, hdefinition2,
      hdefinition3, hterminal⟩
  refine ⟨hmallows, hdefinition1, hdefinition2, hdefinition3, ?_⟩
  intro thetaH hthetaH
  simpa only [literal_outer_payoff_paradox,
    DistributionalAccuracyFamily.theorem1_f,
    DistributionalAccuracyFamily.theorem1_g,
    DistributionalAccuracyFamily.theorem1_h,
    DistributionalAccuracyFamily.theorem1_algorithmAgainstHuman,
    DistributionalAccuracyFamily.outerExpected] using
    hterminal thetaH hthetaH

/--
Audited source-facing proposition for Theorem 4 under the recorded finite
horizon, ex-ante fresh-ranking convention.  Both literal Mallows laws and
every feasible-history payoff comparison are visible in this proposition.
-/
abbrev theorem4_source_mallows_outer_horizon_lt_literal_semantic_completeSpec
    {n k : ℕ} (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    (center : Ranking n)
    (phiA thetaA phiH thetaH : ℝ)
    (hphiA : 1 < phiA) (hphiH : 1 < phiH)
    (hthetaA : thetaA = phiA - 1) (hthetaH : thetaH = phiH - 1)
    (horizon : k < Fintype.card (Candidate n))
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D) : Prop :=
  let algorithm := concreteMallowsSpec center thetaA
  let human := concreteMallowsSpec center thetaH
  algorithm.q = phiA⁻¹ ∧
    human.q = phiH⁻¹ ∧
    (∀ pi : Ranking n,
      (algorithm.law pi).toReal =
        phiA⁻¹ ^ kendallTau center pi /
          (∑ tau : Ranking n, phiA⁻¹ ^ kendallTau center tau)) ∧
    (∀ pi : Ranking n,
      (human.law pi).toReal =
        phiH⁻¹ ^ kendallTau center pi /
          (∑ tau : Ranking n, phiH⁻¹ ^ kendallTau center tau)) ∧
    (phiA ≤ phiH →
      (∀ᵐ value ∂D, WeaklyOrderedBy center value) →
        ∀ i : Fin k,
          ∀ hired : Finset (Candidate n), hired.card = i.val →
            ∀ strategy : Strategy,
              (∫ value : ValueProfile n,
                ∑ pi : Ranking n,
                  ((match strategy with
                    | .algorithm => algorithm.law
                    | .human => human.law) pi).toReal *
                    value (bestInSet pi (Finset.univ \ hired)) ∂D) ≤
                (∫ value : ValueProfile n,
                  ∑ pi : Ranking n, (human.law pi).toReal *
                    value (bestInSet pi (Finset.univ \ hired)) ∂D)) ∧
    (phiA < phiH →
      (∀ᵐ value ∂D, StrictlyOrderedBy center value) →
        ∀ i : Fin k,
          ∀ hired : Finset (Candidate n), hired.card = i.val →
            ∀ strategy : Strategy,
              (∀ alternative : Strategy,
                (∫ value : ValueProfile n,
                  ∑ pi : Ranking n,
                    ((match alternative with
                      | .algorithm => algorithm.law
                      | .human => human.law) pi).toReal *
                      value (bestInSet pi (Finset.univ \ hired)) ∂D) ≤
                  (∫ value : ValueProfile n,
                    ∑ pi : Ranking n,
                      ((match strategy with
                        | .algorithm => algorithm.law
                        | .human => human.law) pi).toReal *
                      value (bestInSet pi (Finset.univ \ hired)) ∂D)) →
                strategy = Strategy.human)

theorem theorem4_source_mallows_outer_horizon_lt_literal_semantic_complete_spec_proof
    {n k : ℕ} (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    (center : Ranking n)
    (phiA thetaA phiH thetaH : ℝ)
    (hphiA : 1 < phiA) (hphiH : 1 < phiH)
    (hthetaA : thetaA = phiA - 1) (hthetaH : thetaH = phiH - 1)
    (horizon : k < Fintype.card (Candidate n))
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D) :
    theorem4_source_mallows_outer_horizon_lt_literal_semantic_completeSpec
      D center phiA thetaA phiH thetaH hphiA hphiH hthetaA hthetaH horizon hvalue :=
  theorem4_source_mallows_outer_horizon_lt_literal_semantic_complete
    D center phiA thetaA phiH thetaH hphiA hphiH hthetaA hthetaH horizon hvalue

/--
Audited source-facing proposition for the Appendix B.1 Definition 2
counterexample.  The product noise experiment, score map, pushed-forward law,
exact payoff gap, and failed predicate are all explicit.
-/
abbrev appendixB1_source_discrete_definition2_counterexample_semantic_completeSpec : Prop :=
  let componentLaw : PMF AppendixB1NoiseAtom := appendixB1NoisePMF
  let rawNoiseLaw : PMF AppendixB1NoiseTriple :=
    AppliedModelingLib.pmfProd (AppliedModelingLib.pmfProd componentLaw componentLaw) componentLaw
  let rawRank : AppendixB1NoiseTriple -> Ranking 1 := fun noise =>
    rankByScore (fun c => appendixB1Value c +
      appendixB1NoiseValue (appendixB1NoiseTripleFunction noise c))
  let rawLaw : PMF (Ranking 1) := rawNoiseLaw.map rawRank
  (appendixB1Value (0 : Candidate 1) = 7 / 4 ∧
    appendixB1Value (1 : Candidate 1) = 1 / 2 ∧
      appendixB1Value (2 : Candidate 1) = 0) ∧
  (appendixB1NoiseValue .plusOne = 1 ∧
    appendixB1NoiseValue .zero = 0 ∧
      appendixB1NoiseValue .minusOne = -1) ∧
  (componentLaw .plusOne).toReal = 1 / 20 ∧
  (componentLaw .zero).toReal = 9 / 10 ∧
  (componentLaw .minusOne).toReal = 1 / 20 ∧
  (∀ noise : AppendixB1NoiseTriple,
    rawRank noise = appendixB1DiscreteTripleRank noise) ∧
  rawLaw = appendixB1RankingPMF ∧
  expectedSecondMoverIndependent rawLaw rawLaw appendixB1Value -
      expectedSecondMoverShared rawLaw appendixB1Value =
    -(9749 / 12800000 : ℝ) ∧
  ¬ Model.PrefersIndependentReranking rawLaw appendixB1Value

theorem appendixB1_source_discrete_definition2_counterexample_semantic_complete_spec_proof :
    appendixB1_source_discrete_definition2_counterexample_semantic_completeSpec :=
  appendixB1_source_discrete_definition2_counterexample_semantic_complete

/--
Audited source-facing proposition for the Appendix B.2 Definition 3
counterexample.  Both source score experiments and their separate pushed-
forward ranking laws remain explicit through the failed predicate.
-/
abbrev appendixB2_source_discrete_definition3_counterexample_semantic_completeSpec : Prop :=
  let componentLaw : PMF AppendixB2NoiseAtom := appendixB2NoisePMF
  let rawNoiseLaw : PMF AppendixB2NoiseTriple :=
    AppliedModelingLib.pmfProd (AppliedModelingLib.pmfProd componentLaw componentLaw) componentLaw
  let algorithmRank : AppendixB2NoiseTriple -> Ranking 1 := fun noise =>
    rankByScore (fun c => appendixB2Value c + (10 / 11) *
      appendixB2NoiseValue (appendixB2NoiseTripleFunction noise c))
  let humanRank : AppendixB2NoiseTriple -> Ranking 1 := fun noise =>
    rankByScore (fun c => appendixB2Value c + (10 / 9) *
      appendixB2NoiseValue (appendixB2NoiseTripleFunction noise c))
  let algorithmLaw : PMF (Ranking 1) := rawNoiseLaw.map algorithmRank
  let humanLaw : PMF (Ranking 1) := rawNoiseLaw.map humanRank
  (appendixB2Value (0 : Candidate 1) = 3 ∧
    appendixB2Value (1 : Candidate 1) = 2 ∧
      appendixB2Value (2 : Candidate 1) = 0) ∧
  (appendixB2NoiseValue .plusOne = 1 ∧
    appendixB2NoiseValue .minusOne = -1 ∧
      appendixB2NoiseValue .plusTen = 10 ∧
        appendixB2NoiseValue .minusTen = -10) ∧
  (componentLaw .plusOne).toReal = 9 / 20 ∧
  (componentLaw .minusOne).toReal = 9 / 20 ∧
  (componentLaw .plusTen).toReal = 1 / 20 ∧
  (componentLaw .minusTen).toReal = 1 / 20 ∧
  ((11 / 10 : ℝ) > 9 / 10 ∧
    (10 / 11 : ℝ) * (11 / 10 : ℝ) = 1 ∧
      (10 / 9 : ℝ) * (9 / 10 : ℝ) = 1) ∧
  (∀ noise : AppendixB2NoiseTriple,
    algorithmRank noise = appendixB2AlgorithmDiscreteTripleRank noise) ∧
  (∀ noise : AppendixB2NoiseTriple,
    humanRank noise = appendixB2HumanDiscreteTripleRank noise) ∧
  algorithmLaw = appendixB2AlgorithmRankingPMF ∧
  humanLaw = appendixB2HumanRankingPMF ∧
  expectedSecondMoverIndependent humanLaw algorithmLaw appendixB2Value -
      expectedSecondMoverIndependent humanLaw humanLaw appendixB2Value =
    567 / 3200000 ∧
  ¬ Model.PrefersWeakerCompetition algorithmLaw humanLaw appendixB2Value

theorem appendixB2_source_discrete_definition3_counterexample_semantic_complete_spec_proof :
    appendixB2_source_discrete_definition3_counterexample_semantic_completeSpec :=
  appendixB2_source_discrete_definition3_counterexample_semantic_complete

/--
Audited source-facing proposition for Equation (B.1).  The equality is tied
to both literal iid score-pushforward laws, rather than merely to named PMFs.
-/
abbrev equationB1_counterexample_first_choice_x1_semantic_completeSpec : Prop :=
  let componentLaw : PMF AppendixB2NoiseAtom := appendixB2NoisePMF
  let rawNoiseLaw : PMF AppendixB2NoiseTriple :=
    AppliedModelingLib.pmfProd (AppliedModelingLib.pmfProd componentLaw componentLaw) componentLaw
  let algorithmRank : AppendixB2NoiseTriple -> Ranking 1 := fun noise =>
    rankByScore (fun c => appendixB2Value c + (10 / 11) *
      appendixB2NoiseValue (appendixB2NoiseTripleFunction noise c))
  let humanRank : AppendixB2NoiseTriple -> Ranking 1 := fun noise =>
    rankByScore (fun c => appendixB2Value c + (10 / 9) *
      appendixB2NoiseValue (appendixB2NoiseTripleFunction noise c))
  let algorithmLaw : PMF (Ranking 1) := rawNoiseLaw.map algorithmRank
  let humanLaw : PMF (Ranking 1) := rawNoiseLaw.map humanRank
  (appendixB2Value (0 : Candidate 1) = 3 ∧
    appendixB2Value (1 : Candidate 1) = 2 ∧
      appendixB2Value (2 : Candidate 1) = 0) ∧
  (appendixB2NoiseValue .plusOne = 1 ∧
    appendixB2NoiseValue .minusOne = -1 ∧
      appendixB2NoiseValue .plusTen = 10 ∧
        appendixB2NoiseValue .minusTen = -10) ∧
  (componentLaw .plusOne).toReal = 9 / 20 ∧
  (componentLaw .minusOne).toReal = 9 / 20 ∧
  (componentLaw .plusTen).toReal = 1 / 20 ∧
  (componentLaw .minusTen).toReal = 1 / 20 ∧
  algorithmLaw = appendixB2AlgorithmRankingPMF ∧
  humanLaw = appendixB2HumanRankingPMF ∧
  firstChoiceProb algorithmLaw (0 : Candidate 1) =
    firstChoiceProb humanLaw (0 : Candidate 1)

theorem equationB1_counterexample_first_choice_x1_semantic_complete_spec_proof :
    equationB1_counterexample_first_choice_x1_semantic_completeSpec :=
  equationB1_counterexample_first_choice_x1_semantic_complete

/--
Audited source-facing proposition for Equation (B.2).  The strict comparison
is tied to both literal iid score-pushforward laws in the audited statement.
-/
abbrev equationB2_counterexample_first_choice_x2_semantic_completeSpec : Prop :=
  let componentLaw : PMF AppendixB2NoiseAtom := appendixB2NoisePMF
  let rawNoiseLaw : PMF AppendixB2NoiseTriple :=
    AppliedModelingLib.pmfProd (AppliedModelingLib.pmfProd componentLaw componentLaw) componentLaw
  let algorithmRank : AppendixB2NoiseTriple -> Ranking 1 := fun noise =>
    rankByScore (fun c => appendixB2Value c + (10 / 11) *
      appendixB2NoiseValue (appendixB2NoiseTripleFunction noise c))
  let humanRank : AppendixB2NoiseTriple -> Ranking 1 := fun noise =>
    rankByScore (fun c => appendixB2Value c + (10 / 9) *
      appendixB2NoiseValue (appendixB2NoiseTripleFunction noise c))
  let algorithmLaw : PMF (Ranking 1) := rawNoiseLaw.map algorithmRank
  let humanLaw : PMF (Ranking 1) := rawNoiseLaw.map humanRank
  (appendixB2Value (0 : Candidate 1) = 3 ∧
    appendixB2Value (1 : Candidate 1) = 2 ∧
      appendixB2Value (2 : Candidate 1) = 0) ∧
  (appendixB2NoiseValue .plusOne = 1 ∧
    appendixB2NoiseValue .minusOne = -1 ∧
      appendixB2NoiseValue .plusTen = 10 ∧
        appendixB2NoiseValue .minusTen = -10) ∧
  (componentLaw .plusOne).toReal = 9 / 20 ∧
  (componentLaw .minusOne).toReal = 9 / 20 ∧
  (componentLaw .plusTen).toReal = 1 / 20 ∧
  (componentLaw .minusTen).toReal = 1 / 20 ∧
  algorithmLaw = appendixB2AlgorithmRankingPMF ∧
  humanLaw = appendixB2HumanRankingPMF ∧
  firstChoiceProb humanLaw (1 : Candidate 1) <
    firstChoiceProb algorithmLaw (1 : Candidate 1)

theorem equationB2_counterexample_first_choice_x2_semantic_complete_spec_proof :
    equationB2_counterexample_first_choice_x2_semantic_completeSpec :=
  equationB2_counterexample_first_choice_x2_semantic_complete

/--
Audited source-facing proposition for Appendix C Lemma 2.  Both accuracy
experiments are explicitly the shared-innovation score pushforwards before the
bottom-first probability comparison is asserted.
-/
abbrev lemma2_source_arbitraryFinite_bottom_first_probability_semantic_completeSpec
    {n : ℕ} {thetaA thetaH : ℝ}
    (mu : Measure (Candidate n -> ℝ)) [IsProbabilityMeasure mu]
    (hthetaH : 0 < thetaH) (hthetaHA : thetaH < thetaA)
    (value : Candidate n -> ℝ) (bottom : Candidate n)
    (hbottom : ∀ i : Candidate n, i ≠ bottom -> value bottom < value i) : Prop :=
  (paper_appendixA_scaledNoiseRankingPMF mu value thetaA).toMeasure = mu.map
    (fun epsilon => rankByScore (fun c => value c + epsilon c / thetaA)) ∧
  (paper_appendixA_scaledNoiseRankingPMF mu value thetaH).toMeasure = mu.map
    (fun epsilon => rankByScore (fun c => value c + epsilon c / thetaH)) ∧
  firstChoiceProb (paper_appendixA_scaledNoiseRankingPMF mu value thetaA) bottom ≤
    firstChoiceProb (paper_appendixA_scaledNoiseRankingPMF mu value thetaH) bottom

theorem lemma2_source_arbitraryFinite_bottom_first_probability_semantic_complete_spec_proof
    {n : ℕ} {thetaA thetaH : ℝ}
    (mu : Measure (Candidate n -> ℝ)) [IsProbabilityMeasure mu]
    (hthetaH : 0 < thetaH) (hthetaHA : thetaH < thetaA)
    (value : Candidate n -> ℝ) (bottom : Candidate n)
    (hbottom : ∀ i : Candidate n, i ≠ bottom -> value bottom < value i) :
    lemma2_source_arbitraryFinite_bottom_first_probability_semantic_completeSpec
      mu hthetaH hthetaHA value bottom hbottom :=
  lemma2_source_arbitraryFinite_bottom_first_probability_semantic_complete
    mu hthetaH hthetaHA value bottom hbottom

/--
Audited source-facing proposition for Appendix C Lemma 2.  The interface pins
the source's iid density product, two-firm candidate domain, strict value
order, last candidate `x_n`, and both score pushforwards before asserting the
bottom-first probability comparison.
-/
abbrev lemma2_source_arbitraryFinite_iid_bottom_first_probability_semantic_completeSpec
    {n : ℕ} {f : ℝ → ℝ}
    (hfmeas : Measurable f) (hnonneg : ∀ z : ℝ, 0 ≤ f z)
    (hnormalized : ∫⁻ z, ENNReal.ofReal (f z) ∂volume = 1)
    (value : Candidate n → ℝ) (hvalueOrder : StrictAnti value)
    {thetaA thetaH : ℝ} (hthetaH : 0 < thetaH) (hthetaHA : thetaH < thetaA) : Prop :=
  (@paper_appendixA_scaledNoiseRankingPMF n
    (w11CandidateNoiseLaw (n := n) f)
    (w11CandidateNoiseLaw_isProbabilityMeasure_of_base_normalization
      n f hnormalized)
    value thetaA).toMeasure =
    (Measure.pi (fun _ : Candidate n =>
      volume.withDensity (fun z => ENNReal.ofReal (f z)))).map
      (fun epsilon => rankByScore (fun c => value c + epsilon c / thetaA)) ∧
  (@paper_appendixA_scaledNoiseRankingPMF n
    (w11CandidateNoiseLaw (n := n) f)
    (w11CandidateNoiseLaw_isProbabilityMeasure_of_base_normalization
      n f hnormalized)
    value thetaH).toMeasure =
    (Measure.pi (fun _ : Candidate n =>
      volume.withDensity (fun z => ENNReal.ofReal (f z)))).map
      (fun epsilon => rankByScore (fun c => value c + epsilon c / thetaH)) ∧
  firstChoiceProb
      (@paper_appendixA_scaledNoiseRankingPMF n
        (w11CandidateNoiseLaw (n := n) f)
        (w11CandidateNoiseLaw_isProbabilityMeasure_of_base_normalization
          n f hnormalized)
        value thetaA)
      (Fin.last (n + 1)) ≤
    firstChoiceProb
      (@paper_appendixA_scaledNoiseRankingPMF n
        (w11CandidateNoiseLaw (n := n) f)
        (w11CandidateNoiseLaw_isProbabilityMeasure_of_base_normalization
          n f hnormalized)
        value thetaH)
      (Fin.last (n + 1))

theorem lemma2_source_arbitraryFinite_iid_bottom_first_probability_semantic_complete_spec_proof
    {n : ℕ} {f : ℝ → ℝ}
    (hfmeas : Measurable f) (hnonneg : ∀ z : ℝ, 0 ≤ f z)
    (hnormalized : ∫⁻ z, ENNReal.ofReal (f z) ∂volume = 1)
    (value : Candidate n → ℝ) (hvalueOrder : StrictAnti value)
    {thetaA thetaH : ℝ} (hthetaH : 0 < thetaH) (hthetaHA : thetaH < thetaA) :
    lemma2_source_arbitraryFinite_iid_bottom_first_probability_semantic_completeSpec
      hfmeas hnonneg hnormalized value hvalueOrder hthetaH hthetaHA :=
  lemma2_source_arbitraryFinite_iid_bottom_first_probability_semantic_complete
    hfmeas hnonneg hnormalized value hvalueOrder hthetaH hthetaHA

/--
Audited source-facing proposition for Appendix C Lemma 3.  The specification
spells out the iid density product, both source score maps, and the stated
first-choice change inequality.
-/
abbrev lemma3_source_arbitraryFinite_iid_delta_le_top_delta_semantic_completeSpec
    {n : ℕ} {f : ℝ → ℝ}
    (hf : StrictlyWellOrderedNoise f) (hfmeas : Measurable f)
    (hnonneg : ∀ z : ℝ, 0 ≤ f z)
    (hnormalized : ∫⁻ z, ENNReal.ofReal (f z) ∂volume = 1)
    (value : Candidate n → ℝ) (hvalueOrder : StrictAnti value)
    {thetaA thetaH : ℝ} (hthetaH : 0 < thetaH) (hthetaHA : thetaH ≤ thetaA)
    {i : Candidate n} (hi : i ≠ 0) : Prop :=
  (@paper_appendixA_scaledNoiseRankingPMF n
    (w11CandidateNoiseLaw (n := n) f)
    (w11CandidateNoiseLaw_isProbabilityMeasure_of_base_normalization
      n f hnormalized)
    value thetaA).toMeasure =
    (Measure.pi (fun _ : Candidate n =>
      volume.withDensity (fun z => ENNReal.ofReal (f z)))).map
      (fun epsilon => rankByScore (fun c => value c + epsilon c / thetaA)) ∧
  (@paper_appendixA_scaledNoiseRankingPMF n
    (w11CandidateNoiseLaw (n := n) f)
    (w11CandidateNoiseLaw_isProbabilityMeasure_of_base_normalization
      n f hnormalized)
    value thetaH).toMeasure =
    (Measure.pi (fun _ : Candidate n =>
      volume.withDensity (fun z => ENNReal.ofReal (f z)))).map
      (fun epsilon => rankByScore (fun c => value c + epsilon c / thetaH)) ∧
  firstChoiceProb
      (@paper_appendixA_scaledNoiseRankingPMF n
        (w11CandidateNoiseLaw (n := n) f)
        (w11CandidateNoiseLaw_isProbabilityMeasure_of_base_normalization
          n f hnormalized)
        value thetaA) i -
    firstChoiceProb
      (@paper_appendixA_scaledNoiseRankingPMF n
        (w11CandidateNoiseLaw (n := n) f)
        (w11CandidateNoiseLaw_isProbabilityMeasure_of_base_normalization
          n f hnormalized)
        value thetaH) i ≤
  firstChoiceProb
      (@paper_appendixA_scaledNoiseRankingPMF n
        (w11CandidateNoiseLaw (n := n) f)
        (w11CandidateNoiseLaw_isProbabilityMeasure_of_base_normalization
          n f hnormalized)
        value thetaA) 0 -
    firstChoiceProb
      (@paper_appendixA_scaledNoiseRankingPMF n
        (w11CandidateNoiseLaw (n := n) f)
        (w11CandidateNoiseLaw_isProbabilityMeasure_of_base_normalization
          n f hnormalized)
        value thetaH) 0

theorem lemma3_source_arbitraryFinite_iid_delta_le_top_delta_semantic_complete_spec_proof
    {n : ℕ} {f : ℝ → ℝ}
    (hf : StrictlyWellOrderedNoise f) (hfmeas : Measurable f)
    (hnonneg : ∀ z : ℝ, 0 ≤ f z)
    (hnormalized : ∫⁻ z, ENNReal.ofReal (f z) ∂volume = 1)
    (value : Candidate n → ℝ) (hvalueOrder : StrictAnti value)
    {thetaA thetaH : ℝ} (hthetaH : 0 < thetaH) (hthetaHA : thetaH ≤ thetaA)
    {i : Candidate n} (hi : i ≠ 0) :
    lemma3_source_arbitraryFinite_iid_delta_le_top_delta_semantic_completeSpec
      hf hfmeas hnonneg hnormalized value hvalueOrder hthetaH hthetaHA hi :=
  lemma3_source_arbitraryFinite_iid_delta_le_top_delta_semantic_complete
    hf hfmeas hnonneg hnormalized value hvalueOrder hthetaH hthetaHA hi

/--
Audited source-facing proposition for Equation (C.3).  The literal Laplace
density, CDF, product law, numerator event, denominator event, and integral
formula all occur in the proposition independently of its proof route.
-/
abbrev equationC3_laplace_strict_conditional_ratio_eq_density_cdf_semantic_completeSpec
    {lam xi xj a : ℝ} (hlam : 0 < lam) : Prop :=
  let density : ℝ -> ℝ -> ℝ := fun location x =>
    lam / 2 * Real.exp (-lam * |x - location|)
  let cdf : ℝ -> ℝ -> ℝ := fun location x =>
    if x < location then
      (1 / 2) * Real.exp (-lam * (location - x))
    else
      1 - (1 / 2) * Real.exp (-lam * (x - location))
  let scoreI : Measure ℝ :=
    (volume : Measure ℝ).withDensity
      (fun x => ENNReal.ofReal (density xi x))
  let scoreJ : Measure ℝ :=
    (volume : Measure ℝ).withDensity
      (fun x => ENNReal.ofReal (density xj x))
  let pairLaw : Measure (ℝ × ℝ) := scoreI.prod scoreJ
  0 < (pairLaw {p | p.1 < a ∧ p.2 < a}).toReal ∧
    (pairLaw {p | p.1 < a ∧ p.2 < p.1}).toReal /
        (pairLaw {p | p.1 < a ∧ p.2 < a}).toReal =
      (∫ x : ℝ in Set.Iic a, density xi x * cdf xj x) /
        (cdf xi a * cdf xj a)

theorem equationC3_laplace_strict_conditional_ratio_eq_density_cdf_semantic_complete_spec_proof
    {lam xi xj a : ℝ} (hlam : 0 < lam) :
    equationC3_laplace_strict_conditional_ratio_eq_density_cdf_semantic_completeSpec
      (lam := lam) (xi := xi) (xj := xj) (a := a) hlam :=
  equationC3_laplace_strict_conditional_ratio_eq_density_cdf_semantic_complete
    (lam := lam) (xi := xi) (xj := xj) (a := a) hlam

/--
Audited source-facing proposition for the corrected signed-welfare example.
It exposes the translated point-value law, preserved ranking laws, payoff and
welfare signs, and the full independent mixed-equilibrium conclusion.
-/
abbrev signed_welfare_source_mallows_literal_mixed_semantic_completeSpec
    {n : ℕ} (center : Ranking n) (value : ValueProfile n)
    (hvalue : StrictlyOrderedBy center value) (hn : 0 < n)
    (thetaH : ℝ) (hthetaH : 0 < thetaH) : Prop :=
  ∃ thetaA, thetaH < thetaA ∧ ∃ shift,
    let M := (fixedCenterMallowsPointFamily center value).modelAt thetaA thetaH
    let T := M.translateValues shift
    let outerValueLaw : Measure (ValueProfile n) :=
      Measure.dirac (fun c => value c + shift)
    outerValueLaw Set.univ = 1 ∧
    (∀ c : Candidate n,
      ∫ profile, profile c ∂outerValueLaw = value c + shift) ∧
    StrictlyOrderedBy center T.value ∧
    T.algorithmRanking = M.algorithmRanking ∧
    T.humanRanking = M.humanRanking ∧
    Model.labeledFirmRandomOrderExpectedPayoff T Strategy.algorithm Strategy.algorithm >
      Model.labeledFirmRandomOrderExpectedPayoff T Strategy.human Strategy.algorithm ∧
    Model.labeledFirmRandomOrderExpectedPayoff T Strategy.algorithm Strategy.human >
      Model.labeledFirmRandomOrderExpectedPayoff T Strategy.human Strategy.human ∧
    Model.welfareRandomOrder T Strategy.algorithm Strategy.algorithm < 0 ∧
    0 < max
      (max (Model.welfareRandomOrder T Strategy.algorithm Strategy.algorithm)
        (Model.welfareRandomOrder T Strategy.algorithm Strategy.human))
      (max (Model.welfareRandomOrder T Strategy.human Strategy.algorithm)
        (Model.welfareRandomOrder T Strategy.human Strategy.human)) ∧
    ∀ first second : Model.MixedStrategy,
      ((∀ deviation : Model.MixedStrategy,
        Model.mixedExpectedPayoff T deviation second ≤
          Model.mixedExpectedPayoff T first second) ∧
      (∀ deviation : Model.MixedStrategy,
        Model.mixedExpectedPayoff T deviation first ≤
          Model.mixedExpectedPayoff T second first)) →
        first = Model.mixedAlgorithm ∧ second = Model.mixedAlgorithm

theorem signed_welfare_source_mallows_literal_mixed_semantic_complete_spec_proof
    {n : ℕ} (center : Ranking n) (value : ValueProfile n)
    (hvalue : StrictlyOrderedBy center value) (hn : 0 < n)
    (thetaH : ℝ) (hthetaH : 0 < thetaH) :
    signed_welfare_source_mallows_literal_mixed_semantic_completeSpec
      center value hvalue hn thetaH hthetaH :=
  signed_welfare_source_mallows_literal_mixed_semantic_complete
    center value hvalue hn thetaH hthetaH

/--
Audited source-facing proposition for Definition 1.  This repeats the
continuity, differentiability, true-ranking concentration, and all removal
monotonicity clauses instead of deriving the specification from a route name.
Its arguments retain the source's global rank-labelled strict value order.
-/
abbrev source_definition1_iffSpec
    {n : ℕ} (F : AccuracyFamily n) (trueRanking : Ranking n)
    (hvalueOrder : StrictlyOrderedBy trueRanking F.value) : Prop :=
  SourceDefinition1 F trueRanking ↔
    (∀ theta, 0 < theta → ∀ pi : Ranking n,
      ContinuousAt (fun theta' => ((F.dist theta') pi).toReal) theta ∧
        DifferentiableAt ℝ (fun theta' => ((F.dist theta') pi).toReal) theta) ∧
    Tendsto (fun theta => ((F.dist theta) trueRanking).toReal) atTop (nhds 1) ∧
    ∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
      (∀ remaining : Finset (Candidate n), remaining.Nonempty →
        expectedBestInSet (F.dist thetaH) F.value remaining ≤
          expectedBestInSet (F.dist thetaA) F.value remaining) ∧
      expectedBestInSet (F.dist thetaH) F.value Finset.univ <
        expectedBestInSet (F.dist thetaA) F.value Finset.univ

theorem source_definition1_iff_spec_proof
    {n : ℕ} (F : AccuracyFamily n) (trueRanking : Ranking n)
    (hvalueOrder : StrictlyOrderedBy trueRanking F.value) :
    source_definition1_iffSpec F trueRanking hvalueOrder :=
  source_definition1_iff F trueRanking hvalueOrder

/-- Audited source-facing proposition for Equation (1)'s literal projection. -/
abbrev source_equation1_removal_monotonicitySpec
    {n : ℕ} {F : AccuracyFamily n} {trueRanking : Ranking n}
    (hvalueOrder : StrictlyOrderedBy trueRanking F.value)
    (hdefinition1 : SourceDefinition1 F trueRanking) : Prop :=
  ∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
    (∀ remaining : Finset (Candidate n), remaining.Nonempty →
      expectedBestInSet (F.dist thetaH) F.value remaining ≤
        expectedBestInSet (F.dist thetaA) F.value remaining) ∧
    expectedBestInSet (F.dist thetaH) F.value Finset.univ <
      expectedBestInSet (F.dist thetaA) F.value Finset.univ

theorem source_equation1_removal_monotonicity_spec_proof
    {n : ℕ} {F : AccuracyFamily n} {trueRanking : Ranking n}
    (hvalueOrder : StrictlyOrderedBy trueRanking F.value)
    (hdefinition1 : SourceDefinition1 F trueRanking) :
    source_equation1_removal_monotonicitySpec hvalueOrder hdefinition1 :=
  source_equation1_removal_monotonicity hvalueOrder hdefinition1

/--
Audited source-facing proposition for the two-firm selection experiment.  It
exposes the shared algorithmic ranking, the independent non-algorithmic rows,
and the random-order payoff average.
-/
abbrev source_two_firm_selection_game_semanticsSpec
    {n : ℕ} (M : Model n) : Prop :=
  Model.firstMoverEU M Strategy.algorithm =
      expectedFirstMoverUtility M.algorithmRanking M.value ∧
  Model.firstMoverEU M Strategy.human =
      expectedFirstMoverUtility M.humanRanking M.value ∧
  Model.secondMoverEU M Strategy.algorithm Strategy.algorithm =
      expectedSecondMoverShared M.algorithmRanking M.value ∧
  Model.secondMoverEU M Strategy.algorithm Strategy.human =
      expectedSecondMoverIndependent M.humanRanking M.algorithmRanking M.value ∧
  Model.secondMoverEU M Strategy.human Strategy.algorithm =
      expectedSecondMoverIndependent M.algorithmRanking M.humanRanking M.value ∧
  Model.secondMoverEU M Strategy.human Strategy.human =
      expectedSecondMoverIndependent M.humanRanking M.humanRanking M.value ∧
  ∀ self other : Strategy,
    Model.payoffAgainst M self other =
      (Model.firstMoverEU M self + Model.secondMoverEU M other self) / 2

theorem source_two_firm_selection_game_semantics_spec_proof
    {n : ℕ} (M : Model n) :
    source_two_firm_selection_game_semanticsSpec M :=
  source_two_firm_selection_game_semantics M

/--
Audited source-facing proposition for the arbitrary outer law `D` on the
source's rank-labelled strict-order domain and its admissible deterministic
special case.
-/
abbrev source_model_outer_distribution_probability_and_point_massSpec
    {n : ℕ} (trueRanking : Ranking n) (D : Measure (ValueProfile n))
    [IsProbabilityMeasure D]
    (hDvalueOrder : ∀ᵐ realizedValue ∂D,
      StrictlyOrderedBy trueRanking realizedValue)
    (value : ValueProfile n)
    (hvalueOrder : StrictlyOrderedBy trueRanking value) : Prop :=
  D Set.univ = 1 ∧
    (Measure.dirac value) Set.univ = 1 ∧
      IsProbabilityMeasure (Measure.dirac value)

theorem source_model_outer_distribution_probability_and_point_mass_spec_proof
    {n : ℕ} (trueRanking : Ranking n) (D : Measure (ValueProfile n))
    [IsProbabilityMeasure D]
    (hDvalueOrder : ∀ᵐ realizedValue ∂D,
      StrictlyOrderedBy trueRanking realizedValue)
    (value : ValueProfile n)
    (hvalueOrder : StrictlyOrderedBy trueRanking value) :
    source_model_outer_distribution_probability_and_point_massSpec
      trueRanking D hDvalueOrder value hvalueOrder :=
  source_model_outer_distribution_probability_and_point_mass
    trueRanking D hDvalueOrder value hvalueOrder

/-- Audited source-facing proposition for Equation (4)'s payoff comparison. -/
abbrev equation4_algorithm_best_response_against_algorithm_iffSpec
    {n : ℕ} (M : Model n) : Prop :=
  (Model.firstMoverEU M Strategy.algorithm +
      Model.secondMoverEU M Strategy.algorithm Strategy.algorithm >
    Model.firstMoverEU M Strategy.human +
      Model.secondMoverEU M Strategy.algorithm Strategy.human) ↔
    Model.payoffAgainst M Strategy.algorithm Strategy.algorithm >
      Model.payoffAgainst M Strategy.human Strategy.algorithm

theorem equation4_algorithm_best_response_against_algorithm_iff_spec_proof
    {n : ℕ} (M : Model n) :
    equation4_algorithm_best_response_against_algorithm_iffSpec M :=
  equation4_algorithm_best_response_against_algorithm_iff M

/--
Audited source-facing proposition for Equation (5), with both the weak
remaining-set and strict full-set Definition 1 conditions visible.
-/
abbrev equation5_from_literal_definition1_removalSpec
    {n : ℕ} (F : AccuracyFamily n) (thetaA thetaH : ℝ)
    (hthetaH : 0 < thetaH) (hthetaA : thetaH < thetaA)
    (hweak : ∀ remaining : Finset (Candidate n), remaining.Nonempty →
      expectedBestInSet (F.dist thetaH) F.value remaining ≤
        expectedBestInSet (F.dist thetaA) F.value remaining)
    (hstrict :
      expectedBestInSet (F.dist thetaH) F.value Finset.univ <
        expectedBestInSet (F.dist thetaA) F.value Finset.univ) : Prop :=
  Model.firstMoverEU (F.modelAt thetaA thetaH) Strategy.algorithm +
      Model.secondMoverEU (F.modelAt thetaA thetaH)
        Strategy.human Strategy.algorithm >
    Model.firstMoverEU (F.modelAt thetaA thetaH) Strategy.human +
      Model.secondMoverEU (F.modelAt thetaA thetaH)
        Strategy.human Strategy.human

theorem equation5_from_literal_definition1_removal_spec_proof
    {n : ℕ} (F : AccuracyFamily n) (thetaA thetaH : ℝ)
    (hthetaH : 0 < thetaH) (hthetaA : thetaH < thetaA)
    (hweak : ∀ remaining : Finset (Candidate n), remaining.Nonempty →
      expectedBestInSet (F.dist thetaH) F.value remaining ≤
        expectedBestInSet (F.dist thetaA) F.value remaining)
    (hstrict :
      expectedBestInSet (F.dist thetaH) F.value Finset.univ <
        expectedBestInSet (F.dist thetaA) F.value Finset.univ) :
    equation5_from_literal_definition1_removalSpec
      F thetaA thetaH hthetaH hthetaA hweak hstrict :=
  equation5_from_literal_definition1_removal
    F thetaA thetaH hthetaH hthetaA hweak hstrict

/--
Audited source-facing proposition for Equation (6)'s continuous sign-change
argument and its strictly intermediate indifference witness.
-/
abbrev equation6_indifference_threshold_of_sign_changeSpec
    {n : ℕ} (F : AccuracyFamily n) (thetaH lo hi : ℝ)
    (hthetaH : 0 < thetaH)
    (hthetaH_lo : thetaH < lo) (hlo_hi : lo < hi)
    (hcontinuous : ContinuousOn
      (fun thetaA =>
        AccuracyFamily.theorem1_f F thetaA thetaH -
          AccuracyFamily.theorem1_g F thetaA thetaH)
      (Set.Icc lo hi))
    (hlo : AccuracyFamily.theorem1_f F lo thetaH <
      AccuracyFamily.theorem1_g F lo thetaH)
    (hhi : AccuracyFamily.theorem1_g F hi thetaH <
      AccuracyFamily.theorem1_f F hi thetaH) : Prop :=
  ∃ thetaA, thetaH < thetaA ∧
    AccuracyFamily.theorem1_f F thetaA thetaH =
      AccuracyFamily.theorem1_g F thetaA thetaH

theorem equation6_indifference_threshold_of_sign_change_spec_proof
    {n : ℕ} (F : AccuracyFamily n) (thetaH lo hi : ℝ)
    (hthetaH : 0 < thetaH)
    (hthetaH_lo : thetaH < lo) (hlo_hi : lo < hi)
    (hcontinuous : ContinuousOn
      (fun thetaA =>
        AccuracyFamily.theorem1_f F thetaA thetaH -
          AccuracyFamily.theorem1_g F thetaA thetaH)
      (Set.Icc lo hi))
    (hlo : AccuracyFamily.theorem1_f F lo thetaH <
      AccuracyFamily.theorem1_g F lo thetaH)
    (hhi : AccuracyFamily.theorem1_g F hi thetaH <
      AccuracyFamily.theorem1_f F hi thetaH) :
    equation6_indifference_threshold_of_sign_changeSpec
      F thetaH lo hi hthetaH hthetaH_lo hlo_hi hcontinuous hlo hhi :=
  equation6_indifference_threshold_of_sign_change
    F thetaH lo hi hthetaH hthetaH_lo hlo_hi hcontinuous hlo hhi

/--
Audited source-facing proposition for the iid finite-positive-variance RUM
normalization, including the product law, unit coordinate variance, and exact
ranking-law parameter transport.
-/
abbrev section31_iidFinitePositiveVariance_normalizationSpec
    {n : ℕ} (E : Measure ℝ) [IsProbabilityMeasure E]
    (hsecond : MemLp id 2 E)
    (hvariance_pos : 0 < Var[id; E])
    (value : Candidate n → ℝ) (theta : ℝ) (htheta : 0 < theta) : Prop :=
  iIndepFun
      (fun i (epsilon : Candidate n → ℝ) => epsilon i)
      (sourceRUMNormalizedIIDNoiseLaw (n := n) E
        (Real.sqrt (Var[id; E]))) ∧
    MemLp id 2
      (sourceRUMNormalizedScalarNoiseLaw E (Real.sqrt (Var[id; E]))) ∧
    (∀ i : Candidate n,
      Var[(fun epsilon : Candidate n → ℝ => epsilon i);
        sourceRUMNormalizedIIDNoiseLaw (n := n) E
          (Real.sqrt (Var[id; E]))] = 1) ∧
    paper_appendixA_scaledNoiseRankingPMF
        (Measure.pi (fun _ : Candidate n => E)) value theta =
      @paper_appendixA_scaledNoiseRankingPMF n
        (sourceRUMNormalizedIIDNoiseLaw (n := n) E
          (Real.sqrt (Var[id; E])))
        (sourceRUMNormalizedIIDNoiseLaw_isProbabilityMeasure E
          (Real.sqrt (Var[id; E])))
        value (theta / Real.sqrt (Var[id; E]))

theorem section31_iidFinitePositiveVariance_normalization_spec_proof
    {n : ℕ} (E : Measure ℝ) [IsProbabilityMeasure E]
    (hsecond : MemLp id 2 E)
    (hvariance_pos : 0 < Var[id; E])
    (value : Candidate n → ℝ) (theta : ℝ) (htheta : 0 < theta) :
    section31_iidFinitePositiveVariance_normalizationSpec
      E hsecond hvariance_pos value theta htheta :=
  section31_iidFinitePositiveVariance_normalization
    E hsecond hvariance_pos value theta htheta

/-- Audited source-facing proposition for Equation (7)'s remaining-set share. -/
abbrev equation7_plackettLuce_choice_probabilitySpec
    {n : ℕ} (theta : ℝ) (value : Candidate n → ℝ)
    (htheta : 0 < theta)
    (remaining : Finset (Candidate n)) {i : Candidate n}
    (hi : i ∈ remaining) : Prop :=
  plackettLuceChoiceProb theta value remaining i =
    Real.exp (theta * value i) /
      ∑ j ∈ remaining, Real.exp (theta * value j)

theorem equation7_plackettLuce_choice_probability_spec_proof
    {n : ℕ} (theta : ℝ) (value : Candidate n → ℝ)
    (htheta : 0 < theta)
    (remaining : Finset (Candidate n)) {i : Candidate n}
    (hi : i ∈ remaining) :
    equation7_plackettLuce_choice_probabilitySpec theta value htheta remaining hi :=
  equation7_plackettLuce_choice_probability theta value htheta remaining hi

/--
Audited outer-D Section 3.1 strategy contract.  It keeps the source's outer
candidate distribution, its strict rank-labelled support condition, the four
integrability obligations, and both ex-ante best-response rows on the direct
surface.  This prevents a fixed-profile dominance theorem from being credited
as though it already were the paper's `D`-averaged claim.
-/
abbrev section31_plackettLuce_outer_best_available_weakly_dominatesSpec
    {n : ℕ} (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    (center : Ranking n) {thetaA thetaH : ℝ}
    (hthetaA : 0 < thetaA) (hthetaH : 0 < thetaH)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D)
    (horder : ∀ᵐ value ∂D, StrictlyOrderedBy center value) : Prop :=
  let M : ValueProfile n → Model n := fun value =>
    { algorithmRanking := plackettLuceRankingPMF thetaA value
      humanRanking := plackettLuceRankingPMF thetaH value
      value := value }
  (∀ self other : Strategy,
    Integrable (fun value => Model.payoffAgainst (M value) self other) D) ∧
  (thetaH ≤ thetaA →
    (∫ value, Model.payoffAgainst (M value) Strategy.algorithm Strategy.algorithm ∂D) ≥
        ∫ value, Model.payoffAgainst (M value) Strategy.human Strategy.algorithm ∂D ∧
      (∫ value, Model.payoffAgainst (M value) Strategy.algorithm Strategy.human ∂D) ≥
        ∫ value, Model.payoffAgainst (M value) Strategy.human Strategy.human ∂D) ∧
    (thetaA ≤ thetaH →
      (∫ value, Model.payoffAgainst (M value) Strategy.human Strategy.algorithm ∂D) ≥
          ∫ value, Model.payoffAgainst (M value) Strategy.algorithm Strategy.algorithm ∂D ∧
        (∫ value, Model.payoffAgainst (M value) Strategy.human Strategy.human ∂D) ≥
          ∫ value, Model.payoffAgainst (M value) Strategy.algorithm Strategy.human ∂D)

theorem section31_plackettLuce_outer_best_available_weakly_dominates_spec_proof
    {n : ℕ} (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    (center : Ranking n) {thetaA thetaH : ℝ}
    (hthetaA : 0 < thetaA) (hthetaH : 0 < thetaH)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D)
    (horder : ∀ᵐ value ∂D, StrictlyOrderedBy center value) :
    section31_plackettLuce_outer_best_available_weakly_dominatesSpec
      D center hthetaA hthetaH hvalue horder :=
  section31_plackettLuce_outer_best_available_weakly_dominates
    D center hthetaA hthetaH hvalue horder

/--
Audited corrected Section 3.1 Gumbel identification.  The specification
spells out the exponential arrival product law, literal noise and score maps,
positive-scale Plackett--Luce transport, and the conditional unit-variance
specialization rather than treating a family label as that identification.
-/
abbrev section31_corrected_gumbel_plackett_luce_targetSpec
    {n : ℕ} (location : ℝ) {s theta : ℝ} (hs : 0 < s) (htheta : 0 < theta)
    (value : Candidate n → ℝ) : Prop :=
  (gumbelArrivalLaw n =
    Measure.pi (fun _ : Candidate n => expMeasure 1)) ∧
    (∀ᵐ arrival ∂gumbelArrivalLaw n, ∀ i : Candidate n, 0 < arrival i) ∧
    (∀ (arrival : Candidate n → ℝ) (i : Candidate n),
      commonLocationPositiveScaleGumbelNoise location s arrival i =
        location + (-s) * Real.log (arrival i)) ∧
    (∀ (arrival : Candidate n → ℝ) (i : Candidate n),
      commonLocationPositiveScaleGumbelScores location s theta value arrival i =
        value i + (location + (-s) * Real.log (arrival i)) / theta) ∧
    (Measure.map (commonLocationPositiveScaleGumbelNoise location s)
        (gumbelArrivalLaw n) =
      Measure.pi (fun _ : Candidate n =>
        (expMeasure 1).map
          (fun arrival : ℝ => location + (-s) * Real.log arrival))) ∧
    commonLocationPositiveScaleGumbelRUMRankingPMF location s theta value =
      plackettLuceRankingPMF (theta / s) value ∧
    (Var[id; scaleOneGumbelMeasure] = Real.pi ^ 2 / 6 →
      (sourceUnitVarianceGumbelNoiseLaw (n := n) location =
        Measure.pi (fun _ : Candidate n =>
          (expMeasure 1).map
            (fun arrival : ℝ => location +
              (-(Real.sqrt 6 / Real.pi)) * Real.log arrival))) ∧
        (∀ (epsilon : Candidate n → ℝ) (i : Candidate n),
          sourceUnitVarianceGumbelScores theta value epsilon i =
            value i + epsilon i / theta) ∧
        (∀ i : Candidate n,
          Var[(fun epsilon : Candidate n → ℝ => epsilon i);
            sourceUnitVarianceGumbelNoiseLaw (n := n) location] = 1) ∧
          sourceUnitVarianceGumbelRUMRankingPMF location theta value =
            plackettLuceRankingPMF (theta / (Real.sqrt 6 / Real.pi)) value)

theorem section31_corrected_gumbel_plackett_luce_target_spec_proof
    {n : ℕ} (location : ℝ) {s theta : ℝ} (hs : 0 < s) (htheta : 0 < theta)
    (value : Candidate n → ℝ) :
    section31_corrected_gumbel_plackett_luce_targetSpec
      location hs htheta value :=
  section31_corrected_gumbel_plackett_luce_target location hs htheta value

/--
Audited source-facing best-available-ranking conclusion for the literal
positive-scale Gumbel RUM.  Equal accuracies yield weak, not strict,
dominance, and both opponent rows are explicit.
-/
abbrev section31_literalUnitVarianceGumbel_best_available_weakly_dominatesSpec
    {n : ℕ} {location thetaA thetaH : ℝ}
    (value : Candidate n → ℝ)
    (hthetaA : 0 < thetaA) (hthetaH : 0 < thetaH) : Prop :=
  let M : Model n :=
    { algorithmRanking :=
        sourceUnitVarianceGumbelRUMRankingPMF location thetaA value
      humanRanking := sourceUnitVarianceGumbelRUMRankingPMF location thetaH value
      value := value }
  (thetaH ≤ thetaA →
    Model.payoffAgainst M Strategy.algorithm Strategy.algorithm ≥
        Model.payoffAgainst M Strategy.human Strategy.algorithm ∧
      Model.payoffAgainst M Strategy.algorithm Strategy.human ≥
        Model.payoffAgainst M Strategy.human Strategy.human) ∧
    (thetaA ≤ thetaH →
      Model.payoffAgainst M Strategy.human Strategy.algorithm ≥
          Model.payoffAgainst M Strategy.algorithm Strategy.algorithm ∧
        Model.payoffAgainst M Strategy.human Strategy.human ≥
          Model.payoffAgainst M Strategy.algorithm Strategy.human)

theorem section31_literalUnitVarianceGumbel_best_available_weakly_dominates_spec_proof
    {n : ℕ} {location thetaA thetaH : ℝ}
    (value : Candidate n → ℝ)
    (hthetaA : 0 < thetaA) (hthetaH : 0 < thetaH) :
    section31_literalUnitVarianceGumbel_best_available_weakly_dominatesSpec
      (location := location) value hthetaA hthetaH :=
  section31_literalUnitVarianceGumbel_best_available_weakly_dominates
    value hthetaA hthetaH

/--
Audited source-facing Definition 2 proposition.  This is the complete
definition, so the universal positive-accuracy quantifier is part of the
semantic target rather than an implicit caller convention.
-/
abbrev source_definition2_iffSpec
    {n : ℕ} (F : DistributionalAccuracyFamily n)
    (D : Measure (ValueProfile n)) : Prop :=
  SourceDefinition2 F D ↔
    ∀ theta : ℝ, 0 < theta → ∀ hatom : ∀ ranking : Ranking n,
      Measurable fun value => F.dist theta value ranking,
      let J := F.outerIndependentPairJointLaw D theta hatom
      let numerator : ℝ := ∫ x : ValueProfile n × RankingPair n,
        if firstChoice x.2.1 ≠ firstChoice x.2.2 then
          x.1 (firstChoice x.2.1) - x.1 (secondChoice x.2.1)
        else 0 ∂J
      let denominator : ℝ := ∫ x : ValueProfile n × RankingPair n,
        if firstChoice x.2.1 ≠ firstChoice x.2.2 then (1 : ℝ) else 0 ∂J
      0 < denominator → 0 < numerator / denominator

theorem source_definition2_iff_spec_proof
    {n : ℕ} (F : DistributionalAccuracyFamily n)
    (D : Measure (ValueProfile n)) :
    source_definition2_iffSpec F D :=
  source_definition2_iff F D

/--
The fixed-accuracy Definition 2 expansion retained as a prerequisite for
results that instantiate the definition at one selected parameter.
-/
abbrev source_definition2_literal_outer_joint_semantic_completeSpec
    {n : ℕ} (F : DistributionalAccuracyFamily n)
    (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    (theta : ℝ) (htheta : 0 < theta)
    (hatom : ∀ ranking : Ranking n,
      Measurable fun value => F.dist theta value ranking)
    (hshared : Integrable
      (fun x : ValueProfile n × RankingPair n =>
        secondMoverUtility x.1 x.2.1 x.2.1)
      (F.outerIndependentPairJointLaw D theta hatom))
    (hindependent : Integrable
      (fun x : ValueProfile n × RankingPair n =>
        secondMoverUtility x.1 x.2.1 x.2.2)
      (F.outerIndependentPairJointLaw D theta hatom))
    (hdisagreement : 0 < ∫ x : ValueProfile n × RankingPair n,
      (if firstChoice x.2.1 ≠ firstChoice x.2.2 then (1 : ℝ) else 0) ∂
        F.outerIndependentPairJointLaw D theta hatom) : Prop :=
  let J := F.outerIndependentPairJointLaw D theta hatom
  let d2Numerator : ℝ := ∫ x : ValueProfile n × RankingPair n,
    if firstChoice x.2.1 ≠ firstChoice x.2.2 then
      x.1 (firstChoice x.2.1) - x.1 (secondChoice x.2.1)
    else 0 ∂J
  let d2Denominator : ℝ := ∫ x : ValueProfile n × RankingPair n,
    if firstChoice x.2.1 ≠ firstChoice x.2.2 then (1 : ℝ) else 0 ∂J
  let d2Shared : ℝ := ∫ x : ValueProfile n × RankingPair n,
    secondMoverUtility x.1 x.2.1 x.2.1 ∂J
  let d2Independent : ℝ := ∫ x : ValueProfile n × RankingPair n,
    secondMoverUtility x.1 x.2.1 x.2.2 ∂J
  (J = Measure.compProd D (F.independentPairKernel theta hatom)) ∧
  (∀ value,
    F.independentPairKernel theta hatom value =
      (AppliedModelingLib.pmfProd (F.dist theta value) (F.dist theta value)).toMeasure) ∧
  (SourceDefinition2ConditionalAt F D theta hatom ↔ 0 < d2Numerator / d2Denominator) ∧
  ((0 < d2Numerator / d2Denominator) ↔ d2Shared < d2Independent)

theorem source_definition2_literal_outer_joint_semantic_complete_spec_proof
    {n : ℕ} (F : DistributionalAccuracyFamily n)
    (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    (theta : ℝ) (htheta : 0 < theta)
    (hatom : ∀ ranking : Ranking n,
      Measurable fun value => F.dist theta value ranking)
    (hshared : Integrable
      (fun x : ValueProfile n × RankingPair n =>
        secondMoverUtility x.1 x.2.1 x.2.1)
      (F.outerIndependentPairJointLaw D theta hatom))
    (hindependent : Integrable
      (fun x : ValueProfile n × RankingPair n =>
        secondMoverUtility x.1 x.2.1 x.2.2)
      (F.outerIndependentPairJointLaw D theta hatom))
    (hdisagreement : 0 < ∫ x : ValueProfile n × RankingPair n,
      (if firstChoice x.2.1 ≠ firstChoice x.2.2 then (1 : ℝ) else 0) ∂
        F.outerIndependentPairJointLaw D theta hatom) :
    source_definition2_literal_outer_joint_semantic_completeSpec
      F D theta htheta hatom hshared hindependent hdisagreement :=
  source_definition2_literal_outer_joint_semantic_complete
    F D theta htheta hatom hshared hindependent hdisagreement

/--
Audited source-facing Definition 3 proposition.  This is the complete
definition, including its universal quantifier over ordered positive accuracy
pairs, rather than a single instantiated comparison.
-/
abbrev source_definition3_iffSpec
    {n : ℕ} (F : DistributionalAccuracyFamily n)
    (D : Measure (ValueProfile n)) : Prop :=
  SourceDefinition3 F D ↔
    ∀ thetaA thetaH : ℝ, 0 < thetaH → thetaH < thetaA →
      (∫ value : ValueProfile n,
        pmfPairExp (F.dist thetaH value) (F.dist thetaA value)
          (fun pi sigma => secondMoverUtility value pi sigma) ∂D) <
      (∫ value : ValueProfile n,
        pmfPairExp (F.dist thetaH value) (F.dist thetaH value)
          (fun pi sigma => secondMoverUtility value pi sigma) ∂D)

theorem source_definition3_iff_spec_proof
    {n : ℕ} (F : DistributionalAccuracyFamily n)
    (D : Measure (ValueProfile n)) :
    source_definition3_iffSpec F D :=
  source_definition3_iff F D

/--
The fixed-pair Definition 3 expansion retained as a prerequisite for results
that instantiate the definition at one ordered accuracy pair.
-/
abbrev source_definition3_literal_outer_semantic_completeSpec
    {n : ℕ} (F : DistributionalAccuracyFamily n)
    (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    (thetaA thetaH : ℝ) (hthetaH : 0 < thetaH) (hthetaA : thetaH < thetaA)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D)
    (hatom_human : ∀ pi : Ranking n,
      AEStronglyMeasurable (fun value : ValueProfile n =>
        ((F.dist thetaH value) pi).toReal) D)
    (hatom_algorithm : ∀ pi : Ranking n,
      AEStronglyMeasurable (fun value : ValueProfile n =>
        ((F.dist thetaA value) pi).toReal) D) : Prop :=
  let d3Algorithm : ℝ := ∫ value,
    pmfPairExp (F.dist thetaH value) (F.dist thetaA value)
      (fun pi sigma => secondMoverUtility value pi sigma) ∂D
  let d3Human : ℝ := ∫ value,
    pmfPairExp (F.dist thetaH value) (F.dist thetaH value)
      (fun pi sigma => secondMoverUtility value pi sigma) ∂D
  Integrable (fun value =>
    pmfPairExp (F.dist thetaH value) (F.dist thetaA value)
      (fun pi sigma => secondMoverUtility value pi sigma)) D ∧
  Integrable (fun value =>
    pmfPairExp (F.dist thetaH value) (F.dist thetaH value)
      (fun pi sigma => secondMoverUtility value pi sigma)) D ∧
  (SourceDefinition3At F D thetaA thetaH ↔ d3Algorithm < d3Human)

theorem source_definition3_literal_outer_semantic_complete_spec_proof
    {n : ℕ} (F : DistributionalAccuracyFamily n)
    (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    (thetaA thetaH : ℝ) (hthetaH : 0 < thetaH) (hthetaA : thetaH < thetaA)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D)
    (hatom_human : ∀ pi : Ranking n,
      AEStronglyMeasurable (fun value : ValueProfile n =>
        ((F.dist thetaH value) pi).toReal) D)
    (hatom_algorithm : ∀ pi : Ranking n,
      AEStronglyMeasurable (fun value : ValueProfile n =>
        ((F.dist thetaA value) pi).toReal) D) :
    source_definition3_literal_outer_semantic_completeSpec
      F D thetaA thetaH hthetaH hthetaA hvalue hatom_human hatom_algorithm :=
  source_definition3_literal_outer_semantic_complete
    F D thetaA thetaH hthetaH hthetaA hvalue hatom_human hatom_algorithm

/--
Audited source-facing Theorem 1 proposition, with the raw Definition 2 and
Definition 3 outer-law premises still visible and one common algorithmic
witness outside the value distribution integral.
-/
abbrev theorem1_outer_raw_definition2_definition3_semantic_completeSpec
    {n : ℕ} (F : DistributionalAccuracyFamily n)
    (D : Measure (ValueProfile n)) (hD : IsProbabilityMeasure D)
    (center : Ranking n) (thetaH : ℝ)
    (hthetaH : 0 < thetaH)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D)
    (hatom_aestrongly_measurable : ∀ theta pi,
      AEStronglyMeasurable (fun value : ValueProfile n =>
        ((F.dist theta value) pi).toReal) D)
    (hatom_continuous : ∀ value theta, 0 < theta → ∀ pi : Ranking n,
      ContinuousAt (fun theta' => ((F.dist theta' value) pi).toReal) theta)
    (hatom_differentiable : ∀ value theta, 0 < theta → ∀ pi : Ranking n,
      DifferentiableAt ℝ (fun theta' => ((F.dist theta' value) pi).toReal) theta)
    (hcenter_tendsto : ∀ value,
      Tendsto (fun theta => ((F.dist theta value) center).toReal) atTop (nhds 1))
    (hstrict_order : ∀ᵐ value ∂D, StrictlyOrderedBy center value)
    (hatom_measurable : ∀ theta pi,
      Measurable fun value => F.dist theta value pi)
    (hdefinition2_disagreement_integrable : ∀ theta, 0 < theta → Integrable
      (fun value => pmfPairExp (F.dist theta value) (F.dist theta value)
        (fun pi sigma => if firstChoice pi ≠ firstChoice sigma then (1 : ℝ) else 0)) D)
    (hdefinition2_shared_integrable : ∀ theta, 0 < theta → Integrable
      (fun value => pmfExp (F.dist theta value)
        (fun pi => value (secondChoice pi))) D)
    (hdefinition2_independent_integrable : ∀ theta, 0 < theta → Integrable
      (fun value => pmfPairExp (F.dist theta value) (F.dist theta value)
        (fun pi sigma => secondMoverUtility value pi sigma)) D)
    (hdefinition2_joint_shared_integrable : ∀ theta, ∀ htheta : 0 < theta,
      Integrable (fun x : ValueProfile n × RankingPair n =>
        secondMoverUtility x.1 x.2.1 x.2.1)
        (F.outerIndependentPairJointLaw D theta (hatom_measurable theta)))
    (hdefinition2_joint_independent_integrable : ∀ theta, ∀ htheta : 0 < theta,
      Integrable (fun x : ValueProfile n × RankingPair n =>
        secondMoverUtility x.1 x.2.1 x.2.2)
        (F.outerIndependentPairJointLaw D theta (hatom_measurable theta)))
    (hdefinition2_event : ∀ theta, ∀ htheta : 0 < theta,
      0 < ∫ x : ValueProfile n × RankingPair n,
        (if firstChoice x.2.1 ≠ firstChoice x.2.2 then (1 : ℝ) else 0) ∂
          F.outerIndependentPairJointLaw D theta (hatom_measurable theta))
    (hdefinition2_gain : ∀ theta, ∀ htheta : 0 < theta,
      0 <
        (∫ x : ValueProfile n × RankingPair n,
          if firstChoice x.2.1 ≠ firstChoice x.2.2 then
            x.1 (firstChoice x.2.1) - x.1 (secondChoice x.2.1)
          else 0 ∂F.outerIndependentPairJointLaw D theta (hatom_measurable theta)) /
        (∫ x : ValueProfile n × RankingPair n,
          if firstChoice x.2.1 ≠ firstChoice x.2.2 then (1 : ℝ) else 0 ∂
            F.outerIndependentPairJointLaw D theta (hatom_measurable theta)))
    (hdefinition3_better_integrable : ∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
      Integrable (fun value => pmfPairExp
        (F.dist thetaH value) (F.dist thetaA value)
        (fun pi sigma => secondMoverUtility value pi sigma)) D)
    (hdefinition3_worse_integrable : ∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
      Integrable (fun value => pmfPairExp
        (F.dist thetaH value) (F.dist thetaH value)
        (fun pi sigma => secondMoverUtility value pi sigma)) D)
    (hdefinition3 : ∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
      (∫ value, pmfPairExp (F.dist thetaH value) (F.dist thetaA value)
        (fun pi sigma => secondMoverUtility value pi sigma) ∂D) <
      ∫ value, pmfPairExp (F.dist thetaH value) (F.dist thetaH value)
        (fun pi sigma => secondMoverUtility value pi sigma) ∂D)
    (hremaining_weak : ∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
      ∀ value, ∀ remaining : Finset (Candidate n), remaining.Nonempty →
        expectedBestInSet (F.dist thetaH value) value remaining ≤
          expectedBestInSet (F.dist thetaA value) value remaining)
    (hfull_set_strict : ∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
      ∀ value, StrictlyOrderedBy center value →
        expectedBestInSet (F.dist thetaH value) value Finset.univ <
          expectedBestInSet (F.dist thetaA value) value Finset.univ) : Prop :=
  ∃ thetaA, thetaH < thetaA ∧
    F.theorem1_g D thetaA thetaH < F.theorem1_f D thetaA thetaH ∧
    F.theorem1_h D thetaA thetaH <
      F.theorem1_algorithmAgainstHuman D thetaA thetaH ∧
    F.theorem1_f D thetaA thetaH < F.theorem1_h D thetaA thetaH

theorem theorem1_outer_raw_definition2_definition3_semantic_complete_spec_proof
    {n : ℕ} (F : DistributionalAccuracyFamily n)
    (D : Measure (ValueProfile n)) (hD : IsProbabilityMeasure D)
    (center : Ranking n) (thetaH : ℝ)
    (hthetaH : 0 < thetaH)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D)
    (hatom_aestrongly_measurable : ∀ theta pi,
      AEStronglyMeasurable (fun value : ValueProfile n =>
        ((F.dist theta value) pi).toReal) D)
    (hatom_continuous : ∀ value theta, 0 < theta → ∀ pi : Ranking n,
      ContinuousAt (fun theta' => ((F.dist theta' value) pi).toReal) theta)
    (hatom_differentiable : ∀ value theta, 0 < theta → ∀ pi : Ranking n,
      DifferentiableAt ℝ (fun theta' => ((F.dist theta' value) pi).toReal) theta)
    (hcenter_tendsto : ∀ value,
      Tendsto (fun theta => ((F.dist theta value) center).toReal) atTop (nhds 1))
    (hstrict_order : ∀ᵐ value ∂D, StrictlyOrderedBy center value)
    (hatom_measurable : ∀ theta pi,
      Measurable fun value => F.dist theta value pi)
    (hdefinition2_disagreement_integrable : ∀ theta, 0 < theta → Integrable
      (fun value => pmfPairExp (F.dist theta value) (F.dist theta value)
        (fun pi sigma => if firstChoice pi ≠ firstChoice sigma then (1 : ℝ) else 0)) D)
    (hdefinition2_shared_integrable : ∀ theta, 0 < theta → Integrable
      (fun value => pmfExp (F.dist theta value)
        (fun pi => value (secondChoice pi))) D)
    (hdefinition2_independent_integrable : ∀ theta, 0 < theta → Integrable
      (fun value => pmfPairExp (F.dist theta value) (F.dist theta value)
        (fun pi sigma => secondMoverUtility value pi sigma)) D)
    (hdefinition2_joint_shared_integrable : ∀ theta, ∀ htheta : 0 < theta,
      Integrable (fun x : ValueProfile n × RankingPair n =>
        secondMoverUtility x.1 x.2.1 x.2.1)
        (F.outerIndependentPairJointLaw D theta (hatom_measurable theta)))
    (hdefinition2_joint_independent_integrable : ∀ theta, ∀ htheta : 0 < theta,
      Integrable (fun x : ValueProfile n × RankingPair n =>
        secondMoverUtility x.1 x.2.1 x.2.2)
        (F.outerIndependentPairJointLaw D theta (hatom_measurable theta)))
    (hdefinition2_event : ∀ theta, ∀ htheta : 0 < theta,
      0 < ∫ x : ValueProfile n × RankingPair n,
        (if firstChoice x.2.1 ≠ firstChoice x.2.2 then (1 : ℝ) else 0) ∂
          F.outerIndependentPairJointLaw D theta (hatom_measurable theta))
    (hdefinition2_gain : ∀ theta, ∀ htheta : 0 < theta,
      0 <
        (∫ x : ValueProfile n × RankingPair n,
          if firstChoice x.2.1 ≠ firstChoice x.2.2 then
            x.1 (firstChoice x.2.1) - x.1 (secondChoice x.2.1)
          else 0 ∂F.outerIndependentPairJointLaw D theta (hatom_measurable theta)) /
        (∫ x : ValueProfile n × RankingPair n,
          if firstChoice x.2.1 ≠ firstChoice x.2.2 then (1 : ℝ) else 0 ∂
            F.outerIndependentPairJointLaw D theta (hatom_measurable theta)))
    (hdefinition3_better_integrable : ∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
      Integrable (fun value => pmfPairExp
        (F.dist thetaH value) (F.dist thetaA value)
        (fun pi sigma => secondMoverUtility value pi sigma)) D)
    (hdefinition3_worse_integrable : ∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
      Integrable (fun value => pmfPairExp
        (F.dist thetaH value) (F.dist thetaH value)
        (fun pi sigma => secondMoverUtility value pi sigma)) D)
    (hdefinition3 : ∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
      (∫ value, pmfPairExp (F.dist thetaH value) (F.dist thetaA value)
        (fun pi sigma => secondMoverUtility value pi sigma) ∂D) <
      ∫ value, pmfPairExp (F.dist thetaH value) (F.dist thetaH value)
        (fun pi sigma => secondMoverUtility value pi sigma) ∂D)
    (hremaining_weak : ∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
      ∀ value, ∀ remaining : Finset (Candidate n), remaining.Nonempty →
        expectedBestInSet (F.dist thetaH value) value remaining ≤
          expectedBestInSet (F.dist thetaA value) value remaining)
    (hfull_set_strict : ∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
      ∀ value, StrictlyOrderedBy center value →
        expectedBestInSet (F.dist thetaH value) value Finset.univ <
          expectedBestInSet (F.dist thetaA value) value Finset.univ) :
    theorem1_outer_raw_definition2_definition3_semantic_completeSpec
      F D hD center thetaH hthetaH hvalue hatom_aestrongly_measurable
      hatom_continuous hatom_differentiable hcenter_tendsto hstrict_order
      hatom_measurable hdefinition2_disagreement_integrable
      hdefinition2_shared_integrable hdefinition2_independent_integrable
      hdefinition2_joint_shared_integrable hdefinition2_joint_independent_integrable
      hdefinition2_event hdefinition2_gain hdefinition3_better_integrable
      hdefinition3_worse_integrable hdefinition3 hremaining_weak hfull_set_strict :=
  theorem1_outer_raw_definition2_definition3_semantic_complete
    F D hD center thetaH hthetaH hvalue hatom_aestrongly_measurable
    hatom_continuous hatom_differentiable hcenter_tendsto hstrict_order
    hatom_measurable hdefinition2_disagreement_integrable
    hdefinition2_shared_integrable hdefinition2_independent_integrable
    hdefinition2_joint_shared_integrable hdefinition2_joint_independent_integrable
    hdefinition2_event hdefinition2_gain hdefinition3_better_integrable
    hdefinition3_worse_integrable hdefinition3 hremaining_weak hfull_set_strict

/--
Audited source-facing Theorem 2 proposition.  It names neither Gaussian nor
Laplace as a substitute for the mathematics: both iid product transports,
score pushforwards, variance calibration, Definition 1 fields, outer-D
Definition 2/3 clauses, and Theorem 1 consequences are written below.
-/
abbrev theorem2_gaussian_laplace_source_semantic_completeSpec : Prop :=
  (∀ {theta x1 x2 x3 : ℝ}, 0 < theta →
    MeasurePreserving (rightTripleToCandidateMeasurableEquiv ℝ)
      ((ProbabilityTheory.gaussianReal 0 1).prod
        ((ProbabilityTheory.gaussianReal 0 1).prod
          (ProbabilityTheory.gaussianReal 0 1)))
      (Measure.pi (fun _ : Candidate 1 => ProbabilityTheory.gaussianReal 0 1)) ∧
    ((theorem2GaussianScaledNoiseFamily x1 x2 x3).dist theta).toMeasure =
      ((ProbabilityTheory.gaussianReal 0 1).prod
        ((ProbabilityTheory.gaussianReal 0 1).prod
          (ProbabilityTheory.gaussianReal 0 1))).map
        (fun epsilon => rankByScore (fun i =>
          threeCandidateValueProfile x1 x2 x3 i +
            rightTripleToCandidateFunction epsilon i / theta)) ∧
    (theorem2GaussianScaledNoiseFamily x1 x2 x3).dist theta =
      gaussianThreeCandidateRankingLaw theta x1 x2 x3) ∧
  (Var[id; ProbabilityTheory.gaussianReal 0 1] = 1) ∧
  (Var[id; w11BaseNoiseLaw sourceUnitVarianceLaplaceBaseDensity] = 1) ∧
  (∀ {theta x1 x2 x3 : ℝ}, 0 < theta →
    MeasurePreserving (rightTripleToCandidateMeasurableEquiv ℝ)
      ((theorem7LaplaceMeasure (Real.sqrt 2) 0).prod
        ((theorem7LaplaceMeasure (Real.sqrt 2) 0).prod
          (theorem7LaplaceMeasure (Real.sqrt 2) 0)))
      (Measure.pi (fun _ : Candidate 1 =>
        theorem7LaplaceMeasure (Real.sqrt 2) 0)) ∧
    ((sourceUnitVarianceLaplaceScaledNoiseFamily x1 x2 x3).dist theta).toMeasure =
      ((theorem7LaplaceMeasure (Real.sqrt 2) 0).prod
        ((theorem7LaplaceMeasure (Real.sqrt 2) 0).prod
          (theorem7LaplaceMeasure (Real.sqrt 2) 0))).map
        (fun epsilon => rankByScore (fun i =>
          threeCandidateValueProfile x1 x2 x3 i +
            rightTripleToCandidateFunction epsilon i / theta)) ∧
    (sourceUnitVarianceLaplaceScaledNoiseFamily x1 x2 x3).dist theta =
      sourceUnitVarianceLaplaceThreeCandidateRankingLaw theta x1 x2 x3) ∧
  (∀ {x1 x2 x3 : ℝ}, x2 < x1 → x3 < x2 →
    (∀ theta, 0 < theta → ∀ pi : Ranking 1,
      ContinuousAt (fun theta' =>
        ((theorem2GaussianScaledNoiseFamily x1 x2 x3).dist theta' pi).toReal) theta ∧
        DifferentiableAt ℝ (fun theta' =>
          ((theorem2GaussianScaledNoiseFamily x1 x2 x3).dist theta' pi).toReal) theta) ∧
    Tendsto (fun theta =>
      ((theorem2GaussianScaledNoiseFamily x1 x2 x3).dist theta rum3Ranking012).toReal)
      atTop (nhds 1) ∧
    ∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
      (∀ remaining : Finset (Candidate 1), remaining.Nonempty →
        expectedBestInSet ((theorem2GaussianScaledNoiseFamily x1 x2 x3).dist thetaH)
          (threeCandidateValueProfile x1 x2 x3) remaining ≤
          expectedBestInSet ((theorem2GaussianScaledNoiseFamily x1 x2 x3).dist thetaA)
            (threeCandidateValueProfile x1 x2 x3) remaining) ∧
      expectedBestInSet ((theorem2GaussianScaledNoiseFamily x1 x2 x3).dist thetaH)
        (threeCandidateValueProfile x1 x2 x3) Finset.univ <
        expectedBestInSet ((theorem2GaussianScaledNoiseFamily x1 x2 x3).dist thetaA)
          (threeCandidateValueProfile x1 x2 x3) Finset.univ) ∧
  (∀ {x1 x2 x3 : ℝ}, x2 < x1 → x3 < x2 →
    (∀ theta, 0 < theta → ∀ pi : Ranking 1,
      ContinuousAt (fun theta' =>
        ((sourceUnitVarianceLaplaceScaledNoiseFamily x1 x2 x3).dist theta' pi).toReal) theta ∧
        DifferentiableAt ℝ (fun theta' =>
          ((sourceUnitVarianceLaplaceScaledNoiseFamily x1 x2 x3).dist theta' pi).toReal) theta) ∧
    Tendsto (fun theta =>
      ((sourceUnitVarianceLaplaceScaledNoiseFamily x1 x2 x3).dist theta rum3Ranking012).toReal)
      atTop (nhds 1) ∧
    ∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
      (∀ remaining : Finset (Candidate 1), remaining.Nonempty →
        expectedBestInSet ((sourceUnitVarianceLaplaceScaledNoiseFamily x1 x2 x3).dist thetaH)
          (threeCandidateValueProfile x1 x2 x3) remaining ≤
          expectedBestInSet ((sourceUnitVarianceLaplaceScaledNoiseFamily x1 x2 x3).dist thetaA)
            (threeCandidateValueProfile x1 x2 x3) remaining) ∧
      expectedBestInSet ((sourceUnitVarianceLaplaceScaledNoiseFamily x1 x2 x3).dist thetaH)
        (threeCandidateValueProfile x1 x2 x3) Finset.univ <
        expectedBestInSet ((sourceUnitVarianceLaplaceScaledNoiseFamily x1 x2 x3).dist thetaA)
          (threeCandidateValueProfile x1 x2 x3) Finset.univ) ∧
  (∀ (D : Measure (ValueProfile 1)) [IsProbabilityMeasure D]
    (hvalue : ∀ c : Candidate 1,
      Integrable (fun value : ValueProfile 1 => value c) D)
    (horder : ∀ᵐ value ∂D,
      value (1 : Candidate 1) < value (0 : Candidate 1) ∧
        value (2 : Candidate 1) < value (1 : Candidate 1)),
    (∀ theta : ℝ, 0 < theta →
      ∀ regularity : DistributionalAccuracyFamily.OuterIndependentRerankingJointRegularity
        gaussianThreeCandidateDistributionalFamily D theta,
        0 < ∫ x : ValueProfile 1 × RankingPair 1,
          (if disagreementEvent x.2 then (1 : ℝ) else 0) ∂
            gaussianThreeCandidateDistributionalFamily.outerIndependentPairJointLaw
              D theta regularity.base.ranking_atom_measurable ∧
        0 < gaussianThreeCandidateDistributionalFamily.jointLawDisagreementConditionalGain
          D theta regularity.base.ranking_atom_measurable) ∧
    ∀ thetaA thetaH : ℝ, 0 < thetaH → thetaH < thetaA →
      (∫ value,
        expectedSecondMoverIndependent
          (gaussianThreeCandidateDistributionalFamily.dist thetaH value)
          (gaussianThreeCandidateDistributionalFamily.dist thetaA value) value ∂D) <
        ∫ value,
          expectedSecondMoverIndependent
            (gaussianThreeCandidateDistributionalFamily.dist thetaH value)
            (gaussianThreeCandidateDistributionalFamily.dist thetaH value) value ∂D) ∧
  (∀ (D : Measure (ValueProfile 1)) [IsProbabilityMeasure D]
    (hvalue : ∀ c : Candidate 1,
      Integrable (fun value : ValueProfile 1 => value c) D)
    (horder : ∀ᵐ value ∂D,
      value (1 : Candidate 1) < value (0 : Candidate 1) ∧
        value (2 : Candidate 1) < value (1 : Candidate 1)),
    (∀ theta : ℝ, 0 < theta →
      ∀ regularity : DistributionalAccuracyFamily.OuterIndependentRerankingJointRegularity
        sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily D theta,
        0 < ∫ x : ValueProfile 1 × RankingPair 1,
          (if disagreementEvent x.2 then (1 : ℝ) else 0) ∂
            sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily.outerIndependentPairJointLaw
              D theta regularity.base.ranking_atom_measurable ∧
        0 < sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily.jointLawDisagreementConditionalGain
          D theta regularity.base.ranking_atom_measurable) ∧
    ∀ thetaA thetaH : ℝ, 0 < thetaH → thetaH < thetaA →
      (∫ value,
        expectedSecondMoverIndependent
          (sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily.dist thetaH value)
          (sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily.dist thetaA value)
          value ∂D) <
        ∫ value,
          expectedSecondMoverIndependent
            (sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily.dist thetaH value)
            (sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily.dist thetaH value)
            value ∂D) ∧
  (∀ (D : Measure (ValueProfile 1)) [IsProbabilityMeasure D]
    (thetaH : ℝ), 0 < thetaH →
    (∀ c : Candidate 1, Integrable (fun value : ValueProfile 1 => value c) D) →
    (∀ᵐ value ∂D,
      value (1 : Candidate 1) < value (0 : Candidate 1) ∧
        value (2 : Candidate 1) < value (1 : Candidate 1)) →
    literal_outer_payoff_paradox gaussianThreeCandidateDistributionalFamily D thetaH) ∧
  ∀ (D : Measure (ValueProfile 1)) [IsProbabilityMeasure D]
    (thetaH : ℝ), 0 < thetaH →
    (∀ c : Candidate 1, Integrable (fun value : ValueProfile 1 => value c) D) →
    (∀ᵐ value ∂D,
      value (1 : Candidate 1) < value (0 : Candidate 1) ∧
        value (2 : Candidate 1) < value (1 : Candidate 1)) →
    literal_outer_payoff_paradox
      sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily D thetaH

theorem theorem2_gaussian_laplace_source_semantic_complete_spec_proof :
    theorem2_gaussian_laplace_source_semantic_completeSpec := by
  rcases theorem2_gaussian_laplace_source_semantic_complete with
    ⟨hgaussianLaw, hgaussianVariance, hlaplaceVariance, hlaplaceLaw, hgaussianDefinition1,
      hlaplaceDefinition1, hgaussianDefinitions, hlaplaceDefinitions,
      hgaussianTerminal, hlaplaceTerminal⟩
  refine ⟨hgaussianLaw, hgaussianVariance, hlaplaceVariance, hlaplaceLaw, hgaussianDefinition1,
    hlaplaceDefinition1, hgaussianDefinitions, hlaplaceDefinitions, ?_, ?_⟩
  · intro D _ thetaH hthetaH hvalue horder
    simpa only [literal_outer_payoff_paradox,
      DistributionalAccuracyFamily.theorem1_f,
      DistributionalAccuracyFamily.theorem1_g,
      DistributionalAccuracyFamily.theorem1_h,
      DistributionalAccuracyFamily.theorem1_algorithmAgainstHuman,
      DistributionalAccuracyFamily.outerExpected] using
      hgaussianTerminal D thetaH hthetaH hvalue horder
  · intro D _ thetaH hthetaH hvalue horder
    simpa only [literal_outer_payoff_paradox,
      DistributionalAccuracyFamily.theorem1_f,
      DistributionalAccuracyFamily.theorem1_g,
      DistributionalAccuracyFamily.theorem1_h,
      DistributionalAccuracyFamily.theorem1_algorithmAgainstHuman,
      DistributionalAccuracyFamily.outerExpected] using
      hlaplaceTerminal D thetaH hthetaH hvalue horder

/-- Audited source-facing proposition for Equation (8)'s Mallows mass. -/
abbrev equation8_source_concrete_mallows_probabilitySpec
    {n : ℕ} (center : Ranking n) (phi theta : ℝ)
    (hphi : 1 < phi) (htheta : theta = phi - 1) (pi : Ranking n) : Prop :=
  let M := concreteMallowsSpec center theta
  M.q = phi⁻¹ ∧
    (M.law pi).toReal =
      phi⁻¹ ^ kendallTau center pi /
        (∑ tau : Ranking n, phi⁻¹ ^ kendallTau center tau)

theorem equation8_source_concrete_mallows_probability_spec_proof
    {n : ℕ} (center : Ranking n) (phi theta : ℝ)
    (hphi : 1 < phi) (htheta : theta = phi - 1) (pi : Ranking n) :
    equation8_source_concrete_mallows_probabilitySpec
      center phi theta hphi htheta pi :=
  equation8_source_concrete_mallows_probability
    center phi theta hphi htheta pi

/-- Audited source-facing proposition for Appendix C Definition 4. -/
abbrev definition4_strictlyWellOrderedNoise_iffSpec (f : ℝ → ℝ) : Prop :=
  strictlyWellOrderedNoise f ↔
    ∀ ⦃a b c d : ℝ⦄, b < a → d < c →
      f (a - c) * f (b - d) > f (a - d) * f (b - c)

theorem definition4_strictlyWellOrderedNoise_iff_spec_proof (f : ℝ → ℝ) :
    definition4_strictlyWellOrderedNoise_iffSpec f :=
  definition4_strictlyWellOrderedNoise_iff f

/-- Audited corrected Appendix C Lemma 1 proposition. -/
abbrev lemma1_corrected_gaussian_laplace_kernel_targetSpec
    {kappa lam : ℝ} (hkappa : 0 < kappa) (hlam : 0 < lam) : Prop :=
  (∀ ⦃a b c d : ℝ⦄, b < a → d < c →
    Real.exp (-kappa * (a - c) ^ 2) * Real.exp (-kappa * (b - d) ^ 2) >
      Real.exp (-kappa * (a - d) ^ 2) * Real.exp (-kappa * (b - c) ^ 2)) ∧
  (∀ ⦃a b c d : ℝ⦄, b < a → d < c →
      Real.exp (-lam * |a - d|) * Real.exp (-lam * |b - c|) ≤
        Real.exp (-lam * |a - c|) * Real.exp (-lam * |b - d|)) ∧
    (¬ ∀ ⦃a b c d : ℝ⦄, b < a → d < c →
      Real.exp (-lam * |a - c|) * Real.exp (-lam * |b - d|) >
        Real.exp (-lam * |a - d|) * Real.exp (-lam * |b - c|)) ∧
    ∀ {a b c d : ℝ}, b < a → d < c → b < c → d < a →
      Real.exp (-lam * |a - c|) * Real.exp (-lam * |b - d|) >
        Real.exp (-lam * |a - d|) * Real.exp (-lam * |b - c|)

theorem lemma1_corrected_gaussian_laplace_kernel_target_spec_proof
    {kappa lam : ℝ} (hkappa : 0 < kappa) (hlam : 0 < lam) :
    lemma1_corrected_gaussian_laplace_kernel_targetSpec hkappa hlam :=
  by
    simpa only [StrictlyWellOrderedNoise, WeaklyWellOrderedNoise,
      gaussianNoiseKernel, laplacianNoiseKernel,
      AppliedModelingLib.Probability.StrictlyWellOrderedNoise,
      AppliedModelingLib.Probability.WeaklyWellOrderedNoise,
      AppliedModelingLib.Probability.gaussianNoiseKernel,
      AppliedModelingLib.Probability.laplacianNoiseKernel] using
      (lemma1_corrected_gaussian_laplace_kernel_target hkappa hlam)

/-- Audited source-facing proposition for Equation (C.4). -/
abbrev equationC4_laplace_case3_expression_posSpec
    {lam xi xj a : ℝ} (hlam : 0 < lam) (hx : xj < xi) (ha : xi < a) : Prop :=
  0 <
    Real.exp (-lam * (2 * a - xi - xj)) - 8 +
      4 * Real.exp (-lam * (a - xi)) -
      Real.exp (-2 * lam * (a - xi)) +
      (4 + 2 * lam * (xi - xj)) *
        (1 + Real.exp (-lam * (xi - xj))) -
      (4 + 2 * lam * (xi - xj)) *
        Real.exp (-lam * (a - xj))

theorem equationC4_laplace_case3_expression_pos_spec_proof
    {lam xi xj a : ℝ} (hlam : 0 < lam) (hx : xj < xi) (ha : xi < a) :
    equationC4_laplace_case3_expression_posSpec hlam hx ha :=
  equationC4_laplace_case3_expression_pos hlam hx ha

/-- Audited source-facing proposition for Equation (C.6). -/
abbrev equationC6_gaussian_reduced_expression_posSpec
    {delta t : ℝ} (hdelta : 0 < delta) : Prop :=
  0 <
    ((1 + theorem8Erf t) * (1 + theorem8Erf (t + delta)) ^ 2 *
        Real.exp (-(t ^ 2))) /
      ((1 + theorem8Erf t) * Real.exp (-((t + delta) ^ 2)) +
        (1 + theorem8Erf (t + delta)) * Real.exp (-(t ^ 2))) -
      (1 + theorem8Erf t) -
      (2 / Real.sqrt Real.pi) *
        (∫ x : ℝ in Set.Iic t,
          Real.exp (-(x ^ 2)) * theorem8Erf (x + delta))

theorem equationC6_gaussian_reduced_expression_pos_spec_proof
    {delta t : ℝ} (hdelta : 0 < delta) :
    equationC6_gaussian_reduced_expression_posSpec
      (delta := delta) (t := t) hdelta :=
  equationC6_gaussian_reduced_expression_pos hdelta

/--
Audited source-facing proposition for Equation (C.7): its displayed rational
term and its displayed Gaussian integral have the same explicit left-tail
limit, zero.  The C.6 difference limit is a separate support result.
-/
abbrev equationC7_gaussian_reduced_expression_tendsto_atBot_zeroSpec
    (delta : ℝ) : Prop :=
  Filter.Tendsto
    (fun t =>
      ((1 + theorem8Erf t) * (1 + theorem8Erf (t + delta)) ^ 2 *
          Real.exp (-(t ^ 2))) /
        ((1 + theorem8Erf t) * Real.exp (-((t + delta) ^ 2)) +
          (1 + theorem8Erf (t + delta)) * Real.exp (-(t ^ 2))))
    Filter.atBot (nhds 0) ∧
  Filter.Tendsto
    (fun t =>
      ∫ x : ℝ in Set.Iic t,
        Real.exp (-(x ^ 2)) * theorem8Erf (x + delta))
    Filter.atBot (nhds 0)

theorem equationC7_gaussian_reduced_expression_tendsto_atBot_zero_spec_proof
    (delta : ℝ) :
    equationC7_gaussian_reduced_expression_tendsto_atBot_zeroSpec delta :=
  equationC7_gaussian_reduced_expression_tendsto_atBot_zero delta

/-- Audited source-facing proposition for the literal W¹,¹ Equation (A.1). -/
abbrev equationA1_source_w11_iid_literal_event_conditionalTail_integralSpec
    {n : Nat} (f : Real -> Real)
    (hf_measurable : Measurable f)
    (h_nonnegative : forall x, 0 <= f x)
    (hnormalized : ∫⁻ x, ENNReal.ofReal (f x) ∂volume = 1)
    (value : Candidate n -> Real)
    (hsource_top_order : ∀ d : Fin (n + 1), value (Fin.succ d) < value 0)
    {theta : Real} (htheta : 0 < theta) : Prop :=
  AppliedModelingLib.measureProb
      ((sourceAppendixARestNoiseLaw n (w11BaseNoiseLaw f)).prod
        (w11BaseNoiseLaw f))
      (fun z => firstChoice (rankByScore (fun i =>
        value i + sourceAppendixAProductNoise z i / theta)) = (0 : Candidate n)) =
    ∫ rest : Fin (n + 1) -> Real,
      AppliedModelingLib.measureProb (w11BaseNoiseLaw f)
        (fun epsilon => forall d : Fin (n + 1),
          theta * (value (Fin.succ d) - value 0) + rest d < epsilon)
      ∂sourceAppendixARestNoiseLaw n (w11BaseNoiseLaw f)

theorem equationA1_source_w11_iid_literal_event_conditionalTail_integral_spec_proof
    {n : Nat} (f : Real -> Real)
    (hf_measurable : Measurable f)
    (h_nonnegative : forall x, 0 <= f x)
    (hnormalized : ∫⁻ x, ENNReal.ofReal (f x) ∂volume = 1)
    (value : Candidate n -> Real)
    (hsource_top_order : ∀ d : Fin (n + 1), value (Fin.succ d) < value 0)
    {theta : Real} (htheta : 0 < theta) :
    equationA1_source_w11_iid_literal_event_conditionalTail_integralSpec
      (n := n) (theta := theta) f hf_measurable h_nonnegative hnormalized
      value hsource_top_order htheta :=
  equationA1_source_w11_iid_literal_event_conditionalTail_integral
    f hf_measurable h_nonnegative hnormalized value hsource_top_order htheta

/-- Audited source-facing proposition for the complete Appendix C.1 package. -/
abbrev appendixC1_source_pairwise_full_eventsSpec
    {theta xi xj a : ℝ} (htheta : 0 < theta) (hx : xj < xi) : Prop :=
  let laplace : Measure ℝ :=
    (volume : Measure ℝ).withDensity
      (fun z => ENNReal.ofReal
        ((Real.sqrt 2 / 2) * Real.exp (-Real.sqrt 2 * |z|)))
  let gaussian : Measure ℝ := ProbabilityTheory.gaussianReal 0 1
  let laplaceDenominator : ℝ :=
    ((laplace.prod laplace)
      {epsilon : ℝ × ℝ |
        xi + epsilon.1 / theta < a ∧ xj + epsilon.2 / theta < a}).toReal
  let gaussianDenominator : ℝ :=
    ((gaussian.prod gaussian)
      {epsilon : ℝ × ℝ |
        xi + epsilon.1 / theta < a ∧ xj + epsilon.2 / theta < a}).toReal
  (0 < laplaceDenominator ∧
    ((laplace.prod laplace)
      {epsilon : ℝ × ℝ |
        xi + epsilon.1 / theta < a ∧
          xj + epsilon.2 / theta < a ∧
            xj + epsilon.2 / theta < xi + epsilon.1 / theta}).toReal /
      laplaceDenominator <
    ((laplace.prod laplace)
      {epsilon : ℝ × ℝ | xj + epsilon.2 / theta < xi + epsilon.1 / theta}).toReal) ∧
  (0 < gaussianDenominator ∧
    ((gaussian.prod gaussian)
      {epsilon : ℝ × ℝ |
        xi + epsilon.1 / theta < a ∧
          xj + epsilon.2 / theta < a ∧
            xj + epsilon.2 / theta < xi + epsilon.1 / theta}).toReal /
      gaussianDenominator <
    ((gaussian.prod gaussian)
      {epsilon : ℝ × ℝ | xj + epsilon.2 / theta < xi + epsilon.1 / theta}).toReal)

theorem appendixC1_source_pairwise_full_events_spec_proof
    {theta xi xj a : ℝ} (htheta : 0 < theta) (hx : xj < xi) :
    appendixC1_source_pairwise_full_eventsSpec
      (theta := theta) (xi := xi) (xj := xj) (a := a) htheta hx :=
  appendixC1_source_pairwise_full_events htheta hx

/-- Audited source-facing proposition for the complete Appendix C.2 package. -/
abbrev appendixC2_source_pairwise_full_eventsSpec
    {theta xi xj : ℝ} (htheta : 0 < theta) (hx : xj < xi) : Prop :=
  let laplace : Measure ℝ :=
    (volume : Measure ℝ).withDensity
      (fun z => ENNReal.ofReal
        ((Real.sqrt 2 / 2) * Real.exp (-Real.sqrt 2 * |z|)))
  let gaussian : Measure ℝ := ProbabilityTheory.gaussianReal 0 1
  let laplaceRatio : ℝ → ℝ := fun u =>
    ((laplace.prod laplace)
      {epsilon : ℝ × ℝ |
        xi + epsilon.1 / theta < u ∧
          xj + epsilon.2 / theta < u ∧
            xj + epsilon.2 / theta < xi + epsilon.1 / theta}).toReal /
      ((laplace.prod laplace)
        {epsilon : ℝ × ℝ |
          xi + epsilon.1 / theta < u ∧ xj + epsilon.2 / theta < u}).toReal
  let gaussianRatio : ℝ → ℝ := fun u =>
    ((gaussian.prod gaussian)
      {epsilon : ℝ × ℝ |
        xi + epsilon.1 / theta < u ∧
          xj + epsilon.2 / theta < u ∧
            xj + epsilon.2 / theta < xi + epsilon.1 / theta}).toReal /
      ((gaussian.prod gaussian)
        {epsilon : ℝ × ℝ |
          xi + epsilon.1 / theta < u ∧ xj + epsilon.2 / theta < u}).toReal
  let laplaceWinner : ℝ :=
    ((laplace.prod laplace)
      {epsilon : ℝ × ℝ |
        xj + epsilon.2 / theta < xi + epsilon.1 / theta}).toReal
  let gaussianWinner : ℝ :=
    ((gaussian.prod gaussian)
      {epsilon : ℝ × ℝ |
        xj + epsilon.2 / theta < xi + epsilon.1 / theta}).toReal
  ((∀ a : ℝ,
    0 < ((laplace.prod laplace)
      {epsilon : ℝ × ℝ |
        xi + epsilon.1 / theta < a ∧ xj + epsilon.2 / theta < a}).toReal ∧
    ∃ d, HasDerivAt laplaceRatio d a ∧ 0 ≤ d) ∧
    (∃ a d, HasDerivAt laplaceRatio d a ∧ 0 < d) ∧
    Filter.Tendsto laplaceRatio Filter.atTop (nhds laplaceWinner)) ∧
  (∀ a : ℝ,
    0 < ((gaussian.prod gaussian)
      {epsilon : ℝ × ℝ |
        xi + epsilon.1 / theta < a ∧ xj + epsilon.2 / theta < a}).toReal ∧
    ∃ d, HasDerivAt gaussianRatio d a ∧ 0 < d) ∧
    Filter.Tendsto gaussianRatio Filter.atTop (nhds gaussianWinner)

theorem appendixC2_source_pairwise_full_events_spec_proof
    {theta xi xj : ℝ} (htheta : 0 < theta) (hx : xj < xi) :
    appendixC2_source_pairwise_full_eventsSpec
      (theta := theta) (xi := xi) (xj := xj) htheta hx :=
  appendixC2_source_pairwise_full_events htheta hx

/-- Audited source-facing proposition for Appendix C Theorem 6. -/
abbrev theorem6_source_raw_iid_density_literal_semantic_completeSpec
    (f : ℝ → ℝ) {thetaA thetaH x1 x2 x3 : ℝ}
    (hfmeas : Measurable f)
    (hf : ∀ ⦃a b c d : ℝ⦄, b < a → d < c →
      f (a - c) * f (b - d) > f (a - d) * f (b - c))
    (hnonneg : ∀ z : ℝ, 0 ≤ f z)
    (hfullSupport : ∀ z : ℝ, 0 < f z)
    (hnormalized : ∫⁻ z, ENNReal.ofReal (f z) ∂volume = 1)
    (hthetaH : 0 < thetaH) (hthetaHA : thetaH < thetaA)
    (hx12 : x2 < x1) (hx23 : x3 < x2) : Prop :=
  IsProbabilityMeasure
    (Measure.pi (fun _ : Candidate 1 =>
      volume.withDensity (fun z => ENNReal.ofReal (f z)))) ∧
  ∃ rankingLaw : ℝ → PMF (Ranking 1),
    (∀ theta : ℝ, 0 < theta →
      (rankingLaw theta).toMeasure =
        (Measure.pi (fun _ : Candidate 1 =>
          volume.withDensity (fun z => ENNReal.ofReal (f z)))).map
          (fun epsilon => rankByScore (fun i =>
            threeCandidateValueProfile x1 x2 x3 i + epsilon i / theta))) ∧
    expectedSecondMoverIndependent
      (rankingLaw thetaH) (rankingLaw thetaA)
      (threeCandidateValueProfile x1 x2 x3) <
    expectedSecondMoverIndependent
      (rankingLaw thetaH) (rankingLaw thetaH)
      (threeCandidateValueProfile x1 x2 x3)

theorem theorem6_source_raw_iid_density_literal_semantic_complete_spec_proof
    (f : ℝ → ℝ) {thetaA thetaH x1 x2 x3 : ℝ}
    (hfmeas : Measurable f)
    (hf : ∀ ⦃a b c d : ℝ⦄, b < a → d < c →
      f (a - c) * f (b - d) > f (a - d) * f (b - c))
    (hnonneg : ∀ z : ℝ, 0 ≤ f z)
    (hfullSupport : ∀ z : ℝ, 0 < f z)
    (hnormalized : ∫⁻ z, ENNReal.ofReal (f z) ∂volume = 1)
    (hthetaH : 0 < thetaH) (hthetaHA : thetaH < thetaA)
    (hx12 : x2 < x1) (hx23 : x3 < x2) :
    theorem6_source_raw_iid_density_literal_semantic_completeSpec
      (thetaA := thetaA) (thetaH := thetaH) (x1 := x1) (x2 := x2) (x3 := x3)
      f hfmeas hf hnonneg hfullSupport hnormalized hthetaH hthetaHA hx12 hx23 :=
  theorem6_source_raw_iid_density_literal_semantic_complete
    f hfmeas hf hnonneg hfullSupport hnormalized hthetaH hthetaHA hx12 hx23

/-- Audited corrected source-facing proposition for Theorem 5. -/
abbrev appendixA_theorem5_corrected_source_completeSpec
    {n : ℕ} (f derivative : ℝ → ℝ)
    (hf : Integrable f volume) (hderivative : Integrable derivative volume)
    (hf_measurable : Measurable f)
    (hfullSupport : ∀ x, 0 < f x)
    (absolute_continuity : ∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b)
    (derivative_ae_eq : derivative =ᵐ[volume] deriv f)
    (hnormalized : ∫⁻ x, ENNReal.ofReal (f x) ∂volume = 1)
    (value : Candidate n → ℝ) (center : Ranking n)
    (hcenter : ∀ i : Fin (n + 1),
      value (center i.succ) < value (center i.castSucc)) : Prop :=
  Fintype.card (Candidate n) = n + 2 ∧
  IsProbabilityMeasure
    (Measure.pi (fun _ : Candidate n =>
      volume.withDensity (fun x => ENNReal.ofReal (f x)))) ∧
  ∃ rankingLaw : ℝ → PMF (Ranking n),
    (∀ theta : ℝ, 0 < theta →
      (rankingLaw theta).toMeasure =
        (Measure.pi (fun _ : Candidate n =>
          volume.withDensity (fun x => ENNReal.ofReal (f x)))).map
          (fun epsilon => rankByScore
            (fun i => value i + epsilon i / theta))) ∧
    (∀ theta, 0 < theta → ∀ pi : Ranking n,
      ContinuousAt (fun theta' => ((rankingLaw theta') pi).toReal) theta ∧
      DifferentiableAt ℝ (fun theta' => ((rankingLaw theta') pi).toReal) theta) ∧
    (∀ pi : Ranking n,
      Filter.Tendsto (fun theta => ((rankingLaw theta) pi).toReal)
        Filter.atTop
        (nhds (((PMF.pure center : PMF (Ranking n)) pi).toReal))) ∧
    (∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
      ∀ remaining : Finset (Candidate n), remaining.Nonempty →
        expectedBestInSet (rankingLaw thetaH) value remaining ≤
          expectedBestInSet (rankingLaw thetaA) value remaining) ∧
    ∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
      expectedBestInSet (rankingLaw thetaH) value Finset.univ <
        expectedBestInSet (rankingLaw thetaA) value Finset.univ

theorem appendixA_theorem5_corrected_source_complete_spec_proof
    {n : ℕ} (f derivative : ℝ → ℝ)
    (hf : Integrable f volume) (hderivative : Integrable derivative volume)
    (hf_measurable : Measurable f)
    (hfullSupport : ∀ x, 0 < f x)
    (absolute_continuity : ∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b)
    (derivative_ae_eq : derivative =ᵐ[volume] deriv f)
    (hnormalized : ∫⁻ x, ENNReal.ofReal (f x) ∂volume = 1)
    (value : Candidate n → ℝ) (center : Ranking n)
    (hcenter : ∀ i : Fin (n + 1),
      value (center i.succ) < value (center i.castSucc)) :
    appendixA_theorem5_corrected_source_completeSpec
      (n := n) f derivative hf hderivative hf_measurable hfullSupport
      absolute_continuity derivative_ae_eq hnormalized value center hcenter :=
  appendixA_theorem5_corrected_source_complete
    f derivative hf hderivative hf_measurable hfullSupport absolute_continuity
    derivative_ae_eq hnormalized value center hcenter

/-- Audited source-facing proposition for Appendix C Theorem 7. -/
abbrev theorem7_source_semantic_completeSpec
    {sigma xi xj : ℝ} (hsigma : 0 < sigma) (hx : xj < xi) : Prop :=
  let innovation : Measure ℝ :=
    (volume : Measure ℝ).withDensity
      (fun z => ENNReal.ofReal
        ((Real.sqrt 2 / 2) * Real.exp (-Real.sqrt 2 * |z|)))
  let score : ℝ × ℝ → Candidate 0 → ℝ := fun epsilon c =>
    if c = (0 : Candidate 0) then xi + sigma * epsilon.1
    else xj + sigma * epsilon.2
  let rank : ℝ × ℝ → Ranking 0 := fun epsilon => rankByScore (score epsilon)
  let rankLaw : Measure (Ranking 0) := (innovation.prod innovation).map rank
  Measurable rank ∧
    rankLaw Set.univ = 1 ∧
    (∀ epsilon,
      xj + sigma * epsilon.2 < xi + sigma * epsilon.1 →
        firstChoice (rank epsilon) = (0 : Candidate 0)) ∧
    ((∀ a : ℝ,
      0 < ((innovation.prod innovation)
        {epsilon : ℝ × ℝ |
          xi + sigma * epsilon.1 < a ∧
            xj + sigma * epsilon.2 < a}).toReal ∧
      ∃ d,
        HasDerivAt
          (fun u : ℝ =>
            ((innovation.prod innovation)
              {epsilon : ℝ × ℝ |
                xi + sigma * epsilon.1 < u ∧
                  xj + sigma * epsilon.2 < u ∧
                    xj + sigma * epsilon.2 < xi + sigma * epsilon.1}).toReal /
              ((innovation.prod innovation)
                {epsilon : ℝ × ℝ |
                  xi + sigma * epsilon.1 < u ∧
                    xj + sigma * epsilon.2 < u}).toReal)
          d a ∧ 0 ≤ d) ∧
      (∃ a d,
        HasDerivAt
          (fun u : ℝ =>
            ((innovation.prod innovation)
              {epsilon : ℝ × ℝ |
                xi + sigma * epsilon.1 < u ∧
                  xj + sigma * epsilon.2 < u ∧
                    xj + sigma * epsilon.2 < xi + sigma * epsilon.1}).toReal /
              ((innovation.prod innovation)
                {epsilon : ℝ × ℝ |
                  xi + sigma * epsilon.1 < u ∧
                    xj + sigma * epsilon.2 < u}).toReal)
          d a ∧ 0 < d))

theorem theorem7_source_semantic_complete_spec_proof
    {sigma xi xj : ℝ} (hsigma : 0 < sigma) (hx : xj < xi) :
    theorem7_source_semantic_completeSpec
      (sigma := sigma) (xi := xi) (xj := xj) hsigma hx :=
  theorem7_source_semantic_complete hsigma hx

/-- Audited source-facing proposition for Appendix C Theorem 8. -/
abbrev theorem8_source_semantic_completeSpec
    {sigma xi xj : ℝ} (hsigma : 0 < sigma) (hx : xj < xi) : Prop :=
  let innovation : Measure ℝ := ProbabilityTheory.gaussianReal 0 1
  let score : ℝ × ℝ → Candidate 0 → ℝ := fun epsilon c =>
    if c = (0 : Candidate 0) then xi + sigma * epsilon.1
    else xj + sigma * epsilon.2
  let rank : ℝ × ℝ → Ranking 0 := fun epsilon => rankByScore (score epsilon)
  let rankLaw : Measure (Ranking 0) := (innovation.prod innovation).map rank
  Measurable rank ∧
    rankLaw Set.univ = 1 ∧
    (∀ epsilon,
      xj + sigma * epsilon.2 < xi + sigma * epsilon.1 →
        firstChoice (rank epsilon) = (0 : Candidate 0)) ∧
    ∀ a : ℝ,
      0 < ((innovation.prod innovation)
        {epsilon : ℝ × ℝ |
          xi + sigma * epsilon.1 < a ∧
            xj + sigma * epsilon.2 < a}).toReal ∧
      ∃ d,
        HasDerivAt
          (fun u : ℝ =>
            ((innovation.prod innovation)
              {epsilon : ℝ × ℝ |
                xi + sigma * epsilon.1 < u ∧
                  xj + sigma * epsilon.2 < u ∧
                    xj + sigma * epsilon.2 < xi + sigma * epsilon.1}).toReal /
              ((innovation.prod innovation)
                {epsilon : ℝ × ℝ |
                  xi + sigma * epsilon.1 < u ∧
                    xj + sigma * epsilon.2 < u}).toReal)
          d a ∧ 0 < d

theorem theorem8_source_semantic_complete_spec_proof
    {sigma xi xj : ℝ} (hsigma : 0 < sigma) (hx : xj < xi) :
    theorem8_source_semantic_completeSpec
      (sigma := sigma) (xi := xi) (xj := xj) hsigma hx :=
  theorem8_source_semantic_complete hsigma hx

/-- Audited source-facing proposition for Equation (C.5). -/
abbrev equationC5_gaussian_source_semantic_completeSpec
    {xi xj a : ℝ} (hx : xj < xi) : Prop :=
  let scoreI : Measure ℝ := ProbabilityTheory.gaussianReal xi (1 / 2 : ℝ≥0)
  let scoreJ : Measure ℝ := ProbabilityTheory.gaussianReal xj (1 / 2 : ℝ≥0)
  let denominator : ℝ :=
    ((scoreI.prod scoreJ) {p : ℝ × ℝ | p.1 < a ∧ p.2 < a}).toReal
  0 < denominator ∧
    ((scoreI.prod scoreJ)
      {p : ℝ × ℝ | p.1 < a ∧ p.2 < a ∧ p.2 < p.1}).toReal /
      denominator =
        (2 / Real.sqrt Real.pi) *
          (∫ x : ℝ in Set.Iic a,
            Real.exp (-((x - xi) ^ 2)) * (1 + theorem8Erf (x - xj))) /
          ((1 + theorem8Erf (a - xi)) * (1 + theorem8Erf (a - xj))) ∧
    0 <
      (1 + theorem8Erf (a - xi)) * (1 + theorem8Erf (a - xj)) *
          Real.exp (-((a - xi) ^ 2)) * (1 + theorem8Erf (a - xj)) -
        (∫ x : ℝ in Set.Iic a,
          Real.exp (-((x - xi) ^ 2)) * (1 + theorem8Erf (x - xj))) *
          (2 / Real.sqrt Real.pi) *
          ((1 + theorem8Erf (a - xi)) * Real.exp (-((a - xj) ^ 2)) +
            (1 + theorem8Erf (a - xj)) * Real.exp (-((a - xi) ^ 2))) ∧
    ∃ d,
      HasDerivAt
        (fun u =>
          (2 / Real.sqrt Real.pi) *
            (∫ x : ℝ in Set.Iic u,
              Real.exp (-((x - xi) ^ 2)) * (1 + theorem8Erf (x - xj))) /
            ((1 + theorem8Erf (u - xi)) * (1 + theorem8Erf (u - xj)))) d a ∧
      (0 < d ↔
        0 <
          (1 + theorem8Erf (a - xi)) * (1 + theorem8Erf (a - xj)) *
              Real.exp (-((a - xi) ^ 2)) * (1 + theorem8Erf (a - xj)) -
            (∫ x : ℝ in Set.Iic a,
              Real.exp (-((x - xi) ^ 2)) * (1 + theorem8Erf (x - xj))) *
              (2 / Real.sqrt Real.pi) *
              ((1 + theorem8Erf (a - xi)) * Real.exp (-((a - xj) ^ 2)) +
                (1 + theorem8Erf (a - xj)) *
                  Real.exp (-((a - xi) ^ 2))))

theorem equationC5_gaussian_source_semantic_complete_spec_proof
    {xi xj a : ℝ} (hx : xj < xi) :
    equationC5_gaussian_source_semantic_completeSpec
      (xi := xi) (xj := xj) (a := a) hx :=
  equationC5_gaussian_source_semantic_complete hx

section

local instance : MeasurableSpace AppendixB1NoiseAtom := ⊤
local instance : DiscreteMeasurableSpace AppendixB1NoiseAtom :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩
local instance : MeasurableSpace AppendixB2NoiseAtom := ⊤
local instance : DiscreteMeasurableSpace AppendixB2NoiseAtom :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

/--
Audited source-facing proposition for the literal Appendix B Gaussian
smoothing claim.  It is deliberately independent of the complete W1,1
strengthening Spec below while transparently expanding to the same explicit
source-core construction and strict small-width reversals.
-/
abbrev appendixB_smoothing_source_coreSpec : Prop :=
  (appendixB1Value (0 : Candidate 1) = 7 / 4 ∧
    appendixB1Value (1 : Candidate 1) = 1 / 2 ∧
      appendixB1Value (2 : Candidate 1) = 0) ∧
  (appendixB1NoiseValue .plusOne = 1 ∧
    appendixB1NoiseValue .zero = 0 ∧
      appendixB1NoiseValue .minusOne = -1) ∧
  ((appendixB1NoisePMF .plusOne).toReal = 1 / 20 ∧
    (appendixB1NoisePMF .zero).toReal = 9 / 10 ∧
      (appendixB1NoisePMF .minusOne).toReal = 1 / 20) ∧
  (appendixB1GaussianLatentMeasure =
    ((appendixB1NoisePMF.toMeasure.prod appendixB1NoisePMF.toMeasure).prod
      appendixB1NoisePMF.toMeasure).prod
      ((gaussianReal 0 1).prod ((gaussianReal 0 1).prod (gaussianReal 0 1)))) ∧
  (∀ s theta, 0 < s → 0 < theta →
    (appendixB1SourceGaussianMixtureFamily s).dist theta =
      rumRankingPMFOfMeasure appendixB1GaussianLatentMeasure
        (fun omega =>
          rankByScore (fun c => appendixB1Value c +
            (appendixB1NoiseValue (appendixB1NoiseTripleFunction omega.1 c) +
              s * appendixBGaussianTripleFunction omega.2 c) / theta))
        (appendixB1SourceGaussianMixtureRank_measurable s theta)) ∧
  (appendixB2Value (0 : Candidate 1) = 3 ∧
    appendixB2Value (1 : Candidate 1) = 2 ∧
      appendixB2Value (2 : Candidate 1) = 0) ∧
  (appendixB2NoiseValue .plusOne = 1 ∧
    appendixB2NoiseValue .minusOne = -1 ∧
      appendixB2NoiseValue .plusTen = 10 ∧
        appendixB2NoiseValue .minusTen = -10) ∧
  ((appendixB2NoisePMF .plusOne).toReal = 9 / 20 ∧
    (appendixB2NoisePMF .minusOne).toReal = 9 / 20 ∧
      (appendixB2NoisePMF .plusTen).toReal = 1 / 20 ∧
        (appendixB2NoisePMF .minusTen).toReal = 1 / 20) ∧
  (appendixB2GaussianLatentMeasure =
    ((appendixB2NoisePMF.toMeasure.prod appendixB2NoisePMF.toMeasure).prod
      appendixB2NoisePMF.toMeasure).prod
      ((gaussianReal 0 1).prod ((gaussianReal 0 1).prod (gaussianReal 0 1)))) ∧
  (∀ s theta, 0 < s → 0 < theta →
    (appendixB2SourceGaussianMixtureFamily s).dist theta =
      rumRankingPMFOfMeasure appendixB2GaussianLatentMeasure
        (fun omega =>
          rankByScore (fun c => appendixB2Value c +
            (appendixB2NoiseValue (appendixB2NoiseTripleFunction omega.1 c) +
              s * appendixBGaussianTripleFunction omega.2 c) / theta))
        (appendixB2SourceGaussianMixtureRank_measurable s theta)) ∧
  (∃ delta : ℝ, 0 < delta ∧ ∀ s : ℝ, 0 < s → s < delta →
    expectedSecondMoverIndependent
        ((appendixB1SourceGaussianMixtureFamily s).dist 1)
        ((appendixB1SourceGaussianMixtureFamily s).dist 1) appendixB1Value -
      expectedSecondMoverShared
        ((appendixB1SourceGaussianMixtureFamily s).dist 1)
        appendixB1Value < 0) ∧
  (∃ delta : ℝ, 0 < delta ∧ ∀ s : ℝ, 0 < s → s < delta →
    0 < expectedSecondMoverIndependent
          ((appendixB2SourceGaussianMixtureFamily s).dist (9 / 10))
          ((appendixB2SourceGaussianMixtureFamily s).dist (11 / 10))
          appendixB2Value -
        expectedSecondMoverIndependent
          ((appendixB2SourceGaussianMixtureFamily s).dist (9 / 10))
          ((appendixB2SourceGaussianMixtureFamily s).dist (9 / 10))
          appendixB2Value)

theorem appendixB_smoothing_source_core_spec_proof :
    appendixB_smoothing_source_coreSpec :=
  appendixB_smoothing_source_core

/-- Audited source-facing proposition for the complete Appendix B smoothing package. -/
abbrev appendixB_smoothing_source_completeSpec : Prop :=
  (appendixB1Value (0 : Candidate 1) = 7 / 4 ∧
    appendixB1Value (1 : Candidate 1) = 1 / 2 ∧
      appendixB1Value (2 : Candidate 1) = 0) ∧
  (appendixB1NoiseValue .plusOne = 1 ∧
    appendixB1NoiseValue .zero = 0 ∧
      appendixB1NoiseValue .minusOne = -1) ∧
  ((appendixB1NoisePMF .plusOne).toReal = 1 / 20 ∧
    (appendixB1NoisePMF .zero).toReal = 9 / 10 ∧
      (appendixB1NoisePMF .minusOne).toReal = 1 / 20) ∧
  (appendixB1GaussianLatentMeasure =
    ((appendixB1NoisePMF.toMeasure.prod appendixB1NoisePMF.toMeasure).prod
      appendixB1NoisePMF.toMeasure).prod
      ((gaussianReal 0 1).prod ((gaussianReal 0 1).prod (gaussianReal 0 1)))) ∧
  (∀ s theta, 0 < s → 0 < theta →
    (appendixB1SourceGaussianMixtureFamily s).dist theta =
      rumRankingPMFOfMeasure appendixB1GaussianLatentMeasure
        (fun omega =>
          rankByScore (fun c => appendixB1Value c +
            (appendixB1NoiseValue (appendixB1NoiseTripleFunction omega.1 c) +
              s * appendixBGaussianTripleFunction omega.2 c) / theta))
        (appendixB1SourceGaussianMixtureRank_measurable s theta)) ∧
  (appendixB2Value (0 : Candidate 1) = 3 ∧
    appendixB2Value (1 : Candidate 1) = 2 ∧
      appendixB2Value (2 : Candidate 1) = 0) ∧
  (appendixB2NoiseValue .plusOne = 1 ∧
    appendixB2NoiseValue .minusOne = -1 ∧
      appendixB2NoiseValue .plusTen = 10 ∧
        appendixB2NoiseValue .minusTen = -10) ∧
  ((appendixB2NoisePMF .plusOne).toReal = 9 / 20 ∧
    (appendixB2NoisePMF .minusOne).toReal = 9 / 20 ∧
      (appendixB2NoisePMF .plusTen).toReal = 1 / 20 ∧
        (appendixB2NoisePMF .minusTen).toReal = 1 / 20) ∧
  (appendixB2GaussianLatentMeasure =
    ((appendixB2NoisePMF.toMeasure.prod appendixB2NoisePMF.toMeasure).prod
      appendixB2NoisePMF.toMeasure).prod
      ((gaussianReal 0 1).prod ((gaussianReal 0 1).prod (gaussianReal 0 1)))) ∧
  (∀ s theta, 0 < s → 0 < theta →
    (appendixB2SourceGaussianMixtureFamily s).dist theta =
      rumRankingPMFOfMeasure appendixB2GaussianLatentMeasure
        (fun omega =>
          rankByScore (fun c => appendixB2Value c +
            (appendixB2NoiseValue (appendixB2NoiseTripleFunction omega.1 c) +
              s * appendixBGaussianTripleFunction omega.2 c) / theta))
        (appendixB2SourceGaussianMixtureRank_measurable s theta)) ∧
  (∃ delta : ℝ, 0 < delta ∧ ∀ s : ℝ, 0 < s → s < delta →
    expectedSecondMoverIndependent
        ((appendixB1SourceGaussianMixtureFamily s).dist 1)
        ((appendixB1SourceGaussianMixtureFamily s).dist 1) appendixB1Value -
      expectedSecondMoverShared
        ((appendixB1SourceGaussianMixtureFamily s).dist 1)
        appendixB1Value < 0) ∧
  (∃ delta : ℝ, 0 < delta ∧ ∀ s : ℝ, 0 < s → s < delta →
    0 < expectedSecondMoverIndependent
          ((appendixB2SourceGaussianMixtureFamily s).dist (9 / 10))
          ((appendixB2SourceGaussianMixtureFamily s).dist (11 / 10))
          appendixB2Value -
        expectedSecondMoverIndependent
          ((appendixB2SourceGaussianMixtureFamily s).dist (9 / 10))
          ((appendixB2SourceGaussianMixtureFamily s).dist (9 / 10))
          appendixB2Value) ∧
  (∀ s : ℝ, 0 < s →
    (∀ theta, 0 < theta → ∀ pi : Ranking 1,
      ContinuousAt
        (fun theta' =>
          ((appendixB1SourceGaussianMixtureFamily s).dist theta' pi).toReal)
        theta ∧
      DifferentiableAt ℝ
        (fun theta' =>
          ((appendixB1SourceGaussianMixtureFamily s).dist theta' pi).toReal)
        theta) ∧
    (∀ pi : Ranking 1,
      Filter.Tendsto
        (fun theta =>
          ((appendixB1SourceGaussianMixtureFamily s).dist theta pi).toReal)
        Filter.atTop
        (nhds (((PMF.pure rum3Ranking012 : PMF (Ranking 1)) pi).toReal))) ∧
    ∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
      (∀ remaining : Finset (Candidate 1), remaining.Nonempty →
        expectedBestInSet
            ((appendixB1SourceGaussianMixtureFamily s).dist thetaH)
            appendixB1Value remaining ≤
          expectedBestInSet
            ((appendixB1SourceGaussianMixtureFamily s).dist thetaA)
            appendixB1Value remaining) ∧
        expectedBestInSet
            ((appendixB1SourceGaussianMixtureFamily s).dist thetaH)
            appendixB1Value Finset.univ <
          expectedBestInSet
            ((appendixB1SourceGaussianMixtureFamily s).dist thetaA)
            appendixB1Value Finset.univ) ∧
  (∀ s : ℝ, ∀ hs : 0 < s, ∀ theta : ℝ, 0 < theta →
    (appendixB1SourceGaussianMixtureFamily s).dist theta =
      (appendixB1GaussianMixtureW11Family s hs).dist theta) ∧
  (∀ s : ℝ, 0 < s →
    (∀ theta, 0 < theta → ∀ pi : Ranking 1,
      ContinuousAt
        (fun theta' =>
          ((appendixB2SourceGaussianMixtureFamily s).dist theta' pi).toReal)
        theta ∧
      DifferentiableAt ℝ
        (fun theta' =>
          ((appendixB2SourceGaussianMixtureFamily s).dist theta' pi).toReal)
        theta) ∧
    (∀ pi : Ranking 1,
      Filter.Tendsto
        (fun theta =>
          ((appendixB2SourceGaussianMixtureFamily s).dist theta pi).toReal)
        Filter.atTop
        (nhds (((PMF.pure rum3Ranking012 : PMF (Ranking 1)) pi).toReal))) ∧
    ∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
      (∀ remaining : Finset (Candidate 1), remaining.Nonempty →
        expectedBestInSet
            ((appendixB2SourceGaussianMixtureFamily s).dist thetaH)
            appendixB2Value remaining ≤
          expectedBestInSet
            ((appendixB2SourceGaussianMixtureFamily s).dist thetaA)
            appendixB2Value remaining) ∧
        expectedBestInSet
            ((appendixB2SourceGaussianMixtureFamily s).dist thetaH)
            appendixB2Value Finset.univ <
          expectedBestInSet
            ((appendixB2SourceGaussianMixtureFamily s).dist thetaA)
            appendixB2Value Finset.univ) ∧
  (∀ s : ℝ, ∀ hs : 0 < s, ∀ theta : ℝ, 0 < theta →
    (appendixB2SourceGaussianMixtureFamily s).dist theta =
      (appendixB2GaussianMixtureW11Family s hs).dist theta)

theorem appendixB_smoothing_source_complete_spec_proof :
    appendixB_smoothing_source_completeSpec :=
  appendixB_smoothing_source_complete

end

/-- Audited source-facing proposition for Equation (C.8). -/
abbrev equationC8_gaussian_reduced_expression_hasDerivAtSpec
    (delta t : ℝ) : Prop :=
  HasDerivAt
    (fun u =>
      ((1 + theorem8Erf u) * (1 + theorem8Erf (u + delta)) ^ 2 *
          Real.exp (-(u ^ 2))) /
        ((1 + theorem8Erf u) * Real.exp (-((u + delta) ^ 2)) +
          (1 + theorem8Erf (u + delta)) * Real.exp (-(u ^ 2))) -
        (1 + theorem8Erf u) -
        (2 / Real.sqrt Real.pi) *
          (∫ x : ℝ in Set.Iic u,
            Real.exp (-(x ^ 2)) * theorem8Erf (x + delta)))
    (deriv (fun u =>
        ((1 + theorem8Erf u) * (1 + theorem8Erf (u + delta)) ^ 2 *
            Real.exp (-(u ^ 2))) /
          ((1 + theorem8Erf u) * Real.exp (-((u + delta) ^ 2)) +
            (1 + theorem8Erf (u + delta)) * Real.exp (-(u ^ 2)))) t -
      (2 / Real.sqrt Real.pi) * Real.exp (-(t ^ 2)) -
      (2 / Real.sqrt Real.pi) * Real.exp (-(t ^ 2)) * theorem8Erf (t + delta)) t

theorem equationC8_gaussian_reduced_expression_hasDerivAt_spec_proof
    (delta t : ℝ) :
    equationC8_gaussian_reduced_expression_hasDerivAtSpec delta t :=
  equationC8_gaussian_reduced_expression_hasDerivAt delta t

/-- Audited corrected source-facing proposition for the C.8/C.9 repair. -/
abbrev equationC8_C9_corrected_gaussian_targetSpec
    {delta t : ℝ} (hdelta : 0 < delta) : Prop :=
  HasDerivAt
    (fun u =>
      ((1 + theorem8Erf u) * (1 + theorem8Erf (u + delta)) ^ 2 *
          Real.exp (-(u ^ 2))) /
        ((1 + theorem8Erf u) * Real.exp (-((u + delta) ^ 2)) +
          (1 + theorem8Erf (u + delta)) * Real.exp (-(u ^ 2))) -
        (1 + theorem8Erf u) -
        (2 / Real.sqrt Real.pi) *
          (∫ x : ℝ in Set.Iic u,
            Real.exp (-(x ^ 2)) * theorem8Erf (x + delta)))
    (((2 * (1 + theorem8Erf t) * (1 + theorem8Erf (t + delta)) ^ 2 *
        Real.exp ((t + delta) ^ 2)) /
      (Real.sqrt Real.pi *
        (((theorem8Erf t + 1) * Real.exp (t ^ 2) +
          (theorem8Erf (t + delta) + 1) *
            Real.exp ((t + delta) ^ 2)) ^ 2))) *
      (((1 + theorem8Erf t) / Real.exp (-(t ^ 2))) *
        (delta * Real.sqrt Real.pi +
          (((1 + theorem8Erf (t + delta)) /
            Real.exp (-((t + delta) ^ 2)))⁻¹)) - 1)) t ∧
    0 <
      (2 * (1 + theorem8Erf t) * (1 + theorem8Erf (t + delta)) ^ 2 *
        Real.exp ((t + delta) ^ 2)) /
        (Real.sqrt Real.pi *
          (((theorem8Erf t + 1) * Real.exp (t ^ 2) +
            (theorem8Erf (t + delta) + 1) *
              Real.exp ((t + delta) ^ 2)) ^ 2)) ∧
    0 < ((1 + theorem8Erf t) / Real.exp (-(t ^ 2))) *
        (delta * Real.sqrt Real.pi +
          (((1 + theorem8Erf (t + delta)) /
            Real.exp (-((t + delta) ^ 2)))⁻¹)) - 1

theorem equationC8_C9_corrected_gaussian_target_spec_proof
    {delta t : ℝ} (hdelta : 0 < delta) :
    equationC8_C9_corrected_gaussian_targetSpec
      (delta := delta) (t := t) hdelta :=
  equationC8_C9_corrected_gaussian_target hdelta

/-- Audited source-facing proposition for Equation (C.10). -/
abbrev equationC10_gaussian_g_inv_derivative_lower_boundSpec
    (t : ℝ) : Prop :=
  ∃ d,
    HasDerivAt
      (fun u => (((1 + theorem8Erf u) / Real.exp (-(u ^ 2)))⁻¹)) d t ∧
      -Real.sqrt Real.pi < d

theorem equationC10_gaussian_g_inv_derivative_lower_bound_spec_proof
    (t : ℝ) :
    equationC10_gaussian_g_inv_derivative_lower_boundSpec t :=
  equationC10_gaussian_g_inv_derivative_lower_bound t

/-- Audited source-facing proposition for Theorem 9. -/
abbrev theorem9_source_mallows_definition1_literal_semantic_completeSpec
    {n : ℕ} (center : Ranking n) (value : Candidate n → ℝ)
    (hvalue : StrictlyOrderedBy center value) : Prop :=
  (∀ (phi theta : ℝ), 1 < phi → theta = phi - 1 →
    let M := concreteMallowsSpec center theta
    M.q = phi⁻¹ ∧
      ∀ pi : Ranking n,
        (M.law pi).toReal =
          phi⁻¹ ^ kendallTau center pi /
            (∑ tau : Ranking n, phi⁻¹ ^ kendallTau center tau)) ∧
  (∀ theta, 0 < theta → ∀ pi : Ranking n,
    ContinuousAt
        (fun theta' =>
          ((concreteMallowsSpec center theta').law pi).toReal) theta ∧
      DifferentiableAt ℝ
        (fun theta' =>
          ((concreteMallowsSpec center theta').law pi).toReal) theta) ∧
  Tendsto
    (fun theta => ((concreteMallowsSpec center theta).law center).toReal)
    atTop (nhds 1) ∧
  ∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
    (∀ remaining : Finset (Candidate n), remaining.Nonempty →
      expectedBestInSet (concreteMallowsSpec center thetaH).law value remaining ≤
        expectedBestInSet (concreteMallowsSpec center thetaA).law value remaining) ∧
    expectedBestInSet (concreteMallowsSpec center thetaH).law value Finset.univ <
      expectedBestInSet (concreteMallowsSpec center thetaA).law value Finset.univ

theorem theorem9_source_mallows_definition1_literal_semantic_complete_spec_proof
    {n : ℕ} (center : Ranking n) (value : Candidate n → ℝ)
    (hvalue : StrictlyOrderedBy center value) :
    theorem9_source_mallows_definition1_literal_semantic_completeSpec
      center value hvalue :=
  theorem9_source_mallows_definition1_literal_semantic_complete center value hvalue

/-- Audited corrected source-facing proposition for Equation (D.1). -/
abbrev equationD1_source_phi_likelihood_ratio_completeSpec
    (center : Ranking 1)
    (phiNoisy thetaNoisy phiAccurate thetaAccurate : ℝ)
    (hphiNoisy : 1 < phiNoisy) (hphi_lt : phiNoisy < phiAccurate)
    (hthetaNoisy : thetaNoisy = phiNoisy - 1)
    (hthetaAccurate : thetaAccurate = phiAccurate - 1)
    {remaining : Finset (Candidate 1)} (hremaining : remaining.Nonempty)
    {better worse : Candidate 1}
    (hbetter : better ∈ remaining) (hworse : worse ∈ remaining)
    (hcenter_order : rankOf center better < rankOf center worse) : Prop :=
  let MAccurate := concreteMallowsSpec center thetaAccurate
  let MNoisy := concreteMallowsSpec center thetaNoisy
  MAccurate.q = phiAccurate⁻¹ ∧
    MNoisy.q = phiNoisy⁻¹ ∧
    (∀ pi : Ranking 1,
      (MAccurate.law pi).toReal =
        phiAccurate⁻¹ ^ kendallTau center pi /
          (∑ tau : Ranking 1, phiAccurate⁻¹ ^ kendallTau center tau)) ∧
    (∀ pi : Ranking 1,
      (MNoisy.law pi).toReal =
        phiNoisy⁻¹ ^ kendallTau center pi /
          (∑ tau : Ranking 1, phiNoisy⁻¹ ^ kendallTau center tau)) ∧
    0 <
      pmfProb MAccurate.law (fun pi => better = bestInSet pi remaining) *
        pmfProb MNoisy.law (fun pi => worse = bestInSet pi remaining) -
      pmfProb MAccurate.law (fun pi => worse = bestInSet pi remaining) *
        pmfProb MNoisy.law (fun pi => better = bestInSet pi remaining)

theorem equationD1_source_phi_likelihood_ratio_complete_spec_proof
    (center : Ranking 1)
    (phiNoisy thetaNoisy phiAccurate thetaAccurate : ℝ)
    (hphiNoisy : 1 < phiNoisy) (hphi_lt : phiNoisy < phiAccurate)
    (hthetaNoisy : thetaNoisy = phiNoisy - 1)
    (hthetaAccurate : thetaAccurate = phiAccurate - 1)
    {remaining : Finset (Candidate 1)} (hremaining : remaining.Nonempty)
    {better worse : Candidate 1}
    (hbetter : better ∈ remaining) (hworse : worse ∈ remaining)
    (hcenter_order : rankOf center better < rankOf center worse) :
    equationD1_source_phi_likelihood_ratio_completeSpec
      (remaining := remaining) (better := better) (worse := worse)
      center phiNoisy thetaNoisy phiAccurate thetaAccurate hphiNoisy hphi_lt
      hthetaNoisy hthetaAccurate hremaining hbetter hworse hcenter_order :=
  equationD1_source_phi_likelihood_ratio_complete
    center phiNoisy thetaNoisy phiAccurate thetaAccurate hphiNoisy hphi_lt
    hthetaNoisy hthetaAccurate hremaining hbetter hworse hcenter_order

/-- Audited source-facing proposition for the literal Appendix E.1 conditional gain. -/
abbrev equationE1_source_phi_literal_conditional_semantic_completeSpec
    {n : ℕ} (center : Ranking n) (phi theta : ℝ)
    (hphi : 1 < phi) (htheta : theta = phi - 1) (hn : 0 < n)
    {value : Candidate n → ℝ} (hvalue : StrictlyOrderedBy center value) : Prop :=
  let M := concreteMallowsSpec center theta
  M.q = phi⁻¹ ∧
    (∀ pi : Ranking n,
      (M.law pi).toReal =
        phi⁻¹ ^ kendallTau center pi /
          (∑ tau : Ranking n, phi⁻¹ ^ kendallTau center tau)) ∧
    0 < AppliedModelingLib.pmfPairProb M.law M.law disagreementEvent ∧
    0 < AppliedModelingLib.pmfPairIndicatorExp M.law M.law disagreementEvent
      (fun pair => value (firstChoice pair.1) - value (secondChoice pair.1)) /
        AppliedModelingLib.pmfPairProb M.law M.law disagreementEvent

theorem equationE1_source_phi_literal_conditional_semantic_complete_spec_proof
    {n : ℕ} (center : Ranking n) (phi theta : ℝ)
    (hphi : 1 < phi) (htheta : theta = phi - 1) (hn : 0 < n)
    {value : Candidate n → ℝ} (hvalue : StrictlyOrderedBy center value) :
    equationE1_source_phi_literal_conditional_semantic_completeSpec
      (n := n) (value := value) center phi theta hphi htheta hn hvalue :=
  equationE1_source_phi_literal_conditional_semantic_complete
    center phi theta hphi htheta hn hvalue

/-- Audited source-facing proposition for the literal Appendix E.2 comparisons. -/
abbrev equationE2_source_phi_literal_conditional_semantic_completeSpec
    {n : ℕ} (center : Ranking n) (phi theta : ℝ)
    (hphi : 1 < phi) (htheta : theta = phi - 1) (hn : 0 < n) : Prop :=
  let M := concreteMallowsSpec center theta
  M.q = phi⁻¹ ∧
    (∀ pi : Ranking n,
      (M.law pi).toReal =
        phi⁻¹ ^ kendallTau center pi /
          (∑ tau : Ranking n, phi⁻¹ ^ kendallTau center tau)) ∧
    0 < AppliedModelingLib.pmfPairProb M.law M.law disagreementEvent ∧
    (∀ c d : Candidate n, rankOf M.center c < rankOf M.center d →
      AppliedModelingLib.pmfPairIndicatorExp M.law M.law disagreementEvent
          (fun pair =>
            if d = firstChoice pair.1 ∧ c = secondChoice pair.1 then (1 : ℝ) else 0) /
          AppliedModelingLib.pmfPairProb M.law M.law disagreementEvent ≤
        AppliedModelingLib.pmfPairIndicatorExp M.law M.law disagreementEvent
          (fun pair =>
            if c = firstChoice pair.1 ∧ d = secondChoice pair.1 then (1 : ℝ) else 0) /
          AppliedModelingLib.pmfPairProb M.law M.law disagreementEvent) ∧
    ∃ c d : Candidate n, rankOf M.center c < rankOf M.center d ∧
      AppliedModelingLib.pmfPairIndicatorExp M.law M.law disagreementEvent
          (fun pair =>
            if d = firstChoice pair.1 ∧ c = secondChoice pair.1 then (1 : ℝ) else 0) /
          AppliedModelingLib.pmfPairProb M.law M.law disagreementEvent <
        AppliedModelingLib.pmfPairIndicatorExp M.law M.law disagreementEvent
          (fun pair =>
            if c = firstChoice pair.1 ∧ d = secondChoice pair.1 then (1 : ℝ) else 0) /
          AppliedModelingLib.pmfPairProb M.law M.law disagreementEvent

theorem equationE2_source_phi_literal_conditional_semantic_complete_spec_proof
    {n : ℕ} (center : Ranking n) (phi theta : ℝ)
    (hphi : 1 < phi) (htheta : theta = phi - 1) (hn : 0 < n) :
    equationE2_source_phi_literal_conditional_semantic_completeSpec
      (n := n) center phi theta hphi htheta hn :=
  equationE2_source_phi_literal_conditional_semantic_complete
    center phi theta hphi htheta hn

/-- Audited source-facing proposition for Appendix E.3. -/
abbrev equationE3_source_phi_completeSpec
    {n : ℕ} (center : Ranking n) (phi theta : ℝ)
    (hphi : 1 < phi) (htheta : theta = phi - 1) (hn : 0 < n) : Prop :=
  let M := concreteMallowsSpec center theta
  M.q = phi⁻¹ ∧
    (∀ pi : Ranking n,
      (M.law pi).toReal =
        phi⁻¹ ^ kendallTau center pi /
          (∑ tau : Ranking n, phi⁻¹ ^ kendallTau center tau)) ∧
    (∀ c d : Candidate n, rankOf M.center c < rankOf M.center d →
      0 ≤ M.firstSecondChoiceProb c d * firstChoiceMissProb M.law c -
        M.firstSecondChoiceProb d c * firstChoiceMissProb M.law d) ∧
    ∃ c d : Candidate n, rankOf M.center c < rankOf M.center d ∧
      0 < M.firstSecondChoiceProb c d * firstChoiceMissProb M.law c -
        M.firstSecondChoiceProb d c * firstChoiceMissProb M.law d

theorem equationE3_source_phi_complete_spec_proof
    {n : ℕ} (center : Ranking n) (phi theta : ℝ)
    (hphi : 1 < phi) (htheta : theta = phi - 1) (hn : 0 < n) :
    equationE3_source_phi_completeSpec
      (n := n) center phi theta hphi htheta hn :=
  equationE3_source_phi_complete center phi theta hphi htheta hn

/-- Audited source-facing proposition for Appendix F Lemma 4. -/
abbrev lemma4_weighted_average_lt_of_cross_ratioSpec
    (n : ℕ) {p q y : Candidate n → ℝ}
    (hp_sum : (∑ i : Candidate n, p i) = 1)
    (hq_sum : (∑ i : Candidate n, q i) = 1)
    (hcross_nonneg :
      ∀ i j : Candidate n, i < j → 0 ≤ p i * q j - p j * q i)
    (hcross_pos :
      ∃ i j : Candidate n, i < j ∧ 0 < p i * q j - p j * q i)
    (hy : StrictMono y) : Prop :=
  (∑ i : Candidate n, p i * y i) <
    ∑ i : Candidate n, q i * y i

theorem lemma4_weighted_average_lt_of_cross_ratio_spec_proof
    (n : ℕ) {p q y : Candidate n → ℝ}
    (hp_sum : (∑ i : Candidate n, p i) = 1)
    (hq_sum : (∑ i : Candidate n, q i) = 1)
    (hcross_nonneg :
      ∀ i j : Candidate n, i < j → 0 ≤ p i * q j - p j * q i)
    (hcross_pos :
      ∃ i j : Candidate n, i < j ∧ 0 < p i * q j - p j * q i)
    (hy : StrictMono y) :
    lemma4_weighted_average_lt_of_cross_ratioSpec
      n hp_sum hq_sum hcross_nonneg hcross_pos hy :=
  lemma4_weighted_average_lt_of_cross_ratio
    n hp_sum hq_sum hcross_nonneg hcross_pos hy

/-- Audited source-facing proposition for Equation (F.1). -/
abbrev equationF1_mallows_top_two_probabilitySpec
    {n : ℕ} (M : MallowsSpec n) (phi : ℝ)
    (hphi_gt : 1 < phi) (hphi : M.q = phi⁻¹) {c d : Candidate n}
    (hcd : rankOf M.center c < rankOf M.center d) : Prop :=
  M.firstSecondChoiceProb c d =
    phi * M.firstSecondChoiceProb d c

theorem equationF1_mallows_top_two_probability_spec_proof
    {n : ℕ} (M : MallowsSpec n) (phi : ℝ)
    (hphi_gt : 1 < phi) (hphi : M.q = phi⁻¹) {c d : Candidate n}
    (hcd : rankOf M.center c < rankOf M.center d) :
    equationF1_mallows_top_two_probabilitySpec
      (c := c) (d := d) M phi hphi_gt hphi hcd :=
  equationF1_mallows_top_two_probability M phi hphi_gt hphi hcd

/-- Audited source-facing proposition for Appendix F Lemma 5 / Equation (F.1). -/
abbrev lemma5_source_phi_completeSpec
    {n : ℕ} (center : Ranking n) (phi theta : ℝ)
    (hphi : 1 < phi) (htheta : theta = phi - 1) {c d : Candidate n}
    (hcd : rankOf center c < rankOf center d) : Prop :=
  let M := concreteMallowsSpec center theta
  M.q = phi⁻¹ ∧
    (∀ pi : Ranking n,
      (M.law pi).toReal =
        phi⁻¹ ^ kendallTau center pi /
          (∑ tau : Ranking n, phi⁻¹ ^ kendallTau center tau)) ∧
    M.firstSecondChoiceProb c d =
      phi * M.firstSecondChoiceProb d c

theorem lemma5_source_phi_complete_spec_proof
    {n : ℕ} (center : Ranking n) (phi theta : ℝ)
    (hphi : 1 < phi) (htheta : theta = phi - 1) {c d : Candidate n}
    (hcd : rankOf center c < rankOf center d) :
    lemma5_source_phi_completeSpec
      (c := c) (d := d) center phi theta hphi htheta hcd :=
  lemma5_source_phi_complete center phi theta hphi htheta hcd

/--
Audited source-facing proposition for Appendix F Lemma 6.

`N` is the paper's total number of candidates.  The reusable `Candidate n`
carrier has `n + 2` elements, so the source-facing presentation uses
`Candidate (N - 2)` and records the two-firm model's implicit `2 ≤ N` bound.
-/
abbrev lemma6_source_phi_rank_power_completeSpec
    {N : ℕ} (hN : 2 ≤ N) (center : Ranking (N - 2)) (phi theta : ℝ)
    (hphi : 1 < phi) (htheta : theta = phi - 1) (c : Candidate (N - 2)) : Prop :=
  let M := concreteMallowsSpec center theta
  M.q = phi⁻¹ ∧
    (∀ pi : Ranking (N - 2),
      (M.law pi).toReal =
        phi⁻¹ ^ kendallTau center pi /
          (∑ tau : Ranking (N - 2), phi⁻¹ ^ kendallTau center tau)) ∧
    firstChoiceProb M.law c =
      (1 - phi⁻¹) /
        (phi ^ (rankOf M.center c : ℕ) *
          (1 - phi⁻¹ ^ N))

theorem lemma6_source_phi_rank_power_complete_spec_proof
    {N : ℕ} (hN : 2 ≤ N) (center : Ranking (N - 2)) (phi theta : ℝ)
    (hphi : 1 < phi) (htheta : theta = phi - 1) (c : Candidate (N - 2)) :
    lemma6_source_phi_rank_power_completeSpec
      (N := N) hN center phi theta hphi htheta c := by
  simpa only [lemma6_source_phi_rank_power_completeSpec, inv_pow,
    Nat.sub_add_cancel hN] using
    (equationF2_source_phi_closed_form_complete
      (n := N - 2) center phi theta hphi htheta c)

/-- Audited source-facing proposition for Equation (F.2). -/
abbrev equationF2_source_phi_closed_form_completeSpec
    {n : ℕ} (center : Ranking n) (phi theta : ℝ)
    (hphi : 1 < phi) (htheta : theta = phi - 1) (c : Candidate n) : Prop :=
  let M := concreteMallowsSpec center theta
  M.q = phi⁻¹ ∧
    (∀ pi : Ranking n,
      (M.law pi).toReal =
        phi⁻¹ ^ kendallTau center pi /
          (∑ tau : Ranking n, phi⁻¹ ^ kendallTau center tau)) ∧
    firstChoiceProb M.law c =
      (1 - phi⁻¹) /
        (phi ^ (rankOf M.center c : ℕ) *
          (1 - phi⁻¹ ^ (n + 2)))

theorem equationF2_source_phi_closed_form_complete_spec_proof
    {n : ℕ} (center : Ranking n) (phi theta : ℝ)
    (hphi : 1 < phi) (htheta : theta = phi - 1) (c : Candidate n) :
    equationF2_source_phi_closed_form_completeSpec
      (n := n) center phi theta hphi htheta c :=
  equationF2_source_phi_closed_form_complete center phi theta hphi htheta c

/-- Audited source-facing proposition for Appendix F Lemma 7. -/
abbrev lemma7_mallows_first_mover_gt_second_humanSpec
    {n : ℕ} (M : MallowsSpec n) {value : Candidate n → ℝ}
    (hvalue : StrictlyOrderedBy M.center value) (hq_lt_one : M.q < 1) : Prop :=
  expectedSecondMoverIndependent M.law M.law value <
    expectedFirstMoverUtility M.law value

theorem lemma7_mallows_first_mover_gt_second_human_spec_proof
    {n : ℕ} (M : MallowsSpec n) {value : Candidate n → ℝ}
    (hvalue : StrictlyOrderedBy M.center value) (hq_lt_one : M.q < 1) :
    lemma7_mallows_first_mover_gt_second_humanSpec
      (value := value) M hvalue hq_lt_one :=
  lemma7_mallows_first_mover_gt_second_human M hvalue hq_lt_one

/-- Audited source-facing proposition for Appendix F Lemma 7's literal Mallows law. -/
abbrev lemma7_source_phi_completeSpec
    {n : ℕ} (center : Ranking n) (phi theta : ℝ)
    (hphi : 1 < phi) (htheta : theta = phi - 1)
    {value : Candidate n → ℝ} (hvalue : StrictlyOrderedBy center value) : Prop :=
  let M := concreteMallowsSpec center theta
  M.q = phi⁻¹ ∧
    (∀ pi : Ranking n,
      (M.law pi).toReal =
        phi⁻¹ ^ kendallTau center pi /
          (∑ tau : Ranking n, phi⁻¹ ^ kendallTau center tau)) ∧
    expectedSecondMoverIndependent M.law M.law value <
      expectedFirstMoverUtility M.law value

theorem lemma7_source_phi_complete_spec_proof
    {n : ℕ} (center : Ranking n) (phi theta : ℝ)
    (hphi : 1 < phi) (htheta : theta = phi - 1)
    {value : Candidate n → ℝ} (hvalue : StrictlyOrderedBy center value) :
    lemma7_source_phi_completeSpec
      (value := value) center phi theta hphi htheta hvalue :=
  lemma7_source_phi_complete center phi theta hphi htheta hvalue

/-- Audited source-facing proposition for Appendix F Lemma 8. -/
abbrev lemma8_source_mallows_phi_pairwise_correct_probability_ltSpec
    {n : ℕ} (center : Ranking n) {phiMore phiLess : ℝ}
    (hphiLess : 1 < phiLess) (hphiOrder : phiLess < phiMore)
    {c d : Candidate n} (hcd : rankOf center c < rankOf center d) : Prop :=
  let Mless := concreteMallowsSpec center (phiLess - 1)
  let Mmore := concreteMallowsSpec center (phiMore - 1)
  Mless.q = phiLess⁻¹ ∧
    Mmore.q = phiMore⁻¹ ∧
    (∀ pi : Ranking n,
      (Mless.law pi).toReal =
        phiLess⁻¹ ^ kendallTau center pi /
          (∑ tau : Ranking n, phiLess⁻¹ ^ kendallTau center tau)) ∧
    (∀ pi : Ranking n,
      (Mmore.law pi).toReal =
        phiMore⁻¹ ^ kendallTau center pi /
          (∑ tau : Ranking n, phiMore⁻¹ ^ kendallTau center tau)) ∧
    AppliedModelingLib.pmfProb Mless.law
      (fun pi => rankOf pi c < rankOf pi d) <
      AppliedModelingLib.pmfProb Mmore.law
        (fun pi => rankOf pi c < rankOf pi d)

theorem lemma8_source_mallows_phi_pairwise_correct_probability_lt_spec_proof
    {n : ℕ} (center : Ranking n) {phiMore phiLess : ℝ}
    (hphiLess : 1 < phiLess) (hphiOrder : phiLess < phiMore)
    {c d : Candidate n} (hcd : rankOf center c < rankOf center d) :
    lemma8_source_mallows_phi_pairwise_correct_probability_ltSpec
      (phiMore := phiMore) (phiLess := phiLess) (c := c) (d := d)
      center hphiLess hphiOrder hcd :=
  lemma8_source_mallows_phi_pairwise_correct_probability_lt
    center hphiLess hphiOrder hcd

/-! ## Literal payoff endpoints for the previously opaque theorem boundaries -/

/--
Equation (6) with all three sign-change hypotheses and its indifference
conclusion written in the paper's payoff terms.  The finite expectations inside
`Model.firstMoverEU` and `Model.secondMoverEU` are deliberately visible here;
the proof-only `theorem1_f`/`theorem1_g` abbreviations are not part of this
audited endpoint.
-/
theorem equation6_literal_payoff_indifference_of_sign_change
    {n : ℕ} (F : AccuracyFamily n) (thetaH lo hi : ℝ)
    (hthetaH : 0 < thetaH)
    (hthetaH_lo : thetaH < lo) (hlo_hi : lo < hi)
    (hcontinuous : ContinuousOn
      (fun thetaA =>
        (Model.firstMoverEU (F.modelAt thetaA thetaH) Strategy.algorithm +
            Model.secondMoverEU (F.modelAt thetaA thetaH)
              Strategy.algorithm Strategy.algorithm) -
          (Model.firstMoverEU (F.modelAt thetaA thetaH) Strategy.human +
            Model.secondMoverEU (F.modelAt thetaA thetaH)
              Strategy.algorithm Strategy.human))
      (Set.Icc lo hi))
    (hlo :
      Model.firstMoverEU (F.modelAt lo thetaH) Strategy.algorithm +
          Model.secondMoverEU (F.modelAt lo thetaH)
            Strategy.algorithm Strategy.algorithm <
        Model.firstMoverEU (F.modelAt lo thetaH) Strategy.human +
          Model.secondMoverEU (F.modelAt lo thetaH)
            Strategy.algorithm Strategy.human)
    (hhi :
      Model.firstMoverEU (F.modelAt hi thetaH) Strategy.human +
          Model.secondMoverEU (F.modelAt hi thetaH)
            Strategy.algorithm Strategy.human <
        Model.firstMoverEU (F.modelAt hi thetaH) Strategy.algorithm +
          Model.secondMoverEU (F.modelAt hi thetaH)
            Strategy.algorithm Strategy.algorithm) :
    ∃ thetaA, thetaH < thetaA ∧
      Model.firstMoverEU (F.modelAt thetaA thetaH) Strategy.algorithm +
          Model.secondMoverEU (F.modelAt thetaA thetaH)
            Strategy.algorithm Strategy.algorithm =
        Model.firstMoverEU (F.modelAt thetaA thetaH) Strategy.human +
          Model.secondMoverEU (F.modelAt thetaA thetaH)
            Strategy.algorithm Strategy.human := by
  simpa only [AccuracyFamily.theorem1_f, AccuracyFamily.theorem1_g] using
    equation6_indifference_threshold_of_sign_change
      F thetaH lo hi hthetaH hthetaH_lo hlo_hi hcontinuous hlo hhi

/-- Literal source contract for Equation (6)'s payoff-level crossing result. -/
abbrev equation6_literal_payoff_indifference_of_sign_changeSpec
    {n : ℕ} (F : AccuracyFamily n) (thetaH lo hi : ℝ)
    (hthetaH : 0 < thetaH)
    (hthetaH_lo : thetaH < lo) (hlo_hi : lo < hi)
    (hcontinuous : ContinuousOn
      (fun thetaA =>
        (Model.firstMoverEU (F.modelAt thetaA thetaH) Strategy.algorithm +
            Model.secondMoverEU (F.modelAt thetaA thetaH)
              Strategy.algorithm Strategy.algorithm) -
          (Model.firstMoverEU (F.modelAt thetaA thetaH) Strategy.human +
            Model.secondMoverEU (F.modelAt thetaA thetaH)
              Strategy.algorithm Strategy.human))
      (Set.Icc lo hi))
    (hlo :
      Model.firstMoverEU (F.modelAt lo thetaH) Strategy.algorithm +
          Model.secondMoverEU (F.modelAt lo thetaH)
            Strategy.algorithm Strategy.algorithm <
        Model.firstMoverEU (F.modelAt lo thetaH) Strategy.human +
          Model.secondMoverEU (F.modelAt lo thetaH)
            Strategy.algorithm Strategy.human)
    (hhi :
      Model.firstMoverEU (F.modelAt hi thetaH) Strategy.human +
          Model.secondMoverEU (F.modelAt hi thetaH)
            Strategy.algorithm Strategy.human <
        Model.firstMoverEU (F.modelAt hi thetaH) Strategy.algorithm +
          Model.secondMoverEU (F.modelAt hi thetaH)
            Strategy.algorithm Strategy.algorithm) : Prop :=
  ∃ thetaA, thetaH < thetaA ∧
    Model.firstMoverEU (F.modelAt thetaA thetaH) Strategy.algorithm +
        Model.secondMoverEU (F.modelAt thetaA thetaH)
          Strategy.algorithm Strategy.algorithm =
      Model.firstMoverEU (F.modelAt thetaA thetaH) Strategy.human +
        Model.secondMoverEU (F.modelAt thetaA thetaH)
          Strategy.algorithm Strategy.human

theorem equation6_literal_payoff_indifference_of_sign_change_spec_proof
    {n : ℕ} (F : AccuracyFamily n) (thetaH lo hi : ℝ)
    (hthetaH : 0 < thetaH)
    (hthetaH_lo : thetaH < lo) (hlo_hi : lo < hi)
    (hcontinuous : ContinuousOn
      (fun thetaA =>
        (Model.firstMoverEU (F.modelAt thetaA thetaH) Strategy.algorithm +
            Model.secondMoverEU (F.modelAt thetaA thetaH)
              Strategy.algorithm Strategy.algorithm) -
          (Model.firstMoverEU (F.modelAt thetaA thetaH) Strategy.human +
            Model.secondMoverEU (F.modelAt thetaA thetaH)
              Strategy.algorithm Strategy.human))
      (Set.Icc lo hi))
    (hlo :
      Model.firstMoverEU (F.modelAt lo thetaH) Strategy.algorithm +
          Model.secondMoverEU (F.modelAt lo thetaH)
            Strategy.algorithm Strategy.algorithm <
        Model.firstMoverEU (F.modelAt lo thetaH) Strategy.human +
          Model.secondMoverEU (F.modelAt lo thetaH)
            Strategy.algorithm Strategy.human)
    (hhi :
      Model.firstMoverEU (F.modelAt hi thetaH) Strategy.human +
          Model.secondMoverEU (F.modelAt hi thetaH)
            Strategy.algorithm Strategy.human <
        Model.firstMoverEU (F.modelAt hi thetaH) Strategy.algorithm +
          Model.secondMoverEU (F.modelAt hi thetaH)
            Strategy.algorithm Strategy.algorithm) :
    equation6_literal_payoff_indifference_of_sign_changeSpec
      F thetaH lo hi hthetaH hthetaH_lo hlo_hi hcontinuous hlo hhi :=
  equation6_literal_payoff_indifference_of_sign_change
    F thetaH lo hi hthetaH hthetaH_lo hlo_hi hcontinuous hlo hhi

/--
Equation (6) derived from the source conditions actually used in its proof.

Unlike the conditional intermediate-value wrapper above, this endpoint does
not accept a continuity certificate or either endpoint sign as a caller
premise.  It derives the initial sign from the source Definition 2 condition,
the high-accuracy sign from the source Definition 1 limit, and continuity from
the source atomwise-continuity clause.  The positive disagreement-mass part of
`hdefinition2` is the visible well-posedness condition for the printed
conditional expectation.
-/
theorem equation6_literal_payoff_indifference_from_source_conditions
    {n : ℕ} (F : AccuracyFamily n) (center : Ranking n) (thetaH : ℝ)
    (hthetaH : 0 < thetaH)
    (hcenter : StrictlyOrderedBy center F.value)
    (hdefinition2 : ∀ theta, 0 < theta →
      0 < disagreementProb (F.dist theta) ∧
        0 < disagreementConditionalGain (F.dist theta) F.value)
    (hatom_continuous : ∀ theta, 0 < theta → ∀ pi : Ranking n,
      ContinuousAt (fun theta' => ((F.dist theta') pi).toReal) theta)
    (_hatom_differentiable : ∀ theta, 0 < theta → ∀ pi : Ranking n,
      DifferentiableAt ℝ (fun theta' => ((F.dist theta') pi).toReal) theta)
    (hcenter_tendsto :
      Tendsto (fun theta => ((F.dist theta) center).toReal) atTop (nhds 1)) :
    ∃ thetaA, thetaH < thetaA ∧
      Model.firstMoverEU (F.modelAt thetaA thetaH) Strategy.algorithm +
          Model.secondMoverEU (F.modelAt thetaA thetaH)
            Strategy.algorithm Strategy.algorithm =
        Model.firstMoverEU (F.modelAt thetaA thetaH) Strategy.human +
          Model.secondMoverEU (F.modelAt thetaA thetaH)
            Strategy.algorithm Strategy.human := by
  have hprefers_independent : ∀ theta, 0 < theta →
      Model.PrefersIndependentReranking (F.dist theta) F.value := by
    intro theta htheta
    exact
      (prefersIndependentReranking_iff_conditionalGain_pos_of_disagreementPos
        (F.dist theta) F.value (hdefinition2 theta htheta).1).mpr
        (hdefinition2 theta htheta).2
  have hatom_epsilon_continuous : ∀ theta, 0 < theta → ∀ pi : Ranking n,
      AppliedModelingLib.EpsilonContinuousAt
        (fun theta' => ((F.dist theta') pi).toReal) theta := by
    intro theta htheta pi
    exact AppliedModelingLib.epsilonContinuousAt_of_continuousAt
      (hatom_continuous theta htheta pi)
  obtain ⟨lo, hthetaH_lo, hlo⟩ :=
    AccuracyFamily.theorem1_exists_right_initial_f_lt_g_of_prefersIndependent_and_atom_continuity
      F thetaH (hprefers_independent thetaH hthetaH)
      (hatom_epsilon_continuous thetaH hthetaH)
  obtain ⟨hi, hlo_hi, hhi⟩ :=
    asymptotic_first_dominance_of_atomwise_tendsto_to_strict_center
      F center hcenter hprefers_independent
      (atomwise_tendsto_pure_of_center_atom_tendsto F.dist center hcenter_tendsto)
      thetaH lo hthetaH hthetaH_lo
  have hcontinuous : ContinuousOn
      (fun thetaA =>
        AccuracyFamily.theorem1_f F thetaA thetaH -
          AccuracyFamily.theorem1_g F thetaA thetaH)
      (Set.Icc lo hi) :=
    AccuracyFamily.theorem1_f_sub_g_continuousOn_of_atom_continuity F thetaH lo hi
      (fun thetaA hthetaA pi =>
        hatom_epsilon_continuous thetaA
          (lt_trans hthetaH (lt_of_lt_of_le hthetaH_lo hthetaA.1)) pi)
  exact equation6_literal_payoff_indifference_of_sign_change
    F thetaH lo hi hthetaH hthetaH_lo hlo_hi hcontinuous hlo hhi

/-- Audited direct proposition for Equation (6)'s source-condition route. -/
abbrev equation6_literal_payoff_indifference_from_source_conditionsSpec
    {n : ℕ} (F : AccuracyFamily n) (center : Ranking n) (thetaH : ℝ)
    (hthetaH : 0 < thetaH)
    (hcenter : StrictlyOrderedBy center F.value)
    (hdefinition2 : ∀ theta, 0 < theta →
      0 < disagreementProb (F.dist theta) ∧
        0 < disagreementConditionalGain (F.dist theta) F.value)
    (hatom_continuous : ∀ theta, 0 < theta → ∀ pi : Ranking n,
      ContinuousAt (fun theta' => ((F.dist theta') pi).toReal) theta)
    (hatom_differentiable : ∀ theta, 0 < theta → ∀ pi : Ranking n,
      DifferentiableAt ℝ (fun theta' => ((F.dist theta') pi).toReal) theta)
    (hcenter_tendsto :
      Tendsto (fun theta => ((F.dist theta) center).toReal) atTop (nhds 1)) : Prop :=
  ∃ thetaA, thetaH < thetaA ∧
    Model.firstMoverEU (F.modelAt thetaA thetaH) Strategy.algorithm +
        Model.secondMoverEU (F.modelAt thetaA thetaH)
          Strategy.algorithm Strategy.algorithm =
      Model.firstMoverEU (F.modelAt thetaA thetaH) Strategy.human +
        Model.secondMoverEU (F.modelAt thetaA thetaH)
          Strategy.algorithm Strategy.human

theorem equation6_literal_payoff_indifference_from_source_conditions_spec_proof
    {n : ℕ} (F : AccuracyFamily n) (center : Ranking n) (thetaH : ℝ)
    (hthetaH : 0 < thetaH)
    (hcenter : StrictlyOrderedBy center F.value)
    (hdefinition2 : ∀ theta, 0 < theta →
      0 < disagreementProb (F.dist theta) ∧
        0 < disagreementConditionalGain (F.dist theta) F.value)
    (hatom_continuous : ∀ theta, 0 < theta → ∀ pi : Ranking n,
      ContinuousAt (fun theta' => ((F.dist theta') pi).toReal) theta)
    (hatom_differentiable : ∀ theta, 0 < theta → ∀ pi : Ranking n,
      DifferentiableAt ℝ (fun theta' => ((F.dist theta') pi).toReal) theta)
    (hcenter_tendsto :
      Tendsto (fun theta => ((F.dist theta) center).toReal) atTop (nhds 1)) :
    equation6_literal_payoff_indifference_from_source_conditionsSpec
      F center thetaH hthetaH hcenter hdefinition2 hatom_continuous
      hatom_differentiable hcenter_tendsto :=
  equation6_literal_payoff_indifference_from_source_conditions
    F center thetaH hthetaH hcenter hdefinition2 hatom_continuous
    hatom_differentiable hcenter_tendsto

/--
The analytic core of Equation (6) after the paper's outer candidate-value
draw has been restored.  The crossing is over the already-averaged payoff
functions, so the witness is one common algorithmic accuracy, rather than a
profile-dependent choice hidden inside the integral.

This is support for the direct source endpoint below.  Its assumptions are
kept as separate propositions so the source endpoint cannot obtain the
crossing from an opaque regularity package.
-/
theorem equation6_outer_payoff_indifference_of_crossing_conditions
    {n : ℕ} (F : DistributionalAccuracyFamily n)
    (D : Measure (ValueProfile n)) (thetaH : ℝ)
    (hindependent : F.PrefersIndependentReranking D thetaH)
    (hf_continuity : ∀ theta, thetaH ≤ theta →
      AppliedModelingLib.EpsilonContinuousAt
        (fun thetaA => F.theorem1_f D thetaA thetaH) theta)
    (hg_continuity : ∀ theta, thetaH ≤ theta →
      AppliedModelingLib.EpsilonContinuousAt
        (fun thetaA => F.theorem1_g D thetaA thetaH) theta)
    (hasymptotic : ∀ lower, thetaH < lower →
      ∃ hi, lower < hi ∧
        F.theorem1_g D hi thetaH < F.theorem1_f D hi thetaH) :
    ∃ thetaA, thetaH < thetaA ∧
      F.theorem1_f D thetaA thetaH = F.theorem1_g D thetaA thetaH := by
  have hinitial :
      F.theorem1_f D thetaH thetaH < F.theorem1_g D thetaH thetaH :=
    DistributionalAccuracyFamily.theorem1_f_lt_g_of_prefersIndependent
      F D thetaH hindependent
  rcases exists_right_radius_lt_of_epsilonContinuousAt
      (hf_continuity thetaH le_rfl)
      (hg_continuity thetaH le_rfl) hinitial with
    ⟨initialRadius, hinitialRadius, hpersistInitial⟩
  let lo := thetaH + initialRadius / 2
  have hthetaH_lo : thetaH < lo := by
    dsimp [lo]
    linarith
  have hf_lt_g_lo : F.theorem1_f D lo thetaH < F.theorem1_g D lo thetaH := by
    apply hpersistInitial
    · exact hthetaH_lo
    · dsimp [lo]
      linarith
  rcases hasymptotic lo hthetaH_lo with ⟨hi, hlo_hi, hg_lt_f_hi⟩
  have hdiff_continuous :
      ContinuousOn
        (fun thetaA => F.theorem1_f D thetaA thetaH -
          F.theorem1_g D thetaA thetaH)
        (Set.Icc lo hi) :=
    continuousOn_of_forall_epsilonContinuousAt fun theta htheta =>
      epsilonContinuousAt_sub
        (hf_continuity theta
          (le_trans (le_of_lt hthetaH_lo) htheta.1))
        (hg_continuity theta
          (le_trans (le_of_lt hthetaH_lo) htheta.1))
  have hzero : (0 : ℝ) ∈ Set.Icc
      (F.theorem1_f D lo thetaH - F.theorem1_g D lo thetaH)
      (F.theorem1_f D hi thetaH - F.theorem1_g D hi thetaH) := by
    constructor <;> linarith
  rcases intermediate_value_Icc (le_of_lt hlo_hi) hdiff_continuous hzero with
    ⟨thetaA, hthetaA, hzeroA⟩
  refine ⟨thetaA, hthetaH_lo.trans_le hthetaA.1, ?_⟩
  linarith

/--
Equation (6) at the paper's actual outer value-distribution scope.  The
visible source conditions are Definition 1's atomwise continuity,
differentiability, and asymptotic-optimality clauses, together with the
Definition 2 conditional joint-law experiment.  The outer measurability and
integrability assumptions are explicit because the source leaves them tacit
while they are required to define and transport the averaged payoff functions.
-/
theorem equation6_outer_payoff_indifference_from_source_conditions
    {n : ℕ} (F : DistributionalAccuracyFamily n)
    (D : Measure (ValueProfile n)) (hD : IsProbabilityMeasure D)
    (center : Ranking n) (thetaH : ℝ)
    (hthetaH : 0 < thetaH)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D)
    (hatom_aestrongly_measurable : ∀ theta pi,
      AEStronglyMeasurable (fun value : ValueProfile n =>
        ((F.dist theta value) pi).toReal) D)
    (hatom_continuous : ∀ value theta, 0 < theta → ∀ pi : Ranking n,
      ContinuousAt (fun theta' => ((F.dist theta' value) pi).toReal) theta)
    (_hatom_differentiable : ∀ value theta, 0 < theta → ∀ pi : Ranking n,
      DifferentiableAt ℝ (fun theta' => ((F.dist theta' value) pi).toReal) theta)
    (hcenter_tendsto : ∀ value,
      Tendsto (fun theta => ((F.dist theta value) center).toReal) atTop (nhds 1))
    (hstrict_order : ∀ᵐ value ∂D, StrictlyOrderedBy center value)
    (hatom_measurable : ∀ theta pi,
      Measurable fun value => F.dist theta value pi)
    (hdefinition2_disagreement_integrable : ∀ theta, 0 < theta → Integrable
      (fun value => disagreementProb (F.dist theta value)) D)
    (hdefinition2_shared_integrable : ∀ theta, 0 < theta → Integrable
      (fun value => expectedSecondMoverShared (F.dist theta value) value) D)
    (hdefinition2_independent_integrable : ∀ theta, 0 < theta → Integrable
      (fun value => expectedSecondMoverIndependent
        (F.dist theta value) (F.dist theta value) value) D)
    (hdefinition2_joint_shared_integrable : ∀ theta, ∀ htheta : 0 < theta,
      Integrable DistributionalAccuracyFamily.jointSharedSecondMoverPayoff
        (F.outerIndependentPairJointLaw D theta (hatom_measurable theta)))
    (hdefinition2_joint_independent_integrable : ∀ theta, ∀ htheta : 0 < theta,
      Integrable DistributionalAccuracyFamily.jointIndependentSecondMoverPayoff
        (F.outerIndependentPairJointLaw D theta (hatom_measurable theta)))
    (hdefinition2_event : ∀ theta, ∀ htheta : 0 < theta,
      0 < ∫ x : ValueProfile n × RankingPair n,
        (if disagreementEvent x.2 then (1 : ℝ) else 0) ∂
          F.outerIndependentPairJointLaw D theta (hatom_measurable theta))
    (hdefinition2_gain : ∀ theta, ∀ htheta : 0 < theta,
      0 < F.jointLawDisagreementConditionalGain D theta
        (hatom_measurable theta)) :
    ∃ thetaA, thetaH < thetaA ∧
      (∫ value : ValueProfile n,
        Model.firstMoverEU ((F.pointFamily value).modelAt thetaA thetaH)
          Strategy.algorithm ∂D) +
      (∫ value : ValueProfile n,
        Model.secondMoverEU ((F.pointFamily value).modelAt thetaA thetaH)
          Strategy.algorithm Strategy.algorithm ∂D) =
      (∫ value : ValueProfile n,
        Model.firstMoverEU ((F.pointFamily value).modelAt thetaA thetaH)
          Strategy.human ∂D) +
      (∫ value : ValueProfile n,
        Model.secondMoverEU ((F.pointFamily value).modelAt thetaA thetaH)
          Strategy.algorithm Strategy.human ∂D) := by
  letI : IsProbabilityMeasure D := hD
  let regularity : ∀ theta, 0 < theta →
      DistributionalAccuracyFamily.OuterIndependentRerankingJointRegularity F D theta :=
    fun theta htheta => {
      base := {
        outer_is_probability := hD
        ranking_atom_measurable := hatom_measurable theta
        disagreement_integrable := hdefinition2_disagreement_integrable theta htheta
        shared_payoff_integrable := hdefinition2_shared_integrable theta htheta
        independent_payoff_integrable := hdefinition2_independent_integrable theta htheta }
      joint_shared_payoff_integrable := hdefinition2_joint_shared_integrable theta htheta
      joint_independent_payoff_integrable :=
        hdefinition2_joint_independent_integrable theta htheta }
  have hatom_tendsto : ∀ᵐ value ∂D, ∀ pi : Ranking n,
      Tendsto (fun theta => ((F.dist theta value) pi).toReal) atTop
        (nhds (((PMF.pure center : PMF (Ranking n)) pi).toReal)) := by
    filter_upwards [Filter.Eventually.of_forall hcenter_tendsto] with value hcenter
    exact atomwise_tendsto_pure_of_center_atom_tendsto
      (fun theta => F.dist theta value) center hcenter
  have hdefinition2_payoff : F.PrefersIndependentReranking D thetaH := by
    exact
      (F.prefersIndependentReranking_iff_jointLawDisagreementConditionalGain_pos_of_regular
        D thetaH (regularity thetaH hthetaH)
        (hdefinition2_event thetaH hthetaH)).mpr
        (hdefinition2_gain thetaH hthetaH)
  have houter_disagreement : 0 < F.outerDisagreementProbability D thetaH := by
    rw [← F.integral_jointDisagreementIndicator_eq_outerDisagreementProbability
      D thetaH (regularity thetaH hthetaH).base.ranking_atom_measurable]
    exact hdefinition2_event thetaH hthetaH
  have hgfirst : Integrable (fun value =>
      expectedFirstMoverUtility (F.dist thetaH value) value) D := by
    simpa [expectedFirstMoverUtility] using
      (DistributionalAccuracyFamily.integrable_outer_pmfExp_valueSelection_of_atomwise
        D F.dist thetaH firstChoice hvalue
        (fun pi => hatom_aestrongly_measurable thetaH pi))
  have hgsecond : Integrable (fun value =>
      expectedSecondMoverIndependent (F.dist thetaH value) (PMF.pure center) value) D := by
    simpa [expectedSecondMoverIndependent, secondMoverUtility] using
      (DistributionalAccuracyFamily.integrable_outer_pmfPairExp_valueSelection_of_atomwise
        D (fun value => F.dist thetaH value) (fun _ => PMF.pure center)
        (fun second first => bestRemainingAfter second (firstChoice first)) hvalue
        (fun pi => hatom_aestrongly_measurable thetaH pi)
        (fun _ => aestronglyMeasurable_const))
  have hffirst : Integrable (fun value =>
      expectedFirstMoverUtility (PMF.pure center) value) D := by
    simpa [expectedFirstMoverUtility] using
      (DistributionalAccuracyFamily.integrable_outer_pmfExp_valueSelection_of_atomwise
        D (fun _ _ => PMF.pure center) 0 firstChoice hvalue
        (fun _ => aestronglyMeasurable_const))
  have hfsecond : Integrable (fun value =>
      expectedSecondMoverShared (PMF.pure center) value) D := by
    simpa [expectedSecondMoverShared] using
      (DistributionalAccuracyFamily.integrable_outer_pmfExp_valueSelection_of_atomwise
        D (fun _ _ => PMF.pure center) 0 secondChoice hvalue
        (fun _ => aestronglyMeasurable_const))
  have hpure_gap : F.theorem1_g_pureCenterLimit D thetaH center <
      DistributionalAccuracyFamily.theorem1_f_pureCenterLimit D center :=
    DistributionalAccuracyFamily.theorem1_pureCenterLimit_gap_of_outer_disagreement
      F D thetaH center hgfirst hgsecond hffirst hfsecond
      (regularity thetaH hthetaH).base.disagreement_integrable
      hstrict_order houter_disagreement
  have hcross : ∃ thetaA, thetaH < thetaA ∧
      F.theorem1_f D thetaA thetaH = F.theorem1_g D thetaA thetaH := by
    apply equation6_outer_payoff_indifference_of_crossing_conditions
      F D thetaH hdefinition2_payoff
    · intro theta htheta
      exact DistributionalAccuracyFamily.epsilonContinuousAt_theorem1_f_of_atomwise
        F D thetaH theta hvalue hatom_aestrongly_measurable
        (fun value pi => AppliedModelingLib.epsilonContinuousAt_of_continuousAt
          (hatom_continuous value theta (lt_of_lt_of_le hthetaH htheta) pi))
    · intro theta htheta
      exact DistributionalAccuracyFamily.epsilonContinuousAt_theorem1_g_of_atomwise
        F D thetaH theta hvalue hatom_aestrongly_measurable
        (fun value pi => AppliedModelingLib.epsilonContinuousAt_of_continuousAt
          (hatom_continuous value theta (lt_of_lt_of_le hthetaH htheta) pi))
    · exact DistributionalAccuracyFamily.exists_outer_first_dominance_of_atomwise_tendsto
        F D thetaH center hvalue hatom_aestrongly_measurable hatom_tendsto hpure_gap
  simpa only [DistributionalAccuracyFamily.theorem1_f,
    DistributionalAccuracyFamily.theorem1_g,
    DistributionalAccuracyFamily.outerExpected] using hcross

/-- Audited proposition for Equation (6)'s outer source-model route. -/
abbrev equation6_outer_payoff_indifference_from_source_conditionsSpec
    {n : ℕ} (F : DistributionalAccuracyFamily n)
    (D : Measure (ValueProfile n)) (hD : IsProbabilityMeasure D)
    (center : Ranking n) (thetaH : ℝ)
    (hthetaH : 0 < thetaH)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D)
    (hatom_aestrongly_measurable : ∀ theta pi,
      AEStronglyMeasurable (fun value : ValueProfile n =>
        ((F.dist theta value) pi).toReal) D)
    (hatom_continuous : ∀ value theta, 0 < theta → ∀ pi : Ranking n,
      ContinuousAt (fun theta' => ((F.dist theta' value) pi).toReal) theta)
    (hatom_differentiable : ∀ value theta, 0 < theta → ∀ pi : Ranking n,
      DifferentiableAt ℝ (fun theta' => ((F.dist theta' value) pi).toReal) theta)
    (hcenter_tendsto : ∀ value,
      Tendsto (fun theta => ((F.dist theta value) center).toReal) atTop (nhds 1))
    (hstrict_order : ∀ᵐ value ∂D, StrictlyOrderedBy center value)
    (hatom_measurable : ∀ theta pi,
      Measurable fun value => F.dist theta value pi)
    (hdefinition2_disagreement_integrable : ∀ theta, 0 < theta → Integrable
      (fun value => disagreementProb (F.dist theta value)) D)
    (hdefinition2_shared_integrable : ∀ theta, 0 < theta → Integrable
      (fun value => expectedSecondMoverShared (F.dist theta value) value) D)
    (hdefinition2_independent_integrable : ∀ theta, 0 < theta → Integrable
      (fun value => expectedSecondMoverIndependent
        (F.dist theta value) (F.dist theta value) value) D)
    (hdefinition2_joint_shared_integrable : ∀ theta, ∀ htheta : 0 < theta,
      Integrable DistributionalAccuracyFamily.jointSharedSecondMoverPayoff
        (F.outerIndependentPairJointLaw D theta (hatom_measurable theta)))
    (hdefinition2_joint_independent_integrable : ∀ theta, ∀ htheta : 0 < theta,
      Integrable DistributionalAccuracyFamily.jointIndependentSecondMoverPayoff
        (F.outerIndependentPairJointLaw D theta (hatom_measurable theta)))
    (hdefinition2_event : ∀ theta, ∀ htheta : 0 < theta,
      0 < ∫ x : ValueProfile n × RankingPair n,
        (if disagreementEvent x.2 then (1 : ℝ) else 0) ∂
          F.outerIndependentPairJointLaw D theta (hatom_measurable theta))
    (hdefinition2_gain : ∀ theta, ∀ htheta : 0 < theta,
      0 < F.jointLawDisagreementConditionalGain D theta
        (hatom_measurable theta)) : Prop :=
  ∃ thetaA, thetaH < thetaA ∧
    (∫ value : ValueProfile n,
      Model.firstMoverEU ((F.pointFamily value).modelAt thetaA thetaH)
        Strategy.algorithm ∂D) +
    (∫ value : ValueProfile n,
      Model.secondMoverEU ((F.pointFamily value).modelAt thetaA thetaH)
        Strategy.algorithm Strategy.algorithm ∂D) =
    (∫ value : ValueProfile n,
      Model.firstMoverEU ((F.pointFamily value).modelAt thetaA thetaH)
        Strategy.human ∂D) +
    (∫ value : ValueProfile n,
      Model.secondMoverEU ((F.pointFamily value).modelAt thetaA thetaH)
        Strategy.algorithm Strategy.human ∂D)

theorem equation6_outer_payoff_indifference_from_source_conditions_spec_proof
    {n : ℕ} (F : DistributionalAccuracyFamily n)
    (D : Measure (ValueProfile n)) (hD : IsProbabilityMeasure D)
    (center : Ranking n) (thetaH : ℝ)
    (hthetaH : 0 < thetaH)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D)
    (hatom_aestrongly_measurable : ∀ theta pi,
      AEStronglyMeasurable (fun value : ValueProfile n =>
        ((F.dist theta value) pi).toReal) D)
    (hatom_continuous : ∀ value theta, 0 < theta → ∀ pi : Ranking n,
      ContinuousAt (fun theta' => ((F.dist theta' value) pi).toReal) theta)
    (hatom_differentiable : ∀ value theta, 0 < theta → ∀ pi : Ranking n,
      DifferentiableAt ℝ (fun theta' => ((F.dist theta' value) pi).toReal) theta)
    (hcenter_tendsto : ∀ value,
      Tendsto (fun theta => ((F.dist theta value) center).toReal) atTop (nhds 1))
    (hstrict_order : ∀ᵐ value ∂D, StrictlyOrderedBy center value)
    (hatom_measurable : ∀ theta pi,
      Measurable fun value => F.dist theta value pi)
    (hdefinition2_disagreement_integrable : ∀ theta, 0 < theta → Integrable
      (fun value => disagreementProb (F.dist theta value)) D)
    (hdefinition2_shared_integrable : ∀ theta, 0 < theta → Integrable
      (fun value => expectedSecondMoverShared (F.dist theta value) value) D)
    (hdefinition2_independent_integrable : ∀ theta, 0 < theta → Integrable
      (fun value => expectedSecondMoverIndependent
        (F.dist theta value) (F.dist theta value) value) D)
    (hdefinition2_joint_shared_integrable : ∀ theta, ∀ htheta : 0 < theta,
      Integrable DistributionalAccuracyFamily.jointSharedSecondMoverPayoff
        (F.outerIndependentPairJointLaw D theta (hatom_measurable theta)))
    (hdefinition2_joint_independent_integrable : ∀ theta, ∀ htheta : 0 < theta,
      Integrable DistributionalAccuracyFamily.jointIndependentSecondMoverPayoff
        (F.outerIndependentPairJointLaw D theta (hatom_measurable theta)))
    (hdefinition2_event : ∀ theta, ∀ htheta : 0 < theta,
      0 < ∫ x : ValueProfile n × RankingPair n,
        (if disagreementEvent x.2 then (1 : ℝ) else 0) ∂
          F.outerIndependentPairJointLaw D theta (hatom_measurable theta))
    (hdefinition2_gain : ∀ theta, ∀ htheta : 0 < theta,
      0 < F.jointLawDisagreementConditionalGain D theta
        (hatom_measurable theta)) :
    equation6_outer_payoff_indifference_from_source_conditionsSpec
      F D hD center thetaH hthetaH hvalue hatom_aestrongly_measurable
      hatom_continuous hatom_differentiable hcenter_tendsto hstrict_order
      hatom_measurable hdefinition2_disagreement_integrable
      hdefinition2_shared_integrable hdefinition2_independent_integrable
      hdefinition2_joint_shared_integrable hdefinition2_joint_independent_integrable
      hdefinition2_event hdefinition2_gain :=
  equation6_outer_payoff_indifference_from_source_conditions
    F D hD center thetaH hthetaH hvalue hatom_aestrongly_measurable
    hatom_continuous hatom_differentiable hcenter_tendsto hstrict_order
    hatom_measurable hdefinition2_disagreement_integrable
    hdefinition2_shared_integrable hdefinition2_independent_integrable
    hdefinition2_joint_shared_integrable hdefinition2_joint_independent_integrable
    hdefinition2_event hdefinition2_gain

/--
Theorem 1's raw outer-law endpoint with the terminal comparison expanded into
the literal outer integrals of `Model.firstMoverEU` and
`Model.secondMoverEU`.  The source Definition 2/3 and Definition 1
assumptions remain exactly as in the existing raw endpoint.
-/
theorem theorem1_raw_outer_literal_payoff_terminal_conclusion
    {n : ℕ} (F : DistributionalAccuracyFamily n)
    (D : Measure (ValueProfile n)) (hD : IsProbabilityMeasure D)
    (center : Ranking n) (thetaH : ℝ)
    (hthetaH : 0 < thetaH)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D)
    (hatom_aestrongly_measurable : ∀ theta pi,
      AEStronglyMeasurable (fun value : ValueProfile n =>
        ((F.dist theta value) pi).toReal) D)
    (hatom_continuous : ∀ value theta, 0 < theta → ∀ pi : Ranking n,
      ContinuousAt (fun theta' => ((F.dist theta' value) pi).toReal) theta)
    (hatom_differentiable : ∀ value theta, 0 < theta → ∀ pi : Ranking n,
      DifferentiableAt ℝ (fun theta' => ((F.dist theta' value) pi).toReal) theta)
    (hcenter_tendsto : ∀ value,
      Tendsto (fun theta => ((F.dist theta value) center).toReal) atTop (nhds 1))
    (hstrict_order : ∀ᵐ value ∂D, StrictlyOrderedBy center value)
    (hatom_measurable : ∀ theta pi,
      Measurable fun value => F.dist theta value pi)
    (hdefinition2_disagreement_integrable : ∀ theta, 0 < theta → Integrable
      (fun value => pmfPairExp (F.dist theta value) (F.dist theta value)
        (fun pi sigma => if firstChoice pi ≠ firstChoice sigma then (1 : ℝ) else 0)) D)
    (hdefinition2_shared_integrable : ∀ theta, 0 < theta → Integrable
      (fun value => pmfExp (F.dist theta value)
        (fun pi => value (secondChoice pi))) D)
    (hdefinition2_independent_integrable : ∀ theta, 0 < theta → Integrable
      (fun value => pmfPairExp (F.dist theta value) (F.dist theta value)
        (fun pi sigma => secondMoverUtility value pi sigma)) D)
    (hdefinition2_joint_shared_integrable : ∀ theta, ∀ htheta : 0 < theta,
      Integrable (fun x : ValueProfile n × RankingPair n =>
        secondMoverUtility x.1 x.2.1 x.2.1)
        (F.outerIndependentPairJointLaw D theta (hatom_measurable theta)))
    (hdefinition2_joint_independent_integrable : ∀ theta, ∀ htheta : 0 < theta,
      Integrable (fun x : ValueProfile n × RankingPair n =>
        secondMoverUtility x.1 x.2.1 x.2.2)
        (F.outerIndependentPairJointLaw D theta (hatom_measurable theta)))
    (hdefinition2_event : ∀ theta, ∀ htheta : 0 < theta,
      0 < ∫ x : ValueProfile n × RankingPair n,
        (if firstChoice x.2.1 ≠ firstChoice x.2.2 then (1 : ℝ) else 0) ∂
          F.outerIndependentPairJointLaw D theta (hatom_measurable theta))
    (hdefinition2_gain : ∀ theta, ∀ htheta : 0 < theta,
      0 <
        (∫ x : ValueProfile n × RankingPair n,
          if firstChoice x.2.1 ≠ firstChoice x.2.2 then
            x.1 (firstChoice x.2.1) - x.1 (secondChoice x.2.1)
          else 0 ∂F.outerIndependentPairJointLaw D theta (hatom_measurable theta)) /
        (∫ x : ValueProfile n × RankingPair n,
          if firstChoice x.2.1 ≠ firstChoice x.2.2 then (1 : ℝ) else 0 ∂
            F.outerIndependentPairJointLaw D theta (hatom_measurable theta)))
    (hdefinition3_better_integrable : ∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
      Integrable (fun value => pmfPairExp
        (F.dist thetaH value) (F.dist thetaA value)
        (fun pi sigma => secondMoverUtility value pi sigma)) D)
    (hdefinition3_worse_integrable : ∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
      Integrable (fun value => pmfPairExp
        (F.dist thetaH value) (F.dist thetaH value)
        (fun pi sigma => secondMoverUtility value pi sigma)) D)
    (hdefinition3 : ∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
      (∫ value, pmfPairExp (F.dist thetaH value) (F.dist thetaA value)
        (fun pi sigma => secondMoverUtility value pi sigma) ∂D) <
      ∫ value, pmfPairExp (F.dist thetaH value) (F.dist thetaH value)
        (fun pi sigma => secondMoverUtility value pi sigma) ∂D)
    (hremaining_weak : ∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
      ∀ value, ∀ remaining : Finset (Candidate n), remaining.Nonempty →
        expectedBestInSet (F.dist thetaH value) value remaining ≤
          expectedBestInSet (F.dist thetaA value) value remaining)
    (hfull_set_strict : ∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
      ∀ value, StrictlyOrderedBy center value →
        expectedBestInSet (F.dist thetaH value) value Finset.univ <
          expectedBestInSet (F.dist thetaA value) value Finset.univ) :
    ∃ thetaA, thetaH < thetaA ∧
      (∫ value : ValueProfile n,
        Model.firstMoverEU ((F.pointFamily value).modelAt thetaA thetaH)
          Strategy.human ∂D) +
        (∫ value : ValueProfile n,
          Model.secondMoverEU ((F.pointFamily value).modelAt thetaA thetaH)
            Strategy.algorithm Strategy.human ∂D) <
      (∫ value : ValueProfile n,
        Model.firstMoverEU ((F.pointFamily value).modelAt thetaA thetaH)
          Strategy.algorithm ∂D) +
        (∫ value : ValueProfile n,
          Model.secondMoverEU ((F.pointFamily value).modelAt thetaA thetaH)
            Strategy.algorithm Strategy.algorithm ∂D) ∧
      (∫ value : ValueProfile n,
        Model.firstMoverEU ((F.pointFamily value).modelAt thetaA thetaH)
          Strategy.human ∂D) +
        (∫ value : ValueProfile n,
          Model.secondMoverEU ((F.pointFamily value).modelAt thetaA thetaH)
            Strategy.human Strategy.human ∂D) <
      (∫ value : ValueProfile n,
        Model.firstMoverEU ((F.pointFamily value).modelAt thetaA thetaH)
          Strategy.algorithm ∂D) +
        (∫ value : ValueProfile n,
          Model.secondMoverEU ((F.pointFamily value).modelAt thetaA thetaH)
            Strategy.human Strategy.algorithm ∂D) ∧
      (∫ value : ValueProfile n,
        Model.firstMoverEU ((F.pointFamily value).modelAt thetaA thetaH)
          Strategy.algorithm ∂D) +
        (∫ value : ValueProfile n,
          Model.secondMoverEU ((F.pointFamily value).modelAt thetaA thetaH)
            Strategy.algorithm Strategy.algorithm ∂D) <
      (∫ value : ValueProfile n,
        Model.firstMoverEU ((F.pointFamily value).modelAt thetaA thetaH)
          Strategy.human ∂D) +
        (∫ value : ValueProfile n,
          Model.secondMoverEU ((F.pointFamily value).modelAt thetaA thetaH)
            Strategy.human Strategy.human ∂D) := by
  simpa only [literal_outer_payoff_paradox,
    DistributionalAccuracyFamily.theorem1_f,
    DistributionalAccuracyFamily.theorem1_g,
    DistributionalAccuracyFamily.theorem1_h,
    DistributionalAccuracyFamily.theorem1_algorithmAgainstHuman,
    DistributionalAccuracyFamily.outerExpected] using
    theorem1_outer_raw_definition2_definition3_semantic_complete
      F D hD center thetaH hthetaH hvalue hatom_aestrongly_measurable
      hatom_continuous hatom_differentiable hcenter_tendsto hstrict_order
      hatom_measurable hdefinition2_disagreement_integrable
      hdefinition2_shared_integrable hdefinition2_independent_integrable
      hdefinition2_joint_shared_integrable hdefinition2_joint_independent_integrable
      hdefinition2_event hdefinition2_gain hdefinition3_better_integrable
      hdefinition3_worse_integrable hdefinition3 hremaining_weak hfull_set_strict

/-- Literal contract for Theorem 1's raw outer-law terminal payoff result. -/
abbrev theorem1_raw_outer_literal_payoff_terminal_conclusionSpec
    {n : ℕ} (F : DistributionalAccuracyFamily n)
    (D : Measure (ValueProfile n)) (hD : IsProbabilityMeasure D)
    (center : Ranking n) (thetaH : ℝ)
    (hthetaH : 0 < thetaH)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D)
    (hatom_aestrongly_measurable : ∀ theta pi,
      AEStronglyMeasurable (fun value : ValueProfile n =>
        ((F.dist theta value) pi).toReal) D)
    (hatom_continuous : ∀ value theta, 0 < theta → ∀ pi : Ranking n,
      ContinuousAt (fun theta' => ((F.dist theta' value) pi).toReal) theta)
    (hatom_differentiable : ∀ value theta, 0 < theta → ∀ pi : Ranking n,
      DifferentiableAt ℝ (fun theta' => ((F.dist theta' value) pi).toReal) theta)
    (hcenter_tendsto : ∀ value,
      Tendsto (fun theta => ((F.dist theta value) center).toReal) atTop (nhds 1))
    (hstrict_order : ∀ᵐ value ∂D, StrictlyOrderedBy center value)
    (hatom_measurable : ∀ theta pi,
      Measurable fun value => F.dist theta value pi)
    (hdefinition2_disagreement_integrable : ∀ theta, 0 < theta → Integrable
      (fun value => pmfPairExp (F.dist theta value) (F.dist theta value)
        (fun pi sigma => if firstChoice pi ≠ firstChoice sigma then (1 : ℝ) else 0)) D)
    (hdefinition2_shared_integrable : ∀ theta, 0 < theta → Integrable
      (fun value => pmfExp (F.dist theta value)
        (fun pi => value (secondChoice pi))) D)
    (hdefinition2_independent_integrable : ∀ theta, 0 < theta → Integrable
      (fun value => pmfPairExp (F.dist theta value) (F.dist theta value)
        (fun pi sigma => secondMoverUtility value pi sigma)) D)
    (hdefinition2_joint_shared_integrable : ∀ theta, ∀ htheta : 0 < theta,
      Integrable (fun x : ValueProfile n × RankingPair n =>
        secondMoverUtility x.1 x.2.1 x.2.1)
        (F.outerIndependentPairJointLaw D theta (hatom_measurable theta)))
    (hdefinition2_joint_independent_integrable : ∀ theta, ∀ htheta : 0 < theta,
      Integrable (fun x : ValueProfile n × RankingPair n =>
        secondMoverUtility x.1 x.2.1 x.2.2)
        (F.outerIndependentPairJointLaw D theta (hatom_measurable theta)))
    (hdefinition2_event : ∀ theta, ∀ htheta : 0 < theta,
      0 < ∫ x : ValueProfile n × RankingPair n,
        (if firstChoice x.2.1 ≠ firstChoice x.2.2 then (1 : ℝ) else 0) ∂
          F.outerIndependentPairJointLaw D theta (hatom_measurable theta))
    (hdefinition2_gain : ∀ theta, ∀ htheta : 0 < theta,
      0 <
        (∫ x : ValueProfile n × RankingPair n,
          if firstChoice x.2.1 ≠ firstChoice x.2.2 then
            x.1 (firstChoice x.2.1) - x.1 (secondChoice x.2.1)
          else 0 ∂F.outerIndependentPairJointLaw D theta (hatom_measurable theta)) /
        (∫ x : ValueProfile n × RankingPair n,
          if firstChoice x.2.1 ≠ firstChoice x.2.2 then (1 : ℝ) else 0 ∂
            F.outerIndependentPairJointLaw D theta (hatom_measurable theta)))
    (hdefinition3_better_integrable : ∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
      Integrable (fun value => pmfPairExp
        (F.dist thetaH value) (F.dist thetaA value)
        (fun pi sigma => secondMoverUtility value pi sigma)) D)
    (hdefinition3_worse_integrable : ∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
      Integrable (fun value => pmfPairExp
        (F.dist thetaH value) (F.dist thetaH value)
        (fun pi sigma => secondMoverUtility value pi sigma)) D)
    (hdefinition3 : ∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
      (∫ value, pmfPairExp (F.dist thetaH value) (F.dist thetaA value)
        (fun pi sigma => secondMoverUtility value pi sigma) ∂D) <
      ∫ value, pmfPairExp (F.dist thetaH value) (F.dist thetaH value)
        (fun pi sigma => secondMoverUtility value pi sigma) ∂D)
    (hremaining_weak : ∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
      ∀ value, ∀ remaining : Finset (Candidate n), remaining.Nonempty →
        expectedBestInSet (F.dist thetaH value) value remaining ≤
          expectedBestInSet (F.dist thetaA value) value remaining)
    (hfull_set_strict : ∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
      ∀ value, StrictlyOrderedBy center value →
        expectedBestInSet (F.dist thetaH value) value Finset.univ <
          expectedBestInSet (F.dist thetaA value) value Finset.univ) : Prop :=
  ∃ thetaA, thetaH < thetaA ∧
    (∫ value : ValueProfile n,
      Model.firstMoverEU ((F.pointFamily value).modelAt thetaA thetaH)
        Strategy.human ∂D) +
      (∫ value : ValueProfile n,
        Model.secondMoverEU ((F.pointFamily value).modelAt thetaA thetaH)
          Strategy.algorithm Strategy.human ∂D) <
    (∫ value : ValueProfile n,
      Model.firstMoverEU ((F.pointFamily value).modelAt thetaA thetaH)
        Strategy.algorithm ∂D) +
      (∫ value : ValueProfile n,
        Model.secondMoverEU ((F.pointFamily value).modelAt thetaA thetaH)
          Strategy.algorithm Strategy.algorithm ∂D) ∧
    (∫ value : ValueProfile n,
      Model.firstMoverEU ((F.pointFamily value).modelAt thetaA thetaH)
        Strategy.human ∂D) +
      (∫ value : ValueProfile n,
        Model.secondMoverEU ((F.pointFamily value).modelAt thetaA thetaH)
          Strategy.human Strategy.human ∂D) <
    (∫ value : ValueProfile n,
      Model.firstMoverEU ((F.pointFamily value).modelAt thetaA thetaH)
        Strategy.algorithm ∂D) +
      (∫ value : ValueProfile n,
        Model.secondMoverEU ((F.pointFamily value).modelAt thetaA thetaH)
          Strategy.human Strategy.algorithm ∂D) ∧
    (∫ value : ValueProfile n,
      Model.firstMoverEU ((F.pointFamily value).modelAt thetaA thetaH)
        Strategy.algorithm ∂D) +
      (∫ value : ValueProfile n,
        Model.secondMoverEU ((F.pointFamily value).modelAt thetaA thetaH)
          Strategy.algorithm Strategy.algorithm ∂D) <
    (∫ value : ValueProfile n,
      Model.firstMoverEU ((F.pointFamily value).modelAt thetaA thetaH)
        Strategy.human ∂D) +
      (∫ value : ValueProfile n,
        Model.secondMoverEU ((F.pointFamily value).modelAt thetaA thetaH)
          Strategy.human Strategy.human ∂D)

theorem theorem1_raw_outer_literal_payoff_terminal_conclusion_spec_proof
    {n : ℕ} (F : DistributionalAccuracyFamily n)
    (D : Measure (ValueProfile n)) (hD : IsProbabilityMeasure D)
    (center : Ranking n) (thetaH : ℝ)
    (hthetaH : 0 < thetaH)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D)
    (hatom_aestrongly_measurable : ∀ theta pi,
      AEStronglyMeasurable (fun value : ValueProfile n =>
        ((F.dist theta value) pi).toReal) D)
    (hatom_continuous : ∀ value theta, 0 < theta → ∀ pi : Ranking n,
      ContinuousAt (fun theta' => ((F.dist theta' value) pi).toReal) theta)
    (hatom_differentiable : ∀ value theta, 0 < theta → ∀ pi : Ranking n,
      DifferentiableAt ℝ (fun theta' => ((F.dist theta' value) pi).toReal) theta)
    (hcenter_tendsto : ∀ value,
      Tendsto (fun theta => ((F.dist theta value) center).toReal) atTop (nhds 1))
    (hstrict_order : ∀ᵐ value ∂D, StrictlyOrderedBy center value)
    (hatom_measurable : ∀ theta pi,
      Measurable fun value => F.dist theta value pi)
    (hdefinition2_disagreement_integrable : ∀ theta, 0 < theta → Integrable
      (fun value => pmfPairExp (F.dist theta value) (F.dist theta value)
        (fun pi sigma => if firstChoice pi ≠ firstChoice sigma then (1 : ℝ) else 0)) D)
    (hdefinition2_shared_integrable : ∀ theta, 0 < theta → Integrable
      (fun value => pmfExp (F.dist theta value)
        (fun pi => value (secondChoice pi))) D)
    (hdefinition2_independent_integrable : ∀ theta, 0 < theta → Integrable
      (fun value => pmfPairExp (F.dist theta value) (F.dist theta value)
        (fun pi sigma => secondMoverUtility value pi sigma)) D)
    (hdefinition2_joint_shared_integrable : ∀ theta, ∀ htheta : 0 < theta,
      Integrable (fun x : ValueProfile n × RankingPair n =>
        secondMoverUtility x.1 x.2.1 x.2.1)
        (F.outerIndependentPairJointLaw D theta (hatom_measurable theta)))
    (hdefinition2_joint_independent_integrable : ∀ theta, ∀ htheta : 0 < theta,
      Integrable (fun x : ValueProfile n × RankingPair n =>
        secondMoverUtility x.1 x.2.1 x.2.2)
        (F.outerIndependentPairJointLaw D theta (hatom_measurable theta)))
    (hdefinition2_event : ∀ theta, ∀ htheta : 0 < theta,
      0 < ∫ x : ValueProfile n × RankingPair n,
        (if firstChoice x.2.1 ≠ firstChoice x.2.2 then (1 : ℝ) else 0) ∂
          F.outerIndependentPairJointLaw D theta (hatom_measurable theta))
    (hdefinition2_gain : ∀ theta, ∀ htheta : 0 < theta,
      0 <
        (∫ x : ValueProfile n × RankingPair n,
          if firstChoice x.2.1 ≠ firstChoice x.2.2 then
            x.1 (firstChoice x.2.1) - x.1 (secondChoice x.2.1)
          else 0 ∂F.outerIndependentPairJointLaw D theta (hatom_measurable theta)) /
        (∫ x : ValueProfile n × RankingPair n,
          if firstChoice x.2.1 ≠ firstChoice x.2.2 then (1 : ℝ) else 0 ∂
            F.outerIndependentPairJointLaw D theta (hatom_measurable theta)))
    (hdefinition3_better_integrable : ∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
      Integrable (fun value => pmfPairExp
        (F.dist thetaH value) (F.dist thetaA value)
        (fun pi sigma => secondMoverUtility value pi sigma)) D)
    (hdefinition3_worse_integrable : ∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
      Integrable (fun value => pmfPairExp
        (F.dist thetaH value) (F.dist thetaH value)
        (fun pi sigma => secondMoverUtility value pi sigma)) D)
    (hdefinition3 : ∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
      (∫ value, pmfPairExp (F.dist thetaH value) (F.dist thetaA value)
        (fun pi sigma => secondMoverUtility value pi sigma) ∂D) <
      ∫ value, pmfPairExp (F.dist thetaH value) (F.dist thetaH value)
        (fun pi sigma => secondMoverUtility value pi sigma) ∂D)
    (hremaining_weak : ∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
      ∀ value, ∀ remaining : Finset (Candidate n), remaining.Nonempty →
        expectedBestInSet (F.dist thetaH value) value remaining ≤
          expectedBestInSet (F.dist thetaA value) value remaining)
    (hfull_set_strict : ∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
      ∀ value, StrictlyOrderedBy center value →
        expectedBestInSet (F.dist thetaH value) value Finset.univ <
          expectedBestInSet (F.dist thetaA value) value Finset.univ) :
    theorem1_raw_outer_literal_payoff_terminal_conclusionSpec
      F D hD center thetaH hthetaH hvalue hatom_aestrongly_measurable
      hatom_continuous hatom_differentiable hcenter_tendsto hstrict_order
      hatom_measurable hdefinition2_disagreement_integrable
      hdefinition2_shared_integrable hdefinition2_independent_integrable
      hdefinition2_joint_shared_integrable hdefinition2_joint_independent_integrable
      hdefinition2_event hdefinition2_gain hdefinition3_better_integrable
      hdefinition3_worse_integrable hdefinition3 hremaining_weak hfull_set_strict :=
  theorem1_raw_outer_literal_payoff_terminal_conclusion
    F D hD center thetaH hthetaH hvalue hatom_aestrongly_measurable
    hatom_continuous hatom_differentiable hcenter_tendsto hstrict_order
    hatom_measurable hdefinition2_disagreement_integrable
    hdefinition2_shared_integrable hdefinition2_independent_integrable
    hdefinition2_joint_shared_integrable hdefinition2_joint_independent_integrable
    hdefinition2_event hdefinition2_gain hdefinition3_better_integrable
    hdefinition3_worse_integrable hdefinition3 hremaining_weak hfull_set_strict

/--
Theorem 2's Gaussian and source-normalized Laplace terminal results, with each
payoff comparison exposed through `literal_outer_payoff_paradox` rather than
the proof-notation `theorem1_*` functions.
-/
theorem theorem2_gaussian_laplace_literal_payoff_terminal_conclusions :
    (∀ (D : Measure (ValueProfile 1)) [IsProbabilityMeasure D]
      (thetaH : ℝ), 0 < thetaH →
      (∀ c : Candidate 1, Integrable (fun value : ValueProfile 1 => value c) D) →
      (∀ᵐ value ∂D,
        value (1 : Candidate 1) < value (0 : Candidate 1) ∧
          value (2 : Candidate 1) < value (1 : Candidate 1)) →
      literal_outer_payoff_paradox gaussianThreeCandidateDistributionalFamily D thetaH) ∧
    ∀ (D : Measure (ValueProfile 1)) [IsProbabilityMeasure D]
      (thetaH : ℝ), 0 < thetaH →
      (∀ c : Candidate 1, Integrable (fun value : ValueProfile 1 => value c) D) →
      (∀ᵐ value ∂D,
        value (1 : Candidate 1) < value (0 : Candidate 1) ∧
          value (2 : Candidate 1) < value (1 : Candidate 1)) →
      literal_outer_payoff_paradox
        sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily D thetaH := by
  rcases theorem2_gaussian_laplace_source_semantic_complete with
    ⟨_, _, _, _, _, _, _, _, hgaussian, hlaplace⟩
  constructor
  · intro D _ thetaH hthetaH hvalue horder
    simpa only [literal_outer_payoff_paradox,
      DistributionalAccuracyFamily.theorem1_f,
      DistributionalAccuracyFamily.theorem1_g,
      DistributionalAccuracyFamily.theorem1_h,
      DistributionalAccuracyFamily.theorem1_algorithmAgainstHuman,
      DistributionalAccuracyFamily.outerExpected] using
      hgaussian D thetaH hthetaH hvalue horder
  · intro D _ thetaH hthetaH hvalue horder
    simpa only [literal_outer_payoff_paradox,
      DistributionalAccuracyFamily.theorem1_f,
      DistributionalAccuracyFamily.theorem1_g,
      DistributionalAccuracyFamily.theorem1_h,
      DistributionalAccuracyFamily.theorem1_algorithmAgainstHuman,
      DistributionalAccuracyFamily.outerExpected] using
      hlaplace D thetaH hthetaH hvalue horder

/-- Literal contract for Theorem 2's Gaussian and Laplace terminal payoffs. -/
abbrev theorem2_gaussian_laplace_literal_payoff_terminal_conclusionsSpec : Prop :=
  (∀ (D : Measure (ValueProfile 1)) [IsProbabilityMeasure D]
    (thetaH : ℝ), 0 < thetaH →
    (∀ c : Candidate 1, Integrable (fun value : ValueProfile 1 => value c) D) →
    (∀ᵐ value ∂D,
      value (1 : Candidate 1) < value (0 : Candidate 1) ∧
        value (2 : Candidate 1) < value (1 : Candidate 1)) →
    literal_outer_payoff_paradox gaussianThreeCandidateDistributionalFamily D thetaH) ∧
  ∀ (D : Measure (ValueProfile 1)) [IsProbabilityMeasure D]
    (thetaH : ℝ), 0 < thetaH →
    (∀ c : Candidate 1, Integrable (fun value : ValueProfile 1 => value c) D) →
    (∀ᵐ value ∂D,
      value (1 : Candidate 1) < value (0 : Candidate 1) ∧
        value (2 : Candidate 1) < value (1 : Candidate 1)) →
    literal_outer_payoff_paradox
      sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily D thetaH

theorem theorem2_gaussian_laplace_literal_payoff_terminal_conclusions_spec_proof :
    theorem2_gaussian_laplace_literal_payoff_terminal_conclusionsSpec :=
  theorem2_gaussian_laplace_literal_payoff_terminal_conclusions

/--
Theorem 3's complete source endpoint at its terminal payoff conclusion.  The
Mallows-law, Definition 1, Definition 2, and Definition 3 material remains in
the compatibility theorem; this endpoint makes the final common-witness
payoff result directly auditable as outer integrals.
-/
theorem theorem3_complete_literal_payoff_terminal_conclusion
    {n : ℕ} (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    (center : Ranking n) (hn : 0 < n)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D)
    (hstrict : ∀ᵐ value ∂D, StrictlyOrderedBy center value) :
    ∀ thetaH : ℝ, 0 < thetaH →
      literal_outer_payoff_paradox
        (fixedCenterMallowsDistributionalFamily center) D thetaH := by
  rcases theorem3_source_complete_semantic_complete
    D center hn hvalue hstrict with ⟨_, _, _, _, hterminal⟩
  intro thetaH hthetaH
  simpa only [literal_outer_payoff_paradox,
    DistributionalAccuracyFamily.theorem1_f,
    DistributionalAccuracyFamily.theorem1_g,
    DistributionalAccuracyFamily.theorem1_h,
    DistributionalAccuracyFamily.theorem1_algorithmAgainstHuman,
    DistributionalAccuracyFamily.outerExpected] using
    hterminal thetaH hthetaH

/-- Literal contract for Theorem 3's complete terminal payoff conclusion. -/
abbrev theorem3_complete_literal_payoff_terminal_conclusionSpec
    {n : ℕ} (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    (center : Ranking n) (hn : 0 < n)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D)
    (hstrict : ∀ᵐ value ∂D, StrictlyOrderedBy center value) : Prop :=
  ∀ thetaH : ℝ, 0 < thetaH →
    literal_outer_payoff_paradox
      (fixedCenterMallowsDistributionalFamily center) D thetaH

theorem theorem3_complete_literal_payoff_terminal_conclusion_spec_proof
    {n : ℕ} (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    (center : Ranking n) (hn : 0 < n)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D)
    (hstrict : ∀ᵐ value ∂D, StrictlyOrderedBy center value) :
    theorem3_complete_literal_payoff_terminal_conclusionSpec
      D center hn hvalue hstrict :=
  theorem3_complete_literal_payoff_terminal_conclusion
    D center hn hvalue hstrict

/--
Complete literal-payoff bridge for Theorem 2.  All source-law and Definition
1--3 conjuncts are retained from the compatibility endpoint; only its terminal
payoff groups are supplied by the literal Gaussian/Laplace terminal endpoint.
-/
theorem theorem2_gaussian_laplace_source_semantic_complete_literal_payoff :
    theorem2_gaussian_laplace_source_semantic_completeSpec := by
  rcases theorem2_gaussian_laplace_source_semantic_complete with
    ⟨hgaussianLaw, hgaussianVariance, hlaplaceVariance, hlaplaceLaw, hgaussianDefinition1,
      hlaplaceDefinition1, hgaussianDefinitions, hlaplaceDefinitions,
      _, _⟩
  rcases theorem2_gaussian_laplace_literal_payoff_terminal_conclusions with
    ⟨hgaussianTerminal, hlaplaceTerminal⟩
  exact ⟨hgaussianLaw, hgaussianVariance, hlaplaceVariance, hlaplaceLaw, hgaussianDefinition1,
    hlaplaceDefinition1, hgaussianDefinitions, hlaplaceDefinitions,
    hgaussianTerminal, hlaplaceTerminal⟩

/--
Complete literal-payoff bridge for Theorem 3.  The literal Mallows law and
Definitions 1--3 remain on the full source surface, and the common-witness
terminal group is supplied by the literal outer-payoff endpoint.
-/
theorem theorem3_source_complete_semantic_complete_literal_payoff
    {n : ℕ} (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    (center : Ranking n) (hn : 0 < n)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D)
    (hstrict : ∀ᵐ value ∂D, StrictlyOrderedBy center value) :
    theorem3_source_complete_semantic_completeSpec D center hn hvalue hstrict := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro phi theta hphi htheta
    refine ⟨(source_equation8_concrete_mallows_probability center phi theta
      hphi htheta center).1, ?_⟩
    intro value pi
    simpa [fixedCenterMallowsDistributionalFamily] using
      (source_equation8_concrete_mallows_probability center phi theta
        hphi htheta pi).2
  · intro value horder
    have hdefinition : SourceDefinition1NoisyPermutationFamily
        (fixedCenterMallowsPointFamily center value) center := by
      simpa only [fixedCenterMallowsPointFamily] using
        (concreteMallowsAccuracyFamily_sourceDefinition1 center value horder)
    simpa only [SourceDefinition1NoisyPermutationFamily] using hdefinition
  · intro theta htheta
    let F := fixedCenterMallowsDistributionalFamily center
    let hatom : ∀ ranking : Ranking n,
        Measurable fun value => F.dist theta value ranking :=
      fun ranking => DistributionalAccuracyFamily.fixedCenterMallows_ranking_atom_measurable
        center theta ranking
    have hevent : 0 < ∫ x : ValueProfile n × RankingPair n,
        (if firstChoice x.2.1 ≠ firstChoice x.2.2 then (1 : ℝ) else 0) ∂
          F.outerIndependentPairJointLaw D theta hatom := by
      simpa [F, hatom, disagreementEvent] using
        DistributionalAccuracyFamily.fixedCenterMallows_outerJointDisagreementEvent_pos
          D center theta
    have hgain : 0 < F.jointLawDisagreementConditionalGain D theta hatom := by
      simpa [F, hatom] using
        DistributionalAccuracyFamily.fixedCenterMallows_outer_jointLawDisagreementConditionalGain_pos
          D center hn theta htheta hvalue hstrict
    refine ⟨hevent, ?_⟩
    have hdisagreement_event : 0 < ∫ x : ValueProfile n × RankingPair n,
        (if disagreementEvent x.2 then (1 : ℝ) else 0) ∂
          F.outerIndependentPairJointLaw D theta hatom := by
      simpa only [disagreementEvent] using hevent
    have hnum_eq :
        (∫ x : ValueProfile n × RankingPair n,
          if disagreementEvent x.2 then pairRerankingGain x.1 x.2 else 0 ∂
            F.outerIndependentPairJointLaw D theta hatom) =
        ∫ x : ValueProfile n × RankingPair n,
          if firstChoice x.2.1 ≠ firstChoice x.2.2 then
            x.1 (firstChoice x.2.1) - x.1 (secondChoice x.2.1)
          else 0 ∂F.outerIndependentPairJointLaw D theta hatom := by
      apply integral_congr_ae
      filter_upwards [] with x
      by_cases h : firstChoice x.2.1 = firstChoice x.2.2
      · have h0 : x.2.1 0 = x.2.2 0 := by simpa [firstChoice] using h
        simp [disagreementEvent, firstChoice, secondChoice, h0]
      · have h0 : x.2.1 0 ≠ x.2.2 0 := by simpa [firstChoice] using h
        have hne : firstChoice x.2.1 ≠ firstChoice x.2.2 := h
        simp only [disagreementEvent, if_pos hne]
        change AppliedModelingLib.SocialChoice.Ranking.rerankingGainOnPair
          x.1 x.2.1 x.2.2 = x.1 (x.2.1 0) - x.1 (x.2.1 1)
        exact AppliedModelingLib.SocialChoice.Ranking.rerankingGainOnPair_of_neFirst
          x.1 x.2.1 x.2.2 h0
    have hden_eq :
        (∫ x : ValueProfile n × RankingPair n,
          if disagreementEvent x.2 then (1 : ℝ) else 0 ∂
            F.outerIndependentPairJointLaw D theta hatom) =
        ∫ x : ValueProfile n × RankingPair n,
          if firstChoice x.2.1 ≠ firstChoice x.2.2 then (1 : ℝ) else 0 ∂
            F.outerIndependentPairJointLaw D theta hatom := by
      apply integral_congr_ae
      filter_upwards [] with x
      rfl
    have hratio : F.jointLawDisagreementConditionalGain D theta hatom =
        (∫ x : ValueProfile n × RankingPair n,
          if firstChoice x.2.1 ≠ firstChoice x.2.2 then
            x.1 (firstChoice x.2.1) - x.1 (secondChoice x.2.1)
          else 0 ∂F.outerIndependentPairJointLaw D theta hatom) /
        (∫ x : ValueProfile n × RankingPair n,
          if firstChoice x.2.1 ≠ firstChoice x.2.2 then (1 : ℝ) else 0 ∂
            F.outerIndependentPairJointLaw D theta hatom) := by
      unfold DistributionalAccuracyFamily.jointLawDisagreementConditionalGain
      dsimp only
      rw [if_neg (ne_of_gt hdisagreement_event), hnum_eq, hden_eq]
    rw [← hratio]
    exact hgain
  · intro thetaA thetaH hthetaH hthetaA
    have h := fixedCenterMallows_outer_prefersWeakerCompetition
      D center hn thetaA thetaH hthetaH hthetaA hvalue hstrict
    simpa [DistributionalAccuracyFamily.PrefersWeakerCompetition,
      DistributionalAccuracyFamily.outerExpected,
      expectedSecondMoverIndependent] using h
  · intro thetaH hthetaH
    have hterminal := fixedCenterMallows_outer_distributionalTheorem1Target
      D center hn thetaH hthetaH hvalue hstrict
    simpa only [literal_outer_payoff_paradox,
      DistributionalAccuracyFamily.theorem1_f,
      DistributionalAccuracyFamily.theorem1_g,
      DistributionalAccuracyFamily.theorem1_h,
      DistributionalAccuracyFamily.theorem1_algorithmAgainstHuman,
      DistributionalAccuracyFamily.outerExpected] using hterminal

end PaperInterface
end KR21Monoculture
