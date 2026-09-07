import KR21Monoculture.MallowsDefinition1
import KR21Monoculture.OuterConditional
import KR21Monoculture.SourceModelEquations

open AppliedModelingLib MeasureTheory ProbabilityTheory Filter
open AppliedModelingLib.SocialChoice.Ranking
open scoped ENNReal NNReal Topology

namespace KR21Monoculture

/-!
# Literal source model and definition endpoints for KR21

These declarations expose the source's model and Definitions 1--3 at their
actual proposition surfaces.  They deliberately keep the finite candidate
encoding, the outer value law, the conditioning event, and every source
quantifier visible instead of routing review through theorem-name conventions.
-/

/-- The source's strict intrinsic-value ordering, represented relative to its
true ranking.  The library's `Candidate n` has `n + 2` candidates. -/
def SourceCandidateValueOrder {n : ℕ}
    (trueRanking : Ranking n) (value : Candidate n -> ℝ) : Prop :=
  StrictlyOrderedBy trueRanking value

/-- The source candidate model's true-value condition is exactly strict
decrease down the declared true ranking. -/
theorem source_candidate_value_order_iff
    {n : ℕ} (trueRanking : Ranking n) (value : Candidate n -> ℝ) :
    SourceCandidateValueOrder trueRanking value <->
      StrictlyOrderedBy trueRanking value := Iff.rfl

/-- The library's finite candidate representation has exactly `n + 2`
source candidates. -/
theorem source_candidate_model_cardinality (n : ℕ) :
    Fintype.card (Candidate n) = n + 2 := by
  simp [Candidate]

/-- A degenerate outer value law is an admissible probability law, matching
the source's statement that the joint candidate distribution may be a point
mass. -/
theorem source_outer_candidate_distribution_allows_point_mass
    {n : ℕ} (value : ValueProfile n) :
    IsProbabilityMeasure (Measure.dirac value) := by
  infer_instance

/-- Definition 1 at the literal finite ranking-family surface. -/
abbrev SourceDefinition1 {n : ℕ}
    (F : AccuracyFamily n) (trueRanking : Ranking n) : Prop :=
  SourceDefinition1NoisyPermutationFamily F trueRanking

/-- Equation (1), extracted from the literal Definition 1 package: every
nonempty remaining candidate set weakly improves as accuracy increases, and
the full candidate set improves strictly. -/
theorem source_equation1_removal_monotonicity
    {n : ℕ} {F : AccuracyFamily n} {trueRanking : Ranking n}
    (hdefinition1 : SourceDefinition1 F trueRanking) :
    forall thetaA thetaH, 0 < thetaH -> thetaH < thetaA ->
      (forall remaining : Finset (Candidate n), remaining.Nonempty ->
        expectedBestInSet (F.dist thetaH) F.value remaining <=
          expectedBestInSet (F.dist thetaA) F.value remaining) /\
      expectedBestInSet (F.dist thetaH) F.value Finset.univ <
        expectedBestInSet (F.dist thetaA) F.value Finset.univ := by
  exact hdefinition1.2.2

/-- The concrete Kendall--Mallows construction satisfies every literal
Definition 1 field, including the arbitrary-remaining-set clause. -/
theorem source_definition1_concrete_mallows
    {n : ℕ} (trueRanking : Ranking n) (value : Candidate n -> ℝ)
    (hvalue : SourceCandidateValueOrder trueRanking value) :
    SourceDefinition1
      ({ dist := fun theta => (concreteMallowsSpec trueRanking theta).law,
         value := value } : AccuracyFamily n)
      trueRanking :=
  concreteMallowsAccuracyFamily_sourceDefinition1 trueRanking value hvalue

/-- The literal source Definition 2 conditional experiment at one positive
accuracy: draw a value profile from `D`, then two conditionally independent
rankings, and condition on different first choices. -/
noncomputable def SourceDefinition2ConditionalAt {n : ℕ}
    (F : DistributionalAccuracyFamily n) (D : Measure (ValueProfile n))
    (theta : ℝ) (hatom : forall ranking : Ranking n,
      Measurable fun value => F.dist theta value ranking) : Prop :=
  0 < F.jointLawDisagreementConditionalGain D theta hatom

/--
The full source Definition 2.  Its quantifier is over every positive accuracy,
not a single chosen instance.  The conditioning event is required to have
positive mass, as is necessary for the source conditional expectation to have
its ordinary real-valued meaning.
-/
noncomputable def SourceDefinition2 {n : ℕ}
    (F : DistributionalAccuracyFamily n) (D : Measure (ValueProfile n)) : Prop :=
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

/-- The source Definition 2 conditional gain is equivalent to the outer
second-mover payoff comparison when the actual joint experiment is regular and
the source conditioning event has positive probability. -/
theorem source_definition2_conditional_at_iff_payoff_comparison
    {n : ℕ} (F : DistributionalAccuracyFamily n) (D : Measure (ValueProfile n))
    (theta : ℝ)
    (regularity : DistributionalAccuracyFamily.OuterIndependentRerankingJointRegularity
      F D theta)
    (hdisagreement : 0 < ∫ x : ValueProfile n × RankingPair n,
      (if disagreementEvent x.2 then (1 : ℝ) else 0) ∂
        F.outerIndependentPairJointLaw D theta regularity.base.ranking_atom_measurable) :
    SourceDefinition2ConditionalAt F D theta regularity.base.ranking_atom_measurable <->
      F.PrefersIndependentReranking D theta := by
  exact (F.prefersIndependentReranking_iff_jointLawDisagreementConditionalGain_pos_of_regular
    D theta regularity hdisagreement).symm

/-- The literal outer-D Definition 3 comparison at one ordered pair of
accuracies.  The human ranking is the second mover's ranking in both terms;
only the independent first mover changes from accurate to noisy. -/
noncomputable def SourceDefinition3At {n : ℕ}
    (F : DistributionalAccuracyFamily n) (D : Measure (ValueProfile n))
    (thetaA thetaH : ℝ) : Prop :=
  DistributionalAccuracyFamily.outerExpected D (fun value =>
      expectedSecondMoverIndependent
        (F.dist thetaH value) (F.dist thetaA value) value) <
    DistributionalAccuracyFamily.outerExpected D (fun value =>
      expectedSecondMoverIndependent
        (F.dist thetaH value) (F.dist thetaH value) value)

/--
The full source Definition 3.  It quantifies over every ordered positive pair
of algorithmic and human accuracies.
-/
noncomputable def SourceDefinition3 {n : ℕ}
    (F : DistributionalAccuracyFamily n) (D : Measure (ValueProfile n)) : Prop :=
  ∀ thetaA thetaH : ℝ, 0 < thetaH → thetaH < thetaA →
    (∫ value : ValueProfile n,
      pmfPairExp (F.dist thetaH value) (F.dist thetaA value)
        (fun pi sigma => secondMoverUtility value pi sigma) ∂D) <
    (∫ value : ValueProfile n,
      pmfPairExp (F.dist thetaH value) (F.dist thetaH value)
        (fun pi sigma => secondMoverUtility value pi sigma) ∂D)

/-- The source Definition 3 expression is definitionally the formal outer-D
weaker-competition predicate. -/
theorem source_definition3_at_iff_weaker_competition
    {n : ℕ} (F : DistributionalAccuracyFamily n) (D : Measure (ValueProfile n))
    (thetaA thetaH : ℝ) :
    SourceDefinition3At F D thetaA thetaH <->
      F.PrefersWeakerCompetition D thetaA thetaH := Iff.rfl

/-- Equation (2)'s literal equal-accuracy comparison. -/
theorem source_equation2_independent_reranking_payoff_equivalence
    {n : ℕ} (mu : PMF (Ranking n)) (value : Candidate n -> ℝ)
    (hdisagreement : 0 < disagreementProb mu) :
    0 < disagreementConditionalGain mu value <->
      expectedSecondMoverShared mu value <
        expectedSecondMoverIndependent mu mu value :=
  equation2_independent_reranking_payoff_equivalence mu value hdisagreement

/-- Equation (3)'s literal top-disagreement gain identity. -/
theorem source_equation3_independent_reranking_payoff_identity
    {n : ℕ} (mu : PMF (Ranking n)) (value : Candidate n -> ℝ) :
    expectedSecondMoverIndependent mu mu value -
        expectedSecondMoverShared mu value =
      pmfPairIndicatorExp mu mu disagreementEvent
        (fun pair => value (firstChoice pair.1) - value (secondChoice pair.1)) :=
  equation3_independent_reranking_payoff_identity mu value

/-- Equation (4)'s strict best-response equivalence. -/
theorem source_equation4_algorithm_best_response_against_algorithm_iff
    {n : ℕ} (M : Model n) :
    (Model.firstMoverEU M Strategy.algorithm +
        Model.secondMoverEU M Strategy.algorithm Strategy.algorithm >
      Model.firstMoverEU M Strategy.human +
        Model.secondMoverEU M Strategy.algorithm Strategy.human) <->
      Model.payoffAgainst M Strategy.algorithm Strategy.algorithm >
        Model.payoffAgainst M Strategy.human Strategy.algorithm :=
  equation4_algorithm_best_response_against_algorithm_iff M

/-- Equation (5)'s direct finite-removal consequence. -/
theorem source_equation5_from_definition1_removal
    {n : ℕ} (F : AccuracyFamily n) (thetaA thetaH : ℝ)
    (hweak : forall remaining : Finset (Candidate n), remaining.Nonempty ->
      expectedBestInSet (F.dist thetaH) F.value remaining <=
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
  equation5_from_literal_definition1_removal F thetaA thetaH hweak hstrict

/-- Equation (6)'s intermediate indifference point. -/
theorem source_equation6_indifference_threshold_of_sign_change
    {n : ℕ} (F : AccuracyFamily n) (thetaH lo hi : ℝ)
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
    exists thetaA, thetaH < thetaA /\
      AccuracyFamily.theorem1_f F thetaA thetaH =
        AccuracyFamily.theorem1_g F thetaA thetaH :=
  equation6_indifference_threshold_of_sign_change
    F thetaH lo hi hthetaH_lo hlo_hi hcontinuous hlo hhi

end KR21Monoculture
