import KR21Monoculture.MallowsOuterSource
import KR21Monoculture.OuterConditional
import KR21Monoculture.MallowsSupport

open AppliedModelingLib MeasureTheory ProbabilityTheory Filter

namespace KR21Monoculture

/-!
# Fixed-center Mallows and the source's outer conditional experiment

`fixedCenterMallows_outer_prefersIndependentReranking` proves the ex-ante
payoff inequality used by Definition 2.  The source also describes that
comparison as a gain conditional on two ranking draws disagreeing at the top
choice.  This module proves that stronger, joint-law formulation for the
actual outer value distribution: values are drawn from `D`, followed by two
conditionally independent rankings from the fixed Mallows PMF.

The proof records all regularity needed by `OuterConditional`: atomwise
measurability, outer and raw-joint payoff integrability, and positive mass of
the joint disagreement event.  The fixed ranking law is crucial here; it lets
coordinatewise first moments control every finite ranking-pair payoff.
-/

namespace DistributionalAccuracyFamily

/-- A fixed-center Mallows atom is constant as a function of the outer value
profile, hence measurable. -/
theorem fixedCenterMallows_ranking_atom_measurable
    {n : ℕ} (center : Ranking n) (theta : ℝ) (ranking : Ranking n) :
    Measurable fun value : ValueProfile n =>
      (fixedCenterMallowsDistributionalFamily center).dist theta value ranking := by
  simpa [fixedCenterMallowsDistributionalFamily] using
    (measurable_const : Measurable fun _ : ValueProfile n =>
      (concreteMallowsSpec center theta).law ranking)

/-- Coordinatewise first moments make the outer shared second-mover payoff
integrable for a fixed-center Mallows law. -/
theorem fixedCenterMallows_outer_shared_payoff_integrable
    {n : ℕ} (D : Measure (ValueProfile n)) (center : Ranking n) (theta : ℝ)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D) :
    Integrable
      (fun value => expectedSecondMoverShared
        ((fixedCenterMallowsDistributionalFamily center).dist theta value) value) D := by
  simpa [fixedCenterMallowsDistributionalFamily, expectedSecondMoverShared] using
    (integrable_pmfExp_valueSelection D (concreteMallowsSpec center theta).law
      secondChoice hvalue)

/-- Coordinatewise first moments make the outer independent second-mover
payoff integrable for a fixed-center Mallows law. -/
theorem fixedCenterMallows_outer_independent_payoff_integrable
    {n : ℕ} (D : Measure (ValueProfile n)) (center : Ranking n) (theta : ℝ)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D) :
    Integrable
      (fun value => expectedSecondMoverIndependent
        ((fixedCenterMallowsDistributionalFamily center).dist theta value)
        ((fixedCenterMallowsDistributionalFamily center).dist theta value) value) D := by
  simpa [fixedCenterMallowsDistributionalFamily, expectedSecondMoverIndependent,
    secondMoverUtility] using
    (integrable_pmfPairExp_valueSelection D (concreteMallowsSpec center theta).law
      (concreteMallowsSpec center theta).law
      (fun second first => bestRemainingAfter second (firstChoice first)) hvalue)

/-- The first projection of the actual outer conditional-ranking experiment
has exactly the source law `D`. -/
theorem fixedCenterMallows_outerJointLaw_fst_measurePreserving
    {n : ℕ} (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    (center : Ranking n) (theta : ℝ) :
    MeasurePreserving Prod.fst
      ((fixedCenterMallowsDistributionalFamily center).outerIndependentPairJointLaw D theta
        (fun ranking => fixedCenterMallows_ranking_atom_measurable center theta ranking)) D := by
  let F := fixedCenterMallowsDistributionalFamily center
  let hatom : ∀ ranking : Ranking n, Measurable fun value => F.dist theta value ranking :=
    fun ranking => fixedCenterMallows_ranking_atom_measurable center theta ranking
  letI : IsMarkovKernel (F.independentPairKernel theta hatom) :=
    F.independentPairKernel_isMarkov theta hatom
  refine ⟨measurable_fst, ?_⟩
  change (D ⊗ₘ F.independentPairKernel theta hatom).fst = D
  exact Measure.fst_compProd D (F.independentPairKernel theta hatom)

/-- Any candidate coordinate remains integrable after lifting `D` to the
actual profile/ranking-pair joint experiment. -/
theorem fixedCenterMallows_joint_coordinate_integrable
    {n : ℕ} (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    (center : Ranking n) (theta : ℝ)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D)
    (c : Candidate n) :
    Integrable (fun x : ValueProfile n × RankingPair n => x.1 c)
      ((fixedCenterMallowsDistributionalFamily center).outerIndependentPairJointLaw D theta
        (fun ranking => fixedCenterMallows_ranking_atom_measurable center theta ranking)) := by
  have hpres := fixedCenterMallows_outerJointLaw_fst_measurePreserving D center theta
  simpa [Function.comp_def] using hpres.integrable_comp_of_integrable (hvalue c)

private theorem measurableSet_jointPair_eq
    {n : ℕ} (pair : RankingPair n) :
    MeasurableSet {x : ValueProfile n × RankingPair n | x.2 = pair} := by
  change MeasurableSet (Prod.snd ⁻¹' {pair' : RankingPair n | pair' = pair})
  exact (Set.toFinite {pair' : RankingPair n | pair' = pair}).measurableSet.preimage
    measurable_snd

/-- Raw shared second-mover utility is integrable under the actual joint law.
This is not inferred from the outer expected payoff: it is proved by a finite
partition of the ranking-pair coordinate. -/
theorem fixedCenterMallows_joint_shared_payoff_integrable
    {n : ℕ} (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    (center : Ranking n) (theta : ℝ)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D) :
    Integrable jointSharedSecondMoverPayoff
      ((fixedCenterMallowsDistributionalFamily center).outerIndependentPairJointLaw D theta
        (fun ranking => fixedCenterMallows_ranking_atom_measurable center theta ranking)) := by
  let F := fixedCenterMallowsDistributionalFamily center
  let hatom : ∀ ranking : Ranking n, Measurable fun value => F.dist theta value ranking :=
    fun ranking => fixedCenterMallows_ranking_atom_measurable center theta ranking
  let M := F.outerIndependentPairJointLaw D theta hatom
  have hsum : Integrable (fun x : ValueProfile n × RankingPair n =>
      ∑ pair : RankingPair n,
        Set.indicator {x | x.2 = pair}
          (fun x => x.1 (secondChoice pair.1)) x) M := by
    refine MeasureTheory.integrable_finset_sum Finset.univ ?_
    intro pair _
    exact (fixedCenterMallows_joint_coordinate_integrable D center theta hvalue
      (secondChoice pair.1)).indicator (measurableSet_jointPair_eq pair)
  convert hsum using 1
  funext x
  classical
  simp only [jointSharedSecondMoverPayoff, secondMoverUtility,
    Set.indicator_apply, Set.mem_setOf_eq, bestRemainingAfter_of_eq]
  rw [Finset.sum_ite_eq]
  simp

/-- Raw independent second-mover utility is integrable under the actual joint
law, again by the finite ranking-pair partition. -/
theorem fixedCenterMallows_joint_independent_payoff_integrable
    {n : ℕ} (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    (center : Ranking n) (theta : ℝ)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D) :
    Integrable jointIndependentSecondMoverPayoff
      ((fixedCenterMallowsDistributionalFamily center).outerIndependentPairJointLaw D theta
        (fun ranking => fixedCenterMallows_ranking_atom_measurable center theta ranking)) := by
  let F := fixedCenterMallowsDistributionalFamily center
  let hatom : ∀ ranking : Ranking n, Measurable fun value => F.dist theta value ranking :=
    fun ranking => fixedCenterMallows_ranking_atom_measurable center theta ranking
  let M := F.outerIndependentPairJointLaw D theta hatom
  have hsum : Integrable (fun x : ValueProfile n × RankingPair n =>
      ∑ pair : RankingPair n,
        Set.indicator {x | x.2 = pair}
          (fun x => x.1 (bestRemainingAfter pair.1 (firstChoice pair.2))) x) M := by
    refine MeasureTheory.integrable_finset_sum Finset.univ ?_
    intro pair _
    exact (fixedCenterMallows_joint_coordinate_integrable D center theta hvalue
      (bestRemainingAfter pair.1 (firstChoice pair.2))).indicator
        (measurableSet_jointPair_eq pair)
  convert hsum using 1
  funext x
  classical
  simp only [jointIndependentSecondMoverPayoff, secondMoverUtility,
    Set.indicator_apply, Set.mem_setOf_eq]
  rw [Finset.sum_ite_eq]
  simp

/-- All regularity assumptions for the source's actual Definition-2 joint
experiment follow from coordinatewise first moments in the fixed-center
Mallows model. -/
theorem fixedCenterMallows_outerIndependentRerankingJointRegularity
    {n : ℕ} (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    (center : Ranking n) (theta : ℝ)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D) :
    OuterIndependentRerankingJointRegularity
      (fixedCenterMallowsDistributionalFamily center) D theta := by
  refine
    { base :=
        { outer_is_probability := inferInstance
          ranking_atom_measurable := fun ranking =>
            fixedCenterMallows_ranking_atom_measurable center theta ranking
          disagreement_integrable := ?_
          shared_payoff_integrable :=
            fixedCenterMallows_outer_shared_payoff_integrable D center theta hvalue
          independent_payoff_integrable :=
            fixedCenterMallows_outer_independent_payoff_integrable D center theta hvalue }
      joint_shared_payoff_integrable :=
        fixedCenterMallows_joint_shared_payoff_integrable D center theta hvalue
      joint_independent_payoff_integrable :=
        fixedCenterMallows_joint_independent_payoff_integrable D center theta hvalue }
  simpa [fixedCenterMallowsDistributionalFamily] using
    (integrable_const (disagreementProb (concreteMallowsSpec center theta).law))

/-- Every fixed-center Mallows PMF has positive probability of a top-choice
disagreement between two independent draws.  The ranking library's candidate
type already contains at least two candidates. -/
theorem concreteMallows_disagreementProb_pos
    {n : ℕ} (center : Ranking n) (theta : ℝ) :
    0 < disagreementProb (concreteMallowsSpec center theta).law := by
  change 0 < AppliedModelingLib.pmfPairExp (concreteMallowsSpec center theta).law
    (concreteMallowsSpec center theta).law
    (fun pi sigma => if disagreementEvent (pi, sigma) then 1 else 0)
  rw [← AppliedModelingLib.pmfExp_pmfProd_eq_pairExp
    (concreteMallowsSpec center theta).law
    (concreteMallowsSpec center theta).law
    (fun pair => if disagreementEvent pair then 1 else 0)]
  refine AppliedModelingLib.pmfProb_pos_of_mass
    (AppliedModelingLib.pmfProd (concreteMallowsSpec center theta).law
      (concreteMallowsSpec center theta).law)
    disagreementEvent (center, swapTopTwo center) ?_ ?_
  · exact (swapTopTwo_firstChoice_ne center).symm
  · rw [AppliedModelingLib.pmfProd_apply_toReal]
    exact mul_pos
      ((concreteMallowsSpec center theta).law_apply_toReal_pos center)
      ((concreteMallowsSpec center theta).law_apply_toReal_pos (swapTopTwo center))

/-- The iterated probability of top disagreement is the fixed PMF's
disagreement probability in the fixed-center model. -/
theorem fixedCenterMallows_outerDisagreementProbability_eq
    {n : ℕ} (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    (center : Ranking n) (theta : ℝ) :
    (fixedCenterMallowsDistributionalFamily center).outerDisagreementProbability D theta =
      disagreementProb (concreteMallowsSpec center theta).law := by
  rw [outerDisagreementProbability_eq_outerExpected]
  simp [fixedCenterMallowsDistributionalFamily, outerExpected]

/-- The actual joint value-profile/ranking-pair experiment assigns positive
mass to top-choice disagreement. -/
theorem fixedCenterMallows_outerJointDisagreementEvent_pos
    {n : ℕ} (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    (center : Ranking n) (theta : ℝ) :
    0 < ∫ x : ValueProfile n × RankingPair n,
      (if disagreementEvent x.2 then (1 : ℝ) else 0) ∂
        (fixedCenterMallowsDistributionalFamily center).outerIndependentPairJointLaw D theta
          (fun ranking => fixedCenterMallows_ranking_atom_measurable center theta ranking) := by
  rw [integral_jointDisagreementIndicator_eq_outerDisagreementProbability]
  rw [fixedCenterMallows_outerDisagreementProbability_eq]
  exact concreteMallows_disagreementProb_pos center theta

/-- On the source's conditioning event, the joint-law gain integrand is exactly
the advertised first-ranked minus second-ranked value of the independently
drawn ranking.  This identifies the conditional event semantically rather
than merely through the pre-existing utility-comparison name. -/
theorem pairRerankingGain_eq_sourceFirstPositionGap_of_disagreement
    {n : ℕ} (value : ValueProfile n) (pair : RankingPair n)
    (hdisagreement : disagreementEvent pair) :
    pairRerankingGain value pair =
      value (firstChoice pair.1) - value (secondChoice pair.1) := by
  exact rerankingGainOnPair_of_neFirst value pair.1 pair.2 hdisagreement

/-- Source Definition 2 in its actual conditional-event semantics: draw a
value profile from `D`, then two conditionally i.i.d. fixed-center Mallows
rankings.  Positive conditional gain holds under the same explicit source-order
and finite-first-moment conditions as the outer payoff theorem. -/
theorem fixedCenterMallows_outer_jointLawDisagreementConditionalGain_pos
    {n : ℕ} (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    (center : Ranking n) (hn : 0 < n) (theta : ℝ) (htheta : 0 < theta)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D)
    (hstrict : ∀ᵐ value ∂D, StrictlyOrderedBy center value) :
    0 < jointLawDisagreementConditionalGain
      (fixedCenterMallowsDistributionalFamily center) D theta
      (fun ranking => fixedCenterMallows_ranking_atom_measurable center theta ranking) := by
  let F := fixedCenterMallowsDistributionalFamily center
  let regularity := fixedCenterMallows_outerIndependentRerankingJointRegularity
    D center theta hvalue
  have hpreference : F.PrefersIndependentReranking D theta :=
    fixedCenterMallows_outer_prefersIndependentReranking
      D center hn theta htheta hvalue hstrict
  have hdisagreement : 0 < ∫ x : ValueProfile n × RankingPair n,
      (if disagreementEvent x.2 then (1 : ℝ) else 0) ∂
        F.outerIndependentPairJointLaw D theta regularity.base.ranking_atom_measurable := by
    simpa [F, regularity] using
      (fixedCenterMallows_outerJointDisagreementEvent_pos D center theta)
  exact
    (F.prefersIndependentReranking_iff_jointLawDisagreementConditionalGain_pos_of_regular
      D theta regularity hdisagreement).mp hpreference

end DistributionalAccuracyFamily

end KR21Monoculture
