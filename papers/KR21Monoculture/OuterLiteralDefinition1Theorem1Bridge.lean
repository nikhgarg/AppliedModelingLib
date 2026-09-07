import KR21Monoculture.OuterRUMTheorem1Positive
import KR21Monoculture.OuterRUMMonotonicity
import KR21Monoculture.OuterRUMSourceConcentration
import KR21Monoculture.LiteralDefinition1Theorem1Bridge
import KR21Monoculture.OuterConditional

/-!
# Outer-D literal Definition 1--3 bridge

The source states Definitions 2 and 3 for the experiment that first draws a
value profile from `D`.  This module keeps that quantifier order.  In
particular, it does not replace source Definition 2 with an almost-everywhere
pointwise preference premise merely to obtain the high-accuracy crossing.

The finite fixed-profile proof shows that a disagreement in the human first
choice forces a strict loss relative to the pure true ranking.  The new outer
lemma integrates that fact over the positive-mass disagreement support.  Thus
the crossing uses the literal outer condition together with visible
measurability, integrability, and non-null-conditioning obligations.
-/

open AppliedModelingLib MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace KR21Monoculture
namespace DistributionalAccuracyFamily

/-- Positive iid top-disagreement probability supplies a positive-mass ranking
whose first choice differs from a fixed center's first candidate. -/
theorem exists_positive_mass_firstChoice_ne_centerFirst_of_disagreementProb_pos
    {n : ℕ} (mu : PMF (Ranking n)) (center : Ranking n)
    (hdisagreement : 0 < disagreementProb mu) :
    ∃ pi : Ranking n, 0 < (mu pi).toReal ∧
      firstChoice pi ≠ firstChoice center := by
  classical
  have hprob_eq :
      disagreementProb mu =
        AppliedModelingLib.pmfProb (AppliedModelingLib.pmfProd mu mu) disagreementEvent := by
    change AppliedModelingLib.pmfPairExp mu mu
        (fun pi sigma => if disagreementEvent (pi, sigma) then (1 : ℝ) else 0) =
      AppliedModelingLib.pmfExp (AppliedModelingLib.pmfProd mu mu)
        (fun pair => if disagreementEvent pair then (1 : ℝ) else 0)
    exact (AppliedModelingLib.pmfExp_pmfProd_eq_pairExp mu mu
      (fun pair => if disagreementEvent pair then (1 : ℝ) else 0)).symm
  rw [hprob_eq] at hdisagreement
  rcases (AppliedModelingLib.pmfProb_pos_iff_exists_pos_mass
      (AppliedModelingLib.pmfProd mu mu) disagreementEvent).mp hdisagreement with
    ⟨pair, hpair, hmass⟩
  have hpair_mass : 0 < (mu pair.1).toReal * (mu pair.2).toReal := by
    simpa only [AppliedModelingLib.pmfProd_apply_toReal] using hmass
  have hleft_mass : 0 < (mu pair.1).toReal := by
    rcases (mul_pos_iff.mp hpair_mass) with hpos | hneg
    · exact hpos.1
    · exact False.elim ((not_lt_of_ge ENNReal.toReal_nonneg) hneg.1)
  have hright_mass : 0 < (mu pair.2).toReal := by
    rcases (mul_pos_iff.mp hpair_mass) with hpos | hneg
    · exact hpos.2
    · exact False.elim ((not_lt_of_ge ENNReal.toReal_nonneg) hneg.2)
  by_cases hfirst : firstChoice pair.1 = firstChoice center
  · refine ⟨pair.2, hright_mass, ?_⟩
    intro hsecond
    apply hpair
    exact hfirst.trans hsecond.symm
  · exact ⟨pair.1, hleft_mass, hfirst⟩

/-- Finite iid top-disagreement probability is nonnegative. -/
theorem disagreementProb_nonneg {n : ℕ} (mu : PMF (Ranking n)) :
    0 ≤ disagreementProb mu := by
  change 0 ≤ AppliedModelingLib.pmfPairExp mu mu
    (fun pi sigma => if disagreementEvent (pi, sigma) then (1 : ℝ) else 0)
  rw [← AppliedModelingLib.pmfExp_pmfProd_eq_pairExp mu mu
    (fun pair => if disagreementEvent pair then (1 : ℝ) else 0)]
  change 0 ≤ AppliedModelingLib.pmfProb (AppliedModelingLib.pmfProd mu mu) disagreementEvent
  exact AppliedModelingLib.pmfProb_nonneg _ _

/-- A strict true ranking weakly dominates the human-versus-pure-center total
payoff at one realized value profile. -/
theorem humanAgainstPureCenter_le_pureCenter_payoff
    {n : ℕ} (mu : PMF (Ranking n)) (center : Ranking n)
    (value : Candidate n → ℝ) (hvalue : StrictlyOrderedBy center value) :
    expectedFirstMoverUtility mu value +
        expectedSecondMoverIndependent mu (PMF.pure center) value ≤
      expectedFirstMoverUtility (PMF.pure center) value +
        expectedSecondMoverShared (PMF.pure center) value := by
  have hpoint :
      AppliedModelingLib.pmfExp mu
          (fun sigma =>
            value (firstChoice sigma) +
              value (bestRemainingAfter sigma (firstChoice center))) ≤
        value (firstChoice center) + value (secondChoice center) := by
    refine AppliedModelingLib.pmfExp_le_of_forall_le mu _ _ ?_
    intro sigma
    exact add_le_add
      (AccuracyFamily.value_le_centerFirst_of_strictlyOrderedBy hvalue (firstChoice sigma))
      (AccuracyFamily.value_le_centerSecond_of_strictlyOrderedBy_of_ne_centerFirst
        hvalue (bestRemainingAfter_ne_removed sigma (firstChoice center)))
  have hleft :
      expectedFirstMoverUtility mu value +
          expectedSecondMoverIndependent mu (PMF.pure center) value =
        AppliedModelingLib.pmfExp mu
          (fun sigma =>
            value (firstChoice sigma) +
              value (bestRemainingAfter sigma (firstChoice center))) := by
    rw [AccuracyFamily.expectedSecondMoverIndependent_eq_expect_bestAfterRemoval]
    simp [expectedFirstMoverUtility, AccuracyFamily.expectedBestAfterRemoval,
      AppliedModelingLib.pmfExp_add]
  have hright :
      expectedFirstMoverUtility (PMF.pure center) value +
          expectedSecondMoverShared (PMF.pure center) value =
        value (firstChoice center) + value (secondChoice center) := by
    simp [expectedFirstMoverUtility, expectedSecondMoverShared]
  rw [hleft, hright]
  exact hpoint

/-- On a strict value profile, positive iid top-disagreement makes the
human-versus-pure-center payoff loss strict. -/
theorem humanAgainstPureCenter_lt_pureCenter_payoff_of_disagreementProb_pos
    {n : ℕ} (mu : PMF (Ranking n)) (center : Ranking n)
    (value : Candidate n → ℝ) (hvalue : StrictlyOrderedBy center value)
    (hdisagreement : 0 < disagreementProb mu) :
    expectedFirstMoverUtility mu value +
        expectedSecondMoverIndependent mu (PMF.pure center) value <
      expectedFirstMoverUtility (PMF.pure center) value +
        expectedSecondMoverShared (PMF.pure center) value := by
  rcases exists_positive_mass_firstChoice_ne_centerFirst_of_disagreementProb_pos
      mu center hdisagreement with ⟨pi, hmass, htop_error⟩
  exact
    AccuracyFamily.expected_human_against_pureCenter_lt_pureCenter_payoff_of_positive_top_error
      mu center value hvalue hmass htop_error

/-- The literal outer Definition-2 conditioning event supplies the strict
pure-center limit gap needed by the source crossing proof.  Only the
conditioning-event probability is used here: positive disagreement forces a
positive-mass first-choice error on the strict source-order support. -/
theorem theorem1_pureCenterLimit_gap_of_outer_disagreement
    {n : ℕ} (F : DistributionalAccuracyFamily n)
    (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    (thetaH : ℝ) (center : Ranking n)
    (hgfirst : Integrable (fun value =>
      expectedFirstMoverUtility (F.dist thetaH value) value) D)
    (hgsecond : Integrable (fun value =>
      expectedSecondMoverIndependent (F.dist thetaH value) (PMF.pure center) value) D)
    (hffirst : Integrable (fun value =>
      expectedFirstMoverUtility (PMF.pure center) value) D)
    (hfsecond : Integrable (fun value =>
      expectedSecondMoverShared (PMF.pure center) value) D)
    (hdisagreement_integrable : Integrable
      (fun value => disagreementProb (F.dist thetaH value)) D)
    (hstrict_order : ∀ᵐ value ∂D, StrictlyOrderedBy center value)
    (houter_disagreement : 0 < F.outerDisagreementProbability D thetaH) :
    F.theorem1_g_pureCenterLimit D thetaH center <
      theorem1_f_pureCenterLimit D center := by
  let gap : ValueProfile n → ℝ := fun value =>
    (expectedFirstMoverUtility (PMF.pure center) value +
        expectedSecondMoverShared (PMF.pure center) value) -
      (expectedFirstMoverUtility (F.dist thetaH value) value +
        expectedSecondMoverIndependent (F.dist thetaH value) (PMF.pure center) value)
  have hgap_integrable : Integrable gap D := by
    exact (hffirst.add hfsecond).sub (hgfirst.add hgsecond)
  have hgap_nonneg : 0 ≤ᵐ[D] gap := by
    filter_upwards [hstrict_order] with value hvalue
    dsimp [gap]
    exact sub_nonneg.mpr
      (humanAgainstPureCenter_le_pureCenter_payoff
        (F.dist thetaH value) center value hvalue)
  have hdisagreement_nonneg : 0 ≤ᵐ[D]
      fun value => disagreementProb (F.dist thetaH value) := by
    filter_upwards with value
    exact disagreementProb_nonneg (F.dist thetaH value)
  have houter_disagreement_integral : 0 < ∫ value,
      disagreementProb (F.dist thetaH value) ∂D := by
    have houter := houter_disagreement
    rw [F.outerDisagreementProbability_eq_outerExpected] at houter
    exact houter
  have hdisagreement_support_pos : 0 < D
      (Function.support fun value => disagreementProb (F.dist thetaH value)) :=
    (integral_pos_iff_support_of_nonneg_ae
      hdisagreement_nonneg hdisagreement_integrable).mp houter_disagreement_integral
  have hsupport_mono :
      Function.support (fun value => disagreementProb (F.dist thetaH value)) ≤ᵐ[D]
        Function.support gap := by
    filter_upwards [hstrict_order] with value hvalue
    intro hdisagreement
    have hdisagreement_pos : 0 < disagreementProb (F.dist thetaH value) :=
      lt_of_le_of_ne (disagreementProb_nonneg (F.dist thetaH value))
        (Ne.symm hdisagreement)
    dsimp [gap]
    exact ne_of_gt (sub_pos.mpr
      (humanAgainstPureCenter_lt_pureCenter_payoff_of_disagreementProb_pos
        (F.dist thetaH value) center value hvalue hdisagreement_pos))
  have hgap_support_pos : 0 < D (Function.support gap) :=
    lt_of_lt_of_le hdisagreement_support_pos (measure_mono_ae hsupport_mono)
  have hgap_integral_pos : 0 < ∫ value, gap value ∂D :=
    (integral_pos_iff_support_of_nonneg_ae hgap_nonneg hgap_integrable).mpr
      hgap_support_pos
  have hgap_integral_eq :
      (∫ value, gap value ∂D) =
        ((∫ value, expectedFirstMoverUtility (PMF.pure center) value ∂D) +
          ∫ value, expectedSecondMoverShared (PMF.pure center) value ∂D) -
        ((∫ value, expectedFirstMoverUtility (F.dist thetaH value) value ∂D) +
          ∫ value, expectedSecondMoverIndependent
            (F.dist thetaH value) (PMF.pure center) value ∂D) := by
    dsimp [gap]
    change (∫ value,
      ((fun value => expectedFirstMoverUtility (PMF.pure center) value) +
        fun value => expectedSecondMoverShared (PMF.pure center) value) value -
      ((fun value => expectedFirstMoverUtility (F.dist thetaH value) value) +
        fun value => expectedSecondMoverIndependent
          (F.dist thetaH value) (PMF.pure center) value) value ∂D) = _
    rw [integral_sub (hffirst.add hfsecond) (hgfirst.add hgsecond)]
    simp only [Pi.add_apply]
    rw [integral_add hffirst hfsecond, integral_add hgfirst hgsecond]
  unfold theorem1_g_pureCenterLimit theorem1_f_pureCenterLimit outerExpected
  exact sub_pos.mp (by rw [← hgap_integral_eq]; exact hgap_integral_pos)

/--
The outer-D source-shaped Theorem 1 bridge.  Definition 1 is imposed on the
conditional finite ranking law for almost every realized profile: every atom
is continuous and differentiable at positive accuracy, the true-ranking atom
converges to one, every nonempty remaining set is weakly improved, and the
full set is strictly improved.  Definition 2 is the literal positive
conditional gain in the actual joint experiment that first draws a profile
from `D`, together with explicit joint-law regularity and positive
conditioning-event mass.  Definition 3 is its source-order ex-ante payoff
comparison.

The source leaves measurability and integrability tacit.  They are visible
here because they are needed to form the joint conditional expectation,
transport concentration through `D`, and prevent totalized integrals from
creating a crossing.  The result has one common algorithmic witness outside
the outer expectation.
-/
theorem distributional_theorem1_of_literal_outer_source_conditions
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
    (hcenter_tendsto : ∀ᵐ value ∂D,
      Tendsto (fun theta => ((F.dist theta value) center).toReal) atTop (nhds 1))
    (hstrict_order : ∀ᵐ value ∂D, StrictlyOrderedBy center value)
    (hdefinition2_regular : ∀ theta, 0 < theta →
      OuterIndependentRerankingJointRegularity F D theta)
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
      ∀ᵐ value ∂D, ∀ remaining : Finset (Candidate n), remaining.Nonempty →
        expectedBestInSet (F.dist thetaH value) value remaining ≤
          expectedBestInSet (F.dist thetaA value) value remaining)
    (hfull_set_strict : ∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
      ∀ᵐ value ∂D, StrictlyOrderedBy center value →
        expectedBestInSet (F.dist thetaH value) value Finset.univ <
          expectedBestInSet (F.dist thetaA value) value Finset.univ) :
    F.DistributionalTheorem1Target D thetaH := by
  have hatom_tendsto : ∀ᵐ value ∂D, ∀ pi : Ranking n,
      Tendsto (fun theta => ((F.dist theta value) pi).toReal) atTop
        (nhds (((PMF.pure center : PMF (Ranking n)) pi).toReal)) := by
    filter_upwards [hcenter_tendsto] with value hcenter
    exact atomwise_tendsto_pure_of_center_atom_tendsto
      (fun theta => F.dist theta value) center hcenter
  have hdefinition2_payoff : F.PrefersIndependentReranking D thetaH := by
    exact
      (F.prefersIndependentReranking_iff_jointLawDisagreementConditionalGain_pos_of_regular
        D thetaH (hdefinition2_regular thetaH hthetaH)
        (hdefinition2_event thetaH hthetaH)).mpr
        (hdefinition2_gain thetaH hthetaH)
  have houter_disagreement : 0 < F.outerDisagreementProbability D thetaH := by
    rw [← F.integral_jointDisagreementIndicator_eq_outerDisagreementProbability
      D thetaH (hdefinition2_regular thetaH hthetaH).base.ranking_atom_measurable]
    exact hdefinition2_event thetaH hthetaH
  have hgfirst : Integrable (fun value =>
      expectedFirstMoverUtility (F.dist thetaH value) value) D := by
    simpa [expectedFirstMoverUtility] using
      (integrable_outer_pmfExp_valueSelection_of_atomwise
        D F.dist thetaH firstChoice hvalue
        (fun pi => hatom_aestrongly_measurable thetaH pi))
  have hgsecond : Integrable (fun value =>
      expectedSecondMoverIndependent (F.dist thetaH value) (PMF.pure center) value) D := by
    simpa [expectedSecondMoverIndependent, secondMoverUtility] using
      (integrable_outer_pmfPairExp_valueSelection_of_atomwise
        D (fun value => F.dist thetaH value) (fun _ => PMF.pure center)
        (fun second first => bestRemainingAfter second (firstChoice first)) hvalue
        (fun pi => hatom_aestrongly_measurable thetaH pi)
        (fun _ => aestronglyMeasurable_const))
  have hffirst : Integrable (fun value =>
      expectedFirstMoverUtility (PMF.pure center) value) D := by
    simpa [expectedFirstMoverUtility] using
      (integrable_outer_pmfExp_valueSelection_of_atomwise
        D (fun _ _ => PMF.pure center) 0 firstChoice hvalue
        (fun _ => aestronglyMeasurable_const))
  have hfsecond : Integrable (fun value =>
      expectedSecondMoverShared (PMF.pure center) value) D := by
    simpa [expectedSecondMoverShared] using
      (integrable_outer_pmfExp_valueSelection_of_atomwise
        D (fun _ _ => PMF.pure center) 0 secondChoice hvalue
        (fun _ => aestronglyMeasurable_const))
  have hpure_gap : F.theorem1_g_pureCenterLimit D thetaH center <
      theorem1_f_pureCenterLimit D center :=
    theorem1_pureCenterLimit_gap_of_outer_disagreement F D thetaH center
      hgfirst hgsecond hffirst hfsecond
      (hdefinition2_regular thetaH hthetaH).base.disagreement_integrable
      hstrict_order houter_disagreement
  apply distributional_theorem1_of_outer_atomwise_regular_positive
    F D thetaH center hthetaH hvalue hatom_aestrongly_measurable
  · intro value pi theta htheta
    exact AppliedModelingLib.epsilonContinuousAt_of_continuousAt
      (hatom_continuous value theta htheta pi)
  · exact hatom_tendsto
  · exact hdefinition2_payoff
  · exact hpure_gap
  · intro thetaA hthetaHA
    exact hdefinition3 thetaA thetaH hthetaH hthetaHA
  · intro thetaA hthetaHA
    have hthetaA : 0 < thetaA := lt_trans hthetaH hthetaHA
    apply outer_algorithmAgainstHuman_gt_h_of_ae_removalMonotonicity
      F D thetaA thetaH
    · simpa [expectedFirstMoverUtility] using
        (integrable_outer_pmfExp_valueSelection_of_atomwise
          D F.dist thetaH firstChoice hvalue
          (fun pi => hatom_aestrongly_measurable thetaH pi))
    · simpa [expectedSecondMoverIndependent, secondMoverUtility] using
        (integrable_outer_pmfPairExp_valueSelection_of_atomwise
          D (fun value => F.dist thetaH value) (fun value => F.dist thetaH value)
          (fun second first => bestRemainingAfter second (firstChoice first)) hvalue
          (fun pi => hatom_aestrongly_measurable thetaH pi)
          (fun pi => hatom_aestrongly_measurable thetaH pi))
    · simpa [expectedFirstMoverUtility] using
        (integrable_outer_pmfExp_valueSelection_of_atomwise
          D F.dist thetaA firstChoice hvalue
          (fun pi => hatom_aestrongly_measurable thetaA pi))
    · simpa [expectedSecondMoverIndependent, secondMoverUtility] using
        (integrable_outer_pmfPairExp_valueSelection_of_atomwise
          D (fun value => F.dist thetaA value) (fun value => F.dist thetaH value)
          (fun second first => bestRemainingAfter second (firstChoice first)) hvalue
          (fun pi => hatom_aestrongly_measurable thetaA pi)
          (fun pi => hatom_aestrongly_measurable thetaH pi))
    · filter_upwards [hremaining_weak thetaA thetaH hthetaH hthetaHA,
        hfull_set_strict thetaA thetaH hthetaH hthetaHA, hstrict_order]
          with value hweak hfull hvalue_order
      rcases theorem1RemovalMonotonicity_fields_of_literalFiniteRemoval
          (F := F.pointFamily value) (thetaA := thetaA) (thetaH := thetaH)
          hweak (hfull hvalue_order) with
        ⟨hfirst, hremaining⟩
      exact ⟨hfirst, hremaining⟩

/--
The source-faithful universal-Definition-1 form of the outer-D Theorem 1
bridge. The source quantifies its noisy-family clauses over every admissible,
strictly center-ordered value profile, while the outer proof only consumes
their restriction to the support of `D`; this wrapper performs that restriction
rather than exposing the weaker a.e. formulation as though it were the printed
premise.

The visible regularity hypotheses are not Definition-1--3 replacements.  A
coordinate first moment and atom measurability make the outer payoff and
joint conditional experiment meaningful, `hstrict_order` records the
source's fixed rank-labelled value convention on the support of `D`, and the
positive joint event makes Definition 2's conditional expectation non-vacuous.
-/
theorem distributional_theorem1_of_universal_definition1_and_literal_outer_conditions
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
      OuterIndependentRerankingJointRegularity F D theta)
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
    F.DistributionalTheorem1Target D thetaH := by
  exact distributional_theorem1_of_literal_outer_source_conditions
    (F := F) (D := D) (center := center) (thetaH := thetaH)
    hthetaH hvalue hatom_aestrongly_measurable hatom_continuous
    hatom_differentiable
    (Filter.Eventually.of_forall hcenter_tendsto)
    hstrict_order hdefinition2_regular hdefinition2_event hdefinition2_gain
    hdefinition3
    (by
      intro thetaA thetaH hthetaH hthetaA
      exact Filter.Eventually.of_forall
        (fun value => hremaining_weak thetaA thetaH hthetaH hthetaA value))
    (by
      intro thetaA thetaH hthetaH hthetaA
      filter_upwards [hstrict_order] with value hvalue_order
      intro _
      exact hfull_set_strict thetaA thetaH hthetaH hthetaA value hvalue_order)

end DistributionalAccuracyFamily
end KR21Monoculture
