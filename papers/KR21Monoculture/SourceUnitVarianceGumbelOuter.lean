import KR21Monoculture.UnitVarianceGumbelSource
import KR21Monoculture.OuterRUMSourceConcentration

/-!
# Outer and strategic consequences of the literal source Gumbel RUM

The source model in Section 3.1 draws iid Gumbel innovations from a fixed
unit-variance law and ranks `value i + epsilon i / theta`.  The preceding
modules already prove the finite source ranking law and the corresponding
positive-scale Gumbel outer experiment.  This module makes the *literal source
noise-law RUM* a `DistributionalAccuracyFamily` in its own right and transports
the outer conditional and two-firm strategy conclusions through the proved
measure-level bridge.

The standard Gamma special-value calculation needed to certify the displayed
scale as unit variance remains explicit in `UnitVarianceGumbelSource.lean`.
It is not needed for the ranking-law, outer conditional, or strategy transport:
those follow from the literal product law and score map themselves.
-/

open AppliedModelingLib MeasureTheory ProbabilityTheory
open AppliedModelingLib.SocialChoice.Ranking

namespace KR21Monoculture

noncomputable section

namespace DistributionalAccuracyFamily

/-- The profile-indexed family obtained by applying the source's literal
iid Gumbel noise product law to its displayed RUM score expression. -/
noncomputable def sourceUnitVarianceGumbelRUMDistributionalFamily {n : ℕ}
    (location : ℝ) : DistributionalAccuracyFamily n where
  dist := fun theta value => sourceUnitVarianceGumbelRUMRankingPMF location theta value

@[simp] theorem sourceUnitVarianceGumbelRUMDistributionalFamily_dist {n : ℕ}
    (location theta : ℝ) (value : ValueProfile n) :
    (sourceUnitVarianceGumbelRUMDistributionalFamily (n := n) location).dist theta value =
      sourceUnitVarianceGumbelRUMRankingPMF location theta value := rfl

/-- The literal source noise-law ranking PMF and the exponential-arrival
implementation are the same finite random-ranking experiment. -/
theorem sourceUnitVarianceGumbelRUM_pointwise_eq_commonLocation {n : ℕ}
    (location theta : ℝ) (value : ValueProfile n) :
    (sourceUnitVarianceGumbelRUMDistributionalFamily (n := n) location).dist theta value =
      (commonLocationPositiveScaleGumbelRUMDistributionalFamily (n := n)
        location unitVarianceGumbelScale).dist theta value := by
  exact (commonLocationPositiveScaleGumbelRUMRankingPMF_eq_sourceUnitVarianceGumbel
    location theta value).symm

/-- At positive source accuracy, the literal source RUM law is the sequential
Plackett--Luce law at the corrected inverse temperature. -/
theorem sourceUnitVarianceGumbelRUM_pointwise_eq_plackettLuce {n : ℕ}
    {location theta : ℝ} (htheta : 0 < theta) (value : ValueProfile n) :
    (sourceUnitVarianceGumbelRUMDistributionalFamily (n := n) location).dist theta value =
      plackettLuceRankingPMF (theta / unitVarianceGumbelScale) value := by
  exact sourceUnitVarianceGumbelRUMRankingPMF_eq_plackettLuce_corrected
    location htheta value

/-- Atomwise measurability of the literal source conditional PMF follows
from its proved equality to the sequential finite sampler. -/
theorem sourceUnitVarianceGumbelRUM_ranking_atom_measurable {n : ℕ}
    {location theta : ℝ} (htheta : 0 < theta) (ranking : Ranking n) :
    Measurable fun value : ValueProfile n =>
      (sourceUnitVarianceGumbelRUMDistributionalFamily (n := n) location).dist
        theta value ranking := by
  have heq :
      (fun value : ValueProfile n =>
        (sourceUnitVarianceGumbelRUMDistributionalFamily (n := n) location).dist
          theta value ranking) =
        fun value => plackettLuceRankingPMF
          (theta / unitVarianceGumbelScale) value ranking := by
    funext value
    rw [sourceUnitVarianceGumbelRUM_pointwise_eq_plackettLuce htheta]
  rw [heq]
  exact plackettLuce_ranking_atom_measurable
    (theta / unitVarianceGumbelScale) ranking

/-- The source-family conditionally independent ranking-pair law agrees with
the common-location exponential-arrival implementation. -/
theorem sourceUnitVarianceGumbelRUM_independentPairLaw_eq_commonLocation {n : ℕ}
    (location theta : ℝ) (value : ValueProfile n) :
    (sourceUnitVarianceGumbelRUMDistributionalFamily (n := n) location).independentPairLaw
        theta value =
      (commonLocationPositiveScaleGumbelRUMDistributionalFamily (n := n)
        location unitVarianceGumbelScale).independentPairLaw theta value := by
  unfold independentPairLaw
  rw [sourceUnitVarianceGumbelRUM_pointwise_eq_commonLocation]

/-- Equality of the actual conditional pair kernels, including their
measurability witnesses. -/
theorem sourceUnitVarianceGumbelRUM_independentPairKernel_eq_commonLocation {n : ℕ}
    {location theta : ℝ} (htheta : 0 < theta) :
    (sourceUnitVarianceGumbelRUMDistributionalFamily (n := n) location).independentPairKernel
        theta (fun ranking =>
          sourceUnitVarianceGumbelRUM_ranking_atom_measurable htheta ranking) =
      (commonLocationPositiveScaleGumbelRUMDistributionalFamily (n := n)
        location unitVarianceGumbelScale).independentPairKernel theta
        (fun ranking =>
          commonLocationPositiveScaleGumbelRUM_ranking_atom_measurable
            unitVarianceGumbelScale_pos htheta ranking) := by
  apply Kernel.ext
  intro value
  rw [independentPairKernel_apply, independentPairKernel_apply]
  rw [sourceUnitVarianceGumbelRUM_independentPairLaw_eq_commonLocation]

/-- The complete outer profile/ranking-pair measures coincide.  This is the
bridge needed for the source conditional event; a pointwise PMF equality alone
would not establish it. -/
theorem sourceUnitVarianceGumbelRUM_outerIndependentPairJointLaw_eq_commonLocation
    {n : ℕ} (D : Measure (ValueProfile n)) {location theta : ℝ}
    (htheta : 0 < theta) :
    (sourceUnitVarianceGumbelRUMDistributionalFamily (n := n) location).outerIndependentPairJointLaw D theta
        (fun ranking => sourceUnitVarianceGumbelRUM_ranking_atom_measurable
          htheta ranking) =
      (commonLocationPositiveScaleGumbelRUMDistributionalFamily (n := n)
        location unitVarianceGumbelScale).outerIndependentPairJointLaw D theta
        (fun ranking => commonLocationPositiveScaleGumbelRUM_ranking_atom_measurable
          unitVarianceGumbelScale_pos htheta ranking) := by
  unfold outerIndependentPairJointLaw
  rw [sourceUnitVarianceGumbelRUM_independentPairKernel_eq_commonLocation htheta]

/-- The literal source RUM's outer experiment has positive top-choice
disagreement mass under every probability law on value profiles. -/
theorem sourceUnitVarianceGumbelRUM_outerJointDisagreementEvent_pos {n : ℕ}
    (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    {location theta : ℝ} (htheta : 0 < theta) :
    0 < ∫ x : ValueProfile n × RankingPair n,
      (if disagreementEvent x.2 then (1 : ℝ) else 0) ∂
        (sourceUnitVarianceGumbelRUMDistributionalFamily (n := n) location).outerIndependentPairJointLaw D theta
          (fun ranking => sourceUnitVarianceGumbelRUM_ranking_atom_measurable
            htheta ranking) := by
  rw [sourceUnitVarianceGumbelRUM_outerIndependentPairJointLaw_eq_commonLocation
    D htheta]
  exact commonLocationPositiveScaleGumbelRUM_outerJointDisagreementEvent_pos D
    unitVarianceGumbelScale_pos htheta

/-- With finite coordinatewise first moments, the literal source RUM has zero
actual conditional reranking gain under the outer-then-conditionally-iid
experiment. -/
theorem sourceUnitVarianceGumbelRUM_jointLawDisagreementConditionalGain_eq_zero
    {n : ℕ} (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    {location theta : ℝ} (htheta : 0 < theta)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D) :
    jointLawDisagreementConditionalGain
      (sourceUnitVarianceGumbelRUMDistributionalFamily (n := n) location) D theta
      (fun ranking => sourceUnitVarianceGumbelRUM_ranking_atom_measurable
        htheta ranking) = 0 := by
  calc
    jointLawDisagreementConditionalGain
        (sourceUnitVarianceGumbelRUMDistributionalFamily (n := n) location) D theta
        (fun ranking => sourceUnitVarianceGumbelRUM_ranking_atom_measurable
          htheta ranking) =
      jointLawDisagreementConditionalGain
        (commonLocationPositiveScaleGumbelRUMDistributionalFamily (n := n)
          location unitVarianceGumbelScale) D theta
        (fun ranking => commonLocationPositiveScaleGumbelRUM_ranking_atom_measurable
          unitVarianceGumbelScale_pos htheta ranking) := by
        unfold jointLawDisagreementConditionalGain
        rw [sourceUnitVarianceGumbelRUM_outerIndependentPairJointLaw_eq_commonLocation
          D htheta]
    _ = 0 := commonLocationPositiveScaleGumbelRUM_jointLawDisagreementConditionalGain_eq_zero
      D unitVarianceGumbelScale_pos htheta hvalue

/-- The source RUM also has the literal outer payoff equality used in the
paper's `U_AH(theta, theta) = U_AA(theta, theta)` sentence.  Integrability is
proved from the coordinate first moments and atomwise kernel measurability,
not assumed as an unnamed property of the conditional expectation. -/
theorem sourceUnitVarianceGumbelRUM_outer_payoff_identity
    {n : ℕ} (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    {location theta : ℝ} (htheta : 0 < theta)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D) :
    Integrable (fun value => expectedSecondMoverIndependent
      ((sourceUnitVarianceGumbelRUMDistributionalFamily (n := n) location).dist theta value)
      ((sourceUnitVarianceGumbelRUMDistributionalFamily (n := n) location).dist theta value)
      value) D ∧
    Integrable (fun value => expectedSecondMoverShared
      ((sourceUnitVarianceGumbelRUMDistributionalFamily (n := n) location).dist theta value)
      value) D ∧
    outerExpected D (fun value => expectedSecondMoverIndependent
      ((sourceUnitVarianceGumbelRUMDistributionalFamily (n := n) location).dist theta value)
      ((sourceUnitVarianceGumbelRUMDistributionalFamily (n := n) location).dist theta value)
      value) =
      outerExpected D (fun value => expectedSecondMoverShared
        ((sourceUnitVarianceGumbelRUMDistributionalFamily (n := n) location).dist theta value)
        value) := by
  let F := sourceUnitVarianceGumbelRUMDistributionalFamily (n := n) location
  have hatom : ∀ pi : Ranking n,
      AEStronglyMeasurable (fun value : ValueProfile n =>
        ((F.dist theta value) pi).toReal) D := by
    intro pi
    simpa [F] using
      (sourceUnitVarianceGumbelRUM_ranking_atom_measurable
        (n := n) (location := location) htheta pi).ennreal_toReal.aestronglyMeasurable
  constructor
  · change Integrable (fun value => expectedSecondMoverIndependent
      (F.dist theta value) (F.dist theta value) value) D
    simpa [expectedSecondMoverIndependent, secondMoverUtility] using
      (integrable_outer_pmfPairExp_valueSelection_of_atomwise
        D (fun value => F.dist theta value) (fun value => F.dist theta value)
        (fun second first => bestRemainingAfter second (firstChoice first)) hvalue hatom hatom)
  constructor
  · change Integrable (fun value => expectedSecondMoverShared (F.dist theta value) value) D
    simpa [expectedSecondMoverShared] using
      (integrable_outer_pmfExp_valueSelection_of_atomwise
        D F.dist theta secondChoice hvalue hatom)
  unfold outerExpected
  apply integral_congr_ae
  filter_upwards [] with value
  change expectedSecondMoverIndependent (F.dist theta value) (F.dist theta value) value =
    expectedSecondMoverShared (F.dist theta value) value
  rw [sourceUnitVarianceGumbelRUM_pointwise_eq_plackettLuce htheta]
  have hzero := plackettLuce_pointwise_rerankingGain_eq_zero
    (n := n) (theta / unitVarianceGumbelScale) value
  rw [← expectedSecondMoverIndependent_sub_shared_eq_expectedRerankingGain] at hzero
  linarith

/-- Complete source-RUM form of the Section 3.1 conditional conclusion. -/
theorem sourceUnitVarianceGumbelRUM_source_jointConditionalGain_zero {n : ℕ}
    (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    {location theta : ℝ} (htheta : 0 < theta)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D) :
    (0 < ∫ x : ValueProfile n × RankingPair n,
      (if disagreementEvent x.2 then (1 : ℝ) else 0) ∂
        (sourceUnitVarianceGumbelRUMDistributionalFamily (n := n) location).outerIndependentPairJointLaw D theta
          (fun ranking => sourceUnitVarianceGumbelRUM_ranking_atom_measurable
            htheta ranking)) ∧
      jointLawDisagreementConditionalGain
        (sourceUnitVarianceGumbelRUMDistributionalFamily (n := n) location) D theta
        (fun ranking => sourceUnitVarianceGumbelRUM_ranking_atom_measurable
          htheta ranking) = 0 := by
  exact ⟨sourceUnitVarianceGumbelRUM_outerJointDisagreementEvent_pos D htheta,
    sourceUnitVarianceGumbelRUM_jointLawDisagreementConditionalGain_eq_zero
      D htheta hvalue⟩

end DistributionalAccuracyFamily

/-- The source RUM's Section 3.1 strategy conclusion.  The choice labels are
not used as a proxy for quality: the conclusion is the explicit case split on
the two positive accuracy parameters. -/
theorem sourceUnitVarianceGumbel_best_available_weakly_dominates {n : ℕ}
    {location thetaA thetaH : ℝ}
    (value : Candidate n → ℝ)
    (hthetaA : 0 < thetaA) (hthetaH : 0 < thetaH) :
    let M : Model n :=
      { algorithmRanking := sourceUnitVarianceGumbelRUMRankingPMF location thetaA value
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
            Model.payoffAgainst M Strategy.algorithm Strategy.human) := by
  rw [← commonLocationPositiveScaleGumbelRUMRankingPMF_eq_sourceUnitVarianceGumbel
    location thetaA value,
    ← commonLocationPositiveScaleGumbelRUMRankingPMF_eq_sourceUnitVarianceGumbel
      location thetaH value]
  exact commonLocationPositiveScaleGumbel_best_available_weakly_dominates
    unitVarianceGumbelScale_pos value hthetaA hthetaH

end

end KR21Monoculture
