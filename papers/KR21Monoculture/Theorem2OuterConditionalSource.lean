import KR21Monoculture.Theorem2Distributional
import KR21Monoculture.OuterConditional

open AppliedModelingLib MeasureTheory ProbabilityTheory

namespace KR21Monoculture

/-!
# Actual outer-law conditional semantics for KR21 Theorem 2

The pointwise Gaussian and Laplace proofs in Appendix C establish the two
payoff inequalities at one ordered three-candidate value profile.  The paper's
Definitions 2 and 3 first draw that profile from an outer law `D`.  This file
does the mathematically separate transport to that experiment.

In particular, Definition 2 is not represented merely as a comparison of two
iterated scalar payoffs: its conclusion below is positivity of the conditional
gain under the actual joint law that first samples a value profile and then
samples two conditionally independent rankings.  Measurability and payoff
integrability are explicit inputs; positive mass of the joint conditioning
event is derived from the strict pointwise preference.  None of these analytic
facts is attributed to the source statement or inferred from a Lean declaration
name.
-/

/-- The source Gaussian RUM law as a distributional family over realized
three-candidate cardinal profiles.  At positive `theta`, its score noise has
standard deviation `1 / theta`. -/
noncomputable def gaussianThreeCandidateDistributionalFamily :
    DistributionalAccuracyFamily 1 where
  dist := fun theta value =>
    gaussianThreeCandidateRankingLaw theta
      (value (0 : Candidate 1)) (value (1 : Candidate 1))
      (value (2 : Candidate 1))

@[simp] theorem gaussianThreeCandidateDistributionalFamily_dist
    (theta : ℝ) (value : ValueProfile 1) :
    gaussianThreeCandidateDistributionalFamily.dist theta value =
      gaussianThreeCandidateRankingLaw theta
        (value (0 : Candidate 1)) (value (1 : Candidate 1))
        (value (2 : Candidate 1)) := rfl

/-- Canonical rate-parameterized Laplace law over realized three-candidate
cardinal profiles. Its definition is totalized outside the positive rate
domain. The literal source unit-variance RUM family is the distinct
`sourceUnitVarianceLaplaceThreeCandidateDistributionalFamily` in
`LaplaceSourceNormalization.lean`, with rate `sqrt 2 * theta`. -/
noncomputable def laplaceThreeCandidateDistributionalFamily :
    DistributionalAccuracyFamily 1 where
  dist := fun theta value =>
    laplaceThreeCandidateRankingLaw theta
      (value (0 : Candidate 1)) (value (1 : Candidate 1))
      (value (2 : Candidate 1))

@[simp] theorem laplaceThreeCandidateDistributionalFamily_dist
    (theta : ℝ) (value : ValueProfile 1) :
    laplaceThreeCandidateDistributionalFamily.dist theta value =
      laplaceThreeCandidateRankingLaw theta
        (value (0 : Candidate 1)) (value (1 : Candidate 1))
        (value (2 : Candidate 1)) := rfl

namespace DistributionalAccuracyFamily

/-- Almost-everywhere strict inequalities integrate strictly under a
probability measure when both sides are integrable. -/
theorem integral_lt_integral_of_ae_lt_of_probability
    {α : Type*} [MeasurableSpace α]
    (mu : Measure α) [IsProbabilityMeasure mu]
    {f g : α → ℝ}
    (hf : Integrable f mu) (hg : Integrable g mu)
    (hlt : ∀ᵐ a ∂mu, f a < g a) :
    (∫ a, f a ∂mu) < ∫ a, g a ∂mu := by
  have hdiff_int : Integrable (fun a => g a - f a) mu := hg.sub hf
  have hdiff_nonneg : 0 ≤ᵐ[mu] fun a => g a - f a := by
    filter_upwards [hlt] with a ha
    exact sub_nonneg.mpr (le_of_lt ha)
  have hsupport_ae : ∀ᵐ a ∂mu, a ∈ Function.support (fun a => g a - f a) := by
    filter_upwards [hlt] with a ha
    change g a - f a ≠ 0
    exact ne_of_gt (sub_pos.mpr ha)
  have hsupport_pos : 0 < mu (Function.support fun a => g a - f a) := by
    apply (pos_iff_ne_zero).2
    intro hzero
    have hcompl : mu (Function.support (fun a => g a - f a))ᶜ = 0 :=
      (mem_ae_iff.mp hsupport_ae)
    have huniv : mu Set.univ = 0 := by
      rw [← Set.union_compl_self (Function.support fun a => g a - f a)]
      exact measure_union_null hzero hcompl
    rw [measure_univ] at huniv
    norm_num at huniv
  have hpos : 0 < ∫ a, g a - f a ∂mu :=
    (integral_pos_iff_support_of_nonneg_ae hdiff_nonneg hdiff_int).2 hsupport_pos
  have hsub :
      (∫ a, g a - f a ∂mu) = (∫ a, g a ∂mu) - ∫ a, f a ∂mu :=
    integral_sub hg hf
  linarith

/-- A strict finite Definition-2 payoff preference cannot occur when two iid
ranking draws never disagree at the first position.  This removes a separate
nondegeneracy premise from the outer conditional-event bridge below. -/
theorem disagreementProb_pos_of_prefersIndependentReranking
    {n : ℕ} (mu : PMF (Ranking n)) (value : Candidate n → ℝ)
    (hpref : Model.PrefersIndependentReranking mu value) :
    0 < disagreementProb mu := by
  have hprob_eq :
      disagreementProb mu =
        AppliedModelingLib.pmfProb (AppliedModelingLib.pmfProd mu mu) disagreementEvent := by
    change AppliedModelingLib.pmfPairExp mu mu
        (fun pi sigma => if disagreementEvent (pi, sigma) then (1 : ℝ) else 0) =
      AppliedModelingLib.pmfExp (AppliedModelingLib.pmfProd mu mu)
        (fun pair => if disagreementEvent pair then (1 : ℝ) else 0)
    exact (AppliedModelingLib.pmfExp_pmfProd_eq_pairExp mu mu
      (fun pair => if disagreementEvent pair then (1 : ℝ) else 0)).symm
  by_contra hnot
  have hzero : disagreementProb mu = 0 :=
    le_antisymm (le_of_not_gt hnot) (by
      rw [hprob_eq]
      exact AppliedModelingLib.pmfProb_nonneg _ _)
  have hmass_zero : ∀ pair : RankingPair n, disagreementEvent pair →
      ((AppliedModelingLib.pmfProd mu mu) pair).toReal = 0 := by
    intro pair hpair
    by_contra hmass_ne
    have hmass_pos : 0 < ((AppliedModelingLib.pmfProd mu mu) pair).toReal :=
      lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hmass_ne)
    have hprob_pos :
        0 < AppliedModelingLib.pmfProb (AppliedModelingLib.pmfProd mu mu) disagreementEvent :=
      AppliedModelingLib.pmfProb_pos_of_mass (AppliedModelingLib.pmfProd mu mu)
        disagreementEvent pair hpair hmass_pos
    rw [← hprob_eq, hzero] at hprob_pos
    exact (lt_irrefl (0 : ℝ)) hprob_pos
  have hgain_zero : expectedRerankingGain mu value = 0 := by
    rw [expectedRerankingGain_eq_pairIndicatorExp]
    unfold AppliedModelingLib.pmfPairIndicatorExp
    calc
      AppliedModelingLib.pmfPairExp mu mu
          (fun pi sigma => if disagreementEvent (pi, sigma) then
            pairRerankingGain value (pi, sigma) else 0) =
        AppliedModelingLib.pmfExp (AppliedModelingLib.pmfProd mu mu)
          (fun pair => if disagreementEvent pair then
            pairRerankingGain value pair else 0) :=
          (AppliedModelingLib.pmfExp_pmfProd_eq_pairExp mu mu
            (fun pair => if disagreementEvent pair then
              pairRerankingGain value pair else 0)).symm
      _ = 0 := by
        unfold AppliedModelingLib.pmfExp
        refine Finset.sum_eq_zero ?_
        intro pair _
        by_cases hpair : disagreementEvent pair
        · change ((AppliedModelingLib.pmfProd mu mu) pair).toReal *
              (if disagreementEvent pair then pairRerankingGain value pair else 0) = 0
          rw [if_pos hpair, hmass_zero pair hpair]
          ring
        · simp [hpair]
  rw [prefersIndependentReranking_iff_expectedRerankingGain_pos] at hpref
  linarith

/-- An almost-everywhere pointwise Definition-2 comparison transports to the
outer payoff comparison when both payoff variables are integrable.  Unlike the
older universal bridge, this does not impose conditions on profiles outside
the support of `D`. -/
theorem prefersIndependentReranking_of_ae_pointwise
    {n : ℕ} (F : DistributionalAccuracyFamily n)
    (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    (theta : ℝ)
    (hshared : Integrable
      (fun value => expectedSecondMoverShared (F.dist theta value) value) D)
    (hindependent : Integrable
      (fun value => expectedSecondMoverIndependent
        (F.dist theta value) (F.dist theta value) value) D)
    (hpoint : ∀ᵐ value ∂D,
      Model.PrefersIndependentReranking (F.dist theta value) value) :
    F.PrefersIndependentReranking D theta := by
  unfold PrefersIndependentReranking outerExpected
  exact integral_lt_integral_of_ae_lt_of_probability D hshared hindependent hpoint

/-- An almost-everywhere pointwise Definition-3 comparison transports to the
outer payoff comparison when its two payoff variables are integrable. -/
theorem prefersWeakerCompetition_of_ae_pointwise
    {n : ℕ} (F : DistributionalAccuracyFamily n)
    (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    (thetaA thetaH : ℝ)
    (hbetter : Integrable
      (fun value => expectedSecondMoverIndependent
        (F.dist thetaH value) (F.dist thetaA value) value) D)
    (hworse : Integrable
      (fun value => expectedSecondMoverIndependent
        (F.dist thetaH value) (F.dist thetaH value) value) D)
    (hpoint : ∀ᵐ value ∂D,
      Model.PrefersWeakerCompetition
        (F.dist thetaA value) (F.dist thetaH value) value) :
    F.PrefersWeakerCompetition D thetaA thetaH := by
  unfold PrefersWeakerCompetition outerExpected
  exact integral_lt_integral_of_ae_lt_of_probability D hbetter hworse hpoint

/-- Under the actual outer experiment, almost-everywhere strict pointwise
Definition-2 preference itself forces positive mass on top disagreement.  The
proof first derives positive finite-PMF disagreement on each relevant profile,
then integrates that nonnegative probability under `D`. -/
theorem outerJointDisagreementEvent_pos_of_ae_pointwise_preference
    {n : ℕ} (F : DistributionalAccuracyFamily n)
    (D : Measure (ValueProfile n)) (theta : ℝ)
    (regularity : OuterIndependentRerankingJointRegularity F D theta)
    (hpoint : ∀ᵐ value ∂D,
      Model.PrefersIndependentReranking (F.dist theta value) value) :
    0 < ∫ x : ValueProfile n × RankingPair n,
      (if disagreementEvent x.2 then (1 : ℝ) else 0) ∂
        F.outerIndependentPairJointLaw D theta
          regularity.base.ranking_atom_measurable := by
  letI : IsProbabilityMeasure D := regularity.base.outer_is_probability
  have hfiber : ∀ᵐ value ∂D, 0 < disagreementProb (F.dist theta value) := by
    filter_upwards [hpoint] with value hvalue
    exact disagreementProb_pos_of_prefersIndependentReranking
      (F.dist theta value) value hvalue
  have houter : 0 < F.outerDisagreementProbability D theta := by
    rw [F.outerDisagreementProbability_eq_outerExpected]
    have hstrict := integral_lt_integral_of_ae_lt_of_probability D
      (integrable_const (0 : ℝ)) regularity.base.disagreement_integrable hfiber
    simpa [outerExpected] using hstrict
  rw [F.integral_jointDisagreementIndicator_eq_outerDisagreementProbability
    D theta regularity.base.ranking_atom_measurable]
  exact houter

/-- The actual conditional-event conclusion of Definition 2 follows from an
almost-everywhere pointwise preference proof and explicit joint regularity.
The positive-event fact is derived rather than assumed, so Lean's totalized
conditional expectation cannot hide a zero-mass conditioning event. -/
theorem jointLawDisagreementConditionalGain_pos_of_ae_pointwise_preference
    {n : ℕ} (F : DistributionalAccuracyFamily n)
    (D : Measure (ValueProfile n)) (theta : ℝ)
    (regularity : OuterIndependentRerankingJointRegularity F D theta)
    (hpoint : ∀ᵐ value ∂D,
      Model.PrefersIndependentReranking (F.dist theta value) value) :
    0 < F.jointLawDisagreementConditionalGain D theta
      regularity.base.ranking_atom_measurable := by
  letI : IsProbabilityMeasure D := regularity.base.outer_is_probability
  have hpref : F.PrefersIndependentReranking D theta :=
    F.prefersIndependentReranking_of_ae_pointwise D theta
      regularity.base.shared_payoff_integrable
      regularity.base.independent_payoff_integrable hpoint
  have hdisagreement :=
    F.outerJointDisagreementEvent_pos_of_ae_pointwise_preference
      D theta regularity hpoint
  exact
    (F.prefersIndependentReranking_iff_jointLawDisagreementConditionalGain_pos_of_regular
      D theta regularity hdisagreement).mp hpref

end DistributionalAccuracyFamily

/-- The Gaussian Appendix-C Definition-2 result, averaged over an arbitrary
outer probability law whose realized profiles are ordered almost everywhere.
The integrability assumptions are exactly those needed for this outer payoff
comparison to be defined. -/
theorem gaussianThreeCandidate_outer_prefersIndependentReranking
    (D : Measure (ValueProfile 1)) [IsProbabilityMeasure D]
    (theta : ℝ) (htheta : 0 < theta)
    (horder : ∀ᵐ value ∂D,
      value (1 : Candidate 1) < value (0 : Candidate 1) ∧
        value (2 : Candidate 1) < value (1 : Candidate 1))
    (hshared : Integrable (fun value => expectedSecondMoverShared
      (gaussianThreeCandidateDistributionalFamily.dist theta value) value) D)
    (hindependent : Integrable (fun value => expectedSecondMoverIndependent
      (gaussianThreeCandidateDistributionalFamily.dist theta value)
      (gaussianThreeCandidateDistributionalFamily.dist theta value) value) D) :
    gaussianThreeCandidateDistributionalFamily.PrefersIndependentReranking D theta := by
  apply DistributionalAccuracyFamily.prefersIndependentReranking_of_ae_pointwise
    gaussianThreeCandidateDistributionalFamily D theta hshared hindependent
  filter_upwards [horder] with value hvalue
  exact gaussianThreeCandidate_prefersIndependent htheta hvalue.1 hvalue.2

/-- The Gaussian Appendix-C Definition-3 result, averaged over an arbitrary
outer probability law.  The strict order condition is only required almost
everywhere under `D`; the two integrability hypotheses are visible. -/
theorem gaussianThreeCandidate_outer_prefersWeakerCompetition
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
    gaussianThreeCandidateDistributionalFamily.PrefersWeakerCompetition D thetaA thetaH := by
  apply DistributionalAccuracyFamily.prefersWeakerCompetition_of_ae_pointwise
    gaussianThreeCandidateDistributionalFamily D thetaA thetaH hbetter hworse
  filter_upwards [horder] with value hvalue
  exact gaussianThreeCandidate_prefersWeaker
    hthetaH hthetaHA hvalue.1 hvalue.2

/-- The Gaussian Definition-2 result in the source's actual conditional
experiment.  The draw order is literal: sample `value` from `D`, then sample
two conditionally independent Gaussian RUM rankings. -/
theorem gaussianThreeCandidate_outer_jointLawDisagreementConditionalGain_pos
    (D : Measure (ValueProfile 1)) [IsProbabilityMeasure D]
    (theta : ℝ) (htheta : 0 < theta)
    (horder : ∀ᵐ value ∂D,
      value (1 : Candidate 1) < value (0 : Candidate 1) ∧
        value (2 : Candidate 1) < value (1 : Candidate 1))
    (regularity : DistributionalAccuracyFamily.OuterIndependentRerankingJointRegularity
      gaussianThreeCandidateDistributionalFamily D theta) :
    0 < gaussianThreeCandidateDistributionalFamily.jointLawDisagreementConditionalGain
      D theta regularity.base.ranking_atom_measurable := by
  apply DistributionalAccuracyFamily.jointLawDisagreementConditionalGain_pos_of_ae_pointwise_preference
    gaussianThreeCandidateDistributionalFamily D theta regularity
  · filter_upwards [horder] with value hvalue
    exact gaussianThreeCandidate_prefersIndependent htheta hvalue.1 hvalue.2

/-- The Laplace Appendix-C Definition-2 result, averaged over an arbitrary
outer probability law with almost-everywhere ordered profiles. -/
theorem laplaceThreeCandidate_outer_prefersIndependentReranking
    (D : Measure (ValueProfile 1)) [IsProbabilityMeasure D]
    (theta : ℝ) (htheta : 0 < theta)
    (horder : ∀ᵐ value ∂D,
      value (1 : Candidate 1) < value (0 : Candidate 1) ∧
        value (2 : Candidate 1) < value (1 : Candidate 1))
    (hshared : Integrable (fun value => expectedSecondMoverShared
      (laplaceThreeCandidateDistributionalFamily.dist theta value) value) D)
    (hindependent : Integrable (fun value => expectedSecondMoverIndependent
      (laplaceThreeCandidateDistributionalFamily.dist theta value)
      (laplaceThreeCandidateDistributionalFamily.dist theta value) value) D) :
    laplaceThreeCandidateDistributionalFamily.PrefersIndependentReranking D theta := by
  apply DistributionalAccuracyFamily.prefersIndependentReranking_of_ae_pointwise
    laplaceThreeCandidateDistributionalFamily D theta hshared hindependent
  filter_upwards [horder] with value hvalue
  exact laplaceThreeCandidate_prefersIndependent htheta hvalue.1 hvalue.2

/-- The Laplace Appendix-C Definition-3 result, averaged over an arbitrary
outer probability law with all integrability obligations exposed. -/
theorem laplaceThreeCandidate_outer_prefersWeakerCompetition
    (D : Measure (ValueProfile 1)) [IsProbabilityMeasure D]
    (thetaA thetaH : ℝ) (hthetaH : 0 < thetaH) (hthetaHA : thetaH < thetaA)
    (horder : ∀ᵐ value ∂D,
      value (1 : Candidate 1) < value (0 : Candidate 1) ∧
        value (2 : Candidate 1) < value (1 : Candidate 1))
    (hbetter : Integrable (fun value => expectedSecondMoverIndependent
      (laplaceThreeCandidateDistributionalFamily.dist thetaH value)
      (laplaceThreeCandidateDistributionalFamily.dist thetaA value) value) D)
    (hworse : Integrable (fun value => expectedSecondMoverIndependent
      (laplaceThreeCandidateDistributionalFamily.dist thetaH value)
      (laplaceThreeCandidateDistributionalFamily.dist thetaH value) value) D) :
    laplaceThreeCandidateDistributionalFamily.PrefersWeakerCompetition D thetaA thetaH := by
  apply DistributionalAccuracyFamily.prefersWeakerCompetition_of_ae_pointwise
    laplaceThreeCandidateDistributionalFamily D thetaA thetaH hbetter hworse
  filter_upwards [horder] with value hvalue
  exact laplaceThreeCandidate_prefersWeaker
    hthetaH hthetaHA hvalue.1 hvalue.2

/-- The Laplace Definition-2 result in the source's actual value-plus-two-iid
ranking experiment. -/
theorem laplaceThreeCandidate_outer_jointLawDisagreementConditionalGain_pos
    (D : Measure (ValueProfile 1)) [IsProbabilityMeasure D]
    (theta : ℝ) (htheta : 0 < theta)
    (horder : ∀ᵐ value ∂D,
      value (1 : Candidate 1) < value (0 : Candidate 1) ∧
        value (2 : Candidate 1) < value (1 : Candidate 1))
    (regularity : DistributionalAccuracyFamily.OuterIndependentRerankingJointRegularity
      laplaceThreeCandidateDistributionalFamily D theta) :
    0 < laplaceThreeCandidateDistributionalFamily.jointLawDisagreementConditionalGain
      D theta regularity.base.ranking_atom_measurable := by
  apply DistributionalAccuracyFamily.jointLawDisagreementConditionalGain_pos_of_ae_pointwise_preference
    laplaceThreeCandidateDistributionalFamily D theta regularity
  · filter_upwards [horder] with value hvalue
    exact laplaceThreeCandidate_prefersIndependent htheta hvalue.1 hvalue.2

end KR21Monoculture
