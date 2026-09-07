import KR21Monoculture.GumbelPlackettLuceExact
import KR21Monoculture.PlackettLuceOuterSource

open AppliedModelingLib MeasureTheory ProbabilityTheory

namespace KR21Monoculture

/-!
# Outer-law conditional semantics for the explicit scaled Gumbel RUM

This file concerns only the repository's concrete score construction
`unitVarianceGumbelRUMRankingPMF`: iid `-log Exp(1)` innovations, multiplied
by `sqrt 6 / pi` and divided by the positive accuracy parameter.  It does not
identify that construction with the paper's source parameterization, assert a
variance calculation for the paper's noise, or prove any strategy theorem.

At positive accuracy the concrete finite ranking PMF is proved equal to the
independently defined sequential Plackett--Luce PMF at the explicitly corrected
inverse temperature.  The rest of the file transports the *actual* outer
profile/conditional-ranking-pair measure through that equality.  In particular,
the conditional-gain result is not obtained by relabelling a theorem name or by
postulating a kernel equality.
-/

namespace DistributionalAccuracyFamily

/-- The inverse temperature of the independently defined Plackett--Luce law
matching the repository's explicitly scaled Gumbel score convention. -/
noncomputable def scaledGumbelPlackettLuceTemperature (theta : ℝ) : ℝ :=
  theta / unitVarianceGumbelScale

/-- The repository's concrete scaled-Gumbel random-utility ranking family over
a realized value profile.  The name describes the implemented construction
only; it makes no claim that this is the paper's unproved source-noise
identification. -/
noncomputable def scaledGumbelRUMDistributionalFamily {n : ℕ} :
    DistributionalAccuracyFamily n where
  dist := fun theta value => unitVarianceGumbelRUMRankingPMF theta value

@[simp] theorem scaledGumbelRUMDistributionalFamily_dist {n : ℕ}
    (theta : ℝ) (value : ValueProfile n) :
    (scaledGumbelRUMDistributionalFamily (n := n)).dist theta value =
      unitVarianceGumbelRUMRankingPMF theta value := rfl

/-- At positive accuracy, the concrete scaled-Gumbel RUM PMF is exactly the
sequential Plackett--Luce PMF at its corrected inverse temperature. -/
theorem scaledGumbelRUM_pointwise_eq_plackettLuce_correctedTemperature
    {n : ℕ} {theta : ℝ} (htheta : 0 < theta) (value : ValueProfile n) :
    (scaledGumbelRUMDistributionalFamily (n := n)).dist theta value =
      plackettLuceRankingPMF (scaledGumbelPlackettLuceTemperature theta) value := by
  exact unitVarianceGumbelRUMRankingPMF_eq_plackettLuce htheta value

/-- Atomwise measurability of the concrete scaled-Gumbel conditional PMF.  It
is derived by its proved pointwise equality to the finite Plackett--Luce
sampler, not assumed as a property of a source model. -/
theorem scaledGumbelRUM_ranking_atom_measurable
    {n : ℕ} {theta : ℝ} (htheta : 0 < theta) (ranking : Ranking n) :
    Measurable fun value : ValueProfile n =>
      (scaledGumbelRUMDistributionalFamily (n := n)).dist theta value ranking := by
  have heq :
      (fun value : ValueProfile n =>
        (scaledGumbelRUMDistributionalFamily (n := n)).dist theta value ranking) =
        fun value => plackettLuceRankingPMF
          (scaledGumbelPlackettLuceTemperature theta) value ranking := by
    funext value
    rw [scaledGumbelRUM_pointwise_eq_plackettLuce_correctedTemperature htheta]
  rw [heq]
  exact plackettLuce_ranking_atom_measurable
    (scaledGumbelPlackettLuceTemperature theta) ranking

/-- The profilewise conditionally independent ranking-pair PMFs agree under
the concrete Gumbel/Plackett--Luce bridge. -/
theorem scaledGumbelRUM_independentPairLaw_eq_plackettLuce
    {n : ℕ} {theta : ℝ} (htheta : 0 < theta) (value : ValueProfile n) :
    (scaledGumbelRUMDistributionalFamily (n := n)).independentPairLaw theta value =
      (plackettLuceDistributionalFamily (n := n)).independentPairLaw
        (scaledGumbelPlackettLuceTemperature theta) value := by
  unfold independentPairLaw
  rw [scaledGumbelRUM_pointwise_eq_plackettLuce_correctedTemperature htheta]
  rfl

/-- The two profile-indexed conditional pair kernels are equal, including the
measure representation used by the outer experiment. -/
theorem scaledGumbelRUM_independentPairKernel_eq_plackettLuce
    {n : ℕ} {theta : ℝ} (htheta : 0 < theta) :
    (scaledGumbelRUMDistributionalFamily (n := n)).independentPairKernel theta
        (fun ranking => scaledGumbelRUM_ranking_atom_measurable htheta ranking) =
      (plackettLuceDistributionalFamily (n := n)).independentPairKernel
        (scaledGumbelPlackettLuceTemperature theta)
        (fun ranking => plackettLuce_ranking_atom_measurable
          (scaledGumbelPlackettLuceTemperature theta) ranking) := by
  apply Kernel.ext
  intro value
  rw [independentPairKernel_apply, independentPairKernel_apply]
  rw [scaledGumbelRUM_independentPairLaw_eq_plackettLuce htheta]

/-- The actual outer profile/ranking-pair measures agree.  This is the
measure-level transport needed for the source's conditional event, rather than
only a pointwise equality of finite ranking probabilities. -/
theorem scaledGumbelRUM_outerIndependentPairJointLaw_eq_plackettLuce
    {n : ℕ} (D : Measure (ValueProfile n)) {theta : ℝ} (htheta : 0 < theta) :
    (scaledGumbelRUMDistributionalFamily (n := n)).outerIndependentPairJointLaw D theta
        (fun ranking => scaledGumbelRUM_ranking_atom_measurable htheta ranking) =
      (plackettLuceDistributionalFamily (n := n)).outerIndependentPairJointLaw D
        (scaledGumbelPlackettLuceTemperature theta)
        (fun ranking => plackettLuce_ranking_atom_measurable
          (scaledGumbelPlackettLuceTemperature theta) ranking) := by
  unfold outerIndependentPairJointLaw
  rw [scaledGumbelRUM_independentPairKernel_eq_plackettLuce htheta]

/-- With a probability outer profile law, the constructed scaled-Gumbel
profile/ranking-pair measure is itself a genuine probability law. -/
theorem scaledGumbelRUM_outerJointLaw_isProbability
    {n : ℕ} (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    {theta : ℝ} (htheta : 0 < theta) :
    IsProbabilityMeasure
      ((scaledGumbelRUMDistributionalFamily (n := n)).outerIndependentPairJointLaw D theta
        (fun ranking => scaledGumbelRUM_ranking_atom_measurable htheta ranking)) := by
  exact (scaledGumbelRUMDistributionalFamily (n := n)).outerIndependentPairJointLaw_isProbability
    D theta (fun ranking => scaledGumbelRUM_ranking_atom_measurable htheta ranking)

/-- The full outer experiment has a positive top-disagreement event for the
explicit scaled-Gumbel RUM. -/
theorem scaledGumbelRUM_outerJointDisagreementEvent_pos
    {n : ℕ} (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    {theta : ℝ} (htheta : 0 < theta) :
    0 < ∫ x : ValueProfile n × RankingPair n,
      (if disagreementEvent x.2 then (1 : ℝ) else 0) ∂
        (scaledGumbelRUMDistributionalFamily (n := n)).outerIndependentPairJointLaw D theta
          (fun ranking => scaledGumbelRUM_ranking_atom_measurable htheta ranking) := by
  rw [scaledGumbelRUM_outerIndependentPairJointLaw_eq_plackettLuce D htheta]
  exact plackettLuce_outerJointDisagreementEvent_pos D
    (scaledGumbelPlackettLuceTemperature theta)

/-- Under a probability outer profile law with finite coordinatewise first
moments, the literal conditional reranking gain in the actual scaled-Gumbel
profile/ranking-pair experiment is zero.  These first-moment conditions are
used for raw payoff integrability; no source-law parameterization or strategy
claim is part of this theorem. -/
theorem scaledGumbelRUM_jointLawDisagreementConditionalGain_eq_zero
    {n : ℕ} (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    {theta : ℝ} (htheta : 0 < theta)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D) :
    jointLawDisagreementConditionalGain
      (scaledGumbelRUMDistributionalFamily (n := n)) D theta
      (fun ranking => scaledGumbelRUM_ranking_atom_measurable htheta ranking) = 0 := by
  calc
    jointLawDisagreementConditionalGain
        (scaledGumbelRUMDistributionalFamily (n := n)) D theta
        (fun ranking => scaledGumbelRUM_ranking_atom_measurable htheta ranking) =
      jointLawDisagreementConditionalGain
        (plackettLuceDistributionalFamily (n := n)) D
        (scaledGumbelPlackettLuceTemperature theta)
        (fun ranking => plackettLuce_ranking_atom_measurable
          (scaledGumbelPlackettLuceTemperature theta) ranking) := by
        unfold jointLawDisagreementConditionalGain
        rw [scaledGumbelRUM_outerIndependentPairJointLaw_eq_plackettLuce D htheta]
    _ = 0 := plackettLuce_jointLawDisagreementConditionalGain_eq_zero D
      (scaledGumbelPlackettLuceTemperature theta) hvalue

/-- Complete conditional-event endpoint for the repository's concrete
scaled-Gumbel construction: the conditioning event has positive mass and the
conditional gain is zero. -/
theorem scaledGumbelRUM_source_jointConditionalGain_zero
    {n : ℕ} (D : Measure (ValueProfile n)) [IsProbabilityMeasure D]
    {theta : ℝ} (htheta : 0 < theta)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D) :
    (0 < ∫ x : ValueProfile n × RankingPair n,
      (if disagreementEvent x.2 then (1 : ℝ) else 0) ∂
        (scaledGumbelRUMDistributionalFamily (n := n)).outerIndependentPairJointLaw D theta
          (fun ranking => scaledGumbelRUM_ranking_atom_measurable htheta ranking)) ∧
      jointLawDisagreementConditionalGain
        (scaledGumbelRUMDistributionalFamily (n := n)) D theta
        (fun ranking => scaledGumbelRUM_ranking_atom_measurable htheta ranking) = 0 := by
  exact ⟨scaledGumbelRUM_outerJointDisagreementEvent_pos D htheta,
    scaledGumbelRUM_jointLawDisagreementConditionalGain_eq_zero D htheta hvalue⟩

end DistributionalAccuracyFamily

end KR21Monoculture
