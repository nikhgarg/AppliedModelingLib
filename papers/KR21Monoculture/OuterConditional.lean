import KR21Monoculture.Distributional
import KR21Monoculture.ConditionalForm
import AppliedModelingLib.Foundations.Probability.IndependentProduct
import Mathlib.Probability.Kernel.Composition.Prod

open AppliedModelingLib MeasureTheory ProbabilityTheory

namespace KR21Monoculture
namespace DistributionalAccuracyFamily

/-!
# Outer conditional-event form of KR21 Definition 2

For a realized value profile, Definition 2 conditions the gain from an
independent reranking on the two ranking draws disagreeing at the top choice.
The source first draws that profile from `D`, so the conditioning event is an
event in the joint experiment, rather than a separate conditional expectation
at each profile.

`DistributionalAccuracyFamily` deliberately does not build measurability into
its data.  The scalar definitions below therefore use the exact iterated law:
draw a profile from `D`, then draw two conditionally independent rankings from
the finite PMF at that profile.  `OuterIndependentRerankingRegularity` records
the measurable/integrable hypotheses needed to regard this as a genuine joint
probability experiment.  No theorem below takes the conditional-gain/payoff-gap
identity as an assumption.
-/

/-- The conditional pair law at one realized profile: two independent draws. -/
noncomputable def independentPairLaw {n : ℕ} (F : DistributionalAccuracyFamily n)
    (theta : ℝ) (value : ValueProfile n) : PMF (RankingPair n) :=
  AppliedModelingLib.pmfProd (F.dist theta value) (F.dist theta value)

/-- The iterated expectation in the outer-profile and conditional-pair experiment. -/
noncomputable def outerPairExpected {n : ℕ} (F : DistributionalAccuracyFamily n)
    (D : Measure (ValueProfile n)) (theta : ℝ)
    (u : ValueProfile n → RankingPair n → ℝ) : ℝ :=
  outerExpected D (fun value =>
    pmfPairExp (F.dist theta value) (F.dist theta value)
      (fun pi sigma => u value (pi, sigma)))

/-- Probability of top-choice disagreement in the full iterated experiment. -/
noncomputable def outerDisagreementProbability {n : ℕ}
    (F : DistributionalAccuracyFamily n) (D : Measure (ValueProfile n))
    (theta : ℝ) : ℝ :=
  outerPairExpected F D theta (fun _ pair =>
    if disagreementEvent pair then 1 else 0)

/-- The unnormalized gain restricted to the full experiment's disagreement event. -/
noncomputable def outerDisagreementGainNumerator {n : ℕ}
    (F : DistributionalAccuracyFamily n) (D : Measure (ValueProfile n))
    (theta : ℝ) : ℝ :=
  outerPairExpected F D theta (fun value pair =>
    if disagreementEvent pair then pairRerankingGain value pair else 0)

/-- Conditional gain in the full experiment, defined as zero on a zero-mass event. -/
noncomputable def outerDisagreementConditionalGain {n : ℕ}
    (F : DistributionalAccuracyFamily n) (D : Measure (ValueProfile n))
    (theta : ℝ) : ℝ :=
  let p := outerDisagreementProbability F D theta
  if p = 0 then 0 else outerDisagreementGainNumerator F D theta / p

/-- A deterministic outer value law reduces the iterated two-ranking
experiment to the ordinary finite pair expectation at that value profile. -/
theorem outerPairExpected_dirac {n : ℕ}
    (F : DistributionalAccuracyFamily n) (value : ValueProfile n)
    (theta : ℝ) (u : ValueProfile n → RankingPair n → ℝ) :
    F.outerPairExpected (Measure.dirac value) theta u =
      AppliedModelingLib.pmfPairExp (F.dist theta value) (F.dist theta value)
        (fun pi sigma => u value (pi, sigma)) := by
  unfold outerPairExpected outerExpected
  simp

/-- Under a deterministic candidate profile, outer top-disagreement mass is
exactly the finite-PMF disagreement probability. -/
theorem outerDisagreementProbability_dirac {n : ℕ}
    (F : DistributionalAccuracyFamily n) (value : ValueProfile n)
    (theta : ℝ) :
    F.outerDisagreementProbability (Measure.dirac value) theta =
      disagreementProb (F.dist theta value) := by
  unfold outerDisagreementProbability
  rw [outerPairExpected_dirac]
  rfl

/-- Under a deterministic candidate profile, the outer restricted gain is the
ordinary finite-PMF reranking gain. -/
theorem outerDisagreementGainNumerator_dirac {n : ℕ}
    (F : DistributionalAccuracyFamily n) (value : ValueProfile n)
    (theta : ℝ) :
    F.outerDisagreementGainNumerator (Measure.dirac value) theta =
      expectedRerankingGain (F.dist theta value) value := by
  unfold outerDisagreementGainNumerator
  rw [outerPairExpected_dirac]
  rw [expectedRerankingGain_eq_pairIndicatorExp]
  rfl

/-- The totalized conditional-gain conventions agree for a point-mass outer
law, including the zero-disagreement case. -/
theorem outerDisagreementConditionalGain_dirac {n : ℕ}
    (F : DistributionalAccuracyFamily n) (value : ValueProfile n)
    (theta : ℝ) :
    F.outerDisagreementConditionalGain (Measure.dirac value) theta =
      disagreementConditionalGain (F.dist theta value) value := by
  unfold outerDisagreementConditionalGain disagreementConditionalGain
  rw [outerDisagreementProbability_dirac,
    outerDisagreementGainNumerator_dirac]
  rw [expectedRerankingGain_eq_pairIndicatorExp]
  unfold AppliedModelingLib.SocialChoice.Ranking.disagreementConditionalGain
  rfl

/--
Regularity for the full Definition-2 experiment.  Atomwise measurability is
what permits the profile-indexed finite PMFs to be assembled into a Markov
kernel.  The three integrability fields prevent Lean's totalized integral from
silently assigning an undefined expectation the value zero.
-/
structure OuterIndependentRerankingRegularity {n : ℕ}
    (F : DistributionalAccuracyFamily n) (D : Measure (ValueProfile n))
    (theta : ℝ) : Prop where
  outer_is_probability : IsProbabilityMeasure D
  ranking_atom_measurable : ∀ ranking : Ranking n,
    Measurable fun value => F.dist theta value ranking
  disagreement_integrable : Integrable
    (fun value => disagreementProb (F.dist theta value)) D
  shared_payoff_integrable : Integrable
    (fun value => expectedSecondMoverShared (F.dist theta value) value) D
  independent_payoff_integrable : Integrable
    (fun value => expectedSecondMoverIndependent
      (F.dist theta value) (F.dist theta value) value) D

/-- The conditional pair PMFs form a measurable kernel under atomwise regularity. -/
theorem measurable_independentPairLaw_toMeasure {n : ℕ}
    (F : DistributionalAccuracyFamily n) (theta : ℝ)
    (hatom : ∀ ranking : Ranking n,
      Measurable fun value => F.dist theta value ranking) :
    Measurable fun value => (F.independentPairLaw theta value).toMeasure := by
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  have hmeasure : ∀ value,
      (F.independentPairLaw theta value).toMeasure s =
        ∑ pair : RankingPair n, s.indicator (F.independentPairLaw theta value) pair := by
    intro value
    simpa only [tsum_fintype] using
      PMF.toMeasure_apply (F.independentPairLaw theta value) hs
  simp_rw [hmeasure]
  change Measurable (fun value =>
    ∑ pair : RankingPair n,
      s.indicator (AppliedModelingLib.pmfProd (F.dist theta value) (F.dist theta value)) pair)
  refine Finset.measurable_sum Finset.univ ?_
  intro pair _
  by_cases hpair : pair ∈ s
  · simp only [Set.indicator_of_mem hpair]
    change Measurable (fun value =>
      F.dist theta value pair.1 * F.dist theta value pair.2)
    exact (hatom pair.1).mul (hatom pair.2)
  · simpa [Set.indicator, hpair] using
      (measurable_const : Measurable fun _ : ValueProfile n => (0 : ENNReal))

/-- A Markov kernel for the two conditionally independent ranking draws. -/
noncomputable def independentPairKernel {n : ℕ} (F : DistributionalAccuracyFamily n)
    (theta : ℝ) (hatom : ∀ ranking : Ranking n,
      Measurable fun value => F.dist theta value ranking) :
    Kernel (ValueProfile n) (RankingPair n) where
  toFun value := (F.independentPairLaw theta value).toMeasure
  measurable' := F.measurable_independentPairLaw_toMeasure theta hatom

@[simp] theorem independentPairKernel_apply {n : ℕ}
    (F : DistributionalAccuracyFamily n) (theta : ℝ)
    (hatom : ∀ ranking : Ranking n,
      Measurable fun value => F.dist theta value ranking)
    (value : ValueProfile n) :
    F.independentPairKernel theta hatom value =
      (F.independentPairLaw theta value).toMeasure := rfl

theorem independentPairKernel_isMarkov {n : ℕ}
    (F : DistributionalAccuracyFamily n) (theta : ℝ)
    (hatom : ∀ ranking : Ranking n,
      Measurable fun value => F.dist theta value ranking) :
    IsMarkovKernel (F.independentPairKernel theta hatom) := by
  constructor
  intro value
  change IsProbabilityMeasure (F.independentPairLaw theta value).toMeasure
  infer_instance

/-- The actual joint measure on a value profile and its two conditional draws. -/
noncomputable def outerIndependentPairJointLaw {n : ℕ}
    (F : DistributionalAccuracyFamily n) (D : Measure (ValueProfile n))
    (theta : ℝ) (hatom : ∀ ranking : Ranking n,
      Measurable fun value => F.dist theta value ranking) :
    Measure (ValueProfile n × RankingPair n) :=
  Measure.compProd D (F.independentPairKernel theta hatom)

theorem outerIndependentPairJointLaw_isProbability {n : ℕ}
    (F : DistributionalAccuracyFamily n) (D : Measure (ValueProfile n))
    (theta : ℝ) (hatom : ∀ ranking : Ranking n,
      Measurable fun value => F.dist theta value ranking)
    [IsProbabilityMeasure D] :
    IsProbabilityMeasure (F.outerIndependentPairJointLaw D theta hatom) := by
  unfold outerIndependentPairJointLaw
  letI : IsMarkovKernel (F.independentPairKernel theta hatom) :=
    F.independentPairKernel_isMarkov theta hatom
  infer_instance

/-- The regularity bundle produces an actual probability law for the full experiment. -/
theorem outerIndependentPairJointLaw_isProbability_of_regular {n : ℕ}
    (F : DistributionalAccuracyFamily n) (D : Measure (ValueProfile n))
    (theta : ℝ) (regularity : OuterIndependentRerankingRegularity F D theta) :
    IsProbabilityMeasure
      (F.outerIndependentPairJointLaw D theta regularity.ranking_atom_measurable) := by
  letI : IsProbabilityMeasure D := regularity.outer_is_probability
  exact F.outerIndependentPairJointLaw_isProbability D theta
    regularity.ranking_atom_measurable

/--
The iterated finite-pair expectation is the Bochner expectation under the
actual outer-profile/conditional-pair joint law.  The integrability premise is
essential: it prevents a totalized Bochner integral from manufacturing an
expectation for a non-integrable payoff.
-/
theorem integral_outerIndependentPairJointLaw_eq_outerPairExpected {n : ℕ}
    (F : DistributionalAccuracyFamily n) (D : Measure (ValueProfile n))
    (theta : ℝ) (hatom : ∀ ranking : Ranking n,
      Measurable fun value => F.dist theta value ranking)
    (u : ValueProfile n → RankingPair n → ℝ) [IsProbabilityMeasure D]
    (hu : Integrable (fun x : ValueProfile n × RankingPair n => u x.1 x.2)
      (F.outerIndependentPairJointLaw D theta hatom)) :
    ∫ x, u x.1 x.2 ∂F.outerIndependentPairJointLaw D theta hatom =
      F.outerPairExpected D theta u := by
  letI : IsMarkovKernel (F.independentPairKernel theta hatom) :=
    F.independentPairKernel_isMarkov theta hatom
  unfold outerIndependentPairJointLaw
  rw [Measure.integral_compProd hu]
  unfold outerPairExpected outerExpected
  apply integral_congr_ae
  filter_upwards [] with value
  rw [independentPairKernel_apply]
  rw [← AppliedModelingLib.pmfExp_eq_integral_toMeasure]
  exact AppliedModelingLib.pmfExp_pmfProd_eq_pairExp
    (F.dist theta value) (F.dist theta value) (u value)

/-- The raw second-mover payoff when the two rankings are shared. -/
def jointSharedSecondMoverPayoff {n : ℕ}
    (x : ValueProfile n × RankingPair n) : ℝ :=
  secondMoverUtility x.1 x.2.1 x.2.1

/-- The raw second-mover payoff when the second ranking is independently redrawn. -/
def jointIndependentSecondMoverPayoff {n : ℕ}
    (x : ValueProfile n × RankingPair n) : ℝ :=
  secondMoverUtility x.1 x.2.1 x.2.2

theorem jointIndependentSecondMoverPayoff_sub_jointSharedSecondMoverPayoff
    {n : ℕ} (x : ValueProfile n × RankingPair n) :
    jointIndependentSecondMoverPayoff x - jointSharedSecondMoverPayoff x =
      pairRerankingGain x.1 x.2 := by
  exact secondMoverUtility_sub_self_eq_rerankingGain x.1 x.2.1 x.2.2

/-- Integrability of the two raw joint payoffs implies integrability of their gain. -/
theorem jointRerankingGain_integrable_of_jointPayoffs {n : ℕ}
    (F : DistributionalAccuracyFamily n) (D : Measure (ValueProfile n))
    (theta : ℝ) (hatom : ∀ ranking : Ranking n,
      Measurable fun value => F.dist theta value ranking)
    (hshared : Integrable jointSharedSecondMoverPayoff
      (F.outerIndependentPairJointLaw D theta hatom))
    (hindependent : Integrable jointIndependentSecondMoverPayoff
      (F.outerIndependentPairJointLaw D theta hatom)) :
    Integrable (fun x : ValueProfile n × RankingPair n => pairRerankingGain x.1 x.2)
      (F.outerIndependentPairJointLaw D theta hatom) := by
  have hsub := hindependent.sub hshared
  have hpoint :
      (fun x : ValueProfile n × RankingPair n => pairRerankingGain x.1 x.2) =
        fun x => jointIndependentSecondMoverPayoff x - jointSharedSecondMoverPayoff x := by
    funext x
    exact (jointIndependentSecondMoverPayoff_sub_jointSharedSecondMoverPayoff x).symm
  rw [hpoint]
  exact hsub

/-- The raw joint shared payoff integrates to the existing outer shared payoff. -/
theorem integral_jointSharedSecondMoverPayoff_eq_outerShared {n : ℕ}
    (F : DistributionalAccuracyFamily n) (D : Measure (ValueProfile n))
    (theta : ℝ) (hatom : ∀ ranking : Ranking n,
      Measurable fun value => F.dist theta value ranking) [IsProbabilityMeasure D]
    (hshared : Integrable jointSharedSecondMoverPayoff
      (F.outerIndependentPairJointLaw D theta hatom)) :
    ∫ x, jointSharedSecondMoverPayoff x ∂F.outerIndependentPairJointLaw D theta hatom =
      outerExpected D (fun value => expectedSecondMoverShared (F.dist theta value) value) := by
  change ∫ x, secondMoverUtility x.1 x.2.1 x.2.1 ∂
      F.outerIndependentPairJointLaw D theta hatom =
    outerExpected D (fun value => expectedSecondMoverShared (F.dist theta value) value)
  rw [F.integral_outerIndependentPairJointLaw_eq_outerPairExpected D theta hatom
    (fun value pair => secondMoverUtility value pair.1 pair.1) hshared]
  unfold outerPairExpected outerExpected
  apply integral_congr_ae
  filter_upwards [] with value
  exact expectedSecondMoverSharedOnPairs_eq_expectedSecondMoverShared
    (μ := F.dist theta value) (value := value)

/-- The raw joint independent payoff integrates to the existing outer independent payoff. -/
theorem integral_jointIndependentSecondMoverPayoff_eq_outerIndependent {n : ℕ}
    (F : DistributionalAccuracyFamily n) (D : Measure (ValueProfile n))
    (theta : ℝ) (hatom : ∀ ranking : Ranking n,
      Measurable fun value => F.dist theta value ranking) [IsProbabilityMeasure D]
    (hindependent : Integrable jointIndependentSecondMoverPayoff
      (F.outerIndependentPairJointLaw D theta hatom)) :
    ∫ x, jointIndependentSecondMoverPayoff x ∂F.outerIndependentPairJointLaw D theta hatom =
      outerExpected D (fun value => expectedSecondMoverIndependent
        (F.dist theta value) (F.dist theta value) value) := by
  change ∫ x, secondMoverUtility x.1 x.2.1 x.2.2 ∂
      F.outerIndependentPairJointLaw D theta hatom =
    outerExpected D (fun value => pmfPairExp (F.dist theta value) (F.dist theta value)
      (fun pi sigma => secondMoverUtility value pi sigma))
  exact F.integral_outerIndependentPairJointLaw_eq_outerPairExpected D theta hatom
    (fun value pair => secondMoverUtility value pair.1 pair.2) hindependent

/-- Definition 2's outer payoff comparison is the comparison of raw joint payoffs. -/
theorem prefersIndependentReranking_iff_jointPayoffComparison {n : ℕ}
    (F : DistributionalAccuracyFamily n) (D : Measure (ValueProfile n))
    (theta : ℝ) (hatom : ∀ ranking : Ranking n,
      Measurable fun value => F.dist theta value ranking) [IsProbabilityMeasure D]
    (hshared : Integrable jointSharedSecondMoverPayoff
      (F.outerIndependentPairJointLaw D theta hatom))
    (hindependent : Integrable jointIndependentSecondMoverPayoff
      (F.outerIndependentPairJointLaw D theta hatom)) :
    F.PrefersIndependentReranking D theta ↔
      (∫ x, jointSharedSecondMoverPayoff x ∂F.outerIndependentPairJointLaw D theta hatom) <
        ∫ x, jointIndependentSecondMoverPayoff x ∂F.outerIndependentPairJointLaw D theta hatom := by
  rw [integral_jointSharedSecondMoverPayoff_eq_outerShared F D theta hatom hshared,
    integral_jointIndependentSecondMoverPayoff_eq_outerIndependent F D theta hatom hindependent]
  rfl

/-- The top-disagreement event as a measurable event of the full joint experiment. -/
def jointDisagreementEventSet {n : ℕ} : Set (ValueProfile n × RankingPair n) :=
  {x | disagreementEvent x.2}

theorem measurableSet_jointDisagreementEventSet {n : ℕ} :
    MeasurableSet (jointDisagreementEventSet (n := n)) := by
  change MeasurableSet
    (Prod.snd ⁻¹' {pair : RankingPair n | disagreementEvent pair})
  exact (Set.toFinite {pair : RankingPair n | disagreementEvent pair}).measurableSet.preimage
    measurable_snd

/-- The joint disagreement-event indicator is integrable under the probability experiment. -/
theorem integrable_jointDisagreementIndicator {n : ℕ}
    (F : DistributionalAccuracyFamily n) (D : Measure (ValueProfile n))
    (theta : ℝ) (hatom : ∀ ranking : Ranking n,
      Measurable fun value => F.dist theta value ranking) [IsProbabilityMeasure D] :
    Integrable (fun x : ValueProfile n × RankingPair n =>
      if disagreementEvent x.2 then (1 : ℝ) else 0)
      (F.outerIndependentPairJointLaw D theta hatom) := by
  letI : IsProbabilityMeasure (F.outerIndependentPairJointLaw D theta hatom) :=
    F.outerIndependentPairJointLaw_isProbability D theta hatom
  have hconst : Integrable (fun _ : ValueProfile n × RankingPair n => (1 : ℝ))
      (F.outerIndependentPairJointLaw D theta hatom) :=
    integrable_const (1 : ℝ)
  have h := hconst.indicator (measurableSet_jointDisagreementEventSet (n := n))
  convert h using 1
  funext x
  by_cases hx : disagreementEvent x.2 <;>
    simp [jointDisagreementEventSet, Set.indicator, hx]

/-- Restricting an integrable joint gain to the disagreement event preserves integrability. -/
theorem integrable_jointRestrictedGain {n : ℕ}
    (F : DistributionalAccuracyFamily n) (D : Measure (ValueProfile n))
    (theta : ℝ) (hatom : ∀ ranking : Ranking n,
      Measurable fun value => F.dist theta value ranking)
    (hgain : Integrable (fun x : ValueProfile n × RankingPair n =>
      pairRerankingGain x.1 x.2) (F.outerIndependentPairJointLaw D theta hatom)) :
    Integrable (fun x : ValueProfile n × RankingPair n =>
      if disagreementEvent x.2 then pairRerankingGain x.1 x.2 else 0)
      (F.outerIndependentPairJointLaw D theta hatom) := by
  have h := hgain.indicator (measurableSet_jointDisagreementEventSet (n := n))
  convert h using 1
  funext x
  by_cases hx : disagreementEvent x.2 <;>
    simp [jointDisagreementEventSet, Set.indicator, hx]

/-- The actual joint-event indicator expectation is the outer disagreement probability. -/
theorem integral_jointDisagreementIndicator_eq_outerDisagreementProbability {n : ℕ}
    (F : DistributionalAccuracyFamily n) (D : Measure (ValueProfile n))
    (theta : ℝ) (hatom : ∀ ranking : Ranking n,
      Measurable fun value => F.dist theta value ranking) [IsProbabilityMeasure D] :
    ∫ x : ValueProfile n × RankingPair n,
      (if disagreementEvent x.2 then (1 : ℝ) else 0) ∂
        F.outerIndependentPairJointLaw D theta hatom =
      F.outerDisagreementProbability D theta := by
  simpa [outerDisagreementProbability] using
    F.integral_outerIndependentPairJointLaw_eq_outerPairExpected D theta hatom
      (fun _ pair => if disagreementEvent pair then (1 : ℝ) else 0)
      (F.integrable_jointDisagreementIndicator D theta hatom)

/-- The actual joint restricted-gain expectation is the outer gain numerator. -/
theorem integral_jointRestrictedGain_eq_outerDisagreementGainNumerator {n : ℕ}
    (F : DistributionalAccuracyFamily n) (D : Measure (ValueProfile n))
    (theta : ℝ) (hatom : ∀ ranking : Ranking n,
      Measurable fun value => F.dist theta value ranking) [IsProbabilityMeasure D]
    (hgain : Integrable (fun x : ValueProfile n × RankingPair n =>
      pairRerankingGain x.1 x.2) (F.outerIndependentPairJointLaw D theta hatom)) :
    ∫ x : ValueProfile n × RankingPair n,
      (if disagreementEvent x.2 then pairRerankingGain x.1 x.2 else 0) ∂
        F.outerIndependentPairJointLaw D theta hatom =
      F.outerDisagreementGainNumerator D theta := by
  simpa [outerDisagreementGainNumerator] using
    F.integral_outerIndependentPairJointLaw_eq_outerPairExpected D theta hatom
      (fun value pair =>
        if disagreementEvent pair then pairRerankingGain value pair else 0)
      (F.integrable_jointRestrictedGain D theta hatom hgain)

/--
The conditional gain written directly under the actual joint measure.  It is
zero on a zero-mass event, matching the finite conditional-expectation
convention used elsewhere in the library.
-/
noncomputable def jointLawDisagreementConditionalGain {n : ℕ}
    (F : DistributionalAccuracyFamily n) (D : Measure (ValueProfile n))
    (theta : ℝ) (hatom : ∀ ranking : Ranking n,
      Measurable fun value => F.dist theta value ranking) : ℝ :=
  let M := F.outerIndependentPairJointLaw D theta hatom
  let p := ∫ x : ValueProfile n × RankingPair n,
    if disagreementEvent x.2 then (1 : ℝ) else 0 ∂M
  if p = 0 then 0 else
    (∫ x : ValueProfile n × RankingPair n,
      if disagreementEvent x.2 then pairRerankingGain x.1 x.2 else 0 ∂M) / p

/-- The direct joint-law conditional gain agrees with the iterated conditional gain. -/
theorem jointLawDisagreementConditionalGain_eq_outerDisagreementConditionalGain {n : ℕ}
    (F : DistributionalAccuracyFamily n) (D : Measure (ValueProfile n))
    (theta : ℝ) (hatom : ∀ ranking : Ranking n,
      Measurable fun value => F.dist theta value ranking) [IsProbabilityMeasure D]
    (hgain : Integrable (fun x : ValueProfile n × RankingPair n =>
      pairRerankingGain x.1 x.2) (F.outerIndependentPairJointLaw D theta hatom)) :
    F.jointLawDisagreementConditionalGain D theta hatom =
      F.outerDisagreementConditionalGain D theta := by
  rw [jointLawDisagreementConditionalGain,
    integral_jointDisagreementIndicator_eq_outerDisagreementProbability,
    integral_jointRestrictedGain_eq_outerDisagreementGainNumerator F D theta hatom hgain]
  rfl

/-- The iterated pair expectation is exactly the expectation under `independentPairLaw`. -/
theorem outerPairExpected_eq_outerExpected_pairLaw {n : ℕ}
    (F : DistributionalAccuracyFamily n) (D : Measure (ValueProfile n))
    (theta : ℝ) (u : ValueProfile n → RankingPair n → ℝ) :
    F.outerPairExpected D theta u =
      outerExpected D (fun value =>
        pmfExp (F.independentPairLaw theta value) (u value)) := by
  unfold outerPairExpected outerExpected
  apply integral_congr_ae
  filter_upwards [] with value
  exact (AppliedModelingLib.pmfExp_pmfProd_eq_pairExp
    (F.dist theta value) (F.dist theta value) (u value)).symm

/-- The joint disagreement probability is the outer mean of the fiber probabilities. -/
theorem outerDisagreementProbability_eq_outerExpected {n : ℕ}
    (F : DistributionalAccuracyFamily n) (D : Measure (ValueProfile n))
    (theta : ℝ) :
    F.outerDisagreementProbability D theta =
      outerExpected D (fun value => disagreementProb (F.dist theta value)) := by
  simp only [outerDisagreementProbability, outerPairExpected, outerExpected]
  rfl

/-- The restricted joint gain is the outer mean of the exact finite gain. -/
theorem outerDisagreementGainNumerator_eq_outerExpected {n : ℕ}
    (F : DistributionalAccuracyFamily n) (D : Measure (ValueProfile n))
    (theta : ℝ) :
    F.outerDisagreementGainNumerator D theta =
      outerExpected D (fun value => expectedRerankingGain (F.dist theta value) value) := by
  unfold outerDisagreementGainNumerator outerPairExpected outerExpected
  apply integral_congr_ae
  filter_upwards [] with value
  simpa [AppliedModelingLib.pmfPairIndicatorExp] using
    (expectedRerankingGain_eq_pairIndicatorExp
      (μ := F.dist theta value) (value := value)).symm

/-- The outer reranking-gain integrand is defined whenever both payoff integrands are. -/
theorem rerankingGain_integrable_of_regular {n : ℕ}
    (F : DistributionalAccuracyFamily n) (D : Measure (ValueProfile n))
    (theta : ℝ) (regularity : OuterIndependentRerankingRegularity F D theta) :
    Integrable (fun value => expectedRerankingGain (F.dist theta value) value) D := by
  have hsub := regularity.independent_payoff_integrable.sub
    regularity.shared_payoff_integrable
  have hpoint :
      (fun value => expectedRerankingGain (F.dist theta value) value) =
        fun value => expectedSecondMoverIndependent
          (F.dist theta value) (F.dist theta value) value -
          expectedSecondMoverShared (F.dist theta value) value := by
    funext value
    exact (expectedSecondMoverIndependent_sub_shared_eq_expectedRerankingGain
      (μ := F.dist theta value) (value := value)).symm
  rw [hpoint]
  exact hsub

/--
The full experiment's restricted gain is exactly the ex-ante independent-minus-
shared payoff gap.  This is the key link absent from the earlier fixed-profile
conditional form.
-/
theorem outerRerankingGain_eq_payoffGap {n : ℕ}
    (F : DistributionalAccuracyFamily n) (D : Measure (ValueProfile n))
    (theta : ℝ)
    (hshared : Integrable
      (fun value => expectedSecondMoverShared (F.dist theta value) value) D)
    (hindependent : Integrable
      (fun value => expectedSecondMoverIndependent
        (F.dist theta value) (F.dist theta value) value) D) :
    F.outerDisagreementGainNumerator D theta =
      outerExpected D (fun value => expectedSecondMoverIndependent
        (F.dist theta value) (F.dist theta value) value) -
        outerExpected D (fun value => expectedSecondMoverShared
          (F.dist theta value) value) := by
  rw [outerDisagreementGainNumerator_eq_outerExpected]
  unfold outerExpected
  rw [← integral_sub hindependent hshared]
  apply integral_congr_ae
  filter_upwards [] with value
  exact (expectedSecondMoverIndependent_sub_shared_eq_expectedRerankingGain
    (μ := F.dist theta value) (value := value)).symm

/-- The payoff-gap equality with integrability supplied by the full regularity bundle. -/
theorem outerRerankingGain_eq_payoffGap_of_regular {n : ℕ}
    (F : DistributionalAccuracyFamily n) (D : Measure (ValueProfile n))
    (theta : ℝ) (regularity : OuterIndependentRerankingRegularity F D theta) :
    F.outerDisagreementGainNumerator D theta =
      outerExpected D (fun value => expectedSecondMoverIndependent
        (F.dist theta value) (F.dist theta value) value) -
        outerExpected D (fun value => expectedSecondMoverShared
          (F.dist theta value) value) :=
  F.outerRerankingGain_eq_payoffGap D theta
    regularity.shared_payoff_integrable regularity.independent_payoff_integrable

/-- On a positive joint disagreement event, conditional gain is payoff gap divided by its mass. -/
theorem outerDisagreementConditionalGain_eq_payoffGap_div_of_pos {n : ℕ}
    (F : DistributionalAccuracyFamily n) (D : Measure (ValueProfile n))
    (theta : ℝ)
    (hshared : Integrable
      (fun value => expectedSecondMoverShared (F.dist theta value) value) D)
    (hindependent : Integrable
      (fun value => expectedSecondMoverIndependent
        (F.dist theta value) (F.dist theta value) value) D)
    (hdisagreement : 0 < F.outerDisagreementProbability D theta) :
    F.outerDisagreementConditionalGain D theta =
      (outerExpected D (fun value => expectedSecondMoverIndependent
        (F.dist theta value) (F.dist theta value) value) -
        outerExpected D (fun value => expectedSecondMoverShared
          (F.dist theta value) value)) /
        F.outerDisagreementProbability D theta := by
  unfold outerDisagreementConditionalGain
  rw [if_neg hdisagreement.ne']
  rw [outerRerankingGain_eq_payoffGap F D theta hshared hindependent]

/--
Source Definition 2 is equivalent to positive conditional gain in the full
outer-profile experiment, once the event has positive mass and both payoff
integrals are defined.
-/
theorem prefersIndependentReranking_iff_outerDisagreementConditionalGain_pos_of_pos
    {n : ℕ} (F : DistributionalAccuracyFamily n) (D : Measure (ValueProfile n))
    (theta : ℝ)
    (hshared : Integrable
      (fun value => expectedSecondMoverShared (F.dist theta value) value) D)
    (hindependent : Integrable
      (fun value => expectedSecondMoverIndependent
        (F.dist theta value) (F.dist theta value) value) D)
    (hdisagreement : 0 < F.outerDisagreementProbability D theta) :
    F.PrefersIndependentReranking D theta ↔
      0 < F.outerDisagreementConditionalGain D theta := by
  rw [outerDisagreementConditionalGain_eq_payoffGap_div_of_pos
    F D theta hshared hindependent hdisagreement]
  unfold PrefersIndependentReranking outerExpected
  rw [zero_lt_div_iff_pos_right hdisagreement]
  constructor <;> intro h <;> linarith

/-- A regularity-bundled form of the source Definition-2 conditional-event bridge. -/
theorem prefersIndependentReranking_iff_outerDisagreementConditionalGain_pos
    {n : ℕ} (F : DistributionalAccuracyFamily n) (D : Measure (ValueProfile n))
    (theta : ℝ) (regularity : OuterIndependentRerankingRegularity F D theta)
    (hdisagreement : 0 < F.outerDisagreementProbability D theta) :
    F.PrefersIndependentReranking D theta ↔
      0 < F.outerDisagreementConditionalGain D theta :=
  prefersIndependentReranking_iff_outerDisagreementConditionalGain_pos_of_pos
    F D theta regularity.shared_payoff_integrable
      regularity.independent_payoff_integrable hdisagreement

/--
Regularity for the actual joint formulation of Definition 2.  The raw shared
and independent utility variables are both required to be integrable; merely
integrating their finite conditional expectations would not establish the
source's joint payoff semantics.
-/
structure OuterIndependentRerankingJointRegularity {n : ℕ}
    (F : DistributionalAccuracyFamily n) (D : Measure (ValueProfile n))
    (theta : ℝ) : Prop where
  base : OuterIndependentRerankingRegularity F D theta
  joint_shared_payoff_integrable : Integrable jointSharedSecondMoverPayoff
    (F.outerIndependentPairJointLaw D theta base.ranking_atom_measurable)
  joint_independent_payoff_integrable : Integrable jointIndependentSecondMoverPayoff
    (F.outerIndependentPairJointLaw D theta base.ranking_atom_measurable)

/-- The stronger joint regularity supplies integrability of the raw reranking gain. -/
theorem jointRerankingGain_integrable_of_regular {n : ℕ}
    (F : DistributionalAccuracyFamily n) (D : Measure (ValueProfile n))
    (theta : ℝ) (regularity : OuterIndependentRerankingJointRegularity F D theta) :
    Integrable (fun x : ValueProfile n × RankingPair n => pairRerankingGain x.1 x.2)
      (F.outerIndependentPairJointLaw D theta regularity.base.ranking_atom_measurable) :=
  F.jointRerankingGain_integrable_of_jointPayoffs D theta
    regularity.base.ranking_atom_measurable
    regularity.joint_shared_payoff_integrable
    regularity.joint_independent_payoff_integrable

/-- With a deterministic outer profile, the actual composed joint-law
conditional gain specializes to the ordinary finite conditional gain. -/
theorem jointLawDisagreementConditionalGain_dirac {n : ℕ}
    (F : DistributionalAccuracyFamily n) (value : ValueProfile n)
    (theta : ℝ)
    (regularity : OuterIndependentRerankingJointRegularity F (Measure.dirac value) theta) :
    F.jointLawDisagreementConditionalGain (Measure.dirac value) theta
      regularity.base.ranking_atom_measurable =
        disagreementConditionalGain (F.dist theta value) value := by
  letI : IsProbabilityMeasure (Measure.dirac value) :=
    regularity.base.outer_is_probability
  rw [F.jointLawDisagreementConditionalGain_eq_outerDisagreementConditionalGain
    (Measure.dirac value) theta regularity.base.ranking_atom_measurable
    (F.jointRerankingGain_integrable_of_regular (Measure.dirac value) theta regularity)]
  exact outerDisagreementConditionalGain_dirac F value theta

/-- The outer Definition-2 payoff comparison is exactly the raw joint-payoff comparison. -/
theorem prefersIndependentReranking_iff_jointPayoffComparison_of_regular {n : ℕ}
    (F : DistributionalAccuracyFamily n) (D : Measure (ValueProfile n))
    (theta : ℝ) (regularity : OuterIndependentRerankingJointRegularity F D theta) :
    F.PrefersIndependentReranking D theta ↔
      (∫ x, jointSharedSecondMoverPayoff x ∂
        F.outerIndependentPairJointLaw D theta regularity.base.ranking_atom_measurable) <
        ∫ x, jointIndependentSecondMoverPayoff x ∂
          F.outerIndependentPairJointLaw D theta regularity.base.ranking_atom_measurable := by
  letI : IsProbabilityMeasure D := regularity.base.outer_is_probability
  exact F.prefersIndependentReranking_iff_jointPayoffComparison D theta
    regularity.base.ranking_atom_measurable
    regularity.joint_shared_payoff_integrable
    regularity.joint_independent_payoff_integrable

/--
The source Definition-2 comparison is exactly positivity of the conditional
gain under the actual joint value-profile/ranking-pair law.  The positivity
hypothesis is stated for that event itself, not for a profilewise surrogate.
-/
theorem prefersIndependentReranking_iff_jointLawDisagreementConditionalGain_pos_of_regular
    {n : ℕ} (F : DistributionalAccuracyFamily n) (D : Measure (ValueProfile n))
    (theta : ℝ) (regularity : OuterIndependentRerankingJointRegularity F D theta)
    (hdisagreement : 0 < ∫ x : ValueProfile n × RankingPair n,
      (if disagreementEvent x.2 then (1 : ℝ) else 0) ∂
        F.outerIndependentPairJointLaw D theta regularity.base.ranking_atom_measurable) :
    F.PrefersIndependentReranking D theta ↔
      0 < F.jointLawDisagreementConditionalGain D theta
        regularity.base.ranking_atom_measurable := by
  letI : IsProbabilityMeasure D := regularity.base.outer_is_probability
  have hgain := F.jointRerankingGain_integrable_of_regular D theta regularity
  have houter : 0 < F.outerDisagreementProbability D theta := by
    rw [← F.integral_jointDisagreementIndicator_eq_outerDisagreementProbability
      D theta regularity.base.ranking_atom_measurable]
    exact hdisagreement
  rw [F.jointLawDisagreementConditionalGain_eq_outerDisagreementConditionalGain
    D theta regularity.base.ranking_atom_measurable hgain]
  exact F.prefersIndependentReranking_iff_outerDisagreementConditionalGain_pos_of_pos
    D theta regularity.base.shared_payoff_integrable
      regularity.base.independent_payoff_integrable houter

end DistributionalAccuracyFamily
end KR21Monoculture
