import KR21Monoculture.PlackettLuce
import KR21Monoculture.OuterConditional

open AppliedModelingLib MeasureTheory ProbabilityTheory

namespace KR21Monoculture

/-!
# Plackett--Luce at the source's outer value distribution

The source's Plackett--Luce discussion has two distinct mathematical layers.
The finite sequential sampler in `PlackettLuce` proves equation (7) and the
pointwise equality of independent and shared second-mover payoffs.  This file
puts that result under the source's outer draw of a value profile and, when the
conditional PMF atoms form a measurable kernel, under the actual joint
profile/ranking-pair law.

This is a theorem about the sequential Plackett--Luce law itself.  It does not
claim the separate, unformalized equivalence between that law and iid Gumbel
random-utility noise.
-/

namespace DistributionalAccuracyFamily

/-- The source's sequential Plackett--Luce ranking law, conditional on a
realized cardinal value profile. -/
noncomputable def plackettLuceDistributionalFamily {n : ℕ} :
    DistributionalAccuracyFamily n where
  dist := fun theta value => plackettLuceRankingPMF theta value

@[simp] theorem plackettLuceDistributionalFamily_dist {n : ℕ}
    (theta : ℝ) (value : ValueProfile n) :
    (plackettLuceDistributionalFamily (n := n)).dist theta value =
      plackettLuceRankingPMF theta value := rfl

/-- At every realized profile, the independent-minus-shared payoff gap of the
sequential Plackett--Luce law is zero. -/
theorem plackettLuce_pointwise_rerankingGain_eq_zero {n : ℕ}
    (theta : ℝ) (value : ValueProfile n) :
    expectedRerankingGain (plackettLuceRankingPMF theta value) value = 0 := by
  rw [← expectedSecondMoverIndependent_sub_shared_eq_expectedRerankingGain]
  exact plackettLuceRankingPMF_independentRerankingEffect_eq_zero theta value

/-- The restricted-gain numerator of the source's full outer experiment is
zero for every outer value measure.  This is not merely a fixed-profile
statement: the finite conditional gain is shown to be identically zero before
the outer integral is taken. -/
theorem plackettLuce_outerDisagreementGainNumerator_eq_zero {n : ℕ}
    (D : Measure (ValueProfile n)) (theta : ℝ) :
    (plackettLuceDistributionalFamily (n := n)).outerDisagreementGainNumerator D theta = 0 := by
  rw [outerDisagreementGainNumerator_eq_outerExpected]
  unfold outerExpected
  change ∫ value : ValueProfile n,
      expectedRerankingGain (plackettLuceRankingPMF theta value) value ∂D = 0
  have hzero :
      (fun value : ValueProfile n =>
        expectedRerankingGain (plackettLuceRankingPMF theta value) value) =
        fun _ => 0 := by
    funext value
    exact plackettLuce_pointwise_rerankingGain_eq_zero theta value
  rw [hzero, integral_zero]

/-- In the source's outer-profile/conditionally-iid-ranking experiment, the
conditional reranking gain is exactly zero.  The definition is totalized to
zero when top-choice disagreement has zero mass, so no positivity assumption
is hidden here. -/
theorem plackettLuce_outerDisagreementConditionalGain_eq_zero {n : ℕ}
    (D : Measure (ValueProfile n)) (theta : ℝ) :
    (plackettLuceDistributionalFamily (n := n)).outerDisagreementConditionalGain D theta = 0 := by
  unfold outerDisagreementConditionalGain
  rw [plackettLuce_outerDisagreementGainNumerator_eq_zero]
  simp

/-- On the source's top-disagreement event, the raw joint integrand is the
literal first-position-minus-second-position expression written in Section
3.1. -/
theorem plackettLuce_pairRerankingGain_eq_sourceGap_of_disagreement {n : ℕ}
    (value : ValueProfile n) (pair : RankingPair n)
    (hdisagreement : disagreementEvent pair) :
    pairRerankingGain value pair =
      value (firstChoice pair.1) - value (secondChoice pair.1) := by
  exact rerankingGainOnPair_of_neFirst value pair.1 pair.2 hdisagreement

private theorem measurable_plackettLuceWeight {n : ℕ} (theta : ℝ)
    (i : Candidate n) :
    Measurable fun value : ValueProfile n => plackettLuceWeight theta value i := by
  unfold plackettLuceWeight
  exact Real.continuous_exp.measurable.comp
    ((measurable_const : Measurable fun _ : ValueProfile n => theta).mul
      (measurable_pi_apply i))

private theorem measurable_plackettLuceAvailableWeight {n : ℕ} (theta : ℝ)
    (forbidden : Finset (Candidate n)) :
    Measurable fun value : ValueProfile n =>
      finiteAvailableWeight (plackettLuceWeight theta value) forbidden := by
  classical
  unfold finiteAvailableWeight
  refine Finset.measurable_sum Finset.univ ?_
  intro i _
  by_cases hi : i ∈ forbidden
  · simp [hi]
  · simpa [hi] using measurable_plackettLuceWeight theta i

private theorem measurable_plackettLuceFreshListAtomWeight {n : ℕ} (theta : ℝ) :
    ∀ {k : ℕ} (forbidden : Finset (Candidate n))
      (sample : finiteFreshList (Candidate n) k forbidden),
      Measurable fun value : ValueProfile n =>
        finiteFreshListAtomWeight (plackettLuceWeight theta value) forbidden sample
  | 0, forbidden, sample => by
      simp [finiteFreshListAtomWeight]
  | k + 1, forbidden, sample => by
      classical
      let head : {a : Candidate n // a ∉ forbidden} :=
        ⟨sample.1 ⟨0, Nat.succ_pos k⟩,
          sample.2.2 ⟨0, Nat.succ_pos k⟩⟩
      let tail := finiteFreshListTailOfHead sample head rfl
      have htail := measurable_plackettLuceFreshListAtomWeight theta
        (insert head.1 forbidden) tail
      simpa [finiteFreshListAtomWeight, head, tail] using
        ((measurable_plackettLuceWeight theta head.1).div
          (measurable_plackettLuceAvailableWeight theta forbidden)).mul htail

private theorem plackettLuceFreshRankingPMF_apply_toReal_measurable {n : ℕ}
    (theta : ℝ) (sample : finiteFreshList (Candidate n) (n + 2) ∅) :
    Measurable fun value : ValueProfile n =>
      ((plackettLuceFreshRankingPMF theta value) sample).toReal := by
  have hatom := measurable_plackettLuceFreshListAtomWeight theta
    (∅ : Finset (Candidate n)) sample
  convert hatom using 1
  funext value
  simpa [plackettLuceFreshRankingPMF] using
    (finiteWithoutReplacementPMF_atom_toReal
      (plackettLuceWeight theta value)
      (fun i => (plackettLuceWeight_pos theta value i).le)
      (plackettLuceAvailableWeight_pos theta value)
      (∅ : Finset (Candidate n)) (by simp [Candidate]) sample)

private theorem plackettLuceFreshRankingPMF_atom_measurable {n : ℕ}
    (theta : ℝ) (sample : finiteFreshList (Candidate n) (n + 2) ∅) :
    Measurable fun value : ValueProfile n =>
      plackettLuceFreshRankingPMF theta value sample := by
  have hreal := plackettLuceFreshRankingPMF_apply_toReal_measurable theta sample
  have heq :
      (fun value : ValueProfile n => plackettLuceFreshRankingPMF theta value sample) =
        fun value => ENNReal.ofReal
          ((plackettLuceFreshRankingPMF theta value sample).toReal) := by
    funext value
    exact (ENNReal.ofReal_toReal
      ((plackettLuceFreshRankingPMF theta value).apply_ne_top sample)).symm
  rw [heq]
  exact hreal.ennreal_ofReal

/-- Every finite sequential Plackett--Luce ranking atom is measurable in the
realized value profile.  The proof uses the exact finite product formula for
the without-replacement sampler; it is not an assumed kernel property. -/
theorem plackettLuce_ranking_atom_measurable {n : ℕ} (theta : ℝ)
    (ranking : Ranking n) :
    Measurable fun value : ValueProfile n =>
      plackettLuceRankingPMF theta value ranking := by
  unfold plackettLuceRankingPMF
  simp only [PMF.map_apply]
  simp only [tsum_fintype]
  refine Finset.measurable_sum Finset.univ ?_
  intro sample _
  by_cases hsample : ranking = fullFreshListToRanking sample
  · simpa [hsample] using plackettLuceFreshRankingPMF_atom_measurable theta sample
  · simp [hsample]

private theorem plackettLuceFreshListAtomWeight_pos {n : ℕ} (theta : ℝ)
    (value : ValueProfile n) :
    ∀ {k : ℕ} (forbidden : Finset (Candidate n))
      (sample : finiteFreshList (Candidate n) k forbidden),
      0 < finiteFreshListAtomWeight (plackettLuceWeight theta value) forbidden sample
  | 0, _forbidden, _sample => by
      simp [finiteFreshListAtomWeight]
  | k + 1, forbidden, sample => by
      classical
      let head : {a : Candidate n // a ∉ forbidden} :=
        ⟨sample.1 ⟨0, Nat.succ_pos k⟩,
          sample.2.2 ⟨0, Nat.succ_pos k⟩⟩
      let tail := finiteFreshListTailOfHead sample head rfl
      have htail := plackettLuceFreshListAtomWeight_pos theta value
        (insert head.1 forbidden) tail
      have havailable : 0 <
          finiteAvailableWeight (plackettLuceWeight theta value) forbidden := by
        unfold finiteAvailableWeight
        refine Finset.sum_pos' ?_ ?_
        · intro i _
          by_cases hi : i ∈ forbidden
          · simp [hi]
          · simpa [hi] using (plackettLuceWeight_pos theta value i).le
        · refine ⟨head.1, Finset.mem_univ _, ?_⟩
          simpa [head.2] using plackettLuceWeight_pos theta value head.1
      simpa [finiteFreshListAtomWeight, head, tail] using
        mul_pos
          (div_pos (plackettLuceWeight_pos theta value head.1)
            havailable)
          htail

private theorem plackettLuceFreshRankingPMF_atom_toReal_pos {n : ℕ}
    (theta : ℝ) (value : ValueProfile n)
    (sample : finiteFreshList (Candidate n) (n + 2) ∅) :
    0 < (plackettLuceFreshRankingPMF theta value sample).toReal := by
  unfold plackettLuceFreshRankingPMF
  rw [finiteWithoutReplacementPMF_atom_toReal
    (plackettLuceWeight theta value)
    (fun i => (plackettLuceWeight_pos theta value i).le)
    (plackettLuceAvailableWeight_pos theta value)
    (∅ : Finset (Candidate n)) (by simp [Candidate]) sample]
  exact plackettLuceFreshListAtomWeight_pos theta value (∅ : Finset (Candidate n)) sample

private def rankingToFullFreshList {n : ℕ} (ranking : Ranking n) :
    finiteFreshList (Candidate n) (n + 2) ∅ :=
  ⟨ranking, ranking.injective, fun _ => by simp⟩

private theorem fullFreshListToRanking_rankingToFullFreshList {n : ℕ}
    (ranking : Ranking n) :
    fullFreshListToRanking (rankingToFullFreshList ranking) = ranking := by
  ext slot
  simp [rankingToFullFreshList, fullFreshListToRanking_apply]

private theorem fullFreshListToRanking_injective {n : ℕ} :
    Function.Injective (@fullFreshListToRanking n) := by
  intro a b hab
  apply Subtype.ext
  funext slot
  simpa only [fullFreshListToRanking_apply] using
    congrArg (fun ranking : Ranking n => ranking slot) hab

private theorem plackettLuceRankingPMF_apply_eq_freshAtom {n : ℕ}
    (theta : ℝ) (value : ValueProfile n) (ranking : Ranking n) :
    plackettLuceRankingPMF theta value ranking =
      plackettLuceFreshRankingPMF theta value
        (rankingToFullFreshList ranking) := by
  let sample := rankingToFullFreshList ranking
  have hsample : fullFreshListToRanking sample = ranking := by
    exact fullFreshListToRanking_rankingToFullFreshList ranking
  have hiff : ∀ candidate : finiteFreshList (Candidate n) (n + 2) ∅,
      ranking = fullFreshListToRanking candidate ↔ candidate = sample := by
    intro candidate
    constructor
    · intro hcandidate
      apply fullFreshListToRanking_injective
      calc
        fullFreshListToRanking candidate = ranking := hcandidate.symm
        _ = fullFreshListToRanking sample := hsample.symm
    · intro hcandidate
      subst candidate
      exact hsample.symm
  unfold plackettLuceRankingPMF
  rw [PMF.map_apply]
  simp_rw [hiff]
  exact tsum_ite_eq sample _

/-- Every full ranking has positive probability under the literal sequential
Plackett--Luce sampler. -/
theorem plackettLuceRankingPMF_atom_toReal_pos {n : ℕ}
    (theta : ℝ) (value : ValueProfile n) (ranking : Ranking n) :
    0 < (plackettLuceRankingPMF theta value ranking).toReal := by
  rw [plackettLuceRankingPMF_apply_eq_freshAtom]
  exact plackettLuceFreshRankingPMF_atom_toReal_pos theta value
    (rankingToFullFreshList ranking)

/-- The source's two independent Plackett--Luce rankings disagree at the top
with positive probability at every realized profile. -/
theorem plackettLuce_disagreementProb_pos {n : ℕ}
    (theta : ℝ) (value : ValueProfile n) :
    0 < disagreementProb (plackettLuceRankingPMF theta value) := by
  let ranking : Ranking n := Equiv.refl (Candidate n)
  let μ := plackettLuceRankingPMF theta value
  change 0 < AppliedModelingLib.pmfPairExp μ μ
    (fun pi sigma => if disagreementEvent (pi, sigma) then 1 else 0)
  rw [← AppliedModelingLib.pmfExp_pmfProd_eq_pairExp μ μ
    (fun pair => if disagreementEvent pair then (1 : ℝ) else 0)]
  change 0 < AppliedModelingLib.pmfProb (AppliedModelingLib.pmfProd μ μ) disagreementEvent
  refine AppliedModelingLib.pmfProb_pos_of_mass (AppliedModelingLib.pmfProd μ μ)
    disagreementEvent (ranking, swapTopTwo ranking) ?_ ?_
  · exact (swapTopTwo_firstChoice_ne ranking).symm
  · rw [AppliedModelingLib.pmfProd_apply_toReal]
    exact mul_pos
      (plackettLuceRankingPMF_atom_toReal_pos theta value ranking)
      (plackettLuceRankingPMF_atom_toReal_pos theta value (swapTopTwo ranking))

private theorem plackettLuce_disagreementProb_measurable {n : ℕ}
    (theta : ℝ) :
    Measurable fun value : ValueProfile n =>
      disagreementProb (plackettLuceRankingPMF theta value) := by
  change Measurable fun value : ValueProfile n =>
    AppliedModelingLib.pmfPairExp (plackettLuceRankingPMF theta value)
      (plackettLuceRankingPMF theta value)
      (fun pi sigma => if disagreementEvent (pi, sigma) then (1 : ℝ) else 0)
  unfold AppliedModelingLib.pmfPairExp AppliedModelingLib.pmfExp
  refine Finset.measurable_sum Finset.univ ?_
  intro pi _
  refine (plackettLuce_ranking_atom_measurable theta pi).ennreal_toReal.mul ?_
  refine Finset.measurable_sum Finset.univ ?_
  intro sigma _
  exact (plackettLuce_ranking_atom_measurable theta sigma).ennreal_toReal.mul
    (measurable_const : Measurable fun _ : ValueProfile n =>
      if disagreementEvent (pi, sigma) then (1 : ℝ) else 0)

private theorem plackettLuce_disagreementProb_nonneg {n : ℕ}
    (theta : ℝ) (value : ValueProfile n) :
    0 ≤ disagreementProb (plackettLuceRankingPMF theta value) := by
  change 0 ≤ AppliedModelingLib.pmfPairExp
    (plackettLuceRankingPMF theta value) (plackettLuceRankingPMF theta value)
    (fun pi sigma => if disagreementEvent (pi, sigma) then (1 : ℝ) else 0)
  rw [← AppliedModelingLib.pmfExp_pmfProd_eq_pairExp
    (plackettLuceRankingPMF theta value) (plackettLuceRankingPMF theta value)
    (fun pair => if disagreementEvent pair then (1 : ℝ) else 0)]
  change 0 ≤ AppliedModelingLib.pmfProb (AppliedModelingLib.pmfProd
    (plackettLuceRankingPMF theta value) (plackettLuceRankingPMF theta value))
    disagreementEvent
  exact AppliedModelingLib.pmfProb_nonneg (AppliedModelingLib.pmfProd
    (plackettLuceRankingPMF theta value) (plackettLuceRankingPMF theta value))
    disagreementEvent

private theorem plackettLuce_disagreementProb_le_one {n : ℕ}
    (theta : ℝ) (value : ValueProfile n) :
    disagreementProb (plackettLuceRankingPMF theta value) ≤ 1 := by
  change AppliedModelingLib.pmfPairExp
    (plackettLuceRankingPMF theta value) (plackettLuceRankingPMF theta value)
    (fun pi sigma => if disagreementEvent (pi, sigma) then (1 : ℝ) else 0) ≤ 1
  rw [← AppliedModelingLib.pmfExp_pmfProd_eq_pairExp
    (plackettLuceRankingPMF theta value) (plackettLuceRankingPMF theta value)
    (fun pair => if disagreementEvent pair then (1 : ℝ) else 0)]
  change AppliedModelingLib.pmfProb (AppliedModelingLib.pmfProd
    (plackettLuceRankingPMF theta value) (plackettLuceRankingPMF theta value))
    disagreementEvent ≤ 1
  exact AppliedModelingLib.pmfProb_le_one (AppliedModelingLib.pmfProd
    (plackettLuceRankingPMF theta value) (plackettLuceRankingPMF theta value))
    disagreementEvent

private theorem plackettLuce_disagreementProb_integrable {n : ℕ}
    (D : Measure (ValueProfile n)) [IsProbabilityMeasure D] (theta : ℝ) :
    Integrable (fun value : ValueProfile n =>
      disagreementProb (plackettLuceRankingPMF theta value)) D := by
  refine Integrable.of_bound
    (plackettLuce_disagreementProb_measurable theta).aestronglyMeasurable 1
    (ae_of_all D fun value => ?_)
  rw [Real.norm_eq_abs,
    abs_of_nonneg (plackettLuce_disagreementProb_nonneg theta value)]
  exact plackettLuce_disagreementProb_le_one theta value

/-- In the source's full outer experiment, top disagreement has positive
probability for every probability distribution over value profiles.  The
candidate carrier contains at least two alternatives, and the finite
Plackett--Luce sampler gives every ranking positive mass. -/
theorem plackettLuce_outerDisagreementProbability_pos {n : ℕ}
    (D : Measure (ValueProfile n)) [IsProbabilityMeasure D] (theta : ℝ) :
    0 < (plackettLuceDistributionalFamily (n := n)).outerDisagreementProbability D theta := by
  rw [outerDisagreementProbability_eq_outerExpected]
  unfold outerExpected
  let p : ValueProfile n → ℝ := fun value =>
    disagreementProb (plackettLuceRankingPMF theta value)
  have hnonneg : 0 ≤ᵐ[D] p := by
    exact ae_of_all _ fun value => plackettLuce_disagreementProb_nonneg theta value
  have hintegrable : Integrable p D :=
    plackettLuce_disagreementProb_integrable D theta
  have hsupport_ae : ∀ᵐ value ∂D, value ∈ Function.support p := by
    exact ae_of_all _ fun value => ne_of_gt (plackettLuce_disagreementProb_pos theta value)
  have hsupport_pos : 0 < D (Function.support p) := by
    apply (pos_iff_ne_zero).2
    intro hzero
    have hcompl : D (Function.support p)ᶜ = 0 := mem_ae_iff.mp hsupport_ae
    have huniv : D Set.univ = 0 := by
      rw [← Set.union_compl_self (Function.support p)]
      exact measure_union_null hzero hcompl
    rw [measure_univ] at huniv
    norm_num at huniv
  exact (integral_pos_iff_support_of_nonneg_ae hnonneg hintegrable).2 hsupport_pos

/-- The actual profile/ranking-pair experiment gives positive mass to the
source conditioning event. -/
theorem plackettLuce_outerJointDisagreementEvent_pos {n : ℕ}
    (D : Measure (ValueProfile n)) [IsProbabilityMeasure D] (theta : ℝ) :
    0 < ∫ x : ValueProfile n × RankingPair n,
      (if disagreementEvent x.2 then (1 : ℝ) else 0) ∂
        (plackettLuceDistributionalFamily (n := n)).outerIndependentPairJointLaw D theta
          (fun ranking => plackettLuce_ranking_atom_measurable theta ranking) := by
  rw [integral_jointDisagreementIndicator_eq_outerDisagreementProbability]
  exact plackettLuce_outerDisagreementProbability_pos D theta

/-- The conditional Plackett--Luce pair kernel, together with a probability
outer law, gives a genuine probability law on value profiles and ranking
pairs.  Atom measurability is recorded explicitly because the source prose
does not itself supply a measurable-kernel construction. -/
theorem plackettLuce_outerJointLaw_isProbability {n : ℕ}
    (D : Measure (ValueProfile n)) [IsProbabilityMeasure D] (theta : ℝ)
    (hatom : ∀ ranking : Ranking n,
      Measurable fun value : ValueProfile n =>
        plackettLuceRankingPMF theta value ranking) :
    IsProbabilityMeasure
      ((plackettLuceDistributionalFamily (n := n)).outerIndependentPairJointLaw D theta
        hatom) := by
  exact (plackettLuceDistributionalFamily (n := n)).outerIndependentPairJointLaw_isProbability
    D theta hatom

/-- The first projection of the actual source experiment is its declared
outer candidate-value law. -/
theorem plackettLuce_outerJointLaw_fst_measurePreserving {n : ℕ}
    (D : Measure (ValueProfile n)) [IsProbabilityMeasure D] (theta : ℝ)
    (hatom : ∀ ranking : Ranking n,
      Measurable fun value : ValueProfile n =>
        plackettLuceRankingPMF theta value ranking) :
    MeasurePreserving Prod.fst
      ((plackettLuceDistributionalFamily (n := n)).outerIndependentPairJointLaw D theta
        hatom) D := by
  let F := plackettLuceDistributionalFamily (n := n)
  letI : IsMarkovKernel (F.independentPairKernel theta hatom) :=
    F.independentPairKernel_isMarkov theta hatom
  refine ⟨measurable_fst, ?_⟩
  change (D ⊗ₘ F.independentPairKernel theta hatom).fst = D
  exact Measure.fst_compProd D (F.independentPairKernel theta hatom)

/-- Coordinatewise first moments lift from the source outer law to the actual
profile/ranking-pair experiment. -/
theorem plackettLuce_joint_coordinate_integrable {n : ℕ}
    (D : Measure (ValueProfile n)) [IsProbabilityMeasure D] (theta : ℝ)
    (hatom : ∀ ranking : Ranking n,
      Measurable fun value : ValueProfile n =>
        plackettLuceRankingPMF theta value ranking)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D)
    (c : Candidate n) :
    Integrable (fun x : ValueProfile n × RankingPair n => x.1 c)
      ((plackettLuceDistributionalFamily (n := n)).outerIndependentPairJointLaw D theta
        hatom) := by
  have hpres := plackettLuce_outerJointLaw_fst_measurePreserving D theta hatom
  simpa [Function.comp_def] using hpres.integrable_comp_of_integrable (hvalue c)

private theorem measurableSet_plackettLuce_jointPair_eq {n : ℕ}
    (pair : RankingPair n) :
    MeasurableSet {x : ValueProfile n × RankingPair n | x.2 = pair} := by
  change MeasurableSet (Prod.snd ⁻¹' {pair' : RankingPair n | pair' = pair})
  exact (Set.toFinite {pair' : RankingPair n | pair' = pair}).measurableSet.preimage
    measurable_snd

/-- Raw shared second-mover utility is integrable under the actual joint law.
The proof partitions the finite ranking-pair fiber rather than inferring
joint integrability from a totalized outer integral. -/
theorem plackettLuce_joint_shared_payoff_integrable {n : ℕ}
    (D : Measure (ValueProfile n)) [IsProbabilityMeasure D] (theta : ℝ)
    (hatom : ∀ ranking : Ranking n,
      Measurable fun value : ValueProfile n =>
        plackettLuceRankingPMF theta value ranking)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D) :
    Integrable jointSharedSecondMoverPayoff
      ((plackettLuceDistributionalFamily (n := n)).outerIndependentPairJointLaw D theta
        hatom) := by
  let F := plackettLuceDistributionalFamily (n := n)
  let M := F.outerIndependentPairJointLaw D theta hatom
  have hsum : Integrable (fun x : ValueProfile n × RankingPair n =>
      ∑ pair : RankingPair n,
        Set.indicator {x | x.2 = pair}
          (fun x => x.1 (secondChoice pair.1)) x) M := by
    refine MeasureTheory.integrable_finset_sum Finset.univ ?_
    intro pair _
    exact (plackettLuce_joint_coordinate_integrable D theta hatom hvalue
      (secondChoice pair.1)).indicator (measurableSet_plackettLuce_jointPair_eq pair)
  convert hsum using 1
  funext x
  classical
  simp only [jointSharedSecondMoverPayoff, secondMoverUtility,
    Set.indicator_apply, Set.mem_setOf_eq, bestRemainingAfter_of_eq]
  rw [Finset.sum_ite_eq]
  simp

/-- Raw independent second-mover utility is integrable under the actual joint
law, by the same finite ranking-pair partition. -/
theorem plackettLuce_joint_independent_payoff_integrable {n : ℕ}
    (D : Measure (ValueProfile n)) [IsProbabilityMeasure D] (theta : ℝ)
    (hatom : ∀ ranking : Ranking n,
      Measurable fun value : ValueProfile n =>
        plackettLuceRankingPMF theta value ranking)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D) :
    Integrable jointIndependentSecondMoverPayoff
      ((plackettLuceDistributionalFamily (n := n)).outerIndependentPairJointLaw D theta
        hatom) := by
  let F := plackettLuceDistributionalFamily (n := n)
  let M := F.outerIndependentPairJointLaw D theta hatom
  have hsum : Integrable (fun x : ValueProfile n × RankingPair n =>
      ∑ pair : RankingPair n,
        Set.indicator {x | x.2 = pair}
          (fun x => x.1 (bestRemainingAfter pair.1 (firstChoice pair.2))) x) M := by
    refine MeasureTheory.integrable_finset_sum Finset.univ ?_
    intro pair _
    exact (plackettLuce_joint_coordinate_integrable D theta hatom hvalue
      (bestRemainingAfter pair.1 (firstChoice pair.2))).indicator
        (measurableSet_plackettLuce_jointPair_eq pair)
  convert hsum using 1
  funext x
  classical
  simp only [jointIndependentSecondMoverPayoff, secondMoverUtility,
    Set.indicator_apply, Set.mem_setOf_eq]
  rw [Finset.sum_ite_eq]
  simp

/-- The raw restricted reranking gain is integrable in the full source
experiment under visible first-moment and kernel-regularity assumptions. -/
theorem plackettLuce_joint_rerankingGain_integrable {n : ℕ}
    (D : Measure (ValueProfile n)) [IsProbabilityMeasure D] (theta : ℝ)
    (hatom : ∀ ranking : Ranking n,
      Measurable fun value : ValueProfile n =>
        plackettLuceRankingPMF theta value ranking)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D) :
    Integrable (fun x : ValueProfile n × RankingPair n => pairRerankingGain x.1 x.2)
      ((plackettLuceDistributionalFamily (n := n)).outerIndependentPairJointLaw D theta
        hatom) := by
  exact (plackettLuceDistributionalFamily (n := n)).jointRerankingGain_integrable_of_jointPayoffs
    D theta hatom
    (plackettLuce_joint_shared_payoff_integrable D theta hatom hvalue)
    (plackettLuce_joint_independent_payoff_integrable D theta hatom hvalue)

/-- The source's conditional statement for sequential Plackett--Luce is true
under the actual joint profile/ranking-pair probability law: the conditional
first-position-minus-second-position gain on top disagreement is zero.  The
only analytic conditions are a measurable conditional PMF kernel and finite
coordinatewise first moments of the outer value distribution. -/
theorem plackettLuce_jointLawDisagreementConditionalGain_eq_zero_of_kernel_regular {n : ℕ}
    (D : Measure (ValueProfile n)) [IsProbabilityMeasure D] (theta : ℝ)
    (hatom : ∀ ranking : Ranking n,
      Measurable fun value : ValueProfile n =>
        plackettLuceRankingPMF theta value ranking)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D) :
    jointLawDisagreementConditionalGain
      (plackettLuceDistributionalFamily (n := n)) D theta hatom = 0 := by
  rw [jointLawDisagreementConditionalGain_eq_outerDisagreementConditionalGain
    (plackettLuceDistributionalFamily (n := n)) D theta hatom
    (plackettLuce_joint_rerankingGain_integrable D theta hatom hvalue)]
  exact plackettLuce_outerDisagreementConditionalGain_eq_zero D theta

/-- Source-law endpoint for the Plackett--Luce discussion: values are drawn
from an arbitrary probability distribution with finite coordinatewise first
moments, then two rankings are conditionally drawn from the literal sequential
law in equation (7).  The actual conditional gain on top disagreement is
zero. -/
theorem plackettLuce_jointLawDisagreementConditionalGain_eq_zero {n : ℕ}
    (D : Measure (ValueProfile n)) [IsProbabilityMeasure D] (theta : ℝ)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D) :
    jointLawDisagreementConditionalGain
      (plackettLuceDistributionalFamily (n := n)) D theta
      (fun ranking => plackettLuce_ranking_atom_measurable theta ranking) = 0 := by
  exact plackettLuce_jointLawDisagreementConditionalGain_eq_zero_of_kernel_regular
    D theta (fun ranking => plackettLuce_ranking_atom_measurable theta ranking) hvalue

/-- Complete source conditional-event endpoint for Plackett--Luce: its
top-disagreement event has positive mass and its literal conditional
reranking gain is zero.  On that event,
`plackettLuce_pairRerankingGain_eq_sourceGap_of_disagreement` identifies the
integrand with the paper's first-position-minus-second-position expression. -/
theorem plackettLuce_source_jointConditionalGain_zero {n : ℕ}
    (D : Measure (ValueProfile n)) [IsProbabilityMeasure D] (theta : ℝ)
    (hvalue : ∀ c : Candidate n,
      Integrable (fun value : ValueProfile n => value c) D) :
    (0 < ∫ x : ValueProfile n × RankingPair n,
      (if disagreementEvent x.2 then (1 : ℝ) else 0) ∂
        (plackettLuceDistributionalFamily (n := n)).outerIndependentPairJointLaw D theta
          (fun ranking => plackettLuce_ranking_atom_measurable theta ranking)) ∧
      jointLawDisagreementConditionalGain
        (plackettLuceDistributionalFamily (n := n)) D theta
        (fun ranking => plackettLuce_ranking_atom_measurable theta ranking) = 0 := by
  exact ⟨plackettLuce_outerJointDisagreementEvent_pos D theta,
    plackettLuce_jointLawDisagreementConditionalGain_eq_zero D theta hvalue⟩

end DistributionalAccuracyFamily

end KR21Monoculture
