import FalahatgarEtAl2017MaxingRanking.AdaptiveFreshSeqEliminate
import FalahatgarEtAl2017MaxingRanking.PickAnchorSeqEliminate

/-!
# Fresh-call Seq-Eliminate on a Pick-Anchor sample

Appendix A.5 first fixes the sample `Q`, then calls `Seq-Eliminate` with
fresh observations.  This file records the conditional sampled-winner bound
before it is mixed over Pick-Anchor's uniform sampling law.
-/

namespace FalahatgarEtAl2017MaxingRanking

open AppliedModelingLib PreferenceRL
open MeasureTheory ProbabilityTheory

/-- The finite failure probability for fresh Seq-Eliminate on one fixed sample. -/
noncomputable def freshPickAnchorSampleFailureProbability
    {Arm Outcome : Type*} [Fintype Arm] [DecidableEq Arm]
    [Fintype Outcome] [DecidableEq Outcome]
    {count : ℕ} (sample : finiteFreshList Arm count ∅) (hcount : 0 < count)
    (outcomeLaw : AdaptiveOutcomeKernel Arm Outcome)
    (observation : ℕ → Arm → Arm → ℕ → Outcome → ℝ)
    (preferenceGap : Arm → Arm → ℝ) (epsilon eta : ℝ) : ℝ :=
  pmfProbClassical
    (freshAdaptiveCompareSeqEliminateStateLaw
      (pickAnchorSampleInitial sample hcount)
      (pickAnchorSampleChallengers sample) outcomeLaw observation
      preferenceGap epsilon eta)
    (fun stateFailure => ¬ ∀ arm ∈ pickAnchorSampleSet sample,
      -epsilon ≤ preferenceGap stateFailure.1 arm)

/--
For one realized Pick-Anchor sample, fresh adaptive comparison calls fail to
return an `ε`-maximum of that sample with probability at most one call budget
per actual challenger.
-/
theorem freshPickAnchorSample_failure_probability_le_callBudget
    {Arm Outcome : Type*} [Fintype Arm] [armDecidable : DecidableEq Arm]
    [Fintype Outcome] [DecidableEq Outcome]
    [MeasurableSpace Outcome] [DiscreteMeasurableSpace Outcome]
    {count : ℕ} (sample : finiteFreshList Arm count ∅) (hcount : 0 < count)
    (outcomeLaw : AdaptiveOutcomeKernel Arm Outcome)
    (observation : ℕ → Arm → Arm → ℕ → Outcome → ℝ)
    (preferenceGap : Arm → Arm → ℝ) (epsilon eta : ℝ)
    (hindependent : ∀ queryIndex < (pickAnchorSampleChallengers sample).length,
      ∀ incumbent,
        iIndepFun (observation queryIndex
          ((pickAnchorSampleChallengers sample).getD queryIndex
            (pickAnchorSampleInitial sample hcount)) incumbent)
          (outcomeLaw queryIndex incumbent).toMeasure)
    (hmeasurable : ∀ queryIndex < (pickAnchorSampleChallengers sample).length,
      ∀ incumbent sampleIndex,
        Measurable (observation queryIndex
          ((pickAnchorSampleChallengers sample).getD queryIndex
            (pickAnchorSampleInitial sample hcount)) incumbent sampleIndex))
    (hbounded : ∀ queryIndex < (pickAnchorSampleChallengers sample).length,
      ∀ incumbent,
        ∀ sampleIndex < fixedSampleBudget 0 epsilon eta,
          ∀ᵐ outcome ∂(outcomeLaw queryIndex incumbent).toMeasure,
            observation queryIndex ((pickAnchorSampleChallengers sample).getD queryIndex
              (pickAnchorSampleInitial sample hcount)) incumbent sampleIndex outcome ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ queryIndex < (pickAnchorSampleChallengers sample).length,
      ∀ incumbent,
        ∀ sampleIndex < fixedSampleBudget 0 epsilon eta,
        (outcomeLaw queryIndex incumbent).toMeasure[
            observation queryIndex ((pickAnchorSampleChallengers sample).getD queryIndex
              (pickAnchorSampleInitial sample hcount)) incumbent sampleIndex] =
              1 / 2 + preferenceGap ((pickAnchorSampleChallengers sample).getD queryIndex
                (pickAnchorSampleInitial sample hcount)) incumbent)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hself : ∀ arm, preferenceGap arm arm = 0)
    (hcomplete : PreferenceComplete preferenceGap)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hepsilon : 0 < epsilon) (heta : 0 < eta) (hetaLeOne : eta ≤ 1) :
    freshPickAnchorSampleFailureProbability sample hcount outcomeLaw observation
      preferenceGap epsilon eta ≤
      ((pickAnchorSampleChallengers sample).length : ℝ) * eta := by
  classical
  letI : DecidableEq Arm := armDecidable
  let maximum : Arm := Classical.choose (exists_pickAnchorSample_localMaximum
    sample hcount preferenceGap hcomplete hsst)
  have hmaximumSpec := Classical.choose_spec (exists_pickAnchorSample_localMaximum
    sample hcount preferenceGap hcomplete hsst)
  have hmaximum : ListAbsoluteMaximum preferenceGap maximum
      (pickAnchorSampleInitial sample hcount) (pickAnchorSampleChallengers sample) :=
    pickAnchorSample_listAbsoluteMaximum_of_localMaximum sample hcount preferenceGap maximum
      hmaximumSpec.1 hmaximumSpec.2
  have hsuccess := freshAdaptiveCompareSeqEliminate_listEpsilonMaximum_probability
    (pickAnchorSampleInitial sample hcount) (pickAnchorSampleChallengers sample)
    outcomeLaw observation preferenceGap epsilon eta
    hindependent hmeasurable hbounded hmean hantisymmetric hself hsst
    hepsilon heta hetaLeOne maximum hmaximum
  unfold freshAdaptiveCompareSeqEliminateListEpsilonMaximumProbability at hsuccess
  unfold freshPickAnchorSampleFailureProbability
  calc
    pmfProbClassical
        (freshAdaptiveCompareSeqEliminateStateLaw
          (pickAnchorSampleInitial sample hcount)
          (pickAnchorSampleChallengers sample) outcomeLaw observation
          preferenceGap epsilon eta)
        (fun stateFailure => ¬ ∀ arm ∈ pickAnchorSampleSet sample,
          -epsilon ≤ preferenceGap stateFailure.1 arm) ≤
        pmfProbClassical
          (freshAdaptiveCompareSeqEliminateStateLaw
            (pickAnchorSampleInitial sample hcount)
            (pickAnchorSampleChallengers sample) outcomeLaw observation
            preferenceGap epsilon eta)
          (fun stateFailure => ¬ ListEpsilonMaximum preferenceGap epsilon
            (pickAnchorSampleInitial sample hcount)
            (pickAnchorSampleChallengers sample) stateFailure.1) := by
      apply pmfProbClassical_le_of_imp
      intro stateFailure hfailure hlocal
      exact hfailure
        (pickAnchorSample_listEpsilonMaximum_implies_sampleEpsilonMaximum
          sample hcount preferenceGap epsilon stateFailure.1 hlocal)
    _ = 1 - pmfProbClassical
          (freshAdaptiveCompareSeqEliminateStateLaw
            (pickAnchorSampleInitial sample hcount)
            (pickAnchorSampleChallengers sample) outcomeLaw observation
            preferenceGap epsilon eta)
          (fun stateFailure => ListEpsilonMaximum preferenceGap epsilon
            (pickAnchorSampleInitial sample hcount)
            (pickAnchorSampleChallengers sample) stateFailure.1) :=
      pmfProbClassical_compl _ _
    _ ≤ ((pickAnchorSampleChallengers sample).length : ℝ) * eta := by
      linarith

/--
The joint law first samples Pick-Anchor's finite set, then runs its fresh
adaptive comparison process conditional on that realized sample.
-/
noncomputable def freshPickAnchorJointLaw
    {Arm Outcome : Type*} [Fintype Arm]
    [Fintype Outcome] [DecidableEq Outcome]
    {count : ℕ} (sampleLaw : PMF (finiteFreshList Arm count ∅))
    (outcomeLaw : finiteFreshList Arm count ∅ → AdaptiveOutcomeKernel Arm Outcome)
    (observation : finiteFreshList Arm count ∅ → ℕ → Arm → Arm → ℕ → Outcome → ℝ)
    (preferenceGap : Arm → Arm → ℝ) (epsilon eta : ℝ) (hcount : 0 < count) :
    PMF (finiteFreshList Arm count ∅ × (Arm × Bool)) := by
  classical
  exact sampleLaw.bind fun sample =>
    (freshAdaptiveCompareSeqEliminateStateLaw
      (pickAnchorSampleInitial sample hcount)
      (pickAnchorSampleChallengers sample) (outcomeLaw sample) (observation sample)
      preferenceGap epsilon eta).map fun stateFailure => (sample, stateFailure)

/-- The sampled-winner failure probability under the joint fresh-call law. -/
noncomputable def freshPickAnchorJointFailureProbability
    {Arm Outcome : Type*} [Fintype Arm] [DecidableEq Arm]
    [Fintype Outcome] [DecidableEq Outcome]
    {count : ℕ} (sampleLaw : PMF (finiteFreshList Arm count ∅))
    (outcomeLaw : finiteFreshList Arm count ∅ → AdaptiveOutcomeKernel Arm Outcome)
    (observation : finiteFreshList Arm count ∅ → ℕ → Arm → Arm → ℕ → Outcome → ℝ)
    (preferenceGap : Arm → Arm → ℝ) (epsilon eta : ℝ) (hcount : 0 < count) : ℝ :=
  pmfProbClassical
    (freshPickAnchorJointLaw sampleLaw outcomeLaw observation preferenceGap epsilon eta hcount)
    (fun sampleStateFailure => ¬ ∀ arm ∈ pickAnchorSampleSet sampleStateFailure.1,
      -epsilon ≤ preferenceGap sampleStateFailure.2.1 arm)

/-- The named joint-failure quantity exposes its exact finite event probability. -/
theorem freshPickAnchorJointFailureProbability_eq_pmfProbClassical
    {Arm Outcome : Type*} [Fintype Arm] [DecidableEq Arm]
    [Fintype Outcome] [DecidableEq Outcome]
    {count : ℕ} (sampleLaw : PMF (finiteFreshList Arm count ∅))
    (outcomeLaw : finiteFreshList Arm count ∅ → AdaptiveOutcomeKernel Arm Outcome)
    (observation : finiteFreshList Arm count ∅ → ℕ → Arm → Arm → ℕ → Outcome → ℝ)
    (preferenceGap : Arm → Arm → ℝ) (epsilon eta : ℝ) (hcount : 0 < count) :
    freshPickAnchorJointFailureProbability sampleLaw outcomeLaw observation preferenceGap
        epsilon eta hcount =
      pmfProbClassical
        (freshPickAnchorJointLaw sampleLaw outcomeLaw observation preferenceGap epsilon eta hcount)
        (fun sampleStateFailure => ¬ ∀ arm ∈ pickAnchorSampleSet sampleStateFailure.1,
          -epsilon ≤ preferenceGap sampleStateFailure.2.1 arm) := by
  rfl

/--
A uniform conditional failure bound remains valid after mixing over a finite
Pick-Anchor sampling law.
-/
theorem freshPickAnchorJoint_failure_probability_le_of_samplewise
    {Arm Outcome : Type*} [Fintype Arm] [DecidableEq Arm]
    [Fintype Outcome] [DecidableEq Outcome]
    {count : ℕ} (sampleLaw : PMF (finiteFreshList Arm count ∅))
    (outcomeLaw : finiteFreshList Arm count ∅ → AdaptiveOutcomeKernel Arm Outcome)
    (observation : finiteFreshList Arm count ∅ → ℕ → Arm → Arm → ℕ → Outcome → ℝ)
    (preferenceGap : Arm → Arm → ℝ) (epsilon eta failureBudget : ℝ) (hcount : 0 < count)
    (hsamplewise : ∀ sample,
      freshPickAnchorSampleFailureProbability sample hcount (outcomeLaw sample)
        (observation sample) preferenceGap epsilon eta ≤ failureBudget) :
    freshPickAnchorJointFailureProbability sampleLaw outcomeLaw observation preferenceGap
      epsilon eta hcount ≤ failureBudget := by
  unfold freshPickAnchorJointFailureProbability
  rw [pmfProbClassical_eq_pmfProb]
  unfold freshPickAnchorJointLaw
  apply pmfProb_adaptiveStep_le_of_historywiseBound sampleLaw
    (fun sample => freshAdaptiveCompareSeqEliminateStateLaw
      (pickAnchorSampleInitial sample hcount)
      (pickAnchorSampleChallengers sample) (outcomeLaw sample) (observation sample)
      preferenceGap epsilon eta)
    (fun sample stateFailure => ¬ ∀ arm ∈ pickAnchorSampleSet sample,
      -epsilon ≤ preferenceGap stateFailure.1 arm)
    failureBudget
  intro sample
  simpa only [freshPickAnchorSampleFailureProbability, pmfProbClassical_eq_pmfProb] using
    hsamplewise sample

/--
For every finite Pick-Anchor sample of a fixed size, the fresh joint law
charges only the `count - 1` realized Seq-Eliminate calls.
-/
theorem freshPickAnchorJoint_failure_probability_le_callBudget
    {Arm Outcome : Type*} [Fintype Arm] [DecidableEq Arm]
    [Fintype Outcome] [DecidableEq Outcome]
    [MeasurableSpace Outcome] [DiscreteMeasurableSpace Outcome]
    {count : ℕ} (sampleLaw : PMF (finiteFreshList Arm count ∅)) (hcount : 0 < count)
    (outcomeLaw : finiteFreshList Arm count ∅ → AdaptiveOutcomeKernel Arm Outcome)
    (observation : finiteFreshList Arm count ∅ → ℕ → Arm → Arm → ℕ → Outcome → ℝ)
    (preferenceGap : Arm → Arm → ℝ) (epsilon eta : ℝ)
    (hindependent : ∀ sample, ∀ queryIndex < (pickAnchorSampleChallengers sample).length,
      ∀ incumbent,
        iIndepFun (observation sample queryIndex
          ((pickAnchorSampleChallengers sample).getD queryIndex
            (pickAnchorSampleInitial sample hcount)) incumbent)
          (outcomeLaw sample queryIndex incumbent).toMeasure)
    (hmeasurable : ∀ sample, ∀ queryIndex < (pickAnchorSampleChallengers sample).length,
      ∀ incumbent sampleIndex,
        Measurable (observation sample queryIndex
          ((pickAnchorSampleChallengers sample).getD queryIndex
            (pickAnchorSampleInitial sample hcount)) incumbent sampleIndex))
    (hbounded : ∀ sample, ∀ queryIndex < (pickAnchorSampleChallengers sample).length,
      ∀ incumbent,
        ∀ sampleIndex < fixedSampleBudget 0 epsilon eta,
          ∀ᵐ outcome ∂(outcomeLaw sample queryIndex incumbent).toMeasure,
            observation sample queryIndex ((pickAnchorSampleChallengers sample).getD queryIndex
              (pickAnchorSampleInitial sample hcount)) incumbent sampleIndex outcome ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ sample, ∀ queryIndex < (pickAnchorSampleChallengers sample).length,
      ∀ incumbent,
        ∀ sampleIndex < fixedSampleBudget 0 epsilon eta,
        (outcomeLaw sample queryIndex incumbent).toMeasure[
            observation sample queryIndex ((pickAnchorSampleChallengers sample).getD queryIndex
              (pickAnchorSampleInitial sample hcount)) incumbent sampleIndex] =
              1 / 2 + preferenceGap ((pickAnchorSampleChallengers sample).getD queryIndex
                (pickAnchorSampleInitial sample hcount)) incumbent)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hself : ∀ arm, preferenceGap arm arm = 0)
    (hcomplete : PreferenceComplete preferenceGap)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hepsilon : 0 < epsilon) (heta : 0 < eta) (hetaLeOne : eta ≤ 1) :
    freshPickAnchorJointFailureProbability sampleLaw outcomeLaw observation preferenceGap
      epsilon eta hcount ≤ ((count - 1 : ℕ) : ℝ) * eta := by
  apply freshPickAnchorJoint_failure_probability_le_of_samplewise
    sampleLaw outcomeLaw observation preferenceGap epsilon eta
    (((count - 1 : ℕ) : ℝ) * eta) hcount
  intro sample
  calc
    freshPickAnchorSampleFailureProbability sample hcount (outcomeLaw sample)
        (observation sample) preferenceGap epsilon eta ≤
        ((pickAnchorSampleChallengers sample).length : ℝ) * eta :=
      freshPickAnchorSample_failure_probability_le_callBudget sample hcount
        (outcomeLaw sample) (observation sample) preferenceGap epsilon eta
        (hindependent sample) (hmeasurable sample) (hbounded sample) (hmean sample)
        hantisymmetric hself hcomplete hsst hepsilon heta hetaLeOne
    _ = ((count - 1 : ℕ) : ℝ) * eta := by
      rw [pickAnchorSampleChallengers_length sample hcount]

/--
With the source allocation `η = δ / (2 |Q|)`, the random sampled winner
fails to be an `ε`-maximum of its realized sample with probability at most
`δ / 2`.
-/
theorem freshPickAnchorJoint_failure_probability_le_delta_half_of_sourceSchedule
    {Arm Outcome : Type*} [Fintype Arm] [DecidableEq Arm]
    [Fintype Outcome] [DecidableEq Outcome]
    [MeasurableSpace Outcome] [DiscreteMeasurableSpace Outcome]
    {count : ℕ} (sampleLaw : PMF (finiteFreshList Arm count ∅)) (hcount : 0 < count)
    (outcomeLaw : finiteFreshList Arm count ∅ → AdaptiveOutcomeKernel Arm Outcome)
    (observation : finiteFreshList Arm count ∅ → ℕ → Arm → Arm → ℕ → Outcome → ℝ)
    (preferenceGap : Arm → Arm → ℝ) (delta epsilon : ℝ)
    (hindependent : ∀ sample, ∀ queryIndex < (pickAnchorSampleChallengers sample).length,
      ∀ incumbent,
        iIndepFun (observation sample queryIndex
          ((pickAnchorSampleChallengers sample).getD queryIndex
            (pickAnchorSampleInitial sample hcount)) incumbent)
          (outcomeLaw sample queryIndex incumbent).toMeasure)
    (hmeasurable : ∀ sample, ∀ queryIndex < (pickAnchorSampleChallengers sample).length,
      ∀ incumbent sampleIndex,
        Measurable (observation sample queryIndex
          ((pickAnchorSampleChallengers sample).getD queryIndex
            (pickAnchorSampleInitial sample hcount)) incumbent sampleIndex))
    (hbounded : ∀ sample, ∀ queryIndex < (pickAnchorSampleChallengers sample).length,
      ∀ incumbent,
        ∀ sampleIndex < fixedSampleBudget 0 epsilon ((delta / 2) / (count : ℝ)),
          ∀ᵐ outcome ∂(outcomeLaw sample queryIndex incumbent).toMeasure,
            observation sample queryIndex ((pickAnchorSampleChallengers sample).getD queryIndex
              (pickAnchorSampleInitial sample hcount)) incumbent sampleIndex outcome ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ sample, ∀ queryIndex < (pickAnchorSampleChallengers sample).length,
      ∀ incumbent,
        ∀ sampleIndex < fixedSampleBudget 0 epsilon ((delta / 2) / (count : ℝ)),
        (outcomeLaw sample queryIndex incumbent).toMeasure[
            observation sample queryIndex ((pickAnchorSampleChallengers sample).getD queryIndex
              (pickAnchorSampleInitial sample hcount)) incumbent sampleIndex] =
              1 / 2 + preferenceGap ((pickAnchorSampleChallengers sample).getD queryIndex
                (pickAnchorSampleInitial sample hcount)) incumbent)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hself : ∀ arm, preferenceGap arm arm = 0)
    (hcomplete : PreferenceComplete preferenceGap)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) (hepsilon : 0 < epsilon) :
    freshPickAnchorJointFailureProbability sampleLaw outcomeLaw observation preferenceGap
      epsilon ((delta / 2) / (count : ℝ)) hcount ≤ delta / 2 := by
  have hcountNat : 1 ≤ count := by omega
  have hcountReal : 0 < (count : ℝ) := by exact_mod_cast hcount
  have hcountOne : (1 : ℝ) ≤ (count : ℝ) := by exact_mod_cast hcountNat
  have heta : 0 < (delta / 2) / (count : ℝ) := by positivity
  have hetaLeOne : (delta / 2) / (count : ℝ) ≤ 1 := by
    rw [div_le_iff₀ hcountReal]
    nlinarith
  calc
    freshPickAnchorJointFailureProbability sampleLaw outcomeLaw observation preferenceGap
        epsilon ((delta / 2) / (count : ℝ)) hcount ≤
        ((count - 1 : ℕ) : ℝ) * ((delta / 2) / (count : ℝ)) :=
      freshPickAnchorJoint_failure_probability_le_callBudget sampleLaw hcount
        outcomeLaw observation preferenceGap epsilon ((delta / 2) / (count : ℝ))
        hindependent hmeasurable hbounded hmean hantisymmetric hself hcomplete hsst
        hepsilon heta hetaLeOne
    _ ≤ (count : ℝ) * ((delta / 2) / (count : ℝ)) := by
      apply mul_le_mul_of_nonneg_right
        (show ((count - 1 : ℕ) : ℝ) ≤ (count : ℝ) by exact_mod_cast Nat.sub_le count 1)
        (le_of_lt heta)
    _ = delta / 2 := by
      field_simp [ne_of_gt hcountReal]

/--
Lemma 3's two-event argument on a finite joint PMF: a top-set hit and a
sample-local `ε`-maximum imply a good anchor.
-/
theorem pickAnchor_goodAnchor_pmf_probability_of_topSetHit_and_sampleWinner
    {Arm Ω : Type*} [Fintype Arm] [DecidableEq Arm]
    [Fintype Ω] [DecidableEq Ω]
    (law : PMF Ω) (sample : Ω → Finset Arm) (winner : Ω → Arm)
    (top : Finset Arm) (preferenceGap : Arm → Arm → ℝ) (epsilon : ℝ) (cutoff : ℕ)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hepsilon : 0 ≤ epsilon)
    (htopRank : ∀ pivot ∈ top,
      (strictlyBetterArms preferenceGap pivot).card ≤ cutoff)
    (delta : ℝ)
    (hmiss : pmfProbClassical law
      (fun outcome => ¬ ∃ pivot, pivot ∈ top ∧ pivot ∈ sample outcome) ≤ delta / 2)
    (hwinnerFailure : pmfProbClassical law
      (fun outcome => ¬ ∀ arm ∈ sample outcome,
        -epsilon ≤ preferenceGap (winner outcome) arm) ≤ delta / 2) :
    1 - delta ≤ pmfProbClassical law
      (fun outcome => GoodAnchor preferenceGap epsilon cutoff (winner outcome)) := by
  classical
  let miss : Ω → Prop := fun outcome =>
    ¬ ∃ pivot, pivot ∈ top ∧ pivot ∈ sample outcome
  let winnerFailure : Ω → Prop := fun outcome =>
    ¬ ∀ arm ∈ sample outcome, -epsilon ≤ preferenceGap (winner outcome) arm
  have hfailureSubset : ∀ outcome,
      ¬ GoodAnchor preferenceGap epsilon cutoff (winner outcome) →
        miss outcome ∨ winnerFailure outcome := by
    intro outcome hnotGood
    by_contra hnotUnion
    have hhit : ∃ pivot, pivot ∈ top ∧ pivot ∈ sample outcome := by
      by_contra hnoHit
      exact hnotUnion (Or.inl hnoHit)
    have hwinner : ∀ arm ∈ sample outcome,
        -epsilon ≤ preferenceGap (winner outcome) arm := by
      by_contra hnoWinner
      exact hnotUnion (Or.inr hnoWinner)
    rcases hhit with ⟨pivot, hpivotTop, hpivotSample⟩
    exact hnotGood (goodAnchor_of_subsetEpsilonMaximum preferenceGap epsilon cutoff
      hantisymmetric hsst hepsilon (sample outcome) pivot (winner outcome)
      hpivotSample hwinner (htopRank pivot hpivotTop))
  have hunion : pmfProb law (fun outcome => miss outcome ∨ winnerFailure outcome) ≤
      pmfProb law miss + pmfProb law winnerFailure := by
    calc
      pmfProb law (fun outcome => miss outcome ∨ winnerFailure outcome) =
          pmfExp law (fun outcome =>
            if miss outcome ∨ winnerFailure outcome then (1 : ℝ) else 0) := rfl
      _ ≤ pmfExp law (fun outcome =>
            (if miss outcome then (1 : ℝ) else 0) +
              (if winnerFailure outcome then (1 : ℝ) else 0)) := by
        apply pmfExp_le_pmfExp_of_forall_le
        intro outcome
        by_cases hmissOutcome : miss outcome <;>
          by_cases hwinnerFailureOutcome : winnerFailure outcome <;>
          simp [hmissOutcome, hwinnerFailureOutcome]
      _ = pmfProb law miss + pmfProb law winnerFailure := by
        rw [pmfExp_add]
        rfl
  have hfailure : pmfProb law
      (fun outcome => ¬ GoodAnchor preferenceGap epsilon cutoff (winner outcome)) ≤ delta := by
    calc
      pmfProb law (fun outcome => ¬ GoodAnchor preferenceGap epsilon cutoff (winner outcome)) ≤
          pmfProb law (fun outcome => miss outcome ∨ winnerFailure outcome) :=
        pmfProb_le_of_imp law _ _ hfailureSubset
      _ ≤ pmfProb law miss + pmfProb law winnerFailure := hunion
      _ ≤ delta := by
        rw [← pmfProbClassical_eq_pmfProb law miss,
          ← pmfProbClassical_eq_pmfProb law winnerFailure]
        change pmfProbClassical law
            (fun outcome => ¬ ∃ pivot, pivot ∈ top ∧ pivot ∈ sample outcome) +
            pmfProbClassical law
              (fun outcome => ¬ ∀ arm ∈ sample outcome,
                -epsilon ≤ preferenceGap (winner outcome) arm) ≤ delta
        linarith
  rw [pmfProbClassical_eq_pmfProb]
  rw [pmfProb_compl law
    (fun outcome => GoodAnchor preferenceGap epsilon cutoff (winner outcome))] at hfailure
  linarith

/-- The sample coordinate of the conditional fresh-call mixture has its input PMF law. -/
theorem freshPickAnchorJoint_pmfProbClassical_fst_eq
    {Arm Outcome : Type*} [Fintype Arm] [DecidableEq Arm]
    [Fintype Outcome] [DecidableEq Outcome]
    {count : ℕ} (sampleLaw : PMF (finiteFreshList Arm count ∅))
    (outcomeLaw : finiteFreshList Arm count ∅ → AdaptiveOutcomeKernel Arm Outcome)
    (observation : finiteFreshList Arm count ∅ → ℕ → Arm → Arm → ℕ → Outcome → ℝ)
    (preferenceGap : Arm → Arm → ℝ) (epsilon eta : ℝ) (hcount : 0 < count)
    (event : finiteFreshList Arm count ∅ → Prop) :
    pmfProbClassical
      (freshPickAnchorJointLaw sampleLaw outcomeLaw observation preferenceGap epsilon eta hcount)
      (fun sampleStateFailure => event sampleStateFailure.1) =
      pmfProbClassical sampleLaw event := by
  classical
  rw [pmfProbClassical_eq_pmfProb, pmfProbClassical_eq_pmfProb]
  unfold freshPickAnchorJointLaw
  rw [pmfProb_bind]
  simp_rw [pmfProb_map]
  unfold pmfProb
  apply pmfExp_congr
  intro sample
  by_cases hevent : event sample <;> simp [hevent, pmfExp_const]

/-- The good-anchor probability under the joint fresh sample-and-call law. -/
noncomputable def freshPickAnchorJointGoodAnchorProbability
    {Arm Outcome : Type*} [Fintype Arm]
    [Fintype Outcome] [DecidableEq Outcome]
    {count : ℕ} (sampleLaw : PMF (finiteFreshList Arm count ∅))
    (outcomeLaw : finiteFreshList Arm count ∅ → AdaptiveOutcomeKernel Arm Outcome)
    (observation : finiteFreshList Arm count ∅ → ℕ → Arm → Arm → ℕ → Outcome → ℝ)
    (preferenceGap : Arm → Arm → ℝ) (epsilon eta : ℝ) (cutoff : ℕ) (hcount : 0 < count) :
    ℝ := by
  classical
  exact pmfProbClassical
    (freshPickAnchorJointLaw sampleLaw outcomeLaw observation preferenceGap epsilon eta hcount)
    (fun sampleStateFailure =>
      GoodAnchor preferenceGap epsilon cutoff sampleStateFailure.2.1)

/-- The good-anchor probability for the source's uniform Pick-Anchor sample. -/
noncomputable def freshPickAnchorUniformGoodAnchorProbability
    {Arm Outcome : Type*} [Fintype Arm] [Nonempty Arm]
    [Fintype Outcome] [DecidableEq Outcome]
    (cutoff : ℕ) (delta epsilon : ℝ)
    (outcomeLaw : finiteFreshList Arm
      (pickAnchorSampleCount (Fintype.card Arm) cutoff delta) ∅ →
      AdaptiveOutcomeKernel Arm Outcome)
    (observation : finiteFreshList Arm
      (pickAnchorSampleCount (Fintype.card Arm) cutoff delta) ∅ →
      ℕ → Arm → Arm → ℕ → Outcome → ℝ)
    (preferenceGap : Arm → Arm → ℝ)
    (hcutoff : 0 < cutoff) (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) : ℝ := by
  classical
  exact freshPickAnchorJointGoodAnchorProbability
    (pickAnchorUniformSampleLaw
      (pickAnchorSampleCount (Fintype.card Arm) cutoff delta)
      (pickAnchorSampleCount_le_armCount (Fintype.card Arm) cutoff delta))
    outcomeLaw observation preferenceGap epsilon
    ((delta / 2) /
      (pickAnchorSampleCount (Fintype.card Arm) cutoff delta : ℝ)) cutoff
    (pickAnchorSampleCount_pos (Fintype.card Arm) cutoff delta
      Fintype.card_pos hcutoff hdelta hdeltaLeOne)

/-- A source-facing top-set rank condition, with finite-set decidability kept internal. -/
noncomputable def PickAnchorTopSetRankBound {Arm : Type*} [Fintype Arm]
    (preferenceGap : Arm → Arm → ℝ) (top : Finset Arm) (cutoff : ℕ) : Prop := by
  classical
  exact ∀ pivot ∈ top, (strictlyBetterArms preferenceGap pivot).card ≤ cutoff

/-- The source Pick-Anchor sample size is positive under its stated parameters. -/
theorem pickAnchorSourceSampleCount_pos {Arm : Type*} [Fintype Arm] [Nonempty Arm]
    (cutoff : ℕ) (delta : ℝ) (hcutoff : 0 < cutoff)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    0 < pickAnchorSampleCount (Fintype.card Arm) cutoff delta :=
  pickAnchorSampleCount_pos (Fintype.card Arm) cutoff delta
    Fintype.card_pos hcutoff hdelta hdeltaLeOne

/--
Lemma 3 / Appendix A.5, with fresh comparison batches conditional on each
realized uniform sample: the Pick-Anchor output is an `(ε, k)`-good anchor
with probability at least `1 - δ`.
-/
theorem freshPickAnchorUniform_goodAnchor_highProbability_of_sourceSchedule
    {Arm Outcome : Type*} [Fintype Arm] [Nonempty Arm]
    [Fintype Outcome] [DecidableEq Outcome]
    [MeasurableSpace Outcome] [DiscreteMeasurableSpace Outcome]
    (cutoff : ℕ) (delta epsilon : ℝ) (top : Finset Arm)
    (outcomeLaw : finiteFreshList Arm
      (pickAnchorSampleCount (Fintype.card Arm) cutoff delta) ∅ →
      AdaptiveOutcomeKernel Arm Outcome)
    (observation : finiteFreshList Arm
      (pickAnchorSampleCount (Fintype.card Arm) cutoff delta) ∅ →
      ℕ → Arm → Arm → ℕ → Outcome → ℝ)
    (preferenceGap : Arm → Arm → ℝ)
    (hcutoff : 0 < cutoff) (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1)
    (hepsilon : 0 < epsilon)
    (hindependent : ∀ sample, ∀ queryIndex < (pickAnchorSampleChallengers sample).length,
      ∀ incumbent,
        iIndepFun (observation sample queryIndex
          ((pickAnchorSampleChallengers sample).getD queryIndex
            (pickAnchorSampleInitial sample
              (pickAnchorSourceSampleCount_pos cutoff delta hcutoff hdelta hdeltaLeOne))) incumbent)
          (outcomeLaw sample queryIndex incumbent).toMeasure)
    (hmeasurable : ∀ sample, ∀ queryIndex < (pickAnchorSampleChallengers sample).length,
      ∀ incumbent sampleIndex,
        Measurable (observation sample queryIndex
          ((pickAnchorSampleChallengers sample).getD queryIndex
            (pickAnchorSampleInitial sample
              (pickAnchorSourceSampleCount_pos cutoff delta hcutoff hdelta hdeltaLeOne))) incumbent sampleIndex))
    (hbounded : ∀ sample, ∀ queryIndex < (pickAnchorSampleChallengers sample).length,
      ∀ incumbent,
        ∀ sampleIndex < fixedSampleBudget 0 epsilon
            ((delta / 2) /
              (pickAnchorSampleCount (Fintype.card Arm) cutoff delta : ℝ)),
          ∀ᵐ outcome ∂(outcomeLaw sample queryIndex incumbent).toMeasure,
            observation sample queryIndex ((pickAnchorSampleChallengers sample).getD queryIndex
              (pickAnchorSampleInitial sample
                (pickAnchorSourceSampleCount_pos cutoff delta hcutoff hdelta hdeltaLeOne)))
              incumbent sampleIndex outcome ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ sample, ∀ queryIndex < (pickAnchorSampleChallengers sample).length,
      ∀ incumbent,
        ∀ sampleIndex < fixedSampleBudget 0 epsilon
            ((delta / 2) /
              (pickAnchorSampleCount (Fintype.card Arm) cutoff delta : ℝ)),
          (outcomeLaw sample queryIndex incumbent).toMeasure[
            observation sample queryIndex ((pickAnchorSampleChallengers sample).getD queryIndex
              (pickAnchorSampleInitial sample
                (pickAnchorSourceSampleCount_pos cutoff delta hcutoff hdelta hdeltaLeOne)))
              incumbent sampleIndex] =
              1 / 2 + preferenceGap ((pickAnchorSampleChallengers sample).getD queryIndex
                (pickAnchorSampleInitial sample
                  (pickAnchorSourceSampleCount_pos cutoff delta hcutoff hdelta hdeltaLeOne))) incumbent)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hself : ∀ arm, preferenceGap arm arm = 0)
    (hcomplete : PreferenceComplete preferenceGap)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (htopCard : top.card = cutoff)
    (htopRank : PickAnchorTopSetRankBound preferenceGap top cutoff) :
    1 - delta ≤ freshPickAnchorUniformGoodAnchorProbability
      cutoff delta epsilon outcomeLaw observation preferenceGap hcutoff hdelta hdeltaLeOne := by
  classical
  change ∀ pivot ∈ top, (strictlyBetterArms preferenceGap pivot).card ≤ cutoff at htopRank
  let count : ℕ := pickAnchorSampleCount (Fintype.card Arm) cutoff delta
  let sampleLaw : PMF (finiteFreshList Arm count ∅) :=
    pickAnchorUniformSampleLaw count
      (pickAnchorSampleCount_le_armCount (Fintype.card Arm) cutoff delta)
  let hcount : 0 < count := pickAnchorSampleCount_pos (Fintype.card Arm) cutoff delta
    Fintype.card_pos hcutoff hdelta hdeltaLeOne
  change 1 - delta ≤ freshPickAnchorJointGoodAnchorProbability
    sampleLaw outcomeLaw observation preferenceGap epsilon ((delta / 2) / (count : ℝ)) cutoff hcount
  apply pickAnchor_goodAnchor_pmf_probability_of_topSetHit_and_sampleWinner
    (freshPickAnchorJointLaw sampleLaw outcomeLaw observation preferenceGap epsilon
      ((delta / 2) / (count : ℝ)) hcount)
    (fun sampleStateFailure => pickAnchorSampleSet sampleStateFailure.1)
    (fun sampleStateFailure => sampleStateFailure.2.1)
    top preferenceGap epsilon cutoff hantisymmetric hsst (le_of_lt hepsilon) htopRank delta
  · calc
      pmfProbClassical
          (freshPickAnchorJointLaw sampleLaw outcomeLaw observation preferenceGap epsilon
            ((delta / 2) / (count : ℝ)) hcount)
          (fun sampleStateFailure => ¬ ∃ pivot, pivot ∈ top ∧
            pivot ∈ pickAnchorSampleSet sampleStateFailure.1) =
          pmfProbClassical sampleLaw
            (fun sample => ¬ ∃ pivot, pivot ∈ top ∧ pivot ∈ pickAnchorSampleSet sample) :=
        freshPickAnchorJoint_pmfProbClassical_fst_eq sampleLaw outcomeLaw observation
          preferenceGap epsilon ((delta / 2) / (count : ℝ)) hcount
          (fun sample => ¬ ∃ pivot, pivot ∈ top ∧ pivot ∈ pickAnchorSampleSet sample)
      _ ≤ delta / 2 := by
        simpa only [sampleLaw, count] using
          (pickAnchor_miss_probability_le_delta_half cutoff delta top
            hcutoff htopCard hdelta hdeltaLeOne)
  · change freshPickAnchorJointFailureProbability sampleLaw outcomeLaw observation preferenceGap
      epsilon ((delta / 2) / (count : ℝ)) hcount ≤ delta / 2
    apply freshPickAnchorJoint_failure_probability_le_delta_half_of_sourceSchedule
      sampleLaw hcount outcomeLaw observation preferenceGap delta epsilon
    · exact hindependent
    · exact hmeasurable
    · exact hbounded
    · exact hmean
    · exact hantisymmetric
    · exact hself
    · exact hcomplete
    · exact hsst
    · exact hdelta
    · exact hdeltaLeOne
    · exact hepsilon

end FalahatgarEtAl2017MaxingRanking
