import FalahatgarEtAl2017MaxingRanking.FiniteBatchFreshSeqEliminate
import FalahatgarEtAl2017MaxingRanking.PickAnchorFreshSeqEliminate

/-!
# Canonical finite fresh Pick-Anchor

This file instantiates Lemma 3's conditional calls with the paper's actual
finite Bernoulli comparison batches, then mixes those calls over the uniform
without-replacement Pick-Anchor sample.
-/

namespace FalahatgarEtAl2017MaxingRanking

open AppliedModelingLib PreferenceRL
open MeasureTheory ProbabilityTheory

/-- The canonical fresh comparison kernel conditional on one Pick-Anchor sample. -/
noncomputable def canonicalFreshPickAnchorOutcomeLaw
    {Arm : Type*} {count : ℕ} (sample : finiteFreshList Arm count ∅) (hcount : 0 < count)
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (epsilon eta : ℝ) :
    AdaptiveOutcomeKernel Arm (Fin (fixedSampleBudget 0 epsilon eta) → Bool) :=
  canonicalFreshAdaptiveCompareOutcomeLaw (pickAnchorSampleInitial sample hcount)
    (pickAnchorSampleChallengers sample) preferenceGap hprobability epsilon eta

/-- The corresponding coordinate-score observation function is independent of the sample. -/
noncomputable def canonicalFreshPickAnchorObservation
    {Arm : Type*} {count : ℕ} (_sample : finiteFreshList Arm count ∅)
    (epsilon eta : ℝ) :
    ℕ → Arm → Arm → ℕ → (Fin (fixedSampleBudget 0 epsilon eta) → Bool) → ℝ :=
  canonicalFreshAdaptiveCompareObservation epsilon eta

/-- A fixed realized Pick-Anchor sample has its source per-call failure budget. -/
theorem canonicalFreshPickAnchorSample_failure_probability_le_callBudget
    {Arm : Type*} [Fintype Arm] [armDecidable : DecidableEq Arm]
    {count : ℕ} (sample : finiteFreshList Arm count ∅) (hcount : 0 < count)
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (epsilon eta : ℝ)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hself : ∀ arm, preferenceGap arm arm = 0)
    (hcomplete : PreferenceComplete preferenceGap)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hepsilon : 0 < epsilon) (heta : 0 < eta) (hetaLeOne : eta ≤ 1) :
    freshPickAnchorSampleFailureProbability sample hcount
      (canonicalFreshPickAnchorOutcomeLaw sample hcount preferenceGap hprobability epsilon eta)
      (canonicalFreshPickAnchorObservation sample epsilon eta)
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
  have hsuccess := canonicalFreshAdaptiveCompareSeqEliminate_listEpsilonMaximum_probability
    (pickAnchorSampleInitial sample hcount) (pickAnchorSampleChallengers sample)
    preferenceGap hprobability epsilon eta hantisymmetric hself hsst
    hepsilon heta hetaLeOne maximum hmaximum
  have hsuccess' : 1 - ((pickAnchorSampleChallengers sample).length : ℝ) * eta ≤
      freshAdaptiveCompareSeqEliminateListEpsilonMaximumProbability
        (pickAnchorSampleInitial sample hcount) (pickAnchorSampleChallengers sample)
        (canonicalFreshPickAnchorOutcomeLaw sample hcount preferenceGap hprobability epsilon eta)
        (canonicalFreshPickAnchorObservation sample epsilon eta)
        preferenceGap epsilon eta := by
    simpa only [canonicalFreshPickAnchorOutcomeLaw,
      canonicalFreshPickAnchorObservation] using hsuccess
  unfold freshAdaptiveCompareSeqEliminateListEpsilonMaximumProbability at hsuccess'
  rw [pmfProbClassical_eq_pmfProb] at hsuccess'
  unfold freshPickAnchorSampleFailureProbability
  calc
    pmfProbClassical
        (freshAdaptiveCompareSeqEliminateStateLaw
          (pickAnchorSampleInitial sample hcount)
          (pickAnchorSampleChallengers sample)
          (canonicalFreshPickAnchorOutcomeLaw sample hcount preferenceGap hprobability epsilon eta)
          (canonicalFreshPickAnchorObservation sample epsilon eta)
          preferenceGap epsilon eta)
        (fun stateFailure => ¬ ∀ arm ∈ pickAnchorSampleSet sample,
          -epsilon ≤ preferenceGap stateFailure.1 arm) =
        pmfProb
          (freshAdaptiveCompareSeqEliminateStateLaw
            (pickAnchorSampleInitial sample hcount)
            (pickAnchorSampleChallengers sample)
            (canonicalFreshPickAnchorOutcomeLaw sample hcount preferenceGap hprobability epsilon eta)
            (canonicalFreshPickAnchorObservation sample epsilon eta)
            preferenceGap epsilon eta)
          (fun stateFailure => ¬ ∀ arm ∈ pickAnchorSampleSet sample,
            -epsilon ≤ preferenceGap stateFailure.1 arm) :=
      pmfProbClassical_eq_pmfProb _ _
    _ ≤ pmfProb
          (freshAdaptiveCompareSeqEliminateStateLaw
            (pickAnchorSampleInitial sample hcount)
            (pickAnchorSampleChallengers sample)
            (canonicalFreshPickAnchorOutcomeLaw sample hcount preferenceGap hprobability epsilon eta)
            (canonicalFreshPickAnchorObservation sample epsilon eta)
            preferenceGap epsilon eta)
          (fun stateFailure => ¬ ListEpsilonMaximum preferenceGap epsilon
            (pickAnchorSampleInitial sample hcount)
            (pickAnchorSampleChallengers sample) stateFailure.1) := by
      apply pmfProb_le_of_imp
      intro stateFailure hfailure hlocal
      exact hfailure
        (pickAnchorSample_listEpsilonMaximum_implies_sampleEpsilonMaximum
          sample hcount preferenceGap epsilon stateFailure.1 hlocal)
    _ = 1 - pmfProb
          (freshAdaptiveCompareSeqEliminateStateLaw
            (pickAnchorSampleInitial sample hcount)
            (pickAnchorSampleChallengers sample)
            (canonicalFreshPickAnchorOutcomeLaw sample hcount preferenceGap hprobability epsilon eta)
            (canonicalFreshPickAnchorObservation sample epsilon eta)
            preferenceGap epsilon eta)
          (fun stateFailure => ListEpsilonMaximum preferenceGap epsilon
            (pickAnchorSampleInitial sample hcount)
            (pickAnchorSampleChallengers sample) stateFailure.1) :=
      pmfProb_compl _ _
    _ ≤ ((pickAnchorSampleChallengers sample).length : ℝ) * eta := by
      linarith [hsuccess']

/-- The finite mixture of canonical fresh calls pays only its realized `count - 1` calls. -/
theorem canonicalFreshPickAnchorJoint_failure_probability_le_callBudget
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    {count : ℕ} (sampleLaw : PMF (finiteFreshList Arm count ∅)) (hcount : 0 < count)
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (epsilon eta : ℝ)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hself : ∀ arm, preferenceGap arm arm = 0)
    (hcomplete : PreferenceComplete preferenceGap)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hepsilon : 0 < epsilon) (heta : 0 < eta) (hetaLeOne : eta ≤ 1) :
    freshPickAnchorJointFailureProbability sampleLaw
      (fun sample => canonicalFreshPickAnchorOutcomeLaw sample hcount preferenceGap hprobability
        epsilon eta)
      (fun sample => canonicalFreshPickAnchorObservation sample epsilon eta)
      preferenceGap epsilon eta hcount ≤ ((count - 1 : ℕ) : ℝ) * eta := by
  apply freshPickAnchorJoint_failure_probability_le_of_samplewise
    sampleLaw
    (fun sample => canonicalFreshPickAnchorOutcomeLaw sample hcount preferenceGap hprobability
      epsilon eta)
    (fun sample => canonicalFreshPickAnchorObservation sample epsilon eta)
    preferenceGap epsilon eta (((count - 1 : ℕ) : ℝ) * eta) hcount
  intro sample
  calc
    freshPickAnchorSampleFailureProbability sample hcount
        (canonicalFreshPickAnchorOutcomeLaw sample hcount preferenceGap hprobability epsilon eta)
        (canonicalFreshPickAnchorObservation sample epsilon eta)
        preferenceGap epsilon eta ≤
        ((pickAnchorSampleChallengers sample).length : ℝ) * eta :=
      canonicalFreshPickAnchorSample_failure_probability_le_callBudget sample hcount
        preferenceGap hprobability epsilon eta hantisymmetric hself hcomplete hsst
        hepsilon heta hetaLeOne
    _ = ((count - 1 : ℕ) : ℝ) * eta := by
      rw [pickAnchorSampleChallengers_length sample hcount]

/-- Under Algorithm 5's allocation, canonical fresh sampled-winner failure is at most `δ / 2`. -/
theorem canonicalFreshPickAnchorJoint_failure_probability_le_delta_half_of_sourceSchedule
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    {count : ℕ} (sampleLaw : PMF (finiteFreshList Arm count ∅)) (hcount : 0 < count)
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (delta epsilon : ℝ)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hself : ∀ arm, preferenceGap arm arm = 0)
    (hcomplete : PreferenceComplete preferenceGap)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) (hepsilon : 0 < epsilon) :
    freshPickAnchorJointFailureProbability sampleLaw
      (fun sample => canonicalFreshPickAnchorOutcomeLaw sample hcount preferenceGap hprobability
        epsilon ((delta / 2) / (count : ℝ)))
      (fun sample => canonicalFreshPickAnchorObservation sample epsilon ((delta / 2) / (count : ℝ)))
      preferenceGap epsilon ((delta / 2) / (count : ℝ)) hcount ≤ delta / 2 := by
  have hcountNat : 1 ≤ count := by omega
  have hcountReal : 0 < (count : ℝ) := by exact_mod_cast hcount
  have hcountOne : (1 : ℝ) ≤ (count : ℝ) := by exact_mod_cast hcountNat
  have heta : 0 < (delta / 2) / (count : ℝ) := by positivity
  have hetaLeOne : (delta / 2) / (count : ℝ) ≤ 1 := by
    rw [div_le_iff₀ hcountReal]
    nlinarith
  calc
    freshPickAnchorJointFailureProbability sampleLaw
        (fun sample => canonicalFreshPickAnchorOutcomeLaw sample hcount preferenceGap hprobability
          epsilon ((delta / 2) / (count : ℝ)))
        (fun sample => canonicalFreshPickAnchorObservation sample epsilon
          ((delta / 2) / (count : ℝ)))
        preferenceGap epsilon ((delta / 2) / (count : ℝ)) hcount ≤
        ((count - 1 : ℕ) : ℝ) * ((delta / 2) / (count : ℝ)) :=
      canonicalFreshPickAnchorJoint_failure_probability_le_callBudget sampleLaw hcount
        preferenceGap hprobability epsilon ((delta / 2) / (count : ℝ))
        hantisymmetric hself hcomplete hsst hepsilon heta hetaLeOne
    _ ≤ (count : ℝ) * ((delta / 2) / (count : ℝ)) := by
      apply mul_le_mul_of_nonneg_right
        (show ((count - 1 : ℕ) : ℝ) ≤ (count : ℝ) by exact_mod_cast Nat.sub_le count 1)
        (le_of_lt heta)
    _ = delta / 2 := by
      field_simp [ne_of_gt hcountReal]

/-- Lemma 3 under the source's concrete finite Bernoulli comparison model. -/
theorem canonicalFreshPickAnchorUniform_goodAnchor_highProbability_of_sourceSchedule
    {Arm : Type*} [Fintype Arm] [Nonempty Arm]
    (cutoff : ℕ) (delta epsilon : ℝ) (top : Finset Arm)
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (hcutoff : 0 < cutoff) (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1)
    (hepsilon : 0 < epsilon)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hself : ∀ arm, preferenceGap arm arm = 0)
    (hcomplete : PreferenceComplete preferenceGap)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (htopCard : top.card = cutoff)
    (htopRank : PickAnchorTopSetRankBound preferenceGap top cutoff) :
    1 - delta ≤ freshPickAnchorUniformGoodAnchorProbability
      cutoff delta epsilon
      (fun sample => canonicalFreshPickAnchorOutcomeLaw sample
        (pickAnchorSourceSampleCount_pos cutoff delta hcutoff hdelta hdeltaLeOne)
        preferenceGap hprobability epsilon
        ((delta / 2) /
          (pickAnchorSampleCount (Fintype.card Arm) cutoff delta : ℝ)))
      (fun sample => canonicalFreshPickAnchorObservation sample epsilon
        ((delta / 2) /
          (pickAnchorSampleCount (Fintype.card Arm) cutoff delta : ℝ)))
      preferenceGap hcutoff hdelta hdeltaLeOne := by
  classical
  change ∀ pivot ∈ top, (strictlyBetterArms preferenceGap pivot).card ≤ cutoff at htopRank
  let count : ℕ := pickAnchorSampleCount (Fintype.card Arm) cutoff delta
  let sampleLaw : PMF (finiteFreshList Arm count ∅) :=
    pickAnchorUniformSampleLaw count
      (pickAnchorSampleCount_le_armCount (Fintype.card Arm) cutoff delta)
  let hcount : 0 < count := pickAnchorSampleCount_pos (Fintype.card Arm) cutoff delta
    Fintype.card_pos hcutoff hdelta hdeltaLeOne
  change 1 - delta ≤ freshPickAnchorJointGoodAnchorProbability
    sampleLaw
    (fun sample => canonicalFreshPickAnchorOutcomeLaw sample hcount preferenceGap hprobability
      epsilon ((delta / 2) / (count : ℝ)))
    (fun sample => canonicalFreshPickAnchorObservation sample epsilon ((delta / 2) / (count : ℝ)))
    preferenceGap epsilon ((delta / 2) / (count : ℝ)) cutoff hcount
  apply pickAnchor_goodAnchor_pmf_probability_of_topSetHit_and_sampleWinner
    (freshPickAnchorJointLaw sampleLaw
      (fun sample => canonicalFreshPickAnchorOutcomeLaw sample hcount preferenceGap hprobability
        epsilon ((delta / 2) / (count : ℝ)))
      (fun sample => canonicalFreshPickAnchorObservation sample epsilon ((delta / 2) / (count : ℝ)))
      preferenceGap epsilon ((delta / 2) / (count : ℝ)) hcount)
    (fun sampleStateFailure => pickAnchorSampleSet sampleStateFailure.1)
    (fun sampleStateFailure => sampleStateFailure.2.1)
    top preferenceGap epsilon cutoff hantisymmetric hsst (le_of_lt hepsilon) htopRank delta
  · calc
      pmfProbClassical
          (freshPickAnchorJointLaw sampleLaw
            (fun sample => canonicalFreshPickAnchorOutcomeLaw sample hcount preferenceGap
              hprobability epsilon ((delta / 2) / (count : ℝ)))
            (fun sample => canonicalFreshPickAnchorObservation sample epsilon
              ((delta / 2) / (count : ℝ)))
            preferenceGap epsilon ((delta / 2) / (count : ℝ)) hcount)
          (fun sampleStateFailure => ¬ ∃ pivot, pivot ∈ top ∧
            pivot ∈ pickAnchorSampleSet sampleStateFailure.1) =
          pmfProbClassical sampleLaw
            (fun sample => ¬ ∃ pivot, pivot ∈ top ∧ pivot ∈ pickAnchorSampleSet sample) :=
        freshPickAnchorJoint_pmfProbClassical_fst_eq sampleLaw
          (fun sample => canonicalFreshPickAnchorOutcomeLaw sample hcount preferenceGap
            hprobability epsilon ((delta / 2) / (count : ℝ)))
          (fun sample => canonicalFreshPickAnchorObservation sample epsilon
            ((delta / 2) / (count : ℝ)))
          preferenceGap epsilon ((delta / 2) / (count : ℝ)) hcount
          (fun sample => ¬ ∃ pivot, pivot ∈ top ∧ pivot ∈ pickAnchorSampleSet sample)
      _ ≤ delta / 2 := by
        simpa only [sampleLaw, count] using
          (pickAnchor_miss_probability_le_delta_half cutoff delta top
            hcutoff htopCard hdelta hdeltaLeOne)
  · change freshPickAnchorJointFailureProbability sampleLaw
      (fun sample => canonicalFreshPickAnchorOutcomeLaw sample hcount preferenceGap hprobability
        epsilon ((delta / 2) / (count : ℝ)))
      (fun sample => canonicalFreshPickAnchorObservation sample epsilon ((delta / 2) / (count : ℝ)))
      preferenceGap epsilon ((delta / 2) / (count : ℝ)) hcount ≤ delta / 2
    apply canonicalFreshPickAnchorJoint_failure_probability_le_delta_half_of_sourceSchedule
      sampleLaw hcount preferenceGap hprobability delta epsilon hantisymmetric hself hcomplete hsst
      hdelta hdeltaLeOne hepsilon

end FalahatgarEtAl2017MaxingRanking
