import FalahatgarEtAl2017MaxingRanking.CanonicalFreshPickAnchor

/-!
# Canonical random-order Seq-Eliminate

Algorithm 1 chooses the candidates in a uniformly random order and then makes
fresh comparison calls along that order.  The fixed-order concentration result
is proved elsewhere; this file supplies the exact paper-facing mixture over all
full without-replacement orders.
-/

namespace FalahatgarEtAl2017MaxingRanking

open AppliedModelingLib PreferenceRL
open MeasureTheory ProbabilityTheory

/-- The joint law of Algorithm 1's uniform full order and fresh-call execution. -/
noncomputable def canonicalFreshUniformSeqEliminateJointLaw
    {Arm : Type*} [Fintype Arm] [Nonempty Arm] [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (epsilon delta : ℝ) :
    PMF (finiteFreshList Arm (Fintype.card Arm) ∅ × (Arm × Bool)) := by
  classical
  exact freshPickAnchorJointLaw
    (pickAnchorUniformSampleLaw (Fintype.card Arm) (le_refl (Fintype.card Arm)))
    (fun sample => canonicalFreshPickAnchorOutcomeLaw sample Fintype.card_pos preferenceGap
      hprobability epsilon (delta / (Fintype.card Arm : ℝ)))
    (fun sample => canonicalFreshPickAnchorObservation sample epsilon
      (delta / (Fintype.card Arm : ℝ)))
    preferenceGap epsilon (delta / (Fintype.card Arm : ℝ)) Fintype.card_pos

/-- Algorithm 1's selected arm after forgetting the sampled full order. -/
noncomputable def canonicalFreshUniformSeqEliminateOutputLaw
    {Arm : Type*} [Fintype Arm] [Nonempty Arm] [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (epsilon delta : ℝ) : PMF Arm :=
  (canonicalFreshUniformSeqEliminateJointLaw preferenceGap hprobability epsilon delta).map
    (fun sampleStateFailure => sampleStateFailure.2.1)

/-- The probability that Algorithm 1 returns an `epsilon`-maximum. -/
noncomputable def canonicalFreshUniformSeqEliminateEpsilonMaximumProbability
    {Arm : Type*} [Fintype Arm] [Nonempty Arm] [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (epsilon delta : ℝ) : ℝ := by
  classical
  exact pmfProbClassical
    (canonicalFreshUniformSeqEliminateOutputLaw preferenceGap hprobability epsilon delta)
    (EpsilonMaximum preferenceGap epsilon)

/-- The complementary probability that Algorithm 1 does not return an `epsilon`-maximum. -/
noncomputable def canonicalFreshUniformSeqEliminateFailureProbability
    {Arm : Type*} [Fintype Arm] [Nonempty Arm] [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (epsilon delta : ℝ) : ℝ :=
  pmfProbClassical
    (canonicalFreshUniformSeqEliminateJointLaw preferenceGap hprobability epsilon delta)
    (fun sampleStateFailure =>
      ¬ EpsilonMaximum preferenceGap epsilon sampleStateFailure.2.1)

/-- Algorithm 1's semantic failure and success probabilities are complements. -/
theorem canonicalFreshUniformSeqEliminate_failureProbability_eq_one_sub_successProbability
    {Arm : Type*} [Fintype Arm] [Nonempty Arm] [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (epsilon delta : ℝ) :
    canonicalFreshUniformSeqEliminateFailureProbability preferenceGap hprobability
        epsilon delta =
      1 - canonicalFreshUniformSeqEliminateEpsilonMaximumProbability
        preferenceGap hprobability epsilon delta := by
  unfold canonicalFreshUniformSeqEliminateFailureProbability
  rw [pmfProbClassical_compl]
  unfold canonicalFreshUniformSeqEliminateEpsilonMaximumProbability
  unfold canonicalFreshUniformSeqEliminateOutputLaw
  rw [pmfProbClassical_map]

/--
The exact random-order Algorithm 1 succeeds with probability at least
`1 - delta`; mixing over the random order costs nothing because the existing
fresh-call theorem holds for every realized order.
-/
theorem canonicalFreshUniformSeqEliminate_epsilonMaximum_probability_of_sourceSchedule
    {Arm : Type*} [Fintype Arm] [Nonempty Arm] [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (epsilon delta : ℝ)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hself : ∀ arm, preferenceGap arm arm = 0)
    (hcomplete : PreferenceComplete preferenceGap)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hepsilon : 0 < epsilon) (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    1 - delta ≤ canonicalFreshUniformSeqEliminateEpsilonMaximumProbability
      preferenceGap hprobability epsilon delta := by
  classical
  let count := Fintype.card Arm
  let hcount : 0 < count := Fintype.card_pos
  let sampleLaw : PMF (finiteFreshList Arm count ∅) :=
    pickAnchorUniformSampleLaw count (le_refl count)
  let outcomeLaw := fun sample =>
    canonicalFreshPickAnchorOutcomeLaw sample hcount preferenceGap hprobability
      epsilon (delta / (count : ℝ))
  let observation := fun (sample : finiteFreshList Arm count ∅) =>
    canonicalFreshPickAnchorObservation sample epsilon (delta / (count : ℝ))
  have hcountReal : 0 < (count : ℝ) := by exact_mod_cast hcount
  have heta : 0 < delta / (count : ℝ) := div_pos hdelta hcountReal
  have hetaLeOne : delta / (count : ℝ) ≤ 1 := by
    apply (div_le_iff₀ hcountReal).mpr
    have hcountOne : (1 : ℝ) ≤ count := by exact_mod_cast hcount
    nlinarith
  have hsampleFailure :
      freshPickAnchorJointFailureProbability sampleLaw outcomeLaw observation
        preferenceGap epsilon (delta / (count : ℝ)) hcount ≤ delta := by
    calc
      freshPickAnchorJointFailureProbability sampleLaw outcomeLaw observation
          preferenceGap epsilon (delta / (count : ℝ)) hcount ≤
          ((count - 1 : ℕ) : ℝ) * (delta / (count : ℝ)) := by
        apply canonicalFreshPickAnchorJoint_failure_probability_le_callBudget
          sampleLaw hcount preferenceGap hprobability epsilon (delta / (count : ℝ))
          hantisymmetric hself hcomplete hsst hepsilon heta hetaLeOne
      _ ≤ (count : ℝ) * (delta / (count : ℝ)) := by
        apply mul_le_mul_of_nonneg_right
          (show ((count - 1 : ℕ) : ℝ) ≤ (count : ℝ) by
            exact_mod_cast Nat.sub_le count 1)
          (le_of_lt heta)
      _ = delta := by
        rw [← mul_div_assoc]
        exact mul_div_cancel_left₀ delta (ne_of_gt hcountReal)
  rw [freshPickAnchorJointFailureProbability_eq_pmfProbClassical] at hsampleFailure
  have hfailure :
      canonicalFreshUniformSeqEliminateFailureProbability preferenceGap hprobability
        epsilon delta ≤ delta := by
    calc
      canonicalFreshUniformSeqEliminateFailureProbability preferenceGap hprobability
          epsilon delta =
          pmfProbClassical
            (freshPickAnchorJointLaw sampleLaw outcomeLaw observation preferenceGap
              epsilon (delta / (count : ℝ)) hcount)
            (fun sampleStateFailure =>
              ¬ ∀ arm ∈ pickAnchorSampleSet sampleStateFailure.1,
                -epsilon ≤ preferenceGap sampleStateFailure.2.1 arm) := by
        unfold canonicalFreshUniformSeqEliminateFailureProbability
        apply pmfProbClassical_congr
        intro sampleStateFailure
        rw [pickAnchorSampleSet_eq_univ_of_card_eq sampleStateFailure.1 rfl]
        simp only [Finset.mem_univ, forall_const, EpsilonMaximum,
          ApproximatePreferenceWinner]
      _ ≤ delta := hsampleFailure
  rw [canonicalFreshUniformSeqEliminate_failureProbability_eq_one_sub_successProbability]
    at hfailure
  linarith

end FalahatgarEtAl2017MaxingRanking
