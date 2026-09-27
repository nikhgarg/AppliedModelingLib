import GolzHaghtalabYang2025Distortion.Lemma11FiniteSample
import GolzHaghtalabYang2025Distortion.Theorem2FiniteSample

/-!
# Finite concentration-to-welfare bridge for source Theorem 2

This file composes Appendix D's literal iid-user Borda concentration with the
deterministic welfare implication in `Theorem2FiniteSample`.  It preserves
the source response-table model: only user reports are iid, while all answers
inside one user's table may be correlated.
-/

namespace GolzHaghtalabYang2025Distortion

open AppliedModelingLib
open AppliedModelingLib.Alignment.Welfare
open AppliedModelingLib.Learning.HumanFeedback
open AppliedModelingLib.Probability

/--
Finite literal-user Theorem 2 endpoint.  Outside the uniform Borda-tail
event, every maximizer of the empirical normalized Borda score satisfies the
source squared-welfare inequality with the explicit finite error
`4 * cutoff / (n * d * minimumMass)`.  The tail is the checked range-based
Lemma 11 bound; it is not identified with the source's sharper big-O rate.
-/
theorem theorem2_iidUserBatch_empiricalBorda_welfare_failure_le_uniform_tail
    {User Alternative : Type*} [Fintype User] [DecidableEq User]
    [Fintype Alternative] [DecidableEq Alternative]
    (population : PMF User) (utility : FiniteUtilityProfile User Alternative)
    (hutility : UnitIntervalUtilityProfile utility)
    (sampling : PMF Alternative) {btScale : ℝ} (hbtScale : 0 < btScale)
    (responseLaw : PMF (theorem2UserResponseTable Alternative))
    (hcalibrated : theorem2UserResponseCalibrated responseLaw
      (populationBradleyTerryPreference population utility btScale))
    (users comparisonsPerUser : ℕ) (husers : 0 < users) (hcomparisons : 0 < comparisonsPerUser)
    (minimumMass cutoff : ℝ) (hminimumMass_pos : 0 < minimumMass)
    (hminimumMass : ∀ alternative, minimumMass ≤ (sampling alternative).toReal)
    (hcutoff_nonneg : 0 ≤ cutoff)
    (hcutoff_small : cutoff ≤
      (users : ℝ) * (comparisonsPerUser : ℝ) * minimumMass) :
    pmfProb (theorem12IidBordaReportBatchLaw
      (theorem2UserBatchLaw responseLaw sampling comparisonsPerUser) users)
      (fun sample => ∃ winner : Alternative,
        (∀ alternative,
          theorem12EmpiricalBordaScore theorem2UserBatchBordaWins theorem2UserBatchBordaIncidences
            alternative sample ≤
          theorem12EmpiricalBordaScore theorem2UserBatchBordaWins theorem2UserBatchBordaIncidences
            winner sample) ∧
        ∃ alternative,
          ((1 : ℝ) / 4) ^ 2 * populationAverageUtility population utility winner +
              ((1 : ℝ) / 4) *
                (2 * (2 * cutoff /
                  ((users : ℝ) * (comparisonsPerUser : ℝ) * minimumMass))) / btScale <
            (sigmoidChordSlope btScale) ^ 2 *
              populationAverageUtility population utility alternative) ≤
      ∑ _alternative : Alternative,
        4 * Real.exp (-cutoff ^ 2 /
          (4 * ((users : ℝ) * (2 * comparisonsPerUser : ℝ) ^ 2 +
            (2 * comparisonsPerUser : ℝ) * cutoff))) := by
  classical
  let law := theorem12IidBordaReportBatchLaw
    (theorem2UserBatchLaw responseLaw sampling comparisonsPerUser) users
  let scoreError : ℝ :=
    2 * cutoff / ((users : ℝ) * (comparisonsPerUser : ℝ) * minimumMass)
  let welfareFailure :
      (Fin users → theorem2UserBatchReport Alternative comparisonsPerUser) → Prop :=
    fun sample => ∃ winner : Alternative,
      (∀ alternative,
        theorem12EmpiricalBordaScore theorem2UserBatchBordaWins theorem2UserBatchBordaIncidences
          alternative sample ≤
        theorem12EmpiricalBordaScore theorem2UserBatchBordaWins theorem2UserBatchBordaIncidences
          winner sample) ∧
      ∃ alternative,
        ((1 : ℝ) / 4) ^ 2 * populationAverageUtility population utility winner +
            ((1 : ℝ) / 4) * (2 * scoreError) / btScale <
          (sigmoidChordSlope btScale) ^ 2 *
            populationAverageUtility population utility alternative
  let scoreTail :
      (Fin users → theorem2UserBatchReport Alternative comparisonsPerUser) → Prop :=
    fun sample => ∃ alternative,
      scoreError <
        |theorem12EmpiricalBordaScore theorem2UserBatchBordaWins theorem2UserBatchBordaIncidences
            alternative sample -
          pairwiseBordaScore sampling
            (populationBradleyTerryPreference population utility btScale) alternative|
  have htail := theorem11_iidBordaScore_uniform_minMass_tail_bound responseLaw sampling
    (populationBradleyTerryPreference population utility btScale) users comparisonsPerUser
    husers hcomparisons hcalibrated minimumMass cutoff hminimumMass_pos hminimumMass
    hcutoff_nonneg hcutoff_small
  change pmfProb law welfareFailure ≤ _
  refine (pmfProb_le_of_imp law welfareFailure scoreTail ?_).trans ?_
  · rintro sample ⟨winner, hmax, alternative, hfailure⟩
    by_contra hnoTail
    have hnoTail' : ¬ ∃ candidate,
        scoreError <
          |theorem12EmpiricalBordaScore theorem2UserBatchBordaWins theorem2UserBatchBordaIncidences
              candidate sample -
            pairwiseBordaScore sampling
              (populationBradleyTerryPreference population utility btScale) candidate| := by
      simpa [scoreTail] using hnoTail
    have happrox : ∀ candidate,
        |theorem12EmpiricalBordaScore theorem2UserBatchBordaWins theorem2UserBatchBordaIncidences
            candidate sample -
          pairwiseBordaScore sampling
            (populationBradleyTerryPreference population utility btScale) candidate| ≤ scoreError := by
      intro candidate
      exact le_of_not_gt fun hbad => hnoTail' ⟨candidate, hbad⟩
    have hwelfare := theorem2_welfare_square_bound_of_uniform_empirical_borda_error
      population utility hutility sampling hbtScale
      (fun candidate => theorem12EmpiricalBordaScore theorem2UserBatchBordaWins
        theorem2UserBatchBordaIncidences candidate sample)
      winner scoreError hmax happrox alternative
    exact (not_lt_of_ge hwelfare) hfailure
  · simpa [law, scoreTail, scoreError] using htail

/--
Finite literal-user source-rate endpoint for Theorem 2.  With the Appendix-D
minimum-mass condition, the normalized empirical Borda scores are uniformly
within the explicit source-rate envelope (with `log (8 m² / δ)`) except on an
event of probability at most `δ`.  Every empirical maximizer then obeys the
source squared-welfare inequality with its corresponding additive welfare
term.  As throughout the paper's finite-report model, reports are iid across
users but may be correlated within a user's response table.
-/
theorem theorem2_iidUserBatch_empiricalBorda_welfare_failure_le_sourceRate
    {User Alternative : Type*} [Fintype User] [DecidableEq User]
    [Fintype Alternative] [DecidableEq Alternative] [Nonempty Alternative]
    (population : PMF User) (utility : FiniteUtilityProfile User Alternative)
    (hutility : UnitIntervalUtilityProfile utility)
    (sampling : PMF Alternative) {btScale : ℝ} (hbtScale : 0 < btScale)
    (responseLaw : PMF (theorem2UserResponseTable Alternative))
    (hcalibrated : theorem2UserResponseCalibrated responseLaw
      (populationBradleyTerryPreference population utility btScale))
    (users comparisonsPerUser : ℕ) (husers : 0 < users) (hcomparisons : 0 < comparisonsPerUser)
    (minimumMass delta : ℝ) (hminimumMass_pos : 0 < minimumMass)
    (hminimumMass : ∀ alternative, minimumMass ≤ (sampling alternative).toReal)
    (hdelta_pos : 0 < delta) (hdelta_le_one : delta ≤ 1)
    (hsource_condition :
      2 * (Fintype.card Alternative : ℝ) *
        Real.exp (-((users * comparisonsPerUser : ℕ) : ℝ) * minimumMass / 8) ≤ delta) :
    pmfProb
      (pmfProduct (Fin users)
        (theorem2UserResponseTable Alternative ×
          (Fin comparisonsPerUser → Alternative × Alternative))
        (pmfProd responseLaw
          (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
            (theorem2UserPairLabelLaw sampling))))
      (fun sample =>
        let logLevel := Real.log (8 * (Fintype.card Alternative : ℝ) ^ 2 / delta)
        let scoreError :=
          20 * Real.sqrt ((users : ℝ) * logLevel /
            min 1 ((comparisonsPerUser : ℝ) * minimumMass ^ 2)) / (users : ℝ) +
            8 * ((Fintype.card Alternative : ℝ) + 1) * logLevel /
              ((users : ℝ) * minimumMass)
        ∃ winner : Alternative,
          (∀ alternative,
            theorem11IidUserLatentBordaScore alternative sample ≤
            theorem11IidUserLatentBordaScore winner sample) ∧
          ∃ alternative,
            ((1 : ℝ) / 4) ^ 2 * populationAverageUtility population utility winner +
                ((1 : ℝ) / 4) * (2 * scoreError) / btScale <
              (sigmoidChordSlope btScale) ^ 2 *
                populationAverageUtility population utility alternative) ≤ delta := by
  classical
  let logLevel : ℝ := Real.log (8 * (Fintype.card Alternative : ℝ) ^ 2 / delta)
  let scoreError : ℝ :=
    20 * Real.sqrt ((users : ℝ) * logLevel /
      min 1 ((comparisonsPerUser : ℝ) * minimumMass ^ 2)) / (users : ℝ) +
      8 * ((Fintype.card Alternative : ℝ) + 1) * logLevel /
        ((users : ℝ) * minimumMass)
  let law := pmfProduct (Fin users)
    (theorem2UserResponseTable Alternative ×
      (Fin comparisonsPerUser → Alternative × Alternative))
    (pmfProd responseLaw
      (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
        (theorem2UserPairLabelLaw sampling)))
  let welfareFailure :
      (Fin users →
        (theorem2UserResponseTable Alternative ×
          (Fin comparisonsPerUser → Alternative × Alternative))) → Prop :=
    fun sample => ∃ winner : Alternative,
      (∀ alternative,
        theorem11IidUserLatentBordaScore alternative sample ≤
        theorem11IidUserLatentBordaScore winner sample) ∧
      ∃ alternative,
        ((1 : ℝ) / 4) ^ 2 * populationAverageUtility population utility winner +
            ((1 : ℝ) / 4) * (2 * scoreError) / btScale <
          (sigmoidChordSlope btScale) ^ 2 *
            populationAverageUtility population utility alternative
  let scoreTail :
      (Fin users →
        (theorem2UserResponseTable Alternative ×
          (Fin comparisonsPerUser → Alternative × Alternative))) → Prop :=
    fun sample => ∃ alternative,
      scoreError <
        |theorem11IidUserLatentBordaScore alternative sample -
          pairwiseBordaScore sampling
            (populationBradleyTerryPreference population utility btScale) alternative|
  have htail := theorem11_iidUserLatentBordaScore_minMass_sourceRate_uniform_confidence
    responseLaw sampling (populationBradleyTerryPreference population utility btScale)
    users comparisonsPerUser husers hcomparisons hcalibrated minimumMass delta
    hminimumMass_pos hminimumMass hdelta_pos hdelta_le_one hsource_condition
  change pmfProb law welfareFailure ≤ delta
  refine (pmfProb_le_of_imp law welfareFailure scoreTail ?_).trans ?_
  · rintro sample ⟨winner, hmax, alternative, hfailure⟩
    by_contra hnoTail
    have hnoTail' : ¬ ∃ candidate,
        scoreError <
          |theorem11IidUserLatentBordaScore candidate sample -
            pairwiseBordaScore sampling
              (populationBradleyTerryPreference population utility btScale) candidate| := by
      simpa [scoreTail] using hnoTail
    have happrox : ∀ candidate,
        |theorem11IidUserLatentBordaScore candidate sample -
          pairwiseBordaScore sampling
            (populationBradleyTerryPreference population utility btScale) candidate| ≤ scoreError := by
      intro candidate
      exact le_of_not_gt fun hbad => hnoTail' ⟨candidate, hbad⟩
    have hwelfare := theorem2_welfare_square_bound_of_uniform_empirical_borda_error
      population utility hutility sampling hbtScale
      (fun candidate => theorem11IidUserLatentBordaScore candidate sample)
      winner scoreError hmax happrox alternative
    exact (not_lt_of_ge hwelfare) hfailure
  · simpa [law, scoreTail, scoreError, logLevel] using htail

end GolzHaghtalabYang2025Distortion
