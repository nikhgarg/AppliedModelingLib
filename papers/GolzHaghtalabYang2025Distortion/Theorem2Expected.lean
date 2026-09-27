import AppliedModelingLib.Foundations.Probability.Conditional
import GolzHaghtalabYang2025Distortion.Theorem2Quantitative

/-!
# Expected finite-sample Borda welfare for source Theorem 2

Appendix E.1 converts its simultaneous Borda concentration statement into an
expected-welfare bound.  This module makes that conversion explicit for every
deterministic empirical-Borda tie breaker.  It keeps the failure probability
as a parameter, rather than treating the source's informal `O(·)` notation as
a formal asymptotic statement.
-/

namespace GolzHaghtalabYang2025Distortion

open AppliedModelingLib
open AppliedModelingLib.Alignment.Welfare
open AppliedModelingLib.Learning.HumanFeedback
open AppliedModelingLib.Probability

/-- The explicit simultaneous normalized-Borda envelope from Appendix D. -/
noncomputable def theorem2SourceRate
    (alternativeCount users comparisonsPerUser : ℕ) (minimumMass delta : ℝ) : ℝ :=
  let logLevel := Real.log (8 * (alternativeCount : ℝ) ^ 2 / delta)
  20 * Real.sqrt ((users : ℝ) * logLevel /
    min 1 ((comparisonsPerUser : ℝ) * minimumMass ^ 2)) / (users : ℝ) +
    8 * ((alternativeCount : ℝ) + 1) * logLevel /
      ((users : ℝ) * minimumMass)

/--
A nonnegative finite random variable that is at least `lower` on a good event
has expectation at least `(1 - delta) * lower` whenever the complementary
event has probability at most `delta`.  The possibly-negative `lower` case is
included so source welfare bounds can be used without an artificial sample-size
condition making their displayed remainder positive.
-/
theorem pmfExp_ge_one_sub_prob_mul_of_nonneg_on_good
    {Sample : Type*} [Fintype Sample] [DecidableEq Sample]
    (law : PMF Sample) (good : Sample → Prop) [DecidablePred good] (value : Sample → ℝ)
    (lower delta : ℝ)
    (hvalue_nonneg : ∀ sample, 0 ≤ value sample)
    (hgood : ∀ sample, good sample → lower ≤ value sample)
    (hbad : pmfProb law (fun sample => ¬ good sample) ≤ delta)
    (hdelta_le_one : delta ≤ 1) :
    (1 - delta) * lower ≤ pmfExp law value := by
  classical
  by_cases hlower_nonneg : 0 ≤ lower
  · have hgood_prob : 1 - delta ≤ pmfProb law good := by
      have hbad_compl : pmfProb law (fun sample => ¬ good sample) =
          1 - pmfProb law good := pmfProb_compl law good
      linarith
    have hpoint : ∀ sample,
        (if good sample then lower else 0) ≤ value sample := by
      intro sample
      by_cases hsample : good sample
      · simpa [hsample] using hgood sample hsample
      · simpa [hsample] using hvalue_nonneg sample
    have hexpectation :
        pmfExp law (fun sample => if good sample then lower else 0) ≤ pmfExp law value :=
      pmfExp_le_pmfExp_of_forall_le law _ _ hpoint
    calc
      (1 - delta) * lower ≤ pmfProb law good * lower :=
        mul_le_mul_of_nonneg_right hgood_prob hlower_nonneg
      _ = pmfIndicatorExp law good (fun _ => lower) := by
        symm
        exact pmfIndicatorExp_const law good lower
      _ = pmfExp law (fun sample => if good sample then lower else 0) := rfl
      _ ≤ pmfExp law value := hexpectation
  · have hlower_nonpos : lower ≤ 0 := le_of_not_ge hlower_nonneg
    have hone_sub_nonneg : 0 ≤ 1 - delta := sub_nonneg.mpr hdelta_le_one
    calc
      (1 - delta) * lower ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hone_sub_nonneg hlower_nonpos
      _ ≤ pmfExp law value := pmfExp_nonneg_of_forall_nonneg law value hvalue_nonneg

/--
Explicit expected-welfare form of the source Theorem 2 finite-sample route.
For any deterministic tie breaker that chooses an empirical normalized-Borda
maximizer for every literal response-table/label sample, the expected welfare
is at least the good-event squared-welfare lower bound times `1 - δ`.
-/
theorem theorem2_iidUserBatch_expectedWelfare_ge_sourceRate
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
        Real.exp (-((users * comparisonsPerUser : ℕ) : ℝ) * minimumMass / 8) ≤ delta)
    (winner : (Fin users →
      (theorem2UserResponseTable Alternative ×
        (Fin comparisonsPerUser → Alternative × Alternative))) → Alternative)
    (hwinner : ∀ sample alternative,
      theorem11IidUserLatentBordaScore alternative sample ≤
        theorem11IidUserLatentBordaScore (winner sample) sample)
    (benchmark : Alternative) :
    (1 - delta) *
      ((sigmoidChordSlope btScale / ((1 : ℝ) / 4)) ^ 2 *
          populationAverageUtility population utility benchmark -
        2 * theorem2SourceRate (Fintype.card Alternative) users comparisonsPerUser
          minimumMass delta / (btScale * ((1 : ℝ) / 4))) ≤
      pmfExp
        (pmfProduct (Fin users)
          (theorem2UserResponseTable Alternative ×
            (Fin comparisonsPerUser → Alternative × Alternative))
          (pmfProd responseLaw
            (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
              (theorem2UserPairLabelLaw sampling))))
        (fun sample => populationAverageUtility population utility (winner sample)) := by
  classical
  let law := pmfProduct (Fin users)
    (theorem2UserResponseTable Alternative ×
      (Fin comparisonsPerUser → Alternative × Alternative))
    (pmfProd responseLaw
      (pmfProduct (Fin comparisonsPerUser) (Alternative × Alternative)
        (theorem2UserPairLabelLaw sampling)))
  let scoreError := theorem2SourceRate (Fintype.card Alternative) users comparisonsPerUser
    minimumMass delta
  let bad : (Fin users →
      (theorem2UserResponseTable Alternative ×
        (Fin comparisonsPerUser → Alternative × Alternative))) → Prop :=
    fun sample => ∃ badWinner : Alternative,
      (∀ alternative,
        theorem11IidUserLatentBordaScore alternative sample ≤
          theorem11IidUserLatentBordaScore badWinner sample) ∧
      ∃ alternative,
        ((1 : ℝ) / 4) ^ 2 * populationAverageUtility population utility badWinner +
            ((1 : ℝ) / 4) * (2 * scoreError) / btScale <
          (sigmoidChordSlope btScale) ^ 2 *
            populationAverageUtility population utility alternative
  have hbad : pmfProb law bad ≤ delta := by
    simpa [law, bad, scoreError, theorem2SourceRate] using
      (theorem2_iidUserBatch_empiricalBorda_welfare_failure_le_sourceRate
        population utility hutility sampling hbtScale responseLaw hcalibrated
        users comparisonsPerUser husers hcomparisons minimumMass delta hminimumMass_pos
        hminimumMass hdelta_pos hdelta_le_one hsource_condition)
  have hvalue_nonneg : ∀ sample,
      0 ≤ populationAverageUtility population utility (winner sample) := by
    intro sample
    exact populationAverageUtility_nonneg population utility hutility (winner sample)
  have hgood : ∀ sample, ¬ bad sample →
      (sigmoidChordSlope btScale / ((1 : ℝ) / 4)) ^ 2 *
          populationAverageUtility population utility benchmark -
        2 * scoreError / (btScale * ((1 : ℝ) / 4)) ≤
          populationAverageUtility population utility (winner sample) := by
    intro sample hsample
    have hsource :
        (sigmoidChordSlope btScale) ^ 2 *
            populationAverageUtility population utility benchmark ≤
          ((1 : ℝ) / 4) ^ 2 *
              populationAverageUtility population utility (winner sample) +
            ((1 : ℝ) / 4) * (2 * scoreError) / btScale := by
      exact le_of_not_gt fun hlt => hsample ⟨winner sample, hwinner sample, benchmark, hlt⟩
    have hquarter_pos : (0 : ℝ) < (1 : ℝ) / 4 := by norm_num
    have hquarter_sq_pos : 0 < ((1 : ℝ) / 4) ^ 2 := sq_pos_of_pos hquarter_pos
    have hrewrite :
        (sigmoidChordSlope btScale / ((1 : ℝ) / 4)) ^ 2 *
            populationAverageUtility population utility benchmark -
          2 * scoreError / (btScale * ((1 : ℝ) / 4)) =
          ((sigmoidChordSlope btScale) ^ 2 *
              populationAverageUtility population utility benchmark -
            ((1 : ℝ) / 4) * (2 * scoreError) / btScale) /
            ((1 : ℝ) / 4) ^ 2 := by
      field_simp [ne_of_gt hbtScale, ne_of_gt hquarter_pos]
    rw [hrewrite]
    apply (div_le_iff₀ hquarter_sq_pos).2
    nlinarith
  change (1 - delta) *
      ((sigmoidChordSlope btScale / ((1 : ℝ) / 4)) ^ 2 *
          populationAverageUtility population utility benchmark -
        2 * scoreError / (btScale * ((1 : ℝ) / 4))) ≤
      pmfExp law (fun sample => populationAverageUtility population utility (winner sample))
  exact pmfExp_ge_one_sub_prob_mul_of_nonneg_on_good law (fun sample => ¬ bad sample)
    (fun sample => populationAverageUtility population utility (winner sample))
    _ delta hvalue_nonneg hgood (by simpa using hbad) hdelta_le_one

end GolzHaghtalabYang2025Distortion
