import FalahatgarEtAl2017MaxingRanking.AdaptiveCompareProbability
import FalahatgarEtAl2017MaxingRanking.SequentialElimination

/-!
# Adaptive Compare inside Seq-Eliminate

This is the deterministic bridge from Appendix A.2's adaptive Compare
guarantees to the two realized-path inequalities used in Appendix A.3.  The
indeterminate interval `[0, epsilon]` is handled directly: either Compare
answer yields a valid Seq-Eliminate update there.
-/

namespace FalahatgarEtAl2017MaxingRanking

/-- Seq-Eliminate's incumbent update when each call uses adaptive Compare. -/
noncomputable def adaptiveCompareStep {Arm Ω : Type*}
    (observation : Arm → Arm → ℕ → Ω → ℝ) (count : ℕ)
    (epsilon delta : ℝ) (outcome : Ω) (incumbent challenger : Arm) : Arm :=
  match adaptiveCompare (observation challenger incumbent) count 0 epsilon delta outcome with
  | .lower => incumbent
  | .upper => challenger

/--
When every outer-hypothesis adaptive Compare call satisfies the corresponding
one-sided confidence conditions, all adaptive Seq-Eliminate updates satisfy
the path-validity inequalities.
-/
theorem adaptiveCompareStep_valid_of_confidence
    {Arm Ω : Type*}
    (observation : Arm → Arm → ℕ → Ω → ℝ) (count : ℕ)
    (preferenceGap : Arm → Arm → ℝ) (epsilon delta : ℝ) (outcome : Ω)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hself : ∀ arm, preferenceGap arm arm = 0)
    (hepsilon : 0 < epsilon)
    (hupperConfidence : ∀ incumbent challenger,
      preferenceGap challenger incumbent ≤ 0 →
        (∀ time, time ∈ Finset.Icc 1 count →
          adaptiveCenteredEstimate (observation challenger incumbent) time outcome -
            preferenceGap challenger incumbent < adaptiveConfidenceRadius time delta) ∧
        adaptiveCenteredEstimate (observation challenger incumbent) count outcome -
          preferenceGap challenger incumbent < epsilon / 2)
    (hlowerConfidence : ∀ incumbent challenger,
      epsilon ≤ preferenceGap challenger incumbent →
        (∀ time, time ∈ Finset.Icc 1 count →
          preferenceGap challenger incumbent -
            adaptiveCenteredEstimate (observation challenger incumbent) time outcome <
              adaptiveConfidenceRadius time delta) ∧
        preferenceGap challenger incumbent -
          adaptiveCenteredEstimate (observation challenger incumbent) count outcome < epsilon / 2) :
    SequentialEliminationStepValid preferenceGap epsilon
      (adaptiveCompareStep observation count epsilon delta outcome) := by
  intro incumbent challenger
  by_cases hsmall : preferenceGap challenger incumbent ≤ 0
  · have hconfidence := hupperConfidence incumbent challenger hsmall
    have hdecision := adaptiveCompare_lower_of_upperConfidence
      (observation challenger incumbent) count 0 epsilon
      (preferenceGap challenger incumbent) delta outcome hsmall hepsilon hconfidence.1
      (by simpa using hconfidence.2)
    simp only [adaptiveCompareStep, hdecision]
    constructor
    · rw [hself]
    · rw [hantisymmetric challenger incumbent]
      linarith
  · have hpositive : 0 ≤ preferenceGap challenger incumbent :=
      le_of_lt (lt_of_not_ge hsmall)
    by_cases hlarge : epsilon ≤ preferenceGap challenger incumbent
    · have hconfidence := hlowerConfidence incumbent challenger hlarge
      have hdecision := adaptiveCompare_upper_of_lowerConfidence
        (observation challenger incumbent) count 0 epsilon
        (preferenceGap challenger incumbent) delta outcome hlarge hepsilon hconfidence.1
        (by simpa using hconfidence.2)
      simp only [adaptiveCompareStep, hdecision]
      constructor
      · exact hpositive
      · rw [hself]
        linarith
    · have hmiddle : preferenceGap challenger incumbent ≤ epsilon := le_of_not_ge hlarge
      cases hdecision : adaptiveCompare (observation challenger incumbent) count 0 epsilon delta outcome with
      | lower =>
          simp only [adaptiveCompareStep, hdecision]
          constructor
          · rw [hself]
          · rw [hantisymmetric challenger incumbent]
            linarith
      | upper =>
          simp only [adaptiveCompareStep, hdecision]
          constructor
          · exact hpositive
          · rw [hself]
            linarith

/--
Theorem 2's deterministic adaptive form: the source's one-sided Compare
conditions at every call make Seq-Eliminate output an `epsilon`-maximum.
-/
theorem seqEliminate_correct_of_adaptiveCompareConfidence
    {Arm Ω : Type*}
    (observation : Arm → Arm → ℕ → Ω → ℝ) (count : ℕ)
    (preferenceGap : Arm → Arm → ℝ) (epsilon delta : ℝ) (outcome : Ω)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hself : ∀ arm, preferenceGap arm arm = 0)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hepsilon : 0 < epsilon)
    (hupperConfidence : ∀ incumbent challenger,
      preferenceGap challenger incumbent ≤ 0 →
        (∀ time, time ∈ Finset.Icc 1 count →
          adaptiveCenteredEstimate (observation challenger incumbent) time outcome -
            preferenceGap challenger incumbent < adaptiveConfidenceRadius time delta) ∧
        adaptiveCenteredEstimate (observation challenger incumbent) count outcome -
          preferenceGap challenger incumbent < epsilon / 2)
    (hlowerConfidence : ∀ incumbent challenger,
      epsilon ≤ preferenceGap challenger incumbent →
        (∀ time, time ∈ Finset.Icc 1 count →
          preferenceGap challenger incumbent -
            adaptiveCenteredEstimate (observation challenger incumbent) time outcome <
              adaptiveConfidenceRadius time delta) ∧
        preferenceGap challenger incumbent -
          adaptiveCenteredEstimate (observation challenger incumbent) count outcome < epsilon / 2)
    (maximum initial : Arm) (challengers : List Arm)
    (hmaximum : AbsoluteMaximum preferenceGap maximum)
    (happears : initial = maximum ∨ maximum ∈ challengers) :
    EpsilonMaximum preferenceGap epsilon
      (sequentialEliminate
        (adaptiveCompareStep observation count epsilon delta outcome)
        initial challengers) :=
  sequentialEliminate_epsilonMaximum_of_maximumAppears preferenceGap epsilon
    (adaptiveCompareStep observation count epsilon delta outcome)
    hantisymmetric hsst (le_of_lt hepsilon)
    (adaptiveCompareStep_valid_of_confidence observation count preferenceGap epsilon delta outcome
      hantisymmetric hself hepsilon hupperConfidence hlowerConfidence)
    maximum initial challengers hmaximum happears

end FalahatgarEtAl2017MaxingRanking
