import FalahatgarEtAl2017MaxingRanking.SequentialElimination
import FalahatgarEtAl2017MaxingRanking.FixedSampleCompare

/-!
# Fixed-sample Compare inside Seq-Eliminate

This bridge makes Appendix A.3 operational for the fixed-budget Compare rule:
the terminal concentration event implies both transition facts used in the
Seq-Eliminate correctness proof.
-/

namespace FalahatgarEtAl2017MaxingRanking

/-- Seq-Eliminate's next incumbent when each pair uses the fixed-sample Compare rule. -/
noncomputable def fixedSampleCompareStep {Arm Ω : Type*}
    (observation : Arm → Arm → ℕ → Ω → ℝ) (count : ℕ)
    (epsilon : ℝ) (outcome : Ω) (incumbent challenger : Arm) : Arm :=
  match fixedSampleCompare (observation challenger incumbent) count 0 epsilon outcome with
  | .lower => incumbent
  | .upper => challenger

/--
For every pair, fixed-sample concentration makes its induced Seq-Eliminate
transition valid.  This closes the deterministic bridge from Lemmas 11--12 to
the two displayed inequalities in Appendix A.3.
-/
theorem fixedSampleCompareStep_valid_of_concentrated {Arm Ω : Type*}
    (observation : Arm → Arm → ℕ → Ω → ℝ) (count : ℕ)
    (preferenceGap : Arm → Arm → ℝ) (epsilon : ℝ) (outcome : Ω)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hself : ∀ arm, preferenceGap arm arm = 0)
    (hepsilon : 0 ≤ epsilon)
    (hconcentrated : ∀ incumbent challenger,
      FixedSampleConcentrated (observation challenger incumbent) count
        (1 / 2 + preferenceGap challenger incumbent) (epsilon / 2) outcome) :
    SequentialEliminationStepValid preferenceGap epsilon
      (fixedSampleCompareStep observation count epsilon outcome) := by
  intro incumbent challenger
  cases hdecision : fixedSampleCompare (observation challenger incumbent) count 0 epsilon outcome with
  | lower =>
      simp only [fixedSampleCompareStep, hdecision]
      constructor
      · rw [hself]
      · by_contra hnot
        have hlarge : epsilon ≤ preferenceGap challenger incumbent := by
          rw [hantisymmetric challenger incumbent] at hnot
          linarith
        have hupper := fixedSampleCompare_upper_of_concentrated
          (observation challenger incumbent) count 0 epsilon
          (preferenceGap challenger incumbent) outcome hlarge
          (by simpa using hconcentrated incumbent challenger)
        rw [hdecision] at hupper
        cases hupper
  | upper =>
      simp only [fixedSampleCompareStep, hdecision]
      constructor
      · by_contra hnot
        have hsmall : preferenceGap challenger incumbent ≤ 0 := by linarith
        have hlower := fixedSampleCompare_lower_of_concentrated
          (observation challenger incumbent) count 0 epsilon
          (preferenceGap challenger incumbent) outcome hsmall
          (by simpa using hconcentrated incumbent challenger)
        rw [hdecision] at hlower
        cases hlower
      · rw [hself]
        linarith

/--
Theorem 2's Seq-Eliminate conclusion for the fixed-sample Compare execution:
simultaneous terminal concentration across its calls returns an `ε`-maximum.
-/
theorem seqEliminate_correct_of_fixedSampleConcentration {Arm Ω : Type*}
    (observation : Arm → Arm → ℕ → Ω → ℝ) (count : ℕ)
    (preferenceGap : Arm → Arm → ℝ) (epsilon : ℝ) (outcome : Ω)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    (hself : ∀ arm, preferenceGap arm arm = 0)
    (hsst : StrongStochasticTransitivity preferenceGap)
    (hepsilon : 0 ≤ epsilon)
    (hconcentrated : ∀ incumbent challenger,
      FixedSampleConcentrated (observation challenger incumbent) count
        (1 / 2 + preferenceGap challenger incumbent) (epsilon / 2) outcome)
    (maximum initial : Arm) (challengers : List Arm)
    (hmaximum : AbsoluteMaximum preferenceGap maximum)
    (happears : initial = maximum ∨ maximum ∈ challengers) :
    EpsilonMaximum preferenceGap epsilon
      (sequentialEliminate
        (fixedSampleCompareStep observation count epsilon outcome)
        initial challengers) :=
  sequentialEliminate_epsilonMaximum_of_maximumAppears preferenceGap epsilon
    (fixedSampleCompareStep observation count epsilon outcome) hantisymmetric hsst hepsilon
    (fixedSampleCompareStep_valid_of_concentrated observation count preferenceGap epsilon outcome
      hantisymmetric hself hepsilon hconcentrated)
    maximum initial challengers hmaximum happears

end FalahatgarEtAl2017MaxingRanking
