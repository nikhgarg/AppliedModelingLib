import KR21Monoculture.W11ScoreTransport
import AppliedModelingLib.Foundations.Probability.MeasureInequalities

open AppliedModelingLib MeasureTheory ProbabilityTheory
open AppliedModelingLib.SocialChoice.Ranking

namespace KR21Monoculture

/-!
# Appendix A source event formula

The displayed A.1 conditional-tail expression first rewrites the event that
the true top candidate is selected.  This module proves that rewrite at the
literal source-score surface.  It intentionally does not claim a Fubini or
regular-conditional-expectation identity that has not been constructed.
-/

/-- The A.1 event that candidate `c` is first under the source scores
`value i + noise i / theta`. -/
def SourceAppendixATopEvent {n : ℕ}
    (value noise : Candidate n -> ℝ) (theta : ℝ) (c : Candidate n) : Prop :=
  firstChoice (rankByScore (fun i => value i + noise i / theta)) = c

/-- The finite universal form of A.1's noise-tail event
`epsilon_c > max_{d ne c} theta * (x_d - x_c) + epsilon_d`.
The universal form avoids silently choosing a maximizer or assuming a
nonempty competitor set. -/
def SourceAppendixATailEvent {n : ℕ}
    (value noise : Candidate n -> ℝ) (theta : ℝ) (c : Candidate n) : Prop :=
  ∀ d : Candidate n, d ≠ c →
    theta * (value d - value c) + noise d < noise c

/-- At positive accuracy, each source score comparison is exactly its A.1
threshold comparison after clearing the positive denominator. -/
theorem source_appendixA_score_lt_iff_tail_threshold
    {n : ℕ} (value noise : Candidate n -> ℝ) {theta : ℝ} (htheta : 0 < theta)
    (c d : Candidate n) :
    value d + noise d / theta < value c + noise c / theta <->
      theta * (value d - value c) + noise d < noise c := by
  constructor <;> intro h
  · have hmul := mul_lt_mul_of_pos_right h htheta
    field_simp [ne_of_gt htheta] at hmul
    linarith
  · have hmul :
        (value d + noise d / theta) * theta <
          (value c + noise c / theta) * theta := by
      field_simp [ne_of_gt htheta]
      linarith
    exact lt_of_mul_lt_mul_right hmul (le_of_lt htheta)

/-- With no score ties, the source's selected-top event is equivalent to the
literal A.1 finite noise-tail event.  The no-tie premise is necessary because
the library deliberately fixes a deterministic tie-breaking rule whereas the
source uses strict inequalities. -/
theorem source_appendixA_top_event_iff_tail_event_of_no_ties
    {n : ℕ} (value noise : Candidate n -> ℝ) {theta : ℝ} (htheta : 0 < theta)
    (c : Candidate n)
    (hnoTie : ∀ i j : Candidate n, i ≠ j →
      value i + noise i / theta ≠ value j + noise j / theta) :
    SourceAppendixATopEvent value noise theta c <->
      SourceAppendixATailEvent value noise theta c := by
  constructor
  · intro htop d hdc
    have hscore :
        value d + noise d / theta < value c + noise c / theta := by
      let score : Candidate n -> ℝ := fun i => value i + noise i / theta
      change firstChoice (rankByScore score) = c at htop
      have hrank :
          rankOf (rankByScore score) c <= rankOf (rankByScore score) d := by
        calc
          rankOf (rankByScore score) c =
              rankOf (rankByScore score) (firstChoice (rankByScore score)) := by
                rw [htop]
          _ = 0 := rankOf_firstChoice (rankByScore score)
          _ <= rankOf (rankByScore score) d := bot_le
      have hle : score d <= score c :=
        rankByScore_weaklyOrdersScores score hrank
      exact lt_of_le_of_ne hle (hnoTie d c hdc)
    exact (source_appendixA_score_lt_iff_tail_threshold
      value noise htheta c d).mp hscore
  · intro htail
    apply (show firstChoice (rankByScore (fun i => value i + noise i / theta)) = c from ?_)
    rw [<- bestInSet_univ]
    apply bestInSet_rankByScore_univ_eq_of_strict_top
    intro d hdc
    exact (source_appendixA_score_lt_iff_tail_threshold
      value noise htheta c d).mpr (htail d hdc)

/-- The A.1 event rewrite transports to the actual source-noise probability
whenever score ties are null.  This is the probability-level part of the
displayed calculation; the further conditional-expectation/Fubini factorization
is intentionally a separate obligation. -/
theorem source_appendixA_top_event_probability_eq_tail_probability
    {n : ℕ} (μ : Measure (Candidate n -> ℝ))
    (value : Candidate n -> ℝ) {theta : ℝ} (htheta : 0 < theta)
    (c : Candidate n)
    (hnoTie : ∀ᵐ noise ∂μ, ∀ i j : Candidate n, i ≠ j →
      value i + noise i / theta ≠ value j + noise j / theta) :
    AppliedModelingLib.measureProb μ
        (fun noise => SourceAppendixATopEvent value noise theta c) =
      AppliedModelingLib.measureProb μ
        (fun noise => SourceAppendixATailEvent value noise theta c) := by
  unfold AppliedModelingLib.measureProb
  apply congrArg ENNReal.toReal
  apply measure_congr
  filter_upwards [hnoTie] with noise hnoise
  exact propext (source_appendixA_top_event_iff_tail_event_of_no_ties
    value noise htheta c hnoise)

end KR21Monoculture
