import KR21Monoculture.AppendixB

open AppliedModelingLib
open AppliedModelingLib.SocialChoice.Ranking

namespace KR21Monoculture

/-!
# Appendix B.2 source probability formulas

The source's B.1 and B.2 labels are the two first-choice comparisons in the
Definition-3 counterexample.  These endpoints state those probabilities
directly at the concrete iid source-score law, rather than only exposing the
ranking-table pushforward used by the calculation.
-/

/-- The source B.2 algorithmic iid score experiment has the displayed
probability of choosing `x₁` first. -/
theorem source_appendixB2_algorithm_x1_first_probability :
    firstChoiceProb appendixB2AlgorithmRankingPMF (0 : Candidate 1) =
      67 / 100 :=
  appendixB2_algorithm_firstChoice_x1_eq

/-- The source B.2 human iid score experiment has the displayed probability
of choosing `x₁` first. -/
theorem source_appendixB2_human_x1_first_probability :
    firstChoiceProb appendixB2HumanRankingPMF (0 : Candidate 1) =
      67 / 100 :=
  appendixB2_human_firstChoice_x1_eq

/-- Equation (B.1): with the source's `theta_A = 1.1 theta` and
`theta_H = 0.9 theta` iid score experiments, `x₁` is selected first with equal
probability. -/
theorem source_equationB1_counterexample_first_choice_x1 :
    firstChoiceProb appendixB2AlgorithmRankingPMF (0 : Candidate 1) =
      firstChoiceProb appendixB2HumanRankingPMF (0 : Candidate 1) :=
  appendixB2_equation_B1

/-- The algorithmic source iid score experiment has the exact `x₂`
first-choice probability used in Equation (B.2). -/
theorem source_appendixB2_algorithm_x2_first_probability :
    firstChoiceProb appendixB2AlgorithmRankingPMF (1 : Candidate 1) =
      2261 / 8000 :=
  appendixB2_algorithm_firstChoice_x2_eq

/-- The human source iid score experiment has the exact `x₂` first-choice
probability used in Equation (B.2). -/
theorem source_appendixB2_human_x2_first_probability :
    firstChoiceProb appendixB2HumanRankingPMF (1 : Candidate 1) =
      109 / 400 :=
  appendixB2_human_firstChoice_x2_eq

/-- Equation (B.2): the more accurate source iid score experiment chooses
`x₂` first strictly more often than the human experiment. -/
theorem source_equationB2_counterexample_first_choice_x2 :
    firstChoiceProb appendixB2HumanRankingPMF (1 : Candidate 1) <
      firstChoiceProb appendixB2AlgorithmRankingPMF (1 : Candidate 1) :=
  appendixB2_equation_B2

/-- Both concrete ranking laws in B.2 are proved pushforwards of the literal
iid source-score enumerations, not assumed ranking-probability tables. -/
theorem source_appendixB2_iid_score_pushforward_tables
    (a : AppendixBRankingAtom) :
    appendixB2AlgorithmRankingWeight a =
      appendixB2AlgorithmIIDRUMRankingWeight a /\
    appendixB2HumanRankingWeight a =
      appendixB2HumanIIDRUMRankingWeight a :=
  ⟨appendixB2AlgorithmRankingWeight_eq_iid_rum_pushforward a,
    appendixB2HumanRankingWeight_eq_iid_rum_pushforward a⟩

end KR21Monoculture
