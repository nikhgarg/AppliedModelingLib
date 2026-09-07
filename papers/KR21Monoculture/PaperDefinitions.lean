import KR21Monoculture.Game

namespace KR21Monoculture
namespace Model

/--
Utility-side version of the paper's "preference for the first position":
when both firms draw from the same ranking distribution, the second mover prefers
an independent reranking to reusing the common ranking.
-/
noncomputable def PrefersIndependentReranking {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ) : Prop :=
  AppliedModelingLib.SocialChoice.Ranking.PrefersIndependentReranking μ value

/--
Utility-side version of the paper's "preference for weaker competition":
holding the second mover's own distribution fixed at the noisier ranking, the
second mover does better when the first mover also uses the noisier ranking than
when the first mover uses the more accurate one.
-/
noncomputable def PrefersWeakerCompetition {n : ℕ}
    (μBetter μWorse : PMF (Ranking n)) (value : Candidate n → ℝ) : Prop :=
  AppliedModelingLib.SocialChoice.Ranking.PrefersWeakerCompetition μBetter μWorse value

/-- The fixed-parameter hypotheses corresponding to a single pair `(μA, μH)`. -/
noncomputable def PaperHypotheses {n : ℕ} (M : Model n) : Prop :=
  PrefersIndependentReranking M.algorithmRanking M.value ∧
    PrefersWeakerCompetition M.algorithmRanking M.humanRanking M.value

/--
A proposition packaging the fixed-parameter conclusion analogous to Theorem 1.
The actual existence-of-`θA` statement belongs one level up, in a family of models
indexed by an accuracy parameter.
-/
noncomputable def FixedParameterTheorem1Conclusion {n : ℕ} (M : Model n) : Prop := HasKR21MonocultureParadox M

end Model
end KR21Monoculture
