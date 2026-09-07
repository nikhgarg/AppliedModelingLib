import KR21Monoculture.AppendixB

open AppliedModelingLib
open scoped BigOperators

namespace KR21Monoculture

/-!
# Appendix B Gaussian-mixture smoothing: finite stability layer

The Appendix B prose says that its finite discrete RUM witnesses can be
replaced by arbitrarily concentrated Gaussian mixtures.  That statement has
two logically separate parts:

1. a measure-level construction must show that the induced finite ranking PMF
   of the Gaussian-mixture model extends continuously to zero component scale;
2. the strict finite payoff reversal must persist under that convergence.

This module proves (2), and checks the concrete no-tie hypothesis needed for
(1) at every source discrete noise realization.  It intentionally does *not*
turn a law merely named "Gaussian mixture" into the required atomwise
continuity fact.  A later measure-level construction must prove that fact for
the actual iid finite mixture of positive-variance Gaussian components.  This
keeps the source's analytic smoothing claim visible instead of smuggling it
into a theorem statement.

The scale parameter is represented by a real `s`, with `s = 0` the existing
discrete ranking law and `s > 0` a proposed smooth approximation.  The
continuity assumptions are about the six actual ranking atoms, not about Lean
declaration names or an informal approximation label.
-/

/-! ## Concrete discrete score gaps -/

/-- Appendix B.1 source scores at the discrete component centers. -/
noncomputable def appendixB1DiscreteScore
    (noise : Candidate 1 → AppendixB1NoiseAtom) (c : Candidate 1) : ℝ :=
  appendixB1Value c + appendixB1NoiseValue (noise c)

/--
Every Appendix B.1 source score realization is tie-free.  This is essential:
without it, shrinking continuous component noise can converge to a different
tie-breaking law than the displayed discrete table.
-/
theorem appendixB1_discreteScore_noTies
    (noise : Candidate 1 → AppendixB1NoiseAtom) :
    ∀ i j : Candidate 1, i ≠ j →
      appendixB1DiscreteScore noise i ≠ appendixB1DiscreteScore noise j := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [appendixB1DiscreteScore, appendixB1Value]
  all_goals
    generalize h0 : noise 0 = e0
    generalize h1 : noise 1 = e1
    generalize h2 : noise 2 = e2
    fin_cases e0 <;> fin_cases e1 <;> fin_cases e2 <;>
      norm_num [appendixB1NoiseValue, h0, h1, h2]

/-- Appendix B.2 algorithm scores at the discrete component centers. -/
noncomputable def appendixB2AlgorithmDiscreteScore
    (noise : Candidate 1 → AppendixB2NoiseAtom) (c : Candidate 1) : ℝ :=
  appendixB2Value c + (10 / 11) * appendixB2NoiseValue (noise c)

/-- Appendix B.2 human scores at the discrete component centers. -/
noncomputable def appendixB2HumanDiscreteScore
    (noise : Candidate 1 → AppendixB2NoiseAtom) (c : Candidate 1) : ℝ :=
  appendixB2Value c + (10 / 9) * appendixB2NoiseValue (noise c)

/-- The B.2 algorithmic discrete score table has no pairwise ties. -/
theorem appendixB2_algorithmDiscreteScore_noTies
    (noise : Candidate 1 → AppendixB2NoiseAtom) :
    ∀ i j : Candidate 1, i ≠ j →
      appendixB2AlgorithmDiscreteScore noise i ≠
        appendixB2AlgorithmDiscreteScore noise j := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [appendixB2AlgorithmDiscreteScore, appendixB2Value]
  all_goals
    generalize h0 : noise 0 = e0
    generalize h1 : noise 1 = e1
    generalize h2 : noise 2 = e2
    fin_cases e0 <;> fin_cases e1 <;> fin_cases e2 <;>
      norm_num [appendixB2NoiseValue, h0, h1, h2]

/-- The B.2 human discrete score table has no pairwise ties. -/
theorem appendixB2_humanDiscreteScore_noTies
    (noise : Candidate 1 → AppendixB2NoiseAtom) :
    ∀ i j : Candidate 1, i ≠ j →
      appendixB2HumanDiscreteScore noise i ≠
        appendixB2HumanDiscreteScore noise j := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [appendixB2HumanDiscreteScore, appendixB2Value]
  all_goals
    generalize h0 : noise 0 = e0
    generalize h1 : noise 1 = e1
    generalize h2 : noise 2 = e2
    fin_cases e0 <;> fin_cases e1 <;> fin_cases e2 <;>
      norm_num [appendixB2NoiseValue, h0, h1, h2]

/--
Tie-free finite score vectors keep the same ranking under any coordinatewise
perturbation that is continuous at zero and vanishes there.  This is the
pointwise source step used to establish atomwise convergence of a coupled
Gaussian-mixture ranking law.
-/
private theorem rankByScore_eventually_eq_of_continuous_zero_perturbation
    (base : Candidate 1 → ℝ)
    (hnoTie : ∀ i j : Candidate 1, i ≠ j → base i ≠ base j)
    (perturb : ℝ → Candidate 1 → ℝ)
    (hcontinuous : ∀ c : Candidate 1,
      ContinuousAt (fun s => perturb s c) 0)
    (hzero : ∀ c : Candidate 1, perturb 0 c = 0) :
    ∀ᶠ s in nhds 0,
      AppliedModelingLib.SocialChoice.Ranking.rankByScore
          (fun c => base c + perturb s c) =
        AppliedModelingLib.SocialChoice.Ranking.rankByScore base := by
  have hscore_zero : (fun c => base c + perturb 0 c) = base := by
    funext c
    rw [hzero c, add_zero]
  have hnoTieAtZero : ∀ i j : Candidate 1, i ≠ j →
      base i + perturb 0 i ≠ base j + perturb 0 j := by
    intro i j hij
    simpa only [hzero i, hzero j, add_zero] using hnoTie i j hij
  have hstable :=
    AppliedModelingLib.SocialChoice.Ranking.eventually_rankByScore_eq_of_continuousAt_of_noTies
      (score := fun s c => base c + perturb s c)
      (x := 0)
      (fun c => continuousAt_const.add (hcontinuous c))
      hnoTieAtZero
  simpa only [hscore_zero] using hstable

/--
Pointwise local ranking stability for each B.1 discrete noise realization.
For a Gaussian component perturbation, take `perturb s c = s * z c`.
-/
theorem appendixB1_rankByScore_eventually_eq_of_continuous_perturbation
    (noise : Candidate 1 → AppendixB1NoiseAtom)
    (perturb : ℝ → Candidate 1 → ℝ)
    (hcontinuous : ∀ c : Candidate 1,
      ContinuousAt (fun s => perturb s c) 0)
    (hzero : ∀ c : Candidate 1, perturb 0 c = 0) :
    ∀ᶠ s in nhds 0,
      AppliedModelingLib.SocialChoice.Ranking.rankByScore
          (fun c => appendixB1DiscreteScore noise c + perturb s c) =
        AppliedModelingLib.SocialChoice.Ranking.rankByScore
          (appendixB1DiscreteScore noise) := by
  exact rankByScore_eventually_eq_of_continuous_zero_perturbation
    (appendixB1DiscreteScore noise)
    (appendixB1_discreteScore_noTies noise)
    perturb hcontinuous hzero

/-- Pointwise local ranking stability for each B.2 algorithmic realization. -/
theorem appendixB2_algorithmRankByScore_eventually_eq_of_continuous_perturbation
    (noise : Candidate 1 → AppendixB2NoiseAtom)
    (perturb : ℝ → Candidate 1 → ℝ)
    (hcontinuous : ∀ c : Candidate 1,
      ContinuousAt (fun s => perturb s c) 0)
    (hzero : ∀ c : Candidate 1, perturb 0 c = 0) :
    ∀ᶠ s in nhds 0,
      AppliedModelingLib.SocialChoice.Ranking.rankByScore
          (fun c => appendixB2AlgorithmDiscreteScore noise c + perturb s c) =
        AppliedModelingLib.SocialChoice.Ranking.rankByScore
          (appendixB2AlgorithmDiscreteScore noise) := by
  exact rankByScore_eventually_eq_of_continuous_zero_perturbation
    (appendixB2AlgorithmDiscreteScore noise)
    (appendixB2_algorithmDiscreteScore_noTies noise)
    perturb hcontinuous hzero

/-- Pointwise local ranking stability for each B.2 human realization. -/
theorem appendixB2_humanRankByScore_eventually_eq_of_continuous_perturbation
    (noise : Candidate 1 → AppendixB2NoiseAtom)
    (perturb : ℝ → Candidate 1 → ℝ)
    (hcontinuous : ∀ c : Candidate 1,
      ContinuousAt (fun s => perturb s c) 0)
    (hzero : ∀ c : Candidate 1, perturb 0 c = 0) :
    ∀ᶠ s in nhds 0,
      AppliedModelingLib.SocialChoice.Ranking.rankByScore
          (fun c => appendixB2HumanDiscreteScore noise c + perturb s c) =
        AppliedModelingLib.SocialChoice.Ranking.rankByScore
          (appendixB2HumanDiscreteScore noise) := by
  exact rankByScore_eventually_eq_of_continuous_zero_perturbation
    (appendixB2HumanDiscreteScore noise)
    (appendixB2_humanDiscreteScore_noTies noise)
    perturb hcontinuous hzero

/-! ## Finite rank-law stability -/

/--
An independent finite pair expectation is continuous when each atom of both
input PMF families is continuous.  The result is stated directly over finite
ranking laws so it can be applied to any proved smoothing construction.
-/
private theorem pmfPairExp_continuousAt_of_atomwise
    {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    {lawLeft : ℝ → PMF α} {lawRight : ℝ → PMF β} {x : ℝ}
    (hleft : ∀ a : α, ContinuousAt (fun t => ((lawLeft t) a).toReal) x)
    (hright : ∀ b : β, ContinuousAt (fun t => ((lawRight t) b).toReal) x)
    (payoff : α → β → ℝ) :
    ContinuousAt
      (fun t => AppliedModelingLib.pmfPairExp (lawLeft t) (lawRight t) payoff) x := by
  unfold AppliedModelingLib.pmfPairExp AppliedModelingLib.pmfExp
  apply AppliedModelingLib.continuousAt_finset_sum
  intro a _
  exact (hleft a).mul (AppliedModelingLib.continuousAt_finset_sum Finset.univ
    (fun b _ => (hright b).mul continuousAt_const))

/--
The exact Appendix B.1 reversal survives every sufficiently small positive
rank-law smoothing whose six ranking-atom probabilities continuously converge
to the checked discrete law at scale zero.

To apply this to the paper's proposed Gaussian mixture, the remaining
measure-level obligation is to prove `hatom` for its induced ranking law and
to prove `hbase`; the no-tie theorem above supplies the source-side stability
condition for that proof.
-/
theorem appendixB1_reversal_persists_of_atomwise_continuity
    (law : ℝ → PMF (Ranking 1))
    (hatom : ∀ pi : Ranking 1,
      ContinuousAt (fun s => ((law s) pi).toReal) 0)
    (hbase : law 0 = appendixB1RankingPMF) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ s : ℝ, 0 < s → s < delta →
      AppliedModelingLib.SocialChoice.Ranking.expectedSecondMoverIndependent
          (law s) (law s) appendixB1Value -
        AppliedModelingLib.SocialChoice.Ranking.expectedSecondMoverShared
          (law s) appendixB1Value < 0 := by
  have hindependent : AppliedModelingLib.EpsilonContinuousAt
      (fun s => AppliedModelingLib.SocialChoice.Ranking.expectedSecondMoverIndependent
        (law s) (law s) appendixB1Value) 0 :=
    AppliedModelingLib.epsilonContinuousAt_of_continuousAt
      (pmfPairExp_continuousAt_of_atomwise hatom hatom
        (AppliedModelingLib.SocialChoice.Ranking.secondMoverUtility appendixB1Value))
  have hshared : AppliedModelingLib.EpsilonContinuousAt
      (fun s => AppliedModelingLib.SocialChoice.Ranking.expectedSecondMoverShared
        (law s) appendixB1Value) 0 := by
    unfold AppliedModelingLib.SocialChoice.Ranking.expectedSecondMoverShared
    exact AppliedModelingLib.epsilonContinuousAt_pmfExp_of_atom
      (fun pi => AppliedModelingLib.epsilonContinuousAt_of_continuousAt (hatom pi)) _
  have hgap := AppliedModelingLib.epsilonContinuousAt_sub hindependent hshared
  have hzero :
      (fun s => AppliedModelingLib.SocialChoice.Ranking.expectedSecondMoverIndependent
          (law s) (law s) appendixB1Value -
        AppliedModelingLib.SocialChoice.Ranking.expectedSecondMoverShared
          (law s) appendixB1Value) 0 < 0 := by
    change
      AppliedModelingLib.SocialChoice.Ranking.expectedSecondMoverIndependent
          (law 0) (law 0) appendixB1Value -
        AppliedModelingLib.SocialChoice.Ranking.expectedSecondMoverShared
          (law 0) appendixB1Value < 0
    rw [hbase]
    rw [appendixB1_definition2_reversal_exact]
    norm_num
  simpa using AppliedModelingLib.exists_right_radius_lt_of_epsilonContinuousAt
    hgap (AppliedModelingLib.epsilonContinuousAt_const 0 0) hzero

/--
The exact Appendix B.2 reversal survives every sufficiently small positive
rank-law smoothing whose algorithm and human ranking atoms each continuously
converge to their checked discrete laws at scale zero.

The conclusion is the literal source payoff sign `U_AH - U_HH > 0`; it is not
replaced by a weaker first-choice or pointwise comparison.
-/
theorem appendixB2_reversal_persists_of_atomwise_continuity
    (algorithm human : ℝ → PMF (Ranking 1))
    (halgorithm : ∀ pi : Ranking 1,
      ContinuousAt (fun s => ((algorithm s) pi).toReal) 0)
    (hhuman : ∀ pi : Ranking 1,
      ContinuousAt (fun s => ((human s) pi).toReal) 0)
    (halgorithm_base : algorithm 0 = appendixB2AlgorithmRankingPMF)
    (hhuman_base : human 0 = appendixB2HumanRankingPMF) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ s : ℝ, 0 < s → s < delta →
      0 <
        AppliedModelingLib.SocialChoice.Ranking.expectedSecondMoverIndependent
            (human s) (algorithm s) appendixB2Value -
          AppliedModelingLib.SocialChoice.Ranking.expectedSecondMoverIndependent
            (human s) (human s) appendixB2Value := by
  have hAgainstAlgorithm : AppliedModelingLib.EpsilonContinuousAt
      (fun s => AppliedModelingLib.SocialChoice.Ranking.expectedSecondMoverIndependent
        (human s) (algorithm s) appendixB2Value) 0 :=
    AppliedModelingLib.epsilonContinuousAt_of_continuousAt
      (pmfPairExp_continuousAt_of_atomwise hhuman halgorithm
        (AppliedModelingLib.SocialChoice.Ranking.secondMoverUtility appendixB2Value))
  have hAgainstHuman : AppliedModelingLib.EpsilonContinuousAt
      (fun s => AppliedModelingLib.SocialChoice.Ranking.expectedSecondMoverIndependent
        (human s) (human s) appendixB2Value) 0 :=
    AppliedModelingLib.epsilonContinuousAt_of_continuousAt
      (pmfPairExp_continuousAt_of_atomwise hhuman hhuman
        (AppliedModelingLib.SocialChoice.Ranking.secondMoverUtility appendixB2Value))
  have hgap := AppliedModelingLib.epsilonContinuousAt_sub hAgainstAlgorithm hAgainstHuman
  have hzero : 0 <
      (fun s =>
        AppliedModelingLib.SocialChoice.Ranking.expectedSecondMoverIndependent
            (human s) (algorithm s) appendixB2Value -
          AppliedModelingLib.SocialChoice.Ranking.expectedSecondMoverIndependent
            (human s) (human s) appendixB2Value) 0 := by
    change 0 <
      AppliedModelingLib.SocialChoice.Ranking.expectedSecondMoverIndependent
          (human 0) (algorithm 0) appendixB2Value -
        AppliedModelingLib.SocialChoice.Ranking.expectedSecondMoverIndependent
          (human 0) (human 0) appendixB2Value
    rw [halgorithm_base, hhuman_base]
    rw [appendixB2_definition3_reversal_exact]
    norm_num
  simpa using AppliedModelingLib.exists_right_radius_lt_of_epsilonContinuousAt
    (AppliedModelingLib.epsilonContinuousAt_const 0 0) hgap hzero

end KR21Monoculture
