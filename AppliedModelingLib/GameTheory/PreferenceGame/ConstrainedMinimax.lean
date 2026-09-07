import AppliedModelingLib.Foundations.Probability.FiniteKLConvex
import AppliedModelingLib.GameTheory.PreferenceGame.KLConstrained
import Mathlib.Topology.Sion

/-!
# Finite KL-constrained symmetric preference games

This module establishes the population-level game-theoretic bridge used by
constrained NLHF.  A finite KL ball is compact and convex in real simplex
coordinates, so Sion's minimax theorem applies to the continuous bilinear,
antisymmetric centered preference payoff.  Averaging a saddle pair gives a
single feasible policy that weakly beats every feasible opponent.

## Main declarations

- `finiteBilinearMass`
- `centeredPreferenceMassPayoff`
- `IsFiniteKLPreferenceMaximin`
- `finiteKLPreferenceMaximin_isConstrainedPreferenceGameEquilibrium`
-/

namespace AppliedModelingLib
namespace GameTheory
namespace PreferenceGame

open Learning.HumanFeedback
open scoped BigOperators

noncomputable section

/-- The finite bilinear form of two real mass vectors against a payoff kernel. -/
def finiteBilinearMass {First Second : Type*} [Fintype First] [Fintype Second]
    (kernel : First → Second → ℝ) (first : First → ℝ) (second : Second → ℝ) : ℝ :=
  ∑ left : First, first left * ∑ right : Second, second right * kernel left right

/-- A centered, context-free pairwise-preference payoff on real mass vectors. -/
def centeredPreferenceMassPayoff {Response : Type*} [Fintype Response]
    (preference : PairwisePreference PUnit Response)
    (first second : Response → ℝ) : ℝ :=
  finiteBilinearMass
    (fun left right => preference.prob PUnit.unit left right - (1 : ℝ) / 2) first second

/-- The singleton-context centered payoff used by a finite KL-constrained game. -/
noncomputable def contextFreeCenteredPreferencePayoff {Response : Type*}
    [Fintype Response] [DecidableEq Response]
    (preference : PairwisePreference PUnit Response)
    (first second : PMF Response) : ℝ :=
  centeredPreferenceGamePayoff (PMF.pure PUnit.unit) preference
    (fun _ => first) (fun _ => second)

/--
The attained finite version of the source constrained `argmax min` definition.
`worst` is an attained minimizer for `policy`, and the last two clauses say
that `policy` maximizes this attained minimum over the literal finite KL ball.
-/
def IsFiniteKLPreferenceMaximin {Response : Type*} [Fintype Response] [DecidableEq Response]
    (preference : PairwisePreference PUnit Response)
    (reference : PMF Response) (klBudget : ℝ) (policy : PMF Response) : Prop :=
  finiteKLDivergence policy reference ≤ klBudget ∧
    ∃ worst : PMF Response, finiteKLDivergence worst reference ≤ klBudget ∧
      (∀ opponent : PMF Response, finiteKLDivergence opponent reference ≤ klBudget →
        contextFreeCenteredPreferencePayoff preference policy worst ≤
          contextFreeCenteredPreferencePayoff preference policy opponent) ∧
      ∀ candidate : PMF Response, finiteKLDivergence candidate reference ≤ klBudget →
        contextFreeCenteredPreferencePayoff preference candidate worst ≤
          contextFreeCenteredPreferencePayoff preference policy worst

/-- A finite bilinear form is continuous in its first mass vector. -/
theorem continuous_finiteBilinearMass_left {First Second : Type*}
    [Fintype First] [Fintype Second] (kernel : First → Second → ℝ)
    (second : Second → ℝ) :
    Continuous (fun first : First → ℝ => finiteBilinearMass kernel first second) := by
  unfold finiteBilinearMass
  apply continuous_finset_sum
  intro left _
  exact (continuous_apply left).mul continuous_const

/-- A finite bilinear form is continuous in its second mass vector. -/
theorem continuous_finiteBilinearMass_right {First Second : Type*}
    [Fintype First] [Fintype Second] (kernel : First → Second → ℝ)
    (first : First → ℝ) :
    Continuous (fun second : Second → ℝ => finiteBilinearMass kernel first second) := by
  unfold finiteBilinearMass
  apply continuous_finset_sum
  intro left _
  exact continuous_const.mul (by
    apply continuous_finset_sum
    intro right _
    exact (continuous_apply right).mul continuous_const)

/-- A finite bilinear form is affine in its first mass vector. -/
theorem finiteBilinearMass_smul_add_left {First Second : Type*}
    [Fintype First] [Fintype Second] (kernel : First → Second → ℝ)
    (first second : First → ℝ) (opponent : Second → ℝ) (a b : ℝ) :
    finiteBilinearMass kernel (a • first + b • second) opponent =
      a * finiteBilinearMass kernel first opponent +
        b * finiteBilinearMass kernel second opponent := by
  unfold finiteBilinearMass
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  calc
    (∑ left : First,
        (a * first left + b * second left) *
          ∑ right : Second, opponent right * kernel left right) =
        ∑ left : First,
          (a * (first left * ∑ right : Second, opponent right * kernel left right) +
            b * (second left * ∑ right : Second, opponent right * kernel left right)) := by
          apply Finset.sum_congr rfl
          intro left _
          ring
    _ = a * (∑ left : First,
          first left * ∑ right : Second, opponent right * kernel left right) +
        b * (∑ left : First,
          second left * ∑ right : Second, opponent right * kernel left right) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/-- A finite bilinear form is affine in its second mass vector. -/
theorem finiteBilinearMass_smul_add_right {First Second : Type*}
    [Fintype First] [Fintype Second] (kernel : First → Second → ℝ)
    (first : First → ℝ) (second third : Second → ℝ) (a b : ℝ) :
    finiteBilinearMass kernel first (a • second + b • third) =
      a * finiteBilinearMass kernel first second +
        b * finiteBilinearMass kernel first third := by
  unfold finiteBilinearMass
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  calc
    (∑ left : First, first left *
        ∑ right : Second, (a * second right + b * third right) * kernel left right) =
        ∑ left : First, first left *
          (a * (∑ right : Second, second right * kernel left right) +
            b * (∑ right : Second, third right * kernel left right)) := by
          apply Finset.sum_congr rfl
          intro left _
          congr 1
          calc
            (∑ right : Second,
                (a * second right + b * third right) * kernel left right) =
                ∑ right : Second,
                  (a * (second right * kernel left right) +
                    b * (third right * kernel left right)) := by
                    apply Finset.sum_congr rfl
                    intro right _
                    ring
            _ = a * (∑ right : Second, second right * kernel left right) +
                b * (∑ right : Second, third right * kernel left right) := by
                  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ = ∑ left : First,
        (a * (first left * ∑ right : Second, second right * kernel left right) +
          b * (first left * ∑ right : Second, third right * kernel left right)) := by
          apply Finset.sum_congr rfl
          intro left _
          ring
    _ = a * (∑ left : First, first left *
          ∑ right : Second, second right * kernel left right) +
        b * (∑ left : First, first left *
          ∑ right : Second, third right * kernel left right) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/-- An antisymmetric finite payoff kernel gives an antisymmetric bilinear form. -/
theorem finiteBilinearMass_swap_eq_neg {Action : Type*} [Fintype Action]
    (kernel : Action → Action → ℝ)
    (hkernel : ∀ first second, kernel second first = -kernel first second)
    (first second : Action → ℝ) :
    finiteBilinearMass kernel second first = -finiteBilinearMass kernel first second := by
  unfold finiteBilinearMass
  calc
    (∑ left : Action, second left *
        ∑ right : Action, first right * kernel left right) =
        ∑ left : Action, ∑ right : Action,
          second left * first right * kernel left right := by
          apply Finset.sum_congr rfl
          intro left _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro right _
          ring
    _ = ∑ right : Action, ∑ left : Action,
          first right * second left * kernel left right := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro left _
          apply Finset.sum_congr rfl
          intro right _
          ring
    _ = ∑ right : Action, ∑ left : Action,
          -(first right * second left * kernel right left) := by
          apply Finset.sum_congr rfl
          intro right _
          apply Finset.sum_congr rfl
          intro left _
          rw [hkernel left right]
          ring
    _ = ∑ right : Action,
          -(first right * ∑ left : Action, second left * kernel right left) := by
          apply Finset.sum_congr rfl
          intro right _
          calc
            (∑ left : Action, -(first right * second left * kernel right left)) =
                -(∑ left : Action, first right * second left * kernel right left) := by
                  rw [Finset.sum_neg_distrib]
            _ = -(first right * ∑ left : Action, second left * kernel right left) := by
                  congr 1
                  calc
                    (∑ left : Action, first right * second left * kernel right left) =
                        ∑ left : Action,
                          first right * (second left * kernel right left) := by
                            apply Finset.sum_congr rfl
                            intro left _
                            ring
                    _ = first right * ∑ left : Action, second left * kernel right left := by
                          rw [Finset.mul_sum]
    _ = -(∑ right : Action, first right *
          ∑ left : Action, second left * kernel right left) := by
          rw [Finset.sum_neg_distrib]

/-- The centered finite preference payoff is antisymmetric. -/
theorem centeredPreferenceMassPayoff_swap_eq_neg {Response : Type*} [Fintype Response]
    (preference : PairwisePreference PUnit Response)
    (first second : Response → ℝ) :
    centeredPreferenceMassPayoff preference second first =
      -centeredPreferenceMassPayoff preference first second := by
  apply finiteBilinearMass_swap_eq_neg
  intro left right
  have hcomplementary := preference.complementary PUnit.unit left right
  linarith

/-- The centered finite preference payoff is affine in its first mass vector. -/
theorem centeredPreferenceMassPayoff_smul_add_left {Response : Type*} [Fintype Response]
    (preference : PairwisePreference PUnit Response)
    (first second opponent : Response → ℝ) (a b : ℝ) :
    centeredPreferenceMassPayoff preference (a • first + b • second) opponent =
      a * centeredPreferenceMassPayoff preference first opponent +
        b * centeredPreferenceMassPayoff preference second opponent :=
  finiteBilinearMass_smul_add_left _ first second opponent a b

/-- The centered finite preference payoff is affine in its second mass vector. -/
theorem centeredPreferenceMassPayoff_smul_add_right {Response : Type*} [Fintype Response]
    (preference : PairwisePreference PUnit Response)
    (first second third : Response → ℝ) (a b : ℝ) :
    centeredPreferenceMassPayoff preference first (a • second + b • third) =
      a * centeredPreferenceMassPayoff preference first second +
        b * centeredPreferenceMassPayoff preference first third :=
  finiteBilinearMass_smul_add_right _ first second third a b

/-- The centered finite preference payoff is continuous in its first mass vector. -/
theorem continuous_centeredPreferenceMassPayoff_left {Response : Type*} [Fintype Response]
    (preference : PairwisePreference PUnit Response) (second : Response → ℝ) :
    Continuous (fun first : Response → ℝ =>
      centeredPreferenceMassPayoff preference first second) :=
  continuous_finiteBilinearMass_left _ second

/-- The centered finite preference payoff is continuous in its second mass vector. -/
theorem continuous_centeredPreferenceMassPayoff_right {Response : Type*} [Fintype Response]
    (preference : PairwisePreference PUnit Response) (first : Response → ℝ) :
    Continuous (fun second : Response → ℝ =>
      centeredPreferenceMassPayoff preference first second) :=
  continuous_finiteBilinearMass_right _ first

/-- Real simplex coordinates compute the same finite bilinear expectation as their PMFs. -/
theorem finiteBilinearMass_eq_pmfPairExp {First Second : Type*}
    [Fintype First] [DecidableEq First] [Fintype Second] [DecidableEq Second]
    (kernel : First → Second → ℝ) (first : First → ℝ) (second : Second → ℝ)
    (hfirst : FiniteProbabilitySimplex first) (hsecond : FiniteProbabilitySimplex second) :
    finiteBilinearMass kernel first second =
      pmfPairExp (finiteProbabilityMassToPMF first hfirst)
        (finiteProbabilityMassToPMF second hsecond) kernel := by
  unfold finiteBilinearMass pmfPairExp pmfExp
  simp only [finiteProbabilityMassToPMF_apply_toReal]

/-- The raw centered payoff agrees with the singleton-context preference-game payoff. -/
theorem centeredPreferenceMassPayoff_eq_contextFreeCenteredPreferencePayoff
    {Response : Type*} [Fintype Response] [DecidableEq Response]
    (preference : PairwisePreference PUnit Response)
    (first second : Response → ℝ)
    (hfirst : FiniteProbabilitySimplex first) (hsecond : FiniteProbabilitySimplex second) :
    centeredPreferenceMassPayoff preference first second =
      contextFreeCenteredPreferencePayoff preference
        (finiteProbabilityMassToPMF first hfirst)
        (finiteProbabilityMassToPMF second hsecond) := by
  unfold centeredPreferenceMassPayoff
  rw [finiteBilinearMass_eq_pmfPairExp
    (fun left right => preference.prob PUnit.unit left right - (1 : ℝ) / 2)
    first second hfirst hsecond]
  unfold contextFreeCenteredPreferencePayoff centeredPreferenceGamePayoff
    preferenceGamePayoff Learning.HumanFeedback.policyPreference
  rw [pmfExp_pure, pmfPairExp_sub]
  simp [pmfPairExp]

/--
An attained source `argmax min` policy in an antisymmetric finite preference
game wins every feasible comparison. The proof uses its own worst-case policy
as a feasible challenger, so the game's value is nonnegative without an
unproved equilibrium certificate.
-/
theorem finiteKLPreferenceMaximin_isConstrainedPreferenceGameEquilibrium
    {Response : Type*} [Fintype Response] [DecidableEq Response]
    (preference : PairwisePreference PUnit Response)
    (reference : PMF Response) (klBudget : ℝ) (policy : PMF Response)
    (hmaximin : IsFiniteKLPreferenceMaximin preference reference klBudget policy) :
    IsConstrainedPreferenceGameEquilibrium (PMF.pure PUnit.unit) preference
      (fun _ => reference) klBudget (fun _ => policy) := by
  rcases hmaximin with ⟨hpolicy, worst, hworst, hminimum, hmaximum⟩
  constructor
  · unfold InContextAveragedKLBall contextAveragedPolicyKLDivergence
      pointwisePolicyKLDivergence
    simpa only [pmfExp_pure] using hpolicy
  · intro opponent hopponent
    let opponentPMF : PMF Response := opponent PUnit.unit
    have hopponent_eq : opponent = fun _ => opponentPMF := by
      funext context
      cases context
      rfl
    rw [hopponent_eq] at hopponent ⊢
    have hopponent' : finiteKLDivergence opponentPMF reference ≤ klBudget := by
      unfold InContextAveragedKLBall contextAveragedPolicyKLDivergence
        pointwisePolicyKLDivergence at hopponent
      simpa only [pmfExp_pure] using hopponent
    have hminimum' := hminimum opponentPMF hopponent'
    have hmaximum' := hmaximum worst hworst
    have hself : contextFreeCenteredPreferencePayoff preference worst worst = 0 := by
      unfold contextFreeCenteredPreferencePayoff
      have hswap := centeredPreferenceGamePayoff_swap_eq_neg (PMF.pure PUnit.unit)
        preference (fun _ => worst) (fun _ => worst)
      linarith
    unfold contextFreeCenteredPreferencePayoff at hminimum' hmaximum' hself
    unfold centeredPreferenceGamePayoff at hminimum' hmaximum' hself
    linarith

/--
Every nonempty finite KL ball has an attained constrained preference-game
maximin policy.  The proof applies Sion's theorem to the negative centered
payoff in exact real simplex coordinates, then converts the saddle pair back
to PMFs.
-/
theorem exists_finiteKLPreferenceMaximin
    {Response : Type*} [Fintype Response] [DecidableEq Response]
    (preference : PairwisePreference PUnit Response)
    (reference : PMF Response) (klBudget : ℝ) (hbudget : 0 ≤ klBudget) :
    ∃ policy : PMF Response,
      IsFiniteKLPreferenceMaximin preference reference klBudget policy := by
  let feasible : Set (Response → ℝ) := finiteKLBallMass reference klBudget
  let payoff : (Response → ℝ) → (Response → ℝ) → ℝ :=
    fun first second => -centeredPreferenceMassPayoff preference first second
  have hconvexLeft (opponent : Response → ℝ) :
      ConvexOn ℝ feasible (fun policy => payoff policy opponent) := by
    constructor
    · exact finiteKLBallMass_convex reference klBudget
    · intro first hfirst second hsecond a b ha hb hab
      change -centeredPreferenceMassPayoff preference (a • first + b • second) opponent ≤
        a * (-centeredPreferenceMassPayoff preference first opponent) +
          b * (-centeredPreferenceMassPayoff preference second opponent)
      rw [centeredPreferenceMassPayoff_smul_add_left]
      ring_nf
      exact le_refl _
  have hconcaveRight (policy : Response → ℝ) :
      ConcaveOn ℝ feasible (fun opponent => payoff policy opponent) := by
    constructor
    · exact finiteKLBallMass_convex reference klBudget
    · intro first hfirst second hsecond a b ha hb hab
      change a * (-centeredPreferenceMassPayoff preference policy first) +
          b * (-centeredPreferenceMassPayoff preference policy second) ≤
        -centeredPreferenceMassPayoff preference policy (a • first + b • second)
      rw [centeredPreferenceMassPayoff_smul_add_right]
      ring_nf
      exact le_refl _
  have hlsc : ∀ opponent ∈ feasible,
      LowerSemicontinuousOn (fun policy => payoff policy opponent) feasible := by
    intro opponent hopponent
    exact ContinuousOn.lowerSemicontinuousOn
      ((continuous_centeredPreferenceMassPayoff_left preference opponent).neg.continuousOn)
  have hqconvex : ∀ opponent ∈ feasible,
      QuasiconvexOn ℝ feasible (fun policy => payoff policy opponent) := by
    intro opponent hopponent
    exact (hconvexLeft opponent).quasiconvexOn
  have husc : ∀ policy ∈ feasible,
      UpperSemicontinuousOn (fun opponent => payoff policy opponent) feasible := by
    intro policy hpolicy
    exact ContinuousOn.upperSemicontinuousOn
      ((continuous_centeredPreferenceMassPayoff_right preference policy).neg.continuousOn)
  have hqconcave : ∀ policy ∈ feasible,
      QuasiconcaveOn ℝ feasible (fun opponent => payoff policy opponent) := by
    intro policy hpolicy
    exact (hconcaveRight policy).quasiconcaveOn
  obtain ⟨first, hfirst, second, hsecond, hsaddle⟩ :=
    Sion.exists_isSaddlePointOn
      (finiteKLBallMass_nonempty reference hbudget)
      (finiteKLBallMass_convex reference klBudget)
      (finiteKLBallMass_isCompact reference klBudget)
      hlsc hqconvex
      (finiteKLBallMass_convex reference klBudget)
      (finiteKLBallMass_nonempty reference hbudget)
      (finiteKLBallMass_isCompact reference klBudget)
      husc hqconcave
  change FiniteProbabilitySimplex first ∧
    finiteKLDivergenceMass first reference ≤ klBudget at hfirst
  change FiniteProbabilitySimplex second ∧
    finiteKLDivergenceMass second reference ≤ klBudget at hsecond
  let firstPolicy := finiteProbabilityMassToPMF first hfirst.1
  let secondPolicy := finiteProbabilityMassToPMF second hsecond.1
  refine ⟨firstPolicy, ?_⟩
  constructor
  · rw [show firstPolicy = finiteProbabilityMassToPMF first hfirst.1 by rfl]
    rw [finiteKLDivergence_finiteProbabilityMassToPMF]
    exact hfirst.2
  · refine ⟨secondPolicy, ?_, ?_, ?_⟩
    · rw [show secondPolicy = finiteProbabilityMassToPMF second hsecond.1 by rfl]
      rw [finiteKLDivergence_finiteProbabilityMassToPMF]
      exact hsecond.2
    · intro opponent hopponent
      let opponentMass : Response → ℝ := fun response => (opponent response).toReal
      have hopponentSimplex : FiniteProbabilitySimplex opponentMass :=
        finiteProbabilitySimplex_pmfMass opponent
      have hopponentFeasible : opponentMass ∈ feasible := by
        change FiniteProbabilitySimplex opponentMass ∧
          finiteKLDivergenceMass opponentMass reference ≤ klBudget
        constructor
        · exact hopponentSimplex
        · rw [finiteKLDivergenceMass_pmf]
          exact hopponent
      have hsaddle' := hsaddle first hfirst opponentMass hopponentFeasible
      change payoff first opponentMass ≤ payoff first second at hsaddle'
      have hfirstOpponent :=
        centeredPreferenceMassPayoff_eq_contextFreeCenteredPreferencePayoff
          preference first opponentMass hfirst.1 hopponentSimplex
      have hfirstSecond :=
        centeredPreferenceMassPayoff_eq_contextFreeCenteredPreferencePayoff
          preference first second hfirst.1 hsecond.1
      unfold payoff at hsaddle'
      rw [hfirstOpponent, hfirstSecond] at hsaddle'
      have hopponentPMF :
          finiteProbabilityMassToPMF opponentMass hopponentSimplex = opponent := by
        simpa only [opponentMass] using finiteProbabilityMassToPMF_pmfMass opponent
      rw [hopponentPMF] at hsaddle'
      change contextFreeCenteredPreferencePayoff preference firstPolicy secondPolicy ≤
        contextFreeCenteredPreferencePayoff preference firstPolicy opponent
      dsimp only [firstPolicy, secondPolicy]
      linarith
    · intro candidate hcandidate
      let candidateMass : Response → ℝ := fun response => (candidate response).toReal
      have hcandidateSimplex : FiniteProbabilitySimplex candidateMass :=
        finiteProbabilitySimplex_pmfMass candidate
      have hcandidateFeasible : candidateMass ∈ feasible := by
        change FiniteProbabilitySimplex candidateMass ∧
          finiteKLDivergenceMass candidateMass reference ≤ klBudget
        constructor
        · exact hcandidateSimplex
        · rw [finiteKLDivergenceMass_pmf]
          exact hcandidate
      have hsaddle' := hsaddle candidateMass hcandidateFeasible second hsecond
      change payoff first second ≤ payoff candidateMass second at hsaddle'
      have hfirstSecond :=
        centeredPreferenceMassPayoff_eq_contextFreeCenteredPreferencePayoff
          preference first second hfirst.1 hsecond.1
      have hcandidateSecond :=
        centeredPreferenceMassPayoff_eq_contextFreeCenteredPreferencePayoff
          preference candidateMass second hcandidateSimplex hsecond.1
      unfold payoff at hsaddle'
      rw [hfirstSecond, hcandidateSecond] at hsaddle'
      have hcandidatePMF :
          finiteProbabilityMassToPMF candidateMass hcandidateSimplex = candidate := by
        simpa only [candidateMass] using finiteProbabilityMassToPMF_pmfMass candidate
      rw [hcandidatePMF] at hsaddle'
      change contextFreeCenteredPreferencePayoff preference candidate secondPolicy ≤
        contextFreeCenteredPreferencePayoff preference firstPolicy secondPolicy
      dsimp only [firstPolicy, secondPolicy]
      linarith

end

end PreferenceGame
end GameTheory
end AppliedModelingLib
