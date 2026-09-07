import AppliedModelingLib.GameTheory.PreferenceGame.Basic

/-!
# External regret and empirical equilibria in finite preference games

This module gives the algebraic no-regret-to-minimax conversion needed by the
unregularized NLHF/maximal-lottery route.  It is stated first for an arbitrary
payoff with a finite empirical-average operator.  The preference-game
specialization then discharges the average-payoff identities using the finite
PMF policy model.

The regret hypotheses are *average* external-regret bounds, namely uniform
expectations over a finite nonempty time type.  A conventional cumulative
bound of `R` over `T` rounds instantiates these hypotheses with `R / T`.
-/

namespace AppliedModelingLib
namespace GameTheory
namespace PreferenceGame

/--
An additive saddle-point guarantee for a maximizer (first policy) and a
minimizer (second policy).  No compactness or equilibrium-existence premise is
built into this definition.
-/
def IsApproximateSaddle {Policy : Type*}
    (payoff : Policy → Policy → ℝ) (approximation : ℝ)
    (first second : Policy) : Prop :=
  (∀ firstAlternative,
    payoff firstAlternative second ≤ payoff first second + approximation) ∧
  (∀ secondAlternative,
    payoff first second - approximation ≤ payoff first secondAlternative)

/--
A pointwise upper bound on the exact max--min duality gap.  In a finite game,
quantifying over both alternatives is equivalent to
`max_x payoff x second - min_y payoff first y ≤ approximation`, but this form
does not require choosing maximizers or minimizers.
-/
def HasDualityGapAtMost {Policy : Type*}
    (payoff : Policy → Policy → ℝ) (approximation : ℝ)
    (first second : Policy) : Prop :=
  ∀ firstAlternative secondAlternative,
    payoff firstAlternative second - payoff first secondAlternative ≤ approximation

/--
Duality-gap stability in a constant-sum game.  If a replacement strategy has
every row payoff within `error` of an original strategy, constant-sum symmetry
gives the same control for its column payoffs, so the symmetric duality gap
increases by at most `2 * error`.
-/
theorem dualityGapAtMost_stable_of_constantSum_rowClose
    {Policy : Type*} (payoff : Policy → Policy → ℝ) (constant : ℝ)
    (original replacement : Policy) (approximation error : ℝ)
    (hconstantSum : ∀ first second,
      payoff first second + payoff second first = constant)
    (hgap : HasDualityGapAtMost payoff approximation original original)
    (hrowClose : ∀ alternative,
      |payoff replacement alternative - payoff original alternative| ≤ error) :
    HasDualityGapAtMost payoff (approximation + 2 * error)
      replacement replacement := by
  intro firstAlternative secondAlternative
  have hsource := hgap firstAlternative secondAlternative
  have hfirstClose := hrowClose firstAlternative
  have hsecondClose := hrowClose secondAlternative
  have hfirstSum := hconstantSum firstAlternative replacement
  have hfirstOriginalSum := hconstantSum firstAlternative original
  rw [abs_le] at hfirstClose hsecondClose
  linarith

/--
In any symmetric constant-sum game, both members of an exact saddle pair are
exact symmetric equilibria.  This is the abstract restricted-Nash reduction;
no preference-specific representation is used.
-/
theorem constantSum_pair_zeroDualityGap_both_self
    {Policy : Type*} (payoff : Policy → Policy → ℝ) (constant : ℝ)
    (first second : Policy)
    (hconstantSum : ∀ left right,
      payoff left right + payoff right left = constant)
    (hgap : HasDualityGapAtMost payoff 0 first second) :
    HasDualityGapAtMost payoff 0 first first ∧
      HasDualityGapAtMost payoff 0 second second := by
  have hfirstSelf : 2 * payoff first first = constant := by
    linarith [hconstantSum first first]
  have hsecondSelf : 2 * payoff second second = constant := by
    linarith [hconstantSum second second]
  constructor
  · intro firstAlternative secondAlternative
    have hleft := hgap second firstAlternative
    have hright := hgap second secondAlternative
    have hswap := hconstantSum first firstAlternative
    linarith
  · intro firstAlternative secondAlternative
    have hpivot := hgap first first
    have hleft := hgap firstAlternative second
    have hright := hgap secondAlternative second
    have hswap := hconstantSum second secondAlternative
    linarith

/--
Preference-game specialization of constant-sum duality-gap stability.
-/
theorem preferenceGame_dualityGapAtMost_stable_of_rowClose
    {Context Response : Type*}
    [Fintype Context] [DecidableEq Context]
    [Fintype Response] [DecidableEq Response]
    (contextLaw : PMF Context)
    (preference : Learning.HumanFeedback.PairwisePreference Context Response)
    (original replacement : Learning.HumanFeedback.FinitePolicy Context Response)
    (approximation error : ℝ)
    (hgap : HasDualityGapAtMost
      (preferenceGamePayoff contextLaw preference) approximation original original)
    (hrowClose : ∀ alternative,
      |preferenceGamePayoff contextLaw preference replacement alternative -
        preferenceGamePayoff contextLaw preference original alternative| ≤ error) :
    HasDualityGapAtMost (preferenceGamePayoff contextLaw preference)
      (approximation + 2 * error) replacement replacement :=
  dualityGapAtMost_stable_of_constantSum_rowClose
    (preferenceGamePayoff contextLaw preference) 1 original replacement
    approximation error
    (preferenceGamePayoff_add_swap contextLaw preference) hgap hrowClose

/--
If every opponent receives, on average over a sequence of policies, payoff at
most `error` above the constant-sum value `1/2`, then the time-averaged policy
has symmetric duality gap at most `2 * error`.  This is the deterministic
output-mixture endgame used by optimistic algorithms for von Neumann winners.
-/
theorem preferenceGame_timeAveragedPolicy_selfDualityGapAtMost_of_expectedRowFloor
    {Time Context Response : Type*}
    [Fintype Time] [DecidableEq Time] [Nonempty Time]
    [Fintype Context] [DecidableEq Context]
    [Fintype Response] [DecidableEq Response]
    (contextLaw : PMF Context)
    (preference : Learning.HumanFeedback.PairwisePreference Context Response)
    (trajectory : Time → Learning.HumanFeedback.FinitePolicy Context Response)
    (error : ℝ)
    (hrowFloor : ∀ alternative,
      1 / 2 - error ≤
        pmfExp (uniformPMF Time) (fun time ↦
          preferenceGamePayoff contextLaw preference
            (trajectory time) alternative)) :
    HasDualityGapAtMost (preferenceGamePayoff contextLaw preference)
      (2 * error)
      (Learning.HumanFeedback.timeAveragedPolicy trajectory)
      (Learning.HumanFeedback.timeAveragedPolicy trajectory) := by
  intro firstAlternative secondAlternative
  have hfirst := hrowFloor firstAlternative
  have hsecond := hrowFloor secondAlternative
  rw [← Learning.HumanFeedback.policyPreference_timeAveragedPolicy_left]
    at hfirst hsecond
  have hswap := preferenceGamePayoff_add_swap contextLaw preference
    (Learning.HumanFeedback.timeAveragedPolicy trajectory) firstAlternative
  linarith

/--
The exact no-regret-to-duality-gap conversion.  Unlike deriving the result via
two separate approximate-saddle inequalities, this preserves the sum of the
two regret bounds without an additional factor of two.
-/
theorem empiricalAverage_externalRegret_dualityGapAtMost
    {Time Policy : Type*} [Fintype Time] [DecidableEq Time] [Nonempty Time]
    (average : (Time → Policy) → Policy) (payoff : Policy → Policy → ℝ)
    (firstTrajectory secondTrajectory : Time → Policy)
    (firstRegret secondRegret : ℝ)
    (haverage_left :
      ∀ (trajectory : Time → Policy) (second : Policy),
        payoff (average trajectory) second =
          pmfExp (uniformPMF Time) (fun time => payoff (trajectory time) second))
    (haverage_right :
      ∀ (first : Policy) (trajectory : Time → Policy),
        payoff first (average trajectory) =
          pmfExp (uniformPMF Time) (fun time => payoff first (trajectory time)))
    (hfirstRegret : ∀ firstAlternative,
      pmfExp (uniformPMF Time) (fun time =>
        payoff firstAlternative (secondTrajectory time) -
          payoff (firstTrajectory time) (secondTrajectory time)) ≤ firstRegret)
    (hsecondRegret : ∀ secondAlternative,
      pmfExp (uniformPMF Time) (fun time =>
        payoff (firstTrajectory time) (secondTrajectory time) -
          payoff (firstTrajectory time) secondAlternative) ≤ secondRegret) :
    HasDualityGapAtMost payoff (firstRegret + secondRegret)
      (average firstTrajectory) (average secondTrajectory) := by
  intro firstAlternative secondAlternative
  have hfirst := hfirstRegret firstAlternative
  have hsecond := hsecondRegret secondAlternative
  rw [pmfExp_sub] at hfirst hsecond
  rw [haverage_right, haverage_left]
  linarith

/--
Average external regret for both players implies that their empirical average
policies form an approximate saddle point.  The only game-specific premises
are the two identities saying that payoff is affine in each empirical average.
-/
theorem empiricalAverage_externalRegret_approximateSaddle
    {Time Policy : Type*} [Fintype Time] [DecidableEq Time] [Nonempty Time]
    (average : (Time → Policy) → Policy) (payoff : Policy → Policy → ℝ)
    (firstTrajectory secondTrajectory : Time → Policy)
    (firstRegret secondRegret : ℝ)
    (haverage_left :
      ∀ (trajectory : Time → Policy) (second : Policy),
        payoff (average trajectory) second =
          pmfExp (uniformPMF Time) (fun time => payoff (trajectory time) second))
    (haverage_right :
      ∀ (first : Policy) (trajectory : Time → Policy),
        payoff first (average trajectory) =
          pmfExp (uniformPMF Time) (fun time => payoff first (trajectory time)))
    (hfirstRegret : ∀ firstAlternative,
      pmfExp (uniformPMF Time) (fun time =>
        payoff firstAlternative (secondTrajectory time) -
          payoff (firstTrajectory time) (secondTrajectory time)) ≤ firstRegret)
    (hsecondRegret : ∀ secondAlternative,
      pmfExp (uniformPMF Time) (fun time =>
        payoff (firstTrajectory time) (secondTrajectory time) -
          payoff (firstTrajectory time) secondAlternative) ≤ secondRegret) :
    IsApproximateSaddle payoff (firstRegret + secondRegret)
      (average firstTrajectory) (average secondTrajectory) := by
  unfold IsApproximateSaddle
  constructor
  · intro firstAlternative
    have hfirst := hfirstRegret firstAlternative
    rw [pmfExp_sub] at hfirst
    have hsecond := hsecondRegret (average secondTrajectory)
    rw [pmfExp_sub] at hsecond
    have hfirstAverage :
        payoff firstAlternative (average secondTrajectory) =
          pmfExp (uniformPMF Time) (fun time =>
            payoff firstAlternative (secondTrajectory time)) :=
      haverage_right firstAlternative secondTrajectory
    have hplayedAgainstAverage :
        payoff (average firstTrajectory) (average secondTrajectory) =
          pmfExp (uniformPMF Time) (fun time =>
            payoff (firstTrajectory time) (average secondTrajectory)) :=
      haverage_left firstTrajectory (average secondTrajectory)
    linarith
  · intro secondAlternative
    have hfirst := hfirstRegret (average firstTrajectory)
    rw [pmfExp_sub] at hfirst
    have hsecond := hsecondRegret secondAlternative
    rw [pmfExp_sub] at hsecond
    have havgAgainstPlayed :
        payoff (average firstTrajectory) (average secondTrajectory) =
          pmfExp (uniformPMF Time) (fun time =>
            payoff (average firstTrajectory) (secondTrajectory time)) :=
      haverage_right (average firstTrajectory) secondTrajectory
    have hplayedAgainstAlternative :
        payoff (average firstTrajectory) secondAlternative =
          pmfExp (uniformPMF Time) (fun time =>
            payoff (firstTrajectory time) secondAlternative) :=
      haverage_left firstTrajectory secondAlternative
    linarith

/--
The finite PMF preference game satisfies the hypotheses of the generic
empirical-average saddle theorem.
-/
theorem preferenceGame_empiricalAverage_externalRegret_approximateSaddle
    {Time Context Response : Type*}
    [Fintype Time] [DecidableEq Time] [Nonempty Time]
    [Fintype Context] [DecidableEq Context]
    [Fintype Response] [DecidableEq Response]
    (contextLaw : PMF Context)
    (preference : Learning.HumanFeedback.PairwisePreference Context Response)
    (firstTrajectory secondTrajectory : Time → Learning.HumanFeedback.FinitePolicy Context Response)
    (firstRegret secondRegret : ℝ)
    (hfirstRegret : ∀ firstAlternative,
      pmfExp (uniformPMF Time) (fun time =>
        preferenceGamePayoff contextLaw preference firstAlternative (secondTrajectory time) -
          preferenceGamePayoff contextLaw preference (firstTrajectory time)
            (secondTrajectory time)) ≤ firstRegret)
    (hsecondRegret : ∀ secondAlternative,
      pmfExp (uniformPMF Time) (fun time =>
        preferenceGamePayoff contextLaw preference (firstTrajectory time)
            (secondTrajectory time) -
          preferenceGamePayoff contextLaw preference (firstTrajectory time)
            secondAlternative) ≤ secondRegret) :
    IsApproximateSaddle (preferenceGamePayoff contextLaw preference)
      (firstRegret + secondRegret)
      (Learning.HumanFeedback.timeAveragedPolicy firstTrajectory)
      (Learning.HumanFeedback.timeAveragedPolicy secondTrajectory) := by
  apply empiricalAverage_externalRegret_approximateSaddle
    (average := Learning.HumanFeedback.timeAveragedPolicy)
    (payoff := preferenceGamePayoff contextLaw preference)
    (firstTrajectory := firstTrajectory) (secondTrajectory := secondTrajectory)
    (firstRegret := firstRegret) (secondRegret := secondRegret)
  · intro trajectory second
    exact Learning.HumanFeedback.policyPreference_timeAveragedPolicy_left
      contextLaw preference trajectory second
  · intro first trajectory
    exact Learning.HumanFeedback.policyPreference_timeAveragedPolicy_right
      contextLaw preference first trajectory
  · exact hfirstRegret
  · exact hsecondRegret

/-- The exact duality-gap form of the finite preference-game regret bound. -/
theorem preferenceGame_empiricalAverage_externalRegret_dualityGapAtMost
    {Time Context Response : Type*}
    [Fintype Time] [DecidableEq Time] [Nonempty Time]
    [Fintype Context] [DecidableEq Context]
    [Fintype Response] [DecidableEq Response]
    (contextLaw : PMF Context)
    (preference : Learning.HumanFeedback.PairwisePreference Context Response)
    (firstTrajectory secondTrajectory :
      Time → Learning.HumanFeedback.FinitePolicy Context Response)
    (firstRegret secondRegret : ℝ)
    (hfirstRegret : ∀ firstAlternative,
      pmfExp (uniformPMF Time) (fun time =>
        preferenceGamePayoff contextLaw preference firstAlternative (secondTrajectory time) -
          preferenceGamePayoff contextLaw preference (firstTrajectory time)
            (secondTrajectory time)) ≤ firstRegret)
    (hsecondRegret : ∀ secondAlternative,
      pmfExp (uniformPMF Time) (fun time =>
        preferenceGamePayoff contextLaw preference (firstTrajectory time)
            (secondTrajectory time) -
          preferenceGamePayoff contextLaw preference (firstTrajectory time)
            secondAlternative) ≤ secondRegret) :
    HasDualityGapAtMost (preferenceGamePayoff contextLaw preference)
      (firstRegret + secondRegret)
      (Learning.HumanFeedback.timeAveragedPolicy firstTrajectory)
      (Learning.HumanFeedback.timeAveragedPolicy secondTrajectory) := by
  apply empiricalAverage_externalRegret_dualityGapAtMost
    (average := Learning.HumanFeedback.timeAveragedPolicy)
    (payoff := preferenceGamePayoff contextLaw preference)
    (firstTrajectory := firstTrajectory) (secondTrajectory := secondTrajectory)
    (firstRegret := firstRegret) (secondRegret := secondRegret)
  · intro trajectory second
    exact Learning.HumanFeedback.policyPreference_timeAveragedPolicy_left
      contextLaw preference trajectory second
  · intro first trajectory
    exact Learning.HumanFeedback.policyPreference_timeAveragedPolicy_right
      contextLaw preference first trajectory
  · exact hfirstRegret
  · exact hsecondRegret

/--
In an antisymmetric constant-sum preference game, a two-policy duality-gap
bound makes the first policy alone an approximate symmetric equilibrium, with
exactly twice the original gap.  This is the extra algebraic step used when
Wang--Liu--Jin output only the first adversarial learner's average policy.
-/
theorem preferenceGame_first_self_dualityGapAtMost_of_pair
    {Context Response : Type*}
    [Fintype Context] [DecidableEq Context]
    [Fintype Response] [DecidableEq Response]
    (contextLaw : PMF Context)
    (preference : Learning.HumanFeedback.PairwisePreference Context Response)
    (first second : Learning.HumanFeedback.FinitePolicy Context Response)
    (approximation : ℝ)
    (hgap : HasDualityGapAtMost (preferenceGamePayoff contextLaw preference)
      approximation first second) :
    HasDualityGapAtMost (preferenceGamePayoff contextLaw preference)
      (2 * approximation) first first := by
  intro firstAlternative secondAlternative
  have hfirst := hgap second firstAlternative
  have hsecond := hgap second secondAlternative
  have hself := preferenceGamePayoff_self contextLaw preference second
  have hswap := preferenceGamePayoff_add_swap contextLaw preference first firstAlternative
  linarith

/--
At zero duality gap, both policies in a saddle pair are exact symmetric
preference-game equilibria.  This is the finite-game content of the paper's
restricted-Nash-to-von-Neumann-winner proposition.
-/
theorem preferenceGame_pair_zeroDualityGap_both_self
    {Context Response : Type*}
    [Fintype Context] [DecidableEq Context]
    [Fintype Response] [DecidableEq Response]
    (contextLaw : PMF Context)
    (preference : Learning.HumanFeedback.PairwisePreference Context Response)
    (first second : Learning.HumanFeedback.FinitePolicy Context Response)
    (hgap : HasDualityGapAtMost (preferenceGamePayoff contextLaw preference)
      0 first second) :
    HasDualityGapAtMost (preferenceGamePayoff contextLaw preference) 0 first first ∧
      HasDualityGapAtMost (preferenceGamePayoff contextLaw preference) 0 second second := by
  constructor
  · simpa using preferenceGame_first_self_dualityGapAtMost_of_pair
      contextLaw preference first second 0 hgap
  · intro firstAlternative secondAlternative
    have hpivot := hgap first first
    have hfirst := hgap firstAlternative second
    have hsecond := hgap secondAlternative second
    have hself := preferenceGamePayoff_self contextLaw preference first
    have hswap := preferenceGamePayoff_add_swap contextLaw preference
      second secondAlternative
    linarith

/--
Source-shaped no-regret conclusion for the first empirical average policy:
its symmetric preference-game duality gap is bounded by twice the sum of the
two average external-regret bounds.
-/
theorem preferenceGame_firstEmpiricalAverage_externalRegret_selfDualityGapAtMost
    {Time Context Response : Type*}
    [Fintype Time] [DecidableEq Time] [Nonempty Time]
    [Fintype Context] [DecidableEq Context]
    [Fintype Response] [DecidableEq Response]
    (contextLaw : PMF Context)
    (preference : Learning.HumanFeedback.PairwisePreference Context Response)
    (firstTrajectory secondTrajectory :
      Time → Learning.HumanFeedback.FinitePolicy Context Response)
    (firstRegret secondRegret : ℝ)
    (hfirstRegret : ∀ firstAlternative,
      pmfExp (uniformPMF Time) (fun time =>
        preferenceGamePayoff contextLaw preference firstAlternative (secondTrajectory time) -
          preferenceGamePayoff contextLaw preference (firstTrajectory time)
            (secondTrajectory time)) ≤ firstRegret)
    (hsecondRegret : ∀ secondAlternative,
      pmfExp (uniformPMF Time) (fun time =>
        preferenceGamePayoff contextLaw preference (firstTrajectory time)
            (secondTrajectory time) -
          preferenceGamePayoff contextLaw preference (firstTrajectory time)
            secondAlternative) ≤ secondRegret) :
    HasDualityGapAtMost (preferenceGamePayoff contextLaw preference)
      (2 * (firstRegret + secondRegret))
      (Learning.HumanFeedback.timeAveragedPolicy firstTrajectory)
      (Learning.HumanFeedback.timeAveragedPolicy firstTrajectory) := by
  exact preferenceGame_first_self_dualityGapAtMost_of_pair contextLaw preference
    (Learning.HumanFeedback.timeAveragedPolicy firstTrajectory)
    (Learning.HumanFeedback.timeAveragedPolicy secondTrajectory)
    (firstRegret + secondRegret)
    (preferenceGame_empiricalAverage_externalRegret_dualityGapAtMost
      contextLaw preference firstTrajectory secondTrajectory firstRegret secondRegret
      hfirstRegret hsecondRegret)

/--
For an antisymmetric constant-sum preference game, mixing the two empirical
average policies converts the two-player saddle guarantee into one approximate
maximal lottery.  This does not require the two learners to have identical
trajectories.
-/
theorem preferenceGame_empiricalAverage_externalRegret_approximateMaximalLottery
    {Time Context Response : Type*}
    [Fintype Time] [DecidableEq Time] [Nonempty Time]
    [Fintype Context] [DecidableEq Context]
    [Fintype Response] [DecidableEq Response]
    (contextLaw : PMF Context)
    (preference : Learning.HumanFeedback.PairwisePreference Context Response)
    (firstTrajectory secondTrajectory : Time → Learning.HumanFeedback.FinitePolicy Context Response)
    (firstRegret secondRegret : ℝ)
    (hfirstRegret : ∀ firstAlternative,
      pmfExp (uniformPMF Time) (fun time =>
        preferenceGamePayoff contextLaw preference firstAlternative (secondTrajectory time) -
          preferenceGamePayoff contextLaw preference (firstTrajectory time)
            (secondTrajectory time)) ≤ firstRegret)
    (hsecondRegret : ∀ secondAlternative,
      pmfExp (uniformPMF Time) (fun time =>
        preferenceGamePayoff contextLaw preference (firstTrajectory time)
            (secondTrajectory time) -
          preferenceGamePayoff contextLaw preference (firstTrajectory time)
            secondAlternative) ≤ secondRegret) :
    IsApproximateMaximalLottery (firstRegret + secondRegret) contextLaw preference
      (Learning.HumanFeedback.binaryMixturePolicy (1 / 2 : NNReal) (by norm_num)
        (Learning.HumanFeedback.timeAveragedPolicy firstTrajectory)
        (Learning.HumanFeedback.timeAveragedPolicy secondTrajectory)) := by
  apply
    (isApproximatePreferenceGameEquilibrium_iff_isApproximateMaximalLottery
      (firstRegret + secondRegret) contextLaw preference
      (Learning.HumanFeedback.binaryMixturePolicy (1 / 2 : NNReal) (by norm_num)
        (Learning.HumanFeedback.timeAveragedPolicy firstTrajectory)
        (Learning.HumanFeedback.timeAveragedPolicy secondTrajectory))).mp
  unfold IsApproximatePreferenceGameEquilibrium
  intro alternative
  have hsaddle := preferenceGame_empiricalAverage_externalRegret_approximateSaddle
    contextLaw preference firstTrajectory secondTrajectory firstRegret secondRegret
    hfirstRegret hsecondRegret
  have hfirst := hsaddle.1 alternative
  have hsecond := hsaddle.2 alternative
  have hswap := preferenceGamePayoff_add_swap contextLaw preference alternative
    (Learning.HumanFeedback.timeAveragedPolicy secondTrajectory)
  have hhalf : ((1 / 2 : NNReal) : ℝ) = (1 / 2 : ℝ) := by norm_num
  have hmixture := preferenceGamePayoff_binaryMixturePolicy_left contextLaw preference
    (1 / 2 : NNReal) (by norm_num)
    (Learning.HumanFeedback.timeAveragedPolicy firstTrajectory)
    (Learning.HumanFeedback.timeAveragedPolicy secondTrajectory) alternative
  rw [hhalf] at hmixture
  rw [hmixture]
  linarith

end PreferenceGame
end GameTheory
end AppliedModelingLib
