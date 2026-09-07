import AppliedModelingLib.Learning.HumanFeedback.Policy

/-!
# Finite pairwise preferences

This module gives the paper-independent finite interface for a preference
probability over ordered response pairs.  Validity is carried by the
`PairwisePreference` structure so downstream loss and game definitions cannot
silently use probabilities outside `[0, 1]` or violate complementarity.

## Main declarations

- `PairwisePreference`
- `policyPreference`
- `policyPreference_add_swap`
- `PairwiseObservation` and `PairwiseDataset`
-/

namespace AppliedModelingLib
namespace Learning
namespace HumanFeedback

/-- A valid probability that one response is preferred to another in a context. -/
structure PairwisePreference (Context Response : Type*) where
  /-- Probability that the first response is preferred to the second. -/
  prob : Context → Response → Response → ℝ
  nonneg : ∀ context first second, 0 ≤ prob context first second
  le_one : ∀ context first second, prob context first second ≤ 1
  complementary : ∀ context first second,
    prob context first second + prob context second first = 1

/-- Valid pairwise preferences are determined by their probability functions. -/
theorem PairwisePreference.ext {Context Response : Type*}
    (first second : PairwisePreference Context Response)
    (hprob : first.prob = second.prob) : first = second := by
  cases first
  cases second
  cases hprob
  rfl

/--
The probability that a response drawn from `first` is preferred to an
independent response drawn from `second`, averaged over contexts.
-/
noncomputable def policyPreference
    {Context Response : Type*} [Fintype Context] [DecidableEq Context]
    [Fintype Response] [DecidableEq Response]
    (contextLaw : PMF Context) (preference : PairwisePreference Context Response)
    (first second : FinitePolicy Context Response) : ℝ :=
  pmfExp contextLaw fun context =>
    pmfPairExp (first context) (second context) (preference.prob context)

/-- Swapping the two policies complements their policy-level preference probability. -/
theorem policyPreference_add_swap
    {Context Response : Type*} [Fintype Context] [DecidableEq Context]
    [Fintype Response] [DecidableEq Response]
    (contextLaw : PMF Context) (preference : PairwisePreference Context Response)
    (first second : FinitePolicy Context Response) :
    policyPreference contextLaw preference first second +
        policyPreference contextLaw preference second first = 1 := by
  unfold policyPreference
  rw [← pmfExp_add, ← pmfExp_const contextLaw 1]
  refine pmfExp_congr contextLaw fun context => ?_
  rw [pmfPairExp_swap (second context) (first context) (preference.prob context)]
  rw [← pmfPairExp_add]
  calc
    pmfPairExp (first context) (second context)
        (fun left right =>
          preference.prob context left right + preference.prob context right left) =
        pmfPairExp (first context) (second context) (fun _ _ => 1) := by
          unfold pmfPairExp
          refine pmfExp_congr (first context) fun left => ?_
          refine pmfExp_congr (second context) fun right => ?_
          exact preference.complementary context left right
    _ = 1 := by simp [pmfPairExp]

/-- Policy-level preference is affine in the first policy. -/
theorem policyPreference_binaryMixturePolicy_left
    {Context Response : Type*} [Fintype Context] [DecidableEq Context]
    [Fintype Response] [DecidableEq Response]
    (contextLaw : PMF Context) (preference : PairwisePreference Context Response)
    (p : NNReal) (hp : p ≤ 1)
    (selected unselected opponent : FinitePolicy Context Response) :
    policyPreference contextLaw preference
        (binaryMixturePolicy p hp selected unselected) opponent =
      p.toReal * policyPreference contextLaw preference selected opponent +
        (1 - p.toReal) * policyPreference contextLaw preference unselected opponent := by
  unfold policyPreference binaryMixturePolicy
  calc
    pmfExp contextLaw (fun context =>
        pmfPairExp (binaryMixturePMF p hp (selected context) (unselected context))
          (opponent context) (preference.prob context)) =
      pmfExp contextLaw (fun context =>
        p.toReal * pmfPairExp (selected context) (opponent context) (preference.prob context) +
          (1 - p.toReal) *
            pmfPairExp (unselected context) (opponent context) (preference.prob context)) := by
        refine pmfExp_congr contextLaw fun context => ?_
        exact pmfPairExp_binaryMixturePMF_left p hp
          (selected context) (unselected context) (opponent context) (preference.prob context)
    _ = p.toReal * pmfExp contextLaw (fun context =>
          pmfPairExp (selected context) (opponent context) (preference.prob context)) +
        (1 - p.toReal) * pmfExp contextLaw (fun context =>
          pmfPairExp (unselected context) (opponent context) (preference.prob context)) := by
          rw [pmfExp_add, pmfExp_const_mul, pmfExp_const_mul]

/-- Policy-level preference is affine in the second policy. -/
theorem policyPreference_binaryMixturePolicy_right
    {Context Response : Type*} [Fintype Context] [DecidableEq Context]
    [Fintype Response] [DecidableEq Response]
    (contextLaw : PMF Context) (preference : PairwisePreference Context Response)
    (p : NNReal) (hp : p ≤ 1)
    (first selected unselected : FinitePolicy Context Response) :
    policyPreference contextLaw preference first
        (binaryMixturePolicy p hp selected unselected) =
      p.toReal * policyPreference contextLaw preference first selected +
        (1 - p.toReal) * policyPreference contextLaw preference first unselected := by
  unfold policyPreference binaryMixturePolicy
  calc
    pmfExp contextLaw (fun context =>
        pmfPairExp (first context)
          (binaryMixturePMF p hp (selected context) (unselected context))
          (preference.prob context)) =
      pmfExp contextLaw (fun context =>
        p.toReal * pmfPairExp (first context) (selected context) (preference.prob context) +
          (1 - p.toReal) *
            pmfPairExp (first context) (unselected context) (preference.prob context)) := by
        refine pmfExp_congr contextLaw fun context => ?_
        exact pmfPairExp_binaryMixturePMF_right p hp
          (first context) (selected context) (unselected context) (preference.prob context)
    _ = p.toReal * pmfExp contextLaw (fun context =>
          pmfPairExp (first context) (selected context) (preference.prob context)) +
        (1 - p.toReal) * pmfExp contextLaw (fun context =>
          pmfPairExp (first context) (unselected context) (preference.prob context)) := by
          rw [pmfExp_add, pmfExp_const_mul, pmfExp_const_mul]

/--
Evaluating a fixed opponent against an empirical policy average is the uniform
average of its per-round preference payoffs.
-/
theorem policyPreference_timeAveragedPolicy_left
    {Time Context Response : Type*}
    [Fintype Time] [DecidableEq Time] [Nonempty Time]
    [Fintype Context] [DecidableEq Context]
    [Fintype Response] [DecidableEq Response]
    (contextLaw : PMF Context) (preference : PairwisePreference Context Response)
    (trajectory : Time → FinitePolicy Context Response)
    (opponent : FinitePolicy Context Response) :
    policyPreference contextLaw preference (timeAveragedPolicy trajectory) opponent =
      pmfExp (uniformPMF Time)
        (fun time => policyPreference contextLaw preference (trajectory time) opponent) := by
  change
    pmfExp contextLaw (fun context =>
      pmfPairExp ((uniformPMF Time).bind fun time => trajectory time context)
        (opponent context) (preference.prob context)) =
      pmfExp (uniformPMF Time) (fun time =>
        pmfExp contextLaw (fun context =>
          pmfPairExp (trajectory time context) (opponent context)
            (preference.prob context)))
  calc
    _ = pmfExp contextLaw (fun context =>
        pmfExp (uniformPMF Time) (fun time =>
          pmfPairExp (trajectory time context) (opponent context)
            (preference.prob context))) := by
          refine pmfExp_congr contextLaw ?_
          intro context
          unfold pmfPairExp
          exact pmfExp_bind (uniformPMF Time) (fun time => trajectory time context) _
    _ = _ := by
      exact pmfPairExp_swap contextLaw (uniformPMF Time)
        (fun context time =>
          pmfPairExp (trajectory time context) (opponent context)
            (preference.prob context))

/--
Evaluating an empirical policy average against a fixed opponent is the uniform
average of its per-round preference payoffs.
-/
theorem policyPreference_timeAveragedPolicy_right
    {Time Context Response : Type*}
    [Fintype Time] [DecidableEq Time] [Nonempty Time]
    [Fintype Context] [DecidableEq Context]
    [Fintype Response] [DecidableEq Response]
    (contextLaw : PMF Context) (preference : PairwisePreference Context Response)
    (first : FinitePolicy Context Response)
    (trajectory : Time → FinitePolicy Context Response) :
    policyPreference contextLaw preference first (timeAveragedPolicy trajectory) =
      pmfExp (uniformPMF Time)
        (fun time => policyPreference contextLaw preference first (trajectory time)) := by
  change
    pmfExp contextLaw (fun context =>
      pmfPairExp (first context)
        ((uniformPMF Time).bind fun time => trajectory time context)
        (preference.prob context)) =
      pmfExp (uniformPMF Time) (fun time =>
        pmfExp contextLaw (fun context =>
          pmfPairExp (first context) (trajectory time context)
            (preference.prob context)))
  calc
    _ = pmfExp contextLaw (fun context =>
        pmfExp (uniformPMF Time) (fun time =>
          pmfPairExp (first context) (trajectory time context)
            (preference.prob context))) := by
          refine pmfExp_congr contextLaw ?_
          intro context
          calc
            pmfPairExp (first context)
                ((uniformPMF Time).bind fun time => trajectory time context)
                (preference.prob context) =
                pmfExp (first context) (fun firstResponse =>
                  pmfExp (uniformPMF Time) (fun time =>
                    pmfExp (trajectory time context) (fun secondResponse =>
                      preference.prob context firstResponse secondResponse))) := by
                    unfold pmfPairExp
                    simp_rw [pmfExp_bind]
            _ = pmfExp (uniformPMF Time) (fun time =>
                pmfPairExp (first context) (trajectory time context)
                  (preference.prob context)) := by
                    exact pmfPairExp_swap (first context) (uniformPMF Time)
                      (fun firstResponse time =>
                        pmfExp (trajectory time context) (fun secondResponse =>
                          preference.prob context firstResponse secondResponse))
    _ = _ := by
      exact pmfPairExp_swap contextLaw (uniformPMF Time)
        (fun context time =>
          pmfPairExp (first context) (trajectory time context)
            (preference.prob context))

/-- One observed ordered pair, with `chosen` recorded as the preferred response. -/
structure PairwiseObservation (Context Response : Type*) where
  context : Context
  chosen : Response
  rejected : Response

/-- A finite collection of observed pairwise preferences. -/
abbrev PairwiseDataset (Context Response : Type*) :=
  List (PairwiseObservation Context Response)

end HumanFeedback
end Learning
end AppliedModelingLib
