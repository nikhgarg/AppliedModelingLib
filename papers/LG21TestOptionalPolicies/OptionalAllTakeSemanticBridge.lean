import LG21TestOptionalPolicies.SequentialEquilibrium

/-!
# Semantic all-taking bridge for LG21 optional reporting

This module records the pre-test part of the repaired Lemma 4.1 argument.
It uses the source-timed Definition 1 interface directly:

* a student chooses whether to take before the score is drawn;
* after a score is realized, reporting is a binary best response; and
* not taking and taking without reporting have the same public-action payoff.

The argument does not inspect a strategy's implementation or assume that an
action set is a cutoff.  A genuinely chosen report action, together with a
strictly increasing score-contingent school estimate, makes every strictly
higher score a reporting action with a strict gain.  Full upper-tail support
of each conditional score law then makes testing strictly preferable for
every latent type.

The bridge is deliberately conditional on the two semantic inputs that the
source PBO construction must establish for a candidate action profile:

1. the score-contingent estimate is strictly increasing; and
2. a report action exists, established by the source bridge from the
   candidate's actual positive branch.

Those inputs must come from literal candidate-action conditional means, not
from an arbitrary value of a conditional distribution on a null history.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib MeasureTheory ProbabilityTheory Set

/-! ## The semantic high-score reporting region -/

/--
An actually chosen report action anchors a strict upper reporting region.

This is only a consequence of the two Definition 1 best-response inequalities
and strict monotonicity of the *score-contingent estimate*.  In particular,
the proof does not assume or derive a cutoff representation for
`reportDecision`.
-/
theorem lg21_optional_high_score_reports_and_strictly_gains
    {Base : Type*}
    {E : LG21OptionalSequentialEquilibriumData ℝ Base ℝ}
    (hEq : lg21OptionalSequentialEquilibrium E) (base : Base)
    (hstrict : StrictMono (E.reportedPayoff base))
    (hactualReport : ∃ score, E.reportDecision base score = true) :
    ∃ anchor : ℝ, ∀ score : ℝ, anchor < score →
      E.reportDecision base score = true ∧
        E.noReportPayoff base < E.reportedPayoff base score := by
  rcases hactualReport with ⟨anchor, hanchorReport⟩
  refine ⟨anchor, ?_⟩
  intro score hscore
  have hanchorBR :=
    (lg21OptionalSequentialEquilibrium_report_bestResponse hEq base).1
      anchor hanchorReport
  have hstrictGain : E.noReportPayoff base < E.reportedPayoff base score :=
    lt_of_le_of_lt hanchorBR (hstrict hscore)
  constructor
  · by_contra hnotReport
    have hnotReportBR :=
      (lg21OptionalSequentialEquilibrium_report_bestResponse hEq base).2
        score hnotReport
    exact (not_le_of_gt hstrictGain) hnotReportBR
  · exact hstrictGain

/-! ## Ex-ante all-taking bridge -/

/--
At a fixed public base profile, source-timed Definition 1 best responses force
all latent skills to take whenever every conditional score law has positive
mass in every strict upper tail and the candidate public-action PBO semantics
provide a strictly increasing estimate with an actual report action.

The conclusion is pointwise because Definition 1's supplied sequential
best-response interface is pointwise.  No action function is classified by
its name, and no cutoff premise is used.  This is the theorem intended for the
LG21 source bridge.
-/
theorem lg21_optional_all_take_at_base_of_strictMono_actual_report_upperTail
    {Base : Type*}
    {E : LG21OptionalSequentialEquilibriumData ℝ Base ℝ}
    (hEq : lg21OptionalSequentialEquilibrium E) (base : Base)
    (hstrict : StrictMono (E.reportedPayoff base))
    (hactualReport : ∃ score, E.reportDecision base score = true)
    (hupperTail : ∀ skill cutoff : ℝ,
      0 < E.testLaw skill base (Set.Ioi cutoff)) :
    ∀ skill : ℝ, E.takeDecision skill base = true := by
  rcases lg21_optional_high_score_reports_and_strictly_gains
      hEq base hstrict hactualReport with ⟨anchor, hhighReport⟩
  intro skill
  by_contra hnotTake
  have htakeBR :=
    (lg21OptionalSequentialEquilibrium_take_bestResponse hEq base).2
      skill hnotTake
  have hpositiveGain :
      0 < E.testLaw skill base
        {score |
          E.reportDecision base score = true ∧
            E.noReportPayoff base < E.reportedPayoff base score} := by
    apply lt_of_lt_of_le (hupperTail skill anchor)
    apply measure_mono
    intro score hscore
    exact hhighReport score hscore
  have htakeStrict :=
    lg21OptionalSequentialTakeExpectedPayoff_gt_noReport_of_positive_strict_gain
      E hEq skill base hpositiveGain
  exact (not_le_of_gt htakeStrict) htakeBR

/--
Uniform version of the semantic all-taking bridge.  Each base profile gets its
own strictly increasing candidate estimate and actual reporting action; no
cross-base payoff comparison is required.
-/
theorem lg21_optional_all_take_of_strictMono_actual_report_upperTail
    {Base : Type*}
    {E : LG21OptionalSequentialEquilibriumData ℝ Base ℝ}
    (hEq : lg21OptionalSequentialEquilibrium E)
    (hstrict : ∀ base, StrictMono (E.reportedPayoff base))
    (hactualReport : ∀ base, ∃ score, E.reportDecision base score = true)
    (hupperTail : ∀ (skill : ℝ) (base : Base) (cutoff : ℝ),
      0 < E.testLaw skill base (Set.Ioi cutoff)) :
    ∀ skill base, E.takeDecision skill base = true := by
  intro skill base
  exact lg21_optional_all_take_at_base_of_strictMono_actual_report_upperTail
    hEq base (hstrict base) (hactualReport base)
    (fun candidateSkill cutoff => hupperTail candidateSkill base cutoff) skill

/--
Gaussian specialization: a nondegenerate additive Gaussian score law has
positive mass in every strict upper tail.  The PBO/source bridge still has to
produce strict monotonicity and an actual report action for the candidate
profile before this theorem can be applied.
-/
theorem lg21_optional_all_take_at_base_gaussian_of_strictMono_actual_report
    {Base : Type*}
    {E : LG21OptionalSequentialEquilibriumData ℝ Base ℝ}
    (hEq : lg21OptionalSequentialEquilibrium E) (base : Base)
    (noiseVariance : NNReal) (hvariance : noiseVariance ≠ 0)
    (htestLaw : ∀ skill, E.testLaw skill base = gaussianReal skill noiseVariance)
    (hstrict : StrictMono (E.reportedPayoff base))
    (hactualReport : ∃ score, E.reportDecision base score = true) :
    ∀ skill : ℝ, E.takeDecision skill base = true := by
  apply lg21_optional_all_take_at_base_of_strictMono_actual_report_upperTail
    hEq base hstrict hactualReport
  intro skill cutoff
  rw [htestLaw skill]
  exact lg21_gaussianReal_Ioi_pos skill cutoff hvariance

end

end LG21TestOptionalPolicies
