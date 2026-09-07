import LG24ServiceLevelAgreements.SLA2026Model
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Reusable response-tail-to-SLA arithmetic

This module retains the scalar tail-to-SLA implications used by older review
surfaces.  Its historical `Cited` names mean that the input tail inequality is
supplied abstractly to these generic algebraic lemmas.  They are not the
active paper-facing queueing route: `SLA2026StationaryTailSLA` proves the
selected-Palm tail from the literal source construction and then reuses the
arithmetic below.

The definitions here deliberately do not package path measurability, GPS
dynamics, or a backlog predicate into an opaque model assumption.
-/

namespace LG24ServiceLevelAgreements

noncomputable section

/--
Compatibility predicate for an abstract response-tail fact.  It is used only
by generic downstream arithmetic; the active paper-facing tail theorem is the
constructed selected-Palm result in `SLA2026StationaryTailSLA`.
-/
def SLA2026CitedGPSResponseTail
    (responseTail guaranteedSlack delay : ℝ) : Prop :=
  responseTail ≤ Real.exp (-(guaranteedSlack * delay))

/-- The source's sufficient SLA inequality in its displayed `log alpha` form. -/
def sla2026SufficientSLAConstraint
    (guaranteedSlack delay alpha : ℝ) : Prop :=
  0 ≤ guaranteedSlack * delay + Real.log alpha

/-- The source's displayed all-request response *rate-fraction* expression.
It is the admitted intensity share times the admitted-request timely-response
probability.  A pathwise raw-arrival or empirical-frequency interpretation
would additionally require a marked-thinning/scheduler coupling and is not
encoded by this scalar definition. -/
def sla2026AllRequestResponseFraction
    (arrival admitted admittedTailProbability : ℝ) : ℝ :=
  admitted / arrival * (1 - admittedTailProbability)

/--
Any supplied exponential response-tail estimate and the printed sufficient
constraint imply the admitted-request tail target.  This is generic algebra,
not the active queueing construction.
-/
theorem sla2026_cited_gps_tail_implies_admitted_sla
    {responseTail guaranteedSlack delay alpha : ℝ}
    (hcited : SLA2026CitedGPSResponseTail responseTail guaranteedSlack delay)
    (halpha : 0 < alpha)
    (hsla : sla2026SufficientSLAConstraint guaranteedSlack delay alpha) :
    responseTail ≤ alpha := by
  unfold SLA2026CitedGPSResponseTail at hcited
  calc
    responseTail ≤ Real.exp (-(guaranteedSlack * delay)) := hcited
    _ ≤ Real.exp (Real.log alpha) := by
      apply Real.exp_le_exp.mpr
      unfold sla2026SufficientSLAConstraint at hsla
      linarith
    _ = alpha := Real.exp_log halpha

/--
Independent admission transfers an admitted-request tail target to the
all-request rate-fraction expression printed in the source.
-/
theorem sla2026_admitted_tail_implies_all_request_sla
    {arrival admitted responseTail alpha : ℝ}
    (harrival : 0 < arrival)
    (hadmitted : 0 ≤ admitted)
    (htail : responseTail ≤ alpha) :
    admitted / arrival * (1 - alpha) ≤
      sla2026AllRequestResponseFraction arrival admitted responseTail := by
  unfold sla2026AllRequestResponseFraction
  have hratio : 0 ≤ admitted / arrival := div_nonneg hadmitted harrival.le
  nlinarith [mul_le_mul_of_nonneg_left htail hratio]

/--
The complete generic deterministic SLA bridge, conditional on an explicitly
supplied response-tail inequality.
-/
theorem sla2026_cited_gps_tail_implies_all_request_sla
    {arrival admitted responseTail guaranteedSlack delay alpha : ℝ}
    (hcited : SLA2026CitedGPSResponseTail responseTail guaranteedSlack delay)
    (harrival : 0 < arrival)
    (hadmitted : 0 ≤ admitted)
    (halpha : 0 < alpha)
    (hsla : sla2026SufficientSLAConstraint guaranteedSlack delay alpha) :
    admitted / arrival * (1 - alpha) ≤
      sla2026AllRequestResponseFraction arrival admitted responseTail := by
  exact sla2026_admitted_tail_implies_all_request_sla harrival hadmitted
    (sla2026_cited_gps_tail_implies_admitted_sla hcited halpha hsla)

end

end LG24ServiceLevelAgreements
