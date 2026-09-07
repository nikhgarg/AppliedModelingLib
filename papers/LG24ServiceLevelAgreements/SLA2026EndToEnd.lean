import LG24ServiceLevelAgreements.SLA2026Queueing
import LG24ServiceLevelAgreements.SLA2026Reformulation
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Source-level bridge from a fixed-load policy to the printed SLA

The active source uses `a = -log alpha` in its reciprocal-capacity program.
This module keeps that identification visible and proves the elementary
connection from an original-program feasible policy to the sufficient
logarithmic SLA inequality.  The stochastic GPS tail estimate remains the
explicit cited boundary from `SLA2026Queueing`.
-/

namespace LG24ServiceLevelAgreements

noncomputable section

/-- The source reliability parameter `a = -log(alpha)` is positive for the
printed domain `0 < alpha < 1`. -/
theorem sla2026_tail_parameter_pos_of_alpha
    {tail alpha : Real}
    (halpha_pos : 0 < alpha) (halpha_lt_one : alpha < 1)
    (htail : tail = -Real.log alpha) :
    0 < tail := by
  rw [htail]
  exact neg_pos.mpr (Real.log_neg halpha_pos halpha_lt_one)

/-- A feasible original-policy SLA constraint forces positive guaranteed
slack when the source tail parameter is positive. -/
theorem sla2026_original_policy_guaranteed_slack_pos
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    {tail capacity : Real} {admitted : Category → Borough → Real}
    {policy : SLA2026OriginalFixedLoadPolicy Category Borough}
    (hpolicy : SLA2026OriginalFixedLoadFeasible tail capacity admitted policy)
    (htail : 0 < tail) (k : Category) (b : Borough) :
    0 < policy.boroughCapacity b * policy.gpsWeight k b - admitted k b := by
  have hsla : tail ≤
      (policy.boroughCapacity b * policy.gpsWeight k b - admitted k b) *
        policy.delay k b := by
    linarith [hpolicy.sla k b]
  have hproduct : 0 <
      (policy.boroughCapacity b * policy.gpsWeight k b - admitted k b) *
        policy.delay k b :=
    lt_of_lt_of_le htail hsla
  rcases (mul_pos_iff.mp hproduct) with hpos | hneg
  · exact hpos.1
  · linarith [hpolicy.delay_pos k b, hneg.2]

/-- The original fixed-load SLA constraint, after the source identification
`a = -log(alpha)`, is exactly the sufficient logarithmic SLA inequality. -/
theorem sla2026_original_policy_implies_sufficient_sla
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    {tail capacity alpha : Real} {admitted : Category → Borough → Real}
    {policy : SLA2026OriginalFixedLoadPolicy Category Borough}
    (hpolicy : SLA2026OriginalFixedLoadFeasible tail capacity admitted policy)
    (htail : tail = -Real.log alpha) (k : Category) (b : Borough) :
    sla2026SufficientSLAConstraint
      (policy.boroughCapacity b * policy.gpsWeight k b - admitted k b)
      (policy.delay k b) alpha := by
  unfold sla2026SufficientSLAConstraint
  have hsla := hpolicy.sla k b
  rw [htail] at hsla
  linarith

/-- Conditional on the explicit cited GPS tail result, an original feasible
policy meeting the source `a = -log(alpha)` convention gives the all-request
SLA fraction printed in the paper. -/
theorem sla2026_original_policy_cited_tail_implies_all_request_sla
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    {tail capacity alpha responseTail arrival : Real}
    {admitted : Category → Borough → Real}
    {policy : SLA2026OriginalFixedLoadPolicy Category Borough}
    (hpolicy : SLA2026OriginalFixedLoadFeasible tail capacity admitted policy)
    (htail : tail = -Real.log alpha)
    (halpha_pos : 0 < alpha)
    (halpha_lt_one : alpha < 1)
    (k : Category) (b : Borough)
    (hcited : SLA2026CitedGPSResponseTail responseTail
      (policy.boroughCapacity b * policy.gpsWeight k b - admitted k b)
      (policy.delay k b))
    (harrival : 0 < arrival) (hadmitted : 0 ≤ admitted k b) :
    admitted k b / arrival * (1 - alpha) ≤
      sla2026AllRequestResponseFraction arrival (admitted k b) responseTail := by
  have htail_pos :=
    sla2026_tail_parameter_pos_of_alpha halpha_pos halpha_lt_one htail
  have _hslack_pos :=
    sla2026_original_policy_guaranteed_slack_pos hpolicy htail_pos k b
  apply sla2026_cited_gps_tail_implies_all_request_sla hcited harrival hadmitted
    halpha_pos
  exact sla2026_original_policy_implies_sufficient_sla hpolicy htail k b

end

end LG24ServiceLevelAgreements
