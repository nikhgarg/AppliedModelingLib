import GolzHaghtalabYang2025Distortion.Theorem3
import GolzHaghtalabYang2025Distortion.EmpiricalCondorcet

/-!
# IID completion of the multi-comparison Condorcet-loser argument

Appendix E.3 permits arbitrary dependence among the comparisons supplied by
one user.  The stochastic input that matters is therefore a finite *report*
law, sampled independently across users, together with a strictly positive
expected aggregate margin for every ordinary alternative against the hidden
special alternative.  This module discharges the resulting convergence premise
of the source's Condorcet-loser argument without treating convergence itself as
an assumption.
-/

namespace GolzHaghtalabYang2025Distortion

open scoped Topology

open AppliedModelingLib
open AppliedModelingLib.Probability
open AppliedModelingLib.Alignment.Welfare

/--
IID finite reports with positive expected aggregate margins make the hidden
alternative an empirical strict Condorcet loser with probability tending to
one.  Combined with the source's probabilistic Condorcet-loser criterion,
this proves the large-`m` `d ≥ 2` lower bound from those concrete stochastic
primitives.

The report type is deliberately left general: one report can encode all `d`
within-user comparisons and their arbitrary dependence.  The only sampling
independence used here is the iid draw of reports across users.
-/
theorem theorem3_d2_asymptotic_lower_bound_of_iid_positive_margins
    {beta : ℝ} (hbeta : 0 < beta)
    {Report : ℕ → Type*}
    [∀ n, Fintype (Report n)] [∀ n, DecidableEq (Report n)]
    (reportLaw : ∀ n, PMF (Report n))
    (margin : ∀ n, Fin (n + 3) → Fin (n + 3) → Report n → ℝ)
    (rule : ∀ n horizon, (Fin horizon → Report n) → PMF (Fin (n + 3)))
    (hcriterion : ∀ n horizon,
      theorem3ProbabilisticCondorcetLoserCriterion (rule n horizon)
        (fun observation alternative =>
          theorem3IidEmpiricalStrictCondorcetLoser (margin n alternative) alternative observation))
    (hmean : ∀ n : ℕ, ∀ ordinary : {ordinary : Fin (n + 3) // ordinary ≠ (0 : Fin (n + 3))},
      0 < pmfExp (reportLaw n) (margin n (0 : Fin (n + 3)) ordinary.1))
    (delta : ℝ) (hdelta : 0 < delta) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ᶠ horizon : ℕ in Filter.atTop,
      beta / 2 * (1 + Real.exp (-beta)) / (1 - Real.exp (-beta)) - delta <
        theorem3SpecialTypeMass beta (theorem3D2DiagonalEpsilon n) /
          policyAverageUtility
            (theorem3TwoTypePopulation beta (theorem3D2DiagonalEpsilon n) hbeta
              (theorem3D2DiagonalEpsilon_pos n))
            (theorem3ManyAlternativeUtility (theorem3D2DiagonalEpsilon n)
              (theorem3D2DiagonalXi n) (0 : Fin (n + 3)))
            (theorem3ObservationSelectionLaw
              (theorem3IidUserReportBatchLaw (reportLaw n) horizon)
              (rule n horizon)) := by
  classical
  refine theorem3_d2_asymptotic_lower_bound_of_condorcetCertification hbeta
    (fun n horizon => theorem3IidUserReportBatchLaw (reportLaw n) horizon)
    rule
    (fun _n _horizon observation alternative =>
      theorem3IidEmpiricalStrictCondorcetLoser (margin _n alternative) alternative observation)
    hcriterion ?_ delta hdelta
  intro n
  have hfailure := theorem3_iidEmpiricalCondorcetFailure_tendsto_zero_of_positive_means
    (reportLaw n) (margin n (0 : Fin (n + 3))) (0 : Fin (n + 3)) (hmean n)
  refine hfailure.congr' ?_
  filter_upwards with horizon
  apply pmfProb_congr
  intro observation
  exact theorem3IidEmpiricalCondorcetFailure_iff_not_strict
    (margin n (0 : Fin (n + 3))) (0 : Fin (n + 3)) observation

end GolzHaghtalabYang2025Distortion
