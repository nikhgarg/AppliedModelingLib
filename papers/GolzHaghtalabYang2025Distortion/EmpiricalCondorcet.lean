import AppliedModelingLib.Foundations.Probability.IIDLargeDeviations
import Mathlib.Tactic

/-!
# IID empirical Condorcet certificates

The multi-comparison branch of Appendix E.3 only needs a finite user report to
provide a positive expected comparison margin for every opponent of a proposed
Condorcet loser. A report may contain an arbitrarily correlated tuple of the
user's comparisons; iid sampling is imposed only across users. This module
turns finite iid left-tail certificates for those per-user margins into the
vanishing empirical Condorcet-certificate error used by Theorem 3.
-/

namespace GolzHaghtalabYang2025Distortion

open scoped Topology

open AppliedModelingLib
open AppliedModelingLib.Probability

/-- The source's iid batch law obtained by independently sampling user reports. -/
noncomputable def theorem3IidUserReportBatchLaw
    {Report : Type*} [Fintype Report] [DecidableEq Report]
    (reportLaw : PMF Report) (horizon : ℕ) : PMF (Fin horizon → Report) :=
  AppliedModelingLib.pmfProduct (Fin horizon) Report reportLaw

/--
A batch certifies `special` as an empirical strict Condorcet loser when every
other alternative has a strictly positive aggregate report margin against it.
The score for an ordinary alternative is allowed to encode all comparisons
made by one user, including arbitrary correlation within that user report.
-/
def theorem3IidEmpiricalStrictCondorcetLoser
    {Report Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (margin : Alternative → Report → ℝ) (special : Alternative) {horizon : ℕ}
    (sample : Fin horizon → Report) : Prop :=
  ∀ ordinary, ordinary ≠ special →
    0 < finiteIidScoreSum (margin ordinary) sample

/--
The explicit finite failure event for the empirical Condorcet certificate.
Writing the failure as an existential over alternatives avoids making a
classical decidability choice part of the probability expression.
-/
abbrev theorem3IidEmpiricalCondorcetFailure
    {Report Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (margin : Alternative → Report → ℝ) (special : Alternative) {horizon : ℕ}
    (sample : Fin horizon → Report) : Prop :=
  ∃ ordinary : {ordinary : Alternative // ordinary ≠ special},
    finiteIidScoreSum (margin ordinary.1) sample ≤ 0

/-- The explicit finite failure event is exactly the negation of certification. -/
theorem theorem3IidEmpiricalCondorcetFailure_iff_not_strict
    {Report Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (margin : Alternative → Report → ℝ) (special : Alternative) {horizon : ℕ}
    (sample : Fin horizon → Report) :
    theorem3IidEmpiricalCondorcetFailure margin special sample ↔
      ¬ theorem3IidEmpiricalStrictCondorcetLoser margin special sample := by
  classical
  constructor
  · rintro ⟨ordinary, htail⟩ hcertificate
    exact not_lt_of_ge htail (hcertificate ordinary.1 ordinary.2)
  · intro hnot
    by_contra hnone
    apply hnot
    intro ordinary hordinary
    by_contra hpositive
    apply hnone
    refine ⟨⟨ordinary, hordinary⟩, le_of_not_gt hpositive⟩

/--
The failure probability of the iid empirical certificate is bounded by the
finite union of its individual ordinary-versus-special nonpositive-margin
tails.
-/
theorem theorem3_iidEmpiricalCondorcetFailure_le_sum
    {Report Alternative : Type*} [Fintype Report] [DecidableEq Report]
    [Fintype Alternative] [DecidableEq Alternative]
    (reportLaw : PMF Report) (margin : Alternative → Report → ℝ)
    (special : Alternative) (horizon : ℕ) :
    AppliedModelingLib.pmfProb (theorem3IidUserReportBatchLaw reportLaw horizon)
      (fun sample => theorem3IidEmpiricalCondorcetFailure margin special sample) ≤
      ∑ ordinary : {ordinary : Alternative // ordinary ≠ special},
        finiteIidScoreLeftTailProb reportLaw (margin ordinary.1) 0 horizon := by
  classical
  let bad : {ordinary : Alternative // ordinary ≠ special} → (Fin horizon → Report) → Prop :=
    fun ordinary sample => finiteIidScoreSum (margin ordinary.1) sample ≤ 0
  change AppliedModelingLib.pmfProb (theorem3IidUserReportBatchLaw reportLaw horizon)
      (fun sample => ∃ ordinary : {ordinary : Alternative // ordinary ≠ special},
        bad ordinary sample) ≤ _
  have hunion := AppliedModelingLib.pmfProb_exists_mem_le_sum
    (μ := theorem3IidUserReportBatchLaw reportLaw horizon)
    (s := Finset.univ) (p := bad)
  simpa [bad, theorem3IidUserReportBatchLaw, finiteIidScoreLeftTailProb] using hunion

/--
Finite iid tail convergence for every ordinary alternative implies that the
empirical Condorcet-loser certificate fails with vanishing probability.
-/
theorem theorem3_iidEmpiricalCondorcetFailure_tendsto_zero
    {Report Alternative : Type*} [Fintype Report] [DecidableEq Report]
    [Fintype Alternative] [DecidableEq Alternative]
    (reportLaw : PMF Report) (margin : Alternative → Report → ℝ)
    (special : Alternative)
    (htail : ∀ ordinary : {ordinary : Alternative // ordinary ≠ special},
      Filter.Tendsto
        (fun horizon => finiteIidScoreLeftTailProb reportLaw (margin ordinary.1) 0 horizon)
        Filter.atTop (𝓝 0)) :
    Filter.Tendsto
      (fun horizon => AppliedModelingLib.pmfProb (theorem3IidUserReportBatchLaw reportLaw horizon)
        (fun sample => theorem3IidEmpiricalCondorcetFailure margin special sample))
      Filter.atTop (𝓝 0) := by
  let tailSum : ℕ → ℝ := fun horizon =>
    ∑ ordinary : {ordinary : Alternative // ordinary ≠ special},
      finiteIidScoreLeftTailProb reportLaw (margin ordinary.1) 0 horizon
  have htailSum : Filter.Tendsto tailSum Filter.atTop (𝓝 0) := by
    simpa [tailSum] using
      tendsto_finset_sum (Finset.univ : Finset {ordinary : Alternative // ordinary ≠ special})
        (fun ordinary _ => htail ordinary)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds htailSum ?_ ?_
  · filter_upwards with horizon
    exact AppliedModelingLib.pmfProb_nonneg (theorem3IidUserReportBatchLaw reportLaw horizon)
      (fun sample => theorem3IidEmpiricalCondorcetFailure margin special sample)
  · filter_upwards with horizon
    exact theorem3_iidEmpiricalCondorcetFailure_le_sum reportLaw margin special horizon

/--
Positive-rate finite iid tail certificates for all ordinary alternatives
discharge the convergence premise above. This is the exact interface required
to connect a Bernstein/Chernoff proof for the source's finite user reports to
the `d ≥ 2` behavioral lower bound.
-/
theorem theorem3_iidEmpiricalCondorcetFailure_tendsto_zero_of_tailExp
    {Report Alternative : Type*} [Fintype Report] [DecidableEq Report]
    [Fintype Alternative] [DecidableEq Alternative]
    (reportLaw : PMF Report) (margin : Alternative → Report → ℝ)
    (special : Alternative)
    (htail : ∀ ordinary : {ordinary : Alternative // ordinary ≠ special},
      ∃ rate : ℝ, 0 < rate ∧
        HasExpUpperBoundWithConst
          (fun horizon => finiteIidScoreLeftTailProb reportLaw (margin ordinary.1) 0 horizon)
          rate) :
    Filter.Tendsto
      (fun horizon => AppliedModelingLib.pmfProb (theorem3IidUserReportBatchLaw reportLaw horizon)
        (fun sample => theorem3IidEmpiricalCondorcetFailure margin special sample))
      Filter.atTop (𝓝 0) := by
  apply theorem3_iidEmpiricalCondorcetFailure_tendsto_zero reportLaw margin special
  intro ordinary
  obtain ⟨rate, hrate, hbound⟩ := htail ordinary
  exact hbound.tendsto_zero_of_pos_rate hrate

/--
For finite reports, strict positivity of each ordinary-versus-special expected
one-user margin supplies the positive exponential certificate used above.  No
independence is required among comparisons within a report: all such
dependence is already contained in `reportLaw`.
-/
theorem theorem3_iidEmpiricalCondorcetFailure_tendsto_zero_of_positive_means
    {Report Alternative : Type*} [Fintype Report] [DecidableEq Report]
    [Fintype Alternative] [DecidableEq Alternative]
    (reportLaw : PMF Report) (margin : Alternative → Report → ℝ)
    (special : Alternative)
    (hmean : ∀ ordinary : {ordinary : Alternative // ordinary ≠ special},
      0 < AppliedModelingLib.pmfExp reportLaw (margin ordinary.1)) :
    Filter.Tendsto
      (fun horizon => AppliedModelingLib.pmfProb (theorem3IidUserReportBatchLaw reportLaw horizon)
        (fun sample => theorem3IidEmpiricalCondorcetFailure margin special sample))
      Filter.atTop (𝓝 0) := by
  apply theorem3_iidEmpiricalCondorcetFailure_tendsto_zero_of_tailExp
    reportLaw margin special
  intro ordinary
  exact finiteIidScoreLeftTail_exists_pos_expUpperBoundWithConst_of_pmfExp_pos
    reportLaw (margin ordinary.1) (hmean ordinary)

end GolzHaghtalabYang2025Distortion
