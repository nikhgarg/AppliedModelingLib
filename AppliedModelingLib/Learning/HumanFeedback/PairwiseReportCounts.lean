import AppliedModelingLib.Foundations.Probability.FiniteIIDCoverage
import AppliedModelingLib.Learning.HumanFeedback.PairwiseCount
import AppliedModelingLib.Learning.HumanFeedback.PairwiseCountExistence

/-!
# Aggregating binary pairwise reports into likelihood counts

One binary report records an ordered displayed pair and whether its first
member won.  This module retains both orientations when it aggregates a finite
report batch into the directed winner-count dataset used by the finite
pairwise-MLE theory.  In particular, it does not replace a random comparison
design by a balanced deterministic design.

## Main declarations

- `PairwiseCountDataset.ofBinaryReports`
- `PairwiseCountDataset.everyComponentStronglyConnected_of_allBinaryReportWins`
- `PairwiseCountDataset.directedWinFailureProbability_tendsto_zero`
- `PairwiseCountDataset.noPairwiseMLEProbability_tendsto_zero`
-/

namespace AppliedModelingLib
namespace Learning
namespace HumanFeedback

open scoped BigOperators Topology

/-- A displayed ordered pair with the Boolean outcome `true` exactly when the
first displayed alternative wins. -/
abbrev BinaryPairwiseReport.{u} (Alternative : Type u) : Type u :=
  (Alternative × Alternative) × Bool

/-- A binary report contributes one directed win from `winner` to `loser`.
Both display orientations are retained, while diagonal displays are excluded
from the pairwise-count likelihood as required by its source model. -/
def binaryReportWin {Alternative : Type*} [DecidableEq Alternative]
    (winner loser : Alternative) (report : BinaryPairwiseReport Alternative) : Prop :=
  winner ≠ loser ∧
    ((report.1.1 = winner ∧ report.1.2 = loser ∧ report.2 = true) ∨
      (report.1.1 = loser ∧ report.1.2 = winner ∧ report.2 = false))

/-- The direct displayed orientation with a true outcome records the indicated
winner. -/
theorem binaryReportWin_direct_true {Alternative : Type*} [DecidableEq Alternative]
    {winner loser : Alternative} (hneq : winner ≠ loser) :
    binaryReportWin winner loser ((winner, loser), true) := by
  exact ⟨hneq, Or.inl ⟨rfl, rfl, rfl⟩⟩

/-- The reversed displayed orientation with a false outcome records the same
directed winner. -/
theorem binaryReportWin_reverse_false {Alternative : Type*} [DecidableEq Alternative]
    {winner loser : Alternative} (hneq : winner ≠ loser) :
    binaryReportWin winner loser ((loser, winner), false) := by
  exact ⟨hneq, Or.inr ⟨rfl, rfl, rfl⟩⟩

namespace PairwiseCountDataset

/-- The direct displayed orientation of a directed win. -/
abbrev directTrueBinaryReport {Alternative : Type*}
    (winner loser : Alternative) : BinaryPairwiseReport Alternative :=
  ((winner, loser), true)

/-- All distinct ordered pairs, represented by their direct-true report atoms. -/
noncomputable def directedTrueBinaryReports
    (Alternative : Type*) [Fintype Alternative] [DecidableEq Alternative] :
    Finset (BinaryPairwiseReport Alternative) := by
  classical
  exact
    (((Finset.univ : Finset Alternative).product (Finset.univ : Finset Alternative)).filter
      (fun pair => pair.1 ≠ pair.2)).image
      (fun pair => directTrueBinaryReport pair.1 pair.2)

/-- Every distinct ordered pair supplies its direct-true report atom. -/
theorem directTrueBinaryReport_mem_directedTrueBinaryReports
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (winner loser : Alternative) (hneq : winner ≠ loser) :
    directTrueBinaryReport winner loser ∈ directedTrueBinaryReports Alternative := by
  classical
  refine Finset.mem_image.mpr ⟨(winner, loser), ?_, rfl⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
    ⟨Finset.mem_univ _, Finset.mem_univ _⟩, hneq⟩

/-- The event that the finite report sample fails to contain some directed
winner report for a distinct pair. -/
def directedWinFailure
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    {horizon : ℕ} (sample : Fin horizon → BinaryPairwiseReport Alternative) : Prop :=
  ¬ ∀ winner loser, winner ≠ loser →
    ∃ index, binaryReportWin winner loser (sample index)

/-- Decidability of the finite directed-win coverage event. -/
noncomputable instance instDecidablePredDirectedWinFailure
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    {horizon : ℕ} :
    DecidablePred (fun sample : Fin horizon → BinaryPairwiseReport Alternative =>
      directedWinFailure sample) :=
  Classical.decPred _

/-- The finite iid probability of failure to cover every directed winner. -/
noncomputable def directedWinFailureProbability
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (reportLaw : PMF (BinaryPairwiseReport Alternative)) (horizon : ℕ) : ℝ :=
  pmfProb (pmfProduct (Fin horizon) (BinaryPairwiseReport Alternative) reportLaw)
    (fun sample => directedWinFailure sample)

/-- If a directed winner is absent, then its direct-true atom is absent. -/
theorem directedWinFailure_imp_coverageFailure
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    {horizon : ℕ} (sample : Fin horizon → BinaryPairwiseReport Alternative)
    (hfailure : directedWinFailure sample) :
    ∃ report, report ∈ directedTrueBinaryReports Alternative ∧
      ∀ index, sample index ≠ report := by
  classical
  simp only [directedWinFailure, not_forall, not_exists] at hfailure
  rcases hfailure with ⟨winner, loser, hneq, hmissing⟩
  refine ⟨directTrueBinaryReport winner loser,
    directTrueBinaryReport_mem_directedTrueBinaryReports winner loser hneq, ?_⟩
  intro index heq
  exact hmissing index (by simpa [heq] using binaryReportWin_direct_true hneq)

/-- Directed-win coverage failure is bounded by failure to observe the finite
collection of direct-true report atoms. -/
theorem directedWinFailureProbability_le_coverageFailure
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (reportLaw : PMF (BinaryPairwiseReport Alternative)) (horizon : ℕ) :
    directedWinFailureProbability reportLaw horizon ≤
      Probability.finiteIidCoverageFailureProbability reportLaw
        (directedTrueBinaryReports Alternative) horizon := by
  classical
  unfold directedWinFailureProbability Probability.finiteIidCoverageFailureProbability
  apply pmfProb_le_of_imp
  intro sample hfailure
  exact directedWinFailure_imp_coverageFailure sample hfailure

/-- Under positive mass on each direct-true report atom, iid samples contain a
directed winner for every distinct ordered pair with probability tending to one. -/
theorem directedWinFailureProbability_tendsto_zero
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (reportLaw : PMF (BinaryPairwiseReport Alternative))
    (hdirect : ∀ winner loser, winner ≠ loser →
      0 < (reportLaw (directTrueBinaryReport winner loser)).toReal) :
    Filter.Tendsto (directedWinFailureProbability reportLaw) Filter.atTop (𝓝 0) := by
  have hcoverage : Filter.Tendsto
      (Probability.finiteIidCoverageFailureProbability reportLaw
        (directedTrueBinaryReports Alternative)) Filter.atTop (𝓝 0) := by
    apply Probability.finiteIidCoverageFailureProbability_tendsto_zero
    intro report hreport
    rcases Finset.mem_image.mp hreport with ⟨pair, hpair, rfl⟩
    exact hdirect pair.1 pair.2 (Finset.mem_filter.mp hpair).2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop (𝓝 0))
    hcoverage ?_ ?_
  · intro horizon
    exact pmfProb_nonneg (pmfProduct (Fin horizon) (BinaryPairwiseReport Alternative) reportLaw) _
  · intro horizon
    exact directedWinFailureProbability_le_coverageFailure reportLaw horizon

/-- Aggregate a finite batch of binary reports into directed winner counts.
The definition is deliberately literal: a `false` report on `(y,x)` is a win
of `x` over `y`, not a discarded or relabelled observation. -/
noncomputable def ofBinaryReports {Alternative : Type*} [DecidableEq Alternative]
    {horizon : ℕ} (sample : Fin horizon → BinaryPairwiseReport Alternative) :
    PairwiseCountDataset Alternative := by
  classical
  refine {
    count := fun winner loser =>
      ((Finset.univ : Finset (Fin horizon)).filter
        (fun index => binaryReportWin winner loser (sample index))).card
    diagonal_zero := ?_ }
  intro alternative
  simp [binaryReportWin]

/--
The log-likelihood contribution of one literal binary report.  A diagonal
display is omitted, matching the zero diagonal in the count likelihood; a
non-diagonal report contributes exactly the log likelihood of its observed
directed winner.  This definition retains both displayed orientations.
-/
noncomputable def binaryReportLogLikelihoodTerm
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (link : ℝ → ℝ) (score : ScoreVector Alternative)
    (report : BinaryPairwiseReport Alternative) : ℝ := by
  classical
  exact ∑ pair ∈ (Finset.univ : Finset Alternative).offDiag,
    if binaryReportWin pair.1 pair.2 report then
      Real.log (randomUtilityWinProbability link score pair.1 pair.2)
    else 0

/-- For the logistic link, each literal report contribution is continuous in
the score vector.  This is the analytic input for uniform finite-sample
likelihood control on a compact score cube. -/
theorem continuous_binaryReportLogLikelihoodTerm_sigmoid
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (report : BinaryPairwiseReport Alternative) :
    Continuous (fun score : ScoreVector Alternative =>
      binaryReportLogLikelihoodTerm Real.sigmoid score report) := by
  classical
  unfold binaryReportLogLikelihoodTerm
  apply continuous_finset_sum
  intro pair hpair
  by_cases hwin : binaryReportWin pair.1 pair.2 report
  · simp only [hwin, if_true]
    have hsigmoid : Continuous (fun score : ScoreVector Alternative =>
        Real.sigmoid (score pair.1 - score pair.2)) :=
      continuous_sigmoid.comp
        ((continuous_apply pair.1).sub (continuous_apply pair.2))
    simpa [randomUtilityWinProbability] using
      hsigmoid.log fun score => ne_of_gt (Real.sigmoid_pos _)
  · simp only [hwin, if_false]
    exact continuous_const

/--
Aggregating literal binary reports and then evaluating the pairwise-count
likelihood is exactly the sum of their individual log-likelihood terms.  In
particular, no balanced-design replacement or conditional reweighting is
hidden in the finite-data objective.
-/
theorem pairwiseLogLikelihood_ofBinaryReports_eq_sum
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    {horizon : ℕ} (sample : Fin horizon → BinaryPairwiseReport Alternative)
    (link : ℝ → ℝ) (score : ScoreVector Alternative) :
    pairwiseLogLikelihood (ofBinaryReports sample) link score =
      ∑ index : Fin horizon,
        binaryReportLogLikelihoodTerm link score (sample index) := by
  classical
  unfold pairwiseLogLikelihood ofBinaryReports binaryReportLogLikelihoodTerm
  calc
    (∑ pair ∈ (Finset.univ : Finset Alternative).offDiag,
        (((Finset.univ : Finset (Fin horizon)).filter
          (fun index => binaryReportWin pair.1 pair.2 (sample index))).card : ℝ) *
          Real.log (randomUtilityWinProbability link score pair.1 pair.2)) =
        ∑ pair ∈ (Finset.univ : Finset Alternative).offDiag,
          ∑ index ∈ (Finset.univ : Finset (Fin horizon)).filter
            (fun index => binaryReportWin pair.1 pair.2 (sample index)),
            Real.log (randomUtilityWinProbability link score pair.1 pair.2) := by
          apply Finset.sum_congr rfl
          intro pair _
          rw [Finset.sum_const, nsmul_eq_mul]
    _ = ∑ pair ∈ (Finset.univ : Finset Alternative).offDiag,
          ∑ index : Fin horizon,
            if binaryReportWin pair.1 pair.2 (sample index) then
              Real.log (randomUtilityWinProbability link score pair.1 pair.2)
            else 0 := by
          apply Finset.sum_congr rfl
          intro pair _
          rw [Finset.sum_filter]
    _ = ∑ index : Fin horizon,
          ∑ pair ∈ (Finset.univ : Finset Alternative).offDiag,
            if binaryReportWin pair.1 pair.2 (sample index) then
              Real.log (randomUtilityWinProbability link score pair.1 pair.2)
            else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ index : Fin horizon,
          binaryReportLogLikelihoodTerm link score (sample index) := rfl

/-- A direct displayed win contributes the corresponding directed log term. -/
theorem binaryReportLogLikelihoodTerm_direct_true
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (link : ℝ → ℝ) (score : ScoreVector Alternative)
    (winner loser : Alternative) (hneq : winner ≠ loser) :
    binaryReportLogLikelihoodTerm link score ((winner, loser), true) =
      Real.log (randomUtilityWinProbability link score winner loser) := by
  classical
  unfold binaryReportLogLikelihoodTerm
  rw [Finset.sum_eq_single (winner, loser)]
  · simp [binaryReportWin, hneq]
  · intro pair _ hpair
    have hnot : ¬ binaryReportWin pair.1 pair.2 ((winner, loser), true) := by
      intro hwin
      rcases hwin with ⟨_, hdirect | hreverse⟩
      · rcases hdirect with ⟨hfirst, hsecond, _⟩
        apply hpair
        exact Prod.ext hfirst.symm hsecond.symm
      · rcases hreverse with ⟨_, _, hfalse⟩
        simp at hfalse
    simp [hnot]
  · intro hnotmem
    exact (hnotmem (Finset.mem_offDiag.mpr
      ⟨Finset.mem_univ winner, Finset.mem_univ loser, hneq⟩)).elim

/-- A reversed displayed loss contributes the same directed winner log term. -/
theorem binaryReportLogLikelihoodTerm_reverse_false
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (link : ℝ → ℝ) (score : ScoreVector Alternative)
    (winner loser : Alternative) (hneq : winner ≠ loser) :
    binaryReportLogLikelihoodTerm link score ((loser, winner), false) =
      Real.log (randomUtilityWinProbability link score winner loser) := by
  classical
  unfold binaryReportLogLikelihoodTerm
  rw [Finset.sum_eq_single (winner, loser)]
  · simp [binaryReportWin, hneq]
  · intro pair _ hpair
    have hnot : ¬ binaryReportWin pair.1 pair.2 ((loser, winner), false) := by
      intro hwin
      rcases hwin with ⟨_, hdirect | hreverse⟩
      · rcases hdirect with ⟨_, _, htrue⟩
        simp at htrue
      · rcases hreverse with ⟨hfirst, hsecond, _⟩
        apply hpair
        exact Prod.ext hsecond.symm hfirst.symm
    simp [hnot]
  · intro hnotmem
    exact (hnotmem (Finset.mem_offDiag.mpr
      ⟨Finset.mem_univ winner, Finset.mem_univ loser, hneq⟩)).elim

/-- Diagonal displays make no contribution to the off-diagonal count likelihood. -/
theorem binaryReportLogLikelihoodTerm_diagonal
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (link : ℝ → ℝ) (score : ScoreVector Alternative)
    (alternative : Alternative) (outcome : Bool) :
    binaryReportLogLikelihoodTerm link score ((alternative, alternative), outcome) = 0 := by
  classical
  unfold binaryReportLogLikelihoodTerm
  apply Finset.sum_eq_zero
  intro pair hpair
  have hneq : pair.1 ≠ pair.2 := (Finset.mem_offDiag.mp hpair).2.2
  have hnot : ¬ binaryReportWin pair.1 pair.2 ((alternative, alternative), outcome) := by
    intro hwin
    rcases hwin with ⟨_, hdirect | hreverse⟩
    · rcases hdirect with ⟨hfirst, hsecond, _⟩
      exact hneq (hfirst.symm.trans hsecond)
    · rcases hreverse with ⟨hfirst, hsecond, _⟩
      exact hneq (hsecond.symm.trans hfirst)
  simp [hnot]

/-- A witnessed report win becomes a positive directed count in the aggregate
likelihood dataset. -/
theorem edge_of_exists_binaryReportWin
    {Alternative : Type*} [DecidableEq Alternative] {horizon : ℕ}
    (sample : Fin horizon → BinaryPairwiseReport Alternative)
    (winner loser : Alternative)
    (hwin : ∃ index, binaryReportWin winner loser (sample index)) :
    (ofBinaryReports sample).edge winner loser := by
  classical
  rcases hwin with ⟨index, hindex⟩
  unfold edge ofBinaryReports
  change 0 < ((Finset.univ : Finset (Fin horizon)).filter
    (fun index => binaryReportWin winner loser (sample index))).card
  apply Finset.card_pos.mpr
  refine ⟨index, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hindex⟩⟩

/-- If each ordered distinct alternative pair has occurred as a directed win,
the aggregated count graph is strongly connected. -/
theorem isStronglyConnected_of_allBinaryReportWins
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    {horizon : ℕ} (sample : Fin horizon → BinaryPairwiseReport Alternative)
    (hall : ∀ winner loser, winner ≠ loser →
      ∃ index, binaryReportWin winner loser (sample index)) :
    (ofBinaryReports sample).isStronglyConnected := by
  intro first second
  by_cases hsame : first = second
  · subst second
    exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single
      (edge_of_exists_binaryReportWin sample first second (hall first second hsame))

/-- The preceding full-directed-support event implies the componentwise form
of strong connectivity used by the finite-MLE existence theorem. -/
theorem everyComponentStronglyConnected_of_allBinaryReportWins
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    {horizon : ℕ} (sample : Fin horizon → BinaryPairwiseReport Alternative)
    (hall : ∀ winner loser, winner ≠ loser →
      ∃ index, binaryReportWin winner loser (sample index)) :
    (ofBinaryReports sample).everyComponentStronglyConnected := by
  intro first second _
  exact isStronglyConnected_of_allBinaryReportWins sample hall first second

/-- Full directed report coverage gives an attained fixed-reference MLE for
the literal finite count dataset. -/
theorem exists_pairwiseMLE_of_allBinaryReportWins
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    {horizon : ℕ} (sample : Fin horizon → BinaryPairwiseReport Alternative)
    (link : CDFLikePairwiseLink) (reference : Alternative)
    (hcontinuous : Continuous (link : ℝ → ℝ))
    (hstrict : StrictMono (link : ℝ → ℝ))
    (hall : ∀ winner loser, winner ≠ loser →
      ∃ index, binaryReportWin winner loser (sample index)) :
    ∃ score : ScoreVector Alternative,
      isPairwiseMLE (ofBinaryReports sample) link reference score :=
  exists_pairwiseMLE_of_everyComponentStronglyConnected
    (ofBinaryReports sample) link reference hcontinuous hstrict
    (everyComponentStronglyConnected_of_allBinaryReportWins sample hall)

/-- The finite iid probability that the literal count dataset has no attained
fixed-reference MLE. -/
noncomputable def noPairwiseMLEProbability
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (reportLaw : PMF (BinaryPairwiseReport Alternative))
    (link : CDFLikePairwiseLink) (reference : Alternative) (horizon : ℕ) : ℝ := by
  classical
  letI : DecidablePred (fun sample : Fin horizon → BinaryPairwiseReport Alternative =>
      ¬ ∃ score : ScoreVector Alternative,
        isPairwiseMLE (ofBinaryReports sample) link reference score) :=
    Classical.decPred _
  exact pmfProb (pmfProduct (Fin horizon) (BinaryPairwiseReport Alternative) reportLaw)
    (fun sample => ¬ ∃ score : ScoreVector Alternative,
      isPairwiseMLE (ofBinaryReports sample) link reference score)

/-- Finite MLE nonexistence is contained in failure to observe every directed
winner. -/
theorem noPairwiseMLEProbability_le_directedWinFailure
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (reportLaw : PMF (BinaryPairwiseReport Alternative))
    (link : CDFLikePairwiseLink) (reference : Alternative) (horizon : ℕ)
    (hcontinuous : Continuous (link : ℝ → ℝ))
    (hstrict : StrictMono (link : ℝ → ℝ)) :
    noPairwiseMLEProbability reportLaw link reference horizon ≤
      directedWinFailureProbability reportLaw horizon := by
  classical
  letI : DecidablePred (fun sample : Fin horizon → BinaryPairwiseReport Alternative =>
      ¬ ∃ score : ScoreVector Alternative,
        isPairwiseMLE (ofBinaryReports sample) link reference score) :=
    Classical.decPred _
  unfold noPairwiseMLEProbability directedWinFailureProbability
  apply pmfProb_le_of_imp
  intro sample hnoMLE
  by_contra hfailure
  have hall : ∀ winner loser, winner ≠ loser →
      ∃ index, binaryReportWin winner loser (sample index) := by
    by_contra hnotAll
    exact hfailure hnotAll
  exact hnoMLE (exists_pairwiseMLE_of_allBinaryReportWins sample link reference
    hcontinuous hstrict hall)

/-- If every direct-true report atom has positive mass, the probability that
the finite iid count likelihood lacks an attained MLE tends to zero. -/
theorem noPairwiseMLEProbability_tendsto_zero
    {Alternative : Type*} [Fintype Alternative] [DecidableEq Alternative]
    (reportLaw : PMF (BinaryPairwiseReport Alternative))
    (link : CDFLikePairwiseLink) (reference : Alternative)
    (hcontinuous : Continuous (link : ℝ → ℝ))
    (hstrict : StrictMono (link : ℝ → ℝ))
    (hdirect : ∀ winner loser, winner ≠ loser →
      0 < (reportLaw (directTrueBinaryReport winner loser)).toReal) :
    Filter.Tendsto (noPairwiseMLEProbability reportLaw link reference)
      Filter.atTop (𝓝 0) := by
  classical
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop (𝓝 0))
    (directedWinFailureProbability_tendsto_zero reportLaw hdirect) ?_ ?_
  · intro horizon
    letI : DecidablePred (fun sample : Fin horizon → BinaryPairwiseReport Alternative =>
        ¬ ∃ score : ScoreVector Alternative,
          isPairwiseMLE (ofBinaryReports sample) link reference score) :=
      Classical.decPred _
    exact pmfProb_nonneg (pmfProduct (Fin horizon) (BinaryPairwiseReport Alternative) reportLaw) _
  · intro horizon
    exact noPairwiseMLEProbability_le_directedWinFailure reportLaw link reference horizon
      hcontinuous hstrict

end PairwiseCountDataset
end HumanFeedback
end Learning
end AppliedModelingLib
